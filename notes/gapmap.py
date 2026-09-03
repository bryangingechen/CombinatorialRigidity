#!/usr/bin/env python3
"""Read-only slice reader for `notes/Pencil-informal.md`'s *State of (K)* gap
map: get one gap's status, or just the sentences mentioning one label, without
loading a 22 000-character table row.

Why this exists -- an ACCESS problem, not a length problem. The gap map is the
Phase-39 arc's authoritative status object (`RESEARCH-ARC.md` section 3) and
`check-gapmap-cells.py` already caps every cell, which today PASSES. But one
row is **one physical line**: `(K-grid)` is 22 260 characters / ~5 600 tokens
on a single line, `(K-out)` 10 738 and `(K-bare)/(K-bare-ext)` 9 381. So
`sed -n '252p'`, `grep '(GR-15)'` and any unanchored grep all deliver the
WHOLE row -- there is no way to read part of one. Measured over four recent
`/coordinate-phase` coordinator sessions, tool results carrying the `(K-grid)`
row cost 30k-53k tokens each (10-13 results per session), and in one session
that single table row was **20% of peak context** -- more than reading the
entire phase note. The coordinator almost never wants the row; it wants one
gap's current status, or the sentences mentioning one label. Hence:

  --list                     an index: every row's gap, section+steps and SIZE,
                             so you see what exists and what is expensive
                             before reading anything (~600 tok for 27 rows).
  --row '(K-grid)'           one row, one cell (--cell status|close|all),
                             sentence-windowed (--head/--tail/--sentences).
  --label '(GR-15)'          only the sentences mentioning that label, each
                             tagged with the row, cell and unit index it came
                             from. This is what replaces `grep`, which cannot
                             do better than whole-line output here.
  --grep PATTERN             the same, for an arbitrary regex.
  --selftest                 lossless-split + size audit (no content).

`--head N` / `--tail N` / `--sentences A-B` / `--full` window the output;
`--sentences` and `--tail` apply to `--row`, while `--label` / `--grep` take
`--head N` (how many matched units to print) and `--full`. `--label` and
`--grep` exit 1 when nothing matched, grep-style; everything else exits 0.

Nothing here writes: it is a reader, and it deliberately offers no way to edit
a row. The table is NOT restructured to make this work -- its one-row-per-gap
shape is load-bearing for `check-gapmap-cells.py` and for `RESEARCH-ARC.md`
section 3, and this script exists so it never has to be.

Parsing. The table walk is NOT reimplemented here: `check-gapmap-cells.py`
`iter_row_cells` is the one parser, imported by path (its filename is not a
Python identifier). That gate documents the table shape -- one row per gap,
four columns `| gap | section + steps | status | what would close it |` -- and
the real hazard, rows carrying literal unescaped `|` inside their prose (e.g.
`|V|` cardinality notation) that are not column delimiters; such a row comes
back as a single `combined` cell rather than a guessed split, and this reader
labels it `[status+close-it, combined]` so the reader knows why.

Sentence splitting, and the no-silent-loss rule. Units are sentences, cut at
`.`/`!`/`?` + optional closing markup + whitespace, with three guards for the
maths in these cells: inline code spans are masked first (so `Escape.lean:555`
and `` `dim Z` `` never split), a boundary is refused after a known
abbreviation (`e.g.`, `Cor.`, `Thm.`, `cf.`, an initial) and refused before a
lowercase continuation. Decimals (`5.7`, section 3.1) need no guard -- they
carry no following whitespace. A sentence longer than SOFT_MAX is further cut
at `; ` clause boundaries where it has any, so that a long enumeration is
still windowable; "unit" therefore means "sentence, or a semicolon-delimited
clause group of an over-long sentence", and `--sentences A-B` indexes units.
A semicolon-free sentence is never cut, so a unit CAN exceed SOFT_MAX
(`--selftest` reports the longest one).

Every unit is a contiguous slice of the cell, so concatenating a cell's units
reproduces it exactly; that identity is asserted on every split (and audited
across the whole file by `--selftest`). If it ever failed, the cell is emitted
WHOLE with a warning rather than partially -- **text is never silently
dropped**. Truncation is likewise always disclosed: every windowed output
states the true total up front and ends with an explicit
`[... N of M units not shown; ...]` line naming the flag that shows the rest,
so a truncated answer can never be mistaken for a complete one.

Other files. `--file` takes any path, so this also serves
`notes/Pencil-informal-grid.md` (14 924 lines, owns section (K-grid)) and
`notes/Pencil-W4-informal.md`. Those carry no gap-map table, so `--label` /
`--grep` fall back to a whole-file sentence scan tagged by nearest heading +
line number, and `--list` prints the heading outline with per-section sizes.

Sizes are reported as characters/words, with `~t` a rough token proxy
(chars/3 -- the ratio measured on this content, not the ~chars/4 of English
prose); the point is relative cost, not an exact tokenizer count.
"""
import argparse
import importlib.util
import os
import re
import sys
import textwrap

_HERE = os.path.dirname(os.path.abspath(__file__))
SOFT_MAX = 900   # chars; over-long sentences get a second cut at `; `
WRAP = 96
DEFAULT_WINDOW = {"row": 20, "scan": 40}


def _load_gate():
    """`check-gapmap-cells.py` as a module (its name is not an identifier)."""
    path = os.path.join(_HERE, "check-gapmap-cells.py")
    spec = importlib.util.spec_from_file_location("check_gapmap_cells", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


GATE = _load_gate()

# ---------------------------------------------------------------- sentences

_CODE_RE = re.compile(r"`[^`\n]*`")
_BOUNDARY_RE = re.compile(r"[.!?](?:\*\*|\*|_|\)|\]|\"|”|’|')*\s+")
_CLAUSE_RE = re.compile(r";\s+")
_TRAIL_WORD_RE = re.compile(r"([A-Za-z][A-Za-z0-9.'’-]*)$")
_ABBREV = {
    "e.g", "i.e", "cf", "resp", "vs", "etc", "al", "viz", "ibid", "approx",
    "cor", "thm", "lem", "lemma", "prop", "def", "rem", "obs", "fig", "tab",
    "eq", "ch", "sec", "app", "no", "nos", "pp", "p", "ff", "op", "alg", "ex",
    "incl", "cca", "w.l.o.g", "s.t", "st", "vol", "ed", "eds", "min", "max",
}


def _mask(s):
    """Same length, inline code spans blanked to `#` -- so a period inside
    `Escape.lean:555` is not a sentence boundary and offsets still line up."""
    return _CODE_RE.sub(lambda m: "#" * len(m.group(0)), s)


def _refuse(masked, m):
    """True if this candidate boundary is not a sentence end."""
    word = _TRAIL_WORD_RE.search(masked[: m.start()])
    if word:
        tok = word.group(1).rstrip(".").lower()
        if tok in _ABBREV:
            return True
        if len(tok) == 1:  # an initial, e.g. `W.`
            return True
    nxt = masked[m.end() : m.end() + 1]
    if nxt and nxt.islower():  # lowercase continuation: not a new sentence
        return True
    return False


def _slice_at(text, cuts):
    """Contiguous slices of `text` at the given offsets (lossless)."""
    out = []
    prev = 0
    for c in cuts:
        if c > prev:
            out.append(text[prev:c])
            prev = c
    if prev < len(text):
        tail = text[prev:]
        if out and not tail.strip():
            out[-1] += tail  # keep a whitespace-only tail attached
        else:
            out.append(tail)
    return out or [text]


def _clause_split(piece):
    """Second cut of an over-long sentence at `; `, greedily grouped to
    SOFT_MAX. Lossless by construction (contiguous slices)."""
    masked = _mask(piece)
    cuts = [m.end() for m in _CLAUSE_RE.finditer(masked)]
    if not cuts:
        return [piece]
    parts = _slice_at(piece, cuts)
    out, buf = [], ""
    for part in parts:
        if buf and len(buf) + len(part) > SOFT_MAX:
            out.append(buf)
            buf = part
        else:
            buf += part
    if buf:
        out.append(buf)
    return out


def units(text):
    """Display units for one cell / block. Never loses text: on any failure of
    the reconstruction identity the input comes back WHOLE, with a warning."""
    masked = _mask(text)
    cuts = [m.end() for m in _BOUNDARY_RE.finditer(masked) if not _refuse(masked, m)]
    pieces = _slice_at(text, cuts)
    out = []
    for piece in pieces:
        out.extend(_clause_split(piece) if len(piece) > SOFT_MAX else [piece])
    if "".join(out) != text:
        print(
            "WARNING: sentence split was not lossless; emitting the cell whole "
            "(no text dropped). Report this as a gapmap.py bug.",
            file=sys.stderr,
        )
        return [text]
    return out


# ------------------------------------------------------------------- naming


def _norm(s):
    """Row name minus markdown emphasis and the `*(new, <date>, …)*` tag."""
    s = re.sub(r"\*\((?:new|renamed)[^)]*\)\*", " ", s)
    s = s.replace("**", " ").replace("*", " ").replace("`", " ")
    s = re.sub(r"\s+", " ", s).strip()
    return re.sub(r"\s+([,;:])", r"\1", s)


def _core(s):
    """Match key: normalized, parens and spaces removed, lowercased."""
    return re.sub(r"[()\s]", "", _norm(s)).lower()


def label_regex(label):
    """Regex for a gap-map label token -- `(GR-15)`, `GR-15`, `(GR-4′)`,
    `(GR-28)(iv)`. Matches the parenthesized and bare forms, and does NOT
    match a longer sibling (`(GR-15<digit>)`, `(GR-15a)`, `(GR-4')` for
    `GR-4`).  The digit form is written as a PLACEHOLDER, not a real label:
    this docstring used to say `(GR-150)`, which direction GLEAF consumes, so
    a grep for that label would have hit this tool.  Keep tool-file examples
    unmintable."""
    core = re.sub(r"^\(+", "", label.strip())
    core = re.sub(r"\)+$", "", core)
    if not core:
        raise SystemExit("empty label")
    return re.compile(
        r"(?<![A-Za-z0-9\-])" + re.escape(core) + r"(?![0-9A-Za-z′'’])"
    )


# -------------------------------------------------------------------- model


class Cell:
    def __init__(self, row, name, text):
        self.row = row          # owning Row
        self.name = name        # "status" / "close-it" / "status+close-it, combined"
        self.text = text.strip()
        self.units = units(self.text)

    @property
    def tag(self):
        return f"{self.row.label} L{self.row.lineno} [{self.name}]"


class Row:
    def __init__(self, lineno, key, col1, col2, kind, cells):
        self.lineno = lineno
        self.key = key
        self.name = _norm(col1)
        self.steps = _norm(col2)
        self.kind = kind
        if kind == "split":
            names = ["status", "close-it"]
        else:
            names = ["status+close-it, combined"]
        self.cells = [Cell(self, n, t) for n, t in zip(names, cells)]
        # Columns 1-2 as a scannable cell too, so --label/--grep cover the WHOLE
        # row and cannot miss an occurrence a grep of the line would find. Not
        # offered to --cell: those two columns are short and always printed.
        self.head_cell = Cell(self, "gap+steps", f"{col1} | {col2}")

    @property
    def label(self):
        return self.name or self.key

    @property
    def chars(self):
        return sum(len(c.text) for c in self.cells)

    def pick(self, which):
        if self.kind == "combined":
            return self.cells  # no guessed split point; one cell either way
        if which == "status":
            return [self.cells[0]]
        if which == "close":
            return [self.cells[1]]
        return self.cells


def read_rows(text):
    return [Row(*r) for r in GATE.iter_row_cells(text)]


def find_row(rows, want):
    """Lenient row lookup: exact on the key, then on the full name, then a
    unique substring. Ambiguity is reported, never guessed."""
    target = _core(want)
    for r in rows:
        if _core(r.key) == target:
            return r
    for r in rows:
        if _core(r.name) == target:
            return r
    hits = [r for r in rows if target and target in _core(r.name)]
    if len(hits) == 1:
        return hits[0]
    if hits:
        raise SystemExit(
            f"'{want}' matches {len(hits)} rows: "
            + ", ".join(r.label for r in hits)
            + "\nName one exactly (see --list)."
        )
    raise SystemExit(f"no gap-map row matches '{want}' (see --list)")


# ------------------------------------------------------- whole-file fallback


class Block:
    """A prose paragraph / table row / code line of a table-less file."""

    def __init__(self, lineno, heading, text):
        self.lineno = lineno
        self.heading = heading
        self.text = text.strip()
        self.units = units(self.text)

    @property
    def tag(self):
        return f"{self.heading} L{self.lineno}"


def read_blocks(text):
    out = []
    heading = "(preamble)"
    buf, start, fence = [], None, False

    def flush():
        nonlocal buf, start
        if buf:
            out.append(Block(start, heading, " ".join(buf)))
        buf, start = [], None

    for i, line in enumerate(text.splitlines(), start=1):
        if line.startswith("```"):
            flush()
            fence = not fence
            continue
        if fence:
            flush()
            if line.strip():
                out.append(Block(i, heading, line))
            continue
        m = re.match(r"^(#{1,6})\s+(.*)$", line)
        if m:
            flush()
            heading = _norm(m.group(2))[:60]
            continue
        if not line.strip():
            flush()
            continue
        if line.startswith("|"):
            flush()
            out.append(Block(i, heading, line))
            continue
        if start is None:
            start = i
        buf.append(line.strip())
    flush()
    return out


# ------------------------------------------------------------------ printing


def _tok(n):
    """Rough token proxy. chars/3, the ratio MEASURED on this content (the
    `(K-grid)` row: 21 815 chars of it cost ~7 300 tokens in a real tool
    result) -- markdown-and-maths prose tokenizes far denser than English."""
    return f"~{round(n / 3):,}t"


def _size(text):
    return f"{len(text):,}c/{len(text.split()):,}w"


def window(items, args, kind):
    """(shown_items, first_index, note) for the requested slice."""
    n = len(items)
    if args.full:
        return items, 1, None
    if args.sentences:
        m = re.match(r"^(\d*)-(\d*)$", args.sentences.strip()) or re.match(
            r"^(\d+)$", args.sentences.strip()
        )
        if not m:
            raise SystemExit("--sentences wants A-B, A-, -B or A")
        g = m.groups()
        lo = int(g[0]) if g[0] else 1
        hi = int(g[1]) if len(g) > 1 and g[1] else (lo if len(g) == 1 else n)
        lo, hi = max(1, lo), min(n, hi)
        if lo > n or hi < lo:
            raise SystemExit(
                f"--sentences {args.sentences}: this cell has {n} unit(s)"
            )
        shown, first = items[lo - 1 : hi], lo
    elif args.tail:
        first = max(1, n - args.tail + 1)
        shown = items[first - 1 :]
    else:
        size = args.head or DEFAULT_WINDOW[kind]
        shown, first = items[:size], 1
    hidden = n - len(shown)
    note = None
    if hidden > 0:
        last = first + len(shown) - 1
        nxt = last + 1
        hint = (
            f"--sentences {nxt}-{min(n, nxt + len(shown) - 1)} for the next window, "
            if nxt <= n
            else ""
        )
        note = (
            f"[... {hidden} of {n} units not shown (shown {first}-{last}); "
            f"{hint}--full for all]"
        )
    return shown, first, note


def emit_units(items, args, kind, indent="  "):
    shown, first, note = window(items, args, kind)
    for i, unit in enumerate(shown, start=first):
        head = f"{indent}u{i}: "
        body = textwrap.fill(
            unit.strip(),
            width=WRAP,
            initial_indent=head,
            subsequent_indent=indent + "    ",
        )
        print(body)
    if note:
        print(indent + note)


def cmd_list(args, path, disp, text):
    rows = read_rows(text)
    if not rows:
        return list_sections(disp, text)
    span = f"{rows[0].lineno}-{rows[-1].lineno}"
    total = sum(r.chars for r in rows)
    print(f"{disp} — *State of (K)* gap map: {len(rows)} rows, lines {span}")
    print(f"  whole table {total:,}c {_tok(total)} — read it a row/cell at a time")
    print(
        f"  {'line':>5}  {'gap':<24} {'§ + steps':<34} "
        f"{'status':>14} {'close-it':>13} {'row':>14}"
    )
    for r in rows:
        cells = {c.name: c for c in r.cells}
        st = cells.get("status")
        cl = cells.get("close-it")
        comb = cells.get("status+close-it, combined")
        st_s = _size(st.text) if st else f"{_size(comb.text)}*"
        cl_s = _size(cl.text) if cl else "(combined)"
        print(
            f"  {r.lineno:>5}  {_norm(r.name)[:24]:<24} {r.steps[:34]:<34} "
            f"{st_s:>14} {cl_s:>13} {r.chars:>6,}c {_tok(r.chars):>7}"
        )
    if any(r.kind == "combined" for r in rows):
        print(
            "  * combined: the row carries an unescaped `|` inside its prose, so "
            "the status/close-it split is not guessed (see the gate's docstring)."
        )
    return 0


def list_sections(disp, text):
    """Heading outline + per-section size, for a file with no gap-map table."""
    lines = text.splitlines()
    heads = [
        (i, len(m.group(1)), m.group(2))
        for i, line in enumerate(lines, start=1)
        for m in [re.match(r"^(#{1,3})\s+(.*)$", line)]
        if m
    ]
    print(f"{disp} — no *State of (K)* gap-map table; {len(lines):,} lines, "
          f"{len(heads)} headings (--row/--cell need the table; --label/--grep "
          f"scan the whole file)")
    for j, (lineno, level, title) in enumerate(heads):
        end = heads[j + 1][0] - 1 if j + 1 < len(heads) else len(lines)
        chunk = "\n".join(lines[lineno - 1 : end])
        print(
            f"  {lineno:>6}  {'  ' * (level - 1)}{_norm(title)[:70 - 2 * level]:<{72 - 2 * level}}"
            f"{end - lineno + 1:>6}L {len(chunk):>8,}c {_tok(len(chunk)):>8}"
        )
    return 0


def cmd_row(args, path, disp, text):
    rows = read_rows(text)
    if not rows:
        raise SystemExit(
            f"{disp} has no *State of (K)* gap-map table; --row needs it. "
            "Use --list for the heading outline, or --label/--grep."
        )
    r = find_row(rows, args.row)
    print(f"{disp}:{r.lineno}  {r.label}")
    print(f"  § + steps: {r.steps}")
    for cell in r.pick(args.cell):
        n = len(cell.units)
        print(
            f"  [{cell.name}] {n} unit{'' if n == 1 else 's'}, "
            f"{_size(cell.text)} {_tok(len(cell.text))}"
        )
        emit_units(cell.units, args, "row", indent="   ")
    return 0


def _scan_targets(text):
    """(units-bearing objects, scope description) for label/grep."""
    rows = read_rows(text)
    if rows:
        return [c for r in rows for c in ([r.head_cell] + r.cells)], (
            f"gap-map table, lines {rows[0].lineno}-{rows[-1].lineno}"
        )
    return read_blocks(text), "whole file (no gap-map table)"


def cmd_scan(args, path, disp, text, pattern, what):
    targets, scope = _scan_targets(text)
    hits, occ = [], 0
    for t in targets:
        for i, unit in enumerate(t.units, start=1):
            found = len(pattern.findall(unit))
            if found:
                occ += found
                hits.append((t, i, unit))
                # keep the unit index so a reader can ask for its neighbours
    groups = []
    for t, i, unit in hits:
        if not groups or groups[-1][0] is not t:
            groups.append((t, []))
        groups[-1][1].append((i, unit))
    print(
        f"{what} — {occ} occurrence(s) in {len(hits)} unit(s) across "
        f"{len(groups)} row(s)/block(s)  [{disp}, {scope}]"
    )
    print(f"  pattern: {pattern.pattern}")
    if not hits:
        return 1
    budget = DEFAULT_WINDOW["scan"] if not args.full else len(hits)
    if args.head:
        budget = args.head
    shown = 0
    for t, found in groups:
        if shown >= budget:
            break
        print(f"── {t.tag}")
        for i, unit in found:
            if shown >= budget:
                break
            head = f"  u{i}: "
            print(
                textwrap.fill(
                    unit.strip(), width=WRAP,
                    initial_indent=head, subsequent_indent="      ",
                )
            )
            shown += 1
    if shown < len(hits):
        print(
            f"  [... {len(hits) - shown} of {len(hits)} matched units not shown; "
            f"--full for all, --head N for more]"
        )
    if scope.startswith("gap-map"):
        print(
            "  (u<i> is the unit index inside that cell: "
            "`--row <gap> --cell <cell> --sentences i-j` for context.)"
        )
    else:
        print("  (L<n> is the block's first line; read the file there for context.)")
    return 0


def cmd_selftest(args, path, disp, text):
    targets, scope = _scan_targets(text)
    worst = (0, "")
    total_units = total_chars = 0
    for t in targets:
        if "".join(t.units) != t.text:
            print(f"FAIL: lossy split at {t.tag}", file=sys.stderr)
            return 1
        total_units += len(t.units)
        total_chars += len(t.text)
        for u in t.units:
            if len(u) > worst[0]:
                worst = (len(u), t.tag)
    print(
        f"OK: {disp} — {scope}; {len(targets)} cells/blocks, {total_units:,} "
        f"units, {total_chars:,}c {_tok(total_chars)}; split lossless everywhere."
    )
    print(f"  longest unit {worst[0]:,}c (SOFT_MAX {SOFT_MAX}) at {worst[1]}")
    return 0


# ---------------------------------------------------------------------- main


def resolve(name):
    for cand in (name, os.path.join(_HERE, name), os.path.join(_HERE, os.path.basename(name))):
        if os.path.isfile(cand):
            disp = name if os.path.isfile(name) else os.path.join("notes", os.path.basename(name))
            return cand, disp
    raise SystemExit(f"no such file: {name}")


def main(argv):
    p = argparse.ArgumentParser(
        prog="gapmap.py",
        description="Read one slice of the *State of (K)* gap map "
                    "(a row is one 22 000-character line; see the docstring).",
    )
    p.add_argument("--file", default=os.path.basename(GATE.PATH),
                   help="workbook to read (default notes/Pencil-informal.md)")
    mode = p.add_mutually_exclusive_group(required=True)
    mode.add_argument("--list", action="store_true", help="row index with sizes")
    mode.add_argument("--row", metavar="GAP", help="one row, e.g. '(K-grid)'")
    mode.add_argument("--label", metavar="LABEL",
                      help="sentences mentioning a label, e.g. '(GR-15)'")
    mode.add_argument("--grep", metavar="PATTERN", help="sentence-scoped regex search")
    mode.add_argument("--selftest", action="store_true",
                      help="audit the sentence split (lossless) and sizes")
    p.add_argument("--cell", default="all", choices=["status", "close", "all"],
                   help="which cell of the row (default all)")
    p.add_argument("--head", type=int, metavar="N",
                   help="first N units (--row) / N matched units (--label, --grep)")
    p.add_argument("--tail", type=int, metavar="N", help="last N units (--row)")
    p.add_argument("--sentences", metavar="A-B",
                   help="unit range for --row, 1-based inclusive (A-B, A-, -B, A)")
    p.add_argument("--full", action="store_true", help="no window (the whole cell)")
    p.add_argument("-i", "--ignore-case", action="store_true", help="for --grep")
    args = p.parse_args(argv)

    path, disp = resolve(args.file)
    with open(path, encoding="utf-8") as f:
        text = f.read()

    if args.list:
        return cmd_list(args, path, disp, text)
    if args.selftest:
        return cmd_selftest(args, path, disp, text)
    if args.row:
        return cmd_row(args, path, disp, text)
    if args.label:
        return cmd_scan(args, path, disp, text, label_regex(args.label), args.label)
    flags = re.I if args.ignore_case else 0
    try:
        pattern = re.compile(args.grep, flags)
    except re.error as e:
        raise SystemExit(f"bad --grep regex: {e}")
    return cmd_scan(args, path, disp, text, pattern, f"/{args.grep}/")


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
