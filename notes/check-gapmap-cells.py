#!/usr/bin/env python3
"""Gate: `notes/Pencil-informal.md`'s *State of (K)* gap-map table must stay
within a per-cell word cap (adapted from `check-log-rows.py`'s Notes-cell
cap, same shape).

Why this exists. The gap map's job is to state the *current* state of each
named gap in one physical table row -- "edit these rows ... rather than
writing a fresh summary of the arc beside it" (the table's own header). In
practice every landing on the live gap tends to *append* a "since direction
X, ..." clause instead of recomputing the row, so the row grows monotonically
until a coordinator recompute resets it -- and then grows again. The
`(K-grid)` row hit this FOUR times (dc4ecc7b 1274 -> 97c9661c 1373 ->
07f6f9b6 1729 -> 0e2bd9b7 2066 -> 2ab3c630 2328 words) before two prose-only
repairs were abandoned in favour of this mechanical cap. See
`notes/Phase39.md` *Decisions made* for the incident and `notes/CLAUDE.md`'s
`Pencil-informal.md` bullet for where this script is documented.

Table shape. One row per gap, four columns: `| gap | § + steps | status |
what would close it |`. Columns 1-2 (gap name, step range) are always short
and pipe-free in practice; columns 3-4 carry the free-form prose this gate
protects. Some rows contain literal, unescaped `|` characters inside their
prose (e.g. `|V|`-style cardinality notation) that are not real column
delimiters -- when a row's pipe count doesn't cleanly resolve to 4 columns,
this script falls back to capping columns 3+4 COMBINED for that row rather
than guessing a split point (see `_row_cells`).

Modes (same three as `check-log-rows.py`):
  (default)  check only rows whose col-3/col-4 content changed vs HEAD --
             the rows this commit touches. Grandfathered rows don't block
             unrelated commits; any row you DO touch must pass.
  --all      check every row (full-table audit / a cleanup pass).
  --last     check rows changed in HEAD vs HEAD~1 (post-commit audit).

Exit 1 (and list offenders) if any checked row/cell exceeds its cap.
Run before committing a change to the gap map -- see the docstring note
above for where this is documented; there is no automated pre-commit hook,
so run it by hand (`python3 notes/check-gapmap-cells.py`).

Caps. `DEFAULT_CAP` applies per cell (status, close-it) to every gap not
listed in `SPECIAL_CAPS`. `(K-grid)` is the one row that has actually needed
more room every time it has been honestly recomputed (it carries the whole
GORIENT/GDEV/GADM theorem chain, GR-32 through GR-43) -- its caps are set at
the 2026-08-18 recompute's own size (1137 / 619 words) plus ~15% headroom,
NOT at the generic default. Recomputing the row again legitimately (more
theorems land) should come with a deliberate bump here, in the same commit,
with a one-line reason -- not a silent regrowth past the cap.
"""
import re
import subprocess
import sys

PATH = "notes/Pencil-informal.md"
SECTION_RE = re.compile(r"^## State of \(K\)")
HEADER_RE = re.compile(r"^\|\s*gap\s*\|")
SEP_RE = re.compile(r"^\|[\s:|-]+\|\s*$")
PIPE = re.compile(r"(?<!\\)\|")  # a column delimiter is an UNescaped pipe
KEY_RE = re.compile(r"\(([A-Za-z0-9\-∞Δσ′]+)\)")

DEFAULT_CAP = 800  # per cell (status / close-it); largest ungrandfathered
                    # row today is (K-ann)'s close-it cell at 628 words.
SPECIAL_CAPS = {
    # gap-key -> {"status": cap, "closeit": cap}. Combined-remainder fallback
    # (ambiguous pipe split) uses the sum of the two.
    "K-grid": {"status": 1300, "closeit": 720},
}


def _key_of(col1):
    """Stable per-row key: the first `(xxx)` token in column 1, else the
    trimmed column-1 text itself (rows like `escape criterion` have no
    parenthesized code)."""
    m = KEY_RE.search(col1)
    return m.group(1) if m else col1.strip().strip("`*").strip()


def table_rows(text):
    """{key: ("split", status_words, closeit_words) | ("combined", words)}
    for every data row of the *State of (K)* gap-map table."""
    lines = text.splitlines()
    out = {}
    in_section = False
    in_table = False
    for line in lines:
        if SECTION_RE.match(line):
            in_section = True
            continue
        if in_section and line.startswith("## "):
            break  # next top-level section ends the gap-map's span
        if not in_section:
            continue
        if HEADER_RE.match(line):
            in_table = True
            continue
        if in_table and SEP_RE.match(line):
            continue
        if in_table and not line.startswith("|"):
            in_table = False  # table ended (prose resumes before the next ##)
            continue
        if not in_table:
            continue
        pos = [m.start() for m in PIPE.finditer(line)]
        if len(pos) < 5:
            continue  # not a well-formed 4-column row; skip rather than guess
        col1 = line[pos[0] + 1 : pos[1]]
        key = _key_of(col1)
        if len(pos) == 5:
            status = line[pos[2] + 1 : pos[3]]
            closeit = line[pos[3] + 1 : pos[4]]
            out[key] = ("split", len(status.split()), len(closeit.split()))
        else:
            # stray unescaped pipe(s) inside columns 3/4 -- don't guess the
            # split, cap the combined remainder instead.
            combined = line[pos[2] + 1 : pos[-1]]
            out[key] = ("combined", len(combined.split()))
    return out


def caps_for(key):
    special = SPECIAL_CAPS.get(key)
    if special:
        return special["status"], special["closeit"]
    return DEFAULT_CAP, DEFAULT_CAP


def offenders(rows, keys):
    bad = []
    for key in sorted(keys):
        row = rows.get(key)
        if row is None:
            continue
        status_cap, closeit_cap = caps_for(key)
        if row[0] == "split":
            _, status_n, closeit_n = row
            if status_n > status_cap:
                bad.append((key, "status", status_n, status_cap))
            if closeit_n > closeit_cap:
                bad.append((key, "close-it", closeit_n, closeit_cap))
        else:
            _, combined_n = row
            combined_cap = status_cap + closeit_cap
            if combined_n > combined_cap:
                bad.append((key, "combined (ambiguous split)", combined_n, combined_cap))
    return bad


def git_show(ref):
    try:
        return subprocess.run(
            ["git", "show", f"{ref}:{PATH}"],
            capture_output=True, text=True, check=True,
        ).stdout
    except Exception:
        return None


def main(argv):
    with open(PATH, encoding="utf-8") as f:
        cur = table_rows(f.read())

    if "--all" in argv:
        check, label = set(cur), "full table"
    elif "--last" in argv:
        head, prev = git_show("HEAD"), git_show("HEAD~1")
        if head is None:
            print("cannot read HEAD copy of the gap map", file=sys.stderr)
            return 2
        cur = table_rows(head)
        base = table_rows(prev) if prev is not None else {}
        check = {k for k, v in cur.items() if base.get(k) != v}
        label = "changed HEAD~1..HEAD"
    else:
        head = git_show("HEAD")
        if head is None:
            check = set(cur)  # no committed base -> check all
        else:
            base = table_rows(head)
            check = {k for k, v in cur.items() if base.get(k) != v}
        label = "changed vs HEAD"

    bad = offenders(cur, check)
    if bad:
        print(
            "FAIL: gap-map cell(s) exceed their word cap "
            "(notes/Pencil-informal.md *State of (K)*):",
            file=sys.stderr,
        )
        for key, cell, n, cap in bad:
            print(f"  ({key}) {cell}: {n} words (+{n - cap} over cap {cap})", file=sys.stderr)
        print(
            "Recompute the row as a current-state statement (no then/now or "
            "correction narrative -- those belong at the owning Step) rather "
            "than appending another 'since direction X' clause. If the row "
            "has genuinely grown (more theorems land), bump its entry in "
            "SPECIAL_CAPS in this script, in the same commit, with a reason.",
            file=sys.stderr,
        )
        return 1
    print(f"OK: {len(check)} gap-map row(s) checked ({label}); all within cap.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
