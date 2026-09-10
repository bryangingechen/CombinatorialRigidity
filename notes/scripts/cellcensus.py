#!/usr/bin/env python3
"""Census of a gap-map status cell: how much of it is SETTLED, and how much is
already recoverable from the section that owns it.

Why this exists. `notes/Harness-structure.md` D7.4 found `(K-bare)` and
`(K-out)` 87% and 32% over their per-cell caps once an escaping bug stopped
masking the split, and proposed relocating settled prose out of the row. The
project's standing test for a relocation is the one `f2905c86` applied --
*what here is REFERENCE rather than STATUS?* -- with the operational form *a
verdict already carried elsewhere is reference by construction*. That commit
answered it by hand for one 281-word block. This answers it by measurement,
for a whole cell, so the relocation's size is known BEFORE the design that
enables it is chosen.

It DECIDES NOTHING and it invents no verdict -- the one unrecoverable error
available to a structural round. It reports what the prose already says and
where else each label already appears. A unit carrying no verdict vocabulary
is reported UNMARKED, never guessed.

Three measurements, in increasing order of weight:

  1. VERDICT CLASS per unit, from the unit's own words. SETTLED if it carries
     terminal vocabulary and no live vocabulary; LIVE if it carries live
     vocabulary; MIXED if both; UNMARKED if neither. Word counts per class.
  2. LABEL LOCATION. For every label token the cell cites, whether that token
     also appears in (a) the row's close-it cell, (b) the workbook file(s)
     that own the gap. A token present in the owning section is recoverable
     there whatever the row does with it -- which is what makes `gapdiff`'s
     in-row retention rule a cost rather than a safeguard for that token.
  3. RELOCATABLE ESTIMATE: words in SETTLED units whose every label token is
     already present in the owning section. That is the honest upper bound on
     what a relocation can move without putting any label beyond reach.

Usage (from the repo root):

    python3 notes/scripts/cellcensus.py [gap-key ...] [--units] [--cell status|close]

Default keys are the three D7.4 names. `--units` lists each unit with its
class and its unrecoverable tokens, which is the worklist a relocation pass
would actually follow.

Parsing is not reimplemented: `check-gapmap-cells.py`'s `iter_row_cells` is
the one row parser, `gapmap.py`'s `units()` the one sentence splitter, and
`gapdiff.py`'s `CODE` the one label regex -- all imported by path, so this
census cannot disagree with the gates about what a row, a unit or a label is.
"""

import argparse
import importlib.util
import glob
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
NOTES = os.path.join(ROOT, "notes")


def _load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


GATE = _load(os.path.join(NOTES, "check-gapmap-cells.py"), "_cg")
GM = _load(os.path.join(NOTES, "gapmap.py"), "_gm")
GD = _load(os.path.join(NOTES, "scripts", "gapdiff.py"), "_gd")

# Verdict vocabulary, taken from the corpus's own words rather than invented.
# Terminal = the claim is finished; live = it is still load-bearing. Matched
# case-sensitively on the SHOUTED forms the cells actually use, plus the few
# lowercase spellings that appear, and word-bounded so `CLOSED` does not fire
# on `closure`.
TERMINAL = r"""REFUTED CLOSED SPENT DEAD STRUCK MOOT RETIRED HISTORY EXHAUSTED
PROVEN PROVED DISCHARGED SETTLED DECIDED FALSE IMPOSSIBLE BARRED SWEPT
COMPLETE UNCONDITIONAL""".split()
LIVE = r"""OPEN PINNED UNRESOLVED UNWITNESSED TARGET LEFT REMAINS STILL
OUTSTANDING LIVE""".split()

TERM_RE = re.compile(r"\b(" + "|".join(TERMINAL) + r")\b")
LIVE_RE = re.compile(r"\b(" + "|".join(LIVE) + r")\b")

# gap key -> the workbook file(s) that own its steps. Derived from the gap
# map's own "§ + steps" column; kept explicit because that column's prose is
# not machine-resolvable and a wrong guess would overstate recoverability.
OWNERS = {
    "K-bare": ["pencil/workbook/bare-ext/*.md", "pencil/workbook/K-bare-ext.md",
               "pencil/workbook/K-ins--INSJOINT.md"],
    "K-grid": ["pencil/workbook/grid.md"],
    # (K-out)'s row cites the (OC-5x) block, which is owned by (K-mech);
    # cross-gap citation is normal and a narrower map would report a
    # recoverable token as stranded.
    "K-out": ["pencil/workbook/K-out.md", "pencil/workbook/K-mech.md"],
}
DEFAULT_KEYS = ["K-bare", "K-grid", "K-out"]


def tokens_of(text):
    out = set()
    for m in GD.CODE.finditer(text):
        out.add(m.group(1) + (m.group(2) or ""))
    return out


def classify(unit):
    t, l = bool(TERM_RE.search(unit)), bool(LIVE_RE.search(unit))
    return "MIXED" if (t and l) else "SETTLED" if t else "LIVE" if l else "UNMARKED"


def owner_text(key):
    if key not in OWNERS:
        return None, []
    files, text = [], []
    for pat in OWNERS[key]:
        for p in sorted(glob.glob(os.path.join(NOTES, pat))):
            files.append(os.path.relpath(p, ROOT))
            with open(p, encoding="utf-8") as f:
                text.append(f.read())
    return "\n".join(text), files


def corpus_text():
    """Every workbook file EXCEPT the gap map itself. A token present here is
    recoverable from the corpus whatever the row does with it -- which is the
    test that decides whether `gapdiff`'s IN-ROW retention rule is protecting
    anything, or duplicating a protection the corpus already provides."""
    out = []
    for p in sorted(glob.glob(os.path.join(NOTES, "pencil/workbook/**/*.md"),
                              recursive=True)):
        if os.path.abspath(p) == os.path.abspath(GATE.PATH):
            continue
        with open(p, encoding="utf-8") as f:
            out.append(f.read())
    return "\n".join(out)


SHINGLE = 8


def shingles(text, n=SHINGLE):
    """Normalised n-word shingles. Markdown emphasis and backticks are
    stripped so that a block relocated with its bolding changed still
    matches -- the test is whether the SENTENCE exists elsewhere, not whether
    its formatting does."""
    w = re.sub(r"[*`_>|\\]", " ", text.lower()).split()
    return {" ".join(w[i:i + n]) for i in range(max(0, len(w) - n + 1))}


def dup_fraction(unit, owner_sh):
    """Share of a unit's shingles already present in the owning section. This
    is `f2905c86`'s test -- *a second copy of a settled verdict is reference
    by construction* -- made mechanical. It is EVIDENCE, not a verdict: a high
    score says the words are already elsewhere, and a human still decides
    whether the row needs them."""
    sh = shingles(unit)
    if not sh:
        return 0.0
    return len(sh & owner_sh) / len(sh)


def coarse(toks):
    """Token set at LABEL granularity -- `BE-37(ii)` -> `BE-37`. `gapdiff`
    tracks the finer form, so the two counts differ and both matter: the fine
    one is what the gate enforces, the coarse one is whether the CLAIM is
    findable."""
    return {t.split("(")[0] for t in toks}


def cells_for(key, text):
    for _ln, k, _c1, _c2, kind, cells in GATE.iter_row_cells(text):
        if k == key:
            if kind != "split":
                raise SystemExit(
                    f"({key}) is in the combined fallback — escape its inline-code "
                    f"pipes first (Harness-structure D7.4(c))"
                )
            return cells[0], cells[1]
    raise SystemExit(f"no gap-map row for ({key})")


def census(key, which, show_units):
    text = open(GATE.PATH, encoding="utf-8").read()
    status, closeit = cells_for(key, text)
    cell = status if which == "status" else closeit
    other = closeit if which == "status" else status

    own, own_files = owner_text(key)
    own_toks = tokens_of(own) if own is not None else set()
    other_toks = tokens_of(other)
    corp_toks = tokens_of(corpus_text())
    corp_coarse = coarse(corp_toks)
    owner_sh = shingles(own) if own else set()

    us = GM.units(cell)
    per = {"SETTLED": [0, 0], "LIVE": [0, 0], "MIXED": [0, 0], "UNMARKED": [0, 0]}
    reloc_w = reloc_n = 0
    dups = [0.0, 0, 0]   # weighted dup mass, words at >=50% dup, unit count
    rows = []
    for i, u in enumerate(us, 1):
        klass = classify(u)
        w = len(u.split())
        per[klass][0] += 1
        per[klass][1] += w
        toks = tokens_of(u)
        stranded = sorted(t for t in toks if t not in own_toks)
        dup = dup_fraction(u, owner_sh)
        dups[0] += w * dup
        if dup >= 0.5:
            dups[1] += w
            dups[2] += 1
        movable = klass == "SETTLED" and not stranded
        if movable:
            reloc_w += w
            reloc_n += 1
        rows.append((i, klass, w, toks, stranded, movable, dup))

    total_w = len(cell.split())
    all_toks = tokens_of(cell)
    in_own = sorted(t for t in all_toks if t in own_toks)
    in_other = sorted(t for t in all_toks if t in other_toks)
    in_corp = sorted(t for t in all_toks if t in corp_toks)
    in_corp_c = sorted(t for t in all_toks if t.split("(")[0] in corp_coarse)
    nowhere = sorted(t for t in all_toks if t.split("(")[0] not in corp_coarse)

    cap = GATE.caps_for(key)[0 if which == "status" else 1]
    print(f"=== ({key}) {which} — {len(us)} units, {total_w} words, cap {cap}"
          f"{'  [OVER by ' + str(total_w - cap) + ']' if total_w > cap else ''}")
    print(f"  owning section: {', '.join(own_files) if own_files else 'UNMAPPED'}")
    print(f"  {'class':<10}{'units':>7}{'words':>8}{'share':>8}")
    for k in ("SETTLED", "LIVE", "MIXED", "UNMARKED"):
        n, w = per[k]
        print(f"  {k:<10}{n:>7}{w:>8}{100*w/total_w:>7.0f}%")
    print(f"  labels: {len(all_toks)} distinct tokens")
    print(f"    also in the nominal owning section : {len(in_own):>4} "
          f"({100*len(in_own)/len(all_toks):.0f}%)")
    print(f"    also SOMEWHERE in workbook/ (exact) : {len(in_corp):>4} "
          f"({100*len(in_corp)/len(all_toks):.0f}%)")
    print(f"    ditto at LABEL granularity          : {len(in_corp_c):>4} "
          f"({100*len(in_corp_c)/len(all_toks):.0f}%)   "
          f"<- what `gapdiff`'s rule is protecting, minus what the corpus "
          f"already protects")
    print(f"    also in the row's other cell        : {len(in_other):>4}")
    print(f"    findable NOWHERE outside this cell  : {len(nowhere):>4}")
    print(f"  DUPLICATION vs the owning section ({SHINGLE}-word shingles): "
          f"{100*dups[0]/total_w:.0f}% of the cell's words are already there; "
          f"{dups[2]} units ({dups[1]} words, {100*dups[1]/total_w:.0f}%) are "
          f"≥50% duplicated")
    print(f"  RELOCATABLE (settled AND every token present in the owning section): "
          f"{reloc_n} units, {reloc_w} words = {100*reloc_w/total_w:.0f}% "
          f"→ cell would be ~{total_w - reloc_w} words")
    if nowhere:
        print(f"  tokens findable NOWHERE else ({len(nowhere)}) — a relocation "
              f"must keep these in the row or carry them to its target:")
        print("    " + ", ".join(nowhere[:24]) + (" …" if len(nowhere) > 24 else ""))
    if per["UNMARKED"][1] > 0.25 * total_w:
        print(f"  CAVEAT: {100*per['UNMARKED'][1]/total_w:.0f}% of the cell is "
              f"UNMARKED — these cells state verdicts by label reference rather "
              f"than by the shouted vocabulary this census matches, so SETTLED "
              f"is a LOWER BOUND and RELOCATABLE is a lower bound on a lower "
              f"bound. Read it as 'at least this much', never as a total.")
    if show_units:
        print(f"  {'#':>4} {'class':<9}{'w':>5}{'dup':>6}  stranded tokens")
        for i, klass, w, _t, stranded, movable, dup in rows:
            mark = "MOVE" if movable else "    "
            print(f"  {i:>4} {klass:<9}{w:>5}{100*dup:>5.0f}%  {mark} "
                  f"{', '.join(stranded[:6])}{' …' if len(stranded) > 6 else ''}")
    return 0


def density_table(which):
    """Words per LABELLED RESULT for every row. This is the measurement that
    decides whether a big cell is padded or merely productive, and the
    standard is the cap gate's OWN: its 2026-08-19 bump note says 2 360 words
    carrying 96 labelled results is "~25 words each, at which point further
    compression deletes status rather than redundancy"."""
    text = open(GATE.PATH, encoding="utf-8").read()
    rows = []
    for _ln, k, _c1, _c2, kind, cells in GATE.iter_row_cells(text):
        if kind != "split":
            continue
        cell = cells[0] if which == "status" else cells[1]
        n = len(tokens_of(cell))
        w = len(cell.split())
        rows.append((k, w, n, (w / n) if n else None,
                     GATE.caps_for(k)[0 if which == "status" else 1]))
    print(f"{'row':<16}{'words':>7}{'labels':>8}{'w/label':>9}{'cap':>7}")
    for k, w, n, r, c in sorted(rows, key=lambda x: -(x[3] or 0)):
        print(f"{k:<16}{w:>7}{n:>8}{(f'{r:.1f}' if r else '—'):>9}{c:>7}")
    tw = sum(r[1] for r in rows)
    tn = sum(r[2] for r in rows)
    print(f"\nwhole table: {tw} {which} words / {tn} label tokens = "
          f"{tw/tn:.1f} w/label; the gate's own stated floor is ~25.")
    return 0


def main(argv):
    p = argparse.ArgumentParser(prog="cellcensus.py", description=__doc__.split("\n")[0])
    p.add_argument("keys", nargs="*", default=DEFAULT_KEYS,
                   help="gap keys (default: the three D7.4 rows)")
    p.add_argument("--cell", default="status", choices=["status", "close"])
    p.add_argument("--units", action="store_true",
                   help="per-unit worklist with stranded tokens")
    p.add_argument("--density", action="store_true",
                   help="words per labelled result, every row (no per-cell census)")
    a = p.parse_args(argv)
    if a.density:
        return density_table(a.cell)
    for k in (a.keys or DEFAULT_KEYS):
        census(k, a.cell, a.units)
        print()
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
