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

**2026-08-19 bump (direction GBAL).** Entry 5 (per-shape admissibility)
lands as a HIT: six new theorems (GR-49)-(GR-54) -- the z-form bijection,
the orientation criterion, the weight criterion, the parity theorem, the
splitting lemma and the balance theorem itself -- are appended to the
Proven list and the ledger-entry-5 sentences in both cells are rewritten
to PROVEN, genuinely growing the row past its prior cap. Caps bumped to
the 2026-08-19 recompute's own size (1504 / 759 words) plus ~15%
headroom: 1730 / 873.

**2026-08-19 third bump (the eighth fan-out, `(K-grid)`).** The row absorbed
**eighteen** new theorems in one day -- (GR-79)-(GR-84) (GTMPL),
(GR-85)-(GR-90) (GFLOW) and (GR-91)-(GR-96) (GCOLL) -- taking the section from
(GR-1)-(GR-78) to (GR-1)-(GR-96), and three of them are status moves rather
than additions (attack (c)'s AA-glue case settled at an exact `n_hub`
boundary; (b′) given a proven `n`-free constant; (GR-64)(R2) refuted and
(GR-64)(R1) delivered). The status cell was honestly recomputed **twice**
across those landings before this bump -- 1706 -> 1730 words while absorbing
GTMPL's six labels (the pre-existing content down ~13%), then a further ~35
words off the oldest (GR-1)-(GR-74) material at GCOLL's -- and each landing
also paid for itself by trimming its own block (GFLOW's twice). What is left
is 2360 words carrying **96** labelled results, ~25 words each, at which point
further compression deletes status rather than redundancy. Cap set at that
recompute's own size plus ~15%: **2715 / 935**. Recompute first, twice, then
bump -- the order this docstring mandates.

**2026-08-26 bump (direction GMINM), `(K-grid)` close-it 935 -> 985 --
deliberately TIGHT.** The row absorbed four labels ((GR-125)-(GR-128)) and,
with them, a distinction it did not previously carry: (b') has THREE
readings -- per-matching, `min_M` of the difference, and the LEDGER's own
difference-of-minima -- which are pairwise inequivalent, and the arc spent
four consecutive directions attacking the first while the consumers run on
the third. Naming all three is what the row is for, and it is irreducible.
Recomputed TWICE before bumping, per the order this docstring mandates: the
GHWIT landing absorbed a whole direction at flat size (108 -> 112 words),
and this landing's own clause went 192 -> 144. The residual is +24. Cap set
at the recompute's own size (959) plus ~2.7%, NOT the ~15% headroom the
earlier bumps used -- the tight setting is deliberate, so the next landing
on this row must recompute again rather than coast on headroom (the F21
lesson: a cap bounds growth but cannot express purpose).

**2026-08-19, `(K-out)` promoted out of the default (eighth fan-out).** The
section absorbed **eleven** new theorems in one day -- (OC-29)-(OC-34) from
direction OSCHU and (OC-35)-(OC-39) from direction SIGZ -- taking it from
(OC-1)-(OC-28) to (OC-1)-(OC-39). Its status cell was honestly recomputed
**twice** in the same day before this bump: 649 -> 431 words of pre-existing
content at SIGZ's landing (a 34% reduction), then a further ~65 words off the
oldest (OC-1)-(OC-25) material at OSCHU's. What is left is 828 words carrying
39 labelled results, i.e. ~21 words each -- comparable to `(K-grid)`'s density,
and further compression would start deleting status rather than redundancy. Cap
set at that recompute's own size plus ~15%: **950 / 873** (the close-it cap
matches `(K-grid)`'s, the cell being at 497). This is the docstring's
"row has genuinely grown" case, not a substitute for the recompute -- which was
done first, twice.

**2026-08-19 second bump (direction GLAW, same day).** Six more theorems
(GR-55)-(GR-60) land on attack (a') -- the deviation normal form, the
SPLIT identity/one-inequality criterion, the SDR exchange calculus, the
exhaustive stratum census, the per-matching refutation and the named
residual input (Y) -- appended to the Proven/Refuted lists, and the
close-it cell's (a') clause is rewritten from its old sticking-case
description to the input-(Y) formulation; only the status cell exceeds
its prior cap (1769 words). Bumped to this recompute's own size
(1769 / 797 words) plus ~15% headroom: 2035 / 873 (close-it left as-is,
still under its prior cap).

**2026-09-02, `(K-bare)`: a bump PROPOSED and WITHDRAWN -- the case this
docstring's order does NOT cover.** Direction BDOUBLE recomputed the row
honestly while absorbing a full direction (1472 -> 1546 words; ~110 words of
pre-existing prose compressed away against ~186 added; label preservation by
scripted set-diff, 129 codes in, 144 out, ZERO dropped) and then added a
SPECIAL_CAPS entry at 1630 / 150. The coordinator **withdrew the entry** in a
follow-up the same day; the recompute stands, and the row passes the generic
1600 cap at 1546 with the entry removed (verified by running the gate both
ways).

Why, and it is a distinction worth having in writing: **every other entry in
SPECIAL_CAPS was added because a row had EXCEEDED its cap** -- `(K-grid)` at
2360 against 2035, `(K-out)` at 828 against the 700 default, `(K-grid)`'s
close-it at 959 against 935 -- and each recorded a *density* argument (~21-25
words per labelled result, "further compression deletes status rather than
redundancy") establishing that the recompute was exhausted. This row was
**compliant**: 1546 under 1600, 54 words spare, and no density argument was
made. Bumping a compliant row buys headroom for a landing that has not
happened, which is exactly what the F21 lesson names -- and the `(K-grid)`
close-it bump had already drawn that conclusion, setting a **deliberately
tight** +2.7% "so the next landing on this row must recompute again rather
than coast on headroom". The rule this leaves: *recompute first, twice, then
bump* presupposes an overflow to bump for. **No overflow, no bump** -- if 54
words of headroom is genuinely the pointless-recompute case, the answer is a
further recompute with an explicit target, not a higher ceiling.
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
# **2026-09-08 bump (direction BSTEER), the first `K-bare` entry.** The row is
# now a 228-label index over section (K-bare-ext)'s 170 steps, and BFOUR
# measured its label-density floor one landing earlier: 219 labels in 1,592
# words, 7.27 words per label, after three compression passes whose last bought
# 12 words. BSTEER's honest recompute is 1,592 -> 1,690 words for 9 new labels
# (~11 words each, BELOW the row's own average density) at 7.41 words per label,
# and holding the old 1,600 combined cap would force 7.02 -- under one verdict
# word per label, with `gapdiff.py` forbidding any drop. Capped at the
# recompute's own size plus ~15%, the `(K-grid)`/`(K-out)` mechanism: 972 / 972,
# combined 1,944. NOT a waiver -- the next landing states its own floor.
# **2026-09-08 second `K-bare` bump (direction BRANKV), and it states its floor
# as the previous entry demanded.** BGPROP's recompute took the row to 1,893
# words / 241 labels (7.85 each) with **51** words of headroom -- which its own
# hand-off flagged as not being headroom at all, since a landing costs ~200.
# BRANKV recomputes again (six blocks, real word cuts, `gapdiff.py` verifying
# 0 DROPPED) and still lands at 2,185 words for 9 new labels, 8.74 words each:
# the row is an index over 250 labels and 194 steps, and compression is past
# the point where it removes redundancy rather than status. Capped at this
# recompute's own size plus ~15%: 1,257 / 1,257, combined **2,514**, leaving
# ~330 words -- about one and a half landings, deliberately more than the last
# bump left. **A bump-per-landing is not a strategy, and the standing proposal
# is a ROW SPLIT** -- `(K-bare)` proper against a `(K-bare-ext)` continuation
# row, on the `(K-res)`/`(K-ins)` precedents. The parser supports it (one key
# per row, `KEY_RE` above), but it is a structural change to the phase's single
# status object and is the coordinator's to authorize, NOT a landing's to take:
# the proposal with its word counts is in the BRANKV write-up in
# `notes/Pencil-fanout.md`.
# **2026-09-08 THIRD `K-bare` bump (coordinator, at BEFOURP's landing) -- and it
# is the trigger the coordinator reserved, fired and then DECIDED AGAINST THE
# SPLIT, with the reason recorded because it reverses that trigger's own
# premise.** The trigger was set at `424f93dc` as *"a third bump becoming
# necessary -- at that point the row is being re-priced per landing rather than
# maintained, and the split becomes the cheaper option"*. It fired: BEFOURP's
# honest recompute lands at 2,483 words / 269 labels (9.23 each) with **31**
# words left. But the premise was set on the row's LEVEL and is wrong on its
# GROWTH. The proposed split moves ~24 labels / ~330 words into a `(K-bare)`
# proper row and leaves ~245 labels in a `(K-bare-ext)` continuation that grows
# at the SAME ~100-300 words per landing -- so it buys about two landings of
# relief for a repoint pass across ROADMAP, the phase note, the strategy board,
# every fan-out write-up and `gapdiff.py`'s key inside ~30 recorded reproduce
# commands, i.e. churn against recorded evidence, which the harness's own
# *invocation paths are frozen* rule exists to prevent. Two landings of relief
# is not worth that, and it is not what the trigger assumed it was buying.
# **So: bumped to this recompute's size plus ~15%, 1,428 / 1,428, combined
# 2,856** (~370 words of headroom), and the split stays DECLINED with its
# costing intact in `notes/Pencil-fanout.md`. **The real lever, if this
# recurs, is neither a bump nor a split: it is RELOCATION** -- the row is a
# summary whose per-label detail already lives in section (K-bare-ext), and
# this phase's standing doc remedy is *relocation or merger, never a fold*.
# Every recompute so far has been a COMPRESSION (rewording inside the cell),
# which is why the floor keeps rising: 7.27 -> 7.41 -> 7.85 -> 8.74 -> 9.23
# words per label across five landings. A relocation pass -- settled verdicts
# out of the cell, pointers in -- is a cleanup-round item and would reset that
# density rather than re-price it. **Do not bump a fourth time without doing
# the relocation pass first.**
SPECIAL_CAPS = {
    "K-bare": {"status": 1428, "closeit": 1428},
    # gap-key -> {"status": cap, "closeit": cap}. Combined-remainder fallback
    # (ambiguous pipe split) uses the sum of the two.
    "K-grid": {"status": 2715, "closeit": 985},
    "K-out": {"status": 950, "closeit": 873},
}


def _key_of(col1):
    """Stable per-row key: the first `(xxx)` token in column 1, else the
    trimmed column-1 text itself (rows like `escape criterion` have no
    parenthesized code)."""
    m = KEY_RE.search(col1)
    return m.group(1) if m else col1.strip().strip("`*").strip()


def iter_row_cells(text):
    """Yield `(lineno, key, col1, col2, kind, cells)` for every data row of the
    *State of (K)* gap-map table, in file order (`lineno` 1-based).

    `kind` is `"split"` for a clean 4-column row (`cells == [status, closeit]`)
    or `"combined"` for a row whose columns 3/4 carry stray unescaped pipe(s)
    (`cells == [status_plus_closeit]`) -- see the docstring's *Table shape*.
    Cell text is raw (not stripped). This is the ONE parser for the table:
    `table_rows` below counts words on top of it, and `notes/gapmap.py` (the
    read-only slice reader) prints slices of it, so both agree on what a row,
    a key and a column are.
    """
    lines = text.splitlines()
    in_section = False
    in_table = False
    for lineno, line in enumerate(lines, start=1):
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
        col2 = line[pos[1] + 1 : pos[2]]
        key = _key_of(col1)
        if len(pos) == 5:
            status = line[pos[2] + 1 : pos[3]]
            closeit = line[pos[3] + 1 : pos[4]]
            yield lineno, key, col1, col2, "split", [status, closeit]
        else:
            # stray unescaped pipe(s) inside columns 3/4 -- don't guess the
            # split, cap the combined remainder instead.
            combined = line[pos[2] + 1 : pos[-1]]
            yield lineno, key, col1, col2, "combined", [combined]


def table_rows(text):
    """{key: ("split", status_words, closeit_words) | ("combined", words)}
    for every data row of the *State of (K)* gap-map table."""
    out = {}
    for _lineno, key, _col1, _col2, kind, cells in iter_row_cells(text):
        if kind == "split":
            out[key] = ("split", len(cells[0].split()), len(cells[1].split()))
        else:
            out[key] = ("combined", len(cells[0].split()))
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
