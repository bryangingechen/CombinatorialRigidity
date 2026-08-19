# PENCIL doc-split — structural round (work log)

**Status:** in progress. **Slice 1 LANDED 2026-08-19** — §(K-grid) split out of
`notes/Pencil-informal.md` into its own file, `notes/Pencil-informal-grid.md`.
**Slice 2 NOT started** — archiving `notes/Pencil-fanout.md`'s landed direction
history. This is a **structural** round (file layout / navigability), not a
defect-cleanup round — hence the `Phase22-structure.md`-style name rather than
`-cleanup`; round discipline is `CLEANUP.md`'s all the same (there is no
separate structure-round manual). Opened and slice 1 executed in the same
commit, per the coordinator's dispatch this session; agreed with the user at
the seventh fan-out's close (`notes/Phase39.md` *Hand-off*).

## Why this round

Phase 39 (PENCIL) stays open (`notes/Phase39.md` *Current state*); the
kernel-(K) research arc's workbook, `notes/Pencil-informal.md`, had grown to
**21 851 lines** by the seventh fan-out's close, of which **§(K-grid) alone
was 8 553 — 39%**, six times the next-largest section (§(K-out), 1 827 lines)
— the coordinator's own measurement motivating the round, taken from a stale
*Section index* snapshot (the actual boundary, re-measured at heading level
for this slice, is **9 883 lines**; see *Decisions made*). §(K-grid) is also
the section three of the seventh fan-out's five directions (YLOC, BALB, AGLU)
wrote into, and its gap-map cell has regressed from a changelog into a
current-state cell and back **five times** now (four before this round, per
`notes/check-gapmap-cells.py`'s docstring, plus the `4edd2143` recompute this
phase already logged). `notes/Pencil-fanout.md` is 6 221 lines, of which
roughly 5 100 is landed direction history (fan-out specs + their landing
write-ups) rather than live dispatch scoping — slice 2's target. The *Section
index*'s line ranges go stale on every landing and must be recomputed by hand
each time; a **file** index for the largest, most volatile section retires
that cost permanently for it.

## Task list

- [x] **Slice 1 — move §(K-grid) to its own file.** Verbatim relocation:
  heading, standing notation, *Steps G0–G97* with their Verification /
  Confidence / What-would-change-this blocks. The *State of (K)* gap map
  (incl. §(K-grid)'s own row) stays whole in `Pencil-informal.md`; repoint
  every cross-reference that named §(K-grid)'s old *location* (not its
  labels, which resolve via `Pencil-labels.md` regardless of file). Detail
  below.
- [ ] **Slice 2 — archive `Pencil-fanout.md`'s landed direction history.**
  Precedent: `notes/FRICTION.md` → `notes/FRICTION-archive.md` (`88436c0b`) —
  verbatim relocation, live cross-references repointed. Scope to work out at
  slice-2 time: which of the file's sections count as "landed direction
  history" (the per-direction dispatch specs plus their landing write-ups,
  roughly 5 100 of the file's 6 221 lines) versus the live dispatch-scoping
  material (the non-collision mechanics, the landing checklist, the label
  reservation table) that should stay in the live file. Not started.
- [ ] **Follow-up, not this round unless folded in:** recompute the *Section
  index*'s §(K-frame)/§(K-chart)/§(K-mech) line ranges, stale after slice 1's
  deletion shifted every row after §(K-grid) by −9 883 lines. Left explicitly
  stale (below) rather than silently trusted.
- [ ] **Discipline distillation** (immediately after slice 2, per
  `notes/Phase39.md` *Hand-off*) — a separate round, not this one's task list;
  named here only for the ordering.

## Decisions made

- **New file name: `notes/Pencil-informal-grid.md`.** Sorts next to its parent
  `Pencil-informal.md` in a directory listing, matching the coordinator's own
  suggestion; no reason found to deviate.
- **Exact boundary: lines 11212–21094 of the pre-split `Pencil-informal.md`**
  (`## §(K-grid)` through the line immediately before the next `## ` heading,
  `## §(K-frame)`) — **9 883 lines**, cut at heading boundaries so no
  editorial judgement about ownership of a blank line was needed. This is the
  true current size; the round-opening estimate of 8 553 was a stale
  *Section index* read (the index's own row said `10410–19680`, 9 271 lines,
  itself stale — the index goes stale on every landing, which is exactly this
  round's motivation). The new file's header + purpose paragraph is additional
  prose, not part of the relocation; the moved body is byte-identical to what
  stood in `Pencil-informal.md`.
- **What did not move, unconditionally.** The *State of (K)* gap map
  (`Pencil-informal.md` lines 205–451, incl. §(K-grid)'s own row, line 249) —
  byte-identical, confirmed by `git diff` showing exactly two hunks in
  `Pencil-informal.md`: the *Section index* row (line 83) and the deleted
  range. The *Shared dictionary*, every other §(K-*) section, and the *Section
  index* table itself (apart from §(K-grid)'s own row) are untouched.
- **Mechanical verification (all required, all run — not eyeballed):**
  - *Nothing lost.* `sed -n '11212,21094p'` extracted exactly 9 883 lines;
    the assembled new file is 9 883 (body) + 34 (new header/preamble) = 9 917
    lines; `Pencil-informal.md` dropped from 23 983 to 14 100 lines
    (23 983 − 9 883 = 14 100, confirmed by `wc -l`).
  - *Label-set diff.* Captured every `(GR-nn)`/`(GR-nn′)` token (79) and every
    `Step(s) Gnn[–Gmm]` token (137) in the pre-split file; recomputed both
    sets over the two post-split files combined. GR-label set: **identical**
    (79 = 79, empty symmetric difference). Step-token set: 137 → 138, the one
    addition being `Steps G0–G97` from this file's own new header sentence
    (a deliberate new mention, not a moved or duplicated original token) — no
    original token lost or duplicated.
  - *No dangling location references.* Grepped the whole `notes/` tree for
    `§(K-grid)`; audited every hit against the label/location distinction
    (a label — `(GR-nn)` — resolves via `Pencil-labels.md` regardless of
    file; a location claim — the word "workbook" adjacent to `§(K-grid)`, or
    an explicit `` `notes/Pencil-informal.md` `` pointer next to it, or a raw
    line range — asserts a specific file and had to be repointed). Found and
    fixed **41** genuine location claims, verified by diffing (not
    eyeballing) each pattern's count: **25** instances of the literal string
    `workbook §(K-grid)` (`notes/Pencil-fanout.md` ×5, `notes/scripts/
    README.md` ×18, `notes/scripts/w4/{grid,yloc}.py` ×1 each); **12**
    instances of an explicit `` `notes/Pencil-informal.md` §(K-grid) ``
    pairing (11 in driver docstrings —
    `notes/scripts/w4/{aglu,cflank,gexist,gcap,gorient,gdev,gridwit,gridcol,
    gunif,packmm}.py` ×1 each plus a second occurrence in `grid.py` — and 1
    more inside `notes/Pencil-fanout.md`'s Step-0 pin paragraph); **1**
    ASCII-typo variant `workbook S(K-grid)` in `glaw.py` (kept the pre-existing
    typo, fixed only the file pointer); **1** more in `notes/Pencil-fanout.md`
    naming the file in the opposite word order — "§(K-grid) Steps G29–G33,
    `notes/Pencil-informal.md`)" — before the section name; and **2** inside
    `notes/Phase39.md` itself (one `` (`notes/Pencil-informal.md`) ``
    parenthetical in *Current state*, one "the workbook sections" generic
    claim in *Decisions made*).
    Every fix repointed to `` `notes/Pencil-informal-grid.md` ``, keeping the
    surrounding sentence otherwise verbatim. Left alone (confirmed
    label-only, no location claim): bare `§(K-grid) (GR-nn)` citations, bare
    `§(K-grid)'s pool/residual/route/census/driver` mentions, and every
    citation inside the *State of (K)* gap map itself (which does not move
    and is not edited for this reason or any other). `notes/Pencil-cleanup.md`
    and `notes/dispatch-log.md` carry several `§(K-grid)` + line-number
    mentions too, but every one of them is a **historical** record of a
    *closed* round/logged incident (word counts and line numbers as they
    stood on 2026-08-13) — archival, not live navigation, so left untouched.
  - `python3 notes/check-gapmap-cells.py` — **0 gap-map row(s) checked
    (changed vs HEAD); all within cap** (confirms the gap map's live-diff
    surface is untouched by this commit). `--all` — **27 gap-map row(s)
    checked (full table); all within cap** (confirms nothing was
    inadvertently broken elsewhere in the table). The script itself is
    unmodified (`git status` shows no change to it), as expected — it reads
    only `## State of (K)`, which did not move.
- **Section index: now stale, explicitly, for three rows.** §(K-grid)'s row
  is now `` | §(K-grid) | `notes/Pencil-informal-grid.md` | ... | `` — a file
  reference, per the task. Every row **before** §(K-grid) in the table is
  unaffected (all above line 11212). Every row **after** it —
  **§(K-frame)/§(K-chart)/§(K-mech)** — had its line range shift by exactly
  −9 883 (they were already possibly stale before this commit, per the
  index's own standing caveat: "if one looks wrong, grep the `## §(…)`
  heading"). **Do not trust those three ranges**; recompute is a follow-up,
  not folded into this slice (the task named only §(K-grid)'s own row).
- **`.py` driver scripts touched (12 files, comment/docstring text only).**
  Every changed line, verified by inspecting the full `git diff -- '*.py'`,
  is inside a module docstring, a print-string, or a one-line comment citing
  where the mathematics lives — no logic, no numeric literal, no code path
  changed. `git diff --name-only -- '*.py' '*.m2'` is **not** empty (12 files
  listed), so the figure-invariance discharge is stated explicitly rather
  than by an empty diff: the change cannot move any figure because it
  changes no computation, confirmed by reading every changed line above.

## Follow-up items (not this commit's job)

- Recompute the *Section index*'s §(K-frame)/§(K-chart)/§(K-mech) line
  ranges (shifted −9 883 by slice 1). Cheap; folding it into slice 2's own
  commit (which will shift ranges again by removing `Pencil-fanout.md`
  history, though that file's ranges are separate from `Pencil-informal.md`'s)
  is as good a time as any, or a dedicated one-line follow-up commit.
- No mathematical content defect was noticed while moving §(K-grid) — this
  was a mechanical relocation with a boundary/reference audit, not a close
  read of the section's 9 883 lines of mathematics, and none was owed.

## Hand-off / next phase

**Next concrete task: slice 2** — archive `notes/Pencil-fanout.md`'s landed
direction history to a new `notes/Pencil-fanout-archive.md` (name to confirm
at slice-2 time against the file's actual section boundaries — live scoping
material vs. landed history is not yet split by heading the way FRICTION.md's
`[resolved]` tag made that file's split mechanical), following the
`88436c0b` precedent: verbatim relocation, live cross-references repointed,
mechanical nothing-lost + label-set-diff checks before commit. After slice 2
closes this round (flip the ROADMAP row, compress this log's *Current state*
to a verdict), the discipline-distillation round opens next (`RESEARCH-ARC.md`
— detail in `notes/Phase39.md` *Hand-off*).
