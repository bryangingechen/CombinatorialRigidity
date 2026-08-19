# PENCIL doc-split / discipline-distillation — structural rounds (work log)

**Status: COMPLETE — all three slices LANDED 2026-08-19.** **Slice 1** —
§(K-grid) split out of `notes/Pencil-informal.md` into its own file,
`notes/Pencil-informal-grid.md`. **Slice 2** — `notes/Pencil-fanout.md`'s
ordinals-1–19 landed direction history archived to
`notes/Pencil-fanout-archive.md`. **Slice 3** — the phase's research-arc
discipline, invented in-phase and referenced across six files with no
promoted standing home, distilled into the new read-on-demand root manual
**`RESEARCH-ARC.md`** (alongside `CLEANUP.md`, `PHASE-BOUNDARIES.md`; pointer
added to `CLAUDE.md`'s read-on-demand list and to
`.claude/commands/coordinate-phase.md`'s research-shaped-phase step). This is
a **structural** round (file layout / navigability / cross-phase promotion),
not a defect-cleanup round — hence the `Phase22-structure.md`-style name
rather than `-cleanup`; round discipline is `CLEANUP.md`'s all the same
(there is no separate structure-round manual). Slices 1–2 opened and landed
in one session (2026-08-19); slice 3 landed in a follow-up session the same
day. Agreed with the user at the seventh fan-out's close (`notes/Phase39.md`
*Hand-off*). **Next: no queued structural work; the kernel-(K) research step
is UNROUTED, awaiting a pick — see `notes/Phase39.md` *Hand-off*.**

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
- [x] **Slice 2 — archive `Pencil-fanout.md`'s landed direction history.**
  Precedent: `notes/FRICTION.md` → `notes/FRICTION-archive.md` (`88436c0b`) —
  verbatim relocation, live cross-references repointed. The split line was
  coordinator-set at dispatch (not worked out fresh at slice-2 time): the
  adjudication, *Shared mechanics*, the *Landing checklist* and the entire
  seventh fan-out (the worked exemplar) STAY; the first fan-out's specs
  (Direction A/B/C) and every fan-out/direction section for ordinals 1–19
  MOVE. Detail below.
- [ ] **Follow-up, not this round unless folded in:** recompute the *Section
  index*'s §(K-frame)/§(K-chart)/§(K-mech) line ranges, stale after slice 1's
  deletion shifted every row after §(K-grid) by −9 883 lines. Left explicitly
  stale (below) rather than silently trusted; slice 2 touched a different
  file's line ranges and did not fold this in either.
- [x] **Slice 3 — discipline distillation.** Write the new root manual
  `RESEARCH-ARC.md`; per the adjudication, promote six items with
  three-plus waves of evidence (label reservations + minting; serial
  coordinator landing; the gap map as status object; F11's
  driver-per-headline; cap disclosure; mechanical word caps/recompute-not-
  bump), record three one-wave candidates as watched-not-promoted (pointing
  at `notes/dispatch-log.md` F18–F21, not restated), and record three
  genuinely unsettled questions as deferred with the question stated (fan-out
  width; compute/derivation tier split; prose-recon vs compiler-checked
  spike). Replace the duplicated general-rule prose in the six referencing
  files with one-line pointers, per *Lift on promotion*. Detail below.
- [x] **Round CLOSED.**

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

## Slice 2 — Decisions made

- **New file name: `notes/Pencil-fanout-archive.md`.** Matches the
  `FRICTION.md`→`FRICTION-archive.md` precedent (`88436c0b`) exactly.
- **The split line is coordinator-set, not heading-mechanical.** Unlike
  FRICTION.md's `[resolved]` tag, `Pencil-fanout.md`'s sections carry no
  archived/live marker, so the coordinator's invocation prompt named the
  exact boundary: STAYS = *The adjudication that produced this*, *Shared
  mechanics*, the *Landing checklist*, and the **entire seventh fan-out**
  (its own section plus Twentieth/YLOC–Twenty-fourth/CIRR) as the worked
  exemplar a future wave copies from; MOVES = *Why a fan-out now* + Direction
  A/B/C (the first fan-out's specs) and every fan-out/direction section for
  ordinals 1–19 (second through sixth fan-outs, the nine single directions).
  Unlike slice 1's single contiguous range, STAYS and MOVES **interleave** —
  9 STAYS sections and 23 MOVES sections, both preserved in original relative
  order in their respective files (verified: each group's heading-start line
  numbers were already monotonic in the source, so a straight partition-and-
  concatenate needed no reordering).
- **Exact accounting.** Header (lines 1–21) + STAYS body (921 lines) + MOVES
  body (5 279 lines) = 6 221 = the pre-split file's total, cut at heading
  boundaries. New parent = edited header (27 lines, +6 for a short paragraph
  naming the archive plus one restored blank line before the first heading)
  + STAYS body = 948 lines. New archive = new header (36 lines) + MOVES body
  = 5 315 lines. 948 + 5315 = 6263 = 6221 + 6 (header growth) + 36 (archive's
  new header) — accounted in full, no line unexplained.
- **Live cross-references inside the moved/kept text itself, not just
  elsewhere in the tree.** Because STAYS and MOVES interleave, six spots
  needed a same-file "above"/bare-heading reference upgraded to a file-
  qualified one so it resolves after the split: a STAYS section (ZNEQ) cited
  "§'Direction A' above" (MOVED) and, separately, a "fifth fan-out's block"
  item number (MOVED); two MOVES sections each cited "§'Landing checklist'"
  (STAYS) with no file qualifier; one MOVES section said "identical to the
  first fan-out's [mechanics] (top of this file)" — true before the split,
  false after, since "this file" becomes the archive, which has no *Shared
  mechanics* heading of its own; one MOVES section said "this file's own top
  `**Status:**` header", also now false once "this file" is the archive
  (its header is new prose, not the original Status block). All six fixed
  by naming the correct file explicitly; no verdict, label or status word
  touched — content is otherwise verbatim.
- **Mechanical verification (all required, all run — not eyeballed):**
  - *Heading-set diff.* `grep '^## '` on the pre-split file (32 headings) vs.
    the two post-split files combined (32 headings, same multiset) —
    **identical**, confirmed by `diff` on sorted lists, not eyeballing.
  - *Line accounting* — above; confirmed by `wc -l` on all four inputs/outputs.
  - *No dangling references.* Swept the whole `notes/` tree plus the eight
    `.py` drivers that cite `Pencil-fanout.md` by name+section. Repointed
    **62** cross-file citations: `Phase39.md` (6), `Pencil-informal.md` (9,
    incl. one gap-map cell), `Pencil-informal-grid.md` (15), `Pencil-labels.md`
    (25), `ROADMAP.md` (1 row rewrite) and 6 `.py` drivers — plus the six
    same-file spots above — every one verified against the STAYS/MOVES
    partition before touching it (not a blind string replace): a citation
    naming a MOVED heading got `-archive.md`; a citation naming a STAYS
    heading (Landing checklist, Shared mechanics, the adjudication, or
    ordinals 20–24) was left alone.
    Two false-positive traps caught: `notes/Pencil-cleanup.md` and
    `notes/dispatch-log.md` cite several now-moved section names, but both
    are **closed round logs** describing a past state — left untouched, same
    call as slice 1 made for `Pencil-cleanup.md`.
  - `python3 notes/check-gapmap-cells.py` — **0 gap-map row(s) checked
    (changed vs HEAD); all within cap** (the one gap-map cell edited — the
    (K-out) row's file-pointer repoint — changed no cell's *word count*, so
    the change-detector correctly does not flag it; confirmed by inspecting
    the diff directly, not trusting the 0 blindly). `--all` — **27 gap-map
    row(s) checked (full table); all within cap.**
- **`.py` driver scripts touched (6 files, docstring text only).** `gpsa.py`,
  `gadm.py`, `gdesc.py`, `gunif.py`, `glaw.py`, `gbal.py` — every changed line
  is a module-docstring file pointer; `balb.py`/`yloc.py` correctly left
  alone (their sections, Twenty-first/Twentieth, stayed). No code, no
  numeric literal, no figure touched — `git diff --name-only -- '*.py'
  '*.m2'` lists exactly these 6, all comment-only, verified by reading the
  full diff.

## Slice 3 — discipline distillation — Decisions made

- **New file: `RESEARCH-ARC.md` at the repo root**, read-on-demand alongside
  `CLEANUP.md`/`PHASE-BOUNDARIES.md` (pointer added to both `CLAUDE.md`'s
  read-on-demand paragraph and `.claude/commands/coordinate-phase.md`'s
  research-shaped-phase loop step). Not auto-loaded; read when scoping a
  research-shaped phase.
- **The three-tier split is the round's main content, not a formatting
  choice.** A manual presenting all twelve candidate items as settled rules
  would be worse than none, because a reader could not tell which are
  load-bearing. **Ready** (six, three-plus waves each): label reservations +
  minting rule; serial coordinator landing with worktrees deliberately not
  used; the gap map as the phase's status object; F11's driver-per-headline
  claim, with "exhaustive"/"forced"/"the only" their own claim class; cap
  disclosure; mechanical word caps with recompute-not-bump (+ F21's
  target-and-scripted-diff refinement). **Candidates, not yet promoted**
  (one wave, 2026-08-19): the duplicate check against landed Lean and
  concurrent siblings (F20); cross-direction convergence as corroboration
  (F18/F19); the coordinator-predicted-obstruction category plus
  coordinator artifacts needing the subagent verification tier (F19) — all
  three point at `notes/dispatch-log.md` *Findings*, not restated in the
  manual. **Genuinely unsettled**, deferred with the question stated, no
  guidance invented: optimal fan-out width; the compute-licensed /
  derivation-first tier split; when a prose recon beats a compiler-checked
  spike.
- **`notes/dispatch-log.md` untouched, by design** — its Findings (F11,
  F17–F21) are the primary source the manual points at; rewriting them would
  duplicate exactly what this round exists to stop.
- **Lift-on-promotion applied to the six referencing files**, per the
  adjudication's canonical-detail-stays-put rule: `notes/Pencil-labels.md`
  and `notes/Pencil-informal.md`'s gap-map header and
  `notes/scripts/README.md` convention 8 are each the **canonical detail**
  for one promoted item (label reservations; the gap map; cap disclosure
  respectively) — each gained a one-line pointer to `RESEARCH-ARC.md` for the
  cross-phase generalization, with no content removed. `notes/Pencil-fanout.md`'s
  *Shared mechanics* section carried the one genuine **duplicate** — the
  worktree/serial-landing rationale and the "F11 requirement" paragraph,
  both full restatements of the general rule inside a live (non-archived)
  file — trimmed to one-line pointers, the historical fact (exercised twice,
  zero collisions) kept, the rationale removed to its new canonical home.
  `notes/dispatch-log.md` and `.claude/commands/coordinate-phase.md` are
  covered above.
- **`python3 notes/check-gapmap-cells.py`** — 0 gap-map row(s) checked
  (changed vs HEAD); all within cap (the one sentence added to
  `Pencil-informal.md`'s gap-map *header* prose is outside the table, so no
  cell changed).

## Follow-up items (not this round's job)

- Recompute the *Section index*'s §(K-frame)/§(K-chart)/§(K-mech) line
  ranges in `notes/Pencil-informal.md` (shifted −9 883 by slice 1). **Not**
  folded into slice 2 — that file's line ranges are unrelated to
  `Pencil-fanout.md`'s split — so it remains a standing, cheap, dedicated
  one-line follow-up commit whenever someone next reads that table.
- No mathematical content defect was noticed while moving §(K-grid) (slice 1)
  or while sweeping `Pencil-fanout.md`'s cross-references (slice 2) — both
  were mechanical relocations with a boundary/reference audit, not a close
  read of the mathematics, and none was owed either time.
- **One pre-existing, not-this-round defect noticed in passing (slice 2):**
  `notes/scripts/w4/glaw.py`'s docstring cites its own spec as "Seventeenth
  direction — GLAW"; GLAW is the **sixteenth** direction everywhere else
  (`Pencil-labels.md`, the heading itself, `Phase39.md`). Predates this
  round (confirmed by `git diff` showing only the file-pointer changed);
  left verbatim per the "kept the pre-existing typo, fixed only the file
  pointer" precedent (slice 1's `glaw.py` §(K-grid) fix).

## Hand-off / next phase

**All three slices LANDED 2026-08-19; every structural round on PENCIL's doc
set is now COMPLETE.** ROADMAP's doc-split row is ✓ Complete and carries a new
sibling row for this round; this log's *Status* header is the verdict.
`RESEARCH-ARC.md` exists and is linked from `CLAUDE.md` and
`.claude/commands/coordinate-phase.md`. **No structural work is queued.**
The phase's own next concrete task — the kernel-(K) research step — is
**UNROUTED, awaiting a pick**; see `notes/Phase39.md` *Hand-off* (not
duplicated here), which also carries, unchanged, ZNEQ's `σ > 0`-everywhere
disproof hunt awaiting user adjudication and excluded from the standing
2026-08-07 delegation's pool.
