# PENCIL doc-split / discipline-distillation — structural rounds (work log)

**Status: ALL THREE ROUNDS COMPLETE — first round slices 1–3 LANDED 2026-08-19;
second round slices 4–5 LANDED (slice 4 2026-08-19, slice 5 2026-08-20); third
round, the phase-note compression pass, **slice 6 LANDED 2026-08-26**.
Nothing structural is queued; the phase's next concrete task is the kernel-(K)
research pick (`notes/Phase39.md` *Hand-off*).** **Slice 1** —
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
*Hand-off*).

**Second round, opened by the 2026-08-19 post-wave adjudication**
(`notes/Phase39.md` *Current state*: "Clear the two structural items first"),
numbered as a continuation (slices 4–5) rather than a new file, since this
round is more of the same structural work, not a different kind. **Slice 4**
— `notes/Phase39.md`'s own dated adjudication bullets covering the archived
ordinals 1–19 moved verbatim to the new `notes/Pencil-adjudications.md`,
same precedent as slice 2. **Slice 5, LANDED 2026-08-20** — the harness
move-down round, paying all five debt items the sixth-to-eighth fan-outs
accumulated (`notes/scripts/README.md` *Harness debt*, now **BOTH ROUNDS
PAID**), including the adjudicated `closure.Gauss` → `exactcore` move: `meet` →
`lambda`, six `zneq` devices → `ocon`, seven `aglu` devices → `gridcol`,
`tree_triple` → `grid`, `Gauss` → `exactcore`, each re-exported from its old
home so no consumer changed and **no recorded figure moved** (18 driver modes
re-run; the round's write-up is in that file's *Harness debt*). **Next: nothing
here — the phase's next concrete task is the kernel-(K) research pick
(`notes/Phase39.md` *Hand-off*, "Queued behind the wave").**

## The relocated reference blocks — the index `notes/Phase39.md` points at

**EIGHT blocks, relocated verbatim from `notes/Phase39.md` between 2026-08-27 and
2026-09-01**, each because it is **stable reference, not status** — it changes only
when something is *added* to it, never when a gap's status moves. (Block 8 is the
one exception to the "never when a gap's status moves" reading, and it is a
deliberate one: it is the *per-landing attribution* of a thread whose status the
note keeps — see its own section for why that split is the right cut.) That is the
disposition the phase note's own *Doc debt* watch item prescribes moving, instead of
another compression fold of *Decisions made* (three prior folds recovered 2–5 lines
each, because the note is forward-weighted and the forward part is what grew). **No
cap was ever bumped and nothing was deleted**; the note keeps a pointer to each.
**Read these once per session.**

| # | block | relocated | what it carries |
|---|---|---|---|
| 1 | *Conventions and canonical homes* | 2026-08-27 | direction-code conventions; which doc owns which content |
| 2 | *Gates for any continuation* | 2026-08-28 | which gate fires on which file type; the figure-invariance discharge |
| 3 | *The question and the opening recon* | 2026-08-28 | the phase's question; R1/R2/R3's still-binding clauses |
| 4 | *Durable negatives and deliberate non-goals* | 2026-08-28 | the do-not-re-run / do-not-re-open list |
| 5 | *What the recent landings closed* | 2026-08-29 | BZAVOID / ZJACOB / ZSHEAR / GHWIT / GMINM closes |
| 6 | *The unselected candidate continuations* | 2026-08-29 | leads (b)–(f); ranking lives in the fan-out losers sections |
| 7 | *Citations — the phase's verified bibliography* | 2026-09-01 | every verified source; **a new source is added HERE** |
| 8 | *The (BE-14) thread — per-landing detail* | 2026-09-01 | which direction proved which sub-clause of the three sides, with its labels |

The one line that stays in `notes/Phase39.md` rather than moving here: the **State of
(K)** gap map in `notes/Pencil-informal.md` is the phase's status object, authoritative
for every status word — and it is read with `python3 notes/gapmap.py`, never
`sed`/`grep` (one row is one 22 000-character line).

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
- [x] **First round CLOSED.**
- [x] **Slice 4 — the phase-note doc split.** Move `notes/Phase39.md`
  *Current state*'s dated adjudication bullets covering the archived
  ordinals 1–19 (2026-08-05…07, 2026-08-07, 2026-08-12, 2026-08-13, and the
  2026-08-19 sixth-fan-out dispatch) verbatim to the new
  `notes/Pencil-adjudications.md`. Precedent and shape: slice 2 above. Detail
  below.
- [x] **Slice 5 — the harness move-down round (LANDED 2026-08-20).** One pass
  paying all five debt items (`ocon.meet` → `lambda`; `aglu.py`'s seven
  combinatorial devices → `gridcol`; six `zneq` primitives → `ocon`;
  `gridwit.tree_triple` → `grid`; `closure.Gauss` → `exactcore`), each with a
  re-export from its old home, so every consumer's import line is untouched.
  Acceptance test was figure invariance, not the build: 18 driver modes re-run
  in the foreground, 12 byte-identical against pre-edit baselines and 6 checked
  against §3's recorded figures. Record: `notes/scripts/README.md` *Harness
  debt* → *The move-down round* (not restated here).

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

## Slice 4 — phase-note doc split — Decisions made

- **New file name: `notes/Pencil-adjudications.md`.** Sibling of
  `notes/Pencil-fanout-archive.md`, same precedent
  (`FRICTION.md`→`FRICTION-archive.md`, `88436c0b`): verbatim relocation,
  live cross-references repointed, search-target only.
- **Exact scope, coordinator-set at dispatch:** the five dated bullets in
  `Phase39.md` *Current state* covering the archived ordinals 1–19 — the
  2026-08-05…07 (second–fifth fan-outs), 2026-08-07 (delegation
  adjudication), 2026-08-12 (seventh-direction delegation), 2026-08-13
  (phase-shape adjudication + ninth–fourteenth selections) and the
  2026-08-19 sixth-fan-out dispatch (ordinals 15–19) bullets. The last of
  these was not named by date in the dispatching agent's illustrative list
  (which enumerated only the four pre-08-19 bullets) but matches the
  same stated principle — "covering the archived ordinals 1–19" — and its
  inclusion is confirmed by the hand-off's own arithmetic check ("the three
  2026-08-19 bullets" remaining): the file carries **four** 2026-08-19-dated
  bullets (sixth-fan-out, seventh-fan-out, post-wave, eighth-fan-out), so
  exactly one of them had to move for three to remain. Left in place: the
  five standing kernel GO/NO-GO constraints (2026-07-24; the two 2026-07-30s;
  2026-08-02; 2026-08-05 reproducibility) and the three still-live
  2026-08-19 bullets (seventh-fan-out, post-wave, eighth-fan-out) — none of
  which cover archived material.
- **Exact boundary: lines 65–103 of the pre-split `Phase39.md`** (the
  `- **2026-08-05…07` bullet through the end of the sixth-fan-out bullet),
  cut at bullet boundaries, confirmed blank at line 104 both sides. 39 lines
  moved, replaced by a single 7-line pointer bullet in `Phase39.md`.
- **Mechanical verification (all run, not eyeballed):**
  - *Verbatim diff.* `sed -n '65,103p'` of `git show HEAD:notes/Phase39.md`
    (pre-commit) against the corresponding lines of the new file's bullet
    body: **identical**, confirmed by `diff` returning no output.
  - *No dangling references.* Grepped the whole tree for
    `Pencil-adjudications.md` (resolves to the three files that cite it —
    `Phase39.md`, `Pencil-structure.md`, `CLAUDE.md` — all intentional, no
    stray) and for unique phrases from the moved bullets (e.g.
    "seventh-direction delegation", "phase-shape adjudication, then the
    ninth") outside the two files touched: **zero** hits, so no other file
    in the tree cited these bullets by content and needed repointing.
  - `python3 notes/check-gapmap-cells.py` — **0 gap-map row(s) checked
    (changed vs HEAD); all within cap** (this slice touches no gap-map
    cell). `--all` unaffected (no `.py`/`.m2` file touched, no gap-map
    content moved).
  - No `.lean`, `.tex`, `.py` or `.m2` file touched — no build/lint/
    blueprint/figure-invariance gate applies; the empty
    `git diff --name-only -- '*.py' '*.m2'` **is** the figure-invariance
    discharge.
- **Line count: `Phase39.md` 596 → 581.** The verbatim bullet move alone
  nets 596 → 564; the same commit also fixed two pre-existing stale
  hand-off/status sentences it found while re-reading this file's status
  surfaces per the split's own caution (the top-status "next two concrete
  commits" wording, and a since-superseded "four remaining returns"
  eighth-fan-out banner), which added lines back. The file does not land
  under its ~500-line tripwire from this slice alone — see *Hand-off*'s
  honest note on why. New file `Pencil-adjudications.md` is 76
  lines (39 moved + a 34-line header/provenance preamble + the `---`
  separator).
- **Forward/finished ratio.** Unharmed: the moved material was entirely
  *Current state* (a finished/settled section), so the forward sections
  (*Hand-off*, the open kernel items) are untouched and their share of the
  note only grows as *Current state* shrinks.

## Slice 6 — phase-note compression — Decisions made (LANDED 2026-08-26)

**What fired it.** A context-usage measurement over six `/coordinate-phase`
sessions: `notes/Phase39.md` held at ~500 lines from 07-25 to 08-15, then went
660 (08-20) → 882 (08-25) → **1 500 (08-26)**, i.e. **3× the `notes/CLAUDE.md`
tripwire**, with *Decisions made* (328) plus the Status header (155) outweighing
nothing the note needed forward. Every landing commit was `+50…100 / −20…30` on
it, and in one session writes to this single file consumed 138 399 characters of
tool arguments — the largest consumer of that session's context. Slice 4's own
hand-off had named the remaining work and declined to improvise it: *"Closing the
rest would need a genuine compression pass on live prose … a different,
not-yet-commissioned kind of work."* This slice is that pass, commissioned.

**What moved, and the rule it moved under.** Governing rule: **relocate, never
delete**, and cut only verified duplication.

- **Ordinals 20–44's dated adjudication bullets → `notes/Pencil-adjudications.md`,
  verbatim** (385 lines, relocation verified byte-identical by `md5` on the
  extracted block before and after). That file's title and header now cover
  **ordinals 1–44**; it is sectioned by move round (1–19 / 20–44). Slice 4's
  precedent exactly, at the other half of the same content.
- **Kept in `Phase39.md` *Current state*:** the five standing GO/NO-GO
  constraints (2026-07-24, 07-30 ×2, 08-02, 08-05) verbatim, plus a
  **compressed** statement of three live things whose verbatim now lives in the
  companion — the widened research-pick delegation and its three selection
  criteria, the direction-A pivot rule's pre-adjudicated stop clause, and the
  measured session-headroom calibration. The last of these had **no other home
  in the tree** (not `dispatch-log.md`, not the coordinator command), which is
  why it was compressed rather than cut.
- **Cut as verified duplicate**, each checked against the named home before
  removal: the sixth/seventh/eighth fan-out completion paragraphs and their
  per-direction verdicts (`Pencil-fanout{,-archive}.md`); the ZJACOB / ZSHEAR /
  BZAVOID / OGEOM / GMINM / GHWIT landing recaps and successor lists (same, plus
  the workbook sections each names); both probe paragraphs
  (`Pencil-informal.md` §(K-bare-ext) *Step BE1* carries the tier semantics;
  `Pencil-strategy.md` §4.7 the C3 pricing); the wider-candidate-list and
  harness-debt recitals (`Pencil-strategy.md` §8, `notes/scripts/README.md`
  *Harness debt*); the "nothing awaits adjudication" pair (both discharged); the
  structural-rounds paragraph (this file); and `## The question` /
  `## Opening recon verdicts`, which duplicated `ROADMAP.md` §39 against
  `notes/CLAUDE.md`'s own canonical-home table.
- **Merged, not cut:** *Hand-off*'s target-ordered list and its separate "three
  carried items" bullet list were two rankings of the same three objects; they
  are now one ranked list. The two route-σ blockquotes (one per section, each
  saying the other carried the other half) are now one.
- ***Decisions made* collapsed to one-line verdicts**, the four (BE-14)-thread
  entries kept at prose length because the next task leans on them. Four
  landings (BATTAIN, OGEOM, GMINM, GHWIT) had **no** *Decisions made* entry at
  all — their record lived only in *Hand-off* prose that this slice cut — so
  entries were added for them from the coordinator's own landed words.

**Stale facts reconciled** (current reading kept, stale one fixed): **52
directions / ordinals 1–44** against `ROADMAP.md`:157, replacing "all 47", "46
directions on `hK`" and "45"; the doubled `**OGEOM is LANDED****OGEOM is
LANDED**` from a botched sed; the *"pin it when the tight side closes"* (K-res)
deferral, **retired** by the 2026-08-26 adjudication rather than "stale"; and
*Harness debt*'s **four** outstanding items against the phase note's "one".

**Cross-references repaired in the same commit** (the slice-2 lesson): the
`Pencil-fanout.md` header's selection-provenance rule; seven per-direction
*Selection provenance* citations in `Pencil-fanout.md` (GFLIP…GMINM); three in
`Pencil-labels.md`; four **pre-existing slice-4 dangles** in
`Pencil-fanout-archive.md` that had cited moved 1–19 bullets since 2026-08-19;
and `notes/CLAUDE.md`'s own `Pencil-adjudications.md` entry.

**Result: 1 500 → 554 lines**, forward (*Current state* 97 + *Blockers* 60 +
*Hand-off* 169 = **326**) outweighing finished (*Decisions made* **93**); Status
header 155 → **58**. Still
above the ~500 tripwire, and honestly so: the standing-constraint block, the
next-task spec, the three ranked carried items and the do-not-re-open list are
all live. The watch item is recorded in `Phase39.md` *Blockers* — ~10 landings
re-breach it at the observed per-commit rate, and the gate is the landing
checklist's step 5 plus a one-line *Decisions made* entry per landing.

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

**First round (slices 1–3) COMPLETE 2026-08-19; second round opened the same
day (post-wave adjudication, "Clear the two structural items first") and
slice 4 has now LANDED too. `RESEARCH-ARC.md` exists and is linked from
`CLAUDE.md` and `.claude/commands/coordinate-phase.md`.**

**Slice 4's honest line-count result.** `notes/Phase39.md` moved from 596 to
581 lines — still above the ~500-line tripwire. The verbatim bullet move
alone nets 596 → 564; the commit also fixed two pre-existing stale
hand-off/status sentences caught while re-reading this file's status
surfaces (the top-status "next two concrete commits" wording, and a
since-superseded "four remaining returns" eighth-fan-out banner that
pre-dated this slice and contradicted the table right below it), which
added lines back. None of this is a defect in the slice's execution (the moved
text is verified byte-identical, no cross-reference dangles): the note grew
past the 580-line figure this round's own hand-off cited as current, adding
a fourth 2026-08-19-dated bullet (the post-wave adjudication) and the
eighth-fan-out landing detail *after* that figure was written, and all of
that growth is **live** state a fresh session must read — not archivable
ordinal-1–19 material — so this slice's scope (verbatim relocation of
settled selection history, plus the status-surface fixes it turned up) has
no further lever on the gap. Closing the rest would need a genuine
compression pass on live prose (e.g. the *Kernel-(K) research arc*
paragraph or the eighth-fan-out hand-off detail), which is a different,
not-yet-commissioned kind of work — flagging it rather than improvising it.

**Slice 5, the harness move-down round, LANDED 2026-08-20** — the five debt
items paid in one pass, `closure.Gauss` → `exactcore` included, with no
recorded figure moved. ROADMAP's doc-split row carries this slice's record;
this log's *Status* header is the verdict.

**Slice 6, the phase-note compression pass, LANDED 2026-08-26** — and it
**discharges the item slice 4's hand-off above declined to improvise** (*"a
genuine compression pass on live prose … a different, not-yet-commissioned kind
of work"*). `notes/Phase39.md` 1 500 → 554, forward-weighted, ordinals 20–44's
dated bullets relocated verbatim; per-slice record in *Slice 6* above.
**With it the structural work is finished**, and the phase's next concrete task
— the kernel-(K) research pick — is live; see `notes/Phase39.md` *Hand-off*.

## Conventions and canonical homes

**Relocated verbatim from `notes/Phase39.md`'s `**Status:**` header, 2026-08-27**,
at the BEARFULL landing. The reason is recorded rather than implied: three
consecutive landings had each compressed *Decisions made* with real deletions and
each recovered only 2–5 lines, because the note is **forward-weighted and the
forward part is what grew** (339 forward vs 104 finished). These two paragraphs
are **stable reference, not status**, so they were the right thing to move — and
moving them is what the note's own watch item prescribed instead of bumping the
gate's caps. `notes/Phase39.md` keeps a pointer plus the one line that genuinely
is status (the gap map is authoritative).

**Conventions.** Direction codes are multi-letter and topic-tagged from the
fifth fan-out on (`notes/Pencil-labels.md` (L5)); grandfathered single letters
are re-used across dates, so **always date those**. The doc-split and
discipline-distillation rounds are both COMPLETE (`notes/Pencil-structure.md`;
`RESEARCH-ARC.md` is the promoted manual). Both architecture probes are landed
(KBARE-FALSIFY, C3-AVOID). File layout: `Molecule/Pencil.lean` split into
`Molecule/Pencil/{Statement,Arms,Motive,Chart,Engine,Reseed,Witness,Steer,Pair,
Pair2,Escape,Base}.lean`; per-leaf history `notes/Phase39-design.md`.

**Canonical homes — read these, not a summary of them.** The **State of (K)**
gap map in `notes/Pencil-informal.md` is the phase's status object and is
authoritative for every status word; `notes/Pencil-informal-grid.md` owns
§(K-grid); `notes/Pencil-W4-informal.md` owns the W4 (`hcontract`) residual arc;
`notes/Pencil-strategy.md` owns the option board (§8) and the unpriced
§9 shelf **(ZH-1)–(ZH-6)**, which stays ineligible;
`notes/Pencil-fanout.md` owns dispatch specs and landing write-ups;
`notes/Pencil-adjudications.md` owns the archived verbatim user calls.

## Gates for any continuation

**Relocated verbatim from `notes/Phase39.md`'s *Hand-off* section, 2026-08-28**, at
the BSHARP prep, when the note's line gate stood at 580/580 with a landing due. It
is **stable reference, not status** — the same list every session, changing only
when a gate is added — which is what the note's own watch item prescribes moving
instead of bumping the cap. The note keeps a pointer.

Gates for any continuation: `lake build` (warning-clean) + `lake lint` when `.lean` is touched;
`blueprint/verify.sh` + `blueprint/lint.sh` (vocabulary gate bans "stratum"/"strata") when `.tex`
is touched; **when `notes/scripts/` is touched**, figure invariance proportionate to what the
commit modifies (`git diff --name-only -- '*.py' '*.m2'` empty ⇒ that check IS the discharge,
stated in the commit message) — canonical home `notes/scripts/README.md` *Hard rule — figures do
not move*; a **symbolic** dispatch adds `notes/scripts/m2/README.md`;
**`notes/check-gapmap-cells.py` before any gap-map edit** — the cap-exhaustion hazard this
guards against is now a standing, harness-wide rule (`notes/scripts/README.md` §4 convention
8, promoted 2026-08-19 after a second instance; not restated here); bump a row's cap only
with a dated one-line reason, never a silent regrowth.

## The question and the opening recon

**Relocated verbatim from `notes/Phase39.md`, 2026-08-28**, at the recompute that followed
the BSHARP landing, when the note stood at 578/580 lines with three landings already queued
behind it. It is **stable reference, not status**: the question itself has been stated once
in `ROADMAP.md` §39 since the phase opened, and R1/R2/R3's three still-binding clauses have
not moved since 2026-07-23. That is what the note's own *Doc debt* watch item prescribes —
*"what here is reference rather than status?"*, not a fourth compression fold of *Decisions
made*, which the three preceding folds had already reduced to 2–5 recovered lines each. Caps
were not bumped and nothing was deleted; the note keeps a pointer.

**The question is stated once, in `ROADMAP.md` §39** (the intersection stratum:
each body's hinges both concurrent *and* coplanar, i.e. a pencil of lines through
a point in a plane; in the `G²` molecular reading, every atom's bond-star
coplanar — sp²/planar-bonded atoms; the trivial direction is pencil ⇒ panel per
body, so the content is the **lower bound**, and the all-bodies form implies every
mixed version by rank lower-semicontinuity) — **not restated here**. Two clauses
that section does not carry: the condition only bites at bodies of degree `≥ 3`,
and the two literature hunts after the opening one (2026-07-30 rigidity-side,
2026-08-05 Δ-matroid-side) are both MISSes for **complementary** reasons
(§(K-Δ)) — **this is new mathematics**.

**Opening recon verdicts R1–R3** (landed 2026-07-23) are one-lined in
`ROADMAP.md` §39; the full record, grounding and the W0–W5 decomposition are
`notes/Phase39-design.md`. Three clauses still constrain statements: **R1** pins
the statement in the Phase-35 containment model + `ExtensorThroughPoint` (dual of
`ExtensorInPanel`), satisfiable for every graph and self-dual on-stratum via
`screwComplementIso` (§(K-clos) (AC-1)); **R2**'s queued-warmup claim is
*bar-joint-side* and **false** for body-hinge on dense graphs; **R3**'s three open
cores (outer Thm-5.6 strip-extend, Case-I glue Claim 6.4, Case III Claim 6.12
span break) are what W3–W5 were built against.

## Durable negatives and deliberate non-goals

**Relocated verbatim from `notes/Phase39.md`'s route-σ block, 2026-08-28**, at the same
recompute and for the same reason — a standing *do not re-run / do not re-open* list is
**stable reference, not status**, changing only when a direction closes something new — so
it belongs beside the *Conventions* and *Gates* blocks relocated here on 2026-08-27/28. The
only edit is formatting: these paragraphs sat inside the note's route-σ blockquote, and the
`> ` markers are dropped here. **The route σ candidacy itself is status and stays in the
note**; only its trailing do-not-re-open paragraphs moved. The note keeps a pointer.

**Two durable negatives from the 2026-08-07 adjudication — do not re-run:** §4.6's
shortlist is **partially superseded** for the tight stratum (U2 delivered by (GR-16)'s
reduction; U3's negative-form insight already exploited); the symbolic meta-option
("upgrade §(K-Λ) via M2") is **landed, not pending** (`m2/lambda0.m2`) — only §5.3 item
(i) remains, ruled out by §5.3's own local-frame feasibility boundary.
**Not open, and not re-litigated per wave:** the **(FR-6) follow-ons** ((ii)/(iv)
un-commissioned; **(iii)** struck by (OC-17)), the unselected leads (b)–(f) (below,
§"The unselected candidate continuations"), and route σ / W4. **Deliberate non-goals — do not
re-derive, re-sweep, or re-open:** (Λ0), (Λ1), the `g₁₄` clause, §(K-ind),
§(K-Δ), §(K-clos)'s field question,
§(K-ann)'s settled batch ((ANH-1)–(ANH-6), (SD-6)) and §(K-out)'s settled batch
((OC-1)–(OC-7); pinned, disjoint pools) — including "does the polarity generalize?",
(D2)'s far block, POOL-G/POOL-S, a counting/matroid route to (OUT)'s hypothesis ((OC-3)
refutes the whole class), or `lambda.py`'s figures (slice **S3**'s carve-out is spent).

## What the recent landings closed

**Relocated verbatim from `notes/Phase39.md`'s *Hand-off* section, 2026-08-29**, at the
recompute that followed the BWIN landing, when the note stood at 575/580 lines with the
user's next pick to record in both the header and the hand-off. A standing
**do-not-re-open** list is **stable reference, not status** — it changes only when a
direction closes something new — which is exactly the disposition the four blocks above
already have, and what the note's own *Doc debt* watch item prescribes instead of a fifth
compression fold. Each item's own gap-map row carries the same close, and the gap map is
authoritative for status; caps were not bumped and nothing was deleted. The note keeps a
pointer.

**DO NOT RE-OPEN — what the recent landings closed.** From **BZAVOID**: the
forced-degeneration cap as a refutation route for **any** graph ((BE-15); cap-free for the
**triangle** mechanism, the general one MEASURED only — a proof of **(BE-23)(ii)** would
restore it in full and is the disproof side's highest-value single search); the landed
Phases-24–26 `G²` apparatus, whose general-position gate is the **literal negation** of the
pencil condition ((BE-17)); and the **transversality/dimension count** ((BE-16)(iv)). From
**ZJACOB**: the determinantal / scheme-theoretic package is a **conservation law** — it
converts expected codimension *into* structure with **no theorem producing it** over a
non-generic base, so any route getting properness from a codimension count, a Jacobian
criterion or Cohen–Macaulayness is answered by §(K-jac) before it starts. From **ZSHEAR**:
`Q(r̃) ≠ 0` is `PGL(4)`-invariant, so **no gauge-fixing can ever supply it**. From
**GHWIT/GMINM**: per-matching (b′) at the constant 2 is FALSE and the `min_M` reading is
PROVEN — **do not re-open either**.

## The unselected candidate continuations

**Relocated verbatim from `notes/Phase39.md`'s *Current state* section, 2026-08-29**, at the
same recompute and for the same reason. This list is **reference, not status** by its own
last sentence — *"the current ranking of what a wave did not pick is
`notes/Pencil-fanout.md`'s own losers sections, not this list"* — so what a fresh session
needs from `notes/Phase39.md` is the pointer, and the ranking is read where it is live. The
`notes/Pencil-fanout-archive.md` references to *"the unselected leads (b)–(f)"* are dated
records of what a user did **not** select and name no section, so they do not dangle; the one
live section-naming reference, in §"Durable negatives and deliberate non-goals" above, is
repointed here in the same commit. The note keeps a pointer.

The other candidate continuations, unselected — items (a)/(g) **DONE** (second-fan-out
directions M and R), each with a canonical home carrying the detail: **(b)** **(K-wit)**, the
pitch route's single live form at companion splits (§(K-Λ)) — its (OC-8) residue now reduces
to chart irreducibility (**DONE**, CIRR) plus input (a), which itself **FACTORS** (**DONE**,
ZNEQ) into a dominated half and the target-rank half (OSCHU, landed 2026-08-19; OQRANK,
landed 2026-08-25); **(c)** the **W4 build**, decomposed and buildable, **PARKED** by the
Lean hold; **(d)** the companion-length dichotomy frame (§(K-dom) *D7*) + the unprobed
`k ≥ 4` parallel-edge item (§(K-pure) *P4*); **(e)** §(K-Λ) item (vii)'s residual, since
LTWO a named, non-empty, floor-classified family; **(f)** strategy §4.6's shortlist,
**partially superseded** for the tight stratum, U3 still unrun. **The current ranking of
what a wave did not pick is `notes/Pencil-fanout.md`'s own losers sections, not this list.**

## Citations — the phase's verified bibliography

**Relocated verbatim from `notes/Phase39.md`'s *Citations* section, 2026-09-01**, at
the BDECOR prep, when the note stood at 576/580 lines with an in-flight block to add.
It is **stable reference, not status**: a bibliography changes only when a direction
verifies a new source, never when a gap's status moves — the same disposition as the
six blocks relocated here on 2026-08-27/29, and what the note's own *Doc debt* watch
item prescribes (*"what here is reference rather than status?"*) instead of another
fold of *Decisions made*, which three prior folds had already reduced to 2–5 recovered
lines each. Caps were not bumped and nothing was deleted; the note keeps a pointer.

**`CLAUDE.md` *Referencing prior work* still binds here, unmoved:** this is the
canonical home for the phase's verified attributions, and **a direction that verifies
a new source adds it to this section in its landing commit**. The two fuller
bibliographies this section deliberately does not duplicate keep their own homes —
`notes/Phase39-design.md` §"(K) literature hunt" and `notes/Pencil-informal.md`
§(K-Δ) *Sources*.

- Katoh–Tanigawa, *A proof of the molecular conjecture*, Discrete Comput. Geom. **45** (2011) —
  the KT pointers in this note (Cor. 5.7, Thm 5.5, Lemma 6.13, the Case I/II/III split) are
  transcribed from `notes/Pencil.md`'s 2026-07-23 survey against the project-canonical source
  (ROADMAP *References*); pointer verification history: `notes/Phase35.md` *Citations*,
  `notes/Phase23-cleanup.md`. The (K-tight) re-pin (2026-08-02) verified pp. 681–691 directly
  against the `.refs` copy — workbook §(K-tight) *Step 0*. **KT Thm 4.9 is cited by the
  *molecular* side only**: the pencil induction is `Graph.pencil_reduction`, not
  `minimal_kdof_reduction` (§(K-ind) *Verification*).
- Jordán 2016 (MSJ Memoirs 34) — checked silent on the pencil stratum in the 2026-07-23 survey,
  re-confirmed by the 2026-07-30 (K) literature hunt.
- The 2026-07-30 (K) literature hunt (option C) verified six project-new sources against the
  `.refs` copies / primary metadata, all MISSes on the (K-tight) crux — White–Whiteley 1987 and
  1983, Whiteley 1988 and 1999, Schulze–Tanigawa, Garamvölgyi. **The full verified bibliography,
  with per-source venue data and the reason each is a MISS, is `notes/Phase39-design.md` §"(K)
  literature hunt" — the canonical home; it is not duplicated here** (same pointer discipline as
  the Δ-matroid bibliography below).
- White–Whiteley 1987 (op. cit.) §2 — verified against the `.refs` copy (2026-08-04, the
  (K-slide-cl) development): Proposition 2.6, Corollary 2.7, Theorem 2.18 (the technique the
  tetrahedral collapse instantiates), Corollary 2.19 (Tay's count).
- **The 2026-08-06 direction-T landing** (§(K-grid)) verified one project-new source against
  publisher metadata (Smith ScholarWorks record + arXiv listing), cited as context only (nothing
  in §(K-grid) is derived from it): **Gilbert–Polster–Tymoczko**, *Generalized splines on
  arbitrary graphs*, Pacific J. Math. **281** (2016), no. 2, 333–364 (arXiv:1306.0801).
  Whiteley 1996 (op. cit. below) is re-used for the matroid-union context, no new section pointer.
- Whiteley, *Some matroids from discrete applied geometry*, in Matroid Theory
  (Bonin–Oxley–Servatius, eds.), Contemp. Math. **197**, AMS 1996, 171–311 — §12.2's screw-center
  description of body-hinge motions verified against the `.refs` copy (2026-08-04, the (K-pitch)
  development); volume/pages verified against AMS metadata.
- The 2026-08-05 (K-slide-comb) pass reuses the project-canonical **Edmonds 1965** (verified in
  Phase 12) and the **Tutte 1961 / Nash-Williams 1961** tree-packing pair (Phase 13). One
  project-new source, verified against publisher metadata: **Grünbaum**, *Acyclic colorings of
  planar graphs*, Israel J. Math. **14** (1973) 390–408, DOI 10.1007/BF02764716. Brooks' theorem
  is cited by name only (classical).
- **The 2026-08-05 broad class-uniformity recon** (`notes/Pencil-strategy.md` §4.6) verified one
  project-new source against publisher metadata + the arXiv preprint listing, **no section pointer
  asserted**: **Scott**, *Grassmannians and Cluster Algebras*, Proc. London Math. Soc. **92**
  (2006), no. 2, 345–380, DOI 10.1112/S0024611505015571 (preprint arXiv:math/0311148) — the
  finite-type Grassmannian classification. Its `D₄`/`A_{n−3}` labels state the *refuted* proposal
  only, never a load-bearing step; **White–Whiteley 1987** (below) is re-used by name for the pure
  condition, with no new section pointer.
- **The 2026-08-05 Δ-matroid literature hunt** (§(K-Δ)) verified ~20 project-new sources —
  Bouchet, Dress–Havel, Wenzel, Gelfand–Serganova, Borovik–Gelfand–White, Vince(–White), Rincón,
  Jin–Kim, Baker–Jin, Geelen–Iwata–Murota, Bouchet–Cunningham, Koana–Wahlström, Moffatt, Chun et
  al., Kung, and Cruickshank–Jackson–Jordán–Tanigawa (arXiv:2508.11636, the corroborating
  negative). **The full verified bibliography, with its two caught hallucinated attributions and
  one deliberately omitted volume number, is `notes/Pencil-informal.md` §(K-Δ) *Sources* — the
  canonical home; it is not duplicated here.**

## The (BE-14) thread — per-landing detail

**Relocated verbatim from `notes/Phase39.md`'s `**Status:**` header, 2026-09-01**, at the
BSPREAD prep. This is the block the note's own *Doc debt* watch item **named in advance** as
the next relocation candidate — *"the `**Status:**` header's own per-landing detail
paragraph, which becomes reference the moment the next direction starts; do that instead of
a fold"* — and the moment arrived when BSPREAD was prepped. The prediction was also
quantitatively right: the header stood at **505/525** words with 20 spare, an in-flight
block needs ~55–70, and three consecutive folds before it had recovered only 2–5 lines
each. Relocating this paragraph took the header to **420/525**, buying **105** words.

**Why this is reference and not status, when the thread itself is very much live.** The cut
is between *where the three sides stand* — which the note keeps, in three clauses — and
*which direction proved which sub-clause, with its labels and its HIT shapes*, which is
attribution. Attribution has two canonical homes already (`notes/Pencil-fanout.md` §"<CODE>"
for the landing write-up, and the note's own *Decisions made* one-liners), so the header was
a third copy; and the **`(K-bare)` gap-map row is authoritative for every status word**
regardless. Nothing was deleted and no cap was bumped; `notes/Phase39.md` keeps a pointer
plus the status clauses.

**The paragraph, as it stood at the BPEEL landing (`94af7fdd`) and the session-close commit
(`ae78b432`):**

**WHERE THE (BE-14) THREAD STANDS** — the 2-cut composition lemma (S-mark) is (BE-14)'s
only open step, and it has three sides (details **not restated here**). **THE EAR SIDE:** (α) **CLOSED**;
(β) **PROVED AT THE WINDOW BY A CLASS THEOREM** (BWIN, with BSHARP's (b1)/(b2) and BRULE's
(b3)) on the 87-of-91 domain — **MODULO the side conditions (S1)/(S2)** ((BE-57)(iv)),
vacuous at every drawn piece but **not theorems**; residue per-shape outside the window
plus the `π_u = π_v` corner. **THE GENERAL-PIECE
SIDE:** the internal R-node is **DESCRIBED** and its achievable decorations **REDUCED TO
EARS** — a **product** of ear chains, one per topological branch, **modulo the proviso
`G`** ((BE-64)/(BE-66)) — and **half (B)'s CLASS quantifier is now ONE NUMBER PER PEEL**
(BPEEL, ordinal 54, `recon-opus`, HIT shapes 2/4/5): the good locus is Zariski-open on an
irreducible chart, hence **dense or empty**, and no branch crosses a 2-cut, so the two
sides are **independent**, sharing only the flag pair ((BE-69)/(BE-70)) — which **retires
the exhaustiveness obligation** without claiming any mechanism list is complete (F11).
**`G` is CLOSED on (CH-1)'s class** ((BE-72)); **(BE-66)(iv)'s stated REASON is refuted**
(F12, corrected at source), its conclusion re-derived from (BE-32)(+) + (BE-22)(vi)
((BE-73)). Residue: the **uniformity** of that number over pieces, the **flag base** off
the no-adjacent-hubs class ((BE-65)(i)/(BE-68)), and **cross-cut-only forcing**, whose
obligation is the **SPREAD step** — now the last gap in half (B)'s discharge. **THE THIRD
SIDE:** cross-pair welding ((BE-28)(i)), untouched. **The phase-boundary consequence is
reported, NOT acted on** (next block).

**Reading it later.** Every label in it resolves in `notes/Pencil-informal.md`
§(K-bare-ext); the direction codes resolve in `notes/Pencil-fanout.md`. Treat the paragraph
as a snapshot dated 2026-09-01, **not** as a live status surface — if it disagrees with the
gap map, the gap map wins.
