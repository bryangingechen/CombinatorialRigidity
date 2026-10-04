# Phase 40 cleanup round 4/5 — `40-simplify`, the deep simplification recon (work log)

**Status:** in progress (opened 2026-10-04). Round 4 of the five post-Phase-40 cleanup rounds. Their
order, stops and the PI's decisions are in `notes/Cleanup40.md`, and `.claude/autopilot/queue.toml`
is the authority for which rounds are done. The round is a read-only Opus recon over the pencil
surface, looking for bigger simplifications (`notes/Cleanup40.md` §2 *Round 4*). Seven recon tasks
each commit GO / NO-GO verdicts with commit estimates, to their own file,
`notes/Phase40-simplify-verdicts.md`. Task 8 writes Stop 2 (`NEEDS_PI`), the round's one planned
stop; then the items the PI sanctions land, and task 11 closes. Tasks 1 (the liveness map), 2 (the
reduction layer), 3 (node shapes), 4 (the open ears), 5 (re-proofs) and 6 (the producers) are done.
**Next concrete task:** task 7 (G), the remaining long proofs (Opus, docs only). Round manual:
`CLEANUP.md`.

## Autopilot: for the PI

No entry yet. Task 8 writes Stop 2 here: newest entry first, dated, headed with its status. The
PI's answer goes below it, in an entry of the PI's own.

## Current state

**Round 4 is open** (2026-10-04, a docs-only commit). The verdicts are in
`notes/Phase40-simplify-verdicts.md`, one subsection a task. Task 1 (L) has landed: the liveness
map, its verdicts, and the pinned dead clusters handed to tasks 2–4 by name (*Task 1*). Task 2 (R)
has landed: the reduction layer's shape and fifteen verdicts, two of them PI calls (`1a`, design
§6's Lean; `a2`, a headline signature) (*Task 2*). Task 3 (N) has landed: eighteen verdicts on the
nodes outside that layer, two of them conditioned on `1a` (*Task 3*). Task 4 (E) has landed: the
open ears are four arguments, not one; one GO inside the first (`q1a`), `a7` kept, and `c9`'s halves
to retire (*Task 4*). Task 5 (A) has landed: three re-proofs to remove (`q2a`–`q2c`), `b1` after
`r1`, half of `a3`, and `q2d` handed to task 6 (*Task 5*). Task 6 (P) has landed: one tail for #4
and #6 (`a5`), each cut case's two branches as one assembly (`a6`, and Theorem55's, `a6a`), and no
classification lemma (`q2d`) (*Task 6*). Nothing is mid-stream. The task list is
complete for the recon (tasks 1–8).
Task 9 slices the landings after Stop 2, and task 11 closes.

**Verified at the open** (the Lean tree is `0b260626`'s and the blueprint `30e79461`'s; neither has
changed since round 3's close):
- Whole-project `lake build` green, 3003 jobs: 0 `warning:`, 0 `error:` and 0 `failed to cache
  artifact` lines. `lake lint` green.
- `#print axioms` on all 19 `formalization.yaml` main results gives `[propext, Classical.choice,
  Quot.sound]`. Round 3's harness was diffed against the yaml's `declaration:` and `file:` fields
  (19 names in order, 14 imports: identical), copied to `scratch/40-simplify/Axioms.lean`
  (gitignored) and run with `lake lean`. Its output is round 3's close's, byte for byte apart from
  the harness's own path. Re-run it the same way at the close.

**The surface**, as round 1 set it (`notes/Cleanup40.md` §2 *Round 1*):
- the Lean: `Molecular/Molecule/Pencil/**`, now 42 files and 33 691 lines; Phase 40's edits in 26
  Lean files outside it (`git diff --stat c9d26ef9^ 91fcd24a -- CombinatorialRigidity/`), with
  rounds 1–2's moves and additions; and, for task 1, every declaration the two chapters pin
  (Phase 39 put some in `Induction/ForestSurgery/`, e.g. `Graph.pencil_reduction`);
- the blueprint: `pencil.tex` (1 589 lines) and `main-component.tex` (5 696), plus Phase 40's nodes
  in `deficiency.tex`, `rigidity-matrix.tex`, `molecular-induction.tex` and `panel-layer.tex`
  (`notes/Phase40-cleanup.md` *Scope*).

## Scope and standing rules

From `notes/Cleanup40.md` §1–§2, restated only as far as a task needs them.

- **Read-only recon.** Tasks 1–9 are docs commits. Each edits this log, its verdicts file
  (`notes/Phase40-simplify-verdicts.md`, which these rules bind), and the next-task pointer
  in ROADMAP's queued-rounds bullet and `notes/Cleanup40.md`'s header (`CLAUDE.md`, F17); tasks 8
  and 9 also the other status surfaces. No Lean, no blueprint TeX, no `formalization.yaml`,
  no `queue.toml`. A probe or spike goes in `scratch/40-simplify/<task>/` (gitignored) and runs
  with `lake lean <file>`, never `lake env lean`. `git status` is clean apart from the commit's
  own files.
- **Route questions get compiler-checked spikes** (`notes/coordinate-phase-rescue.md` §6). Build
  the candidate composition with `sorry` at each gap, and record the exact kernel-checked residual
  goals, not a prose verdict.
- **Evidence.** A claim about a declaration comes from its statement and body, never its docstring
  (`CLAUDE.md` *Docstrings are not evidence*). Liveness is the Lean call chain (`CLEANUP.md`
  *Liveness*): task 1's closure here, and trial deletion with a whole-project build at landing;
  never grep or `\uses` alone.
- **No statement moves in the recon.** A verdict may propose a headline signature change, or a
  change to a blueprint statement's strength. Only the PI's sanction at Stop 2 lets one land
  (`notes/Cleanup40.md` §2, *All five rounds*).
- **Prior evidence stands unless a task brings a new argument.** Round 1's task 17 (a
  `Fin.succAbove`-general split-off ear nets no shorter) and task 24 (no `_three`/`_four`
  unification); round 2's residual shared tail (about 13 lines a hub, left); round 3's eight
  recommendations, which task 8 presents as written unless a task here changes a premise.
- **A verdict** is one entry in its task's subsection of the verdicts file, at most five lines:
  `**<id>, <name>: GO**` (or NO-GO); one sentence of why; the commit estimate (commits, rung, ⚠Z
  for the fragility zone); what it changes (a headline signature, a blueprint statement's strength,
  the dependency graph, or nothing a reader sees); any verdict it depends on; its evidence (read,
  measured, or a spike's residual). The detail goes in the task's commit message.
- **Gates for tasks 1–9.** `git diff --stat` shows docs only. This log stays under ~500 lines,
  forward-weighted, with a **Status:** header under 300 words and *Decisions* entries of at most 8
  lines. `notes/check-phase-note.py`'s name pattern skips `Phase40-*.md`, so run its `parse` and
  `offenders` on this file directly, as the open did. No local machine paths in the diff or the
  message.
- **Rungs.** The recon tasks are Opus (`notes/Cleanup40.md` §2 *Round 4*). A landing's rung is
  its verdict's: Opus in the fragility zone (`.claude/commands/coordinate-phase.md` *Fragility
  zone*), otherwise rung-mapped.

## Input IDs

`notes/Cleanup40.md` §2 *Round 4* lists the round's inputs, one line each, and this log names them
by their position there. Each input has one owner task, which writes its verdict; other tasks may
read it. Round 3's `r1`–`r8` are recommendations already: task 8 presents them, and task 1 answers
the one question `r1` left open, whether to delete its 29 off-headline names.

- `a1`–`a7`, round 1's candidates: `a1` the one-ended chain-side degree pin; `a2` the six
  `[DecidableEq β]` binders; `a3` the finsum rewrite; `a4` `pencilPair_of_habitat_ncard_eq_four`;
  `a5` `Pair2.lean`'s #4/#6 tails; `a6` `Arms.lean`'s `|C| = 0`/`|C| = 1` split; `a7`
  `Graph.X0Attains.of_closedEar`.
- `b1`–`b2`, round 2's: `b1` `.compl` against `ᶜ` in the two hubs; `b2` the merged hub's `hne`.
- `m1`–`m7`, round 3's *Moved* lines: the six missing `\uses` edges and the unfilled pair node, in
  that list's order.
- `c1`–`c9`, round 3's structural candidates, in that list's order (`c4` is the "…and its
  statement" line, `c8` the four-pin nodes, `c9` the caller-less toolkit halves).
- `r1`–`r8`, round 3's build-or-leave recommendations, as numbered there.
- `q1`–`q3`, the coordinator's starting questions: `q1` the open ears, `q2` `Pencil/` against
  `AlgebraicInduction/`, `q3` the Lean that feeds neither headline.
- Added by the tasks: `1a`, `1b`, `1c-i` and `1c-ii` are task 1's hand-ons (a)–(c) to task 2. A
  new finding takes the ID of the input it bears on, with a letter (`q3a`, `c3a`).

## Lemma checklist (the round's task list)

One commit per task, in this order. Each line names the inputs it owns; its commit names its
verdicts.

- [x] **1. L — the liveness map** (`q3`, `b2`, and `r1`'s deletion question; Opus, docs). The
  closure of the 19 main results, the off-closure clusters, the verdicts and the hand-ons are in
  the verdicts file, *Task 1*.
- [x] **2. R — `pencil.tex`'s reduction layer** (`a2`, `a4`, `m1`–`m5`, `c2`–`c4`, design §6,
  task 1's hand-ons; Opus, docs). The shape and the verdicts are in the verdicts file, *Task 2*.
- [x] **3. N — node shapes outside the reduction layer** (`a1`, `m6`, `m7`, `c1`, `c5`–`c8`, task
  1's hand-ons; Opus, docs). Which side moves where a node and its pins disagree, or a node bundles
  results: the verdicts are in the verdicts file, *Task 3*.
- [x] **4. E — the open ears** (`q1`, `a7`, `c9`, with task 1's sizes; Opus, docs; two spikes).
  One argument or several, and if one, what shared statement: the reading and the verdicts are in
  the verdicts file, *Task 4*.
- [x] **5. A — where `Pencil/` re-proves** (`q2`, `b1`, `a3`; Opus, docs; five spikes). What
  `Pencil/` re-proves of `Theorem55.lean`, `Meet.lean` and the project's mathlib mirrors, with the
  hubs' `ᶜ` and the degree-sum pair: the reading and the verdicts are in the verdicts file,
  *Task 5*.
- [x] **6. P — Phase 39's producers** (`a5`, `a6`, and task 5's `q2d`; Opus, docs; four spikes).
  Whether a recorded cross-proof duplication admits a shared lemma that nets shorter: the reading
  and the verdicts are in the verdicts file, *Task 6*.
- [ ] **7. G — the remaining long proofs** (round 1's §C screen, now structural; Opus, docs). The
  question: is any long proof longer than its argument, now that round 3 has written the argument
  down? Re-rank the surface's proofs by span at the open's tree (round 1's method: header to the
  next column-0 line). Walk the top ten not owned elsewhere: the open-ear steps (#9 in `Orbit.lean`,
  and SHORT's two) are task 4's, `_four` task 2's (`a4`), and #4/#6 (`Pair2.lean`) and #8
  (`Arms.lean`) task 6's. Of round 1's ranking that leaves `_three`, the two `Witness.lean` proofs,
  #5 (`Pair.lean`) and #7 (`GenericTriangle.lean`); the re-rank adds what has risen since. The
  blueprint proof is the yardstick. Verdicts only for structural changes; round 1 took the local
  ones, and settled that `_three` and `_four` do not unify.
- [ ] **8. W — Stop 2, the write-up** (`r1`–`r8`, and every verdict; Opus, docs; `NEEDS_PI`). One
  entry under *Autopilot: for the PI*, dated and headed `NEEDS_PI: Stop 2`. It holds what tasks
  1–7 found; every verdict as one row (ID, GO or NO-GO, commit estimate and rung, what it changes,
  what it depends on); round 3's eight recommendations, one line each, with any premise a task
  here changed (task 1's verdicts bear on `r1` and `r2`); a proposed landing order with its total
  estimate; and the questions for the PI. It compresses the log if it nears ~500 lines.
  ROADMAP's queued-rounds bullet and `notes/Cleanup40.md`'s **Status** say the round waits on the
  PI. Then the autopilot stops (`NEEDS_PI`).
- [ ] **9. S — slice the sanctioned items** (after the PI's answer; Opus, docs). Transcribe the
  answer verbatim into *Decisions made*. Replace task 10's placeholder with one line per sanctioned
  item (10a, 10b, …), in dependency order, each with its rung and gates. Record each NO-GO and
  each item not sanctioned as a one-line verdict under *Decisions made*. Move an item the PI sends
  elsewhere (round 5, or **PROSE** in ROADMAP's queue) to *Moved to a later round*.
- [ ] **10. B — the sanctioned items land** (a placeholder until task 9). One commit each, green at
  every commit: whole-project `lake build` warning-clean and `lake lint` green; the blueprint gates
  (`blueprint/CLAUDE.md` *Static checks before commit*) on any TeX edit; and
  `CombinatorialRigidity/CLAUDE.md` *Forward-mode slices* on a changed statement, an additive
  successor or a deletion. A deletion is confirmed by trial deletion and a whole-project build. A
  commit that touches a headline re-runs the axioms harness.
- [ ] **11. X — close the round** (`CLEANUP.md` *Workflow* rule 5; docs). Whole-project
  `lake build` and `lake lint` green. The axioms harness re-diffed against `formalization.yaml`
  and re-run with `lake lean`: 19 of 19 at the three standard axioms. The ROADMAP row reads ✓, and
  `40-simplify`'s row in `.claude/autopilot/queue.toml` gets `done = true` (nothing else there
  changes). The status surfaces name round 5, `40-docs`, as next. *Moved to a later round* is
  mirrored into `notes/Cleanup40.md` §2 *Round 5*, or ROADMAP's **PROSE** bullet.

## Verdicts (Stop 2's inputs)

In their own file, `notes/Phase40-simplify-verdicts.md` (moved at task 4; *Decisions*). Each recon
task adds a subsection there, `### Task N (X)`, with one entry per input it owns, in the format
under *Scope*.

## Moved to a later round

Each line gives the task, its target (round 5, `40-docs`, or **PROSE** in ROADMAP's queue) and a
one-line reason. The same line goes into the target's plan section in the same commit. None yet.

## Blockers / open questions

- None. The round's one planned stop is Stop 2, after task 8.

## Hand-off / next phase

**Next: task 7 (G), the remaining long proofs** (Opus, docs only): checklist item 7's question and
re-rank, one docs commit of verdicts, as `### Task 7 (G)` in `notes/Phase40-simplify-verdicts.md`.
It skips the open-ear steps, which task 4 walked, and task 6's #4, #6 and #8, which have verdicts
(`a5`, `a6`). Task 6 hands it #5 and `Pair.lean`'s `|C| = 0` producer: they glue as the core's two
branches did, so weigh `a6`'s shape there. Then task 8 writes
Stop 2, and the autopilot stops for the PI. For task 8, the statement moves so far are task 3's
`c6`, and `c8`'s `-lifting-restrict` and `-contract-standing`, and task 4's `c9` (two clauses
dropped); task 5's `b1` changes a pinned signature's form, not its strength;
`sec:pencil-girth-chain` and `a1` follow `1a`; `a7` keeps a PI decision, which the PI may revisit.
Task 6 moves no statement.

## Decisions made during this round

- **2026-10-04, the open: the granularity.** Seven recon tasks, each one coherent question over a
  bounded reading surface. The mechanical map comes first, since three tasks' verdicts rest on it.
  Then come the two blueprint regions whose inputs are statement-against-pin questions, and then
  the three deeper questions. The write-up is its own commit because it is the stop. A task per
  input would re-pay a dispatch's reading for each of 36 inputs; fewer tasks would put two of the
  spike-bearing tasks 4–6, or task 7's long reading, into one sitting. The landings are sliced
  after Stop 2, once the PI has chosen them.
- **Probes stay in scratch.** No recon task commits a script. Its figures are tagged *measured,
  script not retained* (`HARNESS.md` *Reproducibility*), as rounds 1 and 3 did for liveness. No
  deletion rests on such a figure: a sanctioned retirement is re-verified at landing by trial
  deletion and a whole-project build (`CLEANUP.md` *Liveness*).
- **The landing order is set at task 9, not now.** It depends on what the PI sanctions, and on
  task 1's map: a retired cluster can moot another verdict, as retiring `TwoCut.lean` would moot
  `b2` and half of `b1`.
- **2026-10-04, task 1: a pinned cluster goes to the task that reads its node.** The checklist
  named hand-ons to tasks 2 and 4 only; the map found pinned dead nodes in sections neither reads.
  Task 2 takes those the reduction layer `\uses`; task 3, which already owns `c5`, `c6`, `c8` and
  the girth chain's `a1`, takes the rest outside the ears, as one-line verdicts where prior
  evidence stands (round 3 kept the unused parts the chapter's opening names).
- **2026-10-04, task 4: the verdicts move to their own file** (the coordinator's decision). At 440
  lines, with tasks 4–8 still to write, the log would pass its ~500-line tripwire. *Verdicts*,
  tasks 1–3 verbatim, moved to `notes/Phase40-simplify-verdicts.md`, as round 3 moved its exemplar
  to `notes/Phase40-exposition-exemplar.md`; *Verdicts* here points there, *Scope* binds it, and
  each task from 4 on writes its subsection there.
