# Phase 40 cleanup round 4/5 — `40-simplify`, the deep simplification recon (work log)

**Status:** in progress (opened 2026-10-04). Round 4 of the five post-Phase-40 cleanup rounds.
Their order, stops and the PI's decisions are in `notes/Cleanup40.md`, and
`.claude/autopilot/queue.toml` is the authority for which rounds are done. The round is a
read-only Opus recon over the pencil surface, looking for bigger simplifications
(`notes/Cleanup40.md` §2 *Round 4*). Seven recon tasks each commit GO / NO-GO verdicts with commit
estimates to this log. Task 8 writes Stop 2 (`NEEDS_PI`), the round's one planned stop; then the
items the PI sanctions land, and task 11 closes. Task 1, the liveness map, is done (*Verdicts* →
*Task 1*). **Next concrete task:** task 2 (R), `pencil.tex`'s reduction layer, with what task 1
handed it (Opus, docs only). Round manual: `CLEANUP.md`.

## Autopilot: for the PI

No entry yet. Task 8 writes Stop 2 here: newest entry first, dated, headed with its status. The
PI's answer goes below it, in an entry of the PI's own.

## Current state

**Round 4 is open** (2026-10-04, a docs-only commit). Task 1 (L) has landed: the liveness map,
its verdicts, and the pinned dead clusters handed to tasks 2–4 by name, under *Verdicts* →
*Task 1*. Nothing is mid-stream. The task list is complete for the recon (tasks 1–8). Task 9
slices the landings after Stop 2, and task 11 closes.

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

- **Read-only recon.** Tasks 1–9 are docs commits. Each edits this log, and the next-task pointer
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
- **A verdict** is one entry under *Verdicts*, at most five lines: `**<id>, <name>: GO**` (or
  NO-GO); one sentence of why; the commit estimate (commits, rung, ⚠Z for the fragility zone);
  what it changes (a headline signature, a blueprint statement's strength, the dependency graph,
  or nothing a reader sees); any verdict it depends on; its evidence (read, measured, or a spike's
  residual). The detail goes in the task's commit message.
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

## Lemma checklist (the round's task list)

One commit per task, in this order. Each line names the inputs it owns; its commit names its
verdicts.

- [x] **1. L — the liveness map** (`q3`, `b2`, and `r1`'s deletion question; Opus, docs). The
  closure of the 19 main results, the off-closure clusters, the verdicts and the hand-ons are under
  *Verdicts* → *Task 1*.
- [ ] **2. R — `pencil.tex`'s reduction layer** (`a2`, `a4`, `m1`–`m5`, `c2`–`c4`, design §6's
  conditional theorems, and task 1's hand-ons to it; Opus, docs). The question: once one route is
  live, what do `sec:pencil-reduction`, `sec:pencil-nondegenerate` and
  `sec:pencil-main-component-route` keep, and in what shape? Read those three subsections (about
  810 lines, 27 labels) and the statements, not the proofs, of their pins, including
  `Graph.pencil_reduction` and the six `pencil_conjecture*` theorems. `a4`'s proof is read only
  for its estimate, against task 1's map.
  Verdicts: retire, keep or re-pin each off-route conditional with its node; split
  `thm:pencil-conditional-realization-pair` (`c3`); align its statement (`c4`) and
  `thm:pencil-reduction`'s (`c2`) with their pins, or the pins with them; drop the six binders
  (`a2`, a headline signature); the five graph lines `m1`–`m5`.
- [ ] **3. N — node shapes outside the reduction layer** (`a1`, `m6`, `m7`, `c1`, `c5`–`c8`, and
  task 1's hand-ons to it; Opus, docs). The question: where a node's statement and its pins
  disagree, or a node bundles unrelated facts, which side moves? Read the nodes and their pins'
  statements. In `pencil.tex`:
  `lem:pencil-chain-side-connected`. In `main-component.tex`:
  `lem:pencil-selector-independent-scalar`, `lem:pencil-condition-linear` with
  `lem:pencil-config-distinct-realization`,
  `lem:pencil-x0-main-picture-open`, `lem:pencil-lifting-restrict`, `thm:pencil-x0-bridge`,
  `lem:pencil-contract-standing`, `lem:pencil-splitoff-curve`, `thm:pencil-x0-theorem-s` and
  `lem:pencil-generic-steer`. Verdicts, per node: strengthen the Lean, weaken or restate the node,
  split it (principle D of `blueprint/AUTHORING.md`, as round 1's task 19 split
  `lem:pencil-ear-data`), or leave it; and the two graph lines `m6`, `m7`.
- [ ] **4. E — the open ears** (`q1`, `a7`, `c9`, with task 1's sizes; Opus, docs; spikes as
  needed). SHORT splits the open-ear steps by two, three and four interior bodies, ORBIT by one or
  two at non-adjacent ends, and CHAIN has the cycle and the closed ear. The question: one argument
  or several, and if one, what shared statement, saving what? Read `sec:main-component-chain`,
  `-short` and `-orbit` first (about 1 480 lines, round 3's account of their ideas). Then read the
  step theorems' statements and top-level structure in `Chain.lean`, `Short.lean` and `Orbit.lean`.
  Prior evidence: round 1's tasks 17–18 (the `Fin.succAbove` generality failed; the shared assembly
  `Graph.X0Attains.of_openEar_splitOff` landed) and `r5`. Verdicts: the unification, or NO-GO naming
  the step where the arguments diverge; `a7` keep, retarget or retire; `c9`'s two halves.
- [ ] **5. A — where `Pencil/` re-proves** (`q2`, `b1`, `a3`; Opus, docs; spikes as needed). The
  question: where does `Pencil/` re-prove what `AlgebraicInduction/`, `RigidityMatrix/`,
  `Induction/` or mathlib already has? Round 2's hub normalization is the one known instance. To
  bound the reading, work at statement level first: match `Pencil/`'s declarations about motion
  spaces, rigidity rows, deficiency and rank by shape (`lean_loogle`, `lean_local_search`) against
  those directories. Read in full only the candidate pairs, and spike the one or two strongest
  replacements. Also `b1` (restating both hubs with `ᶜ` should drop five `rfl` bridges, and
  changes two statements, one pinned) and `a3` (the finsum mirrors `CoverageTheoremS.lean`'s
  degree-sum pair needs).
- [ ] **6. P — Phase 39's producers** (`a5`, `a6`; Opus, docs; ⚠Z reading, spikes). The question:
  does either recorded cross-proof duplication admit a shared lemma that nets shorter? `a5`:
  `Pair2.lean`'s pendant producers #4 and #6, whose ~190-line tails are byte-identical; the lemma
  abstracts the `point_vc`-avoidance target and the hub-transfer proof. `a6`: the `|C| = 0` and
  `|C| = 1` branches of `hasPencilRealization_of_not_twoEdgeConnected_core` (`Arms.lean`), over
  `ScrewSpace` carrier terms. Spike each shared signature against both call sites (`sorry` bodies,
  residual goals recorded), and estimate the net lines.
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
  estimate; and the questions for the PI. It compresses *Verdicts* if the log nears ~500 lines.
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

Each recon task adds a subsection here, `### Task N (X)`, with one entry per input it owns, in the
format under *Scope*.

### Task 1 (L)

**The map** (*measured, script not retained*). The project's declaration graph at `4039ba02`, run
with `lake lean`: edges are `Expr.getUsedConstants` over types and values; matchers, `_proof_`,
`_auxLemma` and equation lemmas are expanded into their users, and constructors, projections and
recursors folded into their inductive. Of 3 221 project declarations, 2 380 feed the 19 main
results and 1 629 the two pencil headlines. A raw closure without folding (round 3's
`Liveness8.lean` method, checked and rerun) agrees on all 3 221 for both. The surface is 920
declarations: 778 in `Pencil/`, 96 that Phase 40 or rounds 1–3 added outside it, 18 more pins of
the two chapters, 28 more of D5's names.

**`q3`: 121 of the 920 feed no main result** (5 400 lines). With the 23 helpers outside the
surface that only they reach: 144 declarations, 5 963 lines, under 60 dead roots, none with a Lean
caller. Of the 799 live, 791 feed the pencil headlines and 8 feed only the other 17 results
(Phase 40's `mapExtensor` lemmas, `three_le_bodyBarDim_of_two_le`); nothing in `Pencil/` feeds
another result. Five `rfl` lemmas (four `@[simp]`) could serve `simp` with no trace in a term;
none is retired here, and trial deletion settles them. The 5 963 lines go as follows.

*Handed on (pinned clusters, decided by the task named):*
- **Task 2, 1 754 lines.** (a) Design §6's cluster under
  `pencil_conjecture_of_hcontract_hK_hbareSplit_of_card`, 1 565: `_hbareSplit` and `_of_card`
  (`thm:pencil-conditional-realization-pair`), `pencilPair_of_splitOff_of_habitat`, `a4` (879),
  two more in `Escape.lean`, `Habitat.lean` whole, two in `ReducibleVertex.lean`; it shares 746
  with `q3a` and 43 with the girth chain. (b) `pencil_conjecture_of_arms`
  (`thm:pencil-conditional-realization`, 78); `_of_arms_pair` is live. (c) Two nodes the
  reduction layer `\uses` with no live pin: `lem:two-pencil-extension-iff` (25; by
  `lem:pencil-cut-case` and `lem:pencil-cut-nondegeneracy`, whose pins never call it; the cut
  case's calls `lem:two-pencil-extension`'s) and `lem:pencil-base-parallel-pair` (86 with its
  unpinned root; by `lem:pencil-base-case`, whose pin does not call it).
- **Task 3, 1 777 lines.** (a) Three of the four parts the chapter's opening calls unused, all pins
  dead, rewritten and kept by round 3: `sec:pencil-duality` (3 nodes) and `sec:pencil-cycle` (3),
  366; `sec:pencil-girth-chain` (8), 947 with `MaximalChain.lean` and `Girth.lean` whole. (b)
  In `main-component.tex`, on `thm:pencil-conjecture`'s `\uses` ancestry with no live pin:
  `lem:pencil-selector-independent-scalar` (`c5`) and `lem:pencil-x0-two-hubs-obstruction`. One
  caller-less pin beside live ones (`c9`'s pattern): `lem:pencil-condition-linear` (`c6`),
  `lem:pencil-contract-standing` (`c8`), `lem:pencil-lifting-space-affine`,
  `lem:pencil-picture-local`, `def:pencil-configuration`, `thm:pencil-flat-rank`,
  `cor:pencil-flat-attains`, `cor:pencil-flat-x0`, `thm:pencil-jj-equality`; 337 in all. (c)
  The same pattern in other chapters, 127: `thm:projective-invariance` (three pins),
  `lem:panel-hinge-dual-molecular` (two), `thm:theorem-55-6-rows`, `lem:deficiency-cut-vertex`.
- **Task 4, 153 lines.** `a7` (`thm:pencil-x0-closed-ear`, off the `\uses` ancestry; 118 with
  `pathVertex_shift`); `c9`'s halves, 15 and 20.

*Verdicts (the unpinned clusters and the two named sets):*
- **`r1`, delete the D5 debt's 29 off-headline names: GO for 27, NO-GO for the 2 pinned.** The 27,
  with two helpers only they reach, serve only the two-cut composition, built for smark's kernel
  attack, which design §6 retired; no blueprint text names them. 1 commit, Sonnet (a deletion in
  ⚠Z files): `TwoCut.lean` whole and 20 declarations elsewhere, 986 lines; nothing a reader sees.
  Keep the 2 (51 lines; two chapters cite their node). Moots `b2`, half of `b1`. Evidence: the map.
- **`b2`, the merged hub's `hne`: NO-GO.** Moot under `r1`: the hub and its one consumer,
  `weldedLoss_nonneg`, are in `TwoCut.lean`'s dead cluster. If the PI keeps that file: GO, 1
  commit, Sonnet, an unpinned statement (drop `hne`, its `have`, and `⟨u, hu⟩` at the call).
  Depends on `r1`. Spike: without `hne` the hub compiles warning-free, and at the consumer's call
  its conclusion is `rfl`-equal to the original's.
- **`q3a`, the kernel-route roots: GO with task 2's §6 verdict, else keep.**
  `hasGenericPencilRealization_of_independent_pencilRow_target` (`Escape.lean`, 129) and
  `pencilNondegFeasible_of_le_of_triangleFree` (`Steer.lean`, 42) serve only kernel (K)'s route.
  Retired with `_of_card`'s cluster they free 2 482 lines (`Escape.lean`, `Habitat.lean`,
  `WitnessGeneral.lean` whole); kept, they are its inputs if the PI reopens it. In that commit.
- **`q3b`, `pencilChartWF_standing_ofCoord_toCoord`: GO.** A Phase 39 leftover in `Steer.lean`'s
  live layer (27 lines): `exists_fillNbr_pencilChartWF_of_standing` takes its conclusion as
  hypotheses, which its callers build otherwise. In `r1`'s commit, Sonnet; nothing a reader sees.
- **`q3c`, the rest: NO-GO (keep), 255 lines.** API beside its definition: `Chart.lean`'s `cross₃`
  linearity lemmas, `Statement.lean`'s four scale-invariance iffs, seven short lemmas. A design
  witness: `exists_isNondegPencilRealization_parallel_pair` (`Pair.lean`, 90), cited in two live
  docstrings as the proof that feasibility could not replace `PencilPair`'s `G.Simple`.

Outside the surface, not this round's: 18 dead declarations (529 lines) whose headers were added
between Phase 39's open and Phase 40's, in none of the clusters above (one, 139 lines, is shared by
`_of_card` and an outside root); named in the commit message.

## Moved to a later round

Each line gives the task, its target (round 5, `40-docs`, or **PROSE** in ROADMAP's queue) and a
one-line reason. The same line goes into the target's plan section in the same commit. None yet.

## Blockers / open questions

- None. The round's one planned stop is Stop 2, after task 8.

## Hand-off / next phase

**Next: task 2 (R), `pencil.tex`'s reduction layer** (Opus, docs only): checklist item 2's
question and inputs, plus task 1's hand-ons to it (*Verdicts* → *Task 1*): design §6's cluster
with `a4`, `pencil_conjecture_of_arms`, and the two nodes the reduction layer `\uses` with no live
pin. Its §6 verdict also settles `q3a`'s. Then tasks 3–7 in order, each one docs commit of
verdicts; tasks 3 and 4 take task 1's other hand-ons. Then task 8 writes Stop 2, and the
autopilot stops for the PI.

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
