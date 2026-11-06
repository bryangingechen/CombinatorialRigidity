# CLEANUP-42 round 4 — the folds, the witnesses and the docstrings (work log)

**Status:** closed (2026-11-05; opened the same day at the PI's word, `notes/Cleanup42.md` §1),
and CLEANUP-42 with it. Round 4 was the Lean round: Theorem S's `d = 3` core and four `d = 3`
cases of the reduction are now the `n = 3` / `m = 1` cases of their graded Lean (the folds), every
statement kept; two non-vacuity witnesses, at `K₂` and `K_{2,3}`; the ten stale Lean docstrings and
five dated `notes/BlueprintExposition.md` entries rounds 1–2 left; and, at the PI's word, the
folded `d = 3` nodes' 15 edges and five formalization notes. Ten tasks, ten commits; no `NEEDS_PI`
stop; `formalization.yaml` unchanged.
**Next concrete task:** ORIGAMI's open, with the PI (ROADMAP *Queued post-program phases*).
Round manual: `CLEANUP.md`.

## Autopilot: for the PI

CLEANUP-42's row of `.claude/autopilot/queue.toml` is attended, so the coordinator runs this round
to its close. **The one stop is the PI's** (§1 there): a fold that would change a main result's
statement or a blueprint statement. Such a task does not land that change: it writes a `NEEDS_PI`
entry here, newest first, and the loop stops; the PI answers in an entry that starts
`**PI, <date>:**`. Sessions hand off as usual when the context grows long (the PI's note).

- None arose. (The open's spikes found none, and every fold kept its statements, `d = 3` and
  graded. The PI's adjudication of the folds' fallout came at a coordinator check-in, not a stop:
  `notes/Cleanup42.md` §1, task 9.)

## Current state

**Task 10 landed** (this commit; docs only): each task's sha in its line; the two *Candidates*
entries and their `notes/Cleanup42.md` §3 mirrors marked taken by task 9 (`d7e18795`), and §3's nine
*Moved* lines for round 4 by task 2 (`e803c78d`); the round and CLEANUP-42 closed here, in
`notes/Cleanup42.md`'s **Status** and §3, ROADMAP's row, §42's *Next* and *Queued post-program
phases*, `notes/MolecularConjecture.md`, the queue (`done = true`) and the sentence of `README.md`
and `home_page/index.md` that left the route differences to this cleanup; `notes/BlueprintExposition.md`
records the close's no-entry judgment in its header. Two slips corrected: task 9's line (the three
`main-component` *missing* edges left were there at the open) and the dead pin's node, which is
`lem:extensor-pair-through-given-point` (task 6's line, its *Candidates* entry, the §3 mirror).
At HEAD, `python3 scripts/blueprint-deps.py --chapter` (nodes, pins, *missing*, dead pins): `pencil`
31, 44, 0, 7; `main-component` 124, 211, 3, 14; `pencil-d` 99, 237, 0, 26. Gates: G1, and the Lean
and TeX diff empty.

**The round's gates** (each task's own were in this section at its landing; git keeps them):
every Lean task (2–8) a whole-tree `lake build` with 0 warnings (6247 jobs at task 2, 6249 from
task 4 on) and `lake lint`, and `blueprint/lint.sh` at tasks 2 and 4–9; the folds (4–6) and task 9
`blueprint/verify.sh` with `checkdecls` silent; `#print axioms` the three standard for the three
pencil main results at each fold, with the bridge (4), the four `d = 3` cases (5) and the graded
nonsimple case (6), and for each new witness (3, 7, 8).

**Verified at the open** (2026-11-05, at `8797f875`):
- **The tree:** the coordinator's `lake build` of
  `CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Generic`, green, no warning (6108 jobs). A
  whole-tree `lake build` and `lake lint` were not run at the open (no Lean edit): task 2 runs both
  before editing, as the round's Lean baseline.
- **Blueprint:** `blueprint/lint.sh` green; `python3 scripts/check-docstring-labels.py --counts`
  total 0. `python3 scripts/blueprint-deps.py --chapter <c>` (nodes, pins, *missing*, implied,
  unbacked transitive, no Lean basis, dead): `pencil` 31, 45, **0**, 180, 2, 5, 4;
  `main-component` 124, 211, **3**, 607, 24, 36, 11; `pencil-d` 99, 236, **0**, 645, 17, 54, 31.
- **Main results** (`formalization.yaml`): the three pencil rows, `pencil_realization_theorem`,
  `pencilPair_of_nonempty` and `Graph.graded_pencil_conditioned_pair`, each the three standard
  axioms; both folds reach all three.
- **The import graph** (`scratch/cleanup-42/round4/imports.py`, reading every `import` line):
  `Grade/TheoremS` imports `MainComponent/CoverageTheoremS`, which imports only
  `MainComponent/CoverageCut` and `Induction/SparseDeficiency`; below `Grade/TheoremS` sit
  `Grade/Chains`, `Grade/Coverage`, `Grade/Reduction`, `Grade/Generic` and `Nonvacuity`, and of
  CoverageTheoremS's own declarations they call only `three_mul_sub_le_two_mul_ncard`
  (`Grade/Chains`), `Graph.IsX0Graph.x0Attains` and `Graph.exists_rigidCore_of_deficiency_two_pos`
  (`Grade/Coverage`). `Grade/Arms` sits below `Grade/TwoPencil`, `Grade/Realization`,
  `Pencil/Motive`, `Pencil/Arms` and `Pencil/Statement`, and not below `ArmsAssembly`, `Pair`,
  `Pair2` or `X0`; `X0` is not above `Grade/Reduction`.

**The open's spikes** (`scratch/cleanup-42/round4/`, gitignored; each a `module` file, as every
consumer is; `lake lean` counts):
- `Fold1Statement.lean` (0 errors, 0 warnings): the bridge
  `Graph.chainUsable_iff_chainUsableAt_three` and `Graph.IsX0Graph.exists_additiveCore`'s statement,
  verbatim, as the `n = 3` case of `Graph.IsX0Graph.exists_additiveCoreAt`.
- `Fold1Upstream.lean` (0, 0): `Grade/TheoremS`'s body over `CoverageCut` and `SparseDeficiency`
  alone, with the five `d = 3` lemmas it calls copied in (CoverageTheoremS lines 216–408): the
  fold's import order has no cycle.
- `Fold2Statements.lean` (0, 0): the five `d = 3` declarations of the four cases, statements
  verbatim, as the `m = 1` cases through `hasGradedPencilRealization_two_iff` and
  `hasGradedDistinctPencilRealization_two_iff`.
- `Fold2ArmsAssembly.lean` (0, 0): four of them (base, loop, both cut forms) importing `Grade/Arms`
  alone, `ArmsAssembly.lean`'s place after the fold. `Fold2NotSimpleOverArms.lean` (0, 0):
  `hasGradedPencilRealization_of_not_simple` over `Grade/Arms` alone.
- `WitnessK2.lean` (0, 0; axioms the three standard): witness (1), complete.
- `WitnessK23.lean` (0 errors; 5 warnings, the five `sorry` leaves): witness (2)'s composition.

## Scope and standing rules

- **The hygiene rule, at the PI's stop.** No main result's statement and no blueprint statement
  changes; every `d = 3` declaration a fold re-proves keeps its statement byte for byte (the
  parent's signature lines, `diff`ed). A finding that would change one is a `NEEDS_PI` entry
  above and a stop; any other out-of-scope finding goes under *Candidates for the PI* or *Moved to
  a later round*, mirrored into `notes/Cleanup42.md` §3 in the same commit, and is not a stop.
- **Writes.** Lean in the files each task names (and a new file where it says so, with its line in
  `CombinatorialRigidity.lean`); a `\lean{…}` pin only where a fold moves one (task 4 adds one,
  task 5 removes one), with its node's `\uses` where the task says, and no other TeX;
  `notes/FRICTION.md` (and `FRICTION-archive.md`) for the entries a fold resolves; the task's
  notes; this log and `notes/Cleanup42.md`; at the close only, the status surfaces of the open.
  `formalization.yaml` does not change (decision below). No `lakefile.toml`, `lake-manifest.json`
  or `lean-toolchain`.
- **Evidence.** A claim about a declaration comes from its statement and body at HEAD, never its
  docstring (root `CLAUDE.md`); the spikes are the build plan, re-run against HEAD before they are
  transcribed.
- **Decision (the open): the deleted-name sweep.** For each declaration a task deletes, `grep -rn`
  its name and its distinctive stem over the whole tree, every file kind (Lean docstrings,
  blueprint `\lean{}` lists and prose, `notes/`). A live mention (a Lean docstring, the blueprint,
  an open FRICTION entry, a planning note's current text) is repointed in the same commit; a dated
  record (a closed phase's or round's note, a frozen design doc, a workbook, the findings ledger
  `notes/Prose-findings.md`, a FRICTION *Where it bit* line, a dated judgment of
  `notes/BlueprintExposition.md`) stays, and the task's line lists it as kept.
- **Decision (the open): the `d = 3` chapter keeps its proofs.** After a fold, a `d = 3` node's pin
  is the `d = 3` case of a `pencil-d.tex` node's, while its chapter proof stays the `d = 3`
  argument (the same argument at one dimension). No blueprint proof, note or `\uses` changes for
  it, and no ledger row (the ledger is `pencil-d.tex`'s). `scripts/blueprint-deps.py` will report
  the new reach as *missing* edges from those nodes into `pencil-d.tex`, and some of their proofs'
  edges as unbacked: each fold task records them, `--chapter` before and after, in its line, and
  the close puts one *Candidates for the PI* line (add an edge and a formalization note naming the
  `d = 3` case, or leave). `--chapter pencil-d` stays at 0 *missing*. **Overridden** by the PI's adjudication of 2026-11-05 (`notes/Cleanup42.md` §1, "the folds' fallout"): task 9 adds the edges and the notes; the six dead pins stay.
- **Decision (the open): the witnesses' home.** Both go in `CombinatorialRigidity/Nonvacuity.lean`,
  the home of the main results' witnesses, which already imports `Grade/Generic` and has the
  private `ofSimpleGraph_simple` that `K_{2,3}` needs: witness (1) beside
  `graded_pencil_conditioned_pair_witness`, witness (2) under its own header, its module-docstring
  bullet saying that it witnesses an inner arm of the generic theorem, not a main result's
  hypothesis. **`formalization.yaml` does not change:** its rows carry no witness field, and no
  main result's statement or axioms change.
- **Decision (the open): the docstring count.** Ten stale Lean docstrings in eight files, not eight
  (the coordinator's count to the PI): `Grade/LiftNoRigid.lean` (module, and
  `exists_pencilConfigPoint_of_dotProduct`), `Grade/Stars.lean`
  (`exists_mulVec_add_mulVec_eq_zero`), `Grade/ShortThree.lean`
  (`Graph.X0AttainsGrade.of_openEar_three`), `Grade/LiftWitness.lean` (`liftAttains_of_least`),
  `Grade/LiftSmall.lean` (module), `Grade/LiftCutEdge.lean` (`liftAttains_of_cutEdge`),
  `Grade/LiftCases.lean` (module), `Grade/EarFree.lean` (`exists_earExtend_poly`,
  `isTrivialLift_of_finrank_liftSpaceTilde_le`); each stale sentence `grep`ed at `8797f875`. The
  dated notes are five entries of `notes/BlueprintExposition.md`, not three: §3's *Moved* lines name
  42h, 42l and 42m, and 42i (R-14) and 42k (R-19) list route differences round 2 aligned too; 42j's
  (R-17, kept) is accurate.
- **The gates**, each in the foreground with an explicit `timeout`, the commit under
  `if <gates>; then git commit …; fi`:
  - **Every task:** (G1) `python3 notes/check-phase-note.py` green.
  - **Every Lean task:** (G2) a whole-tree `lake build`, warning-clean (`grep -cE 'warning:|error:'`
    0, `grep -c 'failed to cache artifact'` 0), then bare `lake lint` green. (G3)
    `blueprint/lint.sh` green, check 9's docstring-label total still 0 (a moved declaration's lead
    names its own node; a new helper's lead parenthetical opens "a step of <label>").
  - **The folds (tasks 4–6):** (G4) `blueprint/verify.sh`, `checkdecls` silent. (G5) `#print axioms`
    of the three pencil main results, by a scratch `lake lean` file: the three standard axioms.
    (G6) the statement diff and the deleted-name sweep above. (G7) `--chapter pencil`,
    `main-component` and `pencil-d` before and after, the new *missing* and unbacked edges listed.
  - **The witnesses (tasks 3, 7, 8):** G5's `#print axioms` for each new witness.
  - **The close:** G1 and the tallies its line names.
- **One task, one dispatch**, the rung beside each task. A task that does not fit lands what
  closes and appends the rest as a new task right after it, with a one-line note.

## Lemma checklist (the round's task list)

One commit per task, in this order (the docstring task first: none of its files is a fold's). Line
numbers are at `8797f875`; re-`grep` before editing. **On landing, a task's line is cut to at most
three lines:** number, sha, what landed, lines deleted, its edges and any *Candidates* line.

- [x] **1. Open** (`83ac039d`; docs only).
- [x] **2. The stale docstrings and dated notes** (`e803c78d`; Lean docstrings and notes only). Ten
  docstrings in eight `Grade/` files lose or restate the sentence contrasting them with a round-2-removed
  route or hypothesis; five `BlueprintExposition.md` entries (42h, 42i, 42k, 42l, 42m) gain a closing sentence.
  §3's *Moved* lines for round 4 marked taken at the close. 11 lines deleted net.
- [x] **3. Witness (1): `K₂` at the generic conjunct** (`40554d8b`). `graded_pencil_conditioned_pair_generic_witness`
  in `Nonvacuity.lean` after `graded_pencil_conditioned_pair_witness`, spike transcribed, three private
  helpers, a module bullet; `#print axioms`: `propext`, `Classical.choice`, `Quot.sound`. 47 lines added.
- [x] **4. Theorem S's fold** (`6bdb5686`). New `MainComponent/SparseCount.lean` (the five counting lemmas, 229 lines);
  `Grade/TheoremS` imports it, drops its private `six_le_bodyBarDim` (FRICTION's fourth site); `CoverageTheoremS` imports `Grade/TheoremS`, gains the bridge, `exists_additiveCore` (statement `diff`ed, unchanged) is `exists_additiveCoreAt` at `3`, `exists_additiveCore_of_rigid` deleted (673 → 317). `pencil-d.tex`: `def:pencil-d-usable-chain` pins the bridge, `\uses` `def:pencil-x0-usable-chain`. Kept in the sweep: `Phase40-design.md`, `Prose-findings.md`. G7 `--chapter`, HEAD → after: `pencil` and `pencil-d` 0 *missing*; `main-component` *missing* 3 → 5 (`thm:pencil-x0-theorem-s` into `def:pencil-d-usable-chain`, `thm:pencil-d-theorem-s`), unbacked 24+36 → 32+39 (its proof's `\uses`: `lem:deficiency-*`, `lem:pencil-x0-chain-exists`, `lem:pencil-x0-sparse-count`), dead pins 11 → 14 (`partitionDef_induce_id_le_of_maximal`, `deficiencyMerged_three_add_five_le`, `deficiencyMerged_two_add_two_le`).
- [x] **5. The reduction's fold: base, loop and cut-edge cases** (`273e824b`). `ArmsAssembly.lean` imports `Grade/Arms`; its four `d = 3` cases (statements `diff`ed, unchanged) are the `m = 1` cases, with one private helper, `exists_cut_sides` (`n = 3` by the existing `Graph.eq_add_one_of_bodyBarDim_eq_screwDim`, so no new FRICTION site); `…_core` deleted; `Arms.lean` 930 → 630, `ArmsAssembly.lean` 233 → 137 (396 Lean lines deleted net); docstrings in `Grade/Arms`, `Pair`, `Pair2`, the `pair_map` mirror; FRICTION: the 42k entries updated, a new *cut sides* entry.
  `pencil.tex`: `lem:pencil-cut-case`'s pin drops `…_core`. Kept in the sweep: `BlueprintExposition.md`, `Cleanup40.md`, `Phase40-cleanup.md`, `Phase39-design.md`, `Prose-findings.md`, the W4 workbook and archive, FRICTION's `pair_map` *Where it bit*.
  G7 `--chapter`, HEAD → after: `pencil` *missing* 0 → 10 (loop, base, cut into `def:pencil-d-rank-hypothesis`, `lem:pencil-d-rank-agrees-three` and their `pencil-d` case; the cut into `def:pencil-d-distinct-motive`), unbacked 2+5 → 12+9 (their proofs' `\uses`), dead pins 4 → 6 (`exists_reposition_cross_incidences`, `exists_perp_linearIndependent`); `pencil-d` 0 *missing*, dead 29 → 26 (the two `two_iff`s, `exists_hasPencilPlaneRealization_two_iff`); `main-component` unchanged. A *Candidates* line (below).
- [x] **6. The reduction's fold: the nonsimple case** (`d9dee0c6`). `hasGradedPencilRealization_of_not_simple` moved verbatim to the end of `Grade/Arms.lean` (`Grade/Reduction.lean` 372 → 109 lines, `Arms.lean` 594 → 858); `X0.lean` imports `Grade/Arms`, its `hasPencilRealization_of_not_simple` (statement `diff`ed, unchanged) is the `m = 1` case (375 → 122; no orphaned helper in `X0.lean`); FRICTION *42k's cases repeat…* to the archive. Nothing deleted, so the sweep found only moves; no TeX. G7: `pencil` *missing* 10 → 13 (nonsimple into `def:pencil-d-rank-hypothesis`, `lem:pencil-d-rank-agrees-three`, `lem:pencil-d-nonsimple-case`), unbacked 12+9 → 21+10, dead pins 6 → 7 (`exists_linearIndependent_extensor_pair_through_given_point`, pinned by `lem:extensor-pair-through-given-point`, now unused); `pencil-d` and `main-component` unchanged. A *Candidates* line.
- [x] **7. Witness (2), part 1: `K_{2,3}` is feasible** (`f3487c00`). `Nonvacuity.lean`, a new header after the molecular rows: private `k23_degree` and `k23_pencilNondegFeasible`, the route's data
  unchanged (every conjunct holds; the hubs are the two bodies of degree three), hinges by `exists_extensor_two_pencils`; axioms the three standard (a scratch `module` with `import all`). The hygiene fix
  ("the least simple graph with an edge"). FRICTION: a new idiom entry, lifted to a TACTICS-QUIRKS symptom row. 147 Lean lines added net.
- [x] **8. Witness (2), part 2: the good ear and the ear's condition** (`1e6f40f6`). Public `holdsGenerally_earFree_witness` in `Nonvacuity.lean` under task 7's header (a `K₂₃` local notation, task 7's two statements on it), its module bullet; the
  five leaves closed as eight private lemmas: (a2) by `|E(K_{2,3}[Z])| ≤ i·j` and `interval_cases`; selectors by the existing `exists_steer_selectors`. Axioms the three standard. FRICTION: a new
  mirror-candidate entry (`ncard` of a set of a sum type), a line on 22i's `vertexSet_induce` entry. 135 Lean lines added net.
- [x] **9. The folds' `d = 3` nodes: their edges and notes** (`d7e18795`; blueprint and notes only). The 15 edges, proof `\uses`: `pencil.tex`'s loop, base, cut and nonsimple cases into `def:pencil-d-rank-hypothesis`, `lem:pencil-d-rank-agrees-three` and their `pencil-d` case (the cut also `def:pencil-d-distinct-motive`); `main-component.tex`'s `thm:pencil-x0-theorem-s` into `def:pencil-d-usable-chain`, `thm:pencil-d-theorem-s`; no cycle, none left out. Five one-sentence formalization notes (`fmlnote:pencil-cut-case` rewritten). G7: `pencil` *missing* 13 → 0, `main-component` 5 → 3 (the other three, `lem:deficiency-core-bound`, `lem:deficiency-one-body-chain` and `lem:deficiency-two-body-chain` into their `-d` forms, were missing at the open, `8797f875`, since Phase 42 proved those `d = 3` lemmas through their `-d` forms; outside the PI's 15, untouched), dead pins unchanged.
- [x] **10. The close** (this commit; docs only). Shas in tasks 1–9's lines and §3's mirrored lines;
  the two *Candidates* entries taken by task 9 (`d7e18795`); the round and CLEANUP-42 closed on the
  open's status surfaces, the queue row `done = true`; the README and home-page sentence; no ledger entry.

## Candidates for the PI

- **A stale formalization note** (task 5, `273e824b`; taken by task 9, `d7e18795`, at the PI's word:
  the note reworded). `fmlnote:pencil-cut-case` (`pencil.tex`) said the two forms "are one Lean
  theorem whose parameter selects the form"; task 5 deleted that theorem (`…_core`), and each form
  is now the `m = 1` case of 42k's cut case through a `two_iff`. Mirrored in `notes/Cleanup42.md` §3.

- **Dead pin and the nonsimple edges** (task 6, `d9dee0c6`; taken by task 9, `d7e18795`: edges and
  note added, the pin kept at the PI's word). `lem:extensor-pair-through-given-point`'s Lean
  declaration (`Statement.lean`) has no user now that the `d = 3` nonsimple proof is the `m = 1`
  case; its node is pinned, so it stays. `lem:pencil-nonsimple-case` gained the `d = 3` reach into
  `pencil-d.tex`, like task 5's nodes. Mirrored in `notes/Cleanup42.md` §3.

## Moved to a later round

- None: nothing left the round, and round 4 is CLEANUP-42's last.

## Blockers / open questions

- None.

## Hand-off / next phase

**Next concrete task:** ORIGAMI's open, with the PI (ROADMAP *Queued post-program phases*;
`notes/Origami.md`). CLEANUP-42 is done: round 4 closed with this commit, and the queue's
`CLEANUP-42` row is `done = true`. ORIGAMI, the queue's next row, is attended, so it opens with the
PI and takes its phase number then. Nothing carries over from round 4.

**For the PI** (a report, not a stop): the six dead pins stay pinned (§1 there, the folds'
fallout); `--chapter main-component`'s three *missing* edges, `lem:deficiency-core-bound`,
`lem:deficiency-one-body-chain` and `lem:deficiency-two-body-chain` into their `-d` forms, from
Phase 42 (missing at round 4's open, outside the PI's 15), were added after the close at the PI's
word, each with a formalization note (`b27e447a`; `main-component` 0 *missing*); and
`notes/dispatch-log.md` was groomed after the close (`bf8eaaf5`; its *CLEANUP-42 grooming*),
and its two open items closed (this commit: F59's `--surfaces` fix, F56's promotion).

## Decisions made during this round

- **The log, the order and the rungs** (the open): nine tasks at the open (a tenth added 2026-11-05), the PI's four items; the cheap
  docstring task first, as it shares no file with a fold; the folds before witness (2), whose file
  they do not touch either. Under *Scope*: the sweep, the `d = 3` proofs, the witnesses' home, the
  count, the gates.
- **The close** (task 10): `notes/BlueprintExposition.md` takes no entry, by its header's
  criterion: a fold is project-side (the `d = 3` Lean proved once, as a case of the every-dimension
  Lean), each folded node keeps its `d = 3` argument, and no node rerouted for difficulty; its
  header records the judgment. `README.md` and `home_page/index.md` said the route differences were
  "recorded for the cleanup that follows the phase"; they now say what the cleanup did.
