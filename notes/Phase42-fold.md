# CLEANUP-42 round 4 — the folds, the witnesses and the docstrings (work log)

**Status:** open (2026-11-05, at the PI's word, `notes/Cleanup42.md` §1). Round 4 is the Lean
round of CLEANUP-42: Theorem S's `d = 3` core and four `d = 3` cases of the reduction become the
`n = 3` / `m = 1` cases of their graded Lean (the folds); two non-vacuity witnesses, at `K₂` and
`K_{2,3}`; and the ten stale Lean docstrings and five dated `notes/BlueprintExposition.md` entries
left by rounds 1–2. The open's spikes: both folds keep every `d = 3` statement, no blueprint
statement changes, so no `NEEDS_PI`. Nine tasks, one commit each.
**Next concrete task:** task 3, witness (1), `K₂` at the generic conjunct (below); task 2 landed.
Round manual: `CLEANUP.md`.

## Autopilot: for the PI

CLEANUP-42's row of `.claude/autopilot/queue.toml` is attended, so the coordinator runs this round
to its close. **The one stop is the PI's** (§1 there): a fold that would change a main result's
statement or a blueprint statement. Such a task does not land that change: it writes a `NEEDS_PI`
entry here, newest first, and the loop stops; the PI answers in an entry that starts
`**PI, <date>:**`. Sessions hand off as usual when the context grows long (the PI's note).

- None yet. (The open's spikes found none: both folds keep every statement, `d = 3` and graded.)

## Current state

**Task 2 landed** (Lean docstrings only, no statement or proof): the ten stale docstrings and the
five dated `BlueprintExposition.md` entries (the checklist line). **Task 1 landed** (docs only): this log; `notes/Cleanup42.md`'s §1 (the PI's entry
of 2026-11-05 for round 4), **Status** and §3; ROADMAP's Status row, §42's *Next* and the
CLEANUP-42 bullet; `notes/MolecularConjecture.md`; the queue's comment.

**Task 2's gates** (the round's Lean baseline): whole-tree `lake build` green (6247 jobs, 0 warnings,
0 cache failures), `lake lint` green, `blueprint/lint.sh` green, docstring-label total 0.

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
  `d = 3` case, or leave). `--chapter pencil-d` stays at 0 *missing*.
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

- [x] **1. Open** (this commit; docs only).
- [x] **2. The stale docstrings and dated notes** (this commit; Lean docstrings and notes only). Ten
  docstrings in eight `Grade/` files lose or restate the sentence contrasting them with a round-2-removed
  route or hypothesis; five `BlueprintExposition.md` entries (42h, 42i, 42k, 42l, 42m) gain a closing sentence.
  §3's *Moved* lines for round 4 are marked taken at the close (task 9). 11 lines deleted net.
- [ ] **3. Witness (1): `K₂` at the generic conjunct** (Sonnet, or a resume of the open's recon:
  the spike is the build). Transcribe `scratch/cleanup-42/round4/WitnessK2.lean` into
  `Nonvacuity.lean` after `graded_pencil_conditioned_pair_witness`:
  `graded_pencil_conditioned_pair_generic_witness : HasGradedGenericPencilRealization ℝ 3 4
  (Graph.banana (0 : Fin 2) 1 ({0} : Set (Fin 2)))`, the headline's third conjunct at `m = 2`, its
  feasibility from the double edge (`exists_isNondegPencilRealization_parallel_pair`,
  `PencilNondegFeasible.mono`, no hub there) through `gradedPencilNondegFeasible_iff`; three private
  helpers. A module-docstring bullet. Gates G1–G3, the witness's axioms.
- [ ] **4. Theorem S's fold** (Sonnet). New `Pencil/MainComponent/SparseCount.lean` (imports
  `MainComponent/CoverageCut`, `Induction/SparseDeficiency`): CoverageTheoremS's lines 216–408
  verbatim (`Graph.IsX0Graph.three_mul_sub_le_two_mul_ncard`, `…exists_degree_eq_two_notMem`,
  `…two_mul_ncard_le_ncard_edgeSet`, `…partitionDef_three_induce_diff_nonpos`,
  `Graph.IsOpenEar.deficiency_three_induce_cycle`). `Grade/TheoremS.lean` imports it in place of
  CoverageTheoremS and drops its private `six_le_bodyBarDim` for `Graph.six_le_bodyBarDim` (FRICTION
  *`bodyBarDim` has no monotonicity…*, its fourth site). `CoverageTheoremS.lean` imports
  `Grade/TheoremS`; gains `Graph.chainUsable_iff_chainUsableAt_three` (spike; its lead names
  `def:pencil-d-usable-chain`); `exists_additiveCore`, statement unchanged, is
  `hG.exists_additiveCoreAt le_rfl …` with the bridge; `exists_additiveCore_of_rigid` (lines
  412–461; unpinned, no other caller) is deleted. `Grade/Coverage.lean` imports CoverageTheoremS.
  Module docstrings of the three files restated. Blueprint: `def:pencil-d-usable-chain`'s pin gains
  the bridge, its statement's `\uses` `def:pencil-x0-usable-chain` (its last sentence). Sweep:
  `exists_additiveCore_of_rigid` (live: `Grade/TheoremS.lean`'s docstring; kept:
  `notes/Phase40-design.md`, `notes/Prose-findings.md`). About 150 lines deleted (CoverageTheoremS
  673 → ~330, SparseCount ~215). G1–G7.
- [ ] **5. The reduction's fold: base, loop and cut-edge cases** (Opus: three files, an import
  reversal, a deleted pin). `ArmsAssembly.lean` imports `Grade/Arms`;
  `hasPencilRealization_of_ncard_le_two` is the `m = 1` case, and it gains
  `hasPencilRealization_of_isLoopAt`, `hasPencilRealization_of_not_twoEdgeConnected` and
  `hasDistinctPencilRealization_of_not_twoEdgeConnected`, moved from `Pencil/Arms.lean`, statements
  unchanged, proofs `Fold2ArmsAssembly.lean`'s with its two helpers (private; `n = 3` from
  `bodyBarDim n = screwDim 2`, a new site for FRICTION's *`bodyBarDim` has no monotonicity…*, and
  the cut's two sides). `Pencil/Arms.lean` loses the loop case
  (lines 56–165), `hasPencilRealization_of_not_twoEdgeConnected_core` (745–891, deleted) and the two
  forms. `pencil.tex`'s `lem:pencil-cut-case` pin drops `…_core`. Below `ArmsAssembly` (so `Pair`,
  `Pair2`, `X0`, `MainComponent/Statements`, the `Grade/Lift*` files, `Grade/Generic`) now sit
  `Grade/Realization`, `Grade/TwoPencil` and `Grade/Arms`; no cycle. Sweep `…_core` (live:
  `Arms.lean`, `pencil.tex`, FRICTION's open *42k's cases repeat…*; the rest kept); docstrings that
  place the moved cases in `Arms.lean` (`grep 'Arms.lean'`). FRICTION *42k build 2: the one-edge
  count…*: the inline `m = 1` count is gone. About 380 lines deleted. G1–G7.
- [ ] **6. The reduction's fold: the nonsimple case** (Sonnet).
  `hasGradedPencilRealization_of_not_simple` (`Grade/Reduction.lean` lines 40–300) moves verbatim to
  the end of `Grade/Arms.lean` (`Fold2NotSimpleOverArms.lean`); `Grade/Reduction.lean` keeps the
  theorem. `X0.lean`'s `hasPencilRealization_of_not_simple` (lines 66–~335), statement unchanged, is
  the `m = 1` case (`Fold2Statements.lean`). FRICTION *42k's cases repeat the `d = 3` cases' proofs*
  resolved, to the archive. Module docstrings of the three files. About 265 lines deleted. G1–G7.
- [ ] **7. Witness (2), part 1: `K_{2,3}` is feasible** (Opus: an explicit realization through the
  screw-space carrier). In `Nonvacuity.lean`, `Graph.OfSimpleGraph (completeBipartiteGraph (Fin 2)
  (Fin 3))` and `PencilNondegFeasible ℝ` of it, `WitnessK23.lean`'s RESIDUAL (b): points `e₀`,
  `e₁` at the two bodies of degree three, `e₂`, `e₃`, `e₂ + e₃` at the others, normals `e₁`, `e₀`,
  `e₃`, `e₂`, `e₂ − e₃` (each orthogonal to its own point and its neighbours'), each hinge the line
  through its ends' points; template `exists_isNondegPencilRealization_parallel_pair` (`Pair.lean`).
  Gates G1–G3, its axioms.
- [ ] **8. Witness (2), part 2: the good ear and the ear's condition** (Opus). Transcribe
  `WitnessK23.lean`'s `k23_goodEar_earLiftCondition` (`∃ W₀ x a b`, a good ear of `K_{2,3}`, and
  selectors at which `EarLiftCondition (K := ℝ)` holds at `x`, `a`, `b`), through
  `Graph.IsX0Graph.exists_goodEar_or_pendantTriangle` and `holdsGenerally_earFree`, discharging its
  leaves: (a1) `IsX0Graph` (connected from the two-edge-connectivity the spike derives); (a2)
  `0 ≤ s(Z)` for every nonempty `Z` (the one enumeration: `3(i + j − 1) − 2ij ≥ 0` at `i ≤ 2`,
  `j ≤ 3`; route open); (a3) `s(V) = 0`; (a4) no two bodies of degree two adjacent. Its own header
  and module-docstring bullet. G1–G3, its axioms. If (a2) does not close, land the rest as lemmas
  and append the assembly as task 8b.
- [ ] **9. The close** (Sonnet). Each task's sha in its line and in §3's mirrored lines; the
  *Candidates* line on the folds' new edges (*Scope*); the status surfaces of the open; the queue
  row's `done = true` only if CLEANUP-42 has nothing left.

## Candidates for the PI

- None yet.

## Moved to a later round

- None yet.

## Blockers / open questions

- None. Witness (2)'s leaf (a2) has no settled proof route (task 8).

## Hand-off / next phase

**Next concrete task:** task 3, witness (1), `K₂` at the generic conjunct (Sonnet, from
`scratch/cleanup-42/round4/WitnessK2.lean`). Then tasks 4–9 in order; the PI's stop applies to tasks 4–6.

## Decisions made during this round

- **The log, the order and the rungs** (the open): nine tasks, the PI's four items; the cheap
  docstring task first, as it shares no file with a fold; the folds before witness (2), whose file
  they do not touch either. Under *Scope*: the sweep, the `d = 3` proofs, the witnesses' home, the
  count, the gates.
