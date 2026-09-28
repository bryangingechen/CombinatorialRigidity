# Phase 40l — PENCIL-X0 / COVERAGE-REDUCE: the one-step interface, the induction and the deficiency layer (work log)

**Status:** in progress (opened design-first 2026-09-28). COVERAGE's first sub-phase, **REDUCE**
(`notes/Phase40-design.md` §3 COVERAGE; the PI's calls in `notes/pencil/adjudications.md`,
2026-09-28). It lands the one-step predicate `X0Reduces`, which packages each landed step's
hypotheses; the strong induction on the number of bodies, carried on the statement "every graph
satisfying (H) reduces to smaller ones"; and the deficiency layer of the structural half: the
singleton bound, (MC-75)(i), (MC-76), merging along a rigid set, (MC-79)(ii)(iii) and (MC-87), with
the departures D1–D3. No workbook change. Eleven red nodes to green in three builds, both spikes
sorry-free. **Next: B1, the interface** — see *Hand-off*. CHAINS and THEOREM-S follow, by code.

## Current state

**Opened.** Two new subsections of `main-component.tex`, before `sec:main-component-statements`,
transcribe COVERAGE's whole node plan (the "transcribe a layer's section when it opens" rule), all
red, with no `\lean{…}` yet (40h's open convention; planned pins in the checklist). Statements are
the compiled spike statements. Which sub-phase greens each node:
- **§`sec:main-component-sparse` (REDUCE, this sub-phase):** `lem:deficiency-singleton-bound`,
  `lem:deficiency-add-body`, `lem:deficiency-sparse`, `lem:deficiency-merge-rigid`,
  `lem:deficiency-tight-rigid`, `lem:deficiency-core-bound`, `lem:deficiency-additive-core`,
  `lem:deficiency-one-body-chain`, `lem:deficiency-two-body-chain`.
- **§`sec:main-component-coverage`:** `def:pencil-x0-reduces` and
  `thm:pencil-x0-reduction-attains` (REDUCE, B1); `def:pencil-x0-chain`,
  `lem:pencil-x0-chain-exists`, `lem:pencil-x0-chain-standing`, `lem:pencil-x0-cycle-reduces`,
  `lem:pencil-x0-cut-reduces` (CHAINS; the cut half's statements are S5's interface statements,
  unspiked); `def:pencil-x0-usable-chain`, `lem:pencil-x0-chain-reduces`,
  `lem:pencil-x0-planar-rigid-reduces`, `lem:pencil-x0-sparse-count`,
  `thm:pencil-x0-theorem-s`, `thm:pencil-x0-coverage` (THEOREM-S).
- `thm:pencil-x0-generic-attains` `\uses` `thm:pencil-x0-coverage` and stays red (MOTIVES);
  `rem:pencil-x0-theta` is reworded (D4). The chapter preamble names both subsections.

**The spikes** (gitignored `scratch/40l/`, local to this checkout; builder pointers, not evidence;
**keep them**: CHAINS and THEOREM-S transcribe from S5 too), run with **`lake lean`** at `f7481590`,
matching the coordinator's re-run:
- `S1Dispatch.lean` (140 lines; B1's source): exit 0, no warnings, no `sorry`; two axioms lines,
  standard.
- `S4Kit.lean` (812 lines; B2's and B3's source): exit 0, no `sorry`, 25 warnings (deprecations,
  one `show`, one unused variable, one long line); sixteen axioms lines, standard.
- `S5Full.lean` (1 930 lines): the kit, the interface and CHAINS' and THEOREM-S' material composed;
  exit 0, exactly five `sorry`s (lines 960–982, the plumbing statements); 21 axioms lines standard,
  six on `sorryAx` (the composites over the five).
- `S6Inst.lean` (instances): exit 0, no `sorry`. `measure.py`: the recon's output.
- **Satisfiability** (not landed). Kernel-checked in S6: `X0Reduces` at `C₄` (the cycle clause);
  `IsChain` at `K₄` with every edge subdivided twice, chain `0 − 4 − 5 − 1`, degrees by `decide`;
  `ChainUsable` by its `k ≥ 3` clause. Measured (`measure.py`, coverstruct's exact deficiencies):
  that graph is sparse, `def₂ = 9`, `def₃ = 0`, six two-body chains with `δ = δ₂ = 3`, all
  usable; the necklaces QsQsQ, AsAsAs, QQQQQ, TsTsTs have no usable chain, and Theorem S's core
  meets `hatt` and `hadd` (1+4≤5, 1+5≤6, 1+6≤7, 2+10≤12); sixteen θ-graphs each reach FLAT,
  CONTRACT-R or a usable chain (D4).
- **Faithfulness.** Each `X0Reduces` clause is one landed step's hypothesis list verbatim (the
  dispatch compiles against all thirteen step calls). The kit lemmas state the workbook claims at
  their Lean strength: (MC-76) one direction; (MC-79)(ii)'s first claims and first bullet; (MC-79)(iii)
  as `δ₂ ≥ 2` from `a ≁ b`, `δ ≠ 0`; (MC-87)(i)'s "if" half in the `≤` form without "`G/H`
  simple"; (MC-87)(ii) at any maximal rigid set avoiding `X₀`.

## Architectural choices made up front

- **The route** (the recon's verdict; `notes/Phase40-design.md` §3 COVERAGE): `X0Reduces` (a
  non-recursive one-step predicate, not the ruled-out `Covered`), the dispatch, the carried
  induction, and a partition kit built on the landed `partitionDef_split_of_sides` and
  `partitionDef_merge`. Proof-level departures, recorded in the node proofs and not second-read
  (the PI's call, the 40k precedent): **D1** the core bound by a minimal counterexample
  (`lem:deficiency-core-bound`); **D2** (MC-79)(ii)'s first bullet by refining one part
  (`lem:deficiency-one-body-chain`); **D3** "a tight set of three or more bodies is rigid"
  (`lem:deficiency-tight-rigid`, used by `lem:deficiency-two-body-chain`); **D4** no θ branch
  (THEOREM-S).
- **The PI's calls (2026-09-28, verbatim in `notes/pencil/adjudications.md`):** three sub-phases
  with named interfaces, REDUCE = 40l (S1 + S4), CHAINS, THEOREM-S; D1–D4 in the blueprint, no
  second reading; `X0Reduces` adopted; settled by precedent at this open: PI decision 2's `hatt`
  todo closed with `hatt` kept, the unconsumed claims re-homed to the design doc's §2 *Not needed*
  with the caveat, §7's D5 list completed.
- **Layout (the recon's, kept).** `MainComponent/Coverage.lean` for the interface (imports
  `SplitOff.lean`, `Chain.lean`, `Contract.lean`, `ContractAdditive.lean`, the four step files not
  already below one another); `Molecular/Induction/SparseDeficiency.lean` for the kit (imports
  `Induction/ReducibleVertex.lean` for `rigidContract` and the mirror
  `Mathlib/Combinatorics/Graph/Delete.lean` for `induce_induce_of_subset`), beside
  `SplitOffDeficiency.lean`: `Deficiency.lean` is at 4 389 lines, past the tripwire, and nothing
  outside COVERAGE consumes the kit. Both are new leaf modules, added to the root import.
- **D5 pins paid here:** `Graph.partitionDef_map` and `Graph.deficiencyMerged_le_deficiency` (on
  `lem:deficiency-additive-core` and `lem:deficiency-merge-rigid`).

## Lemma checklist

Pins in **bold**, the other names unpinned helpers. S4 line ranges are `scratch/40l/S4Kit.lean`'s.

- [ ] **B1, the interface** → new `Coverage.lean`: `Graph.IsOpenEar`, `Graph.X0Reduces`,
  `Graph.X0Below` (from S5, the three-line abbrev, the codomain of CHAINS' and THEOREM-S'
  interface statements), `Graph.X0Reduces.x0Attains`, `Graph.X0Attains.of_isX0Graph_of_x0Reduces`.
  Nodes: `def:pencil-x0-reduces` (**`Graph.IsOpenEar`, `Graph.X0Reduces`**),
  `thm:pencil-x0-reduction-attains` (**`Graph.X0Reduces.x0Attains`,
  `Graph.X0Attains.of_isX0Graph_of_x0Reduces`**).
- [ ] **B2, the value calculus** → new `SparseDeficiency.lean`, S4 lines 12–207, 263–366,
  523–575:
  - `lem:deficiency-singleton-bound`: **`Graph.partitionDef_le_partitionDef_id`,
    `Graph.partitionDef_add_partitionDef_induce_id_le`**;
  - `lem:deficiency-add-body`: **`Graph.partitionDef_induce_insert`,
    `Graph.deficiency_induce_insert_eq_zero`**;
  - `lem:deficiency-sparse`: **`Graph.exists_deficiency_induce_eq_zero_of_partitionDef_id_nonpos`,
    `Graph.one_le_partitionDef_induce_id`**;
  - `lem:deficiency-merge-rigid`: **`Graph.exists_partitionDef_le_mergeOn`,
    `Graph.deficiencyMerged_le_deficiency`** (landed; D5), **`Graph.deficiencyMerged_eq_deficiency_of_mem`**;
  - helpers: `partitionDef_eq_zero_of_forall_eq`, `partitionDef_induce_singleton_id`,
    `bodyBarDim_two`, `bodyBarDim_three`, `partitionDef_three_eq`, `partitionDef_induce_id_nonneg`,
    `mem_crossingEdges_induce`, `exists_maximal_deficiency_induce_eq_zero`,
    `partitionDef_eq_of_forall_iff`, `exists_glue`.
- [ ] **B3, the suppliers** → `SparseDeficiency.lean`, S4 lines 209–262, 368–522, 576–794:
  - `lem:deficiency-tight-rigid`: **`Graph.deficiency_three_induce_eq_zero_of_tight`**;
  - `lem:deficiency-core-bound`: **`Graph.deficiency_three_induce_eq_zero_of_le`,
    `Graph.partitionDef_induce_id_le_of_maximal`**;
  - `lem:deficiency-additive-core`: **`Graph.partitionDef_map`** (landed; D5),
    **`Graph.deficiency_induce_add_deficiency_rigidContract_le`** (helper
    `partitionDef_deleteEdges_induce_eq`);
  - `lem:deficiency-one-body-chain`: **`Graph.not_adj_and_deficiencyMerged_two_add_two_le`,
    `Graph.deficiencyMerged_three_add_five_le`**;
  - `lem:deficiency-two-body-chain`: **`Graph.deficiencyMerged_two_add_two_le`**.
- [ ] **The close** (docs and blueprint): the re-read of both subsections; headline axioms on the
  21 new pins and the `formalization.yaml` main results, one `#print axioms` line each under
  `import CombinatorialRigidity` with `lake lean` after a full `lake build` (the 40k method); the
  design doc, ROADMAP, `MolecularConjecture.md`; the public surfaces unchanged (the PI's standing
  call: they update when Phase 40 closes); the exposition-ledger candidates (D1's minimal
  counterexample, D3's tight-set count).

## Blockers / open questions

- None blocking B1.
- **Builder notes.**
  - B1: S1 compiles warning-free as is. Write real docstrings and a module docstring listing the
    statements (the `Cut.lean` pattern). `Graph.IsChain` is not in B1 (CHAINS).
  - B2/B3: fix S4's 25 warnings on transcription: `if_pos`/`if_neg`/`dif_pos` → the suggested
    `ite_eq_left`/`ite_eq_right`/`dite_eq_left` (or `simp only`), `Set.mem_setOf_eq` →
    `Set.mem_ofPred_eq`, `Set.insert_diff_singleton` → `Set.insert_sdiff_singleton`, the `show`
    at S4:153 → `change`, the long line at S4:666; `push Not`, not `push_neg`.
  - `partitionDef_induce_id_le_of_maximal`'s `hWV : W ⊆ V(G)` is unused (S4:407): drop it, and
    THEOREM-S drops the argument at its one call site (S5's `exists_additiveCore_of_rigid`).
  - Every new top-level name greps to no prior definition (this open's check, TACTICS-QUIRKS §65).
    Root-level `IsChain` (mathlib, sets) exists; the CHAINS builder uses `Graph.IsChain` qualified
    or by dot notation.

## Hand-off / next phase

**The next concrete commit is B1, the interface** (fresh builder; sonnet at S=1 suffices). Source
`scratch/40l/S1Dispatch.lean` (gitignored, local to this checkout), lines 14–135, verbatim, plus
`Graph.X0Below` from `scratch/40l/S5Full.lean` lines 931–933. Target: new
`CombinatorialRigidity/Molecular/Molecule/Pencil/MainComponent/Coverage.lean`, `namespace
CombinatorialRigidity.Molecular`, `variable {K : Type*} [Field K] {α β : Type*}`, importing exactly
S1's four imports (`…MainComponent.SplitOff`, `.Chain`, `.Contract`, `.ContractAdditive`); add it
to `CombinatorialRigidity.lean`. The declarations: `Graph.IsOpenEar`, `Graph.X0Reduces`,
`Graph.X0Below`, `Graph.X0Reduces.x0Attains`, `Graph.X0Attains.of_isX0Graph_of_x0Reduces`.
Chores:
- copyright header and a module docstring listing the five declarations; real docstrings;
- blueprint: pin and flip `def:pencil-x0-reduces` (`\lean{Graph.IsOpenEar, Graph.X0Reduces}`,
  `\leanok`) and `thm:pencil-x0-reduction-attains` (`\lean{Graph.X0Reduces.x0Attains,
  Graph.X0Attains.of_isX0Graph_of_x0Reduces}`, `\leanok` on statement and proof);
- gates: `lake build`, `lake lint`, `blueprint/verify.sh`, `blueprint/lint.sh`,
  `notes/check-phase-note.py`; this note's checklist, *Current state* and *Hand-off*.

**Then B2 and B3** (`SparseDeficiency.lean`, about 350 and 430 lines; the checklist), **then the
close.** After 40l: **CHAINS** opens (a spike of its cut half first; about 5–7 builds), then
**THEOREM-S** (about 2 builds; closes COVERAGE). Both transcribe from `scratch/40l/S5Full.lean`
(design doc §3 COVERAGE lists each one's interface statements).

## Decisions made during this phase

- **2026-09-28 — opened design-first** from COVERAGE's design recon (opus, read-only,
  compiler-checked); the spikes re-run at `f7481590` with `lake lean` match the coordinator's
  counts. The PI's calls are under *Architectural choices*.
