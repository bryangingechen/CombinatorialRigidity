# Phase 41e — UNSTATED: the claims no declaration states (work log)

**Status:** in progress (opened 2026-10-29 with the PI), a sub-phase of Phase 41 and planned as its
last, so its close closes Phase 41 and the RECONCILE program. The phase's design, the PI's decisions
(here §1h.1, the scope, and §1j, the open) and UNSTATED's open recon are in
`notes/Phase41-design.md`; the recon's Lean witnesses are
`notes/reconcile-formal/UnstatedWitness.lean` and, for item R and U4,
`notes/reconcile-formal/ReductionWitness.lean`. Fourteen build items, a recon, a spike and the
close (planned 17–23 commits, the open included); U1, U2, U3 and R have landed. Next: U4.

## Current state

**The next concrete commit is U4** (*Hand-off*); U1, U2, U3 and R have landed. Each claim of the full
list (§1h.1) gets a declaration and a pin: S22–S25, S31, S3, S16, S19, G5's three
(`def:blockingWitness`, `def:dof-generic`, the Plücker expansion) and `F-061`'s forest lemma, with
§4(a). The PI also took, at the open (§1j): item R's build, which drops `hfresh` from KT Theorem
4.9's principle before U4, so that U4 assumes nothing of the labels; the rows form's restatement
without `hfresh` and the repointed `\uses` edge of `thm:theorem-55-6-rows`, both riding on U6; and
`G.shadowGraph`'s padding, dropped in its own commit PAD just before U10. Mode: structural edit.
The two red target nodes, `def:blockingWitness` (U1) and `def:dof-generic` (U11), were re-read at
the open (the red-node consistency gate): each states its notion consistently, and
`def:dof-generic`'s fmlnote ("The formalization defines neither notion") goes with U11.

**Re-read at `0a63c7ef`.** The recon was written at `3b9f766b`, before 41d restated
`Theorem55.lean`, `HingeGeneric.lean`, `PanelGeneric.lean` and the molecule chain. Every name,
file and line it cites resolves at HEAD, with these corrections, which the checklist carries:
- U4's form carried `hfresh`; with R taken, its source is `ReductionWitness.lean`'s last section,
  whose split step takes `e₀ ∉ E(G − v)`. `UnstatedWitness.lean`'s copy is superseded.
- U6: `rigidityMatrix_prop11` (`PanelHinge.lean:1103`) still asks `hC` at every link. Its callers
  are `Theorem55.lean:2173` (passes `hC` itself), `:2273` (in
  `rankHypothesis_genuine_of_theorem_55_gen_of_supply`, renamed by 41d) and `:2854`, the last two
  passing `fun e _ _ _ => hC e`.
- U7's three callers are in `Theorem55.lean` (`:1802`, `:1851`, `:2050`), so its check for a
  now-unused `have : G.Loopless` is there, not in `GenericityDevice.lean`.
- U10: `exists_molecular_rankHypothesis_generalPosition` takes no label bound since 41d's B3, so
  "its bound met by `card_shadowLabel_lt`" goes (§1j.3); after PAD the selector is `Sym2 V → V × V`.
- U11's "after RELABEL" is met: 41d's B3 restated `HingeGeneric.lean`.
- U12: `case_II_realization_all_k`'s proof is about 710 lines (`CaseII.lean:295` to the file's
  end), not ~600.
- PAD's footprint is larger than §1j's bracketed note counts: `Application.lean` has two padded
  ascriptions too, one in the statement of the main result `molecule_generic_square_packing`, and
  `JacobsCounting.lean`'s `Sum.inl` steps go with its 12 ascription lines.
- The witnesses were not re-run. `UnstatedWitness.lean` (checked at `3b9f766b`) calls none of the
  declarations 41d restated, and the ones it calls are unchanged since. `ReductionWitness.lean` was
  checked at `953367f0`, the last commit to change library Lean. Each item runs its section first.

## Architectural choices made up front

- **Statements change only as §1h, §1j and the recon say** (`notes/Reconcile.md` §2, *Hygiene*).
  Each item adds a declaration and a pin. The statement changes are R's four strengthenings, U6's
  `hC` relaxed, U7's `[G.Loopless]` dropped, the rows form's `hfresh` and `[DecidableEq β]`
  dropped (§1j.2), and PAD's label type (§1j.3). A free strengthening only under §1f.3, recorded
  in the design doc.
- **The witnesses are the source.** Each build item checks its witness section with `lake lean`
  first, transcribes the proved ones, compiles the stated-only ones (S23, S24's criterion, S16,
  the forest lemma, the Plücker expansion, S31), and takes a shorter route that compiles, noted in
  its commit. The evidence files are not repointed.
- **The placements** (the open's call, §1j; why: *Decisions made*): R immediately before U4; the
  riders of §1j.2 and §1j.4 on U6; PAD immediately before U10.
- **The per-slice gates** (`CombinatorialRigidity/CLAUDE.md` *Forward-mode slices*) at every pin
  added or statement changed: changed statement, additive successor, deletion
  (`card_shadowLabel_lt` at PAD, `case_II_placement_eq612` at U12), moved pin
  (`scripts/check-docstring-labels.py` diffed against the parent).
- **Ledger.** Each commit names the ledger IDs it acts on; §4(a), R, the riders and PAD have none.
  One commit per dispatch (dispatch-log F53).
- **The loop** runs under §1j.5: no run cap, mechanical fixups pre-authorized, Sonnet and Opus
  dispatchable; it stops at 41e's close, which closes Phase 41, for the PI's push, and when the
  coordinator's context runs low.

## Lemma checklist

In the recon's order (isolated items, then the zone's one-commit items, then the rebuild-heavy and
crux items, then the two that need their own recon), with R before U4 and PAD before U10. "Zone"
is the fragility zone (`Molecular/AlgebraicInduction/`, `Molecular/RigidityMatrix/`, the
ScrewSpace carrier). Witness names are in `ReconUnstated` (`UnstatedWitness.lean`) and
`Graph.Recon41Reduction` (`ReductionWitness.lean`).

- [x] **U1. S25 and `def:blockingWitness`** (landed: `SimpleGraph.IsBlockingWitness` and
  `not_isSparse_of_isBlockingWitness` in `Sparsity.lean`, the pebble-game lemma in
  `Correctness.lean` with a `[Fintype V]` binder as `runPebbleGameWith_correct`; the node pinned
  `\leanok`, `thm:pebble-game-correct` gains the pin and a `\uses`; the definition's docstring
  corrected at verification, as a reject verdict's vertex set, not a pair, is the witness) (`F-041`; `F-038`, `F-008`'s part). New
  `SimpleGraph.IsBlockingWitness G k ℓ s :=
  ℓ ≤ k * s.card ∧ k * s.card < (G.edgesIn ↑s).ncard + ℓ` beside `IsSparse`
  (`Sparsity.lean:103`), with `not_isSparse_of_isBlockingWitness`; and
  `PartialOrientation.runPebbleGameWith_isBlockingWitness` (`PebbleGame/Correctness.lean`): under
  `ℓ < 2k`, a `.inl w` return from the empty orientation on a list of edges of `G` (`hmem` only)
  gives `G.IsBlockingWitness k ℓ w.V'`, by `runPebbleGameWith_witness_bridges` (`:401`) and
  `WorkhorseWitness.certifies_against` (`:500`). Proved in the witness. `def:blockingWitness`
  (`pebble-game.tex`, red) pinned and `\leanok`; `thm:pebble-game-correct` gains the pin. Outside
  the zone. 1 commit.
- [x] **U2. S24** (landed: `Matroid.Union_rk_eq` and `Matroid.Union_indep_iff_count` in
  `Union.lean`, both pinned on `thm:matroid-partition-rank`, whose note is dropped; the
  independence proof is `Union_pow_indep_iff_count`'s with the sum in place of `k * rk`, no shorter
  route tried; the file header credits Nelson's port as before; the criterion's credit corrected at
  verification to the matroid-union theorem, Edmonds 1965 being its `k`-copies case) (`F-051`). `Matroid.Union_rk_eq`, the rank of every `X` in the union of a finite
  family (proved: `Union_pow_rk_eq`'s proof without its `Finset.sum_const`), and
  `Matroid.Union_indep_iff_count`,
  `(Matroid.Union Ms).Indep X ↔ ∀ Y ⊆ X, Y.ncard ≤ ∑ i, (Ms i).rk Y`, by
  `Union_pow_indep_iff_count`'s proof (`S24IndepTarget`, stated only), in
  `Matroid/Constructions/Union.lean` (beside `:562` and `:588`; ported from Peter Nelson's
  `Matroid`: credit). `thm:matroid-partition-rank` pins both; its note goes. 1 commit.
- [x] **U3. S23** (landed: `Graph.circuit_diff_isSpanningTreePacking` in `Operations.lean`, after
  `circuit_induces_isTight`; the third pin of `lem:circuit-induces-rigid`, whose note is dropped.
  Proved as planned, with `D >= 2` from the copy index of `e`, so `IsTight.connected` needs no
  hypothesis; the bookkeeping was two small facts, `E(H) = X \ {e}` and that `H` and the
  restriction span the same vertices) (`F-083`). `Graph.circuit_diff_isSpanningTreePacking`
  (`Molecular/Induction/Operations.lean`, beside `circuit_induces_isTight` at `:164`): for a
  circuit `X` of `M(G̃)` and `e ∈ X`,
  `(((G.mulTilde n) ↾ (X \ {e})).induce (G.fiberSpan n X)).IsSpanningTreePacking (bodyBarDim n)`
  (`S23Target`, stated only), by `circuit_induces_isTight`,
  `isSparse_diff_singleton_of_isCircuit` (`Deficiency.lean:856`) carried to the induced graph,
  `IsTight.connected` and `isSpanningTreePacking_of_isTight` (`BodyBar/TreePacking.lean`). The
  friction is the `induce`/`restrict` bookkeeping (`E = X \ {e}`, `V = V(X)`).
  `lem:circuit-induces-rigid`'s third pin; its note goes. 1 commit.
- [x] **R. KT Theorem 4.9's principle without `hfresh`** (landed as planned, one commit: the four
  statements restated, the helpers `notMem_edgeSet_removeVertex` and `notMem_edgeSet_removeVertex_iff`
  in `Operations.lean`, the weaker forms `removeVertex_le_splitOff_of_notMem_removeVertex` and
  `edgeSet_mulTilde_splitOff_diff_fiber_of_notMem_removeVertex`, the landed forms kept as their
  corollaries; `splitOff_deficiency_le_aux` is gone, `splitOff_deficiency_le` being its
  generalization, and `splitOff_deficiency_le_of_eq_left` calls it at `eₐ`. The proof of
  `splitOff_isMinimalKDof` calls `splitOff_deficiency_le` directly, so `dof_tracking` is unchanged;
  at verification, three unpinned helpers' docstrings stopped naming a node as their own (the
  label ratchet), and `lem:reduction-step` `\uses` `lem:splitoff-deficiency`, the bound its pin
  calls, in place of `lem:dof-tracking`)
  (§1j.1; design doc §2, *Item R's
  recon*; no ledger ID). Source: `ReductionWitness.lean`, transcribed. Four statements, each a
  strengthening, files under `Molecular/Induction/`:
  - `Graph.minimal_kdof_reduction` (`ForestSurgery/Reduction.lean:578`): `hfresh` dropped, and
    `hsplit` given `P` at `G.splitOff v a b e₀` for every `e₀ ∉ E(G − v)` (form (b), the
    witness's `minimal_kdof_reduction'`). Its proof is the landed one, with the induction
    hypothesis at each admissible label.
  - `splitOff_isMinimalKDof` (`:151`, `lem:reduction-step`'s pin): `e₀ ∉ E(G − v)`, and
    `eₐ ≠ e_b` dropped; `chainData_extract`'s call (`ForestSurgery/ChainExtraction.lean:1284`)
    adapts.
  - `circuit_splitOff_meets_fiber` (`:66`): `e₀ ∉ E(G − v)`; its one caller is the lemma above.
  - `splitOff_deficiency_le` (`SplitOffDeficiency.lean:165`, `lem:splitoff-deficiency`'s pin; the
    private `splitOff_deficiency_le_aux` at `:49` generalized): `e₀ ∉ E(G − v)`. Its callers
    (`Reduction.lean:1466`, `:1534`, and `dof_tracking` at `SplitOffDeficiency.lean:590`) pass
    `e₀ ∉ E(G)` through the helper.

  Added: the helper `notMem_edgeSet_removeVertex`, and weaker forms of `removeVertex_le_splitOff`
  (`Operations.lean:702`) and `edgeSet_mulTilde_splitOff_diff_fiber` (`EdgeSplitting.lean:98`),
  the landed forms kept for their other callers (`CaseIII/Realization.lean`, `link_le_tac` at
  `PanelHinge.lean:320–321`, the `k > 0` surgery). No file of `AlgebraicInduction/` is edited.
  Not planned: `splitOff_deficiency_ge` without `he₀` and `dof_tracking` under `e₀ ∉ E(G − v)`
  (both compiled in the witness). Blueprint, four nodes: `thm:minimal-kdof-reduction`'s fmlnote
  (its statement stays); `rem:fresh-edge-supply`'s supply list loses the principle;
  `lem:splitoff-edge-substitution` (the new pin, under the additive-successor gate, and its
  fmlnote); `lem:splitoff-deficiency-reuse`'s fmlnote. `formalization.yaml`'s KT Theorem 4.9 row
  names no label condition, before or after. One full build, from `Operations.lean` through the
  molecular chain. 1 commit.
- [ ] **U4. S22** (`F-101`), R landed. `Graph.minimal_kdof_reduction_sequence`
  (`ForestSurgery/Reduction.lean`): `Relation.ReflTransGen` of a step relation
  (`KTReductionStep`: to a minimal `0`-dof-graph, by a split-off at a vertex of degree two at a
  label `e₀ ∉ E(G − v)`, the formal `G_v^{ab}`, or the contraction of a proper rigid subgraph)
  from `G` to a double edge, under `3 ≤ D` alone: **no `hfresh`** (§1j.1). Its proof is R's
  principle at `e₀ = eₐ`, with `isMinimalKDof_ncard_le_two_trichotomy` (`Deficiency.lean:3248`),
  `splitOff_isMinimalKDof` as R restates it and `rigidContract_isMinimalKDof`
  (`Contraction.lean:521`). Source: `ReductionWitness.lean`'s last section (proved). Not a main
  result. `thm:minimal-kdof-reduction` pins it beside (ii)'s; the note's first sentence goes.
  1 commit.
- [ ] **U5. S19** (`F-116`). `BodyHingeFramework.case_I_rank_add_iff` (proved): for a proper
  rigid `H` with `r ∈ V(H)` and frameworks `F`, `F₂`, if `rank R(F₂) = D(|V(G/E(H))| − 1) − def`
  of the contraction, then `rank R(F) = D(|V(G)| − 1) − def(G̃)` iff
  `rank R(F) = D(|V(H)| − 1) + rank R(F₂)`, by `rigidContract_deficiency_eq`
  (`Contraction.lean:566`) and `rigidContract_vertexSet_ncard` (`ReducibleVertex.lean:962`), with
  no minimality. Additive, beside the block-pin criteria in `AlgebraicInduction/Pinning.lean`; no
  fragile proof is touched. `lem:case-I` pins it first; its note's "No pinned theorem mentions the
  contraction" is rewritten; the three block-pin pins stay unless the label check moves them.
  1 commit.
- [ ] **U6. §4(a)** (no ledger ID: a new one), **with the riders of §1j.2 and §1j.4.**
  `rigidityMatrix_prop11` (`AlgebraicInduction/PanelHinge.lean:1103`): `hC` becomes
  `∀ e u v, F.graph.IsLink e u v → u ≠ v → F.supportExtensor e ≠ 0` (the witness's
  `rigidityMatrix_prop11'`, proved, one argument fewer). Its three callers in `Theorem55.lean`
  wrap: `:2173` passes `fun e u v h _ => hC e u v h`, and `:2273` and `:2854` add a binder to
  `fun e _ _ _ => hC e`. `prop:rank-formula-of-motion-bound` asks the hinge at the edges whose
  ends differ. Riders:
  - **The rows form** (§1j.2):
    `PanelHingeFramework.hasGenericFullRankRealization_of_theorem_55_gen`
    (`Theorem55.lean:2457`) repackages the bound-free
    `finrank_span_rigidityRows_genuine_recordsLinks_of_theorem_55_gen` (`:2431`), dropping
    `hfresh` and `[DecidableEq β]`; its docstring's supply clause goes.
    `thm:theorem-55-6-rows`'s fmlnote ("The second and third assume the supply", "The third
    restates the second") and `rem:fresh-edge-supply`'s supply list (`the second and third pinned
    on`) say the third pin assumes nothing of the labels.
  - **The `\uses` edge** (§1j.4): `thm:theorem-55-6-rows`'s statement `\uses` repoints
    `thm:theorem-55-6-genuine` to `thm:theorem-55`, what its Lean uses (every pin builds from
    `theorem_55_minimalKDof_gen_of_supply`); the proof's opening sentence, which cites the same
    node, is re-read with it.

  Zone, mechanical. 1 commit.
- [ ] **U7. S16** (`F-124`). `hasPanelRealization_of_generic` (`GenericityDevice.lean:862`)
  without `[G.Loopless]` (`S16Target`, stated; its one new step
  `span_rigidityRows_eq_of_eq_off_loops` proved): the framework is `Q.toBodyHinge` with the hinge
  at each loop at `u` replaced by `C(n_u, n_w)` for a body `w ≠ u` (`2 ≤ |V(G)|`), which lies in
  `u`'s panel (`exists_extensor_eq_panelSupportExtensor_gen`, `PanelLayer.lean:437`) and is
  nonzero by general position; the rows' span is unchanged, as a loop's rows are zero. Zone. Its
  three callers are in `Theorem55.lean` (`:1802`, `:1851`, `:2050`), which pass the instance
  today: check each for a now-unused `have : G.Loopless`. `lem:generic-yields-genuine-hinge`'s
  note on loops goes. 1 commit.
- [ ] **U8. `F-061`'s forest lemma.**
  `BodyHingeFramework.exists_independent_rigidityRows_of_isForest` (`ForestTarget`, stated): for a
  forest `T ≤ F.graph` (`Graph.IsForest`) with a nonzero hinge at each edge, `D − 1` rows per
  edge, jointly independent, in `exists_independent_rigidityRows_of_starForest`'s shape
  (`RigidityMatrix/Basic.lean:1205`). Route: induction on `|E(T)|` removing a pendant edge (the
  `Matroid` package's `IsForest.exists_isPendant` and `IsForest.anti`); its rows stay independent
  on the assignments supported at the pendant body, where the others vanish, and
  `linearIndependent_sum_pinned_block` (`:902`) joins them. Zone: an interface change in
  `Basic.lean` rebuilds the molecular chain. A new node after `lem:own-end-rows-independent`.
  1–2 commits.
- [ ] **U9. The Plücker expansion** (`F-059`). The coordinates of `extensor v` in
  `(Pi.basisFun K (Fin (d+1))).exteriorPower j` are the Plücker coordinates times KT's sign
  (`PluckerTarget`, stated), by mathlib's `exteriorPower.basis_repr_apply` and
  `ιMultiDual_apply_ιMulti` (the minor), against `pluckerCoord`'s `orderEmbOfFin` submatrix
  (`Molecular/Extensor.lean:430`). The friction is the index bridge
  (`Set.powersetCard.ofFinEmbEquiv` against `Finset.orderEmbOfFin`) and a transpose. The chain's
  root, so a full rebuild. A lemma node after `def:plucker-coords`; its note goes. 1–2 commits.
- [ ] **PAD. `G.shadowGraph`'s padding dropped** (§1j.3; no ledger ID), immediately before U10,
  so that U10 is stated over `Sym2 V`. `SimpleGraph.shadowGraph : Graph V (Sym2 V)`
  (`Molecule/Carrier.lean:53`), linking `x` and `y` by `s(x, y)` when `G.Adj x y`;
  `card_shadowLabel_lt` (`:89`) deleted under the deletion gate; the module and definition
  docstrings restated. The padded type's other occurrences (grep `Fin (6 \* (Nat.card`):
  `JacobsCounting.lean` (12 ascription lines, `:142`–`:430`, and the `Sum.inl`, `Sum.inl.injEq`
  and `Sum.inl_injective` steps with them), `CombinatorialRigidity/Nonvacuity.lean` (`path3`
  `:701` and `treeWalk` `:708`, with their labels) and `Molecule/Application.lean` (`let ends`
  `:130`, and `:247` in the statement of `molecule_generic_square_packing`, a main result whose
  label type changes: `cor:molecule-generic-square-packing` and its `formalization.yaml` row
  re-read). Blueprint: `lem:molecule-graph-carrier` loses its fifth pin and "more than
  6(|V| − 1) labels", its proof the further labels, its fmlnote the bound; the nodes that cite it
  (`jacobs.tex` three, `molecule-application.tex` two, `generic-lift.tex` one) re-read. One full
  build. Mechanical. 1 commit.
- [ ] **U10. S31** (`F-174`, `F-183`), after PAD. `SimpleGraph.molecular_rigid_iff_square_rigid`
  (`S31Target`, stated; after PAD its selector is `ends : Sym2 V → V × V`), under `[Nonempty V]`
  and `hmin`: some selector recording the links of `G.shadowGraph` and centres distinct at each
  edge give an infinitesimally rigid molecular framework iff `G²` has an infinitesimally rigid
  placement. (⇒) nondegenerate hinges (`lineExtensor_ne_zero_of_ne`) and
  `screwDim_add_deficiency_le_finrank_infinitesimalMotions` give `def = 0`, then
  `molecule_generic_rigid` at `exists_isGenericPlacement`. (⇐) The rigid placement bounds the
  generic rank (`finrank_range_rigidityMap_le_genericRank`), `molecule_rank_formula` and
  `deficiency_nonneg` give `def = 0`, and `exists_molecular_rankHypothesis_generalPosition`
  (`Modelling.lean:78`, no label bound) with `rankHypothesis_zero_iff` gives the framework, its
  centres distinct by general position. `Molecule/Application.lean`.
  `thm:molecular-iff-square-bar-joint`'s second pin; its note's last sentences go. A crux node:
  its exposition-ledger entry is re-read. 1–2 commits.
- [ ] **U11, recon. `def:dof-generic`** (`F-008`'s part): read-only first, the
  definition-faithfulness gate. The witness's candidates: `dof F = D(|V(G)| − 1) − rank R(G,p)`,
  and `IsMaxRankHingePoints G q` (nondegenerate at the non-loop links, and at every `E' ⊆ E(G)`
  the rows of `ofHinge (G ↾ E') q` of the largest rank over the hinge-point assignments with that
  property), which the paragraph after `lem:generic-hinge-points-nondegenerate` derives from
  `IsGenericHingePoints` (`HingeGeneric.lean:216`) for loopless `G`. Open: which carrier stands
  for "all realizations of `G`"; loops, whose hinge points genericity leaves free; whether KT
  Proposition 2.3 then holds at every such realization (a main result's statement: the PI's). Its
  verdict goes to the design doc's §2 in one docs commit, as item R's did; a main-result change
  goes to the PI before U11 builds. 0–1 commits.
- [ ] **U11. `def:dof-generic` built** as its recon settles, in `GenericLift/HingeGeneric.lean`;
  the node pinned and `\leanok`, its fmlnote rewritten. 1–2 commits.
- [ ] **U12, spike. S3's route** (compiler-checked, read-only): in `CaseII.lean` (zone), the count
  in steps 7–14 of `case_II_realization_all_k`'s proof (`:295`, about 710 lines) extracted as a
  lemma, a realization of `G_v^{ab}` of rank `N` giving `rank R(G, q₀) ≥ N + D − 1`
  (`D(|V(G)| − 1) − 1` at a rigid one), and the proof calling it, compiled. A committed witness if
  it settles the route. 0–1 commits.
- [ ] **U12. S3** (`F-150`; the dead pin, `F-152`'s part). A declaration for
  `lem:case-II-realization-placement` as stated, from a realization of `G_v^{ab}`: the spike's
  lemma, which `case_II_realization_all_k` then calls; `case_II_placement_eq612`
  (`CaseII.lean:67`), dead and unmeetable in Cases II and III, deleted with the repin under the
  deletion gate (its mention in `GenericityDevice.lean:258`'s docstring included). 2 commits.
- [ ] **Close**, a full-phase close (Phase 41 and the RECONCILE program,
  `PHASE-BOUNDARIES.md` *When this commit closes a phase*): the gates (whole-project build with 0
  warnings, `lake lint`, the blueprint gates, the main results' axioms against 41d's close run; a
  new `main_results` row, if any, with its non-vacuity witness); the re-read of the restated
  chapters and the exposition ledger; the ledger's remaining `reported` and `left` entries given
  dispositions, and ROADMAP's RECONCILE bullet compressed (`notes/Reconcile.md` §3); ROADMAP's
  row flipped to ✓ and §41 compressed; README, the home page, `intro.tex` and
  `formalization.yaml` re-summarized; `.claude/autopilot/queue.toml`'s `RECONCILE-FORMAL` row
  `done = true`; `notes/MolecularConjecture.md`; the design doc's UNSTATED arc compressed (its
  anchors counted first); the dispatch log groomed; the project-organization review. The loop
  stops for the PI's push (§1j.5); ORIGAMI opens later, with the PI.

**Estimate.** 17–23 commits, the open and the close included: U1–U7 one each, R and PAD one each,
U8–U11 one or two each, U12 two, U11's recon and U12's spike none or one each. The recon's 15–21
moved by R's build (+1, §1j.1) and PAD as its own commit (+1, §1j.3); the riders of §1j.2 and
§1j.4 add none.

## Blockers / open questions

- None blocking. Two items may return to the PI: U11's recon, if `def:dof-generic` moves a main
  result's statement; and U12's spike, if the route does not compose (U12's size moves with it).

## Hand-off / next phase

**U4** (S22, checklist item U4; source the last section of `ReductionWitness.lean`):
`Graph.minimal_kdof_reduction_sequence` and its step relation `KTReductionStep` (the split clause
at a label `e₀ ∉ E(G − v)`) in `ForestSurgery/Reduction.lean`, proved from item R's principle at
`e₀ = eₐ` (`notMem_edgeSet_removeVertex_iff` gives its admissibility); pinned beside
`thm:minimal-kdof-reduction`'s (ii), whose first-sentence note goes. One commit.

## Decisions made during this phase

- **The PI's decisions at the open** (2026-10-29): `notes/Phase41-design.md` §1j, verbatim.
- **The placements** (the open's call under §1j): R its own commit before U4; the riders on U6,
  the earliest item that edits both `Theorem55.lean` (the rows form's file) and
  `panel-layer.tex`, and a mechanical one; PAD its own commit before U10, mechanical where U10 is
  a crux node with an uncompiled route.
