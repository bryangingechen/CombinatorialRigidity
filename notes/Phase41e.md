# Phase 41e — UNSTATED: the claims no declaration states (work log)

**Status:** in progress (opened 2026-10-29 with the PI), a sub-phase of Phase 41 and planned as its
last, so its close closes Phase 41 and the RECONCILE program. The phase's design, the PI's decisions
(here §1h.1, the scope, §1j, the open, and §1k, after U11's recon) and UNSTATED's open recon are in
`notes/Phase41-design.md`; the recon's Lean witnesses are
`notes/reconcile-formal/UnstatedWitness.lean`, for item R and U4
`notes/reconcile-formal/ReductionWitness.lean`, and for U11 `DofGenericWitness.lean`. Fifteen build items, two recons, a spike and the
close (planned 18–24 commits, the open included); U1–U11, R, PAD, U11's recon and M1K have
landed. Next: U12's spike, S3's route.

## Current state

**The next concrete commit is U12's spike** (*Hand-off*); U1–U11, R, PAD, U11's recon and M1K
have landed. M1K moved M1, the `main_results` row, to
`isInfinitesimallyRigidOn_ofHinge_isMaxRankHingePoints_iff_spanningTrees` (KT's genericity, §1k.2);
the count stays 20, its axioms the three standard ones. Each claim of the full
list (§1h.1) gets a declaration and a pin: S22–S25, S31, S3, S16, S19, G5's three
(`def:blockingWitness`, `def:dof-generic`, the Plücker expansion) and `F-061`'s forest lemma, with
§4(a). The PI also took, at the open (§1j): item R's build, which drops `hfresh` from KT Theorem
4.9's principle before U4, so that U4 assumes nothing of the labels; the rows form's restatement
without `hfresh` and the repointed `\uses` edge of `thm:theorem-55-6-rows`, both landed with U6; and
`G.shadowGraph`'s padding, dropped in its own commit PAD just before U10. Mode: structural edit.
The two red target nodes, `def:blockingWitness` (U1) and `def:dof-generic` (U11), were re-read at
the open (the red-node consistency gate): each states its notion consistently, and
`def:dof-generic`'s fmlnote ("The formalization defines neither notion") goes with U11.

**Re-read at `0a63c7ef`.** The recon was written at `3b9f766b`, before 41d restated
`Theorem55.lean`, `HingeGeneric.lean`, `PanelGeneric.lean` and the molecule chain. Every name,
file and line it cites resolves at HEAD, with these corrections, which the checklist carries:
- U4's form carried `hfresh`; with R taken, its source is `ReductionWitness.lean`'s last section,
  whose split step takes `e₀ ∉ E(G − v)`. `UnstatedWitness.lean`'s copy is superseded.
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
  `hC` relaxed, U7's `[G.Loopless]` dropped (and its unused `[Finite α]`, §1f.3), the rows form's `hfresh` and `[DecidableEq β]`
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

- [x] **U1. S25 and `def:blockingWitness`** (`F-041`; `F-038`, `F-008`'s part; landed:
  `SimpleGraph.IsBlockingWitness` and `not_isSparse_of_isBlockingWitness` in `Sparsity.lean`,
  `runPebbleGameWith_isBlockingWitness` in `PebbleGame/Correctness.lean`; the node pinned
  `\leanok`, `thm:pebble-game-correct` gains the pin; the docstring names a reject verdict's vertex
  set as the witness, corrected at verification).
- [x] **U2. S24** (`F-051`; landed: `Matroid.Union_rk_eq` and `Matroid.Union_indep_iff_count` in
  `Matroid/Constructions/Union.lean`, ported from Peter Nelson's `Matroid`, both pinned on
  `thm:matroid-partition-rank`, its note dropped; the criterion credited to the matroid-union
  theorem at verification, Edmonds 1965 being its `k`-copies case).
- [x] **U3. S23** (`F-083`; landed: `Graph.circuit_diff_isSpanningTreePacking` in
  `Operations.lean` after `circuit_induces_isTight`, the third pin of `lem:circuit-induces-rigid`,
  its note dropped; `D ≥ 2` from the copy index of `e`).
- [x] **R. KT Theorem 4.9's principle without `hfresh`** (§1j.1; design doc §2, *Item R's recon*;
  no ledger ID; landed as planned, one commit, from `ReductionWitness.lean`): four statements under
  `Molecular/Induction/` take `e₀ ∉ E(G − v)` (`minimal_kdof_reduction`, `splitOff_isMinimalKDof`,
  `circuit_splitOff_meets_fiber`, `splitOff_deficiency_le`), with the helpers
  `notMem_edgeSet_removeVertex(_iff)` and weaker forms of `removeVertex_le_splitOff` and
  `edgeSet_mulTilde_splitOff_diff_fiber`; four nodes restated, `lem:splitoff-edge-substitution`
  the new pin; at verification `lem:reduction-step` `\uses` `lem:splitoff-deficiency`.
- [x] **U4. S22** (landed: `Graph.minimal_kdof_reduction_sequence`, with `KTReductionStep` and
  `IsDoubleEdge`, in `ForestSurgery/Reduction.lean` after `minimal_kdof_reduction`, which needed
  the new import of `Contraction.lean`; no `hfresh`, `3 ≤ D` alone. Transcribed from the witness
  with R's names, no proof change. `thm:minimal-kdof-reduction` pins it beside (ii)'s and its
  fmlnote now says both parts are proved; the two definitions are unpinned helpers, their
  docstrings leading `a step of thm:minimal-kdof-reduction`.) (`F-101`)
- [x] **U5. S19** (`F-116`; landed: `BodyHingeFramework.case_I_rank_add_iff`, transcribed, in
  `CaseI.lean`'s first section, moved there from `Pinning.lean` at verification to keep imports
  off the chain; `lem:case-I` pins it first, its proof `\uses` the two counts the pin calls, its
  fmlnote says the pin asks no minimality).
- [x] **U6. §4(a)**, with the riders of §1j.2 and §1j.4 (landed): `rigidityMatrix_prop11`'s `hC`
  asks `u ≠ v`; the rows form `hasGenericFullRankRealization_of_theorem_55_gen` drops `hfresh`
  and `[DecidableEq β]`; `prop:rank-formula-of-motion-bound` and neighbours restated.
- [x] **U7. S16** (landed): `hasPanelRealization_of_generic` without `[G.Loopless]` and
  `[Finite α]`; `span_rigidityRows_eq_of_eq_off_loops` in `RigidityMatrix/Basic.lean`.
- [x] **U8. `F-061`'s forest lemma** (landed): `exists_independent_rigidityRows_of_isForest`;
  `public import Matroid.Graph.Forest` added upstream of `Basic`; node `lem:forest-rows-independent`.
- [x] **U9. The Plücker expansion** (`F-059`; landed): `extensor_repr_exteriorPower`, node
  `lem:plucker-expansion`.
- [x] **PAD. `G.shadowGraph`'s padding dropped** (§1j.3; landed): `shadowGraph : Graph V (Sym2 V)`,
  `card_shadowLabel_lt` deleted.
- [x] **U10. S31** (`F-174`, `F-183`; landed): `molecular_rigid_iff_square_rigid` in
  `Molecule/Application.lean`; `thm:molecular-iff-square-bar-joint` pins it second.
- [x] **U11, recon and build. `def:dof-generic`** (`F-008`'s part; design doc §2, *U11's recon*;
  witness `DofGenericWitness.lean`): `dof`, `dof_eq_zero_iff`, `IsMaxRankHingePoints` (nondegeneracy
  only between distinct bodies, a loop's hinge free), `lem:generic-hinge-points-max-rank`,
  `cor:dof-generic-realization`; `prop:rigidity-matrix-prop11` restated at KT's genericity (§1k.1),
  the JJ alignment row restated, no `main_results` row touched, no new import.
- [x] **M1K. M1 at KT's genericity** (design doc §1k.2; no ledger ID; landed): siblings
  `isInfinitesimallyRigidOn_ofHinge_isMaxRankHingePoints_iff(_spanningTrees)`, the second the
  `main_results` row (description restated, axioms standard); both directions through `dof`
  (U11's `dof_ofHinge_of_isMaxRankHingePoints`, `dof_eq_zero_iff`). The generic forms stay, second
  pins of `cor:bodyhinge-generic-rigid` and `-tree-packing`, both restated and moved after
  `cor:dof-generic-realization`. The three `Nonvacuity.lean` witnesses repointed and renamed.
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
  warnings, `lake lint`, the blueprint gates, the main results' axioms against 41d's close run,
  where M1K renamed M1's row; a new `main_results` row, if any, with its non-vacuity witness); the re-read of the restated
  chapters and the exposition ledger; the ledger's remaining `reported` and `left` entries given
  dispositions, and ROADMAP's RECONCILE bullet compressed (`notes/Reconcile.md` §3); ROADMAP's
  row flipped to ✓ and §41 compressed; README, the home page, `intro.tex` and
  `formalization.yaml` re-summarized (README and ROADMAP §34 name M1's generic form, which
  M1K kept beside the row's maximum-rank form); `.claude/autopilot/queue.toml`'s `RECONCILE-FORMAL` row
  `done = true`; `notes/MolecularConjecture.md`; the design doc's UNSTATED arc compressed (its
  anchors counted first); the dispatch log groomed; the project-organization review. The loop
  stops for the PI's push (§1j.5); ORIGAMI opens later, with the PI.

**Estimate.** 18–24 commits, the open and the close included (M1K's commit added by §1k.2): U1–U7 one each, R and PAD one each,
U8–U11 one or two each, U12 two, U11's recon and U12's spike none or one each. The recon's 15–21
moved by R's build (+1, §1j.1) and PAD as its own commit (+1, §1j.3); the riders of §1j.2 and
§1j.4 add none.

## Blockers / open questions

- None blocking. U12's spike may return to the PI, if the route does not compose (U12's size
  moves with it).

## Hand-off / next phase

**U12's spike** (checklist item *U12, spike*), compiler-checked and read-only: in `CaseII.lean`
(zone), extract the count in steps 7–14 of `case_II_realization_all_k`'s proof (`:295`) as a
lemma (a realization of `G_v^{ab}` of rank `N` gives `rank R(G, q₀) ≥ N + D − 1`), and compile the
proof calling it. A committed witness if it settles the route; it may return to the PI if the
route does not compose (*Blockers*). Then U12 itself (2 commits), then the close.

## Decisions made during this phase

- **The PI's decisions at the open** (2026-10-29): `notes/Phase41-design.md` §1j, verbatim.
- **The PI's decision after U11's recon** (2026-10-29): §1k, verbatim; KT Proposition 2.3 at
  KT's genericity rides on U11, and M1 follows as item M1K.
- **The placements** (the open's call under §1j): R its own commit before U4; the riders on U6,
  the earliest item that edits both `Theorem55.lean` (the rows form's file) and
  `panel-layer.tex`, and a mechanical one; PAD its own commit before U10, mechanical where U10 is
  a crux node with an uncompiled route.
