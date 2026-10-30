# Phase 42b — PD-STATE: the pencil's statement layer in every dimension (work log)

**Status:** in progress, opened 2026-10-30 beside 42a (the PI's planning default, design doc §1,
item 4), the Lean under `/coordinate-phase`. Forward mode: the dep-graph is
`blueprint/src/chapter/pencil-d.tex`, 17 nodes, all 17 green (the collineation lemma, the
configuration, the scale-shift, the contraction's rank, the attaining definition and its `d = 3` agreement, `def:extensor-through-flat` and its point form, `def:pencil-d-realization` and its `d = 3` agreement, `def:pencil-d-rank-hypothesis`, `def:pencil-d-distinct-motive`, `lem:pencil-d-rank-agrees-three`, `lem:pencil-d-point-configuration`, `lem:pencil-d-config-realization`, `lem:pencil-d-x0-one-witness`, `lem:pencil-d-join-independence-open`), Lean in `Pencil/Grade/`. The carrier is the PI's (2026-10-30, design doc §1): the
dual form with each body's 3-space as data, as the chapter states. The chapter is all green; next concrete task: the phase-close review
(`PHASE-BOUNDARIES.md`, coordinator).

## Current state

**Next:** none in the chapter (all nodes green); the phase-close review, run separately by the coordinator.

**Landed:** `lem:pencil-d-join-independence-open` (`Pencil/Grade/JoinIndependence.lean`, new, imports
`Grade/Witness.lean` and `PanelLayer.lean`): `exists_mvPolynomial_linearIndependent_normalsJoin` (the
shared step: points with polynomial coordinates, the coordinates of `normalsJoin` being
`normalsJoinPoly` composed with them, fed to `exists_polynomial_ne_zero_of_linearIndependent_at_reindex`
through `b.equivFun` of the exterior-power basis) and the two halves
`exists_mvPolynomial_linearIndependent_join_picture_grade` / `…_heights_grade` (joins of
`pencilConfigPointGrade` as `normalsJoin`). `map_vecCons_vecCons_snoc` is now non-private in `Witness.lean`.

**Landed:** `lem:pencil-d-x0-one-witness` (`Pencil/Grade/Witness.lean`, new, imports
`Grade/Configuration.lean`): `Graph.x0AttainsGrade_of_exists` (`hz₀ : z₀ ∈ G.liftingSpaceGrade q₀ m`,
`hrank` at `ofNormals (k := m + 1)` at `pencilConfigPointGrade q₀ z₀`, conclusion
`G.X0AttainsGrade K m`), the `d = 3` proof `Graph.x0Attains_of_exists` with one polynomial section
`(D i, Z i)` per height (`choose`), `P = Padm * ∏ D i * Qsec`; and
`Graph.IsAdmissiblePicture.supportExtensor_ne_zero_grade`. The private
`map_vecCons_vecCons_snoc` (a ring map through the block layout of `pencilConfigPointGrade`) does the
coordinate checks by `Fin.cases`/`Fin.lastCases`. The CARRIER item is done with it:
`Graph.bodyBarDim_add_one_eq_screwDim` (`PanelLayer.lean`, beside `bodyBarDim_eq_screwDim_sub_one`),
and the inline use in `screwDim_add_deficiency_le_finrank_infinitesimalMotions` repointed to it.

**Landed:** `lem:pencil-d-config-realization` (`Pencil/Grade/Configuration.lean`, new, imports
`Grade/Carrier.lean` and `Grade/Realization.lean`):
`Graph.IsAdmissiblePicture.hasPencilPlaneRealization_ofNormals_pencilConfigPointGrade` (the first
sentence, on `P.toPatchedBodyHinge`, `plane v` the span of the closed neighbourhood's points, with
independent normals at links) and `Graph.IsAdmissiblePicture.hasGradedDistinctPencilRealization`
(`hz : z ∈ G.liftingSpaceGrade q m`, `hrank` at `ofNormals (k := m + 1)`, conclusion at grade
`m + 1`, deficiency at `m + 2`), with the helpers `…_pencilConfigPointGrade_pair`,
`linearIndependent_pencilConfigPointGrade_of_linearIndependent_pencilPicturePoint` (the projection to
coordinates `0, 1, last`) and `finrank_span_pencilConfigPointGrade_closedNbhd_le` (the range of one
linear map from `K³`).

**Landed:** `lem:pencil-d-point-configuration` (`Grade/Realization.lean`, which now imports
`Pencil/Motive.lean` for `Graph.closedNbhd`). Part (1),
`PanelHingeFramework.hasPencilPlaneRealization_toPatchedBodyHinge` (`[NeZero k]`; nonzero normals on
`V(G)`, independent at links, `plane v` three-dimensional containing the closed neighbourhood's
normals), on `P.toPatchedBodyHinge` (*Decisions*), with `span_rigidityRows_toPatchedBodyHinge`.
Part (2), `HasPencilPlaneRealization.supportExtensor_eq_smul_panelSupportExtensor` (independence at
the link, any `k`) and `.normal_mem_plane_of_mem_closedNbhd` (no independence). Grade-general helpers:
`span_range_eq_of_extensor_eq_grade`, `extensorInPanel_panelSupportExtensor_gen`,
`extensorThroughSubspace_panelSupportExtensor`, `exists_smul_panelSupportExtensor_eq_of_extensorInPanel`
(through `extensor_join_proportional_complementIso_meet`); FRICTION mirror-candidate for their homes.

**Landed:** `def:pencil-d-distinct-motive` and the second equivalence of `lem:pencil-d-rank-agrees-three`
(`Grade/Realization.lean`): `HasGradedDistinctPencilRealization K k n G` is `HasGradedPencilRealization`
plus independent normals `![normal u, normal v]` at every link; `hasGradedDistinctPencilRealization_two_iff`
applies the polarity once per direction (the carrier check: `HasDistinctPencilRealization` asks
independence of the POINTS, so the polar framework's points are the graded one's normals). The file
now imports `GenericLift/HingeGeneric.lean` for `finrank_span_rigidityRows_mapExtensor`; the lemma
node is green with both names and the chapter's proof text matches.

`def:pencil-d-rank-hypothesis` (`Grade/Realization.lean`):
`HasGradedPencilRealization K k n G` (order of `HasPencilRealization`, then `k`; `n` a parameter, the
chapter's deficiency "at `D`" read at `n = k + 1`), and `hasGradedPencilRealization_two_iff`, the
first equivalence of `lem:pencil-d-rank-agrees-three` (red until the second).

`def:pencil-d-realization` and `lem:pencil-d-agrees-three` (`Grade/Realization.lean`):
`HasPencilPlaneRealization G F normal plane` (`plane : α → Submodule K (Fin (k + 2) → K)`, asked
on `V(G)`), `dotPerp` with `mem_dotPerp`, `dotPerp_dotPerp`, `finrank_dotPerp` and
`exists_eq_dotPerp_span_singleton`; `hasPencilPlaneRealization_two_iff` (pointwise, `hplane : ∀ v ∈
V(G), plane v = dotPerp (K ∙ point v)`, no `point v ≠ 0` needed) and the `∃ plane ↔ ∃ point` form;
`exists_hasPencilPlaneRealization_one_iff` (grade `1` is hinge-coplanarity, pinned on the def).
`def:extensor-through-flat` and `lem:extensor-through-flat-point` (`Grade/Realization.lean`):
`ExtensorThroughSubspace C A` is `ExtensorThroughPoint` with
`A ≤ span (range p)`, and `extensorThroughSubspace_span_singleton_iff` is `span_singleton_le_iff_mem`;
the zero element is not excluded (a dependent family has extensor `0`), so the hinge is asked
nonzero separately. The open (the chapter, its nodes red with planned names; the carrier check, design doc
§2.3; PD-STABLE's statements, design doc §3). `lem:pencil-d-rank-collineation`
(`Pencil/Grade/Collineation.lean`): one automorphism `det g • Λ_h` of `ScrewSpace K k`, `h` the
contragredient, maps every hinge (`panelSupportExtensor_linearEquiv_eq_det_smul`).
`def:pencil-d-configuration` (`Pencil/Grade/Carrier.lean`): `pencilConfigPointGrade`, its
coordinates, and its agreement with the picture point (no height) and `pencilConfigPoint` (one).
`lem:pencil-d-rank-scale-shift` (`Grade/Carrier.lean`, now importing `Grade/Collineation.lean`): `T`
an automorphism of `K^m`, `a_i ∈ Aff(q)`, the block map with inverse `T⁻¹`; the `t • id` case of
`…_smul_add_affineLifts` is not restated (no consumer needs it yet; it is not a one-line add, as it also needs the one-height bridge to `pencilConfigPoint`).
`lem:pencil-d-contract-magnified-rank` (`Grade/Contract.lean`):
`Graph.finrank_span_rigidityRows_induce_contractHeightGrade_eq`, one unknown vector `x : Fin m → …`
per height, the heights `contractHeight W t (x i)` along the curve and `x i (inl w)` at `(q, z)`;
no kernel hypothesis, no `r ∈ W`. The block helpers `gradeMk`, `gradeHeights` and their lemmas
were lifted to file level in `Grade/Carrier.lean` (scale-shift re-proved on them).
`def:pencil-d-x0-attains` and `lem:pencil-d-x0-attains-three` (`Grade/Carrier.lean`):
`Graph.X0AttainsGrade K m G` (`R : MvPolynomial (α × Fin m) K`, heights in `Graph.liftingSpaceGrade q m`
= `L(q)^m`, an `⨅` of comaps of `L(q)`, with `Graph.mem_liftingSpaceGrade`; target
`screwDim (m + 1) * (|V| − 1) − deficiency (m + 2)`), and `Graph.x0AttainsGrade_one_iff` (named for
`m = 1`; `rename` along `Prod.fst` and `(·, 0)`, the one-height rank lemma rewriting the normals).

## Architectural choices made up front

- **The carrier (the PI's):** `def:pencil-d-realization` is the containment
  model (`HasCoplanarPanelRealization` at grade `k = d − 1`) plus, at each body, a 3-space
  `Π_v ∋ b_v` as data, every hinge at `v` through `Π_v^⊥` (`def:extensor-through-flat`). At
  `k = 2`, `Π_v = q_v^⊥` gives Phase 39's definition; the meet form (Result 13) is its
  adjacent-distinct case (`lem:pencil-d-point-configuration`). Why not the one-line encoding:
  design doc §2.3 CARRIER. **PI, 2026-10-30:** "(a) 3-space as data (Rec.)" (the question and
  the options as put: design doc §1).
- **`Π^⊥` (2026-10-30):** `dotPerp P := LinearMap.BilinForm.orthogonal (dotProductBilin K K) P`
  on `Fin n → K`; `mem_dotPerp` is the chapter's `x ⬝ᵥ y = 0` for all `y ∈ P`. Chosen over
  `Meet.lean`'s `⨅ ker toDual.flip` / `dualAnnihilator.comap` form because `(P^⊥)^⊥ = P` and
  `dim P^⊥ = n − dim P` are then mathlib's `orthogonal_orthogonal` / `finrank_orthogonal`, given the
  mirrored reflexivity and nondegeneracy (`Mathlib/LinearAlgebra/Matrix/BilinearForm.lean`).
- **The configuration, by its number of heights (2026-10-30):** `pencilConfigPointGrade q z w :
  Fin (m + 1 + 2) → K`, `z : α × Fin m → K` uncurried (as pictures and rank-polynomial variables
  are), `m = d − 2`, at grade `k = m + 1`: `vecCons x (vecCons y (Fin.snoc z 1))`. It fits the
  consumers: `GL_m` and `Aff(q)^m` (scale-shift), `m` contracted heights, `MvPolynomial (α × Fin m)`
  (`X0AttainsGrade K m G`), zero heights appended as PD-STABLE's `ι`; no `k − 1`, and `m = 0` is
  the picture point. Simp coordinates: index `i.castSucc.succ.succ`, last `Fin.last (m + 2)`. At
  one height the rank lemma `…_ofNormals_pencilConfigPointGrade_one` bridges `k := 1 + 1` to
  `k := 2`: `rfl` there times out, rewrite the normals first.
- **Grade, not dimension, in Lean:** statements take the grade `k` (`ScrewSpace K k`,
  `Fin (k + 2)`), as KT's chain does, and configurations their `m = k − 1` heights (above); the
  blueprint says `d = k + 1`. The deficiency's `n` stays a
  parameter, as in Phase 39's `HasPencilRealization K n G`, so the `d = 3` agreement holds at
  every `n`; the targets read it at `n = k + 1`.
- **Phase 39's and 40's `P³` declarations stay:** the new layer is additive. Each `P³` node keeps
  its pin; the chapter's `d = 3` agreement lemmas connect the two.

## Lemma checklist

Planned `\lean{...}` names (namespace `CombinatorialRigidity.Molecular` unless `Graph.`); a builder
may refine a name, and the pin lands with the Lean.

- [x] `def:extensor-through-flat` — `ExtensorThroughSubspace`
- [x] `lem:extensor-through-flat-point` — `extensorThroughSubspace_span_singleton_iff`
- [x] `def:pencil-d-realization` — `HasPencilPlaneRealization`, `dotPerp`,
  `exists_hasPencilPlaneRealization_one_iff`
- [x] `lem:pencil-d-agrees-three` — `hasPencilPlaneRealization_two_iff`,
  `exists_hasPencilPlaneRealization_two_iff`
- [x] `lem:pencil-d-point-configuration` — `PanelHingeFramework.toPatchedBodyHinge`,
  `PanelHingeFramework.span_rigidityRows_toPatchedBodyHinge`,
  `PanelHingeFramework.hasPencilPlaneRealization_toPatchedBodyHinge`,
  `HasPencilPlaneRealization.supportExtensor_eq_smul_panelSupportExtensor`,
  `HasPencilPlaneRealization.normal_mem_plane_of_mem_closedNbhd`
- [x] `def:pencil-d-rank-hypothesis` — `HasGradedPencilRealization`
- [x] `def:pencil-d-distinct-motive` — `HasGradedDistinctPencilRealization`
- [x] `lem:pencil-d-rank-agrees-three` — `hasGradedPencilRealization_two_iff`,
  `hasGradedDistinctPencilRealization_two_iff`
- [x] `def:pencil-d-configuration` — `pencilConfigPointGrade`,
  `pencilConfigPointGrade_eq_pencilPicturePoint`, `pencilConfigPointGrade_eq_pencilConfigPoint`,
  `PanelHingeFramework.finrank_span_rigidityRows_ofNormals_pencilConfigPointGrade_one`
- [x] `lem:pencil-d-config-realization` — `Graph.IsAdmissiblePicture.hasGradedDistinctPencilRealization`
  (at grade `m + 1` for `m` heights), `Graph.IsAdmissiblePicture.hasPencilPlaneRealization_ofNormals_pencilConfigPointGrade`
- [x] `def:pencil-d-x0-attains` — `Graph.X0AttainsGrade` (`K m G`, `m` heights), `Graph.liftingSpaceGrade`
- [x] `lem:pencil-d-x0-attains-three` — `Graph.x0AttainsGrade_one_iff` (one height; through
  `…_ofNormals_pencilConfigPointGrade_one`)
- [x] `lem:pencil-d-rank-collineation` — `PanelHingeFramework.finrank_span_rigidityRows_ofNormals_linearEquiv_grade`,
  `panelSupportExtensor_linearEquiv_eq_det_smul`
- [x] `lem:pencil-d-rank-scale-shift` — `Graph.finrank_span_rigidityRows_ofNormals_heights_linearEquiv_add_affineLifts`
- [x] `lem:pencil-d-x0-one-witness` — `Graph.x0AttainsGrade_of_exists`
- [x] `lem:pencil-d-contract-magnified-rank` — `Graph.finrank_span_rigidityRows_induce_contractHeightGrade_eq`
- [ ] `lem:pencil-d-join-independence-open` — `exists_mvPolynomial_linearIndependent_join_picture_grade`,
  `exists_mvPolynomial_linearIndependent_join_heights_grade`
- [x] Lean only (CARRIER): name `bodyBarDim (k + 1) = screwDim k`, inline in
  `screwDim_add_deficiency_le_finrank_infinitesimalMotions` (`PanelLayer.lean`); planned
  `Graph.bodyBarDim_add_one_eq_screwDim`.
- Not here: nondegeneracy's lift (`IsNondegPencilRealization`, the generic conjunct) is GENERIC's
  (design doc §2.3, §4); PD-STABLE's statements are design doc §3, for its own sub-phase.

## Blockers / open questions

- None for 42b. The carrier is settled (the PI, 2026-10-30, *Architectural choices*) and built:
  `def:pencil-d-realization` is green, so the rest of the realization chain is open.

## Hand-off / next phase

The chapter is all green; the next step is the phase-close review (coordinator). Optional, any time: the `k = 2` form
`PanelHingeFramework.finrank_span_rigidityRows_ofNormals_linearEquiv` is the new lemma at
`k := 2` verbatim, so it could be re-proved from it once `Configuration.lean` imports
`Grade/Collineation.lean` (not done: the commits stay additive).

## Decisions made during this phase

- **The point-configuration lemma's framework (2026-10-30):** `HasCoplanarPanelRealization` asks a
  nonzero hinge at every label of `β`, and `ofNormals`'s may vanish off `E(G)`, so part (1) is about
  `P.toPatchedBodyHinge` (any `PanelHingeFramework P`): `P.toBodyHinge`'s hinge on `E(P.graph)`,
  `C(e₀, e₁)` off it, the grade-`k` form of Phase 40's `pencilConfigFramework`; its rows are
  `P.toBodyHinge`'s. The chapter statement gained "nonzero `b_v`" (an isolated body's normal is not
  forced by independence) and the rows sentence; an fmlnote records the patch.

- **The realization (2026-10-30):** `plane` is `Submodule`-valued data, asked about only on `V(G)`
  (as `point` is). The `d = 3` agreement is stated pointwise under `plane v = dotPerp (K ∙ point v)`
  on `V(G)`, with no `point v ≠ 0` (both sides force it: `finrank (q^⊥) = 3 ↔ q ≠ 0`), plus the
  `∃ plane ↔ ∃ point` form `lem:pencil-d-rank-agrees-three` will use; the chapter statement gained
  that sentence. The grade-`1` sanity lemma is pinned on the def beside the `d = 2` remark.

- **The configuration (2026-10-30):** `Pencil/Grade/Carrier.lean`, importing only
  `MainComponent/Carrier.lean`; the encoding is *Architectural choices*. A `lake lean` witness at
  grade 3 (scratch, not retained) checked the point `(x, y, z₀, z₁, 1)`, a concrete `ℚ` point, and
  the collineation lemma at grade `m + 1` on these points with no cast.
- **The collineation leaf (2026-10-30):** a new directory `Pencil/Grade/` for the chapter's Lean,
  importing only `HingeGeneric.lean`. The contragredient is an inline `LinearEquiv`
  (`toDualEquiv ≪≫ₗ g.symm.dualMap ≪≫ₗ toDualEquiv.symm`, `contragredient g` by definition), not
  `exists_contragredient_linearEquiv`, whose pin would add a `lem:pencil-cut-nondegeneracy` edge.
  The `k + 2 - 2` cast closed by `rfl`; the API gaps are FRICTION's open `contragredient` entry.
- **The open (2026-10-30):** the carrier checked against the bodies of `Statement.lean`,
  `Motive.lean`, `HasCoplanarPanelRealization` and `PanelHingeFramework.ofNormals`; findings W1
  and W2 and the options in design doc §2.3 CARRIER. PD-STABLE laid out as a stable code only
  (design doc §3), its `d = 3` embedding covering Result 17's `def[3] = 0` case too.
