# Phase 42b — PD-STATE: the pencil's statement layer in every dimension (work log)

**Status:** in progress, opened 2026-10-30 beside 42a (the PI's planning default, design doc §1,
item 4), the Lean under `/coordinate-phase`. Forward mode: the dep-graph is
`blueprint/src/chapter/pencil-d.tex`, 17 nodes, 4 green (the collineation lemma, the
configuration, the scale-shift, the contraction's rank), Lean in `Pencil/Grade/`. The carrier is the PI's (2026-10-30, design doc §1): the
dual form with each body's 3-space as data, as the chapter states. Next concrete task:
`def:pencil-d-x0-attains` (`Graph.X0AttainsGrade`); the realization chain can interleave.

## Current state

**Next:** `def:pencil-d-x0-attains` (planned `Graph.X0AttainsGrade K m G`, `m` heights); read its
chapter statement first. The realization chain (`def:extensor-through-flat` first) can interleave.

**Landed:** the open (the chapter, its nodes red with planned names; the carrier check, design doc
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

## Architectural choices made up front

- **The carrier (the PI's):** `def:pencil-d-realization` is the containment
  model (`HasCoplanarPanelRealization` at grade `k = d − 1`) plus, at each body, a 3-space
  `Π_v ∋ b_v` as data, every hinge at `v` through `Π_v^⊥` (`def:extensor-through-flat`). At
  `k = 2`, `Π_v = q_v^⊥` gives Phase 39's definition; the meet form (Result 13) is its
  adjacent-distinct case (`lem:pencil-d-point-configuration`). Why not the one-line encoding:
  design doc §2.3 CARRIER. **PI, 2026-10-30:** "(a) 3-space as data (Rec.)" (the question and
  the options as put: design doc §1).
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

- [ ] `def:extensor-through-flat` — `ExtensorThroughSubspace`
- [ ] `lem:extensor-through-flat-point` — `extensorThroughSubspace_span_singleton_iff`
- [ ] `def:pencil-d-realization` — `HasPencilPlaneRealization`
- [ ] `lem:pencil-d-agrees-three` — `hasPencilPlaneRealization_two_iff`
- [ ] `lem:pencil-d-point-configuration` — `PanelHingeFramework.hasPencilPlaneRealization_ofNormals`,
  `HasPencilPlaneRealization.supportExtensor_eq_smul_panelSupportExtensor`
- [ ] `def:pencil-d-rank-hypothesis` — `HasGradedPencilRealization`
- [ ] `def:pencil-d-distinct-motive` — `HasGradedDistinctPencilRealization`
- [ ] `lem:pencil-d-rank-agrees-three` — `hasGradedPencilRealization_two_iff`,
  `hasGradedDistinctPencilRealization_two_iff`
- [x] `def:pencil-d-configuration` — `pencilConfigPointGrade`,
  `pencilConfigPointGrade_eq_pencilPicturePoint`, `pencilConfigPointGrade_eq_pencilConfigPoint`,
  `PanelHingeFramework.finrank_span_rigidityRows_ofNormals_pencilConfigPointGrade_one`
- [ ] `lem:pencil-d-config-realization` — `Graph.IsAdmissiblePicture.hasGradedDistinctPencilRealization`
  (at grade `m + 1` for `m` heights)
- [ ] `def:pencil-d-x0-attains` — `Graph.X0AttainsGrade` (`K m G`, `m` heights) (**next**)
- [ ] `lem:pencil-d-x0-attains-three` — `Graph.x0AttainsGrade_one_iff` (one height; through
  `…_ofNormals_pencilConfigPointGrade_one`)
- [x] `lem:pencil-d-rank-collineation` — `PanelHingeFramework.finrank_span_rigidityRows_ofNormals_linearEquiv_grade`,
  `panelSupportExtensor_linearEquiv_eq_det_smul`
- [x] `lem:pencil-d-rank-scale-shift` — `Graph.finrank_span_rigidityRows_ofNormals_heights_linearEquiv_add_affineLifts`
- [ ] `lem:pencil-d-x0-one-witness` — `Graph.x0AttainsGrade_of_exists`
- [x] `lem:pencil-d-contract-magnified-rank` — `Graph.finrank_span_rigidityRows_induce_contractHeightGrade_eq`
- [ ] `lem:pencil-d-join-independence-open` — `exists_mvPolynomial_linearIndependent_join_picture_grade`,
  `exists_mvPolynomial_linearIndependent_join_heights_grade`
- [ ] Lean only (CARRIER): name `bodyBarDim (k + 1) = screwDim k`, inline in
  `screwDim_add_deficiency_le_finrank_infinitesimalMotions` (`PanelLayer.lean`); planned
  `Graph.bodyBarDim_add_one_eq_screwDim`.
- Not here: nondegeneracy's lift (`IsNondegPencilRealization`, the generic conjunct) is GENERIC's
  (design doc §2.3, §4); PD-STABLE's statements are design doc §3, for its own sub-phase.

## Blockers / open questions

- None for 42b. The carrier is settled (the PI, 2026-10-30, *Architectural choices*), so the
  realization nodes are open to build: `def:extensor-through-flat` is a leaf.

## Hand-off / next phase

The next commit is `def:pencil-d-x0-attains` (*Current state*), with its `\lean` and `\leanok`; the
realization chain (`def:extensor-through-flat` first) can interleave. Optional, any time: the `k = 2` form
`PanelHingeFramework.finrank_span_rigidityRows_ofNormals_linearEquiv` is the new lemma at
`k := 2` verbatim, so it could be re-proved from it once `Configuration.lean` imports
`Grade/Collineation.lean` (not done: the commits stay additive).

## Decisions made during this phase

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
