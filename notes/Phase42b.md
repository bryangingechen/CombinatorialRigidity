# Phase 42b — PD-STATE: the pencil's statement layer in every dimension (work log)

**Status:** in progress, opened 2026-10-30 beside 42a (the PI's planning default, design doc §1,
item 4), the Lean under `/coordinate-phase`. Forward mode: the dep-graph is
`blueprint/src/chapter/pencil-d.tex`, 17 nodes, 1 green (the collineation lemma), Lean in
`Pencil/Grade/`. The carrier check at the open (design doc §2.3 CARRIER) found the PI's dual form
right once each body's 3-space is data, and wrong as a one-line encoding; that reading is put to
the PI for confirmation and does not block the configuration nodes. Next concrete task:
`def:pencil-d-configuration`, the configuration's points at every grade.

## Current state

**Next:** `def:pencil-d-configuration` (`pencilConfigPointGrade`), a leaf (its `\uses` all
green): the points `b_v = (x_v, y_v, z^1_v, …, z^{k-1}_v, 1) ∈ K^{k+2}` of a picture `q` and `k − 1`
heights (`d − 2 = k − 1`), whose `k = 2` form is `pencilConfigPoint` (`MainComponent/Carrier.lean`).
Its rank is `ofNormals` at those points, as at `k = 2`. A new file beside `Grade/Collineation.lean`.

**Landed:** the open (the chapter, its nodes red with planned names; the carrier check, design doc
§2.3; PD-STABLE's statements, design doc §3). `lem:pencil-d-rank-collineation`
(`Pencil/Grade/Collineation.lean`): one automorphism `det g • Λ_h` of `ScrewSpace K k`, `h` the
contragredient, maps every hinge (`panelSupportExtensor_linearEquiv_eq_det_smul`).

## Architectural choices made up front

- **The carrier (pending the PI's confirmation):** `def:pencil-d-realization` is the containment
  model (`HasCoplanarPanelRealization` at grade `k = d − 1`) plus, at each body, a 3-space
  `Π_v ∋ b_v` as data, every hinge at `v` through `Π_v^⊥` (`def:extensor-through-flat`). At
  `k = 2`, `Π_v = q_v^⊥` gives Phase 39's definition; the meet form (Result 13) is its
  adjacent-distinct case (`lem:pencil-d-point-configuration`). Why not the one-line encoding, and
  the options with estimates: design doc §2.3 CARRIER.
- **Grade, not dimension, in Lean:** statements take the grade `k` (`ScrewSpace K k`,
  `Fin (k + 2)`), as KT's chain does; the blueprint says `d = k + 1`. The deficiency's `n` stays a
  parameter, as in Phase 39's `HasPencilRealization K n G`, so the `d = 3` agreement holds at
  every `n`; the targets read it at `n = k + 1`.
- **Phase 39's and 40's `P³` declarations stay:** the new layer is additive. Each `P³` node keeps
  its pin; the chapter's `d = 3` agreement lemmas connect the two.

## Lemma checklist

Planned `\lean{...}` names (namespace `CombinatorialRigidity.Molecular` unless `Graph.`); a builder
may refine a name, and the pin lands with the Lean.

- [ ] `def:extensor-through-flat` — `ExtensorThroughSubspace`
- [ ] `lem:extensor-through-flat-point` — `extensorThroughSubspace_span_singleton_iff`
- [ ] `def:pencil-d-realization` — `HasPencilPlaneRealization` (awaits the PI's confirmation)
- [ ] `lem:pencil-d-agrees-three` — `hasPencilPlaneRealization_two_iff`
- [ ] `lem:pencil-d-point-configuration` — `PanelHingeFramework.hasPencilPlaneRealization_ofNormals`,
  `HasPencilPlaneRealization.supportExtensor_eq_smul_panelSupportExtensor`
- [ ] `def:pencil-d-rank-hypothesis` — `HasGradedPencilRealization`
- [ ] `def:pencil-d-distinct-motive` — `HasGradedDistinctPencilRealization`
- [ ] `lem:pencil-d-rank-agrees-three` — `hasGradedPencilRealization_two_iff`,
  `hasGradedDistinctPencilRealization_two_iff`
- [ ] `def:pencil-d-configuration` — `pencilConfigPointGrade` (**next**)
- [ ] `lem:pencil-d-config-realization` — `Graph.IsAdmissiblePicture.hasGradedDistinctPencilRealization`
- [ ] `def:pencil-d-x0-attains` — `Graph.X0AttainsGrade`
- [ ] `lem:pencil-d-x0-attains-three` — `Graph.x0AttainsGrade_two_iff`
- [x] `lem:pencil-d-rank-collineation` — `PanelHingeFramework.finrank_span_rigidityRows_ofNormals_linearEquiv_grade`,
  `panelSupportExtensor_linearEquiv_eq_det_smul`
- [ ] `lem:pencil-d-rank-scale-shift` — `Graph.finrank_span_rigidityRows_ofNormals_heights_linearEquiv_add_affineLifts`
- [ ] `lem:pencil-d-x0-one-witness` — `Graph.x0AttainsGrade_of_exists`
- [ ] `lem:pencil-d-contract-magnified-rank` — `Graph.finrank_span_rigidityRows_induce_contractHeightGrade_eq`
- [ ] `lem:pencil-d-join-independence-open` — `exists_mvPolynomial_linearIndependent_join_picture_grade`,
  `exists_mvPolynomial_linearIndependent_join_heights_grade`
- [ ] Lean only (CARRIER): name `bodyBarDim (k + 1) = screwDim k`, inline in
  `screwDim_add_deficiency_le_finrank_infinitesimalMotions` (`PanelLayer.lean`); planned
  `Graph.bodyBarDim_add_one_eq_screwDim`.
- Not here: nondegeneracy's lift (`IsNondegPencilRealization`, the generic conjunct) is GENERIC's
  (design doc §2.3, §4); PD-STABLE's statements are design doc §3, for its own sub-phase.

## Blockers / open questions

- **For the PI (not blocking):** confirm the carrier's reading, design doc §2.3 CARRIER options
  (a)–(d); (a) is recommended and is what `def:pencil-d-realization` states. The configuration
  nodes, the collineation leaf first, are the same under each.

## Hand-off / next phase

The next commit is `def:pencil-d-configuration` (*Current state*), with its `\lean` and `\leanok`
in the chapter. Then `lem:pencil-d-rank-scale-shift` (the collineation lemma at the map
`(ξ, η, ζ, ω) ↦ (ξ, η, Tζ + ξα + ηβ + ωγ, ω)`, as
`Graph.finrank_span_rigidityRows_ofNormals_smul_add_affineLifts` does at `k = 2`) and
`lem:pencil-d-contract-magnified-rank`; the realization nodes wait for the PI's confirmation of the
carrier. Optional, any time: the `k = 2` form
`PanelHingeFramework.finrank_span_rigidityRows_ofNormals_linearEquiv` is the new lemma at
`k := 2` verbatim, so it could be re-proved from it once `Configuration.lean` imports
`Grade/Collineation.lean` (not done: the commit stays additive).

## Decisions made during this phase

- **The collineation leaf (2026-10-30):** a new directory `Pencil/Grade/` for the chapter's Lean,
  importing only `HingeGeneric.lean`. The contragredient is an inline `LinearEquiv`
  (`toDualEquiv ≪≫ₗ g.symm.dualMap ≪≫ₗ toDualEquiv.symm`, `contragredient g` by definition), not
  `exists_contragredient_linearEquiv`, whose pin would add a `lem:pencil-cut-nondegeneracy` edge.
  The `k + 2 - 2` cast closed by `rfl`; the API gaps are FRICTION's open `contragredient` entry.
- **The open (2026-10-30):** the carrier checked against the bodies of `Statement.lean`,
  `Motive.lean`, `HasCoplanarPanelRealization` and `PanelHingeFramework.ofNormals`; findings W1
  and W2 and the options in design doc §2.3 CARRIER. PD-STABLE laid out as a stable code only
  (design doc §3), its `d = 3` embedding covering Result 17's `def[3] = 0` case too.
