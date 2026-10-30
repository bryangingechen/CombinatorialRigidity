# Phase 42b — PD-STATE: the pencil's statement layer in every dimension (work log)

**Status:** in progress, opened 2026-10-30 beside 42a (the PI's planning default, design doc §1,
item 4), the Lean under `/coordinate-phase`. Forward mode: the dep-graph is
`blueprint/src/chapter/pencil-d.tex`, 17 nodes, all red, no Lean yet. The carrier check at the
open (design doc §2.3 CARRIER) found the PI's dual form right once each body's 3-space is data,
and wrong as a one-line encoding; that reading is put to the PI for confirmation and does not
block the first leaf. Next concrete task: `lem:pencil-d-rank-collineation`, the collineation
lemma at every grade.

## Current state

**Next:** `lem:pencil-d-rank-collineation`, a leaf (its `\uses` all green): the panel-hinge
rank at normals `b` and `g ∘ b` agree, `g ∈ GL(K^{k+2})`, every `k`. Route: `panelSupportExtensor
(g n₁) (g n₂) = complementIso (map 2 g (n₁ ∧ n₂)) = det g • map k (contragredient g) (…)`
(`complementIso_map_contragredient_eq`, `Molecular/Meet.lean`, `k`-general), so one automorphism
of `ScrewSpace K k` maps every hinge, and `finrank_span_rigidityRows_mapExtensor` keeps the rank.
The `k = 2` form, `PanelHingeFramework.finrank_span_rigidityRows_ofNormals_linearEquiv`
(`MainComponent/Configuration.lean`), goes through `pointJoinFramework` and stays.

**Landed (the open):** the chapter, its nodes red with planned names (*Lemma checklist*); the
carrier check (design doc §2.3), witnessed in `lake lean` (scratch, not retained); PD-STABLE's
exact statements (design doc §3). No Lean.

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
- [ ] `def:pencil-d-configuration` — `pencilConfigPointGrade`
- [ ] `lem:pencil-d-config-realization` — `Graph.IsAdmissiblePicture.hasGradedDistinctPencilRealization`
- [ ] `def:pencil-d-x0-attains` — `Graph.X0AttainsGrade`
- [ ] `lem:pencil-d-x0-attains-three` — `Graph.x0AttainsGrade_two_iff`
- [ ] `lem:pencil-d-rank-collineation` — `PanelHingeFramework.finrank_span_rigidityRows_ofNormals_linearEquiv_grade` (**next**)
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

The next commit is `lem:pencil-d-rank-collineation` at every grade (*Current state*), with its
`\lean` and `\leanok` in the chapter. Then `lem:pencil-d-rank-scale-shift` and
`lem:pencil-d-contract-magnified-rank` follow from it once `def:pencil-d-configuration` lands;
the realization nodes wait for the PI's confirmation of the carrier.

## Decisions made during this phase

- **The open (2026-10-30):** the carrier checked against the bodies of `Statement.lean`,
  `Motive.lean`, `HasCoplanarPanelRealization` and `PanelHingeFramework.ofNormals`; findings W1
  and W2 and the options in design doc §2.3 CARRIER. PD-STABLE laid out as a stable code only
  (design doc §3), its `d = 3` embedding covering Result 17's `def[3] = 0` case too.
