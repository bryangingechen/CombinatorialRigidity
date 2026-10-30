# Phase 42b — PD-STATE: the pencil's statement layer in every dimension (work log)

**Status:** ✓ closed 2026-10-30 (opened the same day beside 42a, the PI's planning default, design
doc §1, item 4), a sub-phase of Phase 42, which stays in progress with 42a. Forward mode, the Lean
under `/coordinate-phase`: the dep-graph `blueprint/src/chapter/pencil-d.tex` has all 17 nodes
green, the Lean in `Pencil/Grade/` (seven new files) and one lemma in `PanelLayer.lean`, in 15
commits with the open and the close. The carrier is the PI's (2026-10-30, design doc §1): the dual
form with each body's 3-space as data. Next (*Hand-off*): PD-STABLE's open, the PI's to start.

## Current state

**Closed.** The chapter states pencil realizations in dimension `d` (`HasPencilPlaneRealization`,
with `ExtensorThroughSubspace` and `dotPerp`), at the deficiency rank
(`HasGradedPencilRealization`) and adjacent-distinct (`HasGradedDistinctPencilRealization`), each
agreeing with Phase 39's at `d = 3`; the meet form at independent adjacent normals
(`toPatchedBodyHinge`) and configurations over admissible pictures as pencil realizations; and
Phase 40's carrier at every grade: configurations (`pencilConfigPointGrade`), attaining
(`Graph.X0AttainsGrade`, `Graph.liftingSpaceGrade`) with its `d = 3` agreement, the collineation,
the scale-shift, one witness, the magnified rank and join independence. The new layer is additive:
no statement outside `Pencil/Grade/` changed, and the dot product's reflexivity and nondegeneracy
are mirrored (`Mathlib/LinearAlgebra/Matrix/BilinearForm.lean`). The close re-read the chapter end to end (four annotation-order and
tense fixes, no narration to cut; `notes/BlueprintExposition.md` has no 42b entry), groomed the
dispatch log's three 42b rows and compressed the design doc's CARRIER arc. File map, one line each:
- `Grade/Collineation.lean`: the collineation, `det g • Λ_h` with `h` the contragredient.
- `Grade/Carrier.lean`: the configuration and its block helpers `gradeMk` / `gradeHeights`, the
  scale-shift, `L(q)^m` and attaining, and the one-height bridge to `pencilConfigPoint`.
- `Grade/Contract.lean`: the magnified rank.
- `Grade/Realization.lean`: the realization predicates, their `d = 3` agreements,
  `toPatchedBodyHinge` and the grade-general extensor helpers.
- `Grade/Configuration.lean`: a configuration over an admissible picture is a pencil realization.
- `Grade/Witness.lean`: one witness (`map_vecCons_vecCons_snoc`, `supportExtensor_ne_zero_grade`).
- `Grade/JoinIndependence.lean`: join independence, through `exists_mvPolynomial_linearIndependent_normalsJoin`.
- `PanelLayer.lean`: `Graph.bodyBarDim_add_one_eq_screwDim`, the CARRIER item.

## Architectural choices made up front

- **The carrier (the PI's):** `def:pencil-d-realization` is the containment
  model (`HasCoplanarPanelRealization` at grade `k = d − 1`) plus, at each body, a 3-space
  `Π_v ∋ b_v` as data, every hinge at `v` through `Π_v^⊥` (`def:extensor-through-flat`). At
  `k = 2`, `Π_v = q_v^⊥` gives Phase 39's definition; the meet form (Result 13) is its
  adjacent-distinct case (`lem:pencil-d-point-configuration`). Why not the one-line encoding:
  design doc §2.3 CARRIER. **PI, 2026-10-30:** "(a) 3-space as data (Rec.)" (the question and
  the options as put: design doc §1).
- **`Π^⊥`:** `dotPerp P := LinearMap.BilinForm.orthogonal (dotProductBilin K K) P` on `Fin n → K`,
  so `(P^⊥)^⊥ = P` and `dim P^⊥ = n − dim P` are mathlib's `orthogonal_orthogonal` /
  `finrank_orthogonal`, given the mirrored reflexivity and nondegeneracy
  (`Mathlib/LinearAlgebra/Matrix/BilinearForm.lean`); not `Meet.lean`'s annihilator form.
- **The configuration, by its number of heights:** `pencilConfigPointGrade q z w :
  Fin (m + 1 + 2) → K`, `z : α × Fin m → K` uncurried, `m = d − 2`, at grade `k = m + 1`:
  `vecCons x (vecCons y (Fin.snoc z 1))`. It fits `GL_m` and `Aff(q)^m`, `m` contracted heights,
  `MvPolynomial (α × Fin m)`, and PD-STABLE's `ι` (zero heights appended); `m = 0` is the picture
  point. At one height, rewrite with `…_ofNormals_pencilConfigPointGrade_one` (`rfl` times out;
  FRICTION's configuration-points idiom).
- **Grade, not dimension, in Lean:** statements take the grade `k` (`ScrewSpace K k`,
  `Fin (k + 2)`), as KT's chain does, and configurations their `m = k − 1` heights; the
  blueprint says `d = k + 1`. The deficiency's `n` stays a parameter, as in Phase 39's
  `HasPencilRealization K n G`, so the `d = 3` agreement holds at every `n`; targets read it at
  `n = k + 1`.
- **Phase 39's and 40's `P³` declarations stay:** the layer is additive, and the chapter's
  `d = 3` agreement lemmas connect the two.

## Lemma checklist

Pins as landed (namespace `CombinatorialRigidity.Molecular` unless `Graph.`); the chapter's
`\lean{...}` lists are the full record.

- [x] `def:extensor-through-flat` — `ExtensorThroughSubspace`
- [x] `lem:extensor-through-flat-point` — `extensorThroughSubspace_span_singleton_iff`
- [x] `def:pencil-d-realization` — `HasPencilPlaneRealization`, `dotPerp`,
  `exists_hasPencilPlaneRealization_one_iff`
- [x] `lem:pencil-d-agrees-three` — `hasPencilPlaneRealization_two_iff`,
  `exists_hasPencilPlaneRealization_two_iff`
- [x] `lem:pencil-d-point-configuration` — `PanelHingeFramework.toPatchedBodyHinge`,
  `PanelHingeFramework.hasPencilPlaneRealization_toPatchedBodyHinge`,
  `HasPencilPlaneRealization.supportExtensor_eq_smul_panelSupportExtensor`, and two more
- [x] `def:pencil-d-rank-hypothesis` — `HasGradedPencilRealization`
- [x] `def:pencil-d-distinct-motive` — `HasGradedDistinctPencilRealization`
- [x] `lem:pencil-d-rank-agrees-three` — `hasGradedPencilRealization_two_iff`,
  `hasGradedDistinctPencilRealization_two_iff`
- [x] `def:pencil-d-configuration` — `pencilConfigPointGrade` and its two agreements
- [x] `lem:pencil-d-config-realization` — `Graph.IsAdmissiblePicture.hasGradedDistinctPencilRealization`
  (at grade `m + 1` for `m` heights), `Graph.IsAdmissiblePicture.hasPencilPlaneRealization_ofNormals_pencilConfigPointGrade`
- [x] `def:pencil-d-x0-attains` — `Graph.X0AttainsGrade` (`K m G`, `m` heights), `Graph.liftingSpaceGrade`
- [x] `lem:pencil-d-x0-attains-three` — `Graph.x0AttainsGrade_one_iff`
- [x] `lem:pencil-d-rank-collineation` — `PanelHingeFramework.finrank_span_rigidityRows_ofNormals_linearEquiv_grade`,
  `panelSupportExtensor_linearEquiv_eq_det_smul`
- [x] `lem:pencil-d-rank-scale-shift` — `Graph.finrank_span_rigidityRows_ofNormals_heights_linearEquiv_add_affineLifts`
- [x] `lem:pencil-d-x0-one-witness` — `Graph.x0AttainsGrade_of_exists`
- [x] `lem:pencil-d-contract-magnified-rank` — `Graph.finrank_span_rigidityRows_induce_contractHeightGrade_eq`
- [x] `lem:pencil-d-join-independence-open` — `exists_mvPolynomial_linearIndependent_join_picture_grade`,
  `exists_mvPolynomial_linearIndependent_join_heights_grade`
- [x] Lean only (CARRIER): `Graph.bodyBarDim_add_one_eq_screwDim` (`PanelLayer.lean`), the inline
  use in `screwDim_add_deficiency_le_finrank_infinitesimalMotions` repointed to it.
- Not here: nondegeneracy's lift (`IsNondegPencilRealization`, the generic conjunct) is GENERIC's
  (design doc §2.3, §4); PD-STABLE's statements are design doc §3.

## Blockers / open questions

- None. 42b's successor opens at the PI's word (*Hand-off*).

## Hand-off / next phase

**PD-STABLE** (design doc §3) states over this layer's definitions, which have landed, so it can
open now; the coordinator puts the open to the PI. It needs PD-STATE and Phase 40, not the recon:
Results 15–17 formally, the embedding at every `d′ ≤ d`, the deficiency lemma, and `Pᵈ` at
`def_3 ≤ 1` (Tier 0). Its open mints the next letter, its work log and its blueprint nodes, red;
the smallest first build is probably the deficiency lemma (item 2, combinatorial, beside
`lem:deficiency-antitone`), but the open's own red-node read decides. Read the definition bodies
in `Pencil/Grade/` before pinning: this layer's planned pins were refuted once by a consumer's body
(`toPatchedBodyHinge`, *Decisions*).

**Deferred from 42b, where they land:** FRICTION's open `normalsJoin` map lemma with PD-STABLE's
embedding (design doc §3, after item 3); the `k = 2` collineation and scale-shift re-proved from
the grade lemmas, the grade scale-shift's `t • id` case and the hinge form of join independence
with PD-CARRIER / PD-STEPS, each when a consumer needs it (design doc §3). FRICTION also carries
the `contragredient` equivalence (open) and the grade-general extensor helpers' homes in
`Meet.lean` and `PanelLayer.lean` (mirror-candidate).

## Decisions made during this phase

- **Point-configuration framework:** part (1) is on `P.toPatchedBodyHinge` (`C(e₀, e₁)` off
  `E(G)`), not `ofNormals`, whose hinges may vanish where `HasCoplanarPanelRealization` asks them
  nonzero; the open's planned pin was false. The statement gained "nonzero `b_v`".
- **Realization:** `plane` is `Submodule`-valued data on `V(G)`; the `d = 3` agreement is pointwise
  under `plane v = dotPerp (K ∙ point v)`, plus the `∃ plane ↔ ∃ point` form.
- **Adjacent-distinct:** independent normals at every link; at `d = 3` the polarity, once per
  direction, matches Phase 39's independent points.
- **Configuration:** `Grade/Carrier.lean`, importing only `MainComponent/Carrier.lean`
  (*Architectural choices*).
- **Collineation:** the contragredient an inline `LinearEquiv`, not
  `exists_contragredient_linearEquiv`, whose pin would add a `lem:pencil-cut-nondegeneracy` edge.
- **Scale-shift:** `T ∈ GL_m`, `a_i ∈ Aff(q)`; the `t • id` case not restated (*Hand-off*).
- **The open:** the carrier checked against the definition bodies (design doc §2.3 CARRIER, W1
  and W2); PD-STABLE laid out as a stable code (design doc §3).
