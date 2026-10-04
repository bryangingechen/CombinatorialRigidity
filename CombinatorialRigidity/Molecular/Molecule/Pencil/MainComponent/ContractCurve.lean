/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.Cut

/-!
# The rescaled lifting system and the contraction curve (Phase 40f CONTRACT-R / 40k CONTRACT-A)

The rescaled lifting system `M(t)` of the contraction at a core, the curve `q(t)` it moves along,
and the facts at the two ends of the curve that the contraction steps of the `X₀` induction share
(`blueprint/src/chapter/main-component.tex`, `sec:main-component-contract`; Phase 40f
CONTRACT-R and Phase 40k CONTRACT-A,
`notes/Phase40f.md`, `notes/Phase40k.md`). Split out of `Contract.lean` at the Phase 40k
`Contract.lean` split (`notes/Phase40k.md`, call 5): the flat-core assembly
(`Graph.exists_core_plane`, `Graph.finrank_ker_contractLiftingMatrix_zero_le`,
`Graph.finrank_span_rigidityRows_induce_contractHeight`,
`Graph.isX0Graph_induce_of_deficiency_two_eq_zero`) and **CONTRACT-R**
(`Graph.X0Attains.of_rigidContract`) stay in `Contract.lean`; every other declaration moves here
unchanged, except `Graph.contractLimitMap_mem_liftingSpace` and
`Graph.eq_zero_of_contractLimitMap_eq_zero`, generalized in place to take one plane on the core as
a hypothesis (in place of `hqH`/`hLH`) so a later step can supply it from a magnified picture
instead of `Graph.exists_core_plane`; no declaration is renamed or re-stated otherwise, so no
blueprint `\lean{...}` pin moves.

CONTRACT-A's own general pieces land here too (Phase 40k B2): the core's rank along the curve at
any `t ≠ 0` (no flatness needed, by a collineation of `Configuration.lean`), the kernel of `M(0)`
at any core, and the standing hypotheses at a rigid core, at any `n`.

## Main definitions

* `Graph.coreNbhd` — the bodies whose closed neighbourhood meets the core.
* `Graph.contractWeightAt`, `Graph.contractWeight` — the weight point of the rescaled system at
  `t`, and as polynomials in `t`.
* `Graph.contractLiftingMatrix` — the rescaled lifting system `M(t)`, the lifting system with
  weights `Graph.weightedLiftingMatrix` (`Carrier.lean`) at `Graph.contractWeight`.
* `contractPicture` — the contraction curve `q(t)`; `contractHeight` — the heights `z(t)` of a
  solution of `M(t)`, the core heights scaled by `t`.
* `contractLimitMap` — the map from `ker M(0)` to heights of `G/H`.
* `contractCoreRestrict` — the restriction of the unknowns of `M(t)` to the core heights.
* `contractPicturePoly`, `contractConfigPoly` — the curve and its configuration as polynomials in
  `t`.

## Main statements

* `Graph.contractHeight_mem_liftingSpace`, `Graph.exists_contractHeight_eq`,
  `Graph.finrank_liftingSpace_le_finrank_ker_contractLiftingMatrix` — along the curve the heights
  of a solution of `M(t)` lie in `L_G(q(t))`, onto at `t ≠ 0`
  (`lem:pencil-contract-lifting-kernel`).
* `Graph.finrank_span_rigidityRows_induce_contractHeight_eq` — at `t ≠ 0` the core's rank at
  `(q(t), z(t))` equals its rank at the fixed picture `(q, z)`, by a collineation
  (`lem:pencil-contract-magnified-rank`).
* `Graph.contractLimitMap_mem_liftingSpace`, `Graph.eq_zero_of_contractLimitMap_eq_zero` — given
  one plane on the core, the limit map sends `ker M(0)` into `L_{G/H}(q)` and is injective there
  (the embedding in the proof of `lem:pencil-contract-kernel-bound` (2)).
* `Graph.exists_mem_ker_contractLiftingMatrix_zero` — at any core, a height of `G/H` vanishing at
  `r` agrees off the core with the heights of a solution of `M(0)`, the core put on the height's
  plane at `r` (`lem:pencil-contract-limit`; (MC-37) step 2).
* `Graph.liftingRestrict_mem_liftingSpace_induce_of_contract`,
  `Graph.finrank_ker_contractLiftingMatrix_zero_add_three_le` — at any core, `ρ` maps `ker M(t)`
  into `L_H(q)` at every `t`, and `dim ker M(0) + 3 ≤ dim ρ(ker M(0)) + dim L_{G/H}(q)`
  (`lem:pencil-contract-kernel-bound`'s two parts).
* `PanelHingeFramework.exists_rankPolynomial_rigidContract_induce_proj` — a polynomial nonzero at
  the collapsed placement bounds below the surviving rows with the core columns deleted
  (`lem:pencil-contract-degenerate-rank`; KT eqs. (6.5)/(6.9)).
* `Graph.isX0Graph_induce_of_deficiency_eq_zero` — a rigid core satisfies the standing hypotheses,
  at any `n` with `bodyBarDim n ≥ 1` (`lem:pencil-contract-standing-rigid`).
* `Graph.rigidContract_induce_simple`, `Graph.isX0Graph_rigidContract_induce`,
  `Graph.three_le_ncard_closedNbhd_rigidContract`, `Graph.connected_rigidContract_induce` —
  `G/H` satisfies the standing hypotheses (`lem:pencil-contract-standing`, (MC-39)'s side claims).

The general pieces sit beside their definitions: `Graph.weightedLiftingMatrix` (`Carrier.lean`),
`PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking_set_proj_eval` (`CaseI.lean`) and the
collineation lemma `PanelHingeFramework.finrank_span_rigidityRows_ofNormals_linearEquiv`
(`Configuration.lean`, `lem:pencil-rank-collineation`).

## Design

* **`hatt` is the simplicity hypothesis as spiked**: no body outside `W` is adjacent to two core
  bodies. Restating it as `(G/H).Simple` (the converse of `Graph.rigidContract_induce_simple`) is a
  tracked readability item (`notes/Phase40-design.md` §3 STEPS; PI decision 2, 2026-09-26).
* **A defeq trap.** A `panelRow` lemma against a framework over `G.rigidContract (G.induce W) r`
  times out at `isDefEq` unless `rigidContract` is first rewritten to
  `(G.deleteEdges E(G.induce W)).map (collapseTo r W)` and `V(G.induce W)` to `W`, both by `rfl`
  (`PanelHingeFramework.exists_rankPolynomial_rigidContract_induce_proj`).

See `notes/Phase40f.md`, `notes/Phase40k.md` and `notes/Phase40-design.md` §3 STEPS.
-/

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {k : ℕ} {K : Type*} [Field K] {α β : Type*}

/-! ## The rescaled lifting system -/

/-- **The bodies meeting the core** (`def:pencil-contract-lifting-system`): the bodies `v` whose
closed neighbourhood in `G` meets `W` — the core itself and its attachments. At these rows the
rescaled lifting system reads the bodies outside the core in the magnified frame. -/
def _root_.Graph.coreNbhd (G : Graph α β) (W : Set α) : Set α :=
  {v | ∃ c ∈ W, c ∈ G.closedNbhd v}

open Classical in
/-- **The weight point of the rescaled lifting system at `t`**
(`def:pencil-contract-lifting-system`): at a row `(v, w)` with `v` meeting the core and `w`
outside it, the outside point seen from the magnified frame,
`(x_w − (1 − t) x_r, y_w − (1 − t) y_r, t)`; everywhere else the homogeneous picture point
`(x_w, y_w, 1)`. -/
noncomputable def _root_.Graph.contractWeightAt (G : Graph α β) (W : Set α) (r : α)
    (q : α × Fin 2 → K) (t : K) (v w : α) : Fin 3 → K :=
  if v ∈ G.coreNbhd W ∧ w ∉ W then
    ![q (w, 0) - (1 - t) * q (r, 0), q (w, 1) - (1 - t) * q (r, 1), t]
  else pencilPicturePoint q w

open Classical in
/-- **The weight point as polynomials in `t`**: `Graph.contractWeightAt` with `t` the variable
(`Graph.eval_contractWeight`), the weights of `Graph.contractLiftingMatrix`. -/
noncomputable def _root_.Graph.contractWeight (G : Graph α β) (W : Set α) (r : α)
    (q : α × Fin 2 → K) (v w : α) : Fin 3 → MvPolynomial Unit K :=
  if v ∈ G.coreNbhd W ∧ w ∉ W then
    ![MvPolynomial.C (q (w, 0) - q (r, 0)) + MvPolynomial.X () * MvPolynomial.C (q (r, 0)),
      MvPolynomial.C (q (w, 1) - q (r, 1)) + MvPolynomial.X () * MvPolynomial.C (q (r, 1)),
      MvPolynomial.X ()]
  else ![MvPolynomial.C (q (w, 0)), MvPolynomial.C (q (w, 1)), 1]

/-- Evaluating the polynomial weight point at `t` gives `Graph.contractWeightAt` at `t`. -/
theorem _root_.Graph.eval_contractWeight (G : Graph α β) (W : Set α) (r : α)
    (q : α × Fin 2 → K) (t : K) (v w : α) :
    (fun i => MvPolynomial.eval (fun _ => t) (G.contractWeight W r q v w i)) =
      G.contractWeightAt W r q t v w := by
  funext i
  unfold Graph.contractWeight Graph.contractWeightAt
  split_ifs <;> fin_cases i <;> simp [pencilPicturePoint] <;> ring

/-- **The rescaled lifting system** `M(t)` of the contraction at the core `W`, collapsing at `r`'s
picture point (`def:pencil-contract-lifting-system`; Phase 40f CONTRACT-R): the lifting system with
weights (`Graph.weightedLiftingMatrix`) at the polynomial weight point `Graph.contractWeight`, a
matrix of polynomials in the curve's one parameter `t`. -/
noncomputable def _root_.Graph.contractLiftingMatrix (K : Type*) [Field K] (G : Graph α β)
    (W : Set α) (r : α) (q : α × Fin 2 → K) :
    Matrix (α ⊕ (α × α) ⊕ (α × Fin 3)) (α ⊕ (α × Fin 3)) (MvPolynomial Unit K) :=
  G.weightedLiftingMatrix K (G.contractWeight W r q)

/-- **The kernel of `M(t)`**: `x = (z, h)` solves `M(t)` exactly when `z` and `h` vanish off `V(G)`
and `z_w = h_v ⬝ Graph.contractWeightAt W r q t v w` on every closed neighbourhood of a body `v`. -/
theorem _root_.Graph.contractLiftingMatrix_mulVec_eq_zero_iff [Fintype α] {G : Graph α β}
    {W : Set α} {r : α} {q : α × Fin 2 → K} {t : K} {x : α ⊕ (α × Fin 3) → K} :
    (G.contractLiftingMatrix K W r q).map (MvPolynomial.eval (fun _ => t)) *ᵥ x = 0 ↔
      (∀ w ∉ V(G), x (Sum.inl w) = 0) ∧
      (∀ v ∈ V(G), ∀ w ∈ G.closedNbhd v,
        x (Sum.inl w) = (fun i => x (Sum.inr (v, i))) ⬝ᵥ G.contractWeightAt W r q t v w)
      ∧ ∀ v ∉ V(G), ∀ i, x (Sum.inr (v, i)) = 0 := by
  rw [Graph.contractLiftingMatrix, Graph.weightedLiftingMatrix_mulVec_eq_zero_iff]
  simp only [Graph.eval_contractWeight]

/-- At a core body `w ∈ W` the weight is the homogeneous picture point, at every `t`. -/
theorem _root_.Graph.contractWeightAt_of_mem {G : Graph α β} {W : Set α} {r : α}
    {q : α × Fin 2 → K} {t : K} {v w : α} (hw : w ∈ W) :
    G.contractWeightAt W r q t v w = pencilPicturePoint q w := by
  simp [Graph.contractWeightAt, hw]

/-- At a row `(v, w)` with `v` not meeting the core the weight is the homogeneous picture point. -/
theorem _root_.Graph.contractWeightAt_of_not_mem_coreNbhd {G : Graph α β} {W : Set α} {r : α}
    {q : α × Fin 2 → K} {t : K} {v w : α} (hv : v ∉ G.coreNbhd W) :
    G.contractWeightAt W r q t v w = pencilPicturePoint q w := by
  simp [Graph.contractWeightAt, hv]

/-- At a row `(v, w)` with `v` meeting the core and `w ∉ W` the weight is the magnified-frame point
`(x_w − (1 − t) x_r, y_w − (1 − t) y_r, t)`. -/
theorem _root_.Graph.contractWeightAt_of_mem_coreNbhd {G : Graph α β} {W : Set α} {r : α}
    {q : α × Fin 2 → K} {t : K} {v w : α} (hv : v ∈ G.coreNbhd W) (hw : w ∉ W) :
    G.contractWeightAt W r q t v w =
      ![q (w, 0) - (1 - t) * q (r, 0), q (w, 1) - (1 - t) * q (r, 1), t] := by
  simp [Graph.contractWeightAt, hv, hw]

/-! ## The contraction curve -/

open Classical in
/-- **The contraction curve** `q(t)` (`def:pencil-contract-lifting-system`): each core body
`c ∈ W` at `(1 − t) q_r + t q_c`, every other body at `q`. So `q(1) = q` (`contractPicture_one`),
and `q(0)` puts the whole core at `q_r`. -/
noncomputable def contractPicture (W : Set α) (r : α) (q : α × Fin 2 → K) (t : K) :
    α × Fin 2 → K :=
  fun p => if p.1 ∈ W then (1 - t) * q (r, p.2) + t * q p else q p

/-- At `t = 1` the contraction curve is the picture `q`. -/
theorem contractPicture_one (W : Set α) (r : α) (q : α × Fin 2 → K) :
    contractPicture W r q 1 = q := by
  funext p
  simp [contractPicture]

open Classical in
/-- **The heights of a solution of `M(t)`** (`def:pencil-contract-lifting-system`): the core
heights scaled by `t` (`z(t)_w = t z_w` for `w ∈ W`, `z_w` elsewhere), as a linear map on the
unknowns `(z, h)` of `M(t)`. -/
noncomputable def contractHeight (W : Set α) (t : K) :
    (α ⊕ (α × Fin 3) → K) →ₗ[K] (α → K) where
  toFun x w := if w ∈ W then t * x (Sum.inl w) else x (Sum.inl w)
  map_add' x y := by funext w; by_cases hw : w ∈ W <;> simp [hw]; ring
  map_smul' c x := by funext w; by_cases hw : w ∈ W <;> simp [hw]; ring

open Classical in
/-- Unfolding `contractHeight`. -/
theorem contractHeight_apply (W : Set α) (t : K) (x : α ⊕ (α × Fin 3) → K) (w : α) :
    contractHeight W t x w = if w ∈ W then t * x (Sum.inl w) else x (Sum.inl w) := rfl

/-- Off the core the curve does not move the homogeneous picture point. -/
theorem pencilPicturePoint_contractPicture_of_not_mem {W : Set α} {r : α} {q : α × Fin 2 → K}
    {t : K} {w : α} (hw : w ∉ W) :
    pencilPicturePoint (contractPicture W r q t) w = pencilPicturePoint q w := by
  funext i
  fin_cases i <;> simp [pencilPicturePoint, contractPicture, hw]

/-! ## The rescaled system off the end of the curve -/

/-- **The heights of a solution lie in the lifting space along the curve**
(`lem:pencil-contract-lifting-kernel`, first half; (K1)): at every `t`, the heights `z(t)` of a
solution of `M(t)` lie in `L_G(q(t))`. At a body meeting the core the affine coefficients are
`(h₀, h₁, t h₂ − (1 − t)(h₀ x_r + h₁ y_r))`; at the other bodies they are `h_v`. -/
theorem _root_.Graph.contractHeight_mem_liftingSpace [Fintype α] {G : Graph α β} {W : Set α}
    {r : α} {q : α × Fin 2 → K} {t : K} {x : α ⊕ (α × Fin 3) → K}
    (hx : (G.contractLiftingMatrix K W r q).map (MvPolynomial.eval (fun _ => t)) *ᵥ x = 0) :
    contractHeight W t x ∈ G.liftingSpace (contractPicture W r q t) := by
  obtain ⟨h1, h2, -⟩ := Graph.contractLiftingMatrix_mulVec_eq_zero_iff.mp hx
  refine ⟨fun w hw => ?_, fun v hv => ?_⟩
  · rw [contractHeight_apply, h1 w hw]
    simp
  · by_cases hc : v ∈ G.coreNbhd W
    · refine ⟨![x (Sum.inr (v, 0)), x (Sum.inr (v, 1)),
        t * x (Sum.inr (v, 2)) - (1 - t) * (x (Sum.inr (v, 0)) * q (r, 0) +
          x (Sum.inr (v, 1)) * q (r, 1))], fun w hw => ?_⟩
      have h := h2 v hv w hw
      rw [contractHeight_apply]
      by_cases hwW : w ∈ W
      · rw [ite_eq_left hwW, h]
        simp only [Graph.contractWeightAt, hc, hwW, not_true_eq_false, and_false, ite_false,
          pencilPicturePoint, contractPicture, ite_true, dotProduct, Fin.sum_univ_three]
        simp
        ring
      · rw [ite_eq_right hwW, h]
        simp only [Graph.contractWeightAt, hc, hwW, not_false_eq_true, and_self, ite_true,
          pencilPicturePoint, contractPicture, ite_false, dotProduct, Fin.sum_univ_three]
        simp
        ring
    · refine ⟨fun i => x (Sum.inr (v, i)), fun w hw => ?_⟩
      have hwW : w ∉ W := fun hwW => hc ⟨w, hwW, hw⟩
      have h := h2 v hv w hw
      simp only [Graph.contractWeightAt, hc, false_and, ite_false] at h
      rw [contractHeight_apply, ite_eq_right hwW, h]
      congr 1
      funext i
      fin_cases i <;> simp [contractPicture, hwW, pencilPicturePoint]

/-- **At `t ≠ 0` every height along the curve comes from a solution**
(`lem:pencil-contract-lifting-kernel`, second half; (K2)): every `z ∈ L_G(q(t))` is the heights of
a solution of `M(t)`, obtained by dividing the core heights, and the corrected constant
coefficients, by `t`. -/
theorem _root_.Graph.exists_contractHeight_eq [Fintype α] {G : Graph α β} {W : Set α}
    {r : α} {q : α × Fin 2 → K} {t : K} (ht : t ≠ 0) {z : α → K}
    (hz : z ∈ G.liftingSpace (contractPicture W r q t)) :
    ∃ x, (G.contractLiftingMatrix K W r q).map (MvPolynomial.eval (fun _ => t)) *ᵥ x = 0 ∧
      contractHeight W t x = z := by
  classical
  obtain ⟨hs, ha⟩ := hz
  choose! g hg using ha
  set x : α ⊕ (α × Fin 3) → K := Sum.elim (fun w => if w ∈ W then t⁻¹ * z w else z w)
    (fun p => if p.1 ∉ V(G) then 0 else if p.1 ∈ G.coreNbhd W then
      ![g p.1 0, g p.1 1,
        t⁻¹ * (g p.1 2 + (1 - t) * (g p.1 0 * q (r, 0) + g p.1 1 * q (r, 1)))] p.2
      else g p.1 p.2) with hx
  refine ⟨x, Graph.contractLiftingMatrix_mulVec_eq_zero_iff.mpr
    ⟨fun w hw => ?_, fun v hv w hw => ?_, fun v hv i => ?_⟩, ?_⟩
  · have hwW : w ∈ W → z w = 0 := fun _ => hs w hw
    by_cases hW : w ∈ W <;> simp [hx, hW, hs w hw]
  · have hgw := hg v hv w hw
    by_cases hc : v ∈ G.coreNbhd W
    · by_cases hwW : w ∈ W
      · simp only [hx, Sum.elim_inl, Sum.elim_inr, hwW, ite_true, hv, not_true_eq_false,
          ite_false, hc, Graph.contractWeightAt, and_false, dotProduct, Fin.sum_univ_three,
          pencilPicturePoint, hgw, contractPicture]
        simp
        field_simp
        ring
      · simp only [hx, Sum.elim_inl, Sum.elim_inr, hwW, ite_false, hv, not_true_eq_false,
          hc, ite_true, Graph.contractWeightAt, not_false_eq_true, and_self, dotProduct,
          Fin.sum_univ_three, pencilPicturePoint, hgw, contractPicture]
        simp
        field_simp
        ring
    · have hwW : w ∉ W := fun hwW => hc ⟨w, hwW, hw⟩
      simp only [hx, Sum.elim_inl, Sum.elim_inr, hwW, ite_false, hv, not_true_eq_false, hc,
        Graph.contractWeightAt, false_and, hgw, pencilPicturePoint_contractPicture_of_not_mem hwW]
  · simp [hx, hv]
  · funext w
    by_cases hwW : w ∈ W <;> simp [contractHeight_apply, hx, hwW, ht]

/-- **At `t ≠ 0` the kernel of `M(t)` is at least `L_G(q(t))`**
(`lem:pencil-contract-lifting-kernel`): `L_G(q(t))` is the image of `ker M(t)` under
`contractHeight` (`Graph.exists_contractHeight_eq`). -/
theorem _root_.Graph.finrank_liftingSpace_le_finrank_ker_contractLiftingMatrix [Fintype α]
    {G : Graph α β} {W : Set α} {r : α} {q : α × Fin 2 → K} {t : K} (ht : t ≠ 0) :
    Module.finrank K (G.liftingSpace (contractPicture W r q t)) ≤
      Module.finrank K (LinearMap.ker ((G.contractLiftingMatrix K W r q).map
        (MvPolynomial.eval (fun _ => t))).mulVecLin) := by
  have hle : G.liftingSpace (contractPicture W r q t) ≤
      (LinearMap.ker ((G.contractLiftingMatrix K W r q).map
        (MvPolynomial.eval (fun _ => t))).mulVecLin).map (contractHeight W t) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Graph.exists_contractHeight_eq ht hz
    exact ⟨x, hx, rfl⟩
  exact (Submodule.finrank_mono hle).trans (Submodule.finrank_map_le _ _)

/-! ## The core's rank along the curve, by a collineation -/

/-- **The core's rank along the curve is its rank at the magnified core picture**
(`lem:pencil-contract-magnified-rank`; Phase 40k CONTRACT-A). At `t ≠ 0`, the configuration of
`H = G[W]` at `(q(t), z(t))` is the image of the configuration at `(q, z)` (the unscaled core
heights of the unknowns) under the collineation
`(x, y, ζ, w) ↦ (t x + (1 − t) x_r w, t y + (1 − t) y_r w, t ζ, w)` of `K⁴`, so
`PanelHingeFramework.finrank_span_rigidityRows_ofNormals_linearEquiv` gives the same rank at both:
unlike `Graph.finrank_span_rigidityRows_induce_contractHeight` (`Contract.lean`), no flatness of
the core is needed. -/
theorem _root_.Graph.finrank_span_rigidityRows_induce_contractHeight_eq {G : Graph α β}
    {W : Set α} {r : α} (q : α × Fin 2 → K) {t : K} (ht : t ≠ 0) (x : α ⊕ (α × Fin 3) → K)
    {ends : β → α × α}
    (hends : ∀ e u v, (G.induce W).IsLink e u v → (G.induce W).IsLink e (ends e).1 (ends e).2) :
    Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 2) (G.induce W) ends
        (fun p => pencilConfigPoint (contractPicture W r q t) (contractHeight W t x) p.1 p.2)
          ).toBodyHinge.rigidityRows)
      = Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 2) (G.induce W)
        ends (fun p => pencilConfigPoint q (fun w => x (Sum.inl w)) p.1 p.2)
          ).toBodyHinge.rigidityRows) := by
  let f : (Fin 4 → K) →ₗ[K] (Fin 4 → K) :=
    { toFun := fun b => ![t * b 0 + (1 - t) * q (r, 0) * b 3,
        t * b 1 + (1 - t) * q (r, 1) * b 3, t * b 2, b 3]
      map_add' := fun b c => by funext i; fin_cases i <;> simp <;> ring
      map_smul' := fun c b => by funext i; fin_cases i <;> simp <;> ring }
  let f' : (Fin 4 → K) →ₗ[K] (Fin 4 → K) :=
    { toFun := fun b => ![t⁻¹ * (b 0 - (1 - t) * q (r, 0) * b 3),
        t⁻¹ * (b 1 - (1 - t) * q (r, 1) * b 3), t⁻¹ * b 2, b 3]
      map_add' := fun b c => by funext i; fin_cases i <;> simp <;> ring
      map_smul' := fun c b => by funext i; fin_cases i <;> simp <;> ring }
  let g : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K) := LinearEquiv.ofLinearMap f f'
    (LinearMap.ext fun b => funext fun i => by
      fin_cases i <;> simp [f, f'] <;> field_simp <;> ring)
    (LinearMap.ext fun b => funext fun i => by
      fin_cases i <;> simp [f, f'] <;> field_simp)
  refine PanelHingeFramework.finrank_span_rigidityRows_ofNormals_linearEquiv hends g
    (p := pencilConfigPoint q (fun w => x (Sum.inl w))) fun w hw => ?_
  have hwW : w ∈ W := hw
  funext i
  fin_cases i <;> simp [g, f, pencilConfigPoint, contractPicture, contractHeight_apply, hwW] <;>
    ring

/-! ## Three independent picture points pin a plane -/

/-- A coefficient vector `h ∈ K³` orthogonal to three linearly independent homogeneous picture
points is zero. -/
theorem eq_zero_of_dotProduct_pencilPicturePoint {q : α × Fin 2 → K} {s : Fin 3 → α}
    (hli : LinearIndependent K (fun i => pencilPicturePoint q (s i))) {h : Fin 3 → K}
    (hh : ∀ i, h ⬝ᵥ pencilPicturePoint q (s i) = 0) : h = 0 := by
  have hunit : IsUnit (Matrix.of fun j => pencilPicturePoint q (s j)) :=
    Matrix.linearIndependent_rows_iff_isUnit.mp hli
  have hz : (Matrix.of fun j => pencilPicturePoint q (s j)) *ᵥ h =
      (Matrix.of fun j => pencilPicturePoint q (s j)) *ᵥ 0 := by
    rw [Matrix.mulVec_zero]
    funext j
    simp only [Matrix.mulVec, Matrix.of_apply, Pi.zero_apply]
    rw [dotProduct_comm]
    exact hh j
  exact Matrix.mulVec_injective_iff_isUnit.mpr hunit hz

/-- Over an admissible picture, a coefficient vector orthogonal to the homogeneous picture points of
a whole closed neighbourhood is zero: the neighbourhood carries three independent points. -/
theorem _root_.Graph.IsAdmissiblePicture.eq_zero_of_forall_closedNbhd {G : Graph α β}
    {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) {v : α} (hv : v ∈ V(G))
    {h : Fin 3 → K} (hh : ∀ w ∈ G.closedNbhd v, h ⬝ᵥ pencilPicturePoint q w = 0) : h = 0 := by
  obtain ⟨s, hs, hli⟩ := hq.2 v hv
  exact eq_zero_of_dotProduct_pencilPicturePoint hli fun i => hh _ (hs i)

/-- Over an admissible picture, two coefficient vectors that agree on the homogeneous picture points
of a closed neighbourhood are equal: a closed neighbourhood has one plane. -/
theorem _root_.Graph.IsAdmissiblePicture.eq_of_forall_closedNbhd {G : Graph α β}
    {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) {v : α} (hv : v ∈ V(G))
    {h h' : Fin 3 → K}
    (hh : ∀ w ∈ G.closedNbhd v, h ⬝ᵥ pencilPicturePoint q w = h' ⬝ᵥ pencilPicturePoint q w) :
    h = h' := by
  have := hq.eq_zero_of_forall_closedNbhd hv (h := h - h') fun w hw => by
    rw [sub_dotProduct, hh w hw, sub_self]
  exact sub_eq_zero.mp this

/-! ## The bodies and closed neighbourhoods of the contraction -/

/-- The collapse sends a core body to the representative `r`. -/
theorem collapseTo_of_mem {W : Set α} {r a : α} (ha : a ∈ W) : Graph.collapseTo r W a = r := by
  simp [Graph.collapseTo, ha]

/-- The collapse fixes every body outside the core. -/
theorem collapseTo_of_not_mem {W : Set α} {r a : α} (ha : a ∉ W) :
    Graph.collapseTo r W a = a := by
  simp [Graph.collapseTo, ha]

/-- With `r ∈ W`, a body that the collapse sends to `r` lies in the core. -/
theorem mem_of_collapseTo_eq {W : Set α} {r a : α} (hr : r ∈ W)
    (h : Graph.collapseTo r W a = r) : a ∈ W := by
  by_contra ha
  rw [collapseTo_of_not_mem ha] at h
  exact ha (h ▸ hr)

/-- An edge of `G` not inside the core is an edge of `G/H`, between the collapsed ends. -/
theorem _root_.Graph.isLink_rigidContract_of_isLink {G : Graph α β} {W : Set α} {r : α}
    {e : β} {v w : α} (he : G.IsLink e v w) (hvw : ¬ (v ∈ W ∧ w ∈ W)) :
    (G.rigidContract (G.induce W) r).IsLink e (Graph.collapseTo r W v)
      (Graph.collapseTo r W w) := by
  simp only [Graph.rigidContract, Graph.map_isLink, Graph.deleteEdges_isLink]
  refine ⟨v, w, ⟨he, fun heH => hvw ?_⟩, rfl, rfl⟩
  obtain ⟨a, b, hab⟩ := Graph.exists_isLink_of_mem_edgeSet heH
  rw [Graph.induce_isLink] at hab
  rcases he.eq_and_eq_or_eq_and_eq hab.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨hab.2.1, hab.2.2⟩
  · exact ⟨hab.2.2, hab.2.1⟩

/-- The collapse maps a member `w` of the closed neighbourhood of `v` into the closed
neighbourhood of `v`'s image in `G/H`, unless `v` and `w` both lie in the core. -/
theorem _root_.Graph.collapseTo_mem_closedNbhd_rigidContract {G : Graph α β} {W : Set α}
    {r : α} {v w : α} (hw : w ∈ G.closedNbhd v) (hvw : ¬ (v ∈ W ∧ w ∈ W)) :
    Graph.collapseTo r W w ∈
      (G.rigidContract (G.induce W) r).closedNbhd (Graph.collapseTo r W v) := by
  rcases hw with rfl | ⟨e, he⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨e, Graph.isLink_rigidContract_of_isLink he hvw⟩

/-- A member of a closed neighbourhood of `G/H` is the body itself or the collapsed far end of an
edge of `G` not inside the core. -/
theorem _root_.Graph.mem_closedNbhd_rigidContract {G : Graph α β} {W : Set α} {r : α}
    {v' w' : α} (h : w' ∈ (G.rigidContract (G.induce W) r).closedNbhd v') :
    w' = v' ∨ ∃ e a b, G.IsLink e a b ∧ ¬ (a ∈ W ∧ b ∈ W) ∧
      v' = Graph.collapseTo r W a ∧ w' = Graph.collapseTo r W b := by
  rcases h with h | ⟨e, he⟩
  · exact Or.inl h
  · right
    simp only [Graph.rigidContract, Graph.map_isLink, Graph.deleteEdges_isLink] at he
    obtain ⟨a, b, ⟨hab, heH⟩, rfl, rfl⟩ := he
    refine ⟨e, a, b, hab, fun ⟨ha, hb⟩ => heH ?_, rfl, rfl⟩
    exact ((Graph.induce_isLink G W e a b).mpr ⟨hab, ha, hb⟩).edge_mem

/-- The bodies of `G/H` are `r` and the bodies of `G` outside the core. -/
theorem _root_.Graph.mem_vertexSet_rigidContract_iff {G : Graph α β} {W : Set α} {r : α}
    (hr : r ∈ W) (hW : W ⊆ V(G)) {v : α} :
    v ∈ V(G.rigidContract (G.induce W) r) ↔ v = r ∨ (v ∈ V(G) ∧ v ∉ W) := by
  rw [Graph.vertexSet_rigidContract, Graph.vertexSet_induce]
  constructor
  · rintro ⟨a, ha, rfl⟩
    by_cases haW : a ∈ W
    · exact Or.inl (collapseTo_of_mem haW)
    · exact Or.inr ⟨by rwa [collapseTo_of_not_mem haW], by rwa [collapseTo_of_not_mem haW]⟩
  · rintro (rfl | ⟨hv, hvW⟩)
    · exact ⟨v, hW hr, collapseTo_of_mem hr⟩
    · exact ⟨v, hv, collapseTo_of_not_mem hvW⟩

/-! ## Closed neighbourhoods of an induced subgraph -/

/-- A closed neighbourhood in an induced subgraph lies in the closed neighbourhood in `G`. -/
theorem _root_.Graph.closedNbhd_induce_subset {G : Graph α β} {W : Set α} {c : α} :
    (G.induce W).closedNbhd c ⊆ G.closedNbhd c := by
  rintro w (rfl | ⟨e, he⟩)
  · exact Or.inl rfl
  · exact Or.inr ⟨e, he.1⟩

/-! ## The rescaled system at the end of the curve -/

open Classical in
/-- **The limit map** from the unknowns of `M(0)` to heights of `G/H`: `r` gets the core height at
`r`, each body of `G` outside the core its own height shifted by it, and every other body `0`. -/
noncomputable def contractLimitMap (G : Graph α β) (W : Set α) (r : α) :
    (α ⊕ (α × Fin 3) → K) →ₗ[K] (α → K) where
  toFun x w := if w = r then x (Sum.inl r) else
    if w ∈ V(G) ∧ w ∉ W then x (Sum.inl w) + x (Sum.inl r) else 0
  map_add' x y := by
    funext w
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' c x := by
    funext w
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

open Classical in
/-- Unfolding `contractLimitMap`. -/
theorem contractLimitMap_apply (G : Graph α β) (W : Set α) (r : α)
    (x : α ⊕ (α × Fin 3) → K) (w : α) :
    contractLimitMap G W r x w = if w = r then x (Sum.inl r) else
      if w ∈ V(G) ∧ w ∉ W then x (Sum.inl w) + x (Sum.inl r) else 0 := rfl

/-- **The limit map sends a solution of `M(0)` into `L_{G/H}(q)`, given one plane on the core**
(`Graph.exists_core_plane`'s conclusion, taken as a hypothesis so a later step can supply it from a
magnified picture instead): after the shift by the height at `r` the plane passes through `r` and
every attachment. -/
theorem _root_.Graph.contractLimitMap_mem_liftingSpace [Fintype α] {G : Graph α β}
    {W : Set α} {r : α} (hr : r ∈ W) (hW : W ⊆ V(G)) {q : α × Fin 2 → K}
    {x : α ⊕ (α × Fin 3) → K}
    (hx : (G.contractLiftingMatrix K W r q).map (MvPolynomial.eval (fun _ => (0 : K))) *ᵥ x = 0)
    (hg : ∃ g : Fin 3 → K, (∀ w ∈ W, x (Sum.inl w) = g ⬝ᵥ pencilPicturePoint q w) ∧
      ∀ c ∈ W, (fun i => x (Sum.inr (c, i))) = g) :
    contractLimitMap G W r x ∈ (G.rigidContract (G.induce W) r).liftingSpace q := by
  obtain ⟨g, hgW, hgc⟩ := hg
  obtain ⟨-, h2, -⟩ := Graph.contractLiftingMatrix_mulVec_eq_zero_iff.mp hx
  refine ⟨fun w hw => ?_, fun v' hv' => ?_⟩
  · rw [Graph.mem_vertexSet_rigidContract_iff hr hW] at hw
    push Not at hw
    rw [contractLimitMap_apply, ite_eq_right hw.1, ite_eq_right (fun h => h.2 (hw.2 h.1))]
  · rw [Graph.mem_vertexSet_rigidContract_iff hr hW] at hv'
    by_cases hv'r : v' = r
    · subst hv'r
      refine ⟨![g 0, g 1, x (Sum.inl v') - (g 0 * q (v', 0) + g 1 * q (v', 1))],
        fun w' hw' => ?_⟩
      rcases Graph.mem_closedNbhd_rigidContract hw' with rfl | ⟨e, a, b, hab, hnot, ha, rfl⟩
      · simp [contractLimitMap_apply, pencilPicturePoint, dotProduct, Fin.sum_univ_three]
      · have haW : a ∈ W := mem_of_collapseTo_eq hr ha.symm
        have hbW : b ∉ W := fun hb => hnot ⟨haW, hb⟩
        rw [collapseTo_of_not_mem hbW]
        have hrow := h2 a hab.left_mem b (Or.inr ⟨e, hab⟩)
        rw [Graph.contractWeightAt_of_mem_coreNbhd ⟨a, haW, Or.inl rfl⟩ hbW, hgc a haW] at hrow
        have hbr : b ≠ v' := fun h => hbW (h ▸ hr)
        rw [contractLimitMap_apply, ite_eq_right hbr, ite_eq_left ⟨hab.right_mem, hbW⟩, hrow]
        simp [pencilPicturePoint, dotProduct, Fin.sum_univ_three]
        ring
    · have hv'' : v' ∈ V(G) ∧ v' ∉ W := hv'.resolve_left hv'r
      by_cases hc : v' ∈ G.coreNbhd W
      · refine ⟨![x (Sum.inr (v', 0)), x (Sum.inr (v', 1)), x (Sum.inl r) -
          (x (Sum.inr (v', 0)) * q (r, 0) + x (Sum.inr (v', 1)) * q (r, 1))], fun w' hw' => ?_⟩
        have hout : ∀ b ∈ G.closedNbhd v', b ∉ W → contractLimitMap G W r x b =
            ![x (Sum.inr (v', 0)), x (Sum.inr (v', 1)), x (Sum.inl r) -
              (x (Sum.inr (v', 0)) * q (r, 0) + x (Sum.inr (v', 1)) * q (r, 1))] ⬝ᵥ
              pencilPicturePoint q b := by
          intro b hb hbW
          have hrow := h2 v' hv''.1 b hb
          rw [Graph.contractWeightAt_of_mem_coreNbhd hc hbW] at hrow
          have hbr : b ≠ r := fun h => hbW (h ▸ hr)
          rw [contractLimitMap_apply, ite_eq_right hbr,
            ite_eq_left ⟨Graph.closedNbhd_subset_vertexSet hv''.1 hb, hbW⟩, hrow]
          simp [pencilPicturePoint, dotProduct, Fin.sum_univ_three]
          ring
        rcases Graph.mem_closedNbhd_rigidContract hw' with rfl | ⟨e, a, b, hab, hnot, ha, rfl⟩
        · exact hout w' (Or.inl rfl) hv''.2
        · have haW : a ∉ W := fun haW => hv'r (by rw [ha, collapseTo_of_mem haW])
          rw [collapseTo_of_not_mem haW] at ha
          rw [← ha] at hab
          by_cases hbW : b ∈ W
          · rw [collapseTo_of_mem hbW]
            simp [contractLimitMap_apply, pencilPicturePoint, dotProduct, Fin.sum_univ_three]
          · rw [collapseTo_of_not_mem hbW]
            exact hout b (Or.inr ⟨e, hab⟩) hbW
      · refine ⟨fun i => x (Sum.inr (v', i)) + if i = 2 then x (Sum.inl r) else 0,
          fun w' hw' => ?_⟩
        have hout : ∀ b ∈ G.closedNbhd v', contractLimitMap G W r x b =
            (fun i => x (Sum.inr (v', i)) + if i = 2 then x (Sum.inl r) else 0) ⬝ᵥ
              pencilPicturePoint q b := by
          intro b hb
          have hbW : b ∉ W := fun hbW => hc ⟨b, hbW, hb⟩
          have hrow := h2 v' hv''.1 b hb
          rw [Graph.contractWeightAt_of_not_mem_coreNbhd hc] at hrow
          have hbr : b ≠ r := fun h => hbW (h ▸ hr)
          rw [contractLimitMap_apply, ite_eq_right hbr,
            ite_eq_left ⟨Graph.closedNbhd_subset_vertexSet hv''.1 hb, hbW⟩, hrow]
          simp [pencilPicturePoint, dotProduct, Fin.sum_univ_three]
          ring
        rcases Graph.mem_closedNbhd_rigidContract hw' with rfl | ⟨e, a, b, hab, hnot, ha, rfl⟩
        · exact hout w' (Or.inl rfl)
        · have haW : a ∉ W := fun haW => hv'r (by rw [ha, collapseTo_of_mem haW])
          rw [collapseTo_of_not_mem haW] at ha
          rw [← ha] at hab
          have hbW : b ∉ W := fun hbW => hc ⟨b, hbW, Or.inr ⟨e, hab⟩⟩
          rw [collapseTo_of_not_mem hbW]
          exact hout b (Or.inr ⟨e, hab⟩)

/-- **The limit map is injective on `ker M(0)`, given one plane on the core**: the plane
annihilates three independent picture points of `r`'s closed neighbourhood in `G/H` (`q` admissible
there), so it vanishes, and then so does every plane outside the core — an attachment's constant
coefficient by its row at a core neighbour. -/
theorem _root_.Graph.eq_zero_of_contractLimitMap_eq_zero [Fintype α] {G : Graph α β}
    {W : Set α} {r : α} (hr : r ∈ W) (hW : W ⊆ V(G)) {q : α × Fin 2 → K}
    (hqc : (G.rigidContract (G.induce W) r).IsAdmissiblePicture q)
    {x : α ⊕ (α × Fin 3) → K}
    (hx : (G.contractLiftingMatrix K W r q).map (MvPolynomial.eval (fun _ => (0 : K))) *ᵥ x = 0)
    (hg : ∃ g : Fin 3 → K, (∀ w ∈ W, x (Sum.inl w) = g ⬝ᵥ pencilPicturePoint q w) ∧
      ∀ c ∈ W, (fun i => x (Sum.inr (c, i))) = g)
    (h0 : contractLimitMap G W r x = 0) : x = 0 := by
  obtain ⟨g, hgW, hgc⟩ := hg
  obtain ⟨h1, h2, h3⟩ := Graph.contractLiftingMatrix_mulVec_eq_zero_iff.mp hx
  have hxr : x (Sum.inl r) = 0 := by simpa [contractLimitMap_apply] using congr_fun h0 r
  have hxO : ∀ w, w ∉ W → x (Sum.inl w) = 0 := by
    intro w hwW
    by_cases hw : w ∈ V(G)
    · have := congr_fun h0 w
      have hwr : w ≠ r := fun h => hwW (h ▸ hr)
      rw [contractLimitMap_apply, ite_eq_right hwr, ite_eq_left ⟨hw, hwW⟩, hxr, add_zero] at this
      exact this
    · exact h1 w hw
  have hrVc : r ∈ V(G.rigidContract (G.induce W) r) :=
    (Graph.mem_vertexSet_rigidContract_iff hr hW).mpr (Or.inl rfl)
  have hgr : g ⬝ᵥ pencilPicturePoint q r = 0 := by rw [← hgW r hr, hxr]
  have hg0 : g = 0 := by
    refine hqc.eq_zero_of_forall_closedNbhd hrVc fun w' hw' => ?_
    rcases Graph.mem_closedNbhd_rigidContract hw' with rfl | ⟨e, a, b, hab, hnot, ha, rfl⟩
    · exact hgr
    · have haW : a ∈ W := mem_of_collapseTo_eq hr ha.symm
      have hbW : b ∉ W := fun hb => hnot ⟨haW, hb⟩
      rw [collapseTo_of_not_mem hbW]
      have hrow := h2 a hab.left_mem b (Or.inr ⟨e, hab⟩)
      rw [Graph.contractWeightAt_of_mem_coreNbhd ⟨a, haW, Or.inl rfl⟩ hbW, hgc a haW,
        hxO b hbW] at hrow
      simp only [pencilPicturePoint, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, sub_zero, one_mul, mul_zero, add_zero,
        mul_one] at hrow hgr ⊢
      linear_combination hgr + hrow.symm
  have hx_inl : ∀ w, x (Sum.inl w) = 0 := fun w => by
    by_cases hw : w ∈ W
    · rw [hgW w hw, hg0, zero_dotProduct]
    · exact hxO w hw
  have hx_inr : ∀ v i, x (Sum.inr (v, i)) = 0 := by
    intro v i
    by_cases hv : v ∈ V(G)
    swap
    · exact h3 v hv i
    by_cases hvW : v ∈ W
    · have := congr_fun (hgc v hvW) i
      rw [hg0] at this
      exact this
    have hvVc : v ∈ V(G.rigidContract (G.induce W) r) :=
      (Graph.mem_vertexSet_rigidContract_iff hr hW).mpr (Or.inr ⟨hv, hvW⟩)
    by_cases hc : v ∈ G.coreNbhd W
    · have hh' : (![x (Sum.inr (v, 0)), x (Sum.inr (v, 1)),
          -(x (Sum.inr (v, 0)) * q (r, 0) + x (Sum.inr (v, 1)) * q (r, 1))] : Fin 3 → K) = 0 := by
        refine hqc.eq_zero_of_forall_closedNbhd hvVc fun w' hw' => ?_
        have hout : ∀ b ∈ G.closedNbhd v, b ∉ W →
            (![x (Sum.inr (v, 0)), x (Sum.inr (v, 1)),
              -(x (Sum.inr (v, 0)) * q (r, 0) + x (Sum.inr (v, 1)) * q (r, 1))] : Fin 3 → K)
              ⬝ᵥ pencilPicturePoint q b = 0 := by
          intro b hb hbW
          have hrow := h2 v hv b hb
          rw [Graph.contractWeightAt_of_mem_coreNbhd hc hbW, hx_inl b] at hrow
          simp [pencilPicturePoint, dotProduct, Fin.sum_univ_three] at hrow ⊢
          linear_combination -hrow
        rcases Graph.mem_closedNbhd_rigidContract hw' with rfl | ⟨e, a, b, hab, hnot, ha, rfl⟩
        · exact hout w' (Or.inl rfl) hvW
        · have haW : a ∉ W := fun haW => hvW (by rw [ha, collapseTo_of_mem haW]; exact hr)
          rw [collapseTo_of_not_mem haW] at ha
          rw [← ha] at hab
          by_cases hbW : b ∈ W
          · rw [collapseTo_of_mem hbW]
            simp [pencilPicturePoint, dotProduct, Fin.sum_univ_three]
          · rw [collapseTo_of_not_mem hbW]
            exact hout b (Or.inr ⟨e, hab⟩) hbW
      have h0' := congr_fun hh' 0
      have h1' := congr_fun hh' 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h0' h1'
      obtain ⟨c, hcW, hcv⟩ := hc
      have hrow := h2 v hv c hcv
      rw [Graph.contractWeightAt_of_mem hcW, hx_inl c] at hrow
      simp [pencilPicturePoint, dotProduct, Fin.sum_univ_three, h0', h1'] at hrow
      fin_cases i
      · exact h0'
      · exact h1'
      · simpa using hrow.symm
    · have hh : (fun i => x (Sum.inr (v, i))) = 0 := by
        refine hqc.eq_zero_of_forall_closedNbhd hvVc fun w' hw' => ?_
        have hout : ∀ b ∈ G.closedNbhd v,
            (fun i => x (Sum.inr (v, i))) ⬝ᵥ pencilPicturePoint q b = 0 := by
          intro b hb
          have hrow := h2 v hv b hb
          rw [Graph.contractWeightAt_of_not_mem_coreNbhd hc, hx_inl b] at hrow
          exact hrow.symm
        rcases Graph.mem_closedNbhd_rigidContract hw' with rfl | ⟨e, a, b, hab, hnot, ha, rfl⟩
        · exact hout w' (Or.inl rfl)
        · have haW : a ∉ W := fun haW => hvW (by rw [ha, collapseTo_of_mem haW]; exact hr)
          rw [collapseTo_of_not_mem haW] at ha
          rw [← ha] at hab
          have hbW : b ∉ W := fun hbW => hc ⟨b, hbW, Or.inr ⟨e, hab⟩⟩
          rw [collapseTo_of_not_mem hbW]
          exact hout b (Or.inr ⟨e, hab⟩)
      exact congr_fun hh i
  funext c
  rcases c with w | ⟨v, i⟩
  · exact hx_inl w
  · exact hx_inr v i

/-- **The flat-core extension** (`lem:pencil-contract-limit`; (MC-37) step 2): at `t = 0`, every
height of `L_{G/H}(q)` vanishing at `r` agrees off the core with the heights of a solution of
`M(0)`. The core is put on the plane of `z` at `r` (KT's panels of the core set to the contracted
body's panel, Claim 6.4, p. 675); each attachment's constant coefficient is fixed by its one core
neighbour, which is where `hatt` (`G/H` simple) is used. -/
theorem _root_.Graph.exists_mem_ker_contractLiftingMatrix_zero [Fintype α] {G : Graph α β}
    {W : Set α} {r : α} (hr : r ∈ W) (hW : W ⊆ V(G))
    (hatt : ∀ u ∉ W, ∀ c₁ ∈ W, ∀ c₂ ∈ W, G.Adj u c₁ → G.Adj u c₂ → c₁ = c₂)
    {q : α × Fin 2 → K} {z : α → K}
    (hz : z ∈ (G.rigidContract (G.induce W) r).liftingSpace q) (hzr : z r = 0) :
    ∃ x, (G.contractLiftingMatrix K W r q).map (MvPolynomial.eval (fun _ => (0 : K))) *ᵥ x = 0 ∧
      ∀ w ∉ W, x (Sum.inl w) = z w := by
  classical
  obtain ⟨hs, ha⟩ := hz
  have hrVc : r ∈ V(G.rigidContract (G.induce W) r) :=
    (Graph.mem_vertexSet_rigidContract_iff hr hW).mpr (Or.inl rfl)
  choose! h hh using ha
  have hcn : ∀ u, ∃ c, u ∈ G.coreNbhd W → c ∈ W ∧ c ∈ G.closedNbhd u := fun u => by
    by_cases hu : u ∈ G.coreNbhd W
    · obtain ⟨c, hc, hcu⟩ := hu
      exact ⟨c, fun _ => ⟨hc, hcu⟩⟩
    · exact ⟨u, fun h' => absurd h' hu⟩
  choose cn hcn using hcn
  set x : α ⊕ (α × Fin 3) → K :=
    Sum.elim (fun w => if w ∈ W then h r ⬝ᵥ pencilPicturePoint q w else z w)
      (fun p => if p.1 ∉ V(G) then 0 else if p.1 ∈ W then h r p.2 else
        if p.1 ∈ G.coreNbhd W then
          ![h p.1 0, h p.1 1, h r ⬝ᵥ pencilPicturePoint q (cn p.1) -
            (h p.1 0 * q (cn p.1, 0) + h p.1 1 * q (cn p.1, 1))] p.2
        else h p.1 p.2) with hxdef
  have hxinl : ∀ w, x (Sum.inl w) = if w ∈ W then h r ⬝ᵥ pencilPicturePoint q w else z w :=
    fun w => rfl
  have hr0 : h r ⬝ᵥ pencilPicturePoint q r = 0 := by rw [← hh r hrVc r (Or.inl rfl), hzr]
  refine ⟨x, Graph.contractLiftingMatrix_mulVec_eq_zero_iff.mpr ⟨?_, ?_, ?_⟩,
    fun w hw => by rw [hxinl, ite_eq_right hw]⟩
  · intro w hw
    have hwW : w ∉ W := fun h' => hw (hW h')
    have hwc : w ∉ V(G.rigidContract (G.induce W) r) := by
      rw [Graph.mem_vertexSet_rigidContract_iff hr hW]
      rintro (rfl | ⟨h', -⟩)
      · exact hwW hr
      · exact hw h'
    rw [hxinl, ite_eq_right hwW, hs w hwc]
  · intro v hv w hw
    by_cases hvW : v ∈ W
    · have hvc : v ∈ G.coreNbhd W := ⟨v, hvW, Or.inl rfl⟩
      have hcoef : (fun i => x (Sum.inr (v, i))) = h r := by
        funext i
        simp [hxdef, hv, hvW]
      rw [hcoef]
      by_cases hwW : w ∈ W
      · rw [Graph.contractWeightAt_of_mem hwW, hxinl, ite_eq_left hwW]
      · rw [Graph.contractWeightAt_of_mem_coreNbhd hvc hwW, hxinl, ite_eq_right hwW]
        have hwN : w ∈ (G.rigidContract (G.induce W) r).closedNbhd r := by
          have := Graph.collapseTo_mem_closedNbhd_rigidContract (r := r) hw (fun h' => hwW h'.2)
          rwa [collapseTo_of_not_mem hwW, collapseTo_of_mem hvW] at this
        rw [hh r hrVc w hwN]
        simp only [pencilPicturePoint, dotProduct, Fin.sum_univ_three] at hr0 ⊢
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.tail_cons, Matrix.head_cons] at hr0 ⊢
        have hsplit : h r 0 * q (w, 0) + h r 1 * q (w, 1) + h r 2 * 1 =
            (h r 0 * (q (w, 0) - (1 - 0) * q (r, 0)) + h r 1 * (q (w, 1) - (1 - 0) * q (r, 1)) +
              h r 2 * 0) + (h r 0 * q (r, 0) + h r 1 * q (r, 1) + h r 2 * 1) := by ring
        rw [hsplit, hr0, add_zero]
    · have hvVc : v ∈ V(G.rigidContract (G.induce W) r) :=
        (Graph.mem_vertexSet_rigidContract_iff hr hW).mpr (Or.inr ⟨hv, hvW⟩)
      by_cases hvc : v ∈ G.coreNbhd W
      · obtain ⟨hcW, hcv⟩ := hcn v hvc
        have hcoef : (fun i => x (Sum.inr (v, i))) =
            ![h v 0, h v 1, h r ⬝ᵥ pencilPicturePoint q (cn v) -
              (h v 0 * q (cn v, 0) + h v 1 * q (cn v, 1))] := by
          funext i
          simp [hxdef, hv, hvW, hvc]
        rw [hcoef]
        by_cases hwW : w ∈ W
        · have hwc : w = cn v := by
            have hadj1 : G.Adj v w := by
              rcases hw with rfl | ⟨e, he⟩
              · exact absurd hwW hvW
              · exact ⟨e, he⟩
            have hadj2 : G.Adj v (cn v) := by
              rcases hcv with h' | ⟨e, he⟩
              · exact absurd (h' ▸ hcW) hvW
              · exact ⟨e, he⟩
            exact hatt v hvW w hwW (cn v) hcW hadj1 hadj2
          rw [Graph.contractWeightAt_of_mem hwW, hxinl, ite_eq_left hwW, hwc]
          simp only [pencilPicturePoint, dotProduct, Fin.sum_univ_three]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
            Matrix.tail_cons, Matrix.head_cons]
          ring
        · rw [Graph.contractWeightAt_of_mem_coreNbhd hvc hwW, hxinl, ite_eq_right hwW]
          have hwN : w ∈ (G.rigidContract (G.induce W) r).closedNbhd v := by
            have := Graph.collapseTo_mem_closedNbhd_rigidContract (r := r) hw
              (fun h' => hvW h'.1)
            rwa [collapseTo_of_not_mem hwW, collapseTo_of_not_mem hvW] at this
          have hrN : r ∈ (G.rigidContract (G.induce W) r).closedNbhd v := by
            have := Graph.collapseTo_mem_closedNbhd_rigidContract (r := r) hcv
              (fun h' => hvW h'.1)
            rwa [collapseTo_of_mem hcW, collapseTo_of_not_mem hvW] at this
          have h2 := hh v hvVc r hrN
          rw [hzr] at h2
          rw [hh v hvVc w hwN]
          simp only [pencilPicturePoint, dotProduct, Fin.sum_univ_three] at h2 ⊢
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
            Matrix.tail_cons, Matrix.head_cons] at h2 ⊢
          have hsplit : h v 0 * q (w, 0) + h v 1 * q (w, 1) + h v 2 * 1 =
              (h v 0 * (q (w, 0) - (1 - 0) * q (r, 0)) + h v 1 * (q (w, 1) - (1 - 0) * q (r, 1)) +
                (h r 0 * q (cn v, 0) + h r 1 * q (cn v, 1) + h r 2 * 1 -
                  (h v 0 * q (cn v, 0) + h v 1 * q (cn v, 1))) * 0) +
              (h v 0 * q (r, 0) + h v 1 * q (r, 1) + h v 2 * 1) := by ring
          rw [hsplit, ← h2, add_zero]
      · have hwW : w ∉ W := fun hwW => hvc ⟨w, hwW, hw⟩
        have hcoef : (fun i => x (Sum.inr (v, i))) = h v := by
          funext i
          simp [hxdef, hv, hvW, hvc]
        rw [hcoef, Graph.contractWeightAt_of_not_mem_coreNbhd hvc, hxinl, ite_eq_right hwW]
        have hwN : w ∈ (G.rigidContract (G.induce W) r).closedNbhd v := by
          have := Graph.collapseTo_mem_closedNbhd_rigidContract (r := r) hw (fun h' => hvW h'.1)
          rwa [collapseTo_of_not_mem hwW, collapseTo_of_not_mem hvW] at this
        exact hh v hvVc w hwN
  · intro v hv i
    simp [hxdef, hv]

/-! ## The kernel of `M(0)` at any core -/

/-- **The core heights of a solution lie in `L_H(q)`, at every `t`**
(`lem:pencil-contract-kernel-bound` (1); Phase 40k CONTRACT-A): `contractCoreRestrict` (`ρ` below)
maps a solution of `M(t)` into `L_H(q)`. The core rows keep the weight `(x_w, y_w, 1)` along the
curve (the `hmem` step of `Graph.exists_core_plane`), with no flatness of the core needed. -/
theorem _root_.Graph.liftingRestrict_mem_liftingSpace_induce_of_contract [Fintype α]
    {G : Graph α β} {W : Set α} {r : α} (hW : W ⊆ V(G)) {q : α × Fin 2 → K} {t : K}
    {x : α ⊕ (α × Fin 3) → K}
    (hx : (G.contractLiftingMatrix K W r q).map (MvPolynomial.eval (fun _ => t)) *ᵥ x = 0) :
    Graph.liftingRestrict W (fun w => x (Sum.inl w)) ∈ (G.induce W).liftingSpace q := by
  obtain ⟨-, h2, -⟩ := Graph.contractLiftingMatrix_mulVec_eq_zero_iff.mp hx
  refine ⟨fun w hw => by simp [Graph.liftingRestrict_apply, show w ∉ W from hw], fun c hc => ?_⟩
  refine ⟨fun i => x (Sum.inr (c, i)), fun w hw => ?_⟩
  have hwW : w ∈ W := Graph.closedNbhd_subset_vertexSet (G := G.induce W) hc hw
  rw [Graph.liftingRestrict_apply, ite_eq_left hwW,
    h2 c (hW hc) w (Graph.closedNbhd_induce_subset hw), Graph.contractWeightAt_of_mem hwW]

/-- **`ρ`**: the restriction of the unknowns of `M(t)` to the core heights, `x ↦ (x_w)_{w ∈ W}`
(`lem:pencil-contract-kernel-bound`). -/
noncomputable def contractCoreRestrict (W : Set α) :
    (α ⊕ (α × Fin 3) → K) →ₗ[K] (α → K) :=
  Graph.liftingRestrict W ∘ₗ LinearMap.funLeft K K Sum.inl

/-- Unfolding `contractCoreRestrict`. -/
theorem contractCoreRestrict_apply (W : Set α) (x : α ⊕ (α × Fin 3) → K) :
    contractCoreRestrict W x = Graph.liftingRestrict W (fun w => x (Sum.inl w)) := rfl

/-- **The kernel of `M(0)` at any core** (`lem:pencil-contract-kernel-bound` (2); (MC-69)(a)'s
upper bound, the general form of `Graph.finrank_ker_contractLiftingMatrix_zero_le`
(`Contract.lean`), which needs a flat core). With `q` admissible for `H = G[W]` and for `G/H`,
`dim ker M(0) + 3 ≤ dim ρ(ker M(0)) + dim L_{G/H}(q)`. A solution with zero core heights has zero
core planes (admissibility at `H`), so the limit map (`Graph.contractLimitMap_mem_liftingSpace`,
`Graph.eq_zero_of_contractLimitMap_eq_zero`, given the zero plane) embeds those solutions
injectively into `L_{G/H}(q)`, with image in the heights vanishing on the closed neighbourhood of
`r`, which meet `Aff(q)` only in `0`; rank–nullity on `ρ` restricted to `ker M(0)` gives the
bound. -/
theorem _root_.Graph.finrank_ker_contractLiftingMatrix_zero_add_three_le [Fintype α]
    {G : Graph α β} {W : Set α} {r : α} (hr : r ∈ W) (hW : W ⊆ V(G)) {q : α × Fin 2 → K}
    (hqH : (G.induce W).IsAdmissiblePicture q)
    (hqc : (G.rigidContract (G.induce W) r).IsAdmissiblePicture q) :
    Module.finrank K (LinearMap.ker ((G.contractLiftingMatrix K W r q).map
        (MvPolynomial.eval (fun _ => (0 : K)))).mulVecLin) + 3 ≤
      Module.finrank K ((LinearMap.ker ((G.contractLiftingMatrix K W r q).map
          (MvPolynomial.eval (fun _ => (0 : K)))).mulVecLin).map (contractCoreRestrict W)) +
        Module.finrank K ((G.rigidContract (G.induce W) r).liftingSpace q) := by
  set L := LinearMap.ker ((G.contractLiftingMatrix K W r q).map
    (MvPolynomial.eval (fun _ => (0 : K)))).mulVecLin with hL
  set Gc := G.rigidContract (G.induce W) r with hGc
  have hrVc : r ∈ V(Gc) := (Graph.mem_vertexSet_rigidContract_iff hr hW).mpr (Or.inl rfl)
  -- a solution with zero core heights has zero core planes
  have hplane : ∀ x ∈ L, contractCoreRestrict W x = 0 →
      (∀ w ∈ W, x (Sum.inl w) = (0 : Fin 3 → K) ⬝ᵥ pencilPicturePoint q w) ∧
        ∀ c ∈ W, (fun i => x (Sum.inr (c, i))) = 0 := by
    intro x hx h0
    have hxW : ∀ w ∈ W, x (Sum.inl w) = 0 := fun w hw => by
      have := congr_fun h0 w
      rwa [contractCoreRestrict_apply, Graph.liftingRestrict_apply, ite_eq_left hw] at this
    obtain ⟨-, h2, -⟩ := Graph.contractLiftingMatrix_mulVec_eq_zero_iff.mp hx
    refine ⟨fun w hw => by rw [hxW w hw, zero_dotProduct], fun c hc => ?_⟩
    refine hqH.eq_zero_of_forall_closedNbhd hc fun w hw => ?_
    have hwW : w ∈ W := Graph.closedNbhd_subset_vertexSet (G := G.induce W) hc hw
    have := h2 c (hW hc) w (Graph.closedNbhd_induce_subset hw)
    rw [Graph.contractWeightAt_of_mem hwW, hxW w hwW] at this
    exact this.symm
  -- and its limit heights vanish on the closed neighbourhood of `r` in `G/H`
  have hvan : ∀ x ∈ L, contractCoreRestrict W x = 0 →
      ∀ w' ∈ Gc.closedNbhd r, contractLimitMap G W r x w' = 0 := by
    intro x hx h0 w' hw'
    obtain ⟨hxW, hxc⟩ := hplane x hx h0
    obtain ⟨-, h2, -⟩ := Graph.contractLiftingMatrix_mulVec_eq_zero_iff.mp hx
    have hxr : x (Sum.inl r) = 0 := by rw [hxW r hr, zero_dotProduct]
    rcases Graph.mem_closedNbhd_rigidContract hw' with rfl | ⟨e, a, b, hab, hnot, ha, rfl⟩
    · rw [contractLimitMap_apply, ite_eq_left rfl, hxr]
    · have haW : a ∈ W := mem_of_collapseTo_eq hr ha.symm
      have hbW : b ∉ W := fun hb => hnot ⟨haW, hb⟩
      rw [collapseTo_of_not_mem hbW]
      have hrow := h2 a hab.left_mem b (Or.inr ⟨e, hab⟩)
      rw [hxc a haW] at hrow
      have hbr : b ≠ r := fun h => hbW (h ▸ hr)
      rw [contractLimitMap_apply, ite_eq_right hbr, ite_eq_left ⟨hab.right_mem, hbW⟩, hrow, hxr,
        zero_dotProduct, add_zero]
  -- rank–nullity on `ρ` restricted to `L`
  set ρL := (contractCoreRestrict (K := K) W).domRestrict L with hρL
  have hrn := LinearMap.finrank_range_add_finrank_ker ρL
  have hrange : LinearMap.range ρL = L.map (contractCoreRestrict W) :=
    LinearMap.range_domRestrict _ _
  set N : Submodule K (α ⊕ (α × Fin 3) → K) := L ⊓ LinearMap.ker (contractCoreRestrict W)
    with hN
  have hkerN : Module.finrank K (LinearMap.ker ρL) = Module.finrank K N := by
    rw [← Submodule.finrank_map_subtype_eq, hρL, LinearMap.ker_domRestrict,
      Submodule.map_comap_subtype]
  -- the limit map on `N`
  set Ψ : N →ₗ[K] (α → K) := (contractLimitMap (K := K) G W r).domRestrict N with hΨ
  have hNmem : ∀ y : N, (y : α ⊕ (α × Fin 3) → K) ∈ L ∧
      contractCoreRestrict W (y : α ⊕ (α × Fin 3) → K) = 0 :=
    fun y => ⟨y.2.1, LinearMap.mem_ker.mp y.2.2⟩
  have hΨinj : Function.Injective Ψ := by
    refine LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun y hy => ?_)
    obtain ⟨hyL, hy0⟩ := hNmem y
    obtain ⟨hxW, hxc⟩ := hplane _ hyL hy0
    exact Subtype.ext
      (Graph.eq_zero_of_contractLimitMap_eq_zero hr hW hqc hyL ⟨0, hxW, hxc⟩ hy)
  have hΨL : LinearMap.range Ψ ≤ Gc.liftingSpace q := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨hyL, hy0⟩ := hNmem y
    obtain ⟨hxW, hxc⟩ := hplane _ hyL hy0
    exact Graph.contractLimitMap_mem_liftingSpace hr hW hyL ⟨0, hxW, hxc⟩
  have hΨA : LinearMap.range Ψ ⊓ Gc.affineLifts q = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨⟨y, rfl⟩, ⟨g', hg'⟩⟩
    obtain ⟨hyL, hy0⟩ := hNmem y
    have hg'0 : g' = 0 := by
      refine hqc.eq_zero_of_forall_closedNbhd hrVc fun w' hw' => ?_
      have h1 := congr_fun hg' w'
      have hw'V : w' ∈ V(Gc) := Graph.closedNbhd_subset_vertexSet hrVc hw'
      rw [Graph.affineLiftMap_apply, ite_eq_left hw'V] at h1
      rw [h1]
      exact hvan _ hyL hy0 w' hw'
    rw [Submodule.mem_bot, ← hg', hg'0, map_zero]
  have hfin := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range Ψ) (Gc.affineLifts q)
  rw [hΨA, finrank_bot, add_zero, Graph.finrank_affineLifts hqc ⟨r, hrVc⟩,
    LinearMap.finrank_range_of_inj hΨinj] at hfin
  have hsup : Module.finrank K ↥(LinearMap.range Ψ ⊔ Gc.affineLifts q) ≤
      Module.finrank K (Gc.liftingSpace q) :=
    Submodule.finrank_mono (sup_le hΨL (Gc.affineLifts_le_liftingSpace q))
  rw [hrange, hkerN] at hrn
  omega

/-! ## The surviving rows near the collapsed placement -/

/-- **The surviving rows near the collapsed placement** (`lem:pencil-contract-degenerate-rank`;
(MC-36)'s limit in the projected form of Phase 22i; KT eqs. (6.5)/(6.9)). If the contraction
`G/H` (`H = G[W]`, representative `r`) has rank `≥ N` at the normals `nrm`, with every hinge
nonzero, then a polynomial `Qc` in the normals of `G` is nonzero at the collapsed placement
`degeneratePlacement r W nrm` (every core body at `r`'s normal) and, off its zero set, the rows of
`G − E(H)` with the core columns deleted have rank `≥ N`. At the collapsed placement those rows are
the rows of `G/H` with `r`'s column deleted (`panelRow_collapseTo_comp_extProj_dualMap`), which
loses no rank; `exists_rankPolynomial_of_rigidOn_linking_set_proj_eval` keeps the value there. -/
theorem PanelHingeFramework.exists_rankPolynomial_rigidContract_induce_proj [Finite α]
    [Finite β] (G : Graph α β) {W : Set α} {r : α} (hr : r ∈ W) (hW : W ⊆ V(G))
    (ends : β → α × α)
    (hends : ∀ e u v, (G.deleteEdges E(G.induce W)).IsLink e u v →
      (G.deleteEdges E(G.induce W)).IsLink e (ends e).1 (ends e).2)
    (nrm : α → Fin (k + 2) → K)
    (hne : ∀ e, (G.rigidContract (G.induce W) r).IsLink e
        (Graph.collapseTo r W (ends e).1) (Graph.collapseTo r W (ends e).2) →
      (PanelHingeFramework.ofNormals (G.rigidContract (G.induce W) r)
        (fun e => (Graph.collapseTo r W (ends e).1, Graph.collapseTo r W (ends e).2))
        (fun p => nrm p.1 p.2)).toBodyHinge.supportExtensor e ≠ 0)
    {N : ℕ}
    (hN : N ≤ Module.finrank K (Submodule.span K
      (PanelHingeFramework.ofNormals (G.rigidContract (G.induce W) r)
        (fun e => (Graph.collapseTo r W (ends e).1, Graph.collapseTo r W (ends e).2))
        (fun p => nrm p.1 p.2)).toBodyHinge.rigidityRows)) :
    ∃ Qc : MvPolynomial (α × Fin (k + 2)) K,
      MvPolynomial.eval (degeneratePlacement r W nrm) Qc ≠ 0 ∧
      ∀ q, MvPolynomial.eval q Qc ≠ 0 →
        N ≤ Module.finrank K ((Submodule.span K
          (PanelHingeFramework.ofNormals (G.deleteEdges E(G.induce W)) ends
            q).toBodyHinge.rigidityRows).map (extProj (K := K) (k := k) W).dualMap) := by
  set Gc := G.deleteEdges E(G.induce W) with hGc
  set f := Graph.collapseTo r W with hf
  set endsM : β → α × α := fun e => (f (ends e).1, f (ends e).2) with hendsM
  have hGcf : G.rigidContract (G.induce W) r = Gc.map f := rfl
  rw [hGcf] at hne hN
  set F' := (PanelHingeFramework.ofNormals (Gc.map f) endsM
    (fun p => nrm p.1 p.2)).toBodyHinge with hF'
  have hendsF' : ∀ e u v, F'.graph.IsLink e u v → F'.graph.IsLink e (endsM e).1 (endsM e).2 := by
    intro e u v hlink
    rw [hF', PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph,
      Graph.map_isLink] at hlink ⊢
    obtain ⟨x, y, hxy, _, _⟩ := hlink
    exact ⟨_, _, hends e x y hxy, rfl, rfl⟩
  have hinter : F'.graph.vertexSet ∩ W = {r} :=
    Graph.rigidContract_vertexSet_inter_eq_singleton G (G.induce W) hr hW
  obtain ⟨t, hsuppM, hcountM, hindepM⟩ :=
    F'.exists_independent_panelRow_subfamily_of_le_finrank_proj (ends := endsM) (proj := W)
      (r := r) hendsF' hne hinter hN
  have hsupp₀ : ∀ i ∈ t, Gc.IsLink (i : β × _ × _).1 (ends (i : β × _ × _).1).1
      (ends (i : β × _ × _).1).2 := by
    intro i hi
    have := hsuppM i hi
    rw [hF', PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph,
      Graph.map_isLink] at this
    obtain ⟨x, y, hxy, _, _⟩ := this
    exact hends i.1 x y hxy
  have hVH : V(G.induce W) = W := rfl
  have hindep₀ : LinearIndependent K (fun i : t => (extProj (k := k) W).dualMap
      ((PanelHingeFramework.ofNormals Gc ends (degeneratePlacement r W nrm)).toBodyHinge.panelRow
        ends (i : β × _ × _))) := by
    have hrow : (fun i : t => (extProj (k := k) W).dualMap
        ((PanelHingeFramework.ofNormals Gc ends
          (degeneratePlacement r W nrm)).toBodyHinge.panelRow ends (i : β × _ × _)))
        = (fun i : t => (extProj (k := k) W).dualMap (F'.panelRow endsM (i : β × _ × _))) := by
      funext i
      have h := panelRow_collapseTo_comp_extProj_dualMap Gc (G.induce W) hr nrm ends
        (i : β × _ × _)
      rw [hVH] at h
      rw [h]
    rw [hrow]
    exact hindepM
  obtain ⟨Qc, hQc₀, hQc⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking_set_proj_eval Gc ends W
      hsupp₀ hcountM hindep₀
  refine ⟨Qc, hQc₀, fun q hq => ?_⟩
  obtain ⟨rsc, hrsc, hcard, hli⟩ := hQc q hq
  have : Fintype rsc := Fintype.ofFinite _
  have hmem : ∀ i : rsc, (extProj (K := K) (k := k) W).dualMap
      ((PanelHingeFramework.ofNormals Gc ends q).toBodyHinge.panelRow ends (i : β × _ × _)) ∈
      (Submodule.span K (PanelHingeFramework.ofNormals Gc ends q).toBodyHinge.rigidityRows).map
        (extProj (K := K) (k := k) W).dualMap := by
    intro i
    exact Submodule.mem_map_of_mem (Submodule.subset_span
      (BodyHingeFramework.panelRow_mem_rigidityRows _ (hrsc i i.2)))
  calc N ≤ Nat.card rsc := hcard
    _ = Fintype.card rsc := Nat.card_eq_fintype_card
    _ = _ := (finrank_span_eq_card hli).symm
    _ ≤ _ := Submodule.finrank_mono (Submodule.span_le.mpr (by
        rintro _ ⟨i, rfl⟩
        exact hmem i))

/-! ## The standing hypotheses at a rigid core -/

/-- **A rigid core satisfies the standing hypotheses, at any `n`**
(`lem:pencil-contract-standing-rigid`; Phase 40k CONTRACT-A, the `n`-general form of
`Graph.isX0Graph_induce_of_deficiency_two_eq_zero` (`Contract.lean`), which needs `n = 2`). -/
theorem _root_.Graph.isX0Graph_induce_of_deficiency_eq_zero [Finite α] [Finite β]
    {G : Graph α β} (hS : G.Simple) {W : Set α} (hW : W ⊆ V(G)) (hW2 : 2 ≤ W.ncard) {n : ℕ}
    (hn : 1 ≤ Graph.bodyBarDim n) (hdef : (G.induce W).deficiency n = 0) :
    (G.induce W).IsX0Graph where
  simple := hS.mono (Graph.induce_le hW)
  connected := Graph.connected_of_isKDof_zero hn hdef
    (Set.nonempty_of_ncard_ne_zero (s := W) (by omega))
  two_le_degree := fun _ hv => Graph.two_le_degree_of_isKDof_zero hn hdef hv hW2

/-! ## The standing hypotheses at the contraction -/

/-- **`G/H` is simple** (`lem:pencil-contract-standing`; the STEPS recon's compiled lemma,
`notes/Phase40-design.md` appendix): if `G` is simple and no body outside `W` is adjacent to two
core bodies, `G.rigidContract (G.induce W) r` is simple. A surviving edge is not inside `W`, so it
is not a loop; two surviving edges with the same collapsed ends give an attachment two core
neighbours, or are parallel in `G`. -/
theorem _root_.Graph.rigidContract_induce_simple {G : Graph α β} (hS : G.Simple) {W : Set α}
    {r : α} (hr : r ∈ W)
    (hatt : ∀ u ∉ W, ∀ c₁ ∈ W, ∀ c₂ ∈ W, G.Adj u c₁ → G.Adj u c₂ → c₁ = c₂) :
    (G.rigidContract (G.induce W) r).Simple := by
  classical
  have hV : V(G.induce W) = W := rfl
  -- a surviving edge never has both ends in `W`
  have hsurv : ∀ e x y, (G.deleteEdges E(G.induce W)).IsLink e x y →
      G.IsLink e x y ∧ ¬ (x ∈ W ∧ y ∈ W) := by
    intro e x y h
    rw [Graph.deleteEdges_isLink] at h
    refine ⟨h.1, fun ⟨hx, hy⟩ => h.2 ?_⟩
    exact (show (G.induce W).IsLink e x y from ⟨h.1, hx, hy⟩).edge_mem
  have hcol : ∀ x, Graph.collapseTo r W x = if x ∈ W then r else x := fun _ => rfl
  -- the collapse is the identity off `W` and sends `W` to `r ∈ W`
  have hout : ∀ {a b : α}, b ∉ W → Graph.collapseTo r W a = b → a ∉ W ∧ a = b := by
    intro a b hb h
    rw [hcol] at h
    by_cases ha : a ∈ W
    · rw [ite_eq_left ha] at h; exact absurd (h ▸ hr) hb
    · rw [ite_eq_right ha] at h; exact ⟨ha, h⟩
  have hin : ∀ {a : α}, Graph.collapseTo r W a = r → a ∈ W := by
    intro a h
    rw [hcol] at h
    by_cases ha : a ∈ W
    · exact ha
    · rw [ite_eq_right ha] at h; exact h ▸ hr
  have hcolW : ∀ {a : α}, a ∈ W → Graph.collapseTo r W a = r := by
    intro a ha; rw [hcol, ite_eq_left ha]
  have hcolO : ∀ {a : α}, a ∉ W → Graph.collapseTo r W a = a := by
    intro a ha; rw [hcol, ite_eq_right ha]
  refine Graph.rigidContract_simple (fun e x y h hxy => ?_)
    (fun e₁ e₂ x₁ y₁ x₂ y₂ h₁ h₂ hx hy => ?_)
  · obtain ⟨hl, hnW⟩ := hsurv e x y h
    rw [hV] at hxy
    by_cases hx : x ∈ W <;> by_cases hy : y ∈ W
    · exact hnW ⟨hx, hy⟩
    · rw [hcolW hx, hcolO hy] at hxy; exact hy (hxy ▸ hr)
    · rw [hcolO hx, hcolW hy] at hxy; exact hx (hxy ▸ hr)
    · rw [hcolO hx, hcolO hy] at hxy
      subst hxy
      exact hS.toLoopless.not_isLoopAt e x hl
  · obtain ⟨hl₁, hn₁⟩ := hsurv e₁ x₁ y₁ h₁
    obtain ⟨hl₂, hn₂⟩ := hsurv e₂ x₂ y₂ h₂
    rw [hV] at hx hy
    -- one end outside `W` pins the other edge's end there too
    have key : ∀ {a b c : α}, a ∈ W → b ∉ W → c ∈ W → G.IsLink e₁ a b → G.IsLink e₂ c b →
        e₁ = e₂ := by
      intro a b c ha hb hc h1 h2
      have := hatt b hb a ha c hc ⟨e₁, h1.symm⟩ ⟨e₂, h2.symm⟩
      subst this
      exact hS.eq_of_isLink h1 h2
    by_cases hx₁ : x₁ ∈ W
    · have hy₁ : y₁ ∉ W := fun h => hn₁ ⟨hx₁, h⟩
      rw [hcolW hx₁] at hx
      rw [hcolO hy₁] at hy
      have hx₂ := hin hx.symm
      obtain ⟨-, rfl⟩ := hout hy₁ hy.symm
      exact key hx₁ hy₁ hx₂ hl₁ hl₂
    · rw [hcolO hx₁] at hx
      obtain ⟨hx₂, rfl⟩ := hout hx₁ hx.symm
      by_cases hy₁ : y₁ ∈ W
      · rw [hcolW hy₁] at hy
        have hy₂ := hin hy.symm
        exact key hy₁ hx₁ hy₂ hl₁.symm hl₂.symm
      · rw [hcolO hy₁] at hy
        obtain ⟨-, rfl⟩ := hout hy₁ hy.symm
        exact hS.eq_of_isLink hl₁ hl₂

/-- **Every closed neighbourhood of `G/H` has three members** (`lem:pencil-contract-standing`, `h3`
at `G/H`). At `r`: `G` is 2-edge-connected, so two edges leave `W`, and their outside ends are
distinct attachments. At a body outside `W`: the collapse is injective on its closed neighbourhood
in `G` (`hatt`) and maps it into the closed neighbourhood in `G/H`. -/
theorem _root_.Graph.three_le_ncard_closedNbhd_rigidContract [Finite α] [Finite β]
    {G : Graph α β} (hG : G.IsX0Graph) (htec : G.TwoEdgeConnected) {W : Set α} {r : α}
    (hr : r ∈ W) (hWss : W ⊂ V(G))
    (hatt : ∀ u ∉ W, ∀ c₁ ∈ W, ∀ c₂ ∈ W, G.Adj u c₁ → G.Adj u c₂ → c₁ = c₂) :
    ∀ v ∈ V(G.rigidContract (G.induce W) r),
      3 ≤ ((G.rigidContract (G.induce W) r).closedNbhd v).ncard := by
  have hW : W ⊆ V(G) := hWss.subset
  intro v hv
  rw [Graph.mem_vertexSet_rigidContract_iff hr hW] at hv
  rcases hv with rfl | ⟨hvG, hvW⟩
  · -- two cut edges with distinct outside ends
    have hcut := htec W ⟨v, hr⟩ hWss
    obtain ⟨e₁, e₂, he₁, he₂, hne⟩ :=
      (Set.one_lt_ncard_iff (s := G.cutEdges W) (Set.toFinite _)).mp (by omega)
    obtain ⟨-, c₁, u₁, hl₁, hc₁, hu₁⟩ := he₁
    obtain ⟨-, c₂, u₂, hl₂, hc₂, hu₂⟩ := he₂
    have hu : u₁ ≠ u₂ := by
      rintro rfl
      have := hatt u₁ hu₁ c₁ hc₁ c₂ hc₂ ⟨e₁, hl₁.symm⟩ ⟨e₂, hl₂.symm⟩
      subst this
      exact hne (hG.simple.eq_of_isLink hl₁ hl₂)
    have hmem : ∀ {c u e}, c ∈ W → u ∉ W → G.IsLink e c u →
        u ∈ (G.rigidContract (G.induce W) v).closedNbhd v := by
      intro c u e hc hu hl
      have := Graph.collapseTo_mem_closedNbhd_rigidContract (r := v) (W := W)
        (Or.inr ⟨e, hl⟩ : u ∈ G.closedNbhd c) (fun h => hu h.2)
      rwa [collapseTo_of_not_mem hu, collapseTo_of_mem hc] at this
    have := (Set.two_lt_ncard_iff (Set.toFinite _)).mpr ⟨v, u₁, u₂, Or.inl rfl,
      hmem hc₁ hu₁ hl₁, hmem hc₂ hu₂ hl₂, fun h => hu₁ (h ▸ hr), fun h => hu₂ (h ▸ hr), hu⟩
    omega
  · -- the collapse is injective on `N_G[v]` and maps it into `N_{G/H}[v]`
    have h3 := hG.three_le_ncard_closedNbhd v hvG
    have hinj : Set.InjOn (Graph.collapseTo r W) (G.closedNbhd v) := by
      intro a ha b hb hab
      have hadj : ∀ {c}, c ∈ G.closedNbhd v → c ∈ W → G.Adj v c := by
        intro c hc hcW
        rcases hc with rfl | ⟨e, he⟩
        · exact absurd hcW hvW
        · exact ⟨e, he⟩
      by_cases haW : a ∈ W <;> by_cases hbW : b ∈ W
      · exact hatt v hvW a haW b hbW (hadj ha haW) (hadj hb hbW)
      · rw [collapseTo_of_mem haW, collapseTo_of_not_mem hbW] at hab
        exact absurd (hab ▸ hr) hbW
      · rw [collapseTo_of_not_mem haW, collapseTo_of_mem hbW] at hab
        exact absurd (hab ▸ hr) haW
      · rwa [collapseTo_of_not_mem haW, collapseTo_of_not_mem hbW] at hab
    have hsub : Graph.collapseTo r W '' G.closedNbhd v ⊆
        (G.rigidContract (G.induce W) r).closedNbhd v := by
      rintro _ ⟨w, hw, rfl⟩
      have := Graph.collapseTo_mem_closedNbhd_rigidContract (r := r) hw (fun h => hvW h.1)
      rwa [collapseTo_of_not_mem hvW] at this
    calc 3 ≤ (G.closedNbhd v).ncard := h3
      _ = (Graph.collapseTo r W '' G.closedNbhd v).ncard := hinj.ncard_image.symm
      _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)

/-- The contraction of a connected graph at an induced core is connected: a walk of `G` collapses to
a walk of `G/H`. -/
theorem _root_.Graph.connected_rigidContract_induce {G : Graph α β} (hG : G.Connected)
    {W : Set α} {r : α} : (G.rigidContract (G.induce W) r).Connected := by
  obtain ⟨⟨v, hv⟩, hpre⟩ := Graph.connected_iff.mp hG
  refine Graph.connected_iff.mpr ⟨⟨_, ⟨v, hv, rfl⟩⟩, ?_⟩
  rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
  have hab := (Graph.connBetween_iff_reflTransGen_adj.mp (hpre a b ha hb)).2
  refine Graph.connBetween_iff_reflTransGen_adj.mpr ⟨⟨a, ha, rfl⟩, ?_⟩
  clear hb
  induction hab with
  | refl => exact .refl
  | @tail c d _ hcd ih =>
    obtain ⟨e, he⟩ := hcd
    by_cases hboth : c ∈ W ∧ d ∈ W
    · have hcd' : Graph.collapseTo r V(G.induce W) c = Graph.collapseTo r V(G.induce W) d := by
        rw [Graph.vertexSet_induce, collapseTo_of_mem hboth.1, collapseTo_of_mem hboth.2]
      rw [← hcd']
      exact ih
    · exact ih.tail ⟨e, Graph.isLink_rigidContract_of_isLink he hboth⟩

/-- **`G/H` satisfies the standing hypotheses** (`lem:pencil-contract-standing`; (MC-39)'s side
claim): simple (`Graph.rigidContract_induce_simple`), connected, and of minimum degree at least two,
from three members in every closed neighbourhood. -/
theorem _root_.Graph.isX0Graph_rigidContract_induce [Finite α] [Finite β] {G : Graph α β}
    (hG : G.IsX0Graph) (htec : G.TwoEdgeConnected) {W : Set α} {r : α} (hr : r ∈ W)
    (hWss : W ⊂ V(G))
    (hatt : ∀ u ∉ W, ∀ c₁ ∈ W, ∀ c₂ ∈ W, G.Adj u c₁ → G.Adj u c₂ → c₁ = c₂) :
    (G.rigidContract (G.induce W) r).IsX0Graph where
  simple := Graph.rigidContract_induce_simple hG.simple hr hatt
  connected := Graph.connected_rigidContract_induce hG.connected
  two_le_degree := fun v hv => by
    have hS := Graph.rigidContract_induce_simple hG.simple hr hatt
    have h3 := Graph.three_le_ncard_closedNbhd_rigidContract hG htec hr hWss hatt v hv
    have hnot : v ∉ N(G.rigidContract (G.induce W) r, v) := fun h => by
      obtain ⟨e, he⟩ := h
      exact hS.toLoopless.not_isLoopAt e v he
    have heq : (G.rigidContract (G.induce W) r).closedNbhd v =
        insert v (N(G.rigidContract (G.induce W) r, v)) := rfl
    rw [heq, Set.ncard_insert_of_notMem hnot (Set.toFinite _)] at h3
    rw [Graph.degree_eq_ncard_adj]
    omega

/-! ## The curve as polynomials in `t` -/

open Classical in
/-- The contraction curve as polynomials in `t` (`eval_contractPicturePoly`). -/
noncomputable def contractPicturePoly (W : Set α) (r : α) (q : α × Fin 2 → K) :
    α × Fin 2 → MvPolynomial Unit K :=
  fun p => if p.1 ∈ W then
    MvPolynomial.C (q (r, p.2)) + MvPolynomial.X () * MvPolynomial.C (q p - q (r, p.2))
  else MvPolynomial.C (q p)

/-- Evaluating the polynomial curve at `t` gives `contractPicture` at `t`. -/
theorem eval_contractPicturePoly (W : Set α) (r : α) (q : α × Fin 2 → K) (t : K)
    (p : α × Fin 2) :
    MvPolynomial.eval (fun _ => t) (contractPicturePoly W r q p) = contractPicture W r q t p := by
  unfold contractPicturePoly contractPicture
  split_ifs <;> simp
  ring

open Classical in
/-- The configuration along the curve as polynomials in `t`: the polynomial curve, and the heights
`contractHeight` of a polynomial family `Z` of unknowns of `M(t)` (`eval_contractConfigPoly`). -/
noncomputable def contractConfigPoly (W : Set α) (r : α) (q : α × Fin 2 → K)
    (Z : α ⊕ (α × Fin 3) → MvPolynomial Unit K) : α × Fin 4 → MvPolynomial Unit K :=
  fun p => ![contractPicturePoly W r q (p.1, 0), contractPicturePoly W r q (p.1, 1),
    if p.1 ∈ W then MvPolynomial.X () * Z (Sum.inl p.1) else Z (Sum.inl p.1), 1] p.2

/-- Evaluating the polynomial configuration at `t` gives the configuration point at
`(q(t), z(t))`. -/
theorem eval_contractConfigPoly (W : Set α) (r : α) (q : α × Fin 2 → K)
    (Z : α ⊕ (α × Fin 3) → MvPolynomial Unit K) (t : K) :
    (fun p => MvPolynomial.eval (fun _ => t) (contractConfigPoly W r q Z p)) =
      fun p => pencilConfigPoint (contractPicture W r q t)
        (contractHeight W t (fun c => MvPolynomial.eval (fun _ => t) (Z c))) p.1 p.2 := by
  funext ⟨w, i⟩
  fin_cases i
  · simp [contractConfigPoly, pencilConfigPoint, eval_contractPicturePoly]
  · simp [contractConfigPoly, pencilConfigPoint, eval_contractPicturePoly]
  · by_cases hw : w ∈ W <;> simp [contractConfigPoly, pencilConfigPoint, contractHeight_apply, hw]
  · simp [contractConfigPoly, pencilConfigPoint]

end CombinatorialRigidity.Molecular
