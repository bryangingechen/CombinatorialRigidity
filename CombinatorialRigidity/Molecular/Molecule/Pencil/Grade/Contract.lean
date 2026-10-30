/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Carrier
public import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.ContractCurve

/-!
# The core's rank along the contraction curve, in every dimension

`lem:pencil-d-contract-magnified-rank` (`blueprint/src/chapter/pencil-d.tex`): the rank of the core
`H = G[W]` at the configuration `(q(t), z(t))` with `m` heights is its rank at `(q, z)`, the form at
grade `m + 1` of `Graph.finrank_span_rigidityRows_induce_contractHeight_eq`
(`MainComponent/ContractCurve.lean`).

## Main results

* `Graph.finrank_span_rigidityRows_induce_contractHeightGrade_eq`: the rank is the same along the
  curve.
-/

@[expose] public section

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*} {m : ℕ}

/-- **The core's rank along the curve, in every dimension**
(`lem:pencil-d-contract-magnified-rank`): at `t ≠ 0`, with one vector of unknowns `x i` of the
rescaled lifting system for each of the `m` heights, the configuration of `H = G[W]` at
`(q(t), z(t))`, where `z(t)` has the heights `contractHeight W t (x i)`, has the row rank of its
configuration at `(q, z)`, `z` the core heights of the unknowns before the scaling by `t`. The
collineation `(ξ, η, ζ, ω) ↦ (t ξ + (1 − t) x_r ω, t η + (1 − t) y_r ω, t ζ, ω)` of `K^(m+3)`,
invertible as `t ≠ 0`, takes the first to the second at every body of `W`, and
`PanelHingeFramework.finrank_span_rigidityRows_ofNormals_linearEquiv_grade` applies. -/
theorem _root_.Graph.finrank_span_rigidityRows_induce_contractHeightGrade_eq {G : Graph α β}
    {W : Set α} {r : α} (q : α × Fin 2 → K) {t : K} (ht : t ≠ 0)
    (x : Fin m → α ⊕ (α × Fin 3) → K) {ends : β → α × α}
    (hends : ∀ e u v, (G.induce W).IsLink e u v → (G.induce W).IsLink e (ends e).1 (ends e).2) :
    Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := m + 1) (G.induce W)
        ends (fun p => pencilConfigPointGrade (contractPicture W r q t)
          (fun p => contractHeight W t (x p.2) p.1) p.1 p.2)).toBodyHinge.rigidityRows)
      = Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := m + 1)
        (G.induce W) ends (fun p => pencilConfigPointGrade q
          (fun p => x p.2 (Sum.inl p.1)) p.1 p.2)).toBodyHinge.rigidityRows) := by
  let f : (Fin (m + 1 + 2) → K) →ₗ[K] (Fin (m + 1 + 2) → K) :=
    { toFun := fun b => gradeMk (t * b 0 + (1 - t) * q (r, 0) * b (Fin.last (m + 2)))
        (t * b 1 + (1 - t) * q (r, 1) * b (Fin.last (m + 2))) (t • gradeHeights b)
        (b (Fin.last (m + 2)))
      map_add' := fun b c => by
        rw [gradeMk_add]
        refine gradeMk_ext ?_ ?_ ?_ ?_
        · simp only [Pi.add_apply]; ring
        · simp only [Pi.add_apply]; ring
        · rw [gradeHeights_add, smul_add]
        · rfl
      map_smul' := fun c b => by
        rw [RingHom.id_apply, gradeMk_smul]
        refine gradeMk_ext ?_ ?_ ?_ ?_
        · simp only [Pi.smul_apply, smul_eq_mul]; ring
        · simp only [Pi.smul_apply, smul_eq_mul]; ring
        · rw [gradeHeights_smul, smul_comm]
        · rfl }
  let f' : (Fin (m + 1 + 2) → K) →ₗ[K] (Fin (m + 1 + 2) → K) :=
    { toFun := fun b => gradeMk
        (t⁻¹ * (b 0 - (1 - t) * q (r, 0) * b (Fin.last (m + 2))))
        (t⁻¹ * (b 1 - (1 - t) * q (r, 1) * b (Fin.last (m + 2)))) (t⁻¹ • gradeHeights b)
        (b (Fin.last (m + 2)))
      map_add' := fun b c => by
        rw [gradeMk_add]
        refine gradeMk_ext ?_ ?_ ?_ ?_
        · simp only [Pi.add_apply]; ring
        · simp only [Pi.add_apply]; ring
        · rw [gradeHeights_add, smul_add]
        · rfl
      map_smul' := fun c b => by
        rw [RingHom.id_apply, gradeMk_smul]
        refine gradeMk_ext ?_ ?_ ?_ ?_
        · simp only [Pi.smul_apply, smul_eq_mul]; ring
        · simp only [Pi.smul_apply, smul_eq_mul]; ring
        · rw [gradeHeights_smul, smul_comm]
        · rfl }
  have hf : ∀ b, f b = gradeMk (t * b 0 + (1 - t) * q (r, 0) * b (Fin.last (m + 2)))
        (t * b 1 + (1 - t) * q (r, 1) * b (Fin.last (m + 2))) (t • gradeHeights b)
        (b (Fin.last (m + 2))) := fun _ => rfl
  have hf' : ∀ b, f' b = gradeMk (t⁻¹ * (b 0 - (1 - t) * q (r, 0) * b (Fin.last (m + 2))))
        (t⁻¹ * (b 1 - (1 - t) * q (r, 1) * b (Fin.last (m + 2)))) (t⁻¹ • gradeHeights b)
        (b (Fin.last (m + 2))) := fun _ => rfl
  let g : (Fin (m + 1 + 2) → K) ≃ₗ[K] (Fin (m + 1 + 2) → K) := LinearEquiv.ofLinearMap f f'
    (LinearMap.ext fun b => by
      change f (f' b) = b
      conv_rhs => rw [gradeMk_eta b]
      simp only [hf, hf', gradeMk_apply_zero, gradeMk_apply_one, gradeMk_apply_last,
        gradeHeights_gradeMk]
      refine gradeMk_ext ?_ ?_ ?_ rfl
      · field_simp; ring
      · field_simp; ring
      · rw [smul_smul, mul_inv_cancel₀ ht, one_smul])
    (LinearMap.ext fun b => by
      change f' (f b) = b
      conv_rhs => rw [gradeMk_eta b]
      simp only [hf, hf', gradeMk_apply_zero, gradeMk_apply_one, gradeMk_apply_last,
        gradeHeights_gradeMk]
      refine gradeMk_ext ?_ ?_ ?_ rfl
      · field_simp; ring
      · field_simp; ring
      · rw [smul_smul, inv_mul_cancel₀ ht, one_smul])
  refine PanelHingeFramework.finrank_span_rigidityRows_ofNormals_linearEquiv_grade hends g
    (p := pencilConfigPointGrade q (fun p => x p.2 (Sum.inl p.1))) fun w hw => ?_
  have hwW : w ∈ W := hw
  rw [pencilConfigPointGrade_eq_gradeMk, pencilConfigPointGrade_eq_gradeMk]
  change gradeMk _ _ _ _ = _
  refine gradeMk_ext ?_ ?_ ?_ ?_
  · simp [contractPicture, hwW]; ring
  · simp [contractPicture, hwW]; ring
  · funext i
    simp [contractHeight_apply, hwW]
  · exact (gradeMk_apply_last _ _ _ _).symm

end CombinatorialRigidity.Molecular
