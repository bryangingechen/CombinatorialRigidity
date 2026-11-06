/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.GenericLift.HingeGeneric
public import CombinatorialRigidity.Molecular.MeetHyperplanes

/-!
# A collineation of the normals keeps the rank, at every grade

The first Lean of `sec:pencil-d` (`blueprint/src/chapter/pencil-d.tex`), whose statements the
directory `Pencil/Grade/` states at the grade `k` of the screw space `ScrewSpace K k`, in dimension
`d = k + 1`: `lem:pencil-d-rank-collineation`, the form at every grade of
`lem:pencil-rank-collineation`, which
`PanelHingeFramework.finrank_span_rigidityRows_ofNormals_linearEquiv` proves at `k = 2`
(`MainComponent/Configuration.lean`).

An invertible linear map `g` of `K^(k+2)` acts on the hinges of a panel-hinge framework through its
inverse transpose `h` (`contragredient`, here as a linear automorphism). The hinge
`panelSupportExtensor n₁ n₂` is the complement isomorphism of the join `n₁ ∨ n₂`, and the
transformation law of the complement isomorphism (`complementIso_map_contragredient_eq`) gives the
hinge at the normals `g n₁` and `g n₂` as `det g` times the screw map of `h`
(`BodyHingeFramework.screwEquivOfLinearEquiv`) applied to the hinge at `n₁` and `n₂`. So one
automorphism of the screw space carries every hinge, and it keeps the rank
(`BodyHingeFramework.finrank_span_rigidityRows_mapExtensor`). The proof at `k = 2` goes through the
point-join framework instead, and stays as it is.

## Main results

* `panelSupportExtensor_linearEquiv_eq_det_smul`: the hinge at the normals `g n₁` and `g n₂` is
  `det g` times the screw map of a contragredient of `g` applied to the hinge at `n₁` and `n₂`.
* `PanelHingeFramework.finrank_span_rigidityRows_ofNormals_linearEquiv_grade`:
  `lem:pencil-d-rank-collineation`.
-/

@[expose] public section

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {k : ℕ}
variable {α β : Type*}

/-- **A linear automorphism of the normals moves the hinge by one screw automorphism** (a step of
`lem:pencil-d-rank-collineation`): for a linear automorphism `g` of `K^(k+2)` and a contragredient
`h` of it (`⟨h x, g y⟩ = ⟨x, y⟩` for the coordinate pairing, as `contragredient_toDual_pairing`),
`panelSupportExtensor (g n₁) (g n₂) = det g • Λ_h (panelSupportExtensor n₁ n₂)`, where `Λ_h` is the
screw map of `h` (`def:induced-screw-map`). The join of `g n₁` and `g n₂` is the image of the join
of `n₁` and `n₂` under `⋀² g` (`exteriorPower_map_normalsJoin`), and the transformation law of the
complement isomorphism (`complementIso_map_contragredient_eq`) moves `⋀² g` across it as
`det g • ⋀^k h`, which is `Λ_h` on `ScrewSpace K k` by definition. -/
theorem panelSupportExtensor_linearEquiv_eq_det_smul
    (g h : (Fin (k + 2) → K) ≃ₗ[K] (Fin (k + 2) → K))
    (hgh : ∀ x y, (Pi.basisFun K (Fin (k + 2))).toDual (h x) (g y)
      = (Pi.basisFun K (Fin (k + 2))).toDual x y)
    (n₁ n₂ : Fin (k + 2) → K) :
    panelSupportExtensor (g n₁) (g n₂)
      = LinearMap.det (g : (Fin (k + 2) → K) →ₗ[K] (Fin (k + 2) → K))
          • BodyHingeFramework.screwEquivOfLinearEquiv h (panelSupportExtensor n₁ n₂) := by
  have hjoin : normalsJoin (g n₁) (g n₂)
      = exteriorPower.map 2 (g : (Fin (k + 2) → K) →ₗ[K] (Fin (k + 2) → K))
          (normalsJoin n₁ n₂) :=
    (exteriorPower_map_normalsJoin _ n₁ n₂).symm
  rw [panelSupportExtensor, hjoin,
    complementIso_map_contragredient_eq _ _ (h : (Fin (k + 2) → K) →ₗ[K] (Fin (k + 2) → K))
      g.surjective hgh]
  -- `⋀^(k+2-2) h` on the complement is the screw map of `h`: `k + 2 - 2` reduces to `k`, and the
  -- `ScrewSpace.equivExteriorPower` casts of `screwEquivOfLinearEquiv` are identities.
  rfl

/-- **A collineation of the normals preserves the rank, at every grade**
(`lem:pencil-d-rank-collineation`): if the panel normals `p'` are the images of `p` under one
invertible linear map `g` of `K^(k+2)` at every body of `G`, the panel-hinge frameworks with normals
`p` and with normals `p'` have the same row rank. Let `h` be the contragredient of `g`, the dual
map of `g⁻¹` read through the coordinate pairing (`contragredient`, as a linear automorphism). The
hinge at every link of the framework with normals `p'` is the image of the hinge with normals `p`
under the one automorphism `det g • Λ_h` of the screw space
(`panelSupportExtensor_linearEquiv_eq_det_smul`; `det g ≠ 0`), and an automorphism keeps the rank
(`BodyHingeFramework.finrank_span_rigidityRows_mapExtensor`). The form at `k = 2` is
`PanelHingeFramework.finrank_span_rigidityRows_ofNormals_linearEquiv`. -/
theorem PanelHingeFramework.finrank_span_rigidityRows_ofNormals_linearEquiv_grade
    {G : Graph α β} {ends : β → α × α}
    (hends : Graph.RecordsLinks G ends)
    (g : (Fin (k + 2) → K) ≃ₗ[K] (Fin (k + 2) → K)) {p p' : α → Fin (k + 2) → K}
    (hp : ∀ w ∈ V(G), p' w = g (p w)) :
    Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := k) G ends
        (fun x => p' x.1 x.2)).toBodyHinge.rigidityRows)
      = Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := k) G ends
        (fun x => p x.1 x.2)).toBodyHinge.rigidityRows) := by
  let h : (Fin (k + 2) → K) ≃ₗ[K] (Fin (k + 2) → K) := contragredientEquiv g
  have hdet : LinearMap.det (g : (Fin (k + 2) → K) →ₗ[K] (Fin (k + 2) → K)) ≠ 0 :=
    LinearEquiv.coe_det g ▸ (LinearEquiv.det g).ne_zero
  set M : ScrewSpace K k ≃ₗ[K] ScrewSpace K k :=
    (BodyHingeFramework.screwEquivOfLinearEquiv h).trans (LinearEquiv.smulOfNeZero K _ _ hdet)
  have hspan : Submodule.span K (PanelHingeFramework.ofNormals (k := k) G ends
        (fun x => p' x.1 x.2)).toBodyHinge.rigidityRows
      = Submodule.span K ((PanelHingeFramework.ofNormals (k := k) G ends
        (fun x => p x.1 x.2)).toBodyHinge.mapExtensor M).rigidityRows :=
    span_rigidityRows_eq_of_supportExtensor_agree _ _ rfl fun e u v he => by
      have h0 := hends.isLink he
      simp only [BodyHingeFramework.mapExtensor_supportExtensor,
        PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_normal,
        PanelHingeFramework.ofNormals_ends, hp _ h0.left_mem, hp _ h0.right_mem,
        panelSupportExtensor_linearEquiv_eq_det_smul g h (contragredient_toDual_pairing g), M,
        LinearEquiv.trans_apply, LinearEquiv.smulOfNeZero_apply]
  rw [hspan, BodyHingeFramework.finrank_span_rigidityRows_mapExtensor]

end CombinatorialRigidity.Molecular
