/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Mathlib.Algebra.Module.Submodule.Union
public import CombinatorialRigidity.Molecular.MeetHyperplanes
public import CombinatorialRigidity.Molecular.Molecule.Pencil.Statement
public import CombinatorialRigidity.Molecular.GenericLift.HingeGeneric

/-!
# Projective transport and the automorphism of a cut

The lemmas on projective automorphisms of the cut-edge case of the reduction of
`sec:pencil-reduction` (`lem:pencil-projective-transport`, `lem:pencil-cut-nondegeneracy`). The
cut-edge case realizes the two sides of a cut separately and moves the second by a linear
automorphism `g` of `K⁴`, acting on the hinges through the automorphism of the screw space that `g`
induces, on the points by `g` and on the normals by a contragredient `h` of `g`, so that the
crossing edge's two cross-incidences hold (`lem:two-pencil-extension-iff`);
`exists_extensor_two_pencils` then gives that edge its hinge. The loop, base and cut-edge cases
themselves are `ArmsAssembly.lean`, each the case in every dimension (`Grade/Arms.lean`) at grade
`2`.

## Main results

* `hasPencilPanelRealization_mapExtensor_screwEquivOfLinearEquiv`: a linear automorphism of `K⁴` and
  a contragredient of it move a pencil realization to a pencil realization
  (`lem:pencil-projective-transport`).
* `exists_reposition_cross_incidences`: an automorphism after which the two cross-incidences of a
  crossing edge hold and its two points are independent (`lem:pencil-cut-nondegeneracy`).
-/

@[expose] public section

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K]
variable {α β : Type*}

/-! ## Projective transport of a pencil realization

The cut-edge case (`lem:pencil-cut-case`) moves the realization of one side so that the crossing
edge's two cross-incidences hold (`exists_extensor_two_pencils_iff`). A linear automorphism `g` of
`K⁴` moves the hinges by the automorphism `BodyHingeFramework.screwEquivOfLinearEquiv g` of the
screw space that it induces (`def:induced-screw-map`), as in Crapo and Whiteley's projective
invariance (`thm:projective-invariance`), the points by `g`, and the normals by a contragredient `h`
of `g`, a linear automorphism with `g x ⬝ᵥ h y = x ⬝ᵥ y`. The rank does not change
(`BodyHingeFramework.finrank_span_rigidityRows_mapExtensor`, `lem:screw-map-rows`), so a pencil
realization at the deficiency rank moves to one (`lem:pencil-projective-transport`). -/

/-- **Lying in a panel moves with an automorphism of `K⁴`** (`lem:pencil-projective-transport`): if
`C` lies in the panel with normal `n` (`ExtensorInPanel`) and `h` is a contragredient of the linear
automorphism `g` of `K⁴` (`g x ⬝ᵥ h y = x ⬝ᵥ y`), then `screwEquivOfLinearEquiv g C` lies in the
panel with normal `h n`. The vectors `p` whose extensor is `C` become `g ∘ p`
(`screwEquivOfLinearEquiv_mk_extensor`), and the contragredient identity turns each incidence
`p i ⬝ᵥ n = 0` into `g (p i) ⬝ᵥ h n = 0`. -/
theorem extensorInPanel_screwEquivOfLinearEquiv {C : ScrewSpace K 2} {n : Fin 4 → K}
    (g h : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K)) (hgh : ∀ x y : Fin 4 → K, g x ⬝ᵥ h y = x ⬝ᵥ y)
    (hC : ExtensorInPanel C n) :
    ExtensorInPanel (BodyHingeFramework.screwEquivOfLinearEquiv g C) (h n) := by
  obtain ⟨p, hCp, hperp⟩ := hC
  have hCmk : C = ScrewSpace.mk (extensor p) (extensor_mem_exteriorPower p) :=
    ScrewSpace.ext (by rw [ScrewSpace.val_mk]; exact hCp)
  refine ⟨fun i => g (p i), ?_, fun i => ?_⟩
  · rw [hCmk, BodyHingeFramework.screwEquivOfLinearEquiv_mk_extensor, ScrewSpace.val_mk,
      Function.comp_def]
  · rw [hgh]; exact hperp i

/-- **Passing through a point moves with an automorphism of `K⁴`**
(`lem:pencil-projective-transport`): if `C` passes through the point `q` (`ExtensorThroughPoint`),
then `screwEquivOfLinearEquiv g C` passes through `g q`. The vectors `p` whose extensor is `C`
become `g ∘ p` (`screwEquivOfLinearEquiv_mk_extensor`), and `g` sends a linear combination of the
`p i` equal to `q` to the same combination of the `g (p i)`. -/
theorem extensorThroughPoint_screwEquivOfLinearEquiv {C : ScrewSpace K 2} {q : Fin 4 → K}
    (g : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K)) (hC : ExtensorThroughPoint C q) :
    ExtensorThroughPoint (BodyHingeFramework.screwEquivOfLinearEquiv g C) (g q) := by
  obtain ⟨p, hCp, hq⟩ := hC
  have hCmk : C = ScrewSpace.mk (extensor p) (extensor_mem_exteriorPower p) :=
    ScrewSpace.ext (by rw [ScrewSpace.val_mk]; exact hCp)
  refine ⟨fun i => g (p i), ?_, ?_⟩
  · rw [hCmk, BodyHingeFramework.screwEquivOfLinearEquiv_mk_extensor, ScrewSpace.val_mk,
      Function.comp_def]
  · obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hq
    rw [map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- **Projective transport of a pencil realization** (`lem:pencil-projective-transport`, over any
field): moving a pencil realization `(F, normal, point)` of `G` by a linear automorphism `g` of `K⁴`
and a contragredient `h` of it (`g x ⬝ᵥ h y = x ⬝ᵥ y`) gives a pencil realization of `G`: the hinges
move by the induced automorphism `screwEquivOfLinearEquiv g` of the screw space
(`BodyHingeFramework.mapExtensor`), the points by `g` and the normals by `h`. The hinges stay in the
panels and through the points (`extensorInPanel_screwEquivOfLinearEquiv`,
`extensorThroughPoint_screwEquivOfLinearEquiv`), the incidence `point v ⬝ᵥ normal v = 0` holds by
the contragredient identity, and the normals, the points and the hinges stay nonzero, as the three
maps are injective. With `BodyHingeFramework.finrank_span_rigidityRows_mapExtensor`, which keeps the
rank, the cut-edge case uses it to move one side (`lem:pencil-cut-case`). It is the collineation
companion of the polarity's self-duality (`lem:pencil-self-dual`), which exchanges the normals and
the points. -/
theorem hasPencilPanelRealization_mapExtensor_screwEquivOfLinearEquiv
    {G : Graph α β} {F : BodyHingeFramework K 2 α β} {normal point : α → Fin 4 → K}
    (g h : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K)) (hgh : ∀ x y : Fin 4 → K, g x ⬝ᵥ h y = x ⬝ᵥ y)
    (hr : HasPencilPanelRealization G F normal point) :
    HasPencilPanelRealization G (F.mapExtensor (BodyHingeFramework.screwEquivOfLinearEquiv g))
      (fun v => h (normal v)) (fun v => g (point v)) := by
  obtain ⟨⟨hFg, hnnz, hSnz, hlink⟩, hpnz, hincid, hthrough⟩ := hr
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [BodyHingeFramework.mapExtensor_graph]; exact hFg
  · intro v hv
    exact fun H => hnnz v hv (h.map_eq_zero_iff.mp H)
  · intro e; rw [BodyHingeFramework.mapExtensor_supportExtensor]
    exact fun H => hSnz e ((BodyHingeFramework.screwEquivOfLinearEquiv g).map_eq_zero_iff.mp H)
  · intro e u w hlk; rw [BodyHingeFramework.mapExtensor_supportExtensor]
    exact ⟨extensorInPanel_screwEquivOfLinearEquiv g h hgh (hlink e u w hlk).1,
           extensorInPanel_screwEquivOfLinearEquiv g h hgh (hlink e u w hlk).2⟩
  · intro v hv
    exact fun H => hpnz v hv (g.map_eq_zero_iff.mp H)
  · intro v hv
    simp only []
    rw [hgh]; exact hincid v hv
  · intro e u w hlk; rw [BodyHingeFramework.mapExtensor_supportExtensor]
    exact ⟨extensorThroughPoint_screwEquivOfLinearEquiv g (hthrough e u w hlk).1,
           extensorThroughPoint_screwEquivOfLinearEquiv g (hthrough e u w hlk).2⟩

/-! ## The automorphism of the cut-edge case

With the two sides of a cut realized independently, the crossing edge `uv` has a hinge once the
second side is moved by a linear automorphism `g` of `K⁴`, with a contragredient `h`, such that
`pt₁(u) ⬝ᵥ h(n₂(v)) = 0` and `g(pt₂(v)) ⬝ᵥ n₁(u) = 0` (`exists_extensor_two_pencils_iff`). An
explicit `g` does it, over any field (`lem:pencil-cut-nondegeneracy`): it sends `pt₂(v)` to a vector
`a` orthogonal to `n₁(u)`, and a vector `b` orthogonal to `n₂(v)` to `pt₁(u)`. The vectors
orthogonal to one vector of `K⁴` form a space of dimension at least `3`, which no line contains, so
`a` and `b` can be chosen off the lines through `pt₁(u)` and `pt₂(v)`. -/

/-- **Every linear automorphism of `Kⁿ` has a contragredient** (`lem:pencil-cut-nondegeneracy`): for
`g : Kⁿ ≃ₗ Kⁿ` there is a linear automorphism `h` with `g x ⬝ᵥ h y = x ⬝ᵥ y` for all `x, y`, the
inverse transpose of `g`: with `A = LinearMap.toMatrix' g`, `h` is `Matrix.toLinearEquiv'` of
`(A⁻¹)ᵀ`. `contragredient` (`MeetHyperplanes.lean`) gives the same map as a linear map; the moves
of a pencil realization (`hasPencilPanelRealization_mapExtensor_screwEquivOfLinearEquiv`) take `h`
as a linear equivalence, which keeps the normals nonzero. -/
theorem exists_contragredient_linearEquiv {n : ℕ} (g : (Fin n → K) ≃ₗ[K] (Fin n → K)) :
    ∃ h : (Fin n → K) ≃ₗ[K] (Fin n → K), ∀ x y : Fin n → K, g x ⬝ᵥ h y = x ⬝ᵥ y := by
  set A : Matrix (Fin n) (Fin n) K :=
    LinearMap.toMatrix' (g : (Fin n → K) →ₗ[K] (Fin n → K)) with hA
  have hrinv : A * LinearMap.toMatrix' (g.symm : (Fin n → K) →ₗ[K] (Fin n → K)) = 1 := by
    rw [hA, ← LinearMap.toMatrix'_comp, LinearEquiv.comp_symm, LinearMap.toMatrix'_id]
  have hAu : IsUnit A.det := Matrix.isUnit_det_of_right_inverse hrinv
  have : Invertible ((A⁻¹)ᵀ) :=
    ((A⁻¹)ᵀ).invertibleOfIsUnitDet (by
      rw [Matrix.det_transpose, isUnit_iff_ne_zero, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
      exact inv_ne_zero (isUnit_iff_ne_zero.mp hAu))
  refine ⟨Matrix.toLinearEquiv' ((A⁻¹)ᵀ) inferInstance, fun x y => ?_⟩
  have hgx : g x = A *ᵥ x := (LinearMap.toMatrix'_mulVec _ x).symm
  have hhy : Matrix.toLinearEquiv' ((A⁻¹)ᵀ) inferInstance y = (A⁻¹)ᵀ *ᵥ y := rfl
  rw [hgx, hhy, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ hAu, Matrix.one_mulVec]

/-- **A vector orthogonal to `m` and independent of a nonzero `p`**
(`lem:pencil-cut-nondegeneracy`): for any `m` and any nonzero `p` in `K⁴` there is a `w` with
`w ⬝ᵥ m = 0` and `![w, p]` linearly independent. The vectors orthogonal to `m` are the kernel of one
linear form on `K⁴`, of dimension at least `3`, so they do not all lie on the line `span {p}`; any
of them off that line will do. -/
theorem exists_perp_linearIndependent (m p : Fin 4 → K) (hp : p ≠ 0) :
    ∃ w : Fin 4 → K, w ⬝ᵥ m = 0 ∧ LinearIndependent K ![w, p] := by
  set φ : (Fin 4 → K) →ₗ[K] K := ∑ j, m j • (LinearMap.proj j) with hφ
  have hφa : ∀ x : Fin 4 → K, φ x = m ⬝ᵥ x := fun x => by simp [hφ, dotProduct]
  have hrk : 3 ≤ Module.finrank K (LinearMap.ker φ) := by
    have hadd := φ.finrank_range_add_finrank_ker
    have hle : Module.finrank K (LinearMap.range φ) ≤ 1 := by
      have := Submodule.finrank_le (LinearMap.range φ); simpa using this
    have h4 : Module.finrank K (Fin 4 → K) = 4 := by simp
    omega
  have hnotle : ¬ (LinearMap.ker φ ≤ Submodule.span K {p}) := by
    intro hle
    have := Submodule.finrank_mono hle
    rw [finrank_span_singleton hp] at this; omega
  obtain ⟨w, hwker, hwnotin⟩ := IsConcreteLE.not_le_iff_exists.mp hnotle
  refine ⟨w, ?_, ?_⟩
  · have hker : φ w = 0 := hwker
    rw [hφa] at hker; rw [dotProduct_comm]; exact hker
  · rw [linearIndependent_fin2]
    exact ⟨hp, fun c hc => hwnotin (by rw [Submodule.mem_span_singleton]; exact ⟨c, hc⟩)⟩

/-- **The automorphism of the cut-edge case** (`lem:pencil-cut-nondegeneracy`): given the normals
and points at the two ends of a crossing edge `uv`, `n₁(u)` and `pt₁(u)` on the first side and
`n₂(v)` and `pt₂(v)` on the second, with both points nonzero, there are a linear automorphism `g` of
`K⁴` and a contragredient `h` of it (`g x ⬝ᵥ h y = x ⬝ᵥ y`) such that, once the second side is moved
by `(g, h)`, the two cross-incidences of `exists_extensor_two_pencils_iff` hold,
`pt₁(u) ⬝ᵥ h(n₂(v)) = 0` and `g(pt₂(v)) ⬝ᵥ n₁(u) = 0`, and the points `pt₁(u)` and `g(pt₂(v))` are
linearly independent. The cut-edge case uses it with
`hasPencilPanelRealization_mapExtensor_screwEquivOfLinearEquiv` (`lem:pencil-cut-case`); the
independence is what its adjacent-distinct form needs at the crossing edge.

The construction works over any field. Choose `a` orthogonal to `n₁(u)` with `![a, pt₁(u)]`
independent and `b` orthogonal to `n₂(v)` with `![b, pt₂(v)]` independent
(`exists_perp_linearIndependent`); let `g` send `pt₂(v)` to `a` and `b` to `pt₁(u)` (the composite
of two automorphisms of `exists_linearEquiv_basisFun_pair`), and take `h` from
`exists_contragredient_linearEquiv`. Then `g(pt₂(v)) = a` gives the second incidence, and
`g b = pt₁(u)` with the contragredient identity turns the first into `b ⬝ᵥ n₂(v) = 0`. The
independence is that of `![a, pt₁(u)]`, read through `g(pt₂(v)) = a`
(`LinearIndependent.pair_symm_iff`). -/
theorem exists_reposition_cross_incidences (n₁u pt₁u n₂v pt₂v : Fin 4 → K)
    (h1 : pt₁u ≠ 0) (h2 : pt₂v ≠ 0) :
    ∃ (g h : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K)),
      (∀ x y : Fin 4 → K, g x ⬝ᵥ h y = x ⬝ᵥ y) ∧
      pt₁u ⬝ᵥ h n₂v = 0 ∧ (g pt₂v) ⬝ᵥ n₁u = 0 ∧
      LinearIndependent K ![pt₁u, g pt₂v] := by
  obtain ⟨a, hanu, hLIa⟩ := exists_perp_linearIndependent n₁u pt₁u h1
  obtain ⟨b, hbnv, hLIb⟩ := exists_perp_linearIndependent n₂v pt₂v h2
  obtain ⟨g₁, hg₁0, hg₁1⟩ := exists_linearEquiv_basisFun_pair (k := 2) ![b, pt₂v] hLIb
  obtain ⟨g₂, hg₂0, hg₂1⟩ :=
    exists_linearEquiv_basisFun_pair (k := 2) ![pt₁u, a] (LinearIndependent.pair_symm_iff.mp hLIa)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hg₁0 hg₁1 hg₂0 hg₂1
  set g := g₁.symm.trans g₂ with hgdef
  obtain ⟨h, hgh⟩ := exists_contragredient_linearEquiv g
  have hgb : g b = pt₁u := by
    have hsb : g₁.symm b = Pi.basisFun K (Fin (2 + 2)) 0 := by rw [← hg₁0, g₁.symm_apply_apply]
    rw [hgdef, LinearEquiv.trans_apply, hsb, hg₂0]
  have hgpt : g pt₂v = a := by
    have hsp : g₁.symm pt₂v = Pi.basisFun K (Fin (2 + 2)) 1 := by rw [← hg₁1, g₁.symm_apply_apply]
    rw [hgdef, LinearEquiv.trans_apply, hsp, hg₂1]
  exact ⟨g, h, hgh, by rw [← hgb, hgh b n₂v]; exact hbnv, by rw [hgpt]; exact hanu,
    by rw [hgpt]; exact LinearIndependent.pair_symm_iff.mp hLIa⟩

end CombinatorialRigidity.Molecular
