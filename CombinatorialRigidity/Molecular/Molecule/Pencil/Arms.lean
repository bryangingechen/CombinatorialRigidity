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
# The automorphism of a cut

The lemmas of `lem:pencil-cut-nondegeneracy`. Two sides of a cut crossed by one edge `uv`, realized
separately, are glued once the second is moved by a linear automorphism `g` of `K⁴`, with a
contragredient `h` of it (`g x ⬝ᵥ h y = x ⬝ᵥ y`), after which the crossing edge's two
cross-incidences hold (`lem:two-pencil-extension-iff`). Every linear automorphism of `Kⁿ` has a
contragredient, its inverse transpose (`exists_contragredient_linearEquiv`), which the cut-edge
cases in every dimension use (`Grade/Arms.lean`, `Grade/LiftCutEdge.lean`).
`exists_reposition_cross_incidences` chooses `g` in `K⁴`; its form in every dimension, with the
normals and the points exchanged, is `exists_reposition_planes` (`lem:pencil-d-cut-reposition`).

## Main results

* `exists_contragredient_linearEquiv`: every linear automorphism of `Kⁿ` has a contragredient.
* `exists_reposition_cross_incidences`: an automorphism after which the two cross-incidences of a
  crossing edge hold and its two points are independent (`lem:pencil-cut-nondegeneracy`).
-/

@[expose] public section

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K]
variable {α β : Type*}

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
of a pencil realization in every dimension
(`hasPencilPlaneRealization_mapExtensor_screwEquivOfLinearEquiv`) take `h` as a linear equivalence,
which keeps the hinges nonzero. -/
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
linearly independent. Its form in every dimension, with the normals and the points exchanged, is
`exists_reposition_planes` (`lem:pencil-d-cut-reposition`); the independence is what the
adjacent-distinct form of a cut-edge case needs at the crossing edge.

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
