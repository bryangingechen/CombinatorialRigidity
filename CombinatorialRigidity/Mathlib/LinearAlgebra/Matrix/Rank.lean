/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Real.Basic

/-!
# Upstream candidates: rectangular linear independence via rank and the Gram determinant

`Mathlib.LinearAlgebra.Matrix.NonsingularInverse` has `Matrix.linearIndependent_rows_iff_isUnit`
for **square** matrices over a field (rows are LI iff the matrix is a unit, iff its determinant
is a unit, iff over a field it is nonzero). The corresponding **rectangular** characterizations
— that rows of `A : Matrix m n R` are LI iff `A.rank = #m`, and over an ordered field iff
`(A * Aᵀ).det ≠ 0` (the *Gram determinant* form) — are direct consequences of
`Matrix.rank_self_mul_transpose` / `Matrix.rank_eq_finrank_span_row` /
`LinearIndependent.rank_matrix` in `Mathlib.LinearAlgebra.Matrix.Rank`, but are not packaged
in mathlib as iff lemmas.

The combinatorial-rigidity project uses the Gram determinant form to characterize "the rows
of an affine polynomial matrix `M(t) = A + t • B` are LI at `t`" as the non-vanishing of a
single one-variable polynomial in `t`, then concludes via `Polynomial.finite_setOf_isRoot`
that the bad-`t` set is finite — the linear-interpolation-perturbation step of the Phase 8
target `linearRigidityMatroid_eq_rigidityMatroid` (see `LinearRigidityMatroid.lean`).

Mirror path: `Mathlib/LinearAlgebra/Matrix/Rank.lean`. Promotion to mathlib is a copy-paste
into the upstream file, alongside `Matrix.rank_self_mul_transpose` and
`LinearIndependent.rank_matrix`.
-/

namespace Matrix

variable {R : Type*} {m n : Type*}

/-- The rows of a rectangular matrix over a field are linearly independent iff the matrix's
rank equals the number of rows. Iff form of `LinearIndependent.rank_matrix`, derived from
`Matrix.rank_eq_finrank_span_row` + `linearIndependent_iff_card_eq_finrank_span`. -/
theorem linearIndependent_rows_iff_rank_eq_card
    [Field R] [Fintype m] [Fintype n] (A : Matrix m n R) :
    LinearIndependent R A.row ↔ A.rank = Fintype.card m := by
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, ← rank_eq_finrank_span_row,
    eq_comm]

/-- **Rectangular linear independence via the Gram determinant.** The rows of `A : Matrix m n R`
over a linearly ordered field are linearly independent iff `det (A * Aᵀ) ≠ 0`. Rectangular
analogue of `Matrix.linearIndependent_rows_iff_isUnit` (the square case, where the rows are LI
iff `det A ≠ 0` directly). Routes through `rank_self_mul_transpose` and the square
`linearIndependent_rows_iff_isUnit` at `A * Aᵀ`. -/
theorem linearIndependent_rows_iff_det_mul_transpose_ne_zero
    [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype m] [DecidableEq m] [Fintype n] (A : Matrix m n R) :
    LinearIndependent R A.row ↔ (A * Aᵀ).det ≠ 0 := by
  rw [linearIndependent_rows_iff_rank_eq_card, ← rank_self_mul_transpose,
    ← linearIndependent_rows_iff_rank_eq_card, linearIndependent_rows_iff_isUnit,
    isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

/-- **Linear independence is cofinite along an affine path.** Let `A B : Matrix m n ℝ`.
If the rows of `A + t₀ • B` are linearly independent for some `t₀ : ℝ`, then the rows
of `A + t • B` are linearly independent for all but finitely many `t : ℝ`.

The Gram-det characterization (`linearIndependent_rows_iff_det_mul_transpose_ne_zero`)
turns "rows LI" into the non-vanishing of `((A + t • B) * (A + t • B)ᵀ).det`, the evaluation
at `t` of a single polynomial in `Polynomial ℝ` (the determinant of the polynomial-entry matrix
`(X • C(B) + C(A)) * (X • C(B) + C(A))ᵀ`). The polynomial is nonzero (since nonzero at
`t₀`) and hence has finitely many roots by `Polynomial.finite_setOf_isRoot`. -/
theorem finite_setOf_not_linearIndependent_rows_along_affine_path
    [Finite m] [Finite n] (A B : Matrix m n ℝ) {t₀ : ℝ}
    (h : LinearIndependent ℝ (A + t₀ • B).row) :
    {t : ℝ | ¬ LinearIndependent ℝ (A + t • B).row}.Finite := by
  classical
  haveI : Fintype m := Fintype.ofFinite m
  haveI : Fintype n := Fintype.ofFinite n
  -- Polynomial-entry matrix `P` whose evaluation at `t` is `A + t • B`.
  let P : Matrix m n (Polynomial ℝ) :=
    (Polynomial.X : Polynomial ℝ) • B.map Polynomial.C + A.map Polynomial.C
  -- Gram-det polynomial `Q := det(P * Pᵀ) ∈ Polynomial ℝ`.
  let Q : Polynomial ℝ := (P * Pᵀ).det
  -- Each entry of `P` evaluates to `(A + t • B)[i,j]` at `t`.
  have hP_eval : ∀ t : ℝ, P.map ⇑(Polynomial.evalRingHom t) = A + t • B := by
    intro t
    ext i j
    change Polynomial.eval t (P i j) = (A + t • B) i j
    simp only [P, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
    ring
  -- `Q.eval t = det((A + t • B) * (A + t • B)ᵀ)`, via `RingHom.map_det` plus `Matrix.map_mul`
  -- and `Matrix.transpose_map`.
  have hQ_eval : ∀ t : ℝ, Q.eval t = ((A + t • B) * (A + t • B)ᵀ).det := by
    intro t
    change (Polynomial.evalRingHom t) Q = _
    rw [show Q = (P * Pᵀ).det from rfl, (Polynomial.evalRingHom t).map_det,
      show (Polynomial.evalRingHom t).mapMatrix (P * Pᵀ)
        = (P * Pᵀ).map ⇑(Polynomial.evalRingHom t) from rfl,
      Matrix.map_mul, Matrix.transpose_map, hP_eval]
  -- `Q ≠ 0`: at `t = t₀`, `Q.eval t₀ = det((A + t₀ • B) * (A + t₀ • B)ᵀ) ≠ 0` by hypothesis.
  have hQ_ne : Q ≠ 0 := fun hQ_zero => by
    have := hQ_eval t₀
    rw [hQ_zero, Polynomial.eval_zero] at this
    exact ((linearIndependent_rows_iff_det_mul_transpose_ne_zero _).mp h) this.symm
  -- The bad-`t` set is contained in `Q`'s root set, which is finite.
  refine (Polynomial.finite_setOf_isRoot hQ_ne).subset fun t ht => ?_
  rw [Set.mem_setOf_eq] at ht
  rw [Set.mem_setOf_eq, Polynomial.IsRoot, hQ_eval]
  by_contra h_ne
  exact ht ((linearIndependent_rows_iff_det_mul_transpose_ne_zero _).mpr h_ne)

end Matrix

/-- **Vector-form polynomial-along-line.** For a finite-dim ℝ-vector space `W` and an
affine family `t ↦ fun i => a i + t • b i : ℝ → ι → W` (with `ι` finite), if the family
is linearly independent at some `t₀ : ℝ`, then it is LI for all but finitely many `t : ℝ`.

Vector analogue of `Matrix.finite_setOf_not_linearIndependent_rows_along_affine_path`,
derived by pulling along a basis-induced isomorphism `W ≃ₗ[ℝ] (Fin (finrank ℝ W) → ℝ)`. -/
theorem LinearIndependent.finite_setOf_not_along_affine_path
    {ι W : Type*} [Finite ι] [AddCommGroup W] [Module ℝ W] [Module.Finite ℝ W]
    {a b : ι → W} {t₀ : ℝ}
    (h : LinearIndependent ℝ (fun i => a i + t₀ • b i)) :
    {t : ℝ | ¬ LinearIndependent ℝ (fun i => a i + t • b i)}.Finite := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  -- Pick a basis of `W` and identify `W` with `Fin n → ℝ`.
  let φ : W ≃ₗ[ℝ] (Fin (Module.finrank ℝ W) → ℝ) := (Module.finBasis ℝ W).equivFun
  let A : Matrix ι (Fin (Module.finrank ℝ W)) ℝ := Matrix.of (fun i j => φ (a i) j)
  let B : Matrix ι (Fin (Module.finrank ℝ W)) ℝ := Matrix.of (fun i j => φ (b i) j)
  -- The affine matrix family `A + t • B` has rows `φ ∘ (a · + t • b ·)`.
  have h_row : ∀ t : ℝ, (A + t • B).row = ⇑φ ∘ fun i => a i + t • b i := by
    intro t
    funext i j
    change A i j + t • B i j = φ (a i + t • b i) j
    rw [map_add, map_smul]
    rfl
  -- LI of the affine family ↔ LI of matrix rows, via the LinearEquiv `φ`.
  have h_iff : ∀ t : ℝ,
      LinearIndependent ℝ (fun i => a i + t • b i) ↔
      LinearIndependent ℝ (A + t • B).row := by
    intro t
    rw [h_row t]
    exact (LinearMap.linearIndependent_iff φ.toLinearMap (LinearEquiv.ker φ)).symm
  -- Apply the matrix-form helper.
  refine (Matrix.finite_setOf_not_linearIndependent_rows_along_affine_path A B
    ((h_iff t₀).mp h)).subset fun t ht => ?_
  rw [Set.mem_setOf_eq] at ht ⊢
  rwa [← h_iff]
