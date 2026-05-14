/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Upstream candidate: the row-0-subtracted Vandermonde minor

If `v : Fin (n + 1) → R` and we form the `n × n` matrix whose `(i, j)`-entry is
`v i.succ ^ (j.val + 1) - v 0 ^ (j.val + 1)`, then its determinant equals the
full `(n + 1) × (n + 1)` Vandermonde determinant `∏_{0 ≤ i < j ≤ n} (v j - v i)`.

This is the classical row-reduction identity: in the Vandermonde matrix
`V i j = v i ^ j`, subtracting row 0 from each other row preserves the
determinant and turns column 0 into `(1, 0, …, 0)`; cofactor-expansion along
column 0 then collapses the `(n + 1) × (n + 1)` determinant to the `n × n`
minor of `power-difference` entries. The combinatorial-rigidity project uses
the identity at the leading-coefficient step of the moment-curve
`affinely-spanning rigid placement` proof in dimension `d`: the perturbed
difference matrix `M(t) = M_0 + t · M_1` has `det M_1` equal to the
power-difference determinant on the perturbation parameters, so injectivity of
the parameters implies `det M_1 ≠ 0`, hence the polynomial `t ↦ det M(t)` has
finitely many roots.

The lemma is upstream-eligible: pure linear algebra over a `CommRing` with no
project-specific concepts. The proof uses the polynomial-evaluation identity
`Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde` already in mathlib,
plus a one-step Laplace expansion along the sparse top row.

Mirror path: `Mathlib/LinearAlgebra/Vandermonde.lean`. (Naming: the matrix is
the `(Fin.succ, Fin.succ)`-submatrix obtained after the row-0-subtraction
reduction, so `det_powerDiff_succAbove_zero` would be the wordy alternative;
`det_powerDifferences` is the project-internal call site name.)
-/

namespace Matrix

open Polynomial Finset

/-- The `n × n` matrix `M i j = v i.succ ^ (j.val + 1) - v 0 ^ (j.val + 1)` has
determinant equal to the `(n + 1) × (n + 1)` Vandermonde determinant
`∏_{0 ≤ i < j ≤ n} (v j - v i)`.

Geometrically, `M` is the matrix of differences `(p i - p 0)` for `p : Fin (n+1) →
R` defined by the moment curve `p i = (v i, v i^2, …, v i^n)`. -/
theorem det_powerDifferences {n : ℕ} {R : Type*} [CommRing R] (v : Fin (n + 1) → R) :
    (Matrix.of (fun i j : Fin n => v i.succ ^ (j.val + 1) - v 0 ^ (j.val + 1))).det =
      ∏ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i, (v j - v i) := by
  classical
  -- Trivial ring: both sides are `0`.
  nontriviality R
  -- Strategy: realize `M` as the `(Fin.succ, Fin.succ)`-minor of the
  -- `(n+1) × (n+1)` evaluation matrix `A i j = (p j).eval (v i)` where
  -- `p 0 = 1` and `p k.succ = X^(k.val + 1) - C (v 0 ^ (k.val + 1))`. Then
  -- `det A = det (vandermonde v)` by
  -- `det_eval_matrixOfPolynomials_eq_det_vandermonde`, and `det A = det M`
  -- by cofactor-expansion along row 0 (only the `(0, 0)`-entry is nonzero).
  set p : Fin (n + 1) → R[X] :=
    Fin.cases 1 (fun k : Fin n => X ^ (k.val + 1) - C (v 0 ^ (k.val + 1))) with hp
  have h_p_zero : p 0 = 1 := by simp [p]
  have h_p_succ : ∀ k : Fin n, p k.succ = X ^ (k.val + 1) - C (v 0 ^ (k.val + 1)) := by
    intro k; simp [p]
  have h_deg : ∀ i, (p i).natDegree = (i : ℕ) := by
    refine Fin.cases ?_ ?_
    · rw [h_p_zero, Fin.val_zero, natDegree_one]
    · intro k
      rw [h_p_succ, natDegree_X_pow_sub_C, Fin.val_succ]
  have h_monic : ∀ i, (p i).Monic := by
    refine Fin.cases ?_ ?_
    · rw [h_p_zero]; exact monic_one
    · intro k
      rw [h_p_succ]
      exact monic_X_pow_sub_C _ (Nat.succ_ne_zero _)
  -- The (n+1) × (n+1) evaluation matrix and its identification with `vandermonde v`.
  set A : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
    Matrix.of (fun i j : Fin (n + 1) => (p j).eval (v i)) with hA
  have h_vand : (Matrix.vandermonde v).det = A.det :=
    det_eval_matrixOfPolynomials_eq_det_vandermonde v p h_deg h_monic
  rw [det_vandermonde] at h_vand
  -- Row 0 of `A`: only the `(0, 0)`-entry is nonzero (= 1).
  have h_A_row_zero : ∀ j : Fin (n + 1), j ≠ 0 → A 0 j = 0 := by
    intro j hj
    obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.mpr hj
    simp [A, h_p_succ]
  have h_A_zero_zero : A 0 0 = 1 := by simp [A, h_p_zero]
  -- Cofactor-expand along row 0.
  have h_det_A : A.det = (A.submatrix Fin.succ Fin.succ).det := by
    rw [det_succ_row_zero A]
    rw [Finset.sum_eq_single (0 : Fin (n + 1))]
    · simp [h_A_zero_zero, Fin.succAbove_zero]
    · intros j _ hj
      rw [h_A_row_zero j hj]; ring
    · intro h; exact (h (Finset.mem_univ _)).elim
  -- The submatrix `A.submatrix Fin.succ Fin.succ` is our target.
  have h_submatrix :
      A.submatrix Fin.succ Fin.succ =
        Matrix.of (fun i j : Fin n => v i.succ ^ (j.val + 1) - v 0 ^ (j.val + 1)) := by
    ext i j
    simp [A, h_p_succ, eval_sub, eval_pow, eval_X, eval_C]
  rw [← h_submatrix, ← h_det_A, ← h_vand]

end Matrix
