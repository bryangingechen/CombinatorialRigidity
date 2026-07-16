/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.LinearAlgebra.Matrix.Polynomial

/-!
# Upstream candidate: evaluating `det (X • A.map C + B.map C)` at a scalar.

The matrix polynomial `(X • A.map C + B.map C : Matrix n n α[X]).det ∈ α[X]`
already has its `natDegree` and its `0`- and `card`-coefficients pinned down in
`Mathlib.LinearAlgebra.Matrix.Polynomial`
(`natDegree_det_X_add_C_le`, `coeff_det_X_add_C_zero`, `coeff_det_X_add_C_card`).
The companion `eval`-at-a-scalar identity

  `eval t (det (X • A.map C + B.map C)) = (t • A + B).det`

is not in mathlib. It is the direct consequence of `RingHom.map_det` applied to
`evalRingHom t : α[X] →+* α`, plus a pointwise simplification of the entries of
`(evalRingHom t).mapMatrix (X • A.map C + B.map C)` back to `t • A + B`.

The combinatorial-rigidity project uses this at the analysis leaf of the
d-general affinely-spanning rigid placement proof (`RigidityMatroid.lean`, over
the fixed coordinate field `ℝ` that file works in — the lemma itself is
carrier-agnostic, any `CommRing α`): the polynomial
`P := det (X • M₁.map C + M₀.map C) ∈ α[X]` has leading coefficient
`det M₁ ≠ 0` and per-tuple bad-`t` set `{t | P.IsRoot t}`, identified via
`eval_det_X_add_C` with `{t | det (t • M₁ + M₀) = 0}` — i.e. the difference
matrix `t • M₁ + M₀` is singular for only finitely many `t`.

Mirror path: `Mathlib/LinearAlgebra/Matrix/Polynomial.lean`. Promotion to mathlib
is copy-paste into the upstream file, alongside the existing `coeff_*` and
`natDegree_*` siblings.
-/

@[expose] public section

namespace Polynomial

open Matrix

variable {n α : Type*} [DecidableEq n] [Fintype n] [CommRing α]

/-- Evaluating the matrix-polynomial determinant `det (X • A.map C + B.map C)`
at a scalar `t` yields the scalar determinant `det (t • A + B)`. Companion to
`Polynomial.coeff_det_X_add_C_zero` / `Polynomial.coeff_det_X_add_C_card`. -/
theorem eval_det_X_add_C (A B : Matrix n n α) (t : α) :
    eval t (det ((X : α[X]) • A.map C + B.map C)) = (t • A + B).det := by
  rw [show eval t (det ((X : α[X]) • A.map C + B.map C)) =
        evalRingHom t (det ((X : α[X]) • A.map C + B.map C)) from rfl,
      (evalRingHom t).map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, coe_evalRingHom, Matrix.map_apply,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, eval_add, eval_mul,
    eval_X, eval_C]

end Polynomial
