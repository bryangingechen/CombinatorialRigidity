/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Upstream candidate: the rows of a square matrix are independent iff its determinant is nonzero

`Mathlib.LinearAlgebra.Matrix.NonsingularInverse` has `Matrix.linearIndependent_rows_iff_isUnit`
and `Matrix.isUnit_iff_isUnit_det`; over a field the fused determinant form
`LinearIndependent K A.row ↔ A.det ≠ 0` is the three-lemma chain
`linearIndependent_rows_iff_isUnit` + `isUnit_iff_isUnit_det` + `isUnit_iff_ne_zero`, which the
combinatorial-rigidity project hit three times (`cross₃_ne_zero_iff_linearIndependent`, both
directions, and `Graph.IsAdmissiblePicture.exists_mvPolynomial`), so it is packaged here
(`notes/FRICTION.md`).

Mirror path: `Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean`. Promotion to mathlib is a
copy-paste into the upstream file, next to `Matrix.linearIndependent_rows_iff_isUnit`.
-/

@[expose] public section

namespace Matrix

variable {m K : Type*} [DecidableEq m] [Field K] [Fintype m]

/-- **The rows of a square matrix over a field are independent iff its determinant is nonzero.**
The determinant form of `Matrix.linearIndependent_rows_iff_isUnit`. -/
theorem linearIndependent_rows_iff_det_ne_zero {A : Matrix m m K} :
    LinearIndependent K A.row ↔ A.det ≠ 0 := by
  rw [linearIndependent_rows_iff_isUnit, isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

end Matrix
