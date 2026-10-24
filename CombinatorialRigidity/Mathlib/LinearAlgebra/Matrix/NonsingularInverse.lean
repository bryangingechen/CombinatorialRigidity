/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Upstream candidates: independent rows of a square matrix

`Mathlib.LinearAlgebra.Matrix.NonsingularInverse` has `Matrix.linearIndependent_rows_iff_isUnit`
and `Matrix.isUnit_iff_isUnit_det`; over a field the fused determinant form
`LinearIndependent K A.row ↔ A.det ≠ 0` is the three-lemma chain
`linearIndependent_rows_iff_isUnit` + `isUnit_iff_isUnit_det` + `isUnit_iff_ne_zero`, packaged
here. The combinatorial-rigidity project uses it in `Molecular/Molecule/Pencil/`
(`cross₃_ne_zero_iff_linearIndependent` in `Chart.lean`) and in its `MainComponent/`
(`Graph.IsAdmissiblePicture.exists_mvPolynomial` and `Graph.exists_isAdmissiblePicture` in
`Carrier.lean`, `exists_det_poly` in `GenericBase.lean`, and `Configuration.lean`).

`LinearIndependent.eq_zero_of_forall_dotProduct_eq_zero` is the kernel form of
`Matrix.mulVec_injective_iff_isUnit`: a vector with dot product zero against the `n` independent
rows of a square matrix is zero. The project uses it in `MainComponent/` for a vector of `K³`
orthogonal to three independent picture points (`Graph.finrank_affineLifts`,
`Graph.finrank_ker_liftingMatrix`, `Graph.IsAdmissiblePicture.mem_liftingSpace_of_coplanar`,
`Graph.finrank_liftingPlanes`, `Graph.IsAdmissiblePicture.eq_zero_of_forall_closedNbhd`,
`Graph.planeDiff_eq_zero_of_splitOff` and `eq_zero_of_dotProduct_triple`).

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
  rw [linearIndependent_row_iff_isUnit, isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

omit [DecidableEq m] in
/-- **A vector with dot product zero against `n` independent vectors of `Kⁿ` is zero.** The matrix
with those vectors as rows is a unit (`Matrix.linearIndependent_row_iff_isUnit`), so its
`mulVec` is injective (`Matrix.mulVec_injective_iff_isUnit`), and it sends the vector to zero. -/
theorem _root_.LinearIndependent.eq_zero_of_forall_dotProduct_eq_zero {v : m → m → K}
    (hv : LinearIndependent K v) {x : m → K} (hx : ∀ i, x ⬝ᵥ v i = 0) : x = 0 := by
  classical
  refine mulVec_injective_iff_isUnit.mpr ((linearIndependent_row_iff_isUnit (A := of v)).mp hv)
    (?_ : of v *ᵥ x = of v *ᵥ 0)
  rw [mulVec_zero]
  funext i
  exact (dotProduct_comm _ _).trans (hx i)

end Matrix
