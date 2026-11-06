/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.LinearAlgebra.Pi

/-!
# Upstream candidate: `LinearMap.pi_apply_eq_sum_univ` with `Pi.single`

Mathlib's `LinearMap.pi_apply_eq_sum_univ` expands a linear map on `ι → R` over the standard basis
written as `fun j => if i = j then 1 else 0`. **`LinearMap.pi_apply_eq_sum_univ_single`** is the
same statement with the basis vectors spelled `Pi.single i 1`, the form in which `Pi.single` simp
lemmas apply.

Promotion to mathlib: copy-paste into `Mathlib/LinearAlgebra/Pi.lean`, after
`LinearMap.pi_apply_eq_sum_univ`. The namespace (`LinearMap`) matches upstream conventions.

See `DESIGN.md` *Mirror directory*.
-/

@[expose] public section

namespace LinearMap

variable {ι R M₂ : Type*} [Semiring R] [AddCommMonoid M₂] [Module R M₂] [Fintype ι]
  [DecidableEq ι]

/-- A linear map `f` applied to `x : ι → R` is the sum of `x i • f (Pi.single i 1)`: the image of
the canonical basis written with `Pi.single`. -/
theorem pi_apply_eq_sum_univ_single (f : (ι → R) →ₗ[R] M₂) (x : ι → R) :
    f x = ∑ i, x i • f (Pi.single i 1) := by
  rw [pi_apply_eq_sum_univ f x]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  funext j
  simp [Pi.single_apply, eq_comm]

end LinearMap
