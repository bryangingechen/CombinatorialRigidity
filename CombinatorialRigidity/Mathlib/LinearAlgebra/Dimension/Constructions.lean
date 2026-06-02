/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Finrank of a constant (non-dependent) `Pi` type

Upstream-eligible mirror: mathlib has `Module.finrank_pi_fintype` for a *dependent*
finite product `(i : ι) → M i` (a sum of the fibers' finranks) and `Module.finrank_pi`
for the scalar case `ι → R` (= `Fintype.card ι`), but no fused lemma for the constant
non-dependent product `ι → M`. This file supplies it.

When promoted upstream this lives beside `Module.finrank_pi_fintype` in
`Mathlib/LinearAlgebra/Dimension/Constructions.lean`; the namespace stays `Module`.
-/

@[expose] public section

namespace Module

variable (R : Type*) [Semiring R] [StrongRankCondition R]
variable {ι : Type*} [Fintype ι] {M : Type*} [AddCommMonoid M] [Module R M]
  [Module.Free R M] [Module.Finite R M]

/-- The finrank of a constant finite product `ι → M` is `Fintype.card ι * finrank R M`.
The non-dependent specialization of `Module.finrank_pi_fintype`. -/
theorem finrank_pi_const :
    Module.finrank R (ι → M) = Fintype.card ι * Module.finrank R M := by
  rw [Module.finrank_pi_fintype R, Finset.sum_const, Finset.card_univ, smul_eq_mul]

end Module
