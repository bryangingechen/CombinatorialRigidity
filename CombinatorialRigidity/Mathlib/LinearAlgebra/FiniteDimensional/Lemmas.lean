/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Fused finrank equality for disjoint submodules

Upstream-eligible mirror:

* `Submodule.finrank_sup_of_inf_eq_bot` — the disjoint-submodule special case of
  `Submodule.finrank_sup_add_finrank_inf_eq`: when `p ⊓ q = ⊥` the inclusion-exclusion
  identity reduces to `finrank ↥(p ⊔ q) = finrank ↥p + finrank ↥q`. Upstream this lives
  beside `finrank_sup_add_finrank_inf_eq` in
  `Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`; the namespace stays `Submodule`.
-/

@[expose] public section

namespace Submodule

/-- **Finrank of a disjoint sup** — when `p ⊓ q = ⊥`, the inclusion-exclusion identity
`finrank ↥(p ⊔ q) + finrank ↥(p ⊓ q) = finrank ↥p + finrank ↥q` (mathlib's
`Submodule.finrank_sup_add_finrank_inf_eq`) reduces to
`finrank ↥(p ⊔ q) = finrank ↥p + finrank ↥q`.
Upstream-eligible: would live beside `finrank_sup_add_finrank_inf_eq` in
`Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`. -/
theorem finrank_sup_of_inf_eq_bot {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    (p q : Submodule K V) [FiniteDimensional K p] [FiniteDimensional K q]
    (h : p ⊓ q = ⊥) : Module.finrank K ↥(p ⊔ q) = Module.finrank K ↥p + Module.finrank K ↥q := by
  have key := Submodule.finrank_sup_add_finrank_inf_eq p q
  rw [h, finrank_bot, add_zero] at key
  omega

end Submodule
