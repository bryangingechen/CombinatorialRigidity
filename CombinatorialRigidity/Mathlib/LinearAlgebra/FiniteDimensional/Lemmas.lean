/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Fused finrank facts for submodules

Upstream-eligible mirrors:

* `Submodule.finrank_sup_of_inf_eq_bot` — the disjoint-submodule special case of
  `Submodule.finrank_sup_add_finrank_inf_eq`: when `p ⊓ q = ⊥` the inclusion-exclusion
  identity reduces to `finrank ↥(p ⊔ q) = finrank ↥p + finrank ↥q`. Upstream this lives
  beside `finrank_sup_add_finrank_inf_eq` in
  `Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`; the namespace stays `Submodule`.
* `Submodule.finrank_add_finrank_map_le_of_le_ker` — a submodule `A` killed by a linear map `D`
  and a submodule `B` inside `S` together with `A` bound the dimension of `S`:
  `finrank A + finrank (D B) ≤ finrank S` (rank-nullity for `D` on `A ⊔ B`).
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

/-- **A kernel block and an image block bound the ambient dimension** — if `A ≤ ker D` and
`A, B ≤ S`, then `finrank A + finrank (B.map D) ≤ finrank S`: rank-nullity for `D` restricted
to `A ⊔ B ≤ S`, whose image contains `B.map D` and whose kernel contains `A`. This is the linear
algebra of a block-triangular rank bound (the rows of `A` read only the columns `D` deletes).
Upstream-eligible: would live beside `finrank_sup_add_finrank_inf_eq` in
`Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`. -/
theorem finrank_add_finrank_map_le_of_le_ker {K V V' : Type*} [DivisionRing K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [AddCommGroup V'] [Module K V'] {S A B : Submodule K V}
    (D : V →ₗ[K] V') (hA : A ≤ LinearMap.ker D) (hAS : A ≤ S) (hBS : B ≤ S) :
    Module.finrank K A + Module.finrank K (B.map D) ≤ Module.finrank K S := by
  set T := A ⊔ B
  have hrn := LinearMap.finrank_range_add_finrank_ker (D.domRestrict T)
  have hrange : B.map D ≤ LinearMap.range (D.domRestrict T) := by
    rw [LinearMap.range_domRestrict]
    exact Submodule.map_mono le_sup_right
  have hker : A.comap T.subtype ≤ LinearMap.ker (D.domRestrict T) := fun x hx => hA hx
  have hAeq : Module.finrank K (A.comap T.subtype) = Module.finrank K A :=
    (Submodule.comapSubtypeEquivOfLe le_sup_left).finrank_eq
  have hTS : Module.finrank K T ≤ Module.finrank K S := Submodule.finrank_mono (sup_le hAS hBS)
  have h1 := Submodule.finrank_mono hrange
  have h2 := Submodule.finrank_mono hker
  omega

end Submodule
