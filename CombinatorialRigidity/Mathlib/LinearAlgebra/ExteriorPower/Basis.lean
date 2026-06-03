/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Pi

/-!
# Upstream candidate: the canonical top exterior power iso `⋀ⁿ (Fin n → R) ≃ₗ R`

The `n`-th exterior power of a free module of rank `n` is free of rank
`(n.choose n) = 1`, hence (over a nontrivial commutative ring) isomorphic to the
base ring. Mathlib ships the two boundary cases `exteriorPower.zeroEquiv`
(`⋀⁰ M ≃ₗ R`) and `exteriorPower.oneEquiv` (`⋀¹ M ≃ₗ M`), and the dimension count
`exteriorPower.finrank_eq`, but not the *top*-power iso. This file supplies it on
the standard carrier `Fin n → R`:

* **`Set.powersetCard.instUniqueTop`** — the index of the top-power basis,
  `Set.powersetCard (Fin n) n`, is a singleton (only `Finset.univ` has `n`
  elements). This is the combinatorial fact that makes the top power
  `1`-dimensional.
* **`exteriorPower.topEquiv`** — the canonical iso `⋀ⁿ (Fin n → R) ≃ₗ R`, built as
  the standard-basis top-power basis (`Module.Basis.exteriorPower (Pi.basisFun …)`)
  composed with the unique-index evaluation `LinearEquiv.funUnique`. Its value on
  the wedge of all standard basis vectors is `1` (`topEquiv_ιMulti_family_default`).

This is the first deliverable of Phase 21a (the Grassmann–Cayley *meet* / dual
half of the extensor algebra): the volume-form / orientation iso through which the
`⋀ʲ V × ⋀^(N−j) V → ⋀ᴺ V ≅ R` perfect wedge pairing lands in the base ring, on
which `complementIso` and the regressive product `meet` are built.

Promotion to mathlib: the `Unique` instance and `topEquiv` copy-paste into
`Mathlib/LinearAlgebra/ExteriorPower/Basis.lean` (which already supplies
`Module.Basis.exteriorPower` and `finrank_eq`); the Lean namespaces
(`Set.powersetCard`, `exteriorPower`) match upstream conventions.

See `notes/FRICTION.md` *Mirrored* and `DESIGN.md` *Mirror directory*.
-/

@[expose] public section

open Module

namespace Set.powersetCard

/-- The full set is the unique `n`-element subset of an `n`-element type. -/
instance instUniqueTop {n : ℕ} : Unique (Set.powersetCard (Fin n) n) where
  default := ⟨Finset.univ, by simp⟩
  uniq s := by
    apply Subtype.ext
    apply Finset.eq_univ_of_card
    rw [Fintype.card_fin]
    exact s.2

end Set.powersetCard

namespace exteriorPower

variable {R : Type*} [CommRing R] (n : ℕ)

/-- The canonical isomorphism of the *top* exterior power `⋀ⁿ (Fin n → R)` with the
base ring `R`: the top power of a rank-`n` free module is `1`-dimensional. Built
from the standard-basis top-power basis composed with the unique-index evaluation
`LinearEquiv.funUnique`. The dual half of the extensor algebra (the volume form /
orientation through which the perfect wedge pairing lands in `R`). -/
noncomputable def topEquiv : ⋀[R]^n (Fin n → R) ≃ₗ[R] R :=
  ((Pi.basisFun R (Fin n)).exteriorPower n).equivFun ≪≫ₗ
    LinearEquiv.funUnique (Set.powersetCard (Fin n) n) R R

/-- `topEquiv` sends the wedge of all standard basis vectors (the canonical
top-power basis vector) to `1`. -/
@[simp]
theorem topEquiv_ιMulti_family_default :
    topEquiv (R := R) n
        (exteriorPower.ιMulti_family R n (Pi.basisFun R (Fin n)) default) = 1 := by
  unfold topEquiv
  simp [LinearEquiv.funUnique, Basis.equivFun_apply]

end exteriorPower
