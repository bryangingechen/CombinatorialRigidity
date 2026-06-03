/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Dual.Basis

/-!
# Upstream candidates: the top exterior power iso and the `pairingDual` iso

Two upstream-eligible facts about exterior-power bases that mathlib does not yet
ship, both consumed by the Grassmann–Cayley *meet* of Phase 21a.

## The canonical top exterior power iso `⋀ⁿ (Fin n → R) ≃ₗ R`

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

## The `pairingDual` iso `⋀ⁿ (M*) ≃ₗ (⋀ⁿ M)*` for finite free `M`

Mathlib ships `exteriorPower.pairingDual` as a bare linear map `⋀ⁿ (Dual R M) →ₗ
Dual R (⋀ⁿ M)`. When `M` is finite free with an ordered basis `b`, this map is an
isomorphism: it carries the exterior-power basis built from the dual basis
`b.dualBasis` onto the dual basis of the exterior-power basis built from `b`
(`coe_dualBasis` identifies `b.dualBasis` with `b.coord`, and
`exteriorPower.basis_coord` identifies the resulting `pairingDual` image with the
coordinate forms of `b.exteriorPower n`). This file packages that as

* **`exteriorPower.pairingDualEquiv`** — the iso, defined via `Basis.equiv` between
  `b.dualBasis.exteriorPower n` and `(b.exteriorPower n).dualBasis`, and
* **`exteriorPower.coe_pairingDualEquiv`** — its identification with the underlying
  `pairingDual` linear map, so the equiv is `pairingDual` upgraded in place.

This is Phase 21a's second deliverable, the projective-duality dictionary entry
`⋀ʲ(V*) ≃ (⋀ʲ V)*` reused by the Crapo–Whiteley invariance of Phase 25.

Promotion to mathlib: the `Unique` instance, `topEquiv`, and `pairingDualEquiv`
copy-paste into `Mathlib/LinearAlgebra/ExteriorPower/Basis.lean` (which already
supplies `Module.Basis.exteriorPower`, `finrank_eq`, and the `pairingDual` /
`ιMultiDual` API); the Lean namespaces (`Set.powersetCard`, `exteriorPower`) match
upstream conventions.

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

section PairingDual

open Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  {ι : Type*} [LinearOrder ι] [Finite ι] (b : Module.Basis ι R M)

/-- For a finite free module `M` with ordered basis `b`, the canonical map
`exteriorPower.pairingDual` from the exterior power of the dual to the dual of the
exterior power is an isomorphism `⋀ⁿ (Module.Dual R M) ≃ₗ Module.Dual R (⋀ⁿ M)`.
Built as the `Basis.equiv` carrying the exterior-power basis of the dual basis
`b.dualBasis` onto the dual basis of the exterior-power basis of `b`; that this
`Basis.equiv` *is* `pairingDual` is `coe_pairingDualEquiv`. The projective-duality
dictionary entry `⋀ʲ(V*) ≃ (⋀ʲ V)*`. -/
noncomputable def pairingDualEquiv (n : ℕ) :
    ⋀[R]^n (Module.Dual R M) ≃ₗ[R] Module.Dual R (⋀[R]^n M) :=
  (b.dualBasis.exteriorPower n).equiv ((b.exteriorPower n).dualBasis) (Equiv.refl _)

/-- The `pairingDualEquiv` iso is exactly `exteriorPower.pairingDual` as a linear
map: the iso is `pairingDual` upgraded in place for finite free `M`. -/
theorem coe_pairingDualEquiv (n : ℕ) :
    (pairingDualEquiv b n : ⋀[R]^n (Module.Dual R M) →ₗ[R] Module.Dual R (⋀[R]^n M)) =
      pairingDual R M n := by
  apply Module.Basis.ext (b.dualBasis.exteriorPower n)
  intro s
  rw [pairingDualEquiv, LinearEquiv.coe_coe, Basis.equiv_apply, Equiv.refl_apply,
    Basis.coe_dualBasis, basis_coord, basis_apply, ιMultiDual, ιMulti_family,
    Basis.coe_dualBasis]
  rfl

end PairingDual

end exteriorPower
