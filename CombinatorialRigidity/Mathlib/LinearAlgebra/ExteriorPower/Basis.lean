/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.Determinant
public import CombinatorialRigidity.Mathlib.Data.Finset.Sort

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

Promotion to mathlib: the `Unique` instance, `topEquiv`, `pairingDualEquiv`, and the
volume-form change-of-variables fact `topEquiv_map_eq_det_smul` (`topEquiv (map n f X)
= det f • topEquiv X`, the standard "`⋀ⁿ f = det f`" identity on `Fin n → R`) copy-paste
into `Mathlib/LinearAlgebra/ExteriorPower/Basis.lean` (which already supplies
`Module.Basis.exteriorPower`, `finrank_eq`, and the `pairingDual` / `ιMultiDual` API);
the Lean namespaces (`Set.powersetCard`, `exteriorPower`) match upstream conventions.

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

/-- `topEquiv` reads off the single coordinate of its argument with respect to the
top-power basis `(Pi.basisFun R (Fin n)).exteriorPower n` (whose index
`Set.powersetCard (Fin n) n` is a singleton, `default = Finset.univ`): it is the
`default`-coordinate of the basis representation. Definitional unfolding of
`topEquiv = equivFun ≪≫ funUnique`. -/
theorem topEquiv_eq_repr_default (X : ⋀[R]^n (Fin n → R)) :
    topEquiv (R := R) n X = ((Pi.basisFun R (Fin n)).exteriorPower n).repr X default := by
  unfold topEquiv; rfl

/-- `topEquiv` sends the image under `exteriorPower.map n f` of the canonical
top-power generator `e₀ ∧ ⋯ ∧ e_{n−1}` to the determinant of `f`. Computed by
unfolding `topEquiv` to the `default`-coordinate (`topEquiv_eq_repr_default`,
`basis_repr_apply`, `ιMultiDual_apply_ιMulti`), at which point the coordinate is the
determinant of the matrix `(eₛⱼ-coordinate of f(eₛᵢ))` (with `s = default`, so the
index reordering `Set.powersetCard.ofFinEmbEquiv.symm default` is the identity by
`Finset.orderEmbOfFin_unique`); that matrix is the transpose of `LinearMap.toMatrix' f`,
whose determinant is `LinearMap.det f` (`LinearMap.det_toMatrix'`, `Matrix.det_transpose`).
The generator computation behind the linear-extension `topEquiv_map_eq_det_smul`. -/
theorem topEquiv_map_ιMulti_family_default_eq_det
    (f : (Fin n → R) →ₗ[R] (Fin n → R)) :
    topEquiv (R := R) n
        (exteriorPower.map n f
          (exteriorPower.ιMulti_family R n (Pi.basisFun R (Fin n)) default))
      = LinearMap.det f := by
  rw [map_apply_ιMulti_family, topEquiv_eq_repr_default, basis_repr_apply,
    ιMulti_family, ιMultiDual_apply_ιMulti]
  have hsig : ∀ i : Fin n,
      (Set.powersetCard.ofFinEmbEquiv.symm (default : Set.powersetCard (Fin n) n)) i = i := by
    intro i
    rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
    -- `↑default = univ` is `rfl` but not syntactically present; surface it, then the
    -- mirrored `Finset.univ_orderEmbOfFin` collapses the increasing enumeration to `id`.
    have hd : ((default : Set.powersetCard (Fin n) n) : Finset (Fin n)) = Finset.univ := rfl
    simp only [hd, Finset.univ_orderEmbOfFin, id_eq]
  rw [← LinearMap.det_toMatrix' f, ← Matrix.det_transpose]
  congr 1
  ext i j
  simp only [Matrix.of_apply, Function.comp_apply, hsig, Matrix.transpose_apply,
    LinearMap.toMatrix'_apply, Basis.coord_apply, Pi.basisFun_apply, Pi.basisFun_repr]

/-- **The top exterior power transforms by the determinant** (the volume-form change-
of-variables fact, OD-8 sub-leaf (h-0) of the `complementIso` O(n)-equivariance). For
an endomorphism `f` of `Fin n → R`, the induced map on the top exterior power
`exteriorPower.map n f` followed by the volume form `topEquiv` scales by the
determinant of `f`: `topEquiv (map n f X) = (det f) • topEquiv X` for every
`X : ⋀ⁿ (Fin n → R)`. Both sides are `R`-linear in `X`; they agree on the single
top-power basis generator (`topEquiv_map_ιMulti_family_default_eq_det` plus
`topEquiv_ιMulti_family_default = 1`), hence everywhere by `Basis.ext`. The classical
"`⋀ⁿ f = det f`" identity, specialised to the standard carrier. -/
theorem topEquiv_map_eq_det_smul (f : (Fin n → R) →ₗ[R] (Fin n → R))
    (X : ⋀[R]^n (Fin n → R)) :
    topEquiv (R := R) n (exteriorPower.map n f X)
      = (LinearMap.det f) • topEquiv (R := R) n X := by
  suffices h : (topEquiv (R := R) n).toLinearMap ∘ₗ exteriorPower.map n f
      = (LinearMap.det f) • (topEquiv (R := R) n).toLinearMap by
    have := LinearMap.congr_fun h X; simpa using this
  apply Basis.ext ((Pi.basisFun R (Fin n)).exteriorPower n)
  intro s
  obtain rfl := Subsingleton.elim s default
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, basis_apply,
    LinearMap.smul_apply, smul_eq_mul]
  rw [topEquiv_map_ιMulti_family_default_eq_det, topEquiv_ιMulti_family_default, mul_one]

/-- Two `ExteriorAlgebra.ιMulti_family` wedges over the same family `v` agree whenever
their cardinalities and their underlying finsets agree. The `m = n` cardinality cast
(absent from the bare `ιMulti_family` API, whose index `s` lives in
`Set.powersetCard I m`) packaged so a wedge of a `Set.powersetCard`-glued index — e.g.
the `disjUnion` of two complementary subsets at cardinality `j + (n - j)` — can be
identified with one at the literal cardinality `n`. -/
theorem _root_.ExteriorAlgebra.ιMulti_family_congr {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {I : Type*} [LinearOrder I] {m n : ℕ} (hmn : m = n)
    (v : I → M) (s : Set.powersetCard I m) (t : Set.powersetCard I n)
    (hst : (s : Finset I) = (t : Finset I)) :
    ExteriorAlgebra.ιMulti_family R m v s = ExteriorAlgebra.ιMulti_family R n v t := by
  subst hmn
  exact congrArg _ (Subtype.ext hst)

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
