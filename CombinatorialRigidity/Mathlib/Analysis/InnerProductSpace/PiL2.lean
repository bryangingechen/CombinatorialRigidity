/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Upstream candidates: the L² inner product on `EuclideanSpace ℝ ι` as the
standard-basis `toDual` pairing, and the `toDual`-orthogonal transport of an
L²-isometry.

Two facts relating the analytic L²-metric structure of `EuclideanSpace ℝ ι` to
the purely algebraic `Module.Basis.toDual` pairing of the standard basis on the
bare carrier `ι → ℝ`, which mathlib does not package:

1. **`EuclideanSpace.inner_eq_basisFun_toDual`** identifies the real L² inner
   product `⟪a, b⟫` on `EuclideanSpace ℝ ι` with the standard-basis self-pairing
   `(Pi.basisFun ℝ ι).toDual` evaluated on the underlying functions (both equal
   the dot product `∑ i, a i * b i`). `EuclideanSpace.inner_eq_star_dotProduct`
   gives the inner-product-as-dot-product half; `Module.Basis.toDual_apply_left`
   handles a single basis argument; the bridge between the two notions of "dot
   product" — analytic and algebraic — is not packaged.

2. **`EuclideanSpace.toDualOrthogonal_ofLinearIsometryEquiv`** is the transport
   corollary: a linear isometry equiv `L` of `EuclideanSpace ℝ ι` (preserving the
   L² inner product) carries over, along the carrier iso `EuclideanSpace.equiv`,
   to a linear automorphism of `ι → ℝ` (`EuclideanSpace.ofLinearIsometryEquiv L`)
   that preserves the `(Pi.basisFun ℝ ι).toDual` pairing. This converts mathlib's
   metric notion of "orthogonal" (an L²-isometry) into the basis-bilinear-form
   notion used by purely-algebraic exterior-algebra developments.

Promotion to mathlib: copy-paste into `Mathlib/Analysis/InnerProductSpace/PiL2.lean`.
The Lean namespace (`EuclideanSpace`) matches the upstream convention.

See `notes/FRICTION.md` *Mirrored* and `DESIGN.md` *Mirror directory*.
-/

@[expose] public section

namespace EuclideanSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The real L² inner product on `EuclideanSpace ℝ ι` is the standard-basis
`Module.Basis.toDual` self-pairing of the underlying functions: both equal the
coordinate dot product `∑ i, a i * b i`. -/
theorem inner_eq_basisFun_toDual (a b : EuclideanSpace ℝ ι) :
    (inner ℝ a b : ℝ)
      = (Pi.basisFun ℝ ι).toDual
          ((EuclideanSpace.equiv ι ℝ) a) ((EuclideanSpace.equiv ι ℝ) b) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  rw [show (Pi.basisFun ℝ ι).toDual ((EuclideanSpace.equiv ι ℝ) a) ((EuclideanSpace.equiv ι ℝ) b)
      = ∑ i, ((EuclideanSpace.equiv ι ℝ) a) i * ((EuclideanSpace.equiv ι ℝ) b) i from by
        conv_lhs => rw [← (Pi.basisFun ℝ ι).sum_repr ((EuclideanSpace.equiv ι ℝ) b), map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, smul_eq_mul, Module.Basis.toDual_apply_left, Pi.basisFun_repr,
          Pi.basisFun_repr, mul_comm]]
  simp [dotProduct, mul_comm]

/-- Transport a linear isometry equiv of `EuclideanSpace ℝ ι` to a linear
automorphism of the bare carrier `ι → ℝ`, along the carrier iso
`EuclideanSpace.equiv ι ℝ` (which is the identity on the underlying functions).
The underlying map is the *same* function, merely re-typed off the `PiLp 2`
metric refinement; `toDualOrthogonal_ofLinearIsometryEquiv` records that it
preserves the standard-basis `toDual` pairing. -/
noncomputable def ofLinearIsometryEquiv
    (L : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) :=
  (EuclideanSpace.equiv ι ℝ).symm.toLinearEquiv.trans
    (L.toLinearEquiv.trans (EuclideanSpace.equiv ι ℝ).symm.toLinearEquiv.symm)

/-- The transport `ofLinearIsometryEquiv L` of an L²-isometry preserves the
standard-basis `Module.Basis.toDual` pairing on `ι → ℝ`. This converts the
metric "orthogonal" (L²-isometry) into the basis-bilinear-form "orthogonal":
on `EuclideanSpace ℝ ι` the inner product *is* the `toDual` dot-product pairing
(`inner_eq_basisFun_toDual`), so `L`'s isometry property `L.inner_map_map` reads
off directly through the carrier round-trip. -/
theorem toDualOrthogonal_ofLinearIsometryEquiv
    (L : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) (x y : ι → ℝ) :
    (Pi.basisFun ℝ ι).toDual (ofLinearIsometryEquiv L x) (ofLinearIsometryEquiv L y)
      = (Pi.basisFun ℝ ι).toDual x y := by
  set ε : (ι → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ ι :=
    (EuclideanSpace.equiv ι ℝ).symm.toLinearEquiv with hε
  have bridge : ∀ a b : EuclideanSpace ℝ ι,
      (inner ℝ a b : ℝ) = (Pi.basisFun ℝ ι).toDual (ε.symm a) (ε.symm b) := by
    intro a b
    rw [inner_eq_basisFun_toDual]; rfl
  have happ : ∀ z, ofLinearIsometryEquiv L z = ε.symm (L (ε z)) := fun _ => rfl
  rw [happ, happ, ← bridge, L.inner_map_map, bridge, ε.symm_apply_apply, ε.symm_apply_apply]

end EuclideanSpace
