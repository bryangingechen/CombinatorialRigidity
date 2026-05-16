/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.StdBasis

/-!
# Upstream candidates: standard-basis-dual lemmas and the constructive
row-rank-equals-column-rank identity.

Two facts adjacent to `Module.Basis.dualBasis` and `LinearMap.dualMap` that
the combinatorial-rigidity project needed and that mathlib does not ship:

1. **`Pi.basisFun_dualBasis`** identifies the dual-basis-of-the-standard-basis
   on `η → R` with the coordinate projection: the chain
   `Basis.coe_dualBasis ∘ Basis.coord_apply ∘ Pi.basisFun_repr` discharges the
   pointwise equality, but mathlib does not package the equation between linear
   maps directly. (Neither `Mathlib.LinearAlgebra.StdBasis` nor
   `Mathlib.LinearAlgebra.Dual.Basis` carries this lemma; `Dual/Basis.lean` does
   not even import `StdBasis.lean`.)

2. **`LinearMap.range_dualMap_eq_span_image_dualBasis`** is the constructive
   (span) form of row-rank-equals-column-rank: for any basis `b` on the
   codomain, the range of `f.dualMap` is the `R`-linear span of
   `f.dualMap '' (range b.dualBasis)`. Mathlib's
   `LinearMap.finrank_range_dualMap_eq_finrank_range` is the
   *dimension-level* statement of the same fact (Part 1 of Strang's
   Fundamental Theorem of Linear Algebra); the underlying span identity that
   *implies* it is missing.

Promotion to mathlib: copy-paste into `Mathlib/LinearAlgebra/Dual/Basis.lean`,
adding the `import Mathlib.LinearAlgebra.StdBasis` line. The Lean namespaces
(`Pi`, `LinearMap`) match upstream conventions.

See `notes/FRICTION.md` *Mirrored* and `DESIGN.md` *Mirror directory*.
-/

@[expose] public section

namespace Pi

variable {R η : Type*} [CommSemiring R] [Finite η] [DecidableEq η]

/-- The `i`th dual-basis element of the standard basis on `η → R` is the
`i`th coordinate projection. -/
@[simp]
theorem basisFun_dualBasis (i : η) :
    (Pi.basisFun R η).dualBasis i = (LinearMap.proj i : (η → R) →ₗ[R] R) := by
  refine LinearMap.ext fun x => ?_
  simp [Pi.basisFun_repr]

end Pi

namespace LinearMap

variable {ι R M N : Type*} [CommSemiring R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [Finite ι] [DecidableEq ι]

/-- **Row-rank-equals-column-rank, constructive form.** The range of the dual
map `f.dualMap` is the `R`-linear span of the family
`fun i ↦ f.dualMap (b.dualBasis i)` for any basis `b` on the codomain.

Combined with `LinearMap.finrank_range_dualMap_eq_finrank_range` this is the
span-form precursor to Part 1 of Strang's Fundamental Theorem of Linear
Algebra (row rank = column rank). -/
theorem range_dualMap_eq_span_image_dualBasis (b : Module.Basis ι R N)
    (f : M →ₗ[R] N) :
    LinearMap.range f.dualMap =
      Submodule.span R (Set.range (f.dualMap ∘ b.dualBasis)) := by
  rw [Set.range_comp, Submodule.span_image, b.dualBasis.span_eq, Submodule.map_top]

end LinearMap
