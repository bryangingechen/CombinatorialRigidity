/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# Upstream candidate: surjective pullback preserves dual linear independence

`LinearIndependent.map'` plus `LinearMap.dualMap_injective_of_surjective` plus
`LinearMap.ker_eq_bot` is a three-line chain that recurs whenever the rigidity
project restricts a placement along an injective vertex map: the framework
restriction is `LinearMap.funLeft`, surjective by injectivity of the vertex map,
so its dual is injective and pulls linear independence back through the dual.
Both Phase 6's `isSparse_of_edgeSetRowIndependent_dim_two` and Phase 7's
`typeI_edgeSetRowIndependent_extend` build this chain by hand; the `LinearIndepOn`
form folds straight into a `LinearIndepOn.union` partition.

Promotion to mathlib: copy-paste into `Mathlib/LinearAlgebra/Dual/Lemmas.lean`
(or any file that imports both `Dual.Defs` and `LinearIndependent.Basic`); the
namespaces (`LinearIndependent`, `LinearIndepOn`) match upstream conventions.

See `notes/FRICTION.md` *Mirrored* and `DESIGN.md` *Mirror directory*.
-/

namespace LinearIndependent

variable {R M N ι : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A surjective linear map `f : M →ₗ[R] N` pulls a linearly independent family of
dual vectors on `N` back to a linearly independent family of dual vectors on `M`
through `f.dualMap`. -/
theorem dualMap_of_surjective {f : M →ₗ[R] N} (hf : Function.Surjective f)
    {v : ι → Module.Dual R N} (hv : LinearIndependent R v) :
    LinearIndependent R (f.dualMap ∘ v) :=
  hv.map' _ (LinearMap.ker_eq_bot.mpr (LinearMap.dualMap_injective_of_surjective hf))

end LinearIndependent

namespace LinearIndepOn

variable {R M N ι : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- `LinearIndepOn` version of `LinearIndependent.dualMap_of_surjective`. -/
theorem dualMap_of_surjective {f : M →ₗ[R] N} (hf : Function.Surjective f)
    {v : ι → Module.Dual R N} {s : Set ι} (hv : LinearIndepOn R v s) :
    LinearIndepOn R (f.dualMap ∘ v) s :=
  LinearIndependent.dualMap_of_surjective hf hv

end LinearIndepOn
