/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# Upstream candidate: surjective pullback preserves dual linear independence

`LinearIndependent.map'` plus `LinearMap.dualMap_injective_of_surjective` plus
`LinearMap.ker_eq_bot` is a three-line chain, packaged here. The combinatorial-rigidity
project meets it when it restricts a placement along an injective vertex map: the
restriction is `LinearMap.funLeft`, surjective by injectivity of the vertex map, so its
dual is injective and keeps linearly independent rows independent
(`linearIndependent_rigidityRow_lift_of_injective`, `RigidityMatroid.lean`).

Promotion to mathlib: copy-paste into `Mathlib/LinearAlgebra/Dual/Lemmas.lean`
(or any file that imports both `Dual.Defs` and `LinearIndependent.Basic`); the
namespaces (`LinearIndependent`, `LinearIndepOn`) match upstream conventions.

See `DESIGN.md` *Mirror directory*.
-/

@[expose] public section

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
