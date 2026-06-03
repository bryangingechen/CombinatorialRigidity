/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Mathlib.LinearAlgebra.ExteriorPower.Basis
public import CombinatorialRigidity.Molecular.Extensor

/-!
# Grassmann–Cayley meet / projective-duality foundations (`sec:molecular-meet`)

Phase 21a, a prerequisite sub-phase of the algebraic induction (Phase 21), inserted by
the 2026-06-03 panel re-scope. Where Phase 17 (`Molecular/Extensor.lean`) built the
*join* (progressive product `∨ₑ`, the symbolic exterior product on
`ExteriorAlgebra ℝ (Fin (k+2) → ℝ)`) plus a coordinatized Plücker bridge, this file
builds the dual half — the *meet* (regressive product) and the projective-duality
dictionary it rests on — on the same concrete carrier. The meet is the device the
panel-coplanarity layer (DESIGN.md *Panel-hinge = hinge-coplanar body-hinge*), the
cycle-realization Lemma 5.4, and the Crapo–Whiteley projective invariance (Phase 25)
all consume; see `notes/Phase21a.md` for the deliverable plan and `notes/MolecularConjecture.md`
for the program-level placement.

The construction is metric-free: projective geometry needs no inner product, only the
top-power volume form (orientation). Deliverables, in dependency order
(`N = k+2`, `V = Fin (k+2) → ℝ`):

1. **`topEquiv`** (this commit) — the canonical top-power iso `⋀ᴺ V ≃ₗ ℝ`. The
   orientation through which the perfect wedge pairing lands in `ℝ`. Mirrored as the
   general fact `exteriorPower.topEquiv` (over any `CommRing`, on `Fin n → R`) under
   `Mathlib/LinearAlgebra/ExteriorPower/Basis.lean`; `screwAlgebraTopEquiv` below is the
   `N = k+2` specialization on the screw-algebra carrier.
2. **`pairingDualEquiv`** (this commit) — the projective-duality dictionary entry
   `⋀ʲ(V*) ≃ₗ (⋀ʲ V)*` reused by Phase 25, the upgrade of mathlib's
   `exteriorPower.pairingDual` (a bare `→ₗ`) to an iso for finite free `V`. Mirrored
   as the general fact `exteriorPower.pairingDualEquiv` (over any `CommRing`, for any
   finite free `M` with an ordered basis) under
   `Mathlib/LinearAlgebra/ExteriorPower/Basis.lean`; `screwAlgebraPairingDualEquiv`
   below is the screw-algebra specialization at the standard basis.
3. `complementIso : ⋀ʲ V ≃ₗ ⋀^(N−j) V` — from the perfect wedge pairing, shown
   nondegenerate. The genuinely new core.
4. `meet` (regressive product) + `meet_ne_zero_iff` and the geometric reading.

## Carrier

The full exterior algebra `ExteriorAlgebra ℝ (Fin (k+2) → ℝ)` of Phase 17 (the
`affineSubspaceExtensor` / join carrier). The top graded piece is
`⋀[ℝ]^(k+2) (Fin (k+2) → ℝ)`, free of rank `(k+2).choose (k+2) = 1`, hence
`≃ₗ ℝ` — the volume form.
-/

@[expose] public section

namespace CombinatorialRigidity.Molecular

variable (k : ℕ)

/-- The canonical top-power volume-form iso `⋀^(k+2) (Fin (k+2) → ℝ) ≃ₗ ℝ` on the
screw-algebra carrier of Phase 17, the `N = k+2` specialization of the general mirror
`exteriorPower.topEquiv`. The orientation through which the perfect wedge pairing
`⋀ʲ V × ⋀^(N−j) V → ⋀ᴺ V` lands in `ℝ`, on which the regressive product `meet` is built.
Metric-free: no inner product, only the volume form. -/
noncomputable def screwAlgebraTopEquiv :
    ⋀[ℝ]^(k + 2) (Fin (k + 2) → ℝ) ≃ₗ[ℝ] ℝ :=
  exteriorPower.topEquiv (k + 2)

/-- The projective-duality dictionary iso on the screw-algebra carrier:
`⋀ʲ((Fin (k+2) → ℝ)*) ≃ₗ (⋀ʲ (Fin (k+2) → ℝ))*`, the `j`-graded specialization of the
general mirror `exteriorPower.pairingDualEquiv` at the standard basis. This is the
projective-duality dictionary entry `⋀ʲ(V*) ≃ (⋀ʲ V)*` reused by the Crapo–Whiteley
projective invariance of Phase 25; it is mathlib's bare `exteriorPower.pairingDual`
upgraded in place to an iso (`exteriorPower.coe_pairingDualEquiv`). -/
noncomputable def screwAlgebraPairingDualEquiv (j : ℕ) :
    ⋀[ℝ]^j (Module.Dual ℝ (Fin (k + 2) → ℝ)) ≃ₗ[ℝ]
      Module.Dual ℝ (⋀[ℝ]^j (Fin (k + 2) → ℝ)) :=
  exteriorPower.pairingDualEquiv (Pi.basisFun ℝ (Fin (k + 2))) j

end CombinatorialRigidity.Molecular
