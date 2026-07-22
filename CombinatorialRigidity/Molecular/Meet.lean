/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Mathlib.LinearAlgebra.ExteriorPower.Basis
public import CombinatorialRigidity.Mathlib.LinearAlgebra.Dual.Basis
public import CombinatorialRigidity.Mathlib.Data.Finset.Card
public import CombinatorialRigidity.Molecular.Extensor
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Grassmann–Cayley meet / projective-duality foundations (`sec:molecular-meet`)

Phase 21a, a prerequisite sub-phase of the algebraic induction (Phase 21), inserted by
the 2026-06-03 panel re-scope. Where Phase 17 (`Molecular/Extensor.lean`) built the
*join* (progressive product `∨ₑ`, the symbolic exterior product on
`ExteriorAlgebra K (Fin (k+2) → K)`) plus a coordinatized Plücker bridge, this file
builds the dual half — the *meet* (regressive product) and the projective-duality
dictionary it rests on — on the same concrete carrier. The meet is the device the
panel-coplanarity layer (DESIGN.md *Panel-hinge = hinge-coplanar body-hinge*), the
cycle-realization Lemma 5.4, and the Crapo–Whiteley projective invariance (Phase 25)
all consume; see `notes/Phase21a.md` for the deliverable plan and `notes/MolecularConjecture.md`
for the program-level placement.

**Field generality (Phase 33 G1 sweep, Slice 3).** The construction is pure exterior/projective
algebra with no metric, order, or infiniteness content, so it holds over any field `K`
(`variable {K : Type*} [Field K]`, threaded throughout; no characteristic restriction —
originally developed over `ℝ`, Phases 17–26). This is the `K`-generalization of the metric-free
route Spike A (`notes/Phase33.md`) landed at Slice 0: the GL-contragredient equivariance
(`complementIso_map_contragredient_eq`) and the field-general `toDual`-perp count
(`finrank_toDualPerp_pair_eq`) replace the retired `MeetHodge.lean`'s Gram–Schmidt / O(n)-only
route, so no field-specific step remains anywhere in the file.

The construction is metric-free: projective geometry needs no inner product, only the
top-power volume form (orientation). Deliverables, in dependency order
(`N = k+2`, `V = Fin (k+2) → K`):

1. **`topEquiv`** (this commit) — the canonical top-power iso `⋀ᴺ V ≃ₗ K`. The
   orientation through which the perfect wedge pairing lands in `K`. Mirrored as the
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

The full exterior algebra `ExteriorAlgebra K (Fin (k+2) → K)` of Phase 17 (the
`affineSubspaceExtensor` / join carrier). The top graded piece is
`⋀[K]^(k+2) (Fin (k+2) → K)`, free of rank `(k+2).choose (k+2) = 1`, hence
`≃ₗ K` — the volume form.
-/

@[expose] public section

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] (k : ℕ)

/-- The canonical top-power volume-form iso `⋀^(k+2) (Fin (k+2) → K) ≃ₗ K` on the
screw-algebra carrier of Phase 17, the `N = k+2` specialization of the general mirror
`exteriorPower.topEquiv`. The orientation through which the perfect wedge pairing
`⋀ʲ V × ⋀^(N−j) V → ⋀ᴺ V` lands in `K`, on which the regressive product `meet` is built.
Metric-free: no inner product, only the volume form. -/
noncomputable def screwAlgebraTopEquiv :
    ⋀[K]^(k + 2) (Fin (k + 2) → K) ≃ₗ[K] K :=
  exteriorPower.topEquiv (k + 2)

/-- **The volume form transforms by the determinant under `exteriorPower.map`** (OD-8
sub-leaf (h-0), the change-of-variables fact behind the `complementIso`
O(n)-equivariance (h-1)). For an endomorphism `f` of `K^{k+2}`, the screw-algebra
volume form `screwAlgebraTopEquiv` post-composed with the induced top-power map
`exteriorPower.map (k+2) f` scales by `LinearMap.det f`:
`screwAlgebraTopEquiv (map (k+2) f X) = (det f) • screwAlgebraTopEquiv X`. The `N = k+2`
specialization of the general mirror `exteriorPower.topEquiv_map_eq_det_smul`. Since
`complementIso` is built from `screwAlgebraTopEquiv` (the volume form) and the standard
dot product (`Pi.basisFun.toDual`) — i.e. it *is* the Hodge star `⋆` — this is one of
the two transformation laws (volume-by-det and dot-product O-invariance) from which the
panel-meet `complementIso` inherits its O(n)-equivariance. -/
theorem screwAlgebraTopEquiv_map_eq_det_smul (f : (Fin (k + 2) → K) →ₗ[K] (Fin (k + 2) → K))
    (X : ⋀[K]^(k + 2) (Fin (k + 2) → K)) :
    screwAlgebraTopEquiv k (exteriorPower.map (k + 2) f X)
      = (LinearMap.det f) • screwAlgebraTopEquiv k X :=
  exteriorPower.topEquiv_map_eq_det_smul (k + 2) f X

/-- The projective-duality dictionary iso on the screw-algebra carrier:
`⋀ʲ((Fin (k+2) → K)*) ≃ₗ (⋀ʲ (Fin (k+2) → K))*`, the `j`-graded specialization of the
general mirror `exteriorPower.pairingDualEquiv` at the standard basis. This is the
projective-duality dictionary entry `⋀ʲ(V*) ≃ (⋀ʲ V)*` reused by the Crapo–Whiteley
projective invariance of Phase 25; it is mathlib's bare `exteriorPower.pairingDual`
upgraded in place to an iso (`exteriorPower.coe_pairingDualEquiv`). -/
noncomputable def screwAlgebraPairingDualEquiv (j : ℕ) :
    ⋀[K]^j (Module.Dual K (Fin (k + 2) → K)) ≃ₗ[K]
      Module.Dual K (⋀[K]^j (Fin (k + 2) → K)) :=
  exteriorPower.pairingDualEquiv (Pi.basisFun K (Fin (k + 2))) j

/-! ## The graded wedge product `⋀ʲ V × ⋀^(N−j) V → ⋀ᴺ V`

The first ingredient of the perfect wedge pairing on which `complementIso`
(`def:meet-complement-iso`) and the regressive product `meet` (`def:meet`) are
built (route (ii); `notes/Phase21a.md`). It is the join (Phase 17, the symbolic
exterior product in the full `ExteriorAlgebra`) landed back in the *top* graded
piece `⋀^(k+2) V` via the graded-monoid structure `SetLike.GradedMonoid` on
`fun i ↦ ⋀^i V`: the product of a `j`-graded and an `(N−j)`-graded element is
`(j + (N−j)) = N`-graded. Composing with the volume form `screwAlgebraTopEquiv`
sends it into `K`, the pairing whose nondegeneracy is the next deliverable. -/

variable {k}

/-- The graded wedge product `⋀ʲ V × ⋀^(N−j) V → ⋀ᴺ V` (`N = k+2`): the join /
exterior product of `A` and `B`, landed in the *top* graded piece via the graded
monoid structure on `fun i ↦ ⋀^i V`. The bilinear ingredient of the perfect wedge
pairing on which `complementIso` (`def:meet-complement-iso`) is built; on extensors
it agrees with the Phase-17 `join` (`coe_wedgeProd`). -/
noncomputable def wedgeProd {j : ℕ} (hj : j ≤ k + 2)
    (A : ⋀[K]^j (Fin (k + 2) → K)) (B : ⋀[K]^(k + 2 - j) (Fin (k + 2) → K)) :
    ⋀[K]^(k + 2) (Fin (k + 2) → K) := by
  refine ⟨(A : ExteriorAlgebra K (Fin (k + 2) → K)) * (B : ExteriorAlgebra K (Fin (k + 2) → K)), ?_⟩
  have h : j + (k + 2 - j) = k + 2 := by omega
  have := SetLike.mul_mem_graded A.2 B.2
  rwa [h] at this

/-- The underlying exterior-algebra element of `wedgeProd` is the join (Phase-17
`∨ₑ`, the full-algebra exterior product) of the two factors: `wedgeProd` is the
join landed in the top graded piece. The bridge from the meet's graded pairing to
the Phase-17 join API. -/
@[simp]
theorem coe_wedgeProd {j : ℕ} (hj : j ≤ k + 2)
    (A : ⋀[K]^j (Fin (k + 2) → K)) (B : ⋀[K]^(k + 2 - j) (Fin (k + 2) → K)) :
    (wedgeProd hj A B : ExteriorAlgebra K (Fin (k + 2) → K)) =
      (A : ExteriorAlgebra K (Fin (k + 2) → K)) ∨ₑ
        (B : ExteriorAlgebra K (Fin (k + 2) → K)) :=
  rfl

/-! ## The perfect wedge pairing `⋀ʲ V →ₗ Dual K (⋀^(N−j) V)`

The bilinear ingredient (b) of the perfect wedge pairing on which `complementIso`
(`def:meet-complement-iso`) is built (route (ii); `notes/Phase21a.md`). The graded
wedge product `wedgeProd` is bilinear — its underlying element `↑A * ↑B` is bilinear
in the full algebra, and the subtype inclusion `⋀ᴺ V ↪ ExteriorAlgebra` is a linear
map, so `wedgeProd` inherits bilinearity (`wedgeProdBilin`). Composing the second
slot with the volume form `screwAlgebraTopEquiv : ⋀ᴺ V ≃ₗ K` lands the pairing in
`K`, giving `wedgePairing j : ⋀ʲ V →ₗ Dual K (⋀^(N−j) V)`, `A ↦ B ↦
screwAlgebraTopEquiv (wedgeProd A B)`. Its nondegeneracy (the signed-permutation
basis computation) is the next ingredient; `complementIso` is then `wedgePairing`
as an equiv composed with `toDualEquiv.symm`. -/

/-- `wedgeProd` is additive in its first slot: the underlying product `↑A * ↑B` is
additive in `↑A` and the subtype inclusion `⋀ᴺ V ↪ ExteriorAlgebra` is linear. -/
theorem wedgeProd_add_left {j : ℕ} (hj : j ≤ k + 2)
    (A A' : ⋀[K]^j (Fin (k + 2) → K)) (B : ⋀[K]^(k + 2 - j) (Fin (k + 2) → K)) :
    wedgeProd hj (A + A') B = wedgeProd hj A B + wedgeProd hj A' B := by
  apply Subtype.ext
  simp [wedgeProd, add_mul]

/-- `wedgeProd` is additive in its second slot. -/
theorem wedgeProd_add_right {j : ℕ} (hj : j ≤ k + 2)
    (A : ⋀[K]^j (Fin (k + 2) → K)) (B B' : ⋀[K]^(k + 2 - j) (Fin (k + 2) → K)) :
    wedgeProd hj A (B + B') = wedgeProd hj A B + wedgeProd hj A B' := by
  apply Subtype.ext
  simp [wedgeProd, mul_add]

/-- `wedgeProd` is `K`-homogeneous in its first slot. -/
theorem wedgeProd_smul_left {j : ℕ} (hj : j ≤ k + 2) (c : K)
    (A : ⋀[K]^j (Fin (k + 2) → K)) (B : ⋀[K]^(k + 2 - j) (Fin (k + 2) → K)) :
    wedgeProd hj (c • A) B = c • wedgeProd hj A B := by
  apply Subtype.ext
  simp [wedgeProd]

/-- `wedgeProd` is `K`-homogeneous in its second slot. -/
theorem wedgeProd_smul_right {j : ℕ} (hj : j ≤ k + 2) (c : K)
    (A : ⋀[K]^j (Fin (k + 2) → K)) (B : ⋀[K]^(k + 2 - j) (Fin (k + 2) → K)) :
    wedgeProd hj A (c • B) = c • wedgeProd hj A B := by
  apply Subtype.ext
  simp [wedgeProd]

/-- The graded wedge product `⋀ʲ V × ⋀^(N−j) V → ⋀ᴺ V` packaged as an `K`-bilinear
map. The `LinearMap.mk₂` bundling of `wedgeProd`, whose bilinearity is
`wedgeProd_{add,smul}_{left,right}`. -/
noncomputable def wedgeProdBilin {j : ℕ} (hj : j ≤ k + 2) :
    ⋀[K]^j (Fin (k + 2) → K) →ₗ[K]
      ⋀[K]^(k + 2 - j) (Fin (k + 2) → K) →ₗ[K] ⋀[K]^(k + 2) (Fin (k + 2) → K) :=
  LinearMap.mk₂ K (wedgeProd hj) (wedgeProd_add_left hj) (wedgeProd_smul_left hj)
    (wedgeProd_add_right hj) (wedgeProd_smul_right hj)

@[simp]
theorem wedgeProdBilin_apply {j : ℕ} (hj : j ≤ k + 2)
    (A : ⋀[K]^j (Fin (k + 2) → K)) (B : ⋀[K]^(k + 2 - j) (Fin (k + 2) → K)) :
    wedgeProdBilin hj A B = wedgeProd hj A B :=
  rfl

/-- The perfect wedge pairing `⋀ʲ V →ₗ Module.Dual K (⋀^(N−j) V)` (`N = k+2`):
`A ↦ B ↦ screwAlgebraTopEquiv (wedgeProd A B)`, the graded wedge product composed
with the top-power volume form `screwAlgebraTopEquiv : ⋀ᴺ V ≃ₗ K`. The bilinear
pairing whose nondegeneracy makes `complementIso` (`def:meet-complement-iso`) an
isomorphism; `Module.Dual K (⋀^(N−j) V) = (⋀^(N−j) V) →ₗ K` is the second-slot
codomain after the volume form. -/
noncomputable def wedgePairing (k : ℕ) {j : ℕ} (hj : j ≤ k + 2) :
    ⋀[K]^j (Fin (k + 2) → K) →ₗ[K]
      Module.Dual K (⋀[K]^(k + 2 - j) (Fin (k + 2) → K)) :=
  (wedgeProdBilin hj).compr₂ (screwAlgebraTopEquiv k).toLinearMap

@[simp]
theorem wedgePairing_apply {j : ℕ} (hj : j ≤ k + 2)
    (A : ⋀[K]^j (Fin (k + 2) → K)) (B : ⋀[K]^(k + 2 - j) (Fin (k + 2) → K)) :
    wedgePairing k hj A B = screwAlgebraTopEquiv k (wedgeProd hj A B) :=
  rfl

/-- **The graded wedge product is covariant under `exteriorPower.map`** (OD-8 sub-leaf,
the change-of-frame step behind the `complementIso` O(n)-equivariance (h-1)). For an
endomorphism `f` of `K^{k+2}`, transporting both factors of the graded wedge product by
the induced exterior-power maps and then taking the product is the same as taking the
product first and transporting by the top exterior-power map:
`wedgeProd (map j f A) (map (N−j) f B) = map N f (wedgeProd A B)`. The underlying
exterior-algebra elements are products `↑A * ↑B`, and the exterior-algebra morphism
`ExteriorAlgebra.map f` is multiplicative; the bridge `map_coe_eq_exteriorAlgebra_map`
pushes the per-grade `exteriorPower.map` through the product. -/
theorem wedgeProd_map {j : ℕ} (hj : j ≤ k + 2)
    (f : (Fin (k + 2) → K) →ₗ[K] (Fin (k + 2) → K))
    (A : ⋀[K]^j (Fin (k + 2) → K)) (B : ⋀[K]^(k + 2 - j) (Fin (k + 2) → K)) :
    wedgeProd hj (exteriorPower.map j f A) (exteriorPower.map (k + 2 - j) f B)
      = exteriorPower.map (k + 2) f (wedgeProd hj A B) := by
  apply Subtype.ext
  rw [coe_wedgeProd, join_def, exteriorPower.map_coe_eq_exteriorAlgebra_map,
    exteriorPower.map_coe_eq_exteriorAlgebra_map, ← map_mul,
    exteriorPower.map_coe_eq_exteriorAlgebra_map, coe_wedgeProd, join_def]

/-- **The perfect wedge pairing transforms by the determinant under `exteriorPower.map`**
(OD-8 sub-leaf, the algebraic core of the `complementIso` O(n)-equivariance (h-1)). For an
endomorphism `f` of `K^{k+2}`, transporting both factors of the wedge pairing by the
induced exterior-power maps scales the pairing by `LinearMap.det f`:
`wedgePairing (map j f A) (map (N−j) f B) = det f • wedgePairing A B`. Immediate from the
covariance of the graded wedge product (`wedgeProd_map`, the join transforms covariantly)
composed with the volume form's change-of-variables law
(`screwAlgebraTopEquiv_map_eq_det_smul`, sub-leaf (h-0)). Since `complementIso` is built
from this pairing and the standard dot product (`Pi.basisFun.toDual`), this is one of the
two transformation laws (volume-by-det and dot-product O-invariance) the panel-meet
`complementIso` inherits its O(n)-equivariance from. -/
theorem wedgePairing_map {j : ℕ} (hj : j ≤ k + 2)
    (f : (Fin (k + 2) → K) →ₗ[K] (Fin (k + 2) → K))
    (A : ⋀[K]^j (Fin (k + 2) → K)) (B : ⋀[K]^(k + 2 - j) (Fin (k + 2) → K)) :
    wedgePairing k hj (exteriorPower.map j f A) (exteriorPower.map (k + 2 - j) f B)
      = (LinearMap.det f) • wedgePairing k hj A B := by
  simp only [wedgePairing_apply, wedgeProd_map, screwAlgebraTopEquiv_map_eq_det_smul,
    smul_eq_mul]

/-! ## Nondegeneracy of the wedge pairing on the standard basis (ingredient (c))

The third ingredient of `complementIso` (`def:meet-complement-iso`): the perfect
wedge pairing `wedgePairing` is nondegenerate, computed on the standard
exterior-power basis. The basis of `⋀ʲ V` is indexed by the `j`-element subsets
`S : Set.powersetCard (Fin (k+2)) j`, with basis vector
`exteriorPower.ιMulti_family K j (Pi.basisFun …) S` — the wedge `e_{S₀} ∧ ⋯` of the
standard basis vectors indexed by `S` in increasing order; similarly the basis of
`⋀^(N−j) V` is indexed by `(N−j)`-element subsets `T`.

The pairing of two such basis vectors is `screwAlgebraTopEquiv (e_S ∨ₑ e_T)`. Since
the join is the exterior product of two extensors of standard basis vectors
(`join_extensor`, with `coe_wedgeProd`), it is the extensor of the concatenated
family `Fin.append (eₛ) (eₜ)`. That family is injective iff `S` and `T` are disjoint;
given `|S| = j` and `|T| = (k+2)−j`, disjointness is equivalent to `T = Sᶜ`. Hence:

* **off-diagonal** (`T ≠ Sᶜ`, this commit): `S, T` overlap, so the append family
  repeats a standard basis vector and the extensor vanishes
  (`extensor_eq_zero_of_not_injective`), giving pairing `= 0`;
* **diagonal** (`T = Sᶜ`): the append family is a permutation of all standard basis
  vectors, so the extensor is `±` the top basis vector and the pairing is `±1` (the
  permutation sign — the *open sign subproblem* of `notes/Phase21a.md`, deferred).
-/

/-- The underlying exterior-algebra element of the wedge product of two standard
exterior-power basis vectors is the extensor of the concatenated indexing family:
the join `e_S ∨ₑ e_T` is the `(k+2)`-extensor of `Fin.append` of the two ordered
families of standard basis vectors. The bridge from the graded pairing on basis
vectors to the Phase-17 single-extensor API, on which the disjointness ⇒ vanishing
computation runs. -/
theorem coe_wedgeProd_ιMulti_family {j : ℕ} (hj : j ≤ k + 2)
    (S : Set.powersetCard (Fin (k + 2)) j)
    (T : Set.powersetCard (Fin (k + 2)) (k + 2 - j)) :
    (wedgeProd hj (exteriorPower.ιMulti_family K j (Pi.basisFun K (Fin (k + 2))) S)
        (exteriorPower.ιMulti_family K (k + 2 - j) (Pi.basisFun K (Fin (k + 2))) T) :
        ExteriorAlgebra K (Fin (k + 2) → K)) =
      extensor (Fin.append
        (Pi.basisFun K (Fin (k + 2)) ∘ Set.powersetCard.ofFinEmbEquiv.symm S)
        (Pi.basisFun K (Fin (k + 2)) ∘ Set.powersetCard.ofFinEmbEquiv.symm T)) := by
  rw [coe_wedgeProd]
  change (extensor (Pi.basisFun K (Fin (k + 2)) ∘ Set.powersetCard.ofFinEmbEquiv.symm S))
      ∨ₑ (extensor (Pi.basisFun K (Fin (k + 2)) ∘ Set.powersetCard.ofFinEmbEquiv.symm T)) = _
  rw [join_extensor]

/-- **Off-diagonal vanishing of the wedge pairing** (ingredient (c), this commit).
If the indexing subsets `S` (size `j`) and `T` (size `(k+2)−j`) of the two standard
exterior-power basis vectors are *not* disjoint — equivalently, since they have
complementary sizes, `T ≠ Sᶜ` — then the wedge pairing of the basis vectors
vanishes. A shared index `x ∈ S ∩ T` makes the standard basis vector `eₓ` appear in
both factors of the concatenated family `Fin.append`, so the extensor vanishes by
the alternating law (`extensor_eq_zero_of_not_injective`) and the volume form sends
it to `0`. The complementary diagonal case (`T = Sᶜ`, value `±1`) is the open sign
subproblem of `notes/Phase21a.md`. -/
theorem wedgePairing_ιMulti_family_eq_zero_of_not_disjoint {j : ℕ} (hj : j ≤ k + 2)
    (S : Set.powersetCard (Fin (k + 2)) j)
    (T : Set.powersetCard (Fin (k + 2)) (k + 2 - j))
    (hST : ¬Disjoint (S : Finset (Fin (k + 2))) (T : Finset (Fin (k + 2)))) :
    wedgePairing k hj (exteriorPower.ιMulti_family K j (Pi.basisFun K (Fin (k + 2))) S)
        (exteriorPower.ιMulti_family K (k + 2 - j) (Pi.basisFun K (Fin (k + 2))) T) = 0 := by
  rw [wedgePairing_apply]
  have hzero : wedgeProd hj
      (exteriorPower.ιMulti_family K j (Pi.basisFun K (Fin (k + 2))) S)
      (exteriorPower.ιMulti_family K (k + 2 - j) (Pi.basisFun K (Fin (k + 2))) T) = 0 := by
    apply Subtype.ext
    rw [coe_wedgeProd_ιMulti_family, ZeroMemClass.coe_zero]
    -- the append family repeats the standard basis vector `eₓ` for `x ∈ S ∩ T`
    obtain ⟨x, hxS, hxT⟩ := Finset.not_disjoint_iff.mp hST
    obtain ⟨a, ha⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem S x).mpr hxS
    obtain ⟨b, hb⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem T x).mpr hxT
    apply extensor_eq_zero_of_eq _
      (a := Fin.castAdd (k + 2 - j) a) (b := Fin.natAdd j b)
    · simp only [Fin.append_left, Fin.append_right, Function.comp_apply, ha, hb]
    · refine Fin.ne_of_lt ?_
      simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
      have := a.isLt
      omega
  rw [hzero, map_zero]

/-- **Off-diagonal vanishing, complement form** (ingredient (c)). The `T ≠ Sᶜ`
restatement of `wedgePairing_ιMulti_family_eq_zero_of_not_disjoint`, matching the
`notes/Phase21a.md` deliverable shape "`±1` if `T = Sᶜ` else `0`": when the index `T`
is *not* the complement of `S` (using mathlib's complement equivalence
`Set.powersetCard.compl` on the complementary-cardinality subtypes), the two index
sets overlap (`Finset.disjoint_iff_eq_compl`), so the basis-vector pairing vanishes.
The complementary `T = Sᶜ` diagonal (value `±1`) is the open sign subproblem. -/
theorem wedgePairing_ιMulti_family_eq_zero_of_ne_compl {j : ℕ} (hj : j ≤ k + 2)
    (S : Set.powersetCard (Fin (k + 2)) j)
    (T : Set.powersetCard (Fin (k + 2)) (k + 2 - j))
    (hT : T ≠ Set.powersetCard.compl (by rw [Fintype.card_fin]; omega) S) :
    wedgePairing k hj (exteriorPower.ιMulti_family K j (Pi.basisFun K (Fin (k + 2))) S)
        (exteriorPower.ιMulti_family K (k + 2 - j) (Pi.basisFun K (Fin (k + 2))) T) = 0 := by
  apply wedgePairing_ιMulti_family_eq_zero_of_not_disjoint hj S T
  rw [Finset.disjoint_iff_eq_compl
    (by rw [Set.powersetCard.card_eq, Set.powersetCard.card_eq, Fintype.card_fin]; omega)]
  intro h
  exact hT (by rw [← Subtype.coe_inj, Set.powersetCard.coe_compl, h])

/-- **Diagonal non-vanishing of the wedge pairing** (ingredient (c), the diagonal half).
On the diagonal `T = Sᶜ` (mathlib's complement equivalence on the complementary-cardinality
subtypes), the wedge pairing of the two standard exterior-power basis vectors is nonzero —
in fact `±1`, the sign of the permutation interleaving `S` and `Sᶜ` into increasing order, but
only non-vanishing is needed downstream. The concatenated indexing family
`Fin.append (e ∘ φ_S) (e ∘ φ_{Sᶜ})` is `e` (the standard basis, hence injective) precomposed
with the bijection `Fin.append φ_S φ_{Sᶜ}` (injective: `φ_S`, `φ_{Sᶜ}` are order embeddings
with disjoint ranges `S`, `Sᶜ`), so it is a linearly independent family of standard basis
vectors and its extensor is nonzero (`extensor_ne_zero_iff_linearIndependent`); the volume
form `screwAlgebraTopEquiv`, being injective, keeps it nonzero. Together with the off-diagonal
`wedgePairing_ιMulti_family_eq_zero_of_ne_compl` this makes the pairing matrix on the standard
basis a signed-permutation matrix, hence nondegenerate — the input to `complementIso`. -/
theorem wedgePairing_ιMulti_family_compl_ne_zero {j : ℕ} (hj : j ≤ k + 2)
    (S : Set.powersetCard (Fin (k + 2)) j) :
    wedgePairing k hj (exteriorPower.ιMulti_family K j (Pi.basisFun K (Fin (k + 2))) S)
        (exteriorPower.ιMulti_family K (k + 2 - j) (Pi.basisFun K (Fin (k + 2)))
          (Set.powersetCard.compl (by rw [Fintype.card_fin]; omega) S)) ≠ 0 := by
  rw [wedgePairing_apply]
  have hne : wedgeProd hj
      (exteriorPower.ιMulti_family K j (Pi.basisFun K (Fin (k + 2))) S)
      (exteriorPower.ιMulti_family K (k + 2 - j) (Pi.basisFun K (Fin (k + 2)))
        (Set.powersetCard.compl (by rw [Fintype.card_fin]; omega) S)) ≠ 0 := by
    intro h
    have hcoe := congrArg (Subtype.val) h
    rw [coe_wedgeProd_ιMulti_family, ZeroMemClass.coe_zero] at hcoe
    refine (extensor_ne_zero_iff_linearIndependent _).mpr ?_ hcoe
    have hinj : Function.Injective (Fin.append
        (⇑(Set.powersetCard.ofFinEmbEquiv.symm S) : Fin j → Fin (k + 2))
        (⇑(Set.powersetCard.ofFinEmbEquiv.symm
          (Set.powersetCard.compl (by rw [Fintype.card_fin]; omega) S)) :
            Fin (k + 2 - j) → Fin (k + 2))) := by
      rw [Fin.append_injective_iff]
      refine ⟨(Set.powersetCard.ofFinEmbEquiv.symm S).injective,
        (Set.powersetCard.ofFinEmbEquiv.symm _).injective, ?_⟩
      intro p q hpq
      have hp := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem S _).mp ⟨p, rfl⟩
      have hq := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
        (Set.powersetCard.compl (by rw [Fintype.card_fin]; omega) S) _).mp ⟨q, rfl⟩
      rw [hpq] at hp
      rw [Set.powersetCard.mem_compl] at hq
      exact hq hp
    have hrw : ∀ (a : Fin j → Fin (k + 2)) (b : Fin (k + 2 - j) → Fin (k + 2)),
        Fin.append (⇑(Pi.basisFun K (Fin (k + 2))) ∘ a)
          (⇑(Pi.basisFun K (Fin (k + 2))) ∘ b) =
        ⇑(Pi.basisFun K (Fin (k + 2))) ∘ Fin.append a b := by
      intro a b
      funext x
      refine Fin.addCases ?_ ?_ x <;> intro i <;> simp [Fin.append_left, Fin.append_right]
    rw [hrw]
    exact (Pi.basisFun K (Fin (k + 2))).linearIndependent.comp _ hinj
  exact fun hz => hne ((map_eq_zero_iff _ (screwAlgebraTopEquiv k).injective).mp hz)

/-! ## The complement isomorphism `⋀ʲ V ≃ₗ ⋀^(N−j) V` (ingredient (d), `def:meet-complement-iso`)

The perfect wedge pairing `wedgePairing` is nondegenerate (ingredient (c): its matrix on
the standard exterior-power bases is a signed-permutation matrix — off-diagonal `0` by
`wedgePairing_ιMulti_family_eq_zero_of_ne_compl`, diagonal `≠ 0` by
`wedgePairing_ιMulti_family_compl_ne_zero`). Hence `wedgePairing k hj : ⋀ʲ V →ₗ
Module.Dual K (⋀^(N−j) V)` is **injective**: evaluating `wedgePairing k hj m` at the
complementary basis vector `e_{Sᶜ}` of `⋀^(N−j) V` reads off the `S`-coordinate of `m`
up to the nonzero diagonal scalar, so a zero pairing forces every coordinate of `m` to
vanish. Domain and codomain have equal finrank (`(k+2).choose j` on both sides, since
`Module.Dual` preserves finrank and `(k+2).choose j = (k+2).choose (k+2−j)`), so
injectivity upgrades to a `LinearEquiv` via `LinearMap.linearEquivOfInjective`; one more
post-composition with the dual-evaluation iso of `⋀^(N−j) V` lands `complementIso` in
`⋀^(N−j) V` itself. -/

/-- **Injectivity of the wedge pairing** (ingredient (c) → (d)). The perfect wedge pairing
`wedgePairing k hj : ⋀ʲ V →ₗ Module.Dual K (⋀^(N−j) V)` is injective: its matrix on the
standard exterior-power bases is a signed-permutation matrix (nonzero diagonal
`wedgePairing_ιMulti_family_compl_ne_zero`, vanishing off-diagonal
`wedgePairing_ιMulti_family_eq_zero_of_ne_compl`), so evaluating a zero pairing at each
complementary basis vector forces all standard-basis coordinates of the argument to
vanish. The nondegeneracy input to `complementIso` (`def:meet-complement-iso`). -/
theorem wedgePairing_injective {j : ℕ} (hj : j ≤ k + 2) :
    Function.Injective (wedgePairing (K := K) k hj) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro m hm
  set bj := (Pi.basisFun K (Fin (k + 2))).exteriorPower j with hbj
  apply bj.ext_elem_iff.mpr
  intro S
  -- read off the `S`-coordinate by evaluating the zero functional at `e_{Sᶜ}`
  set T : Set.powersetCard (Fin (k + 2)) (k + 2 - j) :=
    Set.powersetCard.compl (by rw [Fintype.card_fin]; omega) S with hT
  have hval : wedgePairing k hj m
      (exteriorPower.ιMulti_family K (k + 2 - j) (Pi.basisFun K (Fin (k + 2))) T) = 0 := by
    rw [hm]; rfl
  rw [← bj.sum_repr m, map_sum] at hval
  simp only [LinearMap.coe_sum, Finset.sum_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul, hbj, exteriorPower.basis_apply] at hval
  rw [Finset.sum_eq_single S] at hval
  · rw [map_zero, Finsupp.coe_zero, Pi.zero_apply]
    by_contra hne
    exact (wedgePairing_ιMulti_family_compl_ne_zero (K := K) hj S)
      (by simpa [hT] using (mul_eq_zero.mp hval).resolve_left hne)
  · intro S' _ hS'
    have : T ≠ Set.powersetCard.compl (by rw [Fintype.card_fin]; omega) S' := by
      rw [hT]
      intro h
      exact hS' ((Set.powersetCard.compl _).injective h).symm
    rw [wedgePairing_ιMulti_family_eq_zero_of_ne_compl (K := K) hj S' T this, mul_zero]
  · intro h; exact absurd (Finset.mem_univ S) h

/-- The finrank of `⋀ʲ (Fin (k+2) → K)` equals the finrank of `Module.Dual K (⋀^(k+2−j)
(Fin (k+2) → K))`: both are `(k+2).choose j`. The dual preserves finrank, and the binomial
symmetry `(k+2).choose j = (k+2).choose (k+2−j)` (`Nat.choose_symm_diff`, valid for
`j ≤ k+2`) matches the two exterior powers. The dimension match feeding
`LinearMap.linearEquivOfInjective` in `complementIso`. -/
theorem finrank_exteriorPower_eq_finrank_dual {j : ℕ} (hj : j ≤ k + 2) :
    Module.finrank K (⋀[K]^j (Fin (k + 2) → K)) =
      Module.finrank K (Module.Dual K (⋀[K]^(k + 2 - j) (Fin (k + 2) → K))) := by
  rw [Subspace.dual_finrank_eq, exteriorPower.finrank_eq, exteriorPower.finrank_eq,
    Module.finrank_fin_fun]
  exact (Nat.choose_symm hj).symm

/-- **The complement isomorphism** `⋀ʲ V ≃ₗ ⋀^(N−j) V` (`N = k+2`, `def:meet-complement-iso`):
the genuinely new core of the Grassmann–Cayley meet. Built from the nondegenerate perfect
wedge pairing `wedgePairing` (ingredient (c)): injectivity (`wedgePairing_injective`) plus
the equal finrank (`finrank_exteriorPower_eq_finrank_dual`) make `wedgePairing` a
`LinearEquiv` onto `Module.Dual K (⋀^(N−j) V)` via `LinearMap.linearEquivOfInjective`, and
post-composing with the dual-evaluation iso `(b.exteriorPower (k+2−j)).toDualEquiv.symm`
lands the result in `⋀^(N−j) V`. The regressive product `meet` is the next deliverable
above this. -/
noncomputable def complementIso {j : ℕ} (hj : j ≤ k + 2) :
    ⋀[K]^j (Fin (k + 2) → K) ≃ₗ[K] ⋀[K]^(k + 2 - j) (Fin (k + 2) → K) :=
  (LinearMap.linearEquivOfInjective (wedgePairing k hj) (wedgePairing_injective hj)
      (finrank_exteriorPower_eq_finrank_dual hj)) ≪≫ₗ
    ((Pi.basisFun K (Fin (k + 2))).exteriorPower (k + 2 - j)).toDualEquiv.symm

/-- **The defining wedge-pairing property of `complementIso`** (`def:meet-complement-iso`, the
staging lemma for the point-join ↔ panel-meet duality `lem:case-III-claim612-line-in-panel-union`).
Pairing `complementIso hj X` against any `B : ⋀^(N−j) V` through the standard exterior-power basis's
`toDual` reproduces the wedge pairing of `X` with `B`:
`(b.exteriorPower (N−j)).toDual (complementIso hj X) B = screwAlgebraTopEquiv (X ∨ₑ B)`, i.e. the
volume of the join `X ∧ B`. This is the characterizing identity of the complement iso — by
construction `complementIso = (wedgePairing as an equiv) ≪≫ toDualEquiv.symm`, so applying
`toDualEquiv` undoes the second factor and leaves `wedgePairing X` (`LinearEquiv.apply_symm_apply` +
`linearEquivOfInjective_apply`). It is the metric-free Grassmann–Cayley duality dictionary entry the
duality bridge consumes: it turns membership/annihilation statements about the panel-meet
`complementIso (n_u ∧ n')` into the volume form `vol((n_u ∧ n') ∧ B)`, the bilinear pairing on
which the point-join ↔ panel-meet proportionality rests. -/
theorem complementIso_toDual {j : ℕ} (hj : j ≤ k + 2)
    (X : ⋀[K]^j (Fin (k + 2) → K)) (B : ⋀[K]^(k + 2 - j) (Fin (k + 2) → K)) :
    ((Pi.basisFun K (Fin (k + 2))).exteriorPower (k + 2 - j)).toDual (complementIso hj X) B
      = wedgePairing k hj X B := by
  rw [complementIso, LinearEquiv.trans_apply, ← Module.Basis.toDualEquiv_apply,
    LinearEquiv.apply_symm_apply, LinearMap.linearEquivOfInjective_apply]

/-! ## The regressive product (meet) `⋀^(N−a) V × ⋀^(N−b) V → ⋀^(N−(a+b)) V` (`def:meet`)

The Grassmann–Cayley **meet** (regressive product), the dual of the Phase-17 join.
Where the join `A ∨ₑ B` spans the two subspaces (and lands in grade `p + q`), the meet
`A ∧ₑ B` *intersects* them: it is the join conjugated by the complement iso
`complementIso` (`def:meet-complement-iso`), which plays the role of the projective dual
(a `*`-operator `⋀^j V → ⋀^(N−j) V`).

Concretely, for `A : ⋀^(N−a) V` and `B : ⋀^(N−b) V` (`N = k+2`, with `a + b ≤ N` the
transversality grade budget), the meet is

  `meet A B := complementIso (gradedMul (complementIso A) (complementIso B))`,

i.e. `*(*A ∨ₑ *B)`: `complementIso A : ⋀^a V`, `complementIso B : ⋀^b V`, their graded
product `gradedMul` lands in `⋀^(a+b) V`, and a third `complementIso` brings it to
`⋀^(N−(a+b)) V`. Geometrically, when `A`, `B` are the supporting `(N−a)`- and
`(N−b)`-extensors of two subspaces of `V`, the meet is the supporting extensor of their
codimension-`(a+b)` intersection; in the screw-space arithmetic of
`sec:molecular-rigidity-matrix` the meet of two hyperplane normals (`a = b = 1`) is the
supporting `(N−2) = k`-extensor of their codimension-2 intersection, landing in
`ScrewSpace k`. -/

/-- The general graded wedge product `⋀^p V × ⋀^q V → ⋀^(p+q) V` (`N = k+2`): the join /
exterior product `↑A * ↑B` landed in the `(p+q)`-graded piece via the graded monoid
structure on `fun i ↦ ⋀^i V`. The grade-general form of `wedgeProd` (which is the
`q = N−p` top-piece specialization); the join transport on which the regressive product
`meet` (`def:meet`) is built. -/
noncomputable def gradedMul {p q : ℕ}
    (A : ⋀[K]^p (Fin (k + 2) → K)) (B : ⋀[K]^q (Fin (k + 2) → K)) :
    ⋀[K]^(p + q) (Fin (k + 2) → K) :=
  ⟨(A : ExteriorAlgebra K (Fin (k + 2) → K)) * (B : ExteriorAlgebra K (Fin (k + 2) → K)),
    SetLike.mul_mem_graded A.2 B.2⟩

/-- The underlying exterior-algebra element of `gradedMul` is the Phase-17 join `∨ₑ`
of the two factors. The bridge from the meet's graded product to the join API. -/
@[simp]
theorem coe_gradedMul {p q : ℕ}
    (A : ⋀[K]^p (Fin (k + 2) → K)) (B : ⋀[K]^q (Fin (k + 2) → K)) :
    (gradedMul A B : ExteriorAlgebra K (Fin (k + 2) → K)) =
      (A : ExteriorAlgebra K (Fin (k + 2) → K)) ∨ₑ
        (B : ExteriorAlgebra K (Fin (k + 2) → K)) :=
  rfl

/-- **The regressive product (meet)** `⋀^(N−a) V × ⋀^(N−b) V → ⋀^(N−(a+b)) V`
(`N = k+2`, `def:meet`): the Grassmann–Cayley meet, the projective dual of the
Phase-17 join. It is the graded product `gradedMul` of the two complements (via
`complementIso` as the `*`-operator), conjugated by a third `complementIso` —
`*(*A ∨ₑ *B)`: `complementIso A : ⋀^a V`, `complementIso B : ⋀^b V`, their product lands
in `⋀^(a+b) V`, and `complementIso` returns it to `⋀^(N−(a+b)) V`. Geometrically the supporting
extensor of the codimension-`(a+b)` intersection of the two factors' subspaces; for
`a = b = 1` the meet of two hyperplane normals is the supporting `k`-extensor of their
codimension-2 intersection, landing in `ScrewSpace k`. -/
noncomputable def meet {a b : ℕ} (ha : a ≤ k + 2) (hb : b ≤ k + 2) (hab : a + b ≤ k + 2)
    (A : ⋀[K]^(k + 2 - a) (Fin (k + 2) → K)) (B : ⋀[K]^(k + 2 - b) (Fin (k + 2) → K)) :
    ⋀[K]^(k + 2 - (a + b)) (Fin (k + 2) → K) := by
  -- `complementIso A : ⋀^a`, `complementIso B : ⋀^b`, product in `⋀^(a+b)`.
  have hA : k + 2 - (k + 2 - a) = a := by omega
  have hB : k + 2 - (k + 2 - b) = b := by omega
  refine complementIso (j := a + b) hab
    (gradedMul (hA ▸ complementIso (k := k) (j := k + 2 - a) (by omega) A)
      (hB ▸ complementIso (k := k) (j := k + 2 - b) (by omega) B))

@[inherit_doc] scoped infixl:70 " ∧ₑ " => meet

/-! ## Step (i) of the point-join ↔ panel-meet duality: the complement of a decomposable lies in
the wedge-orthogonal complement (`lem:case-III-claim612-line-in-panel-union`)

The first remaining leaf of the duality bridge beyond the green dictionary entry
`complementIso_toDual`. Geometrically: the complement `complementIso (n_u ∧ n')` of the grade-2
decomposable `n_u ∧ n'` lands in `⋀²W` for `W = {n_u, n'}^⊥` — i.e. it is annihilated by every
`2`-extensor that shares a factor with `n_u ∧ n'`. The metric-free reading, through the dictionary
entry, is that pairing `complementIso (n_u ∧ n')` against any `B` whose wedge with `n_u ∧ n'`
vanishes gives `0`; the concrete vanishing is the alternating law (`extensor_eq_zero_of_eq`) on the
concatenated family of two `2`-extensors sharing a vector. -/

/-- **Step (i), the dictionary half: `complementIso` of a wedge-orthogonal element vanishes**
(`lem:case-III-claim612-line-in-panel-union`). If the graded wedge `X ∨ₑ B` of `X : ⋀ʲ V` with
`B : ⋀^(N−j) V` vanishes (`wedgeProd hj X B = 0`), then `complementIso hj X` is annihilated by `B`
through the standard exterior-power basis's `toDual`. Immediate from the defining wedge-pairing
property `complementIso_toDual` (`b.toDual (complementIso X) B = vol(X ∨ₑ B)`) and the volume form's
linearity: a vanishing wedge has volume `0`. This is the metric-free criterion turning
"`X ∨ₑ B = 0`" (a shared factor) into "`complementIso X ⊥ B`", i.e. `complementIso X` lies in the
wedge-orthogonal complement of every such `B`. -/
theorem complementIso_toDual_eq_zero_of_wedgeProd_eq_zero {j : ℕ} (hj : j ≤ k + 2)
    (X : ⋀[K]^j (Fin (k + 2) → K)) (B : ⋀[K]^(k + 2 - j) (Fin (k + 2) → K))
    (hwedge : wedgeProd hj X B = 0) :
    ((Pi.basisFun K (Fin (k + 2))).exteriorPower (k + 2 - j)).toDual
        (complementIso hj X) B = 0 := by
  simp only [complementIso_toDual, wedgePairing_apply, hwedge, map_zero]

/-- **Step (i), the concrete half: the wedge of two `2`-extensors sharing a vector vanishes**
(`lem:case-III-claim612-line-in-panel-union`, the `d = 3` / `ScrewSpace 2 = ⋀²K⁴` case). If the
families `n, c : Fin 2 → K⁴` share a vector (here `n 0 = c 0`, the shared panel normal `n_u`), the
graded wedge `wedgeProd (extensor n) (extensor c)` vanishes: its underlying element is the join
`extensor n ∨ₑ extensor c = extensor (Fin.append n c)` (`join_extensor`), whose concatenated family
repeats the shared vector, so the extensor is `0` by the alternating law `extensor_eq_zero_of_eq`.
This supplies the hypothesis of `complementIso_toDual_eq_zero_of_wedgeProd_eq_zero` for the
decomposable `n_u ∧ n' = extensor n`, putting `complementIso (n_u ∧ n')` in `⋀²W`. -/
theorem wedgeProd_extensor_eq_zero_of_shared_vector (n c : Fin 2 → Fin 4 → K) (hshare : n 0 = c 0) :
    wedgeProd (k := 2) (j := 2) (by omega)
      ⟨extensor n, extensor_mem_exteriorPower n⟩
      ⟨extensor c, extensor_mem_exteriorPower c⟩ = 0 := by
  apply Subtype.ext
  rw [coe_wedgeProd, ZeroMemClass.coe_zero]
  change extensor n ∨ₑ extensor c = 0
  rw [join_extensor]
  apply extensor_eq_zero_of_eq _ (a := Fin.castAdd 2 0) (b := Fin.natAdd 2 0)
  · rw [Fin.append_left, Fin.append_right, hshare]
  · decide

/-- **Step (i) of the point-join ↔ panel-meet duality**
(`lem:case-III-claim612-line-in-panel-union`): `complementIso (n_u ∧ n')` lands in `⋀²W` for
`W = {n_u, n'}^⊥`, in operational dual form. At `d = 3` (`k = 2`, `ScrewSpace 2 = ⋀²K⁴`), for the
grade-2 decomposable `n_u ∧ n' = extensor n` (family `n : Fin 2 → K⁴` of two panel normals), its
complement `complementIso (n_u ∧ n')` is annihilated — through the standard exterior-power basis's
`toDual` — by every `2`-extensor `extensor c` sharing a vector with `n` (`n 0 = c 0`). This is the
decomposable-of-orthogonal-complement step: composing the dictionary half
`complementIso_toDual_eq_zero_of_wedgeProd_eq_zero` with the concrete wedge vanishing
`wedgeProd_extensor_eq_zero_of_shared_vector`. With step (ii) (`dim ⋀²W = 1`) it forces the
point-join `p_i ∨ p_j` and the panel-meet `C(L) = complementIso (n_u ∧ n')` to be scalar multiples,
so an `r` annihilating every `C(L)` annihilates each spanning join — the contrapositive glue of the
Claim 6.12 capstone. -/
theorem complementIso_toDual_extensor_eq_zero_of_shared_vector
    (n c : Fin 2 → Fin 4 → K) (hshare : n 0 = c 0) :
    ((Pi.basisFun K (Fin (2 + 2))).exteriorPower (2 + 2 - 2)).toDual
        (complementIso (k := 2) (j := 2) (by omega) ⟨extensor n, extensor_mem_exteriorPower n⟩)
        ⟨extensor c, extensor_mem_exteriorPower c⟩ = 0 :=
  complementIso_toDual_eq_zero_of_wedgeProd_eq_zero (by omega) _ _
    (wedgeProd_extensor_eq_zero_of_shared_vector n c hshare)

/-! ## Step (ii) of the point-join ↔ panel-meet duality: `⋀²W` is `1`-dimensional for a `2`-dim `W`
(`lem:case-III-claim612-line-in-panel-union`)

The second remaining leaf of the duality bridge. Step (i) put both the point-join `p̄ᵢ ∨ p̄ⱼ` and
the panel-meet `C(L) = complementIso (n_u ∧ n')` in `⋀²W` for the `2`-dimensional
`W = {n_u, n'}^⊥ = span{p̄ᵢ, p̄ⱼ}`. Step (ii) is the dimension count: `dim ⋀²W = (dim W).choose 2 =
2.choose 2 = 1`, so the exterior square of a `2`-dimensional space is a *line*, and two nonzero
members of a line are scalar multiples. This forces `p̄ᵢ ∨ p̄ⱼ = λ · C(L)` (the projective scale of
the line), the proportionality on which the annihilation transfer `r(C(L)) = 0 ⟹ r(p̄ᵢ ∨ p̄ⱼ) = 0`
rests. The proportionality itself is the general `finrank_eq_one_iff_of_nonzero'`; the
exterior-square dimension count is the genuinely new content here. -/

/-- **Step (ii) at general grade, the top-grade dimension count: `⋀^n W` is `1`-dimensional for an
`n`-dimensional `W`** (`lem:case-III-claim612-line-in-panel-union`, CHAIN-3 — the general-`d`
restatement of `finrank_exteriorPower_two_eq_one`, replacing the `⋀²`-pinned `d=3` route). For a
finite free `K`-module `W` of dimension `n`, its top exterior power `⋀^n W` has dimension
`(dim W).choose n = n.choose n = 1` by `exteriorPower.finrank_eq` + `Nat.choose_self` — the grade is
free here, the count is the genuinely-general content. At the CHAIN proportionality site
`W = {n_u}^⊥ ∩ ⋯` is the `(d−1)`-dimensional span of the chain points and the grade is `d−1`, so
`⋀^{d−1}W` is the line carrying both the point-join and the panel-meet; the `d=3` instance recovers
`finrank_exteriorPower_two_eq_one` (`n = 2`). -/
theorem finrank_exteriorPower_self_eq_one {W : Type*} [AddCommGroup W] [Module K W]
    [Module.Free K W] [Module.Finite K W] {n : ℕ} (hW : Module.finrank K W = n) :
    Module.finrank K (⋀[K]^n W) = 1 := by
  rw [exteriorPower.finrank_eq, hW, Nat.choose_self]

/-- **Step (ii), the dimension count: `⋀²W` is `1`-dimensional for a `2`-dimensional `W`**
(`lem:case-III-claim612-line-in-panel-union`). The `d=3` instance (grade `2`) of the grade-generic
`finrank_exteriorPower_self_eq_one`. For a finite free `K`-module `W` of dimension `2`, its exterior
square `⋀²W` has dimension `(dim W).choose 2 = 2.choose 2 = 1`. Geometrically, the supporting
extensors of a projective line — written either as the join of two points on it or as the meet of
two hyperplanes through it — live in this `1`-dimensional exterior square, so any two nonzero ones
are proportional (`exteriorPower_finrank_eq_one_proportional`). -/
theorem finrank_exteriorPower_two_eq_one {W : Type*} [AddCommGroup W] [Module K W]
    [Module.Free K W] [Module.Finite K W] (hW : Module.finrank K W = 2) :
    Module.finrank K (⋀[K]^2 W) = 1 :=
  finrank_exteriorPower_self_eq_one hW

/-- **Step (ii), the proportionality: two nonzero members of `⋀²W` are scalar multiples**
(`lem:case-III-claim612-line-in-panel-union`). For a `2`-dimensional `W`, `⋀²W` is a line
(`finrank_exteriorPower_two_eq_one`), so any element `y` of it is a scalar multiple of a fixed
nonzero `x` (`finrank_eq_one_iff_of_nonzero'`). This is the duality bridge's payoff: with both the
point-join `p̄ᵢ ∨ p̄ⱼ` and the panel-meet `C(L)` placed in `⋀²W` by step (i), one is `λ` times the
other, so a functional annihilating `C(L)` annihilates the join. -/
theorem exteriorPower_finrank_eq_one_proportional {W : Type*} [AddCommGroup W] [Module K W]
    [Module.Free K W] [Module.Finite K W] (hW : Module.finrank K W = 2)
    {x : ⋀[K]^2 W} (hx : x ≠ 0) (y : ⋀[K]^2 W) : ∃ c : K, c • x = y :=
  (finrank_eq_one_iff_of_nonzero' x hx).mp (finrank_exteriorPower_two_eq_one hW) y

/-! ## The point-join ↔ panel-meet duality assembly, N3b-1: the inclusion `⋀²W ↪ ⋀²K⁴`
(`lem:case-III-claim612-line-in-panel-union`)

The first sub-leaf of the duality *assembly* (Phase 22f) on top of the green operational steps (i)
(`complementIso_toDual_extensor_eq_zero_of_shared_vector`, placing the panel-meet in `⋀²W`) and (ii)
(`exteriorPower_finrank_eq_one_proportional`, `⋀²W` is a line). The assembly places both the
point-join `p̄ᵢ ∨ p̄ⱼ` and the panel-meet `C(L)` in a common `⋀²W` — for `W = {n_u, n'}^⊥` the
2-dim space spanned by the two points — and extracts the proportionality scalar there. To pull the
two members of `⋀²K⁴` back into `⋀²W` (where step (ii) bites) one needs the inclusion
`exteriorPower.map 2 W.subtype : ⋀²W →ₗ ⋀²K⁴` to be injective. Over the field `K`, injectivity of
the inclusion `⋀²W ↪ ⋀²K⁴` follows from injectivity of `W.subtype` by the general
`exteriorPower.map_injective_field` (no retraction needed — the `CommRing`-level
`exteriorPower.map_injective` requiring an explicit retraction is the fallback, unused over a
field). -/

/-- **N3b-1 at general grade: the inclusion `⋀^g W ↪ ⋀^g (K^{d+1})` is injective**
(`lem:case-III-claim612-line-in-panel-union`, CHAIN-3 — the grade-generic restatement of the
`⋀²`-pinned `d=3` `exteriorPower_map_subtype_injective`). For a submodule `W` of `K^{d+1}` and any
grade `g`, the exterior-power map `exteriorPower.map g W.subtype : ⋀^g W →ₗ ⋀^g (K^{d+1})` induced
by the (injective) inclusion `W.subtype` is injective. Over the field `K` this is immediate from
injectivity of `W.subtype` (`Submodule.injective_subtype`) via `exteriorPower.map_injective_field`
— the grade enters nothing. This is the pull-back map of the CHAIN proportionality: it transports
the two `⋀^{d−1}(K^{d+1})` members (the point-join and the panel-meet, both lying in the image
`⋀^{d−1}W` by `extensor_mem_range_map_subtype_of_mem_grade`) into the line `⋀^{d−1}W`, where the
top-grade count (`finrank_exteriorPower_self_eq_one`) makes them proportional. -/
theorem exteriorPower_map_subtype_injective_grade {d : ℕ} (g : ℕ)
    (W : Submodule K (Fin (d + 1) → K)) :
    Function.Injective (exteriorPower.map g W.subtype) :=
  exteriorPower.map_injective_field W.injective_subtype

/-- **N3b-1 of the point-join ↔ panel-meet duality assembly: the inclusion `⋀²W ↪ ⋀²K⁴` is
injective** (`lem:case-III-claim612-line-in-panel-union`). The `d=3` instance (grade `2`,
ambient `Fin 4`) of the grade-generic `exteriorPower_map_subtype_injective_grade`. For a submodule
`W` of `K⁴`, the exterior-power map `exteriorPower.map 2 W.subtype : ⋀²W →ₗ ⋀²K⁴` is injective. This
is the pull-back map of the assembly: it transports the two `⋀²K⁴` members (the point-join
`p̄ᵢ ∨ p̄ⱼ` and the panel-meet `C(L)`, both lying in the image `⋀²W` by N3b-2) back into the line
`⋀²W`, where step (ii) (`exteriorPower_finrank_eq_one_proportional`) makes them proportional. -/
theorem exteriorPower_map_subtype_injective (W : Submodule K (Fin 4 → K)) :
    Function.Injective (exteriorPower.map 2 W.subtype) :=
  exteriorPower_map_subtype_injective_grade (d := 3) 2 W

/-- **Range push-forward of `⋀^g` along an endomorphism carrying one submodule into another**
(`def:meet-complement-iso`, the transport step of the OD-8 panel-meet range-membership). For an
endomorphism `O` of `K^{k+2}` and submodules `W'`, `W` with `O(W') ⊆ W`, the induced map
`exteriorPower.map g O` carries the range of the inclusion `⋀^g W' ↪ ⋀^g (K^{k+2})` into the range
of the inclusion `⋀^g W ↪ ⋀^g (K^{k+2})`: if `X` is the image of some `Y : ⋀^g W'`, then
`map g O X` is the image of `map g f Y` where `f : W' →ₗ W` corestricts `O ∘ W'.subtype`.
The metric-free transport lemma the panel-meet range-membership composes with the
GL-contragredient equivariance `complementIso_map_contragredient_eq`: a coordinate-complement
membership pushes forward along the contragredient frame map `h` (with `h` sending the coordinate
complement into `W = {n}^⊥`) to the target-`W` membership. -/
theorem exteriorPower_map_mem_range_map_subtype_of_mapsTo {g : ℕ}
    (O : (Fin (k + 2) → K) →ₗ[K] (Fin (k + 2) → K))
    (W' W : Submodule K (Fin (k + 2) → K)) (hO : ∀ w ∈ W', O w ∈ W)
    {X : ⋀[K]^g (Fin (k + 2) → K)} (hX : X ∈ LinearMap.range (exteriorPower.map g W'.subtype)) :
    exteriorPower.map g O X ∈ LinearMap.range (exteriorPower.map g W.subtype) := by
  obtain ⟨Y, rfl⟩ := hX
  -- `f : W' →ₗ W`, the corestriction of `O ∘ₗ W'.subtype`; `W.subtype ∘ₗ f = O ∘ₗ W'.subtype`.
  refine ⟨exteriorPower.map g
      ((O ∘ₗ W'.subtype).codRestrict W fun x => hO _ x.2) Y, ?_⟩
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, ← LinearMap.comp_apply,
    ← exteriorPower.map_comp, LinearMap.subtype_comp_codRestrict]

/-- **N3b-2 with the grade decoupled from the ambient dimension: a `j`-extensor of vectors in `W`
lies in `⋀^j W ↪ ⋀^j (K^{d+1})`** (`lem:case-III-claim612-line-in-panel-union`, CHAIN-3, OD-8 — the
first general-`d` duality brick, replacing the `Fin 4`-pinned `d=3` route). If every vector of a
family `v : Fin j → K^{d+1}` lies in a subspace `W ⊆ K^{d+1}`, the `j`-extensor `extensor v` (as an
element of `⋀^j (K^{d+1})`) lies in the range of the inclusion
`exteriorPower.map j W.subtype : ⋀^j W →ₗ ⋀^j (K^{d+1})` — it is the image of the abstract wedge
`exteriorPower.ιMulti K j` of the family lifted into `W` (`fun i ↦ ⟨v i, hv i⟩`). The grade `j` is
**decoupled** from the ambient `d` (the `_grade` form below ties it to `d − 1`): the OD-8 panel-meet
membership needs the *grade-2* extensor `extensor ![n₀, n₁]` of the two line-normals in the ambient
`Fin (k + 2) = Fin ((k+1)+1)`, grade `2 ≠ (k+1) − 1 = k`, so the grade must be a free parameter. The
proof is *grade-generic verbatim* (the same `exteriorPower.map_apply_ιMulti` +
`exteriorPower.ιMulti_apply_coe` + `Subtype.ext` chain — no `finrank` count, no `fin_cases`):
nothing in it depends on the grade. -/
theorem extensor_mem_range_map_subtype_of_mem_jgrade {d j : ℕ}
    (W : Submodule K (Fin (d + 1) → K)) (v : Fin j → Fin (d + 1) → K)
    (hv : ∀ i, v i ∈ W) :
    (⟨extensor v, extensor_mem_exteriorPower v⟩ : ⋀[K]^j (Fin (d + 1) → K))
      ∈ LinearMap.range (exteriorPower.map j W.subtype) := by
  refine ⟨exteriorPower.ιMulti K j (fun i => ⟨v i, hv i⟩), ?_⟩
  rw [exteriorPower.map_apply_ιMulti]
  apply Subtype.ext
  rw [exteriorPower.ιMulti_apply_coe]
  rfl

/-- **N3b-2 at the grade `d − 1`: a `(d−1)`-extensor of vectors in `W` lies in
`⋀^{d−1}W ↪ ⋀^{d−1}(K^{d+1})`** (`lem:case-III-claim612-line-in-panel-union`, CHAIN-3). The
grade-and-ambient-coupled (`grade = d − 1`) instance of the decoupled
`extensor_mem_range_map_subtype_of_mem_jgrade`, the form the point-join half of the duality
consumes (`W` = the `(d−1)`-dim span of the chain points, grade `d − 1`). The `d=3` instance
recovers `extensor_mem_range_map_subtype_of_mem` (`d−1 = 2`, `d+1 = 4`). -/
theorem extensor_mem_range_map_subtype_of_mem_grade {d : ℕ}
    (W : Submodule K (Fin (d + 1) → K)) (v : Fin (d - 1) → Fin (d + 1) → K)
    (hv : ∀ i, v i ∈ W) :
    (⟨extensor v, extensor_mem_exteriorPower v⟩ : ⋀[K]^(d - 1) (Fin (d + 1) → K))
      ∈ LinearMap.range (exteriorPower.map (d - 1) W.subtype) :=
  extensor_mem_range_map_subtype_of_mem_jgrade W v hv

/-- **N3b-2, the point-join half (`d=3` instance): a `2`-extensor of vectors in `W` lies in
`⋀²W ↪ ⋀²K⁴`** (`lem:case-III-claim612-line-in-panel-union`). Second sub-leaf of the point-join ↔
panel-meet duality assembly (Phase 22f); the `d=3` specialization of
`extensor_mem_range_map_subtype_of_mem_grade` (`d−1 = 2`, `d+1 = 4`). Applied to the point-join
`p̄ᵢ ∨ p̄ⱼ = extensor ![p̄ᵢ, p̄ⱼ]` at `W = span{p̄ᵢ, p̄ⱼ} = {n_u, n'}^⊥` (each `p̄ᵢ ∈ W` by the
incidence `⟨p̄ᵢ, n_u⟩ = ⟨p̄ᵢ, n'⟩ = 0`), this places the join in the line `⋀²W`, the first of the
two members N3b-3 pulls back to apply step (ii). The companion panel-meet membership
(`C(L) = complementIso (n_u ∧ n') ∈ ⋀²W`, the range-membership upgrade of step (i)) lands next. -/
theorem extensor_mem_range_map_subtype_of_mem
    (W : Submodule K (Fin 4 → K)) (v : Fin 2 → Fin 4 → K) (hv : ∀ i, v i ∈ W) :
    (⟨extensor v, extensor_mem_exteriorPower v⟩ : ⋀[K]^2 (Fin 4 → K))
      ∈ LinearMap.range (exteriorPower.map 2 W.subtype) :=
  extensor_mem_range_map_subtype_of_mem_grade (d := 3) W v hv

/-- **N3b-2b-line at general grade, the proportionality engine: `range (⋀^{d−1}W ↪ ⋀^{d−1}K^{d+1})`
is the line `span{x}` of any nonzero member, so two of its members are proportional**
(`lem:case-III-claim612-line-in-panel-union`, CHAIN-3 — the grade-generic restatement of the
`⋀²`-pinned `d=3` `exists_smul_eq_of_mem_range_map_subtype`; the leaf's genuine new count).
For a `(d−1)`-dimensional `W ⊆ K^{d+1}`, the range of the injective inclusion
`exteriorPower.map (d−1) W.subtype : ⋀^{d−1}W →ₗ ⋀^{d−1}(K^{d+1})`
(`exteriorPower_map_subtype_injective_grade`, N3b-1) is `1`-dimensional: `finrank (range) =
finrank ⋀^{d−1}W = (d−1).choose (d−1) = 1` (`LinearMap.finrank_range_of_inj` +
`finrank_exteriorPower_self_eq_one` at the *top* grade `d−1` of `W` — the general count for
the `d=3` `finrank_exteriorPower_two_eq_one`). Hence for any nonzero member `x` of the range,
`span{x}` already exhausts it (`Submodule.eq_of_le_of_finrank_eq`, two `1`-dim subspaces with
`span{x} ≤ range`), so every other member `y` is a scalar multiple `c • x = y`
(`Submodule.mem_span_singleton`).

This is the proportionality engine of the CHAIN duality *in `⋀^{d−1}(K^{d+1})`*: with the point-join
of the chain points placed in the range as the nonzero `x` (`W` = their `(d−1)`-dim span), once the
panel-meet `C(L)` is also shown to be in the range (CHAIN-4's spanning leaf), this yields
`C(L) = λ · (join)` directly — the proportionality lives in `⋀^{d−1}(K^{d+1})` itself, so no
pull-back into the pulled-back `⋀^{d−1}W` is needed. -/
theorem exists_smul_eq_of_mem_range_map_subtype_grade {d : ℕ}
    (W : Submodule K (Fin (d + 1) → K)) (hW : Module.finrank K W = d - 1)
    {x y : ⋀[K]^(d - 1) (Fin (d + 1) → K)}
    (hx : x ∈ LinearMap.range (exteriorPower.map (d - 1) W.subtype)) (hxne : x ≠ 0)
    (hy : y ∈ LinearMap.range (exteriorPower.map (d - 1) W.subtype)) :
    ∃ c : K, c • x = y := by
  have hR : Module.finrank K (LinearMap.range (exteriorPower.map (d - 1) W.subtype)) = 1 := by
    rw [LinearMap.finrank_range_of_inj (exteriorPower_map_subtype_injective_grade (d - 1) W),
      finrank_exteriorPower_self_eq_one hW]
  have hspan : (K ∙ x) = LinearMap.range (exteriorPower.map (d - 1) W.subtype) :=
    Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).2 hx)
      (by rw [finrank_span_singleton hxne, hR])
  rw [← Submodule.mem_span_singleton, hspan]
  exact hy

/-- **N3b-2b-line, the line identity: `range (⋀²W ↪ ⋀²K⁴)` is the line `span{x}` of any nonzero
member, so two of its members are proportional** (`lem:case-III-claim612-line-in-panel-union`).
The `d=3` instance (grade `2`, ambient `Fin 4`, `finrank W = 2`) of the grade-generic
`exists_smul_eq_of_mem_range_map_subtype_grade`. For a `2`-dimensional `W ⊆ K⁴`, the range of the
injective inclusion `exteriorPower.map 2 W.subtype : ⋀²W →ₗ ⋀²K⁴` is `1`-dimensional, so every two
of its members are proportional.

This is the proportionality engine of the assembly *in `⋀²K⁴`*: with the point-join
`p̄ᵢ ∨ p̄ⱼ = extensor ![p̄ᵢ, p̄ⱼ]` placed in the range as the nonzero `x` (N3b-2a,
`W = span{p̄ᵢ, p̄ⱼ}`), once the
panel-meet `C(L) = complementIso (n_u ∧ n')` is also shown to be in the range (N3b-2b-α, the
spanning leaf), this leaf yields the proportionality `complementIso (n_u ∧ n') = λ · (p̄ᵢ ∨ p̄ⱼ)`
directly — subsuming the phase-open N3b-3 pull-back/push-forward wiring, since the proportionality
lives in `⋀²K⁴` itself rather than in the pulled-back `⋀²W`. -/
theorem exists_smul_eq_of_mem_range_map_subtype
    (W : Submodule K (Fin 4 → K)) (hW : Module.finrank K W = 2)
    {x y : ⋀[K]^2 (Fin 4 → K)}
    (hx : x ∈ LinearMap.range (exteriorPower.map 2 W.subtype)) (hxne : x ≠ 0)
    (hy : y ∈ LinearMap.range (exteriorPower.map 2 W.subtype)) :
    ∃ c : K, c • x = y :=
  exists_smul_eq_of_mem_range_map_subtype_grade (d := 3) W hW hx hxne hy

/-- **Two `2`-extensors of pairs spanning the same plane are proportional**
(`lem:case-III-claim612-line-in-panel-union`, CHAIN-3, OD-8 — the input-side proportionality of the
panel-meet range-membership). For a linearly independent pair `v : Fin 2 → K^{d+1}` and any pair
`u : Fin 2 → K^{d+1}` whose two vectors lie in the plane `P = span(range v)`, the `2`-extensor
`extensor u` is a scalar multiple of `extensor v`. Both lie in the line
`range (exteriorPower.map 2 P.subtype)` (`⋀²P` is `1`-dimensional, `P` being `2`-dimensional —
`finrank_exteriorPower_self_eq_one`), and `extensor v ≠ 0` (`v` independent,
`extensor_ne_zero_iff_linearIndependent`), so the line-proportionality engine yields the scalar.
This is the input half of the OD-8 panel-meet range-membership: it lets the panel-meet `extensor n`
(`n` the two line-normals) be replaced — up to a nonzero scalar, which `complementIso` linearity and
the submodule-closed-under-`•` membership target both absorb — by the `2`-extensor of an
*orthonormal* pair spanning the same plane, the pair an orthogonal change-of-frame carries to a
coordinate blade (the standard-frame membership of OD-8 route-(α)). Grade-2-specific (the count
`⋀²P` line needs grade = `finrank P = 2`); ambient `Fin (d+1)` general (the `Fin (k+2)` site is
`d := k + 1`). -/
theorem exists_smul_extensor_eq_of_mem_span_range
    {d : ℕ} (u v : Fin 2 → Fin (d + 1) → K) (hv : LinearIndependent K v)
    (hu : ∀ i, u i ∈ Submodule.span K (Set.range v)) :
    ∃ c : K, c • (⟨extensor v, extensor_mem_exteriorPower v⟩ : ⋀[K]^2 (Fin (d + 1) → K))
      = ⟨extensor u, extensor_mem_exteriorPower u⟩ := by
  have hPdim : Module.finrank K (Submodule.span K (Set.range v)) = 2 := by
    rw [finrank_span_eq_card hv]; simp
  have hvmem : ∀ i, v i ∈ Submodule.span K (Set.range v) := fun i =>
    Submodule.subset_span ⟨i, rfl⟩
  have hxv : (⟨extensor v, extensor_mem_exteriorPower v⟩ : ⋀[K]^2 (Fin (d + 1) → K))
      ∈ LinearMap.range (exteriorPower.map 2 (Submodule.span K (Set.range v)).subtype) :=
    extensor_mem_range_map_subtype_of_mem_jgrade _ v hvmem
  have hxu : (⟨extensor u, extensor_mem_exteriorPower u⟩ : ⋀[K]^2 (Fin (d + 1) → K))
      ∈ LinearMap.range (exteriorPower.map 2 (Submodule.span K (Set.range v)).subtype) :=
    extensor_mem_range_map_subtype_of_mem_jgrade _ u hu
  have hvne : (⟨extensor v, extensor_mem_exteriorPower v⟩ : ⋀[K]^2 (Fin (d + 1) → K)) ≠ 0 := by
    rw [Ne, Subtype.ext_iff]; exact (extensor_ne_zero_iff_linearIndependent v).2 hv
  -- `range (map 2 P.subtype)` is a line; both extensors lie in it, so they are proportional.
  have hR : Module.finrank K
      (LinearMap.range (exteriorPower.map 2 (Submodule.span K (Set.range v)).subtype)) = 1 := by
    rw [LinearMap.finrank_range_of_inj (exteriorPower_map_subtype_injective_grade (d := d) 2 _),
      finrank_exteriorPower_self_eq_one hPdim]
  obtain ⟨z, hz⟩ := hxv
  have hspan : (K ∙ (⟨extensor v, extensor_mem_exteriorPower v⟩ : ⋀[K]^2 (Fin (d + 1) → K)))
      = LinearMap.range (exteriorPower.map 2 (Submodule.span K (Set.range v)).subtype) :=
    Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).2 ⟨z, hz⟩)
      (by rw [finrank_span_singleton hvne, hR])
  rw [← Submodule.mem_span_singleton, hspan]
  exact hxu

/-! ## N3b-2b-α building block: wedge-with-a-fixed-vector `⋀²K⁴` and its 3-dim range
(`lem:case-III-claim612-line-in-panel-union`)

The foundational sub-leaf of the panel-meet range membership N3b-2b-α (Phase 22f). The spanning
fact the membership rests on — that the shared-direction 2-extensors of `n = ![n_u, n']` span a
5-dimensional hyperplane of `⋀²K⁴` — is, via inclusion–exclusion, built from the two grade-2
subspaces `n_u ∧ K⁴` and `n' ∧ K⁴`, each the range of the *wedge-with-a-fixed-vector* map
`v ↦ n_u ∧ v` (resp. `n' ∧ v`). This block builds that map `wedgeFixedLeft a : K⁴ →ₗ ⋀²K⁴`,
identifies its kernel as the line `span{a}` (`a ∧ v = 0 ⟺ a, v` dependent ⟺ `v ∈ span{a}`, for
`a ≠ 0`), and reads off `finrank (range) = 4 − 1 = 3` by rank–nullity. The full `5 = 3 + 3 − 1`
span count (and the panel-meet membership it discharges) is the next sub-leaf above this. -/

/-- **The wedge-with-a-fixed-vector map** `v ↦ a ∧ v : K^{d+1} →ₗ ⋀²K^{d+1}`
(`lem:case-III-claim612-line-in-panel-union`, CHAIN-3 — ambient-generic over `Fin (d+1)`; the
`d=3` instance recovers the `Fin 4` map by `d+1 = 4`), the building block of the N3b-2b-α spanning
fact. It is the left exterior multiplication `LinearMap.mulLeft K (ι a)` by the homogeneous degree-1
element `ι a`, postcomposed with `ι` and corestricted to the grade-2 piece `⋀²K^{d+1}` (the product
`ι a * ι v` is grade `1 + 1 = 2`). On the underlying algebra it sends `v` to `extensor ![a, v]`
(`coe_wedgeFixedLeft`); its kernel is the line `span{a}` (`ker_wedgeFixedLeft`) and its range is
therefore `d`-dimensional (`finrank_range_wedgeFixedLeft`, `= (d+1) − 1`; `3` at `d=3`), the
`a ∧ K^{d+1}` summand of the shared-direction span. The proof is ambient-generic verbatim — `d`
enters only the ambient type, the grade is fixed at `2`. -/
noncomputable def wedgeFixedLeft {d : ℕ} (a : Fin (d + 1) → K) :
    (Fin (d + 1) → K) →ₗ[K] ⋀[K]^2 (Fin (d + 1) → K) :=
  LinearMap.codRestrict (⋀[K]^2 (Fin (d + 1) → K))
    ((LinearMap.mulLeft K (ExteriorAlgebra.ι K a)).comp (ExteriorAlgebra.ι K)) fun v => by
      have h : (LinearMap.mulLeft K (ExteriorAlgebra.ι K a)).comp (ExteriorAlgebra.ι K) v
          = extensor ![a, v] := by
        rw [LinearMap.comp_apply, LinearMap.mulLeft_apply, extensor_apply,
          ExteriorAlgebra.ιMulti_apply]
        simp [List.ofFn_succ]
      rw [h]; exact extensor_mem_exteriorPower _

/-- The underlying exterior-algebra element of `wedgeFixedLeft a v` is the `2`-extensor
`extensor ![a, v] = a ∧ v` (`lem:case-III-claim612-line-in-panel-union`). The bridge from the
linear-map packaging to the `extensor` API on which the kernel computation runs. -/
@[simp]
theorem coe_wedgeFixedLeft {d : ℕ} (a v : Fin (d + 1) → K) :
    (wedgeFixedLeft a v : ExteriorAlgebra K (Fin (d + 1) → K)) = extensor ![a, v] := by
  rw [wedgeFixedLeft, LinearMap.codRestrict_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    extensor_apply, ExteriorAlgebra.ιMulti_apply]
  simp [List.ofFn_succ]

/-- **The kernel of `wedgeFixedLeft a` is the line `span{a}`** for `a ≠ 0`
(`lem:case-III-claim612-line-in-panel-union`). `a ∧ v = 0` exactly when `![a, v]` is linearly
dependent (`extensor_ne_zero_iff_linearIndependent`), and for `a ≠ 0` a pair `![a, v]` is
dependent iff `v` lies in `span{a}` (`LinearIndependent.pair_iff'` ↔
`Submodule.mem_span_singleton`).
The rank–nullity input pinning `finrank (range (wedgeFixedLeft a)) = 3`
(`finrank_range_wedgeFixedLeft`). -/
theorem ker_wedgeFixedLeft {d : ℕ} {a : Fin (d + 1) → K} (ha : a ≠ 0) :
    LinearMap.ker (wedgeFixedLeft a) = Submodule.span K {a} := by
  ext v
  rw [LinearMap.mem_ker, Submodule.mem_span_singleton, ← Subtype.coe_inj, ZeroMemClass.coe_zero,
    coe_wedgeFixedLeft, ← not_iff_not, not_exists, ← ne_eq,
    extensor_ne_zero_iff_linearIndependent, LinearIndependent.pair_iff' ha]

/-- **The range of `wedgeFixedLeft a` is `d`-dimensional** for `a ≠ 0`
(`lem:case-III-claim612-line-in-panel-union`, CHAIN-3 — ambient-generic; `3` at `d=3`). By
rank–nullity (`LinearMap.finrank_range_add_finrank_ker`) on
`wedgeFixedLeft a : K^{d+1} →ₗ ⋀²K^{d+1}`, with the kernel the line `span{a}`
(`ker_wedgeFixedLeft`, `finrank = 1` for `a ≠ 0`) and the domain `K^{d+1}` (`finrank = d+1`), the
range has `finrank = (d+1) − 1 = d`. This is the `a ∧ K^{d+1}` summand of the shared-direction span
`Φ̃`; the general inclusion–exclusion count assembles `d−1` such summands (a panel `Π(u)` has `d−1`
normals), the genuinely-new count above this. -/
theorem finrank_range_wedgeFixedLeft {d : ℕ} {a : Fin (d + 1) → K} (ha : a ≠ 0) :
    Module.finrank K (LinearMap.range (wedgeFixedLeft a)) = d := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (wedgeFixedLeft a)
  rw [ker_wedgeFixedLeft ha, finrank_span_singleton ha, Module.finrank_fin_fun] at hrn
  omega

/-! ## N3b-recon: the coordinate `toDual` of `⋀ⁿK⁴` is the Gram-determinant pairing
(`lem:case-III-claim612-line-in-panel-union`)

The pivot infrastructure of the membership route (route A-corrected, Phase 22f): the `Module.Basis`
coordinate pairing `(b.exteriorPower n).toDual` on `⋀ⁿK⁴` (an opaque Kronecker pairing of the
exterior-power basis) is reconciled with the *computable* `exteriorPower.pairingDual` evaluated on
dual coordinates — the latter expands, via `exteriorPower.pairingDual_ιMulti_ιMulti`, as a **Gram
determinant** of dot products. This is what turns `b.toDual (w₀ ∧ w₁) (extensor c)` into
`det [[w₀·c₀, w₀·c₁], [w₁·c₀, w₁·c₁]]`, so the incidence `wᵢ · c₀ = 0` (both in `{n_u,n'}^⊥`) zeros
a column and kills the point-join — fact 2 of route A-corrected — and likewise pins
`dim (dualCoannihilator Φ̃) = 6 − 5 = 1` (fact 3), since `b.toDual` is a perfect pairing.

Both sides are linear maps `⋀ⁿK⁴ →ₗ Dual ⋀ⁿK⁴`; equality is by double `Module.Basis.ext` on the
exterior-power basis, after which the coordinate pairing collapses to a Kronecker delta
(`Module.Basis.toDual_apply`) and the `pairingDual`/`map` side collapses to the determinant of
that same Kronecker matrix (`map_apply_ιMulti_family` + `pairingDual_ιMulti_ιMulti`). -/

/-- **N3b-recon at general grade and ambient: the coordinate `toDual` of `⋀ⁿ(K^{d+1})` is the
Gram-determinant pairing** (`lem:case-III-claim612-line-in-panel-union`, CHAIN-3 — the grade- and
ambient-generic restatement of the `Fin 4`-pinned `d=3`
`exteriorPower_basis_toDual_eq_pairingDual_comp_map`). For the standard basis
`b = Pi.basisFun K (Fin (d+1))` and any grade `n`, the `Module.Basis` coordinate pairing
`(b.exteriorPower n).toDual` on `⋀ⁿ(K^{d+1})` equals the computable
`exteriorPower.pairingDual ∘ exteriorPower.map n b.toDual` (the Gram-determinant pairing). The proof
is **ambient- and grade-generic verbatim** (`Module.Basis.ext` ×2, then `Module.Basis.toDual_apply`
collapses the coordinate side to a Kronecker delta and `map_apply_ιMulti_family` +
`pairingDual_ιMulti_ιMulti` collapse the other side to the determinant of that same Kronecker
matrix; the diagonal/off-diagonal split uses only the equal-cardinality fact
`Set.powersetCard.card_eq`, no `Fin 4`-arity). The `d=3` instance recovers
`exteriorPower_basis_toDual_eq_pairingDual_comp_map` (`d+1 = 4`). -/
theorem exteriorPower_basis_toDual_eq_pairingDual_comp_map_grade {d : ℕ} (n : ℕ) :
    ((Pi.basisFun K (Fin (d + 1))).exteriorPower n).toDual =
      (exteriorPower.pairingDual K (Fin (d + 1) → K) n).comp
        (exteriorPower.map n (Pi.basisFun K (Fin (d + 1))).toDual) := by
  refine ((Pi.basisFun K (Fin (d + 1))).exteriorPower n).ext fun s => ?_
  refine ((Pi.basisFun K (Fin (d + 1))).exteriorPower n).ext fun t => ?_
  rw [Module.Basis.toDual_apply, LinearMap.comp_apply, exteriorPower.basis_apply,
    exteriorPower.basis_apply, exteriorPower.map_apply_ιMulti_family, exteriorPower.ιMulti_family,
    exteriorPower.ιMulti_family, exteriorPower.pairingDual_ιMulti_ιMulti]
  simp only [Function.comp_apply, Module.Basis.toDual_apply]
  split_ifs with hst
  · -- Diagonal: `s = t`, the matrix is the identity (`σ_s` injective), determinant `1`.
    subst hst
    rw [show (Matrix.of fun i j => if (Set.powersetCard.ofFinEmbEquiv.symm s) j =
        (Set.powersetCard.ofFinEmbEquiv.symm s) i then (1 : K) else 0) = 1 from ?_, Matrix.det_one]
    ext i j
    simp only [Matrix.of_apply, Matrix.one_apply, EmbeddingLike.apply_eq_iff_eq, eq_comm]
  · -- Off-diagonal: `s ≠ t`, equal cardinality forces an element of `t` outside `s`, a zero row.
    obtain ⟨x, hxt, hxs⟩ :
        ∃ x, x ∈ (↑t : Finset (Fin (d + 1))) ∧ x ∉ (↑s : Finset (Fin (d + 1))) := by
      refine Finset.not_subset.1 fun hsub => hst ?_
      exact Subtype.ext (Finset.eq_of_subset_of_card_le hsub
        (by rw [Set.powersetCard.card_eq, Set.powersetCard.card_eq])).symm
    obtain ⟨i₀, hi₀⟩ : ∃ i₀, (Set.powersetCard.ofFinEmbEquiv.symm t) i₀ = x :=
      (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem t x).2 hxt
    refine (Matrix.det_eq_zero_of_row_eq_zero i₀ fun j => ?_).symm
    simp only [Matrix.of_apply, hi₀]
    exact if_neg fun h => hxs ((Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s x).1 ⟨j, h⟩)

/-- **N3b-recon (`d=3` instance): the coordinate `toDual` of `⋀ⁿK⁴` is the Gram-determinant
pairing** (`lem:case-III-claim612-line-in-panel-union`). The `d=3` instance (ambient `Fin 4`) of the
grade- and ambient-generic `exteriorPower_basis_toDual_eq_pairingDual_comp_map_grade` (`d+1 = 4`).
The `Module.Basis` coordinate pairing `(b.exteriorPower n).toDual` on `⋀ⁿK⁴` is reconciled with the
computable `exteriorPower.pairingDual` evaluated on dual coordinates — the latter expands, via
`exteriorPower.pairingDual_ιMulti_ιMulti`, as a **Gram determinant** of dot products. This is what
turns `b.toDual (w₀ ∧ w₁) (extensor c)` into `det [[w₀·c₀, w₀·c₁], [w₁·c₀, w₁·c₁]]`, so the
incidence `wᵢ · c₀ = 0` (both in `{n_u,n'}^⊥`) zeros a column and kills the point-join — fact 2 of
route A-corrected — and likewise pins `dim (dualCoannihilator Φ̃) = 6 − 5 = 1` (fact 3), since
`b.toDual` is a perfect pairing. -/
theorem exteriorPower_basis_toDual_eq_pairingDual_comp_map (n : ℕ) :
    ((Pi.basisFun K (Fin 4)).exteriorPower n).toDual =
      (exteriorPower.pairingDual K (Fin 4 → K) n).comp
        (exteriorPower.map n (Pi.basisFun K (Fin 4)).toDual) :=
  exteriorPower_basis_toDual_eq_pairingDual_comp_map_grade (d := 3) n

/-! ## Fact 2 of the membership route: the point-join is `toDual`-orthogonal to a shared extensor
(`lem:case-III-claim612-line-in-panel-union`)

The genuinely-new annihilation of the membership route (route A-corrected, Phase 22f). The
point-join `w₀ ∧ w₁ = extensor w` of two vectors orthogonal to a shared panel normal `c i₀` is
annihilated, under the standard exterior-power basis's coordinate pairing `toDual`, by every
`2`-extensor `extensor c` through that normal. Through the reconciliation
`b.toDual = pairingDual ∘ map b.toDual` (N3b-recon), the pairing
`b.toDual (extensor w) (extensor c)` is the **Gram determinant**
`det (Matrix.of fun i j => b.toDual (w j) (c i))` (`pairingDual_ιMulti_ιMulti`); the incidence
hypothesis `b.toDual (w j) (c i₀) = 0` for every `j` makes row `i₀` vanish, so the determinant is
`0` (`Matrix.det_eq_zero_of_row_eq_zero`).

This is the companion of green step (i)
(`complementIso_toDual_extensor_eq_zero_of_shared_vector`, the panel-meet's annihilation): step (i)
puts `complementIso(n_u ∧ n')` in `Ω = dualCoannihilator Φ̃`, this fact puts the point-join
`w₀ ∧ w₁` (`wᵢ ∈ W = {n_u, n'}^⊥`) there too. With `dim Ω = 1` (fact 3,
`finrank_sup_range_wedgeFixedLeft`) the two members are proportional — the membership that subsumes
N3b-3. Both `wᵢ` orthogonal to the shared normal is exactly the incidence `wᵢ ∈ W`; the prior
commit's "Route A overturned" tested the volume/wedge pairing `vol(· ∧ ·)` here by mistake, where
the point-join is *not* annihilated — under the coordinate pairing `b.toDual`, the Gram
determinant, it is. -/

/-- **Fact 2 of the membership route: the point-join is `toDual`-orthogonal to a shared extensor**
(`lem:case-III-claim612-line-in-panel-union`). At `d = 3` (`⋀²K⁴`), if every vector of
`w : Fin 2 → K⁴` is `toDual`-orthogonal to the shared vector `c i₀` of a second family
`c : Fin 2 → K⁴` (`hperp : ∀ j, (Pi.basisFun K (Fin 4)).toDual (w j) (c i₀) = 0`), then the
point-join `extensor w` is annihilated, through the standard exterior-power basis's `toDual`, by
`extensor c`. Via N3b-recon (`exteriorPower_basis_toDual_eq_pairingDual_comp_map`) the pairing is
the Gram determinant `det (Matrix.of fun i j => b.toDual (w j) (c i))`
(`pairingDual_ιMulti_ιMulti`), whose row `i₀` vanishes by `hperp`, so it is `0`
(`Matrix.det_eq_zero_of_row_eq_zero`). The point-join analogue of green step (i)'s panel-meet
annihilation: both land in `Ω = dualCoannihilator Φ̃`, a line by fact 3, forcing the
proportionality of meet and join. -/
theorem extensor_toDual_extensor_eq_zero_of_perp (w c : Fin 2 → Fin 4 → K) (i₀ : Fin 2)
    (hperp : ∀ j, (Pi.basisFun K (Fin 4)).toDual (w j) (c i₀) = 0) :
    ((Pi.basisFun K (Fin 4)).exteriorPower 2).toDual
        ⟨extensor w, extensor_mem_exteriorPower w⟩
        ⟨extensor c, extensor_mem_exteriorPower c⟩ = 0 := by
  have hw : (⟨extensor w, extensor_mem_exteriorPower w⟩ : ⋀[K]^2 (Fin 4 → K))
      = exteriorPower.ιMulti K 2 w := by
    apply Subtype.ext; rw [exteriorPower.ιMulti_apply_coe]; rfl
  have hc : (⟨extensor c, extensor_mem_exteriorPower c⟩ : ⋀[K]^2 (Fin 4 → K))
      = exteriorPower.ιMulti K 2 c := by
    apply Subtype.ext; rw [exteriorPower.ιMulti_apply_coe]; rfl
  rw [hw, hc, exteriorPower_basis_toDual_eq_pairingDual_comp_map, LinearMap.comp_apply,
    exteriorPower.map_apply_ιMulti, exteriorPower.pairingDual_ιMulti_ιMulti]
  refine Matrix.det_eq_zero_of_row_eq_zero i₀ fun j => ?_
  rw [Matrix.of_apply, Function.comp_apply]
  exact hperp j

/-! ## N3b-2b-β: the shared-direction span `Φ̃ = n_u ∧ K⁴ + n' ∧ K⁴` is `5`-dimensional
(`lem:case-III-claim612-line-in-panel-union`)

Fact 3 of the membership route (route A-corrected, Phase 22f): the count pinning the dual
coannihilator `Ω = dualCoannihilator Φ̃` to a line. The shared-direction span
`Φ̃ = n_u ∧ K⁴ + n' ∧ K⁴` (the join of the two wedge-with-a-fixed-normal ranges, each
`3`-dimensional by `finrank_range_wedgeFixedLeft`) is `5`-dimensional by inclusion–exclusion
(`3 + 3 − 1`, `Submodule.finrank_sup_add_finrank_inf_eq`); the genuine content is the
**decomposable intersection** `n_u ∧ K⁴ ⊓ n' ∧ K⁴ = span{n_u ∧ n'}` (`inf_range_wedgeFixedLeft`,
`finrank = 1`). With `b.toDual` a perfect pairing on the `6`-dimensional `⋀²K⁴`, this gives
`dim Ω = 6 − 5 = 1`, so the panel-meet (green step (i)) and the point-join (fact 2), both in `Ω`,
are proportional. -/

/-- **The decomposable intersection: `n_u ∧ K^{d+1} ⊓ n' ∧ K^{d+1} = span{n_u ∧ n'}`**
(`lem:case-III-claim612-line-in-panel-union`, CHAIN-3 — ambient-generic over `Fin (d+1)`; the `d=3`
instance recovers the `Fin 4` statement by `d+1 = 4`). The genuine sub-content of the span count
(fact 3 of the membership route). For two linearly-independent vectors `a, b ∈ K^{d+1}`, the
wedge-with-a range `a ∧ K^{d+1}` (`range (wedgeFixedLeft a)`) and `b ∧ K^{d+1}` meet exactly in the
line `span{a ∧ b}`. `⊇` is direct: `a ∧ b = wedgeFixedLeft a b` lies in `range (wedgeFixedLeft a)`,
and `= b ∧ (−a) = wedgeFixedLeft b (−a)` (anticommutativity `ExteriorAlgebra.ι_add_mul_swap`) lies
in `range (wedgeFixedLeft b)`. `⊆`: an element `a ∧ v = b ∧ w` in both ranges, left-multiplied by
`b`, gives `b ∧ a ∧ v = b ∧ b ∧ w = 0` (repeated factor), so `extensor ![b, a, v] = 0`, i.e.
`{b, a, v}` is dependent; with `{a, b}` independent (`linearIndependent_finSnoc`) this forces
`v ∈ span{a, b}`, whence `a ∧ v = β · (a ∧ b) ∈ span{a ∧ b}` (`a ∧ a = 0`). The proof is
ambient-generic verbatim — `d` enters only the ambient type, the family arities (`Fin 2`, `Fin 3`)
are fixed. -/
theorem inf_range_wedgeFixedLeft {d : ℕ} (a b : Fin (d + 1) → K)
    (hab : LinearIndependent K ![a, b]) :
    LinearMap.range (wedgeFixedLeft a) ⊓ LinearMap.range (wedgeFixedLeft b)
      = Submodule.span K {wedgeFixedLeft a b} := by
  apply le_antisymm
  · rintro z ⟨⟨v, hv⟩, ⟨w, hw⟩⟩
    -- `z = a ∧ v = b ∧ w`; left-multiplying by `b` gives `b ∧ a ∧ v = b ∧ b ∧ w = 0`,
    -- so `{b, a, v}` is dependent, hence `v ∈ span{a, b}`.
    have hbav : extensor (![b, a, v] : Fin 3 → Fin (d + 1) → K) = 0 := by
      have key : extensor ![b] ∨ₑ extensor ![a, v] = extensor ![b] ∨ₑ extensor ![b, w] := by
        rw [← Subtype.coe_inj, coe_wedgeFixedLeft] at hv hw; rw [hv, hw]
      rw [join_extensor, join_extensor,
        show Fin.append (![b] : Fin 1 → Fin (d + 1) → K) ![a, v] = ![b, a, v] by
          ext i x; fin_cases i <;> rfl,
        extensor_eq_zero_of_eq (Fin.append (![b] : Fin 1 → Fin (d + 1) → K) ![b, w])
          (a := 0) (b := 1) rfl (by decide)] at key
      exact key
    have hba : LinearIndependent K ![b, a] := by
      rw [LinearIndependent.pair_iff] at hab ⊢
      exact fun s t h => (hab t s (by rw [← h]; ring)).symm
    have hvmem : v ∈ Submodule.span K {a, b} := by
      have hvn : v ∈ Submodule.span K (Set.range (![b, a] : Fin 2 → Fin (d + 1) → K)) := by
        by_contra hvn
        refine (extensor_ne_zero_iff_linearIndependent _).mpr
          ((linearIndependent_finSnoc (x := v)).mpr ⟨hba, hvn⟩) ?_
        rw [show Fin.snoc ![b, a] v = (![b, a, v] : Fin 3 → Fin (d + 1) → K) by
          ext i x; fin_cases i <;> rfl]
        exact hbav
      rwa [show (Set.range (![b, a] : Fin 2 → Fin (d + 1) → K)) = {a, b} by
        rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
          Set.singleton_union, Set.pair_comm]] at hvn
    -- `a ∧ v` for `v = α • a + β • b` is `β • (a ∧ b) ∈ span{a ∧ b}`.
    obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hvmem
    rw [Submodule.mem_span_singleton, show z = wedgeFixedLeft a v from hv.symm, ← hαβ]
    refine ⟨β, ?_⟩
    rw [map_add, map_smul, map_smul]
    have haa : wedgeFixedLeft a a = 0 := by
      apply Subtype.ext
      rw [coe_wedgeFixedLeft, ZeroMemClass.coe_zero]
      exact extensor_eq_zero_of_eq _ (a := 0) (b := 1) rfl (by decide)
    rw [haa, smul_zero, zero_add]
  · rw [Submodule.span_singleton_le_iff_mem]
    refine ⟨⟨b, rfl⟩, -a, ?_⟩
    apply Subtype.ext
    rw [coe_wedgeFixedLeft, coe_wedgeFixedLeft, extensor_apply, extensor_apply,
      ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply]
    simp only [List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero, Matrix.cons_val_one,
      List.prod_cons, List.prod_nil, mul_one, Fin.succ_zero_eq_one]
    rw [map_neg, mul_neg]
    exact (eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap a b)).symm

/-- **N3b-2b-β: the shared-direction span `n_u ∧ K⁴ + n' ∧ K⁴` is `5`-dimensional**
(`lem:case-III-claim612-line-in-panel-union`). Fact 3 of the membership route (route A-corrected,
Phase 22f). For two linearly-independent `a, b ∈ K⁴`, the join `a ∧ K⁴ + b ∧ K⁴` (the
shared-direction span `Φ̃`) has dimension `5`. By inclusion–exclusion
(`Submodule.finrank_sup_add_finrank_inf_eq`), `dim (a ∧ K⁴ ⊔ b ∧ K⁴) = dim (a ∧ K⁴) + dim (b ∧ K⁴) −
dim (a ∧ K⁴ ⊓ b ∧ K⁴) = 3 + 3 − 1 = 5`, the two summand dimensions from
`finrank_range_wedgeFixedLeft` and the intersection dimension `1` from the decomposable
intersection `inf_range_wedgeFixedLeft` (with `a ∧ b ≠ 0` by independence). Since `b.toDual` is a
perfect pairing on the `6`-dimensional `⋀²K⁴`, this forces
`dim Ω = dim (dualCoannihilator Φ̃) = 6 − 5 = 1` — the line into which fact 2 (the point-join) and
green step (i) (the panel-meet) both fall, making them proportional. -/
theorem finrank_sup_range_wedgeFixedLeft (a b : Fin 4 → K) (hab : LinearIndependent K ![a, b]) :
    Module.finrank K
        ((LinearMap.range (wedgeFixedLeft a) ⊔ LinearMap.range (wedgeFixedLeft b) :
          Submodule K (⋀[K]^2 (Fin 4 → K)))) = 5 := by
  have ha : a ≠ 0 := by simpa using hab.ne_zero 0
  have hb : b ≠ 0 := by simpa using hab.ne_zero 1
  have hne : wedgeFixedLeft a b ≠ 0 := fun h => by
    refine (extensor_ne_zero_iff_linearIndependent ![a, b]).mpr hab ?_
    rw [← coe_wedgeFixedLeft, h, ZeroMemClass.coe_zero]
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range (wedgeFixedLeft a)) (LinearMap.range (wedgeFixedLeft b))
  rw [inf_range_wedgeFixedLeft a b hab, finrank_span_singleton hne,
    finrank_range_wedgeFixedLeft (d := 3) ha, finrank_range_wedgeFixedLeft (d := 3) hb] at hsum
  -- `omega` mis-atomizes the two `wedgeFixedLeft` elaborations here (the implicit-`d` lift); the
  -- hypothesis `hsum : finrank(…) + 1 = 3 + 3` closes the `= 5` goal directly.
  simpa using hsum

/-! ## The point-join ↔ panel-meet duality (the membership assembly N3b, KT eq. (6.45))
(`lem:case-III-claim612-line-in-panel-union`)

The capstone of the duality bridge (Phase 22f): the point-join `p̄ᵢ ∨ p̄ⱼ = extensor ![p̄ᵢ, p̄ⱼ]`
and the panel-meet `C(L) = complementIso(n_u ∧ n')` of the *same* line `L = p̄ᵢ p̄ⱼ ⊂ Π(u)` are
scalar multiples in `⋀²K⁴`. The membership route (route A-corrected, *Decisions made*): both lie
in the common `1`-dimensional space `Ω = dualAnnihilator Φ̃` transported across the perfect pairing
`b.toDualEquiv : ⋀²K⁴ ≃ₗ Dual(⋀²K⁴)`, where `Φ̃ = n_u ∧ K⁴ + n' ∧ K⁴` is the `5`-dimensional
shared-direction span (fact 3, `finrank_sup_range_wedgeFixedLeft`); `dim Ω = 6 − 5 = 1`. The
point-join is in `Ω` by the Gram-determinant orthogonality (fact 2,
`extensor_toDual_extensor_eq_zero_of_perp`, applied to each summand `n_u ∧ v` / `n' ∧ v`, since
`p̄ᵢ, p̄ⱼ` are `toDual`-orthogonal to both `n_u` and `n'`); the panel-meet is in `Ω` by the
dictionary half (fact 1 = green step (i), `complementIso_toDual_eq_zero_of_wedgeProd_eq_zero`, the
`n_u ∧ v` summand sharing `n_u` directly, the `n' ∧ v` summand via the shared `n'` in the appended
family). Two members of a line, the panel-meet nonzero (`{n_u, n'}` independent), are proportional.

The annihilation transfer is then immediate: a screw functional `r` with `r(C(L)) = 0` has
`r(p̄ᵢ ∨ p̄ⱼ) = c · r(C(L)) = 0` for the scale `c`. This is the duality KT use implicitly reading
eq. (6.45): the spanning point-joins and the annihilated panel-meets are the *same* extensors of
the lines in the panel union (KT §6.4.1). -/

/-- **The point-join ↔ panel-meet proportionality** (`lem:case-III-claim612-line-in-panel-union`,
N3b assembly). At `d = 3` (`⋀²K⁴`), let `n_u, n'` be the two panel normals of a panel `Π(u)`
(`{n_u, n'}` independent) and `pi, pj` two points whose connecting line `L = pi pj` lies in `Π(u)`
(each `pi, pj` is `toDual`-orthogonal to both normals — the incidence `⟨p̄, n_u⟩ = ⟨p̄, n'⟩ = 0`).
Then the point-join `extensor ![pi, pj]` is a scalar multiple of the panel-meet
`complementIso (n_u ∧ n')`: `∃ c, c • complementIso(n_u ∧ n') = extensor ![pi, pj]`. Both are the
Plücker vector of `L`, up to the projective scale. Membership route A-corrected: both lie in the
`1`-dimensional `Ω = dualAnnihilator Φ̃` (fact 3) — the point-join by the Gram-determinant
orthogonality (fact 2), the panel-meet by the dictionary half (green step (i)) — and the panel-meet
is nonzero, so the two are proportional. -/
theorem complementIso_smul_eq_extensor_join (n_u n' pi pj : Fin 4 → K)
    (hpair : LinearIndependent K ![n_u, n'])
    (hi_u : (Pi.basisFun K (Fin 4)).toDual pi n_u = 0)
    (hi_u' : (Pi.basisFun K (Fin 4)).toDual pi n' = 0)
    (hj_u : (Pi.basisFun K (Fin 4)).toDual pj n_u = 0)
    (hj_u' : (Pi.basisFun K (Fin 4)).toDual pj n' = 0) :
    ∃ c : K, c • (complementIso (k := 2) (j := 2) (by omega)
        ⟨extensor ![n_u, n'], extensor_mem_exteriorPower _⟩)
      = (⟨extensor ![pi, pj], extensor_mem_exteriorPower _⟩ : ⋀[K]^2 (Fin 4 → K)) := by
  set b := Pi.basisFun K (Fin 4) with hb
  set Φ : Submodule K (⋀[K]^2 (Fin 4 → K)) :=
    LinearMap.range (wedgeFixedLeft n_u) ⊔ LinearMap.range (wedgeFixedLeft n') with hΦ
  set Ω : Submodule K (⋀[K]^2 (Fin 4 → K)) :=
    Φ.dualAnnihilator.comap (b.exteriorPower 2).toDualEquiv.toLinearMap with hΩ
  -- `dim Ω = 6 − dim Φ̃ = 6 − 5 = 1` (fact 3 + the perfect pairing's annihilator count).
  have hdim : Module.finrank K Ω = 1 := by
    rw [hΩ, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
    have h6 : Module.finrank K (⋀[K]^2 (Fin 4 → K)) = 6 := by
      rw [exteriorPower.finrank_eq, Module.finrank_pi]; rfl
    have hkey := Subspace.finrank_add_finrank_dualAnnihilator_eq Φ
    have h5 : Module.finrank K Φ = 5 := finrank_sup_range_wedgeFixedLeft n_u n' hpair
    omega
  -- A member that `toDual`-kills all of `Φ̃` lies in `Ω`.
  have hmem : ∀ Z : ⋀[K]^2 (Fin 4 → K),
      (∀ φ ∈ Φ, (b.exteriorPower 2).toDual Z φ = 0) → Z ∈ Ω := by
    intro Z hZ
    rw [hΩ, Submodule.mem_comap, Submodule.mem_dualAnnihilator]
    intro φ hφ
    rw [LinearEquiv.coe_coe, Module.Basis.toDualEquiv_apply]
    exact hZ φ hφ
  -- Killing both summand ranges `n_u ∧ K⁴`, `n' ∧ K⁴` kills all of `Φ̃`.
  have hkills : ∀ Z : ⋀[K]^2 (Fin 4 → K),
      (∀ v, (b.exteriorPower 2).toDual Z (wedgeFixedLeft n_u v) = 0) →
      (∀ v, (b.exteriorPower 2).toDual Z (wedgeFixedLeft n' v) = 0) → Z ∈ Ω := by
    intro Z hu hv'
    refine hmem Z fun φ hφ => ?_
    rw [hΦ, Submodule.mem_sup] at hφ
    obtain ⟨x, ⟨vx, hx⟩, y, ⟨vy, hy⟩, rfl⟩ := hφ
    rw [map_add, ← hx, ← hy, hu, hv', add_zero]
  -- The point-join `extensor ![pi, pj] ∈ Ω`: fact 2 (Gram-det orthogonality) on each summand.
  have hJ : (⟨extensor ![pi, pj], extensor_mem_exteriorPower _⟩ : ⋀[K]^2 (Fin 4 → K)) ∈ Ω := by
    refine hkills _ (fun v => ?_) (fun v => ?_)
    · rw [show (wedgeFixedLeft n_u v) = (⟨extensor ![n_u, v], extensor_mem_exteriorPower _⟩ :
          ⋀[K]^2 (Fin 4 → K)) from by apply Subtype.ext; rw [coe_wedgeFixedLeft]]
      exact extensor_toDual_extensor_eq_zero_of_perp ![pi, pj] ![n_u, v] 0
        (by simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
            exact ⟨hi_u, hj_u⟩)
    · rw [show (wedgeFixedLeft n' v) = (⟨extensor ![n', v], extensor_mem_exteriorPower _⟩ :
          ⋀[K]^2 (Fin 4 → K)) from by apply Subtype.ext; rw [coe_wedgeFixedLeft]]
      exact extensor_toDual_extensor_eq_zero_of_perp ![pi, pj] ![n', v] 0
        (by simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
            exact ⟨hi_u', hj_u'⟩)
  -- The panel-meet `complementIso (n_u ∧ n') ∈ Ω`: green step (i) on each summand (the `n'`
  -- summand through the appended-family shared `n'`).
  have hC : (complementIso (k := 2) (j := 2) (by omega)
      ⟨extensor ![n_u, n'], extensor_mem_exteriorPower _⟩) ∈ Ω := by
    refine hkills _ (fun v => ?_) (fun v => ?_)
    · rw [show (wedgeFixedLeft n_u v) = (⟨extensor ![n_u, v], extensor_mem_exteriorPower _⟩ :
          ⋀[K]^2 (Fin 4 → K)) from by apply Subtype.ext; rw [coe_wedgeFixedLeft]]
      exact complementIso_toDual_extensor_eq_zero_of_shared_vector ![n_u, n'] ![n_u, v] rfl
    · have hwp : wedgeProd (k := 2) (j := 2) (by omega)
          ⟨extensor ![n_u, n'], extensor_mem_exteriorPower _⟩
          ⟨extensor ![n', v], extensor_mem_exteriorPower _⟩ = 0 := by
        apply Subtype.ext
        rw [coe_wedgeProd, ZeroMemClass.coe_zero]
        change extensor ![n_u, n'] ∨ₑ extensor ![n', v] = 0
        rw [join_extensor]
        apply extensor_eq_zero_of_eq _ (a := Fin.castAdd 2 1) (b := Fin.natAdd 2 0)
        · rw [Fin.append_left, Fin.append_right]; rfl
        · decide
      rw [show (wedgeFixedLeft n' v) = (⟨extensor ![n', v], extensor_mem_exteriorPower _⟩ :
          ⋀[K]^2 (Fin 4 → K)) from by apply Subtype.ext; rw [coe_wedgeFixedLeft]]
      exact complementIso_toDual_eq_zero_of_wedgeProd_eq_zero (k := 2) (j := 2) (by omega)
        ⟨extensor ![n_u, n'], extensor_mem_exteriorPower _⟩
        ⟨extensor ![n', v], extensor_mem_exteriorPower _⟩ hwp
  -- The panel-meet is nonzero (`{n_u, n'}` independent), so the two members of the line `Ω` are
  -- proportional.
  have hXne : (⟨extensor ![n_u, n'], extensor_mem_exteriorPower _⟩ : ⋀[K]^2 (Fin 4 → K)) ≠ 0 := by
    rw [Ne, Subtype.ext_iff, ZeroMemClass.coe_zero]
    exact (extensor_ne_zero_iff_linearIndependent ![n_u, n']).mpr hpair
  have hCne := (LinearEquiv.map_ne_zero_iff (complementIso (k := 2) (j := 2) (by omega))).mpr hXne
  have hspan : (K ∙ (complementIso (k := 2) (j := 2) (by omega)
      ⟨extensor ![n_u, n'], extensor_mem_exteriorPower _⟩)) = Ω :=
    Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).2 hC)
      (by rw [finrank_span_singleton hCne, hdim])
  rw [← Submodule.mem_span_singleton, hspan]
  exact hJ

/-- **Point-join ↔ panel-meet duality: the annihilation transfer**
(`lem:case-III-claim612-line-in-panel-union`, N3b, KT eq. (6.45)). At `d = 3` (`⋀²K⁴`), with the
line incidence of `complementIso_smul_eq_extensor_join` (`{n_u, n'}` independent panel normals of
`Π(u)`, the two points `pi, pj` of the line `L = pi pj ⊂ Π(u)` orthogonal to both normals), a screw
functional `r : Dual(⋀²K⁴)` annihilating the panel-meet `C(L) = complementIso (n_u ∧ n')` also
annihilates the spanning point-join `p̄ᵢ ∨ p̄ⱼ = extensor ![pi, pj]`. Immediate from the
proportionality `extensor ![pi, pj] = c • complementIso (n_u ∧ n')`
(`complementIso_smul_eq_extensor_join`): `r(extensor ![pi, pj]) = c · r(C(L)) = 0`. This is the
contrapositive glue of the Claim 6.12 capstone: an `r` annihilating every panel-meet of lines in
`Π(a) ∪ Π(b) ∪ Π(c)` annihilates each spanning join, forcing `r = 0`. -/
theorem extensor_join_eq_zero_of_complementIso_eq_zero (n_u n' pi pj : Fin 4 → K)
    (hpair : LinearIndependent K ![n_u, n'])
    (hi_u : (Pi.basisFun K (Fin 4)).toDual pi n_u = 0)
    (hi_u' : (Pi.basisFun K (Fin 4)).toDual pi n' = 0)
    (hj_u : (Pi.basisFun K (Fin 4)).toDual pj n_u = 0)
    (hj_u' : (Pi.basisFun K (Fin 4)).toDual pj n' = 0)
    (r : Module.Dual K (⋀[K]^2 (Fin 4 → K)))
    (hr : r (complementIso (k := 2) (j := 2) (by omega)
      ⟨extensor ![n_u, n'], extensor_mem_exteriorPower _⟩) = 0) :
    r ⟨extensor ![pi, pj], extensor_mem_exteriorPower _⟩ = 0 := by
  obtain ⟨c, hc⟩ := complementIso_smul_eq_extensor_join n_u n' pi pj hpair hi_u hi_u' hj_u hj_u'
  rw [← hc, map_smul, hr, smul_zero]

/-- **Point-join ↔ panel-meet duality, the dot-product incidence form**
(`lem:case-III-claim612-line-in-panel-union`, N3b, KT eq. (6.45); Phase 22g). The N3a-compatible
restatement of `extensor_join_eq_zero_of_complementIso_eq_zero`: the panel incidence is phrased as
the plain dot product `pi ⬝ᵥ n_u = 0` (the form `exists_affineIndependent_panel_incidence`, N3a,
emits) rather than the standard-basis pairing `(Pi.basisFun K (Fin 4)).toDual pi n_u = 0` of the
exterior-algebra core. At `d = 3` (`⋀²K⁴`), with `{n_u, n'}` independent panel normals of `Π(u)` and
two points `pi, pj` of the line `L = pi pj ⊂ Π(u)` (each dot-orthogonal to both normals), a screw
functional `r` annihilating the panel-meet `C(L) = complementIso (n_u ∧ n')` also annihilates the
spanning point-join `p̄ᵢ ∨ p̄ⱼ = extensor ![pi, pj]`.

This is the per-line annihilation transfer the Claim-6.12 capstone (`case_III_claim612`'s
`hduality`) dispatches over the six joins `pᵢ ∨ pⱼ` of the four affinely-independent points of
eq. (6.45): each join lies in (at least) one of the three panels `Π(a) ∪ Π(b) ∪ Π(c)`, so `r`
orthogonal to that panel's meet annihilates it. The only content over the core is the incidence-form
conversion, via the self-pairing identity `Pi.basisFun_toDual_apply`
(`(Pi.basisFun K (Fin 4)).toDual x y = x ⬝ᵥ y`). -/
theorem extensor_join_eq_zero_of_complementIso_eq_zero_dotProduct (n_u n' pi pj : Fin 4 → K)
    (hpair : LinearIndependent K ![n_u, n'])
    (hi_u : pi ⬝ᵥ n_u = 0) (hi_u' : pi ⬝ᵥ n' = 0)
    (hj_u : pj ⬝ᵥ n_u = 0) (hj_u' : pj ⬝ᵥ n' = 0)
    (r : Module.Dual K (⋀[K]^2 (Fin 4 → K)))
    (hr : r (complementIso (k := 2) (j := 2) (by omega)
      ⟨extensor ![n_u, n'], extensor_mem_exteriorPower _⟩) = 0) :
    r ⟨extensor ![pi, pj], extensor_mem_exteriorPower _⟩ = 0 :=
  extensor_join_eq_zero_of_complementIso_eq_zero n_u n' pi pj hpair
    (by rw [Pi.basisFun_toDual_apply]; exact hi_u) (by rw [Pi.basisFun_toDual_apply]; exact hi_u')
    (by rw [Pi.basisFun_toDual_apply]; exact hj_u) (by rw [Pi.basisFun_toDual_apply]; exact hj_u')
    r hr

/-! ## The `complementIso` of a standard basis blade is the complementary blade
(`def:meet-complement-iso`)

The foundational `complementIso`-image fact, the base case of the route-(α) panel-meet
range-membership (CHAIN-3, OD-8). The complement isomorphism `complementIso hj : ⋀ʲ V ≃ₗ ⋀^(N−j) V`
(`N = k+2`) sends a standard exterior-power basis blade `e_S` (`S ⊆ Fin (k+2)`, `|S| = j`) to a
scalar multiple of the complementary blade `e_{Sᶜ}` — the projective dual of a coordinate subspace
is the complementary coordinate subspace. The scalar is the `±1` wedge pairing
`wedgePairing k hj (e_S) (e_{Sᶜ})` (`wedgePairing_ιMulti_family_compl_ne_zero`, the
signed-permutation diagonal). -/

/-- **The `complementIso` of a standard basis blade is the complementary blade**
(`def:meet-complement-iso`, CHAIN-3 — the foundational `complementIso`-image leaf for the OD-8
route-(α) panel-meet range-membership). `complementIso hj` sends the standard `⋀ʲ` basis blade
`e_S` to the scalar multiple `(wedgePairing k hj e_S e_{Sᶜ}) • e_{Sᶜ}` of the complementary
`⋀^(N−j)` basis blade `e_{Sᶜ}` (`Sᶜ` via `Set.powersetCard.compl`), with the `±1` scalar the
signed-permutation diagonal entry (`wedgePairing_ιMulti_family_compl_ne_zero` for its
non-vanishing). Read off the change-of-basis matrix: the `t`-coordinate of `complementIso hj e_S`
is `wedgePairing k hj e_S e_t` (the dual-basis reading `Module.Basis.coord_toDualEquiv_symm_apply`
of `complementIso = wedgePairing ≪≫ toDualEquiv.symm`), which vanishes off the diagonal `t = Sᶜ`
(`wedgePairing_ιMulti_family_eq_zero_of_ne_compl`), so only the `Sᶜ` term survives. Geometrically
the complement of the coordinate `j`-subspace `span{e_i : i ∈ S}` is the complementary coordinate
`(N−j)`-subspace `span{e_i : i ∈ Sᶜ}` — the standard-frame instance of "the projective dual of a
decomposable is the decomposable of the orthogonal complement". -/
theorem complementIso_exteriorPower_basis_eq_smul_compl {j : ℕ} (hj : j ≤ k + 2)
    (S : Set.powersetCard (Fin (k + 2)) j) :
    complementIso hj ((Pi.basisFun K (Fin (k + 2))).exteriorPower j S)
      = (wedgePairing k hj ((Pi.basisFun K (Fin (k + 2))).exteriorPower j S)
          ((Pi.basisFun K (Fin (k + 2))).exteriorPower (k + 2 - j)
            (Set.powersetCard.compl (by rw [Fintype.card_fin]; omega) S))) •
        ((Pi.basisFun K (Fin (k + 2))).exteriorPower (k + 2 - j)
          (Set.powersetCard.compl (by rw [Fintype.card_fin]; omega) S)) := by
  set b := (Pi.basisFun K (Fin (k + 2))).exteriorPower (k + 2 - j) with hb
  have hcard : (k + 2 - j) + j = Fintype.card (Fin (k + 2)) := by rw [Fintype.card_fin]; omega
  -- Both sides agree in every `b`-coordinate: the `t`-coordinate of `complementIso hj e_S` is the
  -- wedge pairing `wedgePairing e_S e_t`, which vanishes off the diagonal `t = Sᶜ`.
  refine b.repr.injective (Finsupp.ext fun t => ?_)
  have hcoord : b.repr (complementIso hj ((Pi.basisFun K (Fin (k + 2))).exteriorPower j S)) t
      = wedgePairing k hj ((Pi.basisFun K (Fin (k + 2))).exteriorPower j S)
          ((Pi.basisFun K (Fin (k + 2))).exteriorPower (k + 2 - j) t) := by
    rw [hb, ← Module.Basis.coord_apply, complementIso, LinearEquiv.trans_apply,
      Module.Basis.coord_toDualEquiv_symm_apply, Module.Basis.coord_apply,
      Module.Basis.dualBasis_repr, LinearMap.linearEquivOfInjective_apply,
      exteriorPower.basis_apply, exteriorPower.basis_apply]
  rw [hcoord, map_smul, Finsupp.smul_apply, smul_eq_mul]
  by_cases ht : t = Set.powersetCard.compl hcard S
  · subst ht
    rw [hb, Module.Basis.repr_self, Finsupp.single_eq_same, mul_one]
  · have hsingle : (Finsupp.single (Set.powersetCard.compl hcard S) (1 : K)) t = 0 :=
      Finsupp.single_eq_of_ne ht
    rw [hb, Module.Basis.repr_self, hsingle, mul_zero,
      exteriorPower.basis_apply, exteriorPower.basis_apply,
      wedgePairing_ιMulti_family_eq_zero_of_ne_compl hj S t ht]

/-! ## The standard-frame range-membership of a `complementIso`'d coordinate blade
(`def:meet-complement-iso`)

The range-membership packaging of the base case `complementIso_exteriorPower_basis_eq_smul_compl`,
the standard-frame (coordinate-subspace) instance of the OD-8 panel-meet range-membership leaf
`complementIso_extensor_mem_range_map_subtype` (CHAIN-3, the `j = 2` form feeding CHAIN-4). The
general-decomposable lift (an arbitrary grade-2 `extensor n` with `W = {n₀, n₁}^⊥`) is the
remaining content of route (α). -/

/-- **The `complementIso` of a coordinate `2`-blade lands in `⋀^k W` for any `W` containing the
complementary coordinate vectors** (`def:meet-complement-iso`, CHAIN-3 — the standard-frame
range-membership packaging of `complementIso_exteriorPower_basis_eq_smul_compl`). For a coordinate
`2`-subset `S` of `Fin (k+2)` and any submodule `W ⊆ K^{k+2}` containing every complementary
standard basis vector `eₜ` (`t ∈ Sᶜ`), the `complementIso (j := 2)` image of the basis blade `e_S`
lies in the range of the inclusion `exteriorPower.map k W.subtype : ⋀^k W →ₗ ⋀^k K^{k+2}`. Immediate
from the base case (`complementIso e_S = (±1) • e_{Sᶜ}`): the complementary blade `e_{Sᶜ}` is the
`k`-extensor of the standard basis vectors indexed by `Sᶜ`, each in `W` by hypothesis, so it lies in
the range by `extensor_mem_range_map_subtype_of_mem_grade`, and a scalar multiple stays in the range
(a submodule is closed under `•`). This is the coordinate-subspace instance of the OD-8 panel-meet
range-membership; the general-`W = {n₀, n₁}^⊥` case (an arbitrary grade-2 decomposable) is the
remaining route-(α) content. -/
theorem complementIso_exteriorPower_basis_mem_range_map_subtype
    (S : Set.powersetCard (Fin (k + 2)) 2) (W : Submodule K (Fin (k + 2) → K))
    (hW : ∀ t ∈ (Set.powersetCard.compl (n := 2) (m := k) (by rw [Fintype.card_fin]) S :
        Finset (Fin (k + 2))), Pi.basisFun K (Fin (k + 2)) t ∈ W) :
    complementIso (k := k) (j := 2) (by omega)
        ((Pi.basisFun K (Fin (k + 2))).exteriorPower 2 S)
      ∈ LinearMap.range (exteriorPower.map k W.subtype) := by
  rw [complementIso_exteriorPower_basis_eq_smul_compl (by omega) S]
  refine Submodule.smul_mem _ _ ?_
  have hmem : ((Pi.basisFun K (Fin (k + 2))).exteriorPower (k + 2 - 2)
        (Set.powersetCard.compl (by rw [Fintype.card_fin]; omega) S) :
        ⋀[K]^(k + 2 - 2) (Fin (k + 2) → K))
      = ⟨extensor (Pi.basisFun K (Fin (k + 2)) ∘ Set.powersetCard.ofFinEmbEquiv.symm
          (Set.powersetCard.compl (by rw [Fintype.card_fin]; omega) S)),
          extensor_mem_exteriorPower _⟩ := by
    rw [exteriorPower.basis_apply]; rfl
  rw [hmem]
  refine extensor_mem_range_map_subtype_of_mem_grade (d := k + 1) W _ fun i => ?_
  exact hW _ ((Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem _ _).mp ⟨i, rfl⟩)

/-! ## General-field `toDual` facts (`def:meet-complement-iso`)

Field-general algebraic replacements for the `EuclideanSpace`/Gram–Schmidt metric transport
`MeetHodge.lean` used to reach the same facts (the TACTICS-QUIRKS § 59 quarantine, now retired):
the standard-basis `toDual` pairing is the bare dot product over *any* field, and the
`toDual`-perp of two independent vectors has the expected dimension by a `dualAnnihilator`
count — no inner product, no orthogonal complement, no orderedness, no characteristic hypothesis.
Feeds the GL-contragredient equivariance below, which replaces the O(n)-only route this file used
to need `MeetHodge.lean` for. -/

/-- The standard-basis `toDual` pairing on `Fin m → K` is the bilinear form `∑ i, w i * v i` —
purely algebraic, over any field. Replaces the `EuclideanSpace.inner_eq_basisFun_toDual` transport
`MeetHodge.lean` used to reach the same fact through the L² inner product. -/
theorem piBasisFun_toDual_eq_sum {m : ℕ} (w v : Fin m → K) :
    (Pi.basisFun K (Fin m)).toDual w v = ∑ i, w i * v i := by
  conv_lhs => rw [← (Pi.basisFun K (Fin m)).sum_repr v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_smul, Module.Basis.toDual_eq_repr, smul_eq_mul, Pi.basisFun_repr, mul_comm]

/-- Metric-free symmetry of the standard-basis `toDual` pairing, over any field (replaces the
`EuclideanSpace.inner_eq_basisFun_toDual` + `real_inner_comm` transport `MeetHodge.lean`'s
`hsymm` used). -/
theorem piBasisFun_toDual_symm {m : ℕ} (w v : Fin m → K) :
    (Pi.basisFun K (Fin m)).toDual w v = (Pi.basisFun K (Fin m)).toDual v w := by
  rw [piBasisFun_toDual_eq_sum, piBasisFun_toDual_eq_sum]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- **The `toDual`-perp of two independent normals in `K^{m+2}` has dimension `m`, over any
field** (`def:meet-complement-iso`; replaces `MeetHodge.lean`'s `EuclideanSpace`-transport reproof
of the same fact — the metric route TACTICS-QUIRKS § 59 quarantined). The perp is the
`toDualEquiv`-preimage of the dual annihilator of the span, so `finrank(perp) =
finrank(dualAnnihilator) = (m+2) − finrank(span) = (m+2) − 2 = m` by
`Subspace.finrank_add_finrank_dualAnnihilator_eq`. No inner product, no orthogonal complement, no
orderedness, no characteristic hypothesis. -/
theorem finrank_toDualPerp_pair_eq {m : ℕ} {n : Fin 2 → Fin (m + 2) → K}
    (hn : LinearIndependent K n) :
    Module.finrank K
        (⨅ j : Fin 2, LinearMap.ker ((Pi.basisFun K (Fin (m + 2))).toDual.flip (n j))
          : Submodule K (Fin (m + 2) → K)) = m := by
  classical
  set b := Pi.basisFun K (Fin (m + 2)) with hb
  set S : Submodule K (Fin (m + 2) → K) := Submodule.span K (Set.range n) with hS
  have hQ : (⨅ j : Fin 2, LinearMap.ker (b.toDual.flip (n j)))
      = Submodule.comap b.toDualEquiv.toLinearMap S.dualAnnihilator := by
    ext w
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply,
      Submodule.mem_comap, LinearEquiv.coe_coe, Module.Basis.toDualEquiv_apply,
      Submodule.mem_dualAnnihilator]
    constructor
    · intro h v hv
      have hle : S ≤ LinearMap.ker (b.toDual w) := by
        rw [hS, Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        simpa using h j
      simpa using hle hv
    · intro h j
      exact h (n j) (Submodule.subset_span ⟨j, rfl⟩)
  rw [hQ, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
  have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq S
  have h2 : Module.finrank K S = 2 := by
    rw [hS, finrank_span_eq_card hn, Fintype.card_fin]
  have h3 : Module.finrank K (Fin (m + 2) → K) = m + 2 := Module.finrank_fin_fun K
  omega

/-! ## The GL-contragredient equivariance of `complementIso` (`def:meet-complement-iso`)

Replaces the O(n)-only equivariance `complementIso_map_orthogonal_eq` this file used to state
(retired with `MeetHodge.lean`, along with its Gram-invariance half
`exteriorPower_basis_toDual_map_orthogonal_eq`): for a surjective frame map `g` and its
`toDual`-contragredient `h` (`⟨h x, g y⟩ = ⟨x, y⟩`, i.e. `h = (gᵀ)⁻¹` w.r.t. the standard pairing
`Pi.basisFun.toDual`), `complementIso` intertwines `map g` and `map h` up to `det g` — an *exact*
equation, not merely up-to-determinant, and with no orthogonality/isotropy hypothesis: the
contragredient of an invertible `g` exists over every field, for every `g`. This is what lets the
panel-meet range-membership below extend an independent normal pair by an *arbitrary* complement
(`Submodule.exists_isCompl`) rather than a Gram–Schmidt orthonormal one, removing the
`EuclideanSpace` dependency `MeetHodge.lean` needed (TACTICS-QUIRKS § 59). -/

/-- **Two-map Gram invariance** (replaces the O(n)-only
`exteriorPower_basis_toDual_map_orthogonal_eq`, whose `h = g = O` case this generalizes): if `h`,
`g` are `toDual`-dual to each other (`⟨h x, g y⟩ = ⟨x, y⟩` for all `x, y`), the induced
exterior-power pairing is invariant under transporting the two slots by `map n h` and `map n g`
respectively. -/
theorem exteriorPower_basis_toDual_map_dualPair_eq {d : ℕ} (n : ℕ)
    (g h : (Fin (d + 1) → K) →ₗ[K] (Fin (d + 1) → K))
    (hgh : ∀ x y, (Pi.basisFun K (Fin (d + 1))).toDual (h x) (g y)
      = (Pi.basisFun K (Fin (d + 1))).toDual x y)
    (Z B : ⋀[K]^n (Fin (d + 1) → K)) :
    ((Pi.basisFun K (Fin (d + 1))).exteriorPower n).toDual
        (exteriorPower.map n h Z) (exteriorPower.map n g B)
      = ((Pi.basisFun K (Fin (d + 1))).exteriorPower n).toDual Z B := by
  have hgen : ∀ v w : Fin n → (Fin (d + 1) → K),
      ((Pi.basisFun K (Fin (d + 1))).exteriorPower n).toDual
          (exteriorPower.map n h (exteriorPower.ιMulti K n v))
          (exteriorPower.map n g (exteriorPower.ιMulti K n w))
        = ((Pi.basisFun K (Fin (d + 1))).exteriorPower n).toDual
          (exteriorPower.ιMulti K n v) (exteriorPower.ιMulti K n w) := by
    intro v w
    simp only [exteriorPower.map_apply_ιMulti,
      exteriorPower_basis_toDual_eq_pairingDual_comp_map_grade, LinearMap.comp_apply,
      exteriorPower.pairingDual_ιMulti_ιMulti]
    congr 1
    ext i j
    simp only [Matrix.of_apply, Function.comp_apply, hgh]
  have key : ((((Pi.basisFun K (Fin (d + 1))).exteriorPower n).toDual.comp
        (exteriorPower.map n h)).flip.comp (exteriorPower.map n g))
      = ((Pi.basisFun K (Fin (d + 1))).exteriorPower n).toDual.flip := by
    refine LinearMap.ext_on (exteriorPower.ιMulti_span K n _) ?_
    rintro _ ⟨w, rfl⟩
    refine LinearMap.ext_on (exteriorPower.ιMulti_span K n _) ?_
    rintro _ ⟨v, rfl⟩
    simpa only [LinearMap.comp_apply, LinearMap.flip_apply] using hgen v w
  have := LinearMap.congr_fun (LinearMap.congr_fun key B) Z
  simpa only [LinearMap.comp_apply, LinearMap.flip_apply] using this

/-- **GL-contragredient equivariance of `complementIso`** (replaces
`complementIso_map_orthogonal_eq`): for a surjective `g` and any `h` `toDual`-dual to it,
`complementIso hj (map j g X) = (det g) • map (k+2−j) h (complementIso hj X)`. Proof mirrors the
retired O(n) lemma verbatim: pair against `B = map (k+2−j) g B'` (`g` surjective on the
finite-dimensional `Fin (k+2) → K`), use `wedgePairing_map` on the left and the two-map Gram
invariance above on the right. -/
theorem complementIso_map_contragredient_eq {j : ℕ} (hj : j ≤ k + 2)
    (g h : (Fin (k + 2) → K) →ₗ[K] (Fin (k + 2) → K))
    (hgsurj : Function.Surjective g)
    (hgh : ∀ x y, (Pi.basisFun K (Fin (k + 2))).toDual (h x) (g y)
      = (Pi.basisFun K (Fin (k + 2))).toDual x y)
    (X : ⋀[K]^j (Fin (k + 2) → K)) :
    complementIso hj (exteriorPower.map j g X)
      = (LinearMap.det g) • exteriorPower.map (k + 2 - j) h (complementIso hj X) := by
  have hmapsurj : Function.Surjective (exteriorPower.map (k + 2 - j) g) :=
    exteriorPower.map_surjective hgsurj
  apply ((Pi.basisFun K (Fin (k + 2))).exteriorPower (k + 2 - j)).toDual_injective
  refine LinearMap.ext fun B => ?_
  obtain ⟨B', rfl⟩ := hmapsurj B
  simp only [complementIso_toDual, wedgePairing_map, map_smul, LinearMap.smul_apply,
    exteriorPower_basis_toDual_map_dualPair_eq (k + 2 - j) g h hgh, smul_eq_mul]

/-- The `toDual`-contragredient of a linear automorphism `g`: the unique `h` with
`⟨h x, g y⟩ = ⟨x, y⟩` (in matrix terms, the inverse transpose). Exists for every invertible `g`
over every field — this is what replaces "extend the normal frame orthonormally"
(`exists_orthonormalBasis_span_pair_eq`, retired with `MeetHodge.lean`), and why no non-isotropy
hypothesis is needed below. -/
noncomputable def contragredient (g : (Fin (k + 2) → K) ≃ₗ[K] (Fin (k + 2) → K)) :
    (Fin (k + 2) → K) →ₗ[K] (Fin (k + 2) → K) :=
  (Pi.basisFun K (Fin (k + 2))).toDualEquiv.symm.toLinearMap ∘ₗ
    (g.symm : (Fin (k + 2) → K) →ₗ[K] (Fin (k + 2) → K)).dualMap ∘ₗ
    (Pi.basisFun K (Fin (k + 2))).toDualEquiv.toLinearMap

/-- The defining `toDual`-contragredient pairing: `⟨contragredient g x, g y⟩ = ⟨x, y⟩`. -/
theorem contragredient_toDual_pairing (g : (Fin (k + 2) → K) ≃ₗ[K] (Fin (k + 2) → K))
    (x y : Fin (k + 2) → K) :
    (Pi.basisFun K (Fin (k + 2))).toDual (contragredient g x) (g y)
      = (Pi.basisFun K (Fin (k + 2))).toDual x y := by
  have hd : (Pi.basisFun K (Fin (k + 2))).toDual (contragredient g x)
      = ((Pi.basisFun K (Fin (k + 2))).toDual x).comp
          (g.symm : (Fin (k + 2) → K) →ₗ[K] (Fin (k + 2) → K)) := by
    rw [← Module.Basis.toDualEquiv_apply, contragredient]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
      LinearMap.dualMap_apply', Module.Basis.toDualEquiv_apply]
  rw [hd]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

/-- **Basis extension with prescribed first two vectors** (replaces
`exists_orthonormalBasis_span_pair_eq`, retired with `MeetHodge.lean`): a linearly independent
pair extends to a linear automorphism `g` with `g e₀ = n 0`, `g e₁ = n 1`. Pure field linear
algebra — a complement of the span (`Submodule.exists_isCompl`) plus
`basisOfLinearIndependentOfCardEqFinrank` — with no Gram–Schmidt, no inner product. -/
theorem exists_linearEquiv_basisFun_pair (n : Fin 2 → Fin (k + 2) → K)
    (hn : LinearIndependent K n) :
    ∃ g : (Fin (k + 2) → K) ≃ₗ[K] (Fin (k + 2) → K),
      g (Pi.basisFun K (Fin (k + 2)) 0) = n 0 ∧
      g (Pi.basisFun K (Fin (k + 2)) 1) = n 1 := by
  classical
  set S : Submodule K (Fin (k + 2) → K) := Submodule.span K (Set.range n) with hS
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl S
  have hSdim : Module.finrank K S = 2 := by
    rw [hS, finrank_span_eq_card hn, Fintype.card_fin]
  have hCdim : Module.finrank K C = k := by
    have := Submodule.finrank_add_eq_of_isCompl hC
    rw [hSdim, Module.finrank_fin_fun] at this
    omega
  set c : Module.Basis (Fin k) K C := Module.finBasisOfFinrankEq K C hCdim with hc
  -- The summed family `Sum.elim n (coe ∘ c)` is linearly independent.
  set v : (Fin 2 ⊕ Fin k) → (Fin (k + 2) → K) := Sum.elim n (fun i => (c i : Fin (k + 2) → K))
    with hv
  have hvli : LinearIndependent K v := by
    rw [hv, linearIndependent_sum]
    refine ⟨by simpa using hn, ?_, ?_⟩
    · have := c.linearIndependent
      exact (this.map' C.subtype (Submodule.ker_subtype C)).comp _ (fun a b h => by simpa using h)
    · refine Disjoint.mono le_rfl ?_ hC.disjoint
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      simp only [Function.comp_apply, Sum.elim_inr]
      exact (c i).2
  -- Reindex `Fin 2 ⊕ Fin k ≃ Fin (k + 2)`, keeping `inl 0 ↦ 0`, `inl 1 ↦ 1`.
  set e : (Fin 2 ⊕ Fin k) ≃ Fin (k + 2) :=
    finSumFinEquiv.trans (finCongr (by omega)) with he
  set q : Fin (k + 2) → (Fin (k + 2) → K) := v ∘ e.symm with hq
  have hqli : LinearIndependent K q := hvli.comp e.symm e.symm.injective
  have hcard : Fintype.card (Fin (k + 2)) = Module.finrank K (Fin (k + 2) → K) := by
    rw [Fintype.card_fin, Module.finrank_fin_fun]
  set bq : Module.Basis (Fin (k + 2)) K (Fin (k + 2) → K) :=
    basisOfLinearIndependentOfCardEqFinrank hqli hcard with hbq
  refine ⟨(Pi.basisFun K (Fin (k + 2))).equiv bq (Equiv.refl _), ?_, ?_⟩
  · rw [Module.Basis.equiv_apply]
    have h0 : e.symm (0 : Fin (k + 2)) = Sum.inl 0 := by
      rw [Equiv.symm_apply_eq, he]
      simp [finSumFinEquiv, Fin.ext_iff]
    simp only [Equiv.refl_apply, hbq, coe_basisOfLinearIndependentOfCardEqFinrank, hq,
      Function.comp_apply, h0, hv, Sum.elim_inl]
  · rw [Module.Basis.equiv_apply]
    have h1 : e.symm (1 : Fin (k + 2)) = Sum.inl 1 := by
      rw [Equiv.symm_apply_eq, he]
      simp [finSumFinEquiv, Fin.ext_iff]
    simp only [Equiv.refl_apply, hbq, coe_basisOfLinearIndependentOfCardEqFinrank, hq,
      Function.comp_apply, h1, hv, Sum.elim_inl]

/-! ## The panel-meet range-membership and the point-join duality, metric-free
(`def:meet-complement-iso`, `lem:case-III-claim612-line-in-panel-union`)

The two leaves `MeetHodge.lean` used to carry via Gram–Schmidt and O(n)-equivariance, now reproved
metric-free: GL-frame extension (`exists_linearEquiv_basisFun_pair`) + contragredient equivariance
(`complementIso_map_contragredient_eq`) replace Gram–Schmidt + O(n)-equivariance, and the perp
dimension count is the field-general `finrank_toDualPerp_pair_eq` above. This removes the
`EuclideanSpace` dependency TACTICS-QUIRKS § 59 quarantined into a separate file. -/

/-- `exteriorPower.map 2 f` sends the grade-2 decomposable `extensor v` to the extensor of the
image family `fun i => f (v i)` (`map` acts on decomposables by mapping the factors). Extracted
from `complementIso_extensor_mem_range_map_subtype` below, where inlining it was the single largest
elaboration cost; as its own declaration the panel-meet proof stays within the default heartbeat
budget. -/
theorem exteriorPower_map_two_extensor
    (f : (Fin (k + 2) → K) →ₗ[K] (Fin (k + 2) → K)) (v : Fin 2 → Fin (k + 2) → K) :
    exteriorPower.map 2 f ⟨extensor v, extensor_mem_exteriorPower v⟩
      = ⟨extensor (fun i => f (v i)), extensor_mem_exteriorPower _⟩ := by
  have hv2 : (⟨extensor v, extensor_mem_exteriorPower v⟩ : ⋀[K]^2 (Fin (k + 2) → K))
      = exteriorPower.ιMulti K 2 v := by
    apply Subtype.ext; rw [exteriorPower.ιMulti_apply_coe]; rfl
  apply Subtype.ext
  rw [hv2, exteriorPower.map_apply_ιMulti, exteriorPower.ιMulti_apply_coe]
  rfl

/-- **The `complementIso` of an arbitrary grade-2 decomposable `extensor n` lands in `⋀^k W` for
`W` the `toDual`-orthogonal complement of `{n 0, n 1}`** (`def:meet-complement-iso`, the panel-meet
range-membership leaf). For two line-normals `n : Fin 2 → K^{k+2}` and a submodule `W ⊆ K^{k+2}`
that is `toDual`-orthogonal to both (`hWperp`) and of dimension `k` (`hWdim`, forcing `W =
{n 0, n 1}^⊥`), the `complementIso (j := 2)` image of the panel-meet `extensor n` lies in the
range of the inclusion `exteriorPower.map k W.subtype : ⋀^k W →ₗ ⋀^k K^{k+2}`.

Proved by an *arbitrary* (not orthonormal) GL frame `g` with `g e₀ = n 0`, `g e₁ = n 1`
(`exists_linearEquiv_basisFun_pair`) and its contragredient `h := contragredient g`: `h` sends the
coordinate complement of `{e₀, e₁}` into `W` (each generator's `toDual`-pairing against
`n 0`/`n 1` collapses to a Kronecker delta via `contragredient_toDual_pairing`), so the LANDED
standard-frame membership `complementIso_exteriorPower_basis_mem_range_map_subtype` transports
through `h` by the range push-forward `exteriorPower_map_mem_range_map_subtype_of_mapsTo`, and the
coordinate blade `map 2 g e_S` is *exactly* `extensor n` (no proportionality scalar needed —
hitting `n` on the nose is what the exact contragredient equation buys over the up-to-determinant
O(n) route). The dependent (`extensor n = 0`) case is trivial (`complementIso 0 = 0 ∈ range`).
Feeds the assembly `extensor_join_proportional_complementIso_meet` (the per-line join=meet
duality KT leaves implicit). -/
theorem complementIso_extensor_mem_range_map_subtype
    (n : Fin 2 → Fin (k + 2) → K)
    (W : Submodule K (Fin (k + 2) → K))
    (hWperp : ∀ w ∈ W, ∀ j, (Pi.basisFun K (Fin (k + 2))).toDual w (n j) = 0)
    (hWdim : Module.finrank K W = k) :
    complementIso (k := k) (j := 2) (by omega)
        ⟨extensor n, extensor_mem_exteriorPower n⟩
      ∈ LinearMap.range (exteriorPower.map k W.subtype) := by
  -- Dependent case: `extensor n = 0`, so `complementIso 0 = 0 ∈ range`.
  by_cases hn : LinearIndependent K n
  swap
  · have h0 : (⟨extensor n, extensor_mem_exteriorPower n⟩ : ⋀[K]^2 (Fin (k + 2) → K)) = 0 := by
      rw [Subtype.ext_iff]; exact extensor_eq_zero_of_not_linearIndependent hn
    rw [h0, map_zero]
    exact Submodule.zero_mem _
  classical
  -- The `toDual`-perp `Q` of `{n 0, n 1}`; `W = Q` by the metric-free dimension count.
  set Q : Submodule K (Fin (k + 2) → K) :=
    ⨅ j, LinearMap.ker ((Pi.basisFun K (Fin (k + 2))).toDual.flip (n j)) with hQ
  have hWQ : W ≤ Q := by
    intro w hw
    simp only [hQ, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply]
    exact hWperp w hw
  have hQdim : Module.finrank K Q = k := finrank_toDualPerp_pair_eq hn
  have hWQeq : W = Q := Submodule.eq_of_le_of_finrank_eq hWQ (by rw [hWdim, hQdim])
  -- The GL frame `g` with `g e₀ = n 0`, `g e₁ = n 1`, and its contragredient `h`.
  obtain ⟨g, hg0, hg1⟩ := exists_linearEquiv_basisFun_pair n hn
  set h : (Fin (k + 2) → K) →ₗ[K] (Fin (k + 2) → K) := contragredient g with hh
  have hgh : ∀ x y, (Pi.basisFun K (Fin (k + 2))).toDual (h x) (g y)
      = (Pi.basisFun K (Fin (k + 2))).toDual x y := contragredient_toDual_pairing g
  -- The coordinate `2`-subset `S = {0, 1}` and its enumerated frame vectors `vS`.
  set S : Set.powersetCard (Fin (k + 2)) 2 :=
    ⟨{0, 1}, by simp [Finset.card_insert_of_notMem, show (0 : Fin (k + 2)) ≠ 1 from by
      simp only [Ne, Fin.ext_iff, Fin.val_zero, Fin.val_one]; omega]⟩ with hS
  set vS : Fin 2 → Fin (k + 2) → K :=
    Pi.basisFun K (Fin (k + 2)) ∘ Set.powersetCard.ofFinEmbEquiv.symm S with hvS
  have heS : ((Pi.basisFun K (Fin (k + 2))).exteriorPower 2 S
      : ⋀[K]^2 (Fin (k + 2) → K))
      = ⟨extensor vS, extensor_mem_exteriorPower vS⟩ := by
    rw [exteriorPower.basis_apply]; rfl
  -- The enumeration `eS := ofFinEmbEquiv.symm S` of `S = {0, 1}` sends `0 ↦ 0`, `1 ↦ 1`.
  set eS := Set.powersetCard.ofFinEmbEquiv.symm S with heSdef
  have hmemS : ∀ j : Fin 2, eS j ∈ ({0, 1} : Finset (Fin (k + 2))) := by
    intro j
    have := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem S (eS j)).mp ⟨j, rfl⟩
    rwa [hS] at this
  have hmem01 : ∀ x : Fin (k + 2), x ∈ ({0, 1} : Finset (Fin (k + 2))) → x = 0 ∨ x = 1 := by
    intro x hx; simpa only [Finset.mem_insert, Finset.mem_singleton] using hx
  have he01 : eS 0 < eS 1 := eS.strictMono (by norm_num)
  have he0 : eS 0 = 0 := by
    rcases hmem01 _ (hmemS 0) with h | h
    · exact h
    · exfalso
      rcases hmem01 _ (hmemS 1) with h' | h'
      · rw [h, h'] at he01; exact absurd he01 (by norm_num)
      · rw [h, h'] at he01; exact absurd he01 (lt_irrefl _)
  have he1 : eS 1 = 1 := by
    rcases hmem01 _ (hmemS 1) with h | h
    · exfalso; rw [he0, h] at he01; exact absurd he01 (lt_irrefl _)
    · exact h
  -- `map 2 g (e_S) = ⟨extensor n, _⟩` exactly (no proportionality scalar needed).
  have hgvS : ∀ i, (g : (Fin (k + 2) → K) →ₗ[K] (Fin (k + 2) → K)) (vS i) = n i := by
    intro i
    fin_cases i
    · change g (vS 0) = n 0
      rw [show vS 0 = Pi.basisFun K (Fin (k + 2)) (eS 0) from rfl, he0]
      exact hg0
    · change g (vS 1) = n 1
      rw [show vS 1 = Pi.basisFun K (Fin (k + 2)) (eS 1) from rfl, he1]
      exact hg1
  have hmapeS : (exteriorPower.map 2 (g : (Fin (k + 2) → K) →ₗ[K] (Fin (k + 2) → K)))
      ((Pi.basisFun K (Fin (k + 2))).exteriorPower 2 S)
      = ⟨extensor n, extensor_mem_exteriorPower n⟩ := by
    rw [heS, exteriorPower_map_two_extensor]
    apply Subtype.ext
    change extensor (fun i => g (vS i)) = extensor n
    congr 1
    funext i
    exact hgvS i
  -- Every contragredient image `h e_t` (`t ∉ {0, 1}`) lies in `W = Q`.
  set complS := (Set.powersetCard.compl (n := 2) (m := k) (by rw [Fintype.card_fin]) S :
    Finset (Fin (k + 2))) with hcomplS
  have hhW : ∀ t ∈ complS, h (Pi.basisFun K (Fin (k + 2)) t) ∈ W := by
    intro t ht
    have htne : t ≠ 0 ∧ t ≠ 1 := by
      have hnotS : t ∉ (S : Finset (Fin (k + 2))) := Set.powersetCard.mem_compl.mp ht
      rw [hS] at hnotS
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnotS
      exact hnotS
    rw [hWQeq, hQ, Submodule.mem_iInf]
    intro j
    rw [LinearMap.mem_ker, LinearMap.flip_apply]
    have hnj : n j = g (Pi.basisFun K (Fin (k + 2)) (Fin.castLE (by omega) j)) := by
      fin_cases j
      · exact hg0.symm
      · exact hg1.symm
    rw [hnj, hgh, Module.Basis.toDual_apply]
    refine if_neg fun hcontra => ?_
    fin_cases j
    · exact htne.1 hcontra
    · exact htne.2 hcontra
  -- The coordinate-complement subspace `W₀`, with `h(W₀) ⊆ W`.
  set W₀ : Submodule K (Fin (k + 2) → K) :=
    Submodule.span K (↑(complS.image (Pi.basisFun K (Fin (k + 2)))) :
      Set (Fin (k + 2) → K)) with hW₀
  have hW₀mem : ∀ t ∈ complS, Pi.basisFun K (Fin (k + 2)) t ∈ W₀ :=
    fun t ht => Submodule.subset_span
      (by rw [Finset.coe_image]; exact ⟨t, ht, rfl⟩)
  have hhW₀ : ∀ w ∈ W₀, h w ∈ W := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
        simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
        obtain ⟨t, ht, rfl⟩ := hx
        exact hhW t ht
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a c _ _ ha hc => rw [map_add]; exact Submodule.add_mem _ ha hc
    | smul r a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha
  -- The standard-frame range-membership for the coordinate blade `e_S`.
  have hstd : complementIso (k := k) (j := 2) (by omega)
      ((Pi.basisFun K (Fin (k + 2))).exteriorPower 2 S)
      ∈ LinearMap.range (exteriorPower.map k W₀.subtype) :=
    complementIso_exteriorPower_basis_mem_range_map_subtype S W₀ hW₀mem
  -- Assemble: `complementIso (extensor n) = complementIso (map 2 g e_S)
  --   = det g • map k h (complementIso e_S)`, and the RHS is in the range.
  rw [← hmapeS, complementIso_map_contragredient_eq (by omega)
    (g : (Fin (k + 2) → K) →ₗ[K] (Fin (k + 2) → K)) h g.surjective hgh]
  refine Submodule.smul_mem _ _ ?_
  exact exteriorPower_map_mem_range_map_subtype_of_mapsTo h W₀ W hhW₀ hstd

/-- **The per-line point-join ↔ panel-meet duality at general `d`**
(`lem:case-III-claim612-line-in-panel-union`, the assembly closing the panel-meet ↔ point-join
duality). For the two normals `n : Fin 2 → K^{k+2}` cutting out a line `L` (homogeneous span
`dim k = d−1`) inside a panel and the `k = d−1` points `p : Fin k → K^{k+2}` spanning `L` (each
`toDual`-orthogonal to both normals, `hperp`), the panel-meet `complementIso (j := 2) ⟨extensor n,
_⟩` and the point-join `⟨extensor p, _⟩` are proportional in `⋀^k (Fin (k+2) → K)`:
`∃ c, c • (panel-meet) = (point-join)`.

This is the join=meet equality KT leave implicit reading eq. (6.45)/(6.66)/(6.67) — `C(Lᵢ)` is
written agnostically as both the *meet* of the 2 panels cutting out `Lᵢ` (the rank side) and the
*join* of the `d−1` points spanning `Lᵢ` (the `D`-span side); this lemma is the one step the Lean
must spell out. With `W = {n 0, n 1}^⊥` (`dim W = k`, the `toDual`-perp of the 2 independent
normals via `finrank_toDualPerp_pair_eq`), both the point-join (`p i ∈ W` from `hperp`,
`extensor_mem_range_map_subtype_of_mem_grade`) and the panel-meet
(`complementIso_extensor_mem_range_map_subtype` above) land in the line `range
(exteriorPower.map k W.subtype)` (`⋀^k W` is `1`-dimensional, by
`finrank_exteriorPower_self_eq_one`); the point-join is nonzero (`hp` +
`extensor_ne_zero_iff_linearIndependent`), so `exists_smul_eq_of_mem_range_map_subtype_grade`
yields the scalar. -/
theorem extensor_join_proportional_complementIso_meet
    (n : Fin 2 → Fin (k + 2) → K)
    (p : Fin k → Fin (k + 2) → K)
    (hp : LinearIndependent K p)
    (hpair : LinearIndependent K n)
    (hperp : ∀ i j, (Pi.basisFun K (Fin (k + 2))).toDual (p i) (n j) = 0) :
    ∃ c : K, c • (complementIso (k := k) (j := 2) (by omega)
        ⟨extensor n, extensor_mem_exteriorPower n⟩)
      = (⟨extensor p, extensor_mem_exteriorPower p⟩ : ⋀[K]^k (Fin (k + 2) → K)) := by
  classical
  -- `W = {n 0, n 1}^⊥`, the `toDual`-perp of the two normals.
  set W : Submodule K (Fin (k + 2) → K) :=
    ⨅ j, LinearMap.ker ((Pi.basisFun K (Fin (k + 2))).toDual.flip (n j)) with hW
  have hWmem : ∀ w, w ∈ W ↔ ∀ j, (Pi.basisFun K (Fin (k + 2))).toDual w (n j) = 0 := by
    intro w
    simp only [hW, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply]
  -- `hWperp` for the range-membership leaf is the membership characterization.
  have hWperp : ∀ w ∈ W, ∀ j, (Pi.basisFun K (Fin (k + 2))).toDual w (n j) = 0 :=
    fun w hw => (hWmem w).1 hw
  -- `finrank W = k`: the shared `toDual`-perp dimension count.
  have hWdim : Module.finrank K W = k := finrank_toDualPerp_pair_eq hpair
  -- Panel-meet membership.
  have hmeet : complementIso (k := k) (j := 2) (by omega)
      ⟨extensor n, extensor_mem_exteriorPower n⟩
      ∈ LinearMap.range (exteriorPower.map k W.subtype) :=
    complementIso_extensor_mem_range_map_subtype n W hWperp hWdim
  -- Point-join membership (`p i ∈ W` from `hperp`).
  have hjoin : (⟨extensor p, extensor_mem_exteriorPower p⟩ : ⋀[K]^k (Fin (k + 2) → K))
      ∈ LinearMap.range (exteriorPower.map k W.subtype) :=
    extensor_mem_range_map_subtype_of_mem_grade (d := k + 1) W p
      fun i => (hWmem (p i)).2 (hperp i)
  -- Point-join `≠ 0` (`hp`); panel-meet `≠ 0` (`complementIso` injective + `extensor n ≠ 0` from
  -- `hpair`), so the proportionality scalar is invertible.
  have hjoinne : (⟨extensor p, extensor_mem_exteriorPower p⟩ : ⋀[K]^k (Fin (k + 2) → K)) ≠ 0 := by
    rw [Ne, Subtype.ext_iff]; exact (extensor_ne_zero_iff_linearIndependent p).2 hp
  have hmeetne : complementIso (k := k) (j := 2) (by omega)
      ⟨extensor n, extensor_mem_exteriorPower n⟩ ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (complementIso (k := k) (j := 2) (by omega)).injective,
      Subtype.ext_iff]
    exact (extensor_ne_zero_iff_linearIndependent n).2 hpair
  -- Both members of the line `range (⋀^k W ↪)`; the point-join is nonzero, so it generates the
  -- line and the panel-meet is a multiple of it. Invert the (nonzero) scalar to orient the
  -- proportionality `(panel-meet) ↦ (point-join)` (the form the discriminator consumes).
  obtain ⟨c, hc⟩ :=
    exists_smul_eq_of_mem_range_map_subtype_grade (d := k + 1) W hWdim hjoin hjoinne hmeet
  have hcne : c ≠ 0 := by
    rintro rfl; rw [zero_smul] at hc; exact hmeetne hc.symm
  refine ⟨c⁻¹, ?_⟩
  rw [inv_smul_eq_iff₀ hcne]; exact hc.symm

end CombinatorialRigidity.Molecular
