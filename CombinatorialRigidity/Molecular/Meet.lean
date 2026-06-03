/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Mathlib.LinearAlgebra.ExteriorPower.Basis
public import CombinatorialRigidity.Mathlib.Data.Finset.Card
public import CombinatorialRigidity.Molecular.Extensor
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

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

/-! ## The graded wedge product `⋀ʲ V × ⋀^(N−j) V → ⋀ᴺ V`

The first ingredient of the perfect wedge pairing on which `complementIso`
(`def:meet-complement-iso`) and the regressive product `meet` (`def:meet`) are
built (route (ii); `notes/Phase21a.md`). It is the join (Phase 17, the symbolic
exterior product in the full `ExteriorAlgebra`) landed back in the *top* graded
piece `⋀^(k+2) V` via the graded-monoid structure `SetLike.GradedMonoid` on
`fun i ↦ ⋀^i V`: the product of a `j`-graded and an `(N−j)`-graded element is
`(j + (N−j)) = N`-graded. Composing with the volume form `screwAlgebraTopEquiv`
sends it into `ℝ`, the pairing whose nondegeneracy is the next deliverable. -/

variable {k}

/-- The graded wedge product `⋀ʲ V × ⋀^(N−j) V → ⋀ᴺ V` (`N = k+2`): the join /
exterior product of `A` and `B`, landed in the *top* graded piece via the graded
monoid structure on `fun i ↦ ⋀^i V`. The bilinear ingredient of the perfect wedge
pairing on which `complementIso` (`def:meet-complement-iso`) is built; on extensors
it agrees with the Phase-17 `join` (`coe_wedgeProd`). -/
noncomputable def wedgeProd {j : ℕ} (hj : j ≤ k + 2)
    (A : ⋀[ℝ]^j (Fin (k + 2) → ℝ)) (B : ⋀[ℝ]^(k + 2 - j) (Fin (k + 2) → ℝ)) :
    ⋀[ℝ]^(k + 2) (Fin (k + 2) → ℝ) := by
  refine ⟨(A : ExteriorAlgebra ℝ (Fin (k + 2) → ℝ)) * (B : ExteriorAlgebra ℝ (Fin (k + 2) → ℝ)), ?_⟩
  have h : j + (k + 2 - j) = k + 2 := by omega
  have := SetLike.mul_mem_graded A.2 B.2
  rwa [h] at this

/-- The underlying exterior-algebra element of `wedgeProd` is the join (Phase-17
`∨ₑ`, the full-algebra exterior product) of the two factors: `wedgeProd` is the
join landed in the top graded piece. The bridge from the meet's graded pairing to
the Phase-17 join API. -/
@[simp]
theorem coe_wedgeProd {j : ℕ} (hj : j ≤ k + 2)
    (A : ⋀[ℝ]^j (Fin (k + 2) → ℝ)) (B : ⋀[ℝ]^(k + 2 - j) (Fin (k + 2) → ℝ)) :
    (wedgeProd hj A B : ExteriorAlgebra ℝ (Fin (k + 2) → ℝ)) =
      (A : ExteriorAlgebra ℝ (Fin (k + 2) → ℝ)) ∨ₑ
        (B : ExteriorAlgebra ℝ (Fin (k + 2) → ℝ)) :=
  rfl

/-! ## The perfect wedge pairing `⋀ʲ V →ₗ Dual ℝ (⋀^(N−j) V)`

The bilinear ingredient (b) of the perfect wedge pairing on which `complementIso`
(`def:meet-complement-iso`) is built (route (ii); `notes/Phase21a.md`). The graded
wedge product `wedgeProd` is bilinear — its underlying element `↑A * ↑B` is bilinear
in the full algebra, and the subtype inclusion `⋀ᴺ V ↪ ExteriorAlgebra` is a linear
map, so `wedgeProd` inherits bilinearity (`wedgeProdBilin`). Composing the second
slot with the volume form `screwAlgebraTopEquiv : ⋀ᴺ V ≃ₗ ℝ` lands the pairing in
`ℝ`, giving `wedgePairing j : ⋀ʲ V →ₗ Dual ℝ (⋀^(N−j) V)`, `A ↦ B ↦
screwAlgebraTopEquiv (wedgeProd A B)`. Its nondegeneracy (the signed-permutation
basis computation) is the next ingredient; `complementIso` is then `wedgePairing`
as an equiv composed with `toDualEquiv.symm`. -/

/-- `wedgeProd` is additive in its first slot: the underlying product `↑A * ↑B` is
additive in `↑A` and the subtype inclusion `⋀ᴺ V ↪ ExteriorAlgebra` is linear. -/
theorem wedgeProd_add_left {j : ℕ} (hj : j ≤ k + 2)
    (A A' : ⋀[ℝ]^j (Fin (k + 2) → ℝ)) (B : ⋀[ℝ]^(k + 2 - j) (Fin (k + 2) → ℝ)) :
    wedgeProd hj (A + A') B = wedgeProd hj A B + wedgeProd hj A' B := by
  apply Subtype.ext
  simp [wedgeProd, add_mul]

/-- `wedgeProd` is additive in its second slot. -/
theorem wedgeProd_add_right {j : ℕ} (hj : j ≤ k + 2)
    (A : ⋀[ℝ]^j (Fin (k + 2) → ℝ)) (B B' : ⋀[ℝ]^(k + 2 - j) (Fin (k + 2) → ℝ)) :
    wedgeProd hj A (B + B') = wedgeProd hj A B + wedgeProd hj A B' := by
  apply Subtype.ext
  simp [wedgeProd, mul_add]

/-- `wedgeProd` is `ℝ`-homogeneous in its first slot. -/
theorem wedgeProd_smul_left {j : ℕ} (hj : j ≤ k + 2) (c : ℝ)
    (A : ⋀[ℝ]^j (Fin (k + 2) → ℝ)) (B : ⋀[ℝ]^(k + 2 - j) (Fin (k + 2) → ℝ)) :
    wedgeProd hj (c • A) B = c • wedgeProd hj A B := by
  apply Subtype.ext
  simp [wedgeProd]

/-- `wedgeProd` is `ℝ`-homogeneous in its second slot. -/
theorem wedgeProd_smul_right {j : ℕ} (hj : j ≤ k + 2) (c : ℝ)
    (A : ⋀[ℝ]^j (Fin (k + 2) → ℝ)) (B : ⋀[ℝ]^(k + 2 - j) (Fin (k + 2) → ℝ)) :
    wedgeProd hj A (c • B) = c • wedgeProd hj A B := by
  apply Subtype.ext
  simp [wedgeProd]

/-- The graded wedge product `⋀ʲ V × ⋀^(N−j) V → ⋀ᴺ V` packaged as an `ℝ`-bilinear
map. The `LinearMap.mk₂` bundling of `wedgeProd`, whose bilinearity is
`wedgeProd_{add,smul}_{left,right}`. -/
noncomputable def wedgeProdBilin {j : ℕ} (hj : j ≤ k + 2) :
    ⋀[ℝ]^j (Fin (k + 2) → ℝ) →ₗ[ℝ]
      ⋀[ℝ]^(k + 2 - j) (Fin (k + 2) → ℝ) →ₗ[ℝ] ⋀[ℝ]^(k + 2) (Fin (k + 2) → ℝ) :=
  LinearMap.mk₂ ℝ (wedgeProd hj) (wedgeProd_add_left hj) (wedgeProd_smul_left hj)
    (wedgeProd_add_right hj) (wedgeProd_smul_right hj)

@[simp]
theorem wedgeProdBilin_apply {j : ℕ} (hj : j ≤ k + 2)
    (A : ⋀[ℝ]^j (Fin (k + 2) → ℝ)) (B : ⋀[ℝ]^(k + 2 - j) (Fin (k + 2) → ℝ)) :
    wedgeProdBilin hj A B = wedgeProd hj A B :=
  rfl

/-- The perfect wedge pairing `⋀ʲ V →ₗ Module.Dual ℝ (⋀^(N−j) V)` (`N = k+2`):
`A ↦ B ↦ screwAlgebraTopEquiv (wedgeProd A B)`, the graded wedge product composed
with the top-power volume form `screwAlgebraTopEquiv : ⋀ᴺ V ≃ₗ ℝ`. The bilinear
pairing whose nondegeneracy makes `complementIso` (`def:meet-complement-iso`) an
isomorphism; `Module.Dual ℝ (⋀^(N−j) V) = (⋀^(N−j) V) →ₗ ℝ` is the second-slot
codomain after the volume form. -/
noncomputable def wedgePairing (k : ℕ) {j : ℕ} (hj : j ≤ k + 2) :
    ⋀[ℝ]^j (Fin (k + 2) → ℝ) →ₗ[ℝ]
      Module.Dual ℝ (⋀[ℝ]^(k + 2 - j) (Fin (k + 2) → ℝ)) :=
  (wedgeProdBilin hj).compr₂ (screwAlgebraTopEquiv k).toLinearMap

@[simp]
theorem wedgePairing_apply {j : ℕ} (hj : j ≤ k + 2)
    (A : ⋀[ℝ]^j (Fin (k + 2) → ℝ)) (B : ⋀[ℝ]^(k + 2 - j) (Fin (k + 2) → ℝ)) :
    wedgePairing k hj A B = screwAlgebraTopEquiv k (wedgeProd hj A B) :=
  rfl

/-! ## Nondegeneracy of the wedge pairing on the standard basis (ingredient (c))

The third ingredient of `complementIso` (`def:meet-complement-iso`): the perfect
wedge pairing `wedgePairing` is nondegenerate, computed on the standard
exterior-power basis. The basis of `⋀ʲ V` is indexed by the `j`-element subsets
`S : Set.powersetCard (Fin (k+2)) j`, with basis vector
`exteriorPower.ιMulti_family ℝ j (Pi.basisFun …) S` — the wedge `e_{S₀} ∧ ⋯` of the
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
    (wedgeProd hj (exteriorPower.ιMulti_family ℝ j (Pi.basisFun ℝ (Fin (k + 2))) S)
        (exteriorPower.ιMulti_family ℝ (k + 2 - j) (Pi.basisFun ℝ (Fin (k + 2))) T) :
        ExteriorAlgebra ℝ (Fin (k + 2) → ℝ)) =
      extensor (Fin.append
        (Pi.basisFun ℝ (Fin (k + 2)) ∘ Set.powersetCard.ofFinEmbEquiv.symm S)
        (Pi.basisFun ℝ (Fin (k + 2)) ∘ Set.powersetCard.ofFinEmbEquiv.symm T)) := by
  rw [coe_wedgeProd]
  change (extensor (Pi.basisFun ℝ (Fin (k + 2)) ∘ Set.powersetCard.ofFinEmbEquiv.symm S))
      ∨ₑ (extensor (Pi.basisFun ℝ (Fin (k + 2)) ∘ Set.powersetCard.ofFinEmbEquiv.symm T)) = _
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
    wedgePairing k hj (exteriorPower.ιMulti_family ℝ j (Pi.basisFun ℝ (Fin (k + 2))) S)
        (exteriorPower.ιMulti_family ℝ (k + 2 - j) (Pi.basisFun ℝ (Fin (k + 2))) T) = 0 := by
  rw [wedgePairing_apply]
  have hzero : wedgeProd hj
      (exteriorPower.ιMulti_family ℝ j (Pi.basisFun ℝ (Fin (k + 2))) S)
      (exteriorPower.ιMulti_family ℝ (k + 2 - j) (Pi.basisFun ℝ (Fin (k + 2))) T) = 0 := by
    apply Subtype.ext
    rw [coe_wedgeProd_ιMulti_family, ZeroMemClass.coe_zero]
    -- the append family repeats the standard basis vector `eₓ` for `x ∈ S ∩ T`
    obtain ⟨x, hxS, hxT⟩ := Finset.not_disjoint_iff.mp hST
    obtain ⟨a, ha⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem S x).mpr hxS
    obtain ⟨b, hb⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem T x).mpr hxT
    apply extensor_eq_zero_of_eq _
      (a := Fin.castAdd (k + 2 - j) a) (b := Fin.natAdd j b)
    · rw [Fin.append_left, Fin.append_right, Function.comp_apply, Function.comp_apply, ha, hb]
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
    wedgePairing k hj (exteriorPower.ιMulti_family ℝ j (Pi.basisFun ℝ (Fin (k + 2))) S)
        (exteriorPower.ιMulti_family ℝ (k + 2 - j) (Pi.basisFun ℝ (Fin (k + 2))) T) = 0 := by
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
    wedgePairing k hj (exteriorPower.ιMulti_family ℝ j (Pi.basisFun ℝ (Fin (k + 2))) S)
        (exteriorPower.ιMulti_family ℝ (k + 2 - j) (Pi.basisFun ℝ (Fin (k + 2)))
          (Set.powersetCard.compl (by rw [Fintype.card_fin]; omega) S)) ≠ 0 := by
  rw [wedgePairing_apply]
  have hne : wedgeProd hj
      (exteriorPower.ιMulti_family ℝ j (Pi.basisFun ℝ (Fin (k + 2))) S)
      (exteriorPower.ιMulti_family ℝ (k + 2 - j) (Pi.basisFun ℝ (Fin (k + 2)))
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
        Fin.append (⇑(Pi.basisFun ℝ (Fin (k + 2))) ∘ a)
          (⇑(Pi.basisFun ℝ (Fin (k + 2))) ∘ b) =
        ⇑(Pi.basisFun ℝ (Fin (k + 2))) ∘ Fin.append a b := by
      intro a b
      funext x
      refine Fin.addCases ?_ ?_ x <;> intro i <;> simp [Fin.append_left, Fin.append_right]
    rw [hrw]
    exact (Pi.basisFun ℝ (Fin (k + 2))).linearIndependent.comp _ hinj
  exact fun hz => hne ((map_eq_zero_iff _ (screwAlgebraTopEquiv k).injective).mp hz)

/-! ## The complement isomorphism `⋀ʲ V ≃ₗ ⋀^(N−j) V` (ingredient (d), `def:meet-complement-iso`)

The perfect wedge pairing `wedgePairing` is nondegenerate (ingredient (c): its matrix on
the standard exterior-power bases is a signed-permutation matrix — off-diagonal `0` by
`wedgePairing_ιMulti_family_eq_zero_of_ne_compl`, diagonal `≠ 0` by
`wedgePairing_ιMulti_family_compl_ne_zero`). Hence `wedgePairing k hj : ⋀ʲ V →ₗ
Module.Dual ℝ (⋀^(N−j) V)` is **injective**: evaluating `wedgePairing k hj m` at the
complementary basis vector `e_{Sᶜ}` of `⋀^(N−j) V` reads off the `S`-coordinate of `m`
up to the nonzero diagonal scalar, so a zero pairing forces every coordinate of `m` to
vanish. Domain and codomain have equal finrank (`(k+2).choose j` on both sides, since
`Module.Dual` preserves finrank and `(k+2).choose j = (k+2).choose (k+2−j)`), so
injectivity upgrades to a `LinearEquiv` via `LinearMap.linearEquivOfInjective`; one more
post-composition with the dual-evaluation iso of `⋀^(N−j) V` lands `complementIso` in
`⋀^(N−j) V` itself. -/

/-- **Injectivity of the wedge pairing** (ingredient (c) → (d)). The perfect wedge pairing
`wedgePairing k hj : ⋀ʲ V →ₗ Module.Dual ℝ (⋀^(N−j) V)` is injective: its matrix on the
standard exterior-power bases is a signed-permutation matrix (nonzero diagonal
`wedgePairing_ιMulti_family_compl_ne_zero`, vanishing off-diagonal
`wedgePairing_ιMulti_family_eq_zero_of_ne_compl`), so evaluating a zero pairing at each
complementary basis vector forces all standard-basis coordinates of the argument to
vanish. The nondegeneracy input to `complementIso` (`def:meet-complement-iso`). -/
theorem wedgePairing_injective {j : ℕ} (hj : j ≤ k + 2) :
    Function.Injective (wedgePairing k hj) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro m hm
  set bj := (Pi.basisFun ℝ (Fin (k + 2))).exteriorPower j with hbj
  apply bj.ext_elem_iff.mpr
  intro S
  -- read off the `S`-coordinate by evaluating the zero functional at `e_{Sᶜ}`
  set T : Set.powersetCard (Fin (k + 2)) (k + 2 - j) :=
    Set.powersetCard.compl (by rw [Fintype.card_fin]; omega) S with hT
  have hval : wedgePairing k hj m
      (exteriorPower.ιMulti_family ℝ (k + 2 - j) (Pi.basisFun ℝ (Fin (k + 2))) T) = 0 := by
    rw [hm]; rfl
  rw [← bj.sum_repr m, map_sum] at hval
  simp only [LinearMap.coe_sum, Finset.sum_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul, hbj, exteriorPower.basis_apply] at hval
  rw [Finset.sum_eq_single S] at hval
  · rw [map_zero, Finsupp.coe_zero, Pi.zero_apply]
    by_contra hne
    exact (wedgePairing_ιMulti_family_compl_ne_zero hj S)
      (by simpa [hT] using (mul_eq_zero.mp hval).resolve_left hne)
  · intro S' _ hS'
    have : T ≠ Set.powersetCard.compl (by rw [Fintype.card_fin]; omega) S' := by
      rw [hT]
      intro h
      exact hS' ((Set.powersetCard.compl _).injective h).symm
    rw [wedgePairing_ιMulti_family_eq_zero_of_ne_compl hj S' T this, mul_zero]
  · intro h; exact absurd (Finset.mem_univ S) h

/-- The finrank of `⋀ʲ (Fin (k+2) → ℝ)` equals the finrank of `Module.Dual ℝ (⋀^(k+2−j)
(Fin (k+2) → ℝ))`: both are `(k+2).choose j`. The dual preserves finrank, and the binomial
symmetry `(k+2).choose j = (k+2).choose (k+2−j)` (`Nat.choose_symm_diff`, valid for
`j ≤ k+2`) matches the two exterior powers. The dimension match feeding
`LinearMap.linearEquivOfInjective` in `complementIso`. -/
theorem finrank_exteriorPower_eq_finrank_dual {j : ℕ} (hj : j ≤ k + 2) :
    Module.finrank ℝ (⋀[ℝ]^j (Fin (k + 2) → ℝ)) =
      Module.finrank ℝ (Module.Dual ℝ (⋀[ℝ]^(k + 2 - j) (Fin (k + 2) → ℝ))) := by
  rw [Subspace.dual_finrank_eq, exteriorPower.finrank_eq, exteriorPower.finrank_eq,
    Module.finrank_fin_fun]
  exact (Nat.choose_symm hj).symm

/-- **The complement isomorphism** `⋀ʲ V ≃ₗ ⋀^(N−j) V` (`N = k+2`, `def:meet-complement-iso`):
the genuinely new core of the Grassmann–Cayley meet. Built from the nondegenerate perfect
wedge pairing `wedgePairing` (ingredient (c)): injectivity (`wedgePairing_injective`) plus
the equal finrank (`finrank_exteriorPower_eq_finrank_dual`) make `wedgePairing` a
`LinearEquiv` onto `Module.Dual ℝ (⋀^(N−j) V)` via `LinearMap.linearEquivOfInjective`, and
post-composing with the dual-evaluation iso `(b.exteriorPower (k+2−j)).toDualEquiv.symm`
lands the result in `⋀^(N−j) V`. The regressive product `meet` is the next deliverable
above this. -/
noncomputable def complementIso {j : ℕ} (hj : j ≤ k + 2) :
    ⋀[ℝ]^j (Fin (k + 2) → ℝ) ≃ₗ[ℝ] ⋀[ℝ]^(k + 2 - j) (Fin (k + 2) → ℝ) :=
  (LinearMap.linearEquivOfInjective (wedgePairing k hj) (wedgePairing_injective hj)
      (finrank_exteriorPower_eq_finrank_dual hj)) ≪≫ₗ
    ((Pi.basisFun ℝ (Fin (k + 2))).exteriorPower (k + 2 - j)).toDualEquiv.symm

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
    (A : ⋀[ℝ]^p (Fin (k + 2) → ℝ)) (B : ⋀[ℝ]^q (Fin (k + 2) → ℝ)) :
    ⋀[ℝ]^(p + q) (Fin (k + 2) → ℝ) :=
  ⟨(A : ExteriorAlgebra ℝ (Fin (k + 2) → ℝ)) * (B : ExteriorAlgebra ℝ (Fin (k + 2) → ℝ)),
    SetLike.mul_mem_graded A.2 B.2⟩

/-- The underlying exterior-algebra element of `gradedMul` is the Phase-17 join `∨ₑ`
of the two factors. The bridge from the meet's graded product to the join API. -/
@[simp]
theorem coe_gradedMul {p q : ℕ}
    (A : ⋀[ℝ]^p (Fin (k + 2) → ℝ)) (B : ⋀[ℝ]^q (Fin (k + 2) → ℝ)) :
    (gradedMul A B : ExteriorAlgebra ℝ (Fin (k + 2) → ℝ)) =
      (A : ExteriorAlgebra ℝ (Fin (k + 2) → ℝ)) ∨ₑ
        (B : ExteriorAlgebra ℝ (Fin (k + 2) → ℝ)) :=
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
    (A : ⋀[ℝ]^(k + 2 - a) (Fin (k + 2) → ℝ)) (B : ⋀[ℝ]^(k + 2 - b) (Fin (k + 2) → ℝ)) :
    ⋀[ℝ]^(k + 2 - (a + b)) (Fin (k + 2) → ℝ) := by
  -- `complementIso A : ⋀^a`, `complementIso B : ⋀^b`, product in `⋀^(a+b)`.
  have hA : k + 2 - (k + 2 - a) = a := by omega
  have hB : k + 2 - (k + 2 - b) = b := by omega
  refine complementIso (j := a + b) hab
    (gradedMul (hA ▸ complementIso (k := k) (j := k + 2 - a) (by omega) A)
      (hB ▸ complementIso (k := k) (j := k + 2 - b) (by omega) B))

@[inherit_doc] scoped infixl:70 " ∧ₑ " => meet

end CombinatorialRigidity.Molecular
