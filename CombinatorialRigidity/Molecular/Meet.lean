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
# The complement isomorphism and the meet (`sec:molecular-meet`)

The definitions and lemmas of `sec:molecular-meet`. The meet is the operation of the
Grassmann–Cayley algebra dual to the join (Barnabei, Brini and Rota 1985; White 1994), whom Katoh
and Tanigawa cite for the algebra (2011, *A proof of the molecular conjecture*, Discrete Comput.
Geom. **45**, §2.1); they use the join and not the meet. Here `V = K^(k+2)` and `N = k + 2`, so that
`d = k + 1`, over any field `K`: the constructions use the standard basis of `V`, and no order on
`K` or hypothesis on its characteristic. The file proves:

* the volume form `⋀^N V ≃ K` and the duality `⋀^j V* ≃ (⋀^j V)*` (`def:meet-top-equiv`,
  `def:meet-pairing-dual`), the cases of `exteriorPower.topEquiv` and
  `exteriorPower.pairingDualEquiv` at `V`;
* the wedge pairing `(X, Y) ↦ vol (X ∨ Y)` of `⋀^j V` and `⋀^(N−j) V`, which is nondegenerate, the
  complement isomorphism `*` that it gives, and its defining property (`def:meet-complement-iso`,
  `lem:complement-iso-toDual`); the meet `A ∧ B = *(*A ∨ *B)` (`def:meet`); the formula
  `*e_S = ε_S • e_{Sᶜ}` and the transformation law of `*` under a linear automorphism of `V`; and
  the meet of two hyperplanes, an extensor of their intersection and a multiple of the join of
  `d − 1` linearly independent vectors in it (`lem:meet-two-hyperplanes`);
* for `d = 3`, that the meet of two planes is a multiple of the join of two points of their line
  (`lem:complement-iso-decomposable-wedge-perp`, `lem:case-III-claim612-line-in-panel-union`), the
  facts on `⋀² W` for a plane `W` that identify the line of `⋀² K⁴` on which both lie
  (`lem:complement-iso-line-one-dim`, `lem:complement-iso-exterior-map-injective`), and that equal
  nonzero `2`-extensors span the same plane (`lem:decomposable-extensor-span-unique`);
* the coordinate pairing of `V` as the dot product, and the dimension of the space of vectors
  orthogonal to a family, which `Molecule/Pencil/` uses as well.

`rem:meet-kt-steps` says which of these the formal proof of KT Theorem 5.5 uses.
-/

@[expose] public section

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] (k : ℕ)

/-- **The volume form** (`def:meet-top-equiv`): the linear isomorphism `vol : ⋀^(k+2) V ≃ K` that
sends the join of the standard basis vectors to `1`, the case `n = k + 2` of
`exteriorPower.topEquiv`. It takes `v₁ ∨ ⋯ ∨ v_(k+2)` to the determinant of the matrix with these
rows. -/
noncomputable def screwAlgebraTopEquiv :
    ⋀[K]^(k + 2) (Fin (k + 2) → K) ≃ₗ[K] K :=
  exteriorPower.topEquiv (k + 2)

/-- **The volume form scales by the determinant** (a step of `lem:meet-two-hyperplanes`): for a
linear map `f` of `V`, `vol (map (k+2) f X) = det f • vol X`, the case `n = k + 2` of
`exteriorPower.topEquiv_map_eq_det_smul`. With `wedgeProd_map` it gives `wedgePairing_map`, and so
the factor `det g` of the transformation law of `*` (`complementIso_map_contragredient_eq`). -/
theorem screwAlgebraTopEquiv_map_eq_det_smul (f : (Fin (k + 2) → K) →ₗ[K] (Fin (k + 2) → K))
    (X : ⋀[K]^(k + 2) (Fin (k + 2) → K)) :
    screwAlgebraTopEquiv k (exteriorPower.map (k + 2) f X)
      = (LinearMap.det f) • screwAlgebraTopEquiv k X :=
  exteriorPower.topEquiv_map_eq_det_smul (k + 2) f X

/-- **The duality of exterior powers** (`def:meet-pairing-dual`): the linear isomorphism
`⋀^j V* ≃ (⋀^j V)*` that sends `φ₁ ∨ ⋯ ∨ φ_j` to the form `v₁ ∨ ⋯ ∨ v_j ↦ det (φ_a (v_b))`, the case
of `exteriorPower.pairingDualEquiv` at the standard basis of `V`. Its underlying map is mathlib's
`exteriorPower.pairingDual` (`exteriorPower.coe_pairingDualEquiv`). The formal proof uses that map
and its determinant formula (`exteriorPower_basis_toDual_eq_pairingDual_comp_map_grade`), not this
isomorphism (`rem:meet-kt-steps`). -/
noncomputable def screwAlgebraPairingDualEquiv (j : ℕ) :
    ⋀[K]^j (Module.Dual K (Fin (k + 2) → K)) ≃ₗ[K]
      Module.Dual K (⋀[K]^j (Fin (k + 2) → K)) :=
  exteriorPower.pairingDualEquiv (Pi.basisFun K (Fin (k + 2))) j

/-! ## The join into the top exterior power (`def:meet-complement-iso`)

For `j ≤ N`, the join of an element of `⋀^j V` and one of `⋀^(N−j) V` lies in `⋀^N V`, as the
degrees of the exterior algebra add (`wedgeProd`). Followed by the volume form, it gives the wedge
pairing from which `def:meet-complement-iso` builds `*`. -/

variable {k}

/-- **The join into the top exterior power** (for `def:meet-complement-iso`): for `j ≤ k + 2`,
`A : ⋀^j V` and `B : ⋀^(k+2−j) V`, the product `A ∨ B` of the exterior algebra, as an element of
`⋀^(k+2) V` (`SetLike.mul_mem_graded`). Its value in the exterior algebra is the join
(`coe_wedgeProd`). -/
noncomputable def wedgeProd {j : ℕ} (hj : j ≤ k + 2)
    (A : ⋀[K]^j (Fin (k + 2) → K)) (B : ⋀[K]^(k + 2 - j) (Fin (k + 2) → K)) :
    ⋀[K]^(k + 2) (Fin (k + 2) → K) := by
  refine ⟨(A : ExteriorAlgebra K (Fin (k + 2) → K)) * (B : ExteriorAlgebra K (Fin (k + 2) → K)), ?_⟩
  have h : j + (k + 2 - j) = k + 2 := by omega
  have := SetLike.mul_mem_graded A.2 B.2
  rwa [h] at this

/-- **`wedgeProd` is the join** (`def:join`): its value in the exterior algebra is `A ∨ₑ B`, by
`rfl`. -/
@[simp]
theorem coe_wedgeProd {j : ℕ} (hj : j ≤ k + 2)
    (A : ⋀[K]^j (Fin (k + 2) → K)) (B : ⋀[K]^(k + 2 - j) (Fin (k + 2) → K)) :
    (wedgeProd hj A B : ExteriorAlgebra K (Fin (k + 2) → K)) =
      (A : ExteriorAlgebra K (Fin (k + 2) → K)) ∨ₑ
        (B : ExteriorAlgebra K (Fin (k + 2) → K)) :=
  rfl

/-! ## The wedge pairing (`def:meet-complement-iso`)

`wedgeProd` is bilinear (`wedgeProdBilin`). Followed by the volume form, it gives the wedge pairing
`wedgePairing : ⋀^j V → (⋀^(N−j) V)*`, `X ↦ (Y ↦ vol (X ∨ Y))`, which scales by the determinant
under the maps induced by a linear map of `V` (`wedgePairing_map`). -/

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

/-- **`wedgeProd` as a bilinear map** (`LinearMap.mk₂`), by `wedgeProd_add_left`,
`wedgeProd_add_right`, `wedgeProd_smul_left` and `wedgeProd_smul_right`. -/
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

/-- **The wedge pairing** (for `def:meet-complement-iso`): `X ↦ (Y ↦ vol (X ∨ Y))`, a linear map
from `⋀^j V` to the linear forms on `⋀^(N−j) V`, `N = k + 2`: `wedgeProd` followed by the volume
form `screwAlgebraTopEquiv`. It is injective (`wedgePairing_injective`), and `complementIso` is
built from it. -/
noncomputable def wedgePairing (k : ℕ) {j : ℕ} (hj : j ≤ k + 2) :
    ⋀[K]^j (Fin (k + 2) → K) →ₗ[K]
      Module.Dual K (⋀[K]^(k + 2 - j) (Fin (k + 2) → K)) :=
  (wedgeProdBilin hj).compr₂ (screwAlgebraTopEquiv k).toLinearMap

@[simp]
theorem wedgePairing_apply {j : ℕ} (hj : j ≤ k + 2)
    (A : ⋀[K]^j (Fin (k + 2) → K)) (B : ⋀[K]^(k + 2 - j) (Fin (k + 2) → K)) :
    wedgePairing k hj A B = screwAlgebraTopEquiv k (wedgeProd hj A B) :=
  rfl

/-- **The join into the top power commutes with the maps induced by a linear map** (a step of
`lem:meet-two-hyperplanes`): for a linear map `f` of `V`,
`wedgeProd (map j f A) (map (N−j) f B) = map N f (wedgeProd A B)`, as `ExteriorAlgebra.map f` is
multiplicative and agrees with `exteriorPower.map` on each degree
(`exteriorPower.map_coe_eq_exteriorAlgebra_map`). -/
theorem wedgeProd_map {j : ℕ} (hj : j ≤ k + 2)
    (f : (Fin (k + 2) → K) →ₗ[K] (Fin (k + 2) → K))
    (A : ⋀[K]^j (Fin (k + 2) → K)) (B : ⋀[K]^(k + 2 - j) (Fin (k + 2) → K)) :
    wedgeProd hj (exteriorPower.map j f A) (exteriorPower.map (k + 2 - j) f B)
      = exteriorPower.map (k + 2) f (wedgeProd hj A B) := by
  apply Subtype.ext
  rw [coe_wedgeProd, join_def, exteriorPower.map_coe_eq_exteriorAlgebra_map,
    exteriorPower.map_coe_eq_exteriorAlgebra_map, ← map_mul,
    exteriorPower.map_coe_eq_exteriorAlgebra_map, coe_wedgeProd, join_def]

/-- **The wedge pairing scales by the determinant** (a step of `lem:meet-two-hyperplanes`): for a
linear map `f` of `V`, `wedgePairing (map j f A) (map (N−j) f B) = det f • wedgePairing A B`, by
`wedgeProd_map` and `screwAlgebraTopEquiv_map_eq_det_smul`. It gives the factor `det g` of the
transformation law of `*` (`complementIso_map_contragredient_eq`). -/
theorem wedgePairing_map {j : ℕ} (hj : j ≤ k + 2)
    (f : (Fin (k + 2) → K) →ₗ[K] (Fin (k + 2) → K))
    (A : ⋀[K]^j (Fin (k + 2) → K)) (B : ⋀[K]^(k + 2 - j) (Fin (k + 2) → K)) :
    wedgePairing k hj (exteriorPower.map j f A) (exteriorPower.map (k + 2 - j) f B)
      = (LinearMap.det f) • wedgePairing k hj A B := by
  simp only [wedgePairing_apply, wedgeProd_map, screwAlgebraTopEquiv_map_eq_det_smul,
    smul_eq_mul]

/-! ## The wedge pairing on the standard bases (`def:meet-complement-iso`)

For a `j`-element set `S` of indices, let `e_S` be the join of the standard basis vectors `e_s`,
`s ∈ S`, in increasing order (`exteriorPower.ιMulti_family`); these form the standard basis of
`⋀^j V`. The join of `e_S` and an `e_T` of `⋀^(N−j) V` is the extensor of the family that lists the
`e_s` and then the `e_t` (`coe_wedgeProd_ιMulti_family`). If `S` and `T` meet, the family repeats a
vector, and the pairing is `0`. As `|S| + |T| = N`, the sets are disjoint exactly when `T = Sᶜ`, and
then the pairing `ε_S` is not `0`; it is `±1`, which the proofs do not need. So the matrix of the
pairing in these bases has one nonzero entry in each row and each column. -/

/-- **The join of two standard basis elements is an extensor** (for `def:meet-complement-iso`): the
value of `wedgeProd e_S e_T` in the exterior algebra is the extensor of `Fin.append` of the two
increasing families of standard basis vectors (`join_extensor`). -/
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

/-- **The wedge pairing of `e_S` and `e_T` vanishes when `S` and `T` meet** (for
`def:meet-complement-iso`): an index `x ∈ S ∩ T` puts `e_x` twice in the family of
`coe_wedgeProd_ιMulti_family`, so its extensor is `0` (`extensor_eq_zero_of_eq`). The case `T = Sᶜ`
is `wedgePairing_ιMulti_family_compl_ne_zero`. -/
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

/-- **The wedge pairing of `e_S` and `e_T` vanishes unless `T = Sᶜ`** (for
`def:meet-complement-iso`): `S` and `T` have `j` and `N − j` elements, so they are disjoint only
when `T` is the complement of `S` (`Finset.disjoint_iff_eq_compl`, `Set.powersetCard.compl`);
otherwise `wedgePairing_ιMulti_family_eq_zero_of_not_disjoint` applies. -/
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

/-- **The wedge pairing of `e_S` and `e_{Sᶜ}` is not zero** (for `def:meet-complement-iso`): the
family of `coe_wedgeProd_ιMulti_family` is the standard basis composed with `Fin.append` of the
increasing enumerations of `S` and `Sᶜ`, which is injective, so the family is linearly independent
and its extensor is not zero (`extensor_ne_zero_iff_linearIndependent`); the volume form is
injective. The value is `±1`, the sign of the permutation that lists `S` and then `Sᶜ`, which the
proofs do not need. With `wedgePairing_ιMulti_family_eq_zero_of_ne_compl`, the matrix of the pairing
in the standard bases has one nonzero entry in each row and each column. -/
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

/-! ## The complement isomorphism (`def:meet-complement-iso`, `lem:complement-iso-toDual`)

The wedge pairing is injective: the value of `wedgePairing X` at `e_{Sᶜ}` is the coordinate of `X`
at `e_S` times the nonzero `ε_S`. The two sides have dimension `(k+2 choose j)`, so it is an
isomorphism onto `(⋀^(N−j) V)*` (`LinearMap.linearEquivOfInjective`), and `complementIso` follows it
with the inverse of the coordinate identification of `⋀^(N−j) V` with its dual. -/

/-- **The wedge pairing is injective** (for `def:meet-complement-iso`): if `wedgePairing X = 0`, its
value at `e_{Sᶜ}` is the coordinate of `X` at `e_S` times the nonzero pairing of `e_S` and `e_{Sᶜ}`
(`wedgePairing_ιMulti_family_compl_ne_zero`), as the other terms vanish
(`wedgePairing_ιMulti_family_eq_zero_of_ne_compl`); so every coordinate of `X` is `0`. -/
theorem wedgePairing_injective {j : ℕ} (hj : j ≤ k + 2) :
    Function.Injective (wedgePairing (K := K) k hj) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro m hm
  set bj := (Pi.basisFun K (Fin (k + 2))).exteriorPower j with hbj
  apply bj.ext_elem_iff.mpr
  intro S
  -- Read off the coordinate at `e_S` by evaluating the zero form at `e_{Sᶜ}`.
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

/-- **`⋀^j V` and the linear forms on `⋀^(N−j) V` have the same dimension** (for
`def:meet-complement-iso`): both are `(k+2 choose j)`, as a finite-dimensional space and its dual
have the same dimension and `(k+2 choose j) = (k+2 choose (k+2−j))` for `j ≤ k + 2`
(`Nat.choose_symm`). -/
theorem finrank_exteriorPower_eq_finrank_dual {j : ℕ} (hj : j ≤ k + 2) :
    Module.finrank K (⋀[K]^j (Fin (k + 2) → K)) =
      Module.finrank K (Module.Dual K (⋀[K]^(k + 2 - j) (Fin (k + 2) → K))) := by
  rw [Subspace.dual_finrank_eq, exteriorPower.finrank_eq, exteriorPower.finrank_eq,
    Module.finrank_fin_fun]
  exact (Nat.choose_symm hj).symm

/-- **The complement isomorphism** `* : ⋀^j V ≃ ⋀^(N−j) V`, `N = k + 2` (`def:meet-complement-iso`):
the wedge pairing, an isomorphism onto the linear forms on `⋀^(N−j) V` (`wedgePairing_injective`,
`finrank_exteriorPower_eq_finrank_dual`, `LinearMap.linearEquivOfInjective`), followed by the
inverse of the coordinate identification `Z ↦ ⟨Z, ·⟩` of `⋀^(N−j) V` with its dual, for the standard
basis (`Module.Basis.toDualEquiv`). On the standard bases, `*e_S = ε_S • e_{Sᶜ}`
(`complementIso_exteriorPower_basis_eq_smul_compl`), so `*` is the Hodge star operator of the
standard basis. -/
noncomputable def complementIso {j : ℕ} (hj : j ≤ k + 2) :
    ⋀[K]^j (Fin (k + 2) → K) ≃ₗ[K] ⋀[K]^(k + 2 - j) (Fin (k + 2) → K) :=
  (LinearMap.linearEquivOfInjective (wedgePairing k hj) (wedgePairing_injective hj)
      (finrank_exteriorPower_eq_finrank_dual hj)) ≪≫ₗ
    ((Pi.basisFun K (Fin (k + 2))).exteriorPower (k + 2 - j)).toDualEquiv.symm

/-- **The defining property of `*`** (`lem:complement-iso-toDual`): `⟨*X, B⟩ = vol (X ∨ B)` for
`X : ⋀^j V` and `B : ⋀^(N−j) V`, where `⟨·, ·⟩` is the coordinate pairing of the standard basis,
`(b.exteriorPower (N−j)).toDual`. By construction, the coordinate identification undoes the second
factor of `complementIso` and leaves `wedgePairing X`. -/
theorem complementIso_toDual {j : ℕ} (hj : j ≤ k + 2)
    (X : ⋀[K]^j (Fin (k + 2) → K)) (B : ⋀[K]^(k + 2 - j) (Fin (k + 2) → K)) :
    ((Pi.basisFun K (Fin (k + 2))).exteriorPower (k + 2 - j)).toDual (complementIso hj X) B
      = wedgePairing k hj X B := by
  rw [complementIso, LinearEquiv.trans_apply, ← Module.Basis.toDualEquiv_apply,
    LinearEquiv.apply_symm_apply, LinearMap.linearEquivOfInjective_apply]

/-! ## The meet (`def:meet`)

For `A : ⋀^(N−a) V` and `B : ⋀^(N−b) V` with `a + b ≤ N`, the meet is `A ∧ B = *(*A ∨ *B)`: `*A` and
`*B` lie in `⋀^a V` and `⋀^b V`, their join in `⋀^(a+b) V` (`gradedMul`), and `*` takes it to
`⋀^(N−(a+b)) V`. For nonzero extensors of subspaces whose sum is `V`, the meet is a nonzero extensor
of their intersection (the passage after `def:meet`, not formalized). The formal proof uses
`*(n_A ∨ n_B)` for the normals of two hyperplanes, not the meet itself (`lem:meet-two-hyperplanes`).
-/

/-- **The join of `⋀^p V` and `⋀^q V` into `⋀^(p+q) V`** (for `def:meet`): the product `A ∨ B` of
the exterior algebra, as an element of `⋀^(p+q) V`. `wedgeProd` is the same product for `q = N − p`.
-/
noncomputable def gradedMul {p q : ℕ}
    (A : ⋀[K]^p (Fin (k + 2) → K)) (B : ⋀[K]^q (Fin (k + 2) → K)) :
    ⋀[K]^(p + q) (Fin (k + 2) → K) :=
  ⟨(A : ExteriorAlgebra K (Fin (k + 2) → K)) * (B : ExteriorAlgebra K (Fin (k + 2) → K)),
    SetLike.mul_mem_graded A.2 B.2⟩

/-- **`gradedMul` is the join** (`def:join`): its value in the exterior algebra is `A ∨ₑ B`, by
`rfl`. -/
@[simp]
theorem coe_gradedMul {p q : ℕ}
    (A : ⋀[K]^p (Fin (k + 2) → K)) (B : ⋀[K]^q (Fin (k + 2) → K)) :
    (gradedMul A B : ExteriorAlgebra K (Fin (k + 2) → K)) =
      (A : ExteriorAlgebra K (Fin (k + 2) → K)) ∨ₑ
        (B : ExteriorAlgebra K (Fin (k + 2) → K)) :=
  rfl

/-- **The meet** (`def:meet`): for `a + b ≤ N`, `A : ⋀^(N−a) V` and `B : ⋀^(N−b) V`,
`A ∧ₑ B = *(*A ∨ *B) : ⋀^(N−(a+b)) V`, where `*A : ⋀^a V` and `*B : ⋀^b V` (the degrees cast by
`N − (N − a) = a`) and their join is `gradedMul`. Nothing in the project uses `meet`: the formal
proof forms `*(n_A ∨ n_B)` directly (`rem:meet-kt-steps`). -/
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

/-! ## The complement of a `2`-extensor and the `2`-extensors that share a vector with it
(`lem:complement-iso-decomposable-wedge-perp`)

If `X ∨ B = 0`, then `⟨*X, B⟩ = vol (X ∨ B) = 0`, and two `2`-extensors that share a vector have the
join `0`. So `*(n₁ ∨ n₂)` is orthogonal, for the coordinate pairing, to every `2`-extensor `n₁ ∨ c`.
-/

/-- **If `X ∨ B = 0`, then `⟨*X, B⟩ = 0`** (`lem:complement-iso-decomposable-wedge-perp`, part (1)):
by `complementIso_toDual`, `⟨*X, B⟩ = vol (X ∨ B) = vol 0 = 0`. -/
theorem complementIso_toDual_eq_zero_of_wedgeProd_eq_zero {j : ℕ} (hj : j ≤ k + 2)
    (X : ⋀[K]^j (Fin (k + 2) → K)) (B : ⋀[K]^(k + 2 - j) (Fin (k + 2) → K))
    (hwedge : wedgeProd hj X B = 0) :
    ((Pi.basisFun K (Fin (k + 2))).exteriorPower (k + 2 - j)).toDual
        (complementIso hj X) B = 0 := by
  simp only [complementIso_toDual, wedgePairing_apply, hwedge, map_zero]

/-- **Two `2`-extensors of `K⁴` that share a vector have the join `0`**
(`lem:complement-iso-decomposable-wedge-perp`, part (2)): if `n 0 = c 0`, then
`wedgeProd (extensor n) (extensor c) = 0`, as `extensor n ∨ extensor c` is the extensor of
`Fin.append n c` (`join_extensor`), which repeats `n 0` (`extensor_eq_zero_of_eq`). -/
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

/-- **`*(n₁ ∨ n₂)` is orthogonal to the `2`-extensors `n₁ ∨ c`**
(`lem:complement-iso-decomposable-wedge-perp`, part (2)): for `n c : Fin 2 → K⁴` with `n 0 = c 0`,
`⟨*(extensor n), extensor c⟩ = 0`, by `complementIso_toDual_eq_zero_of_wedgeProd_eq_zero` and
`wedgeProd_extensor_eq_zero_of_shared_vector`. The proof of `complementIso_smul_eq_extensor_join`
obtains the case of a shared `n 1` from the first of these. -/
theorem complementIso_toDual_extensor_eq_zero_of_shared_vector
    (n c : Fin 2 → Fin 4 → K) (hshare : n 0 = c 0) :
    ((Pi.basisFun K (Fin (2 + 2))).exteriorPower (2 + 2 - 2)).toDual
        (complementIso (k := 2) (j := 2) (by omega) ⟨extensor n, extensor_mem_exteriorPower n⟩)
        ⟨extensor c, extensor_mem_exteriorPower c⟩ = 0 :=
  complementIso_toDual_eq_zero_of_wedgeProd_eq_zero (by omega) _ _
    (wedgeProd_extensor_eq_zero_of_shared_vector n c hshare)

/-! ## The top exterior power of a space is a line (`lem:complement-iso-line-one-dim`)

For a vector space `W` of dimension `n`, `⋀^n W` has dimension `(n choose n) = 1`, so every element
of it is a multiple of a nonzero one. The formal proof uses the count in degree `d − 1`
(`finrank_exteriorPower_self_eq_one`, in `exists_smul_eq_of_mem_range_map_subtype_grade`); the node
states its case `n = 2`. -/

/-- **The top exterior power of an `n`-dimensional space is a line** (a step of
`lem:meet-two-hyperplanes`; `lem:complement-iso-line-one-dim` for every `n`): if `finrank W = n`,
then `finrank (⋀^n W) = (n choose n) = 1` (`exteriorPower.finrank_eq`, `Nat.choose_self`). -/
theorem finrank_exteriorPower_self_eq_one {W : Type*} [AddCommGroup W] [Module K W]
    [Module.Free K W] [Module.Finite K W] {n : ℕ} (hW : Module.finrank K W = n) :
    Module.finrank K (⋀[K]^n W) = 1 := by
  rw [exteriorPower.finrank_eq, hW, Nat.choose_self]

/-- **The exterior square of a `2`-dimensional space is a line**
(`lem:complement-iso-line-one-dim`): the case `n = 2` of `finrank_exteriorPower_self_eq_one`. -/
theorem finrank_exteriorPower_two_eq_one {W : Type*} [AddCommGroup W] [Module K W]
    [Module.Free K W] [Module.Finite K W] (hW : Module.finrank K W = 2) :
    Module.finrank K (⋀[K]^2 W) = 1 :=
  finrank_exteriorPower_self_eq_one hW

/-- **Every element of the exterior square of a plane is a multiple of a nonzero one**
(`lem:complement-iso-line-one-dim`): for `dim W = 2` and `x ≠ 0` in `⋀² W`, every `y` is `c • x` for
some `c` (`finrank_eq_one_iff_of_nonzero'`). -/
theorem exteriorPower_finrank_eq_one_proportional {W : Type*} [AddCommGroup W] [Module K W]
    [Module.Free K W] [Module.Finite K W] (hW : Module.finrank K W = 2)
    {x : ⋀[K]^2 W} (hx : x ≠ 0) (y : ⋀[K]^2 W) : ∃ c : K, c • x = y :=
  (finrank_eq_one_iff_of_nonzero' x hx).mp (finrank_exteriorPower_two_eq_one hW) y

/-! ## The exterior power of a subspace and its image (`lem:complement-iso-exterior-map-injective`)

For a subspace `W` of `V`, the map `⋀^g W → ⋀^g V` induced by the inclusion is injective, over a
field (`exteriorPower.map_injective_field`). A `g`-extensor of vectors of `W` lies in its image, and
when `dim W = g` the image is a line, so that two of its elements are proportional when one is not
zero. -/

/-- **The exterior power of a subspace embeds, in every degree** (a step of
`lem:meet-two-hyperplanes`; `lem:complement-iso-exterior-map-injective` in degree `g`): for a
subspace `W` of `K^(d+1)`, the map `exteriorPower.map g W.subtype : ⋀^g W → ⋀^g K^(d+1)` is
injective, as `W.subtype` is (`exteriorPower.map_injective_field`). -/
theorem exteriorPower_map_subtype_injective_grade {d : ℕ} (g : ℕ)
    (W : Submodule K (Fin (d + 1) → K)) :
    Function.Injective (exteriorPower.map g W.subtype) :=
  exteriorPower.map_injective_field W.injective_subtype

/-- **The exterior square of a subspace of `K⁴` embeds**
(`lem:complement-iso-exterior-map-injective`): the case `d = 3`, `g = 2` of
`exteriorPower_map_subtype_injective_grade`. -/
theorem exteriorPower_map_subtype_injective (W : Submodule K (Fin 4 → K)) :
    Function.Injective (exteriorPower.map 2 W.subtype) :=
  exteriorPower_map_subtype_injective_grade (d := 3) 2 W

/-- **A linear map that sends `W'` into `W` sends the image of `⋀^g W'` into that of `⋀^g W`** (a
step of `lem:meet-two-hyperplanes`): for a linear map `O` of `V` with `O w ∈ W` for `w ∈ W'`, if `X`
is the image of `Y : ⋀^g W'`, then `map g O X` is the image of `map g f Y`, for `f : W' → W` the
restriction of `O`. The proof of `complementIso_extensor_mem_range_map_subtype` applies it to an
inverse transpose. -/
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

/-- **A `j`-extensor of vectors of `W` lies in the image of `⋀^j W`** (a step of
`lem:meet-two-hyperplanes`): if every `v i` lies in the subspace `W` of `K^(d+1)`, then `extensor v`
is the image of `ιMulti K j (fun i => ⟨v i, hv i⟩)` under the map induced by the inclusion. The
degree `j` is independent of `d`; `extensor_mem_range_map_subtype_of_mem_grade` takes `j = d − 1`.
-/
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

/-- **A `(d−1)`-extensor of vectors of `W` lies in the image of `⋀^(d−1) W`** (a step of
`lem:meet-two-hyperplanes`): the case `j = d − 1` of `extensor_mem_range_map_subtype_of_mem_jgrade`,
the degree of a join of `d − 1` points. -/
theorem extensor_mem_range_map_subtype_of_mem_grade {d : ℕ}
    (W : Submodule K (Fin (d + 1) → K)) (v : Fin (d - 1) → Fin (d + 1) → K)
    (hv : ∀ i, v i ∈ W) :
    (⟨extensor v, extensor_mem_exteriorPower v⟩ : ⋀[K]^(d - 1) (Fin (d + 1) → K))
      ∈ LinearMap.range (exteriorPower.map (d - 1) W.subtype) :=
  extensor_mem_range_map_subtype_of_mem_jgrade W v hv

/-- **A `2`-extensor of vectors of a subspace `W` of `K⁴` lies in the image of `⋀² W`**: the case
`d = 3` of `extensor_mem_range_map_subtype_of_mem_grade`. -/
theorem extensor_mem_range_map_subtype_of_mem
    (W : Submodule K (Fin 4 → K)) (v : Fin 2 → Fin 4 → K) (hv : ∀ i, v i ∈ W) :
    (⟨extensor v, extensor_mem_exteriorPower v⟩ : ⋀[K]^2 (Fin 4 → K))
      ∈ LinearMap.range (exteriorPower.map 2 W.subtype) :=
  extensor_mem_range_map_subtype_of_mem_grade (d := 3) W v hv

/-- **Two elements of the image of `⋀^(d−1) W` are proportional** (a step of
`lem:meet-two-hyperplanes`): if `dim W = d − 1`, the image of the injective map
`⋀^(d−1) W → ⋀^(d−1) K^(d+1)` (`exteriorPower_map_subtype_injective_grade`) has dimension `1`
(`finrank_exteriorPower_self_eq_one`), so for a nonzero `x` in it, `span {x}` is the image
(`Submodule.eq_of_le_of_finrank_eq`), and every `y` in it is `c • x` for some `c`. The proof of
`lem:meet-two-hyperplanes` applies it to a join of `d − 1` vectors and to `*(n₁ ∨ n₂)`. -/
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

/-- **Two elements of the image of `⋀² W` in `⋀² K⁴` are proportional**, for `dim W = 2`: the case
`d = 3` of `exists_smul_eq_of_mem_range_map_subtype_grade`. -/
theorem exists_smul_eq_of_mem_range_map_subtype
    (W : Submodule K (Fin 4 → K)) (hW : Module.finrank K W = 2)
    {x y : ⋀[K]^2 (Fin 4 → K)}
    (hx : x ∈ LinearMap.range (exteriorPower.map 2 W.subtype)) (hxne : x ≠ 0)
    (hy : y ∈ LinearMap.range (exteriorPower.map 2 W.subtype)) :
    ∃ c : K, c • x = y :=
  exists_smul_eq_of_mem_range_map_subtype_grade (d := 3) W hW hx hxne hy

/-- **Two `2`-extensors of pairs in the same plane are proportional** (a step of
`lem:pencil-generic-steer`): for a linearly independent pair `v` and a pair `u` whose vectors lie in
`span (range v)`, `c • extensor v = extensor u` for some `c`. Both lie in the image of `⋀² P`,
`P = span (range v)`, which is a line (`finrank_exteriorPower_self_eq_one`), and `extensor v ≠ 0`
(`extensor_ne_zero_iff_linearIndependent`). `span_range_eq_of_extensor_eq` is a converse. -/
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
  -- The image of `⋀² P` is a line; both extensors lie in it, so they are proportional.
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

/-! ## Equal nonzero `2`-extensors span the same plane (`lem:decomposable-extensor-span-unique`)

A converse of `exists_smul_extensor_eq_of_mem_span_range`: a nonzero `2`-extensor determines the
plane spanned by its two vectors. -/

/-- **A vector lies in the plane of an independent pair exactly when its join with the pair is `0`**
(a step of `lem:decomposable-extensor-span-unique`): for linearly independent `a, b`,
`extensor ![x, a, b] = 0 ↔ x ∈ span {a, b}`, as `x, a, b` are linearly dependent exactly then
(`extensor_ne_zero_iff_linearIndependent`, `linearIndependent_finCons`). -/
theorem extensor_triple_eq_zero_iff {d : ℕ} {a b : Fin (d + 1) → K} (x : Fin (d + 1) → K)
    (hab : LinearIndependent K ![a, b]) :
    extensor ![x, a, b] = 0 ↔ x ∈ Submodule.span K (Set.range ![a, b]) := by
  have hcons : (![x, a, b] : Fin (2 + 1) → Fin (d + 1) → K) = Fin.cons x ![a, b] := rfl
  constructor
  · intro h0
    by_contra hx
    exact (extensor_ne_zero_iff_linearIndependent _).mpr
      (by rw [hcons, linearIndependent_finCons]; exact ⟨hab, hx⟩) h0
  · intro hx
    apply extensor_eq_zero_of_not_linearIndependent
    rw [hcons, linearIndependent_finCons]
    rintro ⟨-, hns⟩; exact hns hx

/-- **Equal nonzero `2`-extensors span the same plane** (`lem:decomposable-extensor-span-unique`):
if `extensor p = extensor p' ≠ 0`, then `span (range p') = span (range p)`. For every `x`,
`extensor ![x, p 0, p 1] = extensor ![x] ∨ extensor p` (`join_extensor`), so it equals
`extensor ![x, p' 0, p' 1]`, and `x` lies in either plane exactly when this is `0`
(`extensor_triple_eq_zero_iff`). It is the case `j = 2` of the proposition of Barnabei, Brini and
Rota recalled after `def:join`. -/
theorem span_range_eq_of_extensor_eq {d : ℕ} {p p' : Fin 2 → Fin (d + 1) → K}
    (hp : extensor p ≠ 0) (heq : extensor p = extensor p') :
    Submodule.span K (Set.range p') = Submodule.span K (Set.range p) := by
  have hp' : extensor p' ≠ 0 := heq ▸ hp
  have hpli : LinearIndependent K p := (extensor_ne_zero_iff_linearIndependent p).1 hp
  have hp'li : LinearIndependent K p' := (extensor_ne_zero_iff_linearIndependent p').1 hp'
  have hpc : (![p 0, p 1] : Fin 2 → Fin (d + 1) → K) = p := by funext i; fin_cases i <;> rfl
  have hp'c : (![p' 0, p' 1] : Fin 2 → Fin (d + 1) → K) = p' := by funext i; fin_cases i <;> rfl
  have habp : LinearIndependent K ![p 0, p 1] := by rw [hpc]; exact hpli
  have habp' : LinearIndependent K ![p' 0, p' 1] := by rw [hp'c]; exact hp'li
  -- The `3`-extensor depends on the pair only through its join (`join_extensor`).
  have key : ∀ x : Fin (d + 1) → K, extensor ![x, p 0, p 1] = extensor ![x, p' 0, p' 1] := by
    intro x
    have e1 : extensor ![x, p 0, p 1] = extensor ![x] * extensor ![p 0, p 1] := by
      rw [← join_def, join_extensor]; congr 1; funext i; fin_cases i <;> rfl
    have e2 : extensor ![x, p' 0, p' 1] = extensor ![x] * extensor ![p' 0, p' 1] := by
      rw [← join_def, join_extensor]; congr 1; funext i; fin_cases i <;> rfl
    rw [e1, e2, hpc, hp'c, heq]
  ext x
  rw [← hpc, ← hp'c, ← extensor_triple_eq_zero_iff x habp', ← extensor_triple_eq_zero_iff x habp,
    key]

/-! ## The `2`-extensors `a ∨ v` (`lem:case-III-claim612-line-in-panel-union`)

The map `v ↦ a ∨ v` from `K^(d+1)` to `⋀² K^(d+1)`, its kernel `span {a}` for `a ≠ 0`, and the
dimension `d` of its image. In the proof of `lem:case-III-claim612-line-in-panel-union`, the space
`Φ` spanned by the `n₁ ∨ v` and the `n₂ ∨ v` is the sum of two such images. -/

/-- **The map `v ↦ a ∨ v`** (for `lem:case-III-claim612-line-in-panel-union`): left multiplication
by `ι a` after `ι`, a linear map from `K^(d+1)` to `⋀² K^(d+1)`, as the product of two elements of
degree `1` has degree `2`. Its value in the exterior algebra is `extensor ![a, v]`
(`coe_wedgeFixedLeft`). -/
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

/-- **`wedgeFixedLeft a v` is `a ∨ v`** (a step of `lem:case-III-claim612-line-in-panel-union`): its
value in the exterior algebra is `extensor ![a, v]`. -/
@[simp]
theorem coe_wedgeFixedLeft {d : ℕ} (a v : Fin (d + 1) → K) :
    (wedgeFixedLeft a v : ExteriorAlgebra K (Fin (d + 1) → K)) = extensor ![a, v] := by
  rw [wedgeFixedLeft, LinearMap.codRestrict_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    extensor_apply, ExteriorAlgebra.ιMulti_apply]
  simp [List.ofFn_succ]

/-- **The kernel of `v ↦ a ∨ v` is `span {a}`** (a step of
`lem:case-III-claim612-line-in-panel-union`): for `a ≠ 0`, `a ∨ v = 0` exactly when `a, v` are
linearly dependent (`extensor_ne_zero_iff_linearIndependent`), that is, when `v ∈ span {a}`
(`LinearIndependent.pair_iff'`). -/
theorem ker_wedgeFixedLeft {d : ℕ} {a : Fin (d + 1) → K} (ha : a ≠ 0) :
    LinearMap.ker (wedgeFixedLeft a) = Submodule.span K {a} := by
  ext v
  rw [LinearMap.mem_ker, Submodule.mem_span_singleton, ← Subtype.coe_inj, ZeroMemClass.coe_zero,
    coe_wedgeFixedLeft, ← not_iff_not, not_exists, ← ne_eq,
    extensor_ne_zero_iff_linearIndependent, LinearIndependent.pair_iff' ha]

/-- **The image of `v ↦ a ∨ v` has dimension `d`** (a step of
`lem:case-III-claim612-line-in-panel-union`): for `a ≠ 0`, by rank–nullity, with the kernel
`span {a}` (`ker_wedgeFixedLeft`). For `d = 3` it is `3`, the dimension of the image of `v ↦ n ∨ v`
in the proof of the lemma. -/
theorem finrank_range_wedgeFixedLeft {d : ℕ} {a : Fin (d + 1) → K} (ha : a ≠ 0) :
    Module.finrank K (LinearMap.range (wedgeFixedLeft a)) = d := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (wedgeFixedLeft a)
  rw [ker_wedgeFixedLeft ha, finrank_span_singleton ha, Module.finrank_fin_fun] at hrn
  omega

/-! ## The coordinate pairing of extensors as a determinant
(`lem:case-III-claim612-line-in-panel-union`, `lem:meet-two-hyperplanes`)

The coordinate pairing `(b.exteriorPower n).toDual` of the standard basis `b` on `⋀^n K^(d+1)` is
`exteriorPower.pairingDual` after the map induced by `b.toDual` (`def:meet-pairing-dual`). On two
extensors it is the determinant of the dot products of their vectors
(`exteriorPower.pairingDual_ιMulti_ιMulti`). -/

/-- **The coordinate pairing of `⋀^n K^(d+1)` is the determinant pairing** (a step of
`lem:meet-two-hyperplanes` and `lem:case-III-claim612-line-in-panel-union`): for the standard basis
`b`, `(b.exteriorPower n).toDual = pairingDual ∘ₗ map n b.toDual`. Both sides are bilinear; on two
standard basis elements `e_s` and `e_t`, the left side is `1` if `s = t` and `0` otherwise, and the
right side is the determinant of the matrix of the pairings of their vectors, which is the identity
if `s = t` and has a zero row otherwise. -/
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
    exact ite_eq_right fun h =>
      hxs ((Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s x).1 ⟨j, h⟩)

/-- **The coordinate pairing of `⋀^n K⁴` is the determinant pairing** (a step of
`lem:case-III-claim612-line-in-panel-union`): the case `d = 3` of
`exteriorPower_basis_toDual_eq_pairingDual_comp_map_grade`. On two `2`-extensors `w₀ ∨ w₁` and
`c₀ ∨ c₁` it is the determinant of the dot products `wᵢ · c_j` (the proof of the lemma). -/
theorem exteriorPower_basis_toDual_eq_pairingDual_comp_map (n : ℕ) :
    ((Pi.basisFun K (Fin 4)).exteriorPower n).toDual =
      (exteriorPower.pairingDual K (Fin 4 → K) n).comp
        (exteriorPower.map n (Pi.basisFun K (Fin 4)).toDual) :=
  exteriorPower_basis_toDual_eq_pairingDual_comp_map_grade (d := 3) n

/-! ## The join of two vectors orthogonal to `n` and the `2`-extensors `n ∨ v`
(`lem:case-III-claim612-line-in-panel-union`)

If `w₀` and `w₁` are orthogonal to `c i₀`, the coordinate pairing of `w₀ ∨ w₁` and `c₀ ∨ c₁` is a
determinant with a zero row. So the join `x ∨ y` of the lemma is orthogonal to every `n_i ∨ v`, and
lies in the space `Ω` of its proof. This holds for the coordinate pairing, not for the wedge pairing
`vol (· ∨ ·)`, under which `w₀ ∨ w₁` and `c₀ ∨ c₁` pair to `det (w₀, w₁, c₀, c₁)`. -/

/-- **A join of vectors orthogonal to `c i₀` is orthogonal to `extensor c`** (a step of
`lem:case-III-claim612-line-in-panel-union`): for `w c : Fin 2 → K⁴` with `w j · c i₀ = 0` for both
`j`, the coordinate pairing of `extensor w` and `extensor c` is `0`. By
`exteriorPower_basis_toDual_eq_pairingDual_comp_map` it is the determinant of the matrix with the
entries `w j · c i` (`exteriorPower.pairingDual_ιMulti_ιMulti`), whose row `i₀` is zero. -/
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

/-! ## The span `Φ` of the `n₁ ∨ v` and the `n₂ ∨ v` has dimension `5`
(`lem:case-III-claim612-line-in-panel-union`)

For linearly independent `a` and `b`, the images of `v ↦ a ∨ v` and `v ↦ b ∨ v` meet in
`span {a ∨ b}`, so for `d = 3` their sum has dimension `3 + 3 − 1 = 5`. -/

/-- **The images of `v ↦ a ∨ v` and `v ↦ b ∨ v` meet in `span {a ∨ b}`** (a step of
`lem:case-III-claim612-line-in-panel-union`): for linearly independent `a, b` of `K^(d+1)`. The join
`a ∨ b` lies in both, as `a ∨ b = b ∨ (−a)` (`ExteriorAlgebra.ι_add_mul_swap`). Conversely, if
`a ∨ v = b ∨ w`, the join with `b` on the left gives `b ∨ a ∨ v = b ∨ b ∨ w = 0`, so `b, a, v` are
linearly dependent and `v ∈ span {a, b}` (`linearIndependent_finSnoc`); then `a ∨ v` is a multiple
of `a ∨ b`. -/
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

/-- **For `d = 3`, the sum of the images of `v ↦ a ∨ v` and `v ↦ b ∨ v` has dimension `5`** (a step
of `lem:case-III-claim612-line-in-panel-union`): for linearly independent `a, b ∈ K⁴`, each image
has dimension `3` (`finrank_range_wedgeFixedLeft`), and they meet in the line `span {a ∨ b}`
(`inf_range_wedgeFixedLeft`, with `a ∨ b ≠ 0`), so the sum has dimension `3 + 3 − 1 = 5`
(`Submodule.finrank_sup_add_finrank_inf_eq`). In the proof of the lemma, the elements of the
`6`-dimensional `⋀² K⁴` orthogonal to this sum for the coordinate pairing then form a line `Ω`. -/
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

/-! ## The meet of two planes and the join of two points of their line
(`lem:case-III-claim612-line-in-panel-union`; KT eq. (6.45), p. 691)

For linearly independent `n₁, n₂ ∈ K⁴` and `x, y` orthogonal to both, `x ∨ y` is a multiple of
`*(n₁ ∨ n₂)`. Let `Φ` be the span of the `n₁ ∨ v` and the `n₂ ∨ v`, of dimension `5`
(`finrank_sup_range_wedgeFixedLeft`), and `Ω` the space of the elements of `⋀² K⁴` orthogonal to `Φ`
for the coordinate pairing, a line. The join lies in `Ω`
(`extensor_toDual_extensor_eq_zero_of_perp`), and so does `*(n₁ ∨ n₂)`
(`complementIso_toDual_eq_zero_of_wedgeProd_eq_zero`), which is not zero. So a linear form that
vanishes on the meet vanishes on the join. Katoh and Tanigawa write the extensor of a line as the
join of two of its points (KT §2.1, p. 651), and use the joins in KT eq. (6.45); the formal proof
gives a hinge by the meet of two panels (`def:panel-support-extensor`). -/

/-- **The join of two points of a line is a multiple of the meet of two planes through it**
(`lem:case-III-claim612-line-in-panel-union`; KT eq. (6.45), p. 691): for linearly independent
`n_u, n'` of `K⁴` and `pi, pj` orthogonal to both (for the coordinate pairing `b.toDual`, the dot
product), `c • *(n_u ∨ n') = pi ∨ pj` for some `c`. Here `n_u` is the normal of the panel `Π(u)` and
`n'` that of a second plane, which meets `Π(u)` in the line through the points with the homogeneous
coordinates `pi` and `pj`. Both extensors lie in the line `Ω` of the section above, and
`*(n_u ∨ n') ≠ 0`. -/
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
  -- `dim Ω = 6 − dim Φ = 6 − 5 = 1`, as the coordinate pairing is nondegenerate.
  have hdim : Module.finrank K Ω = 1 := by
    rw [hΩ, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
    have h6 : Module.finrank K (⋀[K]^2 (Fin 4 → K)) = 6 := by
      rw [exteriorPower.finrank_eq, Module.finrank_pi]; rfl
    have hkey := Subspace.finrank_add_finrank_dualAnnihilator_eq Φ
    have h5 : Module.finrank K Φ = 5 := finrank_sup_range_wedgeFixedLeft n_u n' hpair
    omega
  -- An element orthogonal to all of `Φ` lies in `Ω`.
  have hmem : ∀ Z : ⋀[K]^2 (Fin 4 → K),
      (∀ φ ∈ Φ, (b.exteriorPower 2).toDual Z φ = 0) → Z ∈ Ω := by
    intro Z hZ
    rw [hΩ, Submodule.mem_comap, Submodule.mem_dualAnnihilator]
    intro φ hφ
    rw [LinearEquiv.coe_coe, Module.Basis.toDualEquiv_apply]
    exact hZ φ hφ
  -- An element orthogonal to the images of `v ↦ n_u ∨ v` and `v ↦ n' ∨ v` is orthogonal to `Φ`.
  have hkills : ∀ Z : ⋀[K]^2 (Fin 4 → K),
      (∀ v, (b.exteriorPower 2).toDual Z (wedgeFixedLeft n_u v) = 0) →
      (∀ v, (b.exteriorPower 2).toDual Z (wedgeFixedLeft n' v) = 0) → Z ∈ Ω := by
    intro Z hu hv'
    refine hmem Z fun φ hφ => ?_
    rw [hΦ, Submodule.mem_sup] at hφ
    obtain ⟨x, ⟨vx, hx⟩, y, ⟨vy, hy⟩, rfl⟩ := hφ
    rw [map_add, ← hx, ← hy, hu, hv', add_zero]
  -- The join `extensor ![pi, pj]` lies in `Ω`, by `extensor_toDual_extensor_eq_zero_of_perp`.
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
  -- The meet `complementIso (n_u ∨ n')` lies in `Ω`: the join of `n_u ∨ n'` with `n_u ∨ v` and
  -- with `n' ∨ v` is `0`, as a vector repeats
  -- (`complementIso_toDual_eq_zero_of_wedgeProd_eq_zero`).
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
  -- The meet is not zero (`n_u`, `n'` independent), so it spans the line `Ω`, which contains the
  -- join.
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

/-- **A form that vanishes on the meet vanishes on the join**
(`lem:case-III-claim612-line-in-panel-union`): under the hypotheses of
`complementIso_smul_eq_extensor_join`, a linear form `r` on `⋀² K⁴` with `r (*(n_u ∨ n')) = 0` has
`r (pi ∨ pj) = 0`, as `pi ∨ pj = c • *(n_u ∨ n')`. -/
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

/-- **The same, with the orthogonality as dot products**
(`lem:case-III-claim612-line-in-panel-union`): the hypotheses `pi ⬝ᵥ n_u = 0` and the like,
converted by `Pi.basisFun_toDual_apply`. The formal proof of the case `d = 3`
(`lem:case-III-candidate-dispatch-d3`) applies it, through
`exists_complementIso_ne_zero_of_homogeneousIncidence`, to a join of KT eq. (6.45) on which the form
`r` of KT Claim 6.12 does not vanish. -/
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

/-! ## `*e_S = ε_S • e_{Sᶜ}` (`def:meet-complement-iso`)

The complement of a standard basis element of `⋀^j V` is a multiple of the complementary one: the
formula after `lem:complement-iso-toDual`, by which `*` is the Hodge star operator of the standard
basis. -/

/-- **`*e_S = ε_S • e_{Sᶜ}`** (`def:meet-complement-iso`; the formula after
`lem:complement-iso-toDual`): `complementIso` sends the standard basis element `e_S` of `⋀^j V` to
`ε_S • e_{Sᶜ}`, where `ε_S = wedgePairing e_S e_{Sᶜ}`, which is not zero
(`wedgePairing_ιMulti_family_compl_ne_zero`). The coordinate of `*e_S` at `e_t` is
`wedgePairing e_S e_t` (`Module.Basis.coord_toDualEquiv_symm_apply`), which vanishes unless `t = Sᶜ`
(`wedgePairing_ιMulti_family_eq_zero_of_ne_compl`). -/
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
  -- Compare the coordinates at each `e_t`: that of `complementIso hj e_S` is the wedge pairing
  -- of `e_S` and `e_t`, which vanishes unless `t = Sᶜ`.
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

/-! ## The complement of a coordinate `2`-element (`lem:meet-two-hyperplanes`)

For a `2`-element set `S`, `*e_S` lies in the image of `⋀^k W` for every subspace `W` that contains
the `e_t` with `t ∉ S`: the first statement of `lem:meet-two-hyperplanes` for coordinate planes. -/

/-- **The complement of a coordinate `2`-element lies in the image of `⋀^k W`** (a step of
`lem:meet-two-hyperplanes`): for a `2`-element `S ⊆ Fin (k+2)` and a subspace `W` of `V` that
contains the standard basis vectors `e_t` with `t ∉ S`, `*e_S` lies in the image of
`exteriorPower.map k W.subtype`. By `complementIso_exteriorPower_basis_eq_smul_compl`,
`*e_S = ε_S • e_{Sᶜ}`, and `e_{Sᶜ}` is the extensor of the `e_t` with `t ∉ S`
(`extensor_mem_range_map_subtype_of_mem_grade`). -/
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

/-! ## The dot product as the coordinate pairing

On `K^m`, the coordinate pairing of the standard basis is the dot product, over any field, and the
dimension of the space of the vectors orthogonal to a family, plus that of the span of the family,
is `m`. -/

/-- **The coordinate pairing of `K^m` is the dot product**:
`(Pi.basisFun K (Fin m)).toDual w v = ∑ i, w i * v i`, over any field. -/
theorem piBasisFun_toDual_eq_sum {m : ℕ} (w v : Fin m → K) :
    (Pi.basisFun K (Fin m)).toDual w v = ∑ i, w i * v i := by
  conv_lhs => rw [← (Pi.basisFun K (Fin m)).sum_repr v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_smul, Module.Basis.toDual_eq_repr, smul_eq_mul, Pi.basisFun_repr, mul_comm]

/-- **The coordinate pairing of `K^m` is symmetric**, by `piBasisFun_toDual_eq_sum`. -/
theorem piBasisFun_toDual_symm {m : ℕ} (w v : Fin m → K) :
    (Pi.basisFun K (Fin m)).toDual w v = (Pi.basisFun K (Fin m)).toDual v w := by
  rw [piBasisFun_toDual_eq_sum, piBasisFun_toDual_eq_sum]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- **The vectors orthogonal to a family and the span of the family have complementary dimensions**:
for `n : ι → K^N`, the dimension of the common kernel of the forms `⟨·, n j⟩` plus that of
`span (range n)` is `N`. The kernel is the preimage of the dual annihilator of the span under
`b.toDualEquiv` (`Subspace.finrank_add_finrank_dualAnnihilator_eq`); `n` need not be independent.
`finrank_toDualPerp_pair_eq` and several counts in `Molecule/Pencil/` apply it. -/
theorem finrank_toDualPerp_add_finrank_span {ι : Type*} {N : ℕ} (n : ι → Fin N → K) :
    Module.finrank K
        (⨅ j, LinearMap.ker ((Pi.basisFun K (Fin N)).toDual.flip (n j))
          : Submodule K (Fin N → K)) + Module.finrank K (Submodule.span K (Set.range n)) = N := by
  set b := Pi.basisFun K (Fin N)
  set S : Submodule K (Fin N → K) := Submodule.span K (Set.range n) with hS
  have hQ : (⨅ j, LinearMap.ker (b.toDual.flip (n j)))
      = Submodule.comap b.toDualEquiv.toLinearMap S.dualAnnihilator := by
    ext w
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply,
      Submodule.mem_comap, LinearEquiv.coe_coe, Module.Basis.toDualEquiv_apply,
      Submodule.mem_dualAnnihilator]
    refine ⟨fun h v hv => ?_, fun h j => h (n j) (Submodule.subset_span ⟨j, rfl⟩)⟩
    have hle : S ≤ LinearMap.ker (b.toDual w) := by
      rw [hS, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      simpa using h j
    simpa using hle hv
  rw [hQ, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq, add_comm,
    Subspace.finrank_add_finrank_dualAnnihilator_eq, Module.finrank_fin_fun]

/-- **The vectors orthogonal to two independent vectors of `K^(m+2)` form an `m`-dimensional space**
(a step of `lem:meet-two-hyperplanes`): by `finrank_toDualPerp_add_finrank_span`, as the span has
dimension `2` (`finrank_span_eq_card`). -/
theorem finrank_toDualPerp_pair_eq {m : ℕ} {n : Fin 2 → Fin (m + 2) → K}
    (hn : LinearIndependent K n) :
    Module.finrank K
        (⨅ j : Fin 2, LinearMap.ker ((Pi.basisFun K (Fin (m + 2))).toDual.flip (n j))
          : Submodule K (Fin (m + 2) → K)) = m := by
  have := finrank_toDualPerp_add_finrank_span n
  rw [finrank_span_eq_card hn, Fintype.card_fin] at this
  omega

/-! ## The transformation law of `*` (`lem:meet-two-hyperplanes`)

For a linear automorphism `g` of `V` and its inverse transpose `h` for the coordinate pairing
(`⟨h x, g y⟩ = ⟨x, y⟩`), `*(map j g X) = det g • map (N−j) h (*X)`; with `*e_S = ε_S • e_{Sᶜ}`, this
gives the formula displayed after `def:meet`. Any two linearly independent vectors are `g e₀` and
`g e₁` for some `g` (`exists_linearEquiv_basisFun_pair`). -/

/-- **The coordinate pairing is invariant under a map and its inverse transpose** (a step of
`lem:meet-two-hyperplanes`): if `⟨h x, g y⟩ = ⟨x, y⟩` for all `x, y`, then
`⟨map n h Z, map n g B⟩ = ⟨Z, B⟩` on `⋀^n K^(d+1)`. On extensors both sides are determinants of
coordinate pairings of vectors (`exteriorPower_basis_toDual_eq_pairingDual_comp_map_grade`), and the
extensors span (`exteriorPower.ιMulti_span`). -/
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

/-- **The transformation law of `*`** (a step of `lem:meet-two-hyperplanes`): for a surjective
linear map `g` of `V` and `h` with `⟨h x, g y⟩ = ⟨x, y⟩`, `*(map j g X) = det g • map (N−j) h (*X)`.
Pair both sides with `B = map (N−j) g B'`, which is every `B` as `g` is onto: the left side gives
`vol (map j g X ∨ map (N−j) g B') = det g • vol (X ∨ B')` (`complementIso_toDual`,
`wedgePairing_map`), and the right side `det g • ⟨*X, B'⟩`
(`exteriorPower_basis_toDual_map_dualPair_eq`). -/
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

/-- **The inverse transpose of a linear automorphism** (for `lem:meet-two-hyperplanes`): the map `h`
with `⟨h x, g y⟩ = ⟨x, y⟩` for the coordinate pairing (`contragredient_toDual_pairing`), the dual
map of `g⁻¹` between the coordinate identifications of `V` with its dual. It exists for every linear
automorphism, over every field. -/
noncomputable def contragredient (g : (Fin (k + 2) → K) ≃ₗ[K] (Fin (k + 2) → K)) :
    (Fin (k + 2) → K) →ₗ[K] (Fin (k + 2) → K) :=
  (Pi.basisFun K (Fin (k + 2))).toDualEquiv.symm.toLinearMap ∘ₗ
    (g.symm : (Fin (k + 2) → K) →ₗ[K] (Fin (k + 2) → K)).dualMap ∘ₗ
    (Pi.basisFun K (Fin (k + 2))).toDualEquiv.toLinearMap

/-- **The pairing of the inverse transpose** (a step of `lem:meet-two-hyperplanes`):
`⟨contragredient g x, g y⟩ = ⟨x, y⟩`. -/
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

/-- **Two independent vectors are the images of `e₀` and `e₁` under a linear automorphism** (a step
of `lem:meet-two-hyperplanes`): for linearly independent `n 0, n 1` of `K^(k+2)`, some `g` has
`g e₀ = n 0` and `g e₁ = n 1`. Extend the pair by a basis of a complement of its span
(`Submodule.exists_isCompl`) to a basis of `V`, and let `g` send the standard basis to it. -/
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

/-! ## The meet of two hyperplanes and the join of `d − 1` vectors (`lem:meet-two-hyperplanes`)

For `n : Fin 2 → V`, `*(n 0 ∨ n 1)` lies in the image of `⋀^k W` for the `k`-dimensional space `W`
of the vectors orthogonal to `n 0` and `n 1`. If `n 0, n 1` are linearly independent and `k`
linearly independent vectors lie in `W`, their join is a multiple of `*(n 0 ∨ n 1)`. -/

/-- **The map induced by `f` on a `2`-extensor** (a step of `lem:meet-two-hyperplanes`):
`map 2 f (extensor v) = extensor (f ∘ v)`. It is a lemma of its own so that the proof of
`complementIso_extensor_mem_range_map_subtype` stays within the default heartbeat budget. -/
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

/-- **The meet of two hyperplanes lies in the image of `⋀^k W`** (`lem:meet-two-hyperplanes`, the
first statement): for `n : Fin 2 → K^(k+2)` and a `k`-dimensional subspace `W` whose vectors are
orthogonal to `n 0` and `n 1`, `*(n 0 ∨ n 1)` lies in the image of `exteriorPower.map k W.subtype`.
If `n` is dependent, `n 0 ∨ n 1 = 0`. Otherwise `W` is the space of all the vectors orthogonal to
`n` (`finrank_toDualPerp_pair_eq`). Take `g` with `g e₀ = n 0` and `g e₁ = n 1`
(`exists_linearEquiv_basisFun_pair`) and its inverse transpose `h`. Then `n 0 ∨ n 1 = map 2 g e_S`
for `S = {0, 1}`, so `*(n 0 ∨ n 1) = det g • map k h (*e_S)`
(`complementIso_map_contragredient_eq`). `*e_S` lies in the image of `⋀^k W₀`, for `W₀` the span of
the `e_t` with `t ∉ S` (`complementIso_exteriorPower_basis_mem_range_map_subtype`), and `h` sends
`W₀` into `W` (`exteriorPower_map_mem_range_map_subtype_of_mapsTo`). -/
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
  -- The space `Q` of the vectors orthogonal to `n 0` and `n 1`; `W = Q` by dimension.
  set Q : Submodule K (Fin (k + 2) → K) :=
    ⨅ j, LinearMap.ker ((Pi.basisFun K (Fin (k + 2))).toDual.flip (n j)) with hQ
  have hWQ : W ≤ Q := by
    intro w hw
    simp only [hQ, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply]
    exact hWperp w hw
  have hQdim : Module.finrank K Q = k := finrank_toDualPerp_pair_eq hn
  have hWQeq : W = Q := Submodule.eq_of_le_of_finrank_eq hWQ (by rw [hWdim, hQdim])
  -- The automorphism `g` with `g e₀ = n 0`, `g e₁ = n 1`, and its inverse transpose `h`.
  obtain ⟨g, hg0, hg1⟩ := exists_linearEquiv_basisFun_pair n hn
  set h : (Fin (k + 2) → K) →ₗ[K] (Fin (k + 2) → K) := contragredient g with hh
  have hgh : ∀ x y, (Pi.basisFun K (Fin (k + 2))).toDual (h x) (g y)
      = (Pi.basisFun K (Fin (k + 2))).toDual x y := contragredient_toDual_pairing g
  -- The `2`-element set `S = {0, 1}` and its enumerated standard basis vectors `vS`.
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
  -- Every image `h e_t` with `t ∉ {0, 1}` lies in `W = Q`.
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
    refine ite_eq_right fun hcontra => ?_
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
  -- `*e_S` lies in the image of `⋀^k W₀`.
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

/-- **The join of `d − 1` vectors orthogonal to the normals of two hyperplanes is a multiple of
their meet** (`lem:meet-two-hyperplanes`, the second statement): for linearly independent
`n : Fin 2 → K^(k+2)` and linearly independent `p : Fin k → K^(k+2)` orthogonal to `n 0` and `n 1`,
`c • *(n 0 ∨ n 1) = extensor p` for some `c`. With `W` the space of the vectors orthogonal to `n`,
of dimension `k` (`finrank_toDualPerp_pair_eq`), both lie in the image of `⋀^k W`
(`complementIso_extensor_mem_range_map_subtype`, `extensor_mem_range_map_subtype_of_mem_grade`),
which is a line (`exists_smul_eq_of_mem_range_map_subtype_grade`); both are nonzero, so the scalar
can be inverted. Katoh and Tanigawa take the extensors of KT eq. (6.67) as joins of `d − 1` points
(KT p. 698), while the formal proof gives a hinge by the meet of two panels
(`def:panel-support-extensor`); this lemma compares the two. -/
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
  -- The hypothesis `hWperp` of `complementIso_extensor_mem_range_map_subtype`, from `hWmem`.
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
  -- The join is not zero (`hp`), and the meet is not zero (`complementIso` is injective, and
  -- `extensor n ≠ 0` by `hpair`).
  have hjoinne : (⟨extensor p, extensor_mem_exteriorPower p⟩ : ⋀[K]^k (Fin (k + 2) → K)) ≠ 0 := by
    rw [Ne, Subtype.ext_iff]; exact (extensor_ne_zero_iff_linearIndependent p).2 hp
  have hmeetne : complementIso (k := k) (j := 2) (by omega)
      ⟨extensor n, extensor_mem_exteriorPower n⟩ ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (complementIso (k := k) (j := 2) (by omega)).injective,
      Subtype.ext_iff]
    exact (extensor_ne_zero_iff_linearIndependent n).2 hpair
  -- Both lie in the line, the image of `⋀^k W`, and the join is not zero, so the meet is a
  -- multiple of it; invert the scalar to write the join as a multiple of the meet.
  obtain ⟨c, hc⟩ :=
    exists_smul_eq_of_mem_range_map_subtype_grade (d := k + 1) W hWdim hjoin hjoinne hmeet
  have hcne : c ≠ 0 := by
    rintro rfl; rw [zero_smul] at hc; exact hmeetne hc.symm
  refine ⟨c⁻¹, ?_⟩
  rw [inv_smul_eq_iff₀ hcne]; exact hc.symm

end CombinatorialRigidity.Molecular
