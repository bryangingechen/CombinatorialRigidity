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
  `lem:complement-iso-toDual`); the meet `A ∧ B = *(*A ∨ *B)` (`def:meet`);
* the facts on `⋀² W` for a plane `W` that identify the line of `⋀² K⁴` on which two planes lie
  (`lem:complement-iso-line-one-dim`, `lem:complement-iso-exterior-map-injective`), and that equal
  nonzero `2`-extensors span the same plane (`lem:decomposable-extensor-span-unique`).

The rest of `sec:molecular-meet` is in `MeetHyperplanes.lean`, which imports this file: the
`2`-extensors `a ∨ v`, the coordinate pairing and the dot product (which `Molecule/Pencil/` uses),
`*e_S = ε_S • e_{Sᶜ}`, the transformation law of `*`, the meet of two hyperplanes
(`lem:meet-two-hyperplanes`) and, for `d = 3`, the meet of two planes as a multiple of the join of
two points of their line (`lem:complement-iso-decomposable-wedge-perp`,
`lem:case-III-claim612-line-in-panel-union`).

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

/-- **The meet** (`def:meet`): for `a + b ≤ N`, `A : ⋀^(N−a) V` and `B : ⋀^(N−b) V`,
`A ∧ₑ B = *(*A ∨ *B) : ⋀^(N−(a+b)) V`, where `*A : ⋀^a V` and `*B : ⋀^b V` (the degrees cast by
`N − (N − a) = a`) and their join is `gradedMul`. Nothing in the project uses `meet`: the formal
proof forms `*(n_A ∨ n_B)` directly (`rem:meet-kt-steps`). -/
noncomputable def meet {a b : ℕ} (hab : a + b ≤ k + 2)
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

/-- **Extensors of two bases of one subspace are proportional**, in every grade (the change of
basis of `lem:pencil-d-two-pencil-extension`): if `v : Fin j → K^(d+1)` is linearly independent and
every `u i` lies in the span of the `v i`, then `extensor u = c • extensor v` for some `c`. Both
lie in the image of `⋀^j W`, `W = span (range v)`, which is a line
(`finrank_exteriorPower_self_eq_one`). `span_range_eq_of_extensor_eq_grade` is a converse. -/
theorem exists_smul_extensor_eq_of_mem_span_range_grade {d j : ℕ}
    (u v : Fin j → Fin (d + 1) → K) (hv : LinearIndependent K v)
    (hu : ∀ i, u i ∈ Submodule.span K (Set.range v)) :
    ∃ c : K, c • extensor v = extensor u := by
  set W := Submodule.span K (Set.range v)
  have hWdim : Module.finrank K W = j := by rw [finrank_span_eq_card hv]; simp
  have hxv : (⟨extensor v, extensor_mem_exteriorPower v⟩ : ⋀[K]^j (Fin (d + 1) → K))
      ∈ LinearMap.range (exteriorPower.map j W.subtype) :=
    extensor_mem_range_map_subtype_of_mem_jgrade _ v fun i => Submodule.subset_span ⟨i, rfl⟩
  have hxu : (⟨extensor u, extensor_mem_exteriorPower u⟩ : ⋀[K]^j (Fin (d + 1) → K))
      ∈ LinearMap.range (exteriorPower.map j W.subtype) :=
    extensor_mem_range_map_subtype_of_mem_jgrade _ u hu
  have hvne : (⟨extensor v, extensor_mem_exteriorPower v⟩ : ⋀[K]^j (Fin (d + 1) → K)) ≠ 0 := by
    rw [Ne, Subtype.ext_iff]; exact (extensor_ne_zero_iff_linearIndependent v).2 hv
  have hR : Module.finrank K (LinearMap.range (exteriorPower.map j W.subtype)) = 1 := by
    rw [LinearMap.finrank_range_of_inj (exteriorPower_map_subtype_injective_grade (d := d) j _),
      finrank_exteriorPower_self_eq_one hWdim]
  have hspan : (K ∙ (⟨extensor v, extensor_mem_exteriorPower v⟩ : ⋀[K]^j (Fin (d + 1) → K)))
      = LinearMap.range (exteriorPower.map j W.subtype) :=
    Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).2 hxv)
      (by rw [finrank_span_singleton hvne, hR])
  rw [← hspan, Submodule.mem_span_singleton] at hxu
  obtain ⟨c, hc⟩ := hxu
  exact ⟨c, congrArg Subtype.val hc⟩

/-! ## Equal nonzero `2`-extensors span the same plane (`lem:decomposable-extensor-span-unique`)

A converse of `exists_smul_extensor_eq_of_mem_span_range_grade`: a nonzero `2`-extensor determines
the plane spanned by its two vectors. -/

/-- **Equal nonzero extensors span the same subspace, in every grade** (the argument of
`lem:decomposable-extensor-span-unique` with `j` vectors in place of two): if
`extensor p = extensor p' ≠ 0` for `p p' : Fin j → K^(d+1)`, then the two families have the same
span. For every `x`, the extensor of `x` followed by `p` is `ι x * extensor p`
(`ExteriorAlgebra.ιMulti_succ_apply`), so it equals that of `x` followed by `p'`; and as `p` is
linearly independent, `x` lies in its span exactly when this extensor is `0`
(`extensor_ne_zero_iff_linearIndependent`, `linearIndependent_finCons`). The case `j = 2` is
`span_range_eq_of_extensor_eq`. -/
theorem span_range_eq_of_extensor_eq_grade {d j : ℕ} {p p' : Fin j → Fin (d + 1) → K}
    (hp : extensor p ≠ 0) (heq : extensor p = extensor p') :
    Submodule.span K (Set.range p') = Submodule.span K (Set.range p) := by
  have hmem : ∀ q : Fin j → Fin (d + 1) → K, LinearIndependent K q → ∀ x,
      x ∈ Submodule.span K (Set.range q) ↔ extensor (Fin.cons x q) = 0 := by
    intro q hq x
    rw [← not_iff_not, ← Ne, extensor_ne_zero_iff_linearIndependent, linearIndependent_finCons]
    simp [hq]
  have hcons : ∀ (q : Fin j → Fin (d + 1) → K) x,
      extensor (Fin.cons x q) = ExteriorAlgebra.ι K x * extensor q := by
    intro q x
    rw [extensor_apply, extensor_apply, ExteriorAlgebra.ιMulti_succ_apply]
    rfl
  have hpli := (extensor_ne_zero_iff_linearIndependent p).1 hp
  have hp'li := (extensor_ne_zero_iff_linearIndependent p').1 (heq ▸ hp)
  ext x
  rw [hmem p' hp'li, hmem p hpli, hcons, hcons, heq]

/-- **Equal nonzero `2`-extensors span the same plane** (`lem:decomposable-extensor-span-unique`):
if `extensor p = extensor p' ≠ 0`, then `span (range p') = span (range p)`. It is the case
`j = 2` of `span_range_eq_of_extensor_eq_grade`, whose argument is the chapter's: for every `x`,
the join of `x` with `extensor p` (`def:join`) is their product `ι x * extensor p`, the extensor
of `x` followed by `p`, so it equals the join of `x` with `extensor p'`, and `x` lies in either
plane exactly when this join is `0`. It is the case `j = 2` of the proposition of Barnabei, Brini
and Rota recalled after `def:join`. -/
theorem span_range_eq_of_extensor_eq {d : ℕ} {p p' : Fin 2 → Fin (d + 1) → K}
    (hp : extensor p ≠ 0) (heq : extensor p = extensor p') :
    Submodule.span K (Set.range p') = Submodule.span K (Set.range p) := by
  exact span_range_eq_of_extensor_eq_grade hp heq

end CombinatorialRigidity.Molecular
