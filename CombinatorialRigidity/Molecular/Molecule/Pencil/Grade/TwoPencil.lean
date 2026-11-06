/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Mathlib.LinearAlgebra.LinearIndependent.Basic
public import CombinatorialRigidity.Molecular.MeetHyperplanes
public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Realization

/-!
# A hinge in two pencils, and moving a pencil realization, in every dimension

The three lemmas of linear algebra in `sec:pencil-d-reduction`
(`blueprint/src/chapter/pencil-d.tex`), which the cases of the reduction in every dimension use, at
grade `k`, in `K^(k+2)`. In the polar form of a pencil realization (`HasPencilPlaneRealization`), a
hinge at a link `uv` that lies in the panels of `u` and `v` and passes through the orthogonals of
their three-dimensional subspaces `Π_u`, `Π_v` is the hinge `C_B` of a two-dimensional subspace
`B ⊆ Π_u ∩ Π_v` containing the two normals: the extensor of a basis of `B^⊥`
(`lem:pencil-d-two-pencil-extension`). A linear automorphism `g` of `K^(k+2)` moves a pencil
realization to one of the same rank, the normals and subspaces by `g` and the hinges by the screw
map of its inverse transpose (`lem:pencil-d-projective-transport`), and some `g` puts the normals
`b_u` and `g b_v` of a cut edge, independent, in `Π_u ∩ gΠ_v` (`lem:pencil-d-cut-reposition`).
At grade `2` these are `exists_extensor_two_pencils_iff` (`Pencil/Statement.lean`),
`hasPencilPanelRealization_mapExtensor_screwEquivOfLinearEquiv` and
`exists_reposition_cross_incidences` (`Pencil/Arms.lean`), in the point form.

## Main definitions

* `perpExtensor`: the hinge `C_B` of a two-dimensional subspace `B`.

## Main results

* `perpExtensor_two_pencils`, `exists_eq_smul_perpExtensor`,
  `exists_extensor_two_pencils_iff_grade`, `linearIndependent_perpExtensor_pair`: the three parts of
  `lem:pencil-d-two-pencil-extension`.
* `hasPencilPlaneRealization_mapExtensor_screwEquivOfLinearEquiv`:
  `lem:pencil-d-projective-transport`.
* `exists_reposition_planes`: `lem:pencil-d-cut-reposition`.
-/

@[expose] public section

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

/-! ## `lem:pencil-d-two-pencil-extension` -/

/-- **The hinge of a two-dimensional subspace** (`C_B` of `lem:pencil-d-two-pencil-extension`): for
a subspace `B` of `K^(k+2)` of dimension two, the extensor of a basis of its orthogonal `B^⊥`, of
dimension `k` (`exists_extensor_eq_perpExtensor`); `0` when `B^⊥` does not have dimension `k`. -/
noncomputable def perpExtensor {k : ℕ} (B : Submodule K (Fin (k + 2) → K)) : ScrewSpace K k :=
  if h : Module.finrank K (dotPerp B) = k then
    ScrewSpace.mk
      (extensor fun i => (Module.finBasisOfFinrankEq K (dotPerp B) h i : Fin (k + 2) → K))
      (extensor_mem_exteriorPower _)
  else 0

/-- **`C_B` is the extensor of a basis of `B^⊥`** (the definition of `C_B` in
`lem:pencil-d-two-pencil-extension`): for `B` of dimension two, `B^⊥` has dimension `k`
(`finrank_dotPerp`), and `perpExtensor B` is the extensor of `k` linearly independent vectors that
span it. -/
theorem exists_extensor_eq_perpExtensor {k : ℕ} {B : Submodule K (Fin (k + 2) → K)}
    (hB : Module.finrank K B = 2) :
    ∃ p : Fin k → Fin (k + 2) → K, LinearIndependent K p ∧
      Submodule.span K (Set.range p) = dotPerp B ∧ (perpExtensor B).val = extensor p := by
  have h : Module.finrank K (dotPerp B) = k := by rw [finrank_dotPerp, hB]; omega
  have hli : LinearIndependent K
      (fun i => (Module.finBasisOfFinrankEq K (dotPerp B) h i : Fin (k + 2) → K)) :=
    (Module.finBasisOfFinrankEq K (dotPerp B) h).linearIndependent.map' (dotPerp B).subtype
      (Submodule.ker_subtype _)
  refine ⟨_, hli, Submodule.eq_of_le_of_finrank_eq ?_ ?_, ?_⟩
  · rw [Submodule.span_le, Set.range_subset_iff]
    exact fun i => (Module.finBasisOfFinrankEq K (dotPerp B) h i).2
  · rw [finrank_span_eq_card hli, Fintype.card_fin, h]
  · rw [perpExtensor, dite_eq_left h, ScrewSpace.val_mk]

/-- **A hinge in two pencils, in every dimension** (`lem:pencil-d-two-pencil-extension`, part (1)):
if a two-dimensional `B` contains `b_u` and `b_v` and lies in `Π_u` and in `Π_v`, then `C_B` is
nonzero, lies in the panels with normals `b_u` and `b_v` (`ExtensorInPanel`), and passes through
`Π_u^⊥` and `Π_v^⊥` (`ExtensorThroughSubspace`). The vectors of `C_B` span `B^⊥`
(`exists_extensor_eq_perpExtensor`), so they are independent and orthogonal to every vector of `B`,
and `Π^⊥ ⊆ B^⊥` when `B ⊆ Π`. The node's nonzero normals and three-dimensional subspaces are not
used. -/
theorem perpExtensor_two_pencils {k : ℕ} {B Pu Pv : Submodule K (Fin (k + 2) → K)}
    {bu bv : Fin (k + 2) → K} (hB : Module.finrank K B = 2) (hu : bu ∈ B) (hv : bv ∈ B)
    (hBu : B ≤ Pu) (hBv : B ≤ Pv) :
    perpExtensor B ≠ 0 ∧ ExtensorInPanel (perpExtensor B) bu ∧
      ExtensorInPanel (perpExtensor B) bv ∧
      ExtensorThroughSubspace (perpExtensor B) (dotPerp Pu) ∧
      ExtensorThroughSubspace (perpExtensor B) (dotPerp Pv) := by
  obtain ⟨p, hli, hspan, hval⟩ := exists_extensor_eq_perpExtensor hB
  have hperp : ∀ x ∈ B, ∀ i, p i ⬝ᵥ x = 0 := fun x hx i =>
    mem_dotPerp.1 (hspan ▸ Submodule.subset_span ⟨i, rfl⟩) x hx
  have hthrough : ∀ P : Submodule K (Fin (k + 2) → K), B ≤ P →
      ExtensorThroughSubspace (perpExtensor B) (dotPerp P) := fun P hBP =>
    ⟨p, hval, hspan ▸ LinearMap.BilinForm.orthogonal_le hBP⟩
  refine ⟨fun h0 => ?_, ⟨p, hval, hperp bu hu⟩, ⟨p, hval, hperp bv hv⟩, hthrough Pu hBu,
    hthrough Pv hBv⟩
  rw [h0, ScrewSpace.val_zero] at hval
  exact (extensor_ne_zero_iff_linearIndependent p).2 hli hval.symm

/-- **Every hinge in two pencils is some `C_B`** (`lem:pencil-d-two-pencil-extension`, part (2)):
a nonzero `C` in the panels of `b_u` and `b_v` that passes through `Π_u^⊥` and `Π_v^⊥` is a nonzero
multiple of `C_B` for a two-dimensional `B ⊆ Π_u ∩ Π_v` containing `b_u` and `b_v`. As `C ≠ 0` and
lies in the panel of `b_u`, it is the extensor of independent vectors orthogonal to `b_u`; let `A`
be their span. Every expression of `C` as an extensor has vectors spanning `A`
(`span_range_eq_of_extensor_eq_grade`), so `B = A^⊥` holds `b_u` and `b_v`, and lies in `Π_u` and
`Π_v` as `(Π^⊥)^⊥ = Π` (`dotPerp_dotPerp`). Then `C` and `C_B` are extensors of two bases of
`A = B^⊥`, so proportional (`exists_smul_extensor_eq_of_mem_span_range_grade`). -/
theorem exists_eq_smul_perpExtensor {k : ℕ} {C : ScrewSpace K k}
    {bu bv : Fin (k + 2) → K} {Pu Pv : Submodule K (Fin (k + 2) → K)} (hC : C ≠ 0)
    (hu : ExtensorInPanel C bu) (hv : ExtensorInPanel C bv)
    (htu : ExtensorThroughSubspace C (dotPerp Pu)) (htv : ExtensorThroughSubspace C (dotPerp Pv)) :
    ∃ B : Submodule K (Fin (k + 2) → K), Module.finrank K B = 2 ∧ bu ∈ B ∧ bv ∈ B ∧
      B ≤ Pu ∧ B ≤ Pv ∧ ∃ c : K, c ≠ 0 ∧ C = c • perpExtensor B := by
  obtain ⟨p, hp, hpu⟩ := hu
  have hpne : extensor p ≠ 0 := hp ▸ ScrewSpace.val_injective.ne hC
  have hpli := (extensor_ne_zero_iff_linearIndependent p).1 hpne
  set A := Submodule.span K (Set.range p)
  have hspan : ∀ p' : Fin k → Fin (k + 2) → K, C.val = extensor p' →
      Submodule.span K (Set.range p') = A := fun p' hp' =>
    span_range_eq_of_extensor_eq_grade hpne (hp.symm.trans hp')
  have hB : Module.finrank K (dotPerp A) = 2 := by
    rw [finrank_dotPerp, finrank_span_eq_card hpli]; simp
  have hle : ∀ P : Submodule K (Fin (k + 2) → K), ExtensorThroughSubspace C (dotPerp P) →
      dotPerp A ≤ P := fun P ⟨p', hp', hle⟩ => by
    rw [hspan p' hp'] at hle
    have h2 : dotPerp A ≤ dotPerp (dotPerp P) := LinearMap.BilinForm.orthogonal_le hle
    rwa [dotPerp_dotPerp] at h2
  have hbu : bu ∈ dotPerp A := mem_dotPerp_span_range.2 fun i => by
    rw [dotProduct_comm]; exact hpu i
  have hbv : bv ∈ dotPerp A := by
    obtain ⟨p', hp', hpv⟩ := hv
    rw [← hspan p' hp']
    exact mem_dotPerp_span_range.2 fun i => by rw [dotProduct_comm]; exact hpv i
  refine ⟨dotPerp A, hB, hbu, hbv, hle Pu htu, hle Pv htv, ?_⟩
  -- `C` and `C_B` are extensors of two bases of `A = B^⊥`
  obtain ⟨q, hqli, hqspan, hqval⟩ := exists_extensor_eq_perpExtensor hB
  rw [dotPerp_dotPerp] at hqspan
  obtain ⟨c, hc⟩ := exists_smul_extensor_eq_of_mem_span_range_grade p q hqli
    fun i => hqspan ▸ Submodule.subset_span ⟨i, rfl⟩
  have hCeq : C = c • perpExtensor (dotPerp A) := by
    apply ScrewSpace.ext
    rw [ScrewSpace.val_smul, hqval, hp, hc]
  refine ⟨c, fun h0 => hC ?_, hCeq⟩
  rw [hCeq, h0, zero_smul]

/-- **When a hinge in two pencils exists** (`lem:pencil-d-two-pencil-extension`, part (2), its last
claim): for `b_u ≠ 0`, a nonzero `C` in the panels of `b_u` and `b_v` that passes through `Π_u^⊥`
and `Π_v^⊥` exists if and only if `b_u, b_v ∈ Π_u ∩ Π_v` and `dim (Π_u ∩ Π_v) ≥ 2`. Such a `C` is a
multiple of `C_B` for some `B` (`exists_eq_smul_perpExtensor`), which gives the conditions.
Conversely, let `B` be the span of `b_u` and `b_v` if they are independent, and otherwise of `b_u`
and a vector of `Π_u ∩ Π_v` independent of it (`exists_mem_linearIndependent_pair`); then part (1)
applies (`perpExtensor_two_pencils`). -/
theorem exists_extensor_two_pencils_iff_grade {k : ℕ} {bu bv : Fin (k + 2) → K}
    {Pu Pv : Submodule K (Fin (k + 2) → K)} (hbu : bu ≠ 0) :
    (∃ C : ScrewSpace K k, C ≠ 0 ∧ ExtensorInPanel C bu ∧ ExtensorInPanel C bv ∧
      ExtensorThroughSubspace C (dotPerp Pu) ∧ ExtensorThroughSubspace C (dotPerp Pv)) ↔
      bu ∈ Pu ⊓ Pv ∧ bv ∈ Pu ⊓ Pv ∧ 2 ≤ Module.finrank K ↥(Pu ⊓ Pv) := by
  constructor
  · rintro ⟨C, hC, hu, hv, htu, htv⟩
    obtain ⟨B, hB, hbuB, hbvB, hBu, hBv, -⟩ := exists_eq_smul_perpExtensor hC hu hv htu htv
    have hBle : B ≤ Pu ⊓ Pv := le_inf hBu hBv
    exact ⟨hBle hbuB, hBle hbvB, hB.symm.trans_le (Submodule.finrank_mono hBle)⟩
  · rintro ⟨hu, hv, hdim⟩
    -- a two-dimensional `B` with `bu, bv ∈ B ≤ Pu ⊓ Pv`
    obtain ⟨c, hc, hli, hvmem⟩ : ∃ c ∈ Pu ⊓ Pv, LinearIndependent K ![bu, c] ∧
        bv ∈ Submodule.span K {bu, c} := by
      by_cases hbv : LinearIndependent K ![bu, bv]
      · exact ⟨bv, hv, hbv, Submodule.subset_span (Set.mem_insert_of_mem _ rfl)⟩
      · obtain ⟨c, hc, hli⟩ := exists_mem_linearIndependent_pair hbu hdim
        refine ⟨c, hc, hli, ?_⟩
        rw [LinearIndependent.pair_iff' hbu] at hbv
        push Not at hbv
        obtain ⟨a, rfl⟩ := hbv
        exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _))
    have hBle : Submodule.span K {bu, c} ≤ Pu ⊓ Pv := by
      rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨hu, hc⟩
    obtain ⟨hne, h1, h2, h3, h4⟩ := perpExtensor_two_pencils (finrank_span_pair_eq_two hli)
      (Submodule.subset_span (Set.mem_insert _ _)) hvmem (hBle.trans inf_le_left)
      (hBle.trans inf_le_right)
    exact ⟨_, hne, h1, h2, h3, h4⟩

/-- **The hinges of two different subspaces are independent** (`lem:pencil-d-two-pencil-extension`,
part (3)), for `k ≥ 1`: if `B ≠ B'` both have dimension two, `C_B` and `C_{B'}` are linearly
independent. Otherwise `C_{B'} = a • C_B`, which lies in the panel of every vector of `B`
(`ExtensorInPanel.smul`); as `C_{B'} ≠ 0`, every expression of it as an extensor has vectors
spanning `B'^⊥` (`span_range_eq_of_extensor_eq_grade`), so `B ⊆ (B'^⊥)^⊥ = B'`, and the two are
equal by dimension. -/
theorem linearIndependent_perpExtensor_pair {k : ℕ} [NeZero k]
    {B B' : Submodule K (Fin (k + 2) → K)} (hB : Module.finrank K B = 2)
    (hB' : Module.finrank K B' = 2) (hne : B ≠ B') :
    LinearIndependent K ![perpExtensor B, perpExtensor B'] := by
  have hC := (perpExtensor_two_pencils hB (zero_mem B) (zero_mem B) le_rfl le_rfl).1
  have hC' := (perpExtensor_two_pencils hB' (zero_mem B') (zero_mem B') le_rfl le_rfl).1
  obtain ⟨p', -, hspan', hval'⟩ := exists_extensor_eq_perpExtensor hB'
  rw [LinearIndependent.pair_iff' hC]
  intro a ha
  -- `C_{B'} = a • C_B` lies in the panel of every vector of `B`, so its vectors, which span
  -- `B'^⊥`, are orthogonal to `B`
  have hmem : ∀ w ∈ B, w ∈ B' := by
    intro w hw
    obtain ⟨p'', hp'', hperp⟩ :=
      ha ▸ (perpExtensor_two_pencils hB hw hw le_rfl le_rfl).2.1.smul a
    have hspan'' := span_range_eq_of_extensor_eq_grade
      (hval' ▸ ScrewSpace.val_injective.ne hC') (hval'.symm.trans hp'')
    rw [← dotPerp_dotPerp B', mem_dotPerp, ← hspan', ← hspan'']
    intro y hy
    rw [dotProduct_comm]
    exact dotProduct_eq_zero_of_mem_span_range hperp hy
  exact hne (Submodule.eq_of_le_of_finrank_eq hmem (by rw [hB, hB']))

/-- **Two planes through a normal** (the two independent hinges of `lem:pencil-d-base-case` and
`lem:pencil-d-nonsimple-case`): a three-dimensional `P` containing `b ≠ 0` has two different
two-dimensional subspaces `B₁ ≠ B₂` containing `b`: `B₁ = span {b, c₁}` for some `c₁ ∈ P`
independent of `b`, and `B₂ = span {b, c₂}` for some `c₂ ∈ P` off `B₁`. Their hinges are linearly
independent (`linearIndependent_perpExtensor_pair`). -/
theorem exists_two_planes_of_mem {n : ℕ} {P : Submodule K (Fin n → K)} {b : Fin n → K}
    (hb : b ≠ 0) (hbP : b ∈ P) (hP : Module.finrank K P = 3) :
    ∃ B₁ B₂ : Submodule K (Fin n → K), Module.finrank K B₁ = 2 ∧ Module.finrank K B₂ = 2 ∧
      b ∈ B₁ ∧ b ∈ B₂ ∧ B₁ ≤ P ∧ B₂ ≤ P ∧ B₁ ≠ B₂ := by
  obtain ⟨c₁, hc₁, hli₁⟩ := exists_mem_linearIndependent_pair hb (by rw [hP]; norm_num)
  have hB₁ := finrank_span_pair_eq_two hli₁
  have hB₁le : Submodule.span K {b, c₁} ≤ P := by
    rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]; exact ⟨hbP, hc₁⟩
  have hnotle : ¬ P ≤ Submodule.span K {b, c₁} := fun hle => by
    have := Submodule.finrank_mono hle; omega
  obtain ⟨c₂, hc₂, hc₂B₁⟩ := IsConcreteLE.not_le_iff_exists.1 hnotle
  have hli₂ : LinearIndependent K ![b, c₂] := (LinearIndependent.pair_iff' hb).2 fun a h =>
    hc₂B₁ (h ▸ Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
  refine ⟨_, _, hB₁, finrank_span_pair_eq_two hli₂, Submodule.subset_span (Set.mem_insert _ _),
    Submodule.subset_span (Set.mem_insert _ _), hB₁le, ?_, fun h => hc₂B₁ ?_⟩
  · rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]; exact ⟨hbP, hc₂⟩
  · rw [h]; exact Submodule.subset_span (Set.mem_insert_of_mem _ rfl)

/-! ## `lem:pencil-d-projective-transport` -/

/-- **Moving a pencil realization by a linear map, in every dimension**
(`lem:pencil-d-projective-transport`): let `g` be a linear automorphism of `K^(k+2)` and `h` its
inverse transpose, `h x ⬝ g y = x ⬝ y`. A pencil realization `(F, b, Π)` of `G` moves to one with
the hinges `Λ_h(C_e)` (`BodyHingeFramework.mapExtensor` by the screw map
`BodyHingeFramework.screwEquivOfLinearEquiv h`, `def:induced-screw-map`), the normals `g b_v` and
the subspaces `g Π_v`, whose rigidity rows span a space of the same dimension
(`BodyHingeFramework.finrank_span_rigidityRows_mapExtensor`, `lem:screw-map-rows`); and `g` keeps
every independent pair of normals independent. The hinge of `p` goes to that of `h ∘ p`
(`BodyHingeFramework.screwEquivOfLinearEquiv_mk_extensor`), orthogonal to `g b_v` as
`h x ⬝ g b_v = x ⬝ b_v`, and with span containing `(g Π_v)^⊥ = h (Π_v^⊥)` (`dotPerp_map_eq`). At
grade `2` this is `hasPencilPanelRealization_mapExtensor_screwEquivOfLinearEquiv`, with `g` and `h`
exchanged, in the point form. -/
theorem hasPencilPlaneRealization_mapExtensor_screwEquivOfLinearEquiv {k : ℕ} {G : Graph α β}
    {F : BodyHingeFramework K k α β} {normal : α → Fin (k + 2) → K}
    {plane : α → Submodule K (Fin (k + 2) → K)}
    (g h : (Fin (k + 2) → K) ≃ₗ[K] (Fin (k + 2) → K))
    (hgh : ∀ x y : Fin (k + 2) → K, h x ⬝ᵥ g y = x ⬝ᵥ y)
    (hr : HasPencilPlaneRealization G F normal plane) :
    HasPencilPlaneRealization G (F.mapExtensor (BodyHingeFramework.screwEquivOfLinearEquiv h))
        (fun v => g (normal v))
        (fun v => (plane v).map (g : (Fin (k + 2) → K) →ₗ[K] (Fin (k + 2) → K))) ∧
      Module.finrank K (Submodule.span K
          (F.mapExtensor (BodyHingeFramework.screwEquivOfLinearEquiv h)).rigidityRows) =
        Module.finrank K (Submodule.span K F.rigidityRows) ∧
      ∀ u v, LinearIndependent K ![normal u, normal v] →
        LinearIndependent K ![g (normal u), g (normal v)] := by
  obtain ⟨⟨hFg, hnnz, hSnz, hpanel⟩, hdim, hmem, hthrough⟩ := hr
  -- the moved hinge of an extensor `extensor p` is `extensor (h ∘ p)`
  have hmove : ∀ (C : ScrewSpace K k) (p : Fin k → Fin (k + 2) → K), C.val = extensor p →
      (BodyHingeFramework.screwEquivOfLinearEquiv h C).val = extensor (fun i => h (p i)) := by
    intro C p hp
    have hC : C = ScrewSpace.mk (extensor p) (extensor_mem_exteriorPower p) :=
      ScrewSpace.ext (by rw [ScrewSpace.val_mk]; exact hp)
    rw [hC, BodyHingeFramework.screwEquivOfLinearEquiv_mk_extensor, ScrewSpace.val_mk]
    rfl
  have hpanel' : ∀ (C : ScrewSpace K k) (b : Fin (k + 2) → K), ExtensorInPanel C b →
      ExtensorInPanel (BodyHingeFramework.screwEquivOfLinearEquiv h C) (g b) :=
    fun C b ⟨p, hp, hperp⟩ => ⟨_, hmove C p hp, fun i => by rw [hgh]; exact hperp i⟩
  have hthrough' : ∀ (C : ScrewSpace K k) (P : Submodule K (Fin (k + 2) → K)),
      ExtensorThroughSubspace C (dotPerp P) →
      ExtensorThroughSubspace (BodyHingeFramework.screwEquivOfLinearEquiv h C)
        (dotPerp (P.map (g : (Fin (k + 2) → K) →ₗ[K] (Fin (k + 2) → K)))) := by
    rintro C P ⟨p, hp, hle⟩
    refine ⟨_, hmove C p hp, ?_⟩
    rw [dotPerp_map_eq g h hgh, Set.range_comp' (h : (Fin (k + 2) → K) → (Fin (k + 2) → K)) p]
    exact (Submodule.map_mono hle).trans (Submodule.map_span _ _).le
  refine ⟨⟨⟨hFg, fun v hv => (map_ne_zero_iff g g.injective).2 (hnnz v hv), fun e => ?_,
    fun e u v huv => ⟨hpanel' _ _ (hpanel e u v huv).1, hpanel' _ _ (hpanel e u v huv).2⟩⟩,
    fun v hv => by rw [LinearEquiv.finrank_map_eq]; exact hdim v hv,
    fun v hv => Submodule.mem_map_of_mem (hmem v hv),
    fun e u v huv => ⟨hthrough' _ _ (hthrough e u v huv).1, hthrough' _ _ (hthrough e u v huv).2⟩⟩,
    BodyHingeFramework.finrank_span_rigidityRows_mapExtensor _ _,
    fun u v huv => by
      simpa using huv.pair_map (g : (Fin (k + 2) → K) →ₗ[K] (Fin (k + 2) → K)) g.injective⟩
  rw [BodyHingeFramework.mapExtensor_supportExtensor]
  exact (map_ne_zero_iff _ (LinearEquiv.injective _)).2 (hSnz e)

/-! ## `lem:pencil-d-cut-reposition` -/

/-- **Moving one side of a cut edge, in every dimension** (`lem:pencil-d-cut-reposition`): for
nonzero `b_u ∈ Π_u` and `b_v ∈ Π_v`, with `Π_u` and `Π_v` three-dimensional, some linear
automorphism `g` of `K^(k+2)` makes `b_u` and `g b_v` linearly independent and puts both in
`Π_u ∩ g Π_v`. Take `c ∈ Π_u` independent of `b_u` and `c' ∈ Π_v` independent of `b_v`
(`exists_mem_linearIndependent_pair`), extend the pairs `b_v, c'` and `c, b_u` to bases
(`exists_linearEquiv_basisFun_pair`), and let `g` map the first to the second: `g b_v = c` and
`g c' = b_u`. At grade `2` this is `exists_reposition_cross_incidences`, with the normals and the
points exchanged. -/
theorem exists_reposition_planes {k : ℕ} {bu bv : Fin (k + 2) → K}
    {Pu Pv : Submodule K (Fin (k + 2) → K)} (hbu : bu ≠ 0) (hbv : bv ≠ 0)
    (hPu : Module.finrank K Pu = 3) (hPv : Module.finrank K Pv = 3) (hu : bu ∈ Pu) (hv : bv ∈ Pv) :
    ∃ g : (Fin (k + 2) → K) ≃ₗ[K] (Fin (k + 2) → K),
      LinearIndependent K ![bu, g bv] ∧
      bu ∈ Pu ⊓ Pv.map (g : (Fin (k + 2) → K) →ₗ[K] (Fin (k + 2) → K)) ∧
      g bv ∈ Pu ⊓ Pv.map (g : (Fin (k + 2) → K) →ₗ[K] (Fin (k + 2) → K)) := by
  obtain ⟨c, hc, hlic⟩ := exists_mem_linearIndependent_pair hbu (by rw [hPu]; norm_num)
  obtain ⟨c', hc', hlic'⟩ := exists_mem_linearIndependent_pair hbv (by rw [hPv]; norm_num)
  obtain ⟨g₁, hg₁0, hg₁1⟩ := exists_linearEquiv_basisFun_pair ![bv, c'] hlic'
  obtain ⟨g₂, hg₂0, hg₂1⟩ :=
    exists_linearEquiv_basisFun_pair ![c, bu] (LinearIndependent.pair_symm_iff.mp hlic)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hg₁0 hg₁1 hg₂0 hg₂1
  set g := g₁.symm.trans g₂ with hgdef
  have hgbv : g bv = c := by
    rw [hgdef, LinearEquiv.trans_apply, ← hg₁0, g₁.symm_apply_apply, hg₂0]
  have hgc' : g c' = bu := by
    rw [hgdef, LinearEquiv.trans_apply, ← hg₁1, g₁.symm_apply_apply, hg₂1]
  refine ⟨g, hgbv ▸ hlic, ⟨hu, hgc' ▸ Submodule.mem_map_of_mem hc'⟩,
    ⟨hgbv ▸ hc, Submodule.mem_map_of_mem hv⟩⟩

end CombinatorialRigidity.Molecular
