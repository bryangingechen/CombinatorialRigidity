/-
Copyright (c) 2024 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson, Bryan Gin-ge Chen

This file is ported from Peter Nelson's `apnelson1/Matroid` package
(https://github.com/apnelson1/Matroid, Apache-2.0), specifically its shelved
`WIP/Union.lean`. That file's proofs are complete (modulo a single commented-out
`sorry`) but rest on the package's superseded `FinsetCircuitMatroid`-based
submodular machinery and on a never-committed `Matroid.ForMathlib.Set` lemma.

Modifications made in the port:
* Rebased onto the local `CombinatorialRigidity.Matroid.Constructions.Submodular`
  (which itself rebases `ofSubmodular` / polymatroid onto the live
  `FiniteCircuitMatroid` constructor).
* Reconstructed the commented-out `ForMathlib/Set.lean` lemma
  `exists_pairwiseDisjoint_iUnion_eq` here as a `private` lemma (matching the
  L2a precedent for the commented `ForMathlib/Finset.lean` helpers).
* This file ports only the matroid-union *construction* and its independence
  characterizations (`Matroid.Union`, `Matroid.union`, `union_indep_iff`,
  `union_indep_iff'`); the partition rank theorem (`matroid_partition'` /
  `matroid_partition_eRk'`) is deferred to a follow-up commit.
-/
import Matroid.Constructions.Matching
import Mathlib.Combinatorics.Matroid.Sum
import CombinatorialRigidity.Matroid.Constructions.Submodular

/-!
# Matroid union (independence characterization)

This file ports the matroid-union construction of Nash-Williams 1966 /
Edmonds from Peter Nelson's `apnelson1/Matroid` package. The union of a finite
indexed family of matroids on a common ground set is realized via the
bipartite-matching adjunction `Matroid.adjMap` applied to the direct sum
`Matroid.sum'`.

This is Phase 12 (matroid foundations) of the body-bar program; see
`notes/Phase12.md` and `blueprint/src/chapter/matroid-union.tex`.

## Main declarations

* `Matroid.Union` — the union of an indexed family `Ms : ι → Matroid α`
  (`def:matroid-union`).
* `Matroid.union` — the binary union of two matroids.
* `Matroid.union_indep_iff` / `Matroid.union_indep_iff'` — a set is independent
  in the union iff it decomposes as a union of independent sets, one from each
  factor (`lem:union-indep-iff`).
-/

namespace Matroid

universe u

variable {α ι β : Type*}

open Set Function

/-- A `Set`-valued analogue of `Matroid.AdjIndep`: `I : Set β` is `AdjIndep'`
relative to `M : Matroid α` and `Adj : α → β → Prop` if it is matchable to an
`M`-independent set. -/
def AdjIndep' (M : Matroid α) (Adj : α → β → Prop) (I : Set β) :=
  I = ∅ ∨ ∃ (I₀ : Set α) (f : β → α), M.Indep I₀ ∧ IsMatching Adj f I₀ I

@[simp] lemma adjMap_indep_iff' [DecidableEq β] [Finite β] (M : Matroid α) (Adj : α → β → Prop)
    (E : Set β) {I : Set β} : (M.adjMap Adj E).Indep I ↔ M.AdjIndep' Adj I ∧ (I : Set β) ⊆ E := by
  classical
  haveI : Fintype β := Fintype.ofFinite β
  simp only [adjMap, IndepMatroid.ofFinset, AdjIndep, exists_and_left, restrict_indep_iff,
    IndepMatroid.matroid_Indep, IndepMatroid.ofFinitaryCardAugment_indep, AdjIndep',
    and_congr_left_iff]
  refine fun hIE ↦ ⟨fun h ↦ ?_, fun h J hJ ↦ ?_⟩
  · obtain h | h := h I.toFinset (coe_toFinset I).subset
    · simp only [toFinset_eq_empty.mp h, true_or]
    · obtain ⟨I₀, hi, hm⟩ := h
      right
      refine ⟨I₀, hi, (coe_toFinset I) ▸ hm⟩
  · obtain rfl | hem := eq_or_ne I ∅
    · simp only [Finset.coe_eq_empty.mp (subset_eq_empty hJ rfl), Finset.coe_empty, true_or]
    · simp only [hem, false_or] at h
      obtain ⟨I₀, hi, ⟨f, hm⟩⟩ := h
      right
      refine ⟨Finset.image f J, Matroid.Indep.subset hi ((BijOn.image_eq hm.1) ▸ ?_), ⟨f, ?_, ?_⟩⟩
      · simp only [Finset.coe_image, image_subset_iff]
        exact subset_trans hJ (subset_preimage_image _ _)
      · simp only [Finset.coe_image]
        exact BijOn.subset_left hm.1 hJ
      · refine fun v hv ↦ hm.2 v (hJ hv)

/-- The union of a finite indexed family of matroids on a common ground set
(Nash-Williams 1966 / Edmonds): realized as the bipartite-matching adjunction
`adjMap` applied to the direct sum `sum'`. -/
protected def Union [DecidableEq α] (Ms : ι → Matroid α) : Matroid α :=
  (Matroid.sum' Ms).adjMap (fun x y ↦ x.2 = y) univ

/-- The binary union of two matroids, as a `Matroid.Union` over `Bool`. -/
protected def union [DecidableEq α] (M : Matroid α) (N : Matroid α) : Matroid α :=
  Matroid.Union (Bool.rec M N)

@[simp] lemma Union_empty [DecidableEq α] [IsEmpty ι] (Ms : ι → Matroid α) :
    Matroid.Union Ms = loopyOn univ := by
  classical
  -- With `ι` empty, the matching target type `ι × α` is empty, so the only
  -- finite independent set of the `adjMap` is `∅`; finitarity lifts this to all
  -- independent sets.
  haveI : IsEmpty (ι × α) := by infer_instance
  rw [Matroid.Union, eq_loopyOn_iff]
  refine ⟨adjMap_ground_eq .., fun X _ hX ↦ ?_⟩
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
  -- the singleton `{x}` is a finite independent subset, hence `AdjIndep`-matchable
  have hxI : ((Matroid.sum' Ms).adjMap (fun a b ↦ a.2 = b) univ).Indep {x} :=
    hX.subset (by simpa using hx)
  rw [show ({x} : Set α) = (({x} : Finset α) : Set α) by simp,
    adjMap_indep_iff] at hxI
  obtain (h | ⟨I₀, f, _, hm⟩) := hxI.1
  · simp at h
  · -- `IsMatching` gives `BijOn f ↑{x} ↑I₀` with `I₀ : Finset (ι × α)` empty,
    -- so `↑{x} = ∅` by `bijOn_empty_iff_left`, contradiction.
    have hI₀ : (I₀ : Set (ι × α)) = ∅ := by simp [Finset.eq_empty_of_isEmpty I₀]
    have := Set.bijOn_empty_iff_left.mp (hI₀ ▸ hm.bijOn)
    simp at this

/-- Disjointification: any indexed family of sets admits a pairwise-disjoint
shrinking with the same union. (Revival of the commented-out
`Matroid.ForMathlib.Set` lemma `exists_pairwiseDisjoint_iUnion_eq`.) -/
private lemma exists_pairwiseDisjoint_iUnion_eq (s : ι → Set α) :
    ∃ t : ι → Set α, Pairwise (Disjoint on t) ∧ ⋃ i, t i = ⋃ i, s i ∧ ∀ i, t i ⊆ s i := by
  classical
  choose f hf using show ∀ x ∈ ⋃ i, s i, ∃ i, x ∈ s i by simp
  use fun i ↦ {x ∈ s i | ∃ (h : x ∈ s i), f x (mem_iUnion_of_mem i h) = i}
  refine ⟨fun i j hij ↦ Set.disjoint_left.2 ?_,
    subset_antisymm (iUnion_mono <| fun _ _ h ↦ h.1) ?_,
    fun i ↦ by simp only [sep_subset]⟩
  · simp only [mem_setOf_eq, not_and, not_exists, and_imp, forall_exists_index]
    exact fun a _ hfa hfi _ hfj haj ↦ hij <| by rw [← hfi, haj]
  · simp only [iUnion_subset_iff]
    exact fun i x hxi ↦ mem_iUnion.2 ⟨f x (mem_iUnion_of_mem i hxi), by simp [hf x _]⟩

lemma union_indep_aux [DecidableEq α] [Finite α] {Ms : ι → Matroid α} {I : Set α}
    (hI : (Matroid.Union Ms).Indep I) :
    ∃ Is : ι → Set α, ⋃ (i : ι), Is i = (I : Set α) ∧ ∀ (i : ι), (Ms i).Indep (Is i) := by
    simp only [Matroid.Union, adjMap_indep_iff', AdjIndep', sum'_indep_iff, exists_and_left,
    subset_univ, and_true] at hI
    obtain heq | hne := eq_or_ne I ∅
    · refine ⟨(fun _ ↦ ∅), by simp only [iUnion_empty, heq, empty_indep, implies_true,
        and_self]⟩
    · simp only [hne, false_or] at hI
      obtain ⟨I', h, ⟨f, hB, hAdj⟩⟩ := hI
      refine ⟨(fun i ↦ (Prod.mk i ⁻¹' I') : ι → Set α), (BijOn.image_eq hB) ▸ ?_, h⟩
      refine subset_antisymm (fun v hv ↦ ?_) (fun v hv ↦ ?_)
      · simp only [mem_iUnion, mem_preimage, mem_image] at hv
        obtain ⟨i, x, hx, h⟩ := hv
        specialize hAdj x hx
        simp only [h ▸ hAdj ▸ hx]
      · specialize hAdj v hv
        simp only [mem_iUnion, mem_preimage, mem_image]
        refine ⟨(f v).1, v, hv, ?_⟩
        nth_rw 3 [← hAdj]

lemma union_indep_aux' [DecidableEq α] [Finite α] {Ms : ι → Matroid α} {I : Set α} (Is : ι → Set α)
  (hI : ⋃ (i : ι), Is i = (I : Set α) ∧ ∀ (i : ι), (Ms i).Indep (Is i)) :
    (Matroid.Union Ms).Indep I := by
    obtain ⟨Is, hD, hIs, hsub⟩ := exists_pairwiseDisjoint_iUnion_eq Is
    obtain hD := Pairwise.pairwiseDisjoint hD univ
    have hI : ⋃ i, Is i = I ∧ ∀ (i : ι), (Ms i).Indep (Is i) :=
      ⟨hIs ▸ hI.1, fun i ↦ Matroid.Indep.subset (hI.2 i) (hsub i)⟩
    obtain hα | hα := isEmpty_or_nonempty α
    · simp [eq_empty_of_isEmpty I]
    obtain hι | hι := isEmpty_or_nonempty ι
    · simp only [Union_empty, loopyOn_indep_iff]
      simpa [iUnion_of_empty, IsEmpty.forall_iff, and_true] using Eq.symm hI.1
    simp only [Matroid.Union, adjMap_indep_iff', AdjIndep', subset_univ, and_true]
    obtain rfl | h := eq_or_ne I ∅
    · simp only [true_or]
    · simp only [h, exists_and_left, false_or, sum'_indep_iff]
      refine ⟨{(i, v) | (i ∈ univ) ∧ v ∈ Is i}, fun i ↦ ?_, ?_⟩
      · simp only [mem_univ, true_and, preimage_setOf_eq, setOf_mem_eq, hI.2 i]
      simp_rw [IsMatching, mem_univ, true_and]
      set f := fun x : ι × α ↦ x.2 with hf
      have himage : I = f '' {x : ι × α | x.2 ∈ Is x.1} := by
        rw [← hI.1]
        simp_all only [ne_eq, f]
        obtain ⟨left, _⟩ := hI
        subst left
        simp_all only [iUnion_eq_empty, not_forall]
        ext1 x
        simp_all only [mem_iUnion, mem_image, mem_setOf_eq, Prod.exists, exists_eq_right]
      have hinj: InjOn f {x : ι × α | x.2 ∈ Is x.1} := by
        refine fun x hx y hy hxy ↦ ?_
        simp only [hf] at hxy
        simp only [mem_setOf_eq] at hx hy
        obtain h := PairwiseDisjoint.elim_set hD (mem_univ x.1)
          (mem_univ y.1) x.2 hx (hxy ▸ hy)
        obtain ⟨_, _⟩ := x
        obtain ⟨_, _⟩ := y
        simp_all only
      obtain h := himage ▸ InjOn.bijOn_image hinj
      refine ⟨Function.invFunOn f {x | x.2 ∈ Is x.1},
        BijOn.symm (InvOn.symm (BijOn.invOn_invFunOn h)) h, fun v hv ↦ ?_⟩
      simp only [show (Function.invFunOn f {x | x.2 ∈ Is x.1} v).2 =
        f (Function.invFunOn f {x | x.2 ∈ Is x.1} v) by rfl, Function.invFunOn_eq (himage ▸ hv)]

/-- Independence in the union of an indexed family (Nash-Williams 1966 /
Edmonds): a set is independent iff it decomposes as a union of sets, one
independent in each factor. -/
lemma union_indep_iff [DecidableEq α] [Finite α] {Ms : ι → Matroid α} {I : Set α} :
    (Matroid.Union Ms).Indep I ↔
    ∃ Is : ι → Set α, ⋃ i, Is i = (I : Set α) ∧ ∀ i, (Ms i).Indep (Is i) := by
    refine Iff.intro union_indep_aux (fun ⟨Is, hI⟩ ↦ union_indep_aux' Is hI)

/-- Independence in the binary union: a set is independent iff it splits as
`I₁ ∪ I₂` with `Iⱼ` independent in `Mⱼ`. -/
lemma union_indep_iff' [DecidableEq α] [Finite α] {M₁ : Matroid α} {M₂ : Matroid α}
  {I : Set α} :
  (Matroid.union M₁ M₂).Indep I ↔ ∃ I₁ I₂, I = I₁ ∪ I₂ ∧ M₁.Indep I₁ ∧ M₂.Indep I₂ := by
  simp only [Matroid.union, union_indep_iff, Bool.forall_bool, union_eq_iUnion]
  refine Iff.intro (fun ⟨Is, hI, hI1, hI2⟩ ↦ ⟨Is false, Is true, hI ▸ ?_, hI1, hI2⟩)
    (fun ⟨I₁, I₂, hI, hI1, hI2⟩ ↦ ⟨fun i ↦ bif i then I₂ else I₁, hI ▸ ?_, hI1, hI2⟩)
  · ext1 x
    simp only [mem_iUnion, Bool.exists_bool, cond_false, cond_true]
    tauto
  · ext1 x
    simp only [mem_iUnion, Bool.exists_bool, cond_false, cond_true]
    tauto

end Matroid
