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
* This file ports the matroid-union *construction* and its independence
  characterizations (`Matroid.Union`, `Matroid.union`, `union_indep_iff`,
  `union_indep_iff'`), together with the polymatroid-of-adjMap bridge
  (`polymatroid_of_adjMap`), the rank-distribution lemmas over `Matroid.sum'`,
  and Edmonds' matroid-partition rank formula (`matroid_partition'` /
  `matroid_partition_eRk'`).
-/
import Matroid.Constructions.Matching
import Matroid.Rank.Nat
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
* `Matroid.polymatroid_of_adjMap` — the `adjMap`-matroid is realized as the
  matroid of the polymatroid rank function `f Y = M.rk {v | ∃ u ∈ Y, Adj v u}`.
* `Matroid.matroid_partition'` / `Matroid.matroid_partition_eRk'` — Edmonds'
  matroid-partition rank formula for the (binary) union
  (`thm:matroid-partition-rank`).
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

/-- The neighbourhood of a single right-vertex `v` under `Adj`. -/
def N_singleton (Adj : α → β → Prop) (v : β) := {u | Adj u v}

/-- The neighbourhood of a set of right-vertices `V` under `Adj`. -/
def N (Adj : α → β → Prop) (V : Set β) := {u | ∃ v ∈ V, Adj u v}

/-- The matroid `M.adjMap Adj univ` is the matroid of the polymatroid rank
function `f Y = r_M (N Adj Y)`; this is the polymatroid-of-submodular
realization of the matching matroid (the longest single proof of the port, the
sufficiency direction routes through Rado's theorem `Matroid.rado`). -/
theorem polymatroid_of_adjMap [DecidableEq β] [Finite α] [Finite β] (M : Matroid α)
  (Adj : α → β → Prop) : ∃ f, ∃ h : (PolymatroidFn f), ofPolymatroidFn h = M.adjMap Adj univ ∧
  ∀ Y, f Y = M.rk {v | ∃ u ∈ Y, Adj v u} := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  haveI : Fintype β := Fintype.ofFinite β
  obtain hα | hα := isEmpty_or_nonempty α
  · refine ⟨fun _ : Finset β ↦ (0 : ℤ), PolymatroidFn_of_zero, ext_indep rfl
      (fun J _ ↦ ?_), ?_⟩
    · have heq : ∀ I : Finset β, (ofPolymatroidFn PolymatroidFn_of_zero).Indep (I : Set β) ↔
        (M.adjMap Adj univ).Indep I := by
        simp only [indep_ofPolymatroidFn_iff, Int.natCast_nonpos_iff, Finset.card_eq_zero,
          adjMap_indep_iff', subset_univ, and_true, AdjIndep', Finset.coe_eq_empty, exists_and_left]
        refine fun I ↦ Iff.intro (fun hI ↦ ?_) (fun hI ↦ ?_)
        · obtain rfl | h := eq_or_ne I ∅
          · simp only [Finset.coe_empty, true_or]
          · simp only [h, false_or]
            absurd hI
            simp only [not_forall]
            exact ⟨I, subset_rfl, Finset.nonempty_of_ne_empty h, h⟩
        · refine fun I' hsub _ ↦ ?_
          obtain rfl | h := eq_or_ne I ∅
          · exact Finset.subset_empty.mp hsub
          · simp only [h, false_or] at hI
            obtain ⟨J, _, ⟨f, hm, _⟩⟩ := hI
            obtain hI := Finset.coe_eq_empty.mp <| bijOn_empty_iff_left.mp
              <| (eq_empty_of_isEmpty J) ▸ hm
            exact Finset.subset_empty.mp <| hI ▸ hsub
      exact coe_toFinset J ▸ (heq J.toFinset)
    · simp only
      intro Y
      simp only [eq_empty_of_isEmpty, M.rk_empty, Nat.cast_zero]
  · set N := fun i ↦ (N_singleton Adj i).toFinset with hN
    set f := fun I : Finset β ↦ (M.rk (I.biUnion N) : ℤ) with hf
    have hf_poly : PolymatroidFn f := by
      refine ⟨fun X Y ↦ hf ▸ ?_, ?_, ?_⟩
      · simp only [Finset.inf_eq_inter, Finset.sup_eq_union]
        have hunion : ((X ∪ Y).biUnion N) = X.biUnion N ∪ Y.biUnion N := by aesop
        rw [← Nat.cast_add, ← Nat.cast_add, Nat.cast_le]
        have hsub : ((X ∩ Y).biUnion N : Set α) ⊆
            (X.biUnion N : Set α) ∩ (Y.biUnion N : Set α) := by
          simp only [Finset.coe_biUnion, Finset.coe_inter, mem_inter_iff, Finset.mem_coe,
            N_singleton, subset_inter_iff, iUnion_subset_iff, and_imp,
            toFinset_setOf, Finset.coe_filter, Finset.mem_univ, true_and, hN]
          refine ⟨fun x h1 _ y h3 ↦ ?_, fun x _ h2 y h3 ↦ ?_⟩
          · simp only [mem_iUnion, mem_setOf_eq, exists_prop]
            exact ⟨x, ⟨h1, h3⟩⟩
          · simp only [mem_iUnion, mem_setOf_eq, exists_prop]
            exact ⟨x, ⟨h2, h3⟩⟩
        calc M.rk ↑((X ∩ Y).biUnion N) + M.rk ↑((X ∪ Y).biUnion N)
            ≤ M.rk ((X.biUnion N : Set α) ∩ (Y.biUnion N : Set α))
              + M.rk ((X.biUnion N : Set α) ∪ (Y.biUnion N : Set α)) := by
              gcongr
              · exact M.rk_mono hsub
              · rw [hunion, Finset.coe_union]
          _ ≤ M.rk ↑(X.biUnion N) + M.rk ↑(Y.biUnion N) := M.rk_submod _ _
      · refine fun X Y h ↦ hf ▸ Nat.cast_le.mpr (M.rk_mono ?_)
        simp only [le_eq_subset, Finset.coe_biUnion, Finset.mem_coe, iUnion_subset_iff]
        refine fun x h1 y h2 ↦ ?_
        simp only [mem_iUnion, exists_prop]
        exact ⟨x, h h1, h2⟩
      · simp only [hf, Finset.bot_eq_empty, Finset.biUnion_empty, Finset.coe_empty, rk_empty,
          Nat.cast_zero]
    have heq : ∀ I : Finset β, (ofPolymatroidFn hf_poly).Indep I ↔ (M.adjMap Adj univ).Indep I := by
      intro I
      simp only [adjMap_indep_iff, indep_ofPolymatroidFn_iff]
      refine iff_def'.mpr ⟨fun ha I' hI' _ ↦ hf ▸ ?_, fun hp ↦ ?_⟩
      · simp only [Nat.cast_le]
        obtain h | _ := ha.1
        · obtain h := Finset.subset_empty.mp (h ▸ hI')
          simp only [h, Finset.card_empty, Finset.biUnion_empty, Finset.coe_empty, rk_empty,
            le_refl]
        · obtain h | ⟨I₀, f, h', h''⟩ := (AdjIndep.subset ha.1 hI')
          · simp only [h, Finset.card_empty, Finset.biUnion_empty, Finset.coe_empty, rk_empty,
              le_refl]
          · obtain h := IsMatching.card_eq h''
            rw [← h, ← ncard_coe_finset I₀, ← Indep.rk_eq_ncard h']
            apply rk_mono
            refine fun x hx ↦ mem_setOf_eq ▸ ?_
            rw [← BijOn.image_eq (IsMatching.bijOn h''), image, mem_setOf_eq] at hx
            obtain ⟨u, hu, hadj⟩ := hx
            simp only [← Finset.mem_def, Finset.mem_biUnion, N_singleton, hN]
            refine ⟨u, hu, ?_⟩
            simp only [toFinset_setOf, Finset.mem_filter,
              Finset.mem_univ, true_and]
            exact hadj ▸ (IsMatching.adj h'' hu)
      obtain h := (rado M <| fun i : ↑I ↦ (N_singleton Adj i).toFinset).mpr
      simp only [hf, Nat.cast_le] at hp
      have hp : ∀ I' ⊆ I, I'.card ≤ M.rk ↑(I'.biUnion N) := by
        intro I' hI'
        obtain rfl | hem := eq_or_ne I' ∅
        · simp only [Finset.card_empty, Finset.biUnion_empty, Finset.coe_empty, rk_empty, le_refl]
        · exact hp I' hI' <| Finset.nonempty_of_ne_empty hem
      have : ∀ (K : Finset { x // x ∈ I }), K.card ≤
        M.rk ↑(K.biUnion fun i ↦ (N_singleton Adj ↑i).toFinset) := by
        intro K
        have hsub : Finset.image Subtype.val K ⊆ I := by
          refine fun x hx ↦ ?_
          simp only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right] at hx
          exact hx.1
        have : (Finset.image Subtype.val K).card = K.card := by
          simp [Finset.card_image_iff.mpr injOn_subtype_val]
        specialize hp (Finset.image Subtype.val K) hsub
        simp only [this] at hp
        refine le_trans hp (le_of_eq ?_)
        apply congrArg
        apply congrArg
        exact Finset.image_biUnion
      obtain ⟨e, ⟨hinj, hin⟩, hi⟩ := h this
      refine ⟨?_, subset_univ _⟩
      simp only [AdjIndep, exists_and_left]
      obtain rfl | hem := eq_or_ne I ∅
      · simp only [Finset.coe_empty, true_or]
      · simp only [hem, false_or]
        set e' := fun x ↦ if h : x ∈ I then e ⟨x, h⟩ else Classical.arbitrary α with he'
        refine ⟨(range e).toFinset, (coe_toFinset (range e)).symm ▸ hi, ⟨e', ⟨⟨fun x hx ↦ ?_,
          fun x hx y hy hxy ↦ ?_, fun x hx ↦ ?_⟩, ?_⟩⟩⟩
        · simp only [Finset.mem_coe] at hx
          simp only [hx, toFinset_range, Finset.univ_eq_attach, Finset.coe_image, mem_image,
            Finset.mem_coe, Finset.mem_attach, true_and, Subtype.exists, e']
          refine ⟨x, hx, by simp only [↓reduceDIte]⟩
        · simp only [Finset.mem_coe] at hx hy
          simp only [hx, ↓reduceDIte, hy, e'] at hxy
          exact Subtype.mk_eq_mk.mp (hinj hxy)
        · simp only [mem_image, Finset.mem_coe, e']
          simp only [toFinset_range, Finset.univ_eq_attach, Finset.coe_image, mem_image,
            Finset.mem_coe, Finset.mem_attach, true_and, Subtype.exists] at hx
          obtain ⟨a, b, hab⟩ := hx
          refine ⟨a, b, by simp only [b, ↓reduceDIte, hab]⟩
        · intro v hv
          simp only [Finset.mem_coe] at hv
          specialize hin ⟨v, hv⟩
          simp only [N_singleton, toFinset_setOf, Finset.mem_filter,
            Finset.mem_univ, true_and] at hin
          simp only [hv, ↓reduceDIte, e', hin]
    have h_eq' : (ofPolymatroidFn hf_poly) = M.adjMap Adj univ := by
      refine ext_indep rfl (fun J _ ↦ ?_)
      simpa using heq J.toFinset
    have : ∀ Y, f Y = M.rk {v | ∃ u ∈ Y, Adj v u} := by
      intro Y
      simp only [N_singleton, toFinset_setOf, Finset.coe_biUnion, Finset.mem_coe,
        Finset.coe_filter, Finset.mem_univ, true_and, Nat.cast_inj, f, N]
      have : (⋃ x ∈ Y, {x_2 | Adj x_2 x}) = {v | ∃ u ∈ Y, Adj v u} := by
        refine subset_antisymm (fun x ↦ ?_) (fun x ↦ ?_)
        · simp only [mem_iUnion, mem_setOf_eq, exists_prop, imp_self]
        · simp only [mem_setOf_eq, mem_iUnion, exists_prop, imp_self]
      rw [this]
    exact ⟨f, hf_poly, h_eq', this⟩

theorem sum'_eRk_eq_eRk_sum_on_indep {α ι : Type*} [Fintype ι] [Finite α]
  {Ms : ι → Matroid α} {I : Set (ι × α)} (h : (Matroid.sum' Ms).Indep I) :
  (Matroid.sum' Ms).eRk I = ∑ i : ι, (Ms i).eRk (Prod.mk i ⁻¹' I) := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  rw [Indep.eRk_eq_encard h]
  simp only [sum'_indep_iff] at h
  simp_rw [Indep.eRk_eq_encard (h _)]
  set f := fun x : ι × α ↦ x.1
  rw [← Finite.cast_ncard_eq I.toFinite, I.ncard_eq_toFinset_card']
  rw [Finset.card_eq_sum_card_fiberwise (by refine fun x _ ↦ Finset.mem_univ (f x))]
  have himage : ∀ i : ι, (fun x : ι × α ↦ x.2) '' (Finset.filter (fun x ↦ f x = i) I.toFinset)
    = (Finset.filter (fun v ↦ (i, v) ∈ I) Finset.univ) := by
    refine fun i ↦ subset_antisymm ?_ ?_
    · simp only [Finset.coe_filter, Finset.mem_univ, true_and, image_subset_iff,
        preimage_setOf_eq, setOf_subset_setOf, and_imp, Prod.forall, f]
      refine fun a b h h' ↦ mem_toFinset.mp (h' ▸ h)
    · refine fun x hx ↦ ?_
      simp only [Finset.coe_filter, mem_image, mem_setOf_eq, Prod.exists, exists_eq_right, f]
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, mem_setOf_eq] at hx
      exact mem_toFinset.mpr hx
  have hinj : ∀ i : ι, InjOn (fun x : ι × α ↦ x.2) (Finset.filter (fun x ↦ f x = i) I.toFinset)
    := by
    intro i x hx y hy hxy
    simp only [Finset.coe_filter, mem_setOf_eq, f] at hx hy
    simp only at hxy
    obtain ⟨_, _⟩ := x
    obtain ⟨_, _⟩ := y
    simp_all only
  obtain hcard := fun i : ι ↦ ncard_coe_finset (Finset.filter (fun x_1 ↦ (i, x_1) ∈ I)
    Finset.univ) ▸ ncard_coe_finset (Finset.filter (fun x ↦ f x = i) I.toFinset) ▸ (himage i) ▸
    (hinj i).ncard_image
  simp only [preimage]
  have : ∀ i, {x_1 | (i, x_1) ∈ I}.ncard =
    (Finset.filter (fun x_1 ↦ (i, x_1) ∈ I) Finset.univ).card := by
    intro i
    rw [ncard_eq_toFinset_card']
    simp only [toFinset_setOf]
  simp only [← Finite.cast_ncard_eq {x_1 | (_, x_1) ∈ I}.toFinite, this, hcard, Nat.cast_sum]

@[simp] theorem sum'_eRk_eq_eRk_sum {α ι : Type*} [Fintype ι] [Finite α]
  (Ms : ι → Matroid α) (X : Set (ι × α)) :
  (Matroid.sum' Ms).eRk X = ∑ i : ι, (Ms i).eRk (Prod.mk i ⁻¹' X) := by
  obtain ⟨I, hI⟩ := (Matroid.sum' Ms).exists_isBasis' X
  have : ∀ i : ι, (Ms i).IsBasis' (Prod.mk i ⁻¹' I) (Prod.mk i ⁻¹' X) := by
    intro i
    simp_all only [IsBasis', Maximal, and_imp]
    refine ⟨⟨sum'_indep_iff.mp hI.1.1 i, preimage_mono hI.1.2⟩, fun b hIb h h' ↦ ?_⟩
    have : (∀ (j : ι), (Ms j).Indep (Prod.mk j ⁻¹' (I ∪ (Prod.mk i '' b)))) := by
      intro j
      by_cases h : j = i
      · rw [h, preimage_union]
        exact Matroid.Indep.subset hIb (union_subset h'
          (b.preimage_image_eq (Prod.mk_right_injective i)).subset)
      · have : (Prod.mk j ⁻¹' (Prod.mk i '' b)) = ∅ := by
          refine subset_antisymm (fun x hx ↦ ?_) (empty_subset _)
          simp only [mem_preimage, mem_image, Prod.mk.injEq, exists_eq_right_right] at hx
          simp only [mem_empty_iff_false]
          simp_all only [not_true_eq_false]
        simp only [preimage_union, this, union_empty, sum'_indep_iff.mp hI.1.1 j]
    obtain h'' := hI.2 (sum'_indep_iff.mpr this)
      (union_subset hI.1.2 (subset_trans (image_mono h) (image_preimage_subset _ _)))
      subset_union_left
    exact subset_trans (subset_preimage_image _ _)
      (preimage_mono (union_subset_iff.mp h'').2)
  simp_rw [← IsBasis'.eRk_eq_eRk hI, ← IsBasis'.eRk_eq_eRk (this _)]
  exact sum'_eRk_eq_eRk_sum_on_indep hI.1.1

@[simp] theorem sum'_rk_eq_rk_sum {α ι : Type*} [Fintype ι] [Finite α]
  (Ms : ι → Matroid α) (X : Set (ι × α)) :
  (Matroid.sum' Ms).rk X = ∑ i : ι, (Ms i).rk (Prod.mk i ⁻¹' X) := by
  haveI : Fintype α := Fintype.ofFinite α
  obtain h := sum'_eRk_eq_eRk_sum Ms X
  rw [← Nat.cast_inj (R := ENat)]
  convert h
  · rw [cast_rk_eq]
  · rw [Nat.cast_sum]
    simp_rw [cast_rk_eq]

/-- Edmonds' matroid-partition rank formula in `adjMap` form (Edmonds 1965):
the rank of the `adjMap`-matroid attains `min_Y (r_M (N Adj Y) + |Yᶜ|)`. -/
theorem adjMap_rank_eq [DecidableEq β] [Finite α] [Fintype β] (M : Matroid α)
  (Adj : α → β → Prop) :
  (∃ Y, M.rk {v | ∃ u ∈ Y, Adj v u} + (Finset.univ \ Y).card ≤ (M.adjMap Adj univ).rank) ∧
  (∀ Y, (M.adjMap Adj univ).rank ≤ M.rk {v | ∃ u ∈ Y, Adj v u} + (Finset.univ \ Y).card) := by
  haveI : Fintype α := Fintype.ofFinite α
  obtain ⟨f, hf_poly, heq, hf⟩ := polymatroid_of_adjMap M Adj
  rw [← heq]
  zify
  simp only [← (hf _), rank_def, ofPolymatroidFn_E]
  obtain hpoly := polymatroid_rank_eq hf_poly Finset.univ
  simp only [Finset.subset_univ, Finset.coe_univ, true_and, true_implies] at hpoly
  exact hpoly

/-- Edmonds' matroid-partition rank formula for the binary union (Edmonds 1965):
the rank of `Matroid.union M₁ M₂` attains `min_Y (r_{M₁}(Y) + r_{M₂}(Y) +
|Yᶜ|)`. (`thm:matroid-partition-rank`.) -/
theorem matroid_partition' [DecidableEq α] [Fintype α]
  (M₁ : Matroid α) (M₂ : Matroid α) :
  (∃ Y : Finset α, M₁.rk Y + M₂.rk Y + (Finset.univ \ Y).card ≤ (Matroid.union M₁ M₂).rank) ∧
  (∀ Y : Finset α, (Matroid.union M₁ M₂).rank ≤ M₁.rk Y + M₂.rk Y + (Finset.univ \ Y).card) := by
  simp only [Matroid.union, Matroid.Union]
  obtain ⟨⟨Y, hY⟩, hle⟩ :=
    adjMap_rank_eq (Matroid.sum' fun t ↦ Bool.rec M₁ M₂ t) (fun x y ↦ x.2 = y)
  simp_rw [sum'_rk_eq_rk_sum] at hY hle
  simp only [exists_eq_right', preimage_setOf_eq, Finset.setOf_mem, Fintype.sum_bool] at hY hle
  exact ⟨⟨Y, by omega⟩, fun Y ↦ by have := hle Y; omega⟩

/-- The `eRk`-valued form of Edmonds' matroid-partition rank formula for the
binary union (`thm:matroid-partition-rank`). -/
theorem matroid_partition_eRk' [DecidableEq α] [Finite α]
  (M₁ : Matroid α) (M₂ : Matroid α) : ∃ Y : Set α, M₁.eRk Y + M₂.eRk Y + (univ \ Y).encard =
    (Matroid.union M₁ M₂).eRank := by
  haveI : Fintype α := Fintype.ofFinite α
  obtain ⟨⟨Y, hY⟩, h⟩ := matroid_partition' M₁ M₂
  have : ∀ Y : Finset α, (Finset.univ \ Y).card = (univ \ (Y : Set α)).ncard := by
    intro Y
    rw [← Finset.coe_univ, ← Finset.coe_sdiff, ncard_coe_finset]
  simp_rw [← cast_rk_eq, ← cast_rank_eq,
    ← Finite.cast_ncard_eq (Finite.subset (toFinite univ) (subset_univ _)), ← Nat.cast_add,
    Nat.cast_inj]
  refine ⟨Y, le_antisymm (by simp only [← this _, hY]) (by simp only [← this _, h Y])⟩

/-- Edmonds' matroid-partition rank formula for the union of a finite indexed
family (Edmonds 1965): the rank of `Matroid.Union Ms` attains
`min_Y (∑ᵢ r_{Mᵢ}(Y) + |Yᶜ|)`. The indexed generalization of
`matroid_partition'`, proved by the same `adjMap_rank_eq` + `sum'_rk_eq_rk_sum`
route. (`thm:matroid-partition-rank`.) -/
theorem Union_rank_eq [DecidableEq α] [Fintype α] [Fintype ι] (Ms : ι → Matroid α) :
    (∃ Y : Finset α, (∑ i, (Ms i).rk Y) + (Finset.univ \ Y).card ≤ (Matroid.Union Ms).rank) ∧
    (∀ Y : Finset α, (Matroid.Union Ms).rank ≤ (∑ i, (Ms i).rk Y) + (Finset.univ \ Y).card) := by
  simp only [Matroid.Union]
  obtain ⟨⟨Y, hY⟩, hle⟩ := adjMap_rank_eq (Matroid.sum' Ms) (fun x y ↦ x.2 = y)
  simp_rw [sum'_rk_eq_rk_sum] at hY hle
  simp only [exists_eq_right', preimage_setOf_eq, Finset.setOf_mem] at hY hle
  exact ⟨⟨Y, by convert hY using 3⟩, fun Y ↦ by have := hle Y; convert this using 3⟩

end Matroid
