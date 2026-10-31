/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Stars
public import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.Short

/-!
# The step at four or more interior bodies of an open ear, in every dimension

The graph-combinatorics and rank leaves of the steps `thm:pencil-d-open-ear-four` and its relatives
(`blueprint/src/chapter/pencil-d.tex`, `sec:pencil-d-short`).

* `splitOff_ear_succAbove`: suppressing the second interior body `x 1` of an ear with `k + 3`
  interior bodies and relinking `e 1` to `x 0 − x 2` leaves an ear on `V₁` with `k + 2` interior
  bodies; `splitOff_ear_four` and `splitOff_ear_three` at every length.
-/

@[expose] public section

namespace CombinatorialRigidity.Molecular

open scoped Graph

variable {α β : Type*}

/-! ## Suppressing the second interior body, at every ear length -/

/-- The value of `Fin.succAbove 2`. -/
theorem coe_succAbove_two {n : ℕ} (j : Fin (n + 3)) :
    ((2 : Fin (n + 4)).succAbove j : ℕ) = if (j : ℕ) < 2 then (j : ℕ) else (j : ℕ) + 1 := by
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_two]
  split_ifs <;> simp_all [Fin.val_succ]

/-- The value of `Fin.succAbove 1`. -/
theorem coe_succAbove_one {n : ℕ} (j : Fin (n + 2)) :
    ((1 : Fin (n + 3)).succAbove j : ℕ) = if (j : ℕ) < 1 then (j : ℕ) else (j : ℕ) + 1 := by
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_one]
  split_ifs <;> simp_all [Fin.val_succ]

/-- Removing the second interior body from the path sequence: `pathVertex a (x ∘ succAbove 1) b j`
is `pathVertex a x b (succAbove 2 j)`. -/
theorem pathVertex_comp_succAbove_one {k : ℕ} (a b : α) (x : Fin (k + 3) → α) (j : Fin (k + 4)) :
    pathVertex a (x ∘ Fin.succAbove 1) b j = pathVertex a x b (Fin.succAbove 2 j) := by
  rcases pathVertex_cases a (x ∘ Fin.succAbove 1) b j with ⟨h, h'⟩ | ⟨i, h, h'⟩ | ⟨h, h'⟩
  · have hj : j = 0 := Fin.ext h
    subst hj
    rw [h']
    have : (Fin.succAbove 2 (0 : Fin (k + 4)) : Fin (k + 5)) = 0 := by
      rw [Fin.ext_iff, coe_succAbove_two]; simp
    rw [this, pathVertex_zero]
  · rw [h', pathVertex_eq_of_val_eq a b x (i := Fin.succAbove 1 i)]
    · rfl
    · rw [coe_succAbove_two]
      rw [coe_succAbove_one]
      split_ifs <;> omega
  · have hj : j = Fin.last _ := Fin.ext (by simpa using h)
    subst hj
    have : (Fin.succAbove 2 (Fin.last (k + 3)) : Fin (k + 5)) = Fin.last (k + 4) := by
      rw [Fin.ext_iff, coe_succAbove_two]; simp
    rw [h', this, pathVertex_last]

/-- **Suppressing the second interior body of an ear** (a step of `thm:pencil-d-open-ear-four`):
suppressing `x 1` of an ear with `k + 3` interior bodies and relinking `e 1` to `x 0 − x 2` leaves
the ear `a − x ∘ succAbove 1 − b` on `V₁`, with the labels `e ∘ succAbove 2`; and `x 1` has degree
two. (`splitOff_ear_four` and `splitOff_ear_three` at every length.) -/
theorem splitOff_ear_succAbove {G : Graph α β} {V₁ : Set α} {k : ℕ} {x : Fin (k + 3) → α}
    {a b : α} {e : Fin (k + 4) → β} (hcover : V(G) = V₁ ∪ Set.range x)
    (hinj : Function.Injective x) (hxV₁ : ∀ i, x i ∉ V₁) (ha : a ∈ V₁) (hb : b ∈ V₁) (hab : a ≠ b)
    (hpath : ∀ i : Fin (k + 4),
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (hsep : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁) :
    V(G.splitOff (x 1) (x 0) (x 2) (e 1)) = V₁ ∪ Set.range (x ∘ Fin.succAbove 1) ∧
      Function.Injective (x ∘ Fin.succAbove 1) ∧ (∀ i, (x ∘ Fin.succAbove 1) i ∉ V₁) ∧
      (∀ i : Fin (k + 3), (G.splitOff (x 1) (x 0) (x 2) (e 1)).IsLink ((e ∘ Fin.succAbove 2) i)
        (pathVertex a (x ∘ Fin.succAbove 1) b i.castSucc)
        (pathVertex a (x ∘ Fin.succAbove 1) b i.succ)) ∧
      (∀ f u w, (G.splitOff (x 1) (x 0) (x 2) (e 1)).IsLink f u w →
        (∀ i, f ≠ (e ∘ Fin.succAbove 2) i) → u ∈ V₁ ∧ w ∈ V₁) ∧
      (∀ e' y, G.IsLink e' (x 1) y → e' = e 1 ∨ e' = e 2) := by
  have hax : ∀ i, x i ≠ a := fun i h => hxV₁ i (h ▸ ha)
  have hbx : ∀ i, x i ≠ b := fun i h => hxV₁ i (h ▸ hb)
  have he := pathEdge_injective hinj hax hbx hab hpath
  have hx : ∀ i j, i ≠ j → x i ≠ x j := fun i j h h' => h (hinj h')
  -- only the position of value `2` of the path sequence is `x 1`
  have hne : ∀ idx : Fin (k + 5), (idx : ℕ) ≠ 2 → pathVertex a x b idx ≠ x 1 := by
    intro idx hidx h
    rcases pathVertex_cases a x b idx with ⟨_, h'⟩ | ⟨i, hi, h'⟩ | ⟨_, h'⟩
    · exact hxV₁ 1 (by rw [← h, h']; exact ha)
    · have : i = 1 := hinj (h' ▸ h)
      subst this
      exact hidx (by simpa using hi)
    · exact hxV₁ 1 (by rw [← h, h']; exact hb)
  have l1 : G.IsLink (e 1) (x 0) (x 1) := by
    have := hpath 1
    rwa [pathVertex_eq_of_val_eq a b x (i := 0) (by simp),
      pathVertex_eq_of_val_eq a b x (i := 1) (by simp)] at this
  have l2 : G.IsLink (e 2) (x 1) (x 2) := by
    have := hpath 2
    rwa [pathVertex_eq_of_val_eq a b x (i := 1)
        (by simp only [Fin.val_castSucc, Fin.val_two, Fin.val_one]),
      pathVertex_eq_of_val_eq a b x (i := 2) (by simp only [Fin.val_succ, Fin.val_two])] at this
  have x01 := hx 0 1 Fin.zero_ne_one
  have x21 := hx 2 1 (fun h => by
    have := congrArg Fin.val h
    simp only [Fin.val_two, Fin.val_one] at this
    omega)
  have s2 : (Fin.succAbove 2 (1 : Fin (k + 3)) : Fin (k + 4)) = 1 :=
    Fin.ext (by rw [coe_succAbove_two]; simp)
  refine ⟨?_, hinj.comp (Fin.succAbove_right_injective), fun i => hxV₁ _, ?_, ?_, ?_⟩
  · ext w
    simp only [Graph.vertexSet_splitOff, hcover, Set.mem_sdiff, Set.mem_union, Set.mem_range,
      Set.mem_singleton_iff, Function.comp]
    constructor
    · rintro ⟨h | ⟨i, rfl⟩, hw⟩
      · exact Or.inl h
      · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq (fun h => hw (h ▸ rfl) : i ≠ 1)
        exact Or.inr ⟨j, rfl⟩
    · rintro (h | ⟨j, rfl⟩)
      · exact ⟨Or.inl h, fun h' => hxV₁ 1 (h' ▸ h)⟩
      · exact ⟨Or.inr ⟨_, rfl⟩, fun h => Fin.succAbove_ne _ _ (hinj h)⟩
  · intro i
    simp only [Function.comp, pathVertex_comp_succAbove_one]
    by_cases hi1 : (i : ℕ) = 1
    · have hi : i = 1 := Fin.ext hi1
      subst hi
      have c1 : (Fin.succAbove 2 (Fin.castSucc (1 : Fin (k + 3))) : Fin (k + 5)) = 1 :=
        Fin.ext (by
          rw [coe_succAbove_two]
          simp only [Fin.val_castSucc, Fin.val_one]
          norm_num)
      have c2 : (Fin.succAbove 2 (Fin.succ (1 : Fin (k + 3))) : Fin (k + 5)) = Fin.succ 2 :=
        Fin.ext (by
          rw [coe_succAbove_two]
          simp only [Fin.val_succ, Fin.val_one, Fin.val_two]
          norm_num)
      rw [s2, c1, c2,
        pathVertex_eq_of_val_eq a b x (i := 0) (by simp only [Fin.val_one, Fin.val_zero]),
        pathVertex_eq_of_val_eq a b x (i := 2) (by simp only [Fin.val_succ, Fin.val_two])]
      exact Or.inr ⟨rfl, x01, x21, l1.left_mem, l2.right_mem, Or.inl ⟨rfl, rfl⟩⟩
    · have hc : Fin.castSucc (Fin.succAbove 2 i) = Fin.succAbove 2 (Fin.castSucc i) :=
        Fin.ext (by simp only [Fin.val_castSucc, coe_succAbove_two])
      have hs : Fin.succ (Fin.succAbove 2 i) = Fin.succAbove 2 (Fin.succ i) :=
        Fin.ext (by
          simp only [Fin.val_succ, coe_succAbove_two]
          split_ifs <;> omega)
      have hl := hpath (Fin.succAbove 2 i)
      rw [hc, hs] at hl
      refine Or.inl ⟨fun h => ?_, hl, hne _ ?_, hne _ ?_⟩
      · have := congrArg Fin.val (he h)
        rw [coe_succAbove_two, Fin.val_one] at this
        split_ifs at this <;> omega
      · rw [coe_succAbove_two]
        simp only [Fin.val_castSucc]
        split_ifs <;> omega
      · rw [coe_succAbove_two]
        simp only [Fin.val_succ]
        split_ifs <;> omega
  · intro f u w hf hfe
    rcases hf with ⟨hne', hf, hu, hw⟩ | ⟨rfl, -⟩
    · refine hsep f u w hf (fun j => ?_)
      by_cases hj1 : j = 1
      · exact hj1 ▸ hne'
      by_cases hj2 : j = 2
      · subst hj2
        rintro rfl
        rcases hf.eq_and_eq_or_eq_and_eq l2 with ⟨h, -⟩ | ⟨-, h⟩
        · exact hu h
        · exact hw h
      · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hj2
        exact hfe i
    · exact absurd (by simp [s2]) (hfe 1)
  · intro e' y h
    by_cases hall : ∀ j, e' ≠ e j
    · exact absurd ((hsep e' _ _ h hall).1) (hxV₁ 1)
    · push Not at hall
      obtain ⟨j, rfl⟩ := hall
      by_contra hcon
      push Not at hcon
      have hj1 : j ≠ 1 := fun h' => hcon.1 (h' ▸ rfl)
      have hj2 : j ≠ 2 := fun h' => hcon.2 (h' ▸ rfl)
      have v1 : ((Fin.castSucc j : Fin (k + 5)) : ℕ) ≠ 2 := fun h' =>
        hj2 (Fin.ext (by rw [Fin.val_two]; simpa using h'))
      have v2 : ((Fin.succ j : Fin (k + 5)) : ℕ) ≠ 2 := fun h' =>
        hj1 (Fin.ext (by rw [Fin.val_one]; rw [Fin.val_succ] at h'; omega))
      rcases (hpath j).eq_and_eq_or_eq_and_eq h with ⟨h', -⟩ | ⟨-, h'⟩
      · exact hne _ v1 h'
      · exact hne _ v2 h'

end CombinatorialRigidity.Molecular
