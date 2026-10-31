/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Cut
public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.EarData
public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Stars
public import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.Short

/-!
# The step at four or more interior bodies of an open ear, in every dimension

The graph-combinatorics and rank leaves of the steps `thm:pencil-d-open-ear-four` and its relatives
(`blueprint/src/chapter/pencil-d.tex`, `sec:pencil-d-short`).

* `Graph.exists_earBase_splitOff_grade`: the base data of the steps at three and four or more
  interior bodies, `Graph.exists_earBase_splitOff` with `m` heights (the grade forms of the
  ear data, of lifting an ear's heights column by column, and of the rank congruences).
* `splitOff_ear_succAbove`: suppressing the second interior body `x 1` of an ear with `k + 3`
  interior bodies and relinking `e 1` to `x 0 − x 2` leaves an ear on `V₁` with `k + 2` interior
  bodies; `splitOff_ear_four` and `splitOff_ear_three` at every length.
-/

@[expose] public section

namespace CombinatorialRigidity.Molecular

open scoped Graph

variable {K : Type*} [Field K] {α β : Type*} {m : ℕ}

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

/-! ## The base data, in every dimension -/

open Classical in
/-- The base data of the steps at three and four or more interior bodies, with `m` heights:
`Graph.exists_earBase_splitOff` at grade `m + 1`. -/
theorem _root_.Graph.exists_earBase_splitOff_grade [Infinite K] [Finite α] {G : Graph α β}
    {V₁ : Set α} {v u w : α} {e₀ : β} {k : ℕ} {y : Fin k → α} {a b : α} {e : Fin (k + 1) → β}
    (hk : 2 ≤ k) (hcover : V(G.splitOff v u w e₀) = V₁ ∪ Set.range y)
    (hinj : Function.Injective y) (hyV₁ : ∀ i, y i ∉ V₁) (ha : a ∈ V₁) (hb : b ∈ V₁)
    (hab : a ≠ b)
    (hpath : ∀ i : Fin (k + 1), (G.splitOff v u w e₀).IsLink (e i)
      (pathVertex a y b i.castSucc) (pathVertex a y b i.succ))
    (hsep : ∀ f p p', (G.splitOff v u w e₀).IsLink f p p' → (∀ i, f ≠ e i) →
      p ∈ V₁ ∧ p' ∈ V₁)
    (hl₀ : (G.splitOff v u w e₀).IsLink e₀ u w)
    (he₀ : ∀ p p', G.IsLink e₀ p p' → p ∉ V₁ ∨ p' ∉ V₁)
    (hind : (G.splitOff v u w e₀).induce V₁ = G.induce V₁)
    {ends : β → α × α} (hends : ∀ f p p', G.IsLink f p p' → G.IsLink f (ends f).1 (ends f).2)
    {xf xl : α} {X : Set α} (hxf : xf ∈ (G.splitOff v u w e₀).closedNbhd a)
    (hxl : xl ∈ (G.splitOff v u w e₀).closedNbhd b) (hX : Set.range y ⊆ X)
    (h₁ : (G.induce V₁).X0AttainsGrade K m) (h₂ : (G.splitOff v u w e₀).X0AttainsGrade K m)
    {Pm : MvPolynomial (α × Fin 2) K} (hPm : Pm ≠ 0) :
    ∃ (q : α × Fin 2 → K) (z₁ : α × Fin m → K) (la lb : Fin m → Fin 3 → K)
      (s₁ : (α × Fin 2) ⊕ (α × Fin m) → K) (ρ : Submodule K (ScrewSpace K (m + 1))),
      MvPolynomial.eval q Pm ≠ 0 ∧ (G.splitOff v u w e₀).IsAdmissiblePicture q ∧
      earPictureGrade V₁ q s₁ = q ∧
      (Module.finrank K ↥(Submodule.span K (PanelHingeFramework.ofNormals (k := m + 1)
          (G.splitOff v u w e₀) (Function.update ends e₀ (u, w))
          (earConfigGrade V₁ q z₁ xf xl X la lb s₁)).toBodyHinge.rigidityRows) : ℤ) =
        screwDim (m + 1) * ((V(G.splitOff v u w e₀).ncard : ℤ) - 1) -
          (G.splitOff v u w e₀).deficiency (m + 2) ∧
      (∀ f, (G.splitOff v u w e₀).IsLink f (Function.update ends e₀ (u, w) f).1
          (Function.update ends e₀ (u, w) f).2 →
        (PanelHingeFramework.ofNormals (k := m + 1) (G.splitOff v u w e₀)
          (Function.update ends e₀ (u, w))
          (earConfigGrade V₁ q z₁ xf xl X la lb s₁)).toBodyHinge.supportExtensor f ≠ 0) ∧
      (∀ s : (α × Fin 2) ⊕ (α × Fin m) → K,
        z₁ ∈ (G.induce V₁).liftingSpaceGrade (earPictureGrade V₁ q s) m) ∧
      (∀ (s : (α × Fin 2) ⊕ (α × Fin m) → K) i, ∀ p ∈ (G.induce V₁).closedNbhd a,
        z₁ (p, i) = la i ⬝ᵥ pencilPicturePoint (earPictureGrade V₁ q s) p) ∧
      (∀ (s : (α × Fin 2) ⊕ (α × Fin m) → K) i, ∀ p ∈ (G.induce V₁).closedNbhd b,
        z₁ (p, i) = lb i ⬝ᵥ pencilPicturePoint (earPictureGrade V₁ q s) p) ∧
      (∀ s, (⟨G.induce V₁, (PanelHingeFramework.ofNormals (k := m + 1) G ends
          (earConfigGrade V₁ q z₁ xf xl X la lb s)).toBodyHinge.supportExtensor⟩ :
            BodyHingeFramework K (m + 1) α β).relScrews a b = ρ) ∧
      (∀ s, (⟨(G.splitOff v u w e₀).induce V₁, (PanelHingeFramework.ofNormals (k := m + 1)
          (G.splitOff v u w e₀) (Function.update ends e₀ (u, w))
          (earConfigGrade V₁ q z₁ xf xl X la lb s)).toBodyHinge.supportExtensor⟩ :
            BodyHingeFramework K (m + 1) α β).relScrews a b = ρ) ∧
      (∀ s, (Module.finrank K ↥(Submodule.span K (⟨G.induce V₁,
          (PanelHingeFramework.ofNormals (k := m + 1) G ends
            (earConfigGrade V₁ q z₁ xf xl X la lb s)).toBodyHinge.supportExtensor⟩ :
              BodyHingeFramework K (m + 1) α β).rigidityRows) : ℤ) =
        screwDim (m + 1) * ((V₁.ncard : ℤ) - 1) - (G.induce V₁).deficiency (m + 2)) ∧
      (∀ s, (Module.finrank K ↥(Submodule.span K (⟨(G.splitOff v u w e₀).induce V₁,
          (PanelHingeFramework.ofNormals (k := m + 1) (G.splitOff v u w e₀)
            (Function.update ends e₀ (u, w))
            (earConfigGrade V₁ q z₁ xf xl X la lb s)).toBodyHinge.supportExtensor⟩ :
              BodyHingeFramework K (m + 1) α β).rigidityRows) : ℤ) =
        screwDim (m + 1) * ((V₁.ncard : ℤ) - 1) - (G.induce V₁).deficiency (m + 2)) := by
  set H := G.splitOff v u w e₀ with hH
  have hle : G.induce V₁ ≤ H := hind ▸ Graph.induce_le (hcover ▸ Set.subset_union_left)
  set ends'' := Function.update ends e₀ (u, w) with hends''def
  have hendsG := PanelHingeFramework.recordsLinks_iff_forall_isLink.mpr hends
  have hends'' : ∀ f p p', H.IsLink f p p' → H.IsLink f (ends'' f).1 (ends'' f).2 :=
    fun _ _ _ => (hendsG.update_splitOff hl₀).isLink
  have hendsI := PanelHingeFramework.recordsLinks_iff_forall_isLink.mp (hendsG.induce V₁)
  have hnot : ∀ f p p', (G.induce V₁).IsLink f p p' → f ≠ e₀ := by
    rintro f p p' ⟨hf, hp, hp'⟩ rfl
    rcases he₀ p p' hf with h | h
    exacts [h hp, h hp']
  -- the picture `q*`, generic for `X₀(G[V₁])` and `X₀(H)`, off `Pm`
  obtain ⟨ends₁, P₁, hends₁, hP₁, hgood₁⟩ := h₁
  obtain ⟨ends₂, P₂, hends₂, hP₂, hgood₂⟩ := h₂
  obtain ⟨q', hq'⟩ := MvPolynomial.exists_eval_ne_zero (mul_ne_zero (mul_ne_zero hP₁ hP₂) hPm)
  rw [map_mul, map_mul] at hq'
  obtain ⟨-, R₁, ⟨z₁', hz₁', hR₁'⟩, hatt₁⟩ :=
    hgood₁ q' (left_ne_zero_of_mul (left_ne_zero_of_mul hq'))
  obtain ⟨hadm₂, R₂, ⟨z₂', hz₂', hR₂'⟩, hatt₂⟩ :=
    hgood₂ q' (right_ne_zero_of_mul (left_ne_zero_of_mul hq'))
  -- the heights `z*`: in `L_H(q*)^m`, attaining for `H` and, restricted, for `G[V₁]`
  have hex₁ : ∃ z ∈ H.liftingSpaceGrade q' m,
      MvPolynomial.eval z (restrictPoly (Prod.fst ⁻¹' V₁) R₁) ≠ 0 := by
    rw [← hind] at hz₁'
    obtain ⟨z, hz, hzr⟩ := Graph.exists_liftingRestrict_preimage_fst_eq (X := V₁)
      (fun y hy => by
        obtain ⟨z, hz, hzr, -⟩ :=
          H.earExtend_mem_liftingSpace hk hcover hinj hyV₁ ha hb hab hpath hsep hadm₂ hy 0
        exact ⟨z, hz, hzr⟩) hz₁'
    exact ⟨z, hz, by rwa [eval_restrictPoly, hzr]⟩
  obtain ⟨zs, hzs, hzs₁, hzs₂⟩ := MvPolynomial.exists_mem_eval_ne_zero₂ hex₁ ⟨z₂', hz₂', hR₂'⟩
  rw [eval_restrictPoly] at hzs₁
  set z₁ := Graph.liftingRestrict (Prod.fst ⁻¹' V₁) zs with hz₁def
  have hz₁ : z₁ ∈ (G.induce V₁).liftingSpaceGrade q' m :=
    Graph.liftingRestrict_mem_liftingSpaceGrade hle hzs
  have hr₁ := hatt₁ z₁ hz₁ hzs₁
  have hr₂ := hatt₂ zs hzs hzs₂
  -- the planes at `a` and `b`
  choose la hla using fun i => (Graph.mem_liftingSpaceGrade.1 hzs i).2 a (hcover ▸ Or.inl ha)
  choose lb hlb using fun i => (Graph.mem_liftingSpaceGrade.1 hzs i).2 b (hcover ▸ Or.inl hb)
  -- the ear datum `s* = (q*, z*)`
  set cfg := earConfigGrade V₁ q' z₁ xf xl X la lb with hcfgdef
  set sstar : (α × Fin 2) ⊕ (α × Fin m) → K := Sum.elim q' zs with hsstar
  have hpicstar : earPictureGrade V₁ q' sstar = q' := by
    funext p; by_cases hp : p.1 ∈ V₁ <;> simp [earPictureGrade, hp, hsstar]
  have hzstar : earHeightGrade V₁ z₁ xf xl X la lb q' (fun p => sstar (Sum.inr p)) = zs := by
    funext ⟨p, i⟩
    simp only [earHeightGrade, earHeight, hsstar, Sum.elim_inr]
    split_ifs with h1 h2 h3 h4
    · simp [hz₁def, Graph.liftingRestrict_apply, h1]
    · subst h2; exact (hla i _ hxf).symm
    · subst h3; exact (hlb i _ hxl).symm
    · rfl
    · refine ((Graph.mem_liftingSpaceGrade.1 hzs i).1 p ?_).symm
      rw [hcover]
      rintro (h | h)
      exacts [h1 h, h4 (hX h)]
  have hcfgstar : cfg sstar = fun p => pencilConfigPointGrade q' zs p.1 p.2 := by
    funext p
    change pencilConfigPointGrade (earPictureGrade V₁ q' sstar) (earHeightGrade V₁ z₁ xf xl X la
      lb (earPictureGrade V₁ q' sstar) (fun p => sstar (Sum.inr p))) p.1 p.2 = _
    rw [hpicstar, hzstar]
  -- what the frameworks along the ear data read on `V₁`
  have hcV₁ : ∀ s p, p ∈ V₁ → ∀ j, cfg s (p, j) = pencilConfigPointGrade q' z₁ p j :=
    fun s p hp j => earConfigGrade_of_mem s hp j
  have hCG : ∀ s f p p', (G.induce V₁).IsLink f p p' →
      (PanelHingeFramework.ofNormals (k := m + 1) G ends (cfg s)).toBodyHinge.supportExtensor f =
        (PanelHingeFramework.ofNormals (k := m + 1) G ends
          (cfg sstar)).toBodyHinge.supportExtensor f := by
    intro s f p p' hf
    obtain ⟨-, h1, h2⟩ := hendsI f p p' hf
    simp only [PanelHingeFramework.toBodyHinge_supportExtensor,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_ends]
    congr 1 <;> funext j
    · rw [hcV₁ _ _ h1, hcV₁ _ _ h1]
    · rw [hcV₁ _ _ h2, hcV₁ _ _ h2]
  have hC2 : ∀ s f p p', (G.induce V₁).IsLink f p p' →
      (PanelHingeFramework.ofNormals (k := m + 1) H ends'' (cfg s)).toBodyHinge.supportExtensor
          f =
        (PanelHingeFramework.ofNormals (k := m + 1) G ends
          (cfg s)).toBodyHinge.supportExtensor f := by
    intro s f p p' hf
    simp only [PanelHingeFramework.toBodyHinge_supportExtensor,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_ends, hends''def,
      Function.update_of_ne (hnot f p p' hf)]
  have hrk₁ : ∀ s, (Module.finrank K ↥(Submodule.span K (⟨G.induce V₁,
      (PanelHingeFramework.ofNormals (k := m + 1) G ends (cfg s)).toBodyHinge.supportExtensor⟩ :
        BodyHingeFramework K (m + 1) α β).rigidityRows) : ℤ) =
        screwDim (m + 1) * ((V₁.ncard : ℤ) - 1) - (G.induce V₁).deficiency (m + 2) := by
    intro s
    rw [BodyHingeFramework.finrank_span_rigidityRows_congr (G.induce V₁) (hCG s)]
    have := PanelHingeFramework.finrank_span_rigidityRows_ofNormals_congr (k := m + 1)
      (G.induce V₁) hendsI hends₁ (q := cfg sstar)
      (q' := fun p => pencilConfigPointGrade q' z₁ p.1 p.2)
      (fun w hw j => hcV₁ sstar w hw j)
    change (Module.finrank K ↥(Submodule.span K (PanelHingeFramework.ofNormals (k := m + 1)
      (G.induce V₁) ends (cfg sstar)).toBodyHinge.rigidityRows) : ℤ) = _
    rw [this, hr₁]
    rfl
  have hpp : ∀ s : (α × Fin 2) ⊕ (α × Fin m) → K, ∀ p ∈ V₁,
      pencilPicturePoint (earPictureGrade V₁ q' s) p = pencilPicturePoint q' p := by
    intro s p hp; funext i
    fin_cases i <;> simp [pencilPicturePoint, earPictureGrade_of_mem s hp]
  refine ⟨q', z₁, la, lb, sstar,
    (⟨G.induce V₁, (PanelHingeFramework.ofNormals (k := m + 1) G ends
      (cfg sstar)).toBodyHinge.supportExtensor⟩ : BodyHingeFramework K (m + 1) α β).relScrews a b,
    right_ne_zero_of_mul hq', hadm₂, hpicstar, ?_, ?_, fun s => ?_, fun s i p hp => ?_,
    fun s i p hp => ?_, fun s => BodyHingeFramework.relScrews_congr (G.induce V₁) (hCG s) a b,
    fun s => ?_, hrk₁, fun s => ?_⟩
  · rw [← hcfgdef, hcfgstar, PanelHingeFramework.finrank_span_rigidityRows_ofNormals_congr
      (k := m + 1) H hends'' hends₂ (fun _ _ _ => rfl)]
    exact hr₂
  · rw [← hcfgdef, hcfgstar]
    exact fun f hf => hadm₂.supportExtensor_ne_zero_grade hends'' zs hf
  · rw [Graph.mem_liftingSpaceGrade] at hz₁ ⊢
    intro i
    rw [Graph.liftingSpace_congr (G := G.induce V₁) (q := earPictureGrade V₁ q' s) (q' := q')
      (fun w hw i => earPictureGrade_of_mem (m := m) s hw i)]
    exact hz₁ i
  · have hpV : p ∈ V₁ := Graph.closedNbhd_subset_vertexSet ha hp
    have hp'' : p ∈ H.closedNbhd a := by
      rcases hp with rfl | ⟨f, hf⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨f, hf.of_le hle⟩
    rw [hpp s p hpV, ← hla i p hp'']
    simp [hz₁def, Graph.liftingRestrict_apply, hpV]
  · have hpV : p ∈ V₁ := Graph.closedNbhd_subset_vertexSet hb hp
    have hp'' : p ∈ H.closedNbhd b := by
      rcases hp with rfl | ⟨f, hf⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨f, hf.of_le hle⟩
    rw [hpp s p hpV, ← hlb i p hp'']
    simp [hz₁def, Graph.liftingRestrict_apply, hpV]
  · rw [hind]
    exact BodyHingeFramework.relScrews_congr (G.induce V₁)
      (fun f p p' hf => (hC2 s f p p' hf).trans (hCG s f p p' hf)) a b
  · rw [hind, BodyHingeFramework.finrank_span_rigidityRows_congr (G.induce V₁) (hC2 s)]
    exact hrk₁ s

/-! ## The factoring through `G″`, in every dimension -/

/-- **The complement isomorphism, as the polarity from joins to screws**:
`complementIso : ⋀² K^(k+2) ≃ ⋀^k K^(k+2)` with target `ScrewSpace K k` (the form
`screwComplementIso` takes at every grade). -/
noncomputable def complementScrew (K : Type*) [Field K] (k : ℕ) :
    ⋀[K]^2 (Fin (k + 2) → K) ≃ₗ[K] ScrewSpace K k :=
  complementIso (k := k) (j := 2) (by omega)

/-- **The hinges of `ofNormals` along a family of links are the polar images of the joins**
(`span_supportExtensor_comp_eq_map_pointJoin` at every grade): the span of the hinges at the labels
`g i`, linking `u i` to `w i`, is the image under `complementScrew` of the span of the joins
`c (u i, ·) ∧ c (w i, ·)`. Each hinge is `±` the polar image of the join at its recorded ends
(`panelSupportExtensor`, `panelSupportExtensor_swap`). -/
theorem span_supportExtensor_comp_eq_map_normalsJoin {k : ℕ} {H : Graph α β} {ends : β → α × α}
    (hends : ∀ f u w, H.IsLink f u w → H.IsLink f (ends f).1 (ends f).2)
    (c : α × Fin (k + 2) → K) {ι : Type*} (g : ι → β) (u w : ι → α)
    (hg : ∀ i, H.IsLink (g i) (u i) (w i)) :
    Submodule.span K (Set.range ((PanelHingeFramework.ofNormals (k := k) H ends
        c).toBodyHinge.supportExtensor ∘ g)) =
      (Submodule.span K (Set.range fun i =>
        normalsJoin (fun j => c (u i, j)) (fun j => c (w i, j)))).map
          (complementScrew K k).toLinearMap := by
  rw [Submodule.map_span, ← Set.range_comp]
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
  · rintro _ ⟨i, rfl⟩
    have hbase : panelSupportExtensor (fun j => c (u i, j)) (fun j => c (w i, j)) ∈
        Submodule.span K (Set.range ((complementScrew K k).toLinearMap ∘
          fun i => normalsJoin (fun j => c (u i, j)) (fun j => c (w i, j)))) :=
      Submodule.subset_span ⟨i, rfl⟩
    have h := span_supportExtensor_ofNormals_eq hends c (hg i)
    have h1 := Submodule.mem_span_singleton_self (R := K)
      ((PanelHingeFramework.ofNormals (k := k) H ends c).toBodyHinge.supportExtensor (g i))
    rw [h] at h1
    exact (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hbase)) h1
  · rintro _ ⟨i, rfl⟩
    have h := span_supportExtensor_ofNormals_eq hends c (hg i)
    have h1 := Submodule.mem_span_singleton_self (R := K)
      (panelSupportExtensor (fun j => c (u i, j)) (fun j => c (w i, j)))
    rw [← h] at h1
    exact Submodule.span_mono (Set.singleton_subset_iff.mpr
      (Set.mem_range_self (f := (PanelHingeFramework.ofNormals (k := k) H ends
        c).toBodyHinge.supportExtensor ∘ g) i)) h1

/-- **`dim(ρ + ι Λ) = dim(ι⁻¹ ρ + Λ)`** for the polarity `ι = complementScrew`
(`finrank_sup_map_screwComplementIso` at every grade). -/
theorem finrank_sup_map_complementScrew {k : ℕ} (ρ : Submodule K (ScrewSpace K k))
    (Λ : Submodule K (⋀[K]^2 (Fin (k + 2) → K))) :
    Module.finrank K ↥(ρ ⊔ Λ.map (complementScrew K k).toLinearMap) =
      Module.finrank K ↥(ρ.map (complementScrew K k).symm.toLinearMap ⊔ Λ) := by
  have hΛ : (Λ.map (complementScrew K k).toLinearMap).map
      (complementScrew K k).symm.toLinearMap = Λ := by
    rw [← Submodule.map_comp]
    simp
  rw [← LinearEquiv.finrank_map_eq (complementScrew K k).symm, Submodule.map_sup, hΛ]

open Classical in
/-- `Graph.X0Attains.of_openEar_splitOff` at grade `m + 1`: the steps at three and at four or more
interior bodies, given that the suppressed body `v` can be put back off a polynomial in the ear
data, with `D = screwDim (m + 1)` for `6`. The subspace `ρ` of `hins` lies in `⋀²`, the space of
the joins. -/
theorem _root_.Graph.X0AttainsGrade.of_openEar_splitOff [Infinite K] [Finite α] [Finite β]
    {G : Graph α β} (hG : G.IsX0Graph) {V₁ : Set α} {k : ℕ} (hk : 2 ≤ k)
    {x : Fin (k + 1) → α} {a b : α} {e : Fin (k + 2) → β} (hcover : V(G) = V₁ ∪ Set.range x)
    (hinj : Function.Injective x) (hxV₁ : ∀ i, x i ∉ V₁) (ha : a ∈ V₁) (hb : b ∈ V₁)
    (hab : a ≠ b)
    (hpath : ∀ i : Fin (k + 2),
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (hsep : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁)
    {v u w : α} {e₀ : β} {y : Fin k → α} {e'' : Fin (k + 1) → β}
    (hcover'' : V(G.splitOff v u w e₀) = V₁ ∪ Set.range y) (hinj'' : Function.Injective y)
    (hyV₁ : ∀ i, y i ∉ V₁)
    (hpath'' : ∀ i : Fin (k + 1), (G.splitOff v u w e₀).IsLink (e'' i)
      (pathVertex a y b i.castSucc) (pathVertex a y b i.succ))
    (hsep'' : ∀ f p p', (G.splitOff v u w e₀).IsLink f p p' → (∀ i, f ≠ e'' i) →
      p ∈ V₁ ∧ p' ∈ V₁)
    (hyx : Set.range y ⊆ Set.range x) (hv : v ∈ Set.range x) (hu : u ∉ V₁)
    (hl₀ : G.IsLink e₀ u v) (hl₀'' : (G.splitOff v u w e₀).IsLink e₀ u w)
    (hdef : (G.splitOff v u w e₀).deficiency (m + 2) ≤ G.deficiency (m + 2)) {xf xl : α}
    (hxf : x ⟨0, by omega⟩ = xf) (hxl : x ⟨k, by omega⟩ = xl) (hvf : v ≠ xf) (hvl : v ≠ xl)
    (hins : ∀ (q : α × Fin 2 → K) (z : α × Fin m → K) (la lb : Fin m → Fin 3 → K)
      (ρ : Submodule K (⋀[K]^2 (Fin (m + 1 + 2) → K))),
      (∀ i, z (a, i) = la i ⬝ᵥ pencilPicturePoint q a) →
      (∀ i, z (b, i) = lb i ⬝ᵥ pencilPicturePoint q b) →
      ∃ Q : MvPolynomial ((α × Fin 2) ⊕ (α × Fin m)) K, Q ≠ 0 ∧ ∀ s, MvPolynomial.eval s Q ≠ 0 →
        (G.splitOff v u w e₀).IsAdmissiblePicture (earPictureGrade V₁ q s) →
        ∃ x₂ : Fin (m + 1 + 2) → K, x₂ (Fin.last (m + 2)) = 1 ∧
          ∀ p : α → Fin (m + 1 + 2) → K, p v = x₂ →
          (∀ t, t ≠ v → p t = fun j => earConfigGrade V₁ q z xf xl (Set.range x) la lb s (t, j)) →
          min (Module.finrank K ↥(ρ ⊔ Submodule.span K (Set.range fun i : Fin (k + 1) =>
            normalsJoin (fun j => earConfigGrade V₁ q z xf xl (Set.range x) la lb s
                (pathVertex a y b i.castSucc, j))
              (fun j => earConfigGrade V₁ q z xf xl (Set.range x) la lb s
                (pathVertex a y b i.succ, j)))) + 1) (screwDim (m + 1)) ≤
          Module.finrank K ↥(ρ ⊔ Submodule.span K (Set.range fun i : Fin (k + 2) =>
            normalsJoin (p (pathVertex a x b i.castSucc)) (p (pathVertex a x b i.succ)))))
    (h₁ : (G.induce V₁).X0AttainsGrade K m) (h₂ : (G.splitOff v u w e₀).X0AttainsGrade K m) :
    G.X0AttainsGrade K m := by
  have hV : V(G).Nonempty := hG.connected.nonempty
  have : Inhabited α := ⟨a⟩
  have hvV₁ : v ∉ V₁ := by obtain ⟨i, rfl⟩ := hv; exact hxV₁ i
  set G'' := G.splitOff v u w e₀
  have he₀ : ∀ p p', G.IsLink e₀ p p' → p ∉ V₁ ∨ p' ∉ V₁ := fun p p' h => by
    rcases h.eq_and_eq_or_eq_and_eq hl₀ with ⟨-, rfl⟩ | ⟨rfl, -⟩
    exacts [Or.inr hvV₁, Or.inl hvV₁]
  obtain ⟨-, hind⟩ := induce_splitOff_ear hcover hxV₁ hv hu he₀
  -- the first and the last edge of the ear avoid `v`, so they stay links of `G″`
  have hkeep : ∀ f p y, G.IsLink f p y → p ∈ V₁ → v ≠ y → y ∈ G''.closedNbhd p := by
    intro f p y hf hp hvy
    refine Or.inr ⟨f, Or.inl ⟨fun h => ?_, hf, fun h => hvV₁ (h ▸ hp), fun h => hvy h.symm⟩⟩
    rw [h] at hf
    rcases hf.eq_and_eq_or_eq_and_eq hl₀ with ⟨-, h'⟩ | ⟨h', -⟩
    exacts [hvy h'.symm, hvV₁ (h' ▸ hp)]
  -- the main polynomial of `G`, the selectors, and the base data
  obtain ⟨Pm, hPm, hmain⟩ := G.exists_mvPolynomial_isMainPicture (K := K)
    hG.simple.toLoopless hG.three_le_ncard_closedNbhd
  set ends := G.endsOf
  have hends : ∀ f p p', G.IsLink f p p' → G.IsLink f (ends f).1 (ends f).2 :=
    fun f _ _ hf => G.isLink_endsOf hf.edge_mem
  set ends'' := Function.update ends e₀ (u, w)
  have hends'' : ∀ f p p', G''.IsLink f p p' → G''.IsLink f (ends'' f).1 (ends'' f).2 :=
    fun _ _ _ =>
      ((PanelHingeFramework.recordsLinks_iff_forall_isLink.mpr hends).update_splitOff hl₀'').isLink
  obtain ⟨q', z₁, la, lb, sstar, ρM, hqm', hadm₂, hpicstar, hrk₂, hne₂, hz₁s, hlas, hlbs, hρG,
      hρ2, hrk₁, hrk₁''⟩ :=
    Graph.exists_earBase_splitOff_grade hk hcover'' hinj'' hyV₁ ha hb hab hpath'' hsep'' hl₀'' he₀
      hind hends (hkeep _ _ _ (hxf ▸ ear_isLink_first hpath (by omega)) ha hvf)
      (hkeep _ _ _ (hxl ▸ (ear_isLink_last hpath (by omega)).symm) hb hvl) hyx h₁ h₂ hPm
  set ρJ := ρM.map (complementScrew K (m + 1)).symm.toLinearMap with hρJ
  -- the insertion hypothesis, a polynomial condition on the ear data
  obtain ⟨Qx, hQx₀, hQx⟩ := hins q' z₁ la lb ρJ
    (fun i => by have := hlas sstar i a (Or.inl rfl); rwa [hpicstar] at this)
    (fun i => by have := hlbs sstar i b (Or.inl rfl); rwa [hpicstar] at this)
  set cfg := earConfigGrade V₁ q' z₁ xf xl (Set.range x) la lb
  set P := earPointPolyGrade V₁ q' z₁ xf xl (Set.range x) la lb
  have hPc : ∀ s p, MvPolynomial.eval s (P p) = cfg s p :=
    eval_earPointPolyGrade V₁ q' z₁ xf xl (Set.range x) la lb
  have hPc' : ∀ s, (fun p => MvPolynomial.eval s (P p)) = cfg s := fun s => funext (hPc s)
  have hfam : ∀ s {ι : Type} (u' w' : ι → α),
      (fun i => normalsJoin (fun j => MvPolynomial.eval s (P (u' i, j)))
        (fun j => MvPolynomial.eval s (P (w' i, j)))) =
      fun i => normalsJoin (fun j => cfg s (u' i, j)) (fun j => cfg s (w' i, j)) :=
    fun s _ u' w' => funext fun i => by simp only [hPc]
  -- the rank and admissibility conditions on the ear data of `G″`
  set N'' := ((screwDim (m + 1) : ℤ) * ((V(G'').ncard : ℤ) - 1) - G''.deficiency (m + 2)).toNat
  have hN'' : N'' ≤ Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals
      (k := m + 1) G'' ends''
        (fun p => MvPolynomial.eval sstar (P p))).toBodyHinge.rigidityRows) := by
    rw [hPc']
    exact Int.toNat_le.mpr hrk₂.symm.le
  have hne'' : ∀ f, G''.IsLink f (ends'' f).1 (ends'' f).2 →
      (PanelHingeFramework.ofNormals (k := m + 1) G'' ends''
        (fun p => MvPolynomial.eval sstar (P p))).toBodyHinge.supportExtensor f ≠ 0 := by
    rw [hPc']
    exact hne₂
  obtain ⟨Q₂, hQ₂₀, hQ₂⟩ := exists_mvPolynomial_le_finrank_ofNormals_bind_grade G'' ends''
    hends'' P hne'' hN''
  obtain ⟨Pa, hPa₀, hPa⟩ := hadm₂.exists_mvPolynomial
  have hPa'₀ : MvPolynomial.eval sstar (MvPolynomial.bind₁ (earPicturePolyGrade V₁ q') Pa) ≠ 0 := by
    rwa [eval_bind₁_earPicturePolyGrade, hpicstar]
  have hne0 : ∀ {Q : MvPolynomial ((α × Fin 2) ⊕ (α × Fin m)) K} {s},
      MvPolynomial.eval s Q ≠ 0 → Q ≠ 0 :=
    fun h hQ => h (by rw [hQ, map_zero])
  -- the ear data of `G″`: a common non-root `sy` of the three
  obtain ⟨sy, hsy₂, hsya, hsyx⟩ := MvPolynomial.exists_eval_ne_zero₃ (hne0 hQ₂₀) (hne0 hPa'₀)
    hQx₀
  have hrank'' := hQ₂ sy hsy₂
  rw [hPc'] at hrank''
  rw [eval_bind₁_earPicturePolyGrade] at hsya
  have hadmy := hPa _ hsya
  -- the counts
  have hcard : ∀ {k : ℕ} {z : Fin k → α} {H : Graph α β}, V(H) = V₁ ∪ Set.range z →
      Function.Injective z → (∀ i, z i ∉ V₁) → (V(H).ncard : ℤ) = V₁.ncard + k :=
    fun hc hi hz => by rw [hc]; exact_mod_cast Set.ncard_union_range_of_injective hi hz
  set f₁ := (G.induce V₁).deficiency (m + 2)
  have hD := three_le_screwDim_succ (m := m)
  have hdefG := Graph.deficiency_induce_add_le_of_ear (n := m + 2)
    (by rw [Graph.bodyBarDim_add_one_eq_screwDim]; omega) (by omega) hcover hinj
    hxV₁ ha hb hpath hsep
  have hbb : (Graph.bodyBarDim (m + 2) : ℤ) = screwDim (m + 1) := by
    exact_mod_cast Graph.bodyBarDim_add_one_eq_screwDim (m + 1)
  rw [hbb] at hdefG
  -- the ear rank law at `G″`: `dim W ≥ k + f − def(G″)`
  have hC'' : ∀ i, (PanelHingeFramework.ofNormals (k := m + 1) G'' ends''
      (cfg sy)).toBodyHinge.supportExtensor (e'' i) ≠ 0 :=
    fun i => hadmy.supportExtensor_ne_zero_grade hends''
      (earHeightGrade V₁ z₁ xf xl (Set.range x) la lb (earPictureGrade V₁ q' sy)
        (fun p => sy (Sum.inr p))) (hpath'' i)
  have hear'' := BodyHingeFramework.finrank_span_rigidityRows_ear_eq
    (PanelHingeFramework.ofNormals (k := m + 1) G'' ends'' (cfg sy)).toBodyHinge hinj'' hyV₁ ha hb
    hab hpath'' hsep'' hC''
  rw [PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph] at hear''
  rw [hrk₁'' sy, hρ2 sy, span_supportExtensor_comp_eq_map_normalsJoin hends'' (cfg sy) e''
    (fun i => pathVertex a y b i.castSucc) (fun i => pathVertex a y b i.succ) hpath'',
    finrank_sup_map_complementScrew, ← hρJ] at hear''
  have hW := (Int.self_le_toNat _).trans (Int.ofNat_le.mpr hrank'')
  rw [hear'', hcard hcover'' hinj'' hyV₁] at hW
  -- put `v` back at `x₂`
  obtain ⟨x₂, hx₂1, hins'⟩ := hQx sy hsyx hadmy
  set st : (α × Fin 2) ⊕ (α × Fin m) → K := Sum.elim
    (fun p => if p.1 = v then ![x₂ 0, x₂ 1] p.2 else sy (Sum.inl p))
    (fun p => if p.1 = v then gradeHeights x₂ p.2 else sy (Sum.inr p)) with hst
  have hlt := hins' (fun t j => cfg st (t, j))
    (by
      have h := earConfigGrade_of_mem_X (V₁ := V₁) (q₁ := q') (z₁ := z₁) (la := la) (lb := lb)
        (X := Set.range x) st hvV₁ hvf hvl hv
      refine h.trans ?_
      conv_rhs => rw [gradeMk_eta x₂, hx₂1]
      refine gradeMk_ext ?_ ?_ ?_ rfl
      · simp [hst]
      · simp [hst]
      · funext i; simp [hst])
    (fun t ht => funext fun j => earConfigGrade_congr (fun i => by simp [hst, ht])
      (fun i => by simp [hst, ht]) j)
  -- the target `n₀ = k + 2 + f − def(G)` is met at `st`
  set n₀ := ((k : ℤ) + 2 + f₁ - G.deficiency (m + 2)).toNat
  have hNt : n₀ ≤ Module.finrank K ↥(ρJ ⊔ Submodule.span K (Set.range fun i : Fin (k + 2) =>
      normalsJoin (fun j => MvPolynomial.eval st (P (pathVertex a x b i.castSucc, j)))
        (fun j => MvPolynomial.eval st (P (pathVertex a x b i.succ, j))))) := by
    rw [hfam]
    refine le_trans (le_min_iff.mpr ⟨Int.toNat_le.mpr ?_, Int.toNat_le.mpr ?_⟩) hlt
    · push_cast
      linarith
    · push_cast at hdefG ⊢
      linarith
  obtain ⟨Qs, hQs₀, hQs⟩ := exists_mvPolynomial_le_finrank_sup_span_normalsJoin ρJ P
    (fun i : Fin (k + 2) => pathVertex a x b i.castSucc) (fun i => pathVertex a x b i.succ) hNt
  have hPm'₀ : MvPolynomial.eval sstar (MvPolynomial.bind₁ (earPicturePolyGrade V₁ q') Pm) ≠ 0 := by
    rwa [eval_bind₁_earPicturePolyGrade, hpicstar]
  -- the ear data of `G`: a common non-root `s₀`, main for `G`
  obtain ⟨s₀, hs₀a, hs₀b⟩ := MvPolynomial.exists_eval_ne_zero₂ (hne0 hQs₀) (hne0 hPm'₀)
  rw [eval_bind₁_earPicturePolyGrade] at hs₀b
  have hqmain₀ := hmain _ hs₀b
  have hz₀ : earHeightGrade V₁ z₁ xf xl (Set.range x) la lb (earPictureGrade V₁ q' s₀)
      (fun t => s₀ (Sum.inr t)) ∈ G.liftingSpaceGrade (earPictureGrade V₁ q' s₀) m := by
    subst hxf hxl
    exact Graph.earHeightGrade_mem_liftingSpaceGrade (by omega) hcover hinj hxV₁ ha hb hab hpath
      hsep hqmain₀.1 (hz₁s s₀) (hlas s₀) (hlbs s₀) _
  -- the ear rank law at `G`
  have hC : ∀ i, (PanelHingeFramework.ofNormals (k := m + 1) G ends
      (cfg s₀)).toBodyHinge.supportExtensor (e i) ≠ 0 :=
    fun i => hqmain₀.1.supportExtensor_ne_zero_grade hends
      (earHeightGrade V₁ z₁ xf xl (Set.range x) la lb (earPictureGrade V₁ q' s₀)
        (fun p => s₀ (Sum.inr p))) (hpath i)
  have hear := BodyHingeFramework.finrank_span_rigidityRows_ear_eq
    (PanelHingeFramework.ofNormals (k := m + 1) G ends (cfg s₀)).toBodyHinge hinj hxV₁ ha hb hab
    hpath hsep hC
  rw [PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph] at hear
  rw [hrk₁ s₀, hρG s₀, span_supportExtensor_comp_eq_map_normalsJoin hends (cfg s₀) e
    (fun i => pathVertex a x b i.castSucc) (fun i => pathVertex a x b i.succ) hpath,
    finrank_sup_map_complementScrew, ← hρJ] at hear
  have hspan₀ := hQs s₀ hs₀a
  rw [hfam] at hspan₀
  refine Graph.x0AttainsGrade_of_exists hV ends hends hqmain₀ hz₀ ?_
  change _ ≤ (Module.finrank K ↥(Submodule.span K (PanelHingeFramework.ofNormals (k := m + 1) G
    ends (cfg s₀)).toBodyHinge.rigidityRows) : ℤ)
  rw [hear, hcard hcover hinj hxV₁]
  have h₀ : (k : ℤ) + 2 + f₁ - G.deficiency (m + 2) ≤ (n₀ : ℤ) := Int.self_le_toNat _
  have h₁ := Int.ofNat_le.mpr hspan₀
  push_cast at h₁ ⊢
  linarith



end CombinatorialRigidity.Molecular
