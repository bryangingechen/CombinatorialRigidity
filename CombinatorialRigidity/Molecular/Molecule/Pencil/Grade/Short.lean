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

end CombinatorialRigidity.Molecular
