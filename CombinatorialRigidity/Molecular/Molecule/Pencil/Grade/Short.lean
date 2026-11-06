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
public import CombinatorialRigidity.Molecular.AlgebraicInduction.DeficiencyBound

/-!
# The step at four or more interior bodies of an open ear, in every dimension

The step `thm:pencil-d-open-ear-four` (`blueprint/src/chapter/pencil-d.tex`,
`sec:pencil-d-short`), with the factoring through `G″` it shares with the step at three interior
bodies (which uses the variant `_of_base`).

* `splitOff_ear_succAbove`: suppressing the second interior body `x 1` of an ear with `k + 3`
  interior bodies and relinking `e 1` to `x 0 − x 2` leaves an ear on `V₁` with `k + 2` interior
  bodies; `splitOff_ear_four` and `splitOff_ear_three` at every length.
* `Graph.exists_earBase_splitOff_grade`: the base data of the steps at three and at four or more
  interior bodies, `Graph.exists_earBase_splitOff` with `m` heights (the grade forms of the
  ear data, of lifting an ear's heights column by column, and of the rank congruences), and a
  height polynomial `Rz q` threaded into the choice of the base.
* `joinMotions`, `mem_joinMotions`, `joinRelScrews` and `map_relScrews_ofNormals_eq_joinRelScrews`:
  the motions of a graph at points, in `⋀²`, the relative screws of two vertices (the chapter's
  `ρ`), and their bridge to the hinge framework `ofNormals` through `complementScrew`;
  `joinRelScrews_le_span_of_mem_closedNbhd`: when the closed neighbourhoods of the two vertices
  meet, their relative screws lie in the span of two joins.
* `Graph.X0AttainsGrade.of_openEar_splitOff_of_base`: the step factored through `G″`,
  `Graph.X0Attains.of_openEar_splitOff` at grade `m + 1`, given that the suppressed body can be
  put back (`hins`), asked only at the base data of the first stage and for `G[V₁]`'s own
  `joinRelScrews`. It serves the step at three interior bodies.
* `Graph.X0AttainsGrade.of_openEar_splitOff`: its corollary with `hins` for every `ρ`, `Pq = 1` and
  `Rz = 1`, whose `hins` can be met from four interior bodies on (not at three); the hinges
  become joins through `complementScrew`.
* `starsCond_of_smul` and `span_joins_succAbove_two`: the stars condition is scale invariant, and
  the joins of the ear of `G` are those of the ear of `G″` but one, with the two at the body put
  back, from three interior bodies on (the step at three uses them too).
* `exists_insertion_earDataGrade`: putting the suppressed body back at the ear data
  (`lem:pencil-d-insertion`), for an ear of `G″` with `n + 2` interior bodies; the steps at three
  and at four or more interior bodies both call it.
* `Graph.X0AttainsGrade.of_openEar_four` (`thm:pencil-d-open-ear-four`): the factoring, its `hins`
  discharged by `lem:pencil-d-stars-four`, `lem:pencil-d-ear-data` (3) and `lem:pencil-d-insertion`.

Helpers whose homes are other files, moved with the next commit that edits those files
(`notes/Phase42h.md` *Hand-off*): `span_range_smul_eq` (`notes/FRICTION.md`).
`complementScrew` is in `AlgebraicInduction/PanelLayer.lean`, beside `panelSupportExtensor`.
-/

@[expose] public section

namespace CombinatorialRigidity.Molecular

open scoped Graph Matrix

variable {K : Type*} [Field K] {α β : Type*} {m : ℕ}

/-! ## Suppressing the second interior body, at every ear length -/

/-- The value of `Fin.succAbove 2`. -/
theorem coe_succAbove_two {n : ℕ} (j : Fin (n + 3)) :
    ((2 : Fin (n + 4)).succAbove j : ℕ) = if (j : ℕ) < 2 then (j : ℕ) else (j : ℕ) + 1 := by
  rw [Fin.val_succAbove, Fin.val_two]

/-- The value of `Fin.succAbove 1`. -/
theorem coe_succAbove_one {n : ℕ} (j : Fin (n + 2)) :
    ((1 : Fin (n + 3)).succAbove j : ℕ) = if (j : ℕ) < 1 then (j : ℕ) else (j : ℕ) + 1 := by
  rw [Fin.val_succAbove, Fin.val_one]

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
/-- **The base data of the steps at three and at four or more interior bodies**, with `m` heights:
`Graph.exists_earBase_splitOff` at grade `m + 1` (the grade forms of the ear data, of lifting an
ear's heights column by column, and of the rank congruences), with a height polynomial threaded
in. Given `Rz`, a polynomial in the heights for each admissible picture `q` of `G″` with a
non-root among `G″`'s lifting heights (`hRz`), the base `z*` is chosen off `Rz q*` too, by two
fibre intersections. The conclusion also returns `zs` (the height `z₁` agrees with on `V₁`), in
`L_{G″}(q)^m` with `eval zs (Rz q) ≠ 0`, and the planes `la`, `lb` of `zs` on `G″`'s closed
neighbourhoods of `a`, `b`. -/
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
    {Pm : MvPolynomial (α × Fin 2) K} (hPm : Pm ≠ 0)
    {Rz : (α × Fin 2 → K) → MvPolynomial (α × Fin m) K}
    (hRz : ∀ q, (G.splitOff v u w e₀).IsAdmissiblePicture q →
      ∃ z ∈ (G.splitOff v u w e₀).liftingSpaceGrade q m, MvPolynomial.eval z (Rz q) ≠ 0) :
    ∃ (q : α × Fin 2 → K) (z₁ zs : α × Fin m → K) (la lb : Fin m → Fin 3 → K)
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
        screwDim (m + 1) * ((V₁.ncard : ℤ) - 1) - (G.induce V₁).deficiency (m + 2)) ∧
      zs ∈ (G.splitOff v u w e₀).liftingSpaceGrade q m ∧ MvPolynomial.eval zs (Rz q) ≠ 0 ∧
      (∀ t ∈ V₁, ∀ i, z₁ (t, i) = zs (t, i)) ∧
      (∀ i, ∀ p ∈ (G.splitOff v u w e₀).closedNbhd a,
        zs (p, i) = la i ⬝ᵥ pencilPicturePoint q p) ∧
      (∀ i, ∀ p ∈ (G.splitOff v u w e₀).closedNbhd b,
        zs (p, i) = lb i ⬝ᵥ pencilPicturePoint q p) := by
  set H := G.splitOff v u w e₀ with hH
  have hle : G.induce V₁ ≤ H := hind ▸ Graph.induce_le (hcover ▸ Set.subset_union_left)
  set ends'' := Function.update ends e₀ (u, w) with hends''def
  have hendsG := Graph.recordsLinks_iff_forall_isLink.mpr hends
  have hends'' : ∀ f p p', H.IsLink f p p' → H.IsLink f (ends'' f).1 (ends'' f).2 :=
    fun _ _ _ => (hendsG.update_splitOff hl₀).isLink
  have hendsI := Graph.recordsLinks_iff_forall_isLink.mp (hendsG.induce V₁)
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
  -- `z*` also off `Rz q*`: two applications of the fibre intersection
  obtain ⟨zr, hzr, hzr₂, hzrR⟩ :=
    MvPolynomial.exists_mem_eval_ne_zero₂ ⟨z₂', hz₂', hR₂'⟩ (hRz q' hadm₂)
  obtain ⟨zs, hzs, hzs₁, hzs₂R⟩ := MvPolynomial.exists_mem_eval_ne_zero₂ (p₂ := R₂ * Rz q') hex₁
    ⟨zr, hzr, by rw [map_mul]; exact mul_ne_zero hzr₂ hzrR⟩
  rw [map_mul] at hzs₂R
  have hzs₂ := left_ne_zero_of_mul hzs₂R
  have hzsR := right_ne_zero_of_mul hzs₂R
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
      (G.induce V₁) (hendsG.induce V₁) (Graph.recordsLinks_iff_forall_isLink.mpr hends₁)
      (q := cfg sstar)
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
  refine ⟨q', z₁, zs, la, lb, sstar,
    (⟨G.induce V₁, (PanelHingeFramework.ofNormals (k := m + 1) G ends
      (cfg sstar)).toBodyHinge.supportExtensor⟩ : BodyHingeFramework K (m + 1) α β).relScrews a b,
    right_ne_zero_of_mul hq', hadm₂, hpicstar, ?_, ?_, fun s => ?_, fun s i p hp => ?_,
    fun s i p hp => ?_, fun s => BodyHingeFramework.relScrews_congr (G.induce V₁) (hCG s) a b,
    fun s => ?_, hrk₁, fun s => ?_, hzs, hzsR, fun t ht i => ?_, fun i p hp => hla i p hp,
    fun i p hp => hlb i p hp⟩
  · rw [← hcfgdef, hcfgstar, PanelHingeFramework.finrank_span_rigidityRows_ofNormals_congr
      (k := m + 1) H (hendsG.update_splitOff hl₀) (Graph.recordsLinks_iff_forall_isLink.mpr hends₂)
      (fun _ _ _ => rfl)]
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
  · simp [hz₁def, Graph.liftingRestrict_apply, ht]

/-! ## The factoring through `G″`, in every dimension -/

/-- **The hinges of `ofNormals` along a family of links are the polar images of the joins**
(`span_supportExtensor_comp_eq_map_pointJoin` at every grade): the span of the hinges at the labels
`g i`, linking `u i` to `w i`, is the image under `complementScrew` of the span of the joins
`c (u i, ·) ∧ c (w i, ·)`. Each hinge is the polar image of the join at its recorded ends
(`panelSupportExtensor`), which is `±` that at `u i, w i` (`span_supportExtensor_ofNormals_eq`,
`panelSupportExtensor_swap`). -/
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
    have h := span_supportExtensor_ofNormals_eq (Graph.recordsLinks_iff_forall_isLink.mpr hends) c
      (hg i)
    have h1 := Submodule.mem_span_singleton_self (R := K)
      ((PanelHingeFramework.ofNormals (k := k) H ends c).toBodyHinge.supportExtensor (g i))
    rw [h] at h1
    exact (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hbase)) h1
  · rintro _ ⟨i, rfl⟩
    have h := span_supportExtensor_ofNormals_eq (Graph.recordsLinks_iff_forall_isLink.mpr hends) c
      (hg i)
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

/-! ## The relative screws in `⋀²` (the chapter's `ρ`, `sec:pencil-d-short`) -/

/-- The motions of `H` at the points `c`, in `⋀²` (`sec:pencil-d-short`): the assignments `S` with
`S u − S w ∈ K (c u ∨ c w)` at every link `u w` of `H`. On a graph with no links this is
everything. -/
noncomputable def joinMotions {k : ℕ} (H : Graph α β) (c : α → Fin (k + 2) → K) :
    Submodule K (α → ⋀[K]^2 (Fin (k + 2) → K)) :=
  ⨅ (f : β) (u : α) (w : α) (_ : H.IsLink f u w),
    (K ∙ normalsJoin (c u) (c w)).comap
      ((LinearMap.proj u : (α → ⋀[K]^2 (Fin (k + 2) → K)) →ₗ[K] _) - LinearMap.proj w)

/-- Membership in `joinMotions H c`: the difference at each link lies in the span of the join. -/
theorem mem_joinMotions {k : ℕ} {H : Graph α β} {c : α → Fin (k + 2) → K}
    {S : α → ⋀[K]^2 (Fin (k + 2) → K)} :
    S ∈ joinMotions H c ↔ ∀ f u w, H.IsLink f u w → S u - S w ∈ K ∙ normalsJoin (c u) (c w) := by
  simp [joinMotions, Submodule.mem_iInf]

/-- The relative screws of `a, b` in `H` at the points `c`, in `⋀²` (`sec:pencil-d-short`'s `ρ`):
the differences `S b − S a` over the motions `joinMotions H c`. -/
noncomputable def joinRelScrews {k : ℕ} (H : Graph α β) (c : α → Fin (k + 2) → K) (a b : α) :
    Submodule K (⋀[K]^2 (Fin (k + 2) → K)) :=
  (joinMotions H c).map ((LinearMap.proj b : (α → ⋀[K]^2 (Fin (k + 2) → K)) →ₗ[K] _) -
    LinearMap.proj a)

/-- **The relative screws when the closed neighbourhoods meet** (a step of
`thm:pencil-d-open-ear-three`): if `t` lies in the closed neighbourhoods of both `a` and `b` in `H`
(it is `a`, `b`, or a common neighbour), every motion has `S b − S a = (S b − S t) + (S t − S a)`,
a combination of the joins `c a ∨ c t` and `c t ∨ c b`, so the relative screws lie in their
span. -/
theorem joinRelScrews_le_span_of_mem_closedNbhd {k : ℕ} {H : Graph α β}
    (c : α → Fin (k + 2) → K) {a b t : α} (hta : t ∈ H.closedNbhd a) (htb : t ∈ H.closedNbhd b) :
    joinRelScrews H c a b ≤
      Submodule.span K {normalsJoin (c a) (c t), normalsJoin (c t) (c b)} := by
  rintro _ ⟨S, hS, rfl⟩
  rw [SetLike.mem_coe, mem_joinMotions] at hS
  have h1 : S t - S a ∈ Submodule.span K {normalsJoin (c a) (c t), normalsJoin (c t) (c b)} := by
    rcases hta with rfl | ⟨f, hf⟩
    · simp
    · rw [← neg_sub]
      exact Submodule.neg_mem _ (Submodule.span_mono (by simp) (hS f a t hf))
  have h2 : S b - S t ∈ Submodule.span K {normalsJoin (c a) (c t), normalsJoin (c t) (c b)} := by
    rcases htb with rfl | ⟨f, hf⟩
    · simp
    · rw [← neg_sub]
      exact Submodule.neg_mem _ (Submodule.span_mono (by simp) (hS f t b hf.symm))
  simpa using add_mem h2 h1

/-- **The bridge to the hinge framework**: take `ofNormals G ends c` (whose ends `ends` record
links of `G`) and restrict its hinges to the links of a subgraph `H ≤ G`. The relative screws of
`a, b` of the resulting body-hinge framework, pulled back along `complementScrew`, are
`joinRelScrews H` at the points `c (t, ·)`. -/
theorem map_relScrews_ofNormals_eq_joinRelScrews {k : ℕ} {G H : Graph α β} {ends : β → α × α}
    (hends : ∀ f u w, G.IsLink f u w → G.IsLink f (ends f).1 (ends f).2)
    (hHG : ∀ f u w, H.IsLink f u w → G.IsLink f u w) (c : α × Fin (k + 2) → K) (a b : α) :
    ((⟨H, (PanelHingeFramework.ofNormals (k := k) G ends c).toBodyHinge.supportExtensor⟩ :
      BodyHingeFramework K k α β).relScrews a b).map (complementScrew K k).symm.toLinearMap =
    joinRelScrews H (fun t j => c (t, j)) a b := by
  set ι := complementScrew K k with hι
  have hspan : ∀ f u w, H.IsLink f u w →
      Submodule.span K
          {(PanelHingeFramework.ofNormals (k := k) G ends c).toBodyHinge.supportExtensor f} =
        (K ∙ normalsJoin (fun j => c (u, j)) (fun j => c (w, j))).map ι.toLinearMap := by
    intro f u w hf
    rw [span_supportExtensor_ofNormals_eq (Graph.recordsLinks_iff_forall_isLink.mpr hends) c
      (hHG f u w hf), Submodule.map_span, Set.image_singleton]
    rfl
  ext x
  constructor
  · rintro ⟨_, ⟨S, hS, rfl⟩, rfl⟩
    refine ⟨fun t => ι.symm (S t), mem_joinMotions.mpr fun f u w hf => ?_, ?_⟩
    · have h := hS f u w hf
      rw [BodyHingeFramework.hingeConstraint, hspan f u w hf] at h
      obtain ⟨y, hy, hyeq⟩ := h
      have : ι.symm (S u) - ι.symm (S w) = y := by
        rw [← map_sub, ← hyeq]; simp
      change ι.symm (S u) - ι.symm (S w) ∈ _
      rw [this]; exact hy
    · simp [BodyHingeFramework.screwDiff_apply]
  · rintro ⟨S, hS, rfl⟩
    rw [SetLike.mem_coe, mem_joinMotions] at hS
    refine ⟨_, ⟨fun t => ι (S t), fun f u w hf => ?_, rfl⟩, ?_⟩
    · rw [BodyHingeFramework.hingeConstraint, hspan f u w hf]
      rw [← map_sub]
      exact Submodule.mem_map_of_mem (hS f u w hf)
    · simp [BodyHingeFramework.screwDiff_apply]

open Classical in
/-- **The factoring through `G″`, with its insertion hypothesis at the base data only.**
`Graph.X0Attains.of_openEar_splitOff` at grade `m + 1`: the ear on `V₁` through `x` with `k + 1`
interior bodies attains grade `m`, given that `G[V₁]` and `G″ = G.splitOff v u w e₀` do and that
the suppressed body `v` can be put back (`hins`). Unlike `of_openEar_splitOff`, `hins` is asked
only at the base data of the first stage: a picture `q` off the polynomial `Pq`, a height `zs`
off `Rz q` in `L_{G″}(q)^m` with `z` agreeing with it on `V₁`, and the planes `la`, `lb` of `zs`
at the closed neighbourhoods of `a` and `b`. The subspace `ρ` it quantifies over is
`joinRelScrews (G.induce V₁) (pencilConfigPointGrade q z) a b`, the relative screws of `a`, `b`
in `G[V₁]`, in `⋀²` (not an arbitrary subspace, which fails at three interior bodies). With
`D = screwDim (m + 1)` for `6`. -/
theorem _root_.Graph.X0AttainsGrade.of_openEar_splitOff_of_base [Infinite K] [Finite α] [Finite β]
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
    {Pq : MvPolynomial (α × Fin 2) K} (hPq : Pq ≠ 0)
    {Rz : (α × Fin 2 → K) → MvPolynomial (α × Fin m) K}
    (hRz : ∀ q, (G.splitOff v u w e₀).IsAdmissiblePicture q →
      ∃ z ∈ (G.splitOff v u w e₀).liftingSpaceGrade q m, MvPolynomial.eval z (Rz q) ≠ 0)
    (hins : ∀ (q : α × Fin 2 → K) (z zs : α × Fin m → K) (la lb : Fin m → Fin 3 → K),
      MvPolynomial.eval q Pq ≠ 0 → (G.splitOff v u w e₀).IsAdmissiblePicture q →
      zs ∈ (G.splitOff v u w e₀).liftingSpaceGrade q m → MvPolynomial.eval zs (Rz q) ≠ 0 →
      (∀ t ∈ V₁, ∀ i, z (t, i) = zs (t, i)) →
      (∀ i, ∀ p ∈ (G.splitOff v u w e₀).closedNbhd a,
        zs (p, i) = la i ⬝ᵥ pencilPicturePoint q p) →
      (∀ i, ∀ p ∈ (G.splitOff v u w e₀).closedNbhd b,
        zs (p, i) = lb i ⬝ᵥ pencilPicturePoint q p) →
      ∃ Q : MvPolynomial ((α × Fin 2) ⊕ (α × Fin m)) K, Q ≠ 0 ∧ ∀ s, MvPolynomial.eval s Q ≠ 0 →
        (G.splitOff v u w e₀).IsAdmissiblePicture (earPictureGrade V₁ q s) →
        ∃ x₂ : Fin (m + 1 + 2) → K, x₂ (Fin.last (m + 2)) = 1 ∧
          ∀ p : α → Fin (m + 1 + 2) → K, p v = x₂ →
          (∀ t, t ≠ v → p t = fun j => earConfigGrade V₁ q z xf xl (Set.range x) la lb s (t, j)) →
          min (Module.finrank K ↥(joinRelScrews (G.induce V₁) (pencilConfigPointGrade q z) a b ⊔
            Submodule.span K (Set.range fun i : Fin (k + 1) =>
            normalsJoin (fun j => earConfigGrade V₁ q z xf xl (Set.range x) la lb s
                (pathVertex a y b i.castSucc, j))
              (fun j => earConfigGrade V₁ q z xf xl (Set.range x) la lb s
                (pathVertex a y b i.succ, j)))) + 1) (screwDim (m + 1)) ≤
          Module.finrank K ↥(joinRelScrews (G.induce V₁) (pencilConfigPointGrade q z) a b ⊔
            Submodule.span K (Set.range fun i : Fin (k + 2) =>
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
      ((Graph.recordsLinks_iff_forall_isLink.mpr hends).update_splitOff hl₀'').isLink
  obtain ⟨q', z₁, zs, la, lb, sstar, ρM, hqm', hadm₂, hpicstar, hrk₂, hne₂, hz₁s, hlas, hlbs, hρG,
      hρ2, hrk₁, hrk₁'', hzs, hzsR, hz₁zs, hlaz, hlbz⟩ :=
    Graph.exists_earBase_splitOff_grade hk hcover'' hinj'' hyV₁ ha hb hab hpath'' hsep'' hl₀'' he₀
      hind hends (hkeep _ _ _ (hxf ▸ ear_isLink_first hpath (by omega)) ha hvf)
      (hkeep _ _ _ (hxl ▸ (ear_isLink_last hpath (by omega)).symm) hb hvl) hyx h₁ h₂
      (mul_ne_zero hPm hPq) hRz
  rw [map_mul] at hqm'
  set ρJ := ρM.map (complementScrew K (m + 1)).symm.toLinearMap with hρJ
  -- the insertion hypothesis, a polynomial condition on the ear data
  -- `ρJ` is `G[V₁]`'s relative screws at the base configuration `(q*, z₁)`
  have hendsI := Graph.recordsLinks_iff_forall_isLink.mp
    ((Graph.recordsLinks_iff_forall_isLink.mpr hends).induce V₁)
  have hρJ' : ρJ = joinRelScrews (G.induce V₁) (pencilConfigPointGrade q' z₁) a b := by
    rw [hρJ, ← hρG sstar, ← map_relScrews_ofNormals_eq_joinRelScrews hends
      (fun f p p' hf => hf.of_le (Graph.induce_le (hcover ▸ Set.subset_union_left)))
      (fun p => pencilConfigPointGrade q' z₁ p.1 p.2)]
    congr 1
    refine BodyHingeFramework.relScrews_congr (G.induce V₁) (fun f p p' hf => ?_) a b
    obtain ⟨-, h1, h2⟩ := hendsI f p p' hf
    simp only [PanelHingeFramework.toBodyHinge_supportExtensor,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_ends]
    congr 1 <;> funext j
    · exact earConfigGrade_of_mem sstar h1 j
    · exact earConfigGrade_of_mem sstar h2 j
  obtain ⟨Qx, hQx₀, hQx⟩ := hins q' z₁ zs la lb (right_ne_zero_of_mul hqm') hadm₂ hzs hzsR hz₁zs
    hlaz hlbz
  rw [← hρJ'] at hQx
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
    rw [eval_bind₁_earPicturePolyGrade, hpicstar]; exact left_ne_zero_of_mul hqm'
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

open Classical in
/-- `Graph.X0Attains.of_openEar_splitOff` at grade `m + 1`: the step at four or more interior
bodies, given that the suppressed body `v` can be put back off a polynomial in the ear data, with
`D = screwDim (m + 1)` for `6`. The subspace `ρ` of `hins` lies in `⋀²`, the space of the joins.
It is the corollary of `of_openEar_splitOff_of_base` at `Pq = 1`, `Rz = 1`, and cannot take three
interior bodies, where `hins` fails (`notes/Phase42i.md`); that step goes through `_of_base`. -/
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
  have hRz : ∀ q, (G.splitOff v u w e₀).IsAdmissiblePicture q →
      ∃ z ∈ (G.splitOff v u w e₀).liftingSpaceGrade q m,
        MvPolynomial.eval z ((fun _ => (1 : MvPolynomial (α × Fin m) K)) q) ≠ 0 :=
    fun q _ => ⟨0, Submodule.zero_mem _, by simp⟩
  exact Graph.X0AttainsGrade.of_openEar_splitOff_of_base hG hk hcover hinj hxV₁ ha hb hab hpath
    hsep hcover'' hinj'' hyV₁ hpath'' hsep'' hyx hv hu hl₀ hl₀'' hdef hxf hxl hvf hvl
    one_ne_zero hRz
    (fun q z zs la lb _ _ _ _ hz hla hlb => hins q z la lb _
      (fun i => (hz a ha i).trans (hla i a (Or.inl rfl)))
      (fun i => (hz b hb i).trans (hlb i b (Or.inl rfl)))) h₁ h₂

/-! ## The stars condition and the insertion, in path-join form -/

/-- Rescaling the members of a family by nonzero scalars does not change its span. -/
theorem span_range_smul_eq {ι V : Type*} [AddCommGroup V] [Module K V] (x : ι → V) (d : ι → K)
    (hd : ∀ i, d i ≠ 0) :
    Submodule.span K (Set.range fun i => d i • x i) = Submodule.span K (Set.range x) := by
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
  · rintro _ ⟨i, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rintro _ ⟨i, rfl⟩
    have : x i = (d i)⁻¹ • (d i • x i) := by rw [smul_smul, inv_mul_cancel₀ (hd i), one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- The stars condition of `lem:pencil-d-stars-four` and `lem:pencil-d-stars-three` holds at the
interior points `Y` if it holds at their nonzero multiples `c i • Y i`, as rescaling changes neither
the span of the joins nor the stars (the `hC` of `lem:pencil-d-ear-data` (3)). -/
theorem starsCond_of_smul {k n : ℕ} (ρ : Submodule K (⋀[K]^2 (Fin (k + 2) → K)))
    (pa pb : Fin (k + 2) → K) (Y : Fin (n + 2) → Fin (k + 2) → K) (c : Fin (n + 2) → K)
    (hc : ∀ i, c i ≠ 0)
    (h : starGrade (c 0 • Y 0) ⊔ starGrade (c 1 • Y 1) ≤ ρ ⊔ Submodule.span K
        (Set.range fun i : Fin (n + 3) =>
          normalsJoin (pathVertex pa (fun i => c i • Y i) pb i.castSucc)
            (pathVertex pa (fun i => c i • Y i) pb i.succ)) →
      ρ ⊔ Submodule.span K (Set.range fun i : Fin (n + 3) =>
          normalsJoin (pathVertex pa (fun i => c i • Y i) pb i.castSucc)
            (pathVertex pa (fun i => c i • Y i) pb i.succ)) = ⊤) :
    starGrade (Y 0) ⊔ starGrade (Y 1) ≤ ρ ⊔ Submodule.span K
        (Set.range fun i : Fin (n + 3) =>
          normalsJoin (pathVertex pa Y pb i.castSucc) (pathVertex pa Y pb i.succ)) →
      ρ ⊔ Submodule.span K (Set.range fun i : Fin (n + 3) =>
          normalsJoin (pathVertex pa Y pb i.castSucc) (pathVertex pa Y pb i.succ)) = ⊤ := by
  set sc : Fin (n + 4) → K := Fin.snoc (Fin.cons 1 c : Fin (n + 3) → K) 1 with hsc
  have hsc0 : ∀ i : Fin (n + 4), sc i ≠ 0 := by
    intro i
    induction i using Fin.lastCases with
    | last => simp [hsc]
    | cast i =>
      induction i using Fin.cases with
      | zero => simp [hsc]
      | succ i => simpa only [hsc, Fin.snoc_castSucc, Fin.cons_succ] using hc i
  have hspan : Submodule.span K (Set.range fun i : Fin (n + 3) =>
      normalsJoin (pathVertex pa (fun i => c i • Y i) pb i.castSucc)
        (pathVertex pa (fun i => c i • Y i) pb i.succ)) =
      Submodule.span K (Set.range fun i : Fin (n + 3) =>
        normalsJoin (pathVertex pa Y pb i.castSucc) (pathVertex pa Y pb i.succ)) := by
    simp only [pathVertex_smul_comp, normalsJoin_smul_left, normalsJoin_smul_right, ← hsc]
    simp only [smul_smul]
    exact span_range_smul_eq (fun i : Fin (n + 3) =>
      normalsJoin (pathVertex pa Y pb i.castSucc) (pathVertex pa Y pb i.succ))
      (fun i => sc i.succ * sc i.castSucc) (fun i => mul_ne_zero (hsc0 _) (hsc0 _))
  rw [hspan, starGrade_smul (hc 0), starGrade_smul (hc 1)] at h
  exact h

/-- The joins of the path through the extra point `P 2`: if `Q` is `P` without its index `2`, the
joins of `P` span what the joins of `Q` but the one at `1` (`Q 1 ∨ Q 2`, which is `P 1 ∨ P 3`)
span with `P 1 ∨ P 2` and `P 2 ∨ P 3`. -/
theorem span_joins_succAbove_two {k n : ℕ} (P : Fin (n + 5) → Fin (k + 2) → K)
    (Q : Fin (n + 4) → Fin (k + 2) → K) (h : ∀ j, P (Fin.succAbove 2 j) = Q j) :
    Submodule.span K (Set.range fun i : Fin (n + 4) => normalsJoin (P i.castSucc) (P i.succ)) =
      Submodule.span K (Set.range fun j : Fin (n + 3) =>
        if j = 1 then 0 else normalsJoin (Q j.castSucc) (Q j.succ)) ⊔
      Submodule.span K {normalsJoin (P 1) (P 2), normalsJoin (P 2) (P 3)} := by
  have hQ : ∀ (j : Fin (n + 4)) (t : Fin (n + 5)),
      (t : ℕ) = (if (j : ℕ) < 2 then (j : ℕ) else (j : ℕ) + 1) → P t = Q j := fun j t ht => by
    rw [← h j]
    congr 1
    exact Fin.ext (by rw [coe_succAbove_two]; exact ht)
  have key : ∀ (j : Fin (n + 3)) (i : Fin (n + 4)),
      ((j : ℕ) = 0 → (i : ℕ) = 0) → (2 ≤ (j : ℕ) → (i : ℕ) = j + 1) → (j : ℕ) ≠ 1 →
      normalsJoin (Q j.castSucc) (Q j.succ) = normalsJoin (P i.castSucc) (P i.succ) := by
    intro j i h0 h2 h1
    have e1 : P i.castSucc = Q j.castSucc := hQ _ _ (by
      simp only [Fin.val_castSucc]; split_ifs <;> omega)
    have e2 : P i.succ = Q j.succ := hQ _ _ (by
      simp only [Fin.val_succ]; split_ifs <;> omega)
    rw [e1, e2]
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    by_cases h0 : (i : ℕ) = 0
    · refine Submodule.mem_sup_left (Submodule.subset_span ⟨0, ?_⟩)
      beta_reduce
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by simp))]
      exact key 0 i (fun _ => h0) (by simp) (by simp)
    by_cases h1 : (i : ℕ) = 1
    · refine Submodule.mem_sup_right (Submodule.subset_span (Or.inl ?_))
      have hi : i = 1 := Fin.ext h1
      subst hi
      rfl
    by_cases h2 : (i : ℕ) = 2
    · refine Submodule.mem_sup_right (Submodule.subset_span (Or.inr ?_))
      have hi : i = 2 := Fin.ext h2
      subst hi
      rfl
    · refine Submodule.mem_sup_left (Submodule.subset_span ⟨⟨(i : ℕ) - 1, by omega⟩, ?_⟩)
      beta_reduce
      rw [ite_eq_right_of_eq_false _ _
        (eq_false (by simp only [Fin.ext_iff, Fin.val_one]; omega))]
      exact key _ i (fun h => by simp only at h; omega) (fun _ => by simp only; omega)
        (by simp only; omega)
  · refine sup_le (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
    · rintro _ ⟨j, rfl⟩
      beta_reduce
      by_cases hj : j = 1
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hj)]; exact Submodule.zero_mem _
      rw [ite_eq_right_of_eq_false _ _ (eq_false hj)]
      have hj1 : (j : ℕ) ≠ 1 := fun e => hj (Fin.ext e)
      by_cases hj0 : (j : ℕ) = 0
      · refine Submodule.subset_span ⟨0, ?_⟩
        exact (key j 0 (fun _ => by simp) (by omega) hj1).symm
      · refine Submodule.subset_span ⟨⟨(j : ℕ) + 1, by omega⟩, ?_⟩
        exact (key j _ (fun h => by omega) (fun _ => rfl) hj1).symm
    · rintro _ (rfl | rfl)
      · exact Submodule.subset_span ⟨1, rfl⟩
      · exact Submodule.subset_span ⟨2, rfl⟩

/-- **Putting the suppressed body back** (a step of `thm:pencil-d-open-ear-four` and
`thm:pencil-d-open-ear-three`, by `lem:pencil-d-insertion`). Let `a − x 0 − ⋯ − x (n + 2) − b` be
an ear of `G` with `n + 3` interior bodies, and `a − x 0 − x 2 − ⋯ − x (n + 2) − b` the ear of
`G″`, without `x 1`. At ear data `s` where the third condition holds at the points `Y` of the
interior bodies of `G″` (the span `W` of `ρ` and the joins of the ear of `G″` is everything
whenever it holds both stars of `Y 0`, `Y 1`), some `x₂` with last coordinate `1` raises the span
by one: with `x 1` at `x₂` and the other bodies at their ear points, `ρ` and the joins of the ear
of `G` span at least `min (dim W + 1, D)`. The proof is `exists_insertion_of_starGrade_sup` at
`R = ρ +` the joins of `G″` but `Y 0 ∨ Y 1`, and `span_joins_succAbove_two`. -/
theorem exists_insertion_earDataGrade [Infinite K] {V₁ : Set α} {q₁ : α × Fin 2 → K}
    {z₁ : α × Fin m → K} {xf xl : α} {la lb : Fin m → Fin 3 → K} {n : ℕ} {x : Fin (n + 3) → α}
    {a b : α} (hinj : Function.Injective x) (hxV₁ : ∀ i, x i ∉ V₁) (ha : a ∈ V₁) (hb : b ∈ V₁)
    (ρ : Submodule K (⋀[K]^2 (Fin (m + 1 + 2) → K))) {pa pb : Fin (m + 1 + 2) → K}
    (hpa : pencilConfigPointGrade q₁ z₁ a = pa) (hpb : pencilConfigPointGrade q₁ z₁ b = pb)
    (s : (α × Fin 2) ⊕ (α × Fin m) → K)
    (hC : ∀ Y : Fin (n + 2) → Fin (m + 1 + 2) → K, (∀ i j, Y i j = earConfigGrade V₁ q₁ z₁ xf xl
          (Set.range x) la lb s ((x ∘ Fin.succAbove 1) i, j)) →
        starGrade (Y 0) ⊔ starGrade (Y 1) ≤ ρ ⊔ Submodule.span K
          (Set.range fun i : Fin (n + 3) =>
            normalsJoin (pathVertex pa Y pb i.castSucc) (pathVertex pa Y pb i.succ)) →
          ρ ⊔ Submodule.span K (Set.range fun i : Fin (n + 3) =>
            normalsJoin (pathVertex pa Y pb i.castSucc) (pathVertex pa Y pb i.succ)) = ⊤) :
    ∃ x₂ : Fin (m + 1 + 2) → K, x₂ (Fin.last (m + 2)) = 1 ∧
      ∀ p : α → Fin (m + 1 + 2) → K, p (x 1) = x₂ →
      (∀ t, t ≠ x 1 →
        p t = fun j => earConfigGrade V₁ q₁ z₁ xf xl (Set.range x) la lb s (t, j)) →
      min (Module.finrank K ↥(ρ ⊔ Submodule.span K (Set.range fun i : Fin (n + 3) =>
        normalsJoin (fun j => earConfigGrade V₁ q₁ z₁ xf xl (Set.range x) la lb s
            (pathVertex a (x ∘ Fin.succAbove 1) b i.castSucc, j))
          (fun j => earConfigGrade V₁ q₁ z₁ xf xl (Set.range x) la lb s
            (pathVertex a (x ∘ Fin.succAbove 1) b i.succ, j)))) + 1) (screwDim (m + 1)) ≤
      Module.finrank K ↥(ρ ⊔ Submodule.span K (Set.range fun i : Fin (n + 4) =>
        normalsJoin (p (pathVertex a x b i.castSucc)) (p (pathVertex a x b i.succ)))) := by
  classical
  set cfg : α → Fin (m + 1 + 2) → K := fun w c => earConfigGrade V₁ q₁ z₁ xf xl
    (Set.range x) la lb s (w, c) with hcfg
  set Y : Fin (n + 2) → Fin (m + 1 + 2) → K := fun i => cfg ((x ∘ Fin.succAbove 1) i) with hY
  have hcfa : cfg a = pa := (funext fun c => earConfigGrade_of_mem (V₁ := V₁) (q₁ := q₁)
    (z₁ := z₁) (xf := xf) (xl := xl) (X := Set.range x) (la := la) (lb := lb) s ha c).trans hpa
  have hcfb : cfg b = pb := (funext fun c => earConfigGrade_of_mem (V₁ := V₁) (q₁ := q₁)
    (z₁ := z₁) (xf := xf) (xl := xl) (X := Set.range x) (la := la) (lb := lb) s hb c).trans hpb
  have hQY : ∀ j, cfg (pathVertex a (x ∘ Fin.succAbove 1) b j) = pathVertex pa Y pb j := by
    intro j
    rw [pathVertex_map cfg a b (x ∘ Fin.succAbove 1) j, hcfa, hcfb]
    rfl
  have hy1 : ∀ i, Y i (Fin.last (m + 2)) = 1 := fun i => by
    simp [hY, hcfg, earConfigGrade]
  set pv : Fin (n + 4) → Fin (m + 1 + 2) → K := pathVertex pa Y pb with hpv
  set R : Submodule K (⋀[K]^2 (Fin (m + 1 + 2) → K)) := ρ ⊔ Submodule.span K
    (Set.range fun j : Fin (n + 3) =>
      if j = 1 then 0 else normalsJoin (pv j.castSucc) (pv j.succ)) with hR
  have hJ1 : normalsJoin (pv (Fin.castSucc 1)) (pv (Fin.succ 1)) = normalsJoin (Y 0) (Y 1) := by
    rw [Fin.castSucc_one, Fin.succ_one_eq_two, hpv,
      pathVertex_eq_of_val_eq pa pb Y (i := 0) (by simp),
      pathVertex_eq_of_val_eq pa pb Y (i := 1) (by simp)]
  have hRe : R ⊔ K ∙ normalsJoin (Y 0) (Y 1) = ρ ⊔ Submodule.span K
      (Set.range fun i : Fin (n + 3) => normalsJoin (pv i.castSucc) (pv i.succ)) := by
    rw [hR, sup_assoc]
    congr 1
    refine le_antisymm (sup_le (Submodule.span_le.mpr ?_)
      (Submodule.span_singleton_le_iff_mem _ _ |>.mpr ?_)) (Submodule.span_le.mpr ?_)
    · rintro _ ⟨j, rfl⟩
      beta_reduce
      by_cases hj : j = 1
      · simp only [hj, ↓reduceIte]; exact Submodule.zero_mem _
      · simp only [hj, ↓reduceIte]; exact Submodule.subset_span ⟨j, rfl⟩
    · exact Submodule.subset_span ⟨1, hJ1⟩
    · rintro _ ⟨j, rfl⟩
      by_cases hj : j = 1
      · subst hj
        exact Submodule.mem_sup_right (by
          change normalsJoin (pv (Fin.castSucc 1)) (pv (Fin.succ 1)) ∈ _
          rw [hJ1]; exact Submodule.mem_span_singleton_self _)
      · exact Submodule.mem_sup_left (Submodule.subset_span ⟨j, by simp [hj]⟩)
  obtain ⟨x₂, hx₂, hmin⟩ := exists_insertion_of_starGrade_sup R (Y 0) (Y 1) (hy1 0) (hy1 1)
    (by rw [hRe]; exact hC Y fun i j => rfl)
  refine ⟨x₂, hx₂, fun p hpvx hpt => ?_⟩
  have hP : ∀ j, p (pathVertex a x b (Fin.succAbove 2 j)) = pv j := fun j => by
    rw [← pathVertex_comp_succAbove_one, ← hQY j]
    refine hpt _ ?_
    rcases pathVertex_cases a (x ∘ Fin.succAbove 1) b j with ⟨_, h'⟩ | ⟨i, _, h'⟩ | ⟨_, h'⟩
    · rw [h']; exact fun h => hxV₁ 1 (h ▸ ha)
    · rw [h']; exact fun h => Fin.succAbove_ne 1 i (hinj h)
    · rw [h']; exact fun h => hxV₁ 1 (h ▸ hb)
  have hP1 : p (pathVertex a x b 1) = Y 0 := by
    have h1 : (Fin.succAbove 2 (1 : Fin (n + 4)) : Fin (n + 5)) = 1 :=
      Fin.ext (by rw [coe_succAbove_two]; simp)
    have := hP 1
    rw [h1] at this
    rw [this, hpv, pathVertex_eq_of_val_eq pa pb Y (i := 0) (by simp)]
  have hP3 : p (pathVertex a x b 3) = Y 1 := by
    have h1 : (Fin.succAbove 2 (2 : Fin (n + 4)) : Fin (n + 5)) = 3 :=
      Fin.ext (by
        rw [coe_succAbove_two, Fin.val_two, Fin.coe_ofNat_eq_mod,
          Nat.mod_eq_of_lt (show 3 < n + 4 + 1 by omega)]
        simp)
    have := hP 2
    rw [h1] at this
    rw [this, hpv, pathVertex_eq_of_val_eq pa pb Y (i := 1) (by simp)]
  have hP2 : p (pathVertex a x b 2) = x₂ := by
    rw [pathVertex_eq_of_val_eq a b x (i := 1) (by simp)]; exact hpvx
  have hspan := span_joins_succAbove_two (fun i => p (pathVertex a x b i)) pv hP
  beta_reduce at hspan
  rw [hP1, hP2, hP3] at hspan
  have hfinal : R ⊔ Submodule.span K {normalsJoin (Y 0) x₂, normalsJoin x₂ (Y 1)} =
      ρ ⊔ Submodule.span K (Set.range fun i : Fin (n + 4) =>
        normalsJoin (p (pathVertex a x b i.castSucc)) (p (pathVertex a x b i.succ))) := by
    rw [hspan, hR, sup_assoc]
  have hgoalL : (Set.range fun i : Fin (n + 3) =>
      normalsJoin (fun j => cfg (pathVertex a (x ∘ Fin.succAbove 1) b i.castSucc) j)
        (fun j => cfg (pathVertex a (x ∘ Fin.succAbove 1) b i.succ) j)) =
      Set.range fun i : Fin (n + 3) => normalsJoin (pv i.castSucc) (pv i.succ) := by
    congr 1; funext i; rw [hQY, hQY]
  have hL : Module.finrank K ↥(ρ ⊔ Submodule.span K (Set.range fun i : Fin (n + 3) =>
      normalsJoin (fun j => cfg (pathVertex a (x ∘ Fin.succAbove 1) b i.castSucc) j)
        (fun j => cfg (pathVertex a (x ∘ Fin.succAbove 1) b i.succ) j))) =
      Module.finrank K ↥(R ⊔ K ∙ normalsJoin (Y 0) (Y 1)) := by
    rw [hRe, hgoalL]
  refine le_of_eq_of_le ?_ (hmin.trans_eq (by rw [hfinal]))
  exact congrArg (fun r => min (r + 1) (screwDim (m + 1))) hL

/-! ## The open ear with four or more interior bodies (`thm:pencil-d-open-ear-four`) -/


/-- `thm:pencil-d-open-ear-four`: let `G` satisfy the standing hypotheses, with an open ear
`a − x 0 − ⋯ − x (n + 3) − b` on `V₁` of `n + 4 ≥ 4` interior bodies, its ends possibly adjacent,
and let `G″ = G.splitOff (x 1) (x 0) (x 2) (e 1)` be `G` with `x 1` suppressed. If the general
configurations of `G[V₁]` and `G″` attain with `m` heights, so does that of `G`. The proof is
`Graph.X0AttainsGrade.of_openEar_splitOff` at `G″` (`splitOff_ear_succAbove`), its `hins`
discharged by `exists_mvPolynomial_starsFour`, moved to the ear data by
`exists_mvPolynomial_earDataGrade_of_smul` (`starsCond_of_smul`), and
`exists_insertion_earDataGrade`. -/
theorem _root_.Graph.X0AttainsGrade.of_openEar_four [Infinite K] [Finite α] [Finite β]
    {G : Graph α β} (hG : G.IsX0Graph) {V₁ : Set α} {n : ℕ} {x : Fin (n + 4) → α} {a b : α}
    {e : Fin (n + 5) → β} (hcover : V(G) = V₁ ∪ Set.range x) (hinj : Function.Injective x)
    (hxV₁ : ∀ i, x i ∉ V₁) (ha : a ∈ V₁) (hb : b ∈ V₁) (hab : a ≠ b)
    (hpath : ∀ i : Fin (n + 5),
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (hsep : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁)
    (h₁ : (G.induce V₁).X0AttainsGrade K m)
    (h₂ : (G.splitOff (x 1) (x 0) (x 2) (e 1)).X0AttainsGrade K m) : G.X0AttainsGrade K m := by
  have hx : ∀ i j, i ≠ j → x i ≠ x j := fun i j h h' => h (hinj h')
  obtain ⟨hcover'', hinj'', hxV₁'', hpath'', hsep'', hdeg2⟩ :=
    splitOff_ear_succAbove (k := n + 1) hcover hinj hxV₁ ha hb hab hpath hsep
  have x01 := hx 0 1 (by simp)
  have x12 := hx 1 2 (by simp [Fin.ext_iff, Nat.mod_eq_of_lt (show 2 < n + 4 by omega)])
  have l1 : G.IsLink (e 1) (x 0) (x 1) := by
    have := hpath 1
    rwa [pathVertex_eq_of_val_eq a b x (i := 0) (by simp),
      pathVertex_eq_of_val_eq a b x (i := 1) (by simp)] at this
  have l2 : G.IsLink (e 2) (x 1) (x 2) := by
    have := hpath 2
    rwa [pathVertex_eq_of_val_eq a b x (i := 1) (by simp),
      pathVertex_eq_of_val_eq a b x (i := 2) (by simp [Nat.mod_eq_of_lt (show 2 < n + 4 by omega),
        Nat.mod_eq_of_lt (show 2 < n + 5 by omega)])] at this
  refine Graph.X0AttainsGrade.of_openEar_splitOff (k := n + 3) hG (by omega) hcover hinj hxV₁ ha
    hb hab hpath hsep hcover'' hinj'' hxV₁'' hpath'' hsep''
    (by rintro _ ⟨i, rfl⟩; exact ⟨_, rfl⟩) ⟨1, rfl⟩ (hxV₁ 0) l1 ?_
    (Graph.splitOff_deficiency_le_of_eq_left (n := m + 2)
      (by rw [Graph.bodyBarDim_add_one_eq_screwDim]; have := three_le_screwDim_succ (m := m); omega)
      x01 x12.symm l1.symm l2
      hdeg2) (xf := x 0) (xl := x (Fin.last _)) rfl rfl x01.symm
      (hx 1 (Fin.last _) (by simp [Fin.ext_iff])) (fun q z la lb ρ hza hzb => ?_) h₁ h₂
  · -- the first residual: the relinked edge `e 1` joins `x 0` to `x 2` in `G″`
    have h := hpath'' 1
    have s0 : (Fin.succAbove 1 (0 : Fin (n + 3)) : Fin (n + 4)) = 0 :=
      Fin.ext (by rw [coe_succAbove_one]; simp)
    have s1 : (Fin.succAbove 1 (1 : Fin (n + 3)) : Fin (n + 4)) = 2 :=
      Fin.ext (by rw [coe_succAbove_one]; simp [Nat.mod_eq_of_lt (show 2 < n + 4 by omega)])
    simp only [Function.comp] at h
    rw [pathVertex_eq_of_val_eq a b _ (i := 0) (by simp),
      pathVertex_eq_of_val_eq a b _ (i := 1) (by simp)] at h
    simp only [Function.comp_apply, s0, s1] at h
    exact h
  · classical
    -- the stars-four polynomial, over the planes `Π_a`, `Π_b`
    set pa : Fin (m + 1 + 2) → K := pencilConfigPointGrade q z a with hpa
    set pb : Fin (m + 1 + 2) → K := pencilConfigPointGrade q z b with hpb
    have hSa : LinearMap.range (gradeSigma la) ≠ ⊥ := by
      refine (Submodule.ne_bot_iff _).mpr ⟨gradeSigma la ![0, 0, 1], ⟨_, rfl⟩, fun h => ?_⟩
      have := gradeSigma_injective la (h.trans (map_zero _).symm)
      simpa using congr_fun this 2
    obtain ⟨f, hf₀, hf⟩ := exists_mvPolynomial_starsFour (n := n) ρ hSa pa pb
      (Sb := LinearMap.range (gradeSigma lb))
    have hv0 : ∀ i : Fin (n + 3), (x ∘ Fin.succAbove 1) i = x 0 → i = 0 := fun i h => by
      have h' := hinj h
      rw [Fin.ext_iff, coe_succAbove_one] at h'
      exact Fin.ext (by simp at h'; split_ifs at h'; omega)
    have hvl : ∀ i : Fin (n + 3), (x ∘ Fin.succAbove 1) i = x (Fin.last _) → i = Fin.last _ :=
      fun i h => by
        have h' := hinj h
        rw [Fin.ext_iff, coe_succAbove_one] at h'
        exact Fin.ext (by simp at h' ⊢; split_ifs at h' <;> omega)
    have hfl : x (Fin.last (n + 3)) ≠ x 0 := hx _ _ (by simp [Fin.ext_iff])
    obtain ⟨g, ⟨s₀, hs₀⟩, hg⟩ := exists_mvPolynomial_earDataGrade_of_smul (V₁ := V₁) (q₁ := q)
      (z₁ := z) (xf := x 0) (xl := x (Fin.last _)) (X := Set.range x) (la := la) (lb := lb)
      (v := x ∘ Fin.succAbove 1) hinj'' (fun i => hxV₁ _)
      (fun i => Or.inr (Or.inr ⟨_, rfl⟩)) hfl
      (fun Y => starGrade (Y 0) ⊔ starGrade (Y 1) ≤ ρ ⊔ Submodule.span K
          (Set.range fun i : Fin (n + 4) =>
            normalsJoin (pathVertex pa Y pb i.castSucc) (pathVertex pa Y pb i.succ)) →
        ρ ⊔ Submodule.span K (Set.range fun i : Fin (n + 4) =>
            normalsJoin (pathVertex pa Y pb i.castSucc) (pathVertex pa Y pb i.succ)) = ⊤)
      (fun Y c hc h => starsCond_of_smul ρ pa pb Y c hc h) (f := f)
      (by
        obtain ⟨Y, hY0, hYl, hYf⟩ := hf₀
        exact ⟨Y, fun i hi => hv0 i hi ▸ hY0, fun i hi => hvl i hi ▸ hYl, hYf⟩)
      (fun Y hYa hYb hYf => (hf Y (hYa 0 rfl) (hYb _ rfl) hYf).2)
    refine ⟨g, fun h => hs₀ (by simp [h]), fun s hs _ => exists_insertion_earDataGrade hinj hxV₁
      ha hb ρ rfl rfl s fun Y hY => ?_⟩
    obtain rfl : Y = _ := funext fun i => funext (hY i)
    exact hg s hs

end CombinatorialRigidity.Molecular
