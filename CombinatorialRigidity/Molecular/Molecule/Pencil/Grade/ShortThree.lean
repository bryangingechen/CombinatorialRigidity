/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.GluedEnds
public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.StarsThree
public import CombinatorialRigidity.Molecular.AlgebraicInduction.DeficiencyBound

/-!
# The step at three interior bodies of an open ear, in dimensions four to six

The step `thm:pencil-d-open-ear-three` (`blueprint/src/chapter/pencil-d.tex`,
`sec:pencil-d-short`), with `m` heights, `2 ≤ m ≤ 4`, that is `4 ≤ d ≤ 6`:
`Graph.X0AttainsGrade.of_openEar_three`.

* `exists_mvPolynomial_earDataGrade_starsCond_three`: the third condition on the ear data, off a
  nonzero polynomial, when `dim ρ ≤ 2` (`not_starGrade_sup_le_of_finrank_le_two`,
  `Grade/Stars.lean`) or `d + κ ≤ 6` (by stars-three).
* `Graph.X0AttainsGrade.of_openEar_three`: the factoring through `G″` with the insertion hypothesis
  at the base data (`Graph.X0AttainsGrade.of_openEar_splitOff_of_base`), the picture off
  glued-ends' polynomial for `G[V₁]` and the heights off planes-meet's for `G″`.
-/

@[expose] public section

namespace CombinatorialRigidity.Molecular

open scoped Graph Matrix

variable {K : Type*} [Field K] {α β : Type*} {m : ℕ}

/-- **The third condition at three interior bodies** (a step of `thm:pencil-d-open-ear-three`).
Let the ear of `G″` be `a − x 0 − x 2 − b`, with base data `(q₁, z₁)` and planes `Π_a`, `Π_b` the
images of `gradeSigma la`, `gradeSigma lb`, and let `pa ∈ Π_a`, `pb ∈ Π_b`. If `dim ρ ≤ 2`, or
`d + κ ≤ 6` with `κ = dim (Π_a ∩ Π_b)` (`m + 1 + κ ≤ 5`), then off the zero set of a nonzero
polynomial in the ear data, the span `W` of `ρ` and the joins `pa ∨ y₁`, `y₁ ∨ y₃`, `y₃ ∨ pb` of
the points `y₁`, `y₃` of `x 0`, `x 2` is everything whenever it holds both stars. When
`dim ρ ≤ 2` the polynomial is the difference of the first coordinates of the pictures of `x 0` and
`x 2`, off which `y₁`, `y₃` are independent (`not_starGrade_sup_le_of_finrank_le_two`); otherwise
it is `exists_mvPolynomial_starsThree` moved to the ear data by
`exists_mvPolynomial_earDataGrade_of_smul`. -/
theorem exists_mvPolynomial_earDataGrade_starsCond_three [Infinite K] {V₁ : Set α}
    {q₁ : α × Fin 2 → K} {z₁ : α × Fin m → K} {la lb : Fin m → Fin 3 → K} {x : Fin 3 → α}
    (hinj : Function.Injective x) (hxV₁ : ∀ i, x i ∉ V₁) (hm : 2 ≤ m)
    (ρ : Submodule K (⋀[K]^2 (Fin (m + 1 + 2) → K))) {pa pb : Fin (m + 1 + 2) → K}
    (hpa : pa ∈ LinearMap.range (gradeSigma la)) (hpb : pb ∈ LinearMap.range (gradeSigma lb))
    (hρκ : Module.finrank K ρ ≤ 2 ∨ m + 1 + Module.finrank K
      ↥(LinearMap.range (gradeSigma la) ⊓ LinearMap.range (gradeSigma lb)) ≤ 5) :
    ∃ g : MvPolynomial ((α × Fin 2) ⊕ (α × Fin m)) K, g ≠ 0 ∧ ∀ s, MvPolynomial.eval s g ≠ 0 →
      ∀ Y : Fin 2 → Fin (m + 1 + 2) → K, (∀ i j, Y i j = earConfigGrade V₁ q₁ z₁ (x 0) (x 2)
          (Set.range x) la lb s ((x ∘ Fin.succAbove 1) i, j)) →
        starGrade (Y 0) ⊔ starGrade (Y 1) ≤ ρ ⊔ Submodule.span K (Set.range fun i : Fin 3 =>
            normalsJoin (pathVertex pa Y pb i.castSucc) (pathVertex pa Y pb i.succ)) →
          ρ ⊔ Submodule.span K (Set.range fun i : Fin 3 =>
            normalsJoin (pathVertex pa Y pb i.castSucc) (pathVertex pa Y pb i.succ)) = ⊤ := by
  classical
  rcases hρκ with hρ2 | hκ
  · -- `dim ρ ≤ 2`: the span never holds both stars at independent points
    refine ⟨MvPolynomial.X (Sum.inl (x 0, 0)) - MvPolynomial.X (Sum.inl (x 2, 0)), ?_,
      fun s hs Y hY hle => absurd hle
        (not_starGrade_sup_le_of_finrank_le_two (by omega) hρ2 pa pb ?_)⟩
    · exact sub_ne_zero.mpr fun h => hinj.ne (by decide : (0 : Fin 3) ≠ 2)
        (congrArg Prod.fst (Sum.inl_injective (MvPolynomial.X_injective h)))
    · -- `y₁`, `y₃` have last coordinate `1` and different first coordinates
      have h0 : ∀ i, Y i 0 = s (Sum.inl ((x ∘ Fin.succAbove 1) i, 0)) := fun i => by
        rw [hY]; simp [earConfigGrade, earPictureGrade, hxV₁]
      have hl : ∀ i, Y i (Fin.last (m + 2)) = 1 := fun i => by rw [hY]; simp [earConfigGrade]
      have hs' : s (Sum.inl (x 0, 0)) - s (Sum.inl (x 2, 0)) ≠ 0 := by simpa using hs
      rw [LinearIndependent.pair_iff]
      intro c d hcd
      have e0 := congr_fun hcd 0
      have el := congr_fun hcd (Fin.last (m + 2))
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, h0, hl] at e0 el
      change c * s (Sum.inl (x 0, 0)) + d * s (Sum.inl (x 2, 0)) = 0 at e0
      obtain rfl : d = -c := by linear_combination el
      have hc := (mul_eq_zero.mp (show c * (s (Sum.inl (x 0, 0)) - s (Sum.inl (x 2, 0))) = 0 by
        linear_combination e0)).resolve_right hs'
      exact ⟨hc, by simp [hc]⟩
  · -- `d + κ ≤ 6`: stars-three, moved to the ear data
    obtain ⟨f, hf₀, hf⟩ := exists_mvPolynomial_starsThree (k := m + 1) ρ
      (finrank_range_gradeSigma la) (finrank_range_gradeSigma lb) hκ hpa hpb
    have hv0 : ∀ i : Fin 2, (x ∘ Fin.succAbove 1) i = x 0 → i = 0 := by
      intro i h
      fin_cases i
      · rfl
      · exact absurd (hinj h) (by decide)
    have hvl : ∀ i : Fin 2, (x ∘ Fin.succAbove 1) i = x 2 → i = 1 := by
      intro i h
      fin_cases i
      · exact absurd (hinj h) (by decide)
      · rfl
    obtain ⟨g, ⟨s₀, hs₀⟩, hg⟩ := exists_mvPolynomial_earDataGrade_of_smul (V₁ := V₁) (q₁ := q₁)
      (z₁ := z₁) (xf := x 0) (xl := x 2) (X := Set.range x) (la := la) (lb := lb)
      (v := x ∘ Fin.succAbove 1) (hinj.comp (Fin.succAbove_right_injective)) (fun i => hxV₁ _)
      (fun i => Or.inr (Or.inr ⟨_, rfl⟩)) (hinj.ne (by decide))
      (fun Y => starGrade (Y 0) ⊔ starGrade (Y 1) ≤ ρ ⊔ Submodule.span K
          (Set.range fun i : Fin 3 =>
            normalsJoin (pathVertex pa Y pb i.castSucc) (pathVertex pa Y pb i.succ)) →
        ρ ⊔ Submodule.span K (Set.range fun i : Fin 3 =>
            normalsJoin (pathVertex pa Y pb i.castSucc) (pathVertex pa Y pb i.succ)) = ⊤)
      (fun Y c hc h => starsCond_of_smul ρ pa pb Y c hc h) (f := f)
      (by
        obtain ⟨Y, hY0, hY1, hYf⟩ := hf₀
        exact ⟨Y, fun i hi => hv0 i hi ▸ hY0, fun i hi => hvl i hi ▸ hY1, hYf⟩)
      (fun Y hYa hYb hYf => (hf Y (hYa 0 rfl) (hYb 1 rfl) hYf).2)
    refine ⟨g, fun h => hs₀ (by simp [h]), fun s hs Y hY => ?_⟩
    obtain rfl : Y = fun i j => earConfigGrade V₁ q₁ z₁ (x 0) (x 2) (Set.range x) la lb s
        ((x ∘ Fin.succAbove 1) i, j) := funext fun i => funext (hY i)
    exact hg s hs

/-- `thm:pencil-d-open-ear-three`: let `G` satisfy the standing hypotheses, with an open ear
`a − x 0 − x 1 − x 2 − b` on `V₁` of three interior bodies, its ends possibly adjacent, and let
`G″ = G.splitOff (x 1) (x 0) (x 2) (e 1)` be `G` with `x 1` suppressed. If the general
configurations of `G[V₁]` and `G″` attain with `m` heights, `2 ≤ m ≤ 4` (dimension `d = m + 2`
from four to six), so does that of `G`.

The proof is `Graph.X0AttainsGrade.of_openEar_splitOff_of_base` at `G″`
(`splitOff_ear_succAbove`), with the picture off glued-ends' polynomial `g` for `G[V₁]`
(`Graph.exists_mvPolynomial_gluedEnds`; `1` when the closed neighbourhoods of `a` and `b` meet)
and the heights off planes-meet's for `G″` (`Graph.exists_mvPolynomial_planesMeet`). Its insertion
hypothesis, at those base data, is the third condition and the insertion. Let `r` be the dimension
of `Graph.liftingPlanesDiff` of `G[V₁]`, at most `3`. If `r ≤ 2`, then `dim ρ ≤ 2`: by
`joinRelScrews_le_span_of_mem_closedNbhd` when the closed neighbourhoods of `a` and `b` meet, by
glued-ends otherwise. If `r = 3`, the planes meet in dimension `κ = 3 − min(m, 3)` by
planes-meet, so `d + κ ≤ 6`. Either way `exists_mvPolynomial_earDataGrade_starsCond_three` gives
the third condition, and `exists_insertion_earDataGrade` (`Grade/Short.lean`, at `n = 0`) puts
`x 1` back. The points `pa`, `pb` need not be independent, so the picture is not also taken off
the first coordinate of `q_a − q_b`. -/
theorem _root_.Graph.X0AttainsGrade.of_openEar_three [Infinite K] [Finite α] [Finite β]
    {G : Graph α β} (hG : G.IsX0Graph) {V₁ : Set α} {x : Fin 3 → α} {a b : α}
    {e : Fin 4 → β} (hm : 2 ≤ m) (hm4 : m ≤ 4) (hcover : V(G) = V₁ ∪ Set.range x)
    (hinj : Function.Injective x) (hxV₁ : ∀ i, x i ∉ V₁) (ha : a ∈ V₁) (hb : b ∈ V₁)
    (hab : a ≠ b)
    (hpath : ∀ i : Fin 4, G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (hsep : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁)
    (h₁ : (G.induce V₁).X0AttainsGrade K m)
    (h₂ : (G.splitOff (x 1) (x 0) (x 2) (e 1)).X0AttainsGrade K m) : G.X0AttainsGrade K m := by
  classical
  have hx : ∀ i j, i ≠ j → x i ≠ x j := fun i j h h' => h (hinj h')
  obtain ⟨hcover'', hinj'', hxV₁'', hpath'', hsep'', hdeg2⟩ :=
    splitOff_ear_succAbove (k := 0) hcover hinj hxV₁ ha hb hab hpath hsep
  have l1 : G.IsLink (e 1) (x 0) (x 1) := by
    have := hpath 1
    rwa [pathVertex_eq_of_val_eq a b x (i := 0) (by simp),
      pathVertex_eq_of_val_eq a b x (i := 1) (by simp)] at this
  have l2 : G.IsLink (e 2) (x 1) (x 2) := by
    have := hpath 2
    rwa [pathVertex_eq_of_val_eq a b x (i := 1) (by simp),
      pathVertex_eq_of_val_eq a b x (i := 2) (by simp)] at this
  -- `G″[V₁] = G[V₁]`
  have he₀ : ∀ p p', G.IsLink (e 1) p p' → p ∉ V₁ ∨ p' ∉ V₁ := fun p p' h => by
    rcases h.eq_and_eq_or_eq_and_eq l1 with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> exact Or.inl (hxV₁ _)
  obtain ⟨-, hind⟩ := induce_splitOff_ear (w := x 2) hcover hxV₁ ⟨1, rfl⟩ (hxV₁ 0) he₀
  -- the picture `q*` off glued-ends' polynomial `g` for `G[V₁]`
  have hS₁ : (G.induce V₁).Simple :=
    hG.simple.mono (G.induce_le (hcover ▸ Set.subset_union_left))
  have h3₁ : ∀ t ∈ V(G.induce V₁), 3 ≤ ((G.induce V₁).closedNbhd t).ncard := by
    obtain ⟨_, P₁, _, hP₁, hgood₁⟩ := h₁
    obtain ⟨q₁, hq₁⟩ := MvPolynomial.exists_eval_ne_zero hP₁
    exact fun t ht => (hgood₁ q₁ hq₁).1.three_le_ncard_closedNbhd ht
  obtain ⟨g, hg₀, hg⟩ : ∃ g : MvPolynomial (α × Fin 2) K, g ≠ 0 ∧
      (Disjoint ((G.induce V₁).closedNbhd a) ((G.induce V₁).closedNbhd b) →
        ∀ q, MvPolynomial.eval q g ≠ 0 →
        Module.finrank K ((G.induce V₁).liftingPlanesDiff q a b) ≤ 2 → ∀ z : α × Fin m → K,
          Module.finrank K (joinRelScrews (G.induce V₁) (pencilConfigPointGrade q z) a b) ≤
            Module.finrank K ((G.induce V₁).liftingPlanesDiff q a b)) := by
    by_cases hd : Disjoint ((G.induce V₁).closedNbhd a) ((G.induce V₁).closedNbhd b)
    · obtain ⟨g, hg, hgg⟩ := Graph.exists_mvPolynomial_gluedEnds (K := K) hS₁ h3₁
        (by simpa using ha) (by simpa using hb) hd
      exact ⟨g, hg, fun _ q hq hr z => hgg q hq hr m z⟩
    · exact ⟨1, one_ne_zero, fun h => absurd h hd⟩
  -- the heights `z*` off planes-meet's polynomial for `G″` and its ear `a − x 0 − x 2 − b`
  have hpm := fun (q : α × Fin 2 → K)
      (hq : (G.splitOff (x 1) (x 0) (x 2) (e 1)).IsAdmissiblePicture q) =>
    Graph.exists_mvPolynomial_planesMeet (m := m) hcover'' hinj'' hxV₁'' ha hb hab hpath'' hsep''
      hq
  choose! Rz hRz hRzκ using hpm
  refine Graph.X0AttainsGrade.of_openEar_splitOff_of_base (k := 2) hG le_rfl hcover hinj hxV₁ ha
    hb hab hpath hsep hcover'' hinj'' hxV₁'' hpath'' hsep''
    (by rintro _ ⟨i, rfl⟩; exact ⟨_, rfl⟩) ⟨1, rfl⟩ (hxV₁ 0) l1 ?_
    (Graph.splitOff_deficiency_le_of_eq_left (n := m + 2)
      (by rw [Graph.bodyBarDim_add_one_eq_screwDim]; have := three_le_screwDim_succ (m := m); omega)
      (hx 0 1 (by decide)) (hx 1 2 (by decide)).symm l1.symm l2 hdeg2) (xf := x 0) (xl := x 2)
      rfl rfl (hx 0 1 (by decide)).symm (hx 1 2 (by decide)) hg₀ hRz
      (fun q z zs la lb hgq hadm hzs hRzs hz hla hlb => ?_) h₁ h₂
  · -- the relinked edge `e 1` joins `x 0` to `x 2` in `G″`
    have h := hpath'' 1
    have s0 : (Fin.succAbove 1 (0 : Fin 2) : Fin 3) = 0 := rfl
    have s1 : (Fin.succAbove 1 (1 : Fin 2) : Fin 3) = 2 := rfl
    rw [pathVertex_eq_of_val_eq a b _ (i := 0) (by simp),
      pathVertex_eq_of_val_eq a b _ (i := 1) (by simp)] at h
    simp only [Function.comp_apply, s0, s1] at h
    exact h
  -- the insertion hypothesis at the base data: `pa ∈ Π_a`, `pb ∈ Π_b`
  have hpa : pencilConfigPointGrade q z a ∈ LinearMap.range (gradeSigma la) :=
    ⟨pencilPicturePoint q a, ((pencilConfigPointGrade_eq_gradeSigma_iff q z la a).mpr
      fun i => (hz a ha i).trans (hla i a (Or.inl rfl))).symm⟩
  have hpb : pencilConfigPointGrade q z b ∈ LinearMap.range (gradeSigma lb) :=
    ⟨pencilPicturePoint q b, ((pencilConfigPointGrade_eq_gradeSigma_iff q z lb b).mpr
      fun i => (hz b hb i).trans (hlb i b (Or.inl rfl))).symm⟩
  -- `dim ρ ≤ 2` when `r ≤ 2`, and `d + κ ≤ 6` when `r = 3`
  have hρκ : Module.finrank K (joinRelScrews (G.induce V₁) (pencilConfigPointGrade q z) a b) ≤ 2 ∨
      m + 1 + Module.finrank K
        ↥(LinearMap.range (gradeSigma la) ⊓ LinearMap.range (gradeSigma lb)) ≤ 5 := by
    have hr3 : Module.finrank K ((G.induce V₁).liftingPlanesDiff q a b) ≤ 3 := by
      simpa using Submodule.finrank_le ((G.induce V₁).liftingPlanesDiff q a b)
    rcases Nat.lt_or_ge (Module.finrank K ((G.induce V₁).liftingPlanesDiff q a b)) 3 with hr | hr
    · refine Or.inl ?_
      by_cases hd : Disjoint ((G.induce V₁).closedNbhd a) ((G.induce V₁).closedNbhd b)
      · exact (hg hd q hgq (by omega) z).trans (by omega)
      · obtain ⟨t, hta, htb⟩ := Set.not_disjoint_iff.mp hd
        refine (Submodule.finrank_mono
          (joinRelScrews_le_span_of_mem_closedNbhd _ hta htb)).trans ?_
        exact (finrank_span_le_card _).trans (by simpa using Finset.card_le_two)
    · refine Or.inr ?_
      have hκ := hRzκ q hadm zs hzs hRzs la lb hla hlb
      rw [hind, le_antisymm hr3 hr] at hκ
      rw [hκ]
      omega
  obtain ⟨g', hg'₀, hg'⟩ :=
    exists_mvPolynomial_earDataGrade_starsCond_three hinj hxV₁ hm _ hpa hpb hρκ
  exact ⟨g', hg'₀, fun s hs _ =>
    exists_insertion_earDataGrade hinj hxV₁ ha hb _ rfl rfl s (hg' s hs)⟩

end CombinatorialRigidity.Molecular
