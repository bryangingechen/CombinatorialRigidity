/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.ConditionLinear
public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Stars
public import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.Cut
public import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.Flat

/-!
# Two closed neighbourhoods of an ear meet in a subspace of general dimension

The node `lem:pencil-d-planes-meet` of `blueprint/src/chapter/pencil-d.tex`, `sec:pencil-d-short`:
`Graph.exists_mvPolynomial_planesMeet`, with the space of differences of lifting planes
`Graph.liftingPlanesDiff` (the `r` of the chapter).

The proof is the chapter's. The planes `la`, `lb` of a height are read off the three points of an
admissible closed neighbourhood by a fixed inverse matrix (`exists_inv_of_isAdmissiblePicture`), so
the rows `lb i - la i` of the chapter's `L(z)` are linear in `z`. The intersection of the two
planes has dimension `3 - rank` of those rows (`finrank_inf_range_gradeSigma`); the rows lie in the
differences of the lifting planes of `G[V₁]`, and each such difference is reached by extending
along the ear (`exists_mem_liftingPlanes_extend_ear`). Rank openness
(`exists_mvPolynomial_le_finrank_span_of_repr`) gives `R`. See `notes/Cleanup42.md` R-15 for the
departures from the chapter's text.
-/

@[expose] public section

open scoped Graph Matrix

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*} {m : ℕ}

/-- The differences `h_b − h_a` over the lifting planes (the `r`-space of `lem:pencil-d-glued-ends`
and `lem:pencil-d-planes-meet`). -/
def _root_.Graph.liftingPlanesDiff (G : Graph α β) (q : α × Fin 2 → K) (a b : α) :
    Submodule K (Fin 3 → K) :=
  (G.liftingPlanes q).map ((LinearMap.proj b : (α → Fin 3 → K) →ₗ[K] Fin 3 → K) - LinearMap.proj a)

theorem _root_.Graph.mem_liftingPlanesDiff {G : Graph α β} {q : α × Fin 2 → K} {a b : α}
    {d : Fin 3 → K} :
    d ∈ G.liftingPlanesDiff q a b ↔ ∃ h ∈ G.liftingPlanes q, h b - h a = d := by
  simp [Graph.liftingPlanesDiff]

/-- Off `V(G)` the lifting planes are free, so with `b ∉ V(G)` every difference `h_b − h_a` is
reached (by `Pi.single b w`). -/
theorem _root_.Graph.liftingPlanesDiff_eq_top_of_notMem {G : Graph α β} {q : α × Fin 2 → K}
    {a b : α} (hb : b ∉ V(G)) (hab : a ≠ b) : G.liftingPlanesDiff q a b = ⊤ := by
  classical
  refine eq_top_iff.mpr fun w _ => Graph.mem_liftingPlanesDiff.mpr
    ⟨Pi.single b w, fun e u v he => ?_, by simp [hab]⟩
  have hu : u ≠ b := fun h => hb (h ▸ he.left_mem)
  have hv : v ≠ b := fun h => hb (h ▸ he.right_mem)
  simp [hu, hv]

/-- **A fixed inverse reads the plane off the heights** (a step of `lem:pencil-d-planes-meet`):
at a body `v` of an admissible picture there are three members `t` of the closed neighbourhood and
a matrix `N` such that every affine function `h` agreeing with a height `z` on the closed
neighbourhood is `N` applied to the values of `z` at `t`. `N` is the inverse of the matrix of the
three independent picture points. -/
theorem exists_inv_of_isAdmissiblePicture {G : Graph α β} {q : α × Fin 2 → K}
    (hq : G.IsAdmissiblePicture q) {v : α} (hv : v ∈ V(G)) :
    ∃ (t : Fin 3 → α) (N : Matrix (Fin 3) (Fin 3) K), (∀ i, t i ∈ G.closedNbhd v) ∧
      ∀ (z : α → K) (h : Fin 3 → K), (∀ w ∈ G.closedNbhd v, z w = h ⬝ᵥ pencilPicturePoint q w) →
        h = N *ᵥ fun j => z (t j) := by
  obtain ⟨t, ht, hli⟩ := hq.2 v hv
  set M : Matrix (Fin 3) (Fin 3) K := Matrix.of fun i => pencilPicturePoint q (t i) with hM
  have hu : IsUnit M.det := by
    rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_row_iff_isUnit]
    exact hli
  refine ⟨t, M⁻¹, ht, fun z h hh => ?_⟩
  have : (M *ᵥ h) = fun j => z (t j) := by
    funext j
    rw [hh _ (ht j), dotProduct_comm]
    rfl
  rw [← this, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

/-- **The intersection of two images of `σ`** (a step of `lem:pencil-d-planes-meet`): the common
vectors of the images of `σ_la` and `σ_lb` have dimension `3 − rank` of the rows `lb i − la i`:
they are `σ_la` of the common kernel of the forms `ξ ↦ (lb i − la i) ⬝ᵥ ξ`. -/
theorem finrank_inf_range_gradeSigma (la lb : Fin m → Fin 3 → K) :
    Module.finrank K ↥(LinearMap.range (gradeSigma la) ⊓ LinearMap.range (gradeSigma lb)) =
      3 - Module.finrank K (Submodule.span K (Set.range fun i => lb i - la i)) := by
  set D : Matrix (Fin m) (Fin 3) K := Matrix.of fun i => lb i - la i with hD
  have hker : LinearMap.range (gradeSigma la) ⊓ LinearMap.range (gradeSigma lb) =
      (LinearMap.ker D.mulVecLin).map (gradeSigma la) := by
    ext x
    simp only [Submodule.mem_inf, LinearMap.mem_range, Submodule.mem_map, LinearMap.mem_ker,
      Matrix.mulVecLin_apply]
    constructor
    · rintro ⟨⟨ξ, rfl⟩, ξ', hξ'⟩
      have h0 := congr_fun hξ' 0
      have h1 := congr_fun hξ' 1
      have h2 := congr_fun hξ' (Fin.last (m + 2))
      simp only [gradeSigma_apply, gradeMk_apply_zero, gradeMk_apply_one,
        gradeMk_apply_last] at h0 h1 h2
      have hξ : ξ' = ξ := by
        funext j; fin_cases j
        · exact h0
        · exact h1
        · exact h2
      subst hξ
      refine ⟨ξ', ?_, rfl⟩
      funext i
      have := congr_fun (congr_arg gradeHeights hξ') i
      simp only [gradeSigma_apply, gradeHeights_gradeMk] at this
      simp only [hD, Matrix.mulVec, Matrix.of_apply, sub_dotProduct, Pi.zero_apply]
      rw [this]; ring
    · rintro ⟨ξ, hξ, rfl⟩
      refine ⟨⟨ξ, rfl⟩, ξ, ?_⟩
      refine gradeMk_ext rfl rfl (funext fun i => ?_) rfl
      have := congr_fun hξ i
      simp only [hD, Matrix.mulVec, Matrix.of_apply, sub_dotProduct, Pi.zero_apply] at this
      exact sub_eq_zero.mp (by simpa using this)
  rw [hker, ← (Submodule.equivMapOfInjective _ (gradeSigma_injective la) _).finrank_eq]
  have hrank := LinearMap.finrank_range_add_finrank_ker D.mulVecLin
  have hr : Module.finrank K (LinearMap.range D.mulVecLin) =
      Module.finrank K (Submodule.span K (Set.range fun i => lb i - la i)) := by
    rw [← Matrix.rank, Matrix.rank_eq_finrank_span_row]
    rfl
  simp only [Module.finrank_fin_fun] at hrank
  omega


/-- The ear's two interior links and the two ends, read off the path (a step of
`lem:pencil-d-planes-meet`). -/
theorem isLink_ear_two {G : Graph α β} {y : Fin 2 → α} {a b : α} {e : Fin 3 → β}
    (hpath : ∀ i : Fin 3, G.IsLink (e i) (pathVertex a y b i.castSucc) (pathVertex a y b i.succ)) :
    G.IsLink (e 0) a (y 0) ∧ G.IsLink (e 1) (y 0) (y 1) ∧ G.IsLink (e 2) (y 1) b := by
  refine ⟨?_, ?_, ?_⟩
  · have := hpath 0
    rwa [pathVertex_eq_of_val_eq_zero a y b (m := (0 : Fin 3).castSucc) rfl,
      pathVertex_eq_of_val_eq_succ a y b (m := (0 : Fin 3).succ) (i := 0) rfl] at this
  · have := hpath 1
    rwa [pathVertex_eq_of_val_eq_succ a y b (m := (1 : Fin 3).castSucc) (i := 0) rfl,
      pathVertex_eq_of_val_eq_succ a y b (m := (1 : Fin 3).succ) (i := 1) rfl] at this
  · have := hpath 2
    rwa [pathVertex_eq_of_val_eq_succ a y b (m := (2 : Fin 3).castSucc) (i := 1) rfl,
      pathVertex_eq_of_val_eq_last a y b (m := (2 : Fin 3).succ) rfl] at this


/-- At a body of an admissible picture, a vector orthogonal to every picture point of the closed
neighbourhood is zero (a step of `lem:pencil-d-planes-meet`). -/
theorem eq_zero_of_dotProduct_closedNbhd {G : Graph α β} {q : α × Fin 2 → K}
    (hq : G.IsAdmissiblePicture q) {v : α} (hv : v ∈ V(G)) {x : Fin 3 → K}
    (hx : ∀ w ∈ G.closedNbhd v, x ⬝ᵥ pencilPicturePoint q w = 0) : x = 0 := by
  obtain ⟨t, N, -, hN⟩ := exists_inv_of_isAdmissiblePicture hq hv
  have := hN (fun _ => 0) x fun w hw => by rw [hx w hw]
  rw [this]
  exact Matrix.mulVec_zero N

/-- **The ear extension** (a step of `lem:pencil-d-planes-meet`, its `E = E(G[V₁])`): a family of
lifting planes of `G[V₁]` extends along the open ear `a − y 0 − y 1 − b` to one of `G` with the
same values at `a` and `b`. The two new planes are `h_a + c₁ ℓ₁` and `h_a + c₁ ℓ₁ + c₂ ℓ₂`, where
`ℓ₁, ℓ₂, ℓ₃` are the cross products of the picture points of consecutive path vertices; they are
independent, since the closed neighbourhoods of `y 0` and `y 1` hold three independent picture
points. -/
theorem exists_mem_liftingPlanes_extend_ear {G : Graph α β} {V₁ : Set α} {y : Fin 2 → α}
    {a b : α} {e : Fin 3 → β}
    (hinj : Function.Injective y) (hyV₁ : ∀ i, y i ∉ V₁) (ha : a ∈ V₁) (hb : b ∈ V₁)
    (hpath : ∀ i : Fin 3, G.IsLink (e i) (pathVertex a y b i.castSucc) (pathVertex a y b i.succ))
    (hsep : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁)
    {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) {h : α → Fin 3 → K}
    (hh : h ∈ (G.induce V₁).liftingPlanes q) :
    ∃ h' ∈ G.liftingPlanes q, h' a = h a ∧ h' b = h b := by
  classical
  obtain ⟨l0, l1, l2⟩ := isLink_ear_two hpath
  have y01 : y 0 ≠ y 1 := fun h => by simpa using hinj h
  have ay0 : a ≠ y 0 := fun h => hyV₁ 0 (h ▸ ha)
  have ay1 : a ≠ y 1 := fun h => hyV₁ 1 (h ▸ ha)
  have by0 : b ≠ y 0 := fun h => hyV₁ 0 (h ▸ hb)
  have by1 : b ≠ y 1 := fun h => hyV₁ 1 (h ▸ hb)
  have hy0V : y 0 ∈ V(G) := l0.right_mem
  have hy1V : y 1 ∈ V(G) := l1.right_mem
  -- the closed neighbourhoods of the interior bodies
  have nb : ∀ i, ∀ p ∈ G.closedNbhd (y i), ∀ f, G.IsLink f (y i) p →
      f = e 0 ∨ f = e 1 ∨ f = e 2 := by
    intro i p _ f hf
    by_contra hne
    push Not at hne
    exact hyV₁ i (hsep f _ _ hf fun j => by fin_cases j <;> simp [hne]).1
  have nb0 : ∀ p ∈ G.closedNbhd (y 0), p = y 0 ∨ p = a ∨ p = y 1 := by
    rintro p (rfl | ⟨f, hf⟩)
    · exact Or.inl rfl
    · rcases nb 0 p (Or.inr ⟨f, hf⟩) f hf with rfl | rfl | rfl
      · rcases hf.eq_and_eq_or_eq_and_eq l0 with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact absurd h1.symm ay0
        · exact Or.inr (Or.inl h2)
      · rcases hf.eq_and_eq_or_eq_and_eq l1 with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact Or.inr (Or.inr h2)
        · exact absurd h1 y01
      · rcases hf.eq_and_eq_or_eq_and_eq l2 with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact absurd h1 y01
        · exact absurd h1 by0.symm
  have nb1 : ∀ p ∈ G.closedNbhd (y 1), p = y 1 ∨ p = y 0 ∨ p = b := by
    rintro p (rfl | ⟨f, hf⟩)
    · exact Or.inl rfl
    · rcases nb 1 p (Or.inr ⟨f, hf⟩) f hf with rfl | rfl | rfl
      · rcases hf.eq_and_eq_or_eq_and_eq l0 with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact absurd h1 ay1.symm
        · exact absurd h1 y01.symm
      · rcases hf.eq_and_eq_or_eq_and_eq l1 with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact absurd h1 y01.symm
        · exact Or.inr (Or.inl h2)
      · rcases hf.eq_and_eq_or_eq_and_eq l2 with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact Or.inr (Or.inr h2)
        · exact absurd h1.symm by1
  set pt := pencilPicturePoint q with hpt
  set ℓ₁ : Fin 3 → K := crossProduct (pt a) (pt (y 0)) with hℓ₁
  set ℓ₂ : Fin 3 → K := crossProduct (pt (y 0)) (pt (y 1)) with hℓ₂
  set ℓ₃ : Fin 3 → K := crossProduct (pt (y 1)) (pt b) with hℓ₃
  have c1a : ℓ₁ ⬝ᵥ pt a = 0 := by rw [hℓ₁, dotProduct_comm, dot_self_cross]
  have c10 : ℓ₁ ⬝ᵥ pt (y 0) = 0 := by rw [hℓ₁, dotProduct_comm, dot_cross_self]
  have c20 : ℓ₂ ⬝ᵥ pt (y 0) = 0 := by rw [hℓ₂, dotProduct_comm, dot_self_cross]
  have c21 : ℓ₂ ⬝ᵥ pt (y 1) = 0 := by rw [hℓ₂, dotProduct_comm, dot_cross_self]
  have c31 : ℓ₃ ⬝ᵥ pt (y 1) = 0 := by rw [hℓ₃, dotProduct_comm, dot_self_cross]
  have c3b : ℓ₃ ⬝ᵥ pt b = 0 := by rw [hℓ₃, dotProduct_comm, dot_cross_self]
  have n1 : ℓ₁ ≠ 0 := crossProduct_ne_zero_iff_linearIndependent.mpr
    (linearIndependent_pencilPicturePoint_pair (hq.1 _ _ _ l0))
  have n3 : ℓ₃ ≠ 0 := crossProduct_ne_zero_iff_linearIndependent.mpr
    (linearIndependent_pencilPicturePoint_pair (hq.1 _ _ _ l2))
  have n2 : ℓ₂ ≠ 0 := crossProduct_ne_zero_iff_linearIndependent.mpr
    (linearIndependent_pencilPicturePoint_pair (hq.1 _ _ _ l1))
  -- `ℓ₃` does not vanish at `y 0`, `ℓ₂` does not vanish at `a`
  have d30 : ℓ₃ ⬝ᵥ pt (y 0) ≠ 0 := fun h0 => n3 <|
    eq_zero_of_dotProduct_closedNbhd hq hy1V fun w hw => by
      rcases nb1 w hw with rfl | rfl | rfl <;> assumption
  have d2a : ℓ₂ ⬝ᵥ pt a ≠ 0 := fun h0 => n2 <|
    eq_zero_of_dotProduct_closedNbhd hq hy0V fun w hw => by
      rcases nb0 w hw with rfl | rfl | rfl <;> assumption
  have hli : LinearIndependent K ![ℓ₁, ℓ₂, ℓ₃] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hg
    have e0 := congr_arg (· ⬝ᵥ pt (y 0)) hg
    simp only [add_dotProduct, smul_dotProduct, c10, c20, smul_eq_mul, mul_zero, zero_add,
      zero_dotProduct] at e0
    have g3 : g 2 = 0 := (mul_eq_zero.mp e0).resolve_right d30
    have ea := congr_arg (· ⬝ᵥ pt a) hg
    simp only [add_dotProduct, smul_dotProduct, c1a, smul_eq_mul, mul_zero, zero_add, g3,
      zero_mul, add_zero, zero_dotProduct] at ea
    have g2 : g 1 = 0 := (mul_eq_zero.mp ea).resolve_right d2a
    rw [g2, g3, zero_smul, zero_smul, add_zero, add_zero] at hg
    have g1 : g 0 = 0 := (smul_eq_zero.mp hg).resolve_right n1
    intro i; fin_cases i <;> assumption
  have hspan := hli.span_eq_top_of_card_eq_finrank (by simp)
  have hmem : h b - h a ∈ Submodule.span K (Set.range ![ℓ₁, ℓ₂, ℓ₃]) := by
    rw [hspan]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hmem
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hc
  set h' : α → Fin 3 → K := fun v =>
    if v = y 0 then h a + c 0 • ℓ₁ else if v = y 1 then h a + c 0 • ℓ₁ + c 1 • ℓ₂ else h v
    with hh'
  have hV₁ : ∀ v ∈ V₁, h' v = h v := fun v hv => by
    have h0 : v ≠ y 0 := fun h => hyV₁ 0 (h ▸ hv)
    have h1 : v ≠ y 1 := fun h => hyV₁ 1 (h ▸ hv)
    simp [hh', h0, h1]
  have e0 : h' (y 0) = h a + c 0 • ℓ₁ := by simp [hh']
  have e1 : h' (y 1) = h a + c 0 • ℓ₁ + c 1 • ℓ₂ := by simp [hh', y01.symm]
  have hbeq : h b = h a + c 0 • ℓ₁ + c 1 • ℓ₂ + c 2 • ℓ₃ := by
    calc h b = h a + (h b - h a) := by abel
      _ = _ := by rw [← hc]; abel
  refine ⟨h', fun f u w hf => ?_, by rw [hV₁ a ha], by rw [hV₁ b hb]⟩
  have Qs : ∀ u w, ((h' u - h' w) ⬝ᵥ pt u = 0 ∧ (h' u - h' w) ⬝ᵥ pt w = 0) →
      ((h' w - h' u) ⬝ᵥ pt w = 0 ∧ (h' w - h' u) ⬝ᵥ pt u = 0) := fun u w ⟨h1, h2⟩ => by
    rw [← neg_sub, neg_dotProduct, neg_dotProduct, h1, h2]; simp
  by_cases hfe : ∀ i, f ≠ e i
  · obtain ⟨hu, hw⟩ := hsep f u w hf hfe
    rw [hV₁ u hu, hV₁ w hw]
    exact hh f u w (by simpa [Graph.induce_isLink] using ⟨hf, hu, hw⟩)
  · push Not at hfe
    obtain ⟨i, rfl⟩ := hfe
    have hpa : (h' a - h' (y 0)) ⬝ᵥ pt a = 0 ∧ (h' a - h' (y 0)) ⬝ᵥ pt (y 0) = 0 := by
      rw [hV₁ a ha, e0]
      simp [smul_dotProduct, c1a, c10]
    have hp1 : (h' (y 0) - h' (y 1)) ⬝ᵥ pt (y 0) = 0 ∧
        (h' (y 0) - h' (y 1)) ⬝ᵥ pt (y 1) = 0 := by
      rw [e0, e1]
      simp [smul_dotProduct, c20, c21]
    have hp2 : (h' (y 1) - h' b) ⬝ᵥ pt (y 1) = 0 ∧ (h' (y 1) - h' b) ⬝ᵥ pt b = 0 := by
      rw [hV₁ b hb, e1, hbeq]
      simp [smul_dotProduct, c31, c3b]
    fin_cases i
    · rcases hf.eq_and_eq_or_eq_and_eq l0 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hpa
      · exact Qs _ _ hpa
    · rcases hf.eq_and_eq_or_eq_and_eq l1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hp1
      · exact Qs _ _ hp1
    · rcases hf.eq_and_eq_or_eq_and_eq l2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hp2
      · exact Qs _ _ hp2


/-- **A height with prescribed planes at two bodies is a family of lifting planes** (a step of
`lem:pencil-d-planes-meet`): a height `z ∈ L(q)` and affine functions `ha`, `hb` agreeing with `z`
on the closed neighbourhoods of two bodies `a ≠ b` of `G` extend to a family in `F(q)`, as in
`Graph.finrank_liftingPlanes`. -/
theorem exists_mem_liftingPlanes_of_mem_liftingSpace {G : Graph α β} {q : α × Fin 2 → K}
    {z : α → K} (hz : z ∈ G.liftingSpace q) {a b : α} (ha : a ∈ V(G)) (hb : b ∈ V(G))
    (hab : a ≠ b) {pa pb : Fin 3 → K}
    (hpa : ∀ w ∈ G.closedNbhd a, z w = pa ⬝ᵥ pencilPicturePoint q w)
    (hpb : ∀ w ∈ G.closedNbhd b, z w = pb ⬝ᵥ pencilPicturePoint q w) :
    ∃ H ∈ G.liftingPlanes q, H a = pa ∧ H b = pb := by
  classical
  have hz' := (Graph.mem_liftingSpace.mp hz).2
  let H : α → Fin 3 → K := fun v =>
    if v = a then pa else if v = b then pb else
      if hv : v ∈ V(G) then (hz' v hv).choose else 0
  have hH : ∀ v ∈ V(G), ∀ w ∈ G.closedNbhd v, z w = H v ⬝ᵥ pencilPicturePoint q w := by
    intro v hv w hw
    by_cases h1 : v = a
    · subst h1; simpa [H] using hpa w hw
    by_cases h2 : v = b
    · subst h2; simpa [H, h1] using hpb w hw
    simpa [H, h1, h2, hv] using (hz' v hv).choose_spec w hw
  refine ⟨H, fun f u v hf => ?_, by simp [H], by simp [H, hab.symm]⟩
  have hu := hf.left_mem
  have hv := hf.right_mem
  have huv : u ∈ G.closedNbhd v := Or.inr ⟨f, hf.symm⟩
  have hvu : v ∈ G.closedNbhd u := Or.inr ⟨f, hf⟩
  refine ⟨?_, ?_⟩
  · rw [sub_dotProduct, ← hH u hu u (Or.inl rfl), ← hH v hv u huv, sub_self]
  · rw [sub_dotProduct, ← hH u hu v hvu, ← hH v hv v (Or.inl rfl), sub_self]

/-- **`Φ` of a family of lifting planes agrees with it on the closed neighbourhoods** (a step of
`lem:pencil-d-planes-meet`): at a body `v` of `G`, `Φ h` takes the value `h_v ⬝ (x_w, y_w, 1)` at
every `w` in the closed neighbourhood of `v`. -/
theorem _root_.Graph.liftingPlanesEval_apply_of_mem_closedNbhd {G : Graph α β}
    {q : α × Fin 2 → K} {h : α → Fin 3 → K} (hh : h ∈ G.liftingPlanes q) {v w : α}
    (hv : v ∈ V(G)) (hw : w ∈ G.closedNbhd v) :
    G.liftingPlanesEval q h w = h v ⬝ᵥ pencilPicturePoint q w := by
  have hwV := G.closedNbhd_subset_vertexSet hv hw
  rcases hw with rfl | ⟨f, hf⟩
  · simp [Graph.liftingPlanesEval, hwV]
  · have := (hh f w v hf.symm).1
    rw [sub_dotProduct, sub_eq_zero] at this
    simpa [Graph.liftingPlanesEval, hwV] using this


/-- `lem:pencil-d-planes-meet`: at an admissible picture of `G`, whose open ear `a − y 0 − y 1 − b`
on `V₁` has two interior bodies, general heights cut `Π_a ∩ Π_b` to dimension `3 − min(m, r)`, where
`r` is the dimension of the differences of lifting planes of `G[V₁]`. `R` is rank openness
(`exists_mvPolynomial_le_finrank_span_of_repr`) for the rows `lb i − la i`, which are linear in `z`
by `exists_inv_of_isAdmissiblePicture`: they lie in the differences of `G[V₁]`, and the ear
extension (`exists_mem_liftingPlanes_extend_ear`) reaches `min m r` independent rows. -/
theorem _root_.Graph.exists_mvPolynomial_planesMeet {G : Graph α β}
    {V₁ : Set α} {y : Fin 2 → α} {a b : α} {e : Fin 3 → β} (hcover : V(G) = V₁ ∪ Set.range y)
    (hinj : Function.Injective y) (hyV₁ : ∀ i, y i ∉ V₁) (ha : a ∈ V₁) (hb : b ∈ V₁) (hab : a ≠ b)
    (hpath : ∀ i : Fin 3, G.IsLink (e i) (pathVertex a y b i.castSucc) (pathVertex a y b i.succ))
    (hsep : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁)
    {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) :
    ∃ R : MvPolynomial (α × Fin m) K, (∃ z ∈ G.liftingSpaceGrade q m, MvPolynomial.eval z R ≠ 0) ∧
      ∀ z ∈ G.liftingSpaceGrade q m, MvPolynomial.eval z R ≠ 0 → ∀ la lb : Fin m → Fin 3 → K,
        (∀ i, ∀ p ∈ G.closedNbhd a, z (p, i) = la i ⬝ᵥ pencilPicturePoint q p) →
        (∀ i, ∀ p ∈ G.closedNbhd b, z (p, i) = lb i ⬝ᵥ pencilPicturePoint q p) →
        Module.finrank K ↥(LinearMap.range (gradeSigma la) ⊓ LinearMap.range (gradeSigma lb)) =
          3 - min m (Module.finrank K ((G.induce V₁).liftingPlanesDiff q a b)) := by
  classical
  have haV : a ∈ V(G) := hcover ▸ Or.inl ha
  have hbV : b ∈ V(G) := hcover ▸ Or.inl hb
  obtain ⟨ta, Na, hta, hNa⟩ := exists_inv_of_isAdmissiblePicture hq haV
  obtain ⟨tb, Nb, htb, hNb⟩ := exists_inv_of_isAdmissiblePicture hq hbV
  set E := (G.induce V₁).liftingPlanesDiff q a b with hE
  set r := Module.finrank K E with hr
  -- the rows `lb i − la i` as a function of the heights
  let F : (α × Fin m → K) → Fin m → Fin 3 → K := fun s i =>
    (Nb *ᵥ fun j => s (tb j, i)) - (Na *ᵥ fun j => s (ta j, i))
  have hF : ∀ z i la lb, (∀ p ∈ G.closedNbhd a, z (p, i) = la ⬝ᵥ pencilPicturePoint q p) →
      (∀ p ∈ G.closedNbhd b, z (p, i) = lb ⬝ᵥ pencilPicturePoint q p) → F z i = lb - la := by
    intro z i la lb h1 h2
    simp only [F]
    rw [← hNa (fun p => z (p, i)) la h1, ← hNb (fun p => z (p, i)) lb h2]
  let c : Fin m → Fin 3 → MvPolynomial (α × Fin m) K := fun i j =>
    (∑ k, MvPolynomial.C (Nb j k) * MvPolynomial.X (tb k, i)) -
      ∑ k, MvPolynomial.C (Na j k) * MvPolynomial.X (ta k, i)
  have hc : ∀ s i j, (Pi.basisFun K (Fin 3)).repr (F s i) j = MvPolynomial.eval s (c i j) := by
    intro s i j
    simp [F, c, Matrix.mulVec, dotProduct, map_sum]
  -- the rows lie in `E`
  have hup : ∀ z ∈ G.liftingSpaceGrade q m, ∀ i, F z i ∈ E := by
    intro z hz i
    have hzi := (Graph.mem_liftingSpaceGrade.mp hz) i
    obtain ⟨pa, hpa⟩ := (Graph.mem_liftingSpace.mp hzi).2 a haV
    obtain ⟨pb, hpb⟩ := (Graph.mem_liftingSpace.mp hzi).2 b hbV
    obtain ⟨H, hH, hHa, hHb⟩ :=
      exists_mem_liftingPlanes_of_mem_liftingSpace hzi haV hbV hab hpa hpb
    rw [hF z i pa pb hpa hpb, ← hHa, ← hHb, hE, Graph.mem_liftingPlanesDiff]
    refine ⟨H, fun f u w hf => hH f u w (by rw [Graph.induce_isLink] at hf; exact hf.1), rfl⟩
  -- some height reaches `min m r` independent rows
  have hlow : ∃ z ∈ G.liftingSpaceGrade q m,
      min m r ≤ Module.finrank K (Submodule.span K (Set.range (F z))) := by
    set B := Module.finBasis K E with hB
    have hNr : min m r ≤ r := min_le_right _ _
    have hNm : min m r ≤ m := min_le_left _ _
    let d : Fin m → Fin 3 → K := fun i =>
      if hi : i.val < min m r then (B ⟨i.val, lt_of_lt_of_le hi hNr⟩ : Fin 3 → K) else 0
    have hd : ∀ i, d i ∈ E := fun i => by
      by_cases hi : i.val < min m r
      · simp only [d, hi, dite_true]; exact (B _).2
      · simp only [d, hi, dite_false]; exact E.zero_mem
    have hex : ∀ i, ∃ h ∈ G.liftingPlanes q, h b - h a = d i := fun i => by
      obtain ⟨h, hh, hhd⟩ := Graph.mem_liftingPlanesDiff.mp (hd i)
      obtain ⟨h', hh', h1, h2⟩ := exists_mem_liftingPlanes_extend_ear hinj hyV₁ ha hb hpath hsep hq
        (fun f u w hf => hh f u w hf)
      exact ⟨h', hh', by rw [h1, h2, hhd]⟩
    choose H hH hHd using hex
    let z0 : α × Fin m → K := fun p => G.liftingPlanesEval q (H p.2) p.1
    have hz0 : z0 ∈ G.liftingSpaceGrade q m :=
      Graph.mem_liftingSpaceGrade.2 fun i => G.liftingPlanesEval_mem_liftingSpace (hH i)
    have hFz : ∀ i, F z0 i = d i := fun i => by
      rw [hF z0 i (H i a) (H i b)
        (fun p hp => G.liftingPlanesEval_apply_of_mem_closedNbhd (hH i) haV hp)
        (fun p hp => G.liftingPlanesEval_apply_of_mem_closedNbhd (hH i) hbV hp), hHd]
    refine ⟨z0, hz0, ?_⟩
    have hli : LinearIndependent K
        (fun i : Fin (min m r) => (B ⟨i.val, lt_of_lt_of_le i.2 hNr⟩ : Fin 3 → K)) := by
      have := (B.linearIndependent.comp (fun i : Fin (min m r) => (⟨i.val, lt_of_lt_of_le i.2 hNr⟩ :
        Fin r)) (fun i j hij => Fin.ext (by simpa using congrArg Fin.val hij)))
      exact this.map' E.subtype (Submodule.ker_subtype E)
    calc min m r = Module.finrank K (Submodule.span K (Set.range
          (fun i : Fin (min m r) => (B ⟨i.val, lt_of_lt_of_le i.2 hNr⟩ : Fin 3 → K)))) := by
            rw [finrank_span_eq_card hli]; simp
      _ ≤ _ := by
        refine Submodule.finrank_mono (Submodule.span_mono ?_)
        rintro _ ⟨i, rfl⟩
        refine ⟨⟨i.val, lt_of_lt_of_le i.2 hNm⟩, ?_⟩
        rw [hFz]; simp only [d, i.2, dite_true]
  obtain ⟨z₀, hz₀, hz₀r⟩ := hlow
  obtain ⟨Q, hQ₀, hQ⟩ := exists_mvPolynomial_le_finrank_span_of_repr (Pi.basisFun K (Fin 3)) F c hc
    hz₀r
  refine ⟨Q, ⟨z₀, hz₀, hQ₀⟩, fun z hz hQz la lb hla hlb => ?_⟩
  have hrows : (fun i => lb i - la i) = F z := funext fun i => (hF z i _ _ (hla i) (hlb i)).symm
  rw [finrank_inf_range_gradeSigma, hrows]
  have hge := hQ z hQz
  have hle : Module.finrank K (Submodule.span K (Set.range (F z))) ≤ min m r := by
    refine le_min ?_ ?_
    · exact (finrank_range_le_card (F z)).trans (by simp)
    · exact Submodule.finrank_mono (Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hup z hz i))
  rw [le_antisymm hle hge]

end CombinatorialRigidity.Molecular
