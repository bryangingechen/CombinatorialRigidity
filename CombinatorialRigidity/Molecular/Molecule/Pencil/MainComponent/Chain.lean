/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.Ear

/-!
# Cycles and ears in the `X₀` induction (Phase 40g CHAIN)

The base of the `X₀` induction and its two unconditional ear steps
(`blueprint/src/chapter/main-component.tex`, `sec:main-component-chain`; informal (MC-18)–(MC-21)
and (MC-134), Steps MC10, MC13 and MC20 of §(K-main)). Every step keeps CUT's contract
(`MainComponent/Cut.lean`): one picture off finitely many polynomials' zero sets, heights where two
Zariski-open conditions meet inside `L_G(q)`, and `Graph.x0Attains_of_exists` at the end. The ears
are described as in `MainComponent/Ear.lean`.

## Main statements

* `Graph.X0Attains.of_cycle` — **BASE** (the base of (MC-21)(a), `thm:pencil-x0-cycle`): a cycle
  on `k + 2 ≥ 3` bodies attains, over every infinite field, with no further hypothesis.
* `Graph.X0Attains.of_openEar` — **the open ear** ((MC-20), `thm:pencil-x0-open-ear`): under (H),
  an open ear with `k ≥ 5` interior bodies, its ends possibly adjacent, carries attainment from
  `G[V₁]` to `G`.
* `Graph.X0Attains.of_closedEar` — **the closed ear** ((MC-20), `thm:pencil-x0-closed-ear`): under
  (H), a closed ear with `k ≥ 2`, as CUT (`Graph.X0Attains.of_cutVertex`) plus BASE.

## Design

* **Ears and cycles as explicit paths** (the PI's decision 3, `notes/Phase40g.md`): BASE takes its
  cycle as an edge `ab` plus the path `a − x 0 − ⋯ − x (k − 1) − b`, the format of the ear steps,
  because its proof is the ear rank law at `V₁ = {a, b}`.
* **The chain span by one certificate, inside the fibre.** (MC-19)(b)'s "for any flag pair"
  becomes a witness: the height `1` at `x 1`, `x 2` and `0` elsewhere lies in `L_G(q)` at every
  admissible `q` (the interior heights of an ear are free, `Graph.mem_liftingSpace_of_ear`), and
  the closed hexagon `linearIndependent_pointJoin_certHexagon`, reached at a picture putting `a`
  and `b` at one point, makes six ear joins independent there. The span polynomial in the picture
  (`exists_mvPolynomial_linearIndependent_pointJoin_picture`), then in the heights
  (`exists_mvPolynomial_linearIndependent_pointJoin_heights`), carries the independence to the
  attaining heights. It needs two free middle heights, so `k ≥ 4`.
* **BASE needs no fibre intersection**: every closed neighbourhood of a cycle has three members, so
  every height on `V(G)` is a lifting height
  (`Graph.IsAdmissiblePicture.exists_dotProduct_of_ncard_closedNbhd_le_three`).
* **The closed ear reuses the ear's labels**: its far side is the cycle through `x 0` closed by
  `e 0`, so no fresh edge label is needed, and no chain span of a closed ear ((MC-19)(c)) is used.
* **The steps ask less of `G[V₁]` than the informal statement**: attainment there, and (H) at `G`
  only.
-/

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

/-! ## BASE: a cycle attains -/

/-- **The closed neighbourhoods of the ends of a cycle's closing edge**: `a` sees `b` and `x 0`,
and `b` sees `a` and `x (k − 1)`. -/
theorem _root_.Graph.closedNbhd_cycle_subset {G : Graph α β} {k : ℕ} {x : Fin k → α} {a b : α}
    {e : Fin (k + 1) → β} {f : β} (hk : 1 ≤ k) (hinj : Function.Injective x)
    (hxa : ∀ i, x i ≠ a) (hxb : ∀ i, x i ≠ b) (hab : a ≠ b) (hf : G.IsLink f a b)
    (hpath : ∀ i : Fin (k + 1),
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (honly : ∀ g u w, G.IsLink g u w → (∀ i, g ≠ e i) → g = f) :
    G.closedNbhd a ⊆ {a, b, x ⟨0, (by omega)⟩} ∧
      G.closedNbhd b ⊆ {b, a, x ⟨k - 1, (by omega)⟩} := by
  have hpv := pathVertex_injective hinj hxa hxb hab
  constructor
  · rintro w (rfl | ⟨g, hg⟩)
    · exact Or.inl rfl
    by_cases hge : ∃ i, g = e i
    · obtain ⟨i, rfl⟩ := hge
      rcases hg.eq_and_eq_or_eq_and_eq (hpath i) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have : i.castSucc = 0 := hpv (by rw [← h1, pathVertex_zero])
        have hi : i = 0 := Fin.castSucc_eq_zero_iff.mp this
        subst hi
        right; right
        rw [h2]
        exact pathVertex_eq_of_val_eq_succ a x b (by simp)
      · have : i.succ = 0 := hpv (by rw [← h1, pathVertex_zero])
        exact absurd this (Fin.succ_ne_zero i)
    · have hgf := honly g _ _ hg (fun i h => hge ⟨i, h⟩)
      subst hgf
      rcases hg.eq_and_eq_or_eq_and_eq hf with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact Or.inr (Or.inl h2)
      · exact absurd h1 hab
  · rintro w (rfl | ⟨g, hg⟩)
    · exact Or.inl rfl
    by_cases hge : ∃ i, g = e i
    · obtain ⟨i, rfl⟩ := hge
      rcases hg.eq_and_eq_or_eq_and_eq (hpath i) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have : i.castSucc = Fin.last (k + 1) := hpv (by rw [← h1, pathVertex_last])
        exact absurd (congrArg Fin.val this) (by simp; omega)
      · have : i.succ = Fin.last (k + 1) := hpv (by rw [← h1, pathVertex_last])
        have hi : i.val = k := by
          have := congrArg Fin.val this
          simp only [Fin.val_succ, Fin.val_last] at this
          omega
        right; right
        rw [h2]
        exact pathVertex_eq_of_val_eq_succ a x b (by simp; omega)
    · have hgf := honly g _ _ hg (fun i h => hge ⟨i, h⟩)
      subst hgf
      rcases hg.eq_and_eq_or_eq_and_eq hf with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact absurd h1.symm hab
      · exact Or.inr (Or.inl h2)

/-- **BASE, from a certificate** (Phase 40g CHAIN): the cycle `a − x 0 − ⋯ − x (k − 1) − b − a`
(`k ≥ 1`, so `k + 2 ≥ 3` bodies) attains, given `min (k + 2) 6` of its links whose joins are
independent at one configuration. Every height on `V(G)` is a lifting height (every closed
neighbourhood has three members); the cycle is the edge `ab` (the path brick at `k = 0`: rank `5`,
relative screws its hinge) plus an open ear on `{a, b}`, so the ear rank law gives the rank
`5 (k + 2) − 6 + λ` with `λ ≥ min (k + 2) 6`, against `def ≥ max 0 (k − 4)` from the partition
into single bodies. -/
theorem _root_.Graph.X0Attains.of_cycle_of_certificate [Infinite K] [Finite α] [Finite β]
    {G : Graph α β} {k : ℕ} {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β} {f : β}
    (hk : 1 ≤ k) (hcover : V(G) = {a, b} ∪ Set.range x) (hinj : Function.Injective x)
    (hxa : ∀ i, x i ≠ a) (hxb : ∀ i, x i ≠ b) (hab : a ≠ b) (hf : G.IsLink f a b)
    (hpath : ∀ i : Fin (k + 1),
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (honly : ∀ g u w, G.IsLink g u w → (∀ i, g ≠ e i) → g = f)
    {ι : Type*} [Fintype ι] (hcard : Fintype.card ι = min (k + 2) 6)
    (u w : ι → α) (g : ι → β) (hg : ∀ i, G.IsLink (g i) (u i) (w i))
    (q₀ : α × Fin 2 → K) (zs : α → K)
    (hli : LinearIndependent K
      (fun i => pointJoin (pencilConfigPoint q₀ zs (u i)) (pencilConfigPoint q₀ zs (w i)))) :
    G.X0Attains K := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have : Inhabited α := ⟨a⟩
  have hpv := pathVertex_injective hinj hxa hxb hab
  set V₁ : Set α := {a, b} with hV₁
  have hxV₁ : ∀ i, x i ∉ V₁ := by
    intro i h
    rcases h with h | h
    exacts [hxa i h, hxb i h]
  have hsep : ∀ g u w, G.IsLink g u w → (∀ i, g ≠ e i) → u ∈ V₁ ∧ w ∈ V₁ := by
    intro g' u' w' hg' hge
    have := honly g' u' w' hg' hge
    subst this
    rcases hg'.eq_and_eq_or_eq_and_eq hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨Or.inl rfl, Or.inr rfl⟩
    · exact ⟨Or.inr rfl, Or.inl rfl⟩
  have hcover' : V(G) = V₁ ∪ Set.range x := hcover
  -- every closed neighbourhood has at most three members
  have hN3 : ∀ v ∈ V(G), (G.closedNbhd v).ncard ≤ 3 := by
    intro v hv
    rw [hcover] at hv
    obtain ⟨hNa, hNb⟩ := G.closedNbhd_cycle_subset hk hinj hxa hxb hab hf hpath honly
    rcases hv with (rfl | rfl) | ⟨i, rfl⟩
    · exact (Set.ncard_le_ncard hNa (Set.toFinite _)).trans ((Set.ncard_insert_le _ _).trans
        (Nat.succ_le_succ (Set.ncard_pair_le _ _)))
    · exact (Set.ncard_le_ncard hNb (Set.toFinite _)).trans ((Set.ncard_insert_le _ _).trans
        (Nat.succ_le_succ (Set.ncard_pair_le _ _)))
    · exact G.ncard_closedNbhd_ear_le_three hinj hxV₁ (Or.inl rfl) (Or.inr rfl) hpath hsep i
  -- loopless, and three members in every closed neighbourhood
  have hloop : G.Loopless := by
    refine ⟨fun g v hg => ?_⟩
    by_cases hge : ∃ i, g = e i
    · obtain ⟨i, rfl⟩ := hge
      rcases hg.eq_and_eq_or_eq_and_eq (hpath i) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have := hpv (h1.symm.trans h2)
        exact absurd (congrArg Fin.val this) (by simp)
      · have := hpv (h1.symm.trans h2)
        exact absurd (congrArg Fin.val this) (by simp)
    · have := honly g v v hg (fun i h => hge ⟨i, h⟩)
      subst this
      rcases hg.eq_and_eq_or_eq_and_eq hf with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hab (h1.symm.trans h2)
      · exact hab (h2.symm.trans h1)
  have h3 : ∀ v ∈ V(G), 3 ≤ (G.closedNbhd v).ncard := by
    intro v hv
    rw [hcover] at hv
    have hmem : ∀ {y₁ y₂ y₃ : α}, y₁ ≠ y₂ → y₁ ≠ y₃ → y₂ ≠ y₃ → y₁ ∈ G.closedNbhd v →
        y₂ ∈ G.closedNbhd v → y₃ ∈ G.closedNbhd v → 3 ≤ (G.closedNbhd v).ncard := by
      intro y₁ y₂ y₃ h12 h13 h23 m1 m2 m3
      have hsub : ({y₁, y₂, y₃} : Set α) ⊆ G.closedNbhd v := by
        rintro _ (rfl | rfl | rfl) <;> assumption
      calc 3 = ({y₁, y₂, y₃} : Set α).ncard := by
            rw [Set.ncard_eq_three.mpr ⟨y₁, y₂, y₃, h12, h13, h23, rfl⟩]
        _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
    rcases hv with (rfl | rfl) | ⟨i, rfl⟩
    · exact hmem hab (fun h => hxa _ h.symm) (fun h => hxb _ h.symm) (Or.inl rfl) (Or.inr ⟨f, hf⟩)
        (Or.inr ⟨_, ear_isLink_first hpath hk⟩)
    · exact hmem hab.symm (fun h => hxb _ h.symm) (fun h => hxa _ h.symm) (Or.inl rfl)
        (Or.inr ⟨f, hf.symm⟩) (Or.inr ⟨_, (ear_isLink_last hpath hk).symm⟩)
    · have hl1 := hpath ⟨i.val + 1, (by omega)⟩
      have hl0 := hpath ⟨i.val, (by omega)⟩
      have hxi : pathVertex a x b (Fin.castSucc ⟨i.val + 1, (by omega)⟩) = x i :=
        pathVertex_eq_of_val_eq_succ a x b (by simp)
      have hxi' : pathVertex a x b (Fin.succ ⟨i.val, (by omega)⟩) = x i :=
        pathVertex_eq_of_val_eq_succ a x b (by simp)
      rw [hxi] at hl1
      rw [hxi'] at hl0
      refine hmem (y₁ := x i) (y₂ := pathVertex a x b (Fin.succ ⟨i.val + 1, (by omega)⟩))
        (y₃ := pathVertex a x b (Fin.castSucc ⟨i.val, (by omega)⟩)) ?_ ?_ ?_ (Or.inl rfl)
        (Or.inr ⟨_, hl1⟩) (Or.inr ⟨_, hl0.symm⟩)
      · rw [← hxi]; exact fun h => absurd (congrArg Fin.val (hpv h)) (by simp)
      · rw [← hxi]; exact fun h => absurd (congrArg Fin.val (hpv h)) (by simp)
      · exact fun h => absurd (congrArg Fin.val (hpv h))
          (by simp only [Fin.val_succ, Fin.val_castSucc]; omega)
  obtain ⟨Pm, hPm, hmain⟩ := G.exists_mvPolynomial_isMainPicture (K := K) hloop h3
  obtain ⟨Plam, hPlam₀, hPlam⟩ := exists_mvPolynomial_linearIndependent_pointJoin_picture zs u w hli
  have hPlamne : Plam ≠ 0 := fun h => hPlam₀ (by rw [h, map_zero])
  obtain ⟨q, hq⟩ := MvPolynomial.exists_eval_ne_zero (mul_ne_zero hPm hPlamne)
  rw [map_mul] at hq
  have hqmain := hmain q (left_ne_zero_of_mul hq)
  have hliq := hPlam q (right_ne_zero_of_mul hq)
  set ends := G.endsOf with hendsdef
  have hends : ∀ f u w, G.IsLink f u w → G.IsLink f (ends f).1 (ends f).2 :=
    fun f _ _ hf => G.isLink_endsOf hf.edge_mem
  -- every height on `V(G)` is a lifting height of the cycle
  set z := Graph.liftingRestrict V(G) zs with hzdef
  have hz : z ∈ G.liftingSpace q := by
    refine ⟨fun w hw => by simp [hzdef, Graph.liftingRestrict_apply, hw], fun v hv => ?_⟩
    exact hqmain.1.exists_dotProduct_of_ncard_closedNbhd_le_three hv (hN3 v hv) z
  have hliz : LinearIndependent K
      (fun i => pointJoin (pencilConfigPoint q z (u i)) (pencilConfigPoint q z (w i))) := by
    have heq : ∀ y ∈ V(G), pencilConfigPoint q z y = pencilConfigPoint q zs y :=
      fun y hy => funext fun t => pencilConfigPoint_liftingRestrict V(G) q zs hy t
    have hfun : (fun i => pointJoin (pencilConfigPoint q z (u i)) (pencilConfigPoint q z (w i)))
        = fun i => pointJoin (pencilConfigPoint q zs (u i)) (pencilConfigPoint q zs (w i)) := by
      funext i
      rw [heq _ (hg i).left_mem, heq _ (hg i).right_mem]
    rw [hfun]; exact hliq
  -- the ear rank law at `V₁ = {a, b}`
  set F := (PanelHingeFramework.ofNormals (k := 2) G ends
    (fun p => pencilConfigPoint q z p.1 p.2)).toBodyHinge with hFdef
  have hC : ∀ i, F.supportExtensor (e i) ≠ 0 :=
    fun i => hqmain.1.supportExtensor_ne_zero hends z (hpath i)
  have hear := BodyHingeFramework.finrank_span_rigidityRows_ear_eq F hinj hxV₁ (Or.inl rfl)
    (Or.inr rfl) hab hpath hsep hC
  -- the edge side: a one-hinge path
  set P := G.induce V₁ with hPdef
  have hpathP : ∀ i : Fin (0 + 1), P.IsLink ((fun _ => f) i)
      (pathVertex a (Fin.elim0 : Fin 0 → α) b i.castSucc)
      (pathVertex a (Fin.elim0 : Fin 0 → α) b i.succ) := by
    intro i
    have hi : i = 0 := Fin.ext (by have := i.isLt; omega)
    subst hi
    have h0 : pathVertex a (Fin.elim0 : Fin 0 → α) b (Fin.castSucc (0 : Fin (0 + 1))) = a :=
      pathVertex_zero _ _ _
    have h1 : pathVertex a (Fin.elim0 : Fin 0 → α) b (Fin.succ (0 : Fin (0 + 1))) = b :=
      pathVertex_last _ _ _
    rw [h0, h1]
    exact ⟨hf, Or.inl rfl, Or.inr rfl⟩
  have honlyP : ∀ g u w, P.IsLink g u w → ∃ i : Fin (0 + 1), g = (fun _ => f) i := by
    rintro g' u' w' ⟨hg', hu', hw'⟩
    refine ⟨0, honly g' u' w' hg' (fun i hi => ?_)⟩
    subst hi
    rcases hg'.eq_and_eq_or_eq_and_eq (hpath i) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases pathVertex_cases a x b i.succ with ⟨h0, -⟩ | ⟨j, -, hj⟩ | ⟨h0, -⟩
      · simp only [Fin.val_succ] at h0; omega
      · rw [hj] at h2; exact hxV₁ j (h2 ▸ hw')
      · rcases pathVertex_cases a x b i.castSucc with ⟨h0', -⟩ | ⟨j, -, hj⟩ | ⟨h0', -⟩
        · simp only [Fin.val_succ, Fin.val_castSucc] at h0 h0'; omega
        · rw [hj] at h1; exact hxV₁ j (h1 ▸ hu')
        · simp only [Fin.val_castSucc] at h0'; omega
    · rcases pathVertex_cases a x b i.succ with ⟨h0, -⟩ | ⟨j, -, hj⟩ | ⟨h0, -⟩
      · simp only [Fin.val_succ] at h0; omega
      · rw [hj] at h1; exact hxV₁ j (h1 ▸ hu')
      · rcases pathVertex_cases a x b i.castSucc with ⟨h0', -⟩ | ⟨j, -, hj⟩ | ⟨h0', -⟩
        · simp only [Fin.val_succ, Fin.val_castSucc] at h0 h0'; omega
        · rw [hj] at h2; exact hxV₁ j (h2 ▸ hw')
        · simp only [Fin.val_castSucc] at h0'; omega
  have hCf : F.supportExtensor f ≠ 0 := hqmain.1.supportExtensor_ne_zero hends z hf
  have hFV₁ : F.graph.induce V₁ = P := by
    rw [hFdef, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph, ← hPdef]
  have hrankP : Module.finrank K (Submodule.span K
      (⟨F.graph.induce V₁, F.supportExtensor⟩ : BodyHingeFramework K 2 α β).rigidityRows) = 5 := by
    rw [hFV₁]
    have h1 := BodyHingeFramework.finrank_span_rigidityRows_path_le P F.supportExtensor hpathP
      honlyP (fun _ => hCf)
    have h2 := BodyHingeFramework.le_finrank_span_rigidityRows_path P F.supportExtensor
      (x := (Fin.elim0 : Fin 0 → α)) (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0) hab
      hpathP honlyP (fun _ => hCf)
    have hs : screwDim 2 = 6 := rfl
    rw [hs] at h1 h2
    exact le_antisymm h1 h2
  have hrelP : (⟨F.graph.induce V₁, F.supportExtensor⟩ : BodyHingeFramework K 2 α β).relScrews a b
      = Submodule.span K {F.supportExtensor f} := by
    rw [hFV₁]
    have hpvP := pathVertex_injective (x := (Fin.elim0 : Fin 0 → α)) (fun i => i.elim0)
      (fun i => i.elim0) (fun i => i.elim0) hab
    rw [le_antisymm (BodyHingeFramework.relScrews_path_le_span_range P F.supportExtensor hpathP)
      (BodyHingeFramework.span_range_le_relScrews_path P F.supportExtensor hpvP hpathP honlyP)]
    congr 1
    ext y
    simp [eq_comm]
  rw [hrankP, hrelP] at hear
  -- the span of all hinges has dimension at least `min (k + 2) 6`
  have hdim := card_le_finrank_of_linearIndependent_pointJoin hends (pencilConfigPoint q z) u w g
    hg hliz (Submodule.span K {F.supportExtensor f}
      ⊔ Submodule.span K (Set.range (F.supportExtensor ∘ e))) (by
      intro i
      by_cases hge : ∃ j, g i = e j
      · obtain ⟨j, hj⟩ := hge
        rw [hj]
        exact Submodule.mem_sup_right (Submodule.subset_span ⟨j, rfl⟩)
      · rw [honly _ _ _ (hg i) (fun j h => hge ⟨j, h⟩)]
        exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _))
  rw [hcard] at hdim
  -- the deficiency: the partition into singletons
  have hVcard : V(G).ncard = k + 2 := by
    rw [hcover, Set.ncard_union_eq _ (Set.toFinite _) (Set.toFinite _), Set.ncard_pair hab,
      Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]
    · ring
    · refine Set.disjoint_left.mpr ?_
      rintro _ (rfl | rfl) ⟨i, hi⟩
      exacts [hxa i hi, hxb i hi]
  have hE : E(G) ⊆ insert f (Set.range e) := by
    intro g' hg'
    obtain ⟨u', w', hl⟩ := G.exists_isLink_of_mem_edgeSet hg'
    by_cases hge : ∃ j, g' = e j
    · obtain ⟨j, rfl⟩ := hge; exact Or.inr ⟨j, rfl⟩
    · exact Or.inl (honly _ _ _ hl (fun j h => hge ⟨j, h⟩))
  have hre : (Set.range e).ncard ≤ k + 1 := by
    rw [← Nat.card_coe_set_eq]; exact (Finite.card_range_le _).trans (by simp)
  have hEcard : E(G).ncard ≤ k + 2 :=
    (Set.ncard_le_ncard hE (Set.toFinite _)).trans ((Set.ncard_insert_le _ _).trans
      (by omega))
  have hdef0 : (0 : ℤ) ≤ G.deficiency 3 := G.deficiency_nonneg 3 ⟨a, hcover ▸ Or.inl (Or.inl rfl)⟩
  have hdef1 : (k : ℤ) - 4 ≤ G.deficiency 3 := by
    have hp := G.partitionDef_le_deficiency 3 id
    have hnp : G.numParts id = k + 2 := by rw [Graph.numParts, Set.image_id, hVcard]
    have hce : (G.crossingEdges id).ncard ≤ k + 2 :=
      (Set.ncard_le_ncard (fun g' hg' => hg'.1) (Set.toFinite _)).trans hEcard
    rw [Graph.partitionDef, hnp] at hp
    have hb3 : (Graph.bodyBarDim 3 : ℤ) = 6 := rfl
    rw [hb3] at hp
    have hce' : ((G.crossingEdges id).ncard : ℤ) ≤ k + 2 := by exact_mod_cast hce
    push_cast at hp
    linarith
  refine Graph.x0Attains_of_exists ⟨a, hcover ▸ Or.inl (Or.inl rfl)⟩ ends hends hqmain hz ?_
  have hs : (screwDim 2 : ℤ) = 6 := rfl
  have e1 : (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
      = (5 : ℕ) + ((screwDim 2 : ℤ) - 1) * (k + 1)
        + (Module.finrank K ↥(Submodule.span K {F.supportExtensor f}
            ⊔ Submodule.span K (Set.range (F.supportExtensor ∘ e))) : ℤ) - (screwDim 2 : ℤ) := hear
  rw [e1, hs, hVcard]
  have hdim' : (min (k + 2) 6 : ℕ) ≤ Module.finrank K ↥(Submodule.span K {F.supportExtensor f}
      ⊔ Submodule.span K (Set.range (F.supportExtensor ∘ e))) := hdim
  rcases le_total (k + 2) 6 with hk6 | hk6
  · rw [min_eq_left hk6] at hdim'
    have : ((k + 2 : ℕ) : ℤ) ≤ (Module.finrank K ↥(Submodule.span K {F.supportExtensor f}
      ⊔ Submodule.span K (Set.range (F.supportExtensor ∘ e))) : ℤ) := by exact_mod_cast hdim'
    push_cast at this ⊢
    linarith
  · rw [min_eq_right hk6] at hdim'
    have : ((6 : ℕ) : ℤ) ≤ (Module.finrank K ↥(Submodule.span K {F.supportExtensor f}
      ⊔ Submodule.span K (Set.range (F.supportExtensor ∘ e))) : ℤ) := by exact_mod_cast hdim'
    push_cast at this ⊢
    linarith

/-- **BASE: a cycle attains** (Phase 40g CHAIN, `thm:pencil-x0-cycle`; the base of (MC-21)(a)):
the cycle `a − x 0 − ⋯ − x (k − 1) − b − a` on `k + 2 ≥ 3` bodies attains on `X₀`, over every
infinite field, with no further hypothesis. The certificate is the closed polygon on `k + 2`
bodies for `k + 2 ≤ 5` (`linearIndependent_pointJoin_certTriangle`, `…Square`, `…Pentagon`), and
for `k + 2 ≥ 6` the hexagon with `x 3, …, x (k − 1)` collapsed onto one point. -/
theorem _root_.Graph.X0Attains.of_cycle [Infinite K] [Finite α] [Finite β]
    {G : Graph α β} {k : ℕ} {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β} {f : β}
    (hk : 1 ≤ k) (hcover : V(G) = {a, b} ∪ Set.range x) (hinj : Function.Injective x)
    (hxa : ∀ i, x i ≠ a) (hxb : ∀ i, x i ≠ b) (hab : a ≠ b) (hf : G.IsLink f a b)
    (hpath : ∀ i : Fin (k + 1),
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (honly : ∀ g u w, G.IsLink g u w → (∀ i, g ≠ e i) → g = f) :
    G.X0Attains K := by
  classical
  have hxne : ∀ {i j : Fin k}, i.val ≠ j.val → x i ≠ x j := fun hij h => hij (congrArg _ (hinj h))
  have hcert := fun {ι : Type} [Fintype ι] (hcard : Fintype.card ι = min (k + 2) 6)
      (u w : ι → α) (g : ι → β) (hg : ∀ i, G.IsLink (g i) (u i) (w i)) (lab : α → Fin 6)
      (hli : LinearIndependent K (fun i => pointJoin (certPt (lab (u i))) (certPt (lab (w i))))) =>
    Graph.X0Attains.of_cycle_of_certificate (K := K) hk hcover hinj hxa hxb hab hf hpath honly
      hcard u w g hg (certPicture lab) (certHeights lab) (by
        simp only [pencilConfigPoint_cert]; exact hli)
  obtain hk4 | hk3 | hk2 | hk1 : 4 ≤ k ∨ k = 3 ∨ k = 2 ∨ k = 1 := by omega
  · -- `k + 2 ≥ 6`: the hexagon, collapsing `x 3, …, x (k - 1)`
    set x0 := x ⟨0, (by omega)⟩
    set x1 := x ⟨1, (by omega)⟩
    set x2 := x ⟨2, (by omega)⟩
    set x3 := x ⟨3, (by omega)⟩
    set xl := x ⟨k - 1, (by omega)⟩
    set lab : α → Fin 6 := fun v => if v = x0 then 1 else if v = x1 then 2 else if v = x2 then 3
      else if v = b then 5 else if v = a then 0 else 4 with hlab
    have x01 : x0 ≠ x1 := hxne (by simp)
    have x02 : x0 ≠ x2 := hxne (by simp)
    have x12 : x1 ≠ x2 := hxne (by simp)
    have x30 : x3 ≠ x0 := hxne (by simp)
    have x31 : x3 ≠ x1 := hxne (by simp)
    have x32 : x3 ≠ x2 := hxne (by simp)
    have xl0 : xl ≠ x0 := hxne (by simp; omega)
    have xl1 : xl ≠ x1 := hxne (by simp; omega)
    have xl2 : xl ≠ x2 := hxne (by simp; omega)
    have la : lab a = 0 := by
      have ha0 : a ≠ x0 := (hxa _).symm
      have ha1 : a ≠ x1 := (hxa _).symm
      have ha2 : a ≠ x2 := (hxa _).symm
      simp [hlab, hab, ha0, ha1, ha2]
    have lb : lab b = 5 := by
      have hb0 : b ≠ x0 := (hxb _).symm
      have hb1 : b ≠ x1 := (hxb _).symm
      have hb2 : b ≠ x2 := (hxb _).symm
      simp [hlab, hb0, hb1, hb2]
    have l0 : lab x0 = 1 := by simp [hlab]
    have l1 : lab x1 = 2 := by simp [hlab, x01.symm]
    have l2 : lab x2 = 3 := by simp [hlab, x02.symm, x12.symm]
    have l3 : lab x3 = 4 := by
      simp [hlab, x30, x31, x32, show x3 ≠ b from hxb _, show x3 ≠ a from hxa _]
    have ll : lab xl = 4 := by
      simp [hlab, xl0, xl1, xl2, show xl ≠ b from hxb _, show xl ≠ a from hxa _]
    refine hcert (ι := Fin 6) (by simp; omega) ![a, x0, x1, x2, xl, b] ![x0, x1, x2, x3, b, a]
      ![e ⟨0, (by omega)⟩, e ⟨1, (by omega)⟩, e ⟨2, (by omega)⟩, e ⟨3, (by omega)⟩,
        e ⟨k, (by omega)⟩, f] ?_ lab ?_
    · intro i
      fin_cases i
      · exact ear_isLink_first hpath hk
      · exact ear_isLink_mid hpath 1 le_rfl (by omega)
      · exact ear_isLink_mid hpath 2 (by omega) (by omega)
      · exact ear_isLink_mid hpath 3 (by omega) (by omega)
      · exact ear_isLink_last hpath hk
      · exact hf.symm
    · have heq : (fun i : Fin 6 => pointJoin (certPt (K := K) (lab (![a, x0, x1, x2, xl, b] i)))
          (certPt (lab (![x0, x1, x2, x3, b, a] i))))
          = fun i : Fin 6 =>
          pointJoin (![certPt 0, certPt 1, certPt 2, certPt 3, certPt 4, certPt 5] i : Fin 4 → K)
            (![certPt 1, certPt 2, certPt 3, certPt 4, certPt 5, certPt 0] i) := by
        funext i
        fin_cases i
        · change pointJoin (certPt (lab a)) (certPt (lab x0)) = _; rw [la, l0]; rfl
        · change pointJoin (certPt (lab x0)) (certPt (lab x1)) = _; rw [l0, l1]; rfl
        · change pointJoin (certPt (lab x1)) (certPt (lab x2)) = _; rw [l1, l2]; rfl
        · change pointJoin (certPt (lab x2)) (certPt (lab x3)) = _; rw [l2, l3]; rfl
        · change pointJoin (certPt (lab xl)) (certPt (lab b)) = _; rw [ll, lb]; rfl
        · change pointJoin (certPt (lab b)) (certPt (lab a)) = _; rw [lb, la]; rfl
      rw [heq]; exact linearIndependent_pointJoin_certHexagon
  · -- `k = 3`: the pentagon
    subst hk3
    set lab : α → Fin 6 := fun v => if v = x 0 then 1 else if v = x 1 then 2 else if v = x 2 then 3
      else if v = b then 4 else 0 with hlab
    have la : lab a = 0 := by simp [hlab, (hxa _).symm, hab]
    have lb : lab b = 4 := by simp [hlab, (hxb _).symm]
    have l0 : lab (x 0) = 1 := by simp [hlab]
    have l1 : lab (x 1) = 2 := by simp [hlab, hxne (i := 1) (j := 0) (by simp)]
    have l2 : lab (x 2) = 3 := by
      simp [hlab, hxne (i := 2) (j := 0) (by simp), hxne (i := 2) (j := 1) (by simp)]
    refine hcert (ι := Fin 5) (by simp) ![a, x 0, x 1, x 2, b] ![x 0, x 1, x 2, b, a]
      ![e 0, e 1, e 2, e 3, f] ?_ lab ?_
    · intro i
      fin_cases i
      · exact ear_isLink_first hpath hk
      · exact ear_isLink_mid hpath 1 le_rfl (by omega)
      · exact ear_isLink_mid hpath 2 (by omega) (by omega)
      · exact ear_isLink_last hpath hk
      · exact hf.symm
    · have heq : (fun i : Fin 5 => pointJoin (certPt (K := K) (lab (![a, x 0, x 1, x 2, b] i)))
          (certPt (lab (![x 0, x 1, x 2, b, a] i))))
          = fun i : Fin 5 =>
          pointJoin (![certPt 0, certPt 1, certPt 2, certPt 3, certPt 4] i : Fin 4 → K)
            (![certPt 1, certPt 2, certPt 3, certPt 4, certPt 0] i) := by
        funext i
        fin_cases i
        · change pointJoin (certPt (lab a)) (certPt (lab (x 0))) = _; rw [la, l0]; rfl
        · change pointJoin (certPt (lab (x 0))) (certPt (lab (x 1))) = _; rw [l0, l1]; rfl
        · change pointJoin (certPt (lab (x 1))) (certPt (lab (x 2))) = _; rw [l1, l2]; rfl
        · change pointJoin (certPt (lab (x 2))) (certPt (lab b)) = _; rw [l2, lb]; rfl
        · change pointJoin (certPt (lab b)) (certPt (lab a)) = _; rw [lb, la]; rfl
      rw [heq]; exact linearIndependent_pointJoin_certPentagon
  · -- `k = 2`: the square
    subst hk2
    set lab : α → Fin 6 := fun v => if v = x 0 then 1 else if v = x 1 then 2 else if v = b then 3
      else 0 with hlab
    have la : lab a = 0 := by simp [hlab, (hxa _).symm, hab]
    have lb : lab b = 3 := by simp [hlab, (hxb _).symm]
    have l0 : lab (x 0) = 1 := by simp [hlab]
    have l1 : lab (x 1) = 2 := by simp [hlab, hxne (i := 1) (j := 0) (by simp)]
    refine hcert (ι := Fin 4) (by simp) ![a, x 0, x 1, b] ![x 0, x 1, b, a]
      ![e 0, e 1, e 2, f] ?_ lab ?_
    · intro i
      fin_cases i
      · exact ear_isLink_first hpath hk
      · exact ear_isLink_mid hpath 1 le_rfl (by omega)
      · exact ear_isLink_last hpath hk
      · exact hf.symm
    · have heq : (fun i : Fin 4 => pointJoin (certPt (K := K) (lab (![a, x 0, x 1, b] i)))
          (certPt (lab (![x 0, x 1, b, a] i))))
          = fun i : Fin 4 =>
          pointJoin (![certPt 0, certPt 1, certPt 2, certPt 3] i : Fin 4 → K)
            (![certPt 1, certPt 2, certPt 3, certPt 0] i) := by
        funext i
        fin_cases i
        · change pointJoin (certPt (lab a)) (certPt (lab (x 0))) = _; rw [la, l0]; rfl
        · change pointJoin (certPt (lab (x 0))) (certPt (lab (x 1))) = _; rw [l0, l1]; rfl
        · change pointJoin (certPt (lab (x 1))) (certPt (lab b)) = _; rw [l1, lb]; rfl
        · change pointJoin (certPt (lab b)) (certPt (lab a)) = _; rw [lb, la]; rfl
      rw [heq]; exact linearIndependent_pointJoin_certSquare
  · -- `k = 1`: the triangle
    subst hk1
    set lab : α → Fin 6 := fun v => if v = x 0 then 1 else if v = b then 2 else 0 with hlab
    have la : lab a = 0 := by simp [hlab, (hxa _).symm, hab]
    have lb : lab b = 2 := by simp [hlab, (hxb _).symm]
    have l0 : lab (x 0) = 1 := by simp [hlab]
    refine hcert (ι := Fin 3) (by simp) ![a, x 0, b] ![x 0, b, a] ![e 0, e 1, f] ?_ lab ?_
    · intro i
      fin_cases i
      · exact ear_isLink_first hpath hk
      · exact ear_isLink_last hpath hk
      · exact hf.symm
    · have heq : (fun i : Fin 3 => pointJoin (certPt (K := K) (lab (![a, x 0, b] i)))
          (certPt (lab (![x 0, b, a] i))))
          = fun i : Fin 3 =>
          pointJoin (![certPt 0, certPt 1, certPt 2] i : Fin 4 → K)
            (![certPt 1, certPt 2, certPt 0] i) := by
        funext i
        fin_cases i
        · change pointJoin (certPt (lab a)) (certPt (lab (x 0))) = _; rw [la, l0]; rfl
        · change pointJoin (certPt (lab (x 0))) (certPt (lab b)) = _; rw [l0, lb]; rfl
        · change pointJoin (certPt (lab b)) (certPt (lab a)) = _; rw [lb, la]; rfl
      rw [heq]; exact linearIndependent_pointJoin_certTriangle

/-! ## The open ear with at least five interior bodies -/

/-- **The open ear with at least five interior bodies** (Phase 40g CHAIN, `thm:pencil-x0-open-ear`;
(MC-20), open half): let `G` satisfy (H) with `V(G) = V₁ ∪ {x 0, …, x (k − 1)}`, the interior
bodies distinct and outside `V₁`, and let the path `a − x 0 − ⋯ − x (k − 1) − b` (`a ≠ b` in
`V₁`, possibly adjacent) carry `k + 1 ≥ 6` edges, every other edge lying inside `V₁`. If `X₀(G[V₁])`
attains, `X₀(G)` attains. At heights where `G[V₁]` attains and six ear joins are independent, the
ear hinges span the screw space, so the ear rank law adds `5 (k + 1)` to the rank, while the ear
deficiency bound lets the target grow by at most that. -/
theorem _root_.Graph.X0Attains.of_openEar [Infinite K] [Finite α] [Finite β] {G : Graph α β}
    (hG : G.IsX0Graph) {V₁ : Set α} {k : ℕ} {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β}
    (hk : 5 ≤ k) (hcover : V(G) = V₁ ∪ Set.range x) (hinj : Function.Injective x)
    (hxV₁ : ∀ i, x i ∉ V₁) (ha : a ∈ V₁) (hb : b ∈ V₁) (hab : a ≠ b)
    (hpath : ∀ i : Fin (k + 1),
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (hsep : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁)
    (h₁ : (G.induce V₁).X0Attains K) : G.X0Attains K := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have hV : V(G).Nonempty := hG.connected.nonempty
  have : Inhabited α := ⟨a⟩
  have hV₁G : V₁ ⊆ V(G) := hcover ▸ Set.subset_union_left
  have hle₁ : G.induce V₁ ≤ G := Graph.induce_le hV₁G
  have hax : ∀ i, x i ≠ a := fun i h => hxV₁ i (h ▸ ha)
  have hbx : ∀ i, x i ≠ b := fun i h => hxV₁ i (h ▸ hb)
  have hxne : ∀ {i j : Fin k}, i.val ≠ j.val → x i ≠ x j := fun hij h => hij (congrArg _ (hinj h))
  obtain ⟨ends₁, P₁, hends₁, hP₁, hgood₁⟩ := h₁
  obtain ⟨Pm, hPm, hmain⟩ := G.exists_mvPolynomial_isMainPicture (K := K)
    hG.simple.toLoopless hG.three_le_ncard_closedNbhd
  set ends := G.endsOf with hendsdef
  have hends : ∀ f u w, G.IsLink f u w → G.IsLink f (ends f).1 (ends f).2 :=
    fun f _ _ hf => G.isLink_endsOf hf.edge_mem
  have hendsI : ∀ f u w, (G.induce V₁).IsLink f u w →
      (G.induce V₁).IsLink f (ends f).1 (ends f).2 := by
    intro f u w hf
    have hl := hends f u w hf.1
    rcases hl.eq_and_eq_or_eq_and_eq hf.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨hl, h1 ▸ hf.2.1, h2 ▸ hf.2.2⟩
    · exact ⟨hl, h1 ▸ hf.2.2, h2 ▸ hf.2.1⟩
  -- the interior bodies used by the certificate
  set x0 := x ⟨0, (by omega)⟩ with hx0
  set x1 := x ⟨1, (by omega)⟩ with hx1
  set x2 := x ⟨2, (by omega)⟩ with hx2
  set x3 := x ⟨3, (by omega)⟩ with hx3
  set xm := x ⟨k - 2, (by omega)⟩ with hxm
  set xl := x ⟨k - 1, (by omega)⟩ with hxl
  -- the six certificate links: `a x0, x0 x1, x1 x2, x2 x3, xm xl, xl b`
  set u6 : Fin 6 → α := ![a, x0, x1, x2, xm, xl] with hu6
  set v6 : Fin 6 → α := ![x0, x1, x2, x3, xl, b] with hv6
  set f6 : Fin 6 → β := ![e ⟨0, (by omega)⟩, e ⟨1, (by omega)⟩, e ⟨2, (by omega)⟩,
    e ⟨3, (by omega)⟩, e ⟨k - 1, (by omega)⟩, e ⟨k, (by omega)⟩] with hf6
  have hl6 : ∀ i, G.IsLink (f6 i) (u6 i) (v6 i) := by
    intro i
    fin_cases i
    · exact ear_isLink_first hpath (by omega)
    · exact ear_isLink_mid hpath 1 le_rfl (by omega)
    · exact ear_isLink_mid hpath 2 (by omega) (by omega)
    · exact ear_isLink_mid hpath 3 (by omega) (by omega)
    · have h := ear_isLink_mid hpath (k - 1) (by omega) (by omega)
      have e1 : (⟨(k - 1) - 1, (by omega)⟩ : Fin k) = ⟨k - 2, (by omega)⟩ :=
        Fin.ext (by simp; omega)
      rw [e1] at h
      exact h
    · exact ear_isLink_last hpath (by omega)
  -- the certificate heights (`1` at `x1, x2`) and picture
  set zs : α → K := fun w => if w = x1 ∨ w = x2 then 1 else 0 with hzsdef
  set lab : α → Fin 6 := fun w => if w = x0 then 1 else if w = x1 then 2 else if w = x2 then 3
    else if w = xl then 5 else if w ∈ Set.range x then 4 else 0 with hlabdef
  set q₀ : α × Fin 2 → K := certPicture lab with hq₀def
  have x01 : x0 ≠ x1 := hxne (by simp)
  have x02 : x0 ≠ x2 := hxne (by simp)
  have x12 : x1 ≠ x2 := hxne (by simp)
  have x0l : x0 ≠ xl := hxne (by simp; omega)
  have x1l : x1 ≠ xl := hxne (by simp; omega)
  have x2l : x2 ≠ xl := hxne (by simp; omega)
  have x31 : x3 ≠ x1 := hxne (by simp)
  have x32 : x3 ≠ x2 := hxne (by simp)
  have x30 : x3 ≠ x0 := hxne (by simp)
  have x3l : x3 ≠ xl := hxne (by simp; omega)
  have xm1 : xm ≠ x1 := hxne (by simp; omega)
  have xm2 : xm ≠ x2 := hxne (by simp; omega)
  have xm0 : xm ≠ x0 := hxne (by simp; omega)
  have xml : xm ≠ xl := hxne (by simp; omega)
  have ha0 : a ≠ x0 := fun h => hax _ h.symm
  have ha1 : a ≠ x1 := fun h => hax _ h.symm
  have ha2 : a ≠ x2 := fun h => hax _ h.symm
  have hal : a ≠ xl := fun h => hax _ h.symm
  have hb0 : b ≠ x0 := fun h => hbx _ h.symm
  have hb1 : b ≠ x1 := fun h => hbx _ h.symm
  have hb2 : b ≠ x2 := fun h => hbx _ h.symm
  have hbl : b ≠ xl := fun h => hbx _ h.symm
  have har : a ∉ Set.range x := by rintro ⟨i, hi⟩; exact hax i hi
  have hbr : b ∉ Set.range x := by rintro ⟨i, hi⟩; exact hbx i hi
  have hx3r : ∃ y, x y = x3 := ⟨_, rfl⟩
  have hxmr : ∃ y, x y = xm := ⟨_, rfl⟩
  have pa : pencilConfigPoint q₀ zs a = certPt 0 := by
    have : lab a = 0 := by simp [hlabdef, ha0, ha1, ha2, hal, hax]
    rw [hq₀def, pencilConfigPoint_certPicture lab zs a (by simp [hzsdef, ha1, ha2, this, certPt]),
      this]
  have pb : pencilConfigPoint q₀ zs b = certPt 0 := by
    have : lab b = 0 := by simp [hlabdef, hb0, hb1, hb2, hbl, hbx]
    rw [hq₀def, pencilConfigPoint_certPicture lab zs b (by simp [hzsdef, hb1, hb2, this, certPt]),
      this]
  have p0 : pencilConfigPoint q₀ zs x0 = certPt 1 := by
    have : lab x0 = 1 := by simp [hlabdef]
    rw [hq₀def, pencilConfigPoint_certPicture lab zs x0 (by simp [hzsdef, x01, x02, this, certPt]),
      this]
  have p1 : pencilConfigPoint q₀ zs x1 = certPt 2 := by
    have : lab x1 = 2 := by simp [hlabdef, x01.symm]
    rw [hq₀def, pencilConfigPoint_certPicture lab zs x1 (by simp [hzsdef, this, certPt]), this]
  have p2 : pencilConfigPoint q₀ zs x2 = certPt 3 := by
    have : lab x2 = 3 := by simp [hlabdef, x02.symm, x12.symm]
    rw [hq₀def, pencilConfigPoint_certPicture lab zs x2 (by simp [hzsdef, this, certPt]), this]
  have p3 : pencilConfigPoint q₀ zs x3 = certPt 4 := by
    have : lab x3 = 4 := by simp [hlabdef, x30, x31, x32, x3l, hx3r]
    rw [hq₀def, pencilConfigPoint_certPicture lab zs x3 (by simp [hzsdef, x31, x32, this, certPt]),
      this]
  have pm : pencilConfigPoint q₀ zs xm = certPt 4 := by
    have : lab xm = 4 := by simp [hlabdef, xm0, xm1, xm2, xml, hxmr]
    rw [hq₀def, pencilConfigPoint_certPicture lab zs xm (by simp [hzsdef, xm1, xm2, this, certPt]),
      this]
  have pl : pencilConfigPoint q₀ zs xl = certPt 5 := by
    have : lab xl = 5 := by simp [hlabdef, x0l.symm, x1l.symm, x2l.symm]
    rw [hq₀def,
      pencilConfigPoint_certPicture lab zs xl (by simp [hzsdef, x1l.symm, x2l.symm, this, certPt]),
      this]
  have hcert : LinearIndependent K
      (fun i => pointJoin (pencilConfigPoint q₀ zs (u6 i)) (pencilConfigPoint q₀ zs (v6 i))) := by
    have heq : (fun i =>
        pointJoin (pencilConfigPoint q₀ zs (u6 i)) (pencilConfigPoint q₀ zs (v6 i)))
        = fun i : Fin 6 =>
          pointJoin (![certPt 0, certPt 1, certPt 2, certPt 3, certPt 4, certPt 5] i : Fin 4 → K)
            (![certPt 1, certPt 2, certPt 3, certPt 4, certPt 5, certPt 0] i) := by
      funext i
      fin_cases i
      · change pointJoin (pencilConfigPoint q₀ zs a) (pencilConfigPoint q₀ zs x0) = _
        rw [pa, p0]; rfl
      · change pointJoin (pencilConfigPoint q₀ zs x0) (pencilConfigPoint q₀ zs x1) = _
        rw [p0, p1]; rfl
      · change pointJoin (pencilConfigPoint q₀ zs x1) (pencilConfigPoint q₀ zs x2) = _
        rw [p1, p2]; rfl
      · change pointJoin (pencilConfigPoint q₀ zs x2) (pencilConfigPoint q₀ zs x3) = _
        rw [p2, p3]; rfl
      · change pointJoin (pencilConfigPoint q₀ zs xm) (pencilConfigPoint q₀ zs xl) = _
        rw [pm, pl]; rfl
      · change pointJoin (pencilConfigPoint q₀ zs xl) (pencilConfigPoint q₀ zs b) = _
        rw [pl, pb]; rfl
    rw [heq]
    exact linearIndependent_pointJoin_certHexagon
  -- the picture: generic for `G[V₁]`, main for `G`, the six joins independent at `zs`
  obtain ⟨Plam, hPlam₀, hPlam⟩ :=
    exists_mvPolynomial_linearIndependent_pointJoin_picture zs u6 v6 hcert
  have hPlamne : Plam ≠ 0 := fun h => hPlam₀ (by rw [h, map_zero])
  obtain ⟨q, hq⟩ := MvPolynomial.exists_eval_ne_zero (mul_ne_zero (mul_ne_zero hP₁ hPm) hPlamne)
  rw [map_mul, map_mul] at hq
  obtain ⟨-, R₁, ⟨z₁, hz₁, hR₁⟩, hatt₁⟩ := hgood₁ q (left_ne_zero_of_mul (left_ne_zero_of_mul hq))
  have hqmain := hmain q (right_ne_zero_of_mul (left_ne_zero_of_mul hq))
  have hliq := hPlam q (right_ne_zero_of_mul hq)
  obtain ⟨Rlam, hRlam₀, hRlam⟩ :=
    exists_mvPolynomial_linearIndependent_pointJoin_heights q u6 v6 hliq
  -- `zs` is a height of `G` at `q`
  have hzs : zs ∈ G.liftingSpace q := by
    refine G.mem_liftingSpace_of_ear hcover hinj hxV₁ ha hb hpath hsep hqmain.1 (fun w hw => ?_)
      (fun v hv => ⟨0, fun w hw => ?_⟩)
    · have h1 : w ≠ x1 := fun h => hw (hcover ▸ Or.inr ⟨_, h.symm⟩)
      have h2 : w ≠ x2 := fun h => hw (hcover ▸ Or.inr ⟨_, h.symm⟩)
      simp [hzsdef, h1, h2]
    · rw [zero_dotProduct]
      rcases G.mem_closedNbhd_induce_of_ear (by omega) hxV₁ ha hb hpath hsep hv hw with
        hw' | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · have hwV : w ∈ V₁ := Graph.closedNbhd_subset_vertexSet hv hw'
        have h1 : w ≠ x1 := fun h => hxV₁ _ (h ▸ hwV)
        have h2 : w ≠ x2 := fun h => hxV₁ _ (h ▸ hwV)
        simp [hzsdef, h1, h2]
      · have h1 : ¬ (x0 = x1 ∨ x0 = x2) := by rintro (h | h); exacts [x01 h, x02 h]
        exact ite_eq_right h1
      · have h1 : ¬ (xl = x1 ∨ xl = x2) := by rintro (h | h); exacts [x1l h.symm, x2l h.symm]
        exact ite_eq_right h1
  -- heights on which `G[V₁]` attains and the six joins stay independent
  have hex₁ : ∃ z ∈ G.liftingSpace q, MvPolynomial.eval z (restrictPoly V₁ R₁) ≠ 0 := by
    obtain ⟨z, hz, hzr, -⟩ := G.earExtend_mem_liftingSpace (by omega) hcover hinj hxV₁ ha hb hab
      hpath hsep hqmain.1 hz₁ 0
    exact ⟨z, hz, by rwa [eval_restrictPoly, hzr]⟩
  obtain ⟨z, hz, hz₁', hzlam⟩ := MvPolynomial.exists_mem_eval_ne_zero₂ hex₁ ⟨zs, hzs, hRlam₀⟩
  rw [eval_restrictPoly] at hz₁'
  have hr₁ := hatt₁ _ (Graph.liftingRestrict_mem_liftingSpace hle₁ hz) hz₁'
  have hli := hRlam z hzlam
  rw [Graph.vertexSet_induce G V₁] at hr₁
  rw [PanelHingeFramework.finrank_span_rigidityRows_ofNormals_congr _ hends₁ hendsI
    (q' := fun p => pencilConfigPoint q z p.1 p.2)
    (fun w hw t => pencilConfigPoint_liftingRestrict V₁ q z hw t)] at hr₁
  -- the ear rank law at `ofNormals G ends`, with the ear hinges spanning
  set F := (PanelHingeFramework.ofNormals (k := 2) G ends
    (fun p => pencilConfigPoint q z p.1 p.2)).toBodyHinge with hFdef
  have hC : ∀ i, F.supportExtensor (e i) ≠ 0 :=
    fun i => hqmain.1.supportExtensor_ne_zero hends z (hpath i)
  have hLam : Submodule.span K (Set.range (F.supportExtensor ∘ e)) = ⊤ :=
    span_supportExtensor_eq_top_of_linearIndependent hends (pencilConfigPoint q z) u6 v6 f6 hl6 hli
      e
      (by intro i; fin_cases i <;> exact ⟨_, rfl⟩)
  have hear := BodyHingeFramework.finrank_span_rigidityRows_ear_eq F hinj hxV₁ ha hb hab hpath
    hsep hC
  rw [hLam, sup_top_eq, finrank_top, screwSpace_finrank] at hear
  -- the deficiency and the body count
  have hdef := Graph.deficiency_induce_add_le_of_ear (n := 3) (by decide) (by omega) hcover hinj
    hxV₁ ha hb hpath hsep
  have hcount : (V(G).ncard : ℤ) = V₁.ncard + k := by
    rw [hcover, Set.ncard_union_eq _ (Set.toFinite _) (Set.toFinite _),
      Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]
    · push_cast; ring
    · refine Set.disjoint_left.mpr ?_
      rintro _ h ⟨i, rfl⟩
      exact hxV₁ i h
  refine Graph.x0Attains_of_exists hV ends hends hqmain hz ?_
  have e1 : (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
      = (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 2) (G.induce V₁)
          ends (fun p => pencilConfigPoint q z p.1 p.2)).toBodyHinge.rigidityRows) : ℤ)
        + ((screwDim 2 : ℤ) - 1) * (k + 1) + (screwDim 2 : ℤ) - (screwDim 2 : ℤ) := hear
  rw [e1, hr₁, hcount]
  have hs : (screwDim 2 : ℤ) = 6 := rfl
  have hb3 : (Graph.bodyBarDim 3 : ℤ) = 6 := rfl
  rw [hs]
  rw [hb3] at hdef
  linarith

/-! ## The closed ear -/

/-- **The closed ear** (Phase 40g CHAIN, `thm:pencil-x0-closed-ear`; (MC-20), closed half): a
closed ear `c − x 0 − ⋯ − x (k − 1) − c` (`k ≥ 2`) on `V₁` makes `c` a cut vertex whose far side
`G[{c} ∪ range x]` is the cycle through `x 0` closed by `e 0`, so CUT
(`Graph.X0Attains.of_cutVertex`) and BASE (`Graph.X0Attains.of_cycle`) give `X₀(G)` from
`X₀(G[V₁])`. No chain span of a closed ear ((MC-19)(c)) is used. -/
theorem _root_.Graph.X0Attains.of_closedEar [Infinite K] [Finite α] [Finite β] {G : Graph α β}
    (hG : G.IsX0Graph) {V₁ : Set α} {k : ℕ} {x : Fin k → α} {c : α} {e : Fin (k + 1) → β}
    (hk : 2 ≤ k) (hcover : V(G) = V₁ ∪ Set.range x) (hinj : Function.Injective x)
    (hxV₁ : ∀ i, x i ∉ V₁) (hc : c ∈ V₁)
    (hpath : ∀ i : Fin (k + 1),
      G.IsLink (e i) (pathVertex c x c i.castSucc) (pathVertex c x c i.succ))
    (hsep : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁)
    (h₁ : (G.induce V₁).X0Attains K) : G.X0Attains K := by
  classical
  have hxc : ∀ i, x i ≠ c := fun i h => hxV₁ i (h ▸ hc)
  set V₂ : Set α := insert c (Set.range x) with hV₂
  have hpvV₂ : ∀ m, pathVertex c x c m ∈ V₂ := by
    intro m
    rcases pathVertex_cases c x c m with ⟨-, h⟩ | ⟨i, -, h⟩ | ⟨-, h⟩
    · rw [h]; exact Or.inl rfl
    · rw [h]; exact Or.inr ⟨i, rfl⟩
    · rw [h]; exact Or.inl rfl
  refine Graph.X0Attains.of_cutVertex hG (V₁ := V₁) (V₂ := V₂) (v := c) ?_ ?_ ?_ h₁ ?_
  · rw [hcover, hV₂]
    ext w
    simp only [Set.mem_union, Set.mem_insert_iff]
    constructor
    · rintro (h | rfl | h)
      exacts [Or.inl h, Or.inl hc, Or.inr h]
    · rintro (h | h)
      exacts [Or.inl h, Or.inr (Or.inr h)]
  · ext w
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff, hV₂]
    constructor
    · rintro ⟨hw, rfl | ⟨i, rfl⟩⟩
      · rfl
      · exact absurd hw (hxV₁ i)
    · rintro rfl; exact ⟨hc, Or.inl rfl⟩
  · intro f u w hf
    by_cases hfe : ∃ i, f = e i
    · obtain ⟨i, rfl⟩ := hfe
      rcases hf.eq_and_eq_or_eq_and_eq (hpath i) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr ⟨hpvV₂ _, hpvV₂ _⟩
      · exact Or.inr ⟨hpvV₂ _, hpvV₂ _⟩
    · exact Or.inl (hsep f u w hf (fun i h => hfe ⟨i, h⟩))
  · -- the far side is the cycle `x 0 − x 1 − ⋯ − x (k - 1) − c − x 0`
    set x' : Fin (k - 1) → α := fun j => x ⟨j.val + 1, (by omega)⟩ with hx'
    set e' : Fin ((k - 1) + 1) → β := fun j => e ⟨j.val + 1, (by omega)⟩ with he'
    have hx0c : x ⟨0, (by omega)⟩ ≠ c := hxc _
    have hlinkV₂ : ∀ g u w, G.IsLink g u w → u ∈ V₂ → w ∈ V₂ → (G.induce V₂).IsLink g u w :=
      fun g u w h hu hw => ⟨h, hu, hw⟩
    refine Graph.X0Attains.of_cycle (G := G.induce V₂) (k := k - 1) (x := x')
      (a := x ⟨0, (by omega)⟩) (b := c) (e := e') (f := e ⟨0, (by omega)⟩) (by omega) ?_ ?_ ?_ ?_
      hx0c ?_ ?_ ?_
    · change V₂ = _
      ext w
      simp only [hV₂, Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff, Set.mem_range, hx']
      constructor
      · rintro (rfl | ⟨i, rfl⟩)
        · exact Or.inl (Or.inr rfl)
        · rcases Nat.eq_zero_or_pos i.val with h0 | h0
          · exact Or.inl (Or.inl (congrArg x (Fin.ext h0)))
          · exact Or.inr ⟨⟨i.val - 1, (by omega)⟩, congrArg x (Fin.ext (by simp; omega))⟩
      · rintro ((rfl | rfl) | ⟨j, rfl⟩)
        · exact Or.inr ⟨_, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨_, rfl⟩
    · intro i j h
      have := hinj h
      simp only [Fin.ext_iff] at this
      exact Fin.ext (by omega)
    · intro j h
      have := hinj h
      simp [Fin.ext_iff] at this
    · intro j; exact hxc _
    · have h := ear_isLink_first hpath (by omega)
      exact hlinkV₂ _ _ _ h.symm (Or.inr ⟨_, rfl⟩) (Or.inl rfl)
    · intro j
      have h := hpath ⟨j.val + 1, (by omega)⟩
      have e1 : pathVertex c x c (Fin.castSucc ⟨j.val + 1, (by omega)⟩)
          = pathVertex (x ⟨0, (by omega)⟩) x' c j.castSucc := by
        rw [pathVertex_shift (by omega) c c x]; rfl
      have e2 : pathVertex c x c (Fin.succ ⟨j.val + 1, (by omega)⟩)
          = pathVertex (x ⟨0, (by omega)⟩) x' c j.succ := by
        rw [pathVertex_shift (by omega) c c x]; rfl
      rw [e1, e2] at h
      exact hlinkV₂ _ _ _ h (by rw [← e1]; exact hpvV₂ _) (by rw [← e2]; exact hpvV₂ _)
    · rintro g u w ⟨hg, hu, hw⟩ hge
      by_cases hfe : ∃ i, g = e i
      · obtain ⟨i, rfl⟩ := hfe
        rcases Nat.eq_zero_or_pos i.val with h0 | h0
        · exact congrArg e (Fin.ext h0)
        · exact absurd (congrArg e (Fin.ext (by simp; omega)) : e i = e' ⟨i.val - 1, (by omega)⟩)
            (hge _)
      · -- a non-ear link inside `V₂` would be a loop at `c`
        obtain ⟨hu₁, hw₁⟩ := hsep g u w hg (fun i h => hfe ⟨i, h⟩)
        have huc : u = c := by
          rcases hu with rfl | ⟨i, rfl⟩
          · rfl
          · exact absurd hu₁ (hxV₁ i)
        have hwc : w = c := by
          rcases hw with rfl | ⟨i, rfl⟩
          · rfl
          · exact absurd hw₁ (hxV₁ i)
        rw [huc, hwc] at hg
        exact (hG.simple.toLoopless.not_isLoopAt g c hg).elim

end CombinatorialRigidity.Molecular
