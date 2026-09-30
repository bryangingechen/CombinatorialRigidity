/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.Coverage

/-!
# Chains and the cycle in the `X₀` covering theorem (Phase 40m CHAINS B1)

The maximal ear through bodies of degree two, and the two consequences the covering theorem
needs: every body of degree two lies on a chain, and a graph satisfying (H) all of whose bodies
have degree two is a cycle (`blueprint/src/chapter/main-component.tex`,
`sec:main-component-coverage`; (MC-79)ff). One core, the maximal ear
`Graph.IsOpenEar.exists_maximal`, serves both: strong induction on `V₁.ncard`, by
`Graph.IsOpenEar.symm` and `Graph.IsOpenEar.cons`, extending one more body at a time while an end
has degree two and is not adjacent to the other end.

## Main statements

* `Graph.IsChain` — **a chain** (`def:pencil-x0-chain`): an open ear whose interior bodies have
  degree two and whose ends have degree at least three.
* `Graph.IsOpenEar.exists_maximal` — **the maximal ear**: every open ear of a graph satisfying (H)
  extends, through bodies of degree two at its ends, to one each of whose ends is a hub or
  adjacent to the other end.
* `Graph.IsX0Graph.exists_isChain` — **chain extraction** (`lem:pencil-x0-chain-exists`): in a
  2-connected (H)-graph with a hub, every body of degree two lies on a chain.
* `Graph.IsX0Graph.x0Reduces_of_forall_degree_eq_two` — **the cycle**
  (`lem:pencil-x0-cycle-reduces`): a graph satisfying (H) all of whose bodies have degree two is a
  cycle, and reduces by BASE (`Graph.X0Reduces.cycle`'s format).
-/

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {α β : Type*}

/-! ## The maximal ear -/

/-- In a connected graph, a nonempty set of bodies closed under adjacency is everything. -/
theorem _root_.Graph.Connected.vertexSet_subset_of_forall_adj {G : Graph α β}
    (hG : G.Connected) {T : Set α} (hT : T.Nonempty) (hTV : T ⊆ V(G))
    (hcl : ∀ u ∈ T, ∀ z, G.Adj u z → z ∈ T) : V(G) ⊆ T := by
  by_contra hns
  obtain ⟨y, hy, z, hz, hyz⟩ := (Graph.connected_iff_forall_exists_adj hG.nonempty).mp hG T
    (hTV.ssubset_of_ne fun h => hns h.symm.subset) hT
  exact hz.2 (hcl y hy z hyz)

/-- At an end `a` of degree two, the second link: `a`'s edges are `e 0` and one more, `g`, to a
body `a' ≠ a`, and `g` is no path edge. -/
theorem _root_.Graph.IsOpenEar.exists_isLink_of_degree_eq_two [Finite β]
    {G : Graph α β} [G.Simple] {V₁ : Set α} {k : ℕ} {x : Fin k → α} {a b : α}
    {e : Fin (k + 1) → β} (h : G.IsOpenEar V₁ x a b e) (ha : G.degree a = 2) :
    ∃ a' g, G.IsLink g a a' ∧ a' ≠ a ∧ (∀ i, g ≠ e i) ∧
      ∀ f y, G.IsLink f a y → f = e 0 ∨ f = g := by
  have h0 : G.IsLink (e 0) a (pathVertex a x b 1) := by
    have := h.isLink 0
    rwa [Fin.castSucc_zero, pathVertex_zero, Fin.succ_zero_eq_one] at this
  have hN : N(G, a).ncard = 2 := by rw [← Graph.degree_eq_ncard_adj]; exact ha
  obtain ⟨a', ha'N, ha'p⟩ :=
    Set.exists_ne_of_one_lt_ncard (s := N(G, a)) (by omega) (pathVertex a x b 1)
  obtain ⟨g, hg⟩ := ha'N
  have hg0 : g ≠ e 0 := by
    rintro rfl
    exact ha'p (h0.right_unique hg).symm
  have hge : ∀ i, g ≠ e i := by
    rintro i rfl
    exact hg0 (by rw [h.eq_zero_of_isLink_left hg])
  refine ⟨a', g, hg, fun h' => ?_, hge,
    Graph.isLink_eq_of_degree_eq_two ha (Ne.symm hg0) h0 hg⟩
  rw [h'] at hg
  exact Graph.Loopless.not_isLoopAt g a hg

/-- One step of the maximal ear: an end `a` of degree two not adjacent to `b` extends. -/
theorem _root_.Graph.IsOpenEar.exists_cons [Finite β] {G : Graph α β} [G.Simple]
    {V₁ : Set α} {k : ℕ} {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β}
    (h : G.IsOpenEar V₁ x a b e) (ha : G.degree a = 2) (hab : ¬ G.Adj a b) :
    ∃ a' g, G.IsOpenEar (V₁ \ {a}) (Fin.cons a x) a' b (Fin.cons g e) := by
  obtain ⟨a', g, hg, ha'a, hge, honly⟩ := h.exists_isLink_of_degree_eq_two ha
  refine ⟨a', g, h.cons hg.symm (h.sep g a a' hg hge).2 ha'a (fun h' => hab ?_) honly⟩
  exact ⟨g, h' ▸ hg⟩

/-- **The maximal ear**: every open ear of a graph satisfying (H) extends, through bodies of
degree two at its ends, to one each of whose ends is a hub or adjacent to the other end. -/
theorem _root_.Graph.IsOpenEar.exists_maximal [Finite α] [Finite β] {G : Graph α β}
    (hG : G.IsX0Graph) {V₁ : Set α} {k : ℕ} {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β}
    (h : G.IsOpenEar V₁ x a b e) :
    ∃ (V₂ : Set α) (m : ℕ) (y : Fin m → α) (c d : α) (f : Fin (m + 1) → β),
      G.IsOpenEar V₂ y c d f ∧ Set.range x ⊆ Set.range y ∧
      (3 ≤ G.degree c ∨ G.Adj c d) ∧ (3 ≤ G.degree d ∨ G.Adj c d) := by
  have := hG.simple
  induction hn : V₁.ncard using Nat.strong_induction_on generalizing V₁ k x a b e with
  | _ n ih =>
  have hlt : ∀ c ∈ V₁, (V₁ \ {c}).ncard < n := fun c hc =>
    hn ▸ Set.ncard_sdiff_singleton_lt_of_mem hc (Set.toFinite _)
  have hV : V₁ ⊆ V(G) := h.cover ▸ Set.subset_union_left
  by_cases hA : 3 ≤ G.degree a ∨ G.Adj a b
  · by_cases hB : 3 ≤ G.degree b ∨ G.Adj a b
    · exact ⟨V₁, k, x, a, b, e, h, subset_rfl, hA, hB⟩
    · push Not at hB
      have hb2 : G.degree b = 2 := by
        have := hG.two_le_degree b (hV h.right_mem); omega
      obtain ⟨b', g, h'⟩ := h.symm.exists_cons hb2 fun hba => hB.2 hba.symm
      obtain ⟨V₂, m, y, c, d, f, hy, hsub, hc, hd⟩ := ih _ (hlt b h.right_mem) h' rfl
      refine ⟨V₂, m, y, c, d, f, hy, ?_, hc, hd⟩
      refine subset_trans ?_ hsub
      rw [Fin.range_cons, Fin.rev_surjective.range_comp]
      exact Set.subset_insert _ _
  · push Not at hA
    have ha2 : G.degree a = 2 := by
      have := hG.two_le_degree a (hV h.left_mem); omega
    obtain ⟨a', g, h'⟩ := h.exists_cons ha2 hA.2
    obtain ⟨V₂, m, y, c, d, f, hy, hsub, hc, hd⟩ := ih _ (hlt a h.left_mem) h' rfl
    refine ⟨V₂, m, y, c, d, f, hy, ?_, hc, hd⟩
    refine subset_trans ?_ hsub
    rw [Fin.range_cons]
    exact Set.subset_insert _ _

/-! ## Chains -/

/-- A **chain** of `G` (Step MC16's notation): an open ear whose interior bodies have degree two
and whose ends have degree at least three. -/
structure _root_.Graph.IsChain (G : Graph α β) (V₁ : Set α) {k : ℕ} (x : Fin k → α) (a b : α)
    (e : Fin (k + 1) → β) : Prop extends G.IsOpenEar V₁ x a b e where
  one_le : 1 ≤ k
  degree_eq_two : ∀ i, G.degree (x i) = 2
  three_le_degree_left : 3 ≤ G.degree a
  three_le_degree_right : 3 ≤ G.degree b

/-- A body of degree two has two links, to distinct neighbours. -/
theorem _root_.Graph.IsX0Graph.exists_isLink_pair {G : Graph α β} (hG : G.IsX0Graph) {v : α}
    (hdeg : G.degree v = 2) :
    ∃ c₁ c₂ e₁ e₂, G.IsLink e₁ c₁ v ∧ G.IsLink e₂ v c₂ ∧ c₁ ≠ c₂ := by
  have := hG.simple
  rw [Graph.degree_eq_ncard_adj] at hdeg
  obtain ⟨c₁, c₂, hne, hN⟩ := Set.ncard_eq_two.mp hdeg
  obtain ⟨e₁, he₁⟩ : G.Adj v c₁ := (hN ▸ Set.mem_insert c₁ {c₂} : c₁ ∈ N(G, v))
  obtain ⟨e₂, he₂⟩ : G.Adj v c₂ := (hN ▸ Set.mem_insert_of_mem c₁ rfl : c₂ ∈ N(G, v))
  exact ⟨c₁, c₂, e₁, e₂, he₁.symm, he₂, hne⟩

/-- A body of degree two with distinct neighbours is a one-body open ear. -/
theorem _root_.Graph.IsX0Graph.isOpenEar_one [Finite β] {G : Graph α β} (hG : G.IsX0Graph)
    {x c₁ c₂ : α} {e₁ e₂ : β} (hx : G.degree x = 2) (h₁ : G.IsLink e₁ c₁ x)
    (h₂ : G.IsLink e₂ x c₂) (hne : c₁ ≠ c₂) :
    G.IsOpenEar (V(G) \ {x}) ![x] c₁ c₂ ![e₁, e₂] := by
  have := hG.simple
  have hloop := hG.simple.toLoopless
  have hc₁x : c₁ ≠ x := fun h => hloop.not_isLoopAt e₁ x (h ▸ h₁)
  have hc₂x : c₂ ≠ x := fun h => hloop.not_isLoopAt e₂ x (h ▸ h₂)
  have he : e₁ ≠ e₂ := by
    rintro rfl
    rcases h₁.left_eq_or_eq h₂ with h | h
    · exact hc₁x h
    · exact hne h
  have hxV : x ∈ V(G) := h₂.left_mem
  refine ⟨?_, fun i j _ => Subsingleton.elim i j, ?_, ⟨h₁.left_mem, hc₁x⟩,
    ⟨h₂.right_mem, hc₂x⟩, hne, ?_, ?_⟩
  · ext y
    simp only [Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_range]
    constructor
    · intro hy
      by_cases hyx : y = x
      · exact Or.inr ⟨0, by simp [hyx]⟩
      · exact Or.inl ⟨hy, hyx⟩
    · rintro (⟨hy, -⟩ | ⟨i, rfl⟩)
      · exact hy
      · simpa using hxV
  · intro i h
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact h.2 rfl
  · intro i
    fin_cases i
    · exact h₁
    · exact h₂
  · intro f u w hf hfe
    have hf1 : f ≠ e₁ := hfe 0
    have hf2 : f ≠ e₂ := hfe 1
    refine ⟨⟨hf.left_mem, fun hu => ?_⟩, ⟨hf.right_mem, fun hw => ?_⟩⟩
    · rw [hu] at hf
      rcases Graph.isLink_eq_of_degree_eq_two hx he h₁.symm h₂ f w hf with h | h
      · exact hf1 h
      · exact hf2 h
    · rw [hw] at hf
      rcases Graph.isLink_eq_of_degree_eq_two hx he h₁.symm h₂ f u hf.symm with h | h
      · exact hf1 h
      · exact hf2 h

/-- A body of degree two between two hubs is a one-body chain. -/
theorem _root_.Graph.IsX0Graph.isChain_one [Finite β] {G : Graph α β} (hG : G.IsX0Graph)
    {x c₁ c₂ : α} {e₁ e₂ : β} (hx : G.degree x = 2) (h₁ : G.IsLink e₁ c₁ x)
    (h₂ : G.IsLink e₂ x c₂) (hne : c₁ ≠ c₂) (hc₁ : 3 ≤ G.degree c₁) (hc₂ : 3 ≤ G.degree c₂) :
    G.IsChain (V(G) \ {x}) ![x] c₁ c₂ ![e₁, e₂] :=
  ⟨hG.isOpenEar_one hx h₁ h₂ hne, le_rfl, fun i => by
    obtain rfl : i = 0 := Subsingleton.elim _ _
    simpa using hx, hc₁, hc₂⟩

/-- **Chain extraction**: in a 2-connected (H)-graph with a hub, every body of degree two lies on
a chain. -/
theorem _root_.Graph.IsX0Graph.exists_isChain [Finite α] [Finite β] {G : Graph α β}
    (hG : G.IsX0Graph) (h2c : ∀ v ∈ V(G), (G.induce (V(G) \ {v})).Connected)
    (hhub : ∃ w ∈ V(G), G.degree w ≠ 2) {v : α} (_hv : v ∈ V(G)) (hdeg : G.degree v = 2) :
    ∃ (V₁ : Set α) (k : ℕ) (x : Fin k → α) (a b : α) (e : Fin (k + 1) → β),
      G.IsChain V₁ x a b e ∧ v ∈ Set.range x := by
  have := hG.simple
  obtain ⟨c₁, c₂, e₁, e₂, h₁, h₂, hne⟩ := hG.exists_isLink_pair hdeg
  obtain ⟨V₂, m, y, c, d, f, hy, hsub, hc, hd⟩ :=
    (hG.isOpenEar_one hdeg h₁ h₂ hne).exists_maximal hG
  have hvy : v ∈ Set.range y := hsub ⟨0, rfl⟩
  have hm : 1 ≤ m := by
    obtain ⟨i, -⟩ := hvy
    exact Nat.one_le_iff_ne_zero.mpr fun h0 => (h0 ▸ i).elim0
  have hV : V₂ ⊆ V(G) := hy.cover ▸ Set.subset_union_left
  refine ⟨V₂, m, y, c, d, f, ⟨hy, hm, hy.degree_eq_two, ?_, ?_⟩, hvy⟩
  · rcases hc with hc | hc
    · exact hc
    · by_contra h3
      exact hy.false_of_adj_of_degree_eq_two hG h2c hhub hm hc
        (by have := hG.two_le_degree c (hV hy.left_mem); omega)
  · rcases hd with hd | hd
    · exact hd
    · by_contra h3
      exact hy.symm.false_of_adj_of_degree_eq_two hG h2c hhub hm hd.symm
        (by have := hG.two_le_degree d (hV hy.right_mem); omega)

/-- **The cycle**: a graph satisfying (H) all of whose bodies have degree two is a cycle, and
reduces by BASE (`of_cycle`'s format). -/
theorem _root_.Graph.IsX0Graph.x0Reduces_of_forall_degree_eq_two [Finite α] [Finite β]
    {G : Graph α β} (hG : G.IsX0Graph) (h2 : ∀ v ∈ V(G), G.degree v = 2) :
    G.X0Reduces G.X0Below := by
  have := hG.simple
  obtain ⟨v, hv⟩ := hG.connected.nonempty
  obtain ⟨c₁, c₂, e₁, e₂, h₁, h₂, hne⟩ := hG.exists_isLink_pair (h2 v hv)
  obtain ⟨V₂, m, y, c, d, f, hy, hsub, hc, -⟩ :=
    (hG.isOpenEar_one (h2 v hv) h₁ h₂ hne).exists_maximal hG
  have hm : 1 ≤ m := by
    obtain ⟨i, -⟩ := hsub ⟨0, rfl⟩
    exact Nat.one_le_iff_ne_zero.mpr fun h0 => (h0 ▸ i).elim0
  have hV : V₂ ⊆ V(G) := hy.cover ▸ Set.subset_union_left
  have hc2 := h2 c (hV hy.left_mem)
  have hd2 := h2 d (hV hy.right_mem)
  obtain ⟨g, hg⟩ : G.Adj c d := hc.resolve_left (by omega)
  have hcl := hy.adj_mem_of_adj_of_degree_eq_two hm hg hc2
  have hcl' := hy.symm.adj_mem_of_adj_of_degree_eq_two hm hg.symm hd2
  have hrange : Set.range (y ∘ Fin.rev) = Set.range y := Fin.rev_surjective.range_comp y
  rw [hrange] at hcl'
  -- the closed path is all of `G`
  have hT : V(G) ⊆ insert d (insert c (Set.range y)) := by
    refine hG.connected.vertexSet_subset_of_forall_adj ⟨d, Set.mem_insert _ _⟩ ?_ ?_
    · rintro u (rfl | rfl | ⟨i, rfl⟩)
      · exact hV hy.right_mem
      · exact hV hy.left_mem
      · exact hy.cover ▸ Or.inr ⟨i, rfl⟩
    · rintro u (rfl | hu) z hz
      · rcases hcl' u (Set.mem_insert u _) z hz with rfl | rfl | hz'
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl rfl
        · exact Or.inr (Or.inr hz')
      · exact hcl u hu z hz
  have hxa : ∀ i, y i ≠ c := fun i hi => hy.notMem i (hi ▸ hy.left_mem)
  have hxb : ∀ i, y i ≠ d := fun i hi => hy.notMem i (hi ▸ hy.right_mem)
  refine .cycle hm ?_ hy.inj hxa hxb hy.ne hg hy.isLink ?_
  · refine le_antisymm (fun u hu => ?_) (fun u hu => ?_)
    · rcases hT hu with rfl | rfl | hu'
      · exact Or.inl (Or.inr rfl)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr hu'
    · rcases hu with (rfl | rfl) | ⟨i, rfl⟩
      · exact hV hy.left_mem
      · exact hV hy.right_mem
      · exact hy.cover ▸ Or.inr ⟨i, rfl⟩
  · -- the one non-path edge
    have h0 : G.IsLink (f 0) c (pathVertex c y d 1) := by
      have := hy.isLink 0
      rwa [Fin.castSucc_zero, pathVertex_zero, Fin.succ_zero_eq_one] at this
    have hg0 : f 0 ≠ g := by
      intro h'
      rw [h'] at h0
      have h1 : pathVertex c y d 1 = y ⟨0, hm⟩ := pathVertex_eq_of_val_eq_succ c y d (by simp)
      exact hy.notMem ⟨0, hm⟩ (h1 ▸ (hg.right_unique h0) ▸ hy.right_mem)
    intro g' u w hl hne'
    have hu := (hy.sep g' u w hl hne').1
    rcases hT hl.left_mem with rfl | rfl | ⟨i, rfl⟩
    · -- at `d`
      have hlast : G.IsLink (f (Fin.last m)) u (pathVertex c y u (Fin.last m).castSucc) := by
        have := hy.isLink (Fin.last m)
        rw [Fin.succ_last, pathVertex_last] at this
        exact this.symm
      have hgl : f (Fin.last m) ≠ g := by
        intro h'
        have := congrArg Fin.val (hy.eq_zero_of_isLink_left (i := Fin.last m) (y := u) (h' ▸ hg))
        simp at this
        omega
      rcases Graph.isLink_eq_of_degree_eq_two hd2 hgl hlast hg.symm g' w hl with h' | h'
      · exact absurd h' (hne' _)
      · exact h'
    · rcases Graph.isLink_eq_of_degree_eq_two hc2 hg0 h0 hg g' w hl with h' | h'
      · exact absurd h' (hne' _)
      · exact h'
    · exact absurd hu (hy.notMem i)

/-! ## Plumbing for Theorem S -/

/-- (H) forces three bodies. -/
theorem _root_.Graph.IsX0Graph.three_le_ncard_vertexSet [Finite α] {G : Graph α β}
    (hG : G.IsX0Graph) :
    3 ≤ V(G).ncard := by
  obtain ⟨v, hv⟩ := hG.connected.nonempty
  exact (hG.three_le_ncard_closedNbhd v hv).trans
    (Set.ncard_le_ncard (Graph.closedNbhd_subset_vertexSet hv) (Set.toFinite _))

/-- The identity partition's crossing edges are all of `E(G)`. -/
theorem _root_.Graph.IsX0Graph.crossingEdges_id {G : Graph α β} (hG : G.IsX0Graph) :
    G.crossingEdges id = E(G) := by
  ext e
  refine ⟨fun h => h.1, fun he => ?_⟩
  obtain ⟨x, y, hl⟩ := Graph.exists_isLink_of_mem_edgeSet he
  refine ⟨he, x, y, hl, fun hxy => ?_⟩
  exact hG.simple.toLoopless.not_isLoopAt e x (by rw [show y = x from hxy.symm] at hl; exact hl)

/-- A chain through a body adjacent to another body of degree two has two or more interior
bodies. -/
theorem _root_.Graph.IsChain.two_le_of_adj {G : Graph α β} {V₁ : Set α} {k : ℕ}
    {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β} (hC : G.IsChain V₁ x a b e) {v w : α}
    (hv : v ∈ Set.range x) (hvw : G.Adj v w) (hw : G.degree w = 2) : 2 ≤ k := by
  obtain ⟨i, rfl⟩ := hv
  by_contra hk
  have hk1 := hC.one_le
  obtain rfl : k = 1 := by omega
  obtain rfl : i = 0 := Subsingleton.elim _ _
  obtain ⟨f, hf⟩ := hvw
  have l0 : G.IsLink (e 0) a (x 0) := hC.isLink 0
  have l1 : G.IsLink (e 1) (x 0) b := hC.isLink 1
  rcases hC.toIsOpenEar.isLink_interior 0 hf with rfl | rfl
  · have : w = a := (l0.symm.right_unique hf).symm
    have := hC.three_le_degree_left
    subst_vars; omega
  · have : w = b := (l1.right_unique hf).symm
    have := hC.three_le_degree_right
    subst_vars; omega

/-- Losing a neighbour lowers the degree. -/
theorem _root_.Graph.degree_induce_lt_of_adj [Finite β] {G : Graph α β} {W : Set α} {c x : α}
    (hc : c ∈ W) (hx : x ∉ W) (hadj : G.Adj c x) : (G.induce W).degree c < G.degree c := by
  rw [Graph.degree_eq_ncard_add_ncard, Graph.degree_eq_ncard_add_ncard]
  obtain ⟨f, hf⟩ := hadj
  have hloop : {e | (G.induce W).IsLoopAt e c} ⊆ {e | G.IsLoopAt e c} := fun e he =>
    (show G.IsLink e c c ∧ c ∈ W ∧ c ∈ W from he).1
  have hnl : {e | (G.induce W).IsNonloopAt e c} ⊂ {e | G.IsNonloopAt e c} := by
    have hsub : {e | (G.induce W).IsNonloopAt e c} ⊆ {e | G.IsNonloopAt e c} := by
      rintro e ⟨y, hy, he⟩
      exact ⟨y, hy, (show G.IsLink e c y ∧ c ∈ W ∧ y ∈ W from he).1⟩
    refine (Set.ssubset_iff_of_subset hsub).mpr
      ⟨f, ⟨x, fun h => hx (h ▸ hc), hf⟩, ?_⟩
    rintro ⟨y, hy, hfy⟩
    have hfy' : G.IsLink f c y ∧ c ∈ W ∧ y ∈ W := hfy
    rcases hf.right_eq_or_eq hfy'.1 with h | h
    · exact hx (h ▸ hc)
    · exact hx (h ▸ hfy'.2.2)
  have h1 := Set.ncard_le_ncard hloop (Set.toFinite _)
  have h2 := Set.ncard_lt_ncard hnl (Set.toFinite _)
  omega

/-- The edges from a body into a set avoiding it are at most its degree. -/
theorem _root_.Graph.ncard_setOf_isLink_le_degree [Finite β] {G : Graph α β} {x : α}
    {Y : Set α} (hx : x ∉ Y) : ({e | ∃ y ∈ Y, G.IsLink e x y} : Set β).ncard ≤ G.degree x := by
  rw [Graph.degree_eq_ncard_add_ncard]
  have hsub : ({e | ∃ y ∈ Y, G.IsLink e x y} : Set β) ⊆ {e | G.IsNonloopAt e x} :=
    fun e ⟨y, hy, he⟩ => ⟨y, fun h => hx (h ▸ hy), he⟩
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

/-- In a simple graph, a body with at most one neighbour in `W` sends at most one edge there. -/
theorem _root_.Graph.ncard_setOf_isLink_le_one [Finite β] {G : Graph α β} (hG : G.Simple) {x : α}
    {W : Set α} (hatt : ∀ c₁ ∈ W, ∀ c₂ ∈ W, G.Adj x c₁ → G.Adj x c₂ → c₁ = c₂) :
    ({e | ∃ y ∈ W, G.IsLink e x y} : Set β).ncard ≤ 1 := by
  refine Set.ncard_le_one_iff_subsingleton.mpr fun e ⟨y, hy, he⟩ f ⟨z, hz, hf⟩ => ?_
  obtain rfl := hatt y hy z hz ⟨e, he⟩ ⟨f, hf⟩
  exact hG.eq_of_isLink he hf

end CombinatorialRigidity.Molecular
