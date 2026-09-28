/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.CoverageCut
import CombinatorialRigidity.Molecular.Induction.SparseDeficiency

/-!
# Theorem S, the covering theorem and the pieces they compose from (Phase 40m THEOREM-S B4–B5)

A usable chain's dispatch, contraction at a maximal planar-rigid set, and the count of bodies of
degree two a sparse (H)-graph needs, all of which Theorem S composes from; Theorem S itself; and
the covering theorem — every (H)-graph reduces by one landed step, hence `X₀`'s general point
attains at every simple 2-edge-connected graph on at least three bodies
(`blueprint/src/chapter/main-component.tex`, `sec:main-component-coverage`; (MC-75), (MC-76),
(MC-79)ff, (MC-80), (MC-89), (MC-10)(a)).

## Main statements

* `Graph.ChainUsable` — **a usable chain** (`def:pencil-x0-usable-chain`): a chain long enough, or
  short with a deficiency condition at its ends.
* `Graph.IsChain.x0Reduces_of_chainUsable` — **the chain dispatch**
  (`lem:pencil-x0-chain-reduces`): a usable chain gives a reduction, by the ear or split-off
  clauses.
* `Graph.IsX0Graph.x0Reduces_of_deficiency_two_rigid` — **contraction at a maximal planar-rigid
  set** (`lem:pencil-x0-planar-rigid-reduces`).
* `Graph.IsX0Graph.exists_degree_eq_two_notMem`,
  `Graph.IsX0Graph.partitionDef_three_induce_diff_nonpos` — **counting bodies of degree two**
  (`lem:pencil-x0-sparse-count`): a sparse graph has at least four, and, when no two are adjacent,
  removing any one of them keeps `val₃ ≤ 0`.
* `Graph.IsX0Graph.exists_additiveCore` — **Theorem S** (`thm:pencil-x0-theorem-s`): an (S)-graph
  none of whose chains is usable has an additive core with the attachment condition.
* `Graph.IsX0Graph.x0Reduces`, `Graph.IsX0Graph.x0Attains`,
  `Graph.X0Attains.of_twoEdgeConnected` — **the covering theorem** (`thm:pencil-x0-coverage`):
  every (H)-graph reduces by one landed step, and consequently `X₀`'s general point attains at
  every (H)-graph, in particular at every simple 2-edge-connected graph on at least three bodies.
-/

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

/-- **A usable chain** ((MC-79)(v) in the Lean steps' own hypotheses). -/
def _root_.Graph.ChainUsable (G : Graph α β) (V₁ : Set α) (k : ℕ) (a b : α) : Prop :=
  3 ≤ k ∨
  (k = 2 ∧ ((G.induce V₁).deficiencyMerged 3 a b = (G.induce V₁).deficiency 3 ∨
    (¬ G.Adj a b ∧
      (G.induce V₁).deficiencyMerged 2 a b + 2 ≤ (G.induce V₁).deficiency 2))) ∨
  (k = 1 ∧ ((G.induce V₁).deficiencyMerged 3 a b = (G.induce V₁).deficiency 3 ∨
    (G.induce V₁).deficiencyMerged 3 a b + 5 ≤ (G.induce V₁).deficiency 3))

variable [Finite α] [Finite β]

/-! ## The reductions at a usable chain and at a planar-rigid set -/

/-- CONTRACT-A's producer: an additive core gives a reduction. -/
theorem _root_.Graph.IsX0Graph.x0Reduces_of_additiveCore {G : Graph α β} (hG : G.IsX0Graph)
    (htec : G.TwoEdgeConnected) {W : Set α} {r : α} (hr : r ∈ W) (hWss : W ⊂ V(G))
    (hW2 : 2 ≤ W.ncard) (hdef3 : (G.induce W).deficiency 3 = 0)
    (hadd : (G.induce W).deficiency 2 + (G.rigidContract (G.induce W) r).deficiency 2 ≤
      G.deficiency 2)
    (hatt : ∀ u ∉ W, ∀ c₁ ∈ W, ∀ c₂ ∈ W, G.Adj u c₁ → G.Adj u c₂ → c₁ = c₂) :
    G.X0Reduces G.X0Below := by
  refine .additiveContract htec hr hWss hW2 hdef3 hadd hatt ⟨?_, ?_⟩ ⟨?_, ?_⟩
  · exact Graph.isX0Graph_induce_of_deficiency_eq_zero hG.simple hWss.subset hW2
      (by decide) hdef3
  · exact Set.ncard_lt_ncard hWss
  · exact Graph.isX0Graph_rigidContract_induce hG htec hr hWss hatt
  · exact Graph.rigidContract_vertexSet_ncard_lt hWss.subset hW2

/-- CONTRACT-R's producer: a `def₂`-rigid core with the attachment condition. -/
theorem _root_.Graph.IsX0Graph.x0Reduces_of_rigidCore {G : Graph α β} (hG : G.IsX0Graph)
    (htec : G.TwoEdgeConnected) {W : Set α} {r : α} (hr : r ∈ W) (hWss : W ⊂ V(G))
    (hW2 : 2 ≤ W.ncard) (hdef : (G.induce W).deficiency 2 = 0)
    (hatt : ∀ u ∉ W, ∀ c₁ ∈ W, ∀ c₂ ∈ W, G.Adj u c₁ → G.Adj u c₂ → c₁ = c₂) :
    G.X0Reduces G.X0Below :=
  .rigidContract htec hr hWss hW2 hdef hatt
    ⟨Graph.isX0Graph_rigidContract_induce hG htec hr hWss hatt,
      Graph.rigidContract_vertexSet_ncard_lt hWss.subset hW2⟩

/-- CONTRACT-R's producer at a maximal `def₂`-rigid set ((MC-75)(iii), (MC-89) step 4). -/
theorem _root_.Graph.IsX0Graph.x0Reduces_of_deficiency_two_rigid {G : Graph α β}
    (hG : G.IsX0Graph) (htec : G.TwoEdgeConnected) (hpos : 0 < G.deficiency 2) {Y : Set α}
    (hY : Y ⊆ V(G)) (hY2 : 2 ≤ Y.ncard) (hYd : (G.induce Y).deficiency 2 = 0) :
    G.X0Reduces G.X0Below := by
  obtain ⟨W, hYW, hWV, hWd, hmax⟩ := G.exists_maximal_deficiency_induce_eq_zero 2 hY hYd
  have hW2 : 2 ≤ W.ncard := hY2.trans (Set.ncard_le_ncard hYW (Set.toFinite _))
  have hWne : W ≠ V(G) := by
    rintro rfl
    rw [Graph.induce_vertexSet] at hWd
    omega
  obtain ⟨r, hr⟩ : W.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  refine hG.x0Reduces_of_rigidCore htec hr (hWV.ssubset_of_ne hWne) hW2 hWd ?_
  intro u hu c₁ hc₁ c₂ hc₂ h₁ h₂
  by_contra hne
  have huV : u ∈ V(G) := h₁.left_mem
  have hins := Graph.deficiency_induce_insert_eq_zero (by decide) hWd hu hc₁ hc₂ hne h₁ h₂
  have := hmax (insert u W) (Set.subset_insert _ _) (Set.insert_subset huV hWV) hins
  exact hu (this ▸ Set.mem_insert u W)

omit [Finite β] in
/-- `δ = 0` gives SHORT's and ORBIT's `hdef` (through the landed ear-merge bound). -/
theorem _root_.Graph.IsOpenEar.deficiency_induce_le {G : Graph α β} {V₁ : Set α} {k : ℕ}
    {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β} (hear : G.IsOpenEar V₁ x a b e) {n : ℕ}
    (h : (G.induce V₁).deficiencyMerged n a b = (G.induce V₁).deficiency n) :
    (G.induce V₁).deficiency n ≤ G.deficiency n := by
  have : Nonempty {f : α → α // f a = f b} := ⟨⟨fun _ => a, rfl⟩⟩
  obtain ⟨⟨p, hp⟩, hpeq⟩ := exists_eq_ciSup_of_finite
    (f := fun f : {f : α → α // f a = f b} => (G.induce V₁).partitionDef n f.1)
  refine Graph.deficiency_induce_le_of_ear_of_merge hear.cover hear.inj hear.notMem
    hear.left_mem hear.right_mem hear.isLink hear.sep ⟨p, ?_, hp⟩
  rw [← h]
  exact hpeq

/-- (MC-79)(ii), its first two claims: at a one-body chain of an (S)-graph, `a ≁ b` and
`δ₂ ≥ 2` (ORBIT's `hδ₂` at `k = 1`). -/
theorem _root_.Graph.IsOpenEar.not_adj_and_two_le_pairDelta_two {G : Graph α β} {V₁ : Set α}
    {x : Fin 1 → α} {a b : α} {e : Fin 2 → β} (hear : G.IsOpenEar V₁ x a b e)
    (hSv : ∀ X ⊆ V(G), 2 ≤ X.ncard → 1 ≤ (G.induce X).partitionDef 2 id) :
    ¬ G.Adj a b ∧
      (G.induce V₁).deficiencyMerged 2 a b + 2 ≤ (G.induce V₁).deficiency 2 := by
  have h₀ : G.IsLink (e 0) (x 0) a := (show G.IsLink (e 0) a (x 0) from hear.isLink 0).symm
  have h₁ : G.IsLink (e 1) (x 0) b := hear.isLink 1
  exact Graph.not_adj_and_deficiencyMerged_two_add_two_le hSv
    (hear.cover ▸ Set.subset_union_left) (hear.notMem 0) hear.left_mem hear.right_mem hear.ne
    h₀ h₁

/-- The chain dispatch: a usable chain gives a reduction ((MC-79)(v)). -/
theorem _root_.Graph.IsChain.x0Reduces_of_chainUsable {G : Graph α β} (hG : G.IsX0Graph)
    (h2c : ∀ v ∈ V(G), (G.induce (V(G) \ {v})).Connected)
    (hSv : ∀ X ⊆ V(G), 2 ≤ X.ncard → 1 ≤ (G.induce X).partitionDef 2 id)
    {V₁ : Set α} {k : ℕ} {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β}
    (hC : G.IsChain V₁ x a b e) (hu : G.ChainUsable V₁ k a b) : G.X0Reduces G.X0Below := by
  have hear := hC.toIsOpenEar
  have h₁ : G.X0Below (G.induce V₁) :=
    ⟨hC.isX0Graph_induce hG h2c, hear.ncard_lt hC.one_le⟩
  have hxV : ∀ i, x i ∈ V(G) := fun i => hear.cover ▸ Set.mem_union_right _ ⟨i, rfl⟩
  rcases hu with hk | ⟨rfl, hδ | ⟨hnadj, hδ₂⟩⟩ | ⟨rfl, hδ | hδ⟩
  · rcases Nat.lt_or_ge k 5 with hk5 | hk5
    · obtain rfl | rfl : k = 3 ∨ k = 4 := by omega
      · exact .openEarThree hear h₁
          ⟨hear.isX0Graph_splitOff_three hG, Graph.splitOff_vertexSet_ncard_lt (hxV 1)⟩
      · exact .openEarFour hear h₁
          ⟨hear.isX0Graph_splitOff_four hG, Graph.splitOff_vertexSet_ncard_lt (hxV 1)⟩
    · exact .openEar hear hk5 h₁
  · exact .openEarTwo hear h₁ (hear.deficiency_induce_le hδ)
  · exact .openEarTwoSplitOff hear hnadj h₁
      ⟨hear.isX0Graph_splitOff_orbit hG, Graph.splitOff_vertexSet_ncard_lt (hxV 1)⟩ hδ₂
  · obtain ⟨hnadj, hδ₂⟩ := hear.not_adj_and_two_le_pairDelta_two hSv
    exact .openEarOne hear hnadj h₁ (hear.deficiency_induce_le hδ) hδ₂
  · obtain ⟨hnadj, -⟩ := hear.not_adj_and_two_le_pairDelta_two hSv
    exact .splitOff hear hnadj
      ⟨hear.isX0Graph_splitOff_one hG hnadj, Graph.splitOff_vertexSet_ncard_lt (hxV 0)⟩ hδ

/-! ## Counting bodies of degree two -/

/-- The degree sum `2|E|` over `V(G)` is at least `3|V| − |D₂|`, `D₂` the bodies of degree two. -/
theorem _root_.Graph.IsX0Graph.three_mul_sub_le_two_mul_ncard {G : Graph α β}
    (hG : G.IsX0Graph) :
    3 * (V(G).ncard : ℤ) - ({v ∈ V(G) | G.degree v = 2} : Set α).ncard ≤ 2 * E(G).ncard := by
  classical
  have : G.Finite := { edgeSet_finite := Set.toFinite _, vertexSet_finite := Set.toFinite _ }
  have hhs := Graph.handshake_degree_finset G
  rw [← Set.ncard_eq_toFinset_card _ G.edgeSet_finite] at hhs
  have hle : ∀ v ∈ G.vertexSet_finite.toFinset,
      (3 : ℤ) - (if G.degree v = 2 then 1 else 0) ≤ (G.degree v : ℤ) := by
    intro v hv
    have := hG.two_le_degree v (by simpa using hv)
    split_ifs with h <;> omega
  have hsum := Finset.sum_le_sum hle
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_boole] at hsum
  have hcast : (∑ v ∈ G.vertexSet_finite.toFinset, (G.degree v : ℤ)) = 2 * E(G).ncard := by
    exact_mod_cast hhs
  have hV : G.vertexSet_finite.toFinset.card = V(G).ncard :=
    (Set.ncard_eq_toFinset_card _ _).symm
  have hD : (G.vertexSet_finite.toFinset.filter fun v => G.degree v = 2).card =
      ({v ∈ V(G) | G.degree v = 2} : Set α).ncard := by
    rw [Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
    congr 1
    ext v
    simp
  rw [hcast, hV, nsmul_eq_mul] at hsum
  push_cast [hD] at hsum
  linarith

/-- H1/H2 ((MC-76)'s count): under (S), `Σ (3 − deg) ≥ 4`, so a degree-two body avoids any
three given bodies. -/
theorem _root_.Graph.IsX0Graph.exists_degree_eq_two_notMem {G : Graph α β} (hG : G.IsX0Graph)
    (hSv : ∀ X ⊆ V(G), 2 ≤ X.ncard → 1 ≤ (G.induce X).partitionDef 2 id) {s : Set α}
    (hs : s.ncard ≤ 3) : ∃ v ∈ V(G), G.degree v = 2 ∧ v ∉ s := by
  classical
  have hV3 := hG.three_le_ncard_vertexSet
  have h1 := hSv V(G) subset_rfl (by omega)
  rw [Graph.induce_vertexSet] at h1
  have hval : G.partitionDef 2 id = 3 * ((V(G).ncard : ℤ) - 1) - 2 * E(G).ncard := by
    simp only [Graph.partitionDef, Graph.numParts, Set.image_id, hG.crossingEdges_id,
      Graph.bodyBarDim_two]
    push_cast; ring
  have hc := hG.three_mul_sub_le_two_mul_ncard
  have hD4 : 4 ≤ ({v ∈ V(G) | G.degree v = 2} : Set α).ncard := by
    have : (4 : ℤ) ≤ ({v ∈ V(G) | G.degree v = 2} : Set α).ncard := by linarith
    exact_mod_cast this
  by_contra hno
  push Not at hno
  have hsub : ({v ∈ V(G) | G.degree v = 2} : Set α) ⊆ s := fun v hv => by
    by_contra hvs
    exact hvs (by simpa using (hno v hv.1 hv.2 |> not_not.mpr) ) |>.elim
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

/-- The edges at the bodies of degree two are distinct when no two such bodies are adjacent. -/
theorem _root_.Graph.IsX0Graph.two_mul_ncard_le_ncard_edgeSet {G : Graph α β}
    (hG : G.IsX0Graph) (hhubs : ∀ v w, G.degree v = 2 → G.Adj v w → 3 ≤ G.degree w) :
    2 * ({v ∈ V(G) | G.degree v = 2} : Set α).ncard ≤ E(G).ncard := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have : Fintype β := Fintype.ofFinite β
  set D : Finset α := ({v ∈ V(G) | G.degree v = 2} : Set α).toFinset with hD
  set Ev : α → Finset β := fun v => ({e | G.IsNonloopAt e v} : Set β).toFinset with hEv
  have hdisj : (D : Set α).PairwiseDisjoint Ev := by
    intro v hv w hw hvw
    rw [Function.onFun, Finset.disjoint_left]
    intro e hev hew
    simp only [hEv, Set.mem_toFinset, Set.mem_ofPred_eq] at hev hew
    obtain ⟨y, hyv, hy⟩ := hev
    obtain ⟨z, hzw, hz⟩ := hew
    simp only [hD, Set.coe_toFinset, Set.mem_ofPred_eq] at hv hw
    have hvz : v = z := by
      rcases hy.left_eq_or_eq hz with h | h
      · exact absurd h hvw
      · exact h
    subst hvz
    have := hhubs v w hv.2 ⟨e, hz.symm⟩
    omega
  have hcard : ∀ v ∈ D, (Ev v).card = 2 := by
    intro v hv
    simp only [hD, Set.mem_toFinset, Set.mem_ofPred_eq] at hv
    have h := Graph.degree_eq_ncard_add_ncard G v
    have hl : ({e | G.IsLoopAt e v} : Set β) = ∅ :=
      Set.eq_empty_of_forall_notMem fun e he => hG.simple.toLoopless.not_isLoopAt e v he
    rw [hl, Set.ncard_empty, hv.2] at h
    simp only [hEv, ← Set.ncard_eq_toFinset_card']
    omega
  have hsub : D.biUnion Ev ⊆ E(G).toFinset := by
    intro e he
    simp only [Finset.mem_biUnion, hEv, Set.mem_toFinset, Set.mem_ofPred_eq] at he
    obtain ⟨v, -, hv⟩ := he
    simpa using hv.edge_mem
  have := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisj, Finset.sum_const_nat hcard, ← Set.ncard_eq_toFinset_card',
    ← Set.ncard_eq_toFinset_card'] at this
  omega

/-- H3 ((MC-80)'s rigid case, all chains of one body): if every body of degree two has only
hubs as neighbours, then `5|E| ≥ 6|V|`, so `val₃(G − x, singletons) ≤ −2 ≤ 0`. -/
theorem _root_.Graph.IsX0Graph.partitionDef_three_induce_diff_nonpos {G : Graph α β}
    (hG : G.IsX0Graph) (hhubs : ∀ v w, G.degree v = 2 → G.Adj v w → 3 ≤ G.degree w)
    {x : α} (hx : x ∈ V(G)) (hx2 : G.degree x = 2) :
    (G.induce (V(G) \ {x})).partitionDef 3 id ≤ 0 := by
  classical
  have hxX : x ∉ V(G) \ {x} := fun h => h.2 rfl
  have hins := Graph.partitionDef_induce_insert (G := G) (n := 3) hxX id
  rw [Set.insert_sdiff_singleton, Set.insert_eq_of_mem hx, Graph.induce_vertexSet,
    ite_eq_right (by simp), Graph.bodyBarDim_three] at hins
  have ht : ({e | ∃ y ∈ V(G) \ {x}, G.IsLink e x y ∧ id y ≠ id x} : Set β) =
      {e | G.IsNonloopAt e x} := by
    ext e
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff, id]
    exact ⟨fun ⟨y, ⟨_, hyx⟩, hl, _⟩ => ⟨y, hyx, hl⟩,
      fun ⟨y, hyx, hl⟩ => ⟨y, ⟨hl.right_mem, hyx⟩, hl, hyx⟩⟩
  have hdeg : ({e | G.IsNonloopAt e x} : Set β).ncard = 2 := by
    have h := Graph.degree_eq_ncard_add_ncard G x
    have hl : ({e | G.IsLoopAt e x} : Set β) = ∅ :=
      Set.eq_empty_of_forall_notMem fun e he => hG.simple.toLoopless.not_isLoopAt e x he
    rw [hl, Set.ncard_empty, hx2] at h
    omega
  rw [ht, hdeg] at hins
  have hval : G.partitionDef 3 id = 6 * ((V(G).ncard : ℤ) - 1) - 5 * E(G).ncard := by
    simp only [Graph.partitionDef, Graph.numParts, Set.image_id, hG.crossingEdges_id,
      Graph.bodyBarDim_three]
    push_cast; ring
  have h1 := hG.three_mul_sub_le_two_mul_ncard
  have h2 := hG.two_mul_ncard_le_ncard_edgeSet hhubs
  have h2' : (2 : ℤ) * ({v ∈ V(G) | G.degree v = 2} : Set α).ncard ≤ E(G).ncard := by
    exact_mod_cast h2
  push_cast at hins
  linarith

/-! ## The 4-cycle of a two-body chain -/

/-- The 4-cycle of a two-body chain with adjacent ends is rigid (under (S), it is tight). -/
theorem _root_.Graph.IsOpenEar.deficiency_three_induce_cycle {G : Graph α β} (_hG : G.IsX0Graph)
    {V₁ : Set α} {x : Fin 2 → α} {a b : α} {e : Fin 3 → β} (hear : G.IsOpenEar V₁ x a b e)
    (hadj : G.Adj a b) (hSv : ∀ X ⊆ V(G), 2 ≤ X.ncard → 1 ≤ (G.induce X).partitionDef 2 id) :
    ({a, x 0, x 1, b} : Set α) ⊆ V(G) ∧ 2 ≤ ({a, x 0, x 1, b} : Set α).ncard ∧
      (G.induce {a, x 0, x 1, b}).deficiency 3 = 0 := by
  classical
  obtain ⟨f, hf⟩ := hadj
  have l0 : G.IsLink (e 0) a (x 0) := hear.isLink 0
  have l1 : G.IsLink (e 1) (x 0) (x 1) := hear.isLink 1
  have l2 : G.IsLink (e 2) (x 1) b := hear.isLink 2
  have hax : ∀ i, x i ≠ a := fun i h => hear.notMem i (h ▸ hear.left_mem)
  have hbx : ∀ i, x i ≠ b := fun i h => hear.notMem i (h ▸ hear.right_mem)
  have hx01 : x 0 ≠ x 1 := fun h => absurd (hear.inj h) (by decide)
  have hXV : ({a, x 0, x 1, b} : Set α) ⊆ V(G) := by
    rintro y (rfl | rfl | rfl | rfl)
    · exact l0.left_mem
    · exact l0.right_mem
    · exact l1.right_mem
    · exact l2.right_mem
  have hX4 : ({a, x 0, x 1, b} : Set α).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem (by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨(hax 0).symm, (hax 1).symm, hear.ne⟩) (Set.toFinite _),
      Set.ncard_insert_of_notMem (by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hx01, hbx 0⟩) (Set.toFinite _),
      Set.ncard_pair (hbx 1)]
  have hinj := pathEdge_injective hear.inj hax hbx hear.ne hear.isLink
  have hf0 : f ≠ e 0 := by
    rintro rfl; exact hbx 0 (l0.right_unique hf)
  have hf1 : f ≠ e 1 := by
    rintro rfl
    rcases hf.left_eq_or_eq l1 with h | h
    · exact hax 0 h.symm
    · exact hax 1 h.symm
  have hf2 : f ≠ e 2 := by
    rintro rfl
    rcases hf.left_eq_or_eq l2 with h | h
    · exact hax 1 h.symm
    · exact hear.ne h
  have hF4 : ({e 0, e 1, e 2, f} : Set β).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem (by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨fun h => absurd (hinj h) (by decide), fun h => absurd (hinj h) (by decide),
          fun h => hf0 h.symm⟩) (Set.toFinite _),
      Set.ncard_insert_of_notMem (by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨fun h => absurd (hinj h) (by decide), fun h => hf1 h.symm⟩) (Set.toFinite _),
      Set.ncard_pair (fun h => hf2 h.symm)]
  have hsub : ({e 0, e 1, e 2, f} : Set β) ⊆ (G.induce {a, x 0, x 1, b}).crossingEdges id := by
    rintro g (rfl | rfl | rfl | rfl) <;> rw [Graph.mem_crossingEdges_induce]
    · exact ⟨a, x 0, l0, Or.inl rfl, Or.inr (Or.inl rfl), (hax 0).symm⟩
    · exact ⟨x 0, x 1, l1, Or.inr (Or.inl rfl), Or.inr (Or.inr (Or.inl rfl)), hx01⟩
    · exact ⟨x 1, b, l2, Or.inr (Or.inr (Or.inl rfl)), Or.inr (Or.inr (Or.inr rfl)), hbx 1⟩
    · exact ⟨a, b, hf, Or.inl rfl, Or.inr (Or.inr (Or.inr rfl)), hear.ne⟩
  have hcard := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [hF4] at hcard
  have hval : (G.induce {a, x 0, x 1, b}).partitionDef 2 id ≤ 1 := by
    simp only [Graph.partitionDef, Graph.numParts, Set.image_id, Graph.vertexSet_induce, hX4,
      Graph.bodyBarDim_two]
    have : (4 : ℤ) ≤ ((G.induce {a, x 0, x 1, b}).crossingEdges id).ncard := by
      exact_mod_cast hcard
    push_cast
    linarith
  exact ⟨hXV, by omega, Graph.deficiency_three_induce_eq_zero_of_tight
    (fun Z hZ => hSv Z (hZ.trans hXV)) (by omega) hval⟩

/-! ## Theorem S and the covering theorem -/

/-- The core producer: a maximal rigid superset of a rigid `Y` avoiding `X₀` is an additive core
with the attachment condition. -/
theorem _root_.Graph.IsX0Graph.exists_additiveCore_of_rigid {G : Graph α β}
    (hG : G.IsX0Graph)
    (hSv : ∀ X ⊆ V(G), 2 ≤ X.ncard → 1 ≤ (G.induce X).partitionDef 2 id)
    {X₀ Y : Set α} (hX₀ : X₀.Subsingleton) (hX₀V : X₀ ⊆ V(G)) (hYX₀ : Y ⊆ V(G) \ X₀)
    (hY2 : 2 ≤ Y.ncard) (hYd : (G.induce Y).deficiency 3 = 0)
    (hprop : X₀ = ∅ → G.deficiency 3 ≠ 0) (hdeg : ∀ x ∈ X₀, G.degree x ≤ 2)
    (hattX : ∀ x ∈ X₀, ∀ W ⊆ V(G) \ X₀, 2 ≤ W.ncard → (G.induce W).deficiency 3 = 0 →
      ∀ c₁ ∈ W, ∀ c₂ ∈ W, G.Adj x c₁ → G.Adj x c₂ → c₁ = c₂) :
    ∃ W r, r ∈ W ∧ W ⊂ V(G) ∧ 2 ≤ W.ncard ∧ (G.induce W).deficiency 3 = 0 ∧
      (G.induce W).deficiency 2 + (G.rigidContract (G.induce W) r).deficiency 2 ≤
        G.deficiency 2 ∧
      ∀ u ∉ W, ∀ c₁ ∈ W, ∀ c₂ ∈ W, G.Adj u c₁ → G.Adj u c₂ → c₁ = c₂ := by
  obtain ⟨W, hYW, hWU, hWd, hmax⟩ := G.exists_maximal_deficiency_induce_eq_zero 3 hYX₀ hYd
  have hWV : W ⊆ V(G) := hWU.trans Set.sdiff_subset
  have hW2 : 2 ≤ W.ncard := hY2.trans (Set.ncard_le_ncard hYW (Set.toFinite _))
  obtain ⟨r, hr⟩ : W.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  have hWX₀ : Disjoint W X₀ := Set.disjoint_left.mpr fun w hw hwX₀ => (hWU hw).2 hwX₀
  have hWss : W ⊂ V(G) := by
    refine hWV.ssubset_of_ne fun hWeq => ?_
    have hX₀e : X₀ = ∅ := Set.eq_empty_of_forall_notMem fun x hx =>
      Set.disjoint_left.mp hWX₀ (hWeq ▸ hX₀V hx) hx
    apply hprop hX₀e
    rw [← Graph.induce_vertexSet G, ← hWeq]
    exact hWd
  have hattW : ∀ u ∉ W, ∀ c₁ ∈ W, ∀ c₂ ∈ W, G.Adj u c₁ → G.Adj u c₂ → c₁ = c₂ := by
    intro u hu c₁ hc₁ c₂ hc₂ h₁ h₂
    by_cases huX₀ : u ∈ X₀
    · exact hattX u huX₀ W hWU hW2 hWd c₁ hc₁ c₂ hc₂ h₁ h₂
    by_contra hne
    have hins := Graph.deficiency_induce_insert_eq_zero (by decide) hWd hu hc₁ hc₂ hne h₁ h₂
    have := hmax (insert u W) (Set.subset_insert _ _)
      (Set.insert_subset ⟨h₁.left_mem, huX₀⟩ hWU) hins
    exact hu (this ▸ Set.mem_insert u W)
  have hmono := Graph.partitionDef_induce_id_le_of_maximal hSv ⟨r, hr⟩ hWX₀ hWd
    hmax hX₀ (fun x hx Y' hxY' => (Graph.ncard_setOf_isLink_le_degree hxY').trans (hdeg x hx))
    (fun x hx => Graph.ncard_setOf_isLink_le_one hG.simple (hattX x hx W hWU hW2 hWd))
  exact ⟨W, r, hr, hWss, hW2, hWd,
    Graph.deficiency_induce_add_deficiency_rigidContract_le hSv hWV hr hmono, hattW⟩

/-- **Theorem S** in the Lean steps' form ((MC-80) with (MC-87)): an (S)-graph none of whose
chains is usable has an additive core with the attachment condition. -/
theorem _root_.Graph.IsX0Graph.exists_additiveCore {G : Graph α β} (hG : G.IsX0Graph)
    (h2c : ∀ v ∈ V(G), (G.induce (V(G) \ {v})).Connected)
    (hhub : ∃ w ∈ V(G), G.degree w ≠ 2)
    (hS : ∀ X ⊆ V(G), 2 ≤ X.ncard → (G.induce X).deficiency 2 ≠ 0)
    (hblk : ∀ (V₁ : Set α) (k : ℕ) (x : Fin k → α) (a b : α) (e : Fin (k + 1) → β),
      G.IsChain V₁ x a b e → ¬ G.ChainUsable V₁ k a b) :
    ∃ W r, r ∈ W ∧ W ⊂ V(G) ∧ 2 ≤ W.ncard ∧ (G.induce W).deficiency 3 = 0 ∧
      (G.induce W).deficiency 2 + (G.rigidContract (G.induce W) r).deficiency 2 ≤
        G.deficiency 2 ∧
      ∀ u ∉ W, ∀ c₁ ∈ W, ∀ c₂ ∈ W, G.Adj u c₁ → G.Adj u c₂ → c₁ = c₂ := by
  have hSv := Graph.one_le_partitionDef_induce_id hS
  -- a blocked two-body chain has adjacent ends, and its 4-cycle is rigid
  have hk2 : ∀ (V₁ : Set α) (x : Fin 2 → α) (a b : α) (e : Fin 3 → β),
      G.IsChain V₁ x a b e → G.Adj a b := by
    intro V₁ x a b e hC
    have hb := hblk _ _ _ _ _ _ hC
    have hδ : (G.induce V₁).deficiencyMerged 3 a b ≠ (G.induce V₁).deficiency 3 :=
      fun h => hb (Or.inr (Or.inl ⟨rfl, Or.inl h⟩))
    have hnot : ¬ G.Adj a b → ¬ ((G.induce V₁).deficiencyMerged 2 a b + 2 ≤
        (G.induce V₁).deficiency 2) := fun hn h => hb (Or.inr (Or.inl ⟨rfl, Or.inr ⟨hn, h⟩⟩))
    by_contra hnadj
    have hSv' : ∀ X ⊆ V(G.induce V₁), 2 ≤ X.ncard →
        1 ≤ ((G.induce V₁).induce X).partitionDef 2 id := fun X hX hX2 => by
      have hX' : X ⊆ V₁ := hX
      rw [Graph.induce_induce_of_subset G hX']
      exact hSv X (hX'.trans (hC.cover ▸ Set.subset_union_left)) hX2
    have hnadj' : ¬ (G.induce V₁).Adj a b := fun ⟨f, hf⟩ => hnadj ⟨f, hf.1⟩
    exact hnot hnadj (Graph.deficiencyMerged_two_add_two_le hSv' hC.left_mem hC.right_mem hC.ne
      hnadj' hδ)
  obtain ⟨v, hv, hv2, -⟩ := hG.exists_degree_eq_two_notMem hSv (s := ∅) (by simp)
  obtain ⟨V₁, k, x, a, b, e, hC, hvx⟩ := hG.exists_isChain h2c hhub hv hv2
  have hbC := hblk _ _ _ _ _ _ hC
  have hk3 : k < 3 := Nat.lt_of_not_le fun h => hbC (Or.inl h)
  by_cases hrig : G.deficiency 3 = 0
  · -- the rigid case: a body `x₀` of degree two and a rigid set avoiding it
    obtain ⟨x₀, hx₀V, hx₀2, Y, hYx₀, hY2, hYd⟩ : ∃ x₀ ∈ V(G), G.degree x₀ = 2 ∧
        ∃ Y ⊆ V(G) \ {x₀}, 2 ≤ Y.ncard ∧ (G.induce Y).deficiency 3 = 0 := by
      by_cases hadj : ∃ v w, G.degree v = 2 ∧ G.degree w = 2 ∧ v ∈ V(G) ∧ G.Adj v w
      · obtain ⟨v', w', hv'2, hw'2, hv'V, hv'w'⟩ := hadj
        obtain ⟨V₁', k', x', a', b', e', hC', hv'x'⟩ := hG.exists_isChain h2c hhub hv'V hv'2
        have h2 := hC'.two_le_of_adj hv'x' hv'w' hw'2
        have h3 : k' < 3 := Nat.lt_of_not_le fun h => hblk _ _ _ _ _ _ hC' (Or.inl h)
        obtain rfl : k' = 2 := by omega
        have hab' := hk2 _ _ _ _ _ hC'
        obtain ⟨hcycV, hcyc2, hcycd⟩ :=
          hC'.toIsOpenEar.deficiency_three_induce_cycle hG hab' hSv
        obtain ⟨x₀, hx₀V, hx₀2, hx₀s⟩ :=
          hG.exists_degree_eq_two_notMem hSv (s := {x' 0, x' 1})
            ((Set.ncard_pair_le _ _).trans (by norm_num))
        refine ⟨x₀, hx₀V, hx₀2, _, fun y hy => ⟨hcycV hy, ?_⟩, hcyc2, hcycd⟩
        rintro rfl
        rcases hy with rfl | rfl | rfl | rfl
        · exact absurd hx₀2 (by have := hC'.three_le_degree_left; omega)
        · exact hx₀s (Or.inl rfl)
        · exact hx₀s (Or.inr rfl)
        · exact absurd hx₀2 (by have := hC'.three_le_degree_right; omega)
      · push Not at hadj
        have hhubs : ∀ v w, G.degree v = 2 → G.Adj v w → 3 ≤ G.degree w := by
          intro v w hv2' hvw
          have := hG.two_le_degree w hvw.right_mem
          by_contra h3
          exact hadj v w hv2' (by omega) hvw.left_mem hvw
        have hval := hG.partitionDef_three_induce_diff_nonpos hhubs hv hv2
        have hcard : 2 ≤ (V(G) \ {v}).ncard := by
          have h3 : 3 ≤ V(G).ncard := hG.three_le_ncard_vertexSet
          rw [Set.ncard_sdiff_singleton_of_mem hv]; omega
        obtain ⟨Y, hYs, hY2, hYd⟩ :=
          Graph.exists_deficiency_induce_eq_zero_of_partitionDef_id_nonpos
            (G := G) (n := 3) Set.sdiff_subset hcard hval
        exact ⟨v, hv, hv2, Y, hYs, hY2, hYd⟩
    refine hG.exists_additiveCore_of_rigid hSv (X₀ := {x₀}) Set.subsingleton_singleton
      (Set.singleton_subset_iff.mpr hx₀V) hYx₀ hY2 hYd (fun h => absurd h
        (Set.singleton_ne_empty x₀)) (fun y hy => by rw [Set.mem_singleton_iff.mp hy, hx₀2]) ?_
    rintro y hy W hW hW2 hWd c₁ hc₁ c₂ hc₂ h₁ h₂
    rw [Set.mem_singleton_iff] at hy
    subst hy
    by_contra hne
    have hWV : W ⊆ V(G) := hW.trans Set.sdiff_subset
    have hyW : y ∉ W := fun h => (hW h).2 rfl
    -- a neighbour of degree two in a rigid set would have degree `≤ 1` there
    have hhub : ∀ c ∈ W, G.Adj y c → 3 ≤ G.degree c := by
      intro c hc hyc
      have h2 := Graph.two_le_degree_of_isKDof_zero (G := G.induce W) (n := 3) (by decide) hWd
        hc hW2
      have hlt := Graph.degree_induce_lt_of_adj hc hyW hyc.symm
      have := hG.two_le_degree c (hWV hc)
      by_contra h3
      omega
    obtain ⟨e₁, he₁⟩ := h₁
    obtain ⟨e₂, he₂⟩ := h₂
    have hC₁ := hG.isChain_one hx₀2 he₁.symm he₂ hne (hhub c₁ hc₁ ⟨e₁, he₁⟩)
      (hhub c₂ hc₂ ⟨e₂, he₂⟩)
    have hb₁ := hblk _ _ _ _ _ _ hC₁
    apply hb₁ (Or.inr (Or.inr ⟨rfl, Or.inl ?_⟩))
    have hWd' : ((G.induce (V(G) \ {y})).induce W).deficiency 3 = 0 := by
      rwa [Graph.induce_induce_of_subset G hW]
    exact Graph.deficiencyMerged_eq_deficiency_of_mem (by decide) hW hWd' hc₁ hc₂
  · -- the non-rigid case: one blocked chain lies in a rigid set
    obtain ⟨Y, hYV, hY2, hYd⟩ : ∃ Y ⊆ V(G), 2 ≤ Y.ncard ∧ (G.induce Y).deficiency 3 = 0 := by
      have hk1 := hC.one_le
      obtain rfl | rfl : k = 1 ∨ k = 2 := by omega
      · by_contra hno
        push Not at hno
        apply hbC (Or.inr (Or.inr ⟨rfl, Or.inr ?_⟩))
        exact Graph.deficiencyMerged_three_add_five_le (hC.cover ▸ Set.subset_union_left)
          (hC.notMem 0) hC.left_mem hC.right_mem hC.ne
          (show G.IsLink (e 0) a (x 0) from hC.isLink 0).symm (hC.isLink 1)
          (fun Y hY _ hY2 => hno Y hY hY2)
      · obtain ⟨hcycV, hcyc2, hcycd⟩ :=
          hC.toIsOpenEar.deficiency_three_induce_cycle hG (hk2 _ _ _ _ _ hC) hSv
        exact ⟨_, hcycV, hcyc2, hcycd⟩
    exact hG.exists_additiveCore_of_rigid hSv (X₀ := ∅) Set.subsingleton_empty
      (Set.empty_subset _) (by simpa using hYV) hY2 hYd (fun _ => hrig) (by simp) (by simp)

/-- (MC-89)'s step 5: an (S)-graph that is 2-connected and not a cycle reduces (θ-graphs
included: their longest path is a usable chain, and Theorem S's proof does not exclude them). -/
theorem _root_.Graph.IsX0Graph.x0Reduces_of_sparse {G : Graph α β} (hG : G.IsX0Graph)
    (h2c : ∀ v ∈ V(G), (G.induce (V(G) \ {v})).Connected) (htec : G.TwoEdgeConnected)
    (hhub : ∃ w ∈ V(G), G.degree w ≠ 2)
    (hS : ∀ X ⊆ V(G), 2 ≤ X.ncard → (G.induce X).deficiency 2 ≠ 0) :
    G.X0Reduces G.X0Below := by
  have hSv := Graph.one_le_partitionDef_induce_id hS
  by_cases hu : ∃ (V₁ : Set α) (k : ℕ) (x : Fin k → α) (a b : α) (e : Fin (k + 1) → β),
      G.IsChain V₁ x a b e ∧ G.ChainUsable V₁ k a b
  · obtain ⟨V₁, k, x, a, b, e, hC, hCu⟩ := hu
    exact hC.x0Reduces_of_chainUsable hG h2c hSv hCu
  · push Not at hu
    obtain ⟨W, r, hr, hWss, hW2, hdef3, hadd, hatt⟩ := hG.exists_additiveCore h2c hhub hS hu
    exact hG.x0Reduces_of_additiveCore htec hr hWss hW2 hdef3 hadd hatt

/-- **The covering theorem** ((MC-89)'s case analysis): every (H)-graph reduces by one landed
step to smaller (H)-graphs. -/
theorem _root_.Graph.IsX0Graph.x0Reduces {G : Graph α β} (hG : G.IsX0Graph) :
    G.X0Reduces G.X0Below := by
  by_cases htec : G.TwoEdgeConnected
  swap
  · exact hG.x0Reduces_of_not_twoEdgeConnected htec
  by_cases h2c : ∀ v ∈ V(G), (G.induce (V(G) \ {v})).Connected
  swap
  · push Not at h2c
    obtain ⟨v, hv, hdisc⟩ := h2c
    exact hG.x0Reduces_of_not_connected htec hv hdisc
  by_cases hcyc : ∀ v ∈ V(G), G.degree v = 2
  · exact hG.x0Reduces_of_forall_degree_eq_two hcyc
  push Not at hcyc
  by_cases hflat : G.deficiency 2 = G.deficiency 3
  · exact .flat hflat
  have hpos : 0 < G.deficiency 2 := by
    have h3 := Graph.Connected.deficiency_three_le_deficiency_two hG.connected
    have h0 := Graph.deficiency_nonneg G 3 hG.connected.nonempty
    omega
  by_cases hrig : ∃ Y ⊆ V(G), 2 ≤ Y.ncard ∧ (G.induce Y).deficiency 2 = 0
  · obtain ⟨Y, hY, hY2, hYd⟩ := hrig
    exact hG.x0Reduces_of_deficiency_two_rigid htec hpos hY hY2 hYd
  push Not at hrig
  exact hG.x0Reduces_of_sparse h2c htec hcyc hrig

/-- **(MC-10)(a)**: `X₀(G)`'s general point attains at every simple connected graph of minimum
degree two. Pinned at `thm:pencil-x0-coverage` (whose statement carries this attainment
consequence); also `thm:pencil-x0-generic-attains`'s first sentence, pinned at MOTIVES. -/
theorem _root_.Graph.IsX0Graph.x0Attains [Infinite K] {G : Graph α β} (hG : G.IsX0Graph) :
    G.X0Attains K :=
  Graph.X0Attains.of_isX0Graph_of_x0Reduces (fun _ hG' => hG'.x0Reduces) hG

/-- The consumer's form (MOTIVES, `X0Dist`'s graphs): simple, 2EC, `3 ≤ |V|`. -/
theorem _root_.Graph.X0Attains.of_twoEdgeConnected [Infinite K] {G : Graph α β}
    (hS : G.Simple) (hV : 3 ≤ V(G).ncard) (htec : G.TwoEdgeConnected) : G.X0Attains K :=
  Graph.IsX0Graph.x0Attains
    { simple := hS
      connected := Graph.connected_iff.mpr ⟨Set.nonempty_of_ncard_ne_zero (by omega),
        Graph.preconnected_of_twoEdgeConnected htec⟩
      two_le_degree := fun v hv => Graph.two_le_degree_of_twoEdgeConnected htec hv (by omega) }

end CombinatorialRigidity.Molecular
