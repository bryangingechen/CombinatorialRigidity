/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.TheoremS

/-!
# Chains in every dimension

The two nodes of `sec:pencil-d-chains` (`blueprint/src/chapter/pencil-d.tex`), with
`D = bodyBarDim n`.

## Main results

* `Graph.IsChain.partitionDef_induce_le`: `lem:pencil-d-chain-count`, when every chain has at most
  `ℓ` interior bodies and `3 (ℓ + 1) ≤ D`, the singleton value of the side `V₁` of a chain is at
  most `-(ℓ + 1)`.
* `Graph.IsX0Graph.exists_chain_or_core`: `thm:pencil-d-chain-or-core`, a chain with more than `ℓ`
  interior bodies, or a core at `n`, or every chain has one interior body and `def₃ = def_n = 0`.

The interior sets of the chains partition the bodies of degree two (a chain through a body of
degree two is unique up to reversal, `Graph.IsChain.range_subset_of_mem`), and the edges at the
interior bodies of distinct chains are disjoint, `|S| + 1` of them for a chain with interior `S`.
So, with `T` the bodies of degree two and `c` the chains (up to reversal), `T + c ≤ |E(G)|` and
`T - k ≤ ℓ (c - 1)`; with `3|V(G)| - T ≤ 2|E(G)|` (`three_mul_sub_le_two_mul_ncard`) and
`3(ℓ + 1) ≤ D` the singleton value of `V₁` is at most `-(ℓ + 1)`. This departs from the chapter's
proof, which counts segments (`notes/Cleanup42.md` R-17).
-/

@[expose] public section

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {α β : Type*}

/-- **Counting edges when every chain has few interior bodies** (`lem:pencil-d-chain-count`). -/
theorem _root_.Graph.IsChain.partitionDef_induce_le [Finite α] [Finite β] {G : Graph α β}
    (hG : G.IsX0Graph) (h2c : ∀ v ∈ V(G), (G.induce (V(G) \ {v})).Connected)
    (hhub : ∃ w ∈ V(G), G.degree w ≠ 2) {n ℓ : ℕ} (hℓ : 3 * (ℓ + 1) ≤ Graph.bodyBarDim n)
    (hshort : ∀ (V₁ : Set α) (k : ℕ) (x : Fin k → α) (a b : α) (e : Fin (k + 1) → β),
      G.IsChain V₁ x a b e → k ≤ ℓ)
    {V₁ : Set α} {k : ℕ} {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β}
    (hC : G.IsChain V₁ x a b e) :
    (G.induce V₁).partitionDef n id ≤ -((ℓ : ℤ) + 1) := by
  have := hG.simple
  set D₂ : Set α := {v ∈ V(G) | G.degree v = 2} with hD₂
  set 𝒞 : Set (Set α) := {S | ∃ (W : Set α) (j : ℕ) (y : Fin j → α) (c d : α)
    (f : Fin (j + 1) → β), G.IsChain W y c d f ∧ S = Set.range y} with h𝒞
  set inc : Set α → Set β := fun S => {f | ∃ y ∈ S, G.Inc f y} with hinc
  have hxC : Set.range x ∈ 𝒞 := ⟨V₁, k, x, a, b, e, hC, rfl⟩
  -- the classes: interiors of chains, pairwise disjoint
  have hdisj : 𝒞.PairwiseDisjoint id := by
    rintro _ ⟨W, j, y, c, d, f, hy, rfl⟩ _ ⟨W', j', y', c', d', f', hy', rfl⟩ hne
    refine Set.disjoint_left.mpr fun z hz hz' => hne ?_
    exact (hy.range_subset_of_mem hy' hz hz').antisymm (hy'.range_subset_of_mem hy hz' hz)
  have hcover : ⋃ S ∈ 𝒞, id S = D₂ := by
    ext v
    simp only [id, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨_, ⟨W, j, y, c, d, f, hy, rfl⟩, ⟨i, rfl⟩⟩
      exact ⟨hy.cover ▸ Or.inr ⟨i, rfl⟩, hy.degree_eq_two i⟩
    · rintro ⟨hv, hv2⟩
      obtain ⟨W, j, y, c, d, f, hy, hvy⟩ := hG.exists_isChain h2c hhub hv2
      exact ⟨_, ⟨W, j, y, c, d, f, hy, rfl⟩, hvy⟩
  have hsize : ∀ S ∈ 𝒞, S.ncard ≤ ℓ := by
    rintro _ ⟨W, j, y, c, d, f, hy, rfl⟩
    rw [Set.ncard_range_of_injective hy.inj, Nat.card_fin]
    exact hshort _ _ _ _ _ _ hy
  -- the edges at the interior bodies of a chain: at least one more than the bodies
  have hincsize : ∀ S ∈ 𝒞, S.ncard + 1 ≤ (inc S).ncard := by
    rintro _ ⟨W, j, y, c, d, f, hy, rfl⟩
    have hyc : ∀ i, y i ≠ c := fun i h => hy.notMem i (h ▸ hy.left_mem)
    have hyd : ∀ i, y i ≠ d := fun i h => hy.notMem i (h ▸ hy.right_mem)
    have hf := pathEdge_injective hy.inj hyc hyd hy.ne hy.isLink
    have := Set.ncard_le_ncard (hy.toIsOpenEar.range_subset_inc hy.one_le) (Set.toFinite _)
    rw [Set.ncard_range_of_injective hf, Nat.card_fin] at this
    rw [Set.ncard_range_of_injective hy.inj, Nat.card_fin]
    exact this
  have hincdisj : 𝒞.PairwiseDisjoint inc := by
    rintro S hS S' hS' hne
    refine Set.disjoint_left.mpr fun f ⟨z, hz, hzf⟩ ⟨z', hz', hz'f⟩ => ?_
    obtain ⟨W, j, y, c, d, g, hy, rfl⟩ := hS
    obtain ⟨w, hw⟩ := hzf
    have hD : Disjoint (Set.range y) S' := hdisj ⟨W, j, y, c, d, g, hy, rfl⟩ hS' hne
    have hz'2 : G.degree z' = 2 := by
      have : z' ∈ D₂ := hcover ▸ Set.mem_biUnion hS' hz'
      exact this.2
    rcases hz'f.eq_or_eq_of_isLink hw with rfl | rfl
    · exact Set.disjoint_left.mp hD hz hz'
    · exact Set.disjoint_left.mp hD (hy.mem_range_of_adj hz ⟨f, hw⟩ hz'2) hz'
  -- the sums over the classes, as `Finset` sums
  set 𝒞f : Finset (Set α) := (Set.toFinite 𝒞).toFinset with h𝒞f
  have hmem : ∀ S, S ∈ 𝒞f ↔ S ∈ 𝒞 := fun S => Set.Finite.mem_toFinset _
  have hc : 𝒞.ncard = 𝒞f.card := Set.ncard_eq_toFinset_card 𝒞 (Set.toFinite 𝒞)
  have hT : D₂.ncard = ∑ S ∈ 𝒞f, S.ncard := by
    rw [← hcover, (Set.toFinite 𝒞).ncard_biUnion (fun _ _ => Set.toFinite _) hdisj,
      finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite 𝒞)]
    rfl
  -- F2: `T + c ≤ |E(G)|`
  have hF2 : D₂.ncard + 𝒞.ncard ≤ E(G).ncard := by
    have hU : (⋃ S ∈ 𝒞, inc S) ⊆ E(G) := by
      simp only [Set.iUnion_subset_iff]
      rintro S - f ⟨y, -, hf⟩
      exact hf.edge_mem
    have h1 := Set.ncard_le_ncard hU (Set.toFinite _)
    rw [(Set.toFinite 𝒞).ncard_biUnion (fun _ _ => Set.toFinite _) hincdisj,
      finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite 𝒞)] at h1
    have h2 : ∑ S ∈ 𝒞f, (S.ncard + 1) ≤ ∑ S ∈ 𝒞f, (inc S).ncard :=
      Finset.sum_le_sum fun S hS => hincsize S ((hmem S).mp hS)
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] at h2
    rw [hT, hc]
    exact h2.trans h1
  -- F3: `T ≤ k + ℓ (c − 1)`
  have hF3 : D₂.ncard + ℓ ≤ k + ℓ * 𝒞.ncard := by
    have hx𝒞 : Set.range x ∈ 𝒞f := (hmem _).mpr hxC
    rw [hT, hc, ← Finset.add_sum_erase _ _ hx𝒞, Set.ncard_range_of_injective hC.inj,
      Nat.card_fin]
    have hle : ∑ S ∈ 𝒞f.erase (Set.range x), S.ncard ≤ (𝒞f.erase (Set.range x)).card • ℓ :=
      Finset.sum_le_card_nsmul _ _ _ fun S hS => hsize S ((hmem S).mp (Finset.mem_of_mem_erase hS))
    rw [Finset.card_erase_of_mem hx𝒞, smul_eq_mul] at hle
    have h1 : 1 ≤ 𝒞f.card := Finset.card_pos.mpr ⟨_, hx𝒞⟩
    have : (𝒞f.card - 1) * ℓ + ℓ = ℓ * 𝒞f.card := by
      rw [Nat.sub_mul, one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left ℓ h1), mul_comm]
    omega
  -- F1: `3|V(G)| − T ≤ 2|E(G)|`
  have hF1 := hG.three_mul_sub_le_two_mul_ncard
  -- F0: the singleton value of `V₁`
  have hV : V(G).ncard = V₁.ncard + k := by
    rw [hC.cover]
    exact Set.ncard_union_range_of_injective hC.inj hC.notMem
  have hE : E(G).ncard ≤ ((G.induce V₁).crossingEdges id).ncard + (k + 1) := by
    have hxa : ∀ i, x i ≠ a := fun i h => hC.notMem i (h ▸ hC.left_mem)
    have hxb : ∀ i, x i ≠ b := fun i h => hC.notMem i (h ▸ hC.right_mem)
    have hsub : E(G) ⊆ (G.induce V₁).crossingEdges id ∪ Set.range e := by
      intro f hf
      by_cases hfe : ∃ i, f = e i
      · obtain ⟨i, rfl⟩ := hfe
        exact Or.inr ⟨i, rfl⟩
      · push Not at hfe
        obtain ⟨u, w, hl⟩ := Graph.exists_isLink_of_mem_edgeSet hf
        obtain ⟨hu, hw⟩ := hC.sep f u w hl hfe
        have hl' : (G.induce V₁).IsLink f u w := by
          rw [Graph.induce_isLink]; exact ⟨hl, hu, hw⟩
        refine Or.inl ⟨hl'.edge_mem, u, w, hl', fun huw => ?_⟩
        exact Graph.Loopless.not_isLoopAt f u (by rw [show w = u from huw.symm] at hl; exact hl)
    have := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_union_le _ _)
    rwa [Set.ncard_range_of_injective (pathEdge_injective hC.inj hxa hxb hC.ne hC.isLink),
      Nat.card_fin] at this
  have hval : (G.induce V₁).partitionDef n id =
      (Graph.bodyBarDim n : ℤ) * ((V₁.ncard : ℤ) - 1) -
        ((Graph.bodyBarDim n : ℤ) - 1) * ((G.induce V₁).crossingEdges id).ncard := by
    simp only [Graph.partitionDef, Graph.numParts, Set.image_id, Graph.vertexSet_induce]
  -- the count
  rw [hval]
  have hD : 3 * ((ℓ : ℤ) + 1) ≤ (Graph.bodyBarDim n : ℤ) := by exact_mod_cast hℓ
  have hV' : (V(G).ncard : ℤ) = V₁.ncard + k := by exact_mod_cast hV
  have hE' : (E(G).ncard : ℤ) ≤ ((G.induce V₁).crossingEdges id).ncard + (k + 1) := by
    exact_mod_cast hE
  have hF2' : (D₂.ncard : ℤ) + 𝒞.ncard ≤ E(G).ncard := by exact_mod_cast hF2
  have hF3' : (D₂.ncard : ℤ) + ℓ ≤ k + ℓ * 𝒞.ncard := by exact_mod_cast hF3
  have hc0 : (0 : ℤ) ≤ 𝒞.ncard := by positivity
  have h0 : (Graph.bodyBarDim n : ℤ) * V(G).ncard =
      (Graph.bodyBarDim n : ℤ) * V₁.ncard + (Graph.bodyBarDim n : ℤ) * k := by
    rw [hV']; ring
  have h1 : ((Graph.bodyBarDim n : ℤ) - 1) * ((E(G).ncard : ℤ) - (k + 1)) ≤
      ((Graph.bodyBarDim n : ℤ) - 1) * ((G.induce V₁).crossingEdges id).ncard :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h2 : (Graph.bodyBarDim n : ℤ) * (3 * V(G).ncard - D₂.ncard) ≤
      (Graph.bodyBarDim n : ℤ) * (2 * E(G).ncard) :=
    mul_le_mul_of_nonneg_left hF1 (by linarith)
  have h3 : ((Graph.bodyBarDim n : ℤ) - 3) * 𝒞.ncard ≤
      ((Graph.bodyBarDim n : ℤ) - 3) * ((E(G).ncard : ℤ) - D₂.ncard) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h4 : 3 * (ℓ : ℤ) * 𝒞.ncard ≤ ((Graph.bodyBarDim n : ℤ) - 3) * 𝒞.ncard :=
    mul_le_mul_of_nonneg_right (by linarith) hc0
  linarith

/-- **A chain with many interior bodies, a core, or rigidity in dimension three**
(`thm:pencil-d-chain-or-core`). -/
theorem _root_.Graph.IsX0Graph.exists_chain_or_core [Finite α] [Finite β] {G : Graph α β}
    (hG : G.IsX0Graph) (h2c : ∀ v ∈ V(G), (G.induce (V(G) \ {v})).Connected)
    (hhub : ∃ w ∈ V(G), G.degree w ≠ 2)
    (hS : ∀ X ⊆ V(G), 2 ≤ X.ncard → (G.induce X).deficiency 2 ≠ 0)
    {n ℓ : ℕ} (hn : 3 ≤ n) (hℓ : 3 * (ℓ + 1) ≤ Graph.bodyBarDim n) :
    (∃ (V₁ : Set α) (k : ℕ) (x : Fin k → α) (a b : α) (e : Fin (k + 1) → β),
        G.IsChain V₁ x a b e ∧ ℓ < k) ∨
    (∃ W, ∃ r ∈ W, W ⊂ V(G) ∧ 2 ≤ W.ncard ∧ (G.induce W).deficiency n = 0 ∧
        (G.induce W).deficiency 2 + (G.rigidContract (G.induce W) r).deficiency 2 ≤
          G.deficiency 2 ∧
        ∀ u ∉ W, ∀ c₁ ∈ W, ∀ c₂ ∈ W, G.Adj u c₁ → G.Adj u c₂ → c₁ = c₂) ∨
    ((∀ (V₁ : Set α) (k : ℕ) (x : Fin k → α) (a b : α) (e : Fin (k + 1) → β),
        G.IsChain V₁ x a b e → k = 1) ∧ G.deficiency 3 = 0 ∧ G.deficiency n = 0) := by
  have hSv := Graph.one_le_partitionDef_induce_id hS
  by_cases hlong : ∃ (V₁ : Set α) (k : ℕ) (x : Fin k → α) (a b : α) (e : Fin (k + 1) → β),
      G.IsChain V₁ x a b e ∧ ℓ < k
  · exact Or.inl hlong
  push Not at hlong
  -- a chain with two or more interior bodies: the count, then the core at that chain
  by_cases htwo : ∃ (V₁ : Set α) (k : ℕ) (x : Fin k → α) (a b : α) (e : Fin (k + 1) → β),
      G.IsChain V₁ x a b e ∧ 2 ≤ k
  · obtain ⟨V₁, k, x, a, b, e, hC, hk⟩ := htwo
    have hs := hC.partitionDef_induce_le hG h2c hhub hℓ hlong
    obtain ⟨W, r, -, hr, hWss, hW2, hWd, hadd, hatt⟩ :=
      hC.toIsOpenEar.exists_additiveCoreAt_of_partitionDef_nonpos hG (by omega) hSv hk
        (hs.trans (by omega))
    exact Or.inr (Or.inl ⟨W, r, hr, hWss, hW2, hWd, hadd, hatt⟩)
  push Not at htwo
  -- every chain has one interior body, so no two bodies of degree two are adjacent
  have hone : ∀ (V₁ : Set α) (k : ℕ) (x : Fin k → α) (a b : α) (e : Fin (k + 1) → β),
      G.IsChain V₁ x a b e → k = 1 := fun V₁ k x a b e hC => by
    have := hC.one_le
    have := htwo V₁ k x a b e hC
    omega
  have hhubs : ∀ v w, G.degree v = 2 → G.Adj v w → 3 ≤ G.degree w := by
    intro v w hv hvw
    obtain ⟨V₁, k, x, a, b, e, hC, hvx⟩ := hG.exists_isChain h2c hhub hv
    by_contra h3
    have hw2 : G.degree w = 2 := by
      have := hG.two_le_degree w hvw.right_mem
      omega
    have := hC.two_le_of_adj hvx hvw hw2
    have := hone V₁ k x a b e hC
    omega
  by_cases hpos : 0 < G.deficiency 3
  · exact Or.inr (Or.inl (hG.exists_core_of_deficiency_three_pos hn hSv hhubs hpos))
  · have h3 : G.deficiency 3 = 0 :=
      le_antisymm (by omega) (Graph.deficiency_nonneg G 3 hG.connected.nonempty)
    exact Or.inr (Or.inr ⟨hone, h3, Graph.deficiency_eq_zero_of_deficiency_eq_zero_of_le
      (by decide) hn hG.connected.nonempty h3⟩)

end CombinatorialRigidity.Molecular
