/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.CoverageCut
public import CombinatorialRigidity.Molecular.Induction.SparseDeficiency

/-!
# Counting the bodies of degree two, and the `4`-cycle of a chain

The deficiency counting that finds a core when no chain is usable (`thm:pencil-x0-theorem-s`), at
`d = 3`.

## Main results

* `Graph.IsX0Graph.exists_degree_eq_two_notMem` and
  `Graph.IsX0Graph.partitionDef_three_induce_diff_nonpos`: `lem:pencil-x0-sparse-count`, a sparse
  graph has at least four bodies of degree two, and if no two bodies of degree two are adjacent,
  then `s₆(V(G) \ {x}) ≤ 0` for every body `x` of degree two.
* `Graph.IsOpenEar.deficiency_three_induce_cycle`: the `4`-cycle of a chain with two interior
  bodies is rigid.
-/

@[expose] public section

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {α β : Type*} [Finite α] [Finite β]

/-! ## Counting bodies of degree two (`lem:pencil-x0-sparse-count`) -/

/-- The degree sum `2|E|` over `V(G)` is at least `3|V| − |D₂|`, `D₂` the bodies of degree two. -/
theorem _root_.Graph.IsX0Graph.three_mul_sub_le_two_mul_ncard {G : Graph α β}
    (hG : G.IsX0Graph) :
    3 * (V(G).ncard : ℤ) - ({v ∈ V(G) | G.degree v = 2} : Set α).ncard ≤ 2 * E(G).ncard := by
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

/-- **Counting bodies of degree two** (`lem:pencil-x0-sparse-count`(1)): if `G` satisfies the
standing hypotheses and is sparse, at least four bodies have degree two, so one of them lies outside
any set `s` of at most three bodies. Sparsity at `V(G)` gives `2|E(G)| ≤ 3|V(G)| − 4`, while
`3|V(G)| − |D₂| ≤ 2|E(G)|`, `D₂` the bodies of degree two
(`Graph.IsX0Graph.three_mul_sub_le_two_mul_ncard`). -/
theorem _root_.Graph.IsX0Graph.exists_degree_eq_two_notMem {G : Graph α β} (hG : G.IsX0Graph)
    (hSv : ∀ X ⊆ V(G), 2 ≤ X.ncard → 1 ≤ (G.induce X).partitionDef 2 id) {s : Set α}
    (hs : s.ncard ≤ 3) : ∃ v ∈ V(G), G.degree v = 2 ∧ v ∉ s := by
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
  set D : Set α := {v ∈ V(G) | G.degree v = 2}
  have hdisj : D.PairwiseDisjoint fun v => {e | G.IsNonloopAt e v} := by
    intro v hv w hw hvw
    refine Set.disjoint_left.2 fun e ⟨y, hyv, hy⟩ ⟨z, hzw, hz⟩ => ?_
    obtain rfl : v = z := (hy.left_eq_or_eq hz).resolve_left hvw
    have := hhubs v w hv.2 ⟨e, hz.symm⟩
    have := hw.2
    omega
  have hcard : ∀ v ∈ D, ({e | G.IsNonloopAt e v} : Set β).ncard = 2 := by
    intro v hv
    have h := Graph.degree_eq_ncard_add_ncard G v
    have hl : ({e | G.IsLoopAt e v} : Set β) = ∅ :=
      Set.eq_empty_of_forall_notMem fun e he => hG.simple.toLoopless.not_isLoopAt e v he
    rw [hl, Set.ncard_empty, hv.2] at h
    omega
  have hsub : (⋃ v ∈ D, {e | G.IsNonloopAt e v}) ⊆ E(G) := by
    simp only [Set.iUnion_subset_iff]
    exact fun v _ e he => he.edge_mem
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [(Set.toFinite D).ncard_biUnion (fun _ _ => Set.toFinite _) hdisj,
    finsum_mem_congr rfl hcard, finsum_mem_const, smul_eq_mul] at this
  omega

/-- **Counting bodies of degree two** (`lem:pencil-x0-sparse-count`(2)): let `G` satisfy the
standing hypotheses, with every neighbour of a body of degree two of degree at least three. Then
`s₆(V(G) \ {x}) ≤ 0` for every body `x` of degree two, the value at `d = 3` of the partition of
`G − x` into singletons. With `m` bodies of degree two, their `2m` links are distinct
(`Graph.IsX0Graph.two_mul_ncard_le_ncard_edgeSet`), while `2|E(G)| ≥ 2m + 3(|V(G)| − m)`. So
`5|E(G)| ≥ 6|V(G)|`, and as removing `x` removes one body and two links, `s₆(V(G) \ {x}) ≤ −2`. -/
theorem _root_.Graph.IsX0Graph.partitionDef_three_induce_diff_nonpos {G : Graph α β}
    (hG : G.IsX0Graph) (hhubs : ∀ v w, G.degree v = 2 → G.Adj v w → 3 ≤ G.degree w)
    {x : α} (hx : x ∈ V(G)) (hx2 : G.degree x = 2) :
    (G.induce (V(G) \ {x})).partitionDef 3 id ≤ 0 := by
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

/-! ## The `4`-cycle of a chain with two interior bodies -/

/-- The `4`-cycle of an open ear with two interior bodies and adjacent ends is rigid in a sparse
graph (a step of `thm:pencil-x0-theorem-s`): the set `{a, x 0, x 1, b}` of four bodies spans the
links `e 0`, `e 1`, `e 2` and `a − b`, so its singleton value is at most `1`, and it is tight, hence
rigid (`Graph.deficiency_three_induce_eq_zero_of_tight`, `lem:deficiency-tight-rigid`). -/
theorem _root_.Graph.IsOpenEar.deficiency_three_induce_cycle {G : Graph α β} {V₁ : Set α}
    {x : Fin 2 → α} {a b : α} {e : Fin 3 → β} (hear : G.IsOpenEar V₁ x a b e)
    (hadj : G.Adj a b) (hSv : ∀ X ⊆ V(G), 2 ≤ X.ncard → 1 ≤ (G.induce X).partitionDef 2 id) :
    ({a, x 0, x 1, b} : Set α) ⊆ V(G) ∧ 2 ≤ ({a, x 0, x 1, b} : Set α).ncard ∧
      (G.induce {a, x 0, x 1, b}).deficiency 3 = 0 := by
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

end CombinatorialRigidity.Molecular
