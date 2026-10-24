/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Mathlib.Data.Set.Card.Arithmetic
import CombinatorialRigidity.Molecular.Induction.Contraction

/-!
# The combinatorial induction: forest surgery at a vertex (KT Lemmas 4.1 and 4.2)

Results of the combinatorial induction (`sec:molecular-induction-forest`) after Katoh and Tanigawa
(2011, *A proof of the molecular conjecture*, Discrete Comput. Geom. **45**, §4.1, pp. 660–661). For
a vertex `v` of a multigraph `G`, vertices `a, b ≠ v`, the label `e₀ ∉ E(G)` of the new edge `ab` of
the splitting off `G_v^{ab}`, `D = bodyBarDim n`, `G̃ = (D - 1)·G` and `G_v = G - v`, it proves:

* that the edges of `G̃_v^{ab}` other than the copies `ẽ₀ = edgeFiber e₀ n` of `ab` are those of
  `(G_v)̃`, with the same ends, so that forests pass between `G̃`, `(G_v)̃` and `G̃_v^{ab}`;
* that a forest of `G̃` has at most one copy of an edge whose ends differ, and a forest of
  `G̃_v^{ab}` at most one copy of `ab` when `a ≠ b`;
* the changes that Katoh and Tanigawa make to one forest at `v`: in the proof of KT Lemma 4.1,
  removing its edges at `v` (`lem:reroute-vfree-transport`) and replacing its two edges at `v` by a
  copy of `ab` (`lem:reroute-cycle-lift`); in that of KT Lemma 4.2, replacing a copy of `ab` by two
  edges at `v` (`lem:reverse-reroute-cycle-lift`) and adding an edge at `v`
  (`lem:reverse-pendant-insert`);
* KT Lemma 4.2 (`lem:edge-splitting`, `lem:forest-surgery-unsplit`).

`Reduction.lean` performs the surgery of KT Lemma 4.1 on a base (`lem:forest-surgery-count`,
`lem:forest-surgery-split`).
-/

namespace Graph

open Set Matroid

variable {α β : Type*}

/-! ## Forests of `G̃`, `(G_v)̃` and `G̃_v^{ab}`

An edge of `G̃_v^{ab}` that is not a copy of the new edge `ab` is a copy of an edge of `G` whose
ends differ from `v`, with the same ends. So deleting the copies `ẽ₀ = edgeFiber e₀ n` of `ab` from
`G̃_v^{ab}` gives a subgraph of `G̃`, and when `e₀ ∉ E(G)`, `(G_v)̃` is a subgraph of `G̃_v^{ab}`
whose edges are those of `G̃_v^{ab}` outside `ẽ₀`. A forest of a graph is a forest of every graph of
which that graph is a subgraph. -/

/-- **`G̃_v^{ab}` without the copies of `ab` is a subgraph of `G̃`** (a step of
`lem:reroute-cycle-lift`, `lem:reverse-reroute-cycle-lift` and `lem:edge-splitting`): deleting the
copies `ẽ₀ = edgeFiber e₀ n` of the new edge from `G̃_v^{ab}` gives a subgraph of `G̃ = (D - 1)·G`.
Its vertices are those of `G` but `v`, and an edge of `G̃_v^{ab}` that is not a copy of `e₀` is a
copy of an edge of `G` whose ends differ from `v`, with the same ends (`splitOff_isLink`). The label
`e₀` may lie in `E(G)`. -/
lemma mulTilde_splitOff_deleteFiber_le {G : Graph α β} {v a b : α} {e₀ : β} (n : ℕ) :
    ((G.splitOff v a b e₀).mulTilde n).deleteEdges (edgeFiber e₀ n) ≤ G.mulTilde n := by
  refine ⟨?_, ?_⟩
  · -- Vertex sets: `V(G̃_v^{ab}) = V(G) \ {v} ⊆ V(G) = V(G̃)`.
    intro x hx
    simp only [vertexSet_deleteEdges] at hx
    exact Set.sdiff_subset hx
  · -- Links: a surviving link of `G̃_v^{ab}` (`p.1 ≠ e₀`) is a link of `G̃`.
    intro p x y hp
    simp only [deleteEdges_isLink, mulTilde_isLink, splitOff_isLink] at hp
    obtain ⟨hlink | hlink, hpfiber⟩ := hp
    · simpa only [mulTilde_isLink] using hlink.2.1
    · -- The `e₀`-fiber case is excluded: `p.1 = e₀` puts `p ∈ edgeFiber e₀ n`.
      exact absurd (show p ∈ edgeFiber e₀ n from hlink.1) hpfiber

/-- **`(G_v)̃` is a subgraph of `G̃_v^{ab}`** (a step of `lem:reroute-vfree-transport` and
`lem:reverse-reroute-cycle-lift`): when `e₀ ∉ E(G)`, the multiplied removal `(G_v)̃`, where
`G_v = G - v`, is a subgraph of `G̃_v^{ab}`. Both have the vertices of `G` but `v`, and an edge of
`(G_v)̃` is a copy of an edge of `G` whose ends differ from `v` (`removeVertex_isLink`). That edge
is not `e₀`, so `G_v^{ab}` keeps it, with the same ends. `removeVertex_le_splitOff` states the same
of `G_v` and `G_v^{ab}`. -/
lemma mulTilde_removeVertex_le_splitOff {G : Graph α β} {v a b : α} {e₀ : β} (n : ℕ)
    (he₀ : e₀ ∉ E(G)) :
    (G.removeVertex v).mulTilde n ≤ (G.splitOff v a b e₀).mulTilde n := by
  refine ⟨?_, ?_⟩
  · -- Vertex sets: both are `V(G) \ {v}` definitionally.
    intro x hx
    exact hx
  · -- Links: a link of `(G_v)̃` (a `v`-avoiding `G`-link) is a `splitOff` link (first disjunct).
    intro p x y hp
    simp only [mulTilde_isLink, removeVertex_isLink] at hp ⊢
    obtain ⟨hlink, hxv, hyv⟩ := hp
    rw [splitOff_isLink]
    refine Or.inl ⟨?_, hlink, hxv, hyv⟩
    -- `p.1 ≠ e₀`: `p.1 ∈ E(G)` (it carries the link `hlink`) but `e₀ ∉ E(G)`.
    rintro rfl; exact he₀ hlink.edge_mem

/-- **The edges of `G̃_v^{ab}` other than the copies of `ab` are those of `(G_v)̃`** (a step of
`lem:reverse-reroute-cycle-lift`, `lem:reverse-pendant-insert` and `lem:reduction-step`): when
`e₀ ∉ E(G)`, `E(G̃_v^{ab}) ∖ ẽ₀ = E((G_v)̃)`, where `ẽ₀ = edgeFiber e₀ n`. An edge of `G_v^{ab}`
other than `e₀` is an edge of `G` whose ends differ from `v`, so an edge of `G_v`; conversely, an
edge of `G_v` is an edge of `G`, so it is not `e₀`, and `G_v^{ab}` keeps it. `Reduction.lean` uses
it to compare the matroids of `G̃_v^{ab}` and of `(G_v)̃`. -/
lemma edgeSet_mulTilde_splitOff_diff_fiber {G : Graph α β} {v a b : α} {e₀ : β} (n : ℕ)
    (he₀ : e₀ ∉ E(G)) :
    E((G.splitOff v a b e₀).mulTilde n) \ edgeFiber e₀ n = E((G.removeVertex v).mulTilde n) := by
  ext p
  simp only [Set.mem_sdiff, mem_edgeFiber, mem_edgeSet_mulTilde,
    edgeSet_splitOff, Set.mem_union]
  rw [removeVertex, edgeSet_deleteVerts]
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨(⟨rfl, _⟩ | ⟨_, x, y, hl, hx, hy⟩), hpne⟩
    · exact absurd rfl hpne
    · exact ⟨x, y, hl, hx, hy⟩
  · rintro ⟨x, y, hl, hx, hy⟩
    refine ⟨Or.inr ⟨?_, x, y, hl, hx, hy⟩, ?_⟩
    · rintro rfl; exact he₀ hl.edge_mem
    · rintro rfl; exact he₀ hl.edge_mem

/-- **A forest of `(G_v)̃` is a forest of `G̃_v^{ab}`** (a step of `lem:reroute-vfree-transport`):
when `e₀ ∉ E(G)`, a set of edges independent in the cycle matroid of `(G_v)̃` is independent in that
of `G̃_v^{ab}`, as `(G_v)̃` is a subgraph of `G̃_v^{ab}` (`mulTilde_removeVertex_le_splitOff`). -/
lemma isAcyclicSet_mulTilde_splitOff_of_removeVertex {G : Graph α β} {v a b : α} {e₀ : β}
    {n : ℕ} (he₀ : e₀ ∉ E(G)) {F : Set (β × Fin (bodyHingeMult n))}
    (hF : ((G.removeVertex v).mulTilde n).cycleMatroid.Indep F) :
    ((G.splitOff v a b e₀).mulTilde n).cycleMatroid.Indep F := by
  rw [cycleMatroid_indep] at hF ⊢
  exact hF.mono (mulTilde_removeVertex_le_splitOff n he₀)

/-- **A forest of `G̃_v^{ab}` with no copy of `ab` is a forest of `G̃`** (a step of
`lem:reverse-pendant-insert` and `lem:edge-splitting`): a set `F` of edges independent in the cycle
matroid of `G̃_v^{ab}` and disjoint from the copies `ẽ₀ = edgeFiber e₀ n` of the new edge is
independent in that of `G̃`. It is a forest of `G̃_v^{ab}` with `ẽ₀` deleted, a subgraph of `G̃`
(`mulTilde_splitOff_deleteFiber_le`). In the proof of KT Lemma 4.2 it applies to the forests of a
partition of an independent set of `M(G̃_v^{ab})` that contain no copy of `ab`
(`splitOff_reroute_packing`, `isAcyclicSet_mulTilde_insert_vfiber_of_splitOff`). -/
lemma isAcyclicSet_mulTilde_of_splitOff_of_disjoint {G : Graph α β} {v a b : α} {e₀ : β}
    {n : ℕ} {F : Set (β × Fin (bodyHingeMult n))}
    (hF : ((G.splitOff v a b e₀).mulTilde n).cycleMatroid.Indep F)
    (hdisj : Disjoint F (edgeFiber e₀ n)) :
    (G.mulTilde n).cycleMatroid.Indep F := by
  rw [cycleMatroid_indep] at hF ⊢
  -- `F` is acyclic in `G̃_v^{ab}` and avoids the deleted fiber, hence acyclic in the
  -- deleted subgraph `G̃_v^{ab} ＼ ẽ₀`.
  have hFdel : (((G.splitOff v a b e₀).mulTilde n).deleteEdges (edgeFiber e₀ n)).IsAcyclicSet F :=
      by
    refine ⟨?_, fun C hC hCF ↦ ?_⟩
    · rw [edgeSet_deleteEdges]
      exact Set.subset_sdiff.mpr ⟨hF.1, hdisj⟩
    · -- A cyclic walk in the deleted subgraph is one in `G̃_v^{ab}`, contradicting `hF`.
      exact hF.2 C (hC.of_le (deleteEdges_le)) hCF
  -- Transport acyclicity up the subgraph `… ＼ ẽ₀ ≤ G̃`.
  exact hFdel.mono (mulTilde_splitOff_deleteFiber_le n)

/-! ## The edges of `G̃` at `v`

The edges of `G̃` incident with `v` (`fiberAtVertex`) are the copies of the edges of `G` at `v`.
Katoh and Tanigawa's proof of KT Lemma 4.1 (p. 660) changes each forest `F_i` of a partition at
these edges, according to their number `d_{F_i}(v)`; `forest_surgery_count` (`Reduction.lean`)
uses `fiberAtVertex`. -/

/-- **The edges of `G̃` at `v`**: the elements of `β × Fin (D - 1)` incident with `v` in
`G̃ = (D - 1)·G`, the copies of the edges of `G` at `v` (`mem_fiberAtVertex`). -/
def fiberAtVertex (G : Graph α β) (n : ℕ) (v : α) : Set (β × Fin (bodyHingeMult n)) :=
  {p | (G.mulTilde n).Inc p v}

/-- **Incidence in `G̃`**: a copy `p` of an edge of `G` is incident with `v` in `G̃` exactly when
the edge `p.1` is incident with `v` in `G` (`edgeMultiply_inc`). -/
lemma mulTilde_inc {G : Graph α β} {n : ℕ} {p : β × Fin (bodyHingeMult n)} {v : α} :
    (G.mulTilde n).Inc p v ↔ G.Inc p.1 v := by
  rw [mulTilde, edgeMultiply_inc]

@[simp]
lemma mem_fiberAtVertex {G : Graph α β} {n : ℕ} {v : α} {p : β × Fin (bodyHingeMult n)} :
    p ∈ G.fiberAtVertex n v ↔ G.Inc p.1 v := by
  rw [fiberAtVertex, Set.mem_ofPred_eq, mulTilde_inc]

/-- **Removing the edges at `v` from a forest** (`lem:reroute-vfree-transport`; KT Lemma 4.1,
p. 660): when `e₀ ∉ E(G)`, the edges of a forest `F` of `G̃` that are not incident with `v`,
`F ∖ fiberAtVertex v`, form a forest of `G̃_v^{ab}`. They are edges of `(G_v)̃`, a subgraph of `G̃`
(`edgeMultiply_mono`), and they contain no cycle there, as `F` contains none
(`IsAcyclicSet.anti_inter`). As `(G_v)̃` is a subgraph of `G̃_v^{ab}`, they form a forest of
`G̃_v^{ab}` (`isAcyclicSet_mulTilde_splitOff_of_removeVertex`). In the surgery, a forest with one
edge at `v` loses it (`forest_surgery_count`). -/
lemma isAcyclicSet_splitOff_of_diff_fiberAtVertex {G : Graph α β} {v a b : α} {e₀ : β}
    {n : ℕ} (he₀ : e₀ ∉ E(G)) {F : Set (β × Fin (bodyHingeMult n))}
    (hF : ((G.mulTilde n).cycleMatroid).Indep F) :
    ((G.splitOff v a b e₀).mulTilde n).cycleMatroid.Indep (F \ G.fiberAtVertex n v) := by
  rw [cycleMatroid_indep] at hF
  -- The `v`-free part lands in the ground set of the multiplied vertex-removal.
  have hsub : F \ G.fiberAtVertex n v ⊆ E((G.removeVertex v).mulTilde n) := by
    rintro p ⟨hpF, hpv⟩
    have hpE : p ∈ E(G.mulTilde n) := hF.1 hpF
    rw [mem_fiberAtVertex] at hpv
    rw [mem_edgeSet_mulTilde] at hpE
    obtain ⟨x, y, hl⟩ := exists_isLink_of_mem_edgeSet hpE
    rw [mem_edgeSet_mulTilde, removeVertex,
      edgeSet_deleteVerts, Set.mem_ofPred_eq]
    exact ⟨x, y, hl, fun hx ↦ hpv (hx ▸ hl.inc_left), fun hy ↦ hpv (hy ▸ hl.inc_right)⟩
  -- Acyclic in `(G_v)̃` (subset of the `G̃`-forest, restricted to the smaller ground set),
  -- then lift to `G̃_v^{ab}`.
  apply isAcyclicSet_mulTilde_splitOff_of_removeVertex he₀
  rw [cycleMatroid_indep]
  have hle : (G.removeVertex v).mulTilde n ≤ G.mulTilde n :=
    edgeMultiply_mono (by rw [removeVertex]; exact deleteVerts_le) _
  have hanti := hF.anti (Set.sdiff_subset (t := G.fiberAtVertex n v))
  have := hanti.anti_inter hle
  rwa [Set.inter_eq_self_of_subset_right hsub] at this

/-! ## A forest has at most one copy of an edge

Two copies of an edge whose ends differ form a cycle. So a forest of `G̃` has at most one copy of
such an edge, which the proof of `lem:forest-surgery-count` uses for `eₐ` and `e_b`, and when
`a ≠ b` a forest of `G̃_v^{ab}` has at most one copy of the new edge `ab`, which the proofs of
`lem:reverse-reroute-cycle-lift` and `lem:edge-splitting` use. -/

/-- **Two copies of `ab` form a cycle of `G̃_v^{ab}`** (a step of `lem:edge-splitting`): when
`a ≠ b` are vertices of `G` other than `v`, two distinct copies `p ≠ q` of the new edge `e₀` form a
cycle of `G̃_v^{ab}`. Both join `a` and `b` (`splitOff_isLink`), so `a —p→ b —q→ a` is a cyclic
walk. -/
lemma isCycleSet_pair_edgeFiber_splitOff {G : Graph α β} {v a b : α} {e₀ : β} {n : ℕ}
    (hab : a ≠ b) (ha : a ≠ v) (hb : b ≠ v) (haV : a ∈ V(G)) (hbV : b ∈ V(G))
    {p q : β × Fin (bodyHingeMult n)} (hp : p.1 = e₀) (hq : q.1 = e₀) (hpq : p ≠ q) :
    ((G.splitOff v a b e₀).mulTilde n).IsCycleSet {p, q} := by
  -- Both `p` and `q` are copies of `e₀`, hence links of `a, b` in `G̃_v^{ab}`.
  have hlink : ∀ r : β × Fin (bodyHingeMult n), r.1 = e₀ →
      ((G.splitOff v a b e₀).mulTilde n).IsLink r a b := by
    intro r hr
    rw [mulTilde_isLink, splitOff_isLink, hr]
    exact Or.inr ⟨rfl, ha, hb, haV, hbV, Or.inl ⟨rfl, rfl⟩⟩
  have hlinkp := hlink p hp
  have hlinkq := hlink q hq
  -- The length-2 closed walk `a —p→ b —q→ a`.
  refine ⟨WList.cons a p (WList.cons b q (WList.nil a)), ?_, by simp⟩
  have hwalk : ((G.splitOff v a b e₀).mulTilde n).IsWalk
      (WList.cons a p (WList.cons b q (WList.nil a))) := by
    rw [cons_isWalk_iff, cons_isWalk_iff, nil_isWalk_iff]
    exact ⟨hlinkp, hlinkq.symm, hlinkp.left_mem⟩
  refine ⟨⟨⟨hwalk, ?_⟩, by simp, ?_⟩, ?_⟩
  · -- Distinct edges `p ≠ q`.
    simp [hpq]
  · -- Closed: first vertex = last vertex.
    simp
  · -- No repeated vertices in the tail `[b, a]`: `a ≠ b`.
    simp [hab.symm]

/-- **A forest of `G̃_v^{ab}` has at most one copy of `ab`** (a step of
`lem:reverse-reroute-cycle-lift` and `lem:edge-splitting`): when `a ≠ b` are vertices of `G` other
than `v`, a set `F` of edges independent in the cycle matroid of `G̃_v^{ab}` meets the copies
`ẽ₀ = edgeFiber e₀ n` of the new edge in at most one element, as two of them form a cycle
(`isCycleSet_pair_edgeFiber_splitOff`). -/
lemma fiber_inter_subsingleton_of_isAcyclicSet_splitOff {G : Graph α β}
    {v a b : α} {e₀ : β} {n : ℕ} (hab : a ≠ b) (ha : a ≠ v) (hb : b ≠ v) (haV : a ∈ V(G))
    (hbV : b ∈ V(G)) {F : Set (β × Fin (bodyHingeMult n))}
    (hF : ((G.splitOff v a b e₀).mulTilde n).cycleMatroid.Indep F) :
    (F ∩ edgeFiber e₀ n).Subsingleton := by
  rw [cycleMatroid_indep] at hF
  intro p hp q hq
  by_contra hpq
  -- `p, q` are distinct copies of `e₀` in `F`, so `{p, q}` is a cycle of `G̃_v^{ab}`.
  obtain ⟨C, hCG, hC, hCpq⟩ := isCycleSet_iff.mp
    (isCycleSet_pair_edgeFiber_splitOff hab ha hb haV hbV hp.2 hq.2 hpq)
  -- A cycle with edge set `{p, q} ⊆ F` contradicts the acyclicity of `F`.
  refine (not_isAcyclicSet_iff hF.1).mpr ⟨C, hC, hCG, ?_⟩ hF
  rw [← hCpq]
  exact Set.insert_subset hp.1 (Set.singleton_subset_iff.mpr hq.1)

/-- **Two copies of an edge form a cycle of `G̃`** (a step of `lem:forest-surgery-count`): if `e`
joins distinct vertices `x ≠ y` of `G`, two distinct copies `p ≠ q` of `e` form a cycle of `G̃`,
`x —p→ y —q→ x`, as in `isCycleSet_pair_edgeFiber_splitOff`. -/
lemma isCycleSet_pair_edgeFiber_mulTilde {G : Graph α β} {n : ℕ} {e : β} {x y : α}
    (hxy : x ≠ y) (hl : G.IsLink e x y)
    {p q : β × Fin (bodyHingeMult n)} (hp : p.1 = e) (hq : q.1 = e) (hpq : p ≠ q) :
    (G.mulTilde n).IsCycleSet {p, q} := by
  have hlink : ∀ r : β × Fin (bodyHingeMult n), r.1 = e → (G.mulTilde n).IsLink r x y :=
    fun r hr ↦ by rw [mulTilde_isLink, hr]; exact hl
  have hlinkp := hlink p hp
  have hlinkq := hlink q hq
  refine ⟨WList.cons x p (WList.cons y q (WList.nil x)), ?_, by simp⟩
  have hwalk : (G.mulTilde n).IsWalk (WList.cons x p (WList.cons y q (WList.nil x))) := by
    rw [cons_isWalk_iff, cons_isWalk_iff, nil_isWalk_iff]
    exact ⟨hlinkp, hlinkq.symm, hlinkp.left_mem⟩
  refine ⟨⟨⟨hwalk, ?_⟩, by simp, ?_⟩, ?_⟩
  · simp [hpq]
  · simp
  · simp [hxy.symm]

/-- **A forest of `G̃` has at most one copy of an edge** (a step of `lem:forest-surgery-count`): if
`e` joins distinct vertices of `G`, a set `F` of edges independent in the cycle matroid of `G̃`
meets the copies `ẽ = edgeFiber e n` in at most one element (`isCycleSet_pair_edgeFiber_mulTilde`).
So a forest has at most one edge in `ẽₐ` and at most one in `ẽ_b`. -/
lemma fiber_inter_subsingleton_of_isAcyclicSet_mulTilde {G : Graph α β} {n : ℕ} {e : β}
    {x y : α} (hxy : x ≠ y) (hl : G.IsLink e x y) {F : Set (β × Fin (bodyHingeMult n))}
    (hF : (G.mulTilde n).cycleMatroid.Indep F) : (F ∩ edgeFiber e n).Subsingleton := by
  rw [cycleMatroid_indep] at hF
  intro p hp q hq
  by_contra hpq
  obtain ⟨C, hCG, hC, hCpq⟩ := isCycleSet_iff.mp
    (isCycleSet_pair_edgeFiber_mulTilde hxy hl hp.2 hq.2 hpq)
  refine (not_isAcyclicSet_iff hF.1).mpr ⟨C, hC, hCG, ?_⟩ hF
  rw [← hCpq]
  exact Set.insert_subset hp.1 (Set.singleton_subset_iff.mpr hq.1)

/-! ## Replacing the two edges at `v` by a copy of `ab` (`lem:reroute-cycle-lift`)

Katoh and Tanigawa's proof of KT Lemma 4.1 (p. 660) replaces the two edges `pa` and `pb` at `v` of a
forest `F` of `G̃` by a copy `r` of the new edge `ab`, and `(F ∖ {pa, pb}) ∪ {r}` is a forest of
`G̃_v^{ab}`. A cycle `C` of `G̃_v^{ab}` in that set gives a cycle of `G̃` in `F`. If `C` avoids `r`,
it is a cycle of `G̃_v^{ab}` without copies of `ab`, so a cycle of `G̃`
(`mulTilde_splitOff_deleteFiber_le`). Otherwise `C` passes through `r` once, and the rest of `C` is
a walk from `b` to `a` with edges in `F ∖ {pa, pb}` (`exists_directedWalk_of_isCyclicWalk_isLink`).
With `pa` and `pb` it closes into a closed trail of `G̃` with edges in `F`, which contains a cycle
(`IsTour.exists_isCyclicWalk`). -/

/-- **A cycle through an edge gives a walk between its ends** (a step of `lem:reroute-cycle-lift`
and `lem:reverse-reroute-cycle-lift`): if a cyclic walk `C` of `H` contains an edge `e` that joins
`s` and `t`, there is a walk `w` of `H` from `t` to `s` whose edges are distinct edges of `C` other
than `e`. It is `C`, rotated to begin with `e` (`WList.exists_rotate_firstEdge_eq`), without `e`,
and reversed when `C` traverses `e` from `t` to `s`. -/
private lemma exists_directedWalk_of_isCyclicWalk_isLink {γ : Type*} {H : Graph α γ}
    {C : WList α γ} {e : γ} {s t : α}
    (hC : H.IsCyclicWalk C) (heC : e ∈ C.edgeSet) (hlink : H.IsLink e s t) :
    ∃ w : WList α γ, H.IsWalk w ∧ w.first = t ∧ w.last = s ∧
      w.edgeSet ⊆ C.edgeSet ∧ w.edge.Nodup ∧ e ∉ w.edge := by
  obtain ⟨m, -, hne, hfe⟩ := WList.exists_rotate_firstEdge_eq (w := C) (e := e) heC
  have hDcyc : H.IsCyclicWalk (C.rotate m) := hC.rotate m
  have hDE : (C.rotate m).edgeSet = C.edgeSet := WList.rotate_edgeSet C m
  obtain ⟨x, e', w', heq⟩ := WList.nonempty_iff_exists_cons.mp (hne.rotate m)
  have hee' : e' = e := by simp only [heq, WList.Nonempty.firstEdge_cons] at hfe; exact hfe
  subst e'
  rw [heq] at hDcyc hDE
  -- `cons x e w'` is closed, so `x = w'.last`.
  have hclosed : (WList.cons x e w').IsClosed := hDcyc.isClosed
  rw [WList.cons_isClosed_iff] at hclosed
  -- The first link: `e` joins `x` and `w'.first`; matched against `IsLink e s t`.
  have hwalk : H.IsWalk (WList.cons x e w') := hDcyc.isWalk
  rw [cons_isWalk_iff] at hwalk
  obtain ⟨hfirstlink, hw'walk⟩ := hwalk
  have hxw' : (s = x ∧ t = w'.first) ∨ (s = w'.first ∧ t = x) :=
    hlink.eq_and_eq_or_eq_and_eq hfirstlink
  -- `e` is used once, so `e ∉ E(w')`.
  have hnodup : (WList.cons x e w').edge.Nodup := hDcyc.edge_nodup
  rw [WList.cons_edge, List.nodup_cons] at hnodup
  obtain ⟨henw', hw'nodup⟩ := hnodup
  have hw'sub : w'.edgeSet ⊆ C.edgeSet := by
    rw [← hDE, WList.cons_edgeSet]; exact Set.subset_insert _ _
  -- Reorient `w'` (reverse it in the flipped case) to run from `t` to `s`.
  rcases hxw' with ⟨hsx, htw'⟩ | ⟨hsw', htx⟩
  · exact ⟨w', hw'walk, htw'.symm, (hsx.trans hclosed).symm, hw'sub, hw'nodup, henw'⟩
  · refine ⟨w'.reverse, hw'walk.reverse, ?_, ?_, ?_, ?_, ?_⟩
    · rw [WList.reverse_first]; exact (htx.trans hclosed).symm
    · rw [WList.reverse_last]; exact hsw'.symm
    · rw [WList.reverse_edgeSet]; exact hw'sub
    · rw [WList.reverse_edge]; exact List.nodup_reverse.mpr hw'nodup
    · rw [WList.reverse_edge]; simpa using henw'

/-- **Replacing the two edges at `v` of a forest by a copy of `ab`** (`lem:reroute-cycle-lift`; KT
Lemma 4.1, p. 660): let `a, b ≠ v` be vertices of `G`, let `e₀ ∉ E(G)`, and let `F` be a forest of
`G̃` that contains `pa`, which joins `v` and `a`, and `pb ≠ pa`, which joins `v` and `b`, as its
only edges incident with `v`. Then for a copy `r` of `e₀`, `(F ∖ {pa, pb}) ∪ {r}` is a forest of
`G̃_v^{ab}`, by the argument of the section. Neither the degree of `v` nor `a ≠ b` is assumed. -/
lemma isAcyclicSet_splitOff_reroute {G : Graph α β} {v a b : α} {e₀ : β} {n : ℕ}
    (ha : a ≠ v) (hb : b ≠ v) (haV : a ∈ V(G)) (hbV : b ∈ V(G))
    {F : Set (β × Fin (bodyHingeMult n))} {pa pb r : β × Fin (bodyHingeMult n)}
    (hF : ((G.mulTilde n).cycleMatroid).Indep F)
    (hpa : (G.mulTilde n).IsLink pa v a) (hpb : (G.mulTilde n).IsLink pb v b)
    (hpaF : pa ∈ F) (hpbF : pb ∈ F) (hpab : pa ≠ pb)
    (hFv : ∀ p ∈ F, (G.mulTilde n).Inc p v → p = pa ∨ p = pb)
    (hr : r.1 = e₀) (he₀ : e₀ ∉ E(G)) :
    ((G.splitOff v a b e₀).mulTilde n).cycleMatroid.Indep (insert r (F \ {pa, pb})) := by
  classical
  -- Abbreviations: the original `K = G̃` and the splitting-off `Ksp = G̃_v^{ab}`.
  set K := G.mulTilde n with hK
  set Ksp := (G.splitOff v a b e₀).mulTilde n with hKsp
  rw [cycleMatroid_indep] at hF
  -- The rerouted set lies in the ground set of `Ksp`.
  have hpaE : pa.1 ∈ E(G) := by
    rw [hK, mulTilde_isLink] at hpa; exact hpa.edge_mem
  have hpbE : pb.1 ∈ E(G) := by
    rw [hK, mulTilde_isLink] at hpb; exact hpb.edge_mem
  -- `pa, pb` are not copies of `e₀`.
  have hpane₀ : pa.1 ≠ e₀ := fun h ↦ he₀ (h ▸ hpaE)
  have hpbne₀ : pb.1 ≠ e₀ := fun h ↦ he₀ (h ▸ hpbE)
  have hrE : r ∈ E(Ksp) := by
    rw [hKsp, mem_edgeSet_mulTilde, edgeSet_splitOff]
    exact Or.inl ⟨hr, ha, hb, haV, hbV⟩
  have hdiffsub : F \ {pa, pb} ⊆ E(Ksp) := by
    rintro p ⟨hpF, hp2⟩
    rw [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hp2
    have hpE : p ∈ E(K) := hF.1 hpF
    have hpv : ¬ K.Inc p v := fun hinc ↦ (hFv p hpF hinc).elim hp2.1 hp2.2
    -- `p` is a `v`-avoiding `G`-edge copy distinct from `e₀`, kept by `splitOff`.
    rw [hK, mem_edgeSet_mulTilde] at hpE
    obtain ⟨x, y, hl⟩ := exists_isLink_of_mem_edgeSet hpE
    have hxv : x ≠ v := fun hx ↦ hpv (hx ▸ (by
      rw [hK, mulTilde, edgeMultiply_inc]; exact hl.inc_left))
    have hyv : y ≠ v := fun hy ↦ hpv (hy ▸ (by
      rw [hK, mulTilde, edgeMultiply_inc]; exact hl.inc_right))
    have hpne₀ : p.1 ≠ e₀ := fun h ↦ he₀ (h ▸ hpE)
    rw [hKsp, mem_edgeSet_mulTilde, edgeSet_splitOff]
    exact Or.inr ⟨hpne₀, x, y, hl, hxv, hyv⟩
  set S := insert r (F \ {pa, pb}) with hS
  have hSE : S ⊆ E(Ksp) := Set.insert_subset hrE hdiffsub
  rw [cycleMatroid_indep, isAcyclicSet_iff]
  refine ⟨hSE, ?_⟩
  rw [restrict_isForest_iff']
  intro C hCS hCcyc
  -- The cycle's edges avoid `pa, pb` (they are kept off `S`).
  have hCnpa : pa ∉ C.edgeSet := fun h ↦ (Set.mem_of_mem_of_subset h hCS).elim
    (fun he ↦ hpane₀ (by rw [he, hr]))
    (fun ⟨_, hne⟩ ↦ hne (Or.inl rfl))
  have hCnpb : pb ∉ C.edgeSet := fun h ↦ (Set.mem_of_mem_of_subset h hCS).elim
    (fun he ↦ hpbne₀ (by rw [he, hr]))
    (fun ⟨_, hne⟩ ↦ hne (Or.inr rfl))
  by_cases hrC : r ∈ C.edgeSet
  · -- `C` uses the copy `r` of `ab`: substitute the 2-path through `v`.
    -- `r` joins `a, b` in `Ksp`; rotate + reorient `C` to a walk `w` running `b → a` off `r`.
    have hrlink : Ksp.IsLink r a b := by
      rw [hKsp, mulTilde_isLink, splitOff_isLink]
      exact Or.inr ⟨hr, ha, hb, haV, hbV, Or.inl ⟨rfl, rfl⟩⟩
    obtain ⟨w, hw_walk, hw_first, hw_last, hw_sub, hw_nodup, hr_nw⟩ :=
      exists_directedWalk_of_isCyclicWalk_isLink hCcyc hrC hrlink
    -- `w`'s edges are the non-`r` edges of `C`, hence lie in `F ∖ {pa, pb}`.
    have hw_edge : ∀ p ∈ w.edge, p ∈ F \ {pa, pb} := by
      intro p hp
      have hpS : p ∈ S := hCS (hw_sub (WList.mem_edgeSet_iff.mpr hp))
      exact (Set.mem_insert_iff.mp hpS).resolve_left (fun h ↦ hr_nw (h ▸ hp))
    -- `w` has no copy of `e₀`, hence lifts to a `K = G̃`-walk.
    have hw_fresh : Disjoint w.edgeSet (edgeFiber e₀ n) := by
      rw [Set.disjoint_left]; intro p hp hpf
      have hp1 : p.1 = e₀ := hpf
      have hpEK : p ∈ E(K) := hF.1 (hw_edge p hp).1
      rw [hK, mem_edgeSet_mulTilde] at hpEK
      exact he₀ (hp1 ▸ hpEK)
    have hw_K : K.IsWalk w :=
      (isWalk_deleteEdges_iff.mpr ⟨hw_walk, hw_fresh⟩).of_le
        (mulTilde_splitOff_deleteFiber_le n)
    -- Substitute `a —pa— v —pb— b(=w.first) ⋯ a(=w.last)`: build the `K`-tour, extract a cycle.
    have hkey : ∃ T : WList α (β × Fin (bodyHingeMult n)), K.IsTour T ∧ T.edgeSet ⊆ F := by
      refine ⟨WList.cons a pa (WList.cons v pb w), ?_, ?_⟩
      · refine ⟨⟨?_, ?_⟩, by simp, ?_⟩
        · rw [cons_isWalk_iff, cons_isWalk_iff]
          exact ⟨hpa.symm, hw_first ▸ hpb, hw_K⟩
        · simp only [WList.cons_edge, List.nodup_cons, List.mem_cons]
          refine ⟨?_, ?_, hw_nodup⟩
          · rintro (h | h)
            · exact hpab h
            · exact (hw_edge pa h).2 (by simp)
          · exact fun h ↦ (hw_edge pb h).2 (by simp)
        · -- closed: first `a` = last `(cons v pb w).last = w.last = a`.
          rw [WList.cons_isClosed_iff, WList.last_cons]; exact hw_last.symm
      · intro p hp
        simp only [WList.cons_edgeSet, Set.mem_insert_iff] at hp
        rcases hp with rfl | rfl | hp
        · exact hpaF
        · exact hpbF
        · exact (hw_edge p hp).1
    -- A `K`-tour contains a `K`-cycle whose edges are a sublist, hence inside `F`.
    obtain ⟨T, hT, hTF⟩ := hkey
    obtain ⟨C', hC', hsub⟩ := hT.exists_isCyclicWalk
    exact hF.2 C' hC' (hsub.edge_subset.trans hTF)
  · -- `C` avoids `r`, so its edges lie in `F ∖ {pa, pb}` and are not copies of `e₀`;
    -- `C` is then a cycle of `K = G̃` inside `F`, contradicting `hF`.
    have hCF : C.edgeSet ⊆ F := by
      intro p hp
      rcases Set.mem_of_mem_of_subset hp hCS with hpr | hpd
      · exact absurd (hpr ▸ hp) hrC
      · exact hpd.1
    have hCnofresh : Disjoint C.edgeSet (edgeFiber e₀ n) := by
      rw [Set.disjoint_left]
      intro p hp hpf
      have hpe₀ : p.1 = e₀ := hpf
      rcases Set.mem_of_mem_of_subset hp hCS with hpr | hpd
      · exact hrC (hpr ▸ hp)
      · have hpEK : p ∈ E(K) := hF.1 hpd.1
        rw [hK, mem_edgeSet_mulTilde] at hpEK
        exact he₀ (hpe₀ ▸ hpEK)
    -- Lift `C` to a cyclic walk of `K = G̃` inside `F`, contradicting `F` acyclic.
    have hCK : K.IsCyclicWalk C :=
      ((deleteEdges_isCyclicWalk_iff _ _).mpr ⟨hCcyc, hCnofresh⟩).of_le
        (mulTilde_splitOff_deleteFiber_le n)
    exact hF.2 C hCK hCF

/-! ## Replacing a copy of `ab` by the two edges at `v` (`lem:reverse-reroute-cycle-lift`)

Katoh and Tanigawa's proof of KT Lemma 4.2 (pp. 660–661) reverses the change: a forest `F'` of
`G̃_v^{ab}` that contains a copy `r` of `ab` loses `r` and gains a copy `pa` of the edge joining `v`
and `a` and a copy `pb` of the edge joining `v` and `b`. As `F'` has at most one copy of `ab`
(`fiber_inter_subsingleton_of_isAcyclicSet_splitOff`), the edges of `F' ∖ {r}` are edges of `(G_v)̃`
(`edgeSet_mulTilde_splitOff_diff_fiber`), none of them incident with `v`. So a cycle `C` of `G̃`
with edges in `(F' ∖ {r}) ∪ {pa, pb}` uses both `pa` and `pb`, or neither. If neither, `C` is a
cycle of `(G_v)̃`, so of `G̃_v^{ab}`, with edges in `F'`. If both, the rest of `C` is a walk from
`a` to `b` with edges in `F' ∖ {r}`, and with `r` it closes into a closed trail of `G̃_v^{ab}` with
edges in `F'`, which contains a cycle. Both are impossible. -/

/-- **Replacing a copy of `ab` in a forest by the two edges at `v`**
(`lem:reverse-reroute-cycle-lift`; KT Lemma 4.2, pp. 660–661): let `a ≠ b` be vertices of `G` other
than `v`, let `e₀ ∉ E(G)`, let `F'` be a forest of `G̃_v^{ab}` that contains a copy `r` of `e₀`, and
let `pa` and `pb` be edges of `G̃` that join `v` to `a` and to `b`. Then `(F' ∖ {r}) ∪ {pa, pb}` is
a forest of `G̃`, by the argument of the section. The degree of `v` is not assumed. -/
lemma isAcyclicSet_mulTilde_of_splitOff_reroute {G : Graph α β} {v a b : α} {e₀ : β} {n : ℕ}
    (hab : a ≠ b) (ha : a ≠ v) (hb : b ≠ v) (haV : a ∈ V(G)) (hbV : b ∈ V(G))
    {F' : Set (β × Fin (bodyHingeMult n))} {pa pb r : β × Fin (bodyHingeMult n)}
    (hF' : ((G.splitOff v a b e₀).mulTilde n).cycleMatroid.Indep F')
    (hpa : (G.mulTilde n).IsLink pa v a) (hpb : (G.mulTilde n).IsLink pb v b)
    (hr : r.1 = e₀) (hrF' : r ∈ F') (he₀ : e₀ ∉ E(G)) :
    (G.mulTilde n).cycleMatroid.Indep (insert pa (insert pb (F' \ {r}))) := by
  classical
  -- Abbreviations: the original `K = G̃` and the splitting-off `Ksp = G̃_v^{ab}`.
  set K := G.mulTilde n with hK
  set Ksp := (G.splitOff v a b e₀).mulTilde n with hKsp
  rw [cycleMatroid_indep] at hF'
  -- `pa, pb` are not copies of `e₀` (their edges of `G` lie in `E(G)`, but `e₀` does not).
  have hpaE : pa.1 ∈ E(G) := by rw [hK, mulTilde_isLink] at hpa; exact hpa.edge_mem
  have hpbE : pb.1 ∈ E(G) := by rw [hK, mulTilde_isLink] at hpb; exact hpb.edge_mem
  have hpane₀ : pa.1 ≠ e₀ := fun h ↦ he₀ (h ▸ hpaE)
  have hpbne₀ : pb.1 ≠ e₀ := fun h ↦ he₀ (h ▸ hpbE)
  -- `pa, pb ∈ E(K)`.
  have hpaEK : pa ∈ E(K) := hpa.edge_mem
  have hpbEK : pb ∈ E(K) := hpb.edge_mem
  -- The core `F' ∖ {r}` has no copy of `e₀` (`F'` has at most one), so it lies in `E((G_v)̃)`.
  have hsubsing : (F' ∩ edgeFiber e₀ n).Subsingleton :=
    fiber_inter_subsingleton_of_isAcyclicSet_splitOff hab ha hb haV hbV
      (by rw [cycleMatroid_indep]; exact hF')
  have hdiffdisj : Disjoint (F' \ {r}) (edgeFiber e₀ n) := by
    rw [Set.disjoint_left]
    rintro p ⟨hpF', hpr⟩ hpf
    have hrf : r ∈ F' ∩ edgeFiber e₀ n := ⟨hrF', by rw [mem_edgeFiber]; exact hr⟩
    have hpinter : p ∈ F' ∩ edgeFiber e₀ n := ⟨hpF', hpf⟩
    exact hpr (Set.mem_singleton_iff.mpr (hsubsing hpinter hrf))
  have hdiffGv : (F' \ {r}) ⊆ E((G.removeVertex v).mulTilde n) := by
    rw [← edgeSet_mulTilde_splitOff_diff_fiber n he₀]
    exact Set.subset_sdiff.mpr ⟨fun p hp ↦ hF'.1 hp.1, hdiffdisj⟩
  -- The swapped set lies in `E(K)`.
  have hSE : insert pa (insert pb (F' \ {r})) ⊆ E(K) := by
    refine Set.insert_subset hpaEK (Set.insert_subset hpbEK ?_)
    intro p hp
    exact (mulTilde_splitOff_deleteFiber_le n).edgeSet_mono
      (Set.mem_sdiff_of_mem (hF'.1 hp.1) (Set.disjoint_left.mp hdiffdisj hp))
  -- The core fibers avoid `v` (they live in `(G_v)̃`, which omits `v`).
  have hvnotinc : ∀ p ∈ F' \ {r}, ¬ K.Inc p v := by
    intro p hp hinc
    have hpE : p ∈ E((G.removeVertex v).mulTilde n) := hdiffGv hp
    rw [hK, mulTilde_inc] at hinc
    rw [mem_edgeSet_mulTilde] at hpE
    obtain ⟨x, y, hl⟩ := exists_isLink_of_mem_edgeSet hpE
    rw [removeVertex_isLink] at hl
    obtain ⟨hlink, hxv, hyv⟩ := hl
    rcases hinc with ⟨w, hw⟩
    rcases hlink.eq_and_eq_or_eq_and_eq hw with ⟨hxw, -⟩ | ⟨-, hyw⟩
    · exact hxv hxw
    · exact hyv hyw
  set S := insert pa (insert pb (F' \ {r})) with hS
  -- The only `v`-incident edges of `S` are `pa, pb`.
  have hSv : ∀ p ∈ S, K.Inc p v → p = pa ∨ p = pb := by
    intro p hp hinc
    rcases Set.mem_insert_iff.mp hp with h | h
    · exact Or.inl h
    · rcases Set.mem_insert_iff.mp h with h | h
      · exact Or.inr h
      · exact absurd hinc (hvnotinc p h)
  rw [cycleMatroid_indep, isAcyclicSet_iff]
  refine ⟨hSE, ?_⟩
  rw [restrict_isForest_iff']
  intro C hCS hCcyc
  -- Edges of `C` other than `pa, pb` lie in `F' ∖ {r}`.
  have hCedge : ∀ p ∈ C.edgeSet, p = pa ∨ p = pb ∨ p ∈ F' \ {r} := by
    intro p hp
    rcases Set.mem_insert_iff.mp (Set.mem_of_mem_of_subset hp hCS) with h | h
    · exact Or.inl h
    · rcases Set.mem_insert_iff.mp h with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  by_cases hpaC : pa ∈ C.edgeSet
  · -- `C` uses `pa`: it must also use `pb` (a cycle through `v` uses both `v`-edges).
    -- Rotate + reorient `C` to a walk `wab` running `a → v` off `pa` (`hpa : IsLink pa v a`).
    obtain ⟨wab, hwab_walk, hwab_first, hwab_last, hwab_sub, hwab_nodup, hpa_nwab⟩ :=
      exists_directedWalk_of_isCyclicWalk_isLink hCcyc hpaC hpa
    -- `wab` is nonempty (`a ≠ v`), so its last edge `qpb := wab.lastEdge` exists.
    have hwab_ne : wab.Nonempty := by
      by_contra hnil
      rw [WList.not_nonempty_iff] at hnil
      exact ha (hwab_first ▸ hwab_last ▸ hnil.first_eq_last)
    set qpb := hwab_ne.lastEdge with hqpb
    -- `qpb` is the last edge, incident to `wab.last = v`, and lies in `S`.
    have hqpb_mem : qpb ∈ wab.edge := hwab_ne.lastEdge_mem
    have hqpb_S : qpb ∈ S := hCS (hwab_sub (WList.mem_edgeSet_iff.mpr hqpb_mem))
    -- Decompose `wab = w₂.concat qpb v` with `w₂ = wab.dropLast` running `a → b`.
    set w₂ := wab.dropLast with hw₂
    have hwab_eq : w₂.concat qpb v = wab := by
      rw [hw₂, hqpb, ← hwab_last]; exact hwab_ne.concat_dropLast
    have hw₂_first : w₂.first = a := by rw [hw₂, WList.dropLast_first]; exact hwab_first
    -- The last link of `wab`: `qpb` joins `w₂.last` and `v`.
    have hconcat_walk : K.IsWalk (w₂.concat qpb v) := hwab_eq ▸ hwab_walk
    rw [concat_isWalk_iff] at hconcat_walk
    obtain ⟨hw₂_walk, hqpb_link⟩ := hconcat_walk
    have hqpb_inc : K.Inc qpb v := hqpb_link.symm.inc_left
    -- `qpb` is `v`-incident, so `qpb = pa ∨ qpb = pb`; it is `≠ pa` (`pa ∉ wab.edge`), so `= pb`.
    have hqpb_eq : qpb = pb :=
      (hSv qpb hqpb_S hqpb_inc).resolve_left (fun h ↦ hpa_nwab (h ▸ hqpb_mem))
    -- `w₂.last = b`: `qpb = pb` links `v, b` and `w₂.last, v`.
    have hw₂_last : w₂.last = b := by
      have := hqpb_eq ▸ hqpb_link
      rcases hpb.eq_and_eq_or_eq_and_eq this with ⟨hvw, hbv⟩ | ⟨hvv, hbw⟩
      · exact absurd hbv hb
      · exact hbw.symm
    -- `wab.edge = w₂.edge ++ [qpb]`, so `qpb ∉ w₂.edge` and `w₂.edge` is nodup.
    have hwab_edge_eq : wab.edge = w₂.edge ++ [qpb] := by
      rw [← hwab_eq, WList.concat_edge]
    rw [hwab_edge_eq, List.nodup_append] at hwab_nodup
    have hqpb_nw₂ : qpb ∉ w₂.edge :=
      fun h ↦ hwab_nodup.2.2 qpb h qpb (List.mem_singleton.mpr rfl) rfl
    have hw₂_nodup : w₂.edge.Nodup := hwab_nodup.1
    have hw₂_sub_wab : ∀ p ∈ w₂.edge, p ∈ wab.edge := fun p hp ↦ by
      rw [hwab_edge_eq]; exact List.mem_append_left _ hp
    -- `w₂`'s edges lie in `F' ∖ {r}` (they avoid `pa` and `pb`).
    have hw₂_edge_core : ∀ p ∈ w₂.edge, p ∈ F' \ {r} := by
      intro p hp
      have hpC : p ∈ C.edgeSet := hwab_sub (WList.mem_edgeSet_iff.mpr (hw₂_sub_wab p hp))
      have hpne_pa : p ≠ pa := fun h ↦ hpa_nwab (h ▸ hw₂_sub_wab p hp)
      have hpne_pb : p ≠ pb := fun h ↦ hqpb_nw₂ (hqpb_eq ▸ h ▸ hp)
      rcases hCedge p hpC with h | h | h
      · exact absurd h hpne_pa
      · exact absurd h hpne_pb
      · exact h
    -- The core edges lie in `E((G_v)̃)` and `E(F')` (subset of `F'`).
    have hw₂_edgeSet_Gv : w₂.edgeSet ⊆ E((G.removeVertex v).mulTilde n) := fun p hp ↦
      hdiffGv (hw₂_edge_core p (WList.mem_edgeSet_iff.mp hp))
    have hw₂_edge_F' : ∀ p ∈ w₂.edge, p ∈ F' := fun p hp ↦ (hw₂_edge_core p hp).1
    -- `w₂` is a walk of `(G_v)̃`, hence of `Ksp`.
    have hw₂_ne : w₂.Nonempty := by
      by_contra hnil
      rw [WList.not_nonempty_iff] at hnil
      exact hab (hw₂_first ▸ hw₂_last ▸ hnil.first_eq_last)
    have hle_Gv_K : (G.removeVertex v).mulTilde n ≤ K :=
      hK ▸ edgeMultiply_mono (removeVertex_le G v) _
    have hw₂_Gv : ((G.removeVertex v).mulTilde n).IsWalk w₂ :=
      hw₂_walk.isWalk_le_of_nonempty hle_Gv_K
        (by intro p hp; exact hw₂_edgeSet_Gv hp) hw₂_ne
    have hw₂_Ksp : Ksp.IsWalk w₂ := hw₂_Gv.of_le (mulTilde_removeVertex_le_splitOff n he₀)
    -- The copy `r` of `ab` joins `a, b` in `Ksp`.
    have hrlink : Ksp.IsLink r a b := by
      rw [hKsp, mulTilde_isLink, splitOff_isLink]
      exact Or.inr ⟨hr, ha, hb, haV, hbV, Or.inl ⟨rfl, rfl⟩⟩
    -- `r ∉ w₂.edge` (it is a copy of `e₀`, which the core avoids).
    have hr_nw₂ : r ∉ w₂.edge := fun h ↦ (hw₂_edge_core r h).2 rfl
    -- Build the closed `Ksp`-trail `T = w₂.concat r a`: `a → ⋯ → b —r— a`.
    set T := w₂.concat r a with hT
    have hT_walk : Ksp.IsWalk T := by
      rw [hT, concat_isWalk_iff]; exact ⟨hw₂_Ksp, hw₂_last ▸ hrlink.symm⟩
    have hT_tour : Ksp.IsTour T := by
      refine ⟨⟨hT_walk, ?_⟩, ?_, ?_⟩
      · rw [hT, WList.concat_edge, List.nodup_append]
        exact ⟨hw₂_nodup, List.nodup_singleton _,
          fun p hp q hq hpq ↦ hr_nw₂ (List.mem_singleton.mp hq ▸ hpq ▸ hp)⟩
      · rw [hT]; exact (WList.concat_nonempty w₂ r a)
      · rw [hT, WList.concat_isClosed_iff]; exact hw₂_first.symm
    have hT_edge_F' : T.edgeSet ⊆ F' := by
      rw [hT, WList.concat_edgeSet]
      exact Set.insert_subset hrF' (fun p hp ↦ hw₂_edge_F' p (WList.mem_edgeSet_iff.mp hp))
    -- A `Ksp`-tour contains a `Ksp`-cycle whose edges sit inside `F'`, contradicting `hF'`.
    obtain ⟨C', hC', hsub⟩ := hT_tour.exists_isCyclicWalk
    exact hF'.2 C' hC' (hsub.edge_subset.trans hT_edge_F')
  · -- `C` avoids `pa`. Then it also avoids `pb`, else it would use a single `v`-edge.
    have hpbC : pb ∉ C.edgeSet := by
      intro hpbC
      -- Rotate + reorient `C` to a walk `wba` running `b → v` off `pb` (`hpb : IsLink pb v b`).
      obtain ⟨wba, hwba_walk, hwba_first, hwba_last, hwba_sub, hwba_nodup, hpb_nwba⟩ :=
        exists_directedWalk_of_isCyclicWalk_isLink hCcyc hpbC hpb
      -- `wba` is nonempty (`b ≠ v`); its last edge `qpa` is `v`-incident, distinct from `pb`.
      have hwba_ne : wba.Nonempty := by
        by_contra hnil
        rw [WList.not_nonempty_iff] at hnil
        exact hb (hwba_first ▸ hwba_last ▸ hnil.first_eq_last)
      set qpa := hwba_ne.lastEdge with hqpa
      have hqpa_mem : qpa ∈ wba.edge := hwba_ne.lastEdge_mem
      have hqpa_C : qpa ∈ C.edgeSet := hwba_sub (WList.mem_edgeSet_iff.mpr hqpa_mem)
      -- Decompose `wba = (wba.dropLast).concat qpa v`; the last link makes `qpa` `v`-incident.
      have hwba_eq : wba.dropLast.concat qpa v = wba := by
        rw [hqpa, ← hwba_last]; exact hwba_ne.concat_dropLast
      have hconcat_walk : K.IsWalk (wba.dropLast.concat qpa v) := by rw [hwba_eq]; exact hwba_walk
      rw [concat_isWalk_iff] at hconcat_walk
      have hqpa_inc : K.Inc qpa v := hconcat_walk.2.symm.inc_left
      -- `qpa = pa ∨ qpa = pb`; it is `≠ pb` (nodup), so `qpa = pa ∈ C` — contradiction.
      have hqpa_ne_pb : qpa ≠ pb := fun h ↦ hpb_nwba (h ▸ hqpa_mem)
      have hqpa_eq : qpa = pa :=
        (hSv qpa (hCS hqpa_C) hqpa_inc).resolve_right hqpa_ne_pb
      exact hpaC (hqpa_eq ▸ hqpa_C)
    -- Both `v`-edges absent: `C` lives in `F' ∖ {r} ⊆ E((G_v)̃) ⊆ E(Ksp)`, lift the cycle.
    have hCcore : ∀ p ∈ C.edgeSet, p ∈ F' \ {r} := by
      intro p hp
      rcases hCedge p hp with h | h | h
      · exact absurd (h ▸ hp) hpaC
      · exact absurd (h ▸ hp) hpbC
      · exact h
    have hCGv : C.edgeSet ⊆ E((G.removeVertex v).mulTilde n) := fun p hp ↦ hdiffGv (hCcore p hp)
    -- `C` is a tour of `(G_v)̃`, hence a cyclic walk of `Ksp` inside `F'`.
    have hC_Gv_tour : ((G.removeVertex v).mulTilde n).IsTour C :=
      hCcyc.isTour.of_le_of_subset (hK ▸ edgeMultiply_mono (removeVertex_le G v) _)
        (fun p hp ↦ hCGv hp)
    have hC_Ksp_cyc : Ksp.IsCyclicWalk C :=
      ⟨hC_Gv_tour.of_le (mulTilde_removeVertex_le_splitOff n he₀), hCcyc.nodup⟩
    exact hF'.2 C hC_Ksp_cyc (fun p hp ↦ (hCcore p hp).1)

/-- **Adding an edge at `v` to a forest with no copy of `ab`** (`lem:reverse-pendant-insert`; KT
Lemma 4.2, pp. 660–661): when `e₀ ∉ E(G)`, let `F` be a forest of `G̃_v^{ab}` disjoint from the
copies `ẽ₀ = edgeFiber e₀ n` of the new edge, and let `x` be an edge of `G̃` that joins `v` to a
vertex `w ≠ v`. Then `insert x F` is a forest of `G̃`. The set `F` is a forest of `G̃`
(`isAcyclicSet_mulTilde_of_splitOff_of_disjoint`) whose edges are edges of `(G_v)̃`
(`edgeSet_mulTilde_splitOff_diff_fiber`), so none of them is incident with `v`, and
`acyclicSet_insert_vfiber_of_not_inc` (`lem:acyclic-insert-vfiber`) adds `x` to it. -/
lemma isAcyclicSet_mulTilde_insert_vfiber_of_splitOff {G : Graph α β} {v a b : α} {e₀ : β}
    {n : ℕ} (he₀ : e₀ ∉ E(G)) {F : Set (β × Fin (bodyHingeMult n))}
    {x : β × Fin (bodyHingeMult n)} {w : α}
    (hF : ((G.splitOff v a b e₀).mulTilde n).cycleMatroid.Indep F)
    (hdisj : Disjoint F (edgeFiber e₀ n)) (hxvw : (G.mulTilde n).IsLink x v w) (hwv : w ≠ v) :
    (G.mulTilde n).cycleMatroid.Indep (insert x F) := by
  -- Transport `F` down to `G̃`; it lives in `(G_v)̃`, so it avoids `v`.
  have hFK : (G.mulTilde n).cycleMatroid.Indep F :=
    isAcyclicSet_mulTilde_of_splitOff_of_disjoint hF hdisj
  have hFGv : F ⊆ E((G.removeVertex v).mulTilde n) := by
    rw [← edgeSet_mulTilde_splitOff_diff_fiber n he₀]
    rw [cycleMatroid_indep] at hF
    exact Set.subset_sdiff.mpr ⟨hF.1, hdisj⟩
  have hFv : ∀ p ∈ F, ¬ (G.mulTilde n).Inc p v := by
    intro p hp hinc
    have hpE : p ∈ E((G.removeVertex v).mulTilde n) := hFGv hp
    rw [mulTilde_inc] at hinc
    rw [mem_edgeSet_mulTilde] at hpE
    obtain ⟨y, z, hl⟩ := exists_isLink_of_mem_edgeSet hpE
    rw [removeVertex_isLink] at hl
    obtain ⟨hlink, hyv, hzv⟩ := hl
    obtain ⟨t, ht⟩ := hinc
    rcases hlink.eq_and_eq_or_eq_and_eq ht with ⟨hyw, -⟩ | ⟨-, hzw⟩
    · exact hyv hyw
    · exact hzv hzw
  exact acyclicSet_insert_vfiber_of_not_inc hFK hxvw hwv hFv

/-! ## KT Lemma 4.2 (`lem:edge-splitting`)

KT Lemma 4.2 (pp. 660–661) is the converse of KT Lemma 4.1 for edge-splitting: an independent set
`I'` of `M(G̃_v^{ab})` extends to an independent set `I` of `M(G̃)`. The construction
(`splitOff_reroute_packing`) partitions `I'` into `D` pairwise disjoint forests of `G̃_v^{ab}`
(`matroidMG_indep_iff_exists_forest_packing`, made disjoint by `disjointed`). A forest that contains
the copy `(e₀, j)` of `ab` trades it for `(eₐ, j)` and `(e_b, j)`
(`isAcyclicSet_mulTilde_of_splitOff_reroute`). If `I'` contains the `D - 1` copies of `ab` (KT
Lemma 4.2(ii)), the one other forest is a forest of `G̃` as it is
(`isAcyclicSet_mulTilde_of_splitOff_of_disjoint`), and `|I| + 1 = |I'| + D`. If it contains
`h' < D - 1` of them (KT Lemma 4.2(i)), each forest with no copy of `ab` but one gains a copy
`(eₐ, j)` with `(e₀, j) ∉ I'`, and the last one a copy `(e_b, j)` with `(e₀, j) ∉ I'`
(`isAcyclicSet_mulTilde_insert_vfiber_of_splitOff`), so `|I| = |I'| + D`, and `I` has `h' + 1`
copies of `e_b`. In both cases `I ∖ (ẽₐ ∪ ẽ_b) = I' ∖ ẽ₀`, an equation that `lem:edge-splitting`
adds to Katoh and Tanigawa's statement, as their proof of KT Lemma 4.3 relies on it (p. 661).
`Reduction.lean` uses the lemma for KT Lemmas 4.3(ii), 4.4 and 4.8(ii)
(`lem:splitoff-kdof-criterion`, `lem:removal-deficiency-equality`, `lem:reduction-step-pos`). -/

/-- **The construction of KT Lemma 4.2** (a step of `lem:edge-splitting`; Katoh–Tanigawa 2011,
pp. 660–661): let `D ≥ 2`, let the edges `eₐ ≠ e_b` join `v` to `a ≠ b`, both other than `v`, let
`e₀ ∉ E(G)`, and let `I'` be independent in `M(G̃_v^{ab})`. Then `M(G̃)` has an independent set `I`
with `I ∖ (ẽₐ ∪ ẽ_b) = I' ∖ ẽ₀`, such that `|I| + 1 = |I'| + D` if `I'` has `D - 1` copies of `ab`,
and `|I| = |I'| + D`, with `h' + 1` copies of `e_b` in `I`, if it has `h' < D - 1`. The construction
is the section's. Both cases share the partition of `I'` and the final count, and each pin of
`lem:edge-splitting` takes one of them. -/
private theorem splitOff_reroute_packing [DecidableEq β] [Finite β]
    {G : Graph α β} {n : ℕ} (hD : 2 ≤ bodyBarDim n) {v a b : α} {eₐ e_b e₀ : β}
    (hab : a ≠ b) (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b)
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b) (he₀ : e₀ ∉ E(G))
    {I' : Set (β × Fin (bodyHingeMult n))}
    (hI' : ((G.splitOff v a b e₀).matroidMG n).Indep I') :
    ∃ I, (G.matroidMG n).Indep I ∧
      I \ (edgeFiber eₐ n ∪ edgeFiber e_b n) = I' \ edgeFiber e₀ n ∧
      ((I' ∩ edgeFiber e₀ n).ncard = bodyHingeMult n →
        I.ncard + 1 = I'.ncard + bodyBarDim n) ∧
      ((I' ∩ edgeFiber e₀ n).ncard < bodyHingeMult n →
        I.ncard = I'.ncard + bodyBarDim n ∧
        (I ∩ edgeFiber e_b n).ncard = (I' ∩ edgeFiber e₀ n).ncard + 1) := by
  classical
  have : Nonempty (Fin (bodyBarDim n)) := ⟨⟨0, lt_of_lt_of_le (by norm_num) hD⟩⟩
  have haV : a ∈ V(G) := hla.right_mem
  have hbV : b ∈ V(G) := hlb.right_mem
  have heane₀ : eₐ ≠ e₀ := fun h ↦ he₀ (h ▸ hla.edge_mem)
  have hebne₀ : e_b ≠ e₀ := fun h ↦ he₀ (h ▸ hlb.edge_mem)
  -- Make a forest packing of `I'` pairwise disjoint.
  obtain ⟨hI'E, Fs₀, hcover₀, hindep₀⟩ :=
    (matroidMG_indep_iff_exists_forest_packing (G.splitOff v a b e₀) n).mp hI'
  set Ds := disjointed Fs₀ with hDs
  have hDscover : ⋃ i, Ds i = I' := by rw [hDs, iUnion_disjointed]; exact hcover₀
  have hDsindep : ∀ i, ((G.splitOff v a b e₀).mulTilde n).cycleMatroid.Indep (Ds i) :=
    fun i ↦ (hindep₀ i).subset (disjointed_le Fs₀ i)
  have hDsdisj : Pairwise (Function.onFun Disjoint Ds) := disjoint_disjointed Fs₀
  have hsubsing : ∀ i, (Ds i ∩ edgeFiber e₀ n).Subsingleton := fun i ↦
    fiber_inter_subsingleton_of_isAcyclicSet_splitOff hab hav hbv haV hbV (hDsindep i)
  set S : Finset (Fin (bodyBarDim n)) :=
    {i | (Ds i ∩ edgeFiber e₀ n).Nonempty} with hS
  have hSiff : ∀ i, i ∈ S ↔ (Ds i ∩ edgeFiber e₀ n).Nonempty := by
    intro i; simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
  have : Nonempty (β × Fin (bodyHingeMult n)) := by
    obtain ⟨p, hp⟩ : (edgeFiber e₀ n).Nonempty := by
      rw [← Set.ncard_pos (Set.toFinite _), edgeFiber_ncard, bodyHingeMult]; omega
    exact ⟨p⟩
  set rOf : Fin (bodyBarDim n) → β × Fin (bodyHingeMult n) := fun i =>
    if h : (Ds i ∩ edgeFiber e₀ n).Nonempty then h.choose else Classical.arbitrary _ with hrOf
  have hrOf_mem : ∀ i ∈ S, rOf i ∈ Ds i ∩ edgeFiber e₀ n := by
    intro i hi
    have hne := (hSiff i).mp hi
    simp only [hrOf, dite_eq_left hne]; exact hne.choose_spec
  have hrOf1 : ∀ i ∈ S, (rOf i).1 = e₀ := fun i hi ↦ by
    have := (hrOf_mem i hi).2; rwa [mem_edgeFiber] at this
  set h' : ℕ := (I' ∩ edgeFiber e₀ n).ncard with hh'
  have hfibpart : ⋃ i, Ds i ∩ edgeFiber e₀ n = I' ∩ edgeFiber e₀ n := by
    rw [← Set.iUnion_inter, hDscover]
  have hScard : S.card = h' := by
    have hdisj_fib : Pairwise (Function.onFun Disjoint (fun i ↦ Ds i ∩ edgeFiber e₀ n)) :=
      fun i j hij ↦ (hDsdisj hij).mono Set.inter_subset_left Set.inter_subset_left
    have hsum : ∑ i, (Ds i ∩ edgeFiber e₀ n).ncard = h' := by
      have hkey := Set.ncard_iUnion_of_fintype (s := fun i ↦ Ds i ∩ edgeFiber e₀ n)
        (fun i ↦ Set.toFinite _) hdisj_fib
      rw [hfibpart] at hkey
      exact hkey.symm
    have hterm : ∀ i, (Ds i ∩ edgeFiber e₀ n).ncard = if i ∈ S then 1 else 0 := by
      intro i
      by_cases hi : i ∈ S
      · rw [ite_eq_left hi]
        exact (Set.ncard_le_one_iff_subsingleton.mpr (hsubsing i)).antisymm
          (Set.Nonempty.ncard_pos (Set.toFinite _) ((hSiff i).mp hi))
      · have hemp : Ds i ∩ edgeFiber e₀ n = ∅ :=
          Set.not_nonempty_iff_eq_empty.mp (by rw [← hSiff i]; exact hi)
        rw [ite_eq_right hi, hemp, Set.ncard_empty]
    simp only [hterm, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul,
      mul_one] at hsum
    exact hsum
  set paOf : Fin (bodyBarDim n) → β × Fin (bodyHingeMult n) := fun i => (eₐ, (rOf i).2) with hpaOf
  set pbOf : Fin (bodyBarDim n) → β × Fin (bodyHingeMult n) := fun i => (e_b, (rOf i).2) with hpbOf
  have hpaℓ : ∀ i, (G.mulTilde n).IsLink (paOf i) v a := fun i ↦ by
    rw [mulTilde_isLink, hpaOf]; exact hla
  have hpbℓ : ∀ i, (G.mulTilde n).IsLink (pbOf i) v b := fun i ↦ by
    rw [mulTilde_isLink, hpbOf]; exact hlb
  have hrOf_ne : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → rOf i ≠ rOf j := by
    intro i hi j hj hij heq
    exact Set.disjoint_left.mp (hDsdisj hij) (hrOf_mem i hi).1 (heq ▸ (hrOf_mem j hj).1)
  have hrOf2_ne : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (rOf i).2 ≠ (rOf j).2 := by
    intro i hi j hj hij h2
    exact hrOf_ne i hi j hj hij (Prod.ext ((hrOf1 i hi).trans (hrOf1 j hj).symm) h2)
  have hnotin_of_vlink : ∀ {e w}, e ≠ e₀ → G.IsLink e v w → e ∉ E(G.splitOff v a b e₀) := by
    intro e w hne hl
    rw [edgeSet_splitOff]; rintro (⟨h, _⟩ | ⟨_, x, y, hl', hx, hy⟩)
    · exact hne h
    · rcases hl.eq_and_eq_or_eq_and_eq hl' with ⟨hvx, -⟩ | ⟨hvy, -⟩
      · exact hx hvx.symm
      · exact hy hvy.symm
  have hea_notin : eₐ ∉ E(G.splitOff v a b e₀) := hnotin_of_vlink heane₀ hla
  have heb_notin : e_b ∉ E(G.splitOff v a b e₀) := hnotin_of_vlink hebne₀ hlb
  have hDssubE : ∀ i, Ds i ⊆ E((G.splitOff v a b e₀).mulTilde n) :=
    fun i ↦ (hDsindep i).subset_ground
  have hDs_fst : ∀ k p, p ∈ Ds k → p.1 ≠ eₐ ∧ p.1 ≠ e_b := by
    intro k p hp
    have hpE := hDssubE k hp
    rw [mem_edgeSet_mulTilde] at hpE
    exact ⟨fun h ↦ hea_notin (h ▸ hpE), fun h ↦ heb_notin (h ▸ hpE)⟩
  have hpaOf_fst : ∀ k, (paOf k).1 = eₐ := fun k ↦ by rw [hpaOf]
  have hpbOf_fst : ∀ k, (pbOf k).1 = e_b := fun k ↦ by rw [hpbOf]
  have hpa_notDs : ∀ i j, paOf i ∉ Ds j := fun i j hp ↦ (hDs_fst j _ hp).1 (by rw [hpaOf])
  have hpb_notDs : ∀ i j, pbOf i ∉ Ds j := fun i j hp ↦ (hDs_fst j _ hp).2 (by rw [hpbOf])
  have hpa_ne_pb : ∀ i, paOf i ≠ pbOf i := fun i h ↦ heab (by
    have := (Prod.ext_iff.mp h).1; rwa [hpaOf, hpbOf] at this)
  have hDs_disj_fib : ∀ i ∉ S, Disjoint (Ds i) (edgeFiber e₀ n) := by
    intro i hi
    rw [Set.disjoint_left]
    intro p hpD hpf
    exact ((hSiff i).not.mp hi) ⟨p, hpD, hpf⟩
  have hbHM : bodyHingeMult n = bodyBarDim n - 1 := by rw [bodyHingeMult]
  have hh'le : h' ≤ bodyHingeMult n := by
    rw [hh']
    calc (I' ∩ edgeFiber e₀ n).ncard
        ≤ (edgeFiber e₀ n).ncard :=
          Set.ncard_le_ncard Set.inter_subset_right (Set.toFinite _)
      _ = bodyHingeMult n := edgeFiber_ncard e₀ n
  -- Shared finish: from any per-forest family `Fs` refining the cores `Ds` with the interface
  -- below, assemble `M(G̃)`-independence, the survivor conjunct, and the packing count.
  have hfinish : ∀ (Fs : Fin (bodyBarDim n) → Set (β × Fin (bodyHingeMult n)))
      (g : Fin (bodyBarDim n) → ℕ),
      (∀ i, (G.mulTilde n).cycleMatroid.Indep (Fs i)) →
      Pairwise (Function.onFun Disjoint Fs) →
      (∀ i, (Fs i).ncard = (Ds i).ncard + g i) →
      (∀ i p, p ∈ Fs i → p.1 ≠ eₐ → p.1 ≠ e_b → p ∈ Ds i) →
      (∀ i p, p ∈ Ds i → p.1 ≠ e₀ → p ∈ Fs i) →
      (∀ i ∈ S, rOf i ∉ Fs i) →
      (G.matroidMG n).Indep (⋃ i, Fs i) ∧
        (⋃ i, Fs i) \ (edgeFiber eₐ n ∪ edgeFiber e_b n) = I' \ edgeFiber e₀ n ∧
        (⋃ i, Fs i).ncard = I'.ncard + ∑ i, g i := by
    intro Fs g hindep' hdisj' hshrink hcore_of_ne hDscore hrOf_notin
    refine ⟨?_, ?_, ?_⟩
    · rw [matroidMG_indep_iff_exists_forest_packing]
      exact ⟨Set.iUnion_subset fun i ↦ (hindep' i).subset_ground, Fs, rfl, hindep'⟩
    · rw [← hDscover]
      apply Set.Subset.antisymm
      · rintro p ⟨hpU, hpab⟩
        rw [Set.mem_union, not_or] at hpab
        obtain ⟨hpa, hpb⟩ := hpab
        simp only [mem_edgeFiber] at hpa hpb
        rw [Set.mem_iUnion] at hpU
        obtain ⟨i, hpi⟩ := hpU
        by_cases hp0 : p.1 = e₀
        · exfalso
          have hpD : p ∈ Ds i := hcore_of_ne i p hpi hpa hpb
          have hpf : p ∈ edgeFiber e₀ n := by rw [mem_edgeFiber]; exact hp0
          have hiS : i ∈ S := (hSiff i).mpr ⟨p, hpD, hpf⟩
          have hpeqr : p = rOf i := hsubsing i ⟨hpD, hpf⟩ (hrOf_mem i hiS)
          exact hrOf_notin i hiS (hpeqr ▸ hpi)
        · refine ⟨Set.mem_iUnion.mpr ⟨i, hcore_of_ne i p hpi hpa hpb⟩, ?_⟩
          rw [mem_edgeFiber]; exact hp0
      · rintro p ⟨hpU, hp0⟩
        rw [mem_edgeFiber] at hp0
        rw [Set.mem_iUnion] at hpU
        obtain ⟨i, hpi⟩ := hpU
        obtain ⟨hpa, hpb⟩ := hDs_fst i p hpi
        refine ⟨Set.mem_iUnion.mpr ⟨i, hDscore i p hpi hp0⟩, ?_⟩
        simp only [Set.mem_union, not_or, mem_edgeFiber]
        exact ⟨hpa, hpb⟩
    · have hsumFs : ∑ i, (Fs i).ncard = (⋃ i, Fs i).ncard :=
        (Set.ncard_iUnion_of_fintype (fun i ↦ Set.toFinite _) hdisj').symm
      have hsumDs : ∑ i, (Ds i).ncard = I'.ncard := by
        rw [← Set.ncard_iUnion_of_fintype (fun i ↦ Set.toFinite _) hDsdisj, hDscover]
      rw [← hsumFs, Finset.sum_congr rfl (fun i _ ↦ hshrink i), Finset.sum_add_distrib, hsumDs]
  by_cases hfull : h' = bodyHingeMult n
  · -- Full-fiber arm (`h' = D − 1`): reroute every `S`-forest, no pendants.
    set Fs : Fin (bodyBarDim n) → Set (β × Fin (bodyHingeMult n)) := fun i =>
      if i ∈ S then insert (paOf i) (insert (pbOf i) (Ds i \ {rOf i})) else Ds i with hFs
    have hindep' : ∀ i, (G.mulTilde n).cycleMatroid.Indep (Fs i) := by
      intro i
      simp only [hFs]
      by_cases hi : i ∈ S
      · rw [ite_eq_left hi]
        exact isAcyclicSet_mulTilde_of_splitOff_reroute hab hav hbv haV hbV (hDsindep i)
          (hpaℓ i) (hpbℓ i) (hrOf1 i hi) (hrOf_mem i hi).1 he₀
      · rw [ite_eq_right hi]
        exact isAcyclicSet_mulTilde_of_splitOff_of_disjoint (hDsindep i) (hDs_disj_fib i hi)
    have hFsmem : ∀ k p, p ∈ Fs k →
        (k ∈ S ∧ p = paOf k) ∨ (k ∈ S ∧ p = pbOf k) ∨ p ∈ Ds k := by
      intro k p hp
      simp only [hFs] at hp
      by_cases hk : k ∈ S
      · rw [ite_eq_left hk] at hp
        rcases Set.mem_insert_iff.mp hp with rfl | hp'
        · exact Or.inl ⟨hk, rfl⟩
        rcases Set.mem_insert_iff.mp hp' with rfl | hp''
        · exact Or.inr (Or.inl ⟨hk, rfl⟩)
        · exact Or.inr (Or.inr hp''.1)
      · rw [ite_eq_right hk] at hp; exact Or.inr (Or.inr hp)
    have hcore_of_ne : ∀ i p, p ∈ Fs i → p.1 ≠ eₐ → p.1 ≠ e_b → p ∈ Ds i := by
      intro i p hp hpa hpb
      rcases hFsmem i p hp with ⟨_, rfl⟩ | ⟨_, rfl⟩ | hc
      · exact absurd (hpaOf_fst i) hpa
      · exact absurd (hpbOf_fst i) hpb
      · exact hc
    have hDscore : ∀ i p, p ∈ Ds i → p.1 ≠ e₀ → p ∈ Fs i := by
      intro i p hpi hp0
      simp only [hFs]
      by_cases hi : i ∈ S
      · rw [ite_eq_left hi]
        refine Set.mem_insert_iff.mpr (Or.inr (Set.mem_insert_iff.mpr (Or.inr ⟨hpi, ?_⟩)))
        rw [Set.mem_singleton_iff]
        intro h; exact hp0 (h ▸ hrOf1 i hi)
      · rw [ite_eq_right hi]; exact hpi
    have hrOf_notin : ∀ i ∈ S, rOf i ∉ Fs i := by
      intro i hiS hmem
      simp only [hFs, ite_eq_left hiS] at hmem
      rcases Set.mem_insert_iff.mp hmem with hpa' | hmem'
      · exact heane₀ (((hrOf1 i hiS).symm.trans (congrArg Prod.fst hpa')).trans (hpaOf_fst i)).symm
      rcases Set.mem_insert_iff.mp hmem' with hpb' | hmem''
      · exact hebne₀ (((hrOf1 i hiS).symm.trans (congrArg Prod.fst hpb')).trans (hpbOf_fst i)).symm
      · exact hmem''.2 rfl
    have hdisj' : Pairwise (Function.onFun Disjoint Fs) := by
      intro i j hij
      simp only [Function.onFun, Set.disjoint_left]
      intro p hpi hpj
      rcases hFsmem i p hpi with ⟨hiS, hpeqi⟩ | ⟨hiS, hpeqi⟩ | hpci <;>
        rcases hFsmem j p hpj with ⟨hjS, hpeqj⟩ | ⟨hjS, hpeqj⟩ | hpcj
      · exact hrOf2_ne i hiS j hjS hij (by
          have := (Prod.ext_iff.mp (hpeqi.symm.trans hpeqj)).2; simpa only [hpaOf] using this)
      · exact heab ((hpaOf_fst i) ▸ (hpbOf_fst j) ▸ hpeqi ▸ hpeqj ▸ rfl)
      · exact (hDs_fst j p hpcj).1 (hpeqi ▸ hpaOf_fst i)
      · exact heab ((hpaOf_fst j) ▸ (hpbOf_fst i) ▸ hpeqj ▸ hpeqi ▸ rfl)
      · exact hrOf2_ne i hiS j hjS hij (by
          have := (Prod.ext_iff.mp (hpeqi.symm.trans hpeqj)).2; simpa only [hpbOf] using this)
      · exact (hDs_fst j p hpcj).2 (hpeqi ▸ hpbOf_fst i)
      · exact (hDs_fst i p hpci).1 (hpeqj ▸ hpaOf_fst j)
      · exact (hDs_fst i p hpci).2 (hpeqj ▸ hpbOf_fst j)
      · exact Set.disjoint_left.mp (hDsdisj hij) hpci hpcj
    have hshrink : ∀ i, (Fs i).ncard = (Ds i).ncard + (if i ∈ S then 1 else 0) := by
      intro i
      by_cases hi : i ∈ S
      · simp only [hFs, ite_eq_left hi]
        have hpaD : paOf i ∉ insert (pbOf i) (Ds i \ {rOf i}) := by
          rw [Set.mem_insert_iff, not_or]
          exact ⟨hpa_ne_pb i, fun h ↦ hpa_notDs i i h.1⟩
        have hpbD : pbOf i ∉ Ds i \ {rOf i} := fun h ↦ hpb_notDs i i h.1
        rw [Set.ncard_insert_of_notMem hpaD (Set.toFinite _),
          Set.ncard_insert_of_notMem hpbD (Set.toFinite _),
          Set.ncard_sdiff_singleton_of_mem (hrOf_mem i hi).1]
        have hpos : 0 < (Ds i).ncard :=
          Set.Nonempty.ncard_pos (Set.toFinite _) ⟨rOf i, (hrOf_mem i hi).1⟩
        omega
      · simp only [hFs, ite_eq_right hi, add_zero]
    obtain ⟨hindU, hsurv, hcountsum⟩ := hfinish Fs (fun i => if i ∈ S then 1 else 0)
      hindep' hdisj' hshrink hcore_of_ne hDscore hrOf_notin
    simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul,
      mul_one] at hcountsum
    refine ⟨⋃ i, Fs i, hindU, hsurv, ?_, ?_⟩
    · intro _
      rw [hcountsum]; omega
    · intro hcon
      exact absurd hcon (by omega)
  · -- Partial-fiber arm (`h' < D − 1`): reroute the `S`-forests and pendant the copy-free ones.
    have hh'lt : h' < bodyHingeMult n := lt_of_le_of_ne hh'le hfull
    set Simg : Finset (Fin (bodyHingeMult n)) := S.image (fun i ↦ (rOf i).2) with hSimg
    have hSimg_card : Simg.card = h' := by
      rw [hSimg, Finset.card_image_of_injOn, hScard]
      intro i hi j hj h2
      by_contra hij
      exact hrOf2_ne i hi j hj hij h2
    set U : Finset (Fin (bodyHingeMult n)) := Finset.univ \ Simg with hU
    have hUcard : U.card = bodyHingeMult n - h' := by
      rw [hU, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
        hSimg_card]
    have hUpos : 0 < U.card := by rw [hUcard]; omega
    have hUne : U.Nonempty := Finset.card_pos.mp hUpos
    set T : Finset (Fin (bodyBarDim n)) := Sᶜ with hT
    have hTcard : T.card = bodyBarDim n - h' := by
      rw [hT, Finset.card_compl, Fintype.card_fin, hScard]
    have hTpos : 0 < T.card := by rw [hTcard]; rw [hbHM] at hh'lt; omega
    have hTne : T.Nonempty := Finset.card_pos.mp hTpos
    set i_b : Fin (bodyBarDim n) := T.min' hTne with hi_b
    have hi_bT : i_b ∈ T := T.min'_mem hTne
    have hi_bnotS : i_b ∉ S := by
      have := hi_bT; rwa [hT, Finset.mem_compl] at this
    set Ta : Finset (Fin (bodyBarDim n)) := T.erase i_b with hTa
    have hTaUcard : Ta.card = U.card := by
      rw [hTa, Finset.card_erase_of_mem hi_bT, hTcard, hUcard, hbHM]; omega
    set eTa : Fin Ta.card ≃o ↥Ta := Ta.orderIsoOfFin rfl with heTa
    set eU : Fin Ta.card ≃o ↥U := U.orderIsoOfFin hTaUcard.symm with heU
    set pcEquiv : ↥Ta ≃ ↥U := eTa.symm.trans eU |>.toEquiv with hpcEquiv
    set pc : Fin (bodyBarDim n) → Fin (bodyHingeMult n) := fun i =>
      if h : i ∈ Ta then ↑(pcEquiv ⟨i, h⟩) else U.min' hUne with hpc
    set cb : Fin (bodyHingeMult n) := U.min' hUne with hcb
    have hcbU : cb ∈ U := U.min'_mem hUne
    have hpcU : ∀ i ∈ Ta, pc i ∈ U := by
      intro i hi; simp only [hpc, dite_eq_left hi]; exact (pcEquiv ⟨i, hi⟩).2
    have hpc_inj : ∀ i ∈ Ta, ∀ j ∈ Ta, pc i = pc j → i = j := by
      intro i hi j hj heq
      simp only [hpc, dite_eq_left hi, dite_eq_left hj] at heq
      have : pcEquiv ⟨i, hi⟩ = pcEquiv ⟨j, hj⟩ := Subtype.ext heq
      have := pcEquiv.injective this
      exact congrArg Subtype.val this
    have hU_notSimg : ∀ {c}, c ∈ U → c ∉ Simg := by
      intro c hc; rw [hU, Finset.mem_sdiff] at hc; exact hc.2
    set qaOf : Fin (bodyBarDim n) → β × Fin (bodyHingeMult n) := fun i => (eₐ, pc i) with hqaOf
    set qb : β × Fin (bodyHingeMult n) := (e_b, cb) with hqb
    have hqaℓ : ∀ i, (G.mulTilde n).IsLink (qaOf i) v a := fun i ↦ by
      rw [mulTilde_isLink, hqaOf]; exact hla
    have hqbℓ : (G.mulTilde n).IsLink qb v b := by rw [mulTilde_isLink, hqb]; exact hlb
    set Fs : Fin (bodyBarDim n) → Set (β × Fin (bodyHingeMult n)) := fun i =>
      if i ∈ S then insert (paOf i) (insert (pbOf i) (Ds i \ {rOf i}))
      else if i ∈ Ta then insert (qaOf i) (Ds i)
      else insert qb (Ds i) with hFs
    have hqa_notDs : ∀ i j, qaOf i ∉ Ds j := fun i j hp ↦ (hDs_fst j _ hp).1 (by rw [hqaOf])
    have hqb_notDs : ∀ j, qb ∉ Ds j := fun j hp ↦ (hDs_fst j _ hp).2 (by rw [hqb])
    have hindep' : ∀ i, (G.mulTilde n).cycleMatroid.Indep (Fs i) := by
      intro i
      simp only [hFs]
      by_cases hi : i ∈ S
      · rw [ite_eq_left hi]
        exact isAcyclicSet_mulTilde_of_splitOff_reroute hab hav hbv haV hbV (hDsindep i)
          (hpaℓ i) (hpbℓ i) (hrOf1 i hi) (hrOf_mem i hi).1 he₀
      · rw [ite_eq_right hi]
        by_cases hia : i ∈ Ta
        · rw [ite_eq_left hia]
          exact isAcyclicSet_mulTilde_insert_vfiber_of_splitOff he₀ (hDsindep i)
            (hDs_disj_fib i hi) (hqaℓ i) hav
        · rw [ite_eq_right hia]
          exact isAcyclicSet_mulTilde_insert_vfiber_of_splitOff he₀ (hDsindep i)
            (hDs_disj_fib i hi) hqbℓ hbv
    have hqaOf_fst : ∀ k, (qaOf k).1 = eₐ := fun k ↦ by rw [hqaOf]
    have hqb_fst : qb.1 = e_b := by rw [hqb]
    have hnotSnotTa : ∀ {i}, i ∉ S → i ∉ Ta → i = i_b := by
      intro i hiS hiTa
      by_contra hne
      exact hiTa (Finset.mem_erase.mpr ⟨hne, (hT ▸ Finset.mem_compl.mpr hiS)⟩)
    have hFsmem : ∀ k p, p ∈ Fs k →
        (k ∈ S ∧ p = paOf k) ∨ (k ∈ S ∧ p = pbOf k) ∨ (k ∈ Ta ∧ p = qaOf k) ∨
          (k = i_b ∧ p = qb) ∨ p ∈ Ds k := by
      intro k p hp
      simp only [hFs] at hp
      by_cases hk : k ∈ S
      · rw [ite_eq_left hk] at hp
        rcases Set.mem_insert_iff.mp hp with rfl | hp'
        · exact Or.inl ⟨hk, rfl⟩
        rcases Set.mem_insert_iff.mp hp' with rfl | hp''
        · exact Or.inr (Or.inl ⟨hk, rfl⟩)
        · exact Or.inr (Or.inr (Or.inr (Or.inr hp''.1)))
      · rw [ite_eq_right hk] at hp
        by_cases hka : k ∈ Ta
        · rw [ite_eq_left hka] at hp
          rcases Set.mem_insert_iff.mp hp with rfl | hp'
          · exact Or.inr (Or.inr (Or.inl ⟨hka, rfl⟩))
          · exact Or.inr (Or.inr (Or.inr (Or.inr hp')))
        · rw [ite_eq_right hka] at hp
          rcases Set.mem_insert_iff.mp hp with rfl | hp'
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hnotSnotTa hk hka, rfl⟩)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr hp')))
    have hpaOf2 : ∀ i ∈ S, (paOf i).2 ∈ Simg := by
      intro i hi; rw [hpaOf]; exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
    have hea_class : ∀ k p, p ∈ Fs k → p.1 = eₐ →
        (k ∈ S ∧ p.2 = (rOf k).2) ∨ (k ∈ Ta ∧ p.2 = pc k) := by
      intro k p hp hp1
      rcases hFsmem k p hp with ⟨hkS, rfl⟩ | ⟨hkS, rfl⟩ | ⟨hkTa, rfl⟩ | ⟨hkk, rfl⟩ | hc
      · exact Or.inl ⟨hkS, by rw [hpaOf]⟩
      · exact absurd ((hpbOf_fst k).symm.trans hp1) heab.symm
      · exact Or.inr ⟨hkTa, by rw [hqaOf]⟩
      · exact absurd (hqb_fst.symm.trans hp1) heab.symm
      · exact absurd hp1 (hDs_fst k p hc).1
    have heb_class : ∀ k p, p ∈ Fs k → p.1 = e_b →
        (k ∈ S ∧ p.2 = (rOf k).2) ∨ (k = i_b ∧ p.2 = cb) := by
      intro k p hp hp1
      rcases hFsmem k p hp with ⟨hkS, rfl⟩ | ⟨hkS, rfl⟩ | ⟨hkTa, rfl⟩ | ⟨hkk, rfl⟩ | hc
      · exact absurd ((hpaOf_fst k).symm.trans hp1) heab
      · exact Or.inl ⟨hkS, by rw [hpbOf]⟩
      · exact absurd ((hqaOf_fst k).symm.trans hp1) heab
      · exact Or.inr ⟨hkk, by rw [hqb]⟩
      · exact absurd hp1 (hDs_fst k p hc).2
    have hcore_of_ne : ∀ k p, p ∈ Fs k → p.1 ≠ eₐ → p.1 ≠ e_b → p ∈ Ds k := by
      intro k p hp hpa hpb
      rcases hFsmem k p hp with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | hc
      · exact absurd (hpaOf_fst k) hpa
      · exact absurd (hpbOf_fst k) hpb
      · exact absurd (hqaOf_fst k) hpa
      · exact absurd hqb_fst hpb
      · exact hc
    have hdisj' : Pairwise (Function.onFun Disjoint Fs) := by
      intro i j hij
      simp only [Function.onFun, Set.disjoint_left]
      intro p hpi hpj
      by_cases hp1a : p.1 = eₐ
      · rcases hea_class i p hpi hp1a with ⟨hiS, hi2⟩ | ⟨hiTa, hi2⟩ <;>
          rcases hea_class j p hpj hp1a with ⟨hjS, hj2⟩ | ⟨hjTa, hj2⟩
        · exact hrOf2_ne i hiS j hjS hij (hi2 ▸ hj2 ▸ rfl)
        · exact hU_notSimg (hi2 ▸ hj2 ▸ hpcU j hjTa) (hi2 ▸ hpaOf2 i hiS)
        · exact hU_notSimg (hj2 ▸ hi2 ▸ hpcU i hiTa) (hj2 ▸ hpaOf2 j hjS)
        · exact hij (hpc_inj i hiTa j hjTa (hi2 ▸ hj2 ▸ rfl))
      · by_cases hp1b : p.1 = e_b
        · rcases heb_class i p hpi hp1b with ⟨hiS, hi2⟩ | ⟨hii, hi2⟩ <;>
            rcases heb_class j p hpj hp1b with ⟨hjS, hj2⟩ | ⟨hjj, hj2⟩
          · exact hrOf2_ne i hiS j hjS hij (hi2 ▸ hj2 ▸ rfl)
          · exact hU_notSimg (hi2 ▸ hj2 ▸ hcbU) (hi2 ▸ hpaOf2 i hiS)
          · exact hU_notSimg (hj2 ▸ hi2 ▸ hcbU) (hj2 ▸ hpaOf2 j hjS)
          · exact hij (hii.trans hjj.symm)
        · exact Set.disjoint_left.mp (hDsdisj hij)
            (hcore_of_ne i p hpi hp1a hp1b) (hcore_of_ne j p hpj hp1a hp1b)
    have hshrink : ∀ i, (Fs i).ncard = (Ds i).ncard + 1 := by
      intro i
      by_cases hi : i ∈ S
      · simp only [hFs, ite_eq_left hi]
        have hpaD : paOf i ∉ insert (pbOf i) (Ds i \ {rOf i}) := by
          rw [Set.mem_insert_iff, not_or]
          exact ⟨hpa_ne_pb i, fun h ↦ hpa_notDs i i h.1⟩
        have hpbD : pbOf i ∉ Ds i \ {rOf i} := fun h ↦ hpb_notDs i i h.1
        rw [Set.ncard_insert_of_notMem hpaD (Set.toFinite _),
          Set.ncard_insert_of_notMem hpbD (Set.toFinite _),
          Set.ncard_sdiff_singleton_of_mem (hrOf_mem i hi).1]
        have hpos : 0 < (Ds i).ncard :=
          Set.Nonempty.ncard_pos (Set.toFinite _) ⟨rOf i, (hrOf_mem i hi).1⟩
        omega
      · simp only [hFs, ite_eq_right hi]
        by_cases hia : i ∈ Ta
        · rw [ite_eq_left hia, Set.ncard_insert_of_notMem (hqa_notDs i i) (Set.toFinite _)]
        · rw [ite_eq_right hia, Set.ncard_insert_of_notMem (hqb_notDs i) (Set.toFinite _)]
    have hDscore : ∀ i p, p ∈ Ds i → p.1 ≠ e₀ → p ∈ Fs i := by
      intro i p hpi hp0
      simp only [hFs]
      by_cases hi : i ∈ S
      · rw [ite_eq_left hi]
        refine Set.mem_insert_iff.mpr (Or.inr (Set.mem_insert_iff.mpr (Or.inr ⟨hpi, ?_⟩)))
        rw [Set.mem_singleton_iff]
        intro h; exact hp0 (h ▸ hrOf1 i hi)
      · rw [ite_eq_right hi]
        by_cases hia : i ∈ Ta
        · rw [ite_eq_left hia]; exact Set.mem_insert_of_mem _ hpi
        · rw [ite_eq_right hia]; exact Set.mem_insert_of_mem _ hpi
    have hrOf_notin : ∀ i ∈ S, rOf i ∉ Fs i := by
      intro i hiS hmem
      simp only [hFs, ite_eq_left hiS] at hmem
      rcases Set.mem_insert_iff.mp hmem with hpa' | hmem'
      · exact heane₀ (((hrOf1 i hiS).symm.trans (congrArg Prod.fst hpa')).trans (hpaOf_fst i)).symm
      rcases Set.mem_insert_iff.mp hmem' with hpb' | hmem''
      · exact hebne₀ (((hrOf1 i hiS).symm.trans (congrArg Prod.fst hpb')).trans (hpbOf_fst i)).symm
      · exact hmem''.2 rfl
    obtain ⟨hindU, hsurv, hcount⟩ := hfinish Fs (fun _ => 1)
      hindep' hdisj' hshrink hcore_of_ne hDscore hrOf_notin
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one] at hcount
    have heb : ((⋃ i, Fs i) ∩ edgeFiber e_b n).ncard = h' + 1 := by
      have hpbmem : ∀ i ∈ S, pbOf i ∈ (⋃ k, Fs k) := by
        intro i hi
        refine Set.mem_iUnion.mpr ⟨i, ?_⟩
        simp only [hFs, ite_eq_left hi]
        exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
      have hqbmem : qb ∈ (⋃ k, Fs k) := by
        refine Set.mem_iUnion.mpr ⟨i_b, ?_⟩
        have : i_b ∉ Ta := Finset.notMem_erase i_b T
        simp only [hFs, ite_eq_right hi_bnotS, ite_eq_right this]
        exact Set.mem_insert _ _
      have hEb : (⋃ k, Fs k) ∩ edgeFiber e_b n =
          (pbOf '' (↑S : Set (Fin (bodyBarDim n)))) ∪ {qb} := by
        apply Set.Subset.antisymm
        · rintro p ⟨hpU, hpf⟩
          rw [mem_edgeFiber] at hpf
          rw [Set.mem_iUnion] at hpU
          obtain ⟨k, hpk⟩ := hpU
          rcases heb_class k p hpk hpf with ⟨hkS, hp2⟩ | ⟨hkk, hp2⟩
          · refine Or.inl ⟨k, hkS, Prod.ext ?_ ?_⟩
            · rw [hpbOf]; exact hpf.symm
            · rw [hpbOf]; exact hp2.symm
          · refine Or.inr (Prod.ext ?_ ?_)
            · rw [hqb]; exact hpf
            · rw [hqb]; exact hp2
        · rintro p (⟨i, hiS, rfl⟩ | rfl)
          · exact ⟨hpbmem i (by simpa using hiS), by rw [mem_edgeFiber, hpbOf]⟩
          · exact ⟨hqbmem, by rw [mem_edgeFiber, hqb]⟩
      rw [hEb]
      have hdisjpieces : Disjoint (pbOf '' (↑S : Set (Fin (bodyBarDim n)))) {qb} := by
        rw [Set.disjoint_right]
        rintro x rfl ⟨i, hiS, hpb⟩
        have hImg : (rOf i).2 ∈ Simg := Finset.mem_image.mpr ⟨i, by simpa using hiS, rfl⟩
        have hcoord : (rOf i).2 = cb := by
          have := (Prod.ext_iff.mp hpb).2; rw [hpbOf, hqb] at this; exact this
        exact hU_notSimg hcbU (hcoord ▸ hImg)
      rw [Set.ncard_union_eq hdisjpieces (Set.toFinite _) (Set.toFinite _), Set.ncard_singleton]
      have hpbinj : Set.InjOn pbOf (↑S : Set (Fin (bodyBarDim n))) := by
        intro i hi j hj heq
        by_contra hij
        refine hrOf2_ne i (by simpa using hi) j (by simpa using hj) hij ?_
        exact (Prod.ext_iff.mp heq).2
      rw [hpbinj.ncard_image, Set.ncard_coe_finset, hScard]
    refine ⟨⋃ i, Fs i, hindU, hsurv, ?_, ?_⟩
    · intro hg; exact absurd hg (by omega)
    · intro _; exact ⟨hcount, heb⟩

/-- **KT Lemma 4.2(ii)** (`lem:edge-splitting`; Katoh–Tanigawa 2011, pp. 660–661): let `D ≥ 2`, let
the edges `eₐ ≠ e_b` join `v` to `a ≠ b`, both other than `v`, and let `e₀ ∉ E(G)`; `v` need not
have degree two. If an independent set `I'` of `M(G̃_v^{ab})` contains the `D - 1` copies
`ẽ₀ = edgeFiber e₀ n` of the new edge (`hsub`), then `M(G̃)` has an independent set `I` with
`|I| + 1 = |I'| + D` and `I ∖ (ẽₐ ∪ ẽ_b) = I' ∖ ẽ₀`. Each copy `(e₀, j)` is traded for `(eₐ, j)` and
`(e_b, j)` (`splitOff_reroute_packing`). -/
theorem splitOff_indep_extend_of_fiber_subset [DecidableEq β] [Finite β]
    {G : Graph α β} {n : ℕ} (hD : 2 ≤ bodyBarDim n) {v a b : α} {eₐ e_b e₀ : β}
    (hab : a ≠ b) (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b)
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b) (he₀ : e₀ ∉ E(G))
    {I' : Set (β × Fin (bodyHingeMult n))}
    (hI' : ((G.splitOff v a b e₀).matroidMG n).Indep I')
    (hsub : edgeFiber e₀ n ⊆ I') :
    ∃ I, (G.matroidMG n).Indep I ∧ I.ncard + 1 = I'.ncard + bodyBarDim n ∧
      I \ (edgeFiber eₐ n ∪ edgeFiber e_b n) = I' \ edgeFiber e₀ n := by
  obtain ⟨I, hI, hsurv, hc1, _⟩ :=
    splitOff_reroute_packing hD hab hav hbv heab hla hlb he₀ hI'
  have hfull : (I' ∩ edgeFiber e₀ n).ncard = bodyHingeMult n := by
    rw [Set.inter_eq_right.mpr hsub, edgeFiber_ncard]
  exact ⟨I, hI, hc1 hfull, hsurv⟩

/-- **KT Lemma 4.2(i)** (`lem:edge-splitting`, `lem:forest-surgery-unsplit`; Katoh–Tanigawa 2011,
pp. 660–661): under the hypotheses of `splitOff_indep_extend_of_fiber_subset`, if an independent set
`I'` of `M(G̃_v^{ab})` contains `h' < D - 1` of the copies `ẽ₀ = edgeFiber e₀ n` of the new edge
(`hlt`), then `M(G̃)` has an independent set `I` with `|I| = |I'| + D`, `h' + 1` copies of `e_b` and
`I ∖ (ẽₐ ∪ ẽ_b) = I' ∖ ẽ₀`. The `h'` copies of `ab` are traded for two edges at `v` each, as in KT
Lemma 4.2(ii), and each of the other `D - h'` forests gains one edge at `v`: all but one a copy of
`eₐ`, and the last a copy of `e_b` (`splitOff_reroute_packing`). -/
theorem splitOff_indep_extend_of_fiber_lt [DecidableEq β] [Finite β]
    {G : Graph α β} {n : ℕ} (hD : 2 ≤ bodyBarDim n) {v a b : α} {eₐ e_b e₀ : β}
    (hab : a ≠ b) (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b)
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b) (he₀ : e₀ ∉ E(G))
    {I' : Set (β × Fin (bodyHingeMult n))}
    (hI' : ((G.splitOff v a b e₀).matroidMG n).Indep I')
    (hlt : (I' ∩ edgeFiber e₀ n).ncard < bodyHingeMult n) :
    ∃ I, (G.matroidMG n).Indep I ∧ I.ncard = I'.ncard + bodyBarDim n ∧
      (I ∩ edgeFiber e_b n).ncard = (I' ∩ edgeFiber e₀ n).ncard + 1 ∧
      I \ (edgeFiber eₐ n ∪ edgeFiber e_b n) = I' \ edgeFiber e₀ n := by
  obtain ⟨I, hI, hsurv, _, hc2⟩ :=
    splitOff_reroute_packing hD hab hav hbv heab hla hlb he₀ hI'
  obtain ⟨hcount, heb⟩ := hc2 hlt
  exact ⟨I, hI, hcount, heb, hsurv⟩

end Graph
