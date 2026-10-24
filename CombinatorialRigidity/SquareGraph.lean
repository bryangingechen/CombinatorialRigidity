/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import CombinatorialRigidity.Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# The square of a graph

The **square** `G.square` of a graph `G = (V, E)` is `G` together with an edge for every pair of
vertices at distance exactly two: the graph `G² = (V, E²)` that Katoh–Tanigawa 2011 define on
p. 650, where a molecule whose atoms and bonds form `G` is modelled as a bar-joint framework on
`G²`, and also as a body-hinge framework on `G` with the hinges at each body meeting in one
point, because in `G²` a vertex and its neighbors form a complete graph (the equivalence of the
two models is Whiteley's; `sec:molecule-modelling`). This file supplies the square, the fact
that a closed neighborhood `N[v] = {v} ∪ N(v)` induces a complete subgraph of `G²`, every edge of
`G²` lying in one, and what squaring does under the deletion of the edges at a vertex of degree
at most one and under the restriction to a set containing the support. The blueprint presents
the file in `sec:molecule-modelling-defs` (`def:square-graph`, `lem:square-cliques`), with the
clique at a singleton part in `sec:jacobs-counting` and the rest in `sec:jacobs-zero-extension`.

## Main definitions

* `SimpleGraph.square G` — the square graph `G²`.
* `SimpleGraph.closedNeighborSet G v` — the closed neighborhood `N[v] = {v} ∪ N(v)`.

## Main results

* `SimpleGraph.le_square` — `G` is a subgraph of `G.square`.
* `SimpleGraph.isClique_closedNeighborSet_square` — every closed neighborhood is a clique
  of the square.
* `SimpleGraph.isClique_neighborSet_square` — the open neighborhood is also a clique
  (`lem:singleton-part-neighborhood`).
* `SimpleGraph.exists_mem_closedNeighborSet_of_square_adj` — every edge of `G.square` lies
  inside the closed neighborhood of some vertex of `G`.
* `SimpleGraph.square_deleteIncidenceSet_of_degree_le_one`,
  `SimpleGraph.neighborSet_square_of_degree_eq_one`,
  `SimpleGraph.ncard_neighborSet_square_of_degree_eq_one`,
  `SimpleGraph.isClique_neighborSet_square_of_degree_eq_one` (`lem:square-delete-degree-le-one`,
  `lem:square-leaf-neighborhood`): deleting the edges at a vertex of degree at most one commutes
  with squaring, and the neighborhood in `G²` of a degree-one vertex is the closed neighborhood of
  its neighbor `u` without itself, a clique of `G²` with `d_G(u)` elements.
* `SimpleGraph.square_support_subset`, `SimpleGraph.square_induce_of_support_subset`
  (`lem:square-induce-support`): the support of the square lies inside `G`'s, and squaring
  commutes with the restriction to any set containing the support.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-! ## The square graph -/

/-- The **square** of a graph `G`: distinct vertices `u, v` are adjacent in `G.square` when
they are already adjacent in `G`, or when they share a common neighbor in `G` (i.e. are at
graph distance exactly two). `def:square-graph`; Katoh–Tanigawa 2011, p. 650. -/
def square (G : SimpleGraph V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ (G.Adj u v ∨ (G.commonNeighbors u v).Nonempty)
  symm := ⟨fun u v => by
    rintro ⟨hne, hc | hc⟩
    · exact ⟨hne.symm, Or.inl hc.symm⟩
    · exact ⟨hne.symm, Or.inr (by rwa [commonNeighbors_symm])⟩⟩
  loopless := ⟨fun u h => h.1 rfl⟩

@[simp]
theorem square_adj {u v : V} :
    G.square.Adj u v ↔ u ≠ v ∧ (G.Adj u v ∨ (G.commonNeighbors u v).Nonempty) := Iff.rfl

/-- `G` is a subgraph of its own square: every original edge survives. -/
theorem le_square (G : SimpleGraph V) : G ≤ G.square := fun _ _ h => ⟨h.ne, Or.inl h⟩

/-! ## Closed neighborhoods -/

/-- The **closed neighborhood** of a vertex: itself together with its neighbors,
`N[v] = {v} ∪ N(v)`. -/
def closedNeighborSet (G : SimpleGraph V) (v : V) : Set V := insert v (G.neighborSet v)

@[simp]
theorem mem_closedNeighborSet {u v : V} :
    u ∈ G.closedNeighborSet v ↔ u = v ∨ G.Adj v u := Iff.rfl

theorem self_mem_closedNeighborSet (G : SimpleGraph V) (v : V) : v ∈ G.closedNeighborSet v :=
  Or.inl rfl

/-- Closed neighborhoods induce complete subgraphs of the square (`lem:square-cliques`): any two
distinct vertices of `N[v]` are within distance two of each other, through `v` if neither is `v`
itself. -/
theorem isClique_closedNeighborSet_square (G : SimpleGraph V) (v : V) :
    G.square.IsClique (G.closedNeighborSet v) := by
  intro x hx y hy hxy
  rcases hx with rfl | hx <;> rcases hy with rfl | hy
  · exact absurd rfl hxy
  · exact ⟨hxy, Or.inl hy⟩
  · exact ⟨hxy, Or.inl hx.symm⟩
  · exact ⟨hxy, Or.inr ⟨v, hx.symm, hy.symm⟩⟩

/-- The **open neighborhood** is also a clique of the square (`lem:singleton-part-neighborhood`,
the clique): a special case of `isClique_closedNeighborSet_square`, restricting from `N[v]` to
`N(v) ⊆ N[v]`. This is the form the counting bound uses at a singleton part. -/
theorem isClique_neighborSet_square (G : SimpleGraph V) (v : V) :
    G.square.IsClique (G.neighborSet v) :=
  (isClique_closedNeighborSet_square G v).subset (Set.subset_insert v _)

/-- Every edge of `G.square` lies inside the closed neighborhood of some vertex of `G`
(`lem:square-cliques`): an original edge `uv` inside `N[u]`, a distance-two edge `uv` through a
common neighbor `w` inside `N[w]`. -/
theorem exists_mem_closedNeighborSet_of_square_adj {u v : V} (h : G.square.Adj u v) :
    ∃ w, u ∈ G.closedNeighborSet w ∧ v ∈ G.closedNeighborSet w := by
  obtain ⟨-, hadj | hcn⟩ := h
  · exact ⟨u, G.self_mem_closedNeighborSet u, Or.inr hadj⟩
  · obtain ⟨w, hw⟩ := hcn
    rw [mem_commonNeighbors] at hw
    exact ⟨w, Or.inr hw.1.symm, Or.inr hw.2.symm⟩

/-- A closed neighborhood has cardinality one more than the vertex's degree. -/
theorem ncard_closedNeighborSet (G : SimpleGraph V) (v : V) [Fintype (G.neighborSet v)] :
    (G.closedNeighborSet v).ncard = G.degree v + 1 := by
  rw [closedNeighborSet, Set.ncard_insert_of_notMem G.notMem_neighborSet_self,
    ncard_neighborSet_eq_degree]

/-! ## Degree-one vertices

The proof of Jacobs' conjecture (`thm:jacobs`) and the degree-one rank formulas (JJ Lemma 4.2)
both delete the edge at a degree-one vertex `v` and pass to `G' = G - E_G(v)`. The lemmas below
say what squaring does under that deletion (`sec:jacobs-zero-extension`): it commutes with it,
and in `G²` the vertex `v` has the `d_G(u)` neighbors `N_G[u] \ {v}`, `u` its neighbor, which
form a clique. -/

/-- **Deleting the edges at a vertex of degree at most one commutes with squaring**
(`lem:square-delete-degree-le-one`). A path of length two between vertices `x, y ≠ v` cannot
pass through `v`, which has at most one neighbor, so the squares agree away from `v`; and
neither side has an edge at `v`. -/
theorem square_deleteIncidenceSet_of_degree_le_one {G : SimpleGraph V} {v : V}
    [Fintype (G.neighborSet v)] (hv : G.degree v ≤ 1) :
    (G.deleteIncidenceSet v).square = G.square.deleteIncidenceSet v := by
  ext x y
  simp only [square_adj, deleteIncidenceSet_adj]
  constructor
  · rintro ⟨hxy, ⟨hadj, hxv, hyv⟩ | hcn⟩
    · exact ⟨⟨hxy, Or.inl hadj⟩, hxv, hyv⟩
    · obtain ⟨w, hw⟩ := hcn
      rw [mem_commonNeighbors, deleteIncidenceSet_adj, deleteIncidenceSet_adj] at hw
      exact ⟨⟨hxy, Or.inr ⟨w, ⟨hw.1.1, hw.2.1⟩⟩⟩, hw.1.2.1, hw.2.2.1⟩
  · rintro ⟨⟨hxy, hadj | hcn⟩, hxv, hyv⟩
    · exact ⟨hxy, Or.inl ⟨hadj, hxv, hyv⟩⟩
    · obtain ⟨w, hw⟩ := hcn
      rw [mem_commonNeighbors] at hw
      rcases eq_or_ne w v with rfl | hwv
      · exact absurd (eq_of_adj_of_degree_le_one hv hw.1.symm hw.2.symm) hxy
      · exact ⟨hxy, Or.inr ⟨w,
          deleteIncidenceSet_adj.mpr ⟨hw.1, hxv, hwv⟩,
            deleteIncidenceSet_adj.mpr ⟨hw.2, hyv, hwv⟩⟩⟩

/-- **The neighborhood in the square of a degree-one vertex** (`lem:square-leaf-neighborhood`).
If `v` has degree one in `G` with neighbor `u`, its neighborhood in `G.square` is the closed
neighborhood of `u` without `v`: every neighbor of `v` in `G.square` is `u` (`v`'s only edge) or
a neighbor of `u` (`u` being the only possible common neighbor). -/
theorem neighborSet_square_of_degree_eq_one {G : SimpleGraph V} {v u : V}
    [Fintype (G.neighborSet v)] (hdeg : G.degree v = 1) (hu : G.Adj v u) :
    G.square.neighborSet v = G.closedNeighborSet u \ {v} := by
  ext w
  simp only [mem_neighborSet, square_adj, Set.mem_sdiff, mem_closedNeighborSet,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨hvw, hadj | hcn⟩
    · exact ⟨Or.inl (eq_of_adj_of_degree_le_one hdeg.le hu hadj).symm, hvw.symm⟩
    · obtain ⟨c, hc⟩ := hcn
      rw [mem_commonNeighbors] at hc
      obtain rfl : c = u := eq_of_adj_of_degree_le_one hdeg.le hc.1 hu
      exact ⟨Or.inr hc.2.symm, hvw.symm⟩
  · rintro ⟨rfl | hadj, hwv⟩
    · exact ⟨fun h => hwv h.symm, Or.inl hu⟩
    · exact ⟨fun h => hwv h.symm, Or.inr ⟨u, hu, hadj.symm⟩⟩

/-- **The degree in the square of a degree-one vertex** (`lem:square-leaf-neighborhood`). A
degree-one vertex `v` has `G.square`-degree the `G`-degree of its neighbor `u`: the closed
neighborhood of `u` has `d_G(u) + 1` elements, and removing `v` (which lies in it) drops exactly
one. -/
theorem ncard_neighborSet_square_of_degree_eq_one {G : SimpleGraph V} {v u : V}
    [Fintype (G.neighborSet v)] [Fintype (G.neighborSet u)]
    (hdeg : G.degree v = 1) (hu : G.Adj v u) :
    (G.square.neighborSet v).ncard = G.degree u := by
  classical
  rw [neighborSet_square_of_degree_eq_one hdeg hu,
    Set.ncard_sdiff_singleton_of_mem (mem_closedNeighborSet.mpr (Or.inr hu.symm)),
    ncard_closedNeighborSet]
  omega

/-- **The neighborhood in the square of a degree-one vertex is a clique**
(`lem:square-leaf-neighborhood`): it is a subset of the clique `N_G[u]`
(`isClique_closedNeighborSet_square`). -/
theorem isClique_neighborSet_square_of_degree_eq_one {G : SimpleGraph V} {v u : V}
    [Fintype (G.neighborSet v)] (hdeg : G.degree v = 1) (hu : G.Adj v u) :
    G.square.IsClique (G.square.neighborSet v) := by
  rw [neighborSet_square_of_degree_eq_one hdeg hu]
  exact (isClique_closedNeighborSet_square G u).subset Set.sdiff_subset

/-! ## Restriction to a set containing the support

When no vertex has degree one, the proof of Jacobs' conjecture (`thm:jacobs`) restricts `G` to its
support, the set of its non-isolated vertices; squaring commutes with that restriction
(`lem:square-induce-support`). -/

/-- **Squaring does not grow the support** (`lem:square-induce-support`). Every edge of `G.square`
has both endpoints in `G`'s support: an edge or a common neighbor in `G` puts each endpoint in
`G.support`. -/
theorem square_support_subset (G : SimpleGraph V) : G.square.support ⊆ G.support := by
  rintro x ⟨y, -, hadj | hcn⟩
  · exact hadj.left_mem_support
  · obtain ⟨w, hw⟩ := hcn
    rw [mem_commonNeighbors] at hw
    exact hw.1.left_mem_support

/-- **Squaring commutes with the restriction to a set containing the support**
(`lem:square-induce-support`). If `S` contains every non-isolated vertex of `G`, the square of
the induced subgraph `G[S]` is the induced subgraph of `G.square` on `S`: a length-two path
between vertices of `S` has its middle vertex non-isolated (`square_support_subset`), hence in
`S`, so adjacency in `G.square` and in `G[S].square` agree on `S`. -/
theorem square_induce_of_support_subset {G : SimpleGraph V} {S : Set V} (hS : G.support ⊆ S) :
    (G.induce S).square = G.square.induce S := by
  ext u v
  simp only [square_adj, induce_adj]
  constructor
  · rintro ⟨hne, hadj | hcn⟩
    · exact ⟨fun h => hne (Subtype.coe_injective h), Or.inl hadj⟩
    · obtain ⟨w, hw⟩ := hcn
      rw [mem_commonNeighbors, induce_adj, induce_adj] at hw
      exact ⟨fun h => hne (Subtype.coe_injective h), Or.inr ⟨w, hw⟩⟩
  · rintro ⟨hne, hadj | hcn⟩
    · exact ⟨fun h => hne (congrArg _ h), Or.inl hadj⟩
    · obtain ⟨w, hw⟩ := hcn
      rw [mem_commonNeighbors] at hw
      exact ⟨fun h => hne (congrArg _ h), Or.inr ⟨⟨w, hS hw.1.right_mem_support⟩, hw⟩⟩

end SimpleGraph
