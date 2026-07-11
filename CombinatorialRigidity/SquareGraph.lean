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

Phase 25 (`sec:molecule-modelling`). The **square** `G.square` of a graph `G = (V, E)` is
`G` together with an edge for every pair of vertices at distance exactly two — the graph
`G² = (V, E²)` of Katoh–Tanigawa 2011, p. 650, used there to state the molecule modelling
equivalence: a molecule (atoms as bodies, bonds as hinges) is a bar-joint framework on `G²`
exactly when it is a hinge-concurrent body-hinge framework on `G`. This file supplies the
combinatorial substrate that equivalence needs: the square itself, and the fact that a closed
neighborhood `N[v] = {v} ∪ N(v)` induces a complete subgraph of `G²` covering every edge of
`G²` (KT p. 650: "in the square of a graph a vertex and its neighbors form a complete graph").

See `notes/Phase25.md` and `notes/Phase25-design.md` §3 (leaf W3) for the phase plan, and
`blueprint/src/chapter/molecule-modelling.tex` (`def:square-graph`, `lem:square-cliques`) for
the corresponding blueprint nodes.

## Main definitions

* `SimpleGraph.square G` — the square graph `G²`.
* `SimpleGraph.closedNeighborSet G v` — the closed neighborhood `N[v] = {v} ∪ N(v)`.

## Main results

* `SimpleGraph.le_square` — `G` is a subgraph of `G.square`.
* `SimpleGraph.isClique_closedNeighborSet_square` — every closed neighborhood is a clique
  of the square.
* `SimpleGraph.isClique_neighborSet_square` — the open neighborhood is also a clique (Phase 32,
  `lem:singleton-part-neighborhood`).
* `SimpleGraph.exists_mem_closedNeighborSet_of_square_adj` — every edge of `G.square` lies
  inside the closed neighborhood of some vertex of `G`.
* `SimpleGraph.three_le_ncard_closedNeighborSet_of_two_le_degree` — a vertex of degree at
  least two has a closed neighborhood of size at least three (the fact the square-graph
  dictionary of `def:hinge-concurrent` uses to determine a body's screw from its neighbors'
  velocities).
* `SimpleGraph.square_mono` — squaring is monotone under `≤` (Phase 32, trivial glue for the
  `thm:jacobs` induction peel).
* `SimpleGraph.square_deleteIncidenceSet_of_degree_le_one`,
  `SimpleGraph.neighborSet_square_of_degree_eq_one`,
  `SimpleGraph.ncard_neighborSet_square_of_degree_eq_one`,
  `SimpleGraph.isClique_neighborSet_square_of_degree_eq_one` — Phase 32
  (`lem:square-delete-degree-le-one`, `lem:square-leaf-neighborhood`): deleting a degree-≤-one
  vertex's edges commutes with squaring, and a degree-one vertex's square-neighborhood is the
  closed neighborhood of its unique neighbor (minus itself), hence a clique of the same size.
* `SimpleGraph.square_support_subset`, `SimpleGraph.square_induce_of_support_subset` — Phase 32
  (`lem:square-induce-support`): the square of `G` has support inside `G`'s, so squaring
  commutes with restriction to any support-covering vertex set.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-! ## The square graph -/

/-- The **square** of a graph `G`: distinct vertices `u, v` are adjacent in `G.square` when
they are already adjacent in `G`, or when they share a common neighbor in `G` (i.e. are at
graph distance exactly two). Katoh–Tanigawa 2011, p. 650. -/
def square (G : SimpleGraph V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ (G.Adj u v ∨ (G.commonNeighbors u v).Nonempty)
  symm u v := by
    rintro ⟨hne, hc | hc⟩
    · exact ⟨hne.symm, Or.inl hc.symm⟩
    · exact ⟨hne.symm, Or.inr (by rwa [commonNeighbors_symm])⟩
  loopless := ⟨fun u h => h.1 rfl⟩

@[simp]
theorem square_adj {u v : V} :
    G.square.Adj u v ↔ u ≠ v ∧ (G.Adj u v ∨ (G.commonNeighbors u v).Nonempty) := Iff.rfl

/-- `G` is a subgraph of its own square: every original edge survives. -/
theorem le_square (G : SimpleGraph V) : G ≤ G.square := fun _ _ h => ⟨h.ne, Or.inl h⟩

/-- **Subgraph monotonicity of squaring.** If `G ≤ G'` then `G.square ≤ G'.square`: an edge or
common-neighbor witness for `G` is also one for `G'`. Trivial glue for the `thm:jacobs`
degree-one induction peel (Phase 32), which needs `IsLaman3.mono_left` transported along the
squaring of a deleted-edge subgraph. -/
theorem square_mono {G G' : SimpleGraph V} (h : G ≤ G') : G.square ≤ G'.square := by
  rintro x y ⟨hne, hadj | hcn⟩
  · exact ⟨hne, Or.inl (h hadj)⟩
  · obtain ⟨w, hw⟩ := hcn
    rw [mem_commonNeighbors] at hw
    exact ⟨hne, Or.inr ⟨w, ⟨h hw.1, h hw.2⟩⟩⟩

/-! ## Closed neighborhoods -/

/-- The **closed neighborhood** of a vertex: itself together with its neighbors,
`N[v] = {v} ∪ N(v)`. -/
def closedNeighborSet (G : SimpleGraph V) (v : V) : Set V := insert v (G.neighborSet v)

@[simp]
theorem mem_closedNeighborSet {u v : V} :
    u ∈ G.closedNeighborSet v ↔ u = v ∨ G.Adj v u := Iff.rfl

theorem self_mem_closedNeighborSet (G : SimpleGraph V) (v : V) : v ∈ G.closedNeighborSet v :=
  Or.inl rfl

/-- Closed neighborhoods induce complete subgraphs of the square: any two distinct vertices
of `N[v]` are within distance two of each other, through `v` if neither is `v` itself. -/
theorem isClique_closedNeighborSet_square (G : SimpleGraph V) (v : V) :
    G.square.IsClique (G.closedNeighborSet v) := by
  intro x hx y hy hxy
  rcases hx with rfl | hx <;> rcases hy with rfl | hy
  · exact absurd rfl hxy
  · exact ⟨hxy, Or.inl hy⟩
  · exact ⟨hxy, Or.inl hx.symm⟩
  · exact ⟨hxy, Or.inr ⟨v, hx.symm, hy.symm⟩⟩

/-- The **open neighborhood** is also a clique of the square: a special case of
`isClique_closedNeighborSet_square`, restricting from `N[v]` to `N(v) ⊆ N[v]`. This is the form
Jackson–Jordán's counting bound (`lem:singleton-part-neighborhood`) uses at a singleton part. -/
theorem isClique_neighborSet_square (G : SimpleGraph V) (v : V) :
    G.square.IsClique (G.neighborSet v) :=
  (isClique_closedNeighborSet_square G v).subset (Set.subset_insert v _)

/-- Every edge of `G.square` lies inside the closed neighborhood of some vertex of `G`: an
original edge `uv` inside `N[u]`, a distance-two edge `uv` through a common neighbor `w`
inside `N[w]`. -/
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

/-- **Minimum-degree transfer.** A vertex of degree at least two has a closed neighborhood of
size at least three: itself plus (at least) two distinct neighbors. This is the combinatorial
fact behind KT's "in the square of a graph a vertex and its neighbors form a complete graph"
(p. 650) having enough points to determine a screw (`lem:screw-determination`). -/
theorem three_le_ncard_closedNeighborSet_of_two_le_degree
    (G : SimpleGraph V) {v : V} [Fintype (G.neighborSet v)] (hv : 2 ≤ G.degree v) :
    3 ≤ (G.closedNeighborSet v).ncard := by
  rw [ncard_closedNeighborSet]
  omega

/-! ## Degree-one vertices

Phase 32 (`sec:jacobs-zero-extension`). Jackson–Jordán's reduction of Jacobs' conjecture to
the minimum-degree-two case, and the degree-one rank formula (JJ Lemma 4.2), both peel off a
degree-one vertex `v` and pass to `G' = G - E_G(v)`. The two facts below package what squaring
does under that peel: it commutes with the deletion, and it turns `v`'s single edge into a
clique of size `d_G(u)` at `v`'s unique neighbor `u`. -/

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

/-- **The square-neighborhood of a degree-one vertex** (`lem:square-leaf-neighborhood`). If `v`
has degree one in `G` with neighbor `u`, its square-neighborhood is the closed neighborhood of
`u`, minus `v` itself: every square-neighbor of `v` is either `u` (`v`'s only edge) or a
neighbor of `u` (through the length-two path via `u`, `v`'s only possible common-neighbor
hop). -/
theorem neighborSet_square_of_degree_eq_one {G : SimpleGraph V} {v u : V}
    [Fintype (G.neighborSet v)] (hdeg : G.degree v = 1) (hu : G.Adj v u) :
    G.square.neighborSet v = G.closedNeighborSet u \ {v} := by
  ext w
  simp only [mem_neighborSet, square_adj, Set.mem_diff, mem_closedNeighborSet,
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

/-- **Degree count, `lem:square-leaf-neighborhood` (continued).** A degree-one vertex `v` has
the same `G.square`-degree as its unique neighbor `u`: the closed neighborhood of `u` has
`d_G(u) + 1` elements, and removing `v` (which lies in it) drops exactly one. -/
theorem ncard_neighborSet_square_of_degree_eq_one {G : SimpleGraph V} {v u : V}
    [Fintype (G.neighborSet v)] [Fintype (G.neighborSet u)]
    (hdeg : G.degree v = 1) (hu : G.Adj v u) :
    (G.square.neighborSet v).ncard = G.degree u := by
  classical
  rw [neighborSet_square_of_degree_eq_one hdeg hu,
    Set.ncard_diff_singleton_of_mem (mem_closedNeighborSet.mpr (Or.inr hu.symm)),
    ncard_closedNeighborSet]
  omega

/-- **Clique, `lem:square-leaf-neighborhood` (continued).** A degree-one vertex's
square-neighborhood is a clique of `G.square`: a subset of the clique `N_G[u]`
(`isClique_closedNeighborSet_square`). -/
theorem isClique_neighborSet_square_of_degree_eq_one {G : SimpleGraph V} {v u : V}
    [Fintype (G.neighborSet v)] (hdeg : G.degree v = 1) (hu : G.Adj v u) :
    G.square.IsClique (G.square.neighborSet v) := by
  rw [neighborSet_square_of_degree_eq_one hdeg hu]
  exact (isClique_closedNeighborSet_square G u).subset Set.diff_subset

/-! ## Restriction to a support-covering vertex set

Phase 32 (`lem:square-induce-support`). The `thm:jacobs` induction's base case restricts `G`
to the support of its non-isolated vertices; squaring needs to commute with that restriction. -/

/-- **Squaring does not grow the support.** Every edge of `G.square` already has both endpoints
in `G`'s own support: a direct edge or a common-neighbor witness of `G` puts each endpoint in
`G.support` directly. -/
theorem square_support_subset (G : SimpleGraph V) : G.square.support ⊆ G.support := by
  rintro x ⟨y, -, hadj | hcn⟩
  · exact hadj.left_mem_support
  · obtain ⟨w, hw⟩ := hcn
    rw [mem_commonNeighbors] at hw
    exact hw.1.left_mem_support

/-- **Squaring commutes with restriction to a support-covering set**
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
