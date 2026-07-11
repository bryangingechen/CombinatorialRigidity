/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
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

end SimpleGraph
