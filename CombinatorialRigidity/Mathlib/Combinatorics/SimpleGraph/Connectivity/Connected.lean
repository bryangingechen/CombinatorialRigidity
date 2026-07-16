/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
public import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Upstream candidates: reachability facts for a leaf-peel and a graph's own support

Phase 32 (`sec:jacobs-degree-one`, L2 slice plan T2 second half). Jackson–Jordán 2008's
degree-one rank formulas (Lemma 4.2) run their induction on a *support-relative*
strengthening: connectivity is read as reachability between support vertices, so the
induction can peel a leaf's incident edges while leaving the leaf itself in the ambient
vertex type `V` as an isolated vertex (no rank transport, no type-changing induction). This
file supplies the three reachability facts that strengthening needs: peeling a degree-≤-one
vertex's incidence set preserves reachability among the other vertices, a degree-one vertex's
unique neighbor keeps degree at least two once the graph has a third support vertex, and a
graph's own support is connected (as an induced subgraph) once every pair of support vertices
is reachable.

The Lean namespace is the upstream one (`SimpleGraph`), so promotion to mathlib is a
copy-paste alongside `IsTrail.not_mem_support_of_subsingleton_neighborSet` /
`mem_support_of_mem_walk_support`. See `DESIGN.md` "Mirror directory".

See `notes/Phase32.md` (the L2 slice plan, T2) for the phase plan.

## Contents (target file: `Mathlib/Combinatorics/SimpleGraph/Connectivity/Connected.lean`)

* `reachable_deleteIncidenceSet` — peeling the incidence set of a degree-at-most-one vertex
  `v` preserves reachability between any two vertices other than `v`: a path between them
  avoids `v` (a trail cannot pass through a leaf except at its own endpoints), so it survives
  the peel via `Walk.toDeleteEdges`.
* `two_le_degree_of_adj_degree_eq_one` — if `v` has degree one with neighbor `u`, the graph's
  support has at least three vertices, and every pair of support vertices is reachable, then
  `u` has degree at least two: a path from a third support vertex to `v` must approach `v`
  through its unique neighbor `u`, putting `u` in the path's interior, which a trail forbids
  at a second leaf.
* `connected_induce_support` — if every pair of support vertices is reachable and the support
  is nonempty, the induced subgraph on the support is connected: a path between two support
  vertices stays within the support (any vertex it visits is adjacent to another visited
  vertex, hence itself a support vertex), so it lifts to the induced subgraph.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Peeling the incidence set of a degree-at-most-one vertex `v` preserves reachability
between any two other vertices `x`, `y`: take a path witnessing `G.Reachable x y` (a path,
since paths are trails and the conversion loses no reachability); the trail cannot pass
through `v` (`IsTrail.not_mem_support_of_subsingleton_neighborSet`, `v`'s neighbor set having
at most one element), so none of its edges lie in `v`'s incidence set, and it transfers to
`G.deleteIncidenceSet v` via `Walk.toDeleteEdges`. -/
theorem reachable_deleteIncidenceSet {v x y : V} [Fintype (G.neighborSet v)]
    (hv : G.degree v ≤ 1) (hx : x ≠ v) (hy : y ≠ v) (h : G.Reachable x y) :
    (G.deleteIncidenceSet v).Reachable x y := by
  classical
  obtain ⟨p⟩ := h
  set p' := p.toPath with hp'_def
  have hsub : (G.neighborSet v).Subsingleton :=
    Set.ncard_le_one_iff_subsingleton.mp (by rw [ncard_neighborSet_eq_degree]; exact hv)
  have hvnotin : v ∉ (p'.val).support :=
    p'.property.isTrail.not_mem_support_of_subsingleton_neighborSet hx.symm hy.symm hsub
  have hp : ∀ e ∈ (p'.val).edges, e ∉ G.incidenceSet v := by
    intro e he hve
    exact hvnotin (Walk.mem_support_of_mem_edges he hve.2)
  exact ⟨(p'.val).toDeleteEdges (G.incidenceSet v) hp⟩

/-- If `v` has degree one with neighbor `u`, the support has at least three vertices, and
every pair of support vertices is reachable, then `u` has degree at least two. Otherwise
(`degree u = 1`, since `u` is adjacent to `v`) pick a support vertex `w` outside `{v, u}` and
a path from it to `v`; the path's penultimate vertex is `v`'s unique neighbor `u` (so `u`
sits in the path's interior, distinct from both endpoints), but a trail cannot pass through
a second degree-one vertex except at its own endpoints — contradiction. -/
theorem two_le_degree_of_adj_degree_eq_one {v u : V} [Fintype (G.neighborSet v)]
    [Fintype (G.neighborSet u)]
    (hconn : ∀ x ∈ G.support, ∀ y ∈ G.support, G.Reachable x y)
    (h3 : 3 ≤ G.support.ncard) (hv : G.degree v = 1) (hu : G.Adj v u) :
    2 ≤ G.degree u := by
  classical
  by_contra hlt
  have hlt' : G.degree u < 2 := not_le.mp hlt
  have hpos : 0 < G.degree u := hu.symm.degree_pos_left
  have hdu1 : G.degree u = 1 := by omega
  have hvmem : v ∈ G.support := (mem_support G).mpr ⟨u, hu⟩
  have humem : u ∈ G.support := (mem_support G).mpr ⟨v, hu.symm⟩
  have hex : (G.support \ {v, u}).Nonempty := by
    rw [Set.diff_nonempty]
    intro hsub
    have hle : G.support.ncard ≤ ({v, u} : Set V).ncard := Set.ncard_le_ncard hsub
    have h2 : ({v, u} : Set V).ncard ≤ 2 := Set.ncard_pair_le v u
    omega
  obtain ⟨w, hw_supp, hw_ne⟩ := hex
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hw_ne
  obtain ⟨hwv, hwu⟩ := hw_ne
  obtain ⟨p0⟩ := hconn w hw_supp v hvmem
  set p := p0.toPath with hp_def
  have hpnn : ¬ p.val.Nil := Walk.not_nil_of_ne hwv
  have hadjpen : G.Adj p.val.penultimate v := Walk.adj_penultimate hpnn
  have heq : p.val.penultimate = u := eq_of_adj_of_degree_le_one hv.le hadjpen.symm hu
  have hmem0 : p.val.penultimate ∈ p.val.support :=
    Walk.getVert_mem_support p.val (p.val.length - 1)
  rw [heq] at hmem0
  have hsub_u : (G.neighborSet u).Subsingleton :=
    Set.ncard_le_one_iff_subsingleton.mp (by rw [ncard_neighborSet_eq_degree]; omega)
  have htrail : p.val.IsTrail := p.property.isTrail
  exact (htrail.not_mem_support_of_subsingleton_neighborSet (Ne.symm hwu) hu.ne' hsub_u) hmem0

/-- If every pair of support vertices is reachable and the support is nonempty, the induced
subgraph on the support is connected: given two support vertices, a path between them (as
graph vertices) stays entirely within the support — any vertex it visits is adjacent to
another visited vertex (`mem_support_of_mem_walk_support`), hence itself has positive degree
— so it lifts to a path of the induced subgraph via `Walk.induce`. -/
theorem connected_induce_support (hconn : ∀ x ∈ G.support, ∀ y ∈ G.support, G.Reachable x y)
    (hne : G.support.Nonempty) : (G.induce G.support).Connected := by
  classical
  haveI : Nonempty ↥G.support := hne.to_subtype
  refine ⟨fun a b => ?_⟩
  by_cases heq : a.val = b.val
  · have hab : a = b := Subtype.ext heq
    subst hab
    exact Reachable.refl _
  · obtain ⟨p0⟩ := hconn a.val a.property b.val b.property
    set p := p0.toPath with hp_def
    have hpnn : ¬ p.val.Nil := Walk.not_nil_of_ne heq
    have hw : ∀ x ∈ p.val.support, x ∈ G.support := fun x hx =>
      mem_support_of_mem_walk_support p.val hpnn hx
    exact ⟨p.val.induce G.support hw⟩

end SimpleGraph
