/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Set.Card

/-!
# `edgesIn`: edges with both endpoints in a vertex set

For `G : SimpleGraph V` and `s : Set V`, `G.edgesIn s` is the set of edges
of `G` whose both endpoints lie in `s`. It is the basic selector used by
the sparsity definition (see `Sparsity.lean`).

The closest mathlib analogues are `SimpleGraph.Subgraph.induce` and
`SimpleGraph.induce`, both of which materialize the same content as a
graph rather than a `Set (Sym2 V)`. See `DESIGN.md` for the rationale.

## Main definition

* `SimpleGraph.edgesIn G s = G.edgeSet ∩ s.sym2`.

## Main lemmas

* `SimpleGraph.mem_edgesIn` — membership unfolding.
* `SimpleGraph.mk_mem_edgesIn` — specialised pair-form constructor for `mem_edgesIn`.
* `SimpleGraph.edgesIn_subset_edgeSet`, `edgesIn_mono` — basic inclusions.
* `SimpleGraph.edgesIn_univ`, `edgesIn_empty`, `edgesIn_bot` — corner cases.
* `SimpleGraph.edgesIn_finite` — finiteness over a finite vertex set.
* `SimpleGraph.mem_edgesIn_compl_singleton`, `edgesIn_compl_singleton` — vertex-deletion
  identities.
* `SimpleGraph.ncard_edgesIn_compl_singleton_add_ncard_incidenceSet` — vertex-deletion
  cardinality identity, the keystone for the Phase 2 minimum-degree argument.
* `SimpleGraph.edgesIn_inter` — edges-in distributes over intersection.
* `SimpleGraph.edgesIn_ncard_add_le` — supermodularity of edge counts:
  `(edgesIn S).ncard + (edgesIn T).ncard ≤ (edgesIn (S ∪ T)).ncard + (edgesIn (S ∩ T)).ncard`.
  The Phase 5 tight-set union-closure lemma's edge-arithmetic input.

## Project context

This file is part of the combinatorial-rigidity formalization. See
`ROADMAP.md` for the project plan and `notes/Phase1.md` for the
Phase 1 work log (this file's content is Phase 1).
-/

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- The set of edges of `G` whose both endpoints lie in `s`. -/
def edgesIn (s : Set V) : Set (Sym2 V) := G.edgeSet ∩ s.sym2

variable {G}

@[simp] lemma mem_edgesIn {e : Sym2 V} {s : Set V} :
    e ∈ G.edgesIn s ↔ e ∈ G.edgeSet ∧ (e : Set V) ⊆ s := by
  rw [edgesIn, Set.mem_inter_iff, Set.mem_sym2_iff_subset]

/-- Specialised constructor for `mem_edgesIn` at an explicit pair `s(x, y)`: an adjacent pair with
both endpoints in `s` lies in `G.edgesIn s`. Collapses the
`mem_edgesIn.mpr ⟨_, by rw [Sym2.coe_mk]; exact Set.insert_subset_iff.mpr ⟨_,
Set.singleton_subset_iff.mpr _⟩⟩` boilerplate that recurs in the Phase 5 blocker proofs. -/
lemma mk_mem_edgesIn {x y : V} {s : Set V} (h : G.Adj x y) (hx : x ∈ s) (hy : y ∈ s) :
    s(x, y) ∈ G.edgesIn s :=
  mem_edgesIn.mpr ⟨h, by
    rw [Sym2.coe_mk]
    exact Set.insert_subset_iff.mpr ⟨hx, Set.singleton_subset_iff.mpr hy⟩⟩

/-- Companion to `mk_mem_edgesIn`: an edge `s(x, y)` whose **left** endpoint lies outside `s`
cannot lie in `G.edgesIn s`. -/
lemma notMem_edgesIn_mk_of_left_notMem {x y : V} {s : Set V} (hxs : x ∉ s) :
    s(x, y) ∉ G.edgesIn s := fun hmem => by
  rw [mem_edgesIn, Sym2.coe_mk] at hmem
  exact hxs (hmem.2 (Set.mem_insert _ _))

/-- Companion to `mk_mem_edgesIn`: an edge `s(x, y)` whose **right** endpoint lies outside `s`
cannot lie in `G.edgesIn s`. -/
lemma notMem_edgesIn_mk_of_right_notMem {x y : V} {s : Set V} (hys : y ∉ s) :
    s(x, y) ∉ G.edgesIn s := fun hmem => by
  rw [mem_edgesIn, Sym2.coe_mk] at hmem
  exact hys (hmem.2 (Set.mem_insert_of_mem _ rfl))

lemma edgesIn_subset_edgeSet (s : Set V) : G.edgesIn s ⊆ G.edgeSet :=
  Set.inter_subset_left

@[gcongr]
lemma edgesIn_mono {s t : Set V} (h : s ⊆ t) : G.edgesIn s ⊆ G.edgesIn t :=
  fun _ ⟨he₁, he₂⟩ ↦ ⟨he₁, (Set.mem_sym2_iff_subset.mp he₂).trans h |> Set.mem_sym2_iff_subset.mpr⟩

@[simp] lemma edgesIn_univ : G.edgesIn Set.univ = G.edgeSet := by
  simp [edgesIn]

@[simp] lemma edgesIn_empty : G.edgesIn (∅ : Set V) = ∅ := by
  simp [edgesIn]

@[simp] lemma edgesIn_bot (s : Set V) : (⊥ : SimpleGraph V).edgesIn s = ∅ := by
  simp [edgesIn]

/-- A singleton set spans no edges: a single vertex contains no edge of a simple graph because
edges are non-loops. -/
@[simp] lemma edgesIn_singleton (G : SimpleGraph V) (v : V) : G.edgesIn ({v} : Set V) = ∅ := by
  ext e
  refine e.ind fun x y => ?_
  simp only [mem_edgesIn, mem_edgeSet, Set.mem_empty_iff_false, iff_false, not_and]
  intro hadj hsub
  have hx : x = v := hsub (Sym2.mem_mk_left x y)
  have hy : y = v := hsub (Sym2.mem_mk_right x y)
  rw [hx, hy] at hadj
  exact G.loopless.irrefl _ hadj

/-- For finite `s`, `G.edgesIn ↑s` is finite (it is contained in the symmetric square of `s`). -/
lemma edgesIn_finite (G : SimpleGraph V) (s : Finset V) : (G.edgesIn ↑s).Finite := by
  refine s.sym2.finite_toSet.subset ?_
  rw [Finset.coe_sym2]
  exact Set.inter_subset_right

/-! ### Vertex deletion: edges avoiding a vertex

Edges of `G` whose both endpoints differ from `v` are exactly the edges of `G` that are not
incident to `v`. This bridges `edgesIn` and `incidenceSet`, and is the keystone for vertex-
deletion edge-count arguments (Phase 2). -/

lemma mem_edgesIn_compl_singleton {v : V} {e : Sym2 V} :
    e ∈ G.edgesIn ({v}ᶜ : Set V) ↔ e ∈ G.edgeSet ∧ v ∉ e := by
  rw [mem_edgesIn, Set.subset_compl_singleton_iff]
  rfl

/-- Edges with both endpoints in `{v}ᶜ` are precisely the edges not incident to `v`. -/
lemma edgesIn_compl_singleton (v : V) :
    G.edgesIn ({v}ᶜ : Set V) = G.edgeSet \ G.incidenceSet v := by
  ext e
  grind [mem_edgesIn_compl_singleton, incidenceSet]

/-- Edges of `G` partition into "not incident to `v`" plus "incident to `v`": the cardinality
identity `#(edgesIn {v}ᶜ) + #(incidenceSet v) = #edgeSet`. The vertex-deletion edge-count
keystone for sparsity arguments. -/
lemma ncard_edgesIn_compl_singleton_add_ncard_incidenceSet [Finite V] (v : V) :
    (G.edgesIn ({v}ᶜ : Set V)).ncard + (G.incidenceSet v).ncard = G.edgeSet.ncard := by
  rw [edgesIn_compl_singleton]
  exact Set.ncard_diff_add_ncard_of_subset (G.incidenceSet_subset v) G.edgeSet.toFinite

/-! ### Modularity: edges-in on the intersection / union lattice

`edgesIn` distributes exactly over set-intersection but only sub-distributes over union —
an edge `{x, y}` with `x ∈ S \ T` and `y ∈ T \ S` lies in `edgesIn (S ∪ T)` but in neither
`edgesIn S` nor `edgesIn T`. The cardinality consequence is the "supermodular edge count"
inequality `edgesIn_ncard_add_le`, the only edge-arithmetic input of the Phase 5 tight-set
union-closure argument. -/

/-- `edgesIn` distributes over intersection: `G.edgesIn (S ∩ T) = G.edgesIn S ∩ G.edgesIn T`.
The companion union direction is only an inclusion (cf. `edgesIn_ncard_add_le`). -/
lemma edgesIn_inter (S T : Set V) :
    G.edgesIn (S ∩ T) = G.edgesIn S ∩ G.edgesIn T := by
  ext e
  simp only [Set.mem_inter_iff, mem_edgesIn, Set.subset_inter_iff]
  tauto

/-- **Supermodularity of `edgesIn` counts.** For any two vertex sets `S, T`, the sum
`(edgesIn S).ncard + (edgesIn T).ncard` is at most `(edgesIn (S ∪ T)).ncard +
(edgesIn (S ∩ T)).ncard`. The "edges crossing `S \ T` to `T \ S`" are counted on the right
but not on the left, so the inequality can be strict; intersection cancels via
`edgesIn_inter`. The lift of `Set.ncard_union_add_ncard_inter` to `edgesIn`. -/
lemma edgesIn_ncard_add_le [Finite V] (S T : Set V) :
    (G.edgesIn S).ncard + (G.edgesIn T).ncard ≤
      (G.edgesIn (S ∪ T)).ncard + (G.edgesIn (S ∩ T)).ncard := by
  have h_union : G.edgesIn S ∪ G.edgesIn T ⊆ G.edgesIn (S ∪ T) :=
    Set.union_subset (edgesIn_mono Set.subset_union_left)
                     (edgesIn_mono Set.subset_union_right)
  calc (G.edgesIn S).ncard + (G.edgesIn T).ncard
      = (G.edgesIn S ∪ G.edgesIn T).ncard + (G.edgesIn S ∩ G.edgesIn T).ncard :=
        (Set.ncard_union_add_ncard_inter _ _).symm
    _ = (G.edgesIn S ∪ G.edgesIn T).ncard + (G.edgesIn (S ∩ T)).ncard := by
        rw [← edgesIn_inter]
    _ ≤ (G.edgesIn (S ∪ T)).ncard + (G.edgesIn (S ∩ T)).ncard :=
        Nat.add_le_add_right (Set.ncard_le_ncard h_union) _

end SimpleGraph
