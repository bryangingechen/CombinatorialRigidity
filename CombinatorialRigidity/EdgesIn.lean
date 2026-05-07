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
* `SimpleGraph.edgesIn_subset_edgeSet`, `edgesIn_mono` — basic inclusions.
* `SimpleGraph.edgesIn_univ`, `edgesIn_empty`, `edgesIn_bot` — corner cases.
* `SimpleGraph.edgesIn_finite` — finiteness over a finite vertex set.
* `SimpleGraph.mem_edgesIn_compl_singleton`, `edgesIn_compl_singleton` — vertex-deletion
  identities.
* `SimpleGraph.ncard_edgesIn_compl_singleton_add_ncard_incidenceSet` — vertex-deletion
  cardinality identity, the keystone for the Phase 2 minimum-degree argument.

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

@[simp] lemma mem_edgesIn_compl_singleton {v : V} {e : Sym2 V} :
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

end SimpleGraph
