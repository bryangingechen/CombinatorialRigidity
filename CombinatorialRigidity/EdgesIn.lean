/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Finset.Sym
public import Mathlib.Data.Set.Card

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
* `SimpleGraph.edgeSet_fromEdgeSet_of_off_diag`,
  `SimpleGraph.edgesIn_fromEdgeSet_of_off_diag` — for off-diagonal `X`
  (i.e. `X ⊆ ⊤.edgeSet`), `fromEdgeSet X`'s `edgeSet` is already `X`, and
  consequently `(fromEdgeSet X).edgesIn S = X ∩ S.sym2`.
* `SimpleGraph.edgesIn_finite` — finiteness over a finite vertex set.
* `SimpleGraph.mem_edgesIn_compl_singleton`, `edgesIn_compl_singleton` — vertex-deletion
  identities.
* `SimpleGraph.ncard_edgesIn_compl_singleton_add_ncard_incidenceSet` — vertex-deletion
  cardinality identity, the keystone for the Phase 2 minimum-degree argument.
* `SimpleGraph.edgesIn_inter` — edges-in distributes over intersection.
* `SimpleGraph.edgesIn_ncard_add_le` — supermodularity of edge counts:
  `(edgesIn S).ncard + (edgesIn T).ncard ≤ (edgesIn (S ∪ T)).ncard + (edgesIn (S ∩ T)).ncard`.
  The Phase 5 tight-set union-closure lemma's edge-arithmetic input.
* `SimpleGraph.IsClique.ncard_edgesIn` — a clique's edge count: for `X : Finset V` a clique of
  `G`, `(G.edgesIn ↑X).ncard = X.card.choose 2`. The JJ Lemma 5.2 counting input (Phase 32).

## Project context

This file is part of the combinatorial-rigidity formalization. See
`ROADMAP.md` for the project plan and `notes/Phase1.md` for the
Phase 1 work log (this file's content is Phase 1).
-/

public section

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- The set of edges of `G` whose both endpoints lie in `s`. -/
@[expose] def edgesIn (s : Set V) : Set (Sym2 V) := G.edgeSet ∩ s.sym2

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

/-- For an off-diagonal edge set `X` (i.e. `X ⊆ ⊤.edgeSet`), `fromEdgeSet X` already
has `X` as its edge set — no `sdiff Sym2.diagSet` to clear. -/
lemma edgeSet_fromEdgeSet_of_off_diag {X : Set (Sym2 V)}
    (hX : X ⊆ (⊤ : SimpleGraph V).edgeSet) : (fromEdgeSet X).edgeSet = X := by
  rw [edgeSet_fromEdgeSet, sdiff_eq_left, Set.disjoint_left]
  intro e he_X he_diag
  exact (edgeSet_top (V := V) ▸ hX he_X) he_diag

/-- Combined `edgesIn` + off-diagonal `fromEdgeSet` simplification: for `X ⊆ ⊤.edgeSet`,
`(fromEdgeSet X).edgesIn S = X ∩ S.sym2`. Composes `edgeSet_fromEdgeSet_of_off_diag` with
the definition of `edgesIn`. -/
lemma edgesIn_fromEdgeSet_of_off_diag {X : Set (Sym2 V)}
    (hX : X ⊆ (⊤ : SimpleGraph V).edgeSet) (S : Set V) :
    (fromEdgeSet X).edgesIn S = X ∩ S.sym2 := by
  unfold edgesIn
  rw [edgeSet_fromEdgeSet_of_off_diag hX]

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

/-- Edges of `G` with both endpoints in `S` are exactly the `Sym2.map Subtype.val`-image of the
edges of the induced subgraph `G.induce S` on `S`. The bridge between our `edgesIn` selector
(stated in `Sym2 V`) and mathlib's `SimpleGraph.induce` (whose edges live in `Sym2 ↥S`). -/
lemma edgesIn_eq_image_induce_edgeSet (G : SimpleGraph V) (S : Set V) :
    G.edgesIn S = Sym2.map (Subtype.val : ↥S → V) '' (G.induce S).edgeSet := by
  ext e
  simp only [mem_edgesIn, Set.mem_image]
  refine ⟨fun ⟨he_adj, he_sub⟩ => ?_, ?_⟩
  · induction e with | h u v =>
      rw [Sym2.coe_mk, Set.insert_subset_iff, Set.singleton_subset_iff] at he_sub
      exact ⟨s(⟨u, he_sub.1⟩, ⟨v, he_sub.2⟩), he_adj, rfl⟩
  · rintro ⟨e', he', rfl⟩
    refine e'.ind (fun u v he' => ?_) he'
    refine ⟨he', ?_⟩
    rw [Sym2.map_mk, Sym2.coe_mk, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨u.2, v.2⟩

/-- Cardinality bridge: edges in `S` and edges of the induced subgraph have the same count.
Follows from `edgesIn_eq_image_induce_edgeSet` and injectivity of `Sym2.map Subtype.val`. -/
lemma ncard_edgesIn_eq_ncard_induce_edgeSet (G : SimpleGraph V) (S : Set V) :
    (G.edgesIn S).ncard = (G.induce S).edgeSet.ncard := by
  rw [edgesIn_eq_image_induce_edgeSet,
    Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)]

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

/-! ### Cliques

The edges induced on a clique are exactly the two-element subsets of it: transport
`edgesIn` to the induced subgraph (`ncard_edgesIn_eq_ncard_induce_edgeSet`), which is
complete on a clique (`isClique_iff_induce_eq`), and count the complete graph's edges
(`ncard_edgeSet_top_eq_card_choose_two`). -/

/-- A clique's edge count: if `X : Finset V` is a clique of `G` (every two distinct vertices
of `X` adjacent), the edges of `G` inside `X` number exactly `C(#X, 2)`. -/
theorem IsClique.ncard_edgesIn {X : Finset V} (h : G.IsClique (↑X : Set V)) :
    (G.edgesIn (↑X : Set V)).ncard = X.card.choose 2 := by
  classical
  rw [ncard_edgesIn_eq_ncard_induce_edgeSet, (isClique_iff_induce_eq G).mp h,
    ncard_edgeSet_top_eq_card_choose_two]
  simp

end SimpleGraph
