/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Mathlib.Combinatorics.SimpleGraph.Finite
public import CombinatorialRigidity.Mathlib.Data.Finset.BooleanAlgebra
public import CombinatorialRigidity.Mathlib.Data.Fintype.Card
public import CombinatorialRigidity.Sparsity
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Laman graphs

A simple graph is **Laman** (or *minimally rigid in the plane*) if it is
`(2, 3)`-tight: every set of `k ≥ 2` vertices spans at most `2k − 3`
edges, with equality globally.

Laman's theorem (Pollaczek-Geiringer 1927, Laman 1970) identifies these
graphs with the generically minimally rigid graphs in the plane;
`LamanTheorem.lean` proves it in the form "generically rigid iff some
spanning subgraph is Laman". This file proves the facts about Laman graphs
that its induction rests on.

## Main definitions

* `SimpleGraph.IsLaman G` — `G.IsTight 2 3`.

## Main lemmas

* `SimpleGraph.IsLaman.isSparse`, `IsLaman.edgeSet_ncard` — accessor
  lemmas for the two components.
* `SimpleGraph.isLaman_iff` — unfolds `IsLaman` to the explicit
  conjunction `IsSparse 2 3 ∧ #E + 3 = 2 * #V`.
* `SimpleGraph.IsLaman.two_le_degree` — every vertex of a Laman graph
  on `n ≥ 3` vertices has degree at least 2.
* `SimpleGraph.IsLaman.exists_two_le_degree_le_three` — every Laman graph
  on `n ≥ 3` vertices contains a vertex of degree exactly 2 or 3. The
  degree-≤-3 half is the general `IsSparse.exists_degree_le_three`.
* `SimpleGraph.top_fin_two_isLaman` — `K₂` is Laman. The base case for
  the Henneberg construction.
* `SimpleGraph.IsLaman.iso` — Laman is preserved under graph isomorphism.

## Implementation notes

`IsLaman` is a non-reducible `def` (= `IsTight 2 3`); `grind` will not
unfold it. Use `refine ⟨?_, ?_⟩` or pattern-match to break the
And-structure inherited from `IsTight`. See `TACTICS-GOLF.md` §4.

The blueprint's `sec:laman` presents this file.
-/

public section

namespace SimpleGraph

variable {V : Type*}

/-- A simple graph is **Laman** (or *minimally rigid in the plane*) if it is `(2, 3)`-tight. -/
@[expose] def IsLaman (G : SimpleGraph V) : Prop := G.IsTight 2 3

theorem IsLaman.isSparse {G : SimpleGraph V} (h : G.IsLaman) : G.IsSparse 2 3 := h.1

/-- A Laman graph on `n` vertices has exactly `2n − 3` edges. -/
theorem IsLaman.edgeSet_ncard {G : SimpleGraph V} (h : G.IsLaman) :
    G.edgeSet.ncard + 3 = 2 * Nat.card V := h.2

/-- Unfolding of `IsLaman`: a graph is Laman iff it is `(2, 3)`-sparse and globally meets the
`2n − 3` edge count. -/
theorem isLaman_iff {G : SimpleGraph V} :
    G.IsLaman ↔ G.IsSparse 2 3 ∧ G.edgeSet.ncard + 3 = 2 * Nat.card V := Iff.rfl

/-! ### Minimum degree

In a Laman graph on `n ≥ 3` vertices, every vertex has degree at least 2. Apply sparsity to the
vertex set `{v}ᶜ`: the edges spanned there are exactly the edges of `G` not incident to `v`, so
`#E − G.degree v + 3 ≤ 2 * (n − 1)`; combined with tightness `#E + 3 = 2n`, this forces
`G.degree v ≥ 2`. -/
theorem IsLaman.two_le_degree [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (h : G.IsLaman)
    (hV : 3 ≤ Fintype.card V) (v : V) :
    2 ≤ G.degree v := by
  classical
  -- Apply sparsity to the Finset `{v}ᶜ`; combine with the vertex-deletion partition + tightness.
  have hsparse := h.isSparse ({v} : Finset V)ᶜ (by simp; omega)
  have hpart := G.ncard_edgesIn_compl_singleton_add_ncard_incidenceSet v
  have hE := h.edgeSet_ncard
  grind only [Finset.coe_compl_singleton, Finset.card_compl_singleton,
    G.ncard_incidenceSet_eq_degree, Nat.card_eq_fintype_card]

/-! ### A vertex of low degree

By `IsSparse.exists_degree_le_three` (handshake + the global edge bound), any `(2, 3)`-sparse
graph on `n ≥ 2` vertices has a vertex of degree at most 3. Combined with
`IsLaman.two_le_degree`, when `n ≥ 3` this yields a vertex of degree exactly 2 or 3: the
vertex that a reverse Henneberg move removes. -/

/-- In a Laman graph on `n ≥ 3` vertices there is a vertex of degree exactly 2 or 3.
A reverse Henneberg move removes such a vertex; the reverse decomposition
`Henneberg.IsLaman.exists_typeI_or_typeII_reverse` finds it through the sparse one,
`IsSparse.exists_typeI_or_typeII_reverse`, rather than through this lemma. -/
theorem IsLaman.exists_two_le_degree_le_three [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (h : G.IsLaman)
    (hV : 3 ≤ Fintype.card V) :
    ∃ v, 2 ≤ G.degree v ∧ G.degree v ≤ 3 := by
  obtain ⟨v, hv⟩ := h.isSparse.exists_degree_le_three (by omega)
  exact ⟨v, h.two_le_degree hV v, hv⟩

/-- A graph isomorphism preserves the Laman property. Specialization of `IsTight.iso` at
`(k, ℓ) = (2, 3)`. -/
theorem IsLaman.iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ≃g H) (h : G.IsLaman) : H.IsLaman :=
  IsTight.iso φ h

/-! ### Base case for Henneberg: `K₂` is Laman -/

/-- A Laman graph on exactly two vertices is the complete graph K₂. The proof reads off
`#G.edgeSet = 1` from tightness and matches with `#(⊤ : SimpleGraph V).edgeSet = 1`;
since `G ≤ ⊤` automatically, equal cardinalities force the edge sets equal, hence
`G = ⊤`. The (⇐) direction of Laman's theorem uses this for the base case of the
Henneberg induction on `Fintype.card V`. -/
theorem IsLaman.eq_top_of_card_eq_two [Fintype V]
    {G : SimpleGraph V} (h : G.IsLaman) (hV : Fintype.card V = 2) : G = ⊤ := by
  rw [← edgeSet_inj]
  have hG_card : G.edgeSet.ncard = 1 := by
    grind only [h.edgeSet_ncard, Nat.card_eq_fintype_card]
  have hTop_card : ((⊤ : SimpleGraph V).edgeSet).ncard = 1 := by
    rw [ncard_edgeSet_top_eq_card_choose_two, hV]; rfl
  refine Set.eq_of_subset_of_ncard_le (edgeSet_subset_edgeSet.mpr le_top) ?_ ?_
  · rw [hTop_card, hG_card]
  · classical
    exact (Set.toFinite _)

/-- The complete graph on two vertices is Laman: it has one edge, matching `2 · 2 − 3 = 1`.
This is the base case of the Henneberg construction. -/
theorem top_fin_two_isLaman : (⊤ : SimpleGraph (Fin 2)).IsLaman := by
  have hcard : ((⊤ : SimpleGraph (Fin 2)).edgeSet).ncard = 1 := by
    rw [ncard_edgeSet_top_eq_card_choose_two]; rfl
  refine ⟨fun s hs => ?_, by grind only [Nat.card_eq_fintype_card, Fintype.card_fin]⟩
  -- Sparsity. Only the case `s = Finset.univ` is non-vacuous.
  obtain rfl : s = Finset.univ :=
    s.eq_univ_of_card (by have := s.card_le_univ; grind only [Fintype.card_fin])
  grind only [!Finset.coe_univ, edgesIn_univ]

end SimpleGraph
