/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Mathlib.Data.Set.Card
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Upstream candidates: `Set.ncard` companions for `SimpleGraph` cardinality lemmas

Mathlib has `Fintype.card` / `Finset.card`-flavored equalities for
`SimpleGraph.edgeSet`, `SimpleGraph.incidenceSet`, and the complete graph in
`Mathlib/Combinatorics/SimpleGraph/Finite.lean`. The lemmas below are the
`Set.ncard` companions that the combinatorial-rigidity project repeatedly
needs, plus (Phase 32) a degree-one uniqueness fact companion to the
existing `degree_eq_one_iff_existsUnique_adj`.

The Lean namespace is the upstream one (`SimpleGraph`), not the project's, so
promotion to mathlib is a copy-paste alongside the existing `card_*_eq_*`
lemmas. See `DESIGN.md` "Mirror directory".

## Contents (target file: `Mathlib/Combinatorics/SimpleGraph/Finite.lean`)

* `ncard_incidenceSet_eq_degree` — `(G.incidenceSet v).ncard = G.degree v`.
* `ncard_neighborSet_eq_degree` — `(G.neighborSet v).ncard = G.degree v`.
* `ncard_edgeSet_eq_card_edgeFinset` — `G.edgeSet.ncard = G.edgeFinset.card`.
* `ncard_edgeSet_top_eq_card_choose_two` — `(⊤ : SimpleGraph V).edgeSet.ncard
  = (Fintype.card V).choose 2`.
* `eq_of_adj_of_degree_le_one` — a vertex of degree at most one has at most
  one neighbor: any two vertices adjacent to it coincide.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*}

/-- `Set.ncard` form of `SimpleGraph.card_incidenceSet_eq_degree`. -/
theorem ncard_incidenceSet_eq_degree (G : SimpleGraph V) (v : V)
    [Fintype (G.neighborSet v)] :
    (G.incidenceSet v).ncard = G.degree v := by
  classical
  rw [Set.ncard_eq_card_coe, card_incidenceSet_eq_degree]

/-- `Set.ncard` form of `SimpleGraph.card_neighborSet_eq_degree`. -/
theorem ncard_neighborSet_eq_degree (G : SimpleGraph V) (v : V)
    [Fintype (G.neighborSet v)] :
    (G.neighborSet v).ncard = G.degree v := by
  rw [Set.ncard_eq_card_coe, card_neighborSet_eq_degree]

/-- The `Set.ncard` of `G.edgeSet` agrees with the `Finset.card` of `G.edgeFinset`. Companion of
`SimpleGraph.coe_edgeFinset`. -/
theorem ncard_edgeSet_eq_card_edgeFinset (G : SimpleGraph V) [Fintype G.edgeSet] :
    G.edgeSet.ncard = G.edgeFinset.card := by
  rw [← Set.ncard_coe_finset, coe_edgeFinset]

/-- `Set.ncard` form of `SimpleGraph.card_edgeFinset_top_eq_card_choose_two`. -/
theorem ncard_edgeSet_top_eq_card_choose_two [Fintype V] :
    ((⊤ : SimpleGraph V).edgeSet).ncard = (Fintype.card V).choose 2 := by
  classical
  rw [ncard_edgeSet_eq_card_edgeFinset, card_edgeFinset_top_eq_card_choose_two]

/-- A vertex of degree at most one has at most one neighbor: any two vertices adjacent to it
coincide. Companion to `degree_eq_one_iff_existsUnique_adj`, stated for the inequality
hypothesis used when only an upper bound on the degree is in hand (not its exact value). -/
theorem eq_of_adj_of_degree_le_one {G : SimpleGraph V} {v x y : V} [Fintype (G.neighborSet v)]
    (hv : G.degree v ≤ 1) (hx : G.Adj v x) (hy : G.Adj v y) : x = y := by
  have hdeg : G.degree v = 1 := le_antisymm hv hx.degree_pos_left
  obtain ⟨w, -, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hdeg
  rw [huniq x hx, huniq y hy]

end SimpleGraph
