/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Set.Card

/-!
# Upstream candidates: `Set.ncard` companions for `SimpleGraph` cardinality lemmas

Mathlib has `Fintype.card` / `Finset.card`-flavored equalities for
`SimpleGraph.edgeSet`, `SimpleGraph.incidenceSet`, and the complete graph in
`Mathlib/Combinatorics/SimpleGraph/Finite.lean`. The lemmas below are the
`Set.ncard` companions that the combinatorial-rigidity project repeatedly
needs.

The Lean namespace is the upstream one (`SimpleGraph`), not the project's, so
promotion to mathlib is a copy-paste alongside the existing `card_*_eq_*`
lemmas. See `Archive/CombinatorialRigidity/DESIGN.md` "Mirror directory".

## Contents (target file: `Mathlib/Combinatorics/SimpleGraph/Finite.lean`)

* `ncard_incidenceSet_eq_degree` — `(G.incidenceSet v).ncard = G.degree v`.
* `ncard_edgeSet_eq_card_edgeFinset` — `G.edgeSet.ncard = G.edgeFinset.card`.
* `ncard_edgeSet_top_eq_card_choose_two` — `(⊤ : SimpleGraph V).edgeSet.ncard
  = (Fintype.card V).choose 2`.
-/

namespace SimpleGraph

variable {V : Type*}

/-- `Set.ncard` form of `SimpleGraph.card_incidenceSet_eq_degree`. -/
theorem ncard_incidenceSet_eq_degree (G : SimpleGraph V) (v : V)
    [Fintype (G.neighborSet v)] :
    (G.incidenceSet v).ncard = G.degree v := by
  classical
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, card_incidenceSet_eq_degree]

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

end SimpleGraph
