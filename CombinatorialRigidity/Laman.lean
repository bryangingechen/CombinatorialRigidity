/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Sparsity
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Laman graphs

A simple graph is **Laman** (or *minimally rigid in the plane*) if it is
`(2, 3)`-tight: every set of `k ≥ 2` vertices spans at most `2k − 3`
edges, with equality globally.

Laman's 1970 theorem identifies these graphs with the minimally
generically rigid graphs in the plane. The combinatorial half — counts
and Henneberg moves — is what this directory builds toward.

## Main definitions

* `SimpleGraph.IsLaman G` — `G.IsTight 2 3`.

## Main lemmas

* `SimpleGraph.IsLaman.isSparse`, `IsLaman.edgeSet_ncard` — accessor
  lemmas for the two components.
* The base case for the Henneberg construction: `K₂` (the complete graph
  on `Fin 2`) is Laman. See the worked example below.
-/

namespace SimpleGraph

variable {V : Type*}

/-- A simple graph is **Laman** (or *minimally rigid in the plane*) if it is `(2, 3)`-tight. -/
def IsLaman (G : SimpleGraph V) : Prop := G.IsTight 2 3

theorem IsLaman.isSparse {G : SimpleGraph V} (h : G.IsLaman) : G.IsSparse 2 3 := h.1

/-- A Laman graph on `n` vertices has exactly `2n − 3` edges. -/
theorem IsLaman.edgeSet_ncard {G : SimpleGraph V} (h : G.IsLaman) :
    G.edgeSet.ncard + 3 = 2 * Nat.card V := h.2

/-! ### A concrete sanity check: `K₂` is Laman

The single-edge graph on two vertices is the base case for the Henneberg construction. -/

example : (⊤ : SimpleGraph (Fin 2)).IsLaman := by
  have hcard : ((⊤ : SimpleGraph (Fin 2)).edgeSet).ncard = 1 := by
    rw [← coe_edgeFinset, Set.ncard_coe_finset, card_edgeFinset_top_eq_card_choose_two]; rfl
  refine ⟨fun s hs => ?_, by grind only [Nat.card_eq_fintype_card, Fintype.card_fin]⟩
  -- Sparsity. Only the case `s = Finset.univ` is non-vacuous.
  have hsle : s.card ≤ 2 := by simpa using Finset.card_le_card (Finset.subset_univ s)
  obtain rfl : s = Finset.univ := s.eq_univ_of_card (by grind only [Fintype.card_fin])
  grind only [!Finset.coe_univ, edgesIn_univ]

end SimpleGraph
