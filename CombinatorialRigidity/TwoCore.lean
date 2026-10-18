/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Data.Set.Card

/-!
# The two-core of a graph

The **core** (or *two-core*) `G.twoCore` of a graph `G` is its maximal subgraph of minimum
degree at least two: the join of every subgraph `H ≤ G` whose support vertices all have
`H`-degree at least two. Jackson–Jordán 2008 (*On the rigidity of molecular graphs*,
Combinatorica **28**, §4) define it before their Lemma 4.2, which gives the rank of the square of
a connected graph through that of the square of its core; this file supplies the definition and
the lemmas that formula needs, in particular that deleting the edges at a vertex of degree at
most one leaves the core unchanged. The blueprint presents the file in `sec:jacobs-degree-one`
(`def:two-core`, `lem:two-core-largest`, `lem:two-core-degree-one`).

## Main definitions

* `SimpleGraph.twoCore G` — the maximal subgraph of `G` with minimum degree at least two,
  realized as a supremum over all such subgraphs.

## Main results

* `SimpleGraph.twoCore_le` — the core is a subgraph of `G`.
* `SimpleGraph.le_twoCore` — any minimum-degree-two subgraph of `G` sits inside the core.
* `SimpleGraph.twoCore_minDegree` — every support vertex of the core has core-degree at
  least two.
* `SimpleGraph.twoCore_eq_self_of_minDegree` — a graph of minimum degree at least two on its
  own support is its own core.
* `SimpleGraph.notMem_support_twoCore` — a vertex of degree at most one is not in the core's
  support.
* `SimpleGraph.twoCore_deleteIncidenceSet` — deleting the incident edges of a degree-at-most-
  one vertex does not change the core.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G H : SimpleGraph V} {v : V}

/-! ## Definition -/

/-- The **core** (or *two-core*) of a graph `G` (`def:two-core`; Jackson–Jordán 2008 §4, before
their Lemma 4.2): its maximal subgraph of minimum degree at least two, realized as the supremum
of every subgraph `H ≤ G` whose support vertices all have `H`-degree at least two. -/
def twoCore (G : SimpleGraph V) : SimpleGraph V :=
  sSup {H | H ≤ G ∧ ∀ v ∈ H.support, 2 ≤ (H.neighborSet v).ncard}

/-- The core is a subgraph of `G` (`lem:two-core-largest`). -/
theorem twoCore_le (G : SimpleGraph V) : G.twoCore ≤ G :=
  sSup_le fun _ h => h.1

/-- Any subgraph of `G` whose support vertices all have degree at least two lies inside the
core (`lem:two-core-largest`): it is one of the graphs the core's supremum ranges over. -/
theorem le_twoCore (hle : H ≤ G) (hmin : ∀ v ∈ H.support, 2 ≤ (H.neighborSet v).ncard) :
    H ≤ G.twoCore :=
  le_sSup ⟨hle, hmin⟩

/-! ## Minimum degree -/

/-- Every support vertex of the core has degree at least two in the core
(`lem:two-core-largest`): a support vertex of the supremum is a support vertex of some defining
subgraph `H` (`H ≤ G` with `H`-minimum degree two), and `H`'s neighborhood only grows on passing
to the whole core. -/
theorem twoCore_minDegree (G : SimpleGraph V) [Finite V] :
    ∀ v ∈ G.twoCore.support, 2 ≤ (G.twoCore.neighborSet v).ncard := by
  intro v hv
  obtain ⟨w, hw⟩ := hv
  obtain ⟨H, hH, hadj⟩ := sSup_adj.mp hw
  have hHle : H ≤ G.twoCore := le_twoCore hH.1 hH.2
  exact (hH.2 v ⟨w, hadj⟩).trans (Set.ncard_le_ncard (neighborSet_mono hHle v))

/-- A graph of minimum degree at least two on its own support is its own core
(`lem:two-core-degree-one`). -/
theorem twoCore_eq_self_of_minDegree (G : SimpleGraph V)
    (hmin : ∀ v ∈ G.support, 2 ≤ (G.neighborSet v).ncard) : G.twoCore = G :=
  le_antisymm G.twoCore_le (G.le_twoCore le_rfl hmin)

/-! ## Interaction with a degree-≤-one vertex -/

/-- A vertex of degree at most one is not in the core's support (`lem:two-core-degree-one`): if
it were, its degree in the core would be at least two by `twoCore_minDegree`, but its
neighborhood in the core lies inside its neighborhood in `G`, which has size at most one. -/
theorem notMem_support_twoCore [Finite V] (hdeg : (G.neighborSet v).ncard ≤ 1) :
    v ∉ G.twoCore.support := by
  intro hv
  have h2 := G.twoCore_minDegree v hv
  have hle : (G.twoCore.neighborSet v).ncard ≤ (G.neighborSet v).ncard :=
    Set.ncard_le_ncard (neighborSet_mono G.twoCore_le v)
  omega

/-- **Deleting the edges at a vertex of degree at most one does not change the core**
(`lem:two-core-degree-one`). The core avoids `v` (`notMem_support_twoCore`), so it is a subgraph
of `G.deleteIncidenceSet v` of minimum degree two, giving
`G.twoCore ≤ (G.deleteIncidenceSet v).twoCore`; conversely
`(G.deleteIncidenceSet v).twoCore ≤ G.deleteIncidenceSet v ≤ G` is itself a subgraph of `G` of
minimum degree two, giving the reverse inclusion. -/
theorem twoCore_deleteIncidenceSet [Finite V] (hdeg : (G.neighborSet v).ncard ≤ 1) :
    (G.deleteIncidenceSet v).twoCore = G.twoCore := by
  have hnotMem := notMem_support_twoCore hdeg
  refine le_antisymm ?_ ?_
  · exact le_twoCore ((G.deleteIncidenceSet v).twoCore_le.trans (G.deleteIncidenceSet_le v))
      (G.deleteIncidenceSet v).twoCore_minDegree
  · refine le_twoCore (fun a b hadj => deleteIncidenceSet_adj.mpr ⟨G.twoCore_le hadj, ?_, ?_⟩)
      (G.twoCore_minDegree)
    · rintro rfl; exact hnotMem hadj.left_mem_support
    · rintro rfl; exact hnotMem hadj.right_mem_support

end SimpleGraph
