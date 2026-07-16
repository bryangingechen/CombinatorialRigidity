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

Phase 32 (`sec:jacobs-degree-one`). The **core** (or *two-core*) `G.twoCore` of a graph `G` is
its maximal subgraph of minimum degree at least two: the join of every subgraph `H ≤ G` whose
support vertices all have `H`-degree at least two. Jackson–Jordán 2008 (*On the rigidity of
molecular graphs*, Combinatorica **28**, Lemma 4.2) use the core to reduce the square-graph
rank formula for a general connected graph to the minimum-degree-two case; this file supplies
the definition and the API that reduction needs, in particular that deleting the incident edges
of a degree-at-most-one vertex leaves the core unchanged.

See `notes/Phase32.md` (the L2 slice plan, T1) for the phase plan and
`blueprint/src/chapter/jacobs.tex` (`def:two-core`) for the corresponding blueprint node.

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

/-- The **core** (or *two-core*) of a graph `G`: its maximal subgraph of minimum degree at
least two, realized as the supremum of every subgraph `H ≤ G` whose support vertices all have
`H`-degree at least two. Jackson–Jordán 2008 Lemma 4.2. -/
def twoCore (G : SimpleGraph V) : SimpleGraph V :=
  sSup {H | H ≤ G ∧ ∀ v ∈ H.support, 2 ≤ (H.neighborSet v).ncard}

/-- The core is a subgraph of `G`. -/
theorem twoCore_le (G : SimpleGraph V) : G.twoCore ≤ G :=
  sSup_le fun _ h => h.1

/-- Any subgraph of `G` whose support vertices all have degree at least two sits inside the
core: it is one of the graphs the core's supremum ranges over. -/
theorem le_twoCore (hle : H ≤ G) (hmin : ∀ v ∈ H.support, 2 ≤ (H.neighborSet v).ncard) :
    H ≤ G.twoCore :=
  le_sSup ⟨hle, hmin⟩

/-! ## Minimum degree -/

/-- Every support vertex of the core has core-degree at least two: a support vertex of the
supremum is a support vertex of some defining subgraph `H` (`H ≤ G` with `H`-minimum degree
two), and `H`'s neighborhood only grows on passing to the whole core. -/
theorem twoCore_minDegree (G : SimpleGraph V) [Finite V] :
    ∀ v ∈ G.twoCore.support, 2 ≤ (G.twoCore.neighborSet v).ncard := by
  intro v hv
  obtain ⟨w, hw⟩ := hv
  obtain ⟨H, hH, hadj⟩ := sSup_adj.mp hw
  have hHle : H ≤ G.twoCore := le_twoCore hH.1 hH.2
  exact (hH.2 v ⟨w, hadj⟩).trans (Set.ncard_le_ncard (neighborSet_mono hHle v))

/-- A graph of minimum degree at least two on its own support is its own core. -/
theorem twoCore_eq_self_of_minDegree (G : SimpleGraph V) [Finite V]
    (hmin : ∀ v ∈ G.support, 2 ≤ (G.neighborSet v).ncard) : G.twoCore = G :=
  le_antisymm G.twoCore_le (G.le_twoCore le_rfl hmin)

/-! ## Interaction with a degree-≤-one vertex -/

/-- A vertex of degree at most one is not in the core's support: if it were, its core-degree
would be at least two by `twoCore_minDegree`, but the core-neighborhood sits inside `G`'s
neighborhood, which has size at most one. -/
theorem notMem_support_twoCore [Finite V] (hdeg : (G.neighborSet v).ncard ≤ 1) :
    v ∉ G.twoCore.support := by
  intro hv
  have h2 := G.twoCore_minDegree v hv
  have hle : (G.twoCore.neighborSet v).ncard ≤ (G.neighborSet v).ncard :=
    Set.ncard_le_ncard (neighborSet_mono G.twoCore_le v)
  omega

/-- **Deleting the incident edges of a degree-at-most-one vertex does not change the core.**
The core already avoids `v` (`notMem_support_twoCore`): every defining subgraph of `G.twoCore`
survives the deletion since it has no edge at `v`, giving `G.twoCore ≤ (G.deleteIncidenceSet
v).twoCore`; conversely `(G.deleteIncidenceSet v).twoCore ≤ G.deleteIncidenceSet v ≤ G` is
itself a minimum-degree-two subgraph of `G`, giving the reverse inclusion. -/
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
