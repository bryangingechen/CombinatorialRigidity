/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.BodyBar.KFrame
import CombinatorialRigidity.LamanTheorem
import CombinatorialRigidity.LinearRigidityMatroid
import CombinatorialRigidity.PebbleGame.Correctness

/-!
# Non-vacuity witnesses for the main results

A main result can be free of `sorry` and use only the three standard axioms while no input
satisfies its hypotheses: `#print axioms` does not see that, and the theorem then says nothing.
Each theorem here applies one main result of `formalization.yaml` at a small input of its
intended class, with every hypothesis discharged, and states what the conclusion says at that
input (for an `iff`, the side the theorem derives there). Each is the closed declaration that
`PHASE-BOUNDARIES.md`'s close checklist asks of a main result. `molecular_conjecture_witness`
(`Molecular/AlgebraicInduction/Nonvacuity.lean`) is the one for `molecular_conjecture`.

## The witnesses

* `isGenericallyRigid_two_iff_exists_isLaman_le_witness`: Laman's theorem (Pollaczek-Geiringer,
  Laman) at `K₂`, the smallest graph its hypothesis `2 ≤ |V|` admits. `K₂` is Laman, so it is
  generically rigid in the plane.
* `linearRigidityMatroid_eq_rigidityMatroid_witness`: on two vertices, a placement at which the
  linear rigidity matroid equals the planar count matroid, and at which the row of `K₂`'s one
  edge is independent.
* `countMatroid_indep_iff_runPebbleGame_witness`: Lee and Streinu's pebble game, at the planar
  parameters `(k, ℓ) = (2, 3)`, accepts `K₂`, whose edge set is independent in the count matroid.
* `tutte_nash_williams_witness`: the double edge (two parallel edges between two vertices) is
  `(2, 2)`-sparse, so by Tutte and Nash-Williams it is the union of two edge-disjoint forests. It
  is the smallest multigraph that needs two.
* `kFrameMatroid_eq_unionPow_cycleMatroid_witness`: at the double edge and `k = 2`, Whiteley's
  identification of the generic `2`-frame matroid with the two-fold union of the cycle matroid,
  and what it gives there: the two parallel bars, a cycle of the graph, are independent in the
  `2`-frame matroid.
-/

open scoped Graph

namespace CombinatorialRigidity

open SimpleGraph

/-! ### The planar rows, at `K₂` -/

/-- **Laman's theorem (Pollaczek-Geiringer, Laman) at `K₂`**:
`SimpleGraph.isGenericallyRigid_two_iff_exists_isLaman_le` at the complete graph on two vertices,
its hypothesis `2 ≤ |V|` met with equality. `K₂` is its own Laman spanning subgraph
(`SimpleGraph.top_fin_two_isLaman`), so it is generically rigid in the plane. -/
theorem isGenericallyRigid_two_iff_exists_isLaman_le_witness :
    (⊤ : SimpleGraph (Fin 2)).IsGenericallyRigid 2 :=
  (isGenericallyRigid_two_iff_exists_isLaman_le (by simp)).mpr ⟨⊤, le_rfl, top_fin_two_isLaman⟩

/-- **The planar rigidity matroid as a linear matroid, on two vertices**:
`SimpleGraph.linearRigidityMatroid_eq_rigidityMatroid` at `V = Fin 2`. Its placement `p` makes
the linear rigidity matroid the planar count matroid, so the row of `K₂`'s one edge, a
`(2, 3)`-sparse edge set, is independent at `p`. -/
theorem linearRigidityMatroid_eq_rigidityMatroid_witness :
    ∃ p : Framework (Fin 2) 2,
      linearRigidityMatroid (Fin 2) 2 p = rigidityMatroid (Fin 2) ∧
        (linearRigidityMatroid (Fin 2) 2 p).Indep (⊤ : SimpleGraph (Fin 2)).edgeSet := by
  obtain ⟨p, hp⟩ := linearRigidityMatroid_eq_rigidityMatroid (V := Fin 2)
  refine ⟨p, hp, ?_⟩
  rw [hp, rigidityMatroid, countMatroid_indep_iff, fromEdgeSet_edgeSet]
  exact ⟨subset_rfl, top_fin_two_isLaman.isSparse⟩

/-- **The pebble game accepts `K₂`**: `SimpleGraph.countMatroid_indep_iff_runPebbleGame` at `K₂`
and `(k, ℓ) = (2, 3)`, its hypothesis `ℓ < 2k` met. `K₂`'s edge set is independent in the
`(2, 3)`-count matroid, as `K₂` is `(2, 3)`-sparse, so the game's verdict accepts. -/
theorem countMatroid_indep_iff_runPebbleGame_witness :
    (PebbleGame.PartialOrientation.runPebbleGame (⊤ : SimpleGraph (Fin 2)) 2 3
      (by norm_num)).isAccept := by
  rw [← countMatroid_indep_iff_runPebbleGame, countMatroid_indep_iff, fromEdgeSet_edgeSet]
  exact ⟨subset_rfl, top_fin_two_isLaman.isSparse⟩

/-! ### The matroid rows, at the double edge and `k = 2` -/

/-- The double edge, `Graph.banana 0 1 univ` on two vertices and two edges, is `(2, 2)`-sparse:
a nonempty set of its edges spans both vertices and has at most two edges. -/
private theorem banana_isSparse_two_two :
    (Graph.banana (0 : Fin 2) 1 (Set.univ : Set (Fin 2))).IsSparse 2 2 := by
  intro E' _ hne
  have hV : (Graph.banana (0 : Fin 2) 1 (Set.univ : Set (Fin 2))).spanningVerts E' = Set.univ :=
    Set.eq_univ_of_forall fun x ↦ ⟨hne.some, hne.some_mem, by fin_cases x <;> simp⟩
  have hE : E'.ncard ≤ 2 := (Set.ncard_le_card E').trans_eq (Nat.card_fin 2)
  rw [hV, Set.ncard_univ, Nat.card_fin]
  omega

/-- **Tutte–Nash-Williams at the double edge**: `Graph.tutte_nash_williams` at the double edge and
`k = 2`. The double edge is `(2, 2)`-sparse, so it is the union of two edge-disjoint forests. -/
theorem tutte_nash_williams_witness :
    (Graph.banana (0 : Fin 2) 1 (Set.univ : Set (Fin 2))).IsForestPacking 2 :=
  Graph.tutte_nash_williams.mpr banana_isSparse_two_two

open Matroid in
/-- **Whiteley's identification at the double edge**:
`Graph.kFrameMatroid_eq_unionPow_cycleMatroid` at the double edge and `k = 2`, and what it gives
there. By the identification, the two parallel bars are independent in the generic `2`-frame
matroid, as they are in the two-fold union of the cycle matroid: the double edge is
`(2, 2)`-sparse. -/
theorem kFrameMatroid_eq_unionPow_cycleMatroid_witness :
    (Graph.banana (0 : Fin 2) 1 (Set.univ : Set (Fin 2))).kFrameMatroid 2 =
        (Matroid.Union fun _ : Fin 2 ↦
          (Graph.banana (0 : Fin 2) 1 (Set.univ : Set (Fin 2))).cycleMatroid) ↾
          E(Graph.banana (0 : Fin 2) 1 (Set.univ : Set (Fin 2))) ∧
      ((Graph.banana (0 : Fin 2) 1 (Set.univ : Set (Fin 2))).kFrameMatroid 2).Indep
        E(Graph.banana (0 : Fin 2) 1 (Set.univ : Set (Fin 2))) := by
  refine ⟨Graph.kFrameMatroid_eq_unionPow_cycleMatroid, ?_⟩
  rw [Graph.kFrameMatroid_eq_unionPow_cycleMatroid, Matroid.restrict_indep_iff,
    Graph.unionPow_cycleMatroid_indep_iff_isSparse_restrict subset_rfl, Graph.restrict_self]
  exact ⟨banana_isSparse_two_two, subset_rfl⟩

end CombinatorialRigidity
