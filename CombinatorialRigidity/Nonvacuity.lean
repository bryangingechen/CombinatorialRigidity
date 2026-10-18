/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.BodyBar.BodyHinge
import CombinatorialRigidity.BodyBar.GenericLift
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
`PHASE-BOUNDARIES.md`'s close checklist asks of a main result, named after its row with
`_witness` (`tay_witness`'s, whose name already ends so, is `tay_witness_nonvacuous`).
`molecular_conjecture_witness` (`Molecular/AlgebraicInduction/Nonvacuity.lean`) is the one for
`molecular_conjecture`.

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
* `tay_witness_nonvacuous`: Tay's body-bar theorem at the triple edge (two bodies, three bars). It
  is `(3, 3)`-tight, the least such multigraph with a bar (a `(3, 3)`-tight one has `3|V| - 3`
  bars), so it carries an isostatic body-bar framework in the plane.
* `body_hinge_tay_witness`: Tay and Whiteley's body-hinge theorem at the triangle `K₃` (three
  bodies, pairwise hinged), whose 2-fold edge multiplication is `(3, 3)`-tight; on two bodies none
  is (`2|E| + 3 = 6` has no solution). So `K₃` carries an isostatic framework with two bars at
  each hinge.
* `isIndependent_and_isInfinitesimallyRigid_ofEndpoints_iff_witness`: Tay's theorem at a generic
  endpoint assignment, at the triple edge: an orientation and an endpoint assignment generic for
  row independence (a non-root of the abundance polynomial), at which the realization placing each
  bar between its endpoints is isostatic.

The body-bar and body-hinge rows are taken in the plane, `n = 2`, where `d = bodyBarDim 2 = 3` and
each hinge is two bars (`bodyHingeMult 2 = 2`): at `n = 1` a hinge carries no bar
(`bodyHingeMult 1 = 0`) and a body's one motion is a translation (`bodyBarDim 1 = 1`).
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

/-- The `m`-fold edge, `Graph.banana 0 1 univ` on two vertices and `m` parallel edges, is
`(k, ℓ)`-sparse when `m + ℓ ≤ 2k`: a nonempty set of its edges spans both vertices and has at most
`m` edges. So the double edge is `(2, 2)`-sparse, and the triple edge `(3, 3)`-sparse. -/
private theorem banana_isSparse {m k ℓ : ℕ} (h : m + ℓ ≤ 2 * k) :
    (Graph.banana (0 : Fin 2) 1 (Set.univ : Set (Fin m))).IsSparse k ℓ := by
  intro E' _ hne
  have hV : (Graph.banana (0 : Fin 2) 1 (Set.univ : Set (Fin m))).spanningVerts E' = Set.univ :=
    Set.eq_univ_of_forall fun x ↦ ⟨hne.some, hne.some_mem, by fin_cases x <;> simp⟩
  have hE : E'.ncard ≤ m := (Set.ncard_le_card E').trans_eq (Nat.card_fin m)
  rw [hV, Set.ncard_univ, Nat.card_fin]
  omega

/-- **Tutte–Nash-Williams at the double edge**: `Graph.tutte_nash_williams` at the double edge and
`k = 2`. The double edge is `(2, 2)`-sparse, so it is the union of two edge-disjoint forests. -/
theorem tutte_nash_williams_witness :
    (Graph.banana (0 : Fin 2) 1 (Set.univ : Set (Fin 2))).IsForestPacking 2 :=
  Graph.tutte_nash_williams.mpr (banana_isSparse (by norm_num))

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
  exact ⟨banana_isSparse (by norm_num), subset_rfl⟩

/-! ### The body-bar and body-hinge rows, in the plane -/

/-- The triple edge, `Graph.banana 0 1 univ` on two vertices and three edges, is `(3, 3)`-tight:
it is `(3, 3)`-sparse, and `3 + 3 = 3 · 2`. -/
private theorem banana_isTight_three_three :
    (Graph.banana (0 : Fin 2) 1 (Set.univ : Set (Fin 3))).IsTight 3 3 :=
  ⟨banana_isSparse (by norm_num), by simp⟩

/-- **Tay's theorem at the triple edge**: `Graph.BodyBarFramework.tay_witness` in the plane
(`n = 2`, `d = 3`) at the triple edge, from its `(3, 3)`-tightness. Two bodies joined by three bars
carry an isostatic body-bar framework: independent and infinitesimally rigid. -/
theorem tay_witness_nonvacuous :
    ∃ (F : Graph.BodyBarFramework 2 (Fin 2) (Fin 3))
      (_ : F.graph = Graph.banana (0 : Fin 2) 1 (Set.univ : Set (Fin 3)))
      (D : Graph.orientation F.graph), F.IsIndependent D ∧ F.IsInfinitesimallyRigid D :=
  (Graph.BodyBarFramework.tay_witness _).2.mpr banana_isTight_three_three

/-- The triangle `K₃`, as a multigraph, has a `(3, 3)`-tight 2-fold edge multiplication: six bars
on three vertices, `6 + 3 = 3 · 3`, and a nonempty set of bars missing a vertex spans the other two
and holds at most the two copies of the edge between them, `2 + 3 ≤ 3 · 2`. -/
private theorem ofSimpleGraph_top_edgeMultiply_isTight :
    ((Graph.OfSimpleGraph (⊤ : SimpleGraph (Fin 3))).edgeMultiply 2).IsTight 3 3 := by
  have hK : E(Graph.OfSimpleGraph (⊤ : SimpleGraph (Fin 3))).ncard = 3 := by
    rw [Graph.edgeSet_OfSimpleGraph, Set.ncard_eq_toFinset_card']
    decide
  refine ⟨fun E' hE' hne ↦ ?_, ?_⟩
  · by_cases hS : ∀ x, x ∈ ((Graph.OfSimpleGraph ⊤).edgeMultiply 2).spanningVerts E'
    · have hE : E'.ncard ≤ 6 := (Set.ncard_le_ncard hE').trans
        (by rw [Graph.edgeMultiply_edgeSet_ncard, hK])
      rw [Set.eq_univ_of_forall hS, Set.ncard_univ, Nat.card_fin]
      omega
    · -- `E'` misses a vertex `w`: its bars are copies of the one edge avoiding `w`.
      obtain ⟨w, hw⟩ := not_forall.mp hS
      have hsub : E' ⊆ {p : Sym2 (Fin 3) × Fin 2 | ¬p.1.IsDiag ∧ w ∉ p.1} := by
        intro p hp
        obtain ⟨x, y, hxy, hp1⟩ := hE' hp
        refine ⟨hp1 ▸ Sym2.mk_isDiag_iff.not.mpr hxy, fun hwp ↦ hw ⟨p, hp, ?_⟩⟩
        rw [← hp1, Sym2.mem_iff] at hwp
        rcases hwp with rfl | rfl
        · exact ⟨y, hxy, hp1⟩
        · exact ⟨x, Ne.symm hxy, Sym2.eq_swap.trans hp1⟩
      have hE : E'.ncard ≤ 2 := (Set.ncard_le_ncard hsub).trans
        (by fin_cases w <;> (rw [Set.ncard_eq_toFinset_card']; decide))
      -- A bar of `E'` spans its two ends.
      obtain ⟨p, hp⟩ := hne
      obtain ⟨x, y, hxy, hp1⟩ := hE' hp
      have hV : ({x, y} : Set (Fin 3)) ⊆
          ((Graph.OfSimpleGraph ⊤).edgeMultiply 2).spanningVerts E' := by
        rintro z (rfl | rfl)
        · exact ⟨p, hp, y, hxy, hp1⟩
        · exact ⟨p, hp, x, Ne.symm hxy, Sym2.eq_swap.trans hp1⟩
      have := (Set.ncard_pair hxy).symm.trans_le (Set.ncard_le_ncard hV)
      omega
  · rw [Graph.edgeMultiply_edgeSet_ncard, hK]
    simp

/-- **Tay and Whiteley's body-hinge theorem at the triangle**:
`Graph.BodyHingeFramework.body_hinge_tay` in the plane (`n = 2`, two bars at each hinge) at `K₃`,
from the `(3, 3)`-tightness of its 2-fold edge multiplication. Three bodies, each two joined by a
hinge of two bars, carry an isostatic framework: independent and infinitesimally rigid. -/
theorem body_hinge_tay_witness :
    ∃ (F : Graph.BodyHingeFramework 2 (Fin 3) (Sym2 (Fin 3)))
      (_ : F.graph = Graph.OfSimpleGraph (⊤ : SimpleGraph (Fin 3)))
      (D : Graph.orientation (F.graph.edgeMultiply (Graph.bodyHingeMult 2))),
        F.IsIndependent D ∧ F.IsInfinitesimallyRigid D :=
  (Graph.BodyHingeFramework.body_hinge_tay _).2.mpr ofSimpleGraph_top_edgeMultiply_isTight

open Graph.BodyBarFramework in
/-- **Tay's theorem at a generic endpoint assignment, at the triple edge**:
`Graph.BodyBarFramework.isIndependent_and_isInfinitesimallyRigid_ofEndpoints_iff` in the plane at
the triple edge. It has an orientation `D` (`Graph.orientation_nonempty`) and an endpoint
assignment `q` generic for `D` (`exists_isGenericEndpoints`, a non-root of the polynomial of
`exists_isGenericEndpoints_abundance`); as the triple edge is `(3, 3)`-tight, the realization
placing each bar between its endpoints under `q` is isostatic. -/
theorem isIndependent_and_isInfinitesimallyRigid_ofEndpoints_iff_witness :
    ∃ (D : Graph.orientation (Graph.banana (0 : Fin 2) 1 (Set.univ : Set (Fin 3))))
      (q : Fin 3 × Bool × Fin 2 → ℝ), IsGenericEndpoints _ D q ∧
        (ofEndpoints _ q).IsIndependent D ∧ (ofEndpoints _ q).IsInfinitesimallyRigid D := by
  obtain ⟨D⟩ := Graph.orientation_nonempty
    (G := Graph.banana (0 : Fin 2) 1 (Set.univ : Set (Fin 3)))
  obtain ⟨q, hq⟩ := exists_isGenericEndpoints (n := 2) _ D
  exact ⟨D, q, hq,
    (isIndependent_and_isInfinitesimallyRigid_ofEndpoints_iff hq).mpr banana_isTight_three_three⟩

end CombinatorialRigidity
