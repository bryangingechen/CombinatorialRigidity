/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.BodyBar.GenericLift
public import CombinatorialRigidity.JacobsDegreeOne
public import CombinatorialRigidity.JacobsTheorem
public import CombinatorialRigidity.LamanTheorem
public import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.Statements
public import CombinatorialRigidity.PebbleGame.Correctness
public import Mathlib.Combinatorics.SimpleGraph.Star

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
* `theorem_55_minimalKDof_gen_witness`: Katoh and Tanigawa's Theorem 5.5 at the single edge, a
  minimal `1`-dof-graph, its fresh-edge supply from a label headroom. The single edge is simple, so
  it has a panel realization with nonparallel panels and one with a nondegenerate hinge, at rank
  `3 · (2 - 1) - 1 = 2`.
* `molecular_conjecture_multigraph_witness`: Tay and Whiteley's molecular conjecture, proved by
  Katoh and Tanigawa, for multigraphs, at the double edge, which is `0`-dof. The multigraph
  Theorem 5.6 gives it a rigid hinge-coplanar panel realization, so by the equivalence it has a
  rigid body-hinge realization with nondegenerate hinges.
* `pencil_realization_theorem_witness`: the pencil realization theorem at the star `K₁,₃`, the
  least simple graph with a body of degree three, the least degree at which the pencil condition
  (a body's hinges pass through one point) is not automatic. The star is simple, so it has a pencil
  realization at the deficiency rank whose adjacent bodies have distinct points.
* `pencilPair_of_nonempty_witness`: the pencil realization theorem's general form at the same star
  on four of five bodies, a graph that is not spanning, with the same conclusion.
* `molecule_rank_formula_witness`: Jackson and Jordán's molecule rank formula (Katoh and
  Tanigawa's Corollary 5.7) at the triangle `K₃`, the least simple graph of minimum degree two.
  Its multigraph is a triangle, `0`-dof, so the square `K₃² = K₃` has generic rank `3 · 3 - 6 = 3`.
* `jacobs_witness`: Jacobs' conjecture (Jackson and Jordán's Theorem 5.4) at the path `P₃`, the
  least graph whose square has an edge it lacks. Its square, the triangle, meets the
  three-dimensional Laman count, so its edges are independent in the generic rigidity matroid.
* `degree_one_rank_witness`: Jackson and Jordán's degree-one rank formula at the paw (a triangle
  with a pendant edge), the least connected non-tree whose core is not the whole graph. Its core
  is the triangle, so the pendant vertex adds `2 + 1 = 3` to the rank of the square.
* `molecule_generic_square_packing_witness`: Jackson and Jordán's generic rigidity of squares from
  six spanning trees at `K₃`, the least simple graph on more than one vertex whose multiplied graph
  `5·G` has six edge-disjoint spanning trees. The six trees are paths of length two, exhibited, and
  so is a generic placement, at which the triangle is infinitesimally rigid in 3-space.

The body-bar and body-hinge rows are taken in the plane, `n = 2`, where `d = bodyBarDim 2 = 3` and
each hinge is two bars (`bodyHingeMult 2 = 2`): at `n = 1` a hinge carries no bar
(`bodyHingeMult 1 = 0`) and a body's one motion is a translation (`bodyBarDim 1 = 1`). So are
Theorem 5.5 and the molecular conjecture for multigraphs, whose least dimension is `n = 2` (a panel
is a line and a hinge a point); the pencil rows are stated at `n = 3`, and the molecule and Jacobs
rows, about the square of a graph, in 3-space.
-/

@[expose] public section

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


/-! ### The molecular rows -/

section

open Molecular

/-- The single edge on two bodies is a minimal `1`-dof-graph when `D = bodyBarDim n ≥ 2`. A
partition separating its two bodies has `D`-deficiency `D · 1 - (D - 1) · 1 = 1` and the one-part
partition `0`, so `def(G̃) = 1`. A base of `M(G̃)` then has `D(2 - 1) - 1 = D - 1 ≥ 1` elements
(`Graph.isBase_ncard_add_deficiency_eq`), each a copy of the one edge, so it meets that edge's
copies. -/
private theorem singleEdge_isMinimalKDof_one {β : Type*} [Finite β] [DecidableEq β] {n : ℕ}
    (hD : 2 ≤ Graph.bodyBarDim n) (e : β) :
    (Graph.singleEdge (0 : Fin 2) 1 e).IsMinimalKDof n 1 := by
  classical
  have hpd : ∀ f : Fin 2 → Fin 2,
      (Graph.singleEdge (0 : Fin 2) 1 e).partitionDef n f = if f 0 = f 1 then 0 else 1 := by
    intro f
    have hcross : (Graph.singleEdge (0 : Fin 2) 1 e).crossingEdges f =
        if f 0 = f 1 then ∅ else {e} := by
      ext e'
      simp only [Graph.crossingEdges, Graph.edgeSet_singleEdge, Graph.singleEdge_isLink]
      split_ifs with h <;> simp [h, eq_comm]
    have hparts : (Graph.singleEdge (0 : Fin 2) 1 e).numParts f = if f 0 = f 1 then 1 else 2 := by
      rw [Graph.numParts, Graph.vertexSet_singleEdge, Set.image_pair]
      split_ifs with h
      · simp [h]
      · exact Set.ncard_pair h
    rw [Graph.partitionDef, hcross, hparts]
    split_ifs <;> simp
  have hdef : (Graph.singleEdge (0 : Fin 2) 1 e).IsKDof n 1 := by
    have : Nonempty (Fin 2 → Fin 2) := ⟨id⟩
    refine le_antisymm (ciSup_le fun f ↦ ?_) ?_
    · rw [hpd]
      split_ifs <;> simp
    · simpa [hpd] using (Graph.singleEdge (0 : Fin 2) 1 e).partitionDef_le_deficiency n id
  refine ⟨hdef, fun B hB e' he' ↦ ?_⟩
  have hcard := (Graph.singleEdge (0 : Fin 2) 1 e).isBase_ncard_add_deficiency_eq n (by omega)
    ⟨0, by simp⟩ hB
  rw [hdef.deficiency_eq, Graph.vertexSet_singleEdge, Set.ncard_pair (by decide)] at hcard
  obtain ⟨p, hp⟩ : B.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  have hpE : p.1 ∈ E(Graph.singleEdge (0 : Fin 2) 1 e) := hB.subset_ground hp
  rw [Graph.edgeSet_singleEdge, Set.mem_singleton_iff] at hpE he'
  exact ⟨p, hp, hpE.trans he'.symm⟩

/-- **Katoh and Tanigawa's Theorem 5.5 at the single edge, in the plane**:
`Molecular.PanelHingeFramework.theorem_55_minimalKDof_gen` at `n = 2` and grade `k = 1`
(`bodyBarDim 2 = screwDim 1 = 3`), at the single edge on two bodies, a minimal `1`-dof-graph. Its
fresh-edge supply `hfresh` comes from the label headroom `3 · (2 - 1) < 4`
(`Graph.freshEdgeSupply_of_card_lt`), the bound `molecular_conjecture_witness` meets at `n = 3`.
The single edge is simple, so both sides of the conditioned pair hold: a panel-hinge realization
whose two panels are nonparallel, and a panel realization whose hinge is nondegenerate and lies in
both panels, each with rigidity matrix of rank `3 · (2 - 1) - 1 = 2`. -/
theorem theorem_55_minimalKDof_gen_witness :
    PanelHingeFramework.HasNonparallelFullRankRealization ℝ 1 2
        (Graph.singleEdge (0 : Fin 2) 1 (0 : Fin 4)) ∧
      HasPanelRealization ℝ 1 2 (Graph.singleEdge (0 : Fin 2) 1 (0 : Fin 4)) := by
  obtain ⟨hgen, hpanel⟩ := PanelHingeFramework.theorem_55_minimalKDof_gen (K := ℝ) (k := 1)
    (n := 2) le_rfl
    (Graph.bodyBarDim_eq_screwDim_sub_one (by norm_num))
    (Graph.freshEdgeSupply_of_card_lt (by decide) (by simp only [Nat.card_fin]; decide))
    (Graph.singleEdge (0 : Fin 2) 1 (0 : Fin 4)) (singleEdge_isMinimalKDof_one (by decide) 0)
    (by rw [Graph.vertexSet_singleEdge]; exact (Set.ncard_pair (by decide)).ge)
  exact ⟨hgen (Graph.singleEdge_simple (by decide) 0), hpanel⟩

/-- **The molecular conjecture for multigraphs at the double edge, in the plane**:
`Molecular.molecular_conjecture_multigraph` at `n = 2` (a panel is a line and a hinge a point) at
the double edge, two bodies joined by two parallel hinges, which the simple-graph form
`molecular_conjecture` excludes; the label headroom is `3 · (2 - 1) < 4`. The double edge
is `0`-dof (`Graph.isKDof_zero_of_parallel_pair`), so the multigraph Theorem 5.6
(`theorem_55_6_multigraph_gen`) gives it a hinge-coplanar panel realization at full rank, which is
infinitesimally rigid (`BodyHingeFramework.rankHypothesis_zero_iff`). By the equivalence, the
double edge has an infinitesimally rigid body-hinge realization with every hinge nondegenerate. -/
theorem molecular_conjecture_multigraph_witness :
    ∃ F : BodyHingeFramework ℝ 1 (Fin 2) (Fin 4),
      F.graph = Graph.banana (0 : Fin 2) 1 ({0, 1} : Set (Fin 4)) ∧
        (∀ e, F.supportExtensor e ≠ 0) ∧ F.IsInfinitesimallyRigid := by
  have hspan : V(Graph.banana (0 : Fin 2) 1 ({0, 1} : Set (Fin 4))) = Set.univ :=
    Set.eq_univ_of_forall fun x ↦ by fin_cases x <;> simp
  have hcard : Graph.bodyBarDim 2 * (Nat.card (Fin 2) - 1) < Nat.card (Fin 4) := by
    simp only [Nat.card_fin]; decide
  have hdef : (Graph.banana (0 : Fin 2) 1 ({0, 1} : Set (Fin 4))).deficiency 2 = 0 :=
    Graph.isKDof_zero_of_parallel_pair (by decide) (x := 0) (y := 1) (e₁ := 0) (e₂ := 1)
      (by decide) (by simp) (by simp) (by decide) (by simp) (by simp)
  obtain ⟨F, normal, hF, hrank⟩ := theorem_55_6_multigraph_gen (K := ℝ) le_rfl hcard _ hspan
  rw [hdef] at hrank
  exact (molecular_conjecture_multigraph le_rfl hcard _ hspan).mpr
    ⟨F, normal, hF, (BodyHingeFramework.rankHypothesis_zero_iff F).mp hrank⟩

/-- The dependency's graph of a simple graph, `Graph.OfSimpleGraph H`, is simple: a link is an
adjacency of `H`, which is irreflexive, and its edge is the pair of its ends. -/
private theorem ofSimpleGraph_simple {V : Type*} (H : SimpleGraph V) :
    (Graph.OfSimpleGraph H).Simple where
  not_isLoopAt _ _ h := H.irrefl h.1
  eq_of_isLink _ _ _ _ he hf := he.2.symm.trans hf.2

/-- **The pencil realization theorem at the star `K₁,₃`**: `Molecular.pencil_realization_theorem`
at the star on four bodies centred at `0`, which is spanning. At a body of degree at most two the
pencil condition (the body's hinges pass through one point of its panel) is automatic, two
coplanar hinges always meeting (`exists_concurrency_point_of_extensorInPanel_pair`); the centre has
degree three, and `K₁,₃` is the least simple graph with such a body. The star is simple, so the
conditioned pair gives it a pencil realization at the deficiency rank whose adjacent bodies have
distinct points. -/
theorem pencil_realization_theorem_witness :
    HasDistinctPencilRealization ℝ 3 (Graph.OfSimpleGraph (SimpleGraph.starGraph (0 : Fin 4))) :=
  (pencil_realization_theorem _ (Graph.vertexSet_OfSimpleGraph _)).2.1 (ofSimpleGraph_simple _)

/-- **The pencil realization theorem's general form at a graph that is not spanning**:
`Molecular.pencilPair_of_nonempty` at the star `K₁,₃` on four of five bodies (the star centred at
`0` on five bodies, the fifth deleted). The general form asks only for a body, and its rank target
counts the graph's own four bodies. As in `pencil_realization_theorem_witness`, the star gives a
pencil realization at the deficiency rank whose adjacent bodies have distinct points. -/
theorem pencilPair_of_nonempty_witness :
    HasDistinctPencilRealization ℝ 3
      (Graph.OfSimpleGraph (SimpleGraph.starGraph (0 : Fin 5)) - {4}) :=
  have := ofSimpleGraph_simple (SimpleGraph.starGraph (0 : Fin 5))
  (pencilPair_of_nonempty _ ⟨0, by simp⟩).2.1 inferInstance

end

/-! ### The molecule and Jacobs rows, in 3-space -/

/-- The multigraph `K̃₃ = K₃.shadowGraph` of the triangle is a triangle, so it is `0`-dof in
3-space (`Graph.isKDof_zero_of_triangle`, as `bodyBarDim 3 = 6 ≥ 3`). -/
private theorem top_fin_three_shadowGraph_isKDof_zero :
    (⊤ : SimpleGraph (Fin 3)).shadowGraph.IsKDof 3 0 := by
  refine Graph.isKDof_zero_of_triangle (by decide) (x := 0) (y := 1) (z := 2)
    (exy := Sum.inl s(0, 1)) (eyz := Sum.inl s(1, 2)) (exz := Sum.inl s(0, 2))
    (by decide) (by decide) (by decide) ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ?_ ?_
  · rw [shadowGraph_vertexSet]
    ext x
    fin_cases x <;> simp
  · ext e
    rw [Graph.edgeSet_eq_setOfPred_exists_isLink]
    constructor
    · rintro ⟨x, y, hxy, rfl⟩
      fin_cases x <;> fin_cases y <;> simp_all [Sym2.eq_swap]
    · rintro (rfl | rfl | rfl) <;> exact ⟨_, _, by decide, rfl⟩

/-- **Jackson and Jordán's molecule rank formula (Katoh and Tanigawa's Corollary 5.7) at the
triangle**: `SimpleGraph.molecule_rank_formula` at `K₃`, the least simple graph of minimum degree
two, its hypothesis met with equality. `K₃` is its own square, and its multigraph `K̃₃` is a
triangle, which is `0`-dof, so the formula gives `r(K₃²) = 3 · 3 - 6 - 0 = 3`: the triangle is
generically rigid in 3-space. -/
theorem molecule_rank_formula_witness :
    (⊤ : SimpleGraph (Fin 3)).square.genericRank 3 = 3 := by
  have h := molecule_rank_formula (⊤ : SimpleGraph (Fin 3)) fun v ↦ by simp
  rw [top_fin_three_shadowGraph_isKDof_zero.deficiency_eq, Nat.card_fin] at h
  omega

/-- The square of the path on three vertices satisfies the three-dimensional Laman condition: a
set of at least three of its vertices is all three, and spans at most `3 = 3 · 3 - 6` edges. -/
private theorem pathGraph_three_square_isLaman3 : (pathGraph 3).square.IsLaman3 := by
  classical
  intro s hs
  have h1 : s.card ≤ 3 := (Finset.card_le_univ s).trans_eq (Fintype.card_fin 3)
  have h2 : ((pathGraph 3).square.edgesIn ↑s).ncard ≤ 3 := by
    refine (Set.ncard_le_ncard (edgesIn_subset_edgeSet _) (Set.toFinite _)).trans ?_
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
    exact (card_edgeFinset_le_card_choose_two).trans_eq (by simp)
  omega

/-- **Jacobs' conjecture (Jackson and Jordán's Theorem 5.4) at the path on three vertices**:
`SimpleGraph.jacobs` at `P₃`, the least graph whose square has an edge it lacks. Its square, the
triangle, meets the three-dimensional Laman count `|E(X)| + 6 ≤ 3|X|` (with equality at its three
vertices), so by the theorem's converse direction the square's edges are independent in the
3-dimensional generic rigidity matroid. -/
theorem jacobs_witness :
    (genericRigidityMatroid (Fin 3) 3).Indep (pathGraph 3).square.edgeSet :=
  (jacobs _).mpr pathGraph_three_square_isLaman3

/-- **Jackson and Jordán's degree-one rank formula (their Lemma 4.2) at the paw**:
`SimpleGraph.degree_one_rank` at the triangle `0 1 2` with the pendant edge `0 3`, the least
connected graph that is not a tree and whose core is not the whole graph (on three vertices the one
connected non-tree is `K₃`, its own core). Its core is the triangle (`notMem_support_twoCore` at
the pendant vertex `3`, `le_twoCore` for the triangle), whose support misses only `3`, the one
vertex of degree one. So the formula gives `r(G²) = r(K₃²) + 2 · 1 + 1`: the pendant vertex adds
three to the rank of the square. -/
theorem degree_one_rank_witness :
    (fromEdgeSet {s(0, 1), s(0, 2), s(1, 2), s(0, 3)} : SimpleGraph (Fin 4)).square.genericRank 3 =
      (fromEdgeSet {s(0, 1), s(0, 2), s(1, 2)} : SimpleGraph (Fin 4)).square.genericRank 3 + 3 := by
  have hconn : (fromEdgeSet {s(0, 1), s(0, 2), s(1, 2), s(0, 3)} :
      SimpleGraph (Fin 4)).Connected := by
    rw [connected_iff_exists_forall_reachable]
    refine ⟨0, fun w ↦ ?_⟩
    fin_cases w
    · rfl
    all_goals exact Adj.reachable (by decide)
  -- Not a tree: its degrees sum to `8`, so it has four edges on four vertices.
  have hnt : ¬ (fromEdgeSet {s(0, 1), s(0, 2), s(1, 2), s(0, 3)} :
      SimpleGraph (Fin 4)).IsTree := by
    intro h
    have h1 := h.card_edgeFinset
    have h2 := (fromEdgeSet {s(0, 1), s(0, 2), s(1, 2), s(0, 3)} :
      SimpleGraph (Fin 4)).sum_degrees_eq_twice_card_edges
    have h3 : ∑ v, (fromEdgeSet {s(0, 1), s(0, 2), s(1, 2), s(0, 3)} :
        SimpleGraph (Fin 4)).degree v = 8 := by
      decide
    simp only [Fintype.card_fin, ← Set.ncard_coe_finset, coe_edgeFinset] at h1 h2
    omega
  have hcore : (fromEdgeSet {s(0, 1), s(0, 2), s(1, 2), s(0, 3)} : SimpleGraph (Fin 4)).twoCore =
      fromEdgeSet {s(0, 1), s(0, 2), s(1, 2)} := by
    have h3 : (3 : Fin 4) ∉ (fromEdgeSet {s(0, 1), s(0, 2), s(1, 2), s(0, 3)} :
        SimpleGraph (Fin 4)).twoCore.support :=
      notMem_support_twoCore (by rw [Set.ncard_eq_toFinset_card']; decide)
    refine le_antisymm (fun a b hab ↦ ?_) (le_twoCore (fun a b ↦ ?_) fun v _ ↦ ?_)
    · have ha : a ≠ 3 := by rintro rfl; exact h3 ⟨b, hab⟩
      have hb : b ≠ 3 := by rintro rfl; exact h3 ⟨a, hab.symm⟩
      have key : ∀ a b : Fin 4, a ≠ 3 → b ≠ 3 →
          (fromEdgeSet {s(0, 1), s(0, 2), s(1, 2), s(0, 3)} : SimpleGraph (Fin 4)).Adj a b →
            (fromEdgeSet {s(0, 1), s(0, 2), s(1, 2)} : SimpleGraph (Fin 4)).Adj a b := by
        decide
      exact key a b ha hb (twoCore_le _ hab)
    · revert a b
      decide
    · rw [Set.ncard_eq_toFinset_card']
      revert v
      decide
  have hsupp :
      (fromEdgeSet {s(0, 1), s(0, 2), s(1, 2)} : SimpleGraph (Fin 4)).supportᶜ.ncard = 1 := by
    rw [Set.ncard_eq_toFinset_card']
    decide
  have hdeg : {w | (fromEdgeSet {s(0, 1), s(0, 2), s(1, 2), s(0, 3)} :
      SimpleGraph (Fin 4)).degree w = 1}.ncard = 1 := by
    rw [Set.ncard_eq_toFinset_card']
    decide
  have h := degree_one_rank hconn hnt
  rw [hcore, hsupp, hdeg] at h
  omega

/-- The path `a - m - b` in `K₃.shadowGraph.mulTilde 3`, the multiplied graph `5·K₃`: the `c`-th
copy of the edge `s(a, m)`, then the `d`-th copy of `s(m, b)`. -/
private def path3 (a m b : Fin 3) (c d : Fin (Graph.bodyHingeMult 3)) :
    WList (Fin 3)
      ((Sym2 (Fin 3) ⊕ Fin (6 * (Nat.card (Fin 3) - 1) + 1)) × Fin (Graph.bodyHingeMult 3)) :=
  .cons a (Sum.inl s(a, m), c) (.cons m (Sum.inl s(m, b), d) (.nil b))

/-- Six edge-disjoint spanning trees of `5·K₃`, two paths through each vertex `m`: the `k`-th
(`k = 0, 1`) takes, on its edge from `m` to `o`, copy `k` when `m < o` and copy `2 + k` when
`o < m`. So the four paths through an edge take its copies `0` to `3`. -/
private def treeWalk : Fin 6 → WList (Fin 3)
    ((Sym2 (Fin 3) ⊕ Fin (6 * (Nat.card (Fin 3) - 1) + 1)) × Fin (Graph.bodyHingeMult 3)) :=
  ![path3 1 0 2 ⟨0, by decide⟩ ⟨0, by decide⟩, path3 1 0 2 ⟨1, by decide⟩ ⟨1, by decide⟩,
    path3 0 1 2 ⟨2, by decide⟩ ⟨0, by decide⟩, path3 0 1 2 ⟨3, by decide⟩ ⟨1, by decide⟩,
    path3 0 2 1 ⟨2, by decide⟩ ⟨2, by decide⟩, path3 0 2 1 ⟨3, by decide⟩ ⟨3, by decide⟩]

/-- **Jackson and Jordán's generic rigidity of squares from six spanning trees, at the
triangle**: `SimpleGraph.molecule_generic_square_packing` at `K₃`, with its six trees and a generic
placement exhibited. On one vertex the conclusion holds without the trees, and on two no simple
graph has six edge-disjoint spanning trees in `5·G` (it has at most five edges), so `K₃` is the
least input where the hypothesis bites. `5·K₃` has fifteen edges, five copies of each edge of the
triangle, and the six paths of length two of `treeWalk` use twelve of them; a placement generic for
row independence exists (`exists_isGenericPlacement`). So at that placement the triangle, its own
square, is infinitesimally rigid in 3-space. -/
theorem molecule_generic_square_packing_witness :
    ∃ p : Framework (Fin 3) 3, IsGenericPlacement p ∧
      (⊤ : SimpleGraph (Fin 3)).square.IsInfinitesimallyRigid p := by
  have hV : V((⊤ : SimpleGraph (Fin 3)).shadowGraph.mulTilde 3) = Set.univ := rfl
  have hL : ∀ e x y, (⊤ : SimpleGraph (Fin 3)).shadowGraph.IsLink e x y ↔
      x ≠ y ∧ Sum.inl s(x, y) = e := fun _ _ _ ↦ Iff.rfl
  have hP : ∀ i, ((⊤ : SimpleGraph (Fin 3)).shadowGraph.mulTilde 3).IsPath (treeWalk i) := by
    intro i
    fin_cases i <;> simp [treeWalk, path3, Graph.cons_isPath_iff, hV, hL]
  have hspan : ∀ i, (treeWalk i).toGraph ≤s (⊤ : SimpleGraph (Fin 3)).shadowGraph.mulTilde 3 := by
    refine fun i ↦ ⟨(hP i).isWalk.toGraph_le, ?_⟩
    rw [WList.toGraph_vertexSet, hV]
    fin_cases i <;> (ext x; fin_cases x <;> simp [treeWalk, path3])
  have hdisj : Pairwise (Function.onFun Disjoint fun i ↦ E((treeWalk i).toGraph)) := by
    intro i j hij
    simp only [Function.onFun, WList.toGraph_edgeSet]
    fin_cases i <;> fin_cases j <;> simp_all [treeWalk, path3]
  obtain ⟨p, hp⟩ := exists_isGenericPlacement (V := Fin 3) 3
  exact ⟨p, hp, molecule_generic_square_packing _ hspan
    (fun i ↦ ⟨(hP i).toGraph_isForest, (hP i).isWalk.toGraph_connected⟩) hdisj hp⟩

end CombinatorialRigidity
