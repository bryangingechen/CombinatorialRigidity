/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Arms
public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Coverage

/-!
# The reduction on all multigraphs, in every dimension

The theorem that assembles the reduction in every dimension
(`sec:pencil-d-reduction`, `blueprint/src/chapter/pencil-d.tex`): over an infinite field and in
every dimension `d = m + 2 ≥ 3`, every multigraph with a body has a pencil realization at the
deficiency rank (`HasGradedPencilRealization`), and an adjacent-distinct one
(`HasGradedDistinctPencilRealization`) when it is simple. The proof is the induction of
`Graph.pencil_reduction` (`thm:pencil-reduction`), with the cases at a loop, on at most two bodies
and at a cut edge and at parallel edges from `Grade/Arms.lean`, and at a simple
two-edge-connected multigraph from the distinct statement
(`Graph.hasGradedDistinctPencilRealization_of_twoEdgeConnected`, `Grade/Coverage.lean`). At
`d = 3` these are `hasPencilRealization_of_not_simple` and `pencilPair_of_X0`
(`Pencil/X0.lean`), with the assembly of `pencilPair_of_arms` (`Pencil/Pair2.lean`).

## Main results

* `Graph.graded_pencil_realization_theorem`: `thm:pencil-d-realization-theorem`.
-/

@[expose] public section

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

/-! ## The theorem -/

/-- **Pencil realizations at the deficiency rank, in every dimension**
(`thm:pencil-d-realization-theorem`): over an infinite field and in dimension `d = m + 2 ≥ 3`,
every multigraph with at least one body has a pencil realization at the deficiency rank
(`HasGradedPencilRealization`), and an adjacent-distinct one
(`HasGradedDistinctPencilRealization`) when it is simple. `Graph.pencil_reduction` at
`n = m + 2` (`6 ≤ D` by `Graph.six_le_bodyBarDim`) applies to the conjunction: at a loop by
`hasGradedPencilRealization_of_isLoopAt` (a graph with a loop is not simple); on at most two
bodies by `hasGradedPencilRealization_of_ncard_le_two` and its distinct form; and on at least three
bodies, whether a proper rigid subgraph or a body of degree two is present or not, by the cut case
(`hasGradedPencilRealization_of_cutEdges` and its distinct form, at a cut that `¬ TwoEdgeConnected`
gives, whose sides are simple when `G` is), by the distinct statement at a simple two-edge-connected
`G` (`Graph.hasGradedDistinctPencilRealization_of_twoEdgeConnected`), or by
`hasGradedPencilRealization_of_not_simple`. -/
theorem _root_.Graph.graded_pencil_realization_theorem [Infinite K] [Finite α] [Finite β]
    {m : ℕ} (hm : 1 ≤ m) {G : Graph α β} (hne : V(G).Nonempty) :
    HasGradedPencilRealization K (m + 1) (m + 2) G ∧
      (G.Simple → HasGradedDistinctPencilRealization K (m + 1) (m + 2) G) := by
  classical
  set P : Graph α β → Prop := fun G => HasGradedPencilRealization K (m + 1) (m + 2) G ∧
      (G.Simple → HasGradedDistinctPencilRealization K (m + 1) (m + 2) G)
  -- the cases at three bodies or more: a cut, the distinct statement, or parallel edges
  have hthree : ∀ G : Graph α β, G.Loopless → 3 ≤ V(G).ncard →
      (∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard → P G') → P G := by
    intro G hloop hV IH
    by_cases htec : G.TwoEdgeConnected
    · by_cases hS : G.Simple
      · have hd :=
          Graph.hasGradedDistinctPencilRealization_of_twoEdgeConnected (K := K) hS hV htec hm
        obtain ⟨F, normal, plane, h, -, hr⟩ := id hd
        exact ⟨⟨F, normal, plane, h, hr⟩, fun _ => hd⟩
      · exact ⟨hasGradedPencilRealization_of_not_simple G hloop hV hS
          fun G' h1 h2 => (IH G' h1 h2).1, fun h => absurd h hS⟩
    · simp only [Graph.TwoEdgeConnected, not_forall, not_le, exists_prop] at htec
      obtain ⟨V₁, hne₁, hssub, hcut⟩ := htec
      have hcut' : (G.cutEdges V₁).ncard ≤ 1 := Nat.lt_succ_iff.mp hcut
      have hlt₁ : V(G.induce V₁).ncard < V(G).ncard := Set.ncard_lt_ncard hssub (Set.toFinite _)
      have hne₂ : (V(G) \ V₁).Nonempty := Set.nonempty_of_ssubset hssub
      have hlt₂ : V(G.induce (V(G) \ V₁)).ncard < V(G).ncard := by
        have hVcard : V₁.ncard + (V(G) \ V₁).ncard = V(G).ncard := by
          rw [← Set.ncard_union_eq Set.disjoint_sdiff_right (Set.toFinite V₁) (Set.toFinite _),
            Set.union_sdiff_cancel hssub.subset]
        have := hne₁.ncard_pos
        change (V(G) \ V₁).ncard < _
        omega
      obtain ⟨h₁, hd₁⟩ := IH _ hne₁ hlt₁
      obtain ⟨h₂, hd₂⟩ := IH _ hne₂ hlt₂
      exact ⟨hasGradedPencilRealization_of_cutEdges hssub hne₁ hcut' h₁ h₂, fun hS =>
        hasGradedDistinctPencilRealization_of_cutEdges hssub hne₁ hcut'
          (hd₁ (hS.mono (Graph.induce_le hssub.subset)))
          (hd₂ (hS.mono (Graph.induce_le Set.sdiff_subset)))⟩
  refine Graph.pencil_reduction (n := m + 2) (P := P) (Graph.six_le_bodyBarDim (by omega))
    ?_ ?_ (fun G hloop hV _ IH => hthree G hloop hV IH)
    (fun G hloop hV _ IH => hthree G hloop hV IH)
    (fun G hloop hV _ _ _ IH => hthree G hloop hV IH) G hne
  · -- a loop
    rintro G ⟨e, x, hloopAt⟩ IH
    refine ⟨hasGradedPencilRealization_of_isLoopAt hloopAt
      (IH (G ＼ ({e} : Set β)) ?_ (Or.inr ⟨?_, ?_⟩)).1, fun hS => ?_⟩
    · rw [Graph.vertexSet_deleteEdges]; exact ⟨x, hloopAt.left_mem⟩
    · rw [Graph.vertexSet_deleteEdges]
    · rw [Graph.edgeSet_deleteEdges]
      exact Set.ncard_sdiff_singleton_lt_of_mem hloopAt.edge_mem
    · exact absurd hloopAt (hS.toLoopless.not_isLoopAt e x)
  · -- at most two bodies
    intro G hloop hne hV2
    exact ⟨hasGradedPencilRealization_of_ncard_le_two hloop hne hV2,
      fun hS => hasGradedDistinctPencilRealization_of_ncard_le_two hS hne hV2⟩

end CombinatorialRigidity.Molecular
