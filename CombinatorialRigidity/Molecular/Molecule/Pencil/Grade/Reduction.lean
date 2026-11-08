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

The induction over all multigraphs (`Graph.pencil_reduction`, `thm:pencil-reduction`), on five
structural cases: a loop; at most two vertices; loopless and not two-edge-connected;
two-edge-connected and not simple; simple and two-edge-connected. Then the theorem that assembles
it in every dimension (`sec:pencil-d-reduction`, `blueprint/src/chapter/pencil-d.tex`): over an
infinite field and in every dimension `d = m + 2 ≥ 3`, every multigraph with a body has a pencil
realization at the deficiency rank (`HasGradedPencilRealization`), and an adjacent-distinct one
(`HasGradedDistinctPencilRealization`) when it is simple. The cases at a loop, on at most two
bodies, at a cut edge and at parallel edges are from `Grade/Arms.lean`; the case of a simple
two-edge-connected multigraph is an adjacent-distinct realization of the whole multigraph
(`Graph.hasGradedDistinctPencilRealization_of_twoEdgeConnected`, `Grade/Coverage.lean`), which
takes no induction hypothesis. At `d = 3` the theorem gives the first two conjuncts of the
conditioned pair, through `Graph.graded_pencil_conditioned_pair` (`pencilPair_of_nonempty`,
`MainComponent/Statements.lean`).

## Main results

* `Graph.pencil_reduction`: `thm:pencil-reduction`.
* `Graph.graded_pencil_realization_theorem`: `thm:pencil-d-realization-theorem`.
-/

@[expose] public section

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

/-! ## The reduction on all multigraphs (`thm:pencil-reduction`) -/

/-- **Reduction on all multigraphs** (`thm:pencil-reduction`): let a property `P` of multigraphs
hold of a nonempty multigraph `G` in each of five cases:

* `hloop`: `G` has a loop, and `P` holds of every nonempty `G'` smaller in the lexicographic order
  of `(|V(G')|, |E(G')|)`; deleting the loop keeps `|V(G)|` and lowers `|E(G)|`, and this is the
  only case in which the number of vertices stays;
* `hbase`: `G` is loopless with at most two vertices;
* `hcut`: `G` is loopless with at least three vertices and not `2`-edge-connected, and `P` holds
  of every nonempty multigraph with fewer vertices than `G`;
* `hparallel`: `G` is loopless, `2`-edge-connected and not simple, with at least three vertices,
  and `P` holds of every nonempty multigraph with fewer vertices than `G`;
* `hsimple`: `G` is simple and `2`-edge-connected, with at least three vertices, and nothing is
  assumed of smaller multigraphs.

Then `P` holds of every nonempty multigraph. The proof is an induction on `|V(G)|` and, for a fixed
number of vertices, on `|E(G)|`. The cases are structural: none asks for a proper rigid subgraph or
a vertex of degree two. In the pencil realization theorem this induction plays only the role of the
outer induction of Katoh and Tanigawa's Theorem 4.9 (2011, pp. 666–667): the contraction of a
proper rigid subgraph and the splitting off at a vertex of degree two have their counterparts in
the main-component induction (`sec:main-component-coverage`), which takes a simple
two-edge-connected multigraph whole. -/
theorem _root_.Graph.pencil_reduction {P : Graph α β → Prop}
    (hloop : ∀ G : Graph α β, (∃ e x, G.IsLoopAt e x) →
      (∀ G' : Graph α β, V(G').Nonempty →
        V(G').ncard < V(G).ncard ∨
          (V(G').ncard = V(G).ncard ∧ E(G').ncard < E(G).ncard) → P G') → P G)
    (hbase : ∀ G : Graph α β, G.Loopless → V(G).Nonempty → V(G).ncard ≤ 2 → P G)
    (hcut : ∀ G : Graph α β, G.Loopless → 3 ≤ V(G).ncard → ¬ G.TwoEdgeConnected →
      (∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard → P G') → P G)
    (hparallel : ∀ G : Graph α β, G.Loopless → 3 ≤ V(G).ncard → G.TwoEdgeConnected →
      ¬ G.Simple →
      (∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard → P G') → P G)
    (hsimple : ∀ G : Graph α β, G.Simple → 3 ≤ V(G).ncard → G.TwoEdgeConnected → P G) :
    ∀ G : Graph α β, V(G).Nonempty → P G := by
  classical
  -- Strong induction on the lexicographic measure `(|V(G)|, |E(G)|)`: outer on `|V(G)|`,
  -- inner on `|E(G)|` within each fixed vertex count.
  suffices key : ∀ N : ℕ, ∀ M : ℕ, ∀ G : Graph α β, V(G).ncard = N → E(G).ncard = M →
      V(G).Nonempty → P G by
    intro G hne
    exact key _ _ G rfl rfl hne
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IHV =>
  intro M
  induction M using Nat.strong_induction_on with
  | _ M IHE =>
  intro G hVG hEG hne
  -- The lex-smaller IH, in the shape `hloop` wants, plus its `|V|`-only specialization.
  have IHlt : ∀ G' : Graph α β, V(G').Nonempty →
      V(G').ncard < V(G).ncard ∨ (V(G').ncard = V(G).ncard ∧ E(G').ncard < E(G).ncard) →
      P G' := by
    rw [hVG, hEG]
    rintro G' hne' (hlt | ⟨heq, hlt⟩)
    · exact IHV _ hlt _ G' rfl rfl hne'
    · exact IHE _ hlt G' heq rfl hne'
  have IHV' : ∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard → P G' :=
    fun G' hne' hlt => IHlt G' hne' (Or.inl hlt)
  by_cases hloopEx : ∃ e x, G.IsLoopAt e x
  · exact hloop G hloopEx IHlt
  · push Not at hloopEx
    have hlp : G.Loopless := (Graph.loopless_iff G).mpr hloopEx
    by_cases hV2 : V(G).ncard ≤ 2
    · exact hbase G hlp hne hV2
    · have hV3 : 3 ≤ V(G).ncard := by omega
      by_cases htec : G.TwoEdgeConnected
      · by_cases hS : G.Simple
        · exact hsimple G hS hV3 htec
        · exact hparallel G hlp hV3 htec hS IHV'
      · exact hcut G hlp hV3 htec IHV'

/-! ## The theorem -/

/-- **Pencil realizations at the deficiency rank, in every dimension**
(`thm:pencil-d-realization-theorem`): over an infinite field and in dimension `d = m + 2 ≥ 3`,
every multigraph with at least one body has a pencil realization at the deficiency rank
(`HasGradedPencilRealization`), and an adjacent-distinct one
(`HasGradedDistinctPencilRealization`) when it is simple. `Graph.pencil_reduction` applies to the
conjunction: at a loop by `hasGradedPencilRealization_of_isLoopAt` (a graph with a loop is not
simple); on at most two bodies by `hasGradedPencilRealization_of_ncard_le_two` and its distinct
form; at a cut by `hasGradedPencilRealization_of_cutEdges` and its distinct form, at the cut that
`¬ TwoEdgeConnected` gives, whose sides are simple when `G` is; at parallel edges by
`hasGradedPencilRealization_of_not_simple`; and at a simple two-edge-connected `G` by the distinct
statement (`Graph.hasGradedDistinctPencilRealization_of_twoEdgeConnected`), with no induction
hypothesis. -/
theorem _root_.Graph.graded_pencil_realization_theorem [Infinite K] [Finite α] [Finite β]
    {m : ℕ} (hm : 1 ≤ m) {G : Graph α β} (hne : V(G).Nonempty) :
    HasGradedPencilRealization K (m + 1) (m + 2) G ∧
      (G.Simple → HasGradedDistinctPencilRealization K (m + 1) (m + 2) G) := by
  classical
  refine Graph.pencil_reduction (P := fun G => HasGradedPencilRealization K (m + 1) (m + 2) G ∧
      (G.Simple → HasGradedDistinctPencilRealization K (m + 1) (m + 2) G)) ?_ ?_ ?_ ?_ ?_ G hne
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
  · -- a cut edge
    intro G _ _ htec IH
    obtain ⟨V₁, hssub, hne₁, hcut', -, hlt₁, hne₂, hlt₂⟩ :=
      Graph.exists_cut_sides_of_not_twoEdgeConnected htec
    obtain ⟨h₁, hd₁⟩ := IH _ hne₁ hlt₁
    obtain ⟨h₂, hd₂⟩ := IH _ hne₂ hlt₂
    exact ⟨hasGradedPencilRealization_of_cutEdges hssub hne₁ hcut' h₁ h₂, fun hS =>
      hasGradedDistinctPencilRealization_of_cutEdges hssub hne₁ hcut'
        (hd₁ (hS.mono (Graph.induce_le hssub.subset)))
        (hd₂ (hS.mono (Graph.induce_le Set.sdiff_subset)))⟩
  · -- parallel edges
    intro G hloop hV _ hS IH
    exact ⟨hasGradedPencilRealization_of_not_simple G hloop hV hS
      fun G' h1 h2 => (IH G' h1 h2).1, fun h => absurd h hS⟩
  · -- simple and two-edge-connected: an adjacent-distinct realization, with no induction hypothesis
    intro G hS hV htec
    have hd := Graph.hasGradedDistinctPencilRealization_of_twoEdgeConnected (K := K) hS hV htec hm
    obtain ⟨F, normal, plane, h, -, hr⟩ := id hd
    exact ⟨⟨F, normal, plane, h, hr⟩, fun _ => hd⟩

end CombinatorialRigidity.Molecular
