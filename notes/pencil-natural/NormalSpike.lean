import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Reduction

/-!
# Phase 43c's open: NORMAL's reduction on five structural cases, as a spike

Read-only scratch (not for landing). Written at Phase 43c's open (`notes/Phase43c.md`, the
*Verified at the open* item) against HEAD `7880d8f8`, to pin slice 1's new Lean. The reduction
loses `n`, `hD`, the proper rigid subgraph and the body of degree two; its cases are a loop, at
most two bodies, not two-edge-connected, two-edge-connected and not simple, and simple and
two-edge-connected (no induction hypothesis). The caller is
`Graph.graded_pencil_realization_theorem` with its `hthree` dissolved into the last three arms; the
`example` checks that its type is the landed theorem's. Primed names, so it still runs after slice
1 lands. Run from the repo root: `lake lean notes/pencil-natural/NormalSpike.lean` (at the open: no
error or warning, both on the standard three axioms).
-/

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

/-- NORMAL's restated reduction, as a spike: five structural cases, no `n`, no `hD`. -/
theorem _root_.Graph.pencil_reduction' {P : Graph α β → Prop}
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

theorem _root_.Graph.graded_pencil_realization_theorem' [Infinite K] [Finite α] [Finite β]
    {m : ℕ} (hm : 1 ≤ m) {G : Graph α β} (hne : V(G).Nonempty) :
    HasGradedPencilRealization K (m + 1) (m + 2) G ∧
      (G.Simple → HasGradedDistinctPencilRealization K (m + 1) (m + 2) G) := by
  classical
  refine Graph.pencil_reduction' (P := fun G => HasGradedPencilRealization K (m + 1) (m + 2) G ∧
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
  · -- simple and two-edge-connected: the distinct statement, with no induction hypothesis
    intro G hS hV htec
    have hd := Graph.hasGradedDistinctPencilRealization_of_twoEdgeConnected (K := K) hS hV htec hm
    obtain ⟨F, normal, plane, h, -, hr⟩ := id hd
    exact ⟨⟨F, normal, plane, h, hr⟩, fun _ => hd⟩

example : @Graph.graded_pencil_realization_theorem' = @Graph.graded_pencil_realization_theorem :=
  rfl

#print axioms Graph.pencil_reduction'
#print axioms Graph.graded_pencil_realization_theorem'

end CombinatorialRigidity.Molecular
