/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.X0
import CombinatorialRigidity.Molecular.Molecule.Pencil.Base
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.CoverageTheoremS
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.GenericBase
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.GenericEar
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.GenericTriangle
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.GoodEar

/-!
# The main-component statements and the pencil conjecture (Phase 40n–40p MOTIVES)

`X0Dist` needs only landed pieces, with no hypothesis on the number of edge labels `β`: the
covering theorem (`Graph.X0Attains.of_twoEdgeConnected`, `MainComponent/CoverageTheoremS.lean`)
gives that the general configuration of a simple two-edge-connected graph on at least three bodies
attains, and one attaining configuration is already an adjacent-distinct pencil realization
(`Graph.X0Attains.hasDistinctPencilRealization`, `MainComponent/Configuration.lean`). `X0Gen` is
discharged separately (Phase 40p REDUCE+CLOSE), inside the pencil reduction's own induction: a
minimal planar-rigid set gives a one-body ear at hub ends or a pendant triangle
(`GoodEar.lean`), across which the smaller graph's generic realization extends
(`MainComponent/GenericEar.lean`, `MainComponent/GenericTriangle.lean`); this closes the route-B
induction and assembles the pencil conjecture.

## Main statements

* `x0Dist` — the distinct main-component statement.
* `hasGenericPencilRealization_of_IH` — the generic conjunct from the induction hypothesis
  (`thm:pencil-generic-step`).
* `pencilPair_of_IH` — `pencilPair_of_X0`'s per-graph step with `X0Gen` replaced by the induction
  hypothesis.
* `pencilPair_of_nonempty` — the conditioned pair at every nonempty graph
  (`thm:pencil-conditioned-pair-nonempty`).
* `x0Gen` — the generic main-component statement (`thm:pencil-x0-generic-attains`), a corollary.
* `pencil_conjecture` — the pencil conjecture (`thm:pencil-conjecture`), `pencil_conjecture_of_X0`
  verbatim with `x0Dist`/`x0Gen`.

See `notes/Phase40n.md`, `notes/Phase40p.md`, `notes/pencil/workbook/K-main-MC19.md` (route B,
(MC-183)–(MC-192)), and `blueprint/src/chapter/main-component.tex`
(`sec:main-component-statements`).
-/

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

/-- **The distinct main-component statement** (`lem:pencil-x0-distinct-statement`; Phase 40n
MOTIVES M0). Every simple two-edge-connected multigraph on at least three bodies has a pencil
realization at the deficiency rank with adjacent concurrency points distinct, over an infinite
field: one attaining configuration of the covering theorem is such a realization, with no
hypothesis on the number of edge labels. -/
theorem x0Dist [Finite α] [Finite β] [Infinite K] : X0Dist K α β :=
  fun _ hS hV htec => (Graph.X0Attains.of_twoEdgeConnected hS hV htec).hasDistinctPencilRealization

/-- **The generic conjunct from the induction hypothesis** (route B). -/
theorem hasGenericPencilRealization_of_IH [Infinite K] [Finite α] [Finite β] {G : Graph α β}
    (hS : G.Simple) (hV : 3 ≤ V(G).ncard) (htec : G.TwoEdgeConnected)
    (hfeas : PencilNondegFeasible K G)
    (hIH : ∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard → PencilPair K 3 G') :
    HasGenericPencilRealization K 3 G := by
  classical
  have hG : G.IsX0Graph :=
    { simple := hS
      connected := Graph.connected_iff.mpr ⟨Set.nonempty_of_ncard_ne_zero (by omega),
        Graph.preconnected_of_twoEdgeConnected htec⟩
      two_le_degree := fun v hv => Graph.two_le_degree_of_twoEdgeConnected htec hv (by omega) }
  by_cases hrig : ∃ Y ⊆ V(G), 2 ≤ Y.ncard ∧ (G.induce Y).deficiency 2 = 0
  swap
  · push Not at hrig
    exact hG.hasGenericPencilRealization_of_forall_deficiency_two_ne_zero hfeas hrig
  by_cases h3 : V(G).ncard = 3
  · exact (pencilPair_of_habitat_ncard_eq_three hS.toLoopless h3 htec
      (Graph.noRigid_of_simple_of_ncard_eq_three hS h3)).1 hS hfeas
  obtain ⟨hF1, hF2⟩ := hfeas.hub_conditions
  rcases hG.exists_oneEar_or_pendantTriangle htec (by omega) hF1 hF2 hrig with
    ⟨V₁, x, a, b, e, hear, ha, hb, hdef⟩ |
    ⟨V₁, x, c, e, hcover, hinj, hxV₁, hc, hpath, hsep, hdeg⟩
  · have hS₁ : (G.induce V₁).Simple :=
      hS.mono (Graph.induce_le (hear.cover ▸ Set.subset_union_left))
    have hlt : V(G.induce V₁).ncard < V(G).ncard := hear.ncard_lt le_rfl
    have hne : V(G.induce V₁).Nonempty := ⟨a, hear.left_mem⟩
    exact hear.hasGenericPencilRealization_of_one hS hfeas ha hb hdef
      ((hIH _ hne hlt).1 hS₁)
  · have hS₁ : (G.induce V₁).Simple := hS.mono (Graph.induce_le (hcover ▸ Set.subset_union_left))
    have hlt : V(G.induce V₁).ncard < V(G).ncard := by
      rw [Graph.vertexSet_induce]
      refine Set.ncard_lt_ncard ?_
      refine (Set.ssubset_iff_of_subset (hcover ▸ Set.subset_union_left)).mpr
        ⟨x 0, ?_, hxV₁ 0⟩
      rw [hcover]
      exact Set.mem_union_right _ ⟨_, rfl⟩
    have hne : V(G.induce V₁).Nonempty := ⟨c, hc⟩
    exact hasGenericPencilRealization_of_closedEar_two hS hfeas hcover hinj hxV₁ hc hpath hsep
      hdeg ((hIH _ hne hlt).1 hS₁)

/-- `pencilPair_of_X0`'s per-graph step with `X0Gen` replaced by the induction hypothesis. -/
theorem pencilPair_of_IH [Finite α] [Finite β] [Infinite K]
    (G : Graph α β) (hloop : G.Loopless) (hV : 3 ≤ V(G).ncard)
    (hIH : ∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard → PencilPair K 3 G') :
    PencilPair K 3 G := by
  have hD2 : (2 : ℕ) ≤ Graph.bodyBarDim 3 := by
    have := Graph.six_le_bodyBarDim (n := 3) (by norm_num); omega
  have hn : Graph.bodyBarDim 3 = screwDim 2 := Graph.bodyBarDim_eq_screwDim_sub_one (by norm_num)
  by_cases h2ec : G.TwoEdgeConnected
  · by_cases hs : G.Simple
    · have hd := x0Dist (K := K) G hs hV h2ec
      exact ⟨fun _ hf => hasGenericPencilRealization_of_IH hs hV h2ec hf hIH, fun _ => hd,
        hasPencilRealization_of_distinct hd⟩
    · exact ⟨fun h => absurd h hs, fun h => absurd h hs,
        hasPencilRealization_of_not_simple G hloop hV hs hIH⟩
  · exact pencilPair_of_not_twoEdgeConnected hD2 hn h2ec hIH

/-- **The conditioned pair at every nonempty graph** (`Graph.pencil_reduction` with the arms of
`pencil_conjecture_of_arms_pair`, not only at spanning graphs). -/
theorem pencilPair_of_nonempty [Finite α] [Finite β] [Infinite K] (G : Graph α β)
    (hne : V(G).Nonempty) : PencilPair K 3 G := by
  classical
  have hD6 : (6 : ℕ) ≤ Graph.bodyBarDim 3 := Graph.six_le_bodyBarDim (by norm_num)
  have hD2 : (2 : ℕ) ≤ Graph.bodyBarDim 3 := by omega
  have hn : Graph.bodyBarDim 3 = screwDim 2 := Graph.bodyBarDim_eq_screwDim_sub_one (by norm_num)
  have hloop_arm : ∀ G : Graph α β, (∃ e x, G.IsLoopAt e x) →
      (∀ G' : Graph α β, V(G').Nonempty →
        V(G').ncard < V(G).ncard ∨
          (V(G').ncard = V(G).ncard ∧ E(G').ncard < E(G).ncard) →
          PencilPair K 3 G') → PencilPair K 3 G := by
    rintro G ⟨e, x, hloopAt⟩ IH
    refine pencilPair_of_isLoopAt hloopAt (IH (G ＼ ({e} : Set β)) ?_ (Or.inr ⟨?_, ?_⟩))
    · rw [Graph.vertexSet_deleteEdges]; exact ⟨x, hloopAt.left_mem⟩
    · rw [Graph.vertexSet_deleteEdges]
    · rw [Graph.edgeSet_deleteEdges]
      exact Set.ncard_sdiff_singleton_lt_of_mem hloopAt.edge_mem
  exact Graph.pencil_reduction hD6 hloop_arm
    (fun G hloop hne hV2 => pencilPair_of_ncard_le_two hloop hne hV2)
    (fun G _ _ hntec hIH => pencilPair_of_not_twoEdgeConnected hD2 hn hntec hIH)
    (fun G hloop hV _ hIH => pencilPair_of_IH G hloop hV hIH)
    (fun G hloop hV _ _ _ hIH => pencilPair_of_IH G hloop hV hIH) G hne

/-- **The generic statement**, a corollary. -/
theorem x0Gen [Finite α] [Finite β] [Infinite K] : X0Gen K α β :=
  fun G hS hV _ hfeas =>
    (pencilPair_of_nonempty G (Set.nonempty_of_ncard_ne_zero (by omega))).1 hS hfeas

-- `[DecidableEq β]` is unused in the type; it is only threaded to `pencil_conjecture_of_X0`. The
-- linter's fix (drop it, `by classical exact` for the term) would change a headline signature
-- (`formalization.yaml`'s pencil entry, `thm:pencil-conjecture`), so it is a `40-simplify`
-- candidate (`notes/Phase40-cleanup.md`), not applied here.
set_option linter.unusedDecidableInType false in
/-- **The pencil conjecture** (carrying neither statement): `pencil_conjecture_of_X0` verbatim. -/
theorem pencil_conjecture [Nonempty α] [Finite α] [Finite β] [DecidableEq β] [Infinite K]
    (G : Graph α β) (hspan : V(G) = Set.univ) : PencilPair K 3 G :=
  pencil_conjecture_of_X0 x0Dist x0Gen G hspan

end CombinatorialRigidity.Molecular
