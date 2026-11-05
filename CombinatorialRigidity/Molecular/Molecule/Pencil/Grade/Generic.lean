/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.EarFree
public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Reduction

/-!
# The generic conjunct and the headline, in every dimension

`thm:pencil-d-generic` and `cor:pencil-d-conditioned-pair` of `blueprint/src/chapter/pencil-d.tex`,
`sec:pencil-d-generic`, with the remark after `def:pencil-d-lift-attains`.

* `LiftAttains.hasGradedGenericPencilRealization` (the remark): an attaining general lift is a
  generic realization in dimension `r + 3` (`IsNondegPencilPlaneRealization.lift`).
* `liftAttains_of_simple`: the general lift attains at every simple nondegeneracy-feasible graph
  with a body, by strong induction on the number of bodies, following the case split of the
  conditioned pair and the generic step in dimension three (`pencilPair_of_nonempty`,
  `hasGenericPencilRealization_of_IH`; `thm:pencil-conditioned-pair-nonempty`,
  `thm:pencil-generic-step`), here on the general lift. The arms: at most two bodies, a cut with no
  crossing edge, a cut edge or a pendant body (`Grade/LiftCutEdge.lean`, `Grade/LiftCases.lean`),
  a triangle, no rigid subgraph (`Grade/LiftNoRigid.lean`), and the good ear or pendant triangle
  of `Grade/GoodEar.lean`, whose ear arm gets its condition from `holdsGenerally_earFree`
  (`Grade/EarFree.lean`) at the selectors `liftAttains_of_ear` is given.
* `hasGradedGenericPencilRealization_of_simple` (`thm:pencil-d-generic`), and
  `Graph.graded_pencil_conditioned_pair` (`cor:pencil-d-conditioned-pair`): the three conjuncts,
  the first two being `Graph.graded_pencil_realization_theorem`'s (`Grade/Reduction.lean`).
-/

@[expose] public section

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

/-! ## The remark after `def:pencil-d-lift-attains` -/

/-- **An attaining general lift gives a generic realization** (the remark after
`def:pencil-d-lift-attains`): a lift of rank `tgt_d(G)` at a realization with `Q(b⁰) ≠ 0` is a
nondegenerate realization in dimension `r + 3` (`IsNondegPencilPlaneRealization.lift`), whose rows
are those of the panel-hinge framework. -/
theorem LiftAttains.hasGradedGenericPencilRealization {r : ℕ} {G : Graph α β}
    (h : LiftAttains K r G) :
    HasGradedGenericPencilRealization K (r + 1 + 1) (r + 1 + 2) G := by
  obtain ⟨ends, hlinks, Q, -, -, ⟨F, b0, P0, hnd, hQ⟩, hmain⟩ := h
  obtain ⟨lam, hlam, hrank⟩ := hmain F b0 P0 hnd hQ
  refine ⟨_, _, _, hnd.lift hlam hlinks, ?_⟩
  rw [PanelHingeFramework.span_rigidityRows_toPatchedBodyHinge]
  exact hrank

/-! ## The theorem (`thm:pencil-d-generic`) -/

/-- On three bodies a simple two-edge-connected graph is a triangle. -/
theorem adj_of_twoEdgeConnected_ncard_eq_three [Finite α] [Finite β] {G : Graph α β}
    (hS : G.Simple) (htec : G.TwoEdgeConnected) (h3 : V(G).ncard = 3) :
    ∀ u ∈ V(G), ∀ v ∈ V(G), u ≠ v → G.Adj u v := by
  have := hS
  intro u hu v hv huv
  by_contra hnot
  have hdeg := Graph.two_le_degree_of_twoEdgeConnected htec hu (by omega)
  rw [Graph.degree_eq_ncard_adj] at hdeg
  have hsub : N(G, u) ⊆ V(G) \ {u, v} := fun w hw => ⟨hw.right_mem, by
    rintro (rfl | rfl)
    · exact hw.ne rfl
    · exact hnot hw⟩
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_sdiff (Set.pair_subset hu hv), Set.ncard_pair huv] at h1
  omega

/-- **The general lift attains at every simple nondegeneracy-feasible multigraph with a body**
(`thm:pencil-d-generic`, the induction). -/
theorem liftAttains_of_simple [Infinite K] [Finite α] [Finite β] (r : ℕ) {G : Graph α β}
    (hS : G.Simple) (hne : V(G).Nonempty) (hfeas : PencilNondegFeasible K G) :
    LiftAttains K r G := by
  induction h : V(G).ncard using Nat.strong_induction_on generalizing G with
  | _ N ih =>
  subst h
  have IH : ∀ G' : Graph α β, G'.Simple → V(G').Nonempty → PencilNondegFeasible K G' →
      V(G').ncard < V(G).ncard → LiftAttains K r G' :=
    fun G' hS' hne' hf' hlt => ih _ hlt hS' hne' hf' rfl
  have := hS.toLoopless
  have : Nonempty α := ⟨hne.some⟩
  -- at most two bodies
  by_cases h2 : V(G).ncard ≤ 2
  · exact liftAttains_of_ncard_le_two r hS hfeas h2
  push Not at h2
  -- disconnected: a cut that no edge crosses
  by_cases hdisc : ∃ V₁ : Set α, V₁.Nonempty ∧ V₁ ⊂ V(G) ∧ G.cutEdges V₁ = ∅
  · obtain ⟨V₁, hne₁, hssub, hC0⟩ := hdisc
    obtain ⟨hf₁, hf₂, hstep⟩ := liftAttains_of_cutEdges_eq_empty r hfeas hne₁ hssub hC0
    exact hstep (IH _ (hS.mono (Graph.induce_le hssub.subset)) hne₁ hf₁
        (Set.ncard_lt_ncard hssub (Set.toFinite _)))
      (IH _ (hS.mono (Graph.induce_le Set.sdiff_subset)) (Set.nonempty_of_ssubset hssub) hf₂
        (Set.ncard_lt_ncard (Set.sdiff_ssubset_left_iff.2 (by
          obtain ⟨x, hx⟩ := hne₁; exact ⟨x, hssub.subset hx, hx⟩)) (Set.toFinite _)))
  push Not at hdisc
  -- a cut edge
  by_cases htec : G.TwoEdgeConnected
  swap
  · simp only [Graph.TwoEdgeConnected, not_forall, not_le, exists_prop] at htec
    obtain ⟨V₁, hne₁, hssub, hcut_lt2⟩ := htec
    have hcut : (G.cutEdges V₁).ncard ≤ 1 := Nat.lt_succ_iff.mp hcut_lt2
    obtain ⟨e, -, u, v, huv, hu, hv⟩ := hdisc V₁ hne₁ hssub
    -- a side of one body: a pendant body
    have hpend : ∀ {V₁ : Set α} {e : β} {u v : α}, G.IsLink e u v → u ∈ V₁ → v ∉ V₁ →
        (G.cutEdges V₁).ncard ≤ 1 → V(G) \ V₁ = {v} → LiftAttains K r G := by
      intro V₁ e u v huv hu hv hcut hV₂
      have hNv : ∀ y, G.Adj v y → y = u := by
        rintro y ⟨f, hf⟩
        have hyv : y ≠ v := Graph.Adj.ne (G := G) ⟨f, hf.symm⟩
        have hy : y ∈ V₁ := by
          by_contra hy
          have : y ∈ V(G) \ V₁ := ⟨hf.right_mem, hy⟩
          rw [hV₂] at this
          exact hyv this
        exact (Graph.eq_and_eq_of_isLink_crossing huv hu hv hcut hf.symm hy hv).2.1
      have hdeg : G.degree v = 1 := by
        rw [Graph.degree_eq_ncard_adj]
        convert Set.ncard_singleton u using 2
        ext y
        exact ⟨hNv y, fun h => h ▸ ⟨e, huv.symm⟩⟩
      obtain ⟨hfH, hstep⟩ := liftAttains_of_pendant r hS hfeas hdeg ⟨e, huv.symm⟩
      refine hstep (IH _ (hS.mono (Graph.induce_le Set.sdiff_subset)) ⟨u, huv.left_mem, ?_⟩ hfH ?_)
      · exact fun h => Graph.Adj.ne (G := G) ⟨e, huv⟩ h
      · exact Set.ncard_lt_ncard (Set.sdiff_ssubset_left_iff.2 ⟨v, huv.right_mem, rfl⟩)
    set V₂ := V(G) \ V₁ with hV₂def
    have hv₂ : v ∈ V₂ := ⟨huv.right_mem, hv⟩
    have hu₂ : u ∉ V₂ := fun h => h.2 hu
    have hcut₂ : (G.cutEdges V₂).ncard ≤ 1 :=
      le_trans (Set.ncard_le_ncard (Graph.cutEdges_diff_subset G V₁) (Set.toFinite _)) hcut
    have hVcard : V₁.ncard + V₂.ncard = V(G).ncard := by
      rw [← Set.ncard_union_eq Set.disjoint_sdiff_right (Set.toFinite _) (Set.toFinite _),
        Set.union_sdiff_cancel hssub.subset]
    have hne₂ : V₂.Nonempty := Set.nonempty_of_ssubset hssub
    by_cases hV₂one : V₂.ncard = 1
    · exact hpend huv hu hv hcut
        ((Set.ncard_le_one_iff_subsingleton.mp hV₂one.le).eq_singleton_of_mem hv₂)
    by_cases hV₁one : V₁.ncard = 1
    · refine hpend huv.symm hv₂ hu₂ hcut₂ ?_
      rw [hV₂def, Set.sdiff_sdiff_cancel_left hssub.subset]
      exact (Set.ncard_le_one_iff_subsingleton.mp hV₁one.le).eq_singleton_of_mem hu
    have h₂ : 2 ≤ V₂.ncard := by have := hne₂.ncard_pos; omega
    have h₁ : 2 ≤ V₁.ncard := by have := hne₁.ncard_pos; omega
    obtain ⟨hf₁, hf₂, hstep⟩ :=
      liftAttains_of_cutEdge r hS hfeas huv hu hv hssub.subset hcut
    have hsub₁ : V₁ ∪ {v} ⊆ V(G) := Set.union_subset hssub.subset
      (Set.singleton_subset_iff.2 huv.right_mem)
    have hsub₂ : V₂ ∪ {u} ⊆ V(G) := Set.union_subset Set.sdiff_subset
      (Set.singleton_subset_iff.2 huv.left_mem)
    refine hstep (IH _ (hS.mono (Graph.induce_le hsub₁)) ⟨u, Or.inl hu⟩ hf₁ ?_)
      (IH _ (hS.mono (Graph.induce_le hsub₂)) ⟨v, Or.inl hv₂⟩ hf₂ ?_)
    · change (V₁ ∪ {v}).ncard < _
      rw [Set.union_singleton, Set.ncard_insert_of_notMem hv]; omega
    · change (V₂ ∪ {u}).ncard < _
      rw [Set.union_singleton, Set.ncard_insert_of_notMem hu₂]; omega
  have hconn : G.Connected :=
    Graph.connected_iff.mpr ⟨hne, Graph.preconnected_of_twoEdgeConnected htec⟩
  -- two-edge-connected: the standing hypotheses
  have hG : G.IsX0Graph :=
    { simple := hS
      connected := hconn
      two_le_degree := fun v hv => Graph.two_le_degree_of_twoEdgeConnected htec hv (by omega) }
  by_cases h3 : V(G).ncard = 3
  · exact liftAttains_of_triangle r hS hfeas h3 (adj_of_twoEdgeConnected_ncard_eq_three hS htec h3)
  have h4 : 4 ≤ V(G).ncard := by omega
  by_cases hrig : ∃ Y ⊆ V(G), 2 ≤ Y.ncard ∧ (G.induce Y).deficiency 2 = 0
  swap
  · push Not at hrig
    exact liftAttains_of_forall_deficiency_two_ne_zero r hG hfeas hrig
      (hG.x0AttainsGrade (by omega))
  obtain ⟨hF1, hF2⟩ := hfeas.hub_conditions
  rcases hG.exists_goodEar_or_pendantTriangle htec h4 hF1 hF2 hrig with
    ⟨x₁, x₂, c, h₁, h₂, h₁₂, h₁c, h₂c, hc⟩ | ⟨W₀, x, a, b, hW⟩
  · obtain ⟨hfH, hstep⟩ := liftAttains_of_pendantTriangle r hS hfeas h₁ h₂ h₁₂ h₁c h₂c hc
    refine hstep (IH _ (hS.mono (Graph.induce_le Set.sdiff_subset)) ⟨c, ?_, ?_⟩ hfH ?_)
    · exact h₁c.symm.left_mem
    · rintro (h | h)
      · exact h₁c.ne h.symm
      · exact h₂c.ne h.symm
    · exact Set.ncard_lt_ncard (Set.sdiff_ssubset_left_iff.2 ⟨x₁, h₁c.left_mem, Or.inl rfl⟩)
  · obtain ⟨hfH, hstep⟩ := liftAttains_of_ear r hS hfeas hW.degree_eq hW.adj_a hW.adj_b hW.ne
      hW.hub_a hW.hub_b (le_of_eq (hW.deficiency_delete _ (by omega)))
    obtain ⟨hubSel, nbrSel, hHubSel, hNbrSel⟩ := exists_steer_selectors hfeas
    refine hstep hHubSel hNbrSel (holdsGenerally_earFree hS hfeas hW hHubSel hNbrSel).2
      (IH _ (hS.mono (Graph.induce_le Set.sdiff_subset)) ⟨a, hW.adj_a.right_mem, ?_⟩ hfH ?_)
    · rintro (rfl : a = x)
      exact hW.adj_a.ne rfl
    · exact Set.ncard_lt_ncard (Set.sdiff_ssubset_left_iff.2 ⟨x, hW.adj_a.left_mem, rfl⟩)

/-- **The generic conjunct, in every dimension** (`thm:pencil-d-generic`), in dimension
`d = m + 2 ≥ 3`. -/
theorem hasGradedGenericPencilRealization_of_simple [Infinite K] [Finite α] [Finite β] {m : ℕ}
    (hm : 1 ≤ m) {G : Graph α β} (hS : G.Simple) (hne : V(G).Nonempty)
    (hfeas : GradedPencilNondegFeasible K (m + 1) G) :
    HasGradedGenericPencilRealization K (m + 1) (m + 2) G := by
  obtain ⟨r, rfl⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
  exact (liftAttains_of_simple r hS hne
    ((gradedPencilNondegFeasible_iff (by omega) G).1 hfeas)).hasGradedGenericPencilRealization

/-- **The conditioned pair, in every dimension** (`cor:pencil-d-conditioned-pair`). -/
theorem _root_.Graph.graded_pencil_conditioned_pair [Infinite K] [Finite α] [Finite β] {m : ℕ}
    (hm : 1 ≤ m) {G : Graph α β} (hne : V(G).Nonempty) :
    HasGradedPencilRealization K (m + 1) (m + 2) G ∧
      (G.Simple → HasGradedDistinctPencilRealization K (m + 1) (m + 2) G) ∧
      (G.Simple → GradedPencilNondegFeasible K (m + 1) G →
        HasGradedGenericPencilRealization K (m + 1) (m + 2) G) :=
  ⟨(Graph.graded_pencil_realization_theorem hm hne).1,
    (Graph.graded_pencil_realization_theorem hm hne).2,
    fun hS hfeas => hasGradedGenericPencilRealization_of_simple hm hS hne hfeas⟩

end CombinatorialRigidity.Molecular
