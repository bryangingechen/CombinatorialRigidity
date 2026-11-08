/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.ShortThree
public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.ContractAdditive
public import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.CoverageTheoremS
public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Chains

/-!
# The coverage in every dimension

The two nodes of `sec:pencil-d-coverage` (`blueprint/src/chapter/pencil-d.tex`).

## Main results

* `Graph.IsX0Graph.x0AttainsGrade`: `thm:pencil-d-coverage`, every graph satisfying the standing
  hypotheses attains the grade `m ≥ 1`, by strong induction on `V(G).ncard` with the chapter's cases
  in its order (bridge path, cut vertex, cycle, flat, rigid core, embedding, then a chain or an
  additive core).
* `Graph.X0AttainsGrade.of_twoEdgeConnected`: its last claim, a simple 2-edge-connected graph on at
  least three bodies.
* `Graph.hasGradedDistinctPencilRealization_of_twoEdgeConnected`:
  `lem:pencil-d-distinct-statement`, an adjacent-distinct realization of a simple 2-edge-connected
  graph on at least three bodies.
-/

@[expose] public section

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

/-- `ℓ = 2` at `d = 4` and `ℓ = 3` from `d = 5` on satisfy `3(ℓ + 1) ≤ D`. -/
private theorem exists_chainBound {m : ℕ} (hm : 2 ≤ m) :
    ∃ ℓ, 3 * (ℓ + 1) ≤ Graph.bodyBarDim (m + 2) ∧ ((m = 2 ∧ ℓ = 2) ∨ ℓ = 3) := by
  obtain rfl | hm3 : m = 2 ∨ 3 ≤ m := by omega
  · exact ⟨2, by decide, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨3, (by decide : 3 * (3 + 1) ≤ Graph.bodyBarDim 5).trans
      (Graph.bodyBarDim_mono (by omega)), Or.inr rfl⟩

/-! ## The coverage (`thm:pencil-d-coverage`) -/

/-- **The coverage, in every dimension** (`thm:pencil-d-coverage`). -/
theorem _root_.Graph.IsX0Graph.x0AttainsGrade [Infinite K] [Finite α] [Finite β] {m : ℕ}
    {G : Graph α β} (hG : G.IsX0Graph) (hm : 1 ≤ m) : G.X0AttainsGrade K m := by
  obtain rfl | hm2 : m = 1 ∨ 2 ≤ m := by omega
  · exact Graph.x0AttainsGrade_one_iff.2 hG.x0Attains
  induction h : V(G).ncard using Nat.strong_induction_on generalizing G with
  | _ N ih =>
  subst h
  have ih' : ∀ G' : Graph α β, G.X0Below G' → G'.X0AttainsGrade K m :=
    fun G' hG' => ih _ hG'.2 hG'.1 rfl
  -- the first five cases
  by_cases htec : G.TwoEdgeConnected
  swap
  · obtain ⟨V₁, V₂, k, x, a, b, e, hcover, hdisj, hxV₁, hxV₂, hinj, ha, hb, hpath, hsep, h₁, h₂⟩ :=
      hG.exists_bridgePath_of_not_twoEdgeConnected htec
    exact Graph.X0AttainsGrade.of_bridgePath hG hcover hdisj hxV₁ hxV₂ hinj ha hb hpath hsep
      (ih' _ h₁) (ih' _ h₂)
  by_cases h2c : ∀ v ∈ V(G), (G.induce (V(G) \ {v})).Connected
  swap
  · push Not at h2c
    obtain ⟨v, -, hdisc⟩ := h2c
    obtain ⟨V₁, V₂, hcover, hoverlap, hsep, h₁, h₂⟩ :=
      hG.exists_cutVertex_of_not_connected htec hdisc
    exact Graph.X0AttainsGrade.of_cutVertex hG hcover hoverlap hsep (ih' _ h₁) (ih' _ h₂)
  by_cases hcyc : ∀ v ∈ V(G), G.degree v = 2
  · obtain ⟨k, x, a, b, e, f, hk, hcover, hinj, hxa, hxb, hab, hf, hpath, honly⟩ :=
      hG.exists_cycle_of_forall_degree_eq_two hcyc
    exact Graph.X0AttainsGrade.of_cycle hk hcover hinj hxa hxb hab hf hpath honly
  push Not at hcyc
  by_cases hflat : G.deficiency 2 = G.deficiency (m + 2)
  · exact Graph.x0AttainsGrade_of_deficiency_two_eq hG.connected hG.simple
      hG.three_le_ncard_closedNbhd hflat
  have hpos : 0 < G.deficiency 2 := by
    have h1 := hG.connected.deficiency_le_deficiency_of_le (show 2 ≤ m + 2 by omega)
    have h0 := Graph.deficiency_nonneg G (m + 2) hG.connected.nonempty
    omega
  by_cases hrig : ∃ Y ⊆ V(G), 2 ≤ Y.ncard ∧ (G.induce Y).deficiency 2 = 0
  · obtain ⟨Y, hY, hY2, hYd⟩ := hrig
    obtain ⟨W, r, hr, hWss, hW2, hWd, hatt⟩ :=
      G.exists_rigidCore_of_deficiency_two_pos hpos hY hY2 hYd
    exact Graph.X0AttainsGrade.of_rigidContract hG htec hr hWss hW2 hWd hatt
      (ih' _ ⟨Graph.isX0Graph_rigidContract_induce hG htec hr hWss hatt,
        Graph.rigidContract_vertexSet_ncard_lt hWss.subset hW2⟩)
  push Not at hrig
  -- the embedding
  by_cases hemb : G.deficiency 3 = G.deficiency (m + 2)
  · exact Graph.X0AttainsGrade.of_le hG.connected hm hemb
      (Graph.x0AttainsGrade_one_iff.2 hG.x0Attains)
  -- a chain or a core
  obtain ⟨ℓ, hℓ, hℓm⟩ := exists_chainBound hm2
  rcases hG.exists_chain_or_core h2c hcyc hrig (by omega) hℓ with
    ⟨V₁, k, x, a, b, e, hC, hk⟩ | ⟨W, r, hr, hWss, hW2, hWd, hadd, hatt⟩ | ⟨-, h3, hn⟩
  · have h₁ : G.X0Below (G.induce V₁) :=
      ⟨hC.isX0Graph_induce hG h2c, hC.toIsOpenEar.ncard_lt hC.one_le⟩
    by_cases hlong : screwDim (m + 1) - 1 ≤ k
    · exact Graph.X0AttainsGrade.of_openEar hG hlong hC.cover hC.inj hC.notMem hC.left_mem
        hC.right_mem hC.ne hC.isLink hC.sep (ih' _ h₁)
    by_cases h4 : 4 ≤ k
    · obtain ⟨n, rfl⟩ : ∃ n, k = n + 4 := ⟨k - 4, by omega⟩
      have h₂ : G.X0Below (G.splitOff (x 1) (x 0) (x 2) (e 1)) :=
        ⟨hC.toIsOpenEar.isX0Graph_splitOff_succ (n := n + 1) hG,
          Graph.splitOff_vertexSet_ncard_lt (hC.cover ▸ Or.inr ⟨1, rfl⟩)⟩
      exact Graph.X0AttainsGrade.of_openEar_four hG hC.cover hC.inj hC.notMem hC.left_mem
        hC.right_mem hC.ne hC.isLink hC.sep (ih' _ h₁) (ih' _ h₂)
    · obtain ⟨rfl, rfl⟩ : m = 2 ∧ k = 3 := by omega
      have h₂ : G.X0Below (G.splitOff (x 1) (x 0) (x 2) (e 1)) :=
        ⟨hC.toIsOpenEar.isX0Graph_splitOff_succ (n := 0) hG,
          Graph.splitOff_vertexSet_ncard_lt (hC.cover ▸ Or.inr ⟨1, rfl⟩)⟩
      exact Graph.X0AttainsGrade.of_openEar_three hG le_rfl (by norm_num) hC.cover hC.inj
        hC.notMem hC.left_mem hC.right_mem hC.ne hC.isLink hC.sep (ih' _ h₁) (ih' _ h₂)
  · have hW : G.X0Below (G.induce W) :=
      ⟨Graph.isX0Graph_induce_of_deficiency_eq_zero hG.simple hWss.subset hW2 (by omega) hWd,
        Set.ncard_lt_ncard hWss⟩
    have hc : G.X0Below (G.rigidContract (G.induce W) r) :=
      ⟨Graph.isX0Graph_rigidContract_induce hG htec hr hWss hatt,
        Graph.rigidContract_vertexSet_ncard_lt hWss.subset hW2⟩
    exact Graph.X0AttainsGrade.of_additiveContract hG htec hr hWss hW2 hWd hadd hatt
      (ih' _ hW) (ih' _ hc)
  · exact absurd (h3.trans hn.symm) hemb

/-- **The coverage, its last claim** (`thm:pencil-d-coverage`): a simple 2-edge-connected graph on
at least three bodies. -/
theorem _root_.Graph.X0AttainsGrade.of_twoEdgeConnected [Infinite K] [Finite α] [Finite β]
    {m : ℕ} {G : Graph α β} (hS : G.Simple) (hV : 3 ≤ V(G).ncard)
    (htec : G.TwoEdgeConnected) (hm : 1 ≤ m) : G.X0AttainsGrade K m :=
  Graph.IsX0Graph.x0AttainsGrade
    { simple := hS
      connected := Graph.connected_iff.mpr ⟨Set.nonempty_of_ncard_ne_zero (by omega),
        Graph.preconnected_of_twoEdgeConnected htec⟩
      two_le_degree := fun v hv => Graph.two_le_degree_of_twoEdgeConnected htec hv (by omega) } hm

/-! ## Adjacent-distinct realizations (`lem:pencil-d-distinct-statement`) -/

/-- **Simple 2-edge-connected graphs have adjacent-distinct realizations, in every dimension**
(`lem:pencil-d-distinct-statement`): over an infinite field, every simple 2-edge-connected graph on
at least three bodies has an adjacent-distinct pencil realization in dimension `m + 2`. Its general
configuration attains (`Graph.X0AttainsGrade.of_twoEdgeConnected`), and an attaining configuration
gives one (`Graph.X0AttainsGrade.hasGradedDistinctPencilRealization`). -/
theorem _root_.Graph.hasGradedDistinctPencilRealization_of_twoEdgeConnected [Infinite K]
    [Finite α] [Finite β] {m : ℕ} {G : Graph α β} (hS : G.Simple) (hV : 3 ≤ V(G).ncard)
    (htec : G.TwoEdgeConnected) (hm : 1 ≤ m) :
    HasGradedDistinctPencilRealization K (m + 1) (m + 2) G :=
  (Graph.X0AttainsGrade.of_twoEdgeConnected hS hV htec hm).hasGradedDistinctPencilRealization

end CombinatorialRigidity.Molecular
