/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.ContractAdditive

/-!
# Contraction at a core of planar deficiency zero

The step of the induction on the general configuration at a core of planar deficiency zero
(`cor:pencil-x0-contract-rigid`, `sec:main-component-contract`), a corollary of the step at an
additive core (`thm:pencil-x0-contract-additive`, `MainComponent/ContractAdditive.lean`). Let
`W ⊊ V(G)` with `|W| ≥ 2` induce a core `H = G[W]` with `def₂(H) = 0`, let `r ∈ W`, and let no body
outside `W` be adjacent to two bodies of `W` (for a simple `G`, the simplicity of the contraction
`G/H = G.rigidContract (G.induce W) r`). If the general configuration of `G/H` attains, so does that
of `G`.

`H` satisfies the standing hypotheses (`lem:pencil-contract-standing-rigid` at `n = 2`), so it is
connected, and `0 ≤ def₃(H) ≤ def₂(H) = 0` (`Graph.Connected.deficiency_three_le_deficiency_two`,
`lem:deficiency-antitone`): both deficiencies of `H` vanish, and the general configuration of `H`
attains by the case of equal deficiencies (`Graph.x0Attains_of_deficiency_two_eq_three`,
`cor:pencil-jj-flat`). Contracting `H` does not change the planar deficiency
(`Graph.rigidContract_deficiency_eq`, `lem:pencil-contraction-deficiency`), so
`def₂(H) + def₂(G/H) = def₂(G)`, and the step at an additive core applies. The two steps read Katoh
and Tanigawa's contraction case (KT 2011 §6.2, Lemma 6.3), which contracts any proper rigid subgraph
whose contraction is simple, on configurations.

## Main results

* `Graph.isX0Graph_induce_of_deficiency_two_eq_zero`: a step of `cor:pencil-x0-contract-rigid`, the
  case `n = 2` of `lem:pencil-contract-standing-rigid`.
* `Graph.X0Attains.of_rigidContract`: `cor:pencil-x0-contract-rigid`.
-/

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

/-! ## The standing hypotheses at the core, at `n = 2` (`lem:pencil-contract-standing-rigid`) -/

/-- **A core of planar deficiency zero satisfies the standing hypotheses** (a step of
`cor:pencil-x0-contract-rigid`): if `G` is simple, `W ⊆ V(G)` has at least two bodies and
`def₂(G[W]) = 0`, then `G[W]` is simple, connected, and of minimum degree at least two. The case
`n = 2` of `Graph.isX0Graph_induce_of_deficiency_eq_zero` (`lem:pencil-contract-standing-rigid`,
`MainComponent/ContractCurve.lean`). -/
theorem _root_.Graph.isX0Graph_induce_of_deficiency_two_eq_zero [Finite α] [Finite β]
    {G : Graph α β} (hS : G.Simple) {W : Set α} (hW : W ⊆ V(G)) (hW2 : 2 ≤ W.ncard)
    (hdef : (G.induce W).deficiency 2 = 0) : (G.induce W).IsX0Graph :=
  Graph.isX0Graph_induce_of_deficiency_eq_zero hS hW hW2 (n := 2)
    (by rw [Graph.bodyBarDim_two]; norm_num) hdef

/-! ## Contraction at a core of planar deficiency zero (`cor:pencil-x0-contract-rigid`) -/

/-- **Contraction at a core of planar deficiency zero** (`cor:pencil-x0-contract-rigid`; after Katoh
and Tanigawa's contraction case, KT 2011 §6.2, Lemma 6.3): over an infinite field, let `G` satisfy
the standing hypotheses and be 2-edge-connected, let `W ⊊ V(G)` with `|W| ≥ 2` and `def₂(G[W]) = 0`,
such that no body outside `W` is adjacent to two bodies of `W` (`hatt`), and let `G/H` be the
contraction of `H = G[W]` to `r ∈ W`. If the general configuration of `G/H` attains, then the
general configuration of `G` attains.

Proof. `H` satisfies the standing hypotheses (`Graph.isX0Graph_induce_of_deficiency_two_eq_zero`),
and `def₃(H) ≤ def₂(H) = 0` (`Graph.Connected.deficiency_three_le_deficiency_two`), with
`Graph.deficiency_nonneg`, forces `def₃(H) = 0`, so the general configuration of `H` attains
(`Graph.x0Attains_of_deficiency_two_eq_three`, `cor:pencil-jj-flat`). Contracting `H` does not
change the planar deficiency (`Graph.rigidContract_deficiency_eq`), so
`def₂(H) + def₂(G/H) = def₂(G)`, and `Graph.X0Attains.of_additiveContract` applies. -/
theorem _root_.Graph.X0Attains.of_rigidContract [Infinite K] [Finite α] [Finite β]
    {G : Graph α β} (hG : G.IsX0Graph) (htec : G.TwoEdgeConnected) {W : Set α} {r : α}
    (hr : r ∈ W) (hWss : W ⊂ V(G)) (hW2 : 2 ≤ W.ncard) (hdef : (G.induce W).deficiency 2 = 0)
    (hatt : ∀ u ∉ W, ∀ c₁ ∈ W, ∀ c₂ ∈ W, G.Adj u c₁ → G.Adj u c₂ → c₁ = c₂)
    (hc : (G.rigidContract (G.induce W) r).X0Attains K) : G.X0Attains K := by
  classical
  have hW : W ⊆ V(G) := hWss.subset
  have hHX := Graph.isX0Graph_induce_of_deficiency_two_eq_zero hG.simple hW hW2 hdef
  have hdef3 : (G.induce W).deficiency 3 = 0 :=
    le_antisymm (hHX.connected.deficiency_three_le_deficiency_two.trans hdef.le)
      ((G.induce W).deficiency_nonneg 3 ⟨r, hr⟩)
  have hdefc2 : (G.rigidContract (G.induce W) r).deficiency 2 = G.deficiency 2 := by
    have : NeZero (Graph.bodyHingeMult 2) := ⟨by decide⟩
    exact Graph.rigidContract_deficiency_eq ⟨⟨Graph.induce_le hW, hdef⟩, hW2, hWss⟩ hr
  exact Graph.X0Attains.of_additiveContract hG htec hr hWss hW2 hdef3
    (by rw [hdef, hdefc2, zero_add]) hatt
    (Graph.x0Attains_of_deficiency_two_eq_three hHX.connected hHX.simple
      hHX.three_le_ncard_closedNbhd (by rw [hdef, hdef3])) hc

end CombinatorialRigidity.Molecular
