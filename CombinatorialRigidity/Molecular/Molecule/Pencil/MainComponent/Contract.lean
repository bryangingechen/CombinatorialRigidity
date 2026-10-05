/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.ContractAdditive

/-!
# Contraction at a `def₂`-rigid core in the `X₀` induction (Phase 40f CONTRACT-R)

**CONTRACT-R**, now a corollary of **CONTRACT-A** (`ContractAdditive.lean`; Phase 40-simplify
task `7d`/10q, `notes/Phase40-simplify.md`). Let `W ⊊ V(G)` with `|W| ≥ 2` induce a core
`H = G[W]` with `def₂(H) = 0`, let `r ∈ W`, and let `G/H = G.rigidContract (G.induce W) r` be
simple (no body outside `W` adjacent to two core bodies). If `X₀(G/H)` attains, so does `X₀(G)`.

A `def₂`-rigid core also has `def₃(H) = 0` (`def₃ ≤ def₂` by
`Graph.Connected.deficiency_three_le_deficiency_two`, and `def₃ ≥ 0`), so `X₀(H)` attains by the
flat case (`Graph.x0Attains_of_deficiency_two_eq_three`, FLAT, `cor:pencil-jj-flat`); contracting
at a core conserves `def₂` (`Graph.rigidContract_deficiency_eq`), so
`def₂(H) + def₂(G/H) = def₂(G)` is CONTRACT-A's additivity hypothesis for free, and
`Graph.X0Attains.of_additiveContract` applies. Both steps are after Katoh–Tanigawa 2011 §6.2,
Lemma 6.3, one lemma for any proper rigid subgraph, whose proof has CONTRACT-A's shape.

The rescaled lifting system, the curve, and CONTRACT-A's own argument through them (which this
step's retired curve proof duplicated) are in `ContractAdditive.lean` and `ContractCurve.lean`.
No blueprint `\lean{...}` pin moved: `cor:pencil-x0-contract-rigid`
(`blueprint/src/chapter/main-component.tex`, `sec:main-component-contract`) already pinned this
declaration before its proof changed.

## Main statements

* `Graph.isX0Graph_induce_of_deficiency_two_eq_zero` — a `def₂`-rigid core satisfies the standing
  hypotheses (`lem:pencil-contract-standing`).
* `Graph.X0Attains.of_rigidContract` — **CONTRACT-R** (`cor:pencil-x0-contract-rigid`).

See `notes/Phase40f.md`, `notes/Phase40k.md` and `notes/Phase40-simplify.md` task 10q.
-/

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

/-! ## The standing hypotheses at the core -/

/-- **A `def₂`-rigid core satisfies the standing hypotheses** (`lem:pencil-contract-standing`): a
core `G[W]` of a simple `G` with `|W| ≥ 2` and `def₂(G[W]) = 0` is simple, connected, and of
minimum degree at least two, a corollary of `Graph.isX0Graph_induce_of_deficiency_eq_zero`
(`ContractCurve.lean`) at `n = 2`. -/
theorem _root_.Graph.isX0Graph_induce_of_deficiency_two_eq_zero [Finite α] [Finite β]
    {G : Graph α β} (hS : G.Simple) {W : Set α} (hW : W ⊆ V(G)) (hW2 : 2 ≤ W.ncard)
    (hdef : (G.induce W).deficiency 2 = 0) : (G.induce W).IsX0Graph :=
  Graph.isX0Graph_induce_of_deficiency_eq_zero hS hW hW2 (n := 2)
    (by rw [Graph.bodyBarDim_two]; norm_num) hdef

/-! ## The assembly: contraction at a `def₂`-rigid core -/

/-- **Contraction at a `def₂`-rigid core** (`cor:pencil-x0-contract-rigid`; (MC-59)(d) with
(MC-39); after Katoh–Tanigawa 2011 §6.2, Lemma 6.3). Let `K` be infinite, let `G` satisfy
the standing hypotheses and be 2-edge-connected, and let `W ⊊ V(G)`, `|W| ≥ 2`, induce a core
`H = G[W]` with `def₂(H) = 0` and no outside body adjacent to two core bodies (`G/H` simple). If
`X₀(G/H)` attains, `X₀(G)` attains.

`H` satisfies the standing hypotheses
(`Graph.isX0Graph_induce_of_deficiency_two_eq_zero`), and `def₃(H) ≤ def₂(H) = 0`
(`Graph.Connected.deficiency_three_le_deficiency_two`, with `Graph.deficiency_nonneg`) forces
`def₃(H) = 0` too, so `X₀(H)` attains by the flat case
(`Graph.x0Attains_of_deficiency_two_eq_three`, `cor:pencil-jj-flat`). Contraction at a core
conserves `def₂` (`Graph.rigidContract_deficiency_eq`), so `def₂(H) + def₂(G/H) = def₂(G)` for
free, and `Graph.X0Attains.of_additiveContract` (**CONTRACT-A**) applies. -/
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
