/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Configuration
public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.ZeroHeights
public import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.CoverageTheoremS

/-!
# The pencil in every dimension when `def₂(G) ≤ 3`

`thm:pencil-d-deficiency-two-le-three` (`blueprint/src/chapter/pencil-d.tex`,
`sec:pencil-d-stable`): over an infinite field, a graph satisfying the standing hypotheses
(`Graph.IsX0Graph`) with `def₂(G) ≤ 3` has the general configuration attaining in every dimension
`d = m + 2 ≥ 3`, and an adjacent-distinct pencil realization there.

The general configuration attains in dimension three by `Graph.IsX0Graph.x0Attains`
(`thm:pencil-x0-coverage`). As `G` is connected and `def₂(G) + 3 ≤ 6 = bodyBarDim 3`, the
deficiencies in dimensions three and `d` agree
(`Graph.Connected.deficiency_eq_of_deficiency_two_add_three_le`, `lem:deficiency-stable`), and
`Graph.X0AttainsGrade.of_le` carries the attaining up.

## Main results

* `Graph.x0AttainsGrade_of_deficiency_two_le_three`: the general configuration attains in dimension
  `m + 2`, for `m ≥ 1` and `def₂(G) ≤ 3`.
* `Graph.hasGradedDistinctPencilRealization_of_deficiency_two_le_three`: the adjacent-distinct
  pencil realization in that dimension.
-/

@[expose] public section

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*} {m : ℕ}

/-- **The general configuration attains in every dimension `m + 2 ≥ 3` when `def₂(G) ≤ 3`**
(`thm:pencil-d-deficiency-two-le-three`, first claim): for `G` satisfying the standing hypotheses
(`Graph.IsX0Graph`) over an infinite field, by the dimension-three case
(`Graph.IsX0Graph.x0Attains`) and `Graph.X0AttainsGrade.of_le`, the deficiencies agreeing
(`Graph.Connected.deficiency_eq_of_deficiency_two_add_three_le`). -/
theorem _root_.Graph.x0AttainsGrade_of_deficiency_two_le_three [Infinite K] [Finite α] [Finite β]
    {G : Graph α β} (hG : G.IsX0Graph) (hm : 1 ≤ m) (hdef : G.deficiency 2 ≤ 3) :
    G.X0AttainsGrade K m := by
  have h : G.deficiency 2 + 3 ≤ (Graph.bodyBarDim 3 : ℤ) := by
    have : Graph.bodyBarDim 3 = 6 := by decide
    rw [this]; push_cast; omega
  have hdef' : G.deficiency (1 + 2) = G.deficiency (m + 2) :=
    hG.connected.deficiency_eq_of_deficiency_two_add_three_le (by omega) h
  exact Graph.X0AttainsGrade.of_le hG.connected hm hdef'
    (Graph.x0AttainsGrade_one_iff.2 hG.x0Attains)

/-- **The adjacent-distinct pencil realization in every dimension `m + 2 ≥ 3` when `def₂(G) ≤ 3`**
(`thm:pencil-d-deficiency-two-le-three`, second claim), from the attaining
(`Graph.x0AttainsGrade_of_deficiency_two_le_three`) by
`Graph.X0AttainsGrade.hasGradedDistinctPencilRealization`. -/
theorem _root_.Graph.hasGradedDistinctPencilRealization_of_deficiency_two_le_three [Infinite K]
    [Finite α] [Finite β] {G : Graph α β} (hG : G.IsX0Graph) (hm : 1 ≤ m)
    (hdef : G.deficiency 2 ≤ 3) : HasGradedDistinctPencilRealization K (m + 1) (m + 2) G :=
  (Graph.x0AttainsGrade_of_deficiency_two_le_three hG hm hdef).hasGradedDistinctPencilRealization

end CombinatorialRigidity.Molecular
