/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.X0
public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Generic

/-!
# The two main-component statements and the pencil realization theorem

The proofs of the two main-component statements (`def:pencil-main-component-statements`,
`sec:main-component-statements`) and of the pencil realization theorem
(`thm:pencil-realization-theorem`), over an infinite field. The distinct statement is immediate
(`lem:pencil-x0-distinct-statement`): the general configuration of a simple two-edge-connected graph
on at least three bodies attains (`Graph.X0Attains.of_twoEdgeConnected`, `thm:pencil-x0-coverage`,
`MainComponent/CoverageTheoremS.lean`), and one attaining configuration is an adjacent-distinct
pencil realization (`Graph.X0Attains.hasDistinctPencilRealization`,
`lem:pencil-x0-attains-distinct`, `MainComponent/Configuration.lean`), with no hypothesis on the
number of edge labels.

The generic statement is the case `d = 3` of the generic conjunct in every dimension
(`thm:pencil-d-generic`, `Grade/Generic.lean`): at a simple nondegeneracy-feasible graph with a
body, the general lift attains (`liftAttains_of_simple`, at `r = 0`), and an attaining general lift
is a generic realization (`LiftAttains.hasGradedGenericPencilRealization`), which at `d = 3` is a
generic pencil realization (`hasGradedGenericPencilRealization_two_iff`,
`lem:pencil-d-nondegenerate-three`).

The conditioned pair at every graph with at least one body (the general claim of
`thm:pencil-realization-theorem`) is the case `d = 3` of the conditioned pair in every dimension
(`Graph.graded_pencil_conditioned_pair`, `cor:pencil-d-conditioned-pair`), read through the bridges
of `lem:pencil-d-rank-agrees-three` and `lem:pencil-d-nondegenerate-three`; at a graph on the whole
ambient body set it is the pencil realization theorem.

## Main results

* `x0Dist`: `lem:pencil-x0-distinct-statement`, the distinct main-component statement.
* `x0Gen`: `thm:pencil-x0-generic-attains`, the generic main-component statement.
* `pencilPair_of_nonempty`: the general claim of `thm:pencil-realization-theorem`, the conditioned
  pair at every graph with at least one body.
* `pencil_realization_theorem`: `thm:pencil-realization-theorem`, the conditioned pair at every
  multigraph on the whole ambient body set.
-/

@[expose] public section

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

/-- **The distinct main-component statement** (`lem:pencil-x0-distinct-statement`, and the distinct
statement of `thm:pencil-x0-generic-attains`): over an infinite field, for finite `α` and `β`, every
simple two-edge-connected multigraph on at least three bodies has an adjacent-distinct pencil
realization at the deficiency rank at `n = 3` (`X0Dist`). Its general configuration attains
(`Graph.X0Attains.of_twoEdgeConnected`, `thm:pencil-x0-coverage`), and one attaining configuration
is such a realization (`Graph.X0Attains.hasDistinctPencilRealization`,
`lem:pencil-x0-attains-distinct`), with no hypothesis on the number of edge labels. -/
theorem x0Dist [Finite α] [Finite β] [Infinite K] : X0Dist K α β :=
  fun _ hS hV htec => (Graph.X0Attains.of_twoEdgeConnected hS hV htec).hasDistinctPencilRealization

/-- **The generic main-component statement** (`thm:pencil-x0-generic-attains`, its generic
statement): over an infinite field, for finite `α` and `β`, every simple two-edge-connected
multigraph on at least three bodies that is nondegeneracy-feasible has a generic pencil realization
at `n = 3` (`X0Gen`). It is the case `d = 3` of the generic conjunct in every dimension, which asks
neither two-edge-connectivity nor a third body: the general lift attains
(`liftAttains_of_simple 0`, `thm:pencil-d-generic`), an attaining general lift is a generic
realization in dimension three (`LiftAttains.hasGradedGenericPencilRealization`), and that is a
generic pencil realization (`hasGradedGenericPencilRealization_two_iff`,
`lem:pencil-d-nondegenerate-three`). -/
theorem x0Gen [Finite α] [Finite β] [Infinite K] : X0Gen K α β :=
  fun G hS hV _ hfeas => (hasGradedGenericPencilRealization_two_iff 3 G).1
    (liftAttains_of_simple 0 hS (Set.nonempty_of_ncard_ne_zero (by omega))
      hfeas).hasGradedGenericPencilRealization

/-- **The conditioned pair at every nonempty multigraph** (the general claim of
`thm:pencil-realization-theorem`): over an infinite field, for finite `α`
and `β`, every graph with at least one body satisfies the conditioned pair at `n = 3`. It is the
case `m = 1` (`d = 3`) of `Graph.graded_pencil_conditioned_pair` (`cor:pencil-d-conditioned-pair`):
its three conjuncts are those of `PencilPair K 3` through `hasGradedPencilRealization_two_iff`,
`hasGradedDistinctPencilRealization_two_iff` (`lem:pencil-d-rank-agrees-three`),
`hasGradedGenericPencilRealization_two_iff` and `gradedPencilNondegFeasible_two_iff`
(`lem:pencil-d-nondegenerate-three`). -/
theorem pencilPair_of_nonempty [Finite α] [Finite β] [Infinite K] (G : Graph α β)
    (hne : V(G).Nonempty) : PencilPair K 3 G := by
  obtain ⟨hbare, hdist, hgen⟩ := Graph.graded_pencil_conditioned_pair (K := K) (m := 1) le_rfl hne
  exact ⟨fun hS hfeas => (hasGradedGenericPencilRealization_two_iff 3 G).1
      (hgen hS ((gradedPencilNondegFeasible_two_iff G).2 hfeas)),
    fun hS => (hasGradedDistinctPencilRealization_two_iff 3 G).1 (hdist hS),
    (hasGradedPencilRealization_two_iff 3 G).1 hbare⟩

/-- **The pencil realization theorem** (`thm:pencil-realization-theorem`): over an infinite field,
for finite `α` and `β` with `α` nonempty, every multigraph on the whole ambient body set satisfies
the conditioned pair at `n = 3`. It is `pencilPair_of_nonempty`, as such a multigraph has a body. -/
theorem pencil_realization_theorem [Nonempty α] [Finite α] [Finite β] [Infinite K]
    (G : Graph α β) (hspan : V(G) = Set.univ) : PencilPair K 3 G :=
  pencilPair_of_nonempty G (hspan ▸ Set.univ_nonempty)

end CombinatorialRigidity.Molecular
