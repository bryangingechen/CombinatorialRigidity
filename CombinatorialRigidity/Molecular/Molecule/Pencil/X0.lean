/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Arms
public import CombinatorialRigidity.Molecular.AlgebraicInduction.DeficiencyBound

/-!
# The main-component statements, and a multigraph with parallel edges

The definitions of `sec:pencil-main-component-route`. The two main-component statements
(`def:pencil-main-component-statements`) say that every simple two-edge-connected multigraph on at
least three bodies has an adjacent-distinct pencil realization at the deficiency rank (`X0Dist`),
and a generic one when it is nondegeneracy-feasible (`X0Gen`), at `n = 3`.
`MainComponent/Statements.lean` proves the two statements (`x0Dist`, `x0Gen`). A loopless
multigraph on at least three bodies that is not simple has a pencil realization at the deficiency
rank, by the contraction of two parallel edges (`lem:pencil-nonsimple-case`), as in the proof of
KT Lemma 6.2 (p. 673).

## Main definitions

* `X0Dist` and `X0Gen`: the distinct and the generic main-component statements.

## Main results

* `hasPencilRealization_of_not_simple`: a pencil realization at the deficiency rank of a loopless
  multigraph on at least three bodies that is not simple, given the conditioned pair at every
  nonempty graph on fewer bodies.
-/

@[expose] public section

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

/-- **The distinct main-component statement** (`def:pencil-main-component-statements`): every simple
two-edge-connected multigraph on at least three bodies has an adjacent-distinct pencil realization
at the deficiency rank at `n = 3` (`HasDistinctPencilRealization`). `x0Dist`
(`MainComponent/Statements.lean`) proves it over an infinite field, for finite `α` and `β`. -/
def X0Dist (K : Type*) [Field K] (α β : Type*) : Prop :=
  ∀ G : Graph α β, G.Simple → 3 ≤ V(G).ncard → G.TwoEdgeConnected →
    HasDistinctPencilRealization K 3 G

/-- **The generic main-component statement** (`def:pencil-main-component-statements`): every simple
two-edge-connected multigraph on at least three bodies that is nondegeneracy-feasible
(`PencilNondegFeasible`) has a generic pencil realization at `n = 3`
(`HasGenericPencilRealization`). `x0Gen` (`MainComponent/Statements.lean`) proves it over an
infinite field, for finite `α` and `β`. -/
def X0Gen (K : Type*) [Field K] (α β : Type*) : Prop :=
  ∀ G : Graph α β, G.Simple → 3 ≤ V(G).ncard → G.TwoEdgeConnected →
    PencilNondegFeasible K G → HasGenericPencilRealization K 3 G

/-- **A multigraph with parallel edges** (`lem:pencil-nonsimple-case`; KT Lemma 6.2, p. 673): let
`G` be a loopless multigraph on at least three bodies that is not simple. If every nonempty graph on
fewer bodies than `G` satisfies the conditioned pair at `n = 3` (`hIH`), then `G` has a pencil
realization at the deficiency rank. It holds over every field and asks no minimality of `G`. It is
the `d = 3` case (`m = 1`) of `hasGradedPencilRealization_of_not_simple` (`Grade/Arms.lean`), which
carries the proof (the contraction of two parallel edges, as in KT's proof, eqs. (6.3)–(6.5),
pp. 673–674), through `hasGradedPencilRealization_two_iff`; only the bare conjunct of `hIH` is
used. -/
theorem hasPencilRealization_of_not_simple [Finite α] [Finite β]
    (G : Graph α β) (hloop : G.Loopless) (hV : 3 ≤ V(G).ncard) (hs : ¬ G.Simple)
    (hIH : ∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard → PencilPair K 3 G') :
    HasPencilRealization K 3 G := by
  exact (hasGradedPencilRealization_two_iff 3 G).1
    (hasGradedPencilRealization_of_not_simple (m := 1) G hloop hV hs
      fun G' hne hlt => (hasGradedPencilRealization_two_iff 3 G').2 (hIH G' hne hlt).2.2)

end CombinatorialRigidity.Molecular
