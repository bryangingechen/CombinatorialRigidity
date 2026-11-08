/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Motive

/-!
# The main-component statements

The two main-component statements of `sec:pencil-main-component-route`
(`def:pencil-main-component-statements`): every simple two-edge-connected multigraph on at least
three bodies has an adjacent-distinct pencil realization at the deficiency rank (`X0Dist`), and a
generic one when it is nondegeneracy-feasible (`X0Gen`), at `n = 3`.
`MainComponent/Statements.lean` proves the two statements (`x0Dist`, `x0Gen`).

## Main definitions

* `X0Dist` and `X0Gen`: the distinct and the generic main-component statements.
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

end CombinatorialRigidity.Molecular
