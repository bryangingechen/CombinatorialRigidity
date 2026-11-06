/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Arms
public import CombinatorialRigidity.Molecular.Molecule.Pencil.Pair2
public import CombinatorialRigidity.Molecular.AlgebraicInduction.DeficiencyBound

/-!
# The main-component statements, and the conditioned pair from them

The definitions and steps of `sec:pencil-main-component-route`. The two main-component statements
(`def:pencil-main-component-statements`) say that every simple two-edge-connected multigraph on at
least three bodies has an adjacent-distinct pencil realization at the deficiency rank (`X0Dist`),
and a generic one when it is nondegeneracy-feasible (`X0Gen`), at `n = 3`. Over an infinite field
they give the conditioned pair at every multigraph on the whole ambient body set
(`thm:pencil-conditional-realization-main-component`). The reduction `pencilPair_of_arms`
(`Pair2.lean`) asks only for its contraction and split cases, and one argument proves both: a graph
that is not two-edge-connected is the cut-edge case, a simple two-edge-connected one has the
conjuncts that the two statements give, and one that is not simple has the bare conjunct, a pencil
realization at the deficiency rank, by the contraction of two parallel edges
(`lem:pencil-nonsimple-case`), as in the proof of KT Lemma 6.2 (p. 673), and the other two
vacuously. `MainComponent/Statements.lean` proves the two statements (`x0Dist`, `x0Gen`), and with
them the pencil realization theorem.

## Main definitions

* `X0Dist` and `X0Gen`: the distinct and the generic main-component statements.

## Main results

* `hasPencilRealization_of_not_simple`: a pencil realization at the deficiency rank of a loopless
  multigraph on at least three bodies that is not simple, given the conditioned pair at every
  nonempty graph on fewer bodies.
* `pencilPair_of_X0`: the conditioned pair at a loopless graph on at least three bodies, from the
  two statements and the conditioned pair at every nonempty graph on fewer bodies.
* `pencil_realization_theorem_of_X0`: the conditioned pair at every multigraph on the whole ambient
  body set, from the two statements.
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

/-- **The conditioned pair from the two main-component statements, at one graph**
(`thm:pencil-conditional-realization-main-component`, the three cases of its proof): over an
infinite field, given `X0Dist` and `X0Gen`, a loopless `G` on at least three bodies satisfies
`PencilPair K 3 G` when every nonempty graph on fewer bodies does (`hIH`). If `G` is not
two-edge-connected, this is `pencilPair_of_not_twoEdgeConnected`. If it is two-edge-connected and
simple, `X0Gen` and `X0Dist` give the generic and the adjacent-distinct conjuncts, and the bare
conjunct follows from the adjacent-distinct one (`hasPencilRealization_of_distinct`). If it is
two-edge-connected and not simple, the generic and the adjacent-distinct conjuncts hold vacuously,
and `hasPencilRealization_of_not_simple` gives the bare one. -/
theorem pencilPair_of_X0 [Finite α] [Finite β] [Infinite K]
    (hdist : X0Dist K α β) (hgen : X0Gen K α β)
    (G : Graph α β) (hloop : G.Loopless) (hV : 3 ≤ V(G).ncard)
    (hIH : ∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard → PencilPair K 3 G') :
    PencilPair K 3 G := by
  have hn : Graph.bodyBarDim 3 = screwDim 2 := Graph.bodyBarDim_eq_screwDim_sub_one (by norm_num)
  by_cases h2ec : G.TwoEdgeConnected
  · by_cases hs : G.Simple
    · have hd := hdist G hs hV h2ec
      exact ⟨fun _ hf => hgen G hs hV h2ec hf, fun _ => hd, hasPencilRealization_of_distinct hd⟩
    · exact ⟨fun h => absurd h hs, fun h => absurd h hs,
        hasPencilRealization_of_not_simple G hloop hV hs hIH⟩
  · exact pencilPair_of_not_twoEdgeConnected hn h2ec hIH

/-- **The pencil realization theorem from the two main-component statements**
(`thm:pencil-conditional-realization-main-component`): over an infinite field, given `X0Dist` and
`X0Gen`, every multigraph on the whole ambient body set satisfies the conditioned pair at `n = 3`.
`pencilPair_of_arms` reduces it to the contraction and split cases, and `pencilPair_of_X0` proves
both, as it uses none of the hypotheses that distinguish them. Its hypotheses ask for no edge label
outside the graph (compare `rem:fresh-edge-supply`). -/
theorem pencil_realization_theorem_of_X0 [Nonempty α] [Finite α] [Finite β] [Infinite K]
    (hdist : X0Dist K α β) (hgen : X0Gen K α β)
    (G : Graph α β) (hspan : V(G) = Set.univ) :
    PencilPair K 3 G :=
  pencilPair_of_arms
    (fun G hloop hV _ hIH => pencilPair_of_X0 hdist hgen G hloop hV hIH)
    (fun G hloop hV _ _ _ hIH => pencilPair_of_X0 hdist hgen G hloop hV hIH) G
    (hspan ▸ Set.univ_nonempty)

end CombinatorialRigidity.Molecular
