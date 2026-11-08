/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Generic

/-!
# The pencil realization theorem

The proof of the pencil realization theorem (`thm:pencil-realization-theorem`), over an infinite
field. The conditioned pair at every graph with at least one body (the general claim of
`thm:pencil-realization-theorem`) is the case `d = 3` of the conditioned pair in every dimension
(`Graph.graded_pencil_conditioned_pair`, `cor:pencil-d-conditioned-pair`), read through the bridges
of `lem:pencil-d-rank-agrees-three` and `lem:pencil-d-nondegenerate-three`; at a graph on the whole
ambient body set it is the pencil realization theorem.

## Main results

* `pencilPair_of_nonempty`: the general claim of `thm:pencil-realization-theorem`, the conditioned
  pair at every graph with at least one body.
* `pencil_realization_theorem`: `thm:pencil-realization-theorem`, the conditioned pair at every
  multigraph on the whole ambient body set.
-/

@[expose] public section

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

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
