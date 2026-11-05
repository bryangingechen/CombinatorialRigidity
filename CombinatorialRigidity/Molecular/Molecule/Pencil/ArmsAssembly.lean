/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Arms

/-!
# The loop, base and cut-edge cases of the pencil reduction

Three of the four cases of the induction of `sec:pencil-reduction`, for pencil realizations at the
deficiency rank (`HasPencilRealization`) and, at a cut, for adjacent-distinct ones
(`HasDistinctPencilRealization`): at a loop (`lem:pencil-loop-case`), on at most two bodies
(`lem:pencil-base-case`), and at a cut crossed by at most one edge (`lem:pencil-cut-case`). Each is
the case in every dimension (`Grade/Arms.lean`) at grade `2`, read through
`hasGradedPencilRealization_two_iff` and `hasGradedDistinctPencilRealization_two_iff`
(`lem:pencil-d-rank-agrees-three`). The fourth case, at parallel edges, is `X0.lean`.

## Main results

* `hasPencilRealization_of_isLoopAt`: the loop case (`lem:pencil-loop-case`).
* `hasPencilRealization_of_ncard_le_two`: the base case (`lem:pencil-base-case`).
* `hasPencilRealization_of_not_twoEdgeConnected` and
  `hasDistinctPencilRealization_of_not_twoEdgeConnected`: the cut-edge case, for pencil realizations
  at the deficiency rank and for adjacent-distinct ones (`lem:pencil-cut-case`).
-/

@[expose] public section

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K]
variable {α β : Type*}

/-! ## The loop case -/

/-- **The loop case** (`lem:pencil-loop-case`): let `e` be a loop of `G` at `v`. If `G ＼ {e}` has a
pencil realization at the deficiency rank (`HasPencilRealization`), so does `G`. It is the loop case
in every dimension (`hasGradedPencilRealization_of_isLoopAt`, `lem:pencil-d-loop-case`) at grade
`2`, through `hasGradedPencilRealization_two_iff`: keep the realization of `G ＼ {e}` and give `e` a
nonzero hinge in the panel of `v` through the point of `v`. The rows of a loop are zero, and
deleting a loop changes neither the bodies nor the deficiency. -/
theorem hasPencilRealization_of_isLoopAt {G : Graph α β} {n : ℕ} {e : β} {v : α}
    (hloop : G.IsLoopAt e v)
    (hrec : HasPencilRealization K n (G ＼ ({e} : Set β))) :
    HasPencilRealization K n G := by
  exact (hasGradedPencilRealization_two_iff n G).1 (hasGradedPencilRealization_of_isLoopAt hloop
    ((hasGradedPencilRealization_two_iff n _).2 hrec))

/-! ## The base case -/

/-- **The base case** (`lem:pencil-base-case`): every loopless multigraph `G` on one or two bodies
has a pencil realization at the deficiency rank, at `n = 3`, where
`Graph.bodyBarDim 3 = screwDim 2 = 6`. It is the base case in every dimension
(`hasGradedPencilRealization_of_ncard_le_two`, `lem:pencil-d-base-case`) at `m = 1`, through
`hasGradedPencilRealization_two_iff`. Its construction gives every body the same normal, and the
edges two independent hinges in that panel. With no edge the rank and the target are `0`; with one
edge they are `D - 1`; with two edges or more the deficiency is `0` and the two bodies are rigid
(`lem:theorem-55-base`), so the rank is `D`. -/
theorem hasPencilRealization_of_ncard_le_two [Finite α] [Finite β] {G : Graph α β}
    (hloop : G.Loopless) (hne : V(G).Nonempty) (hV2 : V(G).ncard ≤ 2) :
    HasPencilRealization K 3 G := by
  exact (hasGradedPencilRealization_two_iff 3 G).1
    (hasGradedPencilRealization_of_ncard_le_two (m := 1) hloop hne hV2)

/-! ## The cut-edge case -/

/-- **The two sides of a cut** (a step of `lem:pencil-cut-case`): if `G` is not `2`-edge-connected,
some nonempty `V₁ ⊂ V(G)` is crossed by at most one edge (`¬ G.TwoEdgeConnected` unfolded), and
the two sides `G[V₁]` and `G[V(G) \ V₁]` are nonempty with fewer bodies than `G`. -/
private theorem exists_cut_sides [Finite α] {G : Graph α β} (hntec : ¬ G.TwoEdgeConnected) :
    ∃ V₁ : Set α, V₁ ⊂ V(G) ∧ V₁.Nonempty ∧ (G.cutEdges V₁).ncard ≤ 1 ∧
      V(G.induce V₁).Nonempty ∧ V(G.induce V₁).ncard < V(G).ncard ∧
      V(G.induce (V(G) \ V₁)).Nonempty ∧ V(G.induce (V(G) \ V₁)).ncard < V(G).ncard := by
  simp only [Graph.TwoEdgeConnected, not_forall, not_le, exists_prop] at hntec
  obtain ⟨V₁, hne, hssub, hcut⟩ := hntec
  refine ⟨V₁, hssub, hne, Nat.lt_succ_iff.mp hcut, hne,
    Set.ncard_lt_ncard hssub (Set.toFinite _), Set.nonempty_of_ssubset hssub, ?_⟩
  have hVcard : V₁.ncard + (V(G) \ V₁).ncard = V(G).ncard := by
    rw [← Set.ncard_union_eq Set.disjoint_sdiff_right (Set.toFinite V₁) (Set.toFinite _),
      Set.union_sdiff_cancel hssub.subset]
  have := hne.ncard_pos
  change (V(G) \ V₁).ncard < V(G).ncard
  omega

/-- **The cut-edge case** (`lem:pencil-cut-case`; KT 2011 §6.1): if a multigraph `G` is not
`2`-edge-connected, and every nonempty multigraph with fewer bodies than `G` has a pencil
realization at the deficiency rank (`HasPencilRealization`), then so does `G`. Here `n = 3`
(`Graph.eq_add_one_of_bodyBarDim_eq_screwDim`), and it is the cut-edge case in every dimension
(`hasGradedPencilRealization_of_cutEdges`, `lem:pencil-d-cut-case`) at `m = 1`, through
`hasGradedPencilRealization_two_iff`, at a cut crossed by at most one edge whose two sides have
fewer bodies than `G`: realize both sides, move the second so that the crossing edge can be given a
hinge in both panels through both points, and glue. -/
theorem hasPencilRealization_of_not_twoEdgeConnected [Finite α] [Finite β] {n : ℕ}
    (hn : Graph.bodyBarDim n = screwDim 2)
    {G : Graph α β} (hntec : ¬ G.TwoEdgeConnected)
    (hIH : ∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard →
      HasPencilRealization K n G') :
    HasPencilRealization K n G := by
  have h3 : n = 3 := Graph.eq_add_one_of_bodyBarDim_eq_screwDim hn
  subst h3
  obtain ⟨V₁, hssub, hne, hcut, h₁ne, h₁lt, h₂ne, h₂lt⟩ := exists_cut_sides hntec
  exact (hasGradedPencilRealization_two_iff 3 G).1
    (hasGradedPencilRealization_of_cutEdges (m := 1) hssub hne hcut
      ((hasGradedPencilRealization_two_iff 3 _).2 (hIH _ h₁ne h₁lt))
      ((hasGradedPencilRealization_two_iff 3 _).2 (hIH _ h₂ne h₂lt)))

/-- **The cut-edge case, adjacent-distinct form** (`lem:pencil-cut-case`): if a multigraph `G` is
not `2`-edge-connected, and every nonempty `G' ≤ G` with fewer bodies than `G` has an
adjacent-distinct pencil realization at the deficiency rank (`HasDistinctPencilRealization`), then
so does `G`. It is `hasGradedDistinctPencilRealization_of_cutEdges` (`lem:pencil-d-cut-case`) at
`m = 1`, through `hasGradedDistinctPencilRealization_two_iff`, whose polarity exchanges the
independent points here with the independent normals there. The hypothesis is asked only at
subgraphs of `G`, which both sides of the cut are, so that the conditioned pair
(`pencilPair_of_not_twoEdgeConnected`, `Pair2.lean`), which gives adjacent-distinct realizations
only of simple graphs, can supply it at a simple `G`: a subgraph of a simple graph is simple. -/
theorem hasDistinctPencilRealization_of_not_twoEdgeConnected [Finite α] [Finite β] {n : ℕ}
    (hn : Graph.bodyBarDim n = screwDim 2)
    {G : Graph α β} (hntec : ¬ G.TwoEdgeConnected)
    (hIH : ∀ G' : Graph α β, G' ≤ G → V(G').Nonempty → V(G').ncard < V(G).ncard →
      HasDistinctPencilRealization K n G') :
    HasDistinctPencilRealization K n G := by
  have h3 : n = 3 := Graph.eq_add_one_of_bodyBarDim_eq_screwDim hn
  subst h3
  obtain ⟨V₁, hssub, hne, hcut, h₁ne, h₁lt, h₂ne, h₂lt⟩ := exists_cut_sides hntec
  exact (hasGradedDistinctPencilRealization_two_iff 3 G).1
    (hasGradedDistinctPencilRealization_of_cutEdges (m := 1) hssub hne hcut
      ((hasGradedDistinctPencilRealization_two_iff 3 _).2
        (hIH _ (Graph.induce_le hssub.subset) h₁ne h₁lt))
      ((hasGradedDistinctPencilRealization_two_iff 3 _).2
        (hIH _ (Graph.induce_le Set.sdiff_subset) h₂ne h₂lt)))

end CombinatorialRigidity.Molecular
