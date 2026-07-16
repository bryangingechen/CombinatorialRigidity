/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
-- Plain (legacy) `import`, not the module system: `JacobsZeroExtension.lean` is not a `module`
-- file (it is downstream of `GeneralPositionPlacement.lean`, itself downstream of
-- `LinearRigidityMatroid.lean`'s `Matroid.Representation.Map` dependency), and a `module` file
-- cannot import a non-`module` one.
import CombinatorialRigidity.JacobsZeroExtension
import CombinatorialRigidity.SquareGraph
import CombinatorialRigidity.TwoCore

/-!
# The rank glue for the degree-one/tree formulas (`sec:jacobs-degree-one`)

Phase 32 (`sec:jacobs-degree-one`, L2 slice plan T3). Jackson–Jordán 2008's degree-one and tree
rank formulas (Lemma 4.2) both peel a degree-one vertex `v` and track how `G.square`'s generic
rank changes. This file supplies the two rank facts that peel needs: the base case (a single
edge has generic rank exactly `1`) and the inductive step (peeling a degree-one vertex `v` drops
`G.square`'s generic rank by exactly `min 3 (d_G(u))`, where `u` is `v`'s unique neighbor).

See `notes/Phase32.md` (the L2 slice plan, T3) for the phase plan.

## Main results

* `SimpleGraph.genericRank_single_edge` — a graph consisting of exactly one edge has generic
  rank `1`: the degree-≤-three `0`-extension rank formula
  (`zero_extension_genericRank_add_degree`) applied to the endpoint `x`, whose deletion leaves
  the empty graph (`Matroid.rk_empty`).
* `SimpleGraph.genericRank_square_peel` — peeling a degree-one vertex `v` (with neighbor `u`)
  drops `G.square`'s generic rank by exactly `min 3 (d_G(u))`: the clique-neighborhood
  `0`-extension rank formula (`zero_extension_genericRank_add_min_of_isClique`), applied to
  `G.square` at `v` (whose square-neighborhood is a clique of size `d_G(u)`, by
  `isClique_neighborSet_square_of_degree_eq_one` / `ncard_neighborSet_square_of_degree_eq_one`),
  composed with `square_deleteIncidenceSet_of_degree_le_one` to identify the deleted graph's
  square with the square of the deleted graph.
-/

namespace SimpleGraph

variable {V : Type*}

/-- **Generic rank of a single edge.** A graph whose entire edge set is a single edge `xy` has
generic rank exactly `1`: `x`'s neighbor set is `{y}`, of cardinality `1 ≤ 3`, so the
degree-≤-three `0`-extension rank formula applies; deleting `x`'s incident edges leaves the empty
graph, of rank `0`. -/
theorem genericRank_single_edge {G : SimpleGraph V} [Finite V] {x y : V} (hxy : x ≠ y)
    (hE : G.edgeSet = {s(x, y)}) : G.genericRank 3 = 1 := by
  have hadj : G.Adj x y := by
    have hmem : s(x, y) ∈ G.edgeSet := by simp [hE]
    exact G.mem_edgeSet.mp hmem
  have hnbr : G.neighborSet x = {y} := by
    ext u
    simp only [mem_neighborSet, Set.mem_singleton_iff]
    constructor
    · intro hu
      have hmem : s(x, u) ∈ G.edgeSet := G.mem_edgeSet.mpr hu
      rw [hE, Set.mem_singleton_iff] at hmem
      rcases Sym2.eq_iff.mp hmem with ⟨-, h⟩ | ⟨hxy', -⟩
      · exact h
      · exact absurd hxy' hxy
    · rintro rfl
      exact hadj
  have hnbr_eq : (G.neighborSet x).ncard = 1 := by rw [hnbr, Set.ncard_singleton]
  have hnbr_card : (G.neighborSet x).ncard ≤ 3 := by omega
  have hdel : (G.deleteIncidenceSet x).edgeSet = ∅ := by
    rw [edgeSet_deleteIncidenceSet, hE]
    ext e
    simp only [Set.mem_diff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨rfl, hnotinc⟩
    exact hnotinc (G.mk'_mem_incidenceSet_left_iff.mpr hadj)
  have hdelrank : (G.deleteIncidenceSet x).genericRank 3 = 0 := by
    have heq : (G.deleteIncidenceSet x).genericRank 3 =
        (genericRigidityMatroid V 3).rk (G.deleteIncidenceSet x).edgeSet := rfl
    rw [heq, hdel, Matroid.rk_empty]
  have hrank := zero_extension_genericRank_add_degree (H := G) (v := x) hnbr_card
  rw [hdelrank, hnbr_eq] at hrank
  omega

/-- **Peeling a degree-one vertex drops the squared rank by `min 3 (d_G(u))`.** If `v` has degree
one in `G` with neighbor `u`, then `G.square`'s generic rank equals `(G - E_G(v)).square`'s
generic rank plus `min 3 (d_G(u))`.

`v`'s square-neighborhood is a clique of `G.square`
(`isClique_neighborSet_square_of_degree_eq_one`), so the clique-neighborhood `0`-extension rank
formula applies to `G.square` at `v`:
`r(G.square) = r(G.square - E(v)) + min 3 |N_{G.square}(v)|`. Identify the two pieces:
`G.square.deleteIncidenceSet v = (G.deleteIncidenceSet v).square`
(`square_deleteIncidenceSet_of_degree_le_one`) and `|N_{G.square}(v)| = d_G(u)`
(`ncard_neighborSet_square_of_degree_eq_one`). -/
theorem genericRank_square_peel {G : SimpleGraph V} [Finite V] {v u : V}
    [Fintype (G.neighborSet v)] [Fintype (G.neighborSet u)] (hv : G.degree v = 1)
    (hu : G.Adj v u) :
    G.square.genericRank 3 =
      (G.deleteIncidenceSet v).square.genericRank 3 + min 3 (G.degree u) := by
  have hclique : G.square.IsClique (G.square.neighborSet v) :=
    isClique_neighborSet_square_of_degree_eq_one hv hu
  have hrank := zero_extension_genericRank_add_min_of_isClique (H := G.square) (v := v) hclique
  rw [← square_deleteIncidenceSet_of_degree_le_one hv.le,
    ncard_neighborSet_square_of_degree_eq_one hv hu] at hrank
  exact hrank

end SimpleGraph
