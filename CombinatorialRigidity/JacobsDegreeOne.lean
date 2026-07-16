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
import CombinatorialRigidity.Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import CombinatorialRigidity.Mathlib.Combinatorics.SimpleGraph.Acyclic
import CombinatorialRigidity.Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# The rank glue for the degree-one/tree formulas (`sec:jacobs-degree-one`)

Phase 32 (`sec:jacobs-degree-one`, L2 slice plan T3–T4). Jackson–Jordán 2008's degree-one and
tree rank formulas (Lemma 4.2) both peel a degree-one vertex `v` and track how `G.square`'s
generic rank changes. This file supplies the two rank facts that peel needs (T3): the base case
(a single edge has generic rank exactly `1`) and the inductive step (peeling a degree-one vertex
`v` drops `G.square`'s generic rank by exactly `min 3 (d_G(u))`, where `u` is `v`'s unique
neighbor); and (T4) assembles the tree rank formula itself, by strong induction on the edge
count over a fixed vertex type `V` (`fmlnote:degree-one-fixed-carrier`): peeling a leaf keeps it
in `V` as an isolated vertex, so the induction runs on a support-relative strengthening rather
than a type-changing one.

See `notes/Phase32.md` (the L2 slice plan, T3–T4) for the phase plan.

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
* `SimpleGraph.degree_one_rank_tree` — `thm:degree-one-rank-tree` (JJ Lemma 4.2(a), due to
  Franzblau 2000 for trees): a tree's squared rank is `2|V| - 5 + |V_1(G)|`.
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

/-! ## The tree rank formula (`thm:degree-one-rank-tree`)

Jackson–Jordán 2008 Lemma 4.2(a) (due to Franzblau 2000 for trees): a tree's squared rank is
`2|V| - 5 + |V_1(G)|`, where `V_1(G)` is the set of degree-one vertices. The induction runs on
a *fixed* vertex type `V`, over a support-relative strengthening
(`fmlnote:degree-one-fixed-carrier`): `|V|` is read as the size of the support, connectivity as
reachability between support vertices, so peeling a leaf's incident edges just leaves it
isolated in `V` rather than forcing a type-changing induction. -/

/-- **The degree-one rank formula for trees, by strong induction on the edge count** (private
strengthening of `degree_one_rank_tree`). Base case, two support vertices `a, b`: any neighbor
of a support vertex is itself a support vertex, so `a`'s only possible neighbor is `b`, giving
`G.Adj a b`; squaring adds nothing new (every edge of `G.square` has both endpoints in the
support, hence in `{a, b}`), so `genericRank_single_edge` applies directly to `G.square`, and
`{a, b}` is exactly the degree-one set. Step, at least three support vertices: peel a leaf `v`
with neighbor `u` (`exists_degree_eq_one`); `d_G(u) ≥ 2` (`two_le_degree_of_adj_degree_eq_one`),
so the peel (`genericRank_square_peel`) drops the rank by `min 3 (d_G(u))`, matched by the drop
in `2 * |support| + |V_1(G)|` via the T2 maintenance identities
(`support_deleteIncidenceSet_of_degree_eq_one`,
`setOf_degree_eq_one_deleteIncidenceSet_of_three_le_degree` /
`setOf_degree_eq_one_deleteIncidenceSet_of_degree_eq_two`). -/
private theorem degree_one_rank_tree_of_ncard [Fintype V] :
    ∀ n, ∀ (G : SimpleGraph V) [DecidableRel G.Adj], G.edgeSet.ncard = n →
    (∀ x ∈ G.support, ∀ y ∈ G.support, G.Reachable x y) →
    G.IsAcyclic → 2 ≤ G.support.ncard →
    G.square.genericRank 3 + 5 = 2 * G.support.ncard + {w | G.degree w = 1}.ncard := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ hn hconn hac h2
    by_cases h3 : 3 ≤ G.support.ncard
    · -- Step: peel a leaf `v` with neighbor `u`.
      obtain ⟨v, hvsupp, hv1⟩ := exists_degree_eq_one hconn hac (by omega)
      obtain ⟨u, hu⟩ := (G.degree_pos_iff_exists_adj v).mp (by omega)
      have hu2 : 2 ≤ G.degree u := two_le_degree_of_adj_degree_eq_one hconn h3 hv1 hu
      have hproper : (G.deleteIncidenceSet v).edgeSet ⊂ G.edgeSet := by
        rw [edgeSet_deleteIncidenceSet]
        exact Set.ssubset_iff_of_subset Set.diff_subset |>.mpr
          ⟨s(v, u), hu, fun hc => hc.2 (G.mem_incidenceSet v u |>.mpr hu)⟩
      have hcard_lt : (G.deleteIncidenceSet v).edgeSet.ncard < n := by
        rw [← hn]; exact Set.ncard_lt_ncard hproper
      have hsupp' : (G.deleteIncidenceSet v).support = G.support \ {v} :=
        support_deleteIncidenceSet_of_degree_eq_one hv1 hu hu2
      have hconn' : ∀ x ∈ (G.deleteIncidenceSet v).support, ∀ y ∈ (G.deleteIncidenceSet v).support,
          (G.deleteIncidenceSet v).Reachable x y := by
        intro x hx y hy
        rw [hsupp'] at hx hy
        exact reachable_deleteIncidenceSet hv1.le hx.2 hy.2 (hconn x hx.1 y hy.1)
      have hac' : (G.deleteIncidenceSet v).IsAcyclic := hac.anti (G.deleteIncidenceSet_le v)
      have hsupp_card : (G.deleteIncidenceSet v).support.ncard + 1 = G.support.ncard := by
        rw [hsupp']; exact Set.ncard_diff_singleton_add_one hvsupp
      have h2' : 2 ≤ (G.deleteIncidenceSet v).support.ncard := by omega
      have hIH := ih (G.deleteIncidenceSet v).edgeSet.ncard hcard_lt (G.deleteIncidenceSet v) rfl
        hconn' hac' h2'
      have hpeel := genericRank_square_peel (G := G) hv1 hu
      rcases lt_or_ge (G.degree u) 3 with hlt3 | hge3
      · have hueq2 : G.degree u = 2 := by omega
        have hminEq : min 3 (G.degree u) = 2 := by omega
        have hunotmem : u ∉ ({w | G.degree w = 1} \ {v}) := by
          rintro ⟨h1, -⟩
          simp only [Set.mem_setOf_eq] at h1
          omega
        have hcardEq : {w | (G.deleteIncidenceSet v).degree w = 1}.ncard =
            {w | G.degree w = 1}.ncard := by
          rw [setOf_degree_eq_one_deleteIncidenceSet_of_degree_eq_two hv1 hu hueq2,
            Set.ncard_insert_of_notMem hunotmem]
          exact Set.ncard_diff_singleton_add_one hv1
        omega
      · have hminEq : min 3 (G.degree u) = 3 := by omega
        have hcardEq : {w | (G.deleteIncidenceSet v).degree w = 1}.ncard + 1 =
            {w | G.degree w = 1}.ncard := by
          rw [setOf_degree_eq_one_deleteIncidenceSet_of_three_le_degree hv1 hu hge3]
          exact Set.ncard_diff_singleton_add_one hv1
        omega
    · -- Base case: exactly two support vertices.
      have heq2 : G.support.ncard = 2 := by omega
      obtain ⟨a, b, hne, hsupp⟩ := Set.ncard_eq_two.mp heq2
      have hamem : a ∈ G.support := by rw [hsupp]; exact Set.mem_insert a {b}
      obtain ⟨c, hac0⟩ := (mem_support G).mp hamem
      have hcmem : c ∈ ({a, b} : Set V) := by rw [← hsupp]; exact hac0.right_mem_support
      have hcb : c = b := by
        rcases hcmem with hca | hcb
        · exact absurd hca.symm hac0.ne
        · exact hcb
      have hadj : G.Adj a b := by rw [← hcb]; exact hac0
      have hsquare_edge : G.square.edgeSet = ({s(a, b)} : Set (Sym2 V)) := by
        ext e
        induction e using Sym2.ind with
        | h x y =>
          simp only [mem_edgeSet, Set.mem_singleton_iff, Sym2.eq_iff]
          constructor
          · intro hadj_sq
            have hxmem : x ∈ ({a, b} : Set V) := by
              rw [← hsupp]; exact square_support_subset G hadj_sq.left_mem_support
            have hymem : y ∈ ({a, b} : Set V) := by
              rw [← hsupp]; exact square_support_subset G hadj_sq.right_mem_support
            rcases hxmem with rfl | rfl <;> rcases hymem with rfl | rfl
            · exact absurd rfl hadj_sq.ne
            · exact Or.inl ⟨rfl, rfl⟩
            · exact Or.inr ⟨rfl, rfl⟩
            · exact absurd rfl hadj_sq.ne
          · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
            · exact le_square G hadj
            · exact (le_square G hadj).symm
      have hrank1 : G.square.genericRank 3 = 1 := genericRank_single_edge hne hsquare_edge
      have hnbr_a : G.neighborSet a = {b} := by
        ext x
        simp only [mem_neighborSet, Set.mem_singleton_iff]
        constructor
        · intro hx
          have hxmem : x ∈ ({a, b} : Set V) := by rw [← hsupp]; exact hx.right_mem_support
          rcases hxmem with rfl | rfl
          · exact absurd rfl hx.ne
          · rfl
        · rintro rfl; exact hadj
      have hnbr_b : G.neighborSet b = {a} := by
        ext x
        simp only [mem_neighborSet, Set.mem_singleton_iff]
        constructor
        · intro hx
          have hxmem : x ∈ ({a, b} : Set V) := by rw [← hsupp]; exact hx.right_mem_support
          rcases hxmem with rfl | rfl
          · rfl
          · exact absurd rfl hx.ne
        · rintro rfl; exact hadj.symm
      have hdeg_a : G.degree a = 1 := by
        rw [← ncard_neighborSet_eq_degree, hnbr_a, Set.ncard_singleton]
      have hdeg_b : G.degree b = 1 := by
        rw [← ncard_neighborSet_eq_degree, hnbr_b, Set.ncard_singleton]
      have hset_eq : {w | G.degree w = 1} = ({a, b} : Set V) := by
        ext w
        simp only [Set.mem_setOf_eq]
        constructor
        · intro hw
          have hwmem : w ∈ G.support := (G.degree_pos_iff_mem_support w).mp (by omega)
          rwa [hsupp] at hwmem
        · rintro (rfl | rfl)
          · exact hdeg_a
          · exact hdeg_b
      have hcard1 : {w | G.degree w = 1}.ncard = 2 := by rw [hset_eq]; exact Set.ncard_pair hne
      omega

/-- **The degree-one rank formula for trees** (`thm:degree-one-rank-tree`; JJ Lemma 4.2(a), due
to Franzblau 2000 for trees). Let `G` be a tree on a finite vertex set `V` with `|V| ≥ 2`. Then
`r(G²) = 2|V| - 5 + |V_1(G)|`.

A connected graph on at least two vertices has support all of `V`
(`Preconnected.support_eq_univ`), so the strengthened form `degree_one_rank_tree_of_ncard`, run
at `n := G.edgeSet.ncard`, gives exactly this. -/
theorem degree_one_rank_tree {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj] (hG : G.IsTree)
    (h2 : 2 ≤ Fintype.card V) :
    G.square.genericRank 3 + 5 = 2 * Fintype.card V + {w | G.degree w = 1}.ncard := by
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hsupp_univ : G.support = Set.univ := hG.connected.preconnected.support_eq_univ
  have hconn : ∀ x ∈ G.support, ∀ y ∈ G.support, G.Reachable x y :=
    fun x _ y _ => hG.connected x y
  have hcard : G.support.ncard = Fintype.card V := by
    rw [hsupp_univ, Set.ncard_univ, Nat.card_eq_fintype_card]
  have h2' : 2 ≤ G.support.ncard := by omega
  have hthis := degree_one_rank_tree_of_ncard G.edgeSet.ncard G rfl hconn hG.isAcyclic h2'
  rwa [hcard] at hthis

end SimpleGraph
