/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.X0
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.GenericBase
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.GenericEar
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.GenericTriangle
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.GoodEar

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

The generic statement is proved inside the induction of the pencil reduction, from the conditioned
pair at every graph on fewer bodies, at least one (`thm:pencil-generic-step`). A graph with no
planar-rigid set has a generic realization (`thm:pencil-x0-base-generic`,
`MainComponent/GenericBase.lean`), and so has one on three bodies, a triangle, by a direct
construction (`MainComponent/GenericTriangle.lean`). Otherwise a minimal planar-rigid set gives a
body of degree two whose neighbours are pencil hubs, or a pendant triangle
(`lem:pencil-rigid-good-ear`, `MainComponent/GoodEar.lean`), across which the generic realization of
the smaller graph extends (`lem:pencil-generic-one-ear`, `lem:pencil-generic-pendant-triangle`;
`MainComponent/GenericEar.lean`, `MainComponent/GenericTriangle.lean`). So every graph with at least
one body satisfies the conditioned pair (`thm:pencil-conditioned-pair-nonempty`), the generic
statement is its generic conjunct (`thm:pencil-x0-generic-attains`), and the pencil realization
theorem follows from the two statements (`thm:pencil-conditional-realization-main-component`).

## Main results

* `x0Dist`: `lem:pencil-x0-distinct-statement`, the distinct main-component statement.
* `hasGenericPencilRealization_of_IH`: `thm:pencil-generic-step`, the generic conjunct from the
  induction hypothesis.
* `pencilPair_of_IH` and `pencilPair_of_nonempty`: `thm:pencil-conditioned-pair-nonempty`, the
  conditioned pair at one graph from the induction hypothesis, and at every graph with at least one
  body.
* `x0Gen`: `thm:pencil-x0-generic-attains`, the generic main-component statement.
* `pencil_realization_theorem`: `thm:pencil-realization-theorem`, the conditioned pair at every
  multigraph on the whole ambient body set.
-/

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

/-- **The generic conjunct from the induction hypothesis** (`thm:pencil-generic-step`): let `K` be
infinite and `G` simple and two-edge-connected on at least three bodies, and nondegeneracy-feasible,
and suppose that every graph on fewer bodies, at least one, satisfies the conditioned pair at
`n = 3` (`hIH`). Then `G` has a generic pencil realization.

Proof. As a simple two-edge-connected graph on at least three bodies, `G` satisfies the standing
hypotheses: it is connected (`Graph.preconnected_of_twoEdgeConnected`), with every degree at least
two (`Graph.two_le_degree_of_twoEdgeConnected`). If it has no planar-rigid set, it has a generic
realization (`Graph.IsX0Graph.hasGenericPencilRealization_of_forall_deficiency_two_ne_zero`,
`thm:pencil-x0-base-generic`). On three bodies it is a triangle, which has one by a direct
construction (`pencilPair_of_simple_ncard_eq_three`). Otherwise it has at least four bodies, its
closed hub-neighbourhoods have at most three members and no triangle contains two hubs
(`PencilNondegFeasible.hub_conditions`, `lem:pencil-feasible-hub-conditions`), so it has a one-body
ear whose ends are pencil hubs and whose removal does not raise the deficiency, or a pendant
triangle (`Graph.IsX0Graph.exists_oneEar_or_pendantTriangle`, `lem:pencil-rigid-good-ear`). Removing
the body of the ear, or the two bodies of degree two of the triangle, leaves a simple graph `G[V₁]`
with fewer bodies, at least one. By `hIH` it has a generic realization whenever it is
nondegeneracy-feasible, so `G` has one (`Graph.IsOpenEar.hasGenericPencilRealization_of_one`,
`lem:pencil-generic-one-ear`; `hasGenericPencilRealization_of_closedEar_two`,
`lem:pencil-generic-pendant-triangle`). -/
theorem hasGenericPencilRealization_of_IH [Infinite K] [Finite α] [Finite β] {G : Graph α β}
    (hS : G.Simple) (hV : 3 ≤ V(G).ncard) (htec : G.TwoEdgeConnected)
    (hfeas : PencilNondegFeasible K G)
    (hIH : ∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard → PencilPair K 3 G') :
    HasGenericPencilRealization K 3 G := by
  have hG : G.IsX0Graph :=
    { simple := hS
      connected := Graph.connected_iff.mpr ⟨Set.nonempty_of_ncard_ne_zero (by omega),
        Graph.preconnected_of_twoEdgeConnected htec⟩
      two_le_degree := fun v hv => Graph.two_le_degree_of_twoEdgeConnected htec hv (by omega) }
  by_cases hrig : ∃ Y ⊆ V(G), 2 ≤ Y.ncard ∧ (G.induce Y).deficiency 2 = 0
  swap
  · push Not at hrig
    exact hG.hasGenericPencilRealization_of_forall_deficiency_two_ne_zero hfeas hrig
  by_cases h3 : V(G).ncard = 3
  · exact (pencilPair_of_simple_ncard_eq_three hS h3 htec).1 hS hfeas
  obtain ⟨hF1, hF2⟩ := hfeas.hub_conditions
  rcases hG.exists_oneEar_or_pendantTriangle htec (by omega) hF1 hF2 hrig with
    ⟨V₁, x, a, b, e, hear, ha, hb, hdef⟩ |
    ⟨V₁, x, c, e, hcover, -, hxV₁, hc, hpath, hsep, hdeg⟩
  · have hS₁ : (G.induce V₁).Simple :=
      hS.mono (Graph.induce_le (hear.cover ▸ Set.subset_union_left))
    have hlt : V(G.induce V₁).ncard < V(G).ncard := hear.ncard_lt le_rfl
    have hne : V(G.induce V₁).Nonempty := ⟨a, hear.left_mem⟩
    exact hear.hasGenericPencilRealization_of_one hS hfeas ha hb hdef
      ((hIH _ hne hlt).1 hS₁)
  · have hS₁ : (G.induce V₁).Simple := hS.mono (Graph.induce_le (hcover ▸ Set.subset_union_left))
    have hlt : V(G.induce V₁).ncard < V(G).ncard := by
      rw [Graph.vertexSet_induce]
      refine Set.ncard_lt_ncard ?_
      refine (Set.ssubset_iff_of_subset (hcover ▸ Set.subset_union_left)).mpr
        ⟨x 0, ?_, hxV₁ 0⟩
      rw [hcover]
      exact Set.mem_union_right _ ⟨_, rfl⟩
    have hne : V(G.induce V₁).Nonempty := ⟨c, hc⟩
    exact hasGenericPencilRealization_of_closedEar_two hS hfeas hcover hxV₁ hc hpath hsep hdeg
      ((hIH _ hne hlt).1 hS₁)

/-- **The conditioned pair at one graph from the induction hypothesis**
(`thm:pencil-conditioned-pair-nonempty`, the step of its proof): over an infinite field, a loopless
`G` on at least three bodies satisfies the conditioned pair at `n = 3` when every nonempty graph on
fewer bodies does (`hIH`). The proof is `pencilPair_of_X0`'s, with the generic statement replaced by
`hasGenericPencilRealization_of_IH`. If `G` is not two-edge-connected, this is
`pencilPair_of_not_twoEdgeConnected`. If it is two-edge-connected and simple,
`hasGenericPencilRealization_of_IH` and `x0Dist` give the generic and the adjacent-distinct
conjuncts, and the bare conjunct follows from the adjacent-distinct one
(`hasPencilRealization_of_distinct`). If it is two-edge-connected and not simple, the generic and
the adjacent-distinct conjuncts hold vacuously, and `hasPencilRealization_of_not_simple` gives the
bare one. -/
theorem pencilPair_of_IH [Finite α] [Finite β] [Infinite K]
    (G : Graph α β) (hloop : G.Loopless) (hV : 3 ≤ V(G).ncard)
    (hIH : ∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard → PencilPair K 3 G') :
    PencilPair K 3 G := by
  have hn : Graph.bodyBarDim 3 = screwDim 2 := Graph.bodyBarDim_eq_screwDim_sub_one (by norm_num)
  by_cases h2ec : G.TwoEdgeConnected
  · by_cases hs : G.Simple
    · have hd := x0Dist (K := K) G hs hV h2ec
      exact ⟨fun _ hf => hasGenericPencilRealization_of_IH hs hV h2ec hf hIH, fun _ => hd,
        hasPencilRealization_of_distinct hd⟩
    · exact ⟨fun h => absurd h hs, fun h => absurd h hs,
        hasPencilRealization_of_not_simple G hloop hV hs hIH⟩
  · exact pencilPair_of_not_twoEdgeConnected hn h2ec hIH

/-- **The conditioned pair at every nonempty multigraph** (`thm:pencil-conditioned-pair-nonempty`,
and the general claim of `thm:pencil-realization-theorem`): over an infinite field, for finite `α`
and `β`, every graph with at least one body satisfies the conditioned pair at `n = 3`. The reduction
`pencilPair_of_arms` (`thm:pencil-conditional-realization-pair`) asks for its contraction and split
cases, and `pencilPair_of_IH` proves both, as it uses none of the hypotheses that distinguish them.
-/
theorem pencilPair_of_nonempty [Finite α] [Finite β] [Infinite K] (G : Graph α β)
    (hne : V(G).Nonempty) : PencilPair K 3 G :=
  pencilPair_of_arms (fun G hloop hV _ hIH => pencilPair_of_IH G hloop hV hIH)
    (fun G hloop hV _ _ _ hIH => pencilPair_of_IH G hloop hV hIH) G hne

/-- **The generic main-component statement** (`thm:pencil-x0-generic-attains`, its generic
statement): over an infinite field, for finite `α` and `β`, every simple two-edge-connected
multigraph on at least three bodies that is nondegeneracy-feasible has a generic pencil realization
at `n = 3` (`X0Gen`), the generic conjunct of the conditioned pair at it (`pencilPair_of_nonempty`).
-/
theorem x0Gen [Finite α] [Finite β] [Infinite K] : X0Gen K α β :=
  fun G hS hV _ hfeas =>
    (pencilPair_of_nonempty G (Set.nonempty_of_ncard_ne_zero (by omega))).1 hS hfeas

/-- **The pencil realization theorem** (`thm:pencil-realization-theorem`): over an infinite field,
for finite `α` and `β` with `α` nonempty, every multigraph on the whole ambient body set satisfies
the conditioned pair at `n = 3`. It is `pencil_realization_theorem_of_X0`
(`thm:pencil-conditional-realization-main-component`) at the two main-component statements, now
proved (`x0Dist`, `x0Gen`), so it assumes neither. -/
theorem pencil_realization_theorem [Nonempty α] [Finite α] [Finite β] [Infinite K]
    (G : Graph α β) (hspan : V(G) = Set.univ) : PencilPair K 3 G :=
  pencil_realization_theorem_of_X0 x0Dist x0Gen G hspan

end CombinatorialRigidity.Molecular
