/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Mathlib.Combinatorics.Graph.Delete
import CombinatorialRigidity.Molecular.Molecule.Pencil.Arms

/-!
# Nondegenerate pencil realizations and the conditioned pair

The definitions of `sec:pencil-nondegenerate`, and the facts about them that the induction of the
conditioned pair uses. A pencil hub is a body of degree at least three, and a pencil realization is
nondegenerate when the points at the two ends of every link are independent, the normals of the hubs
among each body and its neighbours are independent, and, at each body that is not a hub, the points
of the body and its neighbours are independent (`def:pencil-nondegenerate`). The conditioned pair
asks of a multigraph a pencil realization at the deficiency rank, an adjacent-distinct one when it
is simple, and a nondegenerate one at the deficiency rank when it is also nondegeneracy-feasible
(`def:pencil-generic-motive`, `def:pencil-conditioned-pair`).

The file also proves that a graph with a loop is not nondegeneracy-feasible; that a nondegenerate
realization restricts to a subgraph, except at a hub of the graph that is not one of the subgraph,
and moves by a linear automorphism of `K⁴` and a contragredient of it; that the point of a body is
orthogonal to the normals of its closed neighbourhood, so that a feasible graph has at most three
members in each closed hub-neighbourhood and no triangle with two hubs
(`lem:pencil-feasible-hub-conditions`); and that two hubs with three common neighbours whose points
are independent have no nondegenerate realization (`lem:pencil-x0-two-hubs-obstruction`). The last
sections compare the degrees and neighbourhoods of a graph with those of the sides of a cut crossed
by at most one edge, for the cut-edge case of the conditioned pair (`lem:pencil-pair-loop-base-cut`,
case (3)): a side with the far end of the crossing edge, a side that no edge leaves, and the side
opposite a single body.

## Main definitions

* `Graph.PencilHub`, `Graph.closedHubNbhd`, `Graph.closedNbhd`, `IsNondegPencilRealization` and
  `PencilNondegFeasible`: pencil hubs, closed hub-neighbourhoods, closed neighbourhoods,
  nondegenerate pencil realizations and nondegeneracy-feasibility (`def:pencil-nondegenerate`).
* `HasGenericPencilRealization`: a generic pencil realization (`def:pencil-generic-motive`).
* `PencilPair`: the conditioned pair (`def:pencil-conditioned-pair`).

## Main results

* `Graph.three_le_ncard_closedNbhd`: in a simple graph, a body of degree at least two has at least
  three members in its closed neighbourhood (`def:pencil-x0-standing`).
* `PencilNondegFeasible.hub_conditions`: a feasible graph has at most three members in each closed
  hub-neighbourhood, and no triangle with two pencil hubs (`lem:pencil-feasible-hub-conditions`).
* `not_isNondegPencilRealization_of_two_hubs_three_common`: two hubs with three common neighbours
  whose points are independent have no nondegenerate realization
  (`lem:pencil-x0-two-hubs-obstruction`).
* `Graph.deficiency_induce_union_singleton`: the deficiency of a side of a cut crossed by one edge,
  with the far end of that edge, is that of the side plus one (`lem:cut-edge-decomposition`, (3)).
-/

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K]
variable {α β : Type*}

/-! ## Nondegenerate realizations and the conditioned pair

The definitions of `def:pencil-nondegenerate`, `def:pencil-generic-motive` and
`def:pencil-conditioned-pair`, the bound on closed neighbourhoods behind the standing hypotheses of
`sec:main-component` (`def:pencil-x0-standing`), and the maps between the three kinds of realization
at the deficiency rank. -/

/-- **A pencil hub** (`def:pencil-nondegenerate`): a body of `G` of degree at least three. The
pencil condition constrains the hinges at a body only at a hub: two nonzero hinges in one panel pass
through a common nonzero point of it (`exists_concurrency_point_of_extensorInPanel_pair`). -/
def _root_.Graph.PencilHub (G : Graph α β) (v : α) : Prop :=
  v ∈ V(G) ∧ 3 ≤ G.degree v

/-- **The closed hub-neighbourhood of `v`** (`def:pencil-nondegenerate`): the pencil hubs among `v`
and the bodies linked to it. At a pencil realization the point of a body `v` is orthogonal to the
normal of each of them, as to that of every member of the closed neighbourhood `G.closedNbhd v`
(`dotProduct_point_eq_zero_of_mem_closedNbhd`), so that at a nondegenerate one each closed
hub-neighbourhood has at most three members
(`ncard_closedHubNbhd_le_three_of_isNondegPencilRealization`). -/
def _root_.Graph.closedHubNbhd (G : Graph α β) (v : α) : Set α :=
  {w | G.PencilHub w ∧ (w = v ∨ ∃ e, G.IsLink e v w)}

/-- **The closed neighbourhood of `v`** (`def:pencil-nondegenerate`): `v` and the bodies linked to
it, hubs or not (`G.closedHubNbhd v` keeps the hubs among them). `IsNondegPencilRealization` asks
for independent points on it at each body that is not a hub, where it has at most three members
(`ncard_closedNbhd_le_three_of_not_pencilHub`). -/
def _root_.Graph.closedNbhd (G : Graph α β) (v : α) : Set α :=
  {w | w = v ∨ ∃ e, G.IsLink e v w}

/-- **The closed neighbourhood of a body of `G` lies in `V(G)`** (a step of
`thm:pencil-jj-equality`, whose proof names it, and of many lemmas of `sec:main-component`). -/
theorem _root_.Graph.closedNbhd_subset_vertexSet {G : Graph α β} {v : α} (hv : v ∈ V(G)) :
    G.closedNbhd v ⊆ V(G) := by
  rintro w (rfl | ⟨e, he⟩)
  · exact hv
  · exact he.right_mem

/-- **In a simple graph, a body of degree at least two has at least three members in its closed
neighbourhood** (`def:pencil-x0-standing`): its neighbours, which in a simple graph are as many as
its degree, and itself, which is none of them, as `G` has no loops. From it
`Graph.IsX0Graph.three_le_ncard_closedNbhd` (`MainComponent/Cut.lean`) gives the bound of the
standing hypotheses. -/
theorem _root_.Graph.three_le_ncard_closedNbhd [Finite α] {G : Graph α β} (hS : G.Simple)
    {v : α} (hdeg : 2 ≤ G.degree v) : 3 ≤ (G.closedNbhd v).ncard := by
  have hnot : v ∉ N(G, v) := fun h => by
    obtain ⟨e, he⟩ := h
    exact hS.toLoopless.not_isLoopAt e v he
  have heq : G.closedNbhd v = insert v (N(G, v)) := rfl
  rw [heq, Set.ncard_insert_of_notMem hnot (Set.toFinite _), ← Graph.degree_eq_ncard_adj]
  omega

/-- **A nondegenerate pencil realization** (`def:pencil-nondegenerate`): a pencil realization
(`HasPencilPanelRealization`) of `G` whose points at the two ends of every link are linearly
independent, whose normals are linearly independent on the closed hub-neighbourhood
(`Graph.closedHubNbhd`) of every body, and whose points are linearly independent on the closed
neighbourhood (`Graph.closedNbhd`) of every body that is not a pencil hub. It is the pencil analogue
of the nonparallel realization that Katoh and Tanigawa ask of a simple graph (KT 2011, Theorem 5.5,
p. 670).

The last condition is not asked at a hub: there the points lie in the panel of the body
(`dotProduct_normal_eq_zero_of_mem_closedNbhd`), of dimension `3`, and a hub of a simple graph has
at least four members in its closed neighbourhood. At a body that is not a hub, it follows from the
independence of adjacent points and from the nonzero point of the body, unless the body has two
distinct neighbours. There it asks that the two hinges at the body be distinct lines, which the
first two conditions do not imply: the path on three bodies has a pencil realization whose three
points are distinct and collinear, and both of its hinges are then the line through them. -/
def IsNondegPencilRealization (G : Graph α β) (F : BodyHingeFramework K 2 α β)
    (normal point : α → Fin 4 → K) : Prop :=
  HasPencilPanelRealization G F normal point ∧
  (∀ e u v, G.IsLink e u v → LinearIndependent K ![point u, point v]) ∧
  (∀ v ∈ V(G), LinearIndepOn K normal (G.closedHubNbhd v)) ∧
  (∀ v ∈ V(G), ¬ G.PencilHub v → LinearIndepOn K point (G.closedNbhd v))

/-- **Nondegeneracy-feasibility** (`def:pencil-nondegenerate`): `G` has a nondegenerate pencil
realization (`IsNondegPencilRealization`) over `K`. With `G.Simple`, it is the condition under which
`PencilPair` asks for a generic realization, and neither condition can be dropped. `K₄` is simple
and not feasible, as each of its closed hub-neighbourhoods has four members
(`ncard_closedHubNbhd_le_three_of_isNondegPencilRealization`). Two bodies joined by two edges are
feasible (`exists_isNondegPencilRealization_parallel_pair`, `Pair.lean`) and not simple
(`not_simple_of_parallel`), and no nondegenerate realization of them attains the deficiency rank:
their points are independent, so both hinges are the line through them, and the rank is `5`, not
`6`. -/
def PencilNondegFeasible (K : Type*) [Field K] (G : Graph α β) : Prop :=
  ∃ (F : BodyHingeFramework K 2 α β) (normal point : α → Fin 4 → K),
    IsNondegPencilRealization G F normal point

/-- **A generic pencil realization** (`def:pencil-generic-motive`): a nondegenerate pencil
realization (`IsNondegPencilRealization`) of `G` whose rigidity rows span a space of dimension
`screwDim 2 * (|V(G)| - 1) - G.deficiency n`, in `ℤ`, as in `HasPencilRealization`; the pencil form
of `HasGenericFullRankRealization`. Generic names the property, not an algebraic independence of the
coordinates. -/
def HasGenericPencilRealization (K : Type*) [Field K] (n : ℕ) (G : Graph α β) : Prop :=
  ∃ (F : BodyHingeFramework K 2 α β) (normal point : α → Fin 4 → K),
    IsNondegPencilRealization G F normal point ∧
    (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
      = screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency n

/-- **The conditioned pair** (`def:pencil-conditioned-pair`): `G` has a pencil realization at the
deficiency rank (`HasPencilRealization`); if `G` is simple, an adjacent-distinct one
(`HasDistinctPencilRealization`); and if `G` is simple and nondegeneracy-feasible
(`PencilNondegFeasible`), a generic one (`HasGenericPencilRealization`). It has the form of the
statement of the induction of KT Theorem 5.5 in `Theorem55.lean`,
`(G.Simple → HasGenericFullRankRealization K k n G) ∧ HasPanelRealization K k n G`, with feasibility
added to the condition of the generic conjunct (neither condition suffices alone:
`PencilNondegFeasible`), and with the adjacent-distinct conjunct.

The adjacent-distinct conjunct asks only that `G` be simple. Two bodies joined by two edges, which
are not simple, have no adjacent-distinct realization at the deficiency rank: both hinges would be
the line through the two points (`HasDistinctPencilRealization`). -/
def PencilPair (K : Type*) [Field K] (n : ℕ) (G : Graph α β) : Prop :=
  (G.Simple → PencilNondegFeasible K G → HasGenericPencilRealization K n G) ∧
    (G.Simple → HasDistinctPencilRealization K n G) ∧
    HasPencilRealization K n G

/-- **Two edges with the same ends make a graph not simple** (a step of
`lem:pencil-pair-loop-base-cut`, case (2)): distinct `e` and `f` that both link `x` and `y`
contradict `Graph.Simple.eq_of_isLink`. So a simple graph on two bodies has at most one edge
(`hasGenericPencilRealization_of_ncard_le_two`, `Pair.lean`). -/
theorem not_simple_of_parallel {G : Graph α β} {e f : β} {x y : α}
    (hef : e ≠ f) (hl_e : G.IsLink e x y) (hl_f : G.IsLink f x y) : ¬ G.Simple :=
  fun hSimple => hef (hSimple.eq_of_isLink hl_e hl_f)

/-- **A generic pencil realization is adjacent-distinct** (the remark after
`def:pencil-distinct-motive`): keep the realization, the independence of the points at the two ends
of every link and the rank, and forget the other two conditions of nondegeneracy. -/
theorem hasDistinctPencilRealization_of_generic {n : ℕ} {G : Graph α β}
    (h : HasGenericPencilRealization K n G) : HasDistinctPencilRealization K n G := by
  obtain ⟨F, normal, point, ⟨hreal, hadj, _, _⟩, hrank⟩ := h
  exact ⟨F, normal, point, hreal, hadj, hrank⟩

/-- **A generic pencil realization is one at the deficiency rank** (the remark after
`def:pencil-distinct-motive`): forget the three conditions of nondegeneracy
(`IsNondegPencilRealization`), through the adjacent-distinct realization
(`hasDistinctPencilRealization_of_generic`, `hasPencilRealization_of_distinct`). The pencil form of
`hasPanelRealization_of_generic`. -/
theorem hasPencilRealization_of_generic {n : ℕ} {G : Graph α β}
    (h : HasGenericPencilRealization K n G) : HasPencilRealization K n G :=
  hasPencilRealization_of_distinct (hasDistinctPencilRealization_of_generic h)

/-- **A graph with a loop is not nondegeneracy-feasible** (a step of
`lem:pencil-pair-loop-base-cut`, case (1)): a loop `e` at `v` is a link `G.IsLink e v v`, at which
`IsNondegPencilRealization` asks that `![point v, point v]` be linearly independent, while
`1 • point v + (-1) • point v = 0` (`LinearIndependent.pair_iff`). `pencilPair_of_isLoopAt`
(`Pair.lean`) discharges with it the generic conjunct of `PencilPair` at a graph with a loop, which
is also not simple. -/
theorem not_pencilNondegFeasible_of_isLoopAt {G : Graph α β} {e : β} {v : α}
    (hloop : G.IsLoopAt e v) : ¬ PencilNondegFeasible K G := by
  rintro ⟨F, normal, point, _, hLI, _, _⟩
  have h := (LinearIndependent.pair_iff).1 (hLI e v v hloop) 1 (-1)
    (by rw [one_smul, neg_one_smul, add_neg_cancel])
  exact one_ne_zero h.1

/-! ## Restriction to a subgraph

A nondegenerate pencil realization of `G` restricts to a subgraph `H ≤ G`, with the same hinges,
normals and points. The hubs of `H` are hubs of `G`, and its closed hub-neighbourhoods and closed
neighbourhoods lie in those of `G`, so each condition at `H` follows from one at `G`, except the
independence of the points of the closed neighbourhood of a body that is a hub of `G` and not of
`H`, which the realization of `G` does not ask. `IsNondegPencilRealization.mono` takes it as a
hypothesis; `PencilNondegFeasible.mono` gives it at such a body of degree at most one in `H`, and
`exists_isNondegPencilRealization_restrict_of_demoted` (`lem:pencil-generic-steer`, (a)) chooses a
realization of `G` that restricts when every such body loses only neighbours that are not hubs. -/

/-- **A pencil hub of a subgraph is one of the graph**: for `H ≤ G`, a body of `H` is one of `G`
(`Graph.vertexSet_mono`), and its degree in `G` is at least that in `H` (`Graph.degree_mono`, for a
locally finite `G`). -/
theorem _root_.Graph.PencilHub.of_le {G H : Graph α β} [G.LocallyFinite] {v : α}
    (h : H.PencilHub v) (hle : H ≤ G) : G.PencilHub v :=
  ⟨Graph.vertexSet_mono hle h.1, h.2.trans (Graph.degree_mono hle v)⟩

/-- **The closed hub-neighbourhood grows with the graph**: for `H ≤ G`, a hub of `H` is one of `G`
(`Graph.PencilHub.of_le`), and a link of `H` is one of `G` (`Graph.IsLink.of_le`). -/
theorem _root_.Graph.closedHubNbhd_mono {G H : Graph α β} [G.LocallyFinite]
    (hle : H ≤ G) (v : α) : H.closedHubNbhd v ⊆ G.closedHubNbhd v := by
  rintro w ⟨hhub, rfl | ⟨e, hlink⟩⟩
  · exact ⟨hhub.of_le hle, Or.inl rfl⟩
  · exact ⟨hhub.of_le hle, Or.inr ⟨e, hlink.of_le hle⟩⟩

/-- **The closed neighbourhood grows with the graph**: for `H ≤ G`, a link of `H` is one of `G`. -/
theorem _root_.Graph.closedNbhd_mono {G H : Graph α β}
    (hle : H ≤ G) (v : α) : H.closedNbhd v ⊆ G.closedNbhd v := by
  rintro w (rfl | ⟨e, hlink⟩)
  · exact Or.inl rfl
  · exact Or.inr ⟨e, hlink.of_le hle⟩

/-- **A nondegenerate pencil realization restricts to a subgraph** (a step of
`lem:pencil-generic-steer`, (a), and of `lem:pencil-pair-loop-base-cut`): for `H ≤ G`, the framework
on `H` with the same supporting extensors, normals and points is a nondegenerate realization of `H`,
given the independence of the points of the closed neighbourhood in `H` of each body of `H` that is
a hub of `G` and not of `H` (`hdemote`). Each other condition at `H` is one at `G` on a smaller set
(`Graph.closedHubNbhd_mono`, `Graph.closedNbhd_mono`); the realization of `G` asks nothing of the
points at a hub of `G`. -/
theorem IsNondegPencilRealization.mono {G H : Graph α β} [G.LocallyFinite]
    {F : BodyHingeFramework K 2 α β} {normal point : α → Fin 4 → K}
    (hnd : IsNondegPencilRealization G F normal point) (hle : H ≤ G)
    (hdemote : ∀ v ∈ V(H), G.PencilHub v → ¬ H.PencilHub v →
      LinearIndepOn K point (H.closedNbhd v)) :
    IsNondegPencilRealization H ⟨H, F.supportExtensor⟩ normal point := by
  obtain ⟨⟨⟨-, hnnz, hSnz, hpanel⟩, hpnz, hpinc, hthrough⟩, hadj, hhubLI, hnbhdLI⟩ := hnd
  have hV : V(H) ⊆ V(G) := Graph.vertexSet_mono hle
  refine ⟨⟨⟨rfl, fun v hv => hnnz v (hV hv), hSnz,
      fun e u v hl => hpanel e u v (hl.of_le hle)⟩,
    fun v hv => hpnz v (hV hv), fun v hv => hpinc v (hV hv),
    fun e u v hl => hthrough e u v (hl.of_le hle)⟩,
    fun e u v hl => hadj e u v (hl.of_le hle),
    fun v hv => (hhubLI v (hV hv)).mono (Graph.closedHubNbhd_mono hle v), ?_⟩
  intro v hv hvnothub
  by_cases hGhub : G.PencilHub v
  · exact hdemote v hv hGhub hvnothub
  · exact (hnbhdLI v (hV hv) hGhub).mono (Graph.closedNbhd_mono hle v)

/-- **Feasibility restricts to a subgraph whose demoted hubs have degree at most one** (a step of
`lem:pencil-pair-loop-base-cut`, case (3)): if each body of `H ≤ G` that is a hub of `G` is a hub of
`H` or has degree at most one in `H`, and `G` is nondegeneracy-feasible, so is `H`. The realization
restricts (`IsNondegPencilRealization.mono`). At a body `v` of degree at most one in `H` that is not
a hub of `H`, the closed neighbourhood lies in `{v, w}` for its one neighbour `w`
(`Graph.Inc.isPendant_of_degree_le_one`), whose points are independent as `v` and `w` are linked, or
in `{v}`, whose point is nonzero. -/
theorem PencilNondegFeasible.mono {G H : Graph α β} [G.LocallyFinite]
    (hfeas : PencilNondegFeasible K G) (hle : H ≤ G)
    (hhub : ∀ v ∈ V(H), G.PencilHub v → H.PencilHub v ∨ H.degree v ≤ 1) :
    PencilNondegFeasible K H := by
  have : H.LocallyFinite := ‹G.LocallyFinite›.mono hle
  obtain ⟨F, normal, point, hnd⟩ := hfeas
  have hadj := hnd.2.1
  have hpnz := hnd.1.2.1
  refine ⟨⟨H, F.supportExtensor⟩, normal, point, hnd.mono hle ?_⟩
  intro v hv hGhub hvnothub
  rcases hhub v hv hGhub with hHhub | hdeg
  · exact absurd hHhub hvnothub
  by_cases hinc : ∃ e w, H.IsLink e v w
  · obtain ⟨e, w, hl⟩ := hinc
    have hpend : H.IsPendant e v := hl.inc_left.isPendant_of_degree_le_one hdeg
    have hvw : v ≠ w := by rintro rfl; exact hpend.not_isLoopAt e hl
    have hsub : H.closedNbhd v ⊆ {v, w} := by
      rintro u (rfl | ⟨e', hl'⟩)
      · exact Set.mem_insert _ _
      · obtain rfl := hpend.edge_unique hl'.inc_left
        obtain rfl := hl.right_unique hl'
        exact Set.mem_insert_of_mem _ rfl
    have hLI : LinearIndepOn K point {v, w} := by
      rw [LinearIndepOn.pair_iff point hvw]
      exact LinearIndependent.pair_iff.1 (hadj e v w (hl.of_le hle))
    exact hLI.mono hsub
  · have hsub : H.closedNbhd v ⊆ {v} := by
      rintro u (rfl | ⟨e', hl'⟩)
      · rfl
      · exact absurd ⟨e', u, hl'⟩ hinc
    exact (LinearIndepOn.singleton (i := v)
      (hpnz v (Graph.vertexSet_mono hle hv))).mono hsub

/-! ## Moving a nondegenerate realization by an automorphism

The cut-edge case of the conditioned pair moves the realization of one side by a linear automorphism
`g` of `K⁴` and a contragredient `h` of it, as the cut-edge case does for pencil realizations
(`hasPencilPanelRealization_mapExtensor_screwEquivOfLinearEquiv`, `lem:pencil-projective-transport`,
`Arms.lean`). The graph does not change, and neither do its hubs and neighbourhoods; the injective
`g` and `h` keep each independence (`LinearIndependent.map_injOn`, `LinearIndepOn.map_injOn`). -/

/-- **Moving a nondegenerate pencil realization** (a step of `lem:pencil-pair-loop-base-cut`, case
(3); the nondegenerate form of `lem:pencil-projective-transport`): moving a nondegenerate pencil
realization `(F, normal, point)` of `G` by a linear automorphism `g` of `K⁴` and a contragredient
`h` of it (`g x ⬝ᵥ h y = x ⬝ᵥ y`), the hinges by `screwEquivOfLinearEquiv g`, the points by `g` and
the normals by `h`, gives a nondegenerate pencil realization of `G`. -/
theorem IsNondegPencilRealization.mapExtensor_screwEquivOfLinearEquiv
    {G : Graph α β} {F : BodyHingeFramework K 2 α β} {normal point : α → Fin 4 → K}
    (g h : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K)) (hgh : ∀ x y : Fin 4 → K, g x ⬝ᵥ h y = x ⬝ᵥ y)
    (hnd : IsNondegPencilRealization G F normal point) :
    IsNondegPencilRealization G (F.mapExtensor (BodyHingeFramework.screwEquivOfLinearEquiv g))
      (fun v => h (normal v)) (fun v => g (point v)) := by
  obtain ⟨hreal, hadj, hhubLI, hnbhdLI⟩ := hnd
  refine ⟨hasPencilPanelRealization_mapExtensor_screwEquivOfLinearEquiv g h hgh hreal,
    fun e u v hl => ?_, fun v hv => ?_, fun v hv hnothub => ?_⟩
  · have hli := (hadj e u v hl).map_injOn g.toLinearMap g.injective.injOn
    have heq : g.toLinearMap ∘ ![point u, point v] = ![g (point u), g (point v)] := by
      funext i; fin_cases i <;> rfl
    rwa [heq] at hli
  · have hli := (hhubLI v hv).map_injOn h.toLinearMap h.injective.injOn
    simpa [Function.comp_def] using hli
  · have hli := (hnbhdLI v hv hnothub).map_injOn g.toLinearMap g.injective.injOn
    simpa [Function.comp_def] using hli

/-! ## Incidences and counts at a nondegenerate realization

The point of a body is orthogonal to the normal of every member of its closed neighbourhood, by the
incidences of a pencil realization (`dotProduct_eq_zero_of_extensorInPanel_of_extensorThroughPoint`,
`lem:two-pencil-extension-iff`). So the normals of a closed hub-neighbourhood lie in a space of
dimension `3`, and a nondegenerate realization has at most three members in each, as the chapter
notes after `def:pencil-nondegenerate`. A body that is not a hub has at most three members in its
closed neighbourhood. -/

/-- **The point of a body is orthogonal to the normals of its closed neighbourhood** (a step of
`lem:pencil-feasible-hub-conditions` and `lem:pencil-x0-two-hubs-obstruction`): at a pencil
realization (`HasPencilPanelRealization`), as the remark after `def:pencil-nondegenerate` derives
it, for `v ∈ V(G)` and `w ∈ G.closedNbhd v`, `point v ⬝ᵥ normal w = 0`. At `w = v` it is the
incidence of the point of `v` in its panel. For a link `e` from `v` to `w`, the nonzero hinge of `e`
lies in the panel of `w` and passes through the point of `v`
(`dotProduct_eq_zero_of_extensorInPanel_of_extensorThroughPoint`). -/
theorem dotProduct_point_eq_zero_of_mem_closedNbhd
    {G : Graph α β} {F : BodyHingeFramework K 2 α β}
    {normal point : α → Fin 4 → K} (h : HasPencilPanelRealization G F normal point)
    {v w : α} (hv : v ∈ V(G)) (hw : w ∈ G.closedNbhd v) :
    point v ⬝ᵥ normal w = 0 := by
  obtain ⟨hcop, _, hself, hthru⟩ := h
  obtain ⟨_, _, hCne, hpanel⟩ := hcop
  rcases hw with rfl | ⟨e, hlink⟩
  · exact hself w hv
  · exact dotProduct_eq_zero_of_extensorInPanel_of_extensorThroughPoint (hCne e)
      (hpanel e v w hlink).2 (hthru e v w hlink).1

/-- **The point of a body is orthogonal to the normals of its closed hub-neighbourhood**:
`dotProduct_point_eq_zero_of_mem_closedNbhd`, as the closed hub-neighbourhood lies in the closed
neighbourhood. -/
theorem dotProduct_point_eq_zero_of_mem_closedHubNbhd
    {G : Graph α β} {F : BodyHingeFramework K 2 α β}
    {normal point : α → Fin 4 → K} (h : HasPencilPanelRealization G F normal point)
    {v w : α} (hv : v ∈ V(G)) (hw : w ∈ G.closedHubNbhd v) :
    point v ⬝ᵥ normal w = 0 :=
  dotProduct_point_eq_zero_of_mem_closedNbhd h hv hw.2

/-- **The normal of a body is orthogonal to the points of its closed neighbourhood**: for `v ∈ V(G)`
and `w ∈ G.closedNbhd v`, `point w ⬝ᵥ normal v = 0`, by `dotProduct_point_eq_zero_of_mem_closedNbhd`
at `w = v`, or at `(w, v)` along the reversed link, as `w ∈ V(G)` and `v ∈ G.closedNbhd w`. -/
theorem dotProduct_normal_eq_zero_of_mem_closedNbhd
    {G : Graph α β} {F : BodyHingeFramework K 2 α β}
    {normal point : α → Fin 4 → K} (h : HasPencilPanelRealization G F normal point)
    {v w : α} (hv : v ∈ V(G)) (hw : w ∈ G.closedNbhd v) :
    point w ⬝ᵥ normal v = 0 := by
  rcases hw with rfl | ⟨e, hlink⟩
  · exact dotProduct_point_eq_zero_of_mem_closedNbhd h hv (Or.inl rfl)
  · exact dotProduct_point_eq_zero_of_mem_closedNbhd h hlink.right_mem (Or.inr ⟨e, hlink.symm⟩)

/-- **A nondegenerate realization has at most three members in each closed hub-neighbourhood** (a
step of `lem:pencil-feasible-hub-conditions`, its first part): for `v ∈ V(G)`, the normals of
`G.closedHubNbhd v` are orthogonal to the nonzero point of `v`
(`dotProduct_point_eq_zero_of_mem_closedHubNbhd`), so they span a subspace of the vectors orthogonal
to it, of dimension `3` (`finrank_toDualPerp_single_eq`); being independent, they span one of
dimension `(G.closedHubNbhd v).ncard` (`finrank_span_eq_card`). So `K₄`, where each closed
hub-neighbourhood has four members, has no nondegenerate realization. -/
theorem ncard_closedHubNbhd_le_three_of_isNondegPencilRealization
    [Finite α] {G : Graph α β} {F : BodyHingeFramework K 2 α β} {normal point : α → Fin 4 → K}
    (h : IsNondegPencilRealization G F normal point) {v : α} (hv : v ∈ V(G)) :
    (G.closedHubNbhd v).ncard ≤ 3 := by
  have hpt_ne : point v ≠ 0 := h.1.2.1 v hv
  have hLI : LinearIndepOn K normal (G.closedHubNbhd v) := h.2.2.1 v hv
  set Vperp : Submodule K (Fin 4 → K) :=
    LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip (point v)) with hVperp
  have hVdim : Module.finrank K Vperp = 3 := finrank_toDualPerp_single_eq hpt_ne
  have hsub : Submodule.span K (normal '' G.closedHubNbhd v) ≤ Vperp := by
    rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    simp only [SetLike.mem_coe, hVperp, LinearMap.mem_ker, LinearMap.flip_apply,
      piBasisFun_toDual_eq_dotProduct]
    rw [dotProduct_comm]
    exact dotProduct_point_eq_zero_of_mem_closedHubNbhd h.1 hv hw
  have hspan_le : Module.finrank K (Submodule.span K (normal '' G.closedHubNbhd v)) ≤ 3 := by
    have hmono := Submodule.finrank_mono hsub
    rwa [hVdim] at hmono
  have : Fintype (G.closedHubNbhd v) := Fintype.ofFinite _
  have hspan_eq : Module.finrank K
      (Submodule.span K (Set.range (fun x : G.closedHubNbhd v => normal x)))
      = Fintype.card (G.closedHubNbhd v) := finrank_span_eq_card hLI
  have himg : Set.range (fun x : G.closedHubNbhd v => normal x) = normal '' G.closedHubNbhd v :=
    (Set.image_eq_range normal (G.closedHubNbhd v)).symm
  rw [himg] at hspan_eq
  have hcard : (G.closedHubNbhd v).ncard = Fintype.card (G.closedHubNbhd v) :=
    (Set.fintypeCard_eq_ncard _).symm
  rw [hcard, ← hspan_eq]
  exact hspan_le

/-- **A body that is not a pencil hub has at most three members in its closed neighbourhood**: its
degree is at most `2` (a body outside `V(G)` has degree `0`); its neighbours are at most as many as
the edges at it (`Graph.encard_adj_le_encard_inc`, `Graph.encard_inc_le_eDegree`, and
`Graph.natCast_degree_eq` with `[Finite β]`); and `G.closedNbhd v = insert v N(G, v)`. -/
theorem ncard_closedNbhd_le_three_of_not_pencilHub [Finite β] {G : Graph α β} {v : α}
    (hv : ¬ G.PencilHub v) :
    (G.closedNbhd v).ncard ≤ 3 := by
  have hdeg : G.degree v ≤ 2 := by
    by_contra hcon
    push Not at hcon
    by_cases hvV : v ∈ V(G)
    · exact hv ⟨hvV, by omega⟩
    · have h0 := Graph.degree_eq_zero_of_notMem (G := G) hvV
      omega
  have hNle : (N(G, v)).encard ≤ G.eDegree v :=
    (Graph.encard_adj_le_encard_inc).trans (Graph.encard_inc_le_eDegree)
  have heDeg : (G.degree v : ℕ∞) = G.eDegree v := Graph.natCast_degree_eq G v
  rw [← heDeg] at hNle
  have hcast : (G.degree v : ℕ∞) ≤ (2 : ℕ∞) := by exact_mod_cast hdeg
  have hNle2 : (N(G, v)).encard ≤ (2 : ℕ∞) := hNle.trans hcast
  obtain ⟨hNfin, hNcard⟩ := Set.encard_le_coe_iff_finite_ncard_le.mp hNle2
  have heq : G.closedNbhd v = insert v (N(G, v)) := rfl
  rw [heq]
  calc (insert v (N(G, v))).ncard ≤ (N(G, v)).ncard + 1 := Set.ncard_insert_le v (N(G, v))
    _ ≤ 2 + 1 := Nat.add_le_add_right hNcard 1
    _ = 3 := by norm_num

/-! ## Three independent vectors of `K⁴`

Independence on a set `{x, y, z}` of three distinct bodies, read as that of the family
`![f x, f y, f z]`, and the dimension `1` of the vectors orthogonal to three independent vectors.
The triangle's obstruction below uses both. -/

/-- **Independence on three distinct bodies is that of their family**: for distinct `x, y, z`,
`LinearIndepOn K f {x, y, z}` gives `LinearIndependent K ![f x, f y, f z]`, by mathlib's
`linearIndepOn_range_iff` at the injective `![x, y, z]`, whose range is `{x, y, z}`. -/
theorem linearIndependent_triple_of_linearIndepOn (f : α → Fin 4 → K) {x y z : α}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hLI : LinearIndepOn K f {x, y, z}) :
    LinearIndependent K ![f x, f y, f z] := by
  have hinj : Function.Injective ![x, y, z] := by
    intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have hr : Set.range ![x, y, z] = {x, y, z} := by
    simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rw [← hr, linearIndepOn_range_iff hinj] at hLI
  convert hLI using 1
  funext i; fin_cases i <;> rfl

/-- **The vectors of `K⁴` orthogonal to three independent vectors form a space of dimension `1`**:
its dimension and that of the span of the three, which is `3` (`finrank_span_eq_card`), add up to
`4` (`finrank_toDualPerp_add_finrank_span`). The form for three vectors of
`finrank_toDualPerp_single_eq` and `finrank_toDualPerp_pair_eq` (`Meet.lean`). -/
theorem finrank_toDualPerp_triple_eq {n : Fin 3 → Fin 4 → K} (hn : LinearIndependent K n) :
    Module.finrank K
        (⨅ j : Fin 3, LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip (n j))
          : Submodule K (Fin 4 → K)) = 1 := by
  have := finrank_toDualPerp_add_finrank_span n
  rw [finrank_span_eq_card hn, Fintype.card_fin] at this
  omega

/-! ## Two obstructions to nondegeneracy

A triangle with two pencil hubs is not nondegeneracy-feasible, and two hubs with three common
neighbours whose points are independent have no nondegenerate realization with those points
(`lem:pencil-feasible-hub-conditions`, `lem:pencil-x0-two-hubs-obstruction`). In each, the normals
of the two hubs are independent, and the vectors orthogonal to both form a space of dimension `2`
(`finrank_toDualPerp_pair_eq`), which holds no three independent vectors
(`not_linearIndependent_of_dotProduct_eq_zero_pair`, which the one-body ear of
`MainComponent/GenericEar.lean` also uses). The first also serves `lem:pencil-generic-steer`
(`MainComponent/GenericSteer.lean`). -/

/-- **Three vectors orthogonal to two independent vectors are dependent** (a step of
`lem:pencil-feasible-hub-conditions`, `lem:pencil-x0-two-hubs-obstruction` and
`lem:pencil-generic-one-ear`): they lie in `n_a^⊥ ∩ n_b^⊥`, of dimension two
(`finrank_toDualPerp_pair_eq`). -/
theorem not_linearIndependent_of_dotProduct_eq_zero_pair {na nb : Fin 4 → K}
    (hab : LinearIndependent K ![na, nb]) (p : Fin 3 → Fin 4 → K)
    (h : ∀ i, p i ⬝ᵥ na = 0 ∧ p i ⬝ᵥ nb = 0) : ¬ LinearIndependent K p := by
  intro hp
  set m : Submodule K (Fin 4 → K) :=
    ⨅ j : Fin 2, LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip (![na, nb] j)) with hm
  have hmdim : Module.finrank K m = 2 := finrank_toDualPerp_pair_eq hab
  have hmem : ∀ i, p i ∈ m := by
    intro i
    simp only [hm, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply,
      piBasisFun_toDual_eq_dotProduct, Fin.forall_fin_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    exact h i
  set p' : Fin 3 → m := fun i => ⟨p i, hmem i⟩
  have hp' : LinearIndependent K p' := LinearIndependent.of_comp m.subtype (by exact hp)
  have := hp'.fintype_card_le_finrank
  rw [Fintype.card_fin, hmdim] at this
  omega

/-- **A triangle with two pencil hubs is not nondegeneracy-feasible** (a step of
`lem:pencil-feasible-hub-conditions`, its second part): let `x, y, z` be the triangle, with `y` and
`z` hubs. At a nondegenerate realization the normals of `y` and `z` are independent, both lying in
the closed hub-neighbourhood of `y`, and the three points of the triangle are orthogonal to both
(`dotProduct_point_eq_zero_of_mem_closedNbhd`, along its edges). If `x` is not a hub, the points of
its closed neighbourhood, which contains `x, y, z`, are independent: three independent vectors
orthogonal to two independent ones (`not_linearIndependent_of_dotProduct_eq_zero_pair`). If `x` is
a hub, the normals of `x, y, z` are independent, so the points of `x` and `y` lie in a space of
dimension `1` (`finrank_toDualPerp_triple_eq`), while the points at the two ends of the link `xy`
are independent. -/
theorem not_pencilNondegFeasible_of_triangle_two_hubs {G : Graph α β}
    {e₁ e₂ e₃ : β} {x y z : α} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (h₁ : G.IsLink e₁ x y) (h₂ : G.IsLink e₂ y z) (h₃ : G.IsLink e₃ z x)
    (hy : G.PencilHub y) (hz : G.PencilHub z) :
    ¬ PencilNondegFeasible K G := by
  rintro ⟨F, normal, point, hnd⟩
  -- `normal y, normal z` are independent: both are in the closed hub-neighbourhood of `y`.
  have hsubyz : ({y, z} : Set α) ⊆ G.closedHubNbhd y := by
    rintro w (rfl | rfl)
    · exact ⟨hy, Or.inl rfl⟩
    · exact ⟨hz, Or.inr ⟨e₂, h₂⟩⟩
  have hLIyz : LinearIndependent K ![normal y, normal z] :=
    LinearIndependent.pair_iff.2
      ((LinearIndepOn.pair_iff normal hyz).1 ((hnd.2.2.1 y hy.1).mono hsubyz))
  -- Every point of the triangle is orthogonal to `normal y` and `normal z` (the incidences along
  -- its three edges).
  have hxV : point x ⬝ᵥ normal y = 0 ∧ point x ⬝ᵥ normal z = 0 :=
    ⟨dotProduct_point_eq_zero_of_mem_closedNbhd hnd.1 h₁.left_mem (Or.inr ⟨e₁, h₁⟩),
      dotProduct_point_eq_zero_of_mem_closedNbhd hnd.1 h₁.left_mem (Or.inr ⟨e₃, h₃.symm⟩)⟩
  have hyV : point y ⬝ᵥ normal y = 0 ∧ point y ⬝ᵥ normal z = 0 :=
    ⟨dotProduct_point_eq_zero_of_mem_closedNbhd hnd.1 h₁.right_mem (Or.inl rfl),
      dotProduct_point_eq_zero_of_mem_closedNbhd hnd.1 h₁.right_mem (Or.inr ⟨e₂, h₂⟩)⟩
  have hzV : point z ⬝ᵥ normal y = 0 ∧ point z ⬝ᵥ normal z = 0 :=
    ⟨dotProduct_point_eq_zero_of_mem_closedNbhd hnd.1 h₂.right_mem (Or.inr ⟨e₂, h₂.symm⟩),
      dotProduct_point_eq_zero_of_mem_closedNbhd hnd.1 h₂.right_mem (Or.inl rfl)⟩
  by_cases hx : G.PencilHub x
  · -- `x` is a hub too: `normal x, normal y, normal z` are independent (the closed
    -- hub-neighbourhood of `x`), so `point x, point y` lie in `Vxyz`, of dimension `1`, while the
    -- link `e₁` makes them independent.
    have hsubxyz : ({x, y, z} : Set α) ⊆ G.closedHubNbhd x := by
      rintro w (rfl | rfl | rfl)
      · exact ⟨hx, Or.inl rfl⟩
      · exact ⟨hy, Or.inr ⟨e₁, h₁⟩⟩
      · exact ⟨hz, Or.inr ⟨e₃, h₃.symm⟩⟩
    have hLI3n : LinearIndepOn K normal {x, y, z} := (hnd.2.2.1 x h₁.left_mem).mono hsubxyz
    have hLItriple : LinearIndependent K ![normal x, normal y, normal z] :=
      linearIndependent_triple_of_linearIndepOn normal hxy hxz hyz hLI3n
    set Vxyz : Submodule K (Fin 4 → K) :=
      ⨅ j : Fin 3, LinearMap.ker
        ((Pi.basisFun K (Fin 4)).toDual.flip (![normal x, normal y, normal z] j))
      with hVxyz
    have hVxyzdim : Module.finrank K Vxyz = 1 := finrank_toDualPerp_triple_eq hLItriple
    have hmemxyz : ∀ w : Fin 4 → K, w ∈ Vxyz ↔
        ∀ j, w ⬝ᵥ (![normal x, normal y, normal z] j) = 0 := by
      intro w
      simp only [hVxyz, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply,
        piBasisFun_toDual_eq_dotProduct]
    have hxV3 : point x ∈ Vxyz := by
      rw [hmemxyz]; intro j; fin_cases j
      · simpa using dotProduct_point_eq_zero_of_mem_closedNbhd hnd.1 h₁.left_mem (Or.inl rfl)
      · simpa using dotProduct_point_eq_zero_of_mem_closedNbhd hnd.1 h₁.left_mem (Or.inr ⟨e₁, h₁⟩)
      · simpa using
          dotProduct_point_eq_zero_of_mem_closedNbhd hnd.1 h₁.left_mem (Or.inr ⟨e₃, h₃.symm⟩)
    have hyV3 : point y ∈ Vxyz := by
      rw [hmemxyz]; intro j; fin_cases j
      · simpa using
          dotProduct_point_eq_zero_of_mem_closedNbhd hnd.1 h₁.right_mem (Or.inr ⟨e₁, h₁.symm⟩)
      · simpa using dotProduct_point_eq_zero_of_mem_closedNbhd hnd.1 h₁.right_mem (Or.inl rfl)
      · simpa using dotProduct_point_eq_zero_of_mem_closedNbhd hnd.1 h₁.right_mem (Or.inr ⟨e₂, h₂⟩)
    have hLIxy : LinearIndependent K ![point x, point y] := hnd.2.1 e₁ x y h₁
    have hsub2 : Submodule.span K (Set.range ![point x, point y]) ≤ Vxyz := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      fin_cases j
      · exact hxV3
      · exact hyV3
    have hdim2 : Module.finrank K (Submodule.span K (Set.range ![point x, point y])) = 2 := by
      rw [finrank_span_eq_card hLIxy]; simp
    have hmono := Submodule.finrank_mono hsub2
    rw [hdim2, hVxyzdim] at hmono
    omega
  · -- `x` is not a hub: `point x, point y, point z` are independent (the closed neighbourhood of
    -- `x`), three vectors orthogonal to `normal y` and `normal z`.
    have hsubpts : ({x, y, z} : Set α) ⊆ G.closedNbhd x := by
      rintro w (rfl | rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr ⟨e₁, h₁⟩
      · exact Or.inr ⟨e₃, h₃.symm⟩
    have hLI3p : LinearIndepOn K point {x, y, z} := (hnd.2.2.2 x h₁.left_mem hx).mono hsubpts
    refine not_linearIndependent_of_dotProduct_eq_zero_pair hLIyz _ (fun i => ?_)
      (linearIndependent_triple_of_linearIndepOn point hxy hxz hyz hLI3p)
    fin_cases i
    exacts [hxV, hyV, hzV]

/-- **Feasibility bounds the hub neighbourhoods** (`lem:pencil-feasible-hub-conditions`): if `G` is
nondegeneracy-feasible, every closed hub-neighbourhood has at most three members
(`ncard_closedHubNbhd_le_three_of_isNondegPencilRealization`; it is empty at a body outside `V(G)`),
and no triangle contains two pencil hubs (`not_pencilNondegFeasible_of_triangle_two_hubs`). -/
theorem PencilNondegFeasible.hub_conditions [Finite α] {G : Graph α β}
    (hfeas : PencilNondegFeasible K G) :
    (∀ v, (G.closedHubNbhd v).ncard ≤ 3) ∧
    (∀ e₁ e₂ e₃ x y z, x ≠ y → y ≠ z → x ≠ z → G.IsLink e₁ x y → G.IsLink e₂ y z →
      G.IsLink e₃ z x → G.PencilHub y → G.PencilHub z → False) := by
  refine ⟨fun w => ?_, fun e₁ e₂ e₃ x y z hxy hyz hxz h₁ h₂ h₃ hy hz =>
    not_pencilNondegFeasible_of_triangle_two_hubs hxy hyz hxz h₁ h₂ h₃ hy hz hfeas⟩
  obtain ⟨F, normal, point, hnd⟩ := hfeas
  by_cases hw : w ∈ V(G)
  · exact ncard_closedHubNbhd_le_three_of_isNondegPencilRealization hnd hw
  · have hempty : G.closedHubNbhd w = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro x ⟨hxhub, rfl | ⟨e, hlink⟩⟩
      · exact hw hxhub.1
      · exact hw hlink.left_mem
    rw [hempty]; simp

/-- **Two hubs with three common neighbours** (`lem:pencil-x0-two-hubs-obstruction`, its first
part): if `a ≠ b` are pencil hubs of `G` with common neighbours `x, y, z` whose points are linearly
independent, the realization is not nondegenerate. Its normals at `a` and `b` would be independent,
both lying in the closed hub-neighbourhood of `x`, and the three independent points would each be
orthogonal to both normals, along its links to `a` and `b`
(`dotProduct_point_eq_zero_of_mem_closedNbhd`), which three independent vectors cannot be
(`not_linearIndependent_of_dotProduct_eq_zero_pair`). -/
theorem not_isNondegPencilRealization_of_two_hubs_three_common
    {G : Graph α β} {F : BodyHingeFramework K 2 α β} {normal point : α → Fin 4 → K}
    {a b x y z : α} {ea eb fa fb ga gb : β} (hab : a ≠ b)
    (ha : G.PencilHub a) (hb : G.PencilHub b)
    (hxa : G.IsLink ea x a) (hxb : G.IsLink eb x b) (hya : G.IsLink fa y a)
    (hyb : G.IsLink fb y b) (hza : G.IsLink ga z a) (hzb : G.IsLink gb z b)
    (hLI : LinearIndependent K ![point x, point y, point z]) :
    ¬ IsNondegPencilRealization G F normal point := by
  intro hnd
  have hsub : ({a, b} : Set α) ⊆ G.closedHubNbhd x := by
    rintro w (rfl | rfl)
    · exact ⟨ha, Or.inr ⟨ea, hxa⟩⟩
    · exact ⟨hb, Or.inr ⟨eb, hxb⟩⟩
  have hLIab : LinearIndependent K ![normal a, normal b] :=
    LinearIndependent.pair_iff.2
      ((LinearIndepOn.pair_iff normal hab).1 ((hnd.2.2.1 x hxa.left_mem).mono hsub))
  have hin : ∀ {w : α} {e f : β}, G.IsLink e w a → G.IsLink f w b →
      point w ⬝ᵥ normal a = 0 ∧ point w ⬝ᵥ normal b = 0 := fun he hf =>
    ⟨dotProduct_point_eq_zero_of_mem_closedNbhd hnd.1 he.left_mem (Or.inr ⟨_, he⟩),
      dotProduct_point_eq_zero_of_mem_closedNbhd hnd.1 hf.left_mem (Or.inr ⟨_, hf⟩)⟩
  refine not_linearIndependent_of_dotProduct_eq_zero_pair hLIab _ (fun i => ?_) hLI
  fin_cases i
  exacts [hin hxa hxb, hin hya hyb, hin hza hzb]

/-! ## Degrees in an induced graph

The cut-edge case of the conditioned pair (`lem:pencil-pair-loop-base-cut`, case (3)) compares the
degree of a body in a side, an induced graph `G[S]`, with its degree in `G`. A body of `S` keeps its
degree when every link of `G` from it ends in `S`; the sections below apply this to each kind of
side. -/

/-- **A body whose links all end in `S` keeps its degree in `G[S]`** (a step of
`lem:pencil-pair-loop-base-cut`): for `v ∈ S` such that every link of `G` from `v` ends in `S`, `v`
has the same degree in `G.induce S` as in `G`, as its loops and its other edges are those of `G`
(`Graph.degree_eq_ncard_add_ncard`). -/
theorem _root_.Graph.degree_induce_eq_of_isLink_mem [Finite β] {G : Graph α β} {S : Set α} {v : α}
    (hv : v ∈ S) (hS : ∀ e y, G.IsLink e v y → y ∈ S) :
    (G.induce S).degree v = G.degree v := by
  have hloops : {e | (G.induce S).IsLoopAt e v} = {e | G.IsLoopAt e v} := by
    ext e
    exact ⟨fun h => ((Graph.induce_isLink G S e v v).mp h).1,
      fun h => (Graph.induce_isLink G S e v v).mpr ⟨h, hv, hv⟩⟩
  have hnonloops : {e | (G.induce S).IsNonloopAt e v} = {e | G.IsNonloopAt e v} := by
    ext e
    constructor
    · rintro ⟨y, hyv, hl⟩
      exact ⟨y, hyv, ((Graph.induce_isLink G S e v y).mp hl).1⟩
    · rintro ⟨y, hyv, hl⟩
      exact ⟨y, hyv, (Graph.induce_isLink G S e v y).mpr ⟨hl, hv, hS e y hl⟩⟩
  rw [Graph.degree_eq_ncard_add_ncard, Graph.degree_eq_ncard_add_ncard, hloops, hnonloops]

/-! ## The side of a cut with the far end of the crossing edge

In the cut-edge case of the conditioned pair (`lem:pencil-pair-loop-base-cut`, case (3)), let one
edge `e₀` join `u₀ ∈ V₁` to `w₀ ∉ V₁`, the only edge crossing `V₁`. When both sides have at least
two bodies, the case uses each side with the far end of `e₀`, `G[V₁ ∪ {w₀}]`, rather than `G[V₁]`:
each body of `V₁` keeps its degree there, so that no hub of `G` in `V₁` stops being one, and `w₀`
has degree `1` when `G` is loopless, which `PencilNondegFeasible.mono` allows. Its links are those
of `G[V₁]` and `e₀` (`Graph.isLink_induce_union_singleton_of_isLink`), so that removing `e₀` lowers
its rank by at most `D - 1` (`BodyHingeFramework.finrank_span_rigidityRows_le_add_of_links_subset`,
`RigidityMatrix/Bricks.lean`), and its deficiency is that of `G[V₁]` plus one
(`Graph.deficiency_induce_union_singleton`). A link of `G` crossing `V₁` is `e₀` by
`Graph.eq_cutEdge_of_isLink_crossing` (`Molecular/Deficiency.lean`). -/

/-- **The closed neighbourhood of a body of `V₁` lies in `V₁ ∪ {w₀}`**: if `e₀` joins `u₀ ∈ V₁` to
`w₀ ∉ V₁` and no other edge crosses `V₁`, a link from `v ∈ V₁` that leaves `V₁` crosses it, so it is
`e₀` (`Graph.eq_cutEdge_of_isLink_crossing`), whose other end is `w₀`. -/
theorem _root_.Graph.closedNbhd_subset_of_mem [Finite β] {G : Graph α β}
    {V₁ : Set α} {e₀ : β} {u₀ w₀ : α}
    (hl₀ : G.IsLink e₀ u₀ w₀) (hu₀ : u₀ ∈ V₁) (hw₀ : w₀ ∉ V₁)
    (hcut : (G.cutEdges V₁).ncard ≤ 1) {v : α} (hv : v ∈ V₁) :
    G.closedNbhd v ⊆ V₁ ∪ {w₀} := by
  rintro w (rfl | ⟨e, hl⟩)
  · exact Set.mem_union_left _ hv
  · by_cases hw : w ∈ V₁
    · exact Set.mem_union_left _ hw
    · obtain rfl := Graph.eq_cutEdge_of_isLink_crossing hl₀ hu₀ hw₀ hcut hl hv hw
      rcases hl.eq_and_eq_or_eq_and_eq hl₀ with ⟨-, rfl⟩ | ⟨rfl, -⟩
      · exact Set.mem_union_right _ rfl
      · exact absurd hv hw₀

/-- **A body of `V₁` keeps its degree in `G[V₁ ∪ {w₀}]`**: with `e₀`, `u₀`, `w₀` and `V₁` as in
`Graph.closedNbhd_subset_of_mem`, each `v ∈ V₁` has the same degree in `G.induce (V₁ ∪ {w₀})` as in
`G`, as every link of `G` from `v` ends in `V₁ ∪ {w₀}` (`Graph.closedNbhd_subset_of_mem`,
`Graph.degree_induce_eq_of_isLink_mem`). So no pencil hub of `G` in `V₁` stops being one there. -/
theorem _root_.Graph.degree_induce_union_singleton_of_mem [Finite β] {G : Graph α β}
    {V₁ : Set α} {e₀ : β} {u₀ w₀ : α}
    (hl₀ : G.IsLink e₀ u₀ w₀) (hu₀ : u₀ ∈ V₁) (hw₀ : w₀ ∉ V₁)
    (hcut : (G.cutEdges V₁).ncard ≤ 1) {v : α} (hv : v ∈ V₁) :
    (G.induce (V₁ ∪ {w₀})).degree v = G.degree v :=
  Graph.degree_induce_eq_of_isLink_mem (Set.mem_union_left _ hv) fun _ _ hl =>
    Graph.closedNbhd_subset_of_mem hl₀ hu₀ hw₀ hcut hv (Or.inr ⟨_, hl⟩)

/-- **The far end `w₀` has degree `1` in `G[V₁ ∪ {w₀}]`**: with `e₀`, `u₀`, `w₀` and `V₁` as in
`Graph.degree_induce_union_singleton_of_mem`, and `G` loopless, `e₀` is the only edge of the induced
graph at `w₀`: another would join `w₀` to a body of `V₁` and cross `V₁`. So a hub `w₀` of `G` has
degree `1` there, which `PencilNondegFeasible.mono` allows. -/
theorem _root_.Graph.degree_induce_union_singleton_far [Finite β] {G : Graph α β} [G.Loopless]
    {V₁ : Set α} {e₀ : β} {u₀ w₀ : α}
    (hl₀ : G.IsLink e₀ u₀ w₀) (hu₀ : u₀ ∈ V₁) (hw₀ : w₀ ∉ V₁)
    (hcut : (G.cutEdges V₁).ncard ≤ 1) :
    (G.induce (V₁ ∪ {w₀})).degree w₀ = 1 := by
  have huw : u₀ ≠ w₀ := fun h => hw₀ (h ▸ hu₀)
  have hloops : {e | (G.induce (V₁ ∪ {w₀})).IsLoopAt e w₀} = ∅ := by
    ext e
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact fun h =>
      G.not_isLoopAt e w₀ ((Graph.induce_isLink G (V₁ ∪ {w₀}) e w₀ w₀).mp h).1
  have hnonloops : {e | (G.induce (V₁ ∪ {w₀})).IsNonloopAt e w₀} = {e₀} := by
    ext e
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, hyw, hl⟩
      obtain ⟨hlG, -, hy⟩ := (Graph.induce_isLink G (V₁ ∪ {w₀}) e w₀ y).mp hl
      have hy₁ : y ∈ V₁ := hy.resolve_right hyw
      exact Graph.eq_cutEdge_of_isLink_crossing hl₀ hu₀ hw₀ hcut hlG.symm hy₁ hw₀
    · rintro he
      rw [he]
      exact ⟨u₀, huw, (Graph.induce_isLink G (V₁ ∪ {w₀}) e₀ w₀ u₀).mpr
        ⟨hl₀.symm, Set.mem_union_right _ rfl, Set.mem_union_left _ hu₀⟩⟩
  rw [Graph.degree_eq_ncard_add_ncard, hloops, hnonloops, Set.ncard_empty, Set.ncard_singleton]

/-- **A link of `G[V₁ ∪ {w₀}]` is one of `G[V₁]` or is `e₀`** (the hypothesis `hlinks` of
`BodyHingeFramework.finrank_span_rigidityRows_le_add_of_links_subset` at `G[V₁ ∪ {w₀}]` and
`G[V₁]`): a link with both ends in `V₁` is one of `G[V₁]`; one with an end `w₀` and the other in
`V₁` crosses `V₁`, so it is `e₀` (`Graph.eq_cutEdge_of_isLink_crossing`); and one with both ends
`w₀` is a loop, which the loopless `G` does not have. -/
theorem _root_.Graph.isLink_induce_union_singleton_of_isLink [Finite β] {G : Graph α β}
    [G.Loopless] {V₁ : Set α} {e₀ : β} {u₀ w₀ : α}
    (hl₀ : G.IsLink e₀ u₀ w₀) (hu₀ : u₀ ∈ V₁) (hw₀ : w₀ ∉ V₁)
    (hcut : (G.cutEdges V₁).ncard ≤ 1) {e : β} {u v : α}
    (hl : (G.induce (V₁ ∪ {w₀})).IsLink e u v) :
    (G.induce V₁).IsLink e u v ∨ e = e₀ := by
  obtain ⟨hlG, hu, hv⟩ := (Graph.induce_isLink G (V₁ ∪ {w₀}) e u v).mp hl
  by_cases hu₁ : u ∈ V₁
  · by_cases hv₁ : v ∈ V₁
    · exact Or.inl ((Graph.induce_isLink G V₁ e u v).mpr ⟨hlG, hu₁, hv₁⟩)
    · have hvw : v = w₀ := hv.resolve_left hv₁
      subst hvw
      exact Or.inr (Graph.eq_cutEdge_of_isLink_crossing hl₀ hu₀ hw₀ hcut hlG hu₁ hw₀)
  · have huw : u = w₀ := hu.resolve_left hu₁
    by_cases hv₁ : v ∈ V₁
    · exact Or.inr (Graph.eq_cutEdge_of_isLink_crossing hl₀ hu₀ hw₀ hcut hlG.symm hv₁ hu₁)
    · have hvw : v = w₀ := hv.resolve_left hv₁
      have huv : u = v := huw.trans hvw.symm
      exact absurd (huv ▸ hlG) (G.not_isLoopAt e v)

/-- **Feasibility passes to `G[V₁ ∪ {w₀}]`** (a step of `lem:pencil-pair-loop-base-cut`, case (3)):
for a loopless `G`, `V₁ ⊆ V(G)`, and `e₀`, `u₀`, `w₀` as in
`Graph.degree_induce_union_singleton_of_mem`, if `G` is nondegeneracy-feasible, so is
`G.induce (V₁ ∪ {w₀})`, by `PencilNondegFeasible.mono`: a hub of `G` in `V₁` keeps its degree, and
`w₀` has degree `1` (`Graph.degree_induce_union_singleton_far`). -/
theorem PencilNondegFeasible.induce_union_singleton [Finite β] {G : Graph α β} [G.Loopless]
    {V₁ : Set α} {e₀ : β} {u₀ w₀ : α}
    (hfeas : PencilNondegFeasible K G)
    (hl₀ : G.IsLink e₀ u₀ w₀) (hu₀ : u₀ ∈ V₁) (hw₀ : w₀ ∉ V₁)
    (hV₁ : V₁ ⊆ V(G)) (hcut : (G.cutEdges V₁).ncard ≤ 1) :
    PencilNondegFeasible K (G.induce (V₁ ∪ {w₀})) := by
  have hle : G.induce (V₁ ∪ {w₀}) ≤ G := Graph.induce_le (by
    rintro x (hx | rfl)
    · exact hV₁ hx
    · exact hl₀.right_mem)
  refine hfeas.mono hle ?_
  rintro v (hv₁ | rfl) hGhub
  · exact Or.inl ⟨Set.mem_union_left _ hv₁, by
      rw [Graph.degree_induce_union_singleton_of_mem hl₀ hu₀ hw₀ hcut hv₁]
      exact hGhub.2⟩
  · exact Or.inr (Graph.degree_induce_union_singleton_far hl₀ hu₀ hw₀ hcut).le

/-- **The deficiency of a side with the far end of the crossing edge**
(`lem:cut-edge-decomposition`, (3)): for a loopless `G`, and `e₀`, `u₀`, `w₀` and `V₁` as in
`Graph.degree_induce_union_singleton_of_mem`, `def(G[V₁ ∪ {w₀}]) = def(G[V₁]) + 1`. Apply (1)
(`Graph.deficiency_eq_of_cutEdges_ncard_le_one`, KT Lemma 3.6) to `G[V₁ ∪ {w₀}]` and `{w₀}`: `e₀` is
the only edge crossing `{w₀}` there; `G[{w₀}]` has no edge, as `G` is loopless, so its deficiency is
`0` (`Graph.deficiency_of_edgeSet_empty`); the other side is `G[V₁]`
(`Graph.induce_induce_of_subset`); and the cut adds `D - (D - 1) = 1`. -/
theorem _root_.Graph.deficiency_induce_union_singleton [Finite α] [Finite β] {G : Graph α β}
    [G.Loopless] {n : ℕ} {V₁ : Set α} {e₀ : β} {u₀ w₀ : α}
    (hl₀ : G.IsLink e₀ u₀ w₀) (hu₀ : u₀ ∈ V₁) (hw₀ : w₀ ∉ V₁)
    (hcut : (G.cutEdges V₁).ncard ≤ 1) :
    (G.induce (V₁ ∪ {w₀})).deficiency n = (G.induce V₁).deficiency n + 1 := by
  set Gp := G.induce (V₁ ∪ {w₀}) with hGpdef
  have hssub : ({w₀} : Set α) ⊂ V(Gp) :=
    (Set.ssubset_iff_of_subset (fun x hx => Set.mem_union_right _ hx)).mpr
      ⟨u₀, Set.mem_union_left _ hu₀, fun h => hw₀ (h ▸ hu₀)⟩
  have hcut' : Gp.cutEdges {w₀} = {e₀} := by
    ext e
    simp only [Graph.cutEdges, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨-, x, y, hl, hx, hy⟩
      obtain ⟨hlG, -, hyV⟩ := (Graph.induce_isLink G (V₁ ∪ {w₀}) e x y).mp hl
      rw [hx] at hlG
      have hy₁ : y ∈ V₁ := hyV.resolve_right hy
      exact Graph.eq_cutEdge_of_isLink_crossing hl₀ hu₀ hw₀ hcut hlG.symm hy₁ hw₀
    · rintro he
      rw [he]
      have hl' : Gp.IsLink e₀ w₀ u₀ := (Graph.induce_isLink G (V₁ ∪ {w₀}) e₀ w₀ u₀).mpr
        ⟨hl₀.symm, Set.mem_union_right _ rfl, Set.mem_union_left _ hu₀⟩
      exact ⟨hl'.edge_mem, w₀, u₀, hl', rfl, fun h => hw₀ (h ▸ hu₀)⟩
  have hsplit := Graph.deficiency_eq_of_cutEdges_ncard_le_one (G := Gp) (n := n) hssub
    (by rw [hcut', Set.ncard_singleton])
  have hdiff : V(Gp) \ {w₀} = V₁ := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_singleton_iff]
    exact ⟨fun ⟨hx, hxw⟩ => (hx.resolve_right hxw : x ∈ V₁),
      fun hx => ⟨Set.mem_union_left _ hx, fun h => hw₀ (h ▸ hx)⟩⟩
  have hE : E(Gp.induce {w₀}) = ∅ := by
    ext e
    simp only [Graph.edgeSet_induce, Set.mem_ofPred_eq, Set.mem_singleton_iff,
      Set.mem_empty_iff_false, iff_false]
    rintro ⟨x, y, hl, hx, hy⟩
    rw [hx, hy] at hl
    exact G.not_isLoopAt e w₀ ((Graph.induce_isLink G (V₁ ∪ {w₀}) e w₀ w₀).mp hl).1
  have hdef₀ : (Gp.induce {w₀}).deficiency n = 0 := by
    rw [Graph.deficiency_of_edgeSet_empty hE]
    simp [Set.ncard_singleton]
  have hind : Gp.induce V₁ = G.induce V₁ :=
    Graph.induce_induce_of_subset G Set.subset_union_left
  rw [hcut', Set.ncard_singleton, hdiff, hind, hdef₀] at hsplit
  rw [hsplit]
  push_cast
  ring

/-! ## Neighbourhoods in `G[V₁ ∪ {w₀}]`

The cut-edge case reads the closed neighbourhood and the closed hub-neighbourhood of a body of `V₁`
in `G[V₁ ∪ {w₀}]`. The first is that in `G`: every neighbour in `G` of a body of `V₁` lies in
`V₁ ∪ {w₀}`, as any other would end a second edge crossing `V₁`. The second is that in `G` without
`w₀`, which is not a hub of `G[V₁ ∪ {w₀}]`; as `u₀` is the only body of `V₁` linked to `w₀`,
removing it changes only the closed hub-neighbourhood of `u₀`. -/

/-- **A body of `V₁` has the same closed neighbourhood in `G[V₁ ∪ {w₀}]` as in `G`**: a link of the
induced graph is one of `G`, and a link of `G` at `v ∈ V₁` has its other end in `V₁ ∪ {w₀}`
(`Graph.closedNbhd_subset_of_mem`), so it is a link of the induced graph. -/
theorem _root_.Graph.closedNbhd_induce_union_singleton [Finite β] {G : Graph α β}
    {V₁ : Set α} {e₀ : β} {u₀ w₀ : α}
    (hl₀ : G.IsLink e₀ u₀ w₀) (hu₀ : u₀ ∈ V₁) (hw₀ : w₀ ∉ V₁)
    (hcut : (G.cutEdges V₁).ncard ≤ 1) {v : α} (hv : v ∈ V₁) :
    (G.induce (V₁ ∪ {w₀})).closedNbhd v = G.closedNbhd v := by
  apply Set.Subset.antisymm
  · rintro w (rfl | ⟨e, hl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨e, ((Graph.induce_isLink G (V₁ ∪ {w₀}) e v w).mp hl).1⟩
  · rintro w hw
    have hwmem : w ∈ V₁ ∪ ({w₀} : Set α) :=
      Graph.closedNbhd_subset_of_mem hl₀ hu₀ hw₀ hcut hv hw
    rcases hw with rfl | ⟨e, hl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨e, (Graph.induce_isLink G (V₁ ∪ {w₀}) e v w).mpr
        ⟨hl, Set.mem_union_left _ hv, hwmem⟩⟩

/-- **A body of `V₁` has in `G[V₁ ∪ {w₀}]` the closed hub-neighbourhood it has in `G`, without
`w₀`**: for a loopless `G` and `V₁ ⊆ V(G)`, a body of `V₁` is a hub of the induced graph exactly
when it is one of `G` (`Graph.degree_induce_union_singleton_of_mem`), `w₀` is not a hub there
(`Graph.degree_induce_union_singleton_far`), and the closed neighbourhoods agree
(`Graph.closedNbhd_induce_union_singleton`). -/
theorem _root_.Graph.closedHubNbhd_induce_union_singleton [Finite β] {G : Graph α β} [G.Loopless]
    {V₁ : Set α} {e₀ : β} {u₀ w₀ : α} (hV₁ : V₁ ⊆ V(G))
    (hl₀ : G.IsLink e₀ u₀ w₀) (hu₀ : u₀ ∈ V₁) (hw₀ : w₀ ∉ V₁)
    (hcut : (G.cutEdges V₁).ncard ≤ 1) {v : α} (hv : v ∈ V₁) :
    (G.induce (V₁ ∪ {w₀})).closedHubNbhd v = G.closedHubNbhd v \ {w₀} := by
  have hNeq := Graph.closedNbhd_induce_union_singleton hl₀ hu₀ hw₀ hcut hv
  ext w
  constructor
  · intro hmem
    have hhub := hmem.1
    have hcase : w ∈ (G.induce (V₁ ∪ {w₀})).closedNbhd v := hmem.2
    have hwmem : w ∈ V₁ ∪ ({w₀} : Set α) := hhub.1
    have hwG : w ∈ G.closedNbhd v := hNeq ▸ hcase
    rcases hwmem with hw₁ | hweq
    · have hdeg3 : 3 ≤ (G.induce (V₁ ∪ {w₀})).degree w := hhub.2
      rw [Graph.degree_induce_union_singleton_of_mem hl₀ hu₀ hw₀ hcut hw₁] at hdeg3
      exact ⟨⟨⟨hV₁ hw₁, hdeg3⟩, hwG⟩, fun h => hw₀ (h ▸ hw₁)⟩
    · exfalso
      have hweq' : w = w₀ := hweq
      have hdeg3 : 3 ≤ (G.induce (V₁ ∪ {w₀})).degree w := hhub.2
      rw [hweq', Graph.degree_induce_union_singleton_far hl₀ hu₀ hw₀ hcut] at hdeg3
      omega
  · intro hmem
    have hmemG : w ∈ G.closedHubNbhd v := hmem.1
    have hwne : w ∉ ({w₀} : Set α) := hmem.2
    have hwG : G.PencilHub w := hmemG.1
    have hwcase : w ∈ G.closedNbhd v := hmemG.2
    have hwmem : w ∈ V₁ ∪ ({w₀} : Set α) :=
      Graph.closedNbhd_subset_of_mem hl₀ hu₀ hw₀ hcut hv hwcase
    have hw₁ : w ∈ V₁ := hwmem.resolve_right hwne
    have hcase' : w ∈ (G.induce (V₁ ∪ {w₀})).closedNbhd v := hNeq.symm ▸ hwcase
    refine ⟨⟨Or.inl hw₁, ?_⟩, hcase'⟩
    rw [Graph.degree_induce_union_singleton_of_mem hl₀ hu₀ hw₀ hcut hw₁]
    exact hwG.2

/-! ## A side that no edge leaves

When no edge crosses `V₁` (`lem:pencil-pair-loop-base-cut`, case (3)), generic realizations of
`G[V₁]` and of `G[V(G) \ V₁]` together form one of `G`
(`hasGenericPencilRealization_of_cutEdges_eq_empty`, `Pair.lean`). For a set `S` such that every
link of `G` from a body of `S` ends in `S`, the degree, the closed hub-neighbourhood and the closed
neighbourhood of a body of `S` are the same in `G[S]` as in `G`; the case applies this to both
sides. -/

/-- **A body of a set closed under links keeps its degree in the induced graph**: if every link of
`G` from a body of `S` ends in `S`, each `v ∈ S` has the same degree in `G.induce S` as in `G`
(`Graph.degree_induce_eq_of_isLink_mem`). -/
theorem _root_.Graph.degree_induce_of_forall_isLink_mem [Finite β] {G : Graph α β} {S : Set α}
    (hS : ∀ e x y, G.IsLink e x y → x ∈ S → y ∈ S) {v : α} (hv : v ∈ S) :
    (G.induce S).degree v = G.degree v :=
  Graph.degree_induce_eq_of_isLink_mem hv fun e y hl => hS e v y hl hv

/-- **A body of a set closed under links keeps its closed hub-neighbourhood in the induced graph**:
with `S` as in `Graph.degree_induce_of_forall_isLink_mem` and `S ⊆ V(G)`, every member of either
closed hub-neighbourhood of `v ∈ S` lies in `S`, where degrees, and so hubs, agree. -/
theorem _root_.Graph.closedHubNbhd_induce_of_forall_isLink_mem [Finite β] {G : Graph α β}
    {S : Set α} (hSVG : S ⊆ V(G)) (hS : ∀ e x y, G.IsLink e x y → x ∈ S → y ∈ S) {v : α}
    (hv : v ∈ S) :
    (G.induce S).closedHubNbhd v = G.closedHubNbhd v := by
  ext w
  constructor
  · rintro ⟨⟨hwS, hdeg⟩, hw⟩
    rw [Graph.degree_induce_of_forall_isLink_mem hS hwS] at hdeg
    refine ⟨⟨hSVG hwS, hdeg⟩, ?_⟩
    rcases hw with rfl | ⟨e, hl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨e, ((Graph.induce_isLink G S e v w).mp hl).1⟩
  · rintro ⟨⟨hwG, hdeg⟩, hw⟩
    have hwS : w ∈ S := by
      rcases hw with rfl | ⟨e, hl⟩
      · exact hv
      · exact hS e v w hl hv
    refine ⟨⟨hwS, ?_⟩, ?_⟩
    · rwa [Graph.degree_induce_of_forall_isLink_mem hS hwS]
    · rcases hw with rfl | ⟨e, hl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨e, (Graph.induce_isLink G S e v w).mpr ⟨hl, hv, hwS⟩⟩

/-- **A body of a set closed under links keeps its closed neighbourhood in the induced graph**: the
form of `Graph.closedHubNbhd_induce_of_forall_isLink_mem` without hubs, and without `S ⊆ V(G)`. -/
theorem _root_.Graph.closedNbhd_induce_of_forall_isLink_mem {G : Graph α β}
    {S : Set α} (hS : ∀ e x y, G.IsLink e x y → x ∈ S → y ∈ S) {v : α} (hv : v ∈ S) :
    (G.induce S).closedNbhd v = G.closedNbhd v := by
  ext w
  constructor
  · rintro (rfl | ⟨e, hl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨e, ((Graph.induce_isLink G S e v w).mp hl).1⟩
  · rintro (rfl | ⟨e, hl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨e, (Graph.induce_isLink G S e v w).mpr ⟨hl, hv, hS e v w hl hv⟩⟩

/-! ## The side opposite a single body

When one side of the cut is a single body `w₀`, joined to `u₀ ∈ V₁ = V(G) \ {w₀}` by the crossing
edge `e₀` (`lem:pencil-pair-loop-base-cut`, case (3)), the side with the far end would be `G`
itself, and the case uses `G[V₁] = G - w₀` (`Pair2.lean`). The two lemmas below hold for any `V₁`
that `e₀` alone crosses: a body of `V₁` other than `u₀` keeps its degree in `G[V₁]`, and `u₀` loses
one. -/

/-- **A body of `V₁` other than `u₀` keeps its degree in `G[V₁]`**: with `e₀` joining `u₀ ∈ V₁` to
`w₀ ∉ V₁`, the only edge crossing `V₁`, an edge of `G` at `v ∈ V₁` with an end outside `V₁` would be
`e₀`, whose ends are `u₀ ≠ v` and `w₀ ∉ V₁` (`Graph.degree_induce_eq_of_isLink_mem`). The form of
`Graph.degree_induce_union_singleton_of_mem` for `G[V₁]`. -/
theorem _root_.Graph.degree_induce_eq_of_ne [Finite β] {G : Graph α β} {V₁ : Set α}
    {e₀ : β} {u₀ w₀ : α} (hl₀ : G.IsLink e₀ u₀ w₀) (hu₀ : u₀ ∈ V₁) (hw₀ : w₀ ∉ V₁)
    (hcut : (G.cutEdges V₁).ncard ≤ 1) {v : α} (hv : v ∈ V₁) (hvne : v ≠ u₀) :
    (G.induce V₁).degree v = G.degree v := by
  refine Graph.degree_induce_eq_of_isLink_mem hv fun e y hl => ?_
  by_contra hy₁
  obtain rfl := Graph.eq_cutEdge_of_isLink_crossing hl₀ hu₀ hw₀ hcut hl hv hy₁
  rcases hl.eq_and_eq_or_eq_and_eq hl₀ with ⟨hveq, -⟩ | ⟨hveq, -⟩
  · exact hvne hveq
  · exact hw₀ (hveq ▸ hv)

/-- **The end `u₀` loses one edge in `G[V₁]`**: for a loopless `G`, and `e₀`, `u₀`, `w₀` and `V₁` as
in `Graph.degree_induce_eq_of_ne`, `G.degree u₀ = (G.induce V₁).degree u₀ + 1`. The edges of `G` at
`u₀` are those of `G[V₁]` and `e₀`: another edge leaving `V₁` would cross it, and `e₀` is not an
edge of `G[V₁]`, as `w₀ ∉ V₁`. -/
theorem _root_.Graph.degree_eq_degree_induce_succ [Finite β] {G : Graph α β} [G.Loopless]
    {V₁ : Set α} {e₀ : β} {u₀ w₀ : α} (hl₀ : G.IsLink e₀ u₀ w₀) (hu₀ : u₀ ∈ V₁) (hw₀ : w₀ ∉ V₁)
    (hcut : (G.cutEdges V₁).ncard ≤ 1) :
    G.degree u₀ = (G.induce V₁).degree u₀ + 1 := by
  have hloopG : {e | G.IsLoopAt e u₀} = ∅ := by
    ext e
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact G.not_isLoopAt e u₀
  have hloopH : {e | (G.induce V₁).IsLoopAt e u₀} = ∅ := by
    ext e
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro h
    exact G.not_isLoopAt e u₀ ((Graph.induce_isLink G V₁ e u₀ u₀).mp h).1
  have hwu : w₀ ≠ u₀ := fun h => hw₀ (h ▸ hu₀)
  have hec_notmem : e₀ ∉ {e | (G.induce V₁).IsNonloopAt e u₀} := by
    rintro ⟨y, -, hl⟩
    obtain ⟨hlG, -, hyV₁⟩ := (Graph.induce_isLink G V₁ e₀ u₀ y).mp hl
    obtain rfl := hlG.right_unique hl₀
    exact hw₀ hyV₁
  have hnonloop_eq :
      {e | G.IsNonloopAt e u₀} = insert e₀ {e | (G.induce V₁).IsNonloopAt e u₀} := by
    ext e
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff]
    constructor
    · rintro ⟨y, hyu, hl⟩
      by_cases hy₁ : y ∈ V₁
      · exact Or.inr ⟨y, hyu, (Graph.induce_isLink G V₁ e u₀ y).mpr ⟨hl, hu₀, hy₁⟩⟩
      · have he := Graph.eq_cutEdge_of_isLink_crossing hl₀ hu₀ hw₀ hcut hl hu₀ hy₁
        exact Or.inl he
    · rintro (rfl | ⟨y, hyu, hl⟩)
      · exact ⟨w₀, hwu, hl₀⟩
      · exact ⟨y, hyu, ((Graph.induce_isLink G V₁ e u₀ y).mp hl).1⟩
  rw [Graph.degree_eq_ncard_add_ncard, Graph.degree_eq_ncard_add_ncard, hloopG, hloopH,
    hnonloop_eq, Set.ncard_insert_of_notMem hec_notmem (Set.toFinite _)]
  omega

end CombinatorialRigidity.Molecular
