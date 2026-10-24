/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Carrier
import CombinatorialRigidity.Molecular.Molecule.Modelling

/-!
# The molecule rank formula

KT Corollary 5.7, the molecule rank formula `r(G²) = 3|V| - 6 - def(G̃)` for a simple graph `G` of
minimum degree at least two on a finite, nonempty set `V`, as `sec:molecule-application-formula`
presents it, and its forms at generic placements, as `sec:generic-lift-molecule` presents them. Here
`r` is the rank function of the generic rigidity matroid in `ℝ³` (`GenericRigidityMatroid.lean`),
and `def(G̃)` is `G.shadowGraph.deficiency 3`, the deficiency of `G̃ = 5·G'` for the multigraph
`G' = G.shadowGraph` of `lem:molecule-graph-carrier` (`Carrier.lean`). Jackson and Jordán 2008
conjectured the formula (their Conjecture 2.2), proved `≤` (their Theorem 4.1), and proved the
formula equivalent to the bar-joint form of the molecular conjecture (their Theorem 4.3). Katoh and
Tanigawa deduce it from their Theorem 5.6 (KT p. 671).

**The lower bound** (`molecule_rank_lower_bound`). The molecular realization of
`thm:panel-hinge-iff-molecular` (`exists_molecular_rankHypothesis_generalPosition`) on `G'` has
centres `c` in general position up to order four and a motion space of dimension `6 + def(G̃)`. The
square-graph dictionary (`molecular_finrank_motions_eq_square_ker`) gives
`dim ker R(G², c) = 6 + def(G̃)`, so by rank–nullity on `Framework V 3`,
`rank R(G², c) = 3|V| - 6 - def(G̃)`; and the generic rank is at least the rank at any placement
(`finrank_range_rigidityMap_le_genericRank`).

**The upper bound** (`molecule_rank_upper_bound`). At a placement `p` generic for row independence
and in general position up to order four (`exists_isGenericPlacement_isGeneralPositionPlacement`),
the generic rank is the rank of `R(G², p)` (`finrank_range_rigidityMap_eq_genericRank`). The proof
builds an endpoint selector for `G'`: a label that `G'` links gets the ends of a link (chosen
classically), and every other label, each label of the second summand among them, one fixed pair of
adjacent vertices of `G`, which exists as `hmin` gives `G` an edge. The square-graph dictionary
identifies `dim ker R(G², p)` with the dimension of the motion space of the molecular framework on
`G'` with this selector, whose hinges are nondegenerate since general position makes the centres
distinct; that dimension is at least `6 + def(G̃)`
(`screwDim_add_deficiency_le_finrank_infinitesimalMotions`, `lem:deficiency-rank-bound`).

## Main results

* `SimpleGraph.molecule_rank_formula`: the molecule rank formula (`cor:molecule-rank-formula`).
* `SimpleGraph.molecule_rank_lower_bound` and `SimpleGraph.molecule_rank_upper_bound`: its two
  inequalities.
* `SimpleGraph.molecule_generic_rank`: the formula for the rank of `R(G², p)` at every placement `p`
  generic for row independence (`thm:molecule-generic-rank`).
* `SimpleGraph.molecule_generic_rigid`: when `def(G̃) = 0`, every such placement is infinitesimally
  rigid for `G²` (`cor:molecule-generic-rigid`).
* `SimpleGraph.molecule_generic_square_packing`: so is every such placement when `5·G'` contains six
  edge-disjoint spanning trees (`cor:molecule-generic-square-packing`).
-/

open CombinatorialRigidity.Molecular
open scoped Graph

namespace SimpleGraph

/-- **The lower bound of the molecule rank formula** (`lem:molecule-rank-lower-bound`; from KT
Theorem 5.6, Katoh and Tanigawa 2011, §5.2): for a simple graph `G` of minimum degree at least two
on a finite, nonempty set `V`, `3|V| - 6 - def(G̃) ≤ r(G²)`, where `r` is the rank function of the
generic rigidity matroid in `ℝ³` and `def(G̃)` is `G.shadowGraph.deficiency 3`, the deficiency of
`G̃ = 5·G'` for the multigraph `G' = G.shadowGraph` (`lem:molecule-graph-carrier`).

The molecular realization of `thm:panel-hinge-iff-molecular` on `G'`, with centres `c`, has a motion
space of dimension `6 + def(G̃)`. The square-graph dictionary makes this the dimension of
`ker R(G², c)`, so by rank–nullity `rank R(G², c) = 3|V| - 6 - def(G̃)`, which the generic rank
bounds. -/
theorem molecule_rank_lower_bound {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hmin : ∀ v, 2 ≤ G.degree v) :
    3 * (Nat.card V : ℤ) - 6 - G.shadowGraph.deficiency 3 ≤ (G.square.genericRank 3 : ℤ) := by
  classical
  -- Step 1: the molecular realization of `thm:panel-hinge-iff-molecular` on `G.shadowGraph`.
  obtain ⟨ends, c, hrank, hgp, hends⟩ :=
    exists_molecular_rankHypothesis_generalPosition (card_shadowLabel_lt V) G.shadowGraph
      (by rw [shadowGraph_vertexSet]; exact Set.univ_nonempty)
      (shadowGraph_vertexSet G) (shadowGraph_simple G)
  -- Step 2: the square-graph dictionary gives the motion-space dimension as `dim ker R(G², c)`.
  have hshadow : ∀ u v, u ≠ v → ((∃ e, G.shadowGraph.IsLink e u v) ↔ G.Adj u v) :=
    fun u v _ => shadowGraph_isLink_iff G u v
  have hkey := molecular_finrank_motions_eq_square_ker hshadow hends hmin hgp
  -- Step 3: `RankHypothesis` gives the motion-space dimension; combine into the kernel dimension.
  have hrank' : (Module.finrank ℝ
      (molecularOfCentres G.shadowGraph ends c).infinitesimalMotions : ℤ)
      = screwDim 2 + G.shadowGraph.deficiency 3 := hrank
  have hscrew : screwDim 2 = 6 := by decide
  -- Step 4: rank–nullity on `Framework V 3`, then dominate by the generic rank. (`omega` closes
  -- the arithmetic directly, over the atoms `hkey`/`hrank'`/`hscrew`/`hrn`/`hdom`/`hcard` name —
  -- a manual `rw` on `6`/`Nat.card V` here breaks, since both literals also occur inside
  -- `G.shadowGraph`'s label-type index, an unrelated dependent-type occurrence.)
  have hrn := LinearMap.finrank_range_add_finrank_ker (G.square.RigidityMap c)
  rw [Framework.finrank] at hrn
  have hdom : Module.finrank ℝ (LinearMap.range (G.square.RigidityMap c)) ≤
      G.square.genericRank 3 := finrank_range_rigidityMap_le_genericRank G.square c
  have hcard : Nat.card V = Fintype.card V := Nat.card_eq_fintype_card
  omega

/-- **The upper bound of the molecule rank formula** (`lem:molecule-rank-upper-bound`; Jackson and
Jordán 2008, Theorem 4.1): for a simple graph `G` of minimum degree at least two on a finite,
nonempty set `V`, `r(G²) ≤ 3|V| - 6 - def(G̃)`, where `r` is the rank function of the generic
rigidity matroid in `ℝ³` and `def(G̃)` is `G.shadowGraph.deficiency 3`, the deficiency of
`G̃ = 5·G'` for the multigraph `G' = G.shadowGraph` (`lem:molecule-graph-carrier`).

Jackson and Jordán bound `r(G²)` by an independent cover of `G²`; the proof here goes through
molecular frameworks. At a placement generic for row independence and in general position up to
order four, the generic rank is the rank of `R(G², p)`. The square-graph dictionary identifies
`dim ker R(G², p)` with the dimension of the motion space of the molecular framework on `G'` with an
endpoint selector built here (a linked label gets the ends of a link, and every other label one
fixed pair of adjacent vertices), whose hinges are nondegenerate since general position makes the
centres distinct; and that dimension is at least `6 + def(G̃)` (`lem:deficiency-rank-bound`). -/
theorem molecule_rank_upper_bound {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hmin : ∀ v, 2 ≤ G.degree v) :
    (G.square.genericRank 3 : ℤ) ≤ 3 * (Nat.card V : ℤ) - 6 - G.shadowGraph.deficiency 3 := by
  classical
  -- A fixed pair of distinct vertices, for every never-linked label (in particular every padding
  -- label) of the endpoint selector below.
  obtain ⟨v₀⟩ := (inferInstance : Nonempty V)
  have hpos : 0 < (G.neighborFinset v₀).card := by
    rw [G.card_neighborFinset_eq_degree]; have := hmin v₀; omega
  obtain ⟨u₀, hu₀mem⟩ := Finset.card_pos.mp hpos
  rw [mem_neighborFinset] at hu₀mem
  -- Step 1: a placement simultaneously generic for row independence and in general position.
  obtain ⟨p, hgen, hgp⟩ := exists_isGenericPlacement_isGeneralPositionPlacement (V := V)
  -- Step 2: the endpoint selector for `G.shadowGraph`: a linked label's (classically chosen)
  -- link pair, or the fixed distinct pair `(v₀, u₀)` for a never-linked label.
  let ends : (Sym2 V ⊕ Fin (6 * (Nat.card V - 1) + 1)) → V × V := fun e =>
    if h : ∃ x y, G.shadowGraph.IsLink e x y then (h.choose, h.choose_spec.choose) else (v₀, u₀)
  have hends_eq : ∀ e, ends e = if h : ∃ x y, G.shadowGraph.IsLink e x y then
      (h.choose, h.choose_spec.choose) else (v₀, u₀) := fun _ => rfl
  have hends_ne : ∀ e, (ends e).1 ≠ (ends e).2 := by
    intro e
    rw [hends_eq]
    split_ifs with h
    · exact h.choose_spec.choose_spec.1.ne
    · exact hu₀mem.ne
  have hends : ∀ e u v, G.shadowGraph.IsLink e u v →
      G.shadowGraph.IsLink e (ends e).1 (ends e).2 := by
    intro e u v huv
    have hex : ∃ x y, G.shadowGraph.IsLink e x y := ⟨u, v, huv⟩
    rw [hends_eq, dite_eq_left hex]
    exact hex.choose_spec.choose_spec
  have hshadow : ∀ u v, u ≠ v → ((∃ e, G.shadowGraph.IsLink e u v) ↔ G.Adj u v) :=
    fun u v _ => shadowGraph_isLink_iff G u v
  -- Step 3: every label's supporting extensor is nonzero — its endpoints are distinct
  -- (`hends_ne`) and `p` is injective (general position).
  set F := molecularOfCentres G.shadowGraph ends p with hF_def
  have hC : ∀ e, F.supportExtensor e ≠ 0 := by
    intro e
    rw [hF_def, molecularOfCentres_supportExtensor]
    apply lineExtensor_ne_zero_of_ne
    intro heq
    exact hends_ne e (hgp.injective (WithLp.ofLp_injective 2 heq))
  -- Step 4: the square-graph dictionary identifies `dim ker R(G², p)` with the molecular motions.
  have hkey : Module.finrank ℝ F.infinitesimalMotions
      = Module.finrank ℝ (LinearMap.ker (G.square.RigidityMap p)) :=
    molecular_finrank_motions_eq_square_ker hshadow hends hmin hgp
  -- Step 5: the genericity-free lower bound on the molecular motion-space dimension.
  have hub : (screwDim 2 : ℤ) + G.shadowGraph.deficiency 3 ≤
      (Module.finrank ℝ F.infinitesimalMotions : ℤ) :=
    F.screwDim_add_deficiency_le_finrank_infinitesimalMotions fun e _ _ _ => hC e
  -- Step 6: rank–nullity on `Framework V 3`, the generic-rank identification, then close the
  -- arithmetic over the named atoms with `omega` (as in the lower bound's proof).
  have hrn := LinearMap.finrank_range_add_finrank_ker (G.square.RigidityMap p)
  rw [Framework.finrank] at hrn
  have hrange := finrank_range_rigidityMap_eq_genericRank G.square hgen
  have hscrew : screwDim 2 = 6 := by decide
  have hcard' : Nat.card V = Fintype.card V := Nat.card_eq_fintype_card
  omega

/-- **The molecule rank formula** (`cor:molecule-rank-formula`; Jackson and Jordán 2008, Conjecture
2.2; Katoh and Tanigawa 2011, Corollary 5.7): for a simple graph `G` of minimum degree at least two
on a finite, nonempty set `V`, `r(G²) = 3|V| - 6 - def(G̃)`, where `r` is the rank function of the
generic rigidity matroid in `ℝ³` and `def(G̃)` is `G.shadowGraph.deficiency 3`, the deficiency of
`G̃ = 5·G'` for the multigraph `G' = G.shadowGraph` (`lem:molecule-graph-carrier`). The two bounds
`molecule_rank_lower_bound` and `molecule_rank_upper_bound` meet.

Jackson and Jordán conjectured the formula, proved `≤` (their Theorem 4.1), and proved the formula
equivalent to the bar-joint form of the molecular conjecture (their Theorem 4.3). Katoh and Tanigawa
deduce it from their Theorem 5.6 (KT p. 671). -/
theorem molecule_rank_formula {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hmin : ∀ v, 2 ≤ G.degree v) :
    (G.square.genericRank 3 : ℤ) = 3 * (Nat.card V : ℤ) - 6 - G.shadowGraph.deficiency 3 :=
  le_antisymm (G.molecule_rank_upper_bound hmin) (G.molecule_rank_lower_bound hmin)

/-! ## The formula at generic placements

At a placement generic for row independence, the rank of `R(G², p)` is the generic rank
(`finrank_range_rigidityMap_eq_genericRank`). So the molecule rank formula gives the rank at every
such placement, and when `def(G̃) = 0` every such placement is infinitesimally rigid for `G²`, as
`sec:generic-lift-molecule` presents them (`thm:molecule-generic-rank`,
`cor:molecule-generic-rigid`, `cor:molecule-generic-square-packing`). -/

/-- **The molecule rank formula at every generic placement** (`thm:molecule-generic-rank`): for a
simple graph `G` of minimum degree at least two on a finite, nonempty set `V` and a placement
`p : Framework V 3` generic for row independence, `rank R(G², p) = 3|V| - 6 - def(G̃)`, where
`def(G̃)` is `G.shadowGraph.deficiency 3`. At such a placement the rank is the generic rank
(`finrank_range_rigidityMap_eq_genericRank`), which `molecule_rank_formula` gives. -/
theorem molecule_generic_rank {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hmin : ∀ v, 2 ≤ G.degree v) {p : Framework V 3}
    (hp : IsGenericPlacement p) :
    (Module.finrank ℝ (LinearMap.range (G.square.RigidityMap p)) : ℤ) =
      3 * (Nat.card V : ℤ) - 6 - G.shadowGraph.deficiency 3 := by
  rw [finrank_range_rigidityMap_eq_genericRank G.square hp]
  exact G.molecule_rank_formula hmin

/-- **Every generic realization of a rigid square** (`cor:molecule-generic-rigid`): for a simple
graph `G` of minimum degree at least two on a finite, nonempty set `V` with
`G.shadowGraph.deficiency 3 = 0`, that is `def(G̃) = 0`, every placement `p : Framework V 3` generic
for row independence is infinitesimally rigid for `G²`. Rank–nullity on `Framework V 3` turns the
rank of `molecule_generic_rank` into the bound on `dim ker R(G², p)` that `IsInfinitesimallyRigid`
states. -/
theorem molecule_generic_rigid {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hmin : ∀ v, 2 ≤ G.degree v) (hdef : G.shadowGraph.deficiency 3 = 0)
    {p : Framework V 3} (hp : IsGenericPlacement p) :
    G.square.IsInfinitesimallyRigid p := by
  have hrank := G.molecule_generic_rank hmin hp
  rw [hdef, sub_zero] at hrank
  have hrn := LinearMap.finrank_range_add_finrank_ker (G.square.RigidityMap p)
  rw [Framework.finrank] at hrn
  have hcard : Nat.card V = Fintype.card V := Nat.card_eq_fintype_card
  rw [IsInfinitesimallyRigid]
  omega

/-- **Generic rigidity of squares from six spanning trees; Jackson–Jordán**
(`cor:molecule-generic-square-packing`, JJ 2010 p. 586): if `G̃ = G.shadowGraph.mulTilde 3`, the
multiplied graph `5·G'` of the multigraph `G' = G.shadowGraph`, contains six pairwise edge-disjoint
spanning trees `Ts`, then every placement `p : Framework V 3` generic for row independence is
infinitesimally rigid for `G²`. Jackson and Jordán note it as a consequence of the molecular
conjecture and Tay and Whiteley's theorem on body-and-hinge frameworks.

If `|V| = 1`, then `dim ker R(G², p) ≤ 3 ≤ 6` (`Submodule.finrank_le`, `Framework.finrank`),
whatever the trees. Let `|V| ≥ 2`. Each tree `Ts i` spans `G̃`, so it has `|V| - 1` edges
(`Graph.IsTree.ncard_vertexSet`) and is acyclic in `G̃`. As the six are pairwise disjoint, their
edges form a set of `6(|V| - 1)` edges independent in the union of six copies of the cycle matroid
of `G̃` (`Matroid.union_indep_iff`, `Graph.cycleMatroid_indep`), hence in
`M(G̃) = G.shadowGraph.matroidMG 3`. As `def(G̃) ≥ 0`, `rank M(G̃) ≤ 6(|V| - 1)`
(`Graph.rank_add_deficiency_eq`), so the set is a base (`Matroid.Indep.isBase_of_ncard`) and
`def(G̃) = 0` (`Graph.isBase_ncard_add_deficiency_eq`). So `G'` is a `0`-dof-graph on at least two
vertices, and its vertices have degree at least two (`Graph.two_le_degree_of_isKDof_zero`,
`lem:deficiency-zero-connected`). As `G'` is simple and links exactly the adjacent pairs of `G`,
each vertex has the same degree in `G`, and `molecule_generic_rigid` applies. -/
theorem molecule_generic_square_packing {V : Type*} [Finite V] [Nonempty V] (G : SimpleGraph V)
    {Ts : Fin 6 → Graph V ((Sym2 V ⊕ Fin (6 * (Nat.card V - 1) + 1)) × Fin (Graph.bodyHingeMult 3))}
    (hspan : ∀ i, Ts i ≤s G.shadowGraph.mulTilde 3) (hTtree : ∀ i, (Ts i).IsTree)
    (hdisj : Pairwise (Function.onFun Disjoint (fun i => E(Ts i))))
    {p : Framework V 3} (hp : IsGenericPlacement p) :
    G.square.IsInfinitesimallyRigid p := by
  classical
  have := Fintype.ofFinite V
  by_cases hV1 : Nat.card V = 1
  · -- Trivial case: the ambient framework space has dimension `≤ 3 ≤ 6` regardless of `G`.
    have hker : Module.finrank ℝ (LinearMap.ker (G.square.RigidityMap p)) ≤
        Module.finrank ℝ (Framework V 3) := Submodule.finrank_le _
    rw [Framework.finrank, ← Nat.card_eq_fintype_card, hV1] at hker
    rw [IsInfinitesimallyRigid]
    omega
  -- `|V| ≥ 2`.
  have hbD : 1 ≤ Graph.bodyBarDim 3 := by decide
  have hV2 : 2 ≤ Nat.card V := by
    have := Nat.card_pos (α := V)
    omega
  have hne : V(G.shadowGraph).Nonempty := by rw [shadowGraph_vertexSet]; exact Set.univ_nonempty
  -- Finiteness of the ambient multiplied shadow graph, inherited by each tree.
  have hMTfin : (G.shadowGraph.mulTilde 3).Finite :=
    { edgeSet_finite := Set.toFinite _, vertexSet_finite := Set.toFinite _ }
  have hTfin : ∀ i, (Ts i).Finite := fun i => hMTfin.mono (hspan i).le
  have hVeq : V(G.shadowGraph.mulTilde 3) = (Set.univ : Set V) := rfl
  -- Each spanning tree has exactly `|V| - 1` edges.
  have hTcard : ∀ i, (E(Ts i)).ncard = Nat.card V - 1 := by
    intro i
    have := hTfin i
    have hnv := (hTtree i).ncard_vertexSet
    rw [(hspan i).vertexSet_eq, hVeq, Set.ncard_univ] at hnv
    omega
  -- Each spanning tree is acyclic in the ambient multiplied shadow graph.
  have hacyc : ∀ i, (G.shadowGraph.mulTilde 3).IsAcyclicSet (E(Ts i)) := by
    intro i
    have hself : (Ts i).IsAcyclicSet (E(Ts i)) := by
      rw [Graph.isAcyclicSet_iff]
      exact ⟨subset_rfl, by rw [Graph.restrict_self]; exact (hTtree i).isForest⟩
    exact hself.mono (hspan i).le
  have hBsub : (⋃ i, E(Ts i)) ⊆ E(G.shadowGraph.mulTilde 3) :=
    Set.iUnion_subset fun i => (hacyc i).subset
  -- The union of the six trees' edge sets is independent in the `6`-fold cycle-matroid union.
  have hBunion : (Matroid.Union (fun _ : Fin 6 => (G.shadowGraph.mulTilde 3).cycleMatroid)).Indep
      (⋃ i, E(Ts i)) := by
    rw [Matroid.union_indep_iff]
    exact ⟨fun i => E(Ts i), rfl, fun i => by rw [Graph.cycleMatroid_indep]; exact hacyc i⟩
  -- `B := ⋃ i, E(Ts i)` is independent in `matroidMG` and has size `6 * (Nat.card V - 1)`.
  have hBindep : (G.shadowGraph.matroidMG 3).Indep (⋃ i, E(Ts i)) := by
    rw [Graph.matroidMG, Matroid.restrict_indep_iff]
    exact ⟨hBunion, hBsub⟩
  have hBcard : (⋃ i, E(Ts i)).ncard = 6 * (Nat.card V - 1) := by
    rw [Set.ncard_iUnion_of_fintype (fun i => Set.toFinite _) hdisj]
    simp [hTcard, Finset.sum_const, Finset.card_univ, mul_comm]
  -- `B` is a base: `def(G̃) ≥ 0` caps `rank M(G̃) ≤ 6(|V|-1) = |B|`.
  have hb6 : (Graph.bodyBarDim 3 : ℤ) = 6 := by decide
  have hcast : ((⋃ i, E(Ts i)).ncard : ℤ) =
      (Graph.bodyBarDim 3 : ℤ) * ((V(G.shadowGraph).ncard : ℤ) - 1) := by
    rw [hBcard, shadowGraph_vertexSet, Set.ncard_univ, hb6]
    push_cast [Nat.cast_sub (show 1 ≤ Nat.card V by omega)]
    ring
  have hrle : (G.shadowGraph.matroidMG 3).rank ≤ (⋃ i, E(Ts i)).ncard := by
    have heq := G.shadowGraph.rank_add_deficiency_eq 3 hbD hne
    have hdefnn := G.shadowGraph.deficiency_nonneg 3 hne
    have : ((G.shadowGraph.matroidMG 3).rank : ℤ) ≤ ((⋃ i, E(Ts i)).ncard : ℤ) := by
      rw [hcast]; linarith
    exact_mod_cast this
  have hBbase : (G.shadowGraph.matroidMG 3).IsBase (⋃ i, E(Ts i)) :=
    hBindep.isBase_of_ncard hrle
  -- `def(G̃) = 0` from the base-size identity.
  have hdef : G.shadowGraph.deficiency 3 = 0 := by
    have heqb := G.shadowGraph.isBase_ncard_add_deficiency_eq 3 hbD hne hBbase
    rw [hcast] at heqb
    linarith
  -- Minimum degree `≥ 2`: a `0`-dof-graph on two or more vertices has it
  -- (`lem:deficiency-zero-connected`), and `G.shadowGraph` has the neighbours of `G`.
  have hmin : ∀ v, 2 ≤ G.degree v := by
    intro v
    have h2 : 2 ≤ G.shadowGraph.degree v :=
      Graph.two_le_degree_of_isKDof_zero (n := 3) hbD hdef
        (v := v) (by rw [shadowGraph_vertexSet]; trivial)
        (by rw [shadowGraph_vertexSet, Set.ncard_univ]; exact hV2)
    have := G.shadowGraph_simple
    have hNeq : N(G.shadowGraph, v) = G.neighborSet v := by
      ext y
      simp only [Graph.Neighbor, Set.mem_ofPred_eq, SimpleGraph.mem_neighborSet, Graph.Adj,
        shadowGraph_isLink_iff]
    rwa [Graph.degree_eq_ncard_adj, hNeq, ncard_neighborSet_eq_degree] at h2
  exact G.molecule_generic_rigid hmin hdef hp

end SimpleGraph
