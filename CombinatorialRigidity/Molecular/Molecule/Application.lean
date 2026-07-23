/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Mathlib.Data.Set.Card.Arithmetic
import CombinatorialRigidity.Molecular.Molecule.Carrier
import CombinatorialRigidity.Molecular.Molecule.Modelling
import CombinatorialRigidity.Molecular.AlgebraicInduction.PanelLayer
import CombinatorialRigidity.GenericRigidityMatroid

/-!
# The molecule rank formula (`cor:molecule-rank-formula`)

Phase 26. Katoh–Tanigawa Corollary 5.7 (the rank formula is Jackson–Jordán 2008): for a simple
graph `G` of minimum degree at least two on a finite vertex set `V`, `r(G²) = 3|V| - 6 - def(G̃)`,
where `r` is the rank of the `3`-dimensional generic bar-joint rigidity matroid (Phase 24,
`GenericRigidityMatroid.lean`) and `G̃ = G.shadowGraph` is the shadowing multigraph carrier
(`lem:molecule-graph-carrier`, `Carrier.lean`). The formula is the conjunction of two
inequalities, each composing the two Phase-25 modelling links with a Phase-24/molecular rank
bound.

**The lower bound (attainment leg, `≥`).** Theorem 5.6's general-position molecular producer
(`exists_molecular_rankHypothesis_generalPosition`), fed the shadowing carrier's label supply,
produces centres `c` in general position up to order four with the molecular framework attaining
motion-space dimension `D + def(G̃) = 6 + def(G̃)`. The square-graph dictionary
(`molecular_finrank_motions_eq_square_ker`) transports this to `dim ker R(G², c) = 6 + def(G̃)`, so
rank–nullity on `Framework V 3` gives `rank R(G², c) = 3|V| - 6 - def(G̃)`; the generic rank
dominates the realized rank at any placement (`finrank_range_rigidityMap_le_genericRank`).

**The upper bound (`≤`).** At a placement `p` simultaneously generic for row independence and in
general position (`exists_isGenericPlacement_isGeneralPositionPlacement`), the generic rank equals
the realized rank (`finrank_range_rigidityMap_eq_genericRank`). Unlike the lower bound, no producer
supplies an endpoint selector for the shadowing carrier here, so the proof builds one directly: a
linked label gets its (classically chosen) link pair, and every never-linked label — in particular
every padding label — gets a fixed default pair of distinct vertices (which exists since `hmin`
forces `G` to have an edge). The square-graph dictionary identifies `dim ker R(G², p)` with the
resulting molecular framework's motion-space dimension on `G.shadowGraph`, whose hinges are
genuine because general position makes the centres distinct; the genericity-free lower bound
`screwDim_add_deficiency_le_finrank_infinitesimalMotions` then caps the realized rank below by
`3|V| - 6 - def(G̃)`.

See `notes/Phase26.md` and `blueprint/src/chapter/molecule-application.tex`
(`lem:molecule-rank-lower-bound`, `lem:molecule-rank-upper-bound`).

## Main results

* `SimpleGraph.molecule_rank_formula` — the molecule rank formula `r(G²) = 3|V| - 6 - def(G̃)`
  (Katoh–Tanigawa Corollary 5.7; Jackson–Jordán 2008).
* `SimpleGraph.molecule_rank_lower_bound` — the attainment leg of the molecule rank formula.
* `SimpleGraph.molecule_rank_upper_bound` — the upper-bound leg of the molecule rank formula.
* `SimpleGraph.molecule_generic_rank` (`thm:molecule-generic-rank`, Phase 34 Layer M) — the
  molecule rank formula holds at the *realized* rank of every placement generic for row
  independence, not just the generic matroid rank.
* `SimpleGraph.molecule_generic_rigid` (`cor:molecule-generic-rigid`) — every generic realization
  of a square with `def(G̃) = 0` is infinitesimally rigid.
-/

open CombinatorialRigidity.Molecular
open scoped Graph

namespace SimpleGraph

/-- **The molecule rank formula, lower bound (attainment leg)** (`lem:molecule-rank-lower-bound`;
Katoh–Tanigawa 2011 §5.2, Jackson–Jordán 2008). For a simple graph `G` of minimum degree at least
two on a finite vertex set `V`, `3|V| - 6 - def(G̃) ≤ r(G²)`, where `r` is the rank of the
`3`-dimensional generic bar-joint rigidity matroid and `G̃ = G.shadowGraph` is the shadowing
multigraph carrier (`lem:molecule-graph-carrier`).

Fixes the shadowing carrier throughout: its label supply meets Theorem 5.6's general-position
producer, whose molecular realization attains motion-space dimension `6 + def(G̃)`; the
square-graph dictionary carries this to the bar-joint kernel dimension of `(G², c)`, so
rank–nullity gives the realized rank `3|V| - 6 - def(G̃)`, dominated by the generic rank. -/
theorem molecule_rank_lower_bound {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hmin : ∀ v, 2 ≤ G.degree v) :
    3 * (Nat.card V : ℤ) - 6 - G.shadowGraph.deficiency 3 ≤ (G.square.genericRank 3 : ℤ) := by
  classical
  -- Step 1: Theorem 5.6's general-position molecular producer, fed the shadowing carrier.
  obtain ⟨ends, c, hrank, hgp, hends⟩ :=
    exists_molecular_rankHypothesis_generalPosition (card_shadowLabel_lt V) G.shadowGraph
      (by rw [shadowGraph_vertexSet]; exact Set.univ_nonempty)
      (shadowGraph_vertexSet G) (shadowGraph_simple G)
  -- Step 2: the square-graph dictionary transports the motion-space dimension to `ker R(G², c)`.
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

/-- **The molecule rank formula, upper bound** (`lem:molecule-rank-upper-bound`; Katoh–Tanigawa
2011 §5.2, Jackson–Jordán 2008). For a simple graph `G` of minimum degree at least two on a finite,
nonempty vertex set `V`, `r(G²) ≤ 3|V| - 6 - def(G̃)`, where `r` is the rank of the
`3`-dimensional generic bar-joint rigidity matroid and `G̃ = G.shadowGraph` is the shadowing
multigraph carrier (`lem:molecule-graph-carrier`).

At a placement generic for row independence and in general position, the generic rank equals the
realized rank; the square-graph dictionary identifies `dim ker R(G², p)` with the motion-space
dimension of the molecular framework on a hand-built endpoint selector for `G.shadowGraph` (a
linked label's link pair, or a fixed distinct default pair for every never-linked label), whose
hinges are genuine because general position makes the centres distinct; the genericity-free lower
bound on that motion space then caps the realized rank. -/
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
    rw [hends_eq, dif_pos hex]
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
    F.screwDim_add_deficiency_le_finrank_infinitesimalMotions hC
  -- Step 6: rank–nullity on `Framework V 3`, the generic-rank identification, then close the
  -- arithmetic over the named atoms with `omega` (as in the lower bound's proof).
  have hrn := LinearMap.finrank_range_add_finrank_ker (G.square.RigidityMap p)
  rw [Framework.finrank] at hrn
  have hrange := finrank_range_rigidityMap_eq_genericRank G.square hgen
  have hscrew : screwDim 2 = 6 := by decide
  have hcard' : Nat.card V = Fintype.card V := Nat.card_eq_fintype_card
  omega

/-- **The molecule rank formula** (`cor:molecule-rank-formula`; Katoh–Tanigawa 2011
Corollary 5.7). For a simple graph `G` of minimum degree at least two on a finite, nonempty
vertex set `V`, `r(G²) = 3|V| - 6 - def(G̃)`, where `r` is the rank of the `3`-dimensional
generic bar-joint rigidity matroid and `G̃ = G.shadowGraph` is the shadowing multigraph carrier
(`lem:molecule-graph-carrier`). The two complementary bounds
(`molecule_rank_lower_bound`/`molecule_rank_upper_bound`) meet.

The formula is due to Jackson–Jordán 2008, who proved it equivalent to the Molecular Conjecture;
Katoh–Tanigawa's resolution of the conjecture (Theorem 5.6, here
`PanelHingeFramework.molecular_conjecture` and its rank-carrying `d = 3` inputs) makes it
unconditional. -/
theorem molecule_rank_formula {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hmin : ∀ v, 2 ≤ G.degree v) :
    (G.square.genericRank 3 : ℤ) = 3 * (Nat.card V : ℤ) - 6 - G.shadowGraph.deficiency 3 :=
  le_antisymm (G.molecule_rank_upper_bound hmin) (G.molecule_rank_lower_bound hmin)

/-! ## The generic form (`thm:molecule-generic-rank`, `cor:molecule-generic-rigid`)

Phase 34, Layer M. At a placement generic for row independence, the realized rank of `G²`
equals its generic rank (`finrank_range_rigidityMap_eq_genericRank`), so the molecule rank
formula above — a statement about the generic matroid — becomes a statement about *every*
generic realization. See `notes/Phase34.md` and
`blueprint/src/chapter/generic-lift.tex`. -/

/-- **The molecule rank formula at every generic placement** (`thm:molecule-generic-rank`;
Jackson–Jordán 2010, coordinate route). For a simple graph `G` of minimum degree at least two on
a finite, nonempty vertex set `V` and a placement `p : Framework V 3` generic for row
independence, `rank R(G², p) = 3|V| - 6 - def(G̃)`, where `G̃ = G.shadowGraph` is the shadowing
multigraph carrier. A thin composition of `finrank_range_rigidityMap_eq_genericRank` (realized
rank = generic rank at a generic placement) with `molecule_rank_formula`. -/
theorem molecule_generic_rank {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hmin : ∀ v, 2 ≤ G.degree v) {p : Framework V 3}
    (hp : IsGenericPlacement p) :
    (Module.finrank ℝ (LinearMap.range (G.square.RigidityMap p)) : ℤ) =
      3 * (Nat.card V : ℤ) - 6 - G.shadowGraph.deficiency 3 := by
  rw [finrank_range_rigidityMap_eq_genericRank G.square hp]
  exact G.molecule_rank_formula hmin

/-- **Every generic realization of a rigid square** (`cor:molecule-generic-rigid`). For a simple
graph `G` of minimum degree at least two on a finite, nonempty vertex set `V` with
`def(G̃) = 0` (`G̃ = G.shadowGraph`), every placement `p : Framework V 3` generic for row
independence is infinitesimally rigid for `G²`. Rank–nullity on `Framework V 3` turns the rank
identity of `molecule_generic_rank` into the kernel-dimension bound of `IsInfinitesimallyRigid`. -/
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
(`cor:molecule-generic-square-packing`, JJ 2010 p. 586). If `G̃ = G.shadowGraph.mulTilde 3`
(the multiplied graph "`5·G`") contains six pairwise edge-disjoint spanning trees `Ts`, then
every bar-joint realization of `G²` in `ℝ³` at a placement generic for row independence is
infinitesimally rigid.

The `|V| = 1` case is the trivial kernel bound (`Submodule.finrank_le` against
`Framework.finrank`, `3 ≤ 6`), independent of the packing hypothesis. For `|V| ≥ 2`: each
spanning tree `Ts i`, being a tree with vertex set all of `V` (`Ts i ≤s G̃`), has exactly
`|V| - 1` edges (`Graph.IsTree.ncard_vertexSet`); the six trees are pairwise disjoint, so their
union has `6(|V|-1)` edges and (each tree acyclic in itself, hence in `G̃`) is independent in
the `6`-fold cycle-matroid union of `G̃`, hence in `M(G̃) = G.shadowGraph.matroidMG 3`
(`Matroid.union_indep_iff` / `Graph.cycleMatroid_indep`). Since `def(G̃) ≥ 0` bounds
`rank M(G̃) ≤ 6(|V|-1)` (`Graph.rank_add_deficiency_eq`), this independent set of size
`6(|V|-1)` is a base (`Matroid.Indep.isBase_of_ncard`), so `def(G̃) = 0`
(`Graph.isBase_ncard_add_deficiency_eq`). A `0`-dof graph has minimum multigraph degree `≥ 2`
(`Graph.two_le_degree_of_isKDof_zero`, KT Lemma 4.6's degree half) — this route to `hmin`
substitutes for a direct "each tree touches every vertex" degree count, since it reuses
existing Phase-19/22i machinery — which transfers to `G`'s own degree via the shadowing
carrier's neighbor-set identity (`G.shadowGraph` is `Simple`); `molecule_generic_rigid`
closes. -/
theorem molecule_generic_square_packing {V : Type*} [Finite V] [Nonempty V] (G : SimpleGraph V)
    {Ts : Fin 6 → Graph V ((Sym2 V ⊕ Fin (6 * (Nat.card V - 1) + 1)) × Fin (Graph.bodyHingeMult 3))}
    (hspan : ∀ i, Ts i ≤s G.shadowGraph.mulTilde 3) (hTtree : ∀ i, (Ts i).IsTree)
    (hdisj : Pairwise (Function.onFun Disjoint (fun i => E(Ts i))))
    {p : Framework V 3} (hp : IsGenericPlacement p) :
    G.square.IsInfinitesimallyRigid p := by
  classical
  haveI := Fintype.ofFinite V
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
  haveI hMTfin : (G.shadowGraph.mulTilde 3).Finite :=
    { edgeSet_finite := Set.toFinite _, vertexSet_finite := Set.toFinite _ }
  have hTfin : ∀ i, (Ts i).Finite := fun i => hMTfin.mono (hspan i).le
  have hVeq : V(G.shadowGraph.mulTilde 3) = (Set.univ : Set V) := rfl
  -- Each spanning tree has exactly `|V| - 1` edges.
  have hTcard : ∀ i, (E(Ts i)).ncard = Nat.card V - 1 := by
    intro i
    haveI := hTfin i
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
  -- Minimum degree `≥ 2`: a `0`-dof graph is `2`-edge-connected (KT Lemma 4.6's degree half),
  -- transferred to `G` via the shadowing carrier's neighbor-set identity.
  have hmin : ∀ v, 2 ≤ G.degree v := by
    intro v
    have h2 : 2 ≤ G.shadowGraph.degree v :=
      Graph.two_le_degree_of_isKDof_zero (n := 3) hbD hdef
        (v := v) (by rw [shadowGraph_vertexSet]; trivial)
        (by rw [shadowGraph_vertexSet, Set.ncard_univ]; exact hV2)
    haveI := G.shadowGraph_simple
    have hNeq : N(G.shadowGraph, v) = G.neighborSet v := by
      ext y
      simp only [Graph.Neighbor, Set.mem_setOf_eq, SimpleGraph.mem_neighborSet, Graph.Adj,
        shadowGraph_isLink_iff]
    rwa [Graph.degree_eq_ncard_adj, hNeq, ncard_neighborSet_eq_degree] at h2
  exact G.molecule_generic_rigid hmin hdef hp

end SimpleGraph
