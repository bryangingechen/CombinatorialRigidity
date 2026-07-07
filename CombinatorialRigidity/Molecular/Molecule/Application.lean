/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Carrier
import CombinatorialRigidity.Molecular.Molecule.Modelling
import CombinatorialRigidity.GenericRigidityMatroid

/-!
# The molecule rank formula: the lower bound (`lem:molecule-rank-lower-bound`)

Phase 26. The attainment leg of Katoh–Tanigawa Corollary 5.7 (Jackson–Jordán 2008): for a simple
graph `G` of minimum degree at least two on a finite vertex set `V`,
`3|V| - 6 - def(G̃) ≤ r(G²)`, where `r` is the rank of the `3`-dimensional generic bar-joint
rigidity matroid (Phase 24, `GenericRigidityMatroid.lean`) and `G̃ = G.shadowGraph` is the
shadowing multigraph carrier (`lem:molecule-graph-carrier`, `Carrier.lean`).

The proof composes the two Phase-25 modelling links with the Phase-24 domination bound: Theorem
5.6's general-position molecular producer (`exists_molecular_rankHypothesis_generalPosition`), fed
the shadowing carrier's label supply, produces centres `c` in general position up to order four
with the molecular framework attaining motion-space dimension `D + def(G̃) = 6 + def(G̃)`. The
square-graph dictionary (`molecular_finrank_motions_eq_square_ker`) transports this to
`dim ker R(G², c) = 6 + def(G̃)`, so rank–nullity on `Framework V 3` gives
`rank R(G², c) = 3|V| - 6 - def(G̃)`; the generic rank dominates the realized rank at any placement
(`finrank_range_rigidityMap_le_genericRank`).

See `notes/Phase26.md` and `blueprint/src/chapter/molecule-application.tex`
(`lem:molecule-rank-lower-bound`).

## Main results

* `SimpleGraph.molecule_rank_lower_bound` — the attainment leg of the molecule rank formula.
-/

open CombinatorialRigidity.Molecular

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

end SimpleGraph
