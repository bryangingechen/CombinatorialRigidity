/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.EdgesIn
public import CombinatorialRigidity.SquareGraph

/-!
# The three-dimensional Laman condition

Phase 32 (`sec:jacobs-laman3`). Jackson–Jordán 2008 (*On the rigidity of molecular
graphs*, Combinatorica **28**) state a three-dimensional counting condition on graphs
(their §5) that is *not* an instance of the `(k, ℓ)`-sparsity family `IsSparse` at
`(3, 6)`: `IsSparse` quantifies over every `s` with `6 ≤ 3 * #s`, which includes `#s = 2`,
where the bound `3 * 2 - 6 = 0` fails on every graph with an edge, while Jackson–Jordán's
condition constrains only `#s ≥ 3` and holds vacuously on `K₂`. This file supplies the
standalone predicate `SimpleGraph.IsLaman3`, its subgraph monotonicity, and the first
consequence used throughout the chapter: a graph whose square is Laman has maximum degree
at most three (Jackson–Jordán Lemma 5.2).

See `notes/Phase32.md` for the phase plan (L1 recon, *Decisions made*) and
`blueprint/src/chapter/jacobs.tex` (`def:isLaman3`, `lem:isLaman3-mono`,
`lem:isLaman3-degree-le-three`) for the corresponding blueprint nodes.

## Main definitions

* `SimpleGraph.IsLaman3 G` — every `s : Finset V` with `3 ≤ s.card` spans at most
  `3 * s.card - 6` edges, phrased additively (`(G.edgesIn ↑s).ncard + 6 ≤ 3 * s.card`) to
  avoid `ℕ`-subtraction, as with `IsSparse`.

## Main results

* `SimpleGraph.IsLaman3.mono_left` — a subgraph of a Laman graph is Laman.
* `SimpleGraph.IsLaman3.degree_le_three` — Jackson–Jordán Lemma 5.2: if `G²` is Laman,
  every vertex of `G` has degree at most three.
* `SimpleGraph.ncard_edgesIn_neighborSet_square` — the counting half of
  `lem:singleton-part-neighborhood` (Phase 32, `sec:jacobs-counting`): at a vertex of degree
  two or three, `N_G(v)`'s clique of `G²`-edges numbers `2 * d_G(v) - 3`. Unconditional on any
  partition — a companion to `degree_le_three`, not a use of `IsSquareTightPartition`.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*}

/-- The **three-dimensional Laman condition** (Jackson–Jordán 2008 §5): every subset of at
least three vertices spans at most `3|X| - 6` edges. Not an instance of `IsSparse` at
`(3, 6)`: that predicate's guard `ℓ ≤ k * #s` also admits `#s = 2`, where the bound
`3 * 2 - 6 = 0` fails on every graph with an edge, while this condition constrains only
`#s ≥ 3` and holds vacuously on `K₂`. Phrased additively to avoid `ℕ`-subtraction. -/
@[expose] def IsLaman3 (G : SimpleGraph V) : Prop :=
  ∀ s : Finset V, 3 ≤ s.card → (G.edgesIn ↑s).ncard + 6 ≤ 3 * s.card

/-- **Monotonicity.** A subgraph of a Laman graph is Laman: the edge counts inside any
`s : Finset V` only decrease. -/
theorem IsLaman3.mono_left {H H' : SimpleGraph V} (h : H ≤ H') (hH' : H'.IsLaman3) :
    H.IsLaman3 := by
  intro s hs
  refine (Nat.add_le_add_right ?_ 6).trans (hH' s hs)
  exact Set.ncard_le_ncard (fun _ ⟨he₁, he₂⟩ ↦ ⟨edgeSet_subset_edgeSet.mpr h he₁, he₂⟩)
    (H'.edgesIn_finite s)

/-- **Maximum degree three; Jackson–Jordán Lemma 5.2.** If `G²` is Laman, every vertex of
`G` has degree at most three. The closed neighborhood `N_G[v]` is a clique of `G²`
(`isClique_closedNeighborSet_square`) on `d_G(v) + 1` vertices; a clique on five (or more)
vertices already violates the Laman condition, since `C(5, 2) = 10 > 3 * 5 - 6 = 9`
(`IsClique.ncard_edgesIn`). -/
theorem IsLaman3.degree_le_three {G : SimpleGraph V} (hd : G.square.IsLaman3) (v : V)
    [Fintype (G.neighborSet v)] : G.degree v ≤ 3 := by
  classical
  by_contra hlt
  have h4 : 4 ≤ G.degree v := by omega
  set s : Finset V := insert v (G.neighborFinset v) with hs_def
  have hs_coe : (↑s : Set V) = G.closedNeighborSet v := by
    rw [hs_def, Finset.coe_insert, coe_neighborFinset, closedNeighborSet]
  have hs_card : s.card = G.degree v + 1 := by
    rw [hs_def, Finset.card_insert_of_notMem (by simp), card_neighborFinset_eq_degree]
  obtain ⟨t, hts, htc⟩ := s.exists_subset_card_eq (n := 5) (by omega)
  have hclique : G.square.IsClique (↑t : Set V) :=
    (isClique_closedNeighborSet_square G v).subset (hs_coe ▸ (Finset.coe_subset.mpr hts))
  have hcount := IsClique.ncard_edgesIn hclique
  rw [htc] at hcount
  have hLaman := hd t (by omega)
  rw [hcount, htc, show Nat.choose 5 2 = 10 from rfl] at hLaman
  omega

/-- **The clique-edge count at a vertex of degree two or three; JJ eq. (5), (7) count.**
If `G²` is Laman and `v` has degree at least two, `N_G(v)` (always a clique of `G²`,
`isClique_neighborSet_square`) has exactly `2 * d_G(v) - 3` edges of `G²` inside it (additive
form to avoid `ℕ`-subtraction). Unconditional on any partition: the degree bound pins
`d_G(v) ∈ {2, 3}` (`degree_le_three`, the hypothesis), and `C(2,2) = 1 = 2·2 - 3`,
`C(3,2) = 3 = 2·3 - 3` both check out. This is the counting half of
`lem:singleton-part-neighborhood`; the singleton-part hypothesis there is only needed to show
every edge counted is a *special cross* edge, not for the count itself. -/
theorem ncard_edgesIn_neighborSet_square {G : SimpleGraph V} (hd : G.square.IsLaman3)
    {v : V} [Fintype (G.neighborSet v)] (hmindeg : 2 ≤ G.degree v) :
    (G.square.edgesIn (G.neighborSet v)).ncard + 3 = 2 * G.degree v := by
  classical
  have hclique_finset : G.square.IsClique (↑(G.neighborFinset v) : Set V) := by
    rw [coe_neighborFinset]; exact isClique_neighborSet_square G v
  have hcount := IsClique.ncard_edgesIn hclique_finset
  rw [coe_neighborFinset, card_neighborFinset_eq_degree] at hcount
  have hle : G.degree v ≤ 3 := hd.degree_le_three v
  obtain hd2 | hd3 : G.degree v = 2 ∨ G.degree v = 3 := by omega
  · rw [hd2] at hcount ⊢; rw [hcount]; decide
  · rw [hd3] at hcount ⊢; rw [hcount]; decide

end SimpleGraph
