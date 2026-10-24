/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Deficiency
import CombinatorialRigidity.Mathlib.GroupTheory.Perm.List
import Matroid.Graph.Minor.Defs

/-!
# The combinatorial induction: circuits, contraction and the graph operations

The first file of the combinatorial induction (`sec:molecular-induction`), after Katoh and
Tanigawa (2011, *A proof of the molecular conjecture*, Discrete Comput. Geom. **45**, §§3.2,
4 and 6). For a multigraph `G` and `D = bodyBarDim n`, with `G̃ = (D-1)·G` and its matroid `M(G̃)`
from `Molecular/Deficiency.lean`, it proves:

* the subgraph `G[V(X)]` induced by the ends of a set `X` of edges of `G̃` (`inducedSpan`,
  `def:induced-span`), KT Lemma 3.4 (a circuit induces a rigid subgraph,
  `lem:circuit-induces-rigid`), and a consequence for a loopless `G` with no proper rigid
  subgraph, from the proof of KT Lemma 4.5(i); `sec:molecular-induction-inherited`;
* a proper rigid subgraph when every degree is at least three (`lem:pencil-min-degree-rigid`,
  `sec:pencil-reduction`);
* the independent sets of `M(G̃)` as unions of `D` forests (`lem:forest-packing-decomp`), and
  KT Lemma 4.1 failing at the empty set (`ex:kt-41-overquantified`);
  `sec:molecular-induction-forest`;
* the rank of a rigid subgraph and the contraction of `M(G̃)` by its edges
  (`lem:rigid-full-rank`, `lem:contract-rank-bridge`, `lem:contract-deficiency-conservation`),
  the deficiency half of KT Lemma 3.5; `sec:molecular-induction-inherited`;
* removal and splitting off at a vertex (`def:graph-operations`) and their common subgraph
  (`lem:splitoff-edge-substitution`), `sec:molecular-induction-operations`, with an endpoint
  choice for the edges of `G` (`endsOf`, `fmlnote:graph-operations`) and the vertex count after
  splitting off (`lem:reduction-measure`);
* KT Lemma 6.7(ii), that splitting off keeps the graph simple (`lem:splitoff-simple`,
  `sec:simplicity-and-adjacent-pair`), and a cycle through a vertex of degree at least three as
  a proper rigid subgraph (`lem:chain-cycle-dichotomy`);
* the three-vertex case of KT Lemma 6.7(i) (`lem:triangle-third-edge`) and KT's isomorphism from
  `G_a^{vc}` to `G_v^{ab}` (`lem:splitOff-isLink-relabel`), in `case-iii.tex`;
* the chains and cycles of KT Lemma 4.6 (`ChainData`, `def:chain-data`; `CycleData`,
  `def:cycle-data`), with the renamings of a chain that Case III of the algebraic induction uses
  at every `d` (KT eqs. (6.54) and (6.55)).

The deficiency bounds, the reducible vertex, the contraction of a graph and the forest surgery
are in the sibling files `SplitOffDeficiency.lean`, `ReducibleVertex.lean`, `Contraction.lean`
and `ForestSurgery/`.
-/

namespace Graph

open Set Matroid

variable {α β : Type*}

/-! ## The subgraph induced by the ends of a set of edges (`def:induced-span`) -/

/-- The **vertices spanned by a set of edges of `G̃`** (`def:induced-span`): for a set `X` of
edges of `G̃ = (D-1)·G`, the set `V(X) = (G̃).spanningVerts X` of the vertices incident with an
edge of `X`. It is the `V(X)` of KT Lemma 3.4 (p. 658). -/
def fiberSpan (G : Graph α β) (n : ℕ) (X : Set (β × Fin (bodyHingeMult n))) : Set α :=
  (G.mulTilde n).spanningVerts X

/-- The **subgraph induced by the ends of a set of edges** `G[V(X)]` (`def:induced-span`): for a
set `X` of edges of `G̃ = (D-1)·G`, mathlib's `Graph.induce` of `G` on `V(X) = G.fiberSpan n X`.
KT Lemma 3.4 (p. 658) says that it is rigid when `X` is a circuit of `M(G̃)`. -/
def inducedSpan (G : Graph α β) (n : ℕ) (X : Set (β × Fin (bodyHingeMult n))) : Graph α β :=
  G.induce (G.fiberSpan n X)

@[simp]
lemma vertexSet_inducedSpan (G : Graph α β) (n : ℕ) (X : Set (β × Fin (bodyHingeMult n))) :
    V(G.inducedSpan n X) = G.fiberSpan n X := by
  rw [inducedSpan, vertexSet_induce]

/-! ## The endpoint choice of a graph (`fmlnote:graph-operations`)

The formalization fixes, for each edge of `G`, an ordered pair of its ends, the *endpoint
choice* of `G` (`fmlnote:graph-operations`). The realizations of the algebraic induction take
the ends of the edges of `G` from it, as the endpoint selector `ends : β → α × α` of a
panel-hinge framework (`fmlnote:panel-hinge-nondegenerate`).
-/

open Classical in
/-- **The endpoint choice of a graph** (`fmlnote:graph-operations`): for each `e : β`, an ordered
pair `(x, y)`, chosen with `Classical.choice` so that `G.IsLink e x y` when `e ∈ E(G)`
(`isLink_endsOf`). At an `e ∉ E(G)` it is `(default, default)`. -/
noncomputable def endsOf [Inhabited α] (G : Graph α β) (e : β) : α × α :=
  if h : ∃ x y, G.IsLink e x y then (h.choose, h.choose_spec.choose) else (default, default)

/-- **The endpoint choice gives the ends of every edge** (`fmlnote:graph-operations`): if
`e ∈ E(G)`, then `G.IsLink e (G.endsOf e).1 (G.endsOf e).2`, as an edge has ends
(`exists_isLink_of_mem_edgeSet`). -/
lemma isLink_endsOf [Inhabited α] (G : Graph α β) {e : β} (he : e ∈ E(G)) :
    G.IsLink e (G.endsOf e).1 (G.endsOf e).2 := by
  have h : ∃ x y, G.IsLink e x y := exists_isLink_of_mem_edgeSet he
  rw [endsOf, dite_eq_left h]
  exact h.choose_spec.choose_spec

/-- **The endpoint choice of a link** (`fmlnote:graph-operations`): if `G.IsLink e x y`, then
`G.endsOf e` is `(x, y)` or `(y, x)`. The ends of an edge are determined up to order
(`IsLink.eq_and_eq_or_eq_and_eq`), and `G.endsOf e` is a pair of ends of `e` (`isLink_endsOf`). -/
lemma endsOf_eq_or_swap [Inhabited α] (G : Graph α β) {e : β} {x y : α} (h : G.IsLink e x y) :
    G.endsOf e = (x, y) ∨ G.endsOf e = (y, x) := by
  have hl := G.isLink_endsOf h.edge_mem
  rcases hl.eq_and_eq_or_eq_and_eq h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (Prod.ext h1 h2)
  · exact Or.inr (Prod.ext h1 h2)

/-- **The endpoint choice of a loopless graph has distinct ends** (`fmlnote:graph-operations`): if
`G` is loopless and `e ∈ E(G)`, then `(G.endsOf e).1 ≠ (G.endsOf e).2`, as the two are the ends
of `e` (`isLink_endsOf`) and a loopless graph's links join distinct vertices (`IsLink.ne`). The
lemma is stated for the edges of `G`: at an `e ∉ E(G)` both ends are `default`. -/
lemma endsOf_fst_ne_snd [Inhabited α] (G : Graph α β) [G.Loopless] {e : β} (he : e ∈ E(G)) :
    (G.endsOf e).1 ≠ (G.endsOf e).2 :=
  (G.isLink_endsOf he).ne

/-! ## A circuit induces a rigid subgraph (`lem:circuit-induces-rigid`; KT Lemma 3.4) -/

/-- **A circuit exceeds the sparsity bound** (a step of `lem:circuit-induces-rigid`; KT p. 658):
for a circuit `X` of `M(G̃)`, `D·|V(X)| < |X| + D`, that is, `|X| > D(|V(X)| − 1)`. If `X`
satisfied the bound `|X| + D ≤ D·|V(X)|`, it would be independent: a nonempty `E'' ⊊ X` misses
some `e ∈ X` and lies in the independent, hence sparse, set `X \ {e}`
(`IsCircuit.sdiff_singleton_indep`), so every nonempty subset of `X` satisfies the bound. -/
theorem circuit_ncard_gt [DecidableEq β] [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    {X : Set (β × Fin (bodyHingeMult n))} (hX : (G.matroidMG n).IsCircuit X) :
    bodyBarDim n * (G.fiberSpan n X).ncard < X.ncard + bodyBarDim n := by
  by_contra hle
  push Not at hle
  -- It suffices to show `X` is `(D,D)`-sparse-as-restriction; then `X` is independent,
  -- contradicting that it is a circuit.
  apply hX.not_indep
  rw [matroidMG_indep_iff]
  have hXg : X ⊆ E(G.mulTilde n) := hX.subset_ground
  refine ⟨hXg, fun E'' hE'' hE''ne ↦ ?_⟩
  rw [edgeSet_restrict, inter_eq_right.mpr hXg] at hE''
  rw [spanningVerts_restrict_of_subset hE'']
  rcases eq_or_ne E'' X with rfl | hne
  · -- The full set `X`: use the assumed bound and `spanningVerts X = fiberSpan n X`.
    exact hle.trans_eq (by rw [fiberSpan])
  · -- A proper subset `E'' ⊊ X`: contained in `X \ {e}` for some `e ∈ X \ E''`, which is
    -- independent, hence `(D,D)`-sparse, so `E''` satisfies the bound.
    obtain ⟨e, heX, heE''⟩ : ∃ e ∈ X, e ∉ E'' := by
      by_contra h
      push Not at h
      exact hne (subset_antisymm hE'' h)
    have hsub : E'' ⊆ X \ {e} := fun p hp ↦ ⟨hE'' hp, fun hpe ↦ heE'' (hpe ▸ hp)⟩
    have hsparse := ((matroidMG_indep_iff G n).mp (hX.sdiff_singleton_indep heX)).2
    have hE''edge : E'' ⊆ E(G.mulTilde n ↾ (X \ {e})) := by
      rw [edgeSet_restrict, inter_eq_right.mpr (sdiff_subset.trans hXg)]
      exact hsub
    have hsp := hsparse E'' hE''edge hE''ne
    rwa [spanningVerts_restrict_of_subset hsub] at hsp

/-- **The count of KT Lemma 3.4** (`lem:circuit-induces-rigid`; KT p. 658): for a circuit `X` of
`M(G̃)` and `e ∈ X`, `|X − e| + D = D·|V(X)|`, that is, `|X − e| = D(|V(X)| − 1)`. By KT, `X − e`
is then the union of `D` edge-disjoint spanning trees on `V(X)`, which is not formalized;
`circuit_induces_isRigidSubgraph` gives the rigidity of `G[V(X)]`.

The upper bound: `G̃ ↾ (X − e)` is `(D,D)`-sparse (`isSparse_diff_singleton_of_isCircuit`). If
`X − e` is not empty, sparsity applied to `X − e` itself gives
`|X − e| + D ≤ D·|V(X − e)| ≤ D·|V(X)|`; if it is empty, `V(X)` is not, so `D ≤ D·|V(X)|`. The
lower bound is `circuit_ncard_gt` with `|X| = |X − e| + 1`. -/
theorem circuit_induces_isTight [DecidableEq β] [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    {X : Set (β × Fin (bodyHingeMult n))} (hX : (G.matroidMG n).IsCircuit X)
    {e : β × Fin (bodyHingeMult n)} (he : e ∈ X) :
    (X \ {e}).ncard + bodyBarDim n = bodyBarDim n * (G.fiberSpan n X).ncard := by
  -- `|X| = |X − e| + 1`.
  have hfinX : X.Finite := X.toFinite
  have hcardX : X.ncard = (X \ {e}).ncard + 1 := by
    rw [Set.ncard_sdiff_singleton_add_one he hfinX]
  -- Lower bound: `circuit_ncard_gt` (`|X| > D(|V(X)| − 1)`).
  have hlower := circuit_ncard_gt hX
  rw [hcardX] at hlower
  -- Upper bound: `X − e` independent ⟹ `(G̃ ↾ (X − e))` is `(D,D)`-sparse; apply to `X − e`.
  have hsparse := (isSparse_diff_singleton_of_isCircuit hX he).1
  have hXe_sub : X \ {e} ⊆ E(G.mulTilde n) := sdiff_subset.trans hX.subset_ground
  have hupper : (X \ {e}).ncard + bodyBarDim n ≤ bodyBarDim n * (G.fiberSpan n X).ncard := by
    have hmono : (G.mulTilde n).spanningVerts (X \ {e}) ⊆ G.fiberSpan n X :=
      fun x ⟨p, hp, hinc⟩ ↦ ⟨p, sdiff_subset hp, hinc⟩
    have hcardle : ((G.mulTilde n).spanningVerts (X \ {e})).ncard ≤ (G.fiberSpan n X).ncard :=
      Set.ncard_le_ncard hmono (Set.toFinite _)
    rcases (X \ {e}).eq_empty_or_nonempty with hem | hne
    · -- `X − e = ∅`: forces `|V(X)| ≥ 1` (`X = {e}` is a nonempty fiber set), so `D ≤ D·|V(X)|`.
      have hVne : (G.fiberSpan n X).Nonempty := by
        obtain ⟨p, hp⟩ := hX.nonempty
        obtain ⟨x, _, hinc⟩ := exists_isLink_of_mem_edgeSet (hX.subset_ground hp)
        exact ⟨x, p, hp, hinc.inc_left⟩
      have : 1 ≤ (G.fiberSpan n X).ncard := hVne.ncard_pos
      rw [hem, Set.ncard_empty, Nat.zero_add]
      calc bodyBarDim n = bodyBarDim n * 1 := (Nat.mul_one _).symm
        _ ≤ bodyBarDim n * (G.fiberSpan n X).ncard := by gcongr
    · have hsp := hsparse (X \ {e}) (by rw [edgeSet_restrict, inter_eq_right.mpr hXe_sub]) hne
      rw [spanningVerts_restrict_of_subset (subset_refl _)] at hsp
      calc (X \ {e}).ncard + bodyBarDim n
          ≤ bodyBarDim n * ((G.mulTilde n).spanningVerts (X \ {e})).ncard := hsp
        _ ≤ bodyBarDim n * (G.fiberSpan n X).ncard := by gcongr
  omega

/-- **The edges of `X` are edges of `H̃`** (a step of `lem:circuit-induces-rigid`): for a set `X`
of edges of `G̃` and `H = G[V(X)]`, `X ⊆ E(H̃)`, as the ends of each `p ∈ X`, which are those of
the edge `p.1` of `G`, lie in `V(X)`. -/
theorem subset_edgeSet_mulTilde_inducedSpan {G : Graph α β} {n : ℕ}
    {X : Set (β × Fin (bodyHingeMult n))} (hX : X ⊆ E(G.mulTilde n)) :
    X ⊆ E((G.inducedSpan n X).mulTilde n) := by
  intro p hp
  -- `p.1` is an edge of `G̃`, joining some `x, y`; both lie in `V(X) = fiberSpan X`.
  obtain ⟨x, y, hlink⟩ := exists_isLink_of_mem_edgeSet (hX hp)
  have hl1 : G.IsLink p.1 x y := hlink
  have hxV : x ∈ G.fiberSpan n X := ⟨p, hp, hlink.inc_left⟩
  have hyV : y ∈ G.fiberSpan n X := ⟨p, hp, hlink.inc_right⟩
  simp only [mem_edgeSet_mulTilde, inducedSpan, edgeSet_induce]
  exact ⟨x, y, hl1, hxV, hyV⟩

/-- **A circuit induces a rigid subgraph** (`lem:circuit-induces-rigid`; KT Lemma 3.4, p. 658):
for `D ≥ 1` and a circuit `X` of `M(G̃)`, `H = G[V(X)]` is a rigid subgraph of `G`, that is,
`H ≤ G` and `def(H̃) = 0`. Katoh and Tanigawa use it in this form in the proofs of their
Lemmas 4.5 and 4.8.

Let `e ∈ X`. The rank of `M(H̃)` is at most `D(|V(H)| − 1)`
(`rank_matroidMG_le`). The set `X − e` lies in `E(H̃)` (`subset_edgeSet_mulTilde_inducedSpan`)
and is independent in `M(G̃)`, hence in its restriction `M(H̃)` (`matroidMG_restrict_mulTilde`),
and it has `D(|V(X)| − 1)` elements (`circuit_induces_isTight`). So
`rank M(H̃) = D(|V(H)| − 1)`, and KT eq. (2.4) (`rank_add_deficiency_eq`) gives
`def(H̃) = 0`. -/
theorem circuit_induces_isRigidSubgraph [DecidableEq β] [Finite α] [Finite β] {G : Graph α β}
    {n : ℕ} (hD : 1 ≤ bodyBarDim n) {X : Set (β × Fin (bodyHingeMult n))}
    (hX : (G.matroidMG n).IsCircuit X) :
    (G.inducedSpan n X).IsRigidSubgraph G n := by
  classical
  set H := G.inducedSpan n X with hH
  -- `V(H) = fiberSpan X`, nonempty (a circuit is nonempty, spanning a vertex).
  have hXground : X ⊆ E(G.mulTilde n) := hX.subset_ground
  have hVeq : V(H) = G.fiberSpan n X := vertexSet_inducedSpan G n X
  have hVne : V(H).Nonempty := by
    rw [hVeq]
    obtain ⟨p, hp⟩ := hX.nonempty
    obtain ⟨x, _, hinc⟩ := exists_isLink_of_mem_edgeSet (hXground hp)
    exact ⟨x, p, hp, hinc.inc_left⟩
  -- `H ≤ G` via `induce_le` (the span sits inside `V(G)`).
  have hVsub : G.fiberSpan n X ⊆ V(G) := by
    rw [fiberSpan]
    exact (G.mulTilde n).spanningVerts_subset_vertexSet X
  have hle : H ≤ G := by
    rw [hH, inducedSpan]; exact G.induce_le hVsub
  refine ⟨hle, ?_⟩
  -- The deficiency is `0`: pin `rank M(H̃) = D(|V(X)| − 1)` from both sides.
  obtain ⟨e, heX⟩ := hX.nonempty
  -- Upper bound: `rank M(H̃) ≤ D(|V(H)| − 1) = D(|V(X)| − 1)`.
  have hupper : (H.matroidMG n).rank ≤ bodyBarDim n * (V(H).ncard - 1) :=
    H.rank_matroidMG_le n hVne
  -- Lower bound: `X − e` is independent in `M(H̃)` of size `D(|V(X)| − 1)`.
  have hXe_sub : X \ {e} ⊆ E(H.mulTilde n) :=
    sdiff_subset.trans (subset_edgeSet_mulTilde_inducedSpan hXground)
  have hXe_indepG : (G.matroidMG n).Indep (X \ {e}) := hX.sdiff_singleton_indep heX
  have hXe_indepH : (H.matroidMG n).Indep (X \ {e}) := by
    rw [← matroidMG_restrict_mulTilde hle n, Matroid.restrict_indep_iff]
    exact ⟨hXe_indepG, hXe_sub⟩
  -- Extend `X − e` to a base `B` of `M(H̃)`; `|X − e| = D(|V(X)| − 1) ≤ |B| = rank`.
  obtain ⟨B, hB, hBsup⟩ := hXe_indepH.exists_isBase_superset
  have htight : (X \ {e}).ncard + bodyBarDim n = bodyBarDim n * (G.fiberSpan n X).ncard :=
    circuit_induces_isTight hX heX
  have hcardle : (X \ {e}).ncard ≤ B.ncard := Set.ncard_le_ncard hBsup (hB.finite)
  rw [hB.ncard] at hcardle
  -- `def(H̃) = D(|V(X)| − 1) − rank M(H̃)`; both bounds pin `rank = D(|V(X)| − 1)`, so `def = 0`.
  have hbridge := H.rank_add_deficiency_eq n hD hVne
  have hVHcard : V(H).ncard = (G.fiberSpan n X).ncard := by rw [hVeq]
  have hnonneg := H.deficiency_nonneg n hVne
  rw [IsKDof]
  -- ℤ arithmetic: `rank ≤ D(|V(X)|−1)`, `D(|V(X)|−1) = |X−e| + D ... ` — close by `omega`/`zify`.
  have hVpos : 1 ≤ V(H).ncard := hVne.ncard_pos
  have hFpos : 1 ≤ (G.fiberSpan n X).ncard := hVHcard ▸ hVpos
  rw [hVHcard] at hbridge hupper
  zify [hFpos] at hcardle htight hupper
  -- `D·(F−1) = D·F − D`, linking `hupper`/`hbridge` (the `D·(F−1)` atom) to `htight` (`D·F`).
  have hmul : (bodyBarDim n : ℤ) * (((G.fiberSpan n X).ncard : ℤ) - 1)
      = (bodyBarDim n : ℤ) * ((G.fiberSpan n X).ncard : ℤ) - (bodyBarDim n : ℤ) := by ring
  linarith

/-- **With no proper rigid subgraph, a fundamental circuit spans `V(G)`** (a step of
`lem:no-rigid-edge-count`; from the proof of KT Lemma 4.5(i), p. 663): let `G` be loopless with
no proper rigid subgraph, `B` a base of `M(G̃)` and `p ∈ E(G̃) ∖ B`. Then the fundamental circuit
`X` of `p` with respect to `B` has `V(X) = V(G)`. Indeed `G[V(X)]` is a rigid subgraph
(`circuit_induces_isRigidSubgraph`), and it has at least two vertices, as an edge of the loopless
`G` has two distinct ends; so it is not proper. Its caller, `no_rigid_edge_count`, has
`G` loopless as a minimal `k`-dof-graph (`loopless_of_isMinimalKDof`). -/
theorem fundCircuit_inducedSpan_vertexSet_eq [DecidableEq β] [Finite α] [Finite β]
    {G : Graph α β} [G.Loopless] {n : ℕ} (hD : 1 ≤ bodyBarDim n)
    (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n)
    {B : Set (β × Fin (bodyHingeMult n))} (hB : (G.matroidMG n).IsBase B)
    {p : β × Fin (bodyHingeMult n)} (hpE : p ∈ E(G.mulTilde n)) (hpB : p ∉ B) :
    V(G.inducedSpan n ((G.matroidMG n).fundCircuit p B)) = V(G) := by
  classical
  set X := (G.matroidMG n).fundCircuit p B with hXdef
  -- `p ∈ M.E = E(G̃)`, so the fundamental circuit `X` is a circuit of `M(G̃)`.
  have hpground : p ∈ (G.matroidMG n).E := by rw [matroidMG, Matroid.restrict_ground_eq]; exact hpE
  have hXcirc : (G.matroidMG n).IsCircuit X := hB.fundCircuit_isCircuit hpground hpB
  -- The induced subgraph `G[V(X)]` is rigid, in particular `H ≤ G` and `0`-dof.
  have hrigid : (G.inducedSpan n X).IsRigidSubgraph G n :=
    circuit_induces_isRigidSubgraph hD hXcirc
  -- `V(X) ⊆ V(G)` (the span sits inside `V(G)`).
  have hsub : V(G.inducedSpan n X) ⊆ V(G) := by
    rw [vertexSet_inducedSpan, fiberSpan]
    exact (G.mulTilde n).spanningVerts_subset_vertexSet X
  -- `V(X)` spans two distinct vertices: a circuit is nonempty, and a fiber of the loopless
  -- `G` has two distinct ends.
  have hV2 : 2 ≤ V(G.inducedSpan n X).ncard := by
    rw [vertexSet_inducedSpan, fiberSpan]
    obtain ⟨q, hq⟩ := hXcirc.nonempty
    obtain ⟨x, y, hinc⟩ := exists_isLink_of_mem_edgeSet (hXcirc.subset_ground hq)
    have hxy : x ≠ y := ((mulTilde_isLink G n).mp hinc).ne
    exact (Set.one_lt_ncard (Set.toFinite _)).mpr
      ⟨x, ⟨q, hq, hinc.inc_left⟩, y, ⟨q, hq, hinc.inc_right⟩, hxy⟩
  -- If `V(X) ⊊ V(G)`, `G[V(X)]` is a *proper* rigid subgraph — excluded by hypothesis.
  refine subset_antisymm hsub ?_
  by_contra hnotle
  exact hnp (G.inducedSpan n X)
    ⟨hrigid, hV2, hsub.ssubset_of_ne (fun heq ↦ hnotle heq.ge)⟩

/-! ## A proper rigid subgraph when every degree is at least three (`lem:pencil-min-degree-rigid`)

The lemma is here, not beside `IsProperRigidSubgraph` in `Molecular/Deficiency.lean`, because its
proof uses `circuit_induces_isRigidSubgraph`. -/

/-- **A proper rigid subgraph when every degree is at least three**
(`lem:pencil-min-degree-rigid`): for `D ≥ 4`, a loopless multigraph `G` with at least three
vertices, each of degree at least three, has a proper rigid subgraph. No minimality is assumed:
`pencil_reduction` (`thm:pencil-reduction`) applies it to find a vertex of degree two.

Let `v` be a vertex of least degree `δ ≥ 3`. As `δ·|V(G)| ≤ 2|E(G)|`, the edges of `G` not at `v`
number `|E(G)| − δ ≥ δ(|V(G)| − 2)/2`, and their `(D − 1)(|E(G)| − δ)` copies in `G̃` are more
than `D(|V(G)| − 2)` when `D ≥ 4`, the bound of `(D, D)`-sparsity on the at most `|V(G)| − 1`
vertices other than `v`. So the copies are dependent in `M(G̃)` (`matroidMG_indep_iff`) and
contain a circuit `X`. Then `G[V(X)]` is a rigid subgraph (`circuit_induces_isRigidSubgraph`)
with at least two vertices, as `G` has no loops, and without `v`, so it is proper. -/
theorem exists_isProperRigidSubgraph_of_three_le_degree
    [Finite α] [Finite β] {n : ℕ} {G : Graph α β}
    (hD : 4 ≤ bodyBarDim n) (hV3 : 3 ≤ V(G).ncard) (hloop : G.Loopless)
    (hdeg : ∀ v ∈ V(G), 3 ≤ G.degree v) :
    ∃ H : Graph α β, H.IsProperRigidSubgraph G n := by
  classical
  have hGfin : G.Finite := { edgeSet_finite := Set.toFinite _, vertexSet_finite := Set.toFinite _ }
  -- A minimum-degree vertex `v`, degree `δ ≥ 3`.
  have hVne : V(G).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨v, hvV, hvmin⟩ := exists_min_image V(G) G.degree (Set.toFinite V(G)) hVne
  set δ := G.degree v with hδdef
  have hδ3 : 3 ≤ δ := hdeg v hvV
  -- The global handshake bound `δ|V| ≤ 2|E|` from `v`'s minimality.
  have hMinDeg : G.MinDegreeGE δ := minDegreeGE_iff.mpr hvmin
  have hHandshake : δ * V(G).ncard ≤ 2 * E(G).ncard := hMinDeg.le_ncard_edgeSet
  -- `Ev`: the edges of `G` avoiding `v`.
  set Ev : Set β := E(G) \ E(G, v) with hEvdef
  have hEvsub : Ev ⊆ E(G) := sdiff_subset
  have hδcard : E(G, v).ncard = δ := degree_eq_ncard_inc.symm
  have hEvcard : Ev.ncard + δ = E(G).ncard := by
    rw [hEvdef, ← hδcard]; exact ncard_sdiff_add_ncard_of_subset (incEdges_subset G v)
  -- `E'`: the `(D − 1)`-fold fiber of `Ev` in the multiplied graph.
  set E' : Set (β × Fin (bodyHingeMult n)) := {p | p.1 ∈ Ev} with hE'def
  have hE'prod : E' = Ev ×ˢ (Set.univ : Set (Fin (bodyHingeMult n))) := by
    ext ⟨e, i⟩; simp [hE'def]
  have hE'card : E'.ncard = Ev.ncard * bodyHingeMult n := by
    rw [hE'prod, Set.ncard_prod, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hE'sub : E' ⊆ E(G.mulTilde n) := fun p hp ↦ (mem_edgeSet_mulTilde G n).mpr (hEvsub hp)
  -- The numeric core: `(D − 1)|Ev| > D(|V| − 2)`, `D = bodyBarDim n ≥ 4`.
  have hHM : (bodyHingeMult n : ℤ) = (bodyBarDim n : ℤ) - 1 := by rw [bodyHingeMult]; omega
  have hD4' : (4 : ℤ) ≤ (bodyBarDim n : ℤ) := by exact_mod_cast hD
  have hδ3' : (3 : ℤ) ≤ (δ : ℤ) := by exact_mod_cast hδ3
  have hV3' : (3 : ℤ) ≤ (V(G).ncard : ℤ) := by exact_mod_cast hV3
  have hHS' : (δ : ℤ) * (V(G).ncard : ℤ) ≤ 2 * (E(G).ncard : ℤ) := by exact_mod_cast hHandshake
  have hEvE' : (Ev.ncard : ℤ) + (δ : ℤ) = (E(G).ncard : ℤ) := by exact_mod_cast hEvcard
  have hVm2nonneg : (0 : ℤ) ≤ (V(G).ncard : ℤ) - 2 := by linarith
  -- `δ(|V| − 2) ≤ 2|Ev|` (handshake); `3(|V| − 2) ≤ δ(|V| − 2)` (`δ ≥ 3`); combine, scale by
  -- `D − 1 ≥ 0`, and use `(D − 3)(|V| − 2) > 0` (`D ≥ 4`, `|V| ≥ 3`) to clear the `3` vs `D`.
  have step1 : (δ : ℤ) * ((V(G).ncard : ℤ) - 2) ≤ 2 * (Ev.ncard : ℤ) := by
    nlinarith [hHS', hEvE']
  have step2 : (3 : ℤ) * ((V(G).ncard : ℤ) - 2) ≤ (δ : ℤ) * ((V(G).ncard : ℤ) - 2) :=
    mul_le_mul_of_nonneg_right hδ3' hVm2nonneg
  have step3 : (3 : ℤ) * ((V(G).ncard : ℤ) - 2) ≤ 2 * (Ev.ncard : ℤ) := step2.trans step1
  have hDm1nonneg : (0 : ℤ) ≤ (bodyBarDim n : ℤ) - 1 := by linarith
  have step4 : ((bodyBarDim n : ℤ) - 1) * (3 * ((V(G).ncard : ℤ) - 2)) ≤
      ((bodyBarDim n : ℤ) - 1) * (2 * (Ev.ncard : ℤ)) :=
    mul_le_mul_of_nonneg_left step3 hDm1nonneg
  have hD3pos : (0 : ℤ) < (bodyBarDim n : ℤ) - 3 := by linarith
  have hVm2pos : (0 : ℤ) < (V(G).ncard : ℤ) - 2 := by linarith
  have hcross : (0 : ℤ) < ((bodyBarDim n : ℤ) - 3) * ((V(G).ncard : ℤ) - 2) :=
    mul_pos hD3pos hVm2pos
  have hnumeric : (bodyBarDim n : ℤ) * ((V(G).ncard : ℤ) - 2) <
      (Ev.ncard : ℤ) * (bodyHingeMult n : ℤ) := by
    rw [hHM]; nlinarith [step4, hcross]
  have hprodpos : (0 : ℤ) < (Ev.ncard : ℤ) * (bodyHingeMult n : ℤ) := by nlinarith
  have hEvpos : 0 < Ev.ncard := by
    rcases Nat.eq_zero_or_pos Ev.ncard with h0 | hpos
    · rw [h0] at hprodpos; simp at hprodpos
    · exact hpos
  have hEvne : Ev.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  have hE'ne : E'.Nonempty := by
    obtain ⟨e, he⟩ := hEvne
    have hHM0 : 0 < bodyHingeMult n := by rw [bodyHingeMult]; omega
    exact ⟨(e, ⟨0, hHM0⟩), he⟩
  -- `E'`'s spanned vertices avoid `v`.
  have hspan_sub : (G.mulTilde n).spanningVerts E' ⊆ V(G) \ {v} := by
    rintro x ⟨p, hpE', y, hlink⟩
    have hxyG : G.IsLink p.1 x y := (mulTilde_isLink G n).mp hlink
    have hpEv : p.1 ∈ Ev := hpE'
    refine ⟨hxyG.left_mem, ?_⟩
    rw [Set.mem_singleton_iff]
    rintro rfl
    exact hpEv.2 hxyG.inc_left
  -- `E'` is dependent in `M(G̃)`: it exceeds the sparsity cap on `V(G) ∖ {v}`.
  have hnotindep : ¬ (G.matroidMG n).Indep E' := by
    intro hindep
    rw [matroidMG_indep_iff] at hindep
    obtain ⟨_, hsparse⟩ := hindep
    have hsp := hsparse E' (by rw [edgeSet_restrict, Set.inter_eq_right.mpr hE'sub]) hE'ne
    rw [spanningVerts_restrict_of_subset (subset_refl E')] at hsp
    have hspancard : ((G.mulTilde n).spanningVerts E').ncard ≤ V(G).ncard - 1 :=
      (Set.ncard_le_ncard hspan_sub (Set.toFinite _)).trans_eq
        (Set.ncard_sdiff_singleton_of_mem hvV)
    have hsp' : (E'.ncard : ℤ) + (bodyBarDim n : ℤ) ≤
        (bodyBarDim n : ℤ) * (((G.mulTilde n).spanningVerts E').ncard : ℤ) := by exact_mod_cast hsp
    have hVpos : 1 ≤ V(G).ncard := hVne.ncard_pos
    have hspancard' : (((G.mulTilde n).spanningVerts E').ncard : ℤ) ≤ (V(G).ncard : ℤ) - 1 := by
      zify [hVpos] at hspancard; exact hspancard
    have hE'card' : (E'.ncard : ℤ) = (Ev.ncard : ℤ) * (bodyHingeMult n : ℤ) := by
      exact_mod_cast hE'card
    have hstep : (bodyBarDim n : ℤ) * (((G.mulTilde n).spanningVerts E').ncard : ℤ) ≤
        (bodyBarDim n : ℤ) * ((V(G).ncard : ℤ) - 1) :=
      mul_le_mul_of_nonneg_left hspancard' (by linarith)
    linarith [hsp', hstep, hE'card', hnumeric]
  have hE'dep : (G.matroidMG n).Dep E' :=
    ⟨hnotindep, by rw [matroidMG, Matroid.restrict_ground_eq]; exact hE'sub⟩
  -- Extract a circuit, build its induced rigid span.
  obtain ⟨C, hCsub, hCcirc⟩ := hE'dep.exists_isCircuit_subset
  set H := G.inducedSpan n C with hHdef
  have hD1 : 1 ≤ bodyBarDim n := by omega
  have hHrigid : H.IsRigidSubgraph G n := circuit_induces_isRigidSubgraph hD1 hCcirc
  -- `H` spans `≥ 2` vertices.
  have hVH2 : 2 ≤ V(H).ncard := by
    rw [hHdef, vertexSet_inducedSpan, fiberSpan]
    obtain ⟨q, hq⟩ := hCcirc.nonempty
    obtain ⟨x, y, hinc⟩ := exists_isLink_of_mem_edgeSet ((hCsub.trans hE'sub) hq)
    have hxy : x ≠ y := ((mulTilde_isLink G n).mp hinc).ne
    exact (Set.one_lt_ncard (Set.toFinite _)).mpr
      ⟨x, ⟨q, hq, hinc.inc_left⟩, y, ⟨q, hq, hinc.inc_right⟩, hxy⟩
  -- `H` avoids `v`, hence is proper.
  have hspanC_sub : (G.mulTilde n).spanningVerts C ⊆ (G.mulTilde n).spanningVerts E' :=
    fun x ⟨p, hp, hinc⟩ ↦ ⟨p, hCsub hp, hinc⟩
  have hVHsub : V(H) ⊆ V(G) \ {v} := by
    rw [hHdef, vertexSet_inducedSpan, fiberSpan]
    exact hspanC_sub.trans hspan_sub
  have hvnotH : v ∉ V(H) := fun hvH ↦ (hVHsub hvH).2 rfl
  have hVHssub : V(H) ⊂ V(G) :=
    (ssubset_iff_of_subset (hVHsub.trans sdiff_subset)).mpr ⟨v, hvV, hvnotH⟩
  exact ⟨H, hHrigid, hVH2, hVHssub⟩

/-! ## The independent sets of `M(G̃)` as unions of forests (`lem:forest-packing-decomp`)

Katoh and Tanigawa begin their proofs of Lemmas 4.1 and 4.2 (p. 660) with a partition of an
independent set of `M(G̃)` into `D` edge-disjoint forests. A forest of `G̃` is here a set
independent in its cycle matroid `(G̃).cycleMatroid`, whose independent sets are the acyclic
ones. -/

/-- **The independent sets of `M(G̃)` are the unions of `D` forests** (`lem:forest-packing-decomp`):
a set `I` of edges of `G̃` is independent in `M(G̃)` if and only if `I ⊆ E(G̃)` and `I` is the
union of `D` sets independent in the cycle matroid of `G̃`. As `M(G̃)` is the restriction to
`E(G̃)` of the union of `D` copies of that cycle matroid (`def:matroid-MG`), this unfolds
`Matroid.restrict_indep_iff` and `Matroid.union_indep_iff` (`lem:union-indep-iff`). -/
theorem matroidMG_indep_iff_exists_forest_packing [DecidableEq β] [Finite β]
    (G : Graph α β) (n : ℕ) {I : Set (β × Fin (bodyHingeMult n))} :
    (G.matroidMG n).Indep I ↔ I ⊆ E(G.mulTilde n) ∧
      ∃ Fs : Fin (bodyBarDim n) → Set (β × Fin (bodyHingeMult n)),
        ⋃ i, Fs i = I ∧ ∀ i, ((G.mulTilde n).cycleMatroid).Indep (Fs i) := by
  rw [matroidMG, Matroid.restrict_indep_iff, Matroid.union_indep_iff]
  tauto

/-! ### KT Lemma 4.1 holds only for bases (`rem:kt-lemma-41`)

KT Lemma 4.1 (p. 660; Lemma 5.1, p. 11, of the arXiv version, 2009) states that for any
independent set `I` of `M(G̃)` there is an independent set `I'` of `M(G̃_v^{ab})` with
`|I'| = |I| − D` and fewer than `D − 1` copies of `ab`. No `I'` has `|I'| = |I| − D` when
`|I| < D`, for instance at `I = ∅` (`ex:kt-41-overquantified`). Katoh and Tanigawa apply the
lemma to a base, in the proof of their Lemma 4.3, and the blueprint reads it for bases.
`rem:kt-lemma-41` also shows that a base has the partition into forests that the proof assumes
(`lem:balanced-forest-packing`), and that the induction needs the lemma only through the
deficiency bound of KT Lemma 4.3(i), which `lem:dof-tracking` proves by comparing partitions of
`V(G)`. -/

/-- **KT Lemma 4.1 fails at `I = ∅`** (`ex:kt-41-overquantified`; KT p. 660): for `D ≥ 1`, no set
`I'` has `|I'| + D = |∅| = 0`. The empty set is independent in `M(G̃)`, so no independent `I'` of
`M(G̃_v^{ab})` has `|I'| = |∅| − D`, as KT Lemma 4.1, stated for every independent set, would
give (`rem:kt-lemma-41`). -/
theorem kt_lemma_41_overquantified (n : ℕ) (hD : 1 ≤ bodyBarDim n) :
    ¬ ∃ I' : Set (β × Fin (bodyHingeMult n)),
        I'.ncard + bodyBarDim n = (∅ : Set (β × Fin (bodyHingeMult n))).ncard := by
  rintro ⟨I', hI'⟩
  rw [Set.ncard_empty] at hI'
  omega

/-! ## The rank of a rigid subgraph and the contraction of `M(G̃)` (KT Lemma 3.5)

The deficiency half of KT Lemma 3.5 (pp. 658–659), for the contraction of the matroid `M(G̃)`
by the edges of `H̃` (`sec:molecular-induction-inherited`). A rigid subgraph `H` has
`rank M(H̃) = D(|V(H)| − 1)` (`lem:rigid-full-rank`); contracting `E(H̃)` lowers the rank of
`M(G̃)` by `rank M(H̃)` (`lem:contract-rank-bridge`); so the contraction keeps the deficiency
(`lem:contract-deficiency-conservation`). The minimality half is
`contract_minimality_transport` (`Contraction.lean`). -/

/-- **The rank of a rigid subgraph** (`lem:rigid-full-rank`; the first step of KT Lemma 3.5,
p. 658): for `D ≥ 1` and a `0`-dof-graph `H` with a vertex, `rank M(H̃) = D(|V(H)| − 1)`, by KT
eq. (2.4) (`rank_add_deficiency_eq`) with `def(H̃) = 0`. -/
theorem rank_matroidMG_of_isKDof_zero [DecidableEq β] [Finite α] [Finite β] {H : Graph α β}
    {n : ℕ} (hD : 1 ≤ bodyBarDim n) (hne : V(H).Nonempty) (hrigid : H.IsKDof n 0) :
    ((H.matroidMG n).rank : ℤ) = bodyBarDim n * ((V(H).ncard : ℤ) - 1) := by
  have hbridge := H.rank_add_deficiency_eq n hD hne
  rw [hrigid.deficiency_eq] at hbridge
  simpa using hbridge

/-- **The rank of a contraction** (a step of `lem:contract-rank-bridge`): in a matroid `M` of
finite rank, `rank(M ／ C) + rank(M ↾ C) = rank M`. This is `r(M/C) = r(M) − r_M(C)`, which
follows from Proposition 3.1.6 of Oxley (2011), and which is `Matroid.contract_rank_cast_int_eq`
of the `Matroid` package, as the restriction has rank `r_M(C)` (`Matroid.restrict_rk_eq`). -/
theorem _root_.Matroid.rank_contract_add_rank_restrict {γ : Type*} (M : Matroid γ)
    [M.RankFinite] (C : Set γ) :
    (M ／ C).rank + (M ↾ C).rank = M.rank := by
  have hrestrict : (M ↾ C).rank = M.rk C := by
    rw [Matroid.rank_def, Matroid.restrict_ground_eq, Matroid.restrict_rk_eq M subset_rfl]
  have hcontract : ((M ／ C).rank : ℤ) = (M.rank : ℤ) - (M.rk C : ℤ) := M.contract_rank_cast_int_eq C
  omega

/-- **The rank of `M(G̃) ／ E(H̃)`** (`lem:contract-rank-bridge`): for a subgraph `H ≤ G`,
`rank(M(G̃) ／ E(H̃)) + rank M(H̃) = rank M(G̃)`. It is `Matroid.rank_contract_add_rank_restrict`,
as the restriction `M(G̃) ↾ E(H̃)` is `M(H̃)` (`matroidMG_restrict_mulTilde`,
`lem:matroid-restrict-subgraph`). -/
theorem contract_matroidMG_rank [DecidableEq β] [Finite α] [Finite β] {H G : Graph α β}
    (h : H ≤ G) (n : ℕ) :
    ((G.matroidMG n) ／ E(H.mulTilde n)).rank + (H.matroidMG n).rank = (G.matroidMG n).rank := by
  have hrestrict : (G.matroidMG n) ↾ E(H.mulTilde n) = H.matroidMG n :=
    matroidMG_restrict_mulTilde h n
  rw [← hrestrict]
  exact (G.matroidMG n).rank_contract_add_rank_restrict _

/-- **Contracting a rigid subgraph keeps the deficiency** (`lem:contract-deficiency-conservation`;
KT Lemma 3.5, p. 658): for `D ≥ 1` and a `0`-dof-graph `H ≤ G` with a vertex,
`D(|V(G)| − |V(H)|) − rank(M(G̃) ／ E(H̃)) = def(G̃)`. The contraction of `H` to one of its vertices
has `|V(G)| − |V(H)| + 1` vertices, so `D(|V(G)| − |V(H)|)` is its `D(|V| − 1)`.

By `contract_matroidMG_rank` and `rank_matroidMG_of_isKDof_zero`,
`rank(M(G̃) ／ E(H̃)) = rank M(G̃) − D(|V(H)| − 1)`, and KT eq. (2.4) for `G`
(`rank_add_deficiency_eq`) gives `rank M(G̃) = D(|V(G)| − 1) − def(G̃)`. This is Katoh and
Tanigawa's count. -/
theorem contract_matroidMG_deficiency_eq [DecidableEq β] [Finite α] [Finite β]
    {H G : Graph α β} (h : H ≤ G) (n : ℕ) (hD : 1 ≤ bodyBarDim n) (hVHne : V(H).Nonempty)
    (hVGne : V(G).Nonempty) (hrigid : H.IsKDof n 0) :
    bodyBarDim n * ((V(G).ncard : ℤ) - (V(H).ncard : ℤ))
      - ((G.matroidMG n ／ E(H.mulTilde n)).rank : ℤ) = G.deficiency n := by
  -- The rank a rigid `H` contributes: `rank M(H̃) = D(|V(H)| − 1)`.
  have hrankH := rank_matroidMG_of_isKDof_zero hD hVHne hrigid
  -- Contraction arithmetic: `rank(M(G̃)/E(H̃)) + rank M(H̃) = rank M(G̃)`.
  have hbridge := contract_matroidMG_rank h n
  -- def = corank for `G̃`: `rank M(G̃) + def(G̃) = D(|V(G)| − 1)`.
  have hdefcorank := G.rank_add_deficiency_eq n hD hVGne
  -- Cast the ℕ-valued contraction arithmetic into ℤ; finish by linear bookkeeping.
  zify at hbridge
  linarith [hrankH, hbridge, hdefcorank]

/-! ## Removal and splitting off (`def:graph-operations`)

Two of the operations of `def:graph-operations` (`sec:molecular-induction-operations`): the
removal of a vertex and splitting off at a vertex (KT §4.1, p. 660). Edge-splitting and the
contraction of a subgraph (`def:rigid-contraction`) are in `ReducibleVertex.lean`. -/

/-- **Removal** `G_v = G − v` (`def:graph-operations`): delete `v` and its edges, as mathlib's
`Graph.deleteVerts {v}`. -/
def removeVertex (G : Graph α β) (v : α) : Graph α β :=
  G.deleteVerts {v}

@[simp]
lemma vertexSet_removeVertex (G : Graph α β) (v : α) :
    V(G.removeVertex v) = V(G) \ {v} := by
  rw [removeVertex, vertexSet_deleteVerts]

@[simp]
lemma removeVertex_isLink {G : Graph α β} {v : α} {e : β} {x y : α} :
    (G.removeVertex v).IsLink e x y ↔ G.IsLink e x y ∧ x ≠ v ∧ y ≠ v := by
  rw [removeVertex, deleteVerts_isLink]
  simp [Set.mem_singleton_iff]

/-- **`G − v` is a subgraph of `G`** (`lem:splitoff-edge-substitution`): `G.removeVertex v ≤ G`.
With `removeVertex_le_splitOff`, `G − v` is a common subgraph of `G` and `G_v^{ab}`. -/
lemma removeVertex_le (G : Graph α β) (v : α) : G.removeVertex v ≤ G := by
  rw [removeVertex]; exact G.deleteVerts_le

/-- **An edge of `G` not in `G − v` has `v` as an end** (`lem:splitoff-edge-substitution`): if
`G.IsLink e u w` and `e` does not join `u` and `w` in `G − v`, then `u = v` or `w = v`, as a link
of `G` avoiding `v` is a link of `G − v` (`removeVertex_isLink`). -/
lemma isLink_incident_of_not_removeVertex {G : Graph α β} {v : α} {e : β} {u w : α}
    (h : G.IsLink e u w) (hg : ¬(G.removeVertex v).IsLink e u w) : u = v ∨ w = v := by
  by_contra hc
  rw [not_or] at hc
  exact hg (removeVertex_isLink.mpr ⟨h, hc.1, hc.2⟩)

/-- **A link at `v` is not a link of a graph without `v`** (a step of
`lem:case-III-rank-certification`): if `f` joins `v` to `x` in `G`, `v ∉ V(H)` and every link of
`H` is a link of `G` (`hle`), then no link of `H` is `f`. As a link of `G`, it would have the ends
`v` and `x` (`IsLink.eq_and_eq_or_eq_and_eq`), and a link of `H` has its ends in `V(H)`. Case III
applies it at `H = G − v` to the two edges at `v`. -/
lemma IsLink.ne_of_notMem {G H : Graph α β} {f e : β} {v x u w : α} (hf : G.IsLink f v x)
    (hv : v ∉ V(H)) (hle : ∀ e u w, H.IsLink e u w → G.IsLink e u w) (he : H.IsLink e u w) :
    e ≠ f := by
  rintro rfl
  rcases hf.eq_and_eq_or_eq_and_eq (hle _ _ _ he) with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact hv he.left_mem
  · exact hv he.right_mem

/-- **Splitting off** `G_v^{ab}` (`def:graph-operations`): delete `v` and its edges, and add an
edge with the label `e₀` joining `a` and `b` when `a, b ∈ V(G)` differ from `v`. An edge of `G`
with the label `e₀` is deleted too, so this is `G_v^{ab}` when no edge of `G − v` has the label
`e₀`, as when `e₀ ∉ E(G)` (`fmlnote:graph-operations`). The definition takes any `v`, `a` and
`b`; the blueprint applies it at a vertex `v` of degree two with neighbours `a` and `b`. -/
def splitOff (G : Graph α β) (v a b : α) (e₀ : β) : Graph α β where
  vertexSet := V(G) \ {v}
  IsLink e x y :=
    (e ≠ e₀ ∧ G.IsLink e x y ∧ x ≠ v ∧ y ≠ v) ∨
      (e = e₀ ∧ a ≠ v ∧ b ≠ v ∧ a ∈ V(G) ∧ b ∈ V(G) ∧
        ((x = a ∧ y = b) ∨ (x = b ∧ y = a)))
  isLink_symm := by
    rintro e he
    refine ⟨fun x y h => ?_⟩
    rcases h with ⟨hne, h, hx, hy⟩ | ⟨he₀, ha, hb, haV, hbV, hxy⟩
    · exact Or.inl ⟨hne, h.symm, hy, hx⟩
    · exact Or.inr ⟨he₀, ha, hb, haV, hbV, hxy.symm.imp (fun ⟨p, q⟩ ↦ ⟨q, p⟩)
        (fun ⟨p, q⟩ ↦ ⟨q, p⟩)⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro e x y z w (⟨_, h, _, _⟩ | ⟨_, _, _, _, _, hxy⟩) (⟨_, h', _, _⟩ | ⟨_, _, _, _, _, hzw⟩)
    · exact h.left_eq_or_eq h'
    · exact absurd ‹e = e₀› ‹e ≠ e₀›
    · exact absurd ‹e = e₀› ‹e ≠ e₀›
    · rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hzw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp
  left_mem_of_isLink := by
    rintro e x y (⟨_, h, hx, _⟩ | ⟨_, hav, hbv, haV, hbV, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩)
    · exact ⟨h.left_mem, by simpa using hx⟩
    · exact ⟨haV, by simpa using hav⟩
    · exact ⟨hbV, by simpa using hbv⟩

@[simp]
lemma vertexSet_splitOff (G : Graph α β) (v a b : α) (e₀ : β) :
    V(G.splitOff v a b e₀) = V(G) \ {v} := rfl

/-- **Splitting off lowers the number of vertices** (`lem:reduction-measure`; from the proof of KT
Theorem 4.9, pp. 666–667): for `v ∈ V(G)`, `|V(G_v^{ab})| < |V(G)|`, as
`V(G_v^{ab}) = V(G) ∖ {v}`. Katoh and Tanigawa prove their Theorem 4.9 by induction on the
number of vertices. -/
lemma splitOff_vertexSet_ncard_lt [Finite α] {G : Graph α β} {v a b : α} {e₀ : β}
    (hv : v ∈ V(G)) : V(G.splitOff v a b e₀).ncard < V(G).ncard := by
  rw [vertexSet_splitOff]
  exact Set.ncard_sdiff_singleton_lt_of_mem hv (Set.toFinite _)

@[simp]
lemma splitOff_isLink {G : Graph α β} {v a b : α} {e₀ : β} {e : β} {x y : α} :
    (G.splitOff v a b e₀).IsLink e x y ↔
      (e ≠ e₀ ∧ G.IsLink e x y ∧ x ≠ v ∧ y ≠ v) ∨
        (e = e₀ ∧ a ≠ v ∧ b ≠ v ∧ a ∈ V(G) ∧ b ∈ V(G) ∧
          ((x = a ∧ y = b) ∨ (x = b ∧ y = a))) := Iff.rfl

/-- **The edges of `G_v^{ab}`** (`def:graph-operations`): `e` is an edge of `G_v^{ab}` if and only
if `e = e₀` with `a, b ∈ V(G)` different from `v` (the new edge), or `e ≠ e₀` is an edge of `G`
whose ends differ from `v`. -/
lemma edgeSet_splitOff {G : Graph α β} {v a b : α} {e₀ : β} :
    E(G.splitOff v a b e₀) =
      {e | e = e₀ ∧ a ≠ v ∧ b ≠ v ∧ a ∈ V(G) ∧ b ∈ V(G)} ∪
        {e | e ≠ e₀ ∧ ∃ x y, G.IsLink e x y ∧ x ≠ v ∧ y ≠ v} := by
  ext e
  rw [edgeSet_eq_setOfPred_exists_isLink]
  simp only [splitOff_isLink, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨x, y, (⟨hne, h, hx, hy⟩ | ⟨rfl, ha, hb, haV, hbV, _⟩)⟩
    · exact Or.inr ⟨hne, x, y, h, hx, hy⟩
    · exact Or.inl ⟨rfl, ha, hb, haV, hbV⟩
  · rintro (⟨rfl, ha, hb, haV, hbV⟩ | ⟨hne, x, y, h, hx, hy⟩)
    · exact ⟨a, b, Or.inr ⟨rfl, ha, hb, haV, hbV, Or.inl ⟨rfl, rfl⟩⟩⟩
    · exact ⟨x, y, Or.inl ⟨hne, h, hx, hy⟩⟩

/-- **The copies of the new edge are edges of `G̃_v^{ab}`** (`def:graph-operations`): if
`a, b ∈ V(G)` differ from `v`, the `D − 1` copies `ẽ₀ = edgeFiber e₀ n` of the new edge `ab` lie
in `E(G̃_v^{ab})`. They are the copies of `ab` in KT Lemma 4.1 (p. 660). -/
lemma edgeFiber_subset_edgeSet_mulTilde_splitOff {G : Graph α β} {v a b : α} {e₀ : β}
    (n : ℕ) (ha : a ≠ v) (hb : b ≠ v) (haV : a ∈ V(G)) (hbV : b ∈ V(G)) :
    edgeFiber e₀ n ⊆ E((G.splitOff v a b e₀).mulTilde n) := by
  intro p hp
  rw [mem_edgeSet_mulTilde]
  rw [mem_edgeFiber] at hp
  rw [hp, edgeSet_splitOff]
  exact Or.inl ⟨rfl, ha, hb, haV, hbV⟩

/-- **`G − v` is a subgraph of `G_v^{ab}`** (`lem:splitoff-edge-substitution`): if `e₀ ∉ E(G)`,
then `G.removeVertex v ≤ G.splitOff v a b e₀`. A link of `G − v` is a link of `G` whose ends
differ from `v` (`removeVertex_isLink`), and its edge, an edge of `G`, is not `e₀`. So `G − v` is
a common subgraph of `G` (`removeVertex_le`) and of `G_v^{ab}`, which is not a subgraph of `G`.
Its callers are `exists_isBase_vb_fiber_eq_one_of_removeVertex_isKDof`
(`lem:removal-deficiency-equality`) and `splitOff_removeVertex_minimalKDof`. -/
lemma removeVertex_le_splitOff {G : Graph α β} {v a b : α} {e₀ : β} (he₀ : e₀ ∉ E(G)) :
    G.removeVertex v ≤ G.splitOff v a b e₀ := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [vertexSet_splitOff]
    rw [vertexSet_removeVertex] at hx
    exact hx
  · intro e x y h
    rw [removeVertex_isLink] at h
    rw [splitOff_isLink]
    exact Or.inl ⟨fun hee => he₀ (hee ▸ h.1.edge_mem), h.1, h.2.1, h.2.2⟩

/-- **When `G_v^{ab}` is simple** (a step of `lem:splitoff-simple`): `G_v^{ab}` is simple if none
of its links joins a vertex to itself (`hloop`) and any two of its links between the same two
vertices are the same edge (`hpar`). Splitting off need not keep a graph simple: the new edge is
a loop when `a = b`, and it is parallel to every edge of `G` that joins `a` and `b`. When `G` is
simple and has no proper rigid subgraph, KT Lemma 6.7(ii) (p. 677) excludes both
(`splitOff_simple_of_noRigid`). `map_simple` (`Contraction.lean`) is the same criterion for a
relabelling of the vertices, such as the contraction. -/
lemma splitOff_simple {G : Graph α β} {v a b : α} {e₀ : β}
    (hloop : ∀ e x y, (G.splitOff v a b e₀).IsLink e x y → x ≠ y)
    (hpar : ∀ e₁ e₂ x y, (G.splitOff v a b e₀).IsLink e₁ x y →
      (G.splitOff v a b e₀).IsLink e₂ x y → e₁ = e₂) :
    (G.splitOff v a b e₀).Simple where
  not_isLoopAt e x h := hloop e x x (isLink_self_iff.mp h) rfl
  eq_of_isLink e f x y he hf := hpar e f x y he hf

/-- **`H_v^{ab}` is simple when `a` and `b` are not adjacent**: if `H` is simple, `a ≠ b` and no
edge of `H` joins `a` and `b`, then `H_v^{ab}` is simple (`splitOff_simple`), as no edge of `H` is
parallel to the new edge. `exists_oneEar_base` and `X0Attains.of_splitOff`
(`Molecule/Pencil/MainComponent/`) use it. -/
lemma splitOff_simple_of_not_adj {H : Graph α β} (hS : H.Simple) {v a b : α}
    {e₀ : β} (hab : a ≠ b) (hnadj : ¬ H.Adj a b) : (H.splitOff v a b e₀).Simple := by
  refine splitOff_simple (fun f u w h => ?_) (fun f₁ f₂ u w h₁ h₂ => ?_)
  · rcases h with ⟨-, h, -, -⟩ | ⟨-, -, -, -, -, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact h.ne
    · exact hab
    · exact hab.symm
  · rcases h₁ with ⟨-, h₁, -, -⟩ | ⟨rfl, -, -, -, -, h₁⟩ <;>
      rcases h₂ with ⟨-, h₂, -, -⟩ | ⟨rfl, -, -, -, -, h₂⟩
    · exact hS.eq_of_isLink h₁ h₂
    · rcases h₂ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      exacts [absurd ⟨f₁, h₁⟩ hnadj, absurd ⟨f₁, h₁.symm⟩ hnadj]
    · rcases h₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      exacts [absurd ⟨f₂, h₂⟩ hnadj, absurd ⟨f₂, h₂.symm⟩ hnadj]
    · rfl

/-- **`G_v^{ab}` is simple, given the triangle** (a step of `lem:splitoff-simple`; KT Lemma 6.7(ii),
p. 677): let `G` be simple with no proper rigid subgraph, and let edges `eₐ ≠ e_b` join `v` to `a`
and to `b`. If an edge of `G` joining `a` and `b` would give a proper rigid subgraph (`htri`), then
`G_v^{ab}` is simple (`splitOff_simple`). The new edge is not a loop, as `a = b` would make `eₐ` and
`e_b` parallel; the other edges of `G_v^{ab}` are edges of the simple `G`; and an edge parallel to
the new edge would join `a` and `b` in `G`, which `htri` excludes. Katoh and Tanigawa's reason is
that such an edge closes a triangle with `eₐ` and `e_b`, and "a triangle is a `0`-dof-graph".
`splitOff_simple_of_noRigid_of_card` proves `htri` with `triangle_isProperRigidSubgraph` when
`|V(G)| ≥ 4`; `PanelHingeFramework.case_II_realization_all_k` shows instead that no edge of `G`
joins `a` and `b`. -/
lemma splitOff_simple_of_noRigid {G : Graph α β} {v a b : α} {eₐ e_b e₀ : β} {n : ℕ}
    [G.Simple] (heab : eₐ ≠ e_b) (hG_ea : G.IsLink eₐ v a) (hG_eb : G.IsLink e_b v b)
    (hnoRigid : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n)
    (htri : ∀ f, G.IsLink f a b → ∃ H : Graph α β, H.IsProperRigidSubgraph G n) :
    (G.splitOff v a b e₀).Simple := by
  -- `a ≠ b`: else `eₐ, e_b` are parallel `va`-edges, contradicting `G.Simple` via `heab`.
  have hab : a ≠ b := by
    rintro rfl
    exact heab (Simple.eq_of_isLink hG_ea hG_eb)
  refine splitOff_simple (fun e x y h ↦ ?_) (fun e₁ e₂ x y h₁ h₂ ↦ ?_)
  · -- Loop-freeness.
    rw [splitOff_isLink] at h
    rcases h with ⟨_, h, _, _⟩ | ⟨_, _, _, _, _, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
    · exact h.ne
    · exact hab
    · exact hab.symm
  · -- No parallel pair.
    rw [splitOff_isLink] at h₁ h₂
    rcases h₁ with ⟨_, h₁, _, _⟩ | ⟨rfl, _, _, _, _, hxy₁⟩
    · rcases h₂ with ⟨_, h₂, _, _⟩ | ⟨rfl, _, _, _, _, hxy₂⟩
      · exact Simple.eq_of_isLink h₁ h₂
      · -- mixed: `e₁` survives, `e₂ = e₀`; the surviving edge `e₁` links `{a, b}`.
        refine absurd (htri e₁ ?_) (not_exists.mpr hnoRigid)
        rcases hxy₂ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        exacts [h₁, h₁.symm]
    · rcases h₂ with ⟨_, h₂, _, _⟩ | ⟨rfl, _, _, _, _, _⟩
      · -- mixed: `e₁ = e₀`, `e₂` survives; the surviving edge `e₂` links `{a, b}`.
        refine absurd (htri e₂ ?_) (not_exists.mpr hnoRigid)
        rcases hxy₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        exacts [h₂, h₂.symm]
      · rfl

/-- **The triangle `vab` is a proper rigid subgraph** (`lem:splitoff-simple`; KT Lemma 6.7(ii),
p. 677): let `D ≥ 3`, let `G` be simple with `|V(G)| ≥ 4`, and let edges `eₐ`, `e_b` and `f` join
`v` to `a`, `v` to `b` and `a` to `b`. Then `H = G.induce {v, a, b}` is a proper rigid subgraph of
`G`. As `G` is simple, `v`, `a` and `b` are distinct and the edges of `H` are `eₐ`, `e_b` and `f`,
so `H` is a triangle and a `0`-dof-graph (`isKDof_zero_of_triangle`); its three vertices are fewer
than those of `G`. It is the triangle of KT's proof, and `splitOff_simple_of_noRigid_of_card`
applies it as `htri`. -/
lemma triangle_isProperRigidSubgraph [Finite α] {G : Graph α β} [G.Simple] {v a b : α}
    {eₐ e_b f : β} {n : ℕ} (hD : 3 ≤ bodyBarDim n) (hG_ea : G.IsLink eₐ v a)
    (hG_eb : G.IsLink e_b v b) (hf : G.IsLink f a b) (hcard : 4 ≤ V(G).ncard) :
    ∃ H : Graph α β, H.IsProperRigidSubgraph G n := by
  have hva : v ≠ a := hG_ea.ne
  have hvb : v ≠ b := hG_eb.ne
  have hab : a ≠ b := hf.ne
  -- `{v, a, b} ⊆ V(G)` (each vertex is the end of one of the three edges).
  have hsub : ({v, a, b} : Set α) ⊆ V(G) := by
    rintro w (rfl | rfl | rfl)
    exacts [hG_ea.left_mem, hf.left_mem, hf.right_mem]
  refine ⟨G.induce {v, a, b}, ⟨G.induce_le hsub, ?_⟩,
    (Set.one_lt_ncard (Set.toFinite _)).mpr ⟨v, by simp, a, by simp, hva⟩, ?_⟩
  · -- `def((K₃)̃) = 0`: the induced triangle is `0`-dof (vertices `v, a, b`; edges in the
    -- `isKDof_zero_of_triangle` order are `va`, `ab`, `vb`).
    refine isKDof_zero_of_triangle hD hva hab hvb
      ⟨hG_ea, by simp, by simp⟩ ⟨hf, by simp, by simp⟩ ⟨hG_eb, by simp, by simp⟩
      rfl ?_
    -- `E(H) = {eₐ, f, e_b}`. `⊇`: the three edges link pairs inside `{v, a, b}`.
    -- `⊆`: any induced edge has loopless ends among `{v, a, b}`, so it is parallel to
    -- one of the three — equal to it by `G.Simple`.
    rw [edgeSet_induce]
    apply Set.Subset.antisymm
    · rintro e ⟨x, y, he, hx, hy⟩
      have hxy : x ≠ y := he.ne
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
      obtain rfl | rfl | rfl := hx <;> obtain rfl | rfl | rfl := hy <;>
        first
          | exact absurd rfl hxy
          | exact Or.inl (he.unique_edge hG_ea)
          | exact Or.inl (he.symm.unique_edge hG_ea)
          | exact Or.inr (Or.inl (he.unique_edge hf))
          | exact Or.inr (Or.inl (he.symm.unique_edge hf))
          | exact Or.inr (Or.inr (he.unique_edge hG_eb))
          | exact Or.inr (Or.inr (he.symm.unique_edge hG_eb))
    · rintro e (rfl | rfl | rfl)
      exacts [⟨v, a, hG_ea, by simp, by simp⟩, ⟨a, b, hf, by simp, by simp⟩,
        ⟨v, b, hG_eb, by simp, by simp⟩]
  · -- Proper: `{v, a, b}` is a strict subset of `V(G)` because `|V(G)| ≥ 4 > 3 ≥ |{v,a,b}|`.
    refine hsub.ssubset_of_ne fun heq ↦ ?_
    have h3 : ({v, a, b} : Set α).ncard ≤ 3 := by
      refine (Set.ncard_insert_le _ _).trans ?_
      exact Nat.add_le_add (Set.ncard_insert_le _ _) le_rfl |>.trans (by simp)
    rw [heq] at h3; omega

/-- **A third edge at a vertex of degree at least three** (a step of `lem:chain-cycle-dichotomy`):
in a loopless graph, a vertex `v` of degree at least three has an edge other than any two given
edges `e₁` and `e₂`, as its `G.degree v ≥ 3` edges (`degree_eq_ncard_inc`) do not fit in
`{e₁, e₂}`. `cycle_isProperRigidSubgraph` uses it. -/
theorem exists_isLink_not_eq_of_three_le_degree [Finite β] {G : Graph α β} [G.Loopless] {v : α}
    (hdeg : 3 ≤ G.degree v) (e₁ e₂ : β) :
    ∃ g z, G.IsLink g v z ∧ g ≠ e₁ ∧ g ≠ e₂ := by
  classical
  rw [degree_eq_ncard_inc] at hdeg
  have hnotsub : ¬ E(G, v) ⊆ ({e₁, e₂} : Set β) := fun hsub ↦ by
    have h2 : ({e₁, e₂} : Set β).ncard ≤ 2 := by
      have := Set.ncard_insert_le e₁ ({e₂} : Set β)
      simpa using this
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    omega
  obtain ⟨g, hg, hgne⟩ := Set.not_subset.mp hnotsub
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hgne
  obtain ⟨z, hz⟩ : G.Inc g v := hg
  exact ⟨g, z, hz, hgne.1, hgne.2⟩

/-- **A cycle through a vertex of degree at least three is a proper rigid subgraph**
(`lem:chain-cycle-dichotomy`; from the proof of KT Lemma 4.6, pp. 664–665): let `G` be simple, let
`3 ≤ m ≤ D`, and let `vtx` and `edge` be injective on `Fin m`, with `edge i` joining `vtx i` and
`vtx (i + 1)`, such that every `vtx i` with `i ≠ i₀` has no edges but `edge (i − 1)` and `edge i`
(`hcl`), and `vtx i₀` has degree at least three. Then `H = G.induce (range vtx)` is a proper rigid
subgraph of `G`. An edge of `H` has two distinct ends on the cycle, one of them other than `vtx i₀`,
where `hcl` makes it a cycle edge; so `H` is the cycle on `m ≤ D` vertices, a `0`-dof-graph
(`isKDof_zero_of_cycle`). A third edge at `vtx i₀` (`exists_isLink_not_eq_of_three_le_degree`) has
its other end off the cycle, by `hcl` there, so `H` misses a vertex of `G`. This is the case of
KT's proof in which a walk closes up at a vertex of degree at least three.
`triangle_isProperRigidSubgraph` is not a case of it: it asks neither `hcl` nor a degree, but
`|V(G)| ≥ 4`. -/
lemma cycle_isProperRigidSubgraph [Finite α] [Finite β] {G : Graph α β} [G.Simple] {n m : ℕ}
    (hm : 3 ≤ m) (hmD : m ≤ bodyBarDim n)
    {vtx : Fin m → α} {edge : Fin m → β} {i₀ : Fin m}
    (hvtx : Function.Injective vtx) (hedge : Function.Injective edge)
    (hlink : ∀ i : Fin m, G.IsLink (edge i) (vtx i) (vtx (i + ⟨1, by omega⟩)))
    (hcl : ∀ i : Fin m, i ≠ i₀ → ∀ e x, G.IsLink e (vtx i) x →
      e = edge (i - ⟨1, by omega⟩) ∨ e = edge i)
    (hdeg : 3 ≤ G.degree (vtx i₀)) :
    ∃ H : Graph α β, H.IsProperRigidSubgraph G n := by
  classical
  have : NeZero m := ⟨by omega⟩
  -- `range vtx ⊆ V(G)`: each vertex is the source-end of its outgoing cyclic edge.
  have hsub : Set.range vtx ⊆ V(G) := by
    rintro x ⟨i, rfl⟩
    exact (hlink i).left_mem
  refine ⟨G.induce (Set.range vtx), ⟨G.induce_le hsub, ?_⟩, ?_, ?_⟩
  · -- `0`-dof via `isKDof_zero_of_cycle`.
    refine isKDof_zero_of_cycle hm hmD hedge
      (fun i ↦ by rw [induce_isLink]; exact ⟨hlink i, ⟨i, rfl⟩, ⟨i + ⟨1, by omega⟩, rfl⟩⟩)
      (vertexSet_induce G (Set.range vtx)) ?_
    -- `E(H) = range edge`: `⊇` from `hlink`; `⊆` picks the non-anchor end and applies `hcl`.
    rw [edgeSet_induce]
    apply Set.Subset.antisymm
    · rintro e ⟨x, y, he, ⟨i, rfl⟩, ⟨j, rfl⟩⟩
      have hij : i ≠ j := hvtx.ne_iff.mp he.ne
      rcases eq_or_ne i i₀ with hi | hi
      · -- `i = i₀`; since `i ≠ j`, `j ≠ i₀`. `hcl`'s `x`-argument is unconstrained, so
        -- `vtx i` (not `vtx i₀`) already fits.
        have hj : j ≠ i₀ := fun h ↦ hij (hi.trans h.symm)
        rcases hcl j hj e (vtx i) he.symm with h | h
        exacts [⟨_, h.symm⟩, ⟨_, h.symm⟩]
      · rcases hcl i hi e (vtx j) he with h | h
        exacts [⟨_, h.symm⟩, ⟨_, h.symm⟩]
    · rintro e ⟨j, rfl⟩
      exact ⟨vtx j, vtx (j + ⟨1, by omega⟩), hlink j, ⟨j, rfl⟩, ⟨j + ⟨1, by omega⟩, rfl⟩⟩
  · -- `2 ≤ |V(H)|` from `hvtx` + `hm`.
    rw [vertexSet_induce, Set.ncard_range_of_injective hvtx, Nat.card_fin]
    omega
  · -- Properness: `range vtx ⊊ V(G)`, from the anchor's excess third edge.
    rw [vertexSet_induce]
    refine hsub.ssubset_of_ne fun heq ↦ ?_
    obtain ⟨g, z, hgz, hg1, hg2⟩ :=
      exists_isLink_not_eq_of_three_le_degree hdeg (edge i₀) (edge (i₀ - ⟨1, by omega⟩))
    obtain ⟨k, rfl⟩ : z ∈ Set.range vtx := heq ▸ hgz.right_mem
    have hik : i₀ ≠ k := hvtx.ne_iff.mp hgz.ne
    rcases hcl k hik.symm g (vtx i₀) hgz.symm with hgk | hgk
    · -- `g = edge (k − 1)`: its `hlink` far end is `vtx k`, matching `hgz`'s — `i₀ = k − 1`.
      have hlk : G.IsLink (edge (k - ⟨1, by omega⟩)) (vtx (k - ⟨1, by omega⟩)) (vtx k) := by
        have h := hlink (k - ⟨1, by omega⟩)
        have heq1 : (k - ⟨1, by omega⟩ : Fin m) + ⟨1, by omega⟩ = k := by abel
        rwa [heq1] at h
      have hvi : vtx i₀ = vtx (k - ⟨1, by omega⟩) :=
        (hgk ▸ hgz : G.IsLink _ (vtx i₀) (vtx k)).left_unique hlk
      exact hg1 (by rw [hgk, hvtx hvi])
    · -- `g = edge k`: `hlink k`'s far end `vtx (k + 1)` must equal `vtx i₀` — `k = i₀ − 1`.
      have hlk : G.IsLink (edge k) (vtx k) (vtx (k + ⟨1, by omega⟩)) := hlink k
      rcases (hgk ▸ hgz : G.IsLink _ (vtx i₀) (vtx k)).eq_and_eq_or_eq_and_eq hlk with
        ⟨hvi, -⟩ | ⟨hvi, -⟩
      · exact hik (hvtx hvi)
      · have hk : k = i₀ - ⟨1, by omega⟩ := by
          have hidx : i₀ = k + ⟨1, by omega⟩ := hvtx hvi
          rw [hidx]; abel
        exact hg2 (by rw [hgk, hk])

/-- **Splitting off keeps the graph simple** (`lem:splitoff-simple`; KT Lemma 6.7(ii), p. 677):
let `D ≥ 3`, let `G` be simple with `|V(G)| ≥ 4` and no proper rigid subgraph, and let edges
`eₐ ≠ e_b` join `v` to `a` and to `b`. Then `G_v^{ab}` is simple, by `splitOff_simple_of_noRigid`
with the triangle of `triangle_isProperRigidSubgraph`. -/
lemma splitOff_simple_of_noRigid_of_card [Finite α] {G : Graph α β} {v a b : α}
    {eₐ e_b e₀ : β} {n : ℕ} [G.Simple] (hD : 3 ≤ bodyBarDim n) (heab : eₐ ≠ e_b)
    (hG_ea : G.IsLink eₐ v a) (hG_eb : G.IsLink e_b v b) (hcard : 4 ≤ V(G).ncard)
    (hnoRigid : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) :
    (G.splitOff v a b e₀).Simple :=
  splitOff_simple_of_noRigid heab hG_ea hG_eb hnoRigid
    fun _ hf ↦ triangle_isProperRigidSubgraph hD hG_ea hG_eb hf hcard

/-- **A minimal `0`-dof-graph on three vertices is a triangle** (`lem:triangle-third-edge`; from
the proof of KT Lemma 6.7(i), p. 677): let `D ≥ 3`, let `G` be a simple minimal `0`-dof-graph with
three vertices, and let edges `eₐ ≠ e_b` join `v` to `a` and to `b`. Then `a ≠ b`,
`V(G) = {v, a, b}`, and an edge of `G` joins `a` and `b`.

As `G` is simple, `a` and `b` differ from `v` and from each other, so `v`, `a` and `b` are the three
vertices of `G`. By KT eq. (2.4), `rank M(G̃) = 2D` (`rank_matroidMG_of_isKDof_zero`), and `M(G̃)`
has the `(D − 1)|E(G)|` elements of `E(G̃)`, so `G` has an edge other than `eₐ` and `e_b`. Its ends
are two of `v`, `a`, `b`, and as `G` is simple, they are `a` and `b`. -/
theorem exists_isLink_of_isMinimalKDof_card_three [DecidableEq β] [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} [G.Simple]
    (hD : 3 ≤ bodyBarDim n) (hG : G.IsMinimalKDof n 0)
    (hcard : V(G).ncard = 3)
    {v a b : α} {eₐ e_b : β}
    (hG_ea : G.IsLink eₐ v a) (hG_eb : G.IsLink e_b v b) (heab : eₐ ≠ e_b) :
    a ≠ b ∧ V(G) = {v, a, b} ∧ ∃ f, G.IsLink f a b := by
  have hva : v ≠ a := hG_ea.ne
  have hvb : v ≠ b := hG_eb.ne
  have hab : a ≠ b := fun h ↦ heab (Simple.eq_of_isLink hG_ea (h ▸ hG_eb))
  have hsub : ({v, a, b} : Set α) ⊆ V(G) := by
    rintro w (rfl | rfl | rfl)
    exacts [hG_ea.left_mem, hG_ea.right_mem, hG_eb.right_mem]
  have hncard3 : ({v, a, b} : Set α).ncard = 3 := by
    rw [ncard_insert_of_notMem (by simp [hva, hvb]),
        ncard_insert_of_notMem (by simp [hab]), ncard_singleton]
  have hVeq : V(G) = {v, a, b} :=
    (Set.eq_of_subset_of_ncard_le hsub (hcard ▸ hncard3.ge) V(G).toFinite).symm
  have hne : V(G).Nonempty := ⟨v, hG_ea.left_mem⟩
  have hrank : ((G.matroidMG n).rank : ℤ) = bodyBarDim n * ((V(G).ncard : ℤ) - 1) :=
    rank_matroidMG_of_isKDof_zero (by omega) hne hG.1
  have hrank_le : (G.matroidMG n).rank ≤ bodyHingeMult n * E(G).ncard := by
    calc (G.matroidMG n).rank ≤ E(G.mulTilde n).ncard := by
          rw [Matroid.rank_def, mulTilde]; exact (G.matroidMG n).rk_le_card _
      _ = bodyHingeMult n * E(G).ncard := by rw [mulTilde, edgeMultiply_edgeSet_ncard]
  have hE3 : 3 ≤ E(G).ncard := by
    rw [hcard] at hrank; norm_num at hrank
    have hle : ((G.matroidMG n).rank : ℤ) ≤ (bodyHingeMult n : ℤ) * E(G).ncard :=
      by exact_mod_cast hrank_le
    rw [show (bodyHingeMult n : ℤ) = (bodyBarDim n : ℤ) - 1 from by unfold bodyHingeMult; omega,
        hrank] at hle
    exact_mod_cast (show (3 : ℤ) ≤ E(G).ncard by
      nlinarith [show (0 : ℤ) < bodyBarDim n from by exact_mod_cast Nat.pos_of_ne_zero (by omega)])
  have hne2 : (E(G) \ {eₐ, e_b}).Nonempty := by
    by_contra h
    simp only [Set.not_nonempty_iff_eq_empty] at h
    have hpair : E(G) ⊆ {eₐ, e_b} := Set.sdiff_eq_empty.mp h
    have h2 : ({eₐ, e_b} : Set β).ncard = 2 := by
      rw [ncard_insert_of_notMem (by simp [heab]) (Set.finite_singleton _), ncard_singleton]
    exact absurd (Set.ncard_le_ncard hpair (Set.toFinite _)) (by omega)
  obtain ⟨f, hfE, hfne⟩ := hne2
  rw [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hfne
  obtain ⟨hfea, hfeb⟩ := hfne
  obtain ⟨x, y, hfxy⟩ := G.exists_isLink_of_mem_edgeSet hfE
  have hx : x ∈ ({v, a, b} : Set α) := hVeq ▸ hfxy.left_mem
  have hy : y ∈ ({v, a, b} : Set α) := hVeq ▸ hfxy.right_mem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  refine ⟨hab, hVeq, ?_⟩
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  · exact absurd rfl hfxy.ne
  · exact absurd (hfxy.unique_edge hG_ea) hfea
  · exact absurd (hfxy.unique_edge hG_eb) hfeb
  · exact absurd (hfxy.symm.unique_edge hG_ea) hfea
  · exact absurd rfl hfxy.ne
  · exact ⟨f, hfxy⟩
  · exact absurd (hfxy.symm.unique_edge hG_eb) hfeb
  · exact ⟨f, hfxy.symm⟩
  · exact absurd rfl hfxy.ne

/-- **The isomorphism from `G_a^{vc}` to `G_v^{ab}`** (`lem:splitOff-isLink-relabel`; KT p. 686):
let edges `eₐ`, `e_b`, `e_c` join `v` to `a`, `v` to `b` and `a` to `c`, with `a`, `b`, `c`
different from `v`, `c ≠ a` and `eₐ ≠ e_b`, and let `eₐ`, `e_b` be the only edges at
`v` and `eₐ`, `e_c` the only edges at `a`. Let `e₀ ≠ e₁` be labels outside `E(G)` for the new
edges `ab` of `G_v^{ab}` and `vc` of `G_a^{vc}`. With `ρ = Equiv.swap a v` and
`σ = Equiv.swap e_b e₀ * Equiv.swap e₁ e_c`,

  `(G.splitOff a v c e₁).IsLink e x y ↔ (G.splitOff v a b e₀).IsLink (σ e) (ρ x) (ρ y)`.

On the edges of `G_a^{vc}`, `σ` maps `e_b` (`vb`) to the new edge `e₀` (`ab`), the new edge `e₁`
(`vc`) to `e_c` (`ac`), and fixes the others, which meet neither `v` nor `a`. This is Katoh and
Tanigawa's isomorphism `ρ` with `ρ(v) = a`, and its map on edges is that of their eq. (6.31)
(p. 687). The proof expands `splitOff_isLink` on both sides and uses that `v` and `a` have no
other edges. -/
lemma splitOff_isLink_relabel [DecidableEq α] [DecidableEq β] {G : Graph α β}
    {v a b c : α} {eₐ e_b e_c e₀ e₁ : β}
    (hG_ea : G.IsLink eₐ v a) (hG_eb : G.IsLink e_b v b) (hG_ec : G.IsLink e_c a c)
    (hav : a ≠ v) (hbv : b ≠ v) (hcv : c ≠ v) (hca : c ≠ a) (heab : eₐ ≠ e_b)
    (hclv : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    (hcla : ∀ e x, G.IsLink e a x → e = eₐ ∨ e = e_c)
    (he₀ : e₀ ∉ E(G)) (he₁ : e₁ ∉ E(G)) (he₁₀ : e₁ ≠ e₀)
    {e : β} {x y : α} :
    (G.splitOff a v c e₁).IsLink e x y ↔
      (G.splitOff v a b e₀).IsLink
        ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)
        ((Equiv.swap a v) x) ((Equiv.swap a v) y) := by
  -- Derived edge-distinctness facts.
  have he_b_ne_e₀ : e_b ≠ e₀ := fun h => he₀ (h ▸ hG_eb.edge_mem)
  have he_c_ne_e₀ : e_c ≠ e₀ := fun h => he₀ (h ▸ hG_ec.edge_mem)
  have he_b_ne_e₁ : e_b ≠ e₁ := fun h => he₁ (h ▸ hG_eb.edge_mem)
  have he_c_ne_e₁ : e_c ≠ e₁ := fun h => he₁ (h ▸ hG_ec.edge_mem)
  -- `e_b ≠ e_c`: if equal, their endpoint sets coincide; `{v,b} = {a,c}` forces `v = a` or
  -- `v = c`, contradicting `hav` / `hcv`.
  have he_b_ne_e_c : e_b ≠ e_c := by
    intro h
    -- left_eq_or_eq: hG_eb.left_eq_or_eq (h ▸ hG_ec) gives v = a ∨ v = c.
    rcases hG_eb.left_eq_or_eq (h ▸ hG_ec) with hva | hvc
    · exact hav hva.symm
    · exact hcv hvc.symm
  -- `b ≠ a`: if b = a, then G.IsLink e_b a v (from hG_eb.symm rewritten), and hcla gives
  -- e_b = eₐ ∨ e_b = e_c; heab and he_b_ne_e_c both give contradiction.
  have hba : b ≠ a := fun hba' => he_b_ne_e_c
    ((hcla e_b v (hba' ▸ hG_eb.symm)).resolve_left (Ne.symm heab))
  -- Key `σ` evaluations (σ = Equiv.swap e_b e₀ * Equiv.swap e₁ e_c).
  have hσ_eb : (Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e_b = e₀ := by
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
    split_ifs with h1 h2 <;> simp_all
  have hσ_e₁ : (Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e₁ = e_c := by
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
    split_ifs with h1 h2 <;> simp_all
  have hσ_other : ∀ f, f ≠ e_b → f ≠ e₁ → f ≠ e_c → f ≠ e₀ →
      (Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) f = f := by
    intro f hfb hf₁ hfc hf₀
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
    split_ifs <;> simp_all
  -- Key `ρ` evaluations (ρ = Equiv.swap a v).
  have hρ_a : (Equiv.swap a v) a = v := Equiv.swap_apply_left a v
  have hρ_v : (Equiv.swap a v) v = a := Equiv.swap_apply_right a v
  have hρ_other : ∀ w, w ≠ a → w ≠ v → (Equiv.swap a v) w = w :=
    fun w hwa hwv => Equiv.swap_apply_of_ne_of_ne hwa hwv
  -- Helper: ρ w = a ∧ w ≠ a → w = v.
  have hρ_eq_a_imp_v : ∀ w, w ≠ a → (Equiv.swap a v) w = a → w = v := by
    intro w hwa heq
    by_contra hwnv; rw [hρ_other w hwa hwnv] at heq; exact hwa heq
  -- Helper: eₐ's endpoints are {v, a} — used to derive contradictions when e links a to something.
  -- Helper: e_b's unique right endpoint (from G.IsLink e_b v b).
  -- hG_eb.eq_and_eq_or_eq_and_eq hy with hy : G.IsLink e_b v y' gives:
  -- (v = v ∧ b = y') ∨ (v = y' ∧ b = v).
  have hG_eb_right : ∀ y', G.IsLink e_b v y' → y' = b := by
    intro y' hy
    rcases hG_eb.eq_and_eq_or_eq_and_eq hy with ⟨-, hby'⟩ | ⟨-, hbv'⟩
    · exact hby'.symm
    · exact absurd hbv' hbv
  have hG_eb_left : ∀ x', G.IsLink e_b x' b → x' = v := by
    intro x' hx
    rcases hG_eb.eq_and_eq_or_eq_and_eq hx with ⟨hvx', -⟩ | ⟨hbv', -⟩
    · exact hvx'.symm
    · exact absurd hbv'.symm hbv
  -- The iff follows by expanding `splitOff_isLink` on both sides and case-splitting.
  simp only [splitOff_isLink]
  constructor
  · -- Forward: (G.splitOff a v c e₁).IsLink e x y → RHS.
    rintro (⟨hne₁, hGe, hxa, hya⟩ | ⟨he_eq_e₁, hav_ne, hca_ne, hvV, hcV, hxy⟩)
    · -- Surviving edge: e ≠ e₁, G.IsLink e x y, x ≠ a, y ≠ a.
      by_cases heb : e = e_b
      · -- e = e_b: σ e = e₀ → RHS Case 2 (fresh edge of G_v^{ab}).
        -- Determine x, y from G.IsLink e_b x y and hG_eb : G.IsLink e_b v b.
        -- eq_and_eq_or_eq_and_eq gives (v = x ∧ b = y) ∨ (v = y ∧ b = x).
        rcases hG_eb.eq_and_eq_or_eq_and_eq (heb ▸ hGe) with ⟨hvx, hby⟩ | ⟨hvy, hbx⟩
        · -- v = x, b = y.
          rw [heb, hσ_eb, ← hvx, ← hby, hρ_v, hρ_other b (fun h => hya (hby ▸ h ▸ rfl)) hbv]
          exact Or.inr ⟨rfl, hav, hbv, hG_ea.right_mem, hG_eb.right_mem, Or.inl ⟨rfl, rfl⟩⟩
        · -- v = y, b = x.
          rw [heb, hσ_eb, ← hbx, ← hvy,
              hρ_other b (fun h => hxa (hbx ▸ h ▸ rfl)) hbv, hρ_v]
          exact Or.inr ⟨rfl, hav, hbv, hG_ea.right_mem, hG_eb.right_mem, Or.inr ⟨rfl, rfl⟩⟩
      · -- e ≠ e_b: use degree-2 closures to show endpoints avoid v, then σ fixes e.
        have hxv : x ≠ v := by
          intro hxv
          rcases hclv e y (hxv ▸ hGe) with rfl | rfl
          · -- e = eₐ links v and a; eq_and_eq gives (v = v ∧ a = y) ∨ (v = y ∧ a = v).
            rcases hG_ea.eq_and_eq_or_eq_and_eq (hxv ▸ hGe) with ⟨-, hay⟩ | ⟨-, hav_eq⟩
            · exact hya hay.symm
            · exact hav hav_eq
          · exact heb rfl
        have hyv : y ≠ v := by
          intro hyv
          rcases hclv e x (hyv ▸ hGe.symm) with rfl | rfl
          · rcases hG_ea.eq_and_eq_or_eq_and_eq (hyv ▸ hGe.symm) with ⟨-, hax⟩ | ⟨-, hav_eq⟩
            · exact hxa hax.symm
            · exact hav hav_eq
          · exact heb rfl
        have he₀_ne : e ≠ e₀ := fun h => he₀ (h ▸ hGe.edge_mem)
        -- e ≠ e_c: endpoints of e_c are {a, c}, but x ≠ a and y ≠ a.
        -- eq_and_eq_or_eq_and_eq gives (a = x ∧ c = y) ∨ (a = y ∧ c = x).
        have hec : e ≠ e_c := by
          intro hec
          rcases hG_ec.eq_and_eq_or_eq_and_eq (hec ▸ hGe) with ⟨hax, -⟩ | ⟨hay, -⟩
          · exact hxa hax.symm
          · exact hya hay.symm
        have hσe : (Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e = e :=
          hσ_other e heb hne₁ hec he₀_ne
        have hρx : (Equiv.swap a v) x = x := hρ_other x hxa hxv
        have hρy : (Equiv.swap a v) y = y := hρ_other y hya hyv
        rw [hσe, hρx, hρy]
        exact Or.inl ⟨he₀_ne, hGe, hxv, hyv⟩
    · -- Fresh edge: e = e₁, endpoints are {v, c}; σ e₁ = e_c; ρ v = a; ρ c = c.
      subst he_eq_e₁
      have hρc : (Equiv.swap a v) c = c := hρ_other c hca hcv
      rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · -- x = v, y = c; σ e₁ = e_c; ρ v = a; ρ c = c.
        rw [hσ_e₁, hρ_v, hρc]
        exact Or.inl ⟨fun h => he₀ (h ▸ hG_ec.edge_mem), hG_ec, hav, hcv⟩
      · -- x = c, y = v.
        rw [hσ_e₁, hρc, hρ_v]
        exact Or.inl ⟨fun h => he₀ (h ▸ hG_ec.edge_mem), hG_ec.symm, hcv, hav⟩
  · -- Backward: RHS → (G.splitOff a v c e₁).IsLink e x y.
    rintro (⟨hσne₀, hGσe, hρxv, hρyv⟩ | ⟨hσe_eq_e₀, -, hbv_ne, haV, hbV, hxy⟩)
    · -- Surviving in G_v^{ab}: σ e ≠ e₀, G.IsLink (σ e) (ρ x) (ρ y), ρ x ≠ v, ρ y ≠ v.
      have hxa : x ≠ a := fun h => hρxv (h ▸ hρ_a)
      have hya : y ≠ a := fun h => hρyv (h ▸ hρ_a)
      by_cases he₁e : e = e₁
      · -- e = e₁: σ e = e_c. G.IsLink e_c (ρ x) (ρ y). Endpoints of e_c are {a, c}.
        subst he₁e; rw [hσ_e₁] at hGσe hσne₀
        -- Use eq_and_eq_or_eq_and_eq to get (a = ρ x ∧ c = ρ y) ∨ (a = ρ y ∧ c = ρ x).
        rcases hG_ec.eq_and_eq_or_eq_and_eq hGσe with ⟨hρxa, hρyc⟩ | ⟨hρxc, hρya⟩
        · -- hρxa : a = ρ x, hρyc : c = ρ y.
          -- a = ρ x → x = v.
          have hxv : x = v := hρ_eq_a_imp_v x hxa hρxa.symm
          -- c = ρ y → y = c (c ≠ a, c ≠ v).
          have hyc : y = c := by
            have heq : (Equiv.swap a v) y = c := hρyc.symm
            by_contra hync
            by_cases hyv : y = v
            · rw [hyv, hρ_v] at heq; exact hca heq.symm  -- heq : a = c
            · rw [hρ_other y hya hyv] at heq; exact hync heq
          exact Or.inr ⟨rfl, hav.symm, hca, hG_ea.left_mem, hG_ec.right_mem,
                        Or.inl ⟨hxv, hyc⟩⟩
        · -- hρxc : a = ρ y, hρya : c = ρ x (orientations from eq_and_eq_or_eq_and_eq).
          have hyv : y = v := hρ_eq_a_imp_v y hya hρxc.symm
          have hxc : x = c := by
            have heq : (Equiv.swap a v) x = c := hρya.symm
            by_contra hxnc
            by_cases hxv : x = v
            · rw [hxv, hρ_v] at heq; exact hca heq.symm  -- heq : a = c
            · rw [hρ_other x hxa hxv] at heq; exact hxnc heq
          exact Or.inr ⟨rfl, hav.symm, hca, hG_ea.left_mem, hG_ec.right_mem,
                        Or.inr ⟨hxc, hyv⟩⟩
      · -- e ≠ e₁: σ e ≠ e₁ (else e₁ ∈ E(G)), σ e ≠ e_c, σ e ≠ e_b, derive σ e = e.
        have hσe_ne_e₁_val : (Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e ≠ e₁ :=
          fun hσe_e₁ => he₁ (hσe_e₁ ▸ hGσe.edge_mem)
        have hσe_ne_ec : (Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e ≠ e_c := by
          -- σ e₁ = e_c (hσ_e₁); so σ e = e_c → e = e₁ by injectivity. Contradicts he₁e.
          intro hσec
          exact he₁e ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c).injective (hσec.trans hσ_e₁.symm))
        have hσe_ne_eb : (Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e ≠ e_b := by
          intro hσe_eb
          -- hG_eb : G.IsLink e_b v b; eq_and_eq gives (v = ρ x ∧ b = ρ y) ∨ (v = ρ y ∧ b = ρ x).
          rcases hG_eb.eq_and_eq_or_eq_and_eq (hσe_eb ▸ hGσe) with ⟨hvρx, -⟩ | ⟨hvρy, -⟩
          · exact hρxv hvρx.symm
          · exact hρyv hvρy.symm
        have he_ne_eb : e ≠ e_b := fun heb => hσne₀ (heb ▸ hσ_eb)
        have he_ne_ec : e ≠ e_c := by
          -- σ e_c = (swap e_b e₀) ((swap e₁ e_c) e_c) = (swap e_b e₀) e₁ = e₁
          -- (since e₁ ≠ e_b and e₁ ≠ e₀), so e = e_c → σ e = e₁, contradicting hσe_ne_e₁_val.
          intro hec
          apply hσe_ne_e₁_val
          calc (Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e
              = (Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e_c := by rw [hec]
            _ = (Equiv.swap e_b e₀) ((Equiv.swap e₁ e_c) e_c) := rfl
            _ = (Equiv.swap e_b e₀) e₁ := by rw [Equiv.swap_apply_right]
            _ = e₁ := Equiv.swap_apply_of_ne_of_ne he_b_ne_e₁.symm he₁₀
        have he_ne_e₀ : e ≠ e₀ := by
          -- σ e₀ = (swap e_b e₀) ((swap e₁ e_c) e₀) = (swap e_b e₀) e₀ = e_b
          -- (since e₀ ≠ e₁ and e₀ ≠ e_c), so e = e₀ → σ e = e_b, contradicting hσe_ne_eb.
          intro he₀e
          apply hσe_ne_eb
          calc (Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e
              = (Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e₀ := by rw [he₀e]
            _ = (Equiv.swap e_b e₀) ((Equiv.swap e₁ e_c) e₀) := rfl
            _ = (Equiv.swap e_b e₀) e₀ :=
                by rw [Equiv.swap_apply_of_ne_of_ne he₁₀.symm he_c_ne_e₀.symm]
            _ = e_b := Equiv.swap_apply_right e_b e₀
        have hσe_eq : (Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e = e :=
          hσ_other e he_ne_eb he₁e he_ne_ec he_ne_e₀
        rw [hσe_eq] at hGσe
        -- ρ x ≠ a: if ρ x = a then x = v, so e is incident to v via G.IsLink e v (ρ y).
        -- Closure at v: e = eₐ or e_b, both excluded.
        have hρxa_ne_a : (Equiv.swap a v) x ≠ a := by
          intro hρxa
          have hxv : x = v := hρ_eq_a_imp_v x hxa hρxa
          rw [hxv, hρ_v] at hGσe
          -- hGσe : G.IsLink e a (ρ y); use closure at a.
          rcases hcla e ((Equiv.swap a v) y) hGσe with rfl | rfl
          · -- e = eₐ; hG_ea : G.IsLink eₐ v a; eq_and_eq gives (v = a ∧ ..) ∨ (v = ρ y ∧ ..).
            rcases hG_ea.eq_and_eq_or_eq_and_eq hGσe with ⟨hva, -⟩ | ⟨hρyv', -⟩
            · exact hav hva.symm
            · exact hρyv hρyv'.symm
          · exact he_ne_ec rfl
        have hρya_ne_a : (Equiv.swap a v) y ≠ a := by
          intro hρya
          have hyv : y = v := hρ_eq_a_imp_v y hya hρya
          rw [hyv, hρ_v] at hGσe
          rcases hcla e ((Equiv.swap a v) x) hGσe.symm with rfl | rfl
          · rcases hG_ea.eq_and_eq_or_eq_and_eq hGσe.symm with ⟨hva, -⟩ | ⟨hρxv', -⟩
            · exact hav hva.symm
            · exact hρxv hρxv'.symm
          · exact he_ne_ec rfl
        -- ρ x ≠ a → x ≠ v; combined with hxa : x ≠ a, gives ρ x = x.
        have hxv' : x ≠ v := fun hxv => hρxa_ne_a (hxv ▸ hρ_v)
        have hρx_eq : (Equiv.swap a v) x = x := hρ_other x hxa hxv'
        have hyv' : y ≠ v := fun hyv => hρya_ne_a (hyv ▸ hρ_v)
        have hρy_eq : (Equiv.swap a v) y = y := hρ_other y hya hyv'
        rw [hρx_eq, hρy_eq] at hGσe
        exact Or.inl ⟨he₁e, hGσe, hxa, hya⟩
    · -- Fresh edge of G_v^{ab}: σ e = e₀ → e = e_b (σ injective, σ e_b = e₀).
      have he_eq_eb : e = e_b :=
        (Equiv.swap e_b e₀ * Equiv.swap e₁ e_c).injective (hσe_eq_e₀.trans hσ_eb.symm)
      subst he_eq_eb
      -- hxy: (ρ x = a ∧ ρ y = b) ∨ (ρ x = b ∧ ρ y = a).
      rcases hxy with ⟨hρx_a, hρy_b⟩ | ⟨hρx_b, hρy_a⟩
      · -- ρ x = a → x = v; ρ y = b → y = b.
        -- x ≠ a: if x = a then ρ a = v, but ρ x = a → v = a, contradicting hav.
        have hxa_x : x ≠ a := fun hxa' => hav ((hρ_a.symm.trans (hxa' ▸ hρx_a)).symm)
        have hxv : x = v := hρ_eq_a_imp_v x hxa_x hρx_a
        have hyb : y = b := by
          by_contra hynb
          by_cases hyv : y = v
          · -- ρ v = a, so hρy_b becomes a = b; then G.IsLink e a v, closed by hcla.
            -- (After subst he_eq_eb, e_b is replaced by e in the context.)
            rw [hyv, hρ_v] at hρy_b
            rcases hcla e v (hρy_b ▸ hG_eb.symm) with h_ea | h_ec
            · exact heab h_ea.symm
            · exact he_b_ne_e_c h_ec
          by_cases hya : y = a
          · rw [hya, hρ_a] at hρy_b; exact hbv hρy_b.symm  -- hρy_b : v = b
          · rw [hρ_other y hya hyv] at hρy_b; exact hynb hρy_b
        exact Or.inl ⟨he_b_ne_e₁, hxv ▸ hyb ▸ hG_eb, hxv ▸ hav.symm, hyb ▸ hba⟩
      · -- ρ x = b → x = b; ρ y = a → y = v.
        -- y ≠ a: if y = a then ρ a = v, but ρ y = a → v = a, contradicting hav.
        have hya_y : y ≠ a := fun hya' => hav ((hρ_a.symm.trans (hya' ▸ hρy_a)).symm)
        have hyv : y = v := hρ_eq_a_imp_v y hya_y hρy_a
        have hxb : x = b := by
          by_contra hxnb
          by_cases hxv : x = v
          · -- ρ v = a, so hρx_b becomes a = b; then G.IsLink e a v, closed by hcla.
            -- (After subst he_eq_eb, e_b is replaced by e in the context.)
            rw [hxv, hρ_v] at hρx_b
            rcases hcla e v (hρx_b ▸ hG_eb.symm) with h_ea | h_ec
            · exact heab h_ea.symm
            · exact he_b_ne_e_c h_ec
          by_cases hxa : x = a
          · rw [hxa, hρ_a] at hρx_b; exact hbv hρx_b.symm  -- hρx_b : v = b
          · rw [hρ_other x hxa hxv] at hρx_b; exact hxnb hρx_b
        exact Or.inl ⟨he_b_ne_e₁, hxb ▸ hyv ▸ hG_eb.symm, hxb ▸ hba, hyv ▸ hav.symm⟩

/-- **Inducing and splitting off commute** (a step of `lem:reduction-step-pos`): for `v ∉ S` and
`a, b ∈ S ∩ V(G)`,

  `(G.induce (insert v S)).splitOff v a b e₀ = (G.splitOff v a b e₀).induce S`.

Both graphs have the vertices `S`. An edge `e ≠ e₀` joins `x` and `y` in either exactly when it
joins them in `G` and `x, y ∈ S`; the new edge joins `a` and `b` in both, which needs
`a, b ∈ V(G)` on the right. -/
lemma induce_insert_splitOff {G : Graph α β} {v a b : α} {e₀ : β} {S : Set α}
    (hvS : v ∉ S) (haS : a ∈ S) (hbS : b ∈ S) (haV : a ∈ V(G)) (hbV : b ∈ V(G)) :
    (G.induce (insert v S)).splitOff v a b e₀ = (G.splitOff v a b e₀).induce S := by
  have hav : a ≠ v := fun h => hvS (h ▸ haS)
  have hbv : b ≠ v := fun h => hvS (h ▸ hbS)
  refine Graph.ext ?_ (fun e x y => ?_)
  · -- Vertex sets: both are `S`.
    simp only [vertexSet_splitOff]
    ext x
    simp only [Set.mem_sdiff, Set.mem_singleton_iff]
    exact ⟨fun ⟨hxins, hxnv⟩ => Or.resolve_left hxins hxnv,
           fun hxS => ⟨Or.inr hxS, fun h => hvS (h ▸ hxS)⟩⟩
  · -- Link relations: unfold both sides.
    simp only [splitOff_isLink, Graph.induce_isLink]
    constructor
    · -- LHS → RHS
      rintro (⟨hne, ⟨hGl, hxins, hyins⟩, hxv, hyv⟩ | ⟨rfl, -, -, -, -, hxy⟩)
      · -- Surviving edge: membership in `insert v S` + `≠ v` gives `∈ S`.
        exact ⟨Or.inl ⟨hne, hGl, hxv, hyv⟩,
          Set.mem_of_mem_insert_of_ne hxins hxv,
          Set.mem_of_mem_insert_of_ne hyins hyv⟩
      · -- Fresh edge `e = e₀`: endpoints are `a, b ∈ S`.
        rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨Or.inr ⟨rfl, hav, hbv, haV, hbV, Or.inl ⟨rfl, rfl⟩⟩, haS, hbS⟩
        · exact ⟨Or.inr ⟨rfl, hav, hbv, haV, hbV, Or.inr ⟨rfl, rfl⟩⟩, hbS, haS⟩
    · -- RHS → LHS
      rintro ⟨hlink | hlink, hxS, hyS⟩
      · -- Surviving edge: inject back into `insert v S`.
        obtain ⟨hne, hGl, hxv, hyv⟩ := hlink
        exact Or.inl ⟨hne,
          ⟨hGl, Set.mem_insert_of_mem _ hxS, Set.mem_insert_of_mem _ hyS⟩, hxv, hyv⟩
      · -- Fresh edge `e = e₀`: `x = a` or `x = b`, both in `insert v S`.
        obtain ⟨rfl, -, -, -, -, hxy⟩ := hlink
        rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · -- x = a, y = b; hxS : a ∈ S, hyS : b ∈ S
          exact Or.inr ⟨rfl, hav, hbv,
            Set.mem_insert_of_mem _ hxS, Set.mem_insert_of_mem _ hyS, Or.inl ⟨rfl, rfl⟩⟩
        · -- x = b, y = a; hxS : b ∈ S, hyS : a ∈ S; goal has y ≠ v ∧ x ≠ v ∧ y∈.. ∧ x∈..
          exact Or.inr ⟨rfl, hav, hbv,
            Set.mem_insert_of_mem _ hyS, Set.mem_insert_of_mem _ hxS, Or.inr ⟨rfl, rfl⟩⟩

/-! ## Chains of length `d` (`def:chain-data`; KT Lemma 4.6)

A chain `v₀v₁…v_d` of length `d` in `G` (KT Lemma 4.6, p. 664) has distinct vertices `v₀, …, v_d`
and edges `vᵢvᵢ₊₁`, and its interior vertices `v₁, …, v_{d−1}` have degree two. `chainData_extract`
(`lem:chain-data-extract`) gives one, and Case III of the algebraic induction splits off at its
interior vertices for every `d` (KT Lemma 6.13, pp. 692–698; `lem:case-III-chain-dispatch`). The
structure records the chain and a label `e₀ ∉ E(G)` for the new edge of a splitting off
(`fmlnote:graph-operations`). At `d = 3` the chain `v₀v₁v₂v₃` is Katoh and Tanigawa's `b v a c`
(p. 680), with `vtx = ![b, v, a, c]` and `edge = ![e_b, eₐ, e_c]`. -/

/-- **A chain of length `d`** (`def:chain-data`; KT Lemma 4.6, p. 664): distinct vertices
`vtx 0, …, vtx d` of `G` and distinct edges `edge i` joining `vtx i` and `vtx (i + 1)`, such that
every edge of `G` at an interior vertex `vtx i`, `1 ≤ i ≤ d − 1`, is `edge (i − 1)` or `edge i`;
with a label `e₀ ∉ E(G)` for the new edge of a splitting off (`fmlnote:graph-operations`). The
parameter `n` is the dimension, `D = bodyBarDim n`, and the chain has length `d = n` (`d_eq`). -/
structure ChainData (G : Graph α β) (n : ℕ) where
  /-- The length of the chain. -/
  d : ℕ
  /-- The chain has an edge: `d ≥ 1`. -/
  hd : 1 ≤ d
  /-- The length is the dimension: `d = n`, where `D = bodyBarDim n` (KT Lemma 4.6's chains have
  length `d`). -/
  d_eq : d = n
  /-- The vertices `v₀, …, v_d` of the chain. -/
  vtx : Fin (d + 1) → α
  /-- The edges of the chain: `edge i` joins `vtx i` and `vtx (i + 1)`. -/
  edge : Fin d → β
  /-- The label of the new edge when splitting off at an interior vertex of the chain. -/
  e₀ : β
  /-- The vertices of the chain are vertices of `G`. -/
  vtx_mem : ∀ i, vtx i ∈ V(G)
  /-- The vertices of the chain are distinct. -/
  vtx_inj : Function.Injective vtx
  /-- `edge i` joins `vtx i` and `vtx (i + 1)` in `G`. -/
  link : ∀ i : Fin d, G.IsLink (edge i) (vtx i.castSucc) (vtx i.succ)
  /-- The edges of the chain are distinct. -/
  edge_inj : Function.Injective edge
  /-- **The interior vertices have degree two** (KT's `d_G(vᵢ) = 2` for `1 ≤ i ≤ d − 1`): every
  edge of `G` at `vtx i`, for `0 < i < d`, is `edge (i − 1)` or `edge i`. -/
  deg_two : ∀ i : Fin d, 0 < (i : ℕ) →
              (∀ e x, G.IsLink e (vtx i.castSucc) x →
                e = edge ⟨(i : ℕ) - 1, by omega⟩ ∨ e = edge i)
  /-- The label `e₀` is not an edge of `G`. -/
  e₀_fresh : e₀ ∉ E(G)

namespace ChainData

variable {G : Graph α β} {n : ℕ}

/-- The two edges `edge (i − 1)` and `edge i` at an interior vertex (`0 < i`) are distinct
(`edge_inj`). -/
lemma pred_edge_ne (cd : G.ChainData n) {i : Fin cd.d} (hi : 0 < (i : ℕ)) :
    cd.edge ⟨(i : ℕ) - 1, by omega⟩ ≠ cd.edge i := by
  intro h
  have := congrArg Fin.val (cd.edge_inj h)
  simp only at this
  omega

/-- `edge i` joins `vtx i` and `vtx (i + 1)` (the field `link`). -/
lemma isLink_edge (cd : G.ChainData n) (i : Fin cd.d) :
    G.IsLink (cd.edge i) (cd.vtx i.castSucc) (cd.vtx i.succ) := cd.link i

/-! ### Splitting off at an interior vertex

For an interior index `i` (`0 < i`), Case III splits off at `v = vtx i` along its neighbours
`a = vtx (i + 1)` and `b = vtx (i − 1)`, whose edges to `v` are `e_a = edge i` and
`e_b = edge (i − 1)`. These lemmas give the tuple `(v, a, b, e_a, e_b)` in the form that
`PanelHingeFramework.chainData_dispatch_interior` reads it, with both edges leaving `v`. -/

/-- For `0 < i`, the successor of the index `i − 1` of the edges is the index `i` of the
vertices: `(⟨i − 1, _⟩ : Fin cd.d).succ = i.castSucc`. -/
lemma pred_succ_eq_castSucc (cd : G.ChainData n) {i : Fin cd.d} (hi : 0 < (i : ℕ)) :
    (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).succ = i.castSucc :=
  Fin.ext (by simp only [Fin.val_succ, Fin.val_castSucc]; omega)

/-- For `0 < i`, `edge (i − 1)` joins `vtx i` to `vtx (i − 1)` (the field `link` at `i − 1`,
reversed). -/
lemma isLink_pred_edge (cd : G.ChainData n) {i : Fin cd.d} (hi : 0 < (i : ℕ)) :
    G.IsLink (cd.edge ⟨(i : ℕ) - 1, by omega⟩) (cd.vtx i.castSucc)
      (cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc) := by
  have h := cd.isLink_edge ⟨(i : ℕ) - 1, by omega⟩
  rw [cd.pred_succ_eq_castSucc hi] at h
  exact h.symm

/-- `edge i` joins `vtx i` to `vtx (i + 1)` (the field `link`, as `isLink_edge`). -/
lemma isLink_succ_edge (cd : G.ChainData n) (i : Fin cd.d) :
    G.IsLink (cd.edge i) (cd.vtx i.castSucc) (cd.vtx i.succ) := cd.isLink_edge i

/-- For `0 < i`, every edge of `G` at `vtx i` is `edge i` or `edge (i − 1)` (the field
`deg_two`, its two cases exchanged). -/
lemma deg_two_split (cd : G.ChainData n) {i : Fin cd.d} (hi : 0 < (i : ℕ)) :
    ∀ e x, G.IsLink e (cd.vtx i.castSucc) x →
      e = cd.edge i ∨ e = cd.edge ⟨(i : ℕ) - 1, by omega⟩ :=
  fun e x hlink => (cd.deg_two i hi e x hlink).symm

/-- Two vertices `vtx ⟨m, _⟩` and `vtx ⟨m', _⟩` of the chain with `m ≠ m'` are distinct
(`vtx_inj`). -/
lemma vtx_ne {m m' : ℕ} (cd : G.ChainData n) (hm : m < cd.d + 1) (hm' : m' < cd.d + 1)
    (hne : m ≠ m') : cd.vtx ⟨m, hm⟩ ≠ cd.vtx ⟨m', hm'⟩ :=
  fun he => hne (by have := congrArg Fin.val (cd.vtx_inj he); simpa using this)

/-- `vtx i ≠ vtx (i + 1)`, the `v ≠ a` of the split at `vtx i` (`vtx_ne`). -/
lemma castSucc_ne_succ (cd : G.ChainData n) (i : Fin cd.d) :
    cd.vtx i.castSucc ≠ cd.vtx i.succ := by
  rw [show i.castSucc = (⟨(i : ℕ), by omega⟩ : Fin (cd.d + 1)) from Fin.ext (by simp),
    show i.succ = (⟨(i : ℕ) + 1, by omega⟩ : Fin (cd.d + 1)) from Fin.ext (by simp)]
  exact cd.vtx_ne _ _ (by omega)

/-- For `0 < i`, `vtx i ≠ vtx (i − 1)`, the `v ≠ b` of the split at `vtx i` (`vtx_ne`). -/
lemma castSucc_ne_pred_castSucc (cd : G.ChainData n) {i : Fin cd.d} (hi : 0 < (i : ℕ)) :
    cd.vtx i.castSucc ≠ cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc := by
  rw [show i.castSucc = (⟨(i : ℕ), by omega⟩ : Fin (cd.d + 1)) from Fin.ext (by simp),
    show (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc
        = (⟨(i : ℕ) - 1, by omega⟩ : Fin (cd.d + 1)) from Fin.ext (by simp)]
  exact cd.vtx_ne _ _ (by omega)

/-- **The split at `vtx 1`** (a step of `lem:case-III-chain-discriminator`): for `d ≥ 2`, the
vertices `v₀`, `v₁` and `v₂` are distinct, and so are `edge 0` and `edge 1`; `edge 0` joins `v₁` to
`v₀`, `edge 1` joins `v₁` to `v₂`, and every edge of `G` at `v₁` is one of the two (`vtx_ne`,
`edge_inj`, `link`, `deg_two`). This is the split `(v, a, b, e_a, e_b) = (v₁, v₀, v₂, edge 0,
edge 1)` at which Case III splits off once; at `i = 1` the lemmas above give its neighbours the
other way round. -/
lemma splitOff_data_one (cd : G.ChainData n) (hd2 : 2 ≤ cd.d) :
    cd.vtx ⟨0, by omega⟩ ≠ cd.vtx ⟨1, by omega⟩ ∧ cd.vtx ⟨2, by omega⟩ ≠ cd.vtx ⟨1, by omega⟩ ∧
      cd.vtx ⟨2, by omega⟩ ≠ cd.vtx ⟨0, by omega⟩ ∧
      cd.edge ⟨0, by omega⟩ ≠ cd.edge ⟨1, by omega⟩ ∧
      G.IsLink (cd.edge ⟨0, by omega⟩) (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨0, by omega⟩) ∧
      G.IsLink (cd.edge ⟨1, by omega⟩) (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨2, by omega⟩) ∧
      ∀ e x, G.IsLink e (cd.vtx ⟨1, by omega⟩) x →
        e = cd.edge ⟨0, by omega⟩ ∨ e = cd.edge ⟨1, by omega⟩ :=
  ⟨cd.vtx_ne _ _ (by omega), cd.vtx_ne _ _ (by omega), cd.vtx_ne _ _ (by omega),
    fun h => absurd (congrArg Fin.val (cd.edge_inj h)) (by simp), (cd.link _).symm, cd.link _,
    fun e x hlink => cd.deg_two ⟨1, by omega⟩ (by simp) e x hlink⟩

/-! ### Removing an interior vertex

The split at `v = vtx i` (`0 < i`) of the previous section, read on `G_v = G − v`: `v` is not a
vertex of `G_v`, its neighbours `a = vtx (i + 1)` and `b = vtx (i − 1)` are, and every edge of `G`
is `edge i`, `edge (i − 1)` or an edge of `G_v`.
`PanelHingeFramework.chainData_interior_realization_hρGv` (`CaseIII/Realization.lean`) reads these
facts. -/

/-- `vtx i` is not a vertex of `G − vtx i`. -/
lemma notMem_vertexSet_removeVertex_castSucc (cd : G.ChainData n) (i : Fin cd.d) :
    cd.vtx i.castSucc ∉ V(G.removeVertex (cd.vtx i.castSucc)) := by
  rw [Graph.vertexSet_removeVertex]; exact fun h => h.2 rfl

/-- `vtx (i + 1)` is a vertex of `G − vtx i` (`vtx_mem` and `castSucc_ne_succ`). -/
lemma succ_mem_vertexSet_removeVertex_castSucc (cd : G.ChainData n) (i : Fin cd.d) :
    cd.vtx i.succ ∈ V(G.removeVertex (cd.vtx i.castSucc)) := by
  rw [Graph.vertexSet_removeVertex]
  exact ⟨cd.vtx_mem _, (cd.castSucc_ne_succ i).symm⟩

/-- For `0 < i`, `vtx (i − 1)` is a vertex of `G − vtx i` (`vtx_mem` and
`castSucc_ne_pred_castSucc`). -/
lemma pred_castSucc_mem_vertexSet_removeVertex_castSucc (cd : G.ChainData n) {i : Fin cd.d}
    (hi : 0 < (i : ℕ)) :
    cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc ∈
      V(G.removeVertex (cd.vtx i.castSucc)) := by
  rw [Graph.vertexSet_removeVertex]
  exact ⟨cd.vtx_mem _, fun h => cd.castSucc_ne_pred_castSucc hi h.symm⟩

/-- **The edges of `G` at and away from an interior vertex** (`0 < i`): if `G.IsLink e u w`, then
`e = edge i`, `e = edge (i − 1)`, or `e` joins `u` and `w` in `G − vtx i`. If `u` or `w` is
`vtx i`, `deg_two_split` names the edge; otherwise it is a link of `G − vtx i`. -/
lemma isLink_eq_succ_or_pred_or_removeVertex (cd : G.ChainData n) {i : Fin cd.d} (hi : 0 < (i : ℕ))
    {e : β} {u w : α} (hlink : G.IsLink e u w) :
    e = cd.edge i ∨ e = cd.edge ⟨(i : ℕ) - 1, by omega⟩ ∨
      (G.removeVertex (cd.vtx i.castSucc)).IsLink e u w := by
  by_cases hu : u = cd.vtx i.castSucc
  · subst hu; rcases cd.deg_two_split hi e w hlink with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · by_cases hw : w = cd.vtx i.castSucc
    · subst hw; rcases cd.deg_two_split hi e u hlink.symm with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Graph.removeVertex_isLink.mpr ⟨hlink, hu, hw⟩))

/-! ### The cycle `shiftPerm` of KT eq. (6.54)

For `2 ≤ i ≤ d − 1`, Case III builds its `i`-th framework on `Gᵢ = G_{vᵢ}^{vᵢ₋₁vᵢ₊₁}`. Katoh and
Tanigawa's isomorphism `ρᵢ` from `Gᵢ` to `G₁ = G_{v₁}^{v₀v₂}` maps `vₗ` to `vₗ₊₁` for
`1 ≤ l ≤ i − 1` and fixes the other vertices (KT eq. (6.54), p. 694). `shiftPerm i` is the
permutation of `α` that agrees with `ρᵢ` and maps `vᵢ` to `v₁`: the cycle
`v₁ ↦ v₂ ↦ ⋯ ↦ vᵢ ↦ v₁`, the `σᵢ` of `case-iii.tex`, as `List.formPerm` of
`shiftCycle i = [v₁, …, vᵢ]`. At `i = 2` it is the transposition of `v₁` and `v₂`. -/

/-- The list `[vtx 1, …, vtx i]`, the cycle of `shiftPerm i`, for `i : Fin (cd.d + 1)`. -/
def shiftCycle (cd : G.ChainData n) (i : Fin (cd.d + 1)) : List α :=
  List.ofFn fun j : Fin (i : ℕ) => cd.vtx ⟨(j : ℕ) + 1, by omega⟩

@[simp] lemma length_shiftCycle (cd : G.ChainData n) (i : Fin (cd.d + 1)) :
    (cd.shiftCycle i).length = (i : ℕ) := by simp [shiftCycle]

lemma getElem_shiftCycle (cd : G.ChainData n) (i : Fin (cd.d + 1)) (j : ℕ)
    (hj : j < (cd.shiftCycle i).length) :
    (cd.shiftCycle i)[j] = cd.vtx ⟨j + 1, by simp only [length_shiftCycle] at hj; omega⟩ := by
  simp only [shiftCycle, List.getElem_ofFn]

/-- The list `shiftCycle i` has no repeated vertices, as those of the chain are distinct. -/
lemma nodup_shiftCycle (cd : G.ChainData n) (i : Fin (cd.d + 1)) : (cd.shiftCycle i).Nodup := by
  rw [shiftCycle, List.nodup_ofFn]
  intro a b hab
  have := cd.vtx_inj hab
  simpa [Fin.ext_iff] using this

/-- `vtx m` lies on `shiftCycle i = [vtx 1, …, vtx i]` if and only if `1 ≤ m ≤ i`, as the vertices
of the chain are distinct. -/
lemma vtx_mem_shiftCycle_iff (cd : G.ChainData n) (i : Fin (cd.d + 1)) {m : ℕ} (hm : m < cd.d + 1) :
    cd.vtx ⟨m, hm⟩ ∈ cd.shiftCycle i ↔ 1 ≤ m ∧ m ≤ (i : ℕ) := by
  rw [shiftCycle, List.mem_ofFn]
  constructor
  · rintro ⟨j, hj⟩
    have := cd.vtx_inj hj
    simp only [Fin.mk.injEq] at this
    omega
  · rintro ⟨hm1, hmi⟩
    exact ⟨⟨m - 1, by omega⟩, by congr 1; simp only [Fin.mk.injEq]; omega⟩

/-- A vertex `x` lies on `shiftCycle i` if and only if `x = vtx m` for some `1 ≤ m ≤ i`. -/
lemma mem_shiftCycle (cd : G.ChainData n) (i : Fin (cd.d + 1)) {x : α} :
    x ∈ cd.shiftCycle i ↔ ∃ m, ∃ h : m < cd.d + 1, 1 ≤ m ∧ m ≤ (i : ℕ) ∧ x = cd.vtx ⟨m, h⟩ := by
  rw [shiftCycle, List.mem_ofFn]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨(j : ℕ) + 1, by omega, by omega, by omega, rfl⟩
  · rintro ⟨m, hm, hm1, hmi, rfl⟩
    exact ⟨⟨m - 1, by omega⟩, by congr 1; simp only [Fin.mk.injEq]; omega⟩

-- The vertex-side `DecidableEq α` is needed only by the `shiftPerm` block (`List.formPerm`); it is
-- `section`-scoped rather than turned off by a bare `omit` below, because a bare `omit [C]` does
-- *not* remove `C` from the section's variable list — so a later `variable [C]` puts a *second copy
-- in scope* instead of un-omitting the first, which is what `linter.overlappingInstances` reports.
-- (It counts copies in scope, not arguments in the signature: the duplicate never reached any
-- telescope, so this scoping is hygiene — TACTICS-QUIRKS § 108.)
section ShiftPerm

variable [DecidableEq α]

/-- **The cycle `σᵢ` extending KT's `ρᵢ`** (KT eq. (6.54), p. 694): the permutation
`vtx 1 ↦ vtx 2 ↦ ⋯ ↦ vtx i ↦ vtx 1` of `α`, fixing every other vertex; `List.formPerm` of
`shiftCycle i`. -/
def shiftPerm (cd : G.ChainData n) (i : Fin (cd.d + 1)) : Equiv.Perm α :=
  (cd.shiftCycle i).formPerm

/-- `shiftPerm i` fixes every vertex not on `shiftCycle i`. -/
lemma shiftPerm_apply_off (cd : G.ChainData n) (i : Fin (cd.d + 1)) {x : α}
    (hx : x ∉ cd.shiftCycle i) : cd.shiftPerm i x = x :=
  List.formPerm_apply_of_notMem hx

/-- `shiftPerm i` fixes `vtx m` when `m = 0` or `i < m`. -/
lemma shiftPerm_apply_vtx_off (cd : G.ChainData n) (i : Fin (cd.d + 1)) {m : ℕ} (hm : m < cd.d + 1)
    (hoff : m = 0 ∨ (i : ℕ) < m) : cd.shiftPerm i (cd.vtx ⟨m, hm⟩) = cd.vtx ⟨m, hm⟩ :=
  cd.shiftPerm_apply_off i fun hmem => by
    rw [cd.vtx_mem_shiftCycle_iff i hm] at hmem; omega

/-- `shiftPerm i` maps `vtx j` to `vtx (j + 1)` for `1 ≤ j < i`, as `ρᵢ` does (KT eq. (6.54)). -/
lemma shiftPerm_apply_interior (cd : G.ChainData n) (i : Fin (cd.d + 1)) {j : ℕ}
    (hj1 : 1 ≤ j) (hji : j < (i : ℕ)) :
    cd.shiftPerm i (cd.vtx ⟨j, by omega⟩) = cd.vtx ⟨j + 1, by omega⟩ := by
  have hlen : (cd.shiftCycle i).length = (i : ℕ) := cd.length_shiftCycle i
  have hsucc : (j - 1) + 1 < (cd.shiftCycle i).length := by omega
  have hget : (cd.shiftCycle i)[j - 1]'(by omega) = cd.vtx ⟨j, by omega⟩ := by
    rw [cd.getElem_shiftCycle i (j - 1) (by omega)]; congr 1; simp only [Fin.mk.injEq]; omega
  have hget' : (cd.shiftCycle i)[(j - 1) + 1]'hsucc = cd.vtx ⟨j + 1, by omega⟩ := by
    rw [cd.getElem_shiftCycle i ((j - 1) + 1) hsucc]; congr 1; simp only [Fin.mk.injEq]; omega
  rw [shiftPerm, ← hget,
    List.formPerm_apply_lt_getElem _ (cd.nodup_shiftCycle i) (j - 1) hsucc, hget']

/-- For `1 ≤ i`, `shiftPerm i` maps `vtx i` to `vtx 1`; `vtx i` is not a vertex of `Gᵢ`, so this
value extends KT's `ρᵢ`. -/
lemma shiftPerm_vtx_top (cd : G.ChainData n) {i : Fin (cd.d + 1)} (hi : 1 ≤ (i : ℕ)) :
    cd.shiftPerm i (cd.vtx ⟨(i : ℕ), by omega⟩) = cd.vtx ⟨1, by omega⟩ := by
  have hlen : (cd.shiftCycle i).length = (i : ℕ) := cd.length_shiftCycle i
  have hidx : (i : ℕ) - 1 < (cd.shiftCycle i).length := by omega
  have hget : (cd.shiftCycle i)[(i : ℕ) - 1]'hidx = cd.vtx ⟨(i : ℕ), by omega⟩ := by
    rw [cd.getElem_shiftCycle i ((i : ℕ) - 1) hidx]; congr 1; simp only [Fin.mk.injEq]; omega
  have hmod : (((i : ℕ) - 1) + 1) % (cd.shiftCycle i).length = 0 := by
    have he : ((i : ℕ) - 1) + 1 = (i : ℕ) := by omega
    rw [hlen, he, Nat.mod_self]
  rw [shiftPerm, ← hget,
    List.formPerm_apply_getElem _ (cd.nodup_shiftCycle i) ((i : ℕ) - 1) hidx,
    cd.getElem_shiftCycle i ((((i : ℕ) - 1) + 1) % (cd.shiftCycle i).length) (by rw [hmod]; omega)]
  congr 1
  simp only [hmod]

/-! ### The inverse of `shiftPerm`

`lem:case-III-chain-relabel-rows` renames the rows of `R(G₁, q)` along `σᵢ⁻¹ = (shiftPerm i)⁻¹`,
with the normals `qᵢ = q ∘ σᵢ` (KT eqs. (6.55) and (6.62), pp. 694–696): the form `f` becomes
`S ↦ f(S ∘ σᵢ⁻¹)`. These lemmas give the values of `(shiftPerm i)⁻¹`, each from the matching
value of `shiftPerm i` (`Equiv.Perm.inv_eq_iff_eq`). -/

/-- `(shiftPerm i)⁻¹` maps `vtx (j + 1)` to `vtx j` for `1 ≤ j < i` (`shiftPerm_apply_interior`). -/
lemma shiftPerm_inv_apply_interior (cd : G.ChainData n) (i : Fin (cd.d + 1)) {j : ℕ}
    (hj1 : 1 ≤ j) (hji : j < (i : ℕ)) :
    (cd.shiftPerm i)⁻¹ (cd.vtx ⟨j + 1, by omega⟩) = cd.vtx ⟨j, by omega⟩ := by
  rw [Equiv.Perm.inv_eq_iff_eq, cd.shiftPerm_apply_interior i hj1 hji]

/-- `(shiftPerm i)⁻¹` fixes `vtx m` when `m = 0` or `i < m` (`shiftPerm_apply_vtx_off`). -/
lemma shiftPerm_inv_apply_vtx_off (cd : G.ChainData n) (i : Fin (cd.d + 1)) {m : ℕ}
    (hm : m < cd.d + 1) (hoff : m = 0 ∨ (i : ℕ) < m) :
    (cd.shiftPerm i)⁻¹ (cd.vtx ⟨m, hm⟩) = cd.vtx ⟨m, hm⟩ := by
  rw [Equiv.Perm.inv_eq_iff_eq, cd.shiftPerm_apply_vtx_off i hm hoff]

/-! ### The normals `qᵢ = q ∘ σᵢ`

The `i`-th framework of Case III has the normals `qᵢ = q ∘ σᵢ`, where `σᵢ = shiftPerm i`
(`case-iii.tex`; KT eq. (6.55), p. 694). For `q : α × γ → K`, which gives each vertex the
coordinates of its normal, these lemmas give `qᵢ` at the vertices that the split at `vtx i`
names. At `i = 2`, `σ₂` is the transposition of `v₁` and `v₂`. -/

/-- **`qᵢ` at `vtx (i + 1)`**: for `i : Fin cd.d`, `σᵢ` fixes `vtx (i + 1)`, so `qᵢ` is `q` there.
`PanelHingeFramework.chainData_interior_realization_hρGv` reads it. -/
theorem seedShift_succ_castSucc (cd : G.ChainData n) (i : Fin cd.d)
    {γ : Type*} {K : Type*} (q : α × γ → K) :
    (fun j => q (cd.shiftPerm i.castSucc (cd.vtx i.succ), j))
      = (fun j => q (cd.vtx i.succ, j)) := by
  rw [show cd.vtx i.succ = cd.vtx ⟨(i : ℕ) + 1, by have := i.isLt; omega⟩ from
    congrArg cd.vtx (Fin.ext (by simp only [Fin.val_succ]))]
  rw [cd.shiftPerm_apply_vtx_off i.castSucc (by have := i.isLt; omega)
    (Or.inr (by simp only [Fin.val_castSucc]; omega))]

/-- **`qᵢ` at `vtx (i − 1)`**: for `2 ≤ i`, `σᵢ` maps `vtx (i − 1)` to `vtx i` (KT eq. (6.54)), so
`qᵢ` at `vtx (i − 1)` is `q` at `vtx i`. `PanelHingeFramework.chainData_interior_realization_hρGv`
reads it. -/
theorem seedShift_pred_castSucc (cd : G.ChainData n) {i : Fin cd.d} (h2i : 2 ≤ (i : ℕ))
    {γ : Type*} {K : Type*} (q : α × γ → K) :
    (fun j => q (cd.shiftPerm i.castSucc
        (cd.vtx (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc), j))
      = (fun j => q (cd.vtx i.castSucc, j)) := by
  rw [show (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc
      = (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin (cd.d + 1)) from
    Fin.ext (by simp only [Fin.val_castSucc])]
  rw [cd.shiftPerm_apply_interior i.castSucc (by omega) (by simp only [Fin.val_castSucc]; omega),
    show (⟨((i : ℕ) - 1) + 1, by have := i.isLt; omega⟩ : Fin (cd.d + 1)) = i.castSucc from
      Fin.ext (by simp only [Fin.val_castSucc]; omega)]

end ShiftPerm

/-! ### `shiftPerm` as a product of transpositions

The Case III proofs at general `d` in `CaseIII/Relabel/` rename the rows of a framework along
`σᵢ = shiftPerm i` one transposition of consecutive vertices of the chain at a time. A step
`(v, a, c)` exchanges a vertex `a` of degree two with `v`, where `c` is the other neighbour of `a`
(`BodyHingeFramework.wstep`, iterated by `BodyHingeFramework.wstep_foldl_mem_span_rigidityRows`,
`CaseIII/Relabel/Basic.lean`). This section lists the steps in two orders, names the graph of
each step, and shows that the transpositions multiply to `shiftPerm i`. -/

/-- The steps `[(v₂, v₁, v₀), (v₃, v₂, v₁), …, (vᵢ, vᵢ₋₁, vᵢ₋₂)]` of `shiftPerm i`, for
`i : Fin (cd.d + 1)`: for `s < i − 1`, the step `(v, a, c) = (vₛ₊₂, vₛ₊₁, vₛ)` moves `vₛ₊₁` to
`vₛ₊₂`, past `vₛ`. A `List.foldr` over it applies the first step last. -/
def shiftBodyList (cd : G.ChainData n) (i : Fin (cd.d + 1)) : List (α × α × α) :=
  List.ofFn fun s : Fin ((i : ℕ) - 1) =>
    (cd.vtx ⟨(s : ℕ) + 2, by omega⟩, cd.vtx ⟨(s : ℕ) + 1, by omega⟩, cd.vtx ⟨(s : ℕ), by omega⟩)

@[simp] lemma length_shiftBodyList (cd : G.ChainData n) (i : Fin (cd.d + 1)) :
    (cd.shiftBodyList i).length = (i : ℕ) - 1 := by simp [shiftBodyList]

lemma getElem_shiftBodyList (cd : G.ChainData n) (i : Fin (cd.d + 1)) (s : ℕ)
    (hs : s < (cd.shiftBodyList i).length) :
    (cd.shiftBodyList i)[s] =
      (cd.vtx ⟨s + 2, by simp only [length_shiftBodyList] at hs; omega⟩,
        cd.vtx ⟨s + 1, by simp only [length_shiftBodyList] at hs; omega⟩,
        cd.vtx ⟨s, by simp only [length_shiftBodyList] at hs; omega⟩) := by
  simp only [shiftBodyList, List.getElem_ofFn]

/-! ### The steps of `shiftPerm` in ascending order

The same transpositions, as the steps `(v, a, c) = (vₛ₊₁, vₛ₊₂, vₛ₊₃)` for `s < i − 1`: each moves
`vₛ₊₂` to `vₛ₊₁`, past `vₛ₊₃`. A `List.foldl` over them
(`BodyHingeFramework.wstep_foldl_mem_span_rigidityRows`) renames from `G − v₁` up to `G − vᵢ`. -/

/-- The steps `[(v₁, v₂, v₃), (v₂, v₃, v₄), …, (vᵢ₋₁, vᵢ, vᵢ₊₁)]`, for `i : Fin cd.d`: for
`s < i − 1`, the step `(vₛ₊₁, vₛ₊₂, vₛ₊₃)` moves `vₛ₊₂` to `vₛ₊₁`, past `vₛ₊₃`. -/
def shiftBodyListAsc (cd : G.ChainData n) (i : Fin cd.d) : List (α × α × α) :=
  List.ofFn fun s : Fin ((i : ℕ) - 1) =>
    (cd.vtx ⟨(s : ℕ) + 1, by have := i.2; omega⟩, cd.vtx ⟨(s : ℕ) + 2, by have := i.2; omega⟩,
      cd.vtx ⟨(s : ℕ) + 3, by have := i.2; omega⟩)

@[simp] lemma length_shiftBodyListAsc (cd : G.ChainData n) (i : Fin cd.d) :
    (cd.shiftBodyListAsc i).length = (i : ℕ) - 1 := by simp [shiftBodyListAsc]

lemma getElem_shiftBodyListAsc (cd : G.ChainData n) (i : Fin cd.d) (s : ℕ)
    (hs : s < (cd.shiftBodyListAsc i).length) :
    (cd.shiftBodyListAsc i)[s] =
      (cd.vtx ⟨s + 1, by have := i.2; simp only [length_shiftBodyListAsc] at hs; omega⟩,
        cd.vtx ⟨s + 2, by have := i.2; simp only [length_shiftBodyListAsc] at hs; omega⟩,
        cd.vtx ⟨s + 3, by have := i.2; simp only [length_shiftBodyListAsc] at hs; omega⟩) := by
  simp only [shiftBodyListAsc, List.getElem_ofFn]

/-! ### The graphs `G − vₛ₊₁` of the steps

The moves along the chain rename rows through frameworks on the graphs
`shiftBodyGraph s = G − vₛ₊₁`, from `G − v₁` up to `G − vᵢ`. The frameworks on these graphs are
built in `CaseIII/Relabel/Chain.lean` (`shiftBodyFrameworkAsc`). -/

/-- The graph `G − vₛ₊₁` of the step `s`, for `s + 1 ≤ d`. -/
def shiftBodyGraph (cd : G.ChainData n) {s : ℕ} (hs : s + 1 < cd.d + 1) : Graph α β :=
  G.removeVertex (cd.vtx ⟨s + 1, hs⟩)

/-- **`shiftPerm i` is the product of the transpositions of its steps**:
`shiftPerm i = swap v₁ v₂ * swap v₂ v₃ * ⋯ * swap vᵢ₋₁ vᵢ`, the transposition `swap a v` of each
step `(v, a, c)` of `shiftBodyList i` in order. It is `List.formPerm_eq_prod_zipWith_swap_tail`
for `shiftCycle i`, whose consecutive pairs are those of the steps. So the composite of the
renamings of the steps is the renaming along `shiftPerm i`. -/
lemma shiftPerm_eq_prod_map_swap_shiftBodyList [DecidableEq α] (cd : G.ChainData n)
    (i : Fin (cd.d + 1)) :
    cd.shiftPerm i
      = ((cd.shiftBodyList i).map (fun b => Equiv.swap b.2.1 b.1)).prod := by
  rw [shiftPerm, List.formPerm_eq_prod_zipWith_swap_tail]
  congr 1
  refine List.ext_getElem (by simp [shiftCycle, shiftBodyList]) fun m h₁ h₂ => ?_
  simp only [List.getElem_zipWith, List.getElem_map, getElem_shiftBodyList,
    List.getElem_tail, getElem_shiftCycle]

/-- **`shiftPerm i` is the product of the transpositions of its ascending steps**: for
`i : Fin cd.d`, `shiftPerm i` is the product of the transpositions `swap a v` of the steps
`(v, a, c)` of `shiftBodyListAsc i` in order. They are those of `shiftBodyList i`, with the two
vertices exchanged (`Equiv.swap_comm`), so this is `shiftPerm_eq_prod_map_swap_shiftBodyList`. -/
lemma shiftPerm_eq_prod_map_swap_shiftBodyListAsc [DecidableEq α] (cd : G.ChainData n)
    (i : Fin cd.d) :
    cd.shiftPerm i.castSucc
      = ((cd.shiftBodyListAsc i).map (fun b => Equiv.swap b.2.1 b.1)).prod := by
  rw [cd.shiftPerm_eq_prod_map_swap_shiftBodyList i.castSucc]
  congr 1
  refine List.ext_getElem (by simp only [List.length_map, length_shiftBodyList,
    length_shiftBodyListAsc, Fin.val_castSucc]) fun m h₁ h₂ => ?_
  simp only [List.getElem_map, getElem_shiftBodyList, getElem_shiftBodyListAsc]
  exact Equiv.swap_comm _ _

/-! ### The permutation `shiftEdgePerm` of the labels (KT eq. (6.54) on edges)

For `2 ≤ i ≤ d − 1`, `shiftPerm i` maps `Gᵢ = G.splitOff vᵢ vᵢ₊₁ vᵢ₋₁ e₀` onto
`G₁ = G.splitOff v₁ v₂ v₀ e₀`, and `shiftEdgePerm i` is the permutation of the labels that goes
with it, extending KT's `ρᵢ` on edges. It maps the edge `edge 0` (`v₀v₁`) of `Gᵢ` to the new edge
`e₀` (`v₀v₂`) of `G₁`, the new edge `e₀` (`vᵢ₋₁vᵢ₊₁`) of `Gᵢ` to `edge i` (`vᵢvᵢ₊₁`), and
`edge j` to `edge (j + 1)` for `1 ≤ j ≤ i − 2`. It is `List.formPerm` of
`shiftEdgeCycle i = [edge 0, e₀, edge i, edge 1, …, edge (i − 1)]`, so it also maps `edge i` to
`edge 1` and `edge (i − 1)` to `edge 0`, the two edges at `vᵢ`, which are not edges of `Gᵢ`; it
fixes every other label. -/

-- The edge-relabel layer is on the *edge* type only; the vertex-side `DecidableEq α` from the
-- `shiftPerm` section above is out of scope here. `DecidableEq β` is introduced just before
-- `shiftEdgePerm` (only `List.formPerm` needs it; the cycle list + its `Nodup` do not).

/-- The list `[edge 0, e₀, edge i, edge 1, …, edge (i − 1)]`, the cycle of `shiftEdgePerm i`, for
`i : Fin cd.d`. -/
def shiftEdgeCycle (cd : G.ChainData n) (i : Fin cd.d) : List β :=
  cd.edge ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt⟩ :: cd.e₀ :: cd.edge i ::
    List.ofFn fun j : Fin ((i : ℕ) - 1) =>
      cd.edge ⟨(j : ℕ) + 1, lt_of_le_of_lt (by have := j.isLt; omega) i.isLt⟩

/-- For `0 < i`, `shiftEdgeCycle i` has `i + 2` entries. -/
lemma length_shiftEdgeCycle (cd : G.ChainData n) (i : Fin cd.d) (hi : 0 < (i : ℕ)) :
    (cd.shiftEdgeCycle i).length = (i : ℕ) + 2 := by
  simp only [shiftEdgeCycle, List.length_cons, List.length_ofFn]
  omega

lemma getElem_shiftEdgeCycle_zero (cd : G.ChainData n) (i : Fin cd.d)
    (hl : 0 < (cd.shiftEdgeCycle i).length) :
    (cd.shiftEdgeCycle i)[0] = cd.edge ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt⟩ := rfl

lemma getElem_shiftEdgeCycle_one (cd : G.ChainData n) (i : Fin cd.d)
    (hl : 1 < (cd.shiftEdgeCycle i).length) :
    (cd.shiftEdgeCycle i)[1] = cd.e₀ := rfl

lemma getElem_shiftEdgeCycle_two (cd : G.ChainData n) (i : Fin cd.d)
    (hl : 2 < (cd.shiftEdgeCycle i).length) :
    (cd.shiftEdgeCycle i)[2] = cd.edge i := rfl

/-- The entry `k + 3` of `shiftEdgeCycle i` is `edge (k + 1)`. -/
lemma getElem_shiftEdgeCycle_tail (cd : G.ChainData n) (i : Fin cd.d) (k : ℕ)
    (hk : k + 3 < (cd.shiftEdgeCycle i).length) :
    (cd.shiftEdgeCycle i)[k + 3] = cd.edge ⟨k + 1, by
      simp only [shiftEdgeCycle, List.length_cons, List.length_ofFn] at hk
      have := i.isLt; omega⟩ := by
  simp only [shiftEdgeCycle, List.getElem_cons_succ, List.getElem_ofFn]

/-- The label `e₀` is none of the edges of the chain, as it is not an edge of `G`. -/
lemma e₀_ne_edge (cd : G.ChainData n) (j : Fin cd.d) : cd.e₀ ≠ cd.edge j :=
  fun h => cd.e₀_fresh (h ▸ (cd.isLink_edge j).edge_mem)

/-- For `0 < i`, `shiftEdgeCycle i` has no repeated labels: the edges of the chain are distinct
(`edge_inj`), and `e₀` is none of them (`e₀_ne_edge`). -/
lemma nodup_shiftEdgeCycle (cd : G.ChainData n) (i : Fin cd.d) (hi : 0 < (i : ℕ)) :
    (cd.shiftEdgeCycle i).Nodup := by
  rw [shiftEdgeCycle]
  -- The full list is `edge 0 :: e₀ :: edge i :: (edge 1, …, edge (i−1))`.
  refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, ?_⟩⟩⟩
  · -- `edge 0 ∉ e₀ :: edge i :: tail`.
    simp only [List.mem_cons, List.mem_ofFn, not_or]
    refine ⟨fun h => (cd.e₀_ne_edge _) h.symm, fun h => ?_, ?_⟩
    · have := congrArg Fin.val (cd.edge_inj h); simp only at this; omega
    · rintro ⟨j, hj⟩
      have := congrArg Fin.val (cd.edge_inj hj); simp only at this; omega
  · -- `e₀ ∉ edge i :: tail`.
    simp only [List.mem_cons, List.mem_ofFn, not_or]
    exact ⟨cd.e₀_ne_edge _, fun ⟨j, hj⟩ => cd.e₀_ne_edge _ hj.symm⟩
  · -- `edge i ∉ tail` (`tail = edge 1, …, edge (i−1)`, all indices `< i`).
    simp only [List.mem_ofFn, not_exists]
    rintro j hj
    have := congrArg Fin.val (cd.edge_inj hj); simp only at this; omega
  · -- The tail `edge 1, …, edge (i−1)` is nodup (distinct indices via `edge_inj`).
    rw [List.nodup_ofFn]
    intro a b hab
    have := congrArg Fin.val (cd.edge_inj hab)
    simpa [Fin.ext_iff] using this

variable [DecidableEq β]

/-- **The permutation of the labels extending KT's `ρᵢ`** (KT eq. (6.54), p. 694): the cycle
`edge 0 ↦ e₀ ↦ edge i ↦ edge 1 ↦ ⋯ ↦ edge (i − 1) ↦ edge 0`, fixing every other label;
`List.formPerm` of `shiftEdgeCycle i`. -/
def shiftEdgePerm (cd : G.ChainData n) (i : Fin cd.d) : Equiv.Perm β :=
  (cd.shiftEdgeCycle i).formPerm

/-- `shiftEdgePerm i` fixes every label not on `shiftEdgeCycle i`. -/
lemma shiftEdgePerm_apply_off (cd : G.ChainData n) (i : Fin cd.d) {e : β}
    (he : e ∉ cd.shiftEdgeCycle i) : cd.shiftEdgePerm i e = e :=
  List.formPerm_apply_of_notMem he

/-- For `0 < i`, `shiftEdgePerm i` maps `edge 0` to `e₀`. -/
lemma shiftEdgePerm_apply_edge_zero (cd : G.ChainData n) (i : Fin cd.d) (hi : 0 < (i : ℕ)) :
    cd.shiftEdgePerm i (cd.edge ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt⟩) = cd.e₀ := by
  have hlen := cd.length_shiftEdgeCycle i hi
  have h1 : 0 + 1 < (cd.shiftEdgeCycle i).length := by rw [hlen]; omega
  rw [shiftEdgePerm, ← cd.getElem_shiftEdgeCycle_zero i (by rw [hlen]; omega),
    List.formPerm_apply_lt_getElem _ (cd.nodup_shiftEdgeCycle i hi) 0 h1,
    cd.getElem_shiftEdgeCycle_one i (by rw [hlen]; omega)]

/-- For `0 < i`, `shiftEdgePerm i` maps `e₀` to `edge i`. -/
lemma shiftEdgePerm_apply_e₀ (cd : G.ChainData n) (i : Fin cd.d) (hi : 0 < (i : ℕ)) :
    cd.shiftEdgePerm i cd.e₀ = cd.edge i := by
  have hlen := cd.length_shiftEdgeCycle i hi
  have h1 : 1 + 1 < (cd.shiftEdgeCycle i).length := by rw [hlen]; omega
  rw [shiftEdgePerm, ← cd.getElem_shiftEdgeCycle_one i (by rw [hlen]; omega),
    List.formPerm_apply_lt_getElem _ (cd.nodup_shiftEdgeCycle i hi) 1 h1,
    cd.getElem_shiftEdgeCycle_two i (by rw [hlen]; omega)]

/-- `shiftEdgePerm i` maps `edge j` to `edge (j + 1)` for `1 ≤ j ≤ i − 2`, as `ρᵢ` maps `vⱼ` to
`vⱼ₊₁` and `vⱼ₊₁` to `vⱼ₊₂` (KT eq. (6.54)). -/
lemma shiftEdgePerm_apply_edge_interior (cd : G.ChainData n) (i : Fin cd.d) {j : ℕ}
    (hj1 : 1 ≤ j) (hji : j + 1 < (i : ℕ)) :
    cd.shiftEdgePerm i (cd.edge ⟨j, by have := i.isLt; omega⟩)
      = cd.edge ⟨j + 1, by have := i.isLt; omega⟩ := by
  -- `edge j` sits at cycle position `(j − 1) + 3`; `formPerm` steps it to position `(j − 1) + 4`,
  -- which holds `edge ((j − 1) + 2) = edge (j + 1)` by the tail accessor at `k = (j − 1) + 1`.
  have hi1 : 0 < (i : ℕ) := by omega
  have hlen := cd.length_shiftEdgeCycle i hi1
  have hpos1 : ((j - 1) + 3) + 1 < (cd.shiftEdgeCycle i).length := by rw [hlen]; omega
  have hget : (cd.shiftEdgeCycle i)[(j - 1) + 3] = cd.edge ⟨j, by have := i.isLt; omega⟩ := by
    rw [cd.getElem_shiftEdgeCycle_tail i (j - 1) (by rw [hlen]; omega)]
    congr 1; simp only [Fin.mk.injEq]; omega
  have hstep := List.formPerm_apply_lt_getElem _ (cd.nodup_shiftEdgeCycle i hi1) ((j - 1) + 3) hpos1
  -- The successor entry `xs[(j−1)+4]` = `xs[((j−1)+1)+3]` = `edge ((j−1)+1+1) = edge (j+1)`.
  have hget' : (cd.shiftEdgeCycle i)[((j - 1) + 3) + 1]'hpos1
      = cd.edge ⟨(j - 1) + 1 + 1, by have := i.isLt; omega⟩ :=
    cd.getElem_shiftEdgeCycle_tail i ((j - 1) + 1) (by rw [hlen]; omega)
  rw [shiftEdgePerm, ← hget, hstep, hget']
  congr 1; simp only [Fin.mk.injEq]; omega

/-- For `1 < i`, `shiftEdgePerm i` maps `edge i` to `edge 1`. -/
lemma shiftEdgePerm_apply_edge_top (cd : G.ChainData n) (i : Fin cd.d) (hi : 1 < (i : ℕ)) :
    cd.shiftEdgePerm i (cd.edge i) = cd.edge ⟨1, by have := i.isLt; omega⟩ := by
  have hi0 : 0 < (i : ℕ) := by omega
  have hlen := cd.length_shiftEdgeCycle i hi0
  have h2 : 2 + 1 < (cd.shiftEdgeCycle i).length := by rw [hlen]; omega
  -- `edge i` sits at position 2; `formPerm` steps it to position 3 = `edge 1` (tail at `k = 0`).
  have hget' : (cd.shiftEdgeCycle i)[0 + 3]'h2 = cd.edge ⟨1, by have := i.isLt; omega⟩ :=
    cd.getElem_shiftEdgeCycle_tail i 0 (by rw [hlen]; omega)
  rw [shiftEdgePerm, ← cd.getElem_shiftEdgeCycle_two i (by rw [hlen]; omega),
    List.formPerm_apply_lt_getElem _ (cd.nodup_shiftEdgeCycle i hi0) 2 h2, hget']

/-- For `1 < i`, `shiftEdgePerm i` maps `edge (i − 1)` to `edge 0`. -/
lemma shiftEdgePerm_apply_edge_pred (cd : G.ChainData n) (i : Fin cd.d) (hi : 1 < (i : ℕ)) :
    cd.shiftEdgePerm i (cd.edge ⟨(i : ℕ) - 1, by have := i.isLt; omega⟩)
      = cd.edge ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt⟩ := by
  have hi0 : 0 < (i : ℕ) := by omega
  have hlen := cd.length_shiftEdgeCycle i hi0
  -- `edge (i−1)` is the last cycle entry, at position `(i + 2) − 1 = i + 1`; `formPerm` wraps it
  -- to position 0 = `edge 0`. Use the cyclic `formPerm_apply_getElem` (mod the length).
  have hpos : ((i : ℕ) - 2) + 3 < (cd.shiftEdgeCycle i).length := by rw [hlen]; omega
  have hget : (cd.shiftEdgeCycle i)[((i : ℕ) - 2) + 3]'hpos
      = cd.edge ⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ := by
    rw [cd.getElem_shiftEdgeCycle_tail i ((i : ℕ) - 2) (by rw [hlen]; omega)]
    congr 1; simp only [Fin.mk.injEq]; omega
  have hmod : ((((i : ℕ) - 2) + 3) + 1) % (cd.shiftEdgeCycle i).length = 0 := by
    rw [hlen, show (((i : ℕ) - 2) + 3) + 1 = (i : ℕ) + 2 by omega, Nat.mod_self]
  rw [shiftEdgePerm, ← hget,
    List.formPerm_apply_getElem _ (cd.nodup_shiftEdgeCycle i hi0) (((i : ℕ) - 2) + 3) hpos]
  simp only [hmod]
  exact cd.getElem_shiftEdgeCycle_zero i (by rw [hlen]; omega)

variable [DecidableEq α]

/-! ### `shiftPerm` and `shiftEdgePerm` map `Gᵢ` onto `G₁` (KT eq. (6.54))

For `2 ≤ i ≤ d − 1`, with `Gᵢ = G.splitOff vᵢ vᵢ₊₁ vᵢ₋₁ e₀` and `G₁ = G.splitOff v₁ v₂ v₀ e₀`, an
edge `e` joins `x` and `y` in `Gᵢ` if and only if `shiftEdgePerm i e` joins `shiftPerm i x` and
`shiftPerm i y` in `G₁`: KT's isomorphism `ρᵢ` from `Gᵢ` to `G₁` (KT eq. (6.54), p. 694). At
`d = 3` and `i = 2`, `splitOff_isLink_relabel` is the same statement, with the transposition of `v`
and `a` and two labels for the new edges. `shiftPerm` is taken at `i.castSucc`, the index
`i : Fin cd.d` read as an index of the vertices. -/

/-- **`ρᵢ` maps the links of `Gᵢ` to links of `G₁`** (`1 < i`): if `e` joins `x` and `y` in `Gᵢ`,
then `shiftEdgePerm i e` joins `shiftPerm i x` and `shiftPerm i y` in `G₁`. The proof expands
`splitOff_isLink` on `Gᵢ`. An edge of `G` with an end on `[v₁, …, vᵢ]` is an edge of the chain
there (`deg_two`), whose image the values of `shiftEdgePerm` give; both permutations fix an edge
with no such end and its ends. -/
lemma splitOff_isLink_shiftRelabel_forward (cd : G.ChainData n) (i : Fin cd.d) (hi : 1 < (i : ℕ))
    {e : β} {x y : α}
    (h : (G.splitOff (cd.vtx i.castSucc) (cd.vtx i.succ)
        (cd.vtx (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc) cd.e₀).IsLink
          e x y) :
    (G.splitOff (cd.vtx (⟨1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc)
        (cd.vtx (⟨1, by have := i.isLt; omega⟩ : Fin cd.d).succ)
        (cd.vtx (⟨0, by have := i.isLt; omega⟩ : Fin cd.d).castSucc) cd.e₀).IsLink
      (cd.shiftEdgePerm i e) (cd.shiftPerm i.castSucc x) (cd.shiftPerm i.castSucc y) := by
  classical
  have hid : (i : ℕ) < cd.d := i.isLt
  have hicv : (i.castSucc : ℕ) = (i : ℕ) := rfl
  have he₀ : cd.e₀ ∉ E(G) := cd.e₀_fresh
  -- The candidate-split body / neighbours and the base-split body / neighbours as explicit
  -- `Fin (cd.d + 1)`-indexed vertices `vtx ⟨m,_⟩` (all `rfl` index coercions of castSucc / succ).
  have hci : cd.vtx i.castSucc = cd.vtx ⟨(i : ℕ), by omega⟩ := rfl
  have hca : cd.vtx i.succ = cd.vtx ⟨(i : ℕ) + 1, by omega⟩ := rfl
  have hcb : cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc
      = cd.vtx ⟨(i : ℕ) - 1, by omega⟩ := rfl
  have hb1 : cd.vtx (⟨1, by omega⟩ : Fin cd.d).castSucc = cd.vtx ⟨1, by omega⟩ := rfl
  have hb2 : cd.vtx (⟨1, by omega⟩ : Fin cd.d).succ = cd.vtx ⟨2, by omega⟩ := rfl
  have hb0 : cd.vtx (⟨0, by omega⟩ : Fin cd.d).castSucc = cd.vtx ⟨0, by omega⟩ := rfl
  rw [hb1, hb2, hb0]
  rw [splitOff_isLink, hci, hca, hcb] at h
  -- A chain vertex `vtx ⟨m,_⟩` is `≠ vtx 1` when `m ≠ 1` (via `vtx_inj`).
  have hvtx_ne1 : ∀ {m : ℕ} (hm : m < cd.d + 1), m ≠ 1 → cd.vtx ⟨m, hm⟩ ≠ cd.vtx ⟨1, by omega⟩ :=
    fun hm hm1 he => hm1 (by have := congrArg Fin.val (cd.vtx_inj he); simpa using this)
  -- Two chain vertices `vtx ⟨a,_⟩`, `vtx ⟨b,_⟩` differ when their indices differ.
  have hvtx_ne_of : ∀ {a b : ℕ} (ha : a < cd.d + 1) (hb : b < cd.d + 1), a ≠ b →
      cd.vtx ⟨a, ha⟩ ≠ cd.vtx ⟨b, hb⟩ :=
    fun ha hb hab he => hab (by have := congrArg Fin.val (cd.vtx_inj he); simpa using this)
  -- `ρ` value on each chain vertex `vtx ⟨m,_⟩` (top wrap / interior shift / off-cycle fixity).
  have hρtop : cd.shiftPerm i.castSucc (cd.vtx ⟨(i : ℕ), by omega⟩) = cd.vtx ⟨1, by omega⟩ :=
    cd.shiftPerm_vtx_top (i := i.castSucc) (by simp only [Fin.val_castSucc]; omega)
  have hρint : ∀ {m : ℕ} (hm : m < cd.d + 1) (hm1' : m + 1 < cd.d + 1), 1 ≤ m → m < (i : ℕ) →
      cd.shiftPerm i.castSucc (cd.vtx ⟨m, hm⟩) = cd.vtx ⟨m + 1, hm1'⟩ := by
    intro m hm hm1' hm1 hmi
    refine cd.shiftPerm_apply_interior i.castSucc (j := m) hm1 ?_
    simp only [Fin.val_castSucc]; omega
  have hρoff : ∀ {m : ℕ} (hm : m < cd.d + 1), m = 0 ∨ (i : ℕ) < m →
      cd.shiftPerm i.castSucc (cd.vtx ⟨m, hm⟩) = cd.vtx ⟨m, hm⟩ := by
    intro m hm hoff
    exact cd.shiftPerm_apply_vtx_off i.castSucc hm (by simpa only [Fin.val_castSucc] using hoff)
  -- The candidate split body `v = vtx i`; its neighbours `a = vtx (i+1)`, `b = vtx (i−1)`.
  rcases h with ⟨hne₀, hGe, hxv, hyv⟩ | ⟨rfl, _, _, _, _, hxy⟩
  · -- **Survivor branch**: `e ≠ e₀`, `G.IsLink e x y`, `x ≠ vtx i`, `y ≠ vtx i`.
    -- Whether either endpoint lies on the index-shift cycle `[vtx 1, …, vtx i]`.
    by_cases hcyc : x ∈ cd.shiftCycle i.castSucc ∨ y ∈ cd.shiftCycle i.castSucc
    · -- At least one endpoint (say `x'`) lies on the cycle ⇒ `e` is a chain edge at the interior
      -- vertex `x' = vtx m` (`1 ≤ m ≤ i−1`, since `x' ≠ vtx i`), so `e = edge (m−1)` or `edge m`.
      rw [splitOff_isLink]
      -- A `key` handling the on-cycle endpoint, applied to `(x, y)` or — via symmetry — `(y, x)`.
      have key : ∀ {x' y' : α}, G.IsLink e x' y' → x' ≠ cd.vtx ⟨(i : ℕ), by omega⟩ →
          y' ≠ cd.vtx ⟨(i : ℕ), by omega⟩ → x' ∈ cd.shiftCycle i.castSucc →
          (G.splitOff (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨2, by omega⟩) (cd.vtx ⟨0, by omega⟩)
            cd.e₀).IsLink (cd.shiftEdgePerm i e) (cd.shiftPerm i.castSucc x')
              (cd.shiftPerm i.castSucc y') := by
        intro x' y' hl hx'v hy'v hx'c
        -- `x' = vtx (m'+1)` with `0 ≤ m' ≤ i−2` (survivor ⇒ `m'+1 ≠ i`); write `m = m'+1`.
        obtain ⟨m, hm, hm1, hmi, rfl⟩ := (cd.mem_shiftCycle i.castSucc).mp hx'c
        rw [hicv] at hmi
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        have hm'i : m' + 1 < (i : ℕ) :=
          lt_of_le_of_ne hmi fun heq => hx'v (congrArg cd.vtx (by ext; exact heq))
        -- `ρ x' = ρ (vtx (m'+1)) = vtx (m'+2)` (interior, `1 ≤ m'+1 < i`).
        have hρx' : cd.shiftPerm i.castSucc (cd.vtx ⟨m' + 1, hm⟩) = cd.vtx ⟨m' + 2, by omega⟩ :=
          hρint hm (by omega) (by omega) (by omega)
        -- The edge `e` at the interior vertex `vtx (m'+1)` is `edge m'` or `edge (m'+1)`.
        have hldm : G.IsLink e (cd.vtx (⟨m' + 1, by omega⟩ : Fin cd.d).castSucc) y' := hl
        rcases cd.deg_two ⟨m' + 1, by omega⟩ (by simp) e y' hldm with hem | hem
        · -- `e = edge m'` (links `vtx m'`–`vtx (m'+1)`) ⇒ `y' = vtx m'`.
          rw [show (⟨(m' + 1) - 1, by omega⟩ : Fin cd.d) = ⟨m', by omega⟩ from rfl] at hem
          have hlp : G.IsLink (cd.edge ⟨m', by omega⟩) (cd.vtx ⟨m', by omega⟩)
              (cd.vtx ⟨m' + 1, by omega⟩) := cd.isLink_edge ⟨m', by omega⟩
          rw [hem] at hl
          have hy' : y' = cd.vtx ⟨m', by omega⟩ := by
            rcases hlp.eq_and_eq_or_eq_and_eq hl with ⟨hx, _⟩ | ⟨hx, _⟩
            · exact absurd hx (hvtx_ne_of (by omega) (by omega) (by omega))
            · exact hx.symm
          subst hy'
          rw [hem, hρx']
          by_cases hm2 : m' = 0
          · -- `m' = 0`: `σ (edge 0) = e₀`; base FRESH edge `vtx 2`–`vtx 0`.
            subst hm2
            rw [cd.shiftEdgePerm_apply_edge_zero i (by omega), hρoff (by omega) (Or.inl rfl)]
            exact Or.inr ⟨rfl, hvtx_ne1 (by omega) (by omega), hvtx_ne1 (by omega) (by omega),
              cd.vtx_mem _, cd.vtx_mem _, Or.inl ⟨rfl, rfl⟩⟩
          · -- `m' ≥ 1`: `σ (edge m') = edge (m'+1)`; base SURVIVOR `vtx (m'+2)`–`vtx (m'+1)`.
            rw [cd.shiftEdgePerm_apply_edge_interior i (j := m') (by omega) (by omega),
              hρint (m := m') (by omega) (by omega) (by omega) (by omega)]
            exact Or.inl ⟨(cd.e₀_ne_edge ⟨m' + 1, by omega⟩).symm,
              (cd.isLink_edge ⟨m' + 1, by omega⟩).symm,
              hvtx_ne1 (by omega) (by omega), hvtx_ne1 (by omega) (by omega)⟩
        · -- `e = edge (m'+1)` (links `vtx (m'+1)`–`vtx (m'+2)`) ⇒ `y' = vtx (m'+2)`; `m'+2 < i`.
          have hls : G.IsLink (cd.edge ⟨m' + 1, by omega⟩) (cd.vtx ⟨m' + 1, by omega⟩)
              (cd.vtx ⟨m' + 2, by omega⟩) := cd.isLink_edge ⟨m' + 1, by omega⟩
          rw [hem] at hl
          have hy' : y' = cd.vtx ⟨m' + 2, by omega⟩ := by
            rcases hls.eq_and_eq_or_eq_and_eq hl with ⟨_, hy⟩ | ⟨_, hx2⟩
            · exact hy.symm
            · exact absurd hx2 (hvtx_ne_of (by omega) (by omega) (by omega))
          subst hy'
          have hmi2 : m' + 2 < (i : ℕ) :=
            lt_of_le_of_ne (by omega) fun heq => hy'v (congrArg cd.vtx (by ext; exact heq))
          rw [hem, hρx', cd.shiftEdgePerm_apply_edge_interior i (j := m' + 1) (by omega) (by omega),
            hρint (m := m' + 2) (by omega) (by omega) (by omega) (by omega)]
          exact Or.inl ⟨(cd.e₀_ne_edge ⟨m' + 2, by omega⟩).symm, cd.isLink_edge ⟨m' + 2, by omega⟩,
            hvtx_ne1 (by omega) (by omega), hvtx_ne1 (by omega) (by omega)⟩
      rcases hcyc with hx | hy
      · exact key hGe hxv hyv hx
      · exact (key hGe.symm hyv hxv hy).symm
    · -- Both endpoints off the cycle ⇒ `ρ`/`σ` fix the data; the edge survives the base split.
      rw [not_or] at hcyc
      obtain ⟨hxc, hyc⟩ := hcyc
      -- Helper: a chain vertex `vtx ⟨m,_⟩` with `1 ≤ m ≤ i` lies on the cycle.
      have hmem_of : ∀ {m : ℕ} (hm : m < cd.d + 1), 1 ≤ m → m ≤ (i : ℕ) →
          cd.vtx ⟨m, hm⟩ ∈ cd.shiftCycle i.castSucc := by
        intro m hm hm1 hmi
        exact (cd.vtx_mem_shiftCycle_iff i.castSucc hm).mpr
          ⟨hm1, by simp only [Fin.val_castSucc]; omega⟩
      have hσe : cd.shiftEdgePerm i e = e := by
        refine cd.shiftEdgePerm_apply_off i fun hmem => ?_
        -- `e ∈ shiftEdgeCycle` and `e ≠ e₀` ⇒ `e = edge m` for some `0 ≤ m ≤ i`, forcing an
        -- endpoint onto the cycle (or onto the deleted `vtx i`) — both impossible.
        rw [shiftEdgeCycle, List.mem_cons, List.mem_cons, List.mem_cons, List.mem_ofFn] at hmem
        rcases hmem with rfl | rfl | rfl | ⟨j, rfl⟩
        · -- `e = edge 0` links `vtx 0`–`vtx 1`; `vtx 1 ∈ cycle`.
          have hl : G.IsLink (cd.edge ⟨0, by omega⟩) (cd.vtx ⟨0, by omega⟩)
              (cd.vtx ⟨1, by omega⟩) := cd.isLink_edge ⟨0, by omega⟩
          rcases hl.eq_and_eq_or_eq_and_eq hGe with ⟨_, rfl⟩ | ⟨_, rfl⟩
          · exact hyc (hmem_of (by omega) (by omega) (by omega))
          · exact hxc (hmem_of (by omega) (by omega) (by omega))
        · exact hne₀ rfl
        · -- `e = edge i` links `vtx i`–`vtx (i+1)`; `vtx i` is the deleted body.
          have hl : G.IsLink (cd.edge i) (cd.vtx ⟨(i : ℕ), by omega⟩)
              (cd.vtx ⟨(i : ℕ) + 1, by omega⟩) := by
            have := cd.isLink_edge i; rwa [hci, hca] at this
          rcases hl.eq_and_eq_or_eq_and_eq hGe with ⟨rfl, _⟩ | ⟨rfl, _⟩
          · exact hxv rfl
          · exact hyv rfl
        · -- `e = edge (j+1)` (`1 ≤ j+1 ≤ i−1`) links `vtx (j+1)`–`vtx (j+2)`, both on the cycle.
          have hjlt := j.isLt
          have hl : G.IsLink (cd.edge ⟨(j : ℕ) + 1, by omega⟩) (cd.vtx ⟨(j : ℕ) + 1, by omega⟩)
              (cd.vtx ⟨(j : ℕ) + 2, by omega⟩) := cd.isLink_edge ⟨(j : ℕ) + 1, by omega⟩
          rcases hl.eq_and_eq_or_eq_and_eq hGe with ⟨_, rfl⟩ | ⟨_, rfl⟩
          · exact hyc (hmem_of (by omega) (by omega) (by omega))
          · exact hxc (hmem_of (by omega) (by omega) (by omega))
      have hρx : cd.shiftPerm i.castSucc x = x := cd.shiftPerm_apply_off i.castSucc hxc
      have hρy : cd.shiftPerm i.castSucc y = y := cd.shiftPerm_apply_off i.castSucc hyc
      rw [hσe, hρx, hρy]
      refine Or.inl ⟨hne₀, hGe, ?_, ?_⟩
      · intro he; rw [he] at hxc; exact hxc (hmem_of (m := 1) (by omega) le_rfl (by omega))
      · intro he; rw [he] at hyc; exact hyc (hmem_of (m := 1) (by omega) le_rfl (by omega))
  · -- **Fresh-edge branch**: `e = e₀`, `{x, y} = {vtx (i+1), vtx (i−1)}`.
    -- `σ e₀ = edge i`; `ρ (vtx (i+1)) = vtx (i+1)` (off); `ρ (vtx (i−1)) = vtx i`.
    have hσ : cd.shiftEdgePerm i cd.e₀ = cd.edge i := cd.shiftEdgePerm_apply_e₀ i (by omega)
    have hρa : cd.shiftPerm i.castSucc (cd.vtx ⟨(i : ℕ) + 1, by omega⟩)
        = cd.vtx ⟨(i : ℕ) + 1, by omega⟩ := hρoff (by omega) (Or.inr (by omega))
    have hρb : cd.shiftPerm i.castSucc (cd.vtx ⟨(i : ℕ) - 1, by omega⟩)
        = cd.vtx ⟨(i : ℕ), by omega⟩ := by
      rw [hρint (m := (i : ℕ) - 1) (by omega) (by omega) (by omega) (by omega)]
      congr 1; ext; simp only; omega
    -- The base-split link is `edge i` between `vtx (i+1)` and `vtx i` — a base survivor.
    have hlink : G.IsLink (cd.edge i) (cd.vtx ⟨(i : ℕ) + 1, by omega⟩)
        (cd.vtx ⟨(i : ℕ), by omega⟩) := by
      have hl := cd.isLink_edge i
      rw [hci, hca] at hl
      exact hl.symm
    rw [hσ]
    have hedge_ne₀ : cd.edge i ≠ cd.e₀ := fun he => he₀ (he ▸ (cd.isLink_edge i).edge_mem)
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hρa, hρb]
      exact Or.inl ⟨hedge_ne₀, hlink, hvtx_ne1 (by omega) (by omega),
        hvtx_ne1 (by omega) (by omega)⟩
    · rw [hρa, hρb]
      exact Or.inl ⟨hedge_ne₀, hlink.symm, hvtx_ne1 (by omega) (by omega),
        hvtx_ne1 (by omega) (by omega)⟩

/-- **The converse** (`1 < i`): if `shiftEdgePerm i e` joins `shiftPerm i x` and `shiftPerm i y`
in `G₁`, then `e` joins `x` and `y` in `Gᵢ`. The proof expands `splitOff_isLink` on `G₁`. If `x`
or `y` lies on `[v₁, …, vᵢ]`, its image is a vertex of the chain of degree two in `G`, so the
image of `e` is an edge of the chain there (`deg_two`), and the values of `shiftPerm` and
`shiftEdgePerm` give `e`, `x` and `y`; otherwise both permutations fix them. The new edge `e₀` of
`G₁` comes from `edge 0`. -/
lemma splitOff_isLink_shiftRelabel_backward (cd : G.ChainData n) (i : Fin cd.d) (hi : 1 < (i : ℕ))
    {e : β} {x y : α}
    (h : (G.splitOff (cd.vtx (⟨1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc)
        (cd.vtx (⟨1, by have := i.isLt; omega⟩ : Fin cd.d).succ)
        (cd.vtx (⟨0, by have := i.isLt; omega⟩ : Fin cd.d).castSucc) cd.e₀).IsLink
          (cd.shiftEdgePerm i e) (cd.shiftPerm i.castSucc x) (cd.shiftPerm i.castSucc y)) :
    (G.splitOff (cd.vtx i.castSucc) (cd.vtx i.succ)
        (cd.vtx (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc) cd.e₀).IsLink
      e x y := by
  classical
  have hid : (i : ℕ) < cd.d := i.isLt
  have he₀ : cd.e₀ ∉ E(G) := cd.e₀_fresh
  -- Bodies / neighbours of both splits as explicit `Fin (cd.d + 1)`-indexed vertices (`rfl`s).
  have hci : cd.vtx i.castSucc = cd.vtx ⟨(i : ℕ), by omega⟩ := rfl
  have hca : cd.vtx i.succ = cd.vtx ⟨(i : ℕ) + 1, by omega⟩ := rfl
  have hcb : cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc
      = cd.vtx ⟨(i : ℕ) - 1, by omega⟩ := rfl
  have hb1 : cd.vtx (⟨1, by omega⟩ : Fin cd.d).castSucc = cd.vtx ⟨1, by omega⟩ := rfl
  have hb2 : cd.vtx (⟨1, by omega⟩ : Fin cd.d).succ = cd.vtx ⟨2, by omega⟩ := rfl
  have hb0 : cd.vtx (⟨0, by omega⟩ : Fin cd.d).castSucc = cd.vtx ⟨0, by omega⟩ := rfl
  rw [splitOff_isLink, hci, hca, hcb]
  rw [splitOff_isLink, hb1, hb2, hb0] at h
  -- Vertex / edge distinctness helpers.
  have hvtx_ne_of : ∀ {a b : ℕ} (ha : a < cd.d + 1) (hb : b < cd.d + 1), a ≠ b →
      cd.vtx ⟨a, ha⟩ ≠ cd.vtx ⟨b, hb⟩ :=
    fun ha hb hab he => hab (by have := congrArg Fin.val (cd.vtx_inj he); simpa using this)
  have hvtx_nei : ∀ {m : ℕ} (hm : m < cd.d + 1), m ≠ (i : ℕ) →
      cd.vtx ⟨m, hm⟩ ≠ cd.vtx ⟨(i : ℕ), by omega⟩ := fun hm => hvtx_ne_of hm (by omega)
  -- `ρ`-action values (forward) on the chain vertices.
  have hρtop : cd.shiftPerm i.castSucc (cd.vtx ⟨(i : ℕ), by omega⟩) = cd.vtx ⟨1, by omega⟩ :=
    cd.shiftPerm_vtx_top (i := i.castSucc) (by simp only [Fin.val_castSucc]; omega)
  have hρint : ∀ {m : ℕ} (hm : m < cd.d + 1) (hm1' : m + 1 < cd.d + 1), 1 ≤ m → m < (i : ℕ) →
      cd.shiftPerm i.castSucc (cd.vtx ⟨m, hm⟩) = cd.vtx ⟨m + 1, hm1'⟩ := fun hm _ hm1 hmi =>
    cd.shiftPerm_apply_interior i.castSucc (j := _) hm1 (by simp only [Fin.val_castSucc]; omega)
  have hρoff : ∀ {m : ℕ} (hm : m < cd.d + 1), m = 0 ∨ (i : ℕ) < m →
      cd.shiftPerm i.castSucc (cd.vtx ⟨m, hm⟩) = cd.vtx ⟨m, hm⟩ := fun hm hoff =>
    cd.shiftPerm_apply_vtx_off i.castSucc hm (by simpa only [Fin.val_castSucc] using hoff)
  -- A chain vertex `vtx ⟨m,_⟩` with `1 ≤ m ≤ i` lies on the cycle.
  have hmem_of : ∀ {m : ℕ} (hm : m < cd.d + 1), 1 ≤ m → m ≤ (i : ℕ) →
      cd.vtx ⟨m, hm⟩ ∈ cd.shiftCycle i.castSucc := fun hm hm1 hmi =>
    (cd.vtx_mem_shiftCycle_iff i.castSucc hm).mpr ⟨hm1, by simp only [Fin.val_castSucc]; omega⟩
  rcases h with ⟨hσne₀, hGσe, hρx1, hρy1⟩ | ⟨hσe₀, _, _, _, _, hxy⟩
  · -- **Base survivor branch**: `σe ≠ e₀`, `G.IsLink (σe)(ρx)(ρy)`, `ρx ≠ vtx 1`, `ρy ≠ vtx 1`.
    -- `key`: the on-cycle pre-image endpoint `x'` (with `ρ x' ≠ vtx 1`, forcing it interior,
    -- and `ρ y' ≠ vtx 1`) gives the candidate-split link (survivor or fresh `e₀`).
    have key : ∀ {x' y' : α}, G.IsLink (cd.shiftEdgePerm i e)
        (cd.shiftPerm i.castSucc x') (cd.shiftPerm i.castSucc y') →
        cd.shiftPerm i.castSucc x' ≠ cd.vtx ⟨1, by omega⟩ →
        cd.shiftPerm i.castSucc y' ≠ cd.vtx ⟨1, by omega⟩ → x' ∈ cd.shiftCycle i.castSucc →
        (e ≠ cd.e₀ ∧ G.IsLink e x' y' ∧ x' ≠ cd.vtx ⟨(i : ℕ), by omega⟩ ∧
          y' ≠ cd.vtx ⟨(i : ℕ), by omega⟩) ∨
        (e = cd.e₀ ∧ ((x' = cd.vtx ⟨(i : ℕ) + 1, by omega⟩ ∧ y' = cd.vtx ⟨(i : ℕ) - 1, by omega⟩) ∨
          (x' = cd.vtx ⟨(i : ℕ) - 1, by omega⟩ ∧ y' = cd.vtx ⟨(i : ℕ) + 1, by omega⟩))) := by
      intro x' y' hl hρx'1 hρy'1 hx'c
      obtain ⟨m, hm, hm1, hmi, rfl⟩ := (cd.mem_shiftCycle i.castSucc).mp hx'c
      rw [show (i.castSucc : ℕ) = (i : ℕ) from rfl] at hmi
      -- `ρ x' = vtx 1` iff `m = i` (the top wrap); `hρx'1` forbids it, so `m < i`.
      have hmlt : m < (i : ℕ) := lt_of_le_of_ne hmi fun heq => hρx'1 (by
        rw [show (⟨m, hm⟩ : Fin (cd.d + 1)) = ⟨(i : ℕ), by omega⟩ from Fin.ext heq, hρtop])
      -- `ρ x' = vtx (m+1)` (interior, `2 ≤ m+1 ≤ i`); `σ e` is a `G`-chain edge at it.
      have hρx' : cd.shiftPerm i.castSucc (cd.vtx ⟨m, hm⟩) = cd.vtx ⟨m + 1, by omega⟩ :=
        hρint hm (by omega) hm1 hmlt
      rw [hρx'] at hl
      have hldm : G.IsLink (cd.shiftEdgePerm i e)
          (cd.vtx (⟨m + 1, by omega⟩ : Fin cd.d).castSucc) (cd.shiftPerm i.castSucc y') := hl
      rcases cd.deg_two ⟨m + 1, by omega⟩ (by simp) _ _ hldm with hσem | hσem
      · -- `σ e = edge m` (links `vtx m`–`vtx (m+1)`) ⇒ `ρ y' = vtx m`.
        rw [show (⟨(m + 1) - 1, by omega⟩ : Fin cd.d) = ⟨m, by omega⟩ from rfl] at hσem
        have hσy' : G.IsLink (cd.shiftEdgePerm i e) (cd.vtx ⟨m + 1, by omega⟩)
            (cd.vtx ⟨m, by omega⟩) := by rw [hσem]; exact (cd.isLink_edge ⟨m, by omega⟩).symm
        have hρy' : cd.shiftPerm i.castSucc y' = cd.vtx ⟨m, by omega⟩ :=
          (hσy'.right_unique hl).symm
        -- `m = 1` ⇒ `ρ y' = vtx 1`, contradicting `hρy'1`; so `m = m' + 1` with `1 ≤ m'`.
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        have hm'1 : 1 ≤ m' := by
          rcases Nat.eq_zero_or_pos m' with rfl | h2
          · exact absurd hρy' hρy'1
          · exact h2
        have hy' : y' = cd.vtx ⟨m', by omega⟩ := by
          have hρm1 : cd.shiftPerm i.castSucc (cd.vtx ⟨m', by omega⟩) = cd.vtx ⟨m' + 1, by omega⟩ :=
            hρint (by omega) (by omega) hm'1 (by omega)
          exact (cd.shiftPerm i.castSucc).injective (hρy'.trans hρm1.symm)
        have he_eq : e = cd.edge ⟨m', by omega⟩ :=
          (cd.shiftEdgePerm i).injective (by
            rw [hσem, cd.shiftEdgePerm_apply_edge_interior i (j := m') hm'1 (by omega)])
        subst hy'; subst he_eq
        refine Or.inl ⟨(cd.e₀_ne_edge _).symm, ?_, hvtx_nei (by omega) (by omega),
          hvtx_nei (by omega) (by omega)⟩
        have hlp := cd.isLink_edge ⟨m', by omega⟩
        simp only [Fin.castSucc_mk, Fin.succ_mk] at hlp
        exact hlp.symm
      · -- `σ e = edge (m+1)` (links `vtx (m+1)`–`vtx (m+2)`) ⇒ `ρ y' = vtx (m+2)`.
        have hσy' : G.IsLink (cd.shiftEdgePerm i e) (cd.vtx ⟨m + 1, by omega⟩)
            (cd.vtx ⟨m + 2, by omega⟩) := by rw [hσem]; exact cd.isLink_edge ⟨m + 1, by omega⟩
        have hρy' : cd.shiftPerm i.castSucc y' = cd.vtx ⟨m + 2, by omega⟩ :=
          (hσy'.right_unique hl).symm
        by_cases hmlt2 : m + 1 < (i : ℕ)
        · -- `m + 1 < i`: `e = edge m`; `y' = vtx (m+1)`.
          have hy' : y' = cd.vtx ⟨m + 1, by omega⟩ := by
            have hρm2 : cd.shiftPerm i.castSucc (cd.vtx ⟨m + 1, by omega⟩)
                = cd.vtx ⟨m + 2, by omega⟩ := hρint (by omega) (by omega) (by omega) hmlt2
            exact (cd.shiftPerm i.castSucc).injective (hρy'.trans hρm2.symm)
          have he_eq : e = cd.edge ⟨m, by omega⟩ :=
            (cd.shiftEdgePerm i).injective (by
              rw [hσem, cd.shiftEdgePerm_apply_edge_interior i (j := m) (by omega) (by omega)])
          subst hy'; subst he_eq
          refine Or.inl ⟨(cd.e₀_ne_edge _).symm, ?_, hvtx_nei (by omega) (by omega),
            hvtx_nei (by omega) (by omega)⟩
          have hlm := cd.isLink_edge ⟨m, by omega⟩
          simp only [Fin.castSucc_mk, Fin.succ_mk] at hlm
          exact hlm
        · -- `m + 1 = i`: `σ e = edge i`; `e = e₀` ⇒ candidate FRESH branch.
          have he_eq : e = cd.e₀ := by
            have heq : cd.shiftEdgePerm i e = cd.edge i := by
              rw [hσem]; congr 1; exact Fin.ext (by simp only; omega)
            exact (cd.shiftEdgePerm i).injective
              (by rw [heq, cd.shiftEdgePerm_apply_e₀ i (by omega)])
          have hy' : y' = cd.vtx ⟨(i : ℕ) + 1, by omega⟩ := by
            have hρeq : cd.shiftPerm i.castSucc y' = cd.vtx ⟨(i : ℕ) + 1, by omega⟩ := by
              rw [hρy']; congr 1; exact Fin.ext (by simp only; omega)
            have hρoff' : cd.shiftPerm i.castSucc (cd.vtx ⟨(i : ℕ) + 1, by omega⟩)
                = cd.vtx ⟨(i : ℕ) + 1, by omega⟩ := hρoff (by omega) (Or.inr (by omega))
            exact (cd.shiftPerm i.castSucc).injective (hρeq.trans hρoff'.symm)
          have hx'eq : (cd.vtx ⟨m, hm⟩ : α) = cd.vtx ⟨(i : ℕ) - 1, by omega⟩ := by
            congr 1; exact Fin.ext (by simp only; omega)
          rw [hx'eq, hy']
          exact Or.inr ⟨he_eq, Or.inr ⟨rfl, rfl⟩⟩
    -- The candidate fresh-edge `e₀` side data (neighbours `vtx (i+1)`, `vtx (i−1)` of `vtx i`).
    have hfresh_av : cd.vtx ⟨(i : ℕ) + 1, by omega⟩ ≠ cd.vtx ⟨(i : ℕ), by omega⟩ :=
      hvtx_ne_of (by omega) (by omega) (by omega)
    have hfresh_bv : cd.vtx ⟨(i : ℕ) - 1, by omega⟩ ≠ cd.vtx ⟨(i : ℕ), by omega⟩ :=
      hvtx_ne_of (by omega) (by omega) (by omega)
    have hfresh_aV : cd.vtx ⟨(i : ℕ) + 1, by omega⟩ ∈ V(G) := cd.vtx_mem _
    have hfresh_bV : cd.vtx ⟨(i : ℕ) - 1, by omega⟩ ∈ V(G) := cd.vtx_mem _
    -- Dispatch the survivor branch on which pre-image endpoint is on the cycle.
    by_cases hcyc : x ∈ cd.shiftCycle i.castSucc ∨ y ∈ cd.shiftCycle i.castSucc
    · rcases hcyc with hx | hy
      · rcases key hGσe hρx1 hρy1 hx with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1, h2, h3, h4⟩
        · exact Or.inr ⟨h1, hfresh_av, hfresh_bv, hfresh_aV, hfresh_bV, h2⟩
      · rcases key hGσe.symm hρy1 hρx1 hy with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1, h2.symm, h4, h3⟩
        · refine Or.inr ⟨h1, hfresh_av, hfresh_bv, hfresh_aV, hfresh_bV, ?_⟩
          exact (h2.imp (fun ⟨p, q⟩ => ⟨q, p⟩) (fun ⟨p, q⟩ => ⟨q, p⟩)).symm
    · -- Both pre-images off the cycle ⇒ `σ`/`ρ` fix; the edge survives the candidate split.
      rw [not_or] at hcyc
      obtain ⟨hxc, hyc⟩ := hcyc
      have hρx : cd.shiftPerm i.castSucc x = x := cd.shiftPerm_apply_off i.castSucc hxc
      have hρy : cd.shiftPerm i.castSucc y = y := cd.shiftPerm_apply_off i.castSucc hyc
      rw [hρx, hρy] at hGσe
      -- `σ e ∉ edge-cycle` (else an endpoint of `G.IsLink (σ e) x y` lands on the cycle).
      have hσoff : cd.shiftEdgePerm i (cd.shiftEdgePerm i e) = cd.shiftEdgePerm i e := by
        refine cd.shiftEdgePerm_apply_off i fun hmem => ?_
        rw [shiftEdgeCycle, List.mem_cons, List.mem_cons, List.mem_cons, List.mem_ofFn] at hmem
        rcases hmem with heq | heq | heq | ⟨j, heq⟩
        · rw [heq] at hGσe
          rcases (cd.isLink_edge ⟨0, by omega⟩).eq_and_eq_or_eq_and_eq hGσe with ⟨_, rfl⟩ | ⟨_, rfl⟩
          · exact hyc (hmem_of (by omega) (by omega) (by omega))
          · exact hxc (hmem_of (by omega) (by omega) (by omega))
        · exact hσne₀ heq
        · rw [heq] at hGσe
          have hl : G.IsLink (cd.edge i) (cd.vtx ⟨(i : ℕ), by omega⟩)
              (cd.vtx ⟨(i : ℕ) + 1, by omega⟩) := by
            have := cd.isLink_edge i; rwa [hci, hca] at this
          rcases hl.eq_and_eq_or_eq_and_eq hGσe with ⟨rfl, _⟩ | ⟨rfl, _⟩
          · exact hxc (hmem_of (by omega) (by omega) le_rfl)
          · exact hyc (hmem_of (by omega) (by omega) le_rfl)
        · have hjlt := j.isLt
          rw [← heq] at hGσe
          rcases (cd.isLink_edge ⟨(j : ℕ) + 1, by omega⟩).eq_and_eq_or_eq_and_eq hGσe with
            ⟨_, rfl⟩ | ⟨_, rfl⟩
          · exact hyc (hmem_of (by omega) (by omega) (by omega))
          · exact hxc (hmem_of (by omega) (by omega) (by omega))
      have hσe : cd.shiftEdgePerm i e = e := (cd.shiftEdgePerm i).injective hσoff
      rw [hσe] at hGσe hσne₀
      refine Or.inl ⟨hσne₀, hGσe, ?_, ?_⟩
      · intro he; exact hxc (he ▸ hmem_of (m := (i : ℕ)) (by omega) (by omega) le_rfl)
      · intro he; exact hyc (he ▸ hmem_of (m := (i : ℕ)) (by omega) (by omega) le_rfl)
  · -- **Base fresh branch**: `σ e = e₀`, `{ρ x, ρ y} = {vtx 2, vtx 0}`. `e = σ⁻¹ e₀ = edge 0`.
    have he_eq : e = cd.edge ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt⟩ :=
      (cd.shiftEdgePerm i).injective (by rw [hσe₀, cd.shiftEdgePerm_apply_edge_zero i (by omega)])
    have hρ1 : cd.shiftPerm i.castSucc (cd.vtx ⟨1, by omega⟩) = cd.vtx ⟨2, by omega⟩ :=
      hρint (by omega) (by omega) (by omega) (by omega)
    have hρ0 : cd.shiftPerm i.castSucc (cd.vtx ⟨0, by omega⟩) = cd.vtx ⟨0, by omega⟩ :=
      hρoff (by omega) (Or.inl rfl)
    have hlink : G.IsLink (cd.edge ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt⟩)
        (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨0, by omega⟩) := (cd.isLink_edge ⟨0, by omega⟩).symm
    have hedge_ne₀ : cd.edge ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt⟩ ≠ cd.e₀ :=
      (cd.e₀_ne_edge _).symm
    subst he_eq
    rcases hxy with ⟨hx2, hy0⟩ | ⟨hx0, hy2⟩
    · have hxv : x = cd.vtx ⟨1, by omega⟩ :=
        (cd.shiftPerm i.castSucc).injective (hx2.trans hρ1.symm)
      have hyv : y = cd.vtx ⟨0, by omega⟩ :=
        (cd.shiftPerm i.castSucc).injective (hy0.trans hρ0.symm)
      subst hxv; subst hyv
      exact Or.inl ⟨hedge_ne₀, hlink, hvtx_nei (by omega) (by omega),
        hvtx_nei (by omega) (by omega)⟩
    · have hxv : x = cd.vtx ⟨0, by omega⟩ :=
        (cd.shiftPerm i.castSucc).injective (hx0.trans hρ0.symm)
      have hyv : y = cd.vtx ⟨1, by omega⟩ :=
        (cd.shiftPerm i.castSucc).injective (hy2.trans hρ1.symm)
      subst hxv; subst hyv
      exact Or.inl ⟨hedge_ne₀, hlink.symm, hvtx_nei (by omega) (by omega),
        hvtx_nei (by omega) (by omega)⟩

/-- **`ρᵢ` is an isomorphism from `Gᵢ` to `G₁`** (KT eq. (6.54), p. 694): for `1 < i`, `e` joins
`x` and `y` in `Gᵢ` if and only if `shiftEdgePerm i e` joins `shiftPerm i x` and `shiftPerm i y`
in `G₁`, by `splitOff_isLink_shiftRelabel_forward` and `splitOff_isLink_shiftRelabel_backward`.
`removeVertex_genuine_shiftRelabel` and `candidateEnds_records_splitOff_isLink`
(`CaseIII/Relabel/Chain.lean`) use it. -/
lemma splitOff_isLink_shiftRelabel_iff (cd : G.ChainData n) (i : Fin cd.d) (hi : 1 < (i : ℕ))
    {e : β} {x y : α} :
    (G.splitOff (cd.vtx i.castSucc) (cd.vtx i.succ)
        (cd.vtx (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc) cd.e₀).IsLink
      e x y ↔
    (G.splitOff (cd.vtx (⟨1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc)
        (cd.vtx (⟨1, by have := i.isLt; omega⟩ : Fin cd.d).succ)
        (cd.vtx (⟨0, by have := i.isLt; omega⟩ : Fin cd.d).castSucc) cd.e₀).IsLink
      (cd.shiftEdgePerm i e) (cd.shiftPerm i.castSucc x) (cd.shiftPerm i.castSucc y) :=
  ⟨cd.splitOff_isLink_shiftRelabel_forward i hi,
    cd.splitOff_isLink_shiftRelabel_backward i hi⟩

/-! ### The endpoint selector of the `i`-th framework

For `1 < i`, `PanelHingeFramework.chainData_bottom_relabel` (`lem:case-III-chain-relabel-rows`)
renames the rows of a framework on `G − v₁` with an endpoint selector `ends₀` and normals `q` into
rows of a framework on `G − vᵢ` with the selector `candidateEnds i ends₀` and the normals `q ∘ σᵢ`:
`ends₀` and `q` read through KT's `ρᵢ` (KT eqs. (6.54) and (6.55), p. 694). -/

/-- **The endpoint selector of the `i`-th framework**: `ends₀` renamed along `ρᵢ`, that is,
`e ↦ (σᵢ⁻¹ u, σᵢ⁻¹ w)` where `(u, w) = ends₀ (shiftEdgePerm i e)` and `σᵢ = shiftPerm i`. It is
the selector in the conclusion of `PanelHingeFramework.chainData_bottom_relabel`, and
`candidateEnds_records_splitOff_isLink` shows that it gives the ends of the edges of `Gᵢ` when
`ends₀` gives those of `G₁`. -/
def candidateEnds (cd : G.ChainData n) (i : Fin cd.d) (ends₀ : β → α × α) : β → α × α :=
  fun e => ((cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).1,
    (cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).2)

@[simp] lemma candidateEnds_apply (cd : G.ChainData n) (i : Fin cd.d) (ends₀ : β → α × α) (e : β) :
    cd.candidateEnds i ends₀ e =
      ((cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).1,
        (cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).2) :=
  rfl

/-! ### The vertices `uᵢ` of the panels (KT eq. (6.67))

The `d` panels of KT eq. (6.67) (p. 698) are those of `u₀ = v₀` and of `uᵢ = vᵢ₊₁` for
`1 ≤ i ≤ d − 1` (`lem:case-III-chain-discriminator`). `candidateVtx` is `i ↦ uᵢ`, which is
injective, as `v₁` is left out. `Graph.ChainData.candidatePanel` (`CaseIII/Realization.lean`)
reindexes it by `Fin (k + 1)`, as `d = k + 1` (`Graph.ChainData.d_eq_kAdd`). -/

/-- **The vertex `uᵢ` of the `i`-th panel** (KT eq. (6.67)): `u₀ = vtx 0`, and `uᵢ = vtx (i + 1)`
for `1 ≤ i ≤ d − 1`. -/
def candidateVtx (cd : G.ChainData n) (i : Fin cd.d) : α :=
  cd.vtx (if (i : ℕ) = 0 then 0 else ⟨(i : ℕ) + 1, by omega⟩)

omit [DecidableEq α] [DecidableEq β] in
/-- `u₀ = vtx 0`. -/
@[simp] lemma candidateVtx_zero (cd : G.ChainData n) (i : Fin cd.d) (hi : (i : ℕ) = 0) :
    cd.candidateVtx i = cd.vtx 0 := by rw [candidateVtx, ite_eq_left hi]

omit [DecidableEq α] [DecidableEq β] in
/-- For `0 < i`, `uᵢ = vtx (i + 1)`. -/
@[simp] lemma candidateVtx_succ (cd : G.ChainData n) {i : Fin cd.d} (hi : 0 < (i : ℕ)) :
    cd.candidateVtx i = cd.vtx ⟨(i : ℕ) + 1, by omega⟩ := by
  rw [candidateVtx, ite_eq_right (by omega)]

omit [DecidableEq α] [DecidableEq β] in
/-- **The vertices `uᵢ` are distinct**: `v₀, v₂, …, v_d` are distinct vertices of the chain
(`vtx_inj`). -/
lemma candidateVtx_injective (cd : G.ChainData n) : Function.Injective cd.candidateVtx := by
  intro i i' he
  rw [candidateVtx, candidateVtx] at he
  have hval := congrArg Fin.val (cd.vtx_inj he)
  split_ifs at hval with hi hi' hi' <;> simp only [Fin.val_zero] at hval <;>
    exact Fin.ext (by omega)

omit [DecidableEq α] [DecidableEq β] in
/-- For `0 < i`, `uᵢ = vtx i.succ`, the neighbour `a = vtx (i + 1)` of the split at `vtx i`, in the
form `PanelHingeFramework.chainData_dispatch_interior` reads it. It is not `@[simp]`:
`candidateVtx_succ` gives the simp normal form. -/
lemma candidateVtx_succ_eq (cd : G.ChainData n) {i : Fin cd.d} (hi : 0 < (i : ℕ)) :
    cd.candidateVtx i = cd.vtx i.succ := by rw [cd.candidateVtx_succ hi, Fin.succ_mk]

end ChainData

/-! ## Cycle graphs (`def:cycle-data`; KT Lemma 4.6)

By KT Lemma 4.6 (p. 664), a `2`-edge-connected minimal `k`-dof-graph with no proper rigid
subgraph is a cycle graph on at most `d` vertices or has a chain of length `d` (`ChainData`).
`CycleData` presents `G` as the cycle `vtx 0, vtx 1, …, vtx (m − 1)`, indexed by `Fin m`, whose
addition wraps `vtx (m − 1)` around to `vtx 0`. -/

/-- **A cycle graph** (`def:cycle-data`; KT Lemma 4.6, p. 664): distinct vertices
`vtx 0, …, vtx (m − 1)`, `m ≥ 3`, and distinct edges `edge i` joining `vtx i` and `vtx (i + 1)`,
with indices modulo `m`, which are all the vertices and all the edges of `G`. -/
structure CycleData (G : Graph α β) where
  /-- The number of vertices of the cycle, which is also its number of edges. -/
  m : ℕ
  /-- `m ≥ 3`. -/
  hm : 3 ≤ m
  /-- The vertices of the cycle. -/
  vtx : Fin m → α
  /-- The edges of the cycle: `edge i` joins `vtx i` and `vtx (i + 1)`. -/
  edge : Fin m → β
  /-- The vertices are distinct. -/
  vtx_inj : Function.Injective vtx
  /-- The edges are distinct. -/
  edge_inj : Function.Injective edge
  /-- `edge i` joins `vtx i` and `vtx (i + 1)` in `G`. -/
  link : ∀ i : Fin m, G.IsLink (edge i) (vtx i) (vtx (i + ⟨1, by omega⟩))
  /-- Every vertex of `G` is a vertex of the cycle. -/
  vtx_surj : ∀ x ∈ V(G), ∃ i, vtx i = x
  /-- Every edge of `G` is an edge of the cycle. -/
  edge_surj : ∀ e ∈ E(G), ∃ i, edge i = e

namespace CycleData

variable {G : Graph α β}

/-- **The vertices of the cycle are those of `G`** (`def:cycle-data`): `range vtx = V(G)`, as each
`vtx i` is an end of `edge i` and every vertex of `G` is some `vtx i`. So `|V(G)| = m`.
`PanelHingeFramework.cycle_realization` (`lem:cycle-realization`) uses it to pass from rigidity
on the vertices of the cycle to rigidity on `V(G)`. -/
theorem range_vtx (cy : G.CycleData) : Set.range cy.vtx = V(G) := by
  apply Set.Subset.antisymm
  · rintro x ⟨i, rfl⟩
    exact (cy.link i).left_mem
  · intro x hx
    obtain ⟨i, hi⟩ := cy.vtx_surj x hx
    exact ⟨i, hi⟩

/-- **A minimal `0`-dof-graph on three vertices as a cycle** (from the proof of KT Lemma 6.7(i),
p. 677): let `D ≥ 3`, let `G` be a simple minimal `0`-dof-graph with three vertices, and let edges
`eₐ ≠ e_b` join `v` to `a` and `b`. Then `G` is the cycle with `m = 3`, `vtx = ![v, a, b]`
and `edge = ![eₐ, f, e_b]`, where `f` joins `a` and `b`
(`exists_isLink_of_isMinimalKDof_card_three`, `lem:triangle-third-edge`). Katoh and Tanigawa realize
the triangle by their Lemma 5.4 (p. 670), for cycle graphs with `3 ≤ |V| ≤ D`, and so does
`PanelHingeFramework.case_III_hsplit_producer_all_k`, with
`PanelHingeFramework.cycle_realization`. -/
noncomputable def ofCardThree [DecidableEq β] [Finite α] [Finite β] {n : ℕ} [G.Simple]
    (hD : 3 ≤ bodyBarDim n) (hG : G.IsMinimalKDof n 0) (hcard : V(G).ncard = 3)
    {v a b : α} {eₐ e_b : β}
    (hG_ea : G.IsLink eₐ v a) (hG_eb : G.IsLink e_b v b) (heab : eₐ ≠ e_b) : G.CycleData := by
  haveI : G.Loopless := ‹G.Simple›.toLoopless
  have hav : a ≠ v := hG_ea.ne.symm
  have hbv : b ≠ v := hG_eb.ne.symm
  -- Projections (not `obtain`/`casesOn`) so that `.m` of the returned record still reduces to `3`.
  have hdata := exists_isLink_of_isMinimalKDof_card_three hD hG hcard hG_ea hG_eb heab
  have hab : a ≠ b := hdata.1
  have hVeq : V(G) = {v, a, b} := hdata.2.1
  set f := hdata.2.2.choose with hfdef
  have hf : G.IsLink f a b := hdata.2.2.choose_spec
  -- edge distinctness: `f : a–b` differs from `eₐ : v–a` and `e_b : v–b` in a simple graph.
  have heaf : eₐ ≠ f := by
    rintro rfl
    rcases hG_ea.eq_and_eq_or_eq_and_eq hf with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hav h1.symm
    · exact hbv h1.symm
  have hfeb : f ≠ e_b := by
    rintro rfl
    rcases hf.eq_and_eq_or_eq_and_eq hG_eb with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hav h1
    · exact hab h1
  exact
  { m := 3
    hm := le_refl 3
    vtx := ![v, a, b]
    edge := ![eₐ, f, e_b]
    vtx_inj := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp_all [Matrix.cons_val_zero, Matrix.cons_val_one, Ne.symm hav, Ne.symm hbv, Ne.symm hab]
    edge_inj := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp_all [Matrix.cons_val_zero, Matrix.cons_val_one, Ne.symm heab, Ne.symm heaf]
    link := by
      intro i
      fin_cases i
      · exact hG_ea
      · exact hf
      · exact hG_eb.symm
    vtx_surj := by
      intro x hx
      rw [hVeq] at hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    edge_surj := by
      intro e he
      obtain ⟨x, y, hexy⟩ := G.exists_isLink_of_mem_edgeSet he
      have hx : x ∈ ({v, a, b} : Set α) := hVeq ▸ hexy.left_mem
      have hy : y ∈ ({v, a, b} : Set α) := hVeq ▸ hexy.right_mem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
      · exact absurd rfl hexy.ne
      · exact ⟨0, (hexy.unique_edge hG_ea).symm⟩
      · exact ⟨2, (hexy.unique_edge hG_eb).symm⟩
      · exact ⟨0, (hexy.symm.unique_edge hG_ea).symm⟩
      · exact absurd rfl hexy.ne
      · exact ⟨1, (hexy.unique_edge hf).symm⟩
      · exact ⟨2, (hexy.symm.unique_edge hG_eb).symm⟩
      · exact ⟨1, (hexy.symm.unique_edge hf).symm⟩
      · exact absurd rfl hexy.ne }

/-- The cycle `ofCardThree` has `m = 3`, by `rfl`. -/
@[simp] theorem ofCardThree_m [DecidableEq β] [Finite α] [Finite β] {n : ℕ} [G.Simple]
    {hD : 3 ≤ bodyBarDim n} {hG : G.IsMinimalKDof n 0} {hcard : V(G).ncard = 3}
    {v a b : α} {eₐ e_b : β} {hG_ea : G.IsLink eₐ v a} {hG_eb : G.IsLink e_b v b}
    {heab : eₐ ≠ e_b} :
    (ofCardThree hD hG hcard hG_ea hG_eb heab).m = 3 := rfl

end CycleData

end Graph
