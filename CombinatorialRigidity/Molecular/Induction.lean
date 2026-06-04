/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Deficiency
import Matroid.Graph.Minor.Defs

/-!
# The combinatorial induction: graph operations and Theorem 4.9 (`sec:molecular-induction`)

Phase 20, the fourth phase of the molecular-conjecture program (Phases 17–26; see
`notes/MolecularConjecture.md`). Where `Molecular/Deficiency.lean` (Phase 19) built the
matroid `M(G̃)`, the `D`-deficiency, and the `k`-dof hierarchy, this file develops the
graph operations that reduce a minimal `k`-dof-graph to the two-vertex double edge and
assembles them into Katoh–Tanigawa's Theorem 4.9 (Katoh–Tanigawa 2011,
*A proof of the molecular conjecture*, Discrete Comput. Geom. **45**, §3.4–3.5, §4).

This file lands the `sec:molecular-induction` dep-graph in dependency order. The chapter
opens with two structural lemmas inherited from Phase 19's close, whose lower bounds the
def = corank bridge (`thm:def-eq-corank`) now unblocks. The leaf node landing here:

* `inducedSpan` (the **vertex-induced subgraph from a fiber set**): for a fiber set
  `X : Set (β × Fin (bodyHingeMult n))` of the multiplied graph `G̃ = (D-1)·G`, the
  vertex-induced subgraph `G[V(X)]` of the *original* graph `G` on the vertices `V(X)`
  spanned by `X` in `G̃`. Realized through mathlib's `Graph.induce` on the vertex set
  `(G.mulTilde n).spanningVerts X`; the def-eq-corank machinery (Phase 19) consumes its
  multiplied form `(G[V(X)])̃` via `mulTilde`.
* `circuit_induces_isTight` (`lem:circuit-induces-rigid`; Katoh–Tanigawa 2011 Lemma 3.4,
  full form) — for a circuit `X` of `M(G̃)` and `e ∈ X`, the set `X − e` is `(D,D)`-tight
  on its vertex span: `|X − e| + D = D·|V(X)|`, equivalently `|X − e| = D(|V(X)| − 1)`. So
  `X − e` packs `D` edge-disjoint spanning trees on `V(X)` and `G[V(X)]` is rigid. The
  proof combines the upper bound — `X − e` independent ⟹ `(G̃ ↾ (X − e))` is `(D,D)`-sparse
  (Phase 19's `isSparse_diff_singleton_of_isCircuit`), giving `|X − e| ≤ D(|V(X−e)| − 1) ≤
  D(|V(X)| − 1)` — with the matching lower bound `|X| > D(|V(X)| − 1)`, forced by `X` being
  a circuit: every proper subset of `X` is independent, hence the sparsity failure of the
  dependent `X` is at `X` itself (`circuit_ncard_gt`).

See `ROADMAP.md` §20 / `notes/Phase20.md` and the `sec:molecular-induction` dep-graph of
`blueprint/src/chapter/molecular-induction.tex`.
-/

namespace Graph

open Set Matroid

variable {α β : Type*}

/-! ## The vertex-induced subgraph from a fiber set -/

/-- The set of vertices **spanned** by a fiber set `X` of the multiplied graph
`G̃ = (D-1)·G`: `V(X) = (G̃).spanningVerts X`, the vertices of `G` incident to some fiber
of `X`. This is the `V(X)` of Katoh–Tanigawa 2011 Lemma 3.4. -/
def fiberSpan (G : Graph α β) (n : ℕ) (X : Set (β × Fin (bodyHingeMult n))) : Set α :=
  (G.mulTilde n).spanningVerts X

/-- The **vertex-induced subgraph** `G[V(X)]` of `G` on the vertices `V(X)` spanned by a
fiber set `X` of `G̃ = (D-1)·G` (`def:graph-operations`, the induced-from-an-edge-set
construction): mathlib's `Graph.induce` applied to `G.fiberSpan n X`. This is the subgraph
Katoh–Tanigawa 2011 Lemma 3.4 concludes is rigid. -/
def inducedSpan (G : Graph α β) (n : ℕ) (X : Set (β × Fin (bodyHingeMult n))) : Graph α β :=
  G.induce (G.fiberSpan n X)

@[simp]
lemma vertexSet_inducedSpan (G : Graph α β) (n : ℕ) (X : Set (β × Fin (bodyHingeMult n))) :
    V(G.inducedSpan n X) = G.fiberSpan n X := by
  rw [inducedSpan, vertexSet_induce]

/-! ## A canonical endpoint selector (`def:graph-operations`, the `ends` selector)

The from-scratch panel-hinge realization `PanelHingeFramework.ofParam G ends param` of the
algebraic induction (Phase 21b) takes an *endpoint selector* `ends : β → α × α` choosing an
ordered pair of endpoints for each edge. Case I orients the rigid block's spanning forest along
this selector; the Case-I realization producer (`lem:case-I-realization`, Phase 21b) requires it
to be *consistent* with the graph — `G.IsLink (e j) (u j) (other j)` and
`ends (e j) = (u j, other j)` for the forest hinges. This section lands the canonical such
selector once, as a reusable `Graph`
primitive, rather than re-deriving the per-edge `obtain ⟨x, y, hlink⟩` choice inline at each use
(the pattern `exists_isLink_of_mem_edgeSet` is repeated a dozen times across the molecular files).
-/

open Classical in
/-- **The canonical endpoint selector of a graph** (`def:graph-operations`): for each edge
`e : β`, an ordered pair `(x, y) : α × α` of endpoints, chosen (via `Classical.choice`) to be a
genuine link `G.IsLink e x y` whenever `e ∈ E(G)`. On non-edges it returns the junk constant
`(default, default)`; the only contract is consistency on `E(G)` (`isLink_endsOf`). This is the
`ends` selector the from-scratch panel realization `PanelHingeFramework.ofParam` consumes: it
supplies, for every edge, an orientation along which the rigid block's spanning forest is laid
out, with the link witnessed by `isLink_endsOf`. -/
noncomputable def endsOf [Inhabited α] (G : Graph α β) (e : β) : α × α :=
  if h : ∃ x y, G.IsLink e x y then (h.choose, h.choose_spec.choose) else (default, default)

/-- **The canonical endpoint selector is a genuine link on every edge** (`def:graph-operations`):
if `e ∈ E(G)` then `G.IsLink e (G.endsOf e).1 (G.endsOf e).2`. The endpoint pair `G.endsOf e` is
chosen by `Classical.choice` from `exists_isLink_of_mem_edgeSet`, so its components are an actual
pair of ends of `e`. This is the consistency contract the Case-I realization producer
(`lem:case-I-realization`, Phase 21b) requires of its forest hinges (`hlink`), discharging the
per-edge `obtain ⟨x, y, hlink⟩` choice once and for all. -/
lemma isLink_endsOf [Inhabited α] (G : Graph α β) {e : β} (he : e ∈ E(G)) :
    G.IsLink e (G.endsOf e).1 (G.endsOf e).2 := by
  have h : ∃ x y, G.IsLink e x y := exists_isLink_of_mem_edgeSet he
  rw [endsOf, dif_pos h]
  exact h.choose_spec.choose_spec

/-- **The canonical endpoint selector orients along a given link** (`def:graph-operations`): if
`G.IsLink e x y`, then `G.endsOf e` is one of the two oriented pairs `(x, y)` or `(y, x)`. The
two ends of an edge are determined up to order (`IsLink.eq_and_eq_or_eq_and_eq`), so the canonical
selector — itself a genuine link (`isLink_endsOf`) — must agree with `(x, y)` as an unordered
pair. Lets a consumer that has *named* endpoints `x y` recover them (up to swap) from the canonical
selector, which is what the Case-I spanning-forest orientation needs to match `ends (e j) =
(u j, other j)` against a forest edge it already linked. -/
lemma endsOf_eq_or_swap [Inhabited α] (G : Graph α β) {e : β} {x y : α} (h : G.IsLink e x y) :
    G.endsOf e = (x, y) ∨ G.endsOf e = (y, x) := by
  have hl := G.isLink_endsOf h.edge_mem
  rcases hl.eq_and_eq_or_eq_and_eq h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (Prod.ext h1 h2)
  · exact Or.inr (Prod.ext h1 h2)

/-! ## A circuit induces a rigid subgraph (`lem:circuit-induces-rigid`; KT Lemma 3.4 full form) -/

/-- **A circuit exceeds the sparsity bound on its vertex span** (Katoh–Tanigawa 2011
Lemma 3.4, lower-bound half). For a circuit `X` of `M(G̃)`, `|X| + D > D·|V(X)|`, i.e.
`|X| > D(|V(X)| − 1)`. A circuit is a *minimal* dependent set: every proper subset is
independent, hence `(D,D)`-sparse, so the sparsity failure of the dependent `X` can only
occur at `X` itself. Concretely, picking any `e ∈ X`, the proper subset `X \ {e}` is
independent (`IsCircuit.diff_singleton_indep`) hence `(D,D)`-sparse, so if `X` itself also
satisfied the bound, every nonempty subset of `X` would, making `(G̃ ↾ X)` sparse and `X`
independent — contradicting that `X` is a circuit. -/
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
    have hsparse := ((matroidMG_indep_iff G n).mp (hX.diff_singleton_indep heX)).2
    have hE''edge : E'' ⊆ E(G.mulTilde n ↾ (X \ {e})) := by
      rw [edgeSet_restrict, inter_eq_right.mpr (diff_subset.trans hXg)]
      exact hsub
    have hsp := hsparse E'' hE''edge hE''ne
    rwa [spanningVerts_restrict_of_subset hsub] at hsp

/-- **A circuit induces a rigid subgraph** (`lem:circuit-induces-rigid`; Katoh–Tanigawa 2011
Lemma 3.4, full form). Let `X` be a circuit of `M(G̃)` and `e ∈ X`. Then `X − e` is
`(D,D)`-tight on its vertex span `V(X)`: `|X − e| + D = D·|V(X)|`, equivalently
`|X − e| = D(|V(X)| − 1)`. Thus `X − e` packs `D` edge-disjoint spanning trees on `V(X)`
and the vertex-induced subgraph `G[V(X)]` is rigid (`0`-dof).

The upper bound `|X − e| + D ≤ D·|V(X)|`: `X − e` is independent
(`IsCircuit.diff_singleton_indep`), so `(G̃ ↾ (X − e))` is `(D,D)`-sparse
(`isSparse_diff_singleton_of_isCircuit`); applying sparsity to `X − e` itself gives
`|X − e| + D ≤ D·|spanningVerts(X − e)| ≤ D·|V(X)|` (a circuit minus an edge spans no more
vertices, `spanningVerts (X − e) ⊆ spanningVerts X = V(X)`). The lower bound
`D·|V(X)| ≤ |X − e| + D` is `circuit_ncard_gt` (`|X| > D(|V(X)| − 1)`) with `|X| =
|X − e| + 1` (`e ∈ X`). -/
theorem circuit_induces_isTight [DecidableEq β] [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    {X : Set (β × Fin (bodyHingeMult n))} (hX : (G.matroidMG n).IsCircuit X)
    {e : β × Fin (bodyHingeMult n)} (he : e ∈ X) :
    (X \ {e}).ncard + bodyBarDim n = bodyBarDim n * (G.fiberSpan n X).ncard := by
  -- `|X| = |X − e| + 1`.
  have hfinX : X.Finite := X.toFinite
  have hcardX : X.ncard = (X \ {e}).ncard + 1 := by
    rw [Set.ncard_diff_singleton_add_one he hfinX]
  -- Lower bound: `circuit_ncard_gt` (`|X| > D(|V(X)| − 1)`).
  have hlower := circuit_ncard_gt hX
  rw [hcardX] at hlower
  -- Upper bound: `X − e` independent ⟹ `(G̃ ↾ (X − e))` is `(D,D)`-sparse; apply to `X − e`.
  have hsparse := (isSparse_diff_singleton_of_isCircuit hX he).1
  have hXe_sub : X \ {e} ⊆ E(G.mulTilde n) := diff_subset.trans hX.subset_ground
  have hupper : (X \ {e}).ncard + bodyBarDim n ≤ bodyBarDim n * (G.fiberSpan n X).ncard := by
    have hmono : (G.mulTilde n).spanningVerts (X \ {e}) ⊆ G.fiberSpan n X :=
      fun x ⟨p, hp, hinc⟩ ↦ ⟨p, diff_subset hp, hinc⟩
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

/-- **A circuit's fibers are edges of the induced subgraph** (`lem:circuit-induces-rigid`,
support): every fiber `p ∈ X` of a fiber set `X` of `G̃` has its underlying edge `p.1`
joining two vertices of the vertex span `V(X) = fiberSpan X`, hence `p ∈ E((G[V(X)])̃)`.
This is the inclusion `X ⊆ E((inducedSpan X)̃)` that lets the `M(G̃)`-circuit `X` be read
as an edge set of the induced subgraph `G[V(X)]`. -/
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

/-- **A circuit induces a rigid subgraph** (`lem:circuit-induces-rigid`; Katoh–Tanigawa 2011
Lemma 3.4, full form — rigid-subgraph conclusion). Let `X` be a circuit of `M(G̃)`. Then the
vertex-induced subgraph `G[V(X)]` on the vertex span `V(X) = fiberSpan X` is a **rigid
subgraph** of `G`: `G[V(X)] ≤ G` and `def((G[V(X)])̃) = 0`, i.e. it is `0`-dof.

This packages the tightness *equality* `circuit_induces_isTight` (`|X − e| = D(|V(X)| − 1)`)
into the `IsRigidSubgraph` predicate Katoh–Tanigawa's Lemmas 4.5(i)/4.8 consume ("Lemma 3.4
implies `G[V(X)]` is a (proper) rigid subgraph"). The rank of `M((G[V(X)])̃)` is pinned to
`D(|V(X)| − 1)` from both sides: the upper bound is `rank_matroidMG_le`, and the lower bound
is the independent `X − e` of size `D(|V(X)| − 1)` (independent in `M((G[V(X)])̃) = M(G̃) ↾
E((G[V(X)])̃)` by `matroidMG_restrict_mulTilde`, since `X ⊆ E((G[V(X)])̃)`). The def\,=\,corank
bridge `rank_add_deficiency_eq` then forces the deficiency to `0`. -/
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
    diff_subset.trans (subset_edgeSet_mulTilde_inducedSpan hXground)
  have hXe_indepG : (G.matroidMG n).Indep (X \ {e}) := hX.diff_singleton_indep heX
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

/-- **The fundamental circuit of an out-of-base fiber spans all of `G`, given no proper
rigid subgraph** (`lem:no-rigid-edge-count`, support; Katoh–Tanigawa 2011 Lemma 4.5(i),
the spanning step). Let `B` be a base of `M(G̃)` and `p ∈ E(G̃) ∖ B` a fiber element
outside it. Its fundamental circuit `X = fundCircuit p B` induces a rigid subgraph
`G[V(X)]` (`circuit_induces_isRigidSubgraph`, via `IsBase.fundCircuit_isCircuit`); if `G`
has **no proper rigid subgraph**, that rigid subgraph cannot be proper, so it must span all
of `G`: `V(G[V(X)]) = V(X) = V(G)`.

This is the "Lemma 3.4 ⟹ `V(X) = V(G)`" reduction Katoh–Tanigawa use inside the KT 4.5(i)
edge-count bound `lem:no-rigid-edge-count` (and again in the KT 4.7–4.8 reduction step): the
fundamental circuit of any redundant fiber is forced to be *spanning*, which is what lets the
later base-exchange relocate redundancy onto a single fiber `ẽ`. It isolates the clean,
matroid-API half of KT 4.5(i) (the rigid-subgraph / no-proper-rigid reasoning) from the
remaining base-exchange count. -/
theorem fundCircuit_inducedSpan_vertexSet_eq [DecidableEq β] [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} (hD : 1 ≤ bodyBarDim n)
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
  -- `V(X)` is nonempty: a circuit is nonempty, and each fiber spans a vertex.
  have hVne : V(G.inducedSpan n X).Nonempty := by
    rw [vertexSet_inducedSpan, fiberSpan]
    obtain ⟨q, hq⟩ := hXcirc.nonempty
    obtain ⟨x, _, hinc⟩ := exists_isLink_of_mem_edgeSet (hXcirc.subset_ground hq)
    exact ⟨x, q, hq, hinc.inc_left⟩
  -- If `V(X) ⊊ V(G)`, `G[V(X)]` is a *proper* rigid subgraph — excluded by hypothesis.
  refine subset_antisymm hsub ?_
  by_contra hnotle
  exact hnp (G.inducedSpan n X)
    ⟨hrigid, hVne, hsub.ssubset_of_ne (fun heq ↦ hnotle heq.ge)⟩

/-! ## Forest-packing decomposition of `M(G̃)`-independent sets (`lem:forest-surgery-split`)

The matroidal substrate the Katoh–Tanigawa forest surgery (KT Lemmas 4.1/4.2) operates on.
`M(G̃)` is the `D`-fold union of the cycle matroid of `G̃` restricted to `E(G̃)`
(`def:matroid-MG`), so by the matroid-union characterization (`Matroid.union_indep_iff`,
Nash-Williams 1966 / Edmonds) an independent set `I` of `M(G̃)` is exactly one that decomposes into
`D = bodyBarDim n` cycle-matroid-independent fiber sets `F₀, …, F_{D-1}` — the **`D`
edge-disjoint forests on `V(G̃)`** of Katoh–Tanigawa's proof. This pins the **framing** of
the surgery (the open Phase-20 blocker): a "forest" of `G̃` is a cycle-matroid-independent
fiber set (mathlib `Matroid.Graph.cycleMatroid` independence = acyclicity), and the
`D`-forest partition is the `Matroid.union_indep_iff` decomposition — *no* hand-rolled
graph-theoretic acyclicity predicate is introduced. KT 4.1's surgery then reroutes each of
these `D` forests across the degree-2 vertex `v`. -/

/-- **Forest-packing decomposition of an `M(G̃)`-independent set** (`lem:forest-surgery-split`,
framing; Katoh–Tanigawa 2011, the "partition `I` into `D` edge-disjoint forests on `V`" step
opening the proofs of Lemmas 4.1/4.2). A fiber set `I ⊆ E(G̃)` is independent in `M(G̃)` iff it
is covered by `D = bodyBarDim n` cycle-matroid-independent fiber sets (the `D` edge-disjoint
forests of `G̃`): `∃ Fs : Fin D → Set _, ⋃ i, Fs i = I ∧ ∀ i, (G̃.cycleMatroid).Indep (Fs i)`.

This is the matroidal reading of "`I` partitions into `D` edge-disjoint forests": `M(G̃)` is the
`D`-fold cycle-matroid union restricted to `E(G̃)` (`def:matroid-MG`), so independence unfolds
through `Matroid.restrict_indep_iff` and `Matroid.union_indep_iff` (Nash-Williams 1966 /
Edmonds). It fixes
the framing of the Katoh–Tanigawa forest surgery: a "forest" is a `(G̃).cycleMatroid`-independent
fiber set, and the surgery of KT Lemma 4.1 reroutes each of these `D` forests across the
degree-2 vertex. -/
theorem matroidMG_indep_iff_exists_forest_packing [DecidableEq β] [Finite α] [Finite β]
    (G : Graph α β) (n : ℕ) {I : Set (β × Fin (bodyHingeMult n))} :
    (G.matroidMG n).Indep I ↔ I ⊆ E(G.mulTilde n) ∧
      ∃ Fs : Fin (bodyBarDim n) → Set (β × Fin (bodyHingeMult n)),
        ⋃ i, Fs i = I ∧ ∀ i, ((G.mulTilde n).cycleMatroid).Indep (Fs i) := by
  rw [matroidMG, Matroid.restrict_indep_iff, Matroid.union_indep_iff]
  tauto

/-! ### Katoh–Tanigawa Lemma 4.1 is over-quantified (`lem:forest-surgery-split`, off-path note)

Katoh–Tanigawa 2011 Lemma 4.1 (p.660; the 2009 arXiv predecessor Lemma 5.1, p.11) is
quantified "**for any** independent set `I` of `M(G̃)` … there exists `I'` … with
`|I'| = |I| − D`". As literally quantified over *all* independent `I` this is **false**:
for any `I` with `|I| < D` — e.g. `I = ∅` — it demands `|I'| = |I| − D < 0`, impossible.
The intended quantifier is over **bases** of `M(G̃)`; the universal form must be restricted.

We record the literal disproof as a named lemma (the `I = ∅`, ℕ-cardinality witness:
no `I'` can satisfy `|I'| + D = 0` because `D = bodyBarDim n ≥ 1`). This is a narrow
*statement-as-quantified* observation, **not** a refutation of KT's theorem: the molecular
conjecture and KT's proof stand. The intended (base-form) content the induction consumes —
the deficiency inequality `def(G̃ᵥᵃᵇ) ≤ def(G̃)` — is true and is established directly via
the deficiency-count route (`lem:splitoff-deficiency`), bypassing the forest surgery. A
separate, subtler gap (KT's base-case proof silently assumes a *balanced* `D`-forest packing
at the degree-2 vertex `v`, which we could neither justify nor recover) gates only the
deferred surgery TODO; see `notes/Phase20.md` *Finding* / *Replan*. The framing here is
deliberately "KT omits / we did not recover", never "KT errs". -/

/-- **KT Lemma 4.1's universal quantification over independent sets is not satisfiable**
(`lem:forest-surgery-split`, over-quantification note; Katoh–Tanigawa 2011 Lemma 4.1 p.660 /
2009 arXiv Lemma 5.1 p.11). The lemma as stated promises, *for any* independent set `I` of
`M(G̃)`, an `I'` with `|I'| = |I| − D` (i.e. `|I'| + D = |I|`). Taking `I = ∅` (independent
in any matroid) makes the demand `|I'| + D = 0` in ℕ, which fails whenever `D = bodyBarDim n
≥ 1`. So the universal-over-`I` reading is formally false; the intended quantifier is over
*bases*. See the section docstring and `notes/Phase20.md` for the three-layer framing — this
is the *statement-as-quantified* layer only, not a refutation of KT's theorem. -/
theorem kt_lemma_41_overquantified (n : ℕ) (hD : 1 ≤ bodyBarDim n) :
    ¬ ∃ I' : Set (β × Fin (bodyHingeMult n)),
        I'.ncard + bodyBarDim n = (∅ : Set (β × Fin (bodyHingeMult n))).ncard := by
  rintro ⟨I', hI'⟩
  rw [Set.ncard_empty] at hI'
  omega

/-! ## A rigid subgraph attains full rank (`lem:contraction-minimality`, rank core)

The matroidal arithmetic the rigid-subgraph contraction of KT Lemma 3.5 opens on: a
*rigid* subgraph `H` (`def(H̃) = 0`) has `rank M(H̃) = D(|V(H)| − 1)`, the maximal value
allowed by the rank upper bound. This is the `def = 0` reading of the def\,$=$\,corank
bridge (`thm:def-eq-corank`, Phase 19's `rank_add_deficiency_eq`): a `0`-dof graph's
multiplied form packs `D` edge-disjoint spanning trees on its `|V(H)|` vertices, exactly
`D(|V(H)| − 1)` edges. Contracting such an `H` removes precisely this rank from `M(G̃)`
and the matching `D(|V(H)| − 1)` from the ambient `D(|V| − 1)`, leaving the corank — hence
the deficiency — unchanged; that is the engine of Case I of the algebraic induction. -/

/-- **A rigid subgraph attains full rank** (`lem:contraction-minimality`, rank core;
Katoh–Tanigawa 2011 Lemma 3.5, the rank-conservation fact its proof opens on). For a
rigid subgraph — `H.IsKDof n 0`, i.e. `def(H̃) = 0` — with `V(H).Nonempty` and
`D = bodyBarDim n ≥ 1`, the matroid `M(H̃)` has full rank `rank M(H̃) = D(|V(H)| − 1)`.

Immediate from the def\,$=$\,corank bridge `rank_add_deficiency_eq` (Phase 19) with the
deficiency `def(H̃) = 0` of the rigid hypothesis: `rank M(H̃) + 0 = D(|V(H)| − 1)`. This
is the rank quantity contraction of a rigid subgraph removes from both `rank M(G̃)` and
the ambient `D(|V| − 1)`, leaving the corank/deficiency unchanged (KT 3.5). -/
theorem rank_matroidMG_of_isKDof_zero [DecidableEq β] [Finite α] [Finite β] {H : Graph α β}
    {n : ℕ} (hD : 1 ≤ bodyBarDim n) (hne : V(H).Nonempty) (hrigid : H.IsKDof n 0) :
    ((H.matroidMG n).rank : ℤ) = bodyBarDim n * ((V(H).ncard : ℤ) - 1) := by
  have hbridge := H.rank_add_deficiency_eq n hD hne
  rw [IsKDof] at hrigid
  rw [hrigid] at hbridge
  simpa using hbridge

/-! ## The matroid contraction rank bridge (`lem:contraction-minimality`, contraction arithmetic)

The graph↔matroid side of KT Lemma 3.5: contracting a rigid subgraph `H` removes exactly
`rank M(H̃) = D(|V(H)| − 1)` from `rank M(G̃)`. On the matroid this is the rank-conservation
identity for a contraction, `rank(M ／ C) + rank(M ↾ C) = rank M`, specialized to
`C = E(H̃)` via the restriction identity `M(G̃) ↾ E(H̃) = M(H̃)` (`matroidMG_restrict_mulTilde`,
Phase 19). The rank-conservation identity is the abstract matroid chain rule
`eRelRk C M.E + eRk C = eRk M.E` (`Matroid.eRelRk_add_eRk_eq`), read through
`(M ／ C).eRank = eRelRk C M.E` and `(M ↾ C).eRank = eRk C`; together with the rank core
`rank_matroidMG_of_isKDof_zero` it pins the rank contraction removes, the input to the
deficiency-conservation half of `lem:contraction-minimality`. -/

/-- **Contraction rank-conservation** for a matroid: `rank(M ／ C) + rank(M ↾ C) = rank M`
in a rank-finite matroid. This is the standard matroid identity `r(M/C) = r(M) − r_M(C)`
in additive form, the contraction arithmetic the rigid-subgraph contraction of
Katoh–Tanigawa 2011 Lemma 3.5 runs on. The contraction half is the vendored relative-rank
identity `Matroid.contract_rank_cast_int_eq` (`r(M/C) = r(M) − r_M(C)`); the restriction's
rank is `r_M(C)` since `(M ↾ C).E = C` (`Matroid.restrict_rk_eq`). -/
theorem _root_.Matroid.rank_contract_add_rank_restrict {γ : Type*} (M : Matroid γ)
    [M.RankFinite] (C : Set γ) :
    (M ／ C).rank + (M ↾ C).rank = M.rank := by
  have hrestrict : (M ↾ C).rank = M.rk C := by
    rw [Matroid.rank_def, Matroid.restrict_ground_eq, Matroid.restrict_rk_eq M subset_rfl]
  have hcontract : ((M ／ C).rank : ℤ) = (M.rank : ℤ) - (M.rk C : ℤ) := M.contract_rank_cast_int_eq C
  omega

/-- **The contraction rank bridge for `M(G̃)`** (`lem:contraction-minimality`, contraction
arithmetic; Katoh–Tanigawa 2011 Lemma 3.5). For a subgraph `H ≤ G`, contracting the
edge-fibers `E(H̃)` in `M(G̃)` removes exactly `rank M(H̃)`:
`rank(M(G̃) ／ E(H̃)) + rank M(H̃) = rank M(G̃)`. The restriction `M(G̃) ↾ E(H̃)` is
`M(H̃)` (`matroidMG_restrict_mulTilde`, Phase 19), so this is the abstract contraction
rank-conservation `Matroid.rank_contract_add_rank_restrict` read through that identity.
Combined with the rank core `rank_matroidMG_of_isKDof_zero` (rigid `H` ⟹
`rank M(H̃) = D(|V(H)| − 1)`), it pins the rank contraction of a *rigid* subgraph removes
from `rank M(G̃)` — the deficiency-conservation input of KT 3.5's Case-I engine. -/
theorem contract_matroidMG_rank [DecidableEq β] [Finite α] [Finite β] {H G : Graph α β}
    (h : H ≤ G) (n : ℕ) :
    ((G.matroidMG n) ／ E(H.mulTilde n)).rank + (H.matroidMG n).rank = (G.matroidMG n).rank := by
  have hrestrict : (G.matroidMG n) ↾ E(H.mulTilde n) = H.matroidMG n :=
    matroidMG_restrict_mulTilde h n
  rw [← hrestrict]
  exact (G.matroidMG n).rank_contract_add_rank_restrict _

/-! ## Contracting a rigid subgraph conserves the deficiency (`lem:contraction-minimality`)

The deficiency-conservation half of KT Lemma 3.5: contracting a *rigid* proper subgraph
`H` of `G` leaves the deficiency unchanged. Stated on the *matroid* side — against the
matroid contraction `M(G̃) / E(H̃)`, matching how KT's proof reasons — this is pure
bookkeeping over the two rank facts already in hand. Contracting `H` collapses `|V(H)|`
vertices to one, so the contraction lives over `|V(G)| − |V(H)| + 1` vertices and its
ambient trivial-motion count drops by `D(|V(H)| − 1)`; `lem:contract-rank-bridge` removes
the *matching* `rank M(H̃) = D(|V(H)| − 1)` (`lem:rigid-full-rank`) from the rank, so the
corank — hence the deficiency (`thm:def-eq-corank`) — is unchanged. The minimality-transport
half (every base of the contracted matroid meets every surviving edge-fiber) is the second
half of `lem:contraction-minimality`, scheduled next. -/

/-- **Contracting a rigid subgraph conserves the deficiency** (`lem:contraction-minimality`,
deficiency-conservation half; Katoh–Tanigawa 2011 Lemma 3.5). For a rigid subgraph
`H ≤ G` (`H.IsKDof n 0`) with `V(H).Nonempty` and `D = bodyBarDim n ≥ 1`, the corank of
the matroid contraction `M(G̃) / E(H̃)` at the *reduced* ambient `D(|V(G)| − |V(H)|)`
(the trivial-motion count of the contracted graph, which has `|V(G)| − |V(H)| + 1`
vertices) equals `def(G̃)`:
`D(|V(G)| − |V(H)|) − rank(M(G̃) / E(H̃)) = def(G̃)`.

Pure matroid bookkeeping over the two rank facts: `contract_matroidMG_rank`
(`rank(M(G̃)/E(H̃)) + rank M(H̃) = rank M(G̃)`) with the rank core
`rank_matroidMG_of_isKDof_zero` (`rank M(H̃) = D(|V(H)| − 1)`) gives
`rank(M(G̃)/E(H̃)) = rank M(G̃) − D(|V(H)| − 1)`; substituting into the def\,$=$\,corank
bridge `rank_add_deficiency_eq` (`rank M(G̃) + def(G̃) = D(|V(G)| − 1)`) and cancelling the
`D(|V(H)| − 1)` between the rank drop and the ambient drop leaves `def(G̃)`. No
graph↔matroid `map` correspondence is needed — the statement is against the matroid
contraction directly. -/
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

/-! ## Graph operations (`def:graph-operations`, `def:rigid-contraction`)

The four operations on `Graph α β` that drive the Katoh–Tanigawa induction
(`def:graph-operations`, `def:rigid-contraction`): vertex removal, splitting-off at
a degree-2 vertex, its inverse edge-splitting, and rigid-subgraph contraction. These
are graph-level constructions; their *deficiency* behaviour (the forest-surgery core,
KT 4.1–4.5) routes through the matroid `M(G̃)` of Phase 19 in later nodes. -/

/-- **Vertex removal** `G_v := G − v` (`def:graph-operations`): delete `v` and all its
incident edges. Realized through mathlib's `Graph.deleteVerts {v}`. -/
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

/-- **Vertex removal is a subgraph** (`def:graph-operations`): `G_v = G − v ≤ G`. The
common-subgraph lower bound for the splitting-off edge-substitution bridge below
(`removeVertex_le_splitOff`); both `G` and `G_v^{ab}` sit *above* `G − v`. -/
lemma removeVertex_le (G : Graph α β) (v : α) : G.removeVertex v ≤ G := by
  rw [removeVertex]; exact G.deleteVerts_le

/-- **Every link of `G` lost by removing `v` is incident to `v`** (`lem:case-II`, the
`hinc` brick of the genericity-gated tightness). The common lower bound of the Case II
edge-substitution is `G − v` (`removeVertex_le` / `removeVertex_le_splitOff`): both the
parent graph `G` and the splitting-off `G_v^{ab}` re-add edges *over* `G − v`. The hinge
constraints those re-added edges impose on a `v`-pinned motion collapse to a single span
membership at the non-`v` endpoint, but only because every link of `G` outside `G − v` is
incident to `v` — which is exactly this lemma: a link `e u w` of `G` that does *not* survive
the vertex removal must have `u = v ∨ w = v` (else it avoids `v` and `removeVertex_isLink`
would keep it). This is the graph-side hypothesis `hinc` of
`BodyHingeFramework.hnew_of_isLink_incident` instantiated at the Case II common lower bound
`G' = G − v`, so it discharges the incidence side of `hnew` for the splitting-off
1-extension (leaving only the genericity span membership `hspan`, Claim 6.9). -/
lemma isLink_incident_of_not_removeVertex {G : Graph α β} {v : α} {e : β} {u w : α}
    (h : G.IsLink e u w) (hg : ¬(G.removeVertex v).IsLink e u w) : u = v ∨ w = v := by
  by_contra hc
  rw [not_or] at hc
  exact hg (removeVertex_isLink.mpr ⟨h, hc.1, hc.2⟩)

/-- **Splitting-off** `G_v^{ab}` at a degree-2 vertex `v` with neighbours `a`, `b`
(`def:graph-operations`): delete `v` and replace the two edges through `v` by a single
fresh edge `e₀` joining `a` and `b`. Edges other than `e₀` are kept iff they avoid `v`;
the new edge `e₀` links exactly `a` and `b` (requiring `a, b ≠ v` so the construction is
a well-formed graph on the surviving vertices). -/
def splitOff (G : Graph α β) (v a b : α) (e₀ : β) : Graph α β where
  vertexSet := V(G) \ {v}
  IsLink e x y :=
    (e ≠ e₀ ∧ G.IsLink e x y ∧ x ≠ v ∧ y ≠ v) ∨
      (e = e₀ ∧ a ≠ v ∧ b ≠ v ∧ a ∈ V(G) ∧ b ∈ V(G) ∧
        ((x = a ∧ y = b) ∨ (x = b ∧ y = a)))
  isLink_symm := by
    rintro e he x y (⟨hne, h, hx, hy⟩ | ⟨he₀, ha, hb, haV, hbV, hxy⟩)
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

/-- **Splitting-off strictly decreases the vertex count** (`lem:reduction-step`, the
"reduces to a smaller graph" measure). Splitting off a vertex `v ∈ V(G)` deletes `v`
(`V(G_v^{ab}) = V(G) ∖ {v}`), so `|V(G_v^{ab})| < |V(G)|`. This is the well-founded measure
on which Katoh–Tanigawa 2011's Theorem 4.9 inducts in the splitting-off branch (the
no-proper-rigid-subgraph case): each reduction step lands on a strictly smaller minimal
`k`-dof-graph. -/
lemma splitOff_vertexSet_ncard_lt [Finite α] {G : Graph α β} {v a b : α} {e₀ : β}
    (hv : v ∈ V(G)) : V(G.splitOff v a b e₀).ncard < V(G).ncard := by
  rw [vertexSet_splitOff]
  exact Set.ncard_diff_singleton_lt_of_mem hv (Set.toFinite _)

@[simp]
lemma splitOff_isLink {G : Graph α β} {v a b : α} {e₀ : β} {e : β} {x y : α} :
    (G.splitOff v a b e₀).IsLink e x y ↔
      (e ≠ e₀ ∧ G.IsLink e x y ∧ x ≠ v ∧ y ≠ v) ∨
        (e = e₀ ∧ a ≠ v ∧ b ≠ v ∧ a ∈ V(G) ∧ b ∈ V(G) ∧
          ((x = a ∧ y = b) ∨ (x = b ∧ y = a))) := Iff.rfl

/-- **Edge set of a splitting-off** `G_v^{ab}` (`def:graph-operations`): an edge `e`
survives the splitting-off iff either `e = e₀` is the fresh short-circuit edge (which is
present exactly when its endpoints `a, b` are distinct from `v` and lie in `V(G)`), or `e`
is an `e₀`-distinct edge of `G` not incident to the deleted vertex `v`. The condition for
the fresh edge `e₀` records that the splitting-off at a degree-2 vertex `v` with neighbours
`a, b` short-circuits the two `v`-edges into a single `ab` edge. This is the edge-level
bookkeeping the forest surgery of `lem:forest-surgery-split` (KT 4.1) runs on. -/
lemma edgeSet_splitOff {G : Graph α β} {v a b : α} {e₀ : β} :
    E(G.splitOff v a b e₀) =
      {e | e = e₀ ∧ a ≠ v ∧ b ≠ v ∧ a ∈ V(G) ∧ b ∈ V(G)} ∪
        {e | e ≠ e₀ ∧ ∃ x y, G.IsLink e x y ∧ x ≠ v ∧ y ≠ v} := by
  ext e
  rw [edgeSet_eq_setOf_exists_isLink]
  simp only [splitOff_isLink, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · rintro ⟨x, y, (⟨hne, h, hx, hy⟩ | ⟨rfl, ha, hb, haV, hbV, _⟩)⟩
    · exact Or.inr ⟨hne, x, y, h, hx, hy⟩
    · exact Or.inl ⟨rfl, ha, hb, haV, hbV⟩
  · rintro (⟨rfl, ha, hb, haV, hbV⟩ | ⟨hne, x, y, h, hx, hy⟩)
    · exact ⟨a, b, Or.inr ⟨rfl, ha, hb, haV, hbV, Or.inl ⟨rfl, rfl⟩⟩⟩
    · exact ⟨x, y, Or.inl ⟨hne, h, hx, hy⟩⟩

/-- **The fresh short-circuit fiber `ã̃b` lives in `E(G̃_v^{ab})`** (`def:graph-operations`):
when the splitting-off `G_v^{ab}` at a degree-2 vertex `v` with neighbours `a, b`
(`a, b ≠ v`, `a, b ∈ V(G)`) actually inserts its short-circuit edge `e₀`, the whole fiber
`ẽ₀ = {p | p.1 = e₀}` of `D - 1 = bodyHingeMult n` parallel copies lies in
`E(G̃_v^{ab})`. This is the `ã̃b` fiber the forest surgery of `lem:forest-surgery-split`
(KT 4.1) reroutes its degree-2 forests onto, and the fibers whose count must stay
`< D - 1` in the surgery's output. -/
lemma edgeFiber_subset_edgeSet_mulTilde_splitOff {G : Graph α β} {v a b : α} {e₀ : β}
    (n : ℕ) (ha : a ≠ v) (hb : b ≠ v) (haV : a ∈ V(G)) (hbV : b ∈ V(G)) :
    edgeFiber e₀ n ⊆ E((G.splitOff v a b e₀).mulTilde n) := by
  intro p hp
  rw [mem_edgeSet_mulTilde]
  rw [edgeFiber, Set.mem_setOf_eq] at hp
  rw [hp, edgeSet_splitOff]
  exact Or.inl ⟨rfl, ha, hb, haV, hbV⟩

/-- **Edge-substitution bridge for splitting-off** (`def:graph-operations`, the
graph-level brick of `lem:case-II`). The splitting-off `G_v^{ab} = G.splitOff v a b e₀`
is *not* a subgraph of `G`: it deletes `v`'s two edges `eₐ, e_b` but adds a *fresh*
short-circuit edge `e₀` joining `a` and `b` (with `e₀ ∉ E(G)`). The two graphs are instead
an **edge substitution** of each other, sharing the common subgraph `G − v` (all of `G`
away from `v`): `G − v ≤ G` (`removeVertex_le`) and `G − v ≤ G_v^{ab}` (this lemma). The
inclusion holds because every link of `G − v` is a link of `G` avoiding `v`
(`removeVertex_isLink`), and its edge — being an edge of `G` — is `≠ e₀` (else `e₀ ∈ E(G)`,
contradicting `he₀`), so it survives into `G_v^{ab}` through `splitOff`'s `e ≠ e₀` branch.

This is the missing graph-level piece Case II's 1-extension needs to wire the inductive
realization of `G_v^{ab}` (placed *above* `G − v`) into the parent framework on `G` (also
above `G − v`) via `withGraph`: both re-add edges over the shared `G − v`, so the
`withGraph`-routed monotonicity / rank machinery (`pinnedMotions_le_withGraph` et al.,
all requiring `G' ≤ F.graph`) applies through the common lower bound `G − v` rather than
the (false) direct comparison `G_v^{ab} ≤ G`. -/
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

/-! ## Splitting-off does not increase the deficiency (`lem:splitoff-deficiency`)

The substantive splitting-off fact the combinatorial induction consumes (Katoh–Tanigawa
2011 Lemma 4.3(i)), established directly via the **deficiency-count route** that bypasses
the forest surgery of `lem:forest-surgery-split` (see `rem:kt-lemma-41` /
`notes/Phase20.md` *Replan*). For a degree-2 vertex `v` of `G` with neighbours `a, b`,
splitting-off `G_v^{ab}` does not increase the deficiency: `def(G̃_v^{ab}) ≤ def(G̃)`.

The proof is a per-partition comparison on the green `deficiency` infrastructure of
`Molecular/Deficiency.lean`, *no forests*. Take any partition `P'` of
`V(G_v^{ab}) = V(G) ∖ {v}` and extend it to a partition `P` of `V(G)` by dropping `v`
into `a`'s block (`f = update f' v (f' a)`). Then `|P| = |P'|` (the label of `v`, `f' a`,
is already carried by `a ∈ V(G) ∖ {v}`), and the crossing-edge count does not increase:
the `va`-edge no longer crosses `P` (both endpoints carry `f' a`), the `vb`-edge crosses
`P` exactly when the short-circuit `e₀ = ab` crosses `P'`, and every other edge survives
verbatim with the same crossing status. So `def_{G̃}(P) ≥ def_{G̃_v^{ab}}(P')`, and taking
`P'` over the supremum gives `def(G̃) ≥ def(G̃_v^{ab})`. -/

/-- **Splitting-off does not increase the deficiency** (`lem:splitoff-deficiency`,
KT Lemma 4.3(i)). Let `v` be a degree-2 vertex of `G` with neighbours `a, b`, carried by
two distinct edges `eₐ` (joining `v, a`) and `e_b` (joining `v, b`) that are the *only*
edges of `G` incident to `v` (`hdeg2`), with `a, b ≠ v`. With the short-circuit label
`e₀` fresh (`e₀ ∉ E(G)`), the splitting-off `G_v^{ab}` satisfies
`def(G̃_v^{ab}) ≤ def(G̃)`.

Proved by the deficiency-count route (no forest surgery): each partition `P'` of
`V(G) ∖ {v}` extends to a partition `P` of `V(G)` (drop `v` into `a`'s block) with
`|P| = |P'|` and `d_G(P) ≤ d_{G_v^{ab}}(P')`, via the crossing-edge injection
`e_b ↦ e₀`, identity elsewhere. See `rem:kt-lemma-41` and `notes/Phase20.md` for why this
replaces KT's forest surgery (`lem:forest-surgery-split`). -/
theorem splitOff_deficiency_le [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hD : 1 ≤ bodyBarDim n) {v a b : α} {e₀ eₐ e_b : β}
    (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b)
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    (he₀ : e₀ ∉ E(G)) :
    (G.splitOff v a b e₀).deficiency n ≤ G.deficiency n := by
  classical
  set H := G.splitOff v a b e₀ with hH
  have haV : a ∈ V(G) := hla.right_mem
  have hbV : b ∈ V(G) := hlb.right_mem
  -- It suffices to bound each partition `P'` of `H` by `def(G̃)`.
  haveI : Nonempty α := ⟨a⟩
  rw [deficiency]
  refine ciSup_le fun f' => ?_
  -- Extend `f'` to a partition `f` of `V(G)` by dropping `v` into `a`'s block.
  set f := Function.update f' v (f' a) with hf
  have hfne : ∀ x, x ≠ v → f x = f' x := fun x hx => Function.update_of_ne hx _ _
  have hfv : f v = f' a := Function.update_self v (f' a) f'
  -- Step 1: the number of parts is unchanged.
  have hparts : G.numParts f = H.numParts f' := by
    rw [numParts, numParts, vertexSet_splitOff]
    congr 1
    apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      by_cases hxv : x = v
      · subst hxv
        exact ⟨a, ⟨haV, by simpa using hav⟩, by rw [hfv]⟩
      · exact ⟨x, ⟨hx, by simpa using hxv⟩, (hfne x hxv).symm⟩
    · rintro _ ⟨x, ⟨hx, hxv⟩, rfl⟩
      exact ⟨x, hx, hfne x (by simpa using hxv)⟩
  -- Step 2: the crossing-edge count does not increase, via the injection `e_b ↦ e₀`.
  have hcross : (G.crossingEdges f).ncard ≤ (H.crossingEdges f').ncard := by
    -- `f` and `f'` agree away from `v`; `f v = f' a` and `f b = f' b` (since `b ≠ v`).
    have hfb : f b = f' b := hfne b hbv
    have hfa : f a = f' a := hfne a hav
    refine Set.ncard_le_ncard_of_injOn (fun e => if e = e_b then e₀ else e) ?_ ?_ ?_
    · -- maps crossing edges of `G` to crossing edges of `H`
      rintro e ⟨heG, x, y, hlink, hxy⟩
      by_cases hev : e = e_b
      · -- `e_b` ↦ `e₀`: `e₀` links `a, b` in `H`, and `f' a ≠ f' b` (since `e_b` crosses).
        simp only [if_pos hev]
        rw [hev] at hlink
        -- The endpoints `{x, y}` of `e_b` are `{v, b}`, so `f x ≠ f y` gives `f' a ≠ f' b`.
        have hab' : f' a ≠ f' b := by
          rcases hlb.eq_and_eq_or_eq_and_eq hlink with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rwa [hfv, hfb] at hxy
          · rw [hfv, hfb] at hxy; exact fun h => hxy h.symm
        have hl₀ : H.IsLink e₀ a b := by
          rw [hH, splitOff_isLink]
          exact Or.inr ⟨rfl, hav, hbv, haV, hbV, Or.inl ⟨rfl, rfl⟩⟩
        exact ⟨hl₀.edge_mem, a, b, hl₀, hab'⟩
      · -- `e ≠ e_b`: `e` avoids `v`, survives in `H`, crosses with the same labels.
        simp only [if_neg hev]
        -- `e` is not incident to `v`: else `e ∈ {eₐ, e_b}` and `eₐ`/`e_b`-incident edges
        -- through `v` get equal labels or contradict `e ≠ e_b`.
        have hxv : x ≠ v ∧ y ≠ v := by
          refine ⟨fun hxv => hxy ?_, fun hyv => hxy ?_⟩
          · -- `x = v`: `e` through `v` is `eₐ` (not `e_b`), so `y = a`; then `f x = f y`.
            subst hxv
            rcases hdeg2 e y hlink with rfl | rfl
            · obtain ⟨_, rfl⟩ | ⟨_, hav'⟩ := hla.eq_and_eq_or_eq_and_eq hlink
              · rw [hfv, hfa]
              · exact absurd hav' hav
            · exact absurd rfl hev
          · -- `y = v`: symmetric.
            subst hyv
            rcases hdeg2 e x hlink.symm with rfl | rfl
            · obtain ⟨_, rfl⟩ | ⟨_, hav'⟩ := hla.eq_and_eq_or_eq_and_eq hlink.symm
              · rw [hfv, hfa]
              · exact absurd hav' hav
            · exact absurd rfl hev
        have hee₀ : e ≠ e₀ := fun h => he₀ (h ▸ heG)
        refine ⟨?_, x, y, ?_, ?_⟩
        · have : H.IsLink e x y := by
            rw [hH, splitOff_isLink]; exact Or.inl ⟨hee₀, hlink, hxv.1, hxv.2⟩
          exact this.edge_mem
        · rw [hH, splitOff_isLink]; exact Or.inl ⟨hee₀, hlink, hxv.1, hxv.2⟩
        · rwa [hfne x hxv.1, hfne y hxv.2] at hxy
    · -- injectivity on `crossingEdges G f`: `g` is identity except `e_b ↦ e₀ ∉ E(G)`.
      intro e1 he1 e2 he2 hg
      dsimp only at hg
      have hmemG : ∀ {e}, e ∈ G.crossingEdges f → e ∈ E(G) := fun h => h.1
      by_cases h1 : e1 = e_b <;> by_cases h2 : e2 = e_b
      · rw [h1, h2]
      · -- `g e1 = e₀ = e2`, but `e2 ∈ E(G)` and `e₀ ∉ E(G)`.
        rw [if_pos h1, if_neg h2] at hg
        exact absurd (hg ▸ hmemG he2) he₀
      · rw [if_neg h1, if_pos h2] at hg
        exact absurd (hg.symm ▸ hmemG he1) he₀
      · rwa [if_neg h1, if_neg h2] at hg
    · exact Set.toFinite _
  -- Combine: `partitionDef_G(f) ≥ partitionDef_H(f')`, then bound by the supremum.
  have hmono : H.partitionDef n f' ≤ G.partitionDef n f := by
    rw [partitionDef, partitionDef, hparts]
    have hD1 : (0 : ℤ) ≤ (bodyBarDim n : ℤ) - 1 := by
      have : (1 : ℤ) ≤ (bodyBarDim n : ℤ) := by exact_mod_cast hD
      linarith
    nlinarith [Int.ofNat_le.mpr hcross]
  exact hmono.trans (G.partitionDef_le_deficiency n f)

/-! ### Splitting-off lowers the deficiency by at most one (`lem:splitoff-deficiency`, KT 4.3(ii))

The companion lower bound to `splitOff_deficiency_le`: splitting-off at a degree-2 vertex
`v` drops the deficiency by at most `1`, `def(G̃_v^{ab}) ≥ def(G̃) − 1`. Combined with the
upper bound `def(G̃_v^{ab}) ≤ def(G̃)` (`splitOff_deficiency_le`), this pins
`def(G̃_v^{ab}) ∈ {def(G̃), def(G̃) − 1}` — the "`G_v^{ab}` is a `k`-dof-graph or a
`(k−1)`-dof-graph" alternative of KT Lemma 4.3(i)/(ii). The dof-tracking assembly
(`lem:dof-tracking`) consumes this two-sided bound; the matroid-base characterization of
*which* of the two holds (`∃` base `B'` with `|ã̃b ∩ B'| < D − 1`) is KT's reading via the
deferred forest surgery (`rem:kt-lemma-41`) and is not needed for Theorem 4.9.

The proof is again a per-partition deficiency-count comparison, *no forests*, dual to
`splitOff_deficiency_le`: take a partition `f` of `V(G)` attaining `def(G̃)` (finite
supremum, `exists_eq_ciSup_of_finite`), reuse the *same* labeling on `V(G) ∖ {v}`, and
case-split on whether `v`'s label is shared by another vertex.
* If `v`'s label is shared, `|P|` is unchanged and the crossing count does not increase
  (the `va`/`vb` edges leaving and the short-circuit `ab` entering crosses at most as
  often), so `def_{G̃_v^{ab}}(P) ≥ def_{G̃}(P) = def(G̃)`.
* If `v` is isolated in its part, `|P|` drops by exactly `1` and the crossing count drops
  by at least `1` (both `va`, `vb` left, `ab` enters), so `def_{G̃_v^{ab}}(P) ≥
  D(|P| − 2) − (D−1)(d_G(P) − 1) = def(G̃) − 1`. -/

/-- **Splitting-off lowers the deficiency by at most one** (`lem:splitoff-deficiency`,
KT Lemma 4.3(i)/(ii) refinement). With the same degree-2 hypotheses as
`splitOff_deficiency_le` (the two `v`-incident edges `eₐ`, `e_b` and the fresh `e₀ ∉ E(G)`),
`def(G̃) − 1 ≤ def(G̃_v^{ab})`. Together with `splitOff_deficiency_le` this confines the
splitting-off deficiency to `{def(G̃), def(G̃) − 1}`: `G_v^{ab}` is a `k`-dof- or a
`(k−1)`-dof-graph.

Proved by the deficiency-count route (no forest surgery), dual to `splitOff_deficiency_le`:
a partition `f` attaining `def(G̃)` is reused on `V(G) ∖ {v}`; a case split on whether `v`'s
label is shared bounds the change in parts and crossing edges. See `rem:kt-lemma-41` and
`notes/Phase20.md` for why the matroid-base form of KT 4.3(ii) is off the Theorem-4.9
critical path. -/
theorem splitOff_deficiency_ge [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hD : 1 ≤ bodyBarDim n) {v a b : α} {e₀ eₐ e_b : β}
    (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b)
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    (he₀ : e₀ ∉ E(G)) :
    G.deficiency n - 1 ≤ (G.splitOff v a b e₀).deficiency n := by
  classical
  set H := G.splitOff v a b e₀ with hH
  have haV : a ∈ V(G) := hla.right_mem
  have hbV : b ∈ V(G) := hlb.right_mem
  have hD1 : (0 : ℤ) ≤ (bodyBarDim n : ℤ) - 1 := by
    have : (1 : ℤ) ≤ (bodyBarDim n : ℤ) := by exact_mod_cast hD
    linarith
  -- Pick a partition `f` of `V(G)` attaining `def(G̃)` (finite supremum).
  haveI : Nonempty α := ⟨a⟩
  obtain ⟨f, hf⟩ := exists_eq_ciSup_of_finite (f := G.partitionDef n)
  rw [deficiency, ← hf]
  -- It suffices to bound the same labeling `f` (restricted to `V(H) = V(G) ∖ {v}`) below.
  refine le_trans ?_ (H.partitionDef_le_deficiency n f)
  -- `eₐ`, `e_b ∈ E(G)`, and both differ from `e₀`.
  have heaG : eₐ ∈ E(G) := hla.edge_mem
  have hebG : e_b ∈ E(G) := hlb.edge_mem
  have heae₀ : eₐ ≠ e₀ := fun h => he₀ (h ▸ heaG)
  have hebe₀ : e_b ≠ e₀ := fun h => he₀ (h ▸ hebG)
  -- `eₐ`, `e_b` are dropped by the splitting-off (they are `v`-incident), so `∉ E(H)`.
  have heaH : eₐ ∉ E(H) := by
    rw [hH, edgeSet_splitOff]
    rintro (⟨h, _⟩ | ⟨_, x, y, hl, hxv, hyv⟩)
    · exact heae₀ h
    · rcases hla.eq_and_eq_or_eq_and_eq hl with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact hxv rfl
      · exact hyv rfl
  have hebH : e_b ∉ E(H) := by
    rw [hH, edgeSet_splitOff]
    rintro (⟨h, _⟩ | ⟨_, x, y, hl, hxv, hyv⟩)
    · exact hebe₀ h
    · rcases hlb.eq_and_eq_or_eq_and_eq hl with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact hxv rfl
      · exact hyv rfl
  by_cases hshared : ∃ w ∈ V(G), w ≠ v ∧ f w = f v
  · -- Case: `v`'s label `f v` is shared, so `|P|` is unchanged.
    have hparts : H.numParts f = G.numParts f := by
      obtain ⟨w, hwV, hwv, hfw⟩ := hshared
      rw [numParts, numParts, vertexSet_splitOff]
      congr 1
      apply Set.Subset.antisymm
      · rintro _ ⟨x, hx, rfl⟩; exact ⟨x, hx.1, rfl⟩
      · rintro _ ⟨x, hx, rfl⟩
        by_cases hxv : x = v
        · exact ⟨w, ⟨hwV, by simpa using hwv⟩, by rw [hfw, hxv]⟩
        · exact ⟨x, ⟨hx, by simpa using hxv⟩, rfl⟩
    -- Crossing edges of `H` inject into crossing edges of `G` (`e₀ ↦` a crossing `v`-edge).
    have hcross : (H.crossingEdges f).ncard ≤ (G.crossingEdges f).ncard := by
      refine Set.ncard_le_ncard_of_injOn
        (fun e => if e = e₀ then (if f v = f a then e_b else eₐ) else e) ?_ ?_ (Set.toFinite _)
      · rintro e ⟨heH, x, y, hlink, hxy⟩
        by_cases hee₀ : e = e₀
        · -- `e₀` crosses `f`: its endpoints are `a, b`, so `f a ≠ f b`.
          rw [hH, splitOff_isLink] at hlink
          rcases hlink with ⟨hne, _⟩ | ⟨_, _, _, _, _, hxy'⟩
          · exact absurd hee₀ hne
          have hab : f a ≠ f b := by
            rcases hxy' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hxy
            · exact fun h => hxy h.symm
          simp only [if_pos hee₀]
          by_cases hfva : f v = f a
          · -- map to `e_b`: `e_b` links `v, b`, `f v = f a ≠ f b`, so `e_b` crosses.
            simp only [if_pos hfva]
            exact ⟨hebG, v, b, hlb, by rw [hfva]; exact hab⟩
          · -- map to `eₐ`: `eₐ` links `v, a`, `f v ≠ f a`, so `eₐ` crosses.
            simp only [if_neg hfva]
            exact ⟨heaG, v, a, hla, hfva⟩
        · simp only [if_neg hee₀]
          rw [hH, splitOff_isLink] at hlink
          rcases hlink with ⟨_, hl, _, _⟩ | ⟨rfl, _⟩
          · exact ⟨hl.edge_mem, x, y, hl, hxy⟩
          · exact absurd rfl hee₀
      · -- injectivity: identity off `e₀`; `e₀ ↦ eₐ`/`e_b ∉ E(H)`, so no surviving edge hits it.
        intro e1 he1 e2 he2 hg
        dsimp only at hg
        -- A surviving crossing edge of `H` lies in `E(H)`, hence is neither `eₐ` nor `e_b`.
        have hne : ∀ {e}, e ∈ H.crossingEdges f → e ≠ e₀ →
            e ≠ (if f v = f a then e_b else eₐ) := by
          rintro e ⟨heH, -⟩ - rfl
          by_cases hfva : f v = f a
          · rw [if_pos hfva] at heH; exact hebH heH
          · rw [if_neg hfva] at heH; exact heaH heH
        by_cases h1 : e1 = e₀ <;> by_cases h2 : e2 = e₀
        · rw [h1, h2]
        · rw [if_pos h1, if_neg h2] at hg; exact absurd hg.symm (hne he2 h2)
        · rw [if_neg h1, if_pos h2] at hg; exact absurd hg (hne he1 h1)
        · rwa [if_neg h1, if_neg h2] at hg
    rw [partitionDef, partitionDef, hparts]
    nlinarith [Int.ofNat_le.mpr hcross]
  · -- Case: `v` is isolated in its part (`f v` carried only by `v`).
    push Not at hshared
    -- `|P|` drops by exactly `1`: `f '' V(G) = insert (f v) (f '' V(H))`, `f v ∉ f '' V(H)`.
    have hfv_notin : f v ∉ f '' V(H) := by
      rintro ⟨w, hwV, hfw⟩
      rw [hH, vertexSet_splitOff] at hwV
      exact hshared w hwV.1 (by simpa using hwV.2) hfw
    have hvV : v ∈ V(G) := hla.left_mem
    have himg : f '' V(G) = insert (f v) (f '' V(H)) := by
      rw [hH, vertexSet_splitOff]
      apply Set.Subset.antisymm
      · rintro _ ⟨x, hx, rfl⟩
        by_cases hxv : x = v
        · exact Set.mem_insert_iff.mpr (Or.inl (by rw [hxv]))
        · exact Set.mem_insert_iff.mpr (Or.inr ⟨x, ⟨hx, by simpa using hxv⟩, rfl⟩)
      · rintro _ (rfl | ⟨x, hx, rfl⟩)
        · exact ⟨v, hvV, rfl⟩
        · exact ⟨x, hx.1, rfl⟩
    have hparts : (G.numParts f : ℤ) = (H.numParts f : ℤ) + 1 := by
      rw [numParts, numParts, himg, Set.ncard_insert_of_notMem hfv_notin (Set.toFinite _)]
      push_cast; ring
    -- `eₐ`, `e_b` both cross `f` (since `f a ≠ f v` and `f b ≠ f v`), and `eₐ ∉ E(H)`.
    have hfav : f a ≠ f v := hshared a haV hav
    have hfbv : f b ≠ f v := hshared b hbV hbv
    have hea_cross : eₐ ∈ G.crossingEdges f := ⟨heaG, v, a, hla, fun h => hfav h.symm⟩
    have heb_cross : e_b ∈ G.crossingEdges f := ⟨hebG, v, b, hlb, fun h => hfbv h.symm⟩
    -- Crossing edges of `H` inject into crossing edges of `G` *minus* `eₐ`: drop by ≥ 1.
    have hcross : (H.crossingEdges f).ncard + 1 ≤ (G.crossingEdges f).ncard := by
      have hsub : insert eₐ ((fun e => if e = e₀ then e_b else e) '' H.crossingEdges f)
          ⊆ G.crossingEdges f := by
        rintro e (rfl | ⟨e', he', rfl⟩)
        · exact hea_cross
        · obtain ⟨heH', x, y, hlink, hxy⟩ := he'
          by_cases hee₀ : e' = e₀
          · -- `e₀` crosses ⟹ `f a ≠ f b` ⟹ `e_b` crosses (map `e₀ ↦ e_b`).
            simp only [if_pos hee₀]
            rw [hH, splitOff_isLink, hee₀] at hlink
            rcases hlink with ⟨hne, _⟩ | ⟨_, _, _, _, _, hxy'⟩
            · exact absurd rfl hne
            exact heb_cross
          · simp only [if_neg hee₀]
            rw [hH, splitOff_isLink] at hlink
            rcases hlink with ⟨_, hl, _, _⟩ | ⟨rfl, _⟩
            · exact ⟨hl.edge_mem, x, y, hl, hxy⟩
            · exact absurd rfl hee₀
      have hinj : Set.InjOn (fun e => if e = e₀ then e_b else e) (H.crossingEdges f) := by
        intro e1 he1 e2 he2 hg
        dsimp only at hg
        have hne : ∀ {e}, e ∈ H.crossingEdges f → e ≠ e₀ → e ≠ e_b := by
          rintro e ⟨heH, -⟩ - rfl; exact hebH heH
        by_cases h1 : e1 = e₀ <;> by_cases h2 : e2 = e₀
        · rw [h1, h2]
        · rw [if_pos h1, if_neg h2] at hg; exact absurd hg.symm (hne he2 h2)
        · rw [if_neg h1, if_pos h2] at hg; exact absurd hg (hne he1 h1)
        · rwa [if_neg h1, if_neg h2] at hg
      have hnotmem : eₐ ∉ (fun e => if e = e₀ then e_b else e) '' H.crossingEdges f := by
        rintro ⟨e', he', hg⟩
        dsimp only at hg
        by_cases hee₀ : e' = e₀
        · rw [if_pos hee₀] at hg; exact heab hg.symm
        · rw [if_neg hee₀] at hg; exact heaH (hg ▸ he'.1)
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_insert_of_notMem hnotmem (Set.toFinite _), hinj.ncard_image] at this
      omega
    rw [partitionDef, partitionDef]
    have : (G.numParts f : ℤ) = (H.numParts f : ℤ) + 1 := hparts
    nlinarith [Int.ofNat_le.mpr hcross, this]

/-! ### Vertex removal raises the deficiency (`lem:removal-deficiency`, KT Lemma 4.4)

The other half of the local dof bookkeeping at a degree-2 vertex `v`: deleting `v`
(`removeVertex`) does **not** decrease the deficiency, `def(G̃) ≤ def(G̃ᵥ)`. Equivalently,
if `def(G̃) = k` then `def(G̃ᵥ) ≥ k` — Katoh–Tanigawa 2011 Lemma 4.4 (p.662).

This is proved by the **same deficiency-count route** that carried `splitOff_deficiency_le`
/ `splitOff_deficiency_ge`, *no forests* — refuting `notes/Phase20.md` *Finding 2* (which
had claimed KT 4.4's lower bound is not a deficiency-counting fact, gated on the unsplit
forest surgery). The removal case is in fact structurally *simpler* than splitting-off:
`removeVertex v = deleteVerts {v}` adds **no** fresh edge `e₀`/`ab`, so the crossing count
strictly drops with no replacement. Take a partition `f` of `V(G)` attaining `def(G̃) = k`
(finite supremum), and reuse the *same* labeling on `V(Gᵥ) = V(G) ∖ {v}`. The crossing
edges of `Gᵥ` are exactly the crossing edges of `G` other than the two `v`-incident edges
`eₐ`, `e_b` (`hdeg2`), so `d_{Gᵥ}(P) = d_G(P) − c` with `c ∈ {0, 1, 2}` the number of
`v`-edges that crossed. Case-split on whether `v`'s label is shared:
* **shared** — `|P|` unchanged, so `def_{Gᵥ}(P) = k + (D−1)·c ≥ k` (the dropped `v`-edges
  *help*, since `partitionDef` carries `−(D−1)·d`; we only need `d_{Gᵥ}(P) ≤ d_G(P)`).
* **isolated** — `|P|` drops by exactly `1`, but `v`'s neighbours `a, b` are then forced
  into *different* blocks from `v`, so **both** `eₐ` and `e_b` crossed (`c = 2`), giving
  `def_{Gᵥ}(P) = k − D + 2(D−1) = k + (D−2) ≥ k`. The `+2(D−1)` crossing-drop exactly
  pays for the `−D` part-loss precisely because `D ≥ 2`.

The `2 ≤ bodyBarDim n` hypothesis (strengthening the bare `1 ≤ bodyBarDim n` the
splitting-off lemmas carry) is where the molecular regime `n ≥ 2 ⟹ D = n(n+1)/2 ≥ 3`
enters; it is the genuine signature difference from `splitOff_deficiency_ge`, forcing the
isolated case to break even. Degree-2 (`hdeg2`: `eₐ`, `e_b` are the only `v`-incident
edges) is what forces `c = 2` in the isolated case. -/

/-- **Vertex removal raises the deficiency** (`lem:removal-deficiency`, KT Lemma 4.4,
p.662). Let `v` be a degree-2 vertex of `G` with neighbours `a, b`, carried by the two
distinct edges `eₐ` (joining `v, a`) and `e_b` (joining `v, b`) that are the *only* edges
of `G` incident to `v` (`hdeg2`), with `a, b ≠ v`. With `D = bodyBarDim n ≥ 2`, vertex
removal does not decrease the deficiency: `def(G̃) ≤ def(G̃ᵥ)`. So if `G` is a `k`-dof-graph
then `G_v` has `def(G̃ᵥ) ≥ k`.

Proved by the deficiency-count route (no forest surgery), parallel to
`splitOff_deficiency_ge` but simpler — there is no fresh short-circuit edge, so the
crossing count strictly drops. A partition `f` attaining `def(G̃)` is reused on
`V(G) ∖ {v}`; a case split on whether `v`'s label is shared bounds the change in parts and
crossing edges. In the isolated case both `v`-edges necessarily cross (`c = 2`), and the
`D ≥ 2` hypothesis makes the `+2(D−1)` crossing-drop pay for the `−D` part-loss. This is
the deficiency-count proof that **refutes** `notes/Phase20.md` *Finding 2*'s claim that
KT 4.4 needed the unsplit forest surgery. See `notes/Phase20.md` and `rem:kt-lemma-44`. -/
theorem removeVertex_deficiency_ge [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hD : 2 ≤ bodyBarDim n) {v a b : α} {eₐ e_b : β}
    (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b)
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b) :
    G.deficiency n ≤ (G.removeVertex v).deficiency n := by
  classical
  set H := G.removeVertex v with hH
  have haV : a ∈ V(G) := hla.right_mem
  have hbV : b ∈ V(G) := hlb.right_mem
  have hD1 : (0 : ℤ) ≤ (bodyBarDim n : ℤ) - 1 := by
    have : (1 : ℤ) ≤ (bodyBarDim n : ℤ) := by exact_mod_cast (le_trans (by norm_num) hD)
    linarith
  -- Pick a partition `f` of `V(G)` attaining `def(G̃)` (finite supremum).
  haveI : Nonempty α := ⟨a⟩
  obtain ⟨f, hf⟩ := exists_eq_ciSup_of_finite (f := G.partitionDef n)
  rw [deficiency, ← hf]
  -- It suffices to bound the same labeling `f` on `V(H) = V(G) ∖ {v}` below.
  refine le_trans ?_ (H.partitionDef_le_deficiency n f)
  have heaG : eₐ ∈ E(G) := hla.edge_mem
  have hebG : e_b ∈ E(G) := hlb.edge_mem
  -- The crossing edges of `H = Gᵥ` inject into those of `G`: identity, surviving `v`-free.
  have hcross_sub : H.crossingEdges f ⊆ G.crossingEdges f := by
    rintro e ⟨heH, x, y, hlink, hxy⟩
    rw [hH, removeVertex_isLink] at hlink
    exact ⟨hlink.1.edge_mem, x, y, hlink.1, hxy⟩
  -- A crossing edge of `G` that is **not** a crossing edge of `H` must be `v`-incident,
  -- hence `eₐ` or `e_b` (`hdeg2`).
  have hcross_diff : ∀ {e}, e ∈ G.crossingEdges f → e ∉ H.crossingEdges f →
      e = eₐ ∨ e = e_b := by
    rintro e ⟨heG, x, y, hlink, hxy⟩ hnotH
    by_cases hxv : x = v
    · subst hxv; exact hdeg2 e y hlink
    · by_cases hyv : y = v
      · subst hyv; exact hdeg2 e x hlink.symm
      · have hlinkH : H.IsLink e x y := by rw [hH, removeVertex_isLink]; exact ⟨hlink, hxv, hyv⟩
        exact absurd ⟨hlinkH.edge_mem, x, y, hlinkH, hxy⟩ hnotH
  by_cases hshared : ∃ w ∈ V(G), w ≠ v ∧ f w = f v
  · -- Case: `v`'s label `f v` is shared, so `|P|` is unchanged. Crossing count does not
    -- increase (`hcross_sub`), so the per-partition deficiency does not decrease.
    have hparts : H.numParts f = G.numParts f := by
      obtain ⟨w, hwV, hwv, hfw⟩ := hshared
      rw [numParts, numParts, hH, vertexSet_removeVertex]
      congr 1
      apply Set.Subset.antisymm
      · rintro _ ⟨x, hx, rfl⟩; exact ⟨x, hx.1, rfl⟩
      · rintro _ ⟨x, hx, rfl⟩
        by_cases hxv : x = v
        · exact ⟨w, ⟨hwV, by simpa using hwv⟩, by rw [hfw, hxv]⟩
        · exact ⟨x, ⟨hx, by simpa using hxv⟩, rfl⟩
    have hcross : (H.crossingEdges f).ncard ≤ (G.crossingEdges f).ncard :=
      Set.ncard_le_ncard hcross_sub (Set.toFinite _)
    rw [partitionDef, partitionDef, hparts]
    nlinarith [Int.ofNat_le.mpr hcross]
  · -- Case: `v` is isolated in its part (`f v` carried only by `v`).
    push Not at hshared
    -- `|P|` drops by exactly `1`: `f '' V(G) = insert (f v) (f '' V(H))`, `f v ∉ f '' V(H)`.
    have hfv_notin : f v ∉ f '' V(H) := by
      rintro ⟨w, hwV, hfw⟩
      rw [hH, vertexSet_removeVertex] at hwV
      exact hshared w hwV.1 (by simpa using hwV.2) hfw
    have hvV : v ∈ V(G) := hla.left_mem
    have himg : f '' V(G) = insert (f v) (f '' V(H)) := by
      rw [hH, vertexSet_removeVertex]
      apply Set.Subset.antisymm
      · rintro _ ⟨x, hx, rfl⟩
        by_cases hxv : x = v
        · exact Set.mem_insert_iff.mpr (Or.inl (by rw [hxv]))
        · exact Set.mem_insert_iff.mpr (Or.inr ⟨x, ⟨hx, by simpa using hxv⟩, rfl⟩)
      · rintro _ (rfl | ⟨x, hx, rfl⟩)
        · exact ⟨v, hvV, rfl⟩
        · exact ⟨x, hx.1, rfl⟩
    have hparts : (G.numParts f : ℤ) = (H.numParts f : ℤ) + 1 := by
      rw [numParts, numParts, himg, Set.ncard_insert_of_notMem hfv_notin (Set.toFinite _)]
      push_cast; ring
    -- `eₐ`, `e_b` both cross `f` (since `f a ≠ f v` and `f b ≠ f v`), but are not crossing
    -- edges of `H` (they are `v`-incident, dropped by `removeVertex`).
    have hfav : f a ≠ f v := hshared a haV hav
    have hfbv : f b ≠ f v := hshared b hbV hbv
    have hea_cross : eₐ ∈ G.crossingEdges f := ⟨heaG, v, a, hla, fun h => hfav h.symm⟩
    have heb_cross : e_b ∈ G.crossingEdges f := ⟨hebG, v, b, hlb, fun h => hfbv h.symm⟩
    have hea_notH : eₐ ∉ H.crossingEdges f := by
      rintro ⟨heH, x, y, hlink, _⟩
      rw [hH, removeVertex_isLink] at hlink
      rcases hla.eq_and_eq_or_eq_and_eq hlink.1 with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact hlink.2.1 rfl
      · exact hlink.2.2 rfl
    have heb_notH : e_b ∉ H.crossingEdges f := by
      rintro ⟨heH, x, y, hlink, _⟩
      rw [hH, removeVertex_isLink] at hlink
      rcases hlb.eq_and_eq_or_eq_and_eq hlink.1 with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact hlink.2.1 rfl
      · exact hlink.2.2 rfl
    -- Crossing count drops by ≥ 2: `H.crossingEdges f ∪ {eₐ, e_b} ⊆ G.crossingEdges f`,
    -- with `eₐ ≠ e_b` and both `∉ H.crossingEdges f`.
    have hcross : (H.crossingEdges f).ncard + 2 ≤ (G.crossingEdges f).ncard := by
      have hsub : insert eₐ (insert e_b (H.crossingEdges f)) ⊆ G.crossingEdges f := by
        rintro e (rfl | rfl | he)
        · exact hea_cross
        · exact heb_cross
        · exact hcross_sub he
      have hbnotin : e_b ∉ H.crossingEdges f := heb_notH
      have hanotin : eₐ ∉ insert e_b (H.crossingEdges f) := by
        rw [Set.mem_insert_iff]; push Not; exact ⟨heab, hea_notH⟩
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      rwa [Set.ncard_insert_of_notMem hanotin (Set.toFinite _),
        Set.ncard_insert_of_notMem hbnotin (Set.toFinite _)] at this
    rw [partitionDef, partitionDef]
    nlinarith [Int.ofNat_le.mpr hcross, hparts]

/-! ### Degrees of freedom under vertex removal and splitting-off (`lem:dof-tracking`, KT 4.3–4.5)

The local degree-of-freedom bookkeeping at a degree-2 vertex `v`, packaged from the three
green per-partition deficiency bounds. For a `k`-dof-graph `G` (`def(G̃) = k`) with a
degree-2 vertex `v` of neighbours `a, b`:
* the splitting-off `G_v^{ab}` is a `k`-dof- or a `(k−1)`-dof-graph — `def(G̃_v^{ab}) ∈
  {k, k − 1}` — by `splitOff_deficiency_le` (`≤ k`) and `splitOff_deficiency_ge` (`≥ k − 1`);
* the removal `G_v` is at least a `k`-dof-graph — `def(G̃_v) ≥ k` — by
  `removeVertex_deficiency_ge`.

These are the dof-conservation laws the combinatorial induction (KT 4.6–4.9) tracks: each
reduction step (splitting-off or vertex removal) keeps the deficiency `k` invariant or drops
it by exactly one, so the target `k` is preserved along the reduction chain. KT phrases the
"which alternative" refinement (whether `G_v^{ab}` keeps `k` or drops to `k − 1`) via the
fundamental-circuit count of the new edge `ab` through the forest surgery (`rem:kt-lemma-41`);
that refinement is off the Theorem-4.9 critical path (the induction consumes only the
two-sided bound), so it is omitted. -/

/-- **Degrees of freedom under vertex removal and splitting-off** (`lem:dof-tracking`,
KT Lemmas 4.3–4.5). Let `v` be a degree-2 vertex of `G` with neighbours `a, b`, carried by
the two distinct edges `eₐ`/`e_b` that are the *only* edges of `G` incident to `v`
(`hdeg2`), and let `D = bodyBarDim n ≥ 2`. If `G` is a `k`-dof-graph (`def(G̃) = k`), then
with the fresh short-circuit label `e₀ ∉ E(G)`:
* `def(G̃) − 1 ≤ def(G̃_v^{ab}) ≤ def(G̃)` — the splitting-off `G_v^{ab}` is a `k`-dof- or a
  `(k−1)`-dof-graph;
* `def(G̃) ≤ def(G̃_v)` — the removal `G_v` has deficiency `≥ k`.

A packaging lemma over the three deficiency-count bounds `splitOff_deficiency_le`,
`splitOff_deficiency_ge`, `removeVertex_deficiency_ge` (no forests; see `rem:kt-lemma-41`).
These are the dof-conservation laws the induction toward Theorem 4.9 tracks. -/
theorem dof_tracking [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hD : 2 ≤ bodyBarDim n) {v a b : α} {e₀ eₐ e_b : β}
    (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b)
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    (he₀ : e₀ ∉ E(G)) :
    G.deficiency n - 1 ≤ (G.splitOff v a b e₀).deficiency n ∧
      (G.splitOff v a b e₀).deficiency n ≤ G.deficiency n ∧
      G.deficiency n ≤ (G.removeVertex v).deficiency n :=
  have hD1 : 1 ≤ bodyBarDim n := le_trans (by norm_num) hD
  ⟨splitOff_deficiency_ge hD1 hav hbv heab hla hlb hdeg2 he₀,
    splitOff_deficiency_le hD1 hav hbv heab hla hlb hdeg2 he₀,
    removeVertex_deficiency_ge hD hav hbv heab hla hlb hdeg2⟩

/-! ### Every base of `M(G̃)` meets ≥ `D` of the fibers at a degree-2 vertex
(`lem:forest-surgery-split`, the balanced-packing counting half)

The deferred forest surgery (`lem:forest-surgery-split`, KT~4.1) is gated on the
*balanced-packing* assumption Katoh–Tanigawa gloss (`rem:kt-lemma-41`~(2)): that a base of
`M(G̃)` admits a `D`-forest partition with **every** one of the `D` forests meeting the
degree-2 vertex `v`. The pure-counting half of that assumption is *true* and provable on
the green deficiency infrastructure: every base `B` of `M(G̃)` already contains **at least
`D`** of the `2(D−1)` fibers incident to `v`.

The argument is a rank count, **not** a forest reroute. Deleting `v`'s fibers from `B`
lands inside `E((G_v)̃)` (the only `v`-incident `G`-edges are `eₐ`, `e_b` by `hdeg2`, so a
surviving fiber's underlying edge avoids `v`), where the remainder is independent in
`M((G_v)̃) = M(G̃) ↾ E((G_v)̃)` (`matroidMG_restrict_mulTilde`). Hence
`|B ∖ v-fibers| ≤ rank M((G_v)̃)`, and the def\,$=$\,corank bridge
(`isBase_ncard_add_deficiency_eq` / `rank_add_deficiency_eq`) turns
`|B ∩ v-fibers| = |B| − |B ∖ v-fibers|` into
`≥ D + (def((G_v)̃) − def(G̃))`, which is `≥ D` by the removal bound
`removeVertex_deficiency_ge` (KT~4.4, `def(G̃) ≤ def((G_v)̃)`). Needs `2 ≤ bodyBarDim n`.

This reduces the open balanced-packing assumption to a *redistribution* question — given
`≥ D` `v`-fibers (each forest taking at most one `va`-copy and one `vb`-copy), can the `D`
forests be rechosen so each meets `v`? — isolating exactly the combinatorial step KT's
proof omits a justification for (`rem:kt-lemma-41`~(2)); the counting obstruction
("pigeonhole when `h < D`") cannot arise. -/
theorem isBase_vfiber_ncard_ge [DecidableEq β] [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hD : 2 ≤ bodyBarDim n) {v a b : α} {eₐ e_b : β}
    (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b)
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    {B : Set (β × Fin (bodyHingeMult n))} (hB : (G.matroidMG n).IsBase B) :
    bodyBarDim n ≤ (B ∩ (edgeFiber eₐ n ∪ edgeFiber e_b n)).ncard := by
  classical
  haveI : Nonempty α := ⟨a⟩
  have hD1 : 1 ≤ bodyBarDim n := le_trans (by norm_num) hD
  set H := G.removeVertex v with hH
  have hle : H ≤ G := by rw [hH, removeVertex]; exact G.deleteVerts_le
  have hvG : v ∈ V(G) := hla.left_mem
  have hVne : V(G).Nonempty := ⟨v, hvG⟩
  have hVHne : V(H).Nonempty := ⟨a, by rw [hH, vertexSet_removeVertex]; exact ⟨hla.right_mem, hav⟩⟩
  -- `v`-fibers and their cardinality `2(D−1)` is not needed; we only need the count `≥ D`.
  set vfib := edgeFiber eₐ n ∪ edgeFiber e_b n with hvfib
  -- The base lives inside `E(G̃)`.
  have hBground : B ⊆ E(G.mulTilde n) := by
    have := hB.subset_ground; rwa [matroidMG] at this
  -- Step 1: `B ∖ v-fibers ⊆ E((G_v)̃)`.
  have hdiffsub : B \ vfib ⊆ E(H.mulTilde n) := by
    rintro p ⟨hpB, hpnot⟩
    have hpE : p ∈ E(G.mulTilde n) := hBground hpB
    rw [mem_edgeSet_mulTilde] at hpE
    -- `p.1` is a `G`-edge; it is not `eₐ`/`e_b` (else `p ∈ vfib`), hence avoids `v`.
    have hp1ne : p.1 ≠ eₐ ∧ p.1 ≠ e_b := by
      constructor <;> intro hc <;> apply hpnot
      · exact Or.inl (by rw [edgeFiber, Set.mem_setOf_eq]; exact hc)
      · exact Or.inr (by rw [edgeFiber, Set.mem_setOf_eq]; exact hc)
    -- `p.1 ∈ E(G)` survives in `H = G_v`: neither endpoint is `v` (else `p.1 ∈ {eₐ, e_b}`).
    obtain ⟨x, y, hlink⟩ := G.exists_isLink_of_mem_edgeSet hpE
    have hxv : x ≠ v := by rintro rfl; exact absurd (hdeg2 p.1 y hlink) (by tauto)
    have hyv : y ≠ v := by rintro rfl; exact absurd (hdeg2 p.1 x hlink.symm) (by tauto)
    have hlinkH : H.IsLink p.1 x y := by rw [hH, removeVertex_isLink]; exact ⟨hlink, hxv, hyv⟩
    rw [mem_edgeSet_mulTilde]; exact hlinkH.edge_mem
  -- Step 2: `B ∖ v-fibers` is independent in `M((G_v)̃)`, so `|B ∖ v-fibers| ≤ rank M((G_v)̃)`.
  have hdiffindepG : (G.matroidMG n).Indep (B \ vfib) := hB.indep.subset diff_subset
  have hdiffindepH : (H.matroidMG n).Indep (B \ vfib) := by
    rw [← matroidMG_restrict_mulTilde hle n, Matroid.restrict_indep_iff]
    exact ⟨hdiffindepG, hdiffsub⟩
  have hdiffleZ : ((B \ vfib).ncard : ℤ) ≤ ((H.matroidMG n).rank : ℤ) := by
    exact_mod_cast hdiffindepH.ncard_le_rank
  -- Step 3: the two rank/deficiency identities, and `|V(H)| = |V(G)| − 1`.
  have hBrank := G.isBase_ncard_add_deficiency_eq n hD1 hVne hB
  have hHrank := H.rank_add_deficiency_eq n hD1 hVHne
  have hVGpos : 0 < V(G).ncard := Set.ncard_pos (Set.toFinite _) |>.mpr hVne
  have hVHcard : (V(H).ncard : ℤ) = (V(G).ncard : ℤ) - 1 := by
    rw [hH, vertexSet_removeVertex, Set.ncard_diff_singleton_of_mem hvG]
    omega
  rw [hVHcard] at hHrank
  -- Step 4: combine. `|B ∩ vfib| = |B| − |B ∖ vfib| ≥ D + (def(G̃ᵥ) − def(G̃)) ≥ D`.
  have hremoval := removeVertex_deficiency_ge hD hav hbv heab hla hlb hdeg2
  have hsplit : (B ∩ vfib).ncard + (B \ vfib).ncard = B.ncard :=
    Set.ncard_inter_add_ncard_diff_eq_ncard B vfib (Set.toFinite _)
  have hsplitZ : ((B ∩ vfib).ncard : ℤ) + ((B \ vfib).ncard : ℤ) = (B.ncard : ℤ) := by
    exact_mod_cast hsplit
  -- `hdiffleZ : |B∖vfib| ≤ rank M(G̃ᵥ)`; `hHrank : rank M(G̃ᵥ) + def(G̃ᵥ) = D(|V(G)|−1)`;
  -- `hremoval : def(G̃) ≤ def(G̃ᵥ)`; `hBrank : |B| + def(G̃) = D(|V(G)|−1)`; `hsplitZ`.
  have key : (bodyBarDim n : ℤ) ≤ ((B ∩ vfib).ncard : ℤ) := by
    linarith [hdiffleZ, hremoval, hBrank, hsplitZ, hHrank]
  exact_mod_cast key

/-! ### Redistribution kernel: a `v`-avoiding forest accepts any `v`-fiber as a pendant
(`lem:forest-surgery-split`, the balanced-packing redistribution half)

With the *counting* half of the balanced-packing assumption discharged
(`isBase_vfiber_ncard_ge`: a base meets `≥ D` of the `2(D−1)` fibers at the degree-2
vertex `v`), the residual *redistribution* question (`rem:kt-lemma-41`~(2)) is: given the
`D`-forest packing of a base and `≥ D` `v`-fibers among them, can the forests be rechosen
so each meets `v`? This kernel resolves it **affirmatively** — confirming Katoh–Tanigawa's
Lemma 4.1 proof has a *gap, not an error* (the balanced packing is achievable for a base).

The mechanism turns entirely on **`v` having degree 2** in `G`. A forest `F` (a
`(G̃).cycleMatroid`-independent fiber set) that contains no `v`-incident fiber has `v`
isolated in `G̃ ↾ F`; so for any `v`-fiber `x` (a copy of `eₐ` or `e_b`), `x` is a *pendant*
edge in `G̃ ↾ insert x F` — its `v`-endpoint has degree 1 — hence a bridge, and adding a
bridge to a forest keeps it a forest. So `insert x F` is again `(G̃).cycleMatroid`-
independent. The repacking descent (move a `v`-fiber from a forest holding two of them
into a `v`-avoiding forest; the pigeonhole donor always exists since `≥ D` fibers sit in
`< D` non-empty forests) strictly raises the number of `v`-meeting forests, terminating
with every forest meeting `v`. This kernel is the single load-bearing step of that descent;
the descent itself (a `Fin D → Set _` repacking with a well-founded measure) is the
remaining surgery work, off the Theorem-4.9 critical path. -/

/-- **A `v`-avoiding forest accepts a `v`-fiber as a pendant** (`lem:forest-surgery-split`,
balanced-packing redistribution kernel; Katoh–Tanigawa 2011 Lemma 4.1 p.660). Let `F` be a
`(G̃).cycleMatroid`-independent fiber set (a "forest") whose edges all *avoid* `v`
(`∀ p ∈ F, ¬ (G̃).Inc p v`), and let `x` be a fiber joining `v` to a distinct vertex `w`
(`(G̃).IsLink x v w`, `w ≠ v` — a *non-loop* copy of a `v`-incident `G`-edge, exactly the
shape of the `va`/`vb` fibers at a degree-2 vertex). Then `insert x F` is still
`(G̃).cycleMatroid`-independent. (The non-loop hypothesis is essential: a loop at `v` is
itself a cycle, so `insert (loop) F` is never acyclic.)

Proof: by `cycleMatroid_indep`, `insert x F` is acyclic iff `G̃ ↾ insert x F` is a forest;
since `F` is acyclic, it suffices (`IsForest.of_deleteEdges_singleton`) that `x` is a bridge
of `G̃ ↾ insert x F`. `x` is a bridge iff `v` and `w` are disconnected after deleting `x`
(`IsLink.isBridge_iff_not_connBetween`). But in `(G̃ ↾ insert x F) ＼ {x}` the vertex `v` is
*isolated*: its only `insert x F`-edge was `x`, now deleted, and no `F`-edge touches `v`. So
`Isolated.connBetween_iff_eq` forces any `v`–`w` connection to have `v = w`, contradicting
`w ≠ v`. This is the single combinatorial step KT's Lemma 4.1 base-case proof needs and
glosses; it holds because `v` has degree 2 (so a `v`-avoiding forest has `v` isolated). -/
theorem acyclicSet_insert_vfiber_of_not_inc {G : Graph α β} {n : ℕ}
    {F : Set (β × Fin (bodyHingeMult n))} {x : β × Fin (bodyHingeMult n)} {v w : α}
    (hF : ((G.mulTilde n).cycleMatroid).Indep F)
    (hxvw : (G.mulTilde n).IsLink x v w) (hwv : w ≠ v)
    (hFv : ∀ p ∈ F, ¬ (G.mulTilde n).Inc p v) :
    ((G.mulTilde n).cycleMatroid).Indep (insert x F) := by
  classical
  set K := G.mulTilde n with hK
  rw [Graph.cycleMatroid_indep] at hF ⊢
  have hxE : x ∈ E(K) := hxvw.edge_mem
  have hFE : F ⊆ E(K) := hF.1
  -- `insert x F ⊆ E(K)`.
  rw [Graph.isAcyclicSet_iff]
  refine ⟨Set.insert_subset hxE hFE, ?_⟩
  -- It suffices that `x` is a bridge of `K ↾ insert x F`, since deleting it leaves a forest.
  set R := K ↾ insert x F with hR
  have hRforest_del : (R ＼ {x}).IsForest := by
    have hFforest : (K ↾ F).IsForest := (Graph.restrict_isForest_iff hFE).mpr hF
    refine hFforest.anti ?_
    rw [hR, Graph.restrict_deleteEdges]
    refine Graph.restrict_le_restrict (Set.inter_subset_inter_right _ ?_)
    rintro p ⟨hpmem, hpne⟩
    exact (Set.mem_insert_iff.mp hpmem).resolve_left hpne
  have hxlinkR : R.IsLink x v w := by
    rw [hR, Graph.restrict_isLink]; exact ⟨Set.mem_insert _ _, hxvw⟩
  -- `x` is a bridge of `R`: deleting it isolates `v`, so no `v`–`w` path remains.
  have hbridge : R.IsBridge x := by
    rw [hxlinkR.isBridge_iff_not_connBetween]
    intro hconn
    -- `v` is isolated in `R ＼ {x}`.
    have hvisol : (R ＼ {x}).Isolated v := by
      constructor
      · intro e hinc
        rw [hR] at hinc
        have hincK : K.Inc e v ∧ e ∈ insert x F ∧ e ∉ ({x} : Set _) := by
          rw [Graph.deleteEdges_inc, Graph.restrict_inc] at hinc; tauto
        obtain ⟨hincK, hmem, hne⟩ := hincK
        have heF : e ∈ F := (Set.mem_insert_iff.mp hmem).resolve_left (by simpa using hne)
        exact hFv e heF hincK
      · have : v ∈ V(K) := hxvw.left_mem
        rw [Graph.vertexSet_deleteEdges, hR, Graph.vertexSet_restrict]
        exact this
    exact hwv ((hvisol.connBetween_iff_eq).mp hconn).symm
  exact Graph.IsForest.of_deleteEdges_singleton hbridge hRforest_del

/-! ### One rebalancing move of the forest-packing descent
(`lem:forest-surgery-split`, the balanced-packing redistribution descent step)

The two halves of the balanced-packing assumption — the counting half
(`isBase_vfiber_ncard_ge`: a base meets `≥ D` of the `v`-fibers) and the redistribution
kernel (`acyclicSet_insert_vfiber_of_not_inc`: a `v`-avoiding forest absorbs a free
`v`-fiber as a pendant) — assemble into the balanced packing through a **finite repacking
descent**: as long as some forest `Fs j` of the `D`-forest packing of a base avoids `v`,
*move* a spare `v`-fiber `x` into it, raising the count of `v`-meeting forests.

This lemma is the single load-bearing step of that descent: the **move preserves the
packing**. Given a forest packing `Fs : Fin D → Set _` covering `I` (`⋃ i, Fs i = I`, each
`Fs i` a `(G̃).cycleMatroid`-independent fiber set), a designated `v`-avoiding forest
`Fs j` (`∀ p ∈ Fs j, ¬ (G̃).Inc p v`), and a `v`-fiber `x ∈ I` (`(G̃).IsLink x v w`, `w ≠ v`),
the re-choice `Fs' i = insert x (Fs j)` at `i = j` and `Fs i ∖ {x}` elsewhere is again a
forest packing covering `I`. The recipient `Fs j` stays acyclic by the kernel (`x` is a
pendant at the isolated `v`); every donor `Fs i ∖ {x}` stays acyclic as a subset; and the
union is unchanged because `x ∈ I` is re-added at `j` while removed elsewhere. The new
forest `Fs' j` *meets* `v` (it contains `x`), so a descent driven by the count of
`v`-avoiding forests terminates with a balanced packing. The descent's well-founded measure
and the pigeonhole that always supplies such a spare `x` (`≥ D` fibers among `< D` non-empty
forests) are the remaining surgery work, off the Theorem-4.9 critical path. -/
theorem exists_packing_move_of_not_inc {G : Graph α β} {n : ℕ}
    {I : Set (β × Fin (bodyHingeMult n))}
    {Fs : Fin (bodyBarDim n) → Set (β × Fin (bodyHingeMult n))}
    (hcover : ⋃ i, Fs i = I) (hindep : ∀ i, ((G.mulTilde n).cycleMatroid).Indep (Fs i))
    {x : β × Fin (bodyHingeMult n)} {v w : α}
    (hxvw : (G.mulTilde n).IsLink x v w) (hwv : w ≠ v) (hxI : x ∈ I)
    {j : Fin (bodyBarDim n)} (hFjv : ∀ p ∈ Fs j, ¬ (G.mulTilde n).Inc p v) :
    ∃ Fs' : Fin (bodyBarDim n) → Set (β × Fin (bodyHingeMult n)),
      (⋃ i, Fs' i = I) ∧ (∀ i, ((G.mulTilde n).cycleMatroid).Indep (Fs' i)) ∧
        x ∈ Fs' j := by
  classical
  refine ⟨fun i => if i = j then insert x (Fs j) else Fs i \ {x}, ?_, ?_, ?_⟩
  · -- The union is unchanged: `x` is re-added at `j`, removed elsewhere, and `x ∈ I`.
    apply Set.Subset.antisymm
    · rintro p hp
      rw [Set.mem_iUnion] at hp
      obtain ⟨i, hi⟩ := hp
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl] at hi
        rcases Set.mem_insert_iff.mp hi with rfl | hi'
        · exact hxI
        · rw [← hcover]; exact Set.mem_iUnion.mpr ⟨i, hi'⟩
      · simp only [if_neg hij] at hi
        rw [← hcover]; exact Set.mem_iUnion.mpr ⟨i, hi.1⟩
    · rw [← hcover]
      rintro p hp
      rw [Set.mem_iUnion] at hp ⊢
      obtain ⟨i, hi⟩ := hp
      by_cases hpx : p = x
      · exact ⟨j, by rw [if_pos rfl]; exact Set.mem_insert_iff.mpr (Or.inl hpx)⟩
      · by_cases hij : i = j
        · subst hij
          exact ⟨i, by rw [if_pos rfl]; exact Set.mem_insert_iff.mpr (Or.inr hi)⟩
        · exact ⟨i, by simp only [if_neg hij]; exact ⟨hi, by simpa using hpx⟩⟩
  · intro i
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte]
      exact acyclicSet_insert_vfiber_of_not_inc (hindep i) hxvw hwv hFjv
    · simp only [if_neg hij]
      exact (hindep i).subset Set.diff_subset
  · simp only [↓reduceIte]; exact Set.mem_insert _ _

/-! ### Total fiber count of `G̃` (`lem:no-rigid-edge-count`, support)

The KT 4.5(i) edge-count bound (`lem:no-rigid-edge-count`, the prerequisite for the
existence of a reducible degree-2 vertex, KT 4.6) is a statement about `|E(G)|`, while the
matroid `M(G̃)` lives over the fiber set `E(G̃)`. The bridge is the elementary cardinality
identity `|E(G̃)| = (D − 1)·|E(G)|`: the multiplied graph `G̃ = (D−1)·G` replaces each edge
of `G` by `D − 1 = bodyHingeMult n` parallel copies (`Graph.edgeMultiply`), so its edge set
has `(D − 1)·|E(G)|` fibers. This is the per-edge `edgeFiber_ncard` (`|ẽ| = D − 1`) summed
over the `|E(G)|` edges, packaged as a single `mulTilde`-level count. It is the support fact
that lets the matroidal corank bound `corank M(G̃) ≤ D − 2` (the substantive content of KT
4.5(i), still to land — see `notes/Phase20.md` *Hand-off*) be read off as the graph-level
edge bound `(D−1)|E| < D(|V|−1) + (D−1)`, and it also feeds the degree-handshake
`∑_v d(v) = 2|E|` of the average-degree count (KT 4.6, the `F″` sub-step). -/

/-- **The fiber set of `G̃` has `(D − 1)·|E(G)|` elements** (`lem:no-rigid-edge-count`,
support): `|E(G̃)| = bodyHingeMult n · |E(G)| = (D − 1)·|E(G)|`, since the multiplied graph
`G̃ = (D−1)·G` (`mulTilde`, `Graph.edgeMultiply (bodyHingeMult n)`) replaces each edge of `G`
by `D − 1 = bodyHingeMult n` parallel fiber copies. Immediate from
`edgeMultiply_edgeSet_ncard`. This bridges the matroidal corank of `M(G̃)` (which counts
fibers of `E(G̃)`) to the graph-level edge count `|E(G)|` of the KT 4.5(i)/4.6 edge bound. -/
theorem mulTilde_edgeSet_ncard [Finite β] (G : Graph α β) (n : ℕ) :
    E(G.mulTilde n).ncard = bodyHingeMult n * E(G).ncard := by
  rw [mulTilde, edgeMultiply_edgeSet_ncard]

/-! ### The edge-count bound with no proper rigid subgraph (`lem:no-rigid-edge-count`, F′ core)

The matroidal heart of Katoh–Tanigawa 2011 Lemma 4.5(i) (printed p.663). For a minimal
`0`-dof-graph `G` with **no proper rigid subgraph** and `D = bodyBarDim n ≥ 2`, the redundant
fibers of `M(G̃)` concentrate on a single edge-fiber `ẽ` — equivalently the corank is at most
`D − 2` — giving the graph-level edge bound `(D−1)|E| < D(|V|−1) + (D−1)`.

The argument is Katoh–Tanigawa's fundamental-circuit swap (KT eq. 4.3, `Ẽ∖ẽ ⊂ B*`). Fix an
edge `e`, let `h* = minₐ |ẽ ∩ B|` over bases of `M(G̃)`, attained at `B*`; minimality of `G`
forces `h* ≥ 1` (every base meets `ẽ`). For any out-of-`B*` fiber `f ∉ ẽ`, the fundamental
circuit `X = fundCircuit f B*` induces a rigid `G[V(X)]` and — no proper rigid subgraph —
spans `V` (`fundCircuit_inducedSpan_vertexSet_eq`). Then `X ∩ ẽ ≠ ∅`: otherwise `X ⊆ Ẽ∖ẽ` and
`X − ej` (any `ej ∈ X`) is an independent set of full rank `D(|V|−1)` (it is `(D,D)`-tight on
`V(X) = V` by `circuit_induces_isTight`), hence a *base* avoiding `ẽ` — contradicting
minimality. The `X∩ẽ≠∅` step is therefore a direct base-meets-fiber contradiction, **not**
forest reasoning. A base exchange `B = insert f B* − ej` (with `ej ∈ X ∩ ẽ`, independent by
`Indep.mem_fundCircuit_iff`) then has `|B ∩ ẽ| = h* − 1 < h*`, contradicting the choice of
`B*`. So `Ẽ∖ẽ ⊆ B*`, and `|E(G̃)| = |B*| + (|ẽ| − h*) ≤ D(|V|−1) + (D − 2)`. -/

/-- **KT Lemma 4.5(i) edge-count bound, F′ swap core** (`lem:no-rigid-edge-count`;
Katoh–Tanigawa 2011 Lemma 4.5(i), printed p.663). For a minimal `0`-dof-graph `G` with **no
proper rigid subgraph** and `D = bodyBarDim n ≥ 2`,
`(D − 1)·|E(G)| < D·(|V(G)| − 1) + (D − 1)` (in `ℤ`, `|V|−1` written `V(G).ncard - 1`).
Equivalently `corank M(G̃) ≤ D − 2`: the fibers redundant in `M(G̃)` all concentrate on a
single edge-fiber. This is the edge bound Katoh–Tanigawa use to force a low-degree vertex
(`lem:reducible-vertex`).

Proof: the fundamental-circuit swap (KT eq. 4.3). For a fixed edge `e`, the minimum
`h* = minₐ |ẽ ∩ B|` over bases is `≥ 1` by minimality; every out-of-base fiber `f ∉ ẽ` has a
fundamental circuit spanning `V` (`fundCircuit_inducedSpan_vertexSet_eq`) that must meet `ẽ`
(else `X − ej` is a base avoiding `ẽ`, contradicting minimality — a base-meets-fiber step, not
forest reasoning), so a base exchange drops `|B ∩ ẽ|` below `h*` unless `f ∈ B*`. Hence
`Ẽ∖ẽ ⊆ B*`, and `|E(G̃)| = |B*| + (|ẽ| − h*) ≤ D(|V|−1) + (D−2)`. -/
theorem no_rigid_edge_count [DecidableEq β] [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hD : 2 ≤ bodyBarDim n) (hVne : V(G).Nonempty) (hG : G.IsMinimalKDof n 0)
    (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) :
    (bodyHingeMult n : ℤ) * E(G).ncard
      < bodyBarDim n * ((V(G).ncard : ℤ) - 1) + bodyHingeMult n := by
  classical
  have hD1 : 1 ≤ bodyBarDim n := le_trans (by norm_num) hD
  have hHM : (bodyHingeMult n : ℤ) = (bodyBarDim n : ℤ) - 1 := by rw [bodyHingeMult]; omega
  set M := G.matroidMG n with hM
  -- `|E(G̃)| = (D−1)·|E(G)|`.
  have hEcard : E(G.mulTilde n).ncard = bodyHingeMult n * E(G).ncard := mulTilde_edgeSet_ncard G n
  -- Case `E(G) = ∅`: LHS `= 0`, RHS `≥ D−1 ≥ 1 > 0`.
  rcases eq_empty_or_nonempty E(G) with hEempty | hEne
  · rw [hEempty, Set.ncard_empty]
    have hVpos : 1 ≤ V(G).ncard := hVne.ncard_pos
    push_cast
    nlinarith [hD, hVpos]
  -- Pick an edge `e`; its fiber `ẽ = edgeFiber e n ⊆ E(G̃)`, `|ẽ| = D−1`.
  obtain ⟨e, he⟩ := hEne
  have hfiberE : edgeFiber e n ⊆ E(G.mulTilde n) := by
    intro p hp
    rw [mem_edgeSet_mulTilde, (show p.1 = e from hp)]; exact he
  -- The set of bases is finite and nonempty; `h* = minₐ |ẽ ∩ B|` is attained at `Bs`.
  have hbasesFin : {B | M.IsBase B}.Finite := by
    apply Set.Finite.subset ((Set.toFinite E(G.mulTilde n)).finite_subsets)
    intro B hB
    rw [Set.mem_setOf_eq] at hB
    exact hB.subset_ground
  have hbasesNe : {B | M.IsBase B}.Nonempty := M.exists_isBase
  obtain ⟨Bs, hBsmem, hBsmin⟩ :=
    Set.exists_min_image {B | M.IsBase B} (fun B => (edgeFiber e n ∩ B).ncard) hbasesFin hbasesNe
  rw [Set.mem_setOf_eq] at hBsmem
  set hstar := (edgeFiber e n ∩ Bs).ncard with hhstar
  -- `h* ≥ 1` from minimality: every base meets `ẽ`.
  have hstarpos : 1 ≤ hstar := by
    have hmeet := hG.2 Bs hBsmem e he
    rw [Set.inter_comm] at hmeet
    exact hmeet.ncard_pos
  -- Eq 4.3: `E(G̃) ∖ ẽ ⊆ Bs`.
  -- `|Bs| = D(|V|−1)` since `G` is `0`-dof.
  have hBscard : (Bs.ncard : ℤ) = bodyBarDim n * ((V(G).ncard : ℤ) - 1) := by
    have hb := G.isBase_ncard_add_deficiency_eq n hD1 hVne hBsmem
    rw [hM] at hBsmem
    rw [(hG.1 : G.deficiency n = 0)] at hb
    simpa using hb
  have h43 : E(G.mulTilde n) \ edgeFiber e n ⊆ Bs := by
    intro f hf
    by_contra hfB
    -- The fundamental circuit `X = fundCircuit f Bs` is a circuit spanning `V`.
    have hfE : f ∈ M.E := by rw [hM, matroidMG, Matroid.restrict_ground_eq]; exact hf.1
    set X := M.fundCircuit f Bs with hXdef
    have hXcirc : M.IsCircuit X := hBsmem.fundCircuit_isCircuit hfE hfB
    have hspan : V(G.inducedSpan n X) = V(G) :=
      fundCircuit_inducedSpan_vertexSet_eq hD1 hnp hBsmem hf.1 hfB
    have hfiberspan : (G.fiberSpan n X).ncard = V(G).ncard := by
      rw [← vertexSet_inducedSpan G n X, hspan]
    -- Step 3: `X ∩ ẽ ≠ ∅`. Else `X − ej` is a base avoiding `ẽ`, contradicting minimality.
    have hXmeet : (X ∩ edgeFiber e n).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro hXe
      obtain ⟨ej, hej⟩ := hXcirc.nonempty
      -- `X − ej` is independent of full size `D(|V|−1) = |Bs|`, hence a base.
      have hindep : M.Indep (X \ {ej}) := hXcirc.diff_singleton_indep hej
      have htight : (X \ {ej}).ncard + bodyBarDim n = bodyBarDim n * (G.fiberSpan n X).ncard :=
        circuit_induces_isTight (hM ▸ hXcirc) hej
      have hcard : (X \ {ej}).ncard = Bs.ncard := by
        have hVpos : 1 ≤ V(G).ncard := hVne.ncard_pos
        zify [hVpos] at hBscard ⊢
        rw [hfiberspan] at htight
        zify [hVpos] at htight
        linarith [hBscard, htight]
      obtain ⟨B', hB', hsub'⟩ := hindep.exists_isBase_superset
      have heqcard : (X \ {ej}).ncard = B'.ncard := by
        rw [hcard, hBsmem.ncard_eq_ncard_of_isBase hB']
      have hXeb : X \ {ej} = B' :=
        Set.eq_of_subset_of_ncard_le hsub' (le_of_eq heqcard.symm) (hB'.finite)
      have hbase : M.IsBase (X \ {ej}) := hXeb ▸ hB'
      -- But `X − ej ⊆ X ⊆ E(G̃) ∖ ẽ`, so it avoids `ẽ` — contradiction with minimality.
      have hXsub : X ⊆ E(G.mulTilde n) \ edgeFiber e n := by
        intro p hp
        refine ⟨hXcirc.subset_ground hp, fun hpe => ?_⟩
        exact absurd (Set.mem_empty_iff_false p |>.mp (hXe ▸ ⟨hp, hpe⟩)) id
      have hmeet := hG.2 (X \ {ej}) (hM ▸ hbase) e he
      obtain ⟨q, hq⟩ := hmeet
      exact (hXsub (Set.diff_subset hq.1)).2 hq.2
    -- Step 4: `ej ∈ X ∩ ẽ`; exchange `B = insert f (Bs − ej)` drops `|B ∩ ẽ|` below `h*`.
    obtain ⟨ej, hejX, hejfib⟩ := hXmeet
    have hpcl : f ∈ M.closure Bs := by rw [hBsmem.closure_eq]; exact hfE
    have hejdiff : M.Indep (insert f Bs \ {ej}) :=
      (hBsmem.indep.mem_fundCircuit_iff hpcl hfB).mp hejX
    -- `f ∉ ẽ` (since `f ∈ E(G̃) ∖ ẽ`), so `f ≠ ej` (as `ej ∈ ẽ`).
    have hfne : f ≠ ej := fun h => hf.2 (h ▸ hejfib)
    have hinsert_eq : insert f (Bs \ {ej}) = insert f Bs \ {ej} := by
      rw [Set.insert_diff_of_notMem _ (by simp [hfne])]
    have hBnew : M.IsBase (insert f (Bs \ {ej})) :=
      hBsmem.exchange_isBase_of_indep hfB (hinsert_eq ▸ hejdiff)
    -- `|ẽ ∩ B_new| < h*`: removing `ej ∈ ẽ` and adding `f ∉ ẽ` strictly drops the count.
    have hcount : (edgeFiber e n ∩ insert f (Bs \ {ej})).ncard < hstar := by
      have hfnotfib : f ∉ edgeFiber e n := hf.2
      have heq : edgeFiber e n ∩ insert f (Bs \ {ej}) = (edgeFiber e n ∩ Bs) \ {ej} := by
        ext p
        simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_diff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hpfib, rfl | ⟨hpBs, hpne⟩⟩
          · exact absurd hpfib hfnotfib
          · exact ⟨⟨hpfib, hpBs⟩, hpne⟩
        · rintro ⟨⟨hpfib, hpBs⟩, hpne⟩
          exact ⟨hpfib, Or.inr ⟨hpBs, hpne⟩⟩
      rw [heq, hhstar]
      refine Set.ncard_diff_singleton_lt_of_mem ⟨hejfib, ?_⟩ ((Set.toFinite _))
      -- `ej ∈ Bs`: `ej ∈ X ⊆ insert f Bs` and `ej ≠ f` (else `ej = f ∉ ẽ`, but `ej ∈ ẽ`).
      have hejins : ej ∈ insert f Bs := (M.fundCircuit_subset_insert f Bs) hejX
      rcases hejins with hejf | hejBs
      · exact absurd hejf.symm hfne
      · exact hejBs
    exact absurd (hBsmin _ (hM ▸ hBnew)) (by rw [Set.inter_comm] at hcount ⊢; omega)
  -- Final count: `|E(G̃)| = |Bs| + |E(G̃) ∖ Bs| ≤ D(|V|−1) + (D−1) − h* < D(|V|−1) + (D−1)`.
  have hBssub : Bs ⊆ E(G.mulTilde n) := by rw [hM] at hBsmem; exact hBsmem.subset_ground
  -- `|E(G̃) ∖ Bs| + |Bs| = |E(G̃)|`.
  have hsplit : (E(G.mulTilde n) \ Bs).ncard + Bs.ncard = E(G.mulTilde n).ncard :=
    Set.ncard_diff_add_ncard_of_subset hBssub
  -- `E(G̃) ∖ Bs ⊆ ẽ ∖ Bs` (since `E(G̃) ∖ ẽ ⊆ Bs`).
  have hdiffsub : E(G.mulTilde n) \ Bs ⊆ edgeFiber e n \ Bs := by
    intro p hp
    refine ⟨?_, hp.2⟩
    by_contra hpe
    exact hp.2 (h43 ⟨hp.1, hpe⟩)
  have hdiffle : (E(G.mulTilde n) \ Bs).ncard ≤ (edgeFiber e n \ Bs).ncard :=
    Set.ncard_le_ncard hdiffsub (Set.toFinite _)
  -- `|ẽ ∩ Bs| + |ẽ ∖ Bs| = |ẽ| = D − 1`.
  have hfibersplit : (edgeFiber e n ∩ Bs).ncard + (edgeFiber e n \ Bs).ncard = bodyHingeMult n := by
    rw [Set.ncard_inter_add_ncard_diff_eq_ncard _ _ (Set.toFinite _), edgeFiber_ncard]
  -- Assemble: cast to ℤ and close by linear arithmetic.
  have hVpos : 1 ≤ V(G).ncard := hVne.ncard_pos
  rw [hEcard] at hsplit
  zify at hsplit hfibersplit hdiffle hstarpos
  rw [hHM]
  rw [hHM] at hfibersplit
  -- `(D−1)|E| = |Bs| + |E∖Bs| ≤ D(|V|−1) + (D−1−h*) < D(|V|−1) + (D−1)` since `h* ≥ 1`.
  nlinarith [hsplit, hfibersplit, hdiffle, hstarpos, hBscard, hhstar]

/-! ### A low-degree vertex by the average-degree count (`lem:reducible-vertex`, F″ core)

Katoh–Tanigawa 2011 Lemma 4.6 forces a degree-`2` vertex in a minimal `0`-dof-graph with no
proper rigid subgraph. The arithmetic is the average-degree bound `d_avg = 2|E|/|V| <
2D/(D−1) ≤ 3` (for `D = bodyBarDim n ≥ 3`, the molecular regime `n ≥ 2`): with `2|E|/|V| <
3`, the multigraph **handshake** `∑_v deg(v) = 2|E|` (`Graph.handshake_degree_subtype`,
vendored from `apnelson1/Matroid`'s `Graph.degree`/`incFun` API) forces some vertex to have
degree `< 3`, i.e. `≤ 2`. The strict edge bound is the green KT 4.5(i) count
`no_rigid_edge_count`: `(D−1)|E| < D(|V|−1) + (D−1) = D|V| − 1`, which multiplied by `2` and
cancelled against `3(D−1)|V|` (using `D ≥ 3` and `|V| ≥ 1`) gives `2|E| < 3|V|`.

This is the F″ core of `lem:reducible-vertex`. Pairing it with two-edge-connectivity
(`two_le_crossingEdges_of_isKDof_zero`, KT 3.1, which rules out degree `≤ 1`) yields the
degree-`exactly`-2 vertex Theorem 4.9 splits off; that refinement and the full reducibility
packaging are the remaining `lem:reducible-vertex` work. -/

/-- **A minimal `0`-dof-graph with no proper rigid subgraph has a vertex of degree `≤ 2`**
(`lem:reducible-vertex`, F″ core; Katoh–Tanigawa 2011 Lemma 4.6, printed p.664). For
`D = bodyBarDim n ≥ 3` (the molecular regime `n ≥ 2`) and `V(G).Nonempty`, the average-degree
bound `2|E|/|V| < 2D/(D−1) ≤ 3` forces some `v ∈ V(G)` with multigraph degree `G.degree v ≤
2`. Combines the green KT 4.5(i) edge bound (`no_rigid_edge_count`) with the multigraph
handshake `∑_v deg(v) = 2|E|` (`Graph.handshake_degree_subtype`, vendored) via a Finset
pigeonhole (`Finset.exists_lt_of_sum_lt`). The two-edge-connectivity (KT 3.1) needed to
upgrade `≤ 2` to `= 2` is a separate step. -/
theorem exists_degree_le_two [DecidableEq β] [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hD : 3 ≤ bodyBarDim n) (hVne : V(G).Nonempty) (hG : G.IsMinimalKDof n 0)
    (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) :
    ∃ v ∈ V(G), G.degree v ≤ 2 := by
  classical
  haveI : G.Finite := { edgeSet_finite := Set.toFinite _, vertexSet_finite := Set.toFinite _ }
  have hD2 : 2 ≤ bodyBarDim n := le_trans (by norm_num) hD
  -- The KT 4.5(i) edge bound, read over ℤ: `(D−1)|E| < D(|V|−1) + (D−1)`.
  have hedge := no_rigid_edge_count hD2 hVne hG hnp
  -- The handshake `∑_{v ∈ V(G)} deg(v) = 2|E(G)|` over the finite vertex Finset.
  set s := G.vertexSet_finite.toFinset with hs
  have hhand : ∑ v ∈ s, G.degree v = 2 * E(G).ncard := by
    rw [hs, ← finsum_mem_eq_finite_toFinset_sum _ G.vertexSet_finite]
    exact handshake_degree_subtype G
  -- `2|E| < 3|V|` from the edge bound, using `D ≥ 3` and `|V| ≥ 1`.
  have hVpos : 1 ≤ V(G).ncard := hVne.ncard_pos
  have hHM : (bodyHingeMult n : ℤ) = (bodyBarDim n : ℤ) - 1 := by rw [bodyHingeMult]; omega
  have hsum_lt : ∑ v ∈ s, G.degree v < ∑ _v ∈ s, 3 := by
    rw [Finset.sum_const, hhand, smul_eq_mul]
    -- `|s| = |V(G)|`.
    have hscard : s.card = V(G).ncard := by
      rw [hs, ← Set.ncard_eq_toFinset_card _ G.vertexSet_finite]
    rw [hscard]
    -- `2|E| < 3|V|`: cast to ℤ and discharge with the edge bound.
    have h2D : (3 : ℤ) ≤ (bodyBarDim n : ℤ) := by exact_mod_cast hD
    zify
    nlinarith [hedge, hHM, hVpos, h2D]
  obtain ⟨v, hvs, hvdeg⟩ := Finset.exists_lt_of_sum_lt hsum_lt
  exact ⟨v, (by rwa [hs, Set.Finite.mem_toFinset] at hvs), by omega⟩

/-! ### Upgrading degree `≤ 2` to `= 2` via two-edge-connectivity (`lem:reducible-vertex`)

Katoh–Tanigawa 2011 Lemma 4.6 needs a degree-`exactly`-2 vertex, not merely a degree-`≤ 2`
one. The average-degree count (`exists_degree_le_two`) supplies the `≤ 2` half; the
`= 2` upgrade comes from two-edge-connectivity (`two_le_crossingEdges_of_isKDof_zero`, KT
3.1): a `0`-dof-graph admits no bridge cut, so the single-vertex cut `V' = {v}` has at
least two crossing edges, forcing `degree v ≥ 2`.

The bridge from the project's cut form (`crossingEdges`, an edge count) to the vendored
multigraph `Graph.degree` (an endpoint count) is the observation that the crossing edges
of the single-vertex cut `{v}` are exactly the *nonloop* edges at `v`: an edge crosses
`{v}` iff exactly one endpoint is `v`, which is `IsNonloopAt e v`. The multigraph degree
counts each nonloop edge once and each loop twice (`degree_eq_ncard_add_ncard`), so the
crossing count is at most the degree, and `2 ≤ crossing ≤ degree v` pins `degree v ≥ 2`. -/

/-- **Crossing edges of the single-vertex cut are nonloop edges at `v`**
(`lem:reducible-vertex`, cut↔degree bridge). The edges of `G` crossing the two-part cut
`{{v}, V(G) ∖ {v}}` (encoded by `cutLabeling {v} a b` with `a ≠ b`) are exactly the
*nonloop* edges incident to `v`: an edge crosses iff exactly one of its endpoints is `v`.
This is the structural fact linking the project's cut count `d_G(V')` to the vendored
multigraph degree `Graph.degree`. -/
lemma crossingEdges_cutLabeling_singleton_subset {G : Graph α β} {v a b : α}
    [∀ x, Decidable (x ∈ ({v} : Set α))] :
    G.crossingEdges (cutLabeling {v} a b) ⊆ {e | G.IsNonloopAt e v} := by
  rintro e ⟨heG, x, y, hlink, hfxy⟩
  -- `f x ≠ f y` with `f = cutLabeling {v} a b` forces exactly one of `x, y` to equal `v`.
  simp only [cutLabeling, Set.mem_singleton_iff] at hfxy
  rw [Set.mem_setOf_eq]
  by_cases hx : x = v
  · -- `x = v`, so `y ≠ v` (else `f x = f y`); `e` is a nonloop at `v` via the link `v, y`.
    subst hx
    have hy : y ≠ x := by rintro rfl; simp at hfxy
    exact ⟨y, hy, hlink⟩
  · -- `x ≠ v`, so `y = v` (else both map to `b`); `e` is a nonloop at `v` via `v, x`.
    by_cases hy : y = v
    · subst hy
      exact ⟨x, hx, hlink.symm⟩
    · simp [hx, hy] at hfxy

/-- **The cut-crossing count is at most the multigraph degree at `v`**
(`lem:reducible-vertex`, cut↔degree bridge). For the single-vertex cut `{v}`, the number of
crossing edges `d_G({v})` is at most the vendored multigraph degree `Graph.degree v`: the
crossing edges are the nonloop edges at `v` (`crossingEdges_cutLabeling_singleton_subset`),
and the degree counts each nonloop edge at least once
(`Graph.degree_eq_ncard_add_ncard`). -/
lemma crossingEdges_cutLabeling_singleton_ncard_le [Finite β] {G : Graph α β} {v a b : α}
    [∀ x, Decidable (x ∈ ({v} : Set α))] :
    (G.crossingEdges (cutLabeling {v} a b)).ncard ≤ G.degree v := by
  calc (G.crossingEdges (cutLabeling {v} a b)).ncard
      ≤ {e | G.IsNonloopAt e v}.ncard :=
        Set.ncard_le_ncard crossingEdges_cutLabeling_singleton_subset (Set.toFinite _)
    _ ≤ G.degree v := by rw [G.degree_eq_ncard_add_ncard v]; omega

/-- **A minimal `0`-dof-graph with no proper rigid subgraph and `|V| ≥ 2` has a vertex of
degree exactly `2`** (`lem:reducible-vertex`; Katoh–Tanigawa 2011 Lemma 4.6). For
`D = bodyBarDim n ≥ 3` (the molecular regime `n ≥ 2`) and `2 ≤ |V(G)|`, the average-degree
count (`exists_degree_le_two`) gives a vertex `v` of multigraph degree `≤ 2`, and
two-edge-connectivity (`two_le_crossingEdges_of_isKDof_zero`, KT 3.1) rules out
`degree v ≤ 1`: the single-vertex cut `{v}` would otherwise be a bridge cut, contradicting
that a `0`-dof-graph admits none. The bridge `crossingEdges_cutLabeling_singleton_ncard_le`
links the cut count `d_G({v}) ≥ 2` to `degree v ≥ 2`. This is the reducible degree-2 vertex
Theorem 4.9 splits off. -/
theorem exists_degree_eq_two [DecidableEq β] [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hD : 3 ≤ bodyBarDim n) (hV2 : 2 ≤ V(G).ncard) (hG : G.IsMinimalKDof n 0)
    (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) :
    ∃ v ∈ V(G), G.degree v = 2 := by
  classical
  have hD1 : 1 ≤ bodyBarDim n := le_trans (by norm_num) hD
  have hVne : V(G).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  -- The average-degree count supplies a vertex of degree `≤ 2`.
  obtain ⟨v, hvG, hvle⟩ := exists_degree_le_two hD hVne hG hnp
  refine ⟨v, hvG, ?_⟩
  -- Two-edge-connectivity forces `degree v ≥ 2`. Pick a second vertex `b ≠ v` for the cut.
  obtain ⟨b, hbG, hbv⟩ : ∃ b ∈ V(G), b ≠ v := by
    by_contra h
    push Not at h
    -- If every vertex of `G` equals `v`, then `V(G) ⊆ {v}` has `ncard ≤ 1`, contra `≥ 2`.
    have hsub : V(G) ⊆ {v} := fun x hx => h x hx
    have : V(G).ncard ≤ ({v} : Set α).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_singleton] at this
    omega
  -- The single-vertex cut `{v}`: `a = v ∈ {v}`, `b ∉ {v}`, both in `V(G)`.
  have hcross : 2 ≤ (G.crossingEdges (cutLabeling {v} v b)).ncard :=
    two_le_crossingEdges_of_isKDof_zero hD1 hG.1 (Set.mem_singleton v) hvG hbG
      (by simpa using hbv)
  -- The crossing count bounds the degree: `2 ≤ d_G({v}) ≤ degree v ≤ 2`.
  have hle := crossingEdges_cutLabeling_singleton_ncard_le (G := G) (v := v) (a := v) (b := b)
  omega

/-- **Edge-splitting** `H_{ab}^v` (`def:graph-operations`): the inverse of splitting-off.
Subdivide the edge `e₀` of `H` (joining `a` and `b`) by a fresh degree-2 vertex `v`,
replacing `e₀` with the path `a — v — b` carried by two fresh edges `e₁` (joining `a`,
`v`) and `e₂` (joining `v`, `b`). Every edge of `H` other than `e₀` is kept; the new
vertex `v` and the two new edges realize the subdivision. It satisfies
`(H_{ab}^v)_v^{ab} = H` (the `lem:forest-surgery-unsplit` identity, established later). -/
def edgeSplit (H : Graph α β) (a b v : α) (e₀ e₁ e₂ : β) : Graph α β where
  vertexSet := insert v V(H)
  IsLink e x y :=
    (e ≠ e₀ ∧ e ≠ e₁ ∧ e ≠ e₂ ∧ H.IsLink e x y) ∨
      (e = e₁ ∧ ((x = a ∧ y = v) ∨ (x = v ∧ y = a)) ∧ a ∈ V(H)) ∨
      (e = e₂ ∧ e ≠ e₁ ∧ ((x = v ∧ y = b) ∨ (x = b ∧ y = v)) ∧ b ∈ V(H))
  isLink_symm := by
    rintro e he x y (⟨h₀, h₁, h₂, h⟩ | ⟨he₁, hxy, ha⟩ | ⟨he₂, hne, hxy, hb⟩)
    · exact Or.inl ⟨h₀, h₁, h₂, h.symm⟩
    · exact Or.inr <| Or.inl
        ⟨he₁, hxy.symm.imp (fun ⟨p, q⟩ ↦ ⟨q, p⟩) (fun ⟨p, q⟩ ↦ ⟨q, p⟩), ha⟩
    · exact Or.inr <| Or.inr
        ⟨he₂, hne, hxy.symm.imp (fun ⟨p, q⟩ ↦ ⟨q, p⟩) (fun ⟨p, q⟩ ↦ ⟨q, p⟩), hb⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro e x y z w
      (⟨h₀, h₁, h₂, h⟩ | ⟨he, hxy, _⟩ | ⟨he, hne, hxy, _⟩)
      (⟨h₀', h₁', h₂', h'⟩ | ⟨he', hzw, _⟩ | ⟨he', hne', hzw, _⟩)
    · exact h.left_eq_or_eq h'
    · grind
    · grind
    · grind
    · rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hzw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
    · grind
    · grind
    · grind
    · rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hzw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  left_mem_of_isLink := by
    rintro e x y (⟨_, _, _, h⟩ | ⟨_, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), ha⟩ |
        ⟨_, _, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), hb⟩)
    · exact Set.mem_insert_of_mem _ h.left_mem
    · exact Set.mem_insert_of_mem _ ha
    · exact Set.mem_insert _ _
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ hb

@[simp]
lemma vertexSet_edgeSplit (H : Graph α β) (a b v : α) (e₀ e₁ e₂ : β) :
    V(H.edgeSplit a b v e₀ e₁ e₂) = insert v V(H) := rfl

@[simp]
lemma edgeSplit_isLink {H : Graph α β} {a b v : α} {e₀ e₁ e₂ : β} {e : β} {x y : α} :
    (H.edgeSplit a b v e₀ e₁ e₂).IsLink e x y ↔
      (e ≠ e₀ ∧ e ≠ e₁ ∧ e ≠ e₂ ∧ H.IsLink e x y) ∨
        (e = e₁ ∧ ((x = a ∧ y = v) ∨ (x = v ∧ y = a)) ∧ a ∈ V(H)) ∨
        (e = e₂ ∧ e ≠ e₁ ∧ ((x = v ∧ y = b) ∨ (x = b ∧ y = v)) ∧ b ∈ V(H)) := Iff.rfl

/-- **Collapse map** `collapseTo r S` (`def:rigid-contraction`, auxiliary): the vertex
map `α → α` sending every vertex of `S` to the representative `r` and fixing all others.
The vertex identification underlying rigid-subgraph contraction. -/
noncomputable def collapseTo (r : α) (S : Set α) : α → α :=
  open Classical in fun x => if x ∈ S then r else x

/-- **Rigid-subgraph contraction** `G / E(H)` (`def:rigid-contraction`): collapse the
vertex set `V(H)` of a (rigid) subgraph `H ≤ G` to a single representative vertex `r`,
discard the edges of `H`, and retain every other edge of `G` with its endpoints in `V(H)`
redirected to `r`. Realized as `(G.deleteEdges E(H)).map (collapseTo r V(H))`: deleting
`E(H)` discards the rigid subgraph's edges, and `map` identifies `V(H)` to `r`. On the
matroid side this is the matroid contraction `M(G̃) / E(H̃)` restricted to the surviving
fibers (used in `lem:contraction-minimality`). -/
noncomputable def rigidContract (G H : Graph α β) (r : α) : Graph α β :=
  (G.deleteEdges E(H)).map (collapseTo r V(H))

@[simp]
lemma vertexSet_rigidContract (G H : Graph α β) (r : α) :
    V(G.rigidContract H r) = collapseTo r V(H) '' V(G) := rfl

/-- **Rigid-subgraph contraction strictly decreases the vertex count** (`lem:reduction-step`,
the "reduces to a smaller graph" measure). Contracting a subgraph `H ≤ G` whose vertex set
`V(H) ⊆ V(G)` has at least two vertices collapses `V(H)` to the single representative `r`, so
`V(G / E(H)) = collapseTo r V(H) '' V(G)` has cardinality at most `|V(G)| − |V(H)| + 1 <
|V(G)|`. The `2 ≤ |V(H)|` hypothesis is the genuine requirement: collapsing a single-vertex
`H` is a vertex-set no-op (KT's Case I always contracts a proper rigid subgraph spanning at
least two vertices). This is the well-founded measure on which Katoh–Tanigawa 2011's
Theorem 4.9 inducts in the contraction branch. -/
lemma rigidContract_vertexSet_ncard_lt [Finite α] {G H : Graph α β} {r : α}
    (hHsub : V(H) ⊆ V(G)) (hH2 : 2 ≤ V(H).ncard) :
    V(G.rigidContract H r).ncard < V(G).ncard := by
  rw [vertexSet_rigidContract]
  calc (collapseTo r V(H) '' V(G)).ncard
      ≤ ((V(G) \ V(H)) ∪ {r}).ncard := by
        refine Set.ncard_le_ncard ?_ (Set.toFinite _)
        rintro _ ⟨x, hx, rfl⟩
        unfold collapseTo
        split_ifs with hxH
        · exact Or.inr rfl
        · exact Or.inl ⟨hx, hxH⟩
    _ ≤ (V(G) \ V(H)).ncard + 1 := by
        refine le_trans (Set.ncard_union_le _ _) ?_
        simp [Set.ncard_singleton]
    _ < V(G).ncard := by
        have h1 : (V(G) \ V(H)).ncard = V(G).ncard - V(H).ncard :=
          Set.ncard_diff hHsub (Set.toFinite _)
        have hVH : V(H).ncard ≤ V(G).ncard := Set.ncard_le_ncard hHsub (Set.toFinite _)
        omega

/-- **Rigid-subgraph contraction is mathlib's graph contraction** (graph-side brick of
`lem:rigidContract-isMinimalKDof`). The project's `rigidContract G H r =
(G ＼ E(H)).map (collapseTo r V(H))` (delete-then-relabel) coincides with the vendored
`apnelson1/Matroid` graph contraction `(G ＼ E(H)) /[E(H), collapseTo r V(H)]`. The vendored
contraction `H' /[C, φ]` is `(φ ''ᴳ H') ＼ C`, but `H' = G ＼ E(H)` already has its edge set
`E(G) \ E(H)` disjoint from `C = E(H)`, so the trailing `＼ E(H)` is a no-op and
`contract_eq_map_of_disjoint` collapses it to the bare `map` form. This brick is the entry
point of the graph↔matroid bridge for `lem:rigidContract-isMinimalKDof`: it puts
`rigidContract` in the shape `cycleMatroid_contract` (and the `Matroid.Union`-of-`cycleMatroid`
substrate of `matroidMG`) is stated against. -/
lemma rigidContract_eq_contract (G H : Graph α β) (r : α) :
    G.rigidContract H r = (G.deleteEdges E(H)) /[E(H), collapseTo r V(H)] := by
  rw [contract_eq_map_of_disjoint (by simpa using Set.disjoint_sdiff_left), rigidContract]

/-! ## The cycle matroid under the vertex-collapse map (N4b; `lem:rigidContract-isMinimalKDof`)

The graph-side brick of the contraction-minimality bridge: edge multiplication commutes with
rigid-subgraph contraction, and — once the multiplied rigid subgraph `H̃` is preconnected
(`mulTilde_preconnected_of_isKDof_zero`, N4a) — the cycle matroid of the contracted multiplied
graph is the matroid contraction `(G̃).cycleMatroid ／ E(H̃)`. This is the per-cycle-matroid
step the `Matroid.Union` substrate of `matroidMG` is built on (N4c lifts it through the union).
-/

/-- **Edge multiplication commutes with rigid-subgraph contraction** (N4b graph-side brick):
`(G / E(H))̃ = G̃ / E(H̃)`, i.e. `(G.rigidContract H r).mulTilde n = (G.mulTilde n).rigidContract
(H.mulTilde n) r`. Both `deleteEdges` (lifted along the first projection) and the vertex-relabel
`map` commute with the `Fin (D-1)`-indexing of `edgeMultiply`, so multiplying the edges of the
delete-then-relabel contraction agrees with contracting the multiplied graph. The collapse map
`collapseTo r V(H)` is unchanged because `V(H̃) = V(H)`. This puts `mulTilde`-of-`rigidContract`
into the shape `cycleMatroid_contract` (vendored) is stated against. -/
lemma mulTilde_rigidContract (G H : Graph α β) (r : α) (n : ℕ) :
    (G.rigidContract H r).mulTilde n = (G.mulTilde n).rigidContract (H.mulTilde n) r := by
  refine Graph.ext (by simp [mulTilde, rigidContract]) fun p x y => ?_
  obtain ⟨e, i⟩ := p
  simp [mulTilde, rigidContract, edgeMultiply_isLink, Graph.map_isLink, deleteEdges_isLink]

/-- **The collapse map represents the connected components of a preconnected `H̃`** (N4b
brick): for a preconnected multiplied subgraph `H̃` with representative `r ∈ V(H)`, the
vertex-collapse `collapseTo r V(H)` is a representative function for `H̃`'s connectivity
partition. Outside `V(H̃) = V(H)` it is the identity; on `V(H)` it sends everything to `r`,
and preconnectedness makes `r` connected to each such vertex, so `collapseTo` respects the
single connected component. This is the hypothesis the vendored `cycleMatroid_contract`
demands; `mulTilde_preconnected_of_isKDof_zero` (N4a) supplies the preconnectedness. -/
lemma rigidContract_collapseTo_isRepFun {H : Graph α β} {r : α} (hr : r ∈ V(H)) (n : ℕ)
    (hconn : (H.mulTilde n).Preconnected) :
    (H.mulTilde n).connPartition.IsRepFun (collapseTo r V(H)) := by
  have hsupp : ∀ {x : α}, x ∈ (H.mulTilde n).connPartition.supp ↔ x ∈ V(H) := by
    intro x; rw [Graph.connPartition_supp]; simp [mulTilde]
  refine Partition.IsRepFun.mk' _ _ hsupp (fun x hx => ?_) (fun x hx => ?_) (fun x y hxy => ?_)
  · -- `x ∉ V(H)`: `collapseTo` is the identity.
    simp [collapseTo, hx]
  · -- `x ∈ V(H)`: `collapseTo x = r`, related to `x` since `H̃` is preconnected.
    rw [show collapseTo r V(H) x = r from by simp [collapseTo, hx]]
    rw [Graph.connPartition_rel_iff]
    exact hconn x r (show x ∈ V(H.mulTilde n) from hx) (show r ∈ V(H.mulTilde n) from hr)
  · -- related `x, y`: both lie in the support `V(H)`, so both collapse to `r`.
    have hxV : x ∈ V(H) := hsupp.mp hxy.left_mem
    have hyV : y ∈ V(H) := hsupp.mp hxy.right_mem
    simp [collapseTo, hxV, hyV]

/-- **Rigid-subgraph contraction as the direct vendored contraction** (N4b brick): the
delete-then-relabel `rigidContract G H r = (G ＼ E(H)).map (collapseTo r V(H))` *is* the
vendored `G /[E(H), collapseTo r V(H)]` (which expands to `(collapseTo r V(H) ''ᴳ G) ＼ E(H)`),
because the `map` commutes with the `＼ E(H)` (`map_deleteEdges_comm`). The shape
`cycleMatroid_contract` consumes directly — without the spurious inner `＼ E(H)` that the
delete-first phrasing `rigidContract_eq_contract` carries on the contracted matroid side. -/
lemma rigidContract_eq_contract' (G H : Graph α β) (r : α) :
    G.rigidContract H r = G /[E(H), collapseTo r V(H)] := by
  rw [rigidContract, Graph.contract, ← Graph.map_deleteEdges_comm]

/-- **The cycle matroid of a contracted multiplied graph** (N4b, the per-cycle-matroid step;
`lem:rigidContract-isMinimalKDof`). For a subgraph `H ≤ G` whose multiplied graph `H̃` is
preconnected (`mulTilde_preconnected_of_isKDof_zero`, N4a) with representative `r ∈ V(H)`, the
cycle matroid of the multiplied rigid-subgraph contraction equals the matroid contraction:
`((G / E(H))̃).cycleMatroid = (G̃).cycleMatroid ／ E(H̃)`. This is the genuinely new content of
N4b — there is *no* vendored `cycleMatroid`-under-`map` lemma, so it must route through the
vendored `cycleMatroid_contract` (which contracts an edge set rather than relabelling vertices).
The bridge to `cycleMatroid_contract` is the commutation `mulTilde_rigidContract` (edge
multiplication commutes with contraction) plus `rigidContract_eq_contract'` (the contraction is
the vendored `G̃ /[E(H̃), collapseTo r V(H̃)]`), and its `IsRepFun` hypothesis is supplied by
`rigidContract_collapseTo_isRepFun` from N4a's preconnectedness. The result lifts through the
`Matroid.Union` of `matroidMG` in N4c (`ext_indep`). -/
lemma cycleMatroid_mulTilde_rigidContract {H G : Graph α β} (hle : H ≤ G) {r : α} (hr : r ∈ V(H))
    (n : ℕ) (hconn : (H.mulTilde n).Preconnected) :
    ((G.rigidContract H r).mulTilde n).cycleMatroid
      = (G.mulTilde n).cycleMatroid ／ E(H.mulTilde n) := by
  rw [mulTilde_rigidContract, rigidContract_eq_contract',
    show V(H.mulTilde n) = V(H) from rfl]
  exact Graph.cycleMatroid_contract (rigidContract_collapseTo_isRepFun hr n hconn)
    (edgeMultiply_mono hle _)

/-! ## Minimality transport along a contraction (`lem:contraction-minimality`, second half)

The minimality-transport half of KT Lemma 3.5: contracting a (rigid) subgraph `H` of a
minimal `k`-dof-graph `G` leaves the minimality condition intact — every base of the
matroid contraction `M(G̃) / E(H̃)` meets every *surviving* edge-fiber `ẽ`
(`e ∈ E(G) \ E(H)`). This is the contraction analogue of `subgraph_minimality` (KT 3.3),
which transports minimality along a *restriction*; here the transport is along the
contraction, lifting a base `B'` of `M(G̃) / E(H̃)` to a base `B' ∪ J` of `M(G̃)` for an
`M(G̃)`-basis `J` of the contracted-out `E(H̃)` (`Matroid.IsBase.union_isBasis_of_contract`),
applying `G`'s minimality there, and pushing the fiber witness back to `B'` since the
basis part `J ⊆ E(H̃)` is disjoint from every surviving fiber. Stated on the matroid side
`M(G̃) / E(H̃)` — no graph↔matroid `map` correspondence. -/

/-- **A base of a matroid contraction lifts to a base of the matroid** (the abstract
matroid fact behind the contraction analogue of `subgraph_minimality`). For a base `B'`
of `M ／ C` and an `M`-basis `J` of `C` (`M.IsBasis' J C`), the union `B' ∪ J` is a base
of `M`. Via `IsBasis'.contract_eq_contract_delete` (`M ／ C = M ／ J ＼ (C \ J)`): the
deleted `C \ J` consists of loops of `M ／ J` (it lies in `closure J`), so a base `B'` of
`M ／ C` is a base of `M ／ J`, and `Indep.contract_isBase_iff` then gives `B' ∪ J` a base
of `M`. -/
theorem _root_.Matroid.IsBase.union_isBasis_of_contract {γ : Type*} {M : Matroid γ}
    {B' J C : Set γ} (hB' : (M ／ C).IsBase B') (hJ : M.IsBasis' J C) :
    M.IsBase (B' ∪ J) := by
  rw [hJ.contract_eq_contract_delete, Matroid.delete_isBase_iff] at hB'
  -- `C \ J` lies in `closure J`, hence is loops of `M ／ J`.
  have hCcl : C ∩ M.E ⊆ M.closure J := by
    rw [hJ.closure_eq_closure]; exact M.subset_closure_of_subset' Set.inter_subset_left
  have hsub : (M ／ J).E \ (M ／ J).loops ⊆ (M ／ J).E \ (C \ J) := by
    rw [Matroid.contract_loops_eq, Matroid.contract_ground]
    refine fun x hx ↦ ⟨hx.1, fun hxc ↦ hx.2 ⟨hCcl ⟨hxc.1, hx.1.1⟩, hxc.2⟩⟩
  -- So `(M ／ J).E \ (C \ J)` is spanning in `M ／ J`, making `B'` a base of `M ／ J`.
  have hsp : (M ／ J).Spanning ((M ／ J).E \ (C \ J)) := by
    rw [Matroid.spanning_iff_closure_eq Set.diff_subset]
    refine subset_antisymm (Matroid.closure_subset_ground _ _) ?_
    calc (M ／ J).E = (M ／ J).closure ((M ／ J).E \ (M ／ J).loops) := by
            rw [Matroid.closure_diff_loops_eq, Matroid.closure_ground]
      _ ⊆ (M ／ J).closure ((M ／ J).E \ (C \ J)) := Matroid.closure_subset_closure _ hsub
  have hBJ : (M ／ J).IsBase B' := hB'.isBase_of_spanning hsp
  rw [hJ.indep.contract_isBase_iff] at hBJ
  exact hBJ.1

/-- **Minimality transports along a contraction** (`lem:contraction-minimality`, second
half; Katoh–Tanigawa 2011 Lemma 3.5). For a subgraph `H` of a minimal `k`-dof-graph `G`,
every base `B'` of the matroid contraction `M(G̃) ／ E(H̃)` meets every *surviving*
edge-fiber `ẽ` of an edge `e ∈ E(G) \ E(H)`: `B' ∩ ẽ ≠ ∅`. This is the contraction
analogue of `subgraph_minimality` (KT 3.3, restriction transport). (No `H ≤ G` hypothesis
is needed: the argument is entirely on the matroid contraction `M(G̃) ／ E(H̃)`, using only
that the contracted-out fibers `E(H̃)` are the multiplied edges of `H` and the surviving
edge `e ∉ E(H)`; `H ≤ G` enters only the deficiency-conservation half.)

A base `B'` of `M(G̃) ／ E(H̃)` is disjoint from `E(H̃)` (it lies in the contraction's
ground `E(G̃) \ E(H̃)`). Picking an `M(G̃)`-basis `J` of `E(H̃)`, the union `B' ∪ J` is a
base of `M(G̃)` (`Matroid.IsBase.union_isBasis_of_contract`), so `G`'s minimality gives
`(B' ∪ J) ∩ ẽ ≠ ∅`. The surviving fiber `ẽ` (with `e ∉ E(H)`) is disjoint from `E(H̃) ⊇ J`
(`p ∈ E(H̃) ↔ p.1 ∈ E(H)`, but `p.1 = e ∉ E(H)`), so the witness lands in `B'`. -/
theorem contract_minimality_transport [DecidableEq β] [Finite α] [Finite β] {H G : Graph α β}
    {n : ℕ} {k : ℤ} (hG : G.IsMinimalKDof n k) {B' : Set (β × Fin (bodyHingeMult n))}
    (hB' : ((G.matroidMG n) ／ E(H.mulTilde n)).IsBase B') {e : β} (heG : e ∈ E(G))
    (heH : e ∉ E(H)) : (B' ∩ edgeFiber e n).Nonempty := by
  classical
  -- `B'` lives in the contraction's ground `E(G̃) \ E(H̃)`, so it is disjoint from `E(H̃)`.
  have hB'ground : B' ⊆ E(G.mulTilde n) \ E(H.mulTilde n) := by
    have := hB'.subset_ground
    rwa [Matroid.contract_ground, matroidMG, Matroid.restrict_ground_eq] at this
  -- The surviving fiber `ẽ` is disjoint from `E(H̃)` (its edges all have `.1 = e ∉ E(H)`).
  have hfiberdisj : edgeFiber e n ⊆ {p | p.1 ∉ E(H)} := by
    intro p hp; rw [Set.mem_setOf_eq, (show p.1 = e from hp)]; exact heH
  -- Pick an `M(G̃)`-basis `J` of `E(H̃)`; then `B' ∪ J` is a base of `M(G̃)`.
  obtain ⟨J, hJ⟩ := (G.matroidMG n).exists_isBasis' E(H.mulTilde n)
  have hbase : (G.matroidMG n).IsBase (B' ∪ J) := hB'.union_isBasis_of_contract hJ
  -- `e ∈ E(G̃)` as the fiber lies in `E(G̃)`, so `G`'s minimality applies to `B' ∪ J`.
  obtain ⟨p, hp⟩ := hG.2 (B' ∪ J) hbase e heG
  -- The witness `p ∈ (B' ∪ J) ∩ ẽ` cannot lie in `J ⊆ E(H̃)`, so it is in `B'`.
  refine ⟨p, ?_, hp.2⟩
  rcases hp.1 with hpB' | hpJ
  · exact hpB'
  · have hpH : p.1 ∈ E(H) := by
      have hmem := hJ.subset hpJ
      rwa [mem_edgeSet_mulTilde] at hmem
    exact absurd hpH (hfiberdisj hp.2)

/-! ## Rigid-subgraph contraction preserves minimality (`lem:contraction-minimality`)

The full Katoh–Tanigawa Lemma 3.5: contracting a *proper rigid* subgraph `H` of a minimal
`k`-dof-graph `G` again yields a minimal `k`-dof-graph, with the deficiency unchanged. The
assembly packages the two halves already in hand. **No graph↔matroid `map` correspondence
is needed** — both halves are stated against the matroid contraction `M(G̃) / E(H̃)`, and so
is the assembled conclusion: the matroid contraction is itself a *minimal `k`-dof matroid*,
i.e. it has corank `def(G̃)` at the reduced ambient `D(|V(G)| − |V(H)|)`
(`contract_matroidMG_deficiency_eq`, deficiency conservation) **and** every base of it meets
every surviving edge-fiber `ẽ` (`contract_minimality_transport`, minimality transport). This
is the Case-I engine of the algebraic induction (Phases 21–23). -/

/-- **Rigid-subgraph contraction preserves minimality** (`lem:contraction-minimality`;
Katoh–Tanigawa 2011 Lemma 3.5, full form). For a *proper rigid* subgraph `H` of a minimal
`k`-dof-graph `G` (`hG : G.IsMinimalKDof n k`, `hH : H.IsProperRigidSubgraph G n`) with
`D = bodyBarDim n ≥ 1`, the matroid contraction `M(G̃) / E(H̃)` is a *minimal `k`-dof
matroid* at the reduced ambient `D(|V(G)| − |V(H)|)`:

* **deficiency conservation** — its corank at `D(|V(G)| − |V(H)|)` equals `def(G̃) = k`:
  `D(|V(G)| − |V(H)|) − rank(M(G̃) / E(H̃)) = k`;
* **minimality transport** — every base `B'` of `M(G̃) / E(H̃)` meets every surviving
  edge-fiber `ẽ` of an edge `e ∈ E(G) \ E(H)`: `B' ∩ ẽ ≠ ∅`.

The assembly is the conjunction of `contract_matroidMG_deficiency_eq` (rewriting its
`G.deficiency n` RHS to `k` via `hG.1`) and `contract_minimality_transport`. Stated on the
matroid side directly — no graph↔matroid `map` correspondence, matching how Katoh–Tanigawa's
proof reasons. This is the Case-I engine of the algebraic induction (Phases 21–23). -/
theorem contraction_isMinimalKDof [DecidableEq β] [Finite α] [Finite β] {H G : Graph α β}
    {n : ℕ} {k : ℤ} (hD : 1 ≤ bodyBarDim n) (hG : G.IsMinimalKDof n k)
    (hH : H.IsProperRigidSubgraph G n) (hVGne : V(G).Nonempty) :
    bodyBarDim n * ((V(G).ncard : ℤ) - (V(H).ncard : ℤ))
        - ((G.matroidMG n ／ E(H.mulTilde n)).rank : ℤ) = k ∧
      ∀ B', ((G.matroidMG n) ／ E(H.mulTilde n)).IsBase B' →
        ∀ e ∈ E(G), e ∉ E(H) → (B' ∩ edgeFiber e n).Nonempty := by
  obtain ⟨⟨hle, hrigid⟩, hVHne, _⟩ := hH
  refine ⟨?_, fun B' hB' e heG heH ↦ contract_minimality_transport hG hB' heG heH⟩
  -- Deficiency conservation, with `def(G̃) = k` from `G`'s `k`-dof hypothesis.
  have hdef := contract_matroidMG_deficiency_eq hle n hD hVHne hVGne hrigid
  rwa [hG.1] at hdef

/-! ## Acyclicity transport across the short-circuit (`lem:forest-surgery-split`, surgery crux)

The genuine combinatorial crux of the Katoh–Tanigawa 2011 Lemma 4.1 forest surgery: the
reroute of the `D` forests across the degree-2 vertex `v` must **preserve acyclicity** —
each rerouted forest of the splitting-off `G_v^{ab}` is still a forest. The fibers of the
multiplied splitting-off `G̃_v^{ab}` split into the *fresh* short-circuit fiber `ã̃b =
edgeFiber e₀ n` (the `D-1` parallel copies of the new edge `e₀`) and the *surviving* fibers
(`p.1 ≠ e₀`), which are exactly the fibers of `G̃` whose underlying `G`-edge avoids `v`.

The surviving part transports cleanly: deleting the fresh fiber from `G̃_v^{ab}` gives a
subgraph of `G̃` (`mulTilde_splitOff_deleteFiber_le`), because every non-`e₀` link of the
splitting-off is a link of `G` (it keeps `G`'s `e ≠ e₀` links avoiding `v`). So a
cycle-matroid-acyclic fiber set of `G̃_v^{ab}` that avoids `ã̃b` is acyclic in `G̃`
(`isAcyclicSet_mulTilde_of_splitOff_of_disjoint`) — the half of the surgery's
acyclicity-preservation that needs no rerouting (the forests with `dᶠ(v) ≤ 1`, which drop
their `v`-edge rather than swap onto `ã̃b`). The rerouting half (`dᶠ(v) = 2` forests
swapping their two `v`-edges for one `ã̃b` copy, with the `v`-traversing path lift) is landed
as `isAcyclicSet_splitOff_reroute` below; what remains of the still-red
`lem:forest-surgery-split` is only the per-`D`-forest bookkeeping assembly. -/

/-- **Deleting the fresh fiber from the multiplied splitting-off lands inside `G̃`**
(`lem:forest-surgery-split`, surgery crux). The multiplied splitting-off `G̃_v^{ab}` with
its fresh short-circuit fiber `ã̃b = edgeFiber e₀ n` deleted is a subgraph of the multiplied
original `G̃ = (D-1)·G`. Every surviving fiber `p` (`p.1 ≠ e₀`) of `G̃_v^{ab}` is a copy of
an `e₀`-distinct edge of `G` avoiding `v`, so it carries exactly the same link in `G̃` — the
splitting-off only *adds* the fresh `e₀`-fiber and *removes* the `v`-incident fibers, both of
which lie outside the deleted-fiber subgraph. This is the structural fact the acyclicity
transport `isAcyclicSet_mulTilde_of_splitOff_of_disjoint` runs on. -/
lemma mulTilde_splitOff_deleteFiber_le {G : Graph α β} {v a b : α} {e₀ : β} (n : ℕ) :
    ((G.splitOff v a b e₀).mulTilde n).deleteEdges (edgeFiber e₀ n) ≤ G.mulTilde n := by
  refine ⟨?_, ?_⟩
  · -- Vertex sets: `V(G̃_v^{ab}) = V(G) \ {v} ⊆ V(G) = V(G̃)`.
    intro x hx
    simp only [vertexSet_deleteEdges] at hx
    exact Set.diff_subset hx
  · -- Links: a surviving link of `G̃_v^{ab}` (`p.1 ≠ e₀`) is a link of `G̃`.
    intro p x y hp
    simp only [deleteEdges_isLink, mulTilde_isLink, splitOff_isLink] at hp
    obtain ⟨hlink | hlink, hpfiber⟩ := hp
    · simpa only [mulTilde_isLink] using hlink.2.1
    · -- The `e₀`-fiber case is excluded: `p.1 = e₀` puts `p ∈ edgeFiber e₀ n`.
      exact absurd (show p ∈ edgeFiber e₀ n from hlink.1) hpfiber

/-- **The multiplied vertex-removal lands inside the multiplied splitting-off**
(`lem:forest-surgery-split`, surgery crux, reverse inclusion). The converse companion of
`mulTilde_splitOff_deleteFiber_le`: the multiplied vertex-removal `(G_v)̃ = ((G - v))̃` is a
subgraph of the multiplied splitting-off `G̃_v^{ab}`, *provided the short-circuit edge `e₀`
is fresh* (`e₀ ∉ E(G)`): `(G.removeVertex v).mulTilde n ≤ (G.splitOff v a b e₀).mulTilde n`.
Both graphs carry the vertex set `V(G) \ {v}`; every fiber `p` of `(G_v)̃` is a copy of an
edge of `G` avoiding `v` (`removeVertex_isLink`), and freshness forces `p.1 ≠ e₀`, so
`splitOff` keeps that very link (its first disjunct). This is the structural fact the
rerouting half of the surgery runs on: the part of a `G̃`-forest avoiding `v` (the forests
with `dᶠ(v) ≤ 1` reduced to `G_v`) transports verbatim into `G̃_v^{ab}` — only the
`v`-traversing tree-path of a `dᶠ(v) = 2` forest needs the `ã̃b` swap. -/
lemma mulTilde_removeVertex_le_splitOff {G : Graph α β} {v a b : α} {e₀ : β} (n : ℕ)
    (he₀ : e₀ ∉ E(G)) :
    (G.removeVertex v).mulTilde n ≤ (G.splitOff v a b e₀).mulTilde n := by
  refine ⟨?_, ?_⟩
  · -- Vertex sets: both are `V(G) \ {v}` definitionally.
    intro x hx
    exact hx
  · -- Links: a link of `(G_v)̃` (a `v`-avoiding `G`-link) is a `splitOff` link (first disjunct).
    intro p x y hp
    simp only [mulTilde_isLink, removeVertex_isLink] at hp ⊢
    obtain ⟨hlink, hxv, hyv⟩ := hp
    rw [splitOff_isLink]
    refine Or.inl ⟨?_, hlink, hxv, hyv⟩
    -- `p.1 ≠ e₀`: `p.1 ∈ E(G)` (it carries the link `hlink`) but `e₀ ∉ E(G)`.
    rintro rfl; exact he₀ hlink.edge_mem

/-- **The surviving fibers of the multiplied splitting-off are exactly `E((G_v)̃)`**
(`lem:reduction-step`, splitting-off minimality transport; Katoh–Tanigawa 2011 Lemmas 4.7–4.8,
ground-set bridge). With the short-circuit edge `e₀` fresh (`e₀ ∉ E(G)`), the multiplied
splitting-off `G̃_v^{ab}` has ground set the disjoint union of the fresh short-circuit fiber
`ã̃b = edgeFiber e₀ n` and the surviving fibers, and the surviving fibers
(`E(G̃_v^{ab}) ∖ ã̃b`) are *precisely* the fibers of the multiplied vertex-removal
`(G_v)̃ = ((G − v))̃`:
`E((G_v^{ab}))̃ ∖ ã̃b = E((G_v))̃`.

This is the ground-set decomposition the by-hand base correspondence of KT 4.8 runs on:
splitting-off only *adds* the fresh `e₀`-fiber to and *removes* the two `v`-incident fibers
from `G̃`, so deleting the fresh fiber recovers exactly the `v`-free fibers — which are the
ground set of `M((G_v)̃)`. Sharpens the one-sided inclusions
`mulTilde_splitOff_deleteFiber_le` / `mulTilde_removeVertex_le_splitOff` to the edge-set
equality the base lift needs to identify the surviving matroid's ground set. The two `⊆`
directions are: a non-`e₀` fiber of `G̃_v^{ab}` carries a `v`-avoiding `G`-link (so its edge
lies in `E(G_v)`), and conversely a fiber of `(G_v)̃` is `v`-free with a fresh-distinct edge
(forced by `e₀ ∉ E(G)`), hence kept by `splitOff`'s first disjunct. -/
lemma edgeSet_mulTilde_splitOff_diff_fiber {G : Graph α β} {v a b : α} {e₀ : β} (n : ℕ)
    (he₀ : e₀ ∉ E(G)) :
    E((G.splitOff v a b e₀).mulTilde n) \ edgeFiber e₀ n = E((G.removeVertex v).mulTilde n) := by
  ext p
  simp only [Set.mem_diff, edgeFiber, Set.mem_setOf_eq, mem_edgeSet_mulTilde,
    edgeSet_splitOff, Set.mem_union]
  rw [removeVertex, edgeSet_deleteVerts]
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨(⟨rfl, _⟩ | ⟨_, x, y, hl, hx, hy⟩), hpne⟩
    · exact absurd rfl hpne
    · exact ⟨x, y, hl, hx, hy⟩
  · rintro ⟨x, y, hl, hx, hy⟩
    refine ⟨Or.inr ⟨?_, x, y, hl, hx, hy⟩, ?_⟩
    · rintro rfl; exact he₀ hl.edge_mem
    · rintro rfl; exact he₀ hl.edge_mem

/-- **A forest of the multiplied vertex-removal is a forest of the multiplied splitting-off**
(`lem:forest-surgery-split`, surgery crux, reverse acyclicity transport; Katoh–Tanigawa 2011
Lemma 4.1). The reverse companion of `isAcyclicSet_mulTilde_of_splitOff_of_disjoint`: any
cycle-matroid-acyclic fiber set `F` of the multiplied vertex-removal `(G_v)̃ = ((G - v))̃` is
acyclic in the multiplied splitting-off `G̃_v^{ab}`, whenever the short-circuit edge `e₀` is
fresh (`e₀ ∉ E(G)`):
`((G - v))̃.cycleMatroid.Indep F → ((G_v^{ab}))̃.cycleMatroid.Indep F`.

This is the half of the surgery's acyclicity-preservation that transports *into* `G̃_v^{ab}`
without rerouting: a forest of `G̃` reduced to the vertex-removal `G_v` (its `v`-edges
dropped) is a forest of `G̃_v^{ab}` verbatim, because deleting `v` strictly precedes the
short-circuit. No disjointness hypothesis is needed — `(G_v)̃` carries no `v`-incident fibers
at all, so it sits below `G̃_v^{ab}` unconditionally (`mulTilde_removeVertex_le_splitOff`); the
`v`-traversing tree-path that *does* need the `ã̃b` swap is the residual rerouting crux. -/
lemma isAcyclicSet_mulTilde_splitOff_of_removeVertex {G : Graph α β} {v a b : α} {e₀ : β}
    {n : ℕ} (he₀ : e₀ ∉ E(G)) {F : Set (β × Fin (bodyHingeMult n))}
    (hF : ((G.removeVertex v).mulTilde n).cycleMatroid.Indep F) :
    ((G.splitOff v a b e₀).mulTilde n).cycleMatroid.Indep F := by
  rw [cycleMatroid_indep] at hF ⊢
  exact hF.mono (mulTilde_removeVertex_le_splitOff n he₀)

/-- **Acyclicity transports across the short-circuit** (`lem:forest-surgery-split`, surgery
crux; Katoh–Tanigawa 2011 Lemma 4.1). A fiber set `F` that is cycle-matroid-independent
(acyclic) in the multiplied splitting-off `G̃_v^{ab}` and **disjoint from the fresh fiber**
`ã̃b = edgeFiber e₀ n` is acyclic in the multiplied original `G̃ = (D-1)·G`:
`(G̃_v^{ab}).cycleMatroid.Indep F → Disjoint F (edgeFiber e₀ n) → (G̃).cycleMatroid.Indep F`.

This is the half of the surgery's acyclicity-preservation that needs no rerouting — the
forests with `dᶠ(v) ≤ 1` at the degree-2 vertex `v`, which drop their single `v`-edge and
survive verbatim inside `G̃`. The transport routes through `mulTilde_splitOff_deleteFiber_le`
(deleting `ã̃b` from `G̃_v^{ab}` lands in `G̃`): `F`'s disjointness from `ã̃b` means `F` lives
in that deleted subgraph, where acyclicity is monotone up to `G̃` (`IsAcyclicSet.mono`,
`Graph.cycleMatroid_indep`). The rerouting half (the `dᶠ(v) = 2` forests swapping their two
`v`-edges for one `ã̃b` copy) is the residual crux of the still-red surgery. -/
lemma isAcyclicSet_mulTilde_of_splitOff_of_disjoint {G : Graph α β} {v a b : α} {e₀ : β}
    {n : ℕ} {F : Set (β × Fin (bodyHingeMult n))}
    (hF : ((G.splitOff v a b e₀).mulTilde n).cycleMatroid.Indep F)
    (hdisj : Disjoint F (edgeFiber e₀ n)) :
    (G.mulTilde n).cycleMatroid.Indep F := by
  rw [cycleMatroid_indep] at hF ⊢
  -- `F` is acyclic in `G̃_v^{ab}` and avoids the deleted fiber, hence acyclic in the
  -- deleted subgraph `G̃_v^{ab} ＼ ã̃b`.
  have hFdel : (((G.splitOff v a b e₀).mulTilde n).deleteEdges (edgeFiber e₀ n)).IsAcyclicSet F :=
      by
    refine ⟨?_, fun C hC hCF ↦ ?_⟩
    · rw [edgeSet_deleteEdges]
      exact Set.subset_diff.mpr ⟨hF.1, hdisj⟩
    · -- A cyclic walk in the deleted subgraph is one in `G̃_v^{ab}`, contradicting `hF`.
      exact hF.2 C (hC.of_le (deleteEdges_le)) hCF
  -- Transport acyclicity up the subgraph `… ＼ ã̃b ≤ G̃`.
  exact hFdel.mono (mulTilde_splitOff_deleteFiber_le n)

/-! ## Degree of a vertex in a fiber set (`lem:forest-surgery-split`, degree substrate)

The forest surgery of Katoh–Tanigawa 2011 Lemma 4.1 reroutes the `D` edge-disjoint
forests `F₀, …, F_{D-1}` of an `M(G̃)`-independent set across a degree-2 vertex `v`.
Per forest `Fᵢ`, the reroute is driven by the **degree of `v` in `Fᵢ`** — the number
`dᶠ(v)` of fibers of `Fᵢ` incident to `v` in `G̃`. KT's surgery splits the forests by
`dᶠ(v) ∈ {0, 1, 2}` (a forest meeting `v` at `0` fibers is untouched; at `1` fiber its
`v`-edge is dropped; at `2` fibers its two `v`-edges are swapped for one `ãb` copy),
and the `< D − 1` short-circuit-copy count `h' ≤ D − 2` is read off these per-forest
degrees.

This subsection lands the **degree substrate** the surgery bottoms out on: the set of
fibers of `G̃` incident to `v` (`fiberAtVertex`), the reduction of `G̃`-incidence to
`G`-incidence at the underlying edge (`mulTilde_inc`), the per-fiber-set degree
`fiberDegree`, and the count `|fibers at v in E(G̃)| = (D − 1)·|incident G-edges at v|`
(`fiberAtVertex_inter_edgeSet_ncard`) — so a *degree-2* vertex `v` of `G` has exactly
`2(D − 1)` incident fibers, the quantity the `h' ≤ D − 2` bound is counted against. The
acyclicity-preserving reroute itself (a `G̃ᵥᵃᵇ`-cycle through `ãb` lifts to a
`v`-traversing path of `G̃`) is landed as `isAcyclicSet_splitOff_reroute` (reroute wiring
step 2); what remains of the still-red `lem:forest-surgery-split` is only the per-`D`-forest
bookkeeping assembly. -/

/-- **The fibers of `G̃` incident to a vertex `v`** (`lem:forest-surgery-split`, degree
substrate): the set of fibers `p` of the multiplied graph `G̃ = (D-1)·G` with `v` as an
endpoint. These are the fibers the Katoh–Tanigawa 2011 Lemma 4.1 forest surgery reroutes
when it short-circuits the two edges through a degree-2 vertex `v`. -/
def fiberAtVertex (G : Graph α β) (n : ℕ) (v : α) : Set (β × Fin (bodyHingeMult n)) :=
  {p | (G.mulTilde n).Inc p v}

/-- **`G̃`-incidence reduces to `G`-incidence at the underlying edge**
(`lem:forest-surgery-split`, degree substrate): a fiber `p` of `G̃ = (D-1)·G` is incident
to a vertex `v` exactly when its underlying `G`-edge `p.1` is. Each parallel copy `p` of
an edge `e` of `G` carries the same incidences as `e`. -/
lemma mulTilde_inc {G : Graph α β} {n : ℕ} {p : β × Fin (bodyHingeMult n)} {v : α} :
    (G.mulTilde n).Inc p v ↔ G.Inc p.1 v := by
  rw [mulTilde, edgeMultiply_inc]

@[simp]
lemma mem_fiberAtVertex {G : Graph α β} {n : ℕ} {v : α} {p : β × Fin (bodyHingeMult n)} :
    p ∈ G.fiberAtVertex n v ↔ G.Inc p.1 v := by
  rw [fiberAtVertex, Set.mem_setOf_eq, mulTilde_inc]

/-- **The fibers at `v` are the copies of `v`'s incident edges**
(`lem:forest-surgery-split`, degree substrate): inside `E(G̃)`, the fibers incident to
`v` are exactly the fibers `ẽ` of the `G`-edges `e` incident to `v`. So the fibers at `v`
in `E(G̃)` partition by the underlying incident edge. -/
lemma fiberAtVertex_inter_edgeSet {G : Graph α β} {n : ℕ} {v : α} :
    G.fiberAtVertex n v ∩ E(G.mulTilde n) =
      {p : β × Fin (bodyHingeMult n) | p.1 ∈ {e | G.Inc e v}} := by
  ext p
  simp only [Set.mem_inter_iff, mem_fiberAtVertex, mem_edgeSet_mulTilde,
    Set.mem_setOf_eq]
  exact ⟨fun ⟨hinc, _⟩ ↦ hinc, fun hinc ↦ ⟨hinc, hinc.edge_mem⟩⟩

/-- **Count of the fibers at `v`** (`lem:forest-surgery-split`, degree substrate;
Katoh–Tanigawa 2011 Lemma 4.1). The number of fibers of `G̃ = (D-1)·G` incident to `v`
inside `E(G̃)` is `(D − 1)` times the number of `G`-edges incident to `v`:
`|fibers at v in E(G̃)| = bodyHingeMult n · |{e | G.Inc e v}|`. For a degree-2 vertex `v`
of `G` (exactly two incident edges) this is `2(D − 1)`, the total fiber count the surgery
distributes among the `D` forests and counts the `h' ≤ D − 2` short-circuit copies
against. -/
lemma fiberAtVertex_inter_edgeSet_ncard [Finite β] {G : Graph α β} {n : ℕ} {v : α} :
    (G.fiberAtVertex n v ∩ E(G.mulTilde n)).ncard
      = bodyHingeMult n * {e | G.Inc e v}.ncard := by
  rw [fiberAtVertex_inter_edgeSet]
  have hprod : {p : β × Fin (bodyHingeMult n) | p.1 ∈ {e | G.Inc e v}}
      = {e | G.Inc e v} ×ˢ (Set.univ : Set (Fin (bodyHingeMult n))) := by
    ext ⟨e, i⟩; simp
  rw [hprod, Set.ncard_prod, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin,
    mul_comm]

/-- **The degree of `v` in a fiber set `F`** (`lem:forest-surgery-split`, degree
substrate): the number `dᶠ(v)` of fibers of `F` incident to `v` in `G̃ = (D-1)·G`. This
is the per-forest quantity Katoh–Tanigawa 2011 Lemma 4.1's surgery splits on
(`dᶠ(v) ∈ {0, 1, 2}` when `v` is a degree-2 vertex), driving the reroute of each forest
`Fᵢ` across the short-circuit `ab`. -/
noncomputable def fiberDegree (G : Graph α β) (n : ℕ) (v : α)
    (F : Set (β × Fin (bodyHingeMult n))) : ℕ :=
  (F ∩ G.fiberAtVertex n v).ncard

/-- **Degree monotonicity** (`lem:forest-surgery-split`, degree substrate): the degree of
`v` in a subset `F' ⊆ F` is at most its degree in `F`. The surgery drops the `v`-edges of
each forest, reducing `dᶠ(v)`; this is the monotonicity that bounds the rerouted degrees. -/
lemma fiberDegree_mono [Finite β] {G : Graph α β} {n : ℕ} {v : α}
    {F' F : Set (β × Fin (bodyHingeMult n))} (h : F' ⊆ F) :
    G.fiberDegree n v F' ≤ G.fiberDegree n v F :=
  Set.ncard_le_ncard (Set.inter_subset_inter_left _ h) (Set.toFinite _)

/-- **The fiber-degree at `v` is bounded by the total fiber count at `v`**
(`lem:forest-surgery-split`, degree substrate). For a fiber set `F ⊆ E(G̃)`, the degree
`dᶠ(v)` is at most `(D − 1)·|incident G-edges at v|`; for a degree-2 vertex `v` this is
`2(D − 1)`, so the per-forest degrees sum to at most `2(D − 1)` across the `D` forests of
an independent set, the count the surgery's `h' ≤ D − 2` short-circuit bound rests on. -/
lemma fiberDegree_le [Finite β] {G : Graph α β} {n : ℕ} {v : α}
    {F : Set (β × Fin (bodyHingeMult n))} (hF : F ⊆ E(G.mulTilde n)) :
    G.fiberDegree n v F ≤ bodyHingeMult n * {e | G.Inc e v}.ncard := by
  rw [fiberDegree, ← fiberAtVertex_inter_edgeSet_ncard]
  refine Set.ncard_le_ncard (fun p hp ↦ ⟨hp.2, hF hp.1⟩) (Set.toFinite _)

/-- **The `v`-free part of a `G̃`-forest transports verbatim into `G̃_v^{ab}`**
(`lem:forest-surgery-split`, reroute wiring step 1; Katoh–Tanigawa 2011 Lemma 4.1). Given a
cycle-matroid-acyclic (forest) fiber set `F` of the multiplied graph `G̃ = (D-1)·G` and a
*fresh* short-circuit edge `e₀ ∉ E(G)`, the part of `F` avoiding the degree-2 vertex `v` —
`F ∖ fiberAtVertex v`, the fibers KT's surgery keeps untouched (`dᶠ(v) = 0` forests entirely,
and the surviving non-`v`-edges of the `dᶠ(v) ∈ {1,2}` forests) — is acyclic in the multiplied
splitting-off `G̃_v^{ab}`.

This is the half of KT 4.1's per-forest reroute that needs *no* `ã̃b` swap: every `v`-free
fiber `p` of `F` is a copy of a `v`-avoiding edge of `G`, hence a fiber of the multiplied
vertex-removal `(G_v)̃`. The `v`-free part is a subset of `F`, so acyclic in `G̃`; it lives in
`E((G_v)̃) ⊆ E(G̃)`, so by `IsAcyclicSet.anti_inter` along `(G_v)̃ = ((G − v))̃ ≤ G̃`
(`edgeMultiply_mono` of `deleteVerts_le`) it is acyclic already in `(G_v)̃`, and
`isAcyclicSet_mulTilde_splitOff_of_removeVertex` lifts that into `G̃_v^{ab}`. The residual
reroute crux — the `dᶠ(v) = 2` forest swapping its two `v`-edges for one `ã̃b` copy (a
`v`-traversing tree-path lift) — is the still-open second wiring step. -/
lemma isAcyclicSet_splitOff_of_diff_fiberAtVertex {G : Graph α β} {v a b : α} {e₀ : β}
    {n : ℕ} (he₀ : e₀ ∉ E(G)) {F : Set (β × Fin (bodyHingeMult n))}
    (hF : ((G.mulTilde n).cycleMatroid).Indep F) :
    ((G.splitOff v a b e₀).mulTilde n).cycleMatroid.Indep (F \ G.fiberAtVertex n v) := by
  rw [cycleMatroid_indep] at hF
  -- The `v`-free part lands in the ground set of the multiplied vertex-removal.
  have hsub : F \ G.fiberAtVertex n v ⊆ E((G.removeVertex v).mulTilde n) := by
    rintro p ⟨hpF, hpv⟩
    have hpE : p ∈ E(G.mulTilde n) := hF.1 hpF
    rw [mem_fiberAtVertex] at hpv
    rw [mem_edgeSet_mulTilde] at hpE
    obtain ⟨x, y, hl⟩ := exists_isLink_of_mem_edgeSet hpE
    rw [mem_edgeSet_mulTilde, removeVertex,
      edgeSet_deleteVerts, Set.mem_setOf_eq]
    exact ⟨x, y, hl, fun hx ↦ hpv (hx ▸ hl.inc_left), fun hy ↦ hpv (hy ▸ hl.inc_right)⟩
  -- Acyclic in `(G_v)̃` (subset of the `G̃`-forest, restricted to the smaller ground set),
  -- then lift to `G̃_v^{ab}`.
  apply isAcyclicSet_mulTilde_splitOff_of_removeVertex he₀
  rw [cycleMatroid_indep]
  have hle : (G.removeVertex v).mulTilde n ≤ G.mulTilde n :=
    edgeMultiply_mono (by rw [removeVertex]; exact deleteVerts_le) _
  have hanti := hF.anti (Set.diff_subset (t := G.fiberAtVertex n v))
  have := hanti.anti_inter hle
  rwa [Set.inter_eq_self_of_subset_right hsub] at this

/-! ## At most one fresh copy per forest (`lem:forest-surgery-split`, reroute count substrate)

The rerouting half of the Katoh–Tanigawa 2011 Lemma 4.1 forest surgery swaps the two
`v`-edges of each `dᶠ(v) = 2` forest for a *single* fresh copy of the short-circuit fiber
`ã̃b = edgeFiber e₀ n`. The bound that makes the `< D - 1` short-circuit-copy count
(`h' ≤ D - 2`) go through is that **each rerouted forest absorbs at most one `ã̃b` copy**:
an acyclic fiber set of the multiplied splitting-off `G̃_v^{ab}` cannot contain two distinct
parallel copies of `e₀`, since two parallel copies of the same edge between distinct
endpoints `a ≠ b` form a 2-cycle. Aggregated across the `D` forests this caps the total
`ã̃b`-copy count at `D`, and the per-forest single-copy fact is what drives the reroute's
edge-disjointness bookkeeping (the residual rerouting transport itself — a `v`-traversing
tree-path lift — is the still-open crux). -/

/-- **Two distinct parallel copies of the short-circuit edge form a 2-cycle**
(`lem:forest-surgery-split`, reroute count substrate). When the splitting-off `G_v^{ab}` at
a degree-2 vertex `v` with *distinct* neighbours `a ≠ b` (`a, b ≠ v`, `a, b ∈ V(G)`) inserts
its fresh edge `e₀`, any two distinct copies `p ≠ q` of `e₀` in the multiplied splitting-off
`G̃_v^{ab}` are a cycle-edge-set: `{p, q}` is `IsCycleSet` of `G̃_v^{ab}`. Both copies join
the same endpoints `a, b` (`splitOff`'s fresh-edge disjunct), so the length-2 closed walk
`a —p→ b —q→ a` is a cyclic walk. -/
lemma isCycleSet_pair_edgeFiber_splitOff {G : Graph α β} {v a b : α} {e₀ : β} {n : ℕ}
    (hab : a ≠ b) (ha : a ≠ v) (hb : b ≠ v) (haV : a ∈ V(G)) (hbV : b ∈ V(G))
    {p q : β × Fin (bodyHingeMult n)} (hp : p.1 = e₀) (hq : q.1 = e₀) (hpq : p ≠ q) :
    ((G.splitOff v a b e₀).mulTilde n).IsCycleSet {p, q} := by
  -- Both `p` and `q` are copies of `e₀`, hence links of `a, b` in `G̃_v^{ab}`.
  have hlink : ∀ r : β × Fin (bodyHingeMult n), r.1 = e₀ →
      ((G.splitOff v a b e₀).mulTilde n).IsLink r a b := by
    intro r hr
    rw [mulTilde_isLink, splitOff_isLink, hr]
    exact Or.inr ⟨rfl, ha, hb, haV, hbV, Or.inl ⟨rfl, rfl⟩⟩
  have hlinkp := hlink p hp
  have hlinkq := hlink q hq
  -- The length-2 closed walk `a —p→ b —q→ a`.
  refine ⟨WList.cons a p (WList.cons b q (WList.nil a)), ?_, by simp⟩
  have hwalk : ((G.splitOff v a b e₀).mulTilde n).IsWalk
      (WList.cons a p (WList.cons b q (WList.nil a))) := by
    rw [cons_isWalk_iff, cons_isWalk_iff, nil_isWalk_iff]
    exact ⟨hlinkp, hlinkq.symm, hlinkp.left_mem⟩
  refine ⟨⟨⟨hwalk, ?_⟩, by simp, ?_⟩, ?_⟩
  · -- Distinct edges `p ≠ q`.
    simp [hpq]
  · -- Closed: first vertex = last vertex.
    simp
  · -- No repeated vertices in the tail `[b, a]`: `a ≠ b`.
    simp [hab.symm]

/-- **A forest of the multiplied splitting-off carries at most one short-circuit copy**
(`lem:forest-surgery-split`, reroute count substrate; Katoh–Tanigawa 2011 Lemma 4.1). When the
splitting-off `G_v^{ab}` at a degree-2 vertex `v` with distinct neighbours `a ≠ b`
(`a, b ≠ v`, `a, b ∈ V(G)`) inserts its fresh edge `e₀`, any cycle-matroid-acyclic (forest)
fiber set `F` of the multiplied splitting-off `G̃_v^{ab}` meets the fresh short-circuit fiber
`ã̃b = edgeFiber e₀ n` in at most one element: `(F ∩ edgeFiber e₀ n).Subsingleton`.

Two distinct copies of `e₀` form a 2-cycle (`isCycleSet_pair_edgeFiber_splitOff`), so a forest
— containing no cycle — can keep at most one. This is the per-forest cap behind KT 4.1's
`< D - 1` short-circuit-copy count: across the `D` rerouted forests the total number of
`ã̃b` copies retained is at most `D`, each forest absorbing one swapped `v`-traversing path. -/
lemma fiber_inter_subsingleton_of_isAcyclicSet_splitOff {G : Graph α β}
    {v a b : α} {e₀ : β} {n : ℕ} (hab : a ≠ b) (ha : a ≠ v) (hb : b ≠ v) (haV : a ∈ V(G))
    (hbV : b ∈ V(G)) {F : Set (β × Fin (bodyHingeMult n))}
    (hF : ((G.splitOff v a b e₀).mulTilde n).cycleMatroid.Indep F) :
    (F ∩ edgeFiber e₀ n).Subsingleton := by
  rw [cycleMatroid_indep] at hF
  intro p hp q hq
  by_contra hpq
  -- `p, q` are distinct copies of `e₀` in `F`, so `{p, q}` is a cycle of `G̃_v^{ab}`.
  obtain ⟨C, hCG, hC, hCpq⟩ := isCycleSet_iff.mp
    (isCycleSet_pair_edgeFiber_splitOff hab ha hb haV hbV hp.2 hq.2 hpq)
  -- A cycle with edge set `{p, q} ⊆ F` contradicts the acyclicity of `F`.
  refine (not_isAcyclicSet_iff hF.1).mpr ⟨C, hC, hCG, ?_⟩ hF
  rw [← hCpq]
  exact Set.insert_subset hp.1 (Set.singleton_subset_iff.mpr hq.1)

/-- **Two distinct parallel copies of an edge of `G` form a 2-cycle in `G̃`**
(`lem:forest-surgery-count`, degree-cap substrate). If `e` is an edge of `G` linking two
*distinct* vertices `x ≠ y`, any two distinct copies `p ≠ q` of `e` in the multiplied graph
`G̃ = (D-1)·G` are a cycle-edge-set: `{p, q}` is `IsCycleSet` of `G̃`. Both copies link the
same endpoints `x, y`, so `x —p→ y —q→ x` is a length-2 cyclic walk. (This is the plain-`G̃`
analogue of `isCycleSet_pair_edgeFiber_splitOff`; it caps each forest's `v`-degree at `2`.) -/
lemma isCycleSet_pair_edgeFiber_mulTilde {G : Graph α β} {n : ℕ} {e : β} {x y : α}
    (hxy : x ≠ y) (hl : G.IsLink e x y)
    {p q : β × Fin (bodyHingeMult n)} (hp : p.1 = e) (hq : q.1 = e) (hpq : p ≠ q) :
    (G.mulTilde n).IsCycleSet {p, q} := by
  have hlink : ∀ r : β × Fin (bodyHingeMult n), r.1 = e → (G.mulTilde n).IsLink r x y :=
    fun r hr ↦ by rw [mulTilde_isLink, hr]; exact hl
  have hlinkp := hlink p hp
  have hlinkq := hlink q hq
  refine ⟨WList.cons x p (WList.cons y q (WList.nil x)), ?_, by simp⟩
  have hwalk : (G.mulTilde n).IsWalk (WList.cons x p (WList.cons y q (WList.nil x))) := by
    rw [cons_isWalk_iff, cons_isWalk_iff, nil_isWalk_iff]
    exact ⟨hlinkp, hlinkq.symm, hlinkp.left_mem⟩
  refine ⟨⟨⟨hwalk, ?_⟩, by simp, ?_⟩, ?_⟩
  · simp [hpq]
  · simp
  · simp [hxy.symm]

/-- **A `G̃`-forest holds at most one copy of any single edge** (`lem:forest-surgery-count`,
degree-cap substrate). For a cycle-matroid-acyclic (forest) fiber set `F` of `G̃` and an edge
`e` of `G` between *distinct* endpoints, `F` meets the fiber `ẽ = edgeFiber e n` in at most one
element. Two distinct copies of `e` form a 2-cycle (`isCycleSet_pair_edgeFiber_mulTilde`),
which a forest cannot contain. -/
lemma fiber_inter_subsingleton_of_isAcyclicSet_mulTilde {G : Graph α β} {n : ℕ} {e : β}
    {x y : α} (hxy : x ≠ y) (hl : G.IsLink e x y) {F : Set (β × Fin (bodyHingeMult n))}
    (hF : (G.mulTilde n).cycleMatroid.Indep F) : (F ∩ edgeFiber e n).Subsingleton := by
  rw [cycleMatroid_indep] at hF
  intro p hp q hq
  by_contra hpq
  obtain ⟨C, hCG, hC, hCpq⟩ := isCycleSet_iff.mp
    (isCycleSet_pair_edgeFiber_mulTilde hxy hl hp.2 hq.2 hpq)
  refine (not_isAcyclicSet_iff hF.1).mpr ⟨C, hC, hCG, ?_⟩ hF
  rw [← hCpq]
  exact Set.insert_subset hp.1 (Set.singleton_subset_iff.mpr hq.1)

/-! ## The degree-2 reroute preserves acyclicity (`lem:forest-surgery-split`, reroute wiring step 2)

The genuine combinatorial crux of the Katoh–Tanigawa 2011 Lemma 4.1 forest surgery: a balanced
forest `F` of `G̃` that uses **both** of its two `v`-edges (`dᶠ(v) = 2`: the `va`-copy `pa` and
the `vb`-copy `pb`) trades them for a single short-circuit copy `r` of the fresh edge `e₀`. The
rerouted forest `(F ∖ {pa, pb}) ∪ {r}` must stay acyclic in the multiplied splitting-off
`G̃_v^{ab}`.

The acyclicity rests on a **cycle-lift**: any cycle `C` of `G̃_v^{ab}` whose edges lie in
`(F ∖ {pa, pb}) ∪ {r}` lifts to a cyclic structure of `G̃` inside `F`, contradicting `F`'s
acyclicity. Two cases. If `C` avoids `r`, its edges lie in `F ∖ {pa, pb}` (so avoid the fresh
fiber), and deleting the fresh fiber from `G̃_v^{ab}` lands in `G̃`
(`mulTilde_splitOff_deleteFiber_le`), so `C` is already a cycle of `G̃` in `F`. If `C` uses `r` —
exactly once, as a trail has distinct edges — rotate `C` so `r` is its first edge,
`C = cons x r w'` with `{x, w'.first} = {a, b}`. The fresh edge `r` joins `a, b` in `G̃_v^{ab}`;
substituting the `v`-traversing 2-path `a —pa— v —pb— b` of `G̃` for `r` turns `C` into a closed
`G̃`-trail (the substituted `pa, pb ∉ E(w')`, distinct from each other and from `w'`'s edges), and
a closed trail contains a cycle (`IsTour.exists_isCyclicWalk`) whose edges are a sublist — hence
still inside `F = (F ∖ {pa, pb}) ∪ {pa, pb}`. Either way `F`
carries a `G̃`-cycle, contradiction. This is the last open wiring step; with it the per-forest
reroute map and the deficiency-relation assembly close `lem:forest-surgery-split`. -/

/-- **The degree-2 reroute preserves acyclicity** (`lem:forest-surgery-split`, reroute wiring
step 2; Katoh–Tanigawa 2011 Lemma 4.1 p.660). Let `v` be a degree-2 vertex of `G` with distinct
neighbours `a ≠ b` (`a, b ≠ v`, `a, b ∈ V(G)`) and `e₀ ∉ E(G)` the fresh short-circuit edge. Let
`F` be a `(G̃).cycleMatroid`-independent (forest) fiber set whose two `v`-incident fibers are
exactly `pa` (a `v—a` copy) and `pb` (a `v—b` copy) — the `dᶠ(v) = 2` case of the surgery — and
let `r` be any copy of `e₀` (`r.1 = e₀`). Then the **rerouted forest** `(F ∖ {pa, pb}) ∪ {r}`,
obtained by swapping the two `v`-edges for the single short-circuit copy `r`, is acyclic in the
multiplied splitting-off `G̃_v^{ab}`:
`((G.splitOff v a b e₀).mulTilde n).cycleMatroid.Indep (insert r (F \ {pa, pb}))`.

This is the rerouting half of KT 4.1's per-forest acyclicity preservation — the half
`isAcyclicSet_splitOff_of_diff_fiberAtVertex` (reroute wiring step 1, the `v`-free part) does
*not* cover. The proof lifts a hypothetical `G̃_v^{ab}`-cycle through `r` to a `G̃`-cycle inside
`F` (substituting `r` by the 2-path through `v`), contradicting acyclicity; see the section
preamble. -/
lemma isAcyclicSet_splitOff_reroute {G : Graph α β} {v a b : α} {e₀ : β} {n : ℕ}
    (ha : a ≠ v) (hb : b ≠ v) (haV : a ∈ V(G)) (hbV : b ∈ V(G))
    {F : Set (β × Fin (bodyHingeMult n))} {pa pb r : β × Fin (bodyHingeMult n)}
    (hF : ((G.mulTilde n).cycleMatroid).Indep F)
    (hpa : (G.mulTilde n).IsLink pa v a) (hpb : (G.mulTilde n).IsLink pb v b)
    (hpaF : pa ∈ F) (hpbF : pb ∈ F) (hpab : pa ≠ pb)
    (hFv : ∀ p ∈ F, (G.mulTilde n).Inc p v → p = pa ∨ p = pb)
    (hr : r.1 = e₀) (he₀ : e₀ ∉ E(G)) :
    ((G.splitOff v a b e₀).mulTilde n).cycleMatroid.Indep (insert r (F \ {pa, pb})) := by
  classical
  -- Abbreviations: the original `K = G̃` and the splitting-off `Ksp = G̃_v^{ab}`.
  set K := G.mulTilde n with hK
  set Ksp := (G.splitOff v a b e₀).mulTilde n with hKsp
  rw [cycleMatroid_indep] at hF
  -- The rerouted set lies in the ground set of `Ksp`.
  have hpaE : pa.1 ∈ E(G) := by
    rw [hK, mulTilde_isLink] at hpa; exact hpa.edge_mem
  have hpbE : pb.1 ∈ E(G) := by
    rw [hK, mulTilde_isLink] at hpb; exact hpb.edge_mem
  -- `pa, pb` are not copies of the fresh edge.
  have hpane₀ : pa.1 ≠ e₀ := fun h ↦ he₀ (h ▸ hpaE)
  have hpbne₀ : pb.1 ≠ e₀ := fun h ↦ he₀ (h ▸ hpbE)
  have hrE : r ∈ E(Ksp) := by
    rw [hKsp, mem_edgeSet_mulTilde, edgeSet_splitOff]
    exact Or.inl ⟨hr, ha, hb, haV, hbV⟩
  have hdiffsub : F \ {pa, pb} ⊆ E(Ksp) := by
    rintro p ⟨hpF, hp2⟩
    rw [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hp2
    have hpE : p ∈ E(K) := hF.1 hpF
    have hpv : ¬ K.Inc p v := fun hinc ↦ (hFv p hpF hinc).elim hp2.1 hp2.2
    -- `p` is a `v`-avoiding `G`-edge copy distinct from `e₀`, kept by `splitOff`.
    rw [hK, mem_edgeSet_mulTilde] at hpE
    obtain ⟨x, y, hl⟩ := exists_isLink_of_mem_edgeSet hpE
    have hxv : x ≠ v := fun hx ↦ hpv (hx ▸ (by
      rw [hK, mulTilde, edgeMultiply_inc]; exact hl.inc_left))
    have hyv : y ≠ v := fun hy ↦ hpv (hy ▸ (by
      rw [hK, mulTilde, edgeMultiply_inc]; exact hl.inc_right))
    have hpne₀ : p.1 ≠ e₀ := fun h ↦ he₀ (h ▸ hpE)
    rw [hKsp, mem_edgeSet_mulTilde, edgeSet_splitOff]
    exact Or.inr ⟨hpne₀, x, y, hl, hxv, hyv⟩
  set S := insert r (F \ {pa, pb}) with hS
  have hSE : S ⊆ E(Ksp) := Set.insert_subset hrE hdiffsub
  rw [cycleMatroid_indep, isAcyclicSet_iff]
  refine ⟨hSE, ?_⟩
  rw [restrict_isForest_iff']
  intro C hCS hCcyc
  -- The cycle's edges avoid `pa, pb` (they are kept off `S`).
  have hCnpa : pa ∉ C.edgeSet := fun h ↦ (Set.mem_of_mem_of_subset h hCS).elim
    (fun he ↦ hpane₀ (by rw [he, hr]))
    (fun ⟨_, hne⟩ ↦ hne (Or.inl rfl))
  have hCnpb : pb ∉ C.edgeSet := fun h ↦ (Set.mem_of_mem_of_subset h hCS).elim
    (fun he ↦ hpbne₀ (by rw [he, hr]))
    (fun ⟨_, hne⟩ ↦ hne (Or.inr rfl))
  by_cases hrC : r ∈ C.edgeSet
  · -- `C` uses the short-circuit copy `r`: substitute the 2-path through `v`.
    -- Rotate `C` so its first edge is `r`.
    obtain ⟨m, -, hne, hfe⟩ := WList.exists_rotate_firstEdge_eq (w := C) (e := r) hrC
    have hDcyc : Ksp.IsCyclicWalk (C.rotate m) := hCcyc.rotate m
    have hDE : (C.rotate m).edgeSet = C.edgeSet := WList.rotate_edgeSet C m
    -- Destructure the rotated walk: `C.rotate m = cons x r w'`.
    obtain ⟨x, e, w', heq⟩ := WList.nonempty_iff_exists_cons.mp (hne.rotate m)
    have her : e = r := by simp only [heq, WList.Nonempty.firstEdge_cons] at hfe; exact hfe
    subst her
    rw [heq] at hDcyc hDE
    -- `D₀ = cons x e w'` is closed, so `w'.last = x`.
    have hclosed : (WList.cons x e w').IsClosed := hDcyc.isClosed
    rw [WList.cons_isClosed_iff] at hclosed
    -- The first link of `D₀ = cons x e w'`: `e` joins `x` and `w'.first` in `Ksp`.
    have hwalk : Ksp.IsWalk (WList.cons x e w') := hDcyc.isWalk
    rw [cons_isWalk_iff] at hwalk
    obtain ⟨hrlink, hw'walk⟩ := hwalk
    -- `e` is a fresh-edge copy, so it joins exactly `a` and `b`.
    rw [hKsp, mulTilde_isLink, splitOff_isLink] at hrlink
    have hxw' : (x = a ∧ w'.first = b) ∨ (x = b ∧ w'.first = a) := by
      rcases hrlink with ⟨hne', _⟩ | ⟨_, _, _, _, _, hxy⟩
      · exact absurd hr hne'
      · exact hxy
    -- Edge bookkeeping on the cyclic walk `cons x e w'`: distinct edges, so `e ∉ E(w')`.
    have hnodup : (WList.cons x e w').edge.Nodup := hDcyc.edge_nodup
    rw [WList.cons_edge, List.nodup_cons] at hnodup
    obtain ⟨henw', hw'nodup⟩ := hnodup
    have hw'edge : ∀ p ∈ w'.edge, p ∈ F \ {pa, pb} := by
      intro p hp
      have hpS : p ∈ S := hCS (hDE ▸ (by
        rw [WList.cons_edgeSet]; exact Set.mem_insert_of_mem _ (WList.mem_edgeSet_iff.mpr hp)))
      refine (Set.mem_insert_iff.mp hpS).resolve_left ?_
      rintro rfl; exact henw' hp
    -- `w'` avoids the fresh fiber, hence lifts to a `K = G̃`-walk.
    have hw'fresh : Disjoint w'.edgeSet (edgeFiber e₀ n) := by
      rw [Set.disjoint_left]; intro p hp hpf
      have : p.1 = e₀ := hpf
      have hpEK : p ∈ E(K) := hF.1 (hw'edge p hp).1
      rw [hK, mem_edgeSet_mulTilde] at hpEK
      exact he₀ (this ▸ hpEK)
    have hw'K : K.IsWalk w' :=
      (isWalk_deleteEdges_iff.mpr ⟨hw'walk, hw'fresh⟩).of_le
        (mulTilde_splitOff_deleteFiber_le n)
    -- Build the `K`-substitute closed trail and extract a `K`-cycle inside `F`.
    have hkey : ∃ T : WList α (β × Fin (bodyHingeMult n)), K.IsTour T ∧ T.edgeSet ⊆ F := by
      rcases hxw' with ⟨hxa, hwb⟩ | ⟨hxb, hwa⟩
      · -- `x = a`, `w'.first = b`: substitute `a —pa— v —pb— b ⋯ a`.
        refine ⟨WList.cons a pa (WList.cons v pb w'), ?_, ?_⟩
        · refine ⟨⟨?_, ?_⟩, by simp, ?_⟩
          · rw [cons_isWalk_iff, cons_isWalk_iff]
            exact ⟨hpa.symm, hwb ▸ hpb, hw'K⟩
          · simp only [WList.cons_edge, List.nodup_cons, List.mem_cons]
            refine ⟨?_, ?_, hw'nodup⟩
            · rintro (h | h)
              · exact hpab h
              · exact (hw'edge pa h).2 (by simp)
            · exact fun h ↦ (hw'edge pb h).2 (by simp)
          · -- closed: first `a` = last `w'.last = x = a`.
            rw [WList.cons_isClosed_iff, WList.last_cons]; exact hxa ▸ hclosed
        · intro p hp
          simp only [WList.cons_edgeSet, Set.mem_insert_iff] at hp
          rcases hp with rfl | rfl | hp
          · exact hpaF
          · exact hpbF
          · exact (hw'edge p hp).1
      · -- `x = b`, `w'.first = a`: substitute `b —pb— v —pa— a ⋯ b`.
        refine ⟨WList.cons b pb (WList.cons v pa w'), ?_, ?_⟩
        · refine ⟨⟨?_, ?_⟩, by simp, ?_⟩
          · rw [cons_isWalk_iff, cons_isWalk_iff]
            exact ⟨hpb.symm, hwa ▸ hpa, hw'K⟩
          · simp only [WList.cons_edge, List.nodup_cons, List.mem_cons]
            refine ⟨?_, ?_, hw'nodup⟩
            · rintro (h | h)
              · exact hpab.symm h
              · exact (hw'edge pb h).2 (by simp)
            · exact fun h ↦ (hw'edge pa h).2 (by simp)
          · rw [WList.cons_isClosed_iff, WList.last_cons]; exact hxb ▸ hclosed
        · intro p hp
          simp only [WList.cons_edgeSet, Set.mem_insert_iff] at hp
          rcases hp with rfl | rfl | hp
          · exact hpbF
          · exact hpaF
          · exact (hw'edge p hp).1
    -- A `K`-tour contains a `K`-cycle whose edges are a sublist, hence inside `F`.
    obtain ⟨T, hT, hTF⟩ := hkey
    obtain ⟨C', hC', hsub⟩ := hT.exists_isCyclicWalk
    exact hF.2 C' hC' (hsub.edge_subset.trans hTF)
  · -- `C` avoids `r`, so its edges lie in `F ∖ {pa, pb}` and avoid the fresh fiber;
    -- `C` is then a cycle of `K = G̃` inside `F`, contradicting `hF`.
    have hCF : C.edgeSet ⊆ F := by
      intro p hp
      rcases Set.mem_of_mem_of_subset hp hCS with hpr | hpd
      · exact absurd (hpr ▸ hp) hrC
      · exact hpd.1
    have hCnofresh : Disjoint C.edgeSet (edgeFiber e₀ n) := by
      rw [Set.disjoint_left]
      intro p hp hpf
      have hpe₀ : p.1 = e₀ := hpf
      rcases Set.mem_of_mem_of_subset hp hCS with hpr | hpd
      · exact hrC (hpr ▸ hp)
      · have hpEK : p ∈ E(K) := hF.1 hpd.1
        rw [hK, mem_edgeSet_mulTilde] at hpEK
        exact he₀ (hpe₀ ▸ hpEK)
    -- Lift `C` to a cyclic walk of `K = G̃` inside `F`, contradicting `F` acyclic.
    have hCK : K.IsCyclicWalk C :=
      ((deleteEdges_isCyclicWalk_iff _ _).mpr ⟨hCcyc, hCnofresh⟩).of_le
        (mulTilde_splitOff_deleteFiber_le n)
    exact hF.2 C hCK hCF

/-! ## Circuits of the multiplied splitting-off meet the short-circuit (`lem:reduction-step`)

The conceptual heart of the splitting-off minimality transport (Katoh–Tanigawa 2011 Lemma
4.8(i), the claim labelled (4.10) in their proof). For a minimal `k`-dof-graph `G` with **no
proper rigid subgraph** and a degree-2 vertex `v` with neighbours `a, b` (`e₀ ∉ E(G)` fresh),
*every circuit `X` of the matroid `M(G̃_v^{ab})` of the splitting-off meets the fresh
short-circuit fiber* `ã̃b = edgeFiber e₀ n`.

This is KT's (4.10): if instead `X ∩ ã̃b = ∅`, then `X ⊆ E(G̃_v^{ab}) ∖ ã̃b = E(G̃_v) ⊆ E(G̃)`
(the ground-set bridge `edgeSet_mulTilde_splitOff_diff_fiber`), and since the two matroids
restrict identically to the surviving ground set `E(G̃_v)` (`matroidMG_restrict_mulTilde`
applied to `G̃_v ≤ G̃_v^{ab}` and to `G_v ≤ G`, both read off `Matroid.restrict_isCircuit_iff`),
`X` is also a circuit of `M(G̃)` — with `v ∉ V(X)`, since every fiber of `X` is a copy of a
`v`-avoiding edge of `G`. So `G[V(X)]` is a rigid subgraph (`circuit_induces_isRigidSubgraph`)
that is *proper* (`v ∉ V(X)`), contradicting the no-proper-rigid hypothesis.

This is the matroidal claim the minimality transport `splitOff_isMinimalKDof` consumes: it is
exactly the statement that the surviving ground set `E(G̃_v)` is circuit-free, i.e. independent,
in `M(G̃_v^{ab})`. Katoh–Tanigawa use it to drive an iterated fundamental-circuit swap relocating
each `ã̃b` copy onto an `ẽ` copy; `splitOff_isMinimalKDof` instead consumes it directly, as the
fact that `E(G̃_v)` is a base of `M(G̃_v)` (so the swap induction is bypassed by a rank count).
Stated under no-proper-rigid alone — minimality of `G` is not needed for (4.10). -/
theorem circuit_splitOff_meets_fiber [DecidableEq β] [Finite α] [Finite β] {G : Graph α β}
    {n : ℕ} (hD : 1 ≤ bodyBarDim n) {v a b : α} {e₀ : β} (hvG : v ∈ V(G))
    (he₀ : e₀ ∉ E(G)) (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n)
    {X : Set (β × Fin (bodyHingeMult n))}
    (hX : ((G.splitOff v a b e₀).matroidMG n).IsCircuit X) :
    (X ∩ edgeFiber e₀ n).Nonempty := by
  classical
  rw [Set.nonempty_iff_ne_empty]
  intro hXe
  -- `X ⊆ E(G̃_v^{ab}) ∖ ã̃b = E(G̃_v)` (ground-set bridge).
  have hXground : X ⊆ E((G.splitOff v a b e₀).mulTilde n) := by
    have := hX.subset_ground; rwa [matroidMG, Matroid.restrict_ground_eq] at this
  have hXdisj : Disjoint X (edgeFiber e₀ n) := Set.disjoint_iff_inter_eq_empty.mpr hXe
  have hXsubGv : X ⊆ E((G.removeVertex v).mulTilde n) := by
    rw [← edgeSet_mulTilde_splitOff_diff_fiber n he₀]
    exact Set.subset_diff.mpr ⟨hXground, hXdisj⟩
  -- `G_v ≤ G_v^{ab}` at the graph level (every `v`-avoiding `G`-link survives, `e₀` being fresh).
  have hleGvSplit : G.removeVertex v ≤ G.splitOff v a b e₀ := by
    refine ⟨fun x hx => hx, fun p x y hp => ?_⟩
    rw [removeVertex_isLink] at hp
    obtain ⟨hlink, hxv, hyv⟩ := hp
    rw [splitOff_isLink]
    exact Or.inl ⟨fun h => he₀ (h ▸ hlink.edge_mem), hlink, hxv, hyv⟩
  have hleSplitMul : (G.removeVertex v).mulTilde n ≤ (G.splitOff v a b e₀).mulTilde n :=
    edgeMultiply_mono hleGvSplit _
  -- `M(G̃_v^{ab}) ↾ E(G̃_v) = M(G̃_v)`, so `X` is a circuit of `M(G̃_v)`.
  have hcircGv : ((G.removeVertex v).matroidMG n).IsCircuit X := by
    rw [← matroidMG_restrict_mulTilde hleGvSplit n,
      Matroid.restrict_isCircuit_iff hleSplitMul.edgeSet_mono]
    exact ⟨hX, hXsubGv⟩
  -- `M(G̃) ↾ E(G̃_v) = M(G̃_v)`, so `X` is a circuit of `M(G̃)`.
  have hleG : G.removeVertex v ≤ G := by
    rw [removeVertex]; exact deleteVerts_le
  have hcircG : (G.matroidMG n).IsCircuit X := by
    have hbridge := matroidMG_restrict_mulTilde hleG n
    rw [← hbridge] at hcircGv
    exact (Matroid.restrict_isCircuit_iff (edgeMultiply_mono hleG _).edgeSet_mono).mp hcircGv |>.1
  -- `G[V(X)]` is a rigid subgraph of `G`.
  have hrigid : (G.inducedSpan n X).IsRigidSubgraph G n :=
    circuit_induces_isRigidSubgraph hD hcircG
  -- `v ∉ V(X)`: every fiber of `X` is a copy of a `v`-avoiding edge.
  have hvnot : v ∉ V(G.inducedSpan n X) := by
    rw [vertexSet_inducedSpan, fiberSpan, mem_spanningVerts]
    rintro ⟨p, hpX, hinc⟩
    rw [mulTilde_inc] at hinc
    obtain ⟨w, hlw⟩ := hinc
    -- `p.1 ∈ E(G_v)`, so `p.1` carries a `v`-avoiding `G`-link, contradicting `G.IsLink p.1 v w`.
    have hpe : p.1 ∈ E(G.removeVertex v) := by
      have := hXsubGv hpX
      rwa [mem_edgeSet_mulTilde] at this
    obtain ⟨x, y, hlxy⟩ := exists_isLink_of_mem_edgeSet hpe
    rw [removeVertex_isLink] at hlxy
    obtain ⟨hlxyG, hxv, hyv⟩ := hlxy
    rcases hlw.left_eq_or_eq hlxyG with h | h
    · exact hxv h.symm
    · exact hyv h.symm
  -- A circuit spans a nonempty vertex set; with `v ∉ V(X)`, `G[V(X)]` is *proper* rigid.
  have hVne : V(G.inducedSpan n X).Nonempty := by
    rw [vertexSet_inducedSpan, fiberSpan]
    obtain ⟨q, hq⟩ := hcircG.nonempty
    obtain ⟨x, _, hinc⟩ := exists_isLink_of_mem_edgeSet (hcircG.subset_ground hq)
    exact ⟨x, q, hq, hinc.inc_left⟩
  have hVsub : V(G.inducedSpan n X) ⊆ V(G) := by
    rw [vertexSet_inducedSpan, fiberSpan]
    exact (G.mulTilde n).spanningVerts_subset_vertexSet X
  exact hnp (G.inducedSpan n X)
    ⟨hrigid, hVne, hVsub.ssubset_of_ne (fun heq => hvnot (heq ▸ hvG))⟩

/-! ## Splitting-off preserves minimal `0`-dof (`lem:reduction-step`, splitting-off branch)

The full Katoh–Tanigawa 2011 Lemma 4.8(i): splitting off a degree-2 vertex `v` of a minimal
`0`-dof-graph `G` with **no proper rigid subgraph** again yields a minimal `0`-dof-graph
`G_v^{ab}`. This is the splitting-off branch of `lem:reduction-step` (the contraction branch is
`contraction_isMinimalKDof`); paired with `lem:reduction-measure` it drives the `|V|`-induction
of Theorem 4.9.

**A clean counting argument replaces KT's iterated swap.** Katoh–Tanigawa prove minimality by
an iterated fundamental-circuit swap (their (4.10) + the `i = 1,…,h` loop) that relocates each
short-circuit copy `(ab)ᵢ` onto an `eᵢ ∈ ẽ`. We bypass the induction with a rank/cardinality
comparison through the green `def = corank` bridge `isBase_ncard_add_deficiency_eq`:

* the **0-dof half** (`def(G̃_v^{ab}) = 0`) is `dof_tracking`'s two-sided bound squeezed against
  `def(G̃) = 0` and `def ≥ 0`;
* the surviving ground set `E(G̃_v) = E(G̃_v^{ab}) ∖ ã̃b` is a **base of `M(G̃_v)`**: it is
  independent in `M(G̃_v^{ab})` (`circuit_splitOff_meets_fiber` — KT's (4.10) — says no circuit
  avoids `ã̃b`, i.e. `E(G̃_v)` is circuit-free), and restriction descends it to `M(G̃_v)`, where
  it is the whole ground set;
* KT 4.7 (`def(G̃_v) > 0`): `G_v ≤ G` is a proper subgraph, so under no-proper-rigid it is not
  `0`-dof, hence `def(G̃_v) > 0`;
* finally, any base `B'` of `M(G̃_v^{ab})` avoiding a fiber `ẽ` (`e ∈ E(G_v^{ab})`) has
  `|B'| ≤ |E(G̃_v)|` (case `e = e₀`: `B' ⊆ E(G̃_v)`; case `e ≠ e₀`: `B'` splits into `B' ∩ ã̃b`
  of size `≤ D − 1` and `B' ∩ E(G̃_v) ⊆ E(G̃_v) ∖ ẽ` of size `≤ |E(G̃_v)| − (D − 1)`). Via
  `isBase_ncard_add_deficiency_eq` on the two bases this forces `def(G̃_v) ≤ def(G̃_v^{ab}) = 0`,
  contradicting `def(G̃_v) > 0`. So every base meets every fiber: `G_v^{ab}` is minimal. -/
theorem splitOff_isMinimalKDof [DecidableEq β] [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hD : 2 ≤ bodyBarDim n) {v a b : α} {e₀ eₐ e_b : β}
    (hav : a ≠ v) (hbv : b ≠ v) (haV : a ∈ V(G)) (hbV : b ∈ V(G)) (hvG : v ∈ V(G))
    (heab : eₐ ≠ e_b) (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b) (he₀ : e₀ ∉ E(G))
    (hG : G.IsMinimalKDof n 0) (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) :
    (G.splitOff v a b e₀).IsMinimalKDof n 0 := by
  classical
  have hD1 : 1 ≤ bodyBarDim n := le_trans (by norm_num) hD
  set G' := G.splitOff v a b e₀ with hG'def
  set Gv := G.removeVertex v with hGvdef
  -- Vertex sets: `V(G') = V(Gv) = V(G) ∖ {v}`, nonempty (it contains `a`).
  have hVeq : V(G') = V(G) \ {v} := vertexSet_splitOff G v a b e₀
  have hVveq : V(Gv) = V(G) \ {v} := vertexSet_removeVertex G v
  have hVne : V(G').Nonempty := by rw [hVeq]; exact ⟨a, haV, by simpa using hav⟩
  have hVvne : V(Gv).Nonempty := by rw [hVveq]; exact ⟨a, haV, by simpa using hav⟩
  -- `Gv ≤ G` a proper subgraph (`v ∈ V(G)` is dropped); under no-proper-rigid, `def(G̃v) > 0`.
  have hleGvG : Gv ≤ G := by rw [hGvdef, removeVertex]; exact deleteVerts_le
  have hdefGv_pos : 0 < Gv.deficiency n := by
    rcases lt_or_eq_of_le (Gv.deficiency_nonneg n hVvne) with h | h
    · exact h
    · exfalso
      refine hnp Gv ⟨⟨hleGvG, h.symm⟩, hVvne, ?_⟩
      rw [hVveq]; exact Set.diff_singleton_ssubset.mpr hvG
  -- 0-dof half: `def(G̃') = 0` from `dof_tracking` squeezed against `def(G̃) = 0` and `def ≥ 0`.
  have hdofG : G.deficiency n = 0 := hG.1
  have htrack := dof_tracking hD hav hbv heab hla hlb hdeg2 he₀
  have hdefG'_zero : G'.deficiency n = 0 := by
    have h1 : G'.deficiency n ≤ G.deficiency n := htrack.2.1
    have h2 : 0 ≤ G'.deficiency n := G'.deficiency_nonneg n hVne
    rw [hdofG] at h1; omega
  refine ⟨hdefG'_zero, fun B' hB' e heG' => ?_⟩
  -- Prove the fiber-meeting by contradiction: assume `B' ∩ ẽ = ∅`.
  rw [Set.nonempty_iff_ne_empty]
  intro hBe
  -- `E(G̃') = ã̃b ⊔ E(G̃v)`: the fresh fiber and the surviving fibers.
  have hsplit_ground : E(G'.mulTilde n) \ edgeFiber e₀ n = E(Gv.mulTilde n) :=
    edgeSet_mulTilde_splitOff_diff_fiber n he₀
  have hfiberGround : edgeFiber e₀ n ⊆ E(G'.mulTilde n) :=
    edgeFiber_subset_edgeSet_mulTilde_splitOff n hav hbv haV hbV
  -- `B' ⊆ E(G̃')`, `|B'| = D(|V'|−1)` since `def(G̃') = 0`.
  have hB'ground : B' ⊆ E(G'.mulTilde n) := hB'.subset_ground
  have hB'card : (B'.ncard : ℤ) + 0 = bodyBarDim n * ((V(G').ncard : ℤ) - 1) := by
    have := G'.isBase_ncard_add_deficiency_eq n hD1 hVne hB'
    rwa [hdefG'_zero] at this
  -- `E(G̃v)` is a base of `M(G̃v)`: it is circuit-free in `M(G̃')` (KT (4.10)), hence
  -- independent there, and restriction descends it to the whole ground of `M(G̃v)`.
  have hGv_indep_in_G' : (G'.matroidMG n).Indep (E(Gv.mulTilde n)) := by
    rw [Matroid.indep_iff_forall_subset_not_isCircuit']
    refine ⟨fun C hCsub hC => ?_, ?_⟩
    · -- A circuit `C ⊆ E(G̃v)` avoids `ã̃b`, contradicting `circuit_splitOff_meets_fiber`.
      obtain ⟨p, hpC, hpfib⟩ := circuit_splitOff_meets_fiber hD1 hvG he₀ hnp hC
      have hpGv : p ∈ E(Gv.mulTilde n) := hCsub hpC
      rw [← hsplit_ground] at hpGv
      exact hpGv.2 hpfib
    · rw [matroidMG, Matroid.restrict_ground_eq, ← hsplit_ground]; exact Set.diff_subset
  have hleGvG' : Gv ≤ G' := by
    rw [hGvdef, hG'def]
    refine ⟨fun x hx => hx, fun p x y hp => ?_⟩
    rw [removeVertex_isLink] at hp
    obtain ⟨hlink, hxv, hyv⟩ := hp
    rw [splitOff_isLink]
    exact Or.inl ⟨fun h => he₀ (h ▸ hlink.edge_mem), hlink, hxv, hyv⟩
  have hGv_base : (Gv.matroidMG n).IsBase (E(Gv.mulTilde n)) := by
    have hg : (Gv.matroidMG n).E = E(Gv.mulTilde n) := by
      rw [matroidMG, Matroid.restrict_ground_eq]
    rw [← hg, ← Matroid.ground_indep_iff_isBase, hg, ← matroidMG_restrict_mulTilde hleGvG' n,
      Matroid.restrict_indep_iff]
    exact ⟨hGv_indep_in_G', subset_rfl⟩
  -- `|E(G̃v)| + def(G̃v) = D(|V v|−1) = D(|V'|−1)` (same vertex set `V(G)∖{v}`).
  have hEGvcard : (E(Gv.mulTilde n).ncard : ℤ) + Gv.deficiency n
      = bodyBarDim n * ((V(G').ncard : ℤ) - 1) := by
    have hb := Gv.isBase_ncard_add_deficiency_eq n hD1 hVvne hGv_base
    rw [hVveq] at hb; rw [hVeq]; exact hb
  -- Core cardinality bound: any base `B'` avoiding the fiber `ẽ` has `|B'| ≤ |E(G̃v)|`.
  have hB'le : B'.ncard ≤ E(Gv.mulTilde n).ncard := by
    by_cases he : e = e₀
    · -- `e = e₀`: `B'` avoids `ã̃b`, so `B' ⊆ E(G̃v)`.
      subst he
      have hB'sub : B' ⊆ E(Gv.mulTilde n) := by
        rw [← hsplit_ground]
        refine Set.subset_diff.mpr ⟨hB'ground, Set.disjoint_left.mpr fun p hpB' hpfib => ?_⟩
        exact absurd (Set.eq_empty_iff_forall_notMem.mp hBe p ⟨hpB', hpfib⟩) id
      exact Set.ncard_le_ncard hB'sub (Set.toFinite _)
    · -- `e ≠ e₀`: split `B'` into `B' ∩ ã̃b` (≤ D−1) and `B' ∩ E(G̃v) ⊆ E(G̃v) ∖ ẽ`.
      have heGv : edgeFiber e n ⊆ E(Gv.mulTilde n) := by
        intro p hp
        rw [edgeFiber, Set.mem_setOf_eq] at hp
        have heE : e ∈ E(Gv) := by
          have hmem : e ∈ E(G') := heG'
          rw [hG'def, edgeSet_splitOff] at hmem
          rcases hmem with ⟨rfl, _⟩ | ⟨_, x, y, hl, hx, hy⟩
          · exact absurd rfl he
          · have hlGv : Gv.IsLink e x y := by rw [hGvdef, removeVertex_isLink]; exact ⟨hl, hx, hy⟩
            exact hlGv.edge_mem
        rw [mem_edgeSet_mulTilde, hp]; exact heE
      -- Decompose `B' = (B' ∩ ã̃b) ∪ (B' ∩ E(G̃v))` since `B' ⊆ ã̃b ∪ E(G̃v) = E(G̃')`.
      have hcover : B' ⊆ edgeFiber e₀ n ∪ E(Gv.mulTilde n) := by
        intro p hpB'
        rcases em (p ∈ edgeFiber e₀ n) with hpf | hpf
        · exact Or.inl hpf
        · exact Or.inr (hsplit_ground ▸ ⟨hB'ground hpB', hpf⟩)
      have h1 : (B' ∩ edgeFiber e₀ n).ncard ≤ bodyHingeMult n := by
        calc (B' ∩ edgeFiber e₀ n).ncard ≤ (edgeFiber e₀ n).ncard :=
              Set.ncard_le_ncard Set.inter_subset_right (Set.toFinite _)
          _ = bodyHingeMult n := edgeFiber_ncard e₀ n
      have h2 : (B' ∩ E(Gv.mulTilde n)).ncard ≤ E(Gv.mulTilde n).ncard - bodyHingeMult n := by
        have hsub : B' ∩ E(Gv.mulTilde n) ⊆ E(Gv.mulTilde n) \ edgeFiber e n := by
          refine Set.subset_diff.mpr ⟨Set.inter_subset_right, Set.disjoint_left.mpr ?_⟩
          intro p hpB' hpfib
          exact absurd (Set.eq_empty_iff_forall_notMem.mp hBe p ⟨hpB'.1, hpfib⟩) id
        calc (B' ∩ E(Gv.mulTilde n)).ncard ≤ (E(Gv.mulTilde n) \ edgeFiber e n).ncard :=
              Set.ncard_le_ncard hsub (Set.toFinite _)
          _ = E(Gv.mulTilde n).ncard - (edgeFiber e n).ncard :=
              Set.ncard_diff heGv (Set.toFinite _)
          _ = E(Gv.mulTilde n).ncard - bodyHingeMult n := by rw [edgeFiber_ncard]
      have hcoverle : B'.ncard ≤ (B' ∩ edgeFiber e₀ n).ncard + (B' ∩ E(Gv.mulTilde n)).ncard := by
        calc B'.ncard ≤ ((B' ∩ edgeFiber e₀ n) ∪ (B' ∩ E(Gv.mulTilde n))).ncard := by
              refine Set.ncard_le_ncard ?_ (Set.toFinite _)
              rw [← Set.inter_union_distrib_left]
              exact Set.subset_inter (subset_refl _) hcover
          _ ≤ (B' ∩ edgeFiber e₀ n).ncard + (B' ∩ E(Gv.mulTilde n)).ncard :=
              Set.ncard_union_le _ _
      -- `|E(G̃v)| ≥ D − 1` (it contains `ẽ` of size `D − 1`), so the subtraction is exact.
      have hge : bodyHingeMult n ≤ E(Gv.mulTilde n).ncard := by
        calc bodyHingeMult n = (edgeFiber e n).ncard := (edgeFiber_ncard e n).symm
          _ ≤ E(Gv.mulTilde n).ncard := Set.ncard_le_ncard heGv (Set.toFinite _)
      omega
  -- Assemble: `D(|V'|−1) = |B'| ≤ |E(G̃v)| = D(|V'|−1) − def(G̃v)`, so `def(G̃v) ≤ 0` — contra.
  have hle : (B'.ncard : ℤ) ≤ (E(Gv.mulTilde n).ncard : ℤ) := by exact_mod_cast hB'le
  linarith [hB'card, hEGvcard, hle, hdefGv_pos]

/-! ## Theorem 4.9: reduction of minimal `0`-dof-graphs (`thm:minimal-kdof-reduction`)

The capstone of the combinatorial induction (Katoh–Tanigawa 2011 Theorem 4.9). Every
minimal `0`-dof-graph with `2 ≤ |V|` reduces to the two-vertex double edge by a sequence
of two operations — splitting off a reducible degree-2 vertex, and contracting a proper
rigid subgraph — each of which (`lem:reduction-step`) carries a minimal `0`-dof-graph to a
strictly smaller one (`lem:reduction-measure`). Phrased as the well-founded induction
principle this dichotomy + measure drives: a motive closed under the two-vertex base case
and the two reductions holds of every minimal `0`-dof-graph.

The splitting-off step needs the degree-2 vertex's two incident edges as explicit data
(the `eₐ`/`e_b` encoding `splitOff_isMinimalKDof` consumes). The bridge
`exists_splitOff_data_of_degree_eq_two` extracts it: a degree-2 vertex of a `0`-dof-graph
has its two incidences carried by two *distinct nonloop* edges (the `0`-dof
two-edge-connectivity rules out a single loop, which would also give degree 2), whose far
endpoints supply `a`, `b`. -/

/-- **A degree-2 vertex of a `0`-dof-graph carries splitting-off data**
(`thm:minimal-kdof-reduction`, the degree↔edges bridge for the splitting-off step). For
`D = bodyBarDim n ≥ 1`, a `0`-dof-graph
`G`, and a vertex `v` of multigraph degree exactly `2` with a distinct companion `b₀ ∈ V(G)`
(needed only to invoke two-edge-connectivity), the two incidences at `v` are carried by two
*distinct nonloop* edges `eₐ ≠ e_b`: the count `degree v = 2·#loops + #nonloops` together with
`#nonloops ≥ 2` (two-edge-connectivity, `two_le_crossingEdges_of_isKDof_zero`, via the singleton
cut `{v}` whose crossing edges are the nonloops at `v`) forces `#loops = 0` and `#nonloops = 2`.
The two nonloop edges' far endpoints `a, b ≠ v` lie in `V(G)`, and every `v`-incident edge is one
of them (the closure `hdeg2`). This is exactly the `eₐ`/`e_b`/`a`/`b` data `splitOff_isMinimalKDof`
consumes. -/
theorem exists_splitOff_data_of_degree_eq_two [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} (hD1 : 1 ≤ bodyBarDim n) (hG0 : G.IsKDof n 0) {v b₀ : α}
    (hvG : v ∈ V(G)) (hb₀G : b₀ ∈ V(G)) (hb₀v : b₀ ≠ v) (hdeg : G.degree v = 2) :
    ∃ (a b : α) (eₐ e_b : β), a ≠ v ∧ b ≠ v ∧ a ∈ V(G) ∧ b ∈ V(G) ∧ eₐ ≠ e_b ∧
      G.IsLink eₐ v a ∧ G.IsLink e_b v b ∧ ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b := by
  classical
  -- `degree v = 2·#loops + #nonloops`, and `#nonloops ≥ 2` (two-edge-connectivity).
  have hcount := G.degree_eq_ncard_add_ncard v
  have hcross : 2 ≤ (G.crossingEdges (cutLabeling {v} v b₀)).ncard :=
    two_le_crossingEdges_of_isKDof_zero hD1 hG0 (Set.mem_singleton v) hvG hb₀G
      (by simpa using hb₀v)
  have hnl2 : 2 ≤ {e | G.IsNonloopAt e v}.ncard :=
    le_trans hcross (Set.ncard_le_ncard crossingEdges_cutLabeling_singleton_subset
      (Set.toFinite _))
  -- Hence `#loops = 0` and `#nonloops = 2`.
  have hnl_eq : {e | G.IsNonloopAt e v}.ncard = 2 := by omega
  have hloop0 : {e | G.IsLoopAt e v}.ncard = 0 := by omega
  -- The two nonloop edges, distinct, with far endpoints.
  obtain ⟨eₐ, e_b, hne, hset⟩ := Set.ncard_eq_two.mp hnl_eq
  have hea : G.IsNonloopAt eₐ v := by
    have : eₐ ∈ {e | G.IsNonloopAt e v} := by rw [hset]; exact Set.mem_insert _ _
    exact this
  have heb : G.IsNonloopAt e_b v := by
    have : e_b ∈ {e | G.IsNonloopAt e v} := by rw [hset]; exact Set.mem_insert_of_mem _ rfl
    exact this
  obtain ⟨a, hav, hla⟩ := hea
  obtain ⟨b, hbv, hlb⟩ := heb
  -- Closure: every `v`-incident edge is `eₐ` or `e_b` (no loops at `v`).
  have hclosure : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b := by
    intro e x hlink
    have hinc : G.Inc e v := hlink.inc_left
    rcases hinc.isLoopAt_or_isNonloopAt with hloop | hnonloop
    · exact absurd (Set.eq_empty_iff_forall_notMem.mp
        (Set.ncard_eq_zero (Set.toFinite _) |>.mp hloop0) e hloop) id
    · have : e ∈ ({eₐ, e_b} : Set β) := hset ▸ hnonloop
      simpa [Set.mem_insert_iff] using this
  exact ⟨a, b, eₐ, e_b, hav, hbv, hla.right_mem, hlb.right_mem, hne, hla, hlb, hclosure⟩

/-- **Reduction of minimal `0`-dof-graphs** (`thm:minimal-kdof-reduction`; Katoh–Tanigawa 2011
Theorem 4.9). The combinatorial skeleton of the molecular conjecture's induction, phrased as the
well-founded induction principle that the reduction dichotomy + the vertex-count measure drive.

For `D = bodyBarDim n ≥ 3` (the molecular regime `n ≥ 2`), a motive `P` on graphs that

* holds for every minimal `0`-dof-graph on exactly two vertices (the two-vertex double edge,
  `hbase`),
* is reflected by splitting off a reducible degree-2 vertex — if `P` holds of the splitting-off
  `G_v^{ab}` then it holds of `G` (`hsplit`), and
* is reflected by contracting a proper rigid subgraph, given the induction hypothesis on every
  strictly-smaller minimal `0`-dof-graph (`hcontract`),

holds of every minimal `0`-dof-graph `G` with `2 ≤ |V(G)|`. The proof is the `|V|`-induction
(`lem:reduction-measure`): the base case `|V| = 2`; for `|V| ≥ 3`, either `G` has a proper rigid
subgraph — apply `hcontract` with the strong induction hypothesis — or it does not, in which case
`exists_degree_eq_two` (`lem:reducible-vertex`) supplies a degree-2 vertex,
`exists_splitOff_data_of_degree_eq_two` its two incident edges, and `splitOff_isMinimalKDof`
(`lem:reduction-step`) makes the splitting-off a strictly-smaller (`splitOff_vertexSet_ncard_lt`)
minimal `0`-dof-graph on which the induction hypothesis closes the `hsplit` premise.

The contraction branch is handed only the *existence* of a proper rigid subgraph together with
the strong induction hypothesis (rather than recursing on `rigidContract` internally): bridging
the matroid-side `contraction_isMinimalKDof` to a graph-level `(G.rigidContract H r).IsMinimalKDof`
is the graph↔matroid correspondence Phase 20 deliberately did not build (see `notes/Phase20.md`),
and a single-vertex subgraph is vacuously rigid so the predicate alone does not force the measure
to drop — the user discharges Case I from `H`. The splitting-off branch, fully graph-level,
recurses internally. The `hfresh` premise supplies an unused edge label for each splitting-off
(`splitOff` injects a fresh `e₀`); it holds whenever `β` is not exhausted by `E(G)` — e.g. `β`
infinite, or large relative to the edge count. This is the combinatorial backbone the algebraic
induction (Phases 21–23) realizes at the rigidity-matrix rank. -/
theorem minimal_kdof_reduction [DecidableEq β] [Finite α] [Finite β] {n : ℕ}
    (hD : 3 ≤ bodyBarDim n) (hfresh : ∀ G' : Graph α β, ∃ e₀ : β, e₀ ∉ E(G'))
    {P : Graph α β → Prop}
    (hbase : ∀ G : Graph α β, G.IsMinimalKDof n 0 → V(G).ncard = 2 → P G)
    (hsplit : ∀ (G : Graph α β) (v a b : α) (eₐ e_b e₀ : β),
      G.IsMinimalKDof n 0 → (∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) →
      v ∈ V(G) → a ≠ v → b ≠ v → a ∈ V(G) → b ∈ V(G) → eₐ ≠ e_b →
      G.IsLink eₐ v a → G.IsLink e_b v b → (∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b) →
      e₀ ∉ E(G) → P (G.splitOff v a b e₀) → P G)
    (hcontract : ∀ G : Graph α β, G.IsMinimalKDof n 0 → 3 ≤ V(G).ncard →
      (∃ H : Graph α β, H.IsProperRigidSubgraph G n) →
      (∀ G' : Graph α β, G'.IsMinimalKDof n 0 → 2 ≤ V(G').ncard →
        V(G').ncard < V(G).ncard → P G') → P G) :
    ∀ G : Graph α β, G.IsMinimalKDof n 0 → 2 ≤ V(G).ncard → P G := by
  classical
  have hD1 : 1 ≤ bodyBarDim n := le_trans (by norm_num) hD
  have hD2 : 2 ≤ bodyBarDim n := le_trans (by norm_num) hD
  -- Strong induction on the vertex count `|V(G)|`.
  intro G
  induction hN : V(G).ncard using Nat.strong_induction_on generalizing G with
  | _ N IH =>
  intro hG hV2
  rcases eq_or_lt_of_le hV2 with hVeq | hVlt
  · exact hbase G hG (hN.trans hVeq.symm)
  · -- `|V(G)| ≥ 3`: split on the existence of a proper rigid subgraph.
    have hV3 : 3 ≤ V(G).ncard := by rw [hN]; omega
    by_cases hrig : ∃ H : Graph α β, H.IsProperRigidSubgraph G n
    · -- Case I: contract a proper rigid subgraph (handed the strong induction hypothesis).
      refine hcontract G hG hV3 hrig (fun G' hG' hG'2 hlt => IH _ (hN ▸ hlt) _ rfl hG' hG'2)
    · -- Case II: no proper rigid subgraph ⟹ a reducible degree-2 vertex; split it off.
      push Not at hrig
      have hV2' : 2 ≤ V(G).ncard := by rw [hN]; exact hV2
      obtain ⟨v, hvG, hvdeg⟩ := exists_degree_eq_two hD hV2' hG hrig
      -- A companion vertex `b₀ ≠ v` (exists since `|V(G)| ≥ 2`).
      obtain ⟨b₀, hb₀G, hb₀v⟩ : ∃ b₀ ∈ V(G), b₀ ≠ v := by
        by_contra h
        push Not at h
        have hsub : V(G) ⊆ {v} := fun x hx => h x hx
        have : V(G).ncard ≤ 1 := by
          rw [← Set.ncard_singleton v]; exact Set.ncard_le_ncard hsub (Set.toFinite _)
        omega
      obtain ⟨a, b, eₐ, e_b, hav, hbv, haV, hbV, heab, hla, hlb, hdeg2⟩ :=
        exists_splitOff_data_of_degree_eq_two hD1 hG.1 hvG hb₀G hb₀v hvdeg
      -- A fresh edge label `e₀ ∉ E(G)` (the freshness hypothesis: `β` carries unused labels).
      obtain ⟨e₀, he₀⟩ := hfresh G
      have hsplitMin : (G.splitOff v a b e₀).IsMinimalKDof n 0 :=
        splitOff_isMinimalKDof hD2 hav hbv haV hbV hvG heab hla hlb hdeg2 he₀ hG hrig
      have hsmaller : V(G.splitOff v a b e₀).ncard < N :=
        hN ▸ splitOff_vertexSet_ncard_lt hvG
      have hsplit2 : 2 ≤ V(G.splitOff v a b e₀).ncard := by
        rw [vertexSet_splitOff]
        have hdv : (V(G) \ {v}).ncard = V(G).ncard - 1 := by
          rw [Set.ncard_diff (by simpa using hvG) (Set.toFinite _), Set.ncard_singleton]
        omega
      exact hsplit G v a b eₐ e_b e₀ hG hrig hvG hav hbv haV hbV heab hla hlb hdeg2 he₀
        (IH _ hsmaller _ rfl hsplitMin hsplit2)

/-! ### The repacking descent: a base admits a balanced forest packing
(`lem:forest-surgery-split`, the balanced-packing descent — outer loop)

This closes the balanced-packing assumption Katoh–Tanigawa 2011 Lemma 4.1 (p.660) glosses
(`rem:kt-lemma-41`~(2)): **a base of `M(G̃)` admits a `D`-forest packing in which every one
of the `D` forests meets the degree-2 vertex `v`.** The two halves and their assembly step
are green: the counting half (`isBase_vfiber_ncard_ge`: a base meets `≥ D` of the `2(D−1)`
fibers at `v`), the redistribution kernel (`acyclicSet_insert_vfiber_of_not_inc`: a
`v`-avoiding forest absorbs a free `v`-fiber as a pendant), and one rebalancing move
(`exists_packing_move_of_not_inc`). This is the **outer loop** that iterates the move to
termination.

The descent runs on a *disjoint* forest packing (a genuine partition of the base `B`, not
merely a cover), obtained by `disjointed` from the `Matroid.union_indep_iff` cover
(`matroidMG_indep_iff_exists_forest_packing`). Disjointness is the device that handles the
caveat the cover form leaves open — when a `v`-fiber `x` is moved into a `v`-avoiding forest
`F_j`, it is removed from every *other* forest, and disjointness guarantees `x` belonged to
exactly one donor, so at most one forest can lose `v`-incidence. The pigeonhole then makes
the move strictly safe: if `F_j` avoids `v`, then the `≥ D` `v`-fibers of `B` are partitioned
among the other `≤ D − 1` forests, so some forest `F_i` (`i ≠ j`) holds `≥ 2` of them; moving
one to `F_j` leaves `F_i` still meeting `v` while `F_j` now meets `v`, strictly raising the
count of `v`-meeting forests. A strong induction on the count of `v`-avoiding forests
terminates with a balanced packing. Off the Theorem-4.9 critical path (the deficiency route
already delivered Theorem 4.9); this discharges the deferred surgery TODO's last piece. -/

/-- A `v`-fiber (a copy of `eₐ` or `e_b`) is incident to `v` in `G̃`, and conversely a fiber
of `E(G̃)` incident to `v` is a `v`-fiber, when `eₐ`, `e_b` are the only `v`-incident edges. -/
private lemma vfiber_inc_iff {G : Graph α β} {n : ℕ} {v a b : α} {eₐ e_b : β}
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    {p : β × Fin (bodyHingeMult n)} (_hpE : p ∈ E(G.mulTilde n)) :
    (G.mulTilde n).Inc p v ↔ p ∈ edgeFiber eₐ n ∪ edgeFiber e_b n := by
  rw [mulTilde_inc]
  constructor
  · rintro ⟨w, hw⟩
    rcases hdeg2 p.1 w hw with h | h
    · exact Or.inl (by rw [edgeFiber, Set.mem_setOf_eq]; exact h)
    · exact Or.inr (by rw [edgeFiber, Set.mem_setOf_eq]; exact h)
  · rintro (h | h) <;> rw [edgeFiber, Set.mem_setOf_eq] at h <;> rw [h]
    · exact hla.inc_left
    · exact hlb.inc_left

/-- **The repacking descent (outer loop): a base admits a balanced forest packing**
(`lem:forest-surgery-split`; Katoh–Tanigawa 2011 Lemma 4.1 p.660). For a base `B` of
`M(G̃)` at a degree-2 vertex `v` (with `eₐ`, `e_b` its only incident edges, `D ≥ 2`), there
is a `D`-forest packing of `B` — `D = bodyBarDim n` cycle-matroid-independent fiber sets
covering `B` — in which **every** forest meets `v`. This is the balanced packing Katoh–
Tanigawa's Lemma 4.1 base-case proof assumes without justification; it is achievable, so
the missing step is a *gap, not an error*.

Proof: disjointify the `Matroid.union_indep_iff` cover of the base
(`matroidMG_indep_iff_exists_forest_packing`) into a genuine partition, then run a strong
induction on the number of `v`-avoiding forests. The base meets `≥ D` `v`-fibers
(`isBase_vfiber_ncard_ge`); if some forest avoids `v`, the pigeonhole forces another forest
to hold `≥ 2` of them, and the rebalancing move (`exists_packing_move_of_not_inc`, recipient
acyclic via `acyclicSet_insert_vfiber_of_not_inc`) shifts one over, strictly raising the
count of `v`-meeting forests while preserving disjointness. -/
theorem exists_balanced_forest_packing [DecidableEq β] [Finite α] [Finite β] {G : Graph α β}
    {n : ℕ} (hD : 2 ≤ bodyBarDim n) {v a b : α} {eₐ e_b : β}
    (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b)
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    {B : Set (β × Fin (bodyHingeMult n))} (hB : (G.matroidMG n).IsBase B) :
    ∃ Fs : Fin (bodyBarDim n) → Set (β × Fin (bodyHingeMult n)),
      (⋃ i, Fs i = B) ∧ (∀ i, ((G.mulTilde n).cycleMatroid).Indep (Fs i)) ∧
        (Pairwise (Function.onFun Disjoint Fs)) ∧
        (∀ i, ∃ p ∈ Fs i, (G.mulTilde n).Inc p v) := by
  classical
  haveI : Nonempty (Fin (bodyBarDim n)) := ⟨⟨0, lt_of_lt_of_le (by norm_num) hD⟩⟩
  set vfib := edgeFiber eₐ n ∪ edgeFiber e_b n with hvfib
  have hBE : B ⊆ E(G.mulTilde n) := by
    have := hB.subset_ground; rwa [matroidMG] at this
  have hinciff : ∀ p ∈ E(G.mulTilde n),
      ((G.mulTilde n).Inc p v ↔ p ∈ vfib) := fun p hp ↦ vfiber_inc_iff hla hlb hdeg2 hp
  have hcount : bodyBarDim n ≤ (B ∩ vfib).ncard :=
    isBase_vfiber_ncard_ge hD hav hbv heab hla hlb hdeg2 hB
  have hmeet_iff : ∀ F : Set (β × Fin (bodyHingeMult n)), F ⊆ B →
      ((∃ p ∈ F, (G.mulTilde n).Inc p v) ↔ (F ∩ vfib).Nonempty) := by
    intro F hF
    constructor
    · rintro ⟨p, hpF, hpinc⟩
      exact ⟨p, hpF, (hinciff p (hBE (hF hpF))).mp hpinc⟩
    · rintro ⟨p, hpF, hpv⟩
      exact ⟨p, hpF, (hinciff p (hBE (hF hpF))).mpr hpv⟩
  -- Disjointify the cover of `B` into a genuine partition (`disjointed` over `Fin D`).
  obtain ⟨Fs₀, hcover₀, hindep₀⟩ :=
    ((matroidMG_indep_iff_exists_forest_packing G n).mp hB.indep).2
  set Ds := disjointed Fs₀ with hDs
  have hDscover : ⋃ i, Ds i = B := by rw [hDs, iUnion_disjointed]; exact hcover₀
  have hDsindep : ∀ i, ((G.mulTilde n).cycleMatroid).Indep (Ds i) :=
    fun i ↦ (hindep₀ i).subset (disjointed_le Fs₀ i)
  have hDsdisj : Pairwise (Function.onFun Disjoint Ds) := disjoint_disjointed Fs₀
  -- Strong induction on the count of `v`-avoiding forests.
  suffices H : ∀ m : ℕ, ∀ Fs : Fin (bodyBarDim n) → Set (β × Fin (bodyHingeMult n)),
      (⋃ i, Fs i = B) → (∀ i, ((G.mulTilde n).cycleMatroid).Indep (Fs i)) →
      Pairwise (Function.onFun Disjoint Fs) →
      {i | (Fs i ∩ vfib) = ∅}.ncard ≤ m →
      ∃ Fs' : Fin (bodyBarDim n) → Set (β × Fin (bodyHingeMult n)),
        (⋃ i, Fs' i = B) ∧ (∀ i, ((G.mulTilde n).cycleMatroid).Indep (Fs' i)) ∧
          (Pairwise (Function.onFun Disjoint Fs')) ∧
          (∀ i, (Fs' i ∩ vfib).Nonempty) by
    obtain ⟨Fs', hc, hi, hd, hmeet⟩ :=
      H {i | (Ds i ∩ vfib) = ∅}.ncard Ds hDscover hDsindep hDsdisj le_rfl
    refine ⟨Fs', hc, hi, hd, fun i ↦ ?_⟩
    exact (hmeet_iff (Fs' i) (hc ▸ Set.subset_iUnion Fs' i)).mpr (hmeet i)
  intro m
  induction m with
  | zero =>
    intro Fs hcover hindep hdisj hle
    refine ⟨Fs, hcover, hindep, hdisj, fun i ↦ ?_⟩
    have hempty : {i | (Fs i ∩ vfib) = ∅} = ∅ := by
      rw [← Set.ncard_eq_zero (Set.toFinite _)]; omega
    by_contra hne
    have hmem : i ∈ {i | (Fs i ∩ vfib) = ∅} := Set.not_nonempty_iff_eq_empty.mp hne
    rw [hempty] at hmem; exact hmem
  | succ m ih =>
    intro Fs hcover hindep hdisj hle
    by_cases hbal : ∀ i, (Fs i ∩ vfib).Nonempty
    · exact ⟨Fs, hcover, hindep, hdisj, hbal⟩
    simp only [not_forall, Set.not_nonempty_iff_eq_empty] at hbal
    obtain ⟨j, hj⟩ := hbal
    have hssubB : ∀ i, Fs i ⊆ B := fun i ↦ hcover ▸ Set.subset_iUnion Fs i
    -- Pigeonhole: `∑_i |Fs i ∩ vfib| = |B ∩ vfib| ≥ D`, `j` contributes `0`,
    -- `D` indices ⟹ some `i` has `|Fs i ∩ vfib| ≥ 2`.
    have hpart : ∑ i, (Fs i ∩ vfib).ncard = (B ∩ vfib).ncard := by
      rw [← finsum_eq_sum_of_fintype,
        ← Set.ncard_iUnion_of_finite (fun i ↦ Set.toFinite _)
          (fun s t hst ↦ (hdisj hst).mono Set.inter_subset_left Set.inter_subset_left),
        ← Set.iUnion_inter, hcover]
    have hjzero : (Fs j ∩ vfib).ncard = 0 := by rw [hj]; exact Set.ncard_empty _
    obtain ⟨i, hij, hidonor⟩ : ∃ i, i ≠ j ∧ 2 ≤ (Fs i ∩ vfib).ncard := by
      by_contra hcon
      simp only [not_exists, not_and, not_le] at hcon
      have hbnd : ∀ k ∈ Finset.univ, (Fs k ∩ vfib).ncard ≤ (if k = j then 0 else 1) := by
        intro k _
        by_cases hkj : k = j
        · subst hkj; simp [hjzero]
        · simpa [hkj] using Nat.lt_succ_iff.mp (hcon k hkj)
      have hsum : ∑ k : Fin (bodyBarDim n), (if k = j then (0:ℕ) else 1)
          = bodyBarDim n - 1 := by
        have hcong : (∑ k : Fin (bodyBarDim n), if k = j then (0:ℕ) else 1)
            = (Finset.univ.filter (fun k => k ≠ j)).card := by
          rw [Finset.card_filter]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          by_cases h : k = j <;> simp [h]
        rw [hcong, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ j),
          Finset.card_univ, Fintype.card_fin]
      have hle' := Finset.sum_le_sum hbnd
      rw [hsum, hpart] at hle'
      omega
    -- Pick a spare `v`-fiber `x ∈ Fs i ∩ vfib`. `Fs i` holds `≥ 2`, so it is nonempty.
    obtain ⟨x, hxFi, hxvfib⟩ : (Fs i ∩ vfib).Nonempty := by
      rw [← Set.ncard_pos (Set.toFinite _)]; omega
    -- `x` is a non-loop `v`-fiber: `IsLink x v a` (if `eₐ`) or `IsLink x v b` (if `e_b`).
    have hxlink : ∃ w, (G.mulTilde n).IsLink x v w ∧ w ≠ v := by
      rcases hxvfib with hxe | hxe <;> rw [edgeFiber, Set.mem_setOf_eq] at hxe
      · exact ⟨a, by rw [mulTilde_isLink, hxe]; exact hla, hav⟩
      · exact ⟨b, by rw [mulTilde_isLink, hxe]; exact hlb, hbv⟩
    obtain ⟨w, hxvw, hwv⟩ := hxlink
    have hxB : x ∈ B := hssubB i hxFi
    -- `Fs j` avoids `v`: any `v`-incident fiber would be in `vfib`, but `Fs j ∩ vfib = ∅`.
    have hFjv : ∀ p ∈ Fs j, ¬ (G.mulTilde n).Inc p v := by
      intro p hpFj hpinc
      have : p ∈ Fs j ∩ vfib := ⟨hpFj, (hinciff p (hBE (hssubB j hpFj))).mp hpinc⟩
      rw [hj] at this; exact this
    -- The explicit move.
    set Fs' : Fin (bodyBarDim n) → Set (β × Fin (bodyHingeMult n)) :=
      fun k => if k = j then insert x (Fs j) else Fs k \ {x} with hFs'
    have hcover' : ⋃ k, Fs' k = B := by
      apply Set.Subset.antisymm
      · rintro p hp
        rw [Set.mem_iUnion] at hp
        obtain ⟨k, hk⟩ := hp
        by_cases hkj : k = j
        · subst hkj; simp only [hFs', ↓reduceIte] at hk
          rcases Set.mem_insert_iff.mp hk with rfl | hk'
          · exact hxB
          · exact hssubB k hk'
        · simp only [hFs', if_neg hkj] at hk; exact hssubB k hk.1
      · rw [← hcover]
        rintro p hp
        rw [Set.mem_iUnion] at hp ⊢
        obtain ⟨k, hk⟩ := hp
        by_cases hpx : p = x
        · exact ⟨j, by simp only [hFs', ↓reduceIte]; exact Set.mem_insert_iff.mpr (Or.inl hpx)⟩
        · by_cases hkj : k = j
          · subst hkj
            exact ⟨k, by simp only [hFs', ↓reduceIte]; exact Set.mem_insert_iff.mpr (Or.inr hk)⟩
          · exact ⟨k, by simp only [hFs', if_neg hkj]; exact ⟨hk, by simpa using hpx⟩⟩
    have hindep' : ∀ k, ((G.mulTilde n).cycleMatroid).Indep (Fs' k) := by
      intro k
      by_cases hkj : k = j
      · subst hkj
        simp only [hFs', ↓reduceIte]
        exact acyclicSet_insert_vfiber_of_not_inc (hindep k) hxvw hwv hFjv
      · simp only [hFs', if_neg hkj]; exact (hindep k).subset Set.diff_subset
    have hdisj' : Pairwise (Function.onFun Disjoint Fs') := by
      intro k l hkl
      simp only [Function.onFun, hFs']
      rcases eq_or_ne k j with rfl | hk
      · simp only [↓reduceIte, if_neg (Ne.symm hkl), Set.disjoint_left]
        rintro p hpins ⟨hpFl, hpx⟩
        rcases Set.mem_insert_iff.mp hpins with rfl | hpFj
        · exact hpx rfl
        · exact (hdisj (Ne.symm hkl)).le_bot ⟨hpFl, hpFj⟩
      · simp only [if_neg hk]
        rcases eq_or_ne l j with rfl | hl
        · simp only [↓reduceIte, Set.disjoint_right]
          rintro p hpins ⟨hpFk, hpx⟩
          rcases Set.mem_insert_iff.mp hpins with rfl | hpFj
          · exact hpx rfl
          · exact (hdisj hk).le_bot ⟨hpFk, hpFj⟩
        · simp only [if_neg hl]
          exact (hdisj hkl).mono Set.diff_subset Set.diff_subset
    -- The `v`-avoiding count strictly drops: `j` leaves it; `i` and others don't enter it.
    -- `x ∈ Fs' j ∩ vfib`, so `j` no longer avoids `v`.
    have hxFs'j : x ∈ Fs' j ∩ vfib :=
      ⟨by simp only [hFs', ↓reduceIte]; exact Set.mem_insert _ _, hxvfib⟩
    have hdrop : {k | (Fs' k ∩ vfib) = ∅}.ncard < {k | (Fs k ∩ vfib) = ∅}.ncard := by
      apply Set.ncard_lt_ncard _ (Set.toFinite _)
      constructor
      · -- `{k | Fs' k ∩ vfib = ∅} ⊆ {k | Fs k ∩ vfib = ∅}`.
        intro k hk
        simp only [Set.mem_setOf_eq] at hk ⊢
        by_cases hkj : k = j
        · subst hkj
          -- `Fs' j ⊇ {x}`, `x ∈ vfib`, so `Fs' j ∩ vfib ≠ ∅` — `hk` is impossible.
          exact absurd (hk ▸ hxFs'j) (Set.notMem_empty x)
        · -- `Fs' k = Fs k \ {x}`. Show `Fs k ∩ vfib = ∅`.
          simp only [hFs', if_neg hkj] at hk
          rw [Set.eq_empty_iff_forall_notMem] at hk ⊢
          intro p hp
          rcases eq_or_ne p x with hpx | hpx
          · -- `p = x ∈ Fs k`; disjointness with `x ∈ Fs i` forces `k = i`, but then
            -- `Fs i ∩ vfib` (card ≥ 2) has some `y ≠ x` surviving the deletion — contra `hk`.
            have hxFk : x ∈ Fs k := hpx ▸ hp.1
            have hki : k = i := by
              by_contra hne
              exact Set.disjoint_left.mp (hdisj (Ne.symm hne)) hxFi hxFk
            subst hki
            obtain ⟨y, hy, hyne⟩ := Set.exists_ne_of_one_lt_ncard hidonor x
            exact hk y ⟨⟨hy.1, by simpa using hyne⟩, hy.2⟩
          · exact hk p ⟨⟨hp.1, by simpa using hpx⟩, hp.2⟩
      · -- `j` is in the old avoiding-set but not the new one.
        refine fun hsub ↦ ?_
        have hjnew : (Fs' j ∩ vfib) = ∅ := hsub (show j ∈ {k | (Fs k ∩ vfib) = ∅} from hj)
        exact absurd (hjnew ▸ hxFs'j) (Set.notMem_empty x)
    exact ih Fs' hcover' hindep' hdisj' (by omega)

/-! ### The surgery count (`lem:forest-surgery-count`, Katoh–Tanigawa Lemma 4.1)

The cardinality bookkeeping that the corrected forest surgery rests on. Starting from a
*balanced* edge-disjoint `D`-forest packing of a base `I` of `M(G̃)` — every forest meets the
degree-2 vertex `v` (`exists_balanced_forest_packing`) — reroute each forest across `v`:

* a `v`-degree-`2` forest (one `eₐ`-copy `pa`, one `e_b`-copy `pb`) drops `{pa, pb}` and adds a
  *single* short-circuit copy `r = (e₀, pa.2)` of `ã̃b` (via `isAcyclicSet_splitOff_reroute`);
* a `v`-degree-`1` forest drops its lone `v`-fiber and adds **nothing**
  (acyclicity: `isAcyclicSet_splitOff_of_diff_fiberAtVertex`).

Every forest has `v`-degree `1` or `2` — at least `1` by balance, at most `2` because two copies
of the same `v`-edge form a `2`-cycle (`fiber_inter_subsingleton_of_isAcyclicSet_mulTilde`,
applied to `eₐ` and `e_b` separately, the only two edges at the degree-2 vertex `v`). So **every**
forest shrinks by exactly one (`|F'ᵢ| + 1 = |Fᵢ|`), and as the packing partitions `I`, the
rerouted union satisfies `|⋃ F'ᵢ| + D = |I|`. This is precisely Katoh–Tanigawa's accounting
`2h' + (D − h') = h` — `h` fibers dropped, `h'` short-circuit copies added, net `−D` — handling
the `dᶠ(v) = 1` forests their proof glosses. The added copies are distinct across the degree-`2`
forests: `r i = (e₀, (pa i).2)`, and the `pa i` (distinct `eₐ`-copies in disjoint forests) have
distinct second coordinates, so `≤ D − 1` such copies are needed and `D − 1` exist. Off the
Theorem-4.9 critical path (the deficiency route already delivered Theorem 4.9). -/

/-- **The surgery count `|⋃ F'ᵢ| + D = |I|`** (`lem:forest-surgery-count`; Katoh–Tanigawa 2011
Lemma 4.1 p.660). Let `v` be a degree-2 vertex of `G` with distinct neighbours `a ≠ b`
(`a, b ≠ v ∈ V(G)`, incident edges exactly `eₐ ≠ e_b`), `e₀ ∉ E(G)` fresh, `D = bodyBarDim n ≥ 2`.
Given a *balanced* edge-disjoint `D`-forest packing `Fs` of a fiber set `I` — `⋃ Fs i = I`, each
`Fs i` acyclic in `G̃`, pairwise disjoint, and **every** forest meets `v`
(`exists_balanced_forest_packing`) — there is a rerouted family `Fs'` that is an edge-disjoint
`D`-forest packing of the multiplied splitting-off `G̃_v^{ab}` whose union is `M(G̃_v^{ab})`-indep
and satisfies
`(⋃ i, Fs' i).ncard + bodyBarDim n = I.ncard`.

This is the corrected construction (the superseded `forest_surgery_split` was vacuous and assumed
away the `dᶠ(v) = 1` forests): every forest shrinks by exactly one because a degree-`2` forest
loses two `v`-fibers and gains one `ã̃b`-copy while a degree-`1` forest loses one and gains none.
See the section preamble. -/
theorem forest_surgery_count [DecidableEq β] [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hD : 2 ≤ bodyBarDim n) {v a b : α} {eₐ e_b e₀ : β}
    (hab : a ≠ b) (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b)
    (haV : a ∈ V(G)) (hbV : b ∈ V(G)) (he₀ : e₀ ∉ E(G))
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    {I : Set (β × Fin (bodyHingeMult n))}
    (Fs : Fin (bodyBarDim n) → Set (β × Fin (bodyHingeMult n)))
    (hcover : ⋃ i, Fs i = I) (hindep : ∀ i, ((G.mulTilde n).cycleMatroid).Indep (Fs i))
    (hdisj : Pairwise (Function.onFun Disjoint Fs))
    (hmeet : ∀ i, ∃ p ∈ Fs i, (G.mulTilde n).Inc p v) :
    ∃ Fs' : Fin (bodyBarDim n) → Set (β × Fin (bodyHingeMult n)),
      (∀ i, ((G.splitOff v a b e₀).mulTilde n).cycleMatroid.Indep (Fs' i)) ∧
      (Pairwise (Function.onFun Disjoint Fs')) ∧
      ((G.splitOff v a b e₀).matroidMG n).Indep (⋃ i, Fs' i) ∧
      (⋃ i, Fs' i).ncard + bodyBarDim n = I.ncard := by
  classical
  -- Each forest is finite (subset of the finite ground set).
  have hssubE : ∀ i, Fs i ⊆ E(G.mulTilde n) := fun i ↦ (hindep i).subset_ground
  -- `fiberAtVertex v ⊆ ẽₐ ∪ ẽ_b`: the only `v`-incident edges are `eₐ, e_b`.
  have hfibsub : G.fiberAtVertex n v ⊆ edgeFiber eₐ n ∪ edgeFiber e_b n := by
    intro p hp
    rw [mem_fiberAtVertex] at hp
    obtain ⟨x, hlx⟩ := hp
    rcases hdeg2 p.1 x hlx with h | h
    · exact Or.inl (by rw [edgeFiber, Set.mem_setOf_eq]; exact h)
    · exact Or.inr (by rw [edgeFiber, Set.mem_setOf_eq]; exact h)
  -- Per-edge subsingleton: a forest holds ≤ 1 copy of `eₐ`, ≤ 1 of `e_b`.
  have hsubₐ : ∀ i, (Fs i ∩ edgeFiber eₐ n).Subsingleton := fun i ↦
    fiber_inter_subsingleton_of_isAcyclicSet_mulTilde (Ne.symm hav) hla (hindep i)
  have hsub_b : ∀ i, (Fs i ∩ edgeFiber e_b n).Subsingleton := fun i ↦
    fiber_inter_subsingleton_of_isAcyclicSet_mulTilde (Ne.symm hbv) hlb (hindep i)
  -- `Fs i ∩ fiberAtVertex v = (Fs i ∩ ẽₐ) ∪ (Fs i ∩ ẽ_b)`, the two pieces disjoint.
  have hfibdecomp : ∀ i, Fs i ∩ G.fiberAtVertex n v
      = (Fs i ∩ edgeFiber eₐ n) ∪ (Fs i ∩ edgeFiber e_b n) := by
    intro i
    apply Set.Subset.antisymm
    · rintro p ⟨hpF, hpv⟩
      rcases hfibsub hpv with h | h
      · exact Or.inl ⟨hpF, h⟩
      · exact Or.inr ⟨hpF, h⟩
    · rintro p (⟨hpF, hp⟩ | ⟨hpF, hp⟩) <;> refine ⟨hpF, ?_⟩ <;>
        rw [edgeFiber, Set.mem_setOf_eq] at hp <;> rw [mem_fiberAtVertex, hp]
      · exact hla.inc_left
      · exact hlb.inc_left
  have hfibdisj : Disjoint (edgeFiber eₐ n) (edgeFiber e_b n) := by
    rw [Set.disjoint_left]; rintro p hp hp'
    rw [edgeFiber, Set.mem_setOf_eq] at hp hp'; exact heab (hp ▸ hp')
  -- Degree at `v` of each forest is `1` or `2`.
  have hdeg : ∀ i, (Fs i ∩ G.fiberAtVertex n v).ncard = 1 ∨
      (Fs i ∩ G.fiberAtVertex n v).ncard = 2 := by
    intro i
    have hle2 : (Fs i ∩ G.fiberAtVertex n v).ncard ≤ 2 := by
      rw [hfibdecomp i]
      refine le_trans (Set.ncard_union_le _ _) ?_
      have := (Set.ncard_le_one_iff_subsingleton).mpr (hsubₐ i)
      have := (Set.ncard_le_one_iff_subsingleton).mpr (hsub_b i)
      omega
    have hpos : 1 ≤ (Fs i ∩ G.fiberAtVertex n v).ncard := by
      obtain ⟨p, hpF, hpv⟩ := hmeet i
      have : (Fs i ∩ G.fiberAtVertex n v).Nonempty :=
        ⟨p, hpF, by rw [mem_fiberAtVertex, ← mulTilde_inc]; exact hpv⟩
      exact this.ncard_pos (Set.toFinite _)
    omega
  -- When `dᶠ(v) = 2`, the two pieces `Fs i ∩ ẽₐ` and `Fs i ∩ ẽ_b` are each singletons; extract
  -- the `eₐ`-copy `paOf i` and `e_b`-copy `pbOf i`.
  have hdeg2_split : ∀ i, (Fs i ∩ G.fiberAtVertex n v).ncard = 2 →
      ∃ pa pb, Fs i ∩ edgeFiber eₐ n = {pa} ∧ Fs i ∩ edgeFiber e_b n = {pb} := by
    intro i hi
    rw [hfibdecomp i,
      Set.ncard_union_eq (hfibdisj.mono Set.inter_subset_right Set.inter_subset_right)
        (Set.toFinite _) (Set.toFinite _)] at hi
    have hca := (Set.ncard_le_one_iff_subsingleton).mpr (hsubₐ i)
    have hcb := (Set.ncard_le_one_iff_subsingleton).mpr (hsub_b i)
    obtain ⟨pa, hpa⟩ := Set.ncard_eq_one.mp (by omega : (Fs i ∩ edgeFiber eₐ n).ncard = 1)
    obtain ⟨pb, hpb⟩ := Set.ncard_eq_one.mp (by omega : (Fs i ∩ edgeFiber e_b n).ncard = 1)
    exact ⟨pa, pb, hpa, hpb⟩
  -- A fixed inhabitant of the fiber type (the else-branch placeholder; `Fs 0` meets `v`).
  haveI : Nonempty (β × Fin (bodyHingeMult n)) := ⟨(hmeet ⟨0, by omega⟩).choose⟩
  -- Choose, per `dᶠ = 2` forest, the swapped-out pair; `r i := (e₀, (paOf i).2)` is the fresh copy.
  set paOf : Fin (bodyBarDim n) → β × Fin (bodyHingeMult n) := fun i =>
    if h : (Fs i ∩ G.fiberAtVertex n v).ncard = 2 then (hdeg2_split i h).choose
    else Classical.arbitrary _ with hpaOf
  set r : Fin (bodyBarDim n) → β × Fin (bodyHingeMult n) := fun i => (e₀, (paOf i).2) with hr
  have hr1 : ∀ i, (r i).1 = e₀ := fun i ↦ rfl
  -- For `dᶠ = 2` forests, `paOf i` is the unique `eₐ`-copy (so `paOf i ∈ Fs i`, `.1 = eₐ`).
  have hpaOf_mem : ∀ i, (Fs i ∩ G.fiberAtVertex n v).ncard = 2 →
      paOf i ∈ Fs i ∩ edgeFiber eₐ n := by
    intro i hi
    have hsing := (hdeg2_split i hi).choose_spec.choose_spec.1
    simp only [hpaOf, dif_pos hi]
    exact hsing.ge (Set.mem_singleton _)
  -- `r` is injective across the `dᶠ = 2` forests: distinct `eₐ`-copies in disjoint forests have
  -- distinct second coordinates.
  have hr_inj2 : ∀ i j, (Fs i ∩ G.fiberAtVertex n v).ncard = 2 →
      (Fs j ∩ G.fiberAtVertex n v).ncard = 2 → r i = r j → i = j := by
    intro i j hi hj hrij
    by_contra hij
    have hpi := hpaOf_mem i hi
    have hpj := hpaOf_mem j hj
    have hpi1 : (paOf i).1 = eₐ := hpi.2
    have hpj1 : (paOf j).1 = eₐ := hpj.2
    -- `paOf i = paOf j`: same first coord `eₐ`, same second coord (from `r i = r j`).
    rw [hr] at hrij
    simp only at hrij
    have hsnd : (paOf i).2 = (paOf j).2 := (Prod.ext_iff.mp hrij).2
    have heq : paOf i = paOf j := Prod.ext_iff.mpr ⟨hpi1.trans hpj1.symm, hsnd⟩
    exact Set.disjoint_left.mp (hdisj hij) hpi.1 (heq ▸ hpj.1)
  -- The fresh copy `r i` is never in any forest of `G̃` (those are `G`-edge copies; `e₀ ∉ E(G)`).
  have hr_notin : ∀ i j, r i ∉ Fs j := by
    intro i j hrFj
    have hrE : r i ∈ E(G.mulTilde n) := hssubE j hrFj
    rw [mem_edgeSet_mulTilde] at hrE
    exact he₀ ((hr1 i) ▸ hrE)
  -- The rerouted family.
  set Fs' : Fin (bodyBarDim n) → Set (β × Fin (bodyHingeMult n)) := fun i =>
    if (Fs i ∩ G.fiberAtVertex n v).ncard = 2 then insert (r i) (Fs i \ G.fiberAtVertex n v)
    else Fs i \ G.fiberAtVertex n v with hFs'
  -- `Fs i ∖ fiberAtVertex v ⊆ Fs' i ⊆ insert (r i) (Fs i ∖ fiberAtVertex v)`, both branches.
  have hFs'sub : ∀ i, Fs' i ⊆ insert (r i) (Fs i \ G.fiberAtVertex n v) := by
    intro i; simp only [hFs']; split
    · exact subset_rfl
    · exact Set.subset_insert _ _
  have hsubFs' : ∀ i, Fs i \ G.fiberAtVertex n v ⊆ Fs' i := by
    intro i; simp only [hFs']; split
    · exact Set.subset_insert _ _
    · exact subset_rfl
  -- Each rerouted forest is acyclic in `G̃_v^{ab}`.
  have hindep' : ∀ i, ((G.splitOff v a b e₀).mulTilde n).cycleMatroid.Indep (Fs' i) := by
    intro i
    simp only [hFs']
    by_cases hi : (Fs i ∩ G.fiberAtVertex n v).ncard = 2
    · rw [if_pos hi]
      obtain ⟨pa, pb, hSpa, hSpb⟩ := hdeg2_split i hi
      have hpaF : pa ∈ Fs i := (hSpa ▸ Set.mem_singleton pa).1
      have hpbF : pb ∈ Fs i := (hSpb ▸ Set.mem_singleton pb).1
      have hpaℓ : (G.mulTilde n).IsLink pa v a := by
        have : pa.1 = eₐ := by
          have := (hSpa ▸ Set.mem_singleton pa).2; rwa [edgeFiber, Set.mem_setOf_eq] at this
        rw [mulTilde_isLink, this]; exact hla
      have hpbℓ : (G.mulTilde n).IsLink pb v b := by
        have : pb.1 = e_b := by
          have := (hSpb ▸ Set.mem_singleton pb).2; rwa [edgeFiber, Set.mem_setOf_eq] at this
        rw [mulTilde_isLink, this]; exact hlb
      have hpab : pa ≠ pb := by
        rintro rfl
        exact hab (hpaℓ.right_unique hpbℓ)
      -- `pa, pb` are exactly the `v`-fibers of `Fs i` (degree-2 ⟹ no others).
      have hall : ∀ q ∈ Fs i, (G.mulTilde n).Inc q v → q = pa ∨ q = pb := by
        intro q hqF hqv
        have hqfib : q ∈ Fs i ∩ G.fiberAtVertex n v :=
          ⟨hqF, by rw [mem_fiberAtVertex, ← mulTilde_inc]; exact hqv⟩
        rw [hfibdecomp i] at hqfib
        rcases hqfib with hqa | hqb
        · exact Or.inl (hSpa ▸ hqa : q ∈ ({pa} : Set _))
        · exact Or.inr (hSpb ▸ hqb : q ∈ ({pb} : Set _))
      have hdiff : Fs i \ G.fiberAtVertex n v = Fs i \ {pa, pb} := by
        ext q
        simp only [Set.mem_diff, mem_fiberAtVertex, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hqF, hqv⟩
          refine ⟨hqF, fun hq ↦ hqv ?_⟩
          rcases hq with rfl | rfl
          · exact hpaℓ.inc_left
          · exact hpbℓ.inc_left
        · rintro ⟨hqF, hq2⟩
          exact ⟨hqF, fun hqv ↦ hq2 (hall q hqF (mulTilde_inc.mpr hqv))⟩
      rw [hdiff]
      exact isAcyclicSet_splitOff_reroute hav hbv haV hbV (hindep i) hpaℓ hpbℓ hpaF hpbF hpab
        hall (hr1 i) he₀
    · rw [if_neg hi]
      exact isAcyclicSet_splitOff_of_diff_fiberAtVertex he₀ (hindep i)
  -- `r i` lies in `Fs' i` only when `Fs i` has `v`-degree `2` (else `Fs' i ⊆ Fs i`, `r i ∉ Fs i`).
  have hrmem : ∀ i, r i ∈ Fs' i → (Fs i ∩ G.fiberAtVertex n v).ncard = 2 := by
    intro i hri
    by_contra hi
    simp only [hFs', if_neg hi] at hri
    exact hr_notin i i hri.1
  -- Pairwise disjoint: the `v`-free cores are disjoint, and `r i ∈ Fs' i` forces `dᶠ(i) = 2`,
  -- where `r` is injective.
  have hdisj' : Pairwise (Function.onFun Disjoint Fs') := by
    intro i j hij
    simp only [Function.onFun, Set.disjoint_left]
    intro p hpi hpj
    rcases Set.mem_insert_iff.mp (hFs'sub i hpi) with hri | hci <;>
      rcases Set.mem_insert_iff.mp (hFs'sub j hpj) with hrj | hcj
    · -- `p = r i = r j`: both forests took the insert branch (`dᶠ = 2`), and `r` is injective.
      exact hij (hr_inj2 i j (hrmem i (hri ▸ hpi)) (hrmem j (hrj ▸ hpj)) (hri.symm.trans hrj))
    · exact hr_notin i j (hri ▸ hcj.1)
    · exact hr_notin j i (hrj ▸ hci.1)
    · exact (hdisj hij).le_bot ⟨hci.1, hcj.1⟩
  -- The rerouted union is a forest packing of `G̃_v^{ab}`, hence `M(G̃_v^{ab})`-independent.
  have hMindep : ((G.splitOff v a b e₀).matroidMG n).Indep (⋃ i, Fs' i) := by
    rw [matroidMG_indep_iff_exists_forest_packing]
    refine ⟨?_, Fs', rfl, hindep'⟩
    refine Set.iUnion_subset fun i ↦ ?_
    have := hindep' i
    rw [cycleMatroid_indep, isAcyclicSet_iff] at this
    exact this.1
  -- The count: every forest shrinks by exactly one.
  -- `(Fs i).ncard = (Fs i \ fib).ncard + (Fs i ∩ fib).ncard`.
  have hpart_i : ∀ i, (Fs i \ G.fiberAtVertex n v).ncard + (Fs i ∩ G.fiberAtVertex n v).ncard
      = (Fs i).ncard := fun i ↦ by
    rw [add_comm]
    exact Set.ncard_inter_add_ncard_diff_eq_ncard (Fs i) (G.fiberAtVertex n v) (Set.toFinite _)
  -- `r i ∉ Fs i \ fib`, so the insert adds exactly one.
  have hrnotcore : ∀ i, r i ∉ Fs i \ G.fiberAtVertex n v := fun i hri ↦ hr_notin i i hri.1
  have hshrink : ∀ i, (Fs' i).ncard + 1 = (Fs i).ncard := by
    intro i
    by_cases hi : (Fs i ∩ G.fiberAtVertex n v).ncard = 2
    · have hcard' : (Fs' i).ncard = (Fs i \ G.fiberAtVertex n v).ncard + 1 := by
        simp only [hFs', if_pos hi]
        rw [Set.ncard_insert_of_notMem (hrnotcore i) (Set.toFinite _)]
      have := hpart_i i; omega
    · have h1 : (Fs i ∩ G.fiberAtVertex n v).ncard = 1 := (hdeg i).resolve_right hi
      have hcard' : (Fs' i).ncard = (Fs i \ G.fiberAtVertex n v).ncard := by
        simp only [hFs', if_neg hi]
      have := hpart_i i; omega
  -- `∑ |Fs' i| + D = ∑ |Fs i| = |I|`.
  have hsumFs' : ∑ i, (Fs' i).ncard = (⋃ i, Fs' i).ncard := by
    rw [← finsum_eq_sum_of_fintype,
      ← Set.ncard_iUnion_of_finite (fun i ↦ Set.toFinite _) hdisj']
  have hsumFs : ∑ i, (Fs i).ncard = I.ncard := by
    rw [← finsum_eq_sum_of_fintype,
      ← Set.ncard_iUnion_of_finite (fun i ↦ Set.toFinite _) hdisj, hcover]
  have hcount : (⋃ i, Fs' i).ncard + bodyBarDim n = I.ncard := by
    have hkey : ∑ i : Fin (bodyBarDim n), ((Fs' i).ncard + 1) = ∑ i, (Fs i).ncard :=
      Finset.sum_congr rfl (fun i _ ↦ hshrink i)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one] at hkey
    rw [← hsumFs', ← hsumFs, hkey]
  exact ⟨Fs', hindep', hdisj', hMindep, hcount⟩

/-! ### The forest-surgery assembly (`lem:forest-surgery-split`, Katoh–Tanigawa Lemma 4.1)

The deficiency read-off that closes the splitting-off forest surgery. Starting from a base `B`
of `M(G̃)` at a degree-2 vertex `v`, a *balanced* `D`-forest packing exists
(`exists_balanced_forest_packing`); rerouting it across `v` (`forest_surgery_count`) yields a
`D`-forest packing of the multiplied splitting-off `G̃_v^{ab}` covering an `M(G̃_v^{ab})`-indep set
`I'` of size `|B| − D`. Hence `rank M(G̃_v^{ab}) ≥ |B| − D = rank M(G̃) − D`, and the
def\,=\,corank identity (`rank_add_deficiency_eq`, against the `D(|V| − 1)` trivial-motion
ambient — and `G̃_v^{ab}` has one fewer vertex) reads off
`def(G̃_v^{ab}) ≤ def(G̃)`, KT 4.1's intended conclusion. This is the same bound the
deficiency-count route delivers green as `splitOff_deficiency_le`; the surgery is off the
Theorem-4.9 critical path (`rem:kt-lemma-41`). -/

/-- **Forest surgery at a degree-2 vertex, splitting-off direction** (`lem:forest-surgery-split`;
Katoh–Tanigawa 2011 Lemma 4.1 p.660). Let `v` be a degree-2 vertex of `G` with distinct
neighbours `a ≠ b` (`a, b ≠ v ∈ V(G)`), incident edges exactly `eₐ ≠ e_b`, `e₀ ∉ E(G)` fresh,
`D = bodyBarDim n ≥ 2`, `V(G)` nonempty. Rerouting a balanced forest packing of a base of `M(G̃)`
across `v` (`exists_balanced_forest_packing` + `forest_surgery_count`) produces a forest packing
of `G̃_v^{ab}` of size `|base| − D`, an independent set of `M(G̃_v^{ab})`. The def\,=\,corank
identity then gives
`def(G̃_v^{ab}) ≤ def(G̃)`,
KT's Lemma 4.1 conclusion — the same bound the deficiency-count route delivers as
`splitOff_deficiency_le`. This is the assembled repair of the balanced-packing gloss
(`rem:kt-lemma-41`~(2)): the corrected `forest_surgery_count` handles the `dᶠ(v) = 1` forests
(drop their lone `v`-fiber, add no `ã̃b`-copy) that the superseded vacuous over-claim assumed
away. Off the Theorem-4.9 critical path. -/
theorem forest_surgery_split [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hD : 2 ≤ bodyBarDim n) {v a b : α} {eₐ e_b e₀ : β}
    (hab : a ≠ b) (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b)
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    (he₀ : e₀ ∉ E(G)) :
    (G.splitOff v a b e₀).deficiency n ≤ G.deficiency n := by
  classical
  haveI : Nonempty α := ⟨a⟩
  have hD1 : 1 ≤ bodyBarDim n := le_trans (by norm_num) hD
  have haV : a ∈ V(G) := hla.right_mem
  have hbV : b ∈ V(G) := hlb.right_mem
  have hvG : v ∈ V(G) := hla.left_mem
  have hVne : V(G).Nonempty := ⟨v, hvG⟩
  set H := G.splitOff v a b e₀ with hH
  have hVHne : V(H).Nonempty := ⟨a, by rw [hH, vertexSet_splitOff]; exact ⟨haV, hav⟩⟩
  -- A base `B` of `M(G̃)`, its balanced packing, and the reroute into `G̃_v^{ab}`.
  obtain ⟨B, hB⟩ := (G.matroidMG n).exists_isBase
  obtain ⟨Fs, hcover, hindep, hpdisj, hmeetv⟩ :=
    exists_balanced_forest_packing hD hav hbv heab hla hlb hdeg2 hB
  obtain ⟨Fs', _, _, hMindep, hcount⟩ :=
    forest_surgery_count hD hab hav hbv heab haV hbV he₀ hla hlb hdeg2 Fs hcover hindep
      hpdisj hmeetv
  -- `|⋃ Fs' i| ≤ rank M(G̃_v^{ab})`, and `|⋃ Fs' i| + D = |B|`.
  have hrkZ : (((⋃ i, Fs' i).ncard : ℤ)) ≤ ((H.matroidMG n).rank : ℤ) := by
    exact_mod_cast hMindep.ncard_le_rank
  have hcountZ : (((⋃ i, Fs' i).ncard : ℤ)) + (bodyBarDim n : ℤ) = (B.ncard : ℤ) := by
    exact_mod_cast hcount
  -- The two def = corank identities, and `|V(H)| = |V(G)| − 1`.
  have hBrank := G.isBase_ncard_add_deficiency_eq n hD1 hVne hB
  have hHrank := H.rank_add_deficiency_eq n hD1 hVHne
  have hVHcard : (V(H).ncard : ℤ) = (V(G).ncard : ℤ) - 1 := by
    rw [hH, vertexSet_splitOff, Set.ncard_diff_singleton_of_mem hvG]
    have : 0 < V(G).ncard := Set.ncard_pos (Set.toFinite _) |>.mpr hVne
    omega
  rw [hVHcard, mul_sub, mul_one] at hHrank
  -- Combine: `def(H̃) = D(|V|−2) − rank ≤ D(|V|−2) − (|B|−D) = D(|V|−1) − |B| = def(G̃)`.
  linarith [hrkZ, hcountZ, hBrank, hHrank]

/-- **The forest-surgery route to the KT-4.3 splitting-off deficiency bound**
(`cor:forest-surgery-deficiency`; narrative bridge). The deficiency bound
`def(G̃_v^{ab}) ≤ def(G̃)` that `dof_tracking` / Theorem 4.9 consume — landed on the
critical path by the deficiency-count `splitOff_deficiency_le` — is *also* the exact
conclusion of the off-path forest surgery `forest_surgery_split` (KT 4.1, splitting-off
direction). This lemma records that alternative route: it derives the same bound from the
forest reroute, the route Katoh–Tanigawa actually take. It is `@[deprecated]` in favour of
`splitOff_deficiency_le` because that deficiency-count lemma is the route the critical path
uses (and carries the weaker `1 ≤ bodyBarDim n`, no `a ≠ b`); this shim exists solely to
anchor the blueprint's narrative claim that the forest surgery reaches the same place, with
no Lean caller. The `@[deprecated]` shim pattern (and the `(since := "narrative-bridge")`
sentinel) is documented in `CombinatorialRigidity/CLAUDE.md` *Engineering conventions*. -/
@[deprecated splitOff_deficiency_le (since := "narrative-bridge")]
theorem splitOff_deficiency_le_of_forest_surgery [Finite α] [Finite β] {G : Graph α β}
    {n : ℕ} (hD : 2 ≤ bodyBarDim n) {v a b : α} {eₐ e_b e₀ : β}
    (hab : a ≠ b) (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b)
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    (he₀ : e₀ ∉ E(G)) :
    (G.splitOff v a b e₀).deficiency n ≤ G.deficiency n :=
  forest_surgery_split hD hab hav hbv heab hla hlb hdeg2 he₀

end Graph
