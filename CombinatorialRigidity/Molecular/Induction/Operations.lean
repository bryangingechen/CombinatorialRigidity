/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Deficiency
import Matroid.Graph.Minor.Defs

/-!
# The combinatorial induction — graph operations and contraction bridges (`sec:molecular-induction`)

Phase 20, the fourth phase of the molecular-conjecture program (Phases 17–26; see
`notes/MolecularConjecture.md`). This is the base file of the `Induction/` subdirectory.
Building on `Molecular/Deficiency.lean` (Phase 19, the matroid `M(G̃)` + `D`-deficiency +
`k`-dof hierarchy), this file develops the foundations of Katoh–Tanigawa's Theorem 4.9
(Katoh–Tanigawa 2011, *A proof of the molecular conjecture*, Discrete Comput. Geom. **45**,
§3.4–3.5, §4):

* the vertex-induced subgraph from a fiber set (`inducedSpan`) and the canonical endpoint
  selector (`endsOf`, `def:graph-operations`);
* **circuit-induces-rigid** (`circuit_induces_isRigidSubgraph`, `lem:circuit-induces-rigid`;
  KT Lemma 3.4): a circuit of `M(G̃)` minus an edge is `(D,D)`-tight on its vertex span;
* the forest-packing decomposition of `M(G̃)`-independent sets (`lem:forest-surgery-split`);
* the contraction rank and deficiency bridges (`lem:contraction-minimality`);
* the graph operations `removeVertex` and `splitOff` with their basic lemmas.

The deficiency-tracking, reducible-vertex, contraction-minimality, and forest-surgery layers
build on top in the sibling files `SplitOffDeficiency`, `ReducibleVertex`, `Contraction`, and
`ForestSurgery`. See `ROADMAP.md` §20 / `notes/Phase20.md` and the `sec:molecular-induction`
dep-graph of `blueprint/src/chapter/molecular-induction.tex`.
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

/-- **The canonical endpoint selector's two ends are distinct on every link of a loopless graph**
(`def:graph-operations`): if `G` is loopless and `e ∈ E(G)`, then `(G.endsOf e).1 ≠ (G.endsOf e).2`.
The canonical selector is a genuine link (`isLink_endsOf`), and a loopless graph's links join
*distinct* bodies (`IsLink.ne`). This is the edge-restricted endpoint-distinctness fact the Case-I
leg-transport brick `hasGenericRealization_transport_ends` consumes (KT eq. (6.6), Phase 22b): the
all-`β` form `∀ e, (G.endsOf e).1 ≠ (G.endsOf e).2` is *unsatisfiable* for `endsOf` (it returns the
junk constant `(default, default)` on non-edges), so the transversality input must be restricted to
the links, where it is discharged from `G.Simple`/`G.Loopless`. -/
lemma endsOf_fst_ne_snd [Inhabited α] (G : Graph α β) [G.Loopless] {e : β} (he : e ∈ E(G)) :
    (G.endsOf e).1 ≠ (G.endsOf e).2 :=
  (G.isLink_endsOf he).ne

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
remaining base-exchange count. The `[G.Loopless]` hypothesis (which the caller derives from
minimality via `loopless_of_isMinimalKDof`) feeds the `2 ≤ |V(H)|` conjunct of
`IsProperRigidSubgraph`: a circuit of a loopless graph spans two distinct vertices. -/
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

/-- **Splitting-off simplicity criterion** (the splitting-off sibling of the green Case-I
`rigidContract_simple`, Contraction.lean; the graph-side input to Theorem 5.5's *generic*
Case-III/splitting inductive hypothesis `hsplitGP`). The splitting-off `G_v^{ab}` is simple
provided

* `hloop` — no surviving edge is a loop: a link `e x y` of `G_v^{ab}` always has `x ≠ y`
  (rules out the fresh `e₀`-loop `a`-`a`, i.e. forces `a ≠ b`, and rules out any surviving
  `G`-edge becoming a self-link);
* `hpar` — no two surviving edges share an end-pair: links `e₁ x y` and `e₂ x y` of `G_v^{ab}`
  force `e₁ = e₂` (rules out a `G`-edge parallel to the fresh `e₀ = ab`, which is the
  obstruction KT Lemma 6.7(ii) routes to a triangle).

`splitOff` does **not** preserve simplicity unconditionally — it can manufacture both a loop
(when `a = b`) and a parallel pair (when `ab ∈ E(G)` already), which is why simplicity is a
*conditioned* fact rather than an instance (matching `map_simple`'s `Simple`-not-preserved-by-`map`
note). The hypotheses are phrased directly on `G_v^{ab}`'s links (the final edges), the analogue of
`rigidContract_simple`'s realized-graph `hloop`/`hpar`.

KT Lemma 6.7(ii) (Katoh–Tanigawa 2011, p. 677) discharges both from `G.Simple` together with the
no-proper-rigid-subgraph assumption `¬ ∃ H, H.IsProperRigidSubgraph G n`: a parallel edge to
`e₀ = ab` would force `ab ∈ E(G)`, giving the triangle `G[{va, vb, ab}]`, a `0`-dof (hence proper
rigid) subgraph — contradicting the assumption. That discharge (the `splitOff` analogue of Case I's
G2c step, itself routing through the not-yet-formalized "a triangle is `0`-dof" fact) is a separate
graph-side leaf; this lemma is the bounded criterion it feeds, exactly as `rigidContract_simple` is
the criterion its own composer discharges. -/
lemma splitOff_simple {G : Graph α β} {v a b : α} {e₀ : β}
    (hloop : ∀ e x y, (G.splitOff v a b e₀).IsLink e x y → x ≠ y)
    (hpar : ∀ e₁ e₂ x y, (G.splitOff v a b e₀).IsLink e₁ x y →
      (G.splitOff v a b e₀).IsLink e₂ x y → e₁ = e₂) :
    (G.splitOff v a b e₀).Simple where
  not_isLoopAt e x h := hloop e x x (isLink_self_iff.mp h) rfl
  eq_of_isLink e f x y he hf := hpar e f x y he hf

/-- **The splitting-off `G_v^{ab}` is simple** (KT Lemma 6.7(ii), Katoh–Tanigawa 2011 p. 677; the
graph-side discharge feeding Theorem 5.5's *generic* Case-III hypothesis `hsplitGP`). It discharges
both hypotheses of `splitOff_simple` from `G.Simple`, the splitting data, and the
no-proper-rigid-subgraph assumption `hnoRigid`, through the not-yet-formalized triangle brick
`htri`. The two combinatorial halves are bounded:

* **Loop-freeness.** A surviving `G`-edge inherits `G`'s looplessness; the fresh edge `e₀` links the
  *distinct* neighbours `a ≠ b` (`a = b` would make `eₐ, e_b` parallel `va`-edges, contradicting
  `G.Simple` via `heab`).
* **No parallel pair.** Two surviving `G`-edges with a shared end-pair coincide by `G.Simple`; two
  fresh edges both equal `e₀`; a *mixed* pair is the KT obstruction — a surviving `G`-edge `f`
  sharing `e₀`'s end-pair `{a, b}` is a pre-existing edge `f` with `G.IsLink f a b`, which together
  with `eₐ` (`va`) and `e_b` (`vb`) closes the triangle `G[{v, a, b}]`.

The triangle's rigidity is the one non-routine ingredient, carried here as `htri`: an `ab`-edge
yields a *proper* rigid subgraph of `G` (KT: "a triangle is a `0`-dof-graph", `def((K₃)̃) = 0`).
Combined with `hnoRigid` it is the contradiction that rules out the mixed parallel pair. Phrasing
`htri` as the proper-rigid-subgraph existence isolates the deficiency computation `def((K₃)̃) = 0`
(not yet in tree, the sibling sub-leaf) from the bounded edge bookkeeping done here. -/
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

/-- **The triangle on a split vertex and its neighbours is a proper rigid subgraph** (KT
Lemma 6.7(ii), Katoh–Tanigawa 2011 p. 677; the `htri` brick `splitOff_simple_of_noRigid`
carries). Given the splitting data — the `va`-edge `eₐ`, the `vb`-edge `e_b`, and a real
`ab`-edge `f` (the parallel-pair obstruction the splitting-off must avoid) — the
vertex-induced triangle `H = G.induce {v, a, b}` is a *proper* rigid subgraph of `G`: it is
`0`-dof by `isKDof_zero_of_triangle` (`def((K₃)̃) = 0`, the `D ≥ 3` triangle tightness), and
it is *proper* because `|V(G)| ≥ 4` (the splitting branch never reaches the `|V| ≤ 3` base
case), so its three vertices are a strict subset of `V(G)`.

The edge-set computation `E(H) = {eₐ, e_b, f}` is where `G.Simple` enters: a fourth edge
inside `{v, a, b}` would be parallel to one of the three (its loopless ends are one of the
three vertex pairs), contradicting `G.Simple`. This isolates the `def((K₃)̃) = 0` deficiency
count (`isKDof_zero_of_triangle`) from the bounded edge/vertex bookkeeping done here. -/
lemma triangle_isProperRigidSubgraph [Finite α] {G : Graph α β} [G.Simple] {v a b : α}
    {eₐ e_b f : β} {n : ℕ} (hD : 3 ≤ bodyBarDim n) (hG_ea : G.IsLink eₐ v a)
    (hG_eb : G.IsLink e_b v b) (hf : G.IsLink f a b) (hab : a ≠ b)
    (hcard : 4 ≤ V(G).ncard) :
    ∃ H : Graph α β, H.IsProperRigidSubgraph G n := by
  have hva : v ≠ a := hG_ea.ne
  have hvb : v ≠ b := hG_eb.ne
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

/-- **The splitting-off `G_v^{ab}` is simple** (KT Lemma 6.7(ii), Katoh–Tanigawa 2011
p. 677), with the triangle-rigidity brick `htri` discharged: this is the fully
hypothesis-free form of `splitOff_simple_of_noRigid`, supplying its `htri` from
`triangle_isProperRigidSubgraph` (the proper rigid triangle `G[{v, a, b}]` an `ab`-edge
would create) and `hnoRigid`. The proper-ness guard `4 ≤ |V(G)|` is the splitting branch's
standing hypothesis (KT §6.4 only splits when the base case `|V| ≤ 3` is not reached). -/
lemma splitOff_simple_of_noRigid_of_card [Finite α] {G : Graph α β} {v a b : α}
    {eₐ e_b e₀ : β} {n : ℕ} [G.Simple] (hD : 3 ≤ bodyBarDim n) (heab : eₐ ≠ e_b)
    (hG_ea : G.IsLink eₐ v a) (hG_eb : G.IsLink e_b v b) (hcard : 4 ≤ V(G).ncard)
    (hnoRigid : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) :
    (G.splitOff v a b e₀).Simple := by
  have hab : a ≠ b := fun h ↦ heab (Simple.eq_of_isLink hG_ea (h ▸ hG_eb))
  exact splitOff_simple_of_noRigid heab hG_ea hG_eb hnoRigid
    fun f hf ↦ triangle_isProperRigidSubgraph hD hG_ea hG_eb hf hab hcard

/-- **The `|V|=3` triangle base — vertex and edge pin** (KT §6.4 §1.48(1), Katoh–Tanigawa 2011
p. 659). Given a minimal `n`-dof-0 graph `G` on exactly three vertices, with two edges `eₐ : v–a`
and `e_b : v–b` and `eₐ ≠ e_b`, the third vertex pair `a–b` is distinct (`a ≠ b`) and `G` has an
edge `f` linking them.

**Proof.** (1) `a ≠ b`: if `a = b` then `eₐ` and `e_b` are parallel, contradicting `G.Simple`.
(2) Vertex pin: `{v,a,b} ⊆ V(G)` from the `IsLink` hypotheses; `|{v,a,b}| = 3 = |V(G)|` gives
`V(G) = {v,a,b}`. (3) Third edge: the rank formula `rank(G̃) = D·(|V|−1) = 2D` and the rank bound
`rank(G̃) ≤ (D−1)·|E|` force `|E| ≥ 3`, so some third edge `f ∉ {eₐ, e_b}` exists. Its endpoints
are in `{v,a,b}` (same vertex set); the Simple hypothesis and `unique_edge` eliminate all cases
except `f : a–b`. -/
theorem exists_isLink_of_isMinimalKDof_card_three [DecidableEq β] [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} [G.Simple]
    (hD : 3 ≤ bodyBarDim n) (hG : G.IsMinimalKDof n 0)
    (hcard : V(G).ncard = 3)
    {v a b : α} {eₐ e_b : β}
    (hG_ea : G.IsLink eₐ v a) (hG_eb : G.IsLink e_b v b)
    (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b) :
    a ≠ b ∧ V(G) = {v, a, b} ∧ ∃ f, G.IsLink f a b := by
  have hva : v ≠ a := hav.symm
  have hvb : v ≠ b := hbv.symm
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
    have hpair : E(G) ⊆ {eₐ, e_b} := Set.diff_eq_empty.mp h
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

/-- **G4c-i: IsLink correspondence under the `ρ = (a v)` relabel** (the graph-side half of the
`d = 3` Case-III `ρ`-relabel transport; KT 2011 eq. (6.31), p. 686). Given the chain data
`G.IsLink eₐ v a`, `G.IsLink e_b v b`, `G.IsLink e_c a c` with degree-2 closures at `v` and `a`,
and fresh edges `e₀ ∉ E(G)`, `e₁ ∉ E(G)`, `e₁ ≠ e₀`, the two splitting-offs are related by:

  `(G.splitOff a v c e₁).IsLink e x y ↔ (G.splitOff v a b e₀).IsLink (σ e) (ρ x) (ρ y)`

where `ρ = Equiv.swap a v` (vertex transposition) and `σ = Equiv.swap e_b e₀ * Equiv.swap e₁ e_c`
(edge permutation). The bijection maps:
* `e_b ↦ e₀` (the surviving `v`-`b` edge becomes the fresh `a`-`b` edge), carrying `vb ↦ ab`;
* `e₁ ↦ e_c` (the fresh `v`-`c` edge becomes the surviving `a`-`c` edge), carrying `vc ↦ ac`;
* all other edges are fixed (including `eₐ`, which is absent from both graphs as each
  deletes one of its endpoints).

The proof works by expanding `splitOff_isLink` on both sides and exhaustively matching the cases
using the degree-2 closures (only `eₐ, e_b` incident to `v`; only `eₐ, e_c` incident to `a`)
to show that surviving edges not equal to `e_b` have both endpoints away from both `a` and `v`,
so `σ` and `ρ` fix them. -/
lemma splitOff_isLink_relabel [DecidableEq α] [DecidableEq β] {G : Graph α β}
    {v a b c : α} {eₐ e_b e_c e₀ e₁ : β}
    (hG_ea : G.IsLink eₐ v a) (hG_eb : G.IsLink e_b v b) (hG_ec : G.IsLink e_c a c)
    (hav : a ≠ v) (hbv : b ≠ v) (hcv : c ≠ v) (hca : c ≠ a)
    (heab : eₐ ≠ e_b) (heac : eₐ ≠ e_c)
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

/-- **Commuting square: induce then split off = split off then induce** (used by
`lem:reduction-step-pos`, KT 4.8(ii)). Given a vertex `v ∉ S` with neighbours `a, b ∈ S ∩ V(G)`
and a fresh edge `e₀ ∉ E(G)`, splitting off `v` from the `v`-augmented induced subgraph
`G.induce (insert v S)` produces the same graph as splitting off `v` from `G` and then
inducing on `S`:

  `(G.induce (insert v S)).splitOff v a b e₀ = (G.splitOff v a b e₀).induce S`

The vertex sets agree: both equal `S` (the LHS deletes `v` from `insert v S`). The link
relations agree: in the surviving case `e ≠ e₀`, the `insert v S` membership with `x,y ≠ v`
reduces to `x, y ∈ S`; in the fresh-edge case `e = e₀`, the LHS uses `a, b ∈ insert v S`
while the RHS requires `a, b ∈ V(G)`, so `haV`/`hbV` are needed as hypotheses. -/
lemma induce_insert_splitOff {G : Graph α β} {v a b : α} {e₀ : β} {S : Set α}
    (hvS : v ∉ S) (haS : a ∈ S) (hbS : b ∈ S)
    (haV : a ∈ V(G)) (hbV : b ∈ V(G)) (he₀ : e₀ ∉ E(G)) :
    (G.induce (insert v S)).splitOff v a b e₀ = (G.splitOff v a b e₀).induce S := by
  have hav : a ≠ v := fun h => hvS (h ▸ haS)
  have hbv : b ≠ v := fun h => hvS (h ▸ hbS)
  refine Graph.ext ?_ (fun e x y => ?_)
  · -- Vertex sets: both are `S`.
    simp only [vertexSet_splitOff]
    ext x
    simp only [Set.mem_diff, Set.mem_singleton_iff]
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

end Graph
