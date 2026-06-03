/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Deficiency

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
  rw [mulTilde, edgeMultiply_edgeSet, Set.mem_setOf_eq]
  rw [edgeFiber, Set.mem_setOf_eq] at hp
  rw [hp, edgeSet_splitOff]
  exact Or.inl ⟨rfl, ha, hb, haV, hbV⟩

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
      rwa [mulTilde, edgeMultiply_edgeSet, Set.mem_setOf_eq] at hmem
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
`v`-traversing path of `G̃`, via the `Matroid/Graph/AcyclicSet.lean` cycle
characterization) remains the residual crux of the still-red `lem:forest-surgery-split`. -/

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
  simp only [Set.mem_inter_iff, mem_fiberAtVertex, mulTilde, edgeMultiply_edgeSet,
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

end Graph
