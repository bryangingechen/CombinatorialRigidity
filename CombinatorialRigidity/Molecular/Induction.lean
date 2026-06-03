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

end Graph
