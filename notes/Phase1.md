# Phase 1 — Sparsity (work log)

**Status:** complete.

This file is the per-phase work record. See `../ROADMAP.md` for the
high-level plan and `../DESIGN.md` for cross-cutting design choices.
Phase notes are *historical*: don't rewrite them when a phase ends —
they're the reference for "how Phase N actually went."

## Lemma checklist

Tracking against the original ROADMAP bullets, plus what we added.

### Definitions (`EdgesIn.lean`, `Sparsity.lean`, `Laman.lean`)

- [x] `SimpleGraph.edgesIn G s` — edges with both endpoints in `s`
- [x] `SimpleGraph.IsSparse G k ℓ`
- [x] `SimpleGraph.IsTight G k ℓ`
- [x] `SimpleGraph.IsLaman G` (= `IsTight 2 3`)

### `edgesIn` API (`EdgesIn.lean`)

- [x] `mem_edgesIn` — membership unfolding
- [x] `edgesIn_subset_edgeSet`
- [x] `edgesIn_mono` — monotone in vertex set
- [x] `edgesIn_univ`, `edgesIn_empty`, `edgesIn_bot`
- [x] `edgesIn_finite` — finiteness over a finite vertex set
- [x] `mem_edgesIn_compl_singleton` — `e ∈ edgesIn {v}ᶜ ↔ e ∈ edgeSet ∧ v ∉ e`
- [x] `edgesIn_compl_singleton` — `edgesIn {v}ᶜ = edgeSet \ incidenceSet v`

The last two were not in the original ROADMAP but added as the natural
finishers of the `edgesIn` API. They directly enable the vertex-deletion
edge-count argument that Phase 2 (degree results) needs.

### Sparsity / tightness API (`Sparsity.lean`)

- [x] `bot_isSparse` — empty graph is sparse for any `(k, ℓ)`
- [x] `IsSparse.mono_left` — subgraph of a sparse graph is sparse
- [x] `IsTight.isSparse`, `IsTight.edgeSet_ncard` — accessors
- [x] `bot_isTight_iff` — empty graph is tight iff `ℓ = k * #V`
- [x] `IsSparse.edgeSet_ncard_add_le` — global edge bound
  (`#E + ℓ ≤ k * #V`) when `ℓ ≤ k * #V`
- [x] `IsSparse.deleteEdges` — sparsity preserved under edge deletion
- [x] `IsTight.not_isSparse_of_lt` — proper supergraph of a tight graph
  is not sparse

### Laman (`Laman.lean`)

- [x] `IsLaman.isSparse`, `IsLaman.edgeSet_ncard` — accessors
- [x] Worked example: `(⊤ : SimpleGraph (Fin 2)).IsLaman`

### ROADMAP item subsumed by general lemma

The ROADMAP listed: *"For Laman's purposes: a `(2, 3)`-sparse graph has
at most `2 * #V − 3` edges when `#V ≥ 2`."*

We did **not** introduce a separate named lemma for this. It is one
application of `IsSparse.edgeSet_ncard_add_le` with `k = 2`, `ℓ = 3`:
the precondition `3 ≤ 2 * Nat.card V` is equivalent to `2 ≤ Nat.card V`,
and the conclusion is `G.edgeSet.ncard + 3 ≤ 2 * Nat.card V`. Naming
the trivial alias didn't seem worth a public theorem — Phase 5 will
just instantiate the general lemma.

## Decisions made during Phase 1

These are *phase-local* trade-offs. Cross-cutting decisions live in
`DESIGN.md`.

- **`[Finite V]` over `[Fintype V]` in lemma signatures.** The linter
  flagged `[Fintype V]` in `IsTight.not_isSparse_of_lt` as not
  appearing in the type; we switched to `[Finite V]` everywhere and
  promote to `Fintype` internally with `Fintype.ofFinite V` only where
  needed. This keeps the API uniform and the linter quiet.
- **Vertex partition phrased via `{v}ᶜ`, not via `Set.univ \ {v}`.**
  The complement-of-singleton form is shorter and pairs cleanly with
  `Set.subset_compl_singleton_iff`. Both are equivalent;
  `Set.compl_eq_univ_diff` is one rewrite away if a use site needs
  the other form.
- **`grind only [...]` form for landed proofs.** Worked through one
  iteration cycle (write `grind?`, copy the suggestion). Documented
  in `TACTICS-GOLF.md` § 1.

## Hand-off / next phase

Phase 2 (Laman graphs) starts from:
- The vertex partition lemma `edgesIn_compl_singleton` is the keystone
  for proving the minimum-degree-2 result (a Laman graph on `n ≥ 2`
  vertices has every vertex of degree ≥ 2). The proof outline:
  1. If `v` had degree 0, `G.edgesIn {v}ᶜ` would equal `G.edgeSet`,
     and we could apply Laman tightness on `V \ {v}` to get a contradiction.
  2. If `v` had degree 1, `(G.edgesIn {v}ᶜ).ncard = G.edgeSet.ncard − 1`,
     and the same sparsity bound on `V \ {v}` gives a contradiction.
- The handshake lemma (sum of degrees = 2|E|) is in mathlib as
  `SimpleGraph.sum_degrees_eq_twice_card_edges`.

Open question for Phase 2: do we keep working with `Set.ncard` and
`(G.edgesIn ↑s).ncard`, or do we promote to `Finset` versions for the
degree counting? Probably stay on `ncard` for definitions, materialize
to `Finset` only inside specific proofs that need `Finset.sum`.
