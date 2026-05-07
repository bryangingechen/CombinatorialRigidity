# Phase 3 — Henneberg moves (work log)

**Status:** in progress.

This file is the per-phase work record. See `../ROADMAP.md` for the
high-level plan and `../DESIGN.md` for cross-cutting design choices.

## Current state

The foundational layer is in place: `typeI` and `typeII` are defined on
`Option V`, with all eight adjacency lemmas as `Iff.rfl`. `typeI_edgeSet`
gives the explicit set decomposition, and `typeI_edgeSet_ncard` proves
the `+2` cardinality bump under `a ≠ b`.

The session validated the architectural choices (`Option V` for
type-bumping; structural `Adj` definition for free `Iff.rfl` adjacency
lemmas; no `Reachable` inductive). The cost is non-trivial Sym2
manipulation when working with `(typeI G a b).edgeSet` — see
`../notes/FRICTION.md` "Sym2 case analysis".

**Next concrete task** (one sentence): prove `typeII_edgeSet` (the
parallel decomposition with the `\ {s(a, b)}` deletion and three new
edges), then `typeI_isLaman` via tightness from `typeI_edgeSet_ncard`
plus the `edgesIn` decomposition.

## Architectural choices made up front

These diverge from the ROADMAP's original wording. Both are recorded in
`../DESIGN.md` "Choices to revisit"; if either turns out wrong, revisit
there.

- **Type-bumping via `Option V`.** The fresh vertex is `none`; old
  vertices embed via `some`. Validated by `typeI`'s clean structural
  Adj definition and the working edgeSet decomposition. The cost
  surfaced is Sym2 case analysis when relating `Sym2.map some` images
  to concrete `s(none, _)` patterns; this is workable but verbose.
- **No `Reachable` inductive.** Henneberg's theorem will be expressed
  via a structural decomposition lemma plus strong induction on
  `Fintype.card V`. Phase 3 builds the preservation half; Phase 5 will
  use the decomposition and induction directly.
- **Structural `Adj` definition (not lattice).** `typeI` and `typeII`
  use a `match`-based `Adj` (e.g. `| some u, some v => G.Adj u v | …`)
  rather than `G.map .some ⊔ fromEdgeSet …`. This makes all eight
  adjacency lemmas `Iff.rfl` and avoids existential elimination
  (`(G.map f).Adj` unfolds to `∃ u' v', …`) in every adjacency proof.
  Cost: edgeSet decomposition needs explicit Sym2 case analysis rather
  than coming free from `edgeSet_sup`/`edgeSet_map`. The earlier
  lattice attempt is documented in commit history.

## Lemma checklist

### Definitions (this session)
- [x] `Henneberg.typeI G a b : SimpleGraph (Option V)`.
- [x] `Henneberg.typeII G a b c : SimpleGraph (Option V)`.

### typeI API (this session)
- [x] `typeI_adj_some_some`, `typeI_adj_some_none`,
  `typeI_adj_none_some`, `typeI_not_adj_none_none` — all `Iff.rfl`.
- [x] `typeI_edgeSet` — `(Sym2.map some '' G.edgeSet) ∪ {s(none, some a), s(none, some b)}`.
- [x] `typeI_edgeSet_ncard` — under `a ≠ b`, `((typeI G a b).edgeSet).ncard = G.edgeSet.ncard + 2`.

### typeII API (this session — partial)
- [x] Adjacency lemmas (4, all `Iff.rfl`).
- [ ] `typeII_edgeSet` — parallel decomposition; deferred to next session.
- [ ] `typeII_edgeSet_ncard` — depends on `typeII_edgeSet`.

### Phase 1 carryover (this session)
- [x] `edgesIn_singleton` (in `EdgesIn.lean`) — `G.edgesIn {v} = ∅`,
  needed for the `s'.card = 1` case of `typeI_isLaman` sparsity.

### Deferred to next session
- [ ] `typeII_edgeSet` — the `\ {s(a,b)}` deletion and 3 new edges add
  one extra layer of `\` / `≠` bookkeeping over `typeI_edgeSet`. The
  structure is parallel; an earlier in-session attempt got stuck on
  `tauto` and `revert`-ordering details (see `../notes/FRICTION.md`).
- [ ] `typeI_edgesIn_ncard_le` — bound
  `((typeI G a b).edgesIn ↑s).ncard ≤ (G.edgesIn ↑s').ncard + 2`
  (where `s' = s.preimage some _`); requires extending the
  `typeI_edgeSet` decomposition through `∩ ↑s.sym2`.
- [ ] `typeI_isLaman` — Type I preserves Laman. Tightness follows
  immediately from `typeI_edgeSet_ncard` and `Nat.card_option`. Sparsity
  needs the `edgesIn` bound plus a case split on `none ∈ s` and the
  `s'.card = 0/1/≥2` sub-cases (the singleton case uses `edgesIn_singleton`).
- [ ] `typeII_isLaman` — analogous, more delicate due to deletion.
- [ ] `IsLaman.exists_typeI_or_typeII_reverse` — the structural
  decomposition theorem (per the new architecture; replaces the original
  ROADMAP `Reachable` plan).
- [ ] `top_fin_four_minus_edge_isLaman` — `K₄ \ e` example, one-line
  corollary of `typeI_isLaman` applied twice from `K₂`.

## Decisions made during this phase

(Phase-local trade-offs; cross-cutting ones go in `../DESIGN.md`.)

- **Use the structural `match`-based `Adj` for `typeI`/`typeII`.** First
  attempted the lattice form `G.map .some ⊔ fromEdgeSet …` to inherit
  `edgeSet_sup`/`edgeSet_map` for free, but the resulting adjacency
  proofs needed manual existential elimination on `(G.map f).Adj`'s
  unfolding `∃ u' v', G.Adj u' v' ∧ f u' = u ∧ f v' = v`, which simp
  did not fully discharge. Reverted to the structural form: adjacency
  lemmas become `Iff.rfl`, edgeSet decomposition becomes a one-time
  manual proof.
- **`Sym2.eq_iff` for edgeSet equalities, not the lattice.** Working
  with `Sym2.map some e' = s(x, y)` requires `Sym2.eq_iff` plus
  `Option.some.injEq` and `Sym2.map_mk` — a fixed but workable idiom.
  See FRICTION.md "Sym2 case analysis".

## Blockers / open questions

- None blocking next session. The deferred items are well-specified.

## Hand-off / next phase

(Will be written when Phase 3 finishes.)

For the next agent picking this up: start with `typeII_edgeSet`,
copying the structure of `typeI_edgeSet` and threading the
`s(p, q) ∉ {s(a, b)}` hypothesis through. Then `typeI_isLaman`. The
foundation has been validated; further work should not need to revisit
the type-bumping or `Reachable` decisions.
