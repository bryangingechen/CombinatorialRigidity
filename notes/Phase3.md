# Phase 3 — Henneberg moves (work log)

**Status:** in progress.

This file is the per-phase work record. See `../ROADMAP.md` for the
high-level plan and `../DESIGN.md` for cross-cutting design choices.

## Current state

The foundational layer is in place. `typeI` and `typeII` are defined on
`Option V`, with all eight adjacency lemmas as `Iff.rfl`.
`typeI_edgeSet` and `typeII_edgeSet` give the explicit set
decompositions; `typeI_edgeSet_ncard` and `typeII_edgeSet_ncard` give
the corresponding cardinality formulas.

The "Sym2 case analysis" friction logged after the previous session has
been resolved upstream-style: the missing lemma was a predicate-form
`Sym2.exists_and_map_eq_mk_iff`, which is what `simp` reaches after
`Set.mem_image` fires (and after `Set.mem_diff` if the underlying set
is a difference). With that lemma tagged `@[simp]` (mirrored under
`Mathlib/Data/Sym/Sym2.lean`), both `edgeSet` decompositions close in
three lines. See `../notes/FRICTION.md` (resolved entry).

**Next concrete task** (one sentence): prove `typeI_isLaman` —
tightness follows from `typeI_edgeSet_ncard` and `Nat.card_option`;
sparsity needs an `edgesIn` bound plus a case split on `none ∈ s` and
`s'.card = 0/1/≥2` sub-cases. Then the analogous `typeII_isLaman`.

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

### typeII API
- [x] Adjacency lemmas (4, all `Iff.rfl`).
- [x] `typeII_edgeSet` — parallel decomposition with the
  `\ {s(a, b)}` deletion and three new edges, closed by the same
  3-line template as `typeI_edgeSet` once
  `Sym2.exists_and_map_eq_mk_iff` (mirror) is available.
- [x] `typeII_edgeSet_ncard` — under `a ≠ b`, `c ≠ a`, `c ≠ b`,
  `((typeII G a b c).edgeSet).ncard = (G.edgeSet \ {s(a, b)}).ncard + 3`.
  Stated over the deletion-set so the lemma does not require
  `G.Adj a b`; consumers wanting the `+ 2` form (over `G.edgeSet`)
  specialize via `Set.ncard_diff_singleton_add_one` under
  `s(a, b) ∈ G.edgeSet`.

### Phase 1 carryover
- [x] `edgesIn_singleton` (in `EdgesIn.lean`) — `G.edgesIn {v} = ∅`,
  needed for the `s'.card = 1` case of `typeI_isLaman` sparsity.

### Deferred to next session
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
  with `Sym2.map some e' = s(x, y)` originally required `Sym2.eq_iff`
  plus `Option.some.injEq` and `Sym2.map_mk` — a fixed but workable
  idiom. The follow-on session resolved this by adding the
  predicate-form simp lemma `Sym2.exists_and_map_eq_mk_iff` to the
  mirror, after which both `edgeSet` decompositions close in three
  lines. See FRICTION.md (resolved entry).

## Blockers / open questions

- None blocking next session. The deferred items are well-specified.

## Hand-off / next phase

(Will be written when Phase 3 finishes.)

For the next agent picking this up: start with `typeI_isLaman`.
Tightness is `typeI_edgeSet_ncard` + `Nat.card_option`; sparsity needs
the `edgesIn` bound (a new lemma `typeI_edgesIn_ncard_le`) plus a case
split on `none ∈ s` and `s'.card = 0/1/≥2`. The foundation (definitions,
`edgeSet` decompositions, cardinality formulas, Sym2 helper API) has
been validated; further work should not need to revisit the type-bumping
or `Reachable` decisions, and the Sym2 friction has been resolved
upstream-style — see FRICTION.md.
