# Phase 3 — Henneberg moves (work log)

**Status:** in progress.

This file is the per-phase work record. See `../ROADMAP.md` for the
high-level plan and `../DESIGN.md` for cross-cutting design choices.

## Current state

Both Henneberg moves now provably preserve the Laman property:
`typeI_isLaman` (under `a ≠ b`) and `typeII_isLaman` (under `a ≠ b`,
`c ≠ a`, `c ≠ b`, and `G.Adj a b`). Tightness in each case is a few
lines combining the edge-count formula with `Finite.card_option`;
sparsity is a `Finset.preimage some`-driven case-split on `none ∈ s`
and on `s'.card = 0 / 1 / ≥ 2`. See the file for proof structure.

The hand-rolled `edgesIn` decompositions inside each `_isLaman` proof
(`(typeI G a b).edgesIn ↑s = Sym2.map some '' G.edgesIn ↑s' ∪ T`, and
the `typeII` analogue with `\ {s(a, b)}` and a 3-element `T'`) are
the workhorse: cardinality is then split as image-card plus `T.ncard`,
with `T.ncard ≤ 2` (resp. `≤ 3`) and a tighter `≤ 1` sub-bound when
`s' = {w}` is a singleton.

**Next concrete task** (one sentence): prove
`top_fin_four_minus_edge_isLaman` — `K₄ \ e` is Laman — as a one-line
corollary of `typeI_isLaman` applied twice from `K₂` (a quick warm-up
example before the decomposition theorem). Then take on
`IsLaman.exists_typeI_or_typeII_reverse`.

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

### Preservation theorems (this session)
- [x] `typeI_isLaman` — Type I preserves Laman, under `a ≠ b`.
  Sparsity is by case split on `none ∈ s` and on `s'.card`; the
  `s'.card = 1, none ∈ s` sub-case requires showing `T ⊆ {s(none, some w)}`
  (where `s' = {w}`) since the trivial `T.ncard ≤ 2` bound is too loose.
- [x] `typeII_isLaman` — Type II preserves Laman, under `a ≠ b`,
  `c ≠ a`, `c ≠ b`, and `G.Adj a b`. Mirrors `typeI_isLaman` with two
  extra wrinkles: (i) the deleted edge `s(a, b)` interacts with the
  three new edges via a uniform `+ 2` bound — either `s(a, b)` was in
  `G.edgesIn ↑s'` (loses 1, T'.ncard ≤ 3) or it wasn't (T'.ncard ≤ 2,
  because `a ∉ s' ∨ b ∉ s'`); (ii) the inline `edgesIn` decomposition
  needs a final `try tauto` to clean up conjunct re-grouping that
  `simp` leaves for the `s(some u, some v)` case.

  Note: `typeI_edgesIn_ncard_le` did not need to be factored as a
  named lemma; the bound is inlined inside the `none ∈ s` branch of
  `typeI_isLaman`. If a third caller materializes (e.g. for the
  decomposition theorem), promote it then.

  Both proofs use `[Finite V]` plus `have : Fintype V := Fintype.ofFinite V`
  so callers don't have to manage a `Fintype` instance.

### Deferred to next session
- [ ] `top_fin_four_minus_edge_isLaman` — `K₄ \ e` example, expected
  to be a one-/two-line corollary of `typeI_isLaman` applied twice from
  `K₂` (modulo the `Option (Option (Fin 2)) ≃ Fin 4` isomorphism). Good
  warm-up before the decomposition theorem.
- [ ] `IsLaman.exists_typeI_or_typeII_reverse` — the structural
  decomposition theorem (per the new architecture; replaces the original
  ROADMAP `Reachable` plan). The hard remaining Phase 3 task. Plan: use
  `IsLaman.exists_two_le_degree_le_three` to find a degree-2 or
  degree-3 vertex `v`, then case-split on its degree to produce the
  Type I or Type II reverse move.

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

- **Inline the `edgesIn` decomposition in each `_isLaman` proof,
  don't factor it.** The `(typeI G a b).edgesIn ↑s = … ∪ T` equality
  is shaped slightly differently per move (T is 2-element for typeI,
  3-element for typeII; typeII also carries the `\ {s(a, b)}` on the
  image side). Factoring out a generic `_edgesIn_decomp` lemma would
  not be reused enough to pay for itself, and would force consumers
  to also reason about the `Finset.preimage some _` -- which is more
  natural to set up in-context.

- **`s'.card = 1` sub-case needs explicit subset reasoning.** The
  uniform bound `T.ncard ≤ 2` (resp. `T'.ncard ≤ 3`) is one too loose
  here: when `s' = {w}` and `none ∈ s` we need `T.ncard ≤ 1`. Solved by
  showing `T ⊆ {s(none, some w)}`: each `e ∈ T` is `s(none, some v)`
  with `some v ∈ s`, so `v ∈ s' = {w}`, so `v = w`. Same shape for
  both `typeI` and `typeII`.

- **`tauto` cleanup for `typeII` `edgesIn` decomposition.** The simp
  normal form of `(typeII G a b c).Adj (some u) (some v)` after
  unfolding leaves `(G.Adj u v ∧ p) ∧ q` while the RHS produces
  `(G.Adj u v ∧ q) ∧ p` for the same conjuncts; `simp` does not
  re-associate, so a closing `try tauto` is needed. The matching
  `typeI` proof closes with bare `simp` because the `Adj` predicate
  there has no extra clause. Logged in FRICTION.md.

- **Post-landing refactor: extract `Set.ncard_pair_le` / `_triple_le`
  and `Sym2.map_some_injective` to mirrors.** Five literal-pair /
  triple ncard bounds in this file expanded to 3- and 5-line calc
  chains via `Set.ncard_insert_le` + `Set.ncard_singleton`; the
  `Sym2.map some` injectivity argument was written out as
  `Sym2.map.injective (Option.some_injective V)` four times. Both
  patterns now read as one-token applications of named mirror
  lemmas. See FRICTION.md (resolved entries).

- **Don't hand-pass `Set.Finite` witnesses.** The `_fin` preambles
  in front of every `Set.ncard_*` call were unnecessary: the
  relevant lemmas (`ncard_union_eq`, `ncard_le_ncard`,
  `ncard_eq_zero`, `ncard_pos`, …) all take `(hs : s.Finite := by
  toFinite_tac)`, which finds the witness via `Set.toFinite` from
  the ambient `[Finite V]`. The two `edgeSet_ncard` lemmas dropped
  ~9 and ~10 lines of preamble respectively, and the inline
  `_isLaman` proofs lost three more `_fin` haves each. The one
  trap: when chaining `.mpr` on an iff lemma (`Set.ncard_pos.mpr`),
  the autoparam can't fire — pass the witness manually there or use
  `ncard_ne_zero_of_mem` (which is single-argument). Lifted from
  FRICTION.md into TACTICS.md § 2 as a project-wide rule.

- **Grind closes the tightness branches; arithmetic-heavy `omega`s
  stay.** Per TACTICS.md § 1, ran `grind?` on each closing tactic.
  Both `_isLaman` tightness branches collapsed: `typeI_isLaman` from
  4 lines to 1 (`grind only [!typeI_edgeSet_ncard,
  !Finite.card_option, h.edgeSet_ncard]`), `typeII_isLaman` from 7
  to 3 (grind even pulls in `Set.ncard_ne_zero_of_mem` from a local
  edge-membership hypothesis on its own). The pure-arithmetic
  `omega`s in the sparsity branches stayed: each closes a chain of
  staged `have`s with no equational reasoning to do, the canonical
  `omega` use case. Disjointness proofs also stayed — `grind` cannot
  case-split on Sym2 patterns. Worked examples and the don't-bother
  list are now in TACTICS.md § 1.

## Blockers / open questions

- None blocking next session. Both deferred items (K₄\e and the
  decomposition theorem) are well-specified.

## Hand-off / next phase

(Will be written when Phase 3 finishes.)

For the next agent picking this up: start with
`top_fin_four_minus_edge_isLaman` — it should be a short corollary of
`typeI_isLaman` applied twice from `top_fin_two_isLaman`, mediated by
the `Option (Option (Fin 2)) ≃ Fin 4` isomorphism (and `IsLaman` is
preserved under graph isomorphism — if that lemma doesn't exist yet,
add it to `Laman.lean`). Then move to the decomposition theorem
`IsLaman.exists_typeI_or_typeII_reverse`; the Phase 2 lemma
`IsLaman.exists_two_le_degree_le_three` provides the entry point.
