# Phase 2 — Laman graphs (work log)

**Status:** ✓ Complete (part of the Phases 1–6 Laman arc; Phases 1–16 are complete and
`sorry`-free). Archived work log.

This file is the per-phase work record. See `../ROADMAP.md` for the
high-level plan and `../DESIGN.md` for cross-cutting design choices.

## Current state

Phase 1 (sparsity API) closed. Phase 2 has built out the Laman-specific
lemma library: the `iff` unfolding, the K₂ base case (named theorem),
the minimum-degree-2 result, and the existence of a degree-≤-3 vertex
(plus the combined "∃ v, 2 ≤ deg v ≤ 3" for `n ≥ 3`). The K₄ \ e
example is deferred — see "Decisions" below.

## Lemma checklist

Tracking against the ROADMAP Phase 2 bullets.

- [x] `isLaman_iff` — `G.IsLaman ↔ G.IsSparse 2 3 ∧ G.edgeSet.ncard + 3 = 2 * Nat.card V`.
  Definitionally `Iff.rfl`; named for discoverability.
- [x] `top_fin_two_isLaman` — `K₂` is Laman. Named (was an `example`).
- [x] `IsLaman.two_le_degree` — every vertex of a Laman graph on
  `n ≥ 3` vertices has degree at least 2.
- [x] `IsLaman.exists_degree_le_three` — every Laman graph contains a
  vertex of degree ≤ 3.
- [x] `IsLaman.exists_two_le_degree_le_three` — combined: a vertex of
  degree exactly 2 or 3 exists when `n ≥ 3`. This is the inductive
  step underlying Henneberg.
- [ ] `topMinusEdge_fin_four_isLaman` — `K₄ \ e` is Laman. **Deferred to
  Phase 3.**

## Decisions made during this phase

- **Defer `K₄ \ e` to Phase 3.** The proof requires a finite case
  analysis on subsets of `Fin 4` (or a helper lemma bounding
  `(G.edgesIn ↑s).ncard ≤ s.card.choose 2` via the inclusion into the
  complete graph). Both are tractable but tedious. Once Phase 3 has
  `Henneberg.typeI` and the "Type I preserves Laman" lemma, `K₄ \ e`
  is a one-line corollary: it equals `K₂` extended by two Type I
  moves. This deferral is recorded here rather than dropped from the
  roadmap.
- **`IsLaman.two_le_degree` requires `n ≥ 3`, not `n ≥ 2`.** The
  ROADMAP bullet originally said `n ≥ 2`, but `K₂` (the only Laman
  graph on 2 vertices) has both vertices of degree 1, so the result
  would be false. The sparsity precondition `3 ≤ 2 * (n − 1)` forces
  `n ≥ 3` anyway. ROADMAP patched in the close-out commit.
- **Drop unused `[DecidableEq V]` typeclass hypothesis.** The
  unused-decidable-in-type linter flags `[DecidableEq V]` arguments
  that don't appear in the lemma statement. Standard fix:
  use `classical` inside the proof. Same convention as Phase 1.
- **Use `push Not` instead of `push_neg`.** `push_neg` is now
  deprecated in favour of `push Not`. We followed the deprecation.

## Blockers / open questions

- None currently. The deferred `K₄ \ e` example is intentional, not
  blocked.

## Hand-off / next phase

Phase 3 (Henneberg moves) starts from:
- `IsLaman.exists_two_le_degree_le_three` is the inductive lever:
  pick a vertex of degree 2 or 3 and reverse the appropriate Henneberg
  move.
- `top_fin_two_isLaman` is the base case.
- `K₄ \ e` deferred — prove as a corollary of "Type I preserves Laman"
  in Phase 3.
