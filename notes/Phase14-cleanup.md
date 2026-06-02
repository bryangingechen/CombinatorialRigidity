# Phase 14 cleanup round (work log)

**Status:** in progress.

Between-phases cleanup round, run after Phase 14 (k-frame matroid =
k-fold cycle-matroid union) closed in `b90516d` and before Phase 15
(body-bar Tay) opens. Round manual: `CLEANUP.md`. The per-commit
friction review (`CombinatorialRigidity/CLAUDE.md`) still fires on
every commit in this round.

## Current state

(A) blueprint↔Lean divergence audit complete (A1 + A2). One fixable
divergence cluster found and fixed: three reverse-section `KFrame.lean`
docstrings carried a wrong blueprint node-anchor (all three said
`(lem:k-frame-specialize-forest …)` — copy-paste from the
reverse-half session — where the blueprint pins them to
`lem:k-frame-specialize-li` / `lem:k-frame-forest-packing-of-sparse` /
`lem:k-frame-specialize-identity` respectively), plus three stale
"follow-up node" / "deferred" / "remaining Phase-14 target" asides
(the module docstring + two reverse-half docstrings) left over from
when the reverse half was being built incrementally. All `\lean{}`
pins resolve and every blueprint statement form matches its Lean
signature; the Rank.lean Phase-14 adders carry no blueprint node-anchor
(correctly unpinned). Build green + warning-clean + lint clean.

(B) code-smell sweep: B1 done (no-op confirm). The eight `DecidableEq α`
+ `DecidablePred (· ∈ E(G))` `letI`-pair sites all match the FRICTION
pin's accepted boundary and are each *forced*: four are `def` bodies
(`kFrameRow`, `blockPiSpan`, `blockPiSpanOn`, `kFrameRowR` — a `def`
body can't open with the `classical` tactic) and four are
**statement-level** `letI`s where the decidability instance is part of
the theorem's *type* (`finrank_span_signedIncMatrix_eq_cycleMatroid_rk`,
`specRow_linearIndependent`'s statement + its term-mode-proof mirror,
`forestEval_kFrameRowR_eq_single`) — the proof-body `classical` can't
reach the statement. A bundling helper is not viable: a function/abbrev
boundary cannot inject `letI` *instances* into the caller's elaboration
context (that is precisely what `letI` does and an abstraction destroys),
so the only mechanism would be a macro — heavy machinery that would hide
the genuinely-required instances for a 2-line save at 8 sites. No change.

(B3) `noncomputable def` forced-vs-accidental sweep done: seven of the
eight are forced (`kFrameIndet`/`kFrameRow` via the `FractionRing`-backed
`KFrameField`, `kFrameMatroid` via `Matroid.ofFun`, `blockPiSpan`/
`blockPiSpanOn` via `Submodule.span`, `kFrameRowR` via the
`Classical.decPred`-mediated `signedIncMatrix`, `forestEval` via
`MvPolynomial.eval` with `Classical.decPred`). **One accidental:**
`constPiSpanEquiv` — a `LinearEquiv` built from explicit `toFun`/`invFun`
+ `rfl` proofs over a generic `[Semiring R] [AddCommMonoid M] [Module R M]`,
with no `FractionRing` / `span` / `Classical` data, so it is genuinely
computable. Dropped its `noncomputable`. Build green + warning-clean +
lint clean.

(B2) `classical`-invocation sweep done: of the 14 (`KFrame.lean` 11 +
`Rank.lean` 3), 11 are load-bearing and forced (8 `KFrame.lean` def-unfold /
statement-`letI` boundary sites, 3 `Rank.lean` `[Finite]`→`Fintype` matrix
bridges — `[DecidableEq]` is not a cleaner boundary at any per `DESIGN.md`
*Typeclass shape*) and **3 were stray** (`kFrameRow_mem_blockPiSpan`,
`kFrameRow_mem_blockPiSpanOn`, `Matroid.Rep.finrank_span_image_eq_rk`):
dropped. Verified by strip-all build. Build green + warning-clean + lint clean.

(B4+B5) re-run on the two `Rank.lean` Phase-14 adders done: `change`/`show`,
`show … from rfl`, `@[nolint]`, `set_option linter.*` all clean (none); the
sole 3-arg `rw` (the rank-bridge in `exists_submatrix_det_ne_zero_…`) is a
one-off upstream-fact composition already named in its FRICTION resolution, not
a missing fused lemma. (B) complete; no-op confirm, doc-only commit.

(C) long-proof audit done (C1 + C2). C1 closed mostly no-op per
`CLEANUP.md` *Calibration*: all substantive pieces of
`linearIndepOn_kFrameRow_of_isSparse_restrict` (~95 LoC) are already
extracted into named lemmas (`specRow_linearIndependent`,
`forestEval_kFrameRowR_eq_single`, `exists_forestPacking_cover_…`,
`linearIndepOn_kFrameRow_iff_over_polyRing`, `kFrameRow_eq_map_kFrameRowR`,
the two `Rank.lean` engine lemmas); the body is forced wiring (disjoint
forest packing → reindex via `Set.unionEqSigmaOfDisjoint` → minor engine
→ injective `ψ`-transfer). No mathlib lemma missed (the `hentry_inj`
`ker = bot` route is idiomatic; no `LinearMap.compLeft_injective` exists
upstream). **One marginal tightening landed:** the 5-line `hFcover`
sub-block (an intermediate `have hsup` + `rw [hsup, hcover]`) folds into
a single `rw [← hcover, …]` chain over the `iSup`/`Finset.sup` bridge.
C2 (`forest_count_of_linearIndepOn_kFrameRow`, ~27 LoC) ruled out as a
cross-proof-unification partner — the forward half is a finrank-monotone
count (`finrank_span_set_eq_card` → `Submodule.finrank_mono` →
`finrank_blockPiSpanOn`), the reverse a specialization/minor argument;
opposite directions, no shared step-level backbone. Build green +
warning-clean + lint clean.

Next concrete step: (D) compress `notes/Phase14.md` (329 → under 250)
+ FRICTION re-skim.

## Scope

Single-phase surface, so all four categories are in scope but tightly
bounded:

- **(A) Blueprint ↔ Lean divergence** — `sec:body-bar-k-frame` in
  `body-bar.tex` (11 nodes) + the two Phase-14 mirror lemmas' upstream-
  candidate docstrings in `Rank.lean`. Phase 14 closed with the blueprint
  synced (`b90516d`), so expect mostly no-op, but the per-node signature
  compare is the audit gate.
- **(B) Code-smell sweep** — `KFrame.lean` + the Phase-14 `Rank.lean`
  adders. Greps already run at round open (see task list for findings).
- **(C) Long-proof audit** — the two long proofs in `KFrame.lean`
  surfaced by the LoC ranking.
- **(D) Project-organization compression** — `notes/Phase14.md` is 329
  lines, over the 250 soft budget for a phase of this commit count;
  compress now that the phase is closed. Re-skim `FRICTION.md` status
  sections for Phase-14 entries fully indexed elsewhere.

## Task list

### A. Blueprint ↔ Lean divergence audit

- [x] A1 — `sec:body-bar-k-frame` per-node `\lean{}` signature compare
  (12 nodes). All 23 `\lean{}` names resolve to `KFrame.lean` decls
  (one `_root_.Matroid.Rep.…`); every blueprint statement form matches
  its Lean signature. **Finding:** three reverse-section docstrings'
  `(lem:…)` node-anchor parentheticals were wrong (all read
  `lem:k-frame-specialize-forest`; correct anchors are
  `lem:k-frame-specialize-li` on `specRow_linearIndependent`,
  `lem:k-frame-forest-packing-of-sparse` on
  `exists_forestPacking_cover_of_isSparse_restrict`,
  `lem:k-frame-specialize-identity` on
  `forestEval_kFrameRowR_eq_single`). Fixed. Rank.lean Phase-14 adders
  are unpinned (correct — upstream-candidate infra, not blueprint
  nodes).
- [x] A2 — re-read each node's prose proof. No "the Lean does X via Y"
  smoothness gloss and no genuine formalization aside (the prose
  faithfully names the infra lemmas: `Pi.linearIndependent_single`,
  `LinearIndependent.iff_fractionRing`, the minor-nonvanishing engine).
  **Finding (staleness):** the module docstring + two reverse-half
  docstrings carried "follow-up node" / "is deferred" / "remaining
  Phase-14 target" asides from the incremental build; the reverse half
  and `thm:k-frame-union-cycle` are landed. Reworded to point at the
  landed `linearIndepOn_kFrameRow_of_isSparse_restrict` /
  `kFrameMatroid_eq_unionPow_cycleMatroid`. No Lean-simplification
  candidate surfaced.

### B. Code-smell sweep (greps run at round open)

- [x] B1 — repeated `letI : DecidableEq α := Classical.decEq α` +
  `letI : DecidablePred (· ∈ E(G)) := Classical.decPred _` pair
  (8 paired sites in `KFrame.lean`, + one single `letI` in `forestEval`).
  **No-op confirm.** FRICTION `[resolved]` *`Graph.orientation.signedIncMatrix`
  needs `[DecidableEq α]` + `[DecidablePred (· ∈ E(G))]` …* pins the
  term-level `letI` as the accepted boundary (keeps the def signatures
  binder-free). All eight sites match: four are `def` bodies (can't open
  with the `classical` tactic) and four are statement-level `letI`s (the
  instance is part of the theorem type, beyond the reach of a proof-body
  `classical`) — every site forced. A `letI`-bundling helper is **not
  viable**: an abstraction boundary cannot inject `letI` instances into
  the caller's elaboration context; only a macro could, which is not
  worth a 2-line save × 8 sites and would hide the required instances.
- [x] B2 — 14 `classical` invocations across `KFrame.lean` (11) +
  `Rank.lean` (3). At every load-bearing site `[DecidableEq …]` is **not**
  a cleaner boundary: the 8 surviving `KFrame.lean` sites are the def-unfold
  / statement-`letI` boundary already pinned by FRICTION (a `rw` of a
  `Classical.decEq`-carrying def, or an instance that is part of the theorem
  type), and the 3 `Rank.lean` sites are the `[Finite m]`→`Fintype`+
  `DecidableEq` matrix/determinant bridge (`DESIGN.md` *Typeclass shape*).
  **Finding (3 stray):** the `classical` opening `kFrameRow_mem_blockPiSpan`,
  `kFrameRow_mem_blockPiSpanOn`, and `Matroid.Rep.finrank_span_image_eq_rk`
  was dead — the first two `rw`-unfold defs that bake in their own
  `Classical` instances (so the rewritten goal already carries them) and the
  third uses no decidable operation at all. Dropped all three; verified
  load-bearing-ness of the remaining 11 by a strip-all-`classical` build
  (only those 3 proofs stayed error-free). Build green + warning-clean +
  lint clean.
- [x] B3 — 8 `noncomputable def` in `KFrame.lean`: 7 forced
  (`kFrameIndet`/`kFrameRow` via `FractionRing`, `kFrameMatroid` via
  `Matroid.ofFun`, `blockPiSpan`/`blockPiSpanOn` via `Submodule.span`,
  `kFrameRowR` via `signedIncMatrix`'s `Classical.decPred`, `forestEval`
  via `MvPolynomial.eval` + `Classical.decPred`). **1 accidental:**
  `constPiSpanEquiv` (explicit `toFun`/`invFun` `LinearEquiv` over generic
  `[Semiring R]`, no noncomputable data) — `noncomputable` dropped.
- [x] B4 — `change`/`show`, `show … from rfl`, and 3+-arg single-step
  `rw` chains came back **clean** on `KFrame.lean` at round open; re-run
  on the two `Rank.lean` Phase-14 adders
  (`linearIndependent_rows_of_specialized_submatrix_det_ne_zero`,
  `exists_submatrix_det_ne_zero_of_linearIndependent_rows`). `change`/`show`
  and `show … from rfl`: clean (none). **One 3-arg `rw`** in
  `exists_submatrix_det_ne_zero_…`:
  `rw [← Mᵀ.rank_eq_finrank_span_row, rank_transpose, h.rank_matrix]` — a
  one-off composition of three distinct upstream facts (rank=span-finrank /
  rank-transpose / LI-rows⟹rank=card), not a recurring glue-pattern. Already
  named in the mirror's FRICTION resolution body; no fused mirror lemma
  warranted. No-op confirm.
- [x] B5 — `@[nolint …]` / `set_option linter.*` came back **clean** on
  `KFrame.lean` at round open; re-run on the two `Rank.lean` adders —
  clean (none). No-op confirm.

### C. Long-proof audit

- [x] C1 — `linearIndepOn_kFrameRow_of_isSparse_restrict` (~95 lines, the
  reverse-half wiring). Four-question walk: API extraction — none (all
  substantive pieces already named lemmas); missed mathlib lemma — none
  (`hentry_inj`'s `ker = bot` route is idiomatic; no
  `LinearMap.compLeft_injective` upstream); tactic substitution — **one
  marginal tightening** (the 5-line `hFcover` sub-block folds to a single
  `rw [← hcover, …]` over the `iSup`/`Finset.sup` bridge), landed;
  cross-proof unification — see C2. Otherwise forced wiring per
  `CLEANUP.md` *Calibration*.
- [x] C2 — `forest_count_of_linearIndepOn_kFrameRow` (~27 lines, forward
  half). Below the §C 50-line threshold; cross-proof-unification spot-check
  vs. C1: **ruled out.** Forward is a finrank-monotone count
  (`finrank_span_set_eq_card` → `Submodule.finrank_mono` →
  `finrank_blockPiSpanOn`), reverse a specialization/minor argument;
  opposite directions, no shared step-level backbone.

### D. Project-organization compression

- [ ] D1 — compress `notes/Phase14.md` (329 lines → under the 250 soft
  budget): the *Current state* paragraph and the per-node *Lemma
  checklist* both narrate the full landed-node history that the closed
  phase no longer needs at that density; collapse to a commit-log pointer
  + brief summary per `CLEANUP.md` §D. Preserve *Decisions made* (the
  coefficient encoding + ground-set restriction are load-bearing for
  Phase 15) and the *Hand-off* section.
- [ ] D2 — re-skim `FRICTION.md` status sections: Phase-14 `[resolved]`
  entries whose resolution is fully indexed elsewhere migrate to
  `FRICTION-archive.md`; lift any cross-cutting lesson referenced by 2+
  phases.

## Decisions made during this round

### Cleanup pass summaries
- **C1+C2 (KFrame.lean, one marginal tightening).** Four-question
  long-proof audit on `linearIndepOn_kFrameRow_of_isSparse_restrict`
  (~95 LoC) + `forest_count_of_linearIndepOn_kFrameRow` (~27 LoC).
  C1 mostly no-op per `CLEANUP.md` *Calibration* — substantive pieces
  already extracted into named lemmas, body is forced wiring; no missed
  mathlib lemma (the `ker = bot` injectivity route is idiomatic). One
  tightening landed: the 5-line `hFcover` sub-block (`have hsup` +
  `rw [hsup, hcover]`) folds to a single `rw [← hcover, …]` chain over
  the `iSup`/`Finset.sup` bridge — same one mathematical step, two fewer
  lines. C2 cross-proof-unification with C1 ruled out (forward = finrank
  count, reverse = specialization/minor; opposite directions). Build
  green + warning-clean + lint clean; no FRICTION entry (the remaining
  6-arg `rw` is the one-off `iSup`↔`Finset.sup` bridge already pinned as
  non-recurring in B4).
- **B4+B5 (Rank.lean adders, doc-only no-op confirm).** Re-ran the
  `change`/`show`, `show … from rfl`, 3+-arg single-step `rw`,
  `@[nolint …]`, and `set_option linter.*` greps on the two Phase-14
  `Rank.lean` adders (`KFrame.lean` was confirmed clean at round open).
  All clean except one 3-arg `rw` (the rank-bridge in
  `exists_submatrix_det_ne_zero_of_linearIndependent_rows`) — a one-off
  composition of three distinct upstream facts, already named in that
  mirror's FRICTION resolution; not a missing fused lemma. No code change;
  build green + warning-clean + lint clean; no new FRICTION entry.
- **A1+A2 (KFrame.lean, doc-only).** Corrected three reverse-section
  docstring blueprint node-anchors (`lem:k-frame-specialize-li`,
  `lem:k-frame-forest-packing-of-sparse`, `lem:k-frame-specialize-identity`
  — all were `lem:k-frame-specialize-forest`). Reworded six stale
  incremental-build asides (module docstring "is deferred" / "remaining
  Phase-14 target"; two reverse-half "follow-up node" lines) to reflect
  the landed reverse half. No statement/proof changes; no FRICTION
  entry (pure divergence-audit doc fix). Blueprint TeX unchanged — the
  pins were already correct; the drift was Lean-side.
- **B3 (KFrame.lean, one-token fix).** `noncomputable def`
  forced-vs-accidental sweep: 7 of 8 forced (FractionRing-backed
  `kFrameIndet`/`kFrameRow`, `Matroid.ofFun` `kFrameMatroid`,
  `Submodule.span` `blockPiSpan`/`blockPiSpanOn`, `Classical.decPred`-
  mediated `kFrameRowR`/`forestEval`). One accidental — `constPiSpanEquiv`,
  an explicit-data `LinearEquiv` over a generic `[Semiring R]` with no
  noncomputable ingredient — dropped its `noncomputable`. Build green +
  warning-clean + lint clean; no FRICTION entry (pure code-smell fix the
  B-sweep is designed to catch).
- **B2 (KFrame.lean, dead-code fix).** `classical`-invocation sweep over
  all 14 sites (`KFrame.lean` 11 + `Rank.lean` 3). 11 load-bearing and
  forced — the 8 `KFrame.lean` sites are the def-unfold / statement-`letI`
  boundary (a `rw` of a `Classical.decEq`-carrying def, or an instance in
  the theorem type) and the 3 `Rank.lean` sites are the `[Finite]`→`Fintype`
  + `DecidableEq` matrix/determinant bridge; `[DecidableEq]` is not a cleaner
  signature boundary at any (`DESIGN.md` *Typeclass shape*). **3 stray**
  (`kFrameRow_mem_blockPiSpan`, `kFrameRow_mem_blockPiSpanOn`,
  `Matroid.Rep.finrank_span_image_eq_rk`) dropped: the first two `rw`-unfold
  defs that already carry their own `Classical` instances, the third uses no
  decidable op. Verified by a strip-all-`classical` build (only those 3
  proofs stayed error-free). Build green + warning-clean + lint clean; no
  FRICTION entry (pure code-smell fix the B-sweep is designed to catch, like
  B3; the one-off dead-`classical` lesson is below the 2+-file lift
  threshold).
- **B1 (KFrame.lean, no-op confirm).** The eight `DecidableEq α` +
  `DecidablePred (· ∈ E(G))` `letI`-pair sites (plus the single `letI`
  in `forestEval`) all match the FRICTION-pinned boundary and are each
  forced — four `def` bodies (no `classical` tactic available) and four
  statement-level `letI`s (instance is part of the theorem type). No
  bundling helper: an abstraction can't inject `letI` instances into the
  caller's context; only a macro could, not worth it. No code change; no
  new FRICTION entry (the existing `[resolved]` pin already covers it).

## Blockers / open questions

<none at round open>

## Hand-off / next phase

Round in progress ((B) + (C) complete: B1–B5, C1–C2 done). Next concrete
commit: **D1** — compress `notes/Phase14.md` (329 lines → under the 250 soft
budget) per `CLEANUP.md` §D: collapse the *Current state* paragraph and the
per-node *Lemma checklist* (which narrate the full landed-node history) to a
commit-log pointer + brief summary; preserve *Decisions made* (the coefficient
encoding + ground-set restriction are load-bearing for Phase 15) and the
*Hand-off* section. Then **D2** — re-skim `FRICTION.md` status sections (migrate
fully-indexed Phase-14 `[resolved]` entries to `FRICTION-archive.md`; lift any
2+-phase cross-cutting lesson). When (D) closes, write the round summary here
and flip the ROADMAP Status row to ✓.
