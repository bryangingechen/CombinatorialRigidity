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

Next concrete step: continue (B) — B3 (`noncomputable def`
forced-vs-accidental), then B2/B4/B5, then (C)/(D).

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
- [ ] B2 — 14 `classical` invocations across `KFrame.lean` (11) +
  `Rank.lean` (3): is `[DecidableEq …]` a cleaner boundary at each, or is
  the decidability genuinely unavailable (mathlib `[Finite]`-bridge idiom
  per `DESIGN.md` *Typeclass shape*)?
- [ ] B3 — 8 `noncomputable def` in `KFrame.lean`: confirm each is forced
  (`Matroid.ofFun`, `FractionRing`, `Classical.choose`-backed orientation,
  no `Decidable` body) vs accidental.
- [ ] B4 — `change`/`show`, `show … from rfl`, and 3+-arg single-step
  `rw` chains all came back **clean** on `KFrame.lean` at round open;
  re-confirm on `Rank.lean` adders and close as no-op if so.
- [ ] B5 — `@[nolint …]` / `set_option linter.*` came back **clean** on
  both files; confirm no-op.

### C. Long-proof audit

- [ ] C1 — `linearIndepOn_kFrameRow_of_isSparse_restrict` (~95 lines, the
  reverse-half wiring). Walk the four-question audit (API extraction /
  missed mathlib lemma / tactic substitution / cross-proof unification).
  Expect a no-op per `CLEANUP.md` *Calibration* (forced case-dispatch /
  wiring boilerplate), but the walk is the gate.
- [ ] C2 — `forest_count_of_linearIndepOn_kFrameRow` (~27 lines, forward
  half). Below the §C 50-line threshold; spot-check only if C1 surfaces a
  shared backbone with the reverse half (the two genericity halves are the
  obvious cross-proof-unification candidate to rule in/out).

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
- **A1+A2 (KFrame.lean, doc-only).** Corrected three reverse-section
  docstring blueprint node-anchors (`lem:k-frame-specialize-li`,
  `lem:k-frame-forest-packing-of-sparse`, `lem:k-frame-specialize-identity`
  — all were `lem:k-frame-specialize-forest`). Reworded six stale
  incremental-build asides (module docstring "is deferred" / "remaining
  Phase-14 target"; two reverse-half "follow-up node" lines) to reflect
  the landed reverse half. No statement/proof changes; no FRICTION
  entry (pure divergence-audit doc fix). Blueprint TeX unchanged — the
  pins were already correct; the drift was Lean-side.
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

Round in progress (mid-(B)). Next concrete commit: **B3** — walk the
eight `noncomputable def` in `KFrame.lean` (`kFrameIndet`, `kFrameRow`,
`kFrameMatroid`, `blockPiSpan`, `constPiSpanEquiv`, `blockPiSpanOn`,
`kFrameRowR`, `forestEval`) and confirm each `noncomputable` is forced
(`Matroid.ofFun` / `FractionRing` / `Classical.choose`-backed
orientation / `MvPolynomial.eval` with no `Decidable` body) vs
accidental; record as a no-op confirm or fix as found. Then B2 (the 14
`classical` invocations), B4/B5 (re-confirm clean on the `Rank.lean`
adders), then (C) the two long proofs and (D) compress `notes/Phase14.md`
+ FRICTION re-skim. When (D) closes, write the round summary here and
flip the ROADMAP Status row to ✓.
