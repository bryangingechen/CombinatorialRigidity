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

Next concrete step: (B) code-smell sweep — start B1 (the
`letI`-pair sites; likely confirm-only per the FRICTION pin) or B3
(`noncomputable def` forced-vs-accidental), then B2/B4/B5, then (C)/(D).

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

- [ ] B1 — repeated `letI : DecidableEq α := Classical.decEq α` +
  `letI : DecidablePred (· ∈ E(G)) := Classical.decPred _` pair
  (~7 sites in `KFrame.lean`). **Likely confirm-only:** FRICTION
  `[resolved]` *`Graph.orientation.signedIncMatrix` needs `[DecidableEq α]`
  + `[DecidablePred (· ∈ E(G))]` …* pins the term-level `letI` as the
  accepted boundary (keeps the def signatures binder-free). Confirm the
  sites match that pinned answer; consider whether a single
  `letI`-bundling helper is worth it given the repetition count.
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

## Blockers / open questions

<none at round open>

## Hand-off / next phase

<written when the round closes; names what carried over and updates the
ROADMAP Status row>
