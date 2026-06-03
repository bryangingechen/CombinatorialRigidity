# Phase 20 cleanup round (work log)

**Status:** in progress. Round-opening commit lands the comprehensive A–D
sweep checklist (this file) + the ROADMAP Status row; no fixing has begun.

Between-phases cleanup round, run after Phase 20 (combinatorial induction →
Theorem 4.9, KT §3.4–3.5 + §4) closed in `144e3b5` and before Phase 21
(algebraic induction, KT §5–6) opens. Round manual: `CLEANUP.md`. The
per-commit friction review (`CombinatorialRigidity/CLAUDE.md`) still fires on
every commit in this round.

## Scope

Phase-20 surface:
- **Lean:** `CombinatorialRigidity/Molecular/Induction.lean` (3524 lines —
  the largest single file in the project; the full KT §3.4–3.5 inherited
  chain + four graph operations + the deficiency-count critical path A–H +
  the off-path forest-surgery substrate and addendum).
- **Blueprint:** `blueprint/src/chapter/molecular-induction.tex`
  (`sec:molecular-induction`, 1008 lines, 32 nodes). All Phase-20 dep-graph
  nodes live here; `deficiency.tex` carries **no** Phase-20 node (verified by
  grep — the task brief's "deficiency.tex Phase-20 nodes" is vacuous, the
  Phase-19 chapter was not touched in Phase 20).

`lake build CombinatorialRigidity.Molecular.Induction` should be confirmed
green before the first audit/fix commit.

## Pre-open sweep outcome (scoping — comprehensive, not yet fixed)

Greps run 2026-06-03 over the Phase-20 surface; the per-bucket checklist
below records every site so a session that runs out of time is resumable
from this log alone (CLEANUP.md *Task list discipline*).

- **One genuine fix is named up front (A3 / carry-forward seed):** the
  anonymous `example` (Induction.lean L346, the `ex:kt-41-overquantified`
  over-quantification disproof) must be promoted to a named lemma so the
  blueprint node can carry a `\lean{}` pointer instead of its current
  `% Formalized as an unnamed Lean example; no \lean{} pointer to pin`
  orphan comment (molecular-induction.tex L332). This is the seed item from
  `notes/Phase20.md` *User-directed addendum items* #2.
- **B/C expected mostly no-op** per CLEANUP.md's calibration note (a phase
  introduces a genuinely new long-proof shape rarely): no `nolint` /
  `set_option linter`, no `change`/`show`, no `show … from rfl` on the
  surface. `classical` (20) + `haveI Nonempty/Finite/…` (9) sites are the
  project-standard `[Finite]`→body-bridge, to be confirmed per-site. The
  4+-arg `rw` chains (11) are mostly the `mulTilde, edgeMultiply_*,
  Set.mem_setOf_eq, …` defeq-unfold idiom already confirmed no-op in the
  Phase-19 cleanup (B3 there); re-confirm none is a new missing-fused-lemma.
- **Substance is A (per-node form re-confirm on 32 nodes + the one orphan
  fix) and D (Phase20.md length + project-org re-skim).** Phase20.md is
  1089 lines — far past the 250-line soft budget; D1 is a real item (assess
  density vs. genuine over-length given the big multi-route phase).

## Lemma checklist (task list across A–D)

### Bucket A — Blueprint ↔ Lean divergence

- [ ] **A1** — per-node statement-form check. Walk all 30 `\lean`-pinned
  nodes in `molecular-induction.tex` (32 labels − `rem:kt-lemma-41`,
  `rem:kt-lemma-44` which are prose remarks, − `ex:kt-41-overquantified`
  which is the A3 orphan): compare each blueprint statement form against the
  Lean signature (hypotheses incl. the `2 ≤ bodyBarDim n` / `3 ≤ bodyBarDim
  n` / `V(G).Nonempty` / `a ≠ b` side-conditions that vary across nodes,
  conclusion form, implicit/explicit binders). Flag any mismatch.
- [ ] **A2** — formalization-aside check. Re-read the prose-aside hits
  (molecular-induction.tex L32 "fully formalized, repairing the gloss",
  L247 "Formalizing the forest surgery …", L310 "splitting-off direction is
  fully formalized", L340 "Formalized as a one-line `example`", L639
  "unformalized", L979 "The formalization …"). For each: is it a
  one-clause modelling aside (allowed), a load-bearing math statement, or a
  basis-free/representation-choice narration (the Phase-18 A2 anti-pattern to
  collapse)? Given the phase's multi-route history (pivot + Finding/Replan +
  addendum), watch specifically for changelog-not-math narration that
  accreted across the per-commit subagents.
- [ ] **A3** — **the named-lemma promotion (carry-forward seed, the round's
  one known real fix).** Promote the anonymous `example` (Induction.lean
  L346, `lem:forest-surgery-split` over-quantification note) to a named
  `lemma` (e.g. `Graph.kt_lemma_41_overquantified` or similar), then flip
  `molecular-induction.tex` `ex:kt-41-overquantified` to carry a `\lean{...}`
  pointer (replacing the `% Formalized as an unnamed Lean example` comment).
  Run `checkdecls` (new `\lean{}` pointer). Lean + blueprint in one commit.
  Seed: `notes/Phase20.md` *User-directed addendum items* #2.

### Bucket B — Code-smell sweep

- [ ] **B1** — `classical` (20 sites: L190/260/618/753/960/1140/1241/1312/
  1408/1572/1664/1847/2365/2547/2642/2800/2876/2986/3220/3470) + `haveI`
  finiteness/Nonempty (9 sites: L623/761/968/1141/3471 `Nonempty α := ⟨a⟩`;
  L1573 `G.Finite`; L2987 `Nonempty (Fin (bodyBarDim n))`; L3282 `Nonempty
  (β × Fin (bodyHingeMult n))`). Confirm each is the project-standard
  `[Finite]`→body-`classical`/`Fintype` bridge or a Nonempty derived from a
  hypothesis vertex — not a signature-decidability boundary that should move
  to `[DecidableEq]`/`[Fintype]`.
- [ ] **B2** — `noncomputable def` (3 sites: L1742 `collapseTo`, L1752
  `rigidContract`, L2142 `fiberDegree`). Confirm each is forced
  (`collapseTo` uses `open Classical … if`; `rigidContract` built on it;
  `fiberDegree` on `Set.ncard`) vs. accidental.
- [ ] **B3** — 4+-arg `rw` chains (11 sites: L861/996/1027 `numParts,
  numParts, …`; L1424/2379/2387/2394/2730 `mulTilde, edgeMultiply_*,
  Set.mem_setOf_eq, …`; L2234/2428 `mulTilde, edgeMultiply_isLink,
  splitOff_isLink, …`; L2448/2511 `mulTilde, edgeMultiply_edgeSet,
  Set.mem_setOf_eq` at hyps). Confirm each is a cross-API-layer defeq-unfold
  (the Phase-19-B3 confirmed idiom) and not a missing-fused-lemma; check the
  repeated `numParts, numParts` and `mulTilde, edgeMultiply_edgeSet,
  Set.mem_setOf_eq` shapes for a one-line mirror worth extracting (they recur
  3× and 5× respectively).
- [ ] **B4** — `@[deprecated … (since := "narrative-bridge")]` shim
  (`splitOff_deficiency_le_of_forest_surgery`, `cor:forest-surgery-deficiency`).
  Confirm the shim follows the project pattern (one-line composition, defers
  to the general `splitOff_deficiency_le`, `since := "narrative-bridge"`
  sentinel) per `CombinatorialRigidity/CLAUDE.md` *Engineering conventions* +
  `blueprint/CLAUDE.md` *Narrative-bridge corollaries*. Expected no-op (it
  was authored to-spec this phase) — confirm, don't re-litigate.

### Bucket C — Long-proof audit

- [ ] **C1** — top-~10 long-proof four-question walk (API extraction /
  missed-mathlib-lemma / tactic substitution / cross-proof unification),
  ranked by body line count over Induction.lean (3524 lines). Per CLEANUP.md
  *Calibration*, expect mostly no-op (structural-shape regime); the four-
  question walk is the audit gate confirming the no-extract finding. Watch
  specifically for cross-proof unification among the partition-count
  comparison proofs (`splitOff_deficiency_{le,ge}`, `removeVertex_deficiency_ge`
  all run the same maximizer-restriction / partition-extension backbone — the
  Phase-20 notes flag them as siblings; verify they share a per-step backbone,
  not just boilerplate, before claiming a combinator) and among the reroute /
  forest-surgery acyclicity lemmas.

### Bucket D — Project-organization compression

- [ ] **D1** — `notes/Phase20.md` length (1089 lines). **Far past the
  250-line soft budget** — well beyond even the 350–450 adaptive ceiling for
  a big phase (`notes/CLAUDE.md` *Soft length budget*). Assess: is this
  density-justified (the phase had a mid-stream pivot + two Findings + a
  corrected-over-claim addendum, each legitimately recorded), or has content
  accreted that should be promoted/compressed? Candidate compressions: the
  *CORRECTION*, *Finding 2 REFUTED*, and *TODO Progress VERDICT* blocks
  duplicate material now also in *Current state* and the *forest surgery*
  checklist entries (one source of truth — `notes/CLAUDE.md` *Don't duplicate*).
  The phase is closed, so per CLEANUP.md *Project-organization compression*
  the multi-route narrative can compress to a commit-log pointer + brief
  summary. Bring it to the adaptive ceiling at most.
- [ ] **D2** — project-org re-skim (`ROADMAP.md`, `TACTICS-GOLF.md`,
  `TACTICS-QUIRKS.md`, `notes/FRICTION.md` status sections). The Phase-20
  close already lifted TACTICS-GOLF §11 (induction-on-derived-measure),
  TACTICS-QUIRKS §28 (`↓reduceIte`) + §29 (cycle-lift), and several FRICTION
  entries. Re-confirm: nothing drifted; no Phase-20 decision sits at the
  2+-site/2+-phase promotion threshold un-lifted; FRICTION status sections
  scannable (resolved Phase-20 entries indexed elsewhere → consider
  `FRICTION-archive.md` migration); no stale prose-count/section-name
  reference in DESIGN.md/ROADMAP.md.

## Decisions made during this round

<populated as fixes land; one entry per fix commit>

## Blockers / open questions

- None at round open. The two Phase-20 carry-forwards in
  `notes/Phase20.md` *Hand-off* (graph↔matroid contraction bridge; forest
  surgery + balanced-packing — both off the Theorem-4.9 critical path) are
  **Phase-21 scheduling items, not cleanup items**; out of scope here.

## Hand-off / next phase

**Smallest concrete next commit:** execute **A3** — promote the anonymous
`example` at `Molecular/Induction.lean` L346 to a named lemma (the
over-quantification disproof of KT Lemma 4.1), then flip
`molecular-induction.tex` `ex:kt-41-overquantified` (L331–333) to carry a
`\lean{...}` pointer to the new name in place of its
`% Formalized as an unnamed Lean example` orphan comment. Lean + blueprint
in one commit; run `lake build` + `lake lint` + `checkdecls`. This is the
round's single known real fix (the carry-forward seed); the remaining A1/A2/
B1–B4/C1/D1/D2 items are sweeps expected mostly no-op, each landing as its
own confirmation/fix commit per CLEANUP.md *Workflow* rule 3. Close the round
by flipping the ROADMAP Status row to ✓.
