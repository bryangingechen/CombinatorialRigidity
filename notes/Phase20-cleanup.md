# Phase 20 cleanup round (work log)

**Status:** in progress. A3 (the round's one real fix) landed; A1 + B4
confirmed no-op. Remaining: A2 / B1–B3 / C1 / D1 / D2 — see the checklist
and *Hand-off* below.

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

- [x] **A1** — per-node statement-form check. DONE; **no-op** (no
  mismatch). Walked all 28 `\lean`-pinned nodes (30 declarations, since
  `lem:circuit-induces-rigid` / `lem:splitoff-deficiency` /
  `lem:reduction-measure` / `lem:reduction-step` each pin two names),
  comparing every blueprint statement form against the Lean signature
  (`Molecular/Induction.lean`). All names resolve and every form agrees:
  - **Side-conditions track the blueprint's stated `D` bounds exactly.**
    `D ≥ 1` (`circuit_induces_isRigidSubgraph`, the `rank_*`/`contract_*`
    chain, `splitOff_deficiency_{le,ge}`, `kt_lemma_41_overquantified`'s
    `1 ≤ bodyBarDim n`); `D ≥ 2` (`removeVertex_deficiency_ge`,
    `dof_tracking`, `isBase_vfiber_ncard_ge`, `exists_balanced_forest_packing`,
    `forest_surgery_{count,split}`, `no_rigid_edge_count`,
    `splitOff_isMinimalKDof`); `D ≥ 3` (`exists_degree_{le,eq}_two`,
    `minimal_kdof_reduction`). `lem:reducible-vertex` carries `2 ≤ |V(G)|`
    (`hV2`); `lem:reduction-measure` contraction half carries `2 ≤ |V(H)|`
    (`hH2`); `forest_surgery_{count,split}` carry `a ≠ b` (`hab`). Each
    matches the blueprint's explicit hypothesis text.
  - **ℕ-subtraction-free restatements** are the expected project idiom and
    match: `|X−e| = D(|V(X)|−1)` is `circuit_induces_isTight`'s
    `(X∖{e}).ncard + D = D·|V(X)|`; `|I'| = |I|−D` is `forest_surgery_count`'s
    `(⋃ Fs').ncard + D = I.ncard`; `ex:kt-41-overquantified`'s `|I'|+D=0` is
    verbatim.
  - **Benign extra side-conditions** (not a mismatch): several
    contraction/deficiency nodes carry a `V(G).Nonempty` / `V(H).Nonempty`
    (`hVGne`/`hVHne`) the blueprint statement does not spell out; these are
    implied by the node's degree-2 / subgraph hypotheses and are the
    standard `deficiency`/`rank_add_deficiency_eq` precondition. No blueprint
    edit warranted — the prose already names the substantive hypotheses.
  build confirmed green (`lake build CombinatorialRigidity.Molecular.Induction`).
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
- [x] **A3** — **the named-lemma promotion (carry-forward seed, the round's
  one known real fix).** DONE. Promoted the anonymous `example` to
  `Graph.kt_lemma_41_overquantified` (Induction.lean), flipped
  `molecular-induction.tex` `ex:kt-41-overquantified` from the
  `% Formalized as an unnamed Lean example` comment to
  `\lean{Graph.kt_lemma_41_overquantified}`, and dropped the now-stale
  "one-line `example`" prose in both the blueprint example and the Lean
  section docstring. build + lint + checkdecls green.

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
- [x] **B4** — `@[deprecated … (since := "narrative-bridge")]` shim
  (`splitOff_deficiency_le_of_forest_surgery`, `cor:forest-surgery-deficiency`).
  DONE; **no-op** (confirmed in passing during A1). Shim is to-spec:
  `@[deprecated splitOff_deficiency_le (since := "narrative-bridge")]` (the
  general-form target + sentinel), a one-line composition body
  (`forest_surgery_split hD hab …`), doc-comment explaining the narrative-
  bridge intent and the no-caller rationale, blueprint node carries
  `\lean{Graph.splitOff_deficiency_le_of_forest_surgery}` + `\leanok`.
  Matches `CombinatorialRigidity/CLAUDE.md` *Engineering conventions* +
  `blueprint/CLAUDE.md` *Narrative-bridge corollaries*.

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

- **A3 (named-lemma promotion).** The KT-Lemma-4.1 over-quantification
  disproof is now `Graph.kt_lemma_41_overquantified` rather than an
  anonymous `example`, so blueprint node `ex:kt-41-overquantified` carries a
  `\lean{...}` pointer instead of an orphan comment. No friction (trivial
  `rintro`/`rw [Set.ncard_empty]`/`omega` proof, unchanged).
- **A1 + B4 (no-op confirmations).** All 28 `\lean`-pinned nodes match
  their Lean signatures (A1); the forest-surgery narrative-bridge shim is
  to-spec (B4). No blueprint/Lean edits — confirmation only. Detail in the
  A1/B4 checklist entries above. The `D ≥ 1/2/3` side-condition split is the
  only systematic variation across nodes and it tracks the blueprint text
  exactly; the only deltas are benign `V(·).Nonempty` preconditions implied
  by each node's stated hypotheses.

## Blockers / open questions

- None at round open. The two Phase-20 carry-forwards in
  `notes/Phase20.md` *Hand-off* (graph↔matroid contraction bridge; forest
  surgery + balanced-packing — both off the Theorem-4.9 critical path) are
  **Phase-21 scheduling items, not cleanup items**; out of scope here.

## Hand-off / next phase

**Smallest concrete next commit:** execute **A2** — the
formalization-aside check on the `molecular-induction.tex` prose-aside hits
(L32, L247, L310, L340, L639, L979 per the A2 checklist entry), classifying
each as allowed one-clause modelling aside vs. the Phase-18 A2 basis-free /
changelog-not-math anti-pattern to collapse. Expected mostly no-op given the
chapter's phase-end re-read; lands as a confirmation commit (or a small TeX
fix if a changelog aside surfaces). **A1, A3, B4 are done** (A1/B4 no-op,
A3 the real fix). Remaining: A2 / B1–B3 / C1 / D1 / D2 — sweeps expected
mostly no-op; B1–B3/C1 may be batched into one confirmation commit. D1
(`notes/Phase20.md` 1089 lines, far over budget) is the other genuine
substance item. Close the round by flipping the ROADMAP Status row to ✓.
