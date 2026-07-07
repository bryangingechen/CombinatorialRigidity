# Phase 26 cleanup round — the molecular-program-closing hygiene pass (work log)

**Status:** in progress (opened 2026-07-07).

The post-Phase-26 cleanup round. Doubles as the **program-closing** round for
the molecular-conjecture program (17–26): Phases 24/25/26 shipped without their
own between-phase rounds, and the Phase-23-cleanup *Deferred to a future
dead-code / liveness sweep* carry-over (six items) was explicitly parked for
"a future cleanup round at a phase boundary" (`notes/Phase23-cleanup.md`,
echoed in `notes/Phase26.md` *Hand-off*). This round is that boundary. Round
manual: `CLEANUP.md`.

**Pre-round verification (2026-07-07, before any fix):** whole-project
`lake build` green (2860 jobs); the two headline theorems axiom-clean under
`lean_verify` (`PanelHingeFramework.molecular_conjecture`,
`SimpleGraph.molecule_rank_formula` → `{propext, Classical.choice, Quot.sound}`
only); no `sorry`/`axiom`/`native_decide` in proofs. The round is hygiene, not
correctness.

## Current state

**B1 done; A2 disposition settled (owner-adjudicated, 2026-07-07), executing.**
The dead `d=3` Case-III Claim-6.12 island is **not** blanket-retired: the
concrete d=3 development is *kept* to ground its blueprint exposition (owner
call — the concrete case is the readable on-ramp to KT's general Lemma 6.13,
which subsumes it). A2 now = cut only the *truly redundant* decls, re-pin the
affected nodes to the live producers, and **reframe** the exposition as an
explicitly secondary in-chapter section. Next concrete step: the A2 Lean cut +
re-pin commit (see the expanded A2 item).

## Lemma checklist (the round's task list, A–D)

Populated up front per `CLEANUP.md` *Task list discipline*. Each `[ ]` is its
own commit (or small cluster). Items carried from `notes/Phase23-cleanup.md`
*Deferred …* are tagged `(P23-carry #n)`.

### A/B — dead-code + blueprint honesty (the core)

- [x] **B1. Delete `case_I_dispatch`** (P23-carry #3). Was an unpinned
  zero-caller `d=3` `k:=2` wrapper of the live `case_I_dispatch_gen` (its
  one-line body); deleted. Green + lint-clean.
- [ ] **A2/B2. Trim + demote the d=3 Case-III Claim-6.12 exposition**
  (P23-carry #1). Reachability fully mapped via `lean_references` (see
  *Decisions*). The concrete d=3 dispatch chain is **kept** as grounding
  (`case_III_candidate_dispatch` → three arm producers
  `case_III_arm_realization{,_M2,_M3}` → `exists_complementIso…` d=3 →
  `exists_line_data…` d=3 → `exists_homogeneousIncidence_of_normals` d=3, all
  live-within-the-island). Sub-steps:
  - **A2a — cut truly-redundant Lean.** Delete the pure `(k:=2)` wrapper
    `case_III_claim612` (re-point its one caller `exists_complementIso…` d=3
    to `case_III_claim612_gen (k:=2)`); delete the `hann`-obsolete zero-caller
    `exists_hduality_witness_of_panel_incidence` (~104 lines, unpinned); delete
    the superseded abstract-row-family cluster `linearIndependent_sum_{p2,p3}_candidateRow`
    (+ `_selector`s) and `candidateRow_ne_zero` (~250 lines) — the live M₂/M₃
    producers are the framework-level `case_III_arm_realization_M2/_M3`, not these.
  - **A2b — re-pin nodes.** `lem:case-III-claim612` → `case_III_claim612_gen`;
    `lem:case-III-claim612-{p2,p3}-placement` + `-r-nonzero` → the arm producers
    `case_III_arm_realization_M2/_M3` they actually describe.
  - **A2c — reframe `sec:…-claim612`** as an explicitly secondary in-chapter
    section: relocate after the general `lem:case-III` (1313), add a lead
    paragraph ("concrete d=3 case, KT §6.4.1, subsumed by Lemma 6.13
    `lem:case-III`, retained as grounding + illustration, not load-bearing").
  Land as its own commit(s); rebuild + `verify.sh` (checkdecls) + lint each.
- [ ] **A3. `lem:case-II` orphaned bridges** (P23-carry #2). Its two pinned
  decls (`isInfinitesimallyRigidOn_insert_iff` `Pinning.lean:1632`, zero refs;
  `rankHypothesis_withNormal_withGraph_iff_finrank_pinnedMotions`
  `PanelHinge.lean:832`, refs all prose) are zero-caller orphaned infra — the
  live `case_II_realization_all_k` builds the extended framework directly. No
  live `_gen` sibling to re-pin onto; `lem:case-II` is `\uses`'d from 9 files
  (`case-ii.tex:84–85`). Decide node-wide: retire bridges + re-point/red
  `lem:case-II`, or keep as *documented* dead infra with a blueprint note.

### B — blueprint lint

- [ ] **B3. Multi-label `\cref{a,b}` renders as "??"** (P23-carry #5). 9 current
  instances (`grep -E '\\[cC]ref\{[^}]*,[^}]*\}'`, corpus-wide). Verify the
  plastex rendering failure, then fix (split to `\cref{a} and \cref{b}`, or a
  cleveref-config fix if one exists) + add the `lint.sh` guard the P23 note
  proposed.

### C — long-proof audit (screening; expected mostly no-op)

- [ ] **C1. Top-~10 long-proof screen** across the molecular layer (24–26 files
  esp., since 17–23 had dedicated perf passes). Run the LoC ranking, walk the
  four-question gate. Expect no-op per `CLEANUP.md` calibration; record the
  no-extract findings.

### D — project-organization compression

- [ ] **D1. Compress the two oversized closed design docs — DEFERRED this round**
  (owner call, 2026-07-07). `notes/Phase22-realization-design.md` (8590 lines) and
  `notes/Phase23-design.md` (5379) are past the ~1500-line `*-design.md` closed-arc
  tripwire — but they are the **primary raw-material archive** for the planned
  formalization-retrospective task (`notes/FormalizationRetrospective.md`). Compressing
  their closed arcs now would shed exactly the wrong-turns detail the retrospective
  draws on. **Hold** until the retrospective is scoped/written; then compress in step
  with harvesting. (The other D-items proceed.)
- [ ] **D2. Reconcile the exposition ledger** (`notes/BlueprintExposition.md`).
  Header claims "2 remain pending" but markers show 13 `[pending]` / 1 `[done]`.
  Per entry: verify whether its `.tex` prose already carries the exposition,
  flip the marker to `done (<commit>)` if so; write the genuinely-missing ones
  (at least Lemma 2.1 / Phase 17 and the Phase-20 forest-surgery family).
- [ ] **D3. Close the stale `ScrewSpaceCarrier-design.md`.** Status header still
  says general-`d` "part 2" is *deferred to the Phase-23 boundary*, but
  `ScrewSpace` is already an opaque general-`k` `def` (`RigidityMatrix/Basic.lean:115`)
  — Phase-23 CARRIER work subsumed it. Update the header to DONE + close the doc.
- [x] **D4. FRICTION `[resolved]` archive sweep** — no-op. Zero `[resolved]`
  entries (all open items are `[idiom]`/`[mirrored]`/`[process]`); nothing to
  migrate to `FRICTION-archive.md`.

## Blockers / open questions

- **A2 reachability — RESOLVED** (2026-07-07, via `lean_references`). The dead set
  is precisely: `case_III_claim612` (d=3 pure `(k:=2)` wrapper),
  `exists_hduality_witness_of_panel_incidence` (self-obsolete), and the abstract-
  row-family cluster `{p2,p3}_candidateRow` (+ selectors) + `candidateRow_ne_zero`.
  The candidate-row lemmas are **not** shared with the general-`d` path — the live
  M₂/M₃ producers are the framework-level `case_III_arm_realization_M2/_M3`
  (bottoming on the shared-live `augment_candidateRow`/`sumElim_candidateRow_iff`),
  not the `{p2,p3}_candidateRow` abstraction (a Phase-22e factoring superseded in
  22g/h). The concrete d=3 dispatch chain stays (grounds the demoted exposition).
- **Retrospective / D1 sequencing** — see D1 (deferred) + the retrospective stub.

## Hand-off / next phase

The round is hygiene; nothing downstream gates on it (`CLEANUP.md` *What a
cleanup round is not*). If the round is interrupted, resume from the first
unchecked `[ ]` above — the list is self-contained. Program is otherwise
complete: the molecular conjecture + Cor 5.7 are green and axiom-clean.

## Separately-planned / deferred (not this round)

- **Formalization retrospective** (`notes/FormalizationRetrospective.md`, planning
  stub landed this round). A narrative of the formalization's wrong turns — a
  *new-synthesis* deliverable and a deliberate exception to the "process lives in
  git/FRICTION/DESIGN, not live docs" convention, so it is scoped separately, not
  folded into this hygiene round. D1 is held for it (above).

## Decisions made during this round

- **A2 disposition (owner-adjudicated, 2026-07-07):** keep the concrete d=3
  Claim-6.12 development (grounds its exposition; the readable on-ramp to the
  general Lemma 6.13 that subsumes it), cut only truly-redundant Lean, re-pin the
  affected nodes to the live arm producers, and demote `sec:…-claim612` to a
  secondary in-chapter section (no separate appendix). Full sub-step plan +
  reachability verdict in the A2 checklist item / *Blockers*.
- **Retrospective planned separately + D1 deferred (owner call, 2026-07-07):**
  see *Separately-planned* above and D1.
- **B1 (2026-07-07):** deleted `case_I_dispatch` — a zero-caller, blueprint-
  unpinned `k:=2` wrapper whose body was just `case_I_dispatch_gen (k:=2)`. A
  future caller reconstructs it in one line; no value in retaining. Green + lint.
