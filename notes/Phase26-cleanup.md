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

Log skeleton + task list landed. Next concrete step: **B1** (delete the
unpinned zero-caller `case_I_dispatch`) — the safe warm-up before the delicate
dead-island retirement (A2).

## Lemma checklist (the round's task list, A–D)

Populated up front per `CLEANUP.md` *Task list discipline*. Each `[ ]` is its
own commit (or small cluster). Items carried from `notes/Phase23-cleanup.md`
*Deferred …* are tagged `(P23-carry #n)`.

### A/B — dead-code + blueprint honesty (the core)

- [ ] **B1. Delete `case_I_dispatch`** (P23-carry #3). Unpinned zero-caller
  `d=3` `k:=2` wrapper (`Theorem55.lean:2465`); blueprint pins the *live*
  `case_I_dispatch_gen` (`case-i.tex:607`), not this. Clean delete + rebuild.
- [ ] **A2/B2. Retire the dead `d=3` Case-III Claim-6.12 dispatch island**
  (P23-carry #1). `case_III_candidate_dispatch` (`Realization.lean:324`, zero
  code callers — all refs prose) → `exists_complementIso_ne_zero_of_homogeneousIncidence`
  (`Claim612.lean:1486`) → `case_III_claim612` (`Claim612.lean:1353`) + the
  candidate-row cluster (`linearIndependent_sum_augment_candidateRow`,
  `_p2_`/`_p3_candidateRow`, `candidateRow_ne_zero`, `exists_candidate_row_eq612`).
  The live all-`k` path routes through `chainData_dispatch` for every grade
  incl. `d=3`, so the island is bypassed. **Delicate:** confirm per-decl
  reachability (candidate-row lemmas may be *shared* with the general-`d`
  Lemma-6.13 path — verify with `lean_references` / trial-delete-rebuild before
  removing each). Then reconcile the ~13 `sec:molecular-algebraic-induction-claim612`
  blueprint nodes (`case-iii.tex` 595–1100) + the `meet.tex:235` pin: re-red /
  retire / re-point per node. Likely a multi-commit sub-cluster.
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

- [ ] **D1. Compress the two oversized closed design docs.**
  `notes/Phase22-realization-design.md` (8590 lines) and
  `notes/Phase23-design.md` (5379) — both far past the ~1500-line `*-design.md`
  closed-arc tripwire (`notes/CLAUDE.md`), their phases long closed. Compress
  closed arcs to ≤3-line verdicts + pointers.
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

- **A2 per-decl reachability** is the one genuine unknown: are the candidate-row
  construction lemmas shared with the live general-`d` Lemma-6.13 path, or
  wholly inside the dead `d=3` island? Resolve empirically (trial-delete +
  rebuild, or `lean_references`) before deleting each — do not delete on the
  grep evidence alone.

## Hand-off / next phase

The round is hygiene; nothing downstream gates on it (`CLEANUP.md` *What a
cleanup round is not*). If the round is interrupted, resume from the first
unchecked `[ ]` above — the list is self-contained. Program is otherwise
complete: the molecular conjecture + Cor 5.7 are green and axiom-clean.

## Decisions made during this round

(one-line verdicts land here as items close; git is the audit trail)
