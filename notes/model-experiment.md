# Model-tier experiment — repo-local log

**Status:** running. (This line arms the coordinator hook —
`.claude/commands/coordinate-phase.md`'s model-tier step is
conditional on it.)

**Protocol:** [`notes/model-experiment-protocol.md`](model-experiment-protocol.md)
— the portable, repo-agnostic half (axes, assignment map, rubric, log
schema), byte-identical across participating repos. This file carries only
repo-local state: config, the dispatch log, and *Findings*.

**Cross-repo protocol-sync** (pending amendments + last-sync date) lives in
[`notes/model-experiment-sync.md`](model-experiment-sync.md) — one pointer
line per amendment, *not* a copy of the amendment text (that copy is what
ballooned this header for a month; the text's canonical home is the protocol
file).

**Archive:** [`notes/model-experiment-archive.md`](model-experiment-archive.md)
(search-target, not read on load) holds the cold half of the log — the
grandfathered **rows 1–189**, the **Phase 23a–23h rows 190–670**, the
**post-Phase-23 cleanup-round rows 671–717**, the **Phase 24 rows
718–723**, the **Phase 25 rows 724–739**, the **Phase 26 rows 740–745**, and the
**post-Phase-26 cleanup-round rows 746–754** (each with session-close
config notes + *Findings* close-outs), plus the **closed-phase
*Findings*** (Phase 22h–22l + post-22j
perf). This live file keeps only the config, the **active phase's** rows and
*Findings* — **currently none**: the molecular program (17–26) and its
post-Phase-26 cleanup round are complete (round closed 2026-07-07, rows +
close-out archived), and the experiment is **paused + armed**. So the
coordinator's every-dispatch read stays small. **When a
(sub-)phase closes, move its rows + its *Findings* close-out + its session-close
config bullet here** in the same close-out cleanup — a project phase-close
checklist item (`PHASE-BOUNDARIES.md` *When this commit closes a phase*); 23b
closed 2026-06-21 without it and the rows went stale (cleaned up 2026-06-22).

## Repo-local config

- **Testbed:** the molecular program — **COMPLETE (17–26)**, and its
  **post-Phase-26 program-closing cleanup round CLOSED 2026-07-07** (rows
  746–754, archived). **No active testbed.** The experiment is **paused +
  armed** (user decision at the cleanup-round close, 2026-07-07): Status
  stays `running` so a future `/coordinate-phase` session auto-resumes it
  when the next substantive (ideally formalization) work opens. The deferred
  follow-on family (Formalization Retrospective, D2b exposition write-ups,
  A2-x, D1) is doc/exposition work — a weaker fit for the experiment's
  formalization question — so it is **not** auto-adopted as a testbed. Phase
  status lives in the ROADMAP table, **not here**.
- **Rungs:** haiku → sonnet → opus → fable (the Agent tool's `model` param).
- **Coordinator hook:** `.claude/commands/coordinate-phase.md` model-tier
  step, conditional on this file's Status.
- **Phase-side pointer:** `notes/MolecularConjecture.md` (the program map;
  Phase 26 planning) + `notes/Phase25.md` *Hand-off* (the Phase-25 close
  record; its design doc `notes/Phase25-design.md` keeps the §2.2/§2.6
  Phase-26 contract live). `notes/Phase23-design.md` is frozen as the
  §-cited archive.
- **Attribution:** top-level `CLAUDE.md` *Working* → *Commit attribution*
  (exact author string + actual-model trailer).
- **Log-row length gate:** `notes/check-log-rows.py` enforces the protocol's
  ~600-char Notes cap. Run it before committing a log row (default mode checks
  only the rows this commit touched); it is wired into the coordinate-phase
  per-commit step. `--all` audits the whole (live) table; the closed phases'
  rows (1–739) now live in the archive (frozen, not gated).
- **OPUS-ONLY lifted (2026-07-01, user-directed).** The Phase-23 standing
  override is retired: fable is back, and the protocol's **map v2**
  (the S=1/P=3 sonnet boundary cell + the fragility-zone modifier + the
  versioned rung addenda, all adopted 2026-07-01) replaces the blanket
  override as the fragile-zone control. S/P/B → map v2 governs from row 635.
  Trial discipline (user: "pay close attention to the results"): surface the
  first below-opus repaired / escalated / BLOCKED outcome under the new map
  to the user immediately, not just at the check-in cap.
- **Fragility-zone list (repo-local input to map v2's fragility-zone
  modifier):** `Molecular/AlgebraicInduction/` (esp. `CaseIII/` +
  `Theorem55.lean`), `Molecular/RigidityMatrix/`, and any
  ScrewSpace-carrier-touching edit — the §38 / heavy-`whnf` defeq-fragile
  zone where sonnet has wedged (archive rows 7, 157). **Producer builds**
  touching these → **opus minimum**; mechanical refactors / doc edits there
  stay mapped (archive row 166: a sonnet refactor in the same zone ran
  clean). The combinatorial side (`Molecular/Induction/`, incl.
  `ForestSurgery/`) is NOT in the zone.
- **Per-session run modifications — CLOSED.** The 2026-07-07
  program-closing cleanup-round session (fable unavailable → opus
  substitute; cap lifted; rescue-§1 fixups pre-authorized; experiment
  continued for the round, then **paused + armed** at its close) is over;
  its session-close config note + the round's rows/*Findings* are in
  `model-experiment-archive.md`. No active session overrides — a fresh
  coordinator re-runs the session-start availability check and reverts to
  the S/P/B → map v2.
- **Availability check is user-confirmed from 2026-07-02 on** (user-directed
  amendment to `.claude/commands/coordinate-phase.md`): no probe dispatches;
  the session-start check-in asks the user whether any rungs are missing, and
  that check-in **blocks** until answered (no timeout-default).
- **Expired overrides (audit trail in git + *Findings*).** The
  2026-06-{10,12,13,16} session-local rung / availability overrides all
  expired by their own terms; a fresh coordinator reverts to the S/P/B → map
  (substituting opus when fable is unavailable). Grounds: *Findings* (the
  §38-trap / KT-4.2-fiber sonnet-failure clusters).
- **Boundary-pair worktree (repo-local standing constraint).** Git worktrees
  *outside* the project dir fail under the sandbox — create them *inside*
  (e.g. `.bp-<slice>`, hidden via a `.git/info/exclude` line) or use the Agent
  tool's `isolation: "worktree"`. (`~/.cache` write was granted 2026-06-13 so a
  duplicate can run `lake exe cache get`; verify per session — the protocol's
  `.lake`-seeding default works regardless.)

## Log

Schema per the protocol. Rubric vector order: gates / scope / Lean
quality / blueprint sync / notes discipline / commit message
(✓ = pass, ✗ = fail, — = not applicable, e.g. doc-only commits).
Rows 1–754 are in [`model-experiment-archive.md`](model-experiment-archive.md)
(1–189 grandfathered; 190–670 = Phases 23a–23h + the umbrella close; 671–717 = the
post-Phase-23 cleanup round; 718–723 = Phase 24; 724–739 = Phase 25;
740–745 = Phase 26, ending the molecular-conjecture program 17–26; 746–754 =
the post-Phase-26 program-closing cleanup round, closed 2026-07-07). This live
table holds only the **active phase's** rows — currently none: the program + its
cleanup coda are complete, and the experiment is **paused + armed** (Status
`running`), auto-resuming when the next substantive work opens.

(no rows — Phase-26-cleanup closed 2026-07-07; rows 746–754 archived to
[`model-experiment-archive.md`](model-experiment-archive.md) with the round's
*Findings* close-out and session-close config note. The experiment is **paused +
armed**: no active testbed, Status stays `running` so a future `/coordinate-phase`
session auto-resumes it when substantive work opens.)



## Findings

(accumulate episode bullets here; distill at each phase close per
the protocol)

(none live — the Phase-26-cleanup *Findings* close-out (the profile×rung
outcomes + lessons) and the A3 notification-timing bullet are archived to
[`model-experiment-archive.md`](model-experiment-archive.md); the experiment
is paused + armed pending the next testbed.)
