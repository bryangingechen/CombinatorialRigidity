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
grandfathered **rows 1–189**, the **Phase 23a/23b/23c rows 190–434** (with their
session-close config notes + *Findings*), and the **closed-phase *Findings***
(Phase 22h–22l + post-22j perf). This live file keeps only the config, the
**active sub-phase's** rows (currently **23d**, no rows yet), and active-phase
*Findings*, so the coordinator's every-dispatch read stays small. **When a
(sub-)phase closes, move its rows + its *Findings* close-out + its session-close
config bullet here** in the same close-out cleanup — a project phase-close
checklist item (`PHASE-BOUNDARIES.md` *When this commit closes a phase*); 23b
closed 2026-06-21 without it and the rows went stale (cleaned up 2026-06-22).

## Repo-local config

- **Testbed:** the molecular program — **Phase 23** (Case III general `d`:
  KT Lemma 6.13 → Thm 5.5 → Thm 5.6 → Conjecture 1.2; sub-lettered,
  codes-until-open). 22k/22l + the post-22l perf round closed 2026-06-16;
  23a/CARRIER Lean closed 2026-06-16 (row 190); 23b/CHAIN closed 2026-06-21
  (CHAIN bricks landed, the `hρGv`-seam characterized as a hard core); 23c closed
  2026-06-24 (option (A) built + the interior-`hρe₀` crux closed, but the general-`d`
  rank cert hit the member-mapping wall — a phase STOP); the open sub-phase is **23d**
  (`notes/Phase23d.md` — the rank-certification reconsideration; next = the A1
  §I.8.21(α) feasibility recon). Continues into successor phases until concluded.
- **Rungs:** haiku → sonnet → opus → fable (the Agent tool's `model` param).
- **Coordinator hook:** `.claude/commands/coordinate-phase.md` model-tier
  step, conditional on this file's Status.
- **Phase-side pointer:** `notes/Phase23d.md` *Hand-off* + the recon
  `notes/Phase23-design.md`; the general-`d` reuse map is §1.33(C) of
  `notes/Phase22-realization-design.md`.
- **Attribution:** top-level `CLAUDE.md` *Working* → *Commit attribution*
  (exact author string + actual-model trailer).
- **Log-row length gate:** `notes/check-log-rows.py` enforces the protocol's
  ~600-char Notes cap. Run it before committing a log row (default mode checks
  only the rows this commit touched); it is wired into the coordinate-phase
  per-commit step. `--all` audits the whole (live) table; the closed sub-phases'
  rows (1–434) now live in the archive (frozen, not gated).
- **Standing rung override — Phase 23: OPUS-ONLY** (user-set, scoped to the
  whole phase: Case III general `d` is the conjecture's crux and sits in the
  §38 defeq-fragility zone where sonnet-and-below have repeatedly failed).
  S/P/B is still **rated and logged** per dispatch (experiment data), but the
  rung is **opus regardless of the map**; probes off; boundary pairs run
  opus-vs-opus or are skipped. Re-confirm (or lift) at session start.
- **Per-session run modifications** (re-confirm at session start, expires
  session-end): the **same triple** — OPUS-ONLY kept, 10-run check-in cap
  **lifted** (loop runs to phase close or a surfaced concern), step-4 mechanical
  fixups (wrong branch / author / trailer, incl. the `Claude-Session` trailer)
  **pre-authorized** — plus the **same availability**: opus confirmed (the
  coordinator runs on it, reachable via the Agent `model` param); other rungs
  not probed under OPUS-ONLY, so a fresh coordinator reverting to the S/P/B map
  would re-probe. Set/re-confirmed sessions #6–#29 (latest: **#29**, 2026-06-24,
  fresh `/coordinate-phase`; user re-confirmed the triple at session start; opus
  reachable via the Agent `model` param, no substitution needed). **The
  override expires session-end — a fresh coordinator re-runs the
  session-start availability check + re-confirms the triple.** **23c closed 2026-06-24 at the
  member-mapping-wall phase STOP; the active sub-phase is now 23d** — next dispatch =
  the A1 §I.8.21(α) feasibility recon (read-only spike), full kit in
  `notes/Phase23d.md` *A1 dispatch kit*. ALL landed leaves stay in tree (sound, reusable).
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
Rows 1–434 are in [`model-experiment-archive.md`](model-experiment-archive.md)
(1–189 grandfathered; 190–372 = Phase 23a + 23b; 373–434 = Phase 23c).

| # | Task | S/P/B | Model | Mode | Outcome | Rubric | Cost | Notes |
|---|---|---|---|---|---|---|---|---|

## Findings

(accumulate episode bullets here; distill at each phase close per
the protocol)

