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
grandfathered **rows 1–189**, the **Phase 23a–23e rows 190–514** (with their
session-close config notes + *Findings*), and the **closed-phase *Findings***
(Phase 22h–22l + post-22j perf). This live file keeps only the config, the
**active sub-phase's** rows (currently **23f**, no rows yet), and active-phase
*Findings*, so the coordinator's every-dispatch read stays small. **When a
(sub-)phase closes, move its rows + its *Findings* close-out + its session-close
config bullet here** in the same close-out cleanup — a project phase-close
checklist item (`PHASE-BOUNDARIES.md` *When this commit closes a phase*); 23b
closed 2026-06-21 without it and the rows went stale (cleaned up 2026-06-22).

## Repo-local config

- **Testbed:** the molecular program — **Phase 23** (Case III general `d`:
  KT Lemma 6.13 → Thm 5.5 → Thm 5.6 → Conjecture 1.2; sub-lettered,
  codes-until-open). Open sub-phase = **23f** (`notes/Phase23f.md`). Closed
  sub-phases (22k–23e) + the phase status / next-step live in the ROADMAP cell +
  `notes/Phase23f.md` *Hand-off*, **not here**. Continues into successor phases
  until concluded.
- **Rungs:** haiku → sonnet → opus → fable (the Agent tool's `model` param).
- **Coordinator hook:** `.claude/commands/coordinate-phase.md` model-tier
  step, conditional on this file's Status.
- **Phase-side pointer:** `notes/Phase23f.md` *Hand-off* (the active sub-phase)
  + the recon `notes/Phase23-design.md` §(4.54) = the geometry-arm hand-off (the
  cert-route arc §(4.48)–(4.54) is closed/archived with 23e);
  the general-`d` reuse map is §1.33(C) of `notes/Phase22-realization-design.md`.
- **Attribution:** top-level `CLAUDE.md` *Working* → *Commit attribution*
  (exact author string + actual-model trailer).
- **Log-row length gate:** `notes/check-log-rows.py` enforces the protocol's
  ~600-char Notes cap. Run it before committing a log row (default mode checks
  only the rows this commit touched); it is wired into the coordinate-phase
  per-commit step. `--all` audits the whole (live) table; the closed sub-phases'
  rows (1–514) now live in the archive (frozen, not gated).
- **Standing rung override — Phase 23: OPUS-ONLY** (user-set, scoped to the
  whole phase: Case III general `d` is the conjecture's crux and sits in the
  §38 defeq-fragility zone where sonnet-and-below have repeatedly failed).
  S/P/B is still **rated and logged** per dispatch (experiment data), but the
  rung is **opus regardless of the map**; probes off; boundary pairs run
  opus-vs-opus or are skipped. Re-confirm (or lift) at session start.
- **Per-session run modifications** (re-confirm at session start, expires
  session-end): the **Standard triple** — OPUS-ONLY kept, 10-run check-in cap
  **lifted** (loop runs to phase close or a surfaced concern), step-4 mechanical
  fixups (wrong branch / author / trailer) **pre-authorized**. Availability under
  OPUS-ONLY: only **opus** is probed (the coordinator runs on it, reachable via the
  Agent `model` param); a fresh coordinator reverting to the S/P/B map would re-probe
  the other rungs. **The override expires session-end — a fresh coordinator re-runs
  the session-start availability check + re-confirms the triple.** Last re-confirmed
  **session #38** (2026-06-26, the `/coordinate-phase` loop that built the 23e cert
  items 3a–3b‴ + the §(4.53)/(4.54) spikes and closed 23e / opened 23f). The full
  sessions-#36–#38 history + the strategic adjudications (pursue the cert §(4.48);
  cert-shape route (A) §(4.53); close 23e §(4.54)) are archived in the 23e config
  close-out. (Session #36's `hIH` C.3 adjudication stands — lands with 23f.)
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
Rows 1–514 are in [`model-experiment-archive.md`](model-experiment-archive.md)
(1–189 grandfathered; 190–372 = Phase 23a + 23b; 373–434 = Phase 23c; 435–501 = Phase 23d;
502–514 = Phase 23e). This live table holds only the **active sub-phase (23f)** rows.

| # | Task | S/P/B | Model | Mode | Outcome | Rubric | Cost | Notes |
|---|---|---|---|---|---|---|---|---|
*(no rows yet — 23f's first dispatch is the geometry arm's `cGv`→`w` re-key leaf; the 23e rows 502–514 are archived.)*

## Findings

(accumulate episode bullets here; distill at each phase close per
the protocol)

- *(none yet for 23f. The 23e *Findings* (sessions #36–#38: the spike-before-build /
  2-leaf-trigger pattern that broke the recurring "remaining = ASSEMBLY" mis-framing, the
  deferred-crux scrutiny, the architecture-shape satisfiability check, profile×rung) are in the
  **23e close-out** in `notes/model-experiment-archive.md`. The durable cross-phase lessons live in
  the coordinate-phase command + DESIGN.md *Constructibility recon*.)*
