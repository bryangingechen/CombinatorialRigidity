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
  would re-probe. Set/re-confirmed sessions #6–#30 (latest: **#30**, 2026-06-24,
  fresh `/coordinate-phase`; user re-confirmed the triple [Standard triple] at
  session start; opus reachable via the Agent `model` param, no substitution
  needed). **The override expires session-end — a fresh coordinator re-runs the
  session-start availability check + re-confirms the triple.** **The active
  sub-phase is 23d; the A1 §I.8.21(α) feasibility recon is RESOLVED INFEASIBLE**
  (session #30, rows 435–436; design §I.8.24(4.22)). **Next dispatch awaits user
  adjudication of the phase direction — (C) honest-conditional / (D) reconsider /
  open ENTRY** (`notes/Phase23d.md` *Current state* + *Hand-off*). ALL landed
  leaves stay in tree (sound, reusable).
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
| 435 | A1 §I.8.21(α) feasibility spike (→ design §(4.22)) | —/—/— | opus | recon | recon — verdict UNSOUND, caught | — | 171k tok / 36 tools / 8.9 min | First-pass FEASIBLE = a route-COMPOSITION verdict (static-`W` cert type-checks w/ corner data carried as hyps; lone residual = spine deficiency) mis-read as dischargeability; leaned on the §(4.18)-dead cert + §(4.17)-dead router branch, and answered the wrong A1 question (the existing cert, not the new matrix-infra). Mechanically clean, substantively unsound — caught only by the coordinator confronting prior kernel impossibilities. → Findings 2026-06-24. |
| 436 | A1 spike resume — construct-or-concede (→ §(4.22)) | —/—/— | opus | recon/resume | recon — CONCEDED | — | 194k tok / 9 tools / 3.3 min | SendMessage-resume of 435 (same agentId, context intact) w/ the §(4.17)+§(4.18) confrontation. CONCEDED; built 2 sorry-free `concede_*` kernel re-derivations of the impossibilities for the real dispatch slot; confirmed SPIKE 1/2 carried `hG_eb_cand`/`W`/`hWS` as hyps, never discharged. Resume reused the full read phase (9 tools) — cheap vs a fresh refute agent. → Findings 2026-06-24. |
| 437 | §I.8.21(α) matrix-level (row-op) rework spike (→ design §(4.23)) | —/—/— | opus | recon | recon — INFEASIBLE (hypothesis disproven) | — | 199k tok / 71 tools / 15.3 min | User-authorized rework swing: does KT's rank-preserving ROW-OPERATION redundancy handling (vs span membership) escape the wall? DISPROVEN at the kernel (SPIKE 3b/4a/4b): the row-op IS the membership — pure-`vᵢ` corner needs `hingeRow a b ρ₀ ∈ span` (=hρGv), confirmed against the project's OWN Phase-22g `r̂=wGv` docs. The scissors: htopvanish-corner needs hρGv; hρe₀-corner not pure-vᵢ. 4th independent wall confirmation; honest INFEASIBLE (flag-don't-force worked) → option (C). → Findings 2026-06-24. |

## Findings

(accumulate episode bullets here; distill at each phase close per
the protocol)

- **2026-06-24 (rows 435–436) — the A1 §I.8.21(α) dissolution-recon episode (the value of
  construct-or-concede on a fragile-zone dissolution).** A compiler-checked SPIKE answers a
  route-COMPOSITION question ("do these objects compose to goal X?"), NOT a dischargeability one. The A1
  spike built a type-checking composition of the landed static-`W` cert + corner-assembly with the corner
  data (`W`/`hWS`/`hG_eb_cand`/`hvanish`) carried as HYPOTHESES, reported a single (spine-deficiency)
  residual, and returned **FEASIBLE** — but it never discharged those hypotheses, which two PRIOR kernel
  spikes (§(4.17)/(4.18)) had already proved unsatisfiable for the real consumer. Four tells let the
  coordinator catch it without a build: (a) the verdict DISSOLVED the phase's central wall (the
  highest-scrutiny trigger); (b) it contradicted a same-day STOP + primary-source recon; (c) it re-pointed
  at the exact decls those prior spikes killed; (d) it answered the wrong deliverable (the existing
  static-`W` cert, not the *new* §I.8.21(α) matrix-level infra A1 asked about). The decisive settle was a
  **construct-or-concede resume of the SAME spike** (SendMessage to its agentId, context + read phase
  intact, 9 tools / 3.3 min — far cheaper than a fresh refute agent): *produce the actual object at the
  kernel, or concede*. It conceded, re-deriving §(4.17)/(4.18) as two sorry-free `concede_*` theorems for
  the real dispatch slot. **Lesson:** for a dissolution verdict in a fragile zone, the cheapest decisive
  audit is to resume the same spike armed with the prior kernel-impossibilities and force
  construct-or-concede; a "single residual" from a composition spike is NOT evidence of dischargeability
  when the crux is carried as a hypothesis. (The satisfiability corollary is already in DESIGN.md
  *Constructibility recon*; this episode adds the construct-or-concede resume as its audit instrument.)

- **2026-06-24 (row 437) — the matrix-level rework recon (when a wall is genuinely intrinsic, and when to
  STOP reconning it).** After the A1 episode, the coordinator read KT §6.4.2 (eqs. 6.60–6.67) from the
  primary PDF and hypothesized the wall might be an ARTIFACT of the project's span-membership formalization —
  since KT certifies the rank by rank-preserving COLUMN+ROW operations, not membership. The user authorized
  "reworking landed material" to test it. A read-only design+spike DISPROVED the hypothesis at the kernel:
  KT's row operation `r̂ = Σλ rⱼ` IS the `G_v`-row part `wGv ∈ span(R(G_v,q))` — and the project's OWN
  Phase-22g code (`exists_redundant_panelRow_ab_decomposition`, the `r̂ = wGv` docstring) already encoded
  that equivalence. The "scissors": the pure-`vᵢ` corner satisfies the block separator's `htopvanish` but
  needs `hρGv` to enter the candidate span; the `hρe₀`-sourced corner enters the span but isn't pure-`vᵢ`;
  the two differ by exactly the wall row. This was the FOURTH independent kernel confirmation of the wall
  (§(4.18)/(4.20)/(4.21)/(4.23)) + the A1 concede. **Lessons:** (1) when a build-blocking wall has survived
  2–3 independent kernel refutations, one MORE carefully-aimed *orthogonal* recon (here: "is KT's
  row-operation framing genuinely different from the span membership?") is still worth it — it converts "we
  suspect intrinsic" into "kernel-confirmed intrinsic, the rework hypothesis is dead," which is exactly what
  lets a coordinator commit to the honest-conditional path without nagging doubt (and what justifies the
  cost to a user weighing a rework). (2) But after that, STOP: further swings need a genuinely-NEW
  mathematical idea, not another formalization angle. (3) The codebase's own docstrings can carry the
  decisive primary-source equivalence — read them (clause i) before betting a rework escapes.

