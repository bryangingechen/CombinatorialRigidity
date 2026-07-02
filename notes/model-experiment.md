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
grandfathered **rows 1–189**, the **Phase 23a–23g rows 190–660** (with their
session-close config notes + *Findings*, incl. the **23g rows 631–660** + the
**23g close-out**), and the **closed-phase *Findings*** (Phase 22h–22l +
post-22j perf). This live file keeps only the config, the
**active sub-phase's** rows (23h, opened 2026-07-02), and active-phase
*Findings*, so the coordinator's every-dispatch read stays small. **When a
(sub-)phase closes, move its rows + its *Findings* close-out + its session-close
config bullet here** in the same close-out cleanup — a project phase-close
checklist item (`PHASE-BOUNDARIES.md` *When this commit closes a phase*); 23b
closed 2026-06-21 without it and the rows went stale (cleaned up 2026-06-22).

## Repo-local config

- **Testbed:** the molecular program — **Phase 23** (Case III general `d`:
  KT Lemma 6.13 → Thm 5.5 → Thm 5.6 → Conjecture 1.2; sub-lettered,
  codes-until-open). **23h (ASSEMBLY) open** (2026-07-02) — the last
  Phase-23 sub-phase. Closed
  sub-phases (22k–23g) + the phase status / next-step live in the ROADMAP cell +
  `notes/Phase23h.md` *Hand-off*, **not here**. Continues into successor phases
  until concluded.
- **Rungs:** haiku → sonnet → opus → fable (the Agent tool's `model` param).
- **Coordinator hook:** `.claude/commands/coordinate-phase.md` model-tier
  step, conditional on this file's Status.
- **Phase-side pointer:** `notes/Phase23g.md` *Hand-off* (the active sub-phase)
  + the recon `notes/Phase23-design.md` §C.2/§C.5 (the CHAIN-5 reshape + the ENTRY
  `exists_chain_data_of_noRigid` extractor) and the frozen CHAIN↔ENTRY contract
  §C.0–C.6; the general-`d` reuse map is §1.33(C) of
  `notes/Phase22-realization-design.md`.
- **Attribution:** top-level `CLAUDE.md` *Working* → *Commit attribution*
  (exact author string + actual-model trailer).
- **Log-row length gate:** `notes/check-log-rows.py` enforces the protocol's
  ~600-char Notes cap. Run it before committing a log row (default mode checks
  only the rows this commit touched); it is wired into the coordinate-phase
  per-commit step. `--all` audits the whole (live) table; the closed sub-phases'
  rows (1–514) now live in the archive (frozen, not gated).
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
- **Per-session run modifications** (re-confirm at session start, expires
  session-end): availability = **all four rungs** (haiku / sonnet / opus /
  fable), no substitution — probed 2026-07-02, then the user's (late)
  session-start answer confirmed no missing models; **addenda versions in
  effect: `haiku-a1` / `sonnet-a2`**; step-4 mechanical fixups (wrong branch /
  author / trailer) **pre-authorized**; check-in cap **LIFTED** (user,
  2026-07-02) — run until phase close or a stop trigger.
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
Rows 1–660 are in [`model-experiment-archive.md`](model-experiment-archive.md)
(1–189 grandfathered; 190–372 = Phase 23a + 23b; 373–434 = Phase 23c; 435–501 = Phase 23d;
502–514 = Phase 23e; 515–630 = Phase 23f; 631–660 = Phase 23g). This live table holds only
the **active sub-phase (23h, once opened)** rows.

| # | Task | S/P/B | Model | Mode | Outcome | Rubric | Cost | Notes |
|---|---|---|---|---|---|---|---|---|
| 661 | 23h OPEN — `notes/Phase23h.md` + sub-phase-open sync (`24d35aaa`) | 3/1/1 | fable | normal | clean | —✓——✓✓ | 187k tok / 35 tools / 7.2 min | Phase-open (fable-mapped; fable reachable this session). Clean docs-only open: A1–A5 Layer plan seeded faithfully from the 23g hand-off (+ design §2 pointer); umbrella Phase-23 row correctly stayed ◐ with 23h marked open; public surfaces verified-no-edit (arc-level — correct for a sub-phase open); red-node gate recorded in the note (no red stubs; the 3 green restate targets read end-to-end). `MolecularConjecture.md` 4-spot sync. Correct trailer. Coord: mechanics + full ROADMAP/note diff review clean; no Lean touched per dispatch scope. |
| 662 | 23h A1 — producer-site rewire (`b7728996`) | 1/2/1 | opus | normal | clean | ✓✓✓✗✓✓ | 181k tok / 61 tools / 18.2 min | Fragility-zone producer build → opus min (map v2). Coord pre-verified slot-match (brick conclusions ≡ binder bodies). Rewire faithful at all 4 sites; sound beyond-pin simplification: `d=3` wrappers route through the general extractor (covers `d=3`), orphaning `chainData_extract_d3` (sweep-recorded). Coord: full diff read, sorry-grep clean, warning-clean rebuild + lint re-run green. Blueprint bit ✗: "no blueprint edit needed" claim missed `lem:case-III` PROOF-route staleness (\uses + "no cycle branch" prose) → row 663 fixup. |
| 663 | 23h A1 follow-up — `lem:case-III` blueprint route-sync (`daa76cea`) | 1/2/1 | sonnet | normal | clean | ✓✓—✓✓✓ | 171k tok / 56 tools / 12.2 min | Coordinator-detected divergence; sonnet-a2. High-quality: CORRECTED the coordinator's wrong pin (kept `lem:adjacent-degree-two-pair` — still live at the `\|V\|=3` triangle floor, Arms.lean:980, verified by grep) instead of force-following it; fixed both "no cycle branch" claims + off-route sibling caveat; lesson lifted to notes. Coord re-ran blueprint lint+verify green. First below-opus dispatch under map v2 this session: clean, zero repairs. |
| 664 | 23h A2 — general-`d` Thm 5.5 (`theorem_55_minimalKDof_gen`/`theorem_55_gen`, `faaa103f`) | 1/2/1 | opus | normal | clean | ✓✓✓✓✓✓ | 228k tok / 70 tools / 25.8 min | Zone producer build → opus min; built against the `435325ab` carry-map adjudication — faithful, additive, MILESTONE: general-`d` KT 5.5 axiom-clean (coord re-ran `#print axioms` independently). Good judgment: tried then REVERTED the `d=3`-wrapper collapse (would orphan 3 blueprint-pinned sub-producers) — logged as an orphan-sweep decide-item. Blueprint `thm:theorem-55` re-pin + general-`d` restate faithful. Coord: full diff, sorry-grep, build/lint/blueprint gates re-run green. |

## Findings

(accumulate episode bullets here; distill at each phase close per
the protocol)
