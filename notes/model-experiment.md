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
grandfathered **rows 1–189**, the **Phase 23a–23h rows 190–670** (with their
session-close config notes + *Findings* close-outs, incl. the **23h rows
661–670**), and the **closed-phase *Findings*** (Phase 22h–22l + post-22j
perf). This live file keeps only the config, the **active phase's** rows
(Phase 23 closed 2026-07-02; **successor not yet opened**, no rows), and
active-phase *Findings*, so the coordinator's every-dispatch read stays small. **When a
(sub-)phase closes, move its rows + its *Findings* close-out + its session-close
config bullet here** in the same close-out cleanup — a project phase-close
checklist item (`PHASE-BOUNDARIES.md` *When this commit closes a phase*); 23b
closed 2026-06-21 without it and the rows went stale (cleaned up 2026-06-22).

## Repo-local config

- **Testbed:** the molecular program. **Phase 23 CLOSED 2026-07-02**
  (the Molecular Conjecture, `molecular_conjecture`, formalized at general
  `d`); the successor (Phase 24, per `notes/MolecularConjecture.md`) is
  **not yet opened**. Phase status / next-step live in the ROADMAP cell +
  `notes/MolecularConjecture.md`, **not here**. Continues into successor
  phases until concluded.
- **Rungs:** haiku → sonnet → opus → fable (the Agent tool's `model` param).
- **Coordinator hook:** `.claude/commands/coordinate-phase.md` model-tier
  step, conditional on this file's Status.
- **Phase-side pointer:** `notes/MolecularConjecture.md` (the program map;
  Phase 24 planning) + `notes/Phase23h.md` *Hand-off* (the Phase-23 close
  record). `notes/Phase23-design.md` is frozen as the §-cited archive.
- **Attribution:** top-level `CLAUDE.md` *Working* → *Commit attribution*
  (exact author string + actual-model trailer).
- **Log-row length gate:** `notes/check-log-rows.py` enforces the protocol's
  ~600-char Notes cap. Run it before committing a log row (default mode checks
  only the rows this commit touched); it is wired into the coordinate-phase
  per-commit step. `--all` audits the whole (live) table; the closed phases'
  rows (1–717) now live in the archive (frozen, not gated).
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
- **Per-session run modifications (2026-07-06 session; expire at this
  session's close):** user-confirmed at the session-start check-in —
  **all four rungs available** (no substitutions), **run cap lifted**,
  **mechanical fixups pre-authorized** (rescue §1 applied without
  per-instance asks). **Addenda versions in effect: `haiku-a1` /
  `sonnet-a2`.** Active dispatch context: **Phase 24** (opened
  2026-07-06, row 718; next step per `notes/Phase24.md` *Hand-off*).
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
Rows 1–717 are in [`model-experiment-archive.md`](model-experiment-archive.md)
(1–189 grandfathered; 190–670 = Phases 23a–23h + the umbrella close; 671–717 = the
post-Phase-23 cleanup round, closed 2026-07-05). This live table holds only the
**active phase's** rows (successor not yet opened).

| # | Task | S/P/B | Model | Mode | Outcome | Rubric | Cost | Notes |
|---|---|---|---|---|---|---|---|---|
| 718 | Phase-24 open — `bar-joint-3d.tex` chapter + `notes/Phase24.md` + surfaces (`bca7b32c`) | —/—/— | fable | normal | clean | —✓—✓✓✓ | 224k tok / 59 tools / 14.5 min | Phase-open commit (fable-mapped). Full open checklist delivered (coord verified: 8-red-node forward-mode chapter, `\uses` resolve to live Phase-4/8 nodes, no premature `\leanok`; ROADMAP row+§24+layout; README/home_page/intro.tex + MolecularConjecture synced; `jacksonJordan2008` DOI-verified; Phase24.md forward-weighted w/ concrete next step; KT §7 scope guard restated; 25/26 not opened; dead-code sweep recorded as not-this-phase). blueprint lint+verify attested green. |
| 719 | P24 leaf pair — `IsGenericPlacement` + `exists_isGenericPlacement`, new `GenericRigidityMatroid.lean` (`0d67ff50`) | 2/2/2 | sonnet | normal | clean | ✓✓✓✓✓✓ | 174k tok / 55 tools / 81 min | sonnet-a2. Faithful general-`d` lift of the Phase-8 interpolation induction w/ definitional `∃ q` witnesses; sorry-grep 0; coord re-ran touch+build (warning-clean) + `lake lint`; full diff read. Nodes flipped green; hand-off re-pointed. Soft helper-extraction deferred w/ a rationale the coord source-verified (`EdgeSetRowIndependent` home forces the shared core upstream → import-graph call, correctly not same-commit). 81-min wall but modest tok/tools; no degradation signals. |
| 720 | P24 matroid trio — `genericRigidityMatroid` + `_indep_iff` + placement independence (`daa9efc3`) | 1/2/1 | sonnet | normal | clean | ✓✓✓✓✓✓ | 135k tok / 41 tools / 6.4 min | sonnet-a2. Clean `Matroid.ext_indep` plumbing reproducing the Phase-8 identification shape; 3 nodes flipped green (5/8 total), each Lean statement diffed against its blueprint node — exact match. sorry-grep 0; coord re-ran touch+build (warning-clean) + `lake lint`; full diff read. Hand-off re-pointed to the dim-2 reconciliation w/ a sharpened route (both `Indep` predicates already ∃-form). Rank-carrier question correctly kept open for the rank commit. |
| 721 | P24 dim-2 reconciliation — `genericRigidityMatroid_two_eq_rigidityMatroid` (`8264bfd6` + coord fixup `43fce731`) | 1/1/1 | haiku | normal | repaired | ✓✓✓✗✗✗ | 68k tok / 29 tools / 3.2 min | haiku-a1. Lean correct + clean (sorry-grep 0; coord re-ran build warning-clean + lint — return pasted NO gate output despite a1's explicit rail). Three discipline misses, all coord-repaired in `43fce731`: forward-mode blueprint flip omitted (node left red while the note claimed "six green"), hand-off rewrite garbled the rank route ("follow Phase 8's `_eq_rigidityMatroid` rank pattern" — Phase 8 exposed no rank API), `log(` commit prefix. Math layer fine at 1/1/1; the discipline layer again the failure locus (cf. rows 713/715). |


## Findings

(accumulate episode bullets here; distill at each phase close per
the protocol)
