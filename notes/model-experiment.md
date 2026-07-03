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
  fable), no substitution — user-confirmed at the 2026-07-02 (Phase
  23-cleanup) session-start check-in; **addenda versions in effect:
  `haiku-a1` / `sonnet-a2`**; step-4 mechanical fixups (wrong branch /
  author / trailer) **pre-authorized**; check-in cap **LIFTED** (user,
  2026-07-02) — run until the round closes or a stop trigger. Active
  dispatch context: the **post-Phase-23 cleanup round**
  (`notes/Phase23-cleanup.md`) — its rows log in the live table below.
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
Rows 1–670 are in [`model-experiment-archive.md`](model-experiment-archive.md)
(1–189 grandfathered; 190–372 = Phase 23a + 23b; 373–434 = Phase 23c; 435–501 = Phase 23d;
502–514 = Phase 23e; 515–630 = Phase 23f; 631–660 = Phase 23g; 661–670 = Phase 23h +
the Phase-23 umbrella close). This live table holds only the **active phase's** rows
(successor not yet opened).

| # | Task | S/P/B | Model | Mode | Outcome | Rubric | Cost | Notes |
|---|---|---|---|---|---|---|---|---|
| 671 | 23-cleanup R0 — style spec → AUTHORING.md + intro.tex dep-graph note (`4ad3c58d`) | 1/1/2 | sonnet | normal | clean | —✓—✓✓✓ | 141k tok / 40 tools / 7.1 min | Content pre-written in the phase note (S=1); sonnet-a2. All 4 pinned sub-clauses delivered: AUTHORING.md *Audience & vocabulary* (8 rules + D2 dictionary verbatim-faithful to the owner-confirmed table), intro.tex one-para convention note, phase-note copy → pointer, ROADMAP cell → In progress. Good judgment: kept the R1 calibration sample in the note (it's R1's target, not style spec). Coord: full diff, lint.sh re-run green, gates attested w/ stash-and-rerun evidence. Docs-only. |
| 672 | hfresh repair design recon — route verdict + signatures + spiked satisfiability (`978d95fc`) | 3/2/2 | fable | design-pass | clean | —✓—✓✓✓ | 207k tok / 49 tools / 20.3 min | Design-settle (fable-mapped) on the coordinator's kernel-checked vacuity finding. Excellent: census of the 3 real application sites (coord re-verified exhaustively — exact), corrected the coord's own stale "E(G)∪{e₀} helper graph" claim, minimality-conditioned 2-tier route w/ exact signatures ×15 decls, BOTH satisfiability lemmas spiked green, [Finite β] route-1 kill grounded in `matroidMG_indep_iff`+vendored union (coord re-verified), 22a seam cleared, README/home_page honesty clauses landed. F1–F3 sized. Docs-only. |
| 673 | hfresh F1 — the two-tier binder reshape across 6 carrier files (`0add5877`) | 1/2/2 | sonnet | normal | clean | ✓✓✓✓✓✓ | 290k tok / 112 tools / 16.9 min | Zone files, mechanical statement reshape → stays mapped; sonnet-a2. Verbatim match to the §Verdict pin (coord diffed every hfresh line): Tier-1 per-graph ∃ on the 5 leaves + Tier-2 minimality-conditioned ∀ on driver + 10-decl spine family (incl. literal-3 form), 3 app sites + 2 split-arm instantiations + call-site reorders, docstrings + 4 blueprint chapters restated (single-body prose correctly re-derived from E(G)=∅). Coord: full diff, sorry-grep, touch+full rebuild warning-clean, lake lint + blueprint lint re-run green. |
| 674 | hfresh F2 — satisfiability lemmas + Nonvacuity.lean witness + clause removal (`45c25667`) | 1/2/2 | sonnet | normal | clean | ✓✓✓✓✓✓ | 299k tok / 169 tools / 26.3 min | Spiked proofs pre-written (S=1); sonnet-a2. Both Deficiency.lean lemmas verbatim to pin; witness file = the regression cert (molecular_conjecture FULLY APPLIED at singleEdge on Fin 2/Fin 7 — sanctioned cosmetic upgrade from the "literal graph" plan); root import added; README/home_page/ROADMAP honesty clauses dropped; blueprint remark landed. Filed a real QUIRKS §74 (decide passes in lean_run_code but fails lake build on Nat.card (Fin n); fix Nat.card_fin-first). Coord: full diff, sorry-grep, touch+full rebuild warning-clean, both lints re-run green. |
| 675 | hfresh F3 — arc close-out: design-doc compression + S1 flip + 22a reword (`3dbcd66a`) | 1/1/2 | sonnet | normal | clean | ——✓—✓✓ | 105k tok / 36 tools / 5.0 min | Docs-only; sonnet-a2. Design doc 373→10 lines (verdict + git pointer, per notes/CLAUDE.md live-recon rule); S1 flipped w/ resolution record; 22a:440 reworded with a SOUND replacement argument (β:=E(G) forces E(G)=univ at the minimal ambient graph — coord verified the logic); hand-off → R1 against the repaired statements. Nit: hand-off says "S2/S3" where R1's task entry correctly scopes S2 (S3 is R2's) — task entry authoritative, no fixup. |
| 676 | R1a/S2 — collapse the d=3-only Thm-5.5 producer spine (`2fa541f5`) | 2/2/2 | sonnet | normal | repaired | ✓✓✓✓✓✓ | 302k tok / 90 tools / 21.4 min | Zone file, mechanical collapse → stays mapped; sonnet-a2. Decision + execution sound: 3 thin k=2 wrappers deleted, `theorem_55_minimalKDof_k` → `_gen (k:=2)` corollary, 2 blueprint pins re-pointed, gates green. BUT the supersession sweep missed CROSS-FILE residue: 3 stale docstring refs (PanelLayer, GenericityDevice — one claiming the deleted decl "kept") + 1 orphaned wrapper (`exists_extensor_in_two_panels`, zero consumers, unpinned). Coord deletion-check caught it → row 677 follow-up. First below-opus repaired outcome under map v2 (surfaced to user per trial discipline). |
| 677 | S2 follow-up — orphan wrapper + stale docstring sweep (`506fba5a`) | 1/1/1 | haiku | normal | repaired | ✓✓✗✓✓✓ | 69k tok / 20 tools / 14.9 min | Coordinator-specified 3-edit fixup; haiku-a1. All 3 edits exact, note entry filed, gates attested w/ pasted output (coord re-ran all: warning-clean + both lints). Quality ✗: the rewrap dropped "to" in "transfers to any fresh seed" — a one-word prose regression the coord's full-diff read caught and fixed in `434f5bea`. Rails held otherwise (no improvisation, no scope creep). |


## Findings

(accumulate episode bullets here; distill at each phase close per
the protocol)
