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
718–723**, and the **Phase 25 rows 724–739** (each with session-close
config notes + *Findings* close-outs), plus the **closed-phase
*Findings*** (Phase 22h–22l + post-22j
perf). This live file keeps only the config, the **active phase's** rows
(Phase 25 closed 2026-07-07; **successor not yet opened**, no rows), and
active-phase *Findings*, so the coordinator's every-dispatch read stays small. **When a
(sub-)phase closes, move its rows + its *Findings* close-out + its session-close
config bullet here** in the same close-out cleanup — a project phase-close
checklist item (`PHASE-BOUNDARIES.md` *When this commit closes a phase*); 23b
closed 2026-06-21 without it and the rows went stale (cleaned up 2026-06-22).

## Repo-local config

- **Testbed:** the molecular program. **Phase 25 CLOSED 2026-07-07**
  (projective duality + molecule modelling equivalence, all 12
  `molecule-modelling.tex` nodes green across two sessions, rows
  724–739); the successor (Phase 26, Cor 5.7, per
  `notes/MolecularConjecture.md`) is **not yet opened**. Phase status /
  next-step live in the ROADMAP cell + `notes/MolecularConjecture.md`,
  **not here**. Continues into successor phases until concluded.
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
- **Per-session run modifications (2026-07-07 session,
  user-confirmed at the session-start check-in):** all four rungs
  available (no substitutions); the run cap is lifted (run to phase
  close or a genuine stop-trigger); mechanical fixups (rescue §1)
  pre-authorized. These expire at this session's close. **Addenda
  versions in effect: `haiku-a1` / `sonnet-a2`.** Active dispatch
  context: the first dispatch is the **Phase-26 open** (fable per the
  map's phase-open cell; contract in `notes/Phase25-design.md`
  §2.2/§2.6).
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
Rows 1–739 are in [`model-experiment-archive.md`](model-experiment-archive.md)
(1–189 grandfathered; 190–670 = Phases 23a–23h + the umbrella close; 671–717 = the
post-Phase-23 cleanup round; 718–723 = Phase 24; 724–739 = Phase 25, opened
2026-07-06, closed 2026-07-07). This live table holds only the **active
phase's** rows (successor not yet opened).

| # | Task (commit) | S/P/B | Model | Mode | Outcome | Rubric | Cost | Notes |
|---|---|---|---|---|---|---|---|---|
| 740 | Phase-26 open — Cor 5.7 capstone: forward-mode chapter `molecule-application.tex` (5 red nodes) + `notes/Phase26.md` + surfaces sync (`24431f27`) | —/—/— | fable | normal | clean | —✓—✓✓✓ | 227k tok / 77 tools / 20.0 min | Phase-open commit (fable-mapped). Full open checklist delivered (coord verified: ROADMAP row 26 ◐ + §26; README/home_page/intro.tex + MolecularConjecture synced; chapter follows the §2.2/§2.6 plan — glue/carrier/≥/≤/Cor nodes). F4 pinned honestly as first-leaf decision w/ recon findings (no SimpleGraph→Graph bridge in mathlib/repo; `Sym2 V` fails `hcard`, padded β needed; canonical-carrier recommended). Red-node gate + verify.sh + lint.sh attested green; docs-only, no Lean. |
| 741 | P26 genericRank domination leaf — `finrank_span_rigidityRow_le_genericRank`, closes `lem:square-rank-le-genericRank` (`19fe492e`) | 2/2/1 | sonnet | normal | clean | ✓✓✓✓✓✓ | 173k tok / 58 tools / 9.6 min | Sonnet-mapped (max=2; not fragility zone — `GenericRigidityMatroid.lean`). Self-shrank the "leaf pair" hand-off to one complete leaf (sanctioned scope-to-fit); carrier leaf re-flagged next. Statement matches the pinned node; `\uses` trim justified (proof needs neither dropped dep). Coord re-ran: sorry-grep clean, touch+rebuild warning-clean, `lake lint` green; full diff read — clean route via `rk_le_iff` + `genericRigidityMatroid_indep_iff`. a2 addendum honored (foreground gates). |
| 742 | P26 F4 carrier — `SimpleGraph.shadowGraph` (padded `Sym2 V ⊕ Fin (6(n−1)+1)` labels), closes `lem:molecule-graph-carrier` existence half, new `Molecule/Carrier.lean` (`0b804d99`) | 2/2/1 | sonnet | normal | clean | ✓✓✓✓✓✓ | 263k tok / 114 tools / 23.5 min | Sonnet-mapped (max=2; additive new file, not zone). Delivered the pinned F4 canonical carrier (Simple/spanning/isLink↔Adj/`hcard`) exactly; the pin's deficiency-invariance clause honestly demoted to a non-`\leanok` blueprint remark + re-flagged (coord accepted: not load-bearing — both rank legs fix this one carrier). Coord re-ran: sorry-grep clean, rebuild warning-clean, lint green; full diff read. Hand-off flagged the `hends` slot check → coord slot-trace (`aba6656f`). |
| 743 | P26 attainment leg — `molecule_rank_lower_bound` closes `lem:molecule-rank-lower-bound`; `hends` conjunct added to the P25 producer + `rigidityRow_congr` / `finrank_range_rigidityMap_le_genericRank` bridges (`6cc83b01`) | 1/2/2 | sonnet | normal | clean | ✓✓✓✓✓✓ | 297k tok / 114 tools / 26.1 min | Sonnet-mapped (max=2; S=1 after coord slot-trace `aba6656f` pasted the exact fix + bridge chain). Implemented the trace verbatim: statement-strengthened `exists_molecular_rankHypothesis_generalPosition` w/ the pinned `thm:panel-hinge-iff-molecular` node restated same-commit (per-slice gate honored); `[Nonempty V]` flagged in blueprint prose. Coord re-ran: sorry-grep clean, 4 touched modules rebuilt warning-clean, `lake lint` + blueprint lint.sh green; full diff read. 1 QUIRKS §77 + FRICTION idioms. |
| 744 | P26 upper-bound leg — `molecule_rank_upper_bound` closes `lem:molecule-rank-upper-bound`; hand-built `ends` selector + `lineExtensor_ne_zero_of_ne` + eq-sibling `finrank_range_rigidityMap_eq_genericRank` (`5d2af9a8`) | 1/2/2 | sonnet | normal | clean | ✓✓✓✓✓✓ | 308k tok / 96 tools / 25.5 min | Sonnet-mapped (S=1 after coord slot-trace `3daa84ba` — the dual `hends`+`hC` selector obligation incl. padding labels). Route as traced: never-linked labels get a fixed distinct pair from `hmin`; domination lemma cleanly refactored into a private shared helper + le/eq siblings. Coord re-ran: sorry-grep clean, rebuild warning-clean, `lake lint` + blueprint lint.sh green; full diff read. Only `cor:molecule-rank-formula` remains. |


## Findings

(accumulate episode bullets here; distill at each phase close per
the protocol)

(none yet — Phase 25's close-out, rows 724–739, is in the archive;
no successor-phase rows.)
