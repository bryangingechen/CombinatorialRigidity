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
**post-Phase-23 cleanup-round rows 671–717**, and the **Phase 24 rows
718–723** (each with session-close config notes + *Findings* close-outs),
plus the **closed-phase *Findings*** (Phase 22h–22l + post-22j
perf). This live file keeps only the config, the **active phase's** rows
(Phase 24 closed 2026-07-06; **successor not yet opened**, no rows), and
active-phase *Findings*, so the coordinator's every-dispatch read stays small. **When a
(sub-)phase closes, move its rows + its *Findings* close-out + its session-close
config bullet here** in the same close-out cleanup — a project phase-close
checklist item (`PHASE-BOUNDARIES.md` *When this commit closes a phase*); 23b
closed 2026-06-21 without it and the rows went stale (cleaned up 2026-06-22).

## Repo-local config

- **Testbed:** the molecular program. **Phase 24 CLOSED 2026-07-06**
  (the 3-D generic bar-joint rigidity matroid, `bar-joint-3d.tex` fully
  green in one session); the successor (Phase 25, per
  `notes/MolecularConjecture.md`) is **not yet opened**. Phase status /
  next-step live in the ROADMAP cell + `notes/MolecularConjecture.md`,
  **not here**. Continues into successor phases until concluded.
- **Rungs:** haiku → sonnet → opus → fable (the Agent tool's `model` param).
- **Coordinator hook:** `.claude/commands/coordinate-phase.md` model-tier
  step, conditional on this file's Status.
- **Phase-side pointer:** `notes/MolecularConjecture.md` (the program map;
  Phase 25 planning) + `notes/Phase24.md` *Hand-off* (the Phase-24 close
  record). `notes/Phase23-design.md` is frozen as the §-cited archive.
- **Attribution:** top-level `CLAUDE.md` *Working* → *Commit attribution*
  (exact author string + actual-model trailer).
- **Log-row length gate:** `notes/check-log-rows.py` enforces the protocol's
  ~600-char Notes cap. Run it before committing a log row (default mode checks
  only the rows this commit touched); it is wired into the coordinate-phase
  per-commit step. `--all` audits the whole (live) table; the closed phases'
  rows (1–723) now live in the archive (frozen, not gated).
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
- **Per-session run modifications (2026-07-06 second session; expire at
  this session's close):** user-confirmed at the session-start check-in —
  **all four rungs available** (no substitutions), **run cap lifted**,
  **mechanical fixups pre-authorized** (rescue §1 applied without
  per-instance asks); same config as the earlier 2026-07-06 session
  (rows 718–723). **Addenda versions in effect: `haiku-a1` /
  `sonnet-a2`.** Active dispatch context: the **Phase-25 open**
  (`notes/MolecularConjecture.md` *Opening the next phase*).
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
Rows 1–723 are in [`model-experiment-archive.md`](model-experiment-archive.md)
(1–189 grandfathered; 190–670 = Phases 23a–23h + the umbrella close; 671–717 = the
post-Phase-23 cleanup round; 718–723 = Phase 24, opened and closed 2026-07-06).
This live table holds only the **active phase's** rows (successor not yet
opened).

| # | Task | S/P/B | Model | Mode | Outcome | Rubric | Cost | Notes |
|---|---|---|---|---|---|---|---|---|
| 724 | Phase-25 open — `molecule-modelling.tex` chapter + `notes/Phase25.md` + surfaces (`5080a1ec`) | —/—/— | fable | normal | clean | —✓—✓✓✓ | 204k tok / 63 tools / 13.2 min | Phase-open commit (fable-mapped). Full open checklist delivered (coord verified: 6-red-node forward-mode chapter, `\uses` resolve to live Phase-4/16/21/24 nodes, no premature `\leanok`; bib keys `crapoWhiteley1982`/`whiteley1999`/`jacksonJordan2008` all pre-existing; ROADMAP row 25 split + §25; README/home_page/intro.tex + MolecularConjecture synced; single-integer-phase + design-recon-first decision recorded; Phase 26 NOT opened). blueprint lint+verify attested green. Hand-off: layer-level recon → `notes/Phase25-design.md` (OD-25-1/OD-25-2). |
| 725 | Phase-25 layer design recon — rank-level chain + transport-form proj. invariance (`86337025`) | —/—/— | fable | normal | clean | —✓—✓✓✓ | 314k tok / 82 tools / 29.4 min | Design-settle (fable-mapped). OD-25-1: formalize as extensor-transport (`mapExtensor`; polarity already in tree, `panelSupportExtensor = complementIso ∘ normalsJoin`). OD-25-2: rank-level dictionary Φ (iff-level would drag in 2 more JJ papers). Leaves W1–W7, chapter re-cut 6→12 red nodes; cite-fallback framing purged per user directive (mid-flight SendMessage). Coord verified all key anchors at source (Theorem55:2840, PanelLayer:2083, GenericityDevice:718/1303/1396, GenericRigidityMatroid:49/67/241); orphan check clean. |
| 726 | P25 W3 — `SimpleGraph.square` + closed-nbhd clique lemmas, new `SquareGraph.lean` (`34d2184f`) | 2/2/1 | sonnet | normal | clean | ✓✓✓✓✓✓ | 256k tok / 91 tools / 18.8 min | sonnet-mapped (max=2; outside fragility zone; addendum a2). All 4 pinned W3 items delivered (square def, clique + covering lemmas, min-degree transfer); 2 nodes green, pins match decls; `ncard_neighborSet_eq_degree` mirror + QUIRKS §75 lift (friction review done). Coord re-ran full build (warning-clean) + `lake lint` green; sorry-grep clean; hand-off honestly re-pointed at W2/W5. |
| 727 | P25 W2 — extensor transport (`mapExtensor` family + W2c rescaling), new `Molecule/ProjectiveInvariance.lean` (`78b78dbd`) | 1/2/1 | opus | normal | clean | ✓✓✓✓✓✓ | 235k tok / 64 tools / 20.1 min | Opus via fragility-zone modifier (ScrewSpace-carrier producer; profile alone → sonnet). All §1.2 pinned shapes delivered verbatim (motions `map` identity, finrank/RankHyp/rigid{,On}/genuine-hinge transfer, `scaleExtensor`); `thm:projective-invariance` green. Non-module file (imports non-module `Pinning.lean`) — reasonable, flagged. FRICTION [idiom] on T-form iff transports. Coord re-ran build (warning-clean) + lint green; sorry-grep clean. |
| 728 | P25 W5 — `IsGeneralPositionPlacement` + strengthened generic existence, new `GeneralPositionPlacement.lean` (`972ba5f1`) | 1/3/1 | sonnet | normal | clean | ✓✓✓✓✓✓ | 266k tok / 81 tools / 19.8 min | Boundary cell S=1/P=3 (exact §2.5 def + named route; outside zone; addendum a2) — clean, cell data point. Def verbatim to pin; moment-curve Vandermonde witness + `V ⊕ Fin 4` padding (builder's-choice packaging, sanctioned [design]); dual-cofinite interpolation for generic∧GP. 2 nodes green. Coord re-ran build (warning-clean) + lint green; sorry-grep clean; hand-off → W1 crux. |
| 729 | P25 W1 (bricks 1–3) — screw-velocity API, new `Molecule/ScrewVelocity.lean` (`21d0178b`) | 2/3/1 | opus | normal | clean | ✓✓✓✓✓✓ | 322k tok / 83 tools / 36.6 min | Opus-mapped (P=3 w/ S=2; ScrewSpace producer). `screwVel`/`screwOmega`/`screwTau` via graded Plücker pieces, line formula, bricks (1) skew + (2) line char + (3) kill, `screwCoord_injective`. Scope-to-fit shrink sanctioned: brick (4) ∃!-determination deferred with tracking artifact (`lem:screw-determination` stays red; hand-off names 2 routes incl. F2 triangle-rank). 2 nodes green; axioms clean. Coord re-ran build (warning-clean) + lint green; sorry-grep clean. |
| 730 | P25 W1 brick (4) — `existsUnique_screwVel_eq` (∃!-determination), `lem:screw-determination` green (`b7ba0bf4`) | 2/3/1 | opus | normal | clean | ✓✓✓✓✓✓ | 370k tok / 76 tools / 45.7 min | Opus-mapped (P=3 w/ S=2; ScrewSpace producer). Existence via the cross-product `ω`-construction (F2 route 2 — no triangle-rank lemma needed): `exists_crossProduct_eq` crux + triangle then family form; uniqueness from landed bricks. Blueprint proof prose re-described to the built route, statement shape intact (coord checked vs §2.3(4)). 3 FRICTION idioms (`⨯₃` glyph trap etc.). W1 fully green. Coord re-ran build (warning-clean) + lint green; sorry-grep clean; hand-off → W4. |
| 731 | P25 W4 slice 1 — `molecularOfCentres` + Φ (`molecularVel`) + well-definedness, new `Molecule/Dictionary.lean` (`78df6035`) | 2/3/1 | opus | normal | clean | ✓✓✓✓✓✓ | 291k tok / 67 tools / 25.9 min | Opus-mapped (W4 crux; ScrewSpace producer). `molecularOfCentres = ofHinge` at endpoint centres (matches §2.3 pin — coord checked), Φ as `→ₗ`, `molecularVel_mem_ker` via W3 covering + bricks (1)/(2); F3 PiLp glue resolved (`euclidean_inner_eq_dotProduct`). `def:hinge-concurrent` green; `thm:molecular-iff-square-bar-joint` stays red, hand-off re-pointed at slice 2 (inj → surj → finrank) w/ per-step signatures. Coord re-ran build (warning-clean) + lint green; sorry-grep clean. |
| 732 | P25 W4 slice 2 — Φ inj + surj + finrank, `thm:molecular-iff-square-bar-joint` green (`a7301f44`) | 1/3/1 | opus | normal | clean | ✓✓✓✓✓✓ | 324k tok / 90 tools / 40.7 min | Opus-mapped (W4 crux; per-step signatures in hand-off gave S=1). Injectivity (min-deg-2 + GP + brick 3), surjectivity (per-`N[v]` ∃! screws via brick 4, `choose`-assembled), capstone finrank equality via `LinearEquiv.ofBijective` — statement matches §2.6 pin exactly (coord diffed). GP→LI bridge family added to `GeneralPositionPlacement.lean`. `Dictionary.lean` module→non-module conversion (consumes non-module GP file) — flagged, consistent w/ W2 precedent. Axiom-clean. Coord re-ran build (warning-clean) + lint green; sorry-grep clean; hand-off → W6/W7. |


## Findings

(accumulate episode bullets here; distill at each phase close per
the protocol)
