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
- **Per-session run modifications (2026-07-03 checkpoint-#4 session;
  expire at session close):** user-confirmed at the session-start
  check-in — all four rungs available; run cap lifted; mechanical
  fixups (rescue §1) pre-authorized. Checkpoint-#4 verdict: defects —
  the 11-item owner review (row 688; dispositions pending discussion). **Addenda versions in
  effect: `haiku-a1` / `sonnet-a2`.** Active dispatch context: the
  **post-Phase-23 cleanup round** (`notes/Phase23-cleanup.md`) — its
  rows log in the live table below.
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
| 678 | R1b — headline-family prose rewrite, panel-layer.tex (`a85e849c`) | 2/2/2 | sonnet | normal | clean | —✓—✓✓✓ | 293k tok / 88 tools / 23.0 min | Calibration prose; sonnet-a2. Matches the owner-approved sample nearly verbatim; node split delivered (main + cor:theorem-55-d3-spanning); rule-8 honesty spot-checked by coord (HasPanelRealization rank = D(|V|−1)−def, def=0 at minimal 0-dof → "maximal rank" honest; n≥3 ⟺ D≥6 arithmetic checks); general-d Formalization note documents the repaired supply correctly. Good scope-to-fit: infrastructure nodes explicitly re-flagged, not half-done. Coord: full diff, verify.sh(+checkdecls)/lint.sh re-run green. Docs-only. |
| 679 | R1c — infrastructure-node sweep closes R1 (`0c1a9b37`) | 2/2/2 | sonnet | normal | clean | —✓—✓✓✓ | 312k tok / 104 tools / 17.6 min | Sonnet-a2. def:rank-hypothesis, lem:theorem-55-base, 4 base-producer nodes to Target style; correctly parked at the owner checkpoint (did NOT open R2). Coord post-sweep vocab grep: prose clean — residual "producer" hits are all \label/\uses/\cref node IDs (invisible in render; P1's lint gate must whitelist those lines). Coord: full diff, verify.sh/lint.sh re-run green. Docs-only. RETRO (owner review): NOT at target level — commentary-in-statements + \mathtt survived; the "molecular-conjecture already compliant" verdict was WRONG → v2 rules + opus escalation (row 680). |
| 680 | R1d — calibration-v2 revision, chapter-wide + overview preamble (`4a66d820`) | 2/2/2 | opus | escalation | clean | —✓—✓✓✓ | 228k tok / 63 tools / 23.8 min | Escalated from sonnet after the owner review (2 sonnet passes under-delivered on altitude; 1 wrong audit verdict). All 6 owner defect points fixed (coord verified each): statement purity (molecular-conjecture reduced to the bare iff; V(G)-relative essay → rem:rank-hypothesis-relative), 46 KT-prefixed refs, Lean-syntax/`B1` purged from notes, connective prose, multi-paragraph proofs, single rem:fresh-edge-supply w/ all mentions pointing at it; algebraic-induction.tex preamble → jargon-free roadmap. verify.sh + lint.sh re-run green. Parked at owner checkpoint #2. Docs-only. |
| 681 | E1 — consumer-surface ergonomics design-settle (`ebba0c91`) | 3/2/2 | fable | design-pass | clean | —✓—✓✓✓ | 183k tok / 37 tools / 13.8 min | Design-settle (fable-mapped; owner-adjudicated direction). Exemplary pin: per-decl census w/ pins+callers (13 decls: 5 reshapes, 2 deletions incl. theorem_55_all_k-merges-into-theorem_55_d3, engine untouched), arithmetic traced to landed defs (3≤n ⟺ hD; k=n−1 via landed bridge), type-level ℕ-subtraction verdict COMPILE-SPIKED incl. witness defeq (3−1 ≡ 2 exact-closes), 2 helper lemmas spiked w/ proofs + homes, E.5 blueprint touch-points enumerated (statements untouched — rule 13 paid off), E2/E3 leaves sized w/ done-gates. Coord re-verified callers + pin-locality. Docs-only. |
| 682 | E2 — the consumer-surface reshape build (`33d6b2a6`) | 1/2/2 | sonnet | normal | clean | ✓✓✓✓✓✓ | 363k tok / 103 tools / 39.4 min | Zone file, spiked reshape → stays mapped; sonnet-a2. Verbatim to §E.3 (coord byte-checked the headline sig): 5 reshapes, both deletions complete (coord grep: 0 pins, 0 live refs; docstring mentions = E3 as planned), Nonvacuity restated, 7 tex touch-points. ONE forced deviation, handled exemplarily: the sub-one bridge home → PanelLayer.lean (pinned home is `module`, can't import non-module Framework.lean) — recorded as a §E landed-delta + FRICTION entry, not a silent rewrite. Coord: full diff, sorry-grep, full rebuild warning-clean, all 4 gates re-run green. |
| 683 | E3 — the theorem_55_all_k docstring sweep (`5f635f02`) | 2/1/2 | sonnet | normal | clean | ✓✓✓—✓✓ | 242k tok / 145 tools / 16.8 min | Sonnet-a2. 24 mentions / 10 files re-pointed with per-site role judgment (spine-shape → theorem_55_minimalKDof_k_all_k, public-instance → theorem_55_d3, 2 judged exceptions); done-gate 0 hits (coord re-ran); diff verified comment-only; build + lint green (coord re-ran). Closes the E-arc; round parked at owner checkpoint #2. Tool-count high-ish for a comment sweep but within norm for 10-file breadth. |
| 684 | R1e — calibration-v3 revision of the R1 page (`4a6597cc`) | 2/2/2 | opus | escalation | clean | —✓—✓✓✓ | 274k tok / 59 tools / 24.2 min | Escalation held from row 680 (3rd altitude iteration on this chapter). All checkpoint-#2 defects fixed (coord verified each vs the recorded list): register flattened vs KT's own prose; 5 over-pinned nodes split to ≤3 pins via 7 new sibling nodes, labels retained; Formalization notes moved outside defs; Whiteley 1-extension cite coord-verified vs KT p.4 PDF ([33]=Whiteley 1996 Thm 2.2.2). Coord re-ran verify.sh+lint.sh green. One residual (corollary title "feeds", bare KT numbers) → coord follow-up `1ccb9d72`. Docs-only; parks at checkpoint #3. |
| 685 | KT-style statement review, opus lens (read-only) | — | opus | recon | clean | — | 110k tok / 12 tools / 9.2 min | Diverse-lens pair member (protocol's named opus-vs-fable comparison; owner checkpoint-#3 signal "declarations too prose-y"). Read KT §§1,2,5,6.1–6.2 + all 33 nodes. Verdict: flagships clean, 21/33 supporting nodes carry situating/comparison/construction/Lean-name content rules 1–16 miss. Sharpest on category taxonomy, standalone test, attribution carve-outs (JJ/TW-KT stay). 6 before→after samples. Folded into rule 17 (`db6c32ae`). |
| 686 | KT-style statement review, fable lens (read-only) | — | fable | recon | clean | — | 101k tok / 13 tools / 6.1 min | Pair member. Same corpus, independent. Verdict: 24/33 nodes flagged, same worst list as opus (6 severe, 2 with proofs duplicated inside statements). Sharpest on statement shape (Let/Suppose/Then, 1–4 sentences, the trailing "This is…" tell, deletion test) + an honesty flag on theorem_55_base's strength (coord resolved vs Pinning.lean:777 — pinned as conditional, not existence; pinned into the R1f list). PAIR FINDING: verdicts materially identical at ~equal cost; fable ~35% faster. Folded into rule 17 (`db6c32ae`). |
| 687 | R1f — rule-17 statement-surgery pass (`059f344d`) | 1/2/2 | opus | escalation | clean | —✓—✓✓✓ | 258k tok / 65 tools / 24.6 min | Map says sonnet at S=1 (per-node work list); held at opus — 4th owner round-trip costs more than the rung delta, and register-composition of moved prose is the dimension sonnet twice under-delivered here. Verbatim to the work list (coord full-diff-checked all 3 tiers + do-not-touch); honesty pin honored (theorem_55_base restated as the exact conditional; coord re-checked vs Pinning.lean:777); annotations untouched (coord grep); residual "This is" hits all in sanctioned homes (coord swept). Coord re-ran verify.sh+lint.sh green. Docs-only; parked at checkpoint #4. |
| 688 | checkpoint-#4 recon — 11 owner notes vs the R1f page (read-only) | — | fable | recon | clean | — | 200k tok / 33 tools / 14.0 min | Owner checkpoint #4: 11 notes (math-clarity + writing). Recon mapped all to labels, grounded vs Lean + KT PDF. 2 math-fidelity finds coord-verified: proofs of 23.12/23.14 mis-group the cut edge under Case II (wrong cref, missing uses-edges; the Lean combinator has KT's 4 arms); rankHypothesis_of_theorem_55_d3 = un-rebased duplicate of _gen (the S2 shape). Vocab (honest/re-aim/genuine/parallel) + note over-production → 4 candidate v5 rules + dictionary rows; 3 items owner-decision (6 infra, 9a Lean-first, 10 statement shape). Dispositions pending discussion. |
| 689 | 23-cleanup v5 — A–F consolidation of AUTHORING.md (`50736861`) | 2/2/2 | opus | normal | clean | —✓—✓✓✓ | 168k tok / 24 tools / 18.7 min | Consolidation rewrite per the adjudicated A–F pin (held at opus: the durable spec, on the register surface sonnet twice under-delivered). Coverage sweep delivered — coord spot-checked all 17 rules + 4 candidates traceable into A–F/footer; dictionary +5 rows incl. the honesty-gate manual carve-out; historical rule-N pointer added. Two judged deviations, both sound: 126 lines vs pinned ~90–100 (held for coverage, the named failure mode); the unverified KT §2.3 pointer omitted from the genuine row (deferred to R1g per hand-off). Coord re-ran lint.sh green; full diff read. Docs-only. |
| 690 | 23-cleanup 9(a) — rankHypothesis_of_theorem_55_d3 collapse (`643188b7`) | 1/2/2 | sonnet | normal | clean | ✓✓✓✓✓✓ | 220k tok / 44 tools / 11.5 min | Zone file, pinned + spiked collapse → stays mapped; sonnet-a2. Signature byte-identical (coord diffed old vs new decl); delegation exactly per pin (norm_num + simpa bodyBarDim + literal Nat.sub defeq, no cast); ~155-line duplicate body deleted; docstring rewritten, role + KT cite kept. Residue sweep delivered this time (the row-676 lesson): repo-wide grep clean, blueprint pin survives untouched; BlueprintExposition R2 seed verbatim to hand-off; ROADMAP cell refreshed. Coord: full diff, sorry-grep, touch + module rebuild warning-clean, lake lint re-run green. |


## Findings

(accumulate episode bullets here; distill at each phase close per
the protocol)

- **Map-v2 below-opus outcomes, first cluster (rows 676–677, both
  `repaired`):** no math failures — sonnet's S2 collapse was sound but its
  supersession sweep missed *cross-file* residue (3 stale docstrings + 1
  orphaned wrapper; the coordinator's deletion-check caught it), and a
  haiku 3-edit fixup dropped one word in a rewrap (coord full-diff read
  caught it). Both repairs cost one small follow-up each. Lesson encoded
  forward: E1's design pin pre-planned the E3 cross-file sweep with a grep
  done-gate, and E2+E3 then ran clean — *plan the residue sweep as its own
  leaf instead of expecting the build to remember it.*
- **Calibration-prose altitude is a failure axis the rubric's greps can't
  see (rows 678–680):** two sonnet passes delivered dictionary-compliant
  vocabulary but kept commentary inside statements + Lean syntax in notes,
  and one wrote a wrong "already compliant" audit verdict; the owner
  review caught it, the rules were sharpened (AUTHORING.md 9–13 + purity
  v2), and the opus escalation then fixed all six defect points in one
  pass. For owner-facing prose quality, schedule the review checkpoint
  *early* and treat below-opus "audited fine" verdicts about style
  compliance as unverified.
- **Fable design-settles (rows 672, 681) were both exemplary and both
  still needed deviation-handling downstream** (672 corrected the
  coordinator's own stale claim; 681's pinned lemma home hit the
  module-import constraint at build). The pin-verbatim +
  record-deviations-explicitly discipline absorbed both cleanly — the §E
  landed-delta note + FRICTION entry (E2) is the model for a builder
  overriding a pin for cause.
- **Tool-trust caveat (QUIRKS §74, from row 674):** `lean_run_code` can
  accept a `decide` the real `lake build` rejects (`Nat.card (Fin n)`
  kernel reduction). Spikes whose load-bearing step is `decide` need a
  real-build check before a pin trusts them.
- **The `hfresh` vacuity episode (rows 672–675):** a headline theorem sat
  vacuous through a full phase close *and* a careful vacuity analysis of
  its other hypotheses; it was caught only when the coordinator read the
  landed signature to scope a cleanup audit item, and the kernel-checked
  counterexample took minutes. Standing patterns adopted: satisfiability
  witnesses for headline statements (`Nonvacuity.lean` — a fully-applied
  instance whose existence breaks on any unsatisfiable-binder regression)
  and coordinator signature-reads before rating any statement-surface
  audit item.
