# Formalization retrospective — the wrong turns (planning stub)

**Status: PLANNING STUB — deferred, not scheduled.** A future *new-synthesis*
task, distinct from the blueprint's mathematical exposition and from any cleanup
round. Seeded 2026-07-07 during the Phase-26 cleanup round
(`notes/Phase26-cleanup.md`) so the idea + its raw-material inventory are captured
while fresh.

## Purpose

A narrative account of the **wrong turns** the formalization took — the abandoned
routes, mis-factorings, over-quantified source lemmas, undischargeable premises,
and abstraction-layer mismatches — as a methodology record of how a large
formalization actually proceeds (vs. the clean final proof the blueprint presents).

This is a **deliberate exception** to a standing project convention: process /
route-history is normally *deleted* from live documents and left to git +
`notes/FRICTION.md` `[process]` entries + `DESIGN.md` cross-cutting sections
(`notes/CLAUDE.md` *Superseded reasoning leaves the live note*; `blueprint/CLAUDE.md`
supersession gate + vocabulary gate). Writing a wrong-turns narrative is worth
doing *consciously as its own deliverable*, not smuggled into the blueprint's math
exposition. It is the **project-side mirror** of `notes/BlueprintExposition.md`
(which is strictly *source-side* — KT's hard math — and explicitly excludes our
formalization mistakes).

## Scoping decisions to make when this is picked up

1. **Audience / medium** — pick one (or a layered pair):
   - *Project-facing methodology retrospective* — a `notes/` essay (default home;
     no convention exception needed).
   - *Reader-facing "Notes on the formalization"* — a blueprint section/chapter
     (a **conscious exception** to the process-out-of-blueprint convention; decide
     deliberately, and update `blueprint/CLAUDE.md` if adopted).
   - *Raw material for a formalization paper* — a different medium entirely; this
     doc becomes the outline.
2. **Selection bar** — which wrong turns are *instructive* (a transferable lesson)
   vs. mere local churn. The inventory below is a superset, not a table of contents.
3. **Framing** — honest-but-not-self-flagellating; several "wrong turns" were
   source-faithfulness *corrections* (finding KT's argument structure), which is
   normal formalization work, not error.

## Candidate wrong turns + current sources (raw-material inventory)

The richest archives are the two large design docs (kept intact for this — see
`notes/Phase26-cleanup.md` D1, deferred). Each item below names where the
blow-by-blow currently lives.

- **The `d=3`-first → general-`d` arc.** The whole Case III was built concretely
  at `d=3` (Phases 22c–22h) before the general lift (Phase 23). Source: ROADMAP
  §22–23; `notes/Phase22-realization-design.md`, `notes/Phase23-design.md`.
- **`p2/p3_candidateRow` abstraction-layer mis-factoring.** Candidate rows first
  factored as abstract row-family LI lemmas (Phase 22e); the final assembly
  (22g/h) needed framework-level producers (`case_III_arm_realization_M2/_M3`), so
  the abstraction was stranded. Source: this round's A2 (`notes/Phase26-cleanup.md`);
  `Claim612.lean` doc-comments; Phase 22e/g/h notes.
- **The member-mapping wall (Phase 23).** The `±r`-block rank certificate hit a
  wall intrinsic to KT's moving-member row bookkeeping; resolved by the KT-faithful
  `fromBlocks A 0 C D` certificate. Source: ROADMAP §23; `notes/Phase23-design.md`;
  `notes/Phase23e.md`.
- **The eq.-(6.12) `+(D−1)` vs `+D` shortfall.** A one-line arithmetic shortfall
  that sat under several re-plans. Source: `DESIGN.md` *Constructibility recon
  before scheduling a producer build*; `notes/FRICTION.md` *[process] Phase 21b
  realization producers*.
- **Motion-space splice vs. KT block-triangular (Phase 22a).** A locally-sound
  modelling choice re-expressed KT's rank-addition as a common-seed glue, producing
  undischargeable bridge hypotheses. Source: `DESIGN.md` *Match the source's
  argument structure…*; `notes/FRICTION.md` *[process] Phase 22a*.
- **`def:rank-hypothesis` vacuity slip.** A definition sat `\leanok` at KT strength
  while the pinned `Prop` was satisfiable by an all-zero-extensor welded framework;
  unnoticed from Phase 21 through three weeks of downstream work. The Phase-22i
  fix — strengthening the bare realization statement to the free-hinge carrier so
  KT's coincident-panel case (Lemmas 5.3/6.2) is expressible — is the same thread
  from the repair side (a statement made faithful, not an empty proof filled).
  Source: `DESIGN.md` *Statement faithfulness to the source*; `blueprint/CLAUDE.md`
  definition-faithfulness gate (Phase-22h postmortem); the Phase-28 RETROSCAN
  Group-B adjudication (`notes/BlueprintExposition.md` *Retroactive coverage →
  Group B*, which judged this project-side and out of the source-side ledger).
- **KT Lemma 4.1 over-quantification.** Formalized counterexample; routed around via
  a deficiency-count argument. Source: ROADMAP §20; `notes/Phase20.md`.
- **The three-fixed-`Cᵢ` disjunction → six-join existential.** The `d=3` Claim-6.12
  conclusion was first stated as a disjunction over three hardcoded lines
  (mathematically undischargeable: 3 `2`-extensors span ≤ 3 of 6 dims); corrected to
  an existential over the six joins (Lemma 2.1). Source: `Claim612.lean:1320–1332`
  doc-comment; Phase 22e/22g notes.
- **The `hcontract` dispatch left untracked across five sub-phases (22a→22k).**
  A case-split obligation called "coordinator wiring" that had no tracking artifact.
  Source: `DESIGN.md` *Statement faithfulness to the source*; `CLAUDE.md`
  *Before each commit → Move deferred items* (the Phase-22a calibration).
- **The d=3 Claim-6.12 "dead island" misread (Phase-26 cleanup, 2026-07-07).** A
  section was read as dead/orphaned from two signals — its capstone node had zero
  incoming `\uses`, and the d=3 dispatch had zero grep callers — and slated for
  retirement/demotion. Deeper analysis reversed it: the capstone decl is live
  (`case_III_claim612_gen`, used by the general chain), the missing `\uses` was a
  blueprint wiring gap, and the *genuinely* dead decl (the d=3 dispatch) turned out to
  be a genuinely-simpler worked case worth keeping. The transferable lesson —
  liveness is a property of the Lean call chain, not of `\uses`/grep — is now in
  `CLEANUP.md` §B. Source: `notes/Phase26-cleanup.md` *Blockers* + *Decisions*; the
  session's git history.

## Do NOT lose this material

Until this task is written, **do not run the D1 closed-arc compression** on
`notes/Phase22-realization-design.md` / `notes/Phase23-design.md`
(`notes/Phase26-cleanup.md` D1 is deferred for exactly this reason). Compress in
step with harvesting, not before.
