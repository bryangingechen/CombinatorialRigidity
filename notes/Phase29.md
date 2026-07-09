# Phase 29 — Synthesis & retrospective (RETRO) (work log)

**Status:** in progress (opened 2026-07-09).

## Current state

Phase open. Next concrete step: the **W1 scoping-decisions commit** —
settle S2 (selection bar) and S3 (framing) in this note and turn the
planning stub's raw-material inventory
(`notes/FormalizationRetrospective.md` *Candidate wrong turns*) into a
selected, ordered outline for the essay. Nothing has been harvested or
compressed yet; the two big design docs
(`notes/Phase22-realization-design.md`, `notes/Phase23-design.md`) are
intact, per the D1 gate below.

## Scope

The first codenamed phase off ROADMAP's post-program queue (**RETRO**).
Three deliverables, prose/organization only — no Lean, no mathematical
state change (phases 1–26 remain complete + axiom-clean):

1. **The Formalization Retrospective** — the wrong-turns methodology
   narrative planned in `notes/FormalizationRetrospective.md` (abandoned
   routes, mis-factorings, over-quantified source lemmas, undischargeable
   premises, abstraction-layer mismatches); the project-side mirror of
   `notes/BlueprintExposition.md`.
2. **The D1 design-doc compression** (`notes/Phase26-cleanup.md` D1,
   deferred to here): compress the closed arcs of
   `notes/Phase22-realization-design.md` / `notes/Phase23-design.md` —
   **in step with harvesting each doc for the retrospective, never
   before** (see *Blockers*).
3. **A final holistic exposition-quality pass** (the ROADMAP queue
   entry's third clause) — concrete scope defined after W2, once the
   retrospective has forced a re-read of the whole doc set.

## Architectural choices made up front

- **S1 (audience/medium) — settled: the `notes/` essay.** The stub's
  default home; no convention exception needed. The essay is written by
  growing `notes/FormalizationRetrospective.md` itself from planning stub
  into the deliverable (one canonical home; the stub already carries the
  inventory). The *blueprint-chapter* option ("Notes on the
  formalization" as a conscious exception to the process-out-of-blueprint
  convention) is **not** adopted; if the finished essay later seems worth
  surfacing to blueprint readers, that is a user-adjudicated follow-up,
  not this phase's call. The *formalization-paper* option stays open at
  zero cost — the finished essay would be its outline.

## Work items

- [ ] **W1 — scoping decisions S2 + S3 → outline.** Settle the selection
  bar (which wrong turns are *instructive* — a transferable lesson — vs.
  mere local churn) and the framing (honest-but-not-self-flagellating;
  several "wrong turns" were source-faithfulness *corrections*, normal
  formalization work). Then select from the stub's inventory and order
  the essay's sections; record both decisions + the outline in the stub.
- [ ] **W2 — harvest + write the essay, section by section.** Each
  section's commit harvests its sources (the design docs, DESIGN.md,
  FRICTION.md, phase notes) and — for the two big design docs — runs the
  D1 closed-arc compression on the harvested material *in the same
  commit* (compress-in-step). Likely several commits; slice by essay
  section.
- [ ] **W3 — final holistic exposition-quality pass.** Scope it in a
  short planning entry here once W2 closes.
- [ ] **W4 — `formalization.yaml` automation-metadata refresh.** The
  phase-open commit repaired the *status* drift (scope / main_results /
  alignment / fidelity, backfilled for phases 22k–26 with `#print
  axioms` checks); the *automation* section's how-it-was-produced
  metadata (models list, session counts, wall time) still describes the
  2026-06-07 state. A retrospective phase is the right place to
  reconstruct it accurately.

## Blockers / open questions

- **The D1 gate (standing constraint, from the stub):** do **not**
  compress `notes/Phase22-realization-design.md` /
  `notes/Phase23-design.md` ahead of harvesting them — compression
  happens in step with W2, per section, never before. (Also note
  `notes/MolecularConjecture.md`'s caution: dozens of inbound §-pointers
  from `DESIGN.md` / `notes/BlueprintExposition.md` / phase notes cite
  those docs' sections as the sole detailed home — W2's compression must
  keep every §-cited anchor resolvable or repoint the citers in the same
  commit.)
- W3's concrete scope is undefined until W2 closes (deliberate — the
  quality pass should react to what the retrospective surfaces).

## Hand-off / next phase

Next concrete commit: **W1** — settle S2 + S3 and write the essay
outline into `notes/FormalizationRetrospective.md`, updating this note's
*Current state*. Smallest useful slice; no harvesting or compression in
that commit.

## Decisions made during this phase

- (phase open, 2026-07-09) S1 settled — see *Architectural choices made
  up front*.
- (phase open, 2026-07-09) The phase-open commit also repaired the
  `formalization.yaml` status drift left by the Phase 22k–26 closes
  (the file had never been synced since its creation): status.scope /
  policy / fidelity rewritten to the completed state, the four molecular
  headline theorems added to `main_results` + `alignment` (each verified
  `#print axioms`-clean: propext, Classical.choice, Quot.sound), the
  Jackson–Jordán 2008 and Crapo–Whiteley 1982 sources added, and the
  stale `ForestSurgery.lean` module path fixed. Residual: W4.
