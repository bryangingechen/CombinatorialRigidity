# Phase 29 — Synthesis & retrospective (RETRO) (work log)

**Status:** in progress (opened 2026-07-09).

## Current state

**W1 done (2026-07-09).** S1 is **revised** by user adjudication: the
deliverable is a blueprint appendix chapter, not the `notes/` essay the
phase opened with (see *Architectural choices*). S2 (selection bar) and
S3 (framing + register) are settled, and
`notes/FormalizationRetrospective.md` now carries a taxonomy-ordered
outline over the full 10-item inventory plus a pinned exemplar section
(the vacuous-realization-predicate episode, user-approved
register/template).

**W2 first slice done (2026-07-09).**
`blueprint/src/chapter/retrospective.tex` ("Notes on the formalization")
exists, wired in via `\appendix` in `chapter/main.tex` after the last math
chapter (plastex supports `\appendix` natively — no fallback needed); it
carries the chapter intro (outline (i): S3 framing + the three-way classification)
and subsection (iii)'s first episode, the pinned vacuous-realization-
predicate exemplar, LaTeX-ified faithfully (two Lean defs as displayed
`alltt` code with `\(...\)` math substitutions for the source's Unicode;
`\href` commit links; both Lean snippets and both cited commit dates
re-verified against `git show`/`git log` — no factual errors found, no
correction needed). The three W2-opening prerequisites landed in the same
commit: `blueprint/CLAUDE.md` *The retrospective appendix* write-up,
`lint.sh`'s 5a/5b vocabulary-gate exemption for the appendix file, and the
`\href` mechanics (used in the exemplar itself). `blueprint/verify.sh` and
`blueprint/lint.sh` both green with the new file in place. Remaining
outline sections (ii), (iv)–(vi), and (iii)'s other two episodes are not
yet written (see *Hand-off*). Nothing has been harvested or compressed
yet for the other outline items; the two big design docs
(`notes/Phase22-realization-design.md`, `notes/Phase23-design.md`) are
intact, per the D1 gate below.

## Scope

The first codenamed phase off ROADMAP's post-program queue (**RETRO**).
Three deliverables, prose/organization only — no Lean, no mathematical
state change (phases 1–26 remain complete + axiom-clean):

1. **The Formalization Retrospective** — the wrong-turns methodology
   narrative, planned in `notes/FormalizationRetrospective.md` and
   delivered as a blueprint appendix chapter (S1, revised W1; abandoned
   routes, mis-factorings, over-quantified source lemmas,
   undischargeable premises, abstraction-layer mismatches); the
   project-side mirror of `notes/BlueprintExposition.md`.
2. **The D1 design-doc compression** (`notes/Phase26-cleanup.md` D1,
   deferred to here): compress the closed arcs of
   `notes/Phase22-realization-design.md` / `notes/Phase23-design.md` —
   **in step with harvesting each doc for the retrospective, never
   before** (see *Blockers*).
3. **A final holistic exposition-quality pass** (the ROADMAP queue
   entry's third clause) — concrete scope defined after W2, once the
   retrospective has forced a re-read of the whole doc set.

## Architectural choices made up front

- **S1 (audience/medium) — REVISED by user adjudication (2026-07-09): a
  blueprint appendix chapter**, not the `notes/` essay the phase-open
  default named. The deliverable is a new appendix chapter ("Notes on
  the formalization") in `blueprint/src/chapter/`, placed via `\appendix`
  after the math chapters so it never sits in the proof's reading path —
  the conscious exception to the process-out-of-blueprint convention,
  now user-adopted. Structure: one appendix chapter, one section per
  failure-mode class (the *Taxonomy* in the user's adjudication; outline
  in `notes/FormalizationRetrospective.md`). That file stays alive as the
  **planning doc** (inventory + outline + exemplar) — no longer the
  deliverable's home.
- **S2 (selection bar) — settled.** An episode is IN if it carries a
  transferable lesson, evidenced by promotion to a standing rule
  (`DESIGN.md` / `CLAUDE.md` / `CLEANUP.md` / blueprint gates / the
  coordinator playbook) or by genuine promotability. All 10 items in the
  planning doc's inventory pass this bar; new episodes surfaced during
  W2 harvesting face the same test.
- **S3 (framing + register) — settled.** Narrative, mechanism-focused
  postmortem framing — the reasons a wrong turn persisted are stated as
  facts about what each check does/doesn't read, no verdict language.
  Register: `blueprint/AUTHORING.md` principle A (flat published-paper
  prose, no significance-pointing, no mechanism metaphors, KT as
  exemplar) with a scoped carve-out: Lean declarations, types, and code
  blocks are first-class objects in this appendix, not merely
  parenthetical addresses. Commit links via
  `\href{https://github.com/bryangingechen/CombinatorialRigidity/commit/<sha>}{\texttt{<short-sha>}}`
  (post-lift shas only); every date/sha/fact re-verified against git at
  write time.

## Work items

- [x] **W1 — scoping decisions S2 + S3 → outline.** Done (2026-07-09).
  S1 revised, S2/S3 settled (see *Architectural choices*); the taxonomy-
  ordered outline over the full inventory and the pinned exemplar landed
  in `notes/FormalizationRetrospective.md`.
- [ ] **W2 — harvest + write the appendix, section by section.** Each
  section's commit harvests its sources (the design docs, DESIGN.md,
  FRICTION.md, phase notes) and — for the two big design docs — runs the
  D1 closed-arc compression on the harvested material *in the same
  commit* (compress-in-step). Likely several commits; slice by appendix
  section.
  - [x] **W2-opening prerequisites** — done (2026-07-09), landed with the
    commit that created the appendix file:
    - [x] `blueprint/CLAUDE.md` convention-exception + register-carve-out
      write-up (*The retrospective appendix*).
    - [x] `lint.sh`'s vocabulary gate: appendix file exempted from 5a/5b,
      `intro.tex`-style.
    - [x] Commit-link `\href` mechanics (used in the exemplar).
  - [x] (i) Chapter intro + (iii) first episode (the pinned exemplar) —
    done (2026-07-09).
  - [ ] (iii) remaining two episodes: KT Lemma 4.1 over-quantification
    (source: ROADMAP §20, `notes/Phase20.md`); the three-fixed-`Cᵢ`
    disjunction → six-join existential (source: `Claim612.lean:1320–1332`
    doc-comment, Phase 22e/22g notes).
  - [ ] (ii) The scaffolding arc (source: ROADMAP §22–23,
    `notes/Phase22-realization-design.md`, `notes/Phase23-design.md` —
    triggers D1 compression on those two docs, in step).
  - [ ] (iv) Abstraction-layer mis-factorings; (v) Walls from
    mis-modelling; (vi) Process/tracking failures — sources listed in
    `notes/FormalizationRetrospective.md`'s inventory.
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

Next concrete commit: the **second W2 slice**, subject to user review
before it lands (same as the first). Two candidates, either a reasonable
next step — pick whichever is smaller once its sources are actually
opened:
- finish subsection (iii) with its remaining two episodes (KT Lemma 4.1
  over-quantification; the three-fixed-`Cᵢ` disjunction → six-join
  existential — sources listed in the *Work items* checklist above), or
- open subsection (ii), the scaffolding arc, which triggers the D1
  closed-arc compression on `notes/Phase22-realization-design.md` /
  `notes/Phase23-design.md` *in the same commit* (the D1 gate below —
  harvest, then compress, never the reverse).
Each slice: harvest its named sources, LaTeX-ify in the appendix's
established register (flat prose, `alltt` code blocks with `\(...\)`
math substitutions for any further Lean excerpts, `\href` commit links),
and re-verify every date/sha/mathematical claim against git/the Lean
source before writing it down (`blueprint/CLAUDE.md` *The retrospective
appendix* has the mechanics; no new prerequisites are needed).

## Decisions made during this phase

- (W1, 2026-07-09) **S1 REVISED** by user adjudication: the deliverable
  is a blueprint appendix chapter, not the `notes/` essay the phase
  opened with. See *Architectural choices*.
- (W1, 2026-07-09) S2 (selection bar) and S3 (framing + register)
  settled — see *Architectural choices*. All 10 inventory items in
  `notes/FormalizationRetrospective.md` pass the S2 bar; the taxonomy-
  ordered outline assigns each to one of 6 appendix sections, no merges.
- (W2 first slice, 2026-07-09) `\appendix` and `alltt` both work cleanly
  under plastex/xelatex with no fallback needed; the one gotcha is
  `alltt`'s catcode change (`$` becomes literal, so Lean-Unicode math
  substitutions need `\(...\)`, not `$...$`) and a missing theme CSS rule
  for `<div class="alltt">` (added to `extra_styles.css`). Full mechanics
  write-up promoted straight to `blueprint/CLAUDE.md` *The retrospective
  appendix* (cross-cutting to every future W2 slice, so no phase-note
  duplication).
- (phase open, 2026-07-09) The phase-open commit also repaired the
  `formalization.yaml` status drift left by the Phase 22k–26 closes
  (the file had never been synced since its creation): status.scope /
  policy / fidelity rewritten to the completed state, the four molecular
  headline theorems added to `main_results` + `alignment` (each verified
  `#print axioms`-clean: propext, Classical.choice, Quot.sound), the
  Jackson–Jordán 2008 and Crapo–Whiteley 1982 sources added, and the
  stale `ForestSurgery.lean` module path fixed. Residual: W4.
