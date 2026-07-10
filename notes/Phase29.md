# Phase 29 — Synthesis & retrospective (RETRO) (work log)

**Status: ✓ complete** (opened and closed 2026-07-09).

## Outcome

The first codenamed phase off ROADMAP's post-program queue (**RETRO**);
prose/organization only — no Lean, no mathematical state change (phases
1–26 remain complete + axiom-clean). Three deliverables landed:

1. **The Formalization Retrospective** — the wrong-turns methodology
   narrative, delivered as the blueprint appendix chapter
   `blueprint/src/chapter/retrospective.tex` ("Notes on the
   formalization", via `\appendix` after the math chapters): ten
   episodes across six sections (chapter intro; the `d=3`-first
   scaffolding arc; statement-faithfulness episodes; abstraction-layer
   mis-factorings; walls from mis-modelling; process/tracking
   failures), integrated into `intro.tex`'s reader path. Planning doc
   (inventory + outline + pinned exemplar, retained as the archival
   record): `notes/FormalizationRetrospective.md`.
2. **The D1 design-doc compression** (`notes/Phase26-cleanup.md` D1):
   `notes/Phase22-realization-design.md` compressed by an
   anchor-preserving body-shrink (W2-7, twelve slices, §0–§1.71,
   8590 → 1939 lines, zero repoints); `notes/Phase23-design.md`
   **frozen** as a live-cited technical archive (W2-8; 137 live Lean
   doc-comment anchors — canonical disposition record in
   `notes/MolecularConjecture.md` *Program close*).
3. **A final holistic exposition-quality pass** (W3, three slices):
   appendix whole-unit coherence + 300dpi print-render inspection
   (W3-1), `intro.tex` reader-path integration (W3-2), and a post-W2
   doc-set freshness sweep (W3-3).

W4 additionally refreshed `formalization.yaml`'s `automation` section
(models census, wall-time, `tool_setup`); the phase-open commit had
already repaired that file's `status` drift left by the Phase 22k–26
closes (with `#print axioms` checks on the four molecular headline
theorems).

## Work items (all closed 2026-07-09)

- [x] **W1** — scoping decisions: S1 revised by user adjudication to a
  blueprint appendix chapter; S2 (selection bar: transferable lesson,
  evidenced by promotion) and S3 (framing/register: mechanism-focused
  postmortem, principle-A register with a Lean-as-first-class carve-out)
  settled; taxonomy-ordered outline over all 10 inventory items.
- [x] **W2** — the appendix written section by section (subsections
  i–vi, six per-slice-verified slices), then the decoupled D1 slices
  W2-7 (`Phase22-realization-design.md` body-shrink) and W2-8
  (`Phase23-design.md` frozen-disposition write-up). Per-slice detail:
  git history (each slice's commit message).
- [x] **W3** — the three-slice holistic pass (see *Outcome*); all three
  user-flagged deviations ACCEPTED (narrow appendix-centered scope;
  mid-phase `intro.tex` touch; reframe-not-restructure for the
  taxonomy overclaim).
- [x] **W4** — `formalization.yaml` automation-metadata refresh
  (grounded against a whole-history Co-Authored-By census; the
  unrecomputable session/turn count date-scoped rather than invented).
- [x] **Phase close** — ROADMAP row/§29 flip + compression, status
  surfaces verified (see *Phase-close record*), exposition-ledger
  no-entries judgment, doc-set sync, this note's compression.

## Phase-close record (2026-07-09)

- **User-facing status surfaces:** `intro.tex` was already synced by
  W3-2 (appendix in the reader path); `formalization.yaml` got small
  freshness flips at close (phases 27–29 no longer "ongoing"). README /
  `home_page/index.md` need no edit (Phase 27/28 precedent: they carry
  status at the arc level — "phases 1–26 complete, no `sorry`s" — which
  a docs-only post-program phase does not change; the appendix is
  reachable through the blueprint links they already carry).
- **Blueprint-chapter re-read:** W3-1's end-to-end appendix re-read +
  render inspection served as the phase-close re-read (per the
  pre-close hand-off); not repeated.
- **Exposition ledger:** no-entries judgment recorded in
  `notes/BlueprintExposition.md` (the appendix is project-side by
  construction — that ledger is source-side only).
- **Exception-log grooming** (`notes/dispatch-log.md`): coordinator-owned;
  F2/F3 were already promoted to the playbook during the phase, F1
  stays pending its promotion trigger. Left to the coordinator.
- **Project-organization review:** doc-set greps clean after this
  commit's syncs (`notes/CLAUDE.md`, `notes/MolecularConjecture.md`,
  `notes/FormalizationRetrospective.md` all flipped to closed form).
  Auto-loaded CLAUDE.md suite audited: root 439 / notes 239 / Lean 339 /
  blueprint 659 lines — the blueprint file is the largest but its
  growth this phase (*The retrospective appendix* section) is
  load-bearing gate/mechanics content already following the
  extract-to-reference pattern (`AUTHORING.md`, `RENDERING.md`); no
  extraction due. No swallowed promotions found.

## Hand-off / next phase

**Phase 29 is closed; no successor phase is opened.** Between phases,
ROADMAP's *Queued post-program phases* subsection is the hand-off
target: the queue holds **RELAX** (algebraic-independence relaxation,
`notes/AlgebraicIndependence.md`), **UPSTREAM** (mathlib upstreaming of
the `[mirrored]` lemmas), and **VERSO** (paused, external-gated) — all
optional/unscheduled. The next concrete task, when the user schedules
one, is opening that queue's chosen codename (minting its number) per
`PHASE-BOUNDARIES.md` *When this commit opens a phase*, with the
codename's planning note as the planning input.

## Decisions made during this phase

All settled; one-line verdicts (full detail: git history + the
per-surface records above).

- **S1 revised by user adjudication:** deliverable = blueprint appendix
  chapter, not a `notes/` essay; `\appendix` placement keeps it out of
  the proof's reading path. S2/S3 settled as in *Work items* W1.
- **D1 re-scoped by user adjudication (three flagged deviations, all
  ACCEPTED):** decouple compression from episode-writing; freeze
  `Phase23-design.md`; compress `Phase22-realization-design.md` by
  anchor-preserving body-shrink (keep every cited §-heading/letter,
  ≤3-line verdicts) rather than arc-collapse — zero repoints vs. ≈40.
- **Promoted to `blueprint/CLAUDE.md` *The retrospective appendix*:**
  the `\appendix`/`alltt` mechanics, the `alltt` catcode gotchas
  (`\(...\)` for symbols; `\(\sb{1}\)` for Unicode subscripts), the
  `div.alltt` CSS rule, the inline-`\texttt{}` overflow `\allowbreak{}`
  fix, and the commit-link `\href` convention.
- **Promoted to the coordinator playbook** (via
  `notes/dispatch-log.md` F2/F3): pinned-exemplar prose shaping;
  the verification-mandate benign cost signature.
- **Flagged for promotion on recurrence** (kept here as the archival
  flag): (a) pre-read recon size/anchor estimates are scheduling
  inputs, not per-slice contracts — each compression slice re-derives
  its own inventory (→ `notes/CLAUDE.md` if a third `*-design.md`
  compression hits it; dispatch-log F1); (b) a design doc's own inline
  STATUS/⚠️ annotations can overstate what "stands" — compress each
  letter to its *actual* disposition (→ `CLAUDE.md` *Docstrings are not
  evidence* on a third hit); (c) a STATUS-style blockquote dense with
  landed dispositions folds into the citing letters' verdicts rather
  than blanket-drop or verbatim-keep (→ `notes/CLAUDE.md` on
  recurrence).
- **W2-7 merge precedent:** a letter merges only at zero external
  citers + zero internal forward-references (whole-tree grep each
  time); three real merges across twelve slices, including the
  fold-into-nearest-cited-neighbor sub-case for an isolated uncited
  letter. Citer landscape included `model-experiment-archive.md`,
  `BlueprintExposition.md`, and the design doc's own prose — the
  post-edit whole-tree gate is load-bearing.
- **`formalization.yaml` grounding (W4):** the in-repo-unrecomputable
  session/turn count was date-scoped ("as of 2026-06-07") rather than
  extended or invented, per the never-commit-local-paths +
  honest-grounding constraints.
