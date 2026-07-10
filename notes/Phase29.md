# Phase 29 — Synthesis & retrospective (RETRO) (work log)

**Status:** in progress (opened 2026-07-09).

## Current state

**All four work items (W1–W4) are DONE (2026-07-09) — Phase 29 is ready for
the phase-close checklist** (`PHASE-BOUNDARIES.md` *When this commit closes a
phase*, not run in this commit — see *Hand-off*). Per-item detail lives in
*Work items* below, not restated here: W1 settled the scoping decisions (S1
revised to a blueprint appendix chapter; S2/S3 settled — *Architectural
choices*); W2 harvested and wrote the appendix (`retrospective.tex`, 10
episodes across subsections i–vi) and closed the decoupled D1 design-doc
compression (W2-7 `Phase22-realization-design.md` body-shrink, W2-8
`Phase23-design.md` frozen-disposition write-up); W3 ran the three-slice
holistic exposition-quality pass (W3-1 appendix coherence + render
inspection, W3-2 `intro.tex` reader-path integration, W3-3 a post-W2
doc-set freshness sweep — all three user-flagged deviations ACCEPTED); W4
refreshed `formalization.yaml`'s `automation` section (models list,
wall-time, tool_setup — grounding detail in *Work items* → W4).

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
   before** (gate discharged 2026-07-09 — W2-7/W2-8, *W2 slice plan*).
3. **A final holistic exposition-quality pass** (the ROADMAP queue
   entry's third clause) — scoped 2026-07-09, after W2 closed, from an
   actual re-read of the appendix + doc set: see *W3 slice plan*.

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
- [x] **W2 — harvest + write the appendix, section by section. CLOSED
  (2026-07-09).** The appendix (subsections i–vi) is fully written; the D1
  closed-arc compression the 2026-07-09 anchor recon decoupled into its own
  slices — W2-7 (`Phase22-realization-design.md` anchor-preserving
  body-shrink) and W2-8 (`Phase23-design.md` frozen-disposition write-up) —
  is done, per the *W2 slice plan* below.
  - [x] **W2-7 — DONE (2026-07-09).** Twelve slices, §0–§1.71 compressed
    (8590 → 1939 lines; per-slice record in *W2 slice plan* → *Ordered
    sub-slice list*).
  - [x] **W2-8 — DONE (2026-07-09).** `Phase23-design.md` frozen-disposition
    write-up (no-op recording): `notes/Phase26-cleanup.md` D1 flipped to
    closed; `notes/MolecularConjecture.md` *Program close* corrected to
    distinguish the two docs' dispositions. **W2 closes with this slice** —
    next is W3 scoping, see *Hand-off*.
  - [x] **W2-opening prerequisites** — done (2026-07-09), landed with the
    commit that created the appendix file:
    - [x] `blueprint/CLAUDE.md` convention-exception + register-carve-out
      write-up (*The retrospective appendix*).
    - [x] `lint.sh`'s vocabulary gate: appendix file exempted from 5a/5b,
      `intro.tex`-style.
    - [x] Commit-link `\href` mechanics (used in the exemplar).
  - [x] (i) Chapter intro + (iii) first episode (the pinned exemplar) —
    done (2026-07-09).
  - [x] (iii) remaining two episodes — done (2026-07-09): KT Lemma 4.1
    over-quantification (source: ROADMAP §20, `notes/Phase20.md`); the
    three-fixed-`Cᵢ` disjunction → six-join existential (source:
    `Claim612.lean:1320–1332` doc-comment, Phase 22e/22g notes).
    Subsection (iii) is now CLOSED (3 of 3 episodes written).
  - [x] (ii) The scaffolding arc — done (2026-07-09): the `d=3`-first →
    general-`d` scaffolding narrative (source: ROADMAP §22–23,
    `notes/Phase22-realization-design.md` §0/§1.1/§1.25–26/§1.33(C),
    `notes/Phase23-design.md` §0–§3). Read-only harvest per the
    2026-07-09 adjudication — D1 compression on the two design docs is
    **decoupled** to its own later slices (W2-7/W2-8), not triggered here.
  - [x] (iv) Abstraction-layer mis-factorings — done (2026-07-09): both
    episodes (the Claim 6.12 candidate-row producers stranded by the
    certify-then-rebase correction; the motion-space splice vs. KT's
    block-triangular rank-addition, Phase 22a). Subsection (iv) is now
    CLOSED (2 of 2 episodes written).
  - [x] (v) Walls from mis-modelling — done (2026-07-09): both episodes
    (the member-mapping wall, Phase 23; the eq.-(6.12) `+(D−1)` vs `+D`
    shortfall, Phase 21b). Subsection (v) is now CLOSED (2 of 2 episodes
    written).
  - [x] (vi) Process/tracking failures — done (2026-07-09): both episodes
    (the Case-I dispatch's untracked Lemma-6.5 arm, Phase 22a→22k; the
    `d=3` Claim-6.12 "dead island" misread, Phase-26 cleanup). Subsection
    (vi) is now CLOSED (2 of 2 episodes written) — **the appendix is
    complete, i–vi all written.**
- [x] **W3 — final holistic exposition-quality pass. CLOSED
  (2026-07-09).** SCOPED (2026-07-09, design pass) into three ordered
  slices — full plan, out-of-scope list, and the three (now-resolved)
  user flags in *W3 slice plan*:
  - [x] **W3-1 — appendix whole-unit coherence pass + render
    inspection** (`blueprint/src/chapter/retrospective.tex`) — DONE
    (2026-07-09): intro reframe, seam re-read, 300dpi render inspection
    (one overflow fix). See *W3 slice plan* item 1 / *Decisions made*.
  - [x] **W3-2 — reader-path integration of the appendix into
    `intro.tex`** (flag 2 ACCEPTED — sanctioned mid-phase) — DONE
    (2026-07-09). See *W3 slice plan* item 2.
  - [x] **W3-3 — post-W2 doc-set freshness sweep — DONE (2026-07-09),
    closes W3.** Fixed both pre-verified stale statements
    (`notes/CLAUDE.md`'s `FormalizationRetrospective.md` entry; that
    file's own status header) plus three more the bounded grep
    surfaced: `FormalizationRetrospective.md`'s "kept intact"/"D1,
    deferred" line and its *Do NOT lose this material* section (both
    still described the W2-7 compression as in-progress, itemizing
    slices §0–§1.49 through §1.69 as done and §1.70–§1.71 as pending —
    stale since the twelfth slice closed W2-7 entirely); and
    `notes/Phase22-realization-design.md`'s own top-of-file banner,
    written after W2-7's *first* slice and never refreshed across the
    remaining eleven — it still said only §0–§1.49 was compressed and
    the "bulk of the file" (§1.50 on) carried the full narrative,
    though the file is now 1939 lines end to end. `notes/Phase26-cleanup.md`'s
    "Formalization Retrospective" bullet also still said "D1 is held
    for it" despite that same file's own D1 checklist item, three
    lines above, already marking D1 closed. No `###`/`##` section
    anchors touched (verified: `git diff` shows zero heading-line
    changes in `Phase22-realization-design.md`); post-edit re-grep for
    `held for it` / `still carries the full narrative` / `kept intact`
    / `What remains of W2` across the four touched files returns
    nothing outside two unrelated template lines in `notes/CLAUDE.md`'s
    own `PhaseN.md` template.
- [x] **W4 — `formalization.yaml` automation-metadata refresh — DONE
  (2026-07-09).** The phase-open commit repaired the *status* drift (scope /
  main_results / alignment / fidelity, backfilled for phases 22k–26 with
  `#print axioms` checks); this slice repaired the *automation* section's
  how-it-was-produced metadata, which still described the 2026-06-07 state.
  Changes: `models` list gained `claude-fable-5`, `claude-sonnet-5`,
  `claude-sonnet-4-6` (grounded against a whole-history `git log`
  Co-Authored-By census — 2646 commits, 2026-05-06 to 2026-07-09; counts
  recorded in the field's own comment); `cost.wall_time` end date moved
  2026-06-07 → 2026-07-09 (split into the phases-1–26 close 2026-07-07 vs.
  ongoing phase-27+ work); `tool_setup` rewritten to describe per-task
  model-rung dispatch (the coordinator's Dispatch playbook) rather than a
  single fixed model, and names the concluded two-repo model-tier experiment
  (`notes/model-experiment-archive.md`, ~890 rated dispatches). The
  `prompting_notes` session/turn count ("~200 sessions, ~30k assistant
  turns") has no in-repo source to recompute from (it came from local
  session logs a prior session had access to) — per `CLAUDE.md`'s
  never-commit-local-paths + honest-grounding constraints, it was
  date-scoped to "as of 2026-06-07" rather than extended or invented, with a
  note flagging the ~5 further weeks it doesn't cover. YAML re-validated
  with Ruby's YAML parser after edit (no pyyaml available locally); diff
  reviewed for stray local-path leakage (none).

## Blockers / open questions

No hard blockers. The three W3 items flagged for user adjudication were
all resolved 2026-07-09 (*W3 slice plan → Flagged adjudications*): W3
stays narrow/appendix-centered (flag 1 ACCEPTED), W3-2 is sanctioned as
a mid-phase `intro.tex` touch (flag 2 ACCEPTED), and the taxonomy
overclaim was repaired by reframing the chapter intro rather than
restructuring the chapter (flag 3 ACCEPTED — the default).

## Hand-off / next phase

**W4 is DONE — all four Phase 29 work items (W1–W4) are closed.** Next
concrete commit = the **phase-close checklist** (`PHASE-BOUNDARIES.md` *When
this commit closes a phase*), not run in this commit: flip + re-thin the
ROADMAP Phase 29 row, compress the §29 planning section, sync the
user-facing status surfaces (README, `home_page/index.md`,
`blueprint/src/chapter/intro.tex`), reconcile `formalization.yaml` alignment
if the close touches it further, write the exposition-ledger entry
(`notes/BlueprintExposition.md`) if warranted, and do the project-organization
review. W3-1's end-to-end appendix re-read (done, 2026-07-09) doubles as the
natural input to the phase-close "end-to-end blueprint-chapter re-read" for
this phase's chapter — it does not need repeating. No open blockers.

## W3 slice plan (proposed 2026-07-09 by the scoping design pass; all three flags ACCEPTED 2026-07-09)

Scoping input: a full re-read of the appendix (783 lines) as one
document, `intro.tex`, ROADMAP §27–§29, and the post-W2 notes state.
Governing observation: **Phases 27 + 28 already swept the entire
chapter set** (27: the molecular crux expositions; 28: all 15
non-molecular chapters + `intro.tex` against `AUTHORING.md` A–F) on
2026-07-08/09, and no chapter content has changed since **except the
appendix itself** — which was written in six per-slice-verified slices
and has never been read as a unit. So the "final holistic
exposition-quality pass" concentrates on the one exposition surface
not yet holistically read (the appendix) and its integration seams,
not on re-sweeping recently-swept chapters. Each slice = one commit,
user-reviewed before landing (W2 precedent). Docs-only throughout.

1. **W3-1 — appendix whole-unit coherence pass + render inspection —
   DONE (2026-07-09).** File: `blueprint/src/chapter/retrospective.tex`.
   Reframed the two chapter-intro paragraphs (dropped "each episode
   below is one of them" / "each section below is one failure-mode
   class"; named the scaffolding-arc section as outside the
   classification and the walls section as symptom-grouped, both by
   `\cref`), did NOT reorder subsections (flag 3). Check (a), the
   single-sitting seam re-read: found Claim 6.12's second introduction
   (abstraction-layer section) redundantly restating the first
   (statement-faithfulness section)'s free-line-choice background —
   fixed with a `\cref` back-pointer instead of further rewriting; the
   third introduction (process-tracking section) was already
   appropriately cross-linked; no other terminology/`\cref`/register
   seam issues found. Check (b), the 300dpi print-PDF inspection: all 8
   `alltt` blocks clean (true `\sb{}` subscripts, no overflow); but two
   long inline `\texttt{}` Lean identifiers in running prose (outside
   any `alltt` block, process-tracking section) overflowed the print
   margin — fixed with `\allowbreak{}` (mechanics promoted to
   `blueprint/CLAUDE.md` *The retrospective appendix*); web-build
   `div.alltt` spot-check clean (CSS rule present, `\sb{}` macros pass
   through unmangled for MathJax). Check (c) skipped per plan. Gates
   `blueprint/lint.sh` + `blueprint/verify.sh` green throughout.
2. **W3-2 — reader-path integration of the appendix into `intro.tex` —
   DONE (2026-07-09).** File: `blueprint/src/chapter/intro.tex`. Both
   pre-verified defects fixed: (a) the *Reading this blueprint* guide
   nowhere mentioned the appendix — added a closing paragraph naming
   what it records (a statement whose formal strength diverged from the
   source, a decomposition that did not survive contact with the
   argument it was meant to feed, a decision left with no record of the
   obligation it created) and that it stands outside the mathematical
   development, `\cref{sec:formalization-notes}`-linked; (b) the
   forward-mode paragraph's "the one place in the blueprint that uses
   this project-process vocabulary" claim was false since the appendix
   landed — reworded to "the only places" (this paragraph and the
   appendix), cross-linked the same way. `lint.sh` + `verify.sh` both
   green; `inv bp`'s log shows no new Overfull-hbox warnings from either
   added paragraph (checked by isolating the `intro.tex` portion of the
   log before/after).
3. **W3-3 — post-W2 doc-set freshness sweep — DONE (2026-07-09), closes
   W3.** Files: `notes/CLAUDE.md`, `notes/FormalizationRetrospective.md`,
   plus grep-driven. Fixed the two pre-verified stale statements Phase
   29's own W1/W2 left behind: (a) `notes/CLAUDE.md`'s
   `FormalizationRetrospective.md` entry said the D1 compression "is
   held for it — do **not** compress … before harvesting" (both D1
   slices are in fact closed); (b) `FormalizationRetrospective.md`'s
   status header said "What remains of W2 is the D1 closed-arc
   compression". Sweep bound: grep `retrospective` /
   `FormalizationRetrospective` / `Phase22-realization-design` across
   tracked `.md` files and fix ONLY statements Phase 29 itself made
   stale — not a general notes audit. The bounded grep surfaced three
   more genuine hits: `FormalizationRetrospective.md`'s "kept intact …
   D1, deferred" line and its *Do NOT lose this material* section (both
   itemized the W2-7 per-slice progress as of the point that section was
   last touched, with §1.70–§1.71 marked pending — stale once the
   twelfth slice closed W2-7 entirely); `notes/Phase22-realization-design.md`'s
   own top-of-file banner (written after W2-7's first slice, never
   refreshed across the remaining eleven — still said only §0–§1.49 was
   compressed and the file's "bulk" carried the full narrative, though
   the whole file is now compressed end to end, 8590 → 1939 lines); and
   `notes/Phase26-cleanup.md`'s "Formalization Retrospective" bullet
   ("D1 is held for it"), contradicting that same file's own D1
   checklist item three lines above, already marked closed. Check:
   post-edit re-grep (clean — the only remaining "in progress" hits are
   unrelated template lines in `notes/CLAUDE.md`'s `PhaseN.md`
   template); no `###`/`##` section anchors touched (`git diff` on
   `Phase22-realization-design.md` shows zero heading-line changes).

### Explicitly OUT of scope for W3

- **A fresh top-to-bottom register/readability re-read of the math
  chapters** — Phases 27/28 did exactly that days ago and nothing in
  them has changed since; re-running would duplicate with no new
  signal. (Flag 1, ACCEPTED, confirmed this narrow scope.)
- **Lean sources and docstrings** (the phase is docs-only prose).
- **`formalization.yaml`** — that is W4.
- **README / home_page status-surface re-sync, the
  `notes/BlueprintExposition.md` chapter write-up, and the
  project-organization review** — all phase-close checklist items
  (`PHASE-BOUNDARIES.md`); W3-1's re-read feeds the phase-close
  chapter re-read, it does not replace the rest.
- **Back-pointers from math chapters into the appendix** — would put
  process history into the proof's reading path, against the
  `\appendix` placement decision (S1).
- **Any compression/disposition change to
  `notes/FormalizationRetrospective.md` beyond W3-3's status-header
  freshness flip** — design-support docs compress at phase close
  (`notes/CLAUDE.md`).

### Flagged adjudications (user decisions — ALL THREE ACCEPTED 2026-07-09)

1. **Scope width — ACCEPTED.** W3 stays narrow: three small slices
   centered on the appendix and its integration seams, NOT a fresh
   whole-blueprint pass, because Phases 27/28 swept every chapter
   within the last two days.
2. **`intro.tex` mid-phase touch — ACCEPTED.** W3-2 edits a user-facing
   status surface before the phase-close sync; sanctioned now rather
   than folded into that checklist, since both defects are
   reader-visible today.
3. **Reframe vs. restructure in W3-1 — ACCEPTED (reframe).** The
   taxonomy-overclaim repair reframes the chapter intro; the chapter's
   subsections are not reordered or reclassified.

## W2 slice plan (settled 2026-07-09 by the anchor recon)

Per-episode source lists live in `notes/FormalizationRetrospective.md`
*Candidate wrong turns + current sources*; this section adds the slice /
compression / anchor layer on top. **Three deviations from the pinned D1
gate were flagged for the user and ACCEPTED 2026-07-09** (see *Flagged
adjudications*).

### Harvest map (design-doc §-ranges → appendix episode)

Served W2-3…W2-6, all CLOSED — the appendix is written, so the map is
settled. Per-episode source lists (which §-ranges / notes / Lean
doc-comments fed each of the 10 episodes) live in
`notes/FormalizationRetrospective.md` *Candidate wrong turns + current
sources*; the verbatim map this section carried while W2 was open is in
git history (pre-W3 revisions of this file).

### Compression plan (the anchor-preservation constraint) — EXECUTED, compressed 2026-07-09 (W3-1)

The recon inventoried who cites each doc and at what granularity, then
settled two dispositions, both now DONE (W2-7/W2-8): `Phase23-design.md`
**left frozen** — 137 live Lean doc-comment citations at PROBE/LEAF
granularity across ≈40 anchors would break under any compression, and
the frozen-archive verdict is recorded canonically in
`notes/MolecularConjecture.md` *Program close* — and
`Phase22-realization-design.md` compressed by an **anchor-preserving
body-shrink** (keep every cited §-heading and lettered sub-item, shrink
each to a ≤3-line verdict) rather than the `notes/CLAUDE.md`
arc-collapse model, which here would have forced ≈40 repoints instead
of the zero this strategy achieved. Headline figures + the mid-slice
"§1.50 onward" correction: *Decisions made* below. Full per-doc anchor
inventory: git history (pre-W3 revisions of this file).

### Ordered sub-slice list — ALL SIX DONE, CLOSED

Per-slice status already in *Work items* above; not restated here. W2-7's
per-slice byte/anchor/citer detail (twelve slices, §0–§1.71, 8590 → 1939
lines, zero repoints, three letter-pair merges, one legacy-block
hard-collapse, one STATUS-blockquote fold): git history (each slice's own
commit message) + the *Decisions made* cross-cutting-lessons entry.

The three flagged deviations from the pinned D1 gate this slice plan
required (decouple compression from episode-writing; freeze
`Phase23-design.md`; compress `Phase22-realization-design.md` by
anchor-preserving body-shrink, not arc-collapse) — all ACCEPTED
2026-07-09 — are recorded in *Decisions made* bullet 1, not duplicated here.

## Decisions made during this phase

- (W2 slice plan, 2026-07-09) The rest of W2 is decomposed into the
  ordered slices W2-3…W2-8 (*W2 slice plan*). The anchor recon found
  `Phase23-design.md` cited by 137 live Lean doc-comment lines (≈40
  anchors, PROBE/LEAF granularity) vs. `Phase22-realization-design.md`'s
  5 live-Lean anchors, forcing three flagged deviations from the pinned
  D1 gate: decouple compression from episode-writing (own slices, after);
  freeze Phase23 (D1 no-op for it); compress Phase22 by anchor-preserving
  body-shrink (zero repoint), not arc-collapse. User decisions.
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
- (W2 second slice, 2026-07-09) Discovered a second `alltt` gotcha beyond
  the first slice's `$`/catcode one: a Lean identifier with a Unicode
  subscript (`C₁`) needs `\(\sb{1}\)`, not `\(_1\)` — `_` is itself one of
  the characters `alltt` recatcodes to literal, and catcodes are fixed at
  tokenization time before `\(`/`\)` run, so a bare `_` inside `\(...\)`
  stays literal (caught by rendering the print PDF at 300dpi, not by
  `pdftotext`, which only sees the character stream). **Promoted to**
  `blueprint/CLAUDE.md` *The retrospective appendix* (cross-cutting to
  every future W2 slice with a subscripted Lean name).
- (phase open, 2026-07-09) The phase-open commit also repaired the
  `formalization.yaml` status drift left by the Phase 22k–26 closes
  (the file had never been synced since its creation): status.scope /
  policy / fidelity rewritten to the completed state, the four molecular
  headline theorems added to `main_results` + `alignment` (each verified
  `#print axioms`-clean: propext, Classical.choice, Quot.sound), the
  Jackson–Jordán 2008 and Crapo–Whiteley 1982 sources added, and the
  stale `ForestSurgery.lean` module path fixed. Residual: W4.
- (W2-7, 2026-07-09) **Per-slice byte/anchor/citer detail lives in *W2
  slice plan* → *Ordered sub-slice list*, not duplicated here**
  (rebalanced 2026-07-09 seventh slice — this entry previously restated
  it in full, tipping the note
  past the ~500-line tripwire). Cross-cutting lessons only:
  - Two recon-estimate corrections (first/second slices), both found only
    by re-deriving the anchor/size inventory at build time rather than
    trusting the phase-open recon: the pre-planned W2-7a/b content
    boundary was a poor *size* split (re-drawn at §0–§1.49); the recon's
    "5 live-Lean anchors" count holds only for §0–§1.49, not §1.50 on
    (letter-granular citation from ~15 `.lean` files). Flag for promotion
    to `notes/CLAUDE.md` if a third `*-design.md` compression hits the
    same pre-read-estimate trap.
  - **Merge precedent** (zero external citers + zero internal
    forward-references, confirmed by a whole-tree grep each time): zero
    letters merged across the first nine slices (a bare-section citer or
    later in-file forward-reference routinely depends on content under an
    individually-uncited letter), then three real merges — tenth slice
    (§1.69's (e)/(f)), eleventh slice (§1.70's original (g)/(h)), twelfth
    slice (§1.71's (e) into (d)) — so the clause is a used path, not just a
    theoretical one. The twelfth merge is a new sub-case: a single
    genuinely-uncited letter with **no adjacent uncited partner** (unlike
    the first two, which paired two consecutive uncited letters into one
    combined verdict) — resolved by folding it into the nearest cited
    neighbor instead of forcing an artificial pairing.
  - **STATUS-style blockquote handling — a third option beyond
    keep/drop** (twelfth slice): a design pass's own build-time `> STATUS`
    update, denser with already-landed disposition than the routine
    `> Docs-only design pass` audit list, is not well served by either the
    blanket-drop precedent (loses load-bearing "actual disposition" facts
    the citing letters need) or verbatim retention (redundant with
    `Phase22k.md`'s own fuller record). Resolution: fold each STATUS fact
    into the specific citing letter's own verdict it corrects/confirms,
    then compress the blockquote itself to a two-sentence top summary.
    Flag for promotion to `notes/CLAUDE.md` if a future design-doc
    compression meets another such blockquote.
  - **Header-span gate-script fix**, its full arc: sixth slice found the
    post-edit gate must key a section's span by full header *label*
    (`"1.70"` vs `"1.70(i)"`), not bare section number, once a
    `### 1.N(x)` sub-header reuses the same leading number; tenth slice
    found the missing other half — a citation must be checked against the
    header-span dict *before* falling back to a body-letter lookup (else
    `§1.70(i)`/`§1.70(i.1)` misreads as a missing letter `i` of §1.70);
    eleventh slice validated the complete fix for real, on a range that
    actually contains and touches a `### 1.N(x)` sub-header (the tenth
    slice's validation was against pre-existing untouched content).
  - New wrinkle (seventh slice): **a design pass's own internal claims can
    be wrong**, discoverable only by reading the later section that
    corrects them — §1.65's ⚠️ box claimed "(a)–(g) all STAND" but §1.66's
    own text inverts (b) and supersedes (d)/(g); compressed each letter to
    its *actual* disposition rather than the box's blanket claim (a
    compression-scope judgment call, not a new recon). Flag for promotion
    to `CLAUDE.md` *Docstrings are not evidence* if a third design-doc
    compression hits an inline annotation overstating what "stands".
  - **Citer-source landscape**: `notes/model-experiment-archive.md`
    (found eighth slice) and `notes/BlueprintExposition.md` (found
    eleventh slice, by the fresh whole-tree re-derive — not by trusting a
    prior slice's flagged-citer list) are both dense letter-level citers
    of this range, on top of the phase-note/Lean-file citers a design-doc
    compression would expect. A citer *inside* the design doc itself is
    also possible (ninth slice: §1.70's own prose forward-references
    §1.68(d)) — the post-edit gate's whole-tree-incl.-own-sections step is
    load-bearing, not belt-and-suspenders.
- (W3-1, 2026-07-09) Full detail in *W3 slice plan* item 1, not
  duplicated here. Cross-cutting only: a long inline `\texttt{}` Lean
  identifier in running prose (not an `alltt` block) can overflow the
  print build's right margin — TeX has no legal break point inside a
  `\texttt{}` group with no interword glue; fixed with `\allowbreak{}`
  after selected `\_`s. Promoted to `blueprint/CLAUDE.md` *The
  retrospective appendix*, alongside the existing `alltt`-specific
  gotchas, since this appendix's register is the one place in the
  blueprint that inlines long Lean identifiers in flowing prose.
