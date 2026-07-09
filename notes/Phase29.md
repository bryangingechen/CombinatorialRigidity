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
`blueprint/lint.sh` both green with the new file in place.

**W2 second slice done (2026-07-09) — subsection (iii) CLOSED.** The two
remaining statement-faithfulness episodes landed: *KT Lemma 4.1's
over-quantified statement* (the three-layer finding — false universal
quantifier, the balanced-packing gloss resolved positively as a gap not an
error, the true base-quantified content reached instead via the def=corank
bridge — `\cref`-ing the existing Remark `rem:kt-lemma-41` rather than
duplicating it) and *A fixed-candidate disjunction for Claim 6.12's free
line choice* (the `d=3` Claim-6.12 capstone's three-fixed-`Cᵢ` disjunction,
found mathematically undischargeable — 3 vectors span ≤ 3 of
$\bigwedge^2\R^4$'s 6 dims — and restated as the six-join existential).
Every date/sha/Lean statement was re-verified against `git show`/`git log`
before writing (6 commits cited across the two episodes: `f0934296`,
`bc579c3f`, `398ce7ac` for KT 4.1; `56aef7c4`, `82b3b50a`, `d5ff3648` for
Claim 6.12). Subsection (iii) is now fully written (3 of 3 episodes).
Outline sections (ii), (iv)–(vi) remain; the two big design docs are still
intact.

**W2 remaining decomposed (2026-07-09, anchor recon).** The rest of W2 is
now an ordered single-commit slice list (*W2 slice plan* below), grounded
in an inventory of who cites the two design docs. Headline finding:
`Phase23-design.md` is cited by **137 live Lean-source doc-comment lines**
(≈40 anchors, PROBE/LEAF granularity), so it is recommended to stay
**frozen** and the D1 compression is **decoupled from episode-writing**
(three flagged deviations from the pinned same-commit D1 gate — user
decisions). Next commit is slice **W2-3 = appendix §(ii)**, pure prose.

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
  - [x] (iii) remaining two episodes — done (2026-07-09): KT Lemma 4.1
    over-quantification (source: ROADMAP §20, `notes/Phase20.md`); the
    three-fixed-`Cᵢ` disjunction → six-join existential (source:
    `Claim612.lean:1320–1332` doc-comment, Phase 22e/22g notes).
    Subsection (iii) is now CLOSED (3 of 3 episodes written).
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
  happens in step with W2, per section, never before. **Refined by the
  2026-07-09 anchor recon (see *W2 slice plan* → *Compression plan* and
  the flagged deviations):** the "never before" ordering holds, but the
  pinned "in the *same commit* as the harvest" clause and the "compress
  *both* docs" scope do **not** survive contact with the inbound-anchor
  reality — `Phase23-design.md` is cited by **137 live Lean-source
  doc-comment lines** (≈40 distinct anchors, down to PROBE/LEAF
  granularity) and is recommended to stay **frozen**; `Phase22-realization
  -design.md` (5 live-Lean anchors + ≈35 cross-cutting) compresses by an
  **anchor-preserving body-shrink** (keep every cited heading, ≤3-line
  verdicts, zero repoint) as its **own slice after** the episodes that
  harvest it. These are user adjudications flagged in *W2 slice plan*.
- W3's concrete scope is undefined until W2 closes (deliberate — the
  quality pass should react to what the retrospective surfaces).

## Hand-off / next phase

Subsection (iii) is CLOSED. The rest of W2 is now decomposed into ordered
single-commit slices in the **W2 slice plan** below (settled by the
2026-07-09 anchor recon). **Next concrete commit = slice W2-3: write
appendix subsection (ii), the scaffolding arc** — a pure appendix-prose
commit, read-only harvest, *no* compression (the compression is decoupled
to slices W2-7/W2-8; see the plan's flagged deviations for the user).
Register/mechanics unchanged: LaTeX-ify in the appendix's established
register (flat prose, `alltt` code blocks with `\(...\)` math
substitutions — mind the `\sb{...}`/`\sp{...}` subscript gotcha in
`blueprint/CLAUDE.md` *The retrospective appendix*; `\href` commit links),
`verify.sh` + `lint.sh` green, and re-verify every date/sha/claim against
git before writing it down.

## W2 slice plan (settled 2026-07-09 by the anchor recon)

Per-episode source lists live in `notes/FormalizationRetrospective.md`
*Candidate wrong turns + current sources*; this section adds the slice /
compression / anchor layer on top. **Three deviations from the pinned D1
gate are recommended and flagged for the user** (see *Flagged
adjudications*).

### Harvest map (design-doc §-ranges → appendix episode)

- **(ii) scaffolding arc** ("`d=3`-first → general-`d`, scaffolding that
  worked"): ROADMAP §22 (22a–22l) + §23; `Phase22-realization-design.md`
  §0, §1.1, §1.25–§1.26, **§1.33(C)** (the general-`d` reuse map — what
  general `d` reuses / replaces / adds); `Phase23-design.md` §0–§3 (the
  carrier-grade fault line + the CARRIER/CHAIN/ENTRY/ASSEMBLY division +
  why 23a is first); `notes/MolecularConjecture.md` phase table.
- **(iv) abstraction-layer mis-factorings** — two episodes:
  - *`p2/p3_candidateRow`*: `notes/Phase26-cleanup.md` A2 (disposition +
    *Decisions*), `Claim612.lean` doc-comments, `notes/Phase22{e,g,h}.md`;
    `Phase22-realization-design.md` §1.34–§1.35 + §1.40–§1.44.
  - *motion-space splice vs KT block-triangular*: `DESIGN.md` *Match the
    source's argument structure…*, `notes/FRICTION.md` *[process] Phase
    22a*; `Phase22-realization-design.md` §1.12–§1.14.
- **(v) walls from mis-modelling** — two episodes:
  - *member-mapping wall*: `Phase23-design.md` the WHOLE-MATRIX
    RE-ARCHITECTURE arc + the cert arc §(4.44)–§(4.62) (the KT-faithful
    `fromBlocks A 0 C D` cert), `notes/Phase23e.md`, ROADMAP §23.
  - *eq.-(6.12) `+(D−1)` vs `+D` shortfall*: `DESIGN.md` *Constructibility
    recon…*, `notes/FRICTION.md` *[process] Phase 21b*.
- **(vi) process/tracking failures** — two episodes:
  - *`hcontract` dispatch untracked*: `DESIGN.md` *Statement faithfulness
    to the source*, `CLAUDE.md` *Move deferred items*, `blueprint/CLAUDE.md`
    *Case hypotheses are obligations*; `Phase22-realization-design.md`
    §1.54 (the feed audit that surfaced the orphaned Lemma-6.5 arm).
  - *`d=3` Claim-6.12 "dead island" misread*: `notes/Phase26-cleanup.md`
    *Blockers*/*Decisions*, `CLEANUP.md` §B, git history.

### Compression plan (the anchor-preservation constraint)

The recon inventoried who cites each doc and at what granularity:

- **`Phase23-design.md` — recommend LEAVE FROZEN (D1 = no-op for it).**
  It is cited by **137 live Lean-source doc-comment lines** across ≈40
  distinct anchors (§(4.10)…§(4.107.G.5), §(o″), §(o‴)(H.10/I.7.x/I.8.x),
  §I.8.24(4.11)–(4.42)) in `Rank.lean`, `Concrete.lean`, `Chain.lean`,
  `ChainColumn.lean`, `Arm.lean`, `Basic.lean`, `Operations.lean`,
  `ChainExtraction.lean`, `Realization.lean`, `Candidate.lean`,
  `Deficiency.lean`, plus ≈10 cross-cutting pointers. These reference it as
  the **detailed technical archive** down to individual PROBE/LEAF results
  (`§I.8.24(4.31) PROBE 5`, `§(4.71.2) PROBE 2a`, `§(4.53) LEAF-RowOp-1`) —
  content the narrative appendix does **not** reproduce. A ≤3-line-verdict
  compression would break live code references *and* delete referenced
  content; repointing 137 shipped Lean doc-comments is a Lean-comment
  refactor, not a docs-only harvest. This is exactly the frozen-archive
  verdict `notes/MolecularConjecture.md` *Program close* already reached
  (2026-07-07); the harvest does not change it, because the appendix (v)
  episode cites the doc as background, not as a replacement home.
- **`Phase22-realization-design.md` — anchor-preserving body-shrink.**
  Only 5 live-Lean anchors (§1.35, §1.39, §1.41, §1.41(5), §1.42, at
  section — not PROBE — granularity) + ≈35 cross-cutting anchors
  (`DESIGN.md`, `ROADMAP.md`, `notes/BlueprintExposition.md`,
  `notes/MolecularConjecture.md`, `notes/FRICTION.md`) + phase-note
  citers. Strategy: **keep every cited §-heading (§0–§1.71), shrink each
  section body to a ≤3-line verdict, merge only runs of consecutive
  *uncited* sub-recons.** Every anchor still resolves ⟹ **zero repoint**,
  pure docs-only. Target ≈8590 → ≈1500 lines. This is safer than the
  `notes/CLAUDE.md` "collapse the arc to a verdict + repoint citers"
  model, which here would force ≈40 repoints. Must land **after** the
  (ii)+(iv) harvests (the "never before" half of the D1 gate).
- **Anchor inventory verdict:** with the two strategies above, **no
  citer is repointed** — Phase23 stays frozen (all anchors intact),
  Phase22 keeps all cited headings. The only doc edits that touch other
  files are the two D1-tracker updates in slice W2-8.

### Ordered sub-slice list (each = one commit, user-reviewed before landing)

1. **W2-3 — (ii) scaffolding arc.** Write appendix §(ii). Read-only
   harvest per the map. No compression. Gates: `verify.sh` + `lint.sh`
   green; re-verify dates/shas/claims vs git. Phase-note bookkeeping.
2. **W2-4 — (iv) abstraction-layer mis-factorings.** Write appendix §(iv),
   both episodes. Read-only harvest. Split into W2-4a (`p2/p3_candidateRow`)
   / W2-4b (motion-space splice) if either runs long. Gates.
3. **W2-5 — (v) walls from mis-modelling.** Write appendix §(v), both
   episodes. Read-only harvest (Phase23 read frozen). Split W2-5a
   (member-mapping wall) / W2-5b (eq.-(6.12) shortfall) if long. Gates.
4. **W2-6 — (vi) process/tracking failures.** Write appendix §(vi), both
   episodes. **Closes the appendix** (i–vi all written). Gates + the W2
   phase-note close bookkeeping (flip the W2 checklist, set up W3 scope).
5. **W2-7 — D1a: compress `Phase22-realization-design.md`.** Anchor-
   preserving body-shrink (above). Zero repoint. Docs-only. Optionally
   split W2-7a (§0–§1.33) / W2-7b (§1.34–§1.71) for review. Post-commit
   gate: grep the tree for every Phase22 §-anchor and confirm each still
   resolves. Must follow W2-3 and W2-4.
6. **W2-8 — D1b: `Phase23-design.md` disposition (no-op recommended).**
   Record the frozen verdict + the 137-anchor finding in
   `notes/Phase26-cleanup.md` D1 and `notes/MolecularConjecture.md`
   *Program close*; do **not** compress. (If the user instead directs
   compression, it is a separate ≈137-line Lean-doc-comment repoint
   project — out of docs-only scope — not this slice.)

### Question 4 — does the scaffolding-arc episode need anything not in tree?

**No.** ROADMAP §22–23 carries the phase story; `Phase22-realization
-design.md` §1.33(C) + `Phase23-design.md` §1–§3 carry the reuse-map /
carrier-fault-line detail the "scaffolding that worked" narrative needs,
and both docs are intact until their (later) compression slices. The
design docs' **dead-end** sections (the refuted route α/β/γ/D arc; the
motive re-architectures §1.12–§1.14) feed the *wrong-turn* episodes
(iv)/(v), not the (ii) scaffolding narrative — no fact lives only in a
dead-end section that (ii) requires.

### Flagged adjudications (user decisions)

1. **Deviate from "same commit".** The pinned D1 gate bundles compression
   into the harvesting commit. Recommend **decoupling**: episode slices
   (W2-3…6) are pure appendix prose with read-only harvest; compression is
   its own slice(s) (W2-7) *after* the episodes. The "never before"
   ordering is still honored. Reason: compression's anchor concern is
   orthogonal to prose-writing and would otherwise force a non-docs-only,
   anchor-touching commit.
2. **Re-scope D1 for `Phase23-design.md` to frozen (no-op).** Deviates
   from D1's "compress *both* docs"; forced by the 137 live-Lean-anchor
   finding and aligned with the 2026-07-07 program-close decision.
3. **Phase22 compression = anchor-preserving body-shrink, not
   arc-collapse-with-repoint.** Keep every cited heading; zero repoint.
   Deviates from the `notes/CLAUDE.md` design-doc collapse model, which
   here would force ≈40 repoints for no structural gain.

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
