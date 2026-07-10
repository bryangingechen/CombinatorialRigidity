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

**W2 appendix-writing DONE (2026-07-09) — all six subsections (i)–(vi) written,
10 episodes across the taxonomy; `blueprint/verify.sh`/`lint.sh` green throughout,
every date/sha/Lean statement re-verified against `git show`/`git log` (and, for
subsection (v), the KT primary-source PDF directly) before writing, no factual
errors found in any slice.** One line per slice: the opening commit landed the
chapter scaffold + the `\appendix`/`alltt` mechanics + (i) the chapter intro +
(iii)'s first (pinned) episode; the second slice closed (iii) (KT Lemma-4.1
over-quantification; the Claim-6.12 fixed-candidate-disjunction → six-join
existential); **W2-3** wrote (ii) the scaffolding arc; **W2-4** wrote (iv), both
abstraction-layer mis-factoring episodes; **W2-5** wrote (v), both mis-modelling-wall
episodes; **W2-6** wrote (vi), both process/tracking episodes, closing the appendix.
Full per-slice detail: git history on `blueprint/src/chapter/retrospective.tex` +
`notes/FormalizationRetrospective.md` *Candidate wrong turns + current sources*.

**W2-7 (D1a: `Phase22-realization-design.md` compression) — DONE (2026-07-09),
twelve slices: §0–§1.71 compressed (8590 → 1939 lines), plus the stale
legacy `## 3/4/5` block hard-collapsed (zero external citers, confirmed by
tree-wide grep), every cited anchor re-verified per slice at letter
granularity, zero repoints throughout. The twelfth slice closed §1.71
(the L10 signature pin, the design doc's last numbered section), merging
its one genuinely-uncited letter `(e)` into `(d)`; full per-slice record
in *W2 slice plan* item 5. **W2-7 CLOSED.**

**W2-8 (D1b: `Phase23-design.md` frozen-disposition write-up) — DONE
(2026-07-09), a no-op recording, as planned: `notes/Phase26-cleanup.md`
D1 flipped to closed (recording the Phase22 compression outcome + the
Phase23 freeze) and `notes/MolecularConjecture.md` *Program close*
corrected — its 2026-07-07 text called both design docs "frozen in
place"; now distinguishes the two docs' actual dispositions. No
compression of `Phase23-design.md` (still 137-anchor FROZEN). **W2-8
CLOSED, and with it W2** (appendix i–vi + both D1 slices all done).

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
- [x] **W2 — harvest + write the appendix, section by section. CLOSED
  (2026-07-09).** The appendix (subsections i–vi) is fully written; the D1
  closed-arc compression the 2026-07-09 anchor recon decoupled into its own
  slices — W2-7 (`Phase22-realization-design.md` anchor-preserving
  body-shrink) and W2-8 (`Phase23-design.md` frozen-disposition write-up) —
  is done, per the *W2 slice plan* below.
  - [x] **W2-7 — DONE (2026-07-09).** Twelve slices, §0–§1.71 compressed
    (8590 → 1939 lines; per-slice record in *W2 slice plan* item 5).
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
- [ ] **W3 — final holistic exposition-quality pass.** Not yet scoped. The
  *Scope it once W2 closes* trigger has now fired (W2-8 just closed W2,
  this commit) — scoping W3 is the next concrete task, see *Hand-off*.
- [ ] **W4 — `formalization.yaml` automation-metadata refresh.** The
  phase-open commit repaired the *status* drift (scope / main_results /
  alignment / fidelity, backfilled for phases 22k–26 with `#print
  axioms` checks); the *automation* section's how-it-was-produced
  metadata (models list, session counts, wall time) still describes the
  2026-06-07 state. A retrospective phase is the right place to
  reconstruct it accurately.

## Blockers / open questions

None currently open. **The D1 gate is discharged (2026-07-09):** both
slices landed — W2-7 compressed `Phase22-realization-design.md`
(anchor-preserving body-shrink, zero repoint), W2-8 froze
`Phase23-design.md` (137-anchor finding) and recorded both dispositions.
The three flagged deviations from the pinned gate (decouple compression
from harvest-commit; freeze Phase23 as a D1 no-op; body-shrink not
arc-collapse for Phase22) are all user-ACCEPTED — detail in *Decisions
made* and *W2 slice plan* → *Flagged adjudications*. W3's concrete scope,
previously undefined until W2 closed, is the next task (*Hand-off*), not
an open blocker.

## Hand-off / next phase

**W2-8 CLOSED (2026-07-09) — and with it W2, in full.** The
`Phase23-design.md` frozen-disposition write-up landed as a no-op
recording in two places: `notes/Phase26-cleanup.md` D1 flipped from
"DEFERRED" to closed (recording the `Phase22-realization-design.md`
compression outcome — 12 slices, 8590→1939, anchor-preserving, zero
repoints — and the `Phase23-design.md` freeze); `notes/MolecularConjecture.md`
*Program close* corrected — its 2026-07-07 text called *both* design docs
"frozen in place as §-cited archives", now stale for
`Phase22-realization-design.md` (compressed by W2-7, not frozen) and
distinguishes the two docs' actual dispositions. `Phase23-design.md`
itself was **not** touched (137-anchor FROZEN finding stands). Full W2-7
twelfth-slice detail (the §1.71 letter-merge, the STATUS-blockquote fold,
the citation re-confirm) is recorded in *Current state* and *W2 slice
plan* item 5 — not restated here. **W2 is now fully closed**: appendix
(i–vi, 10 episodes) + both D1 slices (W2-7, W2-8) all done.

**Next concrete commit = W3 scoping.** Per *Scope* and *Work items*, W3
("final holistic exposition-quality pass") was deliberately left unscoped
until W2 closed — that trigger has now fired. The next session should
re-read the appendix (`blueprint/src/chapter/retrospective.tex`, all six
subsections) alongside the now-compressed `Phase22-realization-design.md`
and the still-frozen `Phase23-design.md`, and turn "final holistic
exposition-quality pass" into a concrete, ordered checklist (which
chapters/files, what kind of pass — readability vs. cross-reference
consistency vs. a fresh top-to-bottom register check against
`blueprint/AUTHORING.md`) before doing any of it. After W3 is scoped and
run, **W4** (`formalization.yaml` automation-metadata refresh) is the
remaining work item, then the phase-close checklist
(`PHASE-BOUNDARIES.md`).

## W2 slice plan (settled 2026-07-09 by the anchor recon)

Per-episode source lists live in `notes/FormalizationRetrospective.md`
*Candidate wrong turns + current sources*; this section adds the slice /
compression / anchor layer on top. **Three deviations from the pinned D1
gate were flagged for the user and ACCEPTED 2026-07-09** (see *Flagged
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
  **Corrected 2026-07-09 (mid W2-7 second slice) — the original "5
  live-Lean anchors" count below is WRONG for §1.50 onward**, discovered by
  re-deriving the inventory per-slice as the D1 gate requires rather than
  trusting this recon's original count: §0–§1.49 does have only 5 live-Lean
  anchors, all at section granularity, but **§1.50–§1.71 is cited from
  ~15 `.lean` files at LETTER granularity, densely** (every lettered
  sub-item of a section is typically a live citation target from a Lean
  doc-comment explaining a landed producer's design rationale — see the
  *Hand-off* correction note for detail and the W2-7 second-slice commit
  for the worked example, §1.50–§1.53). The original count + ≈35
  cross-cutting anchors (`DESIGN.md`, `ROADMAP.md`,
  `notes/BlueprintExposition.md`, `notes/MolecularConjecture.md`,
  `notes/FRICTION.md`) + phase-note citers still holds for §0–§1.49.
  Strategy, corrected: **keep every cited §-heading AND every cited
  lettered sub-item (§0–§1.71), shrink each to a ≤3-line verdict (one per
  cited letter where a section has several), merge only runs of
  consecutive *uncited* sub-recons/letters.** Every anchor still resolves
  ⟹ **zero repoint**, pure docs-only — this constraint is unchanged by the
  correction, only the compression ratio is smaller than the original
  ≈1500-line target for §1.50 onward (the second slice's §1.50–§1.53 ratio,
  ~84%, is a more realistic estimate than the original ≈83%-of-8590
  target). This is safer than the `notes/CLAUDE.md` "collapse the arc to a
  verdict + repoint citers" model, which here would force far more than
  ≈40 repoints. Must land **after** the (ii)+(iv) harvests (the "never
  before" half of the D1 gate).
- **Anchor inventory verdict:** with the two strategies above, **no
  citer is repointed** — Phase23 stays frozen (all anchors intact),
  Phase22 keeps all cited headings. The only doc edits that touch other
  files are the two D1-tracker updates in slice W2-8.

### Ordered sub-slice list (each = one commit, user-reviewed before landing)

1. **W2-3 — (ii) scaffolding arc — DONE (2026-07-09).**
2. **W2-4 — (iv) abstraction-layer mis-factorings — DONE (2026-07-09).**
3. **W2-5 — (v) walls from mis-modelling — DONE (2026-07-09).**
4. **W2-6 — (vi) process/tracking failures — DONE (2026-07-09); closed
   the appendix** (i–vi all written; per-slice gates + verification
   detail in the commit messages).
5. **W2-7 — D1a: compress `Phase22-realization-design.md` — DONE
   (2026-07-09), CLOSED.** Anchor-preserving body-shrink (above). Zero
   repoint (for the numbered `### 1.xx` sections). Docs-only. Twelve
   slices, §0–§1.71, **8590 → 1939 lines**, zero repoints throughout; every
   slice ran a post-edit tree-wide anchor re-grep confirming every cited
   anchor resolves. Three letter-pair merges (§1.69 (e)/(f); §1.70 original
   (g)/(h); §1.71 (e) folded into (d), the first with no adjacent uncited
   partner); one legacy-block hard-collapse (§1.67's stale `## 3/4/5`,
   zero heading-citers); one STATUS-blockquote fold-into-citing-letters
   (§1.71, rather than blanket-drop). Per-slice byte counts + the
   distinguishing fact of each: git history (each slice's own commit
   message) + the *Decisions made* cross-cutting-lessons entry — not
   duplicated here.
6. **W2-8 — D1b: `Phase23-design.md` disposition (no-op, user-ACCEPTED) —
   DONE (2026-07-09), CLOSED.** Recorded the frozen verdict + the
   137-anchor finding in `notes/Phase26-cleanup.md` D1 (flipped to closed)
   and `notes/MolecularConjecture.md` *Program close* (corrected to
   distinguish the two docs' dispositions); did **not** compress
   `Phase23-design.md`. **This closes W2** (appendix + both D1 slices all
   done) — next is W3 scoping (*Hand-off*).

### Question 4 — does the scaffolding-arc episode need anything not in tree?

**No.** ROADMAP §22–23 carries the phase story; `Phase22-realization
-design.md` §1.33(C) + `Phase23-design.md` §1–§3 carry the reuse-map /
carrier-fault-line detail the "scaffolding that worked" narrative needs,
and both docs are intact until their (later) compression slices. The
design docs' **dead-end** sections (the refuted route α/β/γ/D arc; the
motive re-architectures §1.12–§1.14) feed the *wrong-turn* episodes
(iv)/(v), not the (ii) scaffolding narrative — no fact lives only in a
dead-end section that (ii) requires.

### Flagged adjudications (user decisions — ALL THREE ACCEPTED 2026-07-09)

1. **Deviate from "same commit" — ACCEPTED.** The pinned D1 gate bundles
   compression into the harvesting commit. Decoupled instead: episode
   slices (W2-3…6) are pure appendix prose with read-only harvest;
   compression is its own slice(s) (W2-7) *after* the episodes. The
   "never before" ordering is still honored. Reason: compression's anchor
   concern is orthogonal to prose-writing and would otherwise force a
   non-docs-only, anchor-touching commit.
2. **Re-scope D1 for `Phase23-design.md` to frozen (no-op) — ACCEPTED.**
   Deviates from D1's "compress *both* docs"; forced by the 137
   live-Lean-anchor finding and aligned with the 2026-07-07 program-close
   decision.
3. **Phase22 compression = anchor-preserving body-shrink, not
   arc-collapse-with-repoint — ACCEPTED.** Keep every cited heading; zero repoint.
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
- (W2-7, 2026-07-09) **Per-slice byte/anchor/citer detail lives in *W2
  slice plan* item 5, not duplicated here** (rebalanced 2026-07-09 seventh
  slice — this entry previously restated it in full, tipping the note
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
