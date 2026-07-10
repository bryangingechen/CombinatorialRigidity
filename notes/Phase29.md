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

**W2-7 (D1a: `Phase22-realization-design.md` compression) — eight slices
done (2026-07-09): §0–§1.67 compressed (8590 → 2935 lines), plus the
stale legacy `## 3/4/5` block hard-collapsed (zero external citers,
confirmed by tree-wide grep), every cited anchor re-verified per slice
at letter granularity, zero repoints. §1.68–§1.71 (the Phase-22j
placement-abstraction recon through L10) remains the full narrative**
— see *Hand-off* for the next slice's exact discipline; per-slice
record in *W2 slice plan* item 5.

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
- [ ] **W2 — harvest + write the appendix, section by section.** The
  appendix itself (subsections i–vi) is now **fully written** (below); what
  remains before this item closes is the D1 closed-arc compression the
  2026-07-09 anchor recon decoupled into its own slices — W2-7
  (`Phase22-realization-design.md` anchor-preserving body-shrink) and W2-8
  (`Phase23-design.md` frozen-disposition write-up) — per the *W2 slice
  plan* below.
  - [ ] **W2-7 — in progress.** Eight slices done (§0–§1.67 + the stale
    legacy `## 3/4/5` block, 8590 → 2935 lines; per-slice record in *W2
    slice plan* item 5). Remaining: §1.68–§1.71 — see *Hand-off*.
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
- [ ] **W3 — final holistic exposition-quality pass.** Not yet scoped:
  the *Scope it once W2 closes* trigger fires when W2-7/W2-8 (D1
  compression) land, not at the appendix's own completion — deliberately
  left unscoped by this commit (W2-6) per owner instruction, so it isn't
  scoped against a doc set that D1 is still about to compress.
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
  2026-07-09 anchor recon and settled by user adjudication the same day**
  (see *W2 slice plan* → *Compression plan* and *Flagged adjudications*):
  the "never before" ordering holds, but the pinned "in the *same commit*
  as the harvest" clause and the "compress *both* docs" scope do **not**
  survive contact with the inbound-anchor reality — `Phase23-design.md`
  is cited by **137 live Lean-source doc-comment lines** (≈40 distinct
  anchors, down to PROBE/LEAF granularity) and stays **FROZEN** (no
  compression); `Phase22-realization-design.md` (5 live-Lean anchors +
  ≈35 cross-cutting) compresses by an **anchor-preserving body-shrink**
  (keep every cited heading, ≤3-line verdicts, zero repoint) as its
  **own slice after** the episodes that harvest it (W2-7). All three
  deviations are user-ACCEPTED, not merely recommended.
- W3's concrete scope is undefined until W2 closes (deliberate — the
  quality pass should react to what the retrospective surfaces).

## Hand-off / next phase

**Next concrete commit = the W2-7 ninth slice: compress
`notes/Phase22-realization-design.md` §1.68 onward** (the Phase-22j
placement-abstraction recon through L10 — the remainder, ~1328 of the
current 2935 lines), same discipline as the eight landed slices
(`1ed2ff41`, `ca60cfdf`, `f38a7ac2`, `1fdb8961`, the fifth §1.60–§1.62
slice, the sixth §1.63–§1.64 slice, the seventh §1.65–§1.66 slice, and
the eighth §1.67-plus-legacy-block slice):

- **The eighth slice's stale-legacy-block collapse is DONE, not a
  residual for this slice:** the `## 3. Per-case producer structure...`
  / `## 4. Risk / scope` / `## 5. One-line recommendation` block (zero
  heading-level external citers, confirmed by tree-wide grep) is
  collapsed to a 12-line `[SUPERSEDED]` blockquote pointing at §1.33 +
  `Phase22a.md`; §1.67 itself compressed to a Citation line + a
  short *slot* paragraph + per-letter (a)–(e) verdicts (194→84 raw
  lines including the collapse note). Zero Lean-file citers were found
  for §1.67 (confirmed); the one prose letter-citer, `Phase22i.md:261,497`
  → §1.67(d) (the two build-time verification items `(b1)`/`(b2)`),
  resolves — both retained verbatim in the compressed (d).
- **Re-derive the cited-anchor inventory for §1.68–§1.71 yourself**
  (grep the whole tree for every `§1.68`/`§1.69`/`§1.70(i)?`/`§1.71`
  occurrence, **letter-level**). Two things this slice found that change
  the picture for the remainder:
  - **§1.68 (110 lines, letters a–g) has real letter-level citers**,
    unlike §1.67: `notes/Phase22j.md` cites `§1.68(c)` (lines 60, 168),
    `§1.68(f)` (lines 45, 82, 119, 178), `§1.68(g)(i)` (line 62), plus
    bare `§1.68` (lines 26, 148, 149); `notes/Phase22k.md:9` cites it
    bare; `notes/model-experiment-archive.md` cites `§1.68(c)`/`§1.68(c)/(d)`
    (rows 119, 121) and `§1.68(f)` (row 122); `ROADMAP.md:680` and
    `notes/MolecularConjecture.md:234` cite it bare. **Confirm this
    inventory yourself before compressing** — do not trust it uncritically
    (the standing discipline every slice has followed).
  - **`notes/model-experiment-archive.md` is itself a dense letter-level
    citer across §1.69–§1.71**, a source not prominent in the §1.65–§1.67
    citer inventories: spot-checked hits include `§1.69(a)/(b)`,
    `§1.69(c)`, `§1.69(d)`, `§1.70(c)`, `§1.70(c′)`, `§1.70(e)`,
    `§1.70(i)`, `§1.70(i.1)` (a sub-sub-letter, one level finer than the
    `### 1.N(x)` header granularity the sixth-slice gotcha already
    flagged), `§1.71(b)`, `§1.71(c)`. Treat it as a first-class citer
    source in the tree-wide grep, same as `Phase22j.md`/`Phase22k.md`/
    the Lean files — it is an archival log, not a phase note, but it
    still lives in the tree and its citations must resolve.
  - Carried forward from the seventh/eighth slices (still unconfirmed
    for this slice's own build): `Deficiency.lean:872,903` → §1.70(c′)
    is a confirmed **Lean-file** citer — re-verify it still resolves
    once §1.70 is compressed.
- Preserve every cited lettered sub-item as its own short (1–4 line)
  verdict; merge only genuinely-uncited letters (still zero merges
  across all eight slices for the numbered `### 1.xx` sections). **Zero
  repoints** for the numbered sections.
- §1.70 alone is ~552 lines plus its §1.70(i) continuation (~163
  lines) — by far the largest remaining chunk. A further sub-boundary
  within §1.68–§1.71 is likely (e.g. §1.68 alone as the ninth slice,
  given its real letter-citer inventory deserves care; §1.69 next;
  §1.70/§1.70(i) as their own slice(s) given the size + the dense
  model-experiment-archive.md citations; §1.71 last). Draw it at build
  time, as each prior slice has, and return honestly partial if needed.
- Post-edit gate (every prior slice ran it): re-grep the tree for every
  cited §-anchor in the range, letter-level, and confirm each resolves
  in the shrunk file. The fifth through eighth slices did this with a
  small Python tree-walk (regex matching `1\.\d+(?:\([a-zA-Z0-9\-′″]+\))?`
  header labels, cross-checked against `### 1\.N`/`### 1\.N(x)` headers
  + `**(letter)**` sub-headings, run against the WHOLE tree including
  the design doc's own later sections to catch internal
  forward-references) rather than ad-hoc grep — reuse that approach
  (the eighth slice's script is disposable, written fresh each time; no
  need to hunt for a saved copy). **One gotcha, still relevant for
  §1.70(i):** a naive header-position dict keyed only by section number
  mis-locates a section's span when a later `### 1.N(x)` sub-header
  reuses the same leading number — track header *labels* (`"1.70"` vs
  `"1.70(i)"`), not bare numbers (this slice's script used a
  lookahead-assertion regex, `(?=[\s:])` after the optional
  parenthetical, rather than `\b`, to capture the parenthetical
  correctly — a plain `\b` after an optional `(...)` group backtracks
  the group away whenever the char after `)` is itself non-word, e.g. a
  space, silently losing the `(i)`/`(c′)` suffix).

After W2-7 fully closes: **W2-8** (the `Phase23-design.md`
frozen-disposition write-up, a no-op recording — slice plan item 6), then
**W3 scoping** (deliberately deferred until W2-7/W2-8 land — see *Work
items*), then W4; then the phase-close checklist (`PHASE-BOUNDARIES.md`).

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
5. **W2-7 — D1a: compress `Phase22-realization-design.md` — IN PROGRESS.**
   Anchor-preserving body-shrink (above). Zero repoint (for the numbered
   `### 1.xx` sections). Docs-only. Eight slices DONE (2026-07-09), each
   with a post-edit tree-wide anchor re-grep confirming every cited anchor
   resolves. Byte counts + the one distinguishing fact per slice: §0–§1.49
   (8590→6655, section-level anchors only); §1.50–§1.53 (6656→5606, the
   slice that found letter-level citation is the norm, not the exception);
   §1.54–§1.56 (5606→5147, 13 all-prose anchors); §1.57–§1.59 (5147→4421,
   2 Lean-file citers, `PanelLayer.lean:2124`/`Reduction.lean:734`);
   §1.60–§1.62 (4421→3956, 1 Lean-file citer, §1.62's bare anchor
   load-bearing for §1.68–§1.70's later prose despite its own letters
   being barely cited); §1.63–§1.64 (3956→3520, 2 letters already
   SUPERSEDED-in-prose but kept as named 4-line pointers per the zero-merge
   policy); §1.65–§1.66 (3520→3197, 14 lettered sub-items, 4 of §1.65's 7
   letters inverted/superseded by §1.66's corrected route — kept as named
   verdicts stating the *actual* disposition rather than §1.65's own inline
   claim that "all stand"; the `> Docs-only design pass` audit blockquotes
   and the pinned Lean signature code blocks were dropped/compressed to
   prose, per the §1.63/§1.64 precedent); §1.67 + the stale legacy `## 3/4/5`
   block (3197→2935, zero Lean-file citers and only one lettered prose
   citer — §1.67(d) — found for §1.67 itself; the legacy block hard-collapsed
   to a 12-line pointer, the one section-level exception to the
   anchor-preserving per-letter treatment, sanctioned by its own
   zero-heading-citer confirmation). Zero letters ever merged across
   all eight slices. Full anchor/citer detail: commit history + the
   *Decisions made* cross-cutting-lessons entry. **Remaining: §1.68–§1.71**
   (see *Hand-off*). Must follow W2-3 and W2-4 (satisfied).
6. **W2-8 — D1b: `Phase23-design.md` disposition (no-op, user-ACCEPTED).**
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
  - Zero letters ever merged across all eight slices — a bare-section
    citer or later in-file forward-reference routinely depends on content
    under an individually-uncited letter.
  - Tooling fix (sixth slice): the post-edit gate script must key a
    section's span by full header *label* (`"1.70"` vs `"1.70(i)"`), not
    bare section number, once a `### 1.N(x)` sub-header reuses the same
    leading number.
  - New wrinkle (seventh slice): **a design pass's own internal claims can
    be wrong**, discoverable only by reading the later section that
    corrects them — §1.65's ⚠️ box claimed "(a)–(g) all STAND" but §1.66's
    own text inverts (b) and supersedes (d)/(g); compressed each letter to
    its *actual* disposition rather than the box's blanket claim (a
    compression-scope judgment call, not a new recon). Flag for promotion
    to `CLAUDE.md` *Docstrings are not evidence* if a third design-doc
    compression hits an inline annotation overstating what "stands".
  - The stale, zero-citer legacy block (`## 3. Per-case producer
    structure...` / `## 4` / `## 5`) discovered mid-seventh-slice between
    §1.67 and §1.68 was hard-collapsed to a 12-line pointer in the
    eighth slice, the one section-level exception to the per-letter
    treatment (sanctioned since it has zero heading-level citers, unlike
    every `### 1.xx` section).
  - New citer source found (eighth slice): `notes/model-experiment-
    archive.md` is itself a dense letter-level citer across §1.69–§1.71
    (spot-checked: `§1.69(a)/(b)`, `§1.70(c′)`, `§1.70(i.1)` — a
    sub-sub-letter finer than the sixth-slice header-label gotcha — and
    more), not just `Phase22j.md`/`Phase22k.md`/Lean files. Treat it as a
    first-class citer source in future slices' tree-wide greps.
