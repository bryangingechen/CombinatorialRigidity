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

**W2-7 (D1a: `Phase22-realization-design.md` compression) — THIRD SLICE DONE
(2026-07-09), doc NOT yet fully compressed.** The anchor recon below decomposed D1
into W2-7 (this doc, anchor-preserving body-shrink) + W2-8
(`Phase23-design.md`, frozen no-op). Compressing it found the size distribution far
more lopsided than the recon's line-count estimate suggested: §0–§1.33 (the
motive-decision arc) was already near-verdict-compact (284 lines for 33 sub-recons),
while §1.34–§1.71 (the `d=3`/general-`d` producer's crux architecture — five
different superseded designs for the Case-III six-join dispatch alone) carries
**96% of the file's bulk** in long, heavily-superseded recon chains. The first
slice compressed **§0–§1.49** to ≤3-line verdicts (8590 → 6655 lines, **-1935**);
the second slice compressed **§1.50–§1.53** (6656 → 5606 lines, **-1050**) — see
*Hand-off* for a density correction this slice found in the compression plan's
anchor count. **The third slice compressed §1.54–§1.56** (the Leaf-5 feed-audit,
the user adjudications, and the 22i motive design pass — 5606 → 5147 lines,
**-460**), at the same letter-preserving discipline the second slice pinned;
verified against a full tree-wide re-grep of every `§1.54`/`§1.55`/`§1.56`
citation (64 lines across 10 files), zero repoints. **§1.57–§1.71 (the L0–L10
signature-pin sequence) remains the full narrative** — one or more follow-up
slices must finish it before W2-7 closes (see *Hand-off*).

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
  - [ ] **W2-7 — in progress.** First slice (2026-07-09): §0–§1.49 compressed
    (8590 → 6655 lines). Second slice (2026-07-09): §1.50–§1.53 compressed
    (6656 → 5606 lines). Third slice (2026-07-09): §1.54–§1.56 compressed
    (5606 → 5147 lines). §1.57–§1.71 (the L0–L10 signature-pin sequence,
    ~4320 of the current lines) still needs one or more follow-up slices
    before W2-7 closes — see *Hand-off*.
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

**All six appendix subsections (i)–(vi) are now CLOSED — the appendix is
fully written.** The rest of W2 is the D1 compression. W2-7's first slice
(2026-07-09) compressed `notes/Phase22-realization-design.md` §0–§1.49 to
≤3-line verdicts (8590 → 6655 lines). **Second slice (2026-07-09) compressed
§1.50–§1.53** (6656 → 5606 lines, **-1050**) — the `hcand`-discharge recon
through the W10 design-settle pass (the certify-then-rebase / W-suite arc).

**Correction to the compression plan's anchor count (2026-07-09, discovered
mid-slice).** Re-deriving the cited-anchor inventory for §1.50–§1.53 (the
per-slice discipline this D1 gate requires) found the *Compression plan*
section's "only 5 live-Lean anchors, at section — not PROBE — granularity"
claim badly undercounts: it is true of §0–§1.49, but **§1.50 onward is cited
from ~15 different `.lean` files at LETTER granularity, densely** — e.g.
`RigidityMatrix/Basic.lean` cites §1.50(c) three times, `Claim612.lean` cites
§1.50(a) twice, and essentially every lettered sub-item `(a)`–`(j)` of
§1.50–§1.53 is a live citation target from a Lean doc-comment explaining
*why* a landed producer/leaf has the shape it does (a fundamentally
different citation pattern than §0–§1.49's coarser, mostly-external,
section-level pointers — those sections narrate a still-live design
rationale for already-built Case-III/Case-I code, not superseded
motive-decision history). **Consequence for the compression strategy:**
"≤3-line verdict per section" does not survive contact with this — a
section with N cited letters needs N short (1–4 line) verdicts, one per
letter, not one verdict for the whole section. This slice's compression
therefore preserves every cited lettered sub-item as its own bold `**(x)**`
paragraph (verified against a full tree-wide re-grep post-edit — all letters
`(a)`–`(j)` cited anywhere in the tree for §1.50–§1.53 resolve; see
*Compression plan* for the corrected count), merging only genuinely-uncited
letters (§1.50(d)/(e), each with zero external citations, merged into one
bullet). The overall reduction is accordingly smaller than §0–§1.49's 80%
(here ~84%, mostly from dropping the large inlined Lean-signature code
blocks and "docs-only recon, Lean read this pass" banners — content that
duplicates the now-landed Lean source rather than carrying unique
rationale).

**Third slice (2026-07-09) compressed §1.54–§1.56** (the Leaf-5 feed-audit,
the §1.54 adjudications, and the 22i motive design pass — 5606 → 5147
lines, **-460**). Unlike §1.50–§1.53, this range turned out to have **zero
Lean-file citations** (confirmed by grepping every `.lean` file under
`CombinatorialRigidity/` for `§1.5[456]`: no hits, vs. the dense per-letter
Lean citation of §1.50–§1.53/§1.57/§1.59) — every citer of §1.54–§1.56 is a
`notes/*.md`/`DESIGN.md`/`ROADMAP.md`/`blueprint/CLAUDE.md` prose pointer, at
letter granularity in several cases (`§1.54(a1)`, `§1.54(a3)`, `§1.54(b)`,
`§1.54(c)`, `§1.55(a)`/`(b)`/`(c)`, `§1.56(a)`/`(c)`/`(d)`/`(e)`/`(g)` — 13
distinct lettered anchors across 10 files, 64 citing lines total). This
slice drew its boundary at the hand-off's own suggested split (the Leaf-5
feed-audit + adjudications + motive-design arc, §1.54–§1.56, is one
narrative unit distinct from the L0–L10 signature-pin sequence that
follows) rather than pushing into §1.57, since §1.57 alone is ~320 lines
and already has confirmed Lean-file citations (`PanelLayer.lean` cites
§1.57(b)) — a denser, differently-shaped range best assessed fresh.

**Next concrete commit = the W2-7 follow-up slice: compress §1.57 onward**
(the L0–L10 signature-pin sequence through §1.71 — the remainder, ~4320 of
the current 5147 lines), same discipline as the last three slices:
re-derive the cited-anchor inventory (grep the tree for every
`§1.5[7-9]`/`§1.6[0-9]`/`§1.7[01]` occurrence, letter-level, not just
section-level — expect a MIXED pattern per the confirmed Lean-file hits at
§1.57(b) and §1.59, unlike §1.54–§1.56's all-prose citers), preserve every
cited lettered sub-item as its own short verdict, merge only
genuinely-uncited letters, zero repoint. Given the density (§1.70 alone is
~550 lines, the largest single section in the file), a further
sub-boundary within §1.57–§1.71 is likely needed (assess at build time, as
each prior slice has). Post-commit gate (same as every prior slice ran):
grep the tree for every Phase22 §-anchor, **at letter granularity**, cited
from `DESIGN.md`/`ROADMAP.md`/`notes/BlueprintExposition.md`/
`notes/MolecularConjecture.md`/`notes/FRICTION.md`/phase notes/
`model-experiment-archive.md`/Lean doc-comments, and confirm each still
resolves in the shrunk file. **W2-8** (the `Phase23-design.md`
frozen-disposition write-up, a no-op) and **W3's scoping** (deliberately
not attempted until W2-7/W2-8 land — see *Work items*) follow after W2-7
fully closes.

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

1. **W2-3 — (ii) scaffolding arc — DONE (2026-07-09).** Wrote appendix
   §(ii). Read-only harvest per the map. No compression. Gates:
   `verify.sh` + `lint.sh` green; dates/shas/claims re-verified vs git.
2. **W2-4 — (iv) abstraction-layer mis-factorings — DONE (2026-07-09).** Wrote
   appendix §(iv), both episodes (`p2/p3_candidateRow`; the motion-space
   splice vs. KT block-triangular). Read-only harvest per the map. No
   compression. Gates: `verify.sh` + `lint.sh` green; dates/shas/claims
   (13 commits) and the two live `\cref` targets re-verified vs git.
3. **W2-5 — (v) walls from mis-modelling — DONE (2026-07-09).** Wrote
   appendix §(v), both episodes (the member-mapping wall; the eq.-(6.12)
   shortfall) in one commit (both episodes fit without an a/b split).
   Read-only harvest per the map (`Phase23-design.md` read-frozen). Gates:
   `verify.sh` + `lint.sh` green; 8 commits + the KT primary-source pages
   re-verified vs git/the PDF; print PDF checked at 300dpi for the new
   `alltt` block's subscripts.
4. **W2-6 — (vi) process/tracking failures — DONE (2026-07-09).** Wrote
   appendix §(vi), both episodes (the Case-I dispatch's untracked
   Lemma-6.5 arm; the `d=3` Claim-6.12 "dead island" misread).
   **Closes the appendix** (i–vi all written). Read-only harvest per the
   map. No compression. Gates: `verify.sh` + `lint.sh` green; 12 commits
   re-verified vs git; rendered HTML has zero `??`. W3 scoping deliberately
   deferred to after W2-7/W2-8 (see *Hand-off* + *Work items*).
5. **W2-7 — D1a: compress `Phase22-realization-design.md` — IN PROGRESS.**
   Anchor-preserving body-shrink (above). Zero repoint. Docs-only. **First
   slice DONE (2026-07-09): §0–§1.49 (8590 → 6655 lines); post-edit anchor
   grep confirmed every cited §-heading in that range resolves.** The
   pre-planned W2-7a/W2-7b (§0–§1.33 / §1.34–§1.71) split turned out
   mismatched to the file's actual density (§0–§1.33 was already
   near-compact; §1.34 on is 96% of the bulk) — the working boundary
   became §0–§1.49 instead, decided at build time rather than the
   pre-committed split point. **Second slice DONE (2026-07-09): §1.50–§1.53
   (6656 → 5606 lines); post-edit anchor grep confirmed every cited
   §-heading AND every cited lettered sub-item in that range resolves.**
   This slice found the "5 live-Lean anchors" premise wrong for §1.50
   onward (see *Compression plan*'s correction) and compressed to a
   letter-preserving, not section-preserving, granularity as a result.
   **Third slice DONE (2026-07-09): §1.54–§1.56 (5606 → 5147 lines);
   post-edit anchor grep confirmed all 13 distinct lettered anchors
   (across 10 citing files, 64 lines) resolve.** This range has zero
   Lean-file citers (all citers are `notes/*.md`/`DESIGN.md`/
   `ROADMAP.md`/`blueprint/CLAUDE.md` prose), a different citation shape
   than §1.50–§1.53's dense per-letter Lean doc-comments. **Remaining:
   §1.57–§1.71**, one or more follow-up slices (see *Hand-off*). Must
   follow W2-3 and W2-4 (satisfied).
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
- (W2-7 first + second slice, 2026-07-09) Two recon-estimate corrections,
  both found only by re-deriving the anchor/size inventory at build time
  rather than trusting the phase-open recon: **(1)** the pre-planned
  W2-7a/W2-7b split (§0–§1.33 / §1.34–§1.71) was a natural *content*
  boundary but a poor *size* one (§0–§1.33 is only 284 of 8590 lines;
  §1.34 on carries 96% of the bulk) — re-drawn at §0–§1.49 instead.
  **(2)** the recon's "5 live-Lean anchors" count is true only of §0–§1.49;
  §1.50 onward is cited from ~15 `.lean` files at *letter* granularity
  (every lettered sub-item routinely a live citation target), forcing a
  letter-preserving compression, not section-preserving (see *Compression
  plan*'s correction + the *Hand-off* note). Now a two-occurrence pattern
  (a size/anchor estimate made before reading a file is not a substitute
  for one made while compressing it) — still folded into per-slice hand-offs
  rather than promoted standalone, since both instances are local to this
  one design doc's compression, but flag for promotion to `notes/CLAUDE.md`
  if a third `*-design.md` compression hits the same trap.
- (W2-7 third slice, 2026-07-09) §1.54–§1.56 re-derived cleanly against the
  same letter-preserving discipline as §1.50–§1.53, but with a distinct
  citation shape: **zero Lean-file citers** (confirmed by grepping every
  `.lean` file for `§1.5[456]`) — every citer is `notes/*.md`/`DESIGN.md`/
  `ROADMAP.md`/`blueprint/CLAUDE.md` prose, at letter granularity for 13
  distinct anchors. Drew the boundary at §1.56 (the hand-off's own
  suggestion, and where the Leaf-5/22i motive-design narrative arc ends)
  rather than pushing into §1.57, which already has a confirmed Lean-file
  citer (`PanelLayer.lean` §1.57(b)) and belongs to the denser L0–L10
  signature-pin sequence.
