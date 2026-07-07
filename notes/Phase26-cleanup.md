# Phase 26 cleanup round — the molecular-program-closing hygiene pass (work log)

**Status:** in progress (opened 2026-07-07) — every executable checklist item
has now landed; only the round-close itself remains, deliberately deferred to
a fabled opus step (see *Hand-off*). A2's disposition was corrected mid-round
(see *Decisions*), its wiring half (A2-w) landed, **A3** (the `lem:case-II`
bridge-decl liveness trace + docstring honesty fix) landed, **B3** (the
multi-label `\cref{a,b}` → "??" fix + `lint.sh` guard) landed and surfaced
**B4**, which has now also landed (the `\subsubsection`-cref "??" reword + a
second `lint.sh` guard) and in turn surfaced **B5**, which has now also
landed (the multi-line 3-label `\cref` fix + a multi-line-aware upgrade to
check 6) — the whole B-"??" family is closed; **D3** closed the stale
`ScrewSpaceCarrier-design.md`; **C1** (the top-~10 long-proof screen across
the molecular layer) landed as a no-op screening pass, as expected; **D2a**
(this commit) reconciled the exposition ledger's accounting, flipping 9 of 13
stale `[pending]` markers to `done` — a separate post-Phase-23 readability
rewrite had already written their exposition without anyone updating the
ledger. No task work is mid-flight.

The post-Phase-26 cleanup round. Doubles as the **program-closing** round for
the molecular-conjecture program (17–26): Phases 24/25/26 shipped without their
own between-phase rounds, and the Phase-23-cleanup *Deferred to a future
dead-code / liveness sweep* carry-over (six items) was explicitly parked for
"a future cleanup round at a phase boundary" (`notes/Phase23-cleanup.md`,
echoed in `notes/Phase26.md` *Hand-off*). This round is that boundary. Round
manual: `CLEANUP.md`.

**Pre-round verification (2026-07-07, before any fix):** whole-project
`lake build` green (2860 jobs); the two headline theorems axiom-clean under
`lean_verify` (`PanelHingeFramework.molecular_conjecture`,
`SimpleGraph.molecule_rank_formula` → `{propext, Classical.choice, Quot.sound}`
only); no `sorry`/`axiom`/`native_decide` in proofs. The round is hygiene, not
correctness.

## Current state

**B1 + A2-i + A2-w + A3 + B3/B4/B5 + D3 landed and committed.** A2's disposition was corrected
(deeper dep-graph analysis, 2026-07-07): the d=3 Case-III Claim-6.12 blueprint section is
**live, not orphaned** — its capstone decl `case_III_claim612_gen` is used by the
general proof, and the "zero incoming `\uses`" was a **dep-graph wiring gap**, not
deadness. A2-w closed that gap. What remains of A2:

- **A2-x** — a *worked-case exposition* of the genuinely-simpler concrete d=3
  argument, **deferred to its own plan** `notes/CaseIII-d3-exposition.md`.

The d=3 `case_III_candidate_dispatch` is **kept** as grounding for that worked-case exposition.

**D3 (2026-07-07):** closed `ScrewSpaceCarrier-design.md` — Part 2 (general-`d` API) subsumed by
Phase-23. Doc-only.

**C1 (2026-07-07):** the top-~10 long-proof screen across the molecular layer, weighted toward
Phase 24–26 files, closed **no-op** — every candidate is already a well-factored, well-documented
multi-step algebraic assembly; no extraction / mathlib-miss / tactic-substitution / cross-proof-
unification candidate surfaced. No code changes.

**D2a (2026-07-07):** reconciled the exposition ledger's accounting
(`notes/BlueprintExposition.md`) — see the checklist entry below for the full
per-entry breakdown. Doc-only; no Lean or blueprint `.tex` touched.

**Executable next steps:** none remain — D2a was the round's last checklist
item. The round is ready to **close** (flip the ROADMAP cleanup row, compress
this note, sync user-facing status surfaces, record the deferred
exposition-family follow-ons); that close is a fable-mapped step queued at
opus (see *Hand-off*), not performed in this commit. **D1** and the two
exposition tasks stay deferred (see *Separately-planned*).

## Lemma checklist (the round's task list, A–D)

Each `[ ]` is its own commit (or small cluster). Items carried from
`notes/Phase23-cleanup.md` *Deferred …* are tagged `(P23-carry #n)`.

### A/B — dead-code + blueprint honesty (the core)

> **Liveness lesson (this round, the hard way).** "Zero incoming `\uses`" or
> "zero grep callers" does **not** prove a decl/section dead. A decl can be live
> via a `_gen` sibling while the blueprint under-wires its `\uses`; the d=3
> Claim-6.12 section looked orphaned by both signals yet is load-bearing. Before
> retiring anything, trace the **actual Lean call chain to the main theorem**
> (`lean_references` transitively, or a trial-delete + full rebuild). Applies to
> A3 below. (Lifted to `CLEANUP.md` §B.)

- [x] **B1. Delete `case_I_dispatch`** (P23-carry #3). Was an unpinned zero-caller
  `d=3` `k:=2` wrapper of the live `case_I_dispatch_gen`; deleted. Green + lint.
- [x] **A2-i. Cut two truly-redundant decls.** Deleted the pure `(k:=2)` wrapper
  `case_III_claim612` (its one caller re-pointed to `case_III_claim612_gen`) and
  the obsolete zero-caller `exists_hduality_witness_of_panel_incidence`; node
  `lem:case-III-claim612` re-pinned to `_gen`. −115 lines; green + checkdecls + lint.
  (Correct under the corrected understanding too — these two were genuinely dead.)
- [x] **A2-w. Fix the general-path dep-graph wiring.** Traced the actual Lean
  chain: `chainData_fire_discriminator` (pins `lem:case-III-chain-discriminator`)
  → `exists_shared_redundancy_and_matched_candidate` →
  `exists_chainData_discriminator_pick` (`Realization.lean:1581`) →
  `exists_complementIso_ne_zero_of_homogeneousIncidence_gen`
  (`Claim612.lean:1432`), which calls `case_III_claim612_gen`
  (`lem:case-III-claim612`) directly and then
  `exists_line_data_of_homogeneousIncidence_gen` +
  `extensor_join_proportional_complementIso_meet` — the general-grade form of
  the point-join/panel-meet duality (`lem:case-III-claim612-line-in-panel-union`).
  Added both as `\uses` on `lem:case-III-chain-discriminator`'s proof + one
  clarifying prose clause. `inv web` confirms the dep-graph transitively reduces
  the old `-extensor-span`/`-orthseq-vanish` direct edges (now reachable via the
  new `lem:case-III-claim612` edge) and both target nodes gain an outgoing edge
  (no longer sources). `verify.sh` + `lint.sh` green.
- [ ] **A2-x. d=3 worked-case exposition — DEFERRED** → `notes/CaseIII-d3-exposition.md`.
  Keep `case_III_candidate_dispatch` + its d=3 helpers (a genuinely-simpler worked
  case, not dead code); write it up as the concrete on-ramp to the general
  Lemma 6.13. Substantive exposition-writing, not hygiene — scoped separately.
- [ ] **A2-keep. p2/p3 cluster stays.** `linearIndependent_sum_{p2,p3}_candidateRow`
  (+ selectors) + `candidateRow_ne_zero` are dead general-`k` lemmas **but** they
  exactly ground the nodes `-p2/p3-placement` / `-r-nonzero`. Per owner priority
  (keep formalization grounding exposition), they are **retained**, not cut. No
  action — recorded so a later sweep does not re-flag them.
- [x] **A3. `lem:case-II` bridge decls — dead-but-exposit-live-math; KEPT + honesty fix**
  (P23-carry #2). Traced both pinned decls (`isInfinitesimallyRigidOn_insert_iff`
  `Pinning.lean:1632`; `rankHypothesis_withNormal_withGraph_iff_finrank_pinnedMotions`
  `PanelHinge.lean:832`) via `lean_references` (each `total:1` = self only) + whole-repo grep
  (no `_gen` sibling, no renamed intermediary): **genuinely zero Lean callers**. But
  `lem:case-II` is a **live** blueprint node (6 real `\uses` edges from
  `lem:case-II-realization-placement` / `-placement-old-rows` / two `panel-layer.tex` nodes), and
  the two decls faithfully formalize its stated KT 6.7/6.8 iff-content (body-hinge `V(G)`-relative
  + panel-layer `withGraph` forms). **Not** live-under-wired and **not** divergence:
  `lem:case-II-realization`'s proof does *not* `\uses{lem:case-II}` and its prose says the
  realization is direct — Lean (`case_II_realization_all_k` re-derives the `+(D−1)` count inline)
  and blueprint agree. Per owner priority (keep formalization grounding a live node), **KEPT**;
  fixed the stale `isInfinitesimallyRigidOn_insert_iff` docstring claim ("the leg the producer
  consumes") to name the true role. No blueprint edit (`lem:case-II` already correctly wired).
  Green + lint + warning-clean.

### B — blueprint lint

- [x] **B3. Multi-label `\cref{a,b}` renders as "??"** (P23-carry #5). Confirmed
  root cause by rebuild: plastex's `cleveref.py` shim (`.venv/.../plasTeX/
  Packages/cleveref.py`) subclasses the base `ref` command, whose `args =
  'label:idref'` takes exactly one `\idref` token — unlike real LaTeX
  cleveref, it has no comma-list parser, so `\cref{a,b}`'s whole argument is
  looked up as one (unresolvable) label and renders as the literal string
  "??". Fixed all 9 instances by splitting into `\cref{a} and \cref{b}`
  (`extensor.tex`, `deficiency.tex`, `executable.tex`, `body-hinge.tex` ×3,
  `molecular-induction.tex` ×2, `algebraic-induction/case-iii.tex`); verified
  by rebuild (`inv bp && inv web`) that all 9 target sentences now render a
  real number instead of "??". Added `lint.sh` check 6 (`grep -noE
  '\\[cC]ref\{[^}]*,[^}]*\}'`), sanity-tested against a synthetic multi-cref
  fixture. `verify.sh` + `lint.sh` green.
- [x] **B4. `\subsubsection`-level `\cref`/`\S\ref` renders as "??"** (found by
  B3's rebuild verification, 2026-07-07; distinct root cause from B3). Fixed
  via approach (a): reworded all 9 referencing sentences (8 in `case-iii.tex`
  at the lines the checklist named, plus a 9th in `genericity-and-count.tex`
  the initial scan missed) to name the target in prose ("the
  candidate-completion above/below", "Claim~6.12 above/below", or the
  descriptive title) instead of `\cref`/`\S\ref`-ing the unnumbered
  `\subsubsection` label; the two `\label`s themselves stay (unreferenced,
  matching `laman-theorem.tex`'s six label-less subsubsections). Did **not**
  promote to `\subsection` (option (b), which needed owner sign-off and
  wasn't taken). Added `lint.sh` check 7: detects a `\subsubsection`-level
  label by the on-its-own-line invariant (mirrors check 3's), then flags any
  `\cref`/`\Cref`/`\ref`/`\S\ref` targeting one; sanity-tested by
  reintroducing one of the 9 refs into a scratch copy and confirming the
  guard fires, then reverting. `inv web` confirms zero "??" remain from
  this bug (whole-corpus grep, not just the target page). `verify.sh` +
  `lint.sh` green.
- [x] **B5. A 10th "??": multi-line multi-label `\cref` `case-iii.tex:789-790`**
  (found by B4's whole-corpus "??" grep, 2026-07-07; pre-existing since
  2026-07-04, commit `7c8f86460` — predates this round). Split the
  `\cref{lem:case-II-realization-placement,lem:case-III-claim612-p2-placement,%`
  / `lem:case-III-claim612-p3-placement}` into three single-label
  `\cref`s (matching B3's `\cref{a}, \cref{b}, and \cref{c}` shape).
  Extended `lint.sh` check 6 to be multi-line-aware (joins a
  `%`-terminated line with its successor, TeX's line-continuation idiom,
  before matching) rather than keeping the single-line-only guard that
  let this instance slip past B3 — sanity-tested by reintroducing the bug
  into the live file, confirming the guard fires at the right line, then
  reverting. Whole-corpus post-fix "??" grep on the rendered HTML
  (`grep -ro '??' blueprint/web/*.html`) returns zero — the entire
  B-"??" family (B3/B4/B5) is closed. `verify.sh` + `lint.sh` green.

### C — long-proof audit (screening; expected mostly no-op)

- [x] **C1. Top-~10 long-proof screen** across the molecular layer (24–26 files
  esp.; 17–23 had dedicated perf passes). Ran the `CLEANUP.md` §C LoC-ranking
  `awk` script two ways (fixed to key on per-file `FNR`, not the raw `NR` the
  script's multi-file form bleeds across file boundaries with): (a) the whole
  `Molecular/` tree (41 files, 53,833 lines) — the top-10 is dominated by
  Phase 17–23 decls already covered by their dedicated perf passes
  (`PanelHingeFramework.case_II_realization_all_k`, 931 lines, is the
  documented calibration case — `CLEANUP.md` §C *Calibration (Phase 22j …)* /
  `notes/PERFORMANCE.md`; the `ForestSurgery/` splits are `notes/Phase22l-
  perf.md`), confirming re-auditing them here would duplicate that work; (b)
  scoped to the Phase 24–26 files (`Molecular/Molecule/*.lean`,
  `GenericRigidityMatroid.lean`, `SquareGraph.lean`,
  `GeneralPositionPlacement.lean`) — the top ~10 there run 46–94 lines
  (`Theorem56.lean:88,210`; `GeneralPositionPlacement.lean:115,180`;
  `Modelling.lean:87`; `GeneralPosition4.lean:197`;
  `GenericRigidityMatroid.lean:67`; `Application.lean:108`;
  `ScrewVelocity.lean:78,447,552`), an order of magnitude below the whole-tree
  top and below the ~900-line calibration case. Read all of them in full and
  walked the five-question §C gate (API extraction / missed mathlib lemma /
  tactic substitution / definitional refactor / cross-proof unification) on
  each: every one is a genuine multi-step algebraic assembly (projective-pole
  bridge, polynomial-avoidance certificate, cross-product / screw-
  determination solve) already sectioned into named `-- Step N` comments with
  a module-doc walkthrough; no missed mathlib lemma (each rewrite chain is
  single-purpose bespoke algebra, not glue), no tactic substitution
  (`grind`/`linear_combination`-shaped), no definitional refactor, and no
  cross-proof unification candidate (the three `exists_isGeneralPosition*
  Placement`-shaped siblings rhyme in name only — their per-step content
  diverges, matching the §C calibration note that sibling long proofs
  typically resist a shared combinator). **No-op**, as expected. No code
  changes.

### D — project-organization compression

- [ ] **D1. Compress the two oversized closed design docs — DEFERRED this round**
  (owner call). `notes/Phase22-realization-design.md` (8590 lines) +
  `notes/Phase23-design.md` (5379) are past the ~1500-line `*-design.md` tripwire —
  but they are the **primary raw-material archive** for the formalization
  retrospective. Compressing now sheds the wrong-turns detail it draws on. **Hold**
  until the retrospective is scoped/written, then compress in step with harvesting.
- [x] **D2a (reconcile-only; re-scoped by owner 2026-07-07). Reconcile the exposition
  ledger's ACCOUNTING** (`notes/BlueprintExposition.md`) — landed 2026-07-07. The
  header's "2 remain pending" was a stale post-22d snapshot; markers had drifted to
  13 `[pending]` / 16 `[done]` (29 entries) with no matching re-check. Per-entry
  `.tex` audit found the **post-Phase-23 blueprint readability rewrite** (R1–R9,
  2026-07-02–05 — a separate cleanup round, unrelated to this one) had already
  written the full followable exposition for **9 of the 13** pending entries, with
  nobody flipping the corresponding marker: Lemma 2.1 (`extensor.tex`), the whole
  KT-Lemma-4.1/forest-surgery family + `lem:removal-deficiency` +
  `lem:reduction-step` (`molecular-induction.tex`, written in Phase 20 itself and
  polished by R5), `def:meet-complement-iso` (`meet.tex`), and four Case-I entries
  — the N6 trifurcation composer, the simplicity-conditioned motive, the eq.-(6.3)
  block-triangular rank-addition mechanism, and Claim 6.4's three-brick assembly
  (`case-i.tex`/`panel-layer.tex`). Flipped those 9 to `done (<pointer>)`; corrected
  the header to **4 pending / 25 done**. The remaining 4 (contraction-simplicity
  mechanism, the two-distinct-body-sets splice framing, the matroid-union/
  contraction crux, Claim 6.4's genericity-vs-general-position bundling) are
  genuinely unwritten — no discussion beyond the bare formalized statement — and
  stay `[pending]`. **Did not** write any missing exposition — that (D2b, ~13 crux
  write-ups for the whole 17–26 program) is deliverable-writing, not hygiene, and
  stays **deferred to the exposition/retrospective effort** (see
  *Separately-planned*). Doc-only; no Lean or blueprint `.tex` touched.
- [x] **D3. Close the stale `ScrewSpaceCarrier-design.md`.** Header says general-`d`
  "part 2" is *deferred to the Phase-23 boundary*, but `ScrewSpace` is already an
  opaque general-`k` `def` (`RigidityMatrix/Basic.lean:115`) — Phase-23 CARRIER work
  subsumed it. Updated the header to DONE + closed the doc (c699e767). Doc-only.
- [x] **D4. FRICTION `[resolved]` archive sweep** — no-op. Zero `[resolved]` entries;
  nothing to migrate to `FRICTION-archive.md`.

## Blockers / open questions

- **A2 liveness — RESOLVED, with a correction** (2026-07-07). Earlier this round the
  d=3 Claim-6.12 section (and the Phase-23 note) was read as a dead/orphaned island.
  Deeper analysis overturned that: `case_III_claim612_gen` is **live** (general chain
  `chainData_dispatch → exists_chainData_discriminator_pick → exists_complementIso…_gen
  → case_III_claim612_gen`), so the section exposits live math; its orphaned *look* is
  a missing `\uses` edge (→ A2-w). The one genuinely-dead decl is the unpinned d=3
  `case_III_candidate_dispatch` (bypassed even at d=3 by the general dispatch) — which
  we **keep** as a worked-case exposition (→ A2-x, `notes/CaseIII-d3-exposition.md`),
  because the d=3 argument is genuinely simpler than the general one (fixed three-panel
  dispatch, single relabel, `⋀²ℝ⁴`, no chain/cycle/block machinery).
- No open blockers. **D2a** landed; every checklist item is now closed except
  the deliberately-deferred **D1**. The round is ready to close (see
  *Hand-off*).

## Hand-off / next phase

The round is hygiene; nothing downstream gates on it (`CLEANUP.md` *What a cleanup
round is not*). A future agent (or `/coordinate-phase`) resumes from any unchecked
`[ ]` in the checklist — each is self-contained, with file/line/decl pointers inline.
Program is otherwise complete: the molecular conjecture + Cor 5.7 are green and
axiom-clean.

**A3 landed (2026-07-07):** the `lem:case-II` bridge decls are dead-but-exposit-live-math —
**KEPT** with a docstring honesty fix; the liveness lesson held.
**B3/B4/B5 landed (2026-07-07):** the 10 multi-label and subsubsection `\cref` "??"
instances fixed; `lint.sh` checks 6–7 added and sanity-tested; whole-corpus post-fix
"??" grep returns zero. The entire B-"??" family is closed.

**D3 landed (2026-07-07):** closed `ScrewSpaceCarrier-design.md`. Part 2 (general-`d` API)
subsumed by Phase-23; ScrewSpace is opaque general-`k` with zero overrides project-wide.
Status flipped to DONE; doc body retained as archival spec.

**C1 landed (2026-07-07):** the top-~10 long-proof screen across the molecular layer closed
no-op, as the §C calibration predicted — see the checklist entry for the LoC ranking (both
whole-`Molecular/`-tree and Phase-24–26-scoped) and the per-candidate gate verdict. No code
changes.

**D2a landed (2026-07-07):** reconciled the exposition ledger's accounting
(`notes/BlueprintExposition.md`) — see the checklist entry above for the full
per-entry breakdown. Flipped 9 of the 13 stale `[pending]` markers to `done`
(a separate post-Phase-23 readability rewrite had already written their
exposition) and corrected the header to **4 pending / 25 done**. Did **not**
write any of the 4 genuinely-missing expositions, nor the wider D2b backlog —
both stay deferred to the exposition/retrospective effort
(*Separately-planned*). Doc-only; no Lean or blueprint `.tex` touched.

**Pinned next (coordinator, 2026-07-07): the round-close.** D2a was the
round's last executable checklist item — every `[ ]` above is now `[x]`
except the deliberately-deferred **D1**. Next: flip the ROADMAP cleanup row
to ✓, compress this note, sync any user-facing status surface, and record the
deferred exposition-family follow-ons (A2-x, D1, D2b, the retrospective).
That close is a fable-mapped step → run it at **opus** (fable out this
session).

## Separately-planned / deferred (not this round; each has its own plan doc)

- **d=3 worked-case exposition** → `notes/CaseIII-d3-exposition.md`. Keep the
  concrete d=3 Case-III dispatch and write it up as the accessible on-ramp to the
  general Lemma 6.13. Exposition-writing (BlueprintExposition-flavored), not hygiene.
- **Formalization retrospective** → `notes/FormalizationRetrospective.md`. Narrative
  of the formalization's wrong turns (now including *this round's* d=3
  dead-vs-live misread). New-synthesis; a deliberate exception to the
  "process lives in git/FRICTION/DESIGN, not live docs" convention. **D1 is held for
  it** (that retrospective's raw archive is the two big design docs).
- **Blueprint exposition write-ups (D2b)** → the 4 `[pending]`
  `BlueprintExposition.md` crux nodes left after D2a's accounting reconciliation
  (the Case-I contraction-simplicity mechanism, the two-distinct-body-sets splice
  framing, the matroid-union/contraction crux, and Claim 6.4's genericity-vs-
  general-position bundling — all in `case-i.tex`/`algebraic-induction.tex`). The
  ledger's own "capture-now / write-later" design puts these at a broadened
  blueprint pass; this small remaining backlog is a substantive exposition task,
  **deferred with the Formalization Retrospective** (owner call 2026-07-07). D2a
  reconciled only the ledger's *accounting*; see its checklist entry above.

## Decisions made during this round

- **D2a (2026-07-07):** exposition-ledger accounting reconciled. The header's
  "2 remain pending" was stale; the ledger had drifted to 13 `[pending]` / 16
  `[done]` (29 entries) since a separate post-Phase-23 blueprint readability
  rewrite (R1–R9, 2026-07-02–05) rewrote most of the algebraic-induction
  chapters without anyone re-checking this ledger against the result. Per-entry
  `.tex` audit found 9 of the 13 pending entries already had their full
  exposition landed; flipped them to `done (<pointer>)`, leaving **4 pending /
  25 done**. Wrote no missing exposition (that stays D2b, deferred with the
  retrospective). Full per-entry breakdown in the checklist entry above and in
  `notes/BlueprintExposition.md` itself.
- **C1 (2026-07-07):** long-proof screen closed no-op. Ran the ranking twice — whole
  `Molecular/` tree (top-10 dominated by Phase 17–23 decls already handled by dedicated perf
  passes, e.g. the documented `case_II_realization_all_k` calibration case) and Phase-24–26
  scoped (top ~10 run 46–94 lines, all already well-sectioned algebraic assemblies). Full
  per-candidate write-up is in the checklist entry above. No code changes; no follow-up item.
- **B5 (2026-07-07):** split the `case-iii.tex:789-790` multi-line 3-label
  `\cref` into three single-label `\cref`s. Upgraded `lint.sh` check 6 from a
  single-line-only grep to a multi-line-aware `awk` scan: joins any line
  ending in a bare `%` (TeX's line-continuation idiom — the trailing `%`
  swallows the newline, gluing the next line's content on directly) with its
  successor before matching `\cref\{[^}]*,[^}]*\}`, so a `\cref{a,b,%\nc}`
  split across a continuation is caught the same as a same-line `\cref{a,b}`.
  Chose the persistent-guard route over a one-time hand-fix + grep (the
  hand-off's stated preference) since the single-line gap is exactly what let
  this instance slip past B3's original guard. Sanity-tested by reintroducing
  the bug into the live file, confirming the guard fires at the correct line,
  then reverting. Whole-corpus `grep -ro '??' blueprint/web/*.html` returns
  zero post-fix — closes the entire B-"??" family (B3/B4/B5).
- **B4 (2026-07-07):** fixed via approach (a) (owner-pinned, not (b)). Reworded all
  9 `\subsubsection`-cref "??" sentences (the checklist's 8 in `case-iii.tex` plus a
  9th in `genericity-and-count.tex` that a plain grep of the two labels turned up) to
  name the target in prose; the two `\label`s stay unreferenced (matches
  `laman-theorem.tex`'s label-less subsubsections — `lint.sh` check 1 only requires
  `\uses`/`\cref` targets to have a label, not the reverse). Added `lint.sh` check 7
  (subsubsection-cref guard): identifies an unnumbered heading's label via the
  on-its-own-line invariant (mirrors check 3's environment-label one, with brace-depth
  tracking past a multi-line `\subsubsection{...}` title), then flags any
  `\cref`/`\Cref`/`\ref`/`\S\ref` targeting one. Sanity-tested (reintroduced a ref
  into a scratch copy, confirmed the guard fires, reverted). A whole-corpus post-fix
  "??" grep (not just the target page) surfaced **B5**, a 10th, pre-existing "??"
  from a distinct multi-line multi-label `\cref` that both B3's fix and its
  single-line check-6 guard missed.
- **B3 (2026-07-07):** confirmed root cause — plastex's `cleveref.py` shim
  extends the base `ref` command (`args = 'label:idref'`, one token), so it
  has no comma-list parser and `\cref{a,b}` renders as literal "??". Fixed
  all 9 instances (`\cref{a} and \cref{b}`); added `lint.sh` check 6
  (multi-label `\cref`/`\Cref` guard), sanity-tested against a synthetic
  fixture. Rebuild-verified all 9 target sentences now show real numbers.
  Surfaced **B4**, a same-symptom-different-cause bug (`\subsubsection`
  headings are unnumbered corpus-wide, so any `\cref`/`\ref` to one renders
  "??" regardless of single/multi-label syntax) — tracked separately, not
  folded into this fix.
- **A3 — `lem:case-II` bridge decls: dead-but-exposit-live-math, KEPT (2026-07-07).**
  `lean_references` on both pinned decls returns `total:1` (self only) + whole-repo grep finds no
  `_gen`/renamed caller: genuinely zero Lean callers. But `lem:case-II` is a live node (6 `\uses`
  edges) whose KT 6.7/6.8 iff the decls faithfully formalize, and `lem:case-II-realization`
  bypasses it (its proof omits `\uses{lem:case-II}`; `case_II_realization_all_k` re-derives the
  count inline) — case (ii), not (i) live-under-wired or (iii) divergence. Kept per owner priority;
  honesty fix corrected the stale `isInfinitesimallyRigidOn_insert_iff` "leg the producer consumes"
  docstring. No blueprint change.
- **A2 disposition — CORRECTED (2026-07-07).** Final: the d=3 Claim-6.12 blueprint
  section is **live** (`case_III_claim612_gen` used by the general chain), so it is
  neither demoted nor its nodes cut. Remaining A2 (now that A2-w has landed, see
  below) = the deferred worked-case exposition A2-x. `p2/p3_candidateRow`
  + `candidateRow_ne_zero` are **kept** (they ground exposition nodes). The one
  genuinely-dead decl, `case_III_candidate_dispatch`, is **kept** as worked-case
  grounding (the d=3 argument is genuinely simpler than the general one). *(Supersedes
  the intra-session "demote as non-load-bearing / delete p2/p3" plan — that read was
  wrong; git has the arc.)*
- **Liveness lesson lifted** → `CLEANUP.md` §B (verify liveness against the Lean call
  chain, not `\uses`/grep alone). Applies to A3.
- **A2-w (2026-07-07):** added the missing `\uses` edges — `lem:case-III-claim612`
  and `lem:case-III-claim612-line-in-panel-union` — to `lem:case-III-chain-
  discriminator`'s proof, matching the traced Lean chain (`chainData_fire_
  discriminator → exists_shared_redundancy_and_matched_candidate →
  exists_chainData_discriminator_pick → exists_complementIso_ne_zero_of_
  homogeneousIncidence_gen`, which calls `case_III_claim612_gen` then the
  general-grade join/meet duality). `inv web` shows the old direct edges to
  `-extensor-span`/`-orthseq-vanish` now transitively subsumed; both target
  nodes gain an outgoing edge. Blueprint-only; `verify.sh` + `lint.sh` green.
- **A2-i (2026-07-07):** deleted the `(k:=2)` wrapper `case_III_claim612` (caller
  re-pointed to `case_III_claim612_gen`) + the obsolete zero-caller
  `exists_hduality_witness_of_panel_incidence`. Node `lem:case-III-claim612` → `_gen`.
  −115 lines; green + checkdecls + lint. (Correct under the corrected understanding.)
- **B1 (2026-07-07):** deleted `case_I_dispatch` — a zero-caller, blueprint-unpinned
  `k:=2` wrapper whose body was just `case_I_dispatch_gen (k:=2)`. Green + lint.
- **Retrospective + d=3-exposition planned separately; D1 deferred** — see
  *Separately-planned*.
