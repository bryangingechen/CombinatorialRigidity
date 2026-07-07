# Phase 26 cleanup round — the molecular-program-closing hygiene pass (work log)

**Status:** in progress (opened 2026-07-07). A2's disposition was corrected
mid-round (see *Decisions*), its wiring half (A2-w) landed, **A3** (the
`lem:case-II` bridge-decl liveness trace + docstring honesty fix) landed, and
**B3** (the multi-label `\cref{a,b}` → "??" fix + `lint.sh` guard) has now
landed, surfacing a distinct follow-on finding (**B4**, tracked below); the
round otherwise continues via the remaining checklist items. No task work is
mid-flight.

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

**B1 + A2-i + A2-w landed and committed. A2's disposition was corrected** (deeper
dep-graph analysis, 2026-07-07): the d=3 Case-III Claim-6.12 blueprint section is
**live, not orphaned** — its capstone decl `case_III_claim612_gen` is used by the
general proof, and the "zero incoming `\uses`" was a **dep-graph wiring gap**, not
deadness (see *Blockers*). The Phase-23 note's "dead code described as live"
framing was wrong. So A2 is **not** a demote/delete task. A2-w has now closed that
wiring gap; what remains of A2:

- **A2-x** — a *worked-case exposition* of the genuinely-simpler concrete d=3
  argument, **deferred to its own plan** `notes/CaseIII-d3-exposition.md`.

The genuinely-dead decl (`case_III_candidate_dispatch`) is being **kept** as the
grounding for that worked-case exposition — it is not retired.

**Executable next steps** for a future agent / `/coordinate-phase` session, in any
order (none blocks another): **B4**, **C1**, **D2**, **D3**.
Each is a self-contained commit. **D1** and the two exposition tasks are deferred
(see *Separately-planned*).

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
- [ ] **B4. `\subsubsection`-level `\cref`/`\S\ref` renders as "??"** (found by
  B3's rebuild verification, 2026-07-07; distinct root cause from B3, not
  folded in). `\subsubsection` headings render with no visible number
  corpus-wide (e.g. `laman-theorem.tex`'s six `<h3>`s carry no number) — the
  web build's `secnumdepth` effectively excludes depth-3 headings — so a
  `\cref`/`\ref` to a `\subsubsection`-level `\label` can never produce a
  number (real LaTeX would show the same "??" once a heading level is
  outside `secnumdepth`/`tocdepth`; this is a document-authoring bug, not a
  plastex one). Two `case-iii.tex` subsubsections are affected:
  `sec:molecular-algebraic-induction-candidate-completion` (referenced at
  lines 12, 309, 597, 1095) and `sec:molecular-algebraic-induction-claim612`
  (lines 14, 350, 435, and 1205 via `\S\ref`) — 9 "??" remain in
  `sec-molecular-algebraic-induction.html` (confirm count after any edit
  before/after). Needs a scoping decision before landing: (a) reword the 8
  referencing sentences to name the subsubsection by prose instead of a
  numbered ref (matches how the corpus's other `\subsubsection`s are never
  cross-referenced), or (b) promote the two to `\subsection` (visual/TOC
  change to the chapter). Subagent-friendly once the (a)-vs-(b) call is made.

### C — long-proof audit (screening; expected mostly no-op)

- [ ] **C1. Top-~10 long-proof screen** across the molecular layer (24–26 files
  esp.; 17–23 had dedicated perf passes). Run the `CLEANUP.md` §C LoC ranking, walk
  the four-question gate. Expect no-op per the §C calibration; record findings.

### D — project-organization compression

- [ ] **D1. Compress the two oversized closed design docs — DEFERRED this round**
  (owner call). `notes/Phase22-realization-design.md` (8590 lines) +
  `notes/Phase23-design.md` (5379) are past the ~1500-line `*-design.md` tripwire —
  but they are the **primary raw-material archive** for the formalization
  retrospective. Compressing now sheds the wrong-turns detail it draws on. **Hold**
  until the retrospective is scoped/written, then compress in step with harvesting.
- [ ] **D2. Reconcile the exposition ledger** (`notes/BlueprintExposition.md`).
  Header claims "2 remain pending" but markers show 13 `[pending]` / 1 `[done]`. Per
  entry: verify whether its `.tex` prose already carries the exposition; flip to
  `done (<commit>)` if so; write the genuinely-missing ones (at least Lemma 2.1 /
  Phase 17 and the Phase-20 forest-surgery family). Subagent-friendly (per-entry).
- [ ] **D3. Close the stale `ScrewSpaceCarrier-design.md`.** Header says general-`d`
  "part 2" is *deferred to the Phase-23 boundary*, but `ScrewSpace` is already an
  opaque general-`k` `def` (`RigidityMatrix/Basic.lean:115`) — Phase-23 CARRIER work
  subsumed it. Update the header to DONE + close the doc. Doc-only.
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
- No open blockers. All remaining tasks (B3, C1, D2, D3) are executable.

## Hand-off / next phase

The round is hygiene; nothing downstream gates on it (`CLEANUP.md` *What a cleanup
round is not*). A future agent (or `/coordinate-phase`) resumes from any unchecked
`[ ]` in the checklist — each is self-contained, with file/line/decl pointers inline.
Program is otherwise complete: the molecular conjecture + Cor 5.7 are green and
axiom-clean.

**A3 landed (2026-07-07):** the `lem:case-II` bridge decls are dead-but-exposit-live-math —
**KEPT** with a docstring honesty fix (see *Decisions*); the liveness lesson held (grep/`\uses`
were not decisive, but `lean_references` + the blueprint dep-graph confirmed the verdict).
**B3 landed (2026-07-07):** the 9 multi-label `\cref{a,b}` → "??" instances fixed
(split to `\cref{a} and \cref{b}`) + `lint.sh` check 6 added and sanity-tested. This
surfaced **B4** (a distinct `\subsubsection`-cref "??" bug, 9 more instances, needs a
reword-vs-restructure scoping call before landing — see checklist).
**Pinned next commit (coordinator): B4**, or either of **C1**, **D2**, **D3** (all
independent builds, no ordering constraint).

## Separately-planned / deferred (not this round; each has its own plan doc)

- **d=3 worked-case exposition** → `notes/CaseIII-d3-exposition.md`. Keep the
  concrete d=3 Case-III dispatch and write it up as the accessible on-ramp to the
  general Lemma 6.13. Exposition-writing (BlueprintExposition-flavored), not hygiene.
- **Formalization retrospective** → `notes/FormalizationRetrospective.md`. Narrative
  of the formalization's wrong turns (now including *this round's* d=3
  dead-vs-live misread). New-synthesis; a deliberate exception to the
  "process lives in git/FRICTION/DESIGN, not live docs" convention. **D1 is held for
  it** (that retrospective's raw archive is the two big design docs).

## Decisions made during this round

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
