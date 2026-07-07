# Phase 26 cleanup round — the molecular-program-closing hygiene pass (work log)

**Status:** ✓ complete (2026-07-07). Every executable item (A/B/C/D) landed;
the round is closed. It doubled as the **program-closing** round for the
molecular-conjecture program (17–26) and cleared the six `notes/Phase23-cleanup.md`
*Deferred …* carry-overs. Round manual: `CLEANUP.md`.

**Round was hygiene, not correctness.** No proof content changed — only blueprint
`.tex`, one Lean docstring (A3), `lint.sh`, and notes/docs. Pre- and post-round the
whole-project `lake build` was green (2860 jobs) and the two headline theorems
axiom-clean (`{propext, Classical.choice, Quot.sound}`):
`CombinatorialRigidity.Molecular.PanelHingeFramework.molecular_conjecture` and
`SimpleGraph.molecule_rank_formula` (the former's `_root_` name carries the
`CombinatorialRigidity.Molecular` namespace prefix — plain
`PanelHingeFramework.molecular_conjecture` won't resolve in `#print axioms`).

## What carried over

Nothing gates on this round (`CLEANUP.md` *What a cleanup round is not*). The
molecular conjecture + Cor 5.7 are green and axiom-clean. The round's own deferred
next work is the **exposition/retrospective family** in *Separately-planned* below
(A2-x, D1, D2b, the Formalization Retrospective) — each already has its own plan
doc / pointer; none is hygiene.

**Liveness lesson (this round, the hard way) — lifted to `CLEANUP.md` §B.**
"Zero incoming `\uses`" or "zero grep callers" does **not** prove a decl/section
dead: a decl can be live via a `_gen` sibling while the blueprint under-wires its
`\uses`. The d=3 Claim-6.12 section tripped *both* signals yet is load-bearing.
Trace the actual Lean call chain to the main theorem before retiring anything.

## Lemma checklist (landed record, A–D)

Items carried from `notes/Phase23-cleanup.md` *Deferred …* are tagged `(P23-carry)`.

### A/B — dead-code + blueprint honesty (the core)

- [x] **B1** (`990251fb`, P23-carry). Deleted `case_I_dispatch` — a zero-caller,
  unpinned `k:=2` wrapper of the live `case_I_dispatch_gen`.
- [x] **A2-i** (`78404289`). Cut two genuinely-dead decls: the `(k:=2)` wrapper
  `case_III_claim612` (caller re-pointed to `_gen`) + the zero-caller
  `exists_hduality_witness_of_panel_incidence`; node `lem:case-III-claim612` → `_gen`.
  −115 lines.
- [x] **A2-w** (`a528e227`). Fixed the general-path dep-graph wiring: added
  `lem:case-III-claim612` + `lem:case-III-claim612-line-in-panel-union` as `\uses`
  on `lem:case-III-chain-discriminator`'s proof, matching the traced Lean chain
  (`chainData_fire_discriminator → … → exists_complementIso_ne_zero_of_homogeneousIncidence_gen`,
  which calls `case_III_claim612_gen`). Blueprint-only.
- [x] **A3** (`daaec9d4`, P23-carry). The two `lem:case-II` bridge decls
  (`isInfinitesimallyRigidOn_insert_iff`, `rankHypothesis_withNormal_withGraph_iff_…`)
  are genuinely zero-caller but faithfully formalize the live node's KT 6.7/6.8 iff —
  **KEPT** per owner priority (keep formalization grounding a live node); fixed the
  stale `isInfinitesimallyRigidOn_insert_iff` docstring role claim. No blueprint edit.
- **A2-keep / A2-x kept as grounding, not cut.** `linearIndependent_sum_{p2,p3}_candidateRow`
  (+ selectors), `candidateRow_ne_zero`, and the d=3 `case_III_candidate_dispatch` are
  dead general-`k` / bypassed d=3 decls **retained** because they ground live/worked-case
  exposition nodes. The d=3 worked-case write-up is deferred → A2-x (*Separately-planned*).

### B — blueprint lint (the "??" family, all closed)

- [x] **B3** (`3660f994`, P23-carry). Multi-label `\cref{a,b}` rendered "??"
  (plastex's `cleveref.py` shim has no comma-list parser). Split all 9 into
  `\cref{a} and \cref{b}`; added `lint.sh` check 6.
- [x] **B4** (`f93a515f`, surfaced by B3's rebuild). `\subsubsection`-level
  `\cref`/`\S\ref` rendered "??" (subsubsections are unnumbered). Reworded all 9
  referencing sentences to name the target in prose (approach (a), not `\subsection`
  promotion); added `lint.sh` check 7.
- [x] **B5** (`8be3a2b7`, surfaced by B4's whole-corpus grep). A 10th "??": a
  multi-line 3-label `\cref` at `case-iii.tex:789-790` (pre-existing, predates the
  round). Split into three single-label `\cref`s; upgraded check 6 to be
  multi-line-aware (joins `%`-continuation lines before matching). Whole-corpus
  post-fix `grep -ro '??'` on the rendered HTML returns zero — B-"??" family closed.

### C — long-proof audit (screening)

- [x] **C1** (`bc3c4471`). Top-~10 long-proof screen across the molecular layer
  (Phase-24–26-weighted). Closed **no-op**, as the §C calibration predicted: the
  whole-`Molecular/`-tree top-10 is dominated by Phase-17–23 decls already handled
  by dedicated perf passes (e.g. the ~900-line `case_II_realization_all_k`
  calibration case), and the Phase-24–26-scoped top-~10 (46–94 lines) are all
  well-sectioned multi-step algebraic assemblies with no extraction / missed-mathlib /
  tactic-substitution / cross-proof-unification candidate. No code changes.

### D — project-organization compression

- [x] **D2a** (`261e61c7`, re-scoped to reconcile-only by owner). Reconciled the
  exposition ledger's *accounting* (`notes/BlueprintExposition.md`): a separate
  post-Phase-23 readability rewrite (R1–R9) had written 9 of 13 `[pending]` entries'
  exposition without flipping their markers. Flipped those 9 to `done`; corrected the
  header to **4 pending / 25 done**. Wrote no missing exposition (→ D2b, deferred).
- [x] **D3** (`c699e767`). Closed the stale `ScrewSpaceCarrier-design.md` — its
  general-`d` "part 2" is subsumed by Phase-23 (`ScrewSpace` is already an opaque
  general-`k` `def`). Status → DONE; body retained as archival spec.
- [x] **D4** — no-op. Zero `[resolved]` `FRICTION.md` entries to migrate.
- [ ] **D1 — DEFERRED** (owner call). `notes/Phase22-realization-design.md` (8590
  lines) + `notes/Phase23-design.md` (5379) are past the ~1500-line tripwire but are
  the raw-material archive for the Formalization Retrospective; compress in step with
  harvesting it (*Separately-planned*).

## Blockers / open questions

None. Every checklist item is closed except the deliberately-deferred **D1**.

## Separately-planned / deferred (the round's deferred follow-on family)

Each has its own plan doc / pointer; none is hygiene — all are substantive
exposition/synthesis work, deferred as a family (owner call 2026-07-07).

- **A2-x — d=3 worked-case exposition** → `notes/CaseIII-d3-exposition.md`. Write up
  the concrete d=3 Case-III dispatch (`case_III_candidate_dispatch`, kept as grounding)
  as the accessible on-ramp to the general Lemma 6.13 — genuinely simpler than the
  general argument (fixed three-panel dispatch, single relabel, `⋀²ℝ⁴`, no
  chain/cycle/block machinery).
- **D1 — compress the two oversized closed design docs** (`Phase22-realization-design.md`,
  `Phase23-design.md`). Held for the retrospective (they are its raw archive); compress
  in step with harvesting.
- **D2b — the remaining blueprint exposition write-ups.** The 4 genuinely-unwritten
  `[pending]` crux nodes left after D2a's accounting reconciliation (Case-I
  contraction-simplicity mechanism, the two-distinct-body-sets splice framing, the
  matroid-union/contraction crux, Claim 6.4's genericity-vs-general-position bundling —
  `case-i.tex`/`algebraic-induction.tex`), plus the wider ~13-crux 17–26 backlog the
  ledger's capture-now/write-later design defers to a broadened blueprint pass.
- **Formalization Retrospective** → `notes/FormalizationRetrospective.md`. Narrative of
  the formalization's wrong turns (now including *this round's* d=3 dead-vs-live
  misread). New-synthesis; a deliberate exception to the "process lives in
  git/FRICTION/DESIGN" convention. **D1 is held for it.**

## Decisions made during this round

The checklist above carries each landed item's what + commit. Cross-cutting /
still-live rationale, one-line:

- **Liveness lesson** → lifted to `CLEANUP.md` §B (verify liveness against the Lean
  call chain, not `\uses`/grep alone). The load-bearing lesson of the round; applied
  to A2 and A3.
- **A2 disposition (corrected mid-round).** The d=3 Claim-6.12 blueprint section is
  **live** (`case_III_claim612_gen` used by the general chain), so it is neither
  demoted nor its nodes cut — the "orphaned" look was a missing `\uses` edge (→ A2-w).
  Only `case_III_candidate_dispatch` is genuinely bypassed at d=3, and it is **kept**
  as worked-case grounding (→ A2-x). *(An intra-session "demote / delete p2/p3" read
  was wrong; git has the arc.)*
- **A3 disposition.** `lem:case-II` bridge decls are dead-but-exposit-live-math (case
  (ii): not live-under-wired, not divergence — `lem:case-II-realization` bypasses the
  node and re-derives the count inline). Kept per owner priority; docstring honesty fix.
- **Owner priority applied throughout:** keep formalization that grounds a live or
  worked-case blueprint node, even at zero Lean callers.
