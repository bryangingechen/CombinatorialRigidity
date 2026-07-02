# Phase 23h — Case III general `d`: ASSEMBLY (producer-site rewire → Thm 5.5 → 5.6 → Conjecture 1.2) (work log)

**Status:** in progress (opened 2026-07-02). The `ASSEMBLY` sub-phase — the **last** Phase-23
sub-phase. Authoritative scoping: `notes/Phase23-design.md` §2 *ASSEMBLY* (scope, hard core,
reuse/replace/add map); program map `notes/MolecularConjecture.md` §Phase 23; predecessor
hand-off `notes/Phase23g.md`.

## Current state

**A2 (Theorem 5.5 at general `d`) landed — general-`d` Theorem 5.5 is complete.** The zero-carry
general-grade wrapper `PanelHingeFramework.theorem_55_minimalKDof_gen` (+ its `c = 0` corollary
`theorem_55_gen`) fills every carry of the general-`k` spine `theorem_55_minimalKDof_k_all_k` from
the grade-general producers in tree — `theorem_55_base_producer_gen` (`hbase_k`),
`case_cut_edge_realization_gp_gen` + `case_cut_edge_realization_gen` (`hcut_k`),
`case_I_hcontract_gen` (`hcontract_k`), `hasPanelRealization_of_generic` (`hforget_k`, `[NeZero k]`
from `hk1`). Axiom-clean (`propext`/`Classical.choice`/`Quot.sound`, no `sorryAx`) for
`6 ≤ bodyBarDim n` (i.e. `n ≥ 3`, the Phase-20 chain-extractor floor kept per the 23g decision).
Pure composition, one build, no friction. The `d = 3` `theorem_55_minimalKDof_k` is **left as-is**
(routing it through the general wrapper would orphan the blueprint-pinned `d = 3` sub-producers —
deferred to the orphan sweep). Blueprint `thm:theorem-55` re-pinned to
`theorem_55_gen`/`theorem_55_minimalKDof_gen` and restated general-`d` (statement + proof + the two
chapter-intro passages in `algebraic-induction.tex`); `thm:theorem-55-d3-instance` stays the `d = 3`
specialization. **A3 design pass done (design §(4.109)): A3 has no Lean content** —
`rigidityMatrix_prop11` and the whole `hub` family are already grade-general as landed; A3
dissolves into A4. **Next concrete commit: A4** — Thm 5.6 at general `d`, one build commit
(§(4.109.C): the `eq_add_one_of_bodyBarDim_eq_screwDim` extraction + the
`rankHypothesis_of_theorem_55_gen` carrier-lift + the `thm:theorem-55-6` blueprint node with the
prop11 proof-prose route-sync riding along).

## Layer plan (the ASSEMBLY to-do list; design §2 *ASSEMBLY*)

- [x] **A1 — producer-site rewire** (this phase). Bricks consumed inside
  `case_III_hsplit_producer_all_k` (chain arm ← `Graph.chainData_extract`; cycle arm ←
  `cycle_realization`); `hextract`/`hcycle` binders dropped from all four sites; producer gained
  `hn`; `Arms.lean` gained the `ForestSurgery.ChainExtraction` import. No blueprint edit needed —
  the four signature-changed decls carry no `\lean{...}` pin, and the pinned `case_III_realization`
  statement is unchanged (its binders were always body-filled).
- [x] **A2 — Theorem 5.5 at general `d`** (`theorem_55_minimalKDof_gen` + its `c = 0` corollary
  `theorem_55_gen`; the general-`d` zero-carry wrapper off the rewired spine, axiom-clean for
  `6 ≤ bodyBarDim n`; `thm:theorem-55` re-pinned/restated). `d = 3` wrapper untouched.
- [x] **A3 — re-green `prop:rigidity-matrix-prop11` + its `hub` at general grade** — **dissolved
  by the design pass (design §(4.109)): no Lean content.** `rigidityMatrix_prop11`
  (`PanelHinge.lean:1136`, `hn : n = k + 1`) and the entire `hub` family (`PanelLayer.lean`
  §Partition-respecting motions) are already grade-general as landed, and prop11 is already
  consumed at general grade (`CaseI.lean:2304`). The only `d=3` residue is one proof-prose
  sentence in `prop:rigidity-matrix-prop11` — a blueprint route-sync riding in the A4 commit.
- [ ] **A4 — Theorem 5.6 at general `d`** (KT §5.2, printed p. 670: strip to a minimal `k`-dof
  spanning subgraph, realize via Thm 5.5, re-add edges — rank only grows). **One build commit**,
  decomposed with exact signatures in design §(4.109.C): **A4-L1**
  `Graph.eq_add_one_of_bodyBarDim_eq_screwDim` (extract the twice-inline `d_eq_kAdd` arithmetic);
  **A4-L2** `rankHypothesis_of_theorem_55_gen` (mechanical `2 → k`/`3 → n` numeral pass over
  `rankHypothesis_of_theorem_55_d3`, `Theorem55.lean:2750` — every reach-in verified
  grade-general; the `def = 0` companion is *not* lifted, it is the `def = 0` instance); **A4-L3**
  blueprint: mint `thm:theorem-55-6`, demote `thm:theorem-55-6-d3` to the `d=3` specialization,
  route-sync prop11's proof prose. (The old template name `theorem_55_6_d3` was stale — no such
  decl exists; the projective-invariance worry dissolves: the homogeneous re-add is grade-free,
  §(4.109.D).)
- [ ] **A5 — Conjecture 1.2 stated as a theorem** (the panel-hinge ⇔ body-hinge realizability
  equivalence; with Phase 16's Prop 1.1 this is the conjecture). New blueprint node.

### Carried forward from 23g

- [ ] **GAP 6** — KT's all-`k` nested IH (6.1) vs the project's 0-dof-only motive; orthogonal
  to the 23e cert. (Design-doc tracked; assess against A2.)
- [ ] **Orphan-decl sweep** — the `d=3`-era orphans: `interior_hsplitGP`
  (`CaseIII/Realization.lean`), `case_III_realization_of_line` (`CaseIII/Arms.lean`),
  `case_III_hsplit_producer` (`CaseIII/Arms.lean`; the `d=3` producer wrapper, orphaned since
  CHAIN-5 — the spine calls `_all_k` directly), and **`chainData_extract_d3`
  (`ForestSurgery/Reduction.lean`; newly orphaned by A1 — the general `chainData_extract`
  subsumes it at `d = 3`)**. Delete-or-keep, each with a one-line rationale. (Note: the
  now-unused `ForestSurgery.Reduction`/`ChainExtraction` imports in `Realization.lean`/
  `Theorem55.lean` are harmless — no unused-import linter — but are candidates for the same sweep.)
  **A2 addendum:** routing the `d=3` `theorem_55_minimalKDof_k` through the new general
  `theorem_55_minimalKDof_gen` (`k := 2`) collapses the duplicated callback map but orphans the
  blueprint-pinned `d=3` sub-producers `theorem_55_base_producer` + `case_cut_edge_realization{,_gp}`
  (their only Lean callsite is the `d=3` wrapper) — decide collapse-and-re-pin vs keep here.
- The `notes/model-experiment.md` archive step for 23g's rows is **coordinator-owned** — not
  a 23h work item; listed here only so it isn't re-invented as one.

## LIVE — DO NOT delete / DO NOT plan to delete (inherited from 23g)

- `caseIIICandidate` + its API — the honest engine consumes it via
  `case_III_realization_of_rank` ← `case_III_arm_realization`.
- The non-aug edge-path helpers `rigidityMatrixEdge_mul_columnOp_*` (WITHOUT `Aug`) in
  `RigidityMatrix/Concrete.lean`.

## Phase-open checklist record (2026-07-02)

- **Red-node consistency gate:** 23h has no red stub targets — its blueprint targets are
  currently-*green* nodes to be restated/extended (`thm:theorem-55`,
  `prop:rigidity-matrix-prop11`, `thm:theorem-55-6-d3` in
  `blueprint/src/chapter/algebraic-induction/panel-layer.tex`) plus two not-yet-minted nodes
  (general-`d` Thm 5.6, Conjecture 1.2). Read the three targets end-to-end: each proof routes
  through the argument its statement claims, each correctly names its `d=3` scope and the
  Phase-23 frontier, and no live-route `\uses`/proof step points at a superseded node (the
  only red nodes in the tree are the four `superseded`-marked `lem:case-II-placement-*`
  M-nodes and four known deferred nodes unrelated to 23h).
- **User-facing status surfaces:** no edit needed — README, `home_page/index.md`, and
  `intro.tex` carry arc-level status and already name the general-`d` argument (Phase 23) as
  the frontier; sub-phase transitions don't surface there (`PHASE-BOUNDARIES.md`).
- ROADMAP umbrella cell + §23 prose and `notes/MolecularConjecture.md` (Status, phase table,
  Phase-23 detail block, *Opening the next phase*) synced in the opening commit.

## Blockers / open questions

- None. Both risks the design doc flagged as potentially more than composition are resolved by
  the A3 design pass (design §(4.109)): the general-`d` `hub` was already landed general, and the
  projective-invariance step is grade-free in the homogeneous model.

## Hand-off / next phase

Next concrete commit: **A4 — Theorem 5.6 at general `d`, one build commit** (design §(4.109.C)
carries the exact target signatures): **A4-L1** the arithmetic extraction
`Graph.eq_add_one_of_bodyBarDim_eq_screwDim : bodyBarDim n = screwDim k → n = k + 1` (the inline
`d_eq_kAdd` arithmetic, `CaseIII/Realization.lean:1163–1171`; home `PanelLayer.lean`, builder
confirms the import spine); **A4-L2** `PanelHingeFramework.rankHypothesis_of_theorem_55_gen`
(the mechanical `2 → k`/`3 → n` numeral pass over `rankHypothesis_of_theorem_55_d3`,
`Theorem55.lean:2750`, calling `theorem_55_minimalKDof_gen` + prop11 via A4-L1; signature
convention `hk1`/`hD`/`hn : bodyBarDim n = screwDim k` matching A2); **A4-L3** blueprint in the
same commit — mint `thm:theorem-55-6` pinned to the new decl, demote `thm:theorem-55-6-d3` to the
`d=3` specialization, and route-sync `prop:rigidity-matrix-prop11`'s proof prose (the dissolved
A3's only real payload). A3 needs **no Lean work** — prop11 + `hub` are already grade-general
(design §(4.109.A)). Then **A5** — Conjecture 1.2 as a theorem (new blueprint node). Closing 23h
closes the umbrella Phase 23 (full-phase close: `PHASE-BOUNDARIES.md`) and unblocks Phase 26's use
of Thm 5.6 (Phases 24–25 don't gate on it).

## Decisions made during this phase

### Phase-local choices and proof techniques

- **A3 design pass (docs-only, design §(4.109)):** `rigidityMatrix_prop11` + the `hub` family are
  already grade-general as landed (born general in Phase 19/22i) — the design doc's
  "genuine-content `hub` partition brick" flag was stale, and `theorem_55_6_d3` named a
  nonexistent decl (the `d=3` Thm 5.6 is `rankHypothesis_of_theorem_55_d3`). A3↔A4 settled:
  prop11 is `hgen`-conditional (no Thm-5.5/5.6 dependency); "hgen supplied by Thm 5.6" is the
  unconditional reading — A3 merges into A4 as a blueprint route-sync rider. Lesson re-confirmed
  (as in the A2 assessment): read the landed decl before trusting a recon-era
  "still-`d=3`-pinned" claim.
- **A2 (Theorem 5.5 at general `d`):** the zero-carry general-grade wrapper
  `theorem_55_minimalKDof_gen` fills the four carries of the spine `theorem_55_minimalKDof_k_all_k`
  from the grade-general producers (`theorem_55_base_producer_gen`, `case_cut_edge_realization_gp_gen`
  + `case_cut_edge_realization_gen`, `case_I_hcontract_gen`, `hasPanelRealization_of_generic` with
  `[NeZero k]` synthesized from `hk1`); `theorem_55_gen` is the `c = 0` corollary. Pure composition,
  one build, axiom-clean (no `sorryAx`) — confirms the coordinator's "wrapper, no A3 dependency"
  signature-check. Deliberately **did not** re-base the `d=3` `theorem_55_minimalKDof_k` through it
  (would orphan the blueprint-pinned `d=3` sub-producers — orphan-sweep item). Blueprint
  `thm:theorem-55` re-pinned to the general decls + restated (its prose was already dimension-agnostic;
  the `\uses{lem:case-III}` edge was already representative, since the spine calls `case_III_realization_all_k`).
- **A1 (producer-site rewire):** consumed the two ENTRY bricks *inside* the deepest producer
  `case_III_hsplit_producer_all_k` (not one level up) — the deepest site with all of
  `chainData_extract`'s inputs (`hD`/`hV3`/`hG`/`[Simple]`/`hfresh`), needing only a new
  `hn : bodyBarDim n = screwDim k` binder for `cycle_realization`. Dropping the binders cascaded
  E4-in-reverse up the four sites; one commit, zero regression, `d=3` green. Mechanical (no
  friction: no `change`/`show`, hint additions, or typeclass dances). `Arms.lean` gained the
  `ForestSurgery.ChainExtraction` import (the E3 brick's module had had no importer while
  unconsumed; no cycle — `Induction/` is below `AlgebraicInduction/`).
- **`chainData_extract_d3` orphaned by A1** (not deleted — orphan-sweep item): the general
  `chainData_extract` covers `d = 3` (`bodyBarDim 3 = 6`), so the `d=3` discharge is redundant.
  The `d=3` wrappers stay green through the general path, not via `chainData_extract_d3`.
- **`lem:case-III` blueprint route-sync (A1 follow-up).** Verified against the landed Lean before
  editing: `lem:chain-data-of-noRigid` is genuinely dead on the live route (its sole caller,
  `chainData_extract_d3`, is orphaned) — dropped from `\uses`, added `lem:chain-data-extract` +
  `lem:cycle-realization` instead. **`lem:adjacent-degree-two-pair` stays in `\uses`** — contrary
  to the initial assumption, it is *still* consumed on the live route, just via the `|V| = 3`
  triangle floor (`Arms.lean:980`, unchanged by A1), not the `|V| \ge 4` chain arm the old prose
  attributed it to; reworded the proof narrative to match. Also fixed the proof's closing
  paragraph and the "triangle floor" discussion aside (both pre-A1 text claiming "no cycle
  branch" — false since A1: `cycle_realization`'s branch is on the formal route, vacuous only at
  `d = 3`), and added a one-line status caveat to `lem:chain-data-of-noRigid` in
  `molecular-induction.tex` (now off-route). Lesson: a task's stated diff summary can be
  incomplete for a shared helper lemma used by *two* independent call sites — always grep every
  call site of a "dead" declaration before trusting a route-change claim.
