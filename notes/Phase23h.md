# Phase 23h — Case III general `d`: ASSEMBLY (producer-site rewire → Thm 5.5 → 5.6 → Conjecture 1.2) (work log)

**Status:** in progress (opened 2026-07-02). The `ASSEMBLY` sub-phase — the **last** Phase-23
sub-phase. Authoritative scoping: `notes/Phase23-design.md` §2 *ASSEMBLY* (scope, hard core,
reuse/replace/add map); program map `notes/MolecularConjecture.md` §Phase 23; predecessor
hand-off `notes/Phase23g.md`.

## Current state

**A5 (Conjecture 1.2 stated as a theorem) landed — all Phase-23 node work is complete.** The
Molecular Conjecture `PanelHingeFramework.molecular_conjecture` (`thm:molecular-conjecture`,
KT 2011 Conjecture 1.2, conjectured Tay–Whiteley 1984) is green + axiom-clean
(`propext`/`Classical.choice`/`Quot.sound`, no `sorryAx`): for a simple spanning graph on `≥ 2`
bodies at general `d`, `G` has an infinitesimally rigid genuine **body-hinge** realization iff it
has one as a **panel-hinge** framework. (⇐) is the `toBodyHinge` coercion (same extensors); (⇒)
pins `def(G̃) = 0` via the genuine-hinge hub lower bound
(`screwDim_add_deficiency_le_finrank_infinitesimalMotions`) meeting `dim Z = D` from rigidity, then
Theorem 5.6 realizes it. The **genuine-hinge conjunct** (`∀ e, supportExtensor e ≠ 0`) is
mathematically essential on both sides — a degenerate hinge welds two bodies, so dropping it makes
the ⇐ statement false (a welded framework is rigid on a `def > 0` graph). Landed A5-L1: extracted
the A4 main case as the genuine-hinge witness form `rankHypothesis_genuine_of_theorem_55_gen`
(exposes `hC`, which the single-body branch of `rankHypothesis_of_theorem_55_gen` cannot supply);
A4 delegates its `|V| ≥ 2` case to it (still axiom-clean). Blueprint: minted `thm:molecular-conjecture`
in `panel-layer.tex` + the verified `tayWhiteley1984` bib entry (KT ref [25], Struct. Topol. 9,
31–38). **Next: close Phase 23** (the umbrella) — the remaining items are cleanup (orphan-decl sweep,
GAP 6 assessment), not node work; see *Hand-off*.

**A4 (Theorem 5.6 at general `d`) landed — general-`d` Theorem 5.6 is complete.** The carrier-lift
`PanelHingeFramework.rankHypothesis_of_theorem_55_gen` (Thm 5.6 at general `d`) strips to a minimal
`k`-dof spanning subgraph, realizes via the A2 spine `theorem_55_minimalKDof_gen`, and re-adds edges
(rank only grows), with the arithmetic bridge `Graph.eq_add_one_of_bodyBarDim_eq_screwDim`
(`bodyBarDim n = screwDim k → n = k + 1`, A4-L1, home `PanelLayer.lean`) feeding
`rigidityMatrix_prop11`'s `n = k + 1` premise. Axiom-clean (`propext`/`Classical.choice`/`Quot.sound`,
no `sorryAx`) for `6 ≤ bodyBarDim n` (i.e. `n ≥ 3`). One build, no friction (the one non-mechanical
spot — the single-body `hDpos`/`hnn` routing through `hD` rather than the `bodyBarDim 3` numeral —
was design-anticipated §(4.109.C)). Blueprint: minted `thm:theorem-55-6` (general, pinned to
`rankHypothesis_of_theorem_55_gen`), demoted `thm:theorem-55-6-d3` to the `d = 3` specialization
(both `d=3` pins survive), route-synced `prop:rigidity-matrix-prop11`'s proof prose + the two
`algebraic-induction.tex` chapter-intro passages (prop11 dimension-agnostic; Thm 5.6 now general).
The `d = 3` `rankHypothesis_of_theorem_55_d3` is **left as-is** (its blueprint narrative pin stays;
routing it through the general one is an orphan-sweep call). **A2 (Theorem 5.5 at general `d`) +
A3 (dissolved, no Lean content) done in prior commits.** **Next concrete commit: A5** — Conjecture
1.2 stated as a theorem (the panel-hinge ⇔ body-hinge realizability equivalence; new blueprint node).

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
- [x] **A4 — Theorem 5.6 at general `d`** (KT §5.2, printed p. 670: strip to a minimal `k`-dof
  spanning subgraph, realize via Thm 5.5, re-add edges — rank only grows). One build commit:
  **A4-L1** `Graph.eq_add_one_of_bodyBarDim_eq_screwDim` (`PanelLayer.lean`, the named form of the
  twice-inline `d_eq_kAdd` arithmetic); **A4-L2** `rankHypothesis_of_theorem_55_gen`
  (`Theorem55.lean`, the `2 → k`/`3 → n` pass over `rankHypothesis_of_theorem_55_d3`; the `def = 0`
  companion `rankHypothesis_deficiency_of_theorem_55_d3` was *not* lifted — it is the `def = 0`
  instance + a `d=3` narrative pin); **A4-L3** blueprint: minted `thm:theorem-55-6`, demoted
  `thm:theorem-55-6-d3` to the `d=3` specialization, route-synced prop11 proof prose + the two
  `algebraic-induction.tex` chapter-intro passages. Axiom-clean for `6 ≤ bodyBarDim n`.
- [x] **A5 — Conjecture 1.2 stated as a theorem** (`PanelHingeFramework.molecular_conjecture`, the
  panel-hinge ⇔ body-hinge realizability equivalence; with Phase 16's Prop 1.1 this is the
  conjecture). A5-L1: the genuine-hinge witness form `rankHypothesis_genuine_of_theorem_55_gen`
  (A4 main case extracted, exposing `hC`); A5-L2: the equivalence via hub-lower-bound → `def = 0`
  → Thm 5.6. New blueprint node `thm:molecular-conjecture` + `tayWhiteley1984` bib entry.

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

**All Phase-23 node work is complete (A1–A5 landed).** The general-`d` Theorem 5.5 (A2),
Theorem 5.6 (A4), and Conjecture 1.2 (A5, `molecular_conjecture`) are green + axiom-clean for
`6 ≤ bodyBarDim n`. Next concrete commit: **close the umbrella Phase 23** (full-phase close per
`PHASE-BOUNDARIES.md` — flip + re-thin the ROADMAP row, compress §23, sync user-facing status
surfaces, the end-to-end blueprint-chapter re-read + `notes/BlueprintExposition.md` write-up, the
project-organization review). The two carried-forward items are **cleanup, not node work** and can
land in the close or a follow-up: (1) the orphan-decl sweep (`chainData_extract_d3` and the other
`d=3`-era orphans — see *Carried forward from 23g*; A5 orphaned nothing new — the genuine witness
form is live via `molecular_conjecture`, and the A4 delegation keeps the plain form live); (2) GAP 6
(KT's all-`k` nested IH vs the 0-dof motive — assess; orthogonal to the landed cert). Closing
Phase 23 unblocks Phase 26's use of Thm 5.6 (Phases 24–25 don't gate on it).

## Decisions made during this phase

### Phase-local choices and proof techniques

- **A5 (Conjecture 1.2, `molecular_conjecture`):** stated the panel⇔body realizability equivalence
  with a **genuine-hinge conjunct** `∀ e, supportExtensor e ≠ 0` on *both* sides — verified against
  KT p. 648 (each `p(e)` a genuine `(d−2)`-flat). It is *mathematically essential*: a degenerate
  hinge welds two bodies, so without it a welded framework rigidifies a `def > 0` graph and ⇐ fails.
  Both directions are pure composition: ⇐ = `toBodyHinge` (same extensors); ⇒ = hub lower bound
  (`screwDim_add_deficiency_le_finrank_infinitesimalMotions`, *needs* genuine hinges) + `dim Z = D`
  from `rankHypothesis_zero_iff` ⟹ `def = 0`, then Thm 5.6. Scoped to `2 ≤ V(G).ncard` (a genuine
  hinge needs two distinct bodies, so both sides are vacuous on a single body). To feed ⇒ I
  **extracted the A4 main case** as `rankHypothesis_genuine_of_theorem_55_gen` (exposes `hC`, hidden
  by A4's conclusion; the single-body branch cannot supply it) and delegated A4's `|V| ≥ 2` case to
  it — no duplication, A4 stays axiom-clean. One build; no friction.
- **A4 (Theorem 5.6 at general `d`):** carrier-lift of the `d=3` `rankHypothesis_of_theorem_55_d3`
  to `rankHypothesis_of_theorem_55_gen` (`2 → k`/`3 → n` pass) + the named arithmetic bridge
  `Graph.eq_add_one_of_bodyBarDim_eq_screwDim` (A4-L1, home `PanelLayer.lean`, co-located with the
  hub's converse `hDcast`). Every reach-in (`exists_isMinimalKDof_spanning_subgraph`, the A2 spine,
  `reaimSub`, `finrank_span_rigidityRows_add_finrank_infinitesimalMotions`,
  `finrank_infinitesimalMotions_le_of_graph_le`, `panelSupportExtensor_ne_zero_iff`, prop11) is
  grade-general; the one non-mechanical spot was the single-body `hnn`, where the `d=3`
  `apply mul_nonneg <;> positivity` relied on `bodyBarDim 3` being a closed numeral — at general `n`
  it routes `0 ≤ bodyBarDim n − 1` through `hD` (`mul_nonneg (by omega) (by positivity)`). One build,
  axiom-clean for `6 ≤ bodyBarDim n`. `rankHypothesis_of_theorem_55_d3` + its `def=0` companion stay
  as blueprint narrative pins (`thm:theorem-55-6-d3`, `thm:theorem-55-d3-instance`) — not orphaned.
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
