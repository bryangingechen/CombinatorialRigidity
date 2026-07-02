# Phase 23h — Case III general `d`: ASSEMBLY (producer-site rewire → Thm 5.5 → 5.6 → Conjecture 1.2) (work log)

**Status:** in progress (opened 2026-07-02). The `ASSEMBLY` sub-phase — the **last** Phase-23
sub-phase. Authoritative scoping: `notes/Phase23-design.md` §2 *ASSEMBLY* (scope, hard core,
reuse/replace/add map); program map `notes/MolecularConjecture.md` §Phase 23; predecessor
hand-off `notes/Phase23g.md`.

## Current state

Opened on the 23g hand-off. Both general-`n` bricks are green and land producer-side
**unconsumed** — `Graph.chainData_extract` (discharges `hextract` at general `n`) and
`PanelHingeFramework.cycle_realization` (discharges `hcycle`) — while the producer/spine sites
still *carry* the binders (the `d=3` wrappers fill them via `Or.inl ∘ chainData_extract_d3` +
a vacuous `hcycle`). **Next concrete commit: the producer-site rewire** — consume the two
bricks at the four producer/spine sites and drop the green-modulo binders (first checklist
item below). `d=3` is fully green and must stay so through every slice.

## Layer plan (the ASSEMBLY to-do list; design §2 *ASSEMBLY*)

- [ ] **A1 — producer-site rewire.** Consume `Graph.chainData_extract` (fills `hextract`) and
  `PanelHingeFramework.cycle_realization` (fills `hcycle`) at the four producer/spine sites,
  dropping the binders:
  - `case_III_hsplit_producer_all_k` + its wrapper (`AlgebraicInduction/CaseIII/Arms.lean`);
  - `case_III_realization_all_k` (`AlgebraicInduction/CaseIII/Realization.lean`);
  - `theorem_55_minimalKDof_k_all_k` (`AlgebraicInduction/Theorem55.lean`).

  The `d=3` wrappers keep working via `chainData_extract_d3`. Per-slice gate: these are
  *statement* changes — grep `blueprint/src/` for each touched decl before committing the
  slice (surviving `\lean{...}` names hide a legacy-form node from `checkdecls`).
- [ ] **A2 — Theorem 5.5 at general `d`** (complete `theorem_55` off the rewired spine).
- [ ] **A3 — re-green `prop:rigidity-matrix-prop11`** + its `hub` at general grade. The
  general-`d` `hub` partition brick is a genuine (Track-independent, multi-commit in the
  `d=3` case) obligation — decompose math-first before scheduling.
- [ ] **A4 — Theorem 5.6 at general `d`** (KT §5.2: strip to a minimal `k`-dof spanning
  subgraph, realize via Thm 5.5, re-add edges — rank only grows). Templates:
  `rankHypothesis_of_theorem_55_d3` / `theorem_55_6_d3` (mostly carrier-lift + dropping the
  `hn : bodyBarDim n = screwDim 2` specialization). Confirm the `d=3` "projective-move-free"
  re-add (two distinct hyperplanes through the origin always meet) still holds at general `d`;
  KT uses projective invariance [4, §3.6] explicitly here.
- [ ] **A5 — Conjecture 1.2 stated as a theorem** (the panel-hinge ⇔ body-hinge realizability
  equivalence; with Phase 16's Prop 1.1 this is the conjecture). New blueprint node.

### Carried forward from 23g

- [ ] **GAP 6** — KT's all-`k` nested IH (6.1) vs the project's 0-dof-only motive; orthogonal
  to the 23e cert. (Design-doc tracked; assess against A2.)
- [ ] **Orphan-decl sweep** — the two `d=3`-era orphans: `interior_hsplitGP`
  (`CaseIII/Realization.lean`) and `case_III_realization_of_line` (`CaseIII/Arms.lean`);
  delete-or-keep, each with a one-line rationale.
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

- None yet. A3's `hub` partition brick and A4's projective-invariance check are the two
  places the design doc flags as potentially more than composition.

## Hand-off / next phase

Next concrete commit: **A1**. The binders flow from the spine down to the producer, so the
natural shape is the E4 precedent in reverse — a one-commit zero-regression lockstep across
the four sites (dropping a binder at one site orphans the arguments its callers pass, so a
per-site split risks unused-binder warnings); keep the `d=3` wrappers green in the same
commit. If the lockstep won't fit one sitting, shrink to the deepest consumer + its direct
callers rather than leaving a half-rewired chain. Closing 23h closes
the umbrella Phase 23 (full-phase close: `PHASE-BOUNDARIES.md`), and unblocks Phase 26's use
of Thm 5.6 (Phases 24–25 don't gate on it).

## Decisions made during this phase

(none yet)
