# Phase 41b — RESTATE: the main results restated on the linked carrier (work log)

**Status:** in progress (opened 2026-10-24), a sub-phase of Phase 41. The phase's design, the PI's
decisions (at the phase's open, §1, and at this sub-phase's, §1b) and the recons are in
`notes/Phase41-design.md`. Next concrete task: item 1, the recon on KT's nonparallel panels.

## Current state

Opened with the PI on 2026-10-24, after the RESTATE open's recon (`notes/Phase41-design.md` §2,
*RESTATE's open recon*); no Lean has changed yet. The sub-phase restates S2's and S1's main results
on the carrier that 41a gave the link field, and acts on the PI's four decisions at its open
(§1b): Theorem 5.6 concludes general position for simple `G`, G6's row is the generic rank formula,
`HasGenericFullRankRealization` drops its last conjunct, and Theorem 5.5's conclusion reaches KT's
nonparallel panels. Mode: structural edit. There are no red target nodes; each slice restates the
nodes it reaches (`CombinatorialRigidity/CLAUDE.md` *Forward-mode slices*).

## Architectural choices made up front

- **Statements change only as the design doc's §1 and §1b say** (`notes/Reconcile.md` §2,
  *Hygiene*): any other statement change is recorded as an `S` entry and not acted on. A prompt
  that bars an edit names the neighbouring edits it allows (dispatch-log F51).
- **Each restated main result lands with its non-vacuity witness** in
  `CombinatorialRigidity/Nonvacuity.lean` (`PHASE-BOUNDARIES.md` *When this commit closes a
  phase*); its `formalization.yaml` row follows in the same commit.
- **Ledger.** Each commit names the ledger IDs it acts on (S2: `F-122`, `F-125`, `F-128`; S1:
  `F-207`, with `F-206`, `F-216`, `F-221`; `F-126`, `F-323`, `F-324`) and gives each entry its
  `done (<sha>)` disposition (`notes/Reconcile.md` §2).
- **One commit per dispatch** (dispatch-log F53). PI entries are never compressed (F50).

## Lemma checklist

The order is provisional: item 1's verdict sizes item 4 and may move it.

- [ ] **1. Recon: KT's nonparallel** (§1b.4). Its definition on the carrier's homogeneous normals
  (which coordinates are the direction, what KT §5.1 asks); whether the genericity device's choice
  of normals can avoid parallel pairs as it avoids the step's polynomials; where Theorem 5.5's
  induction fixes normals (`ofParam`'s moment curve, Case III's placements); the cost. The verdict
  lands in the design doc's §2 as a design-pass commit and turns item 4 into commits.
- [ ] **2. `HasGenericFullRankRealization`'s last conjunct** (§1b.3): its producers and
  destructurers, the two dead helpers, `def:rank-hypothesis`'s prose; the two `hswap` hypotheses of
  `Coupling.lean` and the hand-built link sites the field gives (design doc §2).
- [ ] **3. `F-324`**: `theorem_55_minimalKDof_gen`'s derivable `hD` and the chain below it
  (`F-293`, `F-297`, `F-298`; about ten signatures, seven call sites).
- [ ] **4. KT's nonparallel in Theorem 5.5's conclusion** (§1b.4): commits per item 1.
- [ ] **5. Theorem 5.6** (S2; §1b.1): `rankHypothesis_of_theorem_55_gen` concludes `Q.graph = G`,
  general position (item 4's nonparallel) and the rank, keeps `hSimple`, drops `[DecidableEq β]`
  (`F-323`); `thm:theorem-55-6` restated; the link conjunct of the rows form
  `finrank_span_rigidityRows_genuine_recordsLinks_of_theorem_55_gen`, of
  `exists_rankHypothesis_isGeneralPosition4_of_two_le` and of its wrapper
  `exists_rankHypothesis_isGeneralPosition4` dropped; the witness.
- [ ] **6. `molecular_conjecture`** (S2; §1.2): `V(G).Nonempty` for `2 ≤ |V(G)|`, nondegenerate
  hinges on `E(G)` on both sides, `[DecidableEq β]` dropped (`F-323`); the witness.
- [ ] **7. The multigraph rows** (§1.2, §1.4): `molecular_conjecture_multigraph` and
  `theorem_55_6_multigraph_gen` ask nondegeneracy on `E(G)`; `IsHingeCoplanar` constrains `E(G)`
  only; `F-323`'s binders.
- [ ] **8. `cor:theorem-55-d3-spanning`** (`F-126`): derived from `theorem_55_d3` under `hcard`, with
  general position and nondegenerate hinges on `E(G)`, `_hSimple` dropped.
- [ ] **9. S1, the panel theorems** (`PanelGeneric.lean`; S13; §1b.2): `hcard` for `hfresh`, no
  `ends` or `hends`, genericity over the rows of `E(G)`, `hQends` gone; the rank formula over every
  framework on `G` with generic normals becomes G6's `main_results` row, its witness at the single
  edge.
- [ ] **10. S1, the body-hinge theorems** (`HingeGeneric.lean`): `hcard` for `hfresh`,
  `IsGenericHingePoints` oriented by the links, no `ends`, `hends` or `hD`; the spanning-trees row
  restated; the docstring-label check's two findings (`HingeGeneric.lean:477`, `:486`) cleared and
  its baseline lowered.
- [ ] **11. S18** (`prop:rigidity-matrix-prop11`): the conditional statement, or a repin on the
  generic forms.
- [ ] **12. The status surfaces**: the degenerate-hinge sentences (Theorem 5.6's `main_results` row
  and `alignment` note, README, the home page, `intro.tex`, ROADMAP §23) and the footprint's
  remaining docstrings.
- [ ] **Close**: whole-project build with 0 warnings, `lake lint`, the blueprint gates, the main
  results' axioms; MULTIGRAPH or UNSTATED named next.

## Blockers / open questions

- **KT's nonparallel** (§1b.4): definition, route and cost unknown until item 1.
- **CI has not run since 2026-10-15**: the PI pushes after RESTATE closes (§1b), so that push is
  CI's first run of 41a's `module` conversion (doc-gen, the upstreaming dashboard). The close
  should expect to watch it.

## Hand-off / next phase

**Item 1**: a read-only recon on KT's nonparallel panels (the questions in the checklist), whose
verdict lands as a design-pass commit in `notes/Phase41-design.md` §2 and splits item 4 into
commits. Item 2 needs no recon: its spec is the design doc's §2 (*RESTATE's open recon*, Q3).

## Decisions made during this phase

- **The PI's decisions at the open** (2026-10-24): `notes/Phase41-design.md` §1b, verbatim.
