# Phase 41c — MULTIGRAPH: the generic body-hinge theorem for multigraphs (work log)

**Status:** ✓ closed 2026-10-28 (opened the same day with the PI), a sub-phase of Phase 41, which
stays in progress. The phase's design, the PI's decisions (here §1f.4, loops, and §1g, the open)
and the open's recon are in `notes/Phase41-design.md`; the recon's Lean witness is
`notes/reconcile-formal/MultigraphWitness.lean`. Every checklist item landed, in 6 commits with the
open, the re-read and the close. Next: UNSTATED, for the PI to open (*Hand-off*).

## Current state

**Closed.** M1, Jackson and Jordán's Theorem 6.1 in the project's generic form, holds for every
multigraph spanning the bodies, parallel edges and loops allowed: the rank formula, the rigidity
iff and the spanning-trees iff at every generic hinge-point assignment, under Theorem 5.6's label
bound `hcard`, with witnesses at the double edge and the double edge with a loop
(`Nonvacuity.lean`). The lower bound starts from the multigraph Theorem 5.6, whose hinges lie in
the panels; loops cost one commit, the upper bound asked only at the edges that are not loops.
KT Proposition 2.3 is proved as Katoh and Tanigawa state it, the three-way equivalence at every
generic hinge-point assignment (`prop:rigidity-matrix-prop11`), and the conditional form keeps its
own node (`prop:rank-formula-of-motion-bound`). The close's re-read fixed four sentences first, in
`79df20c0`. At the close the 20 main results' axioms are `[propext, Classical.choice, Quot.sound]`,
the output identical to 41b's close run net of the harness path. Mode: structural edit, no red
target nodes.

## Architectural choices made up front

- **Statements change only as the design doc's §1f.4 and §1g say** (`notes/Reconcile.md` §2,
  *Hygiene*); a free strengthening only under §1f.3, recorded in the design doc.
- **Replace in place, no twin**: no Lean outside `HingeGeneric.lean` and `Nonvacuity.lean` uses the
  restated names (41b's items 9 and 10).
- **Each restated main result lands with its non-vacuity witness** and its `formalization.yaml`
  row in the same commit.
- **Ledger.** Each commit names the ledger IDs it acts on (`F-222`: M1; `F-121`: the unconditional
  repin) and gives each its `done (<sha>)` disposition. One commit per dispatch (dispatch-log F53).

## Lemma checklist

- [x] **1. The upper bound at the non-loop links** (§1f.4; `F-332`): `e348a3e8`.
- [x] **2. M1** (`F-222`; JJ 2010 Theorem 6.1, p. 582): `aeac5f6e`.
- [x] **3. KT Proposition 2.3, unconditional** (`F-121`; §1f.1): `5ab192e3`.
- [x] **Close**: the re-read (`79df20c0`), then the gates, ROADMAP's row and §41, the design doc's
  MULTIGRAPH arc compressed, UNSTATED named next (the commit "Phase 41c CLOSES (MULTIGRAPH)").

## Blockers / open questions

- None. Two options the open's recon left unplanned are open questions for the PI in the design
  doc's §4: dropping `hcard` from M1 and KT Proposition 2.3, and relaxing `rigidityMatrix_prop11`'s
  `hC` to the non-loop links.

## Hand-off / next phase

**Successor: UNSTATED**, the claims no declaration states (design doc §3, 13–23 commits), the
last sub-phase of Phase 41, **for the PI to open**: no letter is minted and no work log exists
until then. ORIGAMI opens after Phase 41.

## Decisions made during this phase

- **The PI's decisions at the open** (2026-10-28): `notes/Phase41-design.md` §1g, verbatim.
- **Loops by relaxing the upper bound** (§1f.4): one commit, item 1; the fallback that leaves the
  upper bound alone was not the PI's reading.
- **M1 from the multigraph Theorem 5.6**: its hinges lie in the panels, so each decomposes
  (`exists_extensor_eq_of_extensorInPanel`, in `RigidityMatrix/Basic.lean`).
- **`prop:rigidity-matrix-prop11` moved to `generic-lift.tex`**, pinning
  `tfae_finrank_span_rigidityRows_ofHinge_deficiency`; `rigidityMatrix_prop11` under
  `prop:rank-formula-of-motion-bound`, as the KT label's `\uses` would otherwise cycle.
