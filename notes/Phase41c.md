# Phase 41c — MULTIGRAPH: the generic body-hinge theorem for multigraphs (work log)

**Status:** in progress (opened 2026-10-28 with the PI), a sub-phase of Phase 41. The phase's
design, the PI's decisions (here §1f.4, loops, and §1g, the open) and the open's recon are in
`notes/Phase41-design.md`; the recon's Lean witness is
`notes/reconcile-formal/MultigraphWitness.lean`. Three build items and the close (planned 3–5);
item 1 has landed. Next: item 2, M1 (the witness file's M1 sections transcribed).

## Current state

**The next concrete commit is item 2** (*Hand-off*); item 1 has landed. The open's recon
(design doc §2, *MULTIGRAPH's open recon*) built the whole sub-phase in a witness file against
`ae6a852c`, with no `sorry`: M1, the generic
body-hinge theorems for every spanning multigraph, parallel edges and loops allowed, and KT
Proposition 2.3 at every generic hinge-point assignment. The lower bound comes from the multigraph
Theorem 5.6 (`theorem_55_6_multigraph_gen`): its hinges lie in panels, and `ExtensorInPanel`'s body
is an extensor of vectors, so each hinge at an edge decomposes as the transplant needs. Loops cost
one commit (item 1), within §1f.4's bound. Mode: structural edit, no red target nodes; each item
restates the nodes it reaches, in step with its Lean.

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

The witness file proves each Lean statement below under the namespace `Recon41cMultigraph`; an
item transcribes it into the library, with its blueprint and status surfaces.

- [x] **1. The upper bound at the non-loop links** (§1f.4; `F-332`). Done (the commit "Phase 41c
  item 1: the upper bound asked at the non-loop links"): `hC` of the three upper-bound lemmas asks
  `u ≠ v`, 18 files' callers wrap it, `lem:deficiency-rank-bound` states its hypothesis and
  `lem:relative-deficiency-rank-bound` asks it at the non-loops. S/P/B 1/1/2.
- [ ] **2. M1** (`F-222`; JJ 2010 Theorem 6.1, p. 582). In `HingeGeneric.lean`, `hSimple` dropped
  from `exists_hingePoints_independent_hingePointRow` (now from `theorem_55_6_multigraph_gen`),
  `finrank_span_rigidityRows_ofHinge_of_isGenericHingePoints` and the two iffs, under `hk1`, `hn`,
  `hcard`, `hne`, `hspan`; `supportExtensor_ofHinge_ne_zero_of_isGenericHingePoints` concludes
  `∀ e u v, G.IsLink e u v → u ≠ v → … ≠ 0` with no `G.Loopless`. One new lemma,
  `exists_extensor_eq_of_extensorInPanel` (`RigidityMatrix/Basic.lean`, beside `ExtensorInPanel`).
  `Nonvacuity.lean`: the row's witness at the double edge, a second at the double edge with a loop.
  Blueprint: `thm:bodyhinge-generic-rank`, its two corollaries, `lem:hinge-point-witness`
  (`\uses` the multigraph Theorem 5.6), `lem:generic-hinge-points-nondegenerate`, the chapter
  opening and the scope sentences that say "simple". Status: the main row, the JJ alignment row,
  `fidelity.divergences`, README, the home page, ROADMAP's BH paragraph. S/P/B 1/1/2.
- [ ] **3. KT Proposition 2.3, unconditional** (`F-121`; §1f.1). New
  `BodyHingeFramework.tfae_finrank_span_rigidityRows_ofHinge_deficiency` (`HingeGeneric.lean`):
  KT's (i) ⇔ (ii) ⇔ (iii) at a generic `q`, by M1 and `Graph.rank_add_deficiency_eq`.
  `prop:rigidity-matrix-prop11` states and pins it; `rigidityMatrix_prop11`, the conditional form
  Theorem 5.6's proofs use, gets its own node, and the three proofs that `\uses` the label for it
  (`cor:theorem-55-d3-spanning`, `thm:theorem-55-6-genuine`, `thm:theorem-55-6-multigraph`) move
  to the new one (else a cycle through `lem:hinge-point-witness`), with the Lean docstrings that
  name the label for it (`scripts/check-docstring-labels.py`). Where the KT node sits, beside the
  rank formula in `generic-lift.tex` or in place with a forward `\uses`, is the item's call.
  S/P/B 2/2/2.
- [ ] **Close**: the gates (whole-project build with 0 warnings, `lake lint`, the blueprint gates,
  the 20 main results' axioms), ROADMAP's row and §41, the design doc's MULTIGRAPH arc compressed,
  UNSTATED named next.

## Blockers / open questions

- None blocking. Not planned, for the PI if wanted: dropping `hcard` from M1 and KT Proposition
  2.3 (a transport to a larger label type), and relaxing `rigidityMatrix_prop11`'s `hC` to the
  non-loop links (free under §1f.3, unused).

## Hand-off / next phase

**Item 2**: transcribe the witness file's M1 sections (`HingeGeneric.lean`: drop `hSimple`,
`supportExtensor_ofHinge_ne_zero_of_isGenericHingePoints` loses `Loopless`, new
`exists_extensor_eq_of_extensorInPanel`, the `Nonvacuity.lean` witnesses, the blueprint and status
surfaces), as the checklist says. If it is more than one sitting, land the Lean half first and say so.

## Decisions made during this phase

- **The PI's decisions at the open** (2026-10-28): `notes/Phase41-design.md` §1g, verbatim.
- **Loops by relaxing the upper bound** (§1f.4; the open's recon): one commit, item 1. The
  alternative that leaves the upper bound alone (the rows' span ignores a loop's hinge, applied
  inside M1) costs no commit but is not the PI's reading; it is the fallback.
