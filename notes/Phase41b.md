# Phase 41b — RESTATE: the main results restated on the linked carrier (work log)

**Status:** ✓ closed 2026-10-25 (opened 2026-10-24), a sub-phase of Phase 41, which stays in
progress. The phase's design, the PI's decisions (at the phase's open, §1; at this sub-phase's,
§1b; after item 1's recon, §1c; on `F-330`, §1d; on the generic panel theorems' body bound, §1e; in
advance, §1f) and the recons are in `notes/Phase41-design.md`. Every checklist item landed, in 23
commits with the open and the close. The PI's push ran CI green (2026-10-25), and MULTIGRAPH
opened as 41c on 2026-10-28 (`notes/Phase41c.md`).

## Current state

**Closed.** S1's and S2's main results are restated on the carrier to which 41a gave the link
field, as the PI decided (design doc §1b–§1f). Theorems 5.5 and 5.6 and their `d = 3` instances
conclude KT's nonparallel panels (`IsNonparallel`) for simple `G`, reached at Theorem 5.5's end by
the genericity device (route B), so every hinge at an edge is nondegenerate.
`molecular_conjecture` holds on `V(G).Nonempty`, both sides asking a nonzero hinge on `E(G)`, its
panel side nonparallel panels too. The multigraph rows ask nondegeneracy on `E(G)`, and
`IsHingeCoplanar` constrains `E(F.graph)` only. `cor:theorem-55-d3-spanning` derives from
`theorem_55_d3`. The generic panel and body-hinge theorems hold at every generic realization on
`G`, one body or more, under the label bound `hcard` of Theorem 5.6, so they cover the simple
minimal `k`-dof-graphs; the panel rank formula is a twentieth `main_results` row, and the new and
restated rows have witnesses at the single edge and the triangle (`Nonvacuity.lean`).
`prop:rigidity-matrix-prop11` is KT Proposition 2.3 for a body-hinge framework on a multigraph, in
conditional form. The status surfaces say so. At the close the 20 main results' axioms are
`[propext, Classical.choice, Quot.sound]`, the output byte-identical to 41a's close run with the new
row added. The close's re-read of the restated nodes found two false sentences, fixed first in their
own commit (`810cb2d6`, with `F-133`'s last code). Mode: structural edit, no red target nodes.

## Architectural choices made up front

- **Statements change only as the design doc's §1 and §1b–§1f say** (`notes/Reconcile.md` §2,
  *Hygiene*); a free strengthening is adopted only under §1f.3, recorded in the design doc.
- **Each restated main result lands with its non-vacuity witness** in
  `CombinatorialRigidity/Nonvacuity.lean`, its `formalization.yaml` row in the same commit.
- **Ledger.** Each commit names the ledger IDs it acts on and gives each its `done (<sha>)`
  disposition (`notes/Reconcile.md` §2).
- **One commit per dispatch** (dispatch-log F53). PI entries are never compressed (F50).

## Lemma checklist

- [x] **1. Recon: KT's nonparallel** (§1b.4): route B, design doc §2; witness `NonparallelWitness.lean`.
- [x] **2.** `HasGenericFullRankRealization`'s last conjunct (`376e3ac3`). **3.** `F-324`: twelve
  derivable `hD`s gone (`b2d0839a`).
- [x] **4a–4c.** `IsNonparallel` (`2c502d08`); nonparallel from generic (`39bc341c`); Theorem 5.5's
  simple conjunct is `HasNonparallelFullRankRealization` (`4960364d`).
- [x] **5, 5b.** Theorem 5.6, its genuine form, the rows form, the wrapper and the `d = 3` instance
  conclude `IsNonparallel`, the link conjuncts gone (`5c70542c`, `da20d498`; `F-323`, `F-329`).
- [x] **6, 6b.** `molecular_conjecture` on `V(G).Nonempty`, hinges on `E(G)`, panel side gains
  `Q.IsNonparallel` (`68d5ea84`, `9f7f73ee`; `F-330`, §1d); its witness restated.
- [x] **7.** The multigraph rows ask nondegeneracy on `E(G)`; `IsHingeCoplanar` constrains `E(G)`
  only (`6d261725`).
- [x] **8. `cor:theorem-55-d3-spanning`** (`F-125`, `F-126`): from `theorem_55_d3` (`8c2d4475`).
- [x] **9a, 9b. S1, the panel theorems** (design doc §2, *Item 9's recon*): every `Q` on `G` with
  generic normals (`24d9d0cc`); the rank formula a `main_results` row, at the single edge
  (`ce98d5ec`).
- [x] **10a, 10b. S1, the body-hinge theorems** (design doc §2, *Item 10's recon*): genericity over
  `G`, witnessed at the triangle (`96683b73`); the S1 scope sentences (`43f78c5f`, with item 12).
- [x] **11. S18** (`prop:rigidity-matrix-prop11`; `F-121`, `F-331`; §1f.1): KT Proposition 2.3,
  conditional (`c26edc57`). The unconditional repin is MULTIGRAPH's M1 (design doc §3).
- [x] **12. The degenerate-hinge sentences** (with 10b, `43f78c5f`; `F-130`).
- [x] **Close**: the re-read's two false sentences first (`810cb2d6`); then the gates (whole-project
  build with 0 warnings, `lake lint`, the blueprint gates, the 20 main results' axioms), ROADMAP's
  row and §41, the design doc's RESTATE arcs compressed, MULTIGRAPH or UNSTATED named next. The loop
  **stops for the PI's push** (§1f.2): no next sub-phase opens.

## Blockers / open questions

- None. The push's CI run, the first of 41a's `module` conversion, was green (*Build & deploy
  site*, run 40229429653 at `ae6a852c`, 2026-10-25). Carried to 41c: `prop:rigidity-matrix-prop11`'s
  unconditional repin (§1f.1) and M1, the generic body-hinge theorem for multigraphs.

## Hand-off / next phase

**Successor: 41c (MULTIGRAPH)**, opened 2026-10-28 with the PI (design doc §1g); its next task is
in `notes/Phase41c.md`. UNSTATED stays for the PI after it.

## Decisions made during this phase

- **The PI's decisions at the open** (2026-10-24): `notes/Phase41-design.md` §1b, verbatim.
- **KT's nonparallel, route B** (item 1, 2026-10-24): `IsNonparallel` on the normals' directions,
  reached at Theorem 5.5's end by the genericity device; the induction keeps general position.
  Route A, nonparallel in the motive, was rejected by the PI (design doc §1c).
- **The PI's decisions after item 1's recon** (2026-10-24): `notes/Phase41-design.md` §1c,
  verbatim.
- **The PI's decision on `F-330`** (2026-10-25): `notes/Phase41-design.md` §1d, verbatim.
- **The PI's decision on the generic panel theorems' body bound** (2026-10-25):
  `notes/Phase41-design.md` §1e, verbatim.
- **The PI's answers in advance** (2026-10-25; S18, RESTATE's close, free strengthenings, M1's
  loops): `notes/Phase41-design.md` §1f, verbatim.
- **Item 3** (`F-324`): four lemmas without `1 ≤ k` take `hk` for `hD : 2 ≤ D`.
- **Items 5, 5b** (coordinator): the genuine form gains `Q.IsNonparallel`, the rows form keeps
  general position; the `d = 3` instance passes it through.
- **Item 7** (§1.2, §1.4; coordinator): `HasCoplanarPanelRealization` stays total.
- **Item 8** (coordinator): the corollary keeps `hV`, `hSimple` (false at the double edge without
  it, `restated_theorem56_false_at_banana`) and `[DecidableEq β]` (for `IsMinimalKDof`).
- **Items 9, 10** (design doc §2): genericity the framework's at its edges (9), over every
  recording selector (10); Theorem 5.6's main form the witness; no twin; `hk1`, `hn` stay (10).
- **One body under §1f.3** (item 10a; coordinator): `hne` for `hV`, §1e's pattern (design doc §2).
- **Items 10b and 12 in one commit**, and **item 11 with no Lean bridge** (coordinator): §1f.1
  asks the conditional form, which `rigidityMatrix_prop11` proves.
- **The close's re-read as its own commit first** (`810cb2d6`): the hand-off's rule for a false
  sentence; `HasCoplanarPanelRealization`'s docstring rode with it.
