# Phase 41b — RESTATE: the main results restated on the linked carrier (work log)

**Status:** in progress (opened 2026-10-24), a sub-phase of Phase 41. The phase's design, the PI's
decisions (at the phase's open, §1; at this sub-phase's, §1b; after item 1's recon, §1c; on
`F-330`, §1d; on the generic panel theorems' body bound, §1e; in advance, §1f) and the recons are in
`notes/Phase41-design.md`. Items 1–9 done: Theorems 5.5 and 5.6, and their `d = 3` instances,
conclude KT's nonparallel panels for simple `G`, `molecular_conjecture` holds on one body with
nonparallel panels on its panel side, the multigraph rows ask nondegeneracy on `E(G)`, the `d = 3`
spanning corollary derives from `theorem_55_d3`, and the generic panel theorems hold at every
framework on `G` with generic normals, their rank formula a main result (item 9b). Item 10's
design pass split the body-hinge theorems into 10a and 10b.
Next concrete task: item 10a, the body-hinge restatement with its row's witness.

## Current state

Opened with the PI on 2026-10-24, after the RESTATE open's recon (`notes/Phase41-design.md` §2,
*RESTATE's open recon*). The sub-phase restates S2's and S1's main results on the carrier to which
41a gave the link field, and acts on the PI's decisions at its open (§1b) and after item 1's recon
(§1c). So far: `HasGenericFullRankRealization` lost its link conjunct (item 2); the derivable `hD`
chain is gone (item 3); KT's nonparallel panels are `IsNonparallel` (item 4a); a generic full-rank
realization gives a nonparallel one (item 4b, route B); Theorem 5.5's simple conjunct states it
(item 4c); and Theorem 5.6, its genuine form and the d = 3 wrapper conclude it, the link conjuncts
of the rows form and the wrapper gone (item 5). The d = 3 instance of Theorem 5.6 passes the
conjunct through too (item 5b, `F-329`). `molecular_conjecture` takes `V(G).Nonempty` and asks
nondegenerate hinges on `E(G)` only (item 6), its panel side from Theorem 5.6's nonparallel panels.
The multigraph rows are restated: `molecular_conjecture_multigraph`'s body-hinge side asks nonzero
hinges on `E(G)`, `IsHingeCoplanar` constrains `E(F.graph)` only, both lose `[DecidableEq β]` (item
7). The `d = 3` spanning corollary derives from `theorem_55_d3`, concluding nonparallel panels and
nondegenerate hinges on `E(G)` (item 8). Item 9's design pass (`notes/Phase41-design.md` §2,
*Item 9's recon*) compiled the restated panel theorems in
`notes/reconcile-formal/PanelGenericWitness.lean` and split the item into 9a (the restatement) and
9b (G6's row). Item 9a restated `PanelGeneric.lean`: genericity is the framework's, over the rows at
the edges of its graph; the rank formula and its iff range over every framework on `G` with generic
normals, under Theorem 5.6's `hd`, `hcard` and, by the PI's §1e, `V(G).Nonempty`; their witness is
Theorem 5.6's main form. Item 9b made the rank formula a `main_results` row, witnessed at the
single edge, and narrowed the S1 scope sentences to the body-hinge theorem. The PI answered four
questions in advance (§1f): item 11's form, the stop at RESTATE's close, free strengthenings, M1's
loops. Item 10's design pass (design doc §2, *Item 10's recon*) compiled the restated body-hinge
theorems in `notes/reconcile-formal/HingeGenericWitness.lean`, adopted one body under §1f.3, and
split the item into 10a (the restatement, with the row's witness) and 10b (the scope sentences).
Next: item 10a, then the remaining restatements. Mode: structural edit. There
are no red target nodes; each slice restates the nodes it reaches (`CombinatorialRigidity/CLAUDE.md`
*Forward-mode slices*).

## Architectural choices made up front

- **Statements change only as the design doc's §1 and §1b–§1f say** (`notes/Reconcile.md` §2,
  *Hygiene*): any other statement change is recorded as an `S` entry and not acted on, except a
  conclusion strengthened at no proof cost or a hypothesis relaxed that the proof does not need,
  which the coordinator may adopt under the PI's standing policy, "Adopt, record it" (design doc
  §1f.3: only the theorem at hand, an approved pattern, recorded there). A prompt that bars an
  edit names the neighbouring edits it allows (dispatch-log F51).
- **Each restated main result lands with its non-vacuity witness** in
  `CombinatorialRigidity/Nonvacuity.lean` (`PHASE-BOUNDARIES.md` *When this commit closes a
  phase*); its `formalization.yaml` row follows in the same commit.
- **Ledger.** Each commit names the ledger IDs it acts on (S2: `F-122`, `F-125`, `F-128`; S1:
  `F-207`, with `F-206`, `F-216`, `F-221`; `F-126`, `F-323`, `F-324`) and gives each entry its
  `done (<sha>)` disposition (`notes/Reconcile.md` §2).
- **One commit per dispatch** (dispatch-log F53). PI entries are never compressed (F50).

## Lemma checklist

Item 1's verdict keeps item 4 after items 2 and 3 and before item 5.

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
- [x] **8. `cor:theorem-55-d3-spanning`** (`F-126`): derived from `theorem_55_d3`, concluding
  `IsNonparallel`, hinges on `E(G)` and the rank; `hV` and `hSimple` used (*Decisions made*); moved
  below `theorem_55_d3`.
- **9. S1, the panel theorems** (`PanelGeneric.lean`; S13; §1b.2), in two commits; design doc §2,
  *Item 9's recon*, whose spike `notes/reconcile-formal/PanelGenericWitness.lean` is the Lean.
  - [x] **9a. The restatement**: `Q.IsGenericNormals` (rows at `E(Q.graph)`, its own selector)
    with the orientation lemmas; the abundance, existence, nondegeneracy and transplant restated;
    the rank formula and the iff renamed, over every `Q` on `G`, with `hd`, `hcard`, `hne` (§1e);
    the nodes, fmlnotes, repoints and `formalization.yaml:501`, `:803`–`:810` (`F-206`; the panel
    halves of `F-207`, `F-252`; S13's panel side).
  - [x] **9b. G6's row**: `finrank_span_rigidityRows_of_isGenericNormals` a `main_results` row,
    its witness at the single edge in `Nonvacuity.lean`; the S1 scope sentences name the
    body-hinge theorem only (`F-012`'s PI item; `F-207`).
- **10. S1, the body-hinge theorems** (`HingeGeneric.lean`; S13; §1b.2's form; `F-207`, `F-252`,
  `F-216`, `F-221`, `F-212`), in two commits; design doc §2, *Item 10's recon*, whose spike
  `notes/reconcile-formal/HingeGenericWitness.lean` is the Lean (names as there).
  - [ ] **10a. The restatement, with the row's witness** (Lean, blueprint, yaml).
    `HingeGeneric.lean`: `IsGenericHingePoints G q` (every selector with `RecordsLinks G`, rows at
    `E(G)`); new
    `hingePointRow_eq_neg_of_swap`, `linearIndependent_hingePointRow_iff_of_recordsLinks`,
    `isGenericHingePoints_iff_of_recordsLinks`, `isGenericHingePoints_congr`; the abundance and the
    existence over `G` (product over the selectors); the nondegeneracy at `E(G)`; the witness
    assembly from `rankHypothesis_of_theorem_55_gen` at a recording selector, indices at edges; the
    rank formula, the iff and the spanning-trees row under `hk1`, `hn`, `hcard`, `hne` (§1f.3),
    `hspan`, `hSimple` (gone: `hfresh`, `ends`, `hends`, `hD`, `hV`, `[DecidableEq β]`,
    `[Nonempty α]`). The header and docstrings; `dualBodyMap_hingeRow`'s and
    `mapExtensor_rigidityRows`'s leads ("a step of"), `blueprint/lint.sh` check 9 baseline 2 → 0.
    `Nonvacuity.lean`: `…_iff_spanningTrees_witness` at the triangle (with its minimality), the
    `public import`, the header. Docstrings of `RecordsLinks.of_forall` (`PanelHinge.lean:125`) and
    the genuine form (`Theorem55.lean:2091`). `generic-lift.tex`: `def:generic-hinge-points` (pins
    4–5), its remark and fmlnote, `lem:hinge-point-witness`, `thm:bodyhinge-generic-rank`,
    `cor:bodyhinge-generic-rigid`, `cor:bodyhinge-generic-tree-packing`, the fmlnote after it, the
    chapter and section openings; `body-hinge.tex:79`, `:156`. `formalization.yaml:491`, `:808`.
  - [ ] **10b. The S1 scope sentences removed** (docs only): README `:162`, `home_page/index.md:142`,
    `intro.tex:266`, ROADMAP §34 `:1042`; `F-207`'s last disposition.
- [ ] **11. S18** (`prop:rigidity-matrix-prop11`; `F-121`, `F-331`; the PI's §1f.1): restated as
  KT state Proposition 2.3, a generic body-hinge framework on a multigraph (KT p. 655, credited to
  Jackson–Jordán), not a panel-hinge realization; proved in the conditional form (the bound gives
  the formula), citing item 10's generic body-hinge theorem for simple graphs. The unconditional
  repin waits for MULTIGRAPH's M1 (design doc §3).
- [ ] **12. The status surfaces**: the degenerate-hinge sentences (Theorem 5.6's `main_results` row
  and `alignment` note, README, the home page, `intro.tex`, ROADMAP §23) and the footprint's
  remaining docstrings. The row and the note were restated at item 5; the other surfaces' "Theorem
  5.6 allows degenerate hinges" is false of `rankHypothesis_of_theorem_55_gen` since item 5 (true
  of the d = 3 instance until item 5b).
- [ ] **Close**: whole-project build with 0 warnings, `lake lint`, the blueprint gates, the main
  results' axioms; MULTIGRAPH or UNSTATED named next. Then the loop **stops for the PI's push**
  (§1f.2), CI's first run of 41a's `module` conversion: no next phase opens.

## Blockers / open questions

- **CI has not run since 2026-10-15**: the PI pushes after RESTATE closes (§1b), so that push is
  CI's first run of 41a's `module` conversion (doc-gen, the upstreaming dashboard). The loop stops
  at the close for that push (§1f.2).

## Hand-off / next phase

**Item 10a** (checklist 10a): restate `HingeGeneric.lean` from the spike
`notes/reconcile-formal/HingeGenericWitness.lean`, whose proofs are written in place (the
abundance, the nondegeneracy, the witness assembly, the rank formula); add the row's witness to
`Nonvacuity.lean`; restate the nodes, the yaml row and its note; clear the two docstring-label
findings. A statement edit to `HingeGeneric.lean` rebuilds the pencil chain through
`Pencil/Arms.lean`. Gates: the whole-project build with 0 warnings, `lake lint`,
`blueprint/verify.sh`, `blueprint/lint.sh` at baseline 0, `check-docstring-labels.py`. Then 10b.

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
- **Item 3** (`F-324`): four lemmas without `1 ≤ k` take `hk` for `hD : 2 ≤ D` (`D = 1` at `k = 0`).
- **The genuine form concludes nonparallel too** (item 5; the coordinator's adjudication):
  `rankHypothesis_genuine_of_theorem_55_gen` gains `Q.IsNonparallel`, hypotheses unchanged; the rows
  form keeps `Q.IsGeneralPosition`.
- **The d = 3 instance passes the conjunct through** (item 5b; the coordinator's adjudication):
  `F-128` names `thm:theorem-55-6-d3`, whose conclusion all-zero normals meet (S2's gap); keeping
  the statement would leave `F-128` open at `d = 3`.
- **The multigraph rows** (item 7; §1.2 and §1.4 are the PI's, the totality of `HasCoplanarPanelRealization` the coordinator's):
  `HasCoplanarPanelRealization` keeps its total conjunct (the pencil main result concludes it; the
  containment model realizes it on one body). So `molecular_conjecture_multigraph`'s body-hinge
  side asks `∀ e ∈ E(G)`, its panel side stays total; `IsHingeCoplanar` constrains `E(F.graph)`
  only (the PI's §1.4: the restriction is the PI's; the coordinator's call was only to keep
  `HasCoplanarPanelRealization` total); both results lose `[DecidableEq β]` (`F-323` done for both
  rows).
- **Item 9's design** (2026-10-25; design doc §2, *Item 9's recon*): the predicate is the
  framework's, over the rows at its edges, which do not depend on the selector's orientation; the
  rank formula's witness is Theorem 5.6's main form, whose nonparallel panels give nondegeneracy on
  `E(G)`. No file outside `PanelGeneric.lean` reads its declarations (docstrings only), so no pencil
  statement moves and 9a needs no twin.
- **Item 10's design** (2026-10-25; design doc §2, *Item 10's recon*): genericity at every
  selector that records the links of `G` (no framework selector; a swap negates a row), equal to
  one selector's by a lemma; Theorem 5.6's main form is the witness, as the transplant needs nondegeneracy at edges
  only; `hk1` and `hn` stay (`Fin k` points; § 48 poisons `n - 1 + 1`); one body adopted under
  §1f.3. The row's witness is the triangle with the shadow labels. Nothing outside the file reads
  the declarations, so 10a is one commit with no twin.
- **Item 9a's pins**: `def:generic-normals` gains a third pin, `isGenericNormals_iff_of_graph_eq`, for
  its note's claim that genericity reads only the graph and the normals; the other two orientation
  lemmas and the spike's selector-free abundance are not pinned (the latter not landed).
- **The corollary keeps `hV` and `hSimple`** (item 8; the coordinator's scope-pin): the realization
  comes from `theorem_55_d3`, whose nonparallel conjunct needs `G.Simple`; without it the statement
  is false at the double edge on two bodies, a minimal `0`-dof-graph at `d = 3` whose two meet-model
  hinges coincide (`notes/reconcile-formal/RestateWitness.lean`, `restated_theorem56_false_at_banana`).
  So the checklist's "`_hSimple` dropped" became "used". The statement keeps `[DecidableEq β]`,
  which `IsMinimalKDof` needs; the conclusion passes `IsNonparallel` through, which implies the
  design doc's general position. The declaration moved below `theorem_55_d3`.
