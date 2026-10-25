# Phase 41b — RESTATE: the main results restated on the linked carrier (work log)

**Status:** in progress (opened 2026-10-24), a sub-phase of Phase 41. The phase's design, the PI's
decisions (at the phase's open, §1; at this sub-phase's, §1b; after item 1's recon, §1c; on
`F-330`, §1d) and the recons are in `notes/Phase41-design.md`. Items 1–8 done: Theorems 5.5 and
5.6, and their `d = 3` instances, conclude KT's nonparallel panels for simple `G`,
`molecular_conjecture` holds on one body with nonparallel panels on its panel side (item 6b), the
multigraph rows ask nondegeneracy on `E(G)` (item 7), and the `d = 3` spanning corollary derives
from `theorem_55_d3` (item 8). Item 9's design pass split it in two. Next concrete task: item 9a,
S1's panel theorems restated (`PanelGeneric.lean`).

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
9b (G6's row). Next: item 9a, then the remaining restatements. Mode: structural edit. There are no
red target nodes; each slice restates the nodes it reaches (`CombinatorialRigidity/CLAUDE.md`
*Forward-mode slices*).

## Architectural choices made up front

- **Statements change only as the design doc's §1, §1b, §1c and §1d say** (`notes/Reconcile.md` §2,
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
  - [ ] **9a. The restatement.** `IsGenericNormals` becomes the framework's `Q.IsGenericNormals`
    (rows at `E(Q.graph)`, its own selector); the abundance takes `G`, `ends` and
    `RecordsLinks G ends`; `exists_isGenericNormals` gives `∃ Q, Q.graph = G ∧ Q.IsGenericNormals`;
    the transplant loses `G`, `hQends` and the total `hC`; renamed
    `supportExtensor_ne_zero_of_isGenericNormals`, `finrank_span_rigidityRows_of_isGenericNormals`
    and `isInfinitesimallyRigidOn_of_isGenericNormals_iff`, the last two over every `Q` on `G`
    with Theorem 5.6's `hd`, `hcard`, and no `ends`, `hends`, `[DecidableEq β]`. Nodes:
    `def:generic-normals`, `fmlnote:generic-normals-selector`, `lem:generic-normals-abundance`,
    `lem:exists-generic-normals`, `lem:generic-normals-nondegenerate`,
    `lem:panel-witness-transplant`, `thm:panel-generic-rank` (its proof `\uses`
    `thm:theorem-55-6`), `cor:panel-generic-rigid` and the fmlnotes after the last three; the
    renames' repoints and the false docstrings the recon's *Cascade* lists, with
    `formalization.yaml:501` and `:803`–`:810`. One commit: nothing outside the file reads the six
    declarations. Ledger: `F-206` done; the panel half of `F-207` and `F-252`.
  - [ ] **9b. G6's row.** `finrank_span_rigidityRows_of_isGenericNormals` as a `main_results` row
    of `formalization.yaml`, its witness at the single edge in `Nonvacuity.lean` (the spike's
    `…_witness`; a `public import` of `PanelGeneric`); the S1 scope sentences (README, home page,
    `intro.tex`, ROADMAP §34, `formalization.yaml:503`, `:795`) narrowed to the body-hinge theorem.
    Ledger: `F-012`'s PI item, the panel form a main result.
- [ ] **10. S1, the body-hinge theorems** (`HingeGeneric.lean`): `hcard` for `hfresh`,
  `IsGenericHingePoints` oriented by the links, no `ends`, `hends` or `hD`; the spanning-trees row
  restated; the docstring-label check's two findings (`HingeGeneric.lean:477`, `:486`) cleared and
  its baseline lowered; the S1 scope sentences removed. Item 9's recon does not reach its predicate
  (`BodyHingeFramework` has no selector): a design pass with a spike first, as item 9's.
- [ ] **11. S18** (`prop:rigidity-matrix-prop11`): the conditional statement, or a repin on the
  generic forms.
- [ ] **12. The status surfaces**: the degenerate-hinge sentences (Theorem 5.6's `main_results` row
  and `alignment` note, README, the home page, `intro.tex`, ROADMAP §23) and the footprint's
  remaining docstrings. The row and the note were restated at item 5; the other surfaces' "Theorem
  5.6 allows degenerate hinges" is false of `rankHypothesis_of_theorem_55_gen` since item 5 (true
  of the d = 3 instance until item 5b).
- [ ] **Close**: whole-project build with 0 warnings, `lake lint`, the blueprint gates, the main
  results' axioms; MULTIGRAPH or UNSTATED named next.

## Blockers / open questions

- **CI has not run since 2026-10-15**: the PI pushes after RESTATE closes (§1b), so that push is
  CI's first run of 41a's `module` conversion (doc-gen, the upstreaming dashboard). The close
  should expect to watch it.

## Hand-off / next phase

**Item 9a**: restate `PanelGeneric.lean` from the spike
`notes/reconcile-formal/PanelGenericWitness.lean` (the planned names, in its own namespace; the
abundance keeps its old body, the new hypothesis ignored at its last line), with the nodes and
repoints of the checklist's item 9a. One dispatch. Before it, the coordinator may put the design
doc's §4 one-body item to the PI: 9a can take `hV` or `V(G).Nonempty` (the spike compiles both).
Then 9b.

## Decisions made during this phase

- **The PI's decisions at the open** (2026-10-24): `notes/Phase41-design.md` §1b, verbatim.
- **KT's nonparallel, route B** (item 1, 2026-10-24): `IsNonparallel` on the normals' directions,
  reached at Theorem 5.5's end by the genericity device; the induction keeps general position.
  Route A, nonparallel in the motive, was rejected by the PI (design doc §1c).
- **The PI's decisions after item 1's recon** (2026-10-24): `notes/Phase41-design.md` §1c,
  verbatim.
- **The PI's decision on `F-330`** (2026-10-25): `notes/Phase41-design.md` §1d, verbatim.
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
- **The corollary keeps `hV` and `hSimple`** (item 8; the coordinator's scope-pin): the realization
  comes from `theorem_55_d3`, whose nonparallel conjunct needs `G.Simple`; without it the statement
  is false at the double edge on two bodies, a minimal `0`-dof-graph at `d = 3` whose two meet-model
  hinges coincide (`notes/reconcile-formal/RestateWitness.lean`, `restated_theorem56_false_at_banana`).
  So the checklist's "`_hSimple` dropped" became "used". The statement keeps `[DecidableEq β]`,
  which `IsMinimalKDof` needs; the conclusion passes `IsNonparallel` through, which implies the
  design doc's general position. The declaration moved below `theorem_55_d3`.
