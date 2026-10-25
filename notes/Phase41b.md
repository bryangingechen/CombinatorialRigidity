# Phase 41b — RESTATE: the main results restated on the linked carrier (work log)

**Status:** in progress (opened 2026-10-24), a sub-phase of Phase 41. The phase's design, the PI's
decisions (at the phase's open, §1, and at this sub-phase's, §1b) and the recons are in
`notes/Phase41-design.md`. Items 1 (KT's nonparallel by route B, items 4a–4c; the PI settled its two
open options, design doc §1c), 2 and 3 done. Next concrete task: item 4a, the predicate
`IsNonparallel`.

## Current state

Opened with the PI on 2026-10-24, after the RESTATE open's recon (`notes/Phase41-design.md` §2,
*RESTATE's open recon*). Item 2 is its first Lean change: `HasGenericFullRankRealization` is
`∃ Q, Q.graph = G ∧ Q.IsGeneralPosition ∧` the rank, and its destructurers read the selector's
links off the field `isLink_ends`. Item 1's design pass (design doc §2, *KT's nonparallel recon*)
defined KT's nonparallel on the normals' direction parts (the affine coordinate
is the last) and reaches it at Theorem 5.5's end by the genericity device, the induction untouched
(route B), in three commits, items 4a–4c. The sub-phase restates S2's and S1's main results
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

Item 1's verdict keeps item 4 after items 2 and 3 and before item 5.

- [x] **1. Recon: KT's nonparallel** (§1b.4; design pass, 2026-10-24): route B, in the design
  doc's §2 (*KT's nonparallel recon*); witness `notes/reconcile-formal/NonparallelWitness.lean`.
- [x] **2. `HasGenericFullRankRealization`'s last conjunct** (§1b.3): its producers and
  destructurers, the two dead helpers, `def:rank-hypothesis`'s prose; the two `hswap` hypotheses of
  `Coupling.lean` and the hand-built link sites the field gives (design doc §2). Done: the
  conjunct, `ofNormals_recordsLinks_of_hends` and `ofNormals_endsOf_recordsLinks` gone; `hswap` gone
  from `infinitesimalMotions_ofNormals_eq_of_ends_swap` and `hasGenericRealization_transport_ends`
  (both selectors record the links); the link sites at `CaseII.lean`, `CaseIII/Realization.lean`
  and `Theorem55.lean` read the field; `fmlnote:generic-full-rank` and the note after
  `lem:case-cut-edge-realization-gp` restated. Two helpers lost their callers (*Blockers*).
- [x] **3. `F-324`**: `theorem_55_minimalKDof_gen`'s derivable `hD` and the chain below it
  (`F-293`, `F-297`, `F-298`). Done: the twelve `hD`s gone, each body deriving the bound it uses;
  four lemmas that took no `1 ≤ k` swap `hD : 2 ≤ D` for `hk` (`D = 1` at `k = 0`); the callers
  already derived theirs; the two dead helpers of item 2 deleted.
- [ ] **4a. The predicate** (§1b.4; `PanelHinge.lean`): `PanelHingeFramework.IsNonparallel` beside
  `IsGeneralPosition` (the directions `Fin.init (P.normal a)` of any two distinct bodies of `α`
  independent), `IsNonparallel.isGeneralPosition`, `exists_nonparallel_polynomial` under `1 ≤ k`
  (the product of `exists_generalPosition_polynomial`, nonparallel at its non-roots) and
  `isNonparallel_ofParam`; proofs: the witness's `IsNonparallel.isGeneralPosition`,
  `isNonparallel_of_eval_ne_zero`, `momentCurve_nonparallel`. Blueprint: a new
  `def:panel-nonparallel` from the paragraph after `def:panel-general-position` (KT §5.1, p. 668;
  `jacksonJordan2009` §7), the definition-faithfulness gate; `lem:moment-curve-general-position`
  extended to nonparallel for `d ≥ 2`; `IsGeneralPosition`'s docstring points at it.
- [ ] **4b. Nonparallel from generic** (`PanelHinge.lean`, `GenericityDevice.lean`):
  `HasNonparallelFullRankRealization` beside `HasGenericFullRankRealization` (`∃ Q, Q.graph = G ∧
  Q.IsNonparallel ∧` the rank) and `hasNonparallelFullRankRealization_of_generic` (`1 ≤ k`, `hn`,
  `G.Loopless`, `V(G).Nonempty`), whose proof is the witness's `exists_nonparallel_of_generic`.
  Blueprint: `def:rank-hypothesis` pins the third predicate; a new `lem:nonparallel-of-generic`
  (KT Lemma 5.2's role, p. 669), using `lem:rank-polynomial-of-le-finrank`,
  `lem:relative-deficiency-rank-bound` and `def:panel-nonparallel`.
- [ ] **4c. Theorem 5.5's conclusion** (`Theorem55.lean`, `Nonvacuity.lean`):
  `theorem_55_minimalKDof_gen`'s simple conjunct becomes `HasNonparallelFullRankRealization`, by
  4b from the induction's, passed through `theorem_55_minimalKDof_k`, `theorem_55_d3` and
  `theorem_55_minimalKDof_gen_witness`; proofs only of `rankHypothesis_genuine_of_theorem_55_gen`
  and the rows form; `thm:theorem-55` and `thm:theorem-55-d3-instance` restated; the main result's
  `formalization.yaml` row ("generic for simple G"); `HasGenericFullRankRealization`'s docstring.
- [ ] **5. Theorem 5.6** (S2; §1b.1): `rankHypothesis_of_theorem_55_gen` concludes `Q.graph = G`,
  `Q.IsNonparallel` (the strip realization's normals, which `reaimSubLink` keeps; vacuous at one
  body) and the rank, keeps `hSimple`, drops `[DecidableEq β]` (`F-323`); `thm:theorem-55-6`
  restated; the link conjunct of the rows form
  `finrank_span_rigidityRows_genuine_recordsLinks_of_theorem_55_gen`, of
  `exists_rankHypothesis_isGeneralPosition4_of_two_le` and of its wrapper
  `exists_rankHypothesis_isGeneralPosition4` dropped; the wrapper also concludes `IsNonparallel`
  (design doc §1c.2: one more polynomial factor at its normals, after 4a gives the predicate;
  the `_of_two_le` form gains it where the wrapper's proof needs it), its blueprint node and
  `formalization.yaml` row restated; the witness.
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

- **CI has not run since 2026-10-15**: the PI pushes after RESTATE closes (§1b), so that push is
  CI's first run of 41a's `module` conversion (doc-gen, the upstreaming dashboard). The close
  should expect to watch it.

## Hand-off / next phase

**Item 4a**: the predicate `IsNonparallel` (item 3 landed). Then items 4b and 4c, one commit each,
then item 5. 4b's proof is the witness's `exists_nonparallel_of_generic`, nearly
verbatim, but its `obtain` of `HasGenericFullRankRealization` takes four components since item 2
(the witnesses of `notes/reconcile-formal/` check at their own commits, not at item 2's).

## Decisions made during this phase

- **The PI's decisions at the open** (2026-10-24): `notes/Phase41-design.md` §1b, verbatim.
- **KT's nonparallel, route B** (item 1, 2026-10-24): `IsNonparallel` on the normals' directions,
  reached at Theorem 5.5's end by the genericity device; the induction keeps general position.
  Route A, nonparallel in the motive, needs `1 ≤ k` on about a dozen producers, and stays a PI
  option (design doc §2, *KT's nonparallel recon*; §4).
- **The PI's decisions after item 1's recon** (2026-10-24): `notes/Phase41-design.md` §1c, verbatim.
- **Item 3** (`F-324`): four lemmas without `1 ≤ k` take `hk` for `hD : 2 ≤ D`, a swap the ledger's
  "drop" needed (`D = 1` at `k = 0`); the `F-324` entry says which.
