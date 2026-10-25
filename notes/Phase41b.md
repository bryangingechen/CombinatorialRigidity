# Phase 41b — RESTATE: the main results restated on the linked carrier (work log)

**Status:** in progress (opened 2026-10-24), a sub-phase of Phase 41. The phase's design, the PI's
decisions (at the phase's open, §1; at this sub-phase's, §1b; after item 1's recon, §1c) and the
recons are in `notes/Phase41-design.md`. Items 1–6 done: Theorems 5.5 and 5.6, and their
`d = 3` instances, conclude KT's nonparallel panels for simple `G`, and `molecular_conjecture`
holds on one body. Next concrete task: item 7, the multigraph rows.

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
Next: the multigraph rows (item 7), then the remaining restatements. Mode: structural edit. There
are no red target nodes; each slice restates the nodes it reaches (`CombinatorialRigidity/CLAUDE.md`
*Forward-mode slices*).

## Architectural choices made up front

- **Statements change only as the design doc's §1, §1b and §1c say** (`notes/Reconcile.md` §2,
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
- [x] **2. `HasGenericFullRankRealization`'s last conjunct** (§1b.3; `376e3ac3`): the conjunct
  gone, its destructurers read the field; two helpers and the two `hswap` hypotheses gone.
- [x] **3. `F-324`** (`b2d0839a`): the twelve derivable `hD`s gone; four lemmas without `1 ≤ k`
  take `hk` for `hD : 2 ≤ D`; item 2's two dead helpers deleted.
- [x] **4a. The predicate** (`2c502d08`): `IsNonparallel` (the directions `Fin.init (P.normal a)`
  pairwise independent), `.isGeneralPosition`, `exists_nonparallel_polynomial`,
  `isNonparallel_ofParam`; `def:panel-nonparallel` (KT §5.1, p. 668; JJ 2010 §7).
- [x] **4b. Nonparallel from generic** (`39bc341c`): `HasNonparallelFullRankRealization` and
  `hasNonparallelFullRankRealization_of_generic`; `lem:nonparallel-of-generic` (KT Lemma 5.2's
  role).
- [x] **4c. Theorem 5.5's conclusion** (`4960364d`): the simple conjunct of
  `theorem_55_minimalKDof_gen`, `theorem_55_minimalKDof_k`, `theorem_55_d3` and the witness is
  `HasNonparallelFullRankRealization`; `thm:theorem-55`, `thm:theorem-55-d3-instance` and the
  `formalization.yaml` row restated.
- [x] **5. Theorem 5.6** (S2; §1b.1): `rankHypothesis_of_theorem_55_gen` concludes `Q.graph = G`,
  `Q.IsNonparallel` (the strip realization's normals, which `reaimSubLink` keeps; vacuous at one
  body) and the rank, keeps `hSimple`, drops `[DecidableEq β]` (`F-323`); `thm:theorem-55-6`
  restated; the link conjunct of the rows form
  `finrank_span_rigidityRows_genuine_recordsLinks_of_theorem_55_gen`, of
  `exists_rankHypothesis_isGeneralPosition4_of_two_le` and of its wrapper
  `exists_rankHypothesis_isGeneralPosition4` dropped; the wrapper also concludes `IsNonparallel`
  (design doc §1c.2: one more polynomial factor at its normals, after 4a gives the predicate;
  the `_of_two_le` form gains it where the wrapper's proof needs it), its blueprint node and
  `formalization.yaml` row restated; the witness.
  Done: as listed, and the genuine form concludes `IsNonparallel` too (*Decisions made*); the
  wrapper takes a third factor, `exists_nonparallel_polynomial`, at the same moment curve;
  `thm:theorem-55-6`, `thm:theorem-55-6-genuine`, `thm:theorem-55-6-rows`'s note and
  `lem:theorem-56-general-position` restated; the `main_results` row and the `alignment` note
  (whose degenerate-hinge sentence the restatement made false); the witness
  `rankHypothesis_of_theorem_55_gen_witness` at the single edge in the plane.
- [x] **5b. `rankHypothesis_of_theorem_55_d3`** (`F-329`; found at item 5): the nonparallel
  conjunct passed through the d = 3 instance, as item 4c passed Theorem 5.5's through
  `theorem_55_d3`; `thm:theorem-55-6-d3` and its note restated, the docstring rewritten. No
  `formalization.yaml` row, so no witness; no caller in the library.
- [x] **6. `molecular_conjecture`** (S2; §1.2): `V(G).Nonempty` for `2 ≤ |V(G)|`, nondegenerate
  hinges on `E(G)` on both sides, `[DecidableEq β]` dropped (`F-323`); the witness.
  Done: (⇒) reads `rankHypothesis_of_theorem_55_gen`, whose nonparallel panels give the hinges on
  `E(G)`; `thm:molecular-conjecture`, its note, `rem:molecular-conjecture-essential`,
  `rem:coplanar-single-body`, the two `formalization.yaml` rows and the multigraph docstrings'
  sentences on it restated. The witness `molecular_conjecture_witness` stays in its home
  (`Molecular/AlgebraicInduction/Nonvacuity.lean`, `PHASE-BOUNDARIES.md`), now at one body in the
  plane, the least input; `rem:molecular-conjecture-nonvacuous` with it. Nonparallel panels on the
  panel side come free (`F-330`, for the PI).
- [ ] **7. The multigraph rows** (§1.2, §1.4): `molecular_conjecture_multigraph` and
  `theorem_55_6_multigraph_gen` ask nondegeneracy on `E(G)`; `IsHingeCoplanar` constrains `E(G)`
  only; `F-323`'s binders.
- [ ] **8. `cor:theorem-55-d3-spanning`** (`F-126`): derived from `theorem_55_d3` under `hcard`,
  with general position and nondegenerate hinges on `E(G)`, `_hSimple` dropped.
  `rankHypothesis_deficiency_of_theorem_55_d3` takes a generic `hGP`; `theorem_55_d3` now gives the
  nonparallel one, whose realization is in general position (`IsNonparallel.isGeneralPosition`; no
  predicate-level lemma yet).
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
  remaining docstrings. The row and the note were restated at item 5; the other surfaces' "Theorem
  5.6 allows degenerate hinges" is false of `rankHypothesis_of_theorem_55_gen` since item 5 (true
  of the d = 3 instance until item 5b).
- [ ] **Close**: whole-project build with 0 warnings, `lake lint`, the blueprint gates, the main
  results' axioms; MULTIGRAPH or UNSTATED named next.

## Blockers / open questions

- **CI has not run since 2026-10-15**: the PI pushes after RESTATE closes (§1b), so that push is
  CI's first run of 41a's `module` conversion (doc-gen, the upstreaming dashboard). The close
  should expect to watch it.
- **For the PI, `F-330`** (item 6): `molecular_conjecture`'s iff also holds with `Q.IsNonparallel`
  on its panel side, at no cost (a `lake lean` witness); §1.2 does not name it, so the statement
  kept the panel side as it was.

## Hand-off / next phase

**Item 7**: the multigraph rows, as the checklist's item 7 says, with the witness
`molecular_conjecture_multigraph_witness` (`CombinatorialRigidity/Nonvacuity.lean`).
`molecular_conjecture_multigraph`'s `[DecidableEq β]` goes with `theorem_55_6_multigraph_gen`'s
(`F-323`; the comment above the latter). Its (⇒) lower bound already asks nondegeneracy at links
only, as item 6's did. `HasCoplanarPanelRealization` asks a nonzero hinge at every label
(`def:coplanar-panel-realization`'s note, `rem:molecular-conjecture-essential`): whether that
conjunct narrows with the two theorems, and so whether item 7 is one commit, is its first question.

## Decisions made during this phase

- **The PI's decisions at the open** (2026-10-24): `notes/Phase41-design.md` §1b, verbatim.
- **KT's nonparallel, route B** (item 1, 2026-10-24): `IsNonparallel` on the normals' directions,
  reached at Theorem 5.5's end by the genericity device; the induction keeps general position.
  Route A, nonparallel in the motive, was rejected by the PI (design doc §1c).
- **The PI's decisions after item 1's recon** (2026-10-24): `notes/Phase41-design.md` §1c,
  verbatim.
- **Item 3** (`F-324`): four lemmas without `1 ≤ k` take `hk` for `hD : 2 ≤ D`, a swap the
  ledger's "drop" needed (`D = 1` at `k = 0`); the `F-324` entry says which.
- **The genuine form concludes nonparallel too** (item 5; the coordinator's adjudication, not the
  PI's): `rankHypothesis_genuine_of_theorem_55_gen` gains `Q.IsNonparallel`, its hypotheses
  unchanged; it is how §1b.1 and §1c's Theorem 5.6 is built. The rows form keeps
  `Q.IsGeneralPosition` (its proof needs no upgrade); `rankHypothesis_of_theorem_55_d3` kept its
  statement at item 5 (`F-329`).
- **The d = 3 instance passes the conjunct through** (item 5b; the coordinator's adjudication):
  `F-128` names `thm:theorem-55-6-d3`, whose conclusion the framework with all normals zero meets at
  deficiency zero (S2's gap), so keeping the statement would leave `F-128` open at `d = 3`. The
  option to keep it is rejected.
