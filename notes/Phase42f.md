# Phase 42f — PD-STEPS: cut vertices, bridges and contraction in every dimension (work log)

**Status:** ✓ closed 2026-10-30 (opened the same day at the PI's word, "-cut + -contract
(Recommended)", design doc §1), a sub-phase of Phase 42, which stays in progress with no sub-phase
open. Forward mode, the Lean under `/coordinate-phase`: the six nodes of
`blueprint/src/chapter/pencil-d.tex` in `sec:pencil-d-cut` and `sec:pencil-d-contract` are green,
formalized as written, their Lean at every `m` (every `d ≥ 2`), in five commits with the open, the
recon and the close. Next (*Hand-off*): the rest of PD-STEPS goes to the PI.

## Current state

**Closed.** The first sub-phase of PD-STEPS: Phase 40e/40f/40k in `Pᵈ`, the induction's steps at
a cut vertex, along a chain of bridges and at an additive core. File map, one line each:
- `Grade/Cut.lean` (imports `Grade.Witness`, `MainComponent.Cut`):
  `Graph.liftingRestrict_preimage_fst_apply`, `Graph.liftingRestrict_mem_liftingSpaceGrade`,
  `pencilConfigPointGrade_liftingRestrict` and
  `PanelHingeFramework.finrank_span_rigidityRows_ofNormals_liftingRestrict_grade`, with the landed
  `eval_restrictPoly` (`lem:pencil-d-lifting-restrict`); the helper
  `Graph.exists_liftingRestrict_preimage_fst_eq`; `Graph.X0AttainsGrade.of_cutVertex`
  (`thm:pencil-d-cut`) and `Graph.X0AttainsGrade.of_bridgePath` (`thm:pencil-d-bridge`).
- `Grade/ContractAdditive.lean` (imports `Grade.Contract`, `Grade.Cut`, `Grade.Flat`,
  `Induction.SparseDeficiency`): `Graph.finrank_ker_contractLiftingMatrix_zero_eq_and_map_eq`
  (`lem:pencil-contract-additive-kernel`); `contractConfigPolyGrade` and
  `eval_contractConfigPolyGrade`; `Graph.X0AttainsGrade.of_additiveContract`
  (`thm:pencil-d-contract-additive`) and `Graph.X0AttainsGrade.of_rigidContract`
  (`cor:pencil-d-contract-rigid`).

`#print axioms` at the close (`lake lean`, a scratch file) on the ten pinned names:
`[propext, Classical.choice, Quot.sound]`. The close re-read both sections end to end against the
landed statements: every hypothesis and conclusion matches its pin, and the Lean is stronger only
in holding at `d = 2` too (no `1 ≤ m`); no statement changed. Three wordings were repaired. In
`thm:pencil-d-contract-additive`'s proof, the rank of `G/H` at `b′` follows from `z′` attaining,
not from the nonzero hinges (the open's flag). The coverage section's sentence now says the
coverage needs no step *in dimension `d`* at a chain with one or two interior bodies: the `d = 3`
split-off and two-body ear still enter through the embedding, within `thm:pencil-x0-coverage`.
The `-chains` section's sentence of the same claim gained the same three words.

## Architectural choices made up front

- **Scope** (the PI's, verbatim in design doc §1): the six nodes above.
- **The cut** (the PI's, verbatim in design doc §1): `thm:pencil-d-splitoff`,
  `thm:pencil-d-open-ear-deficiency` and `lem:pencil-d-polygon-ear` are deleted with their sections
  `sec:pencil-d-splitoff` and `sec:pencil-d-ear-deficiency` (the text is in git, last at
  `eeb82ae2`). The coverage section keeps one sentence: from `d = 4` on, no step is needed at a
  chain with one or two interior bodies (`thm:pencil-x0-splitoff`, `thm:pencil-x0-open-ear-two`).
- **Encoding** as 42b, 42c and 42e: `m = d − 2` heights at grade `k = m + 1`,
  `D = screwDim (m + 1)`, `def_d` is `G.deficiency (m + 2)` and `def_2` is `G.deficiency 2`.
  Attaining is `Graph.X0AttainsGrade K m`. The restriction of `m` heights to `X` is
  `Graph.liftingRestrict (Prod.fst ⁻¹' X)`, the one-height form at `α × Fin m`.

## Lemma checklist

All six nodes are green, each pinned in its section with its Lean names; the chapter is the
index (forward mode), and the file map is under *Current state*.

## Blockers / open questions

- None. The rest of PD-STEPS opens at the PI's word (*Hand-off*).

## Hand-off / next phase

Phase 42 stays in progress with no sub-phase open. The next step is **putting the rest of
PD-STEPS's open to the PI** (design doc §3): the 19 red nodes of `sec:pencil-d-short` (12, open
ears with three or more interior bodies) and `sec:pencil-d-long` (7, cycles and long open ears),
no letter minted until it opens. What 42f hands it and PD-COVERAGE, all at every `m`:
- The restriction of `m` heights and its three claims (`lem:pencil-d-lifting-restrict`), which
  `thm:pencil-d-open-ear-four` (`-short`) and `thm:pencil-d-open-ear-long` (`-long`) use, with
  `Graph.exists_liftingRestrict_preimage_fst_eq` lifting a restriction height by height.
- `thm:pencil-d-cut`, `thm:pencil-d-bridge`, `thm:pencil-d-contract-additive` and
  `cor:pencil-d-contract-rigid`, the steps `thm:pencil-d-coverage` (PD-COVERAGE) takes at a cut
  vertex, a chain of bridges, a core and a planar-rigid set.

**Deferred from 42f, where it lands** (design doc §3, *Deferred to them from PD-STEPS (42f)*;
FRICTION): `Graph.X0Attains.of_additiveContract` proves inline (`hlow0`, `hup0`, `honto`) what
`Graph.finrank_ker_contractLiftingMatrix_zero_eq_and_map_eq` states. The fold moves that lemma,
unchanged, into `MainComponent/ContractAdditive.lean` (its dependencies are all there; checked by
a scratch copy at the close), with the next commit that edits that file. The deferrals from 42b,
42c and 42e (design doc §3) are unchanged: 42f's Lean is two new files and the root import.

## Decisions made during this phase

- **The open** (the PI, 2026-10-30; verbatim in design doc §1): 42f opens as PD-STEPS's `-cut` and
  `-contract`, six nodes; `-short` and `-long` stay mapped by section, no letter minted.
- **The cut** (the PI, 2026-10-30; verbatim in design doc §1, superseding the PI's 42d "(a) Keep
  standalone", `notes/Phase42d.md`): the `Pᵈ` split-off and the open-ear step that assumes
  `def_d(G[V₁]) ≤ def_d(G)`, with `lem:pencil-d-polygon-ear`, deleted with their sections; PD-STEPS
  goes from 28 nodes to 25.
- **The open's consistency read:** all six proofs route through the argument their statements
  claim, on the `Grade/` carrier; the kernel lemma's lower bound needs only admissibility, so its
  polynomial is `Graph.IsAdmissiblePicture.exists_mvPolynomial`.
- **The pre-build recon** (spikes in `scratch/42f/`, all complete): no tuple restriction defined;
  two new files, so no landed file edited; the kernel lemma kept out of the `d = 3` file (12
  importers); the corollary through `Graph.isX0Graph_induce_of_deficiency_eq_zero (n := 2)`, the
  cut through `Graph.deficiency_add_le_of_cutVertex`.
- **The builds** (two commits, the spikes transcribed, statements unchanged).
- **The close:** three wording repairs (*Current state*); the kernel lemma's docstring states its
  hypotheses exactly; the fold deferred. No `main_results` row: an intermediate close adds none
  (design doc §3, PD-HEAD).
