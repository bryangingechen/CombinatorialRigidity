# Phase 42g — PD-STEPS: cycles and long open ears in every dimension (work log)

**Status:** ✓ closed 2026-10-31 (opened 2026-10-30 at the PI's word, "-long first (Recommended)",
design doc §1), a sub-phase of Phase 42, which stays in progress with no sub-phase open. Forward
mode, the Lean under `/coordinate-phase`: the seven nodes of `blueprint/src/chapter/pencil-d.tex`
in `sec:pencil-d-long` are green, their Lean at every `m` (every `d ≥ 2`), in six commits with the
open, the recon and the close. At the PI's word two chapter proofs follow their Lean; the other
route differences wait for the cleanup after Phase 42 (`notes/Cleanup42.md`). Next (*Hand-off*):
`-short`'s open goes to the PI.

## Current state

**Closed.** The second sub-phase of PD-STEPS: Phase 40's cycle and long-ear steps in `Pᵈ`, on
CERT's closed polygons with independent joins. File map, one line each:
- `Grade/Polygon.lean` (imports `Grade.Embedding`, `Grade.Carrier`, the mirror below):
  `linearIndependent_polygon_vertices` and `exists_linearEquiv_polygon_normal`
  (`lem:pencil-d-polygon-normal`), `exists_normalsJoin_notMem_span_polygon` (`-polygon-star`),
  `exists_insertNth_linearIndependent_join` (`-polygon-insert`),
  `exists_polygon_linearIndependent_join` (`lem:pencil-d-polygons`), and `polygonCollapse`,
  `polygonCollapseEdge` with five lemmas (`-polygon-collapse`, index level); helpers
  `normalsJoin_add_right`, `normalsJoin_smul_right`, `normalsJoin_zero_left`,
  `exists_linearMap_normalsJoin_eq`, `linearIndependent_join_triangle`,
  `eq_of_add_smul_mem_of_add_smul_mem`.
- `Grade/Chain.lean` (imports `Grade.Polygon`, `Grade.Cut`, `Grade.JoinIndependence`,
  `MainComponent.Chain`): `Graph.X0AttainsGrade.of_cycle` and `…of_cycle_of_certificate`
  (`thm:pencil-d-cycle`), `Graph.X0AttainsGrade.of_openEar` and `…of_openEar_of_cert`
  (`thm:pencil-d-open-ear-long`); helpers `card_le_finrank_of_linearIndependent_normalsJoin` (the
  hinge form, every `k`: PD-STATE's deferral discharged), `three_le_screwDim_succ`,
  `pencilConfigPointGrade_ofPoints`.
- `Mathlib/Data/Fin/Basic.lean` (new mirror): the five `Fin` index lemmas of the insertion.

`#print axioms` at the close (`lake lean`, a scratch file) on the sixteen pinned names and six
helpers: `[propext, Classical.choice, Quot.sound]`, or part of it (the index-level collapse and
`pencilConfigPointGrade_ofPoints`). The close re-read the section end to end against the landed
statements: every hypothesis and conclusion matches its pin, and the Lean is stronger only in
dropping the nodes' `d ≥ 3`; no statement changed, and no wording needed a repair. The star's and
the insertion's proofs, rewritten in 42g, follow their Lean step for step.

## Architectural choices made up front

- **Scope** (the PI's, verbatim in design doc §1): the seven nodes above.
- **Encoding** as 42b–42f: `m = d − 2` heights at grade `k = m + 1`, `D = screwDim (m + 1)`
  (`= Graph.bodyBarDim (m + 2)`), `def_d` is `G.deficiency (m + 2)`. Attaining is
  `Graph.X0AttainsGrade K m`. A closed `n`-gon is `Y : Fin n → Fin (k + 2) → K` with `[NeZero n]`,
  indices cyclic in `Fin n`, with no definition; `P₀`, `P₁`, `P₂` are `gradeMk 0 0 0 1`,
  `gradeMk 1 0 0 1`, `gradeMk 0 1 0 1`, and a vector with last coordinate `1` is a configuration
  point (`gradeMk_eta`).

## Lemma checklist

All seven nodes are green, each pinned in its section with its Lean names; the chapter is the
index (forward mode), and the file map is under *Current state*.

## Blockers / open questions

- None. `-short` opens at the PI's word (*Hand-off*).

## Hand-off / next phase

Phase 42 stays in progress with no sub-phase open. The next step is **putting `-short`'s open to
the PI** (design doc §3): the 12 red nodes of `sec:pencil-d-short`, open ears with three or more
interior bodies (SHORT-CORE's step, the ear data and the three-body case at `d = 4` to `6`), the
last of PD-STEPS, no letter minted until it opens. What 42g hands it and PD-COVERAGE, at every `m`:
- `thm:pencil-d-cycle` and `thm:pencil-d-open-ear-long`, the steps `thm:pencil-d-coverage` takes
  at a cycle and at an open ear with `k ≥ D − 1`; their certificate lemmas take any edges with
  independent joins at any picture and heights.
- The join algebra: `eq_of_add_smul_mem_of_add_smul_mem` and the `normalsJoin` lemmas, which
  `-short`'s `lem:pencil-d-insertion` can share (a dimension gain at `[Infinite K]`, a different
  statement from `-polygon-insert`), and `pencilConfigPointGrade_ofPoints` for any placement.
- The standing rule (design doc §3): `-short`'s recon and builds add a row to
  `notes/Cleanup42.md` §2 wherever their Lean departs from the chapter's proof.

**Deferred from 42g, where it lands** (design doc §3; two `[open]` FRICTION entries): the four
`normalsJoin` lemmas of `Grade/Polygon.lean` join 42c's move to `PanelLayer.lean`, and
`pencilConfigPointGrade_ofPoints` joins 42e's fold into `Grade/Carrier.lean`, each with the next
commit that edits that file. The other deferrals of 42b, 42c, 42e and 42f are unchanged: 42g's Lean
is three new files and the root import list. The ledger's open rows R-3 to R-5 belong to the
post-Phase-42 cleanup; R-6 is no departure.

## Decisions made during this phase

- **The open** (the PI, 2026-10-30; verbatim in design doc §1): 42g opens as PD-STEPS's `-long`,
  seven nodes; `-short` stays mapped by section, no letter minted.
- **Consistency read at the open:** all seven proofs route through the argument their statements
  claim, on the `Grade/` carrier; with every `\uses` list parsed whole, no `-long` node uses a
  `-short` one or the reverse, and `-long`'s four pointers to `sec:pencil-d-short` are notation; no
  chapter edit.
- **The pre-build recon** (spikes in `scratch/42g/`, all complete): the polygon carrier above, with
  no basis of `⋀²` (2 × 2-minor functionals, `exteriorPower.ιMulti_span`); `|K| ≥ 4` kept as
  `4 ≤ ENat.card K`, derived from `[Infinite K]` in the cycle and the ear; the collapse at index
  level; two new files, no landed file edited, no deferral triggered.
- **The star and the insertion follow the Lean** (the PI, 2026-10-30; verbatim in design doc §1 and
  `notes/Cleanup42.md` §1): their chapter proofs were rewritten to the Lean's routes, statements
  unchanged; the star's proof `\uses` `def:extensor`, not `lem:pencil-d-polygon-normal`. The other
  three route differences stay as written for the post-Phase-42 cleanup, in that note's ledger,
  which every later recon or build extends (design doc §3).
- **The builds** (two commits, the spikes transcribed, statements unchanged): the `Fin` lemmas in
  the mirror; the hinge form without a `P³` file importing `Grade/`; the placement any
  `pt : α → V` with last coordinate `1`. The cycle's placement is ledger row R-5.
- **The close:** no wording repair; R-6, the cycle's heights restricted to `V(G)`, is no departure,
  a carrier encoding (`notes/Cleanup42.md` §2); the two home debts filed in FRICTION. No
  `main_results` row: an intermediate close adds none (design doc §3, PD-HEAD).
