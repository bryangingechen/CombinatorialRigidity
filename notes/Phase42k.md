# Phase 42k — PD-REDUCTION: Phase 39's reduction in every dimension (work log)

**Status:** ✓ closed 2026-11-04 (opened the same day at the PI's word, "All 8 nodes as written
(Recommended)", design doc §1), a sub-phase of Phase 42 that took its layer PD-REDUCTION whole and
completes it; Phase 42 stays in progress with no sub-phase open. Forward mode, the Lean under
`/coordinate-phase`: the eight nodes of `blueprint/src/chapter/pencil-d.tex`'s
`sec:pencil-d-reduction` are green, as the chapter states them, in six commits with the open, the
recon and the close. Two cases' route differences wait for the cleanup after Phase 42
(`notes/Cleanup42.md` R-18, R-19). Next (*Hand-off*): PD-HEAD's open goes to the PI.

## Current state

**Closed.** PD-REDUCTION: Phase 39's reduction in every dimension, from a hinge in two pencils to
the realization theorem. File map, one line each (namespace `CombinatorialRigidity.Molecular`,
the theorem in `Graph`):
- `Grade/TwoPencil.lean` (imports `Grade.Realization`; build 1): `perpExtensor` (`C_B`) with
  `exists_extensor_eq_perpExtensor`, and `perpExtensor_two_pencils` (part (1)),
  `exists_eq_smul_perpExtensor` and `exists_extensor_two_pencils_iff_grade` (2),
  `linearIndependent_perpExtensor_pair` (3) (`lem:pencil-d-two-pencil-extension`);
  `hasPencilPlaneRealization_mapExtensor_screwEquivOfLinearEquiv`
  (`lem:pencil-d-projective-transport`); `exists_reposition_planes` (`lem:pencil-d-cut-reposition`);
  helpers `finrank_span_pair_eq_two`, `exists_mem_linearIndependent_pair`, `ExtensorInPanel.smul`,
  `exists_smul_extensor_eq_of_mem_span_range_grade`, `exists_two_planes_of_mem`, `dotPerp_map_eq`.
- `Grade/Arms.lean` (imports `Grade.TwoPencil`; build 2): `hasGradedPencilRealization_of_isLoopAt`
  (`lem:pencil-d-loop-case`); `hasGradedPencilRealization_of_ncard_le_two` and its distinct form
  (`lem:pencil-d-base-case`); `hasGradedPencilRealization_of_cutEdges` and its distinct form
  (`lem:pencil-d-cut-case`), from the glue `exists_hasPencilPlaneRealization_glue` and the core
  `exists_hasPencilPlaneRealization_of_cutEdges`; helpers `exists_plane_single_zero_one`,
  `finrank_span_rigidityRows_of_single_edge`, `exists_pair_of_ncard_le_two_of_edgeSet_nonempty`.
- `Grade/Reduction.lean` (imports `Grade.Arms`, `Grade.Coverage`; build 3):
  `hasGradedPencilRealization_of_not_simple` (`lem:pencil-d-nonsimple-case`) and
  `Graph.graded_pencil_realization_theorem` (`thm:pencil-d-realization-theorem`), by
  `Graph.pencil_reduction` at `n = m + 2`.

`#print axioms` at the close (`lake lean`, a scratch file) on the 15 pinned names and the 11
helpers: `[propext, Classical.choice, Quot.sound]` on all 26; no `sorryAx`. The close re-read the
eight nodes end to end against the landed statements: no sentence is false, and the Lean is
stronger only where *Decisions made* says. Its proofs are the chapter's except two: the base and
nonsimple cases count rows where the chapter counts motions (R-18, R-19, open for the cleanup).

## Architectural choices made up front

- **Scope** (the PI's, verbatim in design doc §1): the eight nodes as the chapter states them; their
  close ends PD-REDUCTION.
- **Encoding** as 42b–42j: grade `k = d − 1`, the targets `HasGradedPencilRealization K (m + 1)
  (m + 2)` and its distinct form at `m = d − 2`, so `d ≥ 3` is `1 ≤ m`, the deficiency at
  `n = m + 2`, the form of 42j's distinct statement.

## Lemma checklist

All eight nodes are green, each pinned in its section with its Lean names; the chapter is the
index (forward mode), and the file map is under *Current state*.

## Blockers / open questions

- None. PD-HEAD opens at the PI's word (*Hand-off*).

## Hand-off / next phase

Phase 42 stays in progress with no sub-phase open, and PD-REDUCTION is complete (8 nodes, all
green), which gives the headline's first two conjuncts at every `d ≥ 3`. The next step is
**putting PD-HEAD's open to the PI** (design doc §3), no letter minted until it opens (answered at
42l's open: `-nondegenerate` and `-lift` only, design doc §1; `notes/Phase42l.md`): the 21 red
nodes of `pencil-d.tex`'s `sec:pencil-d-nondegenerate` (4), `sec:pencil-d-lift` (6) and
`sec:pencil-d-generic` (11), the generic conjunct and the headline `cor:pencil-d-conditioned-pair`
(the first red node is `def:pencil-d-nondegenerate`). PD-HEAD is the last layer, so its close is
Phase 42's, where Tier 0's `main_results` row is decided (design doc §3). What 42k hands on:
- **The theorem** `Graph.graded_pencil_realization_theorem`, at `1 ≤ m`, whose two conjuncts are
  the first two claims of `cor:pencil-d-conditioned-pair`.
- **The standing rule** (design doc §3): PD-HEAD's recon and builds add a row to
  `notes/Cleanup42.md` §2 where their Lean departs from the chapter's proof. Open: R-3 to R-5, R-9
  to R-12, R-14 to R-19; aligned: R-1, R-2, R-7, R-8, R-13; R-6 no departure. CLEANUP-42 also
  takes the fold of the `d = 3` cases into 42k's graded ones (its §3).

**Deferred, where it lands** (design doc §3, *Deferred to PD-HEAD and after from PD-REDUCTION*;
FRICTION's `[open]` 42k entries): no build edited a file that carries a home debt of 42b–42j, so
none rode. 42k's own, each with the next commit that edits its file:
`exists_smul_extensor_eq_of_mem_span_range_grade` to `Meet.lean` (with `contragredientEquiv`),
`ExtensorInPanel.smul` to `RigidityMatrix/Basic.lean`, `dotPerp_map_eq` to
`Grade/Realization.lean`, `finrank_span_rigidityRows_of_single_edge` to `GenericityDevice.lean`
(with `ArmsAssembly.lean`'s inline count); at a cleanup round, the mirror candidates
`finrank_span_pair_eq_two`, `exists_mem_linearIndependent_pair` and
`exists_pair_of_ncard_le_two_of_edgeSet_nonempty`.

## Decisions made during this phase

- **The close:** the re-read changed no statement and found no false sentence. The linear algebra
  holds at every grade without the nodes' nonzero and dimension hypotheses (part (2)'s criterion
  takes `b_u ≠ 0`, part (3) `k ≥ 1`); the transport keeps every independent pair, not only the
  links; the loop holds at every grade and `n`, the cases at every `m`; the cut case takes the cut
  `V₁`, which "not two-edge-connected" supplies; the nonsimple case's hypothesis is over graphs on
  the same types. Only the theorem takes `1 ≤ m`. No `main_results` row (design doc §3, PD-HEAD).
- **The recon's verdicts** (design pass): all eight spiked complete, transcribed from the `d = 3`
  Lean to grade `k` with subspaces for points (the transport with `g` and `h` exchanged); new are
  `C_B` with the two-pencil lemma, and the base case's adjacent-distinct form (`b_u = e₀`,
  `b_v = e₁`). The theorem is `Graph.pencil_reduction` at `n = m + 2` for the conjunction, its
  `hcut`, `hcontract` and `hsplit` one function, as in `pencilPair_of_X0`.
- **The routes** (R-18, R-19): the base case's one-edge rank and `m ≥ 2` deficiency, and the
  nonsimple case's rank by the splice with the other parallel edges keeping their hinges in `G/H`,
  count rows as the `d = 3` Lean does, where the chapter counts motions. Every other proof is the
  chapter's.
- **PI, 2026-11-04 (42k's open):** the PI answered "All 8 nodes as written (Recommended)", whose
  option read: "Close PD-REDUCTION. An Opus open commit, then a pre-build recon that spikes the
  cases against Phase 39's d = 3 Lean and the landed carrier, then roughly 4–8 builds (my
  estimate). PD-HEAD (21 nodes) would come next, at your word." The question as put, the other
  options and a note on them: design doc §1.
- **The open's question, checked** (not the PI's text; design doc §1), and its consistency read:
  all eight PASS, their 23 outside dependencies green; the cases' counts re-derived.
