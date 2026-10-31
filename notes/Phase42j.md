# Phase 42j — PD-COVERAGE: the coverage in every dimension (work log)

**Status:** ✓ closed 2026-10-31 (opened the same day at the PI's word, "All 4 nodes as written
(Recommended)", design doc §1), a sub-phase of Phase 42 that took its layer PD-COVERAGE whole and
completes it; Phase 42 stays in progress with no sub-phase open. Forward mode, the Lean under
`/coordinate-phase`: the four nodes of `blueprint/src/chapter/pencil-d.tex`'s `sec:pencil-d-chains`
and `sec:pencil-d-coverage` are green, as the chapter states them, in six commits with the open,
the recon and the close. Chain-count's route difference waits for the cleanup after Phase 42
(`notes/Cleanup42.md` R-17). Next (*Hand-off*): PD-REDUCTION's open goes to the PI.

## Current state

**Closed.** PD-COVERAGE: the chain count, a long chain or a core, and the coverage in every
dimension with its distinct statement, which put PD-STEPS's eight steps together. File map, one
line each:
- `MainComponent/CoverageChain.lean` (Phase 40's; build 1): the cycle reduction's data,
  `Graph.IsX0Graph.exists_cycle_of_forall_degree_eq_two`; the chain lemmas
  `Graph.IsOpenEar.adj_of_val_eq_succ`, `Graph.IsOpenEar.range_subset_inc`,
  `Graph.IsChain.mem_range_of_adj` and `Graph.IsChain.range_subset_of_mem` (two chains sharing an
  interior body have the same interior bodies).
- `MainComponent/CoverageCut.lean` (build 1): the bridge and cut-vertex data,
  `exists_bridgePath_of_bridgeEar` (was the private `x0Reduces_of_bridgeEar`),
  `Graph.IsX0Graph.exists_bridgePath_of_not_twoEdgeConnected`,
  `Graph.IsX0Graph.exists_cutVertex_of_not_connected`; `Graph.IsOpenEar.isX0Graph_splitOff_succ`,
  of which `_three` and `_four` are the cases `n = 0, 1`.
- `MainComponent/CoverageTheoremS.lean` (build 1): a maximal planar-rigid set's data,
  `Graph.exists_rigidCore_of_deficiency_two_pos`.
- `Grade/Chains.lean` (imports `Grade.TheoremS`; build 2): `Graph.IsChain.partitionDef_induce_le`
  (`lem:pencil-d-chain-count`) and `Graph.IsX0Graph.exists_chain_or_core`
  (`thm:pencil-d-chain-or-core`).
- `Grade/Coverage.lean` (imports `Grade.ShortThree`, `Grade.ContractAdditive`, `Grade.Chains`;
  build 3): `Graph.IsX0Graph.x0AttainsGrade` and `Graph.X0AttainsGrade.of_twoEdgeConnected`
  (`thm:pencil-d-coverage`), `Graph.hasGradedDistinctPencilRealization_of_twoEdgeConnected`
  (`lem:pencil-d-distinct-statement`), with the private `exists_chainBound` (`ℓ`).

Each `d = 3` reduction kept its name and signature, now a short corollary of its data form; the
data forms are unpinned helpers (the coordinator's call at build 1). `#print axioms` at the close
(`lake lean`, a scratch file) on the 5 pinned names and 17 helpers (build 1's 10 new declarations
and the 6 it changed, and `exists_chainBound`, through `Lean.collectAxioms` as it is private):
`[propext, Classical.choice, Quot.sound]` on all 22; no `sorryAx`. The close re-read the four
nodes end to end against the landed statements: no sentence is false, and the Lean is stronger
only where *Decisions made* says.

## Architectural choices made up front

- **Scope** (the PI's, verbatim in design doc §1): the four nodes as the chapter states them; their
  close ends PD-COVERAGE.
- **Encoding** as 42e–42i: `X0AttainsGrade K m` with `m = d − 2` heights, so `d ≥ 3` is `1 ≤ m`;
  the chains at `n = d` with `D = bodyBarDim n` and no field (COUNT-B's). The coverage takes
  `ℓ = 2` at `m = 2` (`d = 4`) and `ℓ = 3` from `m = 3` on; its three-body step is used at `m = 2`
  only.

## Lemma checklist

All four nodes are green, each pinned in its section with its Lean names; the chapter is the
index (forward mode), and the file map is under *Current state*.

## Blockers / open questions

- None. PD-REDUCTION opens at the PI's word (*Hand-off*).

## Hand-off / next phase

Phase 42 stays in progress with no sub-phase open, and PD-COVERAGE is complete (4 nodes, all
green), which completes the induction in every dimension. The next step is **putting
PD-REDUCTION's open to the PI** (design doc §3), no letter minted until it opens: the 8 red nodes
of `pencil-d.tex`'s `sec:pencil-d-reduction`, Phase 39's reduction in `Pᵈ` (from
`lem:pencil-d-two-pencil-extension` to the theorem `thm:pencil-d-realization-theorem`); then
PD-HEAD (21 nodes), at the PI's word. What 42j hands on:
- **The distinct statement** `Graph.hasGradedDistinctPencilRealization_of_twoEdgeConnected`, at
  `1 ≤ m`, which `thm:pencil-d-realization-theorem` uses at the simple 2-edge-connected
  multigraphs; the coverage `Graph.IsX0Graph.x0AttainsGrade`, which `thm:pencil-d-generic`
  (PD-HEAD) uses.
- **The standing rule** (design doc §3): PD-REDUCTION's recon and builds add a row to
  `notes/Cleanup42.md` §2 where their Lean departs from the chapter's proof; R-9 to R-12 and R-14
  to R-17 are open, R-7, R-8 and R-13 aligned.
- **Tier 0 is subsumed** (a fact for Phase 42's close, design doc §3, PD-HEAD): 42c's
  `Graph.x0AttainsGrade_of_deficiency_two_le_three` is `x0AttainsGrade` with `def₂ ≤ 3` added, so
  Tier 0's distinct form also follows from the coverage.

**Deferred, where it lands** (design doc §3; FRICTION's `[open]` entries): the home debts of
42b–42i are unchanged, each with the next commit that edits its target file; none names a file 42j
edited, and 42j adds none. FRICTION's `bodyBarDim` entry gains `exists_chainBound` as its fifth
site, for its `Graph.bodyBarDim_mono` fix. Theorem S's fold, which names
`MainComponent/CoverageTheoremS.lean`, goes to CLEANUP-42 (`notes/Cleanup42.md` §3), as it
reverses an import.

## Decisions made during this phase

- **The close:** the re-read changed no statement and found no false sentence. Chain-count's Lean
  drops `d ≥ 3` and `ℓ ≥ 1`, but only formally: at `ℓ = 0` no chain has at most `ℓ` interior
  bodies, and `ℓ ≥ 1` with `3(ℓ + 1) ≤ D` forces `D ≥ 6`, so `d ≥ 3`. Chain-or-core's drops
  `ℓ ≥ 1` (at `ℓ = 0` its first outcome is any chain). The coverage and the distinct statement
  match their nodes exactly. No `main_results` row (design doc §3, PD-HEAD).
- **Build 1** (the coordinator's call): the data forms stay unpinned; no blueprint edit.
- **The recon's verdicts** (design pass): all four spiked complete. The reductions return their
  data from public forms in `MainComponent/`, the `d = 3` lemmas their corollaries, for one
  rebuild (a copy in `Grade/` would be about 350 lines); the ear steps take a chain's fields;
  `G″`'s standing hypotheses by `Graph.IsX0Graph.splitOff`; the distinct statement is a plain
  theorem, no dimension-`d` `X0Dist`; Theorem S's fold to CLEANUP-42.
- **COUNT-C's route** (R-17): the chains' interior bodies partition the bodies of degree two
  (uniqueness by walking), not edge segments; `T + c ≤ |E(G)|`, `T + ℓ ≤ k + ℓc` and
  `3|V(G)| − T ≤ 2|E(G)|` give it.
- **PI, 2026-10-31 (42j's open):** the PI answered "All 4 nodes as written (Recommended)", whose
  option read: "Close PD-COVERAGE. An Opus open commit, then a pre-build recon that spikes the
  coverage assembly against the landed steps and pins the data-returning reductions, then roughly
  4–7 builds (my estimate). PD-REDUCTION would come next, at your word." The question as put, the
  other options and a note on them: design doc §1.
- **The open's question, checked** (not the PI's text; design doc §1), and its consistency read:
  all four PASS, their 36 outside dependencies green; chain-count's algebra re-derived.
