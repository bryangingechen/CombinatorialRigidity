# Phase 42j — PD-COVERAGE: the coverage in every dimension (work log)

**Status:** in progress, opened 2026-10-31 at the PI's word ("All 4 nodes as written
(Recommended)", design doc §1), a sub-phase of Phase 42 that takes its layer PD-COVERAGE whole.
Forward mode, the Lean under `/coordinate-phase`: the four red nodes of
`blueprint/src/chapter/pencil-d.tex`'s `sec:pencil-d-chains` (`lem:pencil-d-chain-count`, COUNT-C,
and `thm:pencil-d-chain-or-core`) and `sec:pencil-d-coverage` (`thm:pencil-d-coverage`,
`lem:pencil-d-distinct-statement`), on the `Pencil/Grade/` carrier and PD-STEPS's Lean. The open's
consistency read found every proof routing through the argument its statement claims and every
outside dependency green (*Decisions made*); its questions for the recon are under *Blockers*.
Next (*Hand-off*): the pre-build recon of the four nodes.

## Current state

**Next: the pre-build recon** (*Hand-off*). Opened; no Lean yet. The four targets, leaf-first:
`lem:pencil-d-chain-count` rests on Phase 40's chains alone (`def:pencil-x0-chain`,
`lem:pencil-x0-chain-exists`); `thm:pencil-d-chain-or-core` on it, COUNT-B's two cores
(`lem:pencil-d-chain-core`, `lem:pencil-d-core-positive-deficiency`), `lem:deficiency-sparse` and
`lem:deficiency-rigid-higher`; `thm:pencil-d-coverage` on it, the eight steps of PD-STEPS,
PD-CARRIER's `cor:pencil-d-jj-flat`, the embedding (`lem:pencil-d-x0-attains-of-le`) and Phase 40's
coverage with its reductions; `lem:pencil-d-distinct-statement` on the coverage and
`lem:pencil-d-x0-attains-distinct`. Every dependency outside the four is green. The chapter is the
lemma index (forward mode).

## Architectural choices made up front

- **Scope** (the PI's, verbatim in design doc §1): the four nodes as the chapter states them. Their
  close ends PD-COVERAGE; PD-REDUCTION comes next, at the PI's word.
- **Encoding** as 42e–42i: `X0AttainsGrade K m` with `m = d − 2` heights and the deficiency at
  `m + 2`, `D = screwDim (m + 1)`. The coverage takes `ℓ = 2` at `m = 2` (`d = 4`) and `ℓ = 3`
  from `m = 3` on; its three-body step is used at `m = 2` only.
- **What 42i hands on** (`notes/Phase42i.md` *Hand-off*): the three-body step
  `Graph.X0AttainsGrade.of_openEar_three` at `2 ≤ m ≤ 4`, beside 42h's `of_openEar_four` and 42g's
  long ear (`of_openEar`) at every `m`.
- **The standing rule** (design doc §3): the recon and every build add a row to
  `notes/Cleanup42.md` §2 where their Lean departs from the chapter's proof, in the same commit
  (R-9 to R-12 and R-14 to R-16 open; R-7, R-8 and R-13 aligned).

## Lemma checklist

- [ ] **Pre-build recon**: the coverage's assembly spiked on the landed steps, the
  data-returning reductions, exact Lean signatures for the four nodes, their files, and the
  questions under *Blockers*.
- [ ] `lem:pencil-d-chain-count` (COUNT-C), new combinatorics.
- [ ] `thm:pencil-d-chain-or-core`, on the count and COUNT-B's two cores.
- [ ] `thm:pencil-d-coverage`, on chain-or-core, PD-STEPS's steps and the data-returning reductions.
- [ ] `lem:pencil-d-distinct-statement`, on the coverage.
- [ ] **Close** 42j, an intermediate sub-phase close that ends PD-COVERAGE (`PHASE-BOUNDARIES.md`).

## Blockers / open questions

- None blocking the recon. Its questions, from the open's consistency read:
  - **The data-returning reductions.** The coverage's proof reads data out of the *proofs* of
    Phase 40's reductions: the chain of bridges of `lem:pencil-x0-cut-reduces` (1)
    (`Graph.IsX0Graph.x0Reduces_of_not_twoEdgeConnected`, through the private
    `x0Reduces_of_bridgeEar`, `MainComponent/CoverageCut.lean`), the two sides of a cut vertex of
    its part (2) (`x0Reduces_of_not_connected`, same file), the cycle
    (`x0Reduces_of_forall_degree_eq_two`, `MainComponent/CoverageChain.lean`) and a maximal
    planar-rigid set (`x0Reduces_of_deficiency_two_rigid`, `MainComponent/CoverageTheoremS.lean`).
    Each returns only `G.X0Reduces G.X0Below`, whose clauses carry the `d = 3` deficiencies. Pin
    public forms that return the data and the smaller graphs' standing hypotheses, the `d = 3`
    lemmas then their corollaries, or another route. The design doc's "bridge, cut-vertex or cycle
    data" leaves out the fourth: its data is a set `W`, whose properties the coverage's proof
    re-derives inline.
  - **Chain-count (COUNT-C)**, new Lean with no precedent at general `ℓ`: the segments (the chains
    and the edges joining two branch bodies) partition `E(G)`, each body of degree two interior to
    exactly one, and the branch bodies' degrees sum to twice the number of segments. The proof
    needs the chain through a body of degree two unique up to reversal, where
    `Graph.IsX0Graph.exists_isChain` gives existence only; a count that avoids segments (a degree
    sum) is the alternative. At `d = 3` only `ℓ = 1` has Lean,
    `Graph.IsX0Graph.partitionDef_three_induce_diff_nonpos`, under another hypothesis and stated
    `≤ 0`. The bound's form: `(G.induce V₁).partitionDef n id ≤ -(ℓ + 1)`, the singleton value as
    `Graph.IsOpenEar.exists_additiveCoreAt_of_partitionDef_nonpos`'s `hs` reads it; whether the
    Lean keeps `d ≥ 3`, which `ℓ ≥ 1` and `3(ℓ + 1) ≤ D` imply.
  - **Chain-or-core.** Its three-way disjunction in Lean, and the hypotheses COUNT-B's two lemmas
    take: sparsity as `hSv` (from "no planar-rigid set", `Graph.one_le_partitionDef_induce_id`)
    and "no two bodies of degree two adjacent" as `hhubs`.
  - **The coverage's assembly.** Strong induction on `V(G).ncard` at fixed `m`, "smaller" read as
    `sec:pencil-d-induction` defines it (the standing hypotheses and fewer bodies, as
    `Graph.X0Below`); `m = 1` by `Graph.IsX0Graph.x0Attains` and `Graph.x0AttainsGrade_one_iff`.
    Chain-or-core yields a `Graph.IsChain`, while the three ear steps take the ear unpacked
    (`hcover`, `hinj`, `hxV₁`, `hpath`, `hsep`), `of_openEar_four` at `x : Fin (n + 4)` and
    `of_openEar` at `screwDim (m + 1) − 1 ≤ k`: the glue, and `G″`'s standing hypotheses
    (`Graph.IsX0Graph.splitOff`).
  - **The distinct statement.** At `d = 3` its Lean is one line (`x0Dist`, for the predicate
    `X0Dist`); no such predicate exists in dimension `d`. Its form, as PD-REDUCTION's
    `thm:pencil-d-realization-theorem` will consume it.
  - **Theorem S's fold** (optional, design doc §3). `thm:pencil-d-theorem-s` has no consumer among
    the four: the coverage reaches its cores through chain-or-core. `Grade/TheoremS.lean` imports
    `MainComponent/CoverageTheoremS.lean`, so making `Graph.IsX0Graph.exists_additiveCore` its
    `n = 3` case reverses that import. Fold it here or leave it to CLEANUP-42.
  - **Files.** New `Grade/` file(s), at the recon's choice. An edit to a `MainComponent/` file
    rebuilds its importers, and carries any deferral that names that file (design doc §3).

## Hand-off / next phase

The next concrete commit is the **pre-build recon** (a `recon-opus` dispatch, read-only or a
design-pass commit at the coordinator's choice), as `fe5baf0f` (42h) and `3ab48a47` (42i) were. It
spikes the coverage's assembly against the landed PD-STEPS Lean (`Pencil/Grade/`: `Cut.lean`,
`ContractAdditive.lean`, `Chain.lean`, `Short.lean`, `ShortThree.lean`, with `Flat.lean`,
`ZeroHeights.lean` and `TheoremS.lean`) and Phase 40's coverage (`MainComponent/Coverage.lean`,
`CoverageChain.lean`, `CoverageCut.lean`, `CoverageTheoremS.lean`; `thm:pencil-x0-coverage` pins
`Graph.IsX0Graph.x0Reduces`, `Graph.IsX0Graph.x0Attains`, `Graph.X0Attains.of_twoEdgeConnected`). It
pins the four nodes' Lean signatures, the data-returning reductions and the file plan, each spiked
under `lake lean`, settles *Blockers*, and records the signatures here. Then build leaf-first,
roughly 4–7 commits by the coordinator's estimate in the option the PI chose. Each build adds its
node's `\lean{}` and `\leanok`.
- **The standing rule** (*Architectural choices*): a row in `notes/Cleanup42.md` §2 per departure.
- **Deferred, where it lands** (design doc §3; FRICTION's `[open]` entries): the home debts of
  42b–42i are unchanged, each riding with the next commit that edits its target file
  (`notes/Phase42i.md` *Hand-off* lists 42i's).
- **After 42j:** PD-REDUCTION (`-reduction`, 8 red nodes) and PD-HEAD (21) open at the PI's word
  (design doc §3).

## Decisions made during this phase

- **PI, 2026-10-31 (42j's open):** the PI answered "All 4 nodes as written (Recommended)", whose
  option read: "Close PD-COVERAGE. An Opus open commit, then a pre-build recon that spikes the
  coverage assembly against the landed steps and pins the data-returning reductions, then roughly
  4–7 builds (my estimate). PD-REDUCTION would come next, at your word." The question as put, the
  other options and a note on them: design doc §1.
- **The open's question, checked** (not the PI's text; design doc §1): only chain-count counts,
  chain-or-core applying its bound; the coverage uses all eight of PD-STEPS's steps, and more; the
  distinct statement is two citations, its `d = 3` Lean one line; the planar-rigid reduction
  returns a set, not a bridge, cut vertex or cycle.
- **Consistency read at the open:** all four PASS. Each was read in full against the nodes it
  cites: every proof routes through the argument its statement claims, and no wording needs a
  repair. With every `\uses` list parsed whole, the 36 dependencies outside the four (8
  definitions, 18 lemmas, 8 theorems, 2 corollaries) are green, proofs too, none superseded, and
  every `\cref` in the four resolves to a live node. Each of the four uses the one before it;
  outside them `thm:pencil-d-generic` (PD-HEAD) uses the coverage and
  `thm:pencil-d-realization-theorem` (PD-REDUCTION) the distinct statement.
- **The read's checks:** the coverage's induction reads "smaller" as `sec:pencil-d-induction`
  defines it, and each step it calls gets its stated hypotheses (`G″` by
  `lem:pencil-x0-chain-standing` (2), a core and its contraction by the two contract-standing
  lemmas). Chain-count's algebra, re-derived: `|V₁| − 1 = |B| − e + Σ_{j≠i} L_j` and
  `e(V₁) = Σ_{j≠i} L_j`, so `s_D(V₁) = Σ_{j≠i} L_j − D(e − |B|) ≤ (ℓ+1)(e−1) − De/3 ≤ −(ℓ+1)`,
  by `3|B| ≤ 2e` and `3(ℓ+1) ≤ D`. Chain-or-core splits at `k ≥ 2`, `lem:pencil-d-chain-core`'s.
  From `sec:pencil-d-induction` on, 62 nodes, 33 red (recounted).
