# Phase 42j — PD-COVERAGE: the coverage in every dimension (work log)

**Status:** in progress, opened 2026-10-31 at the PI's word ("All 4 nodes as written
(Recommended)", design doc §1), a sub-phase of Phase 42 that takes its layer PD-COVERAGE whole.
Forward mode, the Lean under `/coordinate-phase`: the four red nodes of
`blueprint/src/chapter/pencil-d.tex`'s `sec:pencil-d-chains` (`lem:pencil-d-chain-count`, COUNT-C,
and `thm:pencil-d-chain-or-core`) and `sec:pencil-d-coverage` (`thm:pencil-d-coverage`,
`lem:pencil-d-distinct-statement`), on the `Pencil/Grade/` carrier and PD-STEPS's Lean. The
pre-build recon spiked all four complete, with no `sorry`, and pinned three builds (*Hand-off*).
Next: build 1, the reductions that return their data.

## Current state

**Next: build 1, the data-returning reductions** (*Hand-off*). No Lean has landed yet. The
pre-build recon (design pass, 2026-10-31) spiked the whole layer on the landed carrier, with no
`sorry`: `scratch/42j/All.lean` (gitignored; `lake lean` clean, no warning, the three standard
axioms, the `unusedArguments` and `docBlame` lints clean) is the concatenation of three spikes, each
the transplant of the builds below:
- `scratch/42j/Reductions.lean`, **complete**: the four data-returning reductions, each `d = 3`
  reduction re-proved as a two-line corollary of its data form (build 1).
- `scratch/42j/Chains.lean`, **complete**: COUNT-C and chain-or-core, with the four chain lemmas
  that build 1 lands in `MainComponent/CoverageChain.lean` (build 2).
- `scratch/42j/Coverage.lean`, **complete but for its five inputs**, `sorry`'d there with the
  exact signatures that the other two spikes prove (and `All.lean` checks together): the
  coverage, its last claim and the distinct statement, with the splitting-off lemma that build 1
  lands (build 3).

The chapter is the lemma index (forward mode). The pinned signatures, the files and the build order
are under *Hand-off*; the recon's verdicts under *Decisions made*.

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
  (R-9 to R-12 and R-14 to R-17 open; R-7, R-8 and R-13 aligned; R-17 is 42j's recon's).

## Lemma checklist

- [x] **Pre-build recon** (design pass): all four nodes spiked complete; *Decisions made*.
- [ ] **Build 1**, the data-returning reductions and the chain lemmas, in `MainComponent/` (no red
  node; serves builds 2 and 3).
- [ ] `lem:pencil-d-chain-count` (COUNT-C), build 2, `Grade/Chains.lean`.
- [ ] `thm:pencil-d-chain-or-core`, build 2, same file.
- [ ] `thm:pencil-d-coverage`, build 3, `Grade/Coverage.lean`.
- [ ] `lem:pencil-d-distinct-statement`, build 3, same file.
- [ ] **Close** 42j, an intermediate sub-phase close that ends PD-COVERAGE (`PHASE-BOUNDARIES.md`).

## Blockers / open questions

- None. The open's seven questions for the recon are settled (*Decisions made*, *The recon's
  verdicts*); no node's statement is false against the carrier, and no choice waits on the PI.

## Hand-off / next phase

Three builds, one commit each, then the close. Every declaration they land is spiked complete
(`All.lean`), so each build transplants its spike (the coordinator may resume the recon to land
them). The encoding: the chains at `n = d`
with `D = bodyBarDim n` and no field (COUNT-B's), the coverage at `m = d − 2` with `n = m + 2`.
- **Build 1** (no red node): the data-returning reductions, each `d = 3` lemma kept as a two-line
  corollary of its data form, and the four chain lemmas build 2 calls. Edits three files:
  - `MainComponent/CoverageChain.lean`: `Graph.IsX0Graph.exists_cycle_of_forall_degree_eq_two`
    (the body of `x0Reduces_of_forall_degree_eq_two`, returning the `cycle` clause's fields);
    `Graph.IsOpenEar.adj_of_val_eq_succ`, `Graph.IsOpenEar.range_subset_inc`,
    `Graph.IsChain.mem_range_of_adj` and `Graph.IsChain.range_subset_of_mem` (two chains sharing an
    interior body have the same interior bodies).
  - `MainComponent/CoverageCut.lean`: the private `x0Reduces_of_bridgeEar` becomes
    `exists_bridgePath_of_bridgeEar` (same induction);
    `Graph.IsX0Graph.exists_bridgePath_of_not_twoEdgeConnected` and
    `Graph.IsX0Graph.exists_cutVertex_of_not_connected` return the `bridgePath` and `cutVertex`
    clauses' fields with `G.X0Below` at both sides; `Graph.IsOpenEar.isX0Graph_splitOff_succ` at
    `x : Fin (n + 3)`, of which `isX0Graph_splitOff_three` and `_four` may become one-line cases.
  - `MainComponent/CoverageTheoremS.lean`: `Graph.exists_rigidCore_of_deficiency_two_pos` (a
    maximal planar-rigid `W ⊇ Y`, proper, `r ∈ W`, `hatt`; no `hG`).
  It rebuilds `CoverageChain.lean` and its 9 downstream modules (`CoverageCut`, `CoverageTheoremS`,
  `GenericBase`, `GoodEar`, `Statements`, `Grade/Stable`, `Grade/TheoremS`, `Nonvacuity`, the
  root). No design doc §3 deferral names these files. The data forms may join the `\lean{}` pins
  of `lem:pencil-x0-cut-reduces`, `-cycle-reduces` and `-planar-rigid-reduces`
  (`main-component.tex`) with a clause naming the data, the additive-successor gate's way.
- **Build 2**, new `Grade/Chains.lean` (imports `Grade/TheoremS.lean`), both nodes of `-chains`:
  - `lem:pencil-d-chain-count`: `Graph.IsChain.partitionDef_induce_le (hG : G.IsX0Graph) (h2c)
    (hhub) (hℓ : 3 * (ℓ + 1) ≤ Graph.bodyBarDim n) (hshort : ∀ V₁ k x a b e, G.IsChain V₁ x a b e
    → k ≤ ℓ) (hC : G.IsChain V₁ x a b e) : (G.induce V₁).partitionDef n id ≤ -((ℓ : ℤ) + 1)`.
    It takes neither `d ≥ 3` nor `ℓ ≥ 1`: the proof uses neither, and `unusedArguments` rejects
    them.
  - `thm:pencil-d-chain-or-core`: `Graph.IsX0Graph.exists_chain_or_core (hG) (h2c) (hhub) (hS : ∀ X
    ⊆ V(G), 2 ≤ X.ncard → (G.induce X).deficiency 2 ≠ 0) (hn : 3 ≤ n) (hℓ)`, concluding
    `(∃ V₁ k x a b e, G.IsChain V₁ x a b e ∧ ℓ < k) ∨ (∃ W, ∃ r ∈ W, …)` (the core at `n`, as
    `exists_core_of_deficiency_three_pos` returns it) `∨ ((∀ V₁ k x a b e, G.IsChain V₁ x a b e →
    k = 1) ∧ G.deficiency 3 = 0 ∧ G.deficiency n = 0)`. No `ℓ ≥ 1`; `hSv` is
    `Graph.one_le_partitionDef_induce_id hS`, `hhubs` comes from `exists_isChain` and
    `IsChain.two_le_of_adj`.
- **Build 3**, new `Grade/Coverage.lean` (imports `Grade/ShortThree.lean`,
  `Grade/ContractAdditive.lean`, `Grade/Chains.lean`), both nodes of `-coverage`:
  - `thm:pencil-d-coverage`: `Graph.IsX0Graph.x0AttainsGrade [Infinite K] (hG : G.IsX0Graph)
    (hm : 1 ≤ m) : G.X0AttainsGrade K m` and, for the last claim,
    `Graph.X0AttainsGrade.of_twoEdgeConnected (hS : G.Simple) (hV : 3 ≤ V(G).ncard) (htec) (hm)`.
    `m = 1` by `x0AttainsGrade_one_iff` and `x0Attains`; otherwise strong induction on
    `V(G).ncard` with the chapter's cases in its order; a private `exists_chainBound` gives `ℓ`.
  - `lem:pencil-d-distinct-statement`: `Graph.hasGradedDistinctPencilRealization_of_twoEdgeConnected
    (hS) (hV) (htec) (hm) : HasGradedDistinctPencilRealization K (m + 1) (m + 2) G`, one line.
- **Then the close** (`PHASE-BOUNDARIES.md`), an intermediate one that ends PD-COVERAGE.
- **The standing rule** (*Architectural choices*): R-17 (chain-count's route) is open in
  `notes/Cleanup42.md` §2; builds 1 and 3 depart from no chapter proof.
- **Deferred, where it lands** (design doc §3; FRICTION's `[open]` entries): the home debts of
  42b–42i are unchanged, each riding with the next commit that edits its target file
  (`notes/Phase42i.md` *Hand-off* lists 42i's); none names a file these builds edit. Theorem S's
  fold goes to CLEANUP-42 (`notes/Cleanup42.md` §3).
- **After 42j:** PD-REDUCTION (`-reduction`, 8 red nodes) and PD-HEAD (21) open at the PI's word
  (design doc §3).

## Decisions made during this phase

- **The recon's verdicts** (design pass, 2026-10-31): all four nodes spiked complete (*Current
  state*). The reductions: public data forms in `MainComponent/`, the `d = 3` lemmas their
  corollaries, for one rebuild; re-deriving them in `Grade/` would copy about 350 lines.
  The ear steps take what a chain gives, field by field; `G″`'s standing hypotheses by
  `Graph.IsX0Graph.splitOff`; no ear step takes a deficiency, so chain-or-core suffices. The
  distinct statement: a plain theorem, no dimension-`d` `X0Dist`, as the realization theorem uses
  it at one graph. Theorem S's fold: CLEANUP-42 (it reverses an import; no node here uses it).
- **COUNT-C's route** (R-17): the interior bodies of the chains partition the bodies of degree two
  (uniqueness by walking), not edge segments; no degree sum alone can count them (the bound `ℓ` is
  per chain). `T + c ≤ |E(G)|`, `T + ℓ ≤ k + ℓc` and the landed `3|V(G)| − T ≤ 2|E(G)|` give it.
- **The open's four unchecked claims, against the Lean:** all hold. The ear steps take the ear
  unpacked; `of_openEar_four` takes `x : Fin (n + 4)` (a chain with `4 ≤ k` is reindexed by
  `k = n + 4`); COUNT-C needs uniqueness, of the interior bodies only; and `Grade/TheoremS.lean`
  imports `MainComponent/CoverageTheoremS.lean`.
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
