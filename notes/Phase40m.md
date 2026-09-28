# Phase 40m — PENCIL-X0 / COVERAGE-CHAINS + THEOREM-S: chains, cuts, Theorem S and the covering theorem (work log)

**Status:** ✓ complete (opened design-first, built and closed 2026-09-28). COVERAGE's second and
last sub-phase: **CHAINS** (the maximal ear through bodies of degree two, chains, the cycle, and the
cut-vertex and bridge reductions, with (H) at every smaller graph) with **THEOREM-S** (Theorem S and
the covering theorem) folded in, by the PI's call (2026-09-28, `notes/pencil/adjudications.md`;
plan `notes/Phase40-design.md` §3 COVERAGE). Its close also closes COVERAGE: the general
configuration attains at every graph satisfying (H). **Next: MOTIVES** (`X0Dist` and `X0Gen`),
which closes Phase 40 — see *Hand-off*.

## Current state

**Closed, and with it COVERAGE.** Five build commits (B1 `059fbd25`, B2 `13a3d4e1`, B3 `8858f01d`,
B4 `a394309a`, B5 `36e66c7a`), two coordinator fixups (`61d97b06`, `eb085494`) and the close
landed. All eleven CHAINS+THEOREM-S nodes of `main-component.tex` §`sec:main-component-coverage`
are green: CHAINS' `def:pencil-x0-chain`, `lem:pencil-x0-chain-exists`,
`lem:pencil-x0-chain-standing`, `lem:pencil-x0-cycle-reduces`, `lem:pencil-x0-cut-reduces`, and
THEOREM-S' `def:pencil-x0-usable-chain`, `lem:pencil-x0-chain-reduces`,
`lem:pencil-x0-planar-rigid-reduces`, `lem:pencil-x0-sparse-count`, `thm:pencil-x0-theorem-s`,
`thm:pencil-x0-coverage`. With 40l's two, the whole subsection is green. The chapter's one red
node is `thm:pencil-x0-generic-attains` (`sec:main-component-statements`), for MOTIVES.

The Lean is three leaf modules in `Molecule/Pencil/MainComponent/`, each in the root import after
`…MainComponent.Coverage`, each module docstring listing its statements: `CoverageChain.lean` (708
lines; imports `Coverage`), `CoverageCut.lean` (640; imports `CoverageChain`; its five BRIDGE
helpers `private`), `CoverageTheoremS.lean` (580; imports `CoverageCut` and
`Induction/SparseDeficiency`). Each build is a verbatim transcription of the spikes over the
checklist's ranges, plus docstrings and the listed warning fixes (the coordinator diffed every
landed file against the concatenated ranges); after each, a `touch` + `lake build` of the touched
module was warning-free and `lake lint` passed. **MOTIVES' interface:** `Graph.IsX0Graph.x0Attains`
(every (H)-graph attains, `[Infinite K]`) and `Graph.X0Attains.of_twoEdgeConnected` (the consumer's
form: `G.Simple`, `3 ≤ V(G).ncard`, `G.TwoEdgeConnected`).

**Headline axioms, re-verified at the close** on 34 declarations: the eighteen
`formalization.yaml` main results and the sixteen 40m pins. All 34 are exactly
`[propext, Classical.choice, Quot.sound]` (the structure `Graph.IsChain` and the definition
`Graph.ChainUsable` included); none uses `sorryAx`. *Measured, script not retained*: one
`#print axioms` line per declaration under `import CombinatorialRigidity`, run with `lake lean` on
the fully built tree (a full `lake build` first, after the close's docstring edits: 2 992 jobs, 0
warnings, 0 errors, 0 cache-write failures).

**The spikes** (gitignored `scratch/40m/`, with `scratch/40l/`): consumed. No later sub-phase reads
them; MOTIVES calls the landed interface.

## Architectural choices made up front

- **The route** (the recon's verdict; design doc §3 COVERAGE items 2–3): one core, the maximal ear
  `Graph.IsOpenEar.exists_maximal`, serves chain extraction and the cycle, and BRIDGE runs the same
  extension on a bridge ear with its two sides tracked; the cut arguments go through one gate,
  `Graph.Connected.induce_of_gate`; THEOREM-S is S5's text.
- **Layout:** the three new leaf modules above, named with the `Coverage` prefix (*Decisions*).

## Lemma checklist

All landed with the standard axioms (*Current state*); pins in **bold**.

- [x] **B1** (`059fbd25`) — `CoverageChain.lean`: **`Graph.IsChain`** → `def:pencil-x0-chain`;
  **`Graph.IsX0Graph.exists_isChain`** → `lem:pencil-x0-chain-exists`;
  **`Graph.IsX0Graph.x0Reduces_of_forall_degree_eq_two`** → `lem:pencil-x0-cycle-reduces`; the two
  proofs reworded.
- [x] **B2** (`13a3d4e1`) — `CoverageCut.lean`, the gate and (H) at a chain's smaller graphs:
  **`Graph.IsChain.isX0Graph_induce`, `Graph.IsX0Graph.splitOff`** →
  `lem:pencil-x0-chain-standing`.
- [x] **B3** (`8858f01d`) — `CoverageCut.lean`, BRIDGE and CUT:
  **`Graph.IsX0Graph.x0Reduces_of_not_twoEdgeConnected`,
  `Graph.IsX0Graph.x0Reduces_of_not_connected`** → `lem:pencil-x0-cut-reduces`, the proof reworded.
- [x] **B4** (`a394309a`) — `CoverageTheoremS.lean`: **`Graph.ChainUsable`** →
  `def:pencil-x0-usable-chain`; **`Graph.IsChain.x0Reduces_of_chainUsable`** →
  `lem:pencil-x0-chain-reduces`; **`Graph.IsX0Graph.x0Reduces_of_deficiency_two_rigid`** →
  `lem:pencil-x0-planar-rigid-reduces`; **`Graph.IsX0Graph.exists_degree_eq_two_notMem`,
  `Graph.IsX0Graph.partitionDef_three_induce_diff_nonpos`** → `lem:pencil-x0-sparse-count`; eleven
  spike warnings fixed.
- [x] **B5** (`36e66c7a`) — `CoverageTheoremS.lean`: **`Graph.IsX0Graph.exists_additiveCore`** →
  `thm:pencil-x0-theorem-s`; **`Graph.IsX0Graph.x0Reduces`, `Graph.IsX0Graph.x0Attains`,
  `Graph.X0Attains.of_twoEdgeConnected`** → `thm:pencil-x0-coverage`; two spike warnings fixed.
- [x] **The close** (docs and blueprint, with one Lean docstring chore): the re-read of
  §`sec:main-component-coverage`, the headline axioms, the design doc, ROADMAP and
  `MolecularConjecture.md`, the exposition ledger; the public surfaces left unchanged (the PI's
  standing call: they update when Phase 40 closes, at MOTIVES).

## Blockers / open questions

- **None for 40m.**

## Hand-off / next phase

**40m is closed, and COVERAGE with it. Next: MOTIVES** (`X0Dist` and `X0Gen`; design doc §3
MOTIVES), Phase 40's last layer, which opens as its own sub-phase (lettered when it opens) and
closes Phase 40. Its first concrete step is the design-first open: the **MOTIVES pre-build recon**
(the 40l–40m precedent: compiler-checked, top rung), which settles the design doc's two open
questions, **(a)** the exact `hcard` constant and **(b)** the β-headroom's root cause, against the
landed SPINE2 threading, and then the open commit, which mints the letter and the work log and
runs the red-node consistency gate on `thm:pencil-x0-generic-attains`. MOTIVES consumes
`Graph.X0Attains.of_twoEdgeConnected` (and `Graph.IsX0Graph.x0Attains`) through the landed
`Graph.X0Attains.hasDistinctPencilRealization` (`X0Dist`) and the fibre-intersection lemma
(`X0Gen`). Its close updates the public surfaces (README, home_page, intro.tex,
`formalization.yaml`), writes or closes the two `[pending]` exposition entries (design doc §7),
and re-decides the held kernels (design doc §6).

## Decisions made during this phase

- **2026-09-28 — the close.** The re-read found every node's statement and proof on the Lean
  route; two proofs were tightened: `lem:pencil-x0-chain-standing` (1) now takes a nonempty proper
  subset, and `thm:pencil-x0-theorem-s`'s rigid case states its case split (two adjacent bodies of
  degree two lie on a chain with two interior bodies). Lean chore, docstrings only: four wrong or
  loose docstrings in `CoverageChain.lean` (`pathVertex_eq_of_val_eq_zero`,
  `IsOpenEar.exists_isLink_of_degree_eq_two`, `IsChain.two_le_of_adj`) and `CoverageTheoremS.lean`
  (`three_mul_sub_le_two_mul_ncard`, stated the wrong way round).
- **`61d97b06` (coordinator fixup):** B5's range ran F 1594–1805, one line short; F 1806 is
  `of_twoEdgeConnected`'s last line.
- **`eb085494` (coordinator fixup):** `lem:pencil-x0-cut-reduces`' B3-reworded proof: part (2)'s set
  `C` must be nonempty and not all of `G − v`; part (1) introduced no `V′`, and dropped why each
  side keeps degree ≥ 2.
- **B4/B5 docstrings, at the coordinator's request:** the module docstring's clause for
  `partitionDef_three_induce_diff_nonpos` states its global `hhubs`, and `x0Attains` names
  `thm:pencil-x0-coverage`.
- **B1–B5** — transcribed verbatim from the spikes with fresh docstrings; the thirteen spike warnings
  fixed as listed at the open; proof rewordings in B1 and B3 only.
- **File names** `CoverageChain`/`CoverageCut`/`CoverageTheoremS`, not the planned
  `Chains`/`Cuts`/`Cover`: those sit one letter from the step files `Chain.lean`, `Cut.lean` and
  from `Coverage.lean`.
- **`exists_isChain` keeps `_hv`** (M4's `_hdeg` precedent); a few helpers drop unused `Finite`
  binders (hypotheses only weaken). **Reuse:** the landed `Graph.isLink_eq_of_degree_eq_two`
  replaces S5's duplicate; Phase 39's M1–M3 not adopted (design doc §3 COVERAGE *Lean reuse*).
  **Placement:** the helpers stay in the new files (40l precedent); moving them by definition is a
  tracked cleanup-round item (design doc §3 COVERAGE).
- **2026-09-28 — opened design-first** from CHAINS' design recon (opus, read-only,
  compiler-checked); the PI folded THEOREM-S in (one open, B1–B5, one close).
