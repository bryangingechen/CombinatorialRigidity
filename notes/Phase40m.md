# Phase 40m — PENCIL-X0 / COVERAGE-CHAINS + THEOREM-S: chains, cuts, Theorem S and the covering theorem (work log)

**Status:** ✓ complete (opened design-first, built and closed 2026-09-28). COVERAGE's second and
last sub-phase: **CHAINS** (the maximal ear through bodies of degree two, chains, the cycle, and the
cut-vertex and bridge reductions, with (H) at every smaller graph) with **THEOREM-S** (Theorem S and
the covering theorem) folded in, by the PI's call (2026-09-28, `notes/pencil/adjudications.md`;
plan `notes/Phase40-design.md` §3 COVERAGE). Its close also closes COVERAGE: the general
configuration attains at every graph satisfying (H). **Next: 40n** (MOTIVES-DIST+BASE, opened
2026-09-28): work log `notes/Phase40n.md`.

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

The Lean is three leaf modules in `Molecule/Pencil/MainComponent/`: `CoverageChain.lean` (708
lines), `CoverageCut.lean` (640; its five BRIDGE helpers `private`), `CoverageTheoremS.lean` (580).
**MOTIVES' interface:** `Graph.IsX0Graph.x0Attains` (every (H)-graph attains, `[Infinite K]`) and
`Graph.X0Attains.of_twoEdgeConnected` (the consumer's form).

**Headline axioms, re-verified at the close** on 34 declarations (the eighteen
`formalization.yaml` main results and the sixteen 40m pins): all exactly
`[propext, Classical.choice, Quot.sound]`; none uses `sorryAx`.

## Architectural choices made up front

- **The route** (the recon's verdict; design doc §3 COVERAGE items 2–3): one core, the maximal ear
  `Graph.IsOpenEar.exists_maximal`, serves chain extraction and the cycle, and BRIDGE runs the same
  extension on a bridge ear with its two sides tracked; the cut arguments go through one gate,
  `Graph.Connected.induce_of_gate`; THEOREM-S is S5's text.
- **Layout:** the three new leaf modules above, named with the `Coverage` prefix (*Decisions*).

## Decisions made during this phase

- **2026-09-28 — the close.** The re-read found every node's statement and proof on the Lean
  route; two proofs were tightened: `lem:pencil-x0-chain-standing` (1) now takes a nonempty proper
  subset, and `thm:pencil-x0-theorem-s`'s rigid case states its case split (two adjacent bodies of
  degree two lie on a chain with two interior bodies). Four docstring fixes, no proof change.
- **B1–B5** transcribed verbatim from the spikes, thirteen spike warnings fixed, proof rewordings
  in B1 and B3 only. Two coordinator fixups: `61d97b06` (B5's range one line short), `eb085494` (a
  reworded proof's missing nonemptiness and introduced set).
- **The recon's other flags, settled by precedent** (`notes/pencil/adjudications.md`): file names
  `CoverageChain`/`CoverageCut`/`CoverageTheoremS`, not the planned `Chains`/`Cuts`/`Cover` (one
  letter from the step files and from `Coverage.lean`); `exists_isChain` keeps `_hv` (M4's `_hdeg`
  precedent); the landed `Graph.isLink_eq_of_degree_eq_two` replaces S5's duplicate, Phase 39's
  M1–M3 not adopted; the helpers stay in the new files (40l precedent) — moving them to their
  definition's file was a tracked cleanup-round item (design doc §3 COVERAGE), paid by round 1,
  task 20 (`473a4a11`).
- **2026-09-28 — opened design-first** from CHAINS' design recon (opus, read-only,
  compiler-checked); the PI folded THEOREM-S in (one open, B1–B5, one close).

## Blockers / open questions

- None for 40m.

## Hand-off / next phase

**40m is closed, and COVERAGE with it. MOTIVES continues in 40n**, DIST+BASE, the first of its three
sub-phases (the PI's call at 40n's open, 2026-09-28), opened design-first from a compiler-checked
recon that settled the headroom questions (none is needed) and replaced the fibre route to `X0Gen`
by route B: work log `notes/Phase40n.md`. MOTIVES consumes this sub-phase's interface,
`Graph.X0Attains.of_twoEdgeConnected` and `Graph.IsX0Graph.x0Attains`; its close closes Phase 40.
