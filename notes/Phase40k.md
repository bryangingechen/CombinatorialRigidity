# Phase 40k — PENCIL-X0 / CONTRACT-A: contraction at an additive core (work log)

**Status:** ✓ complete (opened design-first, built and closed 2026-09-28). CONTRACT-A, STEPS'
seventh and last group (`notes/Phase40-design.md` §3 STEPS), proved the contraction step at a
rigid core whose planar deficiency adds: at an induced core `H = G[W]`, `W ⊊ V(G)`, `|W| ≥ 2`,
`def₃(H) = 0`, with no outside body adjacent to two core bodies, in a 2EC `G` satisfying (H), if
`def₂(H) + def₂(G/H) ≤ def₂(G)` and `X₀` attains at `H` and at `G/H`, then `X₀(G)` attains
((MC-71)). No new mathematics. **STEPS is done.** Phase 40 continued with **COVERAGE's REDUCE**
(`notes/Phase40l.md`, closed 2026-09-28) and on through the phase's own close, 2026-09-29
(`notes/Phase40-design.md` §3, ROADMAP §40).

## Current state

**Closed.** Three build commits (B1 `b7e9a778` the `Contract.lean` split, B2 `8499bb79`, B3
`b394aac3`) and the close landed. The five nodes of `main-component.tex`
§`sec:main-component-contract-additive` are green — `lem:pencil-rank-collineation`,
`lem:pencil-contract-kernel-bound`, `lem:pencil-contract-magnified-rank`,
`lem:pencil-contract-standing-rigid` and `thm:pencil-x0-contract-additive` — with CONTRACT-R as
the case `def₂(H) = 0` (an 18-line corollary since round 4's 10p, `993b9e74`). The Lean is
`Molecule/Pencil/MainComponent/ContractAdditive.lean`, importing `ContractCurve.lean` (the pieces
shared with CONTRACT-R, plus CONTRACT-A's general pieces) only; `Contract.lean` keeps the
flat-core pieces and CONTRACT-R; the collineation lemma is in `Configuration.lean`. Headline
axioms were re-verified at the close on 28 declarations (the eighteen `formalization.yaml` main
results, the six pins of the five nodes, and the four pins of `lem:pencil-contract-standing`,
whose statement the close edited), all exactly `[propext, Classical.choice, Quot.sound]`.

**Satisfiability** (not landed, kernel-checked in the recon's instance spike): θ(1,3,4) on `Fin
7`, core `C₄`, path `0–4–5–6–1`, `G/H = C₄`; CONTRACT-R does not cover it (`def₂(H) ≥ 1`).
**Faithfulness**: `of_additiveContract` is (MC-71) in the `≤` form; (H) is asked at `G` only.

## Architectural choices made up front

**The route** (the recon's verdict): two bounds on `ker M(0)` force the core heights onto
`L_H(q)` through Jackson–Jordán additivity, and the core's rank is read by a collineation at the
fixed picture, in place of (MC-68)(d)'s core-freeness and (MC-38)'s dominance (a proof-level
departure, not second-read). Of the coordinator's ten calls (2026-09-28, under the PI's
session-start "follow precedent"), the design doc cross-references four by number: **call 4**
keeps `hatt`, for parity with CONTRACT-R; **call 5** is option A — the general pieces to the new
`ContractCurve.lean` (split out of `Contract.lean`), CONTRACT-R untouched (option B, re-proving
CONTRACT-R through CONTRACT-A and FLAT, was not adopted then — round 4's 10p–10q later did it
anyway); **call 8** sends (MC-67), (MC-68) and (MC-70) to the design doc's §2 *Not needed*; **call 12**
tracked four corollary rebases as a cleanup item, paid by round 1, tasks 14a–14b
(`58c4fa28`, blueprint fixup `388e5a18`; `ab2253e1`) — the recon's labels, mapped to Lean names:
G1 `PanelHingeFramework.finrank_span_rigidityRows_ofNormals_linearEquiv`
(`lem:pencil-rank-collineation`, `Configuration.lean`), G4
`Graph.finrank_ker_contractLiftingMatrix_zero_add_three_le` and G5
`Graph.isX0Graph_induce_of_deficiency_eq_zero` (both `ContractCurve.lean`).

## Decisions made during this phase

- **2026-09-28 — the close.** `lem:pencil-contract-standing` restated so its `G/H` clauses no
  longer assume `def₂(H) = 0` (the Lean never did); the remark after the step became the
  exposition-ledger entry.
- **B1.** The `Contract.lean` split: `ContractCurve.lean` (importing `Cut.lean`) takes every
  piece CONTRACT-R shares; `Contract.lean` (importing `ContractCurve.lean` only) keeps
  `Graph.exists_core_plane`, the flat K3, the flat core rank, the `def₂` standing lemma and
  CONTRACT-R; `contractLimitMap` lemmas generalized in place to a plane hypothesis. No pin moved.

## Hand-off / next phase

**40k is closed, and with it STEPS.** The next concrete step moved to `notes/Phase40l.md`:
COVERAGE, the structural half and the assembly, runs as three sub-phases (the PI's call,
2026-09-28), the first REDUCE = 40l.
