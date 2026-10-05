# Phase 40n — PENCIL-X0 / MOTIVES-DIST+BASE: the distinct statement, and the generic realization without a planar-rigid set (work log)

**Status:** ✓ complete (opened design-first, built and closed 2026-09-28). MOTIVES' first of three
sub-phases (the PI's call, 2026-09-28, `notes/pencil/adjudications.md`; plan
`notes/Phase40-design.md` §3 MOTIVES): **DIST+BASE**, then **EARS** and **REDUCE+CLOSE** by code.
It proved `X0Dist` and the base of route B ((MC-183)–(MC-189), `notes/pencil/workbook/K-main-MC19.md`,
second-read 2026-09-28). **EARS opened as sub-phase 40o** (2026-09-29, design-first from its
pre-build recon; work log `notes/Phase40o.md`); see *Hand-off*.

## Current state

**Closed.** Open `b4226f65`, M0 `8a0752d7`, the second read `3d1d463f`, B1–B3 `2f126b5f`, and the
close. Eight of the fourteen new nodes of `main-component.tex` §`sec:main-component-statements`
are green and pinned: M0's `lem:pencil-x0-distinct-statement` (`x0Dist`),
`lem:pencil-feasible-hub-conditions`, `lem:pencil-three-bodies-no-rigid`,
`lem:pencil-x0-two-hubs-obstruction` (both forms), and B1–B3's `def:pencil-two-ear-graph`
(`Graph.addTwoEar`), `lem:pencil-x0-planes-separate` (`exists_planes_separate`),
`lem:pencil-x0-conjunct-three` (`isNondeg_pencilConfig_of_planeDiff`), `thm:pencil-x0-base-generic`
(`Graph.IsX0Graph.hasGenericPencilRealization_of_forall_deficiency_two_ne_zero`, the `[Finite α]`
wrapper). The Lean: M0 in `MainComponent/Statements.lean` (new); B1–B3 in the new
`MainComponent/GenericBase.lean` (888 lines). Both are in the root import.

**Which sub-phase greens each remaining node** (red and unpinned, the 40h/40l convention): EARS
greens `lem:pencil-generic-steer`, `lem:pencil-generic-one-ear`,
`lem:pencil-generic-pendant-triangle`; REDUCE+CLOSE greens `lem:pencil-rigid-good-ear`,
`thm:pencil-generic-step`, `thm:pencil-conditioned-pair-nonempty`, the rewritten
`thm:pencil-x0-generic-attains`, and `thm:pencil-conjecture` (`pencil.tex`) — as re-planned at
40p's open: `notes/Phase40p.md`.

**The interface EARS and REDUCE+CLOSE consume:** the base
`Graph.IsX0Graph.hasGenericPencilRealization_of_forall_deficiency_two_ne_zero`,
`PencilNondegFeasible.hub_conditions`, `Graph.noRigid_of_simple_of_ncard_eq_three` and `x0Dist`.

**Headline axioms, re-verified at the close** on 27 declarations (the eighteen
`formalization.yaml` main results and the nine 40n pins): all exactly
`[propext, Classical.choice, Quot.sound]`; none uses `sorryAx`.

## Architectural choices made up front

- **Route B** ((MC-183)): the generic conjunct at a simple 2EC feasible graph is proved inside
  `Graph.pencil_reduction`'s induction, from `PencilPair` at every smaller graph; the landed cut arm
  covers the non-2EC graphs. `X0Gen` is a corollary of `pencilPair_of_nonempty`.
- **Both headlines** (PI): `pencil_conjecture := pencil_conjecture_of_X0 x0Dist x0Gen` and
  `pencilPair_of_nonempty`, landed at REDUCE+CLOSE. `pencil_conjecture_of_X0Gen` does not land (the
  coordinator's call: superseded at the close, no consumer).
- **Placement** (the PI's convention: general pieces beside their definitions, the steps in new files
  under `Molecule/Pencil/MainComponent/`); the final assembly file is `MainComponent/Statements.lean`.

## Decisions made during this phase

- **2026-09-28 — the close.** The re-read found the eight green nodes on the Lean route and
  tightened three: `lem:pencil-feasible-hub-conditions` drops "simple" (the Lean has no simplicity
  hypothesis); `lem:pencil-x0-planes-separate` states the affine functions at every body as part of
  the witness, since without admissibility they need not be unique; `thm:pencil-x0-base-generic`'s
  proof takes every pair and triple of distinct bodies, as the Lean does. Docstring fixes only,
  elsewhere.
- **The recorded defect:** `3d1d463f` stated `lem:pencil-x0-planes-separate`'s good pictures as
  "admissible", which the spike never proves; `2f126b5f` dropped it. The workbook's (MC-184) does
  not carry it. A reader's repair text is one writer's too (`DESIGN.md`).
- **M0** (`8a0752d7`) and **B1–B3** (`2f126b5f`): both transcribed verbatim from the opening
  recon's spikes; two flexible `simp`s needed a hand-verified `simp only` set (`FRICTION.md`, the
  `<;>`-chain idiom's third instance). `Graph.addTwoEar` landed in `GenericBase.lean`, not beside
  `embedEdges` (the coordinator's call: keeps `import Matroid.Graph.Constructions.Sum` out of
  `Bridge.lean`'s downstream cone).
- **The second read** (`3d1d463f`, opus, fresh, read-only): no gap; (MC-183), (MC-184), (MC-186)
  repaired in place, (MC-188), (MC-189) added; BASE compiled sorry-free, so B1–B3 landed as one
  build.
- **2026-09-28 — opened design-first** (`b4226f65`) from MOTIVES' pre-build recon (opus, read-only,
  compiler-checked; verdict in the design doc §3 MOTIVES); the PI's three calls (the split, `G_e`,
  both headlines) are verbatim in `notes/pencil/adjudications.md`.

## Blockers / open questions

- None for 40n.

## Hand-off / next phase

**40n is closed. MOTIVES continues with EARS, opened as sub-phase 40o** (2026-09-29, work log
`notes/Phase40o.md`, whose *Hand-off* names the next step). Then REDUCE+CLOSE, whose close closes
Phase 40 and updates the public surfaces.
