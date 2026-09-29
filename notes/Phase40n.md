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
wrapper). The Lean: M0 in `MainComponent/Statements.lean` (42 lines, new), `Pencil/Motive.lean`,
`MainComponent/Configuration.lean` and `Induction/ReducibleVertex.lean`; B1–B3 in the new
`MainComponent/GenericBase.lean` (888 lines; imports `Pencil/X0`, `MainComponent/CoverageTheoremS`,
`Matroid.Graph.Constructions.Sum`). Both are in the root import.

**Which sub-phase greens each remaining node** (red and unpinned, the 40h/40l convention):
- **EARS:** `lem:pencil-generic-steer`, `lem:pencil-generic-one-ear`,
  `lem:pencil-generic-pendant-triangle`.
- **REDUCE+CLOSE:** `lem:pencil-rigid-good-ear`, `thm:pencil-generic-step`,
  `thm:pencil-conditioned-pair-nonempty`, the rewritten `thm:pencil-x0-generic-attains`, and
  `thm:pencil-conjecture` (`pencil.tex`).
- **Planned pins** (the spikes' names; EARS' steering names are its own): one-ear ←
  `Graph.IsOpenEar.hasGenericPencilRealization_of_one`, `…_of_isNondegPencilRealization`;
  pendant triangle ← `hasGenericPencilRealization_of_closedEar_two`; good ear ←
  `Graph.IsX0Graph.exists_oneEar_or_pendantTriangle`; generic step ←
  `hasGenericPencilRealization_of_IH`; nonempty pair ← `pencilPair_of_nonempty`; generic attains ←
  `x0Gen`; the conjecture ← `pencil_conjecture`, `pencilPair_of_nonempty`. REDUCE+CLOSE's as
  re-planned at 40p's open (the good ear with two helpers, generic attains with three):
  `notes/Phase40p.md`.

**The interface EARS and REDUCE+CLOSE consume:** the base
`Graph.IsX0Graph.hasGenericPencilRealization_of_forall_deficiency_two_ne_zero`,
`PencilNondegFeasible.hub_conditions`, `Graph.noRigid_of_simple_of_ncard_eq_three` and `x0Dist`.

**Headline axioms, re-verified at the close** on 27 declarations: the eighteen
`formalization.yaml` main results and the nine 40n pins (M0's five, B1–B3's four). All 27 are
exactly `[propext, Classical.choice, Quot.sound]` (the definition `Graph.addTwoEar` included); none
uses `sorryAx`. *Measured, script not retained*: one `#print axioms` line per declaration under
`import CombinatorialRigidity`, run with `lake lean` on the fully built tree (a full `lake build`
first, after the close's docstring edits: 2 996 jobs, 0 warnings, 0 errors, 0 cache-write
failures).

**The spikes** (gitignored, local to this checkout; builder sources, not evidence). **Keep
`GenBase.lean`** until REDUCE+CLOSE transcribes its tail; the other two are copied into
`scratch/ears/Ears.lean`:
- `scratch/40n/OneEar.lean` (368 lines, the opening recon's, at `c2b74e61`; exit 0 at `8a0752d7`):
  Z1's extension, (MC-185).
- `scratch/40n-read/WitnessGen.lean` (the second read's): T2's witness, (MC-188).
- `scratch/40n-read/GenBase.lean` (954 lines): the route-B assembly over the base at the
  `[Finite α]` signature (l.792), with exactly three `sorry`s, (MC-129) (l.803), (MC-127)(a)
  (l.822) and (MC-127)(b) (l.835). Its lines 1–797 (`BaseFull.lean` and the wrapper) are now
  `GenericBase.lean` and redeclare the landed names under `import CombinatorialRigidity`; its tail,
  l.799 on, is the part to reuse, against the landed base.
- Stale at HEAD: `scratch/40n/Gen.lean`, `K23.lean`, `Headline.lean` (they redeclare M0's names);
  `scratch/40n-read/BaseFull.lean` and its parts are consumed.

## Architectural choices made up front

- **Route B** ((MC-183)): the generic conjunct at a simple 2EC feasible graph is proved inside
  `Graph.pencil_reduction`'s induction, from `PencilPair` at every smaller graph; the landed cut arm
  covers the non-2EC graphs. `X0Gen` is a corollary of `pencilPair_of_nonempty`.
- **Both headlines** (PI): `pencil_conjecture := pencil_conjecture_of_X0 x0Dist x0Gen` and
  `pencilPair_of_nonempty`, landed at REDUCE+CLOSE. `pencil_conjecture_of_X0Gen` does not land (the
  coordinator's call: superseded at the close, no consumer).
- **Placement** (the PI's convention: general pieces beside their definitions, the steps in new files
  under `Molecule/Pencil/MainComponent/`); the final assembly file is `MainComponent/Statements.lean`.

## Lemma checklist

All landed with the standard axioms (*Current state*); pins in **bold**.

- [x] **M0** (`8a0752d7`): **`x0Dist`**, **`PencilNondegFeasible.hub_conditions`**,
  **`Graph.noRigid_of_simple_of_ncard_eq_three`**, the two-hubs obstruction in both forms, verbatim
  from the opening recon's spikes.
- [x] **The second read** of (MC-183)–(MC-187) (`3d1d463f`, docs only).
- [x] **B1–B3, one build** (`2f126b5f`): **`Graph.addTwoEar`**, **`exists_planes_separate`**,
  **`isNondeg_pencilConfig_of_planeDiff`**,
  **`Graph.IsX0Graph.hasGenericPencilRealization_of_forall_deficiency_two_ne_zero`**, transcribed
  from `scratch/40n-read/BaseFull.lean` plus `GenBase.lean`'s wrapper, with lint cleanup.
- [x] **The close** (docs and blueprint, with a Lean docstring chore): the re-read of the eight
  green nodes, the headline axioms, the design doc, ROADMAP and `MolecularConjecture.md`, the
  exposition ledger; the public surfaces left unchanged (the PI's standing call: they update at
  Phase 40's close).

## Blockers / open questions

- **None for 40n.** EARS' recon has since spiked T1, T3 and Z2 sorry-free (`notes/Phase40o.md`).

## Hand-off / next phase

**40n is closed. MOTIVES continues with EARS, opened as sub-phase 40o** (2026-09-29, work log
`notes/Phase40o.md`, whose *Hand-off* names the next step). Its pre-build recon spiked every EARS
leaf sorry-free in `scratch/ears/`. Then REDUCE+CLOSE ((MC-129), the assembly from `GenBase.lean`
l.799 on, both headlines), whose close closes Phase 40 and updates the public surfaces.

## Decisions made during this phase

- **2026-09-28 — the close.** The re-read found the eight green nodes on the Lean route and tightened
  three. `lem:pencil-feasible-hub-conditions` drops "simple" (the Lean has no simplicity
  hypothesis). `lem:pencil-x0-planes-separate` states the affine functions at every body as part of
  the witness (the lifting kernel's point), since without admissibility they need not be unique.
  `thm:pencil-x0-base-generic`'s proof takes every pair and every triple of distinct bodies, as the
  Lean does, says the attaining polynomial makes the picture admissible, and cites the rank node.
  Lean chore, docstrings only: `GenericBase.lean`'s module summary, the spike narration on
  `exists_planes_separate` and the (MC-14) citation on BASE, and `Statements.lean`'s route-B range.
- **The recorded defect:** `3d1d463f` stated `lem:pencil-x0-planes-separate`'s good pictures as
  "admissible", which the spike never proves; `2f126b5f` dropped it. The workbook's (MC-184) does not
  carry it ("off a proper Zariski-closed set of pictures, some `(z, P) ∈ F(G, q)` has `P_u ≠ P_w`").
- **B1–B3** (`2f126b5f`): transcribed from `BaseFull.lean`; both flexible `simp`s needed a
  hand-verified `simp only` set (`FRICTION.md`, the `<;>`-chain idiom's third instance); two
  `unusedFintypeInType` hits suppressed with a justification.
- **`Graph.addTwoEar` in `GenericBase.lean`, not beside `embedEdges`** (the coordinator's call):
  keeps `import Matroid.Graph.Constructions.Sum` out of `Bridge.lean`'s downstream cone.
- **The second read** (`3d1d463f`, opus, fresh, read-only): no gap; (MC-183), (MC-184), (MC-186)
  repaired in place, (MC-188), (MC-189) added; BASE compiled sorry-free, so B1–B3 landed as one build.
- **M0** (`8a0752d7`): transcribed verbatim; `K23.lean`'s witness shrinking and
  `pencil_conjecture_of_X0Gen` do not land (unconsumed).
- **2026-09-28 — opened design-first** (`b4226f65`) from MOTIVES' pre-build recon (opus, read-only,
  compiler-checked; verdict in the design doc §3 MOTIVES); the PI's three calls (the split, `G_e`,
  both headlines) are verbatim in `notes/pencil/adjudications.md`.
