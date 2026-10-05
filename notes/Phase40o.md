# Phase 40o — PENCIL-X0 / MOTIVES-EARS: the steering and the two ear steps (work log)

**Status:** ✓ complete (opened design-first, built and closed 2026-09-29). MOTIVES' second of three
sub-phases (the PI's call, 2026-09-28; plan `notes/Phase40-design.md` §3 MOTIVES): after DIST+BASE
(40n), **EARS** greened the three nodes route B's assembly consumes at its two ear cases. Its claims
(MC-190)–(MC-192) were second-read after the builds, with no gap. **REDUCE+CLOSE opened as
sub-phase 40p** (2026-09-29, design-first; work log `notes/Phase40p.md`); see *Hand-off*.

## Current state

**Closed.** Open `9a877a94`, B1 `e7c80bba`, B2 `45d49861`, B3 `f62cfd3c`, B4 `306dcf15`, the
coordinator's fixup `7f782d79`, then the second read and the close in one commit. All three EARS
nodes of `main-component.tex` §`sec:main-component-statements` are green and pinned:
- `lem:pencil-generic-steer` ← `CombinatorialRigidity.Molecular.exists_pencilSeed_of_nondeg_of_selectors`
  (T1, `Pencil/Reseed.lean`), `…exists_coord_linearIndependent_pencilChartPoint_of_other_nonhub`
  ((MC-188)), `…exists_isNondegPencilRealization_restrict_of_demoted` ((a), (MC-190)) and
  `…exists_isNondegPencilRealization_steer` ((b), (MC-191)), in the new
  `MainComponent/GenericSteer.lean`;
- `lem:pencil-generic-one-ear` ← `Graph.IsOpenEar.hasGenericPencilRealization_of_isNondegPencilRealization`
  ((MC-185)) and `Graph.IsOpenEar.hasGenericPencilRealization_of_one`, in the new
  `MainComponent/GenericEar.lean`;
- `lem:pencil-generic-pendant-triangle` ←
  `CombinatorialRigidity.Molecular.hasGenericPencilRealization_of_closedEar_two_of_isNondegPencilRealization`
  ((MC-192)) and `…hasGenericPencilRealization_of_closedEar_two`, in the new
  `MainComponent/GenericTriangle.lean`.

All three new files are in the root import.

**The interface REDUCE+CLOSE consumes:** `Graph.IsOpenEar.hasGenericPencilRealization_of_one` (no
`hnadj`: feasibility excludes the triangle `a x b` with two hubs) and
`hasGenericPencilRealization_of_closedEar_two` (`4 ≤ G.degree c`, no deficiency hypothesis). The
five nodes left in `sec:main-component-statements` and `pencil.tex` stay red and unpinned for
REDUCE+CLOSE; their pins are planned in `notes/Phase40p.md`.

**Headline axioms, re-verified at the close** on 26 declarations (the eighteen `formalization.yaml`
main results and the eight 40o pins above): all exactly `[propext, Classical.choice,
Quot.sound]`; none uses `sorryAx`.

## Architectural choices made up front

- **Placement** (the coordinator's call, the recon's proposal): T1 beside `exists_pencilSeed_of_nondeg`
  in `Pencil/Reseed.lean`, with `exists_extend_linearIndependent` moved there from `Steer.lean`;
  (MC-188), T2 and T3 in `GenericSteer.lean`; Z1 in `GenericEar.lean`; Z2 in `GenericTriangle.lean`.
- **Z1 drops `hnadj : ¬ G.Adj a b`** (the coordinator's call): the proof never uses it, and (F2) at a
  feasible `G` already excludes it; the second read derived it from feasibility alone.

## Decisions made during this phase

- **2026-09-29 — the second read and the close** (one commit; opus, fresh, read-only): no gap.
  (MC-190) confirmed; (MC-191) states the rank's upper bound and calls the three-closed-neighbours
  count sufficient, not "exactly" needed; (MC-192) credits Crapo–Whiteley 1982, Prop. 3.4 for the
  triangle's rigidity (KT Lemma 5.4 asserts existence only); (MC-193) added, off the route: the
  count is the Lean chart's. Blueprint and docstring fixes only, no Lean rework.
- **Recorded exception: `#print axioms` in library files.** B2 and B4 carried the spike's
  `#print axioms` commands into `GenericSteer.lean` and `GenericTriangle.lean`; a warning-only gate
  does not read `info:` output, so it passed them. The coordinator's fixup `7f782d79` dropped all
  four (promoted to `TACTICS-QUIRKS.md` §55: strip every spike's `#print`/`#check`/`#eval` line
  before transcribing). B4's twice-written link case analysis became `isLink_cases_of_closedEar_two`.
- **2026-09-29 — opened design-first** (`9a877a94`) from EARS' pre-build recon (opus, read-only,
  compiler-checked): every leaf closed sorry-free at `GenBase.lean`'s signatures, with no shorter
  route; its new claims (MC-190)–(MC-192) are in Step MC19.

## Blockers / open questions

- None for 40o.

## Hand-off / next phase

**40o is closed. REDUCE+CLOSE is open as sub-phase 40p** (`notes/Phase40p.md`): its next step,
the one build, and the three items the Phase 40 close carries are in that note's *Hand-off*.
