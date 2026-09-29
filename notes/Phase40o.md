# Phase 40o — PENCIL-X0 / MOTIVES-EARS: the steering and the two ear steps (work log)

**Status:** ✓ complete (opened design-first, built and closed 2026-09-29). MOTIVES' second of three
sub-phases (the PI's call, 2026-09-28; plan `notes/Phase40-design.md` §3 MOTIVES): after DIST+BASE
(40n), **EARS** greened the three nodes route B's assembly consumes at its two ear cases. Its claims
(MC-190)–(MC-192) were second-read after the builds, with no gap. **Next: REDUCE+CLOSE's pre-build
recon** (not yet opened), whose close closes Phase 40; see *Hand-off*.

## Current state

**Closed.** Open `9a877a94`, B1 `e7c80bba`, B2 `45d49861`, B3 `f62cfd3c`, B4 `306dcf15`, the
coordinator's fixup `7f782d79`, then the second read and the close in one commit. All three EARS
nodes of `main-component.tex` §`sec:main-component-statements` are green and pinned:
- `lem:pencil-generic-steer` ← `CombinatorialRigidity.Molecular.exists_pencilSeed_of_nondeg_of_selectors`
  (T1, `Pencil/Reseed.lean`, 386 lines), `…exists_coord_linearIndependent_pencilChartPoint_of_other_nonhub`
  ((MC-188)), `…exists_isNondegPencilRealization_restrict_of_demoted` ((a), (MC-190)) and
  `…exists_isNondegPencilRealization_steer` ((b), (MC-191)), in the new
  `MainComponent/GenericSteer.lean` (776 lines);
- `lem:pencil-generic-one-ear` ← `Graph.IsOpenEar.hasGenericPencilRealization_of_isNondegPencilRealization`
  ((MC-185)) and `Graph.IsOpenEar.hasGenericPencilRealization_of_one`, in the new
  `MainComponent/GenericEar.lean` (570 lines);
- `lem:pencil-generic-pendant-triangle` ←
  `CombinatorialRigidity.Molecular.hasGenericPencilRealization_of_closedEar_two_of_isNondegPencilRealization`
  ((MC-192)) and `…hasGenericPencilRealization_of_closedEar_two`, in the new
  `MainComponent/GenericTriangle.lean` (680 lines).

All three new files are in the root import.

**The interface REDUCE+CLOSE consumes:** `Graph.IsOpenEar.hasGenericPencilRealization_of_one` (no
`hnadj`: feasibility excludes the triangle `a x b` with two hubs) and
`hasGenericPencilRealization_of_closedEar_two` (`4 ≤ G.degree c`, no deficiency hypothesis). Each
takes `G.Simple`, `PencilNondegFeasible K G` and the smaller graph's induction hypothesis in the
conditioned form. The five nodes left in `sec:main-component-statements` and `pencil.tex`
(`lem:pencil-rigid-good-ear`, `thm:pencil-generic-step`, `thm:pencil-conditioned-pair-nonempty`,
`thm:pencil-x0-generic-attains`, `thm:pencil-conjecture`) stay red and unpinned for REDUCE+CLOSE.
Their planned pins are in `notes/Phase40n.md`.

**Headline axioms, re-verified at the close** on 26 declarations: the eighteen `formalization.yaml`
main results and the eight 40o pins above. All 26 are exactly `[propext, Classical.choice,
Quot.sound]`; none uses `sorryAx`. *Measured, script not retained*: one `#print axioms` line per
declaration under `import CombinatorialRigidity`, run with `lake lean` on the fully built tree (a
full `lake build` first, after the close's docstring edits: 2 999 jobs, 0 warnings, 0 errors, 0
cache-write failures).

**The spikes** (gitignored, local to this checkout; builder sources, not evidence). **Keep
`scratch/ears/`** until REDUCE+CLOSE transcribes its assembly:
- `Route.lean` (2264 lines), the route-B assembly's source: `Ears.lean` plus
  `scratch/40n-read/GenBase.lean`'s tail from l.799, with exactly one `sorry`, (MC-129)
  (`Graph.IsX0Graph.exists_oneEar_or_pendantTriangle`, l.2144). Its one-ear call (l.2186) still
  passes `hnadj`, which the landed step no longer takes. Its tail from l.2139 on is the part to reuse.
- `Ears.lean` is consumed by B1–B4; `PlaceReseed/Steer/Ear/Tri.lean` are stale at HEAD (they
  redeclare landed names).
- The second read's compiler witnesses are in `scratch/ears-read/Witness.lean` (exit 0 at
  `7f782d79`).

## Architectural choices made up front

- **Placement** (the coordinator's call, the recon's proposal): T1 beside `exists_pencilSeed_of_nondeg`
  in `Pencil/Reseed.lean`, with `exists_extend_linearIndependent` moved there from `Steer.lean`;
  (MC-188), T2 and T3 in `GenericSteer.lean`; Z1 in `GenericEar.lean`; Z2 in `GenericTriangle.lean`.
- **Z1 drops `hnadj : ¬ G.Adj a b`** (the coordinator's call): the proof never uses it, and (F2) at a
  feasible `G` already excludes it. The second read derived it from feasibility alone
  (`scratch/ears-read/Witness.lean`, W1).

## Lemma checklist

All landed with the standard axioms (*Current state*).

- [x] **B1 = T1** (`e7c80bba`): the reseed at given selectors, into `Pencil/Reseed.lean`.
- [x] **B2 = T2 + T3** (`45d49861`): the steering lemma, the new `GenericSteer.lean`.
- [x] **B3 = Z1** (`f62cfd3c`): the one-ear step, the new `GenericEar.lean`, without `hnadj`.
- [x] **B4 = Z2** (`306dcf15`): the pendant triangle, the new `GenericTriangle.lean`, with the
  shared `isLink_cases_of_closedEar_two`.
- [x] **The second read** of (MC-190)–(MC-192) (in the close commit): no gap, repairs in place.
- [x] **The close**: the three nodes re-read, the headline axioms, the design doc, ROADMAP,
  `MolecularConjecture.md` and the exposition ledger. The public surfaces are unchanged (the PI's
  standing call: they update at Phase 40's close).

## Blockers / open questions

- **None for 40o.** REDUCE+CLOSE's one new leaf, (MC-129) at 2EC graphs, has a proof in the workbook
  (Step MC19) but no spike yet.

## Hand-off / next phase

**40o is closed. Next concrete step: REDUCE+CLOSE's pre-build recon** (compiler-checked, top rung,
read-only), before REDUCE+CLOSE opens as the next sub-phase. Its inputs:
- (MC-129) at 2EC graphs, `Graph.IsX0Graph.exists_oneEar_or_pendantTriangle`: the one remaining
  `sorry` of `scratch/ears/Route.lean`, l.2144 (workbook proof in Step MC19; 40l's deficiency kit);
- the route-B assembly from `Route.lean`'s tail (l.2139 on: `hasGenericPencilRealization_of_IH`,
  `pencilPair_of_IH`, `pencilPair_of_nonempty`, `x0Gen`), with the one-ear call now without
  `hnadj`;
- both headlines, `pencil_conjecture` and `pencilPair_of_nonempty` (the PI's call,
  `notes/Phase40n.md` *Architectural choices*);
- the Phase 40 close, which updates the public surfaces.

Its close closes Phase 40. **The Phase 40 close also carries three items the recon does not settle**
(coordinator, 2026-09-29): re-deciding the held kernels (`notes/Phase40-design.md` §6: (K-res)/`kres`,
(K-c), (K-bare-c) with (α), smark's O7e programme), which is **the PI's call**, surfaced with options
and not decided by the close; writing or closing the two `[pending]` exposition entries (design doc
§7, `notes/BlueprintExposition.md`); and the public surfaces (README, home_page, intro.tex,
`formalization.yaml`, the PI's standing call). The spikes (`scratch/ears/`, `scratch/40n-read/`) are
gitignored and exist only in this checkout. A session without them re-derives the assembly from
`scratch/ears/Route.lean`'s recorded shape in the design doc §3 MOTIVES.

## Decisions made during this phase

- **2026-09-29 — the second read and the close** (one commit; opus, fresh, read-only): no gap.
  (MC-190) confirmed; (MC-191) states the rank's upper bound and calls the three-closed-neighbours
  count sufficient, not "exactly" needed; (MC-192) credits Crapo–Whiteley 1982, Prop. 3.4 for the
  triangle's rigidity (KT Lemma 5.4 asserts existence only); (MC-193) added: the count is the Lean
  chart's, off the route. Blueprint: the steer node's non-hub wording and (b)'s upper bound; the
  pendant triangle's nondegeneracy sentence. Lean, docstrings only: claim labels repointed, spike
  narration dropped, and GenericTriangle's "whose deficiency does not rise" (read as a hypothesis
  the step does not take).
- **Recorded exception: `#print axioms` in library files.** B2 and B4 carried the spike's
  `#print axioms` commands into `GenericSteer.lean` and `GenericTriangle.lean`. A warning-only gate
  does not read `info:` output, so it passed them; the coordinator's fixup `7f782d79` dropped all
  four. Builders transcribing a spike should strip its `#print axioms` lines.
- **B4's tidy-up:** the twice-written link case analysis became `isLink_cases_of_closedEar_two`.
  **B2's:** the unused `hWF₂` is bound as `-`.
- **2026-09-29 — opened design-first** (`9a877a94`) from EARS' pre-build recon (opus, read-only,
  compiler-checked): every leaf closed sorry-free at `GenBase.lean`'s signatures, with no shorter
  route; its new claims (MC-190)–(MC-192) are in Step MC19. The blueprint restatement: the steer node
  as (a), any subgraph, and (b), (MC-191)'s scope; the one-ear node without non-adjacency.
