# Phase 40o — PENCIL-X0 / MOTIVES-EARS: the steering and the two ear steps (work log)

**Status:** in progress (opened design-first 2026-09-29). MOTIVES' second of three sub-phases (the
PI's call, 2026-09-28; plan `notes/Phase40-design.md` §3 MOTIVES): after DIST+BASE (40n), **EARS**,
then **REDUCE+CLOSE** by code. EARS greens the three nodes route B's assembly consumes at its two ear
cases: the steering lemma, the one-ear step and the pendant-triangle step. Its pre-build recon
compiled every leaf sorry-free, so the builds are transcriptions. **B1 and B2 landed** (T1 the
reseed, T2+T3 the steering lemma; `lem:pencil-generic-steer` green). **Next: B3** (Z1, the one-ear
step), then B4, then the second read of (MC-190)–(MC-192), then the close — see *Hand-off*.

## Current state

**B1 landed** (T1, the reseed at given selectors): `exists_extend_linearIndependent` moved verbatim
from `Pencil/Steer.lean` into `Pencil/Reseed.lean` (`Steer.lean` now reaches it through that existing
import), then `scratch/ears/Ears.lean` l.23–219 (the six T1 lemmas, ending with
`exists_pencilSeed_of_nondeg_of_selectors`) appended there. No blueprint node flips (T1 pins nothing
on its own; it feeds B2's `lem:pencil-generic-steer`). `notes/FRICTION.md`'s `[mirror-candidate]`
entry now records T1 as the lemma's second consumer and its new home.

**B2 landed** (T2 + T3, the steering lemma): `scratch/ears/Ears.lean` l.221–956 moved verbatim into
the new `Pencil/MainComponent/GenericSteer.lean` (importing `…Molecule.Pencil.Steer`), with the
`hWF₂`-unused tidy-up (bound as `-`). Greens `lem:pencil-generic-steer`, statement and proof, pinned
to all four planned names (`exists_pencilSeed_of_nondeg_of_selectors`,
`exists_coord_linearIndependent_pencilChartPoint_of_other_nonhub`,
`exists_isNondegPencilRealization_restrict_of_demoted` ((a)),
`exists_isNondegPencilRealization_steer` ((b))); the node's restated (a)/(b) checked against the
landed hypotheses before flipping — (a)'s "with normals independent on the closed hub-neighbourhood
in `G`" clause is already part of `IsNondegPencilRealization G`'s own third conjunct, not a separate
proof obligation. Root import added alphabetically (`GenericBase` < `GenericSteer` < `Lines`).

The remaining three EARS nodes of `blueprint/src/chapter/main-component.tex`
§`sec:main-component-statements` are still red and unpinned (the 40n convention). Each of B2–B4 adds
its node's `\lean{…}` and `\leanok` (statement and proof). **Planned pins:**
- `lem:pencil-generic-steer` (B2) ← `CombinatorialRigidity.Molecular.exists_pencilSeed_of_nondeg_of_selectors`,
  `…exists_coord_linearIndependent_pencilChartPoint_of_other_nonhub`,
  `…exists_isNondegPencilRealization_restrict_of_demoted` ((a)), `…exists_isNondegPencilRealization_steer` ((b)).
- `lem:pencil-generic-one-ear` (B3) ← `Graph.IsOpenEar.hasGenericPencilRealization_of_one`,
  `Graph.IsOpenEar.hasGenericPencilRealization_of_isNondegPencilRealization`.
- `lem:pencil-generic-pendant-triangle` (B4) ←
  `CombinatorialRigidity.Molecular.hasGenericPencilRealization_of_closedEar_two`,
  `…hasGenericPencilRealization_of_closedEar_two_of_isNondegPencilRealization`.

REDUCE+CLOSE's nodes (`lem:pencil-rigid-good-ear`, `thm:pencil-generic-step`,
`thm:pencil-conditioned-pair-nonempty`, `thm:pencil-x0-generic-attains`, `thm:pencil-conjecture`)
stay red and unpinned; their planned pins are in `notes/Phase40n.md`.

**The red-node consistency gate, run at this open.** The three nodes were rewritten from the spike's
statements and (MC-185), (MC-186), (MC-188), (MC-190)–(MC-192). Each proof routes through the
restated steering lemma's (a) and (b), and every `\uses` label exists and is live. The upper bound
now cites `lem:relative-deficiency-rank-bound`, the node pinning the bound the Lean uses.

**The spikes** (gitignored `scratch/ears/`, local to this checkout; builder sources, not evidence;
**keep them** until the close). All were run with `lake lean` at `3e27b385`, and the coordinator's
re-run matched:
- `Ears.lean` (2138 lines, the build source): exit 0, 0 warnings, standard axioms on its eight
  `#print axioms` lines, no `sorryAx`; batteries `#lint` clean.
- `Route.lean` (2264 lines): `Ears.lean` plus `scratch/40n-read/GenBase.lean`'s tail from l.799.
  Exit 0 with exactly one `sorry`, l.2144, (MC-129) (`Graph.IsX0Graph.exists_oneEar_or_pendantTriangle`,
  REDUCE+CLOSE's).
- `PlaceReseed.lean`, `PlaceSteer.lean`, `PlaceEar.lean`, `PlaceTri.lean`: the placement tests below,
  each over its target's imports only; exit 0, 0 warnings.

## Architectural choices made up front

- **Placement** (the coordinator's call, the recon's proposal; the PI's convention: general pieces
  beside their definitions, the steps in new files under `Molecule/Pencil/MainComponent/`):
  - T1 in `Pencil/Reseed.lean`, beside `exists_pencilSeed_of_nondeg`, with
    `exists_extend_linearIndependent` moved there from `Pencil/Steer.lean`;
  - (MC-188), T2 and T3 in the new `MainComponent/GenericSteer.lean` (`Witness.lean`, 1809 lines, and
    `Steer.lean`, 1412, are at or past the soft cap);
  - Z1 in `GenericEar.lean`, Z2 in `GenericTriangle.lean`.

  No new file name is one letter from an existing one, and no new declaration name is one edit
  from a declaration in the tree or the Matroid package (checked by script).
- **Z1 drops `hnadj : ¬ G.Adj a b`** (the coordinator's call): the proof never uses it, since (F2) at
  a feasible simple `G` already excludes the triangle `a x b` with two hubs. So the landed statement
  is strictly stronger. It was kernel-checked in a copy of the spike with the hypothesis removed.
- **The second read after the builds, before the close** (the coordinator's call): the Lean is
  complete and kernel-checked at the exact signatures route B's assembly consumes, so the read checks
  the workbook prose of (MC-190)–(MC-192), not the builds.

## Lemma checklist

Each B-item is one commit by a fresh sonnet builder, handed its `scratch/ears/Ears.lean` range.
Every one of the spike's 23 declarations falls in exactly one range (checked by script; no stray);
lines 1–22 are the spike's header and 2138 its `end`. **Every build:** the gates of
`CombinatorialRigidity/CLAUDE.md` *Before each commit*: a warning-free `lake build`, `lake lint`,
`blueprint/verify.sh`, `blueprint/lint.sh`, and `#print axioms` on each pin. New files get the
copyright header, a module docstring listing their statements, and a root import; every declaration
keeps its docstring.

- [x] **B1 = T1** (l.1–219 → `Pencil/Reseed.lean`; ≈290 lines; no node flips). First move
  `exists_extend_linearIndependent` (`Steer.lean` l.141–220, the section header, docstring and
  proof) verbatim to `Reseed.lean`, updating its docstring's location, and `notes/FRICTION.md`'s
  `[mirror-candidate]` entry (its *Where it bit*; T1 is its second consumer). Then
  `exists_fill_linearIndependent_hubSlotOf`, `mem_ker_toDual_flip_iff`,
  `exists_fill_cross₃_eq_smul_of_selector`, `exists_fill_linearIndependent_of_selector`,
  `LinearIndepOn.of_smul_eq` and `exists_pencilSeed_of_nondeg_of_selectors`. Placement test:
  `PlaceReseed.lean`. **Landed** 2026-09-29: `lake build`/`lake lint`/`blueprint/verify.sh`/
  `blueprint/lint.sh` all clean; `#print axioms` on `exists_pencilSeed_of_nondeg_of_selectors` and
  `exists_extend_linearIndependent` show only the three standard axioms.
- [x] **B2 = T2 + T3** (l.221–956 → new `MainComponent/GenericSteer.lean`, importing
  `…Molecule.Pencil.Steer`; ≈740 lines; greens `lem:pencil-generic-steer`, all four pins). In order:
  (MC-188) `exists_coord_linearIndependent_pencilChartPoint_of_other_nonhub`,
  `Graph.closedNbhd_eq_insert`, `exists_coord_linearIndepOn_closedNbhd_of_demoted`,
  `exists_isNondegPencilRealization_restrict_of_demoted`, `IsFin3SelectorOf.isSome_of_ncard_eq_three`,
  `pencilDotPoly`, `pencilDotPoly_eval`, `exists_isNondegPencilRealization_steer`,
  `ncard_closedNbhd_eq_three_of_demoted`. **Tidy-up:** in the steering proof, `hWF₂` is obtained but
  unused; bind it as `-`. Placement test: `PlaceSteer.lean`. **Landed** 2026-09-29: `lake build`/
  `lake lint`/`blueprint/verify.sh`/`blueprint/lint.sh` all clean; `#print axioms` on all four pinned
  declarations show only the three standard axioms.
- [ ] **B3 = Z1** (l.958–1492 → new `MainComponent/GenericEar.lean`, importing `…GenericSteer` and
  `…MainComponent.CoverageChain`; ≈535 lines; greens `lem:pencil-generic-one-ear`). In order:
  `exists_mem_perp_pair_linearIndependent`,
  `Graph.IsOpenEar.hasGenericPencilRealization_of_isNondegPencilRealization`,
  `not_linearIndependent_of_dotProduct_eq_zero_pair`, `Graph.IsOpenEar.hasGenericPencilRealization_of_one`,
  **the last without `(hnadj : ¬ G.Adj a b)`** (spike l.1339; *Architectural choices*). Placement
  test: `PlaceEar.lean`.
- [ ] **B4 = Z2** (l.1494–2135 → new `MainComponent/GenericTriangle.lean`, importing `…GenericSteer`,
  `…MainComponent.Lines` and `…MainComponent.Cut`; ≈640 lines; greens
  `lem:pencil-generic-pendant-triangle`). In order: `linearIndependent_pointJoin_triangle`,
  `not_pencilHub_of_closedEar_two`, `hasGenericPencilRealization_of_closedEar_two_of_isNondegPencilRealization`,
  `hasGenericPencilRealization_of_closedEar_two`. **Tidy-up:** the case analysis of `G`'s links
  (`hcls`) is written twice, in `not_pencilHub_of_closedEar_two` and in the extension; factor it
  into one lemma both use. Placement test: `PlaceTri.lean`.
- [ ] **The second read** of (MC-190)–(MC-192) (`notes/pencil/workbook/K-main-MC19.md`, Step MC19,
  *EARS' three claims*): a fresh read-only reader, after B4 and before the close. It checks the
  workbook prose against the landed Lean; repairs go in place, dated.
- [ ] **The close**: re-read the three nodes, headline axioms on the landed pins, the design doc,
  ROADMAP and `notes/MolecularConjecture.md`; the public surfaces stay unchanged (the PI's standing
  call: they update at Phase 40's close).

## Blockers / open questions

- **None.** Every leaf is sorry-free at the consumed signatures.

## Hand-off / next phase

**Next concrete step: B3 = Z1** (`scratch/ears/Ears.lean` l.958–1492, new
`MainComponent/GenericEar.lean`, importing `…GenericSteer` and `…MainComponent.CoverageChain`;
≈535 lines; greens `lem:pencil-generic-one-ear`). Checklist has the exact declaration order and the
dropped-`hnadj` architectural choice for the last lemma. Placement test: `PlaceEar.lean`. Then B4,
one sonnet build each, each greening one node. Then the second read of (MC-190)–(MC-192), after the
builds and before the close, then the close. REDUCE+CLOSE follows: (MC-129), the route-B assembly
from `scratch/40n-read/GenBase.lean`'s tail, with Z1's call passing one argument fewer, and both
headlines; its close closes Phase 40.

## Decisions made during this phase

- **2026-09-29 — opened design-first** from EARS' pre-build recon (opus, read-only,
  compiler-checked). It found every leaf closable at `GenBase.lean`'s signatures (l.822, l.835) and no
  shorter route: T3 is needed for the demoted ends' closed hub-neighbourhoods, and T1 to put two
  realizations in one chart. Its shortenings are that T2 covers any subgraph under a one-line
  hypothesis, one T3 serves both steps, and Z2 needs no flag and only a nonnegative triangle
  deficiency. The new claims (MC-190)–(MC-192) are in Step MC19.
- **The blueprint restatement** (this open): `lem:pencil-generic-steer` restated as (a), any subgraph,
  and (b), (MC-191)'s scope, in place of (c)'s "any finitely many polynomial conditions". The one-ear
  node drops non-adjacency. The pendant triangle's proof reads its points as independent together and
  cites the cycle's rigidity and the cut-vertex deficiency.
