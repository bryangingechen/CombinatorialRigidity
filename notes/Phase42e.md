# Phase 42e — PD-CARRIER: the setting and the flat rank in every dimension (work log)

**Status:** ✓ closed 2026-10-30 (opened the same day at the PI's word, "PD-CARRIER only
(Recommended)", design doc §1), a sub-phase of Phase 42, which stays in progress with no sub-phase
open. Forward mode, the Lean under `/coordinate-phase`: the four nodes of
`blueprint/src/chapter/pencil-d.tex` in `sec:pencil-d-induction` and `sec:pencil-d-flat` are
green, formalized as written, their Lean at every `m` (every `d ≥ 2`), in four commits with the
open and the close. Next (*Hand-off*): PD-STEPS's open goes to the PI.

## Current state

**Closed.** Formalizing 42d's proof began here, with Phase 40b–40d in `Pᵈ`: the setting
(coplanarity is linear in the heights) and the flat rank with its two corollaries. File map, one
line each:
- `Grade/ConditionLinear.lean` (imports `Grade.Configuration`): `gradeSigma` (`σ_v`),
  `gradeSigmaPerp` (`n^i`) and their lemmas, `dotPerp_range_gradeSigma` (`Π_v^⊥ = span {n^i}`),
  `pencilConfigPointGrade_eq_gradeSigma_iff`, and over an admissible picture
  `Graph.IsAdmissiblePicture.span_pencilConfigPointGrade_closedNbhd_eq_range`,
  `…finrank_span_pencilConfigPointGrade_closedNbhd_le_iff` and
  `…mem_liftingSpaceGrade_iff_finrank_span_closedNbhd_le` (`lem:pencil-d-condition-linear`).
- `Grade/Flat.lean` (imports `Grade.ZeroHeights`, `MainComponent.Bridge`):
  `Graph.finrank_span_rigidityRows_ofNormals_flat_grade`, `…_flat_le_grade` and
  `…_flat_eq_iff_grade` (`thm:pencil-d-flat-rank`);
  `Graph.finrank_liftingSpace_eq_three_add_deficiency_iff` and
  `Graph.x0AttainsGrade_of_finrank_liftingSpace_le` (`cor:pencil-d-flat-attains`);
  `Graph.x0AttainsGrade_of_deficiency_two_eq` (`cor:pencil-d-jj-flat`).

`#print axioms` at the close (`lake lean`, a scratch file) on the twelve pinned names:
`[propext, Classical.choice, Quot.sound]`, and `[propext, Quot.sound]` for `gradeSigmaPerp`.
The close re-read both sections end to end against the landed statements and found no wording
false: the nodes state `d ≥ 3`, the chapter's notation from `sec:pencil-d-induction` on, and the
Lean is stronger, holding at `d = 2` too; no statement changed.

## Architectural choices made up front

- **Scope** (the PI's, verbatim in design doc §1): PD-CARRIER only, the four nodes above.
  `rem:pencil-d-flat-class` is a remark, which the dependency graph does not draw, so it was no
  target. Its claim checks, and nothing uses it.
- **Encoding** as 42b and 42c: `m = d − 2` heights at grade `k = m + 1`, `D = screwDim (m + 1)`,
  `def_d` is `G.deficiency (m + 2)` and `def_2` is `G.deficiency 2` (`notes/Phase42b.md`,
  `notes/Phase42c.md` *Architectural choices*). Attaining is `Graph.X0AttainsGrade K m`.

## Lemma checklist

All four nodes are green, each pinned in its section with its Lean names; the chapter is the
index (forward mode), and the file map is under *Current state*.

## Blockers / open questions

- None. PD-STEPS opens at the PI's word (*Hand-off*).

## Hand-off / next phase

Phase 42 stays in progress with no sub-phase open. The next step is **putting PD-STEPS's open to
the PI** (design doc §3): Phase 40e–40m's steps in `Pᵈ`, the 28 red nodes of `-cut`, `-contract`,
`-splitoff`, `-short`, `-long` and `-ear-deficiency`, with the question §3 leaves to that open:
whether `thm:pencil-d-splitoff` and `thm:pencil-d-open-ear-deficiency` (with
`lem:pencil-d-polygon-ear`), which no coverage step consumes, are formalized (answered at 42f's
open: cut, design doc §1). What 42e hands it, all at every `m`, so no `1 ≤ m` side condition
reaches a consumer:
- `σ_v` and `Π_v` exposed: `gradeSigma h` and its range, which `def:pencil-d-ear-data` and
  `lem:pencil-d-planes-meet` read, with `pencilConfigPointGrade_eq_gradeSigma_iff` and
  `…span_pencilConfigPointGrade_closedNbhd_eq_range` reading a closed neighbourhood through them.
- `Graph.x0AttainsGrade_of_deficiency_two_eq`, the graphs with `def_2 = def_d`, which
  `cor:pencil-d-contract-rigid` (PD-STEPS) and `thm:pencil-d-coverage` (PD-COVERAGE) consume.
- The flat rank `…_flat_grade`. No node outside `sec:pencil-d-flat` `\uses` it; `-short` computes
  ranks with joins as its proof's second paragraph does, in prose, which needed no Lean here.

**Deferred from 42e, where it lands** (design doc §3, *Deferred to them from PD-CARRIER*;
FRICTION): `gradeSigma` duplicates the map `finrank_span_pencilConfigPointGrade_closedNbhd_le`
builds inline, and ConditionLinear's local projection duplicates the private `pictureProj`, both in
`Grade/Configuration.lean`; the fold lands with the next commit that edits `Configuration.lean` or
`Grade/Carrier.lean`. The deferrals from 42b and 42c (design doc §3) are unchanged: 42e edited no
file they name.

## Decisions made during this phase

- **The open** (the PI, 2026-10-30; verbatim in design doc §1): 42e opens as PD-CARRIER only; the
  other layers are mapped by section in design doc §3, no letters minted.
- **The open's consistency read:** each proof routes through the argument its statement claims, on
  42b's carrier. The `d = 3` one-normal route does not generalize and the projection route does;
  Lean's `L(q)` holds heights vanishing off `V(G)`, so the "in particular" takes that hypothesis per
  height (`hs`), as at `d = 3`, with no statement change.
- **The pre-build recon** (spikes in `scratch/42e/`): `σ_v` is a `def` and `Π_v` its `range`, as
  PD-STEPS reads both; every `m`, as no proof uses `d ≥ 3`; two new files, `pictureProj` private.
  The three flat-rank bridges hold: `rw` matches `k := 0 + 1` against `k := 1` once the normals
  are rewritten.
- **The build** (one commit, the recon's spikes copied): the condition-linear proof gained
  `\uses{lem:pencil-d-config-realization}`, an edge, not a statement change.
- **The close:** the duplication deferred (the coordinator's call: the fold rebuilds the `Grade/`
  stack). No `main_results` row: an intermediate close adds none (design doc §3, PD-HEAD).
