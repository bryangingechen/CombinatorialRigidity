# Phase 42l — PD-HEAD: nondegenerate realizations and their lifts in every dimension (work log)

**Status:** ✓ closed 2026-11-04 (opened the same day at the PI's word, "Nondegenerate + lift only",
design doc §1), the first sub-phase of Phase 42's last layer, PD-HEAD; Phase 42 stays in progress
with no sub-phase open. Forward mode, the Lean under `/coordinate-phase`: the ten nodes of
`blueprint/src/chapter/pencil-d.tex`'s `sec:pencil-d-nondegenerate` and `sec:pencil-d-lift` are
green, as the chapter states them, in seven commits with the open, the recon and the close. Three
route differences wait for the cleanup after Phase 42 (`notes/Cleanup42.md` R-20, R-21, R-23); R-22
is aligned at the PI's word. Next: `-generic`, opened as 42m (`notes/Phase42m.md`).

## Current state

**Closed.** PD-HEAD's first half: nondegenerate pencil realizations in every dimension, and the
lifts of those of dimension three. File map, one line each (namespace
`CombinatorialRigidity.Molecular`; `r` the number of new coordinates, the chapter's `m = d − 3`):
- `Grade/Nondegenerate.lean` (imports `Grade.Embedding`; build 1): `PencilNondegConditions`,
  `IsNondegPencilPlaneRealization`, `GradedPencilNondegFeasible`,
  `HasGradedGenericPencilRealization` (`def:pencil-d-nondegenerate`); the polarity at `d = 3`,
  `isNondegPencilPlaneRealization_two_iff` and its kin (`-three`); `PencilNondegConditions.of_map`,
  `.map`, `IsNondegPencilPlaneRealization.map_gradeEmbed` (`-maps`).
- `Grade/Feasible.lean` (imports `Grade.Nondegenerate`, `Pencil.Steer`, the mirror
  `Mathlib.Algebra.MvPolynomial.Monad`; build 2): the API `IsPolyFun`, `IsZariskiOpen`;
  `exists_rowsMap_two`/`_three`, `exists_injOn_finrank_iInf_map_le`,
  `gradedPencilNondegFeasible_iff` (`-feasible`).
- `Grade/Lift.lean` (imports `Grade.Feasible`; build 3): `PencilSeed.ofGamma`, `steerPoint`,
  `steerNormal`, `steerSet`, `HoldsGenerally` (`lem:pencil-d-steer`); `liftVec`, `liftSpace`,
  `liftMaps`, `liftNormal`, `liftSubspace` (`def:pencil-d-lift`);
  `IsNondegPencilPlaneRealization.lift` and the transport lemmas (`-lift-realization`);
  `LiftAttains` (`-lift-attains`).
- `Grade/LiftWitness.lean` (imports `Grade.Lift`; build 4): `liftSpaceTilde`, `liftMatrixPoly`,
  `liftAttains_of_least`, `liftAttains_of_holdsGenerally` (`-lift-one-witness`); `lift_transfer`
  (`-lift-transfer`).

`#print axioms` at the close (`lake lean`, a scratch file, after `lake build
...Grade.LiftWitness`) on all 140 declarations of the four files, the 47 pins among them:
within `[propext, Classical.choice, Quot.sound]` on all (127 all three, 10 without
`Classical.choice`, 3 `propext` alone); no `sorryAx`. The close re-read the ten nodes end to end
against the landed statements and restated one, the parametrization (*Decisions made*).

## Architectural choices made up front

- **Scope** (the PI's, verbatim in design doc §1): the ten nodes as the chapter states them;
  `-generic` (eleven nodes) is PD-HEAD's other half, no letter, and its close is Phase 42's.
- **Encoding** as 42b–42k: grade `k = d − 1`, Lean's `m = d − 2`; the lift's `d − 3` new
  coordinates are inserted before the last one, as `gradeEmbed` inserts its zeros.

## Lemma checklist

All ten nodes are green, each pinned in its section with its Lean names; the chapter is the index
(forward mode), and the file map is under *Current state*.

## Blockers / open questions

- None. `-generic` opens at the PI's word (*Hand-off*).

## Hand-off / next phase

Phase 42 stays in progress with no sub-phase open. The next step is **putting `-generic`'s open to
the PI** (design doc §3), no letter minted until it opens (answered at 42m's open: all eleven,
design doc §1; `notes/Phase42m.md`): the eleven red nodes of `pencil-d.tex`'s
`sec:pencil-d-generic`, from `lem:pencil-d-lift-small` (the first red node) to
`thm:pencil-d-generic` and the headline `cor:pencil-d-conditioned-pair`. Its close is Phase 42's,
where Tier 0's `main_results` row is decided (design doc §3). What 42l hands on:
- **The ten nodes' Lean** (*Current state*); ten of `-generic`'s eleven nodes use one of them.
- **The remark after `def:pencil-d-lift-attains`** (an attaining general lift gives a generic
  realization) has no node: it is `IsNondegPencilPlaneRealization.lift` with
  `PanelHingeFramework.span_rigidityRows_toPatchedBodyHinge` at a realization with `Q ≠ 0`, and it
  lands with `thm:pencil-d-generic`, which cites it.
- **The parametrization's places** (R-22): `lem:pencil-d-ear-extend`'s proof reads the steer
  lemma's empty places; its own `Γ_L` keeps the members-first form, for its recon to match to a
  selector.
- **The standing rule** (design doc §3): `-generic`'s recon and builds add a row to
  `notes/Cleanup42.md` §2 where their Lean departs from the chapter's proof. Open: R-3 to R-5, R-9
  to R-12, R-14 to R-21, R-23; aligned: R-1, R-2, R-7, R-8, R-13, R-22; R-6 no departure.

**Deferred, where it lands** (design doc §3, *Deferred to `-generic` and after from 42l*;
FRICTION's `[open]` 42l entry): the six `dotPerp` lemmas of `Grade/Feasible.lean` to
`Grade/Realization.lean`, with the next commit that edits it (and 42k's `dotPerp_map_eq`); at a
cleanup round, the mirror candidate `finrank_map_of_injOn`. No build edited a file that carries a
home debt of 42b–42k, so none rode; those stay as `notes/Phase42k.md` *Hand-off* lists them.

## Decisions made during this phase

- **The close:** the re-read found every hypothesis and conclusion of the ten matching its pin, and
  restated only the parametrization (the PI's, below). The Lean is stronger only here: three takes
  no `n_v ≠ 0`; maps holds on any `K^N` with no `b_v ≠ 0`, `b_v ∈ Π_v` or dimension, the embedding
  from any grade `k' ≥ 1`; the parametrization needs no simplicity, only its assignments (the
  selectors); one lift and the restriction take neither simplicity nor feasibility. Feasibility
  takes `[Finite α]`; transfer's open set is a polynomial's in the maps' coordinates.
- **The recon's verdicts** (design pass): all ten spiked complete on the landed carrier, reusing the
  `d = 3` polarity, chart (`exists_pencilSeed_of_nondeg_of_selectors`), `cross₃Poly`, polynomial
  section and rank polynomial; the lift's spaces are forms on `Π⁰_v` (`liftSpace`) and on `K⁴`
  (`liftSpaceTilde`, `= ker A(b⁰)`); "general" is `HoldsGenerally`.
- **The routes** (`notes/Cleanup42.md`): feasibility by forms vanishing on the subspaces, no quadric
  (R-20); one lift through the polynomial section (R-21); transfer's open set by the rank polynomial
  at each `λ` (R-23); all open. The chart's six auxiliary vectors (R-22): aligned at the close.
- **PI, 2026-11-04 (42l's open):** the PI answered "Nondegenerate + lift only", whose option read:
  "Open on the 10 nodes of -nondegenerate and -lift (roughly 3–5 builds, my estimate). The 11
  generic nodes and the headline would wait for a later sub-phase." The question as put, the other
  options and a note on them: design doc §1.
- **PI, 2026-11-04 (42l's close, R-22):** on `lem:pencil-d-steer`'s five auxiliary vectors, where
  its Lean has six, the PI answered, verbatim: "Yes, let's make it say six at the close. I guess we
  should make the wording clear that there's some flexibility in the proof here and we decided to
  go with six in the formalization even though five actually suffice." Design doc §1.
- **R-22, as landed** (not the PI's text): six auxiliary vectors at every body, the `i`-th of the
  first (last) three at an empty place of the closed hub-neighbourhood's (neighbourhood's)
  assignment; a formalization note after the proof says that five suffice and the formalization
  takes six.
- **The open's question, checked** (design doc §1), and its consistency read: all ten PASS, their
  18 outside dependencies green.
