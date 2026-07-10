# Phase 31 — PROSPECT round 1: simplifications + restructuring recon (work log)

**Status:** in progress (opened 2026-07-10).

Planning input: `notes/Prospect.md` (the PROSPECT survey + adjudicated
phase order); this phase is its grouping 1. Blueprint mode:
structural-edit style — no new chapter; each slice's blueprint edits
(node restates, prose sync) ride the slice's commit.

## Current state

S2 and S3 landed; the S2 rider (retention docstrings) landed alongside
S3. Next concrete step: the two recons, **R1** (speculative
restructuring) and **G2 sizing** (`Graph.exists_adjacent_degree_two_pair`
at `D = 3`) — independent of each other, dispatchable in either order.

## Work items (from `notes/Prospect.md`, grouping 1)

- [x] **S2 — rationality-conjunct fold-in.** Dropped the middle
  `(Q.coeffs : Set ℝ) ⊆ Set.range (algebraMap ℚ ℝ)` conjunct from
  `exists_generalPosition_polynomial` (`PanelHinge.lean`) and
  `exists_generalPosition4_polynomial` (`GeneralPosition4.lean`); every
  caller only ever destructured it into `_` (13 sites across
  Coupling/Theorem55/CaseI/CaseII/CaseIII/Realization.lean, 2 in
  Theorem56.lean), each reduced from a 4- to a 3-component pattern.
  Deletion-variant: `leadMinorPoly_mem_range_map` (private, its sole
  consumer) deleted outright. No blueprint node claims rationality for
  either decl's own conclusion (checked); the "rational minor/rank
  polynomial" mentions still in `molecule-modelling.tex`,
  `molecular-induction.tex`, `panel-layer.tex` are pre-existing
  genericity-device debt from Phase 30 slice (e), not this decl pair —
  left untouched, out of this slice's scope. Docstrings + one FRICTION
  entry (the `Subring.prod_mem` idiom) noted the drop. Build + `lake
  lint` clean.
- [x] **S2 rider** — one-line retention docstrings added to the
  zero-caller `d = 3` dispatch decls (`Prospect.md` S1): `theorem_55_d3`,
  `rankHypothesis_deficiency_of_theorem_55_d3`,
  `rankHypothesis_of_theorem_55_d3` (`Theorem55.lean`),
  `case_III_candidate_dispatch` (`CaseIII/Realization.lean`), and its
  sole `d = 3`-only supplier `exists_complementIso_ne_zero_of_homogeneousIncidence`
  (`RigidityMatrix/Claim612.lean`) — the confirmed-zero-caller entry
  points, not a trace of the full support chain (most of which is shared
  with the live general-`k` chain-dispatch route and so isn't dead).
- [x] **S3 — RECLASSIFIED: already formalized in Phase 20; the deferral
  claim was stale.** `Graph.circuit_induces_isTight` /
  `Graph.circuit_induces_isRigidSubgraph`
  (`Molecular/Induction/Operations.lean`) land the full tightness
  equality and `G[V(X)]`-rigid conclusion, pinned green on
  `lem:circuit-induces-rigid` in `molecular-induction.tex` since Phase
  20 — including the vertex-induced-subgraph construction
  (`Graph.inducedSpan`/`fiberSpan`). Fixed the two stale surfaces that
  still claimed deferral: `deficiency.tex`'s `lem:circuit-rigid` proof
  remark and `Deficiency.lean`'s file-header docstring, both now
  cross-referencing the landed node. No Lean work needed; verdict +
  pointers in `notes/Prospect.md` S3.
- [ ] **R1 — speculative restructuring recon** (time-boxed). Seed
  questions + deliverable shape in `notes/Prospect.md` (R1): graded
  restructuring-candidate memo, compiler-witnessed probes only where
  cheap, "no candidates" an acceptable verdict. Verdict lands here and
  in `Prospect.md`; any GO candidate becomes its own adjudicated slice
  or phase, not an in-recon refactor.
- [ ] **G2 sizing recon** — settle `Graph.exists_adjacent_degree_two_pair`
  (`Molecular/Induction/ReducibleVertex.lean`) at `D = 3`: provable by a
  smarter count, or false (making the Case-III degeneration essential)?
  Record the verdict in `notes/Prospect.md` (it gates whether the planar
  G2 phase ever opens).

## Blockers / open questions

- None at open.

## Hand-off / next phase

Next concrete commits: the two recons (*Work items*), dispatchable
independently and in either order — **R1** (speculative restructuring,
time-boxed) and **G2 sizing** (`exists_adjacent_degree_two_pair` at
`D = 3`). Either closes this phase once done (both are recon-only, no
build gating them further). At phase close: the queued PROSPECT
continuation (`notes/Prospect.md` *Hand-off*) — next up the new-math
phase (L1 Jacobs' conjecture + L2 degree-1 rank formula), then G1 field
generality (recon-first), then G3; G2 planar only on a favorable sizing
verdict from this phase.

## Decisions made during this phase

- **S2 landed** (see *Work items*): the general-position family's
  rationality conjunct is gone; the `exists_rankPolynomial_*` family
  (RELAX slice (e)) and the general-position-avoidance family (this
  slice) now share the same shape — no producer in the molecular tree
  carries a live rationality clause.
- **S3 was a docs-sync, not a build** (see *Work items*): the full KT
  Lemma 3.4 landed in Phase 20; the Phase-19 deferral note and its
  Phase-30-era survey mention were never rechecked against the
  already-green `lem:circuit-induces-rigid` node. Lesson for the
  liveness/staleness surveys this phase's tier list otherwise trusts:
  cross-check a "deferred" claim against the current blueprint dep-graph
  before scheduling its Lean work.
