# Phase 31 — PROSPECT round 1: simplifications + restructuring recon (work log)

**Status:** in progress (opened 2026-07-10).

Planning input: `notes/Prospect.md` (the PROSPECT survey + adjudicated
phase order); this phase is its grouping 1. Blueprint mode:
structural-edit style — no new chapter; each slice's blueprint edits
(node restates, prose sync) ride the slice's commit.

## Current state

S2, S3, and R1 done. Next concrete step: the **G2 sizing recon**
(`Graph.exists_adjacent_degree_two_pair` at `D = 3`) — the last open
work item; it closes the phase. One R1 output (the triangle→cycle
merge, R1-3) awaits user adjudication (*Blockers* below).

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
- [x] **R1 — speculative restructuring recon** (time-boxed; graded memo
  in `notes/Prospect.md` *R1 recon verdict*). One GO: merge the
  `|V| = 3` triangle base into the general-`m` cycle brick (R1-3, more
  KT-faithful, est. 1–2 commits — adjudication pending, *Blockers*).
  NO-GO on the Lemma-6.5/Case-III collapse and the Case-II→Case-I
  absorption (disjoint `hnoRigid` preconditions + grounded structural
  blocks); the Phase-30 nested-IH unlock is already fully banked;
  `MeetHodge.lean` metric-free is NEEDS-SPIKE, sharpening the queued G1
  recon (GL-up-to-det route; isotropic-normals risk named). Incidental:
  `Graph.minimal_kdof_reduction_full` is zero-caller with a stale
  docstring. No Lean changed.
- [ ] **G2 sizing recon** — settle `Graph.exists_adjacent_degree_two_pair`
  (`Molecular/Induction/ReducibleVertex.lean`) at `D = 3`: provable by a
  smarter count, or false (making the Case-III degeneration essential)?
  Record the verdict in `notes/Prospect.md` (it gates whether the planar
  G2 phase ever opens).

## Blockers / open questions

- **User adjudication of R1-3** (the one R1 GO): merge the `|V| = 3`
  triangle base into the cycle brick (`notes/Prospect.md` *R1 recon
  verdict*). Options: a slice inside this phase, its own follow-up
  slice, or drop. Sub-call inside it: retire the triangle stack
  (`theorem_55_triangle` / `exists_triangle_normals` / the T4 assembly)
  or retain it as worked-case exposition (the S1 precedent).
- **User adjudication of the incidental**: fix
  `Graph.minimal_kdof_reduction_full`'s stale docstring or retire the
  zero-caller decl.

## Hand-off / next phase

Next concrete commit: the **G2 sizing recon**
(`exists_adjacent_degree_two_pair` at `D = 3`, *Work items*) — the last
open item; recon-only, closes the phase once its verdict is recorded in
`notes/Prospect.md`. The R1-3 / incidental adjudications (*Blockers*)
can land before or after, at the user's call. At phase close: the
queued PROSPECT continuation (`notes/Prospect.md` *Hand-off*) — next up
the new-math phase (L1 Jacobs' conjecture + L2 degree-1 rank formula),
then G1 field generality (recon-first; R1-5's spike sharpenings feed
it), then G3; G2 planar only on a favorable sizing verdict from this
phase.

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
- **R1 verdict landed** (see *Work items*; full memo in
  `notes/Prospect.md` *R1 recon verdict*): the seed questions' two
  case-merge candidates refute on disjoint `hnoRigid` preconditions —
  the same case boundary KT draw — confirming the spine's case structure
  is source-shaped, not an artifact; the one restructuring the tier list
  missed is the triangle/cycle brick duplication (a build-order residue:
  the triangle landed 22g–h, its general-`m` generalization 23g, and the
  `|V| = 3` arm was never re-pointed).
