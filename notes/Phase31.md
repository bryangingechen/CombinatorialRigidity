# Phase 31 — PROSPECT round 1: simplifications + restructuring recon (work log)

**Status:** in progress (opened 2026-07-10).

Planning input: `notes/Prospect.md` (the PROSPECT survey + adjudicated
phase order); this phase is its grouping 1. Blueprint mode:
structural-edit style — no new chapter; each slice's blueprint edits
(node restates, prose sync) ride the slice's commit.

## Current state

All four work items done (S2, S3, R1, G2 — the G2 verdict: false at
`D = 3`, `K_{2,3}`; planar track dropped, `notes/Prospect.md`). Nothing
left but the **phase-close decision, which is the user's**: two
adjudications are pending (*Blockers* below — the R1-3 triangle→cycle
merge could still land as a slice inside this phase), so the phase
stays open until the user rules on them.

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
- [x] **G2 sizing recon — FALSE at `D = 3`; planar track dropped.**
  `K_{2,3}` (at `n = 2`, `bodyBarDim 2 = 3`) satisfies every hypothesis
  of `exists_adjacent_degree_two_pair` — minimal `0`-dof (`2·K_{2,3}`
  exactly `(3,3)`-sparse, `2|E| = 3(|V|−1) = 12`, so `E(G̃)` is the
  unique base), no proper rigid subgraph, `|V| = 5` — yet its degree-2
  vertices (the 3-side) are pairwise non-adjacent. Verified exhaustively
  (all 52 vertex partitions for `def = 0`; all 4095 nonempty `E(G̃)`
  subsets for sparsity; all proper induced subgraphs have `def ≥ 1`)
  against the `Deficiency.lean` definition bodies, by script. Verdict +
  drop recorded in `notes/Prospect.md` (G2 entry, *Hand-off* item 5).

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

Work items are exhausted; next is the **user's call on the two pending
adjudications** (*Blockers*: R1-3 triangle→cycle merge — in-phase slice,
follow-up, or drop; the `minimal_kdof_reduction_full` incidental), then
the **phase close** (user decision; `PHASE-BOUNDARIES.md` checklist on
the closing commit). At phase close: the queued PROSPECT continuation
(`notes/Prospect.md` *Hand-off*) — next up the new-math phase (L1
Jacobs' conjecture + L2 degree-1 rank formula), then G1 field
generality (recon-first; R1-5's spike sharpenings feed it), then G3.
G2 planar is dropped (this phase's sizing recon: false at `D = 3`).

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
- **G2 verdict landed** (see *Work items*; record in `notes/Prospect.md`
  G2 entry): `exists_adjacent_degree_two_pair` is **false** at `D = 3`
  (`K_{2,3}`), so the `6 ≤ D` hypothesis is essential, not a counting
  artifact — no planar transport of the landed Case-III chain exists,
  and the conditional planar grouping leaves the PROSPECT queue per the
  pre-adjudicated rule (`notes/Prospect.md` *Hand-off* item 5).
