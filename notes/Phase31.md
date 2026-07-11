# Phase 31 — PROSPECT round 1: simplifications + restructuring recon (work log)

**Status:** ✓ complete (opened and closed 2026-07-10).

Planning input: `notes/Prospect.md` (the PROSPECT survey + adjudicated
phase order); this phase was its grouping 1. Structural-edit style — no
new blueprint chapter; each slice's blueprint edits rode its commit.
Headline statements unchanged; all 11 `formalization.yaml` headline
results re-verified at the three standard axioms at close.

## Hand-off / next phase

The PROSPECT continuation queue (`notes/Prospect.md` *Hand-off*;
ROADMAP *Queued post-program phases*): next up the **new-math phase**
(L1 Jacobs' conjecture + L2 degree-1 rank formula), then G1 field
generality (recon-first; R1-5's spike sharpenings feed it), then G3
generic lift. G2 planar is dropped (this phase's sizing recon: false at
`D = 3`). Its opening commit mints the next phase number per
`PHASE-BOUNDARIES.md` and seeds `notes/PhaseN.md` from the Prospect
entries.

## Work items (all landed; one-line records, detail in `notes/Prospect.md`)

- [x] **S2** — dropped the everywhere-discarded rationality conjunct
  from `exists_generalPosition_polynomial` /
  `exists_generalPosition4_polynomial` (15 caller sites reduced 4→3
  components; private `leadMinorPoly_mem_range_map` deleted).
- [x] **S2 rider** — retention docstrings on the zero-caller `d = 3`
  dispatch entry points (`theorem_55_d3` family,
  `case_III_candidate_dispatch`,
  `exists_complementIso_ne_zero_of_homogeneousIncidence`), per the S1
  adjudication (kept as worked-case exposition).
- [x] **S3** — reclassified: KT Lemma 3.4's tightness equality was
  already formalized in Phase 20 (`Graph.circuit_induces_isTight` /
  `circuit_induces_isRigidSubgraph`); fixed the stale deferral remarks
  in `deficiency.tex` + `Deficiency.lean`.
- [x] **R1** — graded restructuring memo (`notes/Prospect.md` *R1 recon
  verdict*): one GO (R1-3, executed below), NO-GOs on the case merges
  (disjoint `hnoRigid` preconditions — the spine's case structure is
  source-shaped), R1-4 already banked, R1-5 → NEEDS-SPIKE feeding G1.
- [x] **R1-3 slice** — merged the `|V| = 3` triangle base into the
  general-`m` cycle brick: `Graph.CycleData.ofCardThree`
  (`Molecular/Induction/Operations.lean`) packages the triangle as
  `3`-cycle data; `cycle_realization`'s unused `_hk1`/`_hV4` binders
  dropped; `case_III_hsplit_producer_all_k`'s triangle arm rewired;
  triangle stack retained as worked-case exposition (adjudication (2)).
  Blueprint: `lem:case-III` reroutes through `lem:cycle-realization` +
  `lem:triangle-third-edge` + `def:cycle-data`;
  `lem:triangle-realization` kept off-path with an exposition fmlnote.
- [x] **G2 sizing recon** — `exists_adjacent_degree_two_pair` is
  **false at `D = 3`**: `K_{2,3}` satisfies every hypothesis (verified
  exhaustively by script against the `Deficiency.lean` bodies) with
  pairwise non-adjacent degree-2 vertices. Planar track dropped.

## Decisions made during this phase

- **S2 landed:** no producer in the molecular tree carries a live
  rationality clause (completes the RELAX slice-(e) sweep).
- **S3 was a docs-sync, not a build.** Lesson (also in the Prospect
  survey record): cross-check a "deferred" claim against the current
  blueprint dep-graph before scheduling its Lean work.
- **R1 verdict:** the two case-merge candidates refute on disjoint
  `hnoRigid` preconditions; the one restructuring the tier list missed
  (triangle/cycle duplication) was a build-order residue (triangle
  landed 22g–h, its generalization 23g, never re-pointed).
- **G2 verdict:** the `6 ≤ D` hypothesis is essential, not a counting
  artifact; a planar phase would mean the JJ pin-collinear route — a
  new program, not a Case-III adaptation.
- **R1 incidental adjudicated: retire** `Graph.minimal_kdof_reduction_full`
  (zero-caller, stale docstring, no blueprint pin; superseded by
  `minimal_kdof_reduction_all_k` since Phase 22i).
- **R1-3 adjudicated + landed:** execute the merge as a Phase 31 slice;
  retain the triangle stack (`hasGenericFullRankRealization_of_triangle`
  / `theorem_55_triangle` / `exists_triangle_normals`) as exposition
  with retention docstrings (the S1 precedent). Friction: building
  `CycleData` data via `obtain` blocks `.m`-projection reduction →
  TACTICS-QUIRKS § 79.
- **Phase close (2026-07-10):** touched-chapter re-read collapsed the
  R1-3 reshape narration in `case-iii.tex` to present-shape prose;
  exposition ledger's triangle-floor entry updated to the merged route
  (no new ledger entries); README / home_page / intro.tex unchanged
  (arc-level summaries unaffected by an internals-only phase).
