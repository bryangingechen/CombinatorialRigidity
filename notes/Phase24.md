# Phase 24 — the 3-D generic bar-joint rigidity matroid (work log)

**Status:** ✓ complete (opened and closed 2026-07-06).

## Current state

Closed. All eight nodes of the chapter
`blueprint/src/chapter/bar-joint-3d.tex` (`sec:bar-joint-3d`) are green
and the Lean lives in `CombinatorialRigidity/GenericRigidityMatroid.lean`
(`SimpleGraph` namespace, dimension-general, read at `d = 3` by
Phase 26): `IsGenericPlacement` + `exists_isGenericPlacement`,
`genericRigidityMatroid` with `genericRigidityMatroid_indep_iff` /
`linearRigidityMatroid_eq_genericRigidityMatroid` /
`genericRigidityMatroid_two_eq_rigidityMatroid` (the dim-2
reconciliation), and `genericRank` + `genericRank_eq_finrank_span` (the
rigidity-row-span form, via Phase 14's
`Matroid.Rep.finrank_span_image_eq_rk`). The scope guard held: linear
matroid only, no combinatorial/Laman-3D characterization (open per KT
§7). Phase-close checklist run 2026-07-06 (ROADMAP §24 is the
one-paragraph summary; blueprint-chapter re-read clean, no accreted
formalization asides; exposition ledger records the no-entry judgment
— reuse-heavy phase, no KT-math crux).

## Hand-off / next phase

Phase 24 unblocks Phase 26 (with Phases 23 and 25); **Phase 26 now
gates only on Phase 25**. Next concrete commit: open Phase 25
(projective invariance + the molecule modelling equivalence) per
`notes/MolecularConjecture.md` *Opening the next phase* — a separate
decision in a fresh session, not bundled here. Still open elsewhere: the
molecular-layer dead-code/liveness sweep deferred from
`notes/Phase23-cleanup.md` (a future cleanup round, not Phase-25/26
work), and the possible shared finite-family-perturbation helper
(*Decisions made* below).

## Decisions made during this phase

- **Dimension-general Lean, `d = 3` the consumed instance.** Everything
  stated over `{d : ℕ}` (Phase 8's `linearRigidityMatroid` already is);
  Phase 26 reads it at `d = 3`.
- **New top-level file `GenericRigidityMatroid.lean`**, beside
  `LinearRigidityMatroid.lean`, not under `Molecular/` — a
  bar-joint/`Framework`-layer object. Non-`module` (its import
  `LinearRigidityMatroid.lean` is non-`module`, `notes/PERFORMANCE.md`).
- **`genericRigidityMatroid` fixes its placement via `Classical.choose`
  on `exists_isGenericPlacement`** — a plain `Matroid (Sym2 V)`, no
  placement argument to thread; the identification proofs reproduce
  Phase 8's `Matroid.ext_indep` shape verbatim.
- **Rank carrier: `ℕ`-valued `Matroid.rk`** (not `ℕ∞` `eRk`) — matches
  every existing project rank usage and reuses Phase 14's
  `Matroid.Rep.finrank_span_image_eq_rk` bridge directly.
- **`genericRank_eq_finrank_span` reuses the Phase-14 representation
  bridge** (vendored `Matroid.repOfFun` + `Matroid.ofFun_finite`) rather
  than re-deriving a `finrank`/rank identity; only `Set.indicator`/image
  bookkeeping was new. Imports `BodyBar/KFrame.lean` for it.
- **Deferred: shared finite-family-perturbation helper.**
  `exists_isGenericPlacement`'s induction is structurally identical to
  Phase 8's `exists_uniform_rowIndependent_placement_dim_two`; a shared
  core would move the affine-path `Matrix/Rank` import upstream (e.g.
  onto `RigidityMatroid.lean`) — an import-graph change to weigh against
  a build-time measurement, not a same-commit refactor. Possible future
  follow-up, not blocking.
