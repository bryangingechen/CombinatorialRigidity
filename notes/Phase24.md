# Phase 24 — the 3-D generic bar-joint rigidity matroid (work log)

**Status:** in progress (opened 2026-07-06).

## Current state

All eight chapter nodes are now green, including the rank function
(`def:genericRank`, `lem:genericRank-eq-finrank-span`) that closes
`sec:bar-joint-3d`. `SimpleGraph.genericRank H d := (genericRigidityMatroid V
d).rk H.edgeSet` (`ℕ`-valued `Matroid.rk`, per the *Blockers* resolution
below), and `genericRank_eq_finrank_span` identifies it with the `ℝ`-dimension
of the span of `H`'s rigidity rows at any generic placement, reusing Phase 14's
`Matroid.Rep.finrank_span_image_eq_rk` (`BodyBar/KFrame.lean`) against the
vendored `Matroid.repOfFun`/`Matroid.ofFun_finite` representation API.

**The chapter is content-complete; the phase is not closed.** The next commit
is the `PHASE-BOUNDARIES.md` phase-close checklist (ROADMAP row flip +
re-thin, user-facing status-surface sync, blueprint re-read, project-
organization review) — left to the coordinator's own dispatch, not bundled
into this commit.

## Architectural choices made up front

- **Dimension-general Lean, `d = 3` the consumed instance.** Phase 8's
  `linearRigidityRow` / `linearRigidityMatroid` /
  `linearRigidityMatroid_indep_iff_edgeSetRowIndependent` are already
  stated over `{d : ℕ}`; only its uniform-placement lemma and matroid
  identification are dim-2-pinned. Phase 24 states everything at
  general `d`; Phase 26 reads it at `d = 3`. (Program-doc reuse map:
  Phase 4 `Framework.lean` + Phase 8 `Matroid.ofFun` linear framing.)
- **Scope guard (from `notes/MolecularConjecture.md`):** this phase
  packages the *linear* generic rigidity matroid only — **no
  combinatorial/Laman-3D characterization** (open per KT §7). If a
  step seems to need one, stop and re-read the program doc.
- **New top-level file**
  `CombinatorialRigidity/GenericRigidityMatroid.lean` (`SimpleGraph`
  namespace, beside `LinearRigidityMatroid.lean`), not under
  `Molecular/` — the matroid is a bar-joint/`Framework`-layer object;
  Phases 25–26 connect it to the molecular layer.

## Lemma checklist

The blueprint chapter (`sec:bar-joint-3d`) is the authoritative index
(forward mode; the dep-graph is the to-do list). All eight nodes are
green: `def:generic-placement` → `lem:exists-generic-placement` →
`def:genericRigidityMatroid` → `lem:genericRigidityMatroid-indep-iff`
→ `lem:linearRigidityMatroid-eq-genericRigidityMatroid` →
`lem:genericRigidityMatroid-two-eq-rigidityMatroid` →
`def:genericRank` → `lem:genericRank-eq-finrank-span`.

## Blockers / open questions

None open. The rank-carrier question is resolved (see *Decisions
made*). The dead-code/liveness sweep deferred from
`notes/Phase23-cleanup.md` (*Deferred to a future dead-code /
liveness sweep*) is **not** Phase-24 work; it lands in a later
dedicated cleanup round at a phase boundary.

## Hand-off / next phase

The chapter is content-complete and green end-to-end. Next concrete
commit: the `PHASE-BOUNDARIES.md` *When this commit closes a phase*
checklist — flip + re-thin the ROADMAP §24 row (currently still ◐,
deliberately left for the closing commit), sync the user-facing status
surfaces, the end-to-end blueprint-chapter re-read +
`notes/BlueprintExposition.md` write-up, and the project-organization
review. Phase 24 unblocks Phase 26 (with Phases 23 and 25); Phase 25
is independent of this phase.

## Decisions made during this phase

- **`genericRigidityMatroid` fixes its generic placement via
  `Classical.choose` on `exists_isGenericPlacement`,** not a
  `variable`/hypothesis-carried `p`. This makes the matroid a plain
  `Matroid (Sym2 V)` (no placement argument to thread), matching the
  blueprint's "fix, by the existence lemma, a placement" phrasing;
  `genericRigidityMatroid_indep_iff` and
  `linearRigidityMatroid_eq_genericRigidityMatroid` reproduce the exact
  `Matroid.ext_indep` proof shape of Phase 8's
  `linearRigidityMatroid_eq_rigidityMatroid` (ground-set equality +
  independence-set identification via the `Subtype.val ⁻¹' J` image
  factoring), so no new proof technique was needed.
- **New file `GenericRigidityMatroid.lean` is non-`module`.** It
  imports `LinearRigidityMatroid.lean`, itself non-`module` (blocked on
  `apnelson1/Matroid`'s `Matroid.Representation.Map`,
  `notes/PERFORMANCE.md`), and a `module` file cannot import a
  non-`module` one (`LEAN-OPS.md` *Module-system conversion*). Plain
  `import`, no `public section`, matching `LinearRigidityMatroid.lean`'s
  own style.
- **Rank carrier: `ℕ`-valued `Matroid.rk`,** resolving the phase-open
  *Blockers* question. `genericRank H d := (genericRigidityMatroid V
  d).rk H.edgeSet`, matching every existing rank usage in the project
  (`Deficiency.lean`'s `M(G̃)`, the KFrame/TreePacking/TayTheorem
  cycle-matroid bounds) and, decisively, the exact shape of Phase 14's
  reusable bridge `Matroid.Rep.finrank_span_image_eq_rk : finrank K
  (span K (v '' Y)) = M.rk Y` — an `ℕ∞`-valued `eRk` carrier would have
  needed a fresh `finrank`/`eRk` bridge lemma instead of reuse.
- **`genericRank_eq_finrank_span` reuses Phase 14's representation
  bridge rather than re-deriving it.** `genericRigidityMatroid V d =
  linearRigidityMatroid V d p = Matroid.ofFun ℝ (⊤:SimpleGraph
  V).edgeSet (linearRigidityRow p)` (Phase 8); packaging
  `linearRigidityRow p` as a representation via the vendored
  `Matroid.repOfFun` and feeding it to `Matroid.Rep.
  finrank_span_image_eq_rk` gives the rank–finrank identity directly,
  needing only a `Matroid.ofFun_finite` `RankFinite` instance and a
  `Set.indicator`/image bookkeeping step (`E(H) ⊆ E(K_V)`,
  `linearRigidityRow` restricting to `rigidityRow` there) to match the
  chapter's `(⊤).rigidityRow p`-indexed statement. No new proof
  technique; imports `BodyBar/KFrame.lean` for the reused lemma.
- **Deferred the shared finite-family-perturbation helper extraction**
  flagged in the phase-open hand-off. `exists_isGenericPlacement`'s
  induction is structurally identical to
  `exists_uniform_rowIndependent_placement_dim_two`'s (same
  interpolation-along-a-line argument; the only difference is where the
  per-member witness placement comes from — the sparsity bridge there,
  the defining `∃ q` directly here). A shared core would need to live
  upstream of `LinearRigidityMatroid.lean` (e.g. `RigidityMatroid.lean`)
  to be callable from both, which would pull the
  `Mathlib/LinearAlgebra/Matrix/Rank.lean` affine-path import onto a
  much-more-widely-imported file — a real import-graph change to weigh
  against a build-time measurement, not a same-commit refactor of an
  already-shipped Phase-8 proof. Left as a possible future follow-up,
  not blocking.
