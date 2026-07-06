# Phase 24 — the 3-D generic bar-joint rigidity matroid (work log)

**Status:** in progress (opened 2026-07-06).

## Current state

Six nodes are now green: `def:generic-placement`, `lem:exists-generic-placement`,
`def:genericRigidityMatroid`, `lem:genericRigidityMatroid-indep-iff`,
`lem:linearRigidityMatroid-eq-genericRigidityMatroid`, and
`lem:genericRigidityMatroid-two-eq-rigidityMatroid` (the dimension-two
reconciliation, landed in this commit: `genericRigidityMatroid V 2 =
SimpleGraph.rigidityMatroid V`). Both independence predicates already
say "row-independent at some placement" per `genericRigidityMatroid_indep_iff`
and `rigidityMatroid_indep_iff_edgeSetRowIndependent`, so the two matroids are
equal by `Matroid.ext_indep`.

Next concrete step: the rank function (`def:genericRank`, 
`lem:genericRank-eq-finrank-span`), completing the chapter.

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
(forward mode; the dep-graph is the to-do list). Node order ≈ build
order: `def:generic-placement` → `lem:exists-generic-placement` →
`def:genericRigidityMatroid` → `lem:genericRigidityMatroid-indep-iff`
→ `lem:linearRigidityMatroid-eq-genericRigidityMatroid` →
`lem:genericRigidityMatroid-two-eq-rigidityMatroid` →
`def:genericRank` → `lem:genericRank-eq-finrank-span`.

## Blockers / open questions

- Rank carrier still open (naming settled at the phase-open commit:
  `IsGenericPlacement`): whether `def:genericRank` lands `ℕ`-valued
  (`Matroid.rk`-style) or `ℕ∞`-valued (`eRk`) — pick whichever the
  vendored `Matroid` rank API makes cheapest for the Cor 5.7 arithmetic
  (`3|V| − 6 − def(G̃)`, Phase 26).
- The dead-code/liveness sweep deferred from `notes/Phase23-cleanup.md`
  (*Deferred to a future dead-code / liveness sweep*) is **not**
  Phase-24 work; it lands in a later dedicated cleanup round at a
  phase boundary.

## Hand-off / next phase

Landed: `lem:genericRigidityMatroid-two-eq-rigidityMatroid`
(this commit; see *Current state*).

Next concrete commit: the rank function (`def:genericRank`, 
`lem:genericRank-eq-finrank-span`), completing the chapter. The rank function
should follow the pattern of Phase 8's `linearRigidityMatroid_eq_rigidityMatroid`
(check what rank API was exposed there, since no rank lemma has landed yet in
this project). `lem:genericRank-eq-finrank-span` proves the row-space form via
`linearRigidityMatroid_eq_genericRigidityMatroid` +
`linearRigidityMatroid_indep_iff_edgeSetRowIndependent`.
Phase 24 unblocks Phase 26 (with Phases 23 and 25); Phase 25 is independent of
this phase.

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
