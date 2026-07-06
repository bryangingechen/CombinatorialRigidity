# Phase 24 — the 3-D generic bar-joint rigidity matroid (work log)

**Status:** in progress (opened 2026-07-06).

## Current state

The matroid + independence + placement-independence trio is landed:
`CombinatorialRigidity/GenericRigidityMatroid.lean` now also defines
`SimpleGraph.genericRigidityMatroid V d` (`linearRigidityMatroid` at a
`Classical.choose`-picked generic placement) and proves
`genericRigidityMatroid_indep_iff` (independent iff row-independent at
*some* placement) and `linearRigidityMatroid_eq_genericRigidityMatroid`
(placement independence, via `Matroid.ext_indep`), matching
`LinearRigidityMatroid.lean`'s `linearRigidityMatroid_eq_rigidityMatroid`
proof shape. All five nodes so far
(`def:generic-placement`/`lem:exists-generic-placement`/
`def:genericRigidityMatroid`/`lem:genericRigidityMatroid-indep-iff`/
`lem:linearRigidityMatroid-eq-genericRigidityMatroid`) are green
(`\lean{}` + `\leanok`). Next concrete step: the dimension-two
reconciliation `lem:genericRigidityMatroid-two-eq-rigidityMatroid`
(`genericRigidityMatroid V 2 = SimpleGraph.rigidityMatroid V`, both
independence predicates already say "row-independent at some
placement" per `genericRigidityMatroid_indep_iff` and
`rigidityMatroid_indep_iff_edgeSetRowIndependent`), then the rank
function (`def:genericRank`, `lem:genericRank-eq-finrank-span`), in the
chapter's node order.

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

Next concrete commit: `lem:genericRigidityMatroid-two-eq-rigidityMatroid`
— `genericRigidityMatroid V 2 = SimpleGraph.rigidityMatroid V`
(`RigidityMatroid.lean`'s dim-2 combinatorial planar rigidity matroid),
via `Matroid.ext_indep`: both matroids have ground set
`(⊤ : SimpleGraph V).edgeSet`, and both independence predicates already
say "row-independent at some placement"
(`genericRigidityMatroid_indep_iff` from this commit,
`rigidityMatroid_indep_iff_edgeSetRowIndependent` from
`MatroidIdentification.lean`) — so the two `Indep` predicates should
line up directly, modulo the `Subtype.val ⁻¹' J` image-factoring
boilerplate already used twice in `LinearRigidityMatroid.lean`. After
that, the chapter closes with the rank function: `def:genericRank`
(`r_d(H) := (genericRigidityMatroid V d).rk (E(H))` or the vendored
`Matroid`'s equivalent rank-of-a-set API — check what
`linearRigidityMatroid_eq_rigidityMatroid`/Phase 8 exposed, since no
rank lemma has landed yet in this project) and
`lem:genericRank-eq-finrank-span` (the row-space form, via
`linearRigidityMatroid_eq_genericRigidityMatroid` +
`linearRigidityMatroid_indep_iff_edgeSetRowIndependent`). Phase 24
unblocks Phase 26 (with Phases 23 and 25); Phase 25 is independent of
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
