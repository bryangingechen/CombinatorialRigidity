# Phase 24 — the 3-D generic bar-joint rigidity matroid (work log)

**Status:** in progress (opened 2026-07-06).

## Current state

Phase opened: the forward-mode blueprint chapter
`blueprint/src/chapter/bar-joint-3d.tex` (`sec:bar-joint-3d`, 8 nodes,
all red) is the dep-graph / lemma index and live to-do list; no Lean
yet. Next concrete step: create
`CombinatorialRigidity/GenericRigidityMatroid.lean` (importing
`LinearRigidityMatroid`) and land the leaf-most pair
`def:generic-placement` + `lem:exists-generic-placement` — the
"generic for row independence" predicate and its existence at every
dimension. The existence proof is Phase 8's linear-interpolation
induction (`exists_uniform_rowIndependent_placement_dim_two`) run
against the family `{I | ∃ q, EdgeSetRowIndependent q I}`, whose
per-member witness placements are definitional (no sparsity
characterization needed); consider extracting the finite-family core
of the dim-2 lemma as a shared helper and refactoring the dim-2
statement onto it in the same commit.

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

- Naming + rank carrier to settle at the first Lean commit: the
  predicate name for "generic for row independence", and whether
  `def:genericRank` lands `ℕ`-valued (`Matroid.rk`-style) or
  `ℕ∞`-valued (`eRk`) — pick whichever the vendored `Matroid` rank API
  makes cheapest for the Cor 5.7 arithmetic (`3|V| − 6 − def(G̃)`,
  Phase 26).
- The dead-code/liveness sweep deferred from `notes/Phase23-cleanup.md`
  (*Deferred to a future dead-code / liveness sweep*) is **not**
  Phase-24 work; it lands in a later dedicated cleanup round at a
  phase boundary.

## Hand-off / next phase

Next concrete commit: the Lean for `def:generic-placement` +
`lem:exists-generic-placement` (new file, general-`d` existence via
the interpolation family argument), adding `\lean{}` pins and flipping
both nodes green in the same commit. The rest of the chapter is then
`Matroid.ofFun` plumbing + rank identities. Phase 24 unblocks Phase 26
(with Phases 23 and 25); Phase 25 is independent of this phase.

## Decisions made during this phase

(none yet beyond the up-front choices above)
