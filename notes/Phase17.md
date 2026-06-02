# Phase 17 — Grassmann–Cayley extensor algebra; Lemma 2.1 (work log)

**Status:** in progress (opening commit; chapter dep-graph is all red).

This phase opens the **molecular-conjecture program** (Phases 17–26).
The program-level plan — target, source, five-strata architecture,
phase breakdown, reuse map, risk register — lives in
`notes/MolecularConjecture.md`; read that first. This file is the
Phase-17 work log only.

## Current state

Phase 17 is open: `notes/Phase17.md` (this file), the forward-mode
chapter `blueprint/src/chapter/molecular.tex` (red dep-graph = to-do
list), and the user-facing status surfaces are all in place. **No Lean
has landed yet** — `CombinatorialRigidity/Molecular/` does not exist.
The next concrete commit is the leaf-most red node: the homogeneous
coordinatization `p ↦ (p, 1)` and the affine-independence ↔ nonzero
top-extensor fact (`def:homogeneous-coords`, `lem:affine-indep-iff`),
which has no Phase-17 dependencies and is needed by everything else in
§2.1.

## Scope (Phase 17 only)

Grassmann–Cayley / extensor algebra (Katoh–Tanigawa 2011 §2.1), the
first of the program's five strata. All new linear algebra; nothing
reused from Phases 1–16 except the mirror directory
`CombinatorialRigidity/Mathlib/` for upstream-eligible exterior-algebra
facts. The load-bearing target is **Lemma 2.1**; everything Case III
(Phase 22/23) bottoms out here.

## Architectural choices made up front

- **Symbolic-first, coordinatize as a bridge.** The user chose the full
  symbolic Grassmann–Cayley algebra over a coordinatized-minors-only
  treatment. KT work coordinatized, so build the symbolic extensor
  layer on mathlib's `ExteriorAlgebra` (`⋀[R] M`) first, then land a
  coordinatized Plücker bridge (the `j×j`-minor vector) early so the
  downstream phases (18, 22, 23) can stay concrete. See
  `notes/MolecularConjecture.md` risk register item 1.
- **Carrier for points.** Extensors live in `⋀ʲ ℝ^(d+1)`; affine points
  `p : Fin d → ℝ` (or `EuclideanSpace ℝ (Fin d)`, matching Phase 4's
  `Framework V d`) homogenize to `(p, 1) : Fin (d+1) → ℝ`. Decide the
  concrete carrier when the first Lean lands; keep it compatible with
  Phase 4's framework type so Phase 18/24 reuse is frictionless.
- **KT sign convention.** The Plücker coordinate vector uses KT's sign
  `(−1)^(1+Σ iⱼ)` (KT §2.1). Reproduce faithfully — it feeds Lemma 2.1.
  Carry it in the coordinatized bridge, not the symbolic layer.

## Lemma checklist

Forward-mode: the authoritative dep-graph is
`blueprint/src/chapter/molecular.tex`. This list mirrors its §2.1 nodes
in intended dependency order; flip each `\leanok` as the Lean lands.

- [ ] `def:homogeneous-coords` — homogeneous coordinatization `p ↦ (p,1)`.
- [ ] `lem:affine-indep-iff` — `{pᵢ}` affinely independent ⇔ the top
      extensor `p̄₁ ∨ ⋯ ∨ p̄_k ≠ 0` (top extensor = full determinant).
- [ ] `def:extensor` — `j`-extensors as decomposable elements of
      `⋀ʲ ℝ^(d+1)` (symbolic layer on mathlib `ExteriorAlgebra`).
- [ ] `def:join` — the join `∨` (exterior product / its dual), with
      alternating / vanishes-on-repeats.
- [ ] `def:plucker-coords` — coordinatized Plücker vector of `j×j`
      minors with KT's sign `(−1)^(1+Σ iⱼ)`; the symbolic ↔ coordinate
      bridge.
- [ ] `def:affine-subspace-extensor` — the affine-subspace ↔ extensor
      map `C(·)`.
- [ ] `lem:extensor-independence` — **Lemma 2.1** (hard core): the
      `D = (d+1 choose 2)` many `(d−1)`-extensors of `d+1` affinely
      independent points are linearly independent. Proof joins the
      dependence relation with a `2`-extensor to kill all but one term
      (uses join-alternating + top-extensor ≠ 0).

## Decisions made during this phase

### Phase-local choices and proof techniques
- (none yet — opening commit)

## Blockers / open questions

- **mathlib coverage of `ExteriorAlgebra`.** mathlib has
  `ExteriorAlgebra` / `⋀[R] M` and the universal property, but not the
  Plücker/extensor coordinatization nor `C(·)`. Confirm what's reusable
  (graded pieces `⋀ʲ`, decomposability, the determinant ↔ top-degree
  pairing) before committing the symbolic-layer carrier. Upstream-
  eligible facts go under `CombinatorialRigidity/Mathlib/`.
- **Symbolic vs coordinatized depth** — risk register item 1 in
  `notes/MolecularConjecture.md`. Build the symbolic layer but don't
  over-build past what Lemma 2.1's proof and the Phase-18/22/23
  consumers need.

## Hand-off / next phase

Smallest next commit: land `def:homogeneous-coords` +
`lem:affine-indep-iff` in a new `CombinatorialRigidity/Molecular/Extensor.lean`
(or similar), flipping `\lean{}` + `\leanok` on those two
`molecular.tex` nodes in the same commit. These are the leaf-most red
nodes (no Phase-17 dependencies, both feed Lemma 2.1). Assess whether
the symbolic extensor layer (`def:extensor`, `def:join`) is one
session's work or several once `lem:affine-indep-iff` closes and the
mathlib `ExteriorAlgebra` coverage question above is settled.

Phase 17 completes when `lem:extensor-independence` (Lemma 2.1) is
green; that unblocks Phase 18 (panel-hinge rigidity matrix) and is the
linear-algebra foundation Case III (Phase 22/23) bottoms out on.
