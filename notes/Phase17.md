# Phase 17 — Grassmann–Cayley extensor algebra; Lemma 2.1 (work log)

**Status:** in progress (opening commit; chapter dep-graph is all red).

This phase opens the **molecular-conjecture program** (Phases 17–26).
The program-level plan — target, source, five-strata architecture,
phase breakdown, reuse map, risk register — lives in
`notes/MolecularConjecture.md`; read that first. This file is the
Phase-17 work log only.

## Current state

Phase 17 is open and the **first Lean has landed**:
`CombinatorialRigidity/Molecular/Extensor.lean` ships the two leaf-most
§2.1 nodes — `homogenize` (`def:homogeneous-coords`, the `p ↦ (p,1)`
coordinatization via `Fin.snoc p 1`) and the affine-independence bridge
(`lem:affine-indep-iff`): both the linear-independence form
(`affineIndependent_iff_linearIndependent_homogenize`) and the
top-extensor / determinant form
(`affineIndependent_fin_iff_det_homogenize`). Both blueprint nodes are
now green. The forward-mode chapter `blueprint/src/chapter/molecular.tex`
and the user-facing status surfaces remain in place. The remaining §2.1
dep-graph (extensor, join, Plücker coords, `C(·)`, Lemma 2.1) is still
red.

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

- [x] `def:homogeneous-coords` — homogeneous coordinatization `p ↦ (p,1)`
      (`homogenize`, `Fin.snoc p 1`).
- [x] `lem:affine-indep-iff` — `{pᵢ}` affinely independent ⇔ homogenized
      family lin. indep. (`affineIndependent_iff_linearIndependent_homogenize`),
      and the `d+1`-point top-extensor/determinant form
      (`affineIndependent_fin_iff_det_homogenize`). The join-nonvanishing
      restatement awaits `def:join` (still red).
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
- **Carrier (decided on first Lean).** Point space `Fin d → ℝ`,
  homogenizing to `Fin (d+1) → ℝ` via `Fin.snoc p 1`. Plain coordinate
  tuples (not `EuclideanSpace`) are the natural carrier for the
  exterior power `⋀ʲ (Fin (d+1) → ℝ)` and the `j×j`-minor Plücker
  vectors downstream. Phase 4's `Framework V d` uses
  `EuclideanSpace ℝ (Fin d)`; the two agree up to the canonical
  isometry, so Phase 18/24 reuse stays frictionless (noted in the file
  docstring).
- **`lem:affine-indep-iff` proof.** No join/extensor needed yet:
  mathlib's `affineIndependent_iff` (the `V → V` self-affine-space form:
  affine indep ⇔ every `w` with `∑w=0`, `∑ w•p=0` is zero) is exactly
  the homogenized linear-independence condition — the last homogeneous
  coordinate carries `∑w=0`, the first `d` carry `∑ w•p=0`. Determinant
  form via `Matrix.linearIndependent_rows_iff_isUnit` +
  `isUnit_iff_isUnit_det` + `isUnit_iff_ne_zero`. The join-nonvanishing
  reformulation in the blueprint is now a forward pointer to `def:join`.

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

Done: `def:homogeneous-coords` + `lem:affine-indep-iff` landed in
`CombinatorialRigidity/Molecular/Extensor.lean` (both `molecular.tex`
nodes green). Clean handoff point.

Smallest next commit: start the symbolic extensor layer — land
`def:extensor` (`j`-extensors as decomposable elements of
`⋀ʲ (Fin (d+1) → ℝ)` on mathlib `ExteriorAlgebra` / `exteriorPower`)
and `def:join` (the join `∨` = exterior product, with its
alternating / vanishes-on-repeats facts). **First settle the
mathlib `ExteriorAlgebra` coverage question** in *Blockers* below:
confirm `exteriorPower`'s graded-piece API (`⋀[ℝ]^j`), decomposability,
and the alternating multilinear map into `⋀ʲ` before committing the
symbolic carrier. The join's alternating/vanishes-on-repeats property
is the load-bearing fact for Lemma 2.1's proof; if the chosen carrier
does not give it cheaply, that signals reconsidering the
symbolic-vs-coordinatized depth (risk register item 1). `def:join`
once landed also lets `lem:affine-indep-iff`'s join-nonvanishing
restatement (currently a forward pointer in the blueprint) be tied to
Lean if desired.

Phase 17 completes when `lem:extensor-independence` (Lemma 2.1) is
green; that unblocks Phase 18 (panel-hinge rigidity matrix) and is the
linear-algebra foundation Case III (Phase 22/23) bottoms out on.
