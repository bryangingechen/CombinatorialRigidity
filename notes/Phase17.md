# Phase 17 — Grassmann–Cayley extensor algebra; Lemma 2.1 (work log)

**Status:** in progress (§2.1 symbolic layer + Plücker bridge landed:
homogeneous coords, affine-indep bridge, extensor, join, Plücker coords green;
`C(·)` / Lemma 2.1 red).

This phase opens the **molecular-conjecture program** (Phases 17–26).
The program-level plan — target, source, five-strata architecture,
phase breakdown, reuse map, risk register — lives in
`notes/MolecularConjecture.md`; read that first. This file is the
Phase-17 work log only.

## Current state

Phase 17 is open and the **symbolic extensor layer has landed** on top
of the homogeneous-coordinate bridge. `CombinatorialRigidity/Molecular/
Extensor.lean` now ships, in §2.1 dependency order:
- `homogenize` (`def:homogeneous-coords`) + the affine-independence
  bridge (`lem:affine-indep-iff`, both the linear-independence form
  `affineIndependent_iff_linearIndependent_homogenize` and the
  determinant form `affineIndependent_fin_iff_det_homogenize`);
- `extensor` (`def:extensor`) — `j`-extensors as
  `ExteriorAlgebra.ιMulti ℝ j v` on mathlib's
  `ExteriorAlgebra ℝ (Fin (d+1) → ℝ)`, with `extensor_mem_exteriorPower`
  (lands in `⋀[ℝ]^j`), `extensor_eq_zero_of_eq` /
  `extensor_eq_zero_of_not_injective` (alternating / vanishes-on-repeats
  — the load-bearing Lemma 2.1 fact);
- `join` (`def:join`) — the join `A ∨ₑ B := A * B` (scoped `∨ₑ`), with
  `join_extensor` (`extensor a ∨ₑ extensor b = extensor (Fin.append a b)`
  via `ιMulti_mul_ιMulti`) and `join_assoc`.

The **coordinatized Plücker bridge has now also landed**:
- `coordMatrix` — the `j × (d+1)` row matrix `A(v)` of a family;
- `pluckerCoord` (`def:plucker-coords`) — the signed `j × j` minor at a
  `j`-element column set `s`, with KT's sign `(-1)^{1+∑ iₗ}` carried as
  `1 + ∑ i ∈ s, (i.val + 1)` (KT is 1-based, mathlib `Fin (d+1)` is 0-based,
  so `iₗ = sᵢ.val + 1`);
- `pluckerVector` — the full `(d+1 choose j)`-vector over column subsets;
- `pluckerCoord_univ` — the top coordinate `= ±det (coordMatrix v)`, tying
  back to `affineIndependent_fin_iff_det_homogenize`'s determinant form.

Five blueprint nodes are now green (`def:homogeneous-coords`,
`lem:affine-indep-iff`, `def:extensor`, `def:join`, `def:plucker-coords`).
The remaining §2.1 dep-graph (`C(·)`, Lemma 2.1) is still red.

**mathlib `ExteriorAlgebra` coverage question (Blockers) is settled:**
mathlib's `Mathlib.LinearAlgebra.ExteriorPower.Basic` supplies everything
needed — graded pieces `⋀[ℝ]^j`, the alternating multilinear generator
`ExteriorAlgebra.ιMulti`, the join as `*` (`ιMulti_mul_ιMulti`), and the
vanishes-on-repeats facts. The symbolic layer is a thin wrapper; no new
exterior-algebra infrastructure required, so the symbolic-vs-coordinatized
depth stays shallow (risk register item 1 resolved in favour of "shallow,
reuse mathlib").

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
- [x] `def:extensor` — `j`-extensors as decomposable elements of
      `⋀ʲ ℝ^(d+1)` (`extensor`, on mathlib `ExteriorAlgebra.ιMulti`),
      with `extensor_mem_exteriorPower` + the vanishes-on-repeats facts.
- [x] `def:join` — the join `∨ₑ` (exterior product `*`), with
      `join_extensor` (`Fin.append` concatenation) + `join_assoc`;
      alternating / vanishes-on-repeats inherited via `def:extensor`.
- [x] `def:plucker-coords` — coordinatized Plücker vector of `j×j`
      minors with KT's sign `(−1)^(1+Σ iⱼ)`; the symbolic ↔ coordinate
      bridge (`coordMatrix`, `pluckerCoord`, `pluckerVector`,
      `pluckerCoord_univ`).
- [ ] `def:affine-subspace-extensor` — the affine-subspace ↔ extensor
      map `C(·)`.
- [ ] `lem:extensor-independence` — **Lemma 2.1** (hard core): the
      `D = (d+1 choose 2)` many `(d−1)`-extensors of `d+1` affinely
      independent points are linearly independent. Proof joins the
      dependence relation with a `2`-extensor to kill all but one term
      (uses join-alternating + top-extensor ≠ 0).

## Decisions made during this phase

### Phase-local choices and proof techniques
- **Plücker sign encoding.** KT's `P_{i₁,…,iⱼ}` uses 1-based column
  indices `1 ≤ i₁ < ⋯ ≤ d+1`; mathlib `Fin (d+1)` is 0-based, so KT's
  `iₗ = sᵢ.val + 1`. The exponent `1 + ∑ iₗ` is carried faithfully as
  `1 + ∑ i ∈ s, (i.val + 1)` in `pluckerCoord`. The `j×j` submatrix is
  `(coordMatrix v).submatrix id (s.orderEmbOfFin h)` (columns selected in
  increasing order by the order-embedding of the `j`-element column set).
  `def`/`noncomputable` because `Matrix.det` over `ℝ` is noncomputable.
- **`pluckerCoord_univ` idiom** → FRICTION [open] *No mathlib
  `Finset.univ.orderEmbOfFin = id`* (derive via `orderEmbOfFin_unique` +
  `submatrix_id_id`).
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

- **mathlib coverage of `ExteriorAlgebra` — RESOLVED.** Confirmed
  `Mathlib.LinearAlgebra.ExteriorPower.Basic` supplies the graded pieces
  `⋀[ℝ]^j` (`exteriorPower`), the decomposable generator
  `ExteriorAlgebra.ιMulti` (an `AlternatingMap`), the join as the ring
  product (`ιMulti_mul_ιMulti`), and vanishes-on-repeats
  (`ιMulti_eq_zero_of_not_inj`, `AlternatingMap.map_eq_zero_of_eq`). The
  symbolic carrier is `ExteriorAlgebra ℝ (Fin (d+1) → ℝ)`. No mirror
  lemmas were needed (the wrappers are one-liners over existing mathlib
  facts). The remaining gap (Plücker coords, `C(·)`) is genuinely new and
  is the next §2.1 work, not a mathlib-coverage question.
- **Symbolic vs coordinatized depth — RESOLVED shallow** (risk register
  item 1). The symbolic layer is a thin wrapper; build the coordinatized
  Plücker bridge (`def:plucker-coords`) next so Lemma 2.1 / the
  Phase-18/22/23 consumers stay concrete, exactly as planned.

## Hand-off / next phase

Done: `def:homogeneous-coords`, `lem:affine-indep-iff`, `def:extensor`,
`def:join`, `def:plucker-coords` all landed in
`CombinatorialRigidity/Molecular/Extensor.lean` (five `molecular.tex`
nodes green; symbolic carrier settled on mathlib
`ExteriorAlgebra ℝ (Fin (d+1) → ℝ)`, Plücker bridge via signed `j×j`
submatrix determinants on `coordMatrix`). Clean handoff point.

Smallest next commit: land `def:affine-subspace-extensor` — the
affine-subspace ↔ extensor map `C(·)` sending affinely-independent points
`p₁,…,p_k ∈ ℝ^d` to the join `p̄₁ ∨ ⋯ ∨ p̄_k` of their homogenizations
(`def:homogeneous-coords` + `def:extensor` + `def:join` already green),
with the nonvanishing characterization `C(·) ≠ 0 ⇔ affinely independent`
following from `affineIndependent_iff_linearIndependent_homogenize` +
the extensor/`ιMulti` nonvanishing-iff-LI fact. Likely-needed mathlib API:
`ExteriorAlgebra.ιMulti_ne_zero` / the LI ↔ `ιMulti ≠ 0` characterization
in `Mathlib.LinearAlgebra.ExteriorPower.Basic`. After `C(·)`: the hard
core `lem:extensor-independence` (Lemma 2.1) — joins the dependence
relation with a `2`-extensor `p̄_a ∨ p̄_b` to kill all but one term
(uses `extensor_eq_zero_of_eq` / `join_extensor` + top-extensor ≠ 0 via
`affineIndependent_fin_iff_det_homogenize`).

Phase 17 completes when `lem:extensor-independence` (Lemma 2.1) is green;
that unblocks Phase 18 (panel-hinge rigidity matrix) and is the
linear-algebra foundation Case III (Phase 22/23) bottoms out on.
