# Phase 17 — Grassmann–Cayley extensor algebra; Lemma 2.1 (work log)

**Status:** ✓ Complete. All §2.1 nodes green — homogeneous coords,
affine-indep bridge, extensor, join, Plücker coords, affine-subspace extensor,
and **Lemma 2.1** (`lem:extensor-independence`). Unblocks Phase 18.

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

The **affine-subspace extensor `C(·)` has now also landed**:
- `affineSubspaceExtensor` (`def:affine-subspace-extensor`) — `C(p) :=
  extensor (homogenize ∘ p)`, the join of the homogenizations;
- `affineSubspaceExtensor_ne_zero_iff` — `C(p) ≠ 0 ⇔ AffineIndependent ℝ p`,
  via the homogenization bridge + the extensor ↔ LI characterization
  `extensor_ne_zero_iff_linearIndependent` (forward via
  `AlternatingMap.map_linearDependent`; converse via mathlib's
  `exteriorPower.ιMulti_family_linearIndependent_field`).

All seven §2.1 blueprint nodes are now green (`def:homogeneous-coords`,
`lem:affine-indep-iff`, `def:extensor`, `def:join`, `def:plucker-coords`,
`def:affine-subspace-extensor`, `lem:extensor-independence`). **Lemma 2.1**
(`omitTwoExtensor` + `omitTwoExtensor_linearIndependent`) closes Phase 17.

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
- [x] `def:affine-subspace-extensor` — the affine-subspace ↔ extensor
      map `C(·)` (`affineSubspaceExtensor`), with the nonvanishing
      characterization `affineSubspaceExtensor_ne_zero_iff`
      (`C(p) ≠ 0 ⇔ AffineIndependent ℝ p`). Built on the extensor ↔ LI
      iff `extensor_ne_zero_iff_linearIndependent` +
      `extensor_eq_zero_of_not_linearIndependent`.
- [x] `lem:extensor-independence` — **Lemma 2.1** (hard core):
      `omitTwoExtensor` + `omitTwoExtensor_linearIndependent`. The
      `D = (d+1 choose 2)` many `(d−1)`-extensors of `d+1` affinely
      independent points are linearly independent. Proof joins the
      dependence relation on the left with a `2`-extensor to kill all but
      one term (off-diagonal: `join_pair_omitTwo_other_eq_zero` via
      `extensor_eq_zero_of_not_injective`; diagonal:
      `join_pair_omitTwo_self_ne_zero` via the `pairAppend` bijection +
      `extensor_ne_zero_iff_linearIndependent`).

## Decisions made during this phase

### Phase-local choices and proof techniques
- **Lemma 2.1: reparametrize `d = e+1` to clear `d−1` subtraction.**
  Points are `Fin (e+2) → Fin (e+1) → ℝ`, omit-two extensors are
  `e`-extensors (`omitTwoExtensor`, the extensor of `v` along
  `({a,b}ᶜ).orderEmbOfFin`). Index the `D` extensors by increasing pairs
  `{q : Fin(e+2)×Fin(e+2) // q.1<q.2}`; prove LI via
  `Fintype.linearIndependent_iff` + left-multiply by the `2`-extensor.
  Off-diagonal vanishing and diagonal nonvanishing are split into
  `join_pair_omitTwo_{other_eq_zero,self_ne_zero}`; the diagonal reindex
  is the `pairAppend` bijection (`Fin.append_injective_iff`). The
  `{a,b}≠{c,d}` finset step routes through `Finset.pair_eq_pair_iff`
  (mirrored post-phase — FRICTION [mirrored]).
- **`C(·)` is `extensor ∘ homogenize`, not a fresh join chain.** Since
  `join_extensor` already proves `extensor a ∨ₑ extensor b =
  extensor (a ++ b)`, the join `p̄₁ ∨ ⋯ ∨ p̄_k` *is* the extensor of the
  homogenized family, so `affineSubspaceExtensor p := extensor
  (homogenize ∘ p)` — no iterated `∨ₑ`. The nonvanishing iff then
  factors cleanly: homogenization bridge
  (`affineIndependent_iff_linearIndependent_homogenize`) ∘ the extensor
  ↔ LI fact (`extensor_ne_zero_iff_linearIndependent`).
- **Extensor ↔ LI nonvanishing** → FRICTION [open, kept-deferred] *No mathlib
  `exteriorPower.ιMulti v ≠ 0 ↔ LinearIndependent v`* (forward via
  `AlternatingMap.map_linearDependent`; converse via
  `ιMulti_family_linearIndependent_field` + `.ne_zero` at the unique
  `powersetCard` index, reusing the orderEmbOfFin = id trick).
- **Plücker sign encoding.** KT's `P_{i₁,…,iⱼ}` uses 1-based column
  indices `1 ≤ i₁ < ⋯ ≤ d+1`; mathlib `Fin (d+1)` is 0-based, so KT's
  `iₗ = sᵢ.val + 1`. The exponent `1 + ∑ iₗ` is carried faithfully as
  `1 + ∑ i ∈ s, (i.val + 1)` in `pluckerCoord`. The `j×j` submatrix is
  `(coordMatrix v).submatrix id (s.orderEmbOfFin h)` (columns selected in
  increasing order by the order-embedding of the `j`-element column set).
  `def`/`noncomputable` because `Matrix.det` over `ℝ` is noncomputable.
- **`pluckerCoord_univ` idiom** → FRICTION [mirrored] *`Finset.univ_orderEmbOfFin`
  (`Finset.univ.orderEmbOfFin = id`)*, mirrored post-phase; derived via
  `orderEmbOfFin_unique` + `submatrix_id_id`.
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

**Phase 17 complete.** All seven §2.1 nodes are green in
`CombinatorialRigidity/Molecular/Extensor.lean`: homogeneous coords +
affine-indep bridge, the symbolic extensor/join on mathlib
`ExteriorAlgebra ℝ (Fin (d+1) → ℝ)`, the Plücker bridge (signed `j×j`
submatrix determinants on `coordMatrix`), `C(·) = affineSubspaceExtensor`,
and **Lemma 2.1** (`omitTwoExtensor` + `omitTwoExtensor_linearIndependent`,
reparametrized `d = e+1`, indexed by increasing pairs). The proof joins on
the left with the `2`-extensor and splits per-term vanishing into
`join_pair_omitTwo_{other_eq_zero,self_ne_zero}` (the `pairAppend`
bijection for the surviving diagonal term).

Next phase is **Phase 18** (panel-hinge rigidity matrix `R(G,p)`, rank
Lemmas 5.1–5.3, reconciliation with Phase 16's reduction-form Prop 1.1;
KT §2.2–2.4). No chapter opened yet. First concrete commit: create
`notes/Phase18.md` from the template, open the Phase-18 blueprint chapter
(forward mode), and pick its leaf-most red node. See
`notes/MolecularConjecture.md` for the per-phase detail and the reuse map
(Lemma 2.1 is consumed by Case III, Phases 22–23). Phase 17's
`extensor` / `join` / `pluckerVector` / `affineSubspaceExtensor` are the
building blocks Phase 18's rigidity matrix is assembled from.
