/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Grassmann–Cayley extensor algebra: homogeneous coordinates (`sec:molecular-homog`)

Phase 17, the first phase of the molecular-conjecture program (Phases 17–26;
see `notes/MolecularConjecture.md`). This file opens the Grassmann–Cayley /
extensor-algebra layer of Katoh–Tanigawa 2011 (*A proof of the molecular
conjecture*, Discrete Comput. Geom. **45**, §2.1), the load-bearing target of
which is Lemma 2.1 (independence of the `(d-1)`-extensors of `d+1` affinely
independent points; `blueprint/src/chapter/molecular.tex`,
`lem:extensor-independence`).

This first commit lands the leaf-most red nodes of the §2.1 dep-graph:

* `homogenize` (`def:homogeneous-coords`) — the homogeneous coordinatization
  `p ↦ (p, 1) : ℝ^d → ℝ^(d+1)`, sending a point of affine `d`-space to its
  homogeneous coordinate vector by appending a final `1` coordinate
  (`Fin.snoc p 1`).
* `affineIndependent_iff_linearIndependent_homogenize` (`lem:affine-indep-iff`,
  linear-independence form) — `p₁, …, pₖ` are affinely independent iff their
  homogenizations `p̄₁, …, p̄ₖ` are linearly independent in `ℝ^(d+1)`. This is
  the core bridge underlying the blueprint's join-nonvanishing reformulation
  (the latter additionally restates "linearly independent" as "join `≠ 0`",
  which awaits the join / extensor layer, `def:join` / `def:extensor`).
* `affineIndependent_fin_iff_det_homogenize` (`lem:affine-indep-iff`, top-extensor
  form) — `d+1` points are affinely independent iff the determinant of the
  `(d+1) × (d+1)` matrix of their homogeneous coordinates is nonzero. This is
  the top-extensor (full-determinant) specialization the blueprint singles out.

The symbolic Grassmann–Cayley layer (`def:extensor`, `def:join`) follows:

* `extensor` (`def:extensor`) — a `j`-extensor in `ℝ^(d+1)` is the decomposable
  element `v₁ ∧ ⋯ ∧ vⱼ` of the `j`-th exterior power, built on mathlib's
  `ExteriorAlgebra.ιMulti` (so `extensor v ∈ ⋀[ℝ]^j (Fin (d+1) → ℝ)`, the graded
  piece `exteriorPower`). Two facts the join needs come for free from `ιMulti`
  being an `AlternatingMap`: it vanishes on a repeated vector
  (`extensor_eq_zero_of_not_injective` / `extensor_eq_zero_of_eq`) — the
  load-bearing fact for Lemma 2.1.
* `join` (`def:join`) — the join `A ∨ B` of two extensors is their exterior
  product `A * B` in `ExteriorAlgebra ℝ (Fin (d+1) → ℝ)`. `join_extensor`
  records the defining identity `extensor a ∨ extensor b = extensor (a ++ b)`
  (mathlib `ιMulti_mul_ιMulti`, with `Fin.append` the concatenation); the join
  inherits associativity / graded-commutativity from the ring product.

## Symbolic carrier (mathlib `ExteriorAlgebra` coverage)

The symbolic layer reuses mathlib's `ExteriorAlgebra ℝ (Fin (d+1) → ℝ)`
verbatim. mathlib's `Mathlib.LinearAlgebra.ExteriorPower.Basic` supplies all the
needed scaffolding: the graded pieces `⋀[ℝ]^j M` (`exteriorPower`, a
`Submodule`), the decomposable generators via the alternating multilinear map
`ExteriorAlgebra.ιMulti ℝ j : M [⋀^Fin j]→ₗ[R] ExteriorAlgebra ℝ M`, the
exterior product `*` as the join (`ExteriorAlgebra.ιMulti_mul_ιMulti`), and the
alternating / vanishes-on-repeats facts (`ExteriorAlgebra.ιMulti_eq_zero_of_not_inj`,
`AlternatingMap.map_eq_zero_of_eq`). Lemma 2.1 is self-contained from these plus
the affine-independence bridge above; no new exterior-algebra infrastructure is
required, so the symbolic-vs-coordinatized depth (risk register item 1 in
`notes/MolecularConjecture.md`) stays shallow — the only remaining §2.1 work is
the coordinatized Plücker bridge (`def:plucker-coords`), `C(·)`
(`def:affine-subspace-extensor`), and Lemma 2.1 itself.

## Carrier

A point of affine `d`-space is `Fin d → ℝ` and homogenizes to `Fin (d+1) → ℝ`
(via `Fin.snoc`, appending the constant `1`). This concrete coordinate carrier
is the natural one for the exterior power `⋀ʲ ℝ^(d+1)` and the `j × j`-minor
Plücker vectors of the downstream nodes; the symbolic exterior-algebra layer
(`def:extensor`, `def:join`) builds on mathlib's `⋀[ℝ]` over the same
`Fin (d+1) → ℝ`. (Phase 4's `Framework V d` uses `EuclideanSpace ℝ (Fin d)`;
the two agree up to the canonical isometry on `Fin d → ℝ`, so Phase 18/24 reuse
stays frictionless.)
-/

@[expose] public section

namespace CombinatorialRigidity.Molecular

open scoped Matrix

variable {d : ℕ}

/-- **Homogeneous coordinatization** (`def:homogeneous-coords`). The homogeneous
coordinate vector `p̄ = (p, 1) ∈ ℝ^(d+1)` of a point `p ∈ ℝ^d`, obtained by
appending a final `1` coordinate. -/
def homogenize (p : Fin d → ℝ) : Fin (d + 1) → ℝ :=
  Fin.snoc p 1

@[simp]
theorem homogenize_castSucc (p : Fin d → ℝ) (i : Fin d) :
    homogenize p i.castSucc = p i := by
  simp [homogenize]

@[simp]
theorem homogenize_last (p : Fin d → ℝ) :
    homogenize p (Fin.last d) = 1 := by
  simp [homogenize]

/-- **Affine independence via homogenization** (`lem:affine-indep-iff`,
linear-independence form). A family `p : ι → ℝ^d` of points is affinely
independent if and only if the homogenized family `homogenize ∘ p : ι → ℝ^(d+1)`
is linearly independent.

This is the core content of `lem:affine-indep-iff`. The blueprint additionally
phrases linear independence as the join `p̄₁ ∨ ⋯ ∨ p̄ₖ ≠ 0`; that reformulation
awaits the join / extensor layer (`def:join`, `def:extensor`). -/
theorem affineIndependent_iff_linearIndependent_homogenize
    {ι : Type*} (p : ι → Fin d → ℝ) :
    AffineIndependent ℝ p ↔ LinearIndependent ℝ (fun i => homogenize (p i)) := by
  rw [affineIndependent_iff, linearIndependent_iff']
  constructor
  · -- affine ⇒ linear: a vanishing homogeneous combination has both
    -- `∑ w = 0` (last coordinate) and `∑ w • p = 0` (first `d` coordinates).
    intro h s w hw i hi
    have hsum : ∀ j : Fin (d + 1), (∑ e ∈ s, w e • homogenize (p e)) j = 0 := by
      rw [hw]; simp
    have hlast : ∑ e ∈ s, w e = 0 := by
      have := hsum (Fin.last d)
      simpa [Finset.sum_apply, Pi.smul_apply] using this
    have hpts : ∑ e ∈ s, w e • p e = 0 := by
      funext j
      have := hsum j.castSucc
      simpa [Finset.sum_apply, Pi.smul_apply] using this
    exact h s w hlast hpts i hi
  · -- linear ⇒ affine: an affine combination (`∑ w = 0`, `∑ w • p = 0`) lifts to
    -- a vanishing homogeneous combination.
    intro h s w hw hpts i hi
    refine h s w ?_ i hi
    funext j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · -- last coordinate: `∑ w • 1 = ∑ w = 0`
      simp only [Finset.sum_apply, Pi.smul_apply, homogenize_last, smul_eq_mul, mul_one,
        Pi.zero_apply]
      simpa using hw
    · -- `j = k.castSucc`: `∑ w • p k = 0`
      simp only [Finset.sum_apply, Pi.smul_apply, homogenize_castSucc, smul_eq_mul, Pi.zero_apply]
      have := congrFun hpts k
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this

/-- **Affine independence via the top extensor** (`lem:affine-indep-iff`,
determinant form). `d+1` points `p : Fin (d+1) → ℝ^d` are affinely independent
if and only if the determinant of the `(d+1) × (d+1)` matrix of their homogeneous
coordinates is nonzero.

This is the top-extensor (full-determinant) specialization the blueprint
singles out: for `d+1` points the top exterior power `⋀^(d+1) ℝ^(d+1)` is
one-dimensional and the coordinate of the join `p̄₁ ∨ ⋯ ∨ p̄_{d+1}` is exactly
this determinant. -/
theorem affineIndependent_fin_iff_det_homogenize (p : Fin (d + 1) → Fin d → ℝ) :
    AffineIndependent ℝ p ↔
      (Matrix.of (fun i => homogenize (p i))).det ≠ 0 := by
  rw [affineIndependent_iff_linearIndependent_homogenize,
    show (fun i => homogenize (p i)) = (Matrix.of (fun i => homogenize (p i))).row from rfl,
    Matrix.linearIndependent_rows_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero]
  rfl

/-! ## Extensors and the join

The symbolic Grassmann–Cayley layer on mathlib's exterior algebra. We work in
`ExteriorAlgebra ℝ (Fin (d+1) → ℝ)`; a `j`-extensor is the decomposable element
`v₁ ∧ ⋯ ∧ vⱼ`, packaged through the alternating multilinear map
`ExteriorAlgebra.ιMulti ℝ j`, and the join is the exterior product. -/

/-- **Extensor** (`def:extensor`). The `j`-extensor of a family
`v : Fin j → ℝ^(d+1)` is the decomposable element
`v 0 ∧ ⋯ ∧ v (j-1)` of the exterior algebra, i.e. the value of mathlib's
alternating multilinear map `ExteriorAlgebra.ιMulti ℝ j`. It lands in the graded
piece `⋀[ℝ]^j (Fin (d+1) → ℝ)` (see `extensor_mem_exteriorPower`). -/
def extensor {d j : ℕ} (v : Fin j → Fin (d + 1) → ℝ) :
    ExteriorAlgebra ℝ (Fin (d + 1) → ℝ) :=
  ExteriorAlgebra.ιMulti ℝ j v

theorem extensor_apply {d j : ℕ} (v : Fin j → Fin (d + 1) → ℝ) :
    extensor v = ExteriorAlgebra.ιMulti ℝ j v := rfl

/-- A `j`-extensor lies in the `j`-th exterior power (graded piece)
`⋀[ℝ]^j (Fin (d+1) → ℝ)`. -/
theorem extensor_mem_exteriorPower {d j : ℕ} (v : Fin j → Fin (d + 1) → ℝ) :
    extensor v ∈ ⋀[ℝ]^j (Fin (d + 1) → ℝ) :=
  ExteriorAlgebra.ιMulti_range ℝ j ⟨v, rfl⟩

/-- A `j`-extensor vanishes when two of its vectors coincide (the alternating
property of the join; `def:extensor`). This — together with
`extensor_eq_zero_of_not_injective` — is the load-bearing fact for Lemma 2.1's
"join the relation with a `2`-extensor to kill all but one term" argument. -/
theorem extensor_eq_zero_of_eq {d j : ℕ} (v : Fin j → Fin (d + 1) → ℝ)
    {a b : Fin j} (hab : v a = v b) (hne : a ≠ b) : extensor v = 0 :=
  (ExteriorAlgebra.ιMulti ℝ j).map_eq_zero_of_eq v hab hne

/-- A `j`-extensor vanishes when its family of vectors is not injective — the
contrapositive packaging of `extensor_eq_zero_of_eq` (`def:extensor`). -/
theorem extensor_eq_zero_of_not_injective {d j : ℕ} {v : Fin j → Fin (d + 1) → ℝ}
    (hv : ¬Function.Injective v) : extensor v = 0 :=
  ExteriorAlgebra.ιMulti_eq_zero_of_not_inj hv

/-- **Join** (`def:join`). The join `A ∨ B` of two extensors is their exterior
product `A * B` in `ExteriorAlgebra ℝ (Fin (d+1) → ℝ)`. Geometrically it
represents the span of the two corresponding subspaces (when they meet only at
the origin). The join inherits associativity and graded-commutativity from the
ring product. -/
def join {d : ℕ} (A B : ExteriorAlgebra ℝ (Fin (d + 1) → ℝ)) :
    ExteriorAlgebra ℝ (Fin (d + 1) → ℝ) :=
  A * B

@[inherit_doc] scoped infixl:70 " ∨ₑ " => join

theorem join_def {d : ℕ} (A B : ExteriorAlgebra ℝ (Fin (d + 1) → ℝ)) :
    A ∨ₑ B = A * B := rfl

/-- The defining identity of the join on extensors (`def:join`): joining the
`m`-extensor of `a` with the `n`-extensor of `b` is the `(m+n)`-extensor of the
concatenated family `Fin.append a b`. Immediate from mathlib's
`ExteriorAlgebra.ιMulti_mul_ιMulti`. -/
theorem join_extensor {d m n : ℕ} (a : Fin m → Fin (d + 1) → ℝ)
    (b : Fin n → Fin (d + 1) → ℝ) :
    extensor a ∨ₑ extensor b = extensor (Fin.append a b) :=
  ExteriorAlgebra.ιMulti_mul_ιMulti a b

/-- The join is associative (inherited from the ring product; `def:join`). -/
theorem join_assoc {d : ℕ} (A B C : ExteriorAlgebra ℝ (Fin (d + 1) → ℝ)) :
    (A ∨ₑ B) ∨ₑ C = A ∨ₑ (B ∨ₑ C) :=
  mul_assoc A B C

/-! ## The extensor of an affine subspace

The map `C(·)` sending affinely independent points `p₁, …, p_k ∈ ℝ^d` to the join
`p̄₁ ∨ ⋯ ∨ p̄_k` of their homogenizations, with the nonvanishing characterization
`C(p) ≠ 0 ⇔ p` affinely independent. -/

/-- A `k`-extensor `extensor v` vanishes when `v` is linearly dependent; over a
field, the converse also holds (see `extensor_ne_zero_iff_linearIndependent`).
The forward direction is `AlternatingMap.map_linearDependent` applied to mathlib's
`ExteriorAlgebra.ιMulti`. -/
theorem extensor_eq_zero_of_not_linearIndependent {d k : ℕ}
    {v : Fin k → Fin (d + 1) → ℝ} (hv : ¬LinearIndependent ℝ v) :
    extensor v = 0 :=
  (ExteriorAlgebra.ιMulti ℝ k).map_linearDependent v hv

/-- **Extensor nonvanishing characterizes linear independence** (over `ℝ`). The
`k`-extensor `extensor v` is nonzero if and only if the family `v` is linearly
independent. The forward direction is the contrapositive of
`extensor_eq_zero_of_not_linearIndependent`; the converse extends `v` to a basis of
its span and reads off a nonzero exterior-power basis coordinate
(mathlib's `exteriorPower.ιMulti_family_linearIndependent_field`). -/
theorem extensor_ne_zero_iff_linearIndependent {d k : ℕ}
    (v : Fin k → Fin (d + 1) → ℝ) :
    extensor v ≠ 0 ↔ LinearIndependent ℝ v := by
  constructor
  · intro h
    by_contra hv
    exact h (extensor_eq_zero_of_not_linearIndependent hv)
  · intro hv hzero
    -- The family of `k`-fold exterior products of `v` is linearly independent
    -- (`ιMulti_family_linearIndependent_field`), hence each member is nonzero.
    -- The unique `k`-element subset of `Fin k` is `univ`, whose order embedding is
    -- `id`, so that member is `extensor v` itself (up to the `⋀[ℝ]^k` coercion).
    have hfam := exteriorPower.ιMulti_family_linearIndependent_field
      (K := ℝ) (n := k) (v := v) hv
    set s : Set.powersetCard (Fin k) k := ⟨Finset.univ, by simp⟩ with hs
    have hne := hfam.ne_zero s
    apply hne
    have hid : Set.powersetCard.ofFinEmbEquiv.symm s = (id : Fin k → Fin k) := by
      rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
      exact (Finset.orderEmbOfFin_unique s.2 (fun _ => Finset.mem_univ _) strictMono_id).symm
    apply Subtype.ext
    rw [exteriorPower.ιMulti_family_apply_coe, ZeroMemClass.coe_zero]
    change ExteriorAlgebra.ιMulti ℝ k (v ∘ ⇑(Set.powersetCard.ofFinEmbEquiv.symm s)) = 0
    rw [hid, Function.comp_id]
    exact hzero

/-- **Extensor of an affine subspace** (`def:affine-subspace-extensor`). The
extensor `C(p)` of the affine subspace spanned by points `p₁, …, p_k ∈ ℝ^d` is the
join `p̄₁ ∨ ⋯ ∨ p̄_k ∈ ⋀^k ℝ^(d+1)` of their homogenizations — equivalently
(`join_extensor`) the `k`-extensor of the homogenized family. It is well-defined up
to a nonzero scalar and, by `affineSubspaceExtensor_ne_zero_iff`, nonzero exactly
when the points are affinely independent, so `C` faithfully encodes the affine
subspace. -/
def affineSubspaceExtensor {d k : ℕ} (p : Fin k → Fin d → ℝ) :
    ExteriorAlgebra ℝ (Fin (d + 1) → ℝ) :=
  extensor (fun i => homogenize (p i))

theorem affineSubspaceExtensor_apply {d k : ℕ} (p : Fin k → Fin d → ℝ) :
    affineSubspaceExtensor p = extensor (fun i => homogenize (p i)) := rfl

/-- **The extensor of an affine subspace is nonzero iff the points are affinely
independent** (`def:affine-subspace-extensor`). Combines the homogenization bridge
`affineIndependent_iff_linearIndependent_homogenize` with the extensor nonvanishing
characterization `extensor_ne_zero_iff_linearIndependent`. -/
theorem affineSubspaceExtensor_ne_zero_iff {d k : ℕ} (p : Fin k → Fin d → ℝ) :
    affineSubspaceExtensor p ≠ 0 ↔ AffineIndependent ℝ p := by
  rw [affineSubspaceExtensor, extensor_ne_zero_iff_linearIndependent,
    ← affineIndependent_iff_linearIndependent_homogenize]

/-! ## Plücker coordinates

The coordinatized bridge from the symbolic exterior-algebra layer to the concrete
minor vectors. Following Katoh–Tanigawa §2.1, a family `v : Fin j → ℝ^(d+1)`
assembles into the `j × (d+1)` matrix `A(v)` whose `i`-th row is `v i`; the
Plücker coordinate at an increasing column index set is a signed `j × j` minor of
`A(v)`. -/

/-- The `j × (d+1)` coordinate matrix of a family `v : Fin j → ℝ^(d+1)`, whose
`i`-th row is the vector `v i` (Katoh–Tanigawa's `A(p₁, …, pⱼ)`). -/
def coordMatrix {d j : ℕ} (v : Fin j → Fin (d + 1) → ℝ) :
    Matrix (Fin j) (Fin (d + 1)) ℝ :=
  Matrix.of v

/-- **Plücker coordinate** (`def:plucker-coords`). The Plücker coordinate
`P_{i₁,…,iⱼ}` of the `j`-extensor of `v : Fin j → ℝ^(d+1)`, indexed by a
`j`-element column set `s : Finset (Fin (d+1))`. Following
Katoh–Tanigawa~`\cite{katohTanigawa2011}` §2.1 it is the Katoh–Tanigawa sign
`(-1)^{1 + i₁ + ⋯ + iⱼ}` times the determinant of the `j × j` submatrix of
`coordMatrix v` whose columns are `s`, taken in increasing order. The sign uses
the **1-based** column indices `iₗ = (orderEmbOfFin) + 1` of KT's convention
(mathlib's `Fin (d+1)` is `0`-based, so `iₗ = sᵢ.val + 1`); concretely the
exponent is `1 + ∑_{i ∈ s} (i.val + 1)`. -/
noncomputable def pluckerCoord {d j : ℕ} (v : Fin j → Fin (d + 1) → ℝ)
    (s : Finset (Fin (d + 1))) (h : s.card = j) : ℝ :=
  (-1) ^ (1 + ∑ i ∈ s, (i.val + 1)) *
    ((coordMatrix v).submatrix id (s.orderEmbOfFin h)).det

/-- **Plücker coordinate vector** (`def:plucker-coords`). The full vector of
Plücker coordinates of the `j`-extensor of `v`, indexed by the `j`-element
column subsets `s : {s : Finset (Fin (d+1)) // s.card = j}`. This is the
coordinatized realization of the symbolic extensor `extensor v`; KT's
`(d+1 choose j)`-dimensional Plücker coordinate vector. -/
noncomputable def pluckerVector {d j : ℕ} (v : Fin j → Fin (d + 1) → ℝ) :
    {s : Finset (Fin (d + 1)) // s.card = j} → ℝ :=
  fun s => pluckerCoord v s.1 s.2

/-- The top Plücker coordinate of `d+1` points (the unique column subset is all
of `Fin (d+1)`) is, up to the KT sign, the full homogeneous-coordinate
determinant of `affineIndependent_fin_iff_det_homogenize`. Concretely, taking the
top column set `s = Finset.univ`, the submatrix is the matrix itself, so the
Plücker coordinate is `±det (coordMatrix v)`. -/
theorem pluckerCoord_univ {d : ℕ} (v : Fin (d + 1) → Fin (d + 1) → ℝ)
    (h : (Finset.univ : Finset (Fin (d + 1))).card = d + 1) :
    pluckerCoord v Finset.univ h =
      (-1) ^ (1 + ∑ i : Fin (d + 1), (i.val + 1)) * (coordMatrix v).det := by
  rw [pluckerCoord]
  congr 1
  have hemb : (id : Fin (d + 1) → Fin (d + 1)) = Finset.univ.orderEmbOfFin h :=
    Finset.orderEmbOfFin_unique h (fun _ => Finset.mem_univ _) strictMono_id
  rw [← hemb, Matrix.submatrix_id_id]

end CombinatorialRigidity.Molecular
