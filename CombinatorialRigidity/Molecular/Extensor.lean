/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

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

end CombinatorialRigidity.Molecular
