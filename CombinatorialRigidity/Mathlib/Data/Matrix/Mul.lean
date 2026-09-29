/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.Data.Matrix.Mul

/-!
# Upstream candidates: `dotProduct` against an affine combination

Phase 40-cleanup B7: the recurring `rw [dotProduct_add, dotProduct_smul, …, smul_eq_mul, …]`
three-plus-argument towers, fused into one lemma each.

The Lean namespace has no owner upstream (`dotProduct_add` / `dotProduct_smul` /
`smul_eq_mul` are root-level), so these stay unnamespaced too; promotion to mathlib is a
copy-paste. See `DESIGN.md` "Mirror directory".

## Contents (target file: `Mathlib/Data/Matrix/Mul.lean`)

* `dotProduct_add_smul` — `v ⬝ᵥ (u + c • w) = v ⬝ᵥ u + c * (v ⬝ᵥ w)`. Fuses
  `dotProduct_add` + `dotProduct_smul` + `smul_eq_mul` for a dot product against a sum of a
  plain vector and a scaled one.
* `dotProduct_smul_add_smul` — `v ⬝ᵥ (c • pa + d • pb) = c * (v ⬝ᵥ pa) + d * (v ⬝ᵥ pb)`. Same
  fusion, one level deeper, for a dot product against an affine combination of two vectors.
-/

@[expose] public section

variable {m : Type*} [Fintype m] {α : Type*} [CommSemiring α]

/-- A dot product against a sum of a plain vector and a scaled one: fuses `dotProduct_add`,
`dotProduct_smul` and `smul_eq_mul`. -/
theorem dotProduct_add_smul (v u w : m → α) (c : α) :
    v ⬝ᵥ (u + c • w) = v ⬝ᵥ u + c * (v ⬝ᵥ w) := by
  rw [dotProduct_add, dotProduct_smul, smul_eq_mul]

/-- A dot product against an affine combination of two vectors: fuses `dotProduct_add`,
two `dotProduct_smul`s and two `smul_eq_mul`s. -/
theorem dotProduct_smul_add_smul (v pa pb : m → α) (c d : α) :
    v ⬝ᵥ (c • pa + d • pb) = c * (v ⬝ᵥ pa) + d * (v ⬝ᵥ pb) := by
  rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
