/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Upstream candidates: the dot product is a reflexive nondegenerate bilinear form

`Mathlib.LinearAlgebra.Matrix.ToLin` defines `dotProductBilin`, the dot product of `m → A` as a
bilinear map, but mathlib does not state that it is reflexive or nondegenerate, the two hypotheses
of `LinearMap.BilinForm.orthogonal_orthogonal` (and nondegeneracy that of
`LinearMap.BilinForm.finrank_orthogonal`). The combinatorial-rigidity project uses both for the
orthogonal of a subspace of `K^n` under the dot product (`dotPerp`, in
`Molecular/Molecule/Pencil/Grade/Realization.lean`).

Mirror path: `Mathlib/LinearAlgebra/Matrix/BilinearForm.lean`. Promotion to mathlib is a
copy-paste into the upstream file, next to `Matrix.nondegenerate_toBilin'_iff`.
-/

@[expose] public section

variable {R m : Type*} [CommSemiring R] [Fintype m]

/-- **The dot product is reflexive**: `x ⬝ᵥ y = 0` gives `y ⬝ᵥ x = 0` (`dotProduct_comm`). -/
theorem isRefl_dotProductBilin :
    LinearMap.BilinForm.IsRefl (dotProductBilin R R : LinearMap.BilinForm R (m → R)) := by
  intro x y h
  simpa [dotProduct_comm] using h

/-- **The dot product is nondegenerate**: a vector whose dot product with every vector vanishes is
zero, on either side, as its dot product with `Pi.single i 1` is its `i`-th coordinate. -/
theorem nondegenerate_dotProductBilin :
    (dotProductBilin R R : LinearMap.BilinForm R (m → R)).Nondegenerate := by
  classical
  refine ⟨fun x hx => funext fun i => ?_, fun y hy => funext fun i => ?_⟩
  · simpa using hx (Pi.single i 1)
  · simpa using hy (Pi.single i 1)
