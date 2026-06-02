/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.BodyBar.Framework
import CombinatorialRigidity.BodyBar.KFrame

/-!
# Tay's theorem, existence form (`thm:tay-witness`)

Phase 15. Whiteley 1988 (*The union of matroids and the rigidity of frameworks*,
SIAM J. Disc. Math. **1**, Theorem 8), in the existence-of-realization form: for
`n ≥ 2` and `d = bodyBarDim n = n(n+1)/2`, a multigraph `G` carries an independent
body-bar framework in `ℝⁿ` iff it is `(d, d)`-sparse (equivalently — Phase 13 — the
edge-disjoint union of `d` forests), and an isostatic one iff `(d, d)`-tight (the
union of `d` spanning trees).

## Witness construction

The witness specializes each bar's two-extensor coordinate to a **standard basis
vector** `b_e = e_{j(e)} ∈ ℝᵈ`, where `j(e)` is the index of `e`'s forest in a
chosen tree-packing partition (`thm:tutte-nash-williams`). These degenerate
two-extensors lie on the Plücker variety vacuously (existence-of-realization scope;
see `Framework.lean`'s module docstring), so they form a valid body-bar realization.

With this placement the rigidity-map row for a bar `e` collapses to the single
coordinate `j(e)` of the relative body velocity (`stdPlacement_rigidityMap_apply`):
`⟪e_{j(e)}, m u − m v⟫ = (m u − m v)(j e)`. The rigidity matrix is therefore
**block-diagonal** across the `d` coordinates, the block at index `j` being the
signed incidence matrix of the forest `Fs j` (over `ℝ`). Each block has full row
rank (a forest's incidence rows are linearly independent —
`Graph.orientation.isAcyclicSet_linearIndepOn`), so the row rank of the whole matrix
is `Σⱼ |Fs j| = |E|`, i.e. the framework is independent. This is the reverse
direction of `thm:k-frame-union-cycle`
(`Graph.linearIndepOn_kFrameRow_of_isSparse_restrict`) lifted from indeterminate to
real coefficients.

## Current state (Phase 15, in progress)

This file currently ships the **witness placement and the bar-row reduction** — the
foundational step that exposes the block-diagonal structure. The block-diagonal
rank count and the `thm:tay-witness` iff are the next sub-steps. See
`ROADMAP.md` §15, `notes/Phase15.md`, and the §`sec:body-bar-tay` subsection of
`blueprint/src/chapter/body-bar.tex`.
-/

open scoped InnerProductSpace

namespace Graph

namespace BodyBarFramework

variable {α β : Type*} {n : ℕ}

/-- The **standard-basis placement** of a multigraph `G` from a forest-index map
`j : E(G) → Fin (bodyBarDim n)`: each bar `e` is assigned the standard basis
vector `e_{j(e)} = EuclideanSpace.single (j e) 1 ∈ ℝᵈ`, `d = bodyBarDim n`. This is
the witness placement of Tay's theorem (Whiteley 1988 §3): `j(e)` is the index of
`e`'s forest in a tree-packing partition, and `e_{j(e)}` is a (degenerate)
two-extensor. -/
noncomputable def stdPlacement (G : Graph α β) (n : ℕ)
    (j : E(G) → Fin (bodyBarDim n)) :
    E(G) → EuclideanSpace ℝ (Fin (bodyBarDim n)) :=
  fun e => EuclideanSpace.single (j e) (1 : ℝ)

/-- The **standard-basis body-bar framework** of `G` for a forest-index map `j`:
the body-bar framework whose placement is `stdPlacement G n j`. The witness object
of Tay's theorem. -/
noncomputable def stdFramework (G : Graph α β) (n : ℕ)
    (j : E(G) → Fin (bodyBarDim n)) : BodyBarFramework n α β where
  graph := G
  placement := stdPlacement G n j

@[simp]
theorem stdFramework_graph (G : Graph α β) (n : ℕ)
    (j : E(G) → Fin (bodyBarDim n)) : (stdFramework G n j).graph = G := rfl

@[simp]
theorem stdFramework_placement (G : Graph α β) (n : ℕ)
    (j : E(G) → Fin (bodyBarDim n)) :
    (stdFramework G n j).placement = stdPlacement G n j := rfl

/-- **Bar-row reduction at a standard-basis placement** (the foundational step of
the witness argument). With each bar `e` placed at the standard basis vector
`e_{j(e)}`, the rigidity-map row at `e` evaluated at a motion `m` collapses to the
single coordinate `j(e)` of the relative body velocity at `e`'s oriented endpoints
`(u, v) = D.dInc e`:
`(stdFramework G n j).rigidityMap D m e = (m u − m v) (j e)`.

This is what makes the rigidity matrix block-diagonal across the `d = bodyBarDim n`
coordinates: the row for `e` is supported entirely in coordinate `j(e)`, where it is
the signed incidence row of `e`. Over `ℝ`, `EuclideanSpace.inner_single_left` gives
`⟪e_{j(e)}, w⟫ = conj 1 · w (j e) = w (j e)`. -/
theorem stdPlacement_rigidityMap_apply (G : Graph α β) (n : ℕ)
    (j : E(G) → Fin (bodyBarDim n)) (D : Graph.orientation G)
    (m : Motion n α) (e : E(G)) :
    (stdFramework G n j).rigidityMap D m e
      = (m (D.dInc e).1 - m (D.dInc e).2) (j e) := by
  rw [rigidityMap_apply, stdFramework_placement, stdPlacement,
    EuclideanSpace.inner_single_left]
  simp

end BodyBarFramework

end Graph
