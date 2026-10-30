/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.Carrier

/-!
# Configurations at every grade

The configurations of `sec:pencil-d-carrier` (`blueprint/src/chapter/pencil-d.tex`), the form at
every grade of `pencilConfigPoint` (`MainComponent/Carrier.lean`): a planar picture
`q : α × Fin 2 → K` and `m` heights `z : α × Fin m → K` give at each body `w` the point
`(x_w, y_w, z_(w,0), …, z_(w,m-1), 1)` of `K^(m+3)` (`pencilConfigPointGrade`). The rank of the
configuration (`def:pencil-d-configuration`) is the row rank of the panel-hinge framework
`PanelHingeFramework.ofNormals (k := m + 1)` whose normals are these points, at grade `m + 1`, in
dimension `d = m + 2`.

A configuration is indexed by its number `m = d − 2` of heights, not by its grade `k = m + 1`. The
point is built from its blocks (`Matrix.vecCons` twice, then `Fin.snoc` of the heights and `1`) and
typed `Fin (m + 1 + 2) → K`, so it is a normal of `ofNormals (k := m + 1)` with no cast, and no
truncated `k − 1` heights arise. At no height (`m = 0`, the plane) it is the homogeneous picture
point (`pencilConfigPointGrade_eq_pencilPicturePoint`), and at one height (`m = 1`, space) it is
`pencilConfigPoint` (`pencilConfigPointGrade_eq_pencilConfigPoint`), with the same rank
(`PanelHingeFramework.finrank_span_rigidityRows_ofNormals_pencilConfigPointGrade_one`). The heights
are uncurried, as pictures, normals and the variables of the rank polynomials are
(`MainComponent/Carrier.lean`).

## Main definitions

* `pencilConfigPointGrade`: the point `(x_w, y_w, z_w, 1) ∈ K^(m+3)` of the configuration `(q, z)`
  with `m` heights.

## Main results

* `pencilConfigPointGrade_apply_zero`, `pencilConfigPointGrade_apply_one`,
  `pencilConfigPointGrade_apply_height` and `pencilConfigPointGrade_apply_last`: its coordinates.
* `pencilConfigPointGrade_eq_pencilPicturePoint`: with no height, the homogeneous picture point.
* `pencilConfigPointGrade_eq_pencilConfigPoint` and
  `PanelHingeFramework.finrank_span_rigidityRows_ofNormals_pencilConfigPointGrade_one`: with one
  height, the configuration point of `def:pencil-configuration`, and its rank.
-/

@[expose] public section

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*} {m : ℕ}

/-! ## The configuration point -/

/-- **The configuration point at every grade** (`def:pencil-d-configuration`): the point
`b_w = (x_w, y_w, z_(w,0), …, z_(w,m-1), 1) ∈ K^(m+3)` of the configuration `(q, z)` with `m`
heights at the body `w`, the panel normal at `w` of a panel-hinge framework at grade `m + 1`, in
dimension `m + 2`. The type `Fin (m + 1 + 2) → K` is that of a normal of
`PanelHingeFramework.ofNormals (k := m + 1)`. Its coordinates are
`pencilConfigPointGrade_apply_zero` to `pencilConfigPointGrade_apply_last`; with one height it is
`pencilConfigPoint` (`pencilConfigPointGrade_eq_pencilConfigPoint`). -/
def pencilConfigPointGrade (q : α × Fin 2 → K) (z : α × Fin m → K) (w : α) :
    Fin (m + 1 + 2) → K :=
  Matrix.vecCons (q (w, 0)) (Matrix.vecCons (q (w, 1)) (Fin.snoc (fun i => z (w, i)) 1))

@[simp]
theorem pencilConfigPointGrade_apply_zero (q : α × Fin 2 → K) (z : α × Fin m → K) (w : α) :
    pencilConfigPointGrade q z w 0 = q (w, 0) := rfl

@[simp]
theorem pencilConfigPointGrade_apply_one (q : α × Fin 2 → K) (z : α × Fin m → K) (w : α) :
    pencilConfigPointGrade q z w 1 = q (w, 1) := rfl

/-- The height coordinates of the configuration point: its coordinate `i + 2` is the height
`z_(w,i)`, the index in the form `simp` leaves it (`Fin.castSucc_succ`). -/
@[simp]
theorem pencilConfigPointGrade_apply_height (q : α × Fin 2 → K) (z : α × Fin m → K) (w : α)
    (i : Fin m) : pencilConfigPointGrade q z w i.castSucc.succ.succ = z (w, i) := by
  simp [pencilConfigPointGrade]

/-- The last coordinate of the configuration point is `1`. -/
@[simp]
theorem pencilConfigPointGrade_apply_last (q : α × Fin 2 → K) (z : α × Fin m → K) (w : α) :
    pencilConfigPointGrade q z w (Fin.last (m + 2)) = 1 := by
  simp [pencilConfigPointGrade, ← Fin.succ_last]

/-! ## No height and one height -/

/-- **With no height, the configuration point is the homogeneous picture point**
(`def:pencil-d-configuration` at `d = 2`): `(x_w, y_w, 1) ∈ K³`, `pencilPicturePoint`. -/
theorem pencilConfigPointGrade_eq_pencilPicturePoint (q : α × Fin 2 → K) (z : α × Fin 0 → K)
    (w : α) : pencilConfigPointGrade q z w = pencilPicturePoint q w := by
  funext i
  fin_cases i <;> rfl

/-- **With one height, the configuration point is that of `def:pencil-configuration`**
(`def:pencil-d-configuration` at `d = 3`): `(x_w, y_w, z_(w,0), 1) ∈ K⁴`, `pencilConfigPoint` at the
height `v ↦ z_(v,0)`. A height `z : α → K` is the one of `fun p => z p.1`, so this covers both
directions between `m = 1` heights and one height. -/
theorem pencilConfigPointGrade_eq_pencilConfigPoint (q : α × Fin 2 → K) (z : α × Fin 1 → K)
    (w : α) : pencilConfigPointGrade q z w = pencilConfigPoint q (fun v => z (v, 0)) w := by
  funext i
  fin_cases i <;> rfl

/-- **With one height, the configuration has the rank of `def:pencil-configuration`** (the rank of
`def:pencil-d-configuration` at `d = 3`, read as `Graph.X0Attains` reads it): the framework
`PanelHingeFramework.ofNormals (k := 1 + 1)` at the points `pencilConfigPointGrade q z` has the row
rank of `ofNormals (k := 2)` at the points `pencilConfigPoint q (fun v => z (v, 0))`
(`pencilConfigPointGrade_eq_pencilConfigPoint`). The normals are rewritten first: the two ranks are
not cheaply definitionally equal, and `rfl` exhausts the heartbeats. -/
theorem PanelHingeFramework.finrank_span_rigidityRows_ofNormals_pencilConfigPointGrade_one
    {G : Graph α β} {ends : β → α × α}
    (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2)
    (q : α × Fin 2 → K) (z : α × Fin 1 → K) :
    Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 1 + 1) G ends
        (fun p => pencilConfigPointGrade q z p.1 p.2)).toBodyHinge.rigidityRows)
      = Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 2) G ends
        (fun p => pencilConfigPoint q (fun v => z (v, 0)) p.1 p.2)).toBodyHinge.rigidityRows) := by
  have h : (fun p : α × Fin (1 + 1 + 2) => pencilConfigPointGrade q z p.1 p.2)
      = fun p => pencilConfigPoint q (fun v => z (v, 0)) p.1 p.2 :=
    funext fun p => congrFun (pencilConfigPointGrade_eq_pencilConfigPoint q z p.1) p.2
  rw [h]

end CombinatorialRigidity.Molecular
