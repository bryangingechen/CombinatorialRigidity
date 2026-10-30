/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Collineation
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
* `Graph.finrank_span_rigidityRows_ofNormals_heights_linearEquiv_add_affineLifts`: a linear change
  and affine shifts of the heights keep the rank (`lem:pencil-d-rank-scale-shift`).
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

/-! ## Linear changes and affine shifts of the heights -/

/-- **A linear change and an affine shift of the heights keep the rank**
(`lem:pencil-d-rank-scale-shift`): for an invertible `T` of `K^m` and `a_i ∈ Aff(q)`
(`Graph.affineLifts`), the configurations `(q, z)` and `(q, Tz + a)` with `m` heights have the same
row rank at `ofNormals` of their points, where `(Tz + a)_(w,i) = (T z_w)_i + a_i(w)`. With
`a_i(w) = c_i ⬝ᵥ (x_w, y_w, 1)` on `V(G)`, the invertible linear map
`(ξ, η, ζ, ω) ↦ (ξ, η, Tζ + ξα + ηβ + ωγ, ω)` of `K^(m+3)` takes the point of `(q, z)` to that of
`(q, Tz + a)` at every body of `G`, and
`PanelHingeFramework.finrank_span_rigidityRows_ofNormals_linearEquiv_grade` applies. The map is
built from the blocks as the point is, so its coordinates are those of
`pencilConfigPointGrade_apply_zero` to `pencilConfigPointGrade_apply_last`. -/
theorem _root_.Graph.finrank_span_rigidityRows_ofNormals_heights_linearEquiv_add_affineLifts
    {G : Graph α β} {ends : β → α × α}
    (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2)
    (q : α × Fin 2 → K) (z : α × Fin m → K) (T : (Fin m → K) ≃ₗ[K] (Fin m → K))
    {a : Fin m → α → K} (ha : ∀ i, a i ∈ G.affineLifts q) :
    Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := m + 1) G ends
        (fun p => pencilConfigPointGrade q
          (fun x => T (fun j => z (x.1, j)) x.2 + a x.2 x.1) p.1 p.2)).toBodyHinge.rigidityRows)
      = Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := m + 1) G ends
        (fun p => pencilConfigPointGrade q z p.1 p.2)).toBodyHinge.rigidityRows) := by
  choose c hc using fun i => ha i
  -- the blocks of a vector of `K^(m+3)` and the vector built from them
  let ζ : (Fin (m + 1 + 2) → K) → Fin m → K := fun b j => b j.castSucc.succ.succ
  let mk : K → K → (Fin m → K) → K → Fin (m + 1 + 2) → K := fun x y u w =>
    Matrix.vecCons x (Matrix.vecCons y (Fin.snoc u w))
  have mk_ext : ∀ {x y x' y' : K} {u u' : Fin m → K} {w w' : K},
      x = x' → y = y' → u = u' → w = w' → mk x y u w = mk x' y' u' w' := by
    intro _ _ _ _ _ _ _ _ h1 h2 h3 h4
    subst h1 h2 h3 h4
    rfl
  have mk_eta : ∀ b : Fin (m + 1 + 2) → K, b = mk (b 0) (b 1) (ζ b) (b (Fin.last (m + 2))) := by
    intro b
    funext i
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.lastCases ?_ fun j => ?_)) i
    · rfl
    · rfl
    · simp [mk, ← Fin.succ_last]
    · simp [mk, ζ]
  have mk_add : ∀ x y x' y' u u' w w', mk x y u w + mk x' y' u' w' =
      mk (x + x') (y + y') (u + u') (w + w') := by
    intro x y x' y' u u' w w'
    funext i
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.lastCases ?_ fun j => ?_)) i
    · rfl
    · rfl
    · simp [mk, -Fin.succ_last]
    · simp [mk]
  have mk_smul : ∀ (r : K) x y u w, r • mk x y u w = mk (r * x) (r * y) (r • u) (r * w) := by
    intro r x y u w
    funext i
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.lastCases ?_ fun j => ?_)) i
    · rfl
    · rfl
    · simp [mk, -Fin.succ_last]
    · simp [mk]
  have mk_zero : ∀ x y u w, mk x y u w 0 = x := fun _ _ _ _ => rfl
  have mk_one : ∀ x y u w, mk x y u w 1 = y := fun _ _ _ _ => rfl
  have mk_last : ∀ x y u w, mk x y u w (Fin.last (m + 2)) = w := by
    intro x y u w; simp [mk, ← Fin.succ_last]
  have hζ : ∀ x y u w, ζ (mk x y u w) = u := by
    intro x y u w; funext j; simp [ζ, mk]
  let s : (Fin (m + 1 + 2) → K) → Fin m → K := fun b i =>
    c i 0 * b 0 + c i 1 * b 1 + c i 2 * b (Fin.last (m + 2))
  have s_add : ∀ b b', s (b + b') = s b + s b' := by
    intro b b'; funext i; simp [s]; ring
  have s_smul : ∀ (r : K) b, s (r • b) = r • s b := by
    intro r b; funext i; simp [s]; ring
  let f : (Fin (m + 1 + 2) → K) →ₗ[K] (Fin (m + 1 + 2) → K) :=
    { toFun := fun b => mk (b 0) (b 1) (T (ζ b) + s b) (b (Fin.last (m + 2)))
      map_add' := fun b b' => by
        rw [mk_add]
        refine mk_ext rfl rfl ?_ rfl
        have : ζ (b + b') = ζ b + ζ b' := rfl
        rw [this, map_add, s_add]; abel
      map_smul' := fun r b => by
        rw [RingHom.id_apply, mk_smul]
        refine mk_ext rfl rfl ?_ rfl
        have : ζ (r • b) = r • ζ b := rfl
        rw [this, map_smul, s_smul, smul_add] }
  let f' : (Fin (m + 1 + 2) → K) →ₗ[K] (Fin (m + 1 + 2) → K) :=
    { toFun := fun b => mk (b 0) (b 1) (T.symm (ζ b - s b)) (b (Fin.last (m + 2)))
      map_add' := fun b b' => by
        rw [mk_add]
        refine mk_ext rfl rfl ?_ rfl
        have : ζ (b + b') = ζ b + ζ b' := rfl
        rw [this, s_add, ← map_add]; congr 1; abel
      map_smul' := fun r b => by
        rw [RingHom.id_apply, mk_smul]
        refine mk_ext rfl rfl ?_ rfl
        have : ζ (r • b) = r • ζ b := rfl
        rw [this, s_smul, ← smul_sub, map_smul] }
  have hs : ∀ b, s (f b) = s b := by
    intro b; funext i; simp only [s, f, LinearMap.coe_mk, AddHom.coe_mk, mk_zero, mk_one, mk_last]
  have hs' : ∀ b, s (f' b) = s b := by
    intro b; funext i; simp only [s, f', LinearMap.coe_mk, AddHom.coe_mk, mk_zero, mk_one, mk_last]
  have hl : ∀ b, f b (Fin.last (m + 2)) = b (Fin.last (m + 2)) := fun b => by
    simp only [f, LinearMap.coe_mk, AddHom.coe_mk, mk_last]
  have hl' : ∀ b, f' b (Fin.last (m + 2)) = b (Fin.last (m + 2)) := fun b => by
    simp only [f', LinearMap.coe_mk, AddHom.coe_mk, mk_last]
  have hff : ∀ b, f (f' b) = b := by
    intro b
    change mk _ _ (T (ζ (f' b)) + s (f' b)) _ = b
    conv_rhs => rw [mk_eta b]
    refine mk_ext rfl rfl ?_ (hl' b)
    have h1 : ζ (f' b) = T.symm (ζ b - s b) := by
      simp only [f', LinearMap.coe_mk, AddHom.coe_mk, hζ]
    rw [h1, hs']
    simp
  have hf'f : ∀ b, f' (f b) = b := by
    intro b
    change mk _ _ (T.symm (ζ (f b) - s (f b))) _ = b
    conv_rhs => rw [mk_eta b]
    refine mk_ext rfl rfl ?_ (hl b)
    have h1 : ζ (f b) = T (ζ b) + s b := by
      simp only [f, LinearMap.coe_mk, AddHom.coe_mk, hζ]
    rw [h1, hs]
    simp
  let g : (Fin (m + 1 + 2) → K) ≃ₗ[K] (Fin (m + 1 + 2) → K) := LinearEquiv.ofLinearMap f f'
    (LinearMap.ext hff) (LinearMap.ext hf'f)
  have hg : ∀ w ∈ V(G), g (pencilConfigPointGrade q z w) = pencilConfigPointGrade q
      (fun x => T (fun j => z (x.1, j)) x.2 + a x.2 x.1) w := by
    intro w hw
    have hp : ∀ (q : α × Fin 2 → K) (z : α × Fin m → K) w,
        pencilConfigPointGrade q z w = mk (q (w, 0)) (q (w, 1)) (fun i => z (w, i)) 1 :=
      fun _ _ _ => rfl
    rw [hp, hp]
    change mk _ _ (T (ζ (mk _ _ _ _)) + s (mk _ _ _ _)) _ = _
    refine mk_ext (mk_zero _ _ _ _) (mk_one _ _ _ _) ?_ (mk_last _ _ _ _)
    rw [hζ]
    funext i
    have hai : a i w = c i ⬝ᵥ pencilPicturePoint q w := by
      rw [← hc i, Graph.affineLiftMap_apply]; simp [hw]
    simp only [s, Pi.add_apply, mk_zero, mk_one, mk_last, hai, dotProduct, Fin.sum_univ_three,
      pencilPicturePoint]
    simp [add_assoc]
  exact PanelHingeFramework.finrank_span_rigidityRows_ofNormals_linearEquiv_grade hends g
    (fun w hw => (hg w hw).symm)

end CombinatorialRigidity.Molecular
