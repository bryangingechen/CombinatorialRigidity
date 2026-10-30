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
* `Graph.liftingSpaceGrade` and `Graph.X0AttainsGrade`: the lifting space `L(q)^m` of `m` heights,
  and the general configuration attaining in dimension `m + 2` (`def:pencil-d-x0-attains`).

## Main results

* `pencilConfigPointGrade_apply_zero`, `pencilConfigPointGrade_apply_one`,
  `pencilConfigPointGrade_apply_height` and `pencilConfigPointGrade_apply_last`: its coordinates.
* `pencilConfigPointGrade_eq_pencilPicturePoint`: with no height, the homogeneous picture point.
* `pencilConfigPointGrade_eq_pencilConfigPoint` and
  `PanelHingeFramework.finrank_span_rigidityRows_ofNormals_pencilConfigPointGrade_one`: with one
  height, the configuration point of `def:pencil-configuration`, and its rank.
* `Graph.finrank_span_rigidityRows_ofNormals_heights_linearEquiv_add_affineLifts`: a linear change
  and affine shifts of the heights keep the rank (`lem:pencil-d-rank-scale-shift`).
* `Graph.x0AttainsGrade_one_iff`: at one height, `Graph.X0AttainsGrade` is `Graph.X0Attains`
  (`lem:pencil-d-x0-attains-three`).
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

/-! ## The blocks of a vector of `K^(m+3)` -/

/-- The vector of `K^(m+3)` built from its blocks `(x, y, u, w)`, as `pencilConfigPointGrade` is. -/
def gradeMk (x y : K) (u : Fin m → K) (w : K) : Fin (m + 1 + 2) → K :=
  Matrix.vecCons x (Matrix.vecCons y (Fin.snoc u w))

/-- The height block of a vector of `K^(m+3)`: its coordinates `2` to `m + 1`. -/
def gradeHeights (b : Fin (m + 1 + 2) → K) : Fin m → K := fun j => b j.castSucc.succ.succ

omit [Field K] in
theorem gradeMk_ext {x y x' y' : K} {u u' : Fin m → K} {w w' : K}
    (h1 : x = x') (h2 : y = y') (h3 : u = u') (h4 : w = w') :
    gradeMk x y u w = gradeMk x' y' u' w' := by
  subst h1 h2 h3 h4
  rfl

omit [Field K] in
theorem gradeMk_eta (b : Fin (m + 1 + 2) → K) :
    b = gradeMk (b 0) (b 1) (gradeHeights b) (b (Fin.last (m + 2))) := by
  funext i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.lastCases ?_ fun j => ?_)) i
  · rfl
  · rfl
  · simp [gradeMk, ← Fin.succ_last]
  · simp [gradeMk, gradeHeights]

theorem gradeMk_add (x y x' y' : K) (u u' : Fin m → K) (w w' : K) :
    gradeMk x y u w + gradeMk x' y' u' w' = gradeMk (x + x') (y + y') (u + u') (w + w') := by
  funext i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.lastCases ?_ fun j => ?_)) i
  · rfl
  · rfl
  · simp [gradeMk, -Fin.succ_last]
  · simp [gradeMk]

theorem gradeMk_smul (r x y : K) (u : Fin m → K) (w : K) :
    r • gradeMk x y u w = gradeMk (r * x) (r * y) (r • u) (r * w) := by
  funext i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.lastCases ?_ fun j => ?_)) i
  · rfl
  · rfl
  · simp [gradeMk, -Fin.succ_last]
  · simp [gradeMk]

omit [Field K] in
@[simp]
theorem gradeMk_apply_zero (x y : K) (u : Fin m → K) (w : K) : gradeMk x y u w 0 = x := rfl

omit [Field K] in
@[simp]
theorem gradeMk_apply_one (x y : K) (u : Fin m → K) (w : K) : gradeMk x y u w 1 = y := rfl

omit [Field K] in
@[simp]
theorem gradeMk_apply_last (x y : K) (u : Fin m → K) (w : K) :
    gradeMk x y u w (Fin.last (m + 2)) = w := by
  simp [gradeMk, ← Fin.succ_last]

omit [Field K] in
@[simp]
theorem gradeHeights_gradeMk (x y : K) (u : Fin m → K) (w : K) :
    gradeHeights (gradeMk x y u w) = u := by
  funext j; simp [gradeHeights, gradeMk]

theorem gradeHeights_add (b b' : Fin (m + 1 + 2) → K) :
    gradeHeights (b + b') = gradeHeights b + gradeHeights b' := rfl

theorem gradeHeights_smul (r : K) (b : Fin (m + 1 + 2) → K) :
    gradeHeights (r • b) = r • gradeHeights b := rfl

theorem pencilConfigPointGrade_eq_gradeMk (q : α × Fin 2 → K) (z : α × Fin m → K) (w : α) :
    pencilConfigPointGrade q z w = gradeMk (q (w, 0)) (q (w, 1)) (fun i => z (w, i)) 1 := rfl

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
  let mk : K → K → (Fin m → K) → K → Fin (m + 1 + 2) → K := gradeMk
  let ζ : (Fin (m + 1 + 2) → K) → Fin m → K := gradeHeights
  have mk_ext : ∀ {x y x' y' : K} {u u' : Fin m → K} {w w' : K},
      x = x' → y = y' → u = u' → w = w' → mk x y u w = mk x' y' u' w' := gradeMk_ext
  have mk_eta : ∀ b : Fin (m + 1 + 2) → K, b = mk (b 0) (b 1) (ζ b) (b (Fin.last (m + 2))) :=
    gradeMk_eta
  have mk_add : ∀ x y x' y' u u' w w', mk x y u w + mk x' y' u' w' =
      mk (x + x') (y + y') (u + u') (w + w') := gradeMk_add
  have mk_smul : ∀ (r : K) x y u w, r • mk x y u w = mk (r * x) (r * y) (r • u) (r * w) :=
    gradeMk_smul
  have mk_zero : ∀ x y u w, mk x y u w 0 = x := fun _ _ _ _ => rfl
  have mk_one : ∀ x y u w, mk x y u w 1 = y := fun _ _ _ _ => rfl
  have mk_last : ∀ x y u w, mk x y u w (Fin.last (m + 2)) = w := gradeMk_apply_last
  have hζ : ∀ x y u w, ζ (mk x y u w) = u := gradeHeights_gradeMk
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

/-! ## The general configuration attains -/

/-- **The lifting space of `m` heights, `L(q)^m`** (`def:pencil-d-x0-attains`): the heights
`z : α × Fin m → K` each of whose `m` columns `w ↦ z (w, i)` lies in the lifting space `L(q)` of the
planar picture `q` (`Graph.liftingSpace`). -/
def _root_.Graph.liftingSpaceGrade (G : Graph α β) (q : α × Fin 2 → K) (m : ℕ) :
    Submodule K (α × Fin m → K) :=
  ⨅ i : Fin m, (G.liftingSpace q).comap (LinearMap.funLeft K K fun w : α => (w, i))

theorem _root_.Graph.mem_liftingSpaceGrade {G : Graph α β} {q : α × Fin 2 → K}
    {z : α × Fin m → K} :
    z ∈ G.liftingSpaceGrade q m ↔ ∀ i : Fin m, (fun w => z (w, i)) ∈ G.liftingSpace q := by
  simp [Graph.liftingSpaceGrade, Submodule.mem_iInf]
  rfl

/-- **The general configuration of `G` attains in dimension `m + 2`** (`def:pencil-d-x0-attains`,
`m` heights): `Graph.X0Attains` at `m` heights, `m = 1` being space
(`Graph.x0AttainsGrade_one_iff`).
There are a selector `ends` recording every link of `G` and a nonzero polynomial `P` in the picture
coordinates such that every picture `q` off the zero set of `P` is admissible, and the heights
`z ∈ L(q)^m` (`Graph.liftingSpaceGrade`) at which the configuration `(q, z)` has the deficiency
rank,
that of the panel-hinge framework `PanelHingeFramework.ofNormals (k := m + 1) G ends` at the points
`pencilConfigPointGrade q z` equal to `screwDim (m + 1) * (|V(G)| − 1) − def_(m+2)(G)`, contain a
nonempty Zariski-open subset of `L(q)^m`: the non-roots in `L(q)^m` of a polynomial `R` in the `m`
height coordinates of each body, at least one of which lies in `L(q)^m`. The deficiency is taken at
the dimension `m + 2`.

As for `Graph.X0Attains`, `P ≠ 0` means "off a proper Zariski-closed set of pictures" only over an
infinite field; the lemmas that use it assume `[Infinite K]`. -/
def _root_.Graph.X0AttainsGrade (K : Type*) [Field K] (m : ℕ) (G : Graph α β) : Prop :=
  ∃ (ends : β → α × α) (P : MvPolynomial (α × Fin 2) K)
    (hlinks : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2), P ≠ 0 ∧
    ∀ q : α × Fin 2 → K, MvPolynomial.eval q P ≠ 0 →
      G.IsAdmissiblePicture q ∧
      ∃ R : MvPolynomial (α × Fin m) K,
        (∃ z ∈ G.liftingSpaceGrade q m, MvPolynomial.eval z R ≠ 0) ∧
        ∀ z ∈ G.liftingSpaceGrade q m, MvPolynomial.eval z R ≠ 0 →
          (Module.finrank K (Submodule.span K
            (PanelHingeFramework.ofNormals (k := m + 1) G ends
              (fun p => pencilConfigPointGrade q z p.1 p.2)).toBodyHinge.rigidityRows) : ℤ)
            = screwDim (m + 1) * ((V(G).ncard : ℤ) - 1) - G.deficiency (m + 2)

/-- **Attaining in dimension three** (`lem:pencil-d-x0-attains-three`): with one height,
`Graph.X0AttainsGrade` is `Graph.X0Attains` of `def:pencil-x0-attains`. The heights move along
`α × Fin 1 ≃ α` and the polynomials by `MvPolynomial.rename`. -/
theorem _root_.Graph.x0AttainsGrade_one_iff {G : Graph α β} :
    G.X0AttainsGrade K 1 ↔ G.X0Attains K := by
  have hc : ∀ z : α × Fin 1 → K, z = fun p => (fun v => z (v, 0)) p.1 := by
    intro z; funext p; obtain ⟨a, i⟩ := p; rw [Subsingleton.elim i 0]
  have hmem : ∀ {q : α × Fin 2 → K} {z : α × Fin 1 → K},
      z ∈ G.liftingSpaceGrade q 1 ↔ (fun v => z (v, 0)) ∈ G.liftingSpace q := by
    intro q z
    rw [Graph.mem_liftingSpaceGrade]
    exact ⟨fun h => h 0, fun h i => by rwa [Subsingleton.elim i 0]⟩
  constructor
  · rintro ⟨ends, P, hlinks, hP, H⟩
    refine ⟨ends, P, hlinks, hP, fun q hq => ?_⟩
    obtain ⟨hadm, R, ⟨z, hz, hRz⟩, hR⟩ := H q hq
    refine ⟨hadm, MvPolynomial.rename Prod.fst R, ⟨fun v => z (v, 0), hmem.1 hz, ?_⟩, ?_⟩
    · have h : ((fun v => z (v, 0)) ∘ Prod.fst) = z := (hc z).symm
      rw [MvPolynomial.eval_rename, h]; exact hRz
    · intro z' hz' hRz'
      rw [MvPolynomial.eval_rename] at hRz'
      have := hR (fun p => z' p.1) (hmem.2 hz') hRz'
      rw [PanelHingeFramework.finrank_span_rigidityRows_ofNormals_pencilConfigPointGrade_one
        hlinks q _] at this
      exact this
  · rintro ⟨ends, P, hlinks, hP, H⟩
    refine ⟨ends, P, hlinks, hP, fun q hq => ?_⟩
    obtain ⟨hadm, R, ⟨z, hz, hRz⟩, hR⟩ := H q hq
    refine ⟨hadm, MvPolynomial.rename (fun a => (a, (0 : Fin 1))) R,
      ⟨fun p => z p.1, hmem.2 hz, ?_⟩, ?_⟩
    · rw [MvPolynomial.eval_rename]; exact hRz
    · intro z' hz' hRz'
      rw [MvPolynomial.eval_rename] at hRz'
      rw [PanelHingeFramework.finrank_span_rigidityRows_ofNormals_pencilConfigPointGrade_one
        hlinks q _]
      exact hR _ (hmem.1 hz') hRz'

end CombinatorialRigidity.Molecular
