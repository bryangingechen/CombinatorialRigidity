/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Mathlib.Algebra.MvPolynomial.Monad
import CombinatorialRigidity.Mathlib.LinearAlgebra.Matrix.MvPolynomial
import CombinatorialRigidity.Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import CombinatorialRigidity.Molecular.Molecule.Pencil.Engine

/-!
# The main component: planar pictures, the lifting space, and `X₀` attaining (Phase 40b CARRIER)

The definitions the `X₀` argument rests on and its one-witness upgrade
(`blueprint/src/chapter/main-component.tex`, `sec:main-component-carrier`; Phase 40b CARRIER
slices C1a, C1b, C2, C3, and C4, `notes/Phase40b.md`). A pencil
configuration of `G` over a field `K` is read as a **planar picture** `q` (a point
`(x_v, y_v) ∈ K²` per body) together with a **height** `z` (a scalar `z_v` per body); the body's
homogeneous point is `p_v = (x_v, y_v, z_v, 1)`. Over a fixed admissible picture the heights for
which every closed neighbourhood is coplanar form a linear space `L(q)` (informal (MC-1)), and the
pictures of least `dim L(q)` form the open set `U` over which `X₀` is a vector bundle ((MC-2)).

## Main definitions

* `pencilPicturePoint` — the homogeneous picture point `(x_w, y_w, 1) ∈ K³`.
* `Graph.IsAdmissiblePicture` — adjacent picture points distinct, and every closed neighbourhood
  carries three members with independent homogeneous picture points (not collinear).
* `Graph.liftingSpace` — the lifting space `L(q)`: heights supported on `V(G)` that restrict on
  every closed neighbourhood to an affine function of the picture.
* `Graph.affineLifts` — `Aff(q)` restricted to `V(G)`: the range of `Graph.affineLiftMap`, a
  single triple of affine coefficients applied at every body.
* `Graph.IsMainPicture` — `U`: admissible pictures whose lifting space has the least dimension
  among admissible pictures.
* `pencilConfigPoint` — the homogeneous configuration point `p_w = (x_w, y_w, z_w, 1) ∈ K⁴`.
* `pencilNormalOfPicture` — the plane normal at a body: `cross₃` of three selected configuration
  points, polynomial and denominator-free.
* `Graph.X0Attains` — "`X₀(G)`'s general point attains `6(|V| − 1) − def₃(G)`" ((MC-10)(a)): off
  one nonzero polynomial in the picture coordinates, the picture is admissible and the attaining
  heights contain a nonempty Zariski-open subset of `L(q)`.
* `pointJoinFramework` — the body-hinge framework whose hinge at each label is the join
  `p_u ∧ p_v` of its two ends' points.
* `pencilConfigFramework` — the point-join framework of a configuration, patched off `E(G)` by a
  fixed nonzero hinge: the framework of the pencil realization a configuration gives.

## Main statements

* `Graph.IsAdmissiblePicture.supportExtensor_ne_zero` — over an admissible picture every hinge of
  the configuration is nonzero, at every height.
* `Graph.IsAdmissiblePicture.exists_mvPolynomial` — admissibility is Zariski-open.
* `Graph.liftingMatrix` — the lifting system, a matrix of polynomials in the picture whose kernel
  projects onto `L(q)` (`Graph.map_ker_liftingMatrix`), isomorphically over an admissible picture
  (`Graph.finrank_ker_liftingMatrix`).
* `Graph.weightedLiftingMatrix` — the lifting system with an arbitrary polynomial weight point in
  place of the picture point (`Graph.weightedLiftingMatrix_mulVec_eq_zero_iff`), the shape of the
  contraction step's rescaled system.
* `Graph.x0Attains_of_exists` — one attaining configuration over a main picture forces
  `Graph.X0Attains` (the semicontinuity half of (MC-2)/(MC-10)).
* `Graph.affineLifts_le_liftingSpace` — `Aff(q) ⊆ L(q)` at every picture.
* `Graph.finrank_affineLifts` — `Aff(q)` is three-dimensional at an admissible picture with at
  least one body; `Graph.three_le_finrank_liftingSpace` names the resulting `3 ≤ dim L(q)`.
* `pencilNormalOfPicture_ne_zero_iff` — the normal is nonzero iff the selected configuration
  triple is independent.
* `linearIndependent_pencilConfigPoint_of_linearIndependent_pencilPicturePoint` — picture
  independence gives configuration independence, at every height.
* `dotProduct_pencilNormalOfPicture_eq_zero_of_mem_closedNbhd` — over `z ∈ L(q)`, the plane of a
  valid selector at `v` is orthogonal to the whole closed neighbourhood of `v`, not only the three
  selected bodies (CARRIER's C3, new; consumed by C4).
* `exists_smul_pencilNormalOfPicture_eq_of_mem_closedNbhd` — two selectors at the same body give
  proportional normals.
* `pencilNormalOfPicturePoly` / `eval_pencilNormalOfPicturePoly` — the polynomial mirror of the
  normal in the height variables, at a fixed picture (`X0Gen`'s fibre-intersection shape).
* `ofNormals_toBodyHinge_eq_mapSupport_pointJoinFramework` — `ofNormals` at the points is the
  polarity image of the point-join framework; `finrank_span_rigidityRows_pencilConfigFramework`
  carries the rank to the patched configuration framework.
* `Graph.IsAdmissiblePicture.hasPencilPanelRealization_pencilConfigFramework` — over an admissible
  picture and a height in `L(q)`, the configuration is a pencil panel realization.
* `Graph.IsAdmissiblePicture.hasDistinctPencilRealization` — an attaining configuration over an
  admissible picture gives `HasDistinctPencilRealization K 3 G`;
  `Graph.X0Attains.hasDistinctPencilRealization` is the resulting `X0Dist` leg, over an infinite
  field.
* `Graph.finrank_span_rigidityRows_ofNormals_smul_add_affineLifts` — the rank is unchanged by
  `z ↦ t • z + a` for `t ≠ 0` and `a ∈ Aff(q)` (the last clause of (MC-3)).
* `Graph.IsAdmissiblePicture.mem_liftingSpace_of_coplanar` — over an admissible picture, coplanar
  closed neighbourhoods force `z ∈ L(q)` (`lem:pencil-condition-linear`'s converse, CARRIER's C5′).
* `Graph.IsAdmissiblePicture.exists_smul_eq_interpolant` — every nonzero normal of a closed
  neighbourhood is a nonzero scalar multiple of the interpolant `(h₀, h₁, -1, h₂)`
  (`lem:pencil-condition-linear`'s unique non-vertical plane, CARRIER's C5′).

## Design

* **Uncurried pictures** `q : α × Fin 2 → K`, the shape of `PanelHingeFramework.ofNormals`'s
  coordinate argument and of the rank polynomials' variable type.
* **The rank is taken at `ofNormals` of the configuration points, not of the plane normals.**
  `X0Attains` reads `PanelHingeFramework.ofNormals G ends (p_·)`: each body's *point* `p_v` is the
  normal of the polar plane `p_v^⊥`, and the hinge `panelSupportExtensor p_u p_v` is the polar of
  the pencil line `p_u ∧ p_v`, so its row rank is the rank of the point-join framework the pencil
  motives carry (the complement isomorphism is an invertible map of the screw space;
  `BodyHingeFramework.finrank_span_rigidityRows_mapSupport`; the conversion is
  `finrank_span_rigidityRows_pencilConfigFramework`, CARRIER's C4). It is
  nonzero at every link as soon as the picture points differ. `ofNormals` at the *plane normals*
  would be the wrong rank: adjacent planes coincide on the whole fibre whenever the two bodies lie
  in a common planar-rigid subgraph ((MC-13)(c), e.g. every triangle edge at a generic picture,
  and every edge at a flat configuration), `panelSupportExtensor n n = 0` there, and a zero hinge
  welds its bodies (its hinge-row block is every functional).
* **Fibre-openness is part of `X0Attains`.** The generic motive intersects the attaining heights
  with the nondegenerate ones inside one fibre `L(q)` ((MC-133)(ii)), so `X0Attains` carries a
  nonempty Zariski-open set of attaining heights over each good picture, not one height; the
  semicontinuity is proved once, in `Graph.x0Attains_of_exists` (slice C1b).
* **`U` is a definition** (`Graph.IsMainPicture`): a witness over a picture of non-minimal fibre
  dimension need not lie in `X₀`, so the C1b witness must sit over `U`.

See `notes/Phase40b.md` (*Decisions made*, 2026-09-26 C1a) and `notes/Phase40-design.md` §3.
-/

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K]
variable {α β : Type*}

/-! ## Planar pictures and admissibility -/

/-- **The homogeneous picture point** (`def:pencil-admissible-picture`; Phase 40b CARRIER): the
point `(x_w, y_w, 1) ∈ K³` of the planar picture `q` at body `w`. Three picture points are
collinear exactly when their homogeneous points are linearly dependent. -/
def pencilPicturePoint (q : α × Fin 2 → K) (w : α) : Fin 3 → K :=
  ![q (w, 0), q (w, 1), 1]

/-- **An admissible planar picture** (`def:pencil-admissible-picture`; Phase 40b CARRIER, informal
(MC-1)). The picture `q` puts adjacent bodies at distinct points of `K²`, and at every body `v` of
`G` three members of the closed neighbourhood `G.closedNbhd v` have linearly independent
homogeneous picture points, i.e. the picture points over the closed neighbourhood are not
collinear. The triple form is the one the plane normal (`pencilNormalOfPicture`, via
`cross₃_ne_zero_iff_linearIndependent`) and the openness of admissibility (one `3 × 3`
determinant per body) consume directly. -/
def _root_.Graph.IsAdmissiblePicture (G : Graph α β) (q : α × Fin 2 → K) : Prop :=
  (∀ e u v, G.IsLink e u v → pencilPicturePoint q u ≠ pencilPicturePoint q v) ∧
  ∀ v ∈ V(G), ∃ t : Fin 3 → α, (∀ i, t i ∈ G.closedNbhd v) ∧
    LinearIndependent K (fun i => pencilPicturePoint q (t i))

/-! ## The lifting space -/

/-- **The lifting space `L(q)`** (`def:pencil-lifting-space`; Phase 40b CARRIER, informal (MC-1)).
The heights `z : α → K` that vanish off `V(G)` and, at every body `v` of `G`, restrict on the
closed neighbourhood `G.closedNbhd v` to an affine function of the picture: some `h : Fin 3 → K`
has `z w = h ⬝ᵥ (x_w, y_w, 1)` for every `w` in the neighbourhood. Over an admissible picture
these are exactly the heights for which every closed neighbourhood of the configuration
`(q, z)` is coplanar. Vanishing off `V(G)` makes `L(q)` the space of heights on `V(G)` itself,
so its dimension is the honest one for any `G` inside `α`, spanning or not. -/
def _root_.Graph.liftingSpace (G : Graph α β) (q : α × Fin 2 → K) : Submodule K (α → K) where
  carrier := {z | (∀ w ∉ V(G), z w = 0) ∧
    ∀ v ∈ V(G), ∃ h : Fin 3 → K, ∀ w ∈ G.closedNbhd v, z w = h ⬝ᵥ pencilPicturePoint q w}
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ => ⟨0, fun _ _ => by simp⟩⟩
  add_mem' := by
    rintro z₁ z₂ ⟨hs₁, ha₁⟩ ⟨hs₂, ha₂⟩
    refine ⟨fun w hw => by simp [hs₁ w hw, hs₂ w hw], fun v hv => ?_⟩
    obtain ⟨h₁, hh₁⟩ := ha₁ v hv
    obtain ⟨h₂, hh₂⟩ := ha₂ v hv
    exact ⟨h₁ + h₂, fun w hw => by simp [hh₁ w hw, hh₂ w hw, add_dotProduct]⟩
  smul_mem' := by
    rintro c z ⟨hs, ha⟩
    refine ⟨fun w hw => by simp [hs w hw], fun v hv => ?_⟩
    obtain ⟨h, hh⟩ := ha v hv
    exact ⟨c • h, fun w hw => by simp [hh w hw, smul_dotProduct]⟩

/-- Membership in the lifting space, unfolded (`def:pencil-lifting-space`). -/
theorem _root_.Graph.mem_liftingSpace {G : Graph α β} {q : α × Fin 2 → K} {z : α → K} :
    z ∈ G.liftingSpace q ↔ (∀ w ∉ V(G), z w = 0) ∧
      ∀ v ∈ V(G), ∃ h : Fin 3 → K, ∀ w ∈ G.closedNbhd v, z w = h ⬝ᵥ pencilPicturePoint q w :=
  Iff.rfl

/-- **The main pictures `U`** (`def:pencil-main-picture`; Phase 40b CARRIER, informal (MC-2)): the
admissible pictures whose lifting space has the least dimension `ℓ₀` among all admissible
pictures. Over `U` the pairs `(q, z)` with `z ∈ L(q)` form a vector bundle whose closure is
`X₀`; a configuration over a picture of larger fibre dimension need not lie in `X₀`, which is why
the one-witness upgrade (`Graph.x0Attains_of_exists`) asks for its picture here. -/
def _root_.Graph.IsMainPicture (G : Graph α β) (q : α × Fin 2 → K) : Prop :=
  G.IsAdmissiblePicture q ∧ ∀ q' : α × Fin 2 → K, G.IsAdmissiblePicture q' →
    Module.finrank K (G.liftingSpace q) ≤ Module.finrank K (G.liftingSpace q')

/-! ## The globally affine heights `Aff(q)` -/

open Classical in
/-- **The affine lift map** (`def:pencil-lifting-space`; Phase 40b CARRIER slice C2): the linear
map sending a triple of affine coefficients `h : Fin 3 → K` to the height `w ↦ h ⬝ (x_w, y_w, 1)`
on `V(G)`, zero off `V(G)`. Its range is `Graph.affineLifts`. -/
noncomputable def _root_.Graph.affineLiftMap (G : Graph α β) (q : α × Fin 2 → K) :
    (Fin 3 → K) →ₗ[K] (α → K) where
  toFun h w := if w ∈ V(G) then h ⬝ᵥ pencilPicturePoint q w else 0
  map_add' h₁ h₂ := by funext w; by_cases hw : w ∈ V(G) <;> simp [hw, add_dotProduct]
  map_smul' c h := by funext w; by_cases hw : w ∈ V(G) <;> simp [hw, smul_dotProduct]

open Classical in
@[simp]
theorem _root_.Graph.affineLiftMap_apply (G : Graph α β) (q : α × Fin 2 → K) (h : Fin 3 → K)
    (w : α) :
    G.affineLiftMap q h w = if w ∈ V(G) then h ⬝ᵥ pencilPicturePoint q w else 0 :=
  rfl

/-- **The globally affine heights** `Aff(q)`, restricted to `V(G)` (`def:pencil-lifting-space`;
Phase 40b CARRIER slice C2): the heights `w ↦ h ⬝ (x_w, y_w, 1)` of a single triple of affine
coefficients `h : Fin 3 → K`, vanishing off `V(G)` exactly as `Graph.liftingSpace` does — the
range of `Graph.affineLiftMap`. -/
noncomputable def _root_.Graph.affineLifts (G : Graph α β) (q : α × Fin 2 → K) :
    Submodule K (α → K) :=
  LinearMap.range (G.affineLiftMap q)

/-- **`Aff(q) ⊆ L(q)`, at every picture** (`lem:pencil-lifting-space-affine`; Phase 40b CARRIER
slice C2). A single triple of affine coefficients `h` trivially restricts to an affine function
of the picture on every closed neighbourhood — the same `h` at every body of `G` — so no
admissibility hypothesis is needed. -/
theorem _root_.Graph.affineLifts_le_liftingSpace (G : Graph α β) (q : α × Fin 2 → K) :
    G.affineLifts q ≤ G.liftingSpace q := by
  rintro z ⟨h, rfl⟩
  refine ⟨fun w hw => by simp [hw], fun v hv => ⟨h, fun w hw => ?_⟩⟩
  have hwV : w ∈ V(G) := by
    rcases hw with rfl | ⟨e, he⟩
    · exact hv
    · exact he.right_mem
  simp [hwV]

/-- **`Aff(q)` is three-dimensional at an admissible picture** (`lem:pencil-lifting-space-affine`;
Phase 40b CARRIER slice C2, with `Graph.affineLifts_le_liftingSpace` giving `3 ≤ dim L(q)`). The
affine lift map is injective: admissibility gives, at some body `v₀` of `G`, three
closed-neighbourhood members (hence bodies of `G`) with linearly independent homogeneous picture
points, and a triple `h` in the kernel dots to zero against all three, forcing `h = 0` since that
`3 × 3` matrix is a unit. -/
theorem _root_.Graph.finrank_affineLifts [Finite α] {G : Graph α β} {q : α × Fin 2 → K}
    (hq : G.IsAdmissiblePicture q) (hV : V(G).Nonempty) :
    Module.finrank K (G.affineLifts q) = 3 := by
  classical
  have : Fintype α := Fintype.ofFinite α
  obtain ⟨v₀, hv₀⟩ := hV
  obtain ⟨t, ht, hli⟩ := hq.2 v₀ hv₀
  have hinj : Function.Injective (G.affineLiftMap q) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro h hh
    have htV : ∀ i, t i ∈ V(G) := fun i => by
      rcases ht i with rfl | ⟨e, he⟩
      · exact hv₀
      · exact he.right_mem
    have hunit : IsUnit (Matrix.of fun i => pencilPicturePoint q (t i)) :=
      Matrix.linearIndependent_rows_iff_isUnit.mp hli
    have hzero : (Matrix.of fun i => pencilPicturePoint q (t i)) *ᵥ h =
        (Matrix.of fun i => pencilPicturePoint q (t i)) *ᵥ 0 := by
      rw [Matrix.mulVec_zero]
      funext i
      have hhi := congr_fun hh (t i)
      simp only [Graph.affineLiftMap_apply, htV i, Pi.zero_apply] at hhi
      simp only [Matrix.mulVec, Matrix.of_apply, Pi.zero_apply]
      rwa [dotProduct_comm]
    exact Matrix.mulVec_injective_iff_isUnit.mpr hunit hzero
  rw [Graph.affineLifts, LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun]

/-- **`3 ≤ dim L(q)` at an admissible picture** (`lem:pencil-lifting-space-affine`; Phase 40b
CARRIER, hygiene: the C2 checklist ticked this but no declaration stated it until now).
Immediate from `Aff(q) ⊆ L(q)` (`Graph.affineLifts_le_liftingSpace`) and `dim Aff(q) = 3`
(`Graph.finrank_affineLifts`), via monotonicity of `finrank` on submodules
(`Submodule.finrank_mono`). -/
theorem _root_.Graph.three_le_finrank_liftingSpace [Finite α] {G : Graph α β}
    {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) (hV : V(G).Nonempty) :
    3 ≤ Module.finrank K (G.liftingSpace q) := by
  classical
  have : Fintype α := Fintype.ofFinite α
  rw [← G.finrank_affineLifts hq hV]
  exact Submodule.finrank_mono (G.affineLifts_le_liftingSpace q)

/-! ## Configuration points and plane normals -/

/-- **The homogeneous configuration point** (`def:pencil-configuration`; Phase 40b CARRIER): the
point `p_w = (x_w, y_w, z_w, 1) ∈ K⁴` of the configuration `(q, z)` at body `w`. It is affine in
the picture and height coordinates, and its first, second and fourth coordinates are the
homogeneous picture point (`pencilPicturePoint`). -/
def pencilConfigPoint (q : α × Fin 2 → K) (z : α → K) (w : α) : Fin 4 → K :=
  ![q (w, 0), q (w, 1), z w, 1]

/-- **The plane normal of a configuration** (`def:pencil-configuration`; Phase 40b CARRIER,
informal (MC-1)/(MC-3)): at body `v`, the `cross₃` of the configuration points of the three bodies
the selector `sel v` names — the normal of the plane through them, polynomial and
denominator-free in `(q, z)`. The selector is a plain triple of bodies, not an
`IsFin3SelectorOf`: a closed neighbourhood may have more than three members, and no slot may be
padded, since the normal must be read off the configuration. When the three bodies lie in
`G.closedNbhd v` with non-collinear picture points and `z ∈ L(q)`, this is (up to a nonzero
scalar) the normal of the plane carrying the whole closed neighbourhood (CARRIER's C3). -/
noncomputable def pencilNormalOfPicture (q : α × Fin 2 → K) (z : α → K) (sel : α → Fin 3 → α)
    (v : α) : Fin 4 → K :=
  cross₃ (pencilConfigPoint q z (sel v 0)) (pencilConfigPoint q z (sel v 1))
    (pencilConfigPoint q z (sel v 2))

/-! ## The general point of `X₀` attains -/

/-- **`X₀(G)`'s general point attains the deficiency rank** (`def:pencil-x0-attains`; Phase 40b
CARRIER, informal (MC-10)(a) in the two-level form of (MC-10)(b)). For some endpoint selector
`ends` recording every link of `G` and some nonzero polynomial `P` in the picture coordinates,
every picture `q` off the zero set of `P` is admissible, and the heights `z ∈ L(q)` at which the
configuration's row rank equals `6(|V(G)| − 1) − def₃(G)` contain a nonempty Zariski-open subset
of `L(q)`: the non-roots in `L(q)` of a polynomial `R` in the height coordinates, at least one of
which lies in `L(q)`.

The rank is that of `PanelHingeFramework.ofNormals G ends` at the configuration points (see the
module docstring: the polar of the point-join framework, same rank, nonzero hinges wherever
adjacent picture points differ). The fibre-open clause is what lets the generic motive intersect
the attaining heights with the nondegenerate ones inside a single fibre ((MC-133)(ii)); the
distinct motive uses only one attaining `(q, z)`.

`P ≠ 0` means "off a proper Zariski-closed set of pictures" only over an infinite field: over a
finite field a nonzero polynomial can vanish at every point (`X ^ |K| − X`), and `X0Attains` then
holds vacuously. The program works over an infinite field (`[Infinite K]`) throughout, so the
definition needs no such hypothesis of its own. -/
def _root_.Graph.X0Attains (K : Type*) [Field K] (G : Graph α β) : Prop :=
  ∃ (ends : β → α × α) (P : MvPolynomial (α × Fin 2) K),
    (∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2) ∧ P ≠ 0 ∧
    ∀ q : α × Fin 2 → K, MvPolynomial.eval q P ≠ 0 →
      G.IsAdmissiblePicture q ∧
      ∃ R : MvPolynomial α K, (∃ z ∈ G.liftingSpace q, MvPolynomial.eval z R ≠ 0) ∧
        ∀ z ∈ G.liftingSpace q, MvPolynomial.eval z R ≠ 0 →
          (Module.finrank K (Submodule.span K
            (PanelHingeFramework.ofNormals (k := 2) G ends
              (fun p => pencilConfigPoint q z p.1 p.2)).toBodyHinge.rigidityRows) : ℤ)
            = screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency 3

/-! ## The hinges of a configuration over an admissible picture -/

/-- **Configuration points over distinct picture points are independent** (Phase 40b CARRIER).
Two configuration points `p_u = (x_u, y_u, z_u, 1)` and `p_v = (x_v, y_v, z_v, 1)` whose picture
points differ are linearly independent, whatever the heights: a relation `s p_u + t p_v = 0` has
`s + t = 0` in the last coordinate, so `s (q_u − q_v) = 0` in the picture coordinates. -/
theorem linearIndependent_pencilConfigPoint_pair {q : α × Fin 2 → K} (z : α → K) {u v : α}
    (huv : pencilPicturePoint q u ≠ pencilPicturePoint q v) :
    LinearIndependent K ![pencilConfigPoint q z u, pencilConfigPoint q z v] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h0 : s * q (u, 0) + t * q (v, 0) = 0 := by simpa [pencilConfigPoint] using congr_fun hst 0
  have h1 : s * q (u, 1) + t * q (v, 1) = 0 := by simpa [pencilConfigPoint] using congr_fun hst 1
  have h3 : s + t = 0 := by simpa [pencilConfigPoint] using congr_fun hst 3
  have hs : s = 0 := by
    by_contra hs
    apply huv
    funext i
    fin_cases i
    · have : s * (q (u, 0) - q (v, 0)) = 0 := by linear_combination h0 - q (v, 0) * h3
      simpa [pencilPicturePoint, hs, sub_eq_zero] using this
    · have : s * (q (u, 1) - q (v, 1)) = 0 := by linear_combination h1 - q (v, 1) * h3
      simpa [pencilPicturePoint, hs, sub_eq_zero] using this
    · simp [pencilPicturePoint]
  exact ⟨hs, by rwa [hs, zero_add] at h3⟩

/-- **Distinct picture points are independent** (Phase 40c FLAT). Two homogeneous picture points
`(x_u, y_u, 1)` and `(x_v, y_v, 1)` that differ are linearly independent: a relation
`s p̂_u + t p̂_v = 0` has `s + t = 0` in the last coordinate, so `s (q_u − q_v) = 0`. -/
theorem linearIndependent_pencilPicturePoint_pair {q : α × Fin 2 → K} {u v : α}
    (huv : pencilPicturePoint q u ≠ pencilPicturePoint q v) :
    LinearIndependent K ![pencilPicturePoint q u, pencilPicturePoint q v] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h0 : s * q (u, 0) + t * q (v, 0) = 0 := by simpa [pencilPicturePoint] using congr_fun hst 0
  have h1 : s * q (u, 1) + t * q (v, 1) = 0 := by simpa [pencilPicturePoint] using congr_fun hst 1
  have h2 : s + t = 0 := by simpa [pencilPicturePoint] using congr_fun hst 2
  have hs : s = 0 := by
    by_contra hs
    apply huv
    funext i
    fin_cases i
    · have : s * (q (u, 0) - q (v, 0)) = 0 := by linear_combination h0 - q (v, 0) * h2
      simpa [pencilPicturePoint, hs, sub_eq_zero] using this
    · have : s * (q (u, 1) - q (v, 1)) = 0 := by linear_combination h1 - q (v, 1) * h2
      simpa [pencilPicturePoint, hs, sub_eq_zero] using this
    · simp [pencilPicturePoint]
  exact ⟨hs, by rwa [hs, zero_add] at h2⟩

/-- **The hinges of a configuration over an admissible picture are nonzero** (Phase 40b CARRIER;
the first clause of slice C4). Over an admissible picture `q`, at every height `z`, the framework
`ofNormals G ends` at the configuration points has a nonzero support extensor at every link: the
extensor is nonzero exactly when the two endpoint points are independent
(`PanelHingeFramework.toBodyHinge_supportExtensor_ne_zero_iff`), and adjacent picture points
differ (`linearIndependent_pencilConfigPoint_pair`). -/
theorem _root_.Graph.IsAdmissiblePicture.supportExtensor_ne_zero {G : Graph α β}
    {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) {ends : β → α × α}
    (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2) (z : α → K)
    {e : β} {u v : α} (he : G.IsLink e u v) :
    (PanelHingeFramework.ofNormals (k := 2) G ends
      (fun p => pencilConfigPoint q z p.1 p.2)).toBodyHinge.supportExtensor e ≠ 0 := by
  rw [PanelHingeFramework.toBodyHinge_supportExtensor_ne_zero_iff]
  exact linearIndependent_pencilConfigPoint_pair z (hq.1 e _ _ (hends e u v he))

/-! ## Admissibility is Zariski-open -/

/-- **The homogeneous picture point as polynomials** (Phase 40b CARRIER): the vector
`(X_{w,0}, X_{w,1}, 1)` of polynomials in the picture coordinates, evaluating to
`pencilPicturePoint q w` (`eval_pencilPicturePointPoly`). -/
noncomputable def pencilPicturePointPoly (w : α) : Fin 3 → MvPolynomial (α × Fin 2) K :=
  ![MvPolynomial.X (w, 0), MvPolynomial.X (w, 1), 1]

@[simp]
theorem eval_pencilPicturePointPoly (q : α × Fin 2 → K) (w : α) (i : Fin 3) :
    MvPolynomial.eval q (pencilPicturePointPoly w i) = pencilPicturePoint q w i := by
  fin_cases i <;> simp [pencilPicturePointPoly, pencilPicturePoint]

/-- **Admissibility is Zariski-open** (`def:pencil-admissible-picture`; Phase 40b CARRIER). Around
an admissible picture `q₀` there is a polynomial `P` in the picture coordinates, nonzero at `q₀`,
off whose zero set every picture is admissible: `P` is the product of one coordinate difference
per adjacent pair (a coordinate in which the two picture points of `q₀` differ) and one `3 × 3`
determinant per body (of the homogeneous picture points of a triple `q₀` makes independent). -/
theorem _root_.Graph.IsAdmissiblePicture.exists_mvPolynomial [Finite α] {G : Graph α β}
    {q₀ : α × Fin 2 → K} (hq₀ : G.IsAdmissiblePicture q₀) :
    ∃ P : MvPolynomial (α × Fin 2) K, MvPolynomial.eval q₀ P ≠ 0 ∧
      ∀ q, MvPolynomial.eval q P ≠ 0 → G.IsAdmissiblePicture q := by
  classical
  have : Fintype α := Fintype.ofFinite α
  -- One independent triple per body, from `q₀`.
  have htr : ∀ v, ∃ t : Fin 3 → α, v ∈ V(G) →
      (∀ i, t i ∈ G.closedNbhd v) ∧ LinearIndependent K (fun i => pencilPicturePoint q₀ (t i)) := by
    intro v
    by_cases hv : v ∈ V(G)
    · obtain ⟨t, ht⟩ := hq₀.2 v hv
      exact ⟨t, fun _ => ht⟩
    · exact ⟨fun _ => v, fun h => absurd h hv⟩
  choose t ht using htr
  -- The per-pair coordinate difference and the per-body determinant.
  set link : α → α → MvPolynomial (α × Fin 2) K := fun u v =>
    if q₀ (u, 0) = q₀ (v, 0) then MvPolynomial.X (u, 1) - MvPolynomial.X (v, 1)
    else MvPolynomial.X (u, 0) - MvPolynomial.X (v, 0) with hlink
  set det : α → MvPolynomial (α × Fin 2) K := fun v =>
    (Matrix.of fun i j => pencilPicturePointPoly (t v i) j).det with hdetdef
  have hli : ∀ q v, LinearIndependent K (fun i => pencilPicturePoint q (t v i)) ↔
      MvPolynomial.eval q (det v) ≠ 0 := by
    intro q v
    have hdet : MvPolynomial.eval q (det v) =
        (Matrix.of fun i j => pencilPicturePoint q (t v i) j).det := by
      rw [hdetdef, RingHom.map_det, RingHom.mapMatrix_apply]
      congr 1
      ext i j
      simp
    rw [hdet, ← Matrix.linearIndependent_rows_iff_det_ne_zero]
    rfl
  refine ⟨(∏ p : α × α, if G.Adj p.1 p.2 then link p.1 p.2 else 1) *
      ∏ v : α, if v ∈ V(G) then det v else 1, ?_, ?_⟩
  · rw [map_mul, map_prod, map_prod]
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun p _ => ?_)
      (Finset.prod_ne_zero_iff.mpr fun v _ => ?_)
    · split_ifs with hadj
      · obtain ⟨e, he⟩ := hadj
        have hne := hq₀.1 e _ _ he
        rw [hlink]
        dsimp only
        split_ifs with h0
        · simp only [map_sub, MvPolynomial.eval_X, sub_ne_zero]
          intro h1
          apply hne
          funext i
          fin_cases i <;> simp [pencilPicturePoint, h0, h1]
        · simpa [sub_eq_zero] using h0
      · simp
    · split_ifs with hv
      · exact (hli q₀ v).mp (ht v hv).2
      · simp
  · intro q hq
    rw [map_mul, map_prod, map_prod] at hq
    have h1 := Finset.prod_ne_zero_iff.mp (left_ne_zero_of_mul hq)
    have h2 := Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hq)
    refine ⟨fun e u v he => ?_, fun v hv => ⟨t v, (ht v hv).1, (hli q v).mpr ?_⟩⟩
    · have hl := h1 (u, v) (Finset.mem_univ _)
      rw [ite_eq_left he.adj, hlink] at hl
      dsimp only at hl
      intro huv
      split_ifs at hl
      · exact hl (by simpa [pencilPicturePoint, sub_eq_zero] using congr_fun huv 1)
      · exact hl (by simpa [pencilPicturePoint, sub_eq_zero] using congr_fun huv 0)
    · have hd := h2 v (Finset.mem_univ _)
      rwa [ite_eq_left hv] at hd

/-! ## The lifting system -/

open Classical in
/-- **The lifting system** (Phase 40b CARRIER; the matrix `M(q)` of informal (MC-1)/(MC-2)): a
matrix of polynomials in the picture coordinates whose kernel at a picture `q` is the space of
pairs `(z, h)` of a height `z` and per-body affine coefficients `h_v ∈ K³` with `z` vanishing off
`V(G)`, `z_w = h_v ⬝ (x_w, y_w, 1)` on every closed neighbourhood, and `h_v = 0` off `V(G)`
(`Graph.liftingMatrix_mulVec_eq_zero_iff`). Its height projection is the lifting space
(`Graph.map_ker_liftingMatrix`), isomorphically over an admissible picture
(`Graph.finrank_ker_liftingMatrix`). Rows: support rows for the heights, one affine row per
`(v, w)` (zero unless `w` lies in the closed neighbourhood of a body `v`), support rows for the
coefficients. Entries are constants or `-X`, so the kernel varies polynomially with `q`. -/
noncomputable def _root_.Graph.liftingMatrix (K : Type*) [Field K] (G : Graph α β) :
    Matrix (α ⊕ (α × α) ⊕ (α × Fin 3)) (α ⊕ (α × Fin 3)) (MvPolynomial (α × Fin 2) K) :=
  Matrix.of fun r c => match r, c with
    | Sum.inl w, Sum.inl u => if w ∉ V(G) then (if u = w then 1 else 0) else 0
    | Sum.inl _, Sum.inr _ => 0
    | Sum.inr (Sum.inl (v, w)), Sum.inl u =>
        if v ∈ V(G) ∧ w ∈ G.closedNbhd v then (if u = w then 1 else 0) else 0
    | Sum.inr (Sum.inl (v, w)), Sum.inr (v', i) =>
        if v ∈ V(G) ∧ w ∈ G.closedNbhd v then
          (if v' = v then -pencilPicturePointPoly w i else 0) else 0
    | Sum.inr (Sum.inr _), Sum.inl _ => 0
    | Sum.inr (Sum.inr (v, i)), Sum.inr (v', i') =>
        if v ∉ V(G) then (if v' = v ∧ i' = i then 1 else 0) else 0


/-- **The kernel of the lifting system** (Phase 40b CARRIER): at a picture `q`, a pair `x = (z, h)`
lies in the kernel of the lifting system exactly when `z` vanishes off `V(G)`, restricts on every
closed neighbourhood of a body `v` to the affine function with coefficients `h_v`, and `h`
vanishes off `V(G)`. -/
theorem _root_.Graph.liftingMatrix_mulVec_eq_zero_iff [Fintype α] {G : Graph α β}
    {q : α × Fin 2 → K} {x : α ⊕ (α × Fin 3) → K} :
    (G.liftingMatrix K).map (MvPolynomial.eval q) *ᵥ x = 0 ↔
      (∀ w ∉ V(G), x (Sum.inl w) = 0) ∧
      (∀ v ∈ V(G), ∀ w ∈ G.closedNbhd v,
        x (Sum.inl w) = (fun i => x (Sum.inr (v, i))) ⬝ᵥ pencilPicturePoint q w) ∧
      ∀ v ∉ V(G), ∀ i, x (Sum.inr (v, i)) = 0 := by
  classical
  set M := (G.liftingMatrix K).map (MvPolynomial.eval q) with hM
  have hr1 : ∀ w, (M *ᵥ x) (Sum.inl w) = if w ∉ V(G) then x (Sum.inl w) else 0 := by
    intro w
    by_cases hw : w ∈ V(G) <;>
      simp [hM, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Graph.liftingMatrix, hw]
  have hr2 : ∀ v w, (M *ᵥ x) (Sum.inr (Sum.inl (v, w))) =
      if v ∈ V(G) ∧ w ∈ G.closedNbhd v then
        x (Sum.inl w) - (fun i => x (Sum.inr (v, i))) ⬝ᵥ pencilPicturePoint q w else 0 := by
    intro v w
    by_cases hc : v ∈ V(G) ∧ w ∈ G.closedNbhd v
    · simp [hM, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type,
        Graph.liftingMatrix, hc, apply_ite (MvPolynomial.eval q), mul_ite, Finset.sum_ite_irrel,
        sub_eq_add_neg, mul_comm]
    · simp [hM, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Graph.liftingMatrix, hc]
  have hr3 : ∀ v i, (M *ᵥ x) (Sum.inr (Sum.inr (v, i))) =
      if v ∉ V(G) then x (Sum.inr (v, i)) else 0 := by
    intro v i
    by_cases hv : v ∈ V(G) <;>
      simp [hM, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type,
        Graph.liftingMatrix, hv, ite_and, apply_ite (MvPolynomial.eval q), ite_mul,
        Finset.sum_ite_irrel]
  rw [funext_iff]
  constructor
  · intro h
    refine ⟨fun w hw => ?_, fun v hv w hw => ?_, fun v hv i => ?_⟩
    · simpa [hr1, hw] using h (Sum.inl w)
    · have := h (Sum.inr (Sum.inl (v, w)))
      rw [hr2, ite_eq_left ⟨hv, hw⟩, Pi.zero_apply, sub_eq_zero] at this
      exact this
    · simpa [hr3, hv] using h (Sum.inr (Sum.inr (v, i)))
  · rintro ⟨h1, h2, h3⟩ (w | ⟨v, w⟩ | ⟨v, i⟩)
    · rw [hr1]; split_ifs with hw
      · rfl
      · exact h1 w hw
    · rw [hr2]; split_ifs with hc
      · rw [h2 v hc.1 w hc.2, sub_self]; rfl
      · rfl
    · rw [hr3]; split_ifs with hv
      · rfl
      · exact h3 v hv i

/-- **The lifting space is the height projection of the lifting system's kernel** (Phase 40b
CARRIER): at every picture `q`, projecting the kernel of the lifting system to its height
coordinates gives exactly `L(q)`. -/
theorem _root_.Graph.map_ker_liftingMatrix [Fintype α] (G : Graph α β) (q : α × Fin 2 → K) :
    (LinearMap.ker ((G.liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin).map
      (LinearMap.funLeft K K Sum.inl) = G.liftingSpace q := by
  classical
  ext z
  simp only [Submodule.mem_map, LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨h1, h2, -⟩ := Graph.liftingMatrix_mulVec_eq_zero_iff.mp hx
    exact ⟨h1, fun v hv => ⟨_, h2 v hv⟩⟩
  · rintro ⟨h1, h2⟩
    choose! h hh using h2
    refine ⟨Sum.elim z (fun p => if p.1 ∈ V(G) then h p.1 p.2 else 0), ?_, rfl⟩
    rw [Graph.liftingMatrix_mulVec_eq_zero_iff]
    refine ⟨h1, fun v hv w hw => ?_, fun v hv i => by simp [hv]⟩
    simpa [hv] using hh v hv w hw

/-- **Over an admissible picture the lifting system's kernel has the lifting space's dimension**
(Phase 40b CARRIER): the height projection is injective on the kernel, since three independent
homogeneous picture points in each closed neighbourhood pin the affine coefficients down. -/
theorem _root_.Graph.finrank_ker_liftingMatrix [Fintype α] {G : Graph α β} {q : α × Fin 2 → K}
    (hq : G.IsAdmissiblePicture q) :
    Module.finrank K (LinearMap.ker ((G.liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin) =
      Module.finrank K (G.liftingSpace q) := by
  classical
  rw [← G.map_ker_liftingMatrix q, ← LinearMap.range_domRestrict]
  refine (LinearMap.finrank_range_of_inj ?_).symm
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨x, hx⟩ hx0
  have hz : ∀ w, x (Sum.inl w) = 0 := fun w => congr_fun hx0 w
  obtain ⟨-, h2, h3⟩ := Graph.liftingMatrix_mulVec_eq_zero_iff.mp hx
  refine Subtype.ext (funext fun c => ?_)
  rcases c with w | ⟨v, i⟩
  · exact hz w
  · by_cases hv : v ∈ V(G)
    · obtain ⟨t, ht, hli⟩ := hq.2 v hv
      -- the coefficient vector is orthogonal to three independent vectors of `K³`
      have hunit : IsUnit (Matrix.of fun j => pencilPicturePoint q (t j)) :=
        Matrix.linearIndependent_rows_iff_isUnit.mp hli
      have hzero : (Matrix.of fun j => pencilPicturePoint q (t j)) *ᵥ
          (fun i => x (Sum.inr (v, i))) = (Matrix.of fun j => pencilPicturePoint q (t j)) *ᵥ 0 := by
        rw [Matrix.mulVec_zero]
        funext j
        simp only [Matrix.mulVec, Matrix.of_apply, Pi.zero_apply]
        rw [dotProduct_comm, ← h2 v hv (t j) (ht j), hz]
      exact congr_fun (Matrix.mulVec_injective_iff_isUnit.mpr hunit hzero) i
    · exact h3 v hv i

/-! ## The lifting system with weights -/

open Classical in
/-- **The lifting system with weights** (`def:pencil-weighted-lifting-system`; Phase 40f
CONTRACT-R): `Graph.liftingMatrix` with an arbitrary polynomial weight point `ω v w ∈ K[σ]³` in
place of the homogeneous picture point `(x_w, y_w, 1)`. Its rows say `z_w = h_v ⬝ ω(v, w)` for `w`
in the closed neighbourhood of a body `v`, plus the support rows for the heights and the
coefficients (`Graph.weightedLiftingMatrix_mulVec_eq_zero_iff`). The contraction step reads the
closed neighbourhoods meeting the core through other vectors than the picture points
(`Graph.contractLiftingMatrix`). -/
noncomputable def _root_.Graph.weightedLiftingMatrix {σ : Type*} (K : Type*) [Field K]
    (G : Graph α β) (ω : α → α → Fin 3 → MvPolynomial σ K) :
    Matrix (α ⊕ (α × α) ⊕ (α × Fin 3)) (α ⊕ (α × Fin 3)) (MvPolynomial σ K) :=
  Matrix.of fun ρ c => match ρ, c with
    | Sum.inl w, Sum.inl u => if w ∉ V(G) then (if u = w then 1 else 0) else 0
    | Sum.inl _, Sum.inr _ => 0
    | Sum.inr (Sum.inl (v, w)), Sum.inl u =>
        if v ∈ V(G) ∧ w ∈ G.closedNbhd v then (if u = w then 1 else 0) else 0
    | Sum.inr (Sum.inl (v, w)), Sum.inr (v', i) =>
        if v ∈ V(G) ∧ w ∈ G.closedNbhd v then
          (if v' = v then -ω v w i else 0) else 0
    | Sum.inr (Sum.inr _), Sum.inl _ => 0
    | Sum.inr (Sum.inr (v, i)), Sum.inr (v', i') =>
        if v ∉ V(G) then (if v' = v ∧ i' = i then 1 else 0) else 0

/-- **The kernel of the lifting system with weights**: at a point `s` of the parameters, a pair
`x = (z, h)` lies in the kernel exactly when `z` vanishes off `V(G)`, `z_w = h_v ⬝ ω(v, w)(s)` on
every closed neighbourhood of a body `v`, and `h` vanishes off `V(G)`. -/
theorem _root_.Graph.weightedLiftingMatrix_mulVec_eq_zero_iff {σ : Type*} [Fintype α]
    {G : Graph α β} {ω : α → α → Fin 3 → MvPolynomial σ K} {s : σ → K}
    {x : α ⊕ (α × Fin 3) → K} :
    (G.weightedLiftingMatrix K ω).map (MvPolynomial.eval s) *ᵥ x = 0 ↔
      (∀ w ∉ V(G), x (Sum.inl w) = 0) ∧
      (∀ v ∈ V(G), ∀ w ∈ G.closedNbhd v,
        x (Sum.inl w) = (fun i => x (Sum.inr (v, i))) ⬝ᵥ (fun i => MvPolynomial.eval s (ω v w i)))
      ∧ ∀ v ∉ V(G), ∀ i, x (Sum.inr (v, i)) = 0 := by
  classical
  set M := (G.weightedLiftingMatrix K ω).map (MvPolynomial.eval s) with hM
  have hr1 : ∀ w, (M *ᵥ x) (Sum.inl w) = if w ∉ V(G) then x (Sum.inl w) else 0 := by
    intro w
    by_cases hw : w ∈ V(G) <;>
      simp [hM, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Graph.weightedLiftingMatrix, hw]
  have hr2 : ∀ v w, (M *ᵥ x) (Sum.inr (Sum.inl (v, w))) =
      if v ∈ V(G) ∧ w ∈ G.closedNbhd v then
        x (Sum.inl w) - (fun i => x (Sum.inr (v, i))) ⬝ᵥ
          (fun i => MvPolynomial.eval s (ω v w i)) else 0 := by
    intro v w
    by_cases hc : v ∈ V(G) ∧ w ∈ G.closedNbhd v
    · simp [hM, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type,
        Graph.weightedLiftingMatrix, hc, apply_ite (MvPolynomial.eval s), mul_ite,
        Finset.sum_ite_irrel, sub_eq_add_neg, mul_comm]
    · simp [hM, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Graph.weightedLiftingMatrix, hc]
  have hr3 : ∀ v i, (M *ᵥ x) (Sum.inr (Sum.inr (v, i))) =
      if v ∉ V(G) then x (Sum.inr (v, i)) else 0 := by
    intro v i
    by_cases hv : v ∈ V(G) <;>
      simp [hM, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type,
        Graph.weightedLiftingMatrix, hv, ite_and, apply_ite (MvPolynomial.eval s), ite_mul,
        Finset.sum_ite_irrel]
  rw [funext_iff]
  constructor
  · intro h
    refine ⟨fun w hw => ?_, fun v hv w hw => ?_, fun v hv i => ?_⟩
    · simpa [hr1, hw] using h (Sum.inl w)
    · have := h (Sum.inr (Sum.inl (v, w)))
      rw [hr2, ite_eq_left ⟨hv, hw⟩, Pi.zero_apply, sub_eq_zero] at this
      exact this
    · simpa [hr3, hv] using h (Sum.inr (Sum.inr (v, i)))
  · rintro ⟨h1, h2, h3⟩ (w | ⟨v, w⟩ | ⟨v, i⟩)
    · rw [hr1]; split_ifs with hw
      · rfl
      · exact h1 w hw
    · rw [hr2]; split_ifs with hc
      · rw [h2 v hc.1 w hc.2, sub_self]; rfl
      · rfl
    · rw [hr3]; split_ifs with hv
      · rfl
      · exact h3 v hv i


/-! ## One attaining configuration over a main picture forces the general one -/

/-- **One attaining configuration over a main picture forces the general one**
(`lem:pencil-x0-one-witness`; Phase 40b CARRIER slice C1b, the semicontinuity half of informal
(MC-2)/(MC-10)). If a configuration `(q₀, z₀)` with `q₀` a main picture and `z₀ ∈ L(q₀)` has row
rank at least `6(|V(G)| − 1) − def₃(G)`, then the general configuration of `G` attains
(`Graph.X0Attains`).

Proof. Admissibility is open at `q₀` (`Graph.IsAdmissiblePicture.exists_mvPolynomial`). The
lifting space is the height projection of the kernel of the lifting system `M(q)`
(`Graph.map_ker_liftingMatrix`), of the same dimension over admissible pictures
(`Graph.finrank_ker_liftingMatrix`), so at a main `q₀` the kernel dimension is least among
admissible pictures, and Cramer's rule gives a polynomial section `Z(q)` of the kernel with
`Z(q₀)` over `z₀` (`Matrix.exists_mvPolynomial_section_mulVec_eq_zero`). The rank device
(`PanelHingeFramework.exists_rankPolynomial_of_le_finrank_linking`, hinges nonzero by
`Graph.IsAdmissiblePicture.supportExtensor_ne_zero`) gives a polynomial `Q` at the configuration
points whose non-vanishing forces the rank lower bound. Then `P` = admissibility · the section's
determinant · `Q` at the configuration `(q, Z(q))`, and `R` = `Q` at `(q, ·)`; the rank never
exceeds the target once every hinge is nonzero
(`BodyHingeFramework.finrank_span_rigidityRows_add_deficiency_le`). -/
theorem _root_.Graph.x0Attains_of_exists [Finite α] [Finite β] {G : Graph α β}
    (hV : V(G).Nonempty) (ends : β → α × α)
    (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2)
    {q₀ : α × Fin 2 → K} (hq₀ : G.IsMainPicture q₀) {z₀ : α → K} (hz₀ : z₀ ∈ G.liftingSpace q₀)
    (hrank : screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency 3 ≤
      (Module.finrank K (Submodule.span K
        (PanelHingeFramework.ofNormals (k := 2) G ends
          (fun p => pencilConfigPoint q₀ z₀ p.1 p.2)).toBodyHinge.rigidityRows) : ℤ)) :
    G.X0Attains K := by
  classical
  have : Fintype α := Fintype.ofFinite α
  -- The rank polynomial at the witness configuration.
  obtain ⟨Q, hQ₀, hQ⟩ := PanelHingeFramework.exists_rankPolynomial_of_le_finrank_linking G ends
    hends (q₀ := fun p => pencilConfigPoint q₀ z₀ p.1 p.2)
    (fun e he => hq₀.1.supportExtensor_ne_zero hends z₀ he) (Int.toNat_le.mpr hrank)
  -- Admissibility near `q₀`.
  obtain ⟨Padm, hPadm₀, hPadm⟩ := hq₀.1.exists_mvPolynomial
  -- Lift `z₀` to the lifting system's kernel and take a polynomial section through it.
  rw [← G.map_ker_liftingMatrix q₀] at hz₀
  obtain ⟨x₀, hx₀, hx₀z⟩ := hz₀
  obtain ⟨D, Z, hD₀, hZ₀, -, hZ⟩ :=
    Matrix.exists_mvPolynomial_section_mulVec_eq_zero (G.liftingMatrix K) hx₀
  -- `Q` at the configuration of the section, as a polynomial in the picture.
  set Qsec : MvPolynomial (α × Fin 2) K := MvPolynomial.bind₁ (fun p : α × Fin 4 =>
    ![MvPolynomial.X (p.1, 0), MvPolynomial.X (p.1, 1), Z (Sum.inl p.1), 1] p.2) Q with hQsecdef
  have hQsec : ∀ q, MvPolynomial.eval q Qsec = MvPolynomial.eval
      (fun p => pencilConfigPoint q (fun w => MvPolynomial.eval q (Z (Sum.inl w))) p.1 p.2) Q := by
    intro q
    rw [hQsecdef, MvPolynomial.eval_bind₁]
    congr 2
    funext ⟨w, j⟩
    fin_cases j <;> simp [pencilConfigPoint]
  refine ⟨ends, Padm * D * Qsec, hends, fun h0 => ?_, fun q hq => ?_⟩
  · -- `P(q₀) ≠ 0`: the section passes through `z₀`.
    have hZz₀ : (fun w => MvPolynomial.eval q₀ (Z (Sum.inl w))) = z₀ := by
      rw [← hx₀z]
      funext w
      exact congr_fun hZ₀ (Sum.inl w)
    have h := congrArg (MvPolynomial.eval q₀) h0
    rw [map_mul, map_mul, hQsec, hZz₀, map_zero] at h
    exact mul_ne_zero (mul_ne_zero hPadm₀ hD₀) hQ₀ h
  · rw [map_mul, map_mul] at hq
    have hadm := hPadm q (left_ne_zero_of_mul (left_ne_zero_of_mul hq))
    have hQq := right_ne_zero_of_mul hq
    rw [hQsec] at hQq
    have hdim : Module.finrank K
          (LinearMap.ker ((G.liftingMatrix K).map (MvPolynomial.eval q₀)).mulVecLin) ≤
        Module.finrank K
          (LinearMap.ker ((G.liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin) := by
      rw [Graph.finrank_ker_liftingMatrix hq₀.1, Graph.finrank_ker_liftingMatrix hadm]
      exact hq₀.2 q hadm
    have hmem : (fun w => MvPolynomial.eval q (Z (Sum.inl w))) ∈ G.liftingSpace q := by
      rw [← G.map_ker_liftingMatrix q]
      exact ⟨_, hZ q hdim (right_ne_zero_of_mul (left_ne_zero_of_mul hq)), rfl⟩
    -- `Q` at the configurations `(q, ·)`, as a polynomial in the heights.
    set R : MvPolynomial α K := MvPolynomial.bind₁ (fun p : α × Fin 4 =>
      ![MvPolynomial.C (q (p.1, 0)), MvPolynomial.C (q (p.1, 1)), MvPolynomial.X p.1, 1] p.2) Q
      with hRdef
    have hR : ∀ z, MvPolynomial.eval z R =
        MvPolynomial.eval (fun p => pencilConfigPoint q z p.1 p.2) Q := by
      intro z
      rw [hRdef, MvPolynomial.eval_bind₁]
      congr 2
      funext ⟨w, j⟩
      fin_cases j <;> simp [pencilConfigPoint]
    refine ⟨hadm, R, ⟨_, hmem, by rwa [hR]⟩, fun z _ hRz => ?_⟩
    rw [hR] at hRz
    have hup := BodyHingeFramework.finrank_span_rigidityRows_add_deficiency_le
      (PanelHingeFramework.ofNormals (k := 2) G ends
        (fun p => pencilConfigPoint q z p.1 p.2)).toBodyHinge
      (n := 3) (Graph.bodyBarDim_eq_screwDim_sub_one (by norm_num)) hV
      (fun e u v he => hadm.supportExtensor_ne_zero hends z he)
    exact le_antisymm hup ((Int.self_le_toNat _).trans (by exact_mod_cast hQ _ hRz))

/-! ## An admissible picture exists -/

/-- **Three points on a parabola at pairwise distinct parameters are not collinear** (Phase 40b
CARRIER slice C2). The `3 × 3` determinant of `(a, a², 1)`, `(b, b², 1)`, `(c, c², 1)` is the
permuted Vandermonde product `(b − a)(a − c)(b − c)`. -/
private theorem det_moment_curve_triple (a b c : K) :
    (Matrix.of ![![a, a ^ 2, 1], ![b, b ^ 2, 1], ![c, c ^ 2, 1]] : Matrix (Fin 3) (Fin 3) K).det
      = (b - a) * (a - c) * (b - c) := by
  simp [Matrix.det_fin_three]
  ring

/-- **An admissible planar picture exists** (Phase 40b CARRIER slice C2), when `G` is loopless and
every closed neighbourhood has at least three members (both consequences of simplicity and minimum
degree two). The moment curve `w ↦ (φ w, φ w ^ 2)` at an injective `φ : α → K` (composing a
`Fintype` enumeration of `α`, `Fin.valEmbedding`, and `Infinite.natEmbedding K`) puts every pair of
distinct bodies at distinct points, and any three distinct members of a closed neighbourhood (a
three-element subset, `Set.exists_subset_card_eq` then `Set.ncard_eq_three`) at non-collinear
points (`det_moment_curve_triple`, nonzero since `φ` is injective on the three pairwise-distinct
members). -/
theorem _root_.Graph.exists_isAdmissiblePicture [Infinite K] [Finite α] {G : Graph α β}
    (hloop : G.Loopless) (h3 : ∀ v ∈ V(G), 3 ≤ (G.closedNbhd v).ncard) :
    ∃ q : α × Fin 2 → K, G.IsAdmissiblePicture q := by
  classical
  have : Fintype α := Fintype.ofFinite α
  set φ : α ↪ K :=
    (Fintype.equivFin α).toEmbedding.trans (Fin.valEmbedding.trans (Infinite.natEmbedding K))
    with hφdef
  set q : α × Fin 2 → K := fun p => ![φ p.1, (φ p.1) ^ 2] p.2 with hqdef
  have hpp : ∀ w, pencilPicturePoint q w = ![φ w, (φ w) ^ 2, 1] := by
    intro w; funext i; fin_cases i <;> simp [pencilPicturePoint, hqdef]
  refine ⟨q, fun e u v he => ?_, fun v hv => ?_⟩
  · have huv : u ≠ v := he.ne
    rw [hpp, hpp]
    intro hcontra
    exact huv (φ.injective (by simpa using congr_fun hcontra 0))
  · obtain ⟨t, hts, ht3⟩ := Set.exists_subset_card_eq (h3 v hv)
    obtain ⟨x, y, z, hxy, hxz, hyz, hset⟩ := Set.ncard_eq_three.mp ht3
    refine ⟨![x, y, z], fun i => hts ?_, ?_⟩
    · fin_cases i <;> simp [hset]
    · have hdetne : (Matrix.of
          (fun i j : Fin 3 => pencilPicturePoint q (![x, y, z] i) j)).det ≠ 0 := by
        have hrw : (Matrix.of (fun i j : Fin 3 => pencilPicturePoint q (![x, y, z] i) j))
            = Matrix.of ![![φ x, (φ x) ^ 2, 1], ![φ y, (φ y) ^ 2, 1], ![φ z, (φ z) ^ 2, 1]] := by
          funext i j; fin_cases i <;> simp [hpp]
        rw [hrw, det_moment_curve_triple]
        refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
        · exact sub_ne_zero.mpr (fun h => hxy (φ.injective h).symm)
        · exact sub_ne_zero.mpr (fun h => hxz (φ.injective h))
        · exact sub_ne_zero.mpr (fun h => hyz (φ.injective h))
      have hLI : LinearIndependent K
          (Matrix.of (fun i j : Fin 3 => pencilPicturePoint q (![x, y, z] i) j)).row :=
        Matrix.linearIndependent_rows_iff_det_ne_zero.mpr hdetne
      exact hLI

/-- **A main picture exists** (Phase 40b CARRIER slice C2). Among the (nonempty, by
`Graph.exists_isAdmissiblePicture`) admissible pictures, the natural number `finrank L(q)` attains
its least value at some admissible `q`, which is then a main picture by definition. -/
theorem _root_.Graph.exists_isMainPicture [Infinite K] [Finite α] {G : Graph α β}
    (hloop : G.Loopless) (h3 : ∀ v ∈ V(G), 3 ≤ (G.closedNbhd v).ncard) :
    ∃ q : α × Fin 2 → K, G.IsMainPicture q := by
  classical
  obtain ⟨q₀, hq₀⟩ := G.exists_isAdmissiblePicture (K := K) hloop h3
  set S : Set ℕ := (fun q => Module.finrank K (G.liftingSpace q)) ''
    {q : α × Fin 2 → K | G.IsAdmissiblePicture q} with hSdef
  obtain ⟨q, hq, hqeq⟩ := Nat.sInf_mem (⟨_, q₀, hq₀, rfl⟩ : S.Nonempty)
  have hqeq' : Module.finrank K (G.liftingSpace q) = sInf S := hqeq
  refine ⟨q, hq, fun q' hq' => ?_⟩
  rw [hqeq']
  exact Nat.sInf_le ⟨q', hq', rfl⟩

/-! ## `U` is nonempty and Zariski-open -/

/-- **`U` is nonempty and Zariski-open** (`lem:pencil-x0-main-picture-open`; Phase 40b CARRIER
slice C2). Take a main picture `q_min` (`Graph.exists_isMainPicture`). Admissibility is open
around it (`Graph.IsAdmissiblePicture.exists_mvPolynomial`, polynomial `Padm`), and the
`Matrix.exists_mvPolynomial_section_mulVec_eq_zero` mirror at the trivial kernel vector `0` of the
lifting system gives a second polynomial `D`, nonzero at `q_min`, off whose zero set the kernel of
the lifting system is no larger than at `q_min` — the semicontinuity half of
`Graph.x0Attains_of_exists`'s argument, reused here at the flat section instead of one through a
witness height. Off the zero set of `Padm * D`, `q` is admissible with
`finrank L(q) ≤ finrank L(q_min)` (`Graph.finrank_ker_liftingMatrix` at both ends), and since
`q_min` already achieves the global minimum among admissible pictures, `q` does too: `q ∈ U`. -/
theorem _root_.Graph.exists_mvPolynomial_isMainPicture [Infinite K] [Finite α] {G : Graph α β}
    (hloop : G.Loopless) (h3 : ∀ v ∈ V(G), 3 ≤ (G.closedNbhd v).ncard) :
    ∃ P : MvPolynomial (α × Fin 2) K, P ≠ 0 ∧
      ∀ q : α × Fin 2 → K, MvPolynomial.eval q P ≠ 0 → G.IsMainPicture q := by
  classical
  have : Fintype α := Fintype.ofFinite α
  obtain ⟨q_min, hq_min⟩ := G.exists_isMainPicture (K := K) hloop h3
  obtain ⟨Padm, hPadm₀, hPadm⟩ := hq_min.1.exists_mvPolynomial
  obtain ⟨D, Z, hD₀, -, hDrank, -⟩ :=
    Matrix.exists_mvPolynomial_section_mulVec_eq_zero (G.liftingMatrix K)
      (q₀ := q_min) (z₀ := (0 : α ⊕ (α × Fin 3) → K)) (Matrix.mulVec_zero _)
  refine ⟨Padm * D, ?_, fun q hq => ?_⟩
  · intro h0
    have h := congrArg (MvPolynomial.eval q_min) h0
    rw [map_mul, map_zero] at h
    exact mul_ne_zero hPadm₀ hD₀ h
  · rw [map_mul] at hq
    have hadm : G.IsAdmissiblePicture q := hPadm q (left_ne_zero_of_mul hq)
    have hDq : MvPolynomial.eval q D ≠ 0 := right_ne_zero_of_mul hq
    have hdim : Module.finrank K
          (LinearMap.ker ((G.liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin) ≤
        Module.finrank K
          (LinearMap.ker ((G.liftingMatrix K).map (MvPolynomial.eval q_min)).mulVecLin) :=
      hDrank q hDq
    have hle : Module.finrank K (G.liftingSpace q) ≤ Module.finrank K (G.liftingSpace q_min) := by
      rwa [Graph.finrank_ker_liftingMatrix hadm, Graph.finrank_ker_liftingMatrix hq_min.1] at hdim
    exact ⟨hadm, fun q' hq' => hle.trans (hq_min.2 q' hq')⟩

/-! ## The picture-to-normal API (Phase 40b CARRIER slice C3) -/

/-- **The normal is nonzero iff the selected configuration triple is independent** (Phase 40b
CARRIER slice C3, item 1). Direct unfold of `pencilNormalOfPicture` as `cross₃` of the three
selected configuration points, plus `cross₃_ne_zero_iff_linearIndependent`. -/
theorem pencilNormalOfPicture_ne_zero_iff (q : α × Fin 2 → K) (z : α → K) (sel : α → Fin 3 → α)
    (v : α) :
    pencilNormalOfPicture q z sel v ≠ 0 ↔
      LinearIndependent K (fun i => pencilConfigPoint q z (sel v i)) := by
  have heq : (fun i => pencilConfigPoint q z (sel v i)) =
      ![pencilConfigPoint q z (sel v 0), pencilConfigPoint q z (sel v 1),
        pencilConfigPoint q z (sel v 2)] := by
    funext i; fin_cases i <;> rfl
  rw [heq]
  exact cross₃_ne_zero_iff_linearIndependent _ _ _

/-- **Picture independence gives configuration independence, at every height** (Phase 40b CARRIER
slice C3, item 2). The linear map `f : K⁴ →ₗ K³` dropping the height coordinate (projecting onto
coordinates `0, 1, 3`) sends every configuration point `pencilConfigPoint q z w` to the picture
point `pencilPicturePoint q w`, so an independent family of picture points forces the corresponding
family of configuration points independent (`LinearIndependent.of_comp`, which needs no
injectivity of `f`: a dependency relation among the domain vectors pushes forward to one among
their images, so independent images force independent domain vectors). -/
theorem linearIndependent_pencilConfigPoint_of_linearIndependent_pencilPicturePoint
    {q : α × Fin 2 → K} (z : α → K) {ι : Type*} {t : ι → α}
    (ht : LinearIndependent K (fun i => pencilPicturePoint q (t i))) :
    LinearIndependent K (fun i => pencilConfigPoint q z (t i)) := by
  set f : (Fin 4 → K) →ₗ[K] (Fin 3 → K) :=
    { toFun := fun a => ![a 0, a 1, a 3]
      map_add' := fun a b => by funext i; fin_cases i <;> rfl
      map_smul' := fun c a => by funext i; fin_cases i <;> rfl } with hfdef
  refine LinearIndependent.of_comp f ?_
  have heq : f ∘ (fun i => pencilConfigPoint q z (t i)) = fun i => pencilPicturePoint q (t i) := by
    funext i
    change f (pencilConfigPoint q z (t i)) = pencilPicturePoint q (t i)
    funext j
    fin_cases j <;> rfl
  rwa [heq]

/-- **The plane of a valid selector at `v` contains the whole closed neighbourhood** (Phase 40b
CARRIER slice C3, item 3; new, consumed by C4). Over a height `z ∈ L(q)`, at a body `v ∈ V(G)`
with a selector `sel v` valued in `G.closedNbhd v`, the normal `N = pencilNormalOfPicture q z sel
v` annihilates every configuration point of the closed neighbourhood, not just the three selected
ones. Route: `dotProduct_cross₃` reduces `N ⬝ᵥ p_w` to `det[p_{sel v 0}, p_{sel v 1}, p_{sel v 2},
p_w]`. Membership in `L(q)` gives, at `v`, coefficients `h : Fin 3 → K` with every point over
`G.closedNbhd v` an image of its picture point under the linear map `a ↦ (a 0, a 1, h ⬝ᵥ a, a 2)`
— so all four rows are images, under one linear map, of four vectors in the `3`-dimensional `K³`,
always dependent (`LinearIndependent.fintype_card_le_finrank`), and dependency of the domain
vectors pushes forward through any linear map to the images, so the four rows are dependent too
and the determinant vanishes (`linearIndependent_rows_iff_det_ne_zero`).

No independence hypothesis on the selected triple is needed: a dependent triple has `cross₃ = 0`,
and the conclusion then holds trivially. -/
theorem dotProduct_pencilNormalOfPicture_eq_zero_of_mem_closedNbhd {G : Graph α β}
    {q : α × Fin 2 → K} {z : α → K} (hz : z ∈ G.liftingSpace q) {v : α} (hv : v ∈ V(G))
    {sel : α → Fin 3 → α} (hsel : ∀ i, sel v i ∈ G.closedNbhd v)
    {w : α} (hw : w ∈ G.closedNbhd v) :
    pencilNormalOfPicture q z sel v ⬝ᵥ pencilConfigPoint q z w = 0 := by
  classical
  obtain ⟨h, hh⟩ := (Graph.mem_liftingSpace.mp hz).2 v hv
  set L : (Fin 3 → K) →ₗ[K] (Fin 4 → K) :=
    { toFun := fun a => ![a 0, a 1, h ⬝ᵥ a, a 2]
      map_add' := fun a b => by funext i; fin_cases i <;> simp [dotProduct_add]
      map_smul' := fun c a => by funext i; fin_cases i <;> simp [dotProduct_smul] } with hLdef
  have hLapply : ∀ a, L a = ![a 0, a 1, h ⬝ᵥ a, a 2] := fun _ => rfl
  have hLp : ∀ x ∈ G.closedNbhd v, pencilConfigPoint q z x = L (pencilPicturePoint q x) := by
    intro x hx
    rw [hLapply]
    funext i
    fin_cases i <;> simp [pencilConfigPoint, pencilPicturePoint, hh x hx]
  have hdep : ¬ LinearIndependent K
      ![pencilPicturePoint q (sel v 0), pencilPicturePoint q (sel v 1),
        pencilPicturePoint q (sel v 2), pencilPicturePoint q w] := by
    intro hli
    have hc := hli.fintype_card_le_finrank
    rw [Module.finrank_fin_fun] at hc
    simp at hc
  have hnotLI : ¬ LinearIndependent K
      ![pencilConfigPoint q z (sel v 0), pencilConfigPoint q z (sel v 1),
        pencilConfigPoint q z (sel v 2), pencilConfigPoint q z w] := by
    intro hLI4
    apply hdep
    have heq : (![pencilConfigPoint q z (sel v 0), pencilConfigPoint q z (sel v 1),
          pencilConfigPoint q z (sel v 2), pencilConfigPoint q z w] : Fin 4 → Fin 4 → K) =
        L ∘ ![pencilPicturePoint q (sel v 0), pencilPicturePoint q (sel v 1),
          pencilPicturePoint q (sel v 2), pencilPicturePoint q w] := by
      funext i
      fin_cases i
      · exact hLp _ (hsel 0)
      · exact hLp _ (hsel 1)
      · exact hLp _ (hsel 2)
      · exact hLp _ hw
    rw [heq] at hLI4
    exact hLI4.of_comp L
  have hdetzero : Matrix.det (Matrix.of ![pencilConfigPoint q z (sel v 0),
      pencilConfigPoint q z (sel v 1), pencilConfigPoint q z (sel v 2),
      pencilConfigPoint q z w]) = 0 := by
    by_contra hne
    exact hnotLI (Matrix.linearIndependent_rows_iff_det_ne_zero (K := K)
      (A := Matrix.of ![pencilConfigPoint q z (sel v 0), pencilConfigPoint q z (sel v 1),
        pencilConfigPoint q z (sel v 2), pencilConfigPoint q z w]) |>.mpr hne)
  change cross₃ (pencilConfigPoint q z (sel v 0)) (pencilConfigPoint q z (sel v 1))
      (pencilConfigPoint q z (sel v 2)) ⬝ᵥ pencilConfigPoint q z w = 0
  rw [dotProduct_cross₃]
  exact hdetzero

/-- **Selector independence up to a scalar** (Phase 40b CARRIER slice C3, item 4). Under item 3's
hypotheses for two selectors `sel, sel'` at the same `v`, each selecting a triple with independent
picture points, the normals differ by a nonzero scalar.
Both normals are nonzero (items 1/2); item 3 puts `N = pencilNormalOfPicture q z sel v` in the perp
of the three (independent, by item 2) configuration points at `sel'`, and `N' =
pencilNormalOfPicture q z sel' v` lies there too (`cross₃`'s own orthogonality to its defining
triple, `cross₃_dotProduct_apply_self`) — a `1`-dimensional perp (`finrank_toDualPerp_triple_eq`),
so it is spanned by the nonzero `N'` (`Submodule.eq_of_le_of_finrank_eq`), and `N` is a scalar
multiple. -/
theorem exists_smul_pencilNormalOfPicture_eq_of_mem_closedNbhd {G : Graph α β}
    {q : α × Fin 2 → K} {z : α → K} (hz : z ∈ G.liftingSpace q) {v : α} (hv : v ∈ V(G))
    {sel sel' : α → Fin 3 → α}
    (hsel : ∀ i, sel v i ∈ G.closedNbhd v) (hsel' : ∀ i, sel' v i ∈ G.closedNbhd v)
    (hLI : LinearIndependent K (fun i => pencilPicturePoint q (sel v i)))
    (hLI' : LinearIndependent K (fun i => pencilPicturePoint q (sel' v i))) :
    ∃ c : K, c ≠ 0 ∧
      pencilNormalOfPicture q z sel v = c • pencilNormalOfPicture q z sel' v := by
  set N := pencilNormalOfPicture q z sel v with hNdef
  set N' := pencilNormalOfPicture q z sel' v with hN'def
  have hN : N ≠ 0 :=
    (pencilNormalOfPicture_ne_zero_iff q z sel v).mpr
      (linearIndependent_pencilConfigPoint_of_linearIndependent_pencilPicturePoint z hLI)
  have hN' : N' ≠ 0 :=
    (pencilNormalOfPicture_ne_zero_iff q z sel' v).mpr
      (linearIndependent_pencilConfigPoint_of_linearIndependent_pencilPicturePoint z hLI')
  have hLI'config : LinearIndependent K (fun i => pencilConfigPoint q z (sel' v i)) :=
    linearIndependent_pencilConfigPoint_of_linearIndependent_pencilPicturePoint z hLI'
  set W : Submodule K (Fin 4 → K) := ⨅ j : Fin 3, LinearMap.ker
      ((Pi.basisFun K (Fin 4)).toDual.flip ((fun i => pencilConfigPoint q z (sel' v i)) j))
    with hWdef
  have hWdim : Module.finrank K W = 1 := finrank_toDualPerp_triple_eq hLI'config
  have hmemW : ∀ x : Fin 4 → K, x ∈ W ↔ ∀ j, x ⬝ᵥ pencilConfigPoint q z (sel' v j) = 0 := by
    intro x
    simp only [hWdef, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply,
      piBasisFun_toDual_eq_dotProduct]
  have hNmem : N ∈ W := by
    rw [hmemW]
    intro j
    exact dotProduct_pencilNormalOfPicture_eq_zero_of_mem_closedNbhd hz hv hsel (hsel' j)
  have hN'mem : N' ∈ W := by
    rw [hmemW]
    intro j
    exact cross₃_dotProduct_apply_self (fun i => pencilConfigPoint q z (sel' v i)) j
  have hspan : Submodule.span K ({N'} : Set (Fin 4 → K)) = W := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]; simpa using hN'mem
    · rw [hWdim, finrank_span_singleton hN']
  rw [← hspan] at hNmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hNmem
  refine ⟨c, ?_, hc.symm⟩
  intro hc0
  exact hN (by rw [← hc, hc0, zero_smul])

/-! ## The polynomial mirror of the picture-to-normal map (Phase 40b CARRIER slice C3, item 5) -/

/-- **The homogeneous configuration point as polynomials in the height variables, at a fixed
picture** (Phase 40b CARRIER slice C3, item 5): the vector `(C q_{w,0}, C q_{w,1}, X_w, 1)`, the
picture coordinates baked in as constants and the height `z_w` a variable indexed by `α` — the
shape `X0Gen`'s fibre-intersection needs, at a fixed picture `q`. -/
noncomputable def pencilConfigPointPoly (q : α × Fin 2 → K) (w : α) : Fin 4 → MvPolynomial α K :=
  ![MvPolynomial.C (q (w, 0)), MvPolynomial.C (q (w, 1)), MvPolynomial.X w, 1]

@[simp]
theorem eval_pencilConfigPointPoly (q : α × Fin 2 → K) (z : α → K) (w : α) (i : Fin 4) :
    MvPolynomial.eval z (pencilConfigPointPoly q w i) = pencilConfigPoint q z w i := by
  fin_cases i <;> simp [pencilConfigPointPoly, pencilConfigPoint]

/-- **The polynomial mirror of `pencilNormalOfPicture`, in the height variables at a fixed
picture** (Phase 40b CARRIER slice C3, item 5): `cross₃Poly` of the three selected configuration
points' polynomial mirrors. Its eval lemma (`eval_pencilNormalOfPicturePoly`) is what lets `X0Gen`
intersect the attaining heights with a nondegeneracy polynomial on `L(q)`. -/
noncomputable def pencilNormalOfPicturePoly (q : α × Fin 2 → K) (sel : α → Fin 3 → α) (v : α) :
    Fin 4 → MvPolynomial α K :=
  cross₃Poly (pencilConfigPointPoly q (sel v 0)) (pencilConfigPointPoly q (sel v 1))
    (pencilConfigPointPoly q (sel v 2))

/-- **`pencilNormalOfPicturePoly` evaluates to the actual `pencilNormalOfPicture` value** (Phase
40b CARRIER slice C3, item 5). -/
theorem eval_pencilNormalOfPicturePoly (q : α × Fin 2 → K) (sel : α → Fin 3 → α) (v : α)
    (z : α → K) (i : Fin 4) :
    MvPolynomial.eval z (pencilNormalOfPicturePoly q sel v i)
      = pencilNormalOfPicture q z sel v i := by
  rw [pencilNormalOfPicturePoly, cross₃Poly_eval]
  have h0 : (fun j => MvPolynomial.eval z (pencilConfigPointPoly q (sel v 0) j)) =
      pencilConfigPoint q z (sel v 0) := funext fun j => eval_pencilConfigPointPoly q z (sel v 0) j
  have h1 : (fun j => MvPolynomial.eval z (pencilConfigPointPoly q (sel v 1) j)) =
      pencilConfigPoint q z (sel v 1) := funext fun j => eval_pencilConfigPointPoly q z (sel v 1) j
  have h2 : (fun j => MvPolynomial.eval z (pencilConfigPointPoly q (sel v 2) j)) =
      pencilConfigPoint q z (sel v 2) := funext fun j => eval_pencilConfigPointPoly q z (sel v 2) j
  rw [h0, h1, h2, pencilNormalOfPicture]

/-! ## The configuration as a pencil framework (Phase 40b CARRIER slice C4) -/

/-- **The point-join framework** (`lem:pencil-config-point-join-rank`; Phase 40b CARRIER slice
C4): the body-hinge framework on `G` whose supporting extensor at every label `e` is the join
`p_u ∧ p_v` of the points at `(u, v) = ends e`, the hinge of a pencil realization with concurrency
points `p`. It is unpatched: at a label off `E(G)` the join is whatever `ends` names, possibly
zero; the realization witness `pencilConfigFramework` patches it there. -/
noncomputable def pointJoinFramework (G : Graph α β) (ends : β → α × α) (p : α → Fin 4 → K) :
    BodyHingeFramework K 2 α β where
  graph := G
  supportExtensor e := ScrewSpace.mk (extensor ![p (ends e).1, p (ends e).2])
    (extensor_mem_exteriorPower _)

/-- **`ofNormals` at the points is the polarity image of the point-join framework**
(`lem:pencil-config-point-join-rank`; Phase 40b CARRIER slice C4). The panel-hinge framework whose
panel normal at each body is its point `p_v` has, at every label, the meet
`panelSupportExtensor p_u p_v` of the two polar planes, which the polarity `screwComplementIso`
takes the join `p_u ∧ p_v` to (`screwComplementIso_mk_extensor`, over every field). -/
theorem ofNormals_toBodyHinge_eq_mapSupport_pointJoinFramework (G : Graph α β)
    (ends : β → α × α) (p : α → Fin 4 → K) :
    (PanelHingeFramework.ofNormals (k := 2) G ends (fun x => p x.1 x.2)).toBodyHinge
      = (pointJoinFramework G ends p).mapSupport screwComplementIso := by
  have hsupp : (PanelHingeFramework.ofNormals (k := 2) G ends
        (fun x => p x.1 x.2)).toBodyHinge.supportExtensor
      = ((pointJoinFramework G ends p).mapSupport screwComplementIso).supportExtensor := by
    funext e
    simp only [BodyHingeFramework.mapSupport_supportExtensor, pointJoinFramework,
      screwComplementIso_mk_extensor, PanelHingeFramework.toBodyHinge_supportExtensor,
      PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal]
    rfl
  exact congrArg (BodyHingeFramework.mk (k := 2) G) hsupp

open Classical in
/-- **The configuration as a pencil framework** (`lem:pencil-config-point-join-rank`; Phase 40b
CARRIER slice C4): the point-join framework of the configuration points `p_w =
pencilConfigPoint q z w`, patched off `E(G)`. At a label `e ∈ E(G)` the supporting extensor is the
join `p_u ∧ p_v` at `(u, v) = ends e`; off `E(G)` it is the fixed nonzero join of two standard
basis vectors, as in `pencilChartFramework` (`Molecule/Pencil/Chart.lean`), since
`HasCoplanarPanelRealization` asks for a nonzero supporting extensor at every label of `β`. The
endpoints are read from `ends`, not `Graph.endsOf`, so no `[Inhabited α]` is needed. -/
noncomputable def pencilConfigFramework (G : Graph α β) (ends : β → α × α) (q : α × Fin 2 → K)
    (z : α → K) : BodyHingeFramework K 2 α β where
  graph := G
  supportExtensor e :=
    if e ∈ E(G) then
      ScrewSpace.mk (extensor ![pencilConfigPoint q z (ends e).1, pencilConfigPoint q z (ends e).2])
        (extensor_mem_exteriorPower _)
    else
      ScrewSpace.mk (extensor ![(![1, 0, 0, 0] : Fin 4 → K), (![0, 1, 0, 0] : Fin 4 → K)])
        (extensor_mem_exteriorPower _)

@[simp]
theorem pencilConfigFramework_graph (G : Graph α β) (ends : β → α × α) (q : α × Fin 2 → K)
    (z : α → K) : (pencilConfigFramework G ends q z).graph = G := rfl

/-- The supporting extensor of `pencilConfigFramework` at a label of `E(G)`: the point join. -/
theorem pencilConfigFramework_supportExtensor_of_mem_edgeSet {G : Graph α β} (ends : β → α × α)
    (q : α × Fin 2 → K) (z : α → K) {e : β} (he : e ∈ E(G)) :
    (pencilConfigFramework G ends q z).supportExtensor e =
      ScrewSpace.mk (extensor ![pencilConfigPoint q z (ends e).1, pencilConfigPoint q z (ends e).2])
        (extensor_mem_exteriorPower _) :=
  ite_eq_left he

/-- The supporting extensor of `pencilConfigFramework` off `E(G)`: the standard-basis patch. -/
theorem pencilConfigFramework_supportExtensor_of_not_mem_edgeSet {G : Graph α β}
    (ends : β → α × α) (q : α × Fin 2 → K) (z : α → K) {e : β} (he : e ∉ E(G)) :
    (pencilConfigFramework G ends q z).supportExtensor e =
      ScrewSpace.mk (extensor ![(![1, 0, 0, 0] : Fin 4 → K), (![0, 1, 0, 0] : Fin 4 → K)])
        (extensor_mem_exteriorPower _) :=
  ite_eq_right he

/-- **The patched configuration framework has the rank of `ofNormals` at the configuration
points** (`lem:pencil-config-point-join-rank`; Phase 40b CARRIER slice C4, the polar/primal rank
equality). The patch agrees with the unpatched point-join framework on every link, so the two
have the same rigidity-row span (`span_rigidityRows_eq_of_supportExtensor_agree`); the unpatched
one is carried to `ofNormals` by the polarity
(`ofNormals_toBodyHinge_eq_mapSupport_pointJoinFramework`), an invertible map of the screw space,
which leaves the rank unchanged (`BodyHingeFramework.finrank_span_rigidityRows_mapSupport`). No
hypothesis on `ends` is needed: a link's label lies in `E(G)`, where the patch is the join at
whatever `ends` names, exactly as in the unpatched framework. -/
theorem finrank_span_rigidityRows_pencilConfigFramework (G : Graph α β) (ends : β → α × α)
    (q : α × Fin 2 → K) (z : α → K) :
    Module.finrank K (Submodule.span K (pencilConfigFramework G ends q z).rigidityRows)
      = Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 2) G ends
          (fun p => pencilConfigPoint q z p.1 p.2)).toBodyHinge.rigidityRows) := by
  have hspan : Submodule.span K (pencilConfigFramework G ends q z).rigidityRows
      = Submodule.span K (pointJoinFramework G ends (pencilConfigPoint q z)).rigidityRows :=
    span_rigidityRows_eq_of_supportExtensor_agree _ _ rfl fun _ _ _ he =>
      pencilConfigFramework_supportExtensor_of_mem_edgeSet ends q z he.edge_mem
  rw [hspan, ofNormals_toBodyHinge_eq_mapSupport_pointJoinFramework G ends (pencilConfigPoint q z),
    BodyHingeFramework.finrank_span_rigidityRows_mapSupport]

/-- **The configuration framework's hinges are all nonzero over an admissible picture**
(`lem:pencil-config-point-join-rank`; Phase 40b CARRIER slice C4). At a label of `E(G)`, `ends`
names the two ends of a link, whose picture points differ, so their configuration points are
independent at every height (`linearIndependent_pencilConfigPoint_pair`) and their join is
nonzero; off `E(G)` the patch is nonzero (`extensor_stdBasis_pair_ne_zero`). -/
theorem _root_.Graph.IsAdmissiblePicture.pencilConfigFramework_supportExtensor_ne_zero
    {G : Graph α β} {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) {ends : β → α × α}
    (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2) (z : α → K) (e : β) :
    (pencilConfigFramework G ends q z).supportExtensor e ≠ 0 := by
  intro h0
  have hval := congrArg ScrewSpace.val h0
  by_cases he : e ∈ E(G)
  · rw [pencilConfigFramework_supportExtensor_of_mem_edgeSet ends q z he, ScrewSpace.val_mk,
      ScrewSpace.val_zero] at hval
    obtain ⟨x, y, hxy⟩ := Graph.exists_isLink_of_mem_edgeSet he
    exact (extensor_ne_zero_iff_linearIndependent _).mpr
      (linearIndependent_pencilConfigPoint_pair z (hq.1 _ _ _ (hends e x y hxy))) hval
  · rw [pencilConfigFramework_supportExtensor_of_not_mem_edgeSet ends q z he, ScrewSpace.val_mk,
      ScrewSpace.val_zero] at hval
    exact extensor_stdBasis_pair_ne_zero hval

/-- **A configuration over an admissible picture is a pencil panel realization**
(`lem:pencil-config-distinct-realization`; Phase 40b CARRIER slice C4). Over an admissible picture
`q` and a height `z ∈ L(q)`, with a selector `sel` choosing at every body of `G` three members of
its closed neighbourhood with independent picture points, the configuration framework
`pencilConfigFramework G ends q z`, the plane normals `pencilNormalOfPicture q z sel` and the
configuration points `pencilConfigPoint q z` form a pencil panel realization of `G`. The normals
are nonzero (`pencilNormalOfPicture_ne_zero_iff`, with the picture-to-configuration independence
transport); each normal is orthogonal to the points of the whole closed neighbourhood
(`dotProduct_pencilNormalOfPicture_eq_zero_of_mem_closedNbhd`), which contains both ends of every
link at the body and the body itself, giving both panel containments and the incidence; each
point has last coordinate `1`; and a link's join passes through both its ends by construction. -/
theorem _root_.Graph.IsAdmissiblePicture.hasPencilPanelRealization_pencilConfigFramework
    {G : Graph α β} {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) {ends : β → α × α}
    (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2)
    {z : α → K} (hz : z ∈ G.liftingSpace q) {sel : α → Fin 3 → α}
    (hsel : ∀ v ∈ V(G), (∀ i, sel v i ∈ G.closedNbhd v) ∧
      LinearIndependent K (fun i => pencilPicturePoint q (sel v i))) :
    HasPencilPanelRealization G (pencilConfigFramework G ends q z)
      (pencilNormalOfPicture q z sel) (pencilConfigPoint q z) := by
  have hperp : ∀ v ∈ V(G), ∀ w ∈ G.closedNbhd v,
      pencilConfigPoint q z w ⬝ᵥ pencilNormalOfPicture q z sel v = 0 := fun v hv w hw => by
    rw [dotProduct_comm]
    exact dotProduct_pencilNormalOfPicture_eq_zero_of_mem_closedNbhd hz hv (hsel v hv).1 hw
  -- A link's supporting extensor is the join of its two ends, in one order or the other.
  have hjoin : ∀ e u v, G.IsLink e u v →
      (pencilConfigFramework G ends q z).supportExtensor e =
        ScrewSpace.mk (extensor ![pencilConfigPoint q z u, pencilConfigPoint q z v])
          (extensor_mem_exteriorPower _) ∨
      (pencilConfigFramework G ends q z).supportExtensor e =
        ScrewSpace.mk (extensor ![pencilConfigPoint q z v, pencilConfigPoint q z u])
          (extensor_mem_exteriorPower _) := by
    intro e u v he
    rw [pencilConfigFramework_supportExtensor_of_mem_edgeSet ends q z he.edge_mem]
    rcases (hends e u v he).eq_and_eq_or_eq_and_eq he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; rw [h1, h2]
    · right; rw [h1, h2]
  -- The join of the two ends of a link, in either order, lies in both panels and passes through
  -- both points.
  have hkey : ∀ e a b, G.IsLink e a b →
      ExtensorInPanel (ScrewSpace.mk (extensor ![pencilConfigPoint q z a, pencilConfigPoint q z b])
          (extensor_mem_exteriorPower _)) (pencilNormalOfPicture q z sel a) ∧
      ExtensorInPanel (ScrewSpace.mk (extensor ![pencilConfigPoint q z a, pencilConfigPoint q z b])
          (extensor_mem_exteriorPower _)) (pencilNormalOfPicture q z sel b) ∧
      ExtensorThroughPoint (ScrewSpace.mk (extensor ![pencilConfigPoint q z a,
          pencilConfigPoint q z b]) (extensor_mem_exteriorPower _)) (pencilConfigPoint q z a) ∧
      ExtensorThroughPoint (ScrewSpace.mk (extensor ![pencilConfigPoint q z a,
          pencilConfigPoint q z b]) (extensor_mem_exteriorPower _)) (pencilConfigPoint q z b) := by
    intro e a b he
    have ha : a ∈ V(G) := he.left_mem
    have hb : b ∈ V(G) := he.right_mem
    refine ⟨⟨_, ScrewSpace.val_mk _ _, Fin.forall_fin_two.mpr
        ⟨hperp a ha a (Or.inl rfl), hperp a ha b (Or.inr ⟨e, he⟩)⟩⟩,
      ⟨_, ScrewSpace.val_mk _ _, Fin.forall_fin_two.mpr
        ⟨hperp b hb a (Or.inr ⟨e, he.symm⟩), hperp b hb b (Or.inl rfl)⟩⟩,
      ⟨_, ScrewSpace.val_mk _ _, Submodule.subset_span ⟨0, rfl⟩⟩,
      ⟨_, ScrewSpace.val_mk _ _, Submodule.subset_span ⟨1, rfl⟩⟩⟩
  refine ⟨⟨rfl, fun v hv => ?_, hq.pencilConfigFramework_supportExtensor_ne_zero hends z,
    fun e u v he => ?_⟩, fun v _ h0 => ?_, fun v hv => hperp v hv v (Or.inl rfl),
    fun e u v he => ?_⟩
  · exact (pencilNormalOfPicture_ne_zero_iff q z sel v).mpr
      (linearIndependent_pencilConfigPoint_of_linearIndependent_pencilPicturePoint z (hsel v hv).2)
  · rcases hjoin e u v he with h | h <;> rw [h]
    · exact ⟨(hkey e u v he).1, (hkey e u v he).2.1⟩
    · exact ⟨(hkey e v u he.symm).2.1, (hkey e v u he.symm).1⟩
  · simpa [pencilConfigPoint] using congr_fun h0 3
  · rcases hjoin e u v he with h | h <;> rw [h]
    · exact ⟨(hkey e u v he).2.2.1, (hkey e u v he).2.2.2⟩
    · exact ⟨(hkey e v u he.symm).2.2.2, (hkey e v u he.symm).2.2.1⟩

/-- **An attaining configuration over an admissible picture is a distinct pencil realization at
the deficiency rank** (`lem:pencil-config-distinct-realization`; Phase 40b CARRIER slice C4, the
bridge to the distinct statement). If a configuration `(q, z)` with `q` admissible and
`z ∈ L(q)` has row rank `6(|V(G)| − 1) − def₃(G)` at `ofNormals` of its points (the rank
`Graph.X0Attains` reads), then `G` has an adjacent-distinct pencil realization at the deficiency
rank (`HasDistinctPencilRealization`). The witness is the patched configuration framework
(`pencilConfigFramework`) with the configuration points as concurrency points and, as normals,
the plane normals at admissibility's own triple at each body (chosen classically, a dummy off
`V(G)`): a pencil panel realization
(`Graph.IsAdmissiblePicture.hasPencilPanelRealization_pencilConfigFramework`), adjacent points
independent since adjacent picture points differ (`linearIndependent_pencilConfigPoint_pair`), at
the rank of `ofNormals` (`finrank_span_rigidityRows_pencilConfigFramework`). -/
theorem _root_.Graph.IsAdmissiblePicture.hasDistinctPencilRealization {G : Graph α β}
    {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) {ends : β → α × α}
    (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2)
    {z : α → K} (hz : z ∈ G.liftingSpace q)
    (hrank : (Module.finrank K (Submodule.span K
        (PanelHingeFramework.ofNormals (k := 2) G ends
          (fun p => pencilConfigPoint q z p.1 p.2)).toBodyHinge.rigidityRows) : ℤ)
        = screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency 3) :
    HasDistinctPencilRealization K 3 G := by
  classical
  let sel : α → Fin 3 → α := fun v => if hv : v ∈ V(G) then (hq.2 v hv).choose else fun _ => v
  have hsel : ∀ v ∈ V(G), (∀ i, sel v i ∈ G.closedNbhd v) ∧
      LinearIndependent K (fun i => pencilPicturePoint q (sel v i)) := by
    intro v hv
    simp only [sel, hv, ↓reduceDIte]
    exact (hq.2 v hv).choose_spec
  refine ⟨pencilConfigFramework G ends q z, pencilNormalOfPicture q z sel, pencilConfigPoint q z,
    hq.hasPencilPanelRealization_pencilConfigFramework hends hz hsel,
    fun e u v he => linearIndependent_pencilConfigPoint_pair z (hq.1 e u v he), ?_⟩
  rw [finrank_span_rigidityRows_pencilConfigFramework]
  exact hrank

/-- **The general configuration attaining gives a distinct pencil realization at the deficiency
rank** (`lem:pencil-x0-attains-distinct`; Phase 40b CARRIER slice C4, the `X0Dist` leg of
`thm:pencil-x0-generic-attains`). Over an infinite field, `Graph.X0Attains K G` forces
`HasDistinctPencilRealization K 3 G`: the nonzero picture polynomial `P` has a non-root `q`
(`MvPolynomial.exists_eval_ne_zero`), which is admissible with a height `z ∈ L(q)` off the
height polynomial's zero set, where the rank is attained; the bridge
`Graph.IsAdmissiblePicture.hasDistinctPencilRealization` finishes. This is the consumer
`Graph.X0Attains` was shaped for: the distinct motive uses only one attaining configuration. -/
theorem _root_.Graph.X0Attains.hasDistinctPencilRealization [Infinite K] {G : Graph α β}
    (h : G.X0Attains K) : HasDistinctPencilRealization K 3 G := by
  obtain ⟨ends, P, hends, hP, hgood⟩ := h
  obtain ⟨q, hq⟩ := MvPolynomial.exists_eval_ne_zero hP
  obtain ⟨hadm, R, ⟨z, hz, hRz⟩, hall⟩ := hgood q hq
  exact hadm.hasDistinctPencilRealization hends hz (hall z hz hRz)

/-! ## Scaling and affine shifts of the heights keep the rank (Phase 40b CARRIER, (MC-3)) -/

/-- **A collineation of the points is a change of screw coordinates of the point-join framework**
(`lem:pencil-rank-scale-shift`; Phase 40b CARRIER). Applying an invertible linear map `g` of `K⁴`
to every point replaces each join `p_u ∧ p_v` by `g p_u ∧ g p_v`, its image under the induced
screw-space automorphism (`BodyHingeFramework.screwEquivOfLinearEquiv_mk_extensor`). -/
theorem pointJoinFramework_comp_eq_mapSupport (G : Graph α β) (ends : β → α × α)
    (p : α → Fin 4 → K) (g : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K)) :
    pointJoinFramework G ends (fun v => g (p v))
      = (pointJoinFramework G ends p).mapSupport
          (BodyHingeFramework.screwEquivOfLinearEquiv g) := by
  have hsupp : (pointJoinFramework G ends (fun v => g (p v))).supportExtensor
      = ((pointJoinFramework G ends p).mapSupport
          (BodyHingeFramework.screwEquivOfLinearEquiv g)).supportExtensor := by
    funext e
    simp only [BodyHingeFramework.mapSupport_supportExtensor, pointJoinFramework,
      BodyHingeFramework.screwEquivOfLinearEquiv_mk_extensor]
    congr 2
    funext i; fin_cases i <;> rfl
  exact congrArg (BodyHingeFramework.mk (k := 2) G) hsupp

/-- **The rank of a configuration is unchanged by scaling the heights and shifting them by a
globally affine height** (`lem:pencil-rank-scale-shift`; Phase 40b CARRIER, the last clause of
informal (MC-3)). For `t ≠ 0` and `a ∈ Aff(q)` (`Graph.affineLifts`), the configurations `(q, z)`
and `(q, t • z + a)` have the same row rank at `ofNormals` of their points. With
`a_w = h ⬝ (x_w, y_w, 1)` on `V(G)`, the invertible linear map
`(x, y, ζ, w) ↦ (x, y, t ζ + h ⬝ (x, y, w), w)` of `K⁴` carries `p_w` to the point of
`(q, t • z + a)` at every body of `G`; the ends of every link are bodies of `G` (`hends`), so the
two point-join frameworks agree on links (`span_rigidityRows_eq_of_supportExtensor_agree`), and a
collineation leaves the point-join rank unchanged (`pointJoinFramework_comp_eq_mapSupport`,
`BodyHingeFramework.finrank_span_rigidityRows_mapSupport`), as does the polarity back to
`ofNormals` (`ofNormals_toBodyHinge_eq_mapSupport_pointJoinFramework`). -/
theorem _root_.Graph.finrank_span_rigidityRows_ofNormals_smul_add_affineLifts {G : Graph α β}
    {ends : β → α × α} (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2)
    (q : α × Fin 2 → K) (z : α → K) {t : K} (ht : t ≠ 0) {a : α → K}
    (ha : a ∈ G.affineLifts q) :
    Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 2) G ends
        (fun p => pencilConfigPoint q (t • z + a) p.1 p.2)).toBodyHinge.rigidityRows)
      = Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 2) G ends
        (fun p => pencilConfigPoint q z p.1 p.2)).toBodyHinge.rigidityRows) := by
  classical
  obtain ⟨h, rfl⟩ := ha
  let f : (Fin 4 → K) →ₗ[K] (Fin 4 → K) :=
    { toFun := fun b => ![b 0, b 1, t * b 2 + (h 0 * b 0 + h 1 * b 1 + h 2 * b 3), b 3]
      map_add' := fun b c => by funext i; fin_cases i <;> simp; ring
      map_smul' := fun c b => by funext i; fin_cases i <;> simp; ring }
  let f' : (Fin 4 → K) →ₗ[K] (Fin 4 → K) :=
    { toFun := fun b => ![b 0, b 1, t⁻¹ * (b 2 - (h 0 * b 0 + h 1 * b 1 + h 2 * b 3)), b 3]
      map_add' := fun b c => by funext i; fin_cases i <;> simp; ring
      map_smul' := fun c b => by funext i; fin_cases i <;> simp; ring }
  let g : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K) := LinearEquiv.ofLinearMap f f'
    (LinearMap.ext fun b => funext fun i => by fin_cases i <;> simp [f, f']; field_simp; ring)
    (LinearMap.ext fun b => funext fun i => by fin_cases i <;> simp [f, f']; field_simp)
  have hg : ∀ w ∈ V(G),
      g (pencilConfigPoint q z w) = pencilConfigPoint q (t • z + G.affineLiftMap q h) w := by
    intro w hw
    funext i
    fin_cases i <;> simp [g, f, pencilConfigPoint, pencilPicturePoint, hw, dotProduct,
      Fin.sum_univ_three]
  have hspan : Submodule.span K
        (pointJoinFramework G ends (pencilConfigPoint q (t • z + G.affineLiftMap q h))).rigidityRows
      = Submodule.span K
        (pointJoinFramework G ends (fun w => g (pencilConfigPoint q z w))).rigidityRows :=
    span_rigidityRows_eq_of_supportExtensor_agree _ _ rfl fun e u v he => by
      have h0 := hends e u v he
      simp only [pointJoinFramework, hg _ h0.left_mem, hg _ h0.right_mem]
  rw [ofNormals_toBodyHinge_eq_mapSupport_pointJoinFramework G ends
      (pencilConfigPoint q (t • z + G.affineLiftMap q h)),
    BodyHingeFramework.finrank_span_rigidityRows_mapSupport, hspan,
    pointJoinFramework_comp_eq_mapSupport, BodyHingeFramework.finrank_span_rigidityRows_mapSupport,
    ofNormals_toBodyHinge_eq_mapSupport_pointJoinFramework G ends (pencilConfigPoint q z),
    BodyHingeFramework.finrank_span_rigidityRows_mapSupport]

/-! ## The pencil condition is linear in the heights (Phase 40b CARRIER slice C5′,
`lem:pencil-condition-linear`) -/

/-- **Coplanar closed neighbourhoods force `z ∈ L(q)`, over an admissible picture**
(`lem:pencil-condition-linear`; Phase 40b CARRIER, informal (MC-1)'s converse). If a height `z`
vanishes off `V(G)` and, at every body `v` of `G`, some nonzero `n : K⁴` annihilates the
configuration point of every member of the closed neighbourhood of `v`, then `z ∈ L(q)`.

Route: expand `n ⬝ᵥ p_w` as `(n₀, n₁, n₃) ⬝ᵥ (x_w, y_w, 1) + n₂ z_w`. Admissibility gives, at `v`,
three closed-neighbourhood members `t` with independent picture points; if `n₂ = 0` the relation at
each `t i` puts `(n₀, n₁, n₃)` in the kernel of the unit matrix of their picture points
(`Matrix.linearIndependent_rows_iff_isUnit`), forcing it (hence all of `n`, since `n₂ = 0`) to
vanish, contradicting `n ≠ 0`. So `n₂ ≠ 0`, and solving the relation for `z_w` exhibits `L(q)`'s
affine coefficients `h = -(n₂)⁻¹ • (n₀, n₁, n₃)` at `v`. -/
theorem _root_.Graph.IsAdmissiblePicture.mem_liftingSpace_of_coplanar {G : Graph α β}
    {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) {z : α → K}
    (hs : ∀ w ∉ V(G), z w = 0)
    (hcop : ∀ v ∈ V(G), ∃ n : Fin 4 → K, n ≠ 0 ∧
      ∀ w ∈ G.closedNbhd v, n ⬝ᵥ pencilConfigPoint q z w = 0) :
    z ∈ G.liftingSpace q := by
  refine ⟨hs, fun v hv => ?_⟩
  obtain ⟨n, hn, hnw⟩ := hcop v hv
  obtain ⟨t, ht, hli⟩ := hq.2 v hv
  have hexp : ∀ w, n ⬝ᵥ pencilConfigPoint q z w =
      ![n 0, n 1, n 3] ⬝ᵥ pencilPicturePoint q w + n 2 * z w := by
    intro w
    simp [dotProduct, Fin.sum_univ_four, Fin.sum_univ_three, pencilConfigPoint,
      pencilPicturePoint]
    ring
  have hn2 : n 2 ≠ 0 := by
    intro h2
    have hunit : IsUnit (Matrix.of fun i => pencilPicturePoint q (t i)) :=
      Matrix.linearIndependent_rows_iff_isUnit.mp hli
    have hzero : (Matrix.of fun i => pencilPicturePoint q (t i)) *ᵥ ![n 0, n 1, n 3] =
        (Matrix.of fun i => pencilPicturePoint q (t i)) *ᵥ 0 := by
      rw [Matrix.mulVec_zero]
      funext i
      have := hnw (t i) (ht i)
      rw [hexp, h2, zero_mul, add_zero] at this
      simp only [Matrix.mulVec, Matrix.of_apply, Pi.zero_apply]
      rwa [dotProduct_comm]
    have h3 := Matrix.mulVec_injective_iff_isUnit.mpr hunit hzero
    apply hn
    funext i
    fin_cases i
    · simpa using congr_fun h3 0
    · simpa using congr_fun h3 1
    · exact h2
    · simpa using congr_fun h3 2
  refine ⟨-(n 2)⁻¹ • ![n 0, n 1, n 3], fun w hw => ?_⟩
  have := hnw w hw
  rw [hexp] at this
  rw [smul_dotProduct, smul_eq_mul]
  field_simp
  linear_combination this

/-- **Every nonzero normal of a closed neighbourhood is the interpolant, up to a nonzero scalar**
(`lem:pencil-condition-linear`; Phase 40b CARRIER, informal (MC-1)'s "unique, non-vertical plane",
in interpolant form). Over an admissible picture, at a body `v` where `z` restricts on the closed
neighbourhood to the affine function `h`, any nonzero `n : K⁴` orthogonal to the whole closed
neighbourhood is a nonzero scalar multiple of `(h₀, h₁, -1, h₂)`: in particular its third
coordinate is nonzero (the plane is non-vertical) and it is determined by `h` up to scale (the
plane is unique).

Route, as in `exists_smul_pencilNormalOfPicture_eq_of_mem_closedNbhd`: both `n` and the interpolant
`m = (h₀, h₁, -1, h₂)` lie in the common perp `W` of the three independent configuration points an
admissible selector at `v` supplies (`n` by hypothesis, `m` by direct computation from `hh`); `W` is
one-dimensional (`finrank_toDualPerp_triple_eq`), so it is spanned by the nonzero `m`
(`Submodule.eq_of_le_of_finrank_eq`), and `n` is a scalar multiple. -/
theorem _root_.Graph.IsAdmissiblePicture.exists_smul_eq_interpolant {G : Graph α β}
    {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) {z : α → K} {v : α} (hv : v ∈ V(G))
    {h : Fin 3 → K} (hh : ∀ w ∈ G.closedNbhd v, z w = h ⬝ᵥ pencilPicturePoint q w)
    {n : Fin 4 → K} (hn : n ≠ 0)
    (hnw : ∀ w ∈ G.closedNbhd v, n ⬝ᵥ pencilConfigPoint q z w = 0) :
    ∃ c : K, c ≠ 0 ∧ n = c • ![h 0, h 1, -1, h 2] := by
  obtain ⟨t, ht, hli⟩ := hq.2 v hv
  set m : Fin 4 → K := ![h 0, h 1, -1, h 2] with hmdef
  have hLIc : LinearIndependent K (fun i => pencilConfigPoint q z (t i)) :=
    linearIndependent_pencilConfigPoint_of_linearIndependent_pencilPicturePoint z hli
  have hm : m ≠ 0 := fun h0 => by simpa [hmdef] using congr_fun h0 2
  set W : Submodule K (Fin 4 → K) := ⨅ j : Fin 3, LinearMap.ker
      ((Pi.basisFun K (Fin 4)).toDual.flip ((fun i => pencilConfigPoint q z (t i)) j))
    with hWdef
  have hWdim : Module.finrank K W = 1 := finrank_toDualPerp_triple_eq hLIc
  have hmemW : ∀ x : Fin 4 → K, x ∈ W ↔ ∀ j, x ⬝ᵥ pencilConfigPoint q z (t j) = 0 := by
    intro x
    simp only [hWdef, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply,
      piBasisFun_toDual_eq_dotProduct]
  have hnmem : n ∈ W := (hmemW n).mpr fun j => hnw _ (ht j)
  have hmmem : m ∈ W := by
    rw [hmemW]
    intro j
    have := hh _ (ht j)
    simp only [hmdef, pencilConfigPoint, pencilPicturePoint, dotProduct, Fin.sum_univ_four,
      Fin.sum_univ_three] at this ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at this ⊢
    rw [this]; ring
  have hspan : Submodule.span K ({m} : Set (Fin 4 → K)) = W := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]; simpa using hmmem
    · rw [hWdim, finrank_span_singleton hm]
  rw [← hspan] at hnmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hnmem
  exact ⟨c, fun hc0 => hn (by rw [← hc, hc0, zero_smul]), hc.symm⟩

end CombinatorialRigidity.Molecular
