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
# Planar pictures, the lifting space and the main pictures

The definitions of `sec:main-component-carrier`, and its lemmas that do not read a configuration as
a pencil realization (those are in `Configuration.lean`). A planar picture `q : α × Fin 2 → K`
places each body `v` at `q_v = (x_v, y_v)`, and a height `z : α → K` lifts it to the configuration
point `p_v = (x_v, y_v, z_v, 1) ∈ K⁴` (`pencilConfigPoint`). The picture is admissible when the two
ends of every link sit at distinct points and no closed neighbourhood lies on a line
(`Graph.IsAdmissiblePicture`). The lifting space `L(q)` is the space of heights that agree on every
closed neighbourhood with an affine function of the picture (`Graph.liftingSpace`); over an
admissible picture, these are the heights at which the configuration points of every closed
neighbourhood lie in a plane (`lem:pencil-condition-linear`). In the language of scene analysis,
`L(q)` is the space of heights of the liftings of `q`, for the incidence structure whose faces are
the closed neighbourhoods, and the heights of one affine function at every body
(`Graph.affineLifts`) are its trivial liftings (Whiteley 1996, §8.3). The main pictures are the
admissible pictures at which `dim L(q)` is least (`Graph.IsMainPicture`). The general configuration
of `G` attains when, off the zero set of a nonzero polynomial in the picture, the heights in `L(q)`
at which the configuration has the deficiency rank contain a nonempty Zariski-open subset of `L(q)`
(`Graph.X0Attains`).

The lifting system (`Graph.liftingMatrix`) is a matrix of polynomials in the picture, whose
solutions pair a height in `L(q)` with the affine functions that it agrees with on the closed
neighbourhoods. With the polynomial section of a kernel (`lem:pencil-polynomial-section`), it
extends a height at a main picture to heights at the general picture, which proves
`lem:pencil-x0-one-witness` (`Graph.x0Attains_of_exists`): if one configuration over a main picture
has the deficiency rank, the general configuration attains. For `lem:pencil-x0-main-picture-open`,
the bodies placed on a parabola give an admissible picture, and the non-roots of a nonzero
polynomial are main pictures. The difference of the planes at two bodies (`planeDiff`) serves the
steps at an open ear with one or two interior bodies (`sec:main-component-orbit`), and the lifting
system with weights (`Graph.weightedLiftingMatrix`) the contraction step
(`sec:main-component-contract`).

Pictures are uncurried, `q : α × Fin 2 → K`, as are the normals `α × Fin 4 → K` that
`PanelHingeFramework.ofNormals` takes and the variables of the rank polynomials. `X0Attains` asks
for a nonempty Zariski-open set of attaining heights over each picture, not for one height, so that
a step can meet them with the non-roots of another polynomial on the same fibre `L(q)`
(`lem:pencil-x0-fibre-intersection`).

## Main definitions

* `pencilPicturePoint` and `pencilConfigPoint`: the homogeneous picture point `(x_v, y_v, 1)` and
  the configuration point `(x_v, y_v, z_v, 1)`.
* `Graph.IsAdmissiblePicture`: the admissible pictures.
* `Graph.liftingSpace`, `Graph.affineLiftMap` and `Graph.affineLifts`: the lifting space `L(q)` and
  the globally affine heights `Aff(q)`.
* `Graph.IsMainPicture`: the main pictures.
* `pencilNormalOfPicture`: the plane normal at a body, the `cross₃` of the configuration points of
  three chosen bodies.
* `Graph.X0Attains`: the general configuration of `G` attains.
* `Graph.liftingMatrix` and `Graph.weightedLiftingMatrix`: the lifting system, and the lifting
  system with weights.
* `planeDiff`: the difference `h_a − h_b` of the planes at two bodies, at a solution of the lifting
  system.

## Main results

* `Graph.isAdmissiblePicture_congr` and `Graph.liftingSpace_congr`: admissibility and `L(q)` read
  the picture only at the bodies of `G`.
* `Graph.affineLifts_le_liftingSpace`, `Graph.finrank_affineLifts` and
  `Graph.three_le_finrank_liftingSpace`: `Aff(q) ⊆ L(q)`, and `dim Aff(q) = 3 ≤ dim L(q)` at an
  admissible picture.
* `Graph.IsAdmissiblePicture.supportExtensor_ne_zero`: over an admissible picture every hinge of the
  configuration is nonzero, at every height.
* `Graph.IsAdmissiblePicture.exists_mvPolynomial`: the admissible pictures contain the non-roots of
  a polynomial nonzero at a given one.
* `Graph.map_ker_liftingMatrix` and `Graph.finrank_ker_liftingMatrix`: the heights of the solutions
  of the lifting system form `L(q)`, and over an admissible picture the solutions form a space of
  dimension `dim L(q)`.
* `Graph.ker_liftingMatrix_congr`: the solutions read the picture only at the bodies of the graph.
* `Graph.two_le_finrank_map_planeDiff`: the incidence functionals at two bodies are independent
  (`lem:pencil-flag-genericity`).
* `Graph.x0Attains_of_exists`: one attaining configuration over a main picture makes the general
  configuration attain.
* `Graph.exists_isMainPicture`, `Graph.IsMainPicture.exists_mvPolynomial` and
  `Graph.exists_mvPolynomial_isMainPicture`: the main pictures exist and contain the non-roots of a
  nonzero polynomial.
-/

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K]
variable {α β : Type*}

/-! ## Planar pictures and admissibility -/

/-- **The homogeneous picture point** (`def:pencil-admissible-picture`): the point
`(x_w, y_w, 1) ∈ K³` of the planar picture `q` at the body `w`. Three picture points are collinear
exactly when their homogeneous picture points are linearly dependent. -/
def pencilPicturePoint (q : α × Fin 2 → K) (w : α) : Fin 3 → K :=
  ![q (w, 0), q (w, 1), 1]

/-- **An admissible planar picture** (`def:pencil-admissible-picture`): the picture `q` puts the two
ends of every link of `G` at distinct points of `K²`, and at every body `v` of `G` three members of
the closed neighbourhood `G.closedNbhd v` have linearly independent homogeneous picture points, that
is, the picture points of the closed neighbourhood do not lie on one line. The condition names three
members, as the plane normal `pencilNormalOfPicture` is computed from three points
(`cross₃_ne_zero_iff_linearIndependent`) and the openness of admissibility tests one `3 × 3`
determinant per body (`Graph.IsAdmissiblePicture.exists_mvPolynomial`). -/
def _root_.Graph.IsAdmissiblePicture (G : Graph α β) (q : α × Fin 2 → K) : Prop :=
  (∀ e u v, G.IsLink e u v → pencilPicturePoint q u ≠ pencilPicturePoint q v) ∧
  ∀ v ∈ V(G), ∃ t : Fin 3 → α, (∀ i, t i ∈ G.closedNbhd v) ∧
    LinearIndependent K (fun i => pencilPicturePoint q (t i))

/-- **Admissibility reads the picture only on `V(G)`** (`lem:pencil-picture-local`, its first half):
two pictures that agree at every body of `G` are admissible for `G` together. Admissibility reads
the picture at the two ends of each link and on each closed neighbourhood, and all of these are
bodies of `G`. -/
theorem _root_.Graph.isAdmissiblePicture_congr {G : Graph α β} {q q' : α × Fin 2 → K}
    (hq : ∀ w ∈ V(G), ∀ i, q (w, i) = q' (w, i)) :
    G.IsAdmissiblePicture q ↔ G.IsAdmissiblePicture q' := by
  have hpp : ∀ w ∈ V(G), pencilPicturePoint q w = pencilPicturePoint q' w := by
    intro w hw; funext i; fin_cases i <;> simp [pencilPicturePoint, hq w hw]
  have hN : ∀ v ∈ V(G), ∀ w ∈ G.closedNbhd v, w ∈ V(G) := fun _ hv _ hw =>
    Graph.closedNbhd_subset_vertexSet hv hw
  unfold Graph.IsAdmissiblePicture
  refine and_congr (forall_congr' fun e => forall₂_congr fun u v => imp_congr_right fun he => ?_)
    (forall₂_congr fun v hv => exists_congr fun t => and_congr_right fun ht => ?_)
  · rw [hpp u he.left_mem, hpp v he.right_mem]
  · have : (fun i => pencilPicturePoint q (t i)) = fun i => pencilPicturePoint q' (t i) :=
      funext fun i => hpp _ (hN v hv _ (ht i))
    rw [this]

/-- **An admissible picture puts three members in every closed neighbourhood** (a step of
`thm:pencil-x0-splitoff` and `lem:pencil-one-ear-base`): at a body `v` of `G`, the closed
neighbourhood has at least three members, as the three members with independent picture points that
admissibility gives are pairwise distinct. -/
theorem _root_.Graph.IsAdmissiblePicture.three_le_ncard_closedNbhd [Finite α] {G : Graph α β}
    {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) {v : α} (hv : v ∈ V(G)) :
    3 ≤ (G.closedNbhd v).ncard := by
  obtain ⟨t, ht, hli⟩ := hq.2 v hv
  have htinj : Function.Injective t := fun i j hij => hli.injective (by simp [hij])
  have := Set.ncard_le_ncard (s := Set.range t) (by rintro _ ⟨i, rfl⟩; exact ht i)
    (Set.toFinite _)
  rwa [Set.ncard_range_of_injective htinj, Nat.card_eq_fintype_card, Fintype.card_fin] at this

/-- **A closed neighbourhood inside three bodies has independent picture points** (a step of
`lem:pencil-splitoff-flexes` and `thm:pencil-x0-open-ear-one`): at an admissible picture, if the
closed neighbourhood of a body `v` of `G` lies in `{u₀, u₁, u₂}`, the homogeneous picture points of
`u₀`, `u₁` and `u₂` are linearly independent, as the three members that admissibility gives span
`K³` and lie among them. -/
theorem _root_.Graph.IsAdmissiblePicture.linearIndependent_of_closedNbhd_subset
    {G : Graph α β} {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) {v : α} (hv : v ∈ V(G))
    {u₀ u₁ u₂ : α} (hN : G.closedNbhd v ⊆ {u₀, u₁, u₂}) :
    LinearIndependent K ![pencilPicturePoint q u₀, pencilPicturePoint q u₁,
      pencilPicturePoint q u₂] := by
  obtain ⟨t, ht, hli⟩ := hq.2 v hv
  refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ (by simp)
  have htop : Submodule.span K (Set.range fun i => pencilPicturePoint q (t i)) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simp)
  rw [← htop]
  refine Submodule.span_mono ?_
  rintro _ ⟨i, rfl⟩
  rcases hN (ht i) with h | h | h
  · exact ⟨0, by simp [h]⟩
  · exact ⟨1, by simp [h]⟩
  · rw [Set.mem_singleton_iff] at h
    exact ⟨2, by simp [h]⟩

/-! ## The lifting space -/

/-- **The lifting space `L(q)`** (`def:pencil-lifting-space`): the heights `z : α → K` that vanish
off `V(G)` and, at every body `v` of `G`, agree on the closed neighbourhood `G.closedNbhd v` with an
affine function of the picture: some `h : Fin 3 → K` has `z w = h ⬝ᵥ (x_w, y_w, 1)` for every `w` in
the neighbourhood. Over an admissible picture, a height that vanishes off `V(G)` lies in `L(q)`
exactly when the configuration points of every closed neighbourhood lie in a plane
(`Graph.IsAdmissiblePicture.mem_liftingSpace_iff_coplanar`, `lem:pencil-condition-linear`). In the
language of scene analysis, `L(q)` is the space of heights of the liftings of `q`, for the incidence
structure whose faces are the closed neighbourhoods (Whiteley 1996, §8.3). As its heights vanish off
`V(G)`, `dim L(q)` is the dimension of a space of heights on `V(G)`, also when `G` does not contain
every body (`fmlnote:pencil-lifting-space`). -/
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

/-- **The lifting space reads the picture only on `V(G)`** (`lem:pencil-picture-local`, its second
half): two pictures that agree at every body of `G` have the same `L(q)`. The lifting space reads
the picture on each closed neighbourhood, whose members are bodies of `G`. -/
theorem _root_.Graph.liftingSpace_congr {G : Graph α β} {q q' : α × Fin 2 → K}
    (hq : ∀ w ∈ V(G), ∀ i, q (w, i) = q' (w, i)) : G.liftingSpace q = G.liftingSpace q' := by
  have hpp : ∀ w ∈ V(G), pencilPicturePoint q w = pencilPicturePoint q' w := by
    intro w hw; funext i; fin_cases i <;> simp [pencilPicturePoint, hq w hw]
  have hN : ∀ v ∈ V(G), ∀ w ∈ G.closedNbhd v, w ∈ V(G) := fun _ hv _ hw =>
    Graph.closedNbhd_subset_vertexSet hv hw
  ext z
  simp only [Graph.mem_liftingSpace]
  refine and_congr_right fun _ => forall₂_congr fun v hv => exists_congr fun h =>
    forall₂_congr fun w hw => ?_
  rw [hpp w (hN v hv w hw)]

/-- **The main pictures** (`def:pencil-main-picture`): the admissible pictures whose lifting space
has the least dimension `ℓ₀` among all admissible pictures. Over the main pictures the
configurations `(q, z)` with `z ∈ L(q)` form a vector bundle, whose closure is the main component of
the pencil configuration space (`rem:pencil-x0-main-component`). `Graph.x0Attains_of_exists` asks
for its configuration over a main picture `q₀`, so that `dim L(q) ≥ dim L(q₀)` at every admissible
picture `q`. -/
def _root_.Graph.IsMainPicture (G : Graph α β) (q : α × Fin 2 → K) : Prop :=
  G.IsAdmissiblePicture q ∧ ∀ q' : α × Fin 2 → K, G.IsAdmissiblePicture q' →
    Module.finrank K (G.liftingSpace q) ≤ Module.finrank K (G.liftingSpace q')

/-! ## The globally affine heights `Aff(q)` -/

open Classical in
/-- **The affine lift map** (the map onto `Aff(q)` of `def:pencil-lifting-space`): the linear map
that sends a triple of affine coefficients `h : Fin 3 → K` to the height `w ↦ h ⬝ᵥ (x_w, y_w, 1)` on
`V(G)`, zero off `V(G)`. Its range is `Graph.affineLifts`. -/
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

/-- **The globally affine heights `Aff(q)`** (`def:pencil-lifting-space`): the heights
`w ↦ h ⬝ᵥ (x_w, y_w, 1)` of a single triple of affine coefficients `h : Fin 3 → K`, the same at
every body, on `V(G)`, and zero off `V(G)` as in `Graph.liftingSpace`: the range of
`Graph.affineLiftMap`. They are the trivial liftings of scene analysis, which put all the faces in
one plane. -/
noncomputable def _root_.Graph.affineLifts (G : Graph α β) (q : α × Fin 2 → K) :
    Submodule K (α → K) :=
  LinearMap.range (G.affineLiftMap q)

/-- **`Aff(q) ⊆ L(q)`, at every picture** (`lem:pencil-lifting-space-affine`): a single triple of
affine coefficients `h` gives an affine function of the picture on every closed neighbourhood, the
same `h` at every body of `G`, so no admissibility is needed. -/
theorem _root_.Graph.affineLifts_le_liftingSpace (G : Graph α β) (q : α × Fin 2 → K) :
    G.affineLifts q ≤ G.liftingSpace q := by
  rintro z ⟨h, rfl⟩
  refine ⟨fun w hw => by simp [hw], fun v hv => ⟨h, fun w hw => ?_⟩⟩
  simp [Graph.closedNbhd_subset_vertexSet hv hw]

/-- **`Aff(q)` is three-dimensional at an admissible picture** (`lem:pencil-lifting-space-affine`):
if `G` has a body, the affine lift map is injective. Admissibility gives, at a body `v₀` of `G`,
three members of its closed neighbourhood, which are bodies of `G`, with linearly independent
homogeneous picture points; a triple `h` in the kernel has dot product zero with all three, so
`h = 0`, as the `3 × 3` matrix of these points is a unit. -/
theorem _root_.Graph.finrank_affineLifts [Finite α] {G : Graph α β} {q : α × Fin 2 → K}
    (hq : G.IsAdmissiblePicture q) (hV : V(G).Nonempty) :
    Module.finrank K (G.affineLifts q) = 3 := by
  have : Fintype α := Fintype.ofFinite α
  obtain ⟨v₀, hv₀⟩ := hV
  obtain ⟨t, ht, hli⟩ := hq.2 v₀ hv₀
  have hinj : Function.Injective (G.affineLiftMap q) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro h hh
    have htV : ∀ i, t i ∈ V(G) := fun i => Graph.closedNbhd_subset_vertexSet hv₀ (ht i)
    have hunit : IsUnit (Matrix.of fun i => pencilPicturePoint q (t i)) :=
      Matrix.linearIndependent_row_iff_isUnit.mp hli
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

/-- **`3 ≤ dim L(q)` at an admissible picture** (`lem:pencil-lifting-space-affine`): if `G` has a
body, by `Aff(q) ⊆ L(q)` (`Graph.affineLifts_le_liftingSpace`) and `dim Aff(q) = 3`
(`Graph.finrank_affineLifts`), as `finrank` is monotone on submodules (`Submodule.finrank_mono`). -/
theorem _root_.Graph.three_le_finrank_liftingSpace [Finite α] {G : Graph α β}
    {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) (hV : V(G).Nonempty) :
    3 ≤ Module.finrank K (G.liftingSpace q) := by
  have : Fintype α := Fintype.ofFinite α
  rw [← G.finrank_affineLifts hq hV]
  exact Submodule.finrank_mono (G.affineLifts_le_liftingSpace q)

/-! ## Configuration points and plane normals -/

/-- **The homogeneous configuration point** (`def:pencil-configuration`): the point
`p_w = (x_w, y_w, z_w, 1) ∈ K⁴` of the configuration `(q, z)` at the body `w`. Its coordinates are
affine in the picture and the height, and its first, second and fourth coordinates are those of the
homogeneous picture point (`pencilPicturePoint`). -/
def pencilConfigPoint (q : α × Fin 2 → K) (z : α → K) (w : α) : Fin 4 → K :=
  ![q (w, 0), q (w, 1), z w, 1]

/-- **The plane normal of a configuration** (`def:pencil-configuration`): at the body `v`, the
`cross₃` of the configuration points of the three bodies that `sel v` names, a normal of the plane
through them, polynomial in `(q, z)`. The selector is a plain triple of bodies, not an
`IsFin3SelectorOf`, which lists every member of a set of at most three bodies and pads the empty
slots: a closed neighbourhood may have more than three members, and the normal is read off three of
their configuration points. When the three bodies lie in `G.closedNbhd v` with independent picture
points and `z ∈ L(q)`, this normal is nonzero (`pencilNormalOfPicture_ne_zero_iff`) and orthogonal
to the configuration points of the whole closed neighbourhood
(`dotProduct_pencilNormalOfPicture_eq_zero_of_mem_closedNbhd`, `Configuration.lean`). -/
noncomputable def pencilNormalOfPicture (q : α × Fin 2 → K) (z : α → K) (sel : α → Fin 3 → α)
    (v : α) : Fin 4 → K :=
  cross₃ (pencilConfigPoint q z (sel v 0)) (pencilConfigPoint q z (sel v 1))
    (pencilConfigPoint q z (sel v 2))

/-! ## The general configuration attains -/

/-- **The general configuration of `G` attains** (`def:pencil-x0-attains`): for some endpoint
selector `ends` recording every link of `G` and some nonzero polynomial `P` in the picture
coordinates, every picture `q` off the zero set of `P` is admissible, and the heights `z ∈ L(q)` at
which the configuration's row rank equals `6(|V(G)| − 1) − def₃(G)` contain a nonempty Zariski-open
subset of `L(q)`: the non-roots in `L(q)` of a polynomial `R` in the height coordinates, at least
one of which lies in `L(q)`.

The rank is that of `PanelHingeFramework.ofNormals G ends` at the configuration points (the polar of
the point-join framework, of the same rank, `lem:pencil-config-point-join-rank`, with nonzero hinges
wherever adjacent picture points differ). The open set of attaining heights lets a step meet them
with the non-roots of another polynomial that is nonzero somewhere on the same fibre `L(q)`
(`lem:pencil-x0-fibre-intersection`); `lem:pencil-x0-attains-distinct` uses one attaining
configuration.

`P ≠ 0` means "off a proper Zariski-closed set of pictures" only over an infinite field: over a
finite field a nonzero polynomial can vanish at every point (`X ^ |K| − X`), and `X0Attains` then
holds vacuously. The lemmas that obtain a realization from it assume an infinite field
(`[Infinite K]`), so the definition needs no such hypothesis of its own. -/
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

/-- **Configuration points over distinct picture points are independent** (a step of
`lem:pencil-config-point-join-rank`): two configuration points `p_u = (x_u, y_u, z_u, 1)` and
`p_v = (x_v, y_v, z_v, 1)` whose picture points differ are linearly independent, whatever the
heights: a relation `s p_u + t p_v = 0` has `s + t = 0` in the last coordinate, so
`s (q_u − q_v) = 0` in the picture coordinates. -/
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

/-- **Distinct picture points are independent** (a step of `lem:pencil-flat-split`,
`lem:pencil-lifting-planes-motions` and `lem:pencil-lifting-space-deficiency`): two homogeneous
picture points `(x_u, y_u, 1)` and `(x_v, y_v, 1)` that differ are linearly independent, as a
relation `s p̂_u + t p̂_v = 0` has `s + t = 0` in the last coordinate, so `s (q_u − q_v) = 0`. -/
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

/-- **The hinges of a configuration over an admissible picture are nonzero** (a step of
`lem:pencil-x0-one-witness`, whose proof names it): over an admissible picture `q`, at every height
`z`, the framework `ofNormals G ends` at the configuration points has a nonzero support extensor at
every link: the extensor is nonzero exactly when the two endpoint points are independent
(`PanelHingeFramework.toBodyHinge_supportExtensor_ne_zero_iff`), and adjacent picture points differ
(`linearIndependent_pencilConfigPoint_pair`). -/
theorem _root_.Graph.IsAdmissiblePicture.supportExtensor_ne_zero {G : Graph α β}
    {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) {ends : β → α × α}
    (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2) (z : α → K)
    {e : β} {u v : α} (he : G.IsLink e u v) :
    (PanelHingeFramework.ofNormals (k := 2) G ends
      (fun p => pencilConfigPoint q z p.1 p.2)).toBodyHinge.supportExtensor e ≠ 0 := by
  rw [PanelHingeFramework.toBodyHinge_supportExtensor_ne_zero_iff]
  exact linearIndependent_pencilConfigPoint_pair z (hq.1 e _ _ (hends e u v he))

/-! ## Admissibility is Zariski-open -/

/-- **The homogeneous picture point as polynomials**: the vector `(X_{w,0}, X_{w,1}, 1)` of
polynomials in the picture coordinates, which evaluates to `pencilPicturePoint q w`
(`eval_pencilPicturePointPoly`). -/
noncomputable def pencilPicturePointPoly (w : α) : Fin 3 → MvPolynomial (α × Fin 2) K :=
  ![MvPolynomial.X (w, 0), MvPolynomial.X (w, 1), 1]

@[simp]
theorem eval_pencilPicturePointPoly (q : α × Fin 2 → K) (w : α) (i : Fin 3) :
    MvPolynomial.eval q (pencilPicturePointPoly w i) = pencilPicturePoint q w i := by
  fin_cases i <;> simp [pencilPicturePointPoly, pencilPicturePoint]

/-- **Admissibility is Zariski-open** (the openness noted after `def:pencil-admissible-picture`; a
step of `lem:pencil-x0-one-witness` and `lem:pencil-x0-main-picture-open`, whose proofs name it):
around an admissible picture `q₀` there is a polynomial `P` in the picture coordinates, nonzero at
`q₀`, off whose zero set every picture is admissible. `P` is the product of one coordinate
difference per ordered pair of adjacent bodies (in a coordinate in which their picture points at
`q₀` differ) and one `3 × 3` determinant per body of `G` (of the homogeneous picture points of three
members of its closed neighbourhood that are independent at `q₀`). -/
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
/-- **The lifting system** (`def:pencil-lifting-system`): a matrix of polynomials in the picture
coordinates whose kernel at a picture `q` is the space of pairs `(z, h)` of a height `z` and affine
coefficients `h_v ∈ K³` at each body, with `z` zero off `V(G)`, `z_w = h_v ⬝ᵥ (x_w, y_w, 1)` for
every body `v` of `G` and every `w` in its closed neighbourhood, and `h_v = 0` off `V(G)`
(`Graph.liftingMatrix_mulVec_eq_zero_iff`). The heights of its solutions form the lifting space
(`Graph.map_ker_liftingMatrix`), and over an admissible picture its solutions form a space of
dimension `dim L(q)` (`Graph.finrank_ker_liftingMatrix`). Its rows: one per body for the support of
the heights, one per pair `(v, w)` (zero unless `w` lies in the closed neighbourhood of a body `v`
of `G`), and one per body and coordinate for the support of the coefficients. Its entries are
constants and the negated picture coordinates. -/
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


/-- **The kernel of the lifting system** (the solutions of `def:pencil-lifting-system`): at a
picture `q`, a pair `x = (z, h)` lies in the kernel exactly when `z` vanishes off `V(G)`, agrees on
the closed neighbourhood of every body `v` of `G` with the affine function of coefficients `h_v`,
and `h` vanishes off `V(G)`. -/
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

/-- **Membership in the kernel of the lifting system** (a step of `lem:pencil-splitoff-flexes`):
`Graph.liftingMatrix_mulVec_eq_zero_iff`, stated for membership in the kernel of the linear map. -/
theorem _root_.Graph.mem_ker_liftingMatrix_iff [Fintype α] {G : Graph α β}
    {q : α × Fin 2 → K} {x : α ⊕ (α × Fin 3) → K} :
    x ∈ LinearMap.ker ((G.liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin ↔
      (∀ w ∉ V(G), x (Sum.inl w) = 0) ∧
      (∀ v ∈ V(G), ∀ w ∈ G.closedNbhd v,
        x (Sum.inl w) = (fun i => x (Sum.inr (v, i))) ⬝ᵥ pencilPicturePoint q w) ∧
      ∀ v ∉ V(G), ∀ i, x (Sum.inr (v, i)) = 0 := by
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Graph.liftingMatrix_mulVec_eq_zero_iff]

/-- **The heights of the solutions of the lifting system form the lifting space**
(`def:pencil-lifting-system`): at every picture `q`, the projection of the kernel of the lifting
system to its height coordinates is `L(q)`. -/
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

/-- **Over an admissible picture the solutions of the lifting system have the dimension of the
lifting space** (`def:pencil-lifting-system`): the projection to the heights is injective on the
kernel, as the three independent homogeneous picture points that admissibility gives in each closed
neighbourhood determine the affine coefficients. -/
theorem _root_.Graph.finrank_ker_liftingMatrix [Fintype α] {G : Graph α β} {q : α × Fin 2 → K}
    (hq : G.IsAdmissiblePicture q) :
    Module.finrank K (LinearMap.ker ((G.liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin) =
      Module.finrank K (G.liftingSpace q) := by
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
        Matrix.linearIndependent_row_iff_isUnit.mp hli
      have hzero : (Matrix.of fun j => pencilPicturePoint q (t j)) *ᵥ
          (fun i => x (Sum.inr (v, i))) = (Matrix.of fun j => pencilPicturePoint q (t j)) *ᵥ 0 := by
        rw [Matrix.mulVec_zero]
        funext j
        simp only [Matrix.mulVec, Matrix.of_apply, Pi.zero_apply]
        rw [dotProduct_comm, ← h2 v hv (t j) (ht j), hz]
      exact congr_fun (Matrix.mulVec_injective_iff_isUnit.mpr hunit hzero) i
    · exact h3 v hv i

/-! ## The kernel of the lifting system: locality and monotonicity -/

/-- **The kernel of the lifting system reads the picture only on `V(H)`**
(`lem:pencil-weighted-lifting-system-local`): a closed neighbourhood of a body of `H` lies in `V(H)`
(`Graph.closedNbhd_subset_vertexSet`). -/
theorem _root_.Graph.ker_liftingMatrix_congr [Fintype α] {H : Graph α β} {q q' : α × Fin 2 → K}
    (hq : ∀ w ∈ V(H), ∀ i, q (w, i) = q' (w, i)) :
    LinearMap.ker ((H.liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin =
      LinearMap.ker ((H.liftingMatrix K).map (MvPolynomial.eval q')).mulVecLin := by
  have hpp : ∀ w ∈ V(H), pencilPicturePoint q w = pencilPicturePoint q' w := by
    intro w hw; funext i; fin_cases i <;> simp [pencilPicturePoint, hq w hw]
  ext y
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Graph.liftingMatrix_mulVec_eq_zero_iff]
  refine and_congr_right fun _ => and_congr_left fun _ => forall₂_congr fun v hv =>
    forall₂_congr fun w hw => ?_
  rw [hpp w (Graph.closedNbhd_subset_vertexSet hv hw)]

/-- **Adding links on the same bodies shrinks the kernel of the lifting system** (a step of
`thm:pencil-x0-splitoff`): if `H ≤ H'` with `V(H) = V(H')`, the kernel for `H'` lies in that for
`H`, as each closed neighbourhood in `H` lies in that in `H'`. -/
theorem _root_.Graph.ker_liftingMatrix_le_of_le [Fintype α] {H H' : Graph α β} (hle : H ≤ H')
    (hV : V(H) = V(H')) (q : α × Fin 2 → K) :
    LinearMap.ker ((H'.liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin ≤
      LinearMap.ker ((H.liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin := by
  intro y hy
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Graph.liftingMatrix_mulVec_eq_zero_iff]
    at hy ⊢
  obtain ⟨h1, h2, h3⟩ := hy
  refine ⟨fun w hw => h1 w (hV ▸ hw), fun v hv w hw => h2 v (hV ▸ hv) w ?_,
    fun v hv i => h3 v (hV ▸ hv) i⟩
  rcases hw with rfl | ⟨f, hf⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨f, hf.of_le hle⟩

/-! ## The incidence functionals at two bodies (`lem:pencil-flag-genericity`) -/

/-- **The difference of the planes at `a` and `b`** (`lem:pencil-flag-genericity`): at a solution
`(z, h)` of the lifting system, `h_a − h_b`, the coefficients of the difference of the affine
functions at `a` and `b`. -/
def planeDiff (a b : α) : (α ⊕ (α × Fin 3) → K) →ₗ[K] (Fin 3 → K) :=
  LinearMap.funLeft K K (fun i => Sum.inr (a, i)) - LinearMap.funLeft K K (fun i => Sum.inr (b, i))

theorem planeDiff_apply (a b : α) (x : α ⊕ (α × Fin 3) → K) (i : Fin 3) :
    planeDiff a b x i = x (Sum.inr (a, i)) - x (Sum.inr (b, i)) := rfl

/-- **The projection to the heights is injective on the kernel of the lifting system** at an
admissible picture (a step of `lem:pencil-flag-genericity`): the three independent picture points
that admissibility gives in each closed neighbourhood determine the affine coefficients. The proof
derives it from `Graph.finrank_ker_liftingMatrix` by rank–nullity. -/
theorem _root_.Graph.injective_liftingMatrix_ker_proj [Fintype α] {G : Graph α β}
    {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) :
    Function.Injective ((LinearMap.funLeft K K (Sum.inl : α → α ⊕ (α × Fin 3))).domRestrict
      (LinearMap.ker ((G.liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin)) := by
  set L := LinearMap.ker ((G.liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin
  set f := (LinearMap.funLeft K K (Sum.inl : α → α ⊕ (α × Fin 3))).domRestrict L
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_domRestrict, G.map_ker_liftingMatrix q] at h1
  have h2 : Module.finrank K L = Module.finrank K (G.liftingSpace q) :=
    Graph.finrank_ker_liftingMatrix hq
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.finrank_eq_zero.mp (by omega)

/-- **The incidence functionals at the two ends are independent** (`lem:pencil-flag-genericity`):
let `H` have the bodies of `G'`, and let every closed neighbourhood in `H` lie in that of the same
body in `G'`, except that the one of `a` may also contain `b` and the one of `b` may also contain
`a` (as when `H` joins `a` and `b`). If `q` is admissible for `G'` and
`dim L_H(q) + 2 ≤ dim L_{G'}(q)`, the two functionals `(z, h) ↦ (h_a − h_b) ⬝ᵥ (q_a, 1)` and
`(z, h) ↦ (h_a − h_b) ⬝ᵥ (q_b, 1)` are linearly independent on the kernel of the lifting system of
`G'`: their common zeros project injectively into `L_H(q)`. -/
theorem _root_.Graph.two_le_finrank_map_planeDiff [Fintype α] {G' H : Graph α β}
    {q : α × Fin 2 → K} (hq : G'.IsAdmissiblePicture q) {a b : α} (hV : V(H) = V(G'))
    (hN : ∀ v ∈ V(G'), ∀ w ∈ H.closedNbhd v,
      w ∈ G'.closedNbhd v ∨ (v = a ∧ w = b) ∨ (v = b ∧ w = a))
    (hdim : Module.finrank K (H.liftingSpace q) + 2 ≤ Module.finrank K (G'.liftingSpace q)) :
    2 ≤ Module.finrank K ((LinearMap.ker ((G'.liftingMatrix K).map
      (MvPolynomial.eval q)).mulVecLin).map
        ((Matrix.of ![pencilPicturePoint q a, pencilPicturePoint q b]).mulVecLin ∘ₗ
          planeDiff a b)) := by
  set L := LinearMap.ker ((G'.liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin with hL
  set E := (Matrix.of ![pencilPicturePoint q a, pencilPicturePoint q b]).mulVecLin with hE
  set Φ := (E ∘ₗ planeDiff a b).domRestrict L with hΦ
  set π := (LinearMap.funLeft K K (Sum.inl : α → α ⊕ (α × Fin 3))).domRestrict L with hπ
  have hπinj : Function.Injective π := Graph.injective_liftingMatrix_ker_proj hq
  have h1 := LinearMap.finrank_range_add_finrank_ker Φ
  rw [LinearMap.range_domRestrict, Graph.finrank_ker_liftingMatrix hq] at h1
  -- the kernel of `Φ` projects into `L_H(q)`
  have hker : (LinearMap.ker Φ).map π ≤ H.liftingSpace q := by
    rintro _ ⟨⟨x, hxL⟩, hxΦ, rfl⟩
    have hxΦ' : E (planeDiff a b x) = 0 := by
      have := LinearMap.mem_ker.mp hxΦ
      simpa [hΦ] using this
    have hEa : planeDiff a b x ⬝ᵥ pencilPicturePoint q a = 0 := by
      have := congr_fun hxΦ' 0
      simpa [hE, Matrix.mulVec, dotProduct_comm] using this
    have hEb : planeDiff a b x ⬝ᵥ pencilPicturePoint q b = 0 := by
      have := congr_fun hxΦ' 1
      simpa [hE, Matrix.mulVec, dotProduct_comm] using this
    obtain ⟨h0, h2, -⟩ := Graph.liftingMatrix_mulVec_eq_zero_iff.mp (LinearMap.mem_ker.mp hxL)
    refine ⟨fun w hw => h0 w (hV ▸ hw), fun v hv => ⟨fun i => x (Sum.inr (v, i)), fun w hw => ?_⟩⟩
    have hwV : w ∈ V(G') := hV ▸ Graph.closedNbhd_subset_vertexSet hv hw
    rw [hV] at hv
    simp only [π, LinearMap.domRestrict_apply, LinearMap.funLeft_apply]
    have hdiff : ∀ u, planeDiff a b x ⬝ᵥ pencilPicturePoint q u =
        (fun i => x (Sum.inr (a, i))) ⬝ᵥ pencilPicturePoint q u -
          (fun i => x (Sum.inr (b, i))) ⬝ᵥ pencilPicturePoint q u := by
      intro u
      rw [← sub_dotProduct]
      rfl
    rcases hN v hv w hw with hw' | ⟨hva, hwb⟩ | ⟨hvb, hwa⟩
    · exact h2 v hv w hw'
    · subst hva hwb
      rw [h2 w hwV w (Or.inl rfl)]
      have := hdiff w
      rw [hEb] at this
      linear_combination this
    · subst hvb hwa
      rw [h2 w hwV w (Or.inl rfl)]
      have := hdiff w
      rw [hEa] at this
      linear_combination -this
  have h2 : Module.finrank K (LinearMap.ker Φ) ≤ Module.finrank K (H.liftingSpace q) := by
    rw [LinearEquiv.finrank_eq (Submodule.equivMapOfInjective π hπinj (LinearMap.ker Φ))]
    exact Submodule.finrank_mono hker
  omega

/-! ## The lifting system with weights -/

open Classical in
/-- **The lifting system with weights** (`def:pencil-weighted-lifting-system`):
`Graph.liftingMatrix` with a vector of polynomials `ω v w ∈ K[σ]³` in place of the homogeneous
picture point `(x_w, y_w, 1)`. Its rows say `z_w = h_v ⬝ᵥ ω(v, w)` for `w` in the closed
neighbourhood of a body `v` of `G`, with the rows for the support of the heights and of the
coefficients (`Graph.weightedLiftingMatrix_mulVec_eq_zero_iff`). The contraction step reads the
closed neighbourhoods that meet the core through other vectors than the picture points
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

/-- **The kernel of the lifting system with weights** (the solutions of
`def:pencil-weighted-lifting-system`): at a point `s` of the parameters, a pair `x = (z, h)` lies in
the kernel exactly when `z` vanishes off `V(G)`, `z_w = h_v ⬝ᵥ ω(v, w)(s)` for every body `v` of `G`
and every `w` in its closed neighbourhood, and `h` vanishes off `V(G)`. -/
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

/-- **One attaining configuration over a main picture makes the general configuration attain**
(`lem:pencil-x0-one-witness`, `thm:pencil-x0-main-component`'s third claim): let `G` have a body. If
a configuration `(q₀, z₀)` with `q₀` a main picture and `z₀ ∈ L(q₀)` has row rank at least
`6(|V(G)| − 1) − def₃(G)`, the general configuration of `G` attains (`Graph.X0Attains`).

Admissibility is Zariski-open at `q₀` (`Graph.IsAdmissiblePicture.exists_mvPolynomial`). The heights
of the solutions of the lifting system `M(q)` form `L(q)` (`Graph.map_ker_liftingMatrix`), and over
an admissible picture the solutions form a space of dimension `dim L(q)`
(`Graph.finrank_ker_liftingMatrix`), which is least at the main picture `q₀`. So the polynomial
section of the kernel (`Matrix.exists_mvPolynomial_section_mulVec_eq_zero`,
`lem:pencil-polynomial-section`) gives heights `Z(q) ∈ L(q)` at the general picture, polynomial in
`q`, with `Z(q₀) = z₀`. As the hinges are nonzero
(`Graph.IsAdmissiblePicture.supportExtensor_ne_zero`),
`PanelHingeFramework.exists_rankPolynomial_of_le_finrank_linking`
(`lem:rank-polynomial-of-le-finrank`) gives a polynomial `Q` in the configuration points, nonzero at
`(q₀, z₀)`, at whose non-roots the rank is at least the target. Then `P` is the product of the
polynomial of admissibility, the determinant of the section and `Q` at `(q, Z(q))`, and `R` is `Q`
at `(q, ·)`. The rank never exceeds the target once every hinge is nonzero
(`BodyHingeFramework.finrank_span_rigidityRows_add_deficiency_le`,
`lem:relative-deficiency-rank-bound`). -/
theorem _root_.Graph.x0Attains_of_exists [Finite α] [Finite β] {G : Graph α β}
    (hV : V(G).Nonempty) (ends : β → α × α)
    (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2)
    {q₀ : α × Fin 2 → K} (hq₀ : G.IsMainPicture q₀) {z₀ : α → K} (hz₀ : z₀ ∈ G.liftingSpace q₀)
    (hrank : screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency 3 ≤
      (Module.finrank K (Submodule.span K
        (PanelHingeFramework.ofNormals (k := 2) G ends
          (fun p => pencilConfigPoint q₀ z₀ p.1 p.2)).toBodyHinge.rigidityRows) : ℤ)) :
    G.X0Attains K := by
  have : Fintype α := Fintype.ofFinite α
  -- The rank polynomial, nonzero at `(q₀, z₀)`.
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

/-- **Three points on a parabola at pairwise distinct parameters are not collinear** (a step of
`lem:pencil-x0-main-picture-open`): the `3 × 3` determinant of `(a, a², 1)`, `(b, b², 1)` and
`(c, c², 1)` is the Vandermonde product `(b − a)(a − c)(b − c)`, its columns permuted, which is
nonzero at pairwise distinct parameters. -/
private theorem det_moment_curve_triple (a b c : K) :
    (Matrix.of ![![a, a ^ 2, 1], ![b, b ^ 2, 1], ![c, c ^ 2, 1]] : Matrix (Fin 3) (Fin 3) K).det
      = (b - a) * (a - c) * (b - c) := by
  simp [Matrix.det_fin_three]
  ring

/-- **An admissible planar picture exists** (a step of `lem:pencil-x0-main-picture-open`, whose
proof names it): over an infinite field, when `G` is loopless and every closed neighbourhood has at
least three members, as at a graph that satisfies the standing hypotheses
(`def:pencil-x0-standing`). The parabola `w ↦ (φ w, φ w ^ 2)`, at an injective `φ : α → K` (an
enumeration of `α`, `Fin.valEmbedding` and `Infinite.natEmbedding K`), puts distinct bodies at
distinct points, and any three distinct members of a closed neighbourhood (a subset of three
members, `Set.exists_subset_card_eq` and `Set.ncard_eq_three`) at points that are not collinear
(`det_moment_curve_triple`, nonzero as `φ` is injective). -/
theorem _root_.Graph.exists_isAdmissiblePicture [Infinite K] [Finite α] {G : Graph α β}
    (hloop : G.Loopless) (h3 : ∀ v ∈ V(G), 3 ≤ (G.closedNbhd v).ncard) :
    ∃ q : α × Fin 2 → K, G.IsAdmissiblePicture q := by
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

/-- **A main picture exists** (`lem:pencil-x0-main-picture-open`): admissible pictures exist
(`Graph.exists_isAdmissiblePicture`), so the natural number `dim L(q)` attains its least value at
some admissible `q`, which is then a main picture. -/
theorem _root_.Graph.exists_isMainPicture [Infinite K] [Finite α] {G : Graph α β}
    (hloop : G.Loopless) (h3 : ∀ v ∈ V(G), 3 ≤ (G.closedNbhd v).ncard) :
    ∃ q : α × Fin 2 → K, G.IsMainPicture q := by
  obtain ⟨q₀, hq₀⟩ := G.exists_isAdmissiblePicture (K := K) hloop h3
  set S : Set ℕ := (fun q => Module.finrank K (G.liftingSpace q)) ''
    {q : α × Fin 2 → K | G.IsAdmissiblePicture q} with hSdef
  obtain ⟨q, hq, hqeq⟩ := Nat.sInf_mem (⟨_, q₀, hq₀, rfl⟩ : S.Nonempty)
  have hqeq' : Module.finrank K (G.liftingSpace q) = sInf S := hqeq
  refine ⟨q, hq, fun q' hq' => ?_⟩
  rw [hqeq']
  exact Nat.sInf_le ⟨q', hq', rfl⟩

/-! ## The main pictures are nonempty and Zariski-open -/

/-- **The main pictures around a main picture** (`lem:pencil-x0-main-picture-open`): at every main
picture `q₀`, some polynomial in the picture coordinates, nonzero at `q₀`, has only main pictures as
non-roots. Admissibility is open around `q₀` (`Graph.IsAdmissiblePicture.exists_mvPolynomial`, the
polynomial `Padm`), and the polynomial section of the kernel of the lifting system at `q₀` and its
zero solution (`Matrix.exists_mvPolynomial_section_mulVec_eq_zero`, `lem:pencil-polynomial-section`)
gives a polynomial `D`, nonzero at `q₀`, off whose zero set the kernel has dimension at most its
dimension at `q₀`. Off the zero set of `Padm * D`, `q` is admissible with `dim L(q) ≤ dim L(q₀)`
(`Graph.finrank_ker_liftingMatrix` at both), and as `dim L(q₀)` is least among admissible pictures,
`q` is a main picture. -/
theorem _root_.Graph.IsMainPicture.exists_mvPolynomial [Finite α] {G : Graph α β}
    {q₀ : α × Fin 2 → K} (hq₀ : G.IsMainPicture q₀) :
    ∃ P : MvPolynomial (α × Fin 2) K, MvPolynomial.eval q₀ P ≠ 0 ∧
      ∀ q : α × Fin 2 → K, MvPolynomial.eval q P ≠ 0 → G.IsMainPicture q := by
  have : Fintype α := Fintype.ofFinite α
  obtain ⟨Padm, hPadm₀, hPadm⟩ := hq₀.1.exists_mvPolynomial
  obtain ⟨D, Z, hD₀, -, hDrank, -⟩ :=
    Matrix.exists_mvPolynomial_section_mulVec_eq_zero (G.liftingMatrix K)
      (q₀ := q₀) (z₀ := (0 : α ⊕ (α × Fin 3) → K)) (Matrix.mulVec_zero _)
  refine ⟨Padm * D, by rw [map_mul]; exact mul_ne_zero hPadm₀ hD₀, fun q hq => ?_⟩
  rw [map_mul] at hq
  have hadm : G.IsAdmissiblePicture q := hPadm q (left_ne_zero_of_mul hq)
  have hle : Module.finrank K (G.liftingSpace q) ≤ Module.finrank K (G.liftingSpace q₀) := by
    have := hDrank q (right_ne_zero_of_mul hq)
    rwa [Graph.finrank_ker_liftingMatrix hadm, Graph.finrank_ker_liftingMatrix hq₀.1] at this
  exact ⟨hadm, fun q' hq' => hle.trans (hq₀.2 q' hq')⟩

/-- **The main pictures are nonempty and Zariski-open** (`lem:pencil-x0-main-picture-open`,
`thm:pencil-x0-main-component`'s first claim): some nonzero polynomial in the picture coordinates
has only main pictures as non-roots; `Graph.IsMainPicture.exists_mvPolynomial` at the main picture
of `Graph.exists_isMainPicture`. -/
theorem _root_.Graph.exists_mvPolynomial_isMainPicture [Infinite K] [Finite α] {G : Graph α β}
    (hloop : G.Loopless) (h3 : ∀ v ∈ V(G), 3 ≤ (G.closedNbhd v).ncard) :
    ∃ P : MvPolynomial (α × Fin 2) K, P ≠ 0 ∧
      ∀ q : α × Fin 2 → K, MvPolynomial.eval q P ≠ 0 → G.IsMainPicture q := by
  obtain ⟨q₀, hq₀⟩ := G.exists_isMainPicture (K := K) hloop h3
  obtain ⟨P, hP₀, hP⟩ := hq₀.exists_mvPolynomial
  exact ⟨P, fun h => hP₀ (by rw [h, map_zero]), hP⟩

end CombinatorialRigidity.Molecular
