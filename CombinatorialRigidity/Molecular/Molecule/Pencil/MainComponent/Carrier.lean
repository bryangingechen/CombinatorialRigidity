/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.Chart

/-!
# The main component: planar pictures, the lifting space, and `X₀` attaining (Phase 40b CARRIER)

The definitions the `X₀` argument rests on (`blueprint/src/chapter/main-component.tex`,
`sec:main-component-carrier`; Phase 40b CARRIER slice C1a, `notes/Phase40b.md`). A pencil
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
* `Graph.IsMainPicture` — `U`: admissible pictures whose lifting space has the least dimension
  among admissible pictures.
* `pencilConfigPoint` — the homogeneous configuration point `p_w = (x_w, y_w, z_w, 1) ∈ K⁴`.
* `pencilNormalOfPicture` — the plane normal at a body: `cross₃` of three selected configuration
  points, polynomial and denominator-free.
* `Graph.X0Attains` — "`X₀(G)`'s general point attains `6(|V| − 1) − def₃(G)`" ((MC-10)(a)): off
  one nonzero polynomial in the picture coordinates, the picture is admissible and the attaining
  heights contain a nonempty Zariski-open subset of `L(q)`.

## Design

* **Uncurried pictures** `q : α × Fin 2 → K`, the shape of `PanelHingeFramework.ofNormals`'s
  coordinate argument and of the rank polynomials' variable type.
* **The rank is taken at `ofNormals` of the configuration points, not of the plane normals.**
  `X0Attains` reads `PanelHingeFramework.ofNormals G ends (p_·)`: each body's *point* `p_v` is the
  normal of the polar plane `p_v^⊥`, and the hinge `panelSupportExtensor p_u p_v` is the polar of
  the pencil line `p_u ∧ p_v`, so its row rank is the rank of the point-join framework the pencil
  motives carry (the complement isomorphism is an invertible map of the screw space;
  `BodyHingeFramework.finrank_span_rigidityRows_mapSupport`, the conversion is CARRIER's C4). It is
  nonzero at every link as soon as the picture points differ. `ofNormals` at the *plane normals*
  would be the wrong rank: adjacent planes coincide on the whole fibre whenever the two bodies lie
  in a common planar-rigid subgraph ((MC-13)(c), e.g. every triangle edge at a generic picture,
  and every edge at a flat configuration), `panelSupportExtensor n n = 0` there, and a zero hinge
  welds its bodies (its hinge-row block is every functional).
* **Fibre-openness is part of `X0Attains`.** The generic motive intersects the attaining heights
  with the nondegenerate ones inside one fibre `L(q)` ((MC-133)(ii)), so `X0Attains` carries a
  nonempty Zariski-open set of attaining heights over each good picture, not one height; the
  semicontinuity is proved once, in the planned `Graph.x0Attains_of_exists` (slice C1b).
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
the one-witness upgrade (the planned `Graph.x0Attains_of_exists`) asks for its picture here. -/
def _root_.Graph.IsMainPicture (G : Graph α β) (q : α × Fin 2 → K) : Prop :=
  G.IsAdmissiblePicture q ∧ ∀ q' : α × Fin 2 → K, G.IsAdmissiblePicture q' →
    Module.finrank K (G.liftingSpace q) ≤ Module.finrank K (G.liftingSpace q')

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
distinct motive uses only one attaining `(q, z)`. -/
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

end CombinatorialRigidity.Molecular
