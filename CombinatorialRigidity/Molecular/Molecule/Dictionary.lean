/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.ScrewVelocity
public import CombinatorialRigidity.SquareGraph
public import CombinatorialRigidity.Framework

/-!
# The square-graph dictionary (`thm:molecular-iff-square-bar-joint`)

Phase 25, leaf W4 (`notes/Phase25-design.md` §2.3). Katoh–Tanigawa 2011 (p. 650, p. 671) model a
molecule --- atoms as bodies, covalent bonds as hinges --- as a bar-joint framework on the square
graph `G²` exactly when it is a body-hinge framework of `G` whose hinges at each atom meet at the
atom's centre. This file builds the underlying **dictionary map** `Φ` between the two motion
spaces, at a placement `c : V → ℝ³` of the atom centres.

* The molecular framework `molecularOfCentres G' ends c` is the affine-hinge body-hinge framework
  (`BodyHingeFramework.ofHinge`) whose hinge at each edge `e = uv` is the line through the two
  endpoint centres --- its supporting `2`-extensor is `ĉ(u) ∨ ĉ(v)`, the join of the homogenized
  centres (`def:hinge-concurrent`).
* `Φ = molecularVel c` sends a screw assignment `S : V → ScrewSpace 2` to the joint velocity
  assignment `v ↦ vel_{S v}(c v)`, an `ℝ`-linear map into the bar-joint framework space of `G²`.

This slice delivers `Φ` and its **well-definedness**: `Φ` carries infinitesimal motions of the
molecular framework into `ker R(G², c)` (`molecularVel_mem_ker`). Every edge of `G²` lies inside a
closed neighbourhood `N[w]` (`lem:square-cliques`); on such an edge the two endpoint velocities
agree with those of body `w`'s single screw (the hinge constraint plus the line characterization
`lem:screw-velocity-line`, brick (2)), and body `w`'s screw is infinitesimally isometric
(brick (1)), so the bar-length derivative vanishes. Injectivity, surjectivity, and the resulting
`finrank` equality (the remainder of `thm:molecular-iff-square-bar-joint`) are follow-up slices.

See `notes/Phase25.md` and `notes/Phase25-design.md` §2.3, §3 (leaf W4) for the phase plan.
-/

@[expose] public section

open scoped Matrix InnerProductSpace
open WithLp SimpleGraph

namespace CombinatorialRigidity.Molecular

variable {V β : Type*}

/-! ## The molecular framework from a placement of centres (`def:hinge-concurrent`) -/

/-- **The molecular (hinge-concurrent) framework** on a multigraph `G` with endpoint selector
`ends` and a placement `c : V → ℝ³` of body centres (`def:hinge-concurrent`): the affine-hinge
body-hinge framework whose hinge at each edge `e` is the line through the two endpoint centres
`c (ends e).1`, `c (ends e).2`. Its supporting `2`-extensor is the join of the homogenized
endpoint centres, so every hinge incident to a body `v` passes through `c v` --- Katoh–Tanigawa's
hinge-concurrency (p. 671). When two centres coincide the join degenerates to zero (a welded
hinge). -/
noncomputable def molecularOfCentres (G : Graph V β) (ends : β → V × V)
    (c : V → EuclideanSpace ℝ (Fin 3)) : BodyHingeFramework 2 V β :=
  BodyHingeFramework.ofHinge G (fun e => ![ofLp (c (ends e).1), ofLp (c (ends e).2)])

@[simp] theorem molecularOfCentres_graph (G : Graph V β) (ends : β → V × V)
    (c : V → EuclideanSpace ℝ (Fin 3)) : (molecularOfCentres G ends c).graph = G := rfl

/-- The supporting extensor of a molecular framework's edge is the line extensor of the two
endpoint centres: `C(p(e)) = ĉ(ends e).1 ∨ ĉ(ends e).2`. -/
theorem molecularOfCentres_supportExtensor (G : Graph V β) (ends : β → V × V)
    (c : V → EuclideanSpace ℝ (Fin 3)) (e : β) :
    (molecularOfCentres G ends c).supportExtensor e
      = lineExtensor (ofLp (c (ends e).1)) (ofLp (c (ends e).2)) := by
  apply ScrewSpace.ext
  rw [molecularOfCentres, BodyHingeFramework.ofHinge_supportExtensor_val,
    affineSubspaceExtensor_apply, lineExtensor, ScrewSpace.val_mk]
  congr 1
  funext i
  fin_cases i <;> rfl

/-! ## The dictionary map `Φ = molecularVel` -/

/-- The **screw velocity as a linear map in the screw** (fixing the base point `x`):
`S ↦ vel_S(x) = ω_S ⨯₃ x + t_S`. Both graded coordinate maps are linear, so this is a genuine
linear map `ScrewSpace 2 →ₗ[ℝ] ℝ³`. -/
noncomputable def screwVelL (x : Fin 3 → ℝ) : ScrewSpace 2 →ₗ[ℝ] (Fin 3 → ℝ) :=
  crossProduct.flip x ∘ₗ screwOmega + screwTau

@[simp] theorem screwVelL_apply (x : Fin 3 → ℝ) (S : ScrewSpace 2) :
    screwVelL x S = screwVel S x := by
  simp only [screwVelL, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.flip_apply,
    screwVel_apply]

/-- **The dictionary map `Φ`** (`thm:molecular-iff-square-bar-joint`): sends a screw assignment
`S : V → ScrewSpace 2` (a molecular motion) to the joint-velocity assignment
`v ↦ vel_{S v}(c v)`, a bar-joint framework motion of `G²`. Linear in `S`. The codomain uses the
`EuclideanSpace ℝ (Fin 3)` view of `ℝ³`, so the velocity `vel_{S v}(c v) : Fin 3 → ℝ` is carried
across the `WithLp` boundary by `toLp`. -/
noncomputable def molecularVel (c : V → EuclideanSpace ℝ (Fin 3)) :
    (V → ScrewSpace 2) →ₗ[ℝ] (V → EuclideanSpace ℝ (Fin 3)) :=
  LinearMap.pi fun v =>
    (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toLinearMap ∘ₗ
      screwVelL (ofLp (c v)) ∘ₗ LinearMap.proj v

@[simp] theorem molecularVel_apply (c : V → EuclideanSpace ℝ (Fin 3)) (S : V → ScrewSpace 2)
    (v : V) : molecularVel c S v = toLp 2 (screwVel (S v) (ofLp (c v))) := by
  simp only [molecularVel, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    screwVelL_apply]
  rfl

theorem ofLp_molecularVel_apply (c : V → EuclideanSpace ℝ (Fin 3)) (S : V → ScrewSpace 2)
    (v : V) : ofLp (molecularVel c S v) = screwVel (S v) (ofLp (c v)) := by
  rw [molecularVel_apply, WithLp.ofLp_toLp]

/-! ## `Φ` lands in the bar-joint motions of `G²` (`molecularVel_mem_ker`)

The real inner product on `EuclideanSpace ℝ (Fin 3)` is the dot product of the underlying vectors,
which lets a bar-length-derivative equation `⟪c u − c v, Φ u − Φ v⟫ = 0` be discharged by the
cross-product identities of `ScrewVelocity.lean`. -/

/-- The real inner product on `EuclideanSpace ℝ (Fin 3)` is the dot product of the underlying
`Fin 3 → ℝ` vectors. -/
theorem euclidean_inner_eq_dotProduct (a b : EuclideanSpace ℝ (Fin 3)) :
    ⟪a, b⟫_ℝ = ofLp a ⬝ᵥ ofLp b := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm, star_trivial]

/-- **Endpoint velocity agreement.** For a screw `D` in the span of a molecular hinge's supporting
extensor `C(p(e))` and a link `e = uv`, the velocity field of `D` vanishes at both endpoint
centres `c u`, `c v`. (The hinge is the line through the endpoint centres, and `lem:screw-velocity-
line` says the rotation about it fixes both; the endpoint selector `ends` only orders that pair.)
-/
theorem screwVel_eq_zero_of_link {G : Graph V β} {ends : β → V × V}
    {c : V → EuclideanSpace ℝ (Fin 3)} {D : ScrewSpace 2} {e : β} {u v : V}
    (hcons : D ∈ Submodule.span ℝ {(molecularOfCentres G ends c).supportExtensor e})
    (hends : G.IsLink e (ends e).1 (ends e).2) (hlink : G.IsLink e u v) :
    screwVel D (ofLp (c u)) = 0 ∧ screwVel D (ofLp (c v)) = 0 := by
  rw [molecularOfCentres_supportExtensor] at hcons
  obtain ⟨h1, h2⟩ := screwVel_eq_zero_of_mem_span hcons
  rcases hlink.eq_and_eq_or_eq_and_eq hends with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · rw [hu, hv]; exact ⟨h1, h2⟩
  · rw [hu, hv]; exact ⟨h2, h1⟩

/-- **The dictionary map is well-defined** (`thm:molecular-iff-square-bar-joint`, forward
half): the joint-velocity assignment `Φ S` of any infinitesimal molecular motion `S` is a
bar-joint motion of the square graph `G²`, i.e. lies in `ker R(G², c)`.

`G'` is the multigraph carrier of `G` (`hshadow`: an edge exists between distinct `u, v` iff
`G.Adj u v`) with endpoint selector `ends` (`hends`). No minimum-degree or general-position
hypothesis is needed for well-definedness --- those enter for injectivity/surjectivity.

Every edge `xy` of `G²` lies inside a closed neighbourhood `N[w]` (`lem:square-cliques`); the
hinge constraints on the `G`-edges `wx`, `wy` make `vel_{S x}(c x) = vel_{S w}(c x)` and
`vel_{S y}(c y) = vel_{S w}(c y)` (endpoint agreement), so the bar-length derivative on `xy`
reduces to `⟪c x − c y, vel_{S w}(c x) − vel_{S w}(c y)⟫`, which vanishes because body `w`'s
velocity field is infinitesimally isometric (brick (1)). -/
theorem molecularVel_mem_ker {G : SimpleGraph V} {G' : Graph V β} {ends : β → V × V}
    {c : V → EuclideanSpace ℝ (Fin 3)}
    (hshadow : ∀ u v, u ≠ v → ((∃ e, G'.IsLink e u v) ↔ G.Adj u v))
    (hends : ∀ e u v, G'.IsLink e u v → G'.IsLink e (ends e).1 (ends e).2)
    {S : V → ScrewSpace 2}
    (hmem : S ∈ (molecularOfCentres G' ends c).infinitesimalMotions) :
    molecularVel c S ∈ LinearMap.ker (G.square.RigidityMap c) := by
  have hIM : (molecularOfCentres G' ends c).IsInfinitesimalMotion S := hmem
  rw [LinearMap.mem_ker]
  ext ⟨e, he⟩
  induction e with
  | h x y =>
    have hadj : G.square.Adj x y := he
    obtain ⟨w, hxw, hyw⟩ := G.exists_mem_closedNeighborSet_of_square_adj hadj
    rw [mem_closedNeighborSet] at hxw hyw
    -- On `z ∈ N[w]`, body `z`'s velocity at `c z` agrees with body `w`'s.
    have agree : ∀ z, (z = w ∨ G.Adj w z) →
        screwVel (S z) (ofLp (c z)) = screwVel (S w) (ofLp (c z)) := by
      rintro z (rfl | hadjz)
      · rfl
      · obtain ⟨e', hlink⟩ := (hshadow w z hadjz.ne).mpr hadjz
        have hcons : S w - S z ∈
            Submodule.span ℝ {(molecularOfCentres G' ends c).supportExtensor e'} :=
          hIM e' w z hlink
        obtain ⟨_, h2⟩ := screwVel_eq_zero_of_link hcons (hends e' w z hlink) hlink
        rw [screwVel_sub_screw, sub_eq_zero] at h2
        exact h2.symm
    change G.square.RigidityMap c (molecularVel c S) ⟨s(x, y), he⟩ = 0
    rw [rigidityMap_apply G.square c (molecularVel c S) x y he, euclidean_inner_eq_dotProduct,
      ofLp_sub, ofLp_sub, ofLp_molecularVel_apply, ofLp_molecularVel_apply, agree x hxw,
      agree y hyw]
    exact dotProduct_screwVel_sub (S w) (ofLp (c x)) (ofLp (c y))

end CombinatorialRigidity.Molecular
