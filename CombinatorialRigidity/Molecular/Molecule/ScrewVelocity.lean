/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.RigidityMatrix.Basic
public import Mathlib.LinearAlgebra.CrossProduct

/-!
# Screw velocity fields (`sec:molecule-modelling-velocity`)

Phase 25, leaf W1 (`notes/Phase25-design.md` §2.3, §3). The square-graph dictionary
(`thm:molecular-iff-square-bar-joint`) compares screw assignments (one screw
`S ∈ ScrewSpace 2 = ⋀² ℝ⁴` per body) with joint velocities (one vector `x ∈ ℝ³` per atom
centre). The translation is the classical **velocity field** of a screw: writing `S` in graded
Plücker coordinates `(ω_S, t_S) ∈ ℝ³ × ℝ³` (the rotation part `ω_S`, pairing two affine
directions, and the translation part `t_S`, pairing a direction with the homogenizing
coordinate),
`vel_S(x) = ω_S ⨯₃ x + t_S`.

The two coordinate maps `screwOmega`, `screwTau : ScrewSpace 2 →ₗ[ℝ] (Fin 3 → ℝ)` are the two
graded pieces of the isomorphism `⋀² ℝ⁴ ≅ ⋀² ℝ³ ⊕ (ℝ³ ⊗ ℝ) ≅ ℝ³ × ℝ³`, built here as lifts of
two explicit alternating `2`-forms along `exteriorPower.alternatingMapLinearEquiv` and the
`ScrewSpace` boundary equivalence. On the line `2`-extensor `â ∨ b̂` of two homogenized points
they read off `ω = b − a` and `t = a ⨯₃ b` (`screwOmega_lineExtensor`,
`screwTau_lineExtensor`), so `vel_{â∨b̂}` is the rotation field about the line through `a` and
`b` (`screwVel_lineExtensor`).

## Main definitions

* `CombinatorialRigidity.Molecular.screwOmega`, `screwTau` — the rotation and translation
  coordinate maps of a screw.
* `CombinatorialRigidity.Molecular.screwVel` — the velocity field `vel_S(x) = ω_S ⨯₃ x + t_S`
  (`def:screw-velocity`).
* `CombinatorialRigidity.Molecular.lineExtensor` — the line `2`-extensor `â ∨ b̂` of two points
  (the supporting extensor of a molecular hinge, `def:hinge-concurrent`).

## Main results

* `screwVel_lineExtensor` — `vel_{â∨b̂}(x) = (b − a) ⨯₃ x + a ⨯₃ b`.
* `dotProduct_screwVel_sub` — every velocity field is infinitesimally isometric:
  `(x − y) ⬝ᵥ (vel_S x − vel_S y) = 0` (brick (1) of §2.3).
* `screwVel_eq_zero_iff_mem_span` — for distinct `a, b`: `vel_S a = 0 ∧ vel_S b = 0` iff `S` is
  a scalar multiple of `â ∨ b̂` (brick (2), `lem:screw-velocity-line`).
* `eq_zero_of_screwVel_eq_zero` — a screw whose velocity field vanishes at three non-collinear
  points is zero (brick (3), the kill half of `lem:screw-determination`).
* `exists_crossProduct_eq` — the two-edge cross-product system `ω ⨯₃ e₁ = d₁`, `ω ⨯₃ e₂ = d₂` is
  solvable under the triangle bar constraints (the linear-algebra core of brick (4)).
* `existsUnique_screwVel_eq` — brick (4), body determination: a non-collinear triple plus
  general-position side points pin a unique screw realizing a bar-constrained velocity assignment
  (`lem:screw-determination`). The triangle special case is `existsUnique_screwVel_eq_of_triangle`.

Brick (4)'s existence is proved by an explicit cross-product construction of the angular velocity
(design §2.3(4), flag F2 route two), not the bar-joint triangle-rank fact — everything stays inside
the `ℝ³` cross-product algebra of this file.
-/

@[expose] public section

open scoped Matrix
open exteriorPower

namespace CombinatorialRigidity.Molecular

/-! ## Cross-product bilinearity helpers -/

theorem crossProduct_sub_left (u w v : Fin 3 → ℝ) : (u - w) ⨯₃ v = u ⨯₃ v - w ⨯₃ v := by
  rw [map_sub, LinearMap.sub_apply]

theorem crossProduct_add_left (u w v : Fin 3 → ℝ) : (u + w) ⨯₃ v = u ⨯₃ v + w ⨯₃ v := by
  rw [map_add, LinearMap.add_apply]

theorem crossProduct_sub_right (u v w : Fin 3 → ℝ) : u ⨯₃ (v - w) = u ⨯₃ v - u ⨯₃ w :=
  map_sub _ _ _

theorem crossProduct_smul_left (c : ℝ) (u v : Fin 3 → ℝ) : (c • u) ⨯₃ v = c • (u ⨯₃ v) := by
  rw [map_smul, LinearMap.smul_apply]

/-! ## The coordinate maps and the velocity field

`ScrewSpace 2` is definitionally `⋀² ℝ⁴`. A linear map out of `⋀² ℝ⁴` is, by
`exteriorPower.alternatingMapLinearEquiv`, an alternating `2`-form on `ℝ⁴`. The two graded
Plücker coordinate maps are the lifts of the two alternating forms `omegaForm` and `tauForm`
below, precomposed with the boundary equivalence `ScrewSpace.equivExteriorPower`. -/

/-- **Spatial projection** `ℝ⁴ → ℝ³` onto the first three (affine) coordinates: `v ↦ v ∘ castSucc`.
The last coordinate is the homogenizing one. -/
def spatialProj : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) := LinearMap.funLeft ℝ ℝ Fin.castSucc

@[simp] theorem spatialProj_apply (v : Fin 4 → ℝ) (i : Fin 3) : spatialProj v i = v i.castSucc :=
  rfl

@[simp] theorem spatialProj_homogenize (a : Fin 3 → ℝ) : spatialProj (homogenize a) = a := by
  ext i; simp [spatialProj]

@[simp] theorem homogenize_three (a : Fin 3 → ℝ) : homogenize a 3 = 1 := by
  have h : (3 : Fin 4) = Fin.last 3 := rfl
  rw [h, homogenize_last]

/-- The **rotation part** as an alternating `2`-form on `ℝ⁴`: `ω(v, w) = v₃ • (w spatial) − w₃ •
(v spatial)`. On homogenized points `v = â, w = b̂` (last coordinate `1`) it reads `b − a`. -/
def omegaForm : (Fin 4 → ℝ) [⋀^Fin 2]→ₗ[ℝ] (Fin 3 → ℝ) where
  toFun v := (v 0 3) • spatialProj (v 1) - (v 1 3) • spatialProj (v 0)
  map_update_add' := by intro _ m i x y; fin_cases i <;> simp [Function.update, add_smul] <;> abel
  map_update_smul' := by
    intro _ m i c x; fin_cases i <;> simp [Function.update, smul_sub, smul_smul, mul_comm]
  map_eq_zero_of_eq' v i j hij hne := by fin_cases i <;> fin_cases j <;> simp_all

/-- The **translation part** as an alternating `2`-form on `ℝ⁴`: `t(v, w) = (v spatial) ⨯₃ (w
spatial)`. On homogenized points `v = â, w = b̂` it reads `a ⨯₃ b`. -/
def tauForm : (Fin 4 → ℝ) [⋀^Fin 2]→ₗ[ℝ] (Fin 3 → ℝ) where
  toFun v := crossProduct (spatialProj (v 0)) (spatialProj (v 1))
  map_update_add' := by intro _ m i x y; fin_cases i <;> simp [Function.update]
  map_update_smul' := by intro _ m i c x; fin_cases i <;> simp [Function.update]
  map_eq_zero_of_eq' v i j hij hne := by fin_cases i <;> fin_cases j <;> simp_all

/-- **The rotation coordinate `ω_S` of a screw** (`def:screw-velocity`): the lift of the
alternating form `omegaForm` along the screw-space boundary equivalence. -/
noncomputable def screwOmega : ScrewSpace 2 →ₗ[ℝ] (Fin 3 → ℝ) :=
  (alternatingMapLinearEquiv omegaForm) ∘ₗ (ScrewSpace.equivExteriorPower 2).toLinearMap

/-- **The translation coordinate `t_S` of a screw** (`def:screw-velocity`): the lift of the
alternating form `tauForm` along the screw-space boundary equivalence. -/
noncomputable def screwTau : ScrewSpace 2 →ₗ[ℝ] (Fin 3 → ℝ) :=
  (alternatingMapLinearEquiv tauForm) ∘ₗ (ScrewSpace.equivExteriorPower 2).toLinearMap

/-- **The velocity field of a screw** (`def:screw-velocity`): `vel_S(x) = ω_S ⨯₃ x + t_S`, the
classical instantaneous velocity of the rigid motion `S` at the point `x ∈ ℝ³`. Linear in `S`
(both coordinate maps are). -/
noncomputable def screwVel (S : ScrewSpace 2) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  crossProduct (screwOmega S) x + screwTau S

theorem screwVel_apply (S : ScrewSpace 2) (x : Fin 3 → ℝ) :
    screwVel S x = screwOmega S ⨯₃ x + screwTau S := rfl

/-- The velocity field is linear in the screw: `vel_{c•S}(x) = c • vel_S(x)`. -/
theorem screwVel_smul (c : ℝ) (S : ScrewSpace 2) (x : Fin 3 → ℝ) :
    screwVel (c • S) x = c • screwVel S x := by
  simp only [screwVel_apply, map_smul, smul_add, LinearMap.smul_apply]

/-- The velocity field is additive in the screw, difference form: `vel_{S − S'}(x) = vel_S(x) −
vel_{S'}(x)`. Used for the uniqueness half of `lem:screw-determination`. -/
theorem screwVel_sub_screw (S S' : ScrewSpace 2) (x : Fin 3 → ℝ) :
    screwVel (S - S') x = screwVel S x - screwVel S' x := by
  rw [screwVel_apply, screwVel_apply, screwVel_apply, map_sub, crossProduct_sub_left, map_sub]
  abel

/-! ## The line `2`-extensor and the extensor formulas -/

/-- **The line `2`-extensor `â ∨ b̂`** of two points `a, b ∈ ℝ³`: the join of the homogenized
points, i.e. the supporting `2`-extensor of the molecular hinge through `a` and `b`
(`def:hinge-concurrent`). -/
noncomputable def lineExtensor (a b : Fin 3 → ℝ) : ScrewSpace 2 :=
  ScrewSpace.mk (extensor ![homogenize a, homogenize b]) (extensor_mem_exteriorPower _)

/-- The bridge lemma: `equivExteriorPower` carries a `mk`-extensor to the exterior-power `ιMulti`.
Both are the same underlying element `ExteriorAlgebra.ιMulti ℝ 2 v` of the graded piece. -/
theorem equivExteriorPower_mk_extensor (v : Fin 2 → Fin 4 → ℝ) :
    ScrewSpace.equivExteriorPower 2 (ScrewSpace.mk (extensor v) (extensor_mem_exteriorPower v))
      = ιMulti ℝ 2 v := by
  apply Subtype.ext
  simp only [ScrewSpace.mk, ScrewSpace_def]
  rfl

@[simp] theorem screwOmega_lineExtensor (a b : Fin 3 → ℝ) :
    screwOmega (lineExtensor a b) = b - a := by
  rw [screwOmega, lineExtensor, LinearMap.comp_apply, LinearEquiv.coe_coe,
    equivExteriorPower_mk_extensor, alternatingMapLinearEquiv_apply_ιMulti]
  change (homogenize a 3) • spatialProj (homogenize b)
    - (homogenize b 3) • spatialProj (homogenize a) = b - a
  simp

@[simp] theorem screwTau_lineExtensor (a b : Fin 3 → ℝ) :
    screwTau (lineExtensor a b) = a ⨯₃ b := by
  rw [screwTau, lineExtensor, LinearMap.comp_apply, LinearEquiv.coe_coe,
    equivExteriorPower_mk_extensor, alternatingMapLinearEquiv_apply_ιMulti]
  change crossProduct (spatialProj (homogenize a)) (spatialProj (homogenize b)) = a ⨯₃ b
  simp

/-- **The velocity field of a line extensor** is the rotation field about the line through `a` and
`b`: `vel_{â∨b̂}(x) = (b − a) ⨯₃ x + a ⨯₃ b` (`def:screw-velocity`). -/
theorem screwVel_lineExtensor (a b x : Fin 3 → ℝ) :
    screwVel (lineExtensor a b) x = (b - a) ⨯₃ x + a ⨯₃ b := by
  rw [screwVel_apply, screwOmega_lineExtensor, screwTau_lineExtensor]

/-- The line extensor's velocity field vanishes at each defining point (`def:hinge-concurrent`:
the hinge through `a` and `b` is fixed by the rotation about it). -/
@[simp] theorem screwVel_lineExtensor_left (a b : Fin 3 → ℝ) :
    screwVel (lineExtensor a b) a = 0 := by
  rw [screwVel_lineExtensor, crossProduct_sub_left, cross_self, sub_zero, ← cross_anticomm]
  abel

@[simp] theorem screwVel_lineExtensor_right (a b : Fin 3 → ℝ) :
    screwVel (lineExtensor a b) b = 0 := by
  rw [screwVel_lineExtensor, crossProduct_sub_left, cross_self, zero_sub, ← cross_anticomm]
  abel

/-! ## Brick (1): velocity fields are infinitesimally isometric -/

/-- The velocity **difference** is the rotation acting on the point difference:
`vel_S x − vel_S y = ω_S ⨯₃ (x − y)`. -/
theorem screwVel_sub (S : ScrewSpace 2) (x y : Fin 3 → ℝ) :
    screwVel S x - screwVel S y = screwOmega S ⨯₃ (x - y) := by
  simp only [screwVel_apply, map_sub]
  abel

/-- **Brick (1) (skew): every velocity field is infinitesimally isometric**
(`lem:screw-velocity-line`): `(x − y) ⬝ᵥ (vel_S x − vel_S y) = 0`, because the velocity
difference is a cross product with `x − y`. -/
theorem dotProduct_screwVel_sub (S : ScrewSpace 2) (x y : Fin 3 → ℝ) :
    (x - y) ⬝ᵥ (screwVel S x - screwVel S y) = 0 := by
  rw [screwVel_sub]; exact dot_cross_self (screwOmega S) (x - y)

/-! ## Injectivity of the coordinate pair `(ω, t)`

`ScrewSpace 2` and `ℝ³ × ℝ³` are both `6`-dimensional, and the coordinate pair
`screwCoord = (screwOmega, screwTau)` is a linear isomorphism. We prove injectivity via an
explicit right inverse `rebuild` (surjectivity) plus rank–nullity. This is the fact that lets a
screw be recovered from its rotation and translation parts, on which bricks (2) and (3) rest. -/

/-- The combined coordinate map `S ↦ (ω_S, t_S)`. -/
noncomputable def screwCoord : ScrewSpace 2 →ₗ[ℝ] (Fin 3 → ℝ) × (Fin 3 → ℝ) :=
  screwOmega.prod screwTau

/-- The `i`-th standard basis vector of `ℝ⁴`. -/
def stdVec (i : Fin 4) : Fin 4 → ℝ := Pi.single i 1

/-- The standard basis `2`-extensor `e_i ∧ e_j` of `⋀² ℝ⁴`. -/
noncomputable def stdBiv (i j : Fin 4) : ScrewSpace 2 :=
  ScrewSpace.mk (extensor ![stdVec i, stdVec j]) (extensor_mem_exteriorPower _)

theorem screwOmega_stdBiv (i j : Fin 4) :
    screwOmega (stdBiv i j)
      = stdVec i 3 • spatialProj (stdVec j) - stdVec j 3 • spatialProj (stdVec i) := by
  rw [screwOmega, stdBiv, LinearMap.comp_apply, LinearEquiv.coe_coe,
    equivExteriorPower_mk_extensor, alternatingMapLinearEquiv_apply_ιMulti]
  rfl

theorem screwTau_stdBiv (i j : Fin 4) :
    screwTau (stdBiv i j) = spatialProj (stdVec i) ⨯₃ spatialProj (stdVec j) := by
  rw [screwTau, stdBiv, LinearMap.comp_apply, LinearEquiv.coe_coe,
    equivExteriorPower_mk_extensor, alternatingMapLinearEquiv_apply_ιMulti]
  rfl

/-- An explicit preimage of `(ω, t)` under the coordinate map, spreading the six coordinates back
onto the standard basis bivectors. -/
noncomputable def rebuild (p : (Fin 3 → ℝ) × (Fin 3 → ℝ)) : ScrewSpace 2 :=
  -(p.1 0) • stdBiv 0 3 - (p.1 1) • stdBiv 1 3 - (p.1 2) • stdBiv 2 3
    + (p.2 0) • stdBiv 1 2 - (p.2 1) • stdBiv 0 2 + (p.2 2) • stdBiv 0 1

theorem screwCoord_rebuild (p : (Fin 3 → ℝ) × (Fin 3 → ℝ)) : screwCoord (rebuild p) = p := by
  apply Prod.ext
  · change screwOmega (rebuild p) = p.1
    simp only [rebuild, map_add, map_sub, map_smul, screwOmega_stdBiv]
    ext k; fin_cases k <;> simp [stdVec]
  · change screwTau (rebuild p) = p.2
    simp only [rebuild, map_add, map_sub, map_smul, screwTau_stdBiv]
    ext k; fin_cases k <;> simp [stdVec, cross_apply]

@[simp] theorem screwOmega_rebuild (p : (Fin 3 → ℝ) × (Fin 3 → ℝ)) :
    screwOmega (rebuild p) = p.1 := by
  have h := screwCoord_rebuild p
  rw [screwCoord, LinearMap.prod_apply] at h
  exact congrArg Prod.fst h

@[simp] theorem screwTau_rebuild (p : (Fin 3 → ℝ) × (Fin 3 → ℝ)) :
    screwTau (rebuild p) = p.2 := by
  have h := screwCoord_rebuild p
  rw [screwCoord, LinearMap.prod_apply] at h
  exact congrArg Prod.snd h

theorem screwCoord_surjective : Function.Surjective screwCoord :=
  Function.RightInverse.surjective screwCoord_rebuild

theorem screwCoord_injective : Function.Injective screwCoord := by
  rw [← LinearMap.ker_eq_bot]
  have hrn := LinearMap.finrank_range_add_finrank_ker screwCoord
  have hrange : Module.finrank ℝ (LinearMap.range screwCoord)
      = Module.finrank ℝ ((Fin 3 → ℝ) × (Fin 3 → ℝ)) := by
    rw [LinearMap.range_eq_top.mpr screwCoord_surjective, finrank_top]
  have hdom : Module.finrank ℝ (ScrewSpace 2) = 6 := by
    rw [screwSpace_finrank]; rfl
  have hcod : Module.finrank ℝ ((Fin 3 → ℝ) × (Fin 3 → ℝ)) = 6 := by
    rw [Module.finrank_prod, Module.finrank_pi]; rfl
  have hker : Module.finrank ℝ (LinearMap.ker screwCoord) = 0 := by
    rw [hrange, hcod, hdom] at hrn; omega
  exact Submodule.finrank_eq_zero.mp hker

/-- The kernel form of injectivity: a screw with vanishing rotation and translation parts is zero.
-/
theorem eq_zero_of_screwOmega_eq_zero_of_screwTau_eq_zero {S : ScrewSpace 2}
    (hω : screwOmega S = 0) (hτ : screwTau S = 0) : S = 0 := by
  apply screwCoord_injective
  rw [map_zero]
  exact Prod.ext hω hτ

/-! ## Collinearity from vanishing cross products -/

/-- If `ω ⨯₃ u = 0` and `u ≠ 0`, then `ω` is a scalar multiple of `u` (both are collinear). -/
theorem exists_smul_of_crossProduct_eq_zero {ω u : Fin 3 → ℝ} (hu : u ≠ 0) (h : ω ⨯₃ u = 0) :
    ∃ c : ℝ, ω = c • u := by
  have hdep : ¬ LinearIndependent ℝ ![u, ω] := by
    rw [← crossProduct_ne_zero_iff_linearIndependent, not_not, ← cross_anticomm, h, neg_zero]
  rw [LinearIndependent.pair_iff' hu] at hdep
  simp only [not_forall, ne_eq, not_not] at hdep
  obtain ⟨c, hc⟩ := hdep
  exact ⟨c, hc.symm⟩

/-- If `ω ⨯₃ u = 0` and `ω ⨯₃ w = 0` with `u, w` linearly independent, then `ω = 0`. -/
theorem eq_zero_of_crossProduct_eq_zero_of_linearIndependent {ω u w : Fin 3 → ℝ}
    (hind : LinearIndependent ℝ ![u, w]) (h1 : ω ⨯₃ u = 0) (h2 : ω ⨯₃ w = 0) : ω = 0 := by
  by_contra hω
  have hu : ¬ LinearIndependent ℝ ![ω, u] := by
    rw [← crossProduct_ne_zero_iff_linearIndependent, not_not, h1]
  have hw : ¬ LinearIndependent ℝ ![ω, w] := by
    rw [← crossProduct_ne_zero_iff_linearIndependent, not_not, h2]
  rw [LinearIndependent.pair_iff' hω] at hu hw
  simp only [not_forall, ne_eq, not_not] at hu hw
  obtain ⟨a, ha⟩ := hu
  obtain ⟨b, hb⟩ := hw
  -- `u = a • ω`, `w = b • ω`, so `![u, w]` is dependent.
  have hrel : b • u + (-a) • w = 0 := by rw [← ha, ← hb]; module
  obtain ⟨_, ha0⟩ := LinearIndependent.pair_iff.mp hind b (-a) hrel
  have hu0 : u = 0 := by rw [← ha, neg_eq_zero.mp ha0, zero_smul]
  exact hind.ne_zero 0 hu0

/-! ## Brick (2): the line characterization -/

/-- **Brick (2): lines through two points, velocity form** (`lem:screw-velocity-line`): for
distinct `a, b ∈ ℝ³` and any screw `S`, the velocity field vanishes at both `a` and `b` iff `S`
is a scalar multiple of the line extensor `â ∨ b̂`. -/
theorem screwVel_eq_zero_iff_mem_span {a b : Fin 3 → ℝ} (hab : a ≠ b) (S : ScrewSpace 2) :
    (screwVel S a = 0 ∧ screwVel S b = 0) ↔ S ∈ Submodule.span ℝ {lineExtensor a b} := by
  have hu : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  constructor
  · rintro ⟨hva, hvb⟩
    -- `ω ⨯₃ (b − a) = 0`, so `ω = c • (b − a)`.
    have hcross : screwOmega S ⨯₃ (b - a) = 0 := by
      have h := screwVel_sub S b a
      rw [hvb, hva, sub_zero] at h
      exact h.symm
    obtain ⟨c, hc⟩ := exists_smul_of_crossProduct_eq_zero hu hcross
    refine Submodule.mem_span_singleton.mpr ⟨c, screwCoord_injective (Prod.ext ?_ ?_)⟩
    · change screwOmega (c • lineExtensor a b) = screwOmega S
      rw [map_smul, screwOmega_lineExtensor, ← hc]
    · change screwTau (c • lineExtensor a b) = screwTau S
      rw [map_smul, screwTau_lineExtensor]
      -- `t_S = a ⨯₃ b` scaled by `c`, from `vel_S a = 0`.
      have hadd : screwOmega S ⨯₃ a + screwTau S = 0 := by rw [← screwVel_apply]; exact hva
      rw [eq_neg_of_add_eq_zero_right hadd, hc, crossProduct_smul_left, crossProduct_sub_left,
        cross_self, sub_zero, ← cross_anticomm]
      module
  · intro hmem
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hmem
    refine ⟨?_, ?_⟩ <;> simp [screwVel_smul]

/-! ## Brick (3): a screw is determined by point velocities (kill half) -/

/-- **Brick (3) (kill): a screw whose velocity field vanishes at three non-collinear points is
zero** (`lem:screw-determination`, the vanishing half). Non-collinearity is phrased as linear
independence of the two edge vectors `q₁ − q₀`, `q₂ − q₀`. -/
theorem eq_zero_of_screwVel_eq_zero {S : ScrewSpace 2} {q : Fin 3 → Fin 3 → ℝ}
    (hind : LinearIndependent ℝ ![q 1 - q 0, q 2 - q 0])
    (h : ∀ i, screwVel S (q i) = 0) : S = 0 := by
  have hc1 : screwOmega S ⨯₃ (q 1 - q 0) = 0 := by
    have h10 := screwVel_sub S (q 1) (q 0)
    rw [h 1, h 0, sub_zero] at h10; exact h10.symm
  have hc2 : screwOmega S ⨯₃ (q 2 - q 0) = 0 := by
    have h20 := screwVel_sub S (q 2) (q 0)
    rw [h 2, h 0, sub_zero] at h20; exact h20.symm
  have hω : screwOmega S = 0 :=
    eq_zero_of_crossProduct_eq_zero_of_linearIndependent hind hc1 hc2
  have hτ : screwTau S = 0 := by
    have h0 := screwVel_apply S (q 0)
    rw [h 0, hω] at h0
    simpa using h0.symm
  exact eq_zero_of_screwOmega_eq_zero_of_screwTau_eq_zero hω hτ

/-! ## Nondegeneracy in `ℝ³`

Two linear-algebra facts underpinning brick (4). First, three vectors that are pairwise
independent enough — the two edge vectors of a non-collinear triangle together with their
cross product — form a basis of `ℝ³`; second, a vector orthogonal to a basis is zero. Both
route through `Matrix.det ≠ 0` (via `triple_product_eq_det`) and the invertible-matrix kernel
lemma `Matrix.eq_zero_of_mulVec_eq_zero`. -/

/-- For linearly independent `e₁, e₂ ∈ ℝ³`, the triple `![e₁, e₂, e₁ ⨯₃ e₂]` is a basis of `ℝ³`
(the cross product completes two independent vectors to a frame). -/
theorem linearIndependent_e1_e2_cross {e₁ e₂ : Fin 3 → ℝ}
    (hind : LinearIndependent ℝ ![e₁, e₂]) :
    LinearIndependent ℝ ![e₁, e₂, e₁ ⨯₃ e₂] := by
  have hn : e₁ ⨯₃ e₂ ≠ 0 := crossProduct_ne_zero_iff_linearIndependent.mpr hind
  have hdet : Matrix.det ![e₁, e₂, e₁ ⨯₃ e₂] ≠ 0 := by
    have hdet_eq : Matrix.det ![e₁, e₂, e₁ ⨯₃ e₂] = (e₁ ⨯₃ e₂) ⬝ᵥ (e₁ ⨯₃ e₂) := by
      rw [← triple_product_eq_det e₁ e₂ (e₁ ⨯₃ e₂)]
      exact (triple_product_permutation (e₁ ⨯₃ e₂) e₁ e₂).symm
    rw [hdet_eq]
    exact fun h => hn (dotProduct_self_eq_zero.mp h)
  exact Matrix.linearIndependent_rows_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))

/-- A vector orthogonal to a basis of `ℝ³` is zero: if `![v₀, v₁, v₂]` is linearly independent
and each `vᵢ` is orthogonal to `r`, then `r = 0`. -/
theorem eq_zero_of_dotProduct_row_eq_zero {v : Fin 3 → Fin 3 → ℝ} {r : Fin 3 → ℝ}
    (hv : LinearIndependent ℝ v) (h : ∀ i, v i ⬝ᵥ r = 0) : r = 0 := by
  have hdet : Matrix.det v ≠ 0 :=
    isUnit_iff_ne_zero.mp
      ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hv))
  refine Matrix.eq_zero_of_mulVec_eq_zero hdet (funext fun i => ?_)
  exact h i

/-! ## Solving the two-edge cross-product system

The heart of brick (4): given the two edge vectors `e₁, e₂` of a non-collinear triangle and
target velocity differences `d₁, d₂` obeying the three bar constraints (`e₁ ⟂ d₁`, `e₂ ⟂ d₂`,
`e₁·d₂ + e₂·d₁ = 0`), there is an angular velocity `ω` with `ω ⨯₃ e₁ = d₁` and `ω ⨯₃ e₂ = d₂`.
Solve `ω ⨯₃ e₁ = d₁` first — `ω₀ = (e₁·e₁)⁻¹ (e₁ ⨯₃ d₁)` works by the vector triple product — then
correct along `e₁` (which the first equation ignores) by the multiple of `e₁` making the second
equation hold; the third bar constraint is exactly what makes the correction a multiple of
`e₁ ⨯₃ e₂`. -/

/-- **The two-edge cross-product system is solvable** under the triangle bar constraints. This is
the linear-algebra core of the existence half of `lem:screw-determination`. -/
theorem exists_crossProduct_eq {e₁ e₂ d₁ d₂ : Fin 3 → ℝ}
    (hind : LinearIndependent ℝ ![e₁, e₂])
    (h1 : e₁ ⬝ᵥ d₁ = 0) (h2 : e₂ ⬝ᵥ d₂ = 0) (h3 : e₁ ⬝ᵥ d₂ + e₂ ⬝ᵥ d₁ = 0) :
    ∃ ω : Fin 3 → ℝ, ω ⨯₃ e₁ = d₁ ∧ ω ⨯₃ e₂ = d₂ := by
  have he1 : e₁ ≠ 0 := by simpa using hind.ne_zero 0
  have hE1 : e₁ ⬝ᵥ e₁ ≠ 0 := fun h => he1 (dotProduct_self_eq_zero.mp h)
  have hn : e₁ ⨯₃ e₂ ≠ 0 := crossProduct_ne_zero_iff_linearIndependent.mpr hind
  have hN : (e₁ ⨯₃ e₂) ⬝ᵥ (e₁ ⨯₃ e₂) ≠ 0 := fun h => hn (dotProduct_self_eq_zero.mp h)
  have hd1e1 : d₁ ⬝ᵥ e₁ = 0 := by rw [dotProduct_comm]; exact h1
  set ω₀ := (e₁ ⬝ᵥ e₁)⁻¹ • (e₁ ⨯₃ d₁) with hω₀_def
  -- `ω₀` already solves the first equation.
  have hω₀e₁ : ω₀ ⨯₃ e₁ = d₁ := by
    rw [hω₀_def, crossProduct_smul_left, cross_cross_eq_smul_sub_smul, hd1e1, zero_smul, sub_zero,
      inv_smul_smul₀ hE1]
  -- `ω₀ · (e₁ ⨯₃ e₂) = d₁ · e₂` (used to verify the correction is along the cross product).
  have hω₀n : ω₀ ⬝ᵥ (e₁ ⨯₃ e₂) = d₁ ⬝ᵥ e₂ := by
    rw [hω₀_def, smul_dotProduct, cross_dot_cross, hd1e1, mul_zero, sub_zero, smul_eq_mul,
      ← mul_assoc, inv_mul_cancel₀ hE1, one_mul]
  set u := d₂ - ω₀ ⨯₃ e₂ with hu_def
  set s := (u ⬝ᵥ (e₁ ⨯₃ e₂)) * ((e₁ ⨯₃ e₂) ⬝ᵥ (e₁ ⨯₃ e₂))⁻¹ with hs_def
  -- `u = d₂ − ω₀ ⨯₃ e₂` is orthogonal to `e₁` and `e₂`, hence a multiple of `e₁ ⨯₃ e₂`.
  have hue1 : u ⬝ᵥ e₁ = 0 := by
    have hcross : (ω₀ ⨯₃ e₂) ⬝ᵥ e₁ = -(d₁ ⬝ᵥ e₂) := by
      rw [dotProduct_comm, triple_product_permutation, ← cross_anticomm,
        dotProduct_neg, hω₀n]
    rw [hu_def, sub_dotProduct, hcross, sub_neg_eq_add, dotProduct_comm d₂ e₁,
      dotProduct_comm d₁ e₂]
    exact h3
  have hue2 : u ⬝ᵥ e₂ = 0 := by
    have hcross : (ω₀ ⨯₃ e₂) ⬝ᵥ e₂ = 0 := by rw [dotProduct_comm]; exact dot_cross_self ω₀ e₂
    rw [hu_def, sub_dotProduct, hcross, sub_zero, dotProduct_comm]; exact h2
  have husn : u = s • (e₁ ⨯₃ e₂) := by
    have hd0 : e₁ ⬝ᵥ (u - s • (e₁ ⨯₃ e₂)) = 0 := by
      rw [dotProduct_sub, dotProduct_comm e₁ u, hue1, dotProduct_smul, dot_self_cross,
        smul_zero, sub_zero]
    have hd1 : e₂ ⬝ᵥ (u - s • (e₁ ⨯₃ e₂)) = 0 := by
      rw [dotProduct_sub, dotProduct_comm e₂ u, hue2, dotProduct_smul, dot_cross_self,
        smul_zero, sub_zero]
    have hd2 : (e₁ ⨯₃ e₂) ⬝ᵥ (u - s • (e₁ ⨯₃ e₂)) = 0 := by
      rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, hs_def, dotProduct_comm (e₁ ⨯₃ e₂) u,
        mul_assoc, inv_mul_cancel₀ hN, mul_one, sub_self]
    have hr : u - s • (e₁ ⨯₃ e₂) = 0 :=
      eq_zero_of_dotProduct_row_eq_zero (linearIndependent_e1_e2_cross hind) (fun k => by
        fin_cases k
        · exact hd0
        · exact hd1
        · exact hd2)
    exact sub_eq_zero.mp hr
  refine ⟨ω₀ + s • e₁, ?_, ?_⟩
  · rw [crossProduct_add_left, hω₀e₁, crossProduct_smul_left s e₁ e₁, cross_self, smul_zero,
      add_zero]
  · rw [crossProduct_add_left, crossProduct_smul_left s e₁ e₂, ← husn, hu_def]; abel

/-! ## Brick (4): a screw is determined by point velocities (existence half)

The `∃!`-body-determination half of `lem:screw-determination`. A non-collinear triple pins a
unique screw realizing a bar-constrained velocity assignment on it
(`existsUnique_screwVel_eq_of_triangle`); adding further points, each in general position with the
triple (affine independence up to order four), forces those velocities too, giving the family form
`existsUnique_screwVel_eq`. -/

/-- **Existence on a non-collinear triangle**: a velocity assignment obeying the three bar
constraints of a non-collinear triangle is realized by some screw. -/
theorem exists_screwVel_eq {q x : Fin 3 → Fin 3 → ℝ}
    (hind : LinearIndependent ℝ ![q 1 - q 0, q 2 - q 0])
    (hbar : ∀ i j, (q i - q j) ⬝ᵥ (x i - x j) = 0) :
    ∃ S : ScrewSpace 2, ∀ i, screwVel S (q i) = x i := by
  have h3 : (q 1 - q 0) ⬝ᵥ (x 2 - x 0) + (q 2 - q 0) ⬝ᵥ (x 1 - x 0) = 0 := by
    have h10 := hbar 1 0
    have h20 := hbar 2 0
    have h21 := hbar 2 1
    simp only [sub_dotProduct, dotProduct_sub] at h10 h20 h21 ⊢
    linarith
  obtain ⟨ω, hω1, hω2⟩ := exists_crossProduct_eq hind (hbar 1 0) (hbar 2 0) h3
  refine ⟨rebuild (ω, x 0 - ω ⨯₃ q 0), fun i => ?_⟩
  rw [screwVel_apply, screwOmega_rebuild, screwTau_rebuild]
  fin_cases i
  · change ω ⨯₃ q 0 + (x 0 - ω ⨯₃ q 0) = x 0; abel
  · change ω ⨯₃ q 1 + (x 0 - ω ⨯₃ q 0) = x 1
    have h : ω ⨯₃ q 1 - ω ⨯₃ q 0 = x 1 - x 0 := by rw [← crossProduct_sub_right]; exact hω1
    rw [show ω ⨯₃ q 1 + (x 0 - ω ⨯₃ q 0) = (ω ⨯₃ q 1 - ω ⨯₃ q 0) + x 0 by abel, h]; abel
  · change ω ⨯₃ q 2 + (x 0 - ω ⨯₃ q 0) = x 2
    have h : ω ⨯₃ q 2 - ω ⨯₃ q 0 = x 2 - x 0 := by rw [← crossProduct_sub_right]; exact hω2
    rw [show ω ⨯₃ q 2 + (x 0 - ω ⨯₃ q 0) = (ω ⨯₃ q 2 - ω ⨯₃ q 0) + x 0 by abel, h]; abel

/-- **A unique screw realizes a bar-constrained velocity assignment on a non-collinear triangle**
(`lem:screw-determination`, triangle form). Uniqueness is `eq_zero_of_screwVel_eq_zero`
(via `screwCoord_injective`); existence is `exists_screwVel_eq`. -/
theorem existsUnique_screwVel_eq_of_triangle {q x : Fin 3 → Fin 3 → ℝ}
    (hind : LinearIndependent ℝ ![q 1 - q 0, q 2 - q 0])
    (hbar : ∀ i j, (q i - q j) ⬝ᵥ (x i - x j) = 0) :
    ∃! S : ScrewSpace 2, ∀ i, screwVel S (q i) = x i := by
  obtain ⟨S, hS⟩ := exists_screwVel_eq hind hbar
  refine ⟨S, hS, fun S' hS' => ?_⟩
  have hzero : ∀ i, screwVel (S' - S) (q i) = 0 := fun i => by
    rw [screwVel_sub_screw, hS', hS, sub_self]
  have := eq_zero_of_screwVel_eq_zero hind hzero
  rwa [sub_eq_zero] at this

/-- **Brick (4): a screw is determined by point velocities** (`lem:screw-determination`). If a
point family `p` (indexed by any type) contains a non-collinear triple `p i₀, p i₁, p i₂`, every
other point is affinely independent from that triple (general position up to order four), and a
velocity assignment `x` satisfies the bar constraint on every pair, then a unique screw `S`
realizes it: `vel_S(p i) = x i` for all `i`. Uniqueness reduces to the triangle; existence solves
on the triangle and pins each further point by orthogonality to three independent directions. -/
theorem existsUnique_screwVel_eq {ι : Type*} {p x : ι → Fin 3 → ℝ} {i₀ i₁ i₂ : ι}
    (htri : LinearIndependent ℝ ![p i₁ - p i₀, p i₂ - p i₀])
    (hgp : ∀ j, j ≠ i₀ → j ≠ i₁ → j ≠ i₂ →
      LinearIndependent ℝ ![p i₀ - p j, p i₁ - p j, p i₂ - p j])
    (hbar : ∀ i j, (p i - p j) ⬝ᵥ (x i - x j) = 0) :
    ∃! S : ScrewSpace 2, ∀ i, screwVel S (p i) = x i := by
  -- Solve on the triangle indexed by `![i₀, i₁, i₂]`.
  obtain ⟨S, hStri, hSuniq⟩ := existsUnique_screwVel_eq_of_triangle
    (q := fun k => p (![i₀, i₁, i₂] k)) (x := fun k => x (![i₀, i₁, i₂] k))
    (by simpa using htri) (fun i j => hbar _ _)
  have hS0 : screwVel S (p i₀) = x i₀ := by simpa using hStri 0
  have hS1 : screwVel S (p i₁) = x i₁ := by simpa using hStri 1
  have hS2 : screwVel S (p i₂) = x i₂ := by simpa using hStri 2
  -- `S` realizes every point.
  have hSall : ∀ i, screwVel S (p i) = x i := by
    intro i
    by_cases hi0 : i = i₀
    · rw [hi0]; exact hS0
    by_cases hi1 : i = i₁
    · rw [hi1]; exact hS1
    by_cases hi2 : i = i₂
    · rw [hi2]; exact hS2
    -- Residual `r = vel_S(p i) − x i` is orthogonal to the three edge directions, hence zero.
    set r := screwVel S (p i) - x i with hr_def
    have key : ∀ a, screwVel S (p a) = x a → (p a - p i) ⬝ᵥ r = 0 := by
      intro a ha
      have hbrick := dotProduct_screwVel_sub S (p i) (p a)
      rw [ha] at hbrick
      have hb := hbar i a
      have hpi : (p i - p a) ⬝ᵥ r = 0 := by
        have hexp : (p i - p a) ⬝ᵥ r
            = (p i - p a) ⬝ᵥ (screwVel S (p i) - x a) - (p i - p a) ⬝ᵥ (x i - x a) := by
          rw [← dotProduct_sub]; congr 1; rw [hr_def]; abel
        rw [hexp, hbrick, hb, sub_zero]
      rw [show p a - p i = -(p i - p a) by abel, neg_dotProduct, hpi, neg_zero]
    have hr0 : r = 0 :=
      eq_zero_of_dotProduct_row_eq_zero (hgp i hi0 hi1 hi2) (fun k => by
        fin_cases k
        · exact key i₀ hS0
        · exact key i₁ hS1
        · exact key i₂ hS2)
    rw [hr_def, sub_eq_zero] at hr0
    exact hr0
  -- Uniqueness reduces to the triangle.
  exact ⟨S, hSall, fun S' hS' => hSuniq S' (fun k => hS' (![i₀, i₁, i₂] k))⟩

end CombinatorialRigidity.Molecular
