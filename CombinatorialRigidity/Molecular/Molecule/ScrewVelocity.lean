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
`vel_S(x) = ω_S ×₃ x + t_S`.

The two coordinate maps `screwOmega`, `screwTau : ScrewSpace 2 →ₗ[ℝ] (Fin 3 → ℝ)` are the two
graded pieces of the isomorphism `⋀² ℝ⁴ ≅ ⋀² ℝ³ ⊕ (ℝ³ ⊗ ℝ) ≅ ℝ³ × ℝ³`, built here as lifts of
two explicit alternating `2`-forms along `exteriorPower.alternatingMapLinearEquiv` and the
`ScrewSpace` boundary equivalence. On the line `2`-extensor `â ∨ b̂` of two homogenized points
they read off `ω = b − a` and `t = a ×₃ b` (`screwOmega_lineExtensor`,
`screwTau_lineExtensor`), so `vel_{â∨b̂}` is the rotation field about the line through `a` and
`b` (`screwVel_lineExtensor`).

## Main definitions

* `CombinatorialRigidity.Molecular.screwOmega`, `screwTau` — the rotation and translation
  coordinate maps of a screw.
* `CombinatorialRigidity.Molecular.screwVel` — the velocity field `vel_S(x) = ω_S ×₃ x + t_S`
  (`def:screw-velocity`).
* `CombinatorialRigidity.Molecular.lineExtensor` — the line `2`-extensor `â ∨ b̂` of two points
  (the supporting extensor of a molecular hinge, `def:hinge-concurrent`).

## Main results

* `screwVel_lineExtensor` — `vel_{â∨b̂}(x) = (b − a) ×₃ x + a ×₃ b`.
* `dotProduct_screwVel_sub` — every velocity field is infinitesimally isometric:
  `(x − y) ⬝ᵥ (vel_S x − vel_S y) = 0` (brick (1) of §2.3).
* `screwVel_eq_zero_iff_mem_span` — for distinct `a, b`: `vel_S a = 0 ∧ vel_S b = 0` iff `S` is
  a scalar multiple of `â ∨ b̂` (brick (2), `lem:screw-velocity-line`).
* `eq_zero_of_screwVel_eq_zero` — a screw whose velocity field vanishes at three non-collinear
  points is zero (brick (3), the kill half of `lem:screw-determination`).

The `∃!`-existence half of `lem:screw-determination` (brick (4), body determination) is deferred:
it needs the rank of a non-collinear triangle's bar-joint rigidity matrix (design §2.3(4), flag
F2), which is bar-joint machinery. See `notes/Phase25.md`.
-/

@[expose] public section

open scoped Matrix
open exteriorPower

namespace CombinatorialRigidity.Molecular

/-! ## Cross-product bilinearity helpers -/

theorem crossProduct_sub_left (u w v : Fin 3 → ℝ) : (u - w) ⨯₃ v = u ⨯₃ v - w ⨯₃ v := by
  rw [map_sub, LinearMap.sub_apply]

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

/-- The **translation part** as an alternating `2`-form on `ℝ⁴`: `t(v, w) = (v spatial) ×₃ (w
spatial)`. On homogenized points `v = â, w = b̂` it reads `a ×₃ b`. -/
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

/-- **The velocity field of a screw** (`def:screw-velocity`): `vel_S(x) = ω_S ×₃ x + t_S`, the
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
`b`: `vel_{â∨b̂}(x) = (b − a) ×₃ x + a ×₃ b` (`def:screw-velocity`). -/
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
`vel_S x − vel_S y = ω_S ×₃ (x − y)`. -/
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

/-- If `ω ×₃ u = 0` and `u ≠ 0`, then `ω` is a scalar multiple of `u` (both are collinear). -/
theorem exists_smul_of_crossProduct_eq_zero {ω u : Fin 3 → ℝ} (hu : u ≠ 0) (h : ω ⨯₃ u = 0) :
    ∃ c : ℝ, ω = c • u := by
  have hdep : ¬ LinearIndependent ℝ ![u, ω] := by
    rw [← crossProduct_ne_zero_iff_linearIndependent, not_not, ← cross_anticomm, h, neg_zero]
  rw [LinearIndependent.pair_iff' hu] at hdep
  simp only [not_forall, ne_eq, not_not] at hdep
  obtain ⟨c, hc⟩ := hdep
  exact ⟨c, hc.symm⟩

/-- If `ω ×₃ u = 0` and `ω ×₃ w = 0` with `u, w` linearly independent, then `ω = 0`. -/
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
    -- `ω ×₃ (b − a) = 0`, so `ω = c • (b − a)`.
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
      -- `t_S = a ×₃ b` scaled by `c`, from `vel_S a = 0`.
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

end CombinatorialRigidity.Molecular
