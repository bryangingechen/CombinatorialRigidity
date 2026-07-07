/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.AlgebraicInduction.PanelHinge
import Mathlib.LinearAlgebra.Vandermonde

/-!
# General position up to order four for panel normals (Theorem 5.6, general-position form)

Phase 25 (`sec:molecule-modelling`, `lem:theorem-56-general-position`, leaf W6). The square-graph
dictionary (`thm:molecular-iff-square-bar-joint`) consumes a placement whose points are in general
position *up to order four* — every subfamily of at most four points affinely independent. On the
panel side of the projective duality (`lem:panel-hinge-dual-molecular`) the corresponding data is a
free normal assignment `q : α × Fin 4 → ℝ` whose **poles** (the dehomogenized normals) are in
general position up to order four; via homogenization this is exactly

* each normal has nonvanishing last coordinate (the poles are affine, not at infinity), and
* every subfamily of at most four normals is linearly independent (as homogeneous points).

This file supplies the **avoidance polynomial** for that condition (Katoh–Tanigawa 2011 p. 671, the
word "nonparallel"; §2.4 step 4 of `notes/Phase25-design.md`): a single nonzero rational
`MvPolynomial (α × Fin 4) ℝ` whose non-roots `q` make `PanelHingeFramework.ofNormals G ends q`
satisfy the order-four general-position predicate `IsGeneralPosition4`. It is the order-four
strengthening of `PanelHingeFramework.exists_generalPosition_polynomial` (which supplies only the
order-two, pairwise, condition `IsGeneralPosition`).

The construction mirrors the order-two one: for an injective tuple `f : Fin j → α` (`j ≤ 4`) the
**leading `j × j` minor** of the `j × 4` normal matrix — the determinant on the first `j`
coordinate columns — is a polynomial `leadMinorPoly`; its nonvanishing forces the `j` normals
linearly independent (a projection of a linearly independent family is dependent only if the family
is), and at the moment curve `q(a, i) = (param a)^i` it is the Vandermonde determinant
`∏_{r < r'} (param (f r') − param (f r))`, nonzero for distinct parameters
(`Matrix.det_vandermonde`). Multiplying the leading minors over injective tuples of sizes `2, 3, 4`
by the last-coordinate factor `∏_a X (a, 3)` gives the avoidance polynomial; a non-root is in
general position up to order four (singletons handled by the last-coordinate factor, larger
subfamilies by the matching leading-minor factor, reindexed onto the subset).

Scope is `ℝ³` (`k = 2`, `Fin 4`) throughout, matching the phase (`notes/Phase25.md`).

See `notes/Phase25-design.md` §2.4 (leaf W6) and `blueprint/src/chapter/molecule-modelling.tex`
(`lem:theorem-56-general-position`).

## Main definitions

* `PanelHingeFramework.IsGeneralPosition4` — the panel normals are in general position up to order
  four: nonvanishing last coordinate plus linear independence of every `≤ 4`-normal subfamily.

## Main results

* `PanelHingeFramework.exists_generalPosition4_polynomial` — the avoidance polynomial: a nonzero
  rational polynomial whose non-roots are the order-four general-position normal assignments.
* `PanelHingeFramework.IsGeneralPosition4.isGeneralPosition` — order four implies order two.
-/

namespace CombinatorialRigidity.Molecular

open MvPolynomial Matrix

variable {α β : Type*}

namespace PanelHingeFramework

/-- **General position up to order four of the panel normals** (`def:general-position-placement`,
panel side; `lem:theorem-56-general-position`). The panel framework `P` (in `ℝ³`, `k = 2`) is in
general position up to order four when

* every normal has nonvanishing last coordinate (`P.normal a (Fin.last 3) ≠ 0`), so its pole — the
  dehomogenization by the last coordinate — is an affine point; and
* every subfamily of at most four normals is linearly independent.

Read through the homogenization convention (`Extensor.homogenize = Fin.snoc · 1`, the affine pole
carries a `1` in the last coordinate), this is precisely: the poles are in general position up to
order four, i.e. every `≤ 4`-subfamily of poles is affinely independent — the condition the
square-graph dictionary consumes (`IsGeneralPositionPlacement`, `GeneralPositionPlacement.lean`).
Strengthens the pairwise `IsGeneralPosition` (`IsGeneralPosition4.isGeneralPosition`). -/
def IsGeneralPosition4 (P : PanelHingeFramework 2 α β) : Prop :=
  (∀ a : α, P.normal a (Fin.last 3) ≠ 0) ∧
    (∀ s : Finset α, s.card ≤ 4 → LinearIndependent ℝ (fun a : s => P.normal a))

/-- Order-four general position implies the order-two (pairwise) general position
`IsGeneralPosition`: any two distinct normals form a `2`-element subfamily, hence are independent.
-/
theorem IsGeneralPosition4.isGeneralPosition {P : PanelHingeFramework 2 α β}
    (hP : P.IsGeneralPosition4) : P.IsGeneralPosition := by
  classical
  intro a b hab
  have hcard : ({a, b} : Finset α).card ≤ 4 := by
    rw [Finset.card_pair hab]; norm_num
  have hLI := hP.2 {a, b} hcard
  -- Reindex the `{a, b}`-subfamily onto `![P.normal a, P.normal b]` via `0 ↦ a, 1 ↦ b`.
  let e : Fin 2 → ({a, b} : Finset α) := ![⟨a, by simp⟩, ⟨b, by simp⟩]
  have he : Function.Injective e := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [e, Subtype.ext_iff]
  have hcomp := hLI.comp e he
  have heq : (fun x : ({a, b} : Finset α) => P.normal x) ∘ e = ![P.normal a, P.normal b] := by
    funext i; fin_cases i <;> rfl
  rwa [heq] at hcomp

/-! ### The leading-minor polynomials

For an injective tuple `f : Fin j → α` (`j ≤ 4`) the leading `j × j` minor of the `j × 4` matrix
of normal variables `X (f r, ·)` — the determinant on the first `j` coordinate columns — is a
polynomial whose nonvanishing forces the `j` normals linearly independent, and which at the moment
curve is the Vandermonde determinant of the parameters. -/

/-- The leading `j × j` minor polynomial of an injective tuple `f : Fin j → α` (`j ≤ 4`): the
determinant of the `j × j` submatrix of normal variables on rows `f r` and the first `j` coordinate
columns. -/
private noncomputable def leadMinorPoly {j : ℕ} (hj : j ≤ 4) (f : Fin j → α) :
    MvPolynomial (α × Fin 4) ℝ :=
  (Matrix.of fun r c : Fin j =>
    (MvPolynomial.X (f r, Fin.castLE hj c) : MvPolynomial (α × Fin 4) ℝ)).det

/-- Evaluating the leading-minor polynomial at `q` is the determinant of the numeric leading minor.
-/
private theorem eval_leadMinorPoly {j : ℕ} (hj : j ≤ 4) (f : Fin j → α) (q : α × Fin 4 → ℝ) :
    MvPolynomial.eval q (leadMinorPoly hj f)
      = (Matrix.of fun r c : Fin j => q (f r, Fin.castLE hj c)).det := by
  rw [leadMinorPoly, RingHom.map_det]
  congr 1
  ext r c
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPolynomial.eval_X]

/-- A nonzero leading minor forces the `j` normals linearly independent: the leading-minor rows are
the images of the normals under the projection to the first `j` coordinates (`LinearMap.funLeft`),
so if those rows are independent (`Matrix.linearIndependent_rows_of_det_ne_zero`) the normals are
too (`LinearIndependent.of_comp`). -/
private theorem linearIndependent_of_eval_leadMinorPoly_ne_zero {j : ℕ} (hj : j ≤ 4)
    (f : Fin j → α) {q : α × Fin 4 → ℝ}
    (h : MvPolynomial.eval q (leadMinorPoly hj f) ≠ 0) :
    LinearIndependent ℝ (fun r : Fin j => (fun i => q (f r, i) : Fin 4 → ℝ)) := by
  rw [eval_leadMinorPoly] at h
  refine LinearIndependent.of_comp (LinearMap.funLeft ℝ ℝ (Fin.castLE hj)) ?_
  have heq : (LinearMap.funLeft ℝ ℝ (Fin.castLE hj)) ∘
        (fun r : Fin j => (fun i => q (f r, i) : Fin 4 → ℝ))
      = fun r : Fin j => (Matrix.of fun r' c : Fin j => q (f r', Fin.castLE hj c)) r := by
    funext r; ext c; simp [LinearMap.funLeft_apply, Matrix.of_apply]
  rw [heq]
  exact Matrix.linearIndependent_rows_of_det_ne_zero h

/-- At the moment curve `q(a, i) = (param a)^i`, the leading-minor polynomial of an injective tuple
is the Vandermonde determinant `∏_{r < r'} (param (f r') − param (f r))`, nonzero for distinct
parameters (`Matrix.det_vandermonde`). -/
private theorem eval_momentCurve_leadMinorPoly_ne_zero {j : ℕ} (hj : j ≤ 4)
    {f : Fin j → α} (hf : Function.Injective f) {param : α → ℝ}
    (hparam : Function.Injective param) :
    MvPolynomial.eval (fun p => PanelHingeFramework.momentCurve (param p.1) p.2)
      (leadMinorPoly hj f) ≠ 0 := by
  rw [eval_leadMinorPoly]
  have hmat : (Matrix.of fun r c : Fin j =>
        (fun p => PanelHingeFramework.momentCurve (param p.1) p.2) (f r, Fin.castLE hj c))
      = Matrix.vandermonde (fun r => param (f r)) := by
    ext r c
    simp only [Matrix.of_apply, Matrix.vandermonde_apply, PanelHingeFramework.momentCurve_apply,
      Fin.val_castLE]
  rw [hmat, Matrix.det_vandermonde, Finset.prod_ne_zero_iff]
  intro r _
  rw [Finset.prod_ne_zero_iff]
  intro r' hr'
  rw [Finset.mem_Ioi] at hr'
  exact sub_ne_zero.mpr fun heq => absurd (hf (hparam heq)) hr'.ne'

/-- The leading-minor polynomial has rational (indeed integer) coefficients: it is the image under
`MvPolynomial.map (algebraMap ℚ ℝ)` of the same determinant over `MvPolynomial (α × Fin 4) ℚ`. -/
private theorem leadMinorPoly_mem_range_map {j : ℕ} (hj : j ≤ 4) (f : Fin j → α) :
    leadMinorPoly hj f ∈ (MvPolynomial.map (algebraMap ℚ ℝ) (σ := α × Fin 4)).range := by
  refine ⟨(Matrix.of fun r c : Fin j =>
    (MvPolynomial.X (f r, Fin.castLE hj c) : MvPolynomial (α × Fin 4) ℚ)).det, ?_⟩
  rw [RingHom.map_det, leadMinorPoly]
  congr 1
  ext r c
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPolynomial.map_X]

/-! ### The order-four avoidance polynomial -/

/-- **The order-four general-position avoidance polynomial** (`lem:theorem-56-general-position`,
§2.4 step 4 of `notes/Phase25-design.md`; Katoh–Tanigawa 2011 p. 671, "nonparallel"). A single
nonzero rational `MvPolynomial (α × Fin 4) ℝ` whose non-roots `q` are exactly the normal
assignments in general position up to order four: `ofNormals G ends q` satisfies
`IsGeneralPosition4` (nonvanishing last coordinate — the poles are affine — plus linear
independence of every `≤ 4`-normal subfamily). The order-four strengthening of
`exists_generalPosition_polynomial` (which supplies only the pairwise `IsGeneralPosition`).

Concretely the product of the last-coordinate factor `∏_a X (a, 3)` with the leading `j × j` minors
`leadMinorPoly` over injective tuples `f : Fin j → α` of sizes `j = 2, 3, 4`. It is genuinely
nonzero (witnessed): at an injective parameter `param : α → ℝ` avoiding `0`, the moment-curve
assignment `q(a, i) = (param a)^i` makes the last-coordinate factor `∏_a (param a)^3 ≠ 0` and each
minor factor the Vandermonde determinant of distinct parameters, so the product is nonzero. A
non-root is in general position up to order four: singletons come from the last-coordinate factor
(a nonzero last coordinate makes the normal nonzero), and each `2 ≤ |s| ≤ 4` subfamily reindexes
onto the matching leading-minor factor. Multiplying this factor into the deficiency-graded rank
polynomial (`exists_rankPolynomial_of_le_finrank_linking`) and applying an algebraically-independent
seed yields the general-position form of Theorem 5.6 the square-graph dictionary consumes. -/
theorem exists_generalPosition4_polynomial [Finite α] (G : Graph α β) (ends : β → α × α) :
    ∃ Q : MvPolynomial (α × Fin 4) ℝ,
      (∀ param : α → ℝ, Function.Injective param → (∀ a, param a ≠ 0) →
        MvPolynomial.eval (fun p => PanelHingeFramework.momentCurve (param p.1) p.2) Q ≠ 0) ∧
      (Q.coeffs : Set ℝ) ⊆ Set.range (algebraMap ℚ ℝ) ∧
      ∀ q : α × Fin 4 → ℝ, MvPolynomial.eval q Q ≠ 0 →
        (PanelHingeFramework.ofNormals (k := 2) G ends q).IsGeneralPosition4 := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  set I2 := (Finset.univ : Finset (Fin 2 → α)).filter Function.Injective with hI2
  set I3 := (Finset.univ : Finset (Fin 3 → α)).filter Function.Injective with hI3
  set I4 := (Finset.univ : Finset (Fin 4 → α)).filter Function.Injective with hI4
  refine ⟨(∏ a : α, MvPolynomial.X (a, (Fin.last 3 : Fin 4)))
      * (∏ f ∈ I2, leadMinorPoly (by norm_num) f)
      * (∏ f ∈ I3, leadMinorPoly (by norm_num) f)
      * (∏ f ∈ I4, leadMinorPoly (by norm_num) f), ?_, ?_, ?_⟩
  · -- (i) Nonzero at any injective, nonvanishing moment-curve seed.
    intro param hparam hpne
    simp only [map_mul, map_prod]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_
    · rw [Finset.prod_ne_zero_iff]
      intro a _
      rw [MvPolynomial.eval_X]
      simpa [PanelHingeFramework.momentCurve_apply] using pow_ne_zero (3 : ℕ) (hpne a)
    · rw [Finset.prod_ne_zero_iff]
      exact fun f hf => eval_momentCurve_leadMinorPoly_ne_zero _ (Finset.mem_filter.mp hf).2 hparam
    · rw [Finset.prod_ne_zero_iff]
      exact fun f hf => eval_momentCurve_leadMinorPoly_ne_zero _ (Finset.mem_filter.mp hf).2 hparam
    · rw [Finset.prod_ne_zero_iff]
      exact fun f hf => eval_momentCurve_leadMinorPoly_ne_zero _ (Finset.mem_filter.mp hf).2 hparam
  · -- (ii) Rational coefficients.
    rw [← MvPolynomial.mem_range_map_iff_coeffs_subset]
    set S := (MvPolynomial.map (algebraMap ℚ ℝ) (σ := α × Fin 4)).range with hS
    exact Subring.mul_mem _ (Subring.mul_mem _ (Subring.mul_mem _
      (Subring.prod_mem S fun a _ => ⟨MvPolynomial.X (a, Fin.last 3), MvPolynomial.map_X _ _⟩)
      (Subring.prod_mem S fun f _ => leadMinorPoly_mem_range_map _ f))
      (Subring.prod_mem S fun f _ => leadMinorPoly_mem_range_map _ f))
      (Subring.prod_mem S fun f _ => leadMinorPoly_mem_range_map _ f)
  · -- (iii) A non-root is in general position up to order four.
    intro q hq
    rw [map_mul, map_mul, map_mul, mul_ne_zero_iff, mul_ne_zero_iff, mul_ne_zero_iff] at hq
    obtain ⟨⟨⟨hlast, h2⟩, h3⟩, h4⟩ := hq
    rw [map_prod, Finset.prod_ne_zero_iff] at hlast
    rw [map_prod, Finset.prod_ne_zero_iff] at h2 h3 h4
    -- Nonvanishing last coordinate.
    have hlast' : ∀ a : α, q (a, Fin.last 3) ≠ 0 := by
      intro a
      have := hlast a (Finset.mem_univ a)
      rwa [MvPolynomial.eval_X] at this
    refine ⟨fun a => by simpa [PanelHingeFramework.ofNormals_normal] using hlast' a, ?_⟩
    -- A reindexing helper: linear independence of a `Fin m`-tuple transports to the subset.
    have reindex : ∀ (m : ℕ) (s : Finset α) (e : (s : Finset α) ≃ Fin m),
        LinearIndependent ℝ
          (fun r : Fin m => (fun i => q ((e.symm r : α), i) : Fin 4 → ℝ)) →
        LinearIndependent ℝ
          (fun a : s => (PanelHingeFramework.ofNormals (k := 2) G ends q).normal a) := by
      intro m s e hLI
      simp only [PanelHingeFramework.ofNormals_normal]
      exact (linearIndependent_equiv e.symm).mp hLI
    intro s hs
    rcases (show s.card = 0 ∨ s.card = 1 ∨ s.card = 2 ∨ s.card = 3 ∨ s.card = 4 from by omega)
      with hc | hc | hc | hc | hc
    · -- card 0: empty family.
      haveI : IsEmpty (s : Finset α) :=
        Fintype.card_eq_zero_iff.mp (by rw [Fintype.card_coe]; exact hc)
      exact linearIndependent_empty_type
    · -- card 1: singleton, independent since the normal is nonzero.
      haveI : Unique (s : Finset α) :=
        (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hc])).unique
      rw [linearIndependent_unique_iff]
      simp only [PanelHingeFramework.ofNormals_normal]
      exact fun hz => hlast' _ (congrFun hz (Fin.last 3))
    · -- card 2.
      have e : (s : Finset α) ≃ Fin 2 := Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hc])
      refine reindex 2 s e ?_
      refine linearIndependent_of_eval_leadMinorPoly_ne_zero (by norm_num)
        (fun r => (e.symm r : α)) (h2 _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩))
      exact fun i j hij => e.symm.injective (Subtype.ext hij)
    · -- card 3.
      have e : (s : Finset α) ≃ Fin 3 := Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hc])
      refine reindex 3 s e ?_
      refine linearIndependent_of_eval_leadMinorPoly_ne_zero (by norm_num)
        (fun r => (e.symm r : α)) (h3 _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩))
      exact fun i j hij => e.symm.injective (Subtype.ext hij)
    · -- card 4.
      have e : (s : Finset α) ≃ Fin 4 := Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hc])
      refine reindex 4 s e ?_
      refine linearIndependent_of_eval_leadMinorPoly_ne_zero (by norm_num)
        (fun r => (e.symm r : α)) (h4 _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩))
      exact fun i j hij => e.symm.injective (Subtype.ext hij)

end PanelHingeFramework

end CombinatorialRigidity.Molecular
