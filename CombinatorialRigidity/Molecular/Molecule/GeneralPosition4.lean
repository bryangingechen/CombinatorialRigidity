/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.AlgebraicInduction.PanelHinge

/-!
# Panel normals in general position up to order four

The condition that `lem:theorem-56-general-position` asks of the normals of a panel-hinge framework
in `ℝ³`, and the polynomial of its proof that tests it, as `sec:molecule-modelling-general-position`
presents them. The square-graph dictionary (`thm:molecular-iff-square-bar-joint`) needs the centres
of a molecular framework in general position up to order four (`def:general-position-placement`),
and through the polarity (`lem:panel-hinge-dual-molecular`) the centres are the poles of the normals
of a panel-hinge framework. A normal with a nonzero last coordinate is a nonzero multiple of
`(c, 1)` for a unique point `c`, its pole, and the poles of the normals `q : α × Fin 4 → ℝ` are in
general position up to order four exactly when

* each normal has a nonzero last coordinate (its pole is a point, not at infinity), and
* any four or fewer normals are linearly independent.

`IsGeneralPosition4` is this condition. `exists_generalPosition4_polynomial` gives a polynomial `Q₂`
in the coordinates of the normals that does not vanish at the moment curve and whose non-roots `q`
make `PanelHingeFramework.ofNormals G ends q` satisfy `IsGeneralPosition4`: the order-four form of
`PanelHingeFramework.exists_generalPosition_polynomial`, which tests only that any two normals are
linearly independent (`IsGeneralPosition`). For a tuple `f : Fin j → α` with `j ≤ 4`, the minor
`leadMinorPoly` of the `j × 4` matrix of the normals of `f` on its first `j` columns is a
polynomial; where it does not vanish, the `j` normals are linearly independent (a family is linearly
independent when its projection is), and at the moment curve `q(a, i) = (param a)^i` it is the
Vandermonde determinant `∏_{r < r'} (param (f r') − param (f r))`, which is nonzero for distinct
parameters (`Matrix.det_vandermonde`). `Q₂` is the product of the last coordinates `∏_a X (a, 3)`
and of these minors over the injective tuples of sizes `2`, `3` and `4`. At a non-root a single
normal is nonzero by its last coordinate, and two to four normals are linearly independent by the
minor of a tuple that lists them.

Katoh and Tanigawa need only a nonparallel realization, whose panels meet pairwise in lines (KT
pp. 670–671); the dictionary needs the poles in general position up to order four. The file works in
`ℝ³` (`k = 2`, normals in `ℝ⁴`).

## Main definitions

* `PanelHingeFramework.IsGeneralPosition4`: the normals are in general position up to order four,
  each with a nonzero last coordinate and any four or fewer linearly independent.

## Main results

* `PanelHingeFramework.IsGeneralPosition4.isGeneralPosition`: general position up to order four
  implies general position (`IsGeneralPosition`).
* `PanelHingeFramework.exists_generalPosition4_polynomial`: the polynomial `Q₂`, whose non-roots are
  in general position up to order four.
-/

@[expose] public section

namespace CombinatorialRigidity.Molecular

open MvPolynomial Matrix

variable {α β : Type*}

namespace PanelHingeFramework

/-- **General position up to order four of the normals** (the condition of
`lem:theorem-56-general-position` on the normals; `def:general-position-placement` for their poles):
the panel-hinge framework `P` in `ℝ³` (`k = 2`) has

* every normal with a nonzero last coordinate (`P.normal a (Fin.last 3) ≠ 0`), so that its pole, its
  first three coordinates divided by the last, is a point; and
* any four or fewer normals linearly independent.

As `homogenize` (`Extensor.lean`) appends a last coordinate `1`, this says that the poles are in
general position up to order four, that is, any four or fewer of them are affinely independent: the
condition `IsGeneralPositionPlacement` (`GeneralPositionPlacement.lean`) that the square-graph
dictionary needs. It implies `IsGeneralPosition` (`IsGeneralPosition4.isGeneralPosition`). -/
def IsGeneralPosition4 (P : PanelHingeFramework ℝ 2 α β) : Prop :=
  (∀ a : α, P.normal a (Fin.last 3) ≠ 0) ∧
    (∀ s : Finset α, s.card ≤ 4 → LinearIndependent ℝ (fun a : s => P.normal a))

/-- **General position up to order four implies general position** (a step of
`lem:theorem-56-general-position`): two distinct normals form a set of two, so they are linearly
independent (`IsGeneralPosition`). -/
theorem IsGeneralPosition4.isGeneralPosition {P : PanelHingeFramework ℝ 2 α β}
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

/-- **The leading minor of a tuple of normals** (a step of `lem:theorem-56-general-position`): for
`f : Fin j → α` with `j ≤ 4`, the determinant of the `j × j` matrix of the variables `X (f r, c)` at
the first `j` coordinates `c`. -/
private noncomputable def leadMinorPoly {j : ℕ} (hj : j ≤ 4) (f : Fin j → α) :
    MvPolynomial (α × Fin 4) ℝ :=
  (Matrix.of fun r c : Fin j =>
    (MvPolynomial.X (f r, Fin.castLE hj c) : MvPolynomial (α × Fin 4) ℝ)).det

/-- **The leading minor at numeric normals** (a step of `lem:theorem-56-general-position`): at `q`
it is the determinant of the leading `j × j` minor of the normals `q (f r, ·)`. -/
private theorem eval_leadMinorPoly {j : ℕ} (hj : j ≤ 4) (f : Fin j → α) (q : α × Fin 4 → ℝ) :
    MvPolynomial.eval q (leadMinorPoly hj f)
      = (Matrix.of fun r c : Fin j => q (f r, Fin.castLE hj c)).det := by
  rw [leadMinorPoly, RingHom.map_det]
  congr 1
  ext r c
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPolynomial.eval_X]

/-- **A nonzero leading minor gives independent normals** (a step of
`lem:theorem-56-general-position`): the rows of the leading minor are the images of the normals
under the projection to the first `j` coordinates (`LinearMap.funLeft`), so if those rows are
independent (`Matrix.linearIndependent_rows_of_det_ne_zero`), the normals are too
(`LinearIndependent.of_comp`). -/
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

/-- **The leading minor at the moment curve** (a step of `lem:theorem-56-general-position`): at
`q(a, i) = (param a)^i`, the leading minor of an injective tuple `f` is the Vandermonde determinant
`∏_{r < r'} (param (f r') − param (f r))` (`Matrix.det_vandermonde`), nonzero when `param` is
injective. -/
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

/-! ### The order-four avoidance polynomial -/

/-- **The polynomial that tests general position up to order four** (a step of
`lem:theorem-56-general-position`: the polynomial `Q₂` of its proof): a polynomial `Q` in the
coordinates of the normals that does not vanish at the moment-curve normals `q(a, i) = (param a)^i`
of an injective `param` with no zero value, and whose non-roots `q` make `ofNormals G ends q`
satisfy `IsGeneralPosition4`. It is the order-four form of `exists_generalPosition_polynomial`,
which gives only `IsGeneralPosition`.

`Q` is the product of the last coordinates `∏_a X (a, 3)` and of the leading minors `leadMinorPoly`
of the injective tuples `f : Fin j → α` for `j = 2, 3, 4`. At the moment curve the last coordinates
are `(param a)^3 ≠ 0` and each minor is a Vandermonde determinant of distinct parameters. At a
non-root a single normal is nonzero by its last coordinate, and two to four normals are linearly
independent by the minor of a tuple that lists them.
`exists_rankHypothesis_isGeneralPosition4_of_two_le` takes a non-root of the product of `Q` and the
rank polynomial of `exists_rankPolynomial_of_le_finrank_linking`
(`MvPolynomial.exists_eval_ne_zero`). -/
theorem exists_generalPosition4_polynomial [Finite α] (G : Graph α β) (ends : β → α × α)
    (hlinks : PanelHingeFramework.RecordsLinks G ends := by link_tac) :
    ∃ Q : MvPolynomial (α × Fin 4) ℝ,
      (∀ param : α → ℝ, Function.Injective param → (∀ a, param a ≠ 0) →
        MvPolynomial.eval (fun p => PanelHingeFramework.momentCurve (param p.1) p.2) Q ≠ 0) ∧
      ∀ q : α × Fin 4 → ℝ, MvPolynomial.eval q Q ≠ 0 →
        (PanelHingeFramework.ofNormals (k := 2) G ends q).IsGeneralPosition4 := by
  classical
  have : Fintype α := Fintype.ofFinite α
  set I2 := (Finset.univ : Finset (Fin 2 → α)).filter Function.Injective with hI2
  set I3 := (Finset.univ : Finset (Fin 3 → α)).filter Function.Injective with hI3
  set I4 := (Finset.univ : Finset (Fin 4 → α)).filter Function.Injective with hI4
  refine ⟨(∏ a : α, MvPolynomial.X (a, (Fin.last 3 : Fin 4)))
      * (∏ f ∈ I2, leadMinorPoly (by norm_num) f)
      * (∏ f ∈ I3, leadMinorPoly (by norm_num) f)
      * (∏ f ∈ I4, leadMinorPoly (by norm_num) f), ?_, ?_⟩
  · -- (i) Nonzero at the moment-curve normals of an injective `param` with no zero value.
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
  · -- (ii) A non-root is in general position up to order four.
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
      have : IsEmpty (s : Finset α) :=
        Fintype.card_eq_zero_iff.mp (by rw [Fintype.card_coe]; exact hc)
      exact linearIndependent_empty_type
    · -- card 1: singleton, independent since the normal is nonzero.
      have : Unique (s : Finset α) :=
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
