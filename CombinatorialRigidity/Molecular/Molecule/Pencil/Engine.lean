/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Chart
public import CombinatorialRigidity.Molecular.AlgebraicInduction.PanelHingeForms

/-!
# The pencil chart in coordinates, and `cross₃` of independent vectors

Two parts of the proof of `lem:pencil-generic-steer` (`sec:main-component-statements`), on the chart
of `Chart.lean`.

The first writes the chart in coordinates. A point `q : α × Fin 4 × Fin 4 → K` gives the parameters
`PencilSeed.ofCoord q`: at each body `v`, `hubNormal v` is `q (v, 0, ·)`, and the padding vector `j`
of both `fillHub v` and `fillNbr v` is `q (v, j.succ, ·)`. For fixed selectors, the coordinates of
the points of the chart are polynomials in `q`, as the coordinates of `cross₃` are determinants
(`cross₃_apply`). A family of points that is linearly independent at some `q₀` is independent at
every non-root of a polynomial nonzero at `q₀`, a minor of the matrix of its coordinates
(`exists_polynomial_ne_zero_of_linearIndependent_at_reindex`); and over an infinite field, finitely
many polynomials, each nonzero at some point, have a common non-root.

The second gives two facts on `cross₃`. `cross₃` of three independent vectors is a nonzero
multiple of any nonzero vector orthogonal to them, which writing a given nondegenerate realization
in the chart uses (`exists_pencilSeed_of_nondeg_of_selectors`, `Reseed.lean`). And the `cross₃` of
three distinct standard basis vectors is a nonzero multiple of the fourth, for
`lem:pencil-generic-steer` (`MainComponent/GenericSteer.lean`).

## Main definitions

* `PencilSeed.ofCoord`: the parameters of the chart at a point of `α × Fin 4 × Fin 4 → K`.
* `pencilChartPointPoly`: the points of the chart as polynomials.

## Main results

* `exists_polynomial_ne_zero_of_linearIndependent_pencilChartPoint`: a family of points independent
  at one coordinate point is independent at every non-root of a polynomial nonzero there.
* `exists_common_eval_ne_zero_of_forall_exists`: over an infinite field, finitely many polynomials,
  each nonzero at some point, have a common non-root.
* `exists_smul_cross₃_eq_of_linearIndependent`: `cross₃` of three independent vectors is a multiple
  of any nonzero vector orthogonal to them.
-/

@[expose] public section

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K]
variable {α β : Type*}

/-! ## The chart as polynomials in its parameters

A point `q : α × Fin 4 × Fin 4 → K` gives the parameters `PencilSeed.ofCoord q`: its first factor is
the body, its second the vector, `0` for `hubNormal` and `j.succ` for the padding vector `j` of both
triples, and its third the coordinate. The variable at `(v, r, i)` is `pencilXPoly r v i`.

Each construction of the chart that the points read has a polynomial form, whose value at `q` is the
construction at `PencilSeed.ofCoord q`, as evaluation is a ring homomorphism and commutes with
`Matrix.det` (`RingHom.map_det`): `cross₃Poly`, by `cross₃_apply`, which writes the coordinate `i`
of `cross₃ x y z` as `det[x, y, z, e_i]`; the slots of the hub selector (`hubSlotNormalPoly`); and
the points (`pencilChartPointPoly`). -/

/-- **The parameters of the chart at a coordinate point** (a step of `lem:pencil-generic-steer`):
`hubNormal v` is `q (v, 0, ·)`, and the padding vector `j` of both `fillHub v` and `fillNbr v` is
`q (v, j.succ, ·)`. So only parameters whose two triples of padding vectors agree have coordinates;
`PencilSeed.toCoord` (`Steer.lean`) gives back the `hubNormal` and `fillHub` of any parameters. -/
def PencilSeed.ofCoord (q : α × Fin 4 × Fin 4 → K) : PencilSeed K α where
  hubNormal v i := q (v, 0, i)
  fillHub v j i := q (v, j.succ, i)
  fillNbr v j i := q (v, j.succ, i)

/-- **A variable of the coordinate space** (a step of `lem:pencil-generic-steer`): `X (v, role, i)`,
the coordinate `i` of the vector `role` at body `v` (`pencilXPoly_eval`). -/
noncomputable def pencilXPoly (role : Fin 4) (v : α) (i : Fin 4) :
    MvPolynomial (α × Fin 4 × Fin 4) K :=
  MvPolynomial.X (v, role, i)

@[simp]
theorem pencilXPoly_eval (role : Fin 4) (v : α) (q : α × Fin 4 × Fin 4 → K) (i : Fin 4) :
    MvPolynomial.eval q (pencilXPoly role v i) = q (v, role, i) := by
  rw [pencilXPoly, MvPolynomial.eval_X]

/-- **The coordinates of `cross₃` are determinants** (a step of `lem:pencil-generic-steer`):
`cross₃ x y z i = det[x, y, z, e_i]`, the value of `dotProduct_cross₃` at the standard basis vector
`e_i = Pi.single i 1` (`dotProduct_single_one`). So they are polynomials in the coordinates of `x`,
`y` and `z` (`cross₃Poly`). -/
theorem cross₃_apply (x y z : Fin 4 → K) (i : Fin 4) :
    cross₃ x y z i = Matrix.det (Matrix.of ![x, y, z, Pi.single i 1]) := by
  rw [← dotProduct_single_one (cross₃ x y z) i, dotProduct_cross₃]

/-- **`cross₃` of vectors of polynomials** (a step of `lem:pencil-generic-steer`): for
`X Y Z : Fin 4 → MvPolynomial σ K`, the coordinate `i` is `det[X, Y, Z, e_i]`, as in `cross₃_apply`
(`cross₃Poly_eval`). -/
noncomputable def cross₃Poly {σ : Type*} (X Y Z : Fin 4 → MvPolynomial σ K) (i : Fin 4) :
    MvPolynomial σ K :=
  Matrix.det (Matrix.of ![X, Y, Z, Pi.single i (1 : MvPolynomial σ K)])

/-- **The value of `cross₃Poly`**: at `q`, it is `cross₃` of the values of `X`, `Y` and `Z`, as
evaluation commutes with `Matrix.det` (`RingHom.map_det`) and takes the row `e_i` to `e_i`. -/
theorem cross₃Poly_eval {σ : Type*} (X Y Z : Fin 4 → MvPolynomial σ K) (q : σ → K) (i : Fin 4) :
    MvPolynomial.eval q (cross₃Poly X Y Z i) =
      cross₃ (fun j => MvPolynomial.eval q (X j)) (fun j => MvPolynomial.eval q (Y j))
        (fun j => MvPolynomial.eval q (Z j)) i := by
  rw [cross₃_apply, cross₃Poly, (MvPolynomial.eval q).map_det]
  congr 1
  ext a b
  fin_cases a <;> simp [RingHom.mapMatrix_apply, Pi.single_apply]

/-- **Slot `slot` of `v`'s hub selector as a vector of polynomials** (a step of
`lem:pencil-generic-steer`): the variables of the `hubNormal` of the body in it, or of the padding
vector `slot` of `v` if it is empty; the form of `hubSlotNormal` (`hubSlotNormalPoly_eval`). -/
noncomputable def hubSlotNormalPoly (hubSel : α → Fin 3 → Option α) (v : α) (slot : Fin 3) :
    Fin 4 → MvPolynomial (α × Fin 4 × Fin 4) K :=
  match hubSel v slot with
  | some w => pencilXPoly 0 w
  | none => pencilXPoly slot.succ v

/-- **The value of `hubSlotNormalPoly`**: at `q`, the coordinate `i` of slot `slot` of `v`'s hub
selector at `PencilSeed.ofCoord q` (`hubSlotNormal`). -/
theorem hubSlotNormalPoly_eval (hubSel : α → Fin 3 → Option α) (v : α) (slot : Fin 3)
    (q : α × Fin 4 × Fin 4 → K) (i : Fin 4) :
    MvPolynomial.eval q (hubSlotNormalPoly hubSel v slot i)
      = hubSlotNormal (PencilSeed.ofCoord q) hubSel v slot i := by
  simp only [hubSlotNormalPoly, hubSlotNormal, PencilSeed.ofCoord]
  cases hubSel v slot <;> simp

/-- **`hubSlotNormalPoly_eval` for the whole vector**: the values at `q` of the coordinates of
`hubSlotNormalPoly hubSel v slot` form `hubSlotNormal (PencilSeed.ofCoord q) hubSel v slot`, the
form in which `pencilChartPointPoly_eval` rewrites each of its three slots. -/
theorem hubSlotNormalPoly_eval_funext (hubSel : α → Fin 3 → Option α) (v : α) (slot : Fin 3)
    (q : α × Fin 4 × Fin 4 → K) :
    (fun j => MvPolynomial.eval q (hubSlotNormalPoly hubSel v slot j))
      = hubSlotNormal (PencilSeed.ofCoord q) hubSel v slot :=
  funext fun j => hubSlotNormalPoly_eval hubSel v slot q j

/-- **The point of the chart as a vector of polynomials** (a step of `lem:pencil-generic-steer`):
`cross₃Poly` of the three slots of `v`'s hub selector (`hubSlotNormalPoly`); the form of
`pencilChartPoint` (`pencilChartPointPoly_eval`). -/
noncomputable def pencilChartPointPoly (hubSel : α → Fin 3 → Option α) (v : α) :
    Fin 4 → MvPolynomial (α × Fin 4 × Fin 4) K :=
  cross₃Poly (hubSlotNormalPoly hubSel v 0) (hubSlotNormalPoly hubSel v 1)
    (hubSlotNormalPoly hubSel v 2)

/-- **The value of `pencilChartPointPoly`**: at `q`, the coordinate `i` of the point of the chart at
`PencilSeed.ofCoord q` (`pencilChartPoint`). -/
theorem pencilChartPointPoly_eval (hubSel : α → Fin 3 → Option α) (v : α)
    (q : α × Fin 4 × Fin 4 → K) (i : Fin 4) :
    MvPolynomial.eval q (pencilChartPointPoly hubSel v i)
      = pencilChartPoint (PencilSeed.ofCoord q) hubSel v i := by
  rw [pencilChartPointPoly, cross₃Poly_eval, pencilChartPoint,
    hubSlotNormalPoly_eval_funext hubSel v 0 q,
    hubSlotNormalPoly_eval_funext hubSel v 1 q,
    hubSlotNormalPoly_eval_funext hubSel v 2 q]

/-! ## Independent points, and a common non-root

A family of points of the chart independent at some `q₀` is independent at every non-root of a
polynomial nonzero at `q₀`, by `exists_polynomial_ne_zero_of_linearIndependent_at_reindex` in the
coordinates of `K⁴` (`pencilChartPointPoly_eval`). This needs no infinite field. Over an infinite
field, finitely many polynomials, each nonzero at some point, have a common non-root
(`exists_common_eval_ne_zero_of_forall_exists`). As in the proof of `lem:pencil-generic-steer`, each
condition then holds at one point. -/

/-- **Points of the chart independent at `q₀` stay so off the zero set of a polynomial** (a step of
`lem:pencil-generic-steer`): for `ends : ι → α`, with `ι` finite, if the points of the chart at
`ends i`, for `i` in a set `s`, are linearly independent at `q₀`, there is a polynomial, nonzero at
`q₀`, at whose every non-root they are independent.
`exists_common_seed_linearIndepOn_pencilChartPoint` (`Steer.lean`) uses it at `ends := id`. -/
theorem exists_polynomial_ne_zero_of_linearIndependent_pencilChartPoint
    {ι : Type*} [Finite ι] (hubSel : α → Fin 3 → Option α) (ends : ι → α)
    {q₀ : α × Fin 4 × Fin 4 → K} {s : Set ι}
    (h : LinearIndependent K
      (fun i : s => pencilChartPoint (PencilSeed.ofCoord q₀) hubSel (ends i))) :
    ∃ Q : MvPolynomial (α × Fin 4 × Fin 4) K, MvPolynomial.eval q₀ Q ≠ 0 ∧
      ∀ q, MvPolynomial.eval q Q ≠ 0 →
        LinearIndependent K
          (fun i : s => pencilChartPoint (PencilSeed.ofCoord q) hubSel (ends i)) :=
  exists_polynomial_ne_zero_of_linearIndependent_at_reindex (finCongr (Module.finrank_fin_fun K))
    (fun q i => pencilChartPoint (PencilSeed.ofCoord q) hubSel (ends i))
    (fun i j => pencilChartPointPoly hubSel (ends i) j)
    (LinearEquiv.refl K (Fin 4 → K))
    (fun q i j => (pencilChartPointPoly_eval hubSel (ends i) q j).symm)
    h

/-- **Finitely many polynomials, each nonzero at some point, have a common non-root** (a step of
`lem:pencil-generic-steer`): over an infinite field, if each of finitely many polynomials is nonzero
at some point, then at some point they are all nonzero. Each is then a nonzero polynomial, and
`MvPolynomial.exists_eval_ne_zero_of_forall_ne_zero` (`Mathlib/Algebra/MvPolynomial/Funext.lean`)
takes a non-root of their product. -/
theorem exists_common_eval_ne_zero_of_forall_exists [Infinite K] {σ ι : Type*} [Finite ι]
    (P : ι → MvPolynomial σ K) (h : ∀ i, ∃ q : σ → K, MvPolynomial.eval q (P i) ≠ 0) :
    ∃ q : σ → K, ∀ i, MvPolynomial.eval q (P i) ≠ 0 :=
  MvPolynomial.exists_eval_ne_zero_of_forall_ne_zero P fun i h0 => by
    obtain ⟨q, hq⟩ := h i
    simp [h0] at hq

/-! ## `cross₃` of three independent vectors orthogonal to a point

To write a nondegenerate realization in the chart (the converse in the proof of
`lem:pencil-generic-steer`), the point of each body is written as `cross₃` of the normals of its
closed hub-neighbourhood, which are independent, orthogonal to the point and at most three,
completed by padding vectors to an independent triple orthogonal to the point
(`exists_fill_cross₃_eq_smul_of_selector`, `Reseed.lean`). `cross₃` of three independent vectors
and a nonzero vector orthogonal to them lie in the space of the vectors orthogonal to the three, of
dimension `1`, so each is a nonzero multiple of the other
(`exists_smul_cross₃_eq_of_linearIndependent`). So the chart reproduces a realization up to a
nonzero scalar at each point, which, as that proof notes, changes neither its nondegeneracy nor the
line of any hinge. -/

/-- **`cross₃` of three independent vectors is a multiple of any nonzero vector orthogonal to them**
(a step of `lem:pencil-generic-steer`): for independent `n₁, n₂, n₃` and `q ≠ 0` orthogonal to the
three, `cross₃ n₁ n₂ n₃ = c • q` for some `c ≠ 0`. Both lie in the space of the vectors orthogonal
to the three (`cross₃_dotProduct_fst` and its siblings), of dimension `1`
(`finrank_toDualPerp_triple_eq`), which `q` spans; and `cross₃ n₁ n₂ n₃ ≠ 0`
(`cross₃_ne_zero_iff_linearIndependent`). -/
theorem exists_smul_cross₃_eq_of_linearIndependent {n₁ n₂ n₃ q : Fin 4 → K}
    (hLI : LinearIndependent K ![n₁, n₂, n₃]) (hq : q ≠ 0)
    (hq1 : q ⬝ᵥ n₁ = 0) (hq2 : q ⬝ᵥ n₂ = 0) (hq3 : q ⬝ᵥ n₃ = 0) :
    ∃ c : K, c ≠ 0 ∧ cross₃ n₁ n₂ n₃ = c • q := by
  set perp : Submodule K (Fin 4 → K) :=
    ⨅ j : Fin 3, LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip (![n₁, n₂, n₃] j)) with hperp
  have hmem : ∀ x : Fin 4 → K, x ∈ perp ↔ x ⬝ᵥ n₁ = 0 ∧ x ⬝ᵥ n₂ = 0 ∧ x ⬝ᵥ n₃ = 0 := by
    intro x
    simp only [hperp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply,
      piBasisFun_toDual_eq_dotProduct]
    constructor
    · intro h; exact ⟨by simpa using h 0, by simpa using h 1, by simpa using h 2⟩
    · rintro ⟨h0, h1, h2⟩ j; fin_cases j <;> simpa
  have hqperp : q ∈ perp := (hmem q).2 ⟨hq1, hq2, hq3⟩
  have hcperp : cross₃ n₁ n₂ n₃ ∈ perp := (hmem _).2
    ⟨cross₃_dotProduct_fst n₁ n₂ n₃, cross₃_dotProduct_snd n₁ n₂ n₃,
      cross₃_dotProduct_thd n₁ n₂ n₃⟩
  have hdim : Module.finrank K perp = 1 := finrank_toDualPerp_triple_eq hLI
  have hspan : Submodule.span K {q} = perp := by
    refine Submodule.eq_of_le_of_finrank_eq
      (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hqperp)) ?_
    rw [finrank_span_singleton hq, hdim]
  rw [← hspan] at hcperp
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hcperp
  have hcross_ne : cross₃ n₁ n₂ n₃ ≠ 0 := (cross₃_ne_zero_iff_linearIndependent _ _ _).mpr hLI
  have hcne : c ≠ 0 := fun h0 => hcross_ne (by rw [← hc, h0, zero_smul])
  exact ⟨c, hcne, hc.symm⟩

/-! ## `cross₃` of standard basis vectors

Three distinct standard basis vectors of `K⁴` are independent
(`linearIndependent_pi_single_triple`), and their `cross₃` is a nonzero multiple of the fourth
(`exists_smul_cross₃_pi_single`), which is nonzero and orthogonal to the three. So a point of the
chart whose hub slots are three distinct standard basis vectors is a nonzero multiple of the fourth
(`exists_smul_pencilChartPoint_of_hubSlotNormal_eq_pi_single`), as
`lem:pencil-generic-steer` uses (`exists_coord_linearIndependent_pencilChartPoint_of_other_nonhub`,
`MainComponent/GenericSteer.lean`). Only the independence of such points matters there, which a
nonzero scalar at each point does not change. -/

/-- **Three distinct standard basis vectors of `K⁴` are linearly independent** (a step of
`lem:pencil-generic-steer`): they are the vectors of `Pi.basisFun K (Fin 4)` at the injective
`![a, b, c]`. -/
theorem linearIndependent_pi_single_triple {a b c : Fin 4} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    LinearIndependent K ![(Pi.single a (1 : K) : Fin 4 → K), Pi.single b 1, Pi.single c 1] := by
  have hinj : Function.Injective (![a, b, c] : Fin 3 → Fin 4) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have h := ((Pi.basisFun K (Fin 4)).linearIndependent).comp (![a, b, c] : Fin 3 → Fin 4) hinj
  have heq : (Pi.basisFun K (Fin 4)) ∘ (![a, b, c] : Fin 3 → Fin 4)
      = ![(Pi.single a (1 : K) : Fin 4 → K), Pi.single b 1, Pi.single c 1] := by
    funext j; fin_cases j <;> simp [Pi.basisFun_apply]
  rwa [heq] at h

/-- **`cross₃` of three distinct standard basis vectors is a nonzero multiple of the fourth** (a
step of `lem:pencil-generic-steer`): for distinct `a, b, c, d : Fin 4`, `cross₃ e_a e_b e_c` is a
nonzero multiple of `e_d`, by `exists_smul_cross₃_eq_of_linearIndependent` at `q := e_d`, which is
nonzero and orthogonal to `e_a`, `e_b` and `e_c` (`dotProduct_single_one`). -/
theorem exists_smul_cross₃_pi_single {a b c d : Fin 4} (had : a ≠ d) (hbd : b ≠ d) (hcd : c ≠ d)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ e : K, e ≠ 0 ∧ cross₃ (Pi.single a (1 : K)) (Pi.single b 1) (Pi.single c 1)
      = e • Pi.single d (1 : K) := by
  have hLI := linearIndependent_pi_single_triple (K := K) hab hac hbc
  have hd_ne : (Pi.single d (1 : K) : Fin 4 → K) ≠ 0 := by
    intro h
    have := congrFun h d
    simp at this
  have hq1 : (Pi.single d (1 : K) : Fin 4 → K) ⬝ᵥ Pi.single a (1 : K) = 0 := by
    rw [dotProduct_single_one, Pi.single_apply, ite_eq_right had]
  have hq2 : (Pi.single d (1 : K) : Fin 4 → K) ⬝ᵥ Pi.single b (1 : K) = 0 := by
    rw [dotProduct_single_one, Pi.single_apply, ite_eq_right hbd]
  have hq3 : (Pi.single d (1 : K) : Fin 4 → K) ⬝ᵥ Pi.single c (1 : K) = 0 := by
    rw [dotProduct_single_one, Pi.single_apply, ite_eq_right hcd]
  exact exists_smul_cross₃_eq_of_linearIndependent hLI hd_ne hq1 hq2 hq3

/-- **A point of the chart whose hub slots are distinct standard basis vectors** (a step of
`lem:pencil-generic-steer`): if slot `i` of `v`'s hub selector is `e_{σ i}`, for an injective
`σ : Fin 3 → Fin 4` that misses `d`, the point of `v` is a nonzero multiple of `e_d`
(`exists_smul_cross₃_pi_single`). -/
theorem exists_smul_pencilChartPoint_of_hubSlotNormal_eq_pi_single
    {seed : PencilSeed K α} {hubSel : α → Fin 3 → Option α} {v : α} {σ : Fin 3 → Fin 4} {d : Fin 4}
    (hσinj : Function.Injective σ) (hσd : ∀ i, σ i ≠ d)
    (hslot : ∀ i, hubSlotNormal seed hubSel v i = Pi.single (σ i) (1 : K)) :
    ∃ cc : K, cc ≠ 0 ∧ pencilChartPoint seed hubSel v = cc • (Pi.single d (1 : K) : Fin 4 → K) := by
  have h01 : σ 0 ≠ σ 1 := fun h => absurd (hσinj h) (by decide)
  have h02 : σ 0 ≠ σ 2 := fun h => absurd (hσinj h) (by decide)
  have h12 : σ 1 ≠ σ 2 := fun h => absurd (hσinj h) (by decide)
  obtain ⟨cc, hcc, hcross⟩ :=
    exists_smul_cross₃_pi_single (K := K) (hσd 0) (hσd 1) (hσd 2) h01 h02 h12
  exact ⟨cc, hcc, by rw [pencilChartPoint, hslot 0, hslot 1, hslot 2, hcross]⟩

end CombinatorialRigidity.Molecular
