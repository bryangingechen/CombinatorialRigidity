/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.Chart

/-!
# The pencil chart in coordinates, and a realization in the chart

Two parts of the proof of `lem:pencil-generic-steer` (`sec:main-component-statements`), on the chart
of `Chart.lean`.

The first writes the chart in coordinates. A point `q : α × Fin 4 × Fin 4 → K` gives the parameters
`PencilSeed.ofCoord q`: at each body `v`, `hubNormal v` is `q (v, 0, ·)`, and the padding vector `j`
of both `fillHub v` and `fillNbr v` is `q (v, j.succ, ·)`. For fixed selectors, the coordinates of
the points and normals of the chart, of the join of the points of two bodies, and of the forms
`annihRow` that vanish at that join are polynomials in `q`, as the coordinates of `cross₃` are
determinants (`cross₃_apply`). So are those of the rows of the chart's rigidity matrix, read through
an endpoint selector (`pencilRow`). A family of rows, of points or of normals that is linearly
independent at some `q₀` is independent at every non-root of a polynomial nonzero at `q₀`, a minor
of the matrix of its coordinates (`exists_polynomial_ne_zero_of_linearIndependent_at_reindex`); and
over an infinite field, finitely many polynomials, each nonzero at some point, have a common
non-root.

The second writes a given nondegenerate realization in the chart, up to a nonzero scalar at each
point, and at the normal of each body that is not a hub. At a body `v`, the normals of the closed
hub-neighbourhood are independent, orthogonal to the point of `v` and at most three; completed by
padding vectors to an independent triple orthogonal to the point, their `cross₃` is a nonzero
multiple of it. The normal of a body that is not a hub comes in the same way from the points of the
chart on its closed neighbourhood. `exists_pencilSeed_of_nondeg` (`Reseed.lean`) puts the two sides
together. The file also computes the `cross₃` of three standard basis vectors, for part (a) of
`lem:pencil-generic-steer` (`MainComponent/GenericSteer.lean`).

## Main definitions

* `PencilSeed.ofCoord`: the parameters of the chart at a point of `α × Fin 4 × Fin 4 → K`.
* `pencilChartPointPoly`, `pencilChartNormalPoly` and `pencilAnnihRowPoly`: the points and the
  normals of the chart, and the coordinates of its rows, as polynomials.
* `pencilRow`: the rows of the chart at a coordinate point, read through an endpoint selector.

## Main results

* `exists_polynomial_ne_zero_of_linearIndependent_pencilRow`,
  `exists_polynomial_ne_zero_of_linearIndependent_pencilChartPoint` and
  `exists_polynomial_ne_zero_of_linearIndependent_pencilChartNormal`: a family of rows, of points or
  of normals independent at one coordinate point is independent at every non-root of a polynomial
  nonzero there.
* `exists_common_seed_pencilRow_and_polynomials`: over an infinite field, rows independent at some
  `q₀` and finitely many polynomials, each nonzero at some point, are at one point independent and
  nonzero.
* `exists_hubSel_fillHub_of_isNondegPencilRealization` and
  `exists_nbrSel_fillNbr_of_isNondegPencilRealization`: the two sides of a realization in the chart.
-/

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K]
variable {α β : Type*}

/-! ## The chart as polynomials in its parameters

A point `q : α × Fin 4 × Fin 4 → K` gives the parameters `PencilSeed.ofCoord q`: its first factor is
the body, its second the vector, `0` for `hubNormal` and `j.succ` for the padding vector `j` of both
triples, and its third the coordinate. The variable at `(v, r, i)` is `pencilXPoly r v i`.

Each construction of the chart has a polynomial form, whose value at `q` is the construction at
`PencilSeed.ofCoord q`, as evaluation is a ring homomorphism and commutes with `Matrix.det`
(`RingHom.map_det`): `cross₃Poly`, by `cross₃_apply`, which writes the coordinate `i` of
`cross₃ x y z` as `det[x, y, z, e_i]`; the slots of the two selectors (`hubSlotNormalPoly`,
`nbrSlotPointPoly`); the points and the normals (`pencilChartPointPoly`, `pencilChartNormalPoly`);
the coordinates in `screwBasis 2` of the join of the points of two bodies, the `2 × 2` minors of
their coordinates (`pencilPointJoinPoly`); and the coordinates of the forms `annihRow` that vanish
at that join (`pencilAnnihRowPoly`), as `annihRowPoly` (`PanelLayer.lean`) gives them at the join of
two panels.

`pencilRow` is the family of rows `hingeRow u v (annihRow C t₁ t₂)`, where `(u, v)` are the bodies
an endpoint selector gives an edge and `C` is the join of their points: the chart's counterpart of
`PanelHingeFramework.normalRow` (`GenericLift/PanelGeneric.lean`). It reads no graph: at the
selector `G.endsOf` and an edge of `G`, it is a rigidity row of the chart's framework on `G`
(`pencilRow_mem_rigidityRows_of_mem_edgeSet`, `Steer.lean`). Its coordinates are the polynomials
`pencilAnnihRowPoly`, times `[u = a] − [v = a]` at the coordinates of a body `a`, so a subfamily
independent at some `q₀` is independent at every non-root of a polynomial nonzero at `q₀`
(`exists_polynomial_ne_zero_of_linearIndependent_pencilRow`). -/

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

/-- **Slot `slot` of `v`'s neighbour selector as a vector of polynomials** (a step of
`lem:pencil-generic-steer`): the point of the body in it (`pencilChartPointPoly`), or the variables
of the padding vector `slot` of `v` if it is empty; the form of `nbrSlotPoint`
(`nbrSlotPointPoly_eval`). These are the variables of `hubSlotNormalPoly`'s padding, as
`PencilSeed.ofCoord` gives `fillNbr` the coordinates of `fillHub`. -/
noncomputable def nbrSlotPointPoly (hubSel nbrSel : α → Fin 3 → Option α) (v : α) (slot : Fin 3) :
    Fin 4 → MvPolynomial (α × Fin 4 × Fin 4) K :=
  match nbrSel v slot with
  | some w => pencilChartPointPoly hubSel w
  | none => pencilXPoly slot.succ v

/-- **The value of `nbrSlotPointPoly`**: at `q`, the coordinate `i` of slot `slot` of `v`'s
neighbour selector at `PencilSeed.ofCoord q` (`nbrSlotPoint`): `pencilChartPointPoly_eval` at a
body, and at an empty slot the coordinate `q (v, slot.succ, i)`, which `PencilSeed.ofCoord` gives
`fillNbr v slot`. -/
theorem nbrSlotPointPoly_eval (hubSel nbrSel : α → Fin 3 → Option α) (v : α) (slot : Fin 3)
    (q : α × Fin 4 × Fin 4 → K) (i : Fin 4) :
    MvPolynomial.eval q (nbrSlotPointPoly hubSel nbrSel v slot i)
      = nbrSlotPoint (PencilSeed.ofCoord q) hubSel nbrSel v slot i := by
  simp only [nbrSlotPointPoly, nbrSlotPoint, PencilSeed.ofCoord]
  cases nbrSel v slot with
  | some w => exact pencilChartPointPoly_eval hubSel w q i
  | none => exact pencilXPoly_eval slot.succ v q i

/-- **`nbrSlotPointPoly_eval` for the whole vector**, the form in which `pencilChartNormalPoly_eval`
rewrites each of its three slots. -/
theorem nbrSlotPointPoly_eval_funext (hubSel nbrSel : α → Fin 3 → Option α) (v : α) (slot : Fin 3)
    (q : α × Fin 4 × Fin 4 → K) :
    (fun j => MvPolynomial.eval q (nbrSlotPointPoly hubSel nbrSel v slot j))
      = nbrSlotPoint (PencilSeed.ofCoord q) hubSel nbrSel v slot :=
  funext fun j => nbrSlotPointPoly_eval hubSel nbrSel v slot q j

open Classical in
/-- **The normal of the chart as a vector of polynomials** (a step of `lem:pencil-generic-steer`):
the variables of `hubNormal v` at a pencil hub `v`, and at any other body `cross₃Poly` of the three
slots of `v`'s neighbour selector (`nbrSlotPointPoly`); the form of `pencilChartNormal`
(`pencilChartNormalPoly_eval`). Whether `v` is a hub depends on `G` alone, so the test is the `if`
of `pencilChartNormal`. -/
noncomputable def pencilChartNormalPoly (hubSel nbrSel : α → Fin 3 → Option α) (G : Graph α β)
    (v : α) : Fin 4 → MvPolynomial (α × Fin 4 × Fin 4) K :=
  if G.PencilHub v then pencilXPoly 0 v
  else cross₃Poly (nbrSlotPointPoly hubSel nbrSel v 0) (nbrSlotPointPoly hubSel nbrSel v 1)
    (nbrSlotPointPoly hubSel nbrSel v 2)

/-- **The value of `pencilChartNormalPoly`**: at `q`, the coordinate `i` of the normal of the chart
at `PencilSeed.ofCoord q` (`pencilChartNormal`). Both sides test whether `v` is a hub. At a hub the
value is `q (v, 0, i)`, which `PencilSeed.ofCoord q` gives `hubNormal v`, and elsewhere
`cross₃Poly_eval` and `nbrSlotPointPoly_eval` give it. -/
theorem pencilChartNormalPoly_eval (hubSel nbrSel : α → Fin 3 → Option α) (G : Graph α β) (v : α)
    (q : α × Fin 4 × Fin 4 → K) (i : Fin 4) :
    MvPolynomial.eval q (pencilChartNormalPoly hubSel nbrSel G v i)
      = pencilChartNormal (PencilSeed.ofCoord q) hubSel nbrSel G v i := by
  rw [pencilChartNormalPoly, pencilChartNormal]
  split_ifs with hv
  · rw [pencilXPoly_eval]; rfl
  · rw [cross₃Poly_eval,
      nbrSlotPointPoly_eval_funext hubSel nbrSel v 0 q,
      nbrSlotPointPoly_eval_funext hubSel nbrSel v 1 q,
      nbrSlotPointPoly_eval_funext hubSel nbrSel v 2 q]

/-- **The join of the points of two bodies, in coordinates** (a step of `lem:pencil-generic-steer`):
for bodies `u`, `v` and a `2`-subset `t` of `Fin 4`, the `2 × 2` minor, at the columns of `t`, of
the matrix whose rows are the points of `u` and `v` (`pencilChartPointPoly`). Its value at `q` is
the coordinate at `t`, in `screwBasis 2`, of the join `extensor ![p_u, p_v]` of the points of the
chart (`pencilPointJoinPoly_eval`). The join lies in `⋀² K⁴`, so no `complementIso` enters, unlike
the panel layer's `panelSupportPoly` (`PanelLayer.lean`). -/
noncomputable def pencilPointJoinPoly (hubSel : α → Fin 3 → Option α) (u v : α)
    (t : Set.powersetCard (Fin 4) 2) : MvPolynomial (α × Fin 4 × Fin 4) K :=
  (Matrix.of fun i j : Fin 2 =>
      (![pencilChartPointPoly hubSel u, pencilChartPointPoly hubSel v] i)
        ((t : Finset (Fin 4)).orderEmbOfFin t.2 j)).det

/-- **The value of `pencilPointJoinPoly`**: at `q`, the coordinate at `t`, in `screwBasis 2`, of the
join of the points of `u` and `v` at `PencilSeed.ofCoord q`. The coordinates in `screwBasis 2` are
those in the basis of `⋀² K⁴` (`screwBasis_repr_apply`), where the coordinate at `t` of `ιMulti` of
two vectors is their minor at the columns of `t` (`exteriorPower.basis_repr_apply`,
`exteriorPower.ιMultiDual_apply_ιMulti`); evaluation commutes with the determinant, and
`pencilChartPointPoly_eval` gives each entry. The proof is that of `hingeExtensorPoly_eval`
(`GenericLift/HingeGeneric.lean`). -/
theorem pencilPointJoinPoly_eval (hubSel : α → Fin 3 → Option α) (u v : α)
    (q : α × Fin 4 × Fin 4 → K) (t : Set.powersetCard (Fin 4) 2) :
    MvPolynomial.eval q (pencilPointJoinPoly hubSel u v t)
      = (screwBasis 2).repr (ScrewSpace.mk
          (extensor ![pencilChartPoint (PencilSeed.ofCoord q) hubSel u,
            pencilChartPoint (PencilSeed.ofCoord q) hubSel v])
          (extensor_mem_exteriorPower _)) t := by
  rw [screwBasis_repr_apply]
  change MvPolynomial.eval q (pencilPointJoinPoly hubSel u v t)
      = ((Pi.basisFun K (Fin 4)).exteriorPower 2).repr
          (exteriorPower.ιMulti K 2 ![pencilChartPoint (PencilSeed.ofCoord q) hubSel u,
            pencilChartPoint (PencilSeed.ofCoord q) hubSel v]) t
  rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti, pencilPointJoinPoly,
    (MvPolynomial.eval q).map_det]
  congr 1
  ext i j
  simp only [Matrix.of_apply, Module.Basis.coord_apply, Pi.basisFun_repr,
    Set.powersetCard.ofFinEmbEquiv_symm_apply]
  fin_cases i
  · exact pencilChartPointPoly_eval hubSel u q _
  · exact pencilChartPointPoly_eval hubSel v q _

/-- **The coordinates of the forms that vanish at a join** (a step of `lem:pencil-generic-steer`):
`[t₂ = s] C_{t₁} − [t₁ = s] C_{t₂}`, with `C_t = pencilPointJoinPoly hubSel u v t`. Its value at `q`
is that of `annihRow C t₁ t₂` at the basis vector `screwBasis 2 s`, for `C` the join of the points
of `u` and `v` (`pencilAnnihRowPoly_eval`). It is `annihRowPoly` (`PanelLayer.lean`) with
`pencilPointJoinPoly` in place of `panelSupportPoly`. -/
noncomputable def pencilAnnihRowPoly (hubSel : α → Fin 3 → Option α) (u v : α)
    (t₁ t₂ s : Set.powersetCard (Fin 4) 2) : MvPolynomial (α × Fin 4 × Fin 4) K :=
  (if t₂ = s then pencilPointJoinPoly hubSel u v t₁ else 0)
    - (if t₁ = s then pencilPointJoinPoly hubSel u v t₂ else 0)

/-- **The value of `pencilAnnihRowPoly`**: at `q`, the value of `annihRow C t₁ t₂` at
`screwBasis 2 s`, for `C` the join of the points of `u` and `v` at `PencilSeed.ofCoord q`; the proof
of `annihRowPoly_eval`, with `pencilPointJoinPoly_eval`. -/
theorem pencilAnnihRowPoly_eval (hubSel : α → Fin 3 → Option α) (u v : α)
    (q : α × Fin 4 × Fin 4 → K) (t₁ t₂ s : Set.powersetCard (Fin 4) 2) :
    MvPolynomial.eval q (pencilAnnihRowPoly hubSel u v t₁ t₂ s) =
      annihRow (ScrewSpace.mk (extensor ![pencilChartPoint (PencilSeed.ofCoord q) hubSel u,
          pencilChartPoint (PencilSeed.ofCoord q) hubSel v]) (extensor_mem_exteriorPower _))
        t₁ t₂ (screwBasis 2 s) := by
  rw [pencilAnnihRowPoly, annihRow_apply, map_sub,
    Module.Basis.repr_self_apply (screwBasis 2) (i := s) t₂,
    Module.Basis.repr_self_apply (screwBasis 2) (i := s) t₁,
    apply_ite (MvPolynomial.eval q), apply_ite (MvPolynomial.eval q),
    map_zero, pencilPointJoinPoly_eval, pencilPointJoinPoly_eval, mul_ite, mul_one, mul_zero,
    mul_ite, mul_one, mul_zero]
  congr 1
  · rcases eq_or_ne t₂ s with h | h
    · rw [ite_eq_left h, ite_eq_left h.symm]
    · rw [ite_eq_right h, ite_eq_right fun h' => h h'.symm]
  · rcases eq_or_ne t₁ s with h | h
    · rw [ite_eq_left h, ite_eq_left h.symm]
    · rw [ite_eq_right h, ite_eq_right fun h' => h h'.symm]

/-- **The rows of the chart, read through an endpoint selector** (a step of
`lem:pencil-generic-steer`): for `ends : β → α × α` and a coordinate point `q`, the row at
`(e, t₁, t₂)` is `hingeRow u v (annihRow C t₁ t₂)`, where `(u, v) = ends e` and `C` is the join of
the points of `u` and `v` at `PencilSeed.ofCoord q`. It reads `ends` and `q` and no graph, as
`PanelHingeFramework.normalRow` does. At `G.endsOf` and an edge of `G`, it is the row `panelRow` of
the chart's framework on `G` (`pencilRow_eq_panelRow_pencilChartFramework`, `Steer.lean`). -/
noncomputable def pencilRow (hubSel : α → Fin 3 → Option α) (ends : β → α × α)
    (q : α × Fin 4 × Fin 4 → K)
    (i : β × Set.powersetCard (Fin 4) 2 × Set.powersetCard (Fin 4) 2) :
    Module.Dual K (α → ScrewSpace K 2) :=
  BodyHingeFramework.hingeRow (ends i.1).1 (ends i.1).2
    (annihRow (ScrewSpace.mk
        (extensor ![pencilChartPoint (PencilSeed.ofCoord q) hubSel (ends i.1).1,
          pencilChartPoint (PencilSeed.ofCoord q) hubSel (ends i.1).2])
        (extensor_mem_exteriorPower _))
      i.2.1 i.2.2)

/-- **Rows independent at `q₀` stay so off the zero set of a polynomial** (a step of
`lem:pencil-generic-steer`): if a subfamily of `pencilRow hubSel ends` is linearly independent at
`q₀`, there is a polynomial, nonzero at `q₀`, at whose every non-root it is independent. It is
`exists_polynomial_ne_zero_of_linearIndependent_at_reindex` for the forms on `α → ScrewSpace K 2`,
in the basis dual to `Pi.basis (fun _ => screwBasis 2)`: the coordinate at `(a, s)` of the row at
`(e, t₁, t₂)` is `pencilAnnihRowPoly` times `[u = a] − [v = a]`, for `(u, v) = ends e`
(`BodyHingeFramework.hingeRow_apply`, `pencilAnnihRowPoly_eval`), as in
`PanelHingeFramework.exists_isGenericNormals_abundance` for the rows of normals. -/
theorem exists_polynomial_ne_zero_of_linearIndependent_pencilRow [Finite α] [Finite β]
    (hubSel : α → Fin 3 → Option α) (ends : β → α × α)
    {q₀ : α × Fin 4 × Fin 4 → K}
    {s : Set (β × Set.powersetCard (Fin 4) 2 × Set.powersetCard (Fin 4) 2)}
    (h : LinearIndependent K fun i : s => pencilRow hubSel ends q₀ i) :
    ∃ Q : MvPolynomial (α × Fin 4 × Fin 4) K, MvPolynomial.eval q₀ Q ≠ 0 ∧
      ∀ q, MvPolynomial.eval q Q ≠ 0 →
        LinearIndependent K fun i : s => pencilRow hubSel ends q i := by
  classical
  have : Fintype α := Fintype.ofFinite α
  set B : Module.Basis (Σ _ : α, Set.powersetCard (Fin 4) 2) K (α → ScrewSpace K 2) :=
    Pi.basis (fun _ : α => screwBasis 2) with hB
  set φ : Module.Dual K (α → ScrewSpace K 2)
      ≃ₗ[K] ((Σ _ : α, Set.powersetCard (Fin 4) 2) → K) := B.dualBasis.equivFun with hφ
  have hcard : Fintype.card (Σ _ : α, Set.powersetCard (Fin 4) 2)
      = Module.finrank K (Module.Dual K (α → ScrewSpace K 2)) := by
    rw [Subspace.dual_finrank_eq, Module.finrank_eq_card_basis B]
  let e : Fin (Module.finrank K (Module.Dual K (α → ScrewSpace K 2)))
      ≃ (Σ _ : α, Set.powersetCard (Fin 4) 2) :=
    (Fintype.equivFinOfCardEq hcard).symm
  set g : (α × Fin 4 × Fin 4 → K)
      → (β × Set.powersetCard (Fin 4) 2 × Set.powersetCard (Fin 4) 2)
      → Module.Dual K (α → ScrewSpace K 2) :=
    fun q i => pencilRow hubSel ends q i with hg_def
  set c : (β × Set.powersetCard (Fin 4) 2 × Set.powersetCard (Fin 4) 2)
      → (Σ _ : α, Set.powersetCard (Fin 4) 2) → MvPolynomial (α × Fin 4 × Fin 4) K :=
    fun i j => ((if (ends i.1).1 = j.1 then (1 : K) else 0)
        - (if (ends i.1).2 = j.1 then 1 else 0))
      • pencilAnnihRowPoly hubSel (ends i.1).1 (ends i.1).2 i.2.1 i.2.2 j.2 with hc_def
  have hg : ∀ q i j, φ (g q i) j = MvPolynomial.eval q (c i j) := by
    intro q i j
    obtain ⟨a, t⟩ := j
    rw [hφ, Module.Basis.dualBasis_equivFun, hg_def, hc_def, hB, Pi.basis_apply]
    change pencilRow hubSel ends q i (Pi.single a (screwBasis 2 t)) = _
    rw [pencilRow, BodyHingeFramework.hingeRow_apply, MvPolynomial.smul_eval,
      pencilAnnihRowPoly_eval, Pi.single_apply, Pi.single_apply]
    by_cases hu : (ends i.1).1 = a <;> by_cases hv : (ends i.1).2 = a <;>
      simp only [hu, hv, ite_true, ite_false, sub_zero, zero_sub, sub_self, map_zero,
        map_neg, one_mul, neg_mul, zero_mul]
  obtain ⟨Q, hQ0, hQ⟩ :=
    exists_polynomial_ne_zero_of_linearIndependent_at_reindex e g c φ hg (p₀ := q₀) (s := s) h
  exact ⟨Q, hQ0, hQ⟩

/-! ## Independent points and normals, and a common non-root

The forms of `exists_polynomial_ne_zero_of_linearIndependent_pencilRow` for the points and the
normals of the chart: a family independent at some `q₀` is independent at every non-root of a
polynomial nonzero at `q₀`, by `exists_polynomial_ne_zero_of_linearIndependent_at_reindex` in the
coordinates of `K⁴` (`pencilChartPointPoly_eval`, `pencilChartNormalPoly_eval`). These need no
infinite field. Over an infinite field, finitely many polynomials, each nonzero at some point, have
a common non-root (`exists_common_eval_ne_zero_of_forall_exists`), at which rows independent at one
point remain independent (`exists_common_seed_pencilRow_and_polynomials`). As in the proof of
`lem:pencil-generic-steer`, each condition then holds at one point. -/

/-- **Points of the chart independent at `q₀` stay so off the zero set of a polynomial** (a step of
`lem:pencil-generic-steer`): for `ends : ι → α`, with `ι` finite, if the points of the chart at
`ends i`, for `i` in a set `s`, are linearly independent at `q₀`, there is a polynomial, nonzero at
`q₀`, at whose every non-root they are independent. `exists_isNondegPencilRealization_steer`
(`MainComponent/GenericSteer.lean`) and `exists_common_seed_linearIndepOn_pencilChartPoint`
(`Steer.lean`) use it at `ends := id`. -/
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

/-- **Normals of the chart independent at `q₀` stay so off the zero set of a polynomial** (a step of
`lem:pencil-generic-steer`): the form of
`exists_polynomial_ne_zero_of_linearIndependent_pencilChartPoint` for the normals of the chart on
`G` (`pencilChartNormalPoly_eval`). `exists_isNondegPencilRealization_steer` uses it at
`ends := id`, for the independence of the normals on each of its sets. -/
theorem exists_polynomial_ne_zero_of_linearIndependent_pencilChartNormal
    {ι : Type*} [Finite ι] (hubSel nbrSel : α → Fin 3 → Option α) (G : Graph α β) (ends : ι → α)
    {q₀ : α × Fin 4 × Fin 4 → K} {s : Set ι}
    (h : LinearIndependent K
      (fun i : s => pencilChartNormal (PencilSeed.ofCoord q₀) hubSel nbrSel G (ends i))) :
    ∃ Q : MvPolynomial (α × Fin 4 × Fin 4) K, MvPolynomial.eval q₀ Q ≠ 0 ∧
      ∀ q, MvPolynomial.eval q Q ≠ 0 →
        LinearIndependent K
          (fun i : s => pencilChartNormal (PencilSeed.ofCoord q) hubSel nbrSel G (ends i)) :=
  exists_polynomial_ne_zero_of_linearIndependent_at_reindex (finCongr (Module.finrank_fin_fun K))
    (fun q i => pencilChartNormal (PencilSeed.ofCoord q) hubSel nbrSel G (ends i))
    (fun i j => pencilChartNormalPoly hubSel nbrSel G (ends i) j)
    (LinearEquiv.refl K (Fin 4 → K))
    (fun q i j => (pencilChartNormalPoly_eval hubSel nbrSel G (ends i) q j).symm)
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

/-- **Independent rows and finitely many polynomials at one point** (a step of
`lem:pencil-generic-steer`): over an infinite field, if a subfamily of `pencilRow hubSel ends` is
linearly independent at `q₀`, and each of finitely many polynomials `P i` is nonzero at some point,
then at some point the subfamily is independent and every `P i` is nonzero. The polynomial of
`exists_polynomial_ne_zero_of_linearIndependent_pencilRow`, nonzero at `q₀`, joins the `P i`
(indexed by `Unit ⊕ ι`), and `exists_common_eval_ne_zero_of_forall_exists` gives the point.
`exists_isNondegPencilRealization_steer` uses it for rows of the deficiency rank and the polynomials
of its other conditions. -/
theorem exists_common_seed_pencilRow_and_polynomials [Finite α] [Finite β] [Infinite K]
    (hubSel : α → Fin 3 → Option α) (ends : β → α × α)
    {q₀ : α × Fin 4 × Fin 4 → K}
    {s : Set (β × Set.powersetCard (Fin 4) 2 × Set.powersetCard (Fin 4) 2)}
    (hLI : LinearIndependent K fun i : s => pencilRow hubSel ends q₀ i)
    {ι : Type*} [Finite ι] (P : ι → MvPolynomial (α × Fin 4 × Fin 4) K)
    (hP : ∀ i, ∃ q, MvPolynomial.eval q (P i) ≠ 0) :
    ∃ q : α × Fin 4 × Fin 4 → K,
      LinearIndependent K (fun i : s => pencilRow hubSel ends q i) ∧
      ∀ i, MvPolynomial.eval q (P i) ≠ 0 := by
  obtain ⟨Q0, hQ00, hQ0⟩ := exists_polynomial_ne_zero_of_linearIndependent_pencilRow hubSel ends hLI
  obtain ⟨q, hq⟩ := exists_common_eval_ne_zero_of_forall_exists
    (Sum.elim (fun _ : Unit => Q0) P)
    (fun x => match x with
      | Sum.inl _ => ⟨q₀, hQ00⟩
      | Sum.inr i => hP i)
  exact ⟨q, hQ0 q (hq (Sum.inl ())), fun i => hq (Sum.inr i)⟩

/-! ## `cross₃` of three independent vectors orthogonal to a point

To write a nondegenerate realization in the chart (the converse in the proof of
`lem:pencil-generic-steer`), the point of each body is written as `cross₃` of the normals of its
closed hub-neighbourhood, which are independent, orthogonal to the point and at most three,
completed by padding vectors. With three normals no padding is left: `cross₃` of three independent
vectors and a nonzero vector orthogonal to them lie in the space of the vectors orthogonal to the
three, of dimension `1`, so each is a nonzero multiple of the other
(`exists_smul_cross₃_eq_of_linearIndependent`). So the chart reproduces a realization up to a
nonzero scalar at each point, which, as that proof notes, changes neither its nondegeneracy nor the
line of any hinge. With fewer normals the point is reached exactly (the section after next). -/

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
(`exists_smul_pencilChartPoint_of_hubSlotNormal_eq_pi_single`), as part (a) of
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

/-! ## A point as `cross₃` exactly, when a padding vector is free

With at most two normals at a body, a padding vector is free, and the point is reached exactly. For
independent `n₁, n₂`, the vectors `cross₃ n₁ n₂ z` are those orthogonal to both
(`range_cross₃L_eq_perp`), so each of these is reached
(`exists_cross₃_eq_of_linearIndependent_pair_of_dotProduct_eq_zero`). For a nonzero `n` orthogonal
to a nonzero `q`, two vectors, each outside the span of those before it, complete `n` to an
independent triple orthogonal to `q`, whose `cross₃` is a nonzero multiple of `q`, and rescaling the
last vector gives `q` (`exists_cross₃_eq_of_ne_zero_of_dotProduct_eq_zero`). With no normal, any
nonzero vector orthogonal to `q` serves as `n` (`exists_cross₃_eq_of_ne_zero`). -/

/-- **A vector orthogonal to two independent vectors is their `cross₃` with a third** (a step of
`lem:pencil-generic-steer`): for independent `n₁, n₂` and `q` orthogonal to both,
`cross₃ n₁ n₂ z = q` for some `z`, as `q` lies in the space of the vectors orthogonal to both, the
range of `cross₃ n₁ n₂ ·` (`range_cross₃L_eq_perp`). -/
theorem exists_cross₃_eq_of_linearIndependent_pair_of_dotProduct_eq_zero
    {n₁ n₂ q : Fin 4 → K} (hLI : LinearIndependent K ![n₁, n₂])
    (hq1 : q ⬝ᵥ n₁ = 0) (hq2 : q ⬝ᵥ n₂ = 0) :
    ∃ z : Fin 4 → K, cross₃ n₁ n₂ z = q := by
  have hmem : q ∈ (⨅ j : Fin 2, LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip (![n₁, n₂] j))
      : Submodule K (Fin 4 → K)) := by
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply,
      piBasisFun_toDual_eq_dotProduct]
    intro j
    fin_cases j
    · simpa using hq1
    · simpa using hq2
  rw [← range_cross₃L_eq_perp n₁ n₂ hLI] at hmem
  obtain ⟨z, hz⟩ := hmem
  exact ⟨z, hz⟩

/-- **A nonzero vector orthogonal to a nonzero `n` is `cross₃` of `n` and two more** (a step of
`lem:pencil-generic-steer` and `lem:pencil-generic-pendant-triangle`): for `n ≠ 0` and `q ≠ 0`
orthogonal to it, there are `y`, `z` with `![n, y, z]` linearly independent and `cross₃ n y z = q`.
The vectors orthogonal to `q` form a space of dimension `3` (`finrank_toDualPerp_single_eq`) that
holds `n`; two vectors of it, each outside the span of those before it, complete `n` to an
independent triple there, whose `cross₃` is `c • q` with `c ≠ 0`
(`exists_smul_cross₃_eq_of_linearIndependent`); and multiplying the last vector by `c⁻¹` gives `q`
(`cross₃_smul_thd`) and keeps the triple independent. -/
theorem exists_cross₃_eq_of_ne_zero_of_dotProduct_eq_zero {n q : Fin 4 → K}
    (hn : n ≠ 0) (hq : q ≠ 0) (hqn : q ⬝ᵥ n = 0) :
    ∃ y z : Fin 4 → K, LinearIndependent K ![n, y, z] ∧ cross₃ n y z = q := by
  set V : Submodule K (Fin 4 → K) := LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip q) with hV
  have hmemV : ∀ x : Fin 4 → K, x ∈ V ↔ x ⬝ᵥ q = 0 := by
    intro x
    simp only [hV, LinearMap.mem_ker, LinearMap.flip_apply, piBasisFun_toDual_eq_dotProduct]
  have hVdim : Module.finrank K V = 3 := finrank_toDualPerp_single_eq hq
  have hnV : n ∈ V := (hmemV n).2 (by rw [dotProduct_comm]; exact hqn)
  have hpick : ∀ S : Submodule K (Fin 4 → K), Module.finrank K S < Module.finrank K V →
      ∃ y0, y0 ∈ V ∧ y0 ∉ S := by
    intro S hlt
    by_contra hcon
    push Not at hcon
    have hle : V ≤ S := fun x hx => hcon x hx
    have := Submodule.finrank_mono hle
    omega
  have hnLI : LinearIndependent K (![n] : Fin 1 → Fin 4 → K) := by
    rw [linearIndependent_unique_iff]; simpa using hn
  obtain ⟨y0, hy0V, hy0⟩ := hpick (Submodule.span K (Set.range (![n] : Fin 1 → Fin 4 → K)))
    (by rw [finrank_span_eq_card hnLI, hVdim]; simp)
  have hny0LI : LinearIndependent K (![n, y0] : Fin 2 → Fin 4 → K) := by
    have hsnoc := linearIndependent_finSnoc.mpr ⟨hnLI, hy0⟩
    rwa [show Fin.snoc (![n] : Fin 1 → Fin 4 → K) y0 = ![n, y0] from by
      funext i; fin_cases i <;> simp] at hsnoc
  obtain ⟨z0, hz0V, hz0⟩ := hpick (Submodule.span K (Set.range (![n, y0] : Fin 2 → Fin 4 → K)))
    (by rw [finrank_span_eq_card hny0LI, hVdim]; simp)
  have hnyzLI : LinearIndependent K (![n, y0, z0] : Fin 3 → Fin 4 → K) := by
    have hsnoc := linearIndependent_finSnoc.mpr ⟨hny0LI, hz0⟩
    rwa [show Fin.snoc (![n, y0] : Fin 2 → Fin 4 → K) z0 = ![n, y0, z0] from by
      funext i; fin_cases i <;> simp] at hsnoc
  have hq_y0 : q ⬝ᵥ y0 = 0 := by rw [dotProduct_comm]; exact (hmemV y0).1 hy0V
  have hq_z0 : q ⬝ᵥ z0 = 0 := by rw [dotProduct_comm]; exact (hmemV z0).1 hz0V
  obtain ⟨c, hcne, hc⟩ := exists_smul_cross₃_eq_of_linearIndependent hnyzLI hq hqn hq_y0 hq_z0
  refine ⟨y0, c⁻¹ • z0, ?_, ?_⟩
  · have hw : LinearIndependent K
        ((![(1 : Kˣ), 1, Units.mk0 c⁻¹ (inv_ne_zero hcne)] : Fin 3 → Kˣ) •
          (![n, y0, z0] : Fin 3 → Fin 4 → K)) := hnyzLI.units_smul _
    have heq : ((![(1 : Kˣ), 1, Units.mk0 c⁻¹ (inv_ne_zero hcne)] : Fin 3 → Kˣ) •
        (![n, y0, z0] : Fin 3 → Fin 4 → K)) = ![n, y0, c⁻¹ • z0] := by
      funext i; fin_cases i <;> simp [Units.smul_def]
    rwa [heq] at hw
  · rw [cross₃_smul_thd, hc, inv_smul_smul₀ hcne]

/-- **A nonzero vector is `cross₃` of an independent triple** (a step of
`lem:pencil-generic-steer`): for `q ≠ 0`, `cross₃ x y z = q` for some independent `x, y, z`. Take
for `x` a nonzero vector orthogonal to `q`, which exists as these form a space of dimension `3`
(`finrank_toDualPerp_single_eq`), and apply `exists_cross₃_eq_of_ne_zero_of_dotProduct_eq_zero`.
Writing a realization in the chart uses it at a body whose closed hub-neighbourhood is empty. -/
theorem exists_cross₃_eq_of_ne_zero {q : Fin 4 → K} (hq : q ≠ 0) :
    ∃ x y z : Fin 4 → K, LinearIndependent K ![x, y, z] ∧ cross₃ x y z = q := by
  set V : Submodule K (Fin 4 → K) := LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip q) with hV
  have hVdim : Module.finrank K V = 3 := finrank_toDualPerp_single_eq hq
  obtain ⟨x, hxne⟩ := Module.finrank_pos_iff_exists_ne_zero.1 (show 0 < Module.finrank K V by omega)
  have hxne' : (x : Fin 4 → K) ≠ 0 := fun h => hxne (Submodule.coe_eq_zero.1 h)
  have hxq : q ⬝ᵥ (x : Fin 4 → K) = 0 := by
    rw [dotProduct_comm]
    simpa only [hV, LinearMap.mem_ker, LinearMap.flip_apply,
      piBasisFun_toDual_eq_dotProduct] using x.2
  obtain ⟨y, z, hLI, hxyz⟩ :=
    exists_cross₃_eq_of_ne_zero_of_dotProduct_eq_zero hxne' hq hxq
  exact ⟨(x : Fin 4 → K), y, z, hLI, hxyz⟩

/-! ## A realization in the chart: the hub selector and the points

The points of a nondegenerate realization in the chart. At each body `v`
(`exists_hubSlotOf_isNondegPencilRealization`), a selector `sel` of the closed hub-neighbourhood and
padding vectors `fill` make the three slots `hubSlotOf normal sel fill i` independent and, when
`v ∈ V(G)`, their `cross₃` a nonzero multiple of the point of `v`. There the closed
hub-neighbourhood has at most three members
(`ncard_closedHubNbhd_le_three_of_isNondegPencilRealization`, `Motive.lean`), and each number of
members has its lemma: `exists_cross₃_eq_of_ne_zero`,
`exists_cross₃_eq_of_ne_zero_of_dotProduct_eq_zero` and
`exists_cross₃_eq_of_linearIndependent_pair_of_dotProduct_eq_zero`, with the scalar `1`, and
`exists_smul_cross₃_eq_of_linearIndependent`. At a body outside `V(G)` the closed hub-neighbourhood
is empty, and an independent triple fills the three slots.

Choosing these at every body (`exists_hubSel_fillHub_of_isNondegPencilRealization`) gives the
selector `hubSel` and the padding `fillHub` of the chart, whatever its `fillNbr`: the slots of
`hubSel` at the parameters `⟨normal, fillHub, fillNbr⟩` are those of `hubSlotOf` by definition.
`exists_pencilSeed_of_nondeg_of_selectors` (`Reseed.lean`) does the same at any given selectors. -/

/-- **Slot `i` of a selector at one body** (a step of `lem:pencil-generic-steer`): `normal w` if
`sel` puts `w` in slot `i`, and `fill i` if it leaves the slot empty. At the parameters
`⟨normal, fillHub, fillNbr⟩`, slot `i` of `hubSel v` (`hubSlotNormal`) is
`hubSlotOf normal (hubSel v) (fillHub v) i` by definition, for any `fillNbr`; the neighbour side
uses it with the points of the chart in place of `normal`
(`exists_nbrSlotOf_isNondegPencilRealization`). -/
def hubSlotOf (normal : α → Fin 4 → K) (sel : Fin 3 → Option α)
    (fill : Fin 3 → Fin 4 → K) (i : Fin 3) : Fin 4 → K :=
  match sel i with
  | some w => normal w
  | none => fill i

/-- **The points of a realization in the chart, at one body** (a step of
`lem:pencil-generic-steer`): for a nondegenerate realization of `G` and a body `v`, there are a
selector `sel` of `G.closedHubNbhd v` and padding vectors `fill` such that the three vectors
`hubSlotOf normal sel fill i` are linearly independent and, if `v ∈ V(G)`, their `cross₃` is a
nonzero multiple of `point v`. The proof takes the number of members of `G.closedHubNbhd v`, at most
three, case by case, as the section header says. -/
theorem exists_hubSlotOf_isNondegPencilRealization [Finite α]
    {G : Graph α β} {F : BodyHingeFramework K 2 α β} {normal point : α → Fin 4 → K}
    (h : IsNondegPencilRealization G F normal point) (v : α) :
    ∃ (sel : Fin 3 → Option α) (fill : Fin 3 → Fin 4 → K),
      IsFin3SelectorOf (G.closedHubNbhd v) sel ∧
      LinearIndependent K ![hubSlotOf normal sel fill 0, hubSlotOf normal sel fill 1,
        hubSlotOf normal sel fill 2] ∧
      (v ∈ V(G) → ∃ c : K, c ≠ 0 ∧
        cross₃ (hubSlotOf normal sel fill 0) (hubSlotOf normal sel fill 1)
          (hubSlotOf normal sel fill 2) = c • point v) := by
  by_cases hv : v ∈ V(G)
  · have hpt_ne : point v ≠ 0 := h.1.2.1 v hv
    have hLI : LinearIndepOn K normal (G.closedHubNbhd v) := h.2.2.1 v hv
    have hcard : (G.closedHubNbhd v).ncard ≤ 3 :=
      ncard_closedHubNbhd_le_three_of_isNondegPencilRealization h hv
    have hfin : (G.closedHubNbhd v).Finite := Set.toFinite _
    have hcases : (G.closedHubNbhd v).ncard = 0 ∨ (G.closedHubNbhd v).ncard = 1 ∨
        (G.closedHubNbhd v).ncard = 2 ∨ (G.closedHubNbhd v).ncard = 3 := by omega
    rcases hcases with h0 | h1 | h2 | h3
    · obtain ⟨x, y, z, hLI3, hxyz⟩ := exists_cross₃_eq_of_ne_zero hpt_ne
      refine ⟨fun _ => none, ![x, y, z], ⟨?_, ?_, ?_⟩, ?_, fun _ => ⟨1, one_ne_zero, ?_⟩⟩
      · intro i w hi; simp at hi
      · intro w hw; rw [Set.ncard_eq_zero hfin] at h0; rw [h0] at hw; exact absurd hw (by simp)
      · intro i j w hi; simp at hi
      · change LinearIndependent K
          ![(![x,y,z] : Fin 3 → Fin 4 → K) 0, (![x,y,z] : Fin 3 → Fin 4 → K) 1,
            (![x,y,z] : Fin 3 → Fin 4 → K) 2]
        simpa using hLI3
      · change cross₃ ((![x,y,z] : Fin 3 → Fin 4 → K) 0) ((![x,y,z] : Fin 3 → Fin 4 → K) 1)
          ((![x,y,z] : Fin 3 → Fin 4 → K) 2) = (1:K) • point v
        simpa using hxyz
    · obtain ⟨a, heq⟩ := Set.ncard_eq_one.mp h1
      have hna : normal a ≠ 0 := by rw [heq] at hLI; exact (linearIndepOn_singleton_iff K).mp hLI
      have hqn : point v ⬝ᵥ normal a = 0 :=
        dotProduct_point_eq_zero_of_mem_closedHubNbhd h hv (heq ▸ rfl)
      obtain ⟨y, z, hLIyz, hxyz⟩ := exists_cross₃_eq_of_ne_zero_of_dotProduct_eq_zero hna hpt_ne hqn
      refine ⟨![some a, none, none], ![0, y, z], ⟨?_, ?_, ?_⟩, ?_, fun _ => ⟨1, one_ne_zero, ?_⟩⟩
      · intro i w hi; fin_cases i <;> simp_all
      · intro w hw; rw [heq] at hw
        simp only [Set.mem_singleton_iff] at hw; exact ⟨0, by simp [hw]⟩
      · intro i j w hi hj; fin_cases i <;> fin_cases j <;> simp_all
      · have heqf : (![hubSlotOf normal ![some a, none, none] ![0,y,z] 0,
            hubSlotOf normal ![some a, none, none] ![0,y,z] 1,
            hubSlotOf normal ![some a, none, none] ![0,y,z] 2] : Fin 3 → Fin 4 → K)
            = ![normal a, y, z] := by funext i; fin_cases i <;> rfl
        rw [heqf]; exact hLIyz
      · have hh0 : hubSlotOf normal ![some a, none, none] ![0,y,z] 0 = normal a := rfl
        have hh1 : hubSlotOf normal ![some a, none, none] ![0,y,z] 1 = y := rfl
        have hh2 : hubSlotOf normal ![some a, none, none] ![0,y,z] 2 = z := rfl
        rw [hh0, hh1, hh2, one_smul]
        exact hxyz
    · obtain ⟨x, y, hxy, heq⟩ := Set.ncard_eq_two.mp h2
      have hLIxy : LinearIndependent K ![normal x, normal y] := by
        rw [LinearIndependent.pair_iff]
        exact (LinearIndepOn.pair_iff normal hxy).mp (heq ▸ hLI)
      have hqx : point v ⬝ᵥ normal x = 0 :=
        dotProduct_point_eq_zero_of_mem_closedHubNbhd h hv (heq ▸ Set.mem_insert x {y})
      have hqy : point v ⬝ᵥ normal y = 0 :=
        dotProduct_point_eq_zero_of_mem_closedHubNbhd h hv (heq ▸ Set.mem_insert_of_mem x rfl)
      obtain ⟨z, hxyz⟩ :=
        exists_cross₃_eq_of_linearIndependent_pair_of_dotProduct_eq_zero hLIxy hqx hqy
      have hz_ne : cross₃ (normal x) (normal y) z ≠ 0 := hxyz ▸ hpt_ne
      have hLI3 : LinearIndependent K ![normal x, normal y, z] :=
        (cross₃_ne_zero_iff_linearIndependent _ _ _).mp hz_ne
      refine ⟨![some x, some y, none], ![0, 0, z], ⟨?_, ?_, ?_⟩, ?_, fun _ => ⟨1, one_ne_zero, ?_⟩⟩
      · intro i w hi; fin_cases i <;> simp_all
      · intro w hw; rw [heq] at hw
        rcases hw with rfl | rfl
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
      · intro i j w hi hj; fin_cases i <;> fin_cases j <;> simp_all
      · have heqf : (![hubSlotOf normal ![some x, some y, none] ![0,0,z] 0,
            hubSlotOf normal ![some x, some y, none] ![0,0,z] 1,
            hubSlotOf normal ![some x, some y, none] ![0,0,z] 2] : Fin 3 → Fin 4 → K)
            = ![normal x, normal y, z] := by funext i; fin_cases i <;> rfl
        rw [heqf]; exact hLI3
      · have hh0 : hubSlotOf normal ![some x, some y, none] ![0,0,z] 0 = normal x := rfl
        have hh1 : hubSlotOf normal ![some x, some y, none] ![0,0,z] 1 = normal y := rfl
        have hh2 : hubSlotOf normal ![some x, some y, none] ![0,0,z] 2 = z := rfl
        rw [hh0, hh1, hh2, one_smul]
        exact hxyz
    · obtain ⟨x, y, z, hxy, hxz, hyz, heq⟩ := Set.ncard_eq_three.mp h3
      have hLI3 : LinearIndependent K ![normal x, normal y, normal z] :=
        linearIndependent_triple_of_linearIndepOn normal hxy hxz hyz (heq ▸ hLI)
      have hqx : point v ⬝ᵥ normal x = 0 :=
        dotProduct_point_eq_zero_of_mem_closedHubNbhd h hv
          (heq ▸ (by simp : x ∈ ({x,y,z}:Set α)))
      have hqy : point v ⬝ᵥ normal y = 0 :=
        dotProduct_point_eq_zero_of_mem_closedHubNbhd h hv
          (heq ▸ (by simp : y ∈ ({x,y,z}:Set α)))
      have hqz : point v ⬝ᵥ normal z = 0 :=
        dotProduct_point_eq_zero_of_mem_closedHubNbhd h hv
          (heq ▸ (by simp : z ∈ ({x,y,z}:Set α)))
      obtain ⟨c, hc, hcxyz⟩ := exists_smul_cross₃_eq_of_linearIndependent hLI3 hpt_ne hqx hqy hqz
      refine ⟨![some x, some y, some z], ![0, 0, 0], ⟨?_, ?_, ?_⟩, ?_, fun _ => ⟨c, hc, ?_⟩⟩
      · intro i w hi; fin_cases i <;> simp_all
      · intro w hw; rw [heq] at hw
        rcases hw with rfl | rfl | rfl
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
        · exact ⟨2, rfl⟩
      · intro i j w hi hj; fin_cases i <;> fin_cases j <;> simp_all
      · have heqf : (![hubSlotOf normal ![some x, some y, some z] ![0,0,0] 0,
            hubSlotOf normal ![some x, some y, some z] ![0,0,0] 1,
            hubSlotOf normal ![some x, some y, some z] ![0,0,0] 2] : Fin 3 → Fin 4 → K)
            = ![normal x, normal y, normal z] := by funext i; fin_cases i <;> rfl
        rw [heqf]; exact hLI3
      · have hh0 : hubSlotOf normal ![some x, some y, some z] ![0,0,0] 0 = normal x := rfl
        have hh1 : hubSlotOf normal ![some x, some y, some z] ![0,0,0] 1 = normal y := rfl
        have hh2 : hubSlotOf normal ![some x, some y, some z] ![0,0,0] 2 = normal z := rfl
        rw [hh0, hh1, hh2]
        exact hcxyz
  · have hxne : (![1,0,0,0] : Fin 4 → K) ≠ 0 := by
      intro heq0; have := congr_fun heq0 0; simp at this
    obtain ⟨x, y, z, hLI3, _⟩ := exists_cross₃_eq_of_ne_zero hxne
    refine ⟨fun _ => none, ![x, y, z], ⟨?_, ?_, ?_⟩, ?_, fun hcon => absurd hcon hv⟩
    · intro i w hi; simp at hi
    · intro w hw
      have hempty : G.closedHubNbhd v = ∅ := by
        ext w
        simp only [Graph.closedHubNbhd, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨hPencilHub, rfl | ⟨e, hlink⟩⟩
        · exact hv hPencilHub.1
        · exact hv hlink.left_mem
      rw [hempty] at hw; exact absurd hw (by simp)
    · intro i j w hi; simp at hi
    · change LinearIndependent K
        ![(![x,y,z] : Fin 3 → Fin 4 → K) 0, (![x,y,z] : Fin 3 → Fin 4 → K) 1,
          (![x,y,z] : Fin 3 → Fin 4 → K) 2]
      simpa using hLI3

/-- **The points of a realization in the chart** (a step of `lem:pencil-generic-steer`): for a
nondegenerate realization of `G`, there are a hub selector `hubSel` and padding `fillHub` such that
`hubSel v` lists `G.closedHubNbhd v` at every body, and, for every `fillNbr`, at the parameters
`⟨normal, fillHub, fillNbr⟩`, the three slots of `hubSel v` are independent at every body and the
point of each `v ∈ V(G)` is a nonzero multiple of `point v`: the first and third conditions of
`PencilChartWF`, and the points reproduced up to scalars. `choose` turns
`exists_hubSlotOf_isNondegPencilRealization` into the two functions. `exists_pencilSeed_of_nondeg`
(`Reseed.lean`) uses it with the neighbour side,
`exists_nbrSel_fillNbr_of_isNondegPencilRealization`. -/
theorem exists_hubSel_fillHub_of_isNondegPencilRealization [Finite α]
    {G : Graph α β} {F : BodyHingeFramework K 2 α β} {normal point : α → Fin 4 → K}
    (h : IsNondegPencilRealization G F normal point) :
    ∃ (hubSel : α → Fin 3 → Option α) (fillHub : α → Fin 3 → Fin 4 → K),
      (∀ v, IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v)) ∧
      ∀ fillNbr : α → Fin 3 → Fin 4 → K,
        (∀ v, LinearIndependent K
          ![hubSlotNormal ⟨normal, fillHub, fillNbr⟩ hubSel v 0,
            hubSlotNormal ⟨normal, fillHub, fillNbr⟩ hubSel v 1,
            hubSlotNormal ⟨normal, fillHub, fillNbr⟩ hubSel v 2]) ∧
        (∀ v ∈ V(G), ∃ c : K, c ≠ 0 ∧
          pencilChartPoint ⟨normal, fillHub, fillNbr⟩ hubSel v = c • point v) := by
  choose hubSel fillHub hsel hLI hpt using fun v => exists_hubSlotOf_isNondegPencilRealization h v
  exact ⟨hubSel, fillHub, hsel, fun fillNbr => ⟨fun v => hLI v, fun v hv => hpt v hv⟩⟩

/-! ## A realization in the chart: the neighbour selector and the normals

The normals of a nondegenerate realization in the chart, at the bodies that are not hubs; at a hub
the normal of the chart is `hubNormal` (`pencilChartNormal_of_pencilHub`), which
`exists_pencilSeed_of_nondeg` sets to the normal of the realization. They come from the points of
the chart already chosen, not from those of the realization, as the slots `nbrSlotPoint` of
`pencilChartNormal` hold points of the chart. So the step at one body
(`exists_nbrSlotOf_isNondegPencilRealization`) takes any family `pt` of nonzero vectors with `pt w`
a nonzero multiple of `point w` at each `w ∈ V(G)`. At `v ∈ V(G)` that is not a hub, the points of
the closed neighbourhood are independent, by nondegeneracy, and so are their multiples
(`LinearIndependent.units_smul`); they are orthogonal to the normal of `v`
(`dotProduct_normal_eq_zero_of_mem_closedNbhd`, `Motive.lean`), and there are one to three of them
(`ncard_closedNbhd_le_three_of_not_pencilHub`; `v` is one), so a lemma above gives a nonzero
multiple of `normal v`. At `v ∉ V(G)` the closed neighbourhood is `{v}`, and an independent triple
that starts with `pt v` fills the slots (`exists_linearIndependent_triple_of_ne_zero`).

Choosing these at every body (`exists_nbrSel_fillNbr_of_isNondegPencilRealization`), with `pt` the
points of the hub side, gives the neighbour selector `nbrSel` and the padding `fillNbr`. -/

/-- **A nonzero vector of `K⁴` starts an independent triple** (a step of
`lem:pencil-generic-steer`): for `n ≠ 0`, there are `y`, `z` with `![n, y, z]` linearly independent:
`y` outside the span of `n`, of dimension `1`, and `z` outside that of `n` and `y`, of dimension
`2`, both less than `4`. `exists_nbrSlotOf_isNondegPencilRealization` uses it at a body outside
`V(G)`. -/
theorem exists_linearIndependent_triple_of_ne_zero {n : Fin 4 → K} (hn : n ≠ 0) :
    ∃ y z : Fin 4 → K, LinearIndependent K ![n, y, z] := by
  have hnLI : LinearIndependent K (![n] : Fin 1 → Fin 4 → K) := by
    rw [linearIndependent_unique_iff]; simpa using hn
  obtain ⟨y, hy⟩ :
      ∃ y : Fin 4 → K, y ∉ Submodule.span K (Set.range (![n] : Fin 1 → Fin 4 → K)) := by
    by_contra hcon
    push Not at hcon
    have htop : Submodule.span K (Set.range (![n] : Fin 1 → Fin 4 → K)) = ⊤ :=
      Submodule.eq_top_iff'.mpr hcon
    have h1 : Module.finrank K
        (Submodule.span K (Set.range (![n] : Fin 1 → Fin 4 → K))) = 1 := by
      rw [finrank_span_eq_card hnLI]; simp
    rw [htop, finrank_top, Module.finrank_fin_fun] at h1
    omega
  have hnyLI : LinearIndependent K (![n, y] : Fin 2 → Fin 4 → K) := by
    have hsnoc := linearIndependent_finSnoc.mpr ⟨hnLI, hy⟩
    rwa [show Fin.snoc (![n] : Fin 1 → Fin 4 → K) y = ![n, y] from by
      funext i; fin_cases i <;> simp] at hsnoc
  obtain ⟨z, hz⟩ :
      ∃ z : Fin 4 → K, z ∉ Submodule.span K (Set.range (![n, y] : Fin 2 → Fin 4 → K)) := by
    by_contra hcon
    push Not at hcon
    have htop : Submodule.span K (Set.range (![n, y] : Fin 2 → Fin 4 → K)) = ⊤ :=
      Submodule.eq_top_iff'.mpr hcon
    have h2 : Module.finrank K
        (Submodule.span K (Set.range (![n, y] : Fin 2 → Fin 4 → K))) = 2 := by
      rw [finrank_span_eq_card hnyLI]; simp
    rw [htop, finrank_top, Module.finrank_fin_fun] at h2
    omega
  refine ⟨y, z, ?_⟩
  have hsnoc := linearIndependent_finSnoc.mpr ⟨hnyLI, hz⟩
  rwa [show Fin.snoc (![n, y] : Fin 2 → Fin 4 → K) z = ![n, y, z] from by
    funext i; fin_cases i <;> simp] at hsnoc

/-- **The normals of a realization in the chart, at one body** (a step of
`lem:pencil-generic-steer`): for a nondegenerate realization of `G`, a family `pt` of nonzero
vectors with `pt w` a nonzero multiple of `point w` at each `w ∈ V(G)`, and a body `v` that is not a
pencil hub, there are a selector `sel` of `G.closedNbhd v` and padding vectors `fill` such that the
three vectors `hubSlotOf pt sel fill i` are linearly independent and, if `v ∈ V(G)`, their `cross₃`
is a nonzero multiple of `normal v`. At a hub nothing is asked. The proof takes the cases of the
section header. -/
theorem exists_nbrSlotOf_isNondegPencilRealization [Finite α] [Finite β]
    {G : Graph α β} {F : BodyHingeFramework K 2 α β} {normal point pt : α → Fin 4 → K}
    (h : IsNondegPencilRealization G F normal point)
    (hpt_ne : ∀ v, pt v ≠ 0) (hpt : ∀ v ∈ V(G), ∃ c : K, c ≠ 0 ∧ pt v = c • point v) (v : α) :
    ∃ (sel : Fin 3 → Option α) (fill : Fin 3 → Fin 4 → K),
      (¬ G.PencilHub v → IsFin3SelectorOf (G.closedNbhd v) sel) ∧
      (¬ G.PencilHub v → LinearIndependent K
        ![hubSlotOf pt sel fill 0, hubSlotOf pt sel fill 1, hubSlotOf pt sel fill 2]) ∧
      (v ∈ V(G) → ¬ G.PencilHub v → ∃ d : K, d ≠ 0 ∧
        cross₃ (hubSlotOf pt sel fill 0) (hubSlotOf pt sel fill 1) (hubSlotOf pt sel fill 2)
          = d • normal v) := by
  by_cases hhub : G.PencilHub v
  · exact ⟨fun _ => none, fun _ => 0, fun hcon => absurd hhub hcon, fun hcon => absurd hhub hcon,
      fun _ hcon => absurd hhub hcon⟩
  · by_cases hv : v ∈ V(G)
    · have hcard : (G.closedNbhd v).ncard ≤ 3 := ncard_closedNbhd_le_three_of_not_pencilHub hhub
      have hfin : (G.closedNbhd v).Finite := Set.toFinite _
      have hcases : (G.closedNbhd v).ncard = 0 ∨ (G.closedNbhd v).ncard = 1 ∨
          (G.closedNbhd v).ncard = 2 ∨ (G.closedNbhd v).ncard = 3 := by omega
      rcases hcases with h0 | h1 | h2 | h3
      · exfalso
        rw [Set.ncard_eq_zero hfin] at h0
        have hvmem : v ∈ G.closedNbhd v := Or.inl rfl
        rw [h0] at hvmem
        simp at hvmem
      · obtain ⟨a, heq⟩ := Set.ncard_eq_one.mp h1
        have hSel : IsFin3SelectorOf (G.closedNbhd v) (![some a, none, none]) := by
          clear h hpt hpt_ne
          refine ⟨?_, ?_, ?_⟩
          · intro i w hi; fin_cases i <;> simp_all
          · intro w hw; rw [heq] at hw
            simp only [Set.mem_singleton_iff] at hw; exact ⟨0, by simp [hw]⟩
          · intro i j w hi hj; fin_cases i <;> fin_cases j <;> simp_all
        have hLI_point : LinearIndepOn K point (G.closedNbhd v) := h.2.2.2 v hv hhub
        have hpa_ne : point a ≠ 0 := by
          rw [heq] at hLI_point; exact (linearIndepOn_singleton_iff K).mp hLI_point
        have haV : a ∈ V(G) := Graph.closedNbhd_subset_vertexSet hv (heq ▸ rfl)
        obtain ⟨ca, hca_ne, hca_eq⟩ := hpt a haV
        have hpta_ne : pt a ≠ 0 := by rw [hca_eq]; exact smul_ne_zero hca_ne hpa_ne
        have hqa : normal v ⬝ᵥ pt a = 0 := by
          rw [hca_eq, dotProduct_smul]
          have hh : point a ⬝ᵥ normal v = 0 :=
            dotProduct_normal_eq_zero_of_mem_closedNbhd h hv (heq ▸ rfl)
          rw [dotProduct_comm] at hh
          rw [hh, smul_zero]
        obtain ⟨y, z, hLIyz, hxyz⟩ :=
          exists_cross₃_eq_of_ne_zero_of_dotProduct_eq_zero hpta_ne (h.1.1.2.1 v hv) hqa
        refine ⟨![some a, none, none], ![0, y, z], fun _ => hSel, fun _ => ?_,
          fun _ _ => ⟨1, one_ne_zero, ?_⟩⟩
        · have heqf : (![hubSlotOf pt ![some a, none, none] ![0,y,z] 0,
              hubSlotOf pt ![some a, none, none] ![0,y,z] 1,
              hubSlotOf pt ![some a, none, none] ![0,y,z] 2] : Fin 3 → Fin 4 → K)
              = ![pt a, y, z] := by funext i; fin_cases i <;> rfl
          rw [heqf]; exact hLIyz
        · have hh0 : hubSlotOf pt ![some a, none, none] ![0,y,z] 0 = pt a := rfl
          have hh1 : hubSlotOf pt ![some a, none, none] ![0,y,z] 1 = y := rfl
          have hh2 : hubSlotOf pt ![some a, none, none] ![0,y,z] 2 = z := rfl
          rw [hh0, hh1, hh2, one_smul]
          exact hxyz
      · obtain ⟨x, y, hxy, heq⟩ := Set.ncard_eq_two.mp h2
        have hSel : IsFin3SelectorOf (G.closedNbhd v) (![some x, some y, none]) := by
          clear h hpt hpt_ne
          refine ⟨?_, ?_, ?_⟩
          · intro i w hi; fin_cases i <;> simp_all
          · intro w hw; rw [heq] at hw
            rcases hw with rfl | rfl
            · exact ⟨0, rfl⟩
            · exact ⟨1, rfl⟩
          · intro i j w hi hj; fin_cases i <;> fin_cases j <;> simp_all
        have hLI_point : LinearIndepOn K point (G.closedNbhd v) := h.2.2.2 v hv hhub
        have hLI2 : LinearIndependent K ![point x, point y] := by
          rw [LinearIndependent.pair_iff]
          exact (LinearIndepOn.pair_iff point hxy).mp (heq ▸ hLI_point)
        have hxV : x ∈ V(G) := Graph.closedNbhd_subset_vertexSet hv (heq ▸ Set.mem_insert x {y})
        have hyV : y ∈ V(G) :=
          Graph.closedNbhd_subset_vertexSet hv (heq ▸ Set.mem_insert_of_mem x rfl)
        obtain ⟨cx, hcx_ne, hcx_eq⟩ := hpt x hxV
        obtain ⟨cy, hcy_ne, hcy_eq⟩ := hpt y hyV
        have hLI2' : LinearIndependent K ![pt x, pt y] := by
          have hw : LinearIndependent K
              ((![Units.mk0 cx hcx_ne, Units.mk0 cy hcy_ne] : Fin 2 → Kˣ) •
                (![point x, point y] : Fin 2 → Fin 4 → K)) := hLI2.units_smul _
          have heq2 : ((![Units.mk0 cx hcx_ne, Units.mk0 cy hcy_ne] : Fin 2 → Kˣ) •
              (![point x, point y] : Fin 2 → Fin 4 → K)) = ![pt x, pt y] := by
            funext i; fin_cases i <;> simp [Units.smul_def, hcx_eq, hcy_eq]
          rwa [heq2] at hw
        have hqx : normal v ⬝ᵥ pt x = 0 := by
          rw [hcx_eq, dotProduct_smul]
          have hh : point x ⬝ᵥ normal v = 0 := dotProduct_normal_eq_zero_of_mem_closedNbhd h hv
            (heq ▸ Set.mem_insert x {y})
          rw [dotProduct_comm] at hh
          rw [hh, smul_zero]
        have hqy : normal v ⬝ᵥ pt y = 0 := by
          rw [hcy_eq, dotProduct_smul]
          have hh : point y ⬝ᵥ normal v = 0 := dotProduct_normal_eq_zero_of_mem_closedNbhd h hv
            (heq ▸ Set.mem_insert_of_mem x rfl)
          rw [dotProduct_comm] at hh
          rw [hh, smul_zero]
        obtain ⟨z, hxyz⟩ :=
          exists_cross₃_eq_of_linearIndependent_pair_of_dotProduct_eq_zero hLI2' hqx hqy
        have hz_ne : cross₃ (pt x) (pt y) z ≠ 0 := hxyz ▸ h.1.1.2.1 v hv
        have hLI3 : LinearIndependent K ![pt x, pt y, z] :=
          (cross₃_ne_zero_iff_linearIndependent _ _ _).mp hz_ne
        refine ⟨![some x, some y, none], ![0, 0, z], fun _ => hSel, fun _ => ?_,
          fun _ _ => ⟨1, one_ne_zero, ?_⟩⟩
        · have heqf : (![hubSlotOf pt ![some x, some y, none] ![0,0,z] 0,
              hubSlotOf pt ![some x, some y, none] ![0,0,z] 1,
              hubSlotOf pt ![some x, some y, none] ![0,0,z] 2] : Fin 3 → Fin 4 → K)
              = ![pt x, pt y, z] := by funext i; fin_cases i <;> rfl
          rw [heqf]; exact hLI3
        · have hh0 : hubSlotOf pt ![some x, some y, none] ![0,0,z] 0 = pt x := rfl
          have hh1 : hubSlotOf pt ![some x, some y, none] ![0,0,z] 1 = pt y := rfl
          have hh2 : hubSlotOf pt ![some x, some y, none] ![0,0,z] 2 = z := rfl
          rw [hh0, hh1, hh2, one_smul]
          exact hxyz
      · obtain ⟨x, y, z, hxy, hxz, hyz, heq⟩ := Set.ncard_eq_three.mp h3
        have hSel : IsFin3SelectorOf (G.closedNbhd v) (![some x, some y, some z]) := by
          clear h hpt hpt_ne
          refine ⟨?_, ?_, ?_⟩
          · intro i w hi; fin_cases i <;> simp_all
          · intro w hw; rw [heq] at hw
            rcases hw with rfl | rfl | rfl
            · exact ⟨0, rfl⟩
            · exact ⟨1, rfl⟩
            · exact ⟨2, rfl⟩
          · intro i j w hi hj; fin_cases i <;> fin_cases j <;> simp_all
        have hLI_point : LinearIndepOn K point (G.closedNbhd v) := h.2.2.2 v hv hhub
        have hLI3 : LinearIndependent K ![point x, point y, point z] :=
          linearIndependent_triple_of_linearIndepOn point hxy hxz hyz (heq ▸ hLI_point)
        have hxV : x ∈ V(G) :=
          Graph.closedNbhd_subset_vertexSet hv (heq ▸ (by simp : x ∈ ({x,y,z}:Set α)))
        have hyV : y ∈ V(G) :=
          Graph.closedNbhd_subset_vertexSet hv (heq ▸ (by simp : y ∈ ({x,y,z}:Set α)))
        have hzV : z ∈ V(G) :=
          Graph.closedNbhd_subset_vertexSet hv (heq ▸ (by simp : z ∈ ({x,y,z}:Set α)))
        obtain ⟨cx, hcx_ne, hcx_eq⟩ := hpt x hxV
        obtain ⟨cy, hcy_ne, hcy_eq⟩ := hpt y hyV
        obtain ⟨cz, hcz_ne, hcz_eq⟩ := hpt z hzV
        have hLI3' : LinearIndependent K ![pt x, pt y, pt z] := by
          have hw : LinearIndependent K
              ((![Units.mk0 cx hcx_ne, Units.mk0 cy hcy_ne, Units.mk0 cz hcz_ne] : Fin 3 → Kˣ) •
                (![point x, point y, point z] : Fin 3 → Fin 4 → K)) := hLI3.units_smul _
          have heq2 : ((![Units.mk0 cx hcx_ne, Units.mk0 cy hcy_ne, Units.mk0 cz hcz_ne]
              : Fin 3 → Kˣ) •
              (![point x, point y, point z] : Fin 3 → Fin 4 → K)) = ![pt x, pt y, pt z] := by
            funext i; fin_cases i <;> simp [Units.smul_def, hcx_eq, hcy_eq, hcz_eq]
          rwa [heq2] at hw
        have hqx : normal v ⬝ᵥ pt x = 0 := by
          rw [hcx_eq, dotProduct_smul]
          have hh : point x ⬝ᵥ normal v = 0 := dotProduct_normal_eq_zero_of_mem_closedNbhd h hv
            (heq ▸ (by simp : x ∈ ({x,y,z}:Set α)))
          rw [dotProduct_comm] at hh
          rw [hh, smul_zero]
        have hqy : normal v ⬝ᵥ pt y = 0 := by
          rw [hcy_eq, dotProduct_smul]
          have hh : point y ⬝ᵥ normal v = 0 := dotProduct_normal_eq_zero_of_mem_closedNbhd h hv
            (heq ▸ (by simp : y ∈ ({x,y,z}:Set α)))
          rw [dotProduct_comm] at hh
          rw [hh, smul_zero]
        have hqz : normal v ⬝ᵥ pt z = 0 := by
          rw [hcz_eq, dotProduct_smul]
          have hh : point z ⬝ᵥ normal v = 0 := dotProduct_normal_eq_zero_of_mem_closedNbhd h hv
            (heq ▸ (by simp : z ∈ ({x,y,z}:Set α)))
          rw [dotProduct_comm] at hh
          rw [hh, smul_zero]
        obtain ⟨d, hd, hcxyz⟩ :=
          exists_smul_cross₃_eq_of_linearIndependent hLI3' (h.1.1.2.1 v hv) hqx hqy hqz
        refine ⟨![some x, some y, some z], ![0, 0, 0], fun _ => hSel, fun _ => ?_,
          fun _ _ => ⟨d, hd, ?_⟩⟩
        · have heqf : (![hubSlotOf pt ![some x, some y, some z] ![0,0,0] 0,
              hubSlotOf pt ![some x, some y, some z] ![0,0,0] 1,
              hubSlotOf pt ![some x, some y, some z] ![0,0,0] 2] : Fin 3 → Fin 4 → K)
              = ![pt x, pt y, pt z] := by funext i; fin_cases i <;> rfl
          rw [heqf]; exact hLI3'
        · have hh0 : hubSlotOf pt ![some x, some y, some z] ![0,0,0] 0 = pt x := rfl
          have hh1 : hubSlotOf pt ![some x, some y, some z] ![0,0,0] 1 = pt y := rfl
          have hh2 : hubSlotOf pt ![some x, some y, some z] ![0,0,0] 2 = pt z := rfl
          rw [hh0, hh1, hh2]
          exact hcxyz
    · have heq : G.closedNbhd v = {v} := by
        ext w
        simp only [Graph.closedNbhd, Set.mem_ofPred_eq, Set.mem_singleton_iff]
        constructor
        · rintro (rfl | ⟨e, hlink⟩)
          · rfl
          · exact absurd hlink.left_mem hv
        · rintro rfl; exact Or.inl rfl
      have hSel : IsFin3SelectorOf (G.closedNbhd v) (![some v, none, none]) := by
        clear h hpt hpt_ne
        refine ⟨?_, ?_, ?_⟩
        · intro i w hi; fin_cases i <;> simp_all
        · intro w hw; rw [heq] at hw
          simp only [Set.mem_singleton_iff] at hw; exact ⟨0, by simp [hw]⟩
        · intro i j w hi hj; fin_cases i <;> fin_cases j <;> simp_all
      obtain ⟨y, z, hLIyz⟩ := exists_linearIndependent_triple_of_ne_zero (hpt_ne v)
      refine ⟨![some v, none, none], ![0, y, z], fun _ => hSel, fun _ => ?_,
        fun hcon => absurd hcon hv⟩
      · have heqf : (![hubSlotOf pt ![some v, none, none] ![0,y,z] 0,
            hubSlotOf pt ![some v, none, none] ![0,y,z] 1,
            hubSlotOf pt ![some v, none, none] ![0,y,z] 2] : Fin 3 → Fin 4 → K)
            = ![pt v, y, z] := by funext i; fin_cases i <;> rfl
        rw [heqf]; exact hLIyz

/-- **The normals of a realization in the chart** (a step of `lem:pencil-generic-steer`): given a
nondegenerate realization of `G`, and `hubSel` and `fillHub` whose slots are independent at every
body and whose points are nonzero multiples of `point` on `V(G)`, both at the parameters with
`fillNbr := 0`, there are a neighbour selector `nbrSel` and padding `fillNbr` such that, at every
body `v` that is not a hub, `nbrSel v` lists `G.closedNbhd v`, and, at the parameters
`⟨normal, fillHub, fillNbr⟩`, the three slots `nbrSlotPoint` of `v` are independent and, if
`v ∈ V(G)`, the normal of the chart is a nonzero multiple of `normal v`: the second and fourth
conditions of `PencilChartWF`, and the normals reproduced up to scalars. `choose` applies
`exists_nbrSlotOf_isNondegPencilRealization` at every body, with `pt` the points of the chart, which
do not read `fillNbr` and are nonzero (`pencilChartPoint_ne_zero`); at a body that is not a hub, the
normal of the chart is `cross₃` of the slots (`pencilChartNormal_of_not_pencilHub`). -/
theorem exists_nbrSel_fillNbr_of_isNondegPencilRealization [Finite α] [Finite β]
    {G : Graph α β} {F : BodyHingeFramework K 2 α β} {normal point : α → Fin 4 → K}
    (h : IsNondegPencilRealization G F normal point)
    {hubSel : α → Fin 3 → Option α} {fillHub : α → Fin 3 → Fin 4 → K}
    (hHubLI : ∀ v, LinearIndependent K
      ![hubSlotNormal ⟨normal, fillHub, fun _ _ => (0 : Fin 4 → K)⟩ hubSel v 0,
        hubSlotNormal ⟨normal, fillHub, fun _ _ => (0 : Fin 4 → K)⟩ hubSel v 1,
        hubSlotNormal ⟨normal, fillHub, fun _ _ => (0 : Fin 4 → K)⟩ hubSel v 2])
    (hPtRepro : ∀ v ∈ V(G), ∃ c : K, c ≠ 0 ∧
      pencilChartPoint ⟨normal, fillHub, fun _ _ => (0 : Fin 4 → K)⟩ hubSel v = c • point v) :
    ∃ (nbrSel : α → Fin 3 → Option α) (fillNbr : α → Fin 3 → Fin 4 → K),
      (∀ v, ¬ G.PencilHub v → IsFin3SelectorOf (G.closedNbhd v) (nbrSel v)) ∧
      (∀ v, ¬ G.PencilHub v → LinearIndependent K
        ![nbrSlotPoint ⟨normal, fillHub, fillNbr⟩ hubSel nbrSel v 0,
          nbrSlotPoint ⟨normal, fillHub, fillNbr⟩ hubSel nbrSel v 1,
          nbrSlotPoint ⟨normal, fillHub, fillNbr⟩ hubSel nbrSel v 2]) ∧
      (∀ v ∈ V(G), ¬ G.PencilHub v → ∃ d : K, d ≠ 0 ∧
        pencilChartNormal ⟨normal, fillHub, fillNbr⟩ hubSel nbrSel G v = d • normal v) := by
  set seed0 : PencilSeed K α := ⟨normal, fillHub, fun _ _ => (0 : Fin 4 → K)⟩ with hseed0
  have hpt_ne : ∀ v, pencilChartPoint seed0 hubSel v ≠ 0 :=
    fun v => pencilChartPoint_ne_zero seed0 (hHubLI v)
  choose nbrSel fillNbr hsel hLI hd using
    fun v => exists_nbrSlotOf_isNondegPencilRealization h hpt_ne hPtRepro v
  refine ⟨nbrSel, fillNbr, hsel, fun v hv => hLI v hv, fun v hv hnothub => ?_⟩
  obtain ⟨d, hdne, hdeq⟩ := hd v hv hnothub
  refine ⟨d, hdne, ?_⟩
  rw [pencilChartNormal_of_not_pencilHub _ _ _ hnothub]
  exact hdeq

end CombinatorialRigidity.Molecular
