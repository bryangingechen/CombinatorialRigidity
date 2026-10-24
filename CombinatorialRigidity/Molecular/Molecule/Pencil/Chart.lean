/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.Motive

/-!
# The cross product of `K⁴` and the pencil chart

The parametrization of pencil realizations in the proof of `lem:pencil-generic-steer`
(`sec:main-component-statements`), and the cross product it is built from.

For `x, y, z ∈ K⁴`, `cross₃ x y z` is the vector with `cross₃ x y z ⬝ᵥ w = det[x, y, z, w]` for
every `w`: the product `y₁ × y₂ × y₃` of that proof, and the plane normal of
`def:pencil-configuration`. It is orthogonal to `x`, `y` and `z`, linear in `z`, and nonzero
exactly when the three are linearly independent.

The chart takes, at each body `v`, a vector `hubNormal v` and two triples of padding vectors
(`PencilSeed`), and two selectors, which list the closed hub-neighbourhood and the closed
neighbourhood of each body in three slots (`IsFin3SelectorOf`). The normal of a hub is its
`hubNormal`; the point of a body is the `cross₃` of the `hubNormal`s its hub selector lists, padded
to three vectors; and the normal of a body that is not a hub is the `cross₃` of the points its
neighbour selector lists, padded likewise. The framework of the chart has at each edge the join of
the points of its ends (`pencilChartFramework`). At well-formed parameters (`PencilChartWF`: the
selectors list their sets, the padded triples are independent, and so are the points of the two ends
of every link), the chart is a nondegenerate pencil realization (`def:pencil-nondegenerate`).

## Main definitions

* `cross₃`: the cross product of three vectors of `K⁴`.
* `PencilSeed`, `IsFin3SelectorOf`, `pencilChartPoint`, `pencilChartNormal`, `PencilChartWF` and
  `pencilChartFramework`: the chart.

## Main results

* `dotProduct_cross₃`, `cross₃_dotProduct_fst`, `cross₃_ne_zero_iff_linearIndependent` and
  `range_cross₃L_eq_perp`: the cross product.
* `isNondegPencilRealization_pencilChartFramework_of_pencilChartWF`: at well-formed parameters, the
  chart is a nondegenerate pencil realization.
-/

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K]
variable {α β : Type*}

/-! ## The cross product of `K⁴`

`cross₃ x y z` is the vector that represents, through the dot product, the linear functional
`w ↦ det[x, y, z, w]` (`Pi.basisFun`'s `toDualEquiv`), so that `cross₃ x y z ⬝ᵥ w = det[x, y, z, w]`
for every `w` (`dotProduct_cross₃`). From this:

* it is orthogonal to `x`, `y` and `z`, as a determinant with two equal rows vanishes
  (`cross₃_dotProduct_fst`, `cross₃_dotProduct_snd`, `cross₃_dotProduct_thd`);
* it is additive and homogeneous in its third argument, as the determinant is in a row
  (`cross₃_add_thd`, `cross₃_smul_thd`), so linear in it (`cross₃L`);
* it is nonzero exactly when `x`, `y` and `z` are linearly independent
  (`cross₃_ne_zero_iff_linearIndependent`);
* for independent `n₁, n₂`, the vectors `cross₃ n₁ n₂ z` are exactly those orthogonal to `n₁` and
  `n₂` (`range_cross₃L_eq_perp`).

`cross₃_apply` (`Engine.lean`) writes its coordinates as determinants, polynomials in those of `x`,
`y` and `z`. -/

/-- The linear functional `w ↦ det[x, y, z, w]` that defines `cross₃`, written with
`Matrix.updateRow` at row `3`, so that its linearity in `w` is `Matrix.det_updateRow_add` and
`Matrix.det_updateRow_smul`. -/
private def cross₃Functional (x y z : Fin 4 → K) : (Fin 4 → K) →ₗ[K] K where
  toFun w := Matrix.det ((Matrix.of ![x, y, z, (0 : Fin 4 → K)]).updateRow 3 w)
  map_add' w1 w2 := Matrix.det_updateRow_add _ 3 w1 w2
  map_smul' c w := Matrix.det_updateRow_smul _ 3 c w

/-- **The cross product of three vectors of `K⁴`** (the product `y₁ × y₂ × y₃` of
`lem:pencil-generic-steer`'s proof, and the plane normal of `def:pencil-configuration`): the vector
that represents, through the dot product, the linear functional `w ↦ det[x, y, z, w]`
(`cross₃Functional`). -/
noncomputable def cross₃ (x y z : Fin 4 → K) : Fin 4 → K :=
  (Pi.basisFun K (Fin 4)).toDualEquiv.symm (cross₃Functional x y z)

omit [Field K] in
/-- Replacing row `2` of the matrix with rows `x, y, z0, w` by `a` gives the matrix with rows
`x, y, a, w`, for `cross₃_add_thd` and `cross₃_smul_thd`. -/
private theorem cons_updateRow_two (x y z0 w a : Fin 4 → K) :
    (Matrix.of ![x, y, z0, w]).updateRow 2 a = Matrix.of ![x, y, a, w] := by
  funext i j; fin_cases i <;> simp [Matrix.updateRow_apply]

omit [Field K] in
/-- The row-`3` form of `cons_updateRow_two`, which turns the matrix of `cross₃Functional` into the
one with rows `x, y, z, w` (`dotProduct_cross₃`). -/
private theorem cons_updateRow_three (x y z w0 a : Fin 4 → K) :
    (Matrix.of ![x, y, z, w0]).updateRow 3 a = Matrix.of ![x, y, z, a] := by
  funext i j; fin_cases i <;> simp [Matrix.updateRow_apply]

/-- **The defining property of `cross₃`**: `cross₃ x y z ⬝ᵥ w = det[x, y, z, w]` for every `w`. The
other lemmas on `cross₃` follow from it. -/
theorem dotProduct_cross₃ (x y z w : Fin 4 → K) :
    cross₃ x y z ⬝ᵥ w = Matrix.det (Matrix.of ![x, y, z, w]) := by
  rw [← piBasisFun_toDual_eq_dotProduct, cross₃, ← Module.Basis.toDualEquiv_apply,
    LinearEquiv.apply_symm_apply]
  change Matrix.det ((Matrix.of ![x, y, z, (0 : Fin 4 → K)]).updateRow 3 w) = _
  rw [cons_updateRow_three]

/-- **`cross₃ x y z` is orthogonal to `x`**: `det[x, y, z, x]` has two equal rows. -/
theorem cross₃_dotProduct_fst (x y z : Fin 4 → K) : cross₃ x y z ⬝ᵥ x = 0 := by
  rw [dotProduct_cross₃]; exact Matrix.det_zero_of_row_eq (i := 0) (j := 3) (by decide) rfl

/-- **`cross₃ x y z` is orthogonal to `y`**, as `cross₃_dotProduct_fst`. -/
theorem cross₃_dotProduct_snd (x y z : Fin 4 → K) : cross₃ x y z ⬝ᵥ y = 0 := by
  rw [dotProduct_cross₃]; exact Matrix.det_zero_of_row_eq (i := 1) (j := 3) (by decide) rfl

/-- **`cross₃ x y z` is orthogonal to `z`**, as `cross₃_dotProduct_fst`. -/
theorem cross₃_dotProduct_thd (x y z : Fin 4 → K) : cross₃ x y z ⬝ᵥ z = 0 := by
  rw [dotProduct_cross₃]; exact Matrix.det_zero_of_row_eq (i := 2) (j := 3) (by decide) rfl

/-- **`cross₃` is additive in its third argument**: by `dotProduct_eq_iff`, from the additivity of
`Matrix.det` in a row. -/
theorem cross₃_add_thd (x y z1 z2 : Fin 4 → K) :
    cross₃ x y (z1 + z2) = cross₃ x y z1 + cross₃ x y z2 := by
  rw [← dotProduct_eq_iff]; intro w
  rw [add_dotProduct, dotProduct_cross₃, dotProduct_cross₃, dotProduct_cross₃,
    ← cons_updateRow_two x y z1 w (z1 + z2), Matrix.det_updateRow_add,
    cons_updateRow_two, cons_updateRow_two]

/-- **`cross₃` is homogeneous in its third argument**: `cross₃ x y (c • z) = c • cross₃ x y z`, as
`cross₃_add_thd`. -/
theorem cross₃_smul_thd (c : K) (x y z : Fin 4 → K) :
    cross₃ x y (c • z) = c • cross₃ x y z := by
  rw [← dotProduct_eq_iff]; intro w
  rw [smul_dotProduct, dotProduct_cross₃, dotProduct_cross₃,
    ← cons_updateRow_two x y z w (c • z), Matrix.det_updateRow_smul,
    cons_updateRow_two, smul_eq_mul]

/-- **`cross₃` as a linear map in its third argument**: `z ↦ cross₃ x y z`, whose range
`range_cross₃L_eq_perp` gives. -/
noncomputable def cross₃L (x y : Fin 4 → K) : (Fin 4 → K) →ₗ[K] (Fin 4 → K) where
  toFun z := cross₃ x y z
  map_add' := cross₃_add_thd x y
  map_smul' c z := cross₃_smul_thd c x y z

@[simp]
theorem cross₃L_apply (x y z : Fin 4 → K) : cross₃L x y z = cross₃ x y z := rfl

/-- **`cross₃` is nonzero exactly when its arguments are independent**:
`cross₃ x y z ≠ 0 ↔ LinearIndependent K ![x, y, z]`. If `x, y, z` are dependent, so are `x, y, z, w`
for every `w` (`linearIndependent_finSnoc`), so `det[x, y, z, w] = 0`
(`Matrix.linearIndependent_row_iff_isUnit`) and `cross₃ x y z = 0`. If they are independent, some
`w` lies outside their span, of dimension `3 < 4`; then `x, y, z, w` are independent and
`det[x, y, z, w] ≠ 0`. -/
theorem cross₃_ne_zero_iff_linearIndependent (x y z : Fin 4 → K) :
    cross₃ x y z ≠ 0 ↔ LinearIndependent K ![x, y, z] := by
  constructor
  · intro hne
    by_contra hLI
    apply hne
    rw [← dotProduct_eq_zero_iff]
    intro w
    rw [dotProduct_cross₃]
    have hsnoc : ¬ LinearIndependent K (Fin.snoc ![x, y, z] w) := by
      rw [linearIndependent_finSnoc]
      exact fun h => hLI h.1
    rw [show Fin.snoc (![x, y, z] : Fin 3 → Fin 4 → K) w = ![x, y, z, w] from by
      funext i; fin_cases i <;> simp] at hsnoc
    have := (Matrix.linearIndependent_row_iff_isUnit
      (A := Matrix.of ![x, y, z, w])).not.mp hsnoc
    rwa [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at this
  · intro hLI hzero
    obtain ⟨w, hw⟩ : ∃ w : Fin 4 → K, w ∉ Submodule.span K (Set.range ![x, y, z]) := by
      by_contra hcon
      push Not at hcon
      have htop : Submodule.span K (Set.range (![x, y, z] : Fin 3 → Fin 4 → K)) = ⊤ :=
        Submodule.eq_top_iff'.mpr hcon
      have h3 : Module.finrank K
          (Submodule.span K (Set.range (![x, y, z] : Fin 3 → Fin 4 → K))) = 3 := by
        rw [finrank_span_eq_card hLI]; simp
      rw [htop, finrank_top, Module.finrank_fin_fun] at h3
      omega
    have hsnoc : LinearIndependent K (Fin.snoc ![x, y, z] w) :=
      linearIndependent_finSnoc.mpr ⟨hLI, hw⟩
    rw [show Fin.snoc (![x, y, z] : Fin 3 → Fin 4 → K) w = ![x, y, z, w] from by
      funext i; fin_cases i <;> simp] at hsnoc
    have hdet : Matrix.det (Matrix.of ![x, y, z, w]) ≠ 0 := by
      have hu := (Matrix.linearIndependent_row_iff_isUnit
        (A := Matrix.of ![x, y, z, w])).mp hsnoc
      rwa [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hu
    apply hdet
    rw [← dotProduct_cross₃, hzero, zero_dotProduct]

/-- **The values of `cross₃ n₁ n₂` are the vectors orthogonal to `n₁` and `n₂`** (a step of
`lem:pencil-generic-steer`): for independent `n₁, n₂`, the range of `cross₃L n₁ n₂` is the space of
vectors orthogonal to both. The range lies in that space (`cross₃_dotProduct_fst`,
`cross₃_dotProduct_snd`). The kernel of `cross₃L n₁ n₂` is the span of `n₁, n₂`
(`cross₃_ne_zero_iff_linearIndependent`, `linearIndependent_finSnoc`), of dimension `2`, so the
range has dimension `4 - 2 = 2`, that of the space (`finrank_toDualPerp_pair_eq`), and the two are
equal (`Submodule.eq_of_le_of_finrank_eq`). -/
theorem range_cross₃L_eq_perp (n₁ n₂ : Fin 4 → K) (hLI : LinearIndependent K ![n₁, n₂]) :
    LinearMap.range (cross₃L n₁ n₂) =
      (⨅ j : Fin 2, LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip (![n₁, n₂] j)) :
        Submodule K (Fin 4 → K)) := by
  have hker : LinearMap.ker (cross₃L n₁ n₂) = Submodule.span K (Set.range ![n₁, n₂]) := by
    ext z
    simp only [LinearMap.mem_ker, cross₃L, LinearMap.coe_mk, AddHom.coe_mk]
    constructor
    · intro hz
      by_contra hzmem
      have hsnoc : LinearIndependent K (Fin.snoc ![n₁, n₂] z) :=
        linearIndependent_finSnoc.mpr ⟨hLI, hzmem⟩
      rw [show Fin.snoc (![n₁, n₂] : Fin 2 → Fin 4 → K) z = ![n₁, n₂, z] from by
        funext i; fin_cases i <;> simp] at hsnoc
      exact (cross₃_ne_zero_iff_linearIndependent n₁ n₂ z).mpr hsnoc hz
    · intro hzmem
      by_contra hz
      have hLI3 : LinearIndependent K ![n₁, n₂, z] :=
        (cross₃_ne_zero_iff_linearIndependent n₁ n₂ z).mp hz
      rw [← show Fin.snoc (![n₁, n₂] : Fin 2 → Fin 4 → K) z = ![n₁, n₂, z] from by
        funext i; fin_cases i <;> simp, linearIndependent_finSnoc] at hLI3
      exact hLI3.2 hzmem
  have hle : LinearMap.range (cross₃L n₁ n₂) ≤
      (⨅ j : Fin 2, LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip (![n₁, n₂] j)) :
        Submodule K (Fin 4 → K)) := by
    rintro _ ⟨z, rfl⟩
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply]
    intro j
    fin_cases j
    · change (Pi.basisFun K (Fin 4)).toDual (cross₃L n₁ n₂ z) n₁ = 0
      rw [piBasisFun_toDual_eq_dotProduct]
      exact cross₃_dotProduct_fst n₁ n₂ z
    · change (Pi.basisFun K (Fin 4)).toDual (cross₃L n₁ n₂ z) n₂ = 0
      rw [piBasisFun_toDual_eq_dotProduct]
      exact cross₃_dotProduct_snd n₁ n₂ z
  have hdim_ker : Module.finrank K (LinearMap.ker (cross₃L n₁ n₂)) = 2 := by
    rw [hker, finrank_span_eq_card hLI]; simp
  have hdim_range : Module.finrank K (LinearMap.range (cross₃L n₁ n₂)) = 2 := by
    have hrn := LinearMap.finrank_range_add_finrank_ker (cross₃L n₁ n₂)
    rw [hdim_ker, Module.finrank_fin_fun] at hrn
    omega
  have hdim_perp : Module.finrank K
      (⨅ j : Fin 2, LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip (![n₁, n₂] j)) :
        Submodule K (Fin 4 → K)) = 2 :=
    finrank_toDualPerp_pair_eq hLI
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hdim_range, hdim_perp])

/-! ## The pencil chart

The parameters of the chart (`PencilSeed`) are, at each body `v`, a vector `hubNormal v`, the normal
of `v` when it is a hub, and two triples of padding vectors, `fillHub v` and `fillNbr v`. The
selectors `hubSel` and `nbrSel` list the closed hub-neighbourhood and the closed neighbourhood of a
body in three slots: `some w` puts `w` in a slot, and `none` leaves the slot to padding
(`IsFin3SelectorOf`). The two neighbourhoods are sets, so a selector fixes the order in which their
members enter `cross₃`.

The point of `v` (`pencilChartPoint`) is the `cross₃` of the three vectors `hubSlotNormal`: the
`hubNormal` of each body that `hubSel v` lists, and `fillHub v` at the empty slots. The normal of
`v` (`pencilChartNormal`) is `hubNormal v` if `v` is a hub, and otherwise the `cross₃` of the three
vectors `nbrSlotPoint`: the point of each body that `nbrSel v` lists, and `fillNbr v` at the empty
slots. For fixed selectors, the coordinates of each are polynomials in the parameters.

`PencilChartWF` asks that the selectors list their sets, that the three vectors of each `cross₃` be
independent, and that the points of the two ends of every link be independent. When the selectors
list their sets, at any parameters, the point of `v` is orthogonal to the `hubNormal` of every body
of its closed hub-neighbourhood, and the normal of a body that is not a hub to the point of every
body of its closed neighbourhood (`dotProduct_pencilChartPoint_hubNormal_of_mem_closedHubNbhd`,
`dotProduct_pencilChartPoint_pencilChartNormal_of_mem_closedNbhd`), by the orthogonality of
`cross₃`. These are the incidences of a pencil realization. -/

/-- **The parameters of the pencil chart** (a step of `lem:pencil-generic-steer`): at each body, a
vector `hubNormal`, the normal of a hub, and two triples of padding vectors, `fillHub` for the slots
the hub selector leaves empty and `fillNbr` for those the neighbour selector leaves empty. The
parametrization of `lem:pencil-generic-steer`'s proof pads only the point. Here the normal of a body
that is not a hub is the `cross₃` of the points of its closed neighbourhood, padded by its own
triple, so that the two paddings can be chosen independently. -/
structure PencilSeed (K : Type*) [Field K] (α : Type*) where
  /-- At each body, its normal when it is a hub (`pencilChartNormal`). -/
  hubNormal : α → Fin 4 → K
  /-- At each body `v`, the vectors at the slots that `hubSel v` leaves empty (`hubSlotNormal`), in
  the `cross₃` of `pencilChartPoint`. -/
  fillHub : α → Fin 3 → Fin 4 → K
  /-- At each body `v`, the vectors at the slots that `nbrSel v` leaves empty (`nbrSlotPoint`), in
  the `cross₃` of `pencilChartNormal` at a body that is not a hub. -/
  fillNbr : α → Fin 3 → Fin 4 → K

/-- **A selector of a set in three slots** (a step of `lem:pencil-generic-steer`): `sel i = some w`
puts `w` in slot `i`, and `sel i = none` leaves the slot empty. `IsFin3SelectorOf s sel` says that
every member of a slot lies in `s`, that every member of `s` is in a slot, and that no member is in
two slots; so `s` has at most three members. -/
def IsFin3SelectorOf (s : Set α) (sel : Fin 3 → Option α) : Prop :=
  (∀ i w, sel i = some w → w ∈ s) ∧ (∀ w ∈ s, ∃ i, sel i = some w) ∧
    (∀ i j w, sel i = some w → sel j = some w → i = j)

/-- Slot `i` of `v`'s hub selector as a vector (a step of `lem:pencil-generic-steer`): the
`hubNormal` of the body in it, or `fillHub v i` if it is empty. -/
def hubSlotNormal (seed : PencilSeed K α) (hubSel : α → Fin 3 → Option α) (v : α) (i : Fin 3) :
    Fin 4 → K :=
  match hubSel v i with
  | some w => seed.hubNormal w
  | none => seed.fillHub v i

/-- **The point of the chart** (the point of `lem:pencil-generic-steer`'s parametrization): the
`cross₃` of the three slots of `v`'s hub selector (`hubSlotNormal`). -/
noncomputable def pencilChartPoint (seed : PencilSeed K α) (hubSel : α → Fin 3 → Option α)
    (v : α) : Fin 4 → K :=
  cross₃ (hubSlotNormal seed hubSel v 0) (hubSlotNormal seed hubSel v 1)
    (hubSlotNormal seed hubSel v 2)

/-- Slot `i` of `v`'s neighbour selector as a vector (a step of `lem:pencil-generic-steer`): the
point of the body in it (`pencilChartPoint`), or `fillNbr v i` if it is empty. -/
noncomputable def nbrSlotPoint (seed : PencilSeed K α) (hubSel nbrSel : α → Fin 3 → Option α)
    (v : α) (i : Fin 3) : Fin 4 → K :=
  match nbrSel v i with
  | some w => pencilChartPoint seed hubSel w
  | none => seed.fillNbr v i

open Classical in
/-- **The normal of the chart** (the normal of `lem:pencil-generic-steer`'s parametrization):
`hubNormal v` at a pencil hub `v`, and at any other body the `cross₃` of the three slots of `v`'s
neighbour selector (`nbrSlotPoint`). -/
noncomputable def pencilChartNormal (seed : PencilSeed K α) (hubSel nbrSel : α → Fin 3 → Option α)
    (G : Graph α β) (v : α) : Fin 4 → K :=
  if G.PencilHub v then seed.hubNormal v
  else cross₃ (nbrSlotPoint seed hubSel nbrSel v 0) (nbrSlotPoint seed hubSel nbrSel v 1)
    (nbrSlotPoint seed hubSel nbrSel v 2)

theorem pencilChartNormal_of_pencilHub (seed : PencilSeed K α)
    (hubSel nbrSel : α → Fin 3 → Option α) {G : Graph α β} {v : α} (hv : G.PencilHub v) :
    pencilChartNormal seed hubSel nbrSel G v = seed.hubNormal v :=
  ite_eq_left hv

theorem pencilChartNormal_of_not_pencilHub (seed : PencilSeed K α)
    (hubSel nbrSel : α → Fin 3 → Option α) {G : Graph α β} {v : α} (hv : ¬ G.PencilHub v) :
    pencilChartNormal seed hubSel nbrSel G v =
      cross₃ (nbrSlotPoint seed hubSel nbrSel v 0) (nbrSlotPoint seed hubSel nbrSel v 1)
        (nbrSlotPoint seed hubSel nbrSel v 2) :=
  ite_eq_right hv

/-- **Well-formed parameters of the chart** (a step of `lem:pencil-generic-steer`): the hub selector
lists the closed hub-neighbourhood of every body; the neighbour selector lists the closed
neighbourhood of every body that is not a hub; the three slots of the hub selector are linearly
independent at every body, and those of the neighbour selector at every body that is not a hub, so
that the points and those normals are nonzero (`cross₃_ne_zero_iff_linearIndependent`); and the
points of the two ends of every link are linearly independent, the condition of
`IsNondegPencilRealization` on links.

The conditions on the neighbour selector are asked only where `pencilChartNormal` reads it, at a
body that is not a hub. A selector lists at most three members, and the closed neighbourhood of a
hub can have more (four at every body of `K₄`), while that of a body that is not a hub has at most
three. -/
def PencilChartWF (G : Graph α β) (seed : PencilSeed K α) (hubSel nbrSel : α → Fin 3 → Option α) :
    Prop :=
  (∀ v, IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v)) ∧
  (∀ v, ¬ G.PencilHub v → IsFin3SelectorOf (G.closedNbhd v) (nbrSel v)) ∧
  (∀ v, LinearIndependent K
    ![hubSlotNormal seed hubSel v 0, hubSlotNormal seed hubSel v 1,
      hubSlotNormal seed hubSel v 2]) ∧
  (∀ v, ¬ G.PencilHub v → LinearIndependent K
    ![nbrSlotPoint seed hubSel nbrSel v 0, nbrSlotPoint seed hubSel nbrSel v 1,
      nbrSlotPoint seed hubSel nbrSel v 2]) ∧
  (∀ e u v, G.IsLink e u v →
    LinearIndependent K ![pencilChartPoint seed hubSel u, pencilChartPoint seed hubSel v])

/-- **The point of the chart is nonzero** (a step of `lem:pencil-generic-steer`) when the three
slots of its hub selector are independent (`cross₃_ne_zero_iff_linearIndependent`). -/
theorem pencilChartPoint_ne_zero (seed : PencilSeed K α) {hubSel : α → Fin 3 → Option α} {v : α}
    (hLI : LinearIndependent K
      ![hubSlotNormal seed hubSel v 0, hubSlotNormal seed hubSel v 1,
        hubSlotNormal seed hubSel v 2]) :
    pencilChartPoint seed hubSel v ≠ 0 := by
  rw [pencilChartPoint]
  exact (cross₃_ne_zero_iff_linearIndependent _ _ _).mpr hLI

/-- **The normal of the chart at a body that is not a hub is nonzero** (a step of
`lem:pencil-generic-steer`) when the three slots of its neighbour selector are independent
(`cross₃_ne_zero_iff_linearIndependent`). -/
theorem pencilChartNormal_ne_zero_of_not_pencilHub (seed : PencilSeed K α)
    {hubSel nbrSel : α → Fin 3 → Option α} {G : Graph α β} {v : α} (hv : ¬ G.PencilHub v)
    (hLI : LinearIndependent K
      ![nbrSlotPoint seed hubSel nbrSel v 0, nbrSlotPoint seed hubSel nbrSel v 1,
        nbrSlotPoint seed hubSel nbrSel v 2]) :
    pencilChartNormal seed hubSel nbrSel G v ≠ 0 := by
  rw [pencilChartNormal_of_not_pencilHub seed hubSel nbrSel hv]
  exact (cross₃_ne_zero_iff_linearIndependent _ _ _).mpr hLI

/-- **`cross₃` of a family `f : Fin 3 → Fin 4 → K` is orthogonal to each `f i`** (a step of
`lem:pencil-generic-steer`): `cross₃_dotProduct_fst`, `cross₃_dotProduct_snd` or
`cross₃_dotProduct_thd`, as `i` is `0`, `1` or `2`. -/
theorem cross₃_dotProduct_apply_self (f : Fin 3 → Fin 4 → K) (i : Fin 3) :
    cross₃ (f 0) (f 1) (f 2) ⬝ᵥ f i = 0 := by
  fin_cases i
  · exact cross₃_dotProduct_fst _ _ _
  · exact cross₃_dotProduct_snd _ _ _
  · exact cross₃_dotProduct_thd _ _ _

/-- **The point of the chart is orthogonal to the hub normals of its closed hub-neighbourhood** (a
step of `lem:pencil-generic-steer`): if `hubSel v` lists `G.closedHubNbhd v`, then
`pencilChartPoint seed hubSel v ⬝ᵥ seed.hubNormal w = 0` for every `w` in it. At `w = v`, a hub,
this is `point v ⬝ᵥ normal v = 0`; at a neighbour `w` it is a cross-incidence. The selector puts `w`
in some slot, and `cross₃` is orthogonal to that slot (`cross₃_dotProduct_apply_self`), at any
parameters. -/
theorem dotProduct_pencilChartPoint_hubNormal_of_mem_closedHubNbhd {G : Graph α β} {v w : α}
    (seed : PencilSeed K α) {hubSel : α → Fin 3 → Option α}
    (hSel : IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v)) (hw : w ∈ G.closedHubNbhd v) :
    pencilChartPoint seed hubSel v ⬝ᵥ seed.hubNormal w = 0 := by
  obtain ⟨i, hi⟩ := hSel.2.1 w hw
  have hslot : hubSlotNormal seed hubSel v i = seed.hubNormal w := by
    simp [hubSlotNormal, hi]
  rw [pencilChartPoint, ← hslot]
  exact cross₃_dotProduct_apply_self (hubSlotNormal seed hubSel v) i

/-- **The normal of the chart at a body that is not a hub is orthogonal to the points of its closed
neighbourhood** (a step of `lem:pencil-generic-steer`): if `v` is not a hub and `nbrSel v` lists
`G.closedNbhd v`, then the point of every `w` in it is orthogonal to the normal of `v`. At `w = v`
this is `point v ⬝ᵥ normal v = 0`; at a neighbour `w` it is a cross-incidence. The selector puts `w`
in some slot, and `cross₃` is orthogonal to that slot (`cross₃_dotProduct_apply_self`, after
`dotProduct_comm`). -/
theorem dotProduct_pencilChartPoint_pencilChartNormal_of_mem_closedNbhd {G : Graph α β} {v w : α}
    (seed : PencilSeed K α) {hubSel nbrSel : α → Fin 3 → Option α} (hv : ¬ G.PencilHub v)
    (hSel : IsFin3SelectorOf (G.closedNbhd v) (nbrSel v)) (hw : w ∈ G.closedNbhd v) :
    pencilChartPoint seed hubSel w ⬝ᵥ pencilChartNormal seed hubSel nbrSel G v = 0 := by
  rw [pencilChartNormal_of_not_pencilHub seed hubSel nbrSel hv, dotProduct_comm]
  obtain ⟨i, hi⟩ := hSel.2.1 w hw
  have hslot : nbrSlotPoint seed hubSel nbrSel v i = pencilChartPoint seed hubSel w := by
    simp [nbrSlotPoint, hi]
  rw [← hslot]
  exact cross₃_dotProduct_apply_self (nbrSlotPoint seed hubSel nbrSel v) i

/-! ## Independence and incidence at every body

When a selector lists its set, the map that sends each member to a slot holding it is injective, so
the independence of the three slots passes to the members: the normals of the chart are independent
on every closed hub-neighbourhood (`linearIndepOn_pencilChartNormal_closedHubNbhd`), and its points
on every closed neighbourhood (`linearIndepOn_pencilChartPoint_closedNbhd`), as
`IsNondegPencilRealization` asks. The point of every body is orthogonal to its own normal and to the
normal of each neighbour (`dotProduct_pencilChartPoint_pencilChartNormal_self`,
`dotProduct_pencilChartPoint_pencilChartNormal_of_isLink`). -/

/-- **The three slots of the hub selector as a triple** (a step of `lem:pencil-generic-steer`): the
triple `![f 0, f 1, f 2]` for `f = hubSlotNormal seed hubSel v` is `f`, so the two are independent
together. -/
theorem linearIndependent_hubSlotNormal_iff (seed : PencilSeed K α) (hubSel : α → Fin 3 → Option α)
    (v : α) :
    LinearIndependent K
      ![hubSlotNormal seed hubSel v 0, hubSlotNormal seed hubSel v 1,
        hubSlotNormal seed hubSel v 2] ↔
      LinearIndependent K (hubSlotNormal seed hubSel v) := by
  rw [show (![hubSlotNormal seed hubSel v 0, hubSlotNormal seed hubSel v 1,
      hubSlotNormal seed hubSel v 2] : Fin 3 → Fin 4 → K) = hubSlotNormal seed hubSel v from by
    funext j; fin_cases j <;> rfl]

/-- **The normal of the chart at a hub is nonzero** (a step of `lem:pencil-generic-steer`): if
`hubSel v` lists `G.closedHubNbhd v` and its three slots are independent, then
`seed.hubNormal v ≠ 0` at a hub `v`. The hub `v` lies in its own closed hub-neighbourhood, so in
some slot, and the members of an independent family are nonzero (`LinearIndependent.ne_zero`). -/
theorem hubNormal_ne_zero_of_pencilHub {G : Graph α β} {v : α}
    (seed : PencilSeed K α) {hubSel : α → Fin 3 → Option α}
    (hSel : IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v))
    (hLI : LinearIndependent K
      ![hubSlotNormal seed hubSel v 0, hubSlotNormal seed hubSel v 1,
        hubSlotNormal seed hubSel v 2])
    (hv : G.PencilHub v) :
    seed.hubNormal v ≠ 0 := by
  obtain ⟨i, hi⟩ := hSel.2.1 v ⟨hv, Or.inl rfl⟩
  have hslot : hubSlotNormal seed hubSel v i = seed.hubNormal v := by simp [hubSlotNormal, hi]
  rw [← hslot]
  exact ((linearIndependent_hubSlotNormal_iff seed hubSel v).mp hLI).ne_zero i

/-- **The normals of the chart are independent on a closed hub-neighbourhood** (a step of
`lem:pencil-generic-steer`; a condition of `def:pencil-nondegenerate`): if `hubSel v` lists
`G.closedHubNbhd v` and its three slots are independent, then `pencilChartNormal` is linearly
independent on `G.closedHubNbhd v`. Sending each member `w` to a slot that holds it (the selector's
second condition) is injective, as a slot holds one member, so the independence of the slots passes
to the members (`LinearIndependent.comp`); and each member is a hub, so its normal is its
`hubNormal` (`pencilChartNormal_of_pencilHub`). -/
theorem linearIndepOn_pencilChartNormal_closedHubNbhd {G : Graph α β} {v : α}
    (seed : PencilSeed K α) {hubSel nbrSel : α → Fin 3 → Option α}
    (hSel : IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v))
    (hLI : LinearIndependent K
      ![hubSlotNormal seed hubSel v 0, hubSlotNormal seed hubSel v 1,
        hubSlotNormal seed hubSel v 2]) :
    LinearIndepOn K (pencilChartNormal seed hubSel nbrSel G) (G.closedHubNbhd v) := by
  have hf : LinearIndependent K (hubSlotNormal seed hubSel v) :=
    (linearIndependent_hubSlotNormal_iff seed hubSel v).mp hLI
  set F : (G.closedHubNbhd v) → Fin 3 := fun w => (hSel.2.1 w.1 w.2).choose with hF_def
  have hFspec : ∀ w : (G.closedHubNbhd v), hubSel v (F w) = some w.1 := fun w =>
    (hSel.2.1 w.1 w.2).choose_spec
  have hFinj : Function.Injective F := by
    intro w1 w2 hEq
    have h1 := hFspec w1
    rw [hEq, hFspec w2] at h1
    exact Subtype.ext (Option.some_injective _ h1.symm)
  have hcomp : LinearIndependent K (hubSlotNormal seed hubSel v ∘ F) := hf.comp F hFinj
  have heq2 : hubSlotNormal seed hubSel v ∘ F
      = fun w : (G.closedHubNbhd v) => pencilChartNormal seed hubSel nbrSel G w.1 := by
    funext w
    have hw_hub : G.PencilHub w.1 := w.2.1
    simp only [Function.comp_apply, hubSlotNormal, hFspec w,
      pencilChartNormal_of_pencilHub seed hubSel nbrSel hw_hub]
  rwa [heq2] at hcomp

/-- **The three slots of the neighbour selector as a triple** (a step of
`lem:pencil-generic-steer`): the triple `![f 0, f 1, f 2]` for
`f = nbrSlotPoint seed hubSel nbrSel v` is `f`, so the two are independent together. -/
theorem linearIndependent_nbrSlotPoint_iff (seed : PencilSeed K α)
    (hubSel nbrSel : α → Fin 3 → Option α) (v : α) :
    LinearIndependent K
      ![nbrSlotPoint seed hubSel nbrSel v 0, nbrSlotPoint seed hubSel nbrSel v 1,
        nbrSlotPoint seed hubSel nbrSel v 2] ↔
      LinearIndependent K (nbrSlotPoint seed hubSel nbrSel v) := by
  rw [show (![nbrSlotPoint seed hubSel nbrSel v 0, nbrSlotPoint seed hubSel nbrSel v 1,
      nbrSlotPoint seed hubSel nbrSel v 2] : Fin 3 → Fin 4 → K)
      = nbrSlotPoint seed hubSel nbrSel v from by funext j; fin_cases j <;> rfl]

/-- **The points of the chart are independent on a closed neighbourhood** (a step of
`lem:pencil-generic-steer`; a condition of `def:pencil-nondegenerate`): if `nbrSel v` lists
`G.closedNbhd v` and its three slots are independent, then `pencilChartPoint` is linearly
independent on `G.closedNbhd v`. The proof is that of
`linearIndepOn_pencilChartNormal_closedHubNbhd`, where the slot that holds `w` is the point of `w`
(`nbrSlotPoint`). -/
theorem linearIndepOn_pencilChartPoint_closedNbhd {G : Graph α β} {v : α}
    (seed : PencilSeed K α) {hubSel nbrSel : α → Fin 3 → Option α}
    (hSel : IsFin3SelectorOf (G.closedNbhd v) (nbrSel v))
    (hLI : LinearIndependent K
      ![nbrSlotPoint seed hubSel nbrSel v 0, nbrSlotPoint seed hubSel nbrSel v 1,
        nbrSlotPoint seed hubSel nbrSel v 2]) :
    LinearIndepOn K (pencilChartPoint seed hubSel) (G.closedNbhd v) := by
  have hf : LinearIndependent K (nbrSlotPoint seed hubSel nbrSel v) :=
    (linearIndependent_nbrSlotPoint_iff seed hubSel nbrSel v).mp hLI
  set F : (G.closedNbhd v) → Fin 3 := fun w => (hSel.2.1 w.1 w.2).choose with hF_def
  have hFspec : ∀ w : (G.closedNbhd v), nbrSel v (F w) = some w.1 := fun w =>
    (hSel.2.1 w.1 w.2).choose_spec
  have hFinj : Function.Injective F := by
    intro w1 w2 hEq
    have h1 := hFspec w1
    rw [hEq, hFspec w2] at h1
    exact Subtype.ext (Option.some_injective _ h1.symm)
  have hcomp : LinearIndependent K (nbrSlotPoint seed hubSel nbrSel v ∘ F) := hf.comp F hFinj
  have heq2 : nbrSlotPoint seed hubSel nbrSel v ∘ F
      = fun w : (G.closedNbhd v) => pencilChartPoint seed hubSel w.1 := by
    funext w
    simp only [Function.comp_apply, nbrSlotPoint, hFspec w]
  rwa [heq2] at hcomp

/-- **The point of a body is orthogonal to its normal** (a step of `lem:pencil-generic-steer`):
`point v ⬝ᵥ normal v = 0` at every body `v`, hub or not, when its selectors list their sets. It is
the case `w = v` of `dotProduct_pencilChartPoint_hubNormal_of_mem_closedHubNbhd` at a hub, and of
`dotProduct_pencilChartPoint_pencilChartNormal_of_mem_closedNbhd` elsewhere. -/
theorem dotProduct_pencilChartPoint_pencilChartNormal_self
    {G : Graph α β} {v : α} (seed : PencilSeed K α) {hubSel nbrSel : α → Fin 3 → Option α}
    (hHubSel : IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v))
    (hNbrSel : ¬ G.PencilHub v → IsFin3SelectorOf (G.closedNbhd v) (nbrSel v)) :
    pencilChartPoint seed hubSel v ⬝ᵥ pencilChartNormal seed hubSel nbrSel G v = 0 := by
  by_cases hv : G.PencilHub v
  · rw [pencilChartNormal_of_pencilHub seed hubSel nbrSel hv]
    exact dotProduct_pencilChartPoint_hubNormal_of_mem_closedHubNbhd seed hHubSel ⟨hv, Or.inl rfl⟩
  · exact dotProduct_pencilChartPoint_pencilChartNormal_of_mem_closedNbhd seed hv (hNbrSel hv)
      (Or.inl rfl)

/-- **The point of a body is orthogonal to the normal of each neighbour** (a step of
`lem:pencil-generic-steer`): for a link `e` from `u` to `v`, `point v ⬝ᵥ normal u = 0` when the
selectors list their sets. If `u` is a hub, it lies in the closed hub-neighbourhood of `v`, whose
point is orthogonal to `hubNormal u`; otherwise `v` lies in the closed neighbourhood of `u`, whose
normal is orthogonal to `point v`. At the reversed link it gives `point u ⬝ᵥ normal v = 0`. -/
theorem dotProduct_pencilChartPoint_pencilChartNormal_of_isLink
    {G : Graph α β} {e : β} {u v : α} (seed : PencilSeed K α) {hubSel nbrSel : α → Fin 3 → Option α}
    (hHubSel : ∀ w, IsFin3SelectorOf (G.closedHubNbhd w) (hubSel w))
    (hNbrSel : ∀ w, ¬ G.PencilHub w → IsFin3SelectorOf (G.closedNbhd w) (nbrSel w))
    (hlink : G.IsLink e u v) :
    pencilChartPoint seed hubSel v ⬝ᵥ pencilChartNormal seed hubSel nbrSel G u = 0 := by
  by_cases hu : G.PencilHub u
  · rw [pencilChartNormal_of_pencilHub seed hubSel nbrSel hu]
    exact dotProduct_pencilChartPoint_hubNormal_of_mem_closedHubNbhd seed (hHubSel v)
      ⟨hu, Or.inr ⟨e, hlink.symm⟩⟩
  · exact dotProduct_pencilChartPoint_pencilChartNormal_of_mem_closedNbhd seed hu (hNbrSel u hu)
      (Or.inr ⟨e, hlink⟩)

/-! ## The framework of the chart -/

open Classical in
/-- **The framework of the chart** (the framework of `lem:pencil-generic-steer`'s parametrization):
at an edge `e ∈ E(G)`, whose ends `Graph.endsOf` gives (`Induction/Operations.lean`), the hinge is
the join `extensor ![point (G.endsOf e).1, point (G.endsOf e).2]` of their points
(`pencilChartPoint`). Every other label gets the join of two standard basis vectors, a fixed nonzero
extensor, as every supporting extensor of a hinge-coplanar realization must be nonzero. -/
noncomputable def pencilChartFramework [Inhabited α] (seed : PencilSeed K α)
    (hubSel : α → Fin 3 → Option α) (G : Graph α β) : BodyHingeFramework K 2 α β where
  graph := G
  supportExtensor e :=
    if e ∈ E(G) then
      ScrewSpace.mk (extensor ![pencilChartPoint seed hubSel (G.endsOf e).1,
        pencilChartPoint seed hubSel (G.endsOf e).2]) (extensor_mem_exteriorPower _)
    else
      ScrewSpace.mk (extensor ![(![1, 0, 0, 0] : Fin 4 → K), (![0, 1, 0, 0] : Fin 4 → K)])
        (extensor_mem_exteriorPower _)

@[simp]
theorem pencilChartFramework_graph [Inhabited α] (seed : PencilSeed K α)
    (hubSel : α → Fin 3 → Option α) (G : Graph α β) :
    (pencilChartFramework seed hubSel G).graph = G := rfl

/-- **The hinge of the chart framework at an edge of `G`** (a step of `lem:pencil-generic-steer`):
the `if` of `pencilChartFramework` at `e ∈ E(G)`. -/
theorem pencilChartFramework_supportExtensor_of_mem_edgeSet [Inhabited α] (seed : PencilSeed K α)
    (hubSel : α → Fin 3 → Option α) {G : Graph α β} {e : β} (he : e ∈ E(G)) :
    (pencilChartFramework seed hubSel G).supportExtensor e =
      ScrewSpace.mk (extensor ![pencilChartPoint seed hubSel (G.endsOf e).1,
        pencilChartPoint seed hubSel (G.endsOf e).2]) (extensor_mem_exteriorPower _) :=
  ite_eq_left he

/-- **The hinge of the chart framework at a label off `E(G)`** (a step of
`lem:pencil-generic-steer`): the fixed join of two standard basis vectors. -/
theorem pencilChartFramework_supportExtensor_of_not_mem_edgeSet [Inhabited α]
    (seed : PencilSeed K α) (hubSel : α → Fin 3 → Option α) {G : Graph α β} {e : β}
    (he : e ∉ E(G)) :
    (pencilChartFramework seed hubSel G).supportExtensor e =
      ScrewSpace.mk (extensor ![(![1, 0, 0, 0] : Fin 4 → K), (![0, 1, 0, 0] : Fin 4 → K)])
        (extensor_mem_exteriorPower _) :=
  ite_eq_right he

/-- **The join of two standard basis vectors is nonzero**: `![1, 0, 0, 0]` and `![0, 1, 0, 0]` are
linearly independent, by their first two coordinates, so their extensor is nonzero
(`extensor_ne_zero_iff_linearIndependent`). -/
theorem extensor_stdBasis_pair_ne_zero :
    extensor (![(![1, 0, 0, 0] : Fin 4 → K), (![0, 1, 0, 0] : Fin 4 → K)]) ≠ 0 := by
  rw [extensor_ne_zero_iff_linearIndependent, LinearIndependent.pair_iff]
  intro c1 c2 h
  have h0 := congr_fun h 0
  have h1 := congr_fun h 1
  simp only [Pi.add_apply, Pi.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    smul_eq_mul, mul_one, mul_zero, add_zero, zero_add, Pi.zero_apply] at h0 h1
  exact ⟨h0, h1⟩

/-! ## The incidences of a point join -/

/-- **A point join lies in the panels of both ends** (a step of `lem:pencil-generic-steer`): for a
link `e` from `u` to `v`, the extensor of `![point u, point v]` lies in the panels of `normal u` and
`normal v` (`ExtensorInPanel`) when the selectors list their sets. The family `![point u, point v]`
witnesses both: each point is orthogonal to its own normal
(`dotProduct_pencilChartPoint_pencilChartNormal_self`) and to that of the other end
(`dotProduct_pencilChartPoint_pencilChartNormal_of_isLink`). -/
theorem extensorInPanel_pointJoin_pencilChartNormal_of_isLink
    {G : Graph α β} {e : β} {u v : α} (seed : PencilSeed K α) {hubSel nbrSel : α → Fin 3 → Option α}
    (hHubSel : ∀ w, IsFin3SelectorOf (G.closedHubNbhd w) (hubSel w))
    (hNbrSel : ∀ w, ¬ G.PencilHub w → IsFin3SelectorOf (G.closedNbhd w) (nbrSel w))
    (hlink : G.IsLink e u v) :
    ExtensorInPanel
      (ScrewSpace.mk (extensor ![pencilChartPoint seed hubSel u, pencilChartPoint seed hubSel v])
        (extensor_mem_exteriorPower _))
      (pencilChartNormal seed hubSel nbrSel G u) ∧
    ExtensorInPanel
      (ScrewSpace.mk (extensor ![pencilChartPoint seed hubSel u, pencilChartPoint seed hubSel v])
        (extensor_mem_exteriorPower _))
      (pencilChartNormal seed hubSel nbrSel G v) := by
  refine ⟨⟨![pencilChartPoint seed hubSel u, pencilChartPoint seed hubSel v], ScrewSpace.val_mk _ _,
    fun i => ?_⟩, ⟨![pencilChartPoint seed hubSel u, pencilChartPoint seed hubSel v],
    ScrewSpace.val_mk _ _, fun i => ?_⟩⟩
  · fin_cases i
    · exact dotProduct_pencilChartPoint_pencilChartNormal_self seed (hHubSel u) (hNbrSel u)
    · exact dotProduct_pencilChartPoint_pencilChartNormal_of_isLink seed hHubSel hNbrSel hlink
  · fin_cases i
    · exact dotProduct_pencilChartPoint_pencilChartNormal_of_isLink seed hHubSel hNbrSel hlink.symm
    · exact dotProduct_pencilChartPoint_pencilChartNormal_self seed (hHubSel v) (hNbrSel v)

/-- **A point join passes through both its points** (a step of `lem:pencil-generic-steer`): the
extensor of `![point u, point v]` passes through `point u` and through `point v`
(`ExtensorThroughPoint`), with no hypothesis, as both lie in the span of the family. -/
theorem extensorThroughPoint_pointJoin_self {u v : α} (seed : PencilSeed K α)
    {hubSel : α → Fin 3 → Option α} :
    ExtensorThroughPoint
      (ScrewSpace.mk (extensor ![pencilChartPoint seed hubSel u, pencilChartPoint seed hubSel v])
        (extensor_mem_exteriorPower _))
      (pencilChartPoint seed hubSel u) ∧
    ExtensorThroughPoint
      (ScrewSpace.mk (extensor ![pencilChartPoint seed hubSel u, pencilChartPoint seed hubSel v])
        (extensor_mem_exteriorPower _))
      (pencilChartPoint seed hubSel v) :=
  ⟨⟨![pencilChartPoint seed hubSel u, pencilChartPoint seed hubSel v], ScrewSpace.val_mk _ _,
      Submodule.subset_span ⟨0, rfl⟩⟩,
    ⟨![pencilChartPoint seed hubSel u, pencilChartPoint seed hubSel v], ScrewSpace.val_mk _ _,
      Submodule.subset_span ⟨1, rfl⟩⟩⟩

/-! ## The chart is a nondegenerate pencil realization -/

/-- **At well-formed parameters the chart is a hinge-coplanar panel realization** (a step of
`lem:pencil-generic-steer`): `HasCoplanarPanelRealization` of `pencilChartFramework` and
`pencilChartNormal`. The graph is `G`; the normal is nonzero at a hub
(`hubNormal_ne_zero_of_pencilHub`) and elsewhere (`pencilChartNormal_ne_zero_of_not_pencilHub`); the
hinge is nonzero at an edge, as the points of its ends are independent, and off `E(G)`
(`extensor_stdBasis_pair_ne_zero`); and at a link it lies in the panels of both ends
(`extensorInPanel_pointJoin_pencilChartNormal_of_isLink`), at the ends `Graph.endsOf` gives, which
are those of the link up to order (`IsLink.eq_and_eq_or_eq_and_eq`). -/
theorem hasCoplanarPanelRealization_pencilChartFramework [Inhabited α]
    {G : Graph α β} {seed : PencilSeed K α} {hubSel nbrSel : α → Fin 3 → Option α}
    (hWF : PencilChartWF G seed hubSel nbrSel) :
    HasCoplanarPanelRealization G (pencilChartFramework seed hubSel G)
      (pencilChartNormal seed hubSel nbrSel G) := by
  obtain ⟨hHubSel, hNbrSel, hHubLI, hNbrLI, hPtLI⟩ := hWF
  refine ⟨pencilChartFramework_graph seed hubSel G, ?_, ?_, ?_⟩
  · intro v _
    by_cases hv : G.PencilHub v
    · rw [pencilChartNormal_of_pencilHub seed hubSel nbrSel hv]
      exact hubNormal_ne_zero_of_pencilHub seed (hHubSel v) (hHubLI v) hv
    · exact pencilChartNormal_ne_zero_of_not_pencilHub seed hv (hNbrLI v hv)
  · intro e
    by_cases he : e ∈ E(G)
    · rw [pencilChartFramework_supportExtensor_of_mem_edgeSet seed hubSel he]
      have hlink0 : G.IsLink e (G.endsOf e).1 (G.endsOf e).2 := G.isLink_endsOf he
      intro hz
      have hval := congrArg ScrewSpace.val hz
      rw [ScrewSpace.val_mk, ScrewSpace.val_zero] at hval
      exact (extensor_ne_zero_iff_linearIndependent _).mpr (hPtLI e _ _ hlink0) hval
    · rw [pencilChartFramework_supportExtensor_of_not_mem_edgeSet seed hubSel he]
      intro hz
      have hval := congrArg ScrewSpace.val hz
      rw [ScrewSpace.val_mk, ScrewSpace.val_zero] at hval
      exact extensor_stdBasis_pair_ne_zero hval
  · intro e u v hlink
    have he : e ∈ E(G) := hlink.edge_mem
    rw [pencilChartFramework_supportExtensor_of_mem_edgeSet seed hubSel he]
    have hlink0 : G.IsLink e (G.endsOf e).1 (G.endsOf e).2 := G.isLink_endsOf he
    rcases hlink0.eq_and_eq_or_eq_and_eq hlink with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact extensorInPanel_pointJoin_pencilChartNormal_of_isLink seed hHubSel hNbrSel hlink0
    · exact ⟨(extensorInPanel_pointJoin_pencilChartNormal_of_isLink seed hHubSel hNbrSel hlink0).2,
        (extensorInPanel_pointJoin_pencilChartNormal_of_isLink seed hHubSel hNbrSel hlink0).1⟩

/-- **At well-formed parameters the chart is a pencil realization** (a step of
`lem:pencil-generic-steer`): `HasPencilPanelRealization` of the chart, from the hinge-coplanar
realization above, the nonzero points (`pencilChartPoint_ne_zero`), the incidence
`point v ⬝ᵥ normal v = 0` (`dotProduct_pencilChartPoint_pencilChartNormal_self`), and the pencil
condition at every link, which holds with no hypothesis, as the hinge is the join of the points of
its ends (`extensorThroughPoint_pointJoin_self`). -/
theorem hasPencilPanelRealization_pencilChartFramework [Inhabited α]
    {G : Graph α β} {seed : PencilSeed K α} {hubSel nbrSel : α → Fin 3 → Option α}
    (hWF : PencilChartWF G seed hubSel nbrSel) :
    HasPencilPanelRealization G (pencilChartFramework seed hubSel G)
      (pencilChartNormal seed hubSel nbrSel G) (pencilChartPoint seed hubSel) := by
  have hHubSel := hWF.1
  have hNbrSel := hWF.2.1
  have hHubLI := hWF.2.2.1
  refine ⟨hasCoplanarPanelRealization_pencilChartFramework hWF, ?_, ?_, ?_⟩
  · intro v _; exact pencilChartPoint_ne_zero seed (hHubLI v)
  · intro v _; exact dotProduct_pencilChartPoint_pencilChartNormal_self seed (hHubSel v) (hNbrSel v)
  · intro e u v hlink
    have he : e ∈ E(G) := hlink.edge_mem
    rw [pencilChartFramework_supportExtensor_of_mem_edgeSet seed hubSel he]
    have hlink0 : G.IsLink e (G.endsOf e).1 (G.endsOf e).2 := G.isLink_endsOf he
    rcases hlink0.eq_and_eq_or_eq_and_eq hlink with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact extensorThroughPoint_pointJoin_self seed
    · exact ⟨(extensorThroughPoint_pointJoin_self seed (u := (G.endsOf e).1)
        (v := (G.endsOf e).2)).2,
        (extensorThroughPoint_pointJoin_self seed (u := (G.endsOf e).1)
        (v := (G.endsOf e).2)).1⟩

/-- **At well-formed parameters the chart is a nondegenerate pencil realization** (a step of
`lem:pencil-generic-steer`): `IsNondegPencilRealization` of `pencilChartFramework`,
`pencilChartNormal` and `pencilChartPoint`. Its four conditions are
`hasPencilPanelRealization_pencilChartFramework`, the independence of the points of a link
(`PencilChartWF`), `linearIndepOn_pencilChartNormal_closedHubNbhd` and
`linearIndepOn_pencilChartPoint_closedNbhd`. -/
theorem isNondegPencilRealization_pencilChartFramework_of_pencilChartWF [Inhabited α]
    {G : Graph α β} {seed : PencilSeed K α} {hubSel nbrSel : α → Fin 3 → Option α}
    (hWF : PencilChartWF G seed hubSel nbrSel) :
    IsNondegPencilRealization G (pencilChartFramework seed hubSel G)
      (pencilChartNormal seed hubSel nbrSel G) (pencilChartPoint seed hubSel) := by
  have hHubSel := hWF.1
  have hNbrSel := hWF.2.1
  have hHubLI := hWF.2.2.1
  have hNbrLI := hWF.2.2.2.1
  have hPtLI := hWF.2.2.2.2
  exact ⟨hasPencilPanelRealization_pencilChartFramework hWF, hPtLI,
    fun v _ => linearIndepOn_pencilChartNormal_closedHubNbhd seed (hHubSel v) (hHubLI v),
    fun v _ hv => linearIndepOn_pencilChartPoint_closedNbhd seed (hNbrSel v hv) (hNbrLI v hv)⟩

end CombinatorialRigidity.Molecular
