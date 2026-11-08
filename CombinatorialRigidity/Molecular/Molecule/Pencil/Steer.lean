/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Reseed

/-!
# Parameters as coordinates, and new parameters at a common non-root

Steps of the proof of `lem:pencil-generic-steer` (`sec:main-component-statements`),
which `MainComponent/GenericSteer.lean` puts together: realizations written in the chart
(`Reseed.lean`) give the conditions asked, each at some coordinate point, and a common non-root of
the polynomials of these conditions (`Engine.lean`) gives parameters of the chart at which all of
them hold.

The polynomials of `Engine.lean` evaluate at coordinate points `q`, whose parameters
`PencilSeed.ofCoord q` have the same padding in `fillHub` and `fillNbr`. `PencilSeed.toCoord` writes
any parameters as a coordinate point, from their `hubNormal` and `fillHub`, and the points of the
chart at `PencilSeed.ofCoord seed.toCoord` are those at `seed` (`pencilChartPoint_ofCoord_toCoord`),
as the points do not read `fillNbr`. Of the conditions of `PencilChartWF`, only the fourth, the
independence of the slots of the neighbour selector at a body that is not a hub, reads `fillNbr`, at
the empty slots of a body whose closed neighbourhood has fewer than three members. At a common
non-root, `exists_fillNbr_pencilChartWF_of_standing` chooses `fillNbr` again so that it holds: the
points at the filled slots of each such body are independent, and `exists_extend_linearIndependent`
(`Reseed.lean`) completes them. This does not change the points (`pencilChartPoint_congr`).

Over an infinite field, finitely many sets, on each of which the points of the chart are independent
at some coordinate point, have one at which they are independent on all of them
(`exists_common_seed_linearIndepOn_pencilChartPoint`). Proportional hinges give the same rigidity
rows (`span_rigidityRows_eq_of_supportExtensor_proportional`).

## Main definitions

* `PencilSeed.toCoord`: parameters as a coordinate point.

## Main results

* `pencilChartPoint_ofCoord_toCoord`: the points of the chart at `PencilSeed.ofCoord seed.toCoord`
  are those at `seed`.
* `exists_fillNbr_pencilChartWF_of_standing`: a new `fillNbr` makes parameters well formed.
* `exists_common_seed_linearIndepOn_pencilChartPoint`: points independent on finitely many sets at
  one coordinate point.
* `span_rigidityRows_eq_of_supportExtensor_proportional`: proportional hinges give the same rigidity
  rows.
-/

@[expose] public section

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K]
variable {α β : Type*}

/-! ## Parameters as a coordinate point -/

/-- **Parameters as a coordinate point** (a step of `lem:pencil-generic-steer`): the coordinate `i`
of the vector `0` at a body `v` is `hubNormal v i`, and that of the vector `j.succ` is
`fillHub v j i`, the two fields that `PencilSeed.ofCoord` reads back
(`PencilSeed.ofCoord_toCoord_hubNormal`, `PencilSeed.ofCoord_toCoord_fillHub`). The padding
`fillNbr` is lost, as `PencilSeed.ofCoord` gives `fillNbr` the padding of `fillHub`; the points of
the chart do not read it (`pencilChartPoint_ofCoord_toCoord`). -/
def PencilSeed.toCoord (seed : PencilSeed K α) (p : α × Fin 4 × Fin 4) : K :=
  (Fin.cons (seed.hubNormal p.1 p.2.2) (fun j => seed.fillHub p.1 j p.2.2) : Fin 4 → K) p.2.1

/-- **`PencilSeed.ofCoord` reads back `hubNormal`** from `PencilSeed.toCoord`, at the vector `0`
(`Fin.cons_zero`). -/
theorem PencilSeed.ofCoord_toCoord_hubNormal (seed : PencilSeed K α) :
    (PencilSeed.ofCoord seed.toCoord).hubNormal = seed.hubNormal := by
  funext v i
  simp only [PencilSeed.ofCoord, PencilSeed.toCoord, Fin.cons_zero]

/-- **`PencilSeed.ofCoord` reads back `fillHub`** from `PencilSeed.toCoord`, at the vectors `j.succ`
(`Fin.cons_succ`). -/
theorem PencilSeed.ofCoord_toCoord_fillHub (seed : PencilSeed K α) :
    (PencilSeed.ofCoord seed.toCoord).fillHub = seed.fillHub := by
  funext v j i
  simp only [PencilSeed.ofCoord, PencilSeed.toCoord, Fin.cons_succ]

/-! ## The same points -/

/-- **Parameters with the same `hubNormal` and `fillHub` have the same points** (a step of
`lem:pencil-generic-steer`): the slots of the hub selector read only these two fields
(`hubSlotNormal`). So a new `fillNbr` (`exists_fillNbr_pencilChartWF_of_standing`) keeps every
condition on the points, and so does the read-back of a coordinate point
(`pencilChartPoint_ofCoord_toCoord`). -/
theorem pencilChartPoint_congr {seed seed' : PencilSeed K α} (hubSel : α → Fin 3 → Option α)
    (hhub : seed'.hubNormal = seed.hubNormal) (hfill : seed'.fillHub = seed.fillHub) :
    pencilChartPoint seed' hubSel = pencilChartPoint seed hubSel := by
  funext v
  have hslot : ∀ i, hubSlotNormal seed' hubSel v i = hubSlotNormal seed hubSel v i := by
    intro i
    unfold hubSlotNormal
    cases hubSel v i with
    | none => rw [hfill]
    | some w => rw [hhub]
  simp only [pencilChartPoint, hslot]

/-- **The points of the chart at `PencilSeed.ofCoord seed.toCoord` are those at `seed`** (a step of
`lem:pencil-generic-steer`): `PencilSeed.ofCoord` reads back `hubNormal` and `fillHub`
(`PencilSeed.ofCoord_toCoord_hubNormal`, `PencilSeed.ofCoord_toCoord_fillHub`), and the points
read no other field (`pencilChartPoint_congr`). So a condition on the points that holds at `seed`
holds at the coordinate point `seed.toCoord`, where the polynomials of `Engine.lean` evaluate. -/
theorem pencilChartPoint_ofCoord_toCoord (seed : PencilSeed K α) (hubSel : α → Fin 3 → Option α)
    (v : α) :
    pencilChartPoint (PencilSeed.ofCoord seed.toCoord) hubSel v
      = pencilChartPoint seed hubSel v :=
  congrFun (pencilChartPoint_congr hubSel (PencilSeed.ofCoord_toCoord_hubNormal seed)
    (PencilSeed.ofCoord_toCoord_fillHub seed)) v

/-! ## A new `fillNbr` -/

/-- **A new `fillNbr` makes the parameters well formed** (a step of `lem:pencil-generic-steer`):
given the conditions of `PencilChartWF` that do not read `fillNbr` (`hsel_hub`, `hsel_nbr`,
`hhub_LI` and `hpt_LI`: the two selectors list their sets, the slots of the hub selector are
independent, and so are the points of the two ends of each link), and, at each body that is not a
hub, the independence of the slots that the neighbour selector fills (`hnbr_some`), there are
parameters `seed'` with the `hubNormal` and `fillHub` of `seed` that are well formed. At each body
that is not a hub, `exists_extend_linearIndependent` completes the points at the filled slots to an
independent triple, whose vectors at the empty slots are the new `fillNbr`. The points of the chart
do not read `fillNbr`, so they do not change, and neither do the four other conditions. -/
theorem exists_fillNbr_pencilChartWF_of_standing {G : Graph α β} {seed : PencilSeed K α}
    {hubSel nbrSel : α → Fin 3 → Option α}
    (hsel_hub : ∀ v, IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v))
    (hsel_nbr : ∀ v, ¬ G.PencilHub v → IsFin3SelectorOf (G.closedNbhd v) (nbrSel v))
    (hhub_LI : ∀ v, LinearIndependent K
      ![hubSlotNormal seed hubSel v 0, hubSlotNormal seed hubSel v 1,
        hubSlotNormal seed hubSel v 2])
    (hpt_LI : ∀ e u v, G.IsLink e u v → LinearIndependent K
      ![pencilChartPoint seed hubSel u, pencilChartPoint seed hubSel v])
    (hnbr_some : ∀ v, ¬ G.PencilHub v →
      LinearIndepOn K (nbrSlotPoint seed hubSel nbrSel v) {i | (nbrSel v i).isSome}) :
    ∃ seed' : PencilSeed K α, seed'.hubNormal = seed.hubNormal ∧ seed'.fillHub = seed.fillHub ∧
      PencilChartWF G seed' hubSel nbrSel := by
  have hn : Fintype.card (Fin 3) ≤ Module.finrank K (Fin 4 → K) := by
    rw [Module.finrank_fin_fun, Fintype.card_fin]; norm_num
  have key : ∀ v, ∃ f : Fin 3 → Fin 4 → K, ¬ G.PencilHub v →
      (∀ i, (nbrSel v i).isSome = true → f i = nbrSlotPoint seed hubSel nbrSel v i) ∧
        LinearIndependent K f := by
    intro v
    by_cases hv : G.PencilHub v
    · exact ⟨fun _ _ => 0, fun h => absurd hv h⟩
    · obtain ⟨g', hg'eq, hg'LI⟩ := exists_extend_linearIndependent hn
        (nbrSlotPoint seed hubSel nbrSel v)
        (Finset.univ.filter (fun i => (nbrSel v i).isSome))
        (by
          have h := hnbr_some v hv
          rwa [show ({i | (nbrSel v i).isSome = true} : Set (Fin 3))
              = ((Finset.univ.filter (fun i => (nbrSel v i).isSome)) : Set (Fin 3)) from by
            ext i; simp] at h)
      exact ⟨g', fun _ => ⟨fun i hi => hg'eq i (by simp [hi]), hg'LI⟩⟩
  choose fillNbr' hfillNbr' using key
  refine ⟨⟨seed.hubNormal, seed.fillHub, fillNbr'⟩, rfl, rfl, hsel_hub, hsel_nbr, hhub_LI, ?_,
    hpt_LI⟩
  intro v hv
  obtain ⟨hsome, hLI⟩ := hfillNbr' v hv
  have hfun : (fun i => nbrSlotPoint (⟨seed.hubNormal, seed.fillHub, fillNbr'⟩ : PencilSeed K α)
      hubSel nbrSel v i) = fillNbr' v := by
    funext i
    rcases hi : nbrSel v i with _ | w
    · simp only [nbrSlotPoint, hi]
    · rw [hsome i (by rw [hi]; rfl)]
      simp only [nbrSlotPoint, pencilChartPoint, hubSlotNormal, hi]
  have hmat : ![nbrSlotPoint (⟨seed.hubNormal, seed.fillHub, fillNbr'⟩ : PencilSeed K α)
        hubSel nbrSel v 0,
      nbrSlotPoint (⟨seed.hubNormal, seed.fillHub, fillNbr'⟩ : PencilSeed K α) hubSel nbrSel v 1,
      nbrSlotPoint (⟨seed.hubNormal, seed.fillHub, fillNbr'⟩ : PencilSeed K α) hubSel nbrSel v 2]
        = fillNbr' v := by
    rw [← hfun]; funext i; fin_cases i <;> rfl
  rw [hmat]; exact hLI

/-! ## Points independent on finitely many sets at one coordinate point -/

/-- **Points of the chart independent on finitely many sets at one coordinate point** (a step of
`lem:pencil-generic-steer`): over an infinite field, with finitely many bodies, if for each of
finitely many sets `S i` the points of the chart are linearly independent on `S i` at some
coordinate point, then at one coordinate point they are independent on every `S i`. Each condition
holds off the zero set of a polynomial nonzero at its own coordinate point
(`exists_polynomial_ne_zero_of_linearIndependent_pencilChartPoint`, `Engine.lean`, at `ends := id`),
and these polynomials have a common non-root (`exists_common_eval_ne_zero_of_forall_exists`).
`exists_isNondegPencilRealization_restrict_of_demoted` (`MainComponent/GenericSteer.lean`) uses it
with the sets `{v}` at a hub `v` of `G`, the closed neighbourhood of every other body, the two ends
of every pair of adjacent bodies, and the closed neighbourhood in `H` of each hub of `G` that is a
body but not a hub of `H`. -/
theorem exists_common_seed_linearIndepOn_pencilChartPoint [Finite α] [Infinite K]
    {ι : Type*} [Finite ι] (hubSel : α → Fin 3 → Option α) (S : ι → Set α)
    (h : ∀ i, ∃ q : α × Fin 4 × Fin 4 → K,
      LinearIndepOn K (pencilChartPoint (PencilSeed.ofCoord q) hubSel) (S i)) :
    ∃ q : α × Fin 4 × Fin 4 → K, ∀ i,
      LinearIndepOn K (pencilChartPoint (PencilSeed.ofCoord q) hubSel) (S i) := by
  choose q₀ hq₀ using h
  have hpoly : ∀ i, ∃ Q : MvPolynomial (α × Fin 4 × Fin 4) K,
      MvPolynomial.eval (q₀ i) Q ≠ 0 ∧
      ∀ q, MvPolynomial.eval q Q ≠ 0 →
        LinearIndepOn K (pencilChartPoint (PencilSeed.ofCoord q) hubSel) (S i) :=
    fun i => exists_polynomial_ne_zero_of_linearIndependent_pencilChartPoint hubSel id (hq₀ i)
  choose P hP0 hP using hpoly
  obtain ⟨q, hq⟩ := exists_common_eval_ne_zero_of_forall_exists P (fun i => ⟨q₀ i, hP0 i⟩)
  exact ⟨q, fun i => hP i q (hq i)⟩

/-! ## Independence on a set -/

/-- **Independence of `![f x, f y, f z]` gives independence on `{x, y, z}`**:
`LinearIndependent K ![f x, f y, f z]` gives `LinearIndepOn K f {x, y, z}`, by mathlib's
`linearIndepOn_range_iff` at `![x, y, z]`, whose range is `{x, y, z}`. It is injective, as
`![f x, f y, f z]` is (`LinearIndependent.injective`), so `x`, `y`, `z` are distinct. The converse
of `linearIndependent_triple_of_linearIndepOn` (`Motive.lean`). -/
theorem linearIndepOn_triple_of_linearIndependent {V : Type*} [AddCommGroup V] [Module K V]
    (f : α → V) {x y z : α} (hLI : LinearIndependent K ![f x, f y, f z]) :
    LinearIndepOn K f {x, y, z} := by
  have hinj : Function.Injective ![x, y, z] := by
    refine Function.Injective.of_comp (f := f) ?_
    convert hLI.injective using 1
    funext i; fin_cases i <;> rfl
  have hr : Set.range ![x, y, z] = {x, y, z} := by
    simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rw [← hr, linearIndepOn_range_iff hinj]
  convert hLI using 1
  funext i; fin_cases i <;> rfl

/-- **The filled slots of a neighbour selector are independent when the points of the closed
neighbourhood are** (a step of `lem:pencil-generic-steer`): if `nbrSel v` lists `G.closedNbhd v` and
the points of the chart are linearly independent on `G.closedNbhd v`, then
`nbrSlotPoint seed hubSel nbrSel v` is linearly independent on the slots that `nbrSel v` fills. Such
a slot holds the point of its member (`nbrSlotPoint`), and these slots are the members, one each
(`IsFin3SelectorOf.exists_equiv_isSome`, `Chart.lean`). A partial converse of
`linearIndepOn_pencilChartPoint_closedNbhd` (`Chart.lean`). -/
theorem linearIndepOn_nbrSlotPoint_isSome_of_pencilChartPoint {G : Graph α β} {v : α}
    (seed : PencilSeed K α) {hubSel nbrSel : α → Fin 3 → Option α}
    (hSel : IsFin3SelectorOf (G.closedNbhd v) (nbrSel v))
    (hLI : LinearIndepOn K (pencilChartPoint seed hubSel) (G.closedNbhd v)) :
    LinearIndepOn K (nbrSlotPoint seed hubSel nbrSel v) {i | (nbrSel v i).isSome} := by
  obtain ⟨e, he⟩ := hSel.exists_equiv_isSome
  refine (linearIndependent_equiv' e ?_).mpr hLI
  funext i
  simp only [Function.comp_apply, nbrSlotPoint, he i]

/-! ## Proportional hinges -/

/-- **Proportional hinges give the same rigidity rows**: for two frameworks on the same graph, with
`c • F₁.supportExtensor e = F₂.supportExtensor e` for some `c ≠ 0` at every link `e`, the rigidity
rows are the same, and so is their span. The rows at a link are given by the forms of
`hingeRowBlock e`, those that vanish on the line of the hinge (`hingeRowBlock_apply`), and a
nonzero multiple spans the same line (`Submodule.span_singleton_smul_eq`). The lift uses it when it
rescales normals (`Grade/Lift.lean`, `Grade/LiftWitness.lean`). -/
theorem span_rigidityRows_eq_of_supportExtensor_proportional {k : ℕ}
    (F₁ F₂ : BodyHingeFramework K k α β) (hg : F₁.graph = F₂.graph)
    (hprop : ∀ e u v, F₁.graph.IsLink e u v →
      ∃ c : K, c ≠ 0 ∧ c • F₁.supportExtensor e = F₂.supportExtensor e) :
    Submodule.span K F₁.rigidityRows = Submodule.span K F₂.rigidityRows := by
  have hblock : ∀ e u v, F₁.graph.IsLink e u v → F₁.hingeRowBlock e = F₂.hingeRowBlock e := by
    intro e u v hlink
    obtain ⟨c, hc, hceq⟩ := hprop e u v hlink
    have hspan : Submodule.span K {F₂.supportExtensor e}
        = Submodule.span K {F₁.supportExtensor e} := by
      rw [← hceq]; exact Submodule.span_singleton_smul_eq hc.isUnit _
    rw [F₁.hingeRowBlock_apply, F₂.hingeRowBlock_apply, hspan]
  have hset : F₁.rigidityRows = F₂.rigidityRows := by
    ext φ
    constructor
    · rintro ⟨e, u, v, hlink, r, hr, rfl⟩
      exact ⟨e, u, v, hg ▸ hlink, r, hblock e u v hlink ▸ hr, rfl⟩
    · rintro ⟨e, u, v, hlink, r, hr, rfl⟩
      have hlink₁ : F₁.graph.IsLink e u v := by rw [hg]; exact hlink
      exact ⟨e, u, v, hlink₁, r, (hblock e u v hlink₁).symm ▸ hr, rfl⟩
  rw [hset]

end CombinatorialRigidity.Molecular
