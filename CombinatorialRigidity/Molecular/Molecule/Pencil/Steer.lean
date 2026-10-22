/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.Engine
import CombinatorialRigidity.Molecular.Molecule.Pencil.Reseed
import CombinatorialRigidity.Molecular.Molecule.Pencil.Witness

/-!
# Parameters as coordinates, and the rank of a realization in the chart

Steps of the proof of `lem:pencil-generic-steer` (`sec:main-component-statements`), which
`MainComponent/GenericSteer.lean` puts together: realizations written in the chart (`Reseed.lean`)
give the conditions asked, each at some coordinate point, and a common non-root of the polynomials
of these conditions (`Engine.lean`) gives parameters of the chart at which all of them hold.

The polynomials of `Engine.lean` evaluate at coordinate points `q`, whose parameters
`PencilSeed.ofCoord q` have the same padding in `fillHub` and `fillNbr`. `PencilSeed.toCoord` writes
any parameters as a coordinate point, from their `hubNormal` and `fillHub`, and the points of the
chart at `PencilSeed.ofCoord seed.toCoord` are those at `seed` (`pencilChartPoint_ofCoord_toCoord`),
as the points do not read `fillNbr`. Of the conditions of `PencilChartWF`, only the fourth, the
independence of the slots of the neighbour selector at a body that is not a hub, reads `fillNbr`, at
the empty slots of a body whose closed neighbourhood has fewer than three members. At a common
non-root, `exists_fillNbr_pencilChartWF_of_standing` chooses `fillNbr` again so that it holds: the
points at the filled slots of each such body are independent, and `exists_extend_linearIndependent`
(`Reseed.lean`) completes them. This changes neither the points (`pencilChartPoint_congr`) nor the
framework of the chart (`pencilChartFramework_congr`), nor the normal of a hub or of a body whose
neighbour selector has no empty slot (`pencilChartNormal_congr`).

Over an infinite field, finitely many sets, on each of which the points of the chart are independent
at some coordinate point, have one at which they are independent on all of them
(`exists_common_seed_linearIndepOn_pencilChartPoint`). For the rank: at a link, the hinge of the
chart is a nonzero multiple of that of a nondegenerate realization whose points it gives up to
scalars (`exists_smul_supportExtensor_eq_pencilChartFramework_of_reseed`); proportional hinges give
the same rigidity rows (`span_rigidityRows_eq_of_supportExtensor_proportional`); and at an edge, a
row `pencilRow` of the chart is a rigidity row of its framework
(`pencilRow_mem_rigidityRows_of_mem_edgeSet`). So as many rows `pencilRow` as the rank of the
realization are independent at `seed.toCoord`, and as many rows as the deficiency rank, independent
at a coordinate point where the hinges are nonzero, give the chart that rank there.

## Main definitions

* `PencilSeed.toCoord`: parameters as a coordinate point.

## Main results

* `pencilChartPoint_ofCoord_toCoord`: the points of the chart at `PencilSeed.ofCoord seed.toCoord`
  are those at `seed`.
* `exists_fillNbr_pencilChartWF_of_standing`: a new `fillNbr` makes parameters well formed.
* `exists_common_seed_linearIndepOn_pencilChartPoint`: points independent on finitely many sets at
  one coordinate point.
* `exists_independent_pencilRow_subfamily_at_toCoord_of_reseed`: independent rows of the chart, as
  many as the rank of a realization.
* `finrank_span_rigidityRows_pencilChartFramework_eq_of_independent_pencilRow`: independent rows
  give the chart the deficiency rank.
* `linearIndepOn_pencilChartNormal_congr`: the independence of normals that do not read `fillNbr`
  survives a new `fillNbr`.
-/

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

/-! ## The points of the chart at `PencilSeed.ofCoord seed.toCoord` -/

/-- **The slots of the hub selector at `PencilSeed.ofCoord seed.toCoord` are those at `seed`**: a
slot holds a vector of `hubNormal` or of `fillHub` (`hubSlotNormal`), and both fields are read back.
No slot reads `fillNbr`. -/
theorem hubSlotNormal_ofCoord_toCoord (seed : PencilSeed K α) (hubSel : α → Fin 3 → Option α)
    (v : α) (slot : Fin 3) :
    hubSlotNormal (PencilSeed.ofCoord seed.toCoord) hubSel v slot
      = hubSlotNormal seed hubSel v slot := by
  unfold hubSlotNormal
  cases hubSel v slot with
  | none => rw [PencilSeed.ofCoord_toCoord_fillHub]
  | some w => rw [PencilSeed.ofCoord_toCoord_hubNormal]

/-- **The points of the chart at `PencilSeed.ofCoord seed.toCoord` are those at `seed`** (a step of
`lem:pencil-generic-steer`): each is the `cross₃` of the three slots of the hub selector
(`hubSlotNormal_ofCoord_toCoord`). So a condition on the points that holds at `seed` holds at the
coordinate point `seed.toCoord`, where the polynomials of `Engine.lean` evaluate. -/
theorem pencilChartPoint_ofCoord_toCoord (seed : PencilSeed K α) (hubSel : α → Fin 3 → Option α)
    (v : α) :
    pencilChartPoint (PencilSeed.ofCoord seed.toCoord) hubSel v
      = pencilChartPoint seed hubSel v := by
  simp only [pencilChartPoint, hubSlotNormal_ofCoord_toCoord]

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
  have hn : (3 : ℕ) ≤ Module.finrank K (Fin 4 → K) := by
    rw [Module.finrank_fin_fun]; norm_num
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

/-! ## The same points, and independence on a set -/

/-- **Parameters with the same `hubNormal` and `fillHub` have the same points** (a step of
`lem:pencil-generic-steer`): the slots of the hub selector read only these two fields
(`hubSlotNormal`). So a new `fillNbr` (`exists_fillNbr_pencilChartWF_of_standing`) keeps every
condition on the points. -/
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

/-- **Independence of `![f x, f y, f z]` gives independence on `{x, y, z}`**: for distinct
`x, y, z`, `LinearIndependent K ![f x, f y, f z]` gives `LinearIndepOn K f {x, y, z}`, along the
bijection from `Fin 3` onto `{x, y, z}` that `x`, `y` and `z` define (`linearIndependent_equiv`).
The converse of `linearIndependent_triple_of_linearIndepOn` (`Motive.lean`). Mathlib's
`linearIndepOn_range_iff`, at the injective `![x, y, z]`, gives the same. -/
theorem linearIndepOn_triple_of_linearIndependent {V : Type*} [AddCommGroup V] [Module K V]
    (f : α → V) {x y z : α} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hLI : LinearIndependent K ![f x, f y, f z]) :
    LinearIndepOn K f {x, y, z} := by
  have hx : x ∈ ({x, y, z} : Set α) := by simp
  have hy : y ∈ ({x, y, z} : Set α) := by simp
  have hz : z ∈ ({x, y, z} : Set α) := by simp
  set e : Fin 3 → ↥({x, y, z} : Set α) := ![⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩] with he_def
  have heinj : Function.Injective e := by
    intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [e, Subtype.ext_iff]
  have hesurj : Function.Surjective e := by
    rintro ⟨w, hw⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  set eqv : Fin 3 ≃ ↥({x, y, z} : Set α) := Equiv.ofBijective e ⟨heinj, hesurj⟩ with heqv_def
  rw [← linearIndependent_set_coe_iff]
  have hcomp : (fun w : ↥({x, y, z} : Set α) => f ↑w) ∘ ⇑eqv = ![f x, f y, f z] := by
    funext i; fin_cases i <;> rfl
  exact (linearIndependent_equiv eqv).mp (by rw [hcomp]; exact hLI)

/-- **The filled slots of a neighbour selector are independent when the points of the closed
neighbourhood are** (a step of `lem:pencil-generic-steer`): if `nbrSel v` lists `G.closedNbhd v` and
the points of the chart are linearly independent on `G.closedNbhd v`, then
`nbrSlotPoint seed hubSel nbrSel v` is linearly independent on the slots that `nbrSel v` fills. Such
a slot holds the point of its member (`nbrSlotPoint`), and the map from these slots to their members
is injective, as the selector puts each member in one slot (`LinearIndependent.comp`). A partial
converse of `linearIndepOn_pencilChartPoint_closedNbhd` (`Chart.lean`). -/
theorem linearIndepOn_nbrSlotPoint_isSome_of_pencilChartPoint {G : Graph α β} {v : α}
    (seed : PencilSeed K α) {hubSel nbrSel : α → Fin 3 → Option α}
    (hSel : IsFin3SelectorOf (G.closedNbhd v) (nbrSel v))
    (hLI : LinearIndepOn K (pencilChartPoint seed hubSel) (G.closedNbhd v)) :
    LinearIndepOn K (nbrSlotPoint seed hubSel nbrSel v) {i | (nbrSel v i).isSome} := by
  have hex : ∀ i : ↥{i | (nbrSel v i).isSome}, ∃ w, nbrSel v ↑i = some w :=
    fun i => Option.isSome_iff_exists.mp i.2
  choose wsel hwsel using hex
  set g : ↥{i | (nbrSel v i).isSome} → ↥(G.closedNbhd v) :=
    fun i => ⟨wsel i, hSel.1 ↑i (wsel i) (hwsel i)⟩ with hg_def
  have hginj : Function.Injective g := by
    intro i j hij
    have hval : wsel i = wsel j := congrArg Subtype.val hij
    exact Subtype.ext (hSel.2.2 ↑i ↑j (wsel j) (hval ▸ hwsel i) (hwsel j))
  have hLI' : LinearIndependent K (fun w : ↥(G.closedNbhd v) => pencilChartPoint seed hubSel ↑w) :=
    hLI
  have hcomp := hLI'.comp g hginj
  have heq : (fun w : ↥(G.closedNbhd v) => pencilChartPoint seed hubSel ↑w) ∘ g
      = fun i : ↥{i | (nbrSel v i).isSome} => nbrSlotPoint seed hubSel nbrSel v ↑i := by
    funext i
    simp only [Function.comp_apply, hg_def, nbrSlotPoint, hwsel i]
  rw [← linearIndependent_set_coe_iff, ← heq]; exact hcomp

/-! ## The rows of the chart, and the rank of a realization -/

/-- **At an edge, a row of the chart is a row `panelRow` of its framework** (a step of
`lem:pencil-generic-steer`): at an index `i` whose edge `i.1` is an edge of `G`,
`pencilRow hubSel G.endsOf q i` (`Engine.lean`) is the row `panelRow G.endsOf i` of the framework of
the chart on `G` at `PencilSeed.ofCoord q`, whose hinge at `i.1` is the join of the points of the
ends that `G.endsOf` gives (`pencilChartFramework_supportExtensor_of_mem_edgeSet`). -/
theorem pencilRow_eq_panelRow_pencilChartFramework [Inhabited α]
    (hubSel : α → Fin 3 → Option α) (q : α × Fin 4 × Fin 4 → K) {G : Graph α β}
    {i : β × Set.powersetCard (Fin 4) 2 × Set.powersetCard (Fin 4) 2} (he : i.1 ∈ E(G)) :
    pencilRow hubSel G.endsOf q i
      = (pencilChartFramework (PencilSeed.ofCoord q) hubSel G).panelRow G.endsOf i := by
  rw [pencilRow, BodyHingeFramework.panelRow,
    pencilChartFramework_supportExtensor_of_mem_edgeSet (PencilSeed.ofCoord q) hubSel he]

/-- **At an edge, a row of the chart is a rigidity row of its framework** (a step of
`lem:pencil-generic-steer`): `pencilRow_eq_panelRow_pencilChartFramework`, and
`BodyHingeFramework.panelRow_mem_rigidityRows_of_link` (`Pinning.lean`) at the selector `G.endsOf`,
which gives each edge of `G` its ends (`Graph.isLink_endsOf`). So rows of the chart independent at
edges bound its rank from below
(`finrank_span_rigidityRows_pencilChartFramework_eq_of_independent_pencilRow`). -/
theorem pencilRow_mem_rigidityRows_of_mem_edgeSet [Inhabited α]
    (hubSel : α → Fin 3 → Option α) (q : α × Fin 4 × Fin 4 → K) {G : Graph α β}
    {i : β × Set.powersetCard (Fin 4) 2 × Set.powersetCard (Fin 4) 2} (he : i.1 ∈ E(G)) :
    pencilRow hubSel G.endsOf q i
      ∈ (pencilChartFramework (PencilSeed.ofCoord q) hubSel G).rigidityRows := by
  obtain ⟨e, t₁, t₂⟩ := i
  rw [pencilRow_eq_panelRow_pencilChartFramework hubSel q he]
  exact (pencilChartFramework (PencilSeed.ofCoord q) hubSel G).panelRow_mem_rigidityRows_of_link
    G.endsOf (u := (G.endsOf e).1) (w := (G.endsOf e).2) rfl (G.isLink_endsOf he) t₁ t₂

/-- **Proportional hinges give the same rigidity rows** (a step of `lem:pencil-generic-steer`): for
two frameworks on the same graph, with `c • F₁.supportExtensor e = F₂.supportExtensor e` for some
`c ≠ 0` at every link `e`, the rigidity rows are the same, and so is their span. The rows at a link
are given by the forms of `hingeRowBlock e`, those that vanish on the line of the hinge
(`hingeRowBlock_apply`), and a nonzero multiple spans the same line
(`Submodule.span_singleton_smul_eq`). `span_rigidityRows_pencilChartFramework_eq_of_reseed` uses it.
-/
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

/-- **Scaling the two vectors of a `2`-extensor scales it by the product** (a step of
`lem:pencil-generic-steer`): `extensor ![a • x, b • y] = (a * b) • extensor ![x, y]`, by
`extensor_update_smul` (`Extensor.lean`) at each vector. -/
theorem extensor_pair_smul (a b : K) (x y : Fin 4 → K) :
    extensor (![a • x, b • y] : Fin 2 → Fin 4 → K)
      = (a * b) • extensor (![x, y] : Fin 2 → Fin 4 → K) := by
  have e1 : (![a • x, y] : Fin 2 → Fin 4 → K)
      = Function.update (![x, y] : Fin 2 → Fin 4 → K) 0 (a • (![x, y] : Fin 2 → Fin 4 → K) 0) := by
    funext i; fin_cases i <;> simp
  have e0 : (![a • x, b • y] : Fin 2 → Fin 4 → K)
      = Function.update (![a • x, y] : Fin 2 → Fin 4 → K) 1
          (b • (![a • x, y] : Fin 2 → Fin 4 → K) 1) := by
    funext i; fin_cases i <;> simp
  rw [e0, extensor_update_smul, e1, extensor_update_smul, smul_smul, mul_comm b a]

/-- **The hinge of the chart is a nonzero multiple of that of a realization it gives up to scalars**
(a step of `lem:pencil-generic-steer`): for a nondegenerate realization `F₁` of `H` and parameters
whose points are nonzero multiples of `point₁` on `V(H)` (`hpt`, as `exists_pencilSeed_of_nondeg`
gives), the hinge of the framework of the chart at a link `e` is a nonzero multiple of
`F₁.supportExtensor e`. With `x, y` the ends of `e` that `H.endsOf` gives, the hinge of `F₁` at `e`
is nonzero and passes through the independent `point₁ x` and `point₁ y`, so it is a nonzero multiple
of `extensor ![point₁ x, point₁ y]` (`exists_smul_eq_extensor_of_extensorThroughPoint_pair`,
`Statement.lean`). The hinge of the chart is the join of the points of the chart at `x` and `y`,
nonzero multiples of `point₁ x` and `point₁ y`, and `extensor_pair_smul` takes the two scalars out.
-/
theorem exists_smul_supportExtensor_eq_pencilChartFramework_of_reseed [Inhabited α]
    {H : Graph α β} {F₁ : BodyHingeFramework K 2 α β} {normal₁ point₁ : α → Fin 4 → K}
    (h₁ : IsNondegPencilRealization H F₁ normal₁ point₁)
    {seed₁ : PencilSeed K α} {hubSel : α → Fin 3 → Option α}
    (hpt : ∀ w ∈ V(H), ∃ c : K, c ≠ 0 ∧ pencilChartPoint seed₁ hubSel w = c • point₁ w)
    {e : β} {u v : α} (hlink : H.IsLink e u v) :
    ∃ c : K, c ≠ 0 ∧ c • F₁.supportExtensor e
      = (pencilChartFramework seed₁ hubSel H).supportExtensor e := by
  obtain ⟨⟨⟨-, -, hSuppNe, -⟩, -, -, hThru⟩, hB, -, -⟩ := h₁
  have he : e ∈ E(H) := hlink.edge_mem
  have hEnds : H.IsLink e (H.endsOf e).1 (H.endsOf e).2 := H.isLink_endsOf he
  have hthru := hThru e (H.endsOf e).1 (H.endsOf e).2 hEnds
  have hind : LinearIndependent K ![point₁ (H.endsOf e).1, point₁ (H.endsOf e).2] :=
    hB e (H.endsOf e).1 (H.endsOf e).2 hEnds
  obtain ⟨a, ha_ne, ha_eq⟩ :=
    exists_smul_eq_extensor_of_extensorThroughPoint_pair (hSuppNe e) hthru.1 hthru.2 hind
  obtain ⟨cx, hcx_ne, hcx_eq⟩ := hpt (H.endsOf e).1 hEnds.left_mem
  obtain ⟨cy, hcy_ne, hcy_eq⟩ := hpt (H.endsOf e).2 hEnds.right_mem
  refine ⟨cx * cy * a, mul_ne_zero (mul_ne_zero hcx_ne hcy_ne) ha_ne, ?_⟩
  rw [pencilChartFramework_supportExtensor_of_mem_edgeSet seed₁ hubSel he]
  apply ScrewSpace.ext
  rw [ScrewSpace.val_smul, ScrewSpace.val_mk, hcx_eq, hcy_eq, extensor_pair_smul, ← ha_eq,
    smul_smul]

/-- **Independent rows of the chart give its framework the deficiency rank** (a step of
`lem:pencil-generic-steer`): for `G` with at least one body and a coordinate point `q` at which the
framework of the chart on `G` has nonzero hinges at the links, a set `s` of indices at edges of `G`
whose rows `pencilRow hubSel G.endsOf q` are linearly independent, with `|s|` the deficiency rank
`screwDim 2 * (|V(G)| - 1) - G.deficiency n`, gives the framework that rank. The rows are rigidity
rows (`pencilRow_mem_rigidityRows_of_mem_edgeSet`), so the rank is at least `|s|`, and at nonzero
hinges it is at most the deficiency rank (`lem:relative-deficiency-rank-bound`;
`BodyHingeFramework.finrank_span_rigidityRows_add_deficiency_le`, `GenericityDevice.lean`). The
chart's counterpart of `finrank_span_rigidityRows_ofNormals_of_isGenericNormals`
(`GenericLift/PanelGeneric.lean`), whose rows are independent by genericity. -/
theorem finrank_span_rigidityRows_pencilChartFramework_eq_of_independent_pencilRow
    [Inhabited α] [Finite α] [Finite β] {n : ℕ}
    (hn : Graph.bodyBarDim n = screwDim 2) {G : Graph α β} (hGne : V(G).Nonempty)
    (hubSel : α → Fin 3 → Option α) {q : α × Fin 4 × Fin 4 → K}
    (hC : ∀ e u v, G.IsLink e u v →
      (pencilChartFramework (PencilSeed.ofCoord q) hubSel G).supportExtensor e ≠ 0)
    {s : Set (β × Set.powersetCard (Fin 4) 2 × Set.powersetCard (Fin 4) 2)}
    (hslink : ∀ i ∈ s, (i : β × _ × _).1 ∈ E(G))
    (hsLI : LinearIndependent K fun i : s => pencilRow hubSel G.endsOf q (i : β × _ × _))
    (hscard : (Nat.card s : ℤ) = screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency n) :
    (Module.finrank K (Submodule.span K
        (pencilChartFramework (PencilSeed.ofCoord q) hubSel G).rigidityRows) : ℤ)
      = screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency n := by
  have : Fintype s := Fintype.ofFinite s
  -- The lower bound: the independent rows lie in the span of the rigidity rows.
  have hsub : Submodule.span K
        (Set.range fun i : s => pencilRow hubSel G.endsOf q (i : β × _ × _))
      ≤ Submodule.span K (pencilChartFramework (PencilSeed.ofCoord q) hubSel G).rigidityRows := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span
      (pencilRow_mem_rigidityRows_of_mem_edgeSet hubSel q (hslink i.1 i.2))
  have hlbN : Nat.card s ≤ Module.finrank K (Submodule.span K
      (pencilChartFramework (PencilSeed.ofCoord q) hubSel G).rigidityRows) :=
    calc Nat.card s = Fintype.card s := Nat.card_eq_fintype_card
      _ = Module.finrank K (Submodule.span K
            (Set.range fun i : s => pencilRow hubSel G.endsOf q (i : β × _ × _))) :=
          (finrank_span_eq_card hsLI).symm
      _ ≤ _ := Submodule.finrank_mono hsub
  have hlb : (Nat.card s : ℤ) ≤ (Module.finrank K (Submodule.span K
      (pencilChartFramework (PencilSeed.ofCoord q) hubSel G).rigidityRows) : ℤ) := by
    exact_mod_cast hlbN
  -- The upper bound, at nonzero hinges.
  have hub := BodyHingeFramework.finrank_span_rigidityRows_add_deficiency_le
    (pencilChartFramework (PencilSeed.ofCoord q) hubSel G) hn hGne hC
  simp only [pencilChartFramework_graph] at hub
  exact le_antisymm hub (by rw [← hscard]; exact hlb)

/-! ### Independent rows at `seed.toCoord`

For a nondegenerate realization `F₁` of `H` and parameters `seed₁` whose points are nonzero
multiples of its points, the rigidity rows of the framework of the chart at `seed₁` span the space
that those of `F₁` span (`span_rigidityRows_pencilChartFramework_eq_of_reseed`), and so do those at
`PencilSeed.ofCoord seed₁.toCoord`, which has the same points (`pencilChartFramework_congr`). Rows
`panelRow` at links, as many as the rank of `F₁` and independent
(`BodyHingeFramework.exists_independent_panelRow_subfamily_of_le_finrank`, `GenericityDevice.lean`),
are then rows `pencilRow` at the coordinate point `seed₁.toCoord`
(`pencilRow_eq_panelRow_pencilChartFramework`). `exists_isNondegPencilRealization_steer` keeps them
independent at a common non-root by `exists_common_seed_pencilRow_and_polynomials` (`Engine.lean`).
-/

/-- **Parameters with the same points have the same framework** (a step of
`lem:pencil-generic-steer`): the framework of the chart reads the parameters only through the
points, at the edges of `G`, where the hinge is the join of the points of the ends; at another label
the hinge does not depend on them. So `PencilSeed.ofCoord seed.toCoord` has the framework of `seed`
(`pencilChartPoint_ofCoord_toCoord`), and a new `fillNbr` keeps it (`pencilChartPoint_congr`). -/
theorem pencilChartFramework_congr [Inhabited α] {seed seed' : PencilSeed K α}
    (hubSel : α → Fin 3 → Option α) (G : Graph α β)
    (hpt : pencilChartPoint seed hubSel = pencilChartPoint seed' hubSel) :
    pencilChartFramework seed hubSel G = pencilChartFramework seed' hubSel G := by
  have hsupp : (pencilChartFramework seed hubSel G).supportExtensor
      = (pencilChartFramework seed' hubSel G).supportExtensor := by
    funext e
    by_cases he : e ∈ E(G)
    · rw [pencilChartFramework_supportExtensor_of_mem_edgeSet seed hubSel he,
        pencilChartFramework_supportExtensor_of_mem_edgeSet seed' hubSel he, hpt]
    · rw [pencilChartFramework_supportExtensor_of_not_mem_edgeSet seed hubSel he,
        pencilChartFramework_supportExtensor_of_not_mem_edgeSet seed' hubSel he]
  calc pencilChartFramework seed hubSel G
      = ⟨G, (pencilChartFramework seed hubSel G).supportExtensor⟩ := rfl
    _ = ⟨G, (pencilChartFramework seed' hubSel G).supportExtensor⟩ := by rw [hsupp]
    _ = pencilChartFramework seed' hubSel G := rfl

/-- **The chart has the rigidity rows of a realization it gives up to scalars** (a step of
`lem:pencil-generic-steer`): for a nondegenerate realization `F₁` of `H` and parameters whose points
are nonzero multiples of `point₁` on `V(H)` (`hpt`), the rigidity rows of the framework of the chart
on `H` span the space that those of `F₁` span. Its hinges are nonzero multiples of those of `F₁`
(`exists_smul_supportExtensor_eq_pencilChartFramework_of_reseed`), and proportional hinges give the
same rows (`span_rigidityRows_eq_of_supportExtensor_proportional`). So the chart has the rank of
`F₁`. -/
theorem span_rigidityRows_pencilChartFramework_eq_of_reseed [Inhabited α]
    {H : Graph α β} {F₁ : BodyHingeFramework K 2 α β} {normal₁ point₁ : α → Fin 4 → K}
    (h₁ : IsNondegPencilRealization H F₁ normal₁ point₁)
    {seed₁ : PencilSeed K α} {hubSel : α → Fin 3 → Option α}
    (hpt : ∀ w ∈ V(H), ∃ c : K, c ≠ 0 ∧ pencilChartPoint seed₁ hubSel w = c • point₁ w) :
    Submodule.span K (pencilChartFramework seed₁ hubSel H).rigidityRows
      = Submodule.span K F₁.rigidityRows := by
  have hFg : F₁.graph = H := h₁.1.1.1
  refine (span_rigidityRows_eq_of_supportExtensor_proportional F₁
    (pencilChartFramework seed₁ hubSel H) ?_ ?_).symm
  · rw [pencilChartFramework_graph]; exact hFg
  · intro e u v hlink
    rw [hFg] at hlink
    exact exists_smul_supportExtensor_eq_pencilChartFramework_of_reseed h₁ hpt hlink

/-- **Independent rows of the chart at `seed₁.toCoord`, as many as the rank of a realization** (a
step of `lem:pencil-generic-steer`): for a nondegenerate realization `F₁` of `H`, parameters `seed₁`
whose points are nonzero multiples of `point₁` on `V(H)` (`hpt`), and `N` at most the rank of `F₁`,
there is a set of `N` indices at edges of `H` whose rows `pencilRow hubSel H.endsOf seed₁.toCoord`
are linearly independent. The framework of the chart at `PencilSeed.ofCoord seed₁.toCoord` is that
at `seed₁` (`pencilChartFramework_congr`), with the rigidity rows of `F₁` and with nonzero hinges at
the links, nonzero multiples of those of `F₁`; so
`BodyHingeFramework.exists_independent_panelRow_subfamily_of_le_finrank` gives `N` independent rows
`panelRow` at links, and these are the rows `pencilRow`
(`pencilRow_eq_panelRow_pencilChartFramework`). `exists_isNondegPencilRealization_steer` takes for
`N` the rank of `F₁`. -/
theorem exists_independent_pencilRow_subfamily_at_toCoord_of_reseed
    [Inhabited α] [Finite α] [Finite β]
    {H : Graph α β} {F₁ : BodyHingeFramework K 2 α β} {normal₁ point₁ : α → Fin 4 → K}
    (h₁ : IsNondegPencilRealization H F₁ normal₁ point₁)
    {seed₁ : PencilSeed K α} {hubSel : α → Fin 3 → Option α}
    (hpt : ∀ w ∈ V(H), ∃ c : K, c ≠ 0 ∧ pencilChartPoint seed₁ hubSel w = c • point₁ w)
    {N : ℕ} (hN : N ≤ Module.finrank K (Submodule.span K F₁.rigidityRows)) :
    ∃ s : Set (β × Set.powersetCard (Fin 4) 2 × Set.powersetCard (Fin 4) 2),
      (∀ i ∈ s, (i : β × _ × _).1 ∈ E(H)) ∧ Nat.card s = N ∧
      LinearIndependent K
        (fun i : s => pencilRow hubSel H.endsOf seed₁.toCoord (i : β × _ × _)) := by
  have hSuppNe : ∀ e, F₁.supportExtensor e ≠ 0 := h₁.1.1.2.2.1
  -- The framework at `PencilSeed.ofCoord seed₁.toCoord` is that at `seed₁`: the points agree.
  have hcongr : pencilChartFramework (PencilSeed.ofCoord seed₁.toCoord) hubSel H
      = pencilChartFramework seed₁ hubSel H :=
    pencilChartFramework_congr hubSel H
      (funext fun v => pencilChartPoint_ofCoord_toCoord seed₁ hubSel v)
  -- Its rigidity rows span the space that those of `F₁` span.
  have hspan : Submodule.span K
        (pencilChartFramework (PencilSeed.ofCoord seed₁.toCoord) hubSel H).rigidityRows
      = Submodule.span K F₁.rigidityRows := by
    rw [hcongr]; exact span_rigidityRows_pencilChartFramework_eq_of_reseed h₁ hpt
  have hNle : N ≤ Module.finrank K (Submodule.span K
      (pencilChartFramework (PencilSeed.ofCoord seed₁.toCoord) hubSel H).rigidityRows) := by
    rw [hspan]; exact hN
  -- Its hinges are nonzero at the links, nonzero multiples of those of `F₁`.
  have hne : ∀ e, (pencilChartFramework (PencilSeed.ofCoord seed₁.toCoord) hubSel H).graph.IsLink e
      (H.endsOf e).1 (H.endsOf e).2 →
      (pencilChartFramework (PencilSeed.ofCoord seed₁.toCoord) hubSel H).supportExtensor e ≠ 0 := by
    intro e hlink
    rw [pencilChartFramework_graph] at hlink
    obtain ⟨c, hc, hceq⟩ :=
      exists_smul_supportExtensor_eq_pencilChartFramework_of_reseed h₁ hpt hlink
    rw [hcongr, ← hceq]
    exact smul_ne_zero hc (hSuppNe e)
  -- The selector `H.endsOf` gives every edge of `H` its ends.
  have hends : ∀ e u v,
      (pencilChartFramework (PencilSeed.ofCoord seed₁.toCoord) hubSel H).graph.IsLink e u v →
      (pencilChartFramework (PencilSeed.ofCoord seed₁.toCoord) hubSel H).graph.IsLink e
        (H.endsOf e).1 (H.endsOf e).2 := by
    intro e u v hlink
    rw [pencilChartFramework_graph] at hlink ⊢
    exact H.isLink_endsOf hlink.edge_mem
  -- `N` independent rows `panelRow` at links, at the selector `H.endsOf`.
  obtain ⟨s, hslink, hscard, hsLI⟩ :=
    (pencilChartFramework (PencilSeed.ofCoord seed₁.toCoord) hubSel
      H).exists_independent_panelRow_subfamily_of_le_finrank (ends := H.endsOf) hends hne hNle
  refine ⟨s, ?_, hscard, ?_⟩
  · intro i hi
    have hL := hslink i hi
    rw [pencilChartFramework_graph] at hL
    exact hL.edge_mem
  · -- Each is the row `pencilRow` at its index.
    have hfeq : (fun i : s => pencilRow hubSel H.endsOf seed₁.toCoord (i : β × _ × _))
        = (fun i : s =>
            (pencilChartFramework (PencilSeed.ofCoord seed₁.toCoord) hubSel H).panelRow
              H.endsOf (i : β × _ × _)) := by
      funext i
      have hL := hslink i.1 i.2
      rw [pencilChartFramework_graph] at hL
      exact pencilRow_eq_panelRow_pencilChartFramework hubSel seed₁.toCoord hL.edge_mem
    rw [hfeq]; exact hsLI

/-! ### Normals that do not read `fillNbr`

A new `fillNbr` (`exists_fillNbr_pencilChartWF_of_standing`) keeps `hubNormal` and `fillHub`, so a
condition on the normals at a coordinate point `q` holds at the new parameters where the normals do
not read `fillNbr`. The normal of a hub is its `hubNormal`. That of another body is the `cross₃` of
its slots `nbrSlotPoint`, which read `fillNbr` only at the empty slots of the neighbour selector.
`exists_isNondegPencilRealization_steer` asks its conditions on the normals only at hubs of `H` and
at bodies with three members in their closed neighbourhood in `H`, where the neighbour selector has
no empty slot (`IsFin3SelectorOf.isSome_of_ncard_eq_three`, `MainComponent/GenericSteer.lean`). -/

/-- **Parameters with the same `hubNormal` and `fillHub` have the same normal at a body where it
does not read `fillNbr`** (a step of `lem:pencil-generic-steer`): at a hub `v` the normal is
`hubNormal v`; at a body `v` that is not a hub and whose neighbour selector has no empty slot
(`hassigned`), it is the `cross₃` of the points of three bodies, which agree
(`pencilChartPoint_congr`). -/
theorem pencilChartNormal_congr {seed seed' : PencilSeed K α}
    (hubSel nbrSel : α → Fin 3 → Option α) (G : Graph α β) {v : α}
    (hhub : seed'.hubNormal = seed.hubNormal) (hfill : seed'.fillHub = seed.fillHub)
    (hassigned : ¬ G.PencilHub v → ∀ i, (nbrSel v i).isSome) :
    pencilChartNormal seed' hubSel nbrSel G v = pencilChartNormal seed hubSel nbrSel G v := by
  by_cases hv : G.PencilHub v
  · rw [pencilChartNormal_of_pencilHub seed' hubSel nbrSel hv,
      pencilChartNormal_of_pencilHub seed hubSel nbrSel hv, hhub]
  · rw [pencilChartNormal_of_not_pencilHub seed' hubSel nbrSel hv,
      pencilChartNormal_of_not_pencilHub seed hubSel nbrSel hv]
    have hpt : pencilChartPoint seed' hubSel = pencilChartPoint seed hubSel :=
      pencilChartPoint_congr hubSel hhub hfill
    have hslot : ∀ i, nbrSlotPoint seed' hubSel nbrSel v i
        = nbrSlotPoint seed hubSel nbrSel v i := by
      intro i
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hassigned hv i)
      simp only [nbrSlotPoint, hw]
      exact congrFun hpt w
    rw [hslot 0, hslot 1, hslot 2]

/-- **Parameters with the same `hubNormal` and `fillHub` keep the independence of the normals on a
set where they do not read `fillNbr`** (a step of `lem:pencil-generic-steer`):
`pencilChartNormal_congr` at each member (`LinearIndepOn.congr`).
`exists_isNondegPencilRealization_steer` uses it at each of its sets, whose members are hubs of `H`
or have three members in their closed neighbourhood in `H`. -/
theorem linearIndepOn_pencilChartNormal_congr {seed seed' : PencilSeed K α}
    (hubSel nbrSel : α → Fin 3 → Option α) (G : Graph α β) {s : Set α}
    (hhub : seed'.hubNormal = seed.hubNormal) (hfill : seed'.fillHub = seed.fillHub)
    (hassigned : ∀ w ∈ s, ¬ G.PencilHub w → ∀ i, (nbrSel w i).isSome)
    (hLI : LinearIndepOn K (pencilChartNormal seed hubSel nbrSel G) s) :
    LinearIndepOn K (pencilChartNormal seed' hubSel nbrSel G) s := by
  apply hLI.congr
  intro w hw
  exact (pencilChartNormal_congr hubSel nbrSel G hhub hfill (hassigned w hw)).symm

end CombinatorialRigidity.Molecular
