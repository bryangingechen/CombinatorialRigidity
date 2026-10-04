/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.Engine
import CombinatorialRigidity.Molecular.Molecule.Pencil.Reseed
import CombinatorialRigidity.Molecular.Molecule.Pencil.Witness

/-!
# WF conditions at the `fillNbr`-free flattening (Phase 39 PENCIL, W5-L5 L5-cut-v-d)

The chart-steering toolkit (`notes/Phase39-design.md` §"W5 leaf decomposition" L5-cut-v) that
`lem:pencil-generic-steer` runs (T2 `exists_isNondegPencilRealization_restrict_of_demoted` and T3
`exists_isNondegPencilRealization_steer`, `MainComponent/GenericSteer.lean`): run a nondegenerate
pencil realization through the re-seeding lemma (`exists_pencilSeed_of_nondeg`, `Reseed.lean`) to a
`PencilChartWF` seed, then *steer* that seed along the rows-polynomial engine (`Engine.lean`
§"L5-cut-v-d") so finitely many further point and normal independence conditions hold too. The
steering engine works over the flat seed-coordinate space `α × Fin 4 × Fin 4` via
`PencilSeed.ofCoord`, so a re-seeded `PencilSeed` (three independent fields
`hubNormal`/`fillHub`/`fillNbr`) must first be *flattened* onto that space.

This file carries the **flattening bridge** (`notes/Phase39-design.md` L5-cut-v composition finding
(3)). `PencilSeed.ofCoord` couples the two fill fields — it sets `fillNbr := fillHub` from one
coordinate — so the flattening `PencilSeed.toCoord` of a re-seeded seed drops the re-seeded seed's
own `fillNbr` and keeps only its point-side data (`hubNormal`, `fillHub`). Because
`pencilChartPoint` and `hubSlotNormal` never read `fillNbr`, **the constructed points literally
coincide with the re-seeded seed's** (`pencilChartPoint_ofCoord_toCoord`), and the four
`fillNbr`-independent `PencilChartWF` conjuncts (both selector-correctness conjuncts, the hub-slot
triple independence, and adjacent-point distinctness) transfer verbatim — the "standing WF
conditions witnessed at the `fillNbr`-free flattening" the composition finding names; the
`fillNbr` re-choice lemma below takes them as hypotheses, built directly at each call site.

The one conjunct this bridge does **not** carry is `PencilChartWF`'s fourth — the non-hub
`nbrSlotPoint` triple independence, the sole conjunct reading `fillNbr` (at the `nbrSel`-unassigned
slots of a deg-`≤ 1` non-hub body). That conjunct genuinely fails at the flattening there (the
re-seeded seed's `fillNbr`, chosen to make it hold, is replaced by `fillHub`), and is re-established
by re-choosing `fillNbr` freely POST-steering at those bodies — the `fillNbr` re-choice lemma
`exists_fillNbr_pencilChartWF_of_standing` below, whose linear-algebra core is the general
`exists_extend_linearIndependent` (fill an independent partial family's free slots to a full
independent family). At the *fully-assigned* non-hub bodies
(`nbrSel` all `some`, i.e. degree exactly `2`) the fourth conjunct is `fillNbr`-free too, and a
demoted hub (degree `3` in `G`, `2` in `H`) is one such body — but the bridge stays general and
leaves the fourth conjunct entirely to the re-choice, rather than special-casing degree.

See `notes/Phase39.md`, `notes/Phase39-design.md` (§"W5 leaf decomposition" L5-cut-v, composition
finding (3)), and `blueprint/src/chapter/pencil.tex`.
-/

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K]
variable {α β : Type*}

/-! ## The `fillNbr`-free flattening of a seed (Phase 39 W5-L5 L5-cut-v-d) -/

/-- **The `fillNbr`-free flattening of a seed onto the engine's coordinate space** (Phase 39 W5-L5
L5-cut-v-d): the right inverse of `PencilSeed.ofCoord` on the point side. Role `0` reads the seed's
free hub-normal, role `j.succ` (`j : Fin 3`) reads the seed's `j`-th `fillHub` slot — exactly the
two fields `PencilSeed.ofCoord` reconstructs. The seed's independent `fillNbr` field is dropped: it
plays no role in the engine's `pencilChartPoint`/`hubSlotNormal` machinery, and
`PencilSeed.ofCoord (seed.toCoord)` re-derives `fillNbr := fillHub` (the harmless coupling
`PencilSeed.ofCoord` imposes). -/
def PencilSeed.toCoord (seed : PencilSeed K α) (p : α × Fin 4 × Fin 4) : K :=
  (Fin.cons (seed.hubNormal p.1 p.2.2) (fun j => seed.fillHub p.1 j p.2.2) : Fin 4 → K) p.2.1

/-- **The flattening reproduces the seed's hub-normal field** (Phase 39 W5-L5 L5-cut-v-d):
`PencilSeed.ofCoord` reads role `0` for the hub-normal, and `PencilSeed.toCoord` answers role `0`
with `Fin.cons`'s head (`Fin.cons_zero`), the seed's own `hubNormal`. -/
theorem PencilSeed.ofCoord_toCoord_hubNormal (seed : PencilSeed K α) :
    (PencilSeed.ofCoord seed.toCoord).hubNormal = seed.hubNormal := by
  funext v i
  simp only [PencilSeed.ofCoord, PencilSeed.toCoord, Fin.cons_zero]

/-- **The flattening reproduces the seed's `fillHub` field** (Phase 39 W5-L5 L5-cut-v-d):
`PencilSeed.ofCoord` reads role `j.succ` for the `j`-th `fillHub` slot, and `PencilSeed.toCoord`
answers role `j.succ` with `Fin.cons`'s tail at `j` (`Fin.cons_succ`), the seed's own `fillHub`. -/
theorem PencilSeed.ofCoord_toCoord_fillHub (seed : PencilSeed K α) :
    (PencilSeed.ofCoord seed.toCoord).fillHub = seed.fillHub := by
  funext v j i
  simp only [PencilSeed.ofCoord, PencilSeed.toCoord, Fin.cons_succ]

/-! ## The point-side chart data coincides at the flattening (Phase 39 W5-L5 L5-cut-v-d) -/

/-- **The hub-slot normal at the flattening coincides with the seed's** (Phase 39 W5-L5
L5-cut-v-d): `hubSlotNormal` reads only the seed's `hubNormal` (at a `some` slot) or `fillHub` (at a
`none` slot), both of which the flattening reproduces
(`PencilSeed.ofCoord_toCoord_hubNormal`/`_fillHub`); it never touches `fillNbr`. -/
theorem hubSlotNormal_ofCoord_toCoord (seed : PencilSeed K α) (hubSel : α → Fin 3 → Option α)
    (v : α) (slot : Fin 3) :
    hubSlotNormal (PencilSeed.ofCoord seed.toCoord) hubSel v slot
      = hubSlotNormal seed hubSel v slot := by
  unfold hubSlotNormal
  cases hubSel v slot with
  | none => rw [PencilSeed.ofCoord_toCoord_fillHub]
  | some w => rw [PencilSeed.ofCoord_toCoord_hubNormal]

/-- **The chart's constructed point at the flattening literally coincides with the seed's**
(Phase 39 W5-L5 L5-cut-v-d, the headline of composition finding (3)): `pencilChartPoint` is the
`cross₃` of the three hub-slot normals, each of which coincides
(`hubSlotNormal_ofCoord_toCoord`). This is what lets the steering engine start from the flattening
`seed.toCoord` without disturbing any point-side condition the re-seeded seed already satisfies. -/
theorem pencilChartPoint_ofCoord_toCoord (seed : PencilSeed K α) (hubSel : α → Fin 3 → Option α)
    (v : α) :
    pencilChartPoint (PencilSeed.ofCoord seed.toCoord) hubSel v
      = pencilChartPoint seed hubSel v := by
  simp only [pencilChartPoint, hubSlotNormal_ofCoord_toCoord]

/-! ## The post-steering `fillNbr` re-choice (Phase 39 W5-L5 L5-cut-v-d)

`exists_extend_linearIndependent`, the linear-algebra core this section's re-choice lemma consumes,
moved to `Pencil/Reseed.lean` in Phase 40o (MOTIVES-EARS, B1): this file still sees it through the
`Reseed` import above. -/

/-- **Re-choosing `fillNbr` post-steering closes `PencilChartWF`'s fourth conjunct** (Phase 39 W5-L5
L5-cut-v-d, `notes/Phase39-design.md` §"W5 leaf decomposition" L5-cut-v composition finding (3)):
the last owed piece of the v-d flattening. The four `fillNbr`-free standing conjuncts
(`hsel_hub`, `hsel_nbr`, `hhub_LI`, `hpt_LI` below — hub/neighbour selector correctness, hub-slot
triple independence, adjacent-point distinctness) plus the *partial* independence of each non-hub
body's `nbrSel`-*assigned* `nbrSlotPoint` slots (`hnbr_some`; at a fully-assigned body this IS the
fourth conjunct, supplied by the steering; at a deg-`≤ 1` body it is the `some`-slot subfamily, its
adjacent points independent by conjunct 5) together produce a `fillNbr` re-choice — a seed `seed'`
sharing `seed`'s `hubNormal`/`fillHub` — at which *full* `PencilChartWF` holds.

Nothing but the fourth conjunct reads `fillNbr` (`pencilChartPoint`/`hubSlotNormal` are
`fillNbr`-free), so `seed'` reproduces every point-side datum definitionally and the four standing
conjuncts transfer verbatim; the fourth conjunct is closed body-by-body by
`exists_extend_linearIndependent`, filling each non-hub body's `nbrSel`-unassigned (`none`) slots
with vectors making the whole `nbrSlotPoint` triple independent. -/
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

/-! ## Steering chart points to simultaneous independence (Phase 39 W5-L5 L5-cut-v-e) -/

/-- **Finitely many chart-point independence conditions, each satisfiable somewhere, share a common
seed** (Phase 39 W5-L5 L5-cut-v-e, the "steer to a common seed" engine call of
`notes/Phase39-design.md` §"W5 leaf decomposition" L5-cut-v): over an infinite field with a finite
body type, if for each index `i` some seed makes the chart's constructed points linearly independent
on the set `S i`, then a *single* seed makes every family independent at once. T2
(`exists_isNondegPencilRealization_restrict_of_demoted`) runs it: every condition the steered seed
must satisfy — each body's hub-slot triple independence (`pencilChartPoint v ≠ 0`, the singleton
case), each link's adjacent-point distinctness (the pair case), each non-hub body's closed
neighbourhood, and each demoted hub's closed neighbourhood in `H` — is exactly a
`LinearIndepOn K (pencilChartPoint …)` condition on a subset of `α`, satisfiable somewhere (the
re-seeded flattening for the standing conjuncts, the hub witness (MC-188) for the demoted ones).

Each condition becomes a seed-polynomial nonzero at its own witness seed whose non-roots preserve
the family (`exists_polynomial_ne_zero_of_linearIndependent_pencilChartPoint`, `Engine.lean`, at
`ends := id`, `s := S i`); the common non-root of the finite family
(`exists_common_eval_ne_zero_of_forall_exists`, whence `[Infinite K]`) is the steered seed. -/
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

/-! ## Point-side helpers for the steering (Phase 39 W5-L5 L5-cut-v-e) -/

/-- **The chart's constructed point depends only on the seed's `hubNormal`/`fillHub`** (Phase 39
W5-L5 L5-cut-v-e): two seeds agreeing on `hubNormal` and `fillHub` induce the same
`pencilChartPoint`, since `pencilChartPoint`/`hubSlotNormal` never read `fillNbr`. This lets the
post-steering `fillNbr` re-choice (`exists_fillNbr_pencilChartWF_of_standing`, whose output seed
shares the input's `hubNormal`/`fillHub`) preserve the steered point conditions. -/
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

/-- **An independent literal `Fin 3` triple gives `LinearIndepOn` on the `3`-element set** (Phase 39
W5-L5 L5-cut-v-e; the reverse of `linearIndependent_triple_of_linearIndepOn`, `Motive.lean`): the
distinct-witness map `Fin 3 → ↥{x, y, z}` is a bijection, and `LinearIndependent` is invariant under
precomposition with it (`linearIndependent_equiv`). Upstream-eligible (a general `LinearIndepOn`
fact, no rigidity content); kept local pending a mirror — see `notes/FRICTION.md`. -/
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

/-- **The `nbrSel`-assigned-slot subfamily is independent when the closed-neighbourhood chart points
are** (Phase 39 W5-L5 L5-cut-v-e; the reindexing the `hnbr_some` marshalling needs): at a non-hub
`v` whose neighbour-selector is correct, `LinearIndepOn` of the chart's points over the closed
neighbourhood transfers to `LinearIndepOn` of `nbrSlotPoint` over the selector's `some` slots. The
witnessing map `slot ↦ selected vertex` is injective (selector clause 3), so
`LinearIndependent.comp` carries the closed-neighbourhood independence to the slots (`nbrSlotPoint`
reads off exactly the selected vertex's chart point at a `some` slot). The reverse feed of
`linearIndepOn_pencilChartPoint_closedNbhd` (`Chart.lean`) for the `some`-subfamily. -/
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

/-! ## The output-half rank-transport bricks (Phase 39 W5-L5 L5-cut-v-f) -/

/-- **v-f-1 (link bridge, helper): a chart `pencilRow` at a genuine edge IS the chart framework's
own `panelRow`** (Phase 39 W5-L5 L5-cut-v-f, the Engine docstring's deferred "hends-style"
consumer; `notes/Phase39-design.md` §"W5 leaf decomposition" L5-cut-v "v-f decomposition"). The
graph-free annihilator row `pencilRow hubSel G.endsOf q i` (`Engine.lean`) reads exactly the
`pencilChartFramework (PencilSeed.ofCoord q) hubSel G`'s own supporting extensor at the edge `i.1`
(`pencilChartFramework_supportExtensor_of_mem_edgeSet`, using the canonical selector `G.endsOf`),
so at a genuine edge it is definitionally that framework's `panelRow` at the same index — the whole
bridge is unfolding both sides and rewriting the extensor. -/
theorem pencilRow_eq_panelRow_pencilChartFramework [Inhabited α]
    (hubSel : α → Fin 3 → Option α) (q : α × Fin 4 × Fin 4 → K) {G : Graph α β}
    {i : β × Set.powersetCard (Fin 4) 2 × Set.powersetCard (Fin 4) 2} (he : i.1 ∈ E(G)) :
    pencilRow hubSel G.endsOf q i
      = (pencilChartFramework (PencilSeed.ofCoord q) hubSel G).panelRow G.endsOf i := by
  rw [pencilRow, BodyHingeFramework.panelRow,
    pencilChartFramework_supportExtensor_of_mem_edgeSet (PencilSeed.ofCoord q) hubSel he]

/-- **v-f-1 (link bridge): a chart `pencilRow` at a genuine edge is a rigidity row of the chart
framework** (Phase 39 W5-L5 L5-cut-v-f). Composes the row-identity
`pencilRow_eq_panelRow_pencilChartFramework` with the landed general
`BodyHingeFramework.panelRow_mem_rigidityRows_of_link` (`Pinning.lean`) at the canonical selector
`G.endsOf` — every genuine edge links its `endsOf` bodies (`isLink_endsOf`). This is the lower-bound
feeder of the output-half `le_antisymm`: the steered LI `pencilRow` subfamily lands in the chart's
rigidity-row span. -/
theorem pencilRow_mem_rigidityRows_of_mem_edgeSet [Inhabited α]
    (hubSel : α → Fin 3 → Option α) (q : α × Fin 4 × Fin 4 → K) {G : Graph α β}
    {i : β × Set.powersetCard (Fin 4) 2 × Set.powersetCard (Fin 4) 2} (he : i.1 ∈ E(G)) :
    pencilRow hubSel G.endsOf q i
      ∈ (pencilChartFramework (PencilSeed.ofCoord q) hubSel G).rigidityRows := by
  obtain ⟨e, t₁, t₂⟩ := i
  rw [pencilRow_eq_panelRow_pencilChartFramework hubSel q he]
  exact (pencilChartFramework (PencilSeed.ofCoord q) hubSel G).panelRow_mem_rigidityRows_of_link
    G.endsOf (u := (G.endsOf e).1) (w := (G.endsOf e).2) rfl (G.isLink_endsOf he) t₁ t₂

/-- **v-f-2: two frameworks on the same graph with per-edge proportional support extensors have
equal rigidity-row spans** (Phase 39 W5-L5 L5-cut-v-f). Because the hinge-row block
`r(p(e)) = (span {C(p(e))})^⊥` (`hingeRowBlock`) depends on the supporting extensor only through the
line it spans, a nonzero per-edge scalar `c • F₁.supportExtensor e = F₂.supportExtensor e` on every
link leaves each block — hence the whole rigidity-row *set* (`rigidityRows` quantifies over links) —
unchanged (`Submodule.span_singleton_smul_eq`). Consumed by the output half: the re-seeded chart
framework has hinges proportional to the witness framework's (v-f-3), so their rigidity-row spans,
and thus their ranks, coincide. -/
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

/-- **Scaling both slots of a `2`-extensor scales it by the product of the scalars** (Phase 39
W5-L5 L5-cut-v-f, the arithmetic core of v-f-3): `extensor ![a • x, b • y] = (a * b) • extensor
![x, y]`, two applications of the single-slot multilinearity `extensor_update_smul`
(`Extensor.lean`). A general `extensor` fact whose canonical home is `Extensor.lean`; kept local
here to avoid rebuilding that deep-upstream module for the rank-brick commit — see
`notes/FRICTION.md`. -/
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

/-- **v-f-3: the re-seeded chart framework's hinge is a nonzero multiple of the witness hinge**
(Phase 39 W5-L5 L5-cut-v-f, the one genuinely-new rank leaf; produces v-f-2's `hprop`). For a
nondegenerate pencil realization `IsNondegPencilRealization H F₁ normal₁ point₁` and a re-seeding
whose chart points reproduce the realization's own points up to a nonzero per-body scalar
(`hpt : pencilChartPoint seed₁ hubSel w = c_w • point₁ w`, the `exists_pencilSeed_of_nondeg`
output), each link's chart supporting extensor
`(pencilChartFramework seed₁ hubSel H).supportExtensor e` is a nonzero multiple of
`F₁.supportExtensor e`. The landed
`exists_smul_eq_extensor_of_extensorThroughPoint_pair` (`Statement.lean`) forces the nonzero hinge
`F₁.supportExtensor e` — passing through both endpoints' points (the through-point conjunct) and
carrying the independent pair (the adjacent-distinctness conjunct) — onto `extensor ![point₁ x,
point₁ y]` at the canonical endpoints `x, y = G.endsOf e`; extensor bilinearity
(`extensor_pair_smul`) absorbs the reproduction scalars `c_x, c_y` into the proportionality. Feeds
v-f-2 to transport the witness framework's rank to the re-seeded chart. -/
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

/-- **v-f-4: the chart framework's rigidity-row rank pinches to the deficiency target** (Phase 39
W5-L5 L5-cut-v-f, the output-rank `le_antisymm`). Given a linearly independent `pencilRow` subfamily
of size the target rank `D(|V(G)|−1) − def(G̃)` at the steered seed `PencilSeed.ofCoord q`, indexed
by genuine edges (`hslink`), and nonzero hinges everywhere links occur (`hC`), the rigidity-row span
of `pencilChartFramework (PencilSeed.ofCoord q) hubSel G` has finrank exactly the target. Lower
bound: each subfamily row is a chart rigidity row (v-f-1), so `finrank_span_eq_card` +
`Submodule.finrank_mono` give `Nat.card s ≤ finrank`. Upper bound: the landed deterministic B2 bound
`BodyHingeFramework.finrank_span_rigidityRows_add_deficiency_le` (`GenericityDevice.lean`) at the
nonzero hinges. The mirror of the panel lemma
`finrank_span_rigidityRows_ofNormals_of_isGenericNormals` (`PanelGeneric.lean`), with the panel
proof's genericity-over-`q` step replaced by explicit steering (supplied by T3,
`exists_isNondegPencilRealization_steer`). -/
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
  -- Lower bound: the independent `pencilRow` subfamily lands in the chart's rigidity-row span.
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
  -- Upper bound: the deterministic B2 deficiency bound at the nonzero hinges.
  have hub := BodyHingeFramework.finrank_span_rigidityRows_add_deficiency_le
    (pencilChartFramework (PencilSeed.ofCoord q) hubSel G) hn hGne hC
  simp only [pencilChartFramework_graph] at hub
  exact le_antisymm hub (by rw [← hscard]; exact hlb)

/-! ### The re-seed rank transport: the `pencilRow` subfamily at the flattening (Phase 39 W5-L5
L5-cut-v-f, T3's rank input)

T3 (`exists_isNondegPencilRealization_steer`, `MainComponent/GenericSteer.lean`) steers a *generic*
realization of `H` on `H`'s own chart so further normal and point conditions hold alongside the rank
rows. The rank rows it steers are produced here: re-seed the generic witness
(`exists_pencilSeed_of_nondeg`), transport its deficiency-target rank to the chart (the row-span
depends on the supporting extensor only through the line it spans, and the re-seeded chart hinge is
a nonzero multiple of the witness hinge — v-f-2 ∘ v-f-3), flatten onto the engine's coordinate
space without disturbing points
(`pencilChartFramework_congr`), and extract a linearly-independent `pencilRow` subfamily of the
target size (the general `exists_independent_panelRow_subfamily_of_le_finrank` + the v-f-1 bridge).
This is exactly the `hLI` input `exists_common_seed_pencilRow_and_polynomials` (`Engine.lean`)
consumes when it steers the rank rows to the common seed. -/

/-- **The chart framework depends on the seed only through its constructed points** (Phase 39 W5-L5
L5-cut-v-f, a small helper of the steering; parallel to the landed
`pencilChartPoint_congr`). `pencilChartFramework` reads the seed exclusively through
`pencilChartPoint seed hubSel` — its supporting extensor at a genuine edge is the point-join of the
two endpoints' constructed points, and the off-`E(G)` fallback is seed-free — so two seeds inducing
the same constructed points induce the same framework, hence the same rigidity rows and the same
span rank. This is what lets the point-preserving post-steering `fillNbr` re-choice
(`pencilChartPoint_congr`) carry the steered rank verbatim from `PencilSeed.ofCoord q` to the
re-chosen `seed'`, and lets the flattening `PencilSeed.ofCoord seed₁.toCoord` inherit the re-seeded
chart's rank (`pencilChartPoint_ofCoord_toCoord`). -/
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

/-- **The re-seeded chart's rigidity-row span equals the witness framework's** (Phase 39 W5-L5
L5-cut-v-f, the composition of v-f-2 and v-f-3). For a re-seed `seed₁` of a nondegenerate pencil
realization `IsNondegPencilRealization H F₁ normal₁ point₁` whose chart points reproduce the
realization's own points up to a nonzero per-body scalar (`hpt`, the `exists_pencilSeed_of_nondeg`
output), the chart framework's rigidity-row span coincides with `F₁`'s: every link's chart
supporting extensor is a nonzero multiple of `F₁`'s
(`exists_smul_supportExtensor_eq_pencilChartFramework_of_reseed`, v-f-3), and proportional support
extensors leave the rigidity-row span unchanged
(`span_rigidityRows_eq_of_supportExtensor_proportional`, v-f-2). Consequently the chart attains
`F₁`'s deficiency-target rank verbatim — the "rank transfers along re-seeding" step of the
output-half route. -/
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

/-- **The steered rank rows: an independent `pencilRow` subfamily of the target size at the
flattening** (Phase 39 W5-L5 L5-cut-v-f, the `hLI` input of T3's
`exists_common_seed_pencilRow_and_polynomials` call). From a nondegenerate `H`-realization `F₁`
whose rigidity-row span has rank `≥ N` (`hN`; `N :=` the deficiency target in T3) and a
re-seed reproducing its points (`hpt`), the graph-free rows `pencilRow hubSel H.endsOf
seed₁.toCoord` carry `N` linearly independent members indexed by genuine edges. Assembly: the
flattening's chart coincides with the re-seed's (`pencilChartFramework_congr`,
`pencilChartPoint_ofCoord_toCoord`), so its rigidity-row span attains `F₁`'s rank
(`span_rigidityRows_pencilChartFramework_eq_of_reseed`) and its hinges are nonzero at every link
(v-f-3 proportionality, `F₁`'s hinges nonzero); the general
rank-input extractor (`exists_independent_panelRow_subfamily_of_le_finrank`) hands back `N`
independent `panelRow` rows of genuine links, each of which IS the graph-free `pencilRow`
(`pencilRow_eq_panelRow_pencilChartFramework`, v-f-1). -/
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
  -- The chart at the flattening coincides with the chart at `seed₁` (points coincide).
  have hcongr : pencilChartFramework (PencilSeed.ofCoord seed₁.toCoord) hubSel H
      = pencilChartFramework seed₁ hubSel H :=
    pencilChartFramework_congr hubSel H
      (funext fun v => pencilChartPoint_ofCoord_toCoord seed₁ hubSel v)
  -- Its rigidity-row span attains `F₁`'s rank.
  have hspan : Submodule.span K
        (pencilChartFramework (PencilSeed.ofCoord seed₁.toCoord) hubSel H).rigidityRows
      = Submodule.span K F₁.rigidityRows := by
    rw [hcongr]; exact span_rigidityRows_pencilChartFramework_eq_of_reseed h₁ hpt
  have hNle : N ≤ Module.finrank K (Submodule.span K
      (pencilChartFramework (PencilSeed.ofCoord seed₁.toCoord) hubSel H).rigidityRows) := by
    rw [hspan]; exact hN
  -- The chart's hinges are nonzero at every genuine link (proportional to `F₁`'s nonzero hinges).
  have hne : ∀ e, (pencilChartFramework (PencilSeed.ofCoord seed₁.toCoord) hubSel H).graph.IsLink e
      (H.endsOf e).1 (H.endsOf e).2 →
      (pencilChartFramework (PencilSeed.ofCoord seed₁.toCoord) hubSel H).supportExtensor e ≠ 0 := by
    intro e hlink
    rw [pencilChartFramework_graph] at hlink
    obtain ⟨c, hc, hceq⟩ :=
      exists_smul_supportExtensor_eq_pencilChartFramework_of_reseed h₁ hpt hlink
    rw [hcongr, ← hceq]
    exact smul_ne_zero hc (hSuppNe e)
  -- The canonical selector `H.endsOf` records a genuine link of every edge of the chart's graph.
  have hends : ∀ e u v,
      (pencilChartFramework (PencilSeed.ofCoord seed₁.toCoord) hubSel H).graph.IsLink e u v →
      (pencilChartFramework (PencilSeed.ofCoord seed₁.toCoord) hubSel H).graph.IsLink e
        (H.endsOf e).1 (H.endsOf e).2 := by
    intro e u v hlink
    rw [pencilChartFramework_graph] at hlink ⊢
    exact H.isLink_endsOf hlink.edge_mem
  -- Extract `N` independent `panelRow` rows of genuine links, at the canonical selector.
  obtain ⟨s, hslink, hscard, hsLI⟩ :=
    (pencilChartFramework (PencilSeed.ofCoord seed₁.toCoord) hubSel
      H).exists_independent_panelRow_subfamily_of_le_finrank (ends := H.endsOf) hends hne hNle
  refine ⟨s, ?_, hscard, ?_⟩
  · intro i hi
    have hL := hslink i hi
    rw [pencilChartFramework_graph] at hL
    exact hL.edge_mem
  · -- Each extracted `panelRow` of a genuine link IS the graph-free `pencilRow` (v-f-1).
    have hfeq : (fun i : s => pencilRow hubSel H.endsOf seed₁.toCoord (i : β × _ × _))
        = (fun i : s =>
            (pencilChartFramework (PencilSeed.ofCoord seed₁.toCoord) hubSel H).panelRow
              H.endsOf (i : β × _ × _)) := by
      funext i
      have hL := hslink i.1 i.2
      rw [pencilChartFramework_graph] at hL
      exact pencilRow_eq_panelRow_pencilChartFramework hubSel seed₁.toCoord hL.edge_mem
    rw [hfeq]; exact hsLI

/-! ### The chart-normal congruence for the post-steering `fillNbr` re-choice (Phase 39 W5-L5
L5-cut-v-f, T3's normal-condition transfer)

T3 (`exists_isNondegPencilRealization_steer`) steers a generic realization of `H` so its
normal-independence conditions hold at the steered seed `PencilSeed.ofCoord q`, then re-chooses
`fillNbr` post-steering (`exists_fillNbr_pencilChartWF_of_standing`) to close `PencilChartWF`'s
fourth conjunct. The re-chosen seed `seed'` shares the steered seed's `hubNormal`/`fillHub` but not
its `fillNbr`, so the steered conditions must be *transported* from `PencilSeed.ofCoord q` to
`seed'`.

`pencilChartNormal` reads `fillNbr` only through its non-hub branch's `cross₃` of `nbrSlotPoint`
vectors, and only at that body's `nbrSel`-*unassigned* (`none`) slots. So at any body that is either
a pencil hub (reads the free `hubNormal`, shared) or has a *fully assigned* neighbour-selector
(every `nbrSlotPoint` slot reads a `pencilChartPoint`, itself `fillNbr`-free and preserved by
`pencilChartPoint_congr`), the constructed normal is `fillNbr`-free. T3's hypothesis on its sets
asks exactly this: each member is a hub of `H`, or has three closed neighbours in `H`, which forces
its neighbour-selector total. -/

/-- **The chart's constructed normal depends only on the seed's `hubNormal`/`fillHub` at a body that
is a hub or has a fully-assigned neighbour-selector** (Phase 39 W5-L5 L5-cut-v-f, the third sibling
of `pencilChartPoint_congr`/`pencilChartFramework_congr`). Two seeds agreeing on `hubNormal` and
`fillHub` induce the same `pencilChartNormal G v` whenever `v` is a pencil hub (the normal is the
shared free `hubNormal v`) or, being a non-hub, has every neighbour-slot assigned (`hassigned`: the
non-hub `cross₃` then reads only `pencilChartPoint`s of selected neighbours, preserved by
`pencilChartPoint_congr`, never the re-chosen `fillNbr`). This is what lets the point-preserving
post-steering `fillNbr` re-choice carry the steered normal independence verbatim from
`PencilSeed.ofCoord q` to the re-chosen `seed'`. -/
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

/-- **Normal independence transfers across a point-preserving `fillNbr` re-choice** (Phase
39 W5-L5 L5-cut-v-f, T3's normal-condition transfer). A `LinearIndepOn` of the
chart's constructed normals over a set `s` on which every member is a pencil hub or a fully-assigned
non-hub (`hassigned`, the "`fillNbr`-free" condition) survives replacing the seed by any `seed'`
agreeing on `hubNormal`/`fillHub` — via `LinearIndepOn.congr` and the pointwise
`pencilChartNormal_congr`. T3 (`exists_isNondegPencilRealization_steer`) applies this at each of
its sets, discharging `hassigned` from its hypothesis that a member is a hub of `H` or has three
closed neighbours in `H`. -/
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
