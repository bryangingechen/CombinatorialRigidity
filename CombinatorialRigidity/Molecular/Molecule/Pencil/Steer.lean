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

The L5-cut-v chart-steering discharge (`notes/Phase39-design.md` §"W5 leaf decomposition" L5
"Cut-arm route verdict", the L5-cut-v bullet) runs an arbitrary nondegenerate pencil realization of
the induced graph `H` through the re-seeding lemma (`exists_pencilSeed_of_nondeg`, `Reseed.lean`) to
a `PencilChartWF` seed, then *steers* that seed along the rows-polynomial engine
(`Engine.lean` §"L5-cut-v-d") so the pendant configuration's demoted triple and promoted normal
families become linearly independent. The steering engine works over the flat seed-coordinate space
`α × Fin 4 × Fin 4` via `PencilSeed.ofCoord`, so a re-seeded `PencilSeed` (three independent fields
`hubNormal`/`fillHub`/`fillNbr`) must first be *flattened* onto that space.

This file carries the **flattening bridge** (`notes/Phase39-design.md` L5-cut-v composition finding
(3)). `PencilSeed.ofCoord` couples the two fill fields — it sets `fillNbr := fillHub` from one
coordinate — so the flattening `PencilSeed.toCoord` of a re-seeded seed drops the re-seeded seed's
own `fillNbr` and keeps only its point-side data (`hubNormal`, `fillHub`). Because
`pencilChartPoint` and `hubSlotNormal` never read `fillNbr`, **the constructed points literally
coincide with the re-seeded seed's** (`pencilChartPoint_ofCoord_toCoord`), and the four
`fillNbr`-independent `PencilChartWF` conjuncts (both selector-correctness conjuncts, the hub-slot
triple independence, and adjacent-point distinctness) transfer verbatim
(`pencilChartWF_standing_ofCoord_toCoord`) — the "standing WF conditions witnessed at the
`fillNbr`-free flattening" the composition finding names.

The one conjunct this bridge does **not** carry is `PencilChartWF`'s fourth — the non-hub
`nbrSlotPoint` triple independence, the sole conjunct reading `fillNbr` (at the `nbrSel`-unassigned
slots of a deg-`≤ 1` non-hub body). That conjunct genuinely fails at the flattening there (the
re-seeded seed's `fillNbr`, chosen to make it hold, is replaced by `fillHub`), and is re-established
by re-choosing `fillNbr` freely POST-steering at those bodies — the `fillNbr` re-choice lemma
`exists_fillNbr_pencilChartWF_of_standing` below, whose linear-algebra core is the general
`exists_extend_linearIndependent` (fill an independent partial family's free slots to a full
independent family). At the *fully-assigned* non-hub bodies
(`nbrSel` all `some`, i.e. degree exactly `2`) the fourth conjunct is `fillNbr`-free too, and the
demoted body `u_c` of the pendant configuration is one such body — but the bridge stays general and
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
noncomputable def PencilSeed.toCoord (seed : PencilSeed K α) (p : α × Fin 4 × Fin 4) : K :=
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

/-! ## The standing WF conditions hold at the flattening (Phase 39 W5-L5 L5-cut-v-d) -/

/-- **The standing (`fillNbr`-free) `PencilChartWF` conditions are witnessed at the `fillNbr`-free
flattening** (Phase 39 W5-L5 L5-cut-v-d, composition finding (3)): a re-seeded seed's four
`fillNbr`-independent `PencilChartWF` conjuncts — both selector-correctness conjuncts (which are
seed-independent), the hub-slot triple independence, and adjacent-point distinctness — transfer
verbatim to its `fillNbr`-free flattening `PencilSeed.ofCoord (seed.toCoord)`, since the point-side
chart data coincides (`hubSlotNormal_ofCoord_toCoord`, `pencilChartPoint_ofCoord_toCoord`).

This is the steering engine's standing-condition input: it certifies the flattening `seed.toCoord`
as a seed at which every `PencilChartWF` condition *except* the non-hub `nbrSlotPoint` independence
already holds, so the rows-polynomial genericity engine can preserve them while steering the demoted
/ promoted families to independence. The excluded fourth conjunct (the sole `fillNbr`-reader) is
re-established by the downstream post-steering `fillNbr` re-choice, not here — see the module
docstring. -/
theorem pencilChartWF_standing_ofCoord_toCoord {G : Graph α β} {seed : PencilSeed K α}
    {hubSel nbrSel : α → Fin 3 → Option α} (hWF : PencilChartWF G seed hubSel nbrSel) :
    (∀ v, IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v)) ∧
    (∀ v, ¬ G.PencilHub v → IsFin3SelectorOf (G.closedNbhd v) (nbrSel v)) ∧
    (∀ v, LinearIndependent K
      ![hubSlotNormal (PencilSeed.ofCoord seed.toCoord) hubSel v 0,
        hubSlotNormal (PencilSeed.ofCoord seed.toCoord) hubSel v 1,
        hubSlotNormal (PencilSeed.ofCoord seed.toCoord) hubSel v 2]) ∧
    (∀ e u v, G.IsLink e u v → LinearIndependent K
      ![pencilChartPoint (PencilSeed.ofCoord seed.toCoord) hubSel u,
        pencilChartPoint (PencilSeed.ofCoord seed.toCoord) hubSel v]) := by
  refine ⟨hWF.1, hWF.2.1, fun v => ?_, fun e u v hlink => ?_⟩
  · simpa only [hubSlotNormal_ofCoord_toCoord] using hWF.2.2.1 v
  · simpa only [pencilChartPoint_ofCoord_toCoord] using hWF.2.2.2.2 e u v hlink

/-! ## Filling the free slots of a partial independent family (Phase 39 W5-L5 L5-cut-v-d) -/

/-- **A linearly independent partial family extends to a full independent family by freely filling
the unconstrained slots** (Phase 39 W5-L5 L5-cut-v-d, the linear-algebra core of the post-steering
`fillNbr` re-choice): a family `g : Fin n → V` in a finite-dimensional space of dimension `≥ n`,
linearly independent on a subset `s` of its slots, extends to a `g'` that agrees with `g` on `s` and
is linearly independent on *all* of `Fin n`. Each free slot (outside `s`) is filled, one at a time,
with a vector lying outside the span of the slots already committed — possible because that span has
dimension `≤ |s| < n ≤ finrank K V`, so it is a proper submodule. Proved by induction on the number
of free slots `(univ \ s).card`; `linearIndepOn_insert` certifies each single-slot extension.

Upstream-eligible (a general `LinearIndepOn`-extension fact, no rigidity content); kept local to
this file pending a mirror — see `notes/FRICTION.md`. -/
theorem exists_extend_linearIndependent {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {n : ℕ} (hn : n ≤ Module.finrank K V)
    (g₀ : Fin n → V) (s₀ : Finset (Fin n)) (hs₀ : LinearIndepOn K g₀ (s₀ : Set (Fin n))) :
    ∃ g' : Fin n → V, (∀ i ∈ s₀, g' i = g₀ i) ∧ LinearIndependent K g' := by
  classical
  suffices H : ∀ (m : ℕ) (g : Fin n → V) (s : Finset (Fin n)),
      (Finset.univ \ s).card = m → LinearIndepOn K g (s : Set (Fin n)) →
      ∃ g' : Fin n → V, (∀ i ∈ s, g' i = g i) ∧ LinearIndependent K g' from
    H _ g₀ s₀ rfl hs₀
  intro m
  induction m with
  | zero =>
    intro g s hcard hs
    have hsub : Finset.univ ⊆ s := by
      rwa [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset] at hcard
    have hsu : s = Finset.univ := Finset.Subset.antisymm (Finset.subset_univ s) hsub
    subst hsu
    rw [Finset.coe_univ] at hs
    exact ⟨g, fun _ _ => rfl, linearIndepOn_univ_iff.mp hs⟩
  | succ m ih =>
    intro g s hcard hs
    have hne : (Finset.univ \ s).Nonempty := by
      rw [← Finset.card_pos, hcard]; omega
    obtain ⟨i, hi⟩ := hne
    rw [Finset.mem_sdiff] at hi
    have his : i ∉ s := hi.2
    have hscard : s.card < n := by
      have hss : s ⊂ Finset.univ := by
        rw [Finset.ssubset_univ_iff]
        exact fun h => his (h ▸ Finset.mem_univ i)
      have hlt := Finset.card_lt_card hss
      rwa [Finset.card_univ, Fintype.card_fin] at hlt
    have hfr : Module.finrank K (Submodule.span K (g '' (s : Set (Fin n)))) ≤ s.card := by
      have h1 := finrank_span_finset_le_card (R := K) (s.image g)
      rw [Finset.coe_image] at h1
      exact le_trans h1 Finset.card_image_le
    have hexists : ∃ w : V, w ∉ Submodule.span K (g '' (s : Set (Fin n))) := by
      by_contra hcon
      simp only [not_exists, not_not] at hcon
      rw [Submodule.eq_top_iff'.2 hcon, finrank_top] at hfr
      omega
    obtain ⟨w, hw⟩ := hexists
    have hEqOn : Set.EqOn g (Function.update g i w) (s : Set (Fin n)) := by
      intro x hx
      have hxi : x ≠ i := fun h => his (Finset.mem_coe.mp (h ▸ hx))
      rw [Function.update_of_ne hxi]
    have hLI_s : LinearIndepOn K (Function.update g i w) (s : Set (Fin n)) := hs.congr hEqOn
    have himg : (Function.update g i w) '' (s : Set (Fin n)) = g '' (s : Set (Fin n)) :=
      Set.image_congr (fun x hx => (hEqOn hx).symm)
    have hnotmem : Function.update g i w i ∉
        Submodule.span K ((Function.update g i w) '' (s : Set (Fin n))) := by
      rw [Function.update_self, himg]; exact hw
    have hLI_ins : LinearIndepOn K (Function.update g i w) (insert i (s : Set (Fin n))) :=
      (linearIndepOn_insert (by rwa [Finset.mem_coe])).mpr ⟨hLI_s, hnotmem⟩
    rw [← Finset.coe_insert] at hLI_ins
    have hcard' : (Finset.univ \ insert i s).card = m := by
      have heq : Finset.univ \ insert i s = (Finset.univ \ s).erase i := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_erase, not_or]
      have hmem : i ∈ Finset.univ \ s := Finset.mem_sdiff.2 ⟨Finset.mem_univ i, his⟩
      rw [heq, Finset.card_erase_of_mem hmem]
      omega
    obtain ⟨g', hg'eq, hg'LI⟩ := ih (Function.update g i w) (insert i s) hcard' hLI_ins
    refine ⟨g', fun j hj => ?_, hg'LI⟩
    have hji : j ≠ i := fun h => his (h ▸ hj)
    rw [hg'eq j (Finset.mem_insert_of_mem hj), Function.update_of_ne hji]

/-! ## The post-steering `fillNbr` re-choice (Phase 39 W5-L5 L5-cut-v-d) -/

/-- **Re-choosing `fillNbr` post-steering closes `PencilChartWF`'s fourth conjunct** (Phase 39 W5-L5
L5-cut-v-d, `notes/Phase39-design.md` §"W5 leaf decomposition" L5-cut-v composition finding (3)):
the last owed piece of the v-d flattening. The four `fillNbr`-free standing conjuncts
(`pencilChartWF_standing_ofCoord_toCoord`'s output — hub/neighbour selector correctness, hub-slot
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
  classical
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
on the set `S i`, then a *single* seed makes every family independent at once. This is the
load-bearing step of the L5-cut-v input-half assembly: every condition the steered seed must satisfy
— each body's hub-slot triple independence (`pencilChartPoint v ≠ 0`, the singleton case), each
link's adjacent-point distinctness (the pair case), each non-hub body's `nbrSel`-assigned point
independence, and the demoted pendant triple `{u_c, w₁, w₂}` — is exactly a
`LinearIndepOn K (pencilChartPoint …)` condition on a subset of `α`, satisfiable somewhere (the
re-seeded flattening for the standing conjuncts, witness (i) for the demoted triple).

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

/-! ## The input-half steering assembly (Phase 39 W5-L5 L5-cut-v-e) -/

/-- **The chart's constructed point depends only on the seed's `hubNormal`/`fillHub`** (Phase 39
W5-L5 L5-cut-v-e): two seeds agreeing on `hubNormal` and `fillHub` induce the same
`pencilChartPoint`, since `pencilChartPoint`/`hubSlotNormal` never read `fillNbr`. This lets the
post-steering `fillNbr` re-choice (`exists_fillNbr_pencilChartWF_of_standing`, whose output seed
shares the input's `hubNormal`/`fillHub`) preserve the steered demoted-triple independence. -/
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
  change LinearIndependent K (fun w : ↥({x, y, z} : Set α) => f ↑w)
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
  classical
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
    change pencilChartPoint seed hubSel (wsel i) = nbrSlotPoint seed hubSel nbrSel v ↑i
    simp only [nbrSlotPoint, hwsel i]
  change LinearIndependent K
    (fun i : ↥{i | (nbrSel v i).isSome} => nbrSlotPoint seed hubSel nbrSel v ↑i)
  rw [← heq]; exact hcomp

/-- **The pendant-cut input half: feasibility descends to the induced side** (Phase 39 W5-L5,
L5-cut-v-e; the input-half assembly of `notes/Phase39-design.md` §"W5 leaf decomposition" L5-cut-v
candidate route (i)). Under the sub-case-4 pendant configuration (`G.degree u_c = 3`, cut edge
`e_c : u_c–v_c` the only crossing edge, `u_c`'s two `V₁`-links `e₁ : u_c–w₁`, `e₂ : u_c–w₂`) with
`G` simple and nondegeneracy-feasible over an infinite field, `H := G.induce V₁` is itself
nondegeneracy-feasible. Steers `G`'s re-seeded feasibility witness (`exists_pencilSeed_of_nondeg`)
to a single seed making the demoted triple `{u_c, w₁, w₂}` — the residual the restriction `.mono`
owes at the demoted hub `u_c` — linearly independent *alongside* every standing `PencilChartWF`
condition (`exists_common_seed_linearIndepOn_pencilChartPoint`), re-establishes the fourth WF
conjunct by the post-steering `fillNbr` re-choice (`exists_fillNbr_pencilChartWF_of_standing`,
point-preserving so the demoted triple survives), and restricts the resulting chart realization
(`isNondegPencilRealization_pencilChartFramework_of_pencilChartWF`) to `H`
(`IsNondegPencilRealization.mono`, `u_c` the only demoted body — the sole `V₁`-vertex whose degree
changes across the one crossing edge). Feeds the IH's generic half at the one-smaller `H` in the
eventual sub-case-4 discharge (L5-cut-v-g). -/
theorem pencilNondegFeasible_induce_of_pendant_deg3 [Finite α] [Finite β] [Infinite K]
    {G : Graph α β} {V₁ : Set α} {e_c e₁ e₂ : β} {u_c v_c w₁ w₂ : α}
    (hSimple : G.Simple) (hfeas : PencilNondegFeasible K G)
    (hl_c : G.IsLink e_c u_c v_c) (hu_c : u_c ∈ V₁) (hv_c : v_c ∉ V₁)
    (hVG : V(G) = V₁ ∪ {v_c}) (hcut : (G.cutEdges V₁).ncard ≤ 1) (hdeg : G.degree u_c = 3)
    (hl₁ : G.IsLink e₁ u_c w₁) (hl₂ : G.IsLink e₂ u_c w₂)
    (hw₁ : w₁ ∈ V₁) (hw₂ : w₂ ∈ V₁) (hw12 : w₁ ≠ w₂) :
    PencilNondegFeasible K (G.induce V₁) := by
  classical
  haveI := hSimple
  haveI := hSimple.toLoopless
  haveI : Inhabited α := ⟨u_c⟩
  haveI : G.LocallyFinite := inferInstance
  have hv1 : v_c ≠ w₁ := by rintro rfl; exact hv_c hw₁
  have hv2 : v_c ≠ w₂ := by rintro rfl; exact hv_c hw₂
  -- The re-seeded feasibility witness of `G`.
  obtain ⟨F₀, normal₀, point₀, hnd⟩ := id hfeas
  obtain ⟨seed₀, hubSel, nbrSel, hWF₀, -, -⟩ := exists_pencilSeed_of_nondeg hnd
  -- The flattening `seed₀.toCoord` reproduces `seed₀`'s chart points.
  have hpt_eq : pencilChartPoint (PencilSeed.ofCoord seed₀.toCoord) hubSel
      = pencilChartPoint seed₀ hubSel := funext (pencilChartPoint_ofCoord_toCoord seed₀ hubSel)
  -- Steer to a common seed carrying every standing condition together with the demoted triple.
  obtain ⟨q, hq⟩ := exists_common_seed_linearIndepOn_pencilChartPoint (K := K) hubSel
    (fun i : α ⊕ (α × α) ⊕ Unit => match i with
      | Sum.inl v => if G.PencilHub v then ({v} : Set α) else G.closedNbhd v
      | Sum.inr (Sum.inl p) => if G.Adj p.1 p.2 then ({p.1, p.2} : Set α) else ∅
      | Sum.inr (Sum.inr _) => ({u_c, w₁, w₂} : Set α))
    (by
      rintro (v | ⟨u, v⟩ | _)
      · -- conjunct 3 (all bodies) + `hnbr` (non-hubs): satisfiable at the flattening.
        change ∃ q, LinearIndepOn K (pencilChartPoint (PencilSeed.ofCoord q) hubSel)
          (if G.PencilHub v then ({v} : Set α) else G.closedNbhd v)
        refine ⟨seed₀.toCoord, ?_⟩
        rw [hpt_eq]
        by_cases hv : G.PencilHub v
        · rw [if_pos hv]
          exact (linearIndepOn_singleton_iff K).mpr (pencilChartPoint_ne_zero seed₀ (hWF₀.2.2.1 v))
        · rw [if_neg hv]
          exact linearIndepOn_pencilChartPoint_closedNbhd seed₀ (hWF₀.2.1 v hv) (hWF₀.2.2.2.1 v hv)
      · -- conjunct 5 (adjacent pairs): satisfiable at the flattening.
        change ∃ q, LinearIndepOn K (pencilChartPoint (PencilSeed.ofCoord q) hubSel)
          (if G.Adj u v then ({u, v} : Set α) else ∅)
        by_cases hadj : G.Adj u v
        · rw [if_pos hadj]
          obtain ⟨e, he⟩ := hadj
          refine ⟨seed₀.toCoord, ?_⟩
          rw [hpt_eq]
          exact (LinearIndepOn.pair_iff (pencilChartPoint seed₀ hubSel) he.ne).mpr
            (LinearIndependent.pair_iff.mp (hWF₀.2.2.2.2 e u v he))
        · rw [if_neg hadj]
          exact ⟨seed₀.toCoord, linearIndepOn_empty K _⟩
      · -- the demoted triple: satisfiable at witness (i)'s seed.
        change ∃ q, LinearIndepOn K (pencilChartPoint (PencilSeed.ofCoord q) hubSel)
          ({u_c, w₁, w₂} : Set α)
        obtain ⟨q, hq⟩ := exists_coord_linearIndependent_pencilChartPoint_of_pendant_deg3
          hSimple hfeas hl_c hu_c hv_c hcut hdeg hl₁ hl₂ hw₁ hw₂ hw12 hubSel hWF₀.1
        exact ⟨q, linearIndepOn_triple_of_linearIndependent
          (pencilChartPoint (PencilSeed.ofCoord q) hubSel) hl₁.ne hl₂.ne hw12 hq⟩)
  set seed := PencilSeed.ofCoord q with hseed_def
  -- Reconstruct the standing `PencilChartWF` conditions at the common seed.
  have hptnz : ∀ v, pencilChartPoint seed hubSel v ≠ 0 := by
    intro v
    by_cases hv : G.PencilHub v
    · have h : LinearIndepOn K (pencilChartPoint seed hubSel)
          (if G.PencilHub v then ({v} : Set α) else G.closedNbhd v) := hq (Sum.inl v)
      rw [if_pos hv] at h
      exact (linearIndepOn_singleton_iff K).mp h
    · have h : LinearIndepOn K (pencilChartPoint seed hubSel)
          (if G.PencilHub v then ({v} : Set α) else G.closedNbhd v) := hq (Sum.inl v)
      rw [if_neg hv] at h
      exact (linearIndepOn_singleton_iff K).mp (h.mono (Set.singleton_subset_iff.mpr (Or.inl rfl)))
  have hhub_LI : ∀ v, LinearIndependent K
      ![hubSlotNormal seed hubSel v 0, hubSlotNormal seed hubSel v 1,
        hubSlotNormal seed hubSel v 2] := by
    intro v
    have h := hptnz v
    rw [pencilChartPoint] at h
    exact (cross₃_ne_zero_iff_linearIndependent _ _ _).mp h
  have hpt_LI : ∀ e u v, G.IsLink e u v → LinearIndependent K
      ![pencilChartPoint seed hubSel u, pencilChartPoint seed hubSel v] := by
    intro e u v hl
    have h : LinearIndepOn K (pencilChartPoint seed hubSel)
        (if G.Adj u v then ({u, v} : Set α) else ∅) := hq (Sum.inr (Sum.inl (u, v)))
    rw [if_pos hl.adj] at h
    rw [LinearIndependent.pair_iff]
    exact (LinearIndepOn.pair_iff (pencilChartPoint seed hubSel) hl.ne).mp h
  have hnbr_some : ∀ v, ¬ G.PencilHub v → LinearIndepOn K (nbrSlotPoint seed hubSel nbrSel v)
      {i | (nbrSel v i).isSome} := by
    intro v hv
    have h : LinearIndepOn K (pencilChartPoint seed hubSel)
        (if G.PencilHub v then ({v} : Set α) else G.closedNbhd v) := hq (Sum.inl v)
    rw [if_neg hv] at h
    exact linearIndepOn_nbrSlotPoint_isSome_of_pencilChartPoint seed (hWF₀.2.1 v hv) h
  -- Post-steering `fillNbr` re-choice: full `PencilChartWF` at a point-preserving seed.
  obtain ⟨seed', hhub_eq, hfill_eq, hWF'⟩ :=
    exists_fillNbr_pencilChartWF_of_standing hWF₀.1 hWF₀.2.1 hhub_LI hpt_LI hnbr_some
  have hpcp_eq : pencilChartPoint seed' hubSel = pencilChartPoint seed hubSel :=
    pencilChartPoint_congr hubSel hhub_eq hfill_eq
  -- The demoted triple survives (chart points unchanged by the `fillNbr` re-choice).
  have hdemote_set : LinearIndepOn K (pencilChartPoint seed' hubSel) ({u_c, w₁, w₂} : Set α) := by
    rw [hpcp_eq]; exact hq (Sum.inr (Sum.inr ()))
  -- The chart realization of `G`, then restrict to `H := G.induce V₁`.
  have hnd' := isNondegPencilRealization_pencilChartFramework_of_pencilChartWF hWF'
  have hV₁G : V₁ ⊆ V(G) := by rw [hVG]; exact Set.subset_union_left
  have hle : G.induce V₁ ≤ G := Graph.induce_le hV₁G
  have hN : N(G, u_c) = ({v_c, w₁, w₂} : Set α) :=
    Graph.neighbor_eq_of_degree_eq_three hSimple hl_c hl₁ hl₂ hv1 hv2 hw12 hdeg
  -- `u_c`'s `H`-closed neighbourhood is exactly the demoted triple.
  have hcnbhd : (G.induce V₁).closedNbhd u_c = ({u_c, w₁, w₂} : Set α) := by
    ext w
    constructor
    · rintro (rfl | ⟨e, he⟩)
      · exact Set.mem_insert _ _
      · obtain ⟨hlG, -, hwV₁⟩ := (Graph.induce_isLink G V₁ e u_c w).mp he
        have hwN : w ∈ N(G, u_c) := hlG.adj
        rw [hN] at hwN
        rcases hwN with rfl | rfl | rfl
        · exact absurd hwV₁ hv_c
        · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
        · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)
    · intro hw
      have h1 : u_c ∈ (G.induce V₁).closedNbhd u_c := Or.inl rfl
      have h2 : w₁ ∈ (G.induce V₁).closedNbhd u_c :=
        Or.inr ⟨e₁, (Graph.induce_isLink G V₁ e₁ u_c w₁).mpr ⟨hl₁, hu_c, hw₁⟩⟩
      have h3 : w₂ ∈ (G.induce V₁).closedNbhd u_c :=
        Or.inr ⟨e₂, (Graph.induce_isLink G V₁ e₂ u_c w₂).mpr ⟨hl₂, hu_c, hw₂⟩⟩
      rcases hw with rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
  refine ⟨_, _, _, hnd'.mono hle ?_⟩
  intro v hv hGhub hHnothub
  have hvV₁ : v ∈ V₁ := by rwa [Graph.vertexSet_induce] at hv
  have hveq : v = u_c := by
    by_contra hvne
    exact hHnothub ⟨hv, by
      rw [Graph.degree_induce_eq_of_ne hl_c hu_c hv_c hcut hvV₁ hvne]; exact hGhub.2⟩
  rw [hveq, hcnbhd]
  exact hdemote_set

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
proof's genericity-over-`q` step replaced by explicit steering (supplied by v-f-6). -/
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
  classical
  haveI : Fintype s := Fintype.ofFinite s
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
L5-cut-v-f, the output-half assembly's rank input)

The v-f-6 output-half assembly (`notes/Phase39-design.md` §"W5 leaf decomposition" L5-cut-v "v-f
decomposition", the v-f-6 entry) steers the induction-hypothesis's *generic* `H`-witness on `H`'s
own chart so the promoted normal families hold alongside the rank rows. The rank rows it steers are
produced here: re-seed the generic witness (`exists_pencilSeed_of_nondeg`), transport its
deficiency-target rank to the chart (the row-span depends on the supporting extensor only through
the line it spans, and the re-seeded chart hinge is a nonzero multiple of the witness hinge — v-f-2
∘ v-f-3), flatten onto the engine's coordinate space without disturbing points
(`pencilChartFramework_congr`), and extract a linearly-independent `pencilRow` subfamily of the
target size (the general `exists_independent_panelRow_subfamily_of_le_finrank` + the v-f-1 bridge).
This is exactly the `hLI` input `exists_common_seed_pencilRow_and_polynomials` (`Engine.lean`)
consumes when it steers the rank rows to the common seed. -/

/-- **The chart framework depends on the seed only through its constructed points** (Phase 39 W5-L5
L5-cut-v-f, the small helper the output-half assembly owes; parallel to the landed
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
flattening** (Phase 39 W5-L5 L5-cut-v-f, the `hLI` input of the output-half assembly's
`exists_common_seed_pencilRow_and_polynomials` call). From a nondegenerate `H`-realization `F₁`
whose rigidity-row span has rank `≥ N` (`hN`; `N :=` the deficiency target in the assembly) and a
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
  classical
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
L5-cut-v-f, the output-half assembly's promoted-family transfer)

The output-half assembly (`notes/Phase39-design.md` §"W5 leaf decomposition" L5-cut-v "v-f
decomposition", the v-f-6 entry) steers the induction hypothesis's generic `H`-witness so the
promoted normal families (witness (ii), `Witness.lean`) hold at the steered seed
`PencilSeed.ofCoord q`, then re-chooses `fillNbr` post-steering
(`exists_fillNbr_pencilChartWF_of_standing`) to close `PencilChartWF`'s fourth conjunct. The
re-chosen seed `seed'` shares the steered seed's `hubNormal`/`fillHub` but not its `fillNbr`, so the
steered promoted families must be *transported* from `PencilSeed.ofCoord q` to `seed'`.

`pencilChartNormal` reads `fillNbr` only through its non-hub branch's `cross₃` of `nbrSlotPoint`
vectors, and only at that body's `nbrSel`-*unassigned* (`none`) slots. So at any body that is either
a pencil hub (reads the free `hubNormal`, shared) or has a *fully assigned* neighbour-selector
(every `nbrSlotPoint` slot reads a `pencilChartPoint`, itself `fillNbr`-free and preserved by
`pencilChartPoint_congr`), the constructed normal is `fillNbr`-free — the design's "every promoted
family is `fillNbr`-free" fact. Every member of a promoted family `G.closedHubNbhd v` is a pencil
hub, so on the promoted-family sets the transfer is clean; the sole demoted body `u_c` (a non-hub of
`H := G.induce V₁` whose `H`-closed-neighbourhood `{u_c, w₁, w₂}` has exactly three members, forcing
`nbrSel u_c` total) is `fillNbr`-free via the fully-assigned branch. -/

/-- **The chart's constructed normal depends only on the seed's `hubNormal`/`fillHub` at a body that
is a hub or has a fully-assigned neighbour-selector** (Phase 39 W5-L5 L5-cut-v-f, the third sibling
of `pencilChartPoint_congr`/`pencilChartFramework_congr`). Two seeds agreeing on `hubNormal` and
`fillHub` induce the same `pencilChartNormal G v` whenever `v` is a pencil hub (the normal is the
shared free `hubNormal v`) or, being a non-hub, has every neighbour-slot assigned (`hassigned`: the
non-hub `cross₃` then reads only `pencilChartPoint`s of selected neighbours, preserved by
`pencilChartPoint_congr`, never the re-chosen `fillNbr`). This is what lets the point-preserving
post-steering `fillNbr` re-choice carry the steered promoted-normal independence verbatim from
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

/-- **The promoted normal families transfer across a point-preserving `fillNbr` re-choice** (Phase
39 W5-L5 L5-cut-v-f, the output-half assembly's promoted-family transfer). A `LinearIndepOn` of the
chart's constructed normals over a set `s` on which every member is a pencil hub or a fully-assigned
non-hub (`hassigned`, the "`fillNbr`-free" condition) survives replacing the seed by any `seed'`
agreeing on `hubNormal`/`fillHub` — via `LinearIndepOn.congr` and the pointwise
`pencilChartNormal_congr`. The output-half assembly (`notes/Phase39.md` *Hand-off*) applies this at
each promoted set `G.closedHubNbhd v` (`v ∈ {u_c, w₁, w₂}`), whose members are all `G`-hubs; it
discharges `hassigned` by the sub-case degree bookkeeping (a `G`-hub member of `V₁` other than the
demoted `u_c` stays an `H`-hub, and `u_c`'s neighbour-selector is total since `H.closedNbhd u_c`
has three members). -/
theorem linearIndepOn_pencilChartNormal_congr {seed seed' : PencilSeed K α}
    (hubSel nbrSel : α → Fin 3 → Option α) (G : Graph α β) {s : Set α}
    (hhub : seed'.hubNormal = seed.hubNormal) (hfill : seed'.fillHub = seed.fillHub)
    (hassigned : ∀ w ∈ s, ¬ G.PencilHub w → ∀ i, (nbrSel w i).isSome)
    (hLI : LinearIndepOn K (pencilChartNormal seed hubSel nbrSel G) s) :
    LinearIndepOn K (pencilChartNormal seed' hubSel nbrSel G) s := by
  apply hLI.congr
  intro w hw
  exact (pencilChartNormal_congr hubSel nbrSel G hhub hfill (hassigned w hw)).symm

/-! ## The output-half steering assembly (Phase 39 W5-L5 L5-cut-v-f-6)

The capstone of the pendant-cut route's `deg u_c = 3` sub-case (`notes/Phase39-design.md` §"W5 leaf
decomposition" L5-cut-v "v-f decomposition", the v-f-6 entry; `notes/Phase39.md` *Hand-off*). It is
the generic-realization analogue of the input-half assembly
`pencilNondegFeasible_induce_of_pendant_deg3` above, and structurally mirrors it: re-seed a
nondegenerate realization of `H := G.induce V₁`, steer one common seed carrying every standing
`PencilChartWF` condition, re-choose `fillNbr`, and read off the chart realization. The differences
are the two the v-f decomposition names:

* the **rank rows** are steered *alongside* the point/normal conditions in one
  `exists_common_seed_pencilRow_and_polynomials` call — the LI `pencilRow` subfamily at the
  flattening (`exists_independent_pencilRow_subfamily_at_toCoord_of_reseed`) is its `hLI`, while the
  standing point conditions (via `exists_polynomial_ne_zero_of_linearIndependent_pencilChartPoint`,
  satisfiable at the re-seeded flattening) and the promoted normal families (witness (ii), via
  `exists_polynomial_ne_zero_of_linearIndependent_pencilChartNormal`) are its `P` — so the steered
  seed realizes the target rank (v-f-4) as well as full `PencilChartWF`;
* the **promoted normal families** `LinearIndepOn K normal (G.closedHubNbhd v)`
  (`v ∈ {u_c, w₁, w₂}`) are carried out as an extra conclusion, transferred from the steered seed to
  the `fillNbr`-re-chosen seed by `linearIndepOn_pencilChartNormal_congr` — their `hassigned`
  discharge is standard degree bookkeeping (every family member is a `G`-hub in `V₁`; one other than
  `u_c` keeps its `H`-degree so stays an `H`-hub, and at the sole demotion `u_c` the selector
  `nbrSel u_c` is total since `H.closedNbhd u_c = {u_c, w₁, w₂}` has three members).

The output is exactly the sub-case-3 producer's input shape
(`hasGenericPencilRealization_of_isNondegPencilRealization_induce_pendant`, `Pair2.lean`) — a
nondegenerate realization of `H` at its deficiency-rank target — **plus** the promoted families the
`deg u_c = 3` glue (L5-cut-v-g) consumes to choose fresh pendant data at `u_c`. -/

/-- **The pendant-cut output half: a generic realization of the induced side carrying the promoted
normal families** (Phase 39 W5-L5, L5-cut-v-f-6; the output-half assembly of
`notes/Phase39-design.md` §"W5 leaf decomposition" L5-cut-v "v-f decomposition"). Under the
sub-case-4 pendant configuration (`G.degree u_c = 3`, cut edge `e_c : u_c–v_c` the only crossing
edge, `u_c`'s two `V₁`-links `e₁ : u_c–w₁`, `e₂ : u_c–w₂`) with `G` simple and
nondegeneracy-feasible over an infinite field, and a nondegenerate realization of `H := G.induce V₁`
attaining its
deficiency-rank target, there is a nondegenerate realization of `H` **at the same rank** whose
per-body normal is additionally linearly independent over each of `u_c`, `w₁`, `w₂`'s closed
hub-neighbourhood in `G`.

Re-seeds the given `H`-realization (`exists_pencilSeed_of_nondeg`), extracts the target-rank
`pencilRow` subfamily at the flattening
(`exists_independent_pencilRow_subfamily_at_toCoord_of_reseed`, v-f), and steers it to one common
seed together with every standing `PencilChartWF` point condition
and the promoted normal families (witness (ii)) via `exists_common_seed_pencilRow_and_polynomials`;
re-establishes the fourth WF conjunct by the point-preserving `fillNbr` re-choice
(`exists_fillNbr_pencilChartWF_of_standing`), reads off the chart realization
(`isNondegPencilRealization_pencilChartFramework_of_pencilChartWF`) and its rank (v-f-4
`finrank_span_rigidityRows_pencilChartFramework_eq_of_independent_pencilRow`), and transfers the
promoted families to the re-chosen seed (`linearIndepOn_pencilChartNormal_congr`). -/
theorem exists_isNondegPencilRealization_induce_promotedNormal_of_pendant_deg3
    [Finite α] [Finite β] [Infinite K] {n : ℕ} (hn : Graph.bodyBarDim n = screwDim 2)
    {G : Graph α β} {V₁ : Set α} {e_c e₁ e₂ : β} {u_c v_c w₁ w₂ : α}
    (hSimple : G.Simple) (hfeas : PencilNondegFeasible K G)
    (hl_c : G.IsLink e_c u_c v_c) (hu_c : u_c ∈ V₁) (hv_c : v_c ∉ V₁)
    (hVG : V(G) = V₁ ∪ {v_c}) (hcut : (G.cutEdges V₁).ncard ≤ 1) (hdeg : G.degree u_c = 3)
    (hl₁ : G.IsLink e₁ u_c w₁) (hl₂ : G.IsLink e₂ u_c w₂)
    (hw₁ : w₁ ∈ V₁) (hw₂ : w₂ ∈ V₁) (hw12 : w₁ ≠ w₂)
    {F₁ : BodyHingeFramework K 2 α β} {normal₁ point₁ : α → Fin 4 → K}
    (hnd₁ : IsNondegPencilRealization (G.induce V₁) F₁ normal₁ point₁)
    (hrank₁ : (Module.finrank K (Submodule.span K F₁.rigidityRows) : ℤ)
      = screwDim 2 * ((V₁.ncard : ℤ) - 1) - (G.induce V₁).deficiency n) :
    ∃ (F : BodyHingeFramework K 2 α β) (normal point : α → Fin 4 → K),
      IsNondegPencilRealization (G.induce V₁) F normal point ∧
      (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
        = screwDim 2 * ((V₁.ncard : ℤ) - 1) - (G.induce V₁).deficiency n ∧
      ∀ v ∈ ({u_c, w₁, w₂} : Set α), LinearIndepOn K normal (G.closedHubNbhd v) := by
  classical
  haveI := hSimple
  haveI := hSimple.toLoopless
  haveI : Inhabited α := ⟨u_c⟩
  haveI : G.LocallyFinite := inferInstance
  have hv1 : v_c ≠ w₁ := by rintro rfl; exact hv_c hw₁
  have hv2 : v_c ≠ w₂ := by rintro rfl; exact hv_c hw₂
  -- ── Structural facts about `H := G.induce V₁`. ────────────────────────────────────────────────
  have hVH : V(G.induce V₁) = V₁ := Graph.vertexSet_induce G V₁
  have huc_memH : u_c ∈ V(G.induce V₁) := by rw [hVH]; exact hu_c
  have hvc_deg : G.degree v_c = 1 := by
    have hGeq : G.induce (V₁ ∪ {v_c}) = G := by rw [← hVG]; exact Graph.induce_vertexSet G
    have h := Graph.degree_induce_union_singleton_far hl_c hu_c hv_c hcut
    rwa [hGeq] at h
  have hvc_nothub : ¬ G.PencilHub v_c := fun h => by have := h.2; rw [hvc_deg] at this; omega
  have hdegH_uc : (G.induce V₁).degree u_c = 2 := by
    have h := Graph.degree_eq_degree_induce_succ hl_c hu_c hv_c hcut; omega
  have hnothub_uc : ¬ (G.induce V₁).PencilHub u_c := fun h => by
    have := h.2; rw [hdegH_uc] at this; omega
  have hN : N(G, u_c) = ({v_c, w₁, w₂} : Set α) :=
    Graph.neighbor_eq_of_degree_eq_three hSimple hl_c hl₁ hl₂ hv1 hv2 hw12 hdeg
  have hcnbhd : (G.induce V₁).closedNbhd u_c = ({u_c, w₁, w₂} : Set α) := by
    ext w
    constructor
    · rintro (rfl | ⟨e, he⟩)
      · exact Set.mem_insert _ _
      · obtain ⟨hlG, -, hwV₁⟩ := (Graph.induce_isLink G V₁ e u_c w).mp he
        have hwN : w ∈ N(G, u_c) := hlG.adj
        rw [hN] at hwN
        rcases hwN with rfl | rfl | rfl
        · exact absurd hwV₁ hv_c
        · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
        · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)
    · intro hw
      have h1 : u_c ∈ (G.induce V₁).closedNbhd u_c := Or.inl rfl
      have h2 : w₁ ∈ (G.induce V₁).closedNbhd u_c :=
        Or.inr ⟨e₁, (Graph.induce_isLink G V₁ e₁ u_c w₁).mpr ⟨hl₁, hu_c, hw₁⟩⟩
      have h3 : w₂ ∈ (G.induce V₁).closedNbhd u_c :=
        Or.inr ⟨e₂, (Graph.induce_isLink G V₁ e₂ u_c w₂).mpr ⟨hl₂, hu_c, hw₂⟩⟩
      rcases hw with rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
  -- ── Re-seed the given `H`-realization. ───────────────────────────────────────────────────────
  obtain ⟨seed₁, hubSel, nbrSel, hWF₁, hptrepro, -⟩ := exists_pencilSeed_of_nondeg hnd₁
  have hpt_eq : pencilChartPoint (PencilSeed.ofCoord seed₁.toCoord) hubSel
      = pencilChartPoint seed₁ hubSel := funext (pencilChartPoint_ofCoord_toCoord seed₁ hubSel)
  -- `nbrSel u_c` is total: a `Fin 3`-selector of the 3-element `H.closedNbhd u_c` fills every slot.
  have huc_total : ∀ i, (nbrSel u_c i).isSome := by
    have hsel := hWF₁.2.1 u_c hnothub_uc
    rw [hcnbhd] at hsel
    obtain ⟨i0, hi0⟩ := hsel.2.1 u_c (Set.mem_insert _ _)
    obtain ⟨i1, hi1⟩ := hsel.2.1 w₁ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    obtain ⟨i2, hi2⟩ := hsel.2.1 w₂ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
    have hd01 : i0 ≠ i1 := by rintro rfl; rw [hi0] at hi1; exact hl₁.ne (Option.some.inj hi1)
    have hd02 : i0 ≠ i2 := by rintro rfl; rw [hi0] at hi2; exact hl₂.ne (Option.some.inj hi2)
    have hd12 : i1 ≠ i2 := by rintro rfl; rw [hi1] at hi2; exact hw12 (Option.some.inj hi2)
    intro i
    have hcard : ({i0, i1, i2} : Finset (Fin 3)).card = 3 :=
      Finset.card_eq_three.mpr ⟨i0, i1, i2, hd01, hd02, hd12, rfl⟩
    have huniv : ({i0, i1, i2} : Finset (Fin 3)) = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [Fintype.card_fin]; exact hcard)
    have hi_mem : i ∈ ({i0, i1, i2} : Finset (Fin 3)) := by rw [huniv]; exact Finset.mem_univ i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi_mem
    rcases hi_mem with h | h | h
    · simp [h, hi0]
    · simp [h, hi1]
    · simp [h, hi2]
  -- ── The standing point conditions as "nonvanishing somewhere" polynomials (at the flattening). ─
  have hpolyA : ∀ v : α, ∃ Q : MvPolynomial (α × Fin 4 × Fin 4) K,
      (∃ q, MvPolynomial.eval q Q ≠ 0) ∧
      (∀ q, MvPolynomial.eval q Q ≠ 0 →
        LinearIndepOn K (pencilChartPoint (PencilSeed.ofCoord q) hubSel)
          (if (G.induce V₁).PencilHub v then ({v} : Set α) else (G.induce V₁).closedNbhd v)) := by
    intro v
    have hwit : LinearIndepOn K (pencilChartPoint (PencilSeed.ofCoord seed₁.toCoord) hubSel)
        (if (G.induce V₁).PencilHub v then ({v} : Set α) else (G.induce V₁).closedNbhd v) := by
      rw [hpt_eq]
      by_cases hv : (G.induce V₁).PencilHub v
      · rw [if_pos hv]
        exact (linearIndepOn_singleton_iff K).mpr (pencilChartPoint_ne_zero seed₁ (hWF₁.2.2.1 v))
      · rw [if_neg hv]
        exact linearIndepOn_pencilChartPoint_closedNbhd seed₁ (hWF₁.2.1 v hv) (hWF₁.2.2.2.1 v hv)
    obtain ⟨Q, hQ0, hQ⟩ :=
      exists_polynomial_ne_zero_of_linearIndependent_pencilChartPoint hubSel id hwit
    exact ⟨Q, ⟨seed₁.toCoord, hQ0⟩, fun q hq => hQ q hq⟩
  choose PA hPA0 hPA using hpolyA
  have hpolyB : ∀ p : α × α, ∃ Q : MvPolynomial (α × Fin 4 × Fin 4) K,
      (∃ q, MvPolynomial.eval q Q ≠ 0) ∧
      (∀ q, MvPolynomial.eval q Q ≠ 0 →
        LinearIndepOn K (pencilChartPoint (PencilSeed.ofCoord q) hubSel)
          (if (G.induce V₁).Adj p.1 p.2 then ({p.1, p.2} : Set α) else ∅)) := by
    rintro ⟨u, v⟩
    have hwit : LinearIndepOn K (pencilChartPoint (PencilSeed.ofCoord seed₁.toCoord) hubSel)
        (if (G.induce V₁).Adj u v then ({u, v} : Set α) else ∅) := by
      by_cases hadj : (G.induce V₁).Adj u v
      · rw [if_pos hadj]
        obtain ⟨e, he⟩ := hadj
        rw [hpt_eq]
        exact (LinearIndepOn.pair_iff (pencilChartPoint seed₁ hubSel) he.ne).mpr
          (LinearIndependent.pair_iff.mp (hWF₁.2.2.2.2 e u v he))
      · rw [if_neg hadj]; exact linearIndepOn_empty K _
    obtain ⟨Q, hQ0, hQ⟩ :=
      exists_polynomial_ne_zero_of_linearIndependent_pencilChartPoint hubSel id hwit
    exact ⟨Q, ⟨seed₁.toCoord, hQ0⟩, fun q hq => hQ q hq⟩
  choose PB hPB0 hPB using hpolyB
  -- ── The promoted normal families as "nonvanishing somewhere" polynomials (witness (ii)). ───────
  obtain ⟨qN, hqN⟩ := exists_coord_linearIndependent_pencilChartNormal_of_pendant_deg3
    hSimple hfeas hl_c hu_c hv_c hVG hcut hdeg hl₁ hl₂ hw₁ hw₂ hw12 hubSel nbrSel hWF₁.1 hWF₁.2.1
  have hpolyC : ∀ k : Fin 3, ∃ Q : MvPolynomial (α × Fin 4 × Fin 4) K,
      (∃ q, MvPolynomial.eval q Q ≠ 0) ∧
      (∀ q, MvPolynomial.eval q Q ≠ 0 →
        LinearIndepOn K (pencilChartNormal (PencilSeed.ofCoord q) hubSel nbrSel (G.induce V₁))
          (G.closedHubNbhd (![u_c, w₁, w₂] k))) := by
    intro k
    have hmem : (![u_c, w₁, w₂] k) ∈ ({u_c, w₁, w₂} : Set α) := by fin_cases k <;> simp
    have hwit : LinearIndepOn K
        (pencilChartNormal (PencilSeed.ofCoord qN) hubSel nbrSel (G.induce V₁))
        (G.closedHubNbhd (![u_c, w₁, w₂] k)) := hqN (![u_c, w₁, w₂] k) hmem
    obtain ⟨Q, hQ0, hQ⟩ :=
      exists_polynomial_ne_zero_of_linearIndependent_pencilChartNormal hubSel nbrSel
        (G.induce V₁) id hwit
    exact ⟨Q, ⟨qN, hQ0⟩, fun q hq => hQ q hq⟩
  choose PC hPC0 hPC using hpolyC
  -- ── The rank rows at the flattening. ─────────────────────────────────────────────────────────
  obtain ⟨s, hslink, hscard, hsLI⟩ := exists_independent_pencilRow_subfamily_at_toCoord_of_reseed
    hnd₁ hptrepro (le_refl (Module.finrank K (Submodule.span K F₁.rigidityRows)))
  -- ── One common seed for the rank rows, the point conditions, and the promoted normal families. ─
  have hPsome : ∀ i : (α ⊕ (α × α)) ⊕ Fin 3,
      ∃ q, MvPolynomial.eval q ((Sum.elim (Sum.elim PA PB) PC) i) ≠ 0 := by
    rintro ((v | p) | k)
    · exact hPA0 v
    · exact hPB0 p
    · exact hPC0 k
  obtain ⟨q, hqrows, hqP⟩ := exists_common_seed_pencilRow_and_polynomials hubSel
    (G.induce V₁).endsOf hsLI (Sum.elim (Sum.elim PA PB) PC) hPsome
  have hcondA : ∀ v, LinearIndepOn K (pencilChartPoint (PencilSeed.ofCoord q) hubSel)
      (if (G.induce V₁).PencilHub v then ({v} : Set α) else (G.induce V₁).closedNbhd v) :=
    fun v => hPA v q (hqP (Sum.inl (Sum.inl v)))
  have hcondB : ∀ u v, LinearIndepOn K (pencilChartPoint (PencilSeed.ofCoord q) hubSel)
      (if (G.induce V₁).Adj u v then ({u, v} : Set α) else ∅) :=
    fun u v => hPB (u, v) q (hqP (Sum.inl (Sum.inr (u, v))))
  have hcondC : ∀ k, LinearIndepOn K
      (pencilChartNormal (PencilSeed.ofCoord q) hubSel nbrSel (G.induce V₁))
      (G.closedHubNbhd (![u_c, w₁, w₂] k)) := fun k => hPC k q (hqP (Sum.inr k))
  -- ── Reconstruct the standing `PencilChartWF` conditions at the common seed. ────────────────────
  have hptnz : ∀ v, pencilChartPoint (PencilSeed.ofCoord q) hubSel v ≠ 0 := by
    intro v
    by_cases hv : (G.induce V₁).PencilHub v
    · have h := hcondA v; rw [if_pos hv] at h
      exact (linearIndepOn_singleton_iff K).mp h
    · have h := hcondA v; rw [if_neg hv] at h
      exact (linearIndepOn_singleton_iff K).mp (h.mono (Set.singleton_subset_iff.mpr (Or.inl rfl)))
  have hhub_LI : ∀ v, LinearIndependent K
      ![hubSlotNormal (PencilSeed.ofCoord q) hubSel v 0,
        hubSlotNormal (PencilSeed.ofCoord q) hubSel v 1,
        hubSlotNormal (PencilSeed.ofCoord q) hubSel v 2] := by
    intro v
    have h := hptnz v
    rw [pencilChartPoint] at h
    exact (cross₃_ne_zero_iff_linearIndependent _ _ _).mp h
  have hpt_LI : ∀ e u v, (G.induce V₁).IsLink e u v → LinearIndependent K
      ![pencilChartPoint (PencilSeed.ofCoord q) hubSel u,
        pencilChartPoint (PencilSeed.ofCoord q) hubSel v] := by
    intro e u v hl
    have h := hcondB u v; rw [if_pos hl.adj] at h
    rw [LinearIndependent.pair_iff]
    exact (LinearIndepOn.pair_iff (pencilChartPoint (PencilSeed.ofCoord q) hubSel) hl.ne).mp h
  have hnbr_some : ∀ v, ¬ (G.induce V₁).PencilHub v →
      LinearIndepOn K (nbrSlotPoint (PencilSeed.ofCoord q) hubSel nbrSel v)
        {i | (nbrSel v i).isSome} := by
    intro v hv
    have h := hcondA v; rw [if_neg hv] at h
    exact linearIndepOn_nbrSlotPoint_isSome_of_pencilChartPoint (PencilSeed.ofCoord q)
      (hWF₁.2.1 v hv) h
  -- ── Post-steering `fillNbr` re-choice: full `PencilChartWF` at a point-preserving seed. ────────
  obtain ⟨seed', hhub_eq, hfill_eq, hWF'⟩ :=
    exists_fillNbr_pencilChartWF_of_standing hWF₁.1 hWF₁.2.1 hhub_LI hpt_LI hnbr_some
  have hnd' := isNondegPencilRealization_pencilChartFramework_of_pencilChartWF hWF'
  have hpcp_eq : pencilChartPoint seed' hubSel = pencilChartPoint (PencilSeed.ofCoord q) hubSel :=
    pencilChartPoint_congr hubSel hhub_eq hfill_eq
  have hgcongr : pencilChartFramework (PencilSeed.ofCoord q) hubSel (G.induce V₁)
      = pencilChartFramework seed' hubSel (G.induce V₁) :=
    pencilChartFramework_congr hubSel (G.induce V₁) hpcp_eq.symm
  -- ── The output rank via v-f-4. ────────────────────────────────────────────────────────────────
  have hSuppNe' : ∀ e, (pencilChartFramework seed' hubSel (G.induce V₁)).supportExtensor e ≠ 0 :=
    hnd'.1.1.2.2.1
  have hC : ∀ e u v, (G.induce V₁).IsLink e u v →
      (pencilChartFramework (PencilSeed.ofCoord q) hubSel (G.induce V₁)).supportExtensor e ≠ 0 := by
    intro e u v _
    rw [hgcongr]; exact hSuppNe' e
  have hscardZ : (Nat.card s : ℤ)
      = screwDim 2 * ((V(G.induce V₁).ncard : ℤ) - 1) - (G.induce V₁).deficiency n := by
    rw [hscard, hVH]; exact hrank₁
  have hrankq := finrank_span_rigidityRows_pencilChartFramework_eq_of_independent_pencilRow
    hn (G := G.induce V₁) ⟨u_c, huc_memH⟩ hubSel hC hslink hqrows hscardZ
  have hrankOut : (Module.finrank K (Submodule.span K
        (pencilChartFramework seed' hubSel (G.induce V₁)).rigidityRows) : ℤ)
      = screwDim 2 * ((V₁.ncard : ℤ) - 1) - (G.induce V₁).deficiency n := by
    rw [← hgcongr, hrankq, hVH]
  -- ── The promoted normal families, transferred to the re-chosen seed. ──────────────────────────
  have hassigned_core : ∀ w, G.PencilHub w → ¬ (G.induce V₁).PencilHub w →
      ∀ i, (nbrSel w i).isSome := by
    intro w hwG hwnotH i
    have hwV : w ∈ V(G) := hwG.1
    rw [hVG] at hwV
    have hwvc : w ≠ v_c := by rintro rfl; exact hvc_nothub hwG
    have hwV₁ : w ∈ V₁ := by
      rcases hwV with h | h
      · exact h
      · exact absurd (Set.mem_singleton_iff.mp h) hwvc
    have hwuc : w = u_c := by
      by_contra hne
      apply hwnotH
      refine ⟨by rw [hVH]; exact hwV₁, ?_⟩
      rw [Graph.degree_induce_eq_of_ne hl_c hu_c hv_c hcut hwV₁ hne]; exact hwG.2
    subst hwuc
    exact huc_total i
  refine ⟨pencilChartFramework seed' hubSel (G.induce V₁),
    pencilChartNormal seed' hubSel nbrSel (G.induce V₁), pencilChartPoint seed' hubSel,
    hnd', hrankOut, ?_⟩
  intro v hv
  have hcongrv := fun k => linearIndepOn_pencilChartNormal_congr hubSel nbrSel (G.induce V₁)
    hhub_eq hfill_eq (fun w hw => hassigned_core w hw.1) (hcondC k)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl | rfl
  · simpa using hcongrv 0
  · simpa using hcongrv 1
  · simpa using hcongrv 2

/-! ## The W5-L6b feasibility assembly (Phase 39 W5-L6b-i)

The split arm's feasibility producer `pencilNondegFeasible_of_ncard_closedHubNbhd_le_three_of_
triangleFree` (`notes/Phase39-design.md` §"W5 leaf decomposition" L6b) decomposes into two leaves:
**L6b-i** — the assembly below, which turns global hub/neighbour selectors plus the three
"satisfiable-somewhere" chart-point independence conditions into a full `PencilNondegFeasible`; and
**L6b-ii** — the genuinely-new general-position core producing those satisfiability conditions from
`hcard` + triangle-freeness (spike-first; still open). This file lands L6b-i. -/

open Classical in
/-- **W5-L6b-i — the pencil-feasibility assembly** (Phase 39 W5-L6b-i; `notes/Phase39-design.md`
§"W5 leaf decomposition" L6b). Given global hub/neighbour selectors correct against every body's
closed hub-neighbourhood / (at non-hubs) closed neighbourhood, and the two families of
"satisfiable-somewhere" chart-point independence conditions — one per body (`{v}` at a hub for point
nonvanishing; `closedNbhd v` at a non-hub for the closed-neighbourhood point independence feeding
the fourth WF conjunct), one per adjacent pair (`{u, v}` for adjacent-point distinctness) — the
graph is `PencilNondegFeasible`.

This is the input-half of the L5-cut-v-e template `pencilNondegFeasible_induce_of_pendant_deg3`
**minus its `.mono` restriction step**: steer all the conditions to one common seed
(`exists_common_seed_linearIndepOn_pencilChartPoint`), reconstruct the standing `PencilChartWF`
conjuncts at it, re-choose `fillNbr` for the fourth (`exists_fillNbr_pencilChartWF_of_standing`),
and read off the chart realization
(`isNondegPencilRealization_pencilChartFramework_of_pencilChartWF`) — no restriction to an induced
subgraph. `[G.Loopless]` is genuinely required: at a loop `G.IsLink e v v` the fifth WF conjunct
`LinearIndependent K ![point v, point v]` is unsatisfiable, so the conclusion is false there (the
honest split-arm producer supplies it via `G′.Simple`, L6c). -/
theorem pencilNondegFeasible_of_selectors_of_satisfiable [Finite α] [Finite β] [Infinite K]
    [Inhabited α] {G : Graph α β} [G.Loopless]
    (hubSel nbrSel : α → Fin 3 → Option α)
    (hHubSel : ∀ v, IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v))
    (hNbrSel : ∀ v, ¬ G.PencilHub v → IsFin3SelectorOf (G.closedNbhd v) (nbrSel v))
    (hsat_pt : ∀ v, ∃ q : α × Fin 4 × Fin 4 → K,
      LinearIndepOn K (pencilChartPoint (PencilSeed.ofCoord q) hubSel)
        (if G.PencilHub v then ({v} : Set α) else G.closedNbhd v))
    (hsat_adj : ∀ p : α × α, ∃ q : α × Fin 4 × Fin 4 → K,
      LinearIndepOn K (pencilChartPoint (PencilSeed.ofCoord q) hubSel)
        (if G.Adj p.1 p.2 then ({p.1, p.2} : Set α) else ∅)) :
    PencilNondegFeasible K G := by
  classical
  obtain ⟨q, hq⟩ := exists_common_seed_linearIndepOn_pencilChartPoint (K := K) hubSel
    (fun i : α ⊕ (α × α) => match i with
      | Sum.inl v => if G.PencilHub v then ({v} : Set α) else G.closedNbhd v
      | Sum.inr p => if G.Adj p.1 p.2 then ({p.1, p.2} : Set α) else ∅)
    (by
      rintro (v | p)
      · exact hsat_pt v
      · exact hsat_adj p)
  set seed := PencilSeed.ofCoord q with hseed_def
  have hptnz : ∀ v, pencilChartPoint seed hubSel v ≠ 0 := by
    intro v
    by_cases hv : G.PencilHub v
    · have h : LinearIndepOn K (pencilChartPoint seed hubSel)
          (if G.PencilHub v then ({v} : Set α) else G.closedNbhd v) := hq (Sum.inl v)
      rw [if_pos hv] at h
      exact (linearIndepOn_singleton_iff K).mp h
    · have h : LinearIndepOn K (pencilChartPoint seed hubSel)
          (if G.PencilHub v then ({v} : Set α) else G.closedNbhd v) := hq (Sum.inl v)
      rw [if_neg hv] at h
      exact (linearIndepOn_singleton_iff K).mp (h.mono (Set.singleton_subset_iff.mpr (Or.inl rfl)))
  have hhub_LI : ∀ v, LinearIndependent K
      ![hubSlotNormal seed hubSel v 0, hubSlotNormal seed hubSel v 1,
        hubSlotNormal seed hubSel v 2] := by
    intro v
    have h := hptnz v
    rw [pencilChartPoint] at h
    exact (cross₃_ne_zero_iff_linearIndependent _ _ _).mp h
  have hpt_LI : ∀ e u v, G.IsLink e u v → LinearIndependent K
      ![pencilChartPoint seed hubSel u, pencilChartPoint seed hubSel v] := by
    intro e u v hl
    have h : LinearIndepOn K (pencilChartPoint seed hubSel)
        (if G.Adj u v then ({u, v} : Set α) else ∅) := hq (Sum.inr (u, v))
    rw [if_pos hl.adj] at h
    rw [LinearIndependent.pair_iff]
    exact (LinearIndepOn.pair_iff (pencilChartPoint seed hubSel) hl.ne).mp h
  have hnbr_some : ∀ v, ¬ G.PencilHub v → LinearIndepOn K (nbrSlotPoint seed hubSel nbrSel v)
      {i | (nbrSel v i).isSome} := by
    intro v hv
    have h : LinearIndepOn K (pencilChartPoint seed hubSel)
        (if G.PencilHub v then ({v} : Set α) else G.closedNbhd v) := hq (Sum.inl v)
    rw [if_neg hv] at h
    exact linearIndepOn_nbrSlotPoint_isSome_of_pencilChartPoint seed (hNbrSel v hv) h
  obtain ⟨seed', hhub_eq, hfill_eq, hWF'⟩ :=
    exists_fillNbr_pencilChartWF_of_standing hHubSel hNbrSel hhub_LI hpt_LI hnbr_some
  exact ⟨_, _, _, isNondegPencilRealization_pencilChartFramework_of_pencilChartWF hWF'⟩

/-! ## The W5-L6b feasibility headline (Phase 39 W5-L6b) -/

/-- **W5-L6b — pencil feasibility from `≤ 3` closed hub-neighbourhoods and triangle-freeness**
(Phase 39 W5-L6b; `notes/Phase39-design.md` §"W5 leaf decomposition" L6b): a triangle-free simple
graph whose closed hub-neighbourhoods all have `≤ 3` members is `PencilNondegFeasible`. Choose
global hub / non-hub-neighbour selectors (`exists_isFin3SelectorOf_of_ncard_le_three`, `hcard` on
the hub side and `ncard_closedNbhd_le_three_of_not_pencilHub` on the non-hub side), then feed the
two satisfiability families (`exists_coord_linearIndepOn_pencilChartPoint_perBody` /
`…_adjacentPair`) to the L6b-i assembly `pencilNondegFeasible_of_selectors_of_satisfiable`.
`[G.Simple]` is required — a loop makes the fifth `IsNondegPencilRealization` conjunct
`LinearIndependent ![point v, point v]` unsatisfiable — and supplies the callers' `[G.Loopless]`.
This is the honest producer of the split arm's L6b obligation: `hcard` transfers from `G` at a safe
split (`ncard_closedHubNbhd_splitOff_le_three_of_safe`, L6a-transfer) and `htf` from the
no-proper-rigid habitat (`splitOff_triangleFree_of_noRigid`, L6d). -/
theorem pencilNondegFeasible_of_ncard_closedHubNbhd_le_three_of_triangleFree
    [Inhabited α] [Finite α] [Finite β] [Infinite K] {G : Graph α β} [G.Simple]
    (hcard : ∀ v, (G.closedHubNbhd v).ncard ≤ 3)
    (htf : ∀ e₁ e₂ e₃ x y z, x ≠ y → y ≠ z → x ≠ z →
      G.IsLink e₁ x y → G.IsLink e₂ y z → G.IsLink e₃ z x → False) :
    PencilNondegFeasible K G := by
  classical
  haveI : G.Loopless := ‹G.Simple›.toLoopless
  choose hubSel hHubSel using
    fun v => exists_isFin3SelectorOf_of_ncard_le_three (Set.toFinite _) (hcard v)
  have hnbr : ∀ v, ∃ sel : Fin 3 → Option α,
      ¬ G.PencilHub v → IsFin3SelectorOf (G.closedNbhd v) sel := by
    intro v
    by_cases hv : G.PencilHub v
    · exact ⟨fun _ => none, fun h => absurd hv h⟩
    · obtain ⟨sel, hsel⟩ :=
        exists_isFin3SelectorOf_of_ncard_le_three (Set.toFinite _)
          (ncard_closedNbhd_le_three_of_not_pencilHub hv)
      exact ⟨sel, fun _ => hsel⟩
  choose nbrSel hNbrSel using hnbr
  exact pencilNondegFeasible_of_selectors_of_satisfiable hubSel nbrSel hHubSel hNbrSel
    (exists_coord_linearIndepOn_pencilChartPoint_perBody hcard htf hubSel hHubSel)
    (exists_coord_linearIndepOn_pencilChartPoint_adjacentPair hcard htf hubSel hHubSel)

end CombinatorialRigidity.Molecular
