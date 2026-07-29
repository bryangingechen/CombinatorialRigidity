/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.Engine

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

end CombinatorialRigidity.Molecular
