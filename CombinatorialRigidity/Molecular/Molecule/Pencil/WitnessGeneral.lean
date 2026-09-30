/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.Witness

/-!
# The char-free general-position engine for chart-point independence (Phase 39 PENCIL, W5-L6b-ii)

The reusable general-position core behind the two "satisfiable-somewhere" chart-point-LI families
that the L6b-i assembly `pencilNondegFeasible_of_selectors_of_satisfiable` (`Pencil/Steer.lean`)
consumes (`notes/Phase39-design.md` §"W5 leaf decomposition" L6b), plus the per-set-shape callers
that build it: the **general-position core**
`exists_coord_linearIndepOn_pencilChartPoint_of_idx` generalizes `Witness.lean`'s v-b/v-c
constructions to an arbitrary direction map `idx` and target-index map `dtgt`, char-free of any
feasibility or graph structure beyond the selector hypothesis; the **per-set-shape callers** supply
`idx`/`dtgt` from a body's shape — the **adjacent-pair** family
`exists_coord_linearIndepOn_pencilChartPoint_adjacentPair` (built via the two/three-set
combinatorial cores `exists_idx_dtgt_pair`/`exists_idx_dtgt_triple`), and the **per-body** family
`exists_coord_linearIndepOn_pencilChartPoint_perBody` (`hsat_pt`'s hub/degree-`0`/`1`/`2` case
split).

See `notes/Phase39.md`, `notes/Phase39-design.md` (§"W5 leaf decomposition" L6b-ii), and
`blueprint/src/chapter/pencil.tex` (no blueprint node — unnamed technical infra, as the sibling
L5-cut leaves).
-/

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K]
variable {α β : Type*}

/-! ## The general-position core (Phase 39 W5-L6b-ii)

The reusable core of the v-b/v-c constructions above, extracted for the split arm's feasibility
producer `pencilNondegFeasible_of_ncard_closedHubNbhd_le_three_of_triangleFree`
(`notes/Phase39-design.md` §"W5 leaf decomposition" L6b). Its conclusion,
`∃ q, LinearIndepOn K (pencilChartPoint (PencilSeed.ofCoord q) hubSel) S`, is exactly the shape of
the two "satisfiable-somewhere" chart-point-LI families that the landed L6b-i assembly
`pencilNondegFeasible_of_selectors_of_satisfiable` (`Pencil/Steer.lean`) consumes. The **later**
L6b-ii commits build the per-set-shape direction/target maps (`{v}` / `closedNbhd v` per body,
`{p.1, p.2}` per adjacent pair) from `hcard` + triangle-freeness and wire the headline; this lemma
is the char-free general position engine they all call. -/

/-- **The general-position core of the pendant-cut somewhere-witness** (Phase 39 W5-L5/L6b-ii; the
reusable core of `exists_coord_linearIndependent_pencilChartPoint_of_pendant_deg3` and its `H`-side
sibling): given a direction map `idx` and a target-index map `dtgt`, both respected on the whole of
each body `s ∈ S`'s closed hub-neighbourhood — `idx` injective there and avoiding `dtgt s`, and the
targets `dtgt` distinct across `S` — some seed coordinate `q` makes each `s ∈ S`'s chart point a
nonzero multiple of the distinct standard basis vector `e_{dtgt s}`, hence the chart points
`LinearIndepOn` over `S`.

The construction is v-b's verbatim: `idx` becomes the seed's hub normals, and each body's
selector-induced slots are padded to an injective avoiding-`dtgt s` triple
(`exists_injective_extension_of_isFin3SelectorOf`), so its `cross₃` point is a nonzero multiple of
`e_{dtgt s}` (`exists_smul_cross₃_pi_single`); distinctness of the `dtgt` targets then gives
independence (`linearIndepOn_smul_pi_single`). Unlike v-b/v-c it fixes no configuration: the
per-set-shape callers supply `idx`/`dtgt` and the two combinatorial facts, so this lemma is entirely
char-free general position with no feasibility or graph structure of its own beyond `hHubSel`. -/
theorem exists_coord_linearIndepOn_pencilChartPoint_of_idx
    {G : Graph α β} {S : Set α} {idx dtgt : α → Fin 4}
    (hubSel : α → Fin 3 → Option α)
    (hHubSel : ∀ v, IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v))
    (hdinj : Set.InjOn dtgt S)
    (havoid : ∀ s ∈ S, ∀ x ∈ G.closedHubNbhd s, idx x ≠ dtgt s)
    (hinj : ∀ s ∈ S, Set.InjOn idx (G.closedHubNbhd s)) :
    ∃ q : α × Fin 4 × Fin 4 → K,
      LinearIndepOn K (pencilChartPoint (PencilSeed.ofCoord q) hubSel) S := by
  -- Per body in `S`, pull out the injective avoiding-`dtgt s` slot extension.
  have hex : ∀ s : α, ∃ σ : Fin 3 → Fin 4, s ∈ S →
      Function.Injective σ ∧ (∀ i, σ i ≠ dtgt s) ∧
        (∀ i w, hubSel s i = some w → σ i = idx w) := by
    intro s
    by_cases hs : s ∈ S
    · obtain ⟨σ, hσinj, hσd, hσm⟩ :=
        exists_injective_extension_of_isFin3SelectorOf (hHubSel s) (havoid s hs) (hinj s hs)
      exact ⟨σ, fun _ => ⟨hσinj, hσd, hσm⟩⟩
    · exact ⟨fun _ => 0, fun h => absurd h hs⟩
  choose σfam hσfam using hex
  -- The seed: hub normals from `idx`, fills from the per-body extensions (v-b's seed).
  set q : α × Fin 4 × Fin 4 → K :=
    fun p => Fin.cases (motive := fun _ => K)
      ((Pi.single (idx p.1) (1 : K) : Fin 4 → K) p.2.2)
      (fun j => (Pi.single (σfam p.1 j) (1 : K) : Fin 4 → K) p.2.2) p.2.1
    with hq_def
  refine ⟨q, ?_⟩
  have hHubN : ∀ v : α, (PencilSeed.ofCoord q).hubNormal v = Pi.single (idx v) (1 : K) := by
    intro v; funext i; simp [PencilSeed.ofCoord, hq_def]
  have hFillH : ∀ (v : α) (j : Fin 3),
      (PencilSeed.ofCoord q).fillHub v j = Pi.single (σfam v j) (1 : K) := by
    intro v j; funext i; simp [PencilSeed.ofCoord, hq_def]
  -- Each body's slot triple reads back the extension's basis vectors.
  have hslot : ∀ (v : α), (∀ i w, hubSel v i = some w → σfam v i = idx w) →
      ∀ i, hubSlotNormal (PencilSeed.ofCoord q) hubSel v i = Pi.single (σfam v i) (1 : K) := by
    intro v hmatch i
    cases hcase : hubSel v i with
    | none => simp only [hubSlotNormal, hcase, hFillH]
    | some w =>
        simp only [hubSlotNormal, hcase]
        rw [hHubN, hmatch i w hcase]
  -- On each `s ∈ S`, the chart point is a nonzero multiple of `e_{dtgt s}`.
  have hpt : ∀ s : α, ∃ cc : K, s ∈ S →
      cc ≠ 0 ∧ pencilChartPoint (PencilSeed.ofCoord q) hubSel s
        = cc • (Pi.single (dtgt s) 1 : Fin 4 → K) := by
    intro s
    by_cases hs : s ∈ S
    · obtain ⟨hσinj, hσd, hσm⟩ := hσfam s hs
      have hsl := hslot s hσm
      have h01 : σfam s 0 ≠ σfam s 1 := fun h => absurd (hσinj h) (by decide)
      have h02 : σfam s 0 ≠ σfam s 2 := fun h => absurd (hσinj h) (by decide)
      have h12 : σfam s 1 ≠ σfam s 2 := fun h => absurd (hσinj h) (by decide)
      obtain ⟨cc, hcc, hcross⟩ :=
        exists_smul_cross₃_pi_single (K := K) (hσd 0) (hσd 1) (hσd 2) h01 h02 h12
      exact ⟨cc, fun _ => ⟨hcc, by rw [pencilChartPoint, hsl 0, hsl 1, hsl 2, hcross]⟩⟩
    · exact ⟨1, fun h => absurd h hs⟩
  choose ccfam hccfam using hpt
  -- Distinct targets, rescaled by nonzero scalars, are independent.
  exact (linearIndepOn_smul_pi_single (K := K) (J := dtgt) (c := ccfam) hdinj
    (fun x hx => (hccfam x hx).1)).congr (fun x hx => ((hccfam x hx).2).symm)

/-! ## The per-set-shape callers (Phase 39 W5-L6b-ii)

The two "satisfiable-somewhere" chart-point-LI families that the landed L6b-i assembly
`pencilNondegFeasible_of_selectors_of_satisfiable` (`Pencil/Steer.lean`) consumes, built by
supplying the general-position core `exists_coord_linearIndepOn_pencilChartPoint_of_idx` with a
per-set-shape direction map `idx` and target map `dtgt`. This commit lands the **adjacent-pair**
family (`hsat_adj`'s shape); the per-body family (`hsat_pt`) and the headline wiring are the next
pieces (`notes/Phase39-design.md` §"W5 leaf decomposition" L6b-ii).

For the adjacent pair `{u, v}` (`u ~ v`), the two closed hub-neighbourhoods overlap only in
`{u, v}`: a common third hub `w` (a hub adjacent to both `u` and `v`) would close a triangle
`u–v–w`, excluded by triangle-freeness (`htf`). So the direction map `idx` can be built by a single
injection of `closedHubNbhd u` into a `3`-value palette avoiding `dtgt u`, plus a second injection
of the (disjoint) rest of `closedHubNbhd v` into the values avoiding both `dtgt v` and the image of
the overlap — the exact cardinalities coming from the `≤ 3` bound (`hcard`). -/

/-- **Inject a finite set into a finite set of no-smaller cardinality** (Phase 39 W5-L6b-ii helper;
upstream-eligible, `notes/FRICTION.md` [mirror-candidate]): if `T.ncard ≤ P.ncard`, there is a total
`f` injective on `T` and mapping `T` into `P` (junk `default` off `T`). Used to build the
per-set-shape direction maps `idx` the general-position core consumes. -/
theorem exists_injOn_mapsTo_of_ncard_le {γ δ : Type*} [Inhabited δ] {T : Set γ} {P : Set δ}
    (hT : T.Finite) (hP : P.Finite) (hle : T.ncard ≤ P.ncard) :
    ∃ f : γ → δ, Set.InjOn f T ∧ ∀ x ∈ T, f x ∈ P := by
  classical
  have := hT.fintype
  have := hP.fintype
  have hc : Fintype.card T ≤ Fintype.card P := by simpa using hle
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hc
  refine ⟨fun x => if h : x ∈ T then (e ⟨x, h⟩ : δ) else default, ?_, ?_⟩
  · intro x hx y hy hxy
    simp only [dite_eq_left hx, dite_eq_left hy] at hxy
    exact Subtype.ext_iff.mp (e.injective (Subtype.ext hxy))
  · intro x hx
    simp only [dite_eq_left hx]
    exact (e ⟨x, hx⟩).2

/-- **The direction/target maps for an adjacent pair** (Phase 39 W5-L6b-ii combinatorial core): for
distinct `u, v` whose two `≤ 3`-cardinality sets `U, V` overlap only inside `{u, v}` (`hcap` — the
triangle-freeness exclusion at the call site), there are direction/target maps `idx dtgt` with
`dtgt` injective on `{u, v}`, `idx` injective on each of `U, V` and avoiding the respective target.
`idx` sends `U` injectively into `{0, 1, 3}` (avoiding `dtgt u = 2`) via
`exists_injOn_mapsTo_of_ncard_le`, picks `dtgt v` outside `{2} ∪ idx '' (U ∩ V)`, and sends the
disjoint remainder `V \ U` into the values avoiding `dtgt v` and `idx '' (U ∩ V)` — the palette
sizes matching `V \ U` exactly because `|U ∩ V|` cancels (`≤ 3` on each side). -/
theorem exists_idx_dtgt_pair [Finite α] {u v : α} (huv : u ≠ v) {U V : Set α}
    (hcap : U ∩ V ⊆ ({u, v} : Set α)) (hU3 : U.ncard ≤ 3) (hV3 : V.ncard ≤ 3) :
    ∃ idx dtgt : α → Fin 4,
      Set.InjOn dtgt {u, v} ∧
      (∀ x ∈ U, idx x ≠ dtgt u) ∧ (∀ x ∈ V, idx x ≠ dtgt v) ∧
      Set.InjOn idx U ∧ Set.InjOn idx V := by
  classical
  -- `fu`: inject `U` into `{0, 1, 3}` (avoiding `dtgt u = 2`).
  have hPu : ({0, 1, 3} : Set (Fin 4)).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨0, 1, 3, by decide, by decide, by decide, rfl⟩
  obtain ⟨fu, hfu_inj, hfu_map⟩ :=
    exists_injOn_mapsTo_of_ncard_le (T := U) (P := ({0, 1, 3} : Set (Fin 4)))
      (Set.toFinite _) (Set.toFinite _) (hU3.trans hPu.ge)
  have hfu_ne2 : ∀ x ∈ U, fu x ≠ 2 := by
    intro x hx h2
    have hm := hfu_map x hx
    rw [h2] at hm
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with h | h | h <;> exact absurd h (by decide)
  set m := (U ∩ V).ncard with hm_def
  have hm2 : m ≤ 2 := by
    have h := Set.ncard_le_ncard hcap (Set.toFinite _)
    rwa [Set.ncard_pair huv] at h
  have hfuimg : (fu '' (U ∩ V)).ncard = m := (hfu_inj.mono Set.inter_subset_left).ncard_image
  have hXcard : (insert (2 : Fin 4) (fu '' (U ∩ V))).ncard ≤ 3 := by
    refine (Set.ncard_insert_le _ _).trans ?_
    rw [hfuimg]; omega
  obtain ⟨dtgtv, hdtgtv⟩ : ∃ d : Fin 4, d ∉ insert (2 : Fin 4) (fu '' (U ∩ V)) := by
    by_contra hcon
    push Not at hcon
    have huniv : (insert (2 : Fin 4) (fu '' (U ∩ V))) = Set.univ := Set.eq_univ_of_forall hcon
    rw [huniv, Set.ncard_univ] at hXcard
    simp [Nat.card_eq_fintype_card] at hXcard
  rw [Set.mem_insert_iff] at hdtgtv
  push Not at hdtgtv
  obtain ⟨hdtgtv2, hdtgtv_img⟩ := hdtgtv
  set Y := insert dtgtv (fu '' (U ∩ V)) with hY_def
  have hVU_add : (V \ U).ncard + m = V.ncard := by
    rw [hm_def, ← Set.sdiff_self_inter (s := V) (t := U), Set.inter_comm V U]
    exact Set.ncard_sdiff_add_ncard_of_subset Set.inter_subset_right (Set.toFinite _)
  have hY_card : Y.ncard = m + 1 := by
    rw [hY_def, Set.ncard_insert_of_notMem hdtgtv_img (Set.toFinite _), hfuimg]
  have hPv_add : (Set.univ \ Y).ncard + Y.ncard = 4 := by
    have h := Set.ncard_sdiff_add_ncard_of_subset (Set.subset_univ Y)
      (Set.toFinite (Set.univ : Set (Fin 4)))
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h
  obtain ⟨gv, hgv_inj, hgv_map⟩ :=
    exists_injOn_mapsTo_of_ncard_le (T := V \ U) (P := Set.univ \ Y)
      (Set.toFinite _) (Set.toFinite _) (by omega)
  have hgv_ne : ∀ x ∈ V \ U, gv x ≠ dtgtv ∧ gv x ∉ fu '' (U ∩ V) := by
    intro x hx
    have h := (hgv_map x hx).2
    rw [hY_def, Set.mem_insert_iff] at h
    push Not at h
    exact h
  -- The maps, with evaluation lemmas.
  set idx : α → Fin 4 := fun x => if x ∈ U then fu x else gv x with hidx_def
  set dtgt : α → Fin 4 := fun x => if x = u then (2 : Fin 4) else dtgtv with hdtgt_def
  have hidxU : ∀ x, x ∈ U → idx x = fu x := fun x hx => by rw [hidx_def]; exact ite_eq_left hx
  have hidxnU : ∀ x, x ∉ U → idx x = gv x := fun x hx => by rw [hidx_def]; exact ite_eq_right hx
  have hdtu : dtgt u = 2 := by rw [hdtgt_def]; exact ite_eq_left rfl
  have hdtv : dtgt v = dtgtv := by rw [hdtgt_def]; exact ite_eq_right huv.symm
  refine ⟨idx, dtgt, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · rw [hdtu, hdtv] at hxy; exact absurd hxy hdtgtv2.symm
    · rw [hdtu, hdtv] at hxy; exact absurd hxy hdtgtv2
    · rfl
  · intro x hx
    rw [hidxU x hx, hdtu]; exact hfu_ne2 x hx
  · intro x hx
    rw [hdtv]
    by_cases hxU : x ∈ U
    · rw [hidxU x hxU]
      have him : fu x ∈ fu '' (U ∩ V) := Set.mem_image_of_mem fu ⟨hxU, hx⟩
      intro h; rw [h] at him; exact hdtgtv_img him
    · rw [hidxnU x hxU]; exact (hgv_ne x ⟨hx, hxU⟩).1
  · intro x hx y hy hxy
    rw [hidxU x hx, hidxU y hy] at hxy
    exact hfu_inj hx hy hxy
  · intro x hx y hy hxy
    by_cases hxU : x ∈ U <;> by_cases hyU : y ∈ U
    · rw [hidxU x hxU, hidxU y hyU] at hxy; exact hfu_inj hxU hyU hxy
    · exfalso
      rw [hidxU x hxU, hidxnU y hyU] at hxy
      have h1 : fu x ∈ fu '' (U ∩ V) := Set.mem_image_of_mem fu ⟨hxU, hx⟩
      exact (hgv_ne y ⟨hy, hyU⟩).2 (hxy ▸ h1)
    · exfalso
      rw [hidxnU x hxU, hidxU y hyU] at hxy
      have h1 : fu y ∈ fu '' (U ∩ V) := Set.mem_image_of_mem fu ⟨hyU, hy⟩
      exact (hgv_ne x ⟨hx, hxU⟩).2 (hxy ▸ h1)
    · rw [hidxnU x hxU, hidxnU y hyU] at hxy
      exact hgv_inj ⟨hx, hxU⟩ ⟨hy, hyU⟩ hxy

/-- **The direction/target maps for a non-hub body and its (≤ 2) neighbours** (Phase 39 W5-L6b-ii
combinatorial core, the three-set analogue of `exists_idx_dtgt_pair`): for a non-hub centre `v`
with neighbours `a`, `b` (all distinct), whose closed hub-neighbourhoods `Xa`, `Xb` are `≤ 3` and
overlap in `≤ 2` *external* hubs (`hcap`; neither `a ∈ Xb` nor `b ∈ Xa`, by triangle-freeness),
and whose own closed hub-neighbourhood `Xv ⊆ {a, b}` sits inside `Xa`/`Xb` (`haXv`/`hbXv` — a hub
neighbour of `v` is a hub, hence in its own set), there are direction/target maps `idx dtgt` with
`dtgt` injective on `{v, a, b}` and `idx` injective on each of `Xv`, `Xa`, `Xb` avoiding the
respective target.

`Xa` injects into `{0, 1, 2}` (avoiding `dtgt a = 3`); `dtgt b` is picked as `idx a` when `a ∈ Xa`
(so `idx b`, forced off `dtgt b`, differs from `idx a`, giving injectivity on `Xv`) and otherwise
off `{3} ∪ idx '' (Xa ∩ Xb)`; the disjoint remainder `Xb \ Xa` fills the values avoiding `dtgt b`
and `idx '' (Xa ∩ Xb)`; `dtgt v` avoids `{3, dtgt b, idx b}`. The palette sizes match because
`(Xa ∩ Xb).ncard` cancels — `≤ 3` on each side against a `≤ 2` overlap, exactly the pair core's
arithmetic with the third set layered on. -/
theorem exists_idx_dtgt_triple [Finite α] {v a b : α}
    (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b) {Xv Xa Xb : Set α}
    (hXv : Xv ⊆ ({a, b} : Set α))
    (haXv : a ∈ Xv → a ∈ Xa) (hbXv : b ∈ Xv → b ∈ Xb)
    (haXb : a ∉ Xb) (hbXa : b ∉ Xa)
    (hcap : (Xa ∩ Xb).ncard ≤ 2) (hXa3 : Xa.ncard ≤ 3) (hXb3 : Xb.ncard ≤ 3) :
    ∃ idx dtgt : α → Fin 4,
      Set.InjOn dtgt ({v, a, b} : Set α) ∧
      (∀ x ∈ Xv, idx x ≠ dtgt v) ∧ (∀ x ∈ Xa, idx x ≠ dtgt a) ∧ (∀ x ∈ Xb, idx x ≠ dtgt b) ∧
      Set.InjOn idx Xv ∧ Set.InjOn idx Xa ∧ Set.InjOn idx Xb := by
  classical
  -- Inject `Xa` into `{0, 1, 2}` (avoiding `dtgt a = 3`).
  have hPa : ({0, 1, 2} : Set (Fin 4)).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨0, 1, 2, by decide, by decide, by decide, rfl⟩
  obtain ⟨fa, hfa_inj, hfa_map⟩ :=
    exists_injOn_mapsTo_of_ncard_le (T := Xa) (P := ({0, 1, 2} : Set (Fin 4)))
      (Set.toFinite _) (Set.toFinite _) (hXa3.trans hPa.ge)
  have hfa_ne3 : ∀ x ∈ Xa, fa x ≠ 3 := by
    intro x hx h3
    have hm := hfa_map x hx
    rw [h3] at hm
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with h | h | h <;> exact absurd h (by decide)
  set m := (Xa ∩ Xb).ncard with hm_def
  have hfaimg : (fa '' (Xa ∩ Xb)).ncard = m := (hfa_inj.mono Set.inter_subset_left).ncard_image
  -- `dtgt b`: `idx a` when `a ∈ Xa` (forcing `idx b ≠ idx a`), else off `{3} ∪ idx '' (Xa ∩ Xb)`.
  obtain ⟨db, hdb_notin, hdb_a⟩ :
      ∃ db : Fin 4, db ∉ insert (3 : Fin 4) (fa '' (Xa ∩ Xb)) ∧ (a ∈ Xa → db = fa a) := by
    by_cases ha : a ∈ Xa
    · refine ⟨fa a, ?_, fun _ => rfl⟩
      simp only [Set.mem_insert_iff, not_or]
      refine ⟨hfa_ne3 a ha, ?_⟩
      rintro ⟨w, hw, hwa⟩
      have hweqa : w = a := hfa_inj (Set.inter_subset_left hw) ha hwa
      exact haXb (hweqa ▸ Set.inter_subset_right hw)
    · have hins_le : (insert (3 : Fin 4) (fa '' (Xa ∩ Xb))).ncard ≤ 3 := by
        refine (Set.ncard_insert_le _ _).trans ?_
        rw [hfaimg]; omega
      obtain ⟨db, hdb⟩ : ∃ d : Fin 4, d ∉ insert (3 : Fin 4) (fa '' (Xa ∩ Xb)) := by
        by_contra hcon
        push Not at hcon
        have huniv : insert (3 : Fin 4) (fa '' (Xa ∩ Xb)) = Set.univ := Set.eq_univ_of_forall hcon
        rw [huniv, Set.ncard_univ] at hins_le
        simp [Nat.card_eq_fintype_card] at hins_le
      exact ⟨db, hdb, fun h => absurd h ha⟩
  rw [Set.mem_insert_iff] at hdb_notin
  push Not at hdb_notin
  obtain ⟨hdb3, hdb_img⟩ := hdb_notin
  -- The `dtgt b`-avoiding palette for the disjoint remainder `Xb \ Xa`.
  set Y := insert db (fa '' (Xa ∩ Xb)) with hY_def
  have hbXa_add : (Xb \ Xa).ncard + m = Xb.ncard := by
    rw [hm_def, ← Set.sdiff_self_inter (s := Xb) (t := Xa), Set.inter_comm Xa Xb]
    exact Set.ncard_sdiff_add_ncard_of_subset Set.inter_subset_left (Set.toFinite _)
  have hY_card : Y.ncard = m + 1 := by
    rw [hY_def, Set.ncard_insert_of_notMem hdb_img (Set.toFinite _), hfaimg]
  have hPrem_add : (Set.univ \ Y).ncard + Y.ncard = 4 := by
    have h := Set.ncard_sdiff_add_ncard_of_subset (Set.subset_univ Y)
      (Set.toFinite (Set.univ : Set (Fin 4)))
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h
  obtain ⟨gb, hgb_inj, hgb_map⟩ :=
    exists_injOn_mapsTo_of_ncard_le (T := Xb \ Xa) (P := Set.univ \ Y)
      (Set.toFinite _) (Set.toFinite _) (by omega)
  have hgb_ne : ∀ x ∈ Xb \ Xa, gb x ≠ db ∧ gb x ∉ fa '' (Xa ∩ Xb) := by
    intro x hx
    have h := (hgb_map x hx).2
    rw [hY_def, Set.mem_insert_iff] at h
    push Not at h
    exact h
  -- The index map, with evaluation lemmas.
  set idx : α → Fin 4 := fun x => if x ∈ Xa then fa x else gb x with hidx_def
  have hidxXa : ∀ x, x ∈ Xa → idx x = fa x := fun x hx => by rw [hidx_def]; exact ite_eq_left hx
  have hidxnXa : ∀ x, x ∉ Xa → idx x = gb x := fun x hx => by rw [hidx_def]; exact ite_eq_right hx
  have hidxb : idx b = gb b := hidxnXa b hbXa
  -- `dtgt v` avoiding `{3, db, idx b}`.
  obtain ⟨dv, hdv⟩ : ∃ d : Fin 4, d ∉ ({3, db, idx b} : Set (Fin 4)) := by
    have hle : ({3, db, idx b} : Set (Fin 4)).ncard ≤ 3 := by
      refine (Set.ncard_insert_le _ _).trans ?_
      refine Nat.add_le_add_right ((Set.ncard_insert_le _ _).trans ?_) 1
      simp
    by_contra hcon
    push Not at hcon
    have huniv : ({3, db, idx b} : Set (Fin 4)) = Set.univ := Set.eq_univ_of_forall hcon
    rw [huniv, Set.ncard_univ] at hle
    simp [Nat.card_eq_fintype_card] at hle
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hdv
  obtain ⟨hdv3, hdv_db, hdv_idxb⟩ := hdv
  -- The target map, with evaluation lemmas.
  set dtgt : α → Fin 4 := fun x => if x = v then dv else if x = a then (3 : Fin 4) else db
    with hdtgt_def
  have hdtv : dtgt v = dv := by rw [hdtgt_def]; exact ite_eq_left rfl
  have hdta : dtgt a = 3 := by
    rw [hdtgt_def]; exact (ite_eq_right (Ne.symm hva)).trans (ite_eq_left rfl)
  have hdtb : dtgt b = db := by
    rw [hdtgt_def]; exact (ite_eq_right (Ne.symm hvb)).trans (ite_eq_right (Ne.symm hab))
  refine ⟨idx, dtgt, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `dtgt` injective on `{v, a, b}`.
    intro x hx y hy hxy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · rfl
    · rw [hdtv, hdta] at hxy; exact absurd hxy hdv3
    · rw [hdtv, hdtb] at hxy; exact absurd hxy hdv_db
    · rw [hdtv, hdta] at hxy; exact absurd hxy.symm hdv3
    · rfl
    · rw [hdta, hdtb] at hxy; exact absurd hxy (Ne.symm hdb3)
    · rw [hdtv, hdtb] at hxy; exact absurd hxy.symm hdv_db
    · rw [hdta, hdtb] at hxy; exact absurd hxy.symm (Ne.symm hdb3)
    · rfl
  · -- avoid at `v`.
    intro x hx
    rw [hdtv]
    have hxab := hXv hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxab
    rcases hxab with rfl | rfl
    · rw [hidxXa x (haXv hx), ← hdb_a (haXv hx)]; exact Ne.symm hdv_db
    · exact Ne.symm hdv_idxb
  · -- avoid at `a`.
    intro x hx
    rw [hidxXa x hx, hdta]
    exact hfa_ne3 x hx
  · -- avoid at `b`.
    intro x hx
    rw [hdtb]
    by_cases hxXa : x ∈ Xa
    · rw [hidxXa x hxXa]
      intro heq
      exact hdb_img (heq ▸ Set.mem_image_of_mem fa ⟨hxXa, hx⟩)
    · rw [hidxnXa x hxXa]
      exact (hgb_ne x ⟨hx, hxXa⟩).1
  · -- `idx` injective on `Xv`.
    intro x hx y hy hxy
    have hxab := hXv hx
    have hyab := hXv hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxab hyab
    rcases hxab with hxa | hxb
    · rcases hyab with hya | hyb
      · rw [hxa, hya]
      · exfalso
        have hax : a ∈ Xv := hxa ▸ hx
        have hby : b ∈ Xv := hyb ▸ hy
        rw [hxa, hyb, hidxXa a (haXv hax), ← hdb_a (haXv hax), hidxb] at hxy
        exact (hgb_ne b ⟨hbXv hby, hbXa⟩).1 hxy.symm
    · rcases hyab with hya | hyb
      · exfalso
        have hbx : b ∈ Xv := hxb ▸ hx
        have hay : a ∈ Xv := hya ▸ hy
        rw [hxb, hya, hidxXa a (haXv hay), ← hdb_a (haXv hay), hidxb] at hxy
        exact (hgb_ne b ⟨hbXv hbx, hbXa⟩).1 hxy
      · rw [hxb, hyb]
  · -- `idx` injective on `Xa`.
    intro x hx y hy hxy
    rw [hidxXa x hx, hidxXa y hy] at hxy
    exact hfa_inj hx hy hxy
  · -- `idx` injective on `Xb`.
    intro x hx y hy hxy
    by_cases hxXa : x ∈ Xa <;> by_cases hyXa : y ∈ Xa
    · rw [hidxXa x hxXa, hidxXa y hyXa] at hxy; exact hfa_inj hxXa hyXa hxy
    · exfalso
      rw [hidxXa x hxXa, hidxnXa y hyXa] at hxy
      exact (hgb_ne y ⟨hy, hyXa⟩).2 (hxy ▸ Set.mem_image_of_mem fa ⟨hxXa, hx⟩)
    · exfalso
      rw [hidxnXa x hxXa, hidxXa y hyXa] at hxy
      exact (hgb_ne x ⟨hx, hxXa⟩).2 (hxy ▸ Set.mem_image_of_mem fa ⟨hyXa, hy⟩)
    · rw [hidxnXa x hxXa, hidxnXa y hyXa] at hxy
      exact hgb_inj ⟨hx, hxXa⟩ ⟨hy, hyXa⟩ hxy

open Classical in
/-- **The adjacent-pair somewhere-witness family** (Phase 39 W5-L6b-ii; the `hsat_adj` input of
`pencilNondegFeasible_of_selectors_of_satisfiable`): for any ordered pair `p`, some seed coordinate
`q` makes the chart points linearly independent over `{p.1, p.2}` when the two are adjacent (over
`∅` otherwise, trivially). Adjacency plus triangle-freeness (`htf`) confine the two closed
hub-neighbourhoods' overlap to `{p.1, p.2}`, so `exists_idx_dtgt_pair` builds the direction/target
maps the general-position core `exists_coord_linearIndepOn_pencilChartPoint_of_idx` consumes; the
`≤ 3` bound is `hcard`. -/
theorem exists_coord_linearIndepOn_pencilChartPoint_adjacentPair
    [Finite α] {G : Graph α β} [G.Loopless]
    (hcard : ∀ v, (G.closedHubNbhd v).ncard ≤ 3)
    (htf : ∀ e₁ e₂ e₃ x y z, x ≠ y → y ≠ z → x ≠ z →
      G.IsLink e₁ x y → G.IsLink e₂ y z → G.IsLink e₃ z x → False)
    (hubSel : α → Fin 3 → Option α)
    (hHubSel : ∀ v, IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v))
    (p : α × α) :
    ∃ q : α × Fin 4 × Fin 4 → K,
      LinearIndepOn K (pencilChartPoint (PencilSeed.ofCoord q) hubSel)
        (if G.Adj p.1 p.2 then ({p.1, p.2} : Set α) else ∅) := by
  obtain ⟨u, v⟩ := p
  by_cases hadj : G.Adj u v
  · rw [ite_eq_left hadj]
    obtain ⟨e_uv, hl_uv⟩ := hadj
    have huv : u ≠ v := hl_uv.ne
    -- Triangle-freeness confines the two hub-neighbourhoods' overlap to `{u, v}`.
    have hcap : G.closedHubNbhd u ∩ G.closedHubNbhd v ⊆ ({u, v} : Set α) := by
      intro w hw
      by_cases hwu : w = u
      · exact Or.inl hwu
      by_cases hwv : w = v
      · exact Or.inr hwv
      obtain ⟨e_uw, hl_uw⟩ := hw.1.2.resolve_left hwu
      obtain ⟨e_vw, hl_vw⟩ := hw.2.2.resolve_left hwv
      exact (htf e_uv e_vw e_uw u v w huv (Ne.symm hwv) (Ne.symm hwu)
        hl_uv hl_vw hl_uw.symm).elim
    obtain ⟨idx, dtgt, hdinj, hav_u, hav_v, hinj_u, hinj_v⟩ :=
      exists_idx_dtgt_pair huv hcap (hcard u) (hcard v)
    refine exists_coord_linearIndepOn_pencilChartPoint_of_idx (S := ({u, v} : Set α))
      (idx := idx) (dtgt := dtgt) hubSel hHubSel hdinj ?_ ?_
    · intro s hs
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with rfl | rfl
      · exact hav_u
      · exact hav_v
    · intro s hs
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with rfl | rfl
      · exact hinj_u
      · exact hinj_v
  · rw [ite_eq_right hadj]
    exact ⟨fun _ => 0, linearIndepOn_empty K _⟩

/-! ## The per-body somewhere-witness (Phase 39 W5-L6b-ii)

The `hsat_pt` input of the L6b-i assembly `pencilNondegFeasible_of_selectors_of_satisfiable`
(`Pencil/Steer.lean`): a per-body chart-point-LI family over `{v}` at a hub and over `closedNbhd v`
at a non-hub. The hub / degree-`0` cases are the trivial singleton witness; a non-hub of degree `1`
reuses the two-set core `exists_idx_dtgt_pair`; a non-hub of degree `2` uses the three-set core
`exists_idx_dtgt_triple`, whose overlap hypotheses triangle-freeness (`htf`) and the `≤ 3` bounds
(`hcard`, `ncard_closedNbhd_le_three_of_not_pencilHub`) discharge. -/

/-- **The singleton somewhere-witness** (Phase 39 W5-L6b-ii helper): the trivial one-set case — at
any body `v`, some seed coordinate makes the chart point independent over `{v}` (nonzero), by
injecting `closedHubNbhd v` (`≤ 3` by `hcard`) into `{0, 1, 2}` and targeting `3`. Used for the hub
branch (`{v}`) and the degree-`0` non-hub branch (`closedNbhd v = {v}`) of the per-body family. -/
private theorem exists_coord_linearIndepOn_pencilChartPoint_hubSingleton [Finite α]
    {G : Graph α β} (hcard : ∀ v, (G.closedHubNbhd v).ncard ≤ 3)
    (hubSel : α → Fin 3 → Option α)
    (hHubSel : ∀ v, IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v)) (v : α) :
    ∃ q : α × Fin 4 × Fin 4 → K,
      LinearIndepOn K (pencilChartPoint (PencilSeed.ofCoord q) hubSel) ({v} : Set α) := by
  obtain ⟨idx, hidx_inj, hidx_map⟩ :=
    exists_injOn_mapsTo_of_ncard_le (T := G.closedHubNbhd v) (P := ({0, 1, 2} : Set (Fin 4)))
      (Set.toFinite _) (Set.toFinite _)
      ((hcard v).trans (Set.ncard_eq_three.mpr ⟨0, 1, 2, by decide, by decide, by decide, rfl⟩).ge)
  refine exists_coord_linearIndepOn_pencilChartPoint_of_idx (S := ({v} : Set α))
    (idx := idx) (dtgt := fun _ => 3) hubSel hHubSel ?_ ?_ ?_
  · intro x hx y hy _
    rw [Set.mem_singleton_iff] at hx hy
    rw [hx, hy]
  · intro s hs x hx
    rw [Set.mem_singleton_iff] at hs
    subst hs
    intro heq
    have hm := hidx_map x hx
    rw [heq] at hm
    simp at hm
  · intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    exact hidx_inj

open Classical in
/-- **The per-body somewhere-witness family** (Phase 39 W5-L6b-ii; the `hsat_pt` input of
`pencilNondegFeasible_of_selectors_of_satisfiable`): for any body `v`, some seed coordinate `q`
makes the chart points independent over `{v}` at a hub (point nonvanishing) and over the closed
neighbourhood `closedNbhd v` at a non-hub. The hub / degree-`0` cases reduce to the singleton
witness; a non-hub of degree `1` (`closedNbhd v = {v, a}`) reuses the two-set core
`exists_idx_dtgt_pair`; a non-hub of degree `2` (`closedNbhd v = {v, a, b}`) uses the three-set
core `exists_idx_dtgt_triple` — its overlap hypotheses discharged by triangle-freeness (`htf`
excludes `a ~ b` and any common hub-neighbour closing a triangle) and the `≤ 3` bounds. -/
theorem exists_coord_linearIndepOn_pencilChartPoint_perBody
    [Finite α] [Finite β] {G : Graph α β} [G.Loopless]
    (hcard : ∀ v, (G.closedHubNbhd v).ncard ≤ 3)
    (htf : ∀ e₁ e₂ e₃ x y z, x ≠ y → y ≠ z → x ≠ z →
      G.IsLink e₁ x y → G.IsLink e₂ y z → G.IsLink e₃ z x → False)
    (hubSel : α → Fin 3 → Option α)
    (hHubSel : ∀ v, IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v))
    (v : α) :
    ∃ q : α × Fin 4 × Fin 4 → K,
      LinearIndepOn K (pencilChartPoint (PencilSeed.ofCoord q) hubSel)
        (if G.PencilHub v then ({v} : Set α) else G.closedNbhd v) := by
  by_cases hv : G.PencilHub v
  · rw [ite_eq_left hv]
    exact exists_coord_linearIndepOn_pencilChartPoint_hubSingleton hcard hubSel hHubSel v
  · rw [ite_eq_right hv]
    -- `v` non-hub: `closedNbhd v = insert v N(G,v)`, `|N(G,v)| ≤ 2`.
    have hdeg : G.degree v ≤ 2 := by
      by_contra hcon
      push Not at hcon
      by_cases hvV : v ∈ V(G)
      · exact hv ⟨hvV, by omega⟩
      · have h0 := Graph.degree_eq_zero_of_notMem (G := G) hvV
        omega
    have hNle : (N(G, v)).encard ≤ G.eDegree v :=
      (Graph.encard_adj_le_encard_inc).trans (Graph.encard_inc_le_eDegree)
    have heDeg : (G.degree v : ℕ∞) = G.eDegree v := Graph.natCast_degree_eq G v
    rw [← heDeg] at hNle
    have hcast : (G.degree v : ℕ∞) ≤ (2 : ℕ∞) := by exact_mod_cast hdeg
    have hNle2 : (N(G, v)).encard ≤ (2 : ℕ∞) := hNle.trans hcast
    obtain ⟨hNfin, hNcard⟩ := Set.encard_le_coe_iff_finite_ncard_le.mp hNle2
    obtain h0 | h1 | h2 :
        (N(G, v)).ncard = 0 ∨ (N(G, v)).ncard = 1 ∨ (N(G, v)).ncard = 2 := by
      rcases Nat.lt_or_ge (N(G, v)).ncard 1 with h | h
      · exact Or.inl (by omega)
      · rcases Nat.lt_or_ge (N(G, v)).ncard 2 with h' | h'
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr (le_antisymm hNcard h'))
    · -- degree `0`: `closedNbhd v = {v}`.
      have hcn : G.closedNbhd v = insert v (N(G, v)) := rfl
      have hS : G.closedNbhd v = ({v} : Set α) := by
        rw [hcn, (Set.ncard_eq_zero hNfin).mp h0]; simp
      rw [hS]
      exact exists_coord_linearIndepOn_pencilChartPoint_hubSingleton hcard hubSel hHubSel v
    · -- degree `1`: `closedNbhd v = {v, a}`, two-set core.
      obtain ⟨a, h1eq⟩ := Set.ncard_eq_one.mp h1
      have haN : a ∈ N(G, v) := by rw [h1eq]; simp
      obtain ⟨e_a, hl_a⟩ : G.Adj v a := haN
      have hva : v ≠ a := hl_a.ne
      have hcn : G.closedNbhd v = insert v (N(G, v)) := rfl
      have hS : G.closedNbhd v = ({v, a} : Set α) := by rw [hcn, h1eq]
      have hcap : G.closedHubNbhd v ∩ G.closedHubNbhd a ⊆ ({v, a} : Set α) := by
        intro w hw
        rcases hw.1.2 with heq | ⟨e_vw, hl_vw⟩
        · exact Or.inl heq
        · have hwN : w ∈ N(G, v) := hl_vw.adj
          rw [h1eq] at hwN
          exact Or.inr hwN
      obtain ⟨idx, dtgt, hdinj, hav_u, hav_a, hinj_u, hinj_a⟩ :=
        exists_idx_dtgt_pair hva hcap (hcard v) (hcard a)
      rw [hS]
      refine exists_coord_linearIndepOn_pencilChartPoint_of_idx (S := ({v, a} : Set α))
        (idx := idx) (dtgt := dtgt) hubSel hHubSel hdinj ?_ ?_
      · intro s hs x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl
        · exact hav_u x hx
        · exact hav_a x hx
      · intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl
        · exact hinj_u
        · exact hinj_a
    · -- degree `2`: `closedNbhd v = {v, a, b}`, three-set core.
      obtain ⟨a, b, hab, h2eq⟩ := Set.ncard_eq_two.mp h2
      have haN : a ∈ N(G, v) := by rw [h2eq]; simp
      have hbN : b ∈ N(G, v) := by rw [h2eq]; simp
      obtain ⟨e_a, hl_a⟩ : G.Adj v a := haN
      obtain ⟨e_b, hl_b⟩ : G.Adj v b := hbN
      have hva : v ≠ a := hl_a.ne
      have hvb : v ≠ b := hl_b.ne
      have hcn : G.closedNbhd v = insert v (N(G, v)) := rfl
      have hS : G.closedNbhd v = ({v, a, b} : Set α) := by rw [hcn, h2eq]
      have hXv : G.closedHubNbhd v ⊆ ({a, b} : Set α) := by
        intro w hw
        rcases hw.2 with heq | ⟨e_vw, hl_vw⟩
        · exact absurd (heq ▸ hw.1) hv
        · have hwN : w ∈ N(G, v) := hl_vw.adj
          rw [h2eq] at hwN
          exact hwN
      have haXv : a ∈ G.closedHubNbhd v → a ∈ G.closedHubNbhd a := fun h => ⟨h.1, Or.inl rfl⟩
      have hbXv : b ∈ G.closedHubNbhd v → b ∈ G.closedHubNbhd b := fun h => ⟨h.1, Or.inl rfl⟩
      have haXb : a ∉ G.closedHubNbhd b := by
        intro haCHb
        rcases haCHb.2 with heq | ⟨e_ba, hl_ba⟩
        · exact hab heq
        · exact htf e_a e_ba e_b v a b hva hab hvb hl_a hl_ba.symm hl_b.symm
      have hbXa : b ∉ G.closedHubNbhd a := by
        intro hbCHa
        rcases hbCHa.2 with heq | ⟨e_ab, hl_ab⟩
        · exact hab heq.symm
        · exact htf e_b e_ab e_a v b a hvb hab.symm hva hl_b hl_ab.symm hl_a.symm
      have hcap : (G.closedHubNbhd a ∩ G.closedHubNbhd b).ncard ≤ 2 := by
        have hsub : G.closedHubNbhd a ∩ G.closedHubNbhd b ⊆ G.closedHubNbhd a \ {a} := by
          intro w hw
          refine ⟨hw.1, ?_⟩
          intro hwa
          rw [Set.mem_singleton_iff] at hwa
          exact haXb (hwa ▸ hw.2)
        refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
        by_cases hha : G.PencilHub a
        · have haa : a ∈ G.closedHubNbhd a := ⟨hha, Or.inl rfl⟩
          rw [Set.ncard_sdiff_singleton_of_mem haa]
          have := hcard a; omega
        · have haCN : a ∈ G.closedNbhd a := Or.inl rfl
          have hsub2 : G.closedHubNbhd a \ {a} ⊆ G.closedNbhd a \ {a} := by
            intro w hw
            exact ⟨hw.1.2, hw.2⟩
          refine (Set.ncard_le_ncard hsub2 (Set.toFinite _)).trans ?_
          rw [Set.ncard_sdiff_singleton_of_mem haCN]
          have := ncard_closedNbhd_le_three_of_not_pencilHub hha
          omega
      obtain ⟨idx, dtgt, hdinj, hav_v, hav_a, hav_b, hinj_v, hinj_a, hinj_b⟩ :=
        exists_idx_dtgt_triple hva hvb hab hXv haXv hbXv haXb hbXa hcap (hcard a) (hcard b)
      rw [hS]
      refine exists_coord_linearIndepOn_pencilChartPoint_of_idx (S := ({v, a, b} : Set α))
        (idx := idx) (dtgt := dtgt) hubSel hHubSel hdinj ?_ ?_
      · intro s hs x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl | rfl
        · exact hav_v x hx
        · exact hav_a x hx
        · exact hav_b x hx
      · intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl | rfl
        · exact hinj_v
        · exact hinj_a
        · exact hinj_b

end CombinatorialRigidity.Molecular
