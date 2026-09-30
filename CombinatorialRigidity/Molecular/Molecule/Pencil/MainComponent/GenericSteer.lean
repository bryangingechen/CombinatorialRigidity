/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.Steer

/-!
# Steering a realization of a subgraph (Phase 40o EARS, T2 + T3)

`lem:pencil-generic-steer`'s two claims: (a) a nondegenerate realization of a simple,
nondegeneracy-feasible `G` steers to a chart point whose restriction to a subgraph `H` is
nondegenerate too, whenever every hub of `G` demoted in `H` loses only non-hub neighbours
((MC-190), (MC-188)); (b) a generic pencil realization of `H` steers, in the same way, to also
carry finitely many normal-independence and point–normal non-orthogonality conditions read off a
second nondegenerate realization ((MC-191)). Both route through the reseed at given selectors
(`exists_pencilSeed_of_nondeg_of_selectors`, `Reseed.lean`) and the rows-polynomial steering engine
(`Engine.lean`, `Steer.lean`).

## Main definitions

* `pencilDotPoly` — the dot product of a chart point and a chart normal, as a polynomial in the
  seed.

## Main statements

* `exists_coord_linearIndependent_pencilChartPoint_of_other_nonhub` — (MC-188): a hub with two
  non-hub-adjacent neighbours has a chart seed at which the hub and its two neighbours' points are
  independent.
* `exists_isNondegPencilRealization_restrict_of_demoted` — (MC-190), T2: `G` has a
  nondegenerate realization whose restriction to a demoted-safe subgraph `H` is nondegenerate.
* `exists_isNondegPencilRealization_steer` — (MC-191), T3: a generic pencil realization of `H`
  steers to also satisfy a second realization's finitely many normal-independence and
  point–normal non-orthogonality conditions.

See `notes/Phase40o.md`, `notes/pencil/workbook/K-main-MC19.md` (route B, (MC-186)–(MC-191)), and
`blueprint/src/chapter/main-component.tex` (`lem:pencil-generic-steer`).
-/

open scoped Matrix Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

/-! ## T2 (part 1): (MC-188), the pendant witness with non-hub neighbours -/

theorem exists_coord_linearIndependent_pencilChartPoint_of_other_nonhub
    [Finite α] {G : Graph α β} {e₁ e₂ : β} {h w₁ w₂ : α}
    (hSimple : G.Simple) (hfeas : PencilNondegFeasible K G) (hub_u : G.PencilHub h)
    (hl₁ : G.IsLink e₁ h w₁) (hl₂ : G.IsLink e₂ h w₂) (hw12 : w₁ ≠ w₂)
    (hother : ∀ y, G.Adj h y → y ≠ w₁ → y ≠ w₂ → ¬ G.PencilHub y)
    (hubSel : α → Fin 3 → Option α)
    (hHubSel : ∀ v, IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v)) :
    ∃ q : α × Fin 4 × Fin 4 → K,
      LinearIndependent K
        ![pencilChartPoint (PencilSeed.ofCoord q) hubSel h,
          pencilChartPoint (PencilSeed.ofCoord q) hubSel w₁,
          pencilChartPoint (PencilSeed.ofCoord q) hubSel w₂] := by
  classical
  have := hSimple
  have hw1u : w₁ ≠ h := hl₁.ne.symm
  have hw2u : w₂ ≠ h := hl₂.ne.symm
  obtain ⟨F₀, nrm₀, pt₀, hnd₀⟩ := id hfeas
  have hcard : ∀ v ∈ V(G), (G.closedHubNbhd v).ncard ≤ 3 := fun v hv =>
    ncard_closedHubNbhd_le_three_of_isNondegPencilRealization hnd₀ hv
  -- `h`'s closed hub-neighbourhood lies in `{h, w₁, w₂}`: its other neighbours are non-hubs.
  have hSu : ∀ x ∈ G.closedHubNbhd h, x = h ∨ x = w₁ ∨ x = w₂ := by
    rintro x ⟨hxhub, hx | ⟨e, he⟩⟩
    · exact Or.inl hx
    · by_cases h1 : x = w₁
      · exact Or.inr (Or.inl h1)
      by_cases h2 : x = w₂
      · exact Or.inr (Or.inr h2)
      exact absurd hxhub (hother x ⟨e, he⟩ h1 h2)
  -- The triangle exclusions: `w₁ ~ w₂` is barred whenever either is a hub.
  have hw2_nadj1 : G.PencilHub w₂ → ¬ G.Adj w₁ w₂ := by
    rintro hh2 ⟨e₃, he₃⟩
    exact not_pencilNondegFeasible_of_triangle_two_hubs hw1u (Ne.symm hw2u) hw12
      hl₁.symm hl₂ he₃.symm hub_u hh2 hfeas
  have hw1_nadj2 : G.PencilHub w₁ → ¬ G.Adj w₂ w₁ := by
    rintro hh1 ⟨e₃, he₃⟩
    exact not_pencilNondegFeasible_of_triangle_two_hubs hw2u (Ne.symm hw1u) (Ne.symm hw12)
      hl₂.symm hl₁ he₃.symm hub_u hh1 hfeas
  have hnw2_1 : w₂ ∉ G.closedHubNbhd w₁ := by
    rintro ⟨hh2, h' | ⟨e, he⟩⟩
    · exact hw12 h'.symm
    · exact hw2_nadj1 hh2 ⟨e, he⟩
  have hnw1_2 : w₁ ∉ G.closedHubNbhd w₂ := by
    rintro ⟨hh1, h' | ⟨e, he⟩⟩
    · exact hw12 h'
    · exact hw1_nadj2 hh1 ⟨e, he⟩
  -- At most one third-party member at `w₁` (hub: the `≤ 3` bound; non-hub: degree `≤ 2`).
  have huniq_1 : ∀ x ∈ G.closedHubNbhd w₁, ∀ y ∈ G.closedHubNbhd w₁,
      x ≠ h → x ≠ w₁ → y ≠ h → y ≠ w₁ → x = y := by
    intro x hx y hy hxu hxw hyu hyw
    by_contra hxy
    obtain ⟨hxhub, hx' | ⟨ex, hex⟩⟩ := hx
    · exact hxw hx'
    obtain ⟨hyhub, hy' | ⟨ey, hey⟩⟩ := hy
    · exact hyw hy'
    by_cases h1 : G.PencilHub w₁
    · have hsub4 : ({w₁, h, x, y} : Set α) ⊆ G.closedHubNbhd w₁ := by
        rintro z (rfl | rfl | rfl | rfl)
        · exact ⟨h1, Or.inl rfl⟩
        · exact ⟨hub_u, Or.inr ⟨e₁, hl₁.symm⟩⟩
        · exact ⟨hxhub, Or.inr ⟨ex, hex⟩⟩
        · exact ⟨hyhub, Or.inr ⟨ey, hey⟩⟩
      have h4card : ({w₁, h, x, y} : Set α).ncard = 4 := by
        rw [Set.ncard_insert_of_notMem (by simp [hw1u, Ne.symm hxw, Ne.symm hyw]),
          Set.ncard_insert_of_notMem (by simp [Ne.symm hxu, Ne.symm hyu]),
          Set.ncard_insert_of_notMem (by simp [hxy]), Set.ncard_singleton]
      have hle := Set.ncard_le_ncard hsub4 (Set.toFinite _)
      have hb := hcard w₁ hl₁.right_mem
      rw [h4card] at hle
      omega
    · have hdeg1 : G.degree w₁ ≤ 2 := by
        by_contra hcon
        exact h1 ⟨hl₁.right_mem, by omega⟩
      have hsub3 : ({h, x, y} : Set α) ⊆ N(G, w₁) := by
        rintro z (rfl | rfl | rfl)
        · exact hl₁.symm.adj
        · exact ⟨ex, hex⟩
        · exact ⟨ey, hey⟩
      have h3card : ({h, x, y} : Set α).ncard = 3 :=
        Set.ncard_eq_three.mpr ⟨h, x, y, Ne.symm hxu, Ne.symm hyu, hxy, rfl⟩
      have hle := Set.ncard_le_ncard hsub3 (Set.toFinite _)
      rw [h3card, ← Graph.degree_eq_ncard_adj] at hle
      omega
  have huniq_2 : ∀ x ∈ G.closedHubNbhd w₂, ∀ y ∈ G.closedHubNbhd w₂,
      x ≠ h → x ≠ w₂ → y ≠ h → y ≠ w₂ → x = y := by
    intro x hx y hy hxu hxw hyu hyw
    by_contra hxy
    obtain ⟨hxhub, hx' | ⟨ex, hex⟩⟩ := hx
    · exact hxw hx'
    obtain ⟨hyhub, hy' | ⟨ey, hey⟩⟩ := hy
    · exact hyw hy'
    by_cases h2 : G.PencilHub w₂
    · have hsub4 : ({w₂, h, x, y} : Set α) ⊆ G.closedHubNbhd w₂ := by
        rintro z (rfl | rfl | rfl | rfl)
        · exact ⟨h2, Or.inl rfl⟩
        · exact ⟨hub_u, Or.inr ⟨e₂, hl₂.symm⟩⟩
        · exact ⟨hxhub, Or.inr ⟨ex, hex⟩⟩
        · exact ⟨hyhub, Or.inr ⟨ey, hey⟩⟩
      have h4card : ({w₂, h, x, y} : Set α).ncard = 4 := by
        rw [Set.ncard_insert_of_notMem (by simp [hw2u, Ne.symm hxw, Ne.symm hyw]),
          Set.ncard_insert_of_notMem (by simp [Ne.symm hxu, Ne.symm hyu]),
          Set.ncard_insert_of_notMem (by simp [hxy]), Set.ncard_singleton]
      have hle := Set.ncard_le_ncard hsub4 (Set.toFinite _)
      have hb := hcard w₂ hl₂.right_mem
      rw [h4card] at hle
      omega
    · have hdeg2 : G.degree w₂ ≤ 2 := by
        by_contra hcon
        exact h2 ⟨hl₂.right_mem, by omega⟩
      have hsub3 : ({h, x, y} : Set α) ⊆ N(G, w₂) := by
        rintro z (rfl | rfl | rfl)
        · exact hl₂.symm.adj
        · exact ⟨ex, hex⟩
        · exact ⟨ey, hey⟩
      have h3card : ({h, x, y} : Set α).ncard = 3 :=
        Set.ncard_eq_three.mpr ⟨h, x, y, Ne.symm hxu, Ne.symm hyu, hxy, rfl⟩
      have hle := Set.ncard_le_ncard hsub3 (Set.toFinite _)
      rw [h3card, ← Graph.degree_eq_ncard_adj] at hle
      omega
  -- The global basis-index assignment (no fourth named body: the other neighbours are non-hubs).
  set idx : α → Fin 4 := fun x =>
    if x = h then 0 else if x = w₁ then 1 else if x = w₂ then 2 else 3 with hidx_def
  have hidx_u : idx h = 0 := by simp [hidx_def]
  have hidx_1 : idx w₁ = 1 := by simp [hidx_def, hw1u]
  have hidx_2 : idx w₂ = 2 := by simp [hidx_def, hw2u, Ne.symm hw12]
  have hidx_x : ∀ x, x ≠ h → x ≠ w₁ → x ≠ w₂ → idx x = 3 := by
    intro x h1 h2 h3
    simp [hidx_def, h1, h2, h3]
  have hSw1 : ∀ x ∈ G.closedHubNbhd w₁, x = h ∨ x = w₁ ∨ idx x = 3 := by
    intro x hx
    by_cases h1 : x = h
    · exact Or.inl h1
    by_cases h2 : x = w₁
    · exact Or.inr (Or.inl h2)
    refine Or.inr (Or.inr (hidx_x x h1 h2 ?_))
    rintro rfl; exact hnw2_1 hx
  have hSw2 : ∀ x ∈ G.closedHubNbhd w₂, x = h ∨ x = w₂ ∨ idx x = 3 := by
    intro x hx
    by_cases h1 : x = h
    · exact Or.inl h1
    by_cases h2 : x = w₂
    · exact Or.inr (Or.inl h2)
    refine Or.inr (Or.inr (hidx_x x h1 ?_ h2))
    rintro rfl; exact hnw1_2 hx
  have hd_u : ∀ x ∈ G.closedHubNbhd h, idx x ≠ (3 : Fin 4) := by
    intro x hx
    rcases hSu x hx with rfl | rfl | rfl
    · rw [hidx_u]; decide
    · rw [hidx_1]; decide
    · rw [hidx_2]; decide
  have hinj_u : Set.InjOn idx (G.closedHubNbhd h) := by
    intro x hx y hy hxy
    rcases hSu x hx with rfl | rfl | rfl <;> rcases hSu y hy with rfl | rfl | rfl
    · rfl
    · rw [hidx_u, hidx_1] at hxy; exact absurd hxy (by decide)
    · rw [hidx_u, hidx_2] at hxy; exact absurd hxy (by decide)
    · rw [hidx_1, hidx_u] at hxy; exact absurd hxy (by decide)
    · rfl
    · rw [hidx_1, hidx_2] at hxy; exact absurd hxy (by decide)
    · rw [hidx_2, hidx_u] at hxy; exact absurd hxy (by decide)
    · rw [hidx_2, hidx_1] at hxy; exact absurd hxy (by decide)
    · rfl
  have hd_1 : ∀ x ∈ G.closedHubNbhd w₁, idx x ≠ (2 : Fin 4) := by
    intro x hx
    rcases hSw1 x hx with rfl | rfl | h3
    · rw [hidx_u]; decide
    · rw [hidx_1]; decide
    · rw [h3]; decide
  have hinj_1 : Set.InjOn idx (G.closedHubNbhd w₁) := by
    intro x hx y hy hxy
    rcases hSw1 x hx with rfl | rfl | hx3 <;> rcases hSw1 y hy with rfl | rfl | hy3
    · rfl
    · rw [hidx_u, hidx_1] at hxy; exact absurd hxy (by decide)
    · rw [hidx_u, hy3] at hxy; exact absurd hxy (by decide)
    · rw [hidx_1, hidx_u] at hxy; exact absurd hxy (by decide)
    · rfl
    · rw [hidx_1, hy3] at hxy; exact absurd hxy (by decide)
    · rw [hx3, hidx_u] at hxy; exact absurd hxy (by decide)
    · rw [hx3, hidx_1] at hxy; exact absurd hxy (by decide)
    · have hxu : x ≠ h := by rintro rfl; rw [hidx_u] at hx3; exact absurd hx3 (by decide)
      have hxw : x ≠ w₁ := by rintro rfl; rw [hidx_1] at hx3; exact absurd hx3 (by decide)
      have hyu : y ≠ h := by rintro rfl; rw [hidx_u] at hy3; exact absurd hy3 (by decide)
      have hyw : y ≠ w₁ := by rintro rfl; rw [hidx_1] at hy3; exact absurd hy3 (by decide)
      exact huniq_1 x hx y hy hxu hxw hyu hyw
  have hd_2 : ∀ x ∈ G.closedHubNbhd w₂, idx x ≠ (1 : Fin 4) := by
    intro x hx
    rcases hSw2 x hx with rfl | rfl | h3
    · rw [hidx_u]; decide
    · rw [hidx_2]; decide
    · rw [h3]; decide
  have hinj_2 : Set.InjOn idx (G.closedHubNbhd w₂) := by
    intro x hx y hy hxy
    rcases hSw2 x hx with rfl | rfl | hx3 <;> rcases hSw2 y hy with rfl | rfl | hy3
    · rfl
    · rw [hidx_u, hidx_2] at hxy; exact absurd hxy (by decide)
    · rw [hidx_u, hy3] at hxy; exact absurd hxy (by decide)
    · rw [hidx_2, hidx_u] at hxy; exact absurd hxy (by decide)
    · rfl
    · rw [hidx_2, hy3] at hxy; exact absurd hxy (by decide)
    · rw [hx3, hidx_u] at hxy; exact absurd hxy (by decide)
    · rw [hx3, hidx_2] at hxy; exact absurd hxy (by decide)
    · have hxu : x ≠ h := by rintro rfl; rw [hidx_u] at hx3; exact absurd hx3 (by decide)
      have hxw : x ≠ w₂ := by rintro rfl; rw [hidx_2] at hx3; exact absurd hx3 (by decide)
      have hyu : y ≠ h := by rintro rfl; rw [hidx_u] at hy3; exact absurd hy3 (by decide)
      have hyw : y ≠ w₂ := by rintro rfl; rw [hidx_2] at hy3; exact absurd hy3 (by decide)
      exact huniq_2 x hx y hy hxu hxw hyu hyw
  obtain ⟨σu, hσu_inj, hσu_d, hσu_match⟩ :=
    exists_injective_extension_of_isFin3SelectorOf (hHubSel h) hd_u hinj_u
  obtain ⟨σ1, hσ1_inj, hσ1_d, hσ1_match⟩ :=
    exists_injective_extension_of_isFin3SelectorOf (hHubSel w₁) hd_1 hinj_1
  obtain ⟨σ2, hσ2_inj, hσ2_d, hσ2_match⟩ :=
    exists_injective_extension_of_isFin3SelectorOf (hHubSel w₂) hd_2 hinj_2
  set fill : α → Fin 3 → Fin 4 → K := fun v =>
    if v = h then fun j => Pi.single (σu j) (1 : K)
    else if v = w₁ then fun j => Pi.single (σ1 j) (1 : K)
    else if v = w₂ then fun j => Pi.single (σ2 j) (1 : K)
    else fun _ _ => 0 with hfill_def
  have hfill_u : fill h = fun j => Pi.single (σu j) (1 : K) := by simp [hfill_def]
  have hfill_1 : fill w₁ = fun j => Pi.single (σ1 j) (1 : K) := by simp [hfill_def, hw1u]
  have hfill_2 : fill w₂ = fun j => Pi.single (σ2 j) (1 : K) := by
    simp [hfill_def, hw2u, Ne.symm hw12]
  set q : α × Fin 4 × Fin 4 → K :=
    fun p => Fin.cases (motive := fun _ => K)
      ((Pi.single (idx p.1) (1 : K) : Fin 4 → K) p.2.2)
      (fun j => fill p.1 j p.2.2) p.2.1
    with hq_def
  refine ⟨q, ?_⟩
  have hHubN : ∀ v : α, (PencilSeed.ofCoord q).hubNormal v = Pi.single (idx v) (1 : K) := by
    intro v
    funext i
    simp [PencilSeed.ofCoord, hq_def]
  have hFillH : ∀ (v : α) (j : Fin 3), (PencilSeed.ofCoord q).fillHub v j = fill v j := by
    intro v j
    funext i
    simp [PencilSeed.ofCoord, hq_def]
  have hslot : ∀ (v : α) (σv : Fin 3 → Fin 4), fill v = (fun j => Pi.single (σv j) (1 : K)) →
      (∀ i w, hubSel v i = some w → σv i = idx w) →
      ∀ i, hubSlotNormal (PencilSeed.ofCoord q) hubSel v i = Pi.single (σv i) (1 : K) := by
    intro v σv hfv hmatch i
    cases hcase : hubSel v i with
    | none => simp only [hubSlotNormal, hcase, hFillH, hfv]
    | some w =>
        simp only [hubSlotNormal, hcase]
        rw [hHubN, hmatch i w hcase]
  have hslot_u := hslot h σu hfill_u hσu_match
  have hslot_1 := hslot w₁ σ1 hfill_1 hσ1_match
  have hslot_2 := hslot w₂ σ2 hfill_2 hσ2_match
  have hPu := exists_smul_pencilChartPoint_of_hubSlotNormal_eq_pi_single hσu_inj hσu_d hslot_u
  have hP1 := exists_smul_pencilChartPoint_of_hubSlotNormal_eq_pi_single hσ1_inj hσ1_d hslot_1
  have hP2 := exists_smul_pencilChartPoint_of_hubSlotNormal_eq_pi_single hσ2_inj hσ2_d hslot_2
  obtain ⟨cu, hcu0, hcu⟩ := hPu
  obtain ⟨c1, hc10, hc1⟩ := hP1
  obtain ⟨c2, hc20, hc2⟩ := hP2
  have hbase := (linearIndependent_pi_single_triple (K := K) (a := 3) (b := 2) (c := 1)
    (by decide) (by decide) (by decide)).units_smul
    ![Units.mk0 cu hcu0, Units.mk0 c1 hc10, Units.mk0 c2 hc20]
  have heq : ((![Units.mk0 cu hcu0, Units.mk0 c1 hc10, Units.mk0 c2 hc20] : Fin 3 → Kˣ) •
      ![(Pi.single (3 : Fin 4) (1 : K) : Fin 4 → K), Pi.single 2 1, Pi.single 1 1])
      = ![pencilChartPoint (PencilSeed.ofCoord q) hubSel h,
          pencilChartPoint (PencilSeed.ofCoord q) hubSel w₁,
          pencilChartPoint (PencilSeed.ofCoord q) hubSel w₂] := by
    funext i
    fin_cases i <;> simp [Units.smul_def, hcu, hc1, hc2]
  rwa [heq] at hbase

/-! ## T2 (part 2): the steering in `G`'s chart and the restriction ((MC-190)) -/

/-- **The closed neighbourhood is the body and its neighbours.** -/
theorem _root_.Graph.closedNbhd_eq_insert (G : Graph α β) (v : α) :
    G.closedNbhd v = insert v (N(G, v)) := rfl

/-- **A demoted hub's closed neighbourhood is independent at some chart seed** (T2's witness at
the demoted bodies): a hub `v` of `G` that is a body but not a hub of `H ≤ G`, whose neighbours
lost in `H` are all non-hubs of `G`, has its `H`-closed neighbourhood independent at some chart
seed, for every hub selector correct for `G`. With two `H`-neighbours this is (MC-188); with at most
one, the closed neighbourhood is `{v}` or an edge, independent at the given chart point. -/
theorem exists_coord_linearIndepOn_closedNbhd_of_demoted [Finite α]
    {G H : Graph α β} (hS : G.Simple) (hfeas : PencilNondegFeasible K G) (hle : H ≤ G)
    {seed₀ : PencilSeed K α} {hubSel nbrSel : α → Fin 3 → Option α}
    (hWF₀ : PencilChartWF G seed₀ hubSel nbrSel)
    {v : α} (hvH : v ∈ V(H)) (hvG : G.PencilHub v) (hvnot : ¬ H.PencilHub v)
    (hdem : ∀ y, G.Adj v y → ¬ H.Adj v y → ¬ G.PencilHub y) :
    ∃ q : α × Fin 4 × Fin 4 → K,
      LinearIndepOn K (pencilChartPoint (PencilSeed.ofCoord q) hubSel) (H.closedNbhd v) := by
  have hSH : H.Simple := hS.mono hle
  have hpt_eq : pencilChartPoint (PencilSeed.ofCoord seed₀.toCoord) hubSel
      = pencilChartPoint seed₀ hubSel := funext (pencilChartPoint_ofCoord_toCoord seed₀ hubSel)
  have hdeg : H.degree v ≤ 2 := by
    by_contra hcon
    exact hvnot ⟨hvH, by omega⟩
  have hN : N(H, v).ncard ≤ 2 := by rw [← Graph.degree_eq_ncard_adj]; exact hdeg
  have hfin : N(H, v).Finite := Set.toFinite _
  rcases Nat.lt_or_ge (N(H, v).ncard) 2 with hlt | hge
  · -- at most one `H`-neighbour: the given chart point already works
    refine ⟨seed₀.toCoord, ?_⟩
    rw [hpt_eq, Graph.closedNbhd_eq_insert]
    rcases Nat.lt_or_ge (N(H, v).ncard) 1 with h0 | h1
    · have hempty : N(H, v) = ∅ := (Set.ncard_eq_zero hfin).mp (Nat.lt_one_iff.mp h0)
      rw [hempty, insert_empty_eq]
      exact (linearIndepOn_singleton_iff K).mpr (pencilChartPoint_ne_zero seed₀ (hWF₀.2.2.1 v))
    · obtain ⟨y, hy⟩ := Set.ncard_eq_one.mp (show N(H, v).ncard = 1 by omega)
      rw [hy]
      have hadj : H.Adj v y := by
        have : y ∈ N(H, v) := by rw [hy]; rfl
        exact this
      obtain ⟨e, he⟩ := hadj
      exact (LinearIndepOn.pair_iff (pencilChartPoint seed₀ hubSel) he.ne).mpr
        (LinearIndependent.pair_iff.mp (hWF₀.2.2.2.2 e v y (he.of_le hle)))
  · -- two `H`-neighbours: (MC-188)
    obtain ⟨u, w, huw, hNuw⟩ := Set.ncard_eq_two.mp (show N(H, v).ncard = 2 by omega)
    have hu : H.Adj v u := by
      have : u ∈ N(H, v) := by rw [hNuw]; exact Set.mem_insert _ _
      exact this
    have hw : H.Adj v w := by
      have : w ∈ N(H, v) := by rw [hNuw]; exact Set.mem_insert_of_mem _ rfl
      exact this
    obtain ⟨e₁, he₁⟩ := hu
    obtain ⟨e₂, he₂⟩ := hw
    obtain ⟨q, hq⟩ := exists_coord_linearIndependent_pencilChartPoint_of_other_nonhub hS hfeas hvG
      (he₁.of_le hle) (he₂.of_le hle) huw
      (fun y hy hyu hyw => by
        refine hdem y hy ?_
        intro hHy
        have : y ∈ N(H, v) := hHy
        rw [hNuw] at this
        rcases this with rfl | rfl
        · exact hyu rfl
        · exact hyw rfl)
      hubSel hWF₀.1
    refine ⟨q, ?_⟩
    rw [Graph.closedNbhd_eq_insert, hNuw]
    exact linearIndepOn_triple_of_linearIndependent _ he₁.ne he₂.ne huw hq

/-- **The formal hubs by steering, in `G`'s chart** ((MC-190), EARS' T2): at a simple
feasible `G` and a subgraph `H ≤ G` whose demoted hubs lose only non-hub neighbours, `G` has a
nondegenerate realization whose restriction to `H` is nondegenerate. Re-seed `G`'s feasibility
witness, steer one seed carrying the standing chart conditions and the demoted closed
neighbourhoods, re-choose `fillNbr`, and restrict (`IsNondegPencilRealization.mono`). -/
theorem exists_isNondegPencilRealization_restrict_of_demoted [Finite α] [Finite β] [Infinite K]
    {G H : Graph α β} (hS : G.Simple) (hfeas : PencilNondegFeasible K G) (hle : H ≤ G)
    (hdem : ∀ v ∈ V(H), G.PencilHub v → ¬ H.PencilHub v →
      ∀ y, G.Adj v y → ¬ H.Adj v y → ¬ G.PencilHub y) :
    ∃ (F : BodyHingeFramework K 2 α β) (normal point : α → Fin 4 → K),
      IsNondegPencilRealization G F normal point ∧
      IsNondegPencilRealization H ⟨H, F.supportExtensor⟩ normal point := by
  classical
  have := hS
  have hloop := hS.toLoopless
  obtain ⟨F₀, normal₀, point₀, hnd⟩ := id hfeas
  have : G.LocallyFinite := inferInstance
  rcases isEmpty_or_nonempty α with hα | hα
  · exact ⟨F₀, normal₀, point₀, hnd, hnd.mono hle (fun v => isEmptyElim v)⟩
  have : Inhabited α := Classical.inhabited_of_nonempty hα
  obtain ⟨seed₀, hubSel, nbrSel, hWF₀, -, -⟩ := exists_pencilSeed_of_nondeg hnd
  have hpt_eq : pencilChartPoint (PencilSeed.ofCoord seed₀.toCoord) hubSel
      = pencilChartPoint seed₀ hubSel := funext (pencilChartPoint_ofCoord_toCoord seed₀ hubSel)
  obtain ⟨q, hq⟩ := exists_common_seed_linearIndepOn_pencilChartPoint (K := K) hubSel
    (fun i : α ⊕ (α × α) ⊕ α => match i with
      | Sum.inl v => if G.PencilHub v then ({v} : Set α) else G.closedNbhd v
      | Sum.inr (Sum.inl p) => if G.Adj p.1 p.2 then ({p.1, p.2} : Set α) else ∅
      | Sum.inr (Sum.inr v) =>
          if v ∈ V(H) ∧ G.PencilHub v ∧ ¬ H.PencilHub v then H.closedNbhd v else ∅)
    (by
      rintro (v | ⟨u, v⟩ | v)
      · change ∃ q, LinearIndepOn K (pencilChartPoint (PencilSeed.ofCoord q) hubSel)
          (if G.PencilHub v then ({v} : Set α) else G.closedNbhd v)
        refine ⟨seed₀.toCoord, ?_⟩
        rw [hpt_eq]
        by_cases hv : G.PencilHub v
        · rw [ite_eq_left hv]
          exact (linearIndepOn_singleton_iff K).mpr (pencilChartPoint_ne_zero seed₀ (hWF₀.2.2.1 v))
        · rw [ite_eq_right hv]
          exact linearIndepOn_pencilChartPoint_closedNbhd seed₀ (hWF₀.2.1 v hv) (hWF₀.2.2.2.1 v hv)
      · change ∃ q, LinearIndepOn K (pencilChartPoint (PencilSeed.ofCoord q) hubSel)
          (if G.Adj u v then ({u, v} : Set α) else ∅)
        by_cases hadj : G.Adj u v
        · rw [ite_eq_left hadj]
          obtain ⟨e, he⟩ := hadj
          refine ⟨seed₀.toCoord, ?_⟩
          rw [hpt_eq]
          exact (LinearIndepOn.pair_iff (pencilChartPoint seed₀ hubSel) he.ne).mpr
            (LinearIndependent.pair_iff.mp (hWF₀.2.2.2.2 e u v he))
        · rw [ite_eq_right hadj]
          exact ⟨seed₀.toCoord, linearIndepOn_empty K _⟩
      · change ∃ q, LinearIndepOn K (pencilChartPoint (PencilSeed.ofCoord q) hubSel)
          (if v ∈ V(H) ∧ G.PencilHub v ∧ ¬ H.PencilHub v then H.closedNbhd v else ∅)
        by_cases hv : v ∈ V(H) ∧ G.PencilHub v ∧ ¬ H.PencilHub v
        · rw [ite_eq_left hv]
          exact exists_coord_linearIndepOn_closedNbhd_of_demoted hS hfeas hle hWF₀ hv.1 hv.2.1
            hv.2.2 (hdem v hv.1 hv.2.1 hv.2.2)
        · rw [ite_eq_right hv]
          exact ⟨seed₀.toCoord, linearIndepOn_empty K _⟩)
  set seed := PencilSeed.ofCoord q with hseed_def
  have hptnz : ∀ v, pencilChartPoint seed hubSel v ≠ 0 := by
    intro v
    have h : LinearIndepOn K (pencilChartPoint seed hubSel)
        (if G.PencilHub v then ({v} : Set α) else G.closedNbhd v) := hq (Sum.inl v)
    by_cases hv : G.PencilHub v
    · rw [ite_eq_left hv] at h
      exact (linearIndepOn_singleton_iff K).mp h
    · rw [ite_eq_right hv] at h
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
    rw [ite_eq_left hl.adj] at h
    rw [LinearIndependent.pair_iff]
    exact (LinearIndepOn.pair_iff (pencilChartPoint seed hubSel) hl.ne).mp h
  have hnbr_some : ∀ v, ¬ G.PencilHub v → LinearIndepOn K (nbrSlotPoint seed hubSel nbrSel v)
      {i | (nbrSel v i).isSome} := by
    intro v hv
    have h : LinearIndepOn K (pencilChartPoint seed hubSel)
        (if G.PencilHub v then ({v} : Set α) else G.closedNbhd v) := hq (Sum.inl v)
    rw [ite_eq_right hv] at h
    exact linearIndepOn_nbrSlotPoint_isSome_of_pencilChartPoint seed (hWF₀.2.1 v hv) h
  obtain ⟨seed', hhub_eq, hfill_eq, hWF'⟩ :=
    exists_fillNbr_pencilChartWF_of_standing hWF₀.1 hWF₀.2.1 hhub_LI hpt_LI hnbr_some
  have hpcp_eq : pencilChartPoint seed' hubSel = pencilChartPoint seed hubSel :=
    pencilChartPoint_congr hubSel hhub_eq hfill_eq
  have hnd' := isNondegPencilRealization_pencilChartFramework_of_pencilChartWF hWF'
  refine ⟨_, _, _, hnd', hnd'.mono hle ?_⟩
  intro v hv hGhub hHnot
  have h : LinearIndepOn K (pencilChartPoint seed hubSel)
      (if v ∈ V(H) ∧ G.PencilHub v ∧ ¬ H.PencilHub v then H.closedNbhd v else ∅) :=
    hq (Sum.inr (Sum.inr v))
  rw [ite_eq_left ⟨hv, hGhub, hHnot⟩] at h
  rw [hpcp_eq]
  exact h

/-! ## T3: the steering in `H`'s chart ((MC-191)) -/

/-- **A selector of a three-member set fills every slot.** -/
theorem IsFin3SelectorOf.isSome_of_ncard_eq_three {s : Set α} {sel : Fin 3 → Option α}
    (h : IsFin3SelectorOf s sel) (hs : s.ncard = 3) (i : Fin 3) : (sel i).isSome := by
  by_contra hnone
  have hi : sel i = none := Option.not_isSome_iff_eq_none.mp hnone
  choose! slot hslot using h.2.1
  have hmaps : ∀ w ∈ s, slot w ∈ ({j | j ≠ i} : Set (Fin 3)) := by
    intro w hw hji
    have := hslot w hw
    rw [hji, hi] at this
    simp at this
  have hinj : Set.InjOn slot s := by
    intro w₁ hw₁ w₂ hw₂ heq
    have h1 := hslot w₁ hw₁
    have h2 := hslot w₂ hw₂
    rw [heq, h2] at h1
    exact (Option.some.inj h1).symm
  have hle := Set.ncard_le_ncard_of_injOn slot hmaps hinj
  have hcard : ({j | j ≠ i} : Set (Fin 3)).ncard = 2 := by
    rw [← Set.compl_singleton_eq, Set.ncard_compl, Set.ncard_singleton, Nat.card_fin]
  omega

/-- The dot product of a chart point and a chart normal, as a polynomial in the seed. -/
noncomputable def pencilDotPoly (hubSel nbrSel : α → Fin 3 → Option α) (G : Graph α β) (u w : α) :
    MvPolynomial (α × Fin 4 × Fin 4) K :=
  ∑ i, pencilChartPointPoly hubSel u i * pencilChartNormalPoly hubSel nbrSel G w i

theorem pencilDotPoly_eval (hubSel nbrSel : α → Fin 3 → Option α) (G : Graph α β) (u w : α)
    (q : α × Fin 4 × Fin 4 → K) :
    MvPolynomial.eval q (pencilDotPoly hubSel nbrSel G u w)
      = pencilChartPoint (PencilSeed.ofCoord q) hubSel u ⬝ᵥ
          pencilChartNormal (PencilSeed.ofCoord q) hubSel nbrSel G w := by
  simp only [pencilDotPoly, map_sum, map_mul, pencilChartPointPoly_eval,
    pencilChartNormalPoly_eval, dotProduct]

/-- **The steering in `H`'s chart** ((MC-191), EARS' T3; the pattern of
`exists_isNondegPencilRealization_induce_promotedNormal_of_pendant_deg3`). Two nondegenerate
realizations of `H` — one at the deficiency rank, one carrying finitely many normal-independence
and point–normal non-orthogonality conditions — give one realization with all of them. Both are
chart points of one chart of `H` (T1 at the first one's selectors); every condition is the
nonvanishing of a seed polynomial, so a common seed carries them all. The conditions read
normals only at hubs of `H` and at non-hubs with three closed neighbours, where the normal does
not read the re-chosen `fillNbr`. -/
theorem exists_isNondegPencilRealization_steer [Finite α] [Finite β] [Infinite K] {n : ℕ}
    (hn : Graph.bodyBarDim n = screwDim 2) {H : Graph α β} (hloop : H.Loopless)
    (hne : V(H).Nonempty)
    {F₁ : BodyHingeFramework K 2 α β} {normal₁ point₁ : α → Fin 4 → K}
    (hnd₁ : IsNondegPencilRealization H F₁ normal₁ point₁)
    (hrank₁ : (Module.finrank K (Submodule.span K F₁.rigidityRows) : ℤ)
      = screwDim 2 * ((V(H).ncard : ℤ) - 1) - H.deficiency n)
    {F₂ : BodyHingeFramework K 2 α β} {normal₂ point₂ : α → Fin 4 → K}
    (hnd₂ : IsNondegPencilRealization H F₂ normal₂ point₂)
    {ι : Type*} [Finite ι] (S : ι → Set α) (hSV : ∀ k, S k ⊆ V(H))
    (hSfree : ∀ k, ∀ w ∈ S k, ¬ H.PencilHub w → (H.closedNbhd w).ncard = 3)
    (hS : ∀ k, LinearIndepOn K normal₂ (S k))
    {κ : Type*} [Finite κ] (u w : κ → α) (huV : ∀ j, u j ∈ V(H)) (hwV : ∀ j, w j ∈ V(H))
    (hwfree : ∀ j, ¬ H.PencilHub (w j) → (H.closedNbhd (w j)).ncard = 3)
    (hdot : ∀ j, point₂ (u j) ⬝ᵥ normal₂ (w j) ≠ 0) :
    ∃ (F : BodyHingeFramework K 2 α β) (normal point : α → Fin 4 → K),
      IsNondegPencilRealization H F normal point ∧
      (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
        = screwDim 2 * ((V(H).ncard : ℤ) - 1) - H.deficiency n ∧
      (∀ k, LinearIndepOn K normal (S k)) ∧ ∀ j, point (u j) ⬝ᵥ normal (w j) ≠ 0 := by
  classical
  have := hloop
  obtain ⟨v₀, hv₀⟩ := hne
  have : Inhabited α := ⟨v₀⟩
  -- the chart of the attaining realization, and the second realization in it (T1)
  obtain ⟨seed₁, hubSel, nbrSel, hWF₁, hptrepro, -⟩ := exists_pencilSeed_of_nondeg hnd₁
  obtain ⟨seed₂, hseed₂, -, hpt₂, hnm₂⟩ :=
    exists_pencilSeed_of_nondeg_of_selectors hnd₂ hWF₁.1 hWF₁.2.1
  have hpt_eq : pencilChartPoint (PencilSeed.ofCoord seed₁.toCoord) hubSel
      = pencilChartPoint seed₁ hubSel := funext (pencilChartPoint_ofCoord_toCoord seed₁ hubSel)
  -- the normals read by the conditions do not read `fillNbr`
  have hassigned : ∀ x, ¬ H.PencilHub x → (H.closedNbhd x).ncard = 3 →
      ∀ i, (nbrSel x i).isSome := fun x hx h3 i =>
    (hWF₁.2.1 x hx).isSome_of_ncard_eq_three h3 i
  -- the second realization's normals in the chart, at the flattening
  have hnm₂' : ∀ x ∈ V(H), (¬ H.PencilHub x → (H.closedNbhd x).ncard = 3) →
      ∃ d : K, d ≠ 0 ∧
        pencilChartNormal (PencilSeed.ofCoord seed₂.toCoord) hubSel nbrSel H x = d • normal₂ x := by
    intro x hx hfree
    have hcongr := pencilChartNormal_congr (seed := seed₂)
      (seed' := PencilSeed.ofCoord seed₂.toCoord) hubSel nbrSel H (v := x)
      (PencilSeed.ofCoord_toCoord_hubNormal seed₂) (PencilSeed.ofCoord_toCoord_fillHub seed₂)
      (fun hx' => hassigned x hx' (hfree hx'))
    rw [hcongr]
    by_cases hxh : H.PencilHub x
    · exact ⟨1, one_ne_zero, by rw [pencilChartNormal_of_pencilHub _ _ _ hxh, hseed₂, one_smul]⟩
    · exact hnm₂ x hx hxh
  have hpt₂' : ∀ x ∈ V(H), ∃ c : K, c ≠ 0 ∧
      pencilChartPoint (PencilSeed.ofCoord seed₂.toCoord) hubSel x = c • point₂ x := by
    intro x hx
    rw [pencilChartPoint_ofCoord_toCoord]
    exact hpt₂ x hx
  -- the standing point conditions, at the first flattening
  have hpolyA : ∀ v : α, ∃ Q : MvPolynomial (α × Fin 4 × Fin 4) K,
      (∃ q, MvPolynomial.eval q Q ≠ 0) ∧
      (∀ q, MvPolynomial.eval q Q ≠ 0 →
        LinearIndepOn K (pencilChartPoint (PencilSeed.ofCoord q) hubSel)
          (if H.PencilHub v then ({v} : Set α) else H.closedNbhd v)) := by
    intro v
    have hwit : LinearIndepOn K (pencilChartPoint (PencilSeed.ofCoord seed₁.toCoord) hubSel)
        (if H.PencilHub v then ({v} : Set α) else H.closedNbhd v) := by
      rw [hpt_eq]
      by_cases hv : H.PencilHub v
      · rw [ite_eq_left hv]
        exact (linearIndepOn_singleton_iff K).mpr (pencilChartPoint_ne_zero seed₁ (hWF₁.2.2.1 v))
      · rw [ite_eq_right hv]
        exact linearIndepOn_pencilChartPoint_closedNbhd seed₁ (hWF₁.2.1 v hv) (hWF₁.2.2.2.1 v hv)
    obtain ⟨Q, hQ0, hQ⟩ :=
      exists_polynomial_ne_zero_of_linearIndependent_pencilChartPoint hubSel id hwit
    exact ⟨Q, ⟨seed₁.toCoord, hQ0⟩, fun q hq => hQ q hq⟩
  choose PA hPA0 hPA using hpolyA
  have hpolyB : ∀ p : α × α, ∃ Q : MvPolynomial (α × Fin 4 × Fin 4) K,
      (∃ q, MvPolynomial.eval q Q ≠ 0) ∧
      (∀ q, MvPolynomial.eval q Q ≠ 0 →
        LinearIndepOn K (pencilChartPoint (PencilSeed.ofCoord q) hubSel)
          (if H.Adj p.1 p.2 then ({p.1, p.2} : Set α) else ∅)) := by
    rintro ⟨u, v⟩
    have hwit : LinearIndepOn K (pencilChartPoint (PencilSeed.ofCoord seed₁.toCoord) hubSel)
        (if H.Adj u v then ({u, v} : Set α) else ∅) := by
      by_cases hadj : H.Adj u v
      · rw [ite_eq_left hadj]
        obtain ⟨e, he⟩ := hadj
        rw [hpt_eq]
        exact (LinearIndepOn.pair_iff (pencilChartPoint seed₁ hubSel) he.ne).mpr
          (LinearIndependent.pair_iff.mp (hWF₁.2.2.2.2 e u v he))
      · rw [ite_eq_right hadj]; exact linearIndepOn_empty K _
    obtain ⟨Q, hQ0, hQ⟩ :=
      exists_polynomial_ne_zero_of_linearIndependent_pencilChartPoint hubSel id hwit
    exact ⟨Q, ⟨seed₁.toCoord, hQ0⟩, fun q hq => hQ q hq⟩
  choose PB hPB0 hPB using hpolyB
  -- the normal-independence conditions, at the second flattening
  have hpolyC : ∀ k : ι, ∃ Q : MvPolynomial (α × Fin 4 × Fin 4) K,
      (∃ q, MvPolynomial.eval q Q ≠ 0) ∧
      (∀ q, MvPolynomial.eval q Q ≠ 0 →
        LinearIndepOn K (pencilChartNormal (PencilSeed.ofCoord q) hubSel nbrSel H) (S k)) := by
    intro k
    have hwit : LinearIndepOn K
        (pencilChartNormal (PencilSeed.ofCoord seed₂.toCoord) hubSel nbrSel H) (S k) :=
      LinearIndepOn.of_smul_eq (hS k) (fun x hx => hnm₂' x (hSV k hx) (hSfree k x hx))
    obtain ⟨Q, hQ0, hQ⟩ :=
      exists_polynomial_ne_zero_of_linearIndependent_pencilChartNormal hubSel nbrSel H id hwit
    exact ⟨Q, ⟨seed₂.toCoord, hQ0⟩, fun q hq => hQ q hq⟩
  choose PC hPC0 hPC using hpolyC
  -- the non-orthogonality conditions, at the second flattening
  have hPD0 : ∀ j, ∃ q,
      MvPolynomial.eval q (pencilDotPoly (K := K) hubSel nbrSel H (u j) (w j)) ≠ 0 := by
    intro j
    refine ⟨seed₂.toCoord, ?_⟩
    rw [pencilDotPoly_eval]
    obtain ⟨c, hc, hceq⟩ := hpt₂' (u j) (huV j)
    obtain ⟨d, hd, hdeq⟩ := hnm₂' (w j) (hwV j) (hwfree j)
    rw [hceq, hdeq, smul_dotProduct, dotProduct_smul, smul_smul, smul_eq_mul]
    exact mul_ne_zero (mul_ne_zero hc hd) (hdot j)
  -- the rank rows, at the first flattening
  obtain ⟨s, hslink, hscard, hsLI⟩ := exists_independent_pencilRow_subfamily_at_toCoord_of_reseed
    hnd₁ hptrepro (le_refl (Module.finrank K (Submodule.span K F₁.rigidityRows)))
  -- one common seed
  have hPsome : ∀ i : (α ⊕ (α × α)) ⊕ (ι ⊕ κ),
      ∃ q, MvPolynomial.eval q ((Sum.elim (Sum.elim PA PB)
        (Sum.elim PC (fun j => pencilDotPoly (K := K) hubSel nbrSel H (u j) (w j)))) i) ≠ 0 := by
    rintro ((v | p) | (k | j))
    · exact hPA0 v
    · exact hPB0 p
    · exact hPC0 k
    · exact hPD0 j
  obtain ⟨q, hqrows, hqP⟩ := exists_common_seed_pencilRow_and_polynomials hubSel H.endsOf hsLI _
    hPsome
  have hcondA : ∀ v, LinearIndepOn K (pencilChartPoint (PencilSeed.ofCoord q) hubSel)
      (if H.PencilHub v then ({v} : Set α) else H.closedNbhd v) :=
    fun v => hPA v q (hqP (Sum.inl (Sum.inl v)))
  have hcondB : ∀ u v, LinearIndepOn K (pencilChartPoint (PencilSeed.ofCoord q) hubSel)
      (if H.Adj u v then ({u, v} : Set α) else ∅) :=
    fun u v => hPB (u, v) q (hqP (Sum.inl (Sum.inr (u, v))))
  have hcondC : ∀ k, LinearIndepOn K (pencilChartNormal (PencilSeed.ofCoord q) hubSel nbrSel H)
      (S k) := fun k => hPC k q (hqP (Sum.inr (Sum.inl k)))
  have hcondD : ∀ j, pencilChartPoint (PencilSeed.ofCoord q) hubSel (u j) ⬝ᵥ
      pencilChartNormal (PencilSeed.ofCoord q) hubSel nbrSel H (w j) ≠ 0 := by
    intro j
    have h := hqP (Sum.inr (Sum.inr j))
    simp only [Sum.elim_inr] at h
    rwa [pencilDotPoly_eval] at h
  -- the standing chart conditions at the common seed
  have hptnz : ∀ v, pencilChartPoint (PencilSeed.ofCoord q) hubSel v ≠ 0 := by
    intro v
    by_cases hv : H.PencilHub v
    · have h := hcondA v; rw [ite_eq_left hv] at h
      exact (linearIndepOn_singleton_iff K).mp h
    · have h := hcondA v; rw [ite_eq_right hv] at h
      exact (linearIndepOn_singleton_iff K).mp (h.mono (Set.singleton_subset_iff.mpr (Or.inl rfl)))
  have hhub_LI : ∀ v, LinearIndependent K
      ![hubSlotNormal (PencilSeed.ofCoord q) hubSel v 0,
        hubSlotNormal (PencilSeed.ofCoord q) hubSel v 1,
        hubSlotNormal (PencilSeed.ofCoord q) hubSel v 2] := by
    intro v
    have h := hptnz v
    rw [pencilChartPoint] at h
    exact (cross₃_ne_zero_iff_linearIndependent _ _ _).mp h
  have hpt_LI : ∀ e u v, H.IsLink e u v → LinearIndependent K
      ![pencilChartPoint (PencilSeed.ofCoord q) hubSel u,
        pencilChartPoint (PencilSeed.ofCoord q) hubSel v] := by
    intro e u v hl
    have h := hcondB u v; rw [ite_eq_left hl.adj] at h
    rw [LinearIndependent.pair_iff]
    exact (LinearIndepOn.pair_iff (pencilChartPoint (PencilSeed.ofCoord q) hubSel) hl.ne).mp h
  have hnbr_some : ∀ v, ¬ H.PencilHub v →
      LinearIndepOn K (nbrSlotPoint (PencilSeed.ofCoord q) hubSel nbrSel v)
        {i | (nbrSel v i).isSome} := by
    intro v hv
    have h := hcondA v; rw [ite_eq_right hv] at h
    exact linearIndepOn_nbrSlotPoint_isSome_of_pencilChartPoint (PencilSeed.ofCoord q)
      (hWF₁.2.1 v hv) h
  -- re-choose `fillNbr`, and read off the chart realization and its rank
  obtain ⟨seed', hhub_eq, hfill_eq, hWF'⟩ :=
    exists_fillNbr_pencilChartWF_of_standing hWF₁.1 hWF₁.2.1 hhub_LI hpt_LI hnbr_some
  have hnd' := isNondegPencilRealization_pencilChartFramework_of_pencilChartWF hWF'
  have hpcp_eq : pencilChartPoint seed' hubSel = pencilChartPoint (PencilSeed.ofCoord q) hubSel :=
    pencilChartPoint_congr hubSel hhub_eq hfill_eq
  have hgcongr : pencilChartFramework (PencilSeed.ofCoord q) hubSel H
      = pencilChartFramework seed' hubSel H :=
    pencilChartFramework_congr hubSel H hpcp_eq.symm
  have hC : ∀ e u v, H.IsLink e u v →
      (pencilChartFramework (PencilSeed.ofCoord q) hubSel H).supportExtensor e ≠ 0 := by
    intro e u v _
    rw [hgcongr]; exact hnd'.1.1.2.2.1 e
  have hscardZ : (Nat.card s : ℤ) = screwDim 2 * ((V(H).ncard : ℤ) - 1) - H.deficiency n := by
    rw [hscard]; exact hrank₁
  have hrankq := finrank_span_rigidityRows_pencilChartFramework_eq_of_independent_pencilRow
    hn (G := H) ⟨v₀, hv₀⟩ hubSel hC hslink hqrows hscardZ
  refine ⟨pencilChartFramework seed' hubSel H, pencilChartNormal seed' hubSel nbrSel H,
    pencilChartPoint seed' hubSel, hnd', by rw [← hgcongr, hrankq], fun k => ?_, fun j => ?_⟩
  · exact linearIndepOn_pencilChartNormal_congr hubSel nbrSel H hhub_eq hfill_eq
      (fun x hx hxh => hassigned x hxh (hSfree k x hx hxh)) (hcondC k)
  · rw [hpcp_eq, pencilChartNormal_congr hubSel nbrSel H hhub_eq hfill_eq
      (fun hxh => hassigned (w j) hxh (hwfree j hxh))]
    exact hcondD j

/-- **A demoted body that loses few neighbours keeps exactly two** (the `fillNbr`-free condition
T3 reads): at a simple `G`, a body `v` of `H ≤ G` that is not a hub of `H`, whose
`G`-neighbours outside `H` lie in a set `L` with `|L| + 2 ≤ deg_G v`, has three closed
neighbours in `H`. -/
theorem ncard_closedNbhd_eq_three_of_demoted [Finite α] {G H : Graph α β} (hS : G.Simple)
    (hle : H ≤ G) {v : α} (hvnot : ¬ H.PencilHub v) (hvH : v ∈ V(H))
    {L : Set α} (hL : N(G, v) ⊆ L ∪ N(H, v)) (hdeg : L.ncard + 2 ≤ G.degree v) :
    (H.closedNbhd v).ncard = 3 := by
  have := hS
  have hSH : H.Simple := hS.mono hle
  have hHdeg : H.degree v ≤ 2 := by
    by_contra hcon; exact hvnot ⟨hvH, by omega⟩
  have hG := Graph.degree_eq_ncard_adj (G := G) (x := v)
  have hH := Graph.degree_eq_ncard_adj (G := H) (x := v)
  have h1 : N(G, v).ncard ≤ L.ncard + N(H, v).ncard :=
    (Set.ncard_le_ncard hL (Set.toFinite _)).trans (Set.ncard_union_le _ _)
  have hnot : v ∉ N(H, v) := fun h => by
    obtain ⟨e, he⟩ := h
    exact hSH.toLoopless.not_isLoopAt e v he
  rw [Graph.closedNbhd_eq_insert, Set.ncard_insert_of_notMem hnot (Set.toFinite _)]
  omega

end CombinatorialRigidity.Molecular
