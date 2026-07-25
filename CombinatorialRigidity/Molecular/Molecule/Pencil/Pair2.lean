/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.Pair

/-!
# The conditioned-pair cut arm, sub-case 3: the pendant producer (Phase 39 PENCIL, W5-L5)

Continues `Molecule/Pencil/Pair.lean` (the `≤ 1500`-LoC soft cap, `notes/PERFORMANCE.md`): the
cut-arm route verdict's sub-case 3 (`notes/Phase39-design.md` §"W5 leaf decomposition" L5
"Cut-arm route verdict", item 3), `|V₂| = 1` (the far side is a single pendant vertex) with
`G.degree u_c ≠ 3`. Here `Gᵢ⁺ = G.induce (V₁ ∪ {v_c}) = G` (the closure adds nothing new), so the
`Gᵢ⁺` edge-closure trick (L5-cut-i) is inapplicable — the induction hypothesis fires directly at
the *bare* induced side `H := G.induce V₁`, one vertex smaller than `G`. Unlike sub-case 1
(`Pair.lean`), there is no hub-status change anywhere: `Graph.pencilHub_iff_induce_of_degree_ne`
(`Motive.lean`) shows `u_c`'s pencil-hub status agrees between `H` and `G` whenever
`G.degree u_c ≠ 3`, so feasibility restricts by blanket `.mono` and every closed-hub-neighbourhood
is literally unchanged (`v_c` is never a hub, `G.degree v_c = 1`). The one new construction is
choosing fresh pendant data (`normal v_c`, `point v_c`) off the bad span at `u_c` — a dimension
count in the spirit of `exists_perp_linearIndependent`, but avoiding a `≤ 2`-generator span rather
than a single vector. The rank closes via the landed `finrank_span_rigidityRows_cutEdge_eq`
verbatim: the pendant side is edgeless, so `hlb₂ = 0 ≤ 0` with no new rank work.

See `notes/Phase39.md`, `notes/Phase39-design.md` (§"W5 leaf decomposition"), and
`blueprint/src/chapter/pencil.tex`.
-/

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K]
variable {α β : Type*}

/-! ## W5-L5 cut arm, sub-case 3 (pendant, `deg_G u_c ≠ 3`): the producer (Phase 39 PENCIL)

The cut-arm route verdict's third sub-case (`notes/Phase39-design.md` §"W5 leaf decomposition" L5
"Cut-arm route verdict", item 3): `G = H + pendant v_c at u_c` (`H := G.induce V₁`), with
`G.degree u_c ≠ 3` the sharp value at which a single dropped edge can flip pencil-hub status. Both
the input (feasibility restriction) and the output (the glued fourth conjunct at `u_c`) close
without any hub-status case split: `Graph.pencilHub_iff_induce_of_degree_ne` (`Motive.lean`) makes
`u_c`'s hub status agree between `H` and `G` unconditionally, so `G.closedHubNbhd`/`H.closedHubNbhd`
agree everywhere on `V₁` (`v_c` never a hub, `G.degree v_c = 1`), and the only body whose closed
neighbourhood changes is `u_c` itself, gaining `point v_c`. The fresh pendant data is chosen to
avoid the bad span *unconditionally* (whether or not `u_c` is a hub — the span is a single point
`{point₁ u_c}` when `u_c` is a hub, since conjunct 4 does not apply there and only the second
conjunct's pair-LI is at stake, or the `≤ 2`-member `H.closedNbhd u_c` when it is not), so no
hub-status case split is needed in the construction either. -/

/-- **The pendant sub-case's producer** (Phase 39 W5-L5, L5-cut-iv sub-case 3;
`notes/Phase39-design.md` §"W5 leaf decomposition" L5 "Cut-arm route verdict" item 3). Given a
loopless `G` with a single crossing edge `e_c = u_c v_c` over `V₁ ⊆ V(G)` whose complement is the
singleton `{v_c}`, `G.degree u_c ≠ 3`, and a nondegenerate realization of the bare induced side
`H := G.induce V₁` attaining its deficiency-rank target, `G` has a generic pencil realization: pick
fresh pendant data `normal v_c`/`point v_c` off the bad span at `u_c` (`point_vc` inside
`normal₁ u_c`'s `3`-dimensional perp, avoiding a `≤ 2`-generator cover of `H.closedNbhd u_c`'s point
images; `normal_vc` inside the joint `2`-dimensional perp of `point₁ u_c` and `point_vc`), take the
pendant edge's hinge from `exists_extensor_two_pencils`, and glue; every nondegeneracy conjunct on
`V₁` transfers verbatim (no hub-status change, `Graph.pencilHub_iff_induce_of_degree_ne`), and the
rank closes by `finrank_span_rigidityRows_cutEdge_eq` with the pendant side's `hlb₂ = 0` (edgeless,
`Graph.deficiency_of_edgeSet_empty`). -/
theorem hasGenericPencilRealization_of_isNondegPencilRealization_induce_pendant
    [Finite α] [Finite β] {n : ℕ}
    (hD : 2 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim 2)
    {G : Graph α β} [G.Loopless] {V₁ : Set α} {e_c : β} {u_c v_c : α}
    (hl_c : G.IsLink e_c u_c v_c) (hu_c : u_c ∈ V₁) (hv_c : v_c ∉ V₁)
    (hVG : V(G) = V₁ ∪ {v_c}) (hcut : (G.cutEdges V₁).ncard ≤ 1)
    (hdeg3 : G.degree u_c ≠ 3)
    {F₁ : BodyHingeFramework K 2 α β} {normal₁ point₁ : α → Fin 4 → K}
    (hnd₁ : IsNondegPencilRealization (G.induce V₁) F₁ normal₁ point₁)
    (hrank₁ : (Module.finrank K (Submodule.span K F₁.rigidityRows) : ℤ)
      = screwDim 2 * ((V₁.ncard : ℤ) - 1) - (G.induce V₁).deficiency n) :
    HasGenericPencilRealization K n G := by
  classical
  -- ── Basic structural facts: `Gᵢ⁺ = G`, `v_c` is a pendant, `u_c`'s hub status agrees. ──────
  have hGeq : G.induce (V₁ ∪ {v_c}) = G := by rw [← hVG]; exact Graph.induce_vertexSet G
  have hvc_deg : G.degree v_c = 1 := by
    have h := Graph.degree_induce_union_singleton_far hl_c hu_c hv_c hcut
    rwa [hGeq] at h
  have hvc_not_hub : ¬ G.PencilHub v_c := by
    intro h; have h2 := h.2; omega
  have hcross_eq : ∀ e' x y, G.IsLink e' x y → x ∈ V₁ → y ∉ V₁ →
      e' = e_c ∧ x = u_c ∧ y = v_c := by
    intro e' x y hle hx hy
    have he' := Graph.eq_cutEdge_of_isLink_crossing hl_c hu_c hv_c hcut hle hx hy
    subst he'
    rcases hle.eq_and_eq_or_eq_and_eq hl_c with ⟨hxeq, hyeq⟩ | ⟨hxeq, hyeq⟩
    · exact ⟨rfl, hxeq, hyeq⟩
    · rw [hxeq] at hx; exact absurd hx hv_c
  have hu_c_hub_iff : G.PencilHub u_c ↔ (G.induce V₁).PencilHub u_c :=
    Graph.pencilHub_iff_induce_of_degree_ne hl_c hu_c hv_c hcut hdeg3
  have hdeg_eq : ∀ w ∈ V₁, w ≠ u_c → (G.induce V₁).degree w = G.degree w :=
    fun w hw hwne => Graph.degree_induce_eq_of_ne hl_c hu_c hv_c hcut hw hwne
  -- ── `V(G) \ V₁ = {v_c}`, edgeless. ─────────────────────────────────────────────────────────
  have hV₁sub : V₁ ⊆ V(G) := by rw [hVG]; exact Set.subset_union_left
  have hV₂eq : V(G) \ V₁ = {v_c} := by
    ext x
    constructor
    · rintro ⟨hxG, hxV₁⟩
      rw [hVG] at hxG
      exact hxG.resolve_left hxV₁
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨by rw [hVG]; exact Set.mem_union_right _ rfl, hv_c⟩
  have hV₂edgeless : E(G.induce (V(G) \ V₁)) = ∅ := by
    ext e
    simp only [Graph.edgeSet_induce, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨a, b, hl, ha, hb⟩
    rw [hV₂eq, Set.mem_singleton_iff] at ha hb
    rw [ha, hb] at hl
    exact G.not_isLoopAt e v_c hl
  -- ── `H`'s own witness data. ────────────────────────────────────────────────────────────────
  obtain ⟨hreal₁, hadj₁, hhubLI₁, hnbhdLI₁⟩ := hnd₁
  obtain ⟨⟨hF₁g, hn₁nz, hS₁nz, hpanel₁⟩, hp₁nz, hp₁inc, hthrough₁⟩ := hreal₁
  have hn1_ne : normal₁ u_c ≠ 0 := hn₁nz u_c hu_c
  have hp1_ne : point₁ u_c ≠ 0 := hp₁nz u_c hu_c
  -- ── The `≤ 2`-generator cover of `H.closedNbhd u_c`'s point image (always containing
  -- `point₁ u_c`; the full `H.closedNbhd u_c` image only when `u_c` is not a `G`-hub). ────────
  set ker₁ : (Fin 4 → K) → Submodule K (Fin 4 → K) :=
    fun t => LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip t) with hker₁
  have hker_mem : ∀ t z : Fin 4 → K, z ∈ ker₁ t ↔ z ⬝ᵥ t = 0 := by
    intro t z
    simp only [hker₁, LinearMap.mem_ker, LinearMap.flip_apply, piBasisFun_toDual_eq_dotProduct]
  obtain ⟨a₀, b₀, hmem₀, hcov₀⟩ : ∃ a₀ b₀ : Fin 4 → K,
      point₁ u_c ∈ ({a₀, b₀} : Set (Fin 4 → K)) ∧
      (¬ G.PencilHub u_c → point₁ '' ((G.induce V₁).closedNbhd u_c) ⊆ {a₀, b₀}) := by
    by_cases huc_hub : G.PencilHub u_c
    · exact ⟨point₁ u_c, 0, Or.inl rfl, fun hcon => absurd huc_hub hcon⟩
    · have hdegG2 : G.degree u_c ≤ 2 := by
        by_contra hcon
        push Not at hcon
        exact huc_hub ⟨hl_c.left_mem, hcon⟩
      have hsucc := Graph.degree_eq_degree_induce_succ hl_c hu_c hv_c hcut
      have hdegH1 : (G.induce V₁).degree u_c ≤ 1 := by omega
      by_cases hinc : ∃ e w, (G.induce V₁).IsLink e u_c w
      · obtain ⟨e, w, hl⟩ := hinc
        have hpend : (G.induce V₁).IsPendant e u_c :=
          hl.inc_left.isPendant_of_degree_le_one hdegH1
        have hsub : (G.induce V₁).closedNbhd u_c ⊆ {u_c, w} := by
          rintro y (rfl | ⟨e', hl'⟩)
          · exact Set.mem_insert _ _
          · obtain rfl := hpend.edge_unique hl'.inc_left
            obtain rfl := hl.right_unique hl'
            exact Set.mem_insert_of_mem _ rfl
        refine ⟨point₁ u_c, point₁ w, Or.inl rfl, fun _ => ?_⟩
        rintro _ ⟨x, hx, rfl⟩
        rcases hsub hx with rfl | hxw
        · exact Set.mem_insert _ _
        · rw [Set.mem_singleton_iff.mp hxw]
          exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
      · have hsub : (G.induce V₁).closedNbhd u_c ⊆ {u_c} := by
          rintro y (rfl | ⟨e', hl'⟩)
          · rfl
          · exact absurd ⟨e', y, hl'⟩ hinc
        refine ⟨point₁ u_c, point₁ u_c, Or.inl rfl, fun _ => ?_⟩
        rintro _ ⟨x, hx, rfl⟩
        rw [Set.mem_singleton_iff.mp (hsub hx)]
        exact Set.mem_insert _ _
  -- ── Choose `point_vc` off the cover, inside `normal₁ u_c`'s perp. ─────────────────────────
  have hVdim : Module.finrank K (ker₁ (normal₁ u_c)) = 3 := finrank_toDualPerp_single_eq hn1_ne
  have hspan_le : Module.finrank K (Submodule.span K ({a₀, b₀} : Set (Fin 4 → K))) ≤ 2 :=
    finrank_span_pair_le a₀ b₀
  have hnotle : ¬ (ker₁ (normal₁ u_c) ≤ Submodule.span K ({a₀, b₀} : Set (Fin 4 → K))) := by
    intro hle
    have hm := Submodule.finrank_mono hle
    omega
  obtain ⟨point_vc, hpvc_mem, hpvc_notmem⟩ := SetLike.not_le_iff_exists.mp hnotle
  have hpvc_perp : point_vc ⬝ᵥ normal₁ u_c = 0 := (hker_mem (normal₁ u_c) point_vc).mp hpvc_mem
  have hpvc_ne : point_vc ≠ 0 := by
    intro h; apply hpvc_notmem; rw [h]; exact Submodule.zero_mem _
  -- ── Choose `normal_vc` orthogonal to both `point₁ u_c` and `point_vc`. ────────────────────
  have h2dim : 2 ≤ Module.finrank K
      ((ker₁ (point₁ u_c) ⊓ ker₁ point_vc : Submodule K (Fin 4 → K))) :=
    le_finrank_toDualPerp_inf (point₁ u_c) point_vc
  have hnvc_notle : ¬ (ker₁ (point₁ u_c) ⊓ ker₁ point_vc) ≤ (⊥ : Submodule K (Fin 4 → K)) := by
    intro hle
    have hm := Submodule.finrank_mono hle
    simp only [finrank_bot] at hm
    omega
  obtain ⟨normal_vc, hnvc_mem, hnvc_notbot⟩ := SetLike.not_le_iff_exists.mp hnvc_notle
  have hnvc_p1 : normal_vc ⬝ᵥ point₁ u_c = 0 := (hker_mem (point₁ u_c) normal_vc).mp hnvc_mem.1
  have hnvc_pvc : normal_vc ⬝ᵥ point_vc = 0 := (hker_mem point_vc normal_vc).mp hnvc_mem.2
  have hnvc_ne : normal_vc ≠ 0 := by
    intro h; apply hnvc_notbot; rw [h]; exact Submodule.zero_mem _
  -- ── The pendant edge's hinge. ─────────────────────────────────────────────────────────────
  obtain ⟨C_cut, hCne, hCpn_u, hCpn_v, hCth_u, hCth_v⟩ :=
    exists_extensor_two_pencils (n_u := normal₁ u_c) (n_v := normal_vc)
      (pt_u := point₁ u_c) (pt_v := point_vc)
      hp1_ne (hp₁inc u_c hu_c) (by rw [dotProduct_comm]; exact hnvc_pvc)
      (by rw [dotProduct_comm]; exact hnvc_p1) hpvc_perp
  -- ── The glued data. ────────────────────────────────────────────────────────────────────────
  set normal : α → Fin 4 → K := fun v => if v ∈ V₁ then normal₁ v else normal_vc
  set point : α → Fin 4 → K := fun v => if v ∈ V₁ then point₁ v else point_vc
  set extF : β → ScrewSpace K 2 := fun e =>
    if ∃ a b, (G.induce V₁).IsLink e a b then F₁.supportExtensor e else C_cut
  set F : BodyHingeFramework K 2 α β := ⟨G, extF⟩
  have hlinks : ∀ e u v, G.IsLink e u v →
      ExtensorInPanel (extF e) (normal u) ∧ ExtensorInPanel (extF e) (normal v) ∧
      ExtensorThroughPoint (extF e) (point u) ∧ ExtensorThroughPoint (extF e) (point v) := by
    intro e u v hl
    simp only [extF]
    by_cases hE₁ : ∃ a b, (G.induce V₁).IsLink e a b
    · simp only [hE₁, ↓reduceIte]
      obtain ⟨a, b, hlab⟩ := hE₁
      have hu₁ : u ∈ V₁ := mem_of_induce_isLink_left hl hlab
      have hv₁ : v ∈ V₁ := mem_of_induce_isLink_right hl hlab
      simp only [normal, point, hu₁, hv₁, ↓reduceIte]
      have hl' : (G.induce V₁).IsLink e u v := (Graph.induce_isLink G V₁ e u v).mpr ⟨hl, hu₁, hv₁⟩
      exact ⟨(hpanel₁ e u v hl').1, (hpanel₁ e u v hl').2,
             (hthrough₁ e u v hl').1, (hthrough₁ e u v hl').2⟩
    · simp only [hE₁, ↓reduceIte]
      have hu_or : u ∈ V₁ ∨ u = v_c := by
        have h : u ∈ V₁ ∪ ({v_c} : Set α) := by rw [← hVG]; exact hl.left_mem
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (Set.mem_singleton_iff.mp h)
      have hv_or : v ∈ V₁ ∨ v = v_c := by
        have h : v ∈ V₁ ∪ ({v_c} : Set α) := by rw [← hVG]; exact hl.right_mem
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (Set.mem_singleton_iff.mp h)
      have hopp : (u ∈ V₁ ∧ v = v_c) ∨ (u = v_c ∧ v ∈ V₁) := by
        rcases hu_or with hu₁ | huvc
        · rcases hv_or with hv₁ | hvvc
          · exact absurd ⟨u, v, (Graph.induce_isLink G V₁ e u v).mpr ⟨hl, hu₁, hv₁⟩⟩ hE₁
          · exact Or.inl ⟨hu₁, hvvc⟩
        · rcases hv_or with hv₁ | hvvc
          · exact Or.inr ⟨huvc, hv₁⟩
          · exfalso; rw [huvc, hvvc] at hl; exact G.not_isLoopAt e v_c hl
      rcases hopp with ⟨hu₁, hveq⟩ | ⟨hueq, hv₁⟩
      · have hl' : G.IsLink e u v_c := by rw [hveq] at hl; exact hl
        obtain ⟨-, hueq2, -⟩ := hcross_eq e u v_c hl' hu₁ hv_c
        have hnu : normal u = normal₁ u_c := by rw [hueq2]; simp only [normal, hu_c, ↓reduceIte]
        have hnv : normal v = normal_vc := by rw [hveq]; simp only [normal, hv_c, ↓reduceIte]
        have hpu : point u = point₁ u_c := by rw [hueq2]; simp only [point, hu_c, ↓reduceIte]
        have hpv : point v = point_vc := by rw [hveq]; simp only [point, hv_c, ↓reduceIte]
        rw [hnu, hnv, hpu, hpv]
        exact ⟨hCpn_u, hCpn_v, hCth_u, hCth_v⟩
      · have hu_notin : u ∉ V₁ := by rw [hueq]; exact hv_c
        obtain ⟨-, hveq2, -⟩ := hcross_eq e v u hl.symm hv₁ hu_notin
        have hnu : normal u = normal_vc := by rw [hueq]; simp only [normal, hv_c, ↓reduceIte]
        have hnv : normal v = normal₁ u_c := by rw [hveq2]; simp only [normal, hu_c, ↓reduceIte]
        have hpu : point u = point_vc := by rw [hueq]; simp only [point, hv_c, ↓reduceIte]
        have hpv : point v = point₁ u_c := by rw [hveq2]; simp only [point, hu_c, ↓reduceIte]
        rw [hnu, hnv, hpu, hpv]
        exact ⟨hCpn_v, hCpn_u, hCth_v, hCth_u⟩
  have hnorm_nz : ∀ v ∈ V(G), normal v ≠ 0 := by
    intro v _
    by_cases hv₁ : v ∈ V₁
    · simp only [normal, hv₁, ↓reduceIte]; exact hn₁nz v hv₁
    · simp only [normal, hv₁, ↓reduceIte]; exact hnvc_ne
  have hextF_nz : ∀ e, extF e ≠ 0 := by
    intro e
    simp only [extF]
    by_cases hE₁ : ∃ a b, (G.induce V₁).IsLink e a b
    · simp only [hE₁, ↓reduceIte]; exact hS₁nz e
    · simp only [hE₁, ↓reduceIte]; exact hCne
  have hpoint_nz : ∀ v ∈ V(G), point v ≠ 0 := by
    intro v _
    by_cases hv₁ : v ∈ V₁
    · simp only [point, hv₁, ↓reduceIte]; exact hp₁nz v hv₁
    · simp only [point, hv₁, ↓reduceIte]; exact hpvc_ne
  have hpoint_inc : ∀ v ∈ V(G), point v ⬝ᵥ normal v = 0 := by
    intro v _
    by_cases hv₁ : v ∈ V₁
    · simp only [point, normal, hv₁, ↓reduceIte]; exact hp₁inc v hv₁
    · simp only [point, normal, hv₁, ↓reduceIte]; rw [dotProduct_comm]; exact hnvc_pvc
  -- ── Conjunct 2: adjacent-point pair-LI. ──────────────────────────────────────────────────
  have hadjLI : ∀ e u v, G.IsLink e u v → LinearIndependent K ![point u, point v] := by
    intro e u v hl
    by_cases hu₁ : u ∈ V₁
    · by_cases hv₁ : v ∈ V₁
      · have hl' : (G.induce V₁).IsLink e u v :=
          (Graph.induce_isLink G V₁ e u v).mpr ⟨hl, hu₁, hv₁⟩
        have hpu : point u = point₁ u := by simp only [point, hu₁, ↓reduceIte]
        have hpv : point v = point₁ v := by simp only [point, hv₁, ↓reduceIte]
        rw [hpu, hpv]
        exact hadj₁ e u v hl'
      · have hveq : v = v_c :=
          Set.mem_singleton_iff.mp
            ((show v ∈ V₁ ∪ ({v_c} : Set α) by rw [← hVG]; exact hl.right_mem).resolve_left hv₁)
        have hl' : G.IsLink e u v_c := by rw [hveq] at hl; exact hl
        obtain ⟨-, hueq2, -⟩ := hcross_eq e u v_c hl' hu₁ hv_c
        have hpu : point u = point₁ u_c := by rw [hueq2]; simp only [point, hu_c, ↓reduceIte]
        have hpv : point v = point_vc := by rw [hveq]; simp only [point, hv_c, ↓reduceIte]
        rw [hpu, hpv, LinearIndependent.pair_iff' hp1_ne]
        intro a ha
        exact hpvc_notmem (ha ▸ Submodule.smul_mem _ a (Submodule.subset_span hmem₀))
    · have hueq : u = v_c :=
        Set.mem_singleton_iff.mp
          ((show u ∈ V₁ ∪ ({v_c} : Set α) by rw [← hVG]; exact hl.left_mem).resolve_left hu₁)
      by_cases hv₁ : v ∈ V₁
      · have hu_notin : u ∉ V₁ := by rw [hueq]; exact hv_c
        obtain ⟨-, hveq2, -⟩ := hcross_eq e v u hl.symm hv₁ hu_notin
        have hpu : point u = point_vc := by rw [hueq]; simp only [point, hv_c, ↓reduceIte]
        have hpv : point v = point₁ u_c := by rw [hveq2]; simp only [point, hu_c, ↓reduceIte]
        rw [hpu, hpv]
        refine LinearIndependent.pair_symm_iff.mp ?_
        rw [LinearIndependent.pair_iff' hp1_ne]
        intro a ha
        exact hpvc_notmem (ha ▸ Submodule.smul_mem _ a (Submodule.subset_span hmem₀))
      · exfalso
        have hveq : v = v_c :=
          Set.mem_singleton_iff.mp
            ((show v ∈ V₁ ∪ ({v_c} : Set α) by rw [← hVG]; exact hl.right_mem).resolve_left hv₁)
        rw [hueq, hveq] at hl
        exact G.not_isLoopAt e v_c hl
  -- ── Conjunct 3: closed-hub-neighbourhood normal LI. ──────────────────────────────────────
  have hHubNbhd_eq : ∀ v ∈ V₁, G.closedHubNbhd v = (G.induce V₁).closedHubNbhd v := by
    intro v hv
    ext w
    constructor
    · rintro ⟨hwhub, hcase⟩
      have hwne_vc : w ≠ v_c := fun h => hvc_not_hub (h ▸ hwhub)
      have hwV1 : w ∈ V₁ := by
        have hwG : w ∈ V(G) := hwhub.1
        rw [hVG] at hwG
        exact hwG.resolve_right hwne_vc
      have hwhubH : (G.induce V₁).PencilHub w := by
        by_cases hwu : w = u_c
        · rw [hwu]; rw [hwu] at hwhub; exact hu_c_hub_iff.mp hwhub
        · refine ⟨hwV1, ?_⟩; rw [hdeg_eq w hwV1 hwu]; exact hwhub.2
      refine ⟨hwhubH, ?_⟩
      rcases hcase with rfl | ⟨e, hl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨e, (Graph.induce_isLink G V₁ e v w).mpr ⟨hl, hv, hwV1⟩⟩
    · rintro ⟨hwhubH, hcase⟩
      have hwV1 : w ∈ V₁ := hwhubH.1
      have hwG : w ∈ V(G) := by rw [hVG]; exact Set.mem_union_left _ hwV1
      have hwhub : G.PencilHub w := by
        by_cases hwu : w = u_c
        · rw [hwu]; rw [hwu] at hwhubH; exact hu_c_hub_iff.mpr hwhubH
        · refine ⟨hwG, ?_⟩; rw [← hdeg_eq w hwV1 hwu]; exact hwhubH.2
      refine ⟨hwhub, ?_⟩
      rcases hcase with rfl | ⟨e, hl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨e, ((Graph.induce_isLink G V₁ e v w).mp hl).1⟩
  have hclosedHubNbhd_vc : G.closedHubNbhd v_c ⊆ {u_c} := by
    rintro w ⟨hwhub, hcase⟩
    rcases hcase with rfl | ⟨e, hl⟩
    · exact absurd hwhub hvc_not_hub
    · have hwV1 : w ∈ V₁ := by
        by_contra hwV1
        have hweq : w = v_c :=
          Set.mem_singleton_iff.mp
            ((show w ∈ V₁ ∪ ({v_c} : Set α) by rw [← hVG]; exact hwhub.1).resolve_left hwV1)
        rw [hweq] at hl
        exact G.not_isLoopAt e v_c hl
      obtain ⟨-, hweq2, -⟩ := hcross_eq e w v_c hl.symm hwV1 hv_c
      simp [hweq2]
  have hnu_ne : normal u_c ≠ 0 := by simp only [normal, hu_c, ↓reduceIte]; exact hn1_ne
  have hhubLI_glued : ∀ v ∈ V(G), LinearIndepOn K normal (G.closedHubNbhd v) := by
    intro v hv
    by_cases hv₁ : v ∈ V₁
    · rw [hHubNbhd_eq v hv₁]
      refine (hhubLI₁ v hv₁).congr (fun x hx => ?_)
      have hxV₁ : x ∈ V₁ := hx.1.1
      simp only [normal, hxV₁, ↓reduceIte]
    · have hveq : v = v_c :=
        Set.mem_singleton_iff.mp
          ((show v ∈ V₁ ∪ ({v_c} : Set α) by rw [← hVG]; exact hv).resolve_left hv₁)
      rw [hveq]
      exact (LinearIndepOn.singleton (i := u_c) hnu_ne).mono hclosedHubNbhd_vc
  -- ── Conjunct 4: non-hub closed-neighbourhood point LI. ───────────────────────────────────
  have hnbhdLI_glued : ∀ v ∈ V(G), ¬ G.PencilHub v → LinearIndepOn K point (G.closedNbhd v) := by
    intro v hv hnothub
    by_cases hv₁ : v ∈ V₁
    · by_cases hvu : v = u_c
      · have hnothub_uc : ¬ G.PencilHub u_c := by rw [← hvu]; exact hnothub
        rw [hvu]
        have hnothubH : ¬ (G.induce V₁).PencilHub u_c :=
          fun h => hnothub_uc (hu_c_hub_iff.mpr h)
        have hbase : LinearIndepOn K point ((G.induce V₁).closedNbhd u_c) := by
          refine (hnbhdLI₁ u_c hu_c hnothubH).congr (fun x hx => ?_)
          have hxV₁ : x ∈ V₁ := by
            rcases hx with rfl | ⟨e, hl⟩
            · exact hu_c
            · exact ((Graph.induce_isLink G V₁ e u_c x).mp hl).2.2
          simp only [point, hxV₁, ↓reduceIte]
        have hset : G.closedNbhd u_c = insert v_c ((G.induce V₁).closedNbhd u_c) := by
          ext w
          constructor
          · rintro (rfl | ⟨e, hl⟩)
            · exact Set.mem_insert_of_mem _ (Or.inl rfl)
            · by_cases hw₁ : w ∈ V₁
              · exact Set.mem_insert_of_mem _
                  (Or.inr ⟨e, (Graph.induce_isLink G V₁ e u_c w).mpr ⟨hl, hu_c, hw₁⟩⟩)
              · obtain ⟨-, -, hweq⟩ := hcross_eq e u_c w hl hu_c hw₁
                rw [hweq]; exact Set.mem_insert _ _
          · rintro (rfl | (rfl | ⟨e, hl⟩))
            · exact Or.inr ⟨e_c, hl_c⟩
            · exact Or.inl rfl
            · exact Or.inr ⟨e, ((Graph.induce_isLink G V₁ e u_c w).mp hl).1⟩
        rw [hset]
        refine hbase.insert ?_
        intro hmem
        have hpv : point v_c = point_vc := by simp only [point, hv_c, ↓reduceIte]
        rw [hpv] at hmem
        apply hpvc_notmem
        refine Submodule.span_mono ?_ hmem
        rintro _ ⟨x, hx, rfl⟩
        have hxV₁ : x ∈ V₁ := by
          rcases hx with rfl | ⟨e, hl⟩
          · exact hu_c
          · exact ((Graph.induce_isLink G V₁ e u_c x).mp hl).2.2
        have hpx : point x = point₁ x := by simp only [point, hxV₁, ↓reduceIte]
        rw [hpx]
        exact hcov₀ hnothub_uc ⟨x, hx, rfl⟩
      · have hnothubH : ¬ (G.induce V₁).PencilHub v := by
          intro h
          exact hnothub ⟨hv, by rw [← hdeg_eq v hv₁ hvu]; exact h.2⟩
        have hbase := hnbhdLI₁ v hv₁ hnothubH
        have hset : G.closedNbhd v = (G.induce V₁).closedNbhd v := by
          ext w
          constructor
          · rintro (rfl | ⟨e, hl⟩)
            · exact Or.inl rfl
            · have hw₁ : w ∈ V₁ := by
                by_contra hw₁
                obtain ⟨-, hveq, -⟩ := hcross_eq e v w hl hv₁ hw₁
                exact hvu hveq
              exact Or.inr ⟨e, (Graph.induce_isLink G V₁ e v w).mpr ⟨hl, hv₁, hw₁⟩⟩
          · rintro (rfl | ⟨e, hl⟩)
            · exact Or.inl rfl
            · exact Or.inr ⟨e, ((Graph.induce_isLink G V₁ e v w).mp hl).1⟩
        rw [hset]
        refine hbase.congr (fun x hx => ?_)
        have hxV₁ : x ∈ V₁ := by
          rcases hx with rfl | ⟨e, hl⟩
          · exact hv₁
          · exact ((Graph.induce_isLink G V₁ e v x).mp hl).2.2
        simp only [point, hxV₁, ↓reduceIte]
    · have hveq : v = v_c :=
        Set.mem_singleton_iff.mp
          ((show v ∈ V₁ ∪ ({v_c} : Set α) by rw [← hVG]; exact hv).resolve_left hv₁)
      have hset : G.closedNbhd v = ({v_c, u_c} : Set α) := by
        rw [hveq]
        ext w
        constructor
        · rintro (rfl | ⟨e, hl⟩)
          · exact Set.mem_insert _ _
          · have hwV1 : w ∈ V₁ := by
              by_contra hwV1
              have hweq2 : w = v_c :=
                Set.mem_singleton_iff.mp
                  ((show w ∈ V₁ ∪ ({v_c} : Set α) by
                    rw [← hVG]; exact hl.right_mem).resolve_left hwV1)
              rw [hweq2] at hl
              exact G.not_isLoopAt e v_c hl
            obtain ⟨-, hweq3, -⟩ := hcross_eq e w v_c hl.symm hwV1 hv_c
            rw [hweq3]
            exact Set.mem_insert_of_mem _ rfl
        · rintro (rfl | rfl)
          · exact Or.inl rfl
          · exact Or.inr ⟨e_c, hl_c.symm⟩
      rw [hset]
      rw [LinearIndepOn.pair_iff point (fun h => hv_c (h ▸ hu_c) : v_c ≠ u_c)]
      exact LinearIndependent.pair_iff.mp
        (LinearIndependent.pair_symm_iff.mp (hadjLI e_c u_c v_c hl_c))
  -- ── Rank. ──────────────────────────────────────────────────────────────────────────────────
  have hne : V₁.Nonempty := ⟨u_c, hu_c⟩
  have hssub : V₁ ⊂ V(G) :=
    (Set.ssubset_iff_of_subset hV₁sub).mpr ⟨v_c, by rw [hVG]; exact Set.mem_union_right _ rfl, hv_c⟩
  have hVcard : V₁.ncard + (V(G) \ V₁).ncard = V(G).ncard := by
    have hdisj : Disjoint V₁ (V(G) \ V₁) := Set.disjoint_sdiff_right
    rw [← Set.ncard_union_eq hdisj (Set.toFinite V₁) (Set.toFinite _), Set.union_diff_cancel hV₁sub]
  have hD1 : 1 ≤ Graph.bodyBarDim n := by omega
  have hdef : G.deficiency n = (G.induce V₁).deficiency n + (G.induce (V(G) \ V₁)).deficiency n
      + (Graph.bodyBarDim n : ℤ) - ((Graph.bodyBarDim n : ℤ) - 1) * (G.cutEdges V₁).ncard :=
    Graph.deficiency_eq_of_cutEdges_ncard_le_one hD1 hne hssub hcut
  have hFext : ∀ e u v, F.graph.IsLink e u v → F.supportExtensor e ≠ 0 := fun e _ _ _ => hextF_nz e
  have hFcut : ∀ e ∈ G.cutEdges V₁, ∃ a b, F.graph.IsLink e a b ∧ a ∈ V₁ ∧ b ∉ V₁ := by
    intro e he
    simp only [Graph.cutEdges, Set.mem_setOf_eq] at he
    obtain ⟨-, a, b, hlab, ha, hb⟩ := he
    exact ⟨a, b, hlab, ha, hb⟩
  have hFVne : V(F.graph).Nonempty := ⟨u_c, hV₁sub hu_c⟩
  have hagree₁ : ∀ e u v, (G.induce V₁).IsLink e u v → extF e = F₁.supportExtensor e :=
    fun e u v hl => by
      simp only [extF, show (∃ a b, (G.induce V₁).IsLink e a b) from ⟨u, v, hl⟩, ↓reduceIte]
  have hF₁span := span_rigidityRows_eq_of_supportExtensor_agree extF F₁ hF₁g hagree₁
  have hlb₁ : screwDim 2 * ((V₁.ncard : ℤ) - 1) - (G.induce V₁).deficiency n
      ≤ (Module.finrank K (Submodule.span K F₁.rigidityRows) : ℤ) := hrank₁.ge
  have hlb₂ : screwDim 2 * (((V(G) \ V₁).ncard : ℤ) - 1) - (G.induce (V(G) \ V₁)).deficiency n
      ≤ (Module.finrank K (Submodule.span K
        (⟨G.induce (V(G) \ V₁), extF⟩ : BodyHingeFramework K 2 α β).rigidityRows) : ℤ) := by
    have hrows_empty : (⟨G.induce (V(G) \ V₁), extF⟩ :
        BodyHingeFramework K 2 α β).rigidityRows = ∅ := by
      ext φ
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨e, u, v, hlink, -⟩
      have he : e ∈ E(G.induce (V(G) \ V₁)) := hlink.edge_mem
      rw [hV₂edgeless] at he
      exact he
    have hVeq₂ : (V(G) \ V₁).ncard = 1 := by rw [hV₂eq]; exact Set.ncard_singleton v_c
    have hVeq₂' : V(G.induce (V(G) \ V₁)).ncard = 1 := hVeq₂
    rw [hrows_empty, Submodule.span_empty, finrank_bot, hVeq₂,
      Graph.deficiency_of_edgeSet_empty hV₂edgeless, hVeq₂']
    norm_num
  have hrank_eq := finrank_span_rigidityRows_cutEdge_eq hD hn F rfl rfl hcut hFext hFcut hFVne
    hVcard hdef hF₁span rfl hlb₁ hlb₂
  exact ⟨F, normal, point,
    ⟨⟨⟨rfl, hnorm_nz, hextF_nz,
        fun e u v hl => ⟨(hlinks e u v hl).1, (hlinks e u v hl).2.1⟩⟩,
      hpoint_nz, hpoint_inc,
      fun e u v hl => ⟨(hlinks e u v hl).2.2.1, (hlinks e u v hl).2.2.2⟩⟩,
    hadjLI, hhubLI_glued, hnbhdLI_glued⟩, hrank_eq⟩

/-! ## W5-L5 cut arm, the dispatch shell (Phase 39 PENCIL, L5-cut-iv)

The generic-half assembly wiring all four sub-cases of the cut-arm route verdict
(`notes/Phase39-design.md` §"W5 leaf decomposition" L5 "Cut-arm route verdict") into
`pencilPair_of_not_twoEdgeConnected`: the bare half reuses the landed W3-L4
`hasPencilRealization_of_not_twoEdgeConnected` verbatim (feeding it `hIH`'s own bare halves); the
generic half re-derives the cut decomposition (mirroring the bare arm's own unfold of
`¬TwoEdgeConnected`) and dispatches on `(G.cutEdges V₁).ncard`, then — at the single crossing edge
`e_c = u_c v_c` over `V₁`, complement `V₂` — on which side (if either) is a pendant singleton: `|C|
= 0` is sub-case 2 (`hasGenericPencilRealization_of_cutEdges_eq_empty`); a pendant singleton side
with attachment degree `≠ 3` is sub-case 3
(`hasGenericPencilRealization_of_isNondegPencilRealization_induce_pendant`) — the cut-vertex-set
unfold is unoriented (nothing pins which of `V₁`/`V₂` is the pendant side), so both orientations
route through the same producer with `u_c`/`v_c` (and `V₁`/`V₂`) swapped; a pendant singleton side
with attachment degree exactly `3` is the residual sub-case 4, carried as the explicit hypothesis
`hcutPendant3` (the standing no-`sorry` idiom, `CombinatorialRigidity/CLAUDE.md`) rather than built:
its shape mirrors the pendant producer's own premises with the degree inequality flipped to an
equality and the IH-witness/rank arguments dropped, since the design doc's finding shows no plain
IH consumption can close this sub-case's output gap — this is exactly the eventual conclusion of
L5-cut-v's chart-steering candidate route (**do not build that route yet**: its two
somewhere-witness constructions need a numerics-first assessment first, design doc L5-cut-iv/v),
not a stronger convenience form (it is scoped to this `G` alone, and does not restate the ambient
`G.Simple`/`PencilNondegFeasible K G`/`hIH` already in context). Both sides `≥ 2` is sub-case 1,
consuming the IH at the two edge-closed sides `Gᵢ⁺ = G.induce (Vᵢ ∪ {far})` and gluing via
`hasGenericPencilRealization_of_isNondegPencilRealization_induce_union_singleton`. -/

/-- **The cut arm of the pencil reduction, conditioned-pair motive, dispatch shell**
(Phase 39 W5-L5, L5-cut-iv; the `PencilPair` analogue of the bare-motive
`hasPencilRealization_of_not_twoEdgeConnected`, W3-L4). Let `G` be a multigraph that is not
`2`-edge-connected. If every smaller graph satisfies the conditioned pair at rank `n` (`hIH`), and
every pendant-singleton cut configuration of `G` at attachment degree exactly `3` has a generic
pencil realization (`hcutPendant3`, the residual sub-case 4 — `notes/Phase39-design.md` §"W5 leaf
decomposition" L5-cut-v, design-open), then so does `G` satisfy the conditioned pair. -/
theorem pencilPair_of_not_twoEdgeConnected [Finite α] [Finite β] {n : ℕ}
    (hD : 2 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim 2)
    {G : Graph α β} (hntec : ¬ G.TwoEdgeConnected)
    (hcutPendant3 : ∀ {V₁ : Set α} {e_c : β} {u_c v_c : α}, G.IsLink e_c u_c v_c →
      u_c ∈ V₁ → v_c ∉ V₁ → V(G) = V₁ ∪ {v_c} → (G.cutEdges V₁).ncard ≤ 1 →
      G.degree u_c = 3 → HasGenericPencilRealization K n G)
    (hIH : ∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard → PencilPair K n G') :
    PencilPair K n G := by
  refine ⟨fun hSimple hfeas => ?_,
    hasPencilRealization_of_not_twoEdgeConnected hD hn hntec
      (fun G' hne' hlt' => (hIH G' hne' hlt').2)⟩
  classical
  haveI := hSimple.toLoopless
  simp only [Graph.TwoEdgeConnected, not_forall, not_le, exists_prop] at hntec
  obtain ⟨V₁, hne, hssub, hcut_lt2⟩ := hntec
  have hcut_le : (G.cutEdges V₁).ncard ≤ 1 := Nat.lt_succ_iff.mp hcut_lt2
  set V₂ := V(G) \ V₁
  rcases Set.eq_empty_or_nonempty (G.cutEdges V₁) with hC0 | ⟨e_c, he_c⟩
  · -- ── `|C| = 0`: sub-case 2, the landed disjoint-union producer. ──────────────────────────
    exact hasGenericPencilRealization_of_cutEdges_eq_empty hD hn hne hssub hC0 hSimple hfeas hIH
  · -- ── `|C| = 1`: sub-cases 1/3/4, dispatched on which side (if either) is a pendant. ───────
    have hne₂ : V₂.Nonempty := Set.nonempty_of_ssubset hssub
    have hVcard : V₁.ncard + V₂.ncard = V(G).ncard := by
      have hunion : V₁ ∪ V₂ = V(G) := Set.union_diff_cancel hssub.subset
      have hdisj : Disjoint V₁ V₂ := Set.disjoint_sdiff_right
      rw [← hunion, Set.ncard_union_eq hdisj (Set.toFinite V₁) (Set.toFinite V₂)]
    have hV₁ne : V(G.induce V₁).Nonempty := hne
    have hV₂ne : V(G.induce V₂).Nonempty := hne₂
    have hVeq₂ : V(G.induce V₂).ncard = V₂.ncard := rfl
    have hV₁ncard : V(G.induce V₁).ncard < V(G).ncard := Set.ncard_lt_ncard hssub (Set.toFinite _)
    have hV₂ncard : V(G.induce V₂).ncard < V(G).ncard := by
      have hV₁pos : 0 < V₁.ncard := hne.ncard_pos
      rw [hVeq₂]; omega
    simp only [Graph.cutEdges, Set.mem_setOf_eq] at he_c
    obtain ⟨-, u_c, v_c, hl_c, hu_c, hv_c⟩ := he_c
    have hv_c₂ : v_c ∈ V₂ := ⟨hl_c.right_mem, hv_c⟩
    have hu_notin₂ : u_c ∉ V₂ := fun h => h.2 hu_c
    have hV₂sub : V₂ ⊆ V(G) := Set.diff_subset
    have hcut₂ : (G.cutEdges V₂).ncard ≤ 1 :=
      le_trans (Set.ncard_le_ncard (Graph.cutEdges_diff_subset G V₁) (Set.toFinite _)) hcut_le
    by_cases hV₂one : V₂.ncard = 1
    · -- The far side `V₂` is a pendant singleton `{v_c}`: sub-case 3 (or 4, at `deg u_c = 3`).
      have hV₂eq : V₂ = {v_c} := by
        obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp hV₂one
        have hav : v_c ∈ ({a} : Set α) := by rw [← ha]; exact hv_c₂
        rw [Set.mem_singleton_iff] at hav
        rw [ha, hav]
      have hVG : V(G) = V₁ ∪ {v_c} := by
        rw [← hV₂eq]; exact (Set.union_diff_cancel hssub.subset).symm
      by_cases hdeg3 : G.degree u_c = 3
      · exact hcutPendant3 hl_c hu_c hv_c hVG hcut_le hdeg3
      · have hSimple₁ : (G.induce V₁).Simple := hSimple.mono (Graph.induce_le hssub.subset)
        have hfeas₁ : PencilNondegFeasible K (G.induce V₁) := by
          refine hfeas.mono (Graph.induce_le hssub.subset) ?_
          intro v hv hGhub
          by_cases hvu : v = u_c
          · rw [hvu]; rw [hvu] at hGhub
            exact Or.inl ((Graph.pencilHub_iff_induce_of_degree_ne
              hl_c hu_c hv_c hcut_le hdeg3).mp hGhub)
          · exact Or.inl ⟨hv, by
              rw [Graph.degree_induce_eq_of_ne hl_c hu_c hv_c hcut_le hv hvu]
              exact hGhub.2⟩
        obtain ⟨F₁, normal₁, point₁, hnd₁, hrank₁⟩ :=
          (hIH (G.induce V₁) hV₁ne hV₁ncard).1 hSimple₁ hfeas₁
        exact hasGenericPencilRealization_of_isNondegPencilRealization_induce_pendant
          hD hn hl_c hu_c hv_c hVG hcut_le hdeg3 hnd₁ hrank₁
    · by_cases hV₁one : V₁.ncard = 1
      · -- The near side `V₁` is itself a pendant singleton `{u_c}`: sub-case 3/4, swapped roles.
        have hV₁eq : V₁ = {u_c} := by
          obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp hV₁one
          have hau : u_c ∈ ({a} : Set α) := by rw [← ha]; exact hu_c
          rw [Set.mem_singleton_iff] at hau
          rw [ha, hau]
        have hVG' : V(G) = V₂ ∪ {u_c} := by
          rw [← hV₁eq]; exact (Set.diff_union_of_subset hssub.subset).symm
        by_cases hdeg3' : G.degree v_c = 3
        · exact hcutPendant3 hl_c.symm hv_c₂ hu_notin₂ hVG' hcut₂ hdeg3'
        · have hSimple₂ : (G.induce V₂).Simple := hSimple.mono (Graph.induce_le hV₂sub)
          have hfeas₂ : PencilNondegFeasible K (G.induce V₂) := by
            refine hfeas.mono (Graph.induce_le hV₂sub) ?_
            intro v hv hGhub
            by_cases hvv : v = v_c
            · rw [hvv]; rw [hvv] at hGhub
              exact Or.inl ((Graph.pencilHub_iff_induce_of_degree_ne
                hl_c.symm hv_c₂ hu_notin₂ hcut₂ hdeg3').mp hGhub)
            · exact Or.inl ⟨hv, by
                rw [Graph.degree_induce_eq_of_ne hl_c.symm hv_c₂ hu_notin₂ hcut₂ hv hvv]
                exact hGhub.2⟩
          obtain ⟨F₂, normal₂, point₂, hnd₂, hrank₂⟩ :=
            (hIH (G.induce V₂) hV₂ne hV₂ncard).1 hSimple₂ hfeas₂
          exact hasGenericPencilRealization_of_isNondegPencilRealization_induce_pendant
            hD hn hl_c.symm hv_c₂ hu_notin₂ hVG' hcut₂ hdeg3' hnd₂ hrank₂
      · -- Both sides `≥ 2`: sub-case 1, the `Gᵢ⁺` IH consumption + repositioning glue.
        have hV₂ge2 : 2 ≤ V₂.ncard := by have := hne₂.ncard_pos; omega
        have hV₁ge2 : 2 ≤ V₁.ncard := by have := hne.ncard_pos; omega
        have hV1p_sub : V₁ ∪ {v_c} ⊆ V(G) := by
          rintro x (hx | rfl)
          · exact hssub.subset hx
          · exact hl_c.right_mem
        have hV2p_sub : V₂ ∪ {u_c} ⊆ V(G) := by
          rintro x (hx | rfl)
          · exact hV₂sub hx
          · exact hl_c.left_mem
        have hV1p_card : V(G.induce (V₁ ∪ {v_c})).ncard = V₁.ncard + 1 := by
          change (V₁ ∪ {v_c}).ncard = V₁.ncard + 1
          rw [Set.union_singleton]
          exact Set.ncard_insert_of_notMem hv_c
        have hV2p_card : V(G.induce (V₂ ∪ {u_c})).ncard = V₂.ncard + 1 := by
          change (V₂ ∪ {u_c}).ncard = V₂.ncard + 1
          rw [Set.union_singleton]
          exact Set.ncard_insert_of_notMem hu_notin₂
        have hlt1p : V(G.induce (V₁ ∪ {v_c})).ncard < V(G).ncard := by rw [hV1p_card]; omega
        have hlt2p : V(G.induce (V₂ ∪ {u_c})).ncard < V(G).ncard := by rw [hV2p_card]; omega
        have hSimple1p : (G.induce (V₁ ∪ {v_c})).Simple := hSimple.mono (Graph.induce_le hV1p_sub)
        have hSimple2p : (G.induce (V₂ ∪ {u_c})).Simple := hSimple.mono (Graph.induce_le hV2p_sub)
        have hfeas1p : PencilNondegFeasible K (G.induce (V₁ ∪ {v_c})) :=
          hfeas.induce_union_singleton hl_c hu_c hv_c hssub.subset hcut_le
        have hfeas2p : PencilNondegFeasible K (G.induce (V₂ ∪ {u_c})) :=
          hfeas.induce_union_singleton hl_c.symm hv_c₂ hu_notin₂ hV₂sub hcut₂
        have hne1p : V(G.induce (V₁ ∪ {v_c})).Nonempty := ⟨u_c, Set.mem_union_left _ hu_c⟩
        have hne2p : V(G.induce (V₂ ∪ {u_c})).Nonempty := ⟨v_c, Set.mem_union_left _ hv_c₂⟩
        obtain ⟨F₁, normal₁, point₁, hnd₁, hrank₁⟩ :=
          (hIH (G.induce (V₁ ∪ {v_c})) hne1p hlt1p).1 hSimple1p hfeas1p
        obtain ⟨F₂, normal₂, point₂, hnd₂, hrank₂⟩ :=
          (hIH (G.induce (V₂ ∪ {u_c})) hne2p hlt2p).1 hSimple2p hfeas2p
        exact hasGenericPencilRealization_of_isNondegPencilRealization_induce_union_singleton
          hD hn hl_c hu_c hv_c hssub.subset hcut_le hfeas hnd₁ hrank₁ hnd₂ hrank₂

end CombinatorialRigidity.Molecular
