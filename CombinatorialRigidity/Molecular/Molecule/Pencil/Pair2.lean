/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.Pair
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.GenericSteer

/-!
# The conditioned pair at a cut edge

The cut-edge case of `lem:pencil-pair-loop-base-cut` (`sec:pencil-nondegenerate`) for the
conditioned pair (`PencilPair`), the node itself, and `thm:pencil-conditional-realization-pair`, the
reduction of `sec:pencil-reduction` for the conditioned pair. `Pair.lean` gives the loop and base
cases, and the generic conjunct at a cut that no edge crosses, or that one edge crosses with at
least two bodies on each side.

This file gives the generic conjunct at a cut that one edge `e_c` crosses, from `u_c ∈ V₁` to `v_c`,
with the single body `v_c` on the other side, at every degree of `u_c`. Then `V(G) = V₁ ∪ {v_c}`,
the side `V₁` with the far end of `e_c` is `G` itself, and the induction applies instead to
`H := G.induce V₁`, which has one body fewer. Part (a) of `lem:pencil-generic-steer`
(`exists_isNondegPencilRealization_restrict_of_demoted`) makes `H` nondegeneracy-feasible, by a
realization whose normals are independent on the closed hub-neighbourhood in `G` of every body: the
only neighbour that a body of `H` loses is `v_c`, of degree `1`, so not a hub. Part (b)
(`exists_isNondegPencilRealization_steer`) moves the generic realization of `H`, at the same rank,
to one whose normals are independent on these sets too. Then `v_c` gets a point in the panel of
`u_c`, off the span of two vectors at `u_c`, and a panel through that point and the point of `u_c`,
and the two sides glue
(`hasGenericPencilRealization_of_isNondegPencilRealization_induce_pendant_of_hubLI`).

## Main results

* `hasGenericPencilRealization_pendant_of_IH`: the generic conjunct at a cut with a single body on
  one side.
* `pencilPair_of_not_twoEdgeConnected`: the conditioned pair at a cut edge.
* `pencilPair_loop_base_cut`: the conditioned pair at a loop, on at most two bodies and at a cut
  edge (`lem:pencil-pair-loop-base-cut`).
* `pencilPair_of_arms`: the conditioned pair from the contraction and split cases
  (`thm:pencil-conditional-realization-pair`).
-/

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K]
variable {α β : Type*}

/-! ## At a cut with one body on a side: the glue

`V(G) = V₁ ∪ {v_c}`, one edge `e_c` crosses `V₁`, from `u_c` to `v_c`, and `H := G.induce V₁`. The
glue asks that the normals of the realization of `H` be independent on the closed hub-neighbourhood
in `G` of every body of `V₁`: at `G.degree u_c = 3`, deleting `e_c` leaves `u_c` a hub of `G` that
is not one of `H`, so the condition for `H` does not give that for `G`. The point at `v_c` avoids
the span of two vectors at `u_c`: `point₁ u_c` and `0` when `u_c` is a hub of `G`, where only the
independence of the points of the two ends of `e_c` is at stake, and otherwise the points of the
closed neighbourhood of `u_c` in `H`, at most two, as `u_c` has degree at most `1` in `H`; there
`u_c` is not a hub of `H` either, as a hub of `H` is one of `G` (`Graph.PencilHub.of_le`), and the
realization of `H` gives the independence of these points. No hypothesis of the glue concerns the
degree of `u_c`. The side `{v_c}` has no edge: it takes the normal and point at `v_c`, and the hinge
of `e_c` at every label, and the lower bound on its rank is `0`. -/

/-- **The glue at a cut with one body on a side** (a step of `lem:pencil-pair-loop-base-cut`, case
(3)): let `G` be loopless, and `e_c` link `u_c ∈ V₁` to `v_c ∉ V₁`, with `V(G) = V₁ ∪ {v_c}` and at
most one edge crossing `V₁`. Given a nondegenerate realization of `G.induce V₁` at its deficiency
rank whose normals are linearly independent on the closed hub-neighbourhood in `G` of every body of
`V₁` (`hhub`), `G` has a generic pencil realization. The point at `v_c` is chosen in the panel of
`u_c`, of dimension `3` (`finrank_toDualPerp_single_eq`), off the span of the two vectors of the
section header; the normal at `v_c` is nonzero and orthogonal to the points at `u_c` and `v_c`, in a
space of dimension at least `2` (`le_finrank_toDualPerp_inf`). The hinge of `e_c` comes from
`exists_extensor_two_pencils`, and the two sides glue by `exists_hasPencilPanelRealization_glue`. -/
theorem hasGenericPencilRealization_of_isNondegPencilRealization_induce_pendant_of_hubLI
    [Finite α] [Finite β] {n : ℕ}
    (hD : 2 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim 2)
    {G : Graph α β} [G.Loopless] {V₁ : Set α} {e_c : β} {u_c v_c : α}
    (hl_c : G.IsLink e_c u_c v_c) (hu_c : u_c ∈ V₁) (hv_c : v_c ∉ V₁)
    (hVG : V(G) = V₁ ∪ {v_c}) (hcut : (G.cutEdges V₁).ncard ≤ 1)
    {F₁ : BodyHingeFramework K 2 α β} {normal₁ point₁ : α → Fin 4 → K}
    (hnd₁ : IsNondegPencilRealization (G.induce V₁) F₁ normal₁ point₁)
    (hrank₁ : (Module.finrank K (Submodule.span K F₁.rigidityRows) : ℤ)
      = screwDim 2 * ((V₁.ncard : ℤ) - 1) - (G.induce V₁).deficiency n)
    (hhub : ∀ v ∈ V₁, LinearIndepOn K normal₁ (G.closedHubNbhd v)) :
    HasGenericPencilRealization K n G := by
  classical
  -- ── `G.induce (V₁ ∪ {v_c}) = G`, `v_c` has degree `1`, and `e_c` is the crossing link. ───
  have hGeq : G.induce (V₁ ∪ {v_c}) = G := by rw [← hVG]; exact Graph.induce_vertexSet G
  have hvc_deg : G.degree v_c = 1 := by
    have h := Graph.degree_induce_union_singleton_far hl_c hu_c hv_c hcut
    rwa [hGeq] at h
  have hvc_not_hub : ¬ G.PencilHub v_c := by
    intro h; have h2 := h.2; omega
  have hcross_eq : ∀ e' x y, G.IsLink e' x y → x ∈ V₁ → y ∉ V₁ →
      e' = e_c ∧ x = u_c ∧ y = v_c :=
    fun e' x y hle hx hy => Graph.eq_and_eq_of_isLink_crossing hl_c hu_c hv_c hcut hle hx hy
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
    simp only [Graph.edgeSet_induce, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨a, b, hl, ha, hb⟩
    rw [hV₂eq, Set.mem_singleton_iff] at ha hb
    rw [ha, hb] at hl
    exact G.not_isLoopAt e v_c hl
  -- ── The realization of `H`. ──────────────────────────────────────────────────────────────
  obtain ⟨hreal₁, hadj₁, -, hnbhdLI₁⟩ := hnd₁
  obtain ⟨⟨hF₁g, hn₁nz, -, -⟩, hp₁nz, hp₁inc, -⟩ := id hreal₁
  have hn1_ne : normal₁ u_c ≠ 0 := hn₁nz u_c hu_c
  have hp1_ne : point₁ u_c ≠ 0 := hp₁nz u_c hu_c
  -- ── Two vectors at `u_c` for the point at `v_c` to avoid, one of them `point₁ u_c`. ──────
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
  -- ── Choose `point_vc` in the panel of `u_c`, off the span of the two vectors. ────────────
  have hVdim : Module.finrank K (ker₁ (normal₁ u_c)) = 3 := finrank_toDualPerp_single_eq hn1_ne
  have hspan_le : Module.finrank K (Submodule.span K ({a₀, b₀} : Set (Fin 4 → K))) ≤ 2 :=
    finrank_span_pair_le a₀ b₀
  have hnotle : ¬ (ker₁ (normal₁ u_c) ≤ Submodule.span K ({a₀, b₀} : Set (Fin 4 → K))) := by
    intro hle
    have hm := Submodule.finrank_mono hle
    omega
  obtain ⟨point_vc, hpvc_mem, hpvc_notmem⟩ := IsConcreteLE.not_le_iff_exists.mp hnotle
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
  obtain ⟨normal_vc, hnvc_mem, hnvc_notbot⟩ := IsConcreteLE.not_le_iff_exists.mp hnvc_notle
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
  -- ── The points of the two ends of each link are independent. ─────────────────────────────
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
  -- ── The normals on each closed hub-neighbourhood. ────────────────────────────────────────
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
    · refine (hhub v hv₁).congr (fun x hx => ?_)
      have hxV₁ : x ∈ V₁ := (show x ∈ V₁ ∪ ({v_c} : Set α) by rw [← hVG]; exact hx.1.1)
        |>.resolve_right fun h => hvc_not_hub (Set.mem_singleton_iff.mp h ▸ hx.1)
      simp only [normal, hxV₁, ↓reduceIte]
    · have hveq : v = v_c :=
        Set.mem_singleton_iff.mp
          ((show v ∈ V₁ ∪ ({v_c} : Set α) by rw [← hVG]; exact hv).resolve_left hv₁)
      rw [hveq]
      exact (LinearIndepOn.singleton (i := u_c) hnu_ne).mono hclosedHubNbhd_vc
  -- ── The points on the closed neighbourhood of each body not a hub. ───────────────────────
  have hnbhdLI_glued : ∀ v ∈ V(G), ¬ G.PencilHub v → LinearIndepOn K point (G.closedNbhd v) := by
    intro v hv hnothub
    by_cases hv₁ : v ∈ V₁
    · by_cases hvu : v = u_c
      · have hnothub_uc : ¬ G.PencilHub u_c := by rw [← hvu]; exact hnothub
        rw [hvu]
        have hnothubH : ¬ (G.induce V₁).PencilHub u_c :=
          fun h => hnothub_uc (h.of_le (Graph.induce_le hV₁sub))
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
  -- ── The glue (`exists_hasPencilPanelRealization_glue`): the pendant side `{v_c}` is edgeless,
  -- realized by the constant data at `v_c` with the pendant hinge as every extensor. ────────────
  have hne : V₁.Nonempty := ⟨u_c, hu_c⟩
  have hssub : V₁ ⊂ V(G) :=
    (Set.ssubset_iff_of_subset hV₁sub).mpr ⟨v_c, by rw [hVG]; exact Set.mem_union_right _ rfl, hv_c⟩
  have hnolink : ∀ e u v, ¬ (G.induce (V(G) \ V₁)).IsLink e u v := fun e u v hl => by
    have he : e ∈ E(G.induce (V(G) \ V₁)) := hl.edge_mem
    rw [hV₂edgeless] at he
    exact he
  have hreal₂ : HasPencilPanelRealization (G.induce (V(G) \ V₁))
      ⟨G.induce (V(G) \ V₁), fun _ => C_cut⟩ (fun _ => normal_vc) (fun _ => point_vc) :=
    ⟨⟨rfl, fun _ _ => hnvc_ne, fun _ => hCne, fun e u v hl => absurd hl (hnolink e u v)⟩,
      fun _ _ => hpvc_ne, fun _ _ => by rw [dotProduct_comm]; exact hnvc_pvc,
      fun e u v hl => absurd hl (hnolink e u v)⟩
  have hlb₂ : screwDim 2 * (((V(G) \ V₁).ncard : ℤ) - 1) - (G.induce (V(G) \ V₁)).deficiency n
      ≤ (Module.finrank K (Submodule.span K (⟨G.induce (V(G) \ V₁), fun _ => C_cut⟩ :
        BodyHingeFramework K 2 α β).rigidityRows) : ℤ) := by
    have hrows_empty : (⟨G.induce (V(G) \ V₁), fun _ => C_cut⟩ :
        BodyHingeFramework K 2 α β).rigidityRows = ∅ := by
      ext φ
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨e, u, v, hlink, -⟩
      exact hnolink e u v hlink
    have hVeq₂ : (V(G) \ V₁).ncard = 1 := by rw [hV₂eq]; exact Set.ncard_singleton v_c
    have hVeq₂' : V(G.induce (V(G) \ V₁)).ncard = 1 := hVeq₂
    rw [hrows_empty, Submodule.span_empty, finrank_bot, hVeq₂,
      Graph.deficiency_of_edgeSet_empty hV₂edgeless, hVeq₂']
    norm_num
  obtain ⟨F, hreal, hrank_eq⟩ := exists_hasPencilPanelRealization_glue hD hn hssub hne hcut
    (hreal₁.restrict le_rfl) hreal₂
    (by rw [span_rigidityRows_eq_of_supportExtensor_agree _ F₁ hF₁g (fun _ _ _ _ => rfl)]
        exact hrank₁.ge)
    hlb₂ hCne (fun e u v hl hu hv => by
      obtain ⟨-, rfl, -⟩ := hcross_eq e u v hl hu hv
      exact ⟨hCpn_u, hCpn_v, hCth_u, hCth_v⟩)
  exact ⟨F, normal, point, ⟨hreal, hadjLI, hhubLI_glued, hnbhdLI_glued⟩, hrank_eq⟩

/-! ## At a cut with one body on a side: the induction

By part (a) of `lem:pencil-generic-steer`, a nondegenerate realization of `G` restricts to one of
`H := G.induce V₁`; the induction hypothesis gives `H` a generic realization; and part (b) moves it
to one whose normals are independent on `G.closedHubNbhd v` for every `v ∈ V₁`. Every member of
these sets is a hub of `G` in `V₁`; one that is not a hub of `H` is `u_c` at degree `3`, with three
closed neighbours in `H` (`ncard_closedNbhd_eq_three_of_demoted`, with `L := {v_c}`), as (b) asks.
The glue of the previous section concludes. -/

/-- **The generic conjunct at a cut with one body on a side** (a step of
`lem:pencil-pair-loop-base-cut`, case (3)): over an infinite field, let `G` be simple and
nondegeneracy-feasible, and `e_c` link `u_c ∈ V₁` to `v_c ∉ V₁`, with `V(G) = V₁ ∪ {v_c}` and at
most one edge crossing `V₁`. If every nonempty graph on fewer bodies than `G` satisfies
`PencilPair K n` (`hIH`), then `G` has a generic pencil realization. With `H := G.induce V₁`,
`exists_isNondegPencilRealization_restrict_of_demoted` (part (a) of `lem:pencil-generic-steer`)
makes `H` nondegeneracy-feasible, `hIH` gives `H` a generic realization,
`exists_isNondegPencilRealization_steer` (part (b)) moves it to one whose normals are independent on
`G.closedHubNbhd v` for every `v ∈ V₁`, and
`hasGenericPencilRealization_of_isNondegPencilRealization_induce_pendant_of_hubLI` glues. -/
theorem hasGenericPencilRealization_pendant_of_IH [Finite α] [Finite β] [Infinite K]
    {n : ℕ} (hD : 2 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim 2)
    {G : Graph α β} {V₁ : Set α} {e_c : β} {u_c v_c : α}
    (hSimple : G.Simple) (hfeas : PencilNondegFeasible K G)
    (hl_c : G.IsLink e_c u_c v_c) (hu_c : u_c ∈ V₁) (hv_c : v_c ∉ V₁)
    (hVG : V(G) = V₁ ∪ {v_c}) (hcut : (G.cutEdges V₁).ncard ≤ 1)
    (hIH : ∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard → PencilPair K n G') :
    HasGenericPencilRealization K n G := by
  classical
  have := hSimple
  have := hSimple.toLoopless
  have hV₁sub : V₁ ⊆ V(G) := by rw [hVG]; exact Set.subset_union_left
  have hle : G.induce V₁ ≤ G := Graph.induce_le hV₁sub
  have hS₁ : (G.induce V₁).Simple := hSimple.mono hle
  have hvc_hub : ¬ G.PencilHub v_c := by
    have h := Graph.degree_induce_union_singleton_far hl_c hu_c hv_c hcut
    rw [← hVG, Graph.induce_vertexSet] at h
    exact fun hh => by have := hh.2; omega
  have hoff : ∀ y ∈ V(G), y ∉ V₁ → y = v_c := fun y hy hyV => by
    rw [hVG] at hy; exact hy.resolve_left hyV
  have hNsub : ∀ v ∈ V₁, N(G, v) ⊆ {v_c} ∪ N(G.induce V₁, v) := by
    intro v hv y ⟨f, hf⟩
    by_cases hy : y ∈ V₁
    · exact Or.inr ⟨f, (Graph.induce_isLink G V₁ f v y).mpr ⟨hf, hv, hy⟩⟩
    · exact Or.inl (hoff y hf.right_mem hy)
  obtain ⟨F, normal, point, hndG, hndH⟩ :=
    exists_isNondegPencilRealization_restrict_of_demoted hSimple hfeas hle
      (fun v hv _ _ y hy hyH => by
        rcases hNsub v hv hy with h | h
        · rw [Set.mem_singleton_iff.mp h]; exact hvc_hub
        · exact absurd h hyH)
  have hssub : V₁ ⊂ V(G) :=
    (Set.ssubset_iff_of_subset hV₁sub).mpr
      ⟨v_c, by rw [hVG]; exact Set.mem_union_right _ rfl, hv_c⟩
  obtain ⟨F₁, normal₁, point₁, hnd₁, hrank₁⟩ :=
    (hIH (G.induce V₁) ⟨u_c, hu_c⟩ (Set.ncard_lt_ncard hssub (Set.toFinite _))).1 hS₁
      ⟨_, _, _, hndH⟩
  have hCsub : ∀ v ∈ V₁, G.closedHubNbhd v ⊆ V₁ := by
    rintro v hv w ⟨hwhub, rfl | ⟨f, hf⟩⟩
    · exact hv
    · by_contra hwV
      exact hvc_hub (hoff w hf.right_mem hwV ▸ hwhub)
  obtain ⟨F', n', p', hnd', hrank', hS', -⟩ := exists_isNondegPencilRealization_steer hn
    hS₁.toLoopless ⟨u_c, hu_c⟩ hnd₁ hrank₁ hndH (fun v : V₁ => G.closedHubNbhd v)
    (fun v => hCsub v v.2)
    (fun v w hw hwH => ncard_closedNbhd_eq_three_of_demoted hSimple hle hwH (hCsub v v.2 hw)
      (hNsub w (hCsub v v.2 hw)) (by rw [Set.ncard_singleton]; have := hw.1.2; omega))
    (fun v => hndG.2.2.1 v (hV₁sub v.2))
    (Empty.elim : Empty → α) (Empty.elim : Empty → α) (fun j => j.elim) (fun j => j.elim)
    (fun j => j.elim) (fun j => j.elim)
  exact hasGenericPencilRealization_of_isNondegPencilRealization_induce_pendant_of_hubLI hD hn
    hl_c hu_c hv_c hVG hcut hnd' hrank' fun v hv => hS' ⟨v, hv⟩

/-! ## At a cut edge

`pencilPair_of_not_twoEdgeConnected` puts the cut-edge case together. Its pencil realization at the
deficiency rank is that of the bare case (`hasPencilRealization_of_not_twoEdgeConnected`,
`lem:pencil-cut-case`), and its adjacent-distinct conjunct that case's second form
(`hasDistinctPencilRealization_of_not_twoEdgeConnected`), each from the same conjunct of the
induction hypothesis. For the generic conjunct it takes a nonempty `V₁ ⊂ V(G)` that at most one edge
crosses, as `¬ G.TwoEdgeConnected` gives, and goes by cases. No edge crosses:
`hasGenericPencilRealization_of_cutEdges_eq_empty`. One edge `e_c` crosses, from `u_c ∈ V₁` to
`v_c`, and a side is a single body: `hasGenericPencilRealization_pendant_of_IH`, with the roles of
the sides and of the ends of `e_c` exchanged when that side is `V₁`. Both sides have at least two
bodies: the induction hypothesis applies to each side with the far end of `e_c`, which is
nondegeneracy-feasible (`PencilNondegFeasible.induce_union_singleton`), and
`hasGenericPencilRealization_of_isNondegPencilRealization_induce_union_singleton` glues.

The case of a single body on a side needs the feasibility of `G`, as part (a) of
`lem:pencil-generic-steer` restricts a nondegenerate realization of `G`. The net graph, a triangle
with a pendant edge at each body, has no generic pencil realization, but it is not
nondegeneracy-feasible, so the case does not arise there. -/

/-- **The conditioned pair at a cut edge** (a step of `lem:pencil-pair-loop-base-cut`, case (3)):
over an infinite field, if `G` is not `2`-edge-connected and every nonempty graph on fewer bodies
than `G` satisfies `PencilPair K n` (`hIH`), then so does `G`, by the cases of the section header.
The hypothesis of `hasDistinctPencilRealization_of_not_twoEdgeConnected` (`Arms.lean`) at each
`G' ≤ G` on fewer bodies is the adjacent-distinct conjunct of `hIH`, as `G'` is simple when `G` is
(`Graph.Simple.mono`). -/
theorem pencilPair_of_not_twoEdgeConnected [Finite α] [Finite β] [Infinite K] {n : ℕ}
    (hD : 2 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim 2)
    {G : Graph α β} (hntec : ¬ G.TwoEdgeConnected)
    (hIH : ∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard → PencilPair K n G') :
    PencilPair K n G := by
  refine ⟨fun hSimple hfeas => ?_,
    fun hSimple => hasDistinctPencilRealization_of_not_twoEdgeConnected hD hn hntec
      (fun G' hle' hne' hlt' => (hIH G' hne' hlt').2.1 (hSimple.mono hle')),
    hasPencilRealization_of_not_twoEdgeConnected hD hn hntec
      (fun G' hne' hlt' => (hIH G' hne' hlt').2.2)⟩
  have := hSimple.toLoopless
  simp only [Graph.TwoEdgeConnected, not_forall, not_le, exists_prop] at hntec
  obtain ⟨V₁, hne, hssub, hcut_lt2⟩ := hntec
  have hcut_le : (G.cutEdges V₁).ncard ≤ 1 := Nat.lt_succ_iff.mp hcut_lt2
  set V₂ := V(G) \ V₁
  rcases Set.eq_empty_or_nonempty (G.cutEdges V₁) with hC0 | ⟨e_c, he_c⟩
  · -- no edge crosses `V₁`
    exact hasGenericPencilRealization_of_cutEdges_eq_empty hD hn hne hssub hC0 hSimple hfeas hIH
  · -- one edge crosses `V₁`: by the sizes of the sides
    have hne₂ : V₂.Nonempty := Set.nonempty_of_ssubset hssub
    simp only [Graph.cutEdges, Set.mem_ofPred_eq] at he_c
    obtain ⟨-, u_c, v_c, hl_c, hu_c, hv_c⟩ := he_c
    have hv_c₂ : v_c ∈ V₂ := ⟨hl_c.right_mem, hv_c⟩
    have hu_notin₂ : u_c ∉ V₂ := fun h => h.2 hu_c
    have hV₂sub : V₂ ⊆ V(G) := Set.sdiff_subset
    have hcut₂ : (G.cutEdges V₂).ncard ≤ 1 :=
      le_trans (Set.ncard_le_ncard (Graph.cutEdges_diff_subset G V₁) (Set.toFinite _)) hcut_le
    by_cases hV₂one : V₂.ncard = 1
    · -- the side `V₂` is the single body `v_c`
      have hV₂eq : V₂ = {v_c} :=
        (Set.ncard_le_one_iff_subsingleton.mp hV₂one.le).eq_singleton_of_mem hv_c₂
      exact hasGenericPencilRealization_pendant_of_IH hD hn hSimple hfeas hl_c hu_c hv_c
        (by rw [← hV₂eq]; exact (Set.union_sdiff_cancel hssub.subset).symm) hcut_le hIH
    · by_cases hV₁one : V₁.ncard = 1
      · -- the side `V₁` is the single body `u_c`: the roles of the sides exchanged
        have hV₁eq : V₁ = {u_c} :=
          (Set.ncard_le_one_iff_subsingleton.mp hV₁one.le).eq_singleton_of_mem hu_c
        exact hasGenericPencilRealization_pendant_of_IH hD hn hSimple hfeas hl_c.symm hv_c₂
          hu_notin₂ (by rw [← hV₁eq]; exact (Set.sdiff_union_of_subset hssub.subset).symm)
          hcut₂ hIH
      · -- both sides have at least two bodies: each side with the far end of `e_c`, and the glue
        have hVcard : V₁.ncard + V₂.ncard = V(G).ncard := by
          have hunion : V₁ ∪ V₂ = V(G) := Set.union_sdiff_cancel hssub.subset
          have hdisj : Disjoint V₁ V₂ := Set.disjoint_sdiff_right
          rw [← hunion, Set.ncard_union_eq hdisj (Set.toFinite V₁) (Set.toFinite V₂)]
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
          rw [Graph.vertexSet_induce, Set.union_singleton]
          exact Set.ncard_insert_of_notMem hv_c
        have hV2p_card : V(G.induce (V₂ ∪ {u_c})).ncard = V₂.ncard + 1 := by
          rw [Graph.vertexSet_induce, Set.union_singleton]
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

/-! ## The reduction for the conditioned pair

`Graph.pencil_reduction` at `n = 3` for the property `PencilPair K 3`. Its loop, base and cut-edge
cases hold (`pencilPair_loop_base_cut`, from `pencilPair_of_isLoopAt`, `pencilPair_of_ncard_le_two`
and `pencilPair_of_not_twoEdgeConnected`), so `pencilPair_of_arms` takes only the contraction and
split cases, and concludes at every nonempty graph. `pencil_realization_theorem_of_X0` and
`pencilPair_of_nonempty` use it. -/

/-- **The conditioned pair at a loop, on at most two bodies and at a cut edge**
(`lem:pencil-pair-loop-base-cut`): the loop, base and cut-edge cases of `Graph.pencil_reduction` for
the property `PencilPair K 3`, over an infinite field. At a loop the pair holds given it at the
graph with the loop deleted, smaller in the order of the reduction (`pencilPair_of_isLoopAt`); on at
most two bodies it holds outright (`pencilPair_of_ncard_le_two`); at a cut edge it holds given it at
every nonempty graph on fewer bodies (`pencilPair_of_not_twoEdgeConnected`). -/
theorem pencilPair_loop_base_cut [Finite α] [Finite β] [Infinite K] :
    (∀ G : Graph α β, (∃ e x, G.IsLoopAt e x) →
      (∀ G' : Graph α β, V(G').Nonempty →
        V(G').ncard < V(G).ncard ∨ (V(G').ncard = V(G).ncard ∧ E(G').ncard < E(G).ncard) →
        PencilPair K 3 G') → PencilPair K 3 G) ∧
    (∀ G : Graph α β, G.Loopless → V(G).Nonempty → V(G).ncard ≤ 2 → PencilPair K 3 G) ∧
    (∀ G : Graph α β, G.Loopless → 3 ≤ V(G).ncard → ¬ G.TwoEdgeConnected →
      (∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard → PencilPair K 3 G') →
      PencilPair K 3 G) := by
  have hD6 : (6 : ℕ) ≤ Graph.bodyBarDim 3 := Graph.six_le_bodyBarDim (by norm_num)
  have hn : Graph.bodyBarDim 3 = screwDim 2 := Graph.bodyBarDim_eq_screwDim_sub_one (by norm_num)
  refine ⟨?_, fun G hloop hne hV2 => pencilPair_of_ncard_le_two hloop hne hV2,
    fun G _ _ hntec hIH => pencilPair_of_not_twoEdgeConnected (by omega) hn hntec hIH⟩
  rintro G ⟨e, x, hloopAt⟩ IH
  refine pencilPair_of_isLoopAt hloopAt (IH (G ＼ ({e} : Set β)) ?_ (Or.inr ⟨?_, ?_⟩))
  · rw [Graph.vertexSet_deleteEdges]; exact ⟨x, hloopAt.left_mem⟩
  · rw [Graph.vertexSet_deleteEdges]
  · rw [Graph.edgeSet_deleteEdges]
    exact Set.ncard_sdiff_singleton_lt_of_mem hloopAt.edge_mem

/-- **The conditioned pair from the contraction and split cases**
(`thm:pencil-conditional-realization-pair`): over an infinite field, `Graph.pencil_reduction` at
`n = 3` for the property `PencilPair K 3`, with its loop, base and cut-edge cases from
`pencilPair_loop_base_cut`, gives the conditioned pair at every nonempty graph from the contraction
case `hcontract` and the split case `hsplit`. -/
theorem pencilPair_of_arms [Finite α] [Finite β] [Infinite K]
    (hcontract : ∀ G : Graph α β, G.Loopless → 3 ≤ V(G).ncard →
      (∃ H : Graph α β, H.IsProperRigidSubgraph G 3) →
      (∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard →
        PencilPair K 3 G') →
      PencilPair K 3 G)
    (hsplit : ∀ G : Graph α β, G.Loopless → 3 ≤ V(G).ncard → G.TwoEdgeConnected →
      (∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G 3) →
      (∃ v ∈ V(G), G.degree v = 2) →
      (∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard →
        PencilPair K 3 G') →
      PencilPair K 3 G)
    (G : Graph α β) (hne : V(G).Nonempty) :
    PencilPair K 3 G := by
  classical
  obtain ⟨hloop, hbase, hcut⟩ := pencilPair_loop_base_cut (K := K) (α := α) (β := β)
  exact Graph.pencil_reduction (Graph.six_le_bodyBarDim (by norm_num)) hloop hbase hcut hcontract
    hsplit G hne

end CombinatorialRigidity.Molecular
