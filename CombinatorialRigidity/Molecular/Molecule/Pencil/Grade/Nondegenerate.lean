/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Embedding

/-!
# Nondegenerate pencil realizations in every dimension

`def:pencil-d-nondegenerate`, `lem:pencil-d-nondegenerate-three` and
`lem:pencil-d-nondegenerate-maps` (`blueprint/src/chapter/pencil-d.tex`,
`sec:pencil-d-nondegenerate`). A pencil realization in grade `k` (dimension `d = k + 1`) is
*nondegenerate* (`IsNondegPencilPlaneRealization`) when its normals and subspaces satisfy
`PencilNondegConditions`: the normals of the two ends of every link are linearly independent, those
of the closed neighbourhood of a body that is not a hub are, and the subspaces of at least two
members of a closed hub-neighbourhood meet in dimension at most `4 - |S|`. The multigraph is
*nondegeneracy-feasible* (`GradedPencilNondegFeasible`) when it has one, and has a *generic* one
(`HasGradedGenericPencilRealization`) when the rows of one span the deficiency rank.

In dimension three, with `Π_v = n_v^⊥`, the conditions are those of `IsNondegPencilRealization` on
the polarity's image (`isNondegPencilPlaneRealization_two_iff`, through
`finrank_iInf_dotPerp_add_card_le_iff` and `pencilNondegConditions_dotPerp_iff`), so the two
feasibilities and the two generic realizations agree (`gradedPencilNondegFeasible_two_iff`,
`hasGradedGenericPencilRealization_two_iff`).

The conditions pull back along a linear map injective on the subspaces
(`PencilNondegConditions.of_map`) and are kept by an injective one (`PencilNondegConditions.map`),
so the embedding of a nondegenerate realization is nondegenerate
(`IsNondegPencilPlaneRealization.map_gradeEmbed`).
-/

@[expose] public section

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

/-! ## The definition -/

/-- **The three conditions of nondegeneracy** (`def:pencil-d-nondegenerate`), on normals and
subspaces of `K^N`: the normals of the two ends of every link are linearly independent; at every
body that is not a hub, the normals of its closed neighbourhood are; and at every body `v` and every
set `S` of at least two members of its closed hub-neighbourhood, `dim ⋂_{w ∈ S} Π_w ≤ 4 - |S|`,
written `dim + |S| ≤ 4`. -/
def PencilNondegConditions {N : ℕ} (G : Graph α β) (normal : α → Fin N → K)
    (plane : α → Submodule K (Fin N → K)) : Prop :=
  (∀ e u v, G.IsLink e u v → LinearIndependent K ![normal u, normal v]) ∧
  (∀ v ∈ V(G), ¬ G.PencilHub v → LinearIndepOn K normal (G.closedNbhd v)) ∧
  (∀ v ∈ V(G), ∀ S : Finset α, (S : Set α) ⊆ G.closedHubNbhd v → 2 ≤ S.card →
    Module.finrank K (⨅ w ∈ S, plane w : Submodule K (Fin N → K)) + S.card ≤ 4)

/-- **A nondegenerate pencil realization in every dimension** (`def:pencil-d-nondegenerate`). -/
def IsNondegPencilPlaneRealization {k : ℕ} (G : Graph α β) (F : BodyHingeFramework K k α β)
    (normal : α → Fin (k + 2) → K) (plane : α → Submodule K (Fin (k + 2) → K)) : Prop :=
  HasPencilPlaneRealization G F normal plane ∧ PencilNondegConditions G normal plane

/-- **Nondegeneracy-feasibility in dimension `k + 1`** (`def:pencil-d-nondegenerate`). -/
def GradedPencilNondegFeasible (K : Type*) [Field K] (k : ℕ) (G : Graph α β) : Prop :=
  ∃ (F : BodyHingeFramework K k α β) (normal : α → Fin (k + 2) → K)
    (plane : α → Submodule K (Fin (k + 2) → K)), IsNondegPencilPlaneRealization G F normal plane

/-- **A generic pencil realization in dimension `k + 1`** (`def:pencil-d-nondegenerate`). -/
def HasGradedGenericPencilRealization (K : Type*) [Field K] (k n : ℕ) (G : Graph α β) : Prop :=
  ∃ (F : BodyHingeFramework K k α β) (normal : α → Fin (k + 2) → K)
    (plane : α → Submodule K (Fin (k + 2) → K)),
    IsNondegPencilPlaneRealization G F normal plane ∧
    (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
      = screwDim k * ((V(G).ncard : ℤ) - 1) - G.deficiency n

/-! ## Dimension three -/

/-- The intersection of the orthogonals of finitely many vectors is the orthogonal of their span. -/
theorem iInf_dotPerp_span_singleton_eq {N : ℕ} (n : α → Fin N → K) (S : Finset α) :
    (⨅ w ∈ S, dotPerp (K ∙ n w) : Submodule K (Fin N → K)) =
      dotPerp (Submodule.span K (n '' (S : Set α))) := by
  ext x
  simp only [Submodule.mem_iInf, mem_dotPerp_span_singleton]
  rw [Set.image_eq_range, mem_dotPerp_span_range]
  exact ⟨fun h i => h i i.2, fun h w hw => h ⟨w, hw⟩⟩

/-- **The dimension of an intersection of orthogonals** (a step of
`lem:pencil-d-nondegenerate-three`): `dim ⋂_{w ∈ S} n_w^⊥ + |S| ≤ N` exactly when the `n_w`,
`w ∈ S`, are linearly independent. -/
theorem finrank_iInf_dotPerp_add_card_le_iff {N : ℕ} (n : α → Fin N → K) (S : Finset α) :
    Module.finrank K (⨅ w ∈ S, dotPerp (K ∙ n w) : Submodule K (Fin N → K)) + S.card ≤ N ↔
      LinearIndepOn K n (S : Set α) := by
  classical
  rw [iInf_dotPerp_span_singleton_eq, finrank_dotPerp]
  have hle : Module.finrank K (Submodule.span K (n '' (S : Set α))) ≤ N := by
    simpa using Submodule.finrank_le (Submodule.span K (n '' (S : Set α)))
  have hcard : Module.finrank K (Submodule.span K (n '' (S : Set α))) ≤ S.card := by
    calc _ ≤ (n '' (S : Set α)).toFinset.card := finrank_span_le_card _
      _ ≤ S.card := by
        rw [Set.toFinset_image, Finset.toFinset_coe]; exact Finset.card_image_le
  have hiff : LinearIndepOn K n (S : Set α) ↔
      Module.finrank K (Submodule.span K (n '' (S : Set α))) = S.card := by
    rw [LinearIndepOn, linearIndependent_iff_card_eq_finrank_span, Set.finrank,
      ← Set.image_eq_range]
    simp only [Finset.coe_sort_coe, Fintype.card_coe]
    exact eq_comm
  rw [hiff]
  omega

/-- **The conditions in dimension three** (`lem:pencil-d-nondegenerate-three`): with
`Π_v = n_v^⊥` and `n_v ≠ 0`, the three conditions on `b` and `Π` are those of
`IsNondegPencilRealization` on the points `b` and the normals `n`, without the realization. -/
theorem pencilNondegConditions_dotPerp_iff {G : Graph α β} {b n : α → Fin 4 → K}
    (hn : ∀ v ∈ V(G), n v ≠ 0) :
    PencilNondegConditions G b (fun v => dotPerp (K ∙ n v)) ↔
      (∀ e u v, G.IsLink e u v → LinearIndependent K ![b u, b v]) ∧
      (∀ v ∈ V(G), LinearIndepOn K n (G.closedHubNbhd v)) ∧
      (∀ v ∈ V(G), ¬ G.PencilHub v → LinearIndepOn K b (G.closedNbhd v)) := by
  classical
  unfold PencilNondegConditions
  simp only [finrank_iInf_dotPerp_add_card_le_iff]
  refine ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, fun v hv => ?_, h2⟩, fun ⟨h1, h2, h3⟩ =>
    ⟨h1, h3, fun v hv S hS _ => (h2 v hv).mono hS⟩⟩
  refine linearIndepOn_of_finite _ fun t ht htfin => ?_
  by_cases h2t : 2 ≤ htfin.toFinset.card
  · simpa using h3 v hv htfin.toFinset (by simpa using ht) h2t
  · rcases Finset.card_le_one.1 (by omega : htfin.toFinset.card ≤ 1) with h
    rcases t.eq_empty_or_nonempty with rfl | ⟨w, hw⟩
    · exact linearIndepOn_empty K n
    · have ht' : t = {w} := by
        ext x
        simp only [Set.mem_singleton_iff]
        exact ⟨fun hx => h x (by simpa using hx) w (by simpa using hw), fun hx => hx ▸ hw⟩
      subst ht'
      exact LinearIndepOn.singleton (hn w (ht hw).1.1)

/-- **Nondegeneracy in dimension three** (`lem:pencil-d-nondegenerate-three`): a pencil realization
in dimension three with normals `b` and subspaces `n^⊥` is nondegenerate exactly when its image
under the polarity, with normals `n` and points `b`, is. -/
theorem isNondegPencilPlaneRealization_two_iff {G : Graph α β} {F : BodyHingeFramework K 2 α β}
    {b n : α → Fin 4 → K}
    (hreal : HasPencilPlaneRealization G F b (fun v => dotPerp (K ∙ n v))) :
    IsNondegPencilPlaneRealization G F b (fun v => dotPerp (K ∙ n v)) ↔
      IsNondegPencilRealization G (F.mapExtensor screwComplementIso) n b := by
  have hpt : HasPencilPanelRealization G F b n :=
    (hasPencilPlaneRealization_two_iff fun _ _ => rfl).1 hreal
  have hn : ∀ v ∈ V(G), n v ≠ 0 := hpt.2.1
  have hpol := hasPencilPanelRealization_mapExtensor_screwComplementIso hpt
  unfold IsNondegPencilPlaneRealization IsNondegPencilRealization
  rw [pencilNondegConditions_dotPerp_iff hn]
  exact ⟨fun ⟨_, h⟩ => ⟨hpol, h⟩, fun ⟨_, h⟩ => ⟨hreal, h⟩⟩

/-- A pencil realization with normals `normal` and points `point` gives, through the polarity, one
in dimension three with normals `point` and subspaces `normal^⊥`. -/
theorem hasPencilPlaneRealization_mapExtensor_screwComplementIso {G : Graph α β}
    {F : BodyHingeFramework K 2 α β} {normal point : α → Fin 4 → K}
    (h : HasPencilPanelRealization G F normal point) :
    HasPencilPlaneRealization G (F.mapExtensor screwComplementIso) point
      (fun v => dotPerp (K ∙ normal v)) :=
  (hasPencilPlaneRealization_two_iff fun _ _ => rfl).2
    (hasPencilPanelRealization_mapExtensor_screwComplementIso h)

/-- A plane realization in dimension three with `plane v` three-dimensional on `V(G)` writes
`plane v = n_v^⊥` on `V(G)`. -/
theorem HasPencilPlaneRealization.exists_dotPerp {G : Graph α β} {F : BodyHingeFramework K 2 α β}
    {b : α → Fin 4 → K} {plane : α → Submodule K (Fin 4 → K)}
    (h : HasPencilPlaneRealization G F b plane) :
    ∃ n : α → Fin 4 → K, ∀ v ∈ V(G), plane v = dotPerp (K ∙ n v) := by
  have hex : ∀ v, ∃ q : Fin 4 → K, v ∈ V(G) → plane v = dotPerp (K ∙ q) := by
    intro v
    by_cases hv : v ∈ V(G)
    · obtain ⟨q, -, hq⟩ := exists_eq_dotPerp_span_singleton (plane v) (h.2.1 v hv)
      exact ⟨q, fun _ => hq⟩
    · exact ⟨0, fun h' => absurd h' hv⟩
  choose n hn using hex
  exact ⟨n, hn⟩

/-- The plane conditions only read the subspaces on `V(G)`. -/
theorem PencilNondegConditions.congr_plane {N : ℕ} {G : Graph α β} {b : α → Fin N → K}
    {plane plane' : α → Submodule K (Fin N → K)} (hpl : ∀ v ∈ V(G), plane v = plane' v)
    (h : PencilNondegConditions G b plane) : PencilNondegConditions G b plane' := by
  refine ⟨h.1, h.2.1, fun v hv S hS h2 => ?_⟩
  have heq : (⨅ w ∈ S, plane w) = ⨅ w ∈ S, plane' w := by
    refine iInf_congr fun w => iInf_congr fun hw => hpl w (hS hw).1.1
  rw [← heq]
  exact h.2.2 v hv S hS h2

/-- The realization only reads the subspaces on `V(G)`. -/
theorem HasPencilPlaneRealization.congr_plane {k : ℕ} {G : Graph α β}
    {F : BodyHingeFramework K k α β} {b : α → Fin (k + 2) → K}
    {plane plane' : α → Submodule K (Fin (k + 2) → K)} (hpl : ∀ v ∈ V(G), plane v = plane' v)
    (h : HasPencilPlaneRealization G F b plane) : HasPencilPlaneRealization G F b plane' := by
  refine ⟨h.1, fun v hv => hpl v hv ▸ h.2.1 v hv, fun v hv => hpl v hv ▸ h.2.2.1 v hv,
    fun e u v huv => ?_⟩
  rw [← hpl u huv.left_mem, ← hpl v huv.right_mem]
  exact h.2.2.2 e u v huv

/-- **Nondegeneracy-feasibility in dimension three** (`lem:pencil-d-nondegenerate-three`). -/
theorem gradedPencilNondegFeasible_two_iff (G : Graph α β) :
    GradedPencilNondegFeasible K 2 G ↔ PencilNondegFeasible K G := by
  constructor
  · rintro ⟨F, b, plane, hreal, hcond⟩
    obtain ⟨n, hn⟩ := hreal.exists_dotPerp
    have hreal' := hreal.congr_plane hn
    exact ⟨_, n, b, (isNondegPencilPlaneRealization_two_iff hreal').1
      ⟨hreal', hcond.congr_plane hn⟩⟩
  · rintro ⟨F, normal, point, hnd⟩
    have hreal := hasPencilPlaneRealization_mapExtensor_screwComplementIso hnd.1
    refine ⟨_, point, _, hreal, ?_⟩
    have hn : ∀ v ∈ V(G), normal v ≠ 0 := hnd.1.1.2.1
    exact (pencilNondegConditions_dotPerp_iff hn).2 hnd.2

/-- **A generic pencil realization in dimension three** (`lem:pencil-d-nondegenerate-three`): the
two definitions ask for the same rank. -/
theorem hasGradedGenericPencilRealization_two_iff (n : ℕ) (G : Graph α β) :
    HasGradedGenericPencilRealization K 2 n G ↔ HasGenericPencilRealization K n G := by
  constructor
  · rintro ⟨F, b, plane, ⟨hreal, hcond⟩, hrank⟩
    obtain ⟨nv, hn⟩ := hreal.exists_dotPerp
    have hreal' := hreal.congr_plane hn
    refine ⟨_, nv, b, (isNondegPencilPlaneRealization_two_iff hreal').1
      ⟨hreal', hcond.congr_plane hn⟩, ?_⟩
    rw [BodyHingeFramework.finrank_span_rigidityRows_mapExtensor]
    exact hrank
  · rintro ⟨F, normal, point, hnd, hrank⟩
    have hreal := hasPencilPlaneRealization_mapExtensor_screwComplementIso hnd.1
    refine ⟨_, point, _, ⟨hreal, (pencilNondegConditions_dotPerp_iff hnd.1.1.2.1).2 hnd.2⟩, ?_⟩
    rw [BodyHingeFramework.finrank_span_rigidityRows_mapExtensor]
    exact hrank

/-! ## Linear maps -/

/-- A linear map injective on a subspace keeps its dimension. -/
theorem finrank_map_of_injOn {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] (p : V →ₗ[K] W) {P : Submodule K V} (h : Set.InjOn p P) :
    Module.finrank K (P.map p) = Module.finrank K P := by
  rw [← LinearMap.range_domRestrict]
  refine LinearMap.finrank_range_of_inj fun x y hxy => Subtype.ext (h x.2 y.2 hxy)

/-- **Nondegeneracy pulls back along a map injective on the subspaces**
(`lem:pencil-d-nondegenerate-maps`, part (1)). -/
theorem PencilNondegConditions.of_map {N N' : ℕ} {G : Graph α β} {b : α → Fin N → K}
    {plane : α → Submodule K (Fin N → K)} (p : (Fin N → K) →ₗ[K] (Fin N' → K))
    (hinj : ∀ v ∈ V(G), Set.InjOn p (plane v))
    (h : PencilNondegConditions G (fun v => p (b v)) (fun v => (plane v).map p)) :
    PencilNondegConditions G b plane := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun e u v huv => ?_, fun v hv hhub => ?_, fun v hv S hS h2S => ?_⟩
  · refine LinearIndependent.of_comp p ?_
    convert h1 e u v huv using 1
    funext i; fin_cases i <;> rfl
  · exact LinearIndepOn.of_comp p (h2 v hv hhub)
  · obtain ⟨w₀, hw₀⟩ : S.Nonempty := Finset.card_pos.1 (by omega)
    have hle : (⨅ w ∈ S, plane w) ≤ plane w₀ := iInf₂_le w₀ hw₀
    have hinj' : Set.InjOn p (⨅ w ∈ S, plane w : Submodule K (Fin N → K)) :=
      (hinj w₀ (hS hw₀).1.1).mono hle
    have hmap : (⨅ w ∈ S, plane w).map p ≤ ⨅ w ∈ S, (plane w).map p :=
      le_iInf₂ fun w hw => Submodule.map_mono (iInf₂_le w hw)
    have hfin := finrank_map_of_injOn p hinj'
    have := Submodule.finrank_mono hmap
    have := h3 v hv S hS h2S
    simp only at this
    omega

/-- **Nondegeneracy is kept by an injective linear map** (`lem:pencil-d-nondegenerate-maps`, part
(2)). -/
theorem PencilNondegConditions.map {N N' : ℕ} {G : Graph α β} {b : α → Fin N → K}
    {plane : α → Submodule K (Fin N → K)} (p : (Fin N → K) →ₗ[K] (Fin N' → K))
    (hp : Function.Injective p) (h : PencilNondegConditions G b plane) :
    PencilNondegConditions G (fun v => p (b v)) (fun v => (plane v).map p) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun e u v huv => ?_, fun v hv hhub => ?_, fun v hv S hS h2S => ?_⟩
  · have := (h1 e u v huv).map' p (LinearMap.ker_eq_bot.2 hp)
    convert this using 1
    funext i; fin_cases i <;> rfl
  · exact (h2 v hv hhub).map_injOn p hp.injOn
  · have hle : (⨅ w ∈ S, (plane w).map p) ≤ (⨅ w ∈ S, plane w).map p := by
      obtain ⟨w₀, hw₀⟩ : S.Nonempty := Finset.card_pos.1 (by omega)
      intro x hx
      have hx' : ∀ w ∈ S, x ∈ (plane w).map p := by
        simpa only [Submodule.mem_iInf] using hx
      obtain ⟨y, -, rfl⟩ := hx' w₀ hw₀
      refine ⟨y, Submodule.mem_iInf _ |>.2 fun w => Submodule.mem_iInf _ |>.2 fun hw => ?_, rfl⟩
      obtain ⟨y', hy', hyy⟩ := hx' w hw
      rwa [← hp hyy]
    have := Submodule.finrank_mono hle
    rw [finrank_map_of_injOn p hp.injOn] at this
    have := h3 v hv S hS h2S
    change Module.finrank K (⨅ w ∈ S, (plane w).map p : Submodule K (Fin N' → K)) + S.card ≤ 4
    omega

/-- **The embedding of a nondegenerate realization is nondegenerate**
(`lem:pencil-d-nondegenerate-maps`, part (2), "in particular"). -/
theorem IsNondegPencilPlaneRealization.map_gradeEmbed {k' k : ℕ} [NeZero k'] (h : k' ≤ k)
    {G : Graph α β} {F : BodyHingeFramework K k' α β} {normal : α → Fin (k' + 2) → K}
    {plane : α → Submodule K (Fin (k' + 2) → K)}
    (hnd : IsNondegPencilPlaneRealization G F normal plane) :
    IsNondegPencilPlaneRealization G (F.map (screwEmbed h)) (fun v => gradeEmbed h (normal v))
      (fun v => (plane v).map (gradeEmbed h)) :=
  ⟨hnd.1.map_gradeEmbed h, hnd.2.map _ (gradeEmbed_injective h)⟩

end CombinatorialRigidity.Molecular
