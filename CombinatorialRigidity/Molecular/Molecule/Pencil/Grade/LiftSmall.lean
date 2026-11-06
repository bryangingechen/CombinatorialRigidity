/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.LiftWitness
public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Polygon
public import CombinatorialRigidity.Molecular.AlgebraicInduction.DeficiencyBound

/-!
# Few bodies, a triangle, and a disconnected multigraph

The node `lem:pencil-d-lift-small` of `blueprint/src/chapter/pencil-d.tex`, `sec:pencil-d-generic`.

* Part (1): on at most two bodies (`liftAttains_of_ncard_le_two`) and at a triangle
  (`liftAttains_of_triangle`) every lift of every nondegenerate realization has the target rank, so
  `Q = 1` serves (`liftAttains_of_forall`). On two bodies the rank is that of one hinge
  (`finrank_span_rigidityRows_of_single_edge`); at a triangle the three hinges are independent
  (`finrank_triangle`, by `linearIndependent_normalsJoin_triangle`).
* Part (2), a cut that no edge crosses (`liftAttains_of_cutEdges_eq_empty`): the sides are
  feasible, a realization restricts to each (`IsNondegPencilPlaneRealization.induce`) and two of
  the sides glue (`exists_isNondegPencilPlaneRealization_glue`); the lifts glue body by body, the
  ranks add (`finrank_span_rigidityRows_cutVertex_eq`, with the sides disjoint) and so do the
  targets (`deficiency_eq_of_cutEdges_ncard_le_one`). The polynomial is the product of the sides'.
  It needs no `G.Simple` and no `[Infinite K]`.
-/

@[expose] public section

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

/-- A linear form with given values at three independent vectors. -/
theorem exists_dual_three {N : ℕ} {p q w : Fin N → K} (h : LinearIndependent K ![p, q, w])
    (c₁ c₂ c₃ : K) :
    ∃ ψ : Module.Dual K (Fin N → K), ψ p = c₁ ∧ ψ q = c₂ ∧ ψ w = c₃ := by
  set B := Module.Basis.span h
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (B.constr K ![c₁, c₂, c₃])
  have key : ∀ i : Fin 3, g (![p, q, w] i) = ![c₁, c₂, c₃] i := fun i => by
    have h1 := congrArg (fun f => f (B i)) hg
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.constr_basis] at h1
    rw [← h1, Module.Basis.span_apply]
  exact ⟨g, key 0, key 1, key 2⟩

/-- Three independent members of a set give an independent triple. -/
theorem LinearIndepOn.triple {N : ℕ} {f : α → Fin N → K} {S : Set α} (h : LinearIndepOn K f S)
    {p q w : α} (hp : p ∈ S) (hq : q ∈ S) (hw : w ∈ S) (hpq : p ≠ q) (hqw : q ≠ w) (hpw : p ≠ w) :
    LinearIndependent K ![f p, f q, f w] := by
  have := h.comp (fun i : Fin 3 => (⟨![p, q, w] i, by fin_cases i <;> assumption⟩ : S)) (by
    intro i j hij
    simp only [Subtype.mk.injEq] at hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm])
  convert this using 1
  funext i; fin_cases i <;> rfl

/-! ## `lem:pencil-d-lift-small` (1) -/

section Small

variable {G : Graph α β}

/-- **`Q = 1`**: if every lift by `0` of every nondegenerate realization has the target rank, the
general lift attains. -/
theorem liftAttains_of_forall {r : ℕ} (hfeas : PencilNondegFeasible K G)
    {ends : β → α × α} (hends : Graph.RecordsLinks G ends)
    (h : ∀ (F : BodyHingeFramework K 2 α β) (b0 : α → Fin 4 → K)
      (P0 : α → Submodule K (Fin 4 → K)), IsNondegPencilPlaneRealization G F b0 P0 →
      (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := r + 1 + 1) G ends
          (fun p => liftNormal b0 (fun (_ : Fin r) _ => 0) p.1 p.2)).toBodyHinge.rigidityRows) : ℤ)
        = screwDim (r + 1 + 1) * ((V(G).ncard : ℤ) - 1) - G.deficiency (r + 1 + 2)) :
    LiftAttains K r G := by
  obtain ⟨F, b, P, hnd⟩ := (gradedPencilNondegFeasible_two_iff G).2 hfeas
  refine ⟨ends, Graph.recordsLinks_iff_forall_isLink.mp hends, 1, by simp,
    ⟨0, MvPolynomial.isWeightedHomogeneous_one _ _⟩, ⟨F, b, P, hnd, by simp⟩,
    fun F b0 P0 hnd _ => ⟨fun _ => 0, fun _ => Submodule.zero_mem _, ?_⟩⟩
  exact h F b0 P0 hnd

/-- The joins of the sides of a triangle with independent vertices are independent. -/
theorem linearIndependent_normalsJoin_triangle {k : ℕ} {p q w : Fin (k + 2) → K}
    (h : LinearIndependent K ![p, q, w]) :
    LinearIndependent K ![normalsJoin p q, normalsJoin q w, normalsJoin w p] := by
  obtain ⟨f₁, h₁p, h₁q, h₁w⟩ := exists_dual_three h 1 0 0
  obtain ⟨f₂, h₂p, h₂q, h₂w⟩ := exists_dual_three h 0 1 0
  obtain ⟨f₃, h₃p, h₃q, h₃w⟩ := exists_dual_three h 0 0 1
  obtain ⟨φ₁₂, hφ₁₂⟩ := exists_linearMap_normalsJoin_eq f₁ f₂
  obtain ⟨φ₂₃, hφ₂₃⟩ := exists_linearMap_normalsJoin_eq f₂ f₃
  obtain ⟨φ₃₁, hφ₃₁⟩ := exists_linearMap_normalsJoin_eq f₃ f₁
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have e₁ := congrArg φ₁₂ hg
  have e₂ := congrArg φ₂₃ hg
  have e₃ := congrArg φ₃₁ hg
  simp [Fin.sum_univ_three, hφ₁₂, hφ₂₃, hφ₃₁, h₁p, h₁q, h₁w, h₂p, h₂q, h₂w, h₃p, h₃q,
    h₃w] at e₁ e₂ e₃
  intro i
  fin_cases i <;> simpa

/-- **A triangle with independent normals is rigid**, of rank `2D`. -/
theorem finrank_triangle [Finite α] {k : ℕ} {p q w : α} (hpq : p ≠ q) (hqw : q ≠ w) (hpw : p ≠ w)
    (hV : V(G) = {p, q, w}) {e₀ e₁ e₂ : β} (h₀ : G.IsLink e₀ p q) (h₁ : G.IsLink e₁ q w)
    (h₂ : G.IsLink e₂ w p) {ends : β → α × α} (hends : Graph.RecordsLinks G ends)
    {nv : α → Fin (k + 2) → K} (hli : LinearIndependent K ![nv p, nv q, nv w]) :
    Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := k) G ends
      (fun x => nv x.1 x.2)).toBodyHinge.rigidityRows) = screwDim k * 2 := by
  set F := (PanelHingeFramework.ofNormals (k := k) G ends (fun x => nv x.1 x.2)).toBodyHinge
  have hJ := (panelSupportExtensor_linearIndependent_iff (k := k) ![nv p, nv q, nv w]
    ![nv q, nv w, nv p]).2 (by
      convert linearIndependent_normalsJoin_triangle hli using 1; funext i; fin_cases i <;> rfl)
  have hgen : LinearIndependent K fun i => F.supportExtensor (![e₀, e₁, e₂] i) := by
    have hC : ∀ {e : β} {x y : α}, G.IsLink e x y →
        F.supportExtensor e = panelSupportExtensor (nv x) (nv y) ∨
        F.supportExtensor e = -panelSupportExtensor (nv x) (nv y) := by
      intro e x y he
      change panelSupportExtensor (nv (ends e).1) (nv (ends e).2) = _ ∨
        panelSupportExtensor (nv (ends e).1) (nv (ends e).2) = _
      rcases hends.eq_or_swap he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; rw [h1, h2]
      · right; rw [h1, h2, panelSupportExtensor_swap]
    have hJ' : LinearIndependent K fun i : Fin 3 =>
        panelSupportExtensor (![nv p, nv q, nv w] i) (![nv q, nv w, nv p] i) := hJ
    obtain ⟨c, hc, hceq⟩ : ∃ c : Fin 3 → K, (∀ i, c i ≠ 0) ∧ ∀ i,
        F.supportExtensor (![e₀, e₁, e₂] i) =
          c i • panelSupportExtensor (![nv p, nv q, nv w] i) (![nv q, nv w, nv p] i) := by
      have pick : ∀ {e : β} {x y : α}, G.IsLink e x y → ∃ c : K, c ≠ 0 ∧
          F.supportExtensor e = c • panelSupportExtensor (nv x) (nv y) := by
        intro e x y he
        rcases hC he with h | h
        · exact ⟨1, one_ne_zero, by rw [h, one_smul]⟩
        · exact ⟨-1, neg_ne_zero.2 one_ne_zero, by rw [h, neg_one_smul]⟩
      obtain ⟨c₀, hc₀, h₀'⟩ := pick h₀
      obtain ⟨c₁, hc₁, h₁'⟩ := pick h₁
      obtain ⟨c₂, hc₂, h₂'⟩ := pick h₂
      refine ⟨![c₀, c₁, c₂], fun i => by fin_cases i <;> assumption, fun i => ?_⟩
      fin_cases i <;> assumption
    have := hJ'.units_smul (fun i => Units.mk0 (c i) (hc i))
    convert this using 1
    funext i
    rw [hceq i]; rfl
  have hrig := F.theorem_55_cycle ![p, q, w] ![e₀, e₁, e₂] (fun i => by
    fin_cases i
    · exact h₀
    · exact h₁
    · exact h₂) hgen
  have hrange : Set.range ![p, q, w] = F.graph.vertexSet := by
    change _ = V(G)
    rw [hV, Matrix.range_cons, Matrix.range_cons, Matrix.range_cons, Matrix.range_empty,
      Set.union_empty, Set.singleton_union, Set.singleton_union]
  rw [hrange] at hrig
  have hne : F.graph.vertexSet.Nonempty := ⟨p, by change p ∈ V(G); rw [hV]; exact Or.inl rfl⟩
  rw [(F.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows hne).1 hrig]
  change screwDim k * (V(G).ncard - 1) = _
  rw [hV, Set.ncard_eq_three.2 ⟨p, q, w, hpq, hpw, hqw, rfl⟩]

/-- **`lem:pencil-d-lift-small` (1), at most two bodies.** The ambient `[Nonempty α]` is a carrier
artifact: over an empty `α` with edge labels, `LiftAttains` asks for a selector `β → α × α`, which
does not exist. -/
theorem liftAttains_of_ncard_le_two [Finite α] [Finite β] [Nonempty α] (r : ℕ)
    (hS : G.Simple) (hfeas : PencilNondegFeasible K G) (h2 : V(G).ncard ≤ 2) :
    LiftAttains K r G := by
  classical
  have := hS
  have : Inhabited α := Classical.inhabited_of_nonempty ‹_›
  have hends := Graph.recordsLinks_endsOf G
  refine liftAttains_of_forall hfeas hends fun F b0 P0 hnd => ?_
  have hn : Graph.bodyBarDim (r + 1 + 2) = screwDim (r + 1 + 1) :=
    Graph.bodyBarDim_add_one_eq_screwDim _
  by_cases hE : E(G) = ∅
  · have hrows : (PanelHingeFramework.ofNormals (k := r + 1 + 1) G G.endsOf
        (fun p => liftNormal b0 (fun (_ : Fin r) _ => 0) p.1 p.2)).toBodyHinge.rigidityRows =
        ∅ := by
      ext φ; simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨e, u, v, hlink, -⟩
      have : e ∈ E(G) := hlink.edge_mem
      rw [hE] at this; exact this
    rw [hrows, Submodule.span_empty, finrank_bot, Graph.deficiency_of_edgeSet_empty hE, hn]
    push_cast; ring
  obtain ⟨x, y, hxy, hVG, hlinks⟩ :=
    exists_pair_of_ncard_le_two_of_edgeSet_nonempty hS.toLoopless h2
      (Set.nonempty_iff_ne_empty.2 hE)
  obtain ⟨e, he⟩ := Set.nonempty_iff_ne_empty.2 hE
  have hEe : E(G) = {e} := by
    ext f
    refine ⟨fun hf => (hlinks f hf).unique_edge (hlinks e he), fun hf => hf ▸ he⟩
  have hC : (PanelHingeFramework.ofNormals (k := r + 1 + 1) G G.endsOf
      (fun p => liftNormal b0 (fun (_ : Fin r) _ => 0) p.1 p.2)).toBodyHinge.supportExtensor e
        ≠ 0 := by
    change panelSupportExtensor (liftNormal b0 (fun (_ : Fin r) _ => 0) (G.endsOf e).1)
      (liftNormal b0 (fun (_ : Fin r) _ => 0) (G.endsOf e).2) ≠ 0
    rw [panelSupportExtensor_ne_zero_iff]
    exact linearIndependent_liftNormal _ (hnd.2.1 e _ _ (hends.isLink (hlinks e he)))
  exact finrank_span_rigidityRows_of_single_edge (m := r + 1) rfl hxy (hlinks e he) hVG hEe hC

/-- **`lem:pencil-d-lift-small` (1), the triangle.** -/
theorem liftAttains_of_triangle [Finite α] [Finite β] (r : ℕ) (hS : G.Simple)
    (hfeas : PencilNondegFeasible K G) (h3 : V(G).ncard = 3)
    (hadj : ∀ u ∈ V(G), ∀ v ∈ V(G), u ≠ v → G.Adj u v) :
    LiftAttains K r G := by
  classical
  have := hS
  obtain ⟨p, q, w, hpq, hpw, hqw, hV⟩ := Set.ncard_eq_three.1 h3
  have hp : p ∈ V(G) := hV ▸ Or.inl rfl
  have hq : q ∈ V(G) := hV ▸ Or.inr (Or.inl rfl)
  have hw : w ∈ V(G) := hV ▸ Or.inr (Or.inr rfl)
  obtain ⟨e₀, h₀⟩ := hadj p hp q hq hpq
  obtain ⟨e₁, h₁⟩ := hadj q hq w hw hqw
  obtain ⟨e₂, h₂⟩ := hadj w hw p hp hpw.symm
  have : Inhabited α := ⟨p⟩
  have hends := Graph.recordsLinks_endsOf G
  refine liftAttains_of_forall hfeas hends fun F b0 P0 hnd => ?_
  -- `p` is no hub, and its closed neighbourhood is all three bodies
  have hpnot : ¬ G.PencilHub p := fun h => by
    have h3' := h.2
    rw [Graph.degree_eq_ncard_adj] at h3'
    have hsub : N(G, p) ⊆ V(G) \ {p} := fun z hz => ⟨hz.right_mem, fun h => hz.ne h.symm⟩
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_sdiff (Set.singleton_subset_iff.2 hp), h3, Set.ncard_singleton] at this
    omega
  have hcl : G.closedNbhd p = {p, q, w} := by
    ext z
    refine ⟨fun hz => hV ▸ (Graph.closedNbhd_subset_vertexSet hp hz), ?_⟩
    rintro (rfl | rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr ⟨e₀, h₀⟩
    · exact Or.inr ⟨e₂, h₂.symm⟩
  have hli := LinearIndepOn.triple (hcl ▸ hnd.2.2.1 p hp hpnot) (Or.inl rfl) (Or.inr (Or.inl rfl))
    (Or.inr (Or.inr rfl)) hpq hqw hpw
  have hlin : LinearIndependent K ![liftNormal b0 (fun (_ : Fin r) _ => 0) p,
      liftNormal b0 (fun (_ : Fin r) _ => 0) q, liftNormal b0 (fun (_ : Fin r) _ => 0) w] :=
    LinearIndependent.of_comp liftProj (by
      convert hli using 1; funext i; fin_cases i <;> exact liftProj_liftVec _ _)
  have hrk := finrank_triangle (K := K) hpq hqw hpw hV h₀ h₁ h₂ hends hlin
  have hup := finrank_liftNormal_le hends (fun e x y he => hnd.2.1 e x y he) ⟨p, hp⟩
    (fun (_ : Fin r) _ => (0 : K))
  have hdef := G.deficiency_nonneg (r + 1 + 2) ⟨p, hp⟩
  rw [hrk, h3] at hup ⊢
  push_cast at hup ⊢
  linarith

end Small

/-! ## `lem:pencil-d-lift-small` (2) -/

section Disconnected

variable {G : Graph α β}

/-- A pencil realization restricts to a subgraph, in the plane form (the form of
`HasPencilPanelRealization.restrict`). -/
theorem HasPencilPlaneRealization.restrict {k : ℕ} {H : Graph α β}
    {F : BodyHingeFramework K k α β} {b : α → Fin (k + 2) → K}
    {plane : α → Submodule K (Fin (k + 2) → K)} (h : HasPencilPlaneRealization G F b plane)
    (hle : H ≤ G) : HasPencilPlaneRealization H ⟨H, F.supportExtensor⟩ b plane := by
  obtain ⟨⟨-, hnnz, hSnz, hpanel⟩, hd, hm, hthrough⟩ := h
  have hV : V(H) ⊆ V(G) := Graph.vertexSet_mono hle
  exact ⟨⟨rfl, fun v hv => hnnz v (hV hv), hSnz, fun e u v hl => hpanel e u v (hl.of_le hle)⟩,
    fun v hv => hd v (hV hv), fun v hv => hm v (hV hv),
    fun e u v hl => hthrough e u v (hl.of_le hle)⟩

/-- The conditions of nondegeneracy only read the normals and subspaces on `V(G)`. -/
theorem PencilNondegConditions.congr_on {N : ℕ} {H : Graph α β} {b b' : α → Fin N → K}
    {P P' : α → Submodule K (Fin N → K)} (hb : ∀ v ∈ V(H), b v = b' v)
    (hP : ∀ v ∈ V(H), P v = P' v) (h : PencilNondegConditions H b P) :
    PencilNondegConditions H b' P' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun e u v hl => ?_, fun v hv hnh => ?_, fun v hv S hS h2S => ?_⟩
  · rw [← hb u hl.left_mem, ← hb v hl.right_mem]; exact h1 e u v hl
  · exact (h2 v hv hnh).congr fun w hw => hb w (Graph.closedNbhd_subset_vertexSet hv hw)
  · have heq : (⨅ w ∈ S, P' w) = ⨅ w ∈ S, P w :=
      iInf_congr fun w => iInf_congr fun hw => (hP w (hS hw).1.1).symm
    rw [heq]; exact h3 v hv S hS h2S

/-- A set `S` of bodies closed under the links of `G`: its induced graph keeps the neighbourhoods
and hubs of its bodies, so its conditions of nondegeneracy are those of `G` at them. -/
theorem PencilNondegConditions.of_induce [Finite β] {N : ℕ} {S : Set α} (hSV : S ⊆ V(G))
    (hS : ∀ e x y, G.IsLink e x y → x ∈ S → y ∈ S) {b : α → Fin N → K}
    {P : α → Submodule K (Fin N → K)} (h : PencilNondegConditions (G.induce S) b P) :
    (∀ e u v, G.IsLink e u v → u ∈ S → LinearIndependent K ![b u, b v]) ∧
    (∀ v ∈ S, ¬ G.PencilHub v → LinearIndepOn K b (G.closedNbhd v)) ∧
    (∀ v ∈ S, ∀ T : Finset α, (T : Set α) ⊆ G.closedHubNbhd v → 2 ≤ T.card →
      Module.finrank K (⨅ w ∈ T, P w : Submodule K (Fin N → K)) + T.card ≤ 4) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun e u v hl hu => h1 e u v ((Graph.induce_isLink G S e u v).mpr
    ⟨hl, hu, hS e u v hl hu⟩), fun v hv hnh => ?_, fun v hv T hT h2T => ?_⟩
  · rw [← Graph.closedNbhd_induce_of_forall_isLink_mem hS hv]
    refine h2 v hv fun hh => hnh ⟨hSV hv, ?_⟩
    have := hh.2
    rwa [Graph.degree_induce_of_forall_isLink_mem hS hv] at this
  · rw [← Graph.closedHubNbhd_induce_of_forall_isLink_mem hSV hS hv] at hT
    exact h3 v hv T hT h2T

open Classical in
/-- The nondegenerate realizations of the two sides of a cut that no edge crosses glue to one of
`G`: each body keeps the normal and subspace of its own side. The framework is
`exists_hasPencilPlaneRealization`, and the conditions are those of the sides at their bodies
(`PencilNondegConditions.of_induce`). -/
theorem exists_isNondegPencilPlaneRealization_glue [Finite β] {V₁ : Set α} (hV₁ : V₁ ⊆ V(G))
    (hAdj₁ : ∀ e x y, G.IsLink e x y → x ∈ V₁ → y ∈ V₁)
    (hAdj₂ : ∀ e x y, G.IsLink e x y → x ∈ V(G) \ V₁ → y ∈ V(G) \ V₁)
    {F₁ F₂ : BodyHingeFramework K 2 α β} {b₁ b₂ : α → Fin 4 → K}
    {P₁ P₂ : α → Submodule K (Fin 4 → K)}
    (h₁ : IsNondegPencilPlaneRealization (G.induce V₁) F₁ b₁ P₁)
    (h₂ : IsNondegPencilPlaneRealization (G.induce (V(G) \ V₁)) F₂ b₂ P₂) :
    ∃ F : BodyHingeFramework K 2 α β, IsNondegPencilPlaneRealization G F
      (fun v => if v ∈ V₁ then b₁ v else b₂ v) (fun v => if v ∈ V₁ then P₁ v else P₂ v) := by
  classical
  set V₂ := V(G) \ V₁ with hV₂
  set b : α → Fin 4 → K := fun v => if v ∈ V₁ then b₁ v else b₂ v
  set P : α → Submodule K (Fin 4 → K) := fun v => if v ∈ V₁ then P₁ v else P₂ v
  have hV₂G : V₂ ⊆ V(G) := Set.sdiff_subset
  -- the conditions of each side at the glued data
  have hc₁ := PencilNondegConditions.of_induce hV₁ hAdj₁ (b := b) (P := P)
    (h₁.2.congr_on (fun v hv => by simp [b, show v ∈ V₁ from hv])
      (fun v hv => by simp [P, show v ∈ V₁ from hv]))
  have hc₂ := PencilNondegConditions.of_induce hV₂G hAdj₂ (b := b) (P := P)
    (h₂.2.congr_on (fun v hv => by simp [b, show v ∉ V₁ from (show v ∈ V₂ from hv).2])
      (fun v hv => by simp [P, show v ∉ V₁ from (show v ∈ V₂ from hv).2]))
  have hside : ∀ v ∈ V(G), v ∈ V₁ ∨ v ∈ V₂ := fun v hv => by
    by_cases h : v ∈ V₁
    · exact Or.inl h
    · exact Or.inr ⟨hv, h⟩
  have hcond : PencilNondegConditions G b P := by
    refine ⟨fun e u v hl => ?_, fun v hv hnh => ?_, fun v hv T hT h2T => ?_⟩
    · rcases hside u hl.left_mem with hu | hu
      · exact hc₁.1 e u v hl hu
      · exact hc₂.1 e u v hl hu
    · rcases hside v hv with hv' | hv'
      · exact hc₁.2.1 v hv' hnh
      · exact hc₂.2.1 v hv' hnh
    · rcases hside v hv with hv' | hv'
      · exact hc₁.2.2 v hv' T hT h2T
      · exact hc₂.2.2 v hv' T hT h2T
  -- the framework
  have hb0 : ∀ v ∈ V(G), b v ≠ 0 := fun v hv => by
    rcases hside v hv with h | h
    · simpa [b, h] using h₁.1.1.2.1 v h
    · simpa [b, h.2] using h₂.1.1.2.1 v h
  have hdim : ∀ v ∈ V(G), Module.finrank K (P v) = 3 := fun v hv => by
    rcases hside v hv with h | h
    · rw [show P v = P₁ v from ite_eq_left h]; exact h₁.1.2.1 v h
    · rw [show P v = P₂ v from ite_eq_right h.2]; exact h₂.1.2.1 v h
  have hmem : ∀ v ∈ V(G), ∀ w ∈ G.closedNbhd v, b w ∈ P v := fun v hv w hw => by
    rcases hside v hv with h | h
    · have hw₁ : w ∈ V₁ := by
        rcases hw with rfl | ⟨e, hl⟩
        · exact h
        · exact hAdj₁ e v w hl h
      have := h₁.1.normal_mem_plane_of_mem_closedNbhd (G := G.induce V₁) h
        (by rwa [Graph.closedNbhd_induce_of_forall_isLink_mem hAdj₁ h])
      simpa [b, P, h, hw₁] using this
    · have hw₂ : w ∈ V₂ := by
        rcases hw with rfl | ⟨e, hl⟩
        · exact h
        · exact hAdj₂ e v w hl h
      have := h₂.1.normal_mem_plane_of_mem_closedNbhd (G := G.induce V₂) h
        (by rwa [Graph.closedNbhd_induce_of_forall_isLink_mem hAdj₂ h])
      simpa [b, P, h.2, hw₂.2] using this
  obtain ⟨F, hF⟩ := exists_hasPencilPlaneRealization (k := 2) (G := G) (b := b) (plane := P) hb0
    (fun e u v hl => hcond.1 e u v hl) hdim hmem
  exact ⟨F, hF, hcond⟩

/-- The conditions of nondegeneracy restrict to a set of bodies closed under the links. -/
theorem PencilNondegConditions.induce [Finite β] {N : ℕ} {S : Set α} (hSV : S ⊆ V(G))
    (hS : ∀ e x y, G.IsLink e x y → x ∈ S → y ∈ S) {b : α → Fin N → K}
    {P : α → Submodule K (Fin N → K)} (h : PencilNondegConditions G b P) :
    PencilNondegConditions (G.induce S) b P := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun e u v hl => h1 e u v hl.1, fun v hv hnh => ?_, fun v hv T hT h2T => ?_⟩
  · rw [Graph.closedNbhd_induce_of_forall_isLink_mem hS hv]
    refine h2 v (hSV hv) fun hh => hnh ⟨hv, ?_⟩
    rw [Graph.degree_induce_of_forall_isLink_mem hS hv]; exact hh.2
  · rw [Graph.closedHubNbhd_induce_of_forall_isLink_mem hSV hS hv] at hT
    exact h3 v (hSV hv) T hT h2T

/-- A nondegenerate realization restricts to a set of bodies closed under the links. -/
theorem IsNondegPencilPlaneRealization.induce [Finite β] {k : ℕ} {F : BodyHingeFramework K k α β}
    {b : α → Fin (k + 2) → K} {P : α → Submodule K (Fin (k + 2) → K)} {S : Set α}
    (h : IsNondegPencilPlaneRealization G F b P) (hSV : S ⊆ V(G))
    (hS : ∀ e x y, G.IsLink e x y → x ∈ S → y ∈ S) :
    IsNondegPencilPlaneRealization (G.induce S) ⟨G.induce S, F.supportExtensor⟩ b P :=
  ⟨h.1.restrict (Graph.induce_le hSV), h.2.induce hSV hS⟩

open Classical in
/-- **`lem:pencil-d-lift-small` (2), no edge between `V₁` and its complement.** The sides are
nondegeneracy-feasible (`PencilNondegFeasible.mono`, as no body of a side loses a neighbour). A
nondegenerate realization of `G` restricts to each side
(`IsNondegPencilPlaneRealization.induce`), two of the sides glue to one of `G`
(`exists_isNondegPencilPlaneRealization_glue`), and the lifts glue body by body. The rank of the
glued lift is the sum of the ranks (`finrank_span_rigidityRows_cutVertex_eq`, with the sides
disjoint), and the deficiencies add (`deficiency_eq_of_cutEdges_ncard_le_one` at no crossing edge),
so the targets do. The polynomial is the product of the sides'. -/
theorem liftAttains_of_cutEdges_eq_empty [Finite α] [Finite β] (r : ℕ)
    {G : Graph α β} (hfeas : PencilNondegFeasible K G) {V₁ : Set α} (hne : V₁.Nonempty)
    (hssub : V₁ ⊂ V(G)) (hC0 : G.cutEdges V₁ = ∅) :
    PencilNondegFeasible K (G.induce V₁) ∧ PencilNondegFeasible K (G.induce (V(G) \ V₁)) ∧
      (LiftAttains K r (G.induce V₁) → LiftAttains K r (G.induce (V(G) \ V₁)) →
        LiftAttains K r G) := by
  set V₂ := V(G) \ V₁ with hV₂
  have hV₁G : V₁ ⊆ V(G) := hssub.subset
  have hV₂G : V₂ ⊆ V(G) := Set.sdiff_subset
  have hAdj₁ : ∀ e x y, G.IsLink e x y → x ∈ V₁ → y ∈ V₁ := by
    intro e x y hl hx
    by_contra hy
    have hmem : e ∈ G.cutEdges V₁ := ⟨hl.edge_mem, x, y, hl, hx, hy⟩
    rw [hC0] at hmem; exact hmem
  have hAdj₂ : ∀ e x y, G.IsLink e x y → x ∈ V₂ → y ∈ V₂ := by
    intro e x y hl hx
    by_contra hy
    have hyV₁ : y ∈ V₁ := by
      by_contra hy₁; exact hy ⟨hl.right_mem, hy₁⟩
    have hmem : e ∈ G.cutEdges V₁ := ⟨hl.edge_mem, y, x, hl.symm, hyV₁, hx.2⟩
    rw [hC0] at hmem; exact hmem
  have hfeas₁ : PencilNondegFeasible K (G.induce V₁) :=
    hfeas.mono (Graph.induce_le hV₁G) (fun v hv hGhub => Or.inl ⟨hv, by
      rw [Graph.degree_induce_of_forall_isLink_mem hAdj₁ hv]; exact hGhub.2⟩)
  have hfeas₂ : PencilNondegFeasible K (G.induce V₂) :=
    hfeas.mono (Graph.induce_le hV₂G) (fun v hv hGhub => Or.inl ⟨hv, by
      rw [Graph.degree_induce_of_forall_isLink_mem hAdj₂ hv]; exact hGhub.2⟩)
  refine ⟨hfeas₁, hfeas₂, fun hL₁ hL₂ => ?_⟩
  obtain ⟨ends₁, hends₁, Q₁, hQ₁v, ⟨d₁, hd₁⟩, ⟨F₁, b₁, P₁, hnd₁, hQ₁ne⟩, hall₁⟩ := hL₁
  obtain ⟨ends₂, hends₂, Q₂, hQ₂v, ⟨d₂, hd₂⟩, ⟨F₂, b₂, P₂, hnd₂, hQ₂ne⟩, hall₂⟩ := hL₂
  replace hends₁ := Graph.recordsLinks_iff_forall_isLink.mpr hends₁
  replace hends₂ := Graph.recordsLinks_iff_forall_isLink.mpr hends₂
  -- links and edges of the sides
  have indl₁ : ∀ {e u v}, G.IsLink e u v → u ∈ V₁ → (G.induce V₁).IsLink e u v :=
    fun {e u v} hl hu => (Graph.induce_isLink G V₁ e u v).mpr ⟨hl, hu, hAdj₁ e u v hl hu⟩
  have indl₂ : ∀ {e u v}, G.IsLink e u v → u ∈ V₂ → (G.induce V₂).IsLink e u v :=
    fun {e u v} hl hu => (Graph.induce_isLink G V₂ e u v).mpr ⟨hl, hu, hAdj₂ e u v hl hu⟩
  have hedge₁ : ∀ {e u v}, G.IsLink e u v → (e ∈ E(G.induce V₁) ↔ u ∈ V₁) := by
    intro e u v hl
    refine ⟨fun he => ?_, fun hu => (indl₁ hl hu).edge_mem⟩
    obtain ⟨a, b, hab⟩ := Graph.exists_isLink_of_mem_edgeSet he
    exact mem_of_induce_isLink_left hl hab
  let ends : β → α × α := fun e => if e ∈ E(G.induce V₁) then ends₁ e else ends₂ e
  have hends_1 : ∀ e, e ∈ E(G.induce V₁) → ends e = ends₁ e := fun e he => by
    simp only [ends, he, ↓reduceIte]
  have hends_2 : ∀ e, e ∈ E(G.induce V₂) → ends e = ends₂ e := fun e he => by
    obtain ⟨a, b, hab⟩ := Graph.exists_isLink_of_mem_edgeSet he
    have : e ∉ E(G.induce V₁) := fun he1 => hab.2.1.2 ((hedge₁ hab.1).1 he1)
    simp only [ends, this, ↓reduceIte]
  have hendsG : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2 := by
    intro e u v hl
    by_cases hu : u ∈ V₁
    · rw [hends_1 e ((hedge₁ hl).2 hu)]
      exact (hends₁.isLink (indl₁ hl hu)).of_le (Graph.induce_le hV₁G)
    · have hu₂ : u ∈ V₂ := ⟨hl.left_mem, hu⟩
      rw [hends_2 e (indl₂ hl hu₂).edge_mem]
      exact (hends₂.isLink (indl₂ hl hu₂)).of_le (Graph.induce_le hV₂G)
  have hendsA : Graph.RecordsLinks (G.induce V₁) ends :=
    hends₁.congr fun e _ _ hl => (hends_1 e hl.edge_mem).symm
  have hendsB : Graph.RecordsLinks (G.induce V₂) ends :=
    hends₂.congr fun e _ _ hl => (hends_2 e hl.edge_mem).symm
  have hQvars : ∀ p ∈ (Q₁ * Q₂).vars, p.1 ∈ V(G) := fun p hp => by
    rcases Finset.mem_union.1 (MvPolynomial.vars_mul Q₁ Q₂ hp) with h | h
    · exact hV₁G (hQ₁v p h)
    · exact hV₂G (hQ₂v p h)
  refine ⟨ends, hendsG, Q₁ * Q₂, hQvars, ⟨d₁ + d₂, hd₁.mul hd₂⟩, ?_, ?_⟩
  · obtain ⟨F, hF⟩ := exists_isNondegPencilPlaneRealization_glue hV₁G hAdj₁ hAdj₂ hnd₁ hnd₂
    refine ⟨F, _, _, hF, ?_⟩
    rw [map_mul]
    refine mul_ne_zero ?_ ?_
    · rw [eval_congr_vars (y := fun p => b₁ p.1 p.2) fun p hp => by
        simp [show p.1 ∈ V₁ from hQ₁v p hp]]
      exact hQ₁ne
    · rw [eval_congr_vars (y := fun p => b₂ p.1 p.2) fun p hp => by
        simp [(show p.1 ∈ V₂ from hQ₂v p hp).2]]
      exact hQ₂ne
  · intro F b0 P0 hnd hQne
    rw [map_mul] at hQne
    obtain ⟨lam₁, hlam₁, hrk₁⟩ := hall₁ _ b0 P0 (hnd.induce hV₁G hAdj₁) (left_ne_zero_of_mul hQne)
    obtain ⟨lam₂, hlam₂, hrk₂⟩ := hall₂ _ b0 P0 (hnd.induce hV₂G hAdj₂) (right_ne_zero_of_mul hQne)
    have hnb₁ : ∀ v ∈ V₁, ∀ w ∈ G.closedNbhd v, w ∈ V₁ := fun v hv w hw => by
      rcases hw with rfl | ⟨e, hl⟩
      · exact hv
      · exact hAdj₁ e v w hl hv
    have hnb₂ : ∀ v ∈ V₂, ∀ w ∈ G.closedNbhd v, w ∈ V₂ := fun v hv w hw => by
      rcases hw with rfl | ⟨e, hl⟩
      · exact hv
      · exact hAdj₂ e v w hl hv
    let lam : Fin r → (α → K) × ((v : α) → Module.Dual K (P0 v)) := fun i =>
      (fun v => if v ∈ V₁ then (lam₁ i).1 v else (lam₂ i).1 v,
       fun v => if v ∈ V₁ then (lam₁ i).2 v else (lam₂ i).2 v)
    refine ⟨lam, fun i => ?_, ?_⟩
    · intro v hv w hw h
      by_cases hv₁ : v ∈ V₁
      · have hw₁ := hnb₁ v hv₁ w hw
        have := (mem_liftSpace.1 (hlam₁ i)) v hv₁ w
          (by rwa [Graph.closedNbhd_induce_of_forall_isLink_mem hAdj₁ hv₁]) h
        simpa [lam, hv₁, hw₁] using this
      · have hv₂ : v ∈ V₂ := ⟨hv, hv₁⟩
        have hw₂ := hnb₂ v hv₂ w hw
        have := (mem_liftSpace.1 (hlam₂ i)) v hv₂ w
          (by rwa [Graph.closedNbhd_induce_of_forall_isLink_mem hAdj₂ hv₂]) h
        simpa [lam, hv₁, hw₂.2] using this
    · set qf : α × Fin (r + 1 + 1 + 2) → K :=
        fun p => liftNormal b0 (fun i => (lam i).1) p.1 p.2 with hqf
      have hrows : Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals
            (k := r + 1 + 1) G ends qf).toBodyHinge.rigidityRows)
          = Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := r + 1 + 1)
              (G.induce V₁) ends qf).toBodyHinge.rigidityRows)
            + Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := r + 1 + 1)
              (G.induce V₂) ends qf).toBodyHinge.rigidityRows) :=
        BodyHingeFramework.finrank_span_rigidityRows_cutVertex_eq _ (V₁ := V₁) (V₂ := V₂)
          (v := hne.some) (fun x hx => absurd hx.1 hx.2.2) fun e x y hl => by
            by_cases hx : x ∈ V₁
            · exact Or.inl ⟨hx, hAdj₁ e x y hl hx⟩
            · have hx₂ : x ∈ V₂ := ⟨hl.left_mem, hx⟩
              exact Or.inr ⟨hx₂, hAdj₂ e x y hl hx₂⟩
      have side : ∀ (S : Set α) (endsS : β → α × α) (lamS : Fin r → (α → K) ×
          ((v : α) → Module.Dual K (P0 v)))
          (hS : Graph.RecordsLinks (G.induce S) endsS) (hS' : Graph.RecordsLinks (G.induce S) ends),
          (∀ i, ∀ v ∈ S, (lam i).1 v = (lamS i).1 v) →
          Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := r + 1 + 1)
              (G.induce S) ends qf).toBodyHinge.rigidityRows)
            = Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := r + 1 + 1)
              (G.induce S) endsS
              (fun p => liftNormal b0 (fun i => (lamS i).1) p.1 p.2)).toBodyHinge.rigidityRows) :=
        fun S endsS lamS hS hS' hagree =>
          (finrank_ofNormals_ends hS' hS qf).trans
            (finrank_ofNormals_congr hS fun v hv => by
              simp only [liftNormal]
              congr 1
              funext i
              exact hagree i v hv)
      have e₁ := side V₁ ends₁ lam₁ hends₁ hendsA fun i v hv => by simp [lam, hv]
      have e₂ := side V₂ ends₂ lam₂ hends₂ hendsB fun i v hv => by simp [lam, hv.2]
      have hn : Graph.bodyBarDim (r + 1 + 2) = screwDim (r + 1 + 1) :=
        Graph.bodyBarDim_add_one_eq_screwDim _
      have hdef := Graph.deficiency_eq_of_cutEdges_ncard_le_one (n := r + 1 + 2) hssub
        (by rw [hC0]; simp)
      rw [hC0, Set.ncard_empty, hn, ← hV₂] at hdef
      have hVcard : V(G.induce V₁).ncard + V(G.induce V₂).ncard = V(G).ncard := by
        change V₁.ncard + V₂.ncard = _
        rw [← Set.ncard_union_eq Set.disjoint_sdiff_right (Set.toFinite V₁) (Set.toFinite V₂),
          Set.union_sdiff_cancel hV₁G]
      change (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := r + 1 + 1)
          G ends qf).toBodyHinge.rigidityRows) : ℤ) = _
      rw [hrows, e₁, e₂]
      push_cast
      rw [hrk₁, hrk₂, hdef, ← hVcard]
      push_cast
      ring

end Disconnected

end CombinatorialRigidity.Molecular
