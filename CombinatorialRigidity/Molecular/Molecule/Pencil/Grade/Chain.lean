/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Polygon
public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Cut
public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.JoinIndependence
public import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.Chain

/-!
# A cycle and a long open ear, in every dimension

The last two nodes of `sec:pencil-d-long` (`blueprint/src/chapter/pencil-d.tex`): Phase 40's cycle
and long-ear steps in dimension `m + 2`, the forms with `m` heights of `Graph.X0Attains.of_cycle`
and `Graph.X0Attains.of_openEar` (`MainComponent/Chain.lean`), on closed polygons with independent
joins (`Grade/Polygon.lean`). The placements follow the CERT workbook (S6 (C1) and S7 (a) for the
cycle, S6 (C1) with S2 (a) and S7 (b) for the ear; the bodies of `V₁` at `P₀` is S3's consumer
reading).

Each theorem is a certificate lemma (`…_of_certificate`, `…_of_cert`) and a placement. The
certificate lemma takes any `n` edges with independent joins at any picture and heights, and runs
the rest of the chapter's proof: a main picture and heights from the join-independence polynomials,
the ear rank formula, and the count against the deficiency. The placement puts the bodies on a
closed polygon and reads off the joins (`polygonCollapse`, `polygonCollapseEdge`).

The hinge form of join independence, which PD-STATE deferred to these two steps, is
`card_le_finrank_of_linearIndependent_normalsJoin`: independent joins at the edges of a family
whose hinges lie in a subspace `T` force `finrank T` at least their number, through the complement
isomorphism from the joins to the hinges.

## Main results

* `Graph.X0AttainsGrade.of_cycle`: `thm:pencil-d-cycle`.
* `Graph.X0AttainsGrade.of_openEar`: `thm:pencil-d-open-ear-long`.
* `Graph.X0AttainsGrade.of_cycle_of_certificate`, `Graph.X0AttainsGrade.of_openEar_of_cert`: the
  steps at any independent joins.
* `card_le_finrank_of_linearIndependent_normalsJoin`, `three_le_screwDim_succ`: the helpers
  (`pencilConfigPointGrade_ofPoints` is in `Grade/Carrier.lean`).
-/

@[expose] public section

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {k m : ℕ}

/-! ## The hinge form of independent joins -/

open scoped Graph

/-- **The hinge form of independent joins**: if the joins of the point pairs `p (u i)`, `p (w i)` of
a family of links `g i` are linearly independent, and the hinges of the framework at the `g i` lie
in a subspace `T`, then `Fintype.card ι ≤ finrank T`. The hinge at a link spans the line of the
panel support extensor of its ends (`span_supportExtensor_ofNormals_eq`), and the support extensor
is the image of the join under the complement isomorphism, which is linear and injective, so the
panel support extensors are independent and span a subspace of `T`. -/
theorem card_le_finrank_of_linearIndependent_normalsJoin {α β : Type*} {G : Graph α β}
    {ends : β → α × α}
    (hends : ∀ f u w, G.IsLink f u w → G.IsLink f (ends f).1 (ends f).2)
    (p : α → Fin (k + 2) → K) {ι : Type*} [Fintype ι] (u w : ι → α) (g : ι → β)
    (hg : ∀ i, G.IsLink (g i) (u i) (w i))
    (hli : LinearIndependent K (fun i => normalsJoin (p (u i)) (p (w i))))
    (T : Submodule K (ScrewSpace K k))
    (hT : ∀ i, (PanelHingeFramework.ofNormals G ends
        (fun x => p x.1 x.2)).toBodyHinge.supportExtensor (g i) ∈ T) :
    Fintype.card ι ≤ Module.finrank K T := by
  have hli' : LinearIndependent K (fun i => panelSupportExtensor (p (u i)) (p (w i))) :=
    hli.map' (complementIso (k := k) (j := 2) (by omega)).toLinearMap (LinearEquiv.ker _)
  rw [← finrank_span_eq_card hli']
  refine Submodule.finrank_mono (Submodule.span_le.mpr ?_)
  rintro _ ⟨i, rfl⟩
  have hmem : panelSupportExtensor (p (u i)) (p (w i)) ∈ Submodule.span K
      {(PanelHingeFramework.ofNormals G ends (fun x => p x.1 x.2)).toBodyHinge.supportExtensor
        (g i)} := by
    rw [span_supportExtensor_ofNormals_eq hends _ (hg i)]
    exact Submodule.mem_span_singleton_self _
  exact (Submodule.span_le.mpr (by rintro _ rfl; exact hT i)) hmem

/-! ## A cycle, in every dimension (`thm:pencil-d-cycle`) -/

variable {α β : Type*}

/-- **A cycle attains once `min (k + 2) D` of its edges have independent joins at some picture and
heights** (`thm:pencil-d-cycle`, the picture, the heights and the count): the cycle is the edge `f`
together with the open ear `a - x₁ - ⋯ - x_k - b`, `D = screwDim (m + 1)`. Every closed
neighbourhood has three members, so every height is a lifting height of the cycle
(`Graph.liftingRestrict` of the given heights, `exists_dotProduct_of_ncard_closedNbhd_le_three`),
and the join-independence polynomial times the main-picture polynomial has a non-root picture. The
ear rank formula at `{a, b}`, with the edge of rank `D - 1` and the `min (k + 2) D` independent
joins (`card_le_finrank_of_linearIndependent_normalsJoin`), gives the rank, and the partition into
single bodies gives `def ≥ k + 2 - D`. The Lean follows the chapter's count; the placement is in
`Graph.X0AttainsGrade.of_cycle`. -/
theorem _root_.Graph.X0AttainsGrade.of_cycle_of_certificate [Infinite K] [Finite α] [Finite β]
    {G : Graph α β} {k : ℕ} {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β} {f : β}
    (hk : 1 ≤ k) (hcover : V(G) = {a, b} ∪ Set.range x) (hinj : Function.Injective x)
    (hxa : ∀ i, x i ≠ a) (hxb : ∀ i, x i ≠ b) (hab : a ≠ b) (hf : G.IsLink f a b)
    (hpath : ∀ i : Fin (k + 1),
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (honly : ∀ g u w, G.IsLink g u w → (∀ i, g ≠ e i) → g = f)
    {ι : Type*} [Fintype ι] (hcard : Fintype.card ι = min (k + 2) (screwDim (m + 1)))
    (u w : ι → α) (g : ι → β) (hg : ∀ i, G.IsLink (g i) (u i) (w i))
    (q₀ : α × Fin 2 → K) (zs : α × Fin m → K)
    (hli : LinearIndependent K (fun i =>
      normalsJoin (pencilConfigPointGrade q₀ zs (u i)) (pencilConfigPointGrade q₀ zs (w i)))) :
    G.X0AttainsGrade K m := by
  have : Fintype α := Fintype.ofFinite α
  have : Inhabited α := ⟨a⟩
  have hpv := pathVertex_injective hinj hxa hxb hab
  set V₁ : Set α := {a, b} with hV₁
  have hxV₁ : ∀ i, x i ∉ V₁ := by
    intro i h
    rcases h with h | h
    exacts [hxa i h, hxb i h]
  have hsep : ∀ g u w, G.IsLink g u w → (∀ i, g ≠ e i) → u ∈ V₁ ∧ w ∈ V₁ := by
    intro g' u' w' hg' hge
    have := honly g' u' w' hg' hge
    subst this
    rcases hg'.eq_and_eq_or_eq_and_eq hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨Or.inl rfl, Or.inr rfl⟩
    · exact ⟨Or.inr rfl, Or.inl rfl⟩
  -- every closed neighbourhood has at most three members
  have hN3 : ∀ v ∈ V(G), (G.closedNbhd v).ncard ≤ 3 := by
    intro v hv
    rw [hcover] at hv
    obtain ⟨hNa, hNb⟩ := G.closedNbhd_cycle_subset hk hinj hxa hxb hab hf hpath honly
    rcases hv with (rfl | rfl) | ⟨i, rfl⟩
    · exact (Set.ncard_le_ncard hNa (Set.toFinite _)).trans ((Set.ncard_insert_le _ _).trans
        (Nat.succ_le_succ (Set.ncard_pair_le _ _)))
    · exact (Set.ncard_le_ncard hNb (Set.toFinite _)).trans ((Set.ncard_insert_le _ _).trans
        (Nat.succ_le_succ (Set.ncard_pair_le _ _)))
    · exact G.ncard_closedNbhd_ear_le_three hinj hxV₁ (Or.inl rfl) (Or.inr rfl) hpath hsep i
  -- loopless, and three members in every closed neighbourhood
  have hloop : G.Loopless := by
    refine ⟨fun g v hg => ?_⟩
    by_cases hge : ∃ i, g = e i
    · obtain ⟨i, rfl⟩ := hge
      rcases hg.eq_and_eq_or_eq_and_eq (hpath i) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have := hpv (h1.symm.trans h2)
        exact absurd (congrArg Fin.val this) (by simp)
      · have := hpv (h1.symm.trans h2)
        exact absurd (congrArg Fin.val this) (by simp)
    · have := honly g v v hg (fun i h => hge ⟨i, h⟩)
      subst this
      rcases hg.eq_and_eq_or_eq_and_eq hf with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hab (h1.symm.trans h2)
      · exact hab (h2.symm.trans h1)
  have h3 : ∀ v ∈ V(G), 3 ≤ (G.closedNbhd v).ncard := by
    intro v hv
    rw [hcover] at hv
    have hmem : ∀ {y₁ y₂ y₃ : α}, y₁ ≠ y₂ → y₁ ≠ y₃ → y₂ ≠ y₃ → y₁ ∈ G.closedNbhd v →
        y₂ ∈ G.closedNbhd v → y₃ ∈ G.closedNbhd v → 3 ≤ (G.closedNbhd v).ncard := by
      intro y₁ y₂ y₃ h12 h13 h23 m1 m2 m3
      have hsub : ({y₁, y₂, y₃} : Set α) ⊆ G.closedNbhd v := by
        rintro _ (rfl | rfl | rfl) <;> assumption
      calc 3 = ({y₁, y₂, y₃} : Set α).ncard := by
            rw [Set.ncard_eq_three.mpr ⟨y₁, y₂, y₃, h12, h13, h23, rfl⟩]
        _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
    rcases hv with (rfl | rfl) | ⟨i, rfl⟩
    · exact hmem hab (fun h => hxa _ h.symm) (fun h => hxb _ h.symm) (Or.inl rfl) (Or.inr ⟨f, hf⟩)
        (Or.inr ⟨_, ear_isLink_first hpath hk⟩)
    · exact hmem hab.symm (fun h => hxb _ h.symm) (fun h => hxa _ h.symm) (Or.inl rfl)
        (Or.inr ⟨f, hf.symm⟩) (Or.inr ⟨_, (ear_isLink_last hpath hk).symm⟩)
    · have hl1 := hpath ⟨i.val + 1, (by omega)⟩
      have hl0 := hpath ⟨i.val, (by omega)⟩
      have hxi : pathVertex a x b (Fin.castSucc ⟨i.val + 1, (by omega)⟩) = x i :=
        pathVertex_eq_of_val_eq_succ a x b (by simp)
      have hxi' : pathVertex a x b (Fin.succ ⟨i.val, (by omega)⟩) = x i :=
        pathVertex_eq_of_val_eq_succ a x b (by simp)
      rw [hxi] at hl1
      rw [hxi'] at hl0
      refine hmem (y₁ := x i) (y₂ := pathVertex a x b (Fin.succ ⟨i.val + 1, (by omega)⟩))
        (y₃ := pathVertex a x b (Fin.castSucc ⟨i.val, (by omega)⟩)) ?_ ?_ ?_ (Or.inl rfl)
        (Or.inr ⟨_, hl1⟩) (Or.inr ⟨_, hl0.symm⟩)
      · rw [← hxi]; exact fun h => absurd (congrArg Fin.val (hpv h)) (by simp)
      · rw [← hxi]; exact fun h => absurd (congrArg Fin.val (hpv h)) (by simp)
      · exact fun h => absurd (congrArg Fin.val (hpv h))
          (by simp only [Fin.val_succ, Fin.val_castSucc]; omega)
  obtain ⟨Pm, hPm, hmain⟩ := G.exists_mvPolynomial_isMainPicture (K := K) hloop h3
  obtain ⟨Plam, hPlam₀, hPlam⟩ :=
    exists_mvPolynomial_linearIndependent_join_picture_grade zs u w hli
  have hPlamne : Plam ≠ 0 := fun h => hPlam₀ (by rw [h, map_zero])
  obtain ⟨q, hq⟩ := MvPolynomial.exists_eval_ne_zero (mul_ne_zero hPm hPlamne)
  rw [map_mul] at hq
  have hqmain := hmain q (left_ne_zero_of_mul hq)
  have hliq := hPlam q (right_ne_zero_of_mul hq)
  set ends := G.endsOf with hendsdef
  have hends : ∀ f u w, G.IsLink f u w → G.IsLink f (ends f).1 (ends f).2 :=
    fun f _ _ hf => G.isLink_endsOf hf.edge_mem
  -- every height on `V(G)` is a lifting height of the cycle, height by height
  set z := Graph.liftingRestrict (Prod.fst ⁻¹' V(G)) zs with hzdef
  have hz : z ∈ G.liftingSpaceGrade q m := by
    refine Graph.mem_liftingSpaceGrade.2 fun i => ⟨fun w hw => ?_, fun v hv => ?_⟩
    · simp [hzdef, Graph.liftingRestrict_apply, hw]
    · exact hqmain.1.exists_dotProduct_of_ncard_closedNbhd_le_three hv (hN3 v hv) _
  have hliz : LinearIndependent K (fun i =>
      normalsJoin (pencilConfigPointGrade q z (u i)) (pencilConfigPointGrade q z (w i))) := by
    have heq : ∀ y ∈ V(G), pencilConfigPointGrade q z y = pencilConfigPointGrade q zs y :=
      fun y hy => pencilConfigPointGrade_liftingRestrict V(G) q zs hy
    have hfun : (fun i =>
        normalsJoin (pencilConfigPointGrade q z (u i)) (pencilConfigPointGrade q z (w i))) =
        fun i => normalsJoin (pencilConfigPointGrade q zs (u i))
          (pencilConfigPointGrade q zs (w i)) := by
      funext i
      rw [heq _ (hg i).left_mem, heq _ (hg i).right_mem]
    rw [hfun]; exact hliq
  -- the ear rank formula at `V₁ = {a, b}`
  set F := (PanelHingeFramework.ofNormals (k := m + 1) G ends
    (fun p => pencilConfigPointGrade q z p.1 p.2)).toBodyHinge with hFdef
  have hC : ∀ i, F.supportExtensor (e i) ≠ 0 :=
    fun i => hqmain.1.supportExtensor_ne_zero_grade hends z (hpath i)
  have hear := BodyHingeFramework.finrank_span_rigidityRows_ear_eq F hinj hxV₁ (Or.inl rfl)
    (Or.inr rfl) hab hpath hsep hC
  -- the edge side: a one-hinge path
  set P := G.induce V₁ with hPdef
  have hpathP : ∀ i : Fin (0 + 1), P.IsLink ((fun _ => f) i)
      (pathVertex a (Fin.elim0 : Fin 0 → α) b i.castSucc)
      (pathVertex a (Fin.elim0 : Fin 0 → α) b i.succ) := by
    intro i
    have hi : i = 0 := Fin.ext (by have := i.isLt; omega)
    subst hi
    have h0 : pathVertex a (Fin.elim0 : Fin 0 → α) b (Fin.castSucc (0 : Fin (0 + 1))) = a :=
      pathVertex_zero _ _ _
    have h1 : pathVertex a (Fin.elim0 : Fin 0 → α) b (Fin.succ (0 : Fin (0 + 1))) = b :=
      pathVertex_last _ _ _
    rw [h0, h1]
    exact ⟨hf, Or.inl rfl, Or.inr rfl⟩
  have honlyP : ∀ g u w, P.IsLink g u w → ∃ i : Fin (0 + 1), g = (fun _ => f) i := by
    rintro g' u' w' ⟨hg', hu', hw'⟩
    refine ⟨0, honly g' u' w' hg' (fun i hi => ?_)⟩
    subst hi
    rcases hg'.eq_and_eq_or_eq_and_eq (hpath i) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases pathVertex_cases a x b i.succ with ⟨h0, -⟩ | ⟨j, -, hj⟩ | ⟨h0, -⟩
      · simp only [Fin.val_succ] at h0; omega
      · rw [hj] at h2; exact hxV₁ j (h2 ▸ hw')
      · rcases pathVertex_cases a x b i.castSucc with ⟨h0', -⟩ | ⟨j, -, hj⟩ | ⟨h0', -⟩
        · simp only [Fin.val_succ, Fin.val_castSucc] at h0 h0'; omega
        · rw [hj] at h1; exact hxV₁ j (h1 ▸ hu')
        · simp only [Fin.val_castSucc] at h0'; omega
    · rcases pathVertex_cases a x b i.succ with ⟨h0, -⟩ | ⟨j, -, hj⟩ | ⟨h0, -⟩
      · simp only [Fin.val_succ] at h0; omega
      · rw [hj] at h1; exact hxV₁ j (h1 ▸ hu')
      · rcases pathVertex_cases a x b i.castSucc with ⟨h0', -⟩ | ⟨j, -, hj⟩ | ⟨h0', -⟩
        · simp only [Fin.val_succ, Fin.val_castSucc] at h0 h0'; omega
        · rw [hj] at h2; exact hxV₁ j (h2 ▸ hw')
        · simp only [Fin.val_castSucc] at h0'; omega
  have hCf : F.supportExtensor f ≠ 0 := hqmain.1.supportExtensor_ne_zero_grade hends z hf
  have hFV₁ : F.graph.induce V₁ = P := by
    rw [hFdef, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph, ← hPdef]
  have hrankP : Module.finrank K (Submodule.span K
      (⟨F.graph.induce V₁, F.supportExtensor⟩ : BodyHingeFramework K (m + 1) α β).rigidityRows)
      = screwDim (m + 1) - 1 := by
    rw [hFV₁]
    have h1 := BodyHingeFramework.finrank_span_rigidityRows_path_le P F.supportExtensor hpathP
      honlyP (fun _ => hCf)
    have h2 := BodyHingeFramework.le_finrank_span_rigidityRows_path P F.supportExtensor
      (x := (Fin.elim0 : Fin 0 → α)) (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0) hab
      hpathP honlyP (fun _ => hCf)
    rw [zero_add, mul_one] at h1 h2
    exact le_antisymm h1 h2
  have hrelP : (⟨F.graph.induce V₁, F.supportExtensor⟩ :
      BodyHingeFramework K (m + 1) α β).relScrews a b = Submodule.span K {F.supportExtensor f} := by
    rw [hFV₁]
    have hpvP := pathVertex_injective (x := (Fin.elim0 : Fin 0 → α)) (fun i => i.elim0)
      (fun i => i.elim0) (fun i => i.elim0) hab
    rw [le_antisymm (BodyHingeFramework.relScrews_path_le_span_range P F.supportExtensor hpathP)
      (BodyHingeFramework.span_range_le_relScrews_path P F.supportExtensor hpvP hpathP honlyP)]
    congr 1
    ext y
    simp [eq_comm]
  rw [hrankP, hrelP] at hear
  -- the span of all hinges has dimension at least `min (k + 2) D`
  have hdim := card_le_finrank_of_linearIndependent_normalsJoin hends (pencilConfigPointGrade q z)
    u w g hg hliz (Submodule.span K {F.supportExtensor f}
      ⊔ Submodule.span K (Set.range (F.supportExtensor ∘ e))) (by
      intro i
      by_cases hge : ∃ j, g i = e j
      · obtain ⟨j, hj⟩ := hge
        rw [hj]
        exact Submodule.mem_sup_right (Submodule.subset_span ⟨j, rfl⟩)
      · rw [honly _ _ _ (hg i) (fun j h => hge ⟨j, h⟩)]
        exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _))
  rw [hcard] at hdim
  -- the deficiency: the partition into singletons
  have hVcard : V(G).ncard = k + 2 := by
    rw [hcover, Set.ncard_union_eq _ (Set.toFinite _) (Set.toFinite _), Set.ncard_pair hab,
      Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]
    · ring
    · refine Set.disjoint_left.mpr ?_
      rintro _ (rfl | rfl) ⟨i, hi⟩
      exacts [hxa i hi, hxb i hi]
  have hE : E(G) ⊆ insert f (Set.range e) := by
    intro g' hg'
    obtain ⟨u', w', hl⟩ := G.exists_isLink_of_mem_edgeSet hg'
    by_cases hge : ∃ j, g' = e j
    · obtain ⟨j, rfl⟩ := hge; exact Or.inr ⟨j, rfl⟩
    · exact Or.inl (honly _ _ _ hl (fun j h => hge ⟨j, h⟩))
  have hre : (Set.range e).ncard ≤ k + 1 := (Set.ncard_range_le e).trans (by simp)
  have hEcard : E(G).ncard ≤ k + 2 :=
    (Set.ncard_le_ncard hE (Set.toFinite _)).trans ((Set.ncard_insert_le _ _).trans
      (by omega))
  have hbb : (Graph.bodyBarDim (m + 2) : ℤ) = screwDim (m + 1) := by
    exact_mod_cast Graph.bodyBarDim_add_one_eq_screwDim (m + 1)
  have hdef0 : (0 : ℤ) ≤ G.deficiency (m + 2) :=
    G.deficiency_nonneg (m + 2) ⟨a, hcover ▸ Or.inl (Or.inl rfl)⟩
  have hdef1 : (k : ℤ) + 2 - screwDim (m + 1) ≤ G.deficiency (m + 2) := by
    have hp := G.partitionDef_le_deficiency (m + 2) id
    have hnp : G.numParts id = k + 2 := by rw [Graph.numParts, Set.image_id, hVcard]
    have hce : (G.crossingEdges id).ncard ≤ k + 2 :=
      (Set.ncard_le_ncard (fun g' (hg' : g' ∈ G.crossingEdges id) => hg'.1)
        (Set.toFinite _)).trans hEcard
    rw [Graph.partitionDef, hnp, hbb] at hp
    have hce' : ((G.crossingEdges id).ncard : ℤ) ≤ k + 2 := by exact_mod_cast hce
    have hD1 : (1 : ℤ) ≤ screwDim (m + 1) := by exact_mod_cast one_le_screwDim
    push_cast at hp
    nlinarith
  refine Graph.x0AttainsGrade_of_exists ⟨a, hcover ▸ Or.inl (Or.inl rfl)⟩ ends hends hqmain hz ?_
  have e1 : (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
      = ((screwDim (m + 1) - 1 : ℕ) : ℤ) + ((screwDim (m + 1) : ℤ) - 1) * (k + 1)
        + (Module.finrank K ↥(Submodule.span K {F.supportExtensor f}
            ⊔ Submodule.span K (Set.range (F.supportExtensor ∘ e))) : ℤ)
        - (screwDim (m + 1) : ℤ) := hear
  rw [e1, hVcard]
  push_cast [Nat.cast_sub one_le_screwDim]
  have hdim' : (min (k + 2) (screwDim (m + 1)) : ℕ) ≤ Module.finrank K ↥(Submodule.span K
      {F.supportExtensor f} ⊔ Submodule.span K (Set.range (F.supportExtensor ∘ e))) := hdim
  rcases le_total (k + 2) (screwDim (m + 1)) with hkD | hkD
  · rw [min_eq_left hkD] at hdim'
    have : ((k + 2 : ℕ) : ℤ) ≤ (Module.finrank K ↥(Submodule.span K {F.supportExtensor f}
      ⊔ Submodule.span K (Set.range (F.supportExtensor ∘ e))) : ℤ) := by exact_mod_cast hdim'
    push_cast at this
    linarith
  · rw [min_eq_right hkD] at hdim'
    have : ((screwDim (m + 1) : ℕ) : ℤ) ≤ (Module.finrank K ↥(Submodule.span K
      {F.supportExtensor f} ⊔ Submodule.span K (Set.range (F.supportExtensor ∘ e))) : ℤ) := by
      exact_mod_cast hdim'
    linarith

/-- **`D ≥ 3` in every dimension**: `screwDim (m + 1) = C(m + 3, 2) ≥ C(3, 2) = 3`. -/
theorem three_le_screwDim_succ : 3 ≤ screwDim (m + 1) :=
  (Nat.choose_le_choose 2 (by omega : 3 ≤ m + 1 + 2)).trans' (by decide)

/-- **A cycle attains, in every dimension** (`thm:pencil-d-cycle`, CERT S6 (C1) and S7 (a)): a
cycle on `k + 2` bodies, the open ear `a - x₁ - ⋯ - x_k - b` and one edge `ab`, attains at `m`
heights over an infinite field. The placement puts a closed `N`-gon with independent joins,
`N = min (k + 2) D`, under the bodies: `c j` at the vertex `polygonCollapse N (k + 2) j`, the
identity when `N = k + 2` (`m ≤ D` in the chapter's `m = k + 2`) and the collapse otherwise
(part (1) of `lem:pencil-d-polygon-collapse`). `polygonCollapseEdge` then picks `N` distinct
cyclic edges carrying `J₀, …, J_{N-1}`, and the certificate lemma does the rest. -/
theorem _root_.Graph.X0AttainsGrade.of_cycle [Infinite K] [Finite α] [Finite β]
    {G : Graph α β} {k : ℕ} {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β} {f : β}
    (hk : 1 ≤ k) (hcover : V(G) = {a, b} ∪ Set.range x) (hinj : Function.Injective x)
    (hxa : ∀ i, x i ≠ a) (hxb : ∀ i, x i ≠ b) (hab : a ≠ b) (hf : G.IsLink f a b)
    (hpath : ∀ i : Fin (k + 1),
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (honly : ∀ g u w, G.IsLink g u w → (∀ i, g ≠ e i) → g = f) :
    G.X0AttainsGrade K m := by
  classical
  set N := min (k + 2) (screwDim (m + 1)) with hNdef
  have hN3 : 3 ≤ N := le_min (by omega) three_le_screwDim_succ
  have : NeZero N := ⟨by omega⟩
  have hK4 : 4 ≤ ENat.card K := by rw [ENat.card_eq_top_of_infinite]; exact le_top
  obtain ⟨Y, hY1, hY, -, -, -⟩ :=
    exists_polygon_linearIndependent_join (m := m) hK4 hN3 (min_le_right _ _)
  have hpv := pathVertex_injective hinj hxa hxb hab
  set c := pathVertex a x b with hc
  -- the placement: the body `c j` at the vertex `π j`
  set pt : α → Fin (m + 1 + 2) → K :=
    Function.extend c (fun j => Y (polygonCollapse N (k + 2) j)) (fun _ => gradeMk 0 0 0 1)
    with hptdef
  have hpt : ∀ j, pt (c j) = Y (polygonCollapse N (k + 2) j) := fun j => hpv.extend_apply _ _ _
  have hpt1 : ∀ w, pt w (Fin.last (m + 2)) = 1 := by
    intro w
    by_cases hw : ∃ j, c j = w
    · obtain ⟨j, rfl⟩ := hw; rw [hpt]; exact hY1 _
    · rw [hptdef, Function.extend_apply' _ _ _ hw]; simp
  -- the edges of the cycle in cyclic order: `e j` from `c j` to `c (j + 1)`, then `f` from `b`
  set g' : Fin (k + 2) → β := fun j => if h : (j : ℕ) < k + 1 then e ⟨j, h⟩ else f with hg'
  have hcyc : ∀ j : Fin (k + 2), G.IsLink (g' j) (c j) (c (j + 1)) := by
    intro j
    by_cases h : (j : ℕ) < k + 1
    · have e1 : (⟨j, h⟩ : Fin (k + 1)).castSucc = j := Fin.ext rfl
      have e2 : (⟨j, h⟩ : Fin (k + 1)).succ = j + 1 := by
        rw [Fin.ext_iff, Fin.val_add_one']; simp; omega
      have hgj : g' j = e ⟨j, h⟩ := dite_eq_left h
      have := hpath ⟨j, h⟩
      rw [e1, e2] at this
      rwa [hgj]
    · have hj : j = Fin.last (k + 1) := Fin.ext (by have := j.isLt; simp; omega)
      subst hj
      simpa [hg', hc, pathVertex_last, pathVertex_zero] using hf.symm
  refine Graph.X0AttainsGrade.of_cycle_of_certificate hk hcover hinj hxa hxb hab hf hpath honly
    (ι := Fin N) (by rw [Fintype.card_fin])
    (fun l => c (polygonCollapseEdge N (k + 2) l))
    (fun l => c (polygonCollapseEdge N (k + 2) l + 1))
    (fun l => g' (polygonCollapseEdge N (k + 2) l)) (fun l => hcyc _)
    (fun p => ![pt p.1 0, pt p.1 1] p.2) (fun p => gradeHeights (pt p.1) p.2) ?_
  simp only [pencilConfigPointGrade_ofPoints pt hpt1, hpt]
  convert hY using 2 with l
  obtain ⟨h1, h2⟩ := polygonCollapse_polygonCollapseEdge (by omega) (min_le_left _ _) l
  rw [h1, h2]

/-! ## An open ear with `D − 1` or more interior bodies (`thm:pencil-d-open-ear-long`) -/

/-- **An open ear attains once `n` of its edges have independent joins, at heights that are
lifting heights** (`thm:pencil-d-open-ear-long`, the picture, the heights and the count): `G[V₁]`
attains, the heights `zs` are lifting heights of `G` at every admissible picture, and the joins of
the `n` ear edges are independent at `(q₀, zs)` and `k + 1 + def(G[V₁]) ≤ n + def(G)`. The picture
is a non-root of the attainment polynomial of `G[V₁]`, the main-picture polynomial and the
join-independence polynomial; the heights are a common non-root of the lift of `G[V₁]`'s
polynomial (`Graph.exists_liftingRestrict_preimage_fst_eq`, height by height) and the
join-independence polynomial in the heights; the ear rank formula and the `n` independent hinges
give the rank. -/
theorem _root_.Graph.X0AttainsGrade.of_openEar_of_cert [Infinite K] [Finite α] [Finite β]
    {G : Graph α β} (hG : G.IsX0Graph) {V₁ : Set α} {k : ℕ} {x : Fin k → α} {a b : α}
    {e : Fin (k + 1) → β} (hk : 2 ≤ k) (hcover : V(G) = V₁ ∪ Set.range x)
    (hinj : Function.Injective x) (hxV₁ : ∀ i, x i ∉ V₁) (ha : a ∈ V₁) (hb : b ∈ V₁)
    (hab : a ≠ b)
    (hpath : ∀ i : Fin (k + 1),
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (hsep : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁)
    (h₁ : (G.induce V₁).X0AttainsGrade K m) {n : ℕ} (u v : Fin n → α) (j : Fin n → Fin (k + 1))
    (hl : ∀ i, G.IsLink (e (j i)) (u i) (v i)) (q₀ : α × Fin 2 → K) (zs : α × Fin m → K)
    (hcert : LinearIndependent K (fun i =>
      normalsJoin (pencilConfigPointGrade q₀ zs (u i)) (pencilConfigPointGrade q₀ zs (v i))))
    (hzs : ∀ q, G.IsAdmissiblePicture q → zs ∈ G.liftingSpaceGrade q m)
    (hcount : (k : ℤ) + 1 + (G.induce V₁).deficiency (m + 2) ≤ n + G.deficiency (m + 2)) :
    G.X0AttainsGrade K m := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have hV : V(G).Nonempty := hG.connected.nonempty
  have : Inhabited α := ⟨a⟩
  have hle₁ : G.induce V₁ ≤ G := Graph.induce_le (hcover ▸ Set.subset_union_left)
  obtain ⟨ends₁, P₁, hends₁, hP₁, hgood₁⟩ := h₁
  obtain ⟨Pm, hPm, hmain⟩ := G.exists_mvPolynomial_isMainPicture (K := K)
    hG.simple.toLoopless hG.three_le_ncard_closedNbhd
  set ends := G.endsOf
  have hends : ∀ f u w, G.IsLink f u w → G.IsLink f (ends f).1 (ends f).2 :=
    fun f _ _ hf => G.isLink_endsOf hf.edge_mem
  have hendsG := PanelHingeFramework.recordsLinks_iff_forall_isLink.mpr hends
  -- the picture: generic for `G[V₁]`, main for `G`, the joins independent at `zs`
  obtain ⟨Plam, hPlam₀, hPlam⟩ :=
    exists_mvPolynomial_linearIndependent_join_picture_grade zs u v hcert
  have hPlamne : Plam ≠ 0 := fun h => hPlam₀ (by rw [h, map_zero])
  obtain ⟨q, hq⟩ := MvPolynomial.exists_eval_ne_zero (mul_ne_zero (mul_ne_zero hP₁ hPm) hPlamne)
  rw [map_mul, map_mul] at hq
  obtain ⟨-, R₁, ⟨z₁, hz₁, hR₁⟩, hatt₁⟩ := hgood₁ q (left_ne_zero_of_mul (left_ne_zero_of_mul hq))
  have hqmain := hmain q (right_ne_zero_of_mul (left_ne_zero_of_mul hq))
  have hliq := hPlam q (right_ne_zero_of_mul hq)
  obtain ⟨Rlam, hRlam₀, hRlam⟩ :=
    exists_mvPolynomial_linearIndependent_join_heights_grade q u v hliq
  -- heights on which `G[V₁]` attains and the joins stay independent, height by height
  have hex₁ : ∃ z ∈ G.liftingSpaceGrade q m,
      MvPolynomial.eval z (restrictPoly (Prod.fst ⁻¹' V₁) R₁) ≠ 0 := by
    obtain ⟨z, hz, hzr⟩ := Graph.exists_liftingRestrict_preimage_fst_eq (fun y hy => by
      obtain ⟨z, hz, hzr, -⟩ := G.earExtend_mem_liftingSpace hk hcover hinj hxV₁ ha hb hab
        hpath hsep hqmain.1 hy 0
      exact ⟨z, hz, hzr⟩) hz₁
    exact ⟨z, hz, by rwa [eval_restrictPoly, hzr]⟩
  obtain ⟨z, hz, hz₁', hzlam⟩ :=
    MvPolynomial.exists_mem_eval_ne_zero₂ hex₁ ⟨zs, hzs q hqmain.1, hRlam₀⟩
  rw [eval_restrictPoly] at hz₁'
  have hr₁ := hatt₁ _ (Graph.liftingRestrict_mem_liftingSpaceGrade hle₁ hz) hz₁'
  have hli := hRlam z hzlam
  rw [PanelHingeFramework.finrank_span_rigidityRows_ofNormals_liftingRestrict_grade
    (X := V(G.induce V₁)) subset_rfl hends₁
    (PanelHingeFramework.recordsLinks_iff_forall_isLink.mp (hendsG.induce V₁)),
    Graph.vertexSet_induce G V₁] at hr₁
  -- the ear rank formula at `ofNormals G ends`, with `n` independent ear hinges
  set F := (PanelHingeFramework.ofNormals (k := m + 1) G ends
    (fun p => pencilConfigPointGrade q z p.1 p.2)).toBodyHinge
  have hC : ∀ i, F.supportExtensor (e i) ≠ 0 :=
    fun i => hqmain.1.supportExtensor_ne_zero_grade hends z (hpath i)
  have hear := BodyHingeFramework.finrank_span_rigidityRows_ear_eq F hinj hxV₁ ha hb hab hpath
    hsep hC
  have hdim := card_le_finrank_of_linearIndependent_normalsJoin hends (pencilConfigPointGrade q z)
    u v (e ∘ j) hl hli ((⟨F.graph.induce V₁, F.supportExtensor⟩ :
      BodyHingeFramework K (m + 1) α β).relScrews a b
        ⊔ Submodule.span K (Set.range (F.supportExtensor ∘ e)))
    (fun i => Submodule.mem_sup_right (Submodule.subset_span ⟨j i, rfl⟩))
  rw [Fintype.card_fin] at hdim
  -- the body count
  have hcard : (V(G).ncard : ℤ) = V₁.ncard + k := by
    rw [hcover]; exact_mod_cast Set.ncard_union_range_of_injective hinj hxV₁
  refine Graph.x0AttainsGrade_of_exists hV ends hends hqmain hz ?_
  have e1 : (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
      = (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := m + 1)
          (G.induce V₁) ends (fun p => pencilConfigPointGrade q z p.1 p.2)
            ).toBodyHinge.rigidityRows) : ℤ)
        + ((screwDim (m + 1) : ℤ) - 1) * (k + 1)
        + (Module.finrank K ↥((⟨F.graph.induce V₁, F.supportExtensor⟩ :
              BodyHingeFramework K (m + 1) α β).relScrews a b
            ⊔ Submodule.span K (Set.range (F.supportExtensor ∘ e))) : ℤ)
        - (screwDim (m + 1) : ℤ) := hear
  rw [e1, hr₁, hcard]
  have hdim' : (n : ℤ) ≤ (Module.finrank K ↥((⟨F.graph.induce V₁, F.supportExtensor⟩ :
      BodyHingeFramework K (m + 1) α β).relScrews a b
        ⊔ Submodule.span K (Set.range (F.supportExtensor ∘ e))) : ℤ) := by exact_mod_cast hdim
  linarith

/-- **A long open ear attains, in every dimension** (`thm:pencil-d-open-ear-long`, CERT S6 (C1)
with S2 (a) and S7 (b)): an open ear with `k ≥ D - 1` interior bodies on `V₁`, over an infinite
field, passes attainment of `G[V₁]` to `G`. The placement puts the normalized `D`-gon `Y` under the
ear (part (2) of `lem:pencil-d-polygon-collapse`): `x i` at `Y (polygonCollapse D (k + 1) (i + 1))`
and every other body at `P₀`, so `a` and `b` are at `Y 0`, and every height vanishes on `V₁`, on
`x 0` (at `P₂`) and on `x (k - 1)` (at `P₁`), hence is a lifting height of `G`
(`Graph.mem_liftingSpace_of_ear`). The `D` ear edges carry `J₀, …, J_{D-1}`, and the
deficiency count is `Graph.deficiency_induce_add_le_of_ear` at `D`. -/
theorem _root_.Graph.X0AttainsGrade.of_openEar [Infinite K] [Finite α] [Finite β]
    {G : Graph α β} (hG : G.IsX0Graph) {V₁ : Set α} {k : ℕ} {x : Fin k → α} {a b : α}
    {e : Fin (k + 1) → β} (hk : screwDim (m + 1) - 1 ≤ k) (hcover : V(G) = V₁ ∪ Set.range x)
    (hinj : Function.Injective x) (hxV₁ : ∀ i, x i ∉ V₁) (ha : a ∈ V₁) (hb : b ∈ V₁)
    (hab : a ≠ b)
    (hpath : ∀ i : Fin (k + 1),
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (hsep : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁)
    (h₁ : (G.induce V₁).X0AttainsGrade K m) : G.X0AttainsGrade K m := by
  classical
  set D := screwDim (m + 1) with hDdef
  have hD3 : 3 ≤ D := three_le_screwDim_succ
  have : NeZero D := ⟨by omega⟩
  have hk2 : 2 ≤ k := by omega
  have hK4 : 4 ≤ ENat.card K := by rw [ENat.card_eq_top_of_infinite]; exact le_top
  obtain ⟨Y, hY1, hY, hYl, hY0, hY1'⟩ :=
    exists_polygon_linearIndependent_join (m := m) (n := D) hK4 hD3 le_rfl
  -- the placement: `x i` at `π (i + 1)`, every other body at `Y 0 = P₀`
  set π := polygonCollapse D (k + 1) with hπ
  set pt : α → Fin (m + 1 + 2) → K :=
    Function.extend x (fun i => Y (π i.succ)) (fun _ => Y 0) with hptdef
  have hptx : ∀ i, pt (x i) = Y (π i.succ) := fun i => hinj.extend_apply _ _ _
  have hptn : ∀ w, w ∉ Set.range x → pt w = Y 0 := fun w hw => by
    rw [hptdef, Function.extend_apply' _ _ _ (by simpa using hw)]
  have hpt1 : ∀ w, pt w (Fin.last (m + 2)) = 1 := by
    intro w
    by_cases hw : w ∈ Set.range x
    · obtain ⟨i, rfl⟩ := hw; rw [hptx]; exact hY1 _
    · rw [hptn w hw]; exact hY1 _
  have hπ0 : π 0 = 0 := polygonCollapse_zero (by omega)
  have hpv : ∀ j : Fin (k + 2),
      pt (pathVertex a x b j) = Y (π ⟨j % (k + 1), Nat.mod_lt _ (by omega)⟩) := by
    intro j
    rcases pathVertex_cases a x b j with ⟨h0, hj⟩ | ⟨i, hi, hj⟩ | ⟨hl, hj⟩
    · rw [hj, hptn a (fun ⟨i, hi⟩ => hxV₁ i (hi ▸ ha)), ← hπ0]
      congr 2; ext; simp [h0]
    · rw [hj, hptx]
      congr 2; ext; simp only [Fin.val_succ, hi]
      rw [Nat.mod_eq_of_lt (show (i : ℕ) + 1 < k + 1 by omega)]
    · rw [hj, hptn b (fun ⟨i, hi⟩ => hxV₁ i (hi ▸ hb)), ← hπ0]
      congr 2; ext; simp [hl]
  have hcs : ∀ i : Fin (k + 1), pt (pathVertex a x b i.castSucc) = Y (π i) := by
    intro i; rw [hpv]; congr 2; ext; simp only [Fin.val_castSucc]
    exact Nat.mod_eq_of_lt i.isLt
  have hsu : ∀ i : Fin (k + 1), pt (pathVertex a x b i.succ) = Y (π (i + 1)) := by
    intro i; rw [hpv]; congr 2; ext; simp only [Fin.val_succ]; rw [Fin.val_add_one']
    have := i.isLt
    split_ifs with h
    · rw [h, Nat.mod_self]
    · exact Nat.mod_eq_of_lt (by omega)
  -- every height vanishes on `V₁`, at `x 0` and at `x (k - 1)`
  have hP : ∀ w, w ∉ Set.range x ∨ w = x ⟨0, by omega⟩ ∨ w = x ⟨k - 1, by omega⟩ →
      gradeHeights (pt w) = 0 := by
    rintro w (hw | rfl | rfl)
    · rw [hptn w hw, hY0, gradeHeights_gradeMk]
    · rw [hptx]
      have : π (Fin.succ ⟨0, by omega⟩) = 1 := by
        rw [show (Fin.succ ⟨0, by omega⟩ : Fin (k + 1)) = 1 from Fin.ext (by
          rw [Fin.val_succ, Fin.val_one', Nat.mod_eq_of_lt (by omega)])]
        exact polygonCollapse_one hD3 (by omega)
      rw [this, hY1', gradeHeights_gradeMk]
    · rw [hptx]
      have : π (Fin.succ ⟨k - 1, by omega⟩) = -1 := by
        rw [show (Fin.succ ⟨k - 1, by omega⟩ : Fin (k + 1)) = -1 from Fin.ext (by
          rw [Fin.val_succ, val_neg_one_fin]; simp; omega)]
        exact polygonCollapse_neg_one
      rw [this, hYl, gradeHeights_gradeMk]
  refine Graph.X0AttainsGrade.of_openEar_of_cert hG hk2 hcover hinj hxV₁ ha hb hab hpath hsep h₁
    (n := D) (fun l => pathVertex a x b (polygonCollapseEdge D (k + 1) l).castSucc)
    (fun l => pathVertex a x b (polygonCollapseEdge D (k + 1) l).succ)
    (polygonCollapseEdge D (k + 1)) (fun l => hpath _)
    (fun p => ![pt p.1 0, pt p.1 1] p.2) (fun p => gradeHeights (pt p.1) p.2) ?_ ?_ ?_
  · simp only [pencilConfigPointGrade_ofPoints pt hpt1, hcs, hsu]
    convert hY using 2 with l
    obtain ⟨h1, h2⟩ := polygonCollapse_polygonCollapseEdge (N := D) (M := k + 1) (by omega)
      (by omega) l
    rw [hπ, h1, h2]
  · intro q hq
    refine Graph.mem_liftingSpaceGrade.2 fun i => ?_
    refine G.mem_liftingSpace_of_ear hcover hinj hxV₁ ha hb hpath hsep hq (fun w hw => ?_)
      (fun v hv => ⟨0, fun w hw => ?_⟩)
    · have : w ∉ Set.range x := fun h => hw (hcover ▸ Or.inr h)
      simp [hP w (Or.inl this)]
    · rw [zero_dotProduct]
      rcases G.mem_closedNbhd_induce_of_ear (by omega) hxV₁ ha hb hpath hsep hv hw with
        hw' | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · have hwV : w ∈ V₁ := Graph.closedNbhd_subset_vertexSet hv hw'
        have : w ∉ Set.range x := fun ⟨i, hi⟩ => hxV₁ i (hi ▸ hwV)
        simp [hP w (Or.inl this)]
      · simp [hP _ (Or.inr (Or.inl rfl))]
      · simp [hP _ (Or.inr (Or.inr rfl))]
  · have hdef := Graph.deficiency_induce_add_le_of_ear (n := m + 2)
      (by rw [Graph.bodyBarDim_add_one_eq_screwDim]; omega) (by omega) hcover hinj hxV₁ ha hb
      hpath hsep
    have hbb : (Graph.bodyBarDim (m + 2) : ℤ) = D := by
      exact_mod_cast Graph.bodyBarDim_add_one_eq_screwDim (m + 1)
    rw [hbb] at hdef
    linarith

end CombinatorialRigidity.Molecular
