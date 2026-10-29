/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Mathlib.Basic.Countable.Defs
public import CombinatorialRigidity.Molecular.AlgebraicInduction.GenericityDevice
public import CombinatorialRigidity.Molecular.Induction.ForestSurgery.Reduction
public import CombinatorialRigidity.Molecular.RigidityMatrix.Bricks

/-!
# Case II: putting back a vertex of degree two

Lemmas for Case II of KT Theorem 5.5 (Katoh and Tanigawa 2011, *A proof of the molecular
conjecture*, Discrete Comput. Geom. **45**, §6.3), presented in
`sec:molecular-algebraic-induction-caseII`. The file proves:

* the count of KT eq. (6.12) (`lem:case-II-realization-placement`, in
  `sec:molecular-algebraic-induction-relative`): putting back a vertex `v` of degree two at the
  normal `q(a) + t q(b)`, a realization of the split-off `G_v^{ab}` of rank `N` gives a realization
  of `G` with nondegenerate hinges and rank at least `N + D − 1`; at a rigid realization this is
  one row short of the target rank;
* KT Lemma 6.8 (`lem:case-II-realization`): a 2-edge-connected minimal `k`-dof-graph with `k > 0`,
  at least three vertices and no proper rigid subgraph has a generic full-rank realization.
-/

@[expose] public section

namespace CombinatorialRigidity.Molecular

variable {k : ℕ}
variable {K : Type*} [Field K]

open scoped Graph

variable {α β : Type*}

/-- **The count of KT eq. (6.12)** (`lem:case-II-realization-placement`, second pin; KT Lemma 6.8,
pp. 677–679): let `v` have the edges `e_a` and `e_b` to `a ≠ v` and `b ≠ v` and no others (`hclv`),
let the label `e₀ ∉ E(G − v)` name the new edge `ab` of `G_v^{ab} = G.splitOff v a b e₀`, and let
`ends` and `endsv` record the links of `G` and of `G_v^{ab}`. Let `(G_v^{ab}, q)` have nondegenerate
hinges (`hne`) and rank at least `N` (`hN`), let `t ≠ 0`, and let `q₀` be `q` with the normal
`q(a) + t q(b)` at `v`. Then the hinges of `(G, q₀)` are nondegenerate, and `R(G, q₀)` has rank at
least `N + D − 1`.

The proof. The hinge `C = C(q(a), q(b))` of `ab` is nonzero. As `v` lies on no edge of `G_v^{ab}`,
the normal `q₀(v)` changes neither its hinges nor its motions, nor so its rank
(`toBodyHinge_withNormal_infinitesimalMotions_eq`,
`span_rigidityRows_eq_of_infinitesimalMotions_eq`), and some `N` of its rows at `q₀` are linearly
independent (`exists_independent_panelRow_subfamily_of_le_finrank`). At `q₀` the hinge of `vb` is
`±C` (`panelSupportExtensor_add_smul_right`) and that of `va` is `±t C`
(`panelSupportExtensor_add_smul_left`). Every row of `G_v^{ab}` lies in the row space of `R(G, q₀)`:
at an edge `e ≠ e₀` it is a row of `R(G, q₀)`, as `e` has there the same hinge up to sign, and at
`ab` it is `hingeRow a v ρ + hingeRow v b ρ` (`hingeRow_sub_hingeRow_eq`), with `ρ` vanishing on `C`
and so on the hinges of `va` and `vb`: KT's column operation (eqs. (6.14)–(6.16)) as a row
operation. These rows vanish on the screw assignments that vanish off `v`, where some `D − 1` rows
of `vb` stay linearly independent (`exists_independent_panelRow_subfamily_of_edge`,
`linearIndependent_panelRow_comp_single_of_edge`), so the rank adds
(`le_finrank_span_rigidityRows_of_pinned_placement`). Every other edge of `G` avoids `v` and is an
edge of `G_v^{ab}`, with the same hinge up to sign; with `t ≠ 0`, every hinge of `(G, q₀)` is
nonzero. -/
theorem PanelHingeFramework.case_II_placement_rank [DecidableEq α] [Finite α] [Finite β]
    (G : Graph α β) {v a b : α} {e_a e_b e₀ : β}
    (hav : a ≠ v) (hbv : b ≠ v) (hG_ea : G.IsLink e_a v a) (hG_eb : G.IsLink e_b v b)
    (hclv : ∀ e x, G.IsLink e v x → e = e_a ∨ e = e_b)
    (he₀ : e₀ ∉ E(G.removeVertex v))
    (ends : β → α × α) (hlinks : RecordsLinks G ends)
    (endsv : β → α × α) (hlinksv : RecordsLinks (G.splitOff v a b e₀) endsv)
    {q : α × Fin (k + 2) → K}
    (hne : ∀ e, (G.splitOff v a b e₀).IsLink e (endsv e).1 (endsv e).2 →
      (PanelHingeFramework.ofNormals (G.splitOff v a b e₀) endsv q).toBodyHinge.supportExtensor e
        ≠ 0)
    {N : ℕ} (hN : N ≤ Module.finrank K (Submodule.span K
      (PanelHingeFramework.ofNormals (G.splitOff v a b e₀) endsv q).toBodyHinge.rigidityRows))
    {t : K} (ht : t ≠ 0) (q₀ : α × Fin (k + 2) → K)
    (hq₀ : q₀ = fun p => if p.1 = v then
      ((fun i => q (a, i)) + t • (fun i => q (b, i))) p.2 else q p) :
    (∀ e, G.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.supportExtensor e ≠ 0) ∧
    N + (screwDim k - 1) ≤ Module.finrank K (Submodule.span K
      (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.rigidityRows) := by
  classical
  set Gab := G.splitOff v a b e₀ with hGab_def
  set n_a : Fin (k + 2) → K := fun i => q (a, i) with hn_a
  set n_b : Fin (k + 2) → K := fun i => q (b, i) with hn_b
  have hvG : v ∈ V(G) := hG_ea.left_mem
  have haG : a ∈ V(G) := hG_ea.right_mem
  have hbG : b ∈ V(G) := hG_eb.right_mem
  have hva : v ≠ a := hav.symm
  have hvb : v ≠ b := hbv.symm
  have hvVGab : v ∉ V(Gab) := by rw [hGab_def, Graph.vertexSet_splitOff]; simp
  have hends_Gab : ∀ e u w, Gab.IsLink e u w → Gab.IsLink e (endsv e).1 (endsv e).2 :=
    fun _ _ _ he => hlinksv.isLink he
  have hrec' : ∀ e u w, Gab.IsLink e u w → endsv e = (u, w) ∨ endsv e = (w, u) := by
    intro e u w he
    rcases hlinksv.eq_or_swap he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (Prod.ext h1 h2)
    · exact Or.inr (Prod.ext h1 h2)
  have he₀ab : Gab.IsLink e₀ a b := by
    rw [hGab_def, Graph.splitOff_isLink]
    exact Or.inr ⟨rfl, hav, hbv, haG, hbG, Or.inl ⟨rfl, rfl⟩⟩
  -- The hinge of `e₀` is `±C(n_a, n_b)`, nondegenerate.
  have hC : panelSupportExtensor n_a n_b ≠ 0 := by
    have h := hne e₀ (hends_Gab e₀ a b he₀ab)
    rcases hrec' e₀ a b he₀ab with h' | h'
    · rwa [PanelHingeFramework.ofNormals_supportExtensor_eq_panel_of_ends _ e₀ h'] at h
    · rw [PanelHingeFramework.ofNormals_supportExtensor_eq_panel_of_ends _ e₀ h',
        panelSupportExtensor_swap] at h
      exact neg_ne_zero.mp h
  subst hq₀
  set q₀ : α × Fin (k + 2) → K :=
    fun p => if p.1 = v then (n_a + t • n_b) p.2 else q p with hq₀_def
  have hq₀v : (fun i => q₀ (v, i)) = n_a + t • n_b := by
    funext i; rw [hq₀_def]; simp
  have hq₀a : (fun i => q₀ (a, i)) = n_a := by
    funext i; rw [hq₀_def, hn_a]; simp only [ite_eq_right hva.symm]
  have hq₀b : (fun i => q₀ (b, i)) = n_b := by
    funext i; rw [hq₀_def, hn_b]; simp only [ite_eq_right hvb.symm]
  -- The normals of `v` do not reach `Gab`: its motions, rank and hinges are those at `q`.
  have hvedge : ∀ e u w, Gab.IsLink e u w → (endsv e).1 ≠ v ∧ (endsv e).2 ≠ v := by
    intro e u w he
    have hl := hends_Gab e u w he
    exact ⟨fun h => hvVGab (h ▸ hl.left_mem), fun h => hvVGab (h ▸ hl.right_mem)⟩
  have hwN : PanelHingeFramework.ofNormals Gab endsv q₀
      = (PanelHingeFramework.ofNormals Gab endsv q).withNormal v (n_a + t • n_b) :=
    PanelHingeFramework.ofNormals_update_eq_withNormal Gab endsv q v (n_a + t • n_b)
  have hZeq : (PanelHingeFramework.ofNormals Gab endsv q₀).toBodyHinge.infinitesimalMotions
      = (PanelHingeFramework.ofNormals Gab endsv q).toBodyHinge.infinitesimalMotions := by
    rw [hwN]
    exact (PanelHingeFramework.ofNormals Gab endsv q).toBodyHinge_withNormal_infinitesimalMotions_eq
      v (n_a + t • n_b) hvedge
  have hspan_eq :
      Submodule.span K (PanelHingeFramework.ofNormals Gab endsv q₀).toBodyHinge.rigidityRows
      = Submodule.span K (PanelHingeFramework.ofNormals Gab endsv q).toBodyHinge.rigidityRows :=
    BodyHingeFramework.span_rigidityRows_eq_of_infinitesimalMotions_eq _ _ hZeq
  have hN₀ : N ≤ Module.finrank K (Submodule.span K
      (PanelHingeFramework.ofNormals Gab endsv q₀).toBodyHinge.rigidityRows) := by
    rw [hspan_eq]; exact hN
  have hne₀ : ∀ e, Gab.IsLink e (endsv e).1 (endsv e).2 →
      (PanelHingeFramework.ofNormals Gab endsv q₀).toBodyHinge.supportExtensor e ≠ 0 := by
    intro e he
    obtain ⟨h₁, h₂⟩ := hvedge e _ _ he
    rw [hwN, (PanelHingeFramework.ofNormals Gab endsv
        q).toBodyHinge_withNormal_supportExtensor_of_ne v (n_a + t • n_b) e (by simpa using h₁)
        (by simpa using h₂)]
    exact hne e he
  -- The old rows: `N` independent rows of `Gab` at `q₀`, at its links.
  set FG := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge with hFG_def
  set FGab := (PanelHingeFramework.ofNormals Gab endsv q₀).toBodyHinge with hFGab_def
  obtain ⟨so, hso_link, hso_card, hso_indep⟩ :=
    FGab.exists_independent_panelRow_subfamily_of_le_finrank (ends := endsv)
      (by simpa [hFGab_def] using hends_Gab) (by simpa [hFGab_def] using hne₀)
      (by simpa [hFGab_def] using hN₀)
  -- The hinges of `e_b` and `e_a` at `q₀`: `±C` and `±t C`, with `C = C(n_a, n_b)`.
  have hends_ea : ends e_a = (v, a) ∨ ends e_a = (a, v) := by
    rcases hlinks.eq_or_swap hG_ea with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (Prod.ext h1 h2)
    · exact Or.inr (Prod.ext h1 h2)
  have hends_eb : ends e_b = (v, b) ∨ ends e_b = (b, v) := by
    rcases hlinks.eq_or_swap hG_eb with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (Prod.ext h1 h2)
    · exact Or.inr (Prod.ext h1 h2)
  have hFG_ea : FG.supportExtensor e_a = (-t) • panelSupportExtensor n_a n_b ∨
      FG.supportExtensor e_a = t • panelSupportExtensor n_a n_b := by
    rcases hends_ea with h | h
    · left
      rw [hFG_def, PanelHingeFramework.ofNormals_supportExtensor_eq_panel_of_ends _ e_a h,
        hq₀v, hq₀a]
      exact panelSupportExtensor_add_smul_left n_a n_b t
    · right
      rw [hFG_def, PanelHingeFramework.ofNormals_supportExtensor_eq_panel_of_ends _ e_a h,
        hq₀a, hq₀v, panelSupportExtensor_swap (n_a + t • n_b) n_a,
        panelSupportExtensor_add_smul_left]
      module
  have hFG_eb : FG.supportExtensor e_b = panelSupportExtensor n_a n_b ∨
      FG.supportExtensor e_b = -panelSupportExtensor n_a n_b := by
    rcases hends_eb with h | h
    · left
      rw [hFG_def, PanelHingeFramework.ofNormals_supportExtensor_eq_panel_of_ends _ e_b h,
        hq₀v, hq₀b, panelSupportExtensor_add_smul_right]
    · right
      rw [hFG_def, PanelHingeFramework.ofNormals_supportExtensor_eq_panel_of_ends _ e_b h,
        hq₀b, hq₀v, panelSupportExtensor_swap, panelSupportExtensor_add_smul_right]
  -- A form that vanishes at `C` is in the hinge-row blocks of `e_a` and `e_b`.
  have hblock_a : ∀ ρ : Module.Dual K (ScrewSpace K k), ρ (panelSupportExtensor n_a n_b) = 0 →
      ρ ∈ FG.hingeRowBlock e_a := by
    intro ρ hρ
    rw [BodyHingeFramework.mem_hingeRowBlock_iff]
    rcases hFG_ea with h | h <;> rw [h, map_smul, hρ, smul_zero]
  have hblock_b : ∀ ρ : Module.Dual K (ScrewSpace K k), ρ (panelSupportExtensor n_a n_b) = 0 →
      ρ ∈ FG.hingeRowBlock e_b := by
    intro ρ hρ
    rw [BodyHingeFramework.mem_hingeRowBlock_iff]
    rcases hFG_eb with h | h <;> simp [h, hρ]
  -- The rows of `Gab` at `e₀` lie in the row space of `R(G, q₀)`: KT's column operation.
  have he₀_rows_mem : ∀ (t₁ t₂ : Set.powersetCard (Fin (k + 2)) k),
      FGab.panelRow endsv (e₀, t₁, t₂) ∈ Submodule.span K FG.rigidityRows := by
    intro t₁ t₂
    rw [hFGab_def, PanelHingeFramework.ofNormals_panelRow_eq_hingeRow_of_ends_or_swap Gab endsv q₀
        (hrec' e₀ a b he₀ab) t₁ t₂, hq₀a, hq₀b]
    set ρ := annihRow (panelSupportExtensor n_a n_b) t₁ t₂ with hρ_def
    have hρC : ρ (panelSupportExtensor n_a n_b) = 0 := annihRow_apply_self _ t₁ t₂
    -- `hingeRow a b ρ = hingeRow a v ρ + hingeRow v b ρ`
    rw [← sub_add_cancel (BodyHingeFramework.hingeRow a b ρ) (BodyHingeFramework.hingeRow v b ρ),
      BodyHingeFramework.hingeRow_sub_hingeRow_eq a v b ρ]
    exact Submodule.add_mem _
      (Submodule.subset_span (FG.hingeRow_mem_rigidityRows hG_ea.symm (hblock_a ρ hρC)))
      (Submodule.subset_span (FG.hingeRow_mem_rigidityRows hG_eb (hblock_b ρ hρC)))
  -- The other rows of `Gab` lie in the row space of `R(G, q₀)`: a link `e ≠ e₀` of `Gab` is a link
  -- of `G`, where its hinge is the same up to sign.
  have hGab_to_G_link : ∀ e u w, Gab.IsLink e u w → e ≠ e₀ → G.IsLink e u w := by
    intro e u w he hne
    rw [hGab_def, Graph.splitOff_isLink] at he
    rcases he with ⟨_, hGlink, _, _⟩ | ⟨rfl, _⟩
    · exact hGlink
    · exact absurd rfl hne
  have hse : ∀ e, G.IsLink e (endsv e).1 (endsv e).2 →
      FG.supportExtensor e = FGab.supportExtensor e ∨
        FG.supportExtensor e = -FGab.supportExtensor e := by
    intro e he
    have hFG_se : FG.supportExtensor e =
        panelSupportExtensor (fun i => q₀ ((ends e).1, i)) (fun i => q₀ ((ends e).2, i)) := rfl
    have hFGab_se : FGab.supportExtensor e =
        panelSupportExtensor (fun i => q₀ ((endsv e).1, i)) (fun i => q₀ ((endsv e).2, i)) := rfl
    rcases hlinks.eq_or_swap he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; rw [hFG_se, hFGab_se, h1, h2]
    · right; rw [hFG_se, hFGab_se, h1, h2]; exact panelSupportExtensor_swap _ _
  have hso_span : ∀ i : so, FGab.panelRow endsv (i : β × _ × _)
      ∈ Submodule.span K FG.rigidityRows := by
    rintro ⟨⟨e, t₁, t₂⟩, hi⟩
    have hlink := hso_link _ hi
    change FGab.panelRow endsv (e, t₁, t₂) ∈ Submodule.span K FG.rigidityRows
    by_cases he₀e : e = e₀
    · subst he₀e; exact he₀_rows_mem t₁ t₂
    · have hGlink_e : G.IsLink e (endsv e).1 (endsv e).2 := hGab_to_G_link e _ _ hlink he₀e
      rw [FGab.panelRow_eq_hingeRow_annihRow_of_ends endsv (by rfl) t₁ t₂]
      refine Submodule.subset_span (FG.hingeRow_mem_rigidityRows hGlink_e ?_)
      rw [BodyHingeFramework.mem_hingeRowBlock_iff]
      rcases hse e hGlink_e with h | h <;> rw [h]
      · exact annihRow_apply_self _ t₁ t₂
      · rw [map_neg, annihRow_apply_self, neg_zero]
  -- The new rows: the hinge of `e_b` at `q₀` is `±C ≠ 0`, so `e_b` has `D − 1` independent rows,
  -- which stay independent on the screw assignments that vanish off `v`.
  have hFG_eb_ne : FG.supportExtensor e_b ≠ 0 := by
    rcases hFG_eb with h | h <;> rw [h]
    · exact hC
    · exact neg_ne_zero.mpr hC
  have hends_eb_ne : (ends e_b).1 ≠ (ends e_b).2 := by
    rcases hends_eb with h | h <;> rw [h]
    · exact hvb
    · exact hbv
  obtain ⟨sn, hsn_e, hsn_card, hsn_indep⟩ :=
    FG.exists_independent_panelRow_subfamily_of_edge (ends := ends) (e := e_b) hends_eb_ne
      hFG_eb_ne
  have hnewpin := FG.linearIndependent_panelRow_comp_single_of_edge
    (ends := ends) (e := e_b) hends_eb_ne.symm hsn_e hsn_indep
  have hrow_b_eq : ∀ (t₁ t₂ : Set.powersetCard (Fin (k + 2)) k),
      BodyHingeFramework.hingeRow v b (annihRow (panelSupportExtensor n_a n_b) t₁ t₂)
        = FG.panelRow ends (e_b, t₁, t₂) := by
    intro t₁ t₂
    rw [hFG_def, PanelHingeFramework.ofNormals_panelRow_eq_hingeRow_of_ends_or_swap G ends q₀
        hends_eb t₁ t₂, hq₀v, hq₀b, panelSupportExtensor_add_smul_right]
  have hnewpin_eb : LinearIndependent K (fun i : sn =>
      (FG.panelRow ends (i : β × _ × _)).comp
        (LinearMap.single K (fun _ : α => ScrewSpace K k) v)) := by
    rcases hends_eb with h | h
    · rw [h] at hnewpin; simpa using hnewpin
    · rw [h] at hnewpin
      have : (fun i : sn => (FG.panelRow ends (i : β × _ × _)).comp
            (LinearMap.single K (fun _ : α => ScrewSpace K k) v)) =
          (fun i : sn => -(FG.panelRow ends (i : β × _ × _)).comp
            (LinearMap.single K (fun _ : α => ScrewSpace K k) b)) := by
        funext ⟨⟨e, t₁, t₂⟩, hi⟩
        simp only
        have he_eq : e = e_b := by simpa [Prod.fst] using hsn_e _ hi
        subst he_eq
        apply LinearMap.ext; intro x
        rw [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.comp_apply]
        simp only [LinearMap.single_apply]
        rw [← hrow_b_eq t₁ t₂]; rw [BodyHingeFramework.hingeRow_apply]
        simp [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hvb), Pi.single_eq_of_ne hvb,
          map_neg]
      rw [this]
      exact hnewpin.neg
  -- The old rows vanish on the screw assignments that vanish off `v`.
  have hold : ∀ (j : so) (x : ScrewSpace K k),
      FGab.panelRow endsv (j : β × _ × _)
        (Function.update (0 : α → ScrewSpace K k) v x) = 0 := by
    rintro ⟨i, hi⟩ x
    obtain ⟨h₁, h₂⟩ := hvedge i.1 _ _ (hso_link _ hi)
    simp only [BodyHingeFramework.panelRow, BodyHingeFramework.hingeRow_apply,
      Function.update_of_ne h₁, Function.update_of_ne h₂, Pi.zero_apply, sub_zero, map_zero]
  -- The hinges of `(G, q₀)` are nondegenerate: `e_b` and `e_a` above (`t ≠ 0`), and every other
  -- edge avoids `v` and is a link of `Gab`.
  have hne_G : ∀ e, G.IsLink e (ends e).1 (ends e).2 → FG.supportExtensor e ≠ 0 := by
    intro e he
    by_cases heb : e = e_b
    · subst heb; exact hFG_eb_ne
    by_cases hea : e = e_a
    · subst hea
      rcases hFG_ea with h | h <;> rw [h]
      · exact smul_ne_zero (neg_ne_zero.mpr ht) hC
      · exact smul_ne_zero ht hC
    have h1 : (ends e).1 ≠ v := by
      intro heq
      rcases hclv e (ends e).2 (heq ▸ he) with rfl | rfl
      · exact hea rfl
      · exact heb rfl
    have h2 : (ends e).2 ≠ v := by
      intro heq
      rcases hclv e (ends e).1 (heq ▸ he.symm) with rfl | rfl
      · exact hea rfl
      · exact heb rfl
    have hne₀e : e ≠ e₀ := fun heq =>
      he₀ (heq ▸ (Graph.removeVertex_isLink.mpr ⟨he, h1, h2⟩).edge_mem)
    have hGab_e : Gab.IsLink e (ends e).1 (ends e).2 := by
      rw [hGab_def, Graph.splitOff_isLink]
      exact Or.inl ⟨hne₀e, he, h1, h2⟩
    have hGabv := hends_Gab e _ _ hGab_e
    have hFGab_ne : FGab.supportExtensor e ≠ 0 := hne₀ e hGabv
    rcases hse e (hGab_to_G_link e _ _ hGabv hne₀e) with h | h <;> rw [h]
    · exact hFGab_ne
    · exact neg_ne_zero.mpr hFGab_ne
  -- The count (KT eq. (6.16)).
  refine ⟨hne_G, ?_⟩
  have : Fintype sn := Fintype.ofFinite sn
  have : Fintype so := Fintype.ofFinite so
  set rn : sn → Module.Dual K (α → ScrewSpace K k) :=
    fun i => FG.panelRow ends (i : β × _ × _) with hrn
  set ro : so → Module.Dual K (α → ScrewSpace K k) :=
    fun i => FGab.panelRow endsv (i : β × _ × _) with hro
  have hnew_span : ∀ i : sn, rn i ∈ Submodule.span K FG.rigidityRows := by
    rintro ⟨i, hi⟩
    refine Submodule.subset_span (FG.panelRow_mem_rigidityRows ?_)
    rw [hsn_e _ hi]
    exact hlinks.isLink hG_eb
  have hbrick : Nat.card sn + Nat.card so ≤
      Module.finrank K ↥(Submodule.span K FG.rigidityRows) :=
    BodyHingeFramework.le_finrank_span_rigidityRows_of_pinned_placement FG (v := v)
      (rn := rn) (ro := ro) hold hnewpin_eb hso_indep hnew_span hso_span
  rw [hsn_card, hso_card] at hbrick
  omega

/-- **KT eq. (6.12) at a rigid realization: one row short** (`lem:case-II-realization-placement`):
with `v`, `e_a`, `e_b`, `e₀`, `ends`, `endsv`, `t` and `q₀` as in `case_II_placement_rank`, let
`(G_v^{ab}, q)` have nondegenerate hinges and be infinitesimally rigid on `V(G_v^{ab})`. Then some
`D(|V(G)| − 1) − 1` rows of `R(G, q₀)`, at links of `G`, are linearly independent: one row short of
the target rank `D(|V(G)| − 1)`, as Katoh and Tanigawa note for `k = 0` (p. 680). The rank of
`(G_v^{ab}, q)` is `D(|V(G)| − 2)` (`finrank_span_rigidityRows_of_rigidOn`), so
`case_II_placement_rank` gives nondegenerate hinges and rank at least `D(|V(G)| − 1) − 1`, and
`exists_independent_panelRow_subfamily_of_le_finrank` the rows. No declaration uses it:
`case_II_realization_all_k` calls the count at a realization of rank below `D(|V(G)| − 2)`. -/
theorem PanelHingeFramework.case_II_placement [DecidableEq α] [Finite α] [Finite β]
    (G : Graph α β) {v a b : α} {e_a e_b e₀ : β}
    (hav : a ≠ v) (hbv : b ≠ v) (hG_ea : G.IsLink e_a v a) (hG_eb : G.IsLink e_b v b)
    (hclv : ∀ e x, G.IsLink e v x → e = e_a ∨ e = e_b)
    (he₀ : e₀ ∉ E(G.removeVertex v))
    (ends : β → α × α) (hlinks : RecordsLinks G ends)
    (endsv : β → α × α) (hlinksv : RecordsLinks (G.splitOff v a b e₀) endsv)
    {q : α × Fin (k + 2) → K}
    (hne : ∀ e, (G.splitOff v a b e₀).IsLink e (endsv e).1 (endsv e).2 →
      (PanelHingeFramework.ofNormals (G.splitOff v a b e₀) endsv q).toBodyHinge.supportExtensor e
        ≠ 0)
    (hrig : (PanelHingeFramework.ofNormals (G.splitOff v a b e₀) endsv q).toBodyHinge
      |>.IsInfinitesimallyRigidOn V(G.splitOff v a b e₀))
    {t : K} (ht : t ≠ 0) (q₀ : α × Fin (k + 2) → K)
    (hq₀ : q₀ = fun p => if p.1 = v then
      ((fun i => q (a, i)) + t • (fun i => q (b, i))) p.2 else q p) :
    ∃ s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      (∀ i ∈ s, G.IsLink (i : β × _ × _).1 (ends (i : β × _ × _).1).1
        (ends (i : β × _ × _).1).2) ∧
      Nat.card s = screwDim k * (V(G).ncard - 1) - 1 ∧
      LinearIndependent K (fun i : s =>
        (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.panelRow ends (i : β × _ × _)) := by
  have hvG : v ∈ V(G) := hG_ea.left_mem
  have hnev : V(G.splitOff v a b e₀).Nonempty :=
    ⟨a, by rw [Graph.vertexSet_splitOff]; exact ⟨hG_ea.right_mem, hav⟩⟩
  -- The rank of a rigid realization of `G_v^{ab}` is `D(|V(G_v^{ab})| − 1)`.
  have hrank := (PanelHingeFramework.ofNormals (G.splitOff v a b e₀) endsv q).toBodyHinge
    |>.finrank_span_rigidityRows_of_rigidOn hnev hrig
  obtain ⟨hne_G, hle⟩ := PanelHingeFramework.case_II_placement_rank G hav hbv hG_ea hG_eb hclv he₀
    ends hlinks endsv hlinksv hne hrank.ge ht q₀ hq₀
  -- `D(|V(G)| − 2) + (D − 1) = D(|V(G)| − 1) − 1`, as `|V(G_v^{ab})| = |V(G)| − 1 ≥ 1`.
  have hcard : V(G.splitOff v a b e₀).ncard = V(G).ncard - 1 := by
    rw [Graph.vertexSet_splitOff]; exact Set.ncard_sdiff_singleton_of_mem hvG
  have h1 : 1 ≤ V(G.splitOff v a b e₀).ncard := (Set.ncard_pos (Set.toFinite _)).2 hnev
  have hD1 : 1 ≤ screwDim k := one_le_screwDim
  have hle' : screwDim k * (V(G).ncard - 1) - 1 ≤ Module.finrank K (Submodule.span K
      (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.rigidityRows) := by
    refine le_trans (le_of_eq ?_) hle
    change screwDim k * (V(G).ncard - 1) - 1
      = screwDim k * (V(G.splitOff v a b e₀).ncard - 1) + (screwDim k - 1)
    rw [hcard] at h1 ⊢
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le h1
    rw [hm, Nat.add_sub_cancel_left, Nat.mul_add, mul_one]
    omega
  exact (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge
    |>.exists_independent_panelRow_subfamily_of_le_finrank (fun _ _ _ h => hlinks.isLink h) hne_G
      hle'

/-- **Case II: splitting off a vertex of degree two** (`lem:case-II-realization`; KT Lemma 6.8,
pp. 677–679): let `1 ≤ k` with `bodyBarDim n = screwDim k` (`hn`), and let `G` be a 2-edge-connected
minimal `c`-dof-graph with `c > 0`, `|V(G)| ≥ 3`, no proper rigid subgraph and an edge label
`e₀ ∉ E(G)` (`hfresh`). Suppose the induction hypothesis `hIH`: for every `c'`, every minimal
`c'`-dof-graph with at least one and fewer than `|V(G)|` vertices has a nondegenerate-hinge panel
realization at the target rank (`HasPanelRealization`), and a generic full-rank realization if it is
simple. Then `G` has a generic full-rank realization.

We follow Katoh and Tanigawa's count. `G` is simple (`simple_of_isMinimalKDof_of_noRigid`) and has a
vertex `v` of degree two (`exists_degree_eq_two`, KT Lemma 4.6), whose edges `e_a` and `e_b` join it
to vertices `a ≠ b`. No edge of `G` joins `a` and `b`: for `|V(G)| ≥ 4` it would close a proper
rigid triangle (`triangle_isProperRigidSubgraph`), and for `|V(G)| = 3` `G` would be a triangle, a
`0`-dof-graph (`isKDof_zero_of_triangle`). So the split-off `G_v^{ab}`, with the label `e₀` for
`ab`, is simple (`splitOff_simple_of_noRigid`), and it is a minimal `(c − 1)`-dof-graph
(`splitOff_isMinimalKDof_of_pos`, KT Lemma 4.8(ii)) on `|V(G)| − 1` vertices. The induction
hypothesis gives it a generic full-rank realization `Q` at normals `q`, of rank
`N = D(|V(G)| − 2) − (c − 1)` (KT eq. (6.11)).

Let `q₀` be `q` with the normal `q(a) + q(b)` at `v`, and `ends = G.endsOf`. The hinges of
`G_v^{ab}` are nonzero by general position, so the count of KT eq. (6.12) at `t = 1`
(`case_II_placement_rank`) gives `(G, q₀)` nondegenerate hinges and rank at least
`N + D − 1 = D(|V(G)| − 1) − c`: the rows of `G_v^{ab}` lie in the row space of `R(G, q₀)`, its rows
at `ab` by KT's column operation, and some `D − 1` rows of `e_b` add to them (KT eq. (6.16)). A
polynomial in the normals gives this bound at normals in general position
(`exists_rankPolynomial_of_le_finrank_linking`), where it is the target rank
(`finrank_span_rigidityRows_add_deficiency_le`). -/
theorem PanelHingeFramework.case_II_realization_all_k
    [Infinite K] [DecidableEq β] [Finite α] [Finite β]
    {n : ℕ} (hk1 : 1 ≤ k) (hn : Graph.bodyBarDim n = screwDim k)
    {c : ℤ} (G : Graph α β) (hfresh : ∃ e₀ : β, e₀ ∉ E(G))
    (hG : G.IsMinimalKDof n c) (hc : 0 < c) (hV3 : 3 ≤ V(G).ncard)
    (htec : G.TwoEdgeConnected)
    (hnoRigid : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n)
    (hIH : ∀ (c' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n c' → V(G').Nonempty →
      V(G').ncard < V(G).ncard →
      (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization K k n G') ∧
        HasPanelRealization K k n G') :
    PanelHingeFramework.HasGenericFullRankRealization K k n G := by
  classical
  have : Fintype α := Fintype.ofFinite α
  -- `3 ≤ D` and `2 ≤ D`, from `hn` and `1 ≤ k` (`three_le_screwDim`).
  have hD3 : 3 ≤ Graph.bodyBarDim n := hn ▸ three_le_screwDim hk1
  have hD2 : 2 ≤ Graph.bodyBarDim n := le_trans (by norm_num) hD3
  -- `G` is simple (`simple_of_isMinimalKDof_of_noRigid`).
  have hsimple : G.Simple :=
    Graph.simple_of_isMinimalKDof_of_noRigid hD2 hV3 hG hnoRigid
  have hGloop : G.Loopless := hsimple.toLoopless
  -- ── Step 1: Degree-2 vertex v with two distinct neighbours a, b. ──────────────────────────────
  have hV2 : 2 ≤ V(G).ncard := by omega
  obtain ⟨v, hvG, hdegv⟩ :=
    Graph.exists_degree_eq_two hD3 hV2 hG htec hnoRigid
  -- Extract the nonloop set `{e_a, e_b}` of size 2 at v (G.Simple ⇒ G.Loopless).
  have hcount := G.degree_eq_ncard_add_ncard v
  have hloop0 : {e | G.IsLoopAt e v}.ncard = 0 :=
    (Set.ncard_eq_zero (Set.toFinite _)).mpr
      (Set.eq_empty_iff_forall_notMem.mpr fun e he => hGloop.not_isLoopAt e v he)
  have hnl_eq : {e | G.IsNonloopAt e v}.ncard = 2 := by omega
  obtain ⟨e_a, e_b, heab, hset⟩ := Set.ncard_eq_two.mp hnl_eq
  have hea : G.IsNonloopAt e_a v := by
    have : e_a ∈ {e | G.IsNonloopAt e v} := by rw [hset]; exact Set.mem_insert _ _
    exact this
  have heb : G.IsNonloopAt e_b v := by
    have : e_b ∈ {e | G.IsNonloopAt e v} := by rw [hset]; exact Set.mem_insert_of_mem _ rfl
    exact this
  obtain ⟨a, hav, hG_ea⟩ := hea
  obtain ⟨b, hbv, hG_eb⟩ := heb
  have haG : a ∈ V(G) := hG_ea.right_mem
  have hbG : b ∈ V(G) := hG_eb.right_mem
  -- a ≠ b (else e_a and e_b are parallel at the same pair {v, a}, contradicting Simple).
  have hab : a ≠ b := fun h => heab (hsimple.eq_of_isLink hG_ea (h ▸ hG_eb))
  -- Degree-2 closure: every v-incident edge is e_a or e_b.
  have hclv : ∀ e x, G.IsLink e v x → e = e_a ∨ e = e_b := by
    intro e x hlink
    have hinc : G.Inc e v := hlink.inc_left
    rcases hinc.isLoopAt_or_isNonloopAt with hloop | hnonloop
    · exact absurd (Set.eq_empty_iff_forall_notMem.mp
        (Set.ncard_eq_zero (Set.toFinite _) |>.mp hloop0) e hloop) id
    · have : e ∈ ({e_a, e_b} : Set β) := hset ▸ hnonloop
      simpa [Set.mem_insert_iff] using this
  -- ── Step 2: the split-off `Gab = G.splitOff v a b e₀`, with `e₀ ∉ E(G)`. ───────────────────────
  obtain ⟨e₀, he₀⟩ := hfresh
  set Gab := G.splitOff v a b e₀ with hGab_def
  -- `Gab` is simple (`splitOff_simple_of_noRigid`, whose triangle hypothesis is vacuous here): for
  -- `c > 0` no edge `f` of `G` joins `a` and `b`. If `|V(G)| ≥ 4`, the triangle on `v`, `a`, `b`
  -- would be a proper rigid subgraph (`triangle_isProperRigidSubgraph`), against `hnoRigid`; if
  -- `|V(G)| = 3`, `G` would be the triangle, a `0`-dof-graph (`isKDof_zero_of_triangle`).
  have h_no_fab : ∀ f : β, ¬ G.IsLink f a b := by
    intro f hf
    by_cases hV4 : 4 ≤ V(G).ncard
    · -- |V(G)| ≥ 4: use triangle_isProperRigidSubgraph + hnoRigid.
      obtain ⟨H, hH⟩ := Graph.triangle_isProperRigidSubgraph hD3 hG_ea hG_eb hf hV4
      exact hnoRigid H hH
    · -- |V(G)| = 3: G is K₃, hence 0-dof, contradicting k > 0.
      -- Derive V(G) = {v, a, b}.
      have hcard3 : V(G).ncard = 3 := by omega
      have hVeq : V(G) = {v, a, b} := by
        have hsub : ({v, a, b} : Set α) ⊆ V(G) :=
          Set.insert_subset hvG (Set.insert_subset haG (Set.singleton_subset_iff.mpr hbG))
        have hncard3 : ({v, a, b} : Set α).ncard = 3 := by
          have hva : v ≠ a := hav.symm
          have hvb : v ≠ b := hbv.symm
          rw [Set.ncard_insert_of_notMem (by simp [hva, hvb]),
            Set.ncard_insert_of_notMem (by simp [hab]), Set.ncard_singleton]
        exact (Set.eq_of_subset_of_ncard_le hsub (by omega) (Set.toFinite _)).symm
      -- E(G) = {e_a, e_b, f}: the three edges exhaust all vertex pairs of {v,a,b}.
      have hva : v ≠ a := hav.symm
      have hvb : v ≠ b := hbv.symm
      have hef_ne_ea : f ≠ e_a := by
        intro hfe; rw [hfe] at hf
        -- hf : G.IsLink e_a a b, hG_ea : G.IsLink e_a v a
        -- eq_and_eq_or_eq_and_eq: (a=v ∧ b=a) ∨ (a=a ∧ b=v)
        rcases hf.eq_and_eq_or_eq_and_eq hG_ea with ⟨h1, -⟩ | ⟨-, h2⟩
        · exact absurd h1 hav     -- a = v contradicts hav : a ≠ v
        · exact absurd h2.symm hvb -- b = v → v = b contradicts hvb : v ≠ b
      have hef_ne_eb : f ≠ e_b := by
        intro hfe; rw [hfe] at hf
        -- hf : G.IsLink e_b a b, hG_eb : G.IsLink e_b v b
        -- eq_and_eq_or_eq_and_eq: (a=v ∧ b=b) ∨ (a=b ∧ b=v)
        rcases hf.eq_and_eq_or_eq_and_eq hG_eb with ⟨h1, -⟩ | ⟨h2, -⟩
        · exact absurd h1 hav     -- a = v contradicts hav : a ≠ v
        · exact absurd h2 hab     -- a = b contradicts hab : a ≠ b
      have hEG : E(G) = {e_a, e_b, f} := by
        ext e
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · intro he
          obtain ⟨x, y, hlink⟩ := G.exists_isLink_of_mem_edgeSet he
          -- x, y ∈ V(G) = {v, a, b} and x ≠ y.
          have hxG : x ∈ V(G) := hlink.left_mem
          have hyG : y ∈ V(G) := hlink.right_mem
          rw [hVeq] at hxG hyG
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxG hyG
          -- Case analysis on (x, y) over {v, a, b}².
          rcases hxG with rfl | rfl | rfl <;> rcases hyG with rfl | rfl | rfl
          · exact absurd rfl hlink.ne
          · exact Or.inl (hlink.unique_edge hG_ea)
          · exact Or.inr (Or.inl (hlink.unique_edge hG_eb))
          · exact Or.inl (hlink.symm.unique_edge hG_ea)
          · exact absurd rfl hlink.ne
          · exact Or.inr (Or.inr (hlink.unique_edge hf))
          · exact Or.inr (Or.inl (hlink.symm.unique_edge hG_eb))
          · exact Or.inr (Or.inr (hlink.symm.unique_edge hf))
          · exact absurd rfl hlink.ne
        · rintro (rfl | rfl | rfl)
          exacts [hG_ea.edge_mem, hG_eb.edge_mem, hf.edge_mem]
      -- Apply isKDof_zero_of_triangle to get G.IsKDof n 0.
      -- Edge order: {exy, eyz, exz} = {e_a, f, e_b} (x=v, y=a, z=b, exy=e_a, eyz=f, exz=e_b).
      have hEG' : E(G) = {e_a, f, e_b} := by
        rw [hEG]; ext; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
      have hG0 : G.IsKDof n 0 :=
        Graph.isKDof_zero_of_triangle hD3 hva hab hvb hG_ea hf hG_eb hVeq hEG'
      -- But `G.IsMinimalKDof n c` means `G.deficiency n = c > 0`. Contradiction.
      exact absurd (hG.deficiency_eq.symm.trans hG0) (by omega)
  have hGab_simple : Gab.Simple :=
    Graph.splitOff_simple_of_noRigid heab hG_ea hG_eb hnoRigid
      (fun f hf => False.elim (h_no_fab f hf))
  -- `Gab` is a minimal `(c − 1)`-dof-graph (`splitOff_isMinimalKDof_of_pos`, KT Lemma 4.8(ii)).
  have hGab : Gab.IsMinimalKDof n (c - 1) :=
    Graph.splitOff_isMinimalKDof_of_pos hD3 hc hab hav hbv heab hG_ea hG_eb hclv he₀ hG hnoRigid
  -- Gab has fewer vertices: |V(Gab)| < |V(G)|.
  have hGab_lt : V(Gab).ncard < V(G).ncard := by
    rw [hGab_def]; exact Graph.splitOff_vertexSet_ncard_lt hvG
  -- Gab is nonempty (a ∈ V(Gab)).
  have hGab_ne : V(Gab).Nonempty :=
    ⟨a, by rw [hGab_def, Graph.vertexSet_splitOff]; exact ⟨haG, hav⟩⟩
  -- ── Step 3: the induction hypothesis at `Gab`, at deficiency `c − 1`. ──────────────────────────
  obtain ⟨Q, hQg, hQgp, hQrank⟩ := (hIH (c - 1) Gab hGab hGab_ne hGab_lt).1 hGab_simple
  -- Its selector records the links of `Gab` (the field `isLink_ends`, as `Q.graph = Gab`).
  have hQrec : PanelHingeFramework.RecordsLinks Gab Q.ends := hQg ▸ Q.isLink_ends
  -- Set up the IH normal function q := Q.normal.
  set q : α × Fin (k + 2) → K := fun p => Q.normal p.1 p.2 with hq_def
  -- ── Step 4: the normals `n_a` and `n_b` of `a` and `b`. ────────────────────────────────────────
  set n_a : Fin (k + 2) → K := fun i => q (a, i) with hn_a
  set n_b : Fin (k + 2) → K := fun i => q (b, i) with hn_b
  -- ── Step 5: the selector `ends = G.endsOf` (`Inhabited α`). ────────────────────────────────────
  have : Inhabited α := ⟨v⟩
  set ends := G.endsOf with hendsDef
  -- ── Step 6: the rank `N` of the realization of `Gab`. ──────────────────────────────────────────
  -- N := D(|V(Gab)|−1) − (c−1) as a natural number (the IH's ℤ-rank equality; `c` = dof).
  -- The IH says: (finrank (span rigidityRows) : ℤ) = screwDim k * (|V(Gab)| - 1) - (c - 1).
  -- Since c ≥ 1, (c-1) ≥ 0, and the RHS is a ℕ-cast.
  have h1Gab : 1 ≤ V(Gab).ncard := (Set.ncard_pos (Set.toFinite _)).2 hGab_ne
  -- Extract the IH realization as ofNormals at q.
  have hQeq : PanelHingeFramework.ofNormals Gab Q.ends q = Q := by
    rw [hq_def]; exact PanelHingeFramework.ofNormals_eq_self_of_graph_eq Q hQg
  -- The IH finrank at q (via hQeq identifying ofNormals with Q).
  have hQfin : Module.finrank K (Submodule.span K
      (PanelHingeFramework.ofNormals Gab Q.ends q).toBodyHinge.rigidityRows)
      = Module.finrank K (Submodule.span K Q.toBodyHinge.rigidityRows) := by
    rw [hQeq]
  rw [hGab.1] at hQrank
  -- hQrank now: (finrank : ℤ) = screwDim k * (|V(Gab)| - 1) - (c - 1)
  -- Convert to the ℕ form for the rank bound.
  -- Represent the IH rank as a natural number N.
  -- We need N : ℕ with N ≤ finrank (span (ofNormals Gab Q.ends q).rigidityRows).
  have hc1 : 0 ≤ c - 1 := by omega
  have hNZ : (screwDim k * (V(Gab).ncard - 1) : ℤ) - (c - 1) ≥ 0 := by
    have h0 : (0 : ℤ) ≤ Module.finrank K (Submodule.span K Q.toBodyHinge.rigidityRows) :=
      Int.natCast_nonneg _
    push_cast [h1Gab] at hQrank ⊢
    linarith [hQrank, h0]
  set N : ℕ := (screwDim k * (V(Gab).ncard - 1) - (c - 1)).toNat with hN_def
  have hN_eq : (N : ℤ) = screwDim k * (V(Gab).ncard - 1) - (c - 1) := by
    rw [hN_def]; exact Int.toNat_of_nonneg hNZ
  have hNrank_q : N ≤ Module.finrank K (Submodule.span K
      (PanelHingeFramework.ofNormals Gab Q.ends q).toBodyHinge.rigidityRows) := by
    rw [hQfin]
    have hle : (N : ℤ) ≤ Module.finrank K (Submodule.span K Q.toBodyHinge.rigidityRows) := by
      rw [hN_eq]; push_cast [h1Gab] at hQrank ⊢; linarith [hQrank]
    exact_mod_cast hle
  -- ── Steps 7–18: the count at `q₀ = q[v ↦ n_a + 1 • n_b]` (`case_II_placement_rank`, `t = 1`). ──
  have hQ_ends_Gab : ∀ e u w, Gab.IsLink e u w → Gab.IsLink e (Q.ends e).1 (Q.ends e).2 :=
    fun _ _ _ he => hQrec.isLink he
  have hne_q : ∀ e, Gab.IsLink e (Q.ends e).1 (Q.ends e).2 →
      (PanelHingeFramework.ofNormals Gab Q.ends q).toBodyHinge.supportExtensor e ≠ 0 := by
    intro e he
    apply PanelHingeFramework.supportExtensor_ne_zero_of_isGeneralPosition _
      (by rw [hQeq]; exact hQgp)
    rw [PanelHingeFramework.ofNormals_ends]
    have : Gab.Loopless := hGab_simple.toLoopless
    exact (hQ_ends_Gab e _ _ he).ne
  set q₀ : α × Fin (k + 2) → K :=
    fun p => if p.1 = v then (n_a + (1 : K) • n_b) p.2 else q p with hq₀_def
  obtain ⟨hne_G, hcount⟩ := PanelHingeFramework.case_II_placement_rank G hav hbv hG_ea hG_eb hclv
    (Graph.notMem_edgeSet_removeVertex he₀ v) ends (PanelHingeFramework.recordsLinks_endsOf G)
    Q.ends hQrec hne_q hNrank_q one_ne_zero q₀ rfl
  -- ── Step 15: the count `N + (D − 1) = D(|V(G)| − 1) − c`. ──────────────────────────────────────
  have hVGab_card : V(Gab).ncard = V(G).ncard - 1 := by
    rw [hGab_def, Graph.vertexSet_splitOff]
    exact Set.ncard_sdiff_singleton_of_mem hvG
  have hN_val : (N : ℤ) = screwDim k * ((V(G).ncard : ℤ) - 2) - (c - 1) := by
    rw [hN_eq, hVGab_card]
    have hVG2 : 2 ≤ V(G).ncard := by linarith [hV3]
    norm_cast
  have hNpD : (N : ℤ) + ((screwDim k : ℤ) - 1) = screwDim k * ((V(G).ncard : ℤ) - 1) - c := by
    rw [hN_val]; ring
  -- ── Step 19: the bound in `ℕ`, for `exists_rankPolynomial_of_le_finrank_linking`. ──────────────
  have h1V : 1 ≤ V(G).ncard := (Set.ncard_pos (Set.toFinite _)).2 ⟨v, hvG⟩
  have hD1 : 1 ≤ screwDim k := one_le_screwDim
  have hrank_lb_nat : (screwDim k * (V(G).ncard - 1) - c.toNat) ≤ Module.finrank K
      (Submodule.span K (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.rigidityRows) := by
    rw [sub_toNat_eq_of_add_pred_eq hc h1V hD1 hNpD]
    exact hcount
  have hends_G : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2 := by
    rw [hendsDef]; exact fun e _ _ h => G.isLink_endsOf h.edge_mem
  -- ── Step 20: normals `q'` in general position at the target rank. ──────────────────────────────
  -- `exists_rankPolynomial_of_le_finrank_linking` gives a polynomial off whose zeros the bound
  -- holds; with the polynomial of general position it has a common non-root `q'`.
  obtain ⟨Q_rk, hQ_rk0, hQ_rk⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_le_finrank_linking G ends hends_G hne_G
      hrank_lb_nat
  obtain ⟨Q_gp, hQ_gp_ne, hQ_gp⟩ :=
    exists_generalPosition_polynomial (K := K) (k := k) G ends
  have hQ_rk_ne : Q_rk ≠ 0 := fun h => hQ_rk0 (by rw [h, map_zero])
  have hQ_gp_ne' : Q_gp ≠ 0 := by
    obtain ⟨f, hf⟩ := Countable.exists_injective_of_infinite α K
    exact fun h => hQ_gp_ne f hf (by rw [h, map_zero])
  obtain ⟨q', hq'_rk, hq'_gp⟩ := MvPolynomial.exists_eval_ne_zero₂ hQ_rk_ne hQ_gp_ne'
  have hgp' : (PanelHingeFramework.ofNormals G ends q').IsGeneralPosition := hQ_gp q' hq'_gp
  -- Rank lower bound at q': from rank polynomial.
  have hrankge_q' : screwDim k * (V(G).ncard - 1) - c.toNat ≤
      Module.finrank K (Submodule.span K
        (PanelHingeFramework.ofNormals G ends q').toBodyHinge.rigidityRows) := hQ_rk q' hq'_rk
  -- Upper bound at `q'`: `finrank_span_rigidityRows_add_deficiency_le`, at the nonzero hinges
  -- that general position gives.
  have hFG'_graph : (PanelHingeFramework.ofNormals G ends q').toBodyHinge.graph = G := by
    rw [PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]
  have hVGne : V(G).Nonempty := ⟨v, hvG⟩
  have hne_q' : ∀ e u w, G.IsLink e u w →
      (PanelHingeFramework.ofNormals G ends q').toBodyHinge.supportExtensor e ≠ 0 :=
    fun e u w he => PanelHingeFramework.supportExtensor_ne_zero_of_isGeneralPosition
      _ hgp' (by rw [PanelHingeFramework.ofNormals_ends]; exact (hends_G e u w he).ne)
  have hB2_q' : (Module.finrank K (Submodule.span K
      (PanelHingeFramework.ofNormals G ends q').toBodyHinge.rigidityRows) : ℤ)
      ≤ screwDim k * ((V(G).ncard : ℤ) - 1) - G.deficiency n := by
    have hVGne' :
        (PanelHingeFramework.ofNormals G ends q').toBodyHinge.graph.vertexSet.Nonempty := by
      rw [hFG'_graph]; exact hVGne
    have hCq' : ∀ e u w,
        (PanelHingeFramework.ofNormals G ends q').toBodyHinge.graph.IsLink e u w →
        (PanelHingeFramework.ofNormals G ends q').toBodyHinge.supportExtensor e ≠ 0 := by
      intro e u w hlink
      exact hne_q' e u w (hFG'_graph ▸ hlink)
    have hB2 := BodyHingeFramework.finrank_span_rigidityRows_add_deficiency_le
      (PanelHingeFramework.ofNormals G ends q').toBodyHinge hn hVGne'
      (fun e u v h _ => hCq' e u v h)
    rwa [hFG'_graph] at hB2
  -- Rank equality at q': lb ≥ N and ub ≤ N (since c = G.deficiency n).
  have hrank_eq_q' : (Module.finrank K (Submodule.span K
      (PanelHingeFramework.ofNormals G ends q').toBodyHinge.rigidityRows) : ℤ)
      = screwDim k * ((V(G).ncard : ℤ) - 1) - G.deficiency n := by
    have h1V : 1 ≤ V(G).ncard := (Set.ncard_pos (Set.toFinite _)).2 hVGne
    have hdef : G.deficiency n = c := hG.deficiency_eq
    have hrankge_int : screwDim k * ((V(G).ncard : ℤ) - 1) - c ≤
        (Module.finrank K (Submodule.span K
          (PanelHingeFramework.ofNormals G ends q').toBodyHinge.rigidityRows) : ℤ) := by
      -- hrankge_q' : screwDim k * (V(G).ncard - 1) - c.toNat ≤ finrank (ℕ)
      -- Cast to ℤ (`toNat_le_of_add_pred_eq`).
      have hc_toNat_le' : c.toNat ≤ screwDim k * (V(G).ncard - 1) :=
        toNat_le_of_add_pred_eq h1V hD1 hNpD
      have hZ_eq : (screwDim k : ℤ) * ((V(G).ncard : ℤ) - 1) - c =
          ↑(screwDim k * (V(G).ncard - 1) - c.toNat) := by
        simp only [Nat.cast_sub hc_toNat_le', Nat.cast_mul, Nat.cast_sub h1V,
          Int.toNat_of_nonneg (Int.le_of_lt hc)]
        norm_cast
      calc screwDim k * ((V(G).ncard : ℤ) - 1) - c
          = ↑(screwDim k * (V(G).ncard - 1) - c.toNat) := hZ_eq
        _ ≤ _ := by exact_mod_cast hrankge_q'
    exact le_antisymm hB2_q' (hdef.symm ▸ hrankge_int)
  -- Build the final witness.
  exact ⟨PanelHingeFramework.ofNormals G ends q',
    PanelHingeFramework.ofNormals_graph G ends q',
    hgp',
    hrank_eq_q'⟩

end CombinatorialRigidity.Molecular
