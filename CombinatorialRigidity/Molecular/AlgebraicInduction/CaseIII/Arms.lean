/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.AlgebraicInduction.CaseIII.Candidate
import CombinatorialRigidity.Molecular.Induction.ForestSurgery.ChainExtraction
import CombinatorialRigidity.Molecular.AlgebraicInduction.CaseI

/-!
# Case III: the rotation about `L`, the triangle and the cycle

Lemmas for Case III of KT Theorem 5.5 (Katoh and Tanigawa 2011, *A proof of the molecular
conjecture*, Discrete Comput. Geom. **45**, §6.4), presented in
`sec:molecular-algebraic-induction-caseIII`. The file proves:

* that the framework `(G, p_1)` of `def:case-III-candidate`, at rank `D(|V(G)| − 1)`, gives a
  generic full-rank realization of `G`, by rotating the panel of `v` about the line `L`
  (`case_III_realization_of_rank`); the same after the count of `lem:case-III-rank-certification`
  (`case_III_arm_realization`), and with `a` and `b` exchanged (`case_III_arm_realization_M2`):
  steps of `lem:case-III-candidate-dispatch-d3` and `lem:case-III-chain-dispatch`;
* KT Lemma 6.7(i) for the triangle (`lem:triangle-realization`), which no main result uses, and KT
  Lemma 5.4 for cycles on at most `d + 1` vertices (`lem:cycle-realization`, in
  `sec:molecular-algebraic-induction-caseI`);
* `lem:case-III` from its case of a chain (`case_III_hsplit_producer_all_k`).

`CaseIII/Relabel/` renames the bodies for the third framework and for the general case, and
`CaseIII/Realization.lean` proves the case `d = 3`, the case of a chain and `lem:case-III`.
-/

namespace CombinatorialRigidity.Molecular

variable {k : ℕ}

open scoped Graph

variable {α β : Type*}

variable {K : Type*} [Field K]

/-! ## The rotation about `L`

Steps of `lem:case-III-candidate-dispatch-d3` and `lem:case-III-chain-dispatch`: from the rank of
the framework `F_0` of `def:case-III-candidate`, a generic full-rank realization of `G`, by rotating
the panel of `v` about `L`, where Katoh and Tanigawa apply KT Lemma 5.2 (KT p. 691). -/

/-- **From the rank of `F_0` to a generic full-rank realization** (a step of
`lem:case-III-candidate-dispatch-d3` and `lem:case-III-chain-dispatch`): let `Gv` be a graph without
`v` (`hvVc`), with `a, b ∈ V(Gv)`, whose links are links of `G` (`hleG`), and let every link of `G`
be `e_a`, `e_b` or a link of `Gv` (`hsplitG`), where `e_a ≠ e_b` link `v` to `a` and `b`, with
`ends e_a = (v, a)` and `ends e_b = (v, b)`. Let `ends` give the links of `Gv` their ends
(`hends_Gv`), with nonzero hinges in `ofNormals Gv ends q` (`hne_Gv`), and let `q(a), n'` and
`q(a), q(b)` be linearly independent (`hLn`, `hgab`). If the framework
`F_0 = caseIIICandidate G ends q e_a e_b (q(a,·)) n' (q(b,·)) 0`, Katoh and Tanigawa's `(G, p_1)`,
has rank at least `D(|V(G)| − 1)` (`hrank`) and `G` has deficiency `0`, then `G` has a generic
full-rank realization.

The proof, as in the proof of `lem:case-III-candidate-dispatch-d3`. Some `D(|V(G)| − 1)` panel rows
of `F_0` at links of `G` are linearly independent
(`exists_independent_panelRow_subfamily_of_le_finrank`, `lem:independent-rows-of-rank`). The rows of
`F_t` are affine in `t`, so the same rows stay independent at some `t ≠ 0` off the at most one `t`
at which `q(a) + t n'` and `q(b)` are dependent (`caseIIICandidate_exists_good_shear`,
`setOf_not_shear_linearIndependent_subsingleton`). Let `q₀` be `q` with the normal `q(a) + t n'` at
`v`, a panel through `L`. Each of these rows lies in the span of the rows of `ofNormals G ends q₀`:
at `e_b` and at the links of `Gv` the two frameworks have the same hinge, and at `e_a` the hinge of
`ofNormals G ends q₀` is `−t C(q(a), n')` (`panelSupportExtensor_add_smul_left`), so the row of
`F_t` is `(−t)⁻¹` times a row of `ofNormals G ends q₀`. So `ofNormals G ends q₀` is infinitesimally
rigid on `V(G)` (`isInfinitesimallyRigidOn_vertexSet_of_span_le_rigidityRows`), its hinges at links
are nonzero, and `hasGenericFullRankRealization_of_rigidOn_ofNormals`
(`lem:generic-realization-of-rigid`) gives the realization. Only `case_III_arm_realization` uses it.
-/
theorem PanelHingeFramework.case_III_realization_of_rank [Infinite K]
    [Finite α] [Finite β] [DecidableEq β]
    (G Gv : Graph α β) (ends : β → α × α) {q : α × Fin (k + 2) → K}
    {v a b : α} {e_a e_b : β}
    (hvVc : v ∉ V(Gv)) (haVc : a ∈ V(Gv)) (hbVc : b ∈ V(Gv))
    (hG_ea : G.IsLink e_a v a) (hG_eb : G.IsLink e_b v b)
    (hends_ea : ends e_a = (v, a)) (hends_eb : ends e_b = (v, b)) (heab : e_a ≠ e_b)
    (hleG : ∀ e u w, Gv.IsLink e u w → G.IsLink e u w)
    (hsplitG : ∀ e u w, G.IsLink e u w → e = e_a ∨ e = e_b ∨ Gv.IsLink e u w)
    (hends_Gv : ∀ e u w, Gv.IsLink e u w → Gv.IsLink e (ends e).1 (ends e).2)
    (hne_Gv : ∀ e, Gv.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.supportExtensor e ≠ 0)
    {n' : Fin (k + 2) → K}
    (hLn : LinearIndependent K ![(fun i => q (a, i)), n'])
    (hgab : LinearIndependent K ![(fun i => q (a, i)), (fun i => q (b, i))])
    (hrank : screwDim k * (V(G).ncard - 1)
      ≤ Module.finrank K (Submodule.span K
        (PanelHingeFramework.caseIIICandidate G ends q e_a e_b
          (fun i => q (a, i)) n' (fun i => q (b, i)) 0).rigidityRows))
    {n : ℕ} (hdef : G.deficiency n = 0) :
    PanelHingeFramework.HasGenericFullRankRealization K k n G := by
  classical
  have : Fintype α := Fintype.ofFinite α
  set na := (fun i => q (a, i)) with hna
  set nb := (fun i => q (b, i)) with hnb
  have hva : v ≠ a := fun h => hvVc (h ▸ haVc)
  have hvb : v ≠ b := fun h => hvVc (h ▸ hbVc)
  have hnev : V(G).Nonempty := ⟨v, hG_ea.left_mem⟩
  -- (i) The rank bound of KT eq. (6.29) at the framework `F₀` is `hrank`.
  set F₀ := PanelHingeFramework.caseIIICandidate G ends q e_a e_b na n' nb 0 with hF₀
  -- The hinges of `F₀` at `e_a` and `e_b`, and that they are nonzero.
  have hsuppea : F₀.supportExtensor e_a = panelSupportExtensor na n' :=
    PanelHingeFramework.caseIIICandidate_supportExtensor_candidate G ends q na n' nb 0 heab
  have hsuppeb : F₀.supportExtensor e_b = panelSupportExtensor na nb := by
    simp only [hF₀, PanelHingeFramework.caseIIICandidate_supportExtensor_reproduced, zero_smul,
      add_zero]
  -- (ii) The rank gives that many linearly independent panel rows of `F₀` at links.
  -- `hends` at `F₀.graph = G`: every `G`-link is `e_a`, `e_b`, or a `Gᵥ`-link (`hsplitG`).
  have hF₀graph : F₀.graph = G := by rw [hF₀]; exact PanelHingeFramework.caseIIICandidate_graph ..
  -- `hends` and `hne` at `G` (`F₀.graph = G` by definition), for step (ii) and the last step.
  have hends_q₀ : ∀ e u w, G.IsLink e u w → G.IsLink e (ends e).1 (ends e).2 := by
    intro e u w hlink
    rcases hsplitG e u w hlink with he | he | hGv
    · rw [he, hends_ea]; exact hG_ea
    · rw [he, hends_eb]; exact hG_eb
    · exact hleG e _ _ (hends_Gv e u w hGv)
  have hends_G : ∀ e u w, F₀.graph.IsLink e u w → F₀.graph.IsLink e (ends e).1 (ends e).2 :=
    hF₀graph ▸ hends_q₀
  -- `hne` on linking edges: `e_a ↦ C(L) ≠ 0` (`hLn`), `e_b ↦ C(e₀) ≠ 0` (`hgab`), `Gᵥ` via `hne_Gv`
  -- + extensor agreement off `{e_a, e_b}`, which meet `v ∉ V(Gv)` (`Graph.IsLink.ne_of_notMem`).
  have hGv_off : ∀ {e u w}, Gv.IsLink e u w → e ≠ e_a ∧ e ≠ e_b := fun hlink =>
    ⟨hG_ea.ne_of_notMem hvVc hleG hlink, hG_eb.ne_of_notMem hvVc hleG hlink⟩
  have hne_F₀ : ∀ e, F₀.graph.IsLink e (ends e).1 (ends e).2 → F₀.supportExtensor e ≠ 0 := by
    intro e hlink
    rcases hsplitG e (ends e).1 (ends e).2 hlink with he | he | hGv
    · rw [he, hsuppea]; exact (panelSupportExtensor_ne_zero_iff na n').mpr hLn
    · rw [he, hsuppeb]; exact (panelSupportExtensor_ne_zero_iff na nb).mpr hgab
    · obtain ⟨hne_a, hne_b⟩ := hGv_off hGv
      rw [hF₀, PanelHingeFramework.caseIIICandidate_supportExtensor_of_ne G ends q e_a e_b na n' nb
        0 hne_a hne_b]
      exact hne_Gv e (hends_Gv e _ _ hGv)
  obtain ⟨s, hs_link, hs_card, hs_indep⟩ :=
    F₀.exists_independent_panelRow_subfamily_of_le_finrank (ends := ends) hends_G hne_F₀ hrank
  -- (iii) The same rows stay independent at some `t ≠ 0` off the set `bad` of the `t` at which
  -- `na + t·n'` and `nb` are dependent.
  have : Finite ↥s := Set.Finite.to_subtype (Set.toFinite s)
  set bad : Finset K :=
    (setOf_not_shear_linearIndependent_subsingleton na n' nb hgab).finite.toFinset with hbad
  obtain ⟨t, ht_bad, ht_ne, ht_li⟩ :=
    PanelHingeFramework.caseIIICandidate_exists_good_shear G ends q heab na n' nb
      (ι := ↥s) (fun i => (i : β × _ × _)) (by rw [← hF₀]; exact hs_indep) bad
  -- `t ∉ bad` makes `![na + t·n', nb]` independent, so the hinge of `e_b` stays nonzero.
  have hnewtrans : LinearIndependent K ![na + t • n', nb] := by
    by_contra hdep
    refine ht_bad ?_
    rw [hbad, Set.Finite.mem_toFinset]
    exact hdep
  -- (iv) The normals `q₀`, with `na + t·n'` at `v`, agreeing with `q` off `v`.
  set Ft := PanelHingeFramework.caseIIICandidate G ends q e_a e_b na n' nb t with hFt
  set q₀ : α × Fin (k + 2) → K := fun p => if p.1 = v then (na + t • n') p.2 else q p with hq₀def
  set FG₀ := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge with hFG₀
  have hq₀v : (fun i => q₀ (v, i)) = na + t • n' := by funext i; rw [hq₀def]; simp
  have hq₀a : (fun i => q₀ (a, i)) = na := by
    funext i; rw [hq₀def, hna]; simp only [ite_eq_right hva.symm]
  have hq₀b : (fun i => q₀ (b, i)) = nb := by
    funext i; rw [hq₀def, hnb]; simp only [ite_eq_right hvb.symm]
  -- Off `v`, `q₀` agrees with `q`, so the `ofNormals G ends q₀` extensor of any edge avoiding `v`
  -- equals the `ofNormals G ends q` one (that of `F₀` and `Ft` off `{e_a, e_b}`).
  have hq₀_off : ∀ u, u ≠ v → (fun i => q₀ (u, i)) = (fun i => q (u, i)) := by
    intro u hu; funext i; rw [hq₀def]; simp only [ite_eq_right hu]
  -- The hinges of `FG₀` and `Ft` at `e_a` and `e_b`.
  have hFG₀_ea : FG₀.supportExtensor e_a = (-t) • panelSupportExtensor na n' := by
    rw [hFG₀, PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_ends,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal, hends_ea]
    simp only [hq₀v, hq₀a, panelSupportExtensor_add_smul_left]
  have hFG₀_eb : FG₀.supportExtensor e_b = panelSupportExtensor (na + t • n') nb := by
    rw [hFG₀, PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_ends,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal, hends_eb]
    simp only [hq₀v, hq₀b]
  have hFt_eb : Ft.supportExtensor e_b = panelSupportExtensor (na + t • n') nb := by
    rw [hFt, PanelHingeFramework.caseIIICandidate_supportExtensor_reproduced]
  have hFt_ea : Ft.supportExtensor e_a = panelSupportExtensor na n' :=
    PanelHingeFramework.caseIIICandidate_supportExtensor_candidate G ends q na n' nb t heab
  -- At an edge of `Gᵥ`, `Ft` and `FG₀` have the `ofNormals G ends q` extensor (its endpoints avoid
  -- `v`).
  have hGv_seed_eq : ∀ {e u w}, Gv.IsLink e u w →
      Ft.supportExtensor e = FG₀.supportExtensor e := by
    intro e u w hlink
    obtain ⟨hne_a, hne_b⟩ := hGv_off hlink
    -- the *recorded* endpoints of `e` lie in `V(Gᵥ)` (via `hends_Gv`), so both avoid `v`, hence
    -- `q₀` agrees with `q` at each.
    have hrec := hends_Gv e u w hlink
    have hfst : (ends e).1 ≠ v := fun h => hvVc (h ▸ hrec.left_mem)
    have hsnd : (ends e).2 ≠ v := fun h => hvVc (h ▸ hrec.right_mem)
    simp only [hFt, PanelHingeFramework.caseIIICandidate_supportExtensor_of_ne G ends q e_a e_b na
        n' nb t hne_a hne_b, hFG₀, PanelHingeFramework.toBodyHinge_supportExtensor,
      PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal,
      hq₀_off (ends e).1 hfst, hq₀_off (ends e).2 hsnd]
  -- `FG₀.graph = G` definitionally (`toBodyHinge_graph`/`ofNormals_graph` are `rfl`), so a `G`-link
  -- is an `FG₀`-link and `panelRow_mem_rigidityRows_of_link` applies directly.
  have hFG₀_eq_panelRow : ∀ {e u w} (t₁ t₂ : Set.powersetCard (Fin (k + 2)) k),
      ends e = (u, w) → Ft.supportExtensor e = FG₀.supportExtensor e →
      Ft.panelRow ends (e, t₁, t₂) = FG₀.panelRow ends (e, t₁, t₂) := by
    intro e u w t₁ t₂ hends_e hext
    rw [Ft.panelRow_eq_hingeRow_annihRow_of_ends ends hends_e,
      FG₀.panelRow_eq_hingeRow_annihRow_of_ends ends hends_e, hext]
  -- At `e_a`: a row of `Ft` is `(-t)⁻¹ •` a row of `FG₀` (a separate fact, so that the case split
  -- of `hmem` does not substitute `e_a` and `e_b` away).
  have hmem_ea : ∀ t₁ t₂, Ft.panelRow ends (e_a, t₁, t₂) ∈ Submodule.span K FG₀.rigidityRows := by
    intro t₁ t₂
    have hFtrow : Ft.panelRow ends (e_a, t₁, t₂)
        = BodyHingeFramework.hingeRow v a (annihRow (panelSupportExtensor na n') t₁ t₂) := by
      rw [Ft.panelRow_eq_hingeRow_annihRow_of_ends ends hends_ea, hFt_ea]
    have hFG₀row : FG₀.panelRow ends (e_a, t₁, t₂)
        = (-t) • BodyHingeFramework.hingeRow v a (annihRow (panelSupportExtensor na n') t₁ t₂) := by
      rw [FG₀.panelRow_eq_hingeRow_annihRow_of_ends ends hends_ea, hFG₀_ea, annihRow_smul,
        BodyHingeFramework.hingeRow_eq_dualMap, map_smul, ← BodyHingeFramework.hingeRow_eq_dualMap]
    have hmem_genuine : FG₀.panelRow ends (e_a, t₁, t₂) ∈ Submodule.span K FG₀.rigidityRows :=
      Submodule.subset_span (FG₀.panelRow_mem_rigidityRows_of_link ends hends_ea hG_ea t₁ t₂)
    rw [hFtrow,
      show BodyHingeFramework.hingeRow v a (annihRow (panelSupportExtensor na n') t₁ t₂)
        = (-t)⁻¹ • FG₀.panelRow ends (e_a, t₁, t₂) from by
          simp only [hFG₀row, smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr ht_ne), one_smul]]
    exact Submodule.smul_mem _ _ hmem_genuine
  -- Each of the rows of `Ft` lies in `span FG₀.rigidityRows`.
  have hmem : ∀ i : ↥s, Ft.panelRow ends (i : β × _ × _) ∈ Submodule.span K FG₀.rigidityRows := by
    rintro ⟨⟨e, t₁, t₂⟩, hi⟩
    have hlink : G.IsLink e (ends e).1 (ends e).2 := hs_link _ hi
    change Ft.panelRow ends (e, t₁, t₂) ∈ Submodule.span K FG₀.rigidityRows
    rcases hsplitG e (ends e).1 (ends e).2 hlink with he | he | hGv
    · -- `e = e_a`: by `hmem_ea`.
      rw [he]; exact hmem_ea t₁ t₂
    · -- `e = e_b`: the hinges agree, so it is a row of `FG₀`.
      rw [he, hFG₀_eq_panelRow t₁ t₂ hends_eb (by rw [hFt_eb, hFG₀_eb])]
      exact Submodule.subset_span (FG₀.panelRow_mem_rigidityRows_of_link ends hends_eb hG_eb t₁ t₂)
    · -- An edge of `Gᵥ`: the hinges agree (`hGv_seed_eq`), so it is a row of `FG₀`.
      rw [hFG₀_eq_panelRow t₁ t₂ (Prod.mk.eta (p := ends e)) (hGv_seed_eq hGv)]
      exact Submodule.subset_span (FG₀.panelRow_mem_rigidityRows_of_link ends
        (Prod.mk.eta (p := ends e)) (hleG e _ _ (hends_Gv e _ _ hGv)) t₁ t₂)
  -- (v) Rigidity on `V(G)` at `q₀`, then a generic full-rank realization.
  have hsub : Submodule.span K
      (Set.range (fun i : ↥s => Ft.panelRow ends (i : β × _ × _)))
      ≤ Submodule.span K FG₀.rigidityRows := by
    rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact hmem i
  have hFG₀graph : FG₀.graph.vertexSet = V(G) := by
    rw [hFG₀, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]
  have hcard_s : screwDim k * (V(G).ncard - 1) ≤ Nat.card ↥s := hs_card.ge
  -- Feed the lemma at its own `FG₀.graph.vertexSet` shape (via `hFG₀graph`), then read the
  -- conclusion back as `V(G)` — `FG₀.graph = G` by `rfl`, so no defeq-check forces the heavy
  -- framework at `q₀` open (TACTICS-QUIRKS §38).
  -- `hne` at `q₀`: the hinges at links are nonzero (`e_a ↦ (-t)·C(L)`, `e_b ↦ C(na + t·n', nb)`, an
  -- edge of `Gᵥ` by `hne_Gv`, as `Ft` and `FG₀` agree there).
  have hne_q₀ : ∀ e, G.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.supportExtensor e ≠ 0 := by
    intro e hlink
    rw [show (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge = FG₀ from hFG₀.symm]
    rcases hsplitG e (ends e).1 (ends e).2 hlink with he | he | hGv
    · rw [he, hFG₀_ea]
      exact smul_ne_zero (neg_ne_zero.mpr ht_ne)
        ((panelSupportExtensor_ne_zero_iff na n').mpr hLn)
    · rw [he, hFG₀_eb]; exact (panelSupportExtensor_ne_zero_iff (na + t • n') nb).mpr hnewtrans
    · rw [← hGv_seed_eq hGv]
      obtain ⟨hne_a, hne_b⟩ := hGv_off hGv
      rw [hFt, PanelHingeFramework.caseIIICandidate_supportExtensor_of_ne G ends q e_a e_b na n' nb
        t hne_a hne_b]
      exact hne_Gv e (hends_Gv e _ _ hGv)
  -- (v) Rigidity on `V(G)` at `q₀` — generalize the heavy `Ft.panelRow`-family to a plain `f` so
  -- the `_of_span_le_rigidityRows` application never `whnf`s the `caseIIICandidate` carrier
  -- (TACTICS-QUIRKS §38), then a generic full-rank realization.
  rw [hFG₀] at hsub
  set f : ↥s → Module.Dual K (α → ScrewSpace K k) := fun i => Ft.panelRow ends (i : β × _ × _)
    with hf_def
  clear_value f
  have hG : (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.graph.vertexSet = V(G) := rfl
  have hrig :=
    BodyHingeFramework.isInfinitesimallyRigidOn_vertexSet_of_span_le_rigidityRows
      (F := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge)
      ht_li hsub (by rw [hG]; exact hnev) (by rw [hG]; exact hcard_s)
  rw [hG] at hrig
  exact PanelHingeFramework.hasGenericFullRankRealization_of_rigidOn_ofNormals G ends hends_q₀
    hne_q₀ hnev hrig n hdef

/-- **The count at `(G, p_1)`, then the rotation** (a step of `lem:case-III-candidate-dispatch-d3`
and `lem:case-III-chain-dispatch`): under the hypotheses of `case_III_realization_of_rank` but
`hrank`, with `|V(G)| = |V(Gv)| + 1 ≥ 2`, let `ρ` be a linear form with `ρ(C(q(a), n')) ≠ 0`
(`hρgate`) and `ρ(C(q(a), q(b))) = 0` (`hρe₀`), such that the row `hingeRow a b ρ` lies in the span
of the rows of `ofNormals Gv ends q` (`hρGv`), and let `w` be `D(|V(Gv)| − 1)` linearly independent
forms, each a row of `ofNormals Gv ends q` or a form `hingeRow a b ρ'` with `ρ'(C(q(a), q(b))) = 0`
(`hwmem`). If `G` has deficiency `0`, it has a generic full-rank realization.

`case_III_rank_certification` (`lem:case-III-rank-certification`) gives `F_0` the rank
`D(|V(G)| − 1)`. This is the count of KT eq. (6.29) at `(G, p_1)`: "if the top-left 6 × 6-submatrix
of (6.29) has full rank, then rank R(G, p1) = 6(|V| − 1)" (KT p. 684). Then
`case_III_realization_of_rank` rotates the panel of `v`. Its users are
`case_III_arm_realization_M2`, `case_III_arm_realization_M3` (`CaseIII/Relabel/Arm.lean`), the proof
of the case `d = 3` (`case_III_candidate_dispatch`) and three steps of the case of a chain
(`CaseIII/Realization.lean`). -/
theorem PanelHingeFramework.case_III_arm_realization [Infinite K]
    [Finite α] [Finite β]
    (G Gv : Graph α β) (ends : β → α × α) {q : α × Fin (k + 2) → K}
    {v a b : α} {e_a e_b : β}
    (hvVc : v ∉ V(Gv)) (haVc : a ∈ V(Gv)) (hbVc : b ∈ V(Gv))
    (hG_ea : G.IsLink e_a v a) (hG_eb : G.IsLink e_b v b)
    (hends_ea : ends e_a = (v, a)) (hends_eb : ends e_b = (v, b)) (heab : e_a ≠ e_b)
    (hleG : ∀ e u w, Gv.IsLink e u w → G.IsLink e u w)
    (hsplitG : ∀ e u w, G.IsLink e u w → e = e_a ∨ e = e_b ∨ Gv.IsLink e u w)
    (hends_Gv : ∀ e u w, Gv.IsLink e u w → Gv.IsLink e (ends e).1 (ends e).2)
    (hne_Gv : ∀ e, Gv.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.supportExtensor e ≠ 0)
    (hVone : 1 ≤ V(Gv).ncard) (hVcard : V(G).ncard = V(Gv).ncard + 1)
    {n' : Fin (k + 2) → K}
    (hLn : LinearIndependent K ![(fun i => q (a, i)), n'])
    (hgab : LinearIndependent K ![(fun i => q (a, i)), (fun i => q (b, i))])
    {ρ : Module.Dual K (ScrewSpace K k)}
    (hρgate : ρ (panelSupportExtensor (fun i => q (a, i)) n') ≠ 0)
    (hρe₀ : ρ (panelSupportExtensor (fun i => q (a, i)) (fun i => q (b, i))) = 0)
    (hρGv : BodyHingeFramework.hingeRow a b ρ ∈ Submodule.span K
      (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows)
    {ιb : Type*} [Finite ιb] {w : ιb → Module.Dual K (α → ScrewSpace K k)}
    (hwcard : Nat.card ιb = screwDim k * (V(Gv).ncard - 1))
    (hw : LinearIndependent K w)
    (hwmem : ∀ j, w j ∈ (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows ∨
      ∃ ρ' : Module.Dual K (ScrewSpace K k),
        ρ' (panelSupportExtensor (fun i => q (a, i)) (fun i => q (b, i))) = 0 ∧
        w j = BodyHingeFramework.hingeRow a b ρ')
    {n : ℕ} (hdef : G.deficiency n = 0) :
    PanelHingeFramework.HasGenericFullRankRealization K k n G := by
  classical
  -- (i) The rank bound of KT eq. (6.29) at `F₀`, by `case_III_rank_certification`; then
  -- `case_III_realization_of_rank`, which does not depend on how the rank was found, rotates the
  -- panel of `v`.
  have hrank : screwDim k * (V(G).ncard - 1)
      ≤ Module.finrank K (Submodule.span K
        (PanelHingeFramework.caseIIICandidate G ends q e_a e_b
          (fun i => q (a, i)) n' (fun i => q (b, i)) 0).rigidityRows) :=
    PanelHingeFramework.case_III_rank_certification G Gv ends hvVc haVc hbVc hG_ea hG_eb
      hends_ea heab hleG hVone hVcard hLn hρgate hρe₀ hρGv hwcard hw hwmem
  exact PanelHingeFramework.case_III_realization_of_rank G Gv ends hvVc haVc hbVc hG_ea hG_eb
    hends_ea hends_eb heab hleG hsplitG hends_Gv hne_Gv hLn hgab hrank hdef

/-- **The same with `a` and `b` exchanged** (a step of `lem:case-III-candidate-dispatch-d3` and
`lem:case-III-chain-dispatch`): `case_III_arm_realization` with the line in the panel of `b`
(`hLn : q(b), n''` linearly independent, `hρgate : ρ(C(q(b), n'')) ≠ 0`), where `ρ`, `hρe₀`, `hρGv`
and the forms `w` are those of `case_III_arm_realization`, at `ab`. The framework is Katoh and
Tanigawa's second, `(G, p_2)` of KT eq. (6.19) (p. 682), whose count is
`lem:case-III-claim612-p2-placement`; it takes the same coefficients and index: "the same λ(ab)j, 1
≤ j ≤ 5 and the index `i*` are used in (6.29) and (6.30)" (KT p. 686). Its last row "is indeed equal
to r" (KT p. 681); the form here is `−ρ` only as `hingeRow b a` reverses the order of the ends of
`ab`.

The proof applies `case_III_arm_realization` with `a, e_a` and `b, e_b` exchanged and the form `−ρ`:
as `hingeRow a b ρ = hingeRow b a (−ρ)` (`hingeRow_swap`) and `C(q(b), q(a)) = −C(q(a), q(b))`
(`panelSupportExtensor_swap`), the hypotheses hold in the exchanged roles, and a form
`hingeRow a b ρ'` of `w` is `hingeRow b a (−ρ')`. Its users are the proof of the case `d = 3`
(`case_III_candidate_dispatch`) and a step of the case of a chain
(`chainData_dispatch_floor_of_discriminator`). -/
theorem PanelHingeFramework.case_III_arm_realization_M2 [Infinite K]
    [Finite α] [Finite β]
    (G Gv : Graph α β) (ends : β → α × α) {q : α × Fin (k + 2) → K}
    {v a b : α} {e_a e_b : β}
    (hvVc : v ∉ V(Gv)) (haVc : a ∈ V(Gv)) (hbVc : b ∈ V(Gv))
    (hG_ea : G.IsLink e_a v a) (hG_eb : G.IsLink e_b v b)
    (hends_ea : ends e_a = (v, a)) (hends_eb : ends e_b = (v, b)) (heab : e_a ≠ e_b)
    (hleG : ∀ e u w, Gv.IsLink e u w → G.IsLink e u w)
    (hsplitG : ∀ e u w, G.IsLink e u w → e = e_a ∨ e = e_b ∨ Gv.IsLink e u w)
    (hends_Gv : ∀ e u w, Gv.IsLink e u w → Gv.IsLink e (ends e).1 (ends e).2)
    (hne_Gv : ∀ e, Gv.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.supportExtensor e ≠ 0)
    (hVone : 1 ≤ V(Gv).ncard) (hVcard : V(G).ncard = V(Gv).ncard + 1)
    {n'' : Fin (k + 2) → K}
    -- the line `L' ⊂ Π(b)`: `n''` and the normal of `b` are linearly independent
    (hLn : LinearIndependent K ![(fun i => q (b, i)), n''])
    (hgab : LinearIndependent K ![(fun i => q (a, i)), (fun i => q (b, i))])
    {ρ : Module.Dual K (ScrewSpace K k)}
    -- `ρ` does not vanish on the hinge `C(q(b), n'')` of `L'`
    (hρgate : ρ (panelSupportExtensor (fun i => q (b, i)) n'') ≠ 0)
    (hρe₀ : ρ (panelSupportExtensor (fun i => q (a, i)) (fun i => q (b, i))) = 0)
    (hρGv : BodyHingeFramework.hingeRow a b ρ ∈ Submodule.span K
      (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows)
    {ιb : Type*} [Finite ιb] {w : ιb → Module.Dual K (α → ScrewSpace K k)}
    (hwcard : Nat.card ιb = screwDim k * (V(Gv).ncard - 1))
    (hw : LinearIndependent K w)
    (hwmem : ∀ j, w j ∈ (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows ∨
      ∃ ρ' : Module.Dual K (ScrewSpace K k),
        ρ' (panelSupportExtensor (fun i => q (a, i)) (fun i => q (b, i))) = 0 ∧
        w j = BodyHingeFramework.hingeRow a b ρ')
    {n : ℕ} (hdef : G.deficiency n = 0) :
    PanelHingeFramework.HasGenericFullRankRealization K k n G := by
  classical
  -- Apply `case_III_arm_realization` with `a ↔ b`, `e_a ↔ e_b` and `-ρ`, as
  -- `hingeRow a b ρ = hingeRow b a (-ρ)`.
  refine PanelHingeFramework.case_III_arm_realization (k := k) G Gv ends
    hvVc hbVc haVc hG_eb hG_ea hends_eb hends_ea heab.symm hleG
    (fun e u w hlink => by
      rcases hsplitG e u w hlink with h | h | h
      exacts [Or.inr (Or.inl h), Or.inl h, Or.inr (Or.inr h)])
    hends_Gv hne_Gv hVone hVcard hLn (LinearIndependent.pair_symm_iff.mp hgab)
    (ρ := -ρ) ?_ ?_ ?_ (ιb := ιb) (w := w) hwcard hw ?_ hdef
  -- `hρgate`: `(-ρ)(panelSupportExtensor n_b n'') ≠ 0` from `hρgate` (negation on the functional).
  · rw [LinearMap.neg_apply, neg_ne_zero]; exact hρgate
  -- `hρe₀`: `(-ρ)(panelSupportExtensor n_b n_a) = 0` from `hρe₀` via `panelSupportExtensor_swap`.
  · rw [LinearMap.neg_apply, panelSupportExtensor_swap, map_neg, hρe₀, neg_zero, neg_zero]
  -- `hρGv`: `hingeRow b a (-ρ) ∈ span` is `hingeRow a b ρ ∈ span` (`hingeRow_swap`).
  · rwa [← BodyHingeFramework.hingeRow_swap]
  -- `hwmem`: each `ρ'`-tagged member converts to `-ρ'` (`hingeRow b a (-ρ') = hingeRow a b ρ'`;
  -- the annihilation swaps the normals and negates the functional).
  · intro j
    rcases hwmem j with hgen | ⟨ρ', hρ'e₀, hwj⟩
    · exact Or.inl hgen
    · exact Or.inr ⟨-ρ', by rw [LinearMap.neg_apply, panelSupportExtensor_swap, map_neg, hρ'e₀,
        neg_zero, neg_zero], by rw [hwj, ← BodyHingeFramework.hingeRow_swap]⟩

/-! ## The triangle and the cycle

KT Lemma 6.7(i) for the triangle (`lem:triangle-realization`) and KT Lemma 5.4 for the cycles on at
most `d + 1` vertices (`lem:cycle-realization`). The proof of `lem:case-III` uses the second for the
triangle too, as the cycle on three vertices. -/

/-- **A triangle has a generic full-rank realization** (`lem:triangle-realization`; KT Lemma 6.7(i),
p. 677): let `bodyBarDim n ≥ 3` and `k ≥ 1`, let `G` be a simple minimal `0`-dof-graph with three
vertices, and let `eₐ ≠ e_b` link a vertex `v` to vertices `a, b ≠ v`. Then `G` has a generic
full-rank realization. The proof of `lem:case-III` realizes the triangle by `cycle_realization`
instead, and no main result uses this lemma.

The proof. `Graph.exists_isLink_of_isMinimalKDof_card_three` (`lem:triangle-third-edge`) gives
`a ≠ b`, `V(G) = {v, a, b}` and an edge `f` that joins `a` and `b`. `exists_triangle_normals`
(`lem:triangle-normals`) gives normals `n₀, n₁, n₂` with nonzero joins whose extensors `C(n₀, n₁)`,
`C(n₁, n₂)` and `C(n₂, n₀)` are linearly independent. Let `q₀` give `v`, `a` and `b` these normals
and every other body `0`. The selector `G.endsOf` orients each edge, and the support extensor of
each edge of the triangle is ± one of the three extensors (the unit scalar from the `endsOf`
orientation; `Graph.endsOf_eq_or_swap`, `panelSupportExtensor_swap`), so the three hinges are
linearly independent and every hinge at a link is nonzero. `theorem_55_triangle`
(`lem:theorem-55-triangle`) gives rigidity on `{v, a, b} = V(G)`, and
`hasGenericFullRankRealization_of_rigidOn_ofNormals` (`lem:generic-realization-of-rigid`) the
realization. -/
theorem PanelHingeFramework.hasGenericFullRankRealization_of_triangle [Infinite K]
    [DecidableEq β] [Finite α] [Finite β] {n : ℕ} (G : Graph α β) [G.Simple]
    (hD : 3 ≤ Graph.bodyBarDim n) (hk : 1 ≤ k)
    (hG : G.IsMinimalKDof n 0)
    (hcard : V(G).ncard = 3)
    {v a b : α} {eₐ e_b : β}
    (hG_ea : G.IsLink eₐ v a) (hG_eb : G.IsLink e_b v b)
    (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b) :
    PanelHingeFramework.HasGenericFullRankRealization K k n G := by
  classical
  -- `V(G) = {v, a, b}` and the third edge (`lem:triangle-third-edge`).
  obtain ⟨hab, hVeq, f, hf⟩ :=
    Graph.exists_isLink_of_isMinimalKDof_card_three hD hG hcard hG_ea hG_eb heab
  -- The normals of `lem:triangle-normals`: linearly independent cyclic extensors, nonzero joins.
  obtain ⟨n₀, n₁, n₂, ⟨hn₀₁, hn₁₂, hn₂₀⟩, hLI⟩ := exists_triangle_normals (K := K) (k := k) hk
  -- Convert that fun-form LI to the `![C₀,C₁,C₂]` matrix form.
  -- `fun i => panelSupportExtensor (![n₀,n₁,n₂] i) (![n₁,n₂,n₀] i)` equals
  -- `![C₀, C₁, C₂]` where `Cᵢ = panelSupportExtensor` of those pairs.
  have hLI' : LinearIndependent K
      ![panelSupportExtensor (k := k) n₀ n₁, panelSupportExtensor n₁ n₂,
        panelSupportExtensor n₂ n₀] := by
    have heq : (![panelSupportExtensor (k := k) n₀ n₁, panelSupportExtensor n₁ n₂,
        panelSupportExtensor n₂ n₀] : Fin 3 → _) =
        fun i => panelSupportExtensor (![n₀, n₁, n₂] i) (![n₁, n₂, n₀] i) := by
      funext i; fin_cases i <;> rfl
    rw [heq]; exact hLI
  -- Derive `panelSupportExtensor nᵢ nⱼ ≠ 0` from the nonzero joins.
  have hne₀₁ : panelSupportExtensor (k := k) n₀ n₁ ≠ 0 :=
    (panelSupportExtensor_ne_zero_iff n₀ n₁).mpr ((normalsJoin_ne_zero_iff n₀ n₁).mp hn₀₁)
  have hne₁₂ : panelSupportExtensor (k := k) n₁ n₂ ≠ 0 :=
    (panelSupportExtensor_ne_zero_iff n₁ n₂).mpr ((normalsJoin_ne_zero_iff n₁ n₂).mp hn₁₂)
  have hne₂₀ : panelSupportExtensor (k := k) n₂ n₀ ≠ 0 :=
    (panelSupportExtensor_ne_zero_iff n₂ n₀).mpr ((normalsJoin_ne_zero_iff n₂ n₀).mp hn₂₀)
  -- `G.endsOf` needs `Inhabited α`.
  have : Inhabited α := ⟨v⟩
  -- The normals `q₀`: `v ↦ n₀`, `a ↦ n₁`, `b ↦ n₂`, and `0` elsewhere.
  let q₀ : α × Fin (k + 2) → K :=
    fun p => if p.1 = v then n₀ p.2 else if p.1 = a then n₁ p.2 else if p.1 = b then n₂ p.2 else 0
  -- Normal evaluations: q₀ at the three vertices (pointwise, used below).
  have hq₀v : ∀ i, q₀ (v, i) = n₀ i := fun i => by simp [q₀]
  have hq₀a : ∀ i, q₀ (a, i) = n₁ i := fun i => by
    simp only [q₀]; split_ifs with h1
    · exact absurd h1 hav
    · rfl
  have hq₀b : ∀ i, q₀ (b, i) = n₂ i := fun i => by
    simp only [q₀]; split_ifs with h1 h2
    · exact absurd h1 hbv
    · exact absurd h2.symm hab
    · rfl
  -- Equalities of functions `Fin(k+2) → K` at the three bodies (for support extensor rewriting).
  have hfn_v : (fun i => q₀ (v, i)) = n₀ := funext hq₀v
  have hfn_a : (fun i => q₀ (a, i)) = n₁ := funext hq₀a
  have hfn_b : (fun i => q₀ (b, i)) = n₂ := funext hq₀b
  set F := (PanelHingeFramework.ofNormals (k := k) G G.endsOf q₀).toBodyHinge with hFdef
  -- Raw support extensor formula for `F`.
  have hsupp_raw : ∀ e : β,
      F.supportExtensor e = panelSupportExtensor (fun i => q₀ ((G.endsOf e).1, i))
        (fun i => q₀ ((G.endsOf e).2, i)) := fun e => by
    simp only [hFdef, PanelHingeFramework.toBodyHinge_supportExtensor,
               PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal]
  -- Support extensor at `eₐ` (link `v-a`): either `panelSupportExtensor n₀ n₁` or its negative.
  have hsupp_ea : F.supportExtensor eₐ = panelSupportExtensor n₀ n₁ ∨
      F.supportExtensor eₐ = -panelSupportExtensor n₀ n₁ := by
    rcases G.endsOf_eq_or_swap hG_ea with heo | heo
    · exact Or.inl (by simp only [hsupp_raw, heo, hfn_v, hfn_a])
    · exact Or.inr (by rw [hsupp_raw, heo, hfn_a, hfn_v, panelSupportExtensor_swap])
  -- Support extensor at `f` (link `a-b`): either `panelSupportExtensor n₁ n₂` or its negative.
  have hsupp_f : F.supportExtensor f = panelSupportExtensor n₁ n₂ ∨
      F.supportExtensor f = -panelSupportExtensor n₁ n₂ := by
    rcases G.endsOf_eq_or_swap hf with heo | heo
    · exact Or.inl (by simp only [hsupp_raw, heo, hfn_a, hfn_b])
    · exact Or.inr (by rw [hsupp_raw, heo, hfn_b, hfn_a, panelSupportExtensor_swap])
  -- Support extensor at `e_b` (link `v-b`): either `panelSupportExtensor n₂ n₀` or its negative.
  -- The cyclic family is `n₀n₁, n₁n₂, n₂n₀`; `v-b` gives `n₀n₂ = -(n₂n₀)` or `n₂n₀`.
  have hsupp_eb : F.supportExtensor e_b = panelSupportExtensor n₂ n₀ ∨
      F.supportExtensor e_b = -panelSupportExtensor n₂ n₀ := by
    rcases G.endsOf_eq_or_swap hG_eb with heo | heo
    · exact Or.inr (by rw [hsupp_raw, heo, hfn_v, hfn_b, panelSupportExtensor_swap])
    · exact Or.inl (by simp only [hsupp_raw, heo, hfn_b, hfn_v])
  -- `hne`: every linking edge has nonzero support extensor.
  -- Use `hsupp_raw`, case-split on endpoint membership in V(G)={v,a,b}, apply pairwise nonzero.
  have hne : ∀ e, G.IsLink e (G.endsOf e).1 (G.endsOf e).2 →
      F.supportExtensor e ≠ 0 := by
    intro e hlink
    have hne12 : (G.endsOf e).1 ≠ (G.endsOf e).2 := G.endsOf_fst_ne_snd hlink.edge_mem
    have hmem1 : (G.endsOf e).1 ∈ V(G) := hlink.left_mem
    have hmem2 : (G.endsOf e).2 ∈ V(G) := hlink.right_mem
    rw [hVeq] at hmem1 hmem2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem1 hmem2
    rw [hsupp_raw]
    -- Case-split on membership using named hypotheses, then rewrite via hfn_*.
    rcases hmem1 with h1 | h1 | h1 <;> rcases hmem2 with h2 | h2 | h2
    · exact absurd (h1.trans h2.symm) hne12
    · rw [show (fun i => q₀ ((G.endsOf e).1, i)) = n₀ from by rw [h1]; exact hfn_v,
          show (fun i => q₀ ((G.endsOf e).2, i)) = n₁ from by rw [h2]; exact hfn_a]
      exact hne₀₁
    · rw [show (fun i => q₀ ((G.endsOf e).1, i)) = n₀ from by rw [h1]; exact hfn_v,
          show (fun i => q₀ ((G.endsOf e).2, i)) = n₂ from by rw [h2]; exact hfn_b,
          panelSupportExtensor_swap]
      exact neg_ne_zero.mpr hne₂₀
    · rw [show (fun i => q₀ ((G.endsOf e).1, i)) = n₁ from by rw [h1]; exact hfn_a,
          show (fun i => q₀ ((G.endsOf e).2, i)) = n₀ from by rw [h2]; exact hfn_v,
          panelSupportExtensor_swap]
      exact neg_ne_zero.mpr hne₀₁
    · exact absurd (h1.trans h2.symm) hne12
    · rw [show (fun i => q₀ ((G.endsOf e).1, i)) = n₁ from by rw [h1]; exact hfn_a,
          show (fun i => q₀ ((G.endsOf e).2, i)) = n₂ from by rw [h2]; exact hfn_b]
      exact hne₁₂
    · rw [show (fun i => q₀ ((G.endsOf e).1, i)) = n₂ from by rw [h1]; exact hfn_b,
          show (fun i => q₀ ((G.endsOf e).2, i)) = n₀ from by rw [h2]; exact hfn_v]
      exact hne₂₀
    · rw [show (fun i => q₀ ((G.endsOf e).1, i)) = n₂ from by rw [h1]; exact hfn_b,
          show (fun i => q₀ ((G.endsOf e).2, i)) = n₁ from by rw [h2]; exact hfn_a,
          panelSupportExtensor_swap]
      exact neg_ne_zero.mpr hne₁₂
    · exact absurd (h1.trans h2.symm) hne12
  -- `hgen`: the three extensors of the edges of the triangle are linearly independent.
  -- Each is ± one member of the cyclic family `![C₀,C₁,C₂]`; negation preserves LI via
  -- `LinearIndependent.units_smul_iff`: `w • v` is LI ↔ `v` is LI (w units).
  have hgen : LinearIndependent K
      ![F.supportExtensor eₐ, F.supportExtensor f, F.supportExtensor e_b] := by
    -- Helper: `![-C₀, -C₁, -C₂]`-type sign flips preserve LI.
    have hLI_neg : ∀ (ε₀ ε₁ ε₂ : Kˣ),
        LinearIndependent K
          (fun i : Fin 3 =>
            ![ε₀ • panelSupportExtensor (k := k) n₀ n₁,
              ε₁ • panelSupportExtensor n₁ n₂,
              ε₂ • panelSupportExtensor n₂ n₀] i) := by
      intro ε₀ ε₁ ε₂
      have : (fun i : Fin 3 =>
            ![ε₀ • panelSupportExtensor (k := k) n₀ n₁,
              ε₁ • panelSupportExtensor n₁ n₂,
              ε₂ • panelSupportExtensor n₂ n₀] i) =
          (![ε₀, ε₁, ε₂]) • (![panelSupportExtensor (k := k) n₀ n₁,
              panelSupportExtensor n₁ n₂, panelSupportExtensor n₂ n₀]) := by
        funext i; fin_cases i <;> rfl
      rw [this]
      exact (LinearIndependent.units_smul_iff _ _).mpr hLI'
    rcases hsupp_ea with hea | hea <;> rcases hsupp_f with hf' | hf' <;>
        rcases hsupp_eb with heb | heb <;>
      rw [hea, hf', heb]
    · exact hLI'
    · have h := hLI_neg 1 1 (Units.mk0 (-1 : K) (by norm_num))
      convert h using 1; funext i; fin_cases i <;> (first | rfl | simp)
    · have h := hLI_neg 1 (Units.mk0 (-1 : K) (by norm_num)) 1
      convert h using 1; funext i; fin_cases i <;> (first | rfl | simp)
    · have h := hLI_neg 1 (Units.mk0 (-1 : K) (by norm_num)) (Units.mk0 (-1 : K) (by norm_num))
      convert h using 1; funext i; fin_cases i <;> (first | rfl | simp)
    · have h := hLI_neg (Units.mk0 (-1 : K) (by norm_num)) 1 1
      convert h using 1; funext i; fin_cases i <;> (first | rfl | simp)
    · have h := hLI_neg (Units.mk0 (-1 : K) (by norm_num)) 1 (Units.mk0 (-1 : K) (by norm_num))
      convert h using 1; funext i; fin_cases i <;> (first | rfl | simp)
    · have h := hLI_neg (Units.mk0 (-1 : K) (by norm_num)) (Units.mk0 (-1 : K) (by norm_num)) 1
      convert h using 1; funext i; fin_cases i <;> (first | rfl | simp)
    · have h := hLI_neg (Units.mk0 (-1 : K) (by norm_num)) (Units.mk0 (-1 : K) (by norm_num))
            (Units.mk0 (-1 : K) (by norm_num))
      convert h using 1; funext i; fin_cases i <;> rfl
  -- Rigidity on `{v, a, b}` (`theorem_55_triangle`).
  have hFgraph : F.graph = G := by
    simp only [hFdef, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]
  have hrigVAB : F.IsInfinitesimallyRigidOn {v, a, b} :=
    BodyHingeFramework.theorem_55_triangle F hgen
      (hFgraph ▸ hG_ea) (hFgraph ▸ hf) (hFgraph ▸ hG_eb.symm)
  -- `V(G) = {v, a, b}`, and a generic full-rank realization.
  have hrig : F.IsInfinitesimallyRigidOn V(G) := by rwa [hVeq]
  exact PanelHingeFramework.hasGenericFullRankRealization_of_rigidOn_ofNormals G G.endsOf
    (fun e u w he => G.isLink_endsOf he.edge_mem) hne
    ⟨v, hG_ea.left_mem⟩ hrig n hG.1

/-- **A cycle has a generic full-rank realization** (`lem:cycle-realization`; KT Lemma 5.4, p. 670):
let `bodyBarDim n = D` (`hn`), and let `G` be a minimal `0`-dof-graph that is a cycle `cy` on
`m ≤ n + 1` vertices (`Graph.CycleData`). Then `G` has a generic full-rank realization. Katoh and
Tanigawa state Lemma 5.4 for `3 ≤ m ≤ D`; the range `m ≤ d + 1` here (`n = d`) covers their uses,
the triangle in the proof of KT Lemma 6.7(i) (p. 677) and the cycles on at most `d` vertices in the
proof of KT Lemma 6.13 (p. 692), and the proof of `lem:case-III` applies it to the same cycles (the
note after the node). For the computation in dimension `3` Katoh and Tanigawa refer to Crapo and
Whiteley 1982 (Proposition 3.4) and to Whiteley 1999 (Proposition 3).

The proof. As `bodyBarDim n = screwDim k`, `n = k + 1`
(`Graph.eq_add_one_of_bodyBarDim_eq_screwDim`), so `m ≤ k + 2`, and `exists_cycle_normals`
(`lem:cycle-normals`) gives `m` normals with nonzero consecutive joins whose consecutive extensors
are linearly independent. Let `q₀` give the `i`-th vertex the `i`-th normal and every other body `0`
(`Function.extend`). Each cycle edge's support extensor is
`± panelSupportExtensor (nrm i) (nrm (i+1))` (`endsOf_eq_or_swap` + `panelSupportExtensor_swap`,
`choose`-packaged as unit scalars), so the hinges are linearly independent
(`LinearIndependent.units_smul_iff`), and every link of `G` is an edge of the cycle
(`CycleData.edge_surj`), with a nonzero hinge. `theorem_55_cycle` (`lem:cycle-realization-rigid`)
gives rigidity on the vertices of the cycle, which are `V(G)` (`CycleData.range_vtx`), and
`hasGenericFullRankRealization_of_rigidOn_ofNormals` (`lem:generic-realization-of-rigid`) the
realization. Only `case_III_hsplit_producer_all_k` uses it. -/
theorem PanelHingeFramework.cycle_realization [Infinite K]
    [DecidableEq β] [Finite α] [Finite β] {n : ℕ}
    (hn : Graph.bodyBarDim n = screwDim k)
    {G : Graph α β} (hG : G.IsMinimalKDof n 0)
    (cy : G.CycleData) (hm : cy.m ≤ n + 1) :
    PanelHingeFramework.HasGenericFullRankRealization K k n G := by
  classical
  have hm3 : 3 ≤ cy.m := cy.hm
  have : NeZero cy.m := ⟨by omega⟩
  have : Inhabited α := ⟨cy.vtx 0⟩
  -- The successor `⟨1, _⟩` of the record is the numeral `1` of `Fin cy.m`.
  have hlink : ∀ i : Fin cy.m, G.IsLink (cy.edge i) (cy.vtx i) (cy.vtx (i + 1)) := by
    intro i
    have h := cy.link i
    rwa [show (⟨1, by omega⟩ : Fin cy.m) = 1 from
      Fin.ext (by rw [Fin.val_one']; exact (Nat.mod_eq_of_lt (by omega)).symm)] at h
  -- `n = k + 1` from `hn`, so `cy.m ≤ k + 2`.
  have hnk : n = k + 1 := Graph.eq_add_one_of_bodyBarDim_eq_screwDim hn
  -- The normals of `lem:cycle-normals`.
  obtain ⟨nrm, hjoin, hLI⟩ := exists_cycle_normals (K := K) (k := k) hm3 (by omega : cy.m ≤ k + 2)
  -- The normals `q₀`: `cy.vtx i ↦ nrm i`, and `0` elsewhere (`Function.extend`, by
  -- `CycleData.vtx_inj`).
  let q₀ : α × Fin (k + 2) → K := fun p => Function.extend cy.vtx nrm (fun _ => 0) p.1 p.2
  have hfn : ∀ i : Fin cy.m, (fun j => q₀ (cy.vtx i, j)) = nrm i := fun i =>
    cy.vtx_inj.extend_apply nrm (fun _ => 0) i
  set F := (PanelHingeFramework.ofNormals (k := k) G G.endsOf q₀).toBodyHinge with hFdef
  -- Raw support extensor formula for `F`.
  have hsupp_raw : ∀ e : β,
      F.supportExtensor e = panelSupportExtensor (fun i => q₀ ((G.endsOf e).1, i))
        (fun i => q₀ ((G.endsOf e).2, i)) := fun e => by
    simp only [hFdef, PanelHingeFramework.toBodyHinge_supportExtensor,
               PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal]
  -- Per-edge sign facts: each cycle edge's extensor is a unit multiple of the extensor of
  -- `lem:cycle-normals`.
  have hsupp : ∀ i : Fin cy.m, ∃ ε : Kˣ, F.supportExtensor (cy.edge i)
      = ε • panelSupportExtensor (nrm i) (nrm (i + 1)) := by
    intro i
    rcases G.endsOf_eq_or_swap (hlink i) with heo | heo
    · exact ⟨1, by simp only [hsupp_raw, heo, hfn, one_smul]⟩
    · refine ⟨Units.mk0 (-1 : K) (by norm_num), ?_⟩
      rw [hsupp_raw, heo, hfn, hfn, panelSupportExtensor_swap, Units.smul_def, Units.val_mk0,
        neg_one_smul]
  choose ε hε using hsupp
  -- `hgen` for `theorem_55_cycle`: the hinges of the cycle are linearly independent.
  have hgen : LinearIndependent K fun i : Fin cy.m => F.supportExtensor (cy.edge i) := by
    have hEq : (fun i : Fin cy.m => F.supportExtensor (cy.edge i))
        = ε • fun i : Fin cy.m => panelSupportExtensor (nrm i) (nrm (i + 1)) := by
      funext i
      rw [Pi.smul_apply']
      exact hε i
    rw [hEq, LinearIndependent.units_smul_iff]
    exact hLI
  -- `hne`: every linking edge is a cycle edge (`edge_surj`), with nonzero extensor.
  have hne : ∀ e, G.IsLink e (G.endsOf e).1 (G.endsOf e).2 →
      F.supportExtensor e ≠ 0 := by
    intro e he
    obtain ⟨i, rfl⟩ := cy.edge_surj e he.edge_mem
    rw [hε i, Units.smul_def]
    exact smul_ne_zero (Units.ne_zero _)
      ((panelSupportExtensor_ne_zero_iff _ _).mpr
        ((normalsJoin_ne_zero_iff _ _).mp (hjoin i)))
  -- Rigidity on `Set.range cy.vtx = V(G)` (`theorem_55_cycle`).
  have hFgraph : F.graph = G := by
    simp only [hFdef, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]
  have hlinkF : ∀ i : Fin cy.m, F.graph.IsLink (cy.edge i) (cy.vtx i) (cy.vtx (i + 1)) := by
    rw [hFgraph]; exact hlink
  have hrig : F.IsInfinitesimallyRigidOn V(G) := by
    have h := F.theorem_55_cycle cy.vtx cy.edge hlinkF hgen
    rwa [cy.range_vtx] at h
  -- A generic full-rank realization.
  exact PanelHingeFramework.hasGenericFullRankRealization_of_rigidOn_ofNormals G G.endsOf
    (fun e u w he => G.isLink_endsOf he.edge_mem) hne
    ⟨cy.vtx 0, (hlink 0).left_mem⟩ hrig n hG.1

/-! ## The proof of `lem:case-III` from its case of a chain -/

/-- **Case III from its case of a chain** (a step of `lem:case-III`): let `bodyBarDim n = D ≥ 3`
(`hD`, `hn`), and let `G` be a simple minimal `0`-dof-graph with `|V(G)| ≥ 3`, no proper rigid
subgraph and an edge label outside `E(G)` (`hfresh`). Suppose that every minimal `0`-dof-graph with
at least two and fewer than `|V(G)|` vertices has a panel realization, and a generic full-rank
realization if it is simple (`hIH`), and that `G` has a generic full-rank realization whenever the
graph split off from a chain `cd` of length `n` (`Graph.ChainData`) at `v₁` along `v₀v₂` has
deficiency `0` and a generic full-rank realization (`hcand`). Then `G` has a generic full-rank
realization. The proof of `lem:case-III` (`case_III_realization_all_k`) applies it with `hcand` from
`chainData_dispatch` (`lem:case-III-chain-dispatch`).

The proof, as in the proof of `lem:case-III`. If `|V(G)| = 3`, some vertex `v` has degree two
(`Graph.exists_degree_eq_two_of_noRigid`), with edges to `a` and `b`
(`Graph.exists_splitOff_data_of_degree_eq_two`, given another vertex of `G`), and `G` is the cycle
on `v`, `a` and `b` (`Graph.CycleData.ofCardThree`), which `cycle_realization` realizes, as
`3 ≤ n + 1`. If `|V(G)| ≥ 4`, `Graph.chainData_extract` (`lem:chain-data-extract`) gives a chain of
length `n` whose split-off graph is a simple minimal `0`-dof-graph with at least two and fewer
vertices, to which `hIH` gives the realization `hcand` takes, or shows that `G` is a cycle on at
most `n` vertices, which `cycle_realization` realizes. -/
theorem PanelHingeFramework.case_III_hsplit_producer_all_k
    [Infinite K] [DecidableEq β] [Finite α] [Finite β]
    {n : ℕ} (hD : 3 ≤ Graph.bodyBarDim n)
    (hn : Graph.bodyBarDim n = screwDim k) (G : Graph α β)
    -- `G`: a minimal `0`-dof-graph with at least three vertices and no proper rigid subgraph
    (hG : G.IsMinimalKDof n 0) (hV3 : 3 ≤ V(G).ncard)
    (hnoRigid : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n)
    (hsimple : G.Simple)
    (hIH : ∀ G' : Graph α β, G'.IsMinimalKDof n 0 → 2 ≤ V(G').ncard →
      V(G').ncard < V(G).ncard →
      (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization K k n G') ∧
        HasPanelRealization K k n G')
    -- an edge label outside `E(G)`, for the new edge `v₀v₂` of the chain
    -- (`Graph.chainData_extract` returns it as `cd.e₀`)
    (hfresh : ∃ e₀ : β, e₀ ∉ E(G))
    -- the case of a chain: a generic full-rank realization of the graph split off at `v₁`
    -- along `v₀v₂`, of deficiency `0`, gives one of `G` (`chainData_dispatch` proves it in the
    -- proof of `lem:case-III`)
    (hcand : ∀ (cd : G.ChainData n) (hd2 : 2 ≤ cd.d),
      (G.splitOff (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨0, by omega⟩)
        (cd.vtx ⟨2, by omega⟩) cd.e₀).deficiency n = 0 →
      PanelHingeFramework.HasGenericFullRankRealization K k n
        (G.splitOff (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨0, by omega⟩)
          (cd.vtx ⟨2, by omega⟩) cd.e₀) →
      PanelHingeFramework.HasGenericFullRankRealization K k n G) :
    PanelHingeFramework.HasGenericFullRankRealization K k n G := by
  classical
  have hD3 : 3 ≤ Graph.bodyBarDim n := by omega
  have hD2 : 2 ≤ Graph.bodyBarDim n := by omega
  have hD1 : 1 ≤ Graph.bodyBarDim n := by omega
  have := hsimple
  -- On `|V(G)|`: the triangle (`= 3`), or `|V(G)| ≥ 4`.
  rcases eq_or_lt_of_le hV3 with hV3eq | hV4
  · -- **The triangle (`|V(G)| = 3`).** A vertex of degree two and its two edges; then
    -- `CycleData.ofCardThree` gives `G` as the cycle on three vertices, which
    -- `cycle_realization` realizes (KT Lemma 5.4 at `m = 3`).
    have hcard3 : V(G).ncard = 3 := hV3eq.symm
    -- A vertex `v` of degree two (`D ≥ 3`), and any other vertex `a`, which
    -- `exists_splitOff_data_of_degree_eq_two` needs.
    obtain ⟨v, hvG, hdegv⟩ := Graph.exists_degree_eq_two_of_noRigid hD (by omega) hG hnoRigid
    obtain ⟨a, haG, hav⟩ : ∃ a ∈ V(G), a ≠ v := by
      by_contra hcon
      push Not at hcon
      have hsub : V(G) ⊆ {v} := fun x hx => hcon x hx
      have hle := Set.ncard_le_ncard hsub (Set.finite_singleton v)
      rw [Set.ncard_singleton] at hle
      omega
    obtain ⟨a', b, eₐ', e_b, -, -, ha'G, hbG, heab', hlea', hleb, _⟩ :=
      Graph.exists_splitOff_data_of_degree_eq_two hD1 hG.1 hvG haG hav hdegv
    -- `cy.m = 3 ≤ n + 1` since `n ≥ 2` (from `3 ≤ bodyBarDim n = D`).
    have hn2 : 3 ≤ n + 1 := by
      by_contra h
      have h' : n < 2 := by omega
      have hb := hD
      simp only [Graph.bodyBarDim] at hb
      interval_cases n <;> omega
    exact PanelHingeFramework.cycle_realization hn hG
      (Graph.CycleData.ofCardThree hD3 hG hcard3 hlea' hleb heab') hn2
  · -- **`|V(G)| ≥ 4`.** `Graph.chainData_extract` (`lem:chain-data-extract`) gives a chain of
    -- length `n`, whose graph split off at `v₁` is minimal, simple and smaller, or shows that
    -- `G` is a cycle on at most `n` vertices.
    have hV4' : 4 ≤ V(G).ncard := hV4
    rcases Graph.chainData_extract hD hG hfresh hV4' hnoRigid with
      ⟨cd, hd2, hGv, hGvSimple, hGv2, hGvlt⟩ | ⟨cy, hcym⟩
    · -- A chain: `hIH` gives the split-off graph a generic full-rank realization, its first
      -- conjunct, as the graph is simple; then `hcand`.
      have hsplitGP : PanelHingeFramework.HasGenericFullRankRealization K k n
          (G.splitOff (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) cd.e₀) :=
        (hIH _ hGv hGv2 hGvlt).1 hGvSimple
      exact hcand cd hd2 hGv.1 hsplitGP
    · -- A cycle (`4 ≤ |V(G)| ≤ n`): `cycle_realization` realizes `G`, as `cy.m ≤ n ≤ n + 1`.
      exact PanelHingeFramework.cycle_realization hn hG cy (by omega)

end CombinatorialRigidity.Molecular
