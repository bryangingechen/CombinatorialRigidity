/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.AlgebraicInduction.CaseIII.Candidate

/-!
# The algebraic induction — Case III arm realizations (M₁ / M₂, triangle base, producer spine)

Phase 22 (molecular-conjecture program). The arm-realization layer of the Case-III block
(`CaseIII/` subdirectory; the post-Phase-22l molecular split round, `notes/Phase22l-perf.md`). On
top of the candidate built and certified in `CaseIII/Candidate`, this file carries the
certify-then-rebase arm closers `case_III_arm_realization` (W7 = M₁) /
`case_III_arm_realization_M2` (W8 = M₂), the `Sum.elim` index/packaging glue, the per-line
realization, the `|V| = 3` triangle base (`hasGenericFullRankRealization_of_triangle`), and the
triangle-vs-chain producer dichotomy spine (`case_III_hsplit_producer`). The M₃ arm + relabel
transport is in `CaseIII/Relabel`; the dispatch + capstone in `CaseIII/Realization`.

See `ROADMAP.md` §22 and the `sec:molecular-algebraic-induction-caseIII` dep-graph in
`blueprint/src/chapter/algebraic-induction/case-iii.tex`.
-/

namespace CombinatorialRigidity.Molecular

variable {k : ℕ}

open scoped Graph

variable {α β : Type*}

/-! ## Case III arms M₁ / M₂, the triangle base, and the producer spine

The certify-then-rebase arm closers (W7 = M₁, W8 = M₂), the `Sum.elim` index/packaging glue, the
per-line realization, the `|V| = 3` triangle base (`lem:triangle-realization`), and the
triangle-vs-chain producer dichotomy. -/

/-- **The shared rank-to-realization tail of the Case-III arm** (`lem:case-III`, the W6e–W6f +
GAP-2/GAP-3 stratum of the certify-then-rebase route; Katoh–Tanigawa 2011 §6.4.1, eq. (6.29)→(6.30),
design §1.51(a)/(h), Phase 22h/23c). This is the part of `case_III_arm_realization` that depends
**only** on the candidate rank bound `hrank` (KT's (6.29) full-rank certification of the `t = 0`
candidate framework `F₀ = caseIIICandidate G ends q e_a e_b (q(a,·)) n' (q(b,·)) 0`) and the
split/seed data — *not* on how that rank was certified. Factored out so the two certifications share
it verbatim: the landed `d = 3` engine `case_III_arm_realization` (which produces `hrank` via the
`hρGv`-collapse cert `case_III_rank_certification`) and the forked general-`d` chain arm
`case_III_arm_realization_chain` (which produces `hrank` via the `±r` block-rank-additivity cert
`case_III_rank_certification_chain`, NO `hρGv`; design §(o‴)(I.8.24)(3), the SHARED W6a–W6f tail).

The route, from `hrank`: (ii) W6e re-extracts from the rank a *literal* `F₀.panelRow` family of
exactly `D(|V(G)|−1)` linking edges (each an `annihRow`-of-the-edge-extensor row, polynomial in the
shear). (iii) W6f transfers that family along the one-parameter `t`-family `F(t)` to a good
`t^* ≠ 0` outside the GAP-3 bad set, keeping it linearly independent and forcing
`![n_a + t^*·n', n_b]` independent. (iv) Each `F(t^*)`-slot lies in
`span (ofNormals G ends q₀).rigidityRows` (`q₀` shears `v` along `n_a + t^*·n'`; the candidate
`e_a`-slot is `(-1/t^*) •` the genuine `e_a`-row). (v)
`isInfinitesimallyRigidOn_vertexSet_of_span_le_rigidityRows` gives rigidity on `V(G)`, and GAP-2
upgrades it to the generic motive.

**§38:** the only concrete carrier reached is `ofNormals G ends q₀` in (iv)–(v); every extensor
evaluation goes through the W6a simp lemmas plus `toBodyHinge_supportExtensor`/`ofNormals_normal`
and the funext-`if_neg` `q₀`-override pattern, and every membership is an explicit link witness (the
`hrow_mem` idiom, never `whnf` on the carrier). -/
theorem PanelHingeFramework.case_III_realization_of_rank
    [Finite α] [Finite β] [DecidableEq β]
    (G Gv : Graph α β) (ends : β → α × α) {q : α × Fin (k + 2) → ℝ}
    {v a b : α} {e_a e_b : β}
    (hvVc : v ∉ V(Gv)) (haVc : a ∈ V(Gv)) (hbVc : b ∈ V(Gv))
    (hG_ea : G.IsLink e_a v a) (hG_eb : G.IsLink e_b v b)
    (hends_ea : ends e_a = (v, a)) (hends_eb : ends e_b = (v, b)) (heab : e_a ≠ e_b)
    (hleG : ∀ e u w, Gv.IsLink e u w → G.IsLink e u w)
    (hsplitG : ∀ e u w, G.IsLink e u w → e = e_a ∨ e = e_b ∨ Gv.IsLink e u w)
    (hends_Gv : ∀ e u w, Gv.IsLink e u w → Gv.IsLink e (ends e).1 (ends e).2)
    (hne_Gv : ∀ e, Gv.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.supportExtensor e ≠ 0)
    {n' : Fin (k + 2) → ℝ}
    (hLn : LinearIndependent ℝ ![(fun i => q (a, i)), n'])
    (hgab : LinearIndependent ℝ ![(fun i => q (a, i)), (fun i => q (b, i))])
    (hrank : screwDim k * (V(G).ncard - 1)
      ≤ Module.finrank ℝ (Submodule.span ℝ
        (PanelHingeFramework.caseIIICandidate G ends q e_a e_b
          (fun i => q (a, i)) n' (fun i => q (b, i)) 0).rigidityRows))
    {n : ℕ} (hdef : G.deficiency n = 0) :
    PanelHingeFramework.HasGenericFullRankRealization k n G := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  set na := (fun i => q (a, i)) with hna
  set nb := (fun i => q (b, i)) with hnb
  have hva : v ≠ a := fun h => hvVc (h ▸ haVc)
  have hvb : v ≠ b := fun h => hvVc (h ▸ hbVc)
  have hnev : V(G).Nonempty := ⟨v, hG_ea.left_mem⟩
  -- (i) The (6.29) rank lower bound at the `t = 0` candidate framework `F₀` (supplied as `hrank`).
  set F₀ := PanelHingeFramework.caseIIICandidate G ends q e_a e_b na n' nb 0 with hF₀
  -- The candidate / reproduced extensors at `F₀` (W6a simp lemmas), and their nonvanishing.
  have hsuppea : F₀.supportExtensor e_a = panelSupportExtensor na n' :=
    PanelHingeFramework.caseIIICandidate_supportExtensor_candidate G ends q na n' nb 0 heab
  have hsuppeb : F₀.supportExtensor e_b = panelSupportExtensor na nb := by
    rw [hF₀, PanelHingeFramework.caseIIICandidate_supportExtensor_reproduced, zero_smul, add_zero]
  -- (ii) W6e at `F₀`: the rank re-extracts that many literal linking `F₀.panelRow`s.
  -- `hends` at `F₀.graph = G`: every `G`-link is `e_a`, `e_b`, or a `Gᵥ`-link (`hsplitG`).
  have hF₀graph : F₀.graph = G := by rw [hF₀]; exact PanelHingeFramework.caseIIICandidate_graph ..
  -- `hends`/`hne` at `G` (= `F₀.graph` definitionally), shared by W6e and the GAP-2 close.
  have hends_q₀ : ∀ e u w, G.IsLink e u w → G.IsLink e (ends e).1 (ends e).2 := by
    intro e u w hlink
    rcases hsplitG e u w hlink with he | he | hGv
    · rw [he, hends_ea]; exact hG_ea
    · rw [he, hends_eb]; exact hG_eb
    · exact hleG e _ _ (hends_Gv e u w hGv)
  have hends_G : ∀ e u w, F₀.graph.IsLink e u w → F₀.graph.IsLink e (ends e).1 (ends e).2 :=
    hF₀graph ▸ hends_q₀
  -- `hne` on linking edges: `e_a ↦ C(L) ≠ 0` (`hLn`), `e_b ↦ C(e₀) ≠ 0` (`hgab`), `Gᵥ` via `hne_Gv`
  -- + extensor agreement off `{e_a, e_b}`.
  have hGv_off : ∀ {e u w}, Gv.IsLink e u w → e ≠ e_a ∧ e ≠ e_b := by
    intro e u w hlink
    have hune : u ≠ v := fun h => hvVc (h ▸ hlink.left_mem)
    have hwne : w ≠ v := fun h => hvVc (h ▸ hlink.right_mem)
    have hGlink := hleG e u w hlink
    refine ⟨fun he => ?_, fun he => ?_⟩
    · subst he
      rcases (hG_ea).eq_and_eq_or_eq_and_eq hGlink with ⟨hh, _⟩ | ⟨hh, _⟩
      · exact hune hh.symm
      · exact hwne hh.symm
    · subst he
      rcases (hG_eb).eq_and_eq_or_eq_and_eq hGlink with ⟨hh, _⟩ | ⟨hh, _⟩
      · exact hune hh.symm
      · exact hwne hh.symm
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
  -- (iii) W6f: transfer the re-extracted family to a good `t^* ≠ 0` outside the GAP-3 bad set.
  haveI : Finite ↥s := Set.Finite.to_subtype (Set.toFinite s)
  set bad : Finset ℝ :=
    (setOf_not_shear_linearIndependent_subsingleton na n' nb hgab).finite.toFinset with hbad
  obtain ⟨t, ht_bad, ht_ne, ht_li⟩ :=
    PanelHingeFramework.caseIIICandidate_exists_good_shear G ends q heab na n' nb
      (ι := ↥s) (fun i => (i : β × _ × _)) (by rw [← hF₀]; exact hs_indep) bad
  -- `t ∉ bad` forces `![na + t·n', nb]` independent (the reproduced `vb`-hinge stays transversal).
  have hnewtrans : LinearIndependent ℝ ![na + t • n', nb] := by
    by_contra hdep
    refine ht_bad ?_
    rw [hbad, Set.Finite.mem_toFinset]
    exact hdep
  -- (iv) The sheared seed `q₀ : v ↦ na + t·n'`, agreeing with `q` off `v`.
  set Ft := PanelHingeFramework.caseIIICandidate G ends q e_a e_b na n' nb t with hFt
  set q₀ : α × Fin (k + 2) → ℝ := fun p => if p.1 = v then (na + t • n') p.2 else q p with hq₀def
  set FG₀ := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge with hFG₀
  have hq₀v : (fun i => q₀ (v, i)) = na + t • n' := by funext i; rw [hq₀def]; simp
  have hq₀a : (fun i => q₀ (a, i)) = na := by
    funext i; rw [hq₀def, hna]; simp only [if_neg hva.symm]
  have hq₀b : (fun i => q₀ (b, i)) = nb := by
    funext i; rw [hq₀def, hnb]; simp only [if_neg hvb.symm]
  -- Off `v`, `q₀` agrees with `q`, so the `ofNormals G ends q₀` extensor of any edge avoiding `v`
  -- equals the `ofNormals G ends q` one (= `F₀`/`Ft`'s seed off `{e_a, e_b}`).
  have hq₀_off : ∀ u, u ≠ v → (fun i => q₀ (u, i)) = (fun i => q (u, i)) := by
    intro u hu; funext i; rw [hq₀def]; simp only [if_neg hu]
  -- The genuine `FG₀`-extensors at the three relevant kinds of edge.
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
  -- A `Gᵥ`-edge keeps both `Ft` and `FG₀` at the `q`-seed extensor (its endpoints avoid `v`).
  have hGv_seed_eq : ∀ {e u w}, Gv.IsLink e u w →
      Ft.supportExtensor e = FG₀.supportExtensor e := by
    intro e u w hlink
    obtain ⟨hne_a, hne_b⟩ := hGv_off hlink
    -- the *recorded* endpoints of `e` lie in `V(Gᵥ)` (via `hends_Gv`), so both avoid `v`, hence
    -- `q₀` agrees with `q` at each.
    have hrec := hends_Gv e u w hlink
    have hfst : (ends e).1 ≠ v := fun h => hvVc (h ▸ hrec.left_mem)
    have hsnd : (ends e).2 ≠ v := fun h => hvVc (h ▸ hrec.right_mem)
    rw [hFt, PanelHingeFramework.caseIIICandidate_supportExtensor_of_ne G ends q e_a e_b na n' nb t
        hne_a hne_b, hFG₀, PanelHingeFramework.toBodyHinge_supportExtensor,
      PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_ends,
      PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal,
      PanelHingeFramework.ofNormals_normal, hq₀_off (ends e).1 hfst, hq₀_off (ends e).2 hsnd]
  -- `FG₀.graph = G` definitionally (`toBodyHinge_graph`/`ofNormals_graph` are `rfl`), so a `G`-link
  -- is an `FG₀`-link and `panelRow_mem_rigidityRows_of_link` applies directly.
  have hFG₀_eq_panelRow : ∀ {e u w} (t₁ t₂ : Set.powersetCard (Fin (k + 2)) k),
      ends e = (u, w) → Ft.supportExtensor e = FG₀.supportExtensor e →
      Ft.panelRow ends (e, t₁, t₂) = FG₀.panelRow ends (e, t₁, t₂) := by
    intro e u w t₁ t₂ hends_e hext
    rw [Ft.panelRow_eq_hingeRow_annihRow_of_ends ends hends_e,
      FG₀.panelRow_eq_hingeRow_annihRow_of_ends ends hends_e, hext]
  -- The candidate `e_a`-slot: `Ft`-row is `(-1/t) •` the genuine `FG₀` `e_a`-row (extracted as a
  -- standalone fact to avoid substituting `e_a`/`e_b` away in the `hmem` dispatch).
  have hmem_ea : ∀ t₁ t₂, Ft.panelRow ends (e_a, t₁, t₂) ∈ Submodule.span ℝ FG₀.rigidityRows := by
    intro t₁ t₂
    have hFtrow : Ft.panelRow ends (e_a, t₁, t₂)
        = BodyHingeFramework.hingeRow v a (annihRow (panelSupportExtensor na n') t₁ t₂) := by
      rw [Ft.panelRow_eq_hingeRow_annihRow_of_ends ends hends_ea, hFt_ea]
    have hFG₀row : FG₀.panelRow ends (e_a, t₁, t₂)
        = (-t) • BodyHingeFramework.hingeRow v a (annihRow (panelSupportExtensor na n') t₁ t₂) := by
      rw [FG₀.panelRow_eq_hingeRow_annihRow_of_ends ends hends_ea, hFG₀_ea, annihRow_smul,
        BodyHingeFramework.hingeRow_eq_dualMap, map_smul, ← BodyHingeFramework.hingeRow_eq_dualMap]
    have hmem_genuine : FG₀.panelRow ends (e_a, t₁, t₂) ∈ Submodule.span ℝ FG₀.rigidityRows :=
      Submodule.subset_span (FG₀.panelRow_mem_rigidityRows_of_link ends hends_ea hG_ea t₁ t₂)
    rw [hFtrow,
      show BodyHingeFramework.hingeRow v a (annihRow (panelSupportExtensor na n') t₁ t₂)
        = (-t)⁻¹ • FG₀.panelRow ends (e_a, t₁, t₂) from by
          rw [hFG₀row, smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr ht_ne), one_smul]]
    exact Submodule.smul_mem _ _ hmem_genuine
  -- Membership of each `Ft`-slot in `span FG₀.rigidityRows`.
  have hmem : ∀ i : ↥s, Ft.panelRow ends (i : β × _ × _) ∈ Submodule.span ℝ FG₀.rigidityRows := by
    rintro ⟨⟨e, t₁, t₂⟩, hi⟩
    have hlink : G.IsLink e (ends e).1 (ends e).2 := hs_link _ hi
    change Ft.panelRow ends (e, t₁, t₂) ∈ Submodule.span ℝ FG₀.rigidityRows
    rcases hsplitG e (ends e).1 (ends e).2 hlink with he | he | hGv
    · -- `e = e_a`: the candidate slot, via `hmem_ea`.
      rw [he]; exact hmem_ea t₁ t₂
    · -- `e = e_b`: the reproduced slot, extensors agree so it is a genuine `FG₀`-row.
      rw [he, hFG₀_eq_panelRow t₁ t₂ hends_eb (by rw [hFt_eb, hFG₀_eb])]
      exact Submodule.subset_span (FG₀.panelRow_mem_rigidityRows_of_link ends hends_eb hG_eb t₁ t₂)
    · -- A `Gᵥ`-slot: extensors agree (`hGv_seed_eq`), so `Ft`-row is a genuine `FG₀`-row.
      rw [hFG₀_eq_panelRow t₁ t₂ (Prod.mk.eta (p := ends e)) (hGv_seed_eq hGv)]
      exact Submodule.subset_span (FG₀.panelRow_mem_rigidityRows_of_link ends
        (Prod.mk.eta (p := ends e)) (hleG e _ _ (hends_Gv e _ _ hGv)) t₁ t₂)
  -- (v) Rigidity on `V(G)` at `q₀`, then GAP-2 upgrades to the generic motive.
  have hsub : Submodule.span ℝ
      (Set.range (fun i : ↥s => Ft.panelRow ends (i : β × _ × _)))
      ≤ Submodule.span ℝ FG₀.rigidityRows := by
    rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact hmem i
  have hFG₀graph : FG₀.graph.vertexSet = V(G) := by
    rw [hFG₀, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]
  have hcard_s : screwDim k * (V(G).ncard - 1) ≤ Nat.card ↥s := hs_card.ge
  -- Feed the lemma at its own `FG₀.graph.vertexSet` shape (via `hFG₀graph`), then read the
  -- conclusion back as `V(G)` — `FG₀.graph = G` by `rfl`, so no defeq-check forces the heavy
  -- `q₀`-seed open (TACTICS-QUIRKS §38).
  -- GAP-2 `hne` at `q₀`: the linking-edge extensors are nonzero (`e_a ↦ (-t)·C(L)`, `e_b ↦ C(e₀)`
  -- at the sheared `vb`, `Gᵥ` via `hne_Gv` through the `Ft`/`FG₀` extensor agreement).
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
  -- the `_of_span_le_rigidityRows` application never `whnf`s the `caseIIICandidate` carrier (§38),
  -- then GAP-2 upgrades to the generic motive.
  rw [hFG₀] at hsub
  set f : ↥s → Module.Dual ℝ (α → ScrewSpace k) := fun i => Ft.panelRow ends (i : β × _ × _)
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

/-- **W7 — the M₁ arm closer: certify-then-rebase realizes the `d = 3` candidate at full rank**
(`lem:case-II-realization` / `lem:case-III`, the role-parametric arm of the `hcand` discharge;
Katoh–Tanigawa 2011 §6.4.1, eqs. (6.29)/(6.30), the certify-then-rebase route of design
§1.51(a)/(h),
Phase 22h). Given the unpacked split context — fresh body `v ∉ V(Gᵥ)` joined to `a, b ∈ V(Gᵥ)` by
the two re-inserted hinges `e_a = va`, `e_b = vb`, the IH-rigid old subgraph `Gᵥ`, the witness
second normal `n'` of `Π(a)` with its transversality data (`hLn`, `hgab`), and W6b's candidate /
bottom-row package (`ρ`, `w`) — produces `HasGenericFullRankRealization k G`.

The route is KT's own reading of eq. (6.29) ("if the top-left `6×6` block is full rank then
`rank R(G,p₁) = 6(|V|−1)`", p. 684), a statement about the *rank* of `R(G,p₁)`, not a distinguished
row family. (i) W6d certifies the (6.29) count at the hinge-level framework
`F₀ := caseIIICandidate G ends q e_a e_b n_a n' n_b 0` as the rank bound
`D(|V(G)|−1) ≤ finrank (span F₀.rigidityRows)`. (ii) W6e re-extracts from that rank a *literal*
`F₀.panelRow` family of exactly `D(|V(G)|−1)` linking edges — each slot an
`annihRow`-of-the-edge-extensor row, polynomial in the shear. (iii) W6f transfers that family along
the one-parameter `t`-family `F(t)` to a good `t^* ≠ 0` outside the GAP-3 bad set
(`setOf_not_shear_linearIndependent_subsingleton`), keeping it linearly independent and forcing
`![n_a + t^*·n', n_b]` independent (the reproduced `vb`-hinge stays transversal). (iv) Each
`F(t^*)`-slot lies in `span (ofNormals G ends q₀).rigidityRows`, where `q₀` shears `v` along
`n_a + t^*·n'`: the `e_b`-slot and the `Gᵥ`-slots have extensors *equal* to the sheared seed's (the
`e_b`-normals are `(n_a + t^*·n', n_b)` exactly; the `Gᵥ`-endpoints avoid `v`), so they are genuine
rows, while the candidate `e_a`-slot is `(-1/t^*) •` the genuine `e_a`-row
(`panelSupportExtensor_add_smul_left` makes the sheared `e_a`-extensor `(-t^*) • C(L)`, `annihRow`
linear in the extensor scales the row, and `t^* ≠ 0` inverts). (v)
`isInfinitesimallyRigidOn_vertexSet_of_span_le_rigidityRows` gives rigidity on `V(G)` at
`ofNormals G ends q₀`, and GAP-2 `hasGenericFullRankRealization_of_rigidOn_ofNormals` upgrades
to the generic motive.

Role-parametric over `(v, a, b, e_a, e_b, n')` so that W8 (the M₂ arm) is the instantiation at the
swapped roles `a ↔ b` with `ρ' := -ρ`. **§38:** the only concrete carrier reached is
`ofNormals G ends q₀` in (iv)–(v); every extensor evaluation goes through the W6a simp lemmas plus
`toBodyHinge_supportExtensor`/`ofNormals_normal` and the funext-`if_neg` `q₀`-override pattern, and
every membership is an explicit link witness (the `hrow_mem` idiom, never `whnf` on the carrier). -/
theorem PanelHingeFramework.case_III_arm_realization
    [Finite α] [Finite β]
    (G Gv : Graph α β) (ends : β → α × α) {q : α × Fin (k + 2) → ℝ}
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
    {n' : Fin (k + 2) → ℝ}
    (hLn : LinearIndependent ℝ ![(fun i => q (a, i)), n'])
    (hgab : LinearIndependent ℝ ![(fun i => q (a, i)), (fun i => q (b, i))])
    {ρ : Module.Dual ℝ (ScrewSpace k)}
    (hρgate : ρ (panelSupportExtensor (fun i => q (a, i)) n') ≠ 0)
    (hρe₀ : ρ (panelSupportExtensor (fun i => q (a, i)) (fun i => q (b, i))) = 0)
    (hρGv : BodyHingeFramework.hingeRow a b ρ ∈ Submodule.span ℝ
      (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows)
    {ιb : Type*} [Finite ιb] {w : ιb → Module.Dual ℝ (α → ScrewSpace k)}
    (hwcard : Nat.card ιb = screwDim k * (V(Gv).ncard - 1))
    (hw : LinearIndependent ℝ w)
    (hwmem : ∀ j, w j ∈ (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows ∨
      ∃ ρ' : Module.Dual ℝ (ScrewSpace k),
        ρ' (panelSupportExtensor (fun i => q (a, i)) (fun i => q (b, i))) = 0 ∧
        w j = BodyHingeFramework.hingeRow a b ρ')
    {n : ℕ} (hdef : G.deficiency n = 0) :
    PanelHingeFramework.HasGenericFullRankRealization k n G := by
  classical
  -- (i) W6d: the (6.29) rank lower bound at the `t = 0` candidate framework `F₀` via the
  -- `hρGv`-collapse certification `case_III_rank_certification`. Then the SHARED
  -- rank-to-realization tail (`case_III_realization_of_rank`, W6e–W6f + GAP-2/GAP-3) closes — it is
  -- agnostic to how the rank was certified, so the forked general-`d` arm reuses it verbatim
  -- (design §(o‴)(I.8.24)(3)).
  have hrank : screwDim k * (V(G).ncard - 1)
      ≤ Module.finrank ℝ (Submodule.span ℝ
        (PanelHingeFramework.caseIIICandidate G ends q e_a e_b
          (fun i => q (a, i)) n' (fun i => q (b, i)) 0).rigidityRows) :=
    PanelHingeFramework.case_III_rank_certification G Gv ends hvVc haVc hbVc hG_ea hG_eb
      hends_ea hends_eb heab hleG hVone hVcard hLn hρgate hρe₀ hρGv hwcard hw hwmem
  exact PanelHingeFramework.case_III_realization_of_rank G Gv ends hvVc haVc hbVc hG_ea hG_eb
    hends_ea hends_eb heab hleG hsplitG hends_Gv hne_Gv hLn hgab hrank hdef

/-- **W8 — the M₂ arm closer: the candidate at `e_b` realizes the `d = 3` framework at full rank**
(`lem:case-II-realization` / `lem:case-III`, the second of the three `hcand`-discharge arms;
Katoh–Tanigawa 2011 §6.4.1, eq. (6.42)'s `M₂ = (r(L'); r̂)`, the swapped-role instantiation of
design §1.51(i), Phase 22h). The M₂ arm carries the candidate line `L' ⊂ Π(b)` (the second
normal `n''` of body `b`'s panel), so the witness gate sits at the `b`-side
(`hρgate : ρ (panelSupportExtensor n_b n'') ≠ 0`, the `u = 1` discriminator branch). Everything
tied to the inductive `(ab)`-row — the candidate functional `ρ`, its annihilation `ρ(C(e₀)) = 0`,
its `Gᵥ`-row membership `hingeRow a b ρ ∈ span`, and the bottom family `w` — is **identical** to
W7's (KT p. 686: "the same `λ_{(ab)j}` and the index `i^*` are used"), so W10 feeds both arms from
one W6b invocation; only `hLn`/`hρgate` move to the `b`-side.

This is a pure instantiation of `case_III_arm_realization` at the swapped roles
`(a, b, e_a, e_b, n') := (b, a, e_b, e_a, n'')`, feeding `ρ' := -ρ`: the swapped-role candidate
functional is `-ρ` because `r̂ = hingeRow a b ρ = hingeRow b a (-ρ)` (`hingeRow_swap`) — a
Lean-orientation artifact, not a KT discrepancy (KT p. 681: "`r'` is indeed equal to `r`"; the
row content is identical). The hypothesis conversions are `hingeRow_swap`, `LinearMap.neg_apply`
(the functional-side `(-ρ) x = -(ρ x)`) + `panelSupportExtensor_swap` + `map_neg`, and
`LinearIndependent.pair_symm_iff`. Graph-free over the carrier (it only reorders data and rewrites
functionals); the §38 trap lives inside W7. -/
theorem PanelHingeFramework.case_III_arm_realization_M2
    [Finite α] [Finite β]
    (G Gv : Graph α β) (ends : β → α × α) {q : α × Fin (k + 2) → ℝ}
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
    {n'' : Fin (k + 2) → ℝ}
    -- the candidate line `L' ⊂ Π(b)`: the witness normal `n''` is transversal to `n_b`
    (hLn : LinearIndependent ℝ ![(fun i => q (b, i)), n''])
    (hgab : LinearIndependent ℝ ![(fun i => q (a, i)), (fun i => q (b, i))])
    {ρ : Module.Dual ℝ (ScrewSpace k)}
    -- the gate at the `b`-side line (the `u = 1` discriminator witness)
    (hρgate : ρ (panelSupportExtensor (fun i => q (b, i)) n'') ≠ 0)
    (hρe₀ : ρ (panelSupportExtensor (fun i => q (a, i)) (fun i => q (b, i))) = 0)
    (hρGv : BodyHingeFramework.hingeRow a b ρ ∈ Submodule.span ℝ
      (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows)
    {ιb : Type*} [Finite ιb] {w : ιb → Module.Dual ℝ (α → ScrewSpace k)}
    (hwcard : Nat.card ιb = screwDim k * (V(Gv).ncard - 1))
    (hw : LinearIndependent ℝ w)
    (hwmem : ∀ j, w j ∈ (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows ∨
      ∃ ρ' : Module.Dual ℝ (ScrewSpace k),
        ρ' (panelSupportExtensor (fun i => q (a, i)) (fun i => q (b, i))) = 0 ∧
        w j = BodyHingeFramework.hingeRow a b ρ')
    {n : ℕ} (hdef : G.deficiency n = 0) :
    PanelHingeFramework.HasGenericFullRankRealization k n G := by
  classical
  -- Feed W7 at the swapped roles `a ↔ b`, `e_a ↔ e_b`, with `ρ' := -ρ`. The candidate row content
  -- is invariant: `hingeRow a b ρ = hingeRow b a (-ρ)`.
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

/-- **L5 — the candidate-completion index map is injective** (`lem:case-II-realization` /
`lem:case-III`, the `j`/`Sum.elim` packaging leaf of the `d = 3` `hsplit` producer; Katoh–Tanigawa
2011 §6.4.1, eq. (6.29), Phase 22g). The candidate-completion assembly
(`linearIndependent_sum_{augment,p2,p3}_candidateRow`) outputs a `Sum`-indexed family
`(rn ⊕ {candidate row}) ⊕ ro` over `ι = (sn ⊕ Unit) ⊕ so`; the abstractly-indexed device feed
(`hasFullRankRealization_of_independent_panelRow_index`) consumes it along an injective index map
`j` placing each block index at its `(edge, ⋀ᵏ-pair)`. This certifies that `j` is injective — the
candidate analog of the inline `hjinj` of `case_II_placement_eq612` (which has only the
`sn ⊕ so` two-block split), with the extra `Unit` summand for the candidate row's edge `e_a`.

The `sn`-indices use the new-block edge `e_b` (`hsn_e`); the candidate `Unit`-index uses `e_a`
(the `va`-hinge of the re-inserted body `v`); the `so`-indices use `Gᵥ`-edges, none equal to `e_b`
(`hso_ne_eb`, from `case_III_old_new_blocks`) nor `e_a` (`hso_ne_ea`; both link the fresh body
`v ∉ V(Gᵥ)`). With `e_a ≠ e_b` (`heab`) the three blocks have pairwise-disjoint edge-supports, so
the map is injective: a collision within `sn` or `so` is `Subtype.val`-injectivity, and any
cross-block collision contradicts one of the three disjointness facts on the first coordinate. This
is graph-free over the carrier (it reads only the edge labels), so the recurring `ofNormals`/
`withGraph` defeq trap (TACTICS-QUIRKS §38) does not bite. -/
theorem PanelHingeFramework.candidateCompletion_index_injective
    {sn so : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)}
    {e_a e_b : β} {ta tb : Set.powersetCard (Fin (k + 2)) k} (heab : e_a ≠ e_b)
    (hsn_e : ∀ i ∈ sn, (i : β × _ × _).1 = e_b)
    (hso_ne_eb : ∀ i ∈ so, (i : β × _ × _).1 ≠ e_b)
    (hso_ne_ea : ∀ i ∈ so, (i : β × _ × _).1 ≠ e_a) :
    Function.Injective
      (Sum.elim (Sum.elim (fun i : sn => (i : β × _ × _)) (fun _ : Unit => (e_a, ta, tb)))
        (fun i : so => (i : β × _ × _)) :
        (sn ⊕ Unit) ⊕ so → β × Set.powersetCard (Fin (k + 2)) k
          × Set.powersetCard (Fin (k + 2)) k) := by
  rintro ((⟨in₁, hin₁⟩ | u₁) | ⟨io₁, hio₁⟩) ((⟨in₂, hin₂⟩ | u₂) | ⟨io₂, hio₂⟩) hab <;>
    simp only [Sum.elim_inl, Sum.elim_inr] at hab
  -- `sn` vs `sn`: `Subtype.val` injective.
  · exact congrArg (Sum.inl ∘ Sum.inl) (Subtype.ext hab)
  -- `sn` vs `Unit`: the `sn`-edge `e_b` would equal `e_a`, against `heab`.
  · exact absurd ((hsn_e _ hin₁).symm.trans (congrArg Prod.fst hab)) heab.symm
  -- `sn` vs `so`: the `so`-edge would equal `e_b`, against `hso_ne_eb`.
  · exact absurd ((congrArg Prod.fst hab).symm.trans (hsn_e _ hin₁)) (hso_ne_eb _ hio₂)
  -- `Unit` vs `sn`: symmetric to the `sn` vs `Unit` case.
  · exact absurd ((hsn_e _ hin₂).symm.trans (congrArg Prod.fst hab).symm) heab.symm
  -- `Unit` vs `Unit`: both indices are `()`.
  · rw [Subsingleton.elim u₁ u₂]
  -- `Unit` vs `so`: the `so`-edge would equal `e_a`, against `hso_ne_ea`.
  · exact absurd (congrArg Prod.fst hab).symm (hso_ne_ea _ hio₂)
  -- `so` vs `sn`: symmetric to the `sn` vs `so` case.
  · exact absurd ((congrArg Prod.fst hab).trans (hsn_e _ hin₂)) (hso_ne_eb _ hio₁)
  -- `so` vs `Unit`: symmetric to the `Unit` vs `so` case.
  · exact absurd (congrArg Prod.fst hab) (hso_ne_ea _ hio₁)
  -- `so` vs `so`: `Subtype.val` injective.
  · exact congrArg Sum.inr (Subtype.ext hab)

/-- **L5-pack — the candidate-completion `panelRow ∘ j` family identity and count**
(`lem:case-II-realization` / `lem:case-III`, a packaging leaf for the `d = 3` `hsplit` producer;
Katoh–Tanigawa 2011 §6.4.1, eq. (6.29), Phase 22g). The candidate-completion assembly
(`linearIndependent_sum_{augment,p2,p3}_candidateRow`) outputs the family
`Sum.elim (Sum.elim rn (fun _ : Unit => hingeRow u w ρ)) ro` over `(sn ⊕ Unit) ⊕ so`; this leaf
repackages it as a single `panelRow`-family `fam = fun i => F.panelRow ends (j i)` along an
injective index `j` (the shape a panelRow-shaped device feed would need), supplying both halves
once the three blocks are each a `panelRow`:

* the **OLD/NEW blocks** are `panelRow`s of `F` directly — `rn i = F.panelRow ends i.val` for
  `i : sn` and `ro i = F.panelRow ends i.val` for `i : so` (the L1 `case_III_old_new_blocks` output
  is already in `panelRow` form);
* the **`Unit`-summand candidate row** is the `panelRow` at the candidate edge `e_a` —
  `hingeRow u w ρ = F.panelRow ends (e_a, ta, tb)`, with `ρ = annihRow (C(e_a)) ta tb` and
  `ends e_a = (u, w)`, which is L3 (`panelRow_eq_hingeRow_annihRow_of_ends`). (This resolves the
  §1.34 (F1) subtlety: the producer's `ρ` is realized as a single `annihRow` pair, so the `Unit`
  summand IS one `panelRow`.)

With those, the family is *definitionally* `F.panelRow ends ∘ j` for the L5-inj index map `j`
(`Sum.elim`-of-`Sum.elim` against the matching `j`, closed by `funext`/`rcases`/`rfl`), so the
identity needs no `whnf` of the carrier (graph-free, no TACTICS-QUIRKS §38 trap). The count
`screwDim k * (V(G).ncard − 1) ≤ Nat.card ((sn ⊕ Unit) ⊕ so)` is the L1 block counts
`Nat.card sn = D − 1`, `Nat.card so = D(|V(Gᵥ)|−1)` summed over the `+1` `Unit`, with
`|V(Gᵥ)| = |V(G)| − 1`: `((D−1)+1) + D(m−2) = D(m−1)` for `m = |V(G)| ≥ 1` (the eq. (6.29)
full count `D(|V|−1)`, the `+1` over the eq. (6.12) brick's `D(|V|−1)−1`). -/
theorem PanelHingeFramework.candidateCompletion_panelRow_packaging [Finite β]
    (F : BodyHingeFramework k α β) (ends : β → α × α)
    {sn so : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)}
    {e_a : β} {ta tb : Set.powersetCard (Fin (k + 2)) k} {u w : α}
    {ρ : Module.Dual ℝ (ScrewSpace k)}
    (hends : ends e_a = (u, w)) (hρ : ρ = annihRow (F.supportExtensor e_a) ta tb)
    {mV mVv : ℕ} (hsn_card : Nat.card sn = screwDim k - 1)
    (hso_card : Nat.card so = screwDim k * (mVv - 1)) (hVcard : mVv = mV - 1) (hm : 1 ≤ mV) :
    -- the `panelRow ∘ j` family identity (the device feed's shape)
    (Sum.elim (Sum.elim (fun i : sn => F.panelRow ends (i : β × _ × _))
        (fun _ : Unit => BodyHingeFramework.hingeRow (k := k) (α := α) u w ρ))
      (fun i : so => F.panelRow ends (i : β × _ × _)) =
      fun i => F.panelRow ends
        (Sum.elim (Sum.elim (fun i : sn => (i : β × _ × _)) (fun _ : Unit => (e_a, ta, tb)))
          (fun i : so => (i : β × _ × _)) i)) ∧
    -- the eq. (6.29) full count `D(|V|−1) ≤ |(sn ⊕ Unit) ⊕ so|`
    screwDim k * (mV - 1) ≤ Nat.card ((sn ⊕ Unit) ⊕ so) := by
  refine ⟨?_, ?_⟩
  · -- The `Unit` summand is the panel row at `e_a` (L3); the rest match `j`'s components by `rfl`.
    have hcand : BodyHingeFramework.hingeRow (k := k) (α := α) u w ρ
        = F.panelRow ends (e_a, ta, tb) := by
      rw [F.panelRow_eq_hingeRow_annihRow_of_ends ends hends ta tb, hρ]
    funext i; rcases i with (i | i) | i
    · rfl
    · simp only [Sum.elim_inl, Sum.elim_inr]; exact hcand
    · rfl
  · -- `((D−1)+1) + D(m−2) = D(m−1)` for `m ≥ 1`.
    rw [Nat.card_sum, Nat.card_sum, Nat.card_unique (α := Unit), hsn_card, hso_card, hVcard]
    have hD : 1 ≤ screwDim k := Nat.choose_pos (by omega)
    obtain ⟨m, rfl⟩ : ∃ m, mV = m + 1 := ⟨mV - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    cases m with
    | zero => simp
    | succ m' => rw [Nat.add_sub_cancel, Nat.mul_succ]; omega

/-- **L2b-place (per-line realization) — the line-indexed candidate placement attains a full-rank
realization when the common vector is not orthogonal to the witness line's panel-meet**
(`lem:case-III-claim612-line-in-panel-union`, the C2-feed leaf of the `d = 3` `hsplit` producer;
Katoh–Tanigawa 2011 §6.4.1, eqs.~(6.27)–(6.44), Phase 22g). The graph-free assembly closing the gap
between the per-line independent candidate family (`case_III_full_family_of_line`) and the
realization motive `HasFullRankRealization`: it runs the per-line row-space criterion at `e_a` to
obtain the full `D(|V|−1)` candidate family `Sum.elim (Sum.elim rn {hingeRow v a r}) ro`, then feeds
it straight into the fixed-placement realization brick C1
(`hasFullRankRealization_of_independent_rigidityRow`) — the candidate `+1` row `hingeRow v a r` is
*not* a single `panelRow` (it has `r(C(e_a)) ≠ 0`, while every panelRow annihilates its edge's
extensor), so it cannot route through the panelRow-indexed device feed; but it lies in
`span rigidityRows` (the `hcand_mem` hypothesis, supplied by the consumer via
`hingeRow_mem_rigidityRows` once `r` is restricted to the `e_a`-hinge-row block), exactly C1's
`hsub` shape (§1.35).

The OLD block `ro` (the `D(|V(Gᵥ)|−1)` linking rows) enters abstractly: independent (`holdindep`),
vanishing at `v`'s screw column (`hold`, the per-line criterion's pin input), and members of
`span rigidityRows` (`hro_mem`). The `va`-hinge `e_a` is nondegenerate (`hane`) and the witness
`r(F.supportExtensor e_a) ≠ 0` (`hr`, supplied by Claim~6.12's existential join witness through the
Leaf-2b seed-from-line core) drives both the criterion (the NEW-block `sn`'s candidate-completion is
independent) and C2's selector. The count `D(|V(G)|−1) ≤ |(sn ⊕ Unit) ⊕ ιo|` is the eq.~(6.29) full
count, carried in as `hcard` (the consumer assembles it from the L1 block counts via the L5-pack
arithmetic).

Graph-free over the abstract `F` (it reads only `ends`/`supportExtensor`/`panelRow`/`hingeRow`/
`rigidityRows`); the recurring `ofNormals`/`withGraph` defeq trap (TACTICS-QUIRKS §38) is confined
to the producer's seed feed (Leaf 3), which supplies `F := ofNormals G ends q₀`,
`hane`/`hold`/`holdindep`/`hro_mem`/`hcand_mem`/`hcard`/`hr` at the concrete carrier. -/
theorem PanelHingeFramework.case_III_realization_of_line [DecidableEq α] [Finite α] [Finite β]
    (G : Graph α β) (ends : β → α × α) (hne : V(G).Nonempty)
    {q₀ : α × Fin (k + 2) → ℝ} {v a : α} {e_a : β} (hva : v ≠ a) (hends_ea : ends e_a = (v, a))
    (hG_ea : G.IsLink e_a v a)
    (hane : (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.supportExtensor e_a ≠ 0)
    {ιo : Type*} [Finite ιo] {ro : ιo → Module.Dual ℝ (α → ScrewSpace k)}
    (hold : ∀ (j : ιo) (x : ScrewSpace k), ro j (Function.update (0 : α → ScrewSpace k) v x) = 0)
    (holdindep : LinearIndependent ℝ ro)
    (hro_mem : ∀ j, ro j ∈ Submodule.span ℝ
      (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.rigidityRows)
    (r : Module.Dual ℝ (ScrewSpace k))
    (hcand_mem : BodyHingeFramework.hingeRow (k := k) (α := α) v a r ∈ Submodule.span ℝ
      (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.rigidityRows)
    (hr : r ((PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.supportExtensor e_a) ≠ 0)
    (hcard : ∀ sn : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      Nat.card sn = screwDim k - 1 →
      screwDim k * (V(G).ncard - 1) ≤ Nat.card ((sn ⊕ Unit) ⊕ ιo)) :
    PanelHingeFramework.HasFullRankRealization k G := by
  set F := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge with hF
  -- (1) Run the per-line row-space criterion at `e_a`: the candidate-completion family
  -- `Sum.elim (Sum.elim rn {hingeRow v a r}) ro` is linearly independent (witness `hr`).
  obtain ⟨sn, hsn_e, hsn_card, hfam⟩ :=
    PanelHingeFramework.case_III_full_family_of_line F ends hva hends_ea hane hold holdindep r hr
  haveI : Finite ↥sn := Set.Finite.to_subtype (Set.toFinite sn)
  -- (2) Each row of the family lies in `span rigidityRows`: the `sn`-rows are panelRows of `e_a`
  -- (which links `v a` in `G`, by `hsn_e`/`hends_ea`); the `Unit` candidate row is `hcand_mem`;
  -- the OLD-block rows are `hro_mem`.
  refine PanelHingeFramework.hasFullRankRealization_of_independent_rigidityRow G ends hne
    (q₀ := q₀) hfam ?_ (hcard sn hsn_card)
  rw [Submodule.span_le, Set.range_subset_iff]
  rintro ((⟨i, hi⟩ | u) | i) <;> simp only [Sum.elim_inl, Sum.elim_inr]
  · -- `sn`-row: `panelRow` of `e_a`, a rigidity row by the direct `G`-link `e_a = va`.
    refine Submodule.subset_span ?_
    obtain ⟨e', t₁, t₂⟩ := (i : β × _ × _)
    have hi1 : e' = e_a := hsn_e _ hi
    subst hi1
    exact F.panelRow_mem_rigidityRows_of_link ends hends_ea hG_ea t₁ t₂
  · -- `Unit` candidate row `hingeRow v a r`: the `hcand_mem` hypothesis.
    exact hcand_mem
  · -- OLD-block row: the `hro_mem` hypothesis.
    exact hro_mem i

/-- **Triangle realization, generic motive** (`lem:triangle-realization`, T4; Katoh–Tanigawa 2011
§6.4, KT Lemma 6.7(i) at `m = 3`; Phase 22h). The base of the `d = 3` split-off recursion
for Case~III: a simple minimal `0`-dof-graph on exactly three vertices has the generic-motive
realization `HasGenericFullRankRealization k G`.

**Construction.** T1 (`exists_isLink_of_isMinimalKDof_card_three`) gives `V(G) = {v,a,b}` and
a third edge `f : a–b` completing the triangle. T3 (`exists_triangle_normals`) produces three
normals `n₀, n₁, n₂ ∈ ℝ^(k+2)` with pairwise nonvanishing joins and LI cyclic extensor family
`panelSupportExtensor n₀ n₁, panelSupportExtensor n₁ n₂, panelSupportExtensor n₂ n₀`. The seed
`q₀` assigns `v ↦ n₀`, `a ↦ n₁`, `b ↦ n₂` (junk elsewhere). The canonical `G.endsOf` selector
orients each edge; the support extensor of each triangle edge is ± a member of T3's LI cyclic
family (unit scalar from `endsOf` orientation), so T2 (`theorem_55_triangle`)'s independence
hypothesis holds. T2 gives rigidity on `{v,a,b} = V(G)`, and
`hasGenericFullRankRealization_of_rigidOn_ofNormals` upgrades to the generic motive. -/
theorem PanelHingeFramework.hasGenericFullRankRealization_of_triangle
    [DecidableEq β] [Finite α] [Finite β] {n : ℕ} (G : Graph α β) [G.Simple]
    (hD : 3 ≤ Graph.bodyBarDim n) (hk : 1 ≤ k)
    (hG : G.IsMinimalKDof n 0)
    (hcard : V(G).ncard = 3)
    {v a b : α} {eₐ e_b : β}
    (hG_ea : G.IsLink eₐ v a) (hG_eb : G.IsLink e_b v b)
    (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b) :
    PanelHingeFramework.HasGenericFullRankRealization k n G := by
  classical
  -- T1: vertex set pin + third edge.
  obtain ⟨hab, hVeq, f, hf⟩ :=
    Graph.exists_isLink_of_isMinimalKDof_card_three hD hG hcard hG_ea hG_eb hav hbv heab
  -- T3: the triangle normals with LI cyclic extensor family and pairwise nonzero joins.
  obtain ⟨n₀, n₁, n₂, ⟨hn₀₁, hn₁₂, hn₂₀⟩, hLI⟩ := exists_triangle_normals (k := k) hk
  -- Convert T3's fun-form LI to the `![C₀,C₁,C₂]` matrix form.
  -- `fun i => panelSupportExtensor (![n₀,n₁,n₂] i) (![n₁,n₂,n₀] i)` equals
  -- `![C₀, C₁, C₂]` where `Cᵢ = panelSupportExtensor (T3 pairs)`.
  have hLI' : LinearIndependent ℝ
      ![panelSupportExtensor (k := k) n₀ n₁, panelSupportExtensor n₁ n₂,
        panelSupportExtensor n₂ n₀] := by
    have heq : (![panelSupportExtensor (k := k) n₀ n₁, panelSupportExtensor n₁ n₂,
        panelSupportExtensor n₂ n₀] : Fin 3 → _) =
        fun i => panelSupportExtensor (![n₀, n₁, n₂] i) (![n₁, n₂, n₀] i) := by
      funext i; fin_cases i <;> rfl
    rw [heq]; exact hLI
  -- Derive `panelSupportExtensor nᵢ nⱼ ≠ 0` from T3's join hypotheses.
  have hne₀₁ : panelSupportExtensor (k := k) n₀ n₁ ≠ 0 :=
    (panelSupportExtensor_ne_zero_iff n₀ n₁).mpr ((normalsJoin_ne_zero_iff n₀ n₁).mp hn₀₁)
  have hne₁₂ : panelSupportExtensor (k := k) n₁ n₂ ≠ 0 :=
    (panelSupportExtensor_ne_zero_iff n₁ n₂).mpr ((normalsJoin_ne_zero_iff n₁ n₂).mp hn₁₂)
  have hne₂₀ : panelSupportExtensor (k := k) n₂ n₀ ≠ 0 :=
    (panelSupportExtensor_ne_zero_iff n₂ n₀).mpr ((normalsJoin_ne_zero_iff n₂ n₀).mp hn₂₀)
  -- `G.endsOf` needs `Inhabited α`.
  haveI : Inhabited α := ⟨v⟩
  -- Build the seed `q₀`: vertex `v ↦ n₀`, `a ↦ n₁`, `b ↦ n₂`, junk elsewhere.
  let q₀ : α × Fin (k + 2) → ℝ :=
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
  -- Equalities of functions `Fin(k+2) → ℝ` at the three bodies (for support extensor rewriting).
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
    · exact Or.inl (by rw [hsupp_raw, heo, hfn_v, hfn_a])
    · exact Or.inr (by rw [hsupp_raw, heo, hfn_a, hfn_v, panelSupportExtensor_swap])
  -- Support extensor at `f` (link `a-b`): either `panelSupportExtensor n₁ n₂` or its negative.
  have hsupp_f : F.supportExtensor f = panelSupportExtensor n₁ n₂ ∨
      F.supportExtensor f = -panelSupportExtensor n₁ n₂ := by
    rcases G.endsOf_eq_or_swap hf with heo | heo
    · exact Or.inl (by rw [hsupp_raw, heo, hfn_a, hfn_b])
    · exact Or.inr (by rw [hsupp_raw, heo, hfn_b, hfn_a, panelSupportExtensor_swap])
  -- Support extensor at `e_b` (link `v-b`): either `panelSupportExtensor n₂ n₀` or its negative.
  -- The T3 cyclic family is `n₀n₁, n₁n₂, n₂n₀`; `v-b` gives `n₀n₂ = -(n₂n₀)` or `n₂n₀`.
  have hsupp_eb : F.supportExtensor e_b = panelSupportExtensor n₂ n₀ ∨
      F.supportExtensor e_b = -panelSupportExtensor n₂ n₀ := by
    rcases G.endsOf_eq_or_swap hG_eb with heo | heo
    · exact Or.inr (by rw [hsupp_raw, heo, hfn_v, hfn_b, panelSupportExtensor_swap])
    · exact Or.inl (by rw [hsupp_raw, heo, hfn_b, hfn_v])
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
  -- `hgen`: the three triangle-edge extensors are LI.
  -- Each is ± one member of the T3 cyclic family `![C₀,C₁,C₂]`; negation preserves LI via
  -- `LinearIndependent.units_smul_iff`: `w • v` is LI ↔ `v` is LI (w units).
  have hgen : LinearIndependent ℝ
      ![F.supportExtensor eₐ, F.supportExtensor f, F.supportExtensor e_b] := by
    -- Helper: `![-C₀, -C₁, -C₂]`-type sign flips preserve LI.
    have hLI_neg : ∀ (ε₀ ε₁ ε₂ : ℝˣ),
        LinearIndependent ℝ
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
    · have h := hLI_neg 1 1 (Units.mk0 (-1 : ℝ) (by norm_num))
      convert h using 1; funext i; fin_cases i <;> (first | rfl | simp)
    · have h := hLI_neg 1 (Units.mk0 (-1 : ℝ) (by norm_num)) 1
      convert h using 1; funext i; fin_cases i <;> (first | rfl | simp)
    · have h := hLI_neg 1 (Units.mk0 (-1 : ℝ) (by norm_num)) (Units.mk0 (-1 : ℝ) (by norm_num))
      convert h using 1; funext i; fin_cases i <;> (first | rfl | simp)
    · have h := hLI_neg (Units.mk0 (-1 : ℝ) (by norm_num)) 1 1
      convert h using 1; funext i; fin_cases i <;> (first | rfl | simp)
    · have h := hLI_neg (Units.mk0 (-1 : ℝ) (by norm_num)) 1 (Units.mk0 (-1 : ℝ) (by norm_num))
      convert h using 1; funext i; fin_cases i <;> (first | rfl | simp)
    · have h := hLI_neg (Units.mk0 (-1 : ℝ) (by norm_num)) (Units.mk0 (-1 : ℝ) (by norm_num)) 1
      convert h using 1; funext i; fin_cases i <;> (first | rfl | simp)
    · have h := hLI_neg (Units.mk0 (-1 : ℝ) (by norm_num)) (Units.mk0 (-1 : ℝ) (by norm_num))
            (Units.mk0 (-1 : ℝ) (by norm_num))
      convert h using 1
  -- T2: rigidity on `{v,a,b}` via `theorem_55_triangle`.
  have hFgraph : F.graph = G := by
    simp only [hFdef, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]
  have hrigVAB : F.IsInfinitesimallyRigidOn {v, a, b} :=
    BodyHingeFramework.theorem_55_triangle F hav.symm hab hbv.symm hgen
      (hFgraph ▸ hG_ea) (hFgraph ▸ hf) (hFgraph ▸ hG_eb.symm)
  -- T1 vertex-set pin + upgrade to generic motive.
  have hrig : F.IsInfinitesimallyRigidOn V(G) := by rwa [hVeq]
  exact PanelHingeFramework.hasGenericFullRankRealization_of_rigidOn_ofNormals G G.endsOf
    (fun e u w he => G.isLink_endsOf he.edge_mem) hne
    ⟨v, hG_ea.left_mem⟩ hrig n hG.1


/-- **The general-`d` Case-III (`hsplit`) producer, `hsplitGP` callback shape**
(`lem:case-II-realization` / `lem:case-III`, the `theorem_55_all_k.hsplitZero` branch at `k = 0`;
Katoh–Tanigawa 2011 §6.4.1, Lemma 6.10, Phases 22g–22h; Phase 23a Leaf 4 general-`k` lift). The
conjecture's crux at general grade `k`, stated at the **generic-motive
callback interface** that `theorem_55_all_k`'s `hsplitZero` premise threads (the R2 verdict (B),
`notes/Phase22-realization-design.md` §1.41(5)): the producer receives `hnoRigid`, `G.Simple`, and
the **full conditioned induction hypothesis** `hIH` (the `(G'.Simple → generic) ∧ bare` pair over
all smaller minimal `0`-dof-graphs, mirroring `hcontractGP`), **chooses its own adjacent degree-2
pair** via the chain dichotomy (§1.49(1), verdict (β)), and concludes the **generic** motive
`HasGenericFullRankRealization k G`. No split-vertex data is handed in — the producer re-selects
it, exactly as KT's Lemma 6.10 invokes Lemma 4.6 inside its own proof.

**Dichotomy spine (G4a).** On `|V(G)|`:

* `|V(G)| = 3` — the **triangle base** (T1–T4): `exists_adjacent_degree_two_pair` (G4a-i) picks an
  adjacent degree-2 pair `v–a` and `exists_splitOff_data_of_degree_eq_two` its two `v`-edges, so
  `hasGenericFullRankRealization_of_triangle` (T4) closes the generic motive on the triangle
  directly (KT never splits a `|V| = 3` graph — §1.46 finding 2).
* `|V(G)| ≥ 4` — the **chain arm**: `exists_chain_data_of_noRigid` (G4a-ii) extracts the full chain
  data `(v,a,b,c,eₐ,e_b,e_c)` with the two degree-2 closures; with a fresh `e₀ ∉ E(G)`,
  `splitOff_isMinimalKDof` makes the `v`-split `G_v^{ab}` a smaller minimal `0`-dof-graph
  (`splitOff_vertexSet_ncard_lt` for the measure drop); `splitOff_simple_of_noRigid_of_card` (R3,
  KT Lemma 6.7(ii)) discharges the split's simplicity at `4 ≤ |V(G)|`, so the IH's **GP `.1`
  conjunct** yields the **generic** `v`-split realization — the seed `q` whose `IsGeneralPosition`
  conjunct *is* the placement transversal `hgab` and whose `AlgebraicIndependent ℚ` conjunct feeds
  the triple-LI bridge (§1.41(2), §1.48(2); the bare `.2` conjunct provably cannot supply either —
  a rigid realization may have parallel panels). That generic `v`-split realization feeds the
  carried **candidate-placement core** `hcand`.

`hcand` is the single *explicit* hypothesis carrying the genuinely-hard remaining work, in the
established "carry the analytic crux as `h…`, keep the node red" idiom (Phase 21b): it consumes the
chosen chain data and the IH-derived **generic** `v`-split realization and yields
`HasGenericFullRankRealization k G` — internally its `M₁/M₂/M₃` dispatch arms end in the bare
realization of `G`, and the discharge composes the landed GAP-2 upgrade
`hasGenericFullRankRealization_of_rigidOn_ofNormals` onto the concrete candidate (§1.49(5)). The
§1.49(5) producer-assembly leaf discharges it (Leaf 2/3 + the G4c/G4d/G4e dispatch + the GAP-3
good-`t` choice); `G.Simple`, `hnoRigid`, and `hfresh` remain available to that leaf as
producer-level hypotheses. The dichotomy spine and the IH-at-`v`-split wiring built here are the
rest of the producer. -/
theorem PanelHingeFramework.case_III_hsplit_producer_all_k [DecidableEq β] [Finite α] [Finite β]
    {n : ℕ} (hk1 : 1 ≤ k) (hD : 6 ≤ Graph.bodyBarDim n) (G : Graph α β)
    -- the `theorem_55_all_k.hsplitZero` premise data (at `n`, dof `0`)
    (hG : G.IsMinimalKDof n 0) (hV3 : 3 ≤ V(G).ncard)
    (hnoRigid : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n)
    (hsimple : G.Simple)
    (hIH : ∀ G' : Graph α β, G'.IsMinimalKDof n 0 → 2 ≤ V(G').ncard →
      V(G').ncard < V(G).ncard →
      (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization k n G') ∧
        HasPanelRealization k n G')
    -- a fresh edge label for the chain arm's short-circuit `ab`-edge (the (β) reduction
    -- `minimal_kdof_reduction_full` does no splitting internally, so the producer owns it; the
    -- shape `minimal_kdof_reduction`'s `hfresh` carried, moved here at the (β) interface, §1.49(1))
    (hfresh : ∀ G' : Graph α β, ∃ e₀ : β, e₀ ∉ E(G'))
    -- the candidate-placement core (the still-unbuilt Leaf 2/3 + the `M₁/M₂/M₃` dispatch,
    -- §1.49(5)): given the chosen chain data, a fresh `e₀ ∉ E(G)`, and the IH-derived **generic**
    -- `v`-split realization (the seed `q` with `hgab`/alg-indep, §1.41(2)), it produces the
    -- generic realization of `G` (the bare candidate + the GAP-2 upgrade). The genuinely-hard
    -- residual is carried here in the "explicit `h…` crux" idiom (Phase 21b); the
    -- producer-assembly leaf (§1.49(5)) discharges it.
    (hcand : ∀ (v a b c : α) (eₐ e_b e_c e₀ : β),
      v ∈ V(G) → a ∈ V(G) → b ∈ V(G) → c ∈ V(G) →
      a ≠ v → b ≠ v → b ≠ a → c ≠ v → c ≠ a → b ≠ c →
      eₐ ≠ e_b → eₐ ≠ e_c →
      G.IsLink eₐ v a → G.IsLink e_b v b → G.IsLink e_c a c →
      (∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b) →
      (∀ e x, G.IsLink e a x → e = eₐ ∨ e = e_c) →
      e₀ ∉ E(G) →
      (G.splitOff v a b e₀).deficiency n = 0 →
      PanelHingeFramework.HasGenericFullRankRealization k n (G.splitOff v a b e₀) →
      PanelHingeFramework.HasGenericFullRankRealization k n G) :
    PanelHingeFramework.HasGenericFullRankRealization k n G := by
  classical
  have hD3 : 3 ≤ Graph.bodyBarDim n := by omega
  have hD2 : 2 ≤ Graph.bodyBarDim n := by omega
  have hD1 : 1 ≤ Graph.bodyBarDim n := by omega
  haveI := hsimple
  -- Dichotomy on `|V(G)|`: the triangle base (`= 3`) versus the chain arm (`≥ 4`).
  rcases eq_or_lt_of_le hV3 with hV3eq | hV4
  · -- **Triangle base (T1–T4).** Pick an adjacent degree-2 pair and its two `v`-edges; T4 closes
    -- the generic motive on the triangle directly.
    have hcard3 : V(G).ncard = 3 := hV3eq.symm
    obtain ⟨v, a, hvG, haG, hdegv, _, eₐ, hlea⟩ :=
      Graph.exists_adjacent_degree_two_pair hD hV3 hG hnoRigid
    have hav : a ≠ v := hlea.ne.symm
    obtain ⟨a', b, eₐ', e_b, ha'v, hbv, ha'G, hbG, heab', hlea', hleb, _⟩ :=
      Graph.exists_splitOff_data_of_degree_eq_two hD1 hG.1 hvG haG hav hdegv
    -- The splitOff data at `v` supplies two distinct `v`-edges `eₐ'`, `e_b` with distinct far
    -- endpoints `a'`, `b` (`a' ≠ v`, `b ≠ v`); T4 needs exactly two such edges to pin the triangle.
    exact PanelHingeFramework.hasGenericFullRankRealization_of_triangle (n := n) (k := k)
      G hD3 hk1 hG hcard3 hlea' hleb ha'v hbv heab'
  · -- **Chain arm (`|V(G)| ≥ 4`).** Extract the chain data, build the `v`-split (a smaller minimal
    -- `0`-dof-graph by `splitOff_isMinimalKDof`, simple by R3), pull its **generic** realization
    -- from the IH's GP `.1` conjunct, and feed `hcand`.
    have hV4' : 4 ≤ V(G).ncard := hV4
    obtain ⟨v, a, b, c, eₐ, e_b, e_c, hvG, haG, hbG, hcG, hav, hbv, hba, hcv, hca, hbc,
      heab, heac, hlea, hleb, hlec, hclv, hcla⟩ :=
      Graph.exists_chain_data_of_noRigid hD hV4' hG hnoRigid
    -- A fresh edge label `e₀ ∉ E(G)` for the short-circuit `ab`-edge of the `v`-split.
    obtain ⟨e₀, he₀⟩ := hfresh G
    -- The `v`-split is a smaller minimal `0`-dof-graph; the IH realizes it.
    have hGv : (G.splitOff v a b e₀).IsMinimalKDof n 0 :=
      Graph.splitOff_isMinimalKDof hD2 hV3 hav hbv haG hbG hvG heab hlea hleb hclv he₀ hG hnoRigid
    have hGvlt : V(G.splitOff v a b e₀).ncard < V(G).ncard :=
      Graph.splitOff_vertexSet_ncard_lt hvG
    -- `|V(G.splitOff)| = |V(G)| − 1 ≥ 2` (one vertex `v` removed from `|V(G)| ≥ 3`).
    have hGv2 : 2 ≤ V(G.splitOff v a b e₀).ncard := by
      rw [Graph.vertexSet_splitOff, Set.ncard_diff (by simpa using hvG) (Set.toFinite _),
        Set.ncard_singleton]
      omega
    -- … and simple (R3, KT Lemma 6.7(ii)): an `ab`-parallel pair in the split would close the
    -- triangle `G[{v,a,b}]`, a proper rigid subgraph at `4 ≤ |V(G)|`, contradicting `hnoRigid`.
    have hGvSimple : (G.splitOff v a b e₀).Simple :=
      Graph.splitOff_simple_of_noRigid_of_card hD3 heab hlea hleb hV4' hnoRigid
    -- The IH's GP `.1` conjunct: the generic `v`-split realization (the placement seed `q`, whose
    -- `IsGeneralPosition` conjunct is `hgab` and whose alg-indep conjunct feeds the triple-LI
    -- bridge — the data the bare `.2` conjunct cannot supply, §1.41(1)–(2)).
    have hsplitGP : PanelHingeFramework.HasGenericFullRankRealization k n (G.splitOff v a b e₀) :=
      (hIH _ hGv hGv2 hGvlt).1 hGvSimple
    exact hcand v a b c eₐ e_b e_c e₀ hvG haG hbG hcG hav hbv hba hcv hca hbc heab heac
      hlea hleb hlec hclv hcla he₀ hGv.1 hsplitGP

/-- **The `d = 3` Case-III (`hsplit`) producer** (`lem:case-III`; the `k = 2` specialization of
`case_III_hsplit_producer_all_k`, Phase 23a Leaf 4). Thin wrapper pinning the grade to `k = 2` so
the `d = 3` spine consumer `case_III_realization` keeps its existing shape; the `1 ≤ k` floor is
discharged at `2` by `norm_num`. The `hD : 6 ≤ bodyBarDim n` floor is the `d = 3` graph-side chain
extraction's requirement (Phase 20's `exists_chain_data_of_noRigid` /
`exists_adjacent_degree_two_pair` are `6`-pinned); ENTRY lifts that floor. -/
theorem PanelHingeFramework.case_III_hsplit_producer [DecidableEq β] [Finite α] [Finite β]
    {n : ℕ} (hD : 6 ≤ Graph.bodyBarDim n) (G : Graph α β)
    (hG : G.IsMinimalKDof n 0) (hV3 : 3 ≤ V(G).ncard)
    (hnoRigid : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n)
    (hsimple : G.Simple)
    (hIH : ∀ G' : Graph α β, G'.IsMinimalKDof n 0 → 2 ≤ V(G').ncard →
      V(G').ncard < V(G).ncard →
      (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization 2 n G') ∧
        HasPanelRealization 2 n G')
    (hfresh : ∀ G' : Graph α β, ∃ e₀ : β, e₀ ∉ E(G'))
    (hcand : ∀ (v a b c : α) (eₐ e_b e_c e₀ : β),
      v ∈ V(G) → a ∈ V(G) → b ∈ V(G) → c ∈ V(G) →
      a ≠ v → b ≠ v → b ≠ a → c ≠ v → c ≠ a → b ≠ c →
      eₐ ≠ e_b → eₐ ≠ e_c →
      G.IsLink eₐ v a → G.IsLink e_b v b → G.IsLink e_c a c →
      (∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b) →
      (∀ e x, G.IsLink e a x → e = eₐ ∨ e = e_c) →
      e₀ ∉ E(G) →
      (G.splitOff v a b e₀).deficiency n = 0 →
      PanelHingeFramework.HasGenericFullRankRealization 2 n (G.splitOff v a b e₀) →
      PanelHingeFramework.HasGenericFullRankRealization 2 n G) :
    PanelHingeFramework.HasGenericFullRankRealization 2 n G :=
  PanelHingeFramework.case_III_hsplit_producer_all_k (by norm_num) hD G hG hV3 hnoRigid
    hsimple hIH hfresh hcand

end CombinatorialRigidity.Molecular
