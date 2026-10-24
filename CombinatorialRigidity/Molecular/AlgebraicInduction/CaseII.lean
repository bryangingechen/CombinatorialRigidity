/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Mathlib.Basic.Countable.Defs
import CombinatorialRigidity.Molecular.AlgebraicInduction.GenericityDevice
import CombinatorialRigidity.Molecular.Induction.ForestSurgery.Reduction
import CombinatorialRigidity.Molecular.RigidityMatrix.Bricks

/-!
# Case II: putting back a vertex of degree two

Lemmas for Case II of KT Theorem 5.5 (Katoh and Tanigawa 2011, *A proof of the molecular
conjecture*, Discrete Comput. Geom. **45**, §6.3), presented in
`sec:molecular-algebraic-induction-caseII`. The file proves:

* the count of KT eq. (6.12) at a rigid realization, one row short of the target rank
  (`lem:case-II-realization-placement`, in `sec:molecular-algebraic-induction-relative`), for a
  realization of a subgraph of `G`; no declaration uses it;
* KT Lemma 6.8 (`lem:case-II-realization`): a 2-edge-connected minimal `k`-dof-graph with `k > 0`,
  at least three vertices and no proper rigid subgraph has a generic full-rank realization.
-/

namespace CombinatorialRigidity.Molecular

variable {k : ℕ}
variable {K : Type*} [Field K]

open scoped Graph

variable {α β : Type*}

/-- **KT eq. (6.12) at a rigid realization: one row short** (`lem:case-II-realization-placement`):
let `Gv ≤ G` with `v ∉ V(Gv)`, `a, b ∈ V(Gv)` and `|V(Gv)| = |V(G)| − 1`, let `e_b` link `v` and `b`
in `G`, with `ends e_b = (v, b)` and `ends e_a = (v, a)`, and let `ofNormals Gv ends q` record the
links of `Gv` (`hends_Gv`), have nonzero hinges at them (`hne_Gv`) and be infinitesimally rigid on
`V(Gv)` (`hrig`). Let `q(a)` and `q(b)` be linearly independent (`hgab`), let `t ≠ 0`, and let `q₀`
be `q` with the normal `q(a) + t q(b)` at `v`. Then the hinge of `e_a` at `q₀` is nonzero, and some
`D(|V(G)| − 1) − 1` panel rows of `ofNormals G ends q₀`, all rows of `R(G, q₀)`, are linearly
independent: one row short of the target rank `D(|V(G)| − 1)`, as Katoh and Tanigawa note for
`k = 0` (p. 680).

Its node starts from a realization of the split-off `G_v^{ab}`, which is not a subgraph of `G`; the
proof of `case_II_realization_all_k` makes that count. By the note after the node, a subgraph `Gv`
as here is a proper rigid subgraph of `G` when `|V(G)| ≥ 3`, so that in Cases II and III no
realization meets the hypotheses; no declaration uses the lemma.

The proof. As `v ∉ V(Gv)`, no link of `Gv` has `v` as an end, so `ofNormals Gv ends q₀` has the
motions and the hinges of `ofNormals Gv ends q` (`ofNormals_update_eq_withNormal`,
`toBodyHinge_withNormal_infinitesimalMotions_eq`). At `q₀` the hinge of `e_b` is `C(q(a), q(b))`
(`panelSupportExtensor_add_smul_right`) and that of `e_a` is `−t C(q(a), q(b))`
(`panelSupportExtensor_add_smul_left`), both nonzero. Some `D(|V(Gv)| − 1)` rows of
`ofNormals Gv ends q₀` at links of `Gv` are linearly independent
(`exists_independent_panelRow_subfamily_of_rigidOn_linking`), and they are rows of
`ofNormals G ends q₀` (`exists_independent_panelRow_transport` at the identity,
`lem:case-II-placement-old-rows`). Some `D − 1` rows of `e_b` are linearly independent
(`exists_independent_panelRow_subfamily_of_edge`, `lem:case-II-placement-new-rows`), and stay so on
the screw assignments that vanish off `v` (`linearIndependent_panelRow_comp_single_of_edge`), where
the rows of `Gv` vanish. So the two families are independent together
(`linearIndependent_sum_pinned_block`, `lem:case-II-placement-block-independent`; KT eq. (6.16),
p. 679), and they number `(D − 1) + D(|V(G)| − 2) = D(|V(G)| − 1) − 1`. -/
theorem PanelHingeFramework.case_II_placement_eq612 [DecidableEq α] [Finite α] [Finite β]
    (G Gv : Graph α β) (hGv : Gv ≤ G) (ends : β → α × α)
    -- the body `v`, its edge `e_b = vb`, and the label `e_a` whose selected ends are `v` and `a`
    {v a b : α} {e_a e_b : β} (hvVc : v ∉ V(Gv)) (haVc : a ∈ V(Gv)) (hbVc : b ∈ V(Gv))
    (hG_eb : G.IsLink e_b v b) (hends_eb : ends e_b = (v, b)) (hends_ea : ends e_a = (v, a))
    -- `|V(Gv)| = |V(G)| − 1`
    (hVcard : V(Gv).ncard = V(G).ncard - 1)
    -- a realization of `Gv` at the normals `q`: links recorded, nonzero hinges, rigid on `V(Gv)`
    {q : α × Fin (k + 2) → K}
    (hends_Gv : ∀ e u w, Gv.IsLink e u w → Gv.IsLink e (ends e).1 (ends e).2)
    (hne_Gv : ∀ e, Gv.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.supportExtensor e ≠ 0)
    (hrig : (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.IsInfinitesimallyRigidOn V(Gv))
    -- `t ≠ 0`, and the normals `q₀`: those of `q`, with `q(a) + t • q(b)` at `v`
    {t : K} (ht : t ≠ 0)
    (q₀ : α × Fin (k + 2) → K)
    (hq₀ : q₀ = fun p => if p.1 = v then
        ((fun i => q (a, i)) + t • (fun i => q (b, i))) p.2 else q p)
    -- `q(a)` and `q(b)` are linearly independent, so the hinge `C(q(a), q(b))` is nonzero
    (hgab : LinearIndependent K ![(fun i => q (a, i)), (fun i => q (b, i))]) :
    -- the hinge of `e_a` at `q₀` is nonzero, and some `D(|V(G)|−1) − 1` panel rows of
    -- `ofNormals G ends q₀`, all rows of `R(G, q₀)`, are linearly independent
    (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.supportExtensor e_a ≠ 0 ∧
    ∃ s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      screwDim k * (V(G).ncard - 1) - 1 ≤ Nat.card s ∧
      (∀ i ∈ s, (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.panelRow ends i
        ∈ (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.rigidityRows) ∧
      LinearIndependent K (fun i : s =>
        (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.panelRow ends i) := by
  classical
  have : Fintype α := Fintype.ofFinite α
  set FG := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge with hFG
  set n_a : Fin (k + 2) → K := fun i => q (a, i) with hn_a
  set n_b : Fin (k + 2) → K := fun i => q (b, i) with hn_b
  -- (1) `q₀` is `q` with the normal `n_a + t • n_b` at `v`; as `v ∉ V(Gv)`, `ofNormals Gv ends q₀`
  -- is rigid on `V(Gv)` too.
  have hqeq : (fun p => if p.1 = v then ((n_a + t • n_b) : Fin (k + 2) → K) p.2 else q p) = q₀ := by
    rw [hq₀]
  have hwN : PanelHingeFramework.ofNormals Gv ends q₀
      = (PanelHingeFramework.ofNormals Gv ends q).withNormal v (n_a + t • n_b) := by
    rw [← hqeq]
    exact PanelHingeFramework.ofNormals_update_eq_withNormal Gv ends q v (n_a + t • n_b)
  -- No `Gᵥ`-edge touches `v` (its endpoints lie in `V(Gᵥ)`, and `v ∉ V(Gᵥ)`).
  have hvedge : ∀ e u w, Gv.IsLink e u w → (ends e).1 ≠ v ∧ (ends e).2 ≠ v := by
    intro e u w he
    have hl := hends_Gv e u w he
    exact ⟨fun h => hvVc (h ▸ hl.left_mem), fun h => hvVc (h ▸ hl.right_mem)⟩
  -- The motion space is unchanged when the normal of `v`, on no link, changes.
  have hZeq : (PanelHingeFramework.ofNormals Gv ends q₀).toBodyHinge.infinitesimalMotions
      = (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.infinitesimalMotions := by
    rw [hwN]
    exact (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge_withNormal_infinitesimalMotions_eq
      v (n_a + t • n_b) hvedge
  have hrig₀ :
      (PanelHingeFramework.ofNormals Gv ends q₀).toBodyHinge.IsInfinitesimallyRigidOn V(Gv) := by
    intro S hS u hu w hw
    refine hrig S ?_ u hu w hw
    rw [← BodyHingeFramework.mem_infinitesimalMotions, ← hZeq,
      BodyHingeFramework.mem_infinitesimalMotions] at *
    exact hS
  -- The `Gᵥ`-hinges stay transversal at `q₀` (endpoints avoid `v`, where `q₀` agrees with `q`).
  have hne₀ : ∀ e, Gv.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals Gv ends q₀).toBodyHinge.supportExtensor e ≠ 0 := by
    intro e he
    obtain ⟨h₁, h₂⟩ := hvedge e _ _ he
    rw [hwN, (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge_withNormal_supportExtensor_of_ne
      v (n_a + t • n_b) e (by simpa using h₁) (by simpa using h₂)]
    exact hne_Gv e he
  -- (2) The old rows: `D(|V(Gv)|−1)` independent panel rows of `ofNormals Gv ends q₀` at links
  -- of `Gv`.
  have hVGvne : V(Gv).Nonempty := ⟨b, hbVc⟩
  set FGv := (PanelHingeFramework.ofNormals Gv ends q₀).toBodyHinge with hFGv
  obtain ⟨so, hso_link, hso_card, hso_indep⟩ :=
    FGv.exists_independent_panelRow_subfamily_of_rigidOn_linking (ends := ends)
      (by simpa [hFGv] using hends_Gv) (by simpa [hFGv] using hne₀) (by simpa [hFGv] using hVGvne)
      (by simpa [hFGv] using hrig₀)
  -- (3) They are rows of `ofNormals G ends q₀` (`exists_independent_panelRow_transport` at the
  -- identity: `panelRow` reads only `ends` and `q₀`, not the graph, so `hrow := rfl`).
  have hso_indep_G : LinearIndependent K (fun i : so =>
      FG.panelRow ends (i : β × _ × _)) :=
    PanelHingeFramework.exists_independent_panelRow_transport Gv G ends ends q₀ q₀
      (f := id) Function.injective_id (fun i => rfl) hso_indep
  -- The re-inserted body `v` and its neighbour `b` are distinct (`b ∈ V(Gᵥ)`, `v ∉ V(Gᵥ)`).
  have hvb : v ≠ b := fun h => hvVc (h ▸ hbVc)
  -- The normals `q₀` are `n_a + t·n_b` at `v` and `n_b` at `b`.
  have hq₀v : (fun i => q₀ (v, i)) = n_a + t • n_b := by
    funext i; rw [hq₀]; simp
  have hq₀b : (fun i => q₀ (b, i)) = n_b := by
    funext i; rw [hq₀, hn_b]; simp only [ite_eq_right hvb.symm]
  have hva : v ≠ a := fun h => hvVc (h ▸ haVc)
  have hq₀a : (fun i => q₀ (a, i)) = n_a := by
    funext i; rw [hq₀, hn_a]; simp only [ite_eq_right hva.symm]
  -- The hinge of `e_a` at `q₀` is `−t C(n_a, n_b) ≠ 0` (`t ≠ 0`).
  have hane : FG.supportExtensor e_a ≠ 0 := by
    rw [PanelHingeFramework.ofNormals_supportExtensor_eq_panel_of_ends _ e_a hends_ea]
    simp only [hq₀v, hq₀a, panelSupportExtensor_add_smul_left]
    exact smul_ne_zero (neg_ne_zero.mpr ht) ((panelSupportExtensor_ne_zero_iff n_a n_b).mpr hgab)
  -- (4) The new rows: the hinge of `e_b` at `q₀` is `C(n_a, n_b) ≠ 0`
  -- (`panelSupportExtensor_add_smul_right`), so `e_b` has `D − 1` independent rows.
  have hnewne : FG.supportExtensor e_b ≠ 0 := by
    rw [PanelHingeFramework.ofNormals_supportExtensor_eq_panel_of_ends _ e_b hends_eb]
    simp only [hq₀v, hq₀b, panelSupportExtensor_add_smul_right]
    exact (panelSupportExtensor_ne_zero_iff n_a n_b).mpr hgab
  have hev : (ends e_b).2 ≠ (ends e_b).1 := by rw [hends_eb]; exact hvb.symm
  obtain ⟨sn, hsn_e, hsn_card, hsn_indep⟩ :=
    FG.exists_independent_panelRow_subfamily_of_edge
      (ends := ends) (e := e_b) (by rw [hends_eb]; exact hvb) hnewne
  -- `hnewpin`: the new rows stay independent through `v = (ends e_b).1`'s screw column.
  have hnewpin := FG.linearIndependent_panelRow_comp_single_of_edge
    (ends := ends) (e := e_b) hev hsn_e hsn_indep
  -- (5) The old rows vanish at `update 0 v x` (their `Gᵥ`-edges avoid `v`).
  have hold : ∀ (j : so) (x : ScrewSpace K k),
      FG.panelRow ends (j : β × _ × _)
        (Function.update (0 : α → ScrewSpace K k) v x) = 0 := by
    rintro ⟨i, hi⟩ x
    have hlink := hso_link _ hi
    have h₁ : (ends i.1).1 ≠ v := fun h => hvVc (h ▸ hlink.left_mem)
    have h₂ : (ends i.1).2 ≠ v := fun h => hvVc (h ▸ hlink.right_mem)
    simp only [BodyHingeFramework.panelRow, BodyHingeFramework.hingeRow_apply,
      Function.update_of_ne h₁, Function.update_of_ne h₂, Pi.zero_apply, sub_zero,
      map_zero]
  -- (6) The two families are independent together (`linearIndependent_sum_pinned_block`; KT
  -- eq. (6.16)).
  have hunion : LinearIndependent K (Sum.elim
      (fun i : sn => FG.panelRow ends
        (i : β × _ × _))
      (fun i : so => FG.panelRow ends
        (i : β × _ × _))) := by
    have hpin : LinearIndependent K (fun i : sn =>
        (FG.panelRow ends (i : β × _ × _)).comp
          (LinearMap.single K (fun _ : α => ScrewSpace K k) v)) := by
      have := hnewpin
      rw [hends_eb] at this
      exact this
    exact BodyHingeFramework.linearIndependent_sum_pinned_block (v := v) hold hpin hso_indep_G
  -- (7) Package the `Sum.elim` family as a single `Set`-indexed panel-row subfamily. The map
  -- sending each block index to its underlying `(edge, ⋀^k-pair)` is injective: `sn`-indices use
  -- the new edge `e_b ∉ E(Gᵥ)`, `so`-indices use `Gᵥ`-edges, so the two are disjoint.
  -- No `so`-index uses the new edge `e_b`: else `e_b` would be a `Gᵥ`-edge with endpoint `v`.
  have hso_ne_eb : ∀ i ∈ so, (i : β × _ × _).1 ≠ e_b := by
    intro i hi heq
    have hl := hso_link i hi
    rw [heq, hends_eb] at hl
    exact hvVc hl.left_mem
  set j : (sn ⊕ so) → (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k) :=
    Sum.elim (fun i => (i : β × _ × _)) (fun i => (i : β × _ × _)) with hj
  have hjinj : Function.Injective j := by
    rintro (⟨in₁, hin₁⟩ | ⟨io₁, hio₁⟩) (⟨in₂, hin₂⟩ | ⟨io₂, hio₂⟩) hab <;>
      simp only [hj, Sum.elim_inl, Sum.elim_inr] at hab
    · exact congrArg Sum.inl (Subtype.ext hab)
    · have : (io₂ : β × _ × _).1 = e_b := by rw [← congrArg Prod.fst hab]; exact hsn_e _ hin₁
      exact absurd this (hso_ne_eb _ hio₂)
    · have : (io₁ : β × _ × _).1 = e_b := by rw [congrArg Prod.fst hab]; exact hsn_e _ hin₂
      exact absurd this (hso_ne_eb _ hio₁)
    · exact congrArg Sum.inr (Subtype.ext hab)
  -- `s := range j`, the union index set; the panel-row family on it is the `Sum.elim` family
  -- reindexed across `Equiv.ofInjective j`, hence independent and a rigidity-row family.
  refine ⟨hane, Set.range j, ?_, ?_, ?_⟩
  · -- Count: `(D−1) + D(|V(Gᵥ)|−1) = D(|V(G)|−1) − 1` (using `|V(Gᵥ)| = |V(G)| − 1`).
    rw [Nat.card_range_of_injective hjinj, Nat.card_sum, hsn_card]
    have hgraph : V((PanelHingeFramework.ofNormals Gv ends q₀).toBodyHinge.graph) = V(Gv) := rfl
    rw [hgraph] at hso_card
    rw [hso_card, hVcard]
    have h1 : 1 ≤ V(G).ncard := (Set.ncard_pos (Set.toFinite _)).2 ⟨v, hG_eb.left_mem⟩
    -- `D(m−1)−1 ≤ (D−1) + D(m−1−1)`; with `D(m−1) = D(m−2) + D` (for `m ≥ 1`) this is an equality.
    obtain ⟨m, hm⟩ : ∃ m, V(G).ncard = m + 1 := ⟨V(G).ncard - 1, by omega⟩
    rw [hm]
    simp only [Nat.add_sub_cancel]
    cases m with
    | zero => simp
    | succ m' =>
      rw [Nat.add_sub_cancel, Nat.mul_succ]
      omega
  · -- Membership: each row's edge links in `G` (new edge `e_b`, or a `Gᵥ`-edge ≤ `G`).
    rintro i ⟨(⟨ic, hic⟩ | ⟨ic, hic⟩), rfl⟩ <;>
      refine FG.panelRow_mem_rigidityRows ?_
    · change G.IsLink _ _ _
      simp only [hj, Sum.elim_inl]; rw [hsn_e _ hic, hends_eb]; exact hG_eb
    · change G.IsLink _ _ _
      simp only [hj, Sum.elim_inr]
      exact (Graph.IsSubgraph.isLink_iff hGv (hso_link _ hic).edge_mem).mp (hso_link _ hic)
  · -- Independence: reindex the `Sum.elim` family across `Equiv.ofInjective j`.
    have hreindex : (fun i : Set.range j =>
        FG.panelRow ends (i : β × _ × _))
        ∘ (Equiv.ofInjective j hjinj)
      = Sum.elim
        (fun i : sn => FG.panelRow ends
          (i : β × _ × _))
        (fun i : so => FG.panelRow ends
          (i : β × _ × _)) := by
      funext a
      simp only [Function.comp_apply, Equiv.ofInjective_apply, hj]
      cases a <;> rfl
    set ej := Equiv.ofInjective j hjinj with hej
    have h := hunion.comp ej.symm ej.symm.injective
    rw [← hreindex, Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] at h
    exact h

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

Let `q₀` be `q` with the normal `q(a) + q(b)` at `v`, and `ends = G.endsOf`. At `q₀` the hinges of
`e_b` and `e_a` are `C(q(a), q(b))` up to sign, nonzero by general position. Each row of `G_v^{ab}`
at `e₀` is the sum of rows of `e_b` and `e_a` with the same coordinates
(`hingeRow_sub_hingeRow_eq`), and its rows at the other edges are rows of `R(G, q₀)`; so `N`
independent rows of `G_v^{ab}` at `q₀` lie in the row space of `R(G, q₀)`. They vanish on the screw
assignments that vanish off `v`, where some `D − 1` rows of `e_b` stay independent; so `R(G, q₀)`
has rank at least `N + D − 1 = D(|V(G)| − 1) − c`
(`le_finrank_span_rigidityRows_of_pinned_placement`; KT eq. (6.16)). A polynomial in the normals
gives this bound at normals in general position (`exists_rankPolynomial_of_le_finrank_linking`),
where it is the target rank (`finrank_span_rigidityRows_add_deficiency_le`).
`case_II_placement_eq612` does not apply, as `G_v^{ab}` is not a subgraph of `G`. -/
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
  obtain ⟨Q, hQg, hQgp, hQrank, hQrec⟩ :=
    (hIH (c - 1) Gab hGab hGab_ne hGab_lt).1 hGab_simple
  -- Set up the IH normal function q := Q.normal.
  set q : α × Fin (k + 2) → K := fun p => Q.normal p.1 p.2 with hq_def
  -- ── Step 4: `n_a` and `n_b` are linearly independent (general position, `a ≠ b`). ──────────────
  have haVGab : a ∈ V(Gab) := ⟨haG, hav⟩
  have hbVGab : b ∈ V(Gab) := ⟨hbG, hbv⟩
  set n_a : Fin (k + 2) → K := fun i => q (a, i) with hn_a
  set n_b : Fin (k + 2) → K := fun i => q (b, i) with hn_b
  have hgab : LinearIndependent K ![n_a, n_b] := by
    have := hQgp a b hab
    simp only [hq_def, hn_a, hn_b] at *
    convert this using 2
  -- ── Step 5: the selector `ends = G.endsOf` (`Inhabited α`). ────────────────────────────────────
  have : Inhabited α := ⟨v⟩
  set ends := G.endsOf with hendsDef
  -- ── Step 6: the rank `N` of the realization of `Gab`. ──────────────────────────────────────────
  -- N := D(|V(Gab)|−1) − (c−1) as a natural number (the IH's ℤ-rank equality; `c` = dof).
  -- The IH says: (finrank (span rigidityRows) : ℤ) = screwDim k * (|V(Gab)| - 1) - (c - 1).
  -- Since c ≥ 1, (c-1) ≥ 0, and the RHS is a ℕ-cast.
  have hVGabne : V(Gab).Nonempty := hGab_ne
  have h1Gab : 1 ≤ V(Gab).ncard := (Set.ncard_pos (Set.toFinite _)).2 hGab_ne
  -- Extract the IH realization as ofNormals at q.
  have hQeq : PanelHingeFramework.ofNormals Gab Q.ends q = Q := by
    rw [hq_def, ← hQg]; rfl
  -- The ends for Gab are recorded up to swap: hrec' (Gab isLink → ends record).
  have hrec' : ∀ e u w, Gab.IsLink e u w → Q.ends e = (u, w) ∨ Q.ends e = (w, u) := by
    intro e u w he
    rcases hQrec e u w he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (Prod.ext h1 h2)
    · exact Or.inr (Prod.ext h1 h2)
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
  -- ── Step 7: `q₀ = q[v ↦ n_a + n_b]`. ───────────────────────────────────────────────────────────
  -- q₀ agrees with q off v; at v it is n_a + n_b.
  set q₀ : α × Fin (k + 2) → K :=
    fun p => if p.1 = v then (n_a + n_b) p.2 else q p with hq₀_def
  have hq₀v : (fun i => q₀ (v, i)) = n_a + n_b := by
    funext i; rw [hq₀_def]; simp
  have hva : v ≠ a := hav.symm
  have hvb : v ≠ b := hbv.symm
  have hq₀a : (fun i => q₀ (a, i)) = n_a := by
    funext i; rw [hq₀_def, hn_a]; simp only [ite_eq_right hva.symm]
  have hq₀b : (fun i => q₀ (b, i)) = n_b := by
    funext i; rw [hq₀_def, hn_b]; simp only [ite_eq_right hvb.symm]
  -- ── Step 8: the bound `N` at `q₀`, for `Gab`. ──────────────────────────────────────────────────
  -- Override v's normal in ofNormals Gab doesn't change the motion space (v ∉ V(Gab)).
  have hvVGab : v ∉ V(Gab) := by
    rw [hGab_def, Graph.vertexSet_splitOff]
    simp
  have hQ_ends_Gab : ∀ e u w, Gab.IsLink e u w → Gab.IsLink e (Q.ends e).1 (Q.ends e).2 := by
    intro e u w he
    rcases hrec' e u w he with he' | he' <;> rw [he']
    · exact he
    · exact he.symm
  -- q and q₀ agree on V(Gab) (v ∉ V(Gab), so Gab-links avoid v).
  have hvedge : ∀ e u w, Gab.IsLink e u w →
      (Q.ends e).1 ≠ v ∧ (Q.ends e).2 ≠ v := by
    intro e u w he
    have hl := hQ_ends_Gab e u w he
    exact ⟨fun h => hvVGab (h ▸ hl.left_mem), fun h => hvVGab (h ▸ hl.right_mem)⟩
  -- The withNormal override of v in ofNormals Gab Q.ends q gives ofNormals Gab Q.ends q₀.
  have hwN : PanelHingeFramework.ofNormals Gab Q.ends q₀
      = (PanelHingeFramework.ofNormals Gab Q.ends q).withNormal v (n_a + n_b) := by
    have hqeq : (fun p => if p.1 = v then (n_a + n_b) p.2 else q p) = q₀ := (hq₀_def).symm
    rw [← hqeq]
    exact PanelHingeFramework.ofNormals_update_eq_withNormal Gab Q.ends q v (n_a + n_b)
  -- Motion space unchanged (v ∉ V(Gab) ⇒ its hinges don't involve v's normal).
  have hZeq : (PanelHingeFramework.ofNormals Gab Q.ends q₀).toBodyHinge.infinitesimalMotions
      = (PanelHingeFramework.ofNormals Gab Q.ends q).toBodyHinge.infinitesimalMotions := by
    rw [hwN]
    exact (PanelHingeFramework.ofNormals Gab Q.ends
      q).toBodyHinge_withNormal_infinitesimalMotions_eq v (n_a + n_b) hvedge
  have hspan_eq :
      Submodule.span K (PanelHingeFramework.ofNormals Gab Q.ends q₀).toBodyHinge.rigidityRows
      = Submodule.span K (PanelHingeFramework.ofNormals Gab Q.ends q).toBodyHinge.rigidityRows :=
    BodyHingeFramework.span_rigidityRows_eq_of_infinitesimalMotions_eq _ _ hZeq
  have hN₀ : N ≤ Module.finrank K (Submodule.span K
      (PanelHingeFramework.ofNormals Gab Q.ends q₀).toBodyHinge.rigidityRows) := by
    rw [hspan_eq]; exact hNrank_q
  -- ── Step 9: the hinges of `Gab` at `q₀` are nonzero. ───────────────────────────────────────────
  -- Gab-hinges avoid v (v ∉ V(Gab)), so q₀ agrees with q at their endpoints.
  have hne_q : ∀ e, Gab.IsLink e (Q.ends e).1 (Q.ends e).2 →
      (PanelHingeFramework.ofNormals Gab Q.ends q).toBodyHinge.supportExtensor e ≠ 0 := by
    intro e he
    apply PanelHingeFramework.supportExtensor_ne_zero_of_isGeneralPosition _ (hQeq ▸ hQgp)
    rw [PanelHingeFramework.ofNormals_ends]
    -- (Q.ends e).1 ≠ (Q.ends e).2: Gab is loopless (from hGab_simple) and Gab.IsLink e at Q.ends.
    have : Gab.Loopless := hGab_simple.toLoopless
    exact (hQ_ends_Gab e _ _ he).ne
  have hne₀ : ∀ e, Gab.IsLink e (Q.ends e).1 (Q.ends e).2 →
      (PanelHingeFramework.ofNormals Gab Q.ends
        q₀).toBodyHinge.supportExtensor e ≠ 0 := by
    intro e he
    obtain ⟨h₁, h₂⟩ := hvedge e _ _ he
    rw [hwN, (PanelHingeFramework.ofNormals Gab Q.ends
        q).toBodyHinge_withNormal_supportExtensor_of_ne
      v (n_a + n_b) e (by simpa using h₁) (by simpa using h₂)]
    exact hne_q e he
  -- ── Step 10: the old rows: `N` independent rows of `Gab` at `q₀`, at its links. ────────────────
  set FG := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge with hFG_def
  set FGab := (PanelHingeFramework.ofNormals Gab Q.ends q₀).toBodyHinge with hFGab_def
  have hends_Gab : ∀ e u w, Gab.IsLink e u w →
      Gab.IsLink e (Q.ends e).1 (Q.ends e).2 := hQ_ends_Gab
  obtain ⟨so, hso_link, hso_card, hso_indep⟩ :=
    FGab.exists_independent_panelRow_subfamily_of_le_finrank (ends := Q.ends)
      (by simpa [hFGab_def] using hends_Gab) (by simpa [hFGab_def] using hne₀)
      (by simpa [hFGab_def] using hN₀)
  -- ── Step 11: the hinges of `e_b` and `e_a` at `q₀`. ────────────────────────────────────────────
  -- At q₀ = q[v ↦ n_a + n_b]:
  --   C(e_b) = panelSupportExtensor(n_a + n_b, n_b) = panelSupportExtensor(n_a, n_b)
  --     [add_smul_right]
  --   C(e_a) = panelSupportExtensor(n_a + n_b, n_a) = (-1) • panelSupportExtensor(n_a, n_b)
  --     [add_smul_left]
  -- up to the order in which `ends = G.endsOf` gives their ends. `ends` records every link of `G`:
  have hends_G : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2 := by
    rw [hendsDef]; exact fun e _ _ h => G.isLink_endsOf h.edge_mem
  -- ends e_a = (v,a) or (a,v); ends e_b = (v,b) or (b,v).
  have hends_ea : ends e_a = (v, a) ∨ ends e_a = (a, v) := by
    simp only [hendsDef]; exact G.endsOf_eq_or_swap hG_ea
  have hends_eb : ends e_b = (v, b) ∨ ends e_b = (b, v) := by
    simp only [hendsDef]; exact G.endsOf_eq_or_swap hG_eb
  -- `FG.graph = G` (for `panelRow_mem_rigidityRows` below).
  have hFG_graph : FG.graph = G := by
    rw [hFG_def, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]
  -- The hinge of `e_a` at `q₀`, in each order of its ends:
  -- hFG_ea: FG.supportExtensor e_a = (-1) • panelSupportExtensor n_a n_b  (when ends e_a = (v,a))
  --   OR = panelSupportExtensor n_a n_b  (when ends e_a = (a,v))
  have hFG_ea : FG.supportExtensor e_a = (-1 : K) • panelSupportExtensor n_a n_b ∨
      FG.supportExtensor e_a = panelSupportExtensor n_a n_b := by
    rcases hends_ea with h | h
    · left
      rw [hFG_def, PanelHingeFramework.ofNormals_supportExtensor_eq_panel_of_ends _ e_a h,
        hq₀v, hq₀a, show n_a + n_b = n_a + (1 : K) • n_b from by rw [one_smul]]
      exact panelSupportExtensor_add_smul_left n_a n_b 1
    · right
      rw [hFG_def, PanelHingeFramework.ofNormals_supportExtensor_eq_panel_of_ends _ e_a h,
        hq₀a, hq₀v]
      -- goal: panelSupportExtensor n_a (n_a + n_b) = panelSupportExtensor n_a n_b
      -- panelSupportExtensor n_a (n_a + n_b)
      --   = -panelSupportExtensor (n_a + n_b) n_a
      --     [panelSupportExtensor_swap with n₂=n_a, n₁=n_a+n_b]
      --   = -panelSupportExtensor (n_a + 1•n_b) n_a
      --   = -(-1 • panelSupportExtensor n_a n_b)   [panelSupportExtensor_add_smul_left]
      --   = panelSupportExtensor n_a n_b
      rw [panelSupportExtensor_swap (n_a + n_b) n_a,
        show n_a + n_b = n_a + (1 : K) • n_b from by rw [one_smul],
        panelSupportExtensor_add_smul_left]
      -- goal: -(-1 • panelSupportExtensor n_a n_b) = panelSupportExtensor n_a n_b
      module
  -- `e₀` links `a` and `b` in `Gab`.
  have he₀ab : Gab.IsLink e₀ a b := by
    rw [hGab_def, Graph.splitOff_isLink]
    exact Or.inr ⟨rfl, hav, hbv, haG, hbG, Or.inl ⟨rfl, rfl⟩⟩
  -- ── Step 12: the rows of `e_b` and `e_a` at `q₀`. ──────────────────────────────────────────────
  -- With `ρ = annihRow (panelSupportExtensor n_a n_b) t₁ t₂`, in either order of the ends,
  -- `FG.panelRow ends (e_b, t₁, t₂) = hingeRow v b ρ` and
  -- `FG.panelRow ends (e_a, t₁, t₂) = -hingeRow v a ρ`. The rows of `e_a` and `e_b` are rows of
  -- `R(G, q₀)`:
  have hFG_ea_mem : ∀ (t₁ t₂ : Set.powersetCard (Fin (k + 2)) k),
      FG.panelRow ends (e_a, t₁, t₂) ∈ FG.rigidityRows :=
    fun t₁ t₂ => FG.panelRow_mem_rigidityRows (i := (e_a, t₁, t₂))
      (hFG_graph ▸ hends_G e_a v a hG_ea)
  have hFG_eb_mem : ∀ (t₁ t₂ : Set.powersetCard (Fin (k + 2)) k),
      FG.panelRow ends (e_b, t₁, t₂) ∈ FG.rigidityRows :=
    fun t₁ t₂ => FG.panelRow_mem_rigidityRows (i := (e_b, t₁, t₂))
      (hFG_graph ▸ hends_G e_b v b hG_eb)
  -- hingeRow v b ρ = FG.panelRow ends (e_b, t₁, t₂) in both orientations.
  have hrow_b_eq : ∀ (t₁ t₂ : Set.powersetCard (Fin (k + 2)) k),
      BodyHingeFramework.hingeRow v b (annihRow (panelSupportExtensor n_a n_b) t₁ t₂)
        = FG.panelRow ends (e_b, t₁, t₂) := by
    intro t₁ t₂
    -- Orientation-agnostic: the fused row lemma absorbs `ends e_b = (v,b) ∨ (b,v)` in one shot;
    -- the shear `panelSupportExtensor (n_a+n_b) n_b = panelSupportExtensor n_a n_b` closes it.
    rw [hFG_def, PanelHingeFramework.ofNormals_panelRow_eq_hingeRow_of_ends_or_swap G ends q₀
        hends_eb t₁ t₂, hq₀v, hq₀b,
      show n_a + n_b = n_a + (1 : K) • n_b from by rw [one_smul],
      panelSupportExtensor_add_smul_right]
  -- -hingeRow v a ρ = FG.panelRow ends (e_a, t₁, t₂) in both orientations.
  have hrow_a_eq : ∀ (t₁ t₂ : Set.powersetCard (Fin (k + 2)) k),
      -(BodyHingeFramework.hingeRow v a (annihRow (panelSupportExtensor n_a n_b) t₁ t₂))
        = FG.panelRow ends (e_a, t₁, t₂) := by
    intro t₁ t₂
    -- Orientation-agnostic: the fused row lemma absorbs `ends e_a = (v,a) ∨ (a,v)`; the shear
    -- `panelSupportExtensor (n_a+n_b) n_a = (-1)•panelSupportExtensor n_a n_b` supplies the sign.
    rw [hFG_def, PanelHingeFramework.ofNormals_panelRow_eq_hingeRow_of_ends_or_swap G ends q₀
        hends_ea t₁ t₂, hq₀v, hq₀a,
      show n_a + n_b = n_a + (1 : K) • n_b from by rw [one_smul],
      panelSupportExtensor_add_smul_left, annihRow_smul]
    simp only [BodyHingeFramework.hingeRow_eq_dualMap, map_smul]
    module
  -- ── Step 13: the rows of `Gab` at `e₀` lie in the row space of `R(G, q₀)`. ─────────────────────
  have he₀_rows_mem : ∀ (t₁ t₂ : Set.powersetCard (Fin (k + 2)) k),
      FGab.panelRow Q.ends (e₀, t₁, t₂) ∈ Submodule.span K FG.rigidityRows := by
    intro t₁ t₂
    -- `ofNormals_panelRow_eq_hingeRow_of_ends_or_swap` takes either order of `Q.ends e₀`; then
    -- `hingeRow a b = hingeRow v b − hingeRow v a` gives the rows of `e_b` and `e_a` (`hrow_b_eq`,
    -- `hrow_a_eq`).
    rw [hFGab_def, PanelHingeFramework.ofNormals_panelRow_eq_hingeRow_of_ends_or_swap Gab Q.ends q₀
        (hrec' e₀ a b he₀ab) t₁ t₂, hq₀a, hq₀b]
    set ρ := annihRow (panelSupportExtensor n_a n_b) t₁ t₂ with hρ_def
    have hrow : BodyHingeFramework.hingeRow a b ρ
        = BodyHingeFramework.hingeRow v b ρ - BodyHingeFramework.hingeRow v a ρ := by
      have h := BodyHingeFramework.hingeRow_sub_hingeRow_eq v a b ρ
      rw [← h, sub_sub_self]
    rw [hrow, sub_eq_add_neg, hrow_b_eq t₁ t₂, hrow_a_eq t₁ t₂]
    exact Submodule.add_mem _ (Submodule.subset_span (hFG_eb_mem t₁ t₂))
      (Submodule.subset_span (hFG_ea_mem t₁ t₂))
  -- ── Step 14: the other rows of `Gab` lie in the row space of `R(G, q₀)`. ───────────────────────
  -- A link `e ≠ e₀` of `Gab` is a link of `G` (`splitOff_isLink`), and `Q.ends e` and `ends e`
  -- agree up to order, so its hinges in `FGab` and in `FG`, both at `q₀`, agree up to sign.
  have hGab_to_G_link : ∀ e u w, Gab.IsLink e u w → e ≠ e₀ → G.IsLink e u w := by
    intro e u w he hne
    rw [hGab_def, Graph.splitOff_isLink] at he
    rcases he with ⟨_, hGlink, _, _⟩ | ⟨rfl, _⟩
    · exact hGlink
    · exact absurd rfl hne
  -- For the OLD block rows (via Q.ends), show each in span(FG.rigidityRows).
  have hso_span : ∀ i : so, FGab.panelRow Q.ends (i : β × _ × _)
      ∈ Submodule.span K FG.rigidityRows := by
    rintro ⟨⟨e, t₁, t₂⟩, hi⟩
    have hlink := hso_link _ hi
    change FGab.panelRow Q.ends (e, t₁, t₂) ∈ Submodule.span K FG.rigidityRows
    by_cases he₀e : e = e₀
    · subst he₀e; exact he₀_rows_mem t₁ t₂
    · -- `e ≠ e₀`: `e` links `(Q.ends e).1` and `(Q.ends e).2` in `G`.
      have hGlink_e : G.IsLink e (Q.ends e).1 (Q.ends e).2 := by
        rcases hrec' e _ _ hlink with he | he <;> rw [he]
        · exact hGab_to_G_link e _ _ hlink he₀e
        · exact (hGab_to_G_link e _ _ hlink he₀e).symm
      -- The row `FGab.panelRow Q.ends (e, t₁, t₂)` is `hingeRow (Q.ends e).1 (Q.ends e).2 ρ`, with
      -- `ρ = annihRow (FGab.supportExtensor e) t₁ t₂`. It is a row of `R(G, q₀)`
      -- (`hingeRow_mem_rigidityRows`): `e` links its ends in `FG.graph = G`, and `ρ` vanishes on
      -- `FG.supportExtensor e = ±FGab.supportExtensor e` (`endsOf_eq_or_swap`,
      -- `panelSupportExtensor_swap`).
      rw [FGab.panelRow_eq_hingeRow_annihRow_of_ends Q.ends (by rfl) t₁ t₂]
      apply Submodule.subset_span
      apply FG.hingeRow_mem_rigidityRows hGlink_e
      -- `ρ ∈ FG.hingeRowBlock e`: `ρ` vanishes on `FG.supportExtensor e`.
      rw [FG.hingeRowBlock_apply, Submodule.mem_dualAnnihilator]
      intro x hx
      rw [Submodule.mem_span_singleton] at hx
      obtain ⟨c, rfl⟩ := hx
      rw [map_smul]
      suffices h : annihRow (FGab.supportExtensor e) t₁ t₂ (FG.supportExtensor e) = 0 by
        rw [h, smul_zero]
      -- Need: (annihRow (FGab.supportExtensor e) t₁ t₂)(FG.supportExtensor e) = 0
      -- FGab.supportExtensor e = panelSupportExtensor(q₀ (Q.ends e).1, q₀ (Q.ends e).2)
      -- FG.supportExtensor e   = panelSupportExtensor(q₀ (ends e).1,   q₀ (ends e).2)
      -- endsOf_eq_or_swap hGlink_e: ends e = Q.ends e ∨ ends e = ((Q.ends e).2, (Q.ends e).1)
      have hFGab_se : FGab.supportExtensor e =
          panelSupportExtensor (fun i => q₀ ((Q.ends e).1, i)) (fun i => q₀ ((Q.ends e).2, i)) := by
        rw [hFGab_def, PanelHingeFramework.toBodyHinge_supportExtensor,
          PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal,
          PanelHingeFramework.ofNormals_normal]
      have hFG_se : FG.supportExtensor e =
          panelSupportExtensor (fun i => q₀ ((ends e).1, i)) (fun i => q₀ ((ends e).2, i)) := by
        rw [hFG_def, PanelHingeFramework.toBodyHinge_supportExtensor,
          PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal,
          PanelHingeFramework.ofNormals_normal]
      rcases G.endsOf_eq_or_swap hGlink_e with h_eq | h_swap
      · -- Same orientation: ends e = Q.ends e → FG.supportExtensor e = FGab.supportExtensor e.
        simp only [← hendsDef] at h_eq
        have hse_eq : FG.supportExtensor e = FGab.supportExtensor e := by
          rw [hFGab_se, hFG_se, h_eq]
        rw [hse_eq, hFGab_se]
        exact annihRow_apply_self _ t₁ t₂
      · -- Swapped: ends e = ((Q.ends e).2, (Q.ends e).1)
        --   → FG.supportExtensor e = -FGab.supportExtensor e.
        simp only [← hendsDef] at h_swap
        have hse_swap : FG.supportExtensor e = -FGab.supportExtensor e := by
          rw [hFGab_se, hFG_se, h_swap]
          exact panelSupportExtensor_swap _ _
        simp only [hse_swap, map_neg, hFGab_se, annihRow_apply_self, neg_zero]
  -- ── Step 15: the count `N + (D − 1) = D(|V(G)| − 1) − c`. ──────────────────────────────────────
  -- N = D*(|V(Gab)|-1) - (c-1) = D*(|V(G)|-2) - c + 1, as |V(Gab)| = |V(G)| - 1.
  have hVGab_card : V(Gab).ncard = V(G).ncard - 1 := by
    rw [hGab_def, Graph.vertexSet_splitOff]
    exact Set.ncard_sdiff_singleton_of_mem hvG
  -- screwDim k = D (from hn).
  have hD_eq : (Graph.bodyBarDim n : ℤ) = screwDim k := by exact_mod_cast hn
  -- N = D*(|V(G)|-2) - (c-1)
  have hN_val : (N : ℤ) = screwDim k * ((V(G).ncard : ℤ) - 2) - (c - 1) := by
    rw [hN_eq, hVGab_card]
    have hVG2 : 2 ≤ V(G).ncard := by linarith [hV3]
    norm_cast
  -- Required rank for G: D*(|V(G)|-1) - c.
  -- The total we need: N + (D-1) = D*(|V(G)|-1) - c.
  have hNpD : (N : ℤ) + ((screwDim k : ℤ) - 1) = screwDim k * ((V(G).ncard : ℤ) - 1) - c := by
    rw [hN_val]; ring
  -- ── Step 16: the new rows: the hinge of `e_b` at `q₀` is `±C(n_a, n_b) ≠ 0`. ───────────────────
  have hFG_eb_ne : FG.supportExtensor e_b ≠ 0 := by
    rcases G.endsOf_eq_or_swap hG_eb with h | h
    · simp only [← hendsDef] at h
      rw [hFG_def, PanelHingeFramework.ofNormals_supportExtensor_eq_panel_of_ends _ e_b h,
        hq₀v, hq₀b, show n_a + n_b = n_a + (1 : K) • n_b from by rw [one_smul],
        panelSupportExtensor_add_smul_right]
      exact (panelSupportExtensor_ne_zero_iff n_a n_b).mpr hgab
    · simp only [← hendsDef] at h
      rw [hFG_def, PanelHingeFramework.ofNormals_supportExtensor_eq_panel_of_ends _ e_b h,
        hq₀b, hq₀v, panelSupportExtensor_swap,
        show n_a + n_b = n_a + (1 : K) • n_b from by rw [one_smul],
        panelSupportExtensor_add_smul_right]
      exact neg_ne_zero.mpr ((panelSupportExtensor_ne_zero_iff n_a n_b).mpr hgab)
  -- Get D-1 new independent rows from e_b at FG.
  have hends_eb : ends e_b = (v, b) ∨ ends e_b = (b, v) := by
    simp only [hendsDef]
    exact G.endsOf_eq_or_swap hG_eb
  obtain ⟨sn, hsn_e, hsn_card, hsn_indep⟩ :=
    FG.exists_independent_panelRow_subfamily_of_edge (ends := ends) (e := e_b)
      (by rcases hends_eb with h | h <;> rw [h] <;>
          [exact hbv.symm; exact (Ne.symm hvb)])
      hFG_eb_ne
  -- The e_b rows are independent through v's screw column.
  have hends_eb_fst_ne_snd : (ends e_b).1 ≠ (ends e_b).2 := by
    rcases hends_eb with h | h <;> rw [h]
    · exact hbv.symm  -- (v, b): need v ≠ b
    · exact hbv        -- (b, v): need b ≠ v
  have hnewpin := FG.linearIndependent_panelRow_comp_single_of_edge
    (ends := ends) (e := e_b) hends_eb_fst_ne_snd.symm hsn_e hsn_indep
  -- The old rows, rows of `FGab` at `Q.ends` in the row space of `R(G, q₀)` (`hso_span`), vanish
  -- on the screw assignments that vanish off `v`, as their links in `Gab` avoid `v`.
  have hold : ∀ (j : so) (x : ScrewSpace K k),
      FGab.panelRow Q.ends (j : β × _ × _)
        (Function.update (0 : α → ScrewSpace K k) v x) = 0 := by
    rintro ⟨i, hi⟩ x
    have hlink := hso_link _ hi
    -- (Q.ends i.1).1 ≠ v and (Q.ends i.1).2 ≠ v (since they're in V(Gab), v ∉ V(Gab))
    have h₁ : (Q.ends i.1).1 ≠ v := by
      intro h
      exact hvVGab (h ▸ (hQ_ends_Gab i.1 _ _ hlink).left_mem)
    have h₂ : (Q.ends i.1).2 ≠ v := by
      intro h
      exact hvVGab (h ▸ (hQ_ends_Gab i.1 _ _ hlink).right_mem)
    simp only [BodyHingeFramework.panelRow, BodyHingeFramework.hingeRow_apply,
      Function.update_of_ne h₁, Function.update_of_ne h₂,
      Pi.zero_apply, sub_zero, map_zero]
  -- ── Step 17: the new rows stay independent on the assignments that vanish off `v`. ─────────────
  have hnewpin_eb : LinearIndependent K (fun i : sn =>
      (FG.panelRow ends (i : β × _ × _)).comp
        (LinearMap.single K (fun _ : α => ScrewSpace K k) v)) := by
    rcases hends_eb with h | h
    · rw [h] at hnewpin; simpa using hnewpin
    · -- `ends e_b = (b, v)`: `hnewpin` gives independence on the assignments that vanish off `b`.
      rw [h] at hnewpin
      -- On the assignments that vanish off `v`, the row `hingeRow b v ρ` is `−ρ` of the screw at
      -- `v`, and on those that vanish off `b` it is `ρ` of the screw at `b`; so the family at `v`
      -- is the negative of the family at `b`, and negation keeps it independent.
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
  -- ── Step 18: the rank of `R(G, q₀)` is at least `N + (D − 1)`. ─────────────────────────────────
  -- The new rows (`hnewpin_eb`) and the old rows (vanishing off `v` by `hold`, in the row space
  -- by `hso_span`) give `Nat.card sn + Nat.card so ≤ finrank`
  -- (`le_finrank_span_rigidityRows_of_pinned_placement`); with `hsn_card : Nat.card sn = D−1`,
  -- `hso_card : Nat.card so = N` and `hNpD : N + (D−1) = D(|V|−1)−c`, this is the bound in `ℤ`.
  have hrank_lb : screwDim k * ((V(G).ncard : ℤ) - 1) - c ≤
      Module.finrank K ↥(Submodule.span K FG.rigidityRows) := by
    have : Fintype sn := Fintype.ofFinite sn
    have : Fintype so := Fintype.ofFinite so
    -- Name the new and old families, so that `le_finrank_span_rigidityRows_of_pinned_placement`
    -- unifies against them rather than against the heavy `ofNormals` lambdas.
    set rn : sn → Module.Dual K (α → ScrewSpace K k) :=
      fun i => FG.panelRow ends (i : β × _ × _) with hrn
    set ro : so → Module.Dual K (α → ScrewSpace K k) :=
      fun i => FGab.panelRow Q.ends (i : β × _ × _) with hro
    -- The NEW (e_b) rows are literal `FG.panelRow`s, hence in `span FG.rigidityRows` (`hnew_span`).
    have hnew_span : ∀ i : sn, rn i ∈ Submodule.span K FG.rigidityRows := by
      rintro ⟨i, hi⟩
      refine Submodule.subset_span (FG.panelRow_mem_rigidityRows ?_)
      rw [hsn_e _ hi]
      rcases hends_eb with h | h <;> rw [h]
      · exact hG_eb
      · exact hG_eb.symm
    -- `Nat.card sn + Nat.card so ≤ finrank`.
    have hbrick : Nat.card sn + Nat.card so ≤
        Module.finrank K ↥(Submodule.span K FG.rigidityRows) :=
      BodyHingeFramework.le_finrank_span_rigidityRows_of_pinned_placement FG (v := v)
        (rn := rn) (ro := ro) hold hnewpin_eb hso_indep hnew_span hso_span
    -- `Nat.card sn + Nat.card so = (D−1) + N`; with `hNpD` this is the ℤ bound.
    rw [hsn_card, hso_card] at hbrick
    rw [← hNpD]
    -- hbrick : (D−1) + N ≤ finrank ; goal (ℤ) : ↑N + (↑D − 1) ≤ ↑finrank
    -- `1 ≤ screwDim k` (`one_le_screwDim`) lets the ℕ-`(D−1)` cast bridge to the ℤ-`(↑D − 1)`.
    have h1D : 1 ≤ screwDim k := one_le_screwDim
    have hbrick' : (N : ℤ) + ((screwDim k : ℤ) - 1) ≤
        Module.finrank K ↥(Submodule.span K FG.rigidityRows) := by
      have := Nat.add_comm (screwDim k - 1) N ▸ hbrick
      zify [h1D] at this
      linarith [this]
    exact hbrick'
  -- ── Step 19: the bound in `ℕ`, for `exists_rankPolynomial_of_le_finrank_linking`. ──────────────
  -- hN: D*(|V(G)|-1) - c ≤ finrank(span FG.rigidityRows). Convert to ℕ.
  have h1V : 1 ≤ V(G).ncard := by
    exact (Set.ncard_pos (Set.toFinite _)).2 ⟨v, hvG⟩
  have hD1 : 1 ≤ screwDim k := one_le_screwDim
  have hrank_lb_nat : (screwDim k * (V(G).ncard - 1) - c.toNat) ≤
      Module.finrank K (Submodule.span K FG.rigidityRows) := by
    -- First: N + (D-1) ≤ finrank (ℕ) from hrank_lb via hNpD.
    have hbound : N + (screwDim k - 1) ≤ Module.finrank K ↥(Submodule.span K FG.rigidityRows) := by
      have hrank_lb_Z := hrank_lb
      rw [← hNpD] at hrank_lb_Z
      exact_mod_cast hrank_lb_Z
    -- `D*(V-1) - c.toNat = N + (D-1)` (ℕ), by `sub_toNat_eq_of_add_pred_eq`.
    rw [sub_toNat_eq_of_add_pred_eq hc h1V hD1 hNpD]
    exact hbound
  -- hne_G : ∀ e, G.IsLink e (ends e).1 (ends e).2 → FG.supportExtensor e ≠ 0
  -- Proved by case split: e = e_b (hFG_eb_ne), e = e_a (hFG_ea + nonzero panelSupport),
  -- otherwise (e is a non-v, non-e₀ Gab-link → FG.supportExtensor e = ±FGab.supportExtensor e ≠ 0).
  have hne_G : ∀ e, G.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.supportExtensor e ≠ 0 := by
    intro e he
    by_cases heb : e = e_b
    · -- e = e_b: directly from hFG_eb_ne
      subst heb; exact hFG_eb_ne
    · by_cases hea : e = e_a
      · -- e = e_a: FG.supportExtensor e_a = ±panelSupportExtensor n_a n_b ≠ 0
        subst hea
        rcases hFG_ea with h | h <;> rw [h]
        · exact smul_ne_zero (by norm_num) ((panelSupportExtensor_ne_zero_iff n_a n_b).mpr hgab)
        · exact (panelSupportExtensor_ne_zero_iff n_a n_b).mpr hgab
      · -- Otherwise: e avoids v (not v-incident since hclv gives only e_a, e_b are v-incident)
        -- so e is a Gab-link (not e₀ since e₀ ∉ E(G)).
        -- FG.supportExtensor e = ±FGab.supportExtensor e ≠ 0.
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
        have hne₀e : e ≠ e₀ := fun heq => he₀ (heq ▸ he.edge_mem)
        have hGab_e : Gab.IsLink e (ends e).1 (ends e).2 := by
          rw [hGab_def, Graph.splitOff_isLink]
          exact Or.inl ⟨hne₀e, he, h1, h2⟩
        have hQGab_e : Gab.IsLink e (Q.ends e).1 (Q.ends e).2 := hQ_ends_Gab e _ _ hGab_e
        have hFGab_ne : FGab.supportExtensor e ≠ 0 := hne₀ e hQGab_e
        -- FG.supportExtensor e = ±FGab.supportExtensor e
        have hFGab_se : FGab.supportExtensor e =
            panelSupportExtensor (fun i => q₀ ((Q.ends e).1, i))
              (fun i => q₀ ((Q.ends e).2, i)) := by
          rw [hFGab_def, PanelHingeFramework.toBodyHinge_supportExtensor,
            PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal,
            PanelHingeFramework.ofNormals_normal]
        have hFG_se : FG.supportExtensor e =
            panelSupportExtensor (fun i => q₀ ((ends e).1, i)) (fun i => q₀ ((ends e).2, i)) := by
          rw [hFG_def, PanelHingeFramework.toBodyHinge_supportExtensor,
            PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal,
            PanelHingeFramework.ofNormals_normal]
        have hG_Qe : G.IsLink e (Q.ends e).1 (Q.ends e).2 :=
          hGab_to_G_link e _ _ hQGab_e hne₀e
        rcases G.endsOf_eq_or_swap hG_Qe with h_eq | h_swap
        · -- ends e = Q.ends e → FG.supportExtensor e = FGab.supportExtensor e
          have hse_eq : FG.supportExtensor e = FGab.supportExtensor e := by
            rw [hFG_se, hFGab_se]
            have hendse : ends e = ((Q.ends e).1, (Q.ends e).2) := hendsDef ▸ h_eq
            congr 1 <;> ext i <;> congr 1
            · exact Prod.ext (show (ends e).1 = (Q.ends e).1 from congrArg Prod.fst hendse) rfl
            · exact Prod.ext (show (ends e).2 = (Q.ends e).2 from congrArg Prod.snd hendse) rfl
          rw [hse_eq]; exact hFGab_ne
        · -- ends e = ((Q.ends e).2, (Q.ends e).1) → FG.supportExtensor e = -FGab.supportExtensor e
          have hse_neg : FG.supportExtensor e = -FGab.supportExtensor e := by
            rw [hFG_se, hFGab_se]
            rw [show ends e = ((Q.ends e).2, (Q.ends e).1) from hendsDef ▸ h_swap]
            exact panelSupportExtensor_swap _ _
          rw [hse_neg]; exact neg_ne_zero.mpr hFGab_ne
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
      (PanelHingeFramework.ofNormals G ends q').toBodyHinge hn hVGne' hCq'
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
    hrank_eq_q',
    PanelHingeFramework.ofNormals_recordsLinks_of_hends G ends q' hends_G⟩

end CombinatorialRigidity.Molecular
