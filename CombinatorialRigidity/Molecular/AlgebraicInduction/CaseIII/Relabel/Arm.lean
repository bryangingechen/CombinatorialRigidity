/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.AlgebraicInduction.CaseIII.Relabel.Chain

/-!
# Case III: the third framework, and the form at the new edge of `G_i`

Lemmas for Case III of KT Theorem 5.5 (Katoh and Tanigawa 2011, *A proof of the molecular
conjecture*, Discrete Comput. Geom. **45**, §6.4), presented in
`sec:molecular-algebraic-induction-caseIII`. The file proves:

* in the case `d = 3`, a generic full-rank realization from Katoh and Tanigawa's third framework
  `(G, p_3)` (`case_III_arm_realization_M3`), a step of `lem:case-III-candidate-dispatch-d3`;
* for a chain `v₀ ⋯ v_d` and `2 ≤ i ≤ d − 1`, the value of the moves of `CaseIII/Relabel/Basic.lean`
  along the chain at the form at the new edge `v₀v₂` of `G_1` (`wstep_foldl_hingeRow_telescope`),
  from which the form at the new edge `v_{i−1} v_{i+1}` of `G_i` lies in the row space of `G − v_i`
  once the forms at the edges of the chain are rows (`wstep_foldl_freshEdge_slot_mem`,
  `freshEdge_surviving_row_mem`): steps of `lem:case-III-chain-eq666`.

`CaseIII/Relabel/ChainColumn.lean` and `ForkedArm.lean` prove the rest of
`lem:case-III-chain-eq666`.
-/

namespace CombinatorialRigidity.Molecular

variable {k : ℕ}

open scoped Graph

variable {α β : Type*}

variable {K : Type*} [Field K]

/-- **The third framework, then the rotation** (a step of `lem:case-III-candidate-dispatch-d3`; KT
pp. 686–691): let `v`, `a`, `b` be distinct vertices of `G` and `c` a vertex other than `a` and `v`,
with edges `e_a : va`, `e_b : vb` and `e_c : ac`, where the edges at `a` are `e_a` and `e_c`
(`hcla`), and `|V(G)| ≥ 3`. Let `ends₀` give each link of `G − v` its ends in some order (`hrecGv`),
and let `ends₃` give `e_c`, `e_a` and `e_b` the ends `(a, c)`, `(a, v)` and `(v, b)` and agree with
`ends₀` elsewhere. For the transposition `τ` of `a` and `v`, let `ends₃` give the links of `G − a`
their ends (`hends_Gva`), with nonzero hinges in `ofNormals (G − a) ends₃ (q ∘ τ)` (`hne_Gva`). Let
`q(c)` be linearly independent of `n'''` and of `q(a)` (`hLn`, `hgca`), let `ρ` be a linear form
with `ρ(C(q(c), n''')) ≠ 0` (`hρgate`) and `ρ(C(q(a), q(b))) = 0` (`hρe₀`) such that
`hingeRow a b ρ` lies in the span of the rows of `ofNormals (G − v) ends₀ q` (`hρGv`), and let `w`
be `D(|V(G)| − 2)` linearly independent forms, each a row of `ofNormals (G − v) ends₀ q` or a form
`hingeRow a b ρ'` with `ρ'(C(q(a), q(b))) = 0` (`hwmem`). If `G` has deficiency `0`, it has a
generic full-rank realization.

This is Katoh and Tanigawa's third framework `(G, p_3)`, with the line `L''` in the panel of `c`
given by `n'''` at `ac` (KT eqs. (6.32) and (6.33), p. 687), and the rotation of the panel of `a`
about it. As in the note after `lem:case-III-claim612-p3-placement`, `case_III_arm_realization`
applies with `a`, `c` and `v` in the roles of `v`, `a` and `b`, at `G − a`, the selector `ends₃`,
the normals `q ∘ τ` (those of `lem:splitOff-ofNormals-relabel`), the form `−ρ` and the forms
`S ↦ w j (S ∘ τ)`. Its hypotheses hold: `ρ` vanishes on `C(q(a), q(c))`, by
`acolumn_mem_hingeRowBlock_of_span_rigidityRows`, the span form of KT eq. (6.44) (p. 691);
`hingeRow v c ρ` lies in the span of the rows of `ofNormals (G − a) ends₃ (q ∘ τ)`, by
`funLeft_dualMap_sub_acolumn_mem_span_rigidityRows` at `hingeRow a b ρ`, as `hingeRow v b ρ` is a
row there at `e_b`; and `case_III_bottom_relabel` takes each form `w j` to a row of that framework
or a form `hingeRow c v ρ'` with `ρ'(C(q(c), q(a))) = 0`. Only `case_III_candidate_dispatch` uses
it, when `r` does not vanish on a line in the panel of `c` (KT Claim 6.12, p. 690). -/
theorem PanelHingeFramework.case_III_arm_realization_M3 [Infinite K]
    [Finite α] [Finite β] [DecidableEq α]
    (G : Graph α β) (ends₀ ends₃ : β → α × α) {q : α × Fin (k + 2) → K}
    {v a b c : α} {e_a e_b e_c : β}
    (hva : v ≠ a) (hab : a ≠ b) (hvb : v ≠ b) (hca : c ≠ a) (hcv : c ≠ v)
    (hG_ea : G.IsLink e_a v a) (hG_eb : G.IsLink e_b v b) (hG_ec : G.IsLink e_c a c)
    (heac : e_a ≠ e_c)
    (hcla : ∀ e x, G.IsLink e a x → e = e_a ∨ e = e_c)
    (hrecGv : ∀ e x y, (G.removeVertex v).IsLink e x y →
      ends₀ e = (x, y) ∨ ends₀ e = (y, x))
    (hends₃_ec : ends₃ e_c = (a, c)) (hends₃_ea : ends₃ e_a = (a, v))
    (hends₃_eb : ends₃ e_b = (v, b))
    (hends₃_off : ∀ e, e ≠ e_a → e ≠ e_b → e ≠ e_c → ends₃ e = ends₀ e)
    (hends_Gva : ∀ e x y, (G.removeVertex a).IsLink e x y →
      (G.removeVertex a).IsLink e (ends₃ e).1 (ends₃ e).2)
    (hne_Gva : ∀ e, (G.removeVertex a).IsLink e (ends₃ e).1 (ends₃ e).2 →
      (PanelHingeFramework.ofNormals (G.removeVertex a) ends₃
        (fun p => q (Equiv.swap a v p.1, p.2))).toBodyHinge.supportExtensor e ≠ 0)
    (hV3 : 3 ≤ V(G).ncard)
    {n''' : Fin (k + 2) → K}
    (hLn : LinearIndependent K ![(fun i => q (c, i)), n'''])
    (hgca : LinearIndependent K ![(fun i => q (c, i)), (fun i => q (a, i))])
    {ρ : Module.Dual K (ScrewSpace K k)}
    (hρgate : ρ (panelSupportExtensor (fun i => q (c, i)) n''') ≠ 0)
    (hρe₀ : ρ (panelSupportExtensor (fun i => q (a, i)) (fun i => q (b, i))) = 0)
    (hρGv : BodyHingeFramework.hingeRow a b ρ ∈ Submodule.span K
      (PanelHingeFramework.ofNormals (G.removeVertex v) ends₀ q).toBodyHinge.rigidityRows)
    {ιb : Type*} [Finite ιb] {w : ιb → Module.Dual K (α → ScrewSpace K k)}
    (hwcard : Nat.card ιb = screwDim k * (V(G).ncard - 2))
    (hw : LinearIndependent K w)
    (hwmem : ∀ j, w j ∈
        (PanelHingeFramework.ofNormals (G.removeVertex v) ends₀ q).toBodyHinge.rigidityRows ∨
      ∃ ρ' : Module.Dual K (ScrewSpace K k),
        ρ' (panelSupportExtensor (fun i => q (a, i)) (fun i => q (b, i))) = 0 ∧
        w j = BodyHingeFramework.hingeRow a b ρ')
    {n : ℕ} (hdef : G.deficiency n = 0) :
    PanelHingeFramework.HasGenericFullRankRealization K k n G := by
  classical
  set qρ : α × Fin (k + 2) → K := fun p => q (Equiv.swap a v p.1, p.2) with hqρ
  set Fv := (PanelHingeFramework.ofNormals (G.removeVertex v) ends₀ q).toBodyHinge with hFv
  -- The normals `qρ` read `q` at the transposed body: `qρ(c,·) = q(c,·)`, `qρ(v,·) = q(a,·)`.
  have hqρc : (fun i => qρ (c, i)) = (fun i => q (c, i)) := by
    funext i; rw [hqρ]; simp only [Equiv.swap_apply_of_ne_of_ne hca hcv]
  have hqρv : (fun i => qρ (v, i)) = (fun i => q (a, i)) := by
    funext i; rw [hqρ]; simp only [Equiv.swap_apply_right]
  -- The `e_c`-link of `Fv = ofNormals (G − v) ends₀ q`: `e_c` survives `removeVertex v`
  -- (endpoints `a, c ≠ v`).
  have hGv_ec : (G.removeVertex v).IsLink e_c a c :=
    Graph.removeVertex_isLink.mpr ⟨hG_ec, hva.symm, hcv⟩
  have hFv_link_ec : Fv.graph.IsLink e_c a c := by
    rw [hFv, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]
    exact hGv_ec
  -- Degree-2 at `a` inside `Fv`: the only `(G − v)`-link at `a` is `e_c` (the `e_a` branch links
  -- `v` and so cannot survive `removeVertex v`).
  have hdeg2 : ∀ f x, Fv.graph.IsLink f a x → f = e_c := by
    intro f x hlink
    rw [hFv, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph] at hlink
    obtain ⟨hGlink, _, hxv⟩ := Graph.removeVertex_isLink.mp hlink
    rcases hcla f x hGlink with rfl | rfl
    · rcases hG_ea.eq_and_eq_or_eq_and_eq hGlink with ⟨h, _⟩ | ⟨h, _⟩
      · exact absurd h hva
      · exact absurd h.symm hxv
    · rfl
  have hdeg2r : ∀ f x, Fv.graph.IsLink f x a → f = e_c := fun f x hlink => hdeg2 f x hlink.symm
  -- `ρ` vanishes on `C(q(a), q(c))` by `acolumn_mem_hingeRowBlock_of_span_rigidityRows`: the
  -- restriction of `hingeRow a b ρ` to `a` is `ρ`, which lies in `Fv.hingeRowBlock e_c`, so `ρ`
  -- vanishes on `Fv.supportExtensor e_c = ±C(q(a), q(c))`.
  have hρ_ac : ρ (panelSupportExtensor (fun i => q (a, i)) (fun i => q (c, i))) = 0 := by
    have hcol :=
      BodyHingeFramework.acolumn_mem_hingeRowBlock_of_span_rigidityRows (Fab := Fv) (Fv := Fv)
        (a := a) (c := c) (e_c := e_c) (Ne.symm hca) hFv_link_ec rfl hdeg2 hdeg2r hρGv
    rw [BodyHingeFramework.hingeRow_comp_single_tail hab] at hcol
    have hperp := (Fv.mem_hingeRowBlock_iff e_c ρ).1 hcol
    rw [hFv, PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_normal,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_ends] at hperp
    -- `ends₀ e_c ∈ {(a,c),(c,a)}`; either gives `ρ ⊥ ±C(q(ac))`.
    rcases hrecGv e_c a c hGv_ec with he | he
    · rwa [he] at hperp
    · rw [he, panelSupportExtensor_swap, map_neg, neg_eq_zero] at hperp; exact hperp
  -- The framework `Fva = ofNormals (G − a) ends₃ qρ`.
  set Fva := (PanelHingeFramework.ofNormals (G.removeVertex a) ends₃ qρ).toBodyHinge with hFva
  -- `c, v ∈ V(G − a)` and `a ∉ V(G − a)`.
  have ha_mem : a ∈ V(G) := hG_ea.right_mem
  have hc_mem : c ∈ V(G) := hG_ec.right_mem
  have hv_mem : v ∈ V(G) := hG_ea.left_mem
  have hcard_Gva : V(G.removeVertex a).ncard = V(G).ncard - 1 := by
    rw [Graph.vertexSet_removeVertex, Set.ncard_sdiff_singleton_of_mem ha_mem]
  refine PanelHingeFramework.case_III_arm_realization (k := k) G (G.removeVertex a) ends₃
    (q := qρ) (v := a) (a := c) (b := v) (e_a := e_c) (e_b := e_a) (n' := n''')
    ?hvVc ?haVc ?hbVc hG_ec hG_ea.symm hends₃_ec hends₃_ea heac.symm
    ?hleG ?hsplitG hends_Gva hne_Gva ?hVone ?hVcard ?hLn ?hgab
    (ρ := -ρ) ?hρgate ?hρe₀ ?hρGv (ιb := ιb)
    (w := (LinearMap.funLeft K (ScrewSpace K k) (Equiv.swap a v)).dualMap ∘ w)
    ?hwcard ?hw ?hwmem hdef
  case hvVc => rw [Graph.vertexSet_removeVertex]; exact fun h => h.2 rfl
  case haVc => rw [Graph.vertexSet_removeVertex]; exact ⟨hc_mem, hca⟩
  case hbVc => rw [Graph.vertexSet_removeVertex]; exact ⟨hv_mem, hva⟩
  case hleG => exact fun e u w hlink => (Graph.removeVertex_isLink.mp hlink).1
  case hsplitG =>
    intro e u w hlink
    by_cases hua : u = a
    · subst u; rcases hcla e w hlink with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
    · by_cases hwa : w = a
      · subst w; rcases hcla e u hlink.symm with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl rfl
      · exact Or.inr (Or.inr (Graph.removeVertex_isLink.mpr ⟨hlink, hua, hwa⟩))
  case hVone => rw [hcard_Gva]; omega
  case hVcard => rw [hcard_Gva]; omega
  case hLn => rw [hqρc]; exact hLn
  case hgab => rw [hqρc, hqρv]; exact hgca
  case hρgate =>
    rw [hqρc, LinearMap.neg_apply, neg_ne_zero]; exact hρgate
  case hρe₀ =>
    rw [hqρc, hqρv, LinearMap.neg_apply, panelSupportExtensor_swap, map_neg, hρ_ac,
      neg_zero, neg_zero]
  case hρGv =>
    -- `hingeRow c v (-ρ) = hingeRow v c ρ ∈ span Fva.rigidityRows`. The move
    -- `funLeft_dualMap_sub_acolumn_mem_span_rigidityRows` at `φ := hingeRow a b ρ` (renamed
    -- `hingeRow v b ρ`, restriction to `a` `ρ`) gives `hingeRow v b ρ - hingeRow v c ρ ∈ span`, and
    -- `hingeRow v b ρ` is a row of `Fva` at `e_b` (by `hρe₀`), so `Submodule.sub_mem`.
    rw [BodyHingeFramework.hingeRow_swap c v (-ρ), neg_neg]
    have htrans : ∀ f x y, Fv.graph.IsLink f x y → x ≠ a → y ≠ a →
        Fva.graph.IsLink f x y ∧ Fv.hingeRowBlock f ≤ Fva.hingeRowBlock f := by
      intro f x y hlink hxa hya
      rw [hFv, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph] at hlink
      obtain ⟨hGflink, hxv, hyv⟩ := Graph.removeVertex_isLink.mp hlink
      have hfne_a : f ≠ e_a := by
        rintro rfl
        rcases hG_ea.eq_and_eq_or_eq_and_eq hGflink with ⟨hh, _⟩ | ⟨hh, _⟩
        · exact hxv hh.symm
        · exact hyv hh.symm
      have hfne_b : f ≠ e_b := by
        rintro rfl
        rcases hG_eb.eq_and_eq_or_eq_and_eq hGflink with ⟨hh, _⟩ | ⟨hh, _⟩
        · exact hxv hh.symm
        · exact hyv hh.symm
      have hfne_c : f ≠ e_c := by
        rintro rfl
        rcases hG_ec.eq_and_eq_or_eq_and_eq hGflink with ⟨hh, _⟩ | ⟨hh, _⟩
        · exact hxa hh.symm
        · exact hya hh.symm
      refine ⟨?_, ?_⟩
      · rw [hFva, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph,
          Graph.removeVertex_isLink]
        exact ⟨hGflink, hxa, hya⟩
      · -- the `f`-extensors at `Fva` and `Fv` coincide off `{e_a, e_b, e_c}` (`ends₃ f = ends₀ f`,
        -- `qρ = q` at the recorded endpoints `∉ {a, v}`), so the blocks are equal.
        intro r hr
        rw [Fva.mem_hingeRowBlock_iff]
        rw [Fv.mem_hingeRowBlock_iff] at hr
        rw [hFva, PanelHingeFramework.toBodyHinge_supportExtensor,
          PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal,
          PanelHingeFramework.ofNormals_ends, hends₃_off f hfne_a hfne_b hfne_c]
        rw [hFv, PanelHingeFramework.toBodyHinge_supportExtensor,
          PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal,
          PanelHingeFramework.ofNormals_ends] at hr
        rcases hrecGv f x y hlink with he | he <;> rw [he] at hr ⊢ <;>
          simp only [hqρ, Equiv.swap_apply_of_ne_of_ne hxa hxv,
            Equiv.swap_apply_of_ne_of_ne hya hyv] <;> exact hr
    have hw9a := BodyHingeFramework.funLeft_dualMap_sub_acolumn_mem_span_rigidityRows
      (Fv := Fv) (Fva := Fva) (v := v) (a := a) (c := c) (e_c := e_c)
      hca hcv hFv_link_ec hdeg2 hdeg2r
      (fun f x y hlink => by
        rw [hFv, PanelHingeFramework.toBodyHinge_graph,
          PanelHingeFramework.ofNormals_graph] at hlink
        exact (Graph.removeVertex_isLink.mp hlink).2)
      htrans (φ := BodyHingeFramework.hingeRow a b ρ) hρGv
    -- `(funLeft (a v)).dualMap (hingeRow a b ρ) = hingeRow v b ρ`; `a`-column is `ρ`.
    rw [BodyHingeFramework.hingeRow_funLeft_dualMap, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hab) (Ne.symm hvb),
      BodyHingeFramework.hingeRow_comp_single_tail hab] at hw9a
    -- `hingeRow v b ρ` is a row of `Fva` at `e_b`.
    have hvb_row : BodyHingeFramework.hingeRow v b ρ ∈ Submodule.span K Fva.rigidityRows := by
      refine Submodule.subset_span ⟨e_b, v, b, ?_, ρ, ?_, rfl⟩
      · rw [hFva, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph,
          Graph.removeVertex_isLink]
        exact ⟨hG_eb, hva, Ne.symm hab⟩
      · rw [Fva.mem_hingeRowBlock_iff, hFva, PanelHingeFramework.toBodyHinge_supportExtensor,
          PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal,
          PanelHingeFramework.ofNormals_ends, hends₃_eb]
        simp only [hqρ, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne (Ne.symm hab)
          (Ne.symm hvb)]
        exact hρe₀
    have := Submodule.sub_mem _ hvb_row hw9a
    rwa [sub_sub_cancel] at this
  case hwcard =>
    -- both `w̃` and `w` index by `ιb`; the count matches (`V(G − a).ncard − 1 = V(G).ncard − 2`).
    rw [hwcard, hcard_Gva, Nat.sub_sub]
  case hw =>
    exact hw.map' _ (LinearMap.ker_eq_bot.2
      (LinearMap.dualMap_injective_of_surjective
        (LinearMap.funLeft_surjective_of_injective _ _ (Equiv.swap a v) (Equiv.injective _))))
  case hwmem =>
    intro j
    -- the `∘` and the identities `qρ(c,·) = q(c,·)` and `qρ(v,·) = q(a,·)`, then
    -- `case_III_bottom_relabel`.
    simp only [Function.comp_apply, hqρc, hqρv]
    exact PanelHingeFramework.case_III_bottom_relabel hva hab hvb hca hcv hG_ea hG_eb hG_ec hcla
      (fun e x y hlink => (Graph.removeVertex_isLink.mp hlink).1)
      (fun e x y hlink => ⟨(Graph.removeVertex_isLink.mp hlink).2.1,
        (Graph.removeVertex_isLink.mp hlink).2.2⟩)
      (fun e x y hlink => hrecGv e x y hlink) hends₃_eb hends₃_off (hwmem j)

/-! ## Rows at the edges of the chain in `G − v_i`

For `2 ≤ i ≤ d`, the edges `v_s v_{s+1}` with `s + 1 < i` do not meet `v_i`, so they are edges of
`G − v_i`. `freshEdge_surviving_row_mem`, a step of `lem:case-III-chain-eq666`, gives a form at such
an edge as a row. -/

/-- **A row at an edge of the chain in `G − v_i`** (a step of `lem:case-III-chain-eq666`): for
`s + 1 < i ≤ d`, if `ρ₀` vanishes on the hinge of `ofNormals (G − v_i) ends qρ` at the edge
`v_s v_{s+1}` (`hperp`), then `hingeRow v_s v_{s+1} ρ₀` lies in the span of its rows, as a row at
this edge, which does not meet `v_i`. `chainData_freshEdge_slot_mem`
(`CaseIII/Relabel/ChainColumn.lean`) uses it for the forms of `wstep_foldl_freshEdge_slot_mem`. -/
theorem _root_.Graph.ChainData.freshEdge_surviving_row_mem
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (i : Fin (cd.d + 1)) (s : ℕ)
    (hs : s + 1 < (i : ℕ))
    {ends : β → α × α} {qρ : α × Fin (k + 2) → K} (ρ₀ : Module.Dual K (ScrewSpace K k))
    -- `ρ₀` vanishes on the hinge of the edge `v_s v_{s+1}`:
    (hperp : ρ₀ ((PanelHingeFramework.ofNormals (G.removeVertex
        (cd.vtx i)) ends qρ).toBodyHinge.supportExtensor (cd.edge ⟨s, by omega⟩)) = 0) :
    BodyHingeFramework.hingeRow (cd.vtx ⟨s, by omega⟩) (cd.vtx ⟨s + 1, by omega⟩) ρ₀ ∈
      Submodule.span K (PanelHingeFramework.ofNormals (G.removeVertex
        (cd.vtx i)) ends qρ).toBodyHinge.rigidityRows := by
  classical
  set Fva := (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i)) ends qρ).toBodyHinge
    with hFva
  apply Submodule.subset_span
  -- the chain edge `edge s` links `vtx s — vtx (s+1)` in `G` (the `link` field at `⟨s,_⟩`).
  have hlinkG : G.IsLink (cd.edge ⟨s, by omega⟩) (cd.vtx ⟨s, by omega⟩)
      (cd.vtx ⟨s + 1, by omega⟩) := by
    have h := cd.link ⟨s, by omega⟩
    simpa only [Fin.castSucc_mk, Fin.succ_mk] using h
  -- both endpoints survive `removeVertex (vtx i)`: indices `s, s+1 < i`, distinct from `i`
  -- (`vtx_inj`, comparing `Fin.val`s).
  have hsi : cd.vtx ⟨s, by omega⟩ ≠ cd.vtx i :=
    fun he => by have : s = (i : ℕ) := congrArg Fin.val (cd.vtx_inj he); omega
  have hs1i : cd.vtx ⟨s + 1, by omega⟩ ≠ cd.vtx i :=
    fun he => by have : s + 1 = (i : ℕ) := congrArg Fin.val (cd.vtx_inj he); omega
  have hlinkGv : (G.removeVertex (cd.vtx i)).IsLink (cd.edge ⟨s, by omega⟩)
      (cd.vtx ⟨s, by omega⟩) (cd.vtx ⟨s + 1, by omega⟩) :=
    Graph.removeVertex_isLink.mpr ⟨hlinkG, hsi, hs1i⟩
  -- a row at the link `edge s`: the link in `Fva.graph`, and `ρ₀ ∈ hingeRowBlock (edge s)`.
  refine BodyHingeFramework.hingeRow_mem_rigidityRows Fva (e := cd.edge ⟨s, by omega⟩) ?_ ?_
  · rw [hFva, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]
    exact hlinkGv
  · exact (Fva.mem_hingeRowBlock_iff _ ρ₀).2 hperp

/-! ## The form at the new edge of `G_i`

Steps of `lem:case-III-chain-eq666`. For `2 ≤ i ≤ d − 1`, the maps `wstep v_{s+1} v_{s+2} v_{s+3}`,
for `s = 0, …, i − 2` in this order, take the form `hingeRow v₀ v₂ ρ₀` at the new edge of `G_1` to

  `(∑ s < i − 1, hingeRow v_s v_{s+1} ρ₀) + hingeRow v_{i−1} v_{i+1} ρ₀`

(`wstep_foldl_hingeRow_telescope`): forms at the edges `v_s v_{s+1}` of `G − v_i`, and the form at
the new edge `v_{i−1} v_{i+1}` of `G_i`. The moves take the row space of `G − v₁` into that of
`G − v_i`, with the normals renamed (`shiftBodyListAsc_foldl_mem_span_rigidityRows`), so the form at
the new edge lies in the row space of `G − v_i` once the forms at the edges of the chain are rows
(`wstep_foldl_freshEdge_slot_mem`). `chainData_freshEdge_slot_mem`
(`CaseIII/Relabel/ChainColumn.lean`) puts these together. -/

/-- **The move fixes a form at a pair that meets neither `a` nor `v`** (a step of
`lem:case-III-chain-eq666`): if `x` and `y` are neither `a` nor `v`, then
`wstep v a c (hingeRow x y ρ) = hingeRow x y ρ`, as the transposition of `a` and `v` fixes `x` and
`y` (`hingeRow_funLeft_dualMap`) and the restriction to `a` is zero (`hingeRow_comp_single_off`). In
the closed form of the moves along the chain, these are the forms at the edges already passed. -/
theorem BodyHingeFramework.wstep_hingeRow_off [DecidableEq α] {v a c x y : α}
    (hxa : x ≠ a) (hxv : x ≠ v) (hya : y ≠ a) (hyv : y ≠ v)
    (ρ : Module.Dual K (ScrewSpace K k)) :
    BodyHingeFramework.wstep (k := k) v a c (BodyHingeFramework.hingeRow x y ρ)
      = BodyHingeFramework.hingeRow x y ρ := by
  rw [BodyHingeFramework.wstep_apply, BodyHingeFramework.hingeRow_funLeft_dualMap,
    Equiv.swap_apply_of_ne_of_ne hxa hxv, Equiv.swap_apply_of_ne_of_ne hya hyv,
    BodyHingeFramework.hingeRow_comp_single_off (Ne.symm hxa) (Ne.symm hya)]
  rw [show BodyHingeFramework.hingeRow (k := k) v c 0 = 0 from by
    rw [BodyHingeFramework.hingeRow, LinearMap.zero_comp], sub_zero]

/-- **The move on a form at a pair that meets `a`** (a step of `lem:case-III-chain-eq666`): if `x`
is neither `a` nor `v`, then `wstep v a c (hingeRow x a ρ) = hingeRow x v ρ + hingeRow v c ρ`: the
transposition takes the form to `hingeRow x v ρ`, and its restriction to `a` is `−ρ`, so the move
adds `hingeRow v c ρ`. At the step `s` of the chain,
`(x, v, a, c) = (v_s, v_{s+1}, v_{s+2}, v_{s+3})`: the form at `v_s v_{s+2}` becomes the form at the
edge `v_s v_{s+1}` plus the form at `v_{s+1} v_{s+3}`. -/
theorem BodyHingeFramework.wstep_hingeRow_frontier [DecidableEq α] {v a c x : α}
    (hxa : x ≠ a) (hxv : x ≠ v)
    (ρ : Module.Dual K (ScrewSpace K k)) :
    BodyHingeFramework.wstep (k := k) v a c (BodyHingeFramework.hingeRow x a ρ)
      = BodyHingeFramework.hingeRow x v ρ + BodyHingeFramework.hingeRow v c ρ := by
  rw [BodyHingeFramework.wstep_apply, BodyHingeFramework.hingeRow_funLeft_dualMap,
    Equiv.swap_apply_of_ne_of_ne hxa hxv, Equiv.swap_apply_left,
    BodyHingeFramework.hingeRow_swap x a ρ,
    BodyHingeFramework.hingeRow_comp_single_tail (Ne.symm hxa)]
  ext S
  simp only [LinearMap.sub_apply, LinearMap.add_apply, BodyHingeFramework.hingeRow_apply,
    LinearMap.neg_apply, map_sub]
  ring

/-- **The moves along the chain, in closed form** (a step of `lem:case-III-chain-eq666`): for
`w : ℕ → α` injective on `{0, …, m + 2}`, the maps `wstep (w (s+1)) (w (s+2)) (w (s+3))` for
`s = 0, …, m − 1`, the first applied first, take `hingeRow (w 0) (w 2) ρ₀` to
`(∑ s < m, hingeRow (w s) (w (s+1)) ρ₀) + hingeRow (w m) (w (m+2)) ρ₀`. The proof is by induction on
`m`, with `wstep_hingeRow_off` for the forms at the pairs already passed and
`wstep_hingeRow_frontier` for the last. At the vertices of a chain and `m = i − 1`, the last form is
the form at the new edge `v_{i−1} v_{i+1}` of `G_i`. The statement asks for injectivity on the range
it reads, not on `ℕ`, which a map into the finite vertex type of the proof of `lem:case-III` cannot
have; the chain gives it (`ChainData.vtx_inj`). -/
theorem BodyHingeFramework.wstep_foldl_hingeRow_telescope [DecidableEq α]
    (w : ℕ → α) (m : ℕ) (hinj : Set.InjOn w (Set.Iic (m + 2)))
    (ρ₀ : Module.Dual K (ScrewSpace K k)) :
    ((List.ofFn fun s : Fin m => (w ((s : ℕ) + 1), w ((s : ℕ) + 2), w ((s : ℕ) + 3))).foldl
        (fun T b => (BodyHingeFramework.wstep (k := k) b.1 b.2.1 b.2.2).comp T) LinearMap.id)
      (BodyHingeFramework.hingeRow (w 0) (w 2) ρ₀)
      = (∑ s ∈ Finset.range m, BodyHingeFramework.hingeRow (w s) (w (s + 1)) ρ₀)
        + BodyHingeFramework.hingeRow (w m) (w (m + 2)) ρ₀ := by
  induction m with
  | zero => simp
  | succ m ih =>
    -- The IH needs injectivity on the smaller range `0 … m+2`, by monotonicity of `Set.InjOn`.
    have ihm := ih (hinj.mono (Set.Iic_subset_Iic.mpr (by omega)))
    -- Distinctness on the range: `w i ≠ w j` whenever `i, j ≤ m+2` and `i ≠ j`, from `hinj`,
    -- injectivity on `Set.Iic (m+1+2)`, here used at indices `≤ m+2`.
    have hne : ∀ i j : ℕ, i ≤ m + 2 → j ≤ m + 2 → i ≠ j → w i ≠ w j := fun i j hi hj hij h =>
      hij (hinj (Set.mem_Iic.mpr (by omega)) (Set.mem_Iic.mpr (by omega)) h)
    -- Peel the last body `(w_{m+1}, w_{m+2}, w_{m+3})` off the `ofFn` list (`ofFn_succ'`); the
    -- inner fold over the first `m` bodies is the IH; the last `wstep` then advances the frontier.
    rw [List.ofFn_succ', List.concat_eq_append, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, LinearMap.comp_apply, Fin.val_last,
      Fin.val_castSucc]
    rw [ihm]
    -- `wstep` is linear: distribute over the IH sum + frontier term.
    rw [map_add, map_sum]
    -- the `m` surviving rows (`s < m+1 < m+2`, all `≤ m+2`) are fixed by the last `wstep`.
    have hoff : ∀ s ∈ Finset.range m,
        BodyHingeFramework.wstep (k := k) (w (m + 1)) (w (m + 2)) (w (m + 3))
            (BodyHingeFramework.hingeRow (w s) (w (s + 1)) ρ₀)
          = BodyHingeFramework.hingeRow (w s) (w (s + 1)) ρ₀ := by
      intro s hs
      rw [Finset.mem_range] at hs
      exact BodyHingeFramework.wstep_hingeRow_off
        (hne s (m + 2) (by omega) (by omega) (by omega))
        (hne s (m + 1) (by omega) (by omega) (by omega))
        (hne (s + 1) (m + 2) (by omega) (by omega) (by omega))
        (hne (s + 1) (m + 1) (by omega) (by omega) (by omega)) ρ₀
    rw [Finset.sum_congr rfl hoff]
    -- the form at `w_m w_{m+2}` becomes the form at the edge `w_m w_{m+1}` plus the form at
    -- `w_{m+1} w_{m+3}` (`wstep_hingeRow_frontier`).
    rw [BodyHingeFramework.wstep_hingeRow_frontier
      (hne m (m + 2) (by omega) (by omega) (by omega))
      (hne m (m + 1) (by omega) (by omega) (by omega)) ρ₀]
    -- regroup: `(∑_{s<m} + frontier-advance) = (∑_{s<m+1}) + new-frontier`.
    rw [Finset.sum_range_succ]
    abel

/-- **The form at the new edge, from the moved form and the rows** (a step of
`lem:case-III-chain-eq666`): with `w` and `m` as in `wstep_foldl_hingeRow_telescope`, if a subspace
`S` contains the image of `hingeRow (w 0) (w 2) ρ₀` under the moves (`hW`) and the forms
`hingeRow (w s) (w (s+1)) ρ₀` for `s < m` (`hsurv`), then it contains `hingeRow (w m) (w (m+2)) ρ₀`,
their difference. `chainData_freshEdge_slot_mem` (`CaseIII/Relabel/ChainColumn.lean`) applies it
with `S` the span of the rows of `G − v_i` with the renamed normals, `hW` from
`shiftBodyListAsc_foldl_mem_span_rigidityRows` and `hsurv` from `freshEdge_surviving_row_mem`. -/
theorem BodyHingeFramework.wstep_foldl_freshEdge_slot_mem [DecidableEq α]
    (w : ℕ → α) (m : ℕ) (hinj : Set.InjOn w (Set.Iic (m + 2)))
    (ρ₀ : Module.Dual K (ScrewSpace K k))
    {S : Submodule K (Module.Dual K (α → ScrewSpace K k))}
    (hW : ((List.ofFn fun s : Fin m => (w ((s : ℕ) + 1), w ((s : ℕ) + 2), w ((s : ℕ) + 3))).foldl
        (fun T b => (BodyHingeFramework.wstep (k := k) b.1 b.2.1 b.2.2).comp T) LinearMap.id)
      (BodyHingeFramework.hingeRow (w 0) (w 2) ρ₀) ∈ S)
    (hsurv : ∀ s ∈ Finset.range m, BodyHingeFramework.hingeRow (w s) (w (s + 1)) ρ₀ ∈ S) :
    BodyHingeFramework.hingeRow (w m) (w (m + 2)) ρ₀ ∈ S := by
  -- by the closed form, `hW` says that the sum of the forms at the edges plus the form at the new
  -- edge lies in `S`.
  rw [BodyHingeFramework.wstep_foldl_hingeRow_telescope w m hinj ρ₀] at hW
  -- the `m` forms at the edges sum to a member of `S`.
  have hsum : (∑ s ∈ Finset.range m, BodyHingeFramework.hingeRow (w s) (w (s + 1)) ρ₀) ∈ S :=
    Submodule.sum_mem _ hsurv
  -- subtract.
  have := Submodule.sub_mem _ hW hsum
  rwa [add_sub_cancel_left] at this

end CombinatorialRigidity.Molecular
