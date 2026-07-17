/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.AlgebraicInduction.CaseIII.Relabel.Chain

/-!
# The algebraic induction — Case III relabel: the M₃ arm closer + the `i = 3` de-risks + telescope

Phase 22 (molecular-conjecture program). Third file of the `CaseIII/Relabel/` subdirectory (the
Phase-23c split of `CaseIII/Relabel.lean`, `notes/Phase23c.md`). The M₃ arm closer
`case_III_arm_realization_M3` (W9c, the third `d = 3` candidate arm), the `i = 3` fresh-edge
de-risk family, the `wstep` telescope (`wstep_foldl_hingeRow_telescope` + fresh-edge slot
membership), and the panel-correspondence / candidate-support-perp bricks. Built on `Relabel/Chain`;
consumed by the chain-column machinery in `Relabel/ChainColumn`.

See `ROADMAP.md` §22 and the `sec:molecular-algebraic-induction-caseIII` dep-graph in
`blueprint/src/chapter/algebraic-induction/case-iii.tex`.
-/

namespace CombinatorialRigidity.Molecular

variable {k : ℕ}

open scoped Graph

variable {α β : Type*}

variable {K : Type*} [Field K]

/-- **W9c — the `M₃` arm closer: the third candidate (the line `L'' ⊂ Π(c)`) realizes the `d = 3`
framework at full rank** (`lem:case-II-realization` / `lem:case-III`, the third of the three
`hcand`-discharge arms; Katoh–Tanigawa 2011 §6.4.1, eqs.~(6.31)–(6.44), the `M₃ = (r̂; r(L''))`
arm, design §1.52(d), Phase 22h). The `M₃` arm carries the candidate line `L'' ⊂ Π(c)` at the
*third* body `c` (the neighbour of `a` across the degree-2 edge `e_c = ac`), introduced by the
isomorphism `ρ : (G, p₃) ≅ (G_v^{ab}, q)` of KT eq.~(6.31) that relabels `a ↔ v`. The key
structural fact (KT eqs.~(6.35)–(6.41)) is that `R(G, p₃)`'s relevant submatrix *is* the v-split
matrix read through the relabel: the bottom block of (6.41) is the same `R(G_v^{ab} ∖ (ab)i^*, q)`
as the `M₁`/`M₂` arms, with the same `λ`s and the same redundant index `i^*`. So the `M₃` arm
consumes the **same** candidate/bottom data `ρ`/`w` as `M₁`/`M₂` (one W6b invocation feeds all
three; KT p. 686), transported *pointwise* across the vertex relabel `(a v)` by the W9a/W9b
leaves — there is no a-split rank certification, hence no second GAP-6.

This is a pure instantiation of `case_III_arm_realization` (W7) at the roles
`(v, a, b, e_a, e_b, n') := (a, c, v, e_c, e_a, n''')`, with the `Gv`-slot `G.removeVertex a` (the
relabeled split minus its short-circuit edge — a subgraph of `G`), the relabeled seed
`qρ = q ∘ (a v)` (inline `fun p => q (Equiv.swap a v p.1, p.2)`), the candidate functional
`ρ̃ := -ρ` (KT eq.~(6.44): `Σ λ_{(ac)j} r_j(q(ac)) = -r̂`; the negation is a Lean-orientation
artifact, `hingeRow c v (-ρ) = hingeRow v c ρ`), and the bottom family
`w̃ := (funLeft (a v)).dualMap ∘ w`. The heavy transports are delegated: the candidate
`hρe₀`-slot to **G4d-i** (`ρ ⊥ C(q(ac))`), the candidate `hρGv`-slot to **W9a** (the
short-circuit-free span transport into the `G − a`-row span), and the bottom `hwmem`-slot to
**W9b** (the per-member tag transport). Graph-free transport over the carrier; the §38 trap lives
inside W7. -/
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
  -- The relabeled seed reads `q` at the swapped body: `qρ(c,·) = q(c,·)`, `qρ(v,·) = q(a,·)`.
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
  -- The candidate functional's annihilation `ρ ⊥ C(q(ac))` via G4d-i (the `a`-column of
  -- `hingeRow a b ρ` is `ρ`, which lands in `Fv.hingeRowBlock e_c`, i.e. `ρ ⊥ Fv.supportExtensor
  -- e_c = ±C(q(ac))`).
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
  -- The genuine `e_b`-row of the `M₃` framework `Fva = ofNormals (G − a) ends₃ qρ`.
  set Fva := (PanelHingeFramework.ofNormals (G.removeVertex a) ends₃ qρ).toBodyHinge with hFva
  -- `c, v ∈ V(G − a)` and `a ∉ V(G − a)`.
  have ha_mem : a ∈ V(G) := hG_ea.right_mem
  have hc_mem : c ∈ V(G) := hG_ec.right_mem
  have hv_mem : v ∈ V(G) := hG_ea.left_mem
  have hcard_Gva : V(G.removeVertex a).ncard = V(G).ncard - 1 := by
    rw [Graph.vertexSet_removeVertex, Set.ncard_diff_singleton_of_mem ha_mem]
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
    -- `hingeRow c v (-ρ) = hingeRow v c ρ ∈ span Fva.rigidityRows`. From W9a at
    -- `φ := hingeRow a b ρ` (image `hingeRow v b ρ`, `a`-column `ρ`), giving
    -- `hingeRow v b ρ - hingeRow v c ρ ∈ span`;
    -- `hingeRow v b ρ` is the genuine `e_b`-row of `Fva` (via `hρe₀`), so `Submodule.sub_mem`.
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
    -- `hingeRow v b ρ` is the genuine `e_b`-row of `Fva`.
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
    -- bridge the `∘` and the `qρ(c,·)/qρ(v,·) = q(c,·)/q(a,·)` seed identities, then W9b.
    simp only [Function.comp_apply, hqρc, hqρv]
    exact PanelHingeFramework.case_III_bottom_relabel hva hab hvb hca hcv hG_ea hG_eb hG_ec hcla
      (fun e x y hlink => (Graph.removeVertex_isLink.mp hlink).1)
      (fun e x y hlink => ⟨(Graph.removeVertex_isLink.mp hlink).2.1,
        (Graph.removeVertex_isLink.mp hlink).2.2⟩)
      (fun e x y hlink => hrecGv e x y hlink) hends₃_eb hends₃_off (hwmem j)

/-! ### The `i = 3` 2-residue de-risk for the `hρGv` fresh-edge telescope (CHAIN-2c-ii-arm)

These lemmas carry out, *for real*, the `i = 3` 2-residue case of the `hρGv` extraction (the de-risk
gate of `notes/Phase23-design.md` §(o‴)(I.7.10)'s RESIDUAL). `i = 3` is the first honest 2-residue
case — the `v₁ v₂ v₃` cycle (`i = 2`, the d=3 `M₃` engine) is the 1-residue involution that *masks*
the multi-step telescope.

The chain vertices are `v0 … v4` (`vⱼ = vtx j`); the ascending moved-body list for candidate `i = 3`
is `[(v1,v2,v3), (v2,v3,v4)]`; the base redundancy is `φ = hingeRow v0 v2 ρ₀` (KT eq. (6.52), the
`v₀v₂`-block redundancy of the `v₁`-base split). The KT-source re-derivation
(§(o‴)(I.7.10), option (b)) settled that the engine slot
`case_III_arm_realization.hρGv = hingeRow vᵢ₊₁ vᵢ₋₁ ρ` is **KT-faithful** (the `Mᵢ` fresh-edge row,
KT eqs. 6.56/6.64), and that the genuinely-missing piece is **KT eq. (6.66)** — the iterated
degree-2 `±r` telescope carrying the W9a fold's `(v₀v₁)`-row form to the fresh-edge slot row. These
lemmas confirm that telescope **converges** at `i = 3`:

* **`i3_wstep_foldl_base_redundancy_deRisk`** — the landed seed-advancing W9a `wstep` foldl
  (`shiftBodyListAsc_foldl_mem_span_rigidityRows`, which gives `W φ ∈ span (G − v₃) rows`) sends the
  base redundancy to `W φ = hingeRow v0 v1 ρ₀ + hingeRow v1 v2 ρ₀ + hingeRow v2 v4 ρ₀`.
* **`i3_freshEdge_slot_mem_deRisk`** — the re-targeted de-risk: from `W φ ∈ span` (landed) and the
  two **genuine surviving** chain-edge rows `hingeRow v0 v1 ρ₀` (edge `v₀v₁`, both endpoints survive
  `G − v₃`) and `hingeRow v1 v2 ρ₀` (edge `v₁v₂`, ditto) in `span`, the fresh-edge slot row
  `hingeRow v2 v4 ρ₀` is `∈ span` by `sub_mem` (`W φ` minus the two surviving rows). This is exactly
  the KT-(6.66) peel-off realized as membership algebra: the slot row IS `W φ − (surviving rows)`,
  so the telescope route to `case_III_arm_realization.hρGv` **closes at `i = 3`**. Confirming this
  before pinning the general arm signature is the H.11-discipline gate (option (b) buildable, no
  engine/motive change).

**On the prior `i3_residue_collapse_deRisk` (`D φ = R φ − W φ` at link `v₁—v₄`).** That lemma
records the relabel-only foldl minus `W φ`; its collapse to `hingeRow v1 v4 (−ρ₀)` is correct but a
**red herring** for the slot (§(o‴)(I.7.10)): `D φ` was never the slot row. The slot is via `W φ`
minus the surviving genuine rows (`i3_freshEdge_slot_mem_deRisk`), not via `D φ`. It is kept as the
correct fold-output record. -/
theorem _root_.Graph.ChainData.i3_wstep_foldl_base_redundancy_deRisk
    [DecidableEq α] {v0 v1 v2 v3 v4 : α}
    (h01 : v0 ≠ v1) (h02 : v0 ≠ v2) (h03 : v0 ≠ v3)
    (h12 : v1 ≠ v2) (h13 : v1 ≠ v3)
    (ρ₀ : Module.Dual K (ScrewSpace K k)) :
    ([(v1, v2, v3), (v2, v3, v4)].foldl
        (fun T b => (BodyHingeFramework.wstep (k := k) b.1 b.2.1 b.2.2).comp T) LinearMap.id)
      (BodyHingeFramework.hingeRow v0 v2 ρ₀)
      = BodyHingeFramework.hingeRow v0 v1 ρ₀ + BodyHingeFramework.hingeRow v1 v2 ρ₀
        + BodyHingeFramework.hingeRow v2 v4 ρ₀ := by
  simp only [List.foldl_cons, List.foldl_nil, LinearMap.comp_apply, LinearMap.id_coe, id_eq,
    BodyHingeFramework.wstep_apply, BodyHingeFramework.hingeRow_funLeft_dualMap]
  ext S
  have e1 : (Equiv.swap v2 v1) v0 = v0 := Equiv.swap_apply_of_ne_of_ne h02 h01
  have e2 : (Equiv.swap v2 v1) v2 = v1 := Equiv.swap_apply_left _ _
  have e3 : (Equiv.swap v3 v2) v0 = v0 := Equiv.swap_apply_of_ne_of_ne h03 h02
  have e4 : (Equiv.swap v3 v2) v1 = v1 := Equiv.swap_apply_of_ne_of_ne h13 h12
  have e5 : (Equiv.swap v3 v2) v3 = v2 := Equiv.swap_apply_left _ _
  simp only [LinearMap.sub_apply, LinearMap.funLeft_apply, LinearMap.dualMap_apply,
    LinearMap.comp_apply, BodyHingeFramework.hingeRow_apply, LinearMap.single_apply,
    LinearMap.add_apply, e1, e2, e3, e4, e5, Pi.single_eq_same,
    Pi.single_eq_of_ne h02, Pi.single_eq_of_ne h03,
    Pi.single_eq_of_ne h13, map_sub, map_zero]
  ring

/-- The `i = 3` residue collapse: `D φ = R φ − W φ` (relabel-only foldl minus the `wstep` foldl) is
the single row `hingeRow v1 v4 (−ρ₀)` at the link `v₁—v₄`. This is a correct fold-output record but
a **red herring** for the slot (§(o‴)(I.7.10)): the slot is reached via `W φ` minus the surviving
genuine rows (`i3_freshEdge_slot_mem_deRisk`), not via `D φ`. -/
theorem _root_.Graph.ChainData.i3_residue_collapse_deRisk
    (v0 v1 v2 v4 : α) (ρ₀ : Module.Dual K (ScrewSpace K k)) :
    -- `R φ − W φ` (relabel-only foldl minus the `wstep` foldl):
    (BodyHingeFramework.hingeRow v0 v1 ρ₀ : Module.Dual K (α → ScrewSpace K k))
      - (BodyHingeFramework.hingeRow v0 v1 ρ₀ + BodyHingeFramework.hingeRow v1 v2 ρ₀
          + BodyHingeFramework.hingeRow v2 v4 ρ₀)
      -- collapses to the single non-edge row `D φ` at the link `v₁—v₄`:
      = BodyHingeFramework.hingeRow v1 v4 (-ρ₀) := by
  ext S
  simp only [LinearMap.sub_apply, LinearMap.add_apply, BodyHingeFramework.hingeRow_apply,
    LinearMap.neg_apply, map_sub]
  ring

/-- **The re-targeted `i = 3` de-risk gate — the fresh-edge slot row reaches `span` via the
KT-(6.66) telescope** (CHAIN-2c-ii-arm, `notes/Phase23-design.md` §(o‴)(I.7.10) RESIDUAL). This is
the gate the design pins as the check to do *before* committing the general arm signature: confirm
that the engine slot row `hingeRow v2 v4 ρ₀` (candidate `i = 3`'s fresh-edge pair `vᵢ₋₁—vᵢ₊₁ =
v₂—v₄`) is reachable in `span (G − v₃).rigidityRows` from the landed W9a fold output.

The membership algebra is the KT-(6.66) peel-off made concrete. The landed `wstep` foldl gives
`W φ = hingeRow v0 v1 ρ₀ + hingeRow v1 v2 ρ₀ + hingeRow v2 v4 ρ₀ ∈ span`
(`i3_wstep_foldl_base_redundancy_deRisk` + `shiftBodyListAsc_foldl_mem_span_rigidityRows`). The two
leading summands are **genuine surviving chain-edge rows** of `G − v₃`: `hingeRow v0 v1 ρ₀` is the
`v₀v₁ = edge 0` row and `hingeRow v1 v2 ρ₀` the `v₁v₂ = edge 1` row, both with neither endpoint
equal to the removed `v₃`, so both `∈ span`. Subtracting them from `W φ` (`Submodule.sub_mem`)
leaves the fresh-edge slot row `hingeRow v2 v4 ρ₀ ∈ span` — exactly the engine `hρGv` slot. So the
telescope route **converges at `i = 3`** (option (b) buildable; the general arm is the `i − 1`-step
generalization of this peel-off, the d=3 `M₃` `case hρGv` being the `i = 2` 1-step special case).

Stated abstractly over the span carrier `S` (the membership hypotheses are what the arm closer
supplies from the genuine surviving chain-edge rows; this lemma is the algebraic skeleton, decoupled
from the graph-level `rigidityRows` plumbing the arm wires in). -/
theorem _root_.Graph.ChainData.i3_freshEdge_slot_mem_deRisk
    {v0 v1 v2 v4 : α} {ρ₀ : Module.Dual K (ScrewSpace K k)}
    {S : Submodule K (Module.Dual K (α → ScrewSpace K k))}
    -- the landed W9a fold output `W φ ∈ span (G − v₃) rows`:
    (hW : BodyHingeFramework.hingeRow v0 v1 ρ₀ + BodyHingeFramework.hingeRow v1 v2 ρ₀
          + BodyHingeFramework.hingeRow v2 v4 ρ₀ ∈ S)
    -- the two genuine surviving chain-edge rows:
    (h01 : BodyHingeFramework.hingeRow v0 v1 ρ₀ ∈ S)
    (h12 : BodyHingeFramework.hingeRow v1 v2 ρ₀ ∈ S) :
    -- the fresh-edge slot row `hingeRow v2 v4 ρ₀ = hingeRow vᵢ₋₁ vᵢ₊₁ ρ₀` reaches `span`:
    BodyHingeFramework.hingeRow v2 v4 ρ₀ ∈ S := by
  have h := Submodule.sub_mem _ (Submodule.sub_mem _ hW h01) h12
  -- `(W φ − hingeRow v0 v1 ρ₀) − hingeRow v1 v2 ρ₀ = hingeRow v2 v4 ρ₀`.
  have heq : BodyHingeFramework.hingeRow v0 v1 ρ₀ + BodyHingeFramework.hingeRow v1 v2 ρ₀
        + BodyHingeFramework.hingeRow v2 v4 ρ₀ - BodyHingeFramework.hingeRow v0 v1 ρ₀
        - BodyHingeFramework.hingeRow v1 v2 ρ₀
      = BodyHingeFramework.hingeRow v2 v4 ρ₀ := by abel
  rwa [heq] at h

/-- **The concrete `i = 3` P2 de-risk gate — the two surviving chain-edge rows reach the concrete
`span (G − v₃).rigidityRows`, each via its own per-edge perp obligation** (CHAIN-2c-ii-arm, P2 of
the ARM-WIRING DESIGN-PASS, `notes/Phase23-design.md` §(o‴)(I.8.3); Phase 23b). The H.11-discipline
gate the design pins as "do P2 at `i = 3` FOR REAL at the *concrete* `span (G − v₃)` level (the
`i3_freshEdge_slot_mem_deRisk` gate did it only abstractly over `S`)": confirm that the two genuine
surviving chain-edge rows `hingeRow v₀ v₁ ρ₀` (`edge 0`) and `hingeRow v₁ v₂ ρ₀` (`edge 1`) — the
`hsurv` hypotheses `wstep_foldl_freshEdge_slot_mem` defers — actually reach the concrete candidate
framework's rigidity-row span at candidate `i = 3` (the `removeVertex (vtx 3)` framework).

**What this gate establishes (the `link` half — clean).** Each surviving chain edge `edge s`
(`s ∈ {0, 1}`) links `vtx s` to `vtx (s+1)` in `G` (`cd.link`); both endpoints have index `< 3`, so
neither equals the removed `vtx 3` (`cd.vtx_inj`), and the edge survives `removeVertex (vtx 3)`
(`removeVertex_isLink`). So the genuine-link membership certificate `hingeRow_mem_rigidityRows`
applies once the per-edge block membership `ρ₀ ∈ hingeRowBlock (edge s)` is supplied.

**What this gate ISOLATES as the genuinely-new P2 obligation (the `perp` half — NOT automatic).**
The block membership `ρ₀ ∈ Fva.hingeRowBlock (edge s)` is, by `mem_hingeRowBlock_iff`, exactly
`ρ₀ (Fva.supportExtensor (edge s)) = 0` — i.e. `ρ₀ ⊥` the candidate framework's panel at `edge s`.
This is the per-edge **perp obligation** `hperp0`/`hperp1`, taken here as hypotheses. It is **not
automatic**: the base redundancy `ρ₀` (the W6b-gate functional, `chainData_split_w6b_gates`) is
built to annihilate only the base spliced panel `C(q(v₀v₂))` (its `hρe₀` gate), **not** the
intermediate chain-edge panels `C(qρ(vₛvₛ₊₁))`. That `ρ₀` also annihilates each surviving panel is
precisely KT eq.~(6.62)/(6.66)'s transported-redundancy assertion (the degree-2 `±r` carry,
`candidateRow_ac_eq_neg`), which is **unbuilt in Lean** — the closed-form telescope
(`wstep_foldl_hingeRow_telescope`) gives `W φ = (∑ surviving) + slot` as *linear maps* but does NOT
say each `∑`-summand is a span member. So this gate confirms the de-risk verdict: the `link` half
goes through concretely; the **perp half is the genuinely-new math** the arm wiring must still
discharge (route (a): the degree-2 chain carry off `candidateRow_ac_eq_neg`; route (b): off the
landed `chainData_bottom_relabel` genuine-row branch). Mirrors the H.11 gate — the de-risk
*localizes* the obstruction rather than papering over it. -/
theorem _root_.Graph.ChainData.i3_freshEdge_surviving_rows_mem_deRisk
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (h4 : 4 ≤ cd.d)
    {ends : β → α × α} {qρ : α × Fin (k + 2) → K} (ρ₀ : Module.Dual K (ScrewSpace K k))
    -- the per-edge perp obligations (the genuinely-new P2 content the arm must still discharge):
    (hperp0 : ρ₀ ((PanelHingeFramework.ofNormals (G.removeVertex
        (cd.vtx ⟨3, by omega⟩)) ends qρ).toBodyHinge.supportExtensor (cd.edge ⟨0, by omega⟩)) = 0)
    (hperp1 : ρ₀ ((PanelHingeFramework.ofNormals (G.removeVertex
        (cd.vtx ⟨3, by omega⟩)) ends qρ).toBodyHinge.supportExtensor (cd.edge ⟨1, by omega⟩)) = 0) :
    BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨1, by omega⟩) ρ₀ ∈
        Submodule.span K (PanelHingeFramework.ofNormals (G.removeVertex
          (cd.vtx ⟨3, by omega⟩)) ends qρ).toBodyHinge.rigidityRows ∧
      BodyHingeFramework.hingeRow (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ₀ ∈
        Submodule.span K (PanelHingeFramework.ofNormals (G.removeVertex
          (cd.vtx ⟨3, by omega⟩)) ends qρ).toBodyHinge.rigidityRows := by
  classical
  set Fva := (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨3, by omega⟩))
    ends qρ).toBodyHinge with hFva
  -- A reusable membership builder: a surviving chain edge `edge s` (`s + 1 < 3`) gives a span
  -- member once `ρ₀ ⊥ Fva.supportExtensor (edge s)` (`hp`); the `link` half is concrete.
  have hrow : ∀ s : ℕ, (hs : s + 1 < 3) → ρ₀ (Fva.supportExtensor (cd.edge ⟨s, by omega⟩)) = 0 →
      BodyHingeFramework.hingeRow (cd.vtx ⟨s, by omega⟩) (cd.vtx ⟨s + 1, by omega⟩) ρ₀ ∈
        Submodule.span K Fva.rigidityRows := by
    intro s hs hp
    apply Submodule.subset_span
    -- the chain edge `edge s` links `vtx s — vtx (s+1)` in `G` (the `link` field at `⟨s,_⟩`).
    have hlinkG : G.IsLink (cd.edge ⟨s, by omega⟩) (cd.vtx ⟨s, by omega⟩)
        (cd.vtx ⟨s + 1, by omega⟩) := by
      have h := cd.link ⟨s, by omega⟩
      simpa only [Fin.castSucc_mk, Fin.succ_mk] using h
    -- both endpoints survive `removeVertex (vtx 3)` (`s, s+1 < 3`, distinct from `3` by `vtx_inj`).
    have hs3 : cd.vtx ⟨s, by omega⟩ ≠ cd.vtx ⟨3, by omega⟩ := cd.vtx_ne _ _ (by omega)
    have hs13 : cd.vtx ⟨s + 1, by omega⟩ ≠ cd.vtx ⟨3, by omega⟩ := cd.vtx_ne _ _ (by omega)
    have hlinkGv : (G.removeVertex (cd.vtx ⟨3, by omega⟩)).IsLink (cd.edge ⟨s, by omega⟩)
        (cd.vtx ⟨s, by omega⟩) (cd.vtx ⟨s + 1, by omega⟩) :=
      Graph.removeVertex_isLink.mpr ⟨hlinkG, hs3, hs13⟩
    -- the genuine-link membership certificate: link in `Fva.graph` + `ρ₀ ∈ hingeRowBlock (edge s)`.
    refine BodyHingeFramework.hingeRow_mem_rigidityRows Fva (e := cd.edge ⟨s, by omega⟩) ?_ ?_
    · rw [hFva, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]
      exact hlinkGv
    · exact (Fva.mem_hingeRowBlock_iff _ ρ₀).2 hp
  exact ⟨hrow 0 (by omega) hperp0, hrow 1 (by omega) hperp1⟩

/-- **The `i = 3` all-`i`-lift ROUTE-FORK de-risk gate — the interior `v₁`-column of the W9a fold
output lands ONLY in the *sup* of its two incident chain panels, NOT a single block**
(CHAIN-2c-ii-arm, the A-3 all-`i` lift route fork; `notes/Phase23-design.md` §(o‴)(I.8.7), the
"SMALLEST NEXT COMMIT = the i=3 DE-RISK"; Phase 23b). The de-risk that decides the A-3 all-`i` lift
fork (Route W vs Route G4d-i-PROJECTED) **before** any leaf signature is pinned — the row-321
failure mode was a confident pin ahead of the de-risk.

**The fork.** The single-vertex A-3 composition `freshEdge_surviving_row_mem_of_witness` (landed)
discharges each interior perp `ρ₀ ⊥ Fva.supportExtensor (edge s)` from the eq.~(6.52) `λ`-witness
(`hcol`/`hrest`) AS HYPS; the all-`i` lift must SUPPLY that witness at each interior `s < i − 1`,
and the W6b producer supplies it only at the base `e₀`. **Route G4d-i-PROJECTED** (recommended in
the recon) hoped to derive the interior perp the way the d=3 `M₃` engine does — projecting a span
member's interior column into a *single* incident block via the one-edge G4d-i form
(`acolumn_mem_hingeRowBlock_of_span_rigidityRows`, `case_III_arm_realization_M3`'s `hρ_ac`) — so
that the witness `hcol`/`hrest` is not needed. **Route W** (not recommended) builds a genuinely-new
per-vertex redundancy-witness producer.

**What this gate establishes — the de-risk VERDICT, ground-truth in Lean (not paper reasoning).**
At candidate `i = 3` the candidate framework removes `vtx 3`, so the interior vertex `a = vtx 1` is
**genuinely degree-2** in `Fva = ofNormals (G − vtx 3) ends qρ`: BOTH incident chain edges
`edge 0 = v₀v₁` and `edge 1 = v₁v₂` survive (endpoints `v₀, v₁, v₂` all `≠ v₃`, `vtx_inj`). The
strongest column projection available from the fold output `hW : W φ ∈ span Fva.rigidityRows` is
therefore the **two-edge sup** `acolumn_mem_hingeRowBlock_sup_of_span_rigidityRows`: the `v₁`-column
`W φ ∘ single (vtx 1)` lands in `block (edge 0) ⊔ block (edge 1)`, **NOT** in either block alone.
The d=3 `M₃` mechanism does not project here: there the interior vertex is degree-**one** in the
candidate split (the second incident edge links the *removed* vertex, so it dies in `removeVertex`),
which is exactly what forces the one-edge form's single-block landing. At an honest interior chain
vertex (`d ≥ 4`, `i = 3`) both edges survive, the sup is the ceiling, and `ρ₀ ⊥ C(edge 0)` (a
*single*-block perp) is **not separable** from the sup without extra structure — the "vacuous `=⊤`"
obstruction §(o‴)(I.8.3.v-REFUTED) named, now Lean-confirmed.

**Verdict: the de-risk FAILS — Route G4d-i-PROJECTED's hoped single-block projection does not
exist; Route W (the per-vertex `λ`-witness, via `freshEdge_surviving_row_mem_of_witness` + A-2) is
FORCED.** This is a FLAG-AND-STOP for user adjudication (the genuinely-new-math fork): the all-`i`
lift needs the per-vertex eq.~(6.52) witness supplied at each interior vertex (KT eq.~(6.66)'s
per-vertex redundancy decomposition), which has no landed producer. The single-vertex consumers
`freshEdge_surviving_row_mem_of_witness` + the A-2 carrier `candidate_perp_two_incident_*` STAND
(they are Route W's building blocks). No motive/IH/contract change under either route. -/
theorem _root_.Graph.ChainData.i3_freshEdge_interior_acolumn_sup_deRisk [DecidableEq α]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (h4 : 4 ≤ cd.d)
    {ends : β → α × α} {qρ : α × Fin (k + 2) → K}
    {φ : Module.Dual K (α → ScrewSpace K k)}
    -- the landed W9a fold output `W φ ∈ span (G − v₃) rows`:
    (hW : φ ∈ Submodule.span K (PanelHingeFramework.ofNormals (G.removeVertex
        (cd.vtx ⟨3, by omega⟩)) ends qρ).toBodyHinge.rigidityRows) :
    -- the strongest projection: the interior `v₁`-column lands in the *sup* of the two incident
    -- chain panels — NOT a single block (the route-fork de-risk verdict).
    φ.comp (LinearMap.single K (fun _ : α => ScrewSpace K k) (cd.vtx ⟨1, by omega⟩)) ∈
      ((PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨3, by omega⟩)) ends qρ).toBodyHinge
          |>.hingeRowBlock (cd.edge ⟨0, by omega⟩))
      ⊔ ((PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨3, by omega⟩)) ends qρ).toBodyHinge
          |>.hingeRowBlock (cd.edge ⟨1, by omega⟩)) := by
  classical
  set Fva := (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨3, by omega⟩))
    ends qρ).toBodyHinge with hFva
  -- The interior vertex `a = vtx 1` differs from its two surviving neighbours `vtx 0`/`vtx 2`.
  have h10 : cd.vtx ⟨1, by omega⟩ ≠ cd.vtx ⟨0, by omega⟩ := cd.vtx_ne _ _ (by omega)
  have h12 : cd.vtx ⟨1, by omega⟩ ≠ cd.vtx ⟨2, by omega⟩ := cd.vtx_ne _ _ (by omega)
  -- The two incident chain edges survive `removeVertex (vtx 3)`, oriented FROM interior `vtx 1`.
  -- `edge 0` links `vtx 0 — vtx 1` in `G` (`link` at `⟨0,_⟩`); take `.symm` to orient from `vtx 1`.
  have hG0 : G.IsLink (cd.edge ⟨0, by omega⟩) (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨1, by omega⟩) := by
    have h := cd.link ⟨0, by omega⟩; simpa only [Fin.castSucc_mk, Fin.succ_mk] using h
  have hG1 : G.IsLink (cd.edge ⟨1, by omega⟩) (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨2, by omega⟩) := by
    have h := cd.link ⟨1, by omega⟩; simpa only [Fin.castSucc_mk, Fin.succ_mk] using h
  have hne03 : cd.vtx ⟨0, by omega⟩ ≠ cd.vtx ⟨3, by omega⟩ := cd.vtx_ne _ _ (by omega)
  have hne13 : cd.vtx ⟨1, by omega⟩ ≠ cd.vtx ⟨3, by omega⟩ := cd.vtx_ne _ _ (by omega)
  have hne23 : cd.vtx ⟨2, by omega⟩ ≠ cd.vtx ⟨3, by omega⟩ := cd.vtx_ne _ _ (by omega)
  have hlink_ec : Fva.graph.IsLink (cd.edge ⟨0, by omega⟩) (cd.vtx ⟨1, by omega⟩)
      (cd.vtx ⟨0, by omega⟩) := by
    rw [hFva, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]
    exact Graph.removeVertex_isLink.mpr ⟨hG0.symm, hne13, hne03⟩
  have hlink_ed : Fva.graph.IsLink (cd.edge ⟨1, by omega⟩) (cd.vtx ⟨1, by omega⟩)
      (cd.vtx ⟨2, by omega⟩) := by
    rw [hFva, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]
    exact Graph.removeVertex_isLink.mpr ⟨hG1, hne13, hne23⟩
  -- The interior degree-2 closure at `vtx 1` (`deg_two ⟨1,_⟩`): every `G`-link of `vtx 1` is
  -- `edge 0` or `edge 1`; an `Fva.graph`-link is a `G`-link, so the closure transports.
  have hdeg2 : ∀ f x, Fva.graph.IsLink f (cd.vtx ⟨1, by omega⟩) x →
      f = cd.edge ⟨0, by omega⟩ ∨ f = cd.edge ⟨1, by omega⟩ := by
    intro f x hlink
    rw [hFva, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph] at hlink
    have hGlink := (Graph.removeVertex_isLink.mp hlink).1
    -- `deg_two ⟨1,_⟩` at `(vtx ⟨1,_⟩).castSucc = vtx 1` gives `f = edge ⟨0,_⟩ ∨ f = edge ⟨1,_⟩`.
    have hd := cd.deg_two ⟨1, by omega⟩ (by simp) f x
    simp only [Fin.castSucc_mk] at hd
    exact hd hGlink
  have hdeg2r : ∀ f x, Fva.graph.IsLink f x (cd.vtx ⟨1, by omega⟩) →
      f = cd.edge ⟨0, by omega⟩ ∨ f = cd.edge ⟨1, by omega⟩ :=
    fun f x hlink => hdeg2 f x hlink.symm
  exact BodyHingeFramework.acolumn_mem_hingeRowBlock_sup_of_span_rigidityRows
    (Fab := Fva) (Fv := Fva) h10 h12 hlink_ec hlink_ed rfl rfl hdeg2 hdeg2r hW

/-- **The general-`i` interior degree-2 column-sup projection** (CHAIN-2c-ii-arm, the LEAF-4
interior-`hρe₀` regrouping component; `notes/Phase23-design.md` §I.8.24(4.13); Katoh–Tanigawa 2011
§6.4.2, eq.~(6.44) iterated). The candidate-`i`-general lift of the d=3 de-risk gate
`i3_freshEdge_interior_acolumn_sup_deRisk` (its `i = 3`, `s = 0`, interior vertex `vtx 1` instance):
at a candidate `i : Fin (cd.d + 1)` and a *surviving* interior chain vertex `vtx (s+1)` (with
`s + 2 < (i : ℕ)`, so both incident chain edges `edge s = vₛvₛ₊₁` and `edge (s+1) = vₛ₊₁vₛ₊₂` have
all of `vtx s, vtx (s+1), vtx (s+2)` distinct from `vtx i` and survive `removeVertex (vtx i)`), the
interior vertex is **genuinely degree-2** in `Fva = ofNormals (G − vtx i) ends qρ`, so the strongest
projection of a span member `φ ∈ span Fva.rigidityRows` at the `vtx (s+1)`-column is the **two-edge
sup** `block (edge s) ⊔ block (edge (s+1))`, not a single block (the route-fork verdict at the d=3
gate). This is the column-projection brick the interior-`hρe₀` leaf's eq.~(6.52) regrouping at the
degree-2 vertex `vᵢ` threads through, generalizing the hardcoded `⟨0/1/2/3, _⟩` indices of the d=3
gate to general `i` and surviving-edge index `s`. Direct application of the framework-level
primitive `acolumn_mem_hingeRowBlock_sup_of_span_rigidityRows`, with the degree-2 closure supplied
by the chain helper `shiftBody_deg_two`. The strict `s + 2 < (i : ℕ)` boundary is load-bearing: at
`i = s + 2` the successor neighbour `vtx (s+2) = vtx i` is *removed*, so `edge (s+1)` dies and
`vtx (s+1)` becomes degree-ONE (the d=3-base / `M₃` single-block situation, handled by the one-edge
`acolumn_mem_hingeRowBlock_of_span_rigidityRows`); the two-edge sup is the right form exactly when
both neighbours survive. Self-contained over the chain data, **zero blast radius** (no live
caller); consumed by the all-`i` interior carry. -/
theorem _root_.Graph.ChainData.freshEdge_interior_acolumn_sup [DecidableEq α]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (i : Fin (cd.d + 1)) (s : ℕ)
    (hsi : s + 2 < (i : ℕ))
    {ends : β → α × α} {qρ : α × Fin (k + 2) → K}
    {φ : Module.Dual K (α → ScrewSpace K k)}
    -- a span member of the candidate-`i` split's rigidity rows (the eq.-(6.52) redundancy lives
    -- here):
    (hφ : φ ∈ Submodule.span K (PanelHingeFramework.ofNormals (G.removeVertex
        (cd.vtx i)) ends qρ).toBodyHinge.rigidityRows) :
    -- the strongest projection: the surviving interior `vtx (s+1)`-column lands in the *sup* of the
    -- two incident chain panels — NOT a single block (the genuine degree-2 interior vertex).
    φ.comp (LinearMap.single K (fun _ : α => ScrewSpace K k)
        (cd.vtx ⟨s + 1, by have := i.isLt; omega⟩))
      ∈ ((PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i)) ends qρ).toBodyHinge
          |>.hingeRowBlock (cd.edge ⟨s, by have := i.isLt; omega⟩))
      ⊔ ((PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i)) ends qρ).toBodyHinge
          |>.hingeRowBlock (cd.edge ⟨s + 1, by have := i.isLt; omega⟩)) := by
  classical
  have hid : (i : ℕ) < cd.d + 1 := i.isLt
  set Fva := (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i)) ends qρ).toBodyHinge
    with hFva
  -- The interior vertex `a = vtx (s+1)` differs from its surviving neighbours `vtx s`, `vtx (s+2)`.
  have h_pred : cd.vtx ⟨s + 1, by omega⟩ ≠ cd.vtx ⟨s, by omega⟩ := cd.vtx_ne (by omega) (by omega)
    (by omega)
  have h_succ : cd.vtx ⟨s + 1, by omega⟩ ≠ cd.vtx ⟨s + 2, by omega⟩ := cd.vtx_ne (by omega)
    (by omega) (by omega)
  -- The two incident chain edges in `G`, oriented FROM the interior vertex `vtx (s+1)`.
  -- `edge s` links `vtx s — vtx (s+1)` (`link` at `⟨s,_⟩`); `.symm` orients from `vtx (s+1)`.
  have hGs : G.IsLink (cd.edge ⟨s, by omega⟩) (cd.vtx ⟨s, by omega⟩)
      (cd.vtx ⟨s + 1, by omega⟩) := by
    have h := cd.link ⟨s, by omega⟩; simpa only [Fin.castSucc_mk, Fin.succ_mk] using h
  have hGs1 : G.IsLink (cd.edge ⟨s + 1, by omega⟩) (cd.vtx ⟨s + 1, by omega⟩)
      (cd.vtx ⟨s + 2, by omega⟩) := by
    have h := cd.link ⟨s + 1, by omega⟩; simpa only [Fin.castSucc_mk, Fin.succ_mk] using h
  -- All three survive `removeVertex (vtx i)`: indices `s, s+1, s+2 < i`, distinct from `i`.
  have hnesi : cd.vtx ⟨s, by omega⟩ ≠ cd.vtx i := by
    have := cd.vtx_ne (m := s) (m' := (i : ℕ)) (by omega) hid (by omega)
    simpa using this
  have hnes1i : cd.vtx ⟨s + 1, by omega⟩ ≠ cd.vtx i := by
    have := cd.vtx_ne (m := s + 1) (m' := (i : ℕ)) (by omega) hid (by omega)
    simpa using this
  have hnes2i : cd.vtx ⟨s + 2, by omega⟩ ≠ cd.vtx i := by
    have := cd.vtx_ne (m := s + 2) (m' := (i : ℕ)) (by omega) hid (by omega)
    simpa using this
  -- The two incident chain edges as `Fva.graph`-links from `vtx (s+1)`.
  have hlink_ec : Fva.graph.IsLink (cd.edge ⟨s, by omega⟩) (cd.vtx ⟨s + 1, by omega⟩)
      (cd.vtx ⟨s, by omega⟩) := by
    rw [hFva, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]
    exact Graph.removeVertex_isLink.mpr ⟨hGs.symm, hnes1i, hnesi⟩
  have hlink_ed : Fva.graph.IsLink (cd.edge ⟨s + 1, by omega⟩) (cd.vtx ⟨s + 1, by omega⟩)
      (cd.vtx ⟨s + 2, by omega⟩) := by
    rw [hFva, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]
    exact Graph.removeVertex_isLink.mpr ⟨hGs1, hnes1i, hnes2i⟩
  -- The interior degree-2 closure at `vtx (s+1)` (`shiftBody_deg_two`): every `G`-link is `edge s`
  -- or `edge (s+1)`; an `Fva.graph`-link is a `G`-link, so the closure transports.
  have hdeg2 : ∀ f x, Fva.graph.IsLink f (cd.vtx ⟨s + 1, by omega⟩) x →
      f = cd.edge ⟨s, by omega⟩ ∨ f = cd.edge ⟨s + 1, by omega⟩ := by
    intro f x hlink
    rw [hFva, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph] at hlink
    have hGlink := (Graph.removeVertex_isLink.mp hlink).1
    rcases cd.shiftBody_deg_two (by omega : s + 1 < (i : ℕ)) hid f x hGlink with hf1 | hf0
    · exact Or.inr hf1
    · exact Or.inl hf0
  have hdeg2r : ∀ f x, Fva.graph.IsLink f x (cd.vtx ⟨s + 1, by omega⟩) →
      f = cd.edge ⟨s, by omega⟩ ∨ f = cd.edge ⟨s + 1, by omega⟩ :=
    fun f x hlink => hdeg2 f x hlink.symm
  exact BodyHingeFramework.acolumn_mem_hingeRowBlock_sup_of_span_rigidityRows
    (Fab := Fva) (Fv := Fva) h_pred h_succ hlink_ec hlink_ed rfl rfl hdeg2 hdeg2r hφ

/-- **The general-`i` surviving chain-edge row-membership builder — the `hsurv` summand the
`hρGv` telescope defers** (CHAIN-2c-ii-arm, P2 of the ARM-WIRING DESIGN-PASS,
`notes/Phase23-design.md` §(o‴)(I.8.4) step 2; Phase 23b). The general candidate-`i` lift of the
`i = 3` de-risk gate `i3_freshEdge_surviving_rows_mem_deRisk`'s reusable `hrow` builder: at the
relabel-arm framework `Fva = ofNormals (G − vtx i) ends qρ` (the candidate that removes the chain
vertex `vtx i`, `i : Fin (cd.d + 1)`), a surviving interior chain edge `edge s` (`s + 1 < (i : ℕ)`,
so both endpoints `vtx s`, `vtx (s+1)` have index `< i` and survive `removeVertex (vtx i)`) gives a
rigidity-row-span member `hingeRow (vtx s) (vtx (s+1)) ρ₀ ∈ span Fva.rigidityRows`, **once** the
per-edge perpendicularity `ρ₀ ⊥ Fva.supportExtensor (edge s)` (`hp`) is supplied.

This is exactly the family of `hsurv` summand memberships that `wstep_foldl_freshEdge_slot_mem`
takes as the abstract hypothesis `hsurv : ∀ s ∈ range m, hingeRow (w s) (w (s+1)) ρ₀ ∈ S` (at
`S := span Fva.rigidityRows`, `w := cd.vtx ∘ Fin.mk`): subtracting the `m` surviving rows from the
landed W9a fold output `W φ ∈ span` peels off the fresh-edge slot row (the engine `hρGv` slot). The
**`link` half is concrete-clean** (`cd.link` gives the genuine `G`-link, `vtx_ne` the survival of
`removeVertex (vtx i)`, `hingeRow_mem_rigidityRows` + `mem_hingeRowBlock_iff` the membership
certificate); the **`perp` half `hp` is the genuinely-new P2 obligation** carried here as the
explicit gate hypothesis (the standing project idiom for an undischarged crux), to be discharged by
the iterated KT eq.~(6.66) degree-2 carry `ρ₀_perp_interior_chain_edge` (§(o‴)(I.8.3.v) route (a))
from the W6b `hρe₀` base. Generalizes the `i = 3` gate's `hrow` (the `removeVertex (vtx ⟨3,_⟩)`
special case) to general `i` and general edge index `s` (`s + 1 < (i : ℕ)`), so the arm closer
`chainData_relabel_arm` consumes one instance per surviving chain edge of candidate `i`. -/
theorem _root_.Graph.ChainData.freshEdge_surviving_row_mem
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (i : Fin (cd.d + 1)) (s : ℕ)
    (hs : s + 1 < (i : ℕ))
    {ends : β → α × α} {qρ : α × Fin (k + 2) → K} (ρ₀ : Module.Dual K (ScrewSpace K k))
    -- the per-edge perp obligation (the genuinely-new P2 content the arm must still discharge):
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
  -- the genuine-link membership certificate: link in `Fva.graph` + `ρ₀ ∈ hingeRowBlock (edge s)`.
  refine BodyHingeFramework.hingeRow_mem_rigidityRows Fva (e := cd.edge ⟨s, by omega⟩) ?_ ?_
  · rw [hFva, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]
    exact hlinkGv
  · exact (Fva.mem_hingeRowBlock_iff _ ρ₀).2 hperp

/-- **The general-`i` surviving chain-edge row-membership builder, perp discharged from the
eq.~(6.52) two-edge witness** (CHAIN-2c-ii-arm, the `hρGv` P2 A-3 composition step;
`notes/Phase23-design.md` §(o‴)(I.8.3.v-SETTLED) Route A, §(o‴)(I.8.4); Phase 23b). The Route-A
closure of `freshEdge_surviving_row_mem`: instead of carrying the per-edge perp `ρ₀ ⊥
Fva.supportExtensor (edge s)` as an abstract hypothesis, it is **discharged for real** from the
eq.~(6.52) `λ`-grouped two-edge witness at the surviving edge's interior chain vertex
`vtx (s+1)` — exactly the witness the W6b producer
`exists_candidateRow_bottomRows_of_rigidOn` now supplies (A-1).

The interior vertex `a := vtx (s+1)` is degree-2 with the two incident chain edges `e_c := edge s`
(linking `a` to its predecessor `b := vtx s`) and `e_d := edge (s+1)` (linking `a` to its successor
`c := vtx (s+2)`); the candidate functional is the common redundancy vector `ρ₀ = ∑_j λ_{(ab)j}
(rab j)` of KT eq.~(6.42). Feeding the witness (the per-edge perps `hperp_ab`/`hperp_ac` and the
eq.~(6.43) column vanishing `hcol`/`hrest`) through `candidate_perp_two_incident_supportExtensors`
(A-2, KT eq.~(6.44)) yields `ρ₀ ⊥ Fva.supportExtensor e_c = Fva.supportExtensor (edge s)`, which is
precisely the `hperp` hypothesis `freshEdge_surviving_row_mem` deferred. The `link`/membership half
is then concrete (delegated to `freshEdge_surviving_row_mem`).

This is the single-vertex step of the iterated KT eq.~(6.66) carry; the all-`i` lift (propagating
the witness across the chain off the W6b `hρe₀` base) and the arm assembly `chainData_relabel_arm`
remain. Self-contained over the explicit witness, **zero blast radius** (no live caller). -/
theorem _root_.Graph.ChainData.freshEdge_surviving_row_mem_of_witness [DecidableEq α]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (i : Fin (cd.d + 1)) (s : ℕ)
    (hs : s + 1 < (i : ℕ)) (hsd : s + 1 < cd.d)
    {ends : β → α × α} {qρ : α × Fin (k + 2) → K}
    {ιab ιac : Type*} [Fintype ιab] [Fintype ιac]
    (lamAB : ιab → K) (rab : ιab → Module.Dual K (ScrewSpace K k))
    (lamAC : ιac → K) (rac : ιac → Module.Dual K (ScrewSpace K k))
    (grest : Module.Dual K (α → ScrewSpace K k))
    -- the per-edge perps of the witness rows, in the candidate framework `Fva = ofNormals (G−vᵢ)`:
    (hperp_ab : ∀ j, rab j ((PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i)) ends qρ)
      |>.toBodyHinge.supportExtensor (cd.edge ⟨s, by omega⟩)) = 0)
    (hperp_ac : ∀ j, rac j ((PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i)) ends qρ)
      |>.toBodyHinge.supportExtensor (cd.edge ⟨s + 1, by omega⟩)) = 0)
    -- the eq.~(6.43) column vanishing at the degree-2 interior vertex `a = vtx (s+1)`:
    (hcol : ((∑ j, lamAB j • BodyHingeFramework.hingeRow (k := k) (α := α)
          (cd.vtx ⟨s + 1, by omega⟩) (cd.vtx ⟨s, by omega⟩) (rab j))
        + (∑ j, lamAC j • BodyHingeFramework.hingeRow (k := k) (α := α)
          (cd.vtx ⟨s + 1, by omega⟩) (cd.vtx ⟨s + 2, by omega⟩) (rac j)) + grest).comp
        (LinearMap.single K (fun _ : α => ScrewSpace K k) (cd.vtx ⟨s + 1, by omega⟩)) = 0)
    (hrest : grest.comp
        (LinearMap.single K (fun _ : α => ScrewSpace K k) (cd.vtx ⟨s + 1, by omega⟩)) = 0) :
    BodyHingeFramework.hingeRow (cd.vtx ⟨s, by omega⟩) (cd.vtx ⟨s + 1, by omega⟩)
        (∑ j, lamAB j • rab j) ∈
      Submodule.span K (PanelHingeFramework.ofNormals (G.removeVertex
        (cd.vtx i)) ends qρ).toBodyHinge.rigidityRows := by
  classical
  set Fva := (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i)) ends qρ).toBodyHinge
    with hFva
  -- The interior vertex `a = vtx (s+1)` differs from its two chain neighbours `b = vtx s`,
  -- `c = vtx (s+2)` (distinct chain indices, `vtx_inj`).
  have hab : cd.vtx ⟨s + 1, by omega⟩ ≠ cd.vtx ⟨s, by omega⟩ :=
    fun he => by have : s + 1 = s := congrArg Fin.val (cd.vtx_inj he); omega
  have hac : cd.vtx ⟨s + 1, by omega⟩ ≠ cd.vtx ⟨s + 2, by omega⟩ :=
    fun he => by have : s + 1 = s + 2 := congrArg Fin.val (cd.vtx_inj he); omega
  -- A-2 (KT eq.~(6.44)): the common candidate `ρ₀ = ∑_j λ_{(ab)j} (rab j)` is ⊥ the panel at
  -- the surviving edge `e_c = edge s` (the first of the two incident-panel perps).
  have hperp : (∑ j, lamAB j • rab j) (Fva.supportExtensor (cd.edge ⟨s, by omega⟩)) = 0 :=
    (Fva.candidate_perp_two_incident_supportExtensors hab hac lamAB rab lamAC rac grest
      hperp_ab hperp_ac hcol hrest).1
  -- thread the discharged perp into the `link`-half builder.
  exact cd.freshEdge_surviving_row_mem i s hs (∑ j, lamAB j • rab j) hperp

/-! ### The general-`i` `hρGv` fresh-edge telescope (CHAIN-2c-ii-arm, LEAF-ρ1 algebraic core)

The genuinely-new algebraic core of the `hρGv` discharge: the closed-form value of the
seed-advancing W9a `wstep` `foldl` (the relabel arm's redundancy transport) at general candidate
`i`, generalizing the `i = 3` 2-residue gate `i3_wstep_foldl_base_redundancy_deRisk` to the
`i − 1`-step `reverseRec` telescope. Over an injective vertex function `w : ℕ → α` and the ascending
moved-body list `[(w₁,w₂,w₃), …, (w_{m},w_{m+1},w_{m+2})]` (length `m`, the `shiftBodyListAsc i`
shape with `m = i − 1`), the `wstep` foldl of the base redundancy `hingeRow (w 0) (w 2) ρ₀` is

  `(∑ s ∈ range m, hingeRow (w s) (w (s+1)) ρ₀) + hingeRow (w m) (w (m+2)) ρ₀`

— the `m` genuine surviving chain-edge rows `wₛ—wₛ₊₁` (KT eq. (6.62)'s transported `(v₀v₁)ᵢ∗` form,
iterated) plus the single fresh-edge slot row `w_m—w_{m+2}` (KT's `Mᵢ` row, the engine `hρGv` slot
at candidate `i = m + 1`: `vᵢ₋₁ = w_m`, `vᵢ₊₁ = w_{m+2}`). This is KT eq. (6.66) — the iterated
degree-2 `±r` `a`-column cancellation — realized as the `wstep` telescope's closed form.

The membership corollary (subtract the `m` genuine surviving rows from `W φ ∈ span`, both endpoints
`< i` so surviving `removeVertex vᵢ`) is the general-`i` analogue of the de-risk gate
`i3_freshEdge_slot_mem_deRisk`: the fresh-edge slot row reaches `span (G − vᵢ).rigidityRows`. -/

/-- **`wstep` fixes a hinge row off both moved bodies.** When neither endpoint `x`, `y` of
`hingeRow x y ρ` is the swapped body `a` or the freed slot `v`, the W9a step `wstep v a c` leaves
the row unchanged: the relabel `swap a v` fixes both endpoints (`hingeRow_funLeft_dualMap`), and the
`a`-column subtraction vanishes because body `a` is incident to neither endpoint
(`hingeRow_comp_single_off`). These are the *surviving chain-edge rows* of the telescope — KT eq.
(6.62)'s transported redundancy form, untouched by the later degree-2 cancellations. -/
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

/-- **`wstep` on the fresh-edge frontier row produces the next surviving edge plus the next frontier
row** (the inductive heart of the telescope, the per-step KT eq. (6.66) `±r` cancellation). The
step's body triple is `(v, a, c)`; applied to the frontier row `hingeRow x a ρ` (whose tail endpoint
is the moved body `a`, with `x ≠ a`, `x ≠ v`), the relabel sends `a ↦ v` giving the genuine
successor edge `hingeRow x v ρ`, and the `a`-column subtraction contributes the new frontier
row `hingeRow v c ρ`. So `wstep v a c (hingeRow x a ρ) = hingeRow x v ρ + hingeRow v c ρ`. At chain
step `s` this is `(x, a, v, c) = (wₛ, wₛ₊₂, wₛ₊₁, wₛ₊₃)`: the frontier `wₛ—wₛ₊₂` advances to the
surviving edge `wₛ—wₛ₊₁` plus the new frontier `wₛ₊₁—wₛ₊₃`. -/
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

/-- **The general-`i` `hρGv` fresh-edge telescope — closed form** (CHAIN-2c-ii-arm, LEAF-ρ1
algebraic core; `notes/Phase23-design.md` §(o‴)(I.7.3)/(I.7.10)). The seed-advancing W9a `wstep`
`foldl` over the ascending moved-body list `[(w₁,w₂,w₃), …, (w_m,w_{m+1},w_{m+2})]` (length `m`,
the `shiftBodyListAsc i` shape with `m = i − 1`), applied to the base `(v₀v₂)`-block redundancy
`hingeRow (w 0) (w 2) ρ₀` (KT eq. (6.52)), telescopes to the `m` genuine surviving chain-edge rows
plus the single fresh-edge slot row. This is the `i − 1`-step `reverseRec` generalization of the
`i = 3` 2-residue gate `i3_wstep_foldl_base_redundancy_deRisk` (`m = 2`), and realizes KT eq. (6.66)
(the iterated degree-2 `a`-column cancellation) as the `wstep` telescope's closed form. The vertex
function `w` is injective on the finite index range `0 … m+2` the statement touches (the chain
vertices are distinct, `cd.vtx_inj` — the arm supplies this from `Set.InjOn.mono` of `vtx_inj`;
**not** the global `Function.Injective (ℕ → α)`, which is `False` over the arm's `[Finite α]` vertex
type, §(o‴)(I.8) P1), so each step's swap and `a`-column restriction act cleanly. -/
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
    -- A range-scoped distinctness helper: `w i ≠ w j` whenever `i, j ≤ m+2` and `i ≠ j`. The arm
    -- runs on the finite vertex type, where global injectivity is unavailable; `hinj` is the
    -- finite-range form (`Set.InjOn` on `Set.Iic (m+1+2)`, here used at indices `≤ m+2`).
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
    -- the frontier row `w_m—w_{m+2}` advances to the new surviving edge `w_m—w_{m+1}` + the new
    -- frontier `w_{m+1}—w_{m+3}` (`wstep_hingeRow_frontier`, the per-step KT (6.66) cancellation).
    rw [BodyHingeFramework.wstep_hingeRow_frontier
      (hne m (m + 2) (by omega) (by omega) (by omega))
      (hne m (m + 1) (by omega) (by omega) (by omega)) ρ₀]
    -- regroup: `(∑_{s<m} + frontier-advance) = (∑_{s<m+1}) + new-frontier`.
    rw [Finset.sum_range_succ]
    abel

/-- **The general-`i` `hρGv` fresh-edge slot membership — the KT-(6.66) peel-off** (CHAIN-2c-ii-arm,
LEAF-ρ1 → LEAF-ρ3 bridge; `notes/Phase23-design.md` §(o‴)(I.7.3)/(I.7.10)). The `i − 1`-step
(`m = i − 1`) generalization of the de-risk gate `i3_freshEdge_slot_mem_deRisk` (the `m = 2`
instance): from the landed W9a `wstep` `foldl` output `∈ S` (the closed-form telescope
`wstep_foldl_hingeRow_telescope`) and the `m` genuine surviving chain-edge rows
`hingeRow (w s) (w (s+1)) ρ₀ ∈ S` (`s < m`, both endpoints `< i` so surviving `removeVertex vᵢ`),
the fresh-edge slot row `hingeRow (w m) (w (m+2)) ρ₀` (KT's `Mᵢ` row, the engine `hρGv` slot at
candidate `i = m + 1`: `vᵢ₋₁ = w_m`, `vᵢ₊₁ = w_{m+2}`) reaches `S` by `Submodule.sub_mem`: the slot
row is `W φ − (∑ surviving rows)`.

Stated abstractly over the span carrier `S` (the surviving-row memberships are what the arm closer
`chainData_relabel_arm` supplies from the genuine surviving chain-edge rows of `G − vᵢ`, and `hW`
from the landed `shiftBodyListAsc_foldl_mem_span_rigidityRows`). This is the algebraic skeleton of
the `hρGv` discharge, decoupled from the graph-level `rigidityRows` plumbing the arm wires in — the
general-`d` analogue of the d=3 `M₃` `case hρGv` `sub_mem` peel (`case_III_arm_realization_M3`).

The injectivity hypothesis is the finite-range `Set.InjOn w (Set.Iic (m + 2))` (the index range the
statement touches), **not** the global `Function.Injective (ℕ → α)`: the arm runs on the finite
vertex type `[Finite α]` where global `ℕ → α` injectivity is `False`, so the arm supplies this from
`cd.vtx_inj` via `Set.InjOn.mono` (§(o‴)(I.8) P1). -/
theorem BodyHingeFramework.wstep_foldl_freshEdge_slot_mem [DecidableEq α]
    (w : ℕ → α) (m : ℕ) (hinj : Set.InjOn w (Set.Iic (m + 2)))
    (ρ₀ : Module.Dual K (ScrewSpace K k))
    {S : Submodule K (Module.Dual K (α → ScrewSpace K k))}
    (hW : ((List.ofFn fun s : Fin m => (w ((s : ℕ) + 1), w ((s : ℕ) + 2), w ((s : ℕ) + 3))).foldl
        (fun T b => (BodyHingeFramework.wstep (k := k) b.1 b.2.1 b.2.2).comp T) LinearMap.id)
      (BodyHingeFramework.hingeRow (w 0) (w 2) ρ₀) ∈ S)
    (hsurv : ∀ s ∈ Finset.range m, BodyHingeFramework.hingeRow (w s) (w (s + 1)) ρ₀ ∈ S) :
    BodyHingeFramework.hingeRow (w m) (w (m + 2)) ρ₀ ∈ S := by
  -- the landed closed-form telescope rewrites `hW` to `(∑ surviving) + slot ∈ S`.
  rw [BodyHingeFramework.wstep_foldl_hingeRow_telescope w m hinj ρ₀] at hW
  -- the `m` genuine surviving rows sum to a span member.
  have hsum : (∑ s ∈ Finset.range m, BodyHingeFramework.hingeRow (w s) (w (s + 1)) ρ₀) ∈ S :=
    Submodule.sum_mem _ hsurv
  -- subtract: `((∑ surviving) + slot) − (∑ surviving) = slot ∈ S`.
  have := Submodule.sub_mem _ hW hsum
  rwa [add_sub_cancel_left] at this

/-- **The general-`i` panel-correspondence at the `supportExtensor` level (CHAIN-2c-ii-arm, Route
W's witness-transport identity)** (`notes/Phase23-design.md` §(o‴)(I.8.8) option (a′); KT 2011
§6.4.2 eqs.~(6.59)/(6.62) the index-shift panel correspondence; Phase 23b). The
general-candidate-`i` generalization of `i3_panelCorrespondence_supportExtensor_deRisk` (its
`i = 3` / `s = 0`/`s = 1`
instance): for **any** candidate `i` and **any** surviving interior chain edge `edge s` with
`s + 1 < (i : ℕ)` (so both endpoints `vtx s`, `vtx (s+1)` survive `removeVertex (vtx i)`), the
candidate-`i` framework's supporting extensor at `edge s` equals the `v₁`-base framework's at the
KT-corresponding edge `shiftEdgePerm i (edge s)` — VERBATIM, no metric / Plücker step.

The candidate framework is `ofNormals (G − vtx i) endsσρ qρ` with the
`(shiftPerm i.castSucc, shiftEdgePerm i)`-relabelled selector `endsσρ`/seed `qρ` — exactly the shape
`chainData_bottom_relabel` produces for the `hwmem` slot. This is a **direct application of the
already-landed `ofNormals_supportExtensor_relabel_perm`** (support extensors are graph-independent —
they read only `ends₀`/`normal` — so the candidate base graph `G − vtx i` vs the `v₁`-base graph
`G − vtx 1` is discharged by the closing `simp only`). The corresponding base edge resolves
explicitly via the `shiftEdgePerm_apply_edge_*` lemmas: `edge 0 ↦ e₀` (head, `s = 0`) and
`edge s ↦ edge (s+1)` (interior, `1 ≤ s`). This is the transport identity Route W's per-interior-
vertex witness producer `exists_interior_redundancy_witness` threads its perp across: a `rw` of this
identity turns the candidate-side perp `ρ₀ ⊥ Fva.supportExtensor (edge s)` into the base-side perp
at the corresponding edge, which A-1's base witness supplies. d=3 (`i = 2`) is the landed `M₃` swap
involution; this re-indexes the de-risk over each interior chain edge `s + 1 < (i : ℕ)`. -/
theorem _root_.Graph.ChainData.panelCorrespondence_supportExtensor
    [DecidableEq α] [DecidableEq β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (i : Fin cd.d) (s : ℕ)
    (hsi : s + 1 < (i : ℕ))
    {ends₀ : β → α × α} {q : α × Fin (k + 2) → K} :
    (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨(i : ℕ), by have := i.isLt; omega⟩))
        (fun e => ((cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).1,
          (cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).2))
        (fun p => q (cd.shiftPerm i.castSucc p.1,
          p.2))).toBodyHinge.supportExtensor (cd.edge ⟨s, by have := i.isLt; omega⟩) =
      (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩))
        ends₀ q).toBodyHinge.supportExtensor
          (cd.shiftEdgePerm i (cd.edge ⟨s, by have := i.isLt; omega⟩)) := by
  rw [PanelHingeFramework.ofNormals_supportExtensor_relabel_perm
    (cd.shiftPerm i.castSucc) (cd.shiftEdgePerm i)]
  -- the two base frameworks differ only in their (irrelevant) graph; `supportExtensor` reads only
  -- `ends₀`/`q`, so both sides reduce to the same `panelSupportExtensor`.
  simp only [PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_ends,
    PanelHingeFramework.ofNormals_normal]

/-- **The `i = 3` panel-correspondence de-risk for Route W's witness producer (the smallest next
commit toward `chainData_relabel_arm`'s `hρGv` slot)** (`notes/Phase23-design.md` §(o‴)(I.8.8)
option (a′); KT 2011 §6.4.2 eqs.~(6.59)/(6.62) the index-shift panel correspondence; Phase 23b).
Before
pinning the genuinely-new Route-W producer `exists_interior_redundancy_witness`'s signature
(row-321 discipline), this checks the load-bearing structural fact option (a′) rests on: the
candidate-`i = 3` framework's supporting extensor at each of the interior vertex `vtx 1`'s two
surviving incident chain edges (`edge 0`, `edge 1`) equals — VERBATIM, no metric / Plücker step —
the `v₁`-base framework's supporting extensor at the KT-corresponding edge.

The candidate framework is `ofNormals (G − vtx 3) endsσρ qρ` with the
`(shiftPerm 3.castSucc, shiftEdgePerm 3)`-relabelled selector `endsσρ`/seed `qρ` — exactly the shape
`chainData_bottom_relabel` produces for the `hwmem` slot. The KT-corresponding base edge is the
`shiftEdgePerm 3`-image: `edge 0 ↦ e₀` (`shiftEdgePerm_apply_edge_zero`) and `edge 1 ↦ edge 2`
(`shiftEdgePerm_apply_edge_interior`). The coincidence is the already-landed
`ofNormals_supportExtensor_relabel_perm` (support extensors are graph-independent — they read only
`ends₀`/`normal` — so the base graph `G − vtx 1` vs the relabel lemma's `G − vtx 3` is irrelevant,
discharged by the closing `simp only`).

**VERDICT = SUCCESS** (§(o‴)(I.8.8)): the panel correspondence holds at the `supportExtensor` level,
so option (a′) is buildable — Route W's per-interior-vertex witness can be obtained by re-deriving
A-1's base witness at the `v₁`-split `G₁` (where the eq.-(6.24) decomposition's rigidity premises
`h618`/`h622lb` are available) and transporting the *conclusion* (the perp) to `Fva = G − vtx 3`
across this correspondence + the flagged P3 seed bridge `shiftSeedAdv_eq_funLeft_shiftPerm`. This
de-risks the producer signature without pinning it; the producer + the all-`i` lift +
`chainData_relabel_arm` follow. d=3 (`i = 2`) is the landed `M₃` swap involution; the general lift
re-indexes this over each interior chain edge `s + 1 < (i : ℕ)`. -/
theorem _root_.Graph.ChainData.i3_panelCorrespondence_supportExtensor_deRisk
    [DecidableEq α] [DecidableEq β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (h4 : 4 ≤ cd.d)
    {ends₀ : β → α × α} {q : α × Fin (k + 2) → K} :
    (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨3, by omega⟩))
        (fun e => ((cd.shiftPerm (⟨3, by omega⟩ : Fin cd.d).castSucc).symm
            (ends₀ (cd.shiftEdgePerm ⟨3, by omega⟩ e)).1,
          (cd.shiftPerm (⟨3, by omega⟩ : Fin cd.d).castSucc).symm
            (ends₀ (cd.shiftEdgePerm ⟨3, by omega⟩ e)).2))
        (fun p => q (cd.shiftPerm (⟨3, by omega⟩ : Fin cd.d).castSucc p.1,
          p.2))).toBodyHinge.supportExtensor (cd.edge ⟨0, by omega⟩) =
      (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩))
        ends₀ q).toBodyHinge.supportExtensor cd.e₀ ∧
    (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨3, by omega⟩))
        (fun e => ((cd.shiftPerm (⟨3, by omega⟩ : Fin cd.d).castSucc).symm
            (ends₀ (cd.shiftEdgePerm ⟨3, by omega⟩ e)).1,
          (cd.shiftPerm (⟨3, by omega⟩ : Fin cd.d).castSucc).symm
            (ends₀ (cd.shiftEdgePerm ⟨3, by omega⟩ e)).2))
        (fun p => q (cd.shiftPerm (⟨3, by omega⟩ : Fin cd.d).castSucc p.1,
          p.2))).toBodyHinge.supportExtensor (cd.edge ⟨1, by omega⟩) =
      (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩))
        ends₀ q).toBodyHinge.supportExtensor (cd.edge ⟨2, by omega⟩) := by
  -- both conjuncts are the general `panelCorrespondence_supportExtensor` at `i := ⟨3,_⟩`,
  -- `s := 0` resp. `s := 1`, with the `shiftEdgePerm`-image resolved by the edge accessors.
  refine ⟨?_, ?_⟩
  · rw [cd.panelCorrespondence_supportExtensor ⟨3, by omega⟩ 0 (by norm_num),
      cd.shiftEdgePerm_apply_edge_zero ⟨3, by omega⟩ (by norm_num)]
  · rw [cd.panelCorrespondence_supportExtensor ⟨3, by omega⟩ 1 (by norm_num),
      cd.shiftEdgePerm_apply_edge_interior ⟨3, by omega⟩ (by norm_num) (by norm_num)]

/-- **Route W's per-edge perp transport: a base-split perp becomes a candidate-split perp**
(CHAIN-2c-ii-arm, the structural bridge `exists_interior_redundancy_witness` threads its witness's
per-row perps across; `notes/Phase23-design.md` §(o‴)(I.8.8) option (a′); KT 2011 §6.4.2 eqs.
(6.59)/(6.62) the index-shift panel correspondence; Phase 23b).

A screw-level functional `ρ'` perpendicular to the `v₁`-base framework's supporting extensor at the
KT-corresponding edge `shiftEdgePerm i (edge s)` is perpendicular to the candidate-`i` framework's
supporting extensor at the surviving interior chain edge `edge s` — for any candidate `i : Fin cd.d`
and surviving interior edge `edge s` (`s + 1 < (i : ℕ)`, so both endpoints `vtx s`, `vtx (s+1)`
survive `removeVertex (vtx i)`). This is a one-step `rw` of the landed general-`i` transport
identity `panelCorrespondence_supportExtensor` (the two frameworks' supporting extensors at the
corresponding edges are *equal*).

This is the load-bearing step of option (a′): Route W re-derives A-1's eq.~(6.52) two-edge witness
at the **base split `G₁`** (where the eq.~(6.24) decomposition's rigidity premises `h618`/`h622lb`
are available), obtaining the per-row perps `rab j ⊥ G₁-base.supportExtensor (shiftEdgePerm i
(edge s))`, then this lemma transports them to the candidate framework's `hperp_ab`/`hperp_ac`
shape that `freshEdge_surviving_row_mem_of_witness` (A-3) consumes. The candidate framework is the
relabelled
`ofNormals (G − vtx i) endsσρ qρ` shape `chainData_bottom_relabel` produces for the `hwmem` slot.
Self-contained over the landed transport identity, **zero blast radius** (no live caller; consumed
by the producer + the arm). d=3 (`i = 2`) is the landed `M₃` swap involution. -/
theorem _root_.Graph.ChainData.candidate_supportExtensor_perp_of_base
    [DecidableEq α] [DecidableEq β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (i : Fin cd.d) (s : ℕ)
    (hsi : s + 1 < (i : ℕ))
    {ends₀ : β → α × α} {q : α × Fin (k + 2) → K} (ρ' : Module.Dual K (ScrewSpace K k))
    (hperp : ρ' ((PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩))
        ends₀ q).toBodyHinge.supportExtensor
          (cd.shiftEdgePerm i (cd.edge ⟨s, by have := i.isLt; omega⟩))) = 0) :
    ρ' ((PanelHingeFramework.ofNormals
        (G.removeVertex (cd.vtx ⟨(i : ℕ), by have := i.isLt; omega⟩))
        (fun e => ((cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).1,
          (cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).2))
        (fun p => q (cd.shiftPerm i.castSucc p.1,
          p.2))).toBodyHinge.supportExtensor (cd.edge ⟨s, by have := i.isLt; omega⟩)) = 0 := by
  rw [cd.panelCorrespondence_supportExtensor i s hsi]
  exact hperp

/-- **The BASE-`G₁` interior-regrouping de-risk — at the `v₁`-split the immediate-successor interior
chain vertex `vtx 2` is degree-ONE, so its column projection is a *single* block, NOT the obstructed
two-edge sup** (CHAIN-2c-ii-arm, the Route-W producer-core fork de-risk; `notes/Phase23-design.md`
§(o‴)(I.8.9), the "SMALLEST NEXT COMMIT = the BASE-`G₁` interior-regrouping de-risk"; Phase 23b).
The §(I.8.9) producer-core recon flagged a fork for the genuinely-new Route-W witness producer
`exists_interior_redundancy_witness`: the consumer's witness `hcol`/`hrest` (the eq.~(6.43) column
vanishing) must be *produced* at each interior vertex, and the eq.~(6.24) base decomposition
(`exists_redundant_panelRow_ab_decomposition_acolumn_zero`) supplies only the *single-edge* `e₀`
data with a *global* `g = 0` conclusion — so the open question is whether the base redundancy can be
*regrouped* at an interior degree-2 vertex into `(ab) + (ac) + grest`. The de-risk asks the prior
structural question (before pinning the producer's signature, the row-321 discipline): **at the base
`v₁`-split `G − vtx 1` — where the eq.~(6.24) decomposition's premises `h618`/`h622lb` hold — is the
immediate-successor interior chain vertex `vtx 2` degree-two (forcing the obstructed two-edge sup),
or is it degree-ONE?**

**Verdict (ground-truth in Lean): the base `v₁`-split kills the interior vertex `vtx 2`'s
*predecessor* chain edge `edge 1 = v₁v₂` — that edge has the removed apex `v₁` as an endpoint — so
`vtx 2` retains only its *successor* chain edge `edge 2 = v₂v₃` and is degree-ONE in `G − vtx 1`.**
Hence a span member `wGv ∈ span (G − vtx 1) rigidityRows` has its `vtx 2`-column landing in the
*single* block `block (edge 2)` via the one-edge `acolumn_mem_hingeRowBlock_of_span_rigidityRows` —
**NOT** the two-edge sup `acolumn_..._sup_...` that obstructed the *candidate*-side lift
(`i3_freshEdge_interior_acolumn_sup_deRisk`, which is the same situation read at the candidate split
`G − vtx i` where `vtx 2` keeps both edges and is genuinely degree-two). This is the structural fact
the §(I.8.9) "is `vtx 2` degree-2 in `G − v₁`?" sub-question resolves to **degree-ONE = SUCCESS**:
at the base the immediate-successor interior vertex behaves like the d=3 `M₃` degree-one interior
(single-block, the landed one-edge mechanism applies), so the base-side regrouping at this vertex is
tractable with no new two-block carry — exactly the d=3 `M₃` situation, generalized.

This **de-risks the producer signature without pinning it** (it does not build
`exists_interior_redundancy_witness`): it isolates *which* column-projection brick the base producer
threads through at the first interior vertex (the one-edge form, not the obstructed sup), confirming
the (a′-i) route's base-regrouping half is buildable at this vertex with landed infrastructure. The
asymmetry — base `vtx 2` is degree-one, candidate `vtx 1` is degree-two — is the precise mirror
image of the candidate-side de-risk verdict, and it is *why* the base is the right place to
re-derive the witness (option (a′)): the removed apex shears off one incident edge of its neighbour.
d=3 (`d = 3`, `i = 2`) is the landed `M₃` swap involution; the general lift re-indexes this. -/
theorem _root_.Graph.ChainData.i3_base_interior_acolumn_single_deRisk [DecidableEq α]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (h4 : 4 ≤ cd.d)
    {ends : β → α × α} {q : α × Fin (k + 2) → K}
    {wGv : Module.Dual K (α → ScrewSpace K k)}
    -- a span member of the base `v₁`-split's rigidity rows (the eq.-(6.24) redundancy `wGv` lives
    -- here):
    (hwGv : wGv ∈ Submodule.span K (PanelHingeFramework.ofNormals (G.removeVertex
        (cd.vtx ⟨1, by omega⟩)) ends q).toBodyHinge.rigidityRows) :
    -- its `vtx 2`-column lands in the *single* block `block (edge 2)` — the immediate-successor
    -- interior vertex is degree-ONE at the base (predecessor edge killed by the `v₁`-removal).
    wGv.comp (LinearMap.single K (fun _ : α => ScrewSpace K k) (cd.vtx ⟨2, by omega⟩)) ∈
      ((PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩)) ends q).toBodyHinge
        |>.hingeRowBlock (cd.edge ⟨2, by omega⟩)) := by
  classical
  set Fv := (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩))
    ends q).toBodyHinge with hFv
  -- The successor edge `edge 2 = v₂v₃` survives `removeVertex (vtx 1)`: endpoints `v₂, v₃ ≠ v₁`.
  have h23 : cd.vtx ⟨2, by omega⟩ ≠ cd.vtx ⟨3, by omega⟩ := cd.vtx_ne _ _ (by omega)
  have h21 : cd.vtx ⟨2, by omega⟩ ≠ cd.vtx ⟨1, by omega⟩ := cd.vtx_ne _ _ (by omega)
  have h31 : cd.vtx ⟨3, by omega⟩ ≠ cd.vtx ⟨1, by omega⟩ := cd.vtx_ne _ _ (by omega)
  -- `edge 2` links `vtx 2 — vtx 3` in `G` (`link ⟨2,_⟩`).
  have hG2 : G.IsLink (cd.edge ⟨2, by omega⟩) (cd.vtx ⟨2, by omega⟩) (cd.vtx ⟨3, by omega⟩) := by
    have h := cd.link ⟨2, by omega⟩; simpa only [Fin.castSucc_mk, Fin.succ_mk] using h
  have hlink_ec : Fv.graph.IsLink (cd.edge ⟨2, by omega⟩) (cd.vtx ⟨2, by omega⟩)
      (cd.vtx ⟨3, by omega⟩) := by
    rw [hFv, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]
    exact Graph.removeVertex_isLink.mpr ⟨hG2, h21, h31⟩
  -- **Degree-ONE at `vtx 2` in `G − vtx 1`.** Every `(G − vtx 1)`-link `f` at `vtx 2` is a `G`-link
  -- at `vtx 2` (`removeVertex_isLink`); by `deg_two ⟨2,_⟩` it is `edge 1` or `edge 2`. But `edge 1`
  -- links the removed apex `vtx 1` (it is `v₁v₂`), so a surviving link cannot be `edge 1` — leaving
  -- `f = edge 2` as the sole option.
  have hdeg1 : ∀ f x, Fv.graph.IsLink f (cd.vtx ⟨2, by omega⟩) x → f = cd.edge ⟨2, by omega⟩ := by
    intro f x hlink
    rw [hFv, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph] at hlink
    have hGlink := (Graph.removeVertex_isLink.mp hlink).1
    -- `deg_two ⟨2,_⟩` at `(⟨2,_⟩ : Fin cd.d).castSucc = vtx 2`: `f = edge 1` or `f = edge 2`.
    have hd := cd.deg_two ⟨2, by omega⟩ (by simp) f x
    simp only [Fin.castSucc_mk] at hd
    rcases hd hGlink with he1 | he2
    · -- `f = edge 1`; but `edge 1 = v₁v₂` links the removed apex `v₁`, so the `(G − v₁)`-link `f`
      -- would have `v₁` as an endpoint — contradicting `removeVertex_isLink` (`x ≠ v₁`, `y ≠ v₁`).
      exfalso
      -- `edge 1 = v₁v₂` as a `G`-link (`link ⟨1,_⟩`); `⟨2 - 1, _⟩` is defeq `⟨1, _⟩`.
      have hG1 : G.IsLink (cd.edge ⟨(2 : ℕ) - 1, by omega⟩) (cd.vtx ⟨2, by omega⟩)
          (cd.vtx ⟨1, by omega⟩) := by
        have h := cd.link ⟨1, by omega⟩; simpa only [Fin.castSucc_mk, Fin.succ_mk] using h.symm
      -- `f = edge 1` and `hGlink : G.IsLink f (vtx 2) x`, so `x = vtx 1` by `IsLink.right_unique`.
      rw [he1] at hGlink
      have hx1 : x = cd.vtx ⟨1, by omega⟩ := hGlink.right_unique hG1
      -- but `hlink : (G − v₁).IsLink f (vtx 2) x` forces `x ≠ vtx 1` (`removeVertex_isLink`).
      exact (Graph.removeVertex_isLink.mp hlink).2.2 hx1
    · exact he2
  have hdeg1r : ∀ f x, Fv.graph.IsLink f x (cd.vtx ⟨2, by omega⟩) → f = cd.edge ⟨2, by omega⟩ :=
    fun f x hlink => hdeg1 f x hlink.symm
  exact BodyHingeFramework.acolumn_mem_hingeRowBlock_of_span_rigidityRows
    (Fab := Fv) (Fv := Fv) h23 hlink_ec rfl hdeg1 hdeg1r hwGv


end CombinatorialRigidity.Molecular
