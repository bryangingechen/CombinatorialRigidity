/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.AlgebraicInduction.CaseI

/-!
# The algebraic induction — Case II realization (the L6b producer)

Phase 22 (molecular-conjecture program; see `notes/MolecularConjecture.md`). The Case-II block of
the algebraic-induction realization layer, carved off `AlgebraicInduction/CaseI.lean` in the
post-Phase-22j perf round (`notes/Phase22j-perf.md`; no decl renamed or re-namespaced). On top of
the Case-I / rank-polynomial head in `AlgebraicInduction/CaseI`, this file carries:

* the eq. (6.12) `+(D−1)` block-triangular **placement** brick `case_II_placement_eq612`
  (`lem:case-II-realization-placement`, the first chunk of KT Lemma 6.10; Case III = Case II at
  `k = 0`, stratum 1);
* the **`k > 0` split producer** `case_II_realization_all_k` (`lem:case-II-realization` at `k > 0`;
  KT Lemma 6.8 / §6.3, the Phase-22i L6b `hsplitPos` carry) — a 2-edge-connected minimal `k`-dof
  graph with no proper rigid subgraph carries a generic full-rank realization, assembled inline
  from the eq. (6.12) placement steps and the deficient inductive hypothesis.

See `ROADMAP.md` §22 / `notes/Phase22i.md`, `notes/Phase22j.md` and the
`sec:molecular-algebraic-induction` dep-graph of `blueprint/src/chapter/algebraic-induction.tex`.
-/

namespace CombinatorialRigidity.Molecular

variable {k : ℕ}

open scoped Graph

variable {α β : Type*}

/-- **Case III (= Case II at `k = 0`), stratum 1: the eq. (6.12) `+(D−1)` block-triangular
placement** (`lem:case-II-realization-placement`, the first chunk of KT Lemma 6.10; Katoh–Tanigawa
2011 §6.4.1, eqs. (6.12), (6.16), Phase 22c). The first of three difficulty strata of the
conjecture's crux (the `theorem_55_all_k.hsplitZero` producer at `k = 0`):
the *degenerate* 1-extension
placement of the reducible degree-2 body `v` that re-inserts `v` into the split-off `Gᵥ = G_v^{ab}`
and produces a linearly independent panel-row family of size `D(|V(G)|−1) − 1` — one row short
of the `k = 0` full target `D(|V(G)|−1)`, the missing row being the Case-III content (strata 2–3,
a later sub-phase). It is a **lower-bound brick** toward the (still red) `lem:case-II-realization`
/ `lem:case-III`, *not* a `HasFullRankRealization`.

Construction (KT eq. (6.12)). Take the inductive realization of `Gᵥ` at a seed `q` (rigid on
`V(Gᵥ)`, transversal hinges) and **place `v`'s panel normal at `n_a + t·n_b`** (`n_a = q(a,·)`,
`n_b = q(b,·)`, `t ≠ 0`): the shear identity `panelSupportExtensor_add_smul_right` makes `v`'s
`b`-hinge `e_b = vb` reproduce the `e₀ = ab`-hinge of the inductive realization (the `vb`-row
reproduces the `e₀`-row), while `panelSupportExtensor_add_smul_left` keeps `v`'s `a`-hinge a
nondegenerate line `L ⊂ Π(a)` (the `t ≠ 0` candidate, KT's actual eq. (6.12) — not the degenerate
`t = 0` placement `v = a`). The shared seed is `q₀ := fun p ↦ if p.1 = v then (n_a + t·n_b) p.2 else
q p`; overriding only the fresh body `v` leaves the `Gᵥ`-block untouched (`v ∉ V(Gᵥ)`, so no
`Gᵥ`-edge touches `v`: `ofNormals_update_eq_withNormal` +
`toBodyHinge_withNormal_infinitesimalMotions_eq`), so the IH rigidity transports to `q₀`.

Assembly (KT eq. (6.16), block-triangular). The `+(D−1)` *new* block is the `D − 1` panel rows of
`v`'s `b`-edge `e_b` (`exists_independent_panelRow_subfamily_of_edge`, N7b-1), independent through
`v`'s screw column (`linearIndependent_panelRow_comp_single_of_edge`, the `hnewpin` input). The
`D(|V(Gᵥ)|−1)` *old* block is the rigid `Gᵥ`-realization's linking panel rows
(`exists_independent_panelRow_subfamily_of_rigidOn_linking`, N7b-0), carried onto `G` along the
`e₀`-dropping injection (`exists_independent_panelRow_transport`, N7b-2, with `hrow := rfl` since
`panelRow` reads only `ends`/`q₀`, not the graph). The pin-a-body column split
(`linearIndependent_sum_pinned_block`, N7b-3) joins them: the old rows vanish at `update 0 v x`
(their edges avoid `v`), the new rows read `v`'s column. The count is
`(D−1) + D(|V(Gᵥ)|−1) = D(|V(G)|−1) − 1` (using `|V(Gᵥ)| = |V(G)| − 1`). All members are rigidity
rows of `ofNormals G ends q₀`, the input the device-row closure
`isInfinitesimallyRigidOn_vertexSet_of_independent_rigidityRows` (N7a form (b)) consumes — but here
the family is one short of `D(|V(G)|−1)`, so it certifies only `rank R(G,p₁) ≥ D(|V(G)|−1) − 1`. -/
theorem PanelHingeFramework.case_II_placement_eq612 [DecidableEq α] [Finite α] [Finite β]
    (G Gv : Graph α β) (hGv : Gv ≤ G) (ends : β → α × α)
    -- the split-off block and the re-inserted body `v`, with its two new hinges `e_a = va`,
    -- `e_b = vb`. `e_a`'s `G`-link is crux-strata input, so stratum 1 needs only its selector.
    {v a b : α} {e_a e_b : β} (hvVc : v ∉ V(Gv)) (haVc : a ∈ V(Gv)) (hbVc : b ∈ V(Gv))
    (hG_eb : G.IsLink e_b v b) (hends_eb : ends e_b = (v, b))
    (_hG_ea : G.IsLink e_a v a) (hends_ea : ends e_a = (v, a))
    -- `|V(Gᵥ)| = |V(G)| − 1` (carried from `vertexSet_splitOff` downstream)
    (hVcard : V(Gv).ncard = V(G).ncard - 1)
    -- the inductive realization of `Gᵥ` at a seed `q`: rigid on `V(Gᵥ)`, transversal hinges, links
    {q : α × Fin (k + 2) → ℝ}
    (hends_Gv : ∀ e u w, Gv.IsLink e u w → Gv.IsLink e (ends e).1 (ends e).2)
    (hne_Gv : ∀ e, Gv.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.supportExtensor e ≠ 0)
    (hrig : (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.IsInfinitesimallyRigidOn V(Gv))
    -- the shear parameter `t ≠ 0` and the eq. (6.12) shared seed `q₀`
    {t : ℝ} (ht : t ≠ 0)
    (q₀ : α × Fin (k + 2) → ℝ)
    (hq₀ : q₀ = fun p => if p.1 = v then
        ((fun i => q (a, i)) + t • (fun i => q (b, i))) p.2 else q p)
    -- the inductive realization's `e₀ = ab`-hinge is transversal (so the reproduced `vb`-row ≠ 0)
    (hgab : LinearIndependent ℝ ![(fun i => q (a, i)), (fun i => q (b, i))]) :
    -- a `D(|V(G)|−1) − 1`-size independent panel-row family of `ofNormals G ends q₀`, all rigidity
    -- rows — the eq. (6.12) `+(D−1)` lower bound `rank R(G,p₁) ≥ D(|V(G)|−1) − 1` — together with
    -- `v`'s `a`-hinge nondegeneracy (the `va`-line `L ⊂ Π(a)`, KT's eq. (6.12) candidate, `t ≠ 0`).
    (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.supportExtensor e_a ≠ 0 ∧
    ∃ s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      screwDim k * (V(G).ncard - 1) - 1 ≤ Nat.card s ∧
      (∀ i ∈ s, (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.panelRow ends i
        ∈ (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.rigidityRows) ∧
      LinearIndependent ℝ (fun i : s =>
        (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.panelRow ends i) := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  set FG := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge with hFG
  set n_a : Fin (k + 2) → ℝ := fun i => q (a, i) with hn_a
  set n_b : Fin (k + 2) → ℝ := fun i => q (b, i) with hn_b
  -- (1) The shared seed is the IH seed with `v`'s normal overridden by `n_a + t • n_b`, so the IH
  -- rigidity transports to `q₀` (overriding the fresh `v ∉ V(Gᵥ)` leaves the `Gᵥ`-block untouched).
  have hqeq : (fun p => if p.1 = v then ((n_a + t • n_b) : Fin (k + 2) → ℝ) p.2 else q p) = q₀ := by
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
  -- The motion space is unchanged when overriding the unhinged `v`, so the IH rigidity transports.
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
  -- (2) OLD block (N7b-0, `_linking`): the rigid `Gᵥ`-realization carries `D(|V(Gᵥ)|−1)`
  -- independent linking panel rows of `ofNormals Gv ends q₀`.
  have hVGvne : V(Gv).Nonempty := ⟨b, hbVc⟩
  set FGv := (PanelHingeFramework.ofNormals Gv ends q₀).toBodyHinge with hFGv
  obtain ⟨so, hso_link, hso_card, hso_indep⟩ :=
    FGv.exists_independent_panelRow_subfamily_of_rigidOn_linking (ends := ends)
      (by simpa [hFGv] using hends_Gv) (by simpa [hFGv] using hne₀) (by simpa [hFGv] using hVGvne)
      (by simpa [hFGv] using hrig₀)
  -- (3) Transport the old block onto `G` (N7b-2; `panelRow` reads only `ends`/`q₀`, not the graph,
  -- so `hrow := rfl`).
  have hso_indep_G : LinearIndependent ℝ (fun i : so =>
      FG.panelRow ends (i : β × _ × _)) :=
    PanelHingeFramework.exists_independent_panelRow_transport Gv G ends ends q₀ q₀
      (f := id) Function.injective_id (fun i => rfl) hso_indep
  -- The re-inserted body `v` and its neighbour `b` are distinct (`b ∈ V(Gᵥ)`, `v ∉ V(Gᵥ)`).
  have hvb : v ≠ b := fun h => hvVc (h ▸ hbVc)
  -- The shared seed reads `q₀(v,·) = n_a + t·n_b` and `q₀(b,·) = n_b`.
  have hq₀v : (fun i => q₀ (v, i)) = n_a + t • n_b := by
    funext i; rw [hq₀]; simp
  have hq₀b : (fun i => q₀ (b, i)) = n_b := by
    funext i; rw [hq₀, hn_b]; simp only [if_neg hvb.symm]
  have hva : v ≠ a := fun h => hvVc (h ▸ haVc)
  have hq₀a : (fun i => q₀ (a, i)) = n_a := by
    funext i; rw [hq₀, hn_a]; simp only [if_neg hva.symm]
  -- The `va`-hinge `e_a` stays a nondegenerate line `L ⊂ Π(a)` (KT eq. (6.12), `t ≠ 0`).
  have hane : FG.supportExtensor e_a ≠ 0 := by
    rw [PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_ends,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal, hends_ea]
    simp only [hq₀v, hq₀a, panelSupportExtensor_add_smul_left]
    exact smul_ne_zero (neg_ne_zero.mpr ht) ((panelSupportExtensor_ne_zero_iff n_a n_b).mpr hgab)
  -- (4) NEW block (N7b-1): the reproduced `vb`-hinge `e_b` is transversal
  -- (`panelSupportExtensor_add_smul_right` reproduces the transversal `e₀ = ab`-hinge), giving
  -- `D − 1` independent new rows.
  have hnewne : FG.supportExtensor e_b ≠ 0 := by
    rw [PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_ends,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal, hends_eb]
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
  have hold : ∀ (j : so) (x : ScrewSpace k),
      FG.panelRow ends (j : β × _ × _)
        (Function.update (0 : α → ScrewSpace k) v x) = 0 := by
    rintro ⟨i, hi⟩ x
    have hlink := hso_link _ hi
    have h₁ : (ends i.1).1 ≠ v := fun h => hvVc (h ▸ hlink.left_mem)
    have h₂ : (ends i.1).2 ≠ v := fun h => hvVc (h ▸ hlink.right_mem)
    rw [BodyHingeFramework.panelRow, BodyHingeFramework.hingeRow_apply,
      Function.update_of_ne h₁, Function.update_of_ne h₂, Pi.zero_apply, Pi.zero_apply, sub_zero,
      map_zero]
  -- (6) The two blocks are jointly independent (N7b-3, the pin-a-body split = KT eq. (6.16)).
  have hunion : LinearIndependent ℝ (Sum.elim
      (fun i : sn => FG.panelRow ends
        (i : β × _ × _))
      (fun i : so => FG.panelRow ends
        (i : β × _ × _))) := by
    have hpin : LinearIndependent ℝ (fun i : sn =>
        (FG.panelRow ends (i : β × _ × _)).comp
          (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v)) := by
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

-- `case_II_realization_all_k` builds at the **default** `maxHeartbeats` since the Phase-22l
-- opacity flip (`abbrev ScrewSpace` → opaque `def`, `RigidityMatrix.lean`): the diffuse
-- `ScrewSpace` typeclass re-elaboration spread across its ~16 geometric Steps — formerly a 3×
-- (`600000`) whole-declaration budget — is gone now that the carrier head no longer re-unfolds
-- the heavy screw-space type-expression at every motive (`notes/ScrewSpaceCarrier-design.md` OQ1).
-- (23a Leaf 3 lifted the body to symbolic `ScrewSpace k`; the default budget still suffices.)
/-- **Lemma 6.8, the `k > 0` split** (`lem:case-II-realization` at `k > 0`; `hsplitPos` carry,
Phase 22i L6b). Katoh–Tanigawa 2011 §6.3, p. 677. A 2-edge-connected minimal `k`-dof-graph
(`k > 0`, `|V| ≥ 3`) with no proper rigid subgraph carries a generic full-rank realization.

The proof assembles the eq. (6.12) placement steps inline (no shared brick fits here — see below),
using the deficient IH at the degree-2 split-off `G_v^{ab}` plus the W-suite rank-polynomial
conversion. The key departure from the `k = 0` Case III: the deficient IH supplies exactly
`D(|V|-1) − k` rows (no Claim 6.11 gap-filling needed), so the eq. (6.12) placement closes
the rank exactly on its own.

A `case_II_placement_eq612`-shaped brick cannot be reused here: such a brick requires
`hGv : Gv ≤ G`, which fails for `Gv = G.splitOff v a b e₀` (`e₀ ∉ E(G)` but `e₀ ∈ E(Gab)`).
Instead, OLD `e₀`-rows
are shown to lie in `span(G.rigidityRows)` via the identity
`panelRow(e₀, t₁, t₂) = panelRow(e_b, t₁, t₂) + panelRow(e_a, t₁, t₂)` at `q₀ = q[v ↦ nₐ + n_b]`
(from `panelSupportExtensor_add_smul_right`/`_left` + `hingeRow_sub_hingeRow_eq`). -/
theorem PanelHingeFramework.case_II_realization_all_k [DecidableEq β] [Finite α] [Finite β]
    {n : ℕ} (hk1 : 1 ≤ k) (hn : Graph.bodyBarDim n = screwDim k)
    {c : ℤ} (G : Graph α β) (hfresh : ∃ e₀ : β, e₀ ∉ E(G))
    (hG : G.IsMinimalKDof n c) (hc : 0 < c) (hV3 : 3 ≤ V(G).ncard)
    (htec : G.TwoEdgeConnected)
    (hnoRigid : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n)
    (hIH : ∀ (c' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n c' → V(G').Nonempty →
      V(G').ncard < V(G).ncard →
      (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization k n G') ∧
        HasPanelRealization k n G') :
    PanelHingeFramework.HasGenericFullRankRealization k n G := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  -- Auxiliary bounds: the graph-side `bodyBarDim` floors come from `hn` + the `screwDim`
  -- arithmetic kit (the `d = 3` line discharged `3 ≤ bodyBarDim n` by `omega` on `screwDim 2 = 6`).
  have hD3 : 3 ≤ Graph.bodyBarDim n := hn ▸ three_le_screwDim hk1
  have hD2 : 2 ≤ Graph.bodyBarDim n := le_trans (by norm_num) hD3
  -- G is simple (G0).
  haveI hsimple : G.Simple :=
    Graph.simple_of_isMinimalKDof_of_noRigid hD2 hV3 hG hnoRigid
  haveI hGloop : G.Loopless := hsimple.toLoopless
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
  -- ── Step 3: Fresh edge e₀, set Gab = G.splitOff v a b e₀. ───────────────────────────────────
  obtain ⟨e₀, he₀⟩ := hfresh
  set Gab := G.splitOff v a b e₀ with hGab_def
  -- Gab is simple: use splitOff_simple_of_noRigid with htri vacuously true.
  -- For k > 0, no G-edge f : a-b can exist:
  --  · If |V(G)| ≥ 4: the triangle G[{v,a,b}] is a proper rigid subgraph
  --    (triangle_isProperRigidSubgraph), contradicting hnoRigid.
  --  · If |V(G)| = 3: G is the triangle K₃ and is 0-dof (isKDof_zero_of_triangle),
  --    contradicting hG.1 with k > 0. [hK3_htri, carried as h_no_fab below]
  -- h_no_fab : ∀ f, ¬ G.IsLink f a b
  have h_no_fab : ∀ f : β, ¬ G.IsLink f a b := by
    intro f hf
    by_cases hV4 : 4 ≤ V(G).ncard
    · -- |V(G)| ≥ 4: use triangle_isProperRigidSubgraph + hnoRigid.
      obtain ⟨H, hH⟩ := Graph.triangle_isProperRigidSubgraph hD3 hG_ea hG_eb hf hab hV4
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
      -- But G.IsMinimalKDof n k means G.deficiency n = k > 0. Contradiction.
      exact absurd (hG.1.symm.trans hG0) (by omega)
  haveI hGab_simple : Gab.Simple :=
    Graph.splitOff_simple_of_noRigid heab hG_ea hG_eb hnoRigid
      (fun f hf => False.elim (h_no_fab f hf))
  -- Gab is minimal (k-1)-dof by KT 4.8 (splitOff_isMinimalKDof_of_pos).
  have hGab : Gab.IsMinimalKDof n (c - 1) :=
    Graph.splitOff_isMinimalKDof_of_pos hD3 hV3 hc hab hav hbv haG hbG hvG heab
      hG_ea hG_eb hclv he₀ hG hnoRigid
  -- Gab has fewer vertices: |V(Gab)| < |V(G)|.
  have hGab_lt : V(Gab).ncard < V(G).ncard := by
    rw [hGab_def]; exact Graph.splitOff_vertexSet_ncard_lt hvG
  -- Gab is nonempty (a ∈ V(Gab)).
  have hGab_ne : V(Gab).Nonempty :=
    ⟨a, by rw [hGab_def, Graph.vertexSet_splitOff]; exact ⟨haG, hav⟩⟩
  -- ── Step 4: Apply IH at (k-1, Gab). ─────────────────────────────────────────────────────────
  obtain ⟨Q, hQg, hQgp, hQrank, hQrec, hQalg⟩ :=
    (hIH (c - 1) Gab hGab hGab_ne hGab_lt).1 hGab_simple
  -- Set up the IH normal function q := Q.normal.
  set q : α × Fin (k + 2) → ℝ := fun p => Q.normal p.1 p.2 with hq_def
  -- ── Step 5: Extract hgab (GP at distinct a ≠ b ∈ V(Gab)). ───────────────────────────────────
  have haVGab : a ∈ V(Gab) := ⟨haG, hav⟩
  have hbVGab : b ∈ V(Gab) := ⟨hbG, hbv⟩
  set n_a : Fin (k + 2) → ℝ := fun i => q (a, i) with hn_a
  set n_b : Fin (k + 2) → ℝ := fun i => q (b, i) with hn_b
  have hgab : LinearIndependent ℝ ![n_a, n_b] := by
    have := hQgp a b hab
    simp only [hq_def, hn_a, hn_b] at *
    convert this using 2
  -- ── Step 6: Inhabited α (needed for G.endsOf). ───────────────────────────────────────────────
  haveI : Inhabited α := ⟨v⟩
  set ends := G.endsOf with hendsDef
  -- ── Step 7: Rank lower bound from the IH at Gab. ─────────────────────────────────────────────
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
  have hQfin : Module.finrank ℝ (Submodule.span ℝ
      (PanelHingeFramework.ofNormals Gab Q.ends q).toBodyHinge.rigidityRows)
      = Module.finrank ℝ (Submodule.span ℝ Q.toBodyHinge.rigidityRows) := by
    rw [hQeq]
  rw [hGab.1] at hQrank
  -- hQrank now: (finrank : ℤ) = screwDim k * (|V(Gab)| - 1) - (c - 1)
  -- Convert to the ℕ form for the rank bound.
  -- Represent the IH rank as a natural number N.
  -- We need N : ℕ with N ≤ finrank (span (ofNormals Gab Q.ends q).rigidityRows).
  have hc1 : 0 ≤ c - 1 := by omega
  have hNZ : (screwDim k * (V(Gab).ncard - 1) : ℤ) - (c - 1) ≥ 0 := by
    have h0 : (0 : ℤ) ≤ Module.finrank ℝ (Submodule.span ℝ Q.toBodyHinge.rigidityRows) :=
      Int.natCast_nonneg _
    push_cast [h1Gab] at hQrank ⊢
    linarith [hQrank, h0]
  set N : ℕ := (screwDim k * (V(Gab).ncard - 1) - (c - 1)).toNat with hN_def
  have hN_eq : (N : ℤ) = screwDim k * (V(Gab).ncard - 1) - (c - 1) := by
    rw [hN_def]; exact Int.toNat_of_nonneg hNZ
  have hNrank_q : N ≤ Module.finrank ℝ (Submodule.span ℝ
      (PanelHingeFramework.ofNormals Gab Q.ends q).toBodyHinge.rigidityRows) := by
    rw [hQfin]
    have hle : (N : ℤ) ≤ Module.finrank ℝ (Submodule.span ℝ Q.toBodyHinge.rigidityRows) := by
      rw [hN_eq]; push_cast [h1Gab] at hQrank ⊢; linarith [hQrank]
    exact_mod_cast hle
  -- ── Step 8: Set up q₀ = q[v ↦ n_a + n_b] (t=1 shear). ───────────────────────────────────────
  -- q₀ agrees with q off v; at v it is n_a + n_b.
  set q₀ : α × Fin (k + 2) → ℝ :=
    fun p => if p.1 = v then (n_a + n_b) p.2 else q p with hq₀_def
  have hq₀v : (fun i => q₀ (v, i)) = n_a + n_b := by
    funext i; rw [hq₀_def]; simp
  have hva : v ≠ a := hav.symm
  have hvb : v ≠ b := hbv.symm
  have hq₀a : (fun i => q₀ (a, i)) = n_a := by
    funext i; rw [hq₀_def, hn_a]; simp only [if_neg hva.symm]
  have hq₀b : (fun i => q₀ (b, i)) = n_b := by
    funext i; rw [hq₀_def, hn_b]; simp only [if_neg hvb.symm]
  -- ── Step 9: Transport IH rank bound from q to q₀ (at Gab). ─────────────────────────────────
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
      Submodule.span ℝ (PanelHingeFramework.ofNormals Gab Q.ends q₀).toBodyHinge.rigidityRows
      = Submodule.span ℝ (PanelHingeFramework.ofNormals Gab Q.ends q).toBodyHinge.rigidityRows :=
    BodyHingeFramework.span_rigidityRows_eq_of_infinitesimalMotions_eq _ _ hZeq
  have hN₀ : N ≤ Module.finrank ℝ (Submodule.span ℝ
      (PanelHingeFramework.ofNormals Gab Q.ends q₀).toBodyHinge.rigidityRows) := by
    rw [hspan_eq]; exact hNrank_q
  -- ── Step 10: Transversality of Gab-edges at q₀. ─────────────────────────────────────────────
  -- Gab-hinges avoid v (v ∉ V(Gab)), so q₀ agrees with q at their endpoints.
  have hne_q : ∀ e, Gab.IsLink e (Q.ends e).1 (Q.ends e).2 →
      (PanelHingeFramework.ofNormals Gab Q.ends q).toBodyHinge.supportExtensor e ≠ 0 := by
    intro e he
    apply PanelHingeFramework.supportExtensor_ne_zero_of_isGeneralPosition _ (hQeq ▸ hQgp)
    rw [PanelHingeFramework.ofNormals_ends]
    -- (Q.ends e).1 ≠ (Q.ends e).2: Gab is loopless (from hGab_simple) and Gab.IsLink e at Q.ends.
    haveI : Gab.Loopless := hGab_simple.toLoopless
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
  -- ── Step 11: OLD block (W6e): N independent Gab-linking rows at q₀. ─────────────────────────
  set FG := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge with hFG_def
  set FGab := (PanelHingeFramework.ofNormals Gab Q.ends q₀).toBodyHinge with hFGab_def
  have hends_Gab : ∀ e u w, Gab.IsLink e u w →
      Gab.IsLink e (Q.ends e).1 (Q.ends e).2 := hQ_ends_Gab
  obtain ⟨so, hso_link, hso_card, hso_indep⟩ :=
    FGab.exists_independent_panelRow_subfamily_of_le_finrank (ends := Q.ends)
      (by simpa [hFGab_def] using hends_Gab) (by simpa [hFGab_def] using hne₀)
      (by simpa [hFGab_def] using hN₀)
  -- ── Step 12: e₀-row identity at q₀. ─────────────────────────────────────────────────────────
  -- At q₀ = q[v ↦ n_a + n_b]:
  --   C(e_b) = panelSupportExtensor(n_a + n_b, n_b) = panelSupportExtensor(n_a, n_b)
  --     [add_smul_right]
  --   C(e_a) = panelSupportExtensor(n_a + n_b, n_a) = (-1) • panelSupportExtensor(n_a, n_b)
  --     [add_smul_left]
  -- For e₀, ends e₀ = (a, b) or (b, a) from hQrec at Gab.IsLink e₀ a b.
  -- We need to unify using G.endsOf.
  -- At G.endsOf, the ends of e_a and e_b are recorded from G.endsOf:
  have hends_G : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2 := by
    rw [hendsDef]; exact fun e _ _ h => G.isLink_endsOf h.edge_mem
  -- ends e_a = (v,a) or (a,v); ends e_b = (v,b) or (b,v).
  have hends_ea : ends e_a = (v, a) ∨ ends e_a = (a, v) := by
    simp only [hendsDef]; exact G.endsOf_eq_or_swap hG_ea
  have hends_eb : ends e_b = (v, b) ∨ ends e_b = (b, v) := by
    simp only [hendsDef]; exact G.endsOf_eq_or_swap hG_eb
  -- Compute the extensors for FG at e_a, e_b.
  -- hFG_ea: FG.supportExtensor e_a = (-1) • panelSupportExtensor n_a n_b
  --   (case (v,a): panelSupportExtensor (n_a+n_b) n_a = (-1) • panelSupportExtensor n_a n_b
  --     via add_smul_left)
  --   (case (a,v): panelSupportExtensor n_a (n_a+n_b); via panelSupportExtensor_swap then
  --     add_smul_left: = (1) • ...)
  -- We handle both cases; the result may be ±1 • panelSupportExtensor n_a n_b.
  -- For hne_G we only need ≠ 0; for he₀_rows_mem we need the exact sign.
  -- We'll prove the statement using the actual orientation.
  -- FG.graph = G (used below for panelRow_mem_rigidityRows).
  have hFG_graph : FG.graph = G := by
    rw [hFG_def, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]
  -- Compute FG.supportExtensor for e_a and e_b at each possible orientation.
  -- hFG_ea: FG.supportExtensor e_a = (-1) • panelSupportExtensor n_a n_b  (when ends e_a = (v,a))
  --   OR = panelSupportExtensor n_a n_b  (when ends e_a = (a,v))
  have hFG_ea : FG.supportExtensor e_a = (-1 : ℝ) • panelSupportExtensor n_a n_b ∨
      FG.supportExtensor e_a = panelSupportExtensor n_a n_b := by
    rcases hends_ea with h | h
    · left
      rw [hFG_def, PanelHingeFramework.toBodyHinge_supportExtensor,
        PanelHingeFramework.ofNormals_ends,
        PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal, h, hq₀v, hq₀a]
      rw [show n_a + n_b = n_a + (1 : ℝ) • n_b from by rw [one_smul]]
      exact panelSupportExtensor_add_smul_left n_a n_b 1
    · right
      rw [hFG_def, PanelHingeFramework.toBodyHinge_supportExtensor,
        PanelHingeFramework.ofNormals_ends,
        PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal, h, hq₀a, hq₀v]
      -- goal: panelSupportExtensor n_a (n_a + n_b) = panelSupportExtensor n_a n_b
      -- panelSupportExtensor n_a (n_a + n_b)
      --   = -panelSupportExtensor (n_a + n_b) n_a
      --     [panelSupportExtensor_swap with n₂=n_a, n₁=n_a+n_b]
      --   = -panelSupportExtensor (n_a + 1•n_b) n_a
      --   = -(-1 • panelSupportExtensor n_a n_b)   [panelSupportExtensor_add_smul_left]
      --   = panelSupportExtensor n_a n_b
      rw [panelSupportExtensor_swap (n_a + n_b) n_a,
        show n_a + n_b = n_a + (1 : ℝ) • n_b from by rw [one_smul],
        panelSupportExtensor_add_smul_left]
      -- goal: -(-1 • panelSupportExtensor n_a n_b) = panelSupportExtensor n_a n_b
      module
  -- hFG_eb: FG.supportExtensor e_b = panelSupportExtensor n_a n_b  (when ends e_b = (v,b))
  --                                 OR = -panelSupportExtensor n_a n_b (when ends e_b = (b,v))
  have hFG_eb : FG.supportExtensor e_b = panelSupportExtensor n_a n_b ∨
      FG.supportExtensor e_b = -panelSupportExtensor n_a n_b := by
    rcases hends_eb with h | h
    · left
      rw [hFG_def, PanelHingeFramework.toBodyHinge_supportExtensor,
        PanelHingeFramework.ofNormals_ends,
        PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal, h, hq₀v, hq₀b]
      rw [show n_a + n_b = n_a + (1 : ℝ) • n_b from by rw [one_smul]]
      -- goal: panelSupportExtensor (n_a + 1•n_b) n_b = panelSupportExtensor n_a n_b
      exact panelSupportExtensor_add_smul_right n_a n_b 1
    · right
      rw [hFG_def, PanelHingeFramework.toBodyHinge_supportExtensor,
        PanelHingeFramework.ofNormals_ends,
        PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal, h, hq₀b, hq₀v]
      -- goal: panelSupportExtensor n_b (n_a + n_b) = -panelSupportExtensor n_a n_b
      -- panelSupportExtensor n_b (n_a + n_b)
      --   = -panelSupportExtensor (n_a + n_b) n_b  [swap with n₁=n_a+n_b, n₂=n_b]
      --   = -panelSupportExtensor (n_a + 1•n_b) n_b
      --   = -panelSupportExtensor n_a n_b            [add_smul_right]
      rw [panelSupportExtensor_swap (n_a + n_b) n_b,
        show n_a + n_b = n_a + (1 : ℝ) • n_b from by rw [one_smul],
        panelSupportExtensor_add_smul_right]
  -- e₀ in Gab links a and b; ends e₀ in G is (a, b) or (b, a).
  have he₀ab : Gab.IsLink e₀ a b := by
    rw [hGab_def, Graph.splitOff_isLink]
    exact Or.inr ⟨rfl, hav, hbv, haG, hbG, Or.inl ⟨rfl, rfl⟩⟩
  -- ── Step 13: e₀-rows in span(FG.rigidityRows). ───────────────────────────────────────────────
  -- FGab.panelRow Q.ends (e₀, t₁, t₂)
  --   = hingeRow (Q.ends e₀).1 (Q.ends e₀).2 (annihRow C(e₀) t₁ t₂).
  -- Case Q.ends e₀ = (a, b): C(e₀) = panelSupportExtensor n_a n_b,
  --   hingeRow a b ρ = hingeRow v b ρ - hingeRow v a ρ.
  -- Case Q.ends e₀ = (b, a): C(e₀) = panelSupportExtensor n_b n_a = -panelSupportExtensor n_a n_b,
  --   annihRow (-C) = -annihRow C, hingeRow b a (-ρ) = hingeRow a b ρ via hingeRow_swap.
  --   Either way the row reduces to a sum/difference of FG-rows at e_a and e_b.
  -- Helpful: FG.panelRow ends (e_b, t₁, t₂) = hingeRow v b ρ regardless of orientation:
  --   • (v, b): FG.panelRow = hingeRow v b (annihRow C_b t₁ t₂)
  --       with C_b = panelSupportExtensor n_a n_b, = ρ. ✓
  --   • (b, v): FG.panelRow = hingeRow b v (annihRow C_b t₁ t₂)
  --       with C_b = -panelSupportExtensor n_a n_b,
  --       = hingeRow b v (-ρ) = hingeRow v b ρ by hingeRow_swap.
  -- Similarly FG.panelRow ends (e_a, t₁, t₂) = -hingeRow v a ρ in both orientations.
  -- Helper for the universal FG-row membership (needed regardless of ends orientation):
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
    rcases hends_eb with hb | hb
    · -- ends e_b = (v, b): FG.supportExtensor e_b = panelSupportExtensor n_a n_b
      rw [FG.panelRow_eq_hingeRow_annihRow_of_ends ends hb]
      -- goal: hingeRow v b (annihRow (panelSupportExtensor n_a n_b) t₁ t₂)
      --       = hingeRow v b (annihRow (FG.supportExtensor e_b) t₁ t₂)
      -- suffices: panelSupportExtensor n_a n_b = FG.supportExtensor e_b
      have hCb_eq : panelSupportExtensor n_a n_b = FG.supportExtensor e_b := by
        rw [hFG_def, PanelHingeFramework.toBodyHinge_supportExtensor,
          PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal,
          PanelHingeFramework.ofNormals_normal, hb, hq₀v, hq₀b,
          show n_a + n_b = n_a + (1 : ℝ) • n_b from by rw [one_smul]]
        exact (panelSupportExtensor_add_smul_right n_a n_b 1).symm
      rw [hCb_eq]
    · -- ends e_b = (b, v): FG.supportExtensor e_b = -panelSupportExtensor n_a n_b
      --   FG.panelRow ends (e_b, t₁, t₂) = hingeRow b v (annihRow (-C) t₁ t₂)
      --     = hingeRow b v (-ρ) = hingeRow v b ρ by hingeRow_swap + neg_neg.
      rw [FG.panelRow_eq_hingeRow_annihRow_of_ends ends hb]
      have hCb : FG.supportExtensor e_b = -(panelSupportExtensor n_a n_b) := by
        rw [hFG_def, PanelHingeFramework.toBodyHinge_supportExtensor,
          PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal,
          PanelHingeFramework.ofNormals_normal, hb, hq₀b, hq₀v,
          panelSupportExtensor_swap (n_a + n_b) n_b,
          show n_a + n_b = n_a + (1 : ℝ) • n_b from by rw [one_smul],
          panelSupportExtensor_add_smul_right]
      rw [hCb]
      have hann : annihRow (-(panelSupportExtensor n_a n_b)) t₁ t₂
          = -(annihRow (panelSupportExtensor n_a n_b) t₁ t₂) := by
        rw [show -(panelSupportExtensor n_a n_b) = (-1 : ℝ) • panelSupportExtensor n_a n_b
              from (by module), annihRow_smul]
        module
      symm; rw [hann, BodyHingeFramework.hingeRow_swap, neg_neg]
  -- -hingeRow v a ρ = FG.panelRow ends (e_a, t₁, t₂) in both orientations.
  have hrow_a_eq : ∀ (t₁ t₂ : Set.powersetCard (Fin (k + 2)) k),
      -(BodyHingeFramework.hingeRow v a (annihRow (panelSupportExtensor n_a n_b) t₁ t₂))
        = FG.panelRow ends (e_a, t₁, t₂) := by
    intro t₁ t₂
    rcases hends_ea with ha | ha
    · -- ends e_a = (v, a): FG.supportExtensor e_a = -1 • panelSupportExtensor n_a n_b
      --   FG.panelRow ends (e_a, t₁, t₂) = hingeRow v a (annihRow (-C) t₁ t₂) = -hingeRow v a ρ.
      rw [FG.panelRow_eq_hingeRow_annihRow_of_ends ends ha]
      have hCa : FG.supportExtensor e_a = (-1 : ℝ) • panelSupportExtensor n_a n_b := by
        rw [hFG_def, PanelHingeFramework.toBodyHinge_supportExtensor,
          PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal,
          PanelHingeFramework.ofNormals_normal, ha, hq₀v, hq₀a,
          show n_a + n_b = n_a + (1 : ℝ) • n_b from by rw [one_smul]]
        exact panelSupportExtensor_add_smul_left n_a n_b 1
      -- goal: -(hingeRow v a ρ)
      --   = hingeRow v a (annihRow ((-1:ℝ) • panelSupportExtensor n_a n_b) t₁ t₂)
      -- = hingeRow v a ((-1:ℝ) • ρ)  [annihRow_smul]
      -- = (-1:ℝ) • hingeRow v a ρ    [map_smul via dualMap linearity]
      -- = -(hingeRow v a ρ)            [neg_one_smul]
      rw [hCa, annihRow_smul]
      simp only [BodyHingeFramework.hingeRow_eq_dualMap, map_smul]
      -- goal: -(screwDiff v a).dualMap ρ = -1 • (screwDiff v a).dualMap ρ
      module
    · -- ends e_a = (a, v): FG.supportExtensor e_a = panelSupportExtensor n_a n_b
      --   FG.panelRow ends (e_a, t₁, t₂) = hingeRow a v ρ = hingeRow v a (-ρ) = -(hingeRow v a ρ)
      --   by hingeRow_swap + map_neg.
      rw [FG.panelRow_eq_hingeRow_annihRow_of_ends ends ha]
      have hCa : FG.supportExtensor e_a = panelSupportExtensor n_a n_b := by
        rw [hFG_def, PanelHingeFramework.toBodyHinge_supportExtensor,
          PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal,
          PanelHingeFramework.ofNormals_normal, ha, hq₀a, hq₀v,
          panelSupportExtensor_swap (n_a + n_b) n_a,
          show n_a + n_b = n_a + (1 : ℝ) • n_b from by rw [one_smul],
          panelSupportExtensor_add_smul_left]
        -- goal: -(-1 • panelSupportExtensor n_a n_b) = panelSupportExtensor n_a n_b
        module
      -- goal: -(hingeRow v a (annihRow C t₁ t₂)) = hingeRow a v (annihRow C t₁ t₂)
      -- Expand pointwise: both sides equal -(r(Sv - Sa)), where r = annihRow C t₁ t₂.
      rw [hCa]
      set r := annihRow (panelSupportExtensor n_a n_b) t₁ t₂
      -- goal: -(hingeRow v a r) = hingeRow a v r
      apply LinearMap.ext
      intro S
      simp only [LinearMap.neg_apply, BodyHingeFramework.hingeRow_apply]
      -- goal: -(r (S v - S a)) = r (S a - S v)
      rw [← neg_sub, map_neg, neg_neg]
  -- ── Step 14: e₀-rows in span(FG.rigidityRows). ───────────────────────────────────────────────
  have he₀_rows_mem : ∀ (t₁ t₂ : Set.powersetCard (Fin (k + 2)) k),
      FGab.panelRow Q.ends (e₀, t₁, t₂) ∈ Submodule.span ℝ FG.rigidityRows := by
    intro t₁ t₂
    -- Case-split on Q.ends e₀ first, so panelRow_eq_hingeRow_annihRow_of_ends gets an exact value.
    rcases hrec' e₀ a b he₀ab with he | he
    · -- Q.ends e₀ = (a, b): FGab.supportExtensor e₀ = panelSupportExtensor n_a n_b.
      have hC : FGab.supportExtensor e₀ = panelSupportExtensor n_a n_b := by
        rw [hFGab_def, PanelHingeFramework.toBodyHinge_supportExtensor,
          PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal,
          PanelHingeFramework.ofNormals_normal, he]
        simp only [hq₀a, hq₀b]
      rw [FGab.panelRow_eq_hingeRow_annihRow_of_ends Q.ends he t₁ t₂, hC]
      -- goal: hingeRow a b ρ ∈ span(FG.rigidityRows),
      --   where ρ = annihRow (panelSupportExtensor n_a n_b) t₁ t₂
      set ρ := annihRow (panelSupportExtensor n_a n_b) t₁ t₂ with hρ_def
      -- hingeRow a b ρ = hingeRow v b ρ - hingeRow v a ρ  [hingeRow_sub_hingeRow_eq]
      -- = FG.panelRow ends (e_b, ...) + FG.panelRow ends (e_a, ...)  [hrow_b_eq + hrow_a_eq]
      have hrow : BodyHingeFramework.hingeRow a b ρ
          = BodyHingeFramework.hingeRow v b ρ - BodyHingeFramework.hingeRow v a ρ := by
        -- hingeRow v b ρ - hingeRow a b ρ = hingeRow v a ρ  [hingeRow_sub_hingeRow_eq]
        -- so hingeRow a b ρ = hingeRow v b ρ - hingeRow v a ρ
        have h := BodyHingeFramework.hingeRow_sub_hingeRow_eq v a b ρ
        rw [← h, sub_sub_self]
      rw [hrow, sub_eq_add_neg, hrow_b_eq t₁ t₂, hrow_a_eq t₁ t₂]
      exact Submodule.add_mem _ (Submodule.subset_span (hFG_eb_mem t₁ t₂))
        (Submodule.subset_span (hFG_ea_mem t₁ t₂))
    · -- Q.ends e₀ = (b, a): FGab.supportExtensor e₀ = panelSupportExtensor n_b n_a.
      have hC : FGab.supportExtensor e₀ = panelSupportExtensor n_b n_a := by
        rw [hFGab_def, PanelHingeFramework.toBodyHinge_supportExtensor,
          PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal,
          PanelHingeFramework.ofNormals_normal, he]
        simp only [hq₀b, hq₀a]
      rw [FGab.panelRow_eq_hingeRow_annihRow_of_ends Q.ends he t₁ t₂, hC]
      -- panelSupportExtensor n_b n_a = -panelSupportExtensor n_a n_b.
      -- annihRow (-C) = -annihRow C, hingeRow b a (-ρ) = hingeRow a b ρ by hingeRow_swap + neg_neg.
      -- goal: hingeRow b a (annihRow (panelSupportExtensor n_b n_a) t₁ t₂) ∈ span(FG.rigidityRows)
      have hCba : panelSupportExtensor n_b n_a = -(panelSupportExtensor n_a n_b) :=
        panelSupportExtensor_swap n_a n_b
      set ρ := annihRow (panelSupportExtensor n_a n_b) t₁ t₂ with hρ_def
      have hrow : BodyHingeFramework.hingeRow b a (annihRow (panelSupportExtensor n_b n_a) t₁ t₂)
          = BodyHingeFramework.hingeRow v b ρ - BodyHingeFramework.hingeRow v a ρ := by
        have hann : annihRow (-(panelSupportExtensor n_a n_b)) t₁ t₂
            = -(annihRow (panelSupportExtensor n_a n_b) t₁ t₂) := by
          rw [show -(panelSupportExtensor n_a n_b) = (-1 : ℝ) • panelSupportExtensor n_a n_b
                from (by module), annihRow_smul]
          module
        rw [hCba, hann, BodyHingeFramework.hingeRow_swap, neg_neg]
        -- goal: hingeRow a b ρ = hingeRow v b ρ - hingeRow v a ρ (same as the (a,b) branch)
        have h := BodyHingeFramework.hingeRow_sub_hingeRow_eq v a b ρ
        rw [← h, sub_sub_self]
      rw [hrow, sub_eq_add_neg, hrow_b_eq t₁ t₂, hrow_a_eq t₁ t₂]
      exact Submodule.add_mem _ (Submodule.subset_span (hFG_eb_mem t₁ t₂))
        (Submodule.subset_span (hFG_ea_mem t₁ t₂))
  -- ── Step 15: Non-e₀ OLD rows: translate from FGab (Q.ends) to FG (G.endsOf). ────────────────
  -- For a non-e₀ Gab-link (e, u, w): G.IsLink e u w (from splitOff_isLink) and
  -- Q.ends e = (u, w) or (w, u) by hrec'. The extensor C(e) at q₀ agrees at both selectors
  -- since q₀ agrees with q at u, w (neither is v, since Gab-links ≠ e₀ avoid v).
  have hGab_to_G_link : ∀ e u w, Gab.IsLink e u w → e ≠ e₀ → G.IsLink e u w := by
    intro e u w he hne
    rw [hGab_def, Graph.splitOff_isLink] at he
    rcases he with ⟨_, hGlink, _, _⟩ | ⟨rfl, _⟩
    · exact hGlink
    · exact absurd rfl hne
  -- For the OLD block rows (via Q.ends), show each in span(FG.rigidityRows).
  have hso_span : ∀ i : so, FGab.panelRow Q.ends (i : β × _ × _)
      ∈ Submodule.span ℝ FG.rigidityRows := by
    rintro ⟨⟨e, t₁, t₂⟩, hi⟩
    have hlink := hso_link _ hi
    change FGab.panelRow Q.ends (e, t₁, t₂) ∈ Submodule.span ℝ FG.rigidityRows
    by_cases he₀e : e = e₀
    · subst he₀e; exact he₀_rows_mem t₁ t₂
    · -- e ≠ e₀: e is a G-link, and panelRow agrees at FGab and a suitable F.
      -- G.IsLink e (Q.ends e).1 (Q.ends e).2:
      have hGlink_e : G.IsLink e (Q.ends e).1 (Q.ends e).2 := by
        rcases hrec' e _ _ hlink with he | he <;> rw [he]
        · exact hGab_to_G_link e _ _ hlink he₀e
        · exact (hGab_to_G_link e _ _ hlink he₀e).symm
      -- The extensor at FGab and FG agree for this edge:
      -- FGab.supportExtensor e = panelSupportExtensor(q₀ (Q.ends e).1, q₀ (Q.ends e).2)
      -- FG.supportExtensor e = panelSupportExtensor(q₀ (ends e).1, q₀ (ends e).2)
      -- These may differ if Q.ends e ≠ ends e (they're related by a swap).
      -- We need to show FGab.panelRow Q.ends (e, t₁, t₂) ∈ span(FG.rigidityRows).
      -- The row is hingeRow (Q.ends e).1 (Q.ends e).2 (annihRow C_FGab t₁ t₂).
      -- There's a corresponding FG.panelRow ends (e, t₁, t₂) if ends e = Q.ends e.
      -- If ends e = (Q.ends e).2, (Q.ends e).1 (swapped), use hingeRow swap + neg.
      -- Regardless, the row is a scalar multiple of a G-rigidityRow.
      -- FGab.panelRow Q.ends (e, t₁, t₂) = hingeRow (Q.ends e).1 (Q.ends e).2 ρ_FGab
      -- where ρ_FGab = annihRow (FGab.supportExtensor e) t₁ t₂.
      -- This is in FG.rigidityRows via hingeRow_mem_rigidityRows:
      --   • hGlink_e : FG.graph.IsLink e (Q.ends e).1 (Q.ends e).2 (since FG.graph = G)
      --   • ρ_FGab ∈ FG.hingeRowBlock e: annihRow (FGab.supportExtensor e) t₁ t₂ vanishes at
      --     FG.supportExtensor e because FGab.supportExtensor e = ±FG.supportExtensor e
      --     (by endsOf_eq_or_swap + panelSupportExtensor_swap) and annihRow_apply_self.
      rw [FGab.panelRow_eq_hingeRow_annihRow_of_ends Q.ends (by rfl) t₁ t₂]
      apply Submodule.subset_span
      apply FG.hingeRow_mem_rigidityRows hGlink_e
      -- ρ_FGab ∈ FG.hingeRowBlock e: need
      --   annihRow(FGab.supportExtensor e)(FG.supportExtensor e) = 0
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
        rw [hse_swap, map_neg, hFGab_se, annihRow_apply_self, neg_zero]
  -- ── hso_span established. (The OLD-block span-transport discharge for Brick A's `hold_span`.) ─
  -- ── Step 12 (cont): Compute that N = D*(|V(G)|-1) - c - (D-1). ───────────────────────────────
  -- N = D*(|V(Gab)|-1) - (c-1) = D*(|V(G)|-2) - c + 1.
  -- Required rank for G: D*(|V(G)|-1) - c.
  -- New block adds D-1 rows from the e_b hinge (|V(Gab)| = |V(G)|-1, so |V(G)| - 1 ≥ 2).
  have hVGab_card : V(Gab).ncard = V(G).ncard - 1 := by
    rw [hGab_def, Graph.vertexSet_splitOff]
    exact Set.ncard_diff_singleton_of_mem hvG
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
  -- Cast to ℕ: N + (D-1) ≤ finrank(span(FG.rigidityRows)) + (D-1), so total is computable.
  -- But first: show that (D-1)-many additional rows from e_b lift the bound.
  -- NEW block from e_b (v-b hinge at q₀): D-1 independent rows at FG.
  -- FG.supportExtensor e_b = panelSupportExtensor n_a n_b ≠ 0 (since hgab).
  have hFG_eb_ne : FG.supportExtensor e_b ≠ 0 := by
    rcases G.endsOf_eq_or_swap hG_eb with h | h
    · simp only [← hendsDef] at h
      rw [hFG_def, PanelHingeFramework.toBodyHinge_supportExtensor,
        PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal,
        PanelHingeFramework.ofNormals_normal, h, hq₀v, hq₀b,
        show n_a + n_b = n_a + (1 : ℝ) • n_b from by rw [one_smul],
        panelSupportExtensor_add_smul_right]
      exact (panelSupportExtensor_ne_zero_iff n_a n_b).mpr hgab
    · simp only [← hendsDef] at h
      rw [hFG_def, PanelHingeFramework.toBodyHinge_supportExtensor,
        PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal,
        PanelHingeFramework.ofNormals_normal, h, hq₀b, hq₀v, panelSupportExtensor_swap,
        show n_a + n_b = n_a + (1 : ℝ) • n_b from by rw [one_smul],
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
  -- The old rows (from FGab, now in FG.rigidityRows by hso_span) vanish at update 0 v x
  -- (their Gab-links avoid v, since v ∉ V(Gab)).
  -- OLD block rows (FGab.panelRow Q.ends at so): lie in span(FG.rigidityRows) by hso_span,
  -- vanish at update 0 v x (hold below), and are independently supported by hso_indep.
  -- NEW block rows (FG.panelRow ends at sn): span v's screw column (hnewpin).
  -- These are independent by linearIndependent_sum_pinned_block.
  -- We use FGab.panelRow Q.ends for the old block throughout (not FG.panelRow Q.ends):
  -- hso_span already places FGab rows in span(FG.rigidityRows), and hso_indep is for FGab rows.
  -- The vanishing-at-v property hold holds for FGab.panelRow Q.ends by the same proof
  -- (it only uses the endpoint vertices from Q.ends, which are in V(Gab) and avoid v).
  have hold : ∀ (j : so) (x : ScrewSpace k),
      FGab.panelRow Q.ends (j : β × _ × _)
        (Function.update (0 : α → ScrewSpace k) v x) = 0 := by
    rintro ⟨i, hi⟩ x
    have hlink := hso_link _ hi
    -- (Q.ends i.1).1 ≠ v and (Q.ends i.1).2 ≠ v (since they're in V(Gab), v ∉ V(Gab))
    have h₁ : (Q.ends i.1).1 ≠ v := by
      intro h
      exact hvVGab (h ▸ (hQ_ends_Gab i.1 _ _ hlink).left_mem)
    have h₂ : (Q.ends i.1).2 ≠ v := by
      intro h
      exact hvVGab (h ▸ (hQ_ends_Gab i.1 _ _ hlink).right_mem)
    rw [BodyHingeFramework.panelRow, BodyHingeFramework.hingeRow_apply,
      Function.update_of_ne h₁, Function.update_of_ne h₂,
      Pi.zero_apply, Pi.zero_apply, sub_zero, map_zero]
  -- ── Block-triangular independence: NEW (sn) + OLD (so) at FG. ──────────────────────────────────
  -- NEW block (sn) is independent through v's screw column (hnewpin); OLD block (so) vanishes
  -- at update 0 v x (hold) and is independently supported (hso_indep_FG).
  -- sn rows use FG.panelRow ends (via e_b), so rows use FG.panelRow Q.ends.
  -- linearIndependent_sum_pinned_block combines them.
  have hnewpin_eb : LinearIndependent ℝ (fun i : sn =>
      (FG.panelRow ends (i : β × _ × _)).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v)) := by
    rcases hends_eb with h | h
    · rw [h] at hnewpin; simpa using hnewpin
    · -- ends e_b = (b, v), so v = (ends e_b).2, not .1; need to adjust hnewpin.
      -- hnewpin was for (ends e_b).1 ≠ (ends e_b).2, which is b ≠ v.
      -- linearIndependent_panelRow_comp_single_of_edge gives independence through (ends e_b).1 = b.
      -- But linearIndependent_sum_pinned_block needs independence through v = (ends e_b).2.
      -- Use that e_b-rows also vanish at update 0 v' x for v' ≠ v = (ends e_b).2,
      -- or rephrase the new block's pin at v.
      -- Actually linearIndependent_panelRow_comp_single_of_edge pins at (ends e_b).1.
      -- If (ends e_b) = (b, v), then pin is at b, not v. Need pin at v.
      -- Alternative: use the fact that e_b-rows span the same space as their reflection.
      rw [h] at hnewpin
      -- hnewpin : LinearIndependent ℝ (fun i : sn => (FG.panelRow ends (i: β×_×_)).comp (single b))
      -- We need independence through v, not b. Both are endpoints of e_b.
      -- The e_b-block is the same regardless of orientation.
      -- Use that FG.panelRow ends (e_b, t₁, t₂) = ±FG.panelRow ends[swap(e_b)] (e_b, t₁, t₂).
      -- Actually panelRow ends (e, t₁, t₂) = hingeRow (ends e).1 (ends e).2 (annihRow C t₁ t₂).
      -- For ends e_b = (b, v): = hingeRow b v (annihRow C t₁ t₂).
      -- (hingeRow b v r).comp (single v) x = (hingeRow b v r) (update 0 v x)
      --   = r (update 0 v x).b - r (update 0 v x).v = -r x.
      -- So (FG.panelRow ends (e_b, t₁, t₂)).comp (single v) = neg of the b-pin.
      -- The b-pin family is LI (hnewpin); negation preserves LI.
      -- This requires BodyHingeFramework.linearIndependent_panelRow_comp_single_of_edge to apply
      -- to BOTH endpoints. Let me use the alternative:
      -- Since (ends e_b) = (b, v), (ends e_b).1 = b ≠ v = (ends e_b).2.
      -- hnewpin shows pin at b. We can derive pin at v by:
      -- (FG.panelRow ends (e_b, t₁, t₂)).comp (single v) s
      --   = FG.panelRow ends (e_b, t₁, t₂) (update 0 v s)
      --   = hingeRow b v (annihRow C t₁ t₂) (update 0 v s)
      --   = (annihRow C t₁ t₂) ((update 0 v s) b - (update 0 v s) v)
      --   = (annihRow C t₁ t₂) (0 - s) = -(annihRow C t₁ t₂ s).
      -- So (FG.panelRow ends (e_b, t₁, t₂)).comp (single v)
      --   = -(FG.panelRow ends (e_b, t₁, t₂)).comp (single b).
      -- Thus the v-pin family = neg of the b-pin family, and neg preserves LI.
      have : (fun i : sn => (FG.panelRow ends (i : β × _ × _)).comp
            (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v)) =
          (fun i : sn => -(FG.panelRow ends (i : β × _ × _)).comp
            (LinearMap.single ℝ (fun _ : α => ScrewSpace k) b)) := by
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
  -- ── Total rank bound via Brick A (`le_finrank_span_rigidityRows_of_pinned_placement`). ─────────
  -- The NEW block (sn, the e_b hinge through v's screw column, `hnewpin_eb`) + the OLD block (so,
  -- the IH's N Gab-rows, vanishing at v by `hold`, in `span FG.rigidityRows` by `hso_span`) feed
  -- the shared span-transport pinned-placement brick: `Nat.card sn + Nat.card so ≤ finrank`. With
  -- `hsn_card : Nat.card sn = D−1`, `hso_card : Nat.card so = N`, and
  -- `hNpD : N + (D−1) = D(|V|−1)−k`, this is the required ℤ rank lower bound for G.
  have hrank_lb : screwDim k * ((V(G).ncard : ℤ) - 1) - c ≤
      Module.finrank ℝ ↥(Submodule.span ℝ FG.rigidityRows) := by
    haveI : Fintype sn := Fintype.ofFinite sn
    haveI : Fintype so := Fintype.ofFinite so
    -- Name the NEW (e_b, pinned through v) and OLD (so, the IH's N Gab-rows) blocks as fvars so the
    -- brick application unifies against opaque families rather than the heavy `ofNormals` lambdas.
    set rn : sn → Module.Dual ℝ (α → ScrewSpace k) :=
      fun i => FG.panelRow ends (i : β × _ × _) with hrn
    set ro : so → Module.Dual ℝ (α → ScrewSpace k) :=
      fun i => FGab.panelRow Q.ends (i : β × _ × _) with hro
    -- The NEW (e_b) rows are literal `FG.panelRow`s, hence in `span FG.rigidityRows` (`hnew_span`).
    have hnew_span : ∀ i : sn, rn i ∈ Submodule.span ℝ FG.rigidityRows := by
      rintro ⟨i, hi⟩
      refine Submodule.subset_span (FG.panelRow_mem_rigidityRows ?_)
      rw [hsn_e _ hi]
      rcases hends_eb with h | h <;> rw [h]
      · exact hG_eb
      · exact hG_eb.symm
    -- Brick A: `Nat.card sn + Nat.card so ≤ finrank`.
    have hbrick : Nat.card sn + Nat.card so ≤
        Module.finrank ℝ ↥(Submodule.span ℝ FG.rigidityRows) :=
      BodyHingeFramework.le_finrank_span_rigidityRows_of_pinned_placement FG (v := v)
        (rn := rn) (ro := ro) hold hnewpin_eb hso_indep hnew_span hso_span
    -- `Nat.card sn + Nat.card so = (D−1) + N`; with `hNpD` this is the ℤ bound.
    rw [hsn_card, hso_card] at hbrick
    rw [← hNpD]
    -- hbrick : (D−1) + N ≤ finrank ; goal (ℤ) : ↑N + (↑D − 1) ≤ ↑finrank
    -- `1 ≤ screwDim k` (`one_le_screwDim`) lets the ℕ-`(D−1)` cast bridge to the ℤ-`(↑D − 1)`.
    have h1D : 1 ≤ screwDim k := one_le_screwDim
    have hbrick' : (N : ℤ) + ((screwDim k : ℤ) - 1) ≤
        Module.finrank ℝ ↥(Submodule.span ℝ FG.rigidityRows) := by
      have := Nat.add_comm (screwDim k - 1) N ▸ hbrick
      zify [h1D] at this
      linarith [this]
    exact hbrick'
  -- ── Apply exists_rankPolynomial_of_le_finrank_linking to transfer to generic q. ────────────────
  -- hN: D*(|V(G)|-1) - c ≤ finrank(span FG.rigidityRows). Convert to ℕ.
  have h1V : 1 ≤ V(G).ncard := by
    exact (Set.ncard_pos (Set.toFinite _)).2 ⟨v, hvG⟩
  have hD1 : 1 ≤ screwDim k := one_le_screwDim
  have hrank_lb_nat : (screwDim k * (V(G).ncard - 1) - c.toNat) ≤
      Module.finrank ℝ (Submodule.span ℝ FG.rigidityRows) := by
    -- First: N + (D-1) ≤ finrank (ℕ) from hrank_lb via hNpD.
    have hbound : N + (screwDim k - 1) ≤ Module.finrank ℝ ↥(Submodule.span ℝ FG.rigidityRows) := by
      have hrank_lb_Z := hrank_lb
      rw [← hNpD] at hrank_lb_Z
      exact_mod_cast hrank_lb_Z
    -- `D*(V-1) - c.toNat = N + (D-1)` (ℕ) by the shared rank-equation cast bridge.
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
  -- ── Assembly: HasGenericFullRankRealization k n G. ─────────────────────────────────────────────
  -- Use exists_rankPolynomial_of_le_finrank_linking to transfer the rank lower bound to a
  -- generic q'. Then combine with GP polynomial and algebraic independence.
  obtain ⟨Q_rk, hQ_rk0, hQ_rkrat, hQ_rk⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_le_finrank_linking G ends hends_G hne_G
      hrank_lb_nat
  obtain ⟨Q_gp, hQ_gp_ne, hQ_gprat, hQ_gp⟩ :=
    exists_generalPosition_polynomial (k := k) G ends
  have hQ_rk_ne : Q_rk ≠ 0 := fun h => hQ_rk0 (by rw [h, map_zero])
  have hQ_gp_ne' : Q_gp ≠ 0 := by
    obtain ⟨f, hf⟩ := Countable.exists_injective_nat α
    exact fun h => hQ_gp_ne (fun a => (f a : ℝ))
      (fun a b hab => hf (Nat.cast_injective hab)) (by rw [h, map_zero])
  obtain ⟨q', _, halg⟩ := exists_injective_algebraicIndependent_real (α × Fin (k + 2))
  have hq'_rk : MvPolynomial.eval q' Q_rk ≠ 0 :=
    MvPolynomial.eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent halg hQ_rkrat hQ_rk_ne
  have hq'_gp : MvPolynomial.eval q' Q_gp ≠ 0 :=
    MvPolynomial.eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent halg hQ_gprat hQ_gp_ne'
  have hgp' : (PanelHingeFramework.ofNormals G ends q').IsGeneralPosition := hQ_gp q' hq'_gp
  -- Rank lower bound at q': from rank polynomial.
  have hrankge_q' : screwDim k * (V(G).ncard - 1) - c.toNat ≤
      Module.finrank ℝ (Submodule.span ℝ
        (PanelHingeFramework.ofNormals G ends q').toBodyHinge.rigidityRows) := hQ_rk q' hq'_rk
  -- Rank upper bound at q': B2 via GP.
  have hFG'_graph : (PanelHingeFramework.ofNormals G ends q').toBodyHinge.graph = G := by
    rw [PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]
  have hVGne : V(G).Nonempty := ⟨v, hvG⟩
  have hne_q' : ∀ e u w, G.IsLink e u w →
      (PanelHingeFramework.ofNormals G ends q').toBodyHinge.supportExtensor e ≠ 0 :=
    fun e u w he => PanelHingeFramework.supportExtensor_ne_zero_of_isGeneralPosition
      _ hgp' (by rw [PanelHingeFramework.ofNormals_ends]; exact (hends_G e u w he).ne)
  have hB2_q' : (Module.finrank ℝ (Submodule.span ℝ
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
  have hrank_eq_q' : (Module.finrank ℝ (Submodule.span ℝ
      (PanelHingeFramework.ofNormals G ends q').toBodyHinge.rigidityRows) : ℤ)
      = screwDim k * ((V(G).ncard : ℤ) - 1) - G.deficiency n := by
    have h1V : 1 ≤ V(G).ncard := (Set.ncard_pos (Set.toFinite _)).2 hVGne
    have hdef : G.deficiency n = c := hG.1
    have hrankge_int : screwDim k * ((V(G).ncard : ℤ) - 1) - c ≤
        (Module.finrank ℝ (Submodule.span ℝ
          (PanelHingeFramework.ofNormals G ends q').toBodyHinge.rigidityRows) : ℤ) := by
      -- hrankge_q' : screwDim k * (V(G).ncard - 1) - c.toNat ≤ finrank (ℕ)
      -- Cast to ℤ via the shared rank-equation cast bridge (same as hrank_lb_nat).
      have hc_toNat_le' : c.toNat ≤ screwDim k * (V(G).ncard - 1) :=
        toNat_le_of_add_pred_eq h1V hD1 hNpD
      have hZ_eq : (screwDim k : ℤ) * ((V(G).ncard : ℤ) - 1) - c =
          ↑(screwDim k * (V(G).ncard - 1) - c.toNat) := by
        rw [Nat.cast_sub hc_toNat_le', Nat.cast_mul, Nat.cast_sub h1V,
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
    PanelHingeFramework.ofNormals_recordsLinks_of_hends G ends q' hends_G,
    halg⟩

end CombinatorialRigidity.Molecular
