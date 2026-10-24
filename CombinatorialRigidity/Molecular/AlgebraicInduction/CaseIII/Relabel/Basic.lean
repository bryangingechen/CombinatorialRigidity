/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.AlgebraicInduction.CaseIII.Arms

/-!
# Case III: renaming the bodies

Lemmas for Case III of KT Theorem 5.5 (Katoh and Tanigawa 2011, *A proof of the molecular
conjecture*, Discrete Comput. Geom. **45**, §6.4), presented in
`sec:molecular-algebraic-induction-caseIII`. The file proves:

* that the framework `ofNormals` renamed along a permutation of the bodies and one of the edge
  labels has, at each label, the hinge of the original at the corresponding label
  (`ofNormals_supportExtensor_relabel_perm`), and that renaming takes a row to a row
  (`rigidityRow_relabel_to_genuine`, `blockRow_relabel_perm`): steps of
  `lem:case-III-chain-relabel-rows`;
* in the case `d = 3`, Katoh and Tanigawa's realization of `G_a^{vc}` and its rows
  (`ofNormals_relabel` and `hasGenericFullRankRealization_of_splitOff_relabel`,
  `lem:splitOff-ofNormals-relabel`; `rigidityRows_ofNormals_relabel`,
  `lem:splitOff-rigidityRows-relabel`), which no main result uses;
* that moving a body `a`, whose only edge joins it to `c`, to a body `v` that no edge meets takes
  the row space of one framework into that of another, once the form at `vc` given by the
  restriction to `a` is subtracted (`funLeft_dualMap_sub_acolumn_mem_span_rigidityRows`), and the
  move along a chain (`wstep`, `wstep_foldl_mem_span_rigidityRows`, `seedAdvance_wstep_hstep`):
  steps of `lem:case-III-candidate-dispatch-d3` and `lem:case-III-chain-eq666`.

`CaseIII/Relabel/Chain.lean` applies the renaming and the move to a chain, and
`CaseIII/Relabel/Arm.lean` applies the move to the third framework of the case `d = 3`.
-/

namespace CombinatorialRigidity.Molecular

variable {k : ℕ}

open scoped Graph

variable {α β : Type*}

variable {K : Type*} [Field K]

/-! ## Renaming the bodies by a permutation

Let `ρ` be a permutation of the bodies and `σ` one of the edge labels. The framework `ofNormals Gt`
with the selector `e ↦ (ρ⁻¹ (ends₀ (σ e)).1, ρ⁻¹ (ends₀ (σ e)).2)` and the normals `q₀ ∘ ρ` is
`ofNormals Gs ends₀ q₀` with its bodies renamed, when `σ` and `ρ` map the links of `Gt` to those of
`Gs`, and its rows are the forms `S ↦ φ (S ∘ ρ⁻¹)` for the rows `φ` of `ofNormals Gs ends₀ q₀`. The
proof of `lem:case-III-chain-relabel-rows` takes for `ρ` the cycle `shiftPerm i.castSucc`, which
maps `v₁ ↦ v₂ ↦ ⋯ ↦ v_i ↦ v₁` (the permutation `σᵢ` of that node), and for `σ` the permutation
`shiftEdgePerm i` of the labels. The first lemma, `hσσ_relabel`, serves the case `d = 3` below. -/

/-- **The permutation of the labels in the case `d = 3` is an involution** (a step of
`lem:splitOff-ofNormals-relabel` and `lem:splitOff-rigidityRows-relabel`): if `e_b`, `e_c`, `e₀` and
`e₁` are such that `{e_b, e₀}` and `{e₁, e_c}` are disjoint, then
`σ = Equiv.swap e_b e₀ * Equiv.swap e₁ e_c` satisfies `σ (σ f) = f` for every label `f`, as the two
transpositions commute. `ofNormals_relabel` and `rigidityRows_ofNormals_relabel` use it for the
permutation of `Graph.splitOff_isLink_relabel`. -/
private theorem hσσ_relabel {β : Type*} [DecidableEq β] {e_b e_c e₀ e₁ : β}
    (hbe₁ : e_b ≠ e₁) (hbec : e_b ≠ e_c) (h₀e₁ : e₀ ≠ e₁) (h₀ec : e₀ ≠ e_c) (f : β) :
    (Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) f) = f := by
  -- Pointwise: the two swaps act on disjoint pairs `{e_b, e₀}` and `{e₁, e_c}`.
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  split_ifs <;> simp_all

/-- **Renaming keeps the hinges** (a step of `lem:case-III-chain-relabel-rows` and
`lem:case-III-chain-eq666`): for a permutation `ρ` of the bodies and `σ` of the edge labels, the
framework `ofNormals Gt` with the selector `e ↦ (ρ⁻¹ (ends₀ (σ e)).1, ρ⁻¹ (ends₀ (σ e)).2)` and the
normals `q₀ ∘ ρ` has at `f` the hinge of `ofNormals Gt ends₀ q₀` at `σ f`, as in KT eq. (6.56)
(p. 694).

The renamed framework reads the normals `q₀` at the body `ρ p.1` and the selector `ends₀` at `σ e`,
moved back by `ρ⁻¹`, so the `ρ` of the normals cancels the `ρ⁻¹` of the selector, and the hinge at
`f` is that of `ends₀` at `σ f`; no involution is needed. `chainData_bottom_relabel`
(`lem:case-III-chain-relabel-rows`) uses it at `(ρ, σ) = (shiftPerm i.castSucc, shiftEdgePerm i)`.
-/
theorem PanelHingeFramework.ofNormals_supportExtensor_relabel_perm {Gt : Graph α β}
    (ρ : Equiv.Perm α) (σ : Equiv.Perm β)
    {ends₀ : β → α × α} {q₀ : α × Fin (k + 2) → K} (f : β) :
    (PanelHingeFramework.ofNormals Gt
        (fun e => (ρ.symm (ends₀ (σ e)).1, ρ.symm (ends₀ (σ e)).2))
        (fun p => q₀ (ρ p.1, p.2))).toBodyHinge.supportExtensor f =
      (PanelHingeFramework.ofNormals Gt ends₀ q₀).toBodyHinge.supportExtensor (σ f) := by
  simp only [PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_ends,
    PanelHingeFramework.ofNormals_normal, Equiv.apply_symm_apply]

/-- **Renaming takes a form at the new edge to a row** (a step of
`lem:case-III-chain-relabel-rows`): let `ρ'` vanish on `C(q₀(a), q₀(b))` (`hρ'`), and let `e_t` be a
link of `Gt` from `ρ⁻¹ a` to `ρ⁻¹ b` (`hlink`) at which `ofNormals Gt endsσρ qρ` has the hinge
`C(q₀(a), q₀(b))` (`hsupp`). Then the form `S ↦ hingeRow a b ρ' (S ∘ ρ⁻¹)`, which is
`hingeRow (ρ⁻¹ a) (ρ⁻¹ b) ρ'`, is a row of `ofNormals Gt endsσρ qρ` at `e_t`.
`chainData_bottom_relabel` uses it for the forms at the new edge `v₀v₂` of `G_1`, which the inverse
of the cycle `shiftPerm i.castSucc` takes to the edge `v₀v₁` of `G − v_i` (KT eq. (6.62), p. 696).
-/
theorem PanelHingeFramework.blockRow_relabel_perm {Gt : Graph α β}
    (ρ : Equiv.Perm α) {endsσρ : β → α × α} {qρ : α × Fin (k + 2) → K}
    {a b : α} {q₀ : α × Fin (k + 2) → K} {e_t : β}
    (hlink : Gt.IsLink e_t (ρ.symm a) (ρ.symm b))
    (hsupp : (PanelHingeFramework.ofNormals Gt endsσρ qρ).toBodyHinge.supportExtensor e_t
      = panelSupportExtensor (fun i => q₀ (a, i)) (fun i => q₀ (b, i)))
    {ρ' : Module.Dual K (ScrewSpace K k)}
    (hρ' : ρ' (panelSupportExtensor (fun i => q₀ (a, i)) (fun i => q₀ (b, i))) = 0) :
    (LinearMap.funLeft K (ScrewSpace K k) ρ.symm).dualMap
        (BodyHingeFramework.hingeRow a b ρ') ∈
      (PanelHingeFramework.ofNormals Gt endsσρ qρ).toBodyHinge.rigidityRows := by
  rw [BodyHingeFramework.hingeRow_funLeft_dualMap]
  refine ⟨e_t, ρ.symm a, ρ.symm b, ?_, ρ', ?_, rfl⟩
  · rw [PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]; exact hlink
  · rw [BodyHingeFramework.mem_hingeRowBlock_iff, hsupp]; exact hρ'

/-- **Renaming takes a row at a link to a row at a link** (a step of
`lem:case-III-chain-relabel-rows`): let `r` vanish on the hinge of `ofNormals Gs ends₀ q₀` at `f`
(`hr`), let `ρ⁻¹` take `u` and `w` to `u'` and `w'` (`hu`, `hw`), and let `f'` be a link of `Gt`
from `u'` to `w'` (`hlinkGt`) at which `ofNormals Gt endsσρ qρ` has the hinge of
`ofNormals Gs ends₀ q₀` at `f` (`hsupp`). Then the form `S ↦ hingeRow u w r (S ∘ ρ⁻¹)`, which is
`hingeRow u' w' r`, is a row of `ofNormals Gt endsσρ qρ` at `f'`.

`chainData_bottom_relabel` uses it for each row of `R(G − v₁, q)` whose ends the inverse of the
cycle `shiftPerm i.castSucc` takes to the ends of an edge of `G − v_i`: an edge `v_l v_{l+1}` with
`2 ≤ l ≤ i − 1` goes to `v_{l−1} v_l`, and an edge with no end among `v₁, …, v_i` to itself (KT
eq. (6.62), p. 696). -/
theorem PanelHingeFramework.rigidityRow_relabel_to_genuine {Gt : Graph α β}
    (ρ : Equiv.Perm α) {endsσρ : β → α × α} {qρ : α × Fin (k + 2) → K}
    {Gs : Graph α β} {ends₀ : β → α × α} {q₀ : α × Fin (k + 2) → K}
    {f f' : β} {u w u' w' : α} {r : Module.Dual K (ScrewSpace K k)}
    (hr : r ∈ (PanelHingeFramework.ofNormals Gs ends₀ q₀).toBodyHinge.hingeRowBlock f)
    (hu : ρ.symm u = u') (hw : ρ.symm w = w')
    (hlinkGt : Gt.IsLink f' u' w')
    (hsupp : (PanelHingeFramework.ofNormals Gt endsσρ qρ).toBodyHinge.supportExtensor f'
      = (PanelHingeFramework.ofNormals Gs ends₀ q₀).toBodyHinge.supportExtensor f) :
    (LinearMap.funLeft K (ScrewSpace K k) ρ.symm).dualMap
        (BodyHingeFramework.hingeRow u w r) ∈
      (PanelHingeFramework.ofNormals Gt endsσρ qρ).toBodyHinge.rigidityRows := by
  rw [BodyHingeFramework.hingeRow_funLeft_dualMap, hu, hw]
  refine ⟨f', u', w', ?_, r, ?_, rfl⟩
  · rw [PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]; exact hlinkGt
  · rw [BodyHingeFramework.mem_hingeRowBlock_iff, hsupp]
    exact (BodyHingeFramework.mem_hingeRowBlock_iff _ f r).1 hr

/-! ## The realization of `G_a^{vc}` (`lem:splitOff-ofNormals-relabel`,
`lem:splitOff-rigidityRows-relabel`)

In the case `d = 3`, Katoh and Tanigawa build their third framework `(G, p_3)` on a realization of
`G_a^{vc}` with the panels of `(G_v^{ab}, q)`, through an isomorphism `ρ` from `G_a^{vc}` to
`G_v^{ab}` (KT pp. 686–687 and eq. (6.31)). Here `ρ` is the transposition of `a` and `v`, and the
permutation of the labels is that of `lem:splitOff-isLink-relabel`. No main result uses these
lemmas: the proof of `lem:case-III` renames the bodies by the permutations of
`lem:case-III-chain-relabel-rows`, and the proof of the case `d = 3` (`case_III_candidate_dispatch`)
does not use them either (the note after `lem:case-III-chain-dispatch`). -/

/-- **A realization of `G_a^{vc}`** (`lem:splitOff-ofNormals-relabel`; KT eq. (6.31), p. 687): let
`v`, `a`, `b` and `c` be vertices of `G`, with `a`, `b` and `c` other than `v` and `c ≠ a`, such
that the edges of `G` at `v` are `eₐ : va` and `e_b : vb` (`hclv`) and those at `a` are `eₐ` and
`e_c : ac` (`hcla`), and let `e₀ ≠ e₁` outside `E(G)` label the new edges `ab` of
`G_v^{ab} = G.splitOff v a b e₀` and `vc` of `G_a^{vc} = G.splitOff a v c e₁`. Let `ρ` be the
transposition of `a` and `v`, and `σ = Equiv.swap e_b e₀ * Equiv.swap e₁ e_c` the permutation of the
labels of `lem:splitOff-isLink-relabel`. If `ofNormals G_v^{ab} ends₀ q₀` is in general position and
infinitesimally rigid on `V(G_v^{ab})`, and `ends₀` gives each link of `G_v^{ab}` its ends in some
order, then `ofNormals G_a^{vc}` with the selector `e ↦ (ρ (ends₀ (σ e)).1, ρ (ends₀ (σ e)).2)` and
the normals `q₀ ∘ ρ` is in general position and infinitesimally rigid on `V(G_a^{vc})`, and its
selector gives each link of `G_a^{vc}` its ends in some order. These are the three conjuncts of the
statement.

The normals `q₀ ∘ ρ` are those of `q₀`, permuted. As `ρ` and `σ` are involutions (`hσσ_relabel`),
the hinge of the new framework at `f` is that of `ofNormals G_v^{ab} ends₀ q₀` at `σ f`, and `σ f`
joins `ρ x` and `ρ y` in `G_v^{ab}` when `f` joins `x` and `y` in `G_a^{vc}`
(`Graph.splitOff_isLink_relabel`). So for an infinitesimal motion `S` of the new framework, `S ∘ ρ`
is one of `ofNormals G_v^{ab} ends₀ q₀`, constant on `V(G_v^{ab}) = V(G) ∖ {v}`, and `S` is constant
on `V(G) ∖ {a} = V(G_a^{vc})`, which `ρ` maps onto `V(G) ∖ {v}`. A link of `G_a^{vc}` maps to a link
of `G_v^{ab}`, whose ends `ends₀` gives. No declaration uses it but
`hasGenericFullRankRealization_of_splitOff_relabel`. -/
theorem PanelHingeFramework.ofNormals_relabel [DecidableEq α] [DecidableEq β]
    {G : Graph α β}
    {v a b c : α} {eₐ e_b e_c e₀ e₁ : β}
    (hG_ea : G.IsLink eₐ v a) (hG_eb : G.IsLink e_b v b) (hG_ec : G.IsLink e_c a c)
    (hav : a ≠ v) (hbv : b ≠ v) (hcv : c ≠ v) (hca : c ≠ a) (heab : eₐ ≠ e_b)
    (hclv : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    (hcla : ∀ e x, G.IsLink e a x → e = eₐ ∨ e = e_c)
    (he₀ : e₀ ∉ E(G)) (he₁ : e₁ ∉ E(G)) (he₁₀ : e₁ ≠ e₀)
    {ends₀ : β → α × α} {q₀ : α × Fin (k + 2) → K}
    (hQgp : (PanelHingeFramework.ofNormals (G.splitOff v a b e₀) ends₀ q₀).IsGeneralPosition)
    (hQrig :
      (PanelHingeFramework.ofNormals (G.splitOff v a b e₀) ends₀
        q₀).toBodyHinge.IsInfinitesimallyRigidOn V(G.splitOff v a b e₀))
    (hQrec : ∀ e u w, (G.splitOff v a b e₀).IsLink e u w →
        ends₀ e = (u, w) ∨ ends₀ e = (w, u)) :
    (PanelHingeFramework.ofNormals (G.splitOff a v c e₁)
        (fun e => (Equiv.swap a v (ends₀ ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)).1,
          Equiv.swap a v (ends₀ ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)).2))
        (fun p => q₀ (Equiv.swap a v p.1, p.2))).IsGeneralPosition ∧
    (PanelHingeFramework.ofNormals (G.splitOff a v c e₁)
        (fun e => (Equiv.swap a v (ends₀ ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)).1,
          Equiv.swap a v (ends₀ ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)).2))
        (fun p => q₀ (Equiv.swap a v p.1, p.2))).toBodyHinge.IsInfinitesimallyRigidOn
          V(G.splitOff a v c e₁) ∧
    (∀ e u w, (G.splitOff a v c e₁).IsLink e u w →
        (Equiv.swap a v (ends₀ ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)).1,
          Equiv.swap a v (ends₀ ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)).2) = (u, w) ∨
        (Equiv.swap a v (ends₀ ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)).1,
          Equiv.swap a v (ends₀ ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)).2) = (w, u)) := by
  classical
  set ρ : Equiv.Perm α := Equiv.swap a v with hρ_def
  set σ : Equiv.Perm β := Equiv.swap e_b e₀ * Equiv.swap e₁ e_c with hσ_def
  set endsσρ : β → α × α := fun e => (ρ (ends₀ (σ e)).1, ρ (ends₀ (σ e)).2) with hendsσρ
  set qρ : α × Fin (k + 2) → K := fun p => q₀ (ρ p.1, p.2) with hqρ
  -- ρ ∘ ρ = id.
  have hρρ : ∀ x : α, ρ (ρ x) = x := fun x => Equiv.swap_apply_self a v x
  -- ρ maps V(G) to itself (a, v ∈ V(G)).
  have hρmemV : ∀ u : α, u ∈ V(G) → ρ u ∈ V(G) := fun u hu => by
    rw [hρ_def, Equiv.swap_apply_def]
    split_ifs with h1 h2
    · exact hG_ea.left_mem   -- u = a → ρ u = v ∈ V(G)
    · exact hG_ea.right_mem  -- u = v → ρ u = a ∈ V(G)
    · exact hu               -- otherwise fixed
  -- ρ maps V(G) \ {a} to V(G) \ {v} bijectively.
  have hρ_diff : ∀ u : α, u ∈ V(G) \ {a} → ρ u ∈ V(G) \ {v} := fun u hu => by
    refine Set.mem_sdiff_of_mem (hρmemV u hu.1) ?_
    intro h
    have hρa : ρ a = v := by rw [hρ_def]; exact Equiv.swap_apply_left a v
    have hua : u = a := ρ.injective ((Set.mem_singleton_iff.mp h).trans hρa.symm)
    exact hu.2 (Set.mem_singleton_iff.mpr hua)
  -- σ ∘ σ = id, from the four edge-distinctness facts.
  have hbe₁ : e_b ≠ e₁ := fun h => he₁ (h ▸ hG_eb.edge_mem)
  have h₀ec : e₀ ≠ e_c := fun h => he₀ (h ▸ hG_ec.edge_mem)
  have hbec : e_b ≠ e_c := by
    intro h
    rcases hG_eb.left_eq_or_eq (h ▸ hG_ec) with h1 | h1
    · exact hav h1.symm
    · exact hcv h1.symm
  have hσσ : ∀ f, σ (σ f) = f := fun f => hσσ_relabel hbe₁ hbec he₁₀.symm h₀ec f
  set Q := PanelHingeFramework.ofNormals (G.splitOff v a b e₀) ends₀ q₀ with hQ_def
  set Q' := PanelHingeFramework.ofNormals (G.splitOff a v c e₁) endsσρ qρ with hQ'_def
  -- Q'.supportExtensor f = Q.supportExtensor (σ f): the relabelled framework's hinge at f reads
  -- q₀ at the ρ-shifted endpoints, i.e. the original hinge at (σ f). No σ-involution needed.
  have h_supp : ∀ f : β,
      Q'.toBodyHinge.supportExtensor f = Q.toBodyHinge.supportExtensor (σ f) := by
    intro f
    simp only [hQ_def, hQ'_def, PanelHingeFramework.toBodyHinge_supportExtensor,
      PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal, hendsσρ, hqρ, hρρ]
  refine ⟨?_, ?_, ?_⟩
  -- (1) General position: Q'.normal x = q₀ (ρ x, ·), reindexed by injective ρ.
  · intro x y hxy
    change LinearIndependent K ![fun i => qρ (x, i), fun i => qρ (y, i)]
    have := hQgp (ρ x) (ρ y) (ρ.injective.ne hxy)
    simpa only [hQ_def, PanelHingeFramework.ofNormals_normal, hqρ] using this
  -- (2) Rigidity: any motion S of Q' yields the motion S ∘ ρ of Q, constant on V(G) \ {v},
  --     hence S constant on V(G) \ {a}.
  · intro S hS u hu w hw
    -- S ∘ ρ is an infinitesimal motion of Q.
    have hSmot : Q.toBodyHinge.IsInfinitesimalMotion (S ∘ ρ) := by
      intro f x y hf
      simp only [hQ_def, PanelHingeFramework.toBodyHinge_graph,
        PanelHingeFramework.ofNormals_graph] at hf
      have hfQ' : (G.splitOff a v c e₁).IsLink (σ f) (ρ x) (ρ y) :=
        (_root_.Graph.splitOff_isLink_relabel hG_ea hG_eb hG_ec hav hbv hcv hca
          heab hclv hcla he₀ he₁ he₁₀).mpr (by rw [hσσ f, hρρ, hρρ]; exact hf)
      have harg : Q'.toBodyHinge.graph.IsLink (σ f) (ρ x) (ρ y) := by
        simp only [hQ'_def, PanelHingeFramework.toBodyHinge_graph,
          PanelHingeFramework.ofNormals_graph]; exact hfQ'
      have hSc : Q'.toBodyHinge.hingeConstraint S (σ f) (ρ x) (ρ y) := hS (σ f) (ρ x) (ρ y) harg
      -- hSc : S (ρ x) - S (ρ y) ∈ span {Q'.supportExtensor (σ f)} = span {Q.supportExtensor f}.
      change (S ∘ ρ) x - (S ∘ ρ) y ∈ Submodule.span K {Q.toBodyHinge.supportExtensor f}
      rw [show Q.toBodyHinge.supportExtensor f = Q'.toBodyHinge.supportExtensor (σ f) by
        rw [h_supp (σ f), hσσ f]]
      exact hSc
    -- Apply Q's rigidity on V(G.splitOff v a b e₀) = V(G) \ {v}.
    rw [Graph.vertexSet_splitOff] at hu hw
    have hρu := hρ_diff u hu
    have hρw := hρ_diff w hw
    rw [hQ_def, Graph.vertexSet_splitOff] at hQrig
    have hSmotConst := hQrig (S ∘ ρ) hSmot (ρ u) hρu (ρ w) hρw
    simp only [Function.comp] at hSmotConst
    rwa [hρρ u, hρρ w] at hSmotConst
  -- (3) Link-recording: every link of G.splitOff a v c e₁ has endpoints recorded by endsσρ.
  · intro e' u w he'
    have hfQ : (G.splitOff v a b e₀).IsLink (σ e') (ρ u) (ρ w) :=
      (_root_.Graph.splitOff_isLink_relabel hG_ea hG_eb hG_ec hav hbv hcv hca
        heab hclv hcla he₀ he₁ he₁₀).mp he'
    rcases hQrec (σ e') (ρ u) (ρ w) hfQ with h1 | h1
    · refine Or.inl ?_
      rw [h1]; exact Prod.ext (hρρ u) (hρρ w)
    · refine Or.inr ?_
      rw [h1]; exact Prod.ext (hρρ w) (hρρ u)

/-- **The rows of the realization of `G_a^{vc}`** (`lem:splitOff-rigidityRows-relabel`; KT
eq. (6.31), p. 687): with `G`, `v`, `a`, `b`, `c`, the labels, `ρ = Equiv.swap a v` and `σ` as in
`ofNormals_relabel`, and for every selector `ends₀` and normals `q₀`, the rows of
`ofNormals G_a^{vc}` with the selector `e ↦ (ρ (ends₀ (σ e)).1, ρ (ends₀ (σ e)).2)` and the normals
`q₀ ∘ ρ` are the forms `S ↦ φ (S ∘ ρ)` for the rows `φ` of `ofNormals G_v^{ab} ends₀ q₀`.

A row `hingeRow u w r` of the new framework at a link `f` is the image of the row
`hingeRow (ρ u) (ρ w) r` at the link `σ f` of `G_v^{ab}` (`Graph.splitOff_isLink_relabel`), as `ρ`
is an involution, and the two links have the same hinge, so the same block of rows. No main result
uses it (the note after `lem:case-III-chain-dispatch`). -/
theorem PanelHingeFramework.rigidityRows_ofNormals_relabel [DecidableEq α] [DecidableEq β]
    {G : Graph α β}
    {v a b c : α} {eₐ e_b e_c e₀ e₁ : β}
    (hG_ea : G.IsLink eₐ v a) (hG_eb : G.IsLink e_b v b) (hG_ec : G.IsLink e_c a c)
    (hav : a ≠ v) (hbv : b ≠ v) (hcv : c ≠ v) (hca : c ≠ a) (heab : eₐ ≠ e_b)
    (hclv : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    (hcla : ∀ e x, G.IsLink e a x → e = eₐ ∨ e = e_c)
    (he₀ : e₀ ∉ E(G)) (he₁ : e₁ ∉ E(G)) (he₁₀ : e₁ ≠ e₀)
    (ends₀ : β → α × α) (q₀ : α × Fin (k + 2) → K) :
    (PanelHingeFramework.ofNormals (G.splitOff a v c e₁)
        (fun e => (Equiv.swap a v (ends₀ ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)).1,
          Equiv.swap a v (ends₀ ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)).2))
        (fun p => q₀ (Equiv.swap a v p.1, p.2))).toBodyHinge.rigidityRows =
      (LinearMap.funLeft K (ScrewSpace K k) (Equiv.swap a v)).dualMap ''
        (PanelHingeFramework.ofNormals (G.splitOff v a b e₀) ends₀
          q₀).toBodyHinge.rigidityRows := by
  classical
  set ρ : Equiv.Perm α := Equiv.swap a v with hρ_def
  set σ : Equiv.Perm β := Equiv.swap e_b e₀ * Equiv.swap e₁ e_c with hσ_def
  set endsσρ : β → α × α := fun e => (ρ (ends₀ (σ e)).1, ρ (ends₀ (σ e)).2) with hendsσρ
  set qρ : α × Fin (k + 2) → K := fun p => q₀ (ρ p.1, p.2) with hqρ
  have hρρ : ∀ x : α, ρ (ρ x) = x := fun x => Equiv.swap_apply_self a v x
  -- (funLeft ρ).dualMap (hingeRow (ρ u) (ρ w) r) = hingeRow u w r.
  have hdual : ∀ (u w : α) (r : Module.Dual K (ScrewSpace K k)),
      (LinearMap.funLeft K (ScrewSpace K k) ρ).dualMap
        (BodyHingeFramework.hingeRow (ρ u) (ρ w) r) = BodyHingeFramework.hingeRow u w r := by
    intro u w r
    refine LinearMap.ext fun S => ?_
    rw [LinearMap.dualMap_apply, BodyHingeFramework.hingeRow_apply,
      BodyHingeFramework.hingeRow_apply]
    simp only [LinearMap.funLeft_apply, hρρ]
  have hbe₁ : e_b ≠ e₁ := fun h => he₁ (h ▸ hG_eb.edge_mem)
  have h₀ec : e₀ ≠ e_c := fun h => he₀ (h ▸ hG_ec.edge_mem)
  have hbec : e_b ≠ e_c := by
    intro h
    rcases hG_eb.left_eq_or_eq (h ▸ hG_ec) with h1 | h1
    · exact hav h1.symm
    · exact hcv h1.symm
  have hσσ : ∀ f, σ (σ f) = f := fun f => hσσ_relabel hbe₁ hbec he₁₀.symm h₀ec f
  set Q := PanelHingeFramework.ofNormals (G.splitOff v a b e₀) ends₀ q₀ with hQ_def
  set Q' := PanelHingeFramework.ofNormals (G.splitOff a v c e₁) endsσρ qρ with hQ'_def
  -- Q'.supportExtensor f = Q.supportExtensor (σ f): the relabelled hinge at f reads q₀ at the
  -- ρ-shifted endpoints, i.e. the original hinge at (σ f). No σ-involution needed.
  have h_supp : ∀ f : β,
      Q'.toBodyHinge.supportExtensor f = Q.toBodyHinge.supportExtensor (σ f) := by
    intro f
    simp only [hQ_def, hQ'_def, PanelHingeFramework.toBodyHinge_supportExtensor,
      PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal, hendsσρ, hqρ, hρρ]
  -- The hinge-row blocks at ρ-corresponding edges coincide (dual annihilator of the same span).
  have hblock : ∀ f : β,
      Q'.toBodyHinge.hingeRowBlock f = Q.toBodyHinge.hingeRowBlock (σ f) := by
    intro f; simp only [BodyHingeFramework.hingeRowBlock, h_supp f]
  apply Set.eq_of_subset_of_subset
  -- ⊆ : every a-split row is the image of a matching v-split row.
  · rintro φ ⟨e', u, w, hlink', r, hr, rfl⟩
    refine ⟨BodyHingeFramework.hingeRow (ρ u) (ρ w) r,
      ⟨σ e', ρ u, ρ w, ?_, r, ?_, rfl⟩, hdual u w r⟩
    · have hmp := (_root_.Graph.splitOff_isLink_relabel hG_ea hG_eb hG_ec hav hbv hcv hca
        heab hclv hcla he₀ he₁ he₁₀ (e := e') (x := u) (y := w)).mp
      simp only [hQ'_def, PanelHingeFramework.toBodyHinge_graph,
        PanelHingeFramework.ofNormals_graph] at hlink'
      simpa only [hQ_def, PanelHingeFramework.toBodyHinge_graph,
        PanelHingeFramework.ofNormals_graph] using hmp hlink'
    · rw [← hblock e']; exact hr
  -- ⊇ : every image of a v-split row is an a-split row.
  · rintro φ ⟨ψ, ⟨e', u, w, hlink, r, hr, rfl⟩, rfl⟩
    refine ⟨σ e', ρ u, ρ w, ?_, r, ?_, ?_⟩
    · have hmpr := (_root_.Graph.splitOff_isLink_relabel hG_ea hG_eb hG_ec hav hbv hcv hca
        heab hclv hcla he₀ he₁ he₁₀ (e := σ e') (x := ρ u) (y := ρ w)).mpr
      simp only [hQ_def, PanelHingeFramework.toBodyHinge_graph,
        PanelHingeFramework.ofNormals_graph] at hlink
      simp only [hQ'_def, PanelHingeFramework.toBodyHinge_graph,
        PanelHingeFramework.ofNormals_graph]
      exact hmpr (by rw [hσσ e', hρρ, hρρ]; exact hlink)
    · rw [hblock (σ e'), hσσ e']; exact hr
    · have := hdual (ρ u) (ρ w) r
      rwa [hρρ, hρρ] at this

/-- **A generic full-rank realization of `G_a^{vc}`** (`lem:splitOff-ofNormals-relabel`, its last
claim; KT eq. (6.31), p. 687): with `G`, `v`, `a`, `b`, `c` and the labels as in
`ofNormals_relabel`, if `G_v^{ab}` and `G_a^{vc}` have deficiency `0` and `G_v^{ab}` has a generic
full-rank realization, then so has `G_a^{vc}`. At deficiency `0` the realization of `G_v^{ab}` has
the rank `D(|V(G_v^{ab})| − 1)`, so it is infinitesimally rigid on `V(G_v^{ab})`
(`isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows`); `ofNormals_relabel` gives a
framework on `G_a^{vc}`, infinitesimally rigid on `V(G_a^{vc})`, hence of the rank
`D(|V(G_a^{vc})| − 1)` (`finrank_span_rigidityRows_of_rigidOn`). No declaration uses it. -/
theorem PanelHingeFramework.hasGenericFullRankRealization_of_splitOff_relabel [Finite α]
    {G : Graph α β}
    {v a b c : α} {eₐ e_b e_c e₀ e₁ : β}
    (hG_ea : G.IsLink eₐ v a) (hG_eb : G.IsLink e_b v b) (hG_ec : G.IsLink e_c a c)
    (hav : a ≠ v) (hbv : b ≠ v) (hcv : c ≠ v) (hca : c ≠ a) (heab : eₐ ≠ e_b)
    (hclv : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    (hcla : ∀ e x, G.IsLink e a x → e = eₐ ∨ e = e_c)
    (he₀ : e₀ ∉ E(G)) (he₁ : e₁ ∉ E(G)) (he₁₀ : e₁ ≠ e₀)
    (n : ℕ) (hdef_in : (G.splitOff v a b e₀).deficiency n = 0)
    (hdef_out : (G.splitOff a v c e₁).deficiency n = 0)
    (hQ : PanelHingeFramework.HasGenericFullRankRealization K k n (G.splitOff v a b e₀)) :
    PanelHingeFramework.HasGenericFullRankRealization K k n (G.splitOff a v c e₁) := by
  classical
  obtain ⟨Q, hQg, hQgp, hQrank, hQrec⟩ := hQ
  -- Derive rigidity from the rank hypothesis.
  have hne_in : V(G.splitOff v a b e₀).Nonempty :=
    ⟨a, by rw [Graph.vertexSet_splitOff]; exact ⟨hG_ea.right_mem, by simp [hav]⟩⟩
  have hne_in' : Q.toBodyHinge.graph.vertexSet.Nonempty := by
    rw [PanelHingeFramework.toBodyHinge_graph, hQg]; exact hne_in
  rw [hdef_in, sub_zero] at hQrank
  have hVeq_in : V(G.splitOff v a b e₀) = Q.toBodyHinge.graph.vertexSet := by
    rw [PanelHingeFramework.toBodyHinge_graph, hQg]
  have h1_in : 1 ≤ V(G.splitOff v a b e₀).ncard := (Set.ncard_pos (Set.toFinite _)).2 hne_in
  have hQrig : Q.toBodyHinge.IsInfinitesimallyRigidOn V(G.splitOff v a b e₀) := by
    rw [hVeq_in, BodyHingeFramework.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows
        Q.toBodyHinge hne_in', ← hVeq_in]
    zify [h1_in] at hQrank ⊢; exact_mod_cast hQrank
  -- Re-express Q as the canonical `ofNormals` of its own normals/ends; feed `ofNormals_relabel`.
  have hQeq : PanelHingeFramework.ofNormals (G.splitOff v a b e₀) Q.ends
      (fun p => Q.normal p.1 p.2) = Q := by rw [← hQg]; rfl
  have hgp' : (PanelHingeFramework.ofNormals (G.splitOff v a b e₀) Q.ends
      (fun p => Q.normal p.1 p.2)).IsGeneralPosition := by rw [hQeq]; exact hQgp
  have hrig' : (PanelHingeFramework.ofNormals (G.splitOff v a b e₀) Q.ends
      (fun p => Q.normal p.1 p.2)).toBodyHinge.IsInfinitesimallyRigidOn
        V(G.splitOff v a b e₀) := by rw [hQeq]; exact hQrig
  have hrec' : ∀ e u w, (G.splitOff v a b e₀).IsLink e u w →
      Q.ends e = (u, w) ∨ Q.ends e = (w, u) := by
    intro e u w he
    rcases hQrec e u w he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (Prod.ext h1 h2)
    · exact Or.inr (Prod.ext h1 h2)
  obtain ⟨hgp, hrig_out, hrec⟩ := PanelHingeFramework.ofNormals_relabel hG_ea hG_eb hG_ec
    hav hbv hcv hca heab hclv hcla he₀ he₁ he₁₀ hgp' hrig' hrec'
  -- Derive rank from the rigidity of the output framework.
  set F_out := PanelHingeFramework.ofNormals (G.splitOff a v c e₁)
      (fun e => (Equiv.swap a v (Q.ends ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)).1,
        Equiv.swap a v (Q.ends ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)).2))
      (fun p => Q.normal (Equiv.swap a v p.1) p.2) with hF_out
  have hne_out : V(G.splitOff a v c e₁).Nonempty :=
    ⟨c, by rw [Graph.vertexSet_splitOff]; exact ⟨hG_ec.right_mem, by simp [hca]⟩⟩
  have h1_out : 1 ≤ V(G.splitOff a v c e₁).ncard := (Set.ncard_pos (Set.toFinite _)).2 hne_out
  have hW2 := F_out.toBodyHinge.finrank_span_rigidityRows_of_rigidOn hne_out
    (by rw [PanelHingeFramework.toBodyHinge_graph,
        PanelHingeFramework.ofNormals_graph]; exact hrig_out)
  have hrank_out :
      (Module.finrank K (Submodule.span K F_out.toBodyHinge.rigidityRows) : ℤ) =
      screwDim k * ((V(G.splitOff a v c e₁).ncard : ℤ) - 1) -
      (G.splitOff a v c e₁).deficiency n := by
    rw [hdef_out, sub_zero]
    have hVncard_out : F_out.toBodyHinge.graph.vertexSet.ncard = V(G.splitOff a v c e₁).ncard := by
      rw [PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]
    rw [← hVncard_out]
    rw [← hVncard_out] at h1_out
    zify [h1_out] at hW2 ⊢; exact_mod_cast hW2
  -- The link conjunct, from equalities of pairs to equalities of their components.
  refine ⟨_, rfl, hgp, hrank_out, fun e u w he => ?_⟩
  rcases hrec e u w he with h1 | h1
  · exact Or.inl ⟨by rw [PanelHingeFramework.ofNormals_ends, (Prod.ext_iff.mp h1).1],
      by rw [PanelHingeFramework.ofNormals_ends, (Prod.ext_iff.mp h1).2]⟩
  · exact Or.inr ⟨by rw [PanelHingeFramework.ofNormals_ends, (Prod.ext_iff.mp h1).1],
      by rw [PanelHingeFramework.ofNormals_ends, (Prod.ext_iff.mp h1).2]⟩

/-! ## Moving a body in a combination of rows

Steps of `lem:case-III-candidate-dispatch-d3` and `lem:case-III-chain-eq666`. Let `a` be a body
whose only edge in a framework `Fv` joins it to `c`, and `v` a body that no edge of `Fv` meets. For
a form `φ` in the span of the rows of `Fv`, the form `S ↦ φ (S ∘ τ)`, for the transposition `τ` of
`a` and `v`, minus the form `S ↦ x(S(v) − S(c))`, for the restriction `x` of `φ` to the screw
assignments that vanish off `a`, lies in the span of the rows of a framework `Fva` in which `v`
takes the place of `a`. In the case `d = 3` this gives the form `S ↦ r(S(v) − S(c))` of the third
framework (the note after `lem:case-III-claim612-p3-placement`); along a chain, the move is made at
one vertex after another. -/

/-- **Moving the body `a` to `v` in a combination of rows** (a step of
`lem:case-III-candidate-dispatch-d3` and `lem:case-III-chain-eq666`): let `e_c` join `a` to `c` in
`Fv`, where `c ≠ a` and `c ≠ v`, let `e_c` be the only link of `Fv` at `a` (`hdeg2`, `hdeg2r`), let
no link of `Fv` meet `v` (`hnov`), and let every link of `Fv` that does not meet `a` be a link of
`Fva` whose block of rows in `Fva` contains that in `Fv` (`htrans`). Then for every `φ` in the span
of the rows of `Fv`, the form `(funLeft τ).dualMap φ − hingeRow v c (φ ∘ single a)`, that is,
`S ↦ φ (S ∘ τ) − x(S(v) − S(c))` for the transposition `τ` of `a` and `v` and the restriction
`x = φ ∘ single a` of `φ` to the screw assignments that vanish off `a`, lies in the span of the rows
of `Fva`.

As no link of `Fv` meets `v`, `φ (S ∘ τ)` is `φ` at the screw assignment `S'` that agrees with `S`
but has `S'(a) = S(v)`, as in the proof of `lem:case-III-claim612-p3-placement`. The proof is by
induction on the span: a row `hingeRow a c r` at `e_c` goes to `hingeRow v c r`, which the
subtracted form cancels, and so does a row `hingeRow c a r`; a row at a link that meets neither `a`
nor `v` is fixed, and it is a row of `Fva` by `htrans`. `case_III_arm_realization_M3` applies it at
`φ = hingeRow a b ρ`, with `Fv` and `Fva` on `G − v` and `G − a`, and `wstep` makes it a linear map
for a chain. Its frameworks are arbitrary, so the proof never unfolds a caller's `ofNormals`
(TACTICS-QUIRKS §38). -/
theorem BodyHingeFramework.funLeft_dualMap_sub_acolumn_mem_span_rigidityRows
    [DecidableEq α] {Fv Fva : BodyHingeFramework K k α β}
    {v a c : α} {e_c : β}
    (hca : c ≠ a) (hcv : c ≠ v)
    (hlink_ec : Fv.graph.IsLink e_c a c)
    (hdeg2 : ∀ f x, Fv.graph.IsLink f a x → f = e_c)
    (hdeg2r : ∀ f x, Fv.graph.IsLink f x a → f = e_c)
    (hnov : ∀ f x y, Fv.graph.IsLink f x y → x ≠ v ∧ y ≠ v)
    (htrans : ∀ f x y, Fv.graph.IsLink f x y → x ≠ a → y ≠ a →
      Fva.graph.IsLink f x y ∧ Fv.hingeRowBlock f ≤ Fva.hingeRowBlock f)
    {φ : Module.Dual K (α → ScrewSpace K k)}
    (hφ : φ ∈ Submodule.span K Fv.rigidityRows) :
    (LinearMap.funLeft K (ScrewSpace K k) (Equiv.swap a v)).dualMap φ
        - BodyHingeFramework.hingeRow (k := k) (α := α) v c
            (φ.comp (LinearMap.single K (fun _ : α => ScrewSpace K k) a))
      ∈ Submodule.span K Fva.rigidityRows := by
  -- Bundle the transport as a single linear map `T` so the `span_induction` predicate stays
  -- light (`T ψ ∈ span …`) — keeping the heavy `Module.Dual (α → ScrewSpace K k)` terms out of
  -- the predicate, which is what the `add`/`smul`/`zero` cases discharge mechanically by
  -- `map_add`/`map_smul`/`map_zero`. `hingeRow v c (· ∘ single a)` is the linear composite
  -- `(screwDiff v c).dualMap ∘ₗ (single a).dualMap` (both `hingeRow_eq_dualMap` and
  -- `LinearMap.dualMap` of `single` unfold `∘ₗ` to the same `comp`).
  set T : Module.Dual K (α → ScrewSpace K k) →ₗ[K] Module.Dual K (α → ScrewSpace K k) :=
    (LinearMap.funLeft K (ScrewSpace K k) (Equiv.swap a v)).dualMap
      - (screwDiff (k := k) (α := α) v c).dualMap.comp
          (LinearMap.single K (fun _ : α => ScrewSpace K k) a).dualMap with hT
  -- `T ψ` is the transported difference, for every `ψ` (the `hingeRow`/`comp` forms agree with
  -- the `dualMap` composites by `rfl`).
  have hTapply : ∀ ψ : Module.Dual K (α → ScrewSpace K k),
      T ψ = (LinearMap.funLeft K (ScrewSpace K k) (Equiv.swap a v)).dualMap ψ
        - BodyHingeFramework.hingeRow (k := k) (α := α) v c
            (ψ.comp (LinearMap.single K (fun _ : α => ScrewSpace K k) a)) := fun ψ => by
    rw [hT, LinearMap.sub_apply, LinearMap.comp_apply, hingeRow_eq_dualMap]; rfl
  rw [← hTapply]
  -- `span_induction` on `hφ` with the light predicate `T ψ ∈ span Fva.rigidityRows`.
  apply Submodule.span_induction
    (p := fun ψ _ => T ψ ∈ Submodule.span K Fva.rigidityRows) _ _ _ _ hφ
  · -- generator case: ψ = hingeRow x y r at a link f, r ∈ Fv.hingeRowBlock f.
    -- Unfold `T` to the `dualMap` form (not via `hTapply`): keeping the subtracted term as
    -- `(screwDiff v c).dualMap (…)` lets `map_zero` close the off-case without producing the
    -- heavy nested `hingeRow v c 0` term whose `rw`-motive abstraction trips §38.
    rintro ψ ⟨f, x, y, hlink, r, hr, rfl⟩
    rw [hT, LinearMap.sub_apply, LinearMap.comp_apply,
      BodyHingeFramework.hingeRow_funLeft_dualMap,
      show (LinearMap.single K (fun _ : α => ScrewSpace K k) a).dualMap (hingeRow x y r)
          = (hingeRow x y r).comp (LinearMap.single K (fun _ : α => ScrewSpace K k) a) from rfl]
    by_cases hxa : x = a
    · -- x = a: hdeg2 forces f = e_c, hence y = c; the relabel is hingeRow v c r and the
      -- a-column is r, so the difference vanishes.
      have hfe : f = e_c := by rw [hxa] at hlink; exact hdeg2 f y hlink
      have hyc : y = c := by
        rw [hxa, hfe] at hlink
        rcases hlink.eq_and_eq_or_eq_and_eq hlink_ec with ⟨-, h⟩ | ⟨h, -⟩
        · exact h
        · exact absurd h (Ne.symm hca)
      rw [hxa, hyc]
      simp only [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hca hcv,
        hingeRow_comp_single_tail hca.symm, ← hingeRow_eq_dualMap, sub_self]
      exact Submodule.zero_mem _
    · by_cases hya : y = a
      · -- y = a, x ≠ a: hdeg2r forces f = e_c, hence x = c.
        have hfe : f = e_c := by rw [hya] at hlink; exact hdeg2r f x hlink
        have hxc : x = c := by
          rw [hya, hfe] at hlink
          rcases hlink.eq_and_eq_or_eq_and_eq hlink_ec with ⟨h, -⟩ | ⟨h, -⟩
          · exact absurd h hxa
          · exact h
        -- relabel: hingeRow c v r; a-column: hingeRow c a r ∘ single a = -r (swap then tail);
        -- subtracted row hingeRow v c (-r) = hingeRow c v r, so the difference vanishes.
        rw [hxc, hya]
        simp only [Equiv.swap_apply_of_ne_of_ne hca hcv, Equiv.swap_apply_left,
          hingeRow_swap c a r, hingeRow_comp_single_tail hca.symm, ← hingeRow_eq_dualMap,
          hingeRow_swap v c (-r), neg_neg, sub_self]
        exact Submodule.zero_mem _
      · -- x ≠ a, y ≠ a: the transposition fixes both ends (they are not `v` either, by `hnov`), and
        -- the restriction to `a` is 0, so the result is the generator itself, a row of `Fva` by
        -- `htrans`.
        obtain ⟨hxv, hyv⟩ := hnov f x y hlink
        obtain ⟨hlink', hble⟩ := htrans f x y hlink hxa hya
        simp only [Equiv.swap_apply_of_ne_of_ne hxa hxv, Equiv.swap_apply_of_ne_of_ne hya hyv,
          hingeRow_comp_single_off (Ne.symm hxa) (Ne.symm hya), map_zero, sub_zero]
        exact Submodule.subset_span ⟨f, x, y, hlink', r, hble hr, rfl⟩
  · -- zero
    rw [map_zero]; exact Submodule.zero_mem _
  · -- add: `T` is linear, so the (x+y)-row is the sum of the x- and y-rows.
    intro x y _ _ hx hy
    rw [map_add]; exact Submodule.add_mem _ hx hy
  · -- smul
    intro t x _ hx
    rw [map_smul]; exact Submodule.smul_mem _ t hx

/-- **A step along the chain satisfies the hypotheses of the move** (a step of
`lem:case-III-chain-eq666`): for a chain `v₀ ⋯ v_d` and `s + 2 < d`, let `ends'` agree with `ends`
off the edges `v_{s+1} v_{s+2}` and `v_{s+2} v_{s+3}` (`hends'_off`), and let `ends` give each link
of `G − v_{s+1}` its ends in some order (`hrec`). Then `Fv = ofNormals (G − v_{s+1}) ends q` and
`Fva = ofNormals (G − v_{s+2}) ends' (q ∘ τ)`, for the transposition `τ` of `v_{s+2}` and `v_{s+1}`,
satisfy the six hypotheses of `funLeft_dualMap_sub_acolumn_mem_span_rigidityRows` at
`(v, a, c) = (v_{s+1}, v_{s+2}, v_{s+3})` and the edge `e_c = v_{s+2} v_{s+3}`. These are the
hypotheses that `wstep_foldl_mem_span_rigidityRows` asks for at each step, and
`shiftBodyListAsc_foldl_mem_span_rigidityRows` (`CaseIII/Relabel/Chain.lean`) takes them from here.

The vertex `v_{s+2}` is interior, so its edges in `G` are `v_{s+1} v_{s+2}` and `v_{s+2} v_{s+3}`
(`ChainData.deg_two`), and only the second is an edge of `G − v_{s+1}`. A link of `G − v_{s+1}` that
does not meet `v_{s+2}` is neither of the two edges, so `ends'` gives it the ends that `ends` gives,
its own ends by `hrec`, which `τ` fixes: the two frameworks have the same hinge there. The proof
reads the graphs and hinges through `toBodyHinge_graph`, `ofNormals_graph`,
`toBodyHinge_supportExtensor`, `ofNormals_ends` and `ofNormals_normal`, not by `whnf`
(TACTICS-QUIRKS §38). -/
theorem _root_.Graph.ChainData.seedAdvance_wstep_hstep
    [DecidableEq α] {G : Graph α β} {n : ℕ} (cd : G.ChainData n) {s : ℕ}
    (hbound : s + 2 < cd.d) (ends ends' : β → α × α) (q : α × Fin (k + 2) → K)
    (hends'_off : ∀ f, f ≠ cd.edge ⟨s + 1, by omega⟩ → f ≠ cd.edge ⟨s + 2, by omega⟩ →
      ends' f = ends f)
    (hrec : ∀ f x y, (G.removeVertex (cd.vtx ⟨s + 1, by omega⟩)).IsLink f x y →
      ends f = (x, y) ∨ ends f = (y, x)) :
    (cd.vtx ⟨s + 3, by omega⟩ ≠ cd.vtx ⟨s + 2, by omega⟩ ∧
        cd.vtx ⟨s + 3, by omega⟩ ≠ cd.vtx ⟨s + 1, by omega⟩) ∧
      (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨s + 1, by omega⟩)) ends
          q).toBodyHinge.graph.IsLink (cd.edge ⟨s + 2, by omega⟩)
        (cd.vtx ⟨s + 2, by omega⟩) (cd.vtx ⟨s + 3, by omega⟩) ∧
      (∀ f x, (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨s + 1, by omega⟩)) ends
          q).toBodyHinge.graph.IsLink f (cd.vtx ⟨s + 2, by omega⟩) x →
          f = cd.edge ⟨s + 2, by omega⟩) ∧
      (∀ f x, (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨s + 1, by omega⟩)) ends
          q).toBodyHinge.graph.IsLink f x (cd.vtx ⟨s + 2, by omega⟩) →
          f = cd.edge ⟨s + 2, by omega⟩) ∧
      (∀ f x y, (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨s + 1, by omega⟩)) ends
          q).toBodyHinge.graph.IsLink f x y →
          x ≠ cd.vtx ⟨s + 1, by omega⟩ ∧ y ≠ cd.vtx ⟨s + 1, by omega⟩) ∧
      (∀ f x y, (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨s + 1, by omega⟩)) ends
          q).toBodyHinge.graph.IsLink f x y → x ≠ cd.vtx ⟨s + 2, by omega⟩ →
          y ≠ cd.vtx ⟨s + 2, by omega⟩ →
          (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨s + 2, by omega⟩)) ends'
            (fun p => q (Equiv.swap (cd.vtx ⟨s + 2, by omega⟩) (cd.vtx ⟨s + 1, by omega⟩) p.1,
              p.2))).toBodyHinge.graph.IsLink f x y ∧
            (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨s + 1, by omega⟩)) ends
              q).toBodyHinge.hingeRowBlock f ≤
              (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨s + 2, by omega⟩)) ends'
                (fun p => q (Equiv.swap (cd.vtx ⟨s + 2, by omega⟩) (cd.vtx ⟨s + 1, by omega⟩) p.1,
                  p.2))).toBodyHinge.hingeRowBlock f) := by
  classical
  -- The roles of the move: `v` is not a vertex of `Fv`, `a` moves to `v`, and `e_c = edge (s+2)`
  -- joins `a` to `c`.
  set v := cd.vtx ⟨s + 1, by omega⟩ with hv
  set a := cd.vtx ⟨s + 2, by omega⟩ with ha
  set c := cd.vtx ⟨s + 3, by omega⟩ with hc
  set e_c := cd.edge ⟨s + 2, by omega⟩ with he_c
  set Fv := (PanelHingeFramework.ofNormals (G.removeVertex v) ends q).toBodyHinge with hFv
  set qρ : α × Fin (k + 2) → K := fun p => q (Equiv.swap a v p.1, p.2) with hqρ
  set Fva := (PanelHingeFramework.ofNormals (G.removeVertex a) ends' qρ).toBodyHinge with hFva
  -- The three chain-vertex distinctness facts among `v, a, c`.
  have hca : c ≠ a := cd.vtx_ne (by omega) (by omega) (by omega)
  have hcv : c ≠ v := cd.vtx_ne (by omega) (by omega) (by omega)
  have hav : a ≠ v := cd.vtx_ne (by omega) (by omega) (by omega)
  -- `e_c = edge (s+2) = ac` survives `removeVertex v` (endpoints `a, c ≠ v`).
  have hG_ec : G.IsLink e_c a c := by
    have h := cd.isLink_edge ⟨s + 2, by omega⟩
    simpa only [Fin.castSucc_mk, Fin.succ_mk] using h
  have hFv_link_ec : Fv.graph.IsLink e_c a c := by
    rw [hFv, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]
    exact Graph.removeVertex_isLink.mpr ⟨hG_ec, hav, hcv⟩
  -- Degree-2 closure at `a` in `G − v`: the body `a = vtx (s+2)`'s `G`-edges are its predecessor
  -- `edge (s+1)` (to `v`, cut by the removal) and its successor `e_c = edge (s+2)` (to `c`); a
  -- `(G − v)`-link out of `a` cannot be the `edge (s+1)`-link (it would touch the removed `v`), so
  -- it is `e_c`.
  have hG_pred : G.IsLink (cd.edge ⟨s + 1, by omega⟩) a v := by
    have h := cd.isLink_edge ⟨s + 1, by omega⟩
    simpa only [Fin.castSucc_mk, Fin.succ_mk] using h.symm
  have hdeg2 : ∀ f x, Fv.graph.IsLink f a x → f = e_c := by
    intro f x hlink
    rw [hFv, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph] at hlink
    obtain ⟨hGlink, _, hxv⟩ := Graph.removeVertex_isLink.mp hlink
    -- `a = vtx (s+2)` is an interior chain vertex; `deg_two` (at index `s+2`) names its two edges:
    -- the predecessor `edge ((s+2)−1) = edge (s+1)` (the `(s+2)−1` reduces to `s+1` by `rfl`) and
    -- the successor `edge (s+2) = e_c`.
    have hd : f = cd.edge ⟨s + 1, by omega⟩ ∨ f = e_c :=
      cd.deg_two ⟨s + 2, by omega⟩ (by simp) f x
        (by simpa only [Fin.castSucc_mk, ← ha] using hGlink)
    rcases hd with hpred | hsucc
    · -- `f = edge (s+1)` would link `a` to `v` (the removed vertex), so `x = v`, contradiction.
      rw [hpred] at hGlink
      exact absurd (hG_pred.right_unique hGlink) (Ne.symm hxv)
    · exact hsucc
  have hdeg2r : ∀ f x, Fv.graph.IsLink f x a → f = e_c :=
    fun f x hlink => hdeg2 f x hlink.symm
  -- No `(G − v)`-link touches `v` at either endpoint.
  have hnov : ∀ f x y, Fv.graph.IsLink f x y → x ≠ v ∧ y ≠ v := by
    intro f x y hlink
    rw [hFv, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph] at hlink
    exact ⟨(Graph.removeVertex_isLink.mp hlink).2.1, (Graph.removeVertex_isLink.mp hlink).2.2⟩
  -- `htrans`: a link of `G − v` that does not meet `a` is a link of `G − a`, and the two frameworks
  -- have the same hinge there (the transposition fixes its ends, which are neither `a` nor `v`, and
  -- `ends'` agrees with `ends` off the two edges at `a`).
  have htrans : ∀ f x y, Fv.graph.IsLink f x y → x ≠ a → y ≠ a →
      Fva.graph.IsLink f x y ∧ Fv.hingeRowBlock f ≤ Fva.hingeRowBlock f := by
    intro f x y hlink hxa hya
    rw [hFv, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph] at hlink
    obtain ⟨hGflink, hxv, hyv⟩ := Graph.removeVertex_isLink.mp hlink
    -- `f` avoids both moved edges (its endpoints avoid `a` and `v`).
    have hfne_pred : f ≠ cd.edge ⟨s + 1, by omega⟩ := by
      rintro rfl
      rcases hG_pred.eq_and_eq_or_eq_and_eq hGflink with ⟨hh, _⟩ | ⟨hh, _⟩
      · exact hxa hh.symm
      · exact hya hh.symm
    have hfne_ec : f ≠ e_c := by
      rintro rfl
      rcases hG_ec.eq_and_eq_or_eq_and_eq hGflink with ⟨hh, _⟩ | ⟨hh, _⟩
      · exact hxa hh.symm
      · exact hya hh.symm
    refine ⟨?_, ?_⟩
    · rw [hFva, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph,
        Graph.removeVertex_isLink]
      exact ⟨hGflink, hxa, hya⟩
    · -- block agreement: the `f`-extensors at `Fva` and `Fv` coincide (`ends' f = ends f` off the
      -- moved edges, and the swap fixes the recorded endpoints `∉ {a, v}`, so `qρ = q` there).
      intro r hr
      rw [Fva.mem_hingeRowBlock_iff]
      rw [Fv.mem_hingeRowBlock_iff] at hr
      rw [hFva, PanelHingeFramework.toBodyHinge_supportExtensor,
        PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal,
        PanelHingeFramework.ofNormals_ends, hends'_off f hfne_pred hfne_ec]
      rw [hFv, PanelHingeFramework.toBodyHinge_supportExtensor,
        PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal,
        PanelHingeFramework.ofNormals_ends] at hr
      -- `ends f`'s two ends are `x` and `y` in some order (`hrec`), neither `a` (`hxa`, `hya`) nor
      -- `v` (`hxv`, `hyv`). The transposition `(a v)` fixes them, so `qρ = q` there, and the hinge
      -- of `Fva` is that of `Fv`, on which `r` vanishes (`hr`).
      rcases hrec f x y hlink with he | he <;> rw [he] at hr ⊢ <;>
        simp only [hqρ, Equiv.swap_apply_of_ne_of_ne hxa hxv,
          Equiv.swap_apply_of_ne_of_ne hya hyv] <;> exact hr
  exact ⟨⟨hca, hcv⟩, hFv_link_ec, hdeg2, hdeg2r, hnov, htrans⟩

/-! ## The move along a chain

Steps of `lem:case-III-chain-eq666`. `wstep v a c` is the move as a linear map (`wstep_apply`), and
`wstep_foldl_mem_span_rigidityRows` composes it along a chain of frameworks, whose normals may
change from one step to the next. -/

/-- **The move as a linear map** (a step of `lem:case-III-chain-eq666`): `wstep v a c` sends `φ` to
`(funLeft τ).dualMap φ − hingeRow v c (φ ∘ single a)`, the form `S ↦ φ (S ∘ τ) − x(S(v) − S(c))` of
`funLeft_dualMap_sub_acolumn_mem_span_rigidityRows`, for the transposition `τ` of `a` and `v` and
the restriction `x = φ ∘ single a`. The subtracted form is the composite
`(screwDiff v c).dualMap ∘ₗ (single a).dualMap`. -/
noncomputable def BodyHingeFramework.wstep [DecidableEq α] (v a c : α) :
    Module.Dual K (α → ScrewSpace K k) →ₗ[K] Module.Dual K (α → ScrewSpace K k) :=
  (LinearMap.funLeft K (ScrewSpace K k) (Equiv.swap a v)).dualMap
    - (screwDiff (k := k) (α := α) v c).dualMap.comp
        (LinearMap.single K (fun _ : α => ScrewSpace K k) a).dualMap

/-- `wstep v a c φ` is `(funLeft (a v)).dualMap φ − hingeRow v c (φ ∘ single a)`. -/
theorem BodyHingeFramework.wstep_apply [DecidableEq α] (v a c : α)
    (φ : Module.Dual K (α → ScrewSpace K k)) :
    BodyHingeFramework.wstep (k := k) v a c φ
      = (LinearMap.funLeft K (ScrewSpace K k) (Equiv.swap a v)).dualMap φ
        - BodyHingeFramework.hingeRow (k := k) (α := α) v c
            (φ.comp (LinearMap.single K (fun _ : α => ScrewSpace K k) a)) := by
  rw [BodyHingeFramework.wstep, LinearMap.sub_apply, LinearMap.comp_apply, hingeRow_eq_dualMap]; rfl

/-- **The move along a chain of frameworks, upwards** (a step of `lem:case-III-chain-eq666`): let
the frameworks `F s` and `F (s + 1)`, with the triple `bodies[s] = (v, a, c)` and the label `ec s`,
satisfy the hypotheses of `funLeft_dualMap_sub_acolumn_mem_span_rigidityRows` from `F s` to
`F (s + 1)`, for each `s` (`hstep`). Then the composite of the maps `wstep v a c` along `bodies`,
the first triple applied first, takes the span of the rows of `F 0` into that of `F bodies.length`.
The frameworks may have different normals. `shiftBodyListAsc_foldl_mem_span_rigidityRows`
(`CaseIII/Relabel/Chain.lean`) applies it along a chain, from `G − v₁` to `G − v_i`, with the steps
of `seedAdvance_wstep_hstep` and the normals renamed by one transposition at each step. The proof is
by induction on `bodies` from its end (`List.reverseRec`). -/
theorem BodyHingeFramework.wstep_foldl_mem_span_rigidityRows
    [DecidableEq α] (F : ℕ → BodyHingeFramework K k α β)
    (ec : ℕ → β) (bodies : List (α × α × α))
    (hstep : ∀ s, (hs : s < bodies.length) →
      (bodies[s].2.2 ≠ bodies[s].2.1 ∧ bodies[s].2.2 ≠ bodies[s].1) ∧
      (F s).graph.IsLink (ec s) bodies[s].2.1 bodies[s].2.2 ∧
      (∀ f x, (F s).graph.IsLink f bodies[s].2.1 x → f = ec s) ∧
      (∀ f x, (F s).graph.IsLink f x bodies[s].2.1 → f = ec s) ∧
      (∀ f x y, (F s).graph.IsLink f x y → x ≠ bodies[s].1 ∧ y ≠ bodies[s].1) ∧
      (∀ f x y, (F s).graph.IsLink f x y → x ≠ bodies[s].2.1 → y ≠ bodies[s].2.1 →
        (F (s + 1)).graph.IsLink f x y ∧ (F s).hingeRowBlock f ≤ (F (s + 1)).hingeRowBlock f))
    {φ : Module.Dual K (α → ScrewSpace K k)}
    (hφ : φ ∈ Submodule.span K (F 0).rigidityRows) :
    (bodies.foldl (fun T b => (BodyHingeFramework.wstep (k := k) b.1 b.2.1 b.2.2).comp T)
        LinearMap.id) φ
      ∈ Submodule.span K (F bodies.length).rigidityRows := by
  induction bodies using List.reverseRec with
  | nil => simpa using hφ
  | append_singleton rest b ih =>
    -- Head-first fold: `foldl (rest ++ [b]) = (wstep b) ∘ (foldl rest)`, last body `b` applied last
    -- (outermost). The inner fold transports `φ` (bottom of the chain, `span (F 0)`) up through
    -- `rest` to land in `span (F rest.length)`, then the last step rises `F rest.length → F (·+1)`.
    rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, LinearMap.comp_apply]
    have hb : (rest ++ [b])[rest.length]'(by simp) = b := by simp
    have hinner : (rest.foldl
        (fun T b => (BodyHingeFramework.wstep (k := k) b.1 b.2.1 b.2.2).comp T)
        LinearMap.id) φ ∈ Submodule.span K (F rest.length).rigidityRows := by
      refine ih (fun s hs => ?_)
      -- the inner steps re-index off `rest ++ [b]` via `getElem_append_left`.
      have hs' : s < (rest ++ [b]).length := by simp; omega
      have hidx : (rest ++ [b])[s]'hs' = rest[s] := by rw [List.getElem_append_left hs]
      have := hstep s hs'
      rwa [hidx] at this
    -- the last triple's move from `F rest.length` to `F (rest.length + 1)`.
    obtain ⟨⟨hca, hcv⟩, hlink_ec, hdeg2, hdeg2r, hnov, htrans⟩ := hstep rest.length (by simp)
    rw [hb] at hca hcv hlink_ec hdeg2 hdeg2r hnov htrans
    have hlast := BodyHingeFramework.funLeft_dualMap_sub_acolumn_mem_span_rigidityRows
      (Fv := F rest.length) (Fva := F (rest.length + 1))
      (v := b.1) (a := b.2.1) (c := b.2.2) (e_c := ec rest.length)
      hca hcv hlink_ec hdeg2 hdeg2r hnov htrans hinner
    rw [show (rest ++ [b]).length = rest.length + 1 by simp]
    simpa [BodyHingeFramework.wstep_apply] using hlast

end CombinatorialRigidity.Molecular
