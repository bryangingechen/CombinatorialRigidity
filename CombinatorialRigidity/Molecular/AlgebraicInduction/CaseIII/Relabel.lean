/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.AlgebraicInduction.CaseIII.Arms

/-!
# The algebraic induction — Case III relabel / split-off transport (the M₃ machinery)

Phase 22 (molecular-conjecture program). The M₃-arm layer of the Case-III block (`CaseIII/`
subdirectory; the post-Phase-22l molecular split round, `notes/Phase22l-perf.md`). The `ρ = (av)`
relabel apparatus (`ofNormals_relabel`, `rigidityRows_ofNormals_relabel`,
`hasGenericFullRankRealization_of_splitOff_relabel`) transporting the candidate `ρ`/`w` data across
the `a ↔ v` swap, the `acolumn`/`hingeRow` span bridges, and the M₃ arm closer
`case_III_arm_realization_M3` (built on the M₁ engine in `CaseIII/Arms`). Consumed by the dispatch
in `CaseIII/Realization`.

See `ROADMAP.md` §22 and the `sec:molecular-algebraic-induction-caseIII` dep-graph in
`blueprint/src/chapter/algebraic-induction/case-iii.tex`.
-/

namespace CombinatorialRigidity.Molecular

variable {k : ℕ}

open scoped Graph

variable {α β : Type*}

/-! ## Relabel / split-off transport (the M₃ machinery)

The `ρ = (av)` relabel apparatus (`lem:splitOff-ofNormals-relabel`,
`lem:splitOff-rigidityRows-relabel`) transporting the `ρ`/`w` data across the `a ↔ v` swap, the
`a`-column span bridges, and the M₃ arm closer (W9c, built on the M₁ engine W7). -/

/-- The edge permutation `σ = Equiv.swap e_b e₀ * Equiv.swap e₁ e_c` of the `ρ = (av)` relabel is
an involution. The two transpositions have disjoint supports (`{e_b, e₀}` and `{e₁, e_c}` are
disjoint by the four distinctness facts), so each cancels: `σ ∘ σ = id`. The shared
σ-cancellation step in `ofNormals_relabel` and `rigidityRows_ofNormals_relabel`. -/
private theorem hσσ_relabel {β : Type*} [DecidableEq β] {e_b e_c e₀ e₁ : β}
    (hbe₁ : e_b ≠ e₁) (hbec : e_b ≠ e_c) (h₀e₁ : e₀ ≠ e₁) (h₀ec : e₀ ≠ e_c) (f : β) :
    (Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) f) = f := by
  -- Pointwise: the two swaps act on disjoint pairs `{e_b, e₀}` and `{e₁, e_c}`.
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  split_ifs <;> simp_all

/-- **The general-`Equiv.Perm` framework-transport (CHAIN-2c-ii-β): an arbitrary vertex relabel
`ρ : Equiv.Perm α` (with edge relabel `σ : Equiv.Perm β`) intertwining two graphs transports the
`ofNormals` generic-realization data from one to the other** (`lem:case-III` general-`d`, KT 2011
§6.4.2 the index-shift isos eqs.~(6.54)–(6.56); Phase 23b). This is the involution-free
generalization of `ofNormals_relabel` (`ρ = Equiv.swap a v` / `σ = Equiv.swap e_b e₀ *
Equiv.swap e₁ e_c`), the load-bearing brick the all-`d` candidate-reduction arm
(`chainData_relabel_arm`, 2c-ii) instantiates at `ρ := cd.shiftPerm i` for each interior chain
candidate `i` — where KT's `ρᵢ` is a genuine `(i−1)`-cycle, **not** a transposition, so the
swap-specific transport must be re-derived for a general permutation.

The graph layer is abstracted into a single hypothesis: the two graphs `Gs` (source, KT's
`v₁`-base split) and `Gt` (target, the candidate-`i` split) are `(ρ, σ)`-related by
`hiso : Gt.IsLink e x y ↔ Gs.IsLink (σ e) (ρ x) (ρ y)` — exactly the shape `splitOff_isLink_relabel`
proves for the d=3 swap pair, and the shape the arm closer supplies per candidate (a
`shiftPerm`-relabel between two interior `splitOff`s). The rigidity region is abstracted into
`sr`/`st` with the forward vertex transport `hρst : u ∈ st → ρ u ∈ sr`.

The relabelled framework reads the original seed `q₀` at the `ρ`-shifted body
(`qρ p := q₀ (ρ p.1, p.2)`) and the original endpoints `ρ.symm`-shifted
(`endsσρ e := (ρ.symm (ends₀ (σ e)).1, ρ.symm (ends₀ (σ e)).2)`); the two `.symm`/forward choices
make the support extensors agree across the relabel (`Q'.supportExtensor f = Q.supportExtensor
(σ f)`) without an involution. The four conjuncts transport: **GP** by the injective `ρ`-reindex of
`q₀`; **rigidity** by pulling a motion `S` of the target back to `S ∘ ρ.symm` of the source (each
target link at `(ρ.symm p, ρ.symm p')` matches a source link `f p p'` through `hiso` at `σ.symm f`),
which `Q`'s rigidity on `sr` forces constant, then forward `ρ` carries the conclusion to `st`;
**link-recording** by the `.mp` direction of `hiso` through `ρ.symm`; **AlgIndep** by the injective
`ρ`-reindex. When `ρ`, `σ` are the d=3 swaps (`ρ.symm = ρ`, `σ.symm = σ`) this is exactly
`ofNormals_relabel`. -/
theorem PanelHingeFramework.ofNormals_relabel_perm {Gs Gt : Graph α β}
    (ρ : Equiv.Perm α) (σ : Equiv.Perm β) {sr st : Set α}
    (hiso : ∀ e x y, Gt.IsLink e x y ↔ Gs.IsLink (σ e) (ρ x) (ρ y))
    (hρst : ∀ u ∈ st, ρ u ∈ sr)
    {ends₀ : β → α × α} {q₀ : α × Fin (k + 2) → ℝ}
    (hQgp : (PanelHingeFramework.ofNormals Gs ends₀ q₀).IsGeneralPosition)
    (hQrig :
      (PanelHingeFramework.ofNormals Gs ends₀ q₀).toBodyHinge.IsInfinitesimallyRigidOn sr)
    (hQrec : ∀ e u w, Gs.IsLink e u w → ends₀ e = (u, w) ∨ ends₀ e = (w, u))
    (hQalg : AlgebraicIndependent ℚ (fun p : α × Fin (k + 2) => q₀ (p.1, p.2))) :
    (PanelHingeFramework.ofNormals Gt
        (fun e => (ρ.symm (ends₀ (σ e)).1, ρ.symm (ends₀ (σ e)).2))
        (fun p => q₀ (ρ p.1, p.2))).IsGeneralPosition ∧
    (PanelHingeFramework.ofNormals Gt
        (fun e => (ρ.symm (ends₀ (σ e)).1, ρ.symm (ends₀ (σ e)).2))
        (fun p => q₀ (ρ p.1, p.2))).toBodyHinge.IsInfinitesimallyRigidOn st ∧
    (∀ e u w, Gt.IsLink e u w →
        (ρ.symm (ends₀ (σ e)).1, ρ.symm (ends₀ (σ e)).2) = (u, w) ∨
        (ρ.symm (ends₀ (σ e)).1, ρ.symm (ends₀ (σ e)).2) = (w, u)) ∧
    AlgebraicIndependent ℚ (fun p : α × Fin (k + 2) => q₀ (ρ p.1, p.2)) := by
  set endsσρ : β → α × α := fun e => (ρ.symm (ends₀ (σ e)).1, ρ.symm (ends₀ (σ e)).2)
    with hendsσρ
  set qρ : α × Fin (k + 2) → ℝ := fun p => q₀ (ρ p.1, p.2) with hqρ
  set Q := PanelHingeFramework.ofNormals Gs ends₀ q₀ with hQ_def
  set Q' := PanelHingeFramework.ofNormals Gt endsσρ qρ with hQ'_def
  -- Q'.supportExtensor f = Q.supportExtensor (σ f): the relabelled framework's hinge at f reads
  -- q₀ at the ρ-shifted endpoints (the forward ρ in qρ cancelling the ρ.symm in endsσρ), i.e. the
  -- original hinge at (σ f). No involution needed.
  have h_supp : ∀ f : β,
      Q'.toBodyHinge.supportExtensor f = Q.toBodyHinge.supportExtensor (σ f) := by
    intro f
    simp only [hQ_def, hQ'_def, PanelHingeFramework.toBodyHinge_supportExtensor,
      PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal, hendsσρ, hqρ,
      Equiv.apply_symm_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  -- (1) General position: Q'.normal x = q₀ (ρ x, ·), reindexed by injective ρ.
  · intro x y hxy
    change LinearIndependent ℝ ![fun i => qρ (x, i), fun i => qρ (y, i)]
    have := hQgp (ρ x) (ρ y) (ρ.injective.ne hxy)
    simpa only [hQ_def, PanelHingeFramework.ofNormals_normal, hqρ] using this
  -- (2) Rigidity: any motion S of Q' yields the motion S ∘ ρ.symm of Q, constant on sr, hence
  --     (carried forward by ρ) S constant on st.
  · intro S hS u hu w hw
    -- S ∘ ρ.symm is an infinitesimal motion of Q.
    have hSmot : Q.toBodyHinge.IsInfinitesimalMotion (S ∘ ρ.symm) := by
      intro f x y hf
      simp only [hQ_def, PanelHingeFramework.toBodyHinge_graph,
        PanelHingeFramework.ofNormals_graph] at hf
      -- The source link f x y matches a target link at (ρ.symm x, ρ.symm y) via hiso at σ.symm f.
      have hfQ' : Gt.IsLink (σ.symm f) (ρ.symm x) (ρ.symm y) :=
        (hiso (σ.symm f) (ρ.symm x) (ρ.symm y)).mpr (by
          simp only [Equiv.apply_symm_apply]; exact hf)
      have harg : Q'.toBodyHinge.graph.IsLink (σ.symm f) (ρ.symm x) (ρ.symm y) := by
        simp only [hQ'_def, PanelHingeFramework.toBodyHinge_graph,
          PanelHingeFramework.ofNormals_graph]; exact hfQ'
      have hSc : Q'.toBodyHinge.hingeConstraint S (σ.symm f) (ρ.symm x) (ρ.symm y) :=
        hS (σ.symm f) (ρ.symm x) (ρ.symm y) harg
      -- hSc : S (ρ.symm x) - S (ρ.symm y) ∈ span {Q'.supportExtensor (σ.symm f)}
      --      = span {Q.supportExtensor f}.
      change (S ∘ ρ.symm) x - (S ∘ ρ.symm) y ∈
        Submodule.span ℝ {Q.toBodyHinge.supportExtensor f}
      rw [show Q.toBodyHinge.supportExtensor f = Q'.toBodyHinge.supportExtensor (σ.symm f) by
        rw [h_supp (σ.symm f), Equiv.apply_symm_apply]]
      exact hSc
    -- Apply Q's rigidity on sr at the forward-ρ images of u, w (which lie in sr by hρst).
    have hSmotConst := hQrig (S ∘ ρ.symm) hSmot (ρ u) (hρst u hu) (ρ w) (hρst w hw)
    simp only [Function.comp, Equiv.symm_apply_apply] at hSmotConst
    exact hSmotConst
  -- (3) Link-recording: every link of Gt has endpoints recorded by endsσρ.
  · intro e' u w he'
    have hfQ : Gs.IsLink (σ e') (ρ u) (ρ w) := (hiso e' u w).mp he'
    rcases hQrec (σ e') (ρ u) (ρ w) hfQ with h1 | h1
    · refine Or.inl ?_
      change (ρ.symm (ends₀ (σ e')).1, ρ.symm (ends₀ (σ e')).2) = (u, w)
      rw [h1]; exact Prod.ext (ρ.symm_apply_apply u) (ρ.symm_apply_apply w)
    · refine Or.inr ?_
      change (ρ.symm (ends₀ (σ e')).1, ρ.symm (ends₀ (σ e')).2) = (w, u)
      rw [h1]; exact Prod.ext (ρ.symm_apply_apply w) (ρ.symm_apply_apply u)
  -- (4) AlgebraicIndependent ℚ: qρ is an injective ρ-reindex of q₀.
  · change AlgebraicIndependent ℚ (fun p : α × Fin (k + 2) => q₀ (ρ p.1, p.2))
    have := hQalg.comp (fun p : α × Fin (k + 2) => (ρ p.1, p.2))
        (fun p q h => Prod.ext (ρ.injective (Prod.ext_iff.mp h).1) (Prod.ext_iff.mp h).2)
    simpa only [Function.comp] using this

/-- **G4c-ii (fixed-seed form): the `ρ = (av)` relabel transports the concrete v-split `ofNormals`
data to the concrete a-split `ofNormals` data at the SAME seed `q₀ ∘ ρ`**
(`lem:splitOff-ofNormals-relabel`, KT 2011 eq. (6.31) framework side, Phase 22h).

This is the transport in the **producer's direction**: the induction hypothesis realizes the
`v`-split `G.splitOff v a b e₀` (`G_v^{ab}` in KT) concretely as `ofNormals (G.splitOff v a b e₀)
ends₀ q₀` with the four generic-realization conjuncts (general position, rigidity on `V(G)∖{v}`,
link-recording, `AlgebraicIndependent ℚ`), and the `M₃` arm of the Case-III producer needs the SAME
data on the `a`-split `G.splitOff a v c e₁` (`G_a^{vc}`) at the SAME seed transported by
`ρ = Equiv.swap a v` — *not* a fresh existential realization (an independent realization has a
different seed, hence different `λ`s and a different `r̂`, collapsing the eq.-(6.44) trichotomy;
KT §6.4.1, eqs. (6.31)/(6.44)). So the lemma is stated at the `ofNormals` level, naming the
relabelled construction explicitly with

* edge permutation `σ = Equiv.swap e_b e₀ * Equiv.swap e₁ e_c`,
* seed `qρ (x, i) := q₀ (ρ x, i)` (the original seed reindexed by `ρ`),
* selector `endsσρ e := (ρ (ends₀ (σ e)).1, ρ (ends₀ (σ e)).2)`,

so the producer and `G4d-ii` can name the relabelled framework `ofNormals (G.splitOff a v c e₁)
endsσρ qρ` directly (its row-space correspondence is `rigidityRows_ofNormals_relabel`, below).

The four conjuncts transport via the graph-level iso `G4c-i` (`Graph.splitOff_isLink_relabel`),
which `ρ`/`σ` intertwine. **GP:** `qρ`'s normals are `q₀`'s reindexed by the injective `ρ`.
**Rigidity:** a motion `S` of the `a`-split framework pulls back to the motion `S ∘ ρ` of the
`v`-split framework (using `splitOff_isLink_relabel` to move each `a`-split link to a `v`-split
link, and the support-extensor equality across the two `ofNormals` terms); the `v`-split rigidity
on `V(G)∖{v}` then forces `S` constant on `V(G)∖{a}` since `ρ` maps `V(G)∖{a} → V(G)∖{v}`
bijectively. **Link-recording:** each `a`-split link maps forward to a `v`-split link whose
endpoints `ends₀` records, transported through `ρ`. **AlgIndep:** `qρ` is an injective `ρ`-reindex
of `q₀`. -/
theorem PanelHingeFramework.ofNormals_relabel [DecidableEq α] [DecidableEq β]
    {G : Graph α β}
    {v a b c : α} {eₐ e_b e_c e₀ e₁ : β}
    (hG_ea : G.IsLink eₐ v a) (hG_eb : G.IsLink e_b v b) (hG_ec : G.IsLink e_c a c)
    (hav : a ≠ v) (hbv : b ≠ v) (hcv : c ≠ v) (hca : c ≠ a)
    (heab : eₐ ≠ e_b) (heac : eₐ ≠ e_c)
    (hclv : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    (hcla : ∀ e x, G.IsLink e a x → e = eₐ ∨ e = e_c)
    (he₀ : e₀ ∉ E(G)) (he₁ : e₁ ∉ E(G)) (he₁₀ : e₁ ≠ e₀)
    {ends₀ : β → α × α} {q₀ : α × Fin (k + 2) → ℝ}
    (hQgp : (PanelHingeFramework.ofNormals (G.splitOff v a b e₀) ends₀ q₀).IsGeneralPosition)
    (hQrig :
      (PanelHingeFramework.ofNormals (G.splitOff v a b e₀) ends₀
        q₀).toBodyHinge.IsInfinitesimallyRigidOn V(G.splitOff v a b e₀))
    (hQrec : ∀ e u w, (G.splitOff v a b e₀).IsLink e u w →
        ends₀ e = (u, w) ∨ ends₀ e = (w, u))
    (hQalg : AlgebraicIndependent ℚ (fun p : α × Fin (k + 2) => q₀ (p.1, p.2))) :
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
          Equiv.swap a v (ends₀ ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)).2) = (w, u)) ∧
    AlgebraicIndependent ℚ
      (fun p : α × Fin (k + 2) => q₀ (Equiv.swap a v p.1, p.2)) := by
  classical
  set ρ : Equiv.Perm α := Equiv.swap a v with hρ_def
  set σ : Equiv.Perm β := Equiv.swap e_b e₀ * Equiv.swap e₁ e_c with hσ_def
  set endsσρ : β → α × α := fun e => (ρ (ends₀ (σ e)).1, ρ (ends₀ (σ e)).2) with hendsσρ
  set qρ : α × Fin (k + 2) → ℝ := fun p => q₀ (ρ p.1, p.2) with hqρ
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
    refine Set.mem_diff_of_mem (hρmemV u hu.1) ?_
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
  refine ⟨?_, ?_, ?_, ?_⟩
  -- (1) General position: Q'.normal x = q₀ (ρ x, ·), reindexed by injective ρ.
  · intro x y hxy
    change LinearIndependent ℝ ![fun i => qρ (x, i), fun i => qρ (y, i)]
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
          heab heac hclv hcla he₀ he₁ he₁₀).mpr (by rw [hσσ f, hρρ, hρρ]; exact hf)
      have harg : Q'.toBodyHinge.graph.IsLink (σ f) (ρ x) (ρ y) := by
        simp only [hQ'_def, PanelHingeFramework.toBodyHinge_graph,
          PanelHingeFramework.ofNormals_graph]; exact hfQ'
      have hSc : Q'.toBodyHinge.hingeConstraint S (σ f) (ρ x) (ρ y) := hS (σ f) (ρ x) (ρ y) harg
      -- hSc : S (ρ x) - S (ρ y) ∈ span {Q'.supportExtensor (σ f)} = span {Q.supportExtensor f}.
      change (S ∘ ρ) x - (S ∘ ρ) y ∈ Submodule.span ℝ {Q.toBodyHinge.supportExtensor f}
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
        heab heac hclv hcla he₀ he₁ he₁₀).mp he'
    rcases hQrec (σ e') (ρ u) (ρ w) hfQ with h1 | h1
    · refine Or.inl ?_
      change (ρ (ends₀ (σ e')).1, ρ (ends₀ (σ e')).2) = (u, w)
      rw [h1]; exact Prod.ext (hρρ u) (hρρ w)
    · refine Or.inr ?_
      change (ρ (ends₀ (σ e')).1, ρ (ends₀ (σ e')).2) = (w, u)
      rw [h1]; exact Prod.ext (hρρ w) (hρρ u)
  -- (4) AlgebraicIndependent ℚ: qρ is an injective ρ-reindex of q₀.
  · change AlgebraicIndependent ℚ (fun p : α × Fin (k + 2) => q₀ (ρ p.1, p.2))
    have := hQalg.comp (fun p : α × Fin (k + 2) => (ρ p.1, p.2))
        (fun p q h => Prod.ext (ρ.injective (Prod.ext_iff.mp h).1) (Prod.ext_iff.mp h).2)
    simpa only [Function.comp] using this

/-- **G4c-ii (row-space correspondence): the relabelled `a`-split framework's rigidity rows are the
image of the `v`-split framework's under the dual of the `ρ`-coordinate permutation** (the
deliverable `G4d-ii` consumes; KT 2011 eqs. (6.31)/(6.44), Phase 22h).

The coordinate-relabel map `LinearMap.funLeft ℝ (ScrewSpace k) ρ : (α → ScrewSpace k) →ₗ[ℝ]
(α → ScrewSpace k)`, `S ↦ S ∘ ρ`, has dual `(funLeft ℝ _ ρ).dualMap` sending `φ ↦ φ ∘ (· ∘ ρ)`.
Under it, each rigidity row `hingeRow u w r` of the `a`-split framework `ofNormals (G.splitOff a v c
e₁) endsσρ qρ` is the image of the `v`-split framework's row `hingeRow (ρ u) (ρ w) r` — because
`ρ ∘ ρ = id`, `(funLeft ρ).dualMap (hingeRow (ρ u) (ρ w) r) = hingeRow u w r`. As `G4c-i`
(`Graph.splitOff_isLink_relabel`) puts the two graphs' links in `ρ`-correspondence and the
hinge-row blocks at corresponding edges coincide (the same support extensor, by the same `q₀`
reindex as in `ofNormals_relabel`), the two rigidity-row *sets* correspond exactly under
`(funLeft ρ).dualMap`. This is the row-space identity the eq.-(6.44) `M₃` candidate-row membership
step transports across. -/
theorem PanelHingeFramework.rigidityRows_ofNormals_relabel [DecidableEq α] [DecidableEq β]
    {G : Graph α β}
    {v a b c : α} {eₐ e_b e_c e₀ e₁ : β}
    (hG_ea : G.IsLink eₐ v a) (hG_eb : G.IsLink e_b v b) (hG_ec : G.IsLink e_c a c)
    (hav : a ≠ v) (hbv : b ≠ v) (hcv : c ≠ v) (hca : c ≠ a)
    (heab : eₐ ≠ e_b) (heac : eₐ ≠ e_c)
    (hclv : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    (hcla : ∀ e x, G.IsLink e a x → e = eₐ ∨ e = e_c)
    (he₀ : e₀ ∉ E(G)) (he₁ : e₁ ∉ E(G)) (he₁₀ : e₁ ≠ e₀)
    (ends₀ : β → α × α) (q₀ : α × Fin (k + 2) → ℝ) :
    (PanelHingeFramework.ofNormals (G.splitOff a v c e₁)
        (fun e => (Equiv.swap a v (ends₀ ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)).1,
          Equiv.swap a v (ends₀ ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)).2))
        (fun p => q₀ (Equiv.swap a v p.1, p.2))).toBodyHinge.rigidityRows =
      (LinearMap.funLeft ℝ (ScrewSpace k) (Equiv.swap a v)).dualMap ''
        (PanelHingeFramework.ofNormals (G.splitOff v a b e₀) ends₀
          q₀).toBodyHinge.rigidityRows := by
  classical
  set ρ : Equiv.Perm α := Equiv.swap a v with hρ_def
  set σ : Equiv.Perm β := Equiv.swap e_b e₀ * Equiv.swap e₁ e_c with hσ_def
  set endsσρ : β → α × α := fun e => (ρ (ends₀ (σ e)).1, ρ (ends₀ (σ e)).2) with hendsσρ
  set qρ : α × Fin (k + 2) → ℝ := fun p => q₀ (ρ p.1, p.2) with hqρ
  have hρρ : ∀ x : α, ρ (ρ x) = x := fun x => Equiv.swap_apply_self a v x
  -- (funLeft ρ).dualMap (hingeRow (ρ u) (ρ w) r) = hingeRow u w r.
  have hdual : ∀ (u w : α) (r : Module.Dual ℝ (ScrewSpace k)),
      (LinearMap.funLeft ℝ (ScrewSpace k) ρ).dualMap
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
        heab heac hclv hcla he₀ he₁ he₁₀ (e := e') (x := u) (y := w)).mp
      simp only [hQ'_def, PanelHingeFramework.toBodyHinge_graph,
        PanelHingeFramework.ofNormals_graph] at hlink'
      simpa only [hQ_def, PanelHingeFramework.toBodyHinge_graph,
        PanelHingeFramework.ofNormals_graph] using hmp hlink'
    · rw [← hblock e']; exact hr
  -- ⊇ : every image of a v-split row is an a-split row.
  · rintro φ ⟨ψ, ⟨e', u, w, hlink, r, hr, rfl⟩, rfl⟩
    refine ⟨σ e', ρ u, ρ w, ?_, r, ?_, ?_⟩
    · have hmpr := (_root_.Graph.splitOff_isLink_relabel hG_ea hG_eb hG_ec hav hbv hcv hca
        heab heac hclv hcla he₀ he₁ he₁₀ (e := σ e') (x := ρ u) (y := ρ w)).mpr
      simp only [hQ_def, PanelHingeFramework.toBodyHinge_graph,
        PanelHingeFramework.ofNormals_graph] at hlink
      simp only [hQ'_def, PanelHingeFramework.toBodyHinge_graph,
        PanelHingeFramework.ofNormals_graph]
      exact hmpr (by rw [hσσ e', hρρ, hρρ]; exact hlink)
    · rw [hblock (σ e'), hσσ e']; exact hr
    · have := hdual (ρ u) (ρ w) r
      rwa [hρρ, hρρ] at this

/-- **G4c-ii (existential corollary): the producer-direction transport at the level of the
existential motive** (`lem:splitOff-ofNormals-relabel`, KT 2011 eq. (6.31); Phase 22h). A short
consequence of the fixed-seed `ofNormals_relabel`: a generic full-rank realization of the `v`-split
`G.splitOff v a b e₀` (`G_v^{ab}`) transports to one of the `a`-split `G.splitOff a v c e₁`
(`G_a^{vc}`) at the relabelled seed `q₀ ∘ ρ`. This is the *producer's* direction (it consumes the
IH at the `v`-split, the form `theorem_55_all_k`'s `hsplitZero` branch supplies, and yields the
`a`-split datum the `M₃` arm needs); the fixed-seed form above is the load-bearing one, since the
producer reads the concrete `ofNormals` framework and its row-space correspondence
(`rigidityRows_ofNormals_relabel`), not the bare existential. -/
theorem PanelHingeFramework.hasGenericFullRankRealization_of_splitOff_relabel [Finite α]
    {G : Graph α β}
    {v a b c : α} {eₐ e_b e_c e₀ e₁ : β}
    (hG_ea : G.IsLink eₐ v a) (hG_eb : G.IsLink e_b v b) (hG_ec : G.IsLink e_c a c)
    (hav : a ≠ v) (hbv : b ≠ v) (hcv : c ≠ v) (hca : c ≠ a)
    (heab : eₐ ≠ e_b) (heac : eₐ ≠ e_c)
    (hclv : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    (hcla : ∀ e x, G.IsLink e a x → e = eₐ ∨ e = e_c)
    (he₀ : e₀ ∉ E(G)) (he₁ : e₁ ∉ E(G)) (he₁₀ : e₁ ≠ e₀)
    (n : ℕ) (hdef_in : (G.splitOff v a b e₀).deficiency n = 0)
    (hdef_out : (G.splitOff a v c e₁).deficiency n = 0)
    (hQ : PanelHingeFramework.HasGenericFullRankRealization k n (G.splitOff v a b e₀)) :
    PanelHingeFramework.HasGenericFullRankRealization k n (G.splitOff a v c e₁) := by
  classical
  obtain ⟨Q, hQg, hQgp, hQrank, hQrec, hQalg⟩ := hQ
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
  obtain ⟨hgp, hrig_out, hrec, halg⟩ := PanelHingeFramework.ofNormals_relabel hG_ea hG_eb hG_ec
    hav hbv hcv hca heab heac hclv hcla he₀ he₁ he₁₀ hgp' hrig' hrec' hQalg
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
      (Module.finrank ℝ (Submodule.span ℝ F_out.toBodyHinge.rigidityRows) : ℤ) =
      screwDim k * ((V(G.splitOff a v c e₁).ncard : ℤ) - 1) -
      (G.splitOff a v c e₁).deficiency n := by
    rw [hdef_out, sub_zero]
    have hVncard_out : F_out.toBodyHinge.graph.vertexSet.ncard = V(G.splitOff a v c e₁).ncard := by
      rw [PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]
    rw [← hVncard_out]
    rw [← hVncard_out] at h1_out
    zify [h1_out] at hW2 ⊢; exact_mod_cast hW2
  -- Repackage the link conjunct from Prod-equality form into the motive's And/Or form.
  refine ⟨_, rfl, hgp, hrank_out, fun e u w he => ?_, halg⟩
  rcases hrec e u w he with h1 | h1
  · exact Or.inl ⟨by rw [PanelHingeFramework.ofNormals_ends, (Prod.ext_iff.mp h1).1],
      by rw [PanelHingeFramework.ofNormals_ends, (Prod.ext_iff.mp h1).2]⟩
  · exact Or.inr ⟨by rw [PanelHingeFramework.ofNormals_ends, (Prod.ext_iff.mp h1).1],
      by rw [PanelHingeFramework.ofNormals_ends, (Prod.ext_iff.mp h1).2]⟩

/-- **G4c-ii (membership transport): a `v`-split rigidity-row-span member transports to the
relabelled `a`-split rigidity-row span under the dual of the `ρ`-coordinate permutation**
(`lem:splitOff-rigidityRows-relabel`, the membership corollary of `rigidityRows_ofNormals_relabel`;
KT 2011 eqs.~(6.31)/(6.44), Phase 22h). The `M₃` arm of the Case-III producer reads its candidate
row off the `v`-split framework `R(G_v^{ab}, q)` (G4d-ii gives `hingeRow a c r̂ ∈ span` there), but
the `a`-split realization it actually places is `ofNormals (G.splitOff a v c e₁) endsσρ qρ`. This is
the transport across the relabel: since the two frameworks' rigidity-row *sets* correspond exactly
under `(funLeft ρ).dualMap` (`rigidityRows_ofNormals_relabel`), the span of one is the
`Submodule.map`-image of the span of the other (`Submodule.span_image`), so any `φ` in the `v`-split
span sends to `(funLeft ρ).dualMap φ` in the `a`-split span (`Submodule.mem_map_of_mem`). Composed
with `hingeRow_funLeft_dualMap` (which evaluates `(funLeft ρ).dualMap (hingeRow u w r) =
hingeRow (ρ u) (ρ w) r` for the involution `ρ = (a v)`), this is exactly the `M₃` candidate-row
membership the arm needs: `hingeRow a c r̂ ∈ span(v-split) ↦ hingeRow v c r̂ ∈ span(a-split)`
(`ρ a = v`, `ρ c = c`). Graph-free over the carrier beyond the relabel lemma it invokes. -/
theorem PanelHingeFramework.mem_span_rigidityRows_ofNormals_relabel [DecidableEq α] [DecidableEq β]
    {G : Graph α β}
    {v a b c : α} {eₐ e_b e_c e₀ e₁ : β}
    (hG_ea : G.IsLink eₐ v a) (hG_eb : G.IsLink e_b v b) (hG_ec : G.IsLink e_c a c)
    (hav : a ≠ v) (hbv : b ≠ v) (hcv : c ≠ v) (hca : c ≠ a)
    (heab : eₐ ≠ e_b) (heac : eₐ ≠ e_c)
    (hclv : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    (hcla : ∀ e x, G.IsLink e a x → e = eₐ ∨ e = e_c)
    (he₀ : e₀ ∉ E(G)) (he₁ : e₁ ∉ E(G)) (he₁₀ : e₁ ≠ e₀)
    (ends₀ : β → α × α) (q₀ : α × Fin (k + 2) → ℝ)
    {φ : Module.Dual ℝ (α → ScrewSpace k)}
    (hφ : φ ∈ Submodule.span ℝ
      (PanelHingeFramework.ofNormals (G.splitOff v a b e₀) ends₀ q₀).toBodyHinge.rigidityRows) :
    (LinearMap.funLeft ℝ (ScrewSpace k) (Equiv.swap a v)).dualMap φ ∈ Submodule.span ℝ
      (PanelHingeFramework.ofNormals (G.splitOff a v c e₁)
        (fun e => (Equiv.swap a v (ends₀ ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)).1,
          Equiv.swap a v (ends₀ ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)).2))
        (fun p => q₀ (Equiv.swap a v p.1, p.2))).toBodyHinge.rigidityRows := by
  rw [PanelHingeFramework.rigidityRows_ofNormals_relabel hG_ea hG_eb hG_ec hav hbv hcv hca
      heab heac hclv hcla he₀ he₁ he₁₀ ends₀ q₀, Submodule.span_image]
  exact Submodule.mem_map_of_mem hφ

/-- **W9a — the short-circuit-free relabel transport** (the `M₃` candidate/bottom-row span-induction
core, design §1.52(b); Katoh–Tanigawa 2011 §6.4.1 eqs.~(6.31)/(6.39), Phase 22h). The G4d-i sibling
that transports a vector in the span of the `v`-split framework `Fv`'s rigidity rows across the
vertex relabel `(a v)` *with the `e_c`-content stripped*: for any `φ ∈ span Fv.rigidityRows`,
$$(\mathrm{funLeft}\,(a\,v)).\mathrm{dualMap}\,\varphi
\;-\; \mathrm{hingeRow}\;v\;c\;(\varphi\circ\mathrm{single}\,a)
\;\in\; \mathrm{span}\;F_{va}.\mathrm{rigidityRows},$$
where `Fva` is a second framework (concretely the `G − a` framework) whose links and hinge-row
blocks agree with `Fv` off body `a` (`htrans`).

This is the relabel half of KT's eq.~(6.39) row correspondence read functional-wise. Under the
degree-2-at-`a` hypothesis (the only `Fv`-links touching `a` are `e_c = ac`), the relabel
`(funLeft (a v)).dualMap` of a generator `hingeRow x y r` lands in the target row span after the
subtracted `a`-column hinge row cancels the `e_c`-content: a generator at `e_c` (endpoint `a`) maps
to `hingeRow v c r`, which the subtracted `hingeRow v c (φ ∘ single a) = hingeRow v c (±r)` exactly
cancels; an off-`a` generator is fixed by the swap (its endpoints avoid both `a` and `v`) and
survives into `Fva`'s rows via `htrans`. The candidate-functional `hρGv`-slot of the `M₃` arm (W9c)
reads this at `φ := hingeRow a b ρ`. Unlike the superseded `mem_span_rigidityRows_ofNormals_relabel`
(whose `a`-split span target cannot strip the short-circuit `e₁`-block post hoc), this concludes
directly in the `G − a`-row span. Graph-free over the carrier (`rigidityRows`/`hingeRowBlock` read
only `graph`/`hingeRowBlock`), so the `ofNormals` defeq trap (TACTICS-QUIRKS §38) does not bite. -/
theorem BodyHingeFramework.funLeft_dualMap_sub_acolumn_mem_span_rigidityRows
    [DecidableEq α] {Fv Fva : BodyHingeFramework k α β}
    {v a c : α} {e_c : β}
    (hca : c ≠ a) (hcv : c ≠ v)
    (hlink_ec : Fv.graph.IsLink e_c a c)
    (hdeg2 : ∀ f x, Fv.graph.IsLink f a x → f = e_c)
    (hdeg2r : ∀ f x, Fv.graph.IsLink f x a → f = e_c)
    (hnov : ∀ f x y, Fv.graph.IsLink f x y → x ≠ v ∧ y ≠ v)
    (htrans : ∀ f x y, Fv.graph.IsLink f x y → x ≠ a → y ≠ a →
      Fva.graph.IsLink f x y ∧ Fv.hingeRowBlock f ≤ Fva.hingeRowBlock f)
    {φ : Module.Dual ℝ (α → ScrewSpace k)}
    (hφ : φ ∈ Submodule.span ℝ Fv.rigidityRows) :
    (LinearMap.funLeft ℝ (ScrewSpace k) (Equiv.swap a v)).dualMap φ
        - BodyHingeFramework.hingeRow (k := k) (α := α) v c
            (φ.comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a))
      ∈ Submodule.span ℝ Fva.rigidityRows := by
  -- Bundle the transport as a single linear map `T` so the `span_induction` predicate stays
  -- light (`T ψ ∈ span …`) — keeping the heavy `Module.Dual (α → ScrewSpace k)` terms out of
  -- the predicate, which is what the `add`/`smul`/`zero` cases discharge mechanically by
  -- `map_add`/`map_smul`/`map_zero`. `hingeRow v c (· ∘ single a)` is the linear composite
  -- `(screwDiff v c).dualMap ∘ₗ (single a).dualMap` (both `hingeRow_eq_dualMap` and
  -- `LinearMap.dualMap` of `single` unfold `∘ₗ` to the same `comp`).
  set T : Module.Dual ℝ (α → ScrewSpace k) →ₗ[ℝ] Module.Dual ℝ (α → ScrewSpace k) :=
    (LinearMap.funLeft ℝ (ScrewSpace k) (Equiv.swap a v)).dualMap
      - (screwDiff (k := k) (α := α) v c).dualMap.comp
          (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a).dualMap with hT
  -- `T ψ` is the transported difference, for every `ψ` (the `hingeRow`/`comp` forms agree with
  -- the `dualMap` composites by `rfl`).
  have hTapply : ∀ ψ : Module.Dual ℝ (α → ScrewSpace k),
      T ψ = (LinearMap.funLeft ℝ (ScrewSpace k) (Equiv.swap a v)).dualMap ψ
        - BodyHingeFramework.hingeRow (k := k) (α := α) v c
            (ψ.comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a)) := fun ψ => by
    rw [hT, LinearMap.sub_apply, LinearMap.comp_apply, hingeRow_eq_dualMap]; rfl
  rw [← hTapply]
  -- `span_induction` on `hφ` with the light predicate `T ψ ∈ span Fva.rigidityRows`.
  apply Submodule.span_induction
    (p := fun ψ _ => T ψ ∈ Submodule.span ℝ Fva.rigidityRows) _ _ _ _ hφ
  · -- generator case: ψ = hingeRow x y r at a link f, r ∈ Fv.hingeRowBlock f.
    -- Unfold `T` to the `dualMap` form (not via `hTapply`): keeping the subtracted term as
    -- `(screwDiff v c).dualMap (…)` lets `map_zero` close the off-case without producing the
    -- heavy nested `hingeRow v c 0` term whose `rw`-motive abstraction trips §38.
    rintro ψ ⟨f, x, y, hlink, r, hr, rfl⟩
    rw [hT, LinearMap.sub_apply, LinearMap.comp_apply,
      BodyHingeFramework.hingeRow_funLeft_dualMap,
      show (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a).dualMap (hingeRow x y r)
          = (hingeRow x y r).comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a) from rfl]
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
      · -- x ≠ a, y ≠ a: the swap fixes both endpoints (they also avoid v by hnov), the a-column
        -- is 0, so the result is the generator itself — a genuine Fva-row via htrans.
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

/-- **W9a composes — the two-step relabel transport** (the cycle-W9a induction step, CHAIN-2c-ii
route B, `notes/Phase23-design.md` §(o″)). Two single-swap W9a transports compose into one transport
across the composite relabel `(a₂ v₂) ∘ (a₁ v₁)`, subtracting *two* a-columns — one per moved
degree-2 body. Concretely: if W9a carries `span Fv.rigidityRows` to `span F₁.rigidityRows` across
the swap `(a₁ v₁)` (stripping body `a₁`'s `e_{c₁} = a₁c₁` column), and a second W9a carries
`span F₁.rigidityRows` to `span Fva.rigidityRows` across `(a₂ v₂)` (stripping `a₂`'s column), then
for any `φ ∈ span Fv.rigidityRows`,
$$(\mathrm{funLeft}\,((a_2\,v_2)\circ(a_1\,v_1))).\mathrm{dualMap}\,\varphi
\;-\;\Bigl[(\mathrm{funLeft}\,(a_2\,v_2)).\mathrm{dualMap}
       \bigl(\mathrm{hingeRow}\;v_1\;c_1\;(\varphi\circ\mathrm{single}\,a_1)\bigr)
   \;+\;\mathrm{hingeRow}\;v_2\;c_2\;((T_1\varphi)\circ\mathrm{single}\,a_2)\Bigr]
\;\in\;\mathrm{span}\;F_{va}.\mathrm{rigidityRows},$$
where `T₁ φ := (funLeft (a₁ v₁)).dualMap φ − hingeRow v₁ c₁ (φ ∘ single a₁)` is the first step's
output (the intermediate vector in `span F₁`). The proof is pure linearity over the two single-step
memberships: feed `T₁ φ ∈ span F₁` (the first W9a) to the second W9a, then rewrite the nested
`(funLeft (a₂ v₂)).dualMap ∘ (funLeft (a₁ v₁)).dualMap` to the composite relabel
`(funLeft ((a₂ v₂) ∘ (a₁ v₁))).dualMap` via `LinearMap.funLeft_comp` (a `funLeft`-contravariance the
dual map straightens). This is the genuinely-new content route B's cycle-W9a needs (the per-step
a-column subtractions *do* compose cleanly — the design §(o″) telescoping concern); the cycle of
`i − 1` adjacent degree-2 bodies iterates this step along the head-peel
`shiftPerm i = (vtx 1 vtx 2) * (tail formPerm)` (`shiftPerm_eq_swap_mul`). Graph-free over the
carrier, inheriting W9a's `§38`-clean discipline. -/
theorem BodyHingeFramework.funLeft_dualMap_sub_acolumn_comp_mem_span_rigidityRows
    [DecidableEq α] {Fv F₁ Fva : BodyHingeFramework k α β}
    {v₁ a₁ c₁ v₂ a₂ c₂ : α} {e_c₁ e_c₂ : β}
    (hca₁ : c₁ ≠ a₁) (hcv₁ : c₁ ≠ v₁)
    (hlink_ec₁ : Fv.graph.IsLink e_c₁ a₁ c₁)
    (hdeg2₁ : ∀ f x, Fv.graph.IsLink f a₁ x → f = e_c₁)
    (hdeg2r₁ : ∀ f x, Fv.graph.IsLink f x a₁ → f = e_c₁)
    (hnov₁ : ∀ f x y, Fv.graph.IsLink f x y → x ≠ v₁ ∧ y ≠ v₁)
    (htrans₁ : ∀ f x y, Fv.graph.IsLink f x y → x ≠ a₁ → y ≠ a₁ →
      F₁.graph.IsLink f x y ∧ Fv.hingeRowBlock f ≤ F₁.hingeRowBlock f)
    (hca₂ : c₂ ≠ a₂) (hcv₂ : c₂ ≠ v₂)
    (hlink_ec₂ : F₁.graph.IsLink e_c₂ a₂ c₂)
    (hdeg2₂ : ∀ f x, F₁.graph.IsLink f a₂ x → f = e_c₂)
    (hdeg2r₂ : ∀ f x, F₁.graph.IsLink f x a₂ → f = e_c₂)
    (hnov₂ : ∀ f x y, F₁.graph.IsLink f x y → x ≠ v₂ ∧ y ≠ v₂)
    (htrans₂ : ∀ f x y, F₁.graph.IsLink f x y → x ≠ a₂ → y ≠ a₂ →
      Fva.graph.IsLink f x y ∧ F₁.hingeRowBlock f ≤ Fva.hingeRowBlock f)
    {φ : Module.Dual ℝ (α → ScrewSpace k)}
    (hφ : φ ∈ Submodule.span ℝ Fv.rigidityRows) :
    (LinearMap.funLeft ℝ (ScrewSpace k) (Equiv.swap a₂ v₂ ∘ Equiv.swap a₁ v₁)).dualMap φ
        - ((LinearMap.funLeft ℝ (ScrewSpace k) (Equiv.swap a₂ v₂)).dualMap
              (BodyHingeFramework.hingeRow (k := k) (α := α) v₁ c₁
                (φ.comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a₁)))
            + BodyHingeFramework.hingeRow (k := k) (α := α) v₂ c₂
                (((LinearMap.funLeft ℝ (ScrewSpace k) (Equiv.swap a₁ v₁)).dualMap φ
                    - BodyHingeFramework.hingeRow (k := k) (α := α) v₁ c₁
                        (φ.comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a₁))).comp
                  (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a₂)))
      ∈ Submodule.span ℝ Fva.rigidityRows := by
  -- The first W9a transport: `T₁ φ ∈ span F₁.rigidityRows`.
  have h₁ := BodyHingeFramework.funLeft_dualMap_sub_acolumn_mem_span_rigidityRows
    (Fv := Fv) (Fva := F₁) hca₁ hcv₁ hlink_ec₁ hdeg2₁ hdeg2r₁ hnov₁ htrans₁ hφ
  -- The second W9a transport, fed the intermediate vector `T₁ φ ∈ span F₁`.
  have h₂ := BodyHingeFramework.funLeft_dualMap_sub_acolumn_mem_span_rigidityRows
    (Fv := F₁) (Fva := Fva) hca₂ hcv₂ hlink_ec₂ hdeg2₂ hdeg2r₂ hnov₂ htrans₂ h₁
  -- `(funLeft (a₂ v₂)).dualMap` is linear, so it distributes over `T₁ φ`'s subtraction; the nested
  -- `(funLeft (a₂ v₂)).dualMap ((funLeft (a₁ v₁)).dualMap φ)` straightens to the composite relabel
  -- via `dualMap_comp_dualMap` (`f.dualMap ∘ₗ g.dualMap = (g ∘ₗ f).dualMap`) + `funLeft_comp`
  -- (`funLeft (σ₂ ∘ σ₁) = funLeft σ₁ ∘ₗ funLeft σ₂`).
  rw [map_sub, ← LinearMap.comp_apply, LinearMap.dualMap_comp_dualMap,
    ← LinearMap.funLeft_comp] at h₂
  -- The two subtractions group as the bracketed double a-column correction.
  rw [sub_sub] at h₂
  exact h₂

/-- **W9b — the `M₃` bottom-row tag transport** (the per-member relabel of one W6b bottom-family
member, design §1.52(c); Katoh–Tanigawa 2011 §6.4.1 eqs.~(6.39)/(6.41), Phase 22h). One bottom row
`φ` of the v-split W6b package — tagged either a genuine `R(G_v, q)`-row or an `(ab)`-block row
`hingeRow a b ρ'` (`ρ' ⊥ C(q(ab))`) — relabels under `(funLeft (a v)).dualMap` to a row tagged in
the `M₃`-arm shape: either a genuine row of the `G − a` framework at the overridden selector `ends₃`
and the relabeled seed `qρ = q ∘ (a v)`, or a `(c, v)`-block row `hingeRow c v ρ'`
(`ρ' ⊥ C(q(ac))`). This is exactly KT's eq.~(6.39) row correspondence `(vb)_j ↔ (ab)_j`,
`(va)_j ↔ (ac)_j`, `e_j ↔ e_j` read row-wise: the `(ab)`-block row maps to the genuine `e_b`-row of
`G − a` (`ends₃ e_b = (v, b)`, `qρ(v,·) = n_a`, `qρ(b,·) = n_b`); a `G_v`-row at the degree-2 body
`a`'s only edge `e_c = ac` maps to the candidate-shaped `(c, v)`-block row; every other `G_v`-row is
fixed by the swap and survives as a genuine `G − a`-row.

W9c maps this over the bottom family `w` to feed `case_III_arm_realization`'s `hwmem` slot at the
`M₃` roles. **§38:** every membership is built from an explicit link witness (the `hrow_mem` idiom)
and every extensor evaluation goes through `toBodyHinge_supportExtensor`/`ofNormals_ends`/
`ofNormals_normal` plus the `Equiv.swap` evaluation lemmas — never `whnf` on the `ofNormals`
carrier. -/
theorem PanelHingeFramework.case_III_bottom_relabel
    [DecidableEq α] {G Gv : Graph α β} {ends₀ ends₃ : β → α × α}
    {q : α × Fin (k + 2) → ℝ}
    {v a b c : α} {e_a e_b e_c : β}
    (hva : v ≠ a) (hab : a ≠ b) (hvb : v ≠ b) (hca : c ≠ a) (hcv : c ≠ v)
    (hG_ea : G.IsLink e_a v a) (hG_eb : G.IsLink e_b v b) (hG_ec : G.IsLink e_c a c)
    (hcla : ∀ e x, G.IsLink e a x → e = e_a ∨ e = e_c)
    (hGv_le : ∀ e x y, Gv.IsLink e x y → G.IsLink e x y)
    (hnov : ∀ e x y, Gv.IsLink e x y → x ≠ v ∧ y ≠ v)
    (hrecGv : ∀ e x y, Gv.IsLink e x y → ends₀ e = (x, y) ∨ ends₀ e = (y, x))
    (hends₃_eb : ends₃ e_b = (v, b))
    (hends₃_off : ∀ e, e ≠ e_a → e ≠ e_b → e ≠ e_c → ends₃ e = ends₀ e)
    {φ : Module.Dual ℝ (α → ScrewSpace k)}
    (hφ : φ ∈ (PanelHingeFramework.ofNormals Gv ends₀ q).toBodyHinge.rigidityRows ∨
      ∃ ρ' : Module.Dual ℝ (ScrewSpace k),
        ρ' (panelSupportExtensor (fun i => q (a, i)) (fun i => q (b, i))) = 0 ∧
        φ = BodyHingeFramework.hingeRow a b ρ') :
    (LinearMap.funLeft ℝ (ScrewSpace k) (Equiv.swap a v)).dualMap φ ∈
      (PanelHingeFramework.ofNormals (G.removeVertex a) ends₃
        (fun p => q (Equiv.swap a v p.1, p.2))).toBodyHinge.rigidityRows ∨
      ∃ ρ' : Module.Dual ℝ (ScrewSpace k),
        ρ' (panelSupportExtensor (fun i => q (c, i)) (fun i => q (a, i))) = 0 ∧
        (LinearMap.funLeft ℝ (ScrewSpace k) (Equiv.swap a v)).dualMap φ
          = BodyHingeFramework.hingeRow c v ρ' := by
  classical
  set qρ : α × Fin (k + 2) → ℝ := fun p => q (Equiv.swap a v p.1, p.2) with hqρ
  set Fv := (PanelHingeFramework.ofNormals Gv ends₀ q).toBodyHinge with hFv
  set Fva := (PanelHingeFramework.ofNormals (G.removeVertex a) ends₃ qρ).toBodyHinge with hFva
  -- The relabeled seed at body `x` reads `q` at the swapped body: `qρ(x,·) = q(swap a v x, ·)`.
  rcases hφ with hgen | ⟨ρ', hρ'e₀, rfl⟩
  · -- The `G_v`-row tag: destructure the generator and case on `a ∈ {x, y}`.
    obtain ⟨f, x, y, hlink, r, hr, rfl⟩ := hgen
    rw [hFv, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph] at hlink
    rw [BodyHingeFramework.hingeRow_funLeft_dualMap]
    obtain ⟨hxv, hyv⟩ := hnov f x y hlink
    have hGflink := hGv_le f x y hlink
    -- `r`'s annihilation at `Fv`'s `f`-extensor (the `q`-seed at `ends₀ f`).
    have hr' : r (Fv.supportExtensor f) = 0 := (Fv.mem_hingeRowBlock_iff f r).1 hr
    rw [hFv, PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_normal,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_ends] at hr'
    by_cases hxa : x = a
    · -- x = a: `hcla` forces `f = e_c` (the `e_a` branch links `v`, contradiction), then `y = c`.
      -- `subst x` (eliminate the local `x`, keeping the section body `a` / `c`).
      subst x
      have hfe : f = e_c := by
        rcases hcla f y hGflink with rfl | rfl
        · -- f = e_a: G.IsLink e_a a y and G.IsLink e_a v a, but a ≠ v (hva) and y ≠ v (hyv).
          rcases hG_ea.eq_and_eq_or_eq_and_eq hGflink with ⟨h1, _⟩ | ⟨h1, _⟩
          · exact absurd h1 hva
          · exact absurd h1.symm hyv
        · rfl
      -- `c = y` (flip so `subst` eliminates `y`, keeping the section variable `c`).
      have hcy : c = y := by
        rw [hfe] at hGflink
        rcases hG_ec.eq_and_eq_or_eq_and_eq hGflink with ⟨_, h2⟩ | ⟨_, h2⟩
        · exact h2
        · exact absurd h2 hca
      subst hcy
      -- relabel `hingeRow a c r → hingeRow v c r = hingeRow c v (-r)`; tag RIGHT with `ρ' := -r`.
      refine Or.inr ⟨-r, ?_, ?_⟩
      · -- annihilation: `r ⊥ C(q(ends₀ e_c))`, and `ends₀ e_c ∈ {(a,c),(c,a)}` (hrecGv).
        rw [hfe] at hr' hlink
        rw [LinearMap.neg_apply, neg_eq_zero]
        rcases hrecGv e_c a c hlink with he | he
        · rw [he] at hr'; rw [panelSupportExtensor_swap, map_neg, hr', neg_zero]
        · rw [he] at hr'; exact hr'
      · rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hca hcv]
        exact BodyHingeFramework.hingeRow_swap v c r
    · by_cases hya : y = a
      · -- y = a, x ≠ a: `hcla` forces `f = e_c`, then `x = c`.
        subst y
        have hfe : f = e_c := by
          rcases hcla f x hGflink.symm with rfl | rfl
          · rcases hG_ea.eq_and_eq_or_eq_and_eq hGflink with ⟨h1, _⟩ | ⟨h1, _⟩
            · exact absurd h1.symm hxv
            · exact absurd h1 hva
          · rfl
        have hcx : c = x := by
          rw [hfe] at hGflink
          rcases hG_ec.eq_and_eq_or_eq_and_eq hGflink with ⟨_, h2⟩ | ⟨_, h2⟩
          · exact absurd h2 hca
          · exact h2
        subst hcx
        -- relabel `hingeRow c a r → hingeRow c v r`; tag RIGHT with `ρ' := r`.
        refine Or.inr ⟨r, ?_, ?_⟩
        · rw [hfe] at hr' hlink
          rcases hrecGv e_c c a hlink with he | he
          · rw [he] at hr'; exact hr'
          · rw [he] at hr'; rw [panelSupportExtensor_swap, map_neg, hr', neg_zero]
        · rw [Equiv.swap_apply_of_ne_of_ne hca hcv, Equiv.swap_apply_left]
      · -- x ≠ a, y ≠ a: the swap fixes both endpoints; the image is the generator itself, a
        -- genuine `G − a`-row at the overridden selector `ends₃`.
        rw [Equiv.swap_apply_of_ne_of_ne hxa hxv, Equiv.swap_apply_of_ne_of_ne hya hyv]
        -- the image `hingeRow x y r` is a genuine row of `Fva`: the link survives `removeVertex a`
        -- and the `f`-extensor at `Fva` equals the `Fv`-extensor `r` annihilates.
        refine Or.inl ⟨f, x, y, ?_, r, ?_, rfl⟩
        · -- the link survives `removeVertex a` (endpoints `≠ a`).
          rw [hFva, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph,
            Graph.removeVertex_isLink]
          exact ⟨hGflink, hxa, hya⟩
        · -- block: the `f`-extensor at `Fva` equals the `f`-extensor at `Fv` (off `{e_a,e_b,e_c}`,
          -- `ends₃ f = ends₀ f`, and the swap fixes the recorded endpoints `∉ {a, v}`).
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
          rw [BodyHingeFramework.mem_hingeRowBlock_iff, hFva,
            PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_normal,
            PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_ends,
            hends₃_off f hfne_a hfne_b hfne_c]
          -- `ends₀ f ∈ {(x,y),(y,x)}` (hrecGv); the swap fixes `x, y ∉ {a, v}`, so `qρ = q` and
          -- the `Fva`-extensor matches the `Fv`-extensor `r` annihilates (`hr'`).
          rcases hrecGv f x y hlink with he | he <;> rw [he] at hr' ⊢ <;>
            simp only [hqρ, Equiv.swap_apply_of_ne_of_ne hxa hxv,
              Equiv.swap_apply_of_ne_of_ne hya hyv] <;> exact hr'
  · -- The `(ab)`-block tag `φ = hingeRow a b ρ'`: relabel to the genuine `e_b`-row.
    have hba : b ≠ a := Ne.symm hab
    have hbv : b ≠ v := Ne.symm hvb
    rw [BodyHingeFramework.hingeRow_funLeft_dualMap, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hba hbv]
    refine Or.inl ⟨e_b, v, b, ?_, ρ', ?_, rfl⟩
    · rw [hFva, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph,
        Graph.removeVertex_isLink]
      exact ⟨hG_eb, hva, hba⟩
    · -- block: `Fva.supportExtensor e_b = panelSupportExtensor n_a n_b` (`ends₃ e_b = (v,b)`,
      -- `qρ(v,·) = q(a,·)`, `qρ(b,·) = q(b,·)`); the input gives `ρ' ⊥` it.
      rw [BodyHingeFramework.mem_hingeRowBlock_iff, hFva,
        PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_normal,
        PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_ends, hends₃_eb]
      simp only [hqρ, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hba hbv]
      exact hρ'e₀

/-- **G4d-i — the `a`-column restriction of a `G_v`-row-span vector lies in `hingeRowBlock e_c`**
(`lem:case-III-claim612-eq644`, §1.49(4), Phase 22h). Given `wGv` in the span of a framework
`Fv`'s rigidity rows and the degree-2-at-`a` constraint that `e_c` is the *only* edge of `Fv`
incident to `a` (endpoints `a`, `c` with `a ≠ c`), the column restriction `wGv ∘ single a` lies
in the `e_c`-hinge-row block of a second framework `Fab` whose `e_c`-block agrees with `Fv`'s
(`hblock`).

The proof is a `Submodule.span_induction` on `hwGv`:
- For each generator `hingeRow u w ρ ∈ Fv.rigidityRows` (link `f u w`, `ρ ∈ Fv.hingeRowBlock f`):
  - If `u = a`: then `hdeg2 f w hlink` forces `f = e_c`, so
    `ρ ∈ Fv.hingeRowBlock e_c = Fab.hingeRowBlock e_c`
    and `(hingeRow a w ρ) ∘ single a = ρ` (`hingeRow_comp_single_tail hac`).
  - If `w = a` (but `u ≠ a`): `hdeg2r f u hlink` forces `f = e_c`; rewrite via `hingeRow_swap`
    (`hingeRow u a ρ = hingeRow a u (−ρ)`) and `hingeRow_comp_single_tail`; the block is a
    submodule so `−ρ` stays in it.
  - Otherwise `u ≠ a` and `w ≠ a`: `hingeRow_comp_single_off` gives zero, which is in any block.
- The `zero`, `add`, and `smul` cases follow from submodule closure. -/
theorem BodyHingeFramework.acolumn_mem_hingeRowBlock_of_span_rigidityRows
    [DecidableEq α] {Fab Fv : BodyHingeFramework k α β}
    {a c : α} {e_c : β}
    (hac : a ≠ c)
    (hlink_ec : Fv.graph.IsLink e_c a c)
    (hblock : Fv.hingeRowBlock e_c = Fab.hingeRowBlock e_c)
    (hdeg2 : ∀ f x, Fv.graph.IsLink f a x → f = e_c)
    (hdeg2r : ∀ f x, Fv.graph.IsLink f x a → f = e_c)
    {wGv : Module.Dual ℝ (α → ScrewSpace k)}
    (hwGv : wGv ∈ Submodule.span ℝ Fv.rigidityRows) :
    wGv.comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a) ∈ Fab.hingeRowBlock e_c := by
  -- Apply span_induction with the transported predicate `φ.comp(single a) ∈ Fab.hingeRowBlock e_c`.
  apply Submodule.span_induction (p := fun ψ _ =>
    ψ.comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a) ∈ Fab.hingeRowBlock e_c) _ _ _ _ hwGv
  · -- generator case: hingeRow u w ρ ∈ Fv.rigidityRows
    rintro ψ ⟨f, u, w, hlink, ρ, hρ, rfl⟩
    by_cases hau : u = a
    · -- u = a: hdeg2 forces f = e_c; use links to get w = c
      have hfe : f = e_c := by rw [hau] at hlink; exact hdeg2 f w hlink
      -- hlink rewritten: IsLink e_c a w; use eq_and_eq_or_eq_and_eq with hlink_ec
      have hwc : w = c := by
        rw [hau, hfe] at hlink
        -- hlink : IsLink e_c a w; hlink_ec : IsLink e_c a c → a = a ∧ w = c ∨ a = c ∧ w = a
        rcases hlink.eq_and_eq_or_eq_and_eq hlink_ec with ⟨-, h⟩ | ⟨h, -⟩
        · exact h
        · exact absurd h hac
      rw [hau, hwc, hingeRow_comp_single_tail hac]
      exact hblock ▸ hfe ▸ hρ
    · by_cases haw : w = a
      · -- w = a, u ≠ a: hdeg2r forces f = e_c; use links to get u = c
        have hfe : f = e_c := by rw [haw] at hlink; exact hdeg2r f u hlink
        have huc : u = c := by
          rw [haw, hfe] at hlink
          -- hlink : IsLink e_c u a; hlink_ec : IsLink e_c a c → u = a ∧ a = c ∨ u = c ∧ a = a
          rcases hlink.eq_and_eq_or_eq_and_eq hlink_ec with ⟨h, -⟩ | ⟨h, -⟩
          · exact absurd h hau
          · exact h
        -- hingeRow u w ρ = hingeRow u a ρ; rewrite via hingeRow_swap, then
        -- hingeRow_comp_single_tail
        rw [hfe] at hρ
        rw [haw, hingeRow_swap u a ρ, huc, hingeRow_comp_single_tail hac]
        exact (Fab.hingeRowBlock e_c).neg_mem (hblock ▸ hρ)
      · -- u ≠ a, w ≠ a: off-column; restricts to 0
        rw [hingeRow_comp_single_off (Ne.symm hau) (Ne.symm haw)]
        exact (Fab.hingeRowBlock e_c).zero_mem
  · -- zero
    simp [(Fab.hingeRowBlock e_c).zero_mem]
  · -- add
    intro x y _ _ hx hy
    rw [LinearMap.add_comp]
    exact (Fab.hingeRowBlock e_c).add_mem hx hy
  · -- smul
    intro r x _ hx
    rw [LinearMap.smul_comp]
    exact (Fab.hingeRowBlock e_c).smul_mem r hx

/-- **G4d-ii — the `M₃` candidate hinge row lies in the `a`-split rigidity-row span**
(`lem:case-III-claim612-eq644`, §1.49(4), Phase 22h). From G4d-i
(`acolumn_mem_hingeRowBlock_of_span_rigidityRows`) —
`r̂ := wGv.comp(single a) ∈ Fab.hingeRowBlock e_c`
— together with `hingeRow_mem_rigidityRows` (the membership certificate for a single hinge row),
the row `hingeRow a c r̂` lies in the rigidity-row *set* of the `v`-split framework `Fv` (since
`hlink_ec : Fv.graph.IsLink e_c a c` and `hblock ▸ hr̂`), and hence in the
`Submodule.span` of `Fv.rigidityRows`.

This is the `M₃` analogue of `exists_candidate_row_eq612`'s `hcand_mem` output: the common
candidate vector `r̂` — the `a`-column restriction of the `G_v`-redundant row — serves as the
block functional for a `hingeRow a c r̂` rigidity row, whose `e_c`-hinge lies in `Fv`. -/
theorem BodyHingeFramework.hingeRow_acolumn_mem_span_rigidityRows
    [DecidableEq α] {Fab Fv : BodyHingeFramework k α β}
    {a c : α} {e_c : β}
    (hac : a ≠ c)
    (hlink_ec : Fv.graph.IsLink e_c a c)
    (hblock : Fv.hingeRowBlock e_c = Fab.hingeRowBlock e_c)
    (hdeg2 : ∀ f x, Fv.graph.IsLink f a x → f = e_c)
    (hdeg2r : ∀ f x, Fv.graph.IsLink f x a → f = e_c)
    {wGv : Module.Dual ℝ (α → ScrewSpace k)}
    (hwGv : wGv ∈ Submodule.span ℝ Fv.rigidityRows) :
    BodyHingeFramework.hingeRow (k := k) (α := α) a c
        (wGv.comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a))
      ∈ Submodule.span ℝ Fv.rigidityRows := by
  apply Submodule.subset_span
  apply hingeRow_mem_rigidityRows Fv hlink_ec
  rw [hblock]
  exact acolumn_mem_hingeRowBlock_of_span_rigidityRows hac hlink_ec hblock hdeg2 hdeg2r hwGv

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
theorem PanelHingeFramework.case_III_arm_realization_M3
    [Finite α] [Finite β] [DecidableEq α]
    (G : Graph α β) (ends₀ ends₃ : β → α × α) {q : α × Fin (k + 2) → ℝ}
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
    {n''' : Fin (k + 2) → ℝ}
    (hLn : LinearIndependent ℝ ![(fun i => q (c, i)), n'''])
    (hgca : LinearIndependent ℝ ![(fun i => q (c, i)), (fun i => q (a, i))])
    {ρ : Module.Dual ℝ (ScrewSpace k)}
    (hρgate : ρ (panelSupportExtensor (fun i => q (c, i)) n''') ≠ 0)
    (hρe₀ : ρ (panelSupportExtensor (fun i => q (a, i)) (fun i => q (b, i))) = 0)
    (hρGv : BodyHingeFramework.hingeRow a b ρ ∈ Submodule.span ℝ
      (PanelHingeFramework.ofNormals (G.removeVertex v) ends₀ q).toBodyHinge.rigidityRows)
    {ιb : Type*} [Finite ιb] {w : ιb → Module.Dual ℝ (α → ScrewSpace k)}
    (hwcard : Nat.card ιb = screwDim k * (V(G).ncard - 2))
    (hw : LinearIndependent ℝ w)
    (hwmem : ∀ j, w j ∈
        (PanelHingeFramework.ofNormals (G.removeVertex v) ends₀ q).toBodyHinge.rigidityRows ∨
      ∃ ρ' : Module.Dual ℝ (ScrewSpace k),
        ρ' (panelSupportExtensor (fun i => q (a, i)) (fun i => q (b, i))) = 0 ∧
        w j = BodyHingeFramework.hingeRow a b ρ')
    {n : ℕ} (hdef : G.deficiency n = 0) :
    PanelHingeFramework.HasGenericFullRankRealization k n G := by
  classical
  set qρ : α × Fin (k + 2) → ℝ := fun p => q (Equiv.swap a v p.1, p.2) with hqρ
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
    (w := (LinearMap.funLeft ℝ (ScrewSpace k) (Equiv.swap a v)).dualMap ∘ w)
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
    have hvb_row : BodyHingeFramework.hingeRow v b ρ ∈ Submodule.span ℝ Fva.rigidityRows := by
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

end CombinatorialRigidity.Molecular
