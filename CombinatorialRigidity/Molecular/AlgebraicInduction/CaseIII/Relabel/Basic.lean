/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.AlgebraicInduction.CaseIII.Arms

/-!
# The algebraic induction — Case III relabel / split-off transport (M₃ machinery: defs + bridges)

Phase 22 (molecular-conjecture program). First file of the `CaseIII/Relabel/` subdirectory (the
Phase-23c split of the over-cap `CaseIII/Relabel.lean`, `notes/Phase23c.md`). The `ρ = (av)` relabel
apparatus (`ofNormals_relabel`, `rigidityRows_ofNormals_relabel`,
`hasGenericFullRankRealization_of_splitOff_relabel`) transporting the candidate `ρ`/`w` data across
the `a ↔ v` swap, the `acolumn`/`hingeRow` span bridges, and the `wstep` / `shiftBody*` chain
definitions (the candidate→base seed-fixed transport). The seed-advancing chain, the M₃ arm closer,
the chain-column machinery, and the forked general-`d` arm are in the sibling
`Relabel/{Chain,Arm,ChainColumn,ForkedArm}` files.

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

/-- **The support-extensor coincidence under a general `Equiv.Perm` relabel (CHAIN-2c-ii-arm, the
`hsupp_of` foundation): the relabelled `ofNormals` framework's supporting extensor at an edge `f`
equals the base framework's at the edge `σ f`** (`lem:case-III` general-`d`, KT 2011 §6.4.2 the
index-shift seed/selector coincidence eqs.~(6.54)–(6.56); Phase 23b). The relabelled framework
reads the base seed `q₀` at the `ρ`-shifted body (`qρ p := q₀ (ρ p.1, p.2)`) and the base endpoints
`ρ.symm`-shifted (`endsσρ e := (ρ.symm (ends₀ (σ e)).1, ρ.symm (ends₀ (σ e)).2)`); the matching
`.symm`/forward choices make the forward `ρ` in `qρ` cancel the `ρ.symm` in `endsσρ`, so the hinge
at `f` reads exactly the original hinge at `σ f` — **no involution needed**.

This is the support-extensor half of `ofNormals_relabel_perm` (the local `h_supp` step), extracted
as a standalone lemma: it is the `hsupp` ingredient the genuine-row transport bricks
(`rigidityRow_relabel_off_cycle`, `rigidityRow_relabel_to_genuine`) consume in the all-`d`
candidate-reduction arm's per-row dispatch (`chainData_bottom_relabel`, 2c-ii). Instantiated at
`(ρ, σ) = (shiftPerm i.castSucc, shiftEdgePerm i)` it supplies the per-branch support-extensor
coincidence at the candidate-`i` split. -/
theorem PanelHingeFramework.ofNormals_supportExtensor_relabel_perm {Gt : Graph α β}
    (ρ : Equiv.Perm α) (σ : Equiv.Perm β)
    {ends₀ : β → α × α} {q₀ : α × Fin (k + 2) → ℝ} (f : β) :
    (PanelHingeFramework.ofNormals Gt
        (fun e => (ρ.symm (ends₀ (σ e)).1, ρ.symm (ends₀ (σ e)).2))
        (fun p => q₀ (ρ p.1, p.2))).toBodyHinge.supportExtensor f =
      (PanelHingeFramework.ofNormals Gt ends₀ q₀).toBodyHinge.supportExtensor (σ f) := by
  simp only [PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_ends,
    PanelHingeFramework.ofNormals_normal, Equiv.apply_symm_apply]

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
    (hQrec : ∀ e u w, Gs.IsLink e u w → ends₀ e = (u, w) ∨ ends₀ e = (w, u)) :
    (PanelHingeFramework.ofNormals Gt
        (fun e => (ρ.symm (ends₀ (σ e)).1, ρ.symm (ends₀ (σ e)).2))
        (fun p => q₀ (ρ p.1, p.2))).IsGeneralPosition ∧
    (PanelHingeFramework.ofNormals Gt
        (fun e => (ρ.symm (ends₀ (σ e)).1, ρ.symm (ends₀ (σ e)).2))
        (fun p => q₀ (ρ p.1, p.2))).toBodyHinge.IsInfinitesimallyRigidOn st ∧
    (∀ e u w, Gt.IsLink e u w →
        (ρ.symm (ends₀ (σ e)).1, ρ.symm (ends₀ (σ e)).2) = (u, w) ∨
        (ρ.symm (ends₀ (σ e)).1, ρ.symm (ends₀ (σ e)).2) = (w, u)) := by
  set endsσρ : β → α × α := fun e => (ρ.symm (ends₀ (σ e)).1, ρ.symm (ends₀ (σ e)).2)
    with hendsσρ
  set qρ : α × Fin (k + 2) → ℝ := fun p => q₀ (ρ p.1, p.2) with hqρ
  set Q := PanelHingeFramework.ofNormals Gs ends₀ q₀ with hQ_def
  set Q' := PanelHingeFramework.ofNormals Gt endsσρ qρ with hQ'_def
  -- Q'.supportExtensor f = Q.supportExtensor (σ f): the relabelled framework's hinge at f reads
  -- q₀ at the ρ-shifted endpoints (the forward ρ in qρ cancelling the ρ.symm in endsσρ), i.e. the
  -- original hinge at (σ f). No involution needed.
  have h_supp : ∀ f : β,
      Q'.toBodyHinge.supportExtensor f = Q.toBodyHinge.supportExtensor (σ f) := fun f =>
    PanelHingeFramework.ofNormals_supportExtensor_relabel_perm ρ σ f
  refine ⟨?_, ?_, ?_⟩
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

/-- **The graph-iso genuine-row correspondence (CHAIN-2c-ii-arm, the genuine-row arm): an arbitrary
relabel `(ρ, σ)` intertwining two graphs carries a genuine rigidity row of the source framework to a
genuine rigidity row of the relabelled target framework** (`lem:case-III` general-`d`, KT 2011
§6.4.2 the (6.62) row correspondence; Phase 23b). This is the row-membership half the all-`d`
candidate-reduction arm (`chainData_relabel_arm`, 2c-ii) needs for the *genuine-row disjunct* of its
`hwmem` slot — the cycle generalization of the d=3 `M₃` arm's genuine-row branch
(`case_III_bottom_relabel`, the `Or.inl` cases where the swap fixes / moves a recorded endpoint),
lifted from the single swap `Equiv.swap a v` to the whole `(i−1)`-cycle relabel `(shiftPerm i)⁻¹`.

The geometry is abstracted exactly as in `ofNormals_relabel_perm`: the two graphs `Gs` (source, KT's
`v₁`-base split) and `Gt` (target, the candidate-`i` split) are `(ρ, σ)`-related by
`hiso : Gt.IsLink e x y ↔ Gs.IsLink (σ e) (ρ x) (ρ y)`, the target framework reads the source seed
`q₀` at the `ρ`-shifted body (`qρ p := q₀ (ρ p.1, p.2)`) and the source endpoints `ρ.symm`-shifted
(`endsσρ e := (ρ.symm (ends₀ (σ e)).1, ρ.symm (ends₀ (σ e)).2)`); the matching `.symm`/forward
choices make the support extensors agree across the relabel (`Q'.supportExtensor f =
Q.supportExtensor (σ f)`, no involution needed). A genuine source row `hingeRow u w r` at the link
`f` (with `r` in the `f`-hinge-row block) maps under `(funLeft ρ.symm).dualMap` to the genuine
target row `hingeRow (ρ.symm u) (ρ.symm w) r` at the link `σ.symm f` (whose target support extensor
equals the source one `r` annihilates). At the d=3 `M₃` swap (`ρ.symm = ρ`, `σ.symm = σ`) this is
the `case_III_bottom_relabel` genuine-row branch. -/
theorem PanelHingeFramework.rigidityRow_relabel_perm {Gs Gt : Graph α β}
    (ρ : Equiv.Perm α) (σ : Equiv.Perm β)
    (hiso : ∀ e x y, Gt.IsLink e x y ↔ Gs.IsLink (σ e) (ρ x) (ρ y))
    {ends₀ : β → α × α} {q₀ : α × Fin (k + 2) → ℝ}
    {φ : Module.Dual ℝ (α → ScrewSpace k)}
    (hφ : φ ∈ (PanelHingeFramework.ofNormals Gs ends₀ q₀).toBodyHinge.rigidityRows) :
    (LinearMap.funLeft ℝ (ScrewSpace k) ρ.symm).dualMap φ ∈
      (PanelHingeFramework.ofNormals Gt
        (fun e => (ρ.symm (ends₀ (σ e)).1, ρ.symm (ends₀ (σ e)).2))
        (fun p => q₀ (ρ p.1, p.2))).toBodyHinge.rigidityRows := by
  set endsσρ : β → α × α := fun e => (ρ.symm (ends₀ (σ e)).1, ρ.symm (ends₀ (σ e)).2)
    with hendsσρ
  set qρ : α × Fin (k + 2) → ℝ := fun p => q₀ (ρ p.1, p.2) with hqρ
  set Q := PanelHingeFramework.ofNormals Gs ends₀ q₀ with hQ_def
  set Q' := PanelHingeFramework.ofNormals Gt endsσρ qρ with hQ'_def
  -- The relabelled support extensor at `f` reads the original at `σ f` (forward `ρ` in `qρ` cancels
  -- the `ρ.symm` in `endsσρ`); no involution needed (the `ofNormals_relabel_perm` `h_supp` step).
  have h_supp : ∀ f : β,
      Q'.toBodyHinge.supportExtensor f = Q.toBodyHinge.supportExtensor (σ f) := by
    intro f
    simp only [hQ_def, hQ'_def, PanelHingeFramework.toBodyHinge_supportExtensor,
      PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal, hendsσρ, hqρ,
      Equiv.apply_symm_apply]
  -- Destructure the source generator: link `f u w`, block membership `r ⊥ Q.supportExtensor f`.
  obtain ⟨f, u, w, hlink, r, hr, rfl⟩ := hφ
  rw [hQ_def, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph] at hlink
  rw [BodyHingeFramework.hingeRow_funLeft_dualMap]
  -- The transported row `hingeRow (ρ.symm u) (ρ.symm w) r` is genuine in `Q'` at link `σ.symm f`.
  refine ⟨σ.symm f, ρ.symm u, ρ.symm w, ?_, r, ?_, rfl⟩
  · -- the source link `f u w` is a target link at `(ρ.symm u, ρ.symm w)` via `hiso` at `σ.symm f`.
    rw [hQ'_def, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]
    refine (hiso (σ.symm f) (ρ.symm u) (ρ.symm w)).mpr ?_
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact hlink
  · -- block: `Q'.supportExtensor (σ.symm f) = Q.supportExtensor f`, which `r` annihilates (`hr`).
    rw [BodyHingeFramework.mem_hingeRowBlock_iff, h_supp (σ.symm f), Equiv.apply_symm_apply]
    rw [hQ_def] at hr ⊢
    exact (BodyHingeFramework.mem_hingeRowBlock_iff _ f r).1 hr

/-- **The block-disjunct transport (CHAIN-2c-ii-arm, Leaf B): an arbitrary relabel `(ρ, σ)`
intertwining two graphs carries a source `(ab)`-block candidate row `hingeRow a b ρ'` to a genuine
rigidity row of the relabelled target framework, at any target edge `e_t` whose target support
extensor equals the source `(ab)`-panel extensor** (`lem:case-III` general-`d`, KT 2011 §6.4.2 the
(6.39)/(6.62) `(ab)`-row correspondence; Phase 23b). This is the **block-disjunct** half of the
all-`d` candidate-reduction arm's `hwmem` slot — the cycle generalization of the d=3 `M₃` arm's
`(ab)`-block branch (`case_III_bottom_relabel`, the final `Or.inl` case mapping `hingeRow a b ρ'` to
the genuine `e_b`-row `hingeRow v b ρ'`), lifted from the single swap `Equiv.swap a v` to the whole
`(i−1)`-cycle relabel `(shiftPerm i)⁻¹`.

The source row is the candidate `(ab)`-block tag `hingeRow a b ρ'` with `ρ'` annihilating the source
`(ab)`-panel extensor `panelSupportExtensor (q₀ a) (q₀ b)` (the W6b bottom-family `(ab)`-block
shape). Under `(funLeft ρ.symm).dualMap` it becomes `hingeRow (ρ.symm a) (ρ.symm b) ρ'`
(`hingeRow_funLeft_dualMap`). The two graph-side facts the caller supplies place this as a genuine
target row: `e_t` is a target link at `(ρ.symm a, ρ.symm b)` (the relabelled `(ab)`-edge survives in
the candidate split — in d=3 `M₃`, `e_t = e_b` with `(ρ.symm a, ρ.symm b) = (v, b)`), and the target
support extensor at `e_t` is exactly the source `(ab)`-panel extensor (`hsupp`, in d=3 from
`ends₃ e_b = (v, b)` and `qρ(v,·) = q₀(a,·)`). At the d=3 `M₃` swap (`ρ.symm = ρ`) this is the
`case_III_bottom_relabel` `(ab)`-block branch (`:1655–1670`). -/
theorem PanelHingeFramework.blockRow_relabel_perm {Gt : Graph α β}
    (ρ : Equiv.Perm α) {endsσρ : β → α × α} {qρ : α × Fin (k + 2) → ℝ}
    {a b : α} {q₀ : α × Fin (k + 2) → ℝ} {e_t : β}
    (hlink : Gt.IsLink e_t (ρ.symm a) (ρ.symm b))
    (hsupp : (PanelHingeFramework.ofNormals Gt endsσρ qρ).toBodyHinge.supportExtensor e_t
      = panelSupportExtensor (fun i => q₀ (a, i)) (fun i => q₀ (b, i)))
    {ρ' : Module.Dual ℝ (ScrewSpace k)}
    (hρ' : ρ' (panelSupportExtensor (fun i => q₀ (a, i)) (fun i => q₀ (b, i))) = 0) :
    (LinearMap.funLeft ℝ (ScrewSpace k) ρ.symm).dualMap
        (BodyHingeFramework.hingeRow a b ρ') ∈
      (PanelHingeFramework.ofNormals Gt endsσρ qρ).toBodyHinge.rigidityRows := by
  rw [BodyHingeFramework.hingeRow_funLeft_dualMap]
  refine ⟨e_t, ρ.symm a, ρ.symm b, ?_, ρ', ?_, rfl⟩
  · rw [PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]; exact hlink
  · rw [BodyHingeFramework.mem_hingeRowBlock_iff, hsupp]; exact hρ'

/-- **The moving-genuine-row (interior-chain-edge) transport (CHAIN-2c-ii-arm, the genuine-row
disjunct's interior-chain-edge branch): a base genuine rigidity row whose link endpoints the relabel
`ρ` carries to a *different* pair of bodies that still span a surviving target link transports under
`(funLeft ρ.symm).dualMap` to a genuine rigidity row of the relabelled target framework**
(`lem:case-III` general-`d`, KT 2011 §6.4.2 the (6.62) one-step-down row correspondence
`vⱼ₋₁vⱼ ⇐⇒ vⱼvⱼ₊₁`; Phase 23b).

This is the **interior-chain-edge / moving branch** of the genuine-row disjunct of the all-`d`
candidate-reduction arm's `hwmem` slot (`chainData_bottom_relabel`, 2c-ii) — the genuinely-new
branch the `d=3` `M₃` arm has no analogue of (at `d = 3` the cycle is the single swap `(v₁ v₂)`, so
the chain interior is trivial and a moved genuine endpoint can only be the candidate fresh pair,
i.e. the wrap-edge → block branch). At general `d` the inverse-cycle relabel `(shiftPerm i)⁻¹`
sends an interior chain edge `edge s` (link `vₛvₛ₊₁`, `2 ≤ s ≤ i−1`) **down one step** to
`edge (s−1)` (link `vₛ₋₁vₛ`) — both endpoints survive `removeVertex vᵢ` (their indices are `< i`),
so the image stays a
**genuine** row of the candidate split, not a block tag (KT (6.62) `e_j ⇐⇒ e_{j−1}`).

This is the **removeVertex-level** transport the arm engine `case_III_arm_realization` needs (it
binds `hwmem` at `ofNormals (G.removeVertex …) …`, **not** at a split, so the split-level
`rigidityRow_relabel_perm` is orphaned-for-the-arm; design §(o‴)(I.5)/(I.6)). It strictly subsumes
the sibling off-cycle branch `rigidityRow_relabel_off_cycle` (which delegates to it at
`(u', w', f') = (u, w, f)`): there the relabel *fixes* both endpoints and the target link is the
same edge `f`; here the relabel *moves* both endpoints (`hu : ρ.symm u = u'`, `hw : ρ.symm w = w'`
with `u' ≠ u` / `w' ≠ w` in general) and the target link is the *shifted* edge `f'`
(`hlinkGt : Gt.IsLink f' u' w'`). The seed/selector coincidence collapses, as in the off-cycle
sibling, to the support-extensor equality `hsupp : Q'.supportExtensor f' = Q.supportExtensor f` (the
caller discharges it from the chain step's seed-shift cancellation + the chain-edge correspondence —
both bodies move one step, so the relabelled `qρ`-extensor at `f'` reads exactly the base
`q₀`-extensor at `f`). The transported row `hingeRow (ρ.symm u) (ρ.symm w) r = hingeRow u' w' r`
(`hu`/`hw`) is then a genuine target row at the shifted link `f'` (whose target support extensor `r`
annihilates by `hr` + `hsupp`). -/
theorem PanelHingeFramework.rigidityRow_relabel_to_genuine {Gt : Graph α β}
    (ρ : Equiv.Perm α) {endsσρ : β → α × α} {qρ : α × Fin (k + 2) → ℝ}
    {Gs : Graph α β} {ends₀ : β → α × α} {q₀ : α × Fin (k + 2) → ℝ}
    {f f' : β} {u w u' w' : α} {r : Module.Dual ℝ (ScrewSpace k)}
    (hr : r ∈ (PanelHingeFramework.ofNormals Gs ends₀ q₀).toBodyHinge.hingeRowBlock f)
    (hu : ρ.symm u = u') (hw : ρ.symm w = w')
    (hlinkGt : Gt.IsLink f' u' w')
    (hsupp : (PanelHingeFramework.ofNormals Gt endsσρ qρ).toBodyHinge.supportExtensor f'
      = (PanelHingeFramework.ofNormals Gs ends₀ q₀).toBodyHinge.supportExtensor f) :
    (LinearMap.funLeft ℝ (ScrewSpace k) ρ.symm).dualMap
        (BodyHingeFramework.hingeRow u w r) ∈
      (PanelHingeFramework.ofNormals Gt endsσρ qρ).toBodyHinge.rigidityRows := by
  rw [BodyHingeFramework.hingeRow_funLeft_dualMap, hu, hw]
  refine ⟨f', u', w', ?_, r, ?_, rfl⟩
  · rw [PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]; exact hlinkGt
  · rw [BodyHingeFramework.mem_hingeRowBlock_iff, hsupp]
    exact (BodyHingeFramework.mem_hingeRowBlock_iff _ f r).1 hr

/-- **The off-cycle (fixed-endpoint) genuine-row transport (CHAIN-2c-ii-arm, the genuine-row
disjunct's off-cycle branch): a base genuine rigidity row whose link endpoints are BOTH fixed by the
relabel `ρ` transports under `(funLeft ρ.symm).dualMap` to a genuine rigidity row of the relabelled
target framework, given a target link at the (unmoved) endpoints whose target support extensor
agrees with the source's** (`lem:case-III` general-`d`, KT 2011 §6.4.2 the (6.62) row correspondence
at a non-cycle body; Phase 23b).

This is the **off-cycle / surviving-link branch** of the genuine-row disjunct of the all-`d`
candidate-reduction arm's `hwmem` slot (`chainData_bottom_relabel`, 2c-ii) — the
**removeVertex-level** transport the arm engine `case_III_arm_realization` actually needs (the
engine binds `hwmem` at `ofNormals (G.removeVertex …) …`, **not** at a split, so the split-level
`rigidityRow_relabel_perm` is orphaned-for-the-arm; design §(o‴)(I.5)/(I.6)). It is the cycle
generalization of the d=3 `M₃` arm's genuine-row branch (`case_III_bottom_relabel`, the final
`Or.inl` case where the swap fixes both recorded endpoints, `:1690–1725`), lifted from the single
swap `Equiv.swap a v` to the whole `(i−1)`-cycle relabel `(shiftPerm i)⁻¹`.

The graph layer is abstracted into the two facts the caller supplies for this branch: the relabel
`ρ` fixes both endpoints (`hu : ρ.symm u = u`, `hw : ρ.symm w = w` — `u`, `w` lie off the
`(i−1)`-cycle, where `shiftPerm` is the identity, via `shiftPerm_inv_apply_off`), and the source
link `f u w` survives into the target graph `Gt` (`hlinkGt`, here `Gt = G.removeVertex (vtxᵢ)`:
both endpoints avoid the removed vertex because they avoid the whole cycle). The seed/selector
coincidence collapses to the support-extensor equality `hsupp : Q'.supportExtensor f =
Q.supportExtensor f` (the caller discharges it from `seedShift_off_cycle`, the off-cycle seed
coincidence `qρ = q₀` at the fixed endpoints — the cycle generalization of the d=3 `M₃` arm's
`qρ = q` step at endpoints `∉ {a, v}`). The transported row
`hingeRow (ρ.symm u) (ρ.symm w) r = hingeRow u w r` (`hu`/`hw`) is then a genuine target row at the
same link `f` (whose target support extensor `r` annihilates by `hr` + `hsupp`). -/
theorem PanelHingeFramework.rigidityRow_relabel_off_cycle {Gt : Graph α β}
    (ρ : Equiv.Perm α) {endsσρ : β → α × α} {qρ : α × Fin (k + 2) → ℝ}
    {Gs : Graph α β} {ends₀ : β → α × α} {q₀ : α × Fin (k + 2) → ℝ}
    {f : β} {u w : α} {r : Module.Dual ℝ (ScrewSpace k)}
    (hr : r ∈ (PanelHingeFramework.ofNormals Gs ends₀ q₀).toBodyHinge.hingeRowBlock f)
    (hu : ρ.symm u = u) (hw : ρ.symm w = w)
    (hlinkGt : Gt.IsLink f u w)
    (hsupp : (PanelHingeFramework.ofNormals Gt endsσρ qρ).toBodyHinge.supportExtensor f
      = (PanelHingeFramework.ofNormals Gs ends₀ q₀).toBodyHinge.supportExtensor f) :
    (LinearMap.funLeft ℝ (ScrewSpace k) ρ.symm).dualMap
        (BodyHingeFramework.hingeRow u w r) ∈
      (PanelHingeFramework.ofNormals Gt endsσρ qρ).toBodyHinge.rigidityRows :=
  -- The fixed-endpoint instance of the moving brick `rigidityRow_relabel_to_genuine`
  -- (`(u', w', f') = (u, w, f)`): both endpoints unmoved, target link the same edge `f`.
  PanelHingeFramework.rigidityRow_relabel_to_genuine ρ hr hu hw hlinkGt hsupp

/-- **The moved-endpoint genuine-row → `(a,b)`-block transport (CHAIN-2c-ii-arm, the genuine-row
disjunct's wrap-edge branch): a base genuine rigidity row whose link endpoints the relabel `ρ` sends
to the candidate's fresh-edge endpoints `(a, b)` transports under `(funLeft ρ.symm).dualMap` to the
candidate `(a,b)`-BLOCK disjunct of the all-`d` candidate-reduction arm's `hwmem` slot**
(`lem:case-III` general-`d`, KT 2011 §6.4.2 the (6.62) wrap-edge correspondence
`vᵢvᵢ₊₁ ↦ vᵢ₋₁vᵢ₊₁`; Phase 23b).

This is the **moving / wrap-edge branch** of the genuine-row disjunct of `chainData_bottom_relabel`
(2c-ii): the base genuine row sits at the chain's top (wrap) edge `edge i` (link `vᵢvᵢ₊₁`), and the
inverse-cycle relabel `(shiftPerm i)⁻¹` carries it to the candidate-`i` split's fresh short-circuit
pair `(a, b) = (vᵢ₊₁, vᵢ₋₁)` — which is **not** a `G`-edge (it is the candidate's `e₀`), so the
image lands in the candidate `(a,b)`-block disjunct rather than a genuine target row. It is the
cycle generalization of the d=3 `M₃` arm's `x = a` / `y = a` genuine-row branches
(`case_III_bottom_relabel`, `:1685–1734`, the degree-2 body's only edge mapping to the candidate
block), lifted from the single swap `Equiv.swap a v` to the whole `(i−1)`-cycle relabel.

The graph layer is abstracted into the two facts the caller supplies for this branch: the relabel
`ρ` sends the recorded source endpoints to the candidate fresh-edge endpoints (`hu : ρ.symm u = a`,
`hw : ρ.symm w = b`), and the candidate `(a,b)`-panel extensor (read at the relabelled seed `qρ`)
coincides with the source `f`-extensor `r` annihilates (`hsupp`, the cycle generalization of the d=3
`M₃` arm's `qρ(v,·) = q₀(a,·)` seed-coincidence step). With `ρ' := r` the transported row
`hingeRow (ρ.symm u) (ρ.symm w) r = hingeRow a b r` (`hu`/`hw`) is then the `(a,b)`-block tag whose
functional annihilates the candidate `(a,b)`-panel extensor (`hsupp` + `hr`). At the d=3 `M₃`
involution case (`i = 2`, `ρ.symm = ρ`) this is the `case_III_bottom_relabel` block branch. -/
theorem PanelHingeFramework.rigidityRow_relabel_to_block
    (ρ : Equiv.Perm α) {qρ : α × Fin (k + 2) → ℝ}
    {Gs : Graph α β} {ends₀ : β → α × α} {q₀ : α × Fin (k + 2) → ℝ}
    {f : β} {u w a b : α} {r : Module.Dual ℝ (ScrewSpace k)}
    (hr : r ∈ (PanelHingeFramework.ofNormals Gs ends₀ q₀).toBodyHinge.hingeRowBlock f)
    (hu : ρ.symm u = a) (hw : ρ.symm w = b)
    (hsupp : panelSupportExtensor (fun i => qρ (a, i)) (fun i => qρ (b, i))
      = (PanelHingeFramework.ofNormals Gs ends₀ q₀).toBodyHinge.supportExtensor f) :
    ∃ ρ' : Module.Dual ℝ (ScrewSpace k),
      ρ' (panelSupportExtensor (fun i => qρ (a, i)) (fun i => qρ (b, i))) = 0 ∧
      (LinearMap.funLeft ℝ (ScrewSpace k) ρ.symm).dualMap
          (BodyHingeFramework.hingeRow u w r) = BodyHingeFramework.hingeRow a b ρ' := by
  refine ⟨r, ?_, ?_⟩
  · rw [hsupp]; exact (BodyHingeFramework.mem_hingeRowBlock_iff _ f r).1 hr
  · rw [BodyHingeFramework.hingeRow_funLeft_dualMap, hu, hw]

/-- **The swapped-orientation moved-endpoint genuine-row → `(a,b)`-block transport (CHAIN-2c-ii-arm,
the genuine-row disjunct's wrap-edge branch, `(b,a)`-order): the `(b,a)`-order sibling of
`rigidityRow_relabel_to_block`** (`lem:case-III` general-`d`, KT 2011 §6.4.2 the (6.62) wrap-edge
correspondence; Phase 23b). Same statement as `rigidityRow_relabel_to_block` except the relabel
`ρ` sends the recorded source endpoints to the candidate fresh-edge endpoints in the **reversed**
order (`hu : ρ.symm u = b`, `hw : ρ.symm w = a`) — the orientation `ends₀ (edge i)` records the top
edge `vᵢvᵢ₊₁` in when the assembly's per-row dispatch hits the wrap edge in the opposite recorded
sense.

The two block bricks together let the assembly's wrap case dispatch BOTH `ends₀ (edge i)`
orientations. It models the d=3 `M₃` arm's ±r handling of the candidate block branch
(`case_III_bottom_relabel`, `:1790–1821`, the `x = a` / `y = a` sub-cases tagging RIGHT with
`ρ' := ±r` depending on which recorded endpoint the swap moves). With `ρ' := -r` the transported
row `hingeRow (ρ.symm u) (ρ.symm w) r = hingeRow b a r = hingeRow a b (-r)`
(`hingeRow_funLeft_dualMap` + `hu`/`hw` + `hingeRow_swap`) is the `(a,b)`-block tag; the negated
functional `-r` still annihilates the candidate `(a,b)`-panel extensor (`hsupp` + `hr`, via
`LinearMap.neg_apply` + `neg_eq_zero`). At the d=3 `M₃` involution case (`i = 2`, `ρ.symm = ρ`)
this is the `case_III_bottom_relabel` `Or.inr ⟨-r, …⟩` block sub-case. -/
theorem PanelHingeFramework.rigidityRow_relabel_to_block_swap
    (ρ : Equiv.Perm α) {qρ : α × Fin (k + 2) → ℝ}
    {Gs : Graph α β} {ends₀ : β → α × α} {q₀ : α × Fin (k + 2) → ℝ}
    {f : β} {u w a b : α} {r : Module.Dual ℝ (ScrewSpace k)}
    (hr : r ∈ (PanelHingeFramework.ofNormals Gs ends₀ q₀).toBodyHinge.hingeRowBlock f)
    (hu : ρ.symm u = b) (hw : ρ.symm w = a)
    (hsupp : panelSupportExtensor (fun i => qρ (a, i)) (fun i => qρ (b, i))
      = (PanelHingeFramework.ofNormals Gs ends₀ q₀).toBodyHinge.supportExtensor f) :
    ∃ ρ' : Module.Dual ℝ (ScrewSpace k),
      ρ' (panelSupportExtensor (fun i => qρ (a, i)) (fun i => qρ (b, i))) = 0 ∧
      (LinearMap.funLeft ℝ (ScrewSpace k) ρ.symm).dualMap
          (BodyHingeFramework.hingeRow u w r) = BodyHingeFramework.hingeRow a b ρ' := by
  refine ⟨-r, ?_, ?_⟩
  · rw [LinearMap.neg_apply, neg_eq_zero, hsupp]
    exact (BodyHingeFramework.mem_hingeRowBlock_iff _ f r).1 hr
  · rw [BodyHingeFramework.hingeRow_funLeft_dualMap, hu, hw, BodyHingeFramework.hingeRow_swap]

/-- **The `ChainData` genuine-row `hwmem` disjunct (CHAIN-2c-ii-arm wiring): the interior-candidate
genuine-row transport, instantiating `rigidityRow_relabel_perm` at the index-shift relabel
`(ρ, σ) = (shiftPerm i.castSucc, shiftEdgePerm i)`** (`lem:case-III` general-`d`, KT 2011 §6.4.2
eqs.~(6.54)/(6.62) the one-step-down row correspondence; Phase 23b). For an interior candidate index
`2 ≤ i ≤ d−1` (`1 < i`, the nondegenerate cycle), a genuine rigidity row `φ` of the `v₁`-base split
framework `ofNormals (G.splitOff v₁ v₀ v₂ e₀) ends₀ q` maps under
`(funLeft (shiftPerm i.castSucc)⁻¹).dualMap` to a genuine rigidity row of the candidate-`i` split
framework `ofNormals (G.splitOff vᵢ vᵢ₊₁ vᵢ₋₁ e₀) endsσρ qρ` — where `qρ = q ∘ shiftPerm i.castSucc`
(KT (6.56), the candidate seed `qᵢ = q₁ ∘ ρᵢ`) and `endsσρ` the `(shiftPerm i.castSucc)⁻¹`-shifted
selector. This is the genuine-row disjunct the relabel arm's `hwmem` slot feeds the engine
`case_III_arm_realization` at the per-`i` roles: the abstract brick `rigidityRow_relabel_perm`
(graph-iso `(ρ, σ)`) instantiated at the `ChainData` graph-iso
`splitOff_isLink_shiftRelabel_iff` (the candidate split and the base split intertwined by
`(shiftPerm i.castSucc, shiftEdgePerm i)`). At the `d = 3` `M₃` instance `i = 2` the cycle
`shiftPerm 2 = (v₁ v₂)` is the single swap and this is the `case_III_bottom_relabel` genuine-row
branch. -/
theorem PanelHingeFramework.rigidityRow_chainData_relabel
    [DecidableEq α] [DecidableEq β] {G : Graph α β} {n : ℕ}
    (cd : G.ChainData n) (i : Fin cd.d) (hi : 1 < (i : ℕ))
    {ends₀ : β → α × α} {q : α × Fin (k + 2) → ℝ}
    {φ : Module.Dual ℝ (α → ScrewSpace k)}
    (hφ : φ ∈ (PanelHingeFramework.ofNormals
        (G.splitOff (cd.vtx (⟨1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc)
          (cd.vtx (⟨1, by have := i.isLt; omega⟩ : Fin cd.d).succ)
          (cd.vtx (⟨0, by have := i.isLt; omega⟩ : Fin cd.d).castSucc) cd.e₀)
        ends₀ q).toBodyHinge.rigidityRows) :
    (LinearMap.funLeft ℝ (ScrewSpace k) (cd.shiftPerm i.castSucc).symm).dualMap φ ∈
      (PanelHingeFramework.ofNormals
        (G.splitOff (cd.vtx i.castSucc) (cd.vtx i.succ)
          (cd.vtx (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc) cd.e₀)
        (fun e => ((cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).1,
          (cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).2))
        (fun p => q (cd.shiftPerm i.castSucc p.1, p.2))).toBodyHinge.rigidityRows :=
  PanelHingeFramework.rigidityRow_relabel_perm (cd.shiftPerm i.castSucc) (cd.shiftEdgePerm i)
    (fun _ _ _ => cd.splitOff_isLink_shiftRelabel_iff i hi) hφ

/-- **G4c-ii (fixed-seed form): the `ρ = (av)` relabel transports the concrete v-split `ofNormals`
data to the concrete a-split `ofNormals` data at the SAME seed `q₀ ∘ ρ`**
(`lem:splitOff-ofNormals-relabel`, KT 2011 eq. (6.31) framework side, Phase 22h).

This is the transport in the **producer's direction**: the induction hypothesis realizes the
`v`-split `G.splitOff v a b e₀` (`G_v^{ab}` in KT) concretely as `ofNormals (G.splitOff v a b e₀)
ends₀ q₀` with the three generic-realization conjuncts (general position, rigidity on `V(G)∖{v}`,
link-recording), and the `M₃` arm of the Case-III producer needs the SAME
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
  refine ⟨?_, ?_, ?_⟩
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
IH at the `v`-split, the form `theorem_55_minimalKDof_k_all_k`'s `hsplitZero` branch supplies, and
yields the `a`-split datum the `M₃` arm needs); the fixed-seed form above is the load-bearing one,
since the producer reads the concrete `ofNormals` framework and its row-space correspondence
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
    hav hbv hcv hca heab heac hclv hcla he₀ he₁ he₁₀ hgp' hrig' hrec'
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
  refine ⟨_, rfl, hgp, hrank_out, fun e u w he => ?_⟩
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

/-- **The six per-step W9a conjuncts of the base→candidate seed-advance step** (CHAIN-2c-ii-arm; the
`hstep`-bundle factored out of `funLeft_dualMap_sub_acolumn_seedAdvance_mem_span_rigidityRows`,
`notes/Phase23-design.md` §(o‴)(H.10)). At chain step `s` (bound `s + 2 < cd.d`), this is the
six-conjunct geometry of the W9a single step `Fv = ofNormals (G − vtx (s+1)) ends q` →
`Fva = ofNormals (G − vtx (s+2)) ends' (q ∘ swap)` with roles
`(v, a, c) = (vtx (s+1), vtx (s+2), vtx (s+3))` and `e_c = edge (s+2)`: the distinctness `c ≠ a ∧
c ≠ v`, the surviving `a—c` link, the degree-2 closures at the moved body `a`, the off-`v` fact, and
the **seed-advancing `htrans`** (the genuinely-new block agreement — an off-`a` link survives the
removal and its supporting extensor coincides at the two seeds because the swap `(a v)` fixes the
recorded endpoints `∉ {a, v}` and `ends' = ends` off the two moved edges). This is exactly the
`hstep`-conjunct shape the `foldl` fold core `wstep_foldl_mem_span_rigidityRows` consumes at the
ascending body triple `(v, a, c) = (vtx (s+1), vtx (s+2), vtx (s+3))`, so the concrete fold instance
`shiftBodyListAsc_foldl_mem_span_rigidityRows` feeds it directly. **§38:** graph reads go through
`toBodyHinge_graph`/`ofNormals_graph` and extensor reads through
`toBodyHinge_supportExtensor`/`ofNormals_ends`/`ofNormals_normal` — never `whnf` on the `ofNormals`
carrier. -/
theorem _root_.Graph.ChainData.seedAdvance_wstep_hstep
    [DecidableEq α] {G : Graph α β} {n : ℕ} (cd : G.ChainData n) {s : ℕ}
    (hbound : s + 2 < cd.d) (ends ends' : β → α × α) (q : α × Fin (k + 2) → ℝ)
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
  -- The W9a roles: `v` the freed slot (removed in the source), `a` the moving body, `c` its
  -- surviving chain-successor; `e_c = edge (s+2)` the surviving `a—c` edge.
  set v := cd.vtx ⟨s + 1, by omega⟩ with hv
  set a := cd.vtx ⟨s + 2, by omega⟩ with ha
  set c := cd.vtx ⟨s + 3, by omega⟩ with hc
  set e_c := cd.edge ⟨s + 2, by omega⟩ with he_c
  set Fv := (PanelHingeFramework.ofNormals (G.removeVertex v) ends q).toBodyHinge with hFv
  set qρ : α × Fin (k + 2) → ℝ := fun p => q (Equiv.swap a v p.1, p.2) with hqρ
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
  -- The seed-advancing `htrans`: an off-`a` link of `G − v` survives `removeVertex a`, and its
  -- supporting extensor coincides at the two seeds (the swap fixes the recorded endpoints
  -- `∉ {a, v}`, and `ends'` agrees with `ends` off the moved edges).
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
      -- `ends f`'s two recorded endpoints are the link endpoints `x, y` up to order (`hrec`),
      -- which avoid `a` (`hxa`/`hya`) and `v` (`hxv`/`hyv`). The swap `(a v)` then fixes them, so
      -- `qρ = q` at those slots and the `Fva`-extensor matches the `Fv`-extensor `r` kills (`hr`).
      rcases hrec f x y hlink with he | he <;> rw [he] at hr ⊢ <;>
        simp only [hqρ, Equiv.swap_apply_of_ne_of_ne hxa hxv,
          Equiv.swap_apply_of_ne_of_ne hya hyv] <;> exact hr
  exact ⟨⟨hca, hcv⟩, hFv_link_ec, hdeg2, hdeg2r, hnov, htrans⟩

/-- **The base→candidate single-step seed-advance W9a transport** (CHAIN-2c-ii-arm de-risk gate,
`notes/Phase23-design.md` §(o‴)(H.10), top-step generalization 2026-06-19). One step of the
interior-candidate relabel arm's **base→candidate** row transport (KT 2011 §6.4.2 eq.~(6.62), the
one-step-up correspondence `vⱼ ⇒ vⱼ₊₁`): at chain step `s` (bound `s + 2 < d`, so the moving body
`vtx (s+2)` is itself an interior degree-2 chain vertex and its surviving neighbour `vtx (s+3)` is a
valid chain vertex), a row of the source framework `Fv = ofNormals (G − vtx (s+1))`
on seed `q` transports — across the swap `(a v) = (vtx (s+2) vtx (s+1))` with the seed *advancing*
to `q' = q ∘ swap (vtx (s+2)) (vtx (s+1))` — into the target framework `Fva = ofNormals (G −
vtx (s+2))` on `q'`, after the moved body `a = vtx (s+2)`'s `a`-column hinge row is subtracted.

**Single bound `s + 2 < d` covers both interior and top steps** (the top-step de-risk outcome).
The full base→candidate cycle fold for candidate `i` (`2 ≤ i ≤ d−1`) runs steps `s = 0, …, i−2`;
the *interior* steps (`s + 2 < i`, the moving body a passing degree-2 body) and the *top* step
(`s = i−2`, where `a = vtx (s+2) = vtx i` is the candidate vertex itself) both satisfy `s + 2 < d`
— because the candidate `vᵢ` at `i ≤ d−1` is *itself* an interior degree-2 chain vertex (`vtx i`,
`i < d`), so the candidate-vertex top step closes with the identical proof, off the same
`deg_two`/`isLink_edge`/`vtx_ne` accessors. The §(o‴)-class concern that the top step is "different
geometry" (the candidate vertex, not a passing body) dissolved: `i ≤ d−1` keeps `vtx i` interior.

This is the chain-indexed, **seed-advancing** instance of `case_III_arm_realization_M3`'s `hρGv`
slot (`CaseIII/Relabel.lean`, the d=3 M₃ arm): there the single step goes `Fv = ofNormals (G − v)
ends q` → `Fva = ofNormals (G − a) ends₃ qρ` with `qρ = q ∘ swap a v`; here the same single step is
indexed by the chain step `s`, with the W9a roles `(v, a, c) = (vtx (s+1), vtx (s+2), vtx (s+3))`
read off the chain (the body `a = vtx (s+2)` is present at degree two in `G − vtx (s+1)`, moving
into the freed slot `v = vtx (s+1)` past its surviving chain-successor `c = vtx (s+3)`, its
predecessor edge to `vtx (s+1)` being cut by the removal). It is the **base→candidate** orientation
the arm needs (source `G − vtx (s+1)` lower-index / base side, target `G − vtx (s+2)` higher-index /
candidate side) — the *opposite* of the landed candidate→base fold
`shiftBodyList_foldr_mem_span_rigidityRows`, and the building block the corrected-Fix-A cycle fold
(re-folded in opposite chain order, seed advancing one swap per step) iterates.

The seed-advancing `htrans` (the genuinely-new piece beyond the seed-fixed
`shiftBodyFramework_htrans`'s `le_refl`) is the extensor-coincidence argument the d=3 M₃ `hρGv`
slot runs: an off-`a` link survives `removeVertex (vtx (s+2))`, and its supporting extensor at the
two seeds coincides because the swap `(a v)` fixes the recorded endpoints (`ends' f = ends f` off
the moved edges, and the swap fixes the link's `≠ {a, v}` endpoints, so `q' = q` there). The
de-risk gate (verify the single step closes before pinning the cycle fold / arm signature, H.10);
graph-free over the carrier (`rigidityRows`/`hingeRowBlock` read only `graph`/`hingeRowBlock`), so
the `ofNormals` defeq trap (TACTICS-QUIRKS §38) does not bite. -/
theorem _root_.Graph.ChainData.funLeft_dualMap_sub_acolumn_seedAdvance_mem_span_rigidityRows
    [DecidableEq α] {G : Graph α β} {n : ℕ} (cd : G.ChainData n) {s : ℕ}
    (hbound : s + 2 < cd.d) (ends ends' : β → α × α) (q : α × Fin (k + 2) → ℝ)
    (hends'_off : ∀ f, f ≠ cd.edge ⟨s + 1, by omega⟩ → f ≠ cd.edge ⟨s + 2, by omega⟩ →
      ends' f = ends f)
    (hrec : ∀ f x y, (G.removeVertex (cd.vtx ⟨s + 1, by omega⟩)).IsLink f x y →
      ends f = (x, y) ∨ ends f = (y, x))
    {φ : Module.Dual ℝ (α → ScrewSpace k)}
    (hφ : φ ∈ Submodule.span ℝ
      (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨s + 1, by omega⟩)) ends
          q).toBodyHinge.rigidityRows) :
    (LinearMap.funLeft ℝ (ScrewSpace k)
          (Equiv.swap (cd.vtx ⟨s + 2, by omega⟩) (cd.vtx ⟨s + 1, by omega⟩))).dualMap φ
        - BodyHingeFramework.hingeRow (k := k) (α := α)
            (cd.vtx ⟨s + 1, by omega⟩) (cd.vtx ⟨s + 3, by omega⟩)
            (φ.comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k)
              (cd.vtx ⟨s + 2, by omega⟩)))
      ∈ Submodule.span ℝ
          (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨s + 2, by omega⟩)) ends'
            (fun p => q (Equiv.swap (cd.vtx ⟨s + 2, by omega⟩) (cd.vtx ⟨s + 1, by omega⟩) p.1,
              p.2))).toBodyHinge.rigidityRows := by
  -- Obtain the six per-step W9a conjuncts (the `hstep` bundle) and conclude via the landed
  -- single-step W9a transport (already the base→candidate orientation).
  obtain ⟨⟨hca, hcv⟩, hFv_link_ec, hdeg2, hdeg2r, hnov, htrans⟩ :=
    cd.seedAdvance_wstep_hstep hbound ends ends' q hends'_off hrec
  exact BodyHingeFramework.funLeft_dualMap_sub_acolumn_mem_span_rigidityRows
    hca hcv hFv_link_ec hdeg2 hdeg2r hnov htrans hφ


/-- **The single-step W9a transport map** (the cycle-W9a building block, CHAIN-2c-ii route B,
`notes/Phase23-design.md` §(o″)). The W9a relabel transport `φ ↦ (funLeft (a v)).dualMap φ −
hingeRow v c (φ ∘ single a)` packaged as a single linear map `Dual ℝ (α → ScrewSpace k) →ₗ Dual`
(the `T` of `funLeft_dualMap_sub_acolumn_mem_span_rigidityRows`, named so the cycle fold over the
chain of degree-2 bodies can iterate it). The subtracted `a`-column term `hingeRow v c (· ∘ single
a)` is the linear composite `(screwDiff v c).dualMap ∘ₗ (single a).dualMap` (the `hTapply` form of
W9a). -/
noncomputable def BodyHingeFramework.wstep [DecidableEq α] (v a c : α) :
    Module.Dual ℝ (α → ScrewSpace k) →ₗ[ℝ] Module.Dual ℝ (α → ScrewSpace k) :=
  (LinearMap.funLeft ℝ (ScrewSpace k) (Equiv.swap a v)).dualMap
    - (screwDiff (k := k) (α := α) v c).dualMap.comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a).dualMap

/-- `wstep v a c φ` is the W9a transported difference `(funLeft (a v)).dualMap φ − hingeRow v c
(φ ∘ single a)`. -/
theorem BodyHingeFramework.wstep_apply [DecidableEq α] (v a c : α)
    (φ : Module.Dual ℝ (α → ScrewSpace k)) :
    BodyHingeFramework.wstep (k := k) v a c φ
      = (LinearMap.funLeft ℝ (ScrewSpace k) (Equiv.swap a v)).dualMap φ
        - BodyHingeFramework.hingeRow (k := k) (α := α) v c
            (φ.comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a)) := by
  rw [BodyHingeFramework.wstep, LinearMap.sub_apply, LinearMap.comp_apply, hingeRow_eq_dualMap]; rfl

/-- **W9a iterates — the cycle-W9a `List`-fold transport** (the genuinely-new piece of route B,
CHAIN-2c-ii-transport-W9a; `notes/Phase23-design.md` §(o″)). The single-step W9a transport `wstep`
composes over a *list* of degree-2 bodies along a chain of intermediate frameworks: given a
framework chain `F : ℕ → BodyHingeFramework k α β` and a list `bodies : List (α × α × α)` of
`(v, a, c)` body triples, if every step `s` is a valid single-swap W9a transport from `F (s+1)`
*down to* `F s` (the per-step `htrans` / degree-2 / off-`v` hypotheses, the `s`-th body
`bodies[s] = (vₛ, aₛ, cₛ)` moved over the framework drop `F (s+1) → F s`), then the iterated
transport `(wstep v₀ a₀ c₀ ∘ ⋯ ∘ wstep vₘ aₘ cₘ) φ` of any `φ ∈ span (F bodies.length).rigidityRows`
(the source, top of the chain) lands in `span (F 0).rigidityRows` (the target, bottom).

The `foldr` applies the list *head* last (outermost), so the head body `bodies[0]` is the final
framework drop `F 1 → F 0` and the chain runs source-at-top `F (length)` down to target-at-bottom
`F 0` — matching `funLeft_dualMap_sub_acolumn_mem_span_rigidityRows`'s `Fv` (source) → `Fva`
(target) orientation per step. This is the cycle generalization of W9a's *single* `a`-column
subtraction: KT's `ρᵢ` is the `(i−1)`-cycle moving a chain of `i−1` adjacent degree-2 bodies
(KT 2011 eq.~(6.66), `2 ≤ i ≤ d−1`), and `shiftPerm i` factors head-first as
`(vtx 1 vtx 2) * (tail formPerm)` (`ChainData.shiftPerm_eq_swap_mul`), so the cycle is the
left-fold of single transpositions and the transport is the iterated `wstep`. The proof is a clean
`List` induction on `bodies`: the base case is `φ ∈ span (F 0)` itself; the step transports `φ`
through the tail's `(rest.length)`-fold over the *shifted* chain `F (· + 1)` (landing in
`span (F 1)` by the inductive hypothesis), then applies the head step's single W9a transport
`F 1 → F 0`. The per-step `a`-column subtractions *do* compose cleanly (the §(o″) telescoping
concern, settled at the binary `funLeft_dualMap_sub_acolumn_comp_mem_span_rigidityRows`). Graph-free
over the carrier, inheriting W9a's §38-clean discipline. -/
theorem BodyHingeFramework.wstep_foldr_mem_span_rigidityRows
    [DecidableEq α] (F : ℕ → BodyHingeFramework k α β)
    (ec : ℕ → β) (bodies : List (α × α × α))
    (hstep : ∀ s, (hs : s < bodies.length) →
      (bodies[s].2.2 ≠ bodies[s].2.1 ∧ bodies[s].2.2 ≠ bodies[s].1) ∧
      (F (s + 1)).graph.IsLink (ec s) bodies[s].2.1 bodies[s].2.2 ∧
      (∀ f x, (F (s + 1)).graph.IsLink f bodies[s].2.1 x → f = ec s) ∧
      (∀ f x, (F (s + 1)).graph.IsLink f x bodies[s].2.1 → f = ec s) ∧
      (∀ f x y, (F (s + 1)).graph.IsLink f x y → x ≠ bodies[s].1 ∧ y ≠ bodies[s].1) ∧
      (∀ f x y, (F (s + 1)).graph.IsLink f x y → x ≠ bodies[s].2.1 → y ≠ bodies[s].2.1 →
        (F s).graph.IsLink f x y ∧ (F (s + 1)).hingeRowBlock f ≤ (F s).hingeRowBlock f))
    {φ : Module.Dual ℝ (α → ScrewSpace k)}
    (hφ : φ ∈ Submodule.span ℝ (F bodies.length).rigidityRows) :
    (bodies.foldr (fun b T => (BodyHingeFramework.wstep (k := k) b.1 b.2.1 b.2.2).comp T)
        LinearMap.id) φ
      ∈ Submodule.span ℝ (F 0).rigidityRows := by
  induction bodies generalizing F ec with
  | nil => simpa using hφ
  | cons b rest ih =>
    -- Head-first fold: `foldr (b :: rest) = (wstep b₀) ∘ (foldr rest)`, head applied last. The tail
    -- transports `φ` (top of the chain, `span (F (rest.length + 1))`) down through `rest` over the
    -- *shifted* chain `F (· + 1)` to land in `span (F 1)`, then the head step drops `F 1 → F 0`.
    have htail := ih (fun s => F (s + 1)) (fun s => ec (s + 1))
      (fun s hs => by simpa using hstep (s + 1) (by simpa using hs))
      (by simpa using hφ)
    -- The head step's single-swap W9a transport `F 1 → F 0`, fed the tail output (in `span (F 1)`).
    obtain ⟨⟨hca, hcv⟩, hlink_ec, hdeg2, hdeg2r, hnov, htrans⟩ := hstep 0 (by simp)
    have hhead := BodyHingeFramework.funLeft_dualMap_sub_acolumn_mem_span_rigidityRows
      (Fv := F 1) (Fva := F 0) (v := b.1) (a := b.2.1) (c := b.2.2) hca hcv
      (e_c := ec 0) hlink_ec hdeg2 hdeg2r hnov htrans htail
    -- Repackage: `foldr (b :: rest) φ = wstep b₀ (foldr rest φ)`, `wstep`'s apply is W9a's
    -- difference.
    simpa [List.foldr_cons, BodyHingeFramework.wstep_apply] using hhead

/-- **W9a iterates the other way — the cycle-W9a `List.foldl` base→candidate transport** (the
seed-advancing fold core, CHAIN-2c-ii-arm; `notes/Phase23-design.md` §(o‴)(H.10)). The
seed-*advancing* analogue of `wstep_foldr_mem_span_rigidityRows`: the single-step W9a transport
`wstep` composes over a list of degree-2 bodies along an **ascending** chain of intermediate
frameworks (the seed advancing one swap per step), running source-at-bottom `F 0` *up to*
target-at-top `F bodies.length` — the **base→candidate** orientation the relabel arm's
`hρGv`/`hwmem` slots need (the landed `wstep_foldr` runs candidate→base / seed-fixed, the converse
implication, so it is orphaned for the arm; §(o‴)(H.10)).

Given a framework chain `F : ℕ → BodyHingeFramework k α β` and a list `bodies : List (α × α × α)`
of `(v, a, c)` body triples, if every step `s` is a valid single-swap W9a transport from `F s` *up
to* `F (s+1)` (the per-step `htrans` / degree-2 / off-`v` hypotheses, the `s`-th body
`bodies[s] = (vₛ, aₛ, cₛ)` moved over the framework rise `F s → F (s+1)`), then the iterated
transport of any `φ ∈ span (F 0).rigidityRows` (the source, bottom of the chain) lands in
`span (F bodies.length).rigidityRows` (the target, top).

The `foldl` applies the list *head* first (innermost), so the head body `bodies[0]` is the first
framework rise `F 0 → F 1` and the chain runs source-at-bottom `F 0` up to target-at-top
`F (length)` — matching `funLeft_dualMap_sub_acolumn_mem_span_rigidityRows`'s `Fv` (source) → `Fva`
(target) orientation per step. The chain `F` is free to carry a *different seed* at each index `s`
(unlike the seed-fixed `shiftBodyFramework` of the candidate→base fold), which is what makes this
the seed-advancing core: a concrete instantiation supplies `F s = ofNormals (G − vₛ₊₁) ends qₛ`
with the seed `qₛ` accumulating one swap per step (KT 2011 §6.4.2 eq.~(6.62)). The proof is a `List`
right-induction (`reverseRec`): the empty fold is `φ ∈ span (F 0)` itself; the `append_singleton`
step transports `φ` through the inner fold over `rest` (landing in `span (F rest.length)` by the
inductive hypothesis), then applies the last step's single W9a transport `F rest.length →
F (rest.length + 1)`. Graph-free over the carrier, inheriting W9a's §38-clean discipline. -/
theorem BodyHingeFramework.wstep_foldl_mem_span_rigidityRows
    [DecidableEq α] (F : ℕ → BodyHingeFramework k α β)
    (ec : ℕ → β) (bodies : List (α × α × α))
    (hstep : ∀ s, (hs : s < bodies.length) →
      (bodies[s].2.2 ≠ bodies[s].2.1 ∧ bodies[s].2.2 ≠ bodies[s].1) ∧
      (F s).graph.IsLink (ec s) bodies[s].2.1 bodies[s].2.2 ∧
      (∀ f x, (F s).graph.IsLink f bodies[s].2.1 x → f = ec s) ∧
      (∀ f x, (F s).graph.IsLink f x bodies[s].2.1 → f = ec s) ∧
      (∀ f x y, (F s).graph.IsLink f x y → x ≠ bodies[s].1 ∧ y ≠ bodies[s].1) ∧
      (∀ f x y, (F s).graph.IsLink f x y → x ≠ bodies[s].2.1 → y ≠ bodies[s].2.1 →
        (F (s + 1)).graph.IsLink f x y ∧ (F s).hingeRowBlock f ≤ (F (s + 1)).hingeRowBlock f))
    {φ : Module.Dual ℝ (α → ScrewSpace k)}
    (hφ : φ ∈ Submodule.span ℝ (F 0).rigidityRows) :
    (bodies.foldl (fun T b => (BodyHingeFramework.wstep (k := k) b.1 b.2.1 b.2.2).comp T)
        LinearMap.id) φ
      ∈ Submodule.span ℝ (F bodies.length).rigidityRows := by
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
        LinearMap.id) φ ∈ Submodule.span ℝ (F rest.length).rigidityRows := by
      refine ih (fun s hs => ?_)
      -- the inner steps re-index off `rest ++ [b]` via `getElem_append_left`.
      have hs' : s < (rest ++ [b]).length := by simp; omega
      have hidx : (rest ++ [b])[s]'hs' = rest[s] := by rw [List.getElem_append_left hs]
      have := hstep s hs'
      rwa [hidx] at this
    -- the last step's single-swap W9a transport `F rest.length → F (rest.length + 1)`.
    obtain ⟨⟨hca, hcv⟩, hlink_ec, hdeg2, hdeg2r, hnov, htrans⟩ := hstep rest.length (by simp)
    rw [hb] at hca hcv hlink_ec hdeg2 hdeg2r hnov htrans
    have hlast := BodyHingeFramework.funLeft_dualMap_sub_acolumn_mem_span_rigidityRows
      (Fv := F rest.length) (Fva := F (rest.length + 1))
      (v := b.1) (a := b.2.1) (c := b.2.2) (e_c := ec rest.length)
      hca hcv hlink_ec hdeg2 hdeg2r hnov htrans hinner
    rw [show (rest ++ [b]).length = rest.length + 1 by simp]
    simpa [BodyHingeFramework.wstep_apply] using hlast

/-- **The relabel side of the cycle-W9a fold is `funLeft` of the swap product** (the linear-map
companion of the permutation-level `shiftPerm_eq_prod_map_swap_shiftBodyList`,
CHAIN-2c-ii-transport-W9a route B, `notes/Phase23-design.md` §(o″)). The cycle-W9a `List.foldr`
composes its single-step relabels `(funLeft (swap aₛ vₛ)).dualMap` — the leading (non-`a`-column)
part of each `wstep` — over the moved-body list; this lemma identifies that *relabel-only* fold with
the single named relabel `(funLeft (⇑((bodies.map (swap b.2.1 b.1)).prod))).dualMap` of the swap
product. Composed with the permutation bridge `ChainData.shiftPerm_eq_prod_map_swap_shiftBodyList`
(`shiftPerm i = ∏ (swap b.2.1 b.1)` over `shiftBodyList i`), it rewrites the fold's relabel
component to `(funLeft (shiftPerm i)).dualMap` — the form the membership half of T-W9a needs.

The proof is a clean `List` induction. The empty fold is `LinearMap.id`, matching
`funLeft (⇑(1 : Equiv.Perm α)).dualMap = funLeft _root_.id |>.dualMap = id` (`Equiv.Perm.coe_one`,
`funLeft_id`, `dualMap_id`). The `cons` step uses the FRICTION composition idiom: the head swap's
`(funLeft (swap a₀ v₀)).dualMap` composed (outermost) with the tail relabel
`(funLeft (⇑P)).dualMap` (the IH, `P` the tail's swap product) straightens via
`dualMap_comp_dualMap` + `funLeft_comp` to `(funLeft (swap a₀ v₀ ∘ ⇑P)).dualMap`, and the swap
product head-peels as `((swap a₀ v₀) * P)` whose coercion is `(swap a₀ v₀) ∘ ⇑P`
(`Equiv.Perm.coe_mul`) — the two contravariances cancel, no order bookkeeping. Graph-free over the
carrier. -/
theorem BodyHingeFramework.wstep_foldr_funLeft_eq [DecidableEq α] (bodies : List (α × α × α)) :
    (bodies.foldr
        (fun b T => ((LinearMap.funLeft ℝ (ScrewSpace k) (Equiv.swap b.2.1 b.1)).dualMap).comp T)
        LinearMap.id)
      = (LinearMap.funLeft ℝ (ScrewSpace k)
          (⇑((bodies.map (fun b => Equiv.swap b.2.1 b.1)).prod))).dualMap := by
  induction bodies with
  | nil =>
    -- empty fold = `id`; the empty product is `1 : Equiv.Perm α`, and `funLeft id = id` (defeq),
    -- so its dual map is `id` (`dualMap_id`).
    simp only [List.foldr_nil, List.map_nil, List.prod_nil, Equiv.Perm.coe_one]
    rw [show (LinearMap.funLeft ℝ (ScrewSpace k) (_root_.id : α → α)) = LinearMap.id from rfl,
      LinearMap.dualMap_id]
  | cons b rest ih =>
    -- head-first fold + head-peel of the swap product, then the contravariance cancellation.
    rw [List.foldr_cons, ih, List.map_cons, List.prod_cons, Equiv.Perm.coe_mul,
      LinearMap.funLeft_comp, LinearMap.dualMap_comp_dualMap]

/-- **The relabel side of the *ascending* (seed-advancing) cycle-W9a fold is `funLeft` of the
inverse swap product** (the `foldl` companion of `wstep_foldr_funLeft_eq`, the linear-map half of
the G1 bridge of the seed-advancing relabel arm, CHAIN-2c-ii-arm route B,
`notes/Phase23-design.md` §(o‴)(H.10)). The seed-advancing W9a `List.foldl` composes its single-step
relabels `(funLeft (swap aₛ vₛ)).dualMap` — the leading (non-`a`-column) part of each `wstep` — over
the *ascending* moved-body list `shiftBodyListAsc i`; this lemma identifies that *relabel-only*
`foldl` with the single named relabel `(funLeft ⇑((bodies.map (swap b.2.1 b.1)).prod)⁻¹).dualMap` of
the **inverse** swap product.

The inverse is forced by the `foldl` accumulation order: `foldl` applies the *last* body outermost,
so the relabel composite runs in the **opposite** order to the swap product `(bodies.map swap).prod`
(which the perm bridge `shiftPerm_eq_prod_map_swap_shiftBodyListAsc` identifies with
`shiftPerm i.castSucc`). Because the swaps are involutions, the reversed product is exactly the
group inverse `((bodies.map swap).prod)⁻¹` — and composed with the perm bridge this rewrites the
`foldl`'s relabel component to `(funLeft (shiftPerm i.castSucc)⁻¹).dualMap = (funLeft (shiftPerm
i.castSucc).symm).dualMap`, the **base→candidate** inverse-cycle relabel the arm's `hρGv` slot needs
(matching the `hwmem` leaf `chainData_bottom_relabel`'s `(funLeft (shiftPerm i.castSucc).symm)`
transport, design §(o‴)(I.6)).

The proof is a `List` right-induction (`reverseRec`, matching the `foldl` base case at index 0). The
empty fold is `LinearMap.id`, matching `funLeft ⇑(1 : Equiv.Perm α)⁻¹ = id` (`inv_one`,
`Equiv.Perm.coe_one`, `funLeft_id`, `dualMap_id`). The `append_singleton` step peels the *last* swap
`(funLeft (swap a v)).dualMap` (applied outermost) over the inner fold's `(funLeft ⇑P⁻¹).dualMap`
(the IH, `P` the inner swap product); the inverse product head-peels as `(P * (swap a v))⁻¹ =
(swap a v)⁻¹ * P⁻¹` (`mul_inv_rev`), the swap self-inverse drops `(swap a v)⁻¹ = swap a v`
(`Equiv.swap_inv`), and the two contravariances of `funLeft_comp` + `dualMap_comp_dualMap` cancel.
Graph-free over the carrier. -/
theorem BodyHingeFramework.wstep_foldl_funLeft_eq [DecidableEq α] (bodies : List (α × α × α)) :
    (bodies.foldl
        (fun T b => ((LinearMap.funLeft ℝ (ScrewSpace k) (Equiv.swap b.2.1 b.1)).dualMap).comp T)
        LinearMap.id)
      = (LinearMap.funLeft ℝ (ScrewSpace k)
          (⇑((bodies.map (fun b => Equiv.swap b.2.1 b.1)).prod)⁻¹)).dualMap := by
  induction bodies using List.reverseRec with
  | nil =>
    simp only [List.foldl_nil, List.map_nil, List.prod_nil, inv_one, Equiv.Perm.coe_one]
    rw [show (LinearMap.funLeft ℝ (ScrewSpace k) (_root_.id : α → α)) = LinearMap.id from rfl,
      LinearMap.dualMap_id]
  | append_singleton rest b ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ih, List.map_append, List.map_cons,
      List.map_nil, List.prod_append, List.prod_cons, List.prod_nil, mul_one, mul_inv_rev,
      Equiv.swap_inv, Equiv.Perm.coe_mul, LinearMap.funLeft_comp, LinearMap.dualMap_comp_dualMap]

/-- **LEAF-ρ2 — the relabel-only ascending fold sends a hinge row to its inverse-cycle-relabelled
row** (CHAIN-2c-ii-arm, the `hρGv` literal-row identification; `notes/Phase23-design.md` §(o‴)(I.7),
LEAF-ρ2). The *relabel-only* component of the seed-advancing cycle-W9a `foldl` — the bare
`(funLeft (swap aₛ vₛ)).dualMap` fold over the ascending moved-body list `shiftBodyListAsc i`,
without the per-step `a`-column residue subtractions — sends an arbitrary hinge row
`hingeRow x y ρ₀` to the literal candidate row
`hingeRow ((shiftPerm i.castSucc)⁻¹ x) ((shiftPerm i.castSucc)⁻¹ y) ρ₀`
under the **base→candidate** inverse-cycle relabel.

This is the d=3 `M₃` step-2/3 generalization (`case_III_arm_realization_M3`, `Relabel.lean:2490`):
there the single relabel `(funLeft (a v)).dualMap (hingeRow a b ρ) = hingeRow v b ρ` identifies the
W9a image's relabel component as the genuine `e_b`-row; here the `i − 1`-step fold's relabel
component is the single named inverse-cycle relabel of the literal base redundancy. The proof is a
pure rewrite over the two landed G1 bridges: `wstep_foldl_funLeft_eq` rewrites the relabel-only
`foldl` to `(funLeft ⇑((bodies.map swap).prod)⁻¹).dualMap`, then
`shiftPerm_eq_prod_map_swap_shiftBodyListAsc` identifies the swap product with
`shiftPerm i.castSucc` (so its inverse is `(shiftPerm i.castSucc)⁻¹`), and
`hingeRow_funLeft_dualMap` evaluates the dual
relabel on the literal row. The arm closer (`chainData_relabel_arm`, LEAF-ρ3) then resolves the two
relabelled endpoints `(shiftPerm i.castSucc)⁻¹ x` / `…⁻¹ y` to the candidate roles via the landed
`shiftPerm_inv_*` action lemmas (`Operations.lean:1550–1572`). Graph-free over the carrier. -/
theorem _root_.Graph.ChainData.shiftBodyListAsc_relabel_foldl_hingeRow [DecidableEq α]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (i : Fin cd.d) (x y : α)
    (ρ₀ : Module.Dual ℝ (ScrewSpace k)) :
    ((cd.shiftBodyListAsc i).foldl
        (fun T b => ((LinearMap.funLeft ℝ (ScrewSpace k) (Equiv.swap b.2.1 b.1)).dualMap).comp T)
        LinearMap.id) (BodyHingeFramework.hingeRow (k := k) (α := α) x y ρ₀)
      = BodyHingeFramework.hingeRow (k := k) (α := α)
          ((cd.shiftPerm i.castSucc)⁻¹ x) ((cd.shiftPerm i.castSucc)⁻¹ y) ρ₀ := by
  rw [BodyHingeFramework.wstep_foldl_funLeft_eq,
    ← cd.shiftPerm_eq_prod_map_swap_shiftBodyListAsc i,
    BodyHingeFramework.hingeRow_funLeft_dualMap]

/-- **The cycle-W9a intermediate-framework chain `F = ofNormals ∘ shiftBodyGraph`**
(CHAIN-2c-ii-transport-W9a, the framework layer; `notes/Phase23-design.md` §(o″)). The
`List.foldr` transport `wstep_foldr_mem_span_rigidityRows` runs over a chain of *intermediate
frameworks* `F : ℕ → BodyHingeFramework`, one degree-2 body moved per cycle step. This is that
chain: the panel framework `ofNormals (cd.shiftBodyGraph s _) ends q` (turned into a
`BodyHingeFramework` via `toBodyHinge`) over the intermediate graph `shiftBodyGraph s = G − vₛ₊₁`,
with the panel selector `ends` and seed `q` **fixed across the chain** — only the graph shrinks,
mirroring the d=3 `M₃` arm's `Fv/Fva = ofNormals (G − v)/(G − a)` at the *single* removeVertex step
(`funLeft_dualMap_sub_acolumn_mem_span_rigidityRows`). The bound `s + 1 < cd.d + 1` is the minimal
chain-vertex validity of `shiftBodyGraph` (decoupled from the cycle top `i`); the total `F : ℕ →
BodyHingeFramework` the fold core consumes is assembled (with the out-of-range tail filled by an
arbitrary value) at the membership half (T-W9a). -/
noncomputable def _root_.Graph.ChainData.shiftBodyFramework {G : Graph α β}
    {n : ℕ} (cd : G.ChainData n) {s : ℕ} (hs : s + 1 < cd.d + 1) (ends : β → α × α)
    (q : α × Fin (k + 2) → ℝ) :
    BodyHingeFramework k α β :=
  (PanelHingeFramework.ofNormals (cd.shiftBodyGraph hs) ends q).toBodyHinge

/-- The graph of the cycle-W9a intermediate framework `shiftBodyFramework s` is the intermediate
graph `shiftBodyGraph s = G − vₛ₊₁`. -/
@[simp]
theorem _root_.Graph.ChainData.shiftBodyFramework_graph {G : Graph α β} {n : ℕ}
    (cd : G.ChainData n) {s : ℕ} (hs : s + 1 < cd.d + 1) (ends : β → α × α)
    (q : α × Fin (k + 2) → ℝ) :
    (cd.shiftBodyFramework hs ends q).graph = cd.shiftBodyGraph hs := rfl

/-- The supporting extensor of the cycle-W9a intermediate framework `shiftBodyFramework s` at an
edge `f` reads only the fixed selector `ends` and seed `q` (the panels at `ends f`'s endpoints) —
independent of the chain step `s` / the intermediate graph. This is why the per-step hinge-row
blocks agree (`shiftBodyFramework_htrans`'s second conjunct is `le_refl`). -/
theorem _root_.Graph.ChainData.shiftBodyFramework_supportExtensor {G : Graph α β}
    {n : ℕ} (cd : G.ChainData n) {s : ℕ} (hs : s + 1 < cd.d + 1) (ends : β → α × α)
    (q : α × Fin (k + 2) → ℝ) (f : β) :
    (cd.shiftBodyFramework hs ends q).supportExtensor f =
      panelSupportExtensor (fun i => q ((ends f).1, i)) (fun i => q ((ends f).2, i)) := rfl

/-- **The per-step `htrans` of the cycle-W9a framework chain** (CHAIN-2c-ii-transport-W9a, the
framework layer's deliverable; `notes/Phase23-design.md` §(o″)). The second-conjunct hypothesis the
fold core `wstep_foldr_mem_span_rigidityRows`'s `hstep` demands at each cycle step `s` (`s + 1 < i`,
the moved body `a = vₛ₊₁` interior): a link of the upper framework `F (s+1) = ofNormals
(G − vₛ₊₂)` *off the moved body* `a` transports to a genuine link of the lower framework `F s =
ofNormals (G − vₛ₊₁)`, with the hinge-row blocks agreeing.

This is the cycle generalization of the d=3 `M₃` arm's `htrans` (`case_III_arm_realization_M3`,
`hρGv` case): there the seed/selector *change* (`q → qρ`, `ends → ends₃`), forcing an
off-`{e_a,e_b,e_c}` extensor-coincidence argument; here the seed `q` and selector `ends` are
**fixed across the chain** (only the graph shrinks under `removeVertex`), so the supporting
extensors `panelSupportExtensor (q((ends f).1)) (q((ends f).2))` of `F (s+1)` and `F s` coincide
*definitionally* and the block agreement is `le_refl`. The graph inclusion is the landed
`shiftBodyGraph_isLink_of_off_body` lifted through `toBodyHinge_graph`/`ofNormals_graph`.

Graph-free over the carrier (`graph`/`hingeRowBlock` read only `graph`/`supportExtensor`), so the
`ofNormals` defeq trap (TACTICS-QUIRKS §38) does not bite. -/
theorem _root_.Graph.ChainData.shiftBodyFramework_htrans {G : Graph α β} {n : ℕ}
    (cd : G.ChainData n) {i s : ℕ} (hs : s + 1 < i) (hi : i < cd.d + 1) (ends : β → α × α)
    (q : α × Fin (k + 2) → ℝ) :
    ∀ f x y, (cd.shiftBodyFramework (s := s + 1) (by omega) ends q).graph.IsLink f x y →
      x ≠ cd.vtx ⟨s + 1, by omega⟩ → y ≠ cd.vtx ⟨s + 1, by omega⟩ →
      (cd.shiftBodyFramework (s := s) (by omega) ends q).graph.IsLink f x y ∧
        (cd.shiftBodyFramework (s := s + 1) (by omega) ends q).hingeRowBlock f ≤
          (cd.shiftBodyFramework (s := s) (by omega) ends q).hingeRowBlock f := by
  intro f x y hlink hxa hya
  -- The graph half: a link of `shiftBodyGraph (s+1) = G − vₛ₊₂` off the moved body `vₛ₊₁` is a link
  -- of `shiftBodyGraph s = G − vₛ₊₁` (the landed un-relabelled inclusion), read through the
  -- `shiftBodyFramework_graph` simp lemma.
  rw [cd.shiftBodyFramework_graph] at hlink
  refine ⟨?_, ?_⟩
  · rw [cd.shiftBodyFramework_graph]
    exact cd.shiftBodyGraph_isLink_of_off_body hs hi f x y hlink hxa hya
  · -- The hinge-row block half: the seed `q` and selector `ends` are fixed across the chain, so the
    -- supporting extensors of the two frameworks at `f` coincide
    -- (`shiftBodyFramework_supportExtensor`, independent of `s`) — the blocks are equal, hence `≤`
    -- by `le_refl` (no off-`{e_a,e_b,e_c}` extensor argument, unlike d=3 `M₃`'s seed/selector
    -- change).
    rw [BodyHingeFramework.hingeRowBlock, BodyHingeFramework.hingeRowBlock,
      cd.shiftBodyFramework_supportExtensor, cd.shiftBodyFramework_supportExtensor]

/-- **The total cycle-W9a intermediate-framework chain** (CHAIN-2c-ii-transport-W9a, the membership
half; `notes/Phase23-design.md` §(o″)). The fold core `wstep_foldr_mem_span_rigidityRows` runs over
a total `F : ℕ → BodyHingeFramework`; this packages the partial `shiftBodyFramework` (defined only
at chain-vertex indices `s + 1 < cd.d + 1`) into that total function, filling the out-of-range tail
with the always-valid `s = 0` framework (`0 + 1 < cd.d + 1` from `cd.hd`). On the in-range indices
the fold touches (`0, …, i − 1` for a cycle top `i ≤ cd.d`) it agrees with `shiftBodyFramework` by
`shiftBodyFrameworkTotal_eq`. -/
noncomputable def _root_.Graph.ChainData.shiftBodyFrameworkTotal {G : Graph α β}
    {n : ℕ} (cd : G.ChainData n) (ends : β → α × α) (q : α × Fin (k + 2) → ℝ) :
    ℕ → BodyHingeFramework k α β :=
  fun s => if h : s + 1 < cd.d + 1 then cd.shiftBodyFramework h ends q
    else cd.shiftBodyFramework (s := 0) (by have := cd.hd; omega) ends q

/-- On an in-range index `s + 1 < cd.d + 1`, the total chain `shiftBodyFrameworkTotal` agrees with
the partial `shiftBodyFramework`. -/
theorem _root_.Graph.ChainData.shiftBodyFrameworkTotal_eq {G : Graph α β} {n : ℕ}
    (cd : G.ChainData n) (ends : β → α × α) (q : α × Fin (k + 2) → ℝ) {s : ℕ}
    (hs : s + 1 < cd.d + 1) :
    cd.shiftBodyFrameworkTotal ends q s = cd.shiftBodyFramework hs ends q := by
  rw [Graph.ChainData.shiftBodyFrameworkTotal, dif_pos hs]

/-- **The cycle-W9a membership half** (CHAIN-2c-ii-transport-W9a route B, the genuinely-new crux;
`notes/Phase23-design.md` §(o″)). The iterated W9a transport over the moved-body list
`shiftBodyList i` carries the source row span at the top of the chain — `span (G − vᵢ)`-rows
(`shiftBodyFramework (i − 1)`) — down to the target row span at the bottom — `span (G − v₁)`-rows
(`shiftBodyFramework 0`). This is the membership content of KT eq.~(6.66): the index-shift cycle
`ρᵢ = shiftPerm i` (the `(i − 1)`-cycle `v₁ → ⋯ → vᵢ → v₁`) moves the chain of `i − 1` adjacent
degree-2 bodies, and the `i − 1` per-body `a`-column subtractions compose along the chain.

This is the cycle generalization of the d=3 `M₃` arm's *single* W9a step
(`funLeft_dualMap_sub_acolumn_mem_span_rigidityRows`, whose endpoints are the `ofNormals (G − v)` /
`ofNormals (G − a)` removeVertex frameworks at the single moved body `a`): here the chain endpoints
are the removeVertex frameworks `F (i − 1) = ofNormals (G − vᵢ)` / `F 0 = ofNormals (G − v₁)`, and
the moved bodies are the interior chain vertices `v₁, …, v_{i−1}`. The proof feeds the fold core all
six per-step `hstep` conjuncts off the landed graph-layer accessors
(`shiftBodyGraph_isLink_pred_edge`,
`shiftBodyGraph_deg_two(_right)`, `shiftBodyGraph_off_succ`) and the framework-layer per-step
`htrans` (`shiftBodyFramework_htrans`), reading the moved-body triple
`(shiftBodyList i)[s] = (vₛ₊₂, vₛ₊₁, vₛ)` off `getElem_shiftBodyList`. The relabel side (rewriting
the `wstep` fold's leading `funLeft`-of-swap product to `funLeft (shiftPerm i)`) is the separate
`wstep_foldr_funLeft_eq` + `shiftPerm_eq_prod_map_swap_shiftBodyList` bridge, applied by the arm
closer. Graph-free over the carrier, inheriting W9a's §38-clean discipline. -/
theorem _root_.Graph.ChainData.shiftBodyList_foldr_mem_span_rigidityRows
    [DecidableEq α] {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (i : Fin (cd.d + 1))
    (hi : 2 ≤ (i : ℕ)) (ends : β → α × α) (q : α × Fin (k + 2) → ℝ)
    {φ : Module.Dual ℝ (α → ScrewSpace k)}
    (hφ : φ ∈ Submodule.span ℝ
      (cd.shiftBodyFramework (s := (i : ℕ) - 1) (by omega) ends q).rigidityRows) :
    ((cd.shiftBodyList i).foldr
        (fun b T => (BodyHingeFramework.wstep (k := k) b.1 b.2.1 b.2.2).comp T) LinearMap.id) φ
      ∈ Submodule.span ℝ (cd.shiftBodyFramework (s := 0) (by omega) ends q).rigidityRows := by
  -- Feed the fold core the total chain `F = shiftBodyFrameworkTotal` and the per-step edge `ec s =
  -- edge s` (out-of-range tail arbitrary; the fold touches only `s ≤ i − 1 ≤ cd.d`).
  have hF0 : cd.shiftBodyFrameworkTotal ends q 0
      = cd.shiftBodyFramework (s := 0) (by omega) ends q :=
    cd.shiftBodyFrameworkTotal_eq ends q (by omega)
  have hFlen : cd.shiftBodyFrameworkTotal ends q (cd.shiftBodyList i).length
      = cd.shiftBodyFramework (s := (i : ℕ) - 1) (by omega) ends q := by
    rw [cd.length_shiftBodyList, cd.shiftBodyFrameworkTotal_eq ends q (by omega)]
  have hmem := BodyHingeFramework.wstep_foldr_mem_span_rigidityRows
    (F := cd.shiftBodyFrameworkTotal ends q)
    (ec := fun s => if h : s < cd.d then cd.edge ⟨s, h⟩
      else cd.edge ⟨0, by have := cd.hd; omega⟩)
    (bodies := cd.shiftBodyList i)
    (hstep := fun s hs => ?_) (hφ := hFlen ▸ hφ)
  · rwa [hF0] at hmem
  -- The per-step `hstep`. Each step `s < length = i − 1` moves the body `a = vₛ₊₁` (interior,
  -- `s + 1 < i`) past its surviving predecessor `c = vₛ`, in the graph drop
  -- `F (s+1) = G − vₛ₊₂ → F s = G − vₛ₊₁`. `hsi : s + 1 < i`, `hiv : i < cd.d + 1`.
  rw [cd.length_shiftBodyList] at hs
  have hiv : (i : ℕ) < cd.d + 1 := i.2
  have hsi : s + 1 < (i : ℕ) := by omega
  -- Resolve the total chain `F` to the partial `shiftBodyFramework` at the two consecutive indices,
  -- and read the moved-body triple `(shiftBodyList i)[s] = (vₛ₊₂, vₛ₊₁, vₛ)`.
  have hFs1 : cd.shiftBodyFrameworkTotal ends q (s + 1)
      = cd.shiftBodyFramework (s := s + 1) (by omega) ends q :=
    cd.shiftBodyFrameworkTotal_eq ends q (by omega)
  have hFs : cd.shiftBodyFrameworkTotal ends q s
      = cd.shiftBodyFramework (s := s) (by omega) ends q :=
    cd.shiftBodyFrameworkTotal_eq ends q (by omega)
  have hbody : (cd.shiftBodyList i)[s]'(by rw [cd.length_shiftBodyList]; omega)
      = (cd.vtx ⟨s + 2, by omega⟩, cd.vtx ⟨s + 1, by omega⟩, cd.vtx ⟨s, by omega⟩) :=
    cd.getElem_shiftBodyList i s (by rw [cd.length_shiftBodyList]; omega)
  -- The per-step edge `ec s = edge s` (in range, `s < cd.d`): resolve the `dite` to the predecessor
  -- edge `e_c = vₛ₊₁vₛ` of the W9a step.
  have hec : (if h : s < cd.d then cd.edge ⟨s, h⟩
      else cd.edge ⟨0, by have := cd.hd; omega⟩) = cd.edge ⟨s, by omega⟩ := dif_pos (by omega)
  simp only [hFs1, hFs, hbody, hec]
  -- The six `hstep` conjuncts off the landed graph/framework accessors (the moved-body geometry).
  refine ⟨⟨cd.shiftBody_pred_ne hsi hiv, cd.shiftBody_pred_ne_succ hsi hiv⟩, ?_, ?_, ?_, ?_, ?_⟩
  · -- `F (s+1).graph.IsLink (edge s) vₛ₊₁ vₛ`: the surviving predecessor link.
    rw [cd.shiftBodyFramework_graph]; exact cd.shiftBodyGraph_isLink_pred_edge hsi hiv
  · -- hdeg2: the body `vₛ₊₁` is at degree 2 in `G − vₛ₊₂`, its only link is `edge s`.
    intro f x hlink; rw [cd.shiftBodyFramework_graph] at hlink
    exact cd.shiftBodyGraph_deg_two hsi hiv f x hlink
  · -- hdeg2r: the right-side mirror.
    intro f x hlink; rw [cd.shiftBodyFramework_graph] at hlink
    exact cd.shiftBodyGraph_deg_two_right hsi hiv f x hlink
  · -- hnov: every link of `G − vₛ₊₂` avoids `v = vₛ₊₂`.
    intro f x y hlink; rw [cd.shiftBodyFramework_graph] at hlink
    exact cd.shiftBodyGraph_off_succ hsi hiv f x y hlink
  · -- htrans: a link off the moved body transports to `G − vₛ₊₁`, blocks agreeing.
    exact cd.shiftBodyFramework_htrans hsi hiv ends q


end CombinatorialRigidity.Molecular
