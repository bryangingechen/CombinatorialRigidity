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
      Q'.toBodyHinge.supportExtensor f = Q.toBodyHinge.supportExtensor (σ f) := fun f =>
    PanelHingeFramework.ofNormals_supportExtensor_relabel_perm ρ σ f
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

/-! ### The ascending (base→candidate) seed-advancing chain (CHAIN-2c-ii-arm)

The corrected-Fix-A relabel arm needs the cycle-W9a transport in the **base→candidate** orientation
with the seed *advancing* one swap per step (`notes/Phase23-design.md` §(o‴)(H.10)) — the opposite
of the seed-fixed candidate→base `shiftBodyFramework` chain above (which is orphaned for the arm: it
proves the converse span implication). The single-step de-risk gate
`funLeft_dualMap_sub_acolumn_seedAdvance_mem_span_rigidityRows` already discharges one rise
`F s = ofNormals (G − vₛ₊₁) ends qₛ` → `F (s+1) = ofNormals (G − vₛ₊₂) ends q_{s+1}` (single bound
`s + 2 < cd.d`, covering every step — interior and the candidate-vertex top step). This block is the
concrete seed-advancing chain it iterates: the seed `Q s = q ∘ (the first s cycle swaps)` advances
one swap per step (`shiftSeedAdv`), the moved-body list is the ascending `shiftBodyListAsc i`, and
the membership theorem `shiftBodyListAsc_foldl_mem_span_rigidityRows` feeds the `foldl` core
`wstep_foldl_mem_span_rigidityRows`, with the per-step gate applied at the last element of each
`reverseRec` step. The selector `ends` is **fixed** across the chain (only the seed advances), so
the gate's `hends'_off` is trivially `rfl`. -/

/-- The per-step seed swap of the ascending chain: at step `s` the swap `(vₛ₊₂ vₛ₊₁)` (the gate's
`(a v)`), made total over `ℕ` by defaulting to the identity off the chain-vertex range
(`s + 2 < cd.d + 1`). The seed accumulator `shiftSeedAdv` composes these. -/
noncomputable def _root_.Graph.ChainData.shiftSeedSwap [DecidableEq α] {G : Graph α β} {n : ℕ}
    (cd : G.ChainData n) (s : ℕ) : Equiv.Perm α :=
  if h : s + 2 < cd.d + 1 then
    Equiv.swap (cd.vtx ⟨s + 2, h⟩) (cd.vtx ⟨s + 1, by omega⟩) else 1

/-- On an in-range step `s + 2 < cd.d + 1`, the per-step seed swap resolves to `(vₛ₊₂ vₛ₊₁)`. -/
theorem _root_.Graph.ChainData.shiftSeedSwap_eq [DecidableEq α] {G : Graph α β} {n : ℕ}
    (cd : G.ChainData n) {s : ℕ} (hs : s + 2 < cd.d + 1) :
    cd.shiftSeedSwap s = Equiv.swap (cd.vtx ⟨s + 2, hs⟩) (cd.vtx ⟨s + 1, by omega⟩) := by
  rw [Graph.ChainData.shiftSeedSwap, dif_pos hs]

/-- **The ascending (base→candidate) seed accumulator** (CHAIN-2c-ii-arm; KT 2011 §6.4.2 eq.~(6.62),
the seed-advance recursion). The seed at chain step `s`: the base seed `q` post-composed (on the
vertex slot `p.1`) with the
first `s` cycle swaps `(v₂ v₁), …, (v_{s+1} vₛ)`, advancing one swap per step. `Q 0 = q`;
`Q (s+1) p = (Q s) (shiftSeedSwap s p.1, p.2)` (the gate's `qρ = q ∘ swap` at one step). -/
noncomputable def _root_.Graph.ChainData.shiftSeedAdv [DecidableEq α] {G : Graph α β} {n : ℕ}
    (cd : G.ChainData n) (q : α × Fin (k + 2) → ℝ) : ℕ → α × Fin (k + 2) → ℝ
  | 0 => q
  | s + 1 => fun p => cd.shiftSeedAdv q s (cd.shiftSeedSwap s p.1, p.2)

@[simp] theorem _root_.Graph.ChainData.shiftSeedAdv_zero [DecidableEq α] {G : Graph α β} {n : ℕ}
    (cd : G.ChainData n) (q : α × Fin (k + 2) → ℝ) : cd.shiftSeedAdv q 0 = q := rfl

theorem _root_.Graph.ChainData.shiftSeedAdv_succ [DecidableEq α] {G : Graph α β} {n : ℕ}
    (cd : G.ChainData n) (q : α × Fin (k + 2) → ℝ) (s : ℕ) :
    cd.shiftSeedAdv q (s + 1)
      = fun p => cd.shiftSeedAdv q s (cd.shiftSeedSwap s p.1, p.2) := rfl

/-- **The ascending (base→candidate) selector accumulator** (CHAIN-2c-ii-arm, ROUTE α leaf 1;
KT 2011 §6.4.2 eq.~(6.62), the selector cousin of `shiftSeedAdv`). The edge-endpoint selector at
chain step `s`: the base selector `ends₀` with each endpoint pair relabelled by the first `s`
per-step cycle swaps `(v₂ v₁), …, (v_{s+1} vₛ)`, advancing one swap per step — the SAME per-step
swap `shiftSeedSwap s` the seed accumulator uses, so selector and seed advance in lockstep.
`E 0 = ends₀`; `E (s+1) e = (shiftSeedSwap s (E s e).1, shiftSeedSwap s (E s e).2)` (KT's iso `ρᵢ`
applied step-by-step on the panel selector, never pre-applied to the base redundancy). -/
noncomputable def _root_.Graph.ChainData.shiftEndsAdv [DecidableEq α] {G : Graph α β} {n : ℕ}
    (cd : G.ChainData n) (ends₀ : β → α × α) : ℕ → β → α × α
  | 0 => ends₀
  | s + 1 => fun e => let p := cd.shiftEndsAdv ends₀ s e
                      ((cd.shiftSeedSwap s) p.1, (cd.shiftSeedSwap s) p.2)

@[simp] theorem _root_.Graph.ChainData.shiftEndsAdv_zero [DecidableEq α] {G : Graph α β} {n : ℕ}
    (cd : G.ChainData n) (ends₀ : β → α × α) : cd.shiftEndsAdv ends₀ 0 = ends₀ := rfl

theorem _root_.Graph.ChainData.shiftEndsAdv_succ [DecidableEq α] {G : Graph α β} {n : ℕ}
    (cd : G.ChainData n) (ends₀ : β → α × α) (s : ℕ) :
    cd.shiftEndsAdv ends₀ (s + 1)
      = fun e => ((cd.shiftSeedSwap s) (cd.shiftEndsAdv ends₀ s e).1,
                  (cd.shiftSeedSwap s) (cd.shiftEndsAdv ends₀ s e).2) := rfl

/-- **The ascending (base→candidate) seed-advancing chain** (CHAIN-2c-ii-arm, the framework layer;
`notes/Phase23-design.md` §(o‴)(H.10)). The seed-advancing analogue of `shiftBodyFramework`: the
panel framework `ofNormals (G − vₛ₊₁) ends (Q s)` (turned into a `BodyHingeFramework` via
`toBodyHinge`) over the intermediate graph `shiftBodyGraph s = G − vₛ₊₁`, with the selector `ends`
fixed but the seed `Q s = shiftSeedAdv q s` advancing one swap per step. The chain runs
source-at-bottom `F 0 = ofNormals (G − v₁) ends q` up to target-at-top
`F (i−1) = ofNormals (G − vᵢ) ends (Q (i−1))` — the orientation the relabel arm's `hρGv`/`hwmem`
slots need (the seed-fixed `shiftBodyFramework` runs the converse direction). -/
noncomputable def _root_.Graph.ChainData.shiftBodyFrameworkAsc [DecidableEq α] {G : Graph α β}
    {n : ℕ} (cd : G.ChainData n) {s : ℕ} (hs : s + 1 < cd.d + 1) (ends : β → α × α)
    (q : α × Fin (k + 2) → ℝ) :
    BodyHingeFramework k α β :=
  (PanelHingeFramework.ofNormals (cd.shiftBodyGraph hs) ends (cd.shiftSeedAdv q s)).toBodyHinge

/-- The graph of the ascending chain `shiftBodyFrameworkAsc s` is `shiftBodyGraph s = G − vₛ₊₁`
(independent of the seed). -/
@[simp]
theorem _root_.Graph.ChainData.shiftBodyFrameworkAsc_graph [DecidableEq α] {G : Graph α β}
    {n : ℕ} (cd : G.ChainData n) {s : ℕ} (hs : s + 1 < cd.d + 1) (ends : β → α × α)
    (q : α × Fin (k + 2) → ℝ) :
    (cd.shiftBodyFrameworkAsc hs ends q).graph = cd.shiftBodyGraph hs := rfl

/-- **The total ascending seed-advancing chain** (the membership half; the `foldl` core
`wstep_foldl_mem_span_rigidityRows` runs over a total `F : ℕ → BodyHingeFramework`). Packages the
partial `shiftBodyFrameworkAsc` (valid at `s + 1 < cd.d + 1`) into that total function, filling the
out-of-range tail with the always-valid `s = 0` member. On the in-range indices the fold touches
(`0, …, i − 1` for a cycle top `i ≤ cd.d`) it agrees by `shiftBodyFrameworkAscTotal_eq`. -/
noncomputable def _root_.Graph.ChainData.shiftBodyFrameworkAscTotal [DecidableEq α] {G : Graph α β}
    {n : ℕ} (cd : G.ChainData n) (ends : β → α × α) (q : α × Fin (k + 2) → ℝ) :
    ℕ → BodyHingeFramework k α β :=
  fun s => if h : s + 1 < cd.d + 1 then cd.shiftBodyFrameworkAsc h ends q
    else cd.shiftBodyFrameworkAsc (s := 0) (by have := cd.hd; omega) ends q

/-- On an in-range index `s + 1 < cd.d + 1`, the total ascending chain agrees with the partial
`shiftBodyFrameworkAsc`. -/
theorem _root_.Graph.ChainData.shiftBodyFrameworkAscTotal_eq [DecidableEq α] {G : Graph α β}
    {n : ℕ} (cd : G.ChainData n) (ends : β → α × α) (q : α × Fin (k + 2) → ℝ) {s : ℕ}
    (hs : s + 1 < cd.d + 1) :
    cd.shiftBodyFrameworkAscTotal ends q s = cd.shiftBodyFrameworkAsc hs ends q := by
  rw [Graph.ChainData.shiftBodyFrameworkAscTotal, dif_pos hs]

/-- **The concrete ascending (base→candidate) seed-advancing fold** (CHAIN-2c-ii-arm, the membership
half feeding the `foldl` core; `notes/Phase23-design.md` §(o‴)(H.10)). The seed-advancing analogue
of `shiftBodyList_foldr_mem_span_rigidityRows` (which runs candidate→base, seed-fixed): the iterated
W9a transport over the ascending moved-body list `shiftBodyListAsc i` carries a source row span at
the **bottom** of the chain — `span (G − v₁)`-rows on seed `q` (`shiftBodyFrameworkAsc 0`) — **up**
to the target row span at the **top** — `span (G − vᵢ)`-rows on the advanced seed `Q (i−1)`
(`shiftBodyFrameworkAsc (i−1)`).

This is the membership content of KT eq.~(6.62) in the base→candidate direction: the `i − 1`
per-body `a`-column subtractions compose along the chain while the seed advances one swap per step
(`Q s = q ∘ (the first s cycle swaps)`). The proof feeds the `foldl` fold core all six per-step
`hstep` conjuncts by applying the **single-step de-risk gate**
`funLeft_dualMap_sub_acolumn_seedAdvance_mem_span_rigidityRows` (which proves the full rise — graph
inclusion, degree-2 closures, and the seed-advancing block agreement — at the single bound
`s + 2 < cd.d`, covering both interior and top steps). The selector `ends` is fixed (so the gate's
`hends'_off` is `rfl`), and the canonical `G`-link-recording hypothesis `hrec` weakens per step to
the `removeVertex` form the gate needs. The relabel side (rewriting the `wstep` fold's leading
`funLeft`-of-swap product to `funLeft (shiftPerm i)`) is the separate `wstep_foldl_funLeft_eq` +
`shiftPerm_eq_prod_map_swap_shiftBodyListAsc` bridge, applied by the arm closer. Graph-free over the
carrier, inheriting W9a's §38-clean discipline. -/
theorem _root_.Graph.ChainData.shiftBodyListAsc_foldl_mem_span_rigidityRows
    [DecidableEq α] {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (i : Fin cd.d)
    (ends : β → α × α) (q : α × Fin (k + 2) → ℝ)
    (hrec : ∀ f x y, G.IsLink f x y → ends f = (x, y) ∨ ends f = (y, x))
    {φ : Module.Dual ℝ (α → ScrewSpace k)}
    (hφ : φ ∈ Submodule.span ℝ
      (cd.shiftBodyFrameworkAsc (s := 0) (by have := i.2; omega) ends q).rigidityRows) :
    ((cd.shiftBodyListAsc i).foldl
        (fun T b => (BodyHingeFramework.wstep (k := k) b.1 b.2.1 b.2.2).comp T) LinearMap.id) φ
      ∈ Submodule.span ℝ
          (cd.shiftBodyFrameworkAsc (s := (i : ℕ) - 1) (by have := i.2; omega) ends q).rigidityRows
            := by
  have hiv : (i : ℕ) < cd.d := i.2
  -- Feed the `foldl` fold core the total ascending chain `F = shiftBodyFrameworkAscTotal` and the
  -- per-step edge `ec s = edge (s+2)` (out-of-range tail arbitrary; the fold touches only
  -- `s ≤ i − 2 < cd.d`).
  have hF0 : cd.shiftBodyFrameworkAscTotal ends q 0
      = cd.shiftBodyFrameworkAsc (s := 0) (by omega) ends q :=
    cd.shiftBodyFrameworkAscTotal_eq ends q (by omega)
  have hFlen : cd.shiftBodyFrameworkAscTotal ends q (cd.shiftBodyListAsc i).length
      = cd.shiftBodyFrameworkAsc (s := (i : ℕ) - 1) (by omega) ends q := by
    rw [cd.length_shiftBodyListAsc, cd.shiftBodyFrameworkAscTotal_eq ends q (by omega)]
  rw [← hFlen]
  refine BodyHingeFramework.wstep_foldl_mem_span_rigidityRows
    (F := cd.shiftBodyFrameworkAscTotal ends q)
    (ec := fun s => if h : s + 2 < cd.d then cd.edge ⟨s + 2, h⟩
      else cd.edge ⟨0, by have := cd.hd; omega⟩)
    (bodies := cd.shiftBodyListAsc i) (hstep := fun s hs => ?_) (hφ := hF0 ▸ hφ)
  -- The per-step `hstep` (step `s < length = i − 1`, so the body `vₛ₊₂` is interior, `s + 2 ≤ i`,
  -- hence `s + 2 < cd.d` since `i < cd.d`). Resolve `F (s+1)`/`F s`/`ec s`/the moved-body triple to
  -- the partial chain and the de-risk gate's roles, then apply the gate as the whole step.
  rw [cd.length_shiftBodyListAsc] at hs
  have hsd : s + 2 < cd.d := by omega
  have hFs : cd.shiftBodyFrameworkAscTotal ends q s
      = cd.shiftBodyFrameworkAsc (s := s) (by omega) ends q :=
    cd.shiftBodyFrameworkAscTotal_eq ends q (by omega)
  have hFs1 : cd.shiftBodyFrameworkAscTotal ends q (s + 1)
      = cd.shiftBodyFrameworkAsc (s := s + 1) (by omega) ends q :=
    cd.shiftBodyFrameworkAscTotal_eq ends q (by omega)
  have hbody : (cd.shiftBodyListAsc i)[s]'(by rw [cd.length_shiftBodyListAsc]; omega)
      = (cd.vtx ⟨s + 1, by omega⟩, cd.vtx ⟨s + 2, by omega⟩, cd.vtx ⟨s + 3, by omega⟩) :=
    cd.getElem_shiftBodyListAsc i s (by rw [cd.length_shiftBodyListAsc]; omega)
  have hec : (if h : s + 2 < cd.d then cd.edge ⟨s + 2, h⟩
      else cd.edge ⟨0, by have := cd.hd; omega⟩) = cd.edge ⟨s + 2, hsd⟩ := dif_pos hsd
  -- Resolve the total chain `F (s+1)`/`F s`/`ec s` to the partial chain and read the moved-body
  -- triple `(shiftBodyListAsc i)[s] = (vₛ₊₁, vₛ₊₂, vₛ₊₃)`. The `foldl` core's per-step `hstep` then
  -- reads the gate's `(v, a, c) = (vtx (s+1), vtx (s+2), vtx (s+3))` roles.
  simp only [hFs1, hFs, hbody, hec]
  -- `F (s+1) = shiftBodyFrameworkAsc (s+1) = ofNormals (G − vₛ₊₂) ends (Q (s+1))`, and
  -- `Q (s+1) = fun p => (Q s)(shiftSeedSwap s p.1, p.2)`, with `shiftSeedSwap s = (vₛ₊₂ vₛ₊₁)`
  -- in range (`hsd`) — so `Q (s+1)` is exactly the de-risk gate's `hstep`-bundle target seed.
  have hQ : cd.shiftSeedAdv q (s + 1)
      = fun p => cd.shiftSeedAdv q s
          (Equiv.swap (cd.vtx ⟨s + 2, by omega⟩) (cd.vtx ⟨s + 1, by omega⟩) p.1, p.2) := by
    rw [cd.shiftSeedAdv_succ, cd.shiftSeedSwap_eq (by omega)]
  -- The six per-step W9a conjuncts (the gate's `hstep` bundle) at the chain step `s`: seed `Q s`,
  -- fixed selector `ends` (so `hends'_off` is `rfl`), the `G`-link-recording `hrec` weakened to the
  -- `removeVertex` form. Unfold the chain frameworks to the `ofNormals (G − vₛ₊₁)`/`(G − vₛ₊₂)`
  -- forms the bundle states, rewriting `Q (s+1)` to the gate's target seed (`hQ`).
  simp only [Graph.ChainData.shiftBodyFrameworkAsc, Graph.ChainData.shiftBodyGraph, hQ]
  exact cd.seedAdvance_wstep_hstep hsd ends ends (cd.shiftSeedAdv q s) (fun _ _ _ => rfl)
    (fun f x y hl => hrec f x y ((Graph.removeVertex_isLink.mp hl).1))

/-- **The removeVertex-level genuine-link transport classification (CHAIN-2c-ii-arm, the genuine-row
`hwmem` make-or-break)** (`lem:case-III` general-`d`, KT 2011 §6.4.2 the (6.62) one-step-down row
correspondence; Phase 23b). A genuine `G`-link `f x y` whose endpoints survive
`removeVertex (vtx 1)` (the `v₁`-base split body, `x ≠ vtx 1`, `y ≠ vtx 1`) transports, under the
inverse index-shift `((shiftPerm i.castSucc)⁻¹, (shiftEdgePerm i)⁻¹)`, to **either** a genuine link
of the candidate-`i` split's `removeVertex (vtx i.castSucc)` graph (the off-cycle /
interior-chain-edge images, both endpoints surviving `removeVertex vᵢ`), **or** the candidate
fresh-edge endpoint pair `{vtx (i+1), vtx (i−1)}` in one of the two orders (the wrap edge `edge i`,
whose endpoints relabel to the candidate's fresh `e₀ = (vtx (i+1)) (vtx (i−1))` short-circuit, so
the image is **not** a `removeVertex vᵢ` link but the candidate `(a,b)`-block).

This is the make-or-break the genuine-row `hwmem` disjunct bottoms out on (design §(o‴)(I.6)): the
**degree-2 closure** `deg_two` (interior chain vertices carry only their two chain edges) rules out
a "homeless interior block" — every genuine `G`-link at a cycle vertex is a chain edge, so it maps
to another chain edge (genuine) or the wrap (the candidate fresh pair), never a stray block. Rather
than re-run the degree-2 case analysis at the removeVertex level, the proof **lifts** the genuine
base row to a link of the `v₁`-base `splitOff` (a survivor, since `f ∈ E(G)` and `e₀ ∉ E(G)`),
applies the landed split-level intertwiner `splitOff_isLink_shiftRelabel_iff` (`.mpr`,
base→candidate via the inverse shift), and reads the resulting candidate-split link back: a
candidate survivor is a genuine `removeVertex vᵢ` link (the fresh-edge label `e₀` cannot be the
survivor edge), while the candidate fresh edge `e₀` records exactly the `{vtx (i+1), vtx (i−1)}`
pair. At the d=3 `M₃` instance `i = 2` the cycle `shiftPerm 2 = (v₁ v₂)` is the single swap and this
is the
`case_III_bottom_relabel` genuine-row branch's three sub-cases. -/
lemma _root_.Graph.ChainData.removeVertex_genuine_shiftRelabel
    [DecidableEq α] [DecidableEq β] {G : Graph α β} {n : ℕ}
    (cd : G.ChainData n) (i : Fin cd.d) (hi : 1 < (i : ℕ))
    {f : β} {x y : α} (hG : G.IsLink f x y)
    (hx1 : x ≠ cd.vtx (⟨1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc)
    (hy1 : y ≠ cd.vtx (⟨1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc) :
    (G.removeVertex (cd.vtx i.castSucc)).IsLink ((cd.shiftEdgePerm i)⁻¹ f)
        ((cd.shiftPerm i.castSucc)⁻¹ x) ((cd.shiftPerm i.castSucc)⁻¹ y) ∨
      (((cd.shiftPerm i.castSucc)⁻¹ x = cd.vtx i.succ ∧
          (cd.shiftPerm i.castSucc)⁻¹ y
            = cd.vtx (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc) ∨
        ((cd.shiftPerm i.castSucc)⁻¹ x
            = cd.vtx (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc ∧
          (cd.shiftPerm i.castSucc)⁻¹ y = cd.vtx i.succ)) := by
  classical
  have hid : (i : ℕ) < cd.d := i.isLt
  -- The fresh `e₀` is not a `G`-edge, so the genuine link `f x y` is a base-split survivor.
  have hfe₀ : f ≠ cd.e₀ := fun he => cd.e₀_fresh (he ▸ hG.edge_mem)
  -- Lift `f x y` to a link of the v₁-base split, then push base→candidate via the inverse shift.
  have hbase : (G.splitOff (cd.vtx (⟨1, by omega⟩ : Fin cd.d).castSucc)
      (cd.vtx (⟨1, by omega⟩ : Fin cd.d).succ) (cd.vtx (⟨0, by omega⟩ : Fin cd.d).castSucc)
      cd.e₀).IsLink f x y :=
    Graph.splitOff_isLink.mpr (Or.inl ⟨hfe₀, hG, hx1, hy1⟩)
  -- The intertwiner `.mpr` at the inverse-shifted candidate data: σ((σ)⁻¹f) = f etc.
  have hcand := (cd.splitOff_isLink_shiftRelabel_iff i hi
      (e := (cd.shiftEdgePerm i)⁻¹ f) (x := (cd.shiftPerm i.castSucc)⁻¹ x)
      (y := (cd.shiftPerm i.castSucc)⁻¹ y)).mpr (by
    simpa using hbase)
  -- `hcand` is a candidate-split link. Read it back: survivor ⇒ removeVertex link; fresh ⇒ wrap.
  rw [Graph.splitOff_isLink] at hcand
  rcases hcand with ⟨hne₀, hGcand, hxv, hyv⟩ | ⟨_, _, _, _, _, hxy⟩
  · exact Or.inl (Graph.removeVertex_isLink.mpr ⟨hGcand, hxv, hyv⟩)
  · exact Or.inr hxy

/-- **The per-member `(shiftPerm i)⁻¹` cycle transport of the `v₁`-base bottom-row disjunction
(CHAIN-2c-ii-arm, the genuine-row `hwmem` leaf `chainData_bottom_relabel`)** (`lem:case-III`
general-`d`, KT 2011 §6.4.2 eqs.~(6.54)/(6.62) the one-step-down row correspondence; Phase 23b).
The cycle generalization of the d=3 `M₃` arm's `case_III_bottom_relabel` from the single swap
`Equiv.swap a v` to the whole `(i−1)`-cycle relabel `(shiftPerm i.castSucc)⁻¹`: it takes the
`v₁`-base `removeVertex (vtx 1)` bottom-row disjunction — a member is either a genuine rigidity row
of the base framework `ofNormals (G.removeVertex (vtx 1)) ends₀ q`, or a `(vtx 2, vtx 0)`-block tag
`hingeRow (vtx 2) (vtx 0) ρ'` (the base split's fresh-edge candidate pair) — to the candidate-`i`
arm's `hwmem` disjunction, under `(funLeft (shiftPerm i.castSucc)⁻¹).dualMap`: a member of the
candidate framework's rigidity rows
`ofNormals (G.removeVertex (vtx i.castSucc)) endsσρ qρ` (with `qρ = q ∘ shiftPerm i.castSucc` the
candidate seed and `endsσρ` the `(shiftPerm i.castSucc)⁻¹`-shifted selector), or a
`(vtx (i+1), vtx (i−1))`-block tag (the candidate split's fresh-edge pair).

This is the genuine-row `hwmem` slot the relabel arm `chainData_relabel_arm` (2c-ii) feeds the
engine `case_III_arm_realization` at the per-`i` roles, exactly as `case_III_arm_realization_M3`'s
`hwmem` case feeds `case_III_bottom_relabel` at `d = 3`. The dispatch (design §(o‴)(I.6)):
* **genuine base row** `hingeRow x y r` at link `f x y` (a `removeVertex (vtx 1)` survivor) — the
  make-or-break crux `removeVertex_genuine_shiftRelabel` classifies the relabelled link as
  **either** a genuine `removeVertex (vtx i.castSucc)` link (off-cycle / interior-chain-edge images,
  both endpoints surviving — `rigidityRow_relabel_to_genuine`) **or** the candidate fresh pair
  `{vtx (i+1), vtx (i−1)}` in one of the two orders (the wrap edge `edge i`, sent to the candidate's
  fresh short-circuit, dispatched to the inline `±r` block tag by the recorded orientation);
* **base `(vtx 2, vtx 0)`-block tag** `hingeRow (vtx 2) (vtx 0) ρ'` — the relabel carries the base
  fresh pair to a *surviving* candidate link, a genuine target row (`blockRow_relabel_perm`),
  exactly as the d=3 `(ab)`-block tag maps to the genuine `e_b`-row.

The per-branch `hsupp`/`hlinkGt` ingredients are supplied by
`ofNormals_supportExtensor_relabel_perm`
(support extensors are graph-independent, so the relabel coincidence holds at the candidate split's
`removeVertex` graph) and the inverse-cycle action lemmas (`seedShift_*`, `shiftPerm_inv_*`,
`shiftEdgePerm_inv_*`). At the d=3 `M₃` instance `i = 2` the cycle `shiftPerm 2 = (v₁ v₂)` is the
single swap and this is exactly `case_III_bottom_relabel`. -/
theorem PanelHingeFramework.chainData_bottom_relabel
    [DecidableEq α] [DecidableEq β] {G : Graph α β} {n : ℕ}
    (cd : G.ChainData n) (i : Fin cd.d) (hi : 1 < (i : ℕ))
    {ends₀ : β → α × α} {q : α × Fin (k + 2) → ℝ}
    (hrec : ∀ e x y, (G.removeVertex
          (cd.vtx (⟨1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc)).IsLink e x y →
      ends₀ e = (x, y) ∨ ends₀ e = (y, x))
    (he₀rec : ends₀ cd.e₀ =
      (cd.vtx (⟨2, by have := i.isLt; omega⟩ : Fin cd.d).castSucc,
        cd.vtx (⟨0, by have := i.isLt; omega⟩ : Fin cd.d).castSucc))
    {φ : Module.Dual ℝ (α → ScrewSpace k)}
    (hφ : φ ∈ (PanelHingeFramework.ofNormals
        (G.removeVertex (cd.vtx (⟨1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc))
        ends₀ q).toBodyHinge.rigidityRows ∨
      ∃ ρ' : Module.Dual ℝ (ScrewSpace k),
        ρ' (panelSupportExtensor
            (fun j => q (cd.vtx (⟨2, by have := i.isLt; omega⟩ : Fin cd.d).castSucc, j))
            (fun j => q (cd.vtx (⟨0, by have := i.isLt; omega⟩ : Fin cd.d).castSucc, j))) = 0 ∧
        φ = BodyHingeFramework.hingeRow
            (cd.vtx (⟨2, by have := i.isLt; omega⟩ : Fin cd.d).castSucc)
            (cd.vtx (⟨0, by have := i.isLt; omega⟩ : Fin cd.d).castSucc) ρ') :
    (LinearMap.funLeft ℝ (ScrewSpace k) (cd.shiftPerm i.castSucc).symm).dualMap φ ∈
      (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i.castSucc))
        (fun e => ((cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).1,
          (cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).2))
        (fun p => q (cd.shiftPerm i.castSucc p.1, p.2))).toBodyHinge.rigidityRows ∨
      ∃ ρ' : Module.Dual ℝ (ScrewSpace k),
        ρ' (panelSupportExtensor
            (fun j => q (cd.shiftPerm i.castSucc (cd.vtx i.succ), j))
            (fun j => q (cd.shiftPerm i.castSucc
              (cd.vtx (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc), j))) = 0 ∧
        (LinearMap.funLeft ℝ (ScrewSpace k) (cd.shiftPerm i.castSucc).symm).dualMap φ =
          BodyHingeFramework.hingeRow (cd.vtx i.succ)
            (cd.vtx (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc) ρ' := by
  classical
  have hid : (i : ℕ) < cd.d := i.isLt
  -- `ρ.symm = ρ⁻¹` for an `Equiv.Perm` (the crux states its classification in `⁻¹` form).
  have hsymm : (cd.shiftPerm i.castSucc).symm = (cd.shiftPerm i.castSucc)⁻¹ := rfl
  rcases hφ with hgen | ⟨ρ', hρ'e₀, rfl⟩
  · -- Genuine base row `hingeRow x y r` at a `removeVertex (vtx 1)` survivor link `f x y`.
    obtain ⟨f, x, y, hlink, r, hr, rfl⟩ := hgen
    rw [PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph,
      Graph.removeVertex_isLink] at hlink
    obtain ⟨hG, hx1, hy1⟩ := hlink
    -- `r` annihilates the `(x, y)`-panel extensor (the base `f`-extensor up to the recorded
    -- orientation, so this absorbs the wrap-edge ±-orientation in one fact).
    have hperp : r (panelSupportExtensor (fun j => q (x, j)) (fun j => q (y, j))) = 0 := by
      have hr' := (BodyHingeFramework.mem_hingeRowBlock_iff _ f r).1 hr
      rw [PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_normal,
        PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_ends] at hr'
      rcases hrec f x y (Graph.removeVertex_isLink.mpr ⟨hG, hx1, hy1⟩) with he | he
      · rw [he] at hr'; exact hr'
      · rw [he, panelSupportExtensor_swap, map_neg, neg_eq_zero] at hr'; exact hr'
    -- The make-or-break classification of the relabelled link `(σ⁻¹ f, ρ⁻¹ x, ρ⁻¹ y)`.
    rcases cd.removeVertex_genuine_shiftRelabel i hi hG hx1 hy1 with
      hgenuine | (⟨hxa, hyb⟩ | ⟨hxb, hya⟩)
    · -- Genuine `removeVertex (vtx i.castSucc)` image (off-cycle / interior-chain-edge): the moving
      -- genuine-row brick at `(u', w', f') = (ρ⁻¹ x, ρ⁻¹ y, σ⁻¹ f)`.
      refine Or.inl ?_
      refine PanelHingeFramework.rigidityRow_relabel_to_genuine (cd.shiftPerm i.castSucc)
        (Gt := G.removeVertex (cd.vtx i.castSucc)) hr rfl rfl hgenuine ?_
      -- `hsupp`: `Q'.supportExtensor (σ⁻¹ f) = Q.supportExtensor f` (graph-independent; the relabel
      -- coincidence cancels `ρ (ρ.symm ·) = ·` and `σ (σ⁻¹ f) = f`).
      simp only [PanelHingeFramework.toBodyHinge_supportExtensor,
        PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_ends,
        Equiv.apply_symm_apply, Equiv.Perm.coe_inv]
    · -- Wrap edge `edge i`: relabelled endpoints land on the candidate fresh pair `(vᵢ₊₁, vᵢ₋₁)`
      -- in the recorded order → `(a,b)`-block, tag `ρ' := r`. `qρ (vtx (i+1)) = q (ρ (vtx (i+1)))`
      -- `= q x` (`hxa`), `qρ (vtx (i−1)) = q y` (`hyb`), so the candidate panel is `C(q x, q y)`,
      -- which `r` annihilates (`hperp`). The relabelled row is `hingeRow (vtx (i+1)) (vtx (i−1))`
      -- `r`, the candidate block tag.
      refine Or.inr ⟨r, ?_, ?_⟩
      · have hax : cd.shiftPerm i.castSucc (cd.vtx i.succ) = x := by
          rw [← hxa]; exact Equiv.apply_symm_apply _ _
        have hby : cd.shiftPerm i.castSucc
            (cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc) = y := by
          rw [← hyb]; exact Equiv.apply_symm_apply _ _
        simp only [hax, hby]; exact hperp
      · rw [BodyHingeFramework.hingeRow_funLeft_dualMap, hsymm, hxa, hyb]
    · -- Wrap edge, swapped recorded order → `(a,b)`-block, tag `ρ' := -r`. Here `ρ` sends the
      -- candidate fresh pair the other way (`qρ (vtx (i+1)) = q y`, `qρ (vtx (i−1)) = q x`), so the
      -- candidate panel is `C(q y, q x) = -C(q x, q y)`, annihilated by `r` (`hperp`); the
      -- relabelled row `hingeRow (vtx (i−1)) (vtx (i+1)) r` is `hingeRow (vtx (i+1)) (vtx (i−1))`
      -- `(-r)` (by `hingeRow_swap`).
      refine Or.inr ⟨-r, ?_, ?_⟩
      · have hbx : cd.shiftPerm i.castSucc (cd.vtx i.succ) = y := by
          rw [← hya]; exact Equiv.apply_symm_apply _ _
        have hay : cd.shiftPerm i.castSucc
            (cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc) = x := by
          rw [← hxb]; exact Equiv.apply_symm_apply _ _
        rw [hbx, hay, LinearMap.neg_apply, panelSupportExtensor_swap, map_neg, neg_neg]
        exact hperp
      · rw [BodyHingeFramework.hingeRow_funLeft_dualMap, hsymm, hxb, hya,
          BodyHingeFramework.hingeRow_swap]
  · -- Base `(vtx 2, vtx 0)`-block tag: relabel carries the base fresh pair to the surviving
    -- candidate link `edge 0` (link `vtx 1 — vtx 0`), a genuine target row (via
    -- `blockRow_relabel_perm`).
    refine Or.inl ?_
    refine PanelHingeFramework.blockRow_relabel_perm (cd.shiftPerm i.castSucc)
      (Gt := G.removeVertex (cd.vtx i.castSucc)) (q₀ := q)
      (e_t := cd.edge ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) hid⟩) ?_ ?_ hρ'e₀
    · -- `edge 0 = vtx 0 — vtx 1`, surviving `removeVertex (vtx i.castSucc)`, at
      -- `(ρ⁻¹ (vtx 2), ρ⁻¹ (vtx 0)) = (vtx 1, vtx 0)`.
      have hpos2 : (cd.shiftPerm i.castSucc).symm
            (cd.vtx (⟨2, by omega⟩ : Fin cd.d).castSucc)
          = cd.vtx (⟨1, by omega⟩ : Fin cd.d).castSucc := by
        rw [hsymm]
        exact cd.shiftPerm_inv_apply_interior i.castSucc (j := 1) le_rfl
          (by simp only [Fin.val_castSucc]; omega)
      have hpos0 : (cd.shiftPerm i.castSucc).symm
            (cd.vtx (⟨0, by omega⟩ : Fin cd.d).castSucc)
          = cd.vtx (⟨0, by omega⟩ : Fin cd.d).castSucc := by
        rw [hsymm]
        exact cd.shiftPerm_inv_apply_vtx_off i.castSucc (by omega) (Or.inl rfl)
      rw [hpos2, hpos0, Graph.removeVertex_isLink]
      refine ⟨(cd.isLink_edge ⟨0, by omega⟩).symm, ?_, ?_⟩
      · exact cd.vtx_ne (m := 1) (m' := (i : ℕ)) (by omega) (by omega) (by omega)
      · exact cd.vtx_ne (m := 0) (m' := (i : ℕ)) (by omega) (by omega) (by omega)
    · -- `hsupp`: `Q'.supportExtensor (edge 0) = base extensor at σ (edge 0) = e₀`, recorded by
      -- `he₀rec` at the base candidate pair `(vtx 2, vtx 0)`.
      rw [PanelHingeFramework.ofNormals_supportExtensor_relabel_perm
        (cd.shiftPerm i.castSucc) (cd.shiftEdgePerm i),
        cd.shiftEdgePerm_apply_edge_zero i (by omega),
        PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_normal,
        PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_ends, he₀rec]

/-- **A relabel-image genuine row lands in the candidate's rigidity-row span** (`lem:case-III
general-d`, the option-(A) chain arm's per-summand `±r`-row routing brick, Phase 23c §I.8.24(4.6);
Katoh–Tanigawa 2011 §6.4.2 the (6.62) one-step-down row correspondence carried into the candidate
framework). The atomic per-summand step of the chain arm's `±r`-row `hg` membership: a base genuine
rigidity row `hingeRow u w r` (`r ∈ (ofNormals Gs ends₀ q₀).hingeRowBlock f`) whose relabel `ρ`
sends its endpoints to a surviving candidate-`(G − vᵢ)` link `f'` **off the two candidate-overridden
slots `{e_c, e_r}`** transports under `(funLeft ρ.symm).dualMap` into the span of the candidate
framework `caseIIICandidate (G − vᵢ) endsσρ qρ e_c e_r n_u n' n_r t`'s rigidity rows.

This composes the two landed bricks the §I.8.24(4.6) Hand-off names: the relabel image is a genuine
row of the *seed* framework `ofNormals (G − vᵢ) endsσρ qρ` (member-MOVING, KT (6.62)) carried into
the candidate's rigidity rows by the off-slot seed-coincidence row bridge
`hingeRow_mem_caseIIICandidate_rigidityRows_of_ofNormals_link`
(`caseIIICandidate_supportExtensor_of_ne`), then `Submodule.subset_span`. The full `±r`-row `hg`
GROUP leaf (`funLeft_dualMap_pmR_group_mem_span_caseIIICandidate` below) `map_sum`s over this brick:
A-1's edge-`i` group is `∑ⱼ cⱼ • hingeRow (uvⱼ)(vvⱼ)(rvⱼ)`, so its relabel image is the
`cⱼ`-combination of these per-summand candidate-span members, hence in the span (closed under
`+`/`•`). The candidate-link survival + off-slot conditions are discharged by the caller from the
chain edge-correspondence (the arm). NO motive/IH/contract change; member-MOVING, no wall (the `±r`
row enters as a genuine candidate-edge member, never the collapsed fixed member). -/
theorem PanelHingeFramework.funLeft_dualMap_genuineRow_mem_span_caseIIICandidate
    [DecidableEq β] {G : Graph α β} (ρ : Equiv.Perm α)
    {endsσρ : β → α × α} {qρ : α × Fin (k + 2) → ℝ} {vᵢ : α}
    {Gs : Graph α β} {ends₀ : β → α × α} {q₀ : α × Fin (k + 2) → ℝ}
    {e_c e_r : β} {n_u n' n_r : Fin (k + 2) → ℝ} {t : ℝ}
    {f f' : β} {u w u' w' : α} {r : Module.Dual ℝ (ScrewSpace k)}
    (hr : r ∈ (PanelHingeFramework.ofNormals Gs ends₀ q₀).toBodyHinge.hingeRowBlock f)
    (hu : ρ.symm u = u') (hw : ρ.symm w = w')
    (h1 : f' ≠ e_c) (h2 : f' ≠ e_r)
    (hlinkGt : (G.removeVertex vᵢ).IsLink f' u' w')
    (hsupp : (PanelHingeFramework.ofNormals (G.removeVertex vᵢ) endsσρ
          qρ).toBodyHinge.supportExtensor f'
        = (PanelHingeFramework.ofNormals Gs ends₀ q₀).toBodyHinge.supportExtensor f) :
    (LinearMap.funLeft ℝ (ScrewSpace k) ρ.symm).dualMap (BodyHingeFramework.hingeRow u w r) ∈
      Submodule.span ℝ (PanelHingeFramework.caseIIICandidate (G.removeVertex vᵢ) endsσρ qρ
        e_c e_r n_u n' n_r t).rigidityRows := by
  -- The relabel image is `hingeRow u' w' r` (member-MOVING, `hu`/`hw`).
  rw [BodyHingeFramework.hingeRow_funLeft_dualMap, hu, hw]
  -- The seed-side block membership at the candidate-`(G − vᵢ)` edge `f'`: `r` annihilates the seed
  -- framework's `f'`-extensor, which `hsupp` identifies with the base `f`-extensor (`hr`).
  have hr' : r ∈ (PanelHingeFramework.ofNormals (G.removeVertex vᵢ) endsσρ
      qρ).toBodyHinge.hingeRowBlock f' := by
    rw [BodyHingeFramework.mem_hingeRowBlock_iff, hsupp]
    exact (BodyHingeFramework.mem_hingeRowBlock_iff _ f r).1 hr
  -- The off-slot row bridge carries the genuine seed row into the candidate's rigidity rows.
  exact Submodule.subset_span
    (PanelHingeFramework.hingeRow_mem_caseIIICandidate_rigidityRows_of_ofNormals_link
      (G.removeVertex vᵢ) endsσρ qρ e_c e_r n_u n' n_r t h1 h2 hlinkGt hr')

/-- **The `±r`-row candidate-span `hg` GROUP membership** (`lem:case-III general-d`, the option-(A)
chain arm's `hg` membership for the `±r` corner row, Phase 23c §I.8.24(4.6); Katoh–Tanigawa 2011
§6.4.2 eq. (6.66), the abstract redundancy `r` carried as a GENUINE candidate-edge group, member-
MOVING). The `±r` row of the chain cert's corner block `g` is the relabel image
`(funLeft (shiftPerm i.castSucc)⁻¹).dualMap` of A-1's edge-`i` base group
`∑_{evⱼ = edge i} cⱼ • hingeRow (uvⱼ)(vvⱼ)(rvⱼ)` — KT's GENUINE candidate-edge `(vᵢvᵢ₊₁)ᵢ∗` row, NOT
the collapsed `hingeRow vᵢ₊₁ vᵢ₋₁ (−ρ₀)` of the dead `chainData_relabel_arm_hρGv` (the
member-mapping wall; the collapsed form would force `ρ₀ ⊥ panelSupportExtensor`, contradicting the
discriminator `hgate`, which is exactly why it is the independent `D`-th row). This GROUP leaf is
what the chain arm puts in the cert's `g`-corner as `rRow`, and the cert
`case_III_rank_certification_chain`'s `hg` is its direct consequence (`Submodule.span`-membership).

The proof is the `map_sum`/`map_smul` push of the relabel-image linear map over the filtered group,
landing each summand in the candidate span by the per-summand brick
`funLeft_dualMap_genuineRow_mem_span_caseIIICandidate` (the relabel image of one genuine base hinge
row at an off-slot surviving candidate link is a candidate-span member), then closing the
`cⱼ`-combination by the span's `+`/`•`-closure (`Submodule.sum_mem`/`smul_mem`). The per-summand
transport data — the relabel image endpoints, the candidate-link survival, the off-slot edge —
enters as a bundled hypothesis `htransport` the arm discharges from the chain edge-correspondence
(KT (6.62) the one-step-down link map, plus the off-`{e_c, e_r}` slot condition). NO motive/IH/
contract change; the `±r` row enters as a genuine candidate-edge member, no wall. -/
theorem PanelHingeFramework.funLeft_dualMap_pmR_group_mem_span_caseIIICandidate
    [DecidableEq β] {G : Graph α β} (ρ : Equiv.Perm α)
    {endsσρ : β → α × α} {qρ : α × Fin (k + 2) → ℝ} {vᵢ : α}
    {Gs : Graph α β} {ends₀ : β → α × α} {q₀ : α × Fin (k + 2) → ℝ}
    {e_c e_r : β} {n_u n' n_r : Fin (k + 2) → ℝ} {t : ℝ}
    {m : ℕ} (c : Fin m → ℝ) (ev : Fin m → β) (uv vv : Fin m → α)
    (rv : Fin m → Module.Dual ℝ (ScrewSpace k)) (e_i : β)
    -- A-1's per-summand base block memberships (the `hrv` of the edge-grouped redundancy):
    (hrv : ∀ j, rv j ∈ (PanelHingeFramework.ofNormals Gs ends₀ q₀).toBodyHinge.hingeRowBlock (ev j))
    -- the per-summand relabel transport data the arm discharges from the chain edge-correspondence:
    (htransport : ∀ j ∈ Finset.univ.filter (fun j => ev j = e_i),
      ∃ f' u' w', ρ.symm (uv j) = u' ∧ ρ.symm (vv j) = w' ∧ f' ≠ e_c ∧ f' ≠ e_r ∧
        (G.removeVertex vᵢ).IsLink f' u' w' ∧
        (PanelHingeFramework.ofNormals (G.removeVertex vᵢ) endsσρ qρ).toBodyHinge.supportExtensor f'
          = (PanelHingeFramework.ofNormals Gs ends₀ q₀).toBodyHinge.supportExtensor (ev j)) :
    (LinearMap.funLeft ℝ (ScrewSpace k) ρ.symm).dualMap
        (∑ j ∈ Finset.univ.filter (fun j => ev j = e_i),
          c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)) ∈
      Submodule.span ℝ (PanelHingeFramework.caseIIICandidate (G.removeVertex vᵢ) endsσρ qρ
        e_c e_r n_u n' n_r t).rigidityRows := by
  classical
  -- Push the relabel-image map through the `cⱼ`-combination (`map_sum`/`map_smul`).
  rw [map_sum]
  refine Submodule.sum_mem _ fun j hj => ?_
  rw [map_smul]
  refine Submodule.smul_mem _ _ ?_
  -- Each summand's relabel image lands in the candidate span by the per-summand brick.
  obtain ⟨f', u', w', hu, hw, h1, h2, hlinkGt, hsupp⟩ := htransport j hj
  exact PanelHingeFramework.funLeft_dualMap_genuineRow_mem_span_caseIIICandidate ρ
    (hrv j) hu hw h1 h2 hlinkGt hsupp

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

/-- **G4d-i for a degree-2 vertex with *two* surviving edges — the `a`-column lands in the sum of
the two incident blocks** (`lem:case-III-claim612-eq644` two-edge form; Katoh–Tanigawa 2011 §6.4.2,
eq.~(6.44) iterated, the genuinely-new `hρGv` P2 leaf, CHAIN-2c-ii-arm). The honest analogue of the
one-edge `acolumn_mem_hingeRowBlock_of_span_rigidityRows` (which forces the column into a *single*
block when `a`'s sole surviving edge is `e_c = ac`) for an **interior chain vertex** `a`, which
after the relabel surgery has **two** surviving links `e_c = ac` and `e_d = ad` (`c ≠ d`). For a
span member `wGv ∈ span Fv.rigidityRows`, its `a`-column restriction `wGv ∘ single a` lands in the
**sum** `Fab.hingeRowBlock e_c ⊔ Fab.hingeRowBlock e_d`: a generator `hingeRow u w ρ` (with
`ρ ∈ Fv.hingeRowBlock f`) touching `a` is, by the two-edge degree-2 field, an `e_c = ac`- or
`e_d = ad`-row, contributing `ρ` (via `hingeRow_comp_single_tail`/`hingeRow_swap`) to the respective
block; a row off `a` contributes `0` (`hingeRow_comp_single_off`). This is KT's eq.~(6.44) two-block
cancellation `∑λ(vₛvₛ₊₁)·r + ∑λ(vₛ₊₁vₛ₊₂)·r = 0` at an interior chain vertex `vₛ₊₁` of degree two —
the carry the `acolumn` one-edge form cannot supply (its `hdeg2` single-edge premise is *false* at a
two-edge vertex). -/
theorem BodyHingeFramework.acolumn_mem_hingeRowBlock_sup_of_span_rigidityRows
    [DecidableEq α] {Fab Fv : BodyHingeFramework k α β}
    {a c d : α} {e_c e_d : β}
    (hac : a ≠ c) (had : a ≠ d)
    (hlink_ec : Fv.graph.IsLink e_c a c)
    (hlink_ed : Fv.graph.IsLink e_d a d)
    (hblock_c : Fv.hingeRowBlock e_c = Fab.hingeRowBlock e_c)
    (hblock_d : Fv.hingeRowBlock e_d = Fab.hingeRowBlock e_d)
    -- `a` is degree-2 in `Fv`: its only links are `e_c = ac` and `e_d = ad`.
    (hdeg2 : ∀ f x, Fv.graph.IsLink f a x → f = e_c ∨ f = e_d)
    (hdeg2r : ∀ f x, Fv.graph.IsLink f x a → f = e_c ∨ f = e_d)
    {wGv : Module.Dual ℝ (α → ScrewSpace k)}
    (hwGv : wGv ∈ Submodule.span ℝ Fv.rigidityRows) :
    wGv.comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a)
      ∈ Fab.hingeRowBlock e_c ⊔ Fab.hingeRowBlock e_d := by
  apply Submodule.span_induction (p := fun ψ _ =>
    ψ.comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a)
      ∈ Fab.hingeRowBlock e_c ⊔ Fab.hingeRowBlock e_d) _ _ _ _ hwGv
  · -- generator case: `hingeRow u w ρ ∈ Fv.rigidityRows`, so `ρ ∈ Fv.hingeRowBlock f`.
    rintro ψ ⟨f, u, w, hlink, ρ, hρ, rfl⟩
    by_cases hau : u = a
    · -- `u = a`: `hdeg2` forces `f ∈ {e_c, e_d}`; `IsLink.right_unique` pins `w` accordingly.
      rw [hau] at hlink
      rcases hdeg2 f w hlink with hfc | hfd
      · rw [hfc] at hlink hρ
        have hwc : w = c := hlink.right_unique hlink_ec
        rw [hau, hwc, hingeRow_comp_single_tail hac]
        exact Submodule.mem_sup_left (hblock_c ▸ hρ)
      · rw [hfd] at hlink hρ
        have hwd : w = d := hlink.right_unique hlink_ed
        rw [hau, hwd, hingeRow_comp_single_tail had]
        exact Submodule.mem_sup_right (hblock_d ▸ hρ)
    · by_cases hwa : w = a
      · -- `w = a`, `u ≠ a`: `hdeg2r` forces `f ∈ {e_c, e_d}`; pin `u` via `IsLink.right_unique`.
        rw [hwa] at hlink
        rcases hdeg2r f u hlink with hfc | hfd
        · rw [hfc] at hlink hρ
          have huc : u = c := hlink.symm.right_unique hlink_ec
          rw [hwa, hingeRow_swap u a ρ, huc, hingeRow_comp_single_tail hac]
          exact Submodule.mem_sup_left ((Fab.hingeRowBlock e_c).neg_mem (hblock_c ▸ hρ))
        · rw [hfd] at hlink hρ
          have hud : u = d := hlink.symm.right_unique hlink_ed
          rw [hwa, hingeRow_swap u a ρ, hud, hingeRow_comp_single_tail had]
          exact Submodule.mem_sup_right ((Fab.hingeRowBlock e_d).neg_mem (hblock_d ▸ hρ))
      · -- `u ≠ a`, `w ≠ a`: off-column, restricts to `0`.
        rw [hingeRow_comp_single_off (Ne.symm hau) (Ne.symm hwa)]
        exact (Fab.hingeRowBlock e_c ⊔ Fab.hingeRowBlock e_d).zero_mem
  · simp [(Fab.hingeRowBlock e_c ⊔ Fab.hingeRowBlock e_d).zero_mem]
  · intro x y _ _ hx hy
    rw [LinearMap.add_comp]
    exact (Fab.hingeRowBlock e_c ⊔ Fab.hingeRowBlock e_d).add_mem hx hy
  · intro r x _ hx
    rw [LinearMap.smul_comp]
    exact (Fab.hingeRowBlock e_c ⊔ Fab.hingeRowBlock e_d).smul_mem r hx

/-! ### The interior-vertex eq.~(6.44) two-edge perp carry (CHAIN-2c-ii-arm, the `hρGv` P2 A-2
de-risk core)

The genuinely-new, self-contained carrier of the `hρGv` arm's per-edge perpendicularity obligation
(`i3_freshEdge_surviving_rows_mem_deRisk`'s `hperp0`/`hperp1`, `freshEdge_surviving_row_mem`'s
`hperp`), discharged FOR REAL from the eq.~(6.52) redundancy witness rather than the *refuted*
generic-`ρ₀` isolated implication (`notes/Phase23-design.md` §(o‴)(I.8.3.v-REFUTED): the bare
`ρ₀ ∈ hingeRowBlock (edge s) → ρ₀ ∈ hingeRowBlock (edge (s+1))` over an arbitrary `ρ₀` is FALSE —
the two-edge crux gives only *sup* membership, and for independent consecutive panels
`block e_c ⊔ block e_d = ⊤`, vacuous). The SETTLED route (§(o‴)(I.8.3.v-SETTLED), Route A) routes
the perp through the **specific** redundancy combination `r̂ := ∑_j λ_{(ab)j} r_j`, whose interior
`a`-columns are non-trivial.

This is the interior-chain-vertex instance of KT's eq.~(6.44) `r̂ = −rAC`
(`candidateRow_ac_eq_neg`, the landed `d = 3` single-degree-2-vertex column equation, KT §6.4.1
eq.~(6.44)) — that lemma already takes the per-edge-grouped witness and **applies verbatim at an
interior chain vertex** `a = vₛ₊₁` (degree-2, incident edges `ab = vₛ₊₁vₛ` and `ac = vₛ₊₁vₛ₊₂`),
which is the structural fix the refuted isolated-implication missed. -/

/-- **The interior-vertex eq.~(6.44) two-edge perp carry** (`lem:case-III-claim612-eq644` interior
form; Katoh–Tanigawa 2011 §6.4.1, eq.~(6.44) at an interior chain vertex, the `hρGv` P2 A-2 de-risk
core, CHAIN-2c-ii-arm, `notes/Phase23-design.md` §(o‴)(I.8.3.v-SETTLED) Route A; Phase 23b). At a
**degree-2** body `a` with the two incident edges' hinges read into the distinct bodies `b` and `c`,
the common candidate vector `r̂ := ∑_j λ_{(ab)j} (rab j)` of KT's eq.~(6.42) is perpendicular to
**both** incident panels `C_c = F.supportExtensor e_c` and `C_d = F.supportExtensor e_d`:

* `r̂ ∈ F.hingeRowBlock e_c` is **direct** — each `rab j ∈ F.hingeRowBlock e_c` (the `ab`-rows are
  block functionals of the `e_c = ab`-hinge), and the block is a submodule closed under the
  `λ`-combination.
* `r̂ ∈ F.hingeRowBlock e_d` is **via eq.~(6.44)** — `candidateRow_ac_eq_neg` reads the column
  vanishing `hcol` of the redundancy combination at body `a` (its degree-2 column has only the
  `ab`/`ac` blocks, `hingeRow_comp_single_tail`/`_off`) as `rAC = −r̂` with
  `rAC := ∑_j λ_{(ac)j} (rac j)`; since each `rac j ∈ F.hingeRowBlock e_d`, so is `rAC`, hence so is
  `r̂ = −rAC` (the block's `neg_mem`).

So `r̂` lies in `hingeRowBlock e_c ⊓ hingeRowBlock e_d` — perpendicular to both incident chain-edge
panels at once. This is the iterated-carry's per-vertex step (KT carries the single redundancy `r̂`
`±`-ly across the `d` panels, eq.~(6.66)); chaining it from the W6b `hρe₀` base discharges the
surviving-row perp at every interior chain edge (`freshEdge_surviving_row_mem`'s `hperp`,
`i3_freshEdge_surviving_rows_mem_deRisk`'s `hperp0`/`hperp1`). Self-contained over the explicit
eq.~(6.52) per-edge witness (the `λ`/`r` data + the combination's `a`-column vanishing): **zero
blast radius**, no live caller touched — the W6b producer strengthening that *supplies* this (A-1)
is the next step. The `supportExtensor`-perp form `..._perp` below is the direct `hperp` shape. -/
theorem BodyHingeFramework.candidate_perp_two_incident_panels [DecidableEq α]
    (F : BodyHingeFramework k α β) {ιab ιac : Type*} [Fintype ιab] [Fintype ιac]
    {a b c : α} {e_c e_d : β} (hab : a ≠ b) (hac : a ≠ c)
    (lamAB : ιab → ℝ) (rab : ιab → Module.Dual ℝ (ScrewSpace k))
    (lamAC : ιac → ℝ) (rac : ιac → Module.Dual ℝ (ScrewSpace k))
    (grest : Module.Dual ℝ (α → ScrewSpace k))
    (hrab : ∀ j, rab j ∈ F.hingeRowBlock e_c)
    (hrac : ∀ j, rac j ∈ F.hingeRowBlock e_d)
    (hcol : ((∑ j, lamAB j • BodyHingeFramework.hingeRow (k := k) (α := α) a b (rab j))
        + (∑ j, lamAC j • BodyHingeFramework.hingeRow (k := k) (α := α) a c (rac j)) + grest).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a) = 0)
    (hrest : grest.comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a) = 0) :
    (∑ j, lamAB j • rab j) ∈ F.hingeRowBlock e_c ∧
      (∑ j, lamAB j • rab j) ∈ F.hingeRowBlock e_d := by
  -- eq.~(6.44): `rAC = −r̂` (the redundancy combination's `a`-column vanishing, regrouped by edge).
  have heq : ∑ j, lamAC j • rac j = -∑ j, lamAB j • rab j :=
    candidateRow_ac_eq_neg hab hac lamAB rab lamAC rac grest hcol hrest
  refine ⟨Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hrab j), ?_⟩
  -- `r̂ = −rAC`, and `rAC ∈ block e_d` (the `λ`-combination of the `ac`-block rows).
  rw [← neg_neg (∑ j, lamAB j • rab j), ← heq]
  exact (F.hingeRowBlock e_d).neg_mem
    (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hrac j))

/-- **The interior-vertex eq.~(6.44) two-edge perp carry, `supportExtensor`-perp form** — the direct
`hperp` shape of `i3_freshEdge_surviving_rows_mem_deRisk` / `freshEdge_surviving_row_mem`
(`lem:case-III-claim612-eq644` interior form; Katoh–Tanigawa 2011 §6.4.1, eq.~(6.44), the
CHAIN-2c-ii-arm `hρGv` P2 A-2 de-risk, Phase 23b). The `mem_hingeRowBlock_iff` restatement of
`candidate_perp_two_incident_panels`: the common candidate vector `r̂ := ∑_j λ_{(ab)j} (rab j)`
annihilates **both** incident panels `F.supportExtensor e_c` and `F.supportExtensor e_d`, given the
per-edge perps in `supportExtensor` form (`hperp_ab`/`hperp_ac`) and the eq.~(6.43) column vanishing
(`hcol`/`hrest`). This is exactly the perp obligation the de-risk gate carries as `hperp0`/`hperp1`
hypotheses — discharged here from the eq.~(6.52) witness, **zero blast radius**. -/
theorem BodyHingeFramework.candidate_perp_two_incident_supportExtensors [DecidableEq α]
    (F : BodyHingeFramework k α β) {ιab ιac : Type*} [Fintype ιab] [Fintype ιac]
    {a b c : α} {e_c e_d : β} (hab : a ≠ b) (hac : a ≠ c)
    (lamAB : ιab → ℝ) (rab : ιab → Module.Dual ℝ (ScrewSpace k))
    (lamAC : ιac → ℝ) (rac : ιac → Module.Dual ℝ (ScrewSpace k))
    (grest : Module.Dual ℝ (α → ScrewSpace k))
    (hperp_ab : ∀ j, rab j (F.supportExtensor e_c) = 0)
    (hperp_ac : ∀ j, rac j (F.supportExtensor e_d) = 0)
    (hcol : ((∑ j, lamAB j • BodyHingeFramework.hingeRow (k := k) (α := α) a b (rab j))
        + (∑ j, lamAC j • BodyHingeFramework.hingeRow (k := k) (α := α) a c (rac j)) + grest).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a) = 0)
    (hrest : grest.comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a) = 0) :
    (∑ j, lamAB j • rab j) (F.supportExtensor e_c) = 0 ∧
      (∑ j, lamAB j • rab j) (F.supportExtensor e_d) = 0 := by
  obtain ⟨hc, hd⟩ := F.candidate_perp_two_incident_panels hab hac lamAB rab lamAC rac grest
    (fun j => (F.mem_hingeRowBlock_iff _ _).2 (hperp_ab j))
    (fun j => (F.mem_hingeRowBlock_iff _ _).2 (hperp_ac j)) hcol hrest
  exact ⟨(F.mem_hingeRowBlock_iff _ _).1 hc, (F.mem_hingeRowBlock_iff _ _).1 hd⟩

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
    (ρ₀ : Module.Dual ℝ (ScrewSpace k)) :
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
    (v0 v1 v2 v4 : α) (ρ₀ : Module.Dual ℝ (ScrewSpace k)) :
    -- `R φ − W φ` (relabel-only foldl minus the `wstep` foldl):
    (BodyHingeFramework.hingeRow v0 v1 ρ₀ : Module.Dual ℝ (α → ScrewSpace k))
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
    {v0 v1 v2 v4 : α} {ρ₀ : Module.Dual ℝ (ScrewSpace k)}
    {S : Submodule ℝ (Module.Dual ℝ (α → ScrewSpace k))}
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
    {ends : β → α × α} {qρ : α × Fin (k + 2) → ℝ} (ρ₀ : Module.Dual ℝ (ScrewSpace k))
    -- the per-edge perp obligations (the genuinely-new P2 content the arm must still discharge):
    (hperp0 : ρ₀ ((PanelHingeFramework.ofNormals (G.removeVertex
        (cd.vtx ⟨3, by omega⟩)) ends qρ).toBodyHinge.supportExtensor (cd.edge ⟨0, by omega⟩)) = 0)
    (hperp1 : ρ₀ ((PanelHingeFramework.ofNormals (G.removeVertex
        (cd.vtx ⟨3, by omega⟩)) ends qρ).toBodyHinge.supportExtensor (cd.edge ⟨1, by omega⟩)) = 0) :
    BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨1, by omega⟩) ρ₀ ∈
        Submodule.span ℝ (PanelHingeFramework.ofNormals (G.removeVertex
          (cd.vtx ⟨3, by omega⟩)) ends qρ).toBodyHinge.rigidityRows ∧
      BodyHingeFramework.hingeRow (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ₀ ∈
        Submodule.span ℝ (PanelHingeFramework.ofNormals (G.removeVertex
          (cd.vtx ⟨3, by omega⟩)) ends qρ).toBodyHinge.rigidityRows := by
  classical
  set Fva := (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨3, by omega⟩))
    ends qρ).toBodyHinge with hFva
  -- A reusable membership builder: a surviving chain edge `edge s` (`s + 1 < 3`) gives a span
  -- member once `ρ₀ ⊥ Fva.supportExtensor (edge s)` (`hp`); the `link` half is concrete.
  have hrow : ∀ s : ℕ, (hs : s + 1 < 3) → ρ₀ (Fva.supportExtensor (cd.edge ⟨s, by omega⟩)) = 0 →
      BodyHingeFramework.hingeRow (cd.vtx ⟨s, by omega⟩) (cd.vtx ⟨s + 1, by omega⟩) ρ₀ ∈
        Submodule.span ℝ Fva.rigidityRows := by
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
    {ends : β → α × α} {qρ : α × Fin (k + 2) → ℝ}
    {φ : Module.Dual ℝ (α → ScrewSpace k)}
    -- the landed W9a fold output `W φ ∈ span (G − v₃) rows`:
    (hW : φ ∈ Submodule.span ℝ (PanelHingeFramework.ofNormals (G.removeVertex
        (cd.vtx ⟨3, by omega⟩)) ends qρ).toBodyHinge.rigidityRows) :
    -- the strongest projection: the interior `v₁`-column lands in the *sup* of the two incident
    -- chain panels — NOT a single block (the route-fork de-risk verdict).
    φ.comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) (cd.vtx ⟨1, by omega⟩)) ∈
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
    {ends : β → α × α} {qρ : α × Fin (k + 2) → ℝ} (ρ₀ : Module.Dual ℝ (ScrewSpace k))
    -- the per-edge perp obligation (the genuinely-new P2 content the arm must still discharge):
    (hperp : ρ₀ ((PanelHingeFramework.ofNormals (G.removeVertex
        (cd.vtx i)) ends qρ).toBodyHinge.supportExtensor (cd.edge ⟨s, by omega⟩)) = 0) :
    BodyHingeFramework.hingeRow (cd.vtx ⟨s, by omega⟩) (cd.vtx ⟨s + 1, by omega⟩) ρ₀ ∈
      Submodule.span ℝ (PanelHingeFramework.ofNormals (G.removeVertex
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
    {ends : β → α × α} {qρ : α × Fin (k + 2) → ℝ}
    {ιab ιac : Type*} [Fintype ιab] [Fintype ιac]
    (lamAB : ιab → ℝ) (rab : ιab → Module.Dual ℝ (ScrewSpace k))
    (lamAC : ιac → ℝ) (rac : ιac → Module.Dual ℝ (ScrewSpace k))
    (grest : Module.Dual ℝ (α → ScrewSpace k))
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
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) (cd.vtx ⟨s + 1, by omega⟩)) = 0)
    (hrest : grest.comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) (cd.vtx ⟨s + 1, by omega⟩)) = 0) :
    BodyHingeFramework.hingeRow (cd.vtx ⟨s, by omega⟩) (cd.vtx ⟨s + 1, by omega⟩)
        (∑ j, lamAB j • rab j) ∈
      Submodule.span ℝ (PanelHingeFramework.ofNormals (G.removeVertex
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
    (ρ : Module.Dual ℝ (ScrewSpace k)) :
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
    (ρ : Module.Dual ℝ (ScrewSpace k)) :
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
    (ρ₀ : Module.Dual ℝ (ScrewSpace k)) :
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
    (ρ₀ : Module.Dual ℝ (ScrewSpace k))
    {S : Submodule ℝ (Module.Dual ℝ (α → ScrewSpace k))}
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
    {ends₀ : β → α × α} {q : α × Fin (k + 2) → ℝ} :
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
    {ends₀ : β → α × α} {q : α × Fin (k + 2) → ℝ} :
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
    {ends₀ : β → α × α} {q : α × Fin (k + 2) → ℝ} (ρ' : Module.Dual ℝ (ScrewSpace k))
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
    {ends : β → α × α} {q : α × Fin (k + 2) → ℝ}
    {wGv : Module.Dual ℝ (α → ScrewSpace k)}
    -- a span member of the base `v₁`-split's rigidity rows (the eq.-(6.24) redundancy `wGv` lives
    -- here):
    (hwGv : wGv ∈ Submodule.span ℝ (PanelHingeFramework.ofNormals (G.removeVertex
        (cd.vtx ⟨1, by omega⟩)) ends q).toBodyHinge.rigidityRows) :
    -- its `vtx 2`-column lands in the *single* block `block (edge 2)` — the immediate-successor
    -- interior vertex is degree-ONE at the base (predecessor edge killed by the `v₁`-removal).
    wGv.comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) (cd.vtx ⟨2, by omega⟩)) ∈
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

/-! ### The base regroup-at-interior-degree-2-vertex column foundation (CHAIN-2c-ii-arm, A-3)

The mechanical column-restriction core the (a′-i) base regroup-at-interior-degree-2-vertex producer
threads through (`notes/Phase23-design.md` §(o‴)(I.8.9); Phase 23b). The A-1 producer
`exists_candidateRow_bottomRows_of_rigidOn` now exposes the candidate row `hρGv` in the
**edge-grouped** form `hingeRow (ab) ρ = ∑ⱼ cGv j • hingeRow (uvGv j)(vvGv j)(rvGv j)` (via
`exists_edgeIndexed_combination_of_mem_span_rigidityRows`); the regroup at a degree-2 interior chain
vertex `a` collects the summands incident to `a` into its two incident-edge groups and discards the
rest. The genuinely-mechanical heart of that regrouping is this lemma: the `a`-column of the sum
over the *non-incident* summands (both endpoints `≠ a`) vanishes — KT eq.~(6.43)/(6.66)'s "every
edge off `a` contributes `0` to the `a`-column", the `grest` half of the eq.~(6.43) witness
`candidate_perp_two_incident_supportExtensors` (A-2) consumes. Framework-free (`hingeRow` reads only
endpoints + screw functional, not the graph), zero blast radius. -/

/-- **The `a`-column of an edge-indexed `hingeRow` combination over summands off `a` vanishes**
(CHAIN-2c-ii-arm, the base regroup column foundation; KT 2011 §6.4.1 eq.~(6.43)/(6.66), Phase 23b).
For a finite ℝ-combination `∑ⱼ cⱼ • hingeRow (uv j)(vv j)(rv j)` in which **every** summand's two
endpoints avoid body `a` (`a ≠ uv j` and `a ≠ vv j`), precomposing with `a`'s screw-column injection
`single a` is `0`: each summand vanishes on the `a`-column by `hingeRow_comp_single_off`, and the
column restriction is additive. This is the `grest`-half (the off-`a` rest vanishes on `a`'s column)
of the eq.~(6.43) regrouping of an edge-grouped redundancy `hρGv` at a degree-2 interior chain
vertex — the `hrest` obligation `candidate_perp_two_incident_supportExtensors` (A-2) /
`freshEdge_surviving_row_mem_of_witness` (A-3) consume. -/
theorem BodyHingeFramework.edgeIndexedCombination_comp_single_off [DecidableEq α]
    (a : α) {n : ℕ} (c : Fin n → ℝ) (uv vv : Fin n → α)
    (rv : Fin n → Module.Dual ℝ (ScrewSpace k))
    (hoff : ∀ j, a ≠ uv j ∧ a ≠ vv j) :
    (∑ j, c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
      (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a) = 0 := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, LinearMap.coe_sum, Finset.sum_apply, LinearMap.zero_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [LinearMap.smul_apply, ← LinearMap.comp_apply,
    BodyHingeFramework.hingeRow_comp_single_off (hoff j).1 (hoff j).2, LinearMap.zero_apply,
    smul_zero]

/-- **The `a`-column of an edge-indexed `hingeRow` combination is its `a`-incident sub-combination's
column** (CHAIN-2c-ii-arm, the base regroup column-isolation core; KT 2011 §6.4.1 eq.~(6.43)/(6.66),
Phase 23b). For a finite ℝ-combination `∑ⱼ cⱼ • hingeRow (uv j)(vv j)(rv j)`, precomposing with body
`a`'s screw-column injection `single a` equals doing so for the restriction to the summands
**incident** to `a` (those with `a = uv j ∨ a = vv j`): split the index set by incidence at `a`, and
the off-`a` part's `a`-column vanishes by `edgeIndexedCombination_comp_single_off`
(`hingeRow_comp_single_off` per summand). This is the column-algebra core of the eq.~(6.43)
regrouping of an edge-grouped redundancy `hρGv` at a degree-2 interior chain vertex `a`: the regroup
proper then uses the degree-2 graph fact (only the two incident chain edges meet `a`) to partition
the incident summands into the `(ab)`/`(ac)` groups `candidate_perp_two_incident_supportExtensors`
(A-2) / `freshEdge_surviving_row_mem_of_witness` (A-3) consume. Framework-free, zero blast
radius. -/
theorem BodyHingeFramework.edgeIndexedCombination_comp_single_eq_incident [DecidableEq α]
    (a : α) {n : ℕ} (c : Fin n → ℝ) (uv vv : Fin n → α)
    (rv : Fin n → Module.Dual ℝ (ScrewSpace k)) :
    (∑ j, c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a)
      = (∑ j ∈ Finset.univ.filter (fun j => a = uv j ∨ a = vv j),
          c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a) := by
  -- Split the full sum into the `a`-incident part and the off-`a` part.
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => a = uv j ∨ a = vv j),
    LinearMap.add_comp]
  -- The off-`a` part's `a`-column vanishes: each summand has `a ≠ uv j` and `a ≠ vv j`.
  have hoff : (∑ j ∈ Finset.univ.filter (fun j => ¬ (a = uv j ∨ a = vv j)),
        c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
      (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a) = 0 := by
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, LinearMap.coe_sum, Finset.sum_apply, LinearMap.zero_apply]
    refine Finset.sum_eq_zero fun j hj => ?_
    obtain ⟨hau, hav⟩ := not_or.mp (Finset.mem_filter.mp hj).2
    rw [LinearMap.smul_apply, ← LinearMap.comp_apply,
      BodyHingeFramework.hingeRow_comp_single_off hau hav, LinearMap.zero_apply, smul_zero]
  rw [hoff, add_zero]

/-- **A single chain-edge group's screw column lands in that edge's hinge-row block**
(CHAIN-2c-ii-arm, the base regroup block-membership core; KT 2011 §6.4.1 eq.~(6.43)/(6.66),
Phase 23b). For an edge-indexed `hingeRow` combination whose every summand `j` carries a
hinge-row-block row `rvⱼ ∈ Fva.hingeRowBlock (evⱼ)`, the screw column at a body `p`
of the **`e`-group** sub-combination (the summands with `evⱼ = e`)
lies in `Fva.hingeRowBlock e`:

`(∑_{evⱼ = e} cⱼ • hingeRow (uvⱼ)(vvⱼ)(rvⱼ)).comp (single p) ∈ Fva.hingeRowBlock e`.

Each summand `j` carried by `e` links `{u, v}` (the link uniqueness pins its endpoints to `e`'s),
so its column at `p` is `±rvⱼ` (`hingeRow_comp_single_tail`/`_swap` at the matching endpoint, or `0`
off both endpoints by `hingeRow_comp_single_off`) — in every case a `block`-member (`rvⱼ ∈ block e`,
closed under scaling and negation). Summing over the group keeps the membership (the block is a
submodule). This is the block-membership half of the eq.~(6.43)/(6.66) regrouping: the `e`-group's
column, read at any body `p`, is `⊥ C(p(e))` — exactly the per-edge perp
`chainData_freshEdge_slot_mem` consumes once the chain induction (LEAF 4) identifies the column with
`−ρ₀`. Framework-bound (the block depends on `Fva`), zero blast radius. -/
theorem BodyHingeFramework.edgeGroup_acolumn_mem_block [DecidableEq α] [DecidableEq β]
    {Fva : BodyHingeFramework k α β} {e : β} {p : α}
    {m : ℕ} (c : Fin m → ℝ) (ev : Fin m → β) (uv vv : Fin m → α)
    (rv : Fin m → Module.Dual ℝ (ScrewSpace k))
    (hrv : ∀ j, rv j ∈ Fva.hingeRowBlock (ev j)) :
    (∑ j ∈ Finset.univ.filter (fun j => ev j = e),
        c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
      (LinearMap.single ℝ (fun _ : α => ScrewSpace k) p) ∈ Fva.hingeRowBlock e := by
  classical
  -- Distribute the column restriction over the filtered sum, then close by the block's submodule
  -- closure (`sum_mem`/`smul_mem`).
  rw [show (∑ j ∈ Finset.univ.filter (fun j => ev j = e),
        c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) p)
      = ∑ j ∈ Finset.univ.filter (fun j => ev j = e),
          (c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
          (LinearMap.single ℝ (fun _ : α => ScrewSpace k) p)
      from LinearMap.ext fun x => by
        simp only [LinearMap.comp_apply, LinearMap.coe_sum, Finset.sum_apply]]
  refine Submodule.sum_mem _ fun j hj => ?_
  have hje : ev j = e := (Finset.mem_filter.mp hj).2
  -- the summand's row `rv j ∈ block e` (after `ev j = e`).
  have hrvj : rv j ∈ Fva.hingeRowBlock e := hje ▸ hrv j
  -- distribute the column over the scalar.
  rw [LinearMap.smul_comp]
  refine Submodule.smul_mem _ _ ?_
  -- read the column as `±rv j` (tail / swapped tail) or `0` (off both endpoints), each a block
  -- member (the block is a submodule, neg-/zero-closed). Loop-safe: `p = uv j = vv j` gives a zero
  -- hinge row (`hingeRow x x ρ = 0`).
  by_cases hpu : p = uv j
  · by_cases hpv : p = vv j
    · -- `p = uv j = vv j`: `hingeRow (uv j) (vv j) (rv j) = hingeRow p p (rv j)`, a zero row.
      have hzero : BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)
          = (0 : Module.Dual ℝ (α → ScrewSpace k)) := by
        rw [← hpu, ← hpv]
        exact LinearMap.ext fun x => by rw [BodyHingeFramework.hingeRow_apply, sub_self, map_zero,
          LinearMap.zero_apply]
      rw [hzero, LinearMap.zero_comp]
      exact (Fva.hingeRowBlock e).zero_mem
    · -- `p = uv j ≠ vv j`: tail column is `rv j`.
      rw [hpu, BodyHingeFramework.hingeRow_comp_single_tail (hpu ▸ hpv)]
      exact hrvj
  · by_cases hpv : p = vv j
    · -- `p = vv j ≠ uv j`: swap to `hingeRow (vv j) (uv j) (−rv j)`, tail column is `−rv j`.
      have hvu : vv j ≠ uv j := fun he => hpu (hpv.trans he)
      rw [hpv, BodyHingeFramework.hingeRow_swap (uv j) (vv j) (rv j),
        BodyHingeFramework.hingeRow_comp_single_tail hvu]
      exact (Fva.hingeRowBlock e).neg_mem hrvj
    · -- `p` off both endpoints: zero column.
      rw [BodyHingeFramework.hingeRow_comp_single_off hpu hpv]
      exact (Fva.hingeRowBlock e).zero_mem

/-! ### The eq.~(6.44) chain-induction step kernel (CHAIN-2c-ii-arm, LEAF 1)

The step kernel of the KT eq.~(6.66) `±r` chain induction
(`notes/Phase23-design.md` §(o‴)(I.8.9-SETTLE), LEAF 1; Phase 23b). At a **deeper** interior
degree-2 chain vertex `a = vtx i.castSucc`
(`2 ≤ i ≤ d−1`) the global base redundancy `g`, exposed edge-grouped as
`∑ⱼ cⱼ • hingeRow (uvⱼ)(vvⱼ)(rvⱼ)` (each summand a `G`-link `evⱼ = uvⱼvvⱼ`), has its `a`-column
governed entirely by the two incident chain edges `edge i` and `edge (i−1)` (the interior degree-2
closure `deg_two_split`: no other `G`-edge meets `a`). Reading the global column-vanishing
`g.comp (single a) = 0` (KT eq.~(6.43)) through the column-isolation core
`edgeIndexedCombination_comp_single_eq_incident` (only `a`-incident summands contribute to the
`a`-column) and partitioning the incident summands by which of the two chain edges carries them
gives KT's eq.~(6.44) at `a`: the successor-edge group's `a`-column is *minus* the predecessor-edge
group's. The two "groups" are the `a`-column restrictions of the per-edge sub-combinations — screw
functionals (`Module.Dual ℝ (ScrewSpace k)`) the chain induction propagates as `±ρ₀`. -/

/-- **The eq.~(6.44) chain-induction step kernel: the two incident chain-edge groups' `a`-columns
cancel** (CHAIN-2c-ii-arm, the `hρGv` regroup chain induction LEAF 1; Katoh–Tanigawa 2011 §6.4.1
eq.~(6.44)/§6.4.2 eq.~(6.66), `notes/Phase23-design.md` §(o‴)(I.8.9-SETTLE); Phase 23b). Let
`g = ∑ⱼ cⱼ • hingeRow (uvⱼ)(vvⱼ)(rvⱼ)` be an edge-indexed `hingeRow` combination in which each
summand `j` is a genuine `G`-link `evⱼ` from `uvⱼ` to `vvⱼ`. At an **interior** chain vertex
`a = cd.vtx i.castSucc` (`0 < i`, so `1 ≤ i ≤ d−1`) — degree-2 in `G` by `cd.deg_two`, its only
incident edges the successor `edge i` and predecessor `edge (i−1)` — the global `a`-column vanishing
`g.comp (single a) = 0` forces the `a`-columns of the two incident-edge sub-combinations to cancel:

`(∑_{evⱼ = edge i} cⱼ • hingeRow (uvⱼ)(vvⱼ)(rvⱼ)).comp (single a)
  = −(∑_{evⱼ = edge (i−1)} cⱼ • hingeRow (uvⱼ)(vvⱼ)(rvⱼ)).comp (single a)`.

The `a`-column restriction `(·).comp (single a)` is orientation-agnostic (it reads `±rvⱼ` per
summand by `hingeRow_comp_single_tail`/`_off`), so the conclusion is exactly the adjacency relation
`group(edge i) = −group(edge (i−1))` the chain induction's step uses, no re-orientation needed.
The proof: the column-isolation core `edgeIndexedCombination_comp_single_eq_incident` reduces the
`a`-column to the `a`-incident summands; the interior degree-2 closure `cd.deg_two_split` partitions
those (disjointly, `edge_inj`) into the `edge i`- and `edge (i−1)`-groups (each chain edge meets `a`
by `cd.isLink_succ_edge`/`cd.isLink_pred_edge`, and every incident summand is one of the two by
`deg_two_split`). Framework-free, zero blast radius. -/
theorem _root_.Graph.ChainData.interiorGroup_acolumn_adjacency [DecidableEq α] [DecidableEq β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) {i : Fin cd.d} (hi : 0 < (i : ℕ))
    {m : ℕ} (c : Fin m → ℝ) (ev : Fin m → β) (uv vv : Fin m → α)
    (rv : Fin m → Module.Dual ℝ (ScrewSpace k))
    (hlink : ∀ j, G.IsLink (ev j) (uv j) (vv j))
    (hcol : (∑ j, c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) (cd.vtx i.castSucc)) = 0) :
    (∑ j ∈ Finset.univ.filter (fun j => ev j = cd.edge i),
        c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
      (LinearMap.single ℝ (fun _ : α => ScrewSpace k) (cd.vtx i.castSucc))
    = -(∑ j ∈ Finset.univ.filter (fun j => ev j = cd.edge ⟨(i : ℕ) - 1, by omega⟩),
        c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
      (LinearMap.single ℝ (fun _ : α => ScrewSpace k) (cd.vtx i.castSucc)) := by
  classical
  set a := cd.vtx i.castSucc with ha
  set ei := cd.edge i with hei
  set ep := cd.edge ⟨(i : ℕ) - 1, by omega⟩ with hep
  -- The two chain edges are distinct (`edge_inj`); each is a `G`-link incident to `a`.
  have hep_ne_ei : ep ≠ ei := (cd.pred_edge_ne hi)
  have hlink_ei : G.IsLink ei a (cd.vtx i.succ) := cd.isLink_succ_edge i
  have hlink_ep : G.IsLink ep a (cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc) :=
    cd.isLink_pred_edge hi
  -- A summand carried by `edge i` (resp. `edge (i−1)`) is incident to `a` (same-edge endpoints).
  have hinc_ei : ∀ j, ev j = ei → a = uv j ∨ a = vv j := fun j hj =>
    (((hlink j).symm.eq_and_eq_or_eq_and_eq (hj ▸ hlink_ei)).imp (·.1.symm) (·.2.symm)).symm
  have hinc_ep : ∀ j, ev j = ep → a = uv j ∨ a = vv j := fun j hj =>
    (((hlink j).symm.eq_and_eq_or_eq_and_eq (hj ▸ hlink_ep)).imp (·.1.symm) (·.2.symm)).symm
  -- Every `a`-incident summand is carried by `edge i` or `edge (i−1)` (interior degree-2 closure).
  have hdeg : ∀ j, (a = uv j ∨ a = vv j) → ev j = ei ∨ ev j = ep := by
    intro j hj
    rcases hj with h | h
    · refine cd.deg_two_split hi (ev j) (vv j) ?_
      rw [← ha, h]; exact hlink j
    · refine cd.deg_two_split hi (ev j) (uv j) ?_
      rw [← ha, h]; exact (hlink j).symm
  -- The `a`-column of `g` is that of its `a`-incident sub-combination (`_eq_incident`); rewrite the
  -- vanishing `hcol` accordingly.
  rw [BodyHingeFramework.edgeIndexedCombination_comp_single_eq_incident a c uv vv rv] at hcol
  -- Partition the incident index set by `ev = edge i`: the `edge i`-part is the `edge i`-group, the
  -- complement (within incident) is the `edge (i−1)`-group (deg-2 closure + `edge_inj` disjoint).
  rw [← Finset.sum_filter_add_sum_filter_not
      (Finset.univ.filter (fun j => a = uv j ∨ a = vv j)) (fun j => ev j = ei),
    LinearMap.add_comp] at hcol
  have he_ei : (Finset.univ.filter (fun j => a = uv j ∨ a = vv j)).filter (fun j => ev j = ei)
      = Finset.univ.filter (fun j => ev j = ei) := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun j _ => ?_
    exact ⟨fun h => h.2, fun h => ⟨hinc_ei j h, h⟩⟩
  have he_ep : (Finset.univ.filter (fun j => a = uv j ∨ a = vv j)).filter (fun j => ¬ ev j = ei)
      = Finset.univ.filter (fun j => ev j = ep) := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun j _ => ?_
    constructor
    · rintro ⟨hinc, hni⟩
      exact (hdeg j hinc).resolve_left hni
    · rintro hj
      exact ⟨hinc_ep j hj, fun h => hep_ne_ei (hj ▸ h)⟩
  rw [he_ei, he_ep] at hcol
  exact eq_neg_of_add_eq_zero_left hcol

/-! ### The eq.~(6.44) chain-induction anchor (CHAIN-2c-ii-arm, LEAF 2)

The base case of the KT eq.~(6.66) `±r` chain induction
(`notes/Phase23-design.md` §(o‴)(I.8.9-SETTLE), LEAF 2; Phase 23b). The chain induction is anchored
at the **first surviving interior chain vertex** `v₂ = cd.vtx 2`. At the base `v₁`-split
`G_v = G − vtx 1`, the `v₁`-removal kills `v₂`'s *predecessor* chain edge `edge 1 = v₁v₂` (which has
the removed apex as an endpoint), so `v₂` is **degree-ONE** in `G_v` — its only surviving incident
edge is the *successor* chain edge `edge 2 = v₂v₃` (the base-side de-risk verdict
`i3_base_interior_acolumn_single_deRisk`, §(o‴)(I.8.9-RESULT)). The candidate row `hρGv`, exposed
edge-grouped over `G_v`-links as `∑ⱼ cⱼ • hingeRow (uvⱼ)(vvⱼ)(rvⱼ) = hingeRow (ab) ρ₀` (the A-1
producer's eq.~(6.66) output), therefore has its `v₂`-column governed entirely by the single
`edge 2`-group: reading the candidate identity through the column-isolation core
`edgeIndexedCombination_comp_single_eq_incident` (only `v₂`-incident summands contribute) and the
degree-1 closure (every `v₂`-incident summand is `edge 2`) gives KT's anchor — the `edge 2`-group's
`v₂`-column equals the candidate row's `v₂`-column, which `hingeRow_comp_single_tail`/`_off` reads
as `±ρ₀` (the `e₀ = v₀v₂`-group of KT's eq.~(6.43) contributing `ρ₀`, the surviving sign absorbed by
the consumer's `neg_mem`). The `v₂`-column restriction `(·).comp (single v₂)` is the
orientation-agnostic screw functional the chain induction propagates as `±ρ₀`. -/

/-- **The eq.~(6.44) chain-induction anchor: the first interior chain-edge group's `v₂`-column is
the candidate row's `v₂`-column** (CHAIN-2c-ii-arm, the `hρGv` regroup chain induction LEAF 2;
Katoh–Tanigawa 2011 §6.4.2 eq.~(6.66) base / §6.4.1 eq.~(6.43), `notes/Phase23-design.md`
§(o‴)(I.8.9-SETTLE); Phase 23b). Let `g = ∑ⱼ cⱼ • hingeRow (uvⱼ)(vvⱼ)(rvⱼ)` be the candidate row
`hρGv` exposed edge-grouped over `G_v`-links (each summand `j` a genuine `G`-link `evⱼ` from `uvⱼ`
to `vvⱼ`), so `g` equals the candidate row `hingeRow ab₁ ab₂ ρ₀` (the A-1 producer's `hcomb`). At
the **first surviving interior chain vertex** `cd.vtx ⟨2, _⟩` — degree-ONE in `G_v = G − vtx 1`, its
only incident summand-edge the successor chain edge `edge ⟨2, _⟩` (the de-risked `hdeg1`) — the
candidate identity forces the `edge 2`-group's `v₂`-column to equal the candidate row's `v₂`-column:

`(∑_{evⱼ = edge 2} cⱼ • hingeRow (uvⱼ)(vvⱼ)(rvⱼ)).comp (single v₂)
  = (hingeRow ab₁ ab₂ ρ₀).comp (single v₂)`.

This is the chain induction's base case `P(2)` in the same `v₂`-column form as the step kernel
LEAF 1 (`interiorGroup_acolumn_adjacency`): the right-hand side is `±ρ₀` once the consumer reads it
through `hingeRow_comp_single_tail`/`_off` (LEAF 4), and the `e₀ = v₀v₂`-group of KT's eq.~(6.43)
contributing `ρ₀` is exactly this candidate row's tail-column. The proof: the column-isolation core
`edgeIndexedCombination_comp_single_eq_incident` reduces the `v₂`-column of `g` to its `v₂`-incident
summands; the degree-1 closure `hdeg1` (every `v₂`-incident summand is `edge 2`, since the
predecessor edge is shorn off at the base) together with "every `edge 2`-summand is `v₂`-incident"
(`hlink` + `IsLink` uniqueness at `edge 2 = v₂v₃`) collapses that to the `edge 2`-group; reading the
candidate identity `hcomb` on the `v₂`-column closes it. Framework-free, zero blast radius. -/
theorem _root_.Graph.ChainData.anchor_group_acolumn_eq_baseRedundancy [DecidableEq α]
    [DecidableEq β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (h3 : 3 ≤ cd.d)
    {m : ℕ} (c : Fin m → ℝ) (ev : Fin m → β) (uv vv : Fin m → α)
    (rv : Fin m → Module.Dual ℝ (ScrewSpace k))
    {ab₁ ab₂ : α} {ρ₀ : Module.Dual ℝ (ScrewSpace k)}
    (hlink : ∀ j, G.IsLink (ev j) (uv j) (vv j))
    (hcomb : (∑ j, c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j))
      = BodyHingeFramework.hingeRow ab₁ ab₂ ρ₀)
    (hdeg1 : ∀ j, (cd.vtx ⟨2, by omega⟩ = uv j ∨ cd.vtx ⟨2, by omega⟩ = vv j) →
      ev j = cd.edge ⟨2, by omega⟩) :
    (∑ j ∈ Finset.univ.filter (fun j => ev j = cd.edge ⟨2, by omega⟩),
        c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
      (LinearMap.single ℝ (fun _ : α => ScrewSpace k) (cd.vtx ⟨2, by omega⟩))
    = (BodyHingeFramework.hingeRow ab₁ ab₂ ρ₀).comp
      (LinearMap.single ℝ (fun _ : α => ScrewSpace k) (cd.vtx ⟨2, by omega⟩)) := by
  classical
  set a := cd.vtx ⟨2, by omega⟩ with ha
  set e2 := cd.edge ⟨2, by omega⟩ with he2
  -- `edge 2` links `vtx 2 — vtx 3` in `G` (`link ⟨2,_⟩`): a `G`-link incident to `a = vtx 2`.
  have hlink_e2 : G.IsLink e2 a (cd.vtx ⟨3, by omega⟩) := by
    have h := cd.link ⟨2, by omega⟩
    simpa only [he2, ha, Fin.castSucc_mk, Fin.succ_mk] using h
  -- A summand carried by `edge 2` is incident to `a` (its endpoints are `a`'s, by `IsLink` uniq).
  have hinc_e2 : ∀ j, ev j = e2 → a = uv j ∨ a = vv j := fun j hj =>
    (((hlink j).symm.eq_and_eq_or_eq_and_eq (hj ▸ hlink_e2)).imp (·.1.symm) (·.2.symm)).symm
  -- The `a`-incident index set equals the `edge 2`-index set: `⊆` by the degree-1 closure `hdeg1`,
  -- `⊇` by `hinc_e2`.
  have hset : Finset.univ.filter (fun j => a = uv j ∨ a = vv j)
      = Finset.univ.filter (fun j => ev j = e2) := by
    refine Finset.filter_congr fun j _ => ?_
    exact ⟨fun h => hdeg1 j h, fun h => hinc_e2 j h⟩
  -- The `a`-column of `g = hingeRow ab₁ ab₂ ρ₀` is that of its `a`-incident sub-combination
  -- (`_eq_incident`); `hset` rewrites the incident set to the `edge 2`-set.
  rw [← hcomb, BodyHingeFramework.edgeIndexedCombination_comp_single_eq_incident a c uv vv rv, hset]

/-! ### The eq.~(6.44) chain-induction endpoint-column flip + the induction itself
(CHAIN-2c-ii-arm, LEAF 3)

The `Nat.le_induction` chaining LEAF 2 (base) and LEAF 1 (step) into the closed form
`(edge i-group).comp (single vᵢ) = ±ρ₀` for every interior chain edge (`2 ≤ i ≤ d−1`); the `±`
sign alternates `(−1)^i` along the chain
(`notes/Phase23-design.md` §(o‴)(I.8.9-SETTLE), LEAF 3; Phase 23b). LEAF 1 relates the two incident
chain edges' columns *at their shared vertex* `vᵢ` (`group(edge i) @ vᵢ = −group(edge (i−1)) @ vᵢ`);
to chain that with the previous step's `P(i−1)` (about `group(edge (i−1)) @ v_{i−1}`, its *tail*
column) the step must flip `group(edge (i−1))`'s column from its head endpoint `vᵢ` back to its tail
`v_{i−1}` — the "two-endpoint-column orientation bookkeeping" of the shape-check note (ii). The flip
is the per-summand `hingeRow` antisymmetry: a hinge row's two endpoint-columns are negatives of each
other (`hingeRow_comp_single_endpoint_flip`), summed over an edge-group whose summands all link the
same pair `{vᵢ, vᵢ₋₁}` (`G`-link uniqueness at `edge (i−1)`). -/

/-- **A hinge row's two endpoint-columns are negatives of each other** (the per-summand orientation
bookkeeping of the eq.~(6.44) chain induction LEAF 3; Katoh–Tanigawa 2011 §6.4.1 eq.~(6.44),
Phase 23b). For a hinge `hingeRow x y ρ` between distinct bodies `x ≠ y`, the screw column at the
head `y` is *minus* the column at the tail `x`: `(hingeRow x y ρ).comp (single y) =
−(hingeRow x y ρ).comp (single x)`. Both columns are `±ρ` (`hingeRow_comp_single_tail` at `x` gives
`ρ`; the swap `hingeRow x y ρ = hingeRow y x (−ρ)` + tail at `y` gives `−ρ`), so they negate. This
is the antisymmetry the chain induction uses to flip an edge-group's column between its two
endpoints. -/
theorem BodyHingeFramework.hingeRow_comp_single_endpoint_flip [DecidableEq α] {x y : α}
    (hxy : x ≠ y) (ρ : Module.Dual ℝ (ScrewSpace k)) :
    (BodyHingeFramework.hingeRow (k := k) (α := α) x y ρ).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) y)
      = -(BodyHingeFramework.hingeRow (k := k) (α := α) x y ρ).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) x) := by
  rw [BodyHingeFramework.hingeRow_comp_single_tail hxy,
    BodyHingeFramework.hingeRow_swap x y ρ,
    BodyHingeFramework.hingeRow_comp_single_tail (Ne.symm hxy)]

/-- **An edge-group's two endpoint-columns are negatives of each other** (the edge-group form of
`hingeRow_comp_single_endpoint_flip`, the eq.~(6.44) chain induction LEAF 3; Katoh–Tanigawa 2011
§6.4.1 eq.~(6.44), Phase 23b). Let `∑ⱼ cⱼ • hingeRow (uvⱼ)(vvⱼ)(rvⱼ)` be an edge-indexed `hingeRow`
combination (each summand `j` a `G`-link `evⱼ`), and let `p ≠ q` be the two endpoints of a chain
edge `e`. Then the `e`-group's screw column at `q` is *minus* its column at `p`:

`(∑_{evⱼ = e} cⱼ • hingeRow (uvⱼ)(vvⱼ)(rvⱼ)).comp (single q)
  = −(∑_{evⱼ = e} cⱼ • hingeRow (uvⱼ)(vvⱼ)(rvⱼ)).comp (single p)`.

Each summand carried by `e` links `{p, q}` (`IsLink` uniqueness, `hpq`), so its two endpoint-columns
negate by `hingeRow_comp_single_endpoint_flip` regardless of its internal orientation (one of two
mirror `hingeRow_swap` cases). Summing the per-summand flip over the group gives the group flip.
This is the "two-endpoint-column orientation bookkeeping" the chain induction's step uses to move an
edge-group's column from its head endpoint to its tail. Framework-free, zero blast radius. -/
theorem BodyHingeFramework.edgeGroup_comp_single_endpoint_flip [DecidableEq α] [DecidableEq β]
    {G : Graph α β} {e : β} {p q : α} (hpq : p ≠ q) (hpq_link : G.IsLink e p q)
    {m : ℕ} (c : Fin m → ℝ) (ev : Fin m → β) (uv vv : Fin m → α)
    (rv : Fin m → Module.Dual ℝ (ScrewSpace k))
    (hlink : ∀ j, G.IsLink (ev j) (uv j) (vv j)) :
    (∑ j ∈ Finset.univ.filter (fun j => ev j = e),
        c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
      (LinearMap.single ℝ (fun _ : α => ScrewSpace k) q)
    = -(∑ j ∈ Finset.univ.filter (fun j => ev j = e),
        c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
      (LinearMap.single ℝ (fun _ : α => ScrewSpace k) p) := by
  classical
  -- Reduce the `LinearMap` equality to scalar equality at each `x`, distribute the column
  -- restriction over the filtered sum on both sides, and compare per summand.
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.coe_sum, Finset.sum_apply]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  -- The summand `j` is carried by `e`, so it links `{p, q}` (`IsLink` uniqueness).
  have hje : ev j = e := (Finset.mem_filter.mp hj).2
  have hjlink : G.IsLink e (uv j) (vv j) := hje ▸ hlink j
  -- Its endpoints are `{p, q}` in one of the two orders; the per-summand endpoint-column flip
  -- (`hingeRow_comp_single_endpoint_flip`) gives the per-summand negation either way.
  have hflip : (BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) q)
      = -(BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) p) := by
    rcases (hpq_link.eq_and_eq_or_eq_and_eq hjlink) with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · -- `p = uv j`, `q = vv j`: the flip `col@q = −col@p` at endpoints `(uv j, vv j)`.
      subst hp hq
      exact BodyHingeFramework.hingeRow_comp_single_endpoint_flip hpq (rv j)
    · -- `p = vv j`, `q = uv j`: the flip at `(uv j, vv j)` gives `col@(vv j) = −col@(uv j)`; the
      -- goal `col@(uv j) = −col@(vv j)` is its `neg`-flipped form.
      subst hp hq
      rw [BodyHingeFramework.hingeRow_comp_single_endpoint_flip (Ne.symm hpq) (rv j), neg_neg]
  rw [LinearMap.smul_apply, LinearMap.smul_apply, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
    hflip, LinearMap.neg_apply, smul_neg]

/-- **The eq.~(6.44) chain induction: every interior chain edge-group's tail-column equals the
anchor's** (CHAIN-2c-ii-arm, the `hρGv` regroup chain induction LEAF 3; Katoh–Tanigawa 2011 §6.4.1
eq.~(6.44)/§6.4.2 eq.~(6.66), `notes/Phase23-design.md` §(o‴)(I.8.9-SETTLE); Phase 23b). For the
**single base redundancy** `g = ∑ⱼ cⱼ • hingeRow (uvⱼ)(vvⱼ)(rvⱼ)` (each summand a `G`-link `evⱼ`)
exposed edge-grouped as the candidate row `hingeRow ab₁ ab₂ ρ₀` (A-1's `hcomb`), whose two endpoints
are the **redundant edge's** chain endpoints `ab₁ = vtx 0`, `ab₂ = vtx 2` (KT eq.~(6.52)'s
`(v₀v₂)`-block redundancy `r`; `hab₁`/`hab₂`), the `edge i`-group's screw column at its **tail**
vertex `vtx i` is the **same** for every interior chain edge `2 ≤ i ≤ d−1`, equal to the anchor
(`edge 2`) column:

`(∑_{evⱼ = edge i} cⱼ • hingeRow (uvⱼ)(vvⱼ)(rvⱼ)).comp (single (vtx i))
  = (hingeRow ab₁ ab₂ ρ₀).comp (single (vtx 2))`.

This is KT eq.~(6.66) — the single redundancy `r` carried with a *consistent* tail-column value
across the chain. The `±` of KT's prose is a per-edge orientation artifact absorbed by the
tail-column reading (`hingeRow_comp_single_endpoint_flip`): the step `P(i) → P(i+1)` applies LEAF 1
(`interiorGroup_acolumn_adjacency` at `i+1`, the `vtx (i+1)`-column adjacency `group(edge (i+1)) =
−group(edge i)`) then flips `group(edge i)`'s column from its head `vtx (i+1)` back to its tail
`vtx i` (`edgeGroup_comp_single_endpoint_flip`, the `−` cancelling LEAF 1's), leaving the value
unchanged; the base `P(2)` is LEAF 2 (`anchor_group_acolumn_eq_baseRedundancy`). The consumer reads
the common value as `±ρ₀` (LEAF 4, `hingeRow_comp_single_tail`/`_off`). Framework-free, zero blast
radius.

**Caller-satisfiability (the corrective, 2026-06-20).** LEAF 1's per-vertex column-vanishing `hcol`
is **not** assumed `∀ a` here — that would be jointly contradictory with `hcomb` for a non-zero
`r̂`: a screw functional on `α → ScrewSpace k` vanishing on every coordinate injection `single a` is
itself `0` (for `[Finite α]`, `LinearMap.pi_ext`), so `hcomb ∧ (∀a, g.comp (single a) = 0)` forces
`hingeRow ab₁ ab₂ ρ₀ = 0`, and the real `hρGv` caller (whose `r̂ = hingeRow (vtx 0)(vtx 2) ρ₀` has
`vtx 2`-column `ρ₀ ≠ 0`) cannot supply it. Instead the step **derives** the column-vanishing it
needs at the deeper step vertex `vtx (i+1)` (`i+1 ≥ 3`, off **both** redundant-edge endpoints
`vtx 0`, `vtx 2` by `vtx_ne`) **internally** from `hcomb` + `hingeRow_comp_single_off`: there
`g.comp (single (vtx (i+1))) = (hingeRow ab₁ ab₂ ρ₀).comp (single (vtx (i+1))) = 0`. This is the
honest content — the anchor `vtx 2` column of `r̂` is `ρ₀ ≠ 0` (LEAF 2 handles it separately, no
`hcol`), and only the deeper step vertices are off `r̂`'s support. -/
theorem _root_.Graph.ChainData.interior_group_eq_baseRedundancy [DecidableEq α] [DecidableEq β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (h3 : 3 ≤ cd.d)
    {m : ℕ} (c : Fin m → ℝ) (ev : Fin m → β) (uv vv : Fin m → α)
    (rv : Fin m → Module.Dual ℝ (ScrewSpace k))
    {ab₁ ab₂ : α} {ρ₀ : Module.Dual ℝ (ScrewSpace k)}
    (hlink : ∀ j, G.IsLink (ev j) (uv j) (vv j))
    (hcomb : (∑ j, c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j))
      = BodyHingeFramework.hingeRow ab₁ ab₂ ρ₀)
    (hab₁ : ab₁ = cd.vtx ⟨0, by omega⟩) (hab₂ : ab₂ = cd.vtx ⟨2, by omega⟩)
    (hdeg1 : ∀ j, (cd.vtx ⟨2, by omega⟩ = uv j ∨ cd.vtx ⟨2, by omega⟩ = vv j) →
      ev j = cd.edge ⟨2, by omega⟩)
    (i : ℕ) (h2i : 2 ≤ i) (hid : i < cd.d) :
    (∑ j ∈ Finset.univ.filter (fun j => ev j = cd.edge ⟨i, by omega⟩),
        c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
      (LinearMap.single ℝ (fun _ : α => ScrewSpace k) (cd.vtx ⟨i, by omega⟩))
    = (BodyHingeFramework.hingeRow ab₁ ab₂ ρ₀).comp
      (LinearMap.single ℝ (fun _ : α => ScrewSpace k) (cd.vtx ⟨2, by omega⟩)) := by
  classical
  induction i, h2i using Nat.le_induction with
  | base =>
    exact cd.anchor_group_acolumn_eq_baseRedundancy h3 c ev uv vv rv hlink hcomb hdeg1
  | succ i h2i ih =>
    -- `i + 1 < cd.d` (the current bound); the predecessor `i` is in range for the IH.
    have hid' : i < cd.d := by omega
    -- The deeper step vertex `vtx (i+1)` (`i+1 ≥ 3`) is off **both** redundant-edge endpoints
    -- `ab₁ = vtx 0`, `ab₂ = vtx 2` (distinct chain indices, `vtx_ne`).
    have hne₁ : cd.vtx (⟨i + 1, by omega⟩ : Fin cd.d).castSucc ≠ ab₁ := by
      rw [hab₁, Fin.castSucc_mk]
      exact cd.vtx_ne (m := i + 1) (m' := 0) (by omega) (by omega) (by omega)
    have hne₂ : cd.vtx (⟨i + 1, by omega⟩ : Fin cd.d).castSucc ≠ ab₂ := by
      rw [hab₂, Fin.castSucc_mk]
      exact cd.vtx_ne (m := i + 1) (m' := 2) (by omega) (by omega) (by omega)
    -- Derive LEAF 1's per-vertex column-vanishing at `vtx (i+1)` INTERNALLY from `hcomb`: the
    -- candidate row `hingeRow ab₁ ab₂ ρ₀` has a zero `vtx (i+1)`-column (off both endpoints,
    -- `hingeRow_comp_single_off`). This is the corrective — `hcol` is NOT assumed `∀ a`.
    have hcol_loc : (∑ j, c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k)
          (cd.vtx (⟨i + 1, by omega⟩ : Fin cd.d).castSucc)) = 0 := by
      rw [hcomb, BodyHingeFramework.hingeRow_comp_single_off hne₁ hne₂]
    -- LEAF 1 at the deeper interior vertex `vtx (i+1)` (index `⟨i+1, _⟩ : Fin cd.d`, `0 < i+1`):
    -- the `edge (i+1)`-group's `vtx (i+1)`-column is `−` the `edge i`-group's `vtx (i+1)`-column.
    have hadj := cd.interiorGroup_acolumn_adjacency (i := ⟨i + 1, by omega⟩) (by simp)
      c ev uv vv rv hlink (by simpa using hcol_loc)
    -- Index arithmetic: `⟨i+1,_⟩.castSucc = ⟨i+1,_⟩`, `⟨(i+1)−1,_⟩ = ⟨i,_⟩`.
    have hcs : (⟨i + 1, by omega⟩ : Fin cd.d).castSucc = (⟨i + 1, by omega⟩ : Fin (cd.d + 1)) :=
      Fin.ext rfl
    have hpred : (⟨(i + 1 : ℕ) - 1, by omega⟩ : Fin cd.d) = (⟨i, by omega⟩ : Fin cd.d) :=
      Fin.ext (by simp)
    rw [hcs, hpred] at hadj
    -- `edge i` links `vtx i — vtx (i+1)` (`cd.link ⟨i,_⟩`), with the two endpoints distinct.
    have hlink_i : G.IsLink (cd.edge ⟨i, by omega⟩) (cd.vtx ⟨i, by omega⟩)
        (cd.vtx ⟨i + 1, by omega⟩) := by
      have h := cd.link (⟨i, by omega⟩ : Fin cd.d)
      simpa only [Fin.castSucc_mk, Fin.succ_mk] using h
    have hpq : (cd.vtx ⟨i, by omega⟩ : α) ≠ cd.vtx ⟨i + 1, by omega⟩ :=
      cd.vtx_ne (by omega) (by omega) (by omega)
    -- Flip the `edge i`-group's column from its head `vtx (i+1)` to its tail `vtx i`: the head
    -- column is `−` the tail column, cancelling LEAF 1's sign.
    have hflip := BodyHingeFramework.edgeGroup_comp_single_endpoint_flip
      (e := cd.edge ⟨i, by omega⟩) hpq hlink_i c ev uv vv rv hlink
    -- `colTail (i+1) = −(edge i-group @ vtx (i+1)) = −(−(edge i-group @ vtx i)) = colTail i = RHS`.
    rw [hadj, hflip, neg_neg]
    exact ih hid'

/-! ### The chain-induction consumer reading: every interior edge-group's tail column is `−ρ₀`
(CHAIN-2c-ii-arm, LEAF 4)

The consumer adapter that turns LEAF 3's *constant common tail column* into the concrete value the
`hρGv` arm consumes: the redundant base row `hingeRow ab₁ ab₂ ρ₀` (`ab₁ = vtx 0`, `ab₂ = vtx 2`, the
eq.~(6.52) spliced edge `e₀ = v₀v₂`) read on its head body `ab₂ = vtx 2`'s screw column is `−ρ₀`
(`hingeRow_swap` + `hingeRow_comp_single_tail`), so LEAF 3's constant value
`(hingeRow ab₁ ab₂ ρ₀).comp (single (vtx 2)) = −ρ₀`. Composed with LEAF 3, every interior chain
edge-group's screw column at its tail body `vᵢ` equals `−ρ₀` (`2 ≤ i ≤ d−1`):

`(∑_{evⱼ = edge i} cⱼ • hingeRow (uvⱼ)(vvⱼ)(rvⱼ)).comp (single vᵢ) = −ρ₀`.

This is KT eq.~(6.66)'s `±r` — the single redundancy `r` carried with the constant screw-column
value `−ρ₀` along the whole interior chain (the `±` is absorbed into the orientation-agnostic
tail-column reading, see LEAF 3). The `hρGv` arm wiring consumes it: the `neg_mem` flips it to the
engine slot's `ρ₀`, and `freshEdge_surviving_row_mem` (via the A-2 carrier) reads it as the per-edge
perp discharge. Framework-free, zero blast radius. -/
theorem _root_.Graph.ChainData.interior_group_acolumn_eq_neg_baseRedundancy [DecidableEq α]
    [DecidableEq β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (h3 : 3 ≤ cd.d)
    {m : ℕ} (c : Fin m → ℝ) (ev : Fin m → β) (uv vv : Fin m → α)
    (rv : Fin m → Module.Dual ℝ (ScrewSpace k))
    {ab₁ ab₂ : α} {ρ₀ : Module.Dual ℝ (ScrewSpace k)}
    (hlink : ∀ j, G.IsLink (ev j) (uv j) (vv j))
    (hcomb : (∑ j, c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j))
      = BodyHingeFramework.hingeRow ab₁ ab₂ ρ₀)
    (hab₁ : ab₁ = cd.vtx ⟨0, by omega⟩) (hab₂ : ab₂ = cd.vtx ⟨2, by omega⟩)
    (hdeg1 : ∀ j, (cd.vtx ⟨2, by omega⟩ = uv j ∨ cd.vtx ⟨2, by omega⟩ = vv j) →
      ev j = cd.edge ⟨2, by omega⟩)
    (i : ℕ) (h2i : 2 ≤ i) (hid : i < cd.d) :
    (∑ j ∈ Finset.univ.filter (fun j => ev j = cd.edge ⟨i, by omega⟩),
        c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
      (LinearMap.single ℝ (fun _ : α => ScrewSpace k) (cd.vtx ⟨i, by omega⟩))
    = -ρ₀ := by
  classical
  -- LEAF 3: the `edge i`-group's tail column is the constant base value
  -- `(hingeRow ab₁ ab₂ ρ₀).comp (single (vtx 2))`.
  rw [cd.interior_group_eq_baseRedundancy h3 c ev uv vv rv hlink hcomb hab₁ hab₂ hdeg1 i h2i hid]
  -- The redundant base row read on its head body `ab₂ = vtx 2`: `hingeRow ab₁ ab₂ ρ₀ =
  -- hingeRow ab₂ ab₁ (−ρ₀)` (`hingeRow_swap`), whose tail column at `ab₂` is `−ρ₀`
  -- (`hingeRow_comp_single_tail`). `ab₁ ≠ ab₂` (distinct chain vertices `vtx 0`/`vtx 2`).
  have hne : ab₂ ≠ ab₁ := by
    rw [hab₁, hab₂]
    exact fun he => by have : (2 : ℕ) = 0 := congrArg Fin.val (cd.vtx_inj he); omega
  rw [← hab₂, BodyHingeFramework.hingeRow_swap ab₁ ab₂ ρ₀,
    BodyHingeFramework.hingeRow_comp_single_tail hne]

/-- **The candidate-transported `±r` column value is `−ρ₀`** (`lem:case-III general-d`, the
option-(A) chain arm's `hrCol` bridge, Phase 23c §I.8.24(4.5)(α); Katoh–Tanigawa 2011 §6.4.2 eqs.
(6.62)/(6.66), the `±r` redundancy carried with constant screw-column value `−ρ₀` across the cycle
relabel). The `notMem_span_mkQ_pmR_row_of_gate` discriminator leaf (`Candidate.lean`) consumes the
`±r` row's column value at the re-inserted candidate body `vᵢ`; this leaf supplies it. The
candidate-`i` `±r` row is the relabel image `(funLeft (shiftPerm i.castSucc)⁻¹).dualMap` of the base
interior edge-`i`-group `φ = ∑_{evⱼ = edge i} cⱼ • hingeRow (uvⱼ)(vvⱼ)(rvⱼ)` (KT (6.56): the
candidate seed `qᵢ = q₁ ∘ ρᵢ` pairs with the **inverse** cycle relabel `(shiftPerm i.castSucc)⁻¹` on
the rows). Reading that candidate row at the candidate base body `vᵢ₋₁ = vtx (i−1)`'s screw column
`single (vtx (i−1))` equals, by the column-naturality bridge `funLeft_dualMap_comp_single`, reading
the base group `φ` at body `((shiftPerm i.castSucc)⁻¹).symm (vtx (i−1)) = shiftPerm i.castSucc
(vtx (i−1)) = vtx i`'s column — which is the base `−ρ₀` of
`interior_group_acolumn_eq_neg_baseRedundancy` (the column read at `vtx i`, `2 ≤ i ≤ d−1`). So the
member MOVES (the row is the relabel image) while the abstract redundancy `ρ₀` stays fixed (the
column value is the constant `−ρ₀`) — the wall-escape, KT's (6.66). At the `d = 3` `M₃` instance
`i = 2` the cycle `shiftPerm 2 = (v₁ v₂)` is the single swap and this is the M₃ arm's
`hingeRow_funLeft_dualMap` + `hingeRow_comp_single_tail` step at length 1. -/
theorem _root_.Graph.ChainData.funLeft_dualMap_interior_group_acolumn_eq_neg_baseRedundancy
    [DecidableEq α] [DecidableEq β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (h3 : 3 ≤ cd.d)
    {m : ℕ} (c : Fin m → ℝ) (ev : Fin m → β) (uv vv : Fin m → α)
    (rv : Fin m → Module.Dual ℝ (ScrewSpace k))
    {ab₁ ab₂ : α} {ρ₀ : Module.Dual ℝ (ScrewSpace k)}
    (hlink : ∀ j, G.IsLink (ev j) (uv j) (vv j))
    (hcomb : (∑ j, c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j))
      = BodyHingeFramework.hingeRow ab₁ ab₂ ρ₀)
    (hab₁ : ab₁ = cd.vtx ⟨0, by omega⟩) (hab₂ : ab₂ = cd.vtx ⟨2, by omega⟩)
    (hdeg1 : ∀ j, (cd.vtx ⟨2, by omega⟩ = uv j ∨ cd.vtx ⟨2, by omega⟩ = vv j) →
      ev j = cd.edge ⟨2, by omega⟩)
    (i : ℕ) (h2i : 2 ≤ i) (hid : i < cd.d) :
    ((LinearMap.funLeft ℝ (ScrewSpace k)
          (cd.shiftPerm (⟨i, by omega⟩ : Fin (cd.d + 1))).symm).dualMap
        (∑ j ∈ Finset.univ.filter (fun j => ev j = cd.edge ⟨i, by omega⟩),
          c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j))).comp
      (LinearMap.single ℝ (fun _ : α => ScrewSpace k) (cd.vtx ⟨i - 1, by omega⟩))
    = -ρ₀ := by
  -- The cycle `shiftPerm ⟨i,_⟩` reads at index `i` (the cycle of `[vtx 1, …, vtx i]`).
  -- Column-naturality (`funLeft_dualMap_comp_single`) at `σ = (shiftPerm ⟨i,_⟩).symm`,
  -- `w = vtx (i−1)`: the candidate column at `vtx (i−1)` is the base group's column at
  -- `σ.symm (vtx (i−1)) = shiftPerm ⟨i,_⟩ (vtx (i−1)) = vtx i`.
  rw [BodyHingeFramework.funLeft_dualMap_comp_single, Equiv.symm_symm]
  -- `shiftPerm ⟨i,_⟩` sends the interior `vtx (i−1)` to `vtx i` (`shiftPerm_apply_interior`,
  -- `1 ≤ i−1 < i`); rewrite the column index `vtx (i−1) ↦ vtx i`.
  have hkey := cd.shiftPerm_apply_interior (⟨i, by omega⟩ : Fin (cd.d + 1))
    (j := i - 1) (by omega) (by simp only; omega)
  have hidx : (⟨(i - 1) + 1, by omega⟩ : Fin (cd.d + 1)) = (⟨i, by omega⟩ : Fin (cd.d + 1)) := by
    simp only [Fin.mk.injEq]; omega
  rw [hidx] at hkey
  rw [hkey]
  -- The base group's column at `vtx i` is `−ρ₀` (eq. (6.66)).
  exact cd.interior_group_acolumn_eq_neg_baseRedundancy h3 c ev uv vv rv hlink hcomb hab₁ hab₂
    hdeg1 i h2i hid

/-! ### P3 — the seed bridge `shiftSeedAdv = q ∘ shiftPerm` (CHAIN-2c-ii-arm)

The seed-advancing fold `shiftBodyListAsc_foldl_mem_span_rigidityRows` proves the `hρGv` span
membership at the *fold* seed `shiftSeedAdv q (i − 1)` — the base seed `q` post-composed (on the
vertex slot) with the first `i − 1` cycle swaps `(v₂ v₁), …, (vᵢ vᵢ₋₁)`, applied one per step.
The arm engine `case_III_arm_realization`, by contrast, binds its candidate seed as `qρ = q ∘
shiftPerm i.castSucc` (KT eq. (6.56), the candidate seed `qᵢ = q₁ ∘ ρᵢ`). These two must coincide
for the fold's span output to feed the engine's `hρGv` slot. They do: the `i − 1` ascending cycle
swaps composed left-to-right ARE `shiftPerm i.castSucc` (the permutation-level G1 bridge
`shiftPerm_eq_prod_map_swap_shiftBodyListAsc`).

The bridge (flagged P3, §(o‴)(I.8.4)/(I.8) — "the fold seed = the engine seed"). At the `d = 3`
`M₃` instance `i = 2` the cycle `shiftPerm 2 = (v₁ v₂)` is the single swap, and `shiftSeedAdv q 1 =
q ∘ swap` is the engine's `qρ` verbatim (zero-regression). -/

/-- **The seed accumulator as a swap-product reindex of `q`** (the P3 closed form). The
seed-advancing accumulator `shiftSeedAdv q s` post-composes the base seed `q` on its vertex slot
with the product of the first `s` per-step cycle swaps `[shiftSeedSwap 0, …, shiftSeedSwap (s−1)]`
(read left-to-right, head outermost). Proved by induction on `s`: the base is `prod [] = 1`, and the
step peels the last swap off `List.ofFn (· + 1)` via `ofFn_succ'` + `List.prod_concat`
(so `(P * swap) x = P (swap x)`), matching `shiftSeedAdv`'s recursion `Q (s+1) = Q s ∘ swap`.
Graph-free over the carrier. -/
theorem _root_.Graph.ChainData.shiftSeedAdv_eq_prod_shiftSeedSwap [DecidableEq α]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (q : α × Fin (k + 2) → ℝ) (s : ℕ) :
    cd.shiftSeedAdv q s
      = fun p => q ((List.ofFn fun t : Fin s => cd.shiftSeedSwap t).prod p.1, p.2) := by
  induction s with
  | zero => simp only [Graph.ChainData.shiftSeedAdv_zero, List.ofFn_zero, List.prod_nil,
      Equiv.Perm.coe_one, _root_.id, Prod.mk.eta]
  | succ s ih =>
    rw [Graph.ChainData.shiftSeedAdv_succ, ih]
    funext p
    -- `ofFn` (over `Fin (s+1)`) peels the last swap off the right (`ofFn_succ'`), and the product
    -- of a `concat` head-applies the trailing swap (`(P * swap) x = P (swap x)`), matching
    -- `shiftSeedAdv`'s recursion `Q (s+1) p = Q s (swap p.1, p.2)`.
    rw [List.ofFn_succ', List.prod_concat]
    simp only [Fin.val_last, Equiv.Perm.coe_mul, Function.comp_apply, Fin.val_castSucc]

/-- **P3 — the fold seed equals the engine seed `q ∘ shiftPerm i.castSucc`** (CHAIN-2c-ii-arm;
the flagged seed bridge `shiftSeedAdv_eq_funLeft_shiftPerm`, design §(o‴)(I.8.4)).
The seed-advancing fold's accumulator at the top step `shiftSeedAdv q (i − 1)` (the seed feeding
`shiftBodyListAsc_foldl_mem_span_rigidityRows`'s span output) coincides with the relabel arm
engine's candidate seed `qρ = fun p => q (shiftPerm i.castSucc p.1, p.2)` (KT eq. (6.56)) — for a
nondegenerate interior candidate `i` (`1 ≤ i`). The proof reads `shiftSeedAdv q (i − 1)` as the
product of the `i − 1` per-step swaps (`shiftSeedAdv_eq_prod_shiftSeedSwap`), then identifies that
product with `shiftPerm i.castSucc` via the permutation-level G1 bridge
`shiftPerm_eq_prod_map_swap_shiftBodyListAsc` (whose `s`-th swap `swap (vtx (s+2)) (vtx (s+1))` is
exactly `shiftSeedSwap s` over the in-range cycle, by `getElem_shiftBodyListAsc` +
`shiftSeedSwap_eq`). Graph-free over the carrier; the `d = 3` `i = 2` instance is the single-swap
`M₃` seed (zero-regression). -/
theorem _root_.Graph.ChainData.shiftSeedAdv_eq_funLeft_shiftPerm [DecidableEq α]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (q : α × Fin (k + 2) → ℝ) (i : Fin cd.d)
    (hi : 1 ≤ (i : ℕ)) :
    cd.shiftSeedAdv q ((i : ℕ) - 1)
      = fun p => q (cd.shiftPerm i.castSucc p.1, p.2) := by
  rw [cd.shiftSeedAdv_eq_prod_shiftSeedSwap q ((i : ℕ) - 1)]
  -- The `i − 1`-fold swap product is `shiftPerm i.castSucc` (the ascending G1 bridge), after
  -- matching the per-step swaps element-for-element (`shiftSeedSwap s = swap (vₛ₊₂) (vₛ₊₁)`).
  have hlist : (List.ofFn fun t : Fin ((i : ℕ) - 1) => cd.shiftSeedSwap t)
      = (cd.shiftBodyListAsc i).map (fun b => Equiv.swap b.2.1 b.1) := by
    refine List.ext_getElem (by simp only [List.length_ofFn, List.length_map,
      cd.length_shiftBodyListAsc]) fun s h₁ h₂ => ?_
    simp only [List.getElem_ofFn, List.getElem_map, cd.getElem_shiftBodyListAsc]
    have hs : s + 2 < cd.d + 1 := by
      simp only [List.length_ofFn] at h₁; have := i.2; omega
    rw [cd.shiftSeedSwap_eq hs]
  rw [hlist, ← cd.shiftPerm_eq_prod_map_swap_shiftBodyListAsc i]

/-! ### The general-`i` `hρGv` fresh-edge slot membership (CHAIN-2c-ii-arm, LEAF 5 core)

The general-candidate-`i` lift of the `i = 3` de-risk gate `i3_freshEdge_slot_mem_deRisk` from the
abstract span carrier `S` to the *concrete* fold framework, threading the genuinely-new infra of
LEAF-ρ1/the chain induction into the engine `hρGv` slot. Given the W6b base redundancy
`hingeRow (vtx 0) (vtx 2) ρ₀ ∈ span (G − v₁) rows` and, for each surviving interior chain edge
`edge s` (`s + 1 < (i : ℕ)`), the per-edge perp `ρ₀ ⊥ Fva.supportExtensor (edge s)` (the P2 content
the chain induction LEAF 4 + the A-2 carrier supply), the fresh-edge slot row
`hingeRow (vtx (i−1)) (vtx (i+1)) ρ₀` — the engine `case_III_arm_realization.hρGv` slot
`hingeRow vᵢ₋₁ vᵢ₊₁ ρ` at candidate `i` — reaches the candidate framework's rigidity-row span.

The assembly: feed the base redundancy through the landed seed-advancing W9a fold
(`shiftBodyListAsc_foldl_mem_span_rigidityRows`, output span at `shiftBodyFrameworkAsc (i−1) =
ofNormals (G − vᵢ) ends (shiftSeedAdv q (i−1))`), giving `W φ ∈ span`; the landed closed-form
telescope `wstep_foldl_freshEdge_slot_mem` then peels the slot row off `W φ` minus the `m = i − 1`
genuine surviving chain-edge rows, each supplied by `freshEdge_surviving_row_mem` from its per-edge
perp. KT eq. (6.66) realized concretely. The `d = 3` `M₃` `case hρGv` is the `i = 2` (`m = 1`,
single-summand) special case (zero-regression). This isolates LEAF 5's hard core; the arm wiring
`chainData_relabel_arm` rewrites the fold seed `shiftSeedAdv q (i−1)` to the engine seed `qρ`
(P3 `shiftSeedAdv_eq_funLeft_shiftPerm`), flips the orientation (`hingeRow_swap`), and discharges
the per-edge perps from LEAF 4 + A-2. -/
theorem _root_.Graph.ChainData.chainData_freshEdge_slot_mem [DecidableEq α]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (i : Fin (cd.d + 1))
    (hi : 1 ≤ (i : ℕ)) (hid : (i : ℕ) < cd.d)
    (ends : β → α × α) (q : α × Fin (k + 2) → ℝ)
    (hrec : ∀ f x y, G.IsLink f x y → ends f = (x, y) ∨ ends f = (y, x))
    {ρ₀ : Module.Dual ℝ (ScrewSpace k)}
    -- the W6b base redundancy `hingeRow (vtx 0)(vtx 2) ρ₀ ∈ span (G − v₁) rows`:
    (hφ : BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ₀ ∈
      Submodule.span ℝ
        (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩)) ends
          (cd.shiftSeedAdv q 0)).toBodyHinge.rigidityRows)
    -- the per-edge perp obligations (P2: each surviving chain-edge panel is ⊥ ρ₀):
    (hperp : ∀ s : ℕ, (hs : s + 1 < (i : ℕ)) → ρ₀ ((PanelHingeFramework.ofNormals
        (G.removeVertex (cd.vtx ⟨(i : ℕ), by omega⟩)) ends
          (cd.shiftSeedAdv q ((i : ℕ) - 1))).toBodyHinge.supportExtensor
          (cd.edge ⟨s, by omega⟩)) = 0) :
    BodyHingeFramework.hingeRow (cd.vtx ⟨(i : ℕ) - 1, by omega⟩) (cd.vtx ⟨(i : ℕ) + 1, by omega⟩) ρ₀
      ∈ Submodule.span ℝ (PanelHingeFramework.ofNormals
        (G.removeVertex (cd.vtx ⟨(i : ℕ), by omega⟩)) ends
          (cd.shiftSeedAdv q ((i : ℕ) - 1))).toBodyHinge.rigidityRows := by
  classical
  -- the `Fin cd.d` version of the candidate index (for the fold lemma + the seed bridge).
  let i' : Fin cd.d := ⟨(i : ℕ), hid⟩
  have hi'v : (i' : ℕ) = (i : ℕ) := rfl
  -- the candidate framework `Fva = ofNormals (G − vᵢ) ends (shiftSeedAdv q (i−1))`.
  set Fva := (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨(i : ℕ), by omega⟩)) ends
    (cd.shiftSeedAdv q ((i : ℕ) - 1))).toBodyHinge with hFva
  -- the `ℕ → α` vertex function for the telescope: `w s = vtx (min s d)` (agrees with `vtx s` on
  -- the range `[0, i+1] ⊆ [0, d]` the fold touches).
  let w : ℕ → α := fun s => cd.vtx ⟨min s cd.d, Nat.lt_succ_of_le (min_le_right s cd.d)⟩
  have hws : ∀ s : ℕ, (h : s < cd.d + 1) → s ≤ cd.d → w s = cd.vtx ⟨s, h⟩ := by
    intro s h hs; exact congrArg cd.vtx (Fin.ext (min_eq_left hs))
  -- `w` is injective on `[0, (i−1)+2] = [0, i+1] ⊆ [0, d]` (`vtx_inj` + `min` collapse).
  have hinj : Set.InjOn w (Set.Iic (((i : ℕ) - 1) + 2)) := by
    intro x hx y hy hxy
    rw [Set.mem_Iic] at hx hy
    rw [hws x (by omega) (by omega), hws y (by omega) (by omega)] at hxy
    have := congrArg Fin.val (cd.vtx_inj hxy); omega
  -- `shiftBodyFrameworkAsc (i'−1) = Fva` (seed `shiftSeedAdv q (i−1)`, graph
  -- `G − v_{(i−1)+1} = G − vᵢ`).
  have hidx : (⟨((i' : ℕ) - 1) + 1, by have := i'.2; omega⟩ : Fin (cd.d + 1))
      = ⟨(i : ℕ), by omega⟩ := Fin.ext (by simp only [hi'v]; omega)
  have hFvaEq : cd.shiftBodyFrameworkAsc (s := (i' : ℕ) - 1) (by have := i'.2; omega) ends q
      = Fva := by
    rw [Graph.ChainData.shiftBodyFrameworkAsc, hFva]
    congr 2
    rw [Graph.ChainData.shiftBodyGraph]
    exact congrArg (fun x => G.removeVertex (cd.vtx x)) hidx
  -- fold start framework `shiftBodyFrameworkAsc 0 = ofNormals (G − v₁) ends (shiftSeedAdv q 0)`.
  have hFvaStart : cd.shiftBodyFrameworkAsc (s := 0) (by have := i'.2; omega) ends q
      = (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩)) ends
          (cd.shiftSeedAdv q 0)).toBodyHinge := by
    rw [Graph.ChainData.shiftBodyFrameworkAsc, Graph.ChainData.shiftBodyGraph]
  -- `hW`: the seed-advancing fold lands `W φ ∈ span Fva.rigidityRows` (`shiftBodyFrameworkAsc
  -- (i−1) = Fva`, after feeding the base redundancy `hφ` matched to the start framework).
  have hfold := cd.shiftBodyListAsc_foldl_mem_span_rigidityRows i' ends q hrec
    (φ := BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ₀)
    (hFvaStart ▸ hφ)
  rw [hFvaEq] at hfold
  -- The body list `shiftBodyListAsc i'` is the telescope's `List.ofFn (· ↦ (w (s+1), w (s+2),
  -- w (s+3)))` shape (`w s = vtx s` on the touched range `s ≤ i+1 ≤ d`); and `vtx 0/2 = w 0/2`.
  have hbodies : cd.shiftBodyListAsc i'
      = List.ofFn fun s : Fin ((i' : ℕ) - 1) =>
          (w ((s : ℕ) + 1), w ((s : ℕ) + 2), w ((s : ℕ) + 3)) := by
    rw [Graph.ChainData.shiftBodyListAsc]
    congr 1
    funext s
    rw [hws ((s : ℕ) + 1) (by omega) (by omega), hws ((s : ℕ) + 2) (by omega) (by omega),
      hws ((s : ℕ) + 3) (by omega) (by omega)]
  have hw02 : BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ₀
      = BodyHingeFramework.hingeRow (w 0) (w 2) ρ₀ := by
    rw [hws 0 (by omega) (by omega), hws 2 (by omega) (by omega)]
  rw [hbodies, hw02] at hfold
  -- the `hsurv` summands: each surviving chain-edge row `hingeRow (w s) (w (s+1)) ρ₀ ∈ span`
  -- via `freshEdge_surviving_row_mem` from its per-edge perp `hperp s`.
  have hsurv : ∀ s ∈ Finset.range ((i' : ℕ) - 1),
      BodyHingeFramework.hingeRow (w s) (w (s + 1)) ρ₀ ∈ Submodule.span ℝ Fva.rigidityRows := by
    intro s hs
    rw [Finset.mem_range] at hs
    rw [hws s (by omega) (by omega), hws (s + 1) (by omega) (by omega)]
    -- `freshEdge_surviving_row_mem`'s framework `ofNormals (G − vᵢ) ends (shiftSeedAdv q (i−1))`
    -- is exactly `Fva` (up to the `set` abbreviation).
    exact cd.freshEdge_surviving_row_mem i s (by omega) ρ₀ (hperp s (by omega))
  -- Apply the telescope (`m = i' − 1 = i − 1`): peel the slot row `hingeRow (w m) (w (m+2)) ρ₀`
  -- off the fold output minus the `m` genuine surviving rows.
  have hslot := BodyHingeFramework.wstep_foldl_freshEdge_slot_mem w ((i' : ℕ) - 1) hinj ρ₀ hfold
    hsurv
  -- the slot row is the conclusion after `w m = vtx (i−1)`, `w (m+2) = vtx (i+1)`.
  rw [hws ((i' : ℕ) - 1) (by omega) (by omega),
    hws (((i' : ℕ) - 1) + 2) (by omega) (by omega)] at hslot
  convert hslot using 4
  omega

/-- **The per-edge perp discharge from the eq.~(6.52) two-edge witness** (CHAIN-2c-ii-arm, the
`hρGv` P2 A-2 composition step; `notes/Phase23-design.md` §(o‴)(I.8.3.v-SETTLED) Route A,
§(o‴)(I.8.9-SETTLE); Phase 23b). The single-edge form of the per-edge perp that
`chainData_freshEdge_slot_mem`'s `hperp` slot consumes: from the eq.~(6.52) `λ`-grouped two-edge
witness at the surviving edge's interior degree-2 chain vertex `vtx (s+1)` (the same witness the W6b
producer `exists_candidateRow_bottomRows_of_rigidOn` supplies, A-1), the common candidate redundancy
`ρ₀ = ∑_j λ_{(ab)j} (rab j)` is ⊥ the candidate framework's `supportExtensor (edge s)`.

The interior vertex `a := vtx (s+1)` is degree-2 with the two incident chain edges `e_c := edge s`
(to its predecessor `b := vtx s`) and `e_d := edge (s+1)` (to its successor `c := vtx (s+2)`).
Feeding the witness perps `hperp_ab`/`hperp_ac` and the eq.~(6.43) column vanishing `hcol`/`hrest`
through `candidate_perp_two_incident_supportExtensors` (A-2, KT eq.~(6.44)) yields the perp at
`e_c = edge s`; the supplied regroup identity `hρ₀` (`∑_j λ_{(ab)j} (rab j) = ρ₀`, the chain
induction LEAF 4's `group = ±ρ₀` reading) rewrites it onto the shared `ρ₀` of the slot core. This
is the exact `hperp s` shape `chainData_freshEdge_slot_mem` takes per surviving chain edge; the arm
`chainData_relabel_arm` calls it once per `s + 1 < i` to supply that slot's `hperp` from the
witnesses. Self-contained over the explicit witness, zero blast radius. -/
theorem _root_.Graph.ChainData.chainData_freshEdge_perp_of_witness [DecidableEq α]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (i : Fin (cd.d + 1)) (s : ℕ)
    (hsd : s + 1 < cd.d)
    {ends : β → α × α} {qρ : α × Fin (k + 2) → ℝ}
    {ιab ιac : Type*} [Fintype ιab] [Fintype ιac]
    (lamAB : ιab → ℝ) (rab : ιab → Module.Dual ℝ (ScrewSpace k))
    (lamAC : ιac → ℝ) (rac : ιac → Module.Dual ℝ (ScrewSpace k))
    (grest : Module.Dual ℝ (α → ScrewSpace k))
    {ρ₀ : Module.Dual ℝ (ScrewSpace k)}
    -- the regroup identity: the `(ab)`-group is the shared slot redundancy `ρ₀` (LEAF 4):
    (hρ₀ : (∑ j, lamAB j • rab j) = ρ₀)
    -- the per-edge witness-row perps, in the candidate framework `Fva = ofNormals (G−vᵢ)`:
    (hperp_ab : ∀ j, rab j ((PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i)) ends qρ)
      |>.toBodyHinge.supportExtensor (cd.edge ⟨s, by omega⟩)) = 0)
    (hperp_ac : ∀ j, rac j ((PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i)) ends qρ)
      |>.toBodyHinge.supportExtensor (cd.edge ⟨s + 1, by omega⟩)) = 0)
    -- the eq.~(6.43) column vanishing at the degree-2 interior vertex `a = vtx (s+1)`:
    (hcol : ((∑ j, lamAB j • BodyHingeFramework.hingeRow (k := k) (α := α)
          (cd.vtx ⟨s + 1, by omega⟩) (cd.vtx ⟨s, by omega⟩) (rab j))
        + (∑ j, lamAC j • BodyHingeFramework.hingeRow (k := k) (α := α)
          (cd.vtx ⟨s + 1, by omega⟩) (cd.vtx ⟨s + 2, by omega⟩) (rac j)) + grest).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) (cd.vtx ⟨s + 1, by omega⟩)) = 0)
    (hrest : grest.comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) (cd.vtx ⟨s + 1, by omega⟩)) = 0) :
    ρ₀ ((PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i)) ends qρ)
      |>.toBodyHinge.supportExtensor (cd.edge ⟨s, by omega⟩)) = 0 := by
  classical
  set Fva := (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i)) ends qρ).toBodyHinge
    with hFva
  -- The interior vertex `a = vtx (s+1)` differs from its two chain neighbours `b = vtx s`,
  -- `c = vtx (s+2)` (distinct chain indices, `vtx_inj`).
  have hab : cd.vtx ⟨s + 1, by omega⟩ ≠ cd.vtx ⟨s, by omega⟩ :=
    fun he => by have : s + 1 = s := congrArg Fin.val (cd.vtx_inj he); omega
  have hac : cd.vtx ⟨s + 1, by omega⟩ ≠ cd.vtx ⟨s + 2, by omega⟩ :=
    fun he => by have : s + 1 = s + 2 := congrArg Fin.val (cd.vtx_inj he); omega
  -- A-2 (KT eq.~(6.44)): the common candidate `∑_j λ_{(ab)j} (rab j)` is ⊥ the panel at the
  -- surviving edge `e_c = edge s`; rewrite onto the shared `ρ₀` via the regroup identity.
  have hperp := (Fva.candidate_perp_two_incident_supportExtensors hab hac lamAB rab lamAC rac grest
    hperp_ab hperp_ac hcol hrest).1
  rwa [hρ₀] at hperp

/-- **The per-edge perp discharged from the single candidate-framework base redundancy**
(CHAIN-2c-ii-arm, the `hρGv` P2 Route-W all-`i` lift; `notes/Phase23-design.md`
§(o‴)(I.8.9-SETTLE); Phase 23b). The witness-free closure of the per-edge perpendicularity that
`chainData_freshEdge_slot_mem` consumes: instead of supplying the eq.~(6.52) two-edge witness
vertex-by-vertex (`chainData_freshEdge_perp_of_witness`), it is discharged for **every** deeper
interior surviving chain edge `edge s` (`2 ≤ s`, `s < cd.d`) from the *one* candidate-framework base
redundancy, exposed edge-grouped (A-1's `hcomb`,
`exists_edgeIndexed_combination_of_mem_span_rigidityRows`).

The mechanism is KT eq.~(6.66)'s iterated degree-2 `±r` carry, now closed in two landed halves:
- the **chain induction LEAF 4** (`interior_group_acolumn_eq_neg_baseRedundancy`) — the `edge
  s`-group's screw column at its tail vertex `vtx s` is `−ρ₀`, the single redundancy `r` carried
  with a constant column value along the chain (eq.~(6.44) iterated, anchored at the spliced
  `e₀ = v₀v₂`);
- the **column-in-block core** (`edgeGroup_acolumn_mem_block`) — that same `edge s`-group column
  lies in `Fva.hingeRowBlock (edge s)` (each summand carried by `edge s` reads
  `±rv j ∈ block (edge s)` on the column, the block closed under negation and zero).

Combining, `−ρ₀ ∈ Fva.hingeRowBlock (edge s)`, so `ρ₀ ∈ Fva.hingeRowBlock (edge s)`
(negation-closed), which is exactly `ρ₀ ⊥ Fva.supportExtensor (edge s)` (`mem_hingeRowBlock_iff`).
No per-vertex witness production, no eq.~(6.52) `λ`-data threading — the arm `chainData_relabel_arm`
supplies the slot core's `hperp` for all deeper surviving edges from this one base redundancy. The
first surviving edge (the degree-1 anchor `edge 2`) is the `s = 2` instance (LEAF 4's base `P(2)`).
Framework-bound, zero blast radius. -/
theorem _root_.Graph.ChainData.chainData_freshEdge_perp_of_baseRedundancy
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (h3 : 3 ≤ cd.d)
    (i : Fin (cd.d + 1)) (s : ℕ) (h2s : 2 ≤ s) (hsd : s < cd.d)
    {ends : β → α × α} {qρ : α × Fin (k + 2) → ℝ}
    {m : ℕ} (c : Fin m → ℝ) (ev : Fin m → β) (uv vv : Fin m → α)
    (rv : Fin m → Module.Dual ℝ (ScrewSpace k))
    {ρ₀ : Module.Dual ℝ (ScrewSpace k)}
    -- the candidate-framework `Fva = ofNormals (G − vᵢ)` edge-grouped base redundancy (A-1 `hcomb`)
    (hlink : ∀ j, G.IsLink (ev j) (uv j) (vv j))
    (hrv : ∀ j, rv j ∈ (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i)) ends
      qρ).toBodyHinge.hingeRowBlock (ev j))
    (hcomb : (∑ j, c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j))
      = BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ₀)
    -- the degree-1-at-anchor closure (the first surviving interior vertex `vtx 2`):
    (hdeg1 : ∀ j, (cd.vtx ⟨2, by omega⟩ = uv j ∨ cd.vtx ⟨2, by omega⟩ = vv j) →
      ev j = cd.edge ⟨2, by omega⟩) :
    ρ₀ ((PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i)) ends
      qρ).toBodyHinge.supportExtensor (cd.edge ⟨s, by omega⟩)) = 0 := by
  classical
  set Fva := (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i)) ends qρ).toBodyHinge
    with hFva
  -- The `edge s`-group's `vtx s`-column is `−ρ₀` (chain induction LEAF 4), and lands in
  -- `Fva.hingeRowBlock (edge s)` (the column-in-block core). So `−ρ₀ ∈ block (edge s)`.
  have hcolval := cd.interior_group_acolumn_eq_neg_baseRedundancy h3 c ev uv vv rv hlink hcomb
    rfl rfl hdeg1 s h2s hsd
  have hmem := Fva.edgeGroup_acolumn_mem_block (e := cd.edge ⟨s, by omega⟩)
    (p := cd.vtx ⟨s, by omega⟩) c ev uv vv rv hrv
  rw [hcolval] at hmem
  -- `−ρ₀ ∈ block (edge s) ⟹ ρ₀ ∈ block ⟹ ρ₀ ⊥ supportExtensor (edge s)`.
  have hρ₀mem : ρ₀ ∈ Fva.hingeRowBlock (cd.edge ⟨s, by omega⟩) := by
    have := (Fva.hingeRowBlock (cd.edge ⟨s, by omega⟩)).neg_mem hmem
    rwa [neg_neg] at this
  exact (Fva.mem_hingeRowBlock_iff (cd.edge ⟨s, by omega⟩) ρ₀).1 hρ₀mem

/-! ### The i=3 candidate-level edge-grouped transport de-risk (CHAIN-2c-ii-arm)

The row-352 GAP-FOUND recon (`notes/Phase23-design.md` §(o‴)(I.8); Phase 23b) located the single
remaining gap between the landed `hρGv` pieces and the arm `chainData_relabel_arm`: the per-edge
perp leaf `chainData_freshEdge_perp_of_baseRedundancy` consumes the edge-grouped base redundancy
`hcomb` together with the per-summand block memberships `hrv : ∀ j, rv j ∈ Fva.hingeRowBlock (ev j)`
**at the CANDIDATE framework** `Fva = ofNormals (G − vᵢ) endsσρ qρ`, but the W6b producer A-1
(`exists_candidateRow_bottomRows_of_rigidOn`) supplies the edge-grouped redundancy only at the
**BASE** framework `ofNormals (G − v₁) ends q` (`Candidate.lean`). No landed lemma transports the
edge-grouped block memberships from base to candidate (candidate-level `hrv` appears only as a
hypothesis, never a conclusion).

The flagged subtlety (de-risk-first, row-321 discipline): A-1's base summand edges `ev j` are
ARBITRARY `(G − v₁)`-links — they need NOT be `shiftEdgePerm`-images of candidate chain edges. The
de-risk question is whether the per-summand block transport is nonetheless clean: does
`rv j ∈ (base).hingeRowBlock (ev j)` transport to a candidate block membership without re-grouping?

**Verdict (this lemma, ground-truth in Lean): YES — the per-summand transport is a clean bijective
re-index, NOT a re-grouping.** The candidate framework's `hingeRowBlock` at an ARBITRARY edge `f`
equals the base framework's `hingeRowBlock` at `(shiftEdgePerm i) f` (the support extensors coincide
under the relabel, `ofNormals_supportExtensor_relabel_perm`, for *every* edge — the base graph is
irrelevant since `supportExtensor` reads only `ends`/`normal`). So A-1's base membership
`rv j ∈ (base).hingeRowBlock (ev j)` is exactly the candidate membership
`rv j ∈ Fva.hingeRowBlock ((shiftEdgePerm i).symm (ev j))` — i.e. the candidate-side summand edges
are the `(shiftEdgePerm i)⁻¹`-images of A-1's base edges, a BIJECTIVE re-labelling of the existing
summands (no summand is dropped, split, or merged). This resolves Q1/Q2/Q3 of the de-risk: the
non-alignment of `ev j` with chain edges is a **non-issue**, because the block correspondence holds
for arbitrary edges and the downstream chain induction (LEAVES 1–4) groups summands by *filtering*
`ev j = cd.edge ⟨i⟩` and discards non-incident contributions via the degree-2 closure — it never
requires the summand edges to be aligned. The transport leaf
`chainData_candidateRow_edgeGrouped_transport` therefore decomposes into: (1) carry `hrv` via this
block correspondence under the `(shiftEdgePerm i).symm`-re-index of the edge family; (2) carry the
combination `hcomb` across the `(funLeft (shiftPerm i.castSucc).symm).dualMap` relabel (as
`chainData_bottom_relabel` carries genuine rows); (3) the chain `G`-links carry by `cd.link`
combinatorics. NO motive/IH/contract change.

This `i = 3`/single-edge de-risk anchors the verdict at the first honest case before any transport
leaf signature is pinned (the row-321 failure mode is a confident pin ahead of the de-risk). -/
theorem _root_.Graph.ChainData.i3_candidateBlock_transport_deRisk
    [DecidableEq α] [DecidableEq β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (i : Fin cd.d)
    {ends₀ : β → α × α} {q : α × Fin (k + 2) → ℝ}
    (f : β) {r : Module.Dual ℝ (ScrewSpace k)}
    -- A-1's base block membership at an ARBITRARY base edge `f` (the W6b producer's `hrv j`):
    (hbase : r ∈ (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i.castSucc))
        ends₀ q).toBodyHinge.hingeRowBlock f) :
    -- transports to the candidate framework's block at the `(shiftEdgePerm i)⁻¹`-image of `f`:
    r ∈ (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i.castSucc))
        (fun e => ((cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).1,
          (cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).2))
        (fun p => q (cd.shiftPerm i.castSucc p.1, p.2))).toBodyHinge.hingeRowBlock
          ((cd.shiftEdgePerm i).symm f) := by
  classical
  -- The candidate block at `g := σ⁻¹ f` equals the base block at `σ (σ⁻¹ f) = f` (support extensors
  -- coincide for ANY edge under the relabel; graph-independent).
  rw [BodyHingeFramework.hingeRowBlock,
    PanelHingeFramework.ofNormals_supportExtensor_relabel_perm (cd.shiftPerm i.castSucc)
      (cd.shiftEdgePerm i) ((cd.shiftEdgePerm i).symm f),
    Equiv.apply_symm_apply]
  -- Now the candidate block at `σ⁻¹ f` is literally the base block at `f` (the two base frameworks
  -- differ only in their irrelevant graph; `supportExtensor` reads only `ends₀`/`q`).
  simpa only [BodyHingeFramework.hingeRowBlock, PanelHingeFramework.toBodyHinge_supportExtensor,
    PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal] using hbase

/-- **T-1 — the candidate-level edge-grouped transport, block half** (CHAIN-2c-ii-arm, the de-risked
half of the row-352 GAP transport leaf `chainData_candidateRow_edgeGrouped_transport`;
`notes/Phase23-design.md` §(o‴)(I.8.10) sub-leaf T-1; KT 2011 §6.4.2 eqs. (6.59)/(6.62) the
index-shift panel correspondence; Phase 23b).

The all-`i`/`∀ j` lift of the single-edge de-risk anchor `i3_candidateBlock_transport_deRisk`: A-1's
edge-grouped base output (`exists_candidateRow_bottomRows_of_rigidOn`, `Candidate.lean`) carries a
family of per-summand block memberships `rvGv j ∈ (base).hingeRowBlock (evGv j)` over **arbitrary**
base links `evGv j`, but `chainData_freshEdge_perp_of_baseRedundancy`'s `hrv` (h3) wants them at the
**candidate** framework `Fva = ofNormals (G − vᵢ) endsσρ qρ`. This lemma transports each summand's
membership to the candidate block at the `(shiftEdgePerm i)⁻¹`-image of its base edge — a clean
BIJECTIVE re-index of the family (no summand dropped, split, or merged), per the de-risk verdict
(Q2-with-a-twist). The candidate-side edge family the perp leaf then consumes is
`evGv' j := (shiftEdgePerm i).symm (evGv j)`.

Each `j` is the anchor at `f := evGv j`; the proof is a per-summand replay. TRANSPORT, no new math:
no motive/IH/contract change, no genuinely-new-math fork. d=3 (`i = 2`) is the landed `M₃` swap
involution. -/
theorem _root_.Graph.ChainData.chainData_candidateRow_edgeGrouped_transport_blocks
    [DecidableEq α] [DecidableEq β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (i : Fin cd.d)
    {ends₀ : β → α × α} {q : α × Fin (k + 2) → ℝ}
    {m : ℕ} (evGv : Fin m → β) (rvGv : Fin m → Module.Dual ℝ (ScrewSpace k))
    -- A-1's edge-grouped base block memberships at arbitrary base links `evGv j` (the W6b
    -- producer's `hrv`, at the base framework `ofNormals (G − vᵢ) ends₀ q`):
    (hrv : ∀ j, rvGv j ∈ (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i.castSucc))
        ends₀ q).toBodyHinge.hingeRowBlock (evGv j)) :
    -- transport to the candidate framework's block at the `(shiftEdgePerm i)⁻¹`-re-indexed edges:
    ∀ j, rvGv j ∈ (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i.castSucc))
        (fun e => ((cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).1,
          (cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).2))
        (fun p => q (cd.shiftPerm i.castSucc p.1, p.2))).toBodyHinge.hingeRowBlock
          ((cd.shiftEdgePerm i).symm (evGv j)) :=
  fun j => cd.i3_candidateBlock_transport_deRisk i (evGv j) (hrv j)

/-- **T-2 — the candidate-level edge-grouped transport, combination half** (CHAIN-2c-ii-arm, the
`hcomb`-relabel half of the row-352 GAP transport leaf
`chainData_candidateRow_edgeGrouped_transport`; `notes/Phase23-design.md` §(o‴)(I.8.10) sub-leaf
T-2; KT 2011 §6.4.2 eqs.~(6.62)/(6.66) the index-shift row correspondence; Phase 23b).

Carries A-1's base combination identity
`hingeRow x y ρ = ∑ⱼ c j • hingeRow (uv j) (vv j) (rv j)`
(`exists_candidateRow_bottomRows_of_rigidOn`'s edge-grouped tail, `Candidate.lean`, over the base
endpoints `x y` of the fresh pair) across the relabel `(funLeft σ.symm).dualMap` (`σ = shiftPerm
i.castSucc`) to the candidate orientation
`hingeRow (σ.symm x) (σ.symm y) ρ = ∑ⱼ c j • hingeRow (σ.symm (uv j)) (σ.symm (vv j)) (rv j)`.

The relabel is a single linear map, so it distributes over the finite sum (`map_sum`) and the
scalar multiples (`map_smul`); each `hingeRow` summand transports endpoint-wise by
`hingeRow_funLeft_dualMap` (`(funLeft ρ).dualMap (hingeRow u v r) = hingeRow (ρ u) (ρ v) r`, no
involution on `ρ` needed). This is **exactly** the linearity step `chainData_bottom_relabel`
(`:1939`) performs on a single genuine row, lifted across the `∑ⱼ c j • ·`. The endpoint relabel
`uv' j := σ.symm (uv j)` makes the candidate combination's RHS match the `(shiftEdgePerm i)⁻¹`-re-
indexed links T-3 supplies. TRANSPORT, no new math: no motive/IH/contract change. d=3 (`i = 2`) is
the landed `M₃` single-swap involution. -/
theorem _root_.Graph.ChainData.chainData_candidateRow_edgeGrouped_transport_comb
    [DecidableEq α]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (i : Fin cd.d)
    {m : ℕ} (c : Fin m → ℝ) (uv vv : Fin m → α)
    (rv : Fin m → Module.Dual ℝ (ScrewSpace k))
    {x y : α} {ρ : Module.Dual ℝ (ScrewSpace k)}
    -- A-1's base combination identity (`exists_candidateRow_bottomRows_of_rigidOn`):
    (hcomb : BodyHingeFramework.hingeRow x y ρ
      = ∑ j, c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)) :
    -- the `(funLeft σ.symm).dualMap`-relabelled candidate-orientation combination:
    BodyHingeFramework.hingeRow ((cd.shiftPerm i.castSucc).symm x)
        ((cd.shiftPerm i.castSucc).symm y) ρ
      = ∑ j, c j • BodyHingeFramework.hingeRow ((cd.shiftPerm i.castSucc).symm (uv j))
          ((cd.shiftPerm i.castSucc).symm (vv j)) (rv j) := by
  -- Apply the linear relabel `(funLeft σ.symm).dualMap` to both sides of A-1's identity, then
  -- read each `hingeRow` summand endpoint-wise by `hingeRow_funLeft_dualMap`.
  have hmap := congrArg
    (LinearMap.funLeft ℝ (ScrewSpace k) (cd.shiftPerm i.castSucc).symm).dualMap hcomb
  rw [BodyHingeFramework.hingeRow_funLeft_dualMap, map_sum] at hmap
  simp only [map_smul, BodyHingeFramework.hingeRow_funLeft_dualMap] at hmap
  exact hmap

/-- **STEP 2 — the single-scalar per-edge perp transport, base → candidate** (CHAIN-2c-ii-arm, the
last un-landed piece of the `hρGv` perp slot; `notes/Phase23-design.md` §(o‴)(I.8.11) STEP 2/STEP
2′; KT 2011 §6.4.2 eqs.~(6.62)/(6.66) the index-shift panel correspondence; Phase 23b).

The route-settling recon (§(o‴)(I.8.11)) replaced the mis-targeted row-354 *family* transport
(`chainData_candidateRow_edgeGrouped_transport_{blocks,comb}`, now orphaned) with this single-scalar
transport: KT works entirely at the base `(G₁,q₁) = G − v₁`, and the only thing crossing to the
candidate-`i` framework is the *scalar* perpendicularity. The base perp at the `shiftEdgePerm`-image
of the candidate chain edge transports to the candidate framework's perp at that edge:

- `(candidate).supportExtensor (edge s) = (base).supportExtensor (shiftEdgePerm i (edge s))`
  (`ofNormals_supportExtensor_relabel_perm` — support extensors coincide under the `(ρ, σ)` relabel
  for *every* edge, with `(ρ, σ) = (shiftPerm i.castSucc, shiftEdgePerm i)`);
- `shiftEdgePerm i (edge s) = edge (s + 1)` for an interior step (`1 ≤ s`, `s + 1 < i`,
  `shiftEdgePerm_apply_edge_interior`) and `= e₀` for the head step `s = 0`
  (`shiftEdgePerm_apply_edge_zero`, the STEP 2′ branch — the splice-panel annihilation `hρe₀` A-1
  already supplies). The two branches merge under `if s = 0 then e₀ else edge (s + 1)`;
- `supportExtensor` reads only `ends`/`normal` (`ofNormals_ends`/`ofNormals_normal`), so the base
  perp's graph is irrelevant — it is taken at an arbitrary `Gb` and bridged to the candidate split
  graph `G − vᵢ` for free.

The candidate `ends`/`q` are the relabelled forms `(endsσρ, qρ)` of A-1's base `ends₀`/`q` (the same
forms `ofNormals_relabel_perm` / `chainData_bottom_relabel` produce); in the arm the base perp comes
from STEP 1 (`chainData_freshEdge_perp_of_baseRedundancy` at base index `⟨1⟩`, no transport) or
`hρe₀`, and this lemma feeds `chainData_freshEdge_slot_mem`'s `hperp s`. TRANSPORT, no new math: no
motive/IH/contract change, no new-math fork. d=3 (`i = 2`) is the landed `M₃` involution. -/
theorem _root_.Graph.ChainData.chainData_freshEdge_perp_transport_base_to_candidate
    [DecidableEq α] [DecidableEq β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (i : Fin cd.d) (hi : 1 ≤ (i : ℕ))
    (s : ℕ) (hs1i : s + 1 < (i : ℕ))
    {Gb : Graph α β} {ends₀ : β → α × α} {q : α × Fin (k + 2) → ℝ}
    {ρ₀ : Module.Dual ℝ (ScrewSpace k)}
    -- the base perp at the `shiftEdgePerm`-image of the candidate chain edge (STEP 1 / `hρe₀`):
    (hbase : ρ₀ ((PanelHingeFramework.ofNormals Gb ends₀ q).toBodyHinge.supportExtensor
        (if s = 0 then cd.e₀ else cd.edge ⟨s + 1, by have := i.isLt; omega⟩)) = 0) :
    -- transports to the candidate framework's perp at `edge s`:
    ρ₀ ((PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i.castSucc))
        (fun e => ((cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).1,
          (cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).2))
        (fun p => q (cd.shiftPerm i.castSucc p.1, p.2))).toBodyHinge.supportExtensor
          (cd.edge ⟨s, by have := i.isLt; omega⟩)) = 0 := by
  classical
  -- The candidate-framework support extensor at `edge s` equals the base framework's at
  -- `σ (edge s) = shiftEdgePerm i (edge s)` (graph-independent; the relabel coincidence lemma).
  rw [PanelHingeFramework.ofNormals_supportExtensor_relabel_perm (cd.shiftPerm i.castSucc)
    (cd.shiftEdgePerm i) (cd.edge ⟨s, by have := i.isLt; omega⟩)]
  -- Resolve `σ (edge s)`: `e₀` at the head (`s = 0`), `edge (s+1)` interior (`1 ≤ s`, `s+1 < i`).
  rcases Nat.eq_zero_or_pos s with hs0 | hs0
  · subst hs0
    rw [cd.shiftEdgePerm_apply_edge_zero i hi]
    -- Bridge the base graph `G − vᵢ` to `Gb`: `supportExtensor` reads only `ends₀`/`q`.
    simpa only [if_pos rfl, PanelHingeFramework.toBodyHinge_supportExtensor,
      PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal] using hbase
  · rw [cd.shiftEdgePerm_apply_edge_interior i hs0 hs1i]
    simpa only [if_neg (by omega : ¬ s = 0), PanelHingeFramework.toBodyHinge_supportExtensor,
      PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal] using hbase

/-- **STEP 1 ∘ STEP 2 — the per-edge perp the slot core consumes, from A-1's base data**
(CHAIN-2c-ii-arm, the `chainData_relabel_arm` `hperp` feed; `notes/Phase23-design.md`
§(o‴)(I.8.11) STEP 3; KT 2011 §6.4.2 eqs.~(6.62)/(6.66); Phase 23b). The composition the arm
assembly invokes once per surviving chain edge `s` (`s + 1 < i`): it produces the candidate-`i`
framework's perp `ρ₀ ⊥ Fva.supportExtensor (edge s)` — exactly `chainData_freshEdge_slot_mem`'s
`hperp s` shape — directly from the W6b base outputs (A-1,
`exists_candidateRow_bottomRows_of_rigidOn` at the base `(G₁, q₁) = G − v₁`), with no
candidate-framework redundancy hypothesis.

The two halves are the LANDED STEP 1 (`chainData_freshEdge_perp_of_baseRedundancy`, the
witness-free per-edge perp at the BASE) and STEP 2
(`chainData_freshEdge_perp_transport_base_to_candidate`, the single-scalar base → candidate
transport):
* for an **interior** surviving edge (`1 ≤ s`), STEP 1 at base index `⟨1⟩` (so its framework is the
  base `ofNormals (G − v₁) ends₀ q`) and edge index `t := s + 1` (`2 ≤ s + 1 < cd.d`) gives the BASE
  perp `ρ₀ ⊥ (base).supportExtensor (edge (s+1))`; STEP 2 (`Gb := G − v₁`) carries it to the
  candidate perp at `edge s`;
* for the **head** edge `s = 0`, the base perp at `e₀` is the splice-panel annihilation `hρe₀` A-1
  already supplies (`ρ₀ ⊥ (base).supportExtensor e₀`), and STEP 2′ carries it to `edge 0`.

The `if s = 0 then e₀ else edge (s+1)` of STEP 2's `hbase` slot merges the two branches. The base
edge-grouped redundancy (`hlink`/`hrv`/`hcomb`/`hdeg1`) is A-1's at the base framework
`ofNormals (G − v₁) ends₀ q` (NOT the candidate `endsσρ`/`qρ` — STEP 1 runs at the base, the
row-352/354 level mismatch's fix, §(o‴)(I.8.11)); the produced perp is at the candidate framework
`endsσρ`/`qρ`, exactly the slot core's `Fva`. TRANSPORT + the landed base leaf, no new math: no
motive/IH/contract change, no genuinely-new-math fork. d=3 (`i = 2`) is the landed `M₃` cycle. -/
theorem _root_.Graph.ChainData.chainData_freshEdge_slot_perp
    [DecidableEq α] [DecidableEq β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (h3 : 3 ≤ cd.d)
    (i : Fin cd.d) (hi : 1 ≤ (i : ℕ)) (s : ℕ) (hs1i : s + 1 < (i : ℕ))
    {ends₀ : β → α × α} {q : α × Fin (k + 2) → ℝ}
    {m : ℕ} (c : Fin m → ℝ) (ev : Fin m → β) (uv vv : Fin m → α)
    (rv : Fin m → Module.Dual ℝ (ScrewSpace k))
    {ρ₀ : Module.Dual ℝ (ScrewSpace k)}
    -- A-1's base edge-grouped redundancy, at the BASE framework `ofNormals (G − v₁) ends₀ q`:
    (hlink : ∀ j, G.IsLink (ev j) (uv j) (vv j))
    (hrv : ∀ j, rv j ∈ (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩))
      ends₀ q).toBodyHinge.hingeRowBlock (ev j))
    (hcomb : (∑ j, c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j))
      = BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ₀)
    (hdeg1 : ∀ j, (cd.vtx ⟨2, by omega⟩ = uv j ∨ cd.vtx ⟨2, by omega⟩ = vv j) →
      ev j = cd.edge ⟨2, by omega⟩)
    -- A-1's splice-panel annihilation `hρe₀` (the `s = 0` base perp at `e₀`):
    (hρe₀ : ρ₀ ((PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩))
      ends₀ q).toBodyHinge.supportExtensor cd.e₀) = 0) :
    ρ₀ ((PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i.castSucc))
        (fun e => ((cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).1,
          (cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).2))
        (fun p => q (cd.shiftPerm i.castSucc p.1, p.2))).toBodyHinge.supportExtensor
          (cd.edge ⟨s, by have := i.isLt; omega⟩)) = 0 := by
  -- STEP 2 carries the base perp at `if s = 0 then e₀ else edge (s+1)` to the candidate.
  refine cd.chainData_freshEdge_perp_transport_base_to_candidate i hi s hs1i
    (Gb := G.removeVertex (cd.vtx ⟨1, by omega⟩)) (ends₀ := ends₀) (q := q) ?_
  -- STEP 1 supplies the base perp: `e₀` at the head (`hρe₀`), `edge (s+1)` interior (`s ≥ 1`).
  rcases Nat.eq_zero_or_pos s with hs0 | hs0
  · subst hs0; rw [if_pos rfl]; exact hρe₀
  · rw [if_neg (by omega : ¬ s = 0)]
    -- STEP 1 (`chainData_freshEdge_perp_of_baseRedundancy`) at base index `⟨1⟩`, edge index `s+1`.
    exact cd.chainData_freshEdge_perp_of_baseRedundancy h3 ⟨1, by omega⟩ (s + 1) (by omega)
      (by have := i.isLt; omega) c ev uv vv rv hlink hrv hcomb hdeg1

/-- **The engine `hρGv` slot at the candidate framework, from A-1's base data** (CHAIN-2c-ii-arm,
the `chainData_relabel_arm` `hρGv` slot; `notes/Phase23-design.md` §(o‴)(I.8.11) STEP 3; KT 2011
§6.4.2 eqs.~(6.56)/(6.64)/(6.66); Phase 23b). The exact `hρGv` slot the arm closer feeds
`case_III_arm_realization` at an interior candidate `i` (`2 ≤ i ≤ d−1`): the fresh-edge candidate
row `hingeRow vᵢ₊₁ vᵢ₋₁ (−ρ₀)` (engine roles `a := vᵢ₊₁`, `b := vᵢ₋₁`, candidate functional `−ρ₀`,
the M₃ sign convention) reaches `span (ofNormals (G − vᵢ) endsσρ qρ).rigidityRows`, where
`qρ`/`endsσρ` are the inverse-cycle relabelled base seed/selector the engine's candidate framework
carries.

The composition (no new math, the arm's hardest slot pre-assembled): `hingeRow_swap` flips the
engine row to `hingeRow vᵢ₋₁ vᵢ₊₁ ρ₀`, which the LEAF-5 slot core `chainData_freshEdge_slot_mem`
produces in `span (ofNormals (G − vᵢ) endsσρ (shiftSeedAdv q (i−1))).rigidityRows`; the P3 seed
bridge `shiftSeedAdv_eq_funLeft_shiftPerm` identifies that fold seed with the engine seed `qρ`. The
slot core's two obligations are discharged from A-1's BASE edge-grouped redundancy (`hlink`/`hrv`/
`hcomb`/`hdeg1` at the base `G − v₁`) + the splice annihilation `hρe₀`: the base redundancy `hφ`
feeds the start fold directly, and every per-edge perp `hperp s` is the LANDED STEP 1∘STEP 2
composition `chainData_freshEdge_slot_perp` (one call per surviving edge `s + 1 < i`). The `d = 3`
`M₃` arm's `case hρGv` (`case_III_arm_realization_M3`, `Relabel.lean`) is the `i = 2` (`m = 1`)
single-summand special case — there the lone surviving row is the reproduced `e_b`-row off `hρe₀`,
which is exactly the `s = 0` branch here (zero-regression). Pure assembly over LANDED leaves; no
motive/IH/contract change, no genuinely-new-math fork. -/
theorem _root_.Graph.ChainData.chainData_relabel_arm_hρGv
    [DecidableEq α] [DecidableEq β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (h3 : 3 ≤ cd.d)
    (i : Fin cd.d) (h2i : 2 ≤ (i : ℕ))
    {ends₀ : β → α × α} {q : α × Fin (k + 2) → ℝ}
    {m : ℕ} (c : Fin m → ℝ) (ev : Fin m → β) (uv vv : Fin m → α)
    (rv : Fin m → Module.Dual ℝ (ScrewSpace k))
    {ρ₀ : Module.Dual ℝ (ScrewSpace k)}
    (hrec : ∀ f x y, G.IsLink f x y →
      (fun e => ((cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).1,
        (cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).2)) f = (x, y) ∨
      (fun e => ((cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).1,
        (cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).2)) f = (y, x))
    -- A-1's base edge-grouped redundancy, at the un-relabelled BASE framework
    -- `ofNormals (G − v₁) ends₀ q` (the STEP 1∘STEP 2 composition's base data):
    (hlink : ∀ j, G.IsLink (ev j) (uv j) (vv j))
    (hrv : ∀ j, rv j ∈ (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩))
      ends₀ q).toBodyHinge.hingeRowBlock (ev j))
    (hcomb : (∑ j, c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j))
      = BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ₀)
    (hdeg1 : ∀ j, (cd.vtx ⟨2, by omega⟩ = uv j ∨ cd.vtx ⟨2, by omega⟩ = vv j) →
      ev j = cd.edge ⟨2, by omega⟩)
    -- A-1's base redundancy as a span membership at the RELABELLED selector `endsσρ`, the fold's
    -- start framework `ofNormals (G − v₁) endsσρ q` the LEAF-5 slot core consumes:
    (hφ : BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ₀ ∈
      Submodule.span ℝ (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩))
        (fun e => ((cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).1,
          (cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).2))
        q).toBodyHinge.rigidityRows)
    -- A-1's splice-panel annihilation `hρe₀` (the `s = 0` base perp at `e₀`), at the un-relabelled
    -- base selector `ends₀` (the composition's STEP 2′ base data):
    (hρe₀ : ρ₀ ((PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩))
      ends₀ q).toBodyHinge.supportExtensor cd.e₀) = 0) :
    BodyHingeFramework.hingeRow (cd.vtx i.succ)
        (cd.vtx (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc) (-ρ₀)
      ∈ Submodule.span ℝ (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i.castSucc))
        (fun e => ((cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).1,
          (cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).2))
        (fun p => q (cd.shiftPerm i.castSucc p.1, p.2))).toBodyHinge.rigidityRows := by
  classical
  -- The relabelled candidate selector `endsσρ` and the engine candidate seed `qρ`.
  set endsσρ : β → α × α :=
    fun e => ((cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).1,
      (cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).2) with hendsσρ
  set qρ : α × Fin (k + 2) → ℝ := fun p => q (cd.shiftPerm i.castSucc p.1, p.2) with hqρ
  -- The `Fin (cd.d + 1)` form of the candidate index `i`.
  have hid : (i : ℕ) < cd.d := i.isLt
  -- `hingeRow_swap` flips the engine row to the slot-core orientation `hingeRow vᵢ₋₁ vᵢ₊₁ ρ₀`.
  rw [BodyHingeFramework.hingeRow_swap (cd.vtx i.succ)
    (cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc) (-ρ₀), neg_neg]
  -- P3: the engine seed `qρ` is the slot core's fold seed `shiftSeedAdv q (i−1)`.
  have hP3 : cd.shiftSeedAdv q ((i : ℕ) - 1) = qρ := by
    rw [hqρ]; exact cd.shiftSeedAdv_eq_funLeft_shiftPerm q i (by omega)
  -- Match the conclusion's vertex indices `vtx (i−1).castSucc`/`vtx i.succ` to the slot core's
  -- `vtx ⟨(i:ℕ)−1, _⟩`/`vtx ⟨(i:ℕ)+1, _⟩` shapes.
  have hidx1 : cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc
      = cd.vtx ⟨(i : ℕ) - 1, by omega⟩ :=
    congrArg cd.vtx (Fin.ext (by simp only [Fin.val_castSucc]))
  have hidx2 : cd.vtx i.succ = cd.vtx ⟨(i : ℕ) + 1, by omega⟩ :=
    congrArg cd.vtx (Fin.ext (by simp only [Fin.val_succ]))
  rw [hidx1, hidx2, ← hP3]
  -- LEAF-5 slot core: peel the slot row off the fold, the base redundancy `hφ` + per-edge perps.
  refine cd.chainData_freshEdge_slot_mem ⟨(i : ℕ), by omega⟩
    (show 1 ≤ (i : ℕ) by omega) (show (i : ℕ) < cd.d from hid) endsσρ q ?hrec ?hφ ?hperp
  case hrec => exact hrec
  case hφ =>
    -- the base redundancy `hingeRow (vtx 0)(vtx 2) ρ₀ ∈ span (G − v₁) rows` (A-1), with the start
    -- fold seed `shiftSeedAdv q 0` reduced to the base seed `q`.
    rw [cd.shiftSeedAdv_zero]; exact hφ
  case hperp =>
    -- each surviving chain-edge perp is the LANDED STEP 1∘STEP 2 composition.
    intro s hs
    rw [hP3]
    exact cd.chainData_freshEdge_slot_perp h3 i (by omega) s hs c ev uv vv rv
      hlink hrv hcomb hdeg1 hρe₀

/-! ## The forked general-`d` Case-III arm realization (Phase 23c, option (A))

The chain-arm closer `case_III_arm_realization_chain`: the general-`d` analogue of the `d = 3` M₃
engine `case_III_arm_realization` (`CaseIII/Arms`), forked off the `±r` block-rank-additivity cert
`case_III_rank_certification_chain` (NO `hρGv`; design §(o‴)(I.8.24)). It is **pure wiring** of two
landed bricks — the cert (for the candidate rank lower bound `hrank`) and the route-agnostic
SHARED rank-to-realization tail `case_III_realization_of_rank` (`CaseIII/Arms`, the W6e–W6f + GAP-2/
GAP-3 part depending only on `hrank`) — over one candidate framework
`F₀ = caseIIICandidate G ends q e_a e_b (q(a,·)) n' (q(b,·)) 0`.

The corner data `(W, hWS, hWcard, ι, hιcard, g, hg, hLI)` of the `±r` block decomposition (KT 2011
§6.4.2 eqs.~(6.64)–(6.66): `W` the relabel-image base block `R(G₁ ∖ row, q₁)`, `g` the `Mᵢ` corner
block with the `±r` row sourced as KT's GENUINE candidate-edge row — design §(o‴)(I.8.24)(4.9)) and
the count facts `(hVone, hVcard)` enter as explicit hypotheses, in the project's standing
"carry the still-undischarged crux as an `h…` hypothesis, never a `sorry`" idiom: the chain dispatch
(CHAIN-2c-iii `chainData_dispatch`, the next sub-step) discharges them from the `ChainData` interior
split — `hWS`/`hWcard` via the carrier leaf
`exists_le_finrank_span_rigidityRows_eq_card_of_injective_map` over the chain bottom family
(`chainData_bottom_relabel`), `hg` via the `±r` GROUP leaf
`funLeft_dualMap_pmR_group_mem_span_caseIIICandidate` + the genuine reproduced-slot row's membership
`hingeRow_mem_caseIIICandidate_rigidityRows_reproduced`, and `hLI` via
`linearIndependent_mkQ_corner_of_gate` with `hrCol` from `reproducedSlot_pmR_acolumn_eq`.

So the arm itself carries no new math — the cert is selector-agnostic (NO `hρGv` slot, the
member-mapping wall is out of it), the `±r` row enters as a member of the corner block `g`, and this
leaf composes the cert with the tail at one framework. At the `d = 3` floor (`i = 2`) the dispatch
stays on the landed `case_III_arm_realization` engine; this chain arm covers the interior
`2 ≤ i < d` of the general-`d` regime. -/
theorem PanelHingeFramework.case_III_arm_realization_chain
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
    (hVone : 1 ≤ V(Gv).ncard) (hVcard : V(G).ncard = V(Gv).ncard + 1)
    {n' : Fin (k + 2) → ℝ}
    (hLn : LinearIndependent ℝ ![(fun i => q (a, i)), n'])
    (hgab : LinearIndependent ℝ ![(fun i => q (a, i)), (fun i => q (b, i))])
    -- The `±r` block decomposition's corner data (the chain dispatch discharges these next):
    {W : Submodule ℝ (Module.Dual ℝ (α → ScrewSpace k))}
    (hWS : W ≤ Submodule.span ℝ
      (PanelHingeFramework.caseIIICandidate G ends q e_a e_b
        (fun i => q (a, i)) n' (fun i => q (b, i)) 0).rigidityRows)
    (hWcard : Module.finrank ℝ W = screwDim k * (V(Gv).ncard - 1))
    {ι : Type*} [Fintype ι] (hιcard : Fintype.card ι = screwDim k)
    {g : ι → Module.Dual ℝ (α → ScrewSpace k)}
    (hg : ∀ j, g j ∈ Submodule.span ℝ
      (PanelHingeFramework.caseIIICandidate G ends q e_a e_b
        (fun i => q (a, i)) n' (fun i => q (b, i)) 0).rigidityRows)
    (hLI : LinearIndependent ℝ (W.mkQ ∘ g))
    {n : ℕ} (hdef : G.deficiency n = 0) :
    PanelHingeFramework.HasGenericFullRankRealization k n G := by
  -- (i) The candidate rank lower bound `hrank` via the `±r` block-rank-additivity cert (NO `hρGv`),
  -- reading off the corner data `(W, g)`.
  have hrank : screwDim k * (V(G).ncard - 1)
      ≤ Module.finrank ℝ (Submodule.span ℝ
        (PanelHingeFramework.caseIIICandidate G ends q e_a e_b
          (fun i => q (a, i)) n' (fun i => q (b, i)) 0).rigidityRows) :=
    PanelHingeFramework.case_III_rank_certification_chain G Gv ends hVone hVcard
      hWS hWcard hιcard hg hLI
  -- (ii) The route-agnostic SHARED rank-to-realization tail closes (W6e–W6f + GAP-2/GAP-3).
  exact PanelHingeFramework.case_III_realization_of_rank G Gv ends hvVc haVc hbVc hG_ea hG_eb
    hends_ea hends_eb heab hleG hsplitG hends_Gv hne_Gv hLn hgab hrank hdef

end CombinatorialRigidity.Molecular
