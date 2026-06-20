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
