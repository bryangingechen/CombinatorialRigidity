/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.AlgebraicInduction.CaseIII.Relabel.ChainColumn

/-!
# The algebraic induction — Case III: the forked general-`d` arm realization (Phase 23c, option (A))

Phase 22/23 (molecular-conjecture program). Terminal file of the `CaseIII/Relabel/` subdirectory
(the
Phase-23c split of `CaseIII/Relabel.lean`, `notes/Phase23c.md`). The forked general-`d` Case-III
chain-arm closer `case_III_arm_realization_chain` (pure cert→tail wiring off the `±r`
block-rank-additivity cert, NO `hρGv`; design §(o‴)(I.8.24)) and the corner-data ASSEMBLY producer
`case_III_arm_corner_assembly` (the option-(A) seam-resolution integration). Built on
`Relabel/ChainColumn`; this is the file `CaseIII/Realization` imports for the chain dispatch.

See `ROADMAP.md` §§22–23 and the `sec:molecular-algebraic-induction-caseIII` dep-graph in
`blueprint/src/chapter/algebraic-induction/case-iii.tex`.
-/

namespace CombinatorialRigidity.Molecular

variable {k : ℕ}

open scoped Graph

variable {α β : Type*}

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

/-! ### The interior-`hρe₀` relabel bridge (Phase 23c §I.8.24(4.13); KT 2011 eq.~(6.66))

The chain arm's corner-assembly `case_III_arm_corner_assembly` carries, at an interior matched
candidate `i` (`2 ≤ i`), the *reproduced-slot* annihilation
`hρe₀ : ρ₀ ⊥ panelSupportExtensor (qρ(a,·)) (qρ(b,·))` with `a = vtx i.succ`,
`b = vtx (i−1).castSucc` the two chain neighbours of the degree-2 split body `v = vtx i.castSucc`,
in candidate `i`'s relabelled seed `qρ = q ∘ shiftPerm i.castSucc` (KT eq.~(6.56)). These lemmas
DISSOLVE the prior Route-A-vs-Route-B routing question into a single splice-perp crux: the
`(a,b)` reproduced panel is, *under the cycle relabel*, the base-seed chain panel of the spliced
edge `edge i` (`vᵢ`-incident, the KT eq.~(6.66) splice). So the leaf reduces to the one
genuinely-new obligation `ρ₀ ⊥ (base-seed `edge i` splice panel)` (the un-landed
`baseRedundancy_perp_interior_reproduced_panel`, KT eq.~(6.66)'s redundancy carry across the
spliced body), and everything else is this pure-`shiftPerm`-algebra rewrite.

The seam was mis-pinned 3–4× by design prose; these lemmas are the compiler-checked replacement for
that adjudication (the original spike, Phase 23c §I.8.24(4.13)). -/

/-- **The reproduced-slot panel is the base-seed splice-edge panel, under the cycle relabel**
(Phase 23c §I.8.24(4.13); Katoh–Tanigawa 2011 §6.4.2 eq.~(6.56) the candidate seed `qᵢ = q ∘ ρᵢ`,
eq.~(6.66) the spliced panel). At an interior candidate `i` (`2 ≤ i`) the consumer's reproduced
panel `panelSupportExtensor (qρ(vtx i.succ,·)) (qρ(vtx (i−1).castSucc,·))`, read at candidate `i`'s
relabelled seed `qρ = q ∘ shiftPerm i.castSucc`, equals the BASE-seed panel of the spliced chain
edge `edge i` — namely `panelSupportExtensor (q(vtx (i+1),·)) (q(vtx i,·))`. The two seed reads
cancel the cycle shift:

* `a = vtx i.succ` has index `i+1 > i`, *off* the cycle `[vtx 1, …, vtx i]`, so
  `shiftPerm i.castSucc` fixes it (`shiftPerm_apply_vtx_off`): `qρ(a,·) = q(vtx (i+1),·)`;
* `b = vtx (i−1).castSucc` has index `1 ≤ i−1 < i`, *interior* to the cycle, so
  `shiftPerm i.castSucc` sends it to its chain-successor `vtx i` (`shiftPerm_apply_interior`):
  `qρ(b,·) = q(vtx i,·)`.

This is the cycle generalization of the `d = 3` `M₃` arm's single-swap seed-coincidence
(`Relabel/Arm.lean`, `case_III_arm_realization_M3`'s `hqρv`/`hqρc`). Pure `shiftPerm`/`vtx`
algebra. -/
theorem _root_.Graph.ChainData.reproduced_panel_eq_splice_panel
    [DecidableEq α]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (i : Fin cd.d) (h2i : 2 ≤ (i : ℕ))
    {q : α × Fin (k + 2) → ℝ} :
    panelSupportExtensor
        (fun j => (fun p => q (cd.shiftPerm i.castSucc p.1, p.2)) (cd.vtx i.succ, j))
        (fun j => (fun p => q (cd.shiftPerm i.castSucc p.1, p.2))
          (cd.vtx (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc, j))
      = panelSupportExtensor (fun j => q (cd.vtx ⟨(i : ℕ) + 1, by have := i.isLt; omega⟩, j))
          (fun j => q (cd.vtx ⟨(i : ℕ), by have := i.isLt; omega⟩, j)) := by
  have hicast : (i.castSucc : Fin (cd.d + 1)) = ⟨(i : ℕ), by have := i.isLt; omega⟩ :=
    Fin.ext (by simp only [Fin.val_castSucc])
  -- `qρ(a,·) = q(vtx (i+1),·)`: `a = vtx i.succ`, index `i+1 > i`, OFF the cycle.
  have ha : (fun j => q (cd.shiftPerm i.castSucc (cd.vtx i.succ), j))
      = fun j => q (cd.vtx ⟨(i : ℕ) + 1, by have := i.isLt; omega⟩, j) := by
    have hsucc : cd.vtx i.succ = cd.vtx ⟨(i : ℕ) + 1, by have := i.isLt; omega⟩ :=
      congrArg cd.vtx (Fin.ext (by simp only [Fin.val_succ]))
    rw [hsucc, hicast, cd.shiftPerm_apply_vtx_off ⟨(i : ℕ), by have := i.isLt; omega⟩
      (by have := i.isLt; omega) (Or.inr (by simp only; omega))]
  -- `qρ(b,·) = q(vtx i,·)`: `b = vtx (i−1)`, index `1 ≤ i−1 < i`, INTERIOR → successor `vtx i`.
  have hb : (fun j => q (cd.shiftPerm i.castSucc
        (cd.vtx (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc), j))
      = fun j => q (cd.vtx ⟨(i : ℕ), by have := i.isLt; omega⟩, j) := by
    have hcs : (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc
        = (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin (cd.d + 1)) :=
      Fin.ext (by simp only [Fin.val_castSucc])
    have hb1 : 1 ≤ (i : ℕ) - 1 := by omega
    have hb2 : (i : ℕ) - 1 < (i : ℕ) := by omega
    rw [hcs, hicast, cd.shiftPerm_apply_interior ⟨(i : ℕ), by have := i.isLt; omega⟩
      (j := (i : ℕ) - 1) hb1 hb2]
    have hval : ((i : ℕ) - 1) + 1 = (i : ℕ) := by omega
    have : (⟨((i : ℕ) - 1) + 1, by have := i.isLt; omega⟩ : Fin (cd.d + 1))
        = ⟨(i : ℕ), by have := i.isLt; omega⟩ := Fin.ext hval
    rw [this]
  rw [show (fun j => (fun p => q (cd.shiftPerm i.castSucc p.1, p.2)) (cd.vtx i.succ, j))
        = (fun j => q (cd.shiftPerm i.castSucc (cd.vtx i.succ), j)) from rfl, ha,
     show (fun j => (fun p => q (cd.shiftPerm i.castSucc p.1, p.2))
          (cd.vtx (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc, j))
        = (fun j => q (cd.shiftPerm i.castSucc
          (cd.vtx (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc), j)) from rfl, hb]

/-- **The interior `hρe₀` leaf, reduced to the splice-perp crux** (Phase 23c §I.8.24(4.13);
Katoh–Tanigawa 2011 §6.4.2 eq.~(6.66)). The exact `hρe₀` slot `case_III_arm_corner_assembly`
consumes at an interior matched candidate `i` (`2 ≤ i`), produced from the SINGLE crux hypothesis
`hsplice : ρ₀ ⊥ (base-seed `edge i` splice panel)` by the cycle-relabel bridge
`reproduced_panel_eq_splice_panel`. Carrying `hsplice` as an explicit hypothesis is the project's
standing no-`sorry` idiom: this leaf is *otherwise complete*, so the whole interior-`hρe₀` leaf
reduces to discharging `hsplice` — the genuinely-new `baseRedundancy_perp_interior_reproduced_panel`
(the KT eq.~(6.66) redundancy carry across the spliced body `vᵢ`, the next focused commit).

This DISSOLVES the prior Route-A-vs-Route-B fork: BOTH routes reduce to `hsplice`. Route A
(`chainData_freshEdge_perp_of_baseRedundancy`) supplies the *surviving*-edge perps (`2 ≤ s`,
`s+1 < i`) that feed the eq.~(6.66) carry as INPUTS — they are not themselves `hsplice` (the spliced
`edge i` is `vᵢ`-incident, never a surviving edge). -/
theorem _root_.Graph.ChainData.interior_hρe₀_of_splice_perp
    [DecidableEq α]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (i : Fin cd.d) (h2i : 2 ≤ (i : ℕ))
    {q : α × Fin (k + 2) → ℝ}
    {ρ₀ : Module.Dual ℝ (ScrewSpace k)}
    -- the splice-perp crux: ρ₀ ⊥ the base-seed panel of the spliced chain edge `edge i`
    -- (`vᵢ`-incident); the genuinely-new `baseRedundancy_perp_interior_reproduced_panel`:
    (hsplice : ρ₀ (panelSupportExtensor
        (fun j => q (cd.vtx ⟨(i : ℕ) + 1, by have := i.isLt; omega⟩, j))
        (fun j => q (cd.vtx ⟨(i : ℕ), by have := i.isLt; omega⟩, j))) = 0) :
    -- the consumer's `hρe₀` at candidate `i`'s relabelled seed `qρ = q ∘ shiftPerm i.castSucc`:
    ρ₀ (panelSupportExtensor
          (fun j => (fun p => q (cd.shiftPerm i.castSucc p.1, p.2)) (cd.vtx i.succ, j))
          (fun j => (fun p => q (cd.shiftPerm i.castSucc p.1, p.2))
            (cd.vtx (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc, j))) = 0 := by
  rw [cd.reproduced_panel_eq_splice_panel i h2i]
  exact hsplice

/-- **The base-seed panel is the `ofNormals` framework's support extensor at a recording edge**
(Phase 23c §I.8.24(4.13)). The projection bridge between Route A's literal output shape
`ρ₀ ⊥ Fva.supportExtensor f` and the base-seed `panelSupportExtensor` shape the splice-perp crux
`hsplice` is stated in: at the seed framework `Fva = ofNormals (G − vᵢ) endsσρ qρ`, an edge `f`
recording `endsσρ f = (x, y)` has `Fva.supportExtensor f = panelSupportExtensor (qρ(x,·)) (qρ(y,·))`
— a pure unfold of `toBodyHinge_supportExtensor` / `ofNormals_{normal,ends}`. Lets the eq.~(6.66)
carry's surviving-edge perp inputs (Route A) be read in the `panelSupportExtensor` form the bridge
and the crux speak. -/
theorem PanelHingeFramework.ofNormals_supportExtensor_eq_panel_of_ends
    (Gv : Graph α β) {endsσρ : β → α × α} {qρ : α × Fin (k + 2) → ℝ}
    (f : β) {x y : α} (hf : endsσρ f = (x, y)) :
    (PanelHingeFramework.ofNormals Gv endsσρ qρ).toBodyHinge.supportExtensor f
      = panelSupportExtensor (fun j => qρ (x, j)) (fun j => qρ (y, j)) := by
  rw [PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_normal,
    PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_ends, hf]

/-- **The chain arm's corner-data ASSEMBLY producer** (`lem:case-III general-d`, the option-(A)
seam-resolution integration: assemble the `±r` block decomposition's `Mᵢ` corner block `g` from the
landed sourcing leaves and feed it to the chain-arm spine `case_III_arm_realization_chain`, Phase
23c §I.8.24(4.9); Katoh–Tanigawa 2011 §6.4.2 eqs.~(6.64)–(6.66)). Where
`case_III_arm_realization_chain`
carries the corner block `(g, hg, hLI)` as *opaque* hypotheses (the cert→tail spine), this producer
*constructs* it at the candidate framework `F₀ = caseIIICandidate G ends q e_a e_b (q(a,·)) n'
(q(b,·)) 0`, taking the dispatch's RAW outputs as hypotheses, and is the **end-to-end check that the
corrected `±r` leaf actually feeds the cert's `hg` and the corrected `hrCol` feeds `hLI`** — the one
integration the seam's 4× mis-pin history warrants isolating before the dispatch's production
complexity.

The corner block is `g = Sum.elim (D − 1 fresh-hinge panel rows) (±r row)` over `ι = ↥s ⊕ Unit`
(`Fintype.card = (D − 1) + 1 = D`):

* the **`D − 1` panel rows** of the candidate's fresh hinge `e_a` (first endpoint `v`, the
  re-inserted body) — extracted by `exists_independent_panelRow_subfamily_of_edge` at `e_a` from
  `F₀.supportExtensor e_a = panelSupportExtensor (q(a,·)) n' ≠ 0` (`hsupp` + `hgate`). Each is a
  candidate rigidity row (`panelRow_mem_rigidityRows_of_link` at the direct `G`-link `e_a = va`,
  `hG_ea`), giving the panel-rows half of `hg`; and

* the **`±r` row** `rRow = hingeRow b v ρ₀`, the genuine reproduced-slot `e_b`-row oriented with the
  re-inserted body `v` as head. Its `hg` membership is
  `hingeRow_mem_caseIIICandidate_rigidityRows_reproduced` (`hlink = hG_eb.symm`, `hperp = hρe₀` at
  the reproduced slot's support `panelSupportExtensor (q(a,·) + 0·n') (q(b,·))`, `t = 0`); its `hLI`
  discriminator column at `single v` is `−ρ₀` (`reproducedSlot_pmR_acolumn_eq`, `b ≠ v`).

`hLI` is then `linearIndependent_mkQ_corner_of_gate` at `F₀`, `e = e_a`, `vᵢ = v`: the panel rows
are independent mod `W` (block-triangular off-`v` vanishing `hW`) and the `±r` class is outside
their span (the discriminator `hgate` at the FIXED `ρ₀`). The `W`-corner inputs (`W, hWS, hWcard,
hW`) are
the spine's own shape, supplied as-is by the dispatch (the carrier leaf
`exists_le_finrank_span_rigidityRows_eq_card_of_injective_map` over the chain bottom family + the
relabel-image off-`v` vanishing); this producer assembles only the `Mᵢ` corner the seam lives in.
NO `hρGv`, no new math — pure assembly of landed leaves into the spine's corner slots. -/
theorem PanelHingeFramework.case_III_arm_corner_assembly
    [Finite α] [Finite β] [DecidableEq α] [DecidableEq β]
    (G Gv : Graph α β) (ends : β → α × α) {q : α × Fin (k + 2) → ℝ}
    {v a b : α} {e_a e_b : β}
    (hvVc : v ∉ V(Gv)) (haVc : a ∈ V(Gv)) (hbVc : b ∈ V(Gv))
    (hG_ea : G.IsLink e_a v a) (hG_eb : G.IsLink e_b v b)
    (hends_ea : ends e_a = (v, a)) (hends_eb : ends e_b = (v, b)) (heab : e_a ≠ e_b)
    (hva : v ≠ a) (hvb : v ≠ b)
    (hleG : ∀ e u w, Gv.IsLink e u w → G.IsLink e u w)
    (hsplitG : ∀ e u w, G.IsLink e u w → e = e_a ∨ e = e_b ∨ Gv.IsLink e u w)
    (hends_Gv : ∀ e u w, Gv.IsLink e u w → Gv.IsLink e (ends e).1 (ends e).2)
    (hne_Gv : ∀ e, Gv.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.supportExtensor e ≠ 0)
    (hVone : 1 ≤ V(Gv).ncard) (hVcard : V(G).ncard = V(Gv).ncard + 1)
    {n' : Fin (k + 2) → ℝ}
    (hLn : LinearIndependent ℝ ![(fun i => q (a, i)), n'])
    (hgab : LinearIndependent ℝ ![(fun i => q (a, i)), (fun i => q (b, i))])
    -- The dispatch's RAW discriminator outputs (at the FIXED redundancy `ρ₀ = KT's abstract `r`):
    {ρ₀ : Module.Dual ℝ (ScrewSpace k)}
    (hgate : ρ₀ (panelSupportExtensor (fun i => q (a, i)) n') ≠ 0)
    (hρe₀ : ρ₀ (panelSupportExtensor (fun i => q (a, i)) (fun i => q (b, i))) = 0)
    -- The base block `W` (the dispatch supplies it from the chain bottom family via the carrier
    -- leaf + the relabel-image off-`v` vanishing):
    {W : Submodule ℝ (Module.Dual ℝ (α → ScrewSpace k))}
    (hWS : W ≤ Submodule.span ℝ
      (PanelHingeFramework.caseIIICandidate G ends q e_a e_b
        (fun i => q (a, i)) n' (fun i => q (b, i)) 0).rigidityRows)
    (hWcard : Module.finrank ℝ W = screwDim k * (V(Gv).ncard - 1))
    (hW : ∀ φ ∈ W, φ.comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v) = 0)
    {n : ℕ} (hdef : G.deficiency n = 0) :
    PanelHingeFramework.HasGenericFullRankRealization k n G := by
  classical
  set F₀ := PanelHingeFramework.caseIIICandidate G ends q e_a e_b
    (fun i => q (a, i)) n' (fun i => q (b, i)) 0 with hF₀
  -- The candidate fresh hinge `e_a` (the `e_c` slot): its support is the `va`-line meet
  -- `panelSupportExtensor (q(a,·)) n'`, nonzero by the discriminator `hgate`.
  have hsupp : F₀.supportExtensor e_a = panelSupportExtensor (fun i => q (a, i)) n' :=
    PanelHingeFramework.caseIIICandidate_supportExtensor_candidate G ends q
      (fun i => q (a, i)) n' (fun i => q (b, i)) 0 heab
  have hane : F₀.supportExtensor e_a ≠ 0 := by
    rw [hsupp]; intro h; rw [h, map_zero] at hgate; exact hgate rfl
  have huv : (ends e_a).1 ≠ (ends e_a).2 := by rw [hends_ea]; exact hva
  have h1v : (ends e_a).1 = v := by rw [hends_ea]
  -- The `D − 1` fresh-hinge panel rows (all on `e_a`, independent), with `Nat.card s = D − 1`.
  obtain ⟨s, hs_e, hs_card, hs_indep⟩ :=
    F₀.exists_independent_panelRow_subfamily_of_edge (ends := ends) (e := e_a) huv hane
  haveI : Finite ↥s := hs_indep.finite
  haveI : Fintype ↥s := Fintype.ofFinite ↥s
  -- The `±r` corner row: the genuine reproduced-slot `e_b`-row, head `v`.
  set rRow := BodyHingeFramework.hingeRow b v ρ₀ with hrRow
  -- (hg) Each corner member is a candidate rigidity row.
  have hg : ∀ j : ↥s ⊕ Unit,
      (Sum.elim (fun i : ↥s => F₀.panelRow ends (i : β × _ × _)) (fun _ : Unit => rRow)) j
        ∈ Submodule.span ℝ F₀.rigidityRows := by
    rintro (⟨i, hi⟩ | _)
    · -- panel rows: a candidate rigidity row at the direct `G`-link `e_a = va`.
      refine Submodule.subset_span ?_
      have hie : (i : β × _ × _).1 = e_a := hs_e i hi
      obtain ⟨e', t₁, t₂⟩ := (i : β × _ × _)
      simp only at hie; subst hie
      exact F₀.panelRow_mem_rigidityRows_of_link ends (u := v) (w := a) hends_ea
        (by rw [hF₀, PanelHingeFramework.caseIIICandidate_graph]; exact hG_ea) t₁ t₂
    · -- the `±r` row: the genuine reproduced-slot `e_b`-row (`hperp = hρe₀`, NEVER `hρGv`).
      rw [hrRow]
      exact PanelHingeFramework.hingeRow_mem_caseIIICandidate_rigidityRows_reproduced G ends q
        e_a e_b (fun i => q (a, i)) n' (fun i => q (b, i)) 0 hG_eb.symm
        (by rw [zero_smul, add_zero]; exact hρe₀)
  -- (hLI) The corner block is independent mod `W` (panel rows mod `W` + the `±r` discriminator).
  have hLI : LinearIndependent ℝ (W.mkQ ∘
      Sum.elim (fun i : ↥s => F₀.panelRow ends (i : β × _ × _)) (fun _ : Unit => rRow)) := by
    rw [hrRow]
    exact F₀.linearIndependent_mkQ_corner_of_gate (e := e_a) (vᵢ := v) h1v huv.symm
      hsupp hgate hs_e hs_indep hW
      (PanelHingeFramework.reproducedSlot_pmR_acolumn_eq hvb.symm ρ₀)
  -- The corner index count `|↥s ⊕ Unit| = (D − 1) + 1 = D`.
  have hιcard : Fintype.card (↥s ⊕ Unit) = screwDim k := by
    rw [Fintype.card_sum, Fintype.card_unit, ← Nat.card_eq_fintype_card, hs_card]
    have hD : 1 ≤ screwDim k := Nat.choose_pos (by omega)
    omega
  -- Feed the assembled corner data to the chain-arm spine.
  exact PanelHingeFramework.case_III_arm_realization_chain G Gv ends hvVc haVc hbVc hG_ea hG_eb
    hends_ea hends_eb heab hleG hsplitG hends_Gv hne_Gv hVone hVcard hLn hgab
    hWS hWcard hιcard hg hLI hdef

end CombinatorialRigidity.Molecular
