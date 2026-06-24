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

/-- **The splice-perp crux — the eq.~(6.66) redundancy carry to the spliced candidate edge**
(Phase 23c §I.8.24(4.13)/(4.16), THE conjecture-crux leaf; Katoh–Tanigawa 2011 §6.4.2 eq.~(6.66)).
The genuinely-new content of the interior-`hρe₀` leaf: the shared redundancy `ρ₀` annihilates the
base-seed panel of the spliced chain edge `edge i` — `panelSupportExtensor (q(vtx (i+1),·))
(q(vtx i,·))` — at an interior matched candidate `i` (`2 ≤ i < d`). This is exactly the `hsplice`
hypothesis `interior_hρe₀_of_splice_perp` (below) consumes; the cycle-relabel bridge then turns it
into the consumer's `hρe₀` slot.

**The carry "across `vᵢ`" needs no new argument — the LANDED value-read does it directly.** The seam
was mis-pinned 3–4× (the wall-vs-escape conflation) precisely because the spliced `edge i` is
`vᵢ`-incident, hence *not* an edge of `G − vᵢ`, so the surviving-edge perp leaf
`chainData_freshEdge_perp_of_baseRedundancy` (which lives in the `G − vᵢ` framework) excludes it.
But the target panel is read off the *base seed* `q` directly, not off any framework, and its block
test `hingeRowBlock` depends only on `ends`/`q` — the graph is irrelevant (`hingeRowBlock e =
(span {supportExtensor e})ᗮ`, and `ofNormals`' `supportExtensor` reads only `ends`/`q`). So the two
LANDED bricks that produced the surviving-edge perps work verbatim at the spliced edge `edge i`:

* `interior_group_acolumn_eq_neg_baseRedundancy` (the chain-induction LEAF 4, **framework-free**) —
  the `edge i`-group's screw column at its tail body `vtx i` is the constant `−ρ₀`, carried along
  the chain from the base redundancy `hcomb` and anchored at `vtx 2`. This holds for *every*
  `2 ≤ i < d`, the candidate edge included (it never invokes a framework or the deletion `G − vᵢ`).
* `edgeGroup_acolumn_mem_block` (the column-in-block core) — that same `edge i`-group column lies in
  `(ofNormals Gw ends q).hingeRowBlock (edge i)` for the base framework `Gw` (here `Gw = G − v₁`,
  what the LEAF-3 widening supplies; the graph is immaterial to the block).

Combining, `−ρ₀ ∈ block (edge i)`, so `ρ₀ ∈ block` (negation-closed), so `ρ₀ ⊥ supportExtensor
(edge i) = panelSupportExtensor (q(vtx (i+1),·)) (q(vtx i,·))` (`ofNormals_supportExtensor_eq_panel_
of_ends`, given the `ends`-recording `hends_i`). No per-vertex eq.~(6.52) witness production, no
inductive chain over `s`, no Grassmann–Cayley meet: the eq.~(6.66) carry IS the framework-free value
read, applied one index deeper than the surviving-edge leaf dared.

The carried inputs — the base redundancy `hcomb` (= the LEAF-3 widening's edge-grouped `G_v`-row
form, KT eq.~(6.66)), the per-summand `G`-links `hlink` + base-framework block memberships `hrv`
(the widening's `evGv`/`rvGv` data), the `ends`-recording `hends_i` at the spliced edge, and the
degree-1-at-anchor closure `hdeg1` — are the LEAF-3 base bundle + widening outputs the dispatch
threads in (LEAF-4 step (ii)); they are *not* a deferred crux. -/
theorem _root_.Graph.ChainData.baseRedundancy_perp_interior_reproduced_panel
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (h3 : 3 ≤ cd.d)
    (i : Fin cd.d) (h2i : 2 ≤ (i : ℕ))
    {q : α × Fin (k + 2) → ℝ}
    {m : ℕ} (c : Fin m → ℝ) (ev : Fin m → β) (uv vv : Fin m → α)
    (rv : Fin m → Module.Dual ℝ (ScrewSpace k))
    {ρ₀ : Module.Dual ℝ (ScrewSpace k)}
    (hlink : ∀ j, G.IsLink (ev j) (uv j) (vv j))
    -- the base block memberships at the base framework `ofNormals Gw ends q` (graph-irrelevant
    -- for `hingeRowBlock`, which reads only `ends`/`q`; `Gw = G − v₁` is the LEAF-3 widening's)
    {Gw : Graph α β} (ends : β → α × α)
    (hrv : ∀ j, rv j ∈ (PanelHingeFramework.ofNormals Gw ends q).toBodyHinge.hingeRowBlock (ev j))
    (hends_i : ends (cd.edge i) = (cd.vtx i.succ, cd.vtx i.castSucc))
    (hcomb : (∑ j, c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j))
      = BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ₀)
    (hdeg1 : ∀ j, (cd.vtx ⟨2, by omega⟩ = uv j ∨ cd.vtx ⟨2, by omega⟩ = vv j) →
      ev j = cd.edge ⟨2, by omega⟩) :
    ρ₀ (panelSupportExtensor (fun j => q (cd.vtx ⟨(i : ℕ) + 1, by have := i.isLt; omega⟩, j))
        (fun j => q (cd.vtx ⟨(i : ℕ), by have := i.isLt; omega⟩, j))) = 0 := by
  classical
  set Fbase := (PanelHingeFramework.ofNormals Gw ends q).toBodyHinge with hFbase
  -- The `edge i`-group's `vtx i`-column is `−ρ₀` (chain induction LEAF 4, framework-free).
  have hcolval := cd.interior_group_acolumn_eq_neg_baseRedundancy h3 c ev uv vv rv hlink hcomb
    rfl rfl hdeg1 (i : ℕ) h2i i.isLt
  -- The `edge i`-group's `vtx i`-column lands in `Fbase.hingeRowBlock (edge i)`.
  have hmem := Fbase.edgeGroup_acolumn_mem_block (e := cd.edge ⟨(i : ℕ), by have := i.isLt; omega⟩)
    (p := cd.vtx ⟨(i : ℕ), by have := i.isLt; omega⟩) c ev uv vv rv hrv
  rw [hcolval] at hmem
  -- `−ρ₀ ∈ block ⟹ ρ₀ ∈ block ⟹ ρ₀ ⊥ Fbase.supportExtensor (edge i)`.
  have hρ₀mem : ρ₀ ∈ Fbase.hingeRowBlock (cd.edge ⟨(i : ℕ), by have := i.isLt; omega⟩) := by
    have := (Fbase.hingeRowBlock (cd.edge ⟨(i : ℕ), by have := i.isLt; omega⟩)).neg_mem hmem
    rwa [neg_neg] at this
  have hperp := (Fbase.mem_hingeRowBlock_iff (cd.edge ⟨(i : ℕ), by have := i.isLt; omega⟩) ρ₀).1
    hρ₀mem
  -- Rewrite `Fbase.supportExtensor (edge i)` to the base-seed panel via the `ends`-recording.
  have hieq : (⟨(i : ℕ), by have := i.isLt; omega⟩ : Fin cd.d) = i := Fin.ext rfl
  rw [hieq] at hperp
  rw [PanelHingeFramework.ofNormals_supportExtensor_eq_panel_of_ends Gw (cd.edge i) hends_i]
    at hperp
  -- The two ends `vtx i.succ`, `vtx i.castSucc` are the panel reads `vtx (i+1)`, `vtx i`.
  have hsucc : cd.vtx i.succ = cd.vtx ⟨(i : ℕ) + 1, by have := i.isLt; omega⟩ :=
    congrArg cd.vtx (Fin.ext (by simp only [Fin.val_succ]))
  have hcast : cd.vtx i.castSucc = cd.vtx ⟨(i : ℕ), by have := i.isLt; omega⟩ :=
    congrArg cd.vtx (Fin.ext (by simp only [Fin.val_castSucc]))
  rw [hsucc, hcast] at hperp
  exact hperp

/-- **The interior `hρe₀` leaf, produced from the splice-perp crux** (Phase 23c §I.8.24(4.13);
Katoh–Tanigawa 2011 §6.4.2 eq.~(6.66)). The exact `hρe₀` slot `case_III_arm_corner_assembly`
consumes at an interior matched candidate `i` (`2 ≤ i`), produced from the SINGLE crux hypothesis
`hsplice : ρ₀ ⊥ (base-seed `edge i` splice panel)` by the cycle-relabel bridge
`reproduced_panel_eq_splice_panel`. With the crux `baseRedundancy_perp_interior_reproduced_panel`
(above) now LANDED, `hsplice` is no longer a deferred obligation — the whole interior-`hρe₀` leaf is
complete modulo the dispatch threading the crux's carried inputs (LEAF-4 step (ii)). This wrapper is
kept in the carry-as-`h…` form so the dispatch can either supply `hsplice` from the crux directly or
re-derive it inline.

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

/-! ### The base block `W`'s per-member `hS` router (Phase 23c §I.8.24(4.10) LEAF-4 step (ii))

The base block `W` of the `±r` block decomposition (`case_III_arm_corner_assembly`'s
`hWS`/`hWcard`/`hW`) is built by `BodyHingeFramework.span_relabelImage_le_and_finrank_and_acolumn_
vanish` (LEAF-2) from the base-split W6b bottom family `w` relabelled along
`L = (funLeft (shiftPerm i.castSucc)⁻¹).dualMap` — the cycle relabel `chainData_bottom_relabel`
realizes. LEAF-2's `hS` slot needs each relabel image `L (w j)` IN the candidate's rigidity-row span
`span (caseIIICandidate (G − vᵢ) (candidateEnds …) (candidateSeed …) e_a e_b …).rigidityRows`.

`chainData_bottom_relabel` produces, for each `w j`, a disjunction over the *seed* framework
`ofNormals (G − vᵢ) endsσρ qρ`: either a genuine rigidity row of it, or a reproduced-slot block tag
`hingeRow (vtx i.succ) (vtx (i−1).castSucc) ρ'` with `ρ'` annihilating the candidate fresh pair's
panel. This leaf is the per-member router carrying *that* disjunction into the candidate span:

* the **genuine seed row** `hingeRow x y r` (`r ∈ (ofNormals (G − vᵢ) endsσρ qρ).hingeRowBlock e`
  at a surviving link `(G − vᵢ).IsLink e x y`) is an off-slot candidate-edge row — its edge `e`
  survives `removeVertex vᵢ`, so it is `vᵢ`-incidence-free, hence distinct from the two
  `vᵢ`-incident candidate slots `e_a`, `e_b` — and routes through the off-slot bridge
  `hingeRow_mem_caseIIICandidate_rigidityRows_of_ofNormals_link` (the candidate keeps the seed
  extensor off `{e_a, e_b}`, `caseIIICandidate_supportExtensor_of_ne`), giving
  `Submodule.subset_span`;
* the **reproduced-slot block tag** `hingeRow (vtx i.succ) (vtx (i−1).castSucc) ρ'` routes through
  `hingeRow_mem_caseIIICandidate_rigidityRows_reproduced` at `e_b`'s genuine candidate link
  `(vtx i.succ, vtx (i−1).castSucc) = (a, b)` (`hG_eb_cand`), with `hperp = hρ'` at the reproduced
  slot's support `panelSupportExtensor (q(a,·) + 0 • n') (q(b,·))` (`t = 0`).

The `vᵢ`-incidence of `e_a`, `e_b` and the candidate `e_b`-link are supplied by the dispatch
(LEAF-5) from the interior split tuple. NO `hρGv`, no new linear algebra — the per-member
case-split feeding LEAF-2 (`notes/Phase23-design.md` §I.8.24(4.10) LEAF-4 (c)). -/
theorem _root_.Graph.ChainData.bottomRelabel_image_mem_span_caseIIICandidate
    [DecidableEq β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (i : Fin cd.d)
    {endsσρ : β → α × α} {qρ : α × Fin (k + 2) → ℝ}
    {e_a e_b : β} {n' : Fin (k + 2) → ℝ}
    -- the candidate's reproduced hinge `e_b` carries the genuine `(a, b)` link
    (hG_eb_cand : G.IsLink e_b (cd.vtx i.succ)
      (cd.vtx (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc))
    -- the off-slot conditions on the two `vᵢ`-incident candidate slots (dispatch-supplied)
    (heab_off : ∀ e x y, (G.removeVertex (cd.vtx i.castSucc)).IsLink e x y → e ≠ e_a ∧ e ≠ e_b)
    {φ : Module.Dual ℝ (α → ScrewSpace k)}
    (hφ : φ ∈ (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i.castSucc))
        endsσρ qρ).toBodyHinge.rigidityRows ∨
      ∃ ρ' : Module.Dual ℝ (ScrewSpace k),
        ρ' (panelSupportExtensor
            (fun j => qρ (cd.vtx i.succ, j))
            (fun j =>
              qρ (cd.vtx (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc, j)))
          = 0 ∧
        φ = BodyHingeFramework.hingeRow (cd.vtx i.succ)
            (cd.vtx (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc) ρ') :
    φ ∈ Submodule.span ℝ
      (PanelHingeFramework.caseIIICandidate G endsσρ qρ e_a e_b
        (fun j => qρ (cd.vtx i.succ, j)) n'
        (fun j => qρ (cd.vtx (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc, j))
        0).rigidityRows := by
  classical
  set a := cd.vtx i.succ with ha
  set b := cd.vtx (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc with hb
  rcases hφ with hgen | ⟨ρ', hρ', rfl⟩
  · -- Genuine seed row at an off-slot surviving candidate link.
    obtain ⟨e, x, y, hlink, r, hr, rfl⟩ := hgen
    rw [PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph] at hlink
    obtain ⟨hea, heb⟩ := heab_off e x y hlink
    refine Submodule.subset_span ?_
    refine PanelHingeFramework.hingeRow_mem_caseIIICandidate_rigidityRows_of_ofNormals_link
      G endsσρ qρ e_a e_b (fun j => qρ (a, j)) n' (fun j => qρ (b, j)) 0 hea heb
      ((Graph.removeVertex_isLink.mp hlink).1) ?_
    -- transport the block membership across the graph (`ofNormals` support is graph-independent)
    rw [BodyHingeFramework.mem_hingeRowBlock_iff,
      PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_normal,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_ends]
    have hr' := (BodyHingeFramework.mem_hingeRowBlock_iff _ e r).1 hr
    rw [PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_normal,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_ends] at hr'
    exact hr'
  · -- Reproduced-slot block tag at `e_b`'s genuine candidate link `(a, b)`.
    exact PanelHingeFramework.hingeRow_mem_caseIIICandidate_rigidityRows_reproduced G endsσρ qρ
      e_a e_b (fun j => qρ (a, j)) n' (fun j => qρ (b, j)) 0 hG_eb_cand
      (by rw [zero_smul, add_zero]; exact hρ')

/-- **The base block `W`'s universal per-member `hS` router, end-to-end into the candidate span**
(`lem:case-III general-d`, the option-(A) LEAF-4 step (ii) `hS`-router half; Phase 23c
§I.8.24(4.10)/(4.25); Katoh–Tanigawa 2011 §6.4.2 eqs.~(6.54)/(6.62)/(6.64)). The route-B
genuine-only `W` producer `exists_genuine_relabelImage_base_block` (LEAF-B2, `CaseIII/Candidate`)
takes its per-genuine-row transport `hS` **universally over the base framework's rigidity rows** —
for the chain dispatch's base framework `Fbase = (ofNormals (G − vtx 1) ends₀ q).toBodyHinge`, every
rigidity row
`φ` must transport under the cycle relabel `(funLeft (shiftPerm i.castSucc).symm).dualMap` into the
candidate's rigidity-row span. This leaf supplies exactly that universal fact, composing the two
landed routing bricks:

* `chainData_bottom_relabel` (`CaseIII/Relabel/Chain`) sends a genuine base row (the `Or.inl` arm —
  here the *only* arm, since `φ ∈ Fbase.rigidityRows` is fed as `Or.inl hφ`, never the base
  `(vtx 2, vtx 0)`-block tag) to the candidate-`i` seed disjunction over
  `ofNormals (G − vtx i.castSucc) endsσρ qρ` — *either* a genuine seed rigidity row *or* the
  reproduced-slot block tag `hingeRow (vtx i.succ) (vtx (i−1).castSucc) ρ'`; then
* `bottomRelabel_image_mem_span_caseIIICandidate` (above) carries that disjunction into the
  candidate
  `caseIIICandidate G endsσρ qρ e_a e_b (qρ(vtx i.succ,·)) n' (qρ(vtx (i−1).castSucc,·)) 0`'s
  rigidity-row span — the genuine seed row via the off-slot bridge
  `hingeRow_mem_caseIIICandidate_rigidityRows_of_ofNormals_link`, the block tag via the genuine
  reproduced-slot row `hingeRow_mem_caseIIICandidate_rigidityRows_reproduced` at `e_b`'s candidate
  link.

**This resolves the route-B LEAF-4 residual risk** (coordinator-flagged): every genuine base row
transports through the cert-SOUND genuine branch — `chainData_bottom_relabel`'s `Or.inl` input never
forces the §(4.17)-dead `hG_eb_cand`/block-tag-via-reproduced path to carry a *genuine* base row
(that path only fires on the candidate's own reproduced slot, supplied by `hG_eb_cand` at the
genuine `(a, b)` candidate link, not on a base-row image). NO `hρGv`, no new linear algebra — pure
composition of the two landed bricks over `Or.inl`. The hypotheses (`hrec`/`he₀rec` for the first
brick, `hG_eb_cand`/`heab_off` for the second) are exactly the dispatch's interior-split data; the
chain dispatch (CHAIN-2c-iii) threads them in and feeds this universal `hS` to LEAF-B2. -/
theorem _root_.Graph.ChainData.bottomRelabel_rigidityRows_mem_span_caseIIICandidate
    [DecidableEq α] [DecidableEq β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (i : Fin cd.d) (hi : 1 < (i : ℕ))
    {ends₀ : β → α × α} {q : α × Fin (k + 2) → ℝ}
    {e_a e_b : β} {n' : Fin (k + 2) → ℝ}
    (hrec : ∀ e x y, (G.removeVertex
          (cd.vtx (⟨1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc)).IsLink e x y →
      ends₀ e = (x, y) ∨ ends₀ e = (y, x))
    (he₀rec : ends₀ cd.e₀ =
      (cd.vtx (⟨2, by have := i.isLt; omega⟩ : Fin cd.d).castSucc,
        cd.vtx (⟨0, by have := i.isLt; omega⟩ : Fin cd.d).castSucc))
    (hG_eb_cand : G.IsLink e_b (cd.vtx i.succ)
      (cd.vtx (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc))
    (heab_off : ∀ e x y, (G.removeVertex (cd.vtx i.castSucc)).IsLink e x y → e ≠ e_a ∧ e ≠ e_b)
    {φ : Module.Dual ℝ (α → ScrewSpace k)}
    (hφ : φ ∈ (PanelHingeFramework.ofNormals
        (G.removeVertex (cd.vtx (⟨1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc))
        ends₀ q).toBodyHinge.rigidityRows) :
    (LinearMap.funLeft ℝ (ScrewSpace k) (cd.shiftPerm i.castSucc).symm).dualMap φ ∈
      Submodule.span ℝ
        (PanelHingeFramework.caseIIICandidate G
          (fun e => ((cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).1,
            (cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).2))
          (fun p => q (cd.shiftPerm i.castSucc p.1, p.2)) e_a e_b
          (fun j => (fun p => q (cd.shiftPerm i.castSucc p.1, p.2)) (cd.vtx i.succ, j)) n'
          (fun j => (fun p => q (cd.shiftPerm i.castSucc p.1, p.2))
            (cd.vtx (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc, j))
          0).rigidityRows :=
  cd.bottomRelabel_image_mem_span_caseIIICandidate i (e_a := e_a) (n' := n') hG_eb_cand heab_off
    (PanelHingeFramework.chainData_bottom_relabel cd i hi hrec he₀rec (Or.inl hφ))

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

/-- **The chain arm's corner-data assembly, with the base block `W` produced by LEAF-B2**
(`lem:case-III general-d`, the route-B LEAF-4 `case_III_arm_corner_assembly` call; Katoh–Tanigawa
2011 §6.4.2 eq.~(6.64), the genuine-only bottom block `R(G₁ ∖ (v₀v₂)ᵢ∗, q₁)`; design §I.8.24(4.25)).
This is the producer the hand-off names as "the rest of LEAF-4 wiring": it folds the base-block
`W`-production into `case_III_arm_corner_assembly`, replacing that theorem's *opaque*
`(W, hWS, hWcard, hW)` block with the route-B LEAF-B2 inputs and constructing `W` internally.

Where `case_III_arm_corner_assembly` carries `W` as a hypothesis (the dispatch was to supply
it), this producer builds it via `exists_genuine_relabelImage_base_block` (LEAF-B2) at the GENUINE
basis of the base framework `Fbase`'s rigidity-row span (the redundant member `rhat` excluded — KT's
`R(G₁ ∖ (v₀v₂)ᵢ∗, q₁)`, escaping the member-mapping wall), transported into the candidate `F₀`'s
rigidity-row span. LEAF-B2's universal per-genuine-row transport `hS` and off-`σ.symm v` vanishing
`hvanish` enter here as hypotheses over **every** base rigidity row; the chain dispatch
(CHAIN-2c-iii) discharges them from the two landed universal lemmas at the cycle relabel
`σ = (shiftPerm i.castSucc)⁻¹` — `hS` from
`Graph.ChainData.bottomRelabel_rigidityRows_mem_span_caseIIICandidate` and `hvanish` from
`PanelHingeFramework.ofNormals_removeVertex_rigidityRow_comp_single_self` at `σ.symm v = vtx 1`. The
card bookkeeping `finrank W = D·(|V(Gv)| − 1)` is LEAF-B2's: the genuine basis has card the full
base rank `D·(|V(Gv)| − 1)` (the IH `hIH`), since deleting the redundant `rhat ∈ span (others)`
(`hrhat`, KT eq.~(6.24)) preserves the span. NO `hρGv`, no new linear algebra — pure composition
of LEAF-B2 with `case_III_arm_corner_assembly`. The candidate framework LEAF-B2 lands `W` in is
the *same* `F₀ = caseIIICandidate G ends q e_a e_b (q(a,·)) n' (q(b,·)) 0` the assembly consumes,
so no
relabel-form alignment is needed at this layer (the dispatch threads the `endsσρ`/`qρ` form when it
discharges `hS`/`hvanish`). -/
theorem PanelHingeFramework.case_III_arm_corner_assembly_via_leafB2
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
    {ρ₀ : Module.Dual ℝ (ScrewSpace k)}
    (hgate : ρ₀ (panelSupportExtensor (fun i => q (a, i)) n') ≠ 0)
    (hρe₀ : ρ₀ (panelSupportExtensor (fun i => q (a, i)) (fun i => q (b, i))) = 0)
    -- The route-B LEAF-B2 inputs (replacing the opaque `(W, hWS, hWcard, hW)` block): a base
    -- framework `Fbase` with a redundant row `rhat` in the span of the others (KT eq. (6.24)), the
    -- IH base rank, the cycle relabel `σ`, and the per-genuine-row transport/vanishing universally.
    (Fbase : BodyHingeFramework k α β) {σ : Equiv.Perm α}
    {rhat : Module.Dual ℝ (α → ScrewSpace k)}
    (hrhat : rhat ∈ Submodule.span ℝ (Fbase.rigidityRows \ {rhat}))
    (hIH : Module.finrank ℝ (Submodule.span ℝ Fbase.rigidityRows)
      = screwDim k * (V(Gv).ncard - 1))
    (hS : ∀ φ ∈ Fbase.rigidityRows,
      (LinearMap.funLeft ℝ (ScrewSpace k) σ).dualMap φ ∈ Submodule.span ℝ
        (PanelHingeFramework.caseIIICandidate G ends q e_a e_b
          (fun i => q (a, i)) n' (fun i => q (b, i)) 0).rigidityRows)
    (hvanish : ∀ φ ∈ Fbase.rigidityRows,
      φ.comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) (σ.symm v)) = 0)
    {n : ℕ} (hdef : G.deficiency n = 0) :
    PanelHingeFramework.HasGenericFullRankRealization k n G := by
  -- LEAF-B2: the genuine-only base block `W` in the candidate's rigidity-row span, of the full base
  -- rank `D·(|V(Gv)| − 1)`, annihilating the re-inserted body `v`'s screw column.
  obtain ⟨W, hWS, hWcard, hW⟩ :=
    Fbase.exists_genuine_relabelImage_base_block
      (PanelHingeFramework.caseIIICandidate G ends q e_a e_b
        (fun i => q (a, i)) n' (fun i => q (b, i)) 0)
      (v := v) (σ := σ) hrhat hIH hS hvanish
  -- Feed the LEAF-B2 `W` into the corner-data assembly.
  exact PanelHingeFramework.case_III_arm_corner_assembly G Gv ends hvVc haVc hbVc hG_ea hG_eb
    hends_ea hends_eb heab hva hvb hleG hsplitG hends_Gv hne_Gv hVone hVcard hLn hgab
    hgate hρe₀ hWS hWcard hW hdef

end CombinatorialRigidity.Molecular
