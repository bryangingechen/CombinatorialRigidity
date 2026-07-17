/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.AlgebraicInduction.CaseIII.Relabel.ChainColumn

/-!
# The algebraic induction — Case III: the interior-`hρe₀` relabel bridge (Phase 23c)

Phase 22/23 (molecular-conjecture program). Terminal file of the `CaseIII/Relabel/` subdirectory
(the Phase-23c split of `CaseIII/Relabel.lean`, `notes/Phase23c.md`). Carries the interior-`hρe₀`
relabel bridge of the honest geometry arm — the splice-perp crux
`baseRedundancy_perp_interior_reproduced_panel` (KT 2011 eq.~(6.66)) and the cycle-relabel widening
chain (`reproduced_panel_eq_splice_panel`, `interior_hρe₀_of_{splice_perp,widening,baseWidening}`)
that turns the shared base redundancy `ρ₀`'s perp into the interior arm's reproduced-slot `hρe₀`
slot. Consumed by the LIVE router branch `chainData_dispatch_interior` (`CaseIII/Realization`)
feeding the interior arm `chainData_interior_realization_hρGv`. Built on `Relabel/ChainColumn`; this
is the file `CaseIII/Realization` imports for the chain dispatch.

The dead `_aug`/override/(D-substitution) fork that previously lived here (the chain-arm closer
`case_III_arm_realization_chain`, the corner-data assembly, and the `ofNormals` (D-substitution)
tail) was retired in the Phase-23f close (`notes/Phase23-design.md` §(4.106), deletion GROUP 2);
the honest `k`-spine engine carries `d = 3` and the reshaped interior arm carries general `d`.

See `ROADMAP.md` §§22–23 and the `sec:molecular-algebraic-induction-caseIII` dep-graph in
`blueprint/src/chapter/algebraic-induction/case-iii.tex`.
-/

namespace CombinatorialRigidity.Molecular

variable {k : ℕ}

open scoped Graph

variable {α β : Type*}

/-! ## The interior-`hρe₀` relabel bridge (Phase 23c §I.8.24(4.13); KT 2011 eq.~(6.66))

The honest interior arm `chainData_interior_realization_hρGv` (`CaseIII/Realization`) carries, at an
interior matched candidate `i` (`2 ≤ i`), the *reproduced-slot* annihilation
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
    (rv : Fin m → Module.Dual ℝ (ScrewSpace ℝ k))
    {ρ₀ : Module.Dual ℝ (ScrewSpace ℝ k)}
    (hlink : ∀ j, G.IsLink (ev j) (uv j) (vv j))
    -- the base block memberships at the base framework `ofNormals Gw ends q` (graph-irrelevant
    -- for `hingeRowBlock`, which reads only `ends`/`q`; `Gw = G − v₁` is the LEAF-3 widening's)
    {Gw : Graph α β} (ends : β → α × α)
    (hrv : ∀ j, rv j ∈ (PanelHingeFramework.ofNormals Gw ends q).toBodyHinge.hingeRowBlock (ev j))
    -- the `ends`-recording of the matched chain edge `edge i`, in *either* orientation (the
    -- discriminator's IH selector `Q.ends` records each link only up to a free disjunction). The
    -- conclusion `ρ₀ ⊥ panel = 0` is orientation-invariant — the support extensor is antisymmetric
    -- in its two normals, so the swapped recording only flips a sign that `= 0` absorbs.
    (hends_i : ends (cd.edge i) = (cd.vtx i.succ, cd.vtx i.castSucc) ∨
      ends (cd.edge i) = (cd.vtx i.castSucc, cd.vtx i.succ))
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
  -- The two ends `vtx i.succ`, `vtx i.castSucc` are the panel reads `vtx (i+1)`, `vtx i`.
  have hsucc : cd.vtx i.succ = cd.vtx ⟨(i : ℕ) + 1, by have := i.isLt; omega⟩ :=
    congrArg cd.vtx (Fin.ext (by simp only [Fin.val_succ]))
  have hcast : cd.vtx i.castSucc = cd.vtx ⟨(i : ℕ), by have := i.isLt; omega⟩ :=
    congrArg cd.vtx (Fin.ext (by simp only [Fin.val_castSucc]))
  rcases hends_i with hends_i | hends_i
  · rw [PanelHingeFramework.ofNormals_supportExtensor_eq_panel_of_ends Gw (cd.edge i) hends_i]
      at hperp
    rw [hsucc, hcast] at hperp
    exact hperp
  · -- swapped recording: the support extensor is the *negated* panel; `ρ₀(−panel) = 0 ⟹ = 0`.
    rw [PanelHingeFramework.ofNormals_supportExtensor_eq_panel_of_ends Gw (cd.edge i) hends_i,
      panelSupportExtensor_swap, map_neg, neg_eq_zero] at hperp
    rw [hsucc, hcast] at hperp
    exact hperp

/-- **The interior `hρe₀` leaf, produced from the splice-perp crux** (Phase 23c §I.8.24(4.13);
Katoh–Tanigawa 2011 §6.4.2 eq.~(6.66)). The exact `hρe₀` slot the honest interior arm
`chainData_interior_realization_hρGv` consumes at an interior matched candidate `i` (`2 ≤ i`),
produced from the SINGLE crux hypothesis
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
    {ρ₀ : Module.Dual ℝ (ScrewSpace ℝ k)}
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

/-- **The interior `hρe₀` slot, produced end-to-end from the W6b edge-grouped widening bundle**
(`lem:case-III general-d`, the option-(A) LEAF-4 interior-`hρe₀` call site; Phase 23c
§I.8.24(4.13)/(4.16); Katoh–Tanigawa 2011 §6.4.2 eq.~(6.66)). The chain dispatch's (CHAIN-2c-iii)
interior branch `chainData_dispatch_interior` feeds the honest interior arm the `hρe₀` slot
`ρ₀ ⊥ panelSupportExtensor (qρ(a,·)) (qρ(b,·))` at the matched interior candidate `i` (`2 ≤ i < d`),
read at candidate `i`'s relabelled seed `qρ = q ∘ shiftPerm i.castSucc` (KT eq.~(6.56)). This leaf
produces exactly that slot from the **single** input the W6b producer already computes — the
edge-grouped `G_v`-row form of the shared redundancy `hingeRow (vtx 0) (vtx 2) ρ₀ =
∑ⱼ cⱼ • hingeRow (uvⱼ)(vvⱼ)(rvⱼ)` (KT eq.~(6.52)/(6.66), the `hedgeGv` bundle re-anchored to the
spliced edge `e₀ = v₀v₂`'s endpoints `(vtx 0, vtx 2)`) — composing the two landed leaves with no
intermediate `hsplice` threading:

* `baseRedundancy_perp_interior_reproduced_panel` (THE conjecture-crux, framework-free) carries the
  base redundancy across `vᵢ` to the spliced chain edge `edge i`: `ρ₀ ⊥` the base-seed panel
  `panelSupportExtensor (q(vtx (i+1),·)) (q(vtx i,·))`;
* `interior_hρe₀_of_splice_perp` (the cycle-relabel bridge `reproduced_panel_eq_splice_panel`)
  rewrites that base-seed splice panel into the consumer's relabelled `qρ`-panel.

So the dispatch threads the widening bundle ONCE and gets the assembly's `hρe₀` directly. NO `hρGv`,
no new linear algebra — pure composition of the crux with the relabel bridge. -/
theorem _root_.Graph.ChainData.interior_hρe₀_of_widening
    [DecidableEq α]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (h3 : 3 ≤ cd.d)
    (i : Fin cd.d) (h2i : 2 ≤ (i : ℕ))
    {q : α × Fin (k + 2) → ℝ}
    {m : ℕ} (c : Fin m → ℝ) (ev : Fin m → β) (uv vv : Fin m → α)
    (rv : Fin m → Module.Dual ℝ (ScrewSpace ℝ k))
    {ρ₀ : Module.Dual ℝ (ScrewSpace ℝ k)}
    (hlink : ∀ j, G.IsLink (ev j) (uv j) (vv j))
    {Gw : Graph α β} (ends : β → α × α)
    (hrv : ∀ j, rv j ∈ (PanelHingeFramework.ofNormals Gw ends q).toBodyHinge.hingeRowBlock (ev j))
    (hends_i : ends (cd.edge i) = (cd.vtx i.succ, cd.vtx i.castSucc) ∨
      ends (cd.edge i) = (cd.vtx i.castSucc, cd.vtx i.succ))
    (hcomb : (∑ j, c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j))
      = BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ₀)
    (hdeg1 : ∀ j, (cd.vtx ⟨2, by omega⟩ = uv j ∨ cd.vtx ⟨2, by omega⟩ = vv j) →
      ev j = cd.edge ⟨2, by omega⟩) :
    ρ₀ (panelSupportExtensor
          (fun j => (fun p => q (cd.shiftPerm i.castSucc p.1, p.2)) (cd.vtx i.succ, j))
          (fun j => (fun p => q (cd.shiftPerm i.castSucc p.1, p.2))
            (cd.vtx (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc, j))) = 0 :=
  cd.interior_hρe₀_of_splice_perp i h2i
    (cd.baseRedundancy_perp_interior_reproduced_panel h3 i h2i c ev uv vv rv hlink ends hrv
      hends_i hcomb hdeg1)

/-- **The interior `hρe₀` slot, produced directly from LEAF-3's base-`v₁`-split widening bundle**
(`lem:case-III general-d`, the option-(A) LEAF-4 interior-`hρe₀` call site, the dispatch's bundle
re-anchoring; Phase 23d; Katoh–Tanigawa 2011 §6.4.2 eq.~(6.66)). The chain dispatch (CHAIN-2c-iii)
fires LEAF-3 (`exists_shared_redundancy_and_matched_candidate`) at the **base `v₁`-split**
`(v, a, b) = (vtx 1, vtx 0, vtx 2)`, which re-exposes the W6b **edge-grouped `G_v`-row widening**
of the shared redundancy `hingeRow (vtx 0) (vtx 2) ρ₀` (the `hedgeGv` bundle: an explicit per-edge
`hingeRow` combination over `Gv = G − vtx 1`'s links). This leaf folds that bundle, in its native
LEAF-3 shape, straight into `interior_hρe₀_of_widening` — the only re-anchoring it needs is

* the per-summand `G − vtx 1`-link `hlinkGv` is a *`G`*-link (`removeVertex_le` /
  `removeVertex_isLink`);
* the bundle's `hcombGv : hingeRow (vtx 0) (vtx 2) ρ₀ = ∑ⱼ cⱼ • hingeRow (uⱼ)(vⱼ)(rⱼ)` is the
  consumer's `hcomb` flipped (`.symm`); and
* the degree-1-at-anchor closure `hdeg1` — a summand incident to the anchor `vtx 2` must use the
  chain edge `edge 2`: the summand is a `G − vtx 1`-link, hence a `G`-edge at `vtx 2`, so by the
  interior degree-2 closure (`deg_two` at `vtx 2`, valid since `3 ≤ d`) it is `edge 1` or `edge 2` —
  but `edge 1` is incident to `vtx 1` (the `link` field at index 1), so it is *not* a
  `G − vtx 1`-link, leaving `edge 2`.

So the dispatch threads LEAF-3's `hedgeGv` bundle and `hends_i` (the `ends`-recording of the matched
chain edge `edge i`) and reads off the consumer's `hρe₀` directly. NO `hρGv`, no new linear
algebra — pure re-anchoring of the landed crux (`interior_hρe₀_of_widening`) to the bundle shape. -/
theorem _root_.Graph.ChainData.interior_hρe₀_of_baseWidening
    [DecidableEq α]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (h3 : 3 ≤ cd.d)
    (i : Fin cd.d) (h2i : 2 ≤ (i : ℕ))
    {q : α × Fin (k + 2) → ℝ} (ends : β → α × α)
    {ρ₀ : Module.Dual ℝ (ScrewSpace ℝ k)}
    (hends_i : ends (cd.edge i) = (cd.vtx i.succ, cd.vtx i.castSucc) ∨
      ends (cd.edge i) = (cd.vtx i.castSucc, cd.vtx i.succ))
    -- LEAF-3's W6b edge-grouped `G_v`-row widening bundle at the base `v₁`-split `(a,b) = (v₀,v₂)`:
    (hedgeGv :
      ∃ (nGv : ℕ) (cGv : Fin nGv → ℝ) (evGv : Fin nGv → β) (uvGv vvGv : Fin nGv → α)
          (rvGv : Fin nGv → Module.Dual ℝ (ScrewSpace ℝ k)),
        (∀ j, (G.removeVertex (cd.vtx ⟨1, by omega⟩)).IsLink (evGv j) (uvGv j) (vvGv j)) ∧
        (∀ j, rvGv j ∈ (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩))
          ends q).toBodyHinge.hingeRowBlock (evGv j)) ∧
        BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ₀
          = ∑ j, cGv j • BodyHingeFramework.hingeRow (uvGv j) (vvGv j) (rvGv j)) :
    ρ₀ (panelSupportExtensor
          (fun j => (fun p => q (cd.shiftPerm i.castSucc p.1, p.2)) (cd.vtx i.succ, j))
          (fun j => (fun p => q (cd.shiftPerm i.castSucc p.1, p.2))
            (cd.vtx (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc, j))) = 0 := by
  obtain ⟨nGv, cGv, evGv, uvGv, vvGv, rvGv, hlinkGv, hrvGv, hcombGv⟩ := hedgeGv
  -- `edge 1` links `vtx 1` to `vtx 2` (the `link` field at index 1), so it is incident to `vtx 1`.
  have hlink_one : G.IsLink (cd.edge ⟨1, by omega⟩) (cd.vtx ⟨1, by omega⟩)
      (cd.vtx ⟨2, by omega⟩) := by
    have h := cd.link ⟨1, by omega⟩
    rwa [show (⟨1, by omega⟩ : Fin cd.d).castSucc = (⟨1, by omega⟩ : Fin (cd.d + 1)) from
        Fin.ext rfl,
      show (⟨1, by omega⟩ : Fin cd.d).succ = (⟨2, by omega⟩ : Fin (cd.d + 1)) from Fin.ext rfl] at h
  refine cd.interior_hρe₀_of_widening h3 i h2i cGv evGv uvGv vvGv rvGv
    (fun j => ((Graph.removeVertex_isLink.mp (hlinkGv j)).1)) ends hrvGv hends_i hcombGv.symm
    (fun j hj => ?_)
  -- The summand `evGv j` is incident to the anchor `vtx 2` in `G − vtx 1`, hence a `G`-edge there.
  obtain ⟨hGlink, hu1, hv1⟩ := Graph.removeVertex_isLink.mp (hlinkGv j)
  have hanchor : G.IsLink (evGv j) (cd.vtx ⟨2, by omega⟩) (vvGv j) ∨
      G.IsLink (evGv j) (uvGv j) (cd.vtx ⟨2, by omega⟩) := by
    rcases hj with h | h
    · exact Or.inl (h ▸ hGlink)
    · exact Or.inr (h ▸ hGlink)
  -- `deg_two` at the interior vertex `vtx 2` (`0 < 2`, valid since `3 ≤ d`): `edge 1` or `edge 2`.
  have hdt := cd.deg_two ⟨2, by omega⟩ (show 0 < (2 : ℕ) by omega)
  have hcl : evGv j = cd.edge ⟨1, by omega⟩ ∨
      evGv j = cd.edge ⟨2, by omega⟩ := by
    rcases hanchor with h | h
    · simpa using hdt (evGv j) (vvGv j)
        (by rw [show (⟨2, by omega⟩ : Fin cd.d).castSucc = (⟨2, by omega⟩ : Fin (cd.d + 1)) from
          Fin.ext rfl]; exact h)
    · simpa using hdt (evGv j) (uvGv j)
        (by rw [show (⟨2, by omega⟩ : Fin cd.d).castSucc = (⟨2, by omega⟩ : Fin (cd.d + 1)) from
          Fin.ext rfl]; exact h.symm)
  -- `evGv j ≠ edge 1`: else the `G − vtx 1`-link uses the `vtx 1`-incident edge `edge 1`,
  -- but `removeVertex_isLink` forbids `vtx 1` as an endpoint.
  rcases hcl with h | h
  · exfalso
    have := hlink_one.eq_and_eq_or_eq_and_eq (h ▸ hGlink)
    rcases this with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hu1 h1.symm
    · exact hv1 h1.symm
  · exact h

end CombinatorialRigidity.Molecular
