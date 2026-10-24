/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.AlgebraicInduction.CaseIII.Relabel.ChainColumn

/-!
# Case III: the form `r` on the hinge of the new edge of `G_i`

Lemmas for Case III of KT Theorem 5.5 (Katoh and Tanigawa 2011, *A proof of the molecular
conjecture*, Discrete Comput. Geom. **45**, §6.4), presented in
`sec:molecular-algebraic-induction-caseIII`. For a chain `v₀ ⋯ v_d` with `d ≥ 3`, `2 ≤ i ≤ d − 1`,
`σ_i = shiftPerm i.castSucc` and `q_i = q ∘ σ_i`, the file proves the first claim of
`lem:case-III-chain-eq666` (KT eq. (6.66), p. 698): if `hingeRow v₀ v₂ ρ₀` is a combination of rows
of `ofNormals (G − v₁) ends q`, then `ρ₀` vanishes on the hinge `C(q_i(v_{i+1}), q_i(v_{i−1}))` of
the new edge `v_{i−1} v_{i+1}` of `(G_i, q_i)` (`interior_hρe₀_of_baseWidening`).

`CaseIII/Relabel/ChainColumn.lean` proves the second claim, and `CaseIII/Realization.lean`, which
imports this file, applies both in the proof of `lem:case-III-chain-dispatch`.
-/

@[expose] public section

namespace CombinatorialRigidity.Molecular

variable {k : ℕ}

open scoped Graph

variable {α β : Type*}

variable {K : Type*} [Field K]

/-! ## The hinge of the new edge of `G_i`

The hinge `C(q_i(v_{i+1}), q_i(v_{i−1}))` of the new edge of `G_i` is `C(q(v_{i+1}), q(v_i))`, up to
sign the hinge of the edge `v_i v_{i+1}` of `(G_1, q)` (`reproduced_panel_eq_splice_panel`; KT
eq. (6.56), p. 694). Write `hingeRow v₀ v₂ ρ₀` as a combination of rows. Its terms at the edge
`v_i v_{i+1}`, restricted to `v_i`, sum to `−ρ₀` (`interior_group_acolumn_eq_neg_baseRedundancy`,
`CaseIII/Relabel/ChainColumn.lean`), a form in the block of rows of that edge, so `ρ₀` vanishes on
its hinge (`baseRedundancy_perp_interior_reproduced_panel`). -/

/-- **The hinge of the new edge of `G_i`** (a step of `lem:case-III-chain-eq666`; KT eq. (6.56),
p. 694): for `2 ≤ i ≤ d − 1`, `σ_i = shiftPerm i.castSucc` and the normals `q_i = q ∘ σ_i`
(`fun p => q (σ_i p.1, p.2)`), the extensor `C(q_i(v_{i+1}), q_i(v_{i−1}))` is
`C(q(v_{i+1}), q(v_i))`. The cycle `σ_i` maps `v₁ ↦ v₂ ↦ ⋯ ↦ v_i ↦ v₁`, so it fixes `v_{i+1}`
(`shiftPerm_apply_vtx_off`) and maps `v_{i−1}` to `v_i`, as `1 ≤ i − 1 < i`
(`shiftPerm_apply_interior`). -/
theorem _root_.Graph.ChainData.reproduced_panel_eq_splice_panel
    [DecidableEq α]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (i : Fin cd.d) (h2i : 2 ≤ (i : ℕ))
    {q : α × Fin (k + 2) → K} :
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

/-- **`ρ₀` vanishes on the hinge of the edge `v_i v_{i+1}`** (a step of `lem:case-III-chain-eq666`;
KT eq. (6.66), p. 698): let `d ≥ 3` and `2 ≤ i ≤ d − 1`, and let
`∑ c_j hingeRow (uv j) (vv j) (rv j)` be `hingeRow v₀ v₂ ρ₀` (`hcomb`), where each `ev j` joins
`uv j` and `vv j` in `G` (`hlink`), each `rv j` lies in the block of rows of `ofNormals Gw ends q`
at `ev j` (`hrv`), and every term at `v₂` is at the edge `v₂v₃` (`hdeg1`). If `ends` gives the edge
`v_i v_{i+1}` its ends in some order (`hends_i`), then `ρ₀` vanishes on `C(q(v_{i+1}), q(v_i))`.

The terms at `v_i v_{i+1}`, restricted to `v_i`, sum to `−ρ₀`
(`interior_group_acolumn_eq_neg_baseRedundancy`), a form in the block of rows of
`ofNormals Gw ends q` at `v_i v_{i+1}` (`edgeGroup_acolumn_mem_block`). So `ρ₀` vanishes on the
hinge there, which is `±C(q(v_{i+1}), q(v_i))` by `hends_i`. The block reads only the hinge, which
`ofNormals` gives from the selector and the normals and not from the graph, so `Gw` is any graph;
the caller takes `G − v₁`. -/
theorem _root_.Graph.ChainData.baseRedundancy_perp_interior_reproduced_panel
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (h3 : 3 ≤ cd.d)
    (i : Fin cd.d) (h2i : 2 ≤ (i : ℕ))
    {q : α × Fin (k + 2) → K}
    {m : ℕ} (c : Fin m → K) (ev : Fin m → β) (uv vv : Fin m → α)
    (rv : Fin m → Module.Dual K (ScrewSpace K k))
    {ρ₀ : Module.Dual K (ScrewSpace K k)}
    (hlink : ∀ j, G.IsLink (ev j) (uv j) (vv j))
    -- each `rv j` in the block of rows of `ofNormals Gw ends q` at `ev j` (a block reads only
    -- `ends` and `q`, not the graph; the caller takes `Gw = G − v₁`):
    {Gw : Graph α β} (ends : β → α × α)
    (hrv : ∀ j, rv j ∈ (PanelHingeFramework.ofNormals Gw ends q).toBodyHinge.hingeRowBlock (ev j))
    -- `ends` gives the edge `v_i v_{i+1}` its ends in some order. Swapping the two normals changes
    -- the sign of the extensor, which does not change whether `ρ₀` vanishes on it.
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
  -- The terms at `edge i`, restricted to `vtx i`, sum to `−ρ₀`.
  have hcolval := cd.interior_group_acolumn_eq_neg_baseRedundancy h3 c ev uv vv rv hlink hcomb
    hdeg1 (i : ℕ) h2i i.isLt
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
  -- `Fbase.supportExtensor (edge i)` is the extensor of the normals at the ends that `ends` gives.
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

/-- **From the hinge of `v_i v_{i+1}` to that of the new edge of `G_i`** (a step of
`lem:case-III-chain-eq666`): for `2 ≤ i ≤ d − 1`, if `ρ₀` vanishes on `C(q(v_{i+1}), q(v_i))`
(`hsplice`), it vanishes on `C(q_i(v_{i+1}), q_i(v_{i−1}))` for `q_i = q ∘ shiftPerm i.castSucc`, as
the two extensors are equal (`reproduced_panel_eq_splice_panel`). -/
theorem _root_.Graph.ChainData.interior_hρe₀_of_splice_perp
    [DecidableEq α]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (i : Fin cd.d) (h2i : 2 ≤ (i : ℕ))
    {q : α × Fin (k + 2) → K}
    {ρ₀ : Module.Dual K (ScrewSpace K k)}
    -- `ρ₀` vanishes on `C(q(v_{i+1}), q(v_i))`:
    (hsplice : ρ₀ (panelSupportExtensor
        (fun j => q (cd.vtx ⟨(i : ℕ) + 1, by have := i.isLt; omega⟩, j))
        (fun j => q (cd.vtx ⟨(i : ℕ), by have := i.isLt; omega⟩, j))) = 0) :
    -- then on `C(q_i(v_{i+1}), q_i(v_{i−1}))`, for the normals `q_i = q ∘ shiftPerm i.castSucc`:
    ρ₀ (panelSupportExtensor
          (fun j => (fun p => q (cd.shiftPerm i.castSucc p.1, p.2)) (cd.vtx i.succ, j))
          (fun j => (fun p => q (cd.shiftPerm i.castSucc p.1, p.2))
            (cd.vtx (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc, j))) = 0 := by
  rw [cd.reproduced_panel_eq_splice_panel i h2i]
  exact hsplice

/-- **`ρ₀` vanishes on the hinge of the new edge of `G_i`, from a combination at links of `G`** (a
step of `lem:case-III-chain-eq666`): under the hypotheses of
`baseRedundancy_perp_interior_reproduced_panel`, `ρ₀` vanishes on `C(q_i(v_{i+1}), q_i(v_{i−1}))`
for `q_i = q ∘ shiftPerm i.castSucc`: that lemma, then `interior_hρe₀_of_splice_perp`. -/
theorem _root_.Graph.ChainData.interior_hρe₀_of_widening
    [DecidableEq α]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (h3 : 3 ≤ cd.d)
    (i : Fin cd.d) (h2i : 2 ≤ (i : ℕ))
    {q : α × Fin (k + 2) → K}
    {m : ℕ} (c : Fin m → K) (ev : Fin m → β) (uv vv : Fin m → α)
    (rv : Fin m → Module.Dual K (ScrewSpace K k))
    {ρ₀ : Module.Dual K (ScrewSpace K k)}
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

/-- **`ρ₀` vanishes on the hinge of the new edge of `G_i`** (`lem:case-III-chain-eq666`, the first
claim; KT eq. (6.66), p. 698): let `d ≥ 3`, `2 ≤ i ≤ d − 1`, `σ_i = shiftPerm i.castSucc` and
`q_i = q ∘ σ_i`, let `ends` give the edge `v_i v_{i+1}` its ends in some order (`hends_i`), and let
`hingeRow v₀ v₂ ρ₀` be a combination `∑ c_j hingeRow (uv j) (vv j) (rv j)` in which each `rv j` lies
in the block of rows of `ofNormals (G − v₁) ends q` at a link `ev j` of `G − v₁` with ends `uv j`
and `vv j` (`hedgeGv`). Then `ρ₀` vanishes on `C(q_i(v_{i+1}), q_i(v_{i−1}))`, the hinge of the new
edge `v_{i−1} v_{i+1}` of `(G_i, q_i)`.

The proof is `interior_hρe₀_of_widening`, whose hypothesis on the terms at `v₂` holds: a link of
`G − v₁` at `v₂` is an edge of `G` at the interior vertex `v₂`, so it is `v₁v₂` or `v₂v₃`
(`ChainData.deg_two`), and it is not `v₁v₂`, which meets `v₁`. `chainData_dispatch_interior`
(`CaseIII/Realization.lean`) applies it to the combination that `chainData_fire_discriminator`
gives. -/
theorem _root_.Graph.ChainData.interior_hρe₀_of_baseWidening
    [DecidableEq α]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (h3 : 3 ≤ cd.d)
    (i : Fin cd.d) (h2i : 2 ≤ (i : ℕ))
    {q : α × Fin (k + 2) → K} (ends : β → α × α)
    {ρ₀ : Module.Dual K (ScrewSpace K k)}
    (hends_i : ends (cd.edge i) = (cd.vtx i.succ, cd.vtx i.castSucc) ∨
      ends (cd.edge i) = (cd.vtx i.castSucc, cd.vtx i.succ))
    -- `hingeRow v₀ v₂ ρ₀` as a combination of rows of `ofNormals (G − v₁) ends q`:
    (hedgeGv :
      ∃ (nGv : ℕ) (cGv : Fin nGv → K) (evGv : Fin nGv → β) (uvGv vvGv : Fin nGv → α)
          (rvGv : Fin nGv → Module.Dual K (ScrewSpace K k)),
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
  -- `edge 1` links `vtx 1` to `vtx 2` (`splitOff_data_one`), so it is incident to `vtx 1`.
  obtain ⟨-, -, -, -, -, hlink_one, -⟩ := cd.splitOff_data_one (by omega)
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
