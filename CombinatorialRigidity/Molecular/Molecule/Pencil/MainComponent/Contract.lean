/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.ContractCurve

/-!
# Contraction at a `def₂`-rigid core in the `X₀` induction (Phase 40f CONTRACT-R)

The flat-core assembly of the contraction step of the `X₀` induction, at a core of planar
deficiency zero (`blueprint/src/chapter/main-component.tex`, `sec:main-component-contract`;
informal (MC-59)(d) with (MC-39), after Katoh–Tanigawa 2011 §6.2, Lemma 6.3). Let `W ⊊ V(G)` with
`|W| ≥ 2` induce a core `H = G[W]` with `def₂(H) = 0`, let `r ∈ W`, and let
`G/H = G.rigidContract (G.induce W) r` be simple (no body outside `W` adjacent to two core
bodies). If `X₀(G/H)` attains, so does `X₀(G)`. The step keeps the contract of `Cut.lean` (one
picture `q` generic for the pieces and main for `G`, ending at `Graph.x0Attains_of_exists`), but
the picture moves: along the curve `q(t)`, on which the core shrinks towards `r`'s picture point
(`q(1) = q`), the heights are the solutions of a rescaled lifting system `M(t)`
(`ContractCurve.lean`) whose kernel does not jump at `t = 0`, and the rank is read through the
block-triangular shape of KT eq. (6.3).

The rescaled lifting system, the curve, and the facts at the two ends of `t = 0`/`t = 1` that this
step and the Phase 40k CONTRACT-A step share are in `ContractCurve.lean` (split out at the Phase
40k `Contract.lean` split, `notes/Phase40k.md`, call 5): no declaration here is renamed or
re-stated, so no blueprint `\lean{...}` pin moved.

## Main statements

* `Graph.exists_core_plane` — at a core with `L_H(q) ⊆ Aff(q)`, a solution of `M(t)` has one plane
  on the whole core, at every `t` (`lem:pencil-contract-core-plane`).
* `Graph.finrank_ker_contractLiftingMatrix_zero_le` — at a flat core, `dim ker M(0) ≤ dim
  L_{G/H}(q)`, through the injective limit map given the core's one plane
  (`lem:pencil-contract-limit` (1); (MC-59)(c2)'s upper bound).
* `Graph.finrank_span_rigidityRows_induce_contractHeight` — the core has rank `6(|W| − 1)` at the
  curve's configuration (`lem:pencil-contract-core-rank`).
* `Graph.isX0Graph_induce_of_deficiency_two_eq_zero` — a `def₂`-rigid core satisfies the standing
  hypotheses (`lem:pencil-contract-standing`).
* `Graph.X0Attains.of_rigidContract` — **CONTRACT-R** (`thm:pencil-x0-contract-rigid`).

The general pieces sit beside their definitions: `Graph.connected_of_isKDof_zero`
(`Molecular/Deficiency.lean`) and the block coupling
`PanelHingeFramework.finrank_span_rigidityRows_induce_add_map_extProj_le` (`Coupling.lean`,
`lem:block-rank-contract`).

## Design

* **One parameter, one product polynomial.** Unlike `Cut.lean`'s steps the picture moves, so
  `MvPolynomial.exists_mem_eval_ne_zero₂` is not used: the curve's parameter `t` is chosen off the
  zero set of one polynomial in `t` — the Cramer section's denominator, `t` itself, the main-picture
  polynomials of `G` and of `H` along the curve (nonzero at `t = 1`), and the degenerate-rank
  polynomial along the curve (nonzero at `t = 0`).
* **The no-jump chain** is `dim ker M(0) ≤ dim L_{G/H}(q) = 3 + def₂(G/H) = 3 + def₂(G) ≤
  dim L_G(q(t)) ≤ dim ker M(t)` (Jackson–Jordán at `G/H`, `Graph.rigidContract_deficiency_eq` at
  `n = 2`, the flat lower bound at `G`), so Cramer's section through the flat-core solution of
  `M(0)` solves `M(t)` off one polynomial.
* **The core's rank is its flat rank**
  (`Graph.finrank_span_rigidityRows_ofNormals_flat_of_finrank_eq_three` after an affine shift); no
  collineation lemma is needed.
* **A defeq trap.** `V(G).ncard - W.ncard + 1` needs its parentheses (`TACTICS-QUIRKS.md` §48).

See `notes/Phase40f.md` and `notes/Phase40-design.md` §3 STEPS.
-/

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {k : ℕ} {K : Type*} [Field K] {α β : Type*}

/-! ## One plane on the core -/

/-- **A core of planar deficiency zero has one plane** (`lem:pencil-contract-core-plane`): at a core
`H = G[W]` with `q` admissible for `H` and `L_H(q) ⊆ Aff(q)`, a solution of `M(t)`, at every `t`,
has one plane `g` on the whole core — every core height is `g ⬝ (x_w, y_w, 1)` and every core
coefficient vector is `g`. The core rows keep the weight `(x_w, y_w, 1)` along the curve, so the
core heights lie in `L_H(q) = Aff(q)`, and three independent points in each core closed
neighbourhood pin its plane. -/
theorem _root_.Graph.exists_core_plane [Fintype α] {G : Graph α β} {W : Set α} {r : α}
    (hW : W ⊆ V(G)) {q : α × Fin 2 → K}
    (hqH : (G.induce W).IsAdmissiblePicture q)
    (hLH : (G.induce W).liftingSpace q ≤ (G.induce W).affineLifts q) {t : K}
    {x : α ⊕ (α × Fin 3) → K}
    (hx : (G.contractLiftingMatrix K W r q).map (MvPolynomial.eval (fun _ => t)) *ᵥ x = 0) :
    ∃ g : Fin 3 → K, (∀ w ∈ W, x (Sum.inl w) = g ⬝ᵥ pencilPicturePoint q w) ∧
      ∀ c ∈ W, (fun i => x (Sum.inr (c, i))) = g := by
  classical
  obtain ⟨-, h2, -⟩ := Graph.contractLiftingMatrix_mulVec_eq_zero_iff.mp hx
  have hcore : ∀ c ∈ W, ∀ w ∈ (G.induce W).closedNbhd c,
      x (Sum.inl w) = (fun i => x (Sum.inr (c, i))) ⬝ᵥ pencilPicturePoint q w := by
    intro c hc w hw
    have hwW : w ∈ W := Graph.closedNbhd_subset_vertexSet (G := G.induce W) hc hw
    rw [h2 c (hW hc) w (Graph.closedNbhd_induce_subset hw), Graph.contractWeightAt_of_mem hwW]
  have hmem : Graph.liftingRestrict W (fun w => x (Sum.inl w)) ∈ (G.induce W).liftingSpace q := by
    refine ⟨fun w hw => by simp [Graph.liftingRestrict_apply, show w ∉ W from hw], fun c hc => ?_⟩
    refine ⟨fun i => x (Sum.inr (c, i)), fun w hw => ?_⟩
    have hwW : w ∈ W := Graph.closedNbhd_subset_vertexSet (G := G.induce W) hc hw
    rw [Graph.liftingRestrict_apply, ite_eq_left hwW]
    exact hcore c hc w hw
  obtain ⟨g, hg⟩ := hLH hmem
  have hgw : ∀ w ∈ W, x (Sum.inl w) = g ⬝ᵥ pencilPicturePoint q w := by
    intro w hw
    have := congr_fun hg w
    simp only [Graph.affineLiftMap_apply, Graph.liftingRestrict_apply] at this
    rw [ite_eq_left (show w ∈ V(G.induce W) from hw), ite_eq_left hw] at this
    exact this.symm
  refine ⟨g, hgw, fun c hc => ?_⟩
  refine hqH.eq_of_forall_closedNbhd hc fun w hw => ?_
  have hwW : w ∈ W := Graph.closedNbhd_subset_vertexSet (G := G.induce W) hc hw
  rw [← hcore c hc w hw, hgw w hwW]

/-! ## The kernel at the end of the curve -/

/-- **The kernel at the end of the curve is at most `L_{G/H}(q)`** (`lem:pencil-contract-limit` (1);
(MC-59)(c2)'s upper bound): at a flat core (`L_H(q) ⊆ Aff(q)`), with `q` admissible for `H` and for
`G/H`, `dim ker M(0) ≤ dim L_{G/H}(q)`, through the injective limit map. -/
theorem _root_.Graph.finrank_ker_contractLiftingMatrix_zero_le [Fintype α] {G : Graph α β}
    {W : Set α} {r : α} (hr : r ∈ W) (hW : W ⊆ V(G)) {q : α × Fin 2 → K}
    (hqH : (G.induce W).IsAdmissiblePicture q)
    (hLH : (G.induce W).liftingSpace q ≤ (G.induce W).affineLifts q)
    (hqc : (G.rigidContract (G.induce W) r).IsAdmissiblePicture q) :
    Module.finrank K (LinearMap.ker ((G.contractLiftingMatrix K W r q).map
        (MvPolynomial.eval (fun _ => (0 : K)))).mulVecLin) ≤
      Module.finrank K ((G.rigidContract (G.induce W) r).liftingSpace q) := by
  set L := LinearMap.ker ((G.contractLiftingMatrix K W r q).map
    (MvPolynomial.eval (fun _ => (0 : K)))).mulVecLin
  set Φ := (contractLimitMap (K := K) G W r).domRestrict L
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨x, hx⟩ h0
    exact Subtype.ext (Graph.eq_zero_of_contractLimitMap_eq_zero hr hW hqc hx
      (Graph.exists_core_plane hW hqH hLH hx) h0)
  have hrange : LinearMap.range Φ ≤ (G.rigidContract (G.induce W) r).liftingSpace q := by
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    exact Graph.contractLimitMap_mem_liftingSpace hr hW hx (Graph.exists_core_plane hW hqH hLH hx)
  rw [← LinearMap.finrank_range_of_inj hinj]
  exact Submodule.finrank_mono hrange

/-! ## The core's rank along the curve -/

/-- **The core is rigid along the curve** (`lem:pencil-contract-core-rank`; (MC-38)/(MC-59)(b) in
the form the step consumes). At `t` with `q(t)` admissible for the connected core and
`dim L_H(q(t)) = 3`, the core's rank at the configuration `(q(t), z(t))` of a solution of `M(t)` is
`6(|W| − 1)`: the core heights are an affine function of `q(t)` (`Graph.exists_core_plane`), so the
rank is the flat rank (`Graph.finrank_span_rigidityRows_ofNormals_flat_of_finrank_eq_three`). -/
theorem _root_.Graph.finrank_span_rigidityRows_induce_contractHeight [Fintype α] {G : Graph α β}
    {W : Set α} {r : α} (hW : W ⊆ V(G)) {q : α × Fin 2 → K}
    (hqH : (G.induce W).IsAdmissiblePicture q)
    (hLH : (G.induce W).liftingSpace q ≤ (G.induce W).affineLifts q)
    (hHc : (G.induce W).Connected) {t : K}
    (hqtH : (G.induce W).IsAdmissiblePicture (contractPicture W r q t))
    (h3t : Module.finrank K ((G.induce W).liftingSpace (contractPicture W r q t)) = 3)
    {x : α ⊕ (α × Fin 3) → K}
    (hx : (G.contractLiftingMatrix K W r q).map (MvPolynomial.eval (fun _ => t)) *ᵥ x = 0)
    {ends : β → α × α}
    (hends : ∀ e u v, (G.induce W).IsLink e u v → (G.induce W).IsLink e (ends e).1 (ends e).2) :
    (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 2) (G.induce W) ends
        (fun p => pencilConfigPoint (contractPicture W r q t) (contractHeight W t x) p.1 p.2)
          ).toBodyHinge.rigidityRows) : ℤ) = screwDim 2 * ((W.ncard : ℤ) - 1) := by
  classical
  obtain ⟨g, hgW, -⟩ := Graph.exists_core_plane hW hqH hLH hx
  set g' : Fin 3 → K := ![g 0, g 1, t * g 2 - (1 - t) * (g 0 * q (r, 0) + g 1 * q (r, 1))]
  have haff : Graph.liftingRestrict W (contractHeight W t x) =
      (G.induce W).affineLiftMap (contractPicture W r q t) g' := by
    funext w
    rw [Graph.liftingRestrict_apply, Graph.affineLiftMap_apply]
    by_cases hw : w ∈ W
    · rw [ite_eq_left hw, ite_eq_left (show w ∈ V(G.induce W) from hw), contractHeight_apply,
        ite_eq_left hw, hgW w hw]
      simp [g', pencilPicturePoint, contractPicture, hw, dotProduct, Fin.sum_univ_three]
      ring
    · rw [ite_eq_right hw, ite_eq_right (show w ∉ V(G.induce W) from hw)]
  -- read the rank on the restriction, which is a globally affine height
  have hcongr := PanelHingeFramework.finrank_span_rigidityRows_ofNormals_congr (k := 2)
    (G.induce W) hends hends (q := fun p => pencilConfigPoint (contractPicture W r q t)
      (contractHeight W t x) p.1 p.2)
    (q' := fun p => pencilConfigPoint (contractPicture W r q t)
      ((1 : K) • (0 : α → K) + (G.induce W).affineLiftMap (contractPicture W r q t) g') p.1 p.2)
    (fun y hy i => by
      rw [one_smul, zero_add, ← haff]
      exact (pencilConfigPoint_liftingRestrict W _ _ hy i).symm)
  rw [hcongr, Graph.finrank_span_rigidityRows_ofNormals_smul_add_affineLifts hends _ _ one_ne_zero
      ⟨g', rfl⟩]
  exact Graph.finrank_span_rigidityRows_ofNormals_flat_of_finrank_eq_three hHc hqtH hends h3t

/-! ## The standing hypotheses at the core -/

/-- **A `def₂`-rigid core satisfies the standing hypotheses** (`lem:pencil-contract-standing`): a
core `G[W]` of a simple `G` with `|W| ≥ 2` and `def₂(G[W]) = 0` is simple, connected, and of
minimum degree at least two (`Graph.connected_of_isKDof_zero`,
`Graph.two_le_degree_of_isKDof_zero`). -/
theorem _root_.Graph.isX0Graph_induce_of_deficiency_two_eq_zero [Finite α] [Finite β]
    {G : Graph α β} (hS : G.Simple) {W : Set α} (hW : W ⊆ V(G)) (hW2 : 2 ≤ W.ncard)
    (hdef : (G.induce W).deficiency 2 = 0) : (G.induce W).IsX0Graph where
  simple := hS.mono (Graph.induce_le hW)
  connected := Graph.connected_of_isKDof_zero (n := 2)
    (by rw [Graph.bodyBarDim_two]; norm_num) hdef
    (Set.nonempty_of_ncard_ne_zero (s := W) (by omega))
  two_le_degree := fun _ hv => Graph.two_le_degree_of_isKDof_zero (n := 2)
    (by rw [Graph.bodyBarDim_two]; norm_num) hdef hv hW2

/-! ## The assembly: contraction at a `def₂`-rigid core -/

/-- **Contraction at a `def₂`-rigid core** (`thm:pencil-x0-contract-rigid`; (MC-59)(d) with
(MC-39); Katoh–Tanigawa 2011 §6.2, Lemma 6.3, on configurations). Let `K` be infinite, let `G`
satisfy the standing hypotheses and be 2-edge-connected, and let `W ⊊ V(G)`, `|W| ≥ 2`, induce a
core `H = G[W]` with `def₂(H) = 0` and no outside body adjacent to two core bodies (`G/H` simple).
If `X₀(G/H)` attains, `X₀(G)` attains.

One picture `q` is generic for `G/H` and `H` and main for `G`. An attaining height of `G/H`,
shifted to vanish at `r`, extends to a solution of `M(0)`
(`Graph.exists_mem_ker_contractLiftingMatrix_zero`); the kernel does not jump
(`Graph.finrank_ker_contractLiftingMatrix_zero_le`, Jackson–Jordán, the conservation of `def₂`),
so Cramer's section through it solves `M(t)` off one polynomial in `t`. At the chosen `t`, the
core has rank `6(|W| − 1)` (`Graph.finrank_span_rigidityRows_induce_contractHeight`), the surviving
rows with the core columns deleted have rank at least `tgt(G/H)`
(`PanelHingeFramework.exists_rankPolynomial_rigidContract_induce_proj`), and the block coupling
(`PanelHingeFramework.finrank_span_rigidityRows_induce_add_map_extProj_le`) adds them to
`tgt(G)`, so `Graph.x0Attains_of_exists` applies. -/
theorem _root_.Graph.X0Attains.of_rigidContract [Infinite K] [Finite α] [Finite β]
    {G : Graph α β} (hG : G.IsX0Graph) (htec : G.TwoEdgeConnected) {W : Set α} {r : α}
    (hr : r ∈ W) (hWss : W ⊂ V(G)) (hW2 : 2 ≤ W.ncard) (hdef : (G.induce W).deficiency 2 = 0)
    (hatt : ∀ u ∉ W, ∀ c₁ ∈ W, ∀ c₂ ∈ W, G.Adj u c₁ → G.Adj u c₂ → c₁ = c₂)
    (hc : (G.rigidContract (G.induce W) r).X0Attains K) : G.X0Attains K := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have : Inhabited α := ⟨r⟩
  have hW : W ⊆ V(G) := hWss.subset
  have hWne : W.Nonempty := ⟨r, hr⟩
  have hV : V(G).Nonempty := hG.connected.nonempty
  -- standing facts at the core and at the contraction
  have hHX := Graph.isX0Graph_induce_of_deficiency_two_eq_zero hG.simple hW hW2 hdef
  have hHc := hHX.connected
  have hHS := hHX.simple
  have hH3 := hHX.three_le_ncard_closedNbhd
  have hdef3 : (G.induce W).deficiency 3 = 0 :=
    le_antisymm (hHc.deficiency_three_le_deficiency_two.trans hdef.le)
      ((G.induce W).deficiency_nonneg 3 hWne)
  have hcS := Graph.rigidContract_induce_simple hG.simple hr hatt
  have hc3 := Graph.three_le_ncard_closedNbhd_rigidContract hG htec hr hWss hatt
  have hrc : r ∈ V(G.rigidContract (G.induce W) r) :=
    (Graph.mem_vertexSet_rigidContract_iff hr hW).mpr (Or.inl rfl)
  -- (MC-35) and (MC-59)(c1): the deficiencies are conserved
  have hprop : ∀ n, (G.induce W).deficiency n = 0 → (G.induce W).IsProperRigidSubgraph G n :=
    fun n h => ⟨⟨Graph.induce_le hW, h⟩, hW2, hWss⟩
  have hdefc3 : (G.rigidContract (G.induce W) r).deficiency 3 = G.deficiency 3 := by
    have : NeZero (Graph.bodyHingeMult 3) := ⟨by decide⟩
    exact Graph.rigidContract_deficiency_eq (hprop 3 hdef3) hr
  have hdefc2 : (G.rigidContract (G.induce W) r).deficiency 2 = G.deficiency 2 := by
    have : NeZero (Graph.bodyHingeMult 2) := ⟨by decide⟩
    exact Graph.rigidContract_deficiency_eq (hprop 2 hdef) hr
  have hcount : V(G.rigidContract (G.induce W) r).ncard = (V(G).ncard - W.ncard) + 1 :=
    Graph.rigidContract_vertexSet_ncard hr hW
  have hWle : W.ncard ≤ V(G).ncard := Set.ncard_le_ncard hW (Set.toFinite _)
  -- one generic ambient picture `q`
  obtain ⟨endsc, Pc, hendsc, hPc, hgoodc⟩ := hc
  obtain ⟨PJc, hPJc, hJc⟩ :=
    Graph.exists_mvPolynomial_finrank_liftingSpace_eq (K := K) hcS ⟨r, hrc⟩ hc3
  obtain ⟨PJH, hPJH, hJH⟩ :=
    Graph.exists_mvPolynomial_finrank_liftingSpace_eq (K := K) hHS hWne hH3
  obtain ⟨Pm, hPm, hmain⟩ := G.exists_mvPolynomial_isMainPicture (K := K)
    hG.simple.toLoopless hG.three_le_ncard_closedNbhd
  obtain ⟨q, hq⟩ := MvPolynomial.exists_eval_ne_zero
    (mul_ne_zero (mul_ne_zero (mul_ne_zero hPc hPJc) hPJH) hPm)
  simp only [map_mul] at hq
  obtain ⟨hqcadm, Rc, ⟨z₁, hz₁, hRz₁⟩, hattc⟩ :=
    hgoodc q (left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hq)))
  obtain ⟨-, hqcdim⟩ := hJc q (right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hq)))
  obtain ⟨hqHmain, hqHdim⟩ := hJH q (right_ne_zero_of_mul (left_ne_zero_of_mul hq))
  -- the core's lifting space at `q` is `Aff(q)` (Jackson–Jordán at `H`, `def₂(H) = 0`)
  have hLH : (G.induce W).liftingSpace q ≤ (G.induce W).affineLifts q := by
    have h1 := Graph.finrank_affineLifts hqHmain.1 hWne
    have h2 : Module.finrank K ((G.induce W).liftingSpace q) = 3 := by
      rw [hdef] at hqHdim; exact_mod_cast hqHdim
    exact (Submodule.eq_of_le_of_finrank_eq ((G.induce W).affineLifts_le_liftingSpace q)
      (by rw [h1, h2])).ge
  -- an attaining height of `G/H`, shifted to vanish at `r` (same rank, (MC-3))
  set z' : α → K := (1 : K) • z₁ + (G.rigidContract (G.induce W) r).affineLiftMap q ![0, 0, -z₁ r]
    with hz'def
  have hz'L : z' ∈ (G.rigidContract (G.induce W) r).liftingSpace q := by
    rw [hz'def, one_smul]
    exact add_mem hz₁ ((G.rigidContract (G.induce W) r).affineLifts_le_liftingSpace q ⟨_, rfl⟩)
  have hz'r : z' r = 0 := by
    rw [hz'def]
    simp only [Pi.add_apply, one_smul, Graph.affineLiftMap_apply, ite_eq_left hrc]
    simp [pencilPicturePoint, dotProduct, Fin.sum_univ_three]
  have hrank' : (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 2)
      (G.rigidContract (G.induce W) r) endsc (fun p => pencilConfigPoint q z' p.1 p.2)
        ).toBodyHinge.rigidityRows) : ℤ) =
      screwDim 2 * ((V(G.rigidContract (G.induce W) r).ncard : ℤ) - 1) -
        (G.rigidContract (G.induce W) r).deficiency 3 := by
    rw [hz'def, Graph.finrank_span_rigidityRows_ofNormals_smul_add_affineLifts hendsc q z₁
      one_ne_zero ⟨_, rfl⟩]
    exact hattc z₁ hz₁ hRz₁
  -- (MC-37) step 2: the flat-core kernel vector of `M(0)`, and Cramer's section through it
  obtain ⟨x₀, hx₀, hx₀z⟩ := Graph.exists_mem_ker_contractLiftingMatrix_zero hr hW hatt hz'L hz'r
  obtain ⟨D, Z, hD₀, hZ₀, -, hZ⟩ :=
    Matrix.exists_mvPolynomial_section_mulVec_eq_zero (G.contractLiftingMatrix K W r q)
      (q₀ := fun _ => (0 : K)) hx₀
  -- the degenerate placement's projected surviving rank
  set ends := G.endsOf with hendsdef
  have hends : ∀ e u w, G.IsLink e u w → G.IsLink e (ends e).1 (ends e).2 :=
    fun e _ _ he => G.isLink_endsOf he.edge_mem
  have hendsI : ∀ X : Set α, ∀ e u w, (G.induce X).IsLink e u w →
      (G.induce X).IsLink e (ends e).1 (ends e).2 := by
    intro X e u w he
    have hl := hends e u w he.1
    rcases hl.eq_and_eq_or_eq_and_eq he.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨hl, h1 ▸ he.2.1, h2 ▸ he.2.2⟩
    · exact ⟨hl, h1 ▸ he.2.2, h2 ▸ he.2.1⟩
  have hendsD : ∀ e u w, (G.deleteEdges E(G.induce W)).IsLink e u w →
      (G.deleteEdges E(G.induce W)).IsLink e (ends e).1 (ends e).2 := by
    intro e u w he
    rw [Graph.deleteEdges_isLink] at he ⊢
    exact ⟨hends e u w he.1, he.2⟩
  have hendsM : ∀ e u w, (G.rigidContract (G.induce W) r).IsLink e u w →
      (G.rigidContract (G.induce W) r).IsLink e (Graph.collapseTo r W (ends e).1)
        (Graph.collapseTo r W (ends e).2) := by
    intro e u w hlink
    rw [Graph.rigidContract, Graph.map_isLink] at hlink ⊢
    obtain ⟨x, y, hxy, _, _⟩ := hlink
    exact ⟨_, _, hendsD e x y hxy, rfl, rfl⟩
  obtain ⟨Qc, hQc₀, hQc⟩ :=
    PanelHingeFramework.exists_rankPolynomial_rigidContract_induce_proj (k := 2) G hr hW ends
      hendsD (pencilConfigPoint q z')
      (fun e he => hqcadm.supportExtensor_ne_zero hendsM z' he) le_rfl
  -- the curve's polynomials, each nonzero
  have hevP : ∀ (P : MvPolynomial (α × Fin 2) K) (t : K),
      MvPolynomial.eval (fun _ => t) (MvPolynomial.bind₁ (contractPicturePoly W r q) P) =
        MvPolynomial.eval (contractPicture W r q t) P := by
    intro P t
    have hf : (fun i => MvPolynomial.eval (fun _ => t) (contractPicturePoly W r q i)) =
        contractPicture W r q t := funext (eval_contractPicturePoly W r q t)
    rw [MvPolynomial.eval_bind₁, hf]
  have hevQ : ∀ t : K, MvPolynomial.eval (fun _ => t)
      (MvPolynomial.bind₁ (contractConfigPoly W r q Z) Qc) = MvPolynomial.eval
      (fun p => pencilConfigPoint (contractPicture W r q t)
        (contractHeight W t (fun c => MvPolynomial.eval (fun _ => t) (Z c))) p.1 p.2) Qc := by
    intro t
    rw [MvPolynomial.eval_bind₁, eval_contractConfigPoly]
  have hPmC : MvPolynomial.bind₁ (contractPicturePoly W r q) Pm ≠ 0 := fun h => by
    have := hevP Pm 1
    rw [h, map_zero, contractPicture_one] at this
    exact (right_ne_zero_of_mul hq) this.symm
  have hPJHC : MvPolynomial.bind₁ (contractPicturePoly W r q) PJH ≠ 0 := fun h => by
    have := hevP PJH 1
    rw [h, map_zero, contractPicture_one] at this
    exact (right_ne_zero_of_mul (left_ne_zero_of_mul hq)) this.symm
  have hdeg : (fun p => pencilConfigPoint (contractPicture W r q 0)
      (contractHeight W 0 (fun c => MvPolynomial.eval (fun _ => (0 : K)) (Z c))) p.1 p.2) =
      degeneratePlacement r W (pencilConfigPoint q z') := by
    rw [hZ₀]
    funext ⟨w, i⟩
    simp only [degeneratePlacement]
    by_cases hw : w ∈ W
    · rw [collapseTo_of_mem hw]
      fin_cases i <;> simp [pencilConfigPoint, contractPicture, contractHeight_apply, hw, hz'r]
    · rw [collapseTo_of_not_mem hw]
      fin_cases i <;> simp [pencilConfigPoint, contractPicture, contractHeight_apply, hw, hx₀z w hw]
  have hQcC : MvPolynomial.bind₁ (contractConfigPoly W r q Z) Qc ≠ 0 := fun h => by
    have := hevQ 0
    rw [h, map_zero, hdeg] at this
    exact hQc₀ this.symm
  have hDne : D ≠ 0 := fun h => hD₀ (by rw [h, map_zero])
  have hX : (MvPolynomial.X () : MvPolynomial Unit K) ≠ 0 := MvPolynomial.X_ne_zero ()
  -- one `t` off every zero set
  obtain ⟨s, hs⟩ := MvPolynomial.exists_eval_ne_zero
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hDne hX) hPmC) hPJHC) hQcC)
  set t : K := s () with htdef
  have hst : s = fun _ => t := funext fun u => by cases u; rfl
  rw [hst] at hs
  simp only [map_mul, MvPolynomial.eval_X] at hs
  have hQt := right_ne_zero_of_mul hs
  have hPJt := right_ne_zero_of_mul (left_ne_zero_of_mul hs)
  have hPmt := right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hs))
  have ht : t ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul
    (left_ne_zero_of_mul hs)))
  have hDt : MvPolynomial.eval (fun _ => t) D ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul
    (left_ne_zero_of_mul (left_ne_zero_of_mul hs)))
  rw [hevP] at hPmt hPJt
  rw [hevQ] at hQt
  have hqtmain := hmain _ hPmt
  obtain ⟨hqtH, hqtHdim⟩ := hJH _ hPJt
  have h3t : Module.finrank K ((G.induce W).liftingSpace (contractPicture W r q t)) = 3 := by
    rw [hdef] at hqtHdim; exact_mod_cast hqtHdim
  -- (MC-59)(c3): no jump, so the section lies in `ker M(t)`
  have hdim : Module.finrank K (LinearMap.ker ((G.contractLiftingMatrix K W r q).map
        (MvPolynomial.eval (fun _ => (0 : K)))).mulVecLin) ≤
      Module.finrank K (LinearMap.ker ((G.contractLiftingMatrix K W r q).map
        (MvPolynomial.eval (fun _ => t))).mulVecLin) := by
    have h0 := Graph.finrank_ker_contractLiftingMatrix_zero_le hr hW hqHmain.1 hLH hqcadm
    have hlow := Graph.three_add_deficiency_le_finrank_liftingSpace hqtmain.1 hV
    have hup := Graph.finrank_liftingSpace_le_finrank_ker_contractLiftingMatrix
      (G := G) (W := W) (r := r) (q := q) ht
    rw [hdefc2] at hqcdim
    have : (Module.finrank K ((G.rigidContract (G.induce W) r).liftingSpace q) : ℤ) ≤
        Module.finrank K (G.liftingSpace (contractPicture W r q t)) := by linarith
    have := Nat.cast_le.mp this
    omega
  set xt : α ⊕ (α × Fin 3) → K := fun c => MvPolynomial.eval (fun _ => t) (Z c)
  have hxt := hZ (fun _ => t) hdim hDt
  -- the configuration at `t`
  set n : α × Fin 4 → K := fun p =>
    pencilConfigPoint (contractPicture W r q t) (contractHeight W t xt) p.1 p.2
  have hzt := Graph.contractHeight_mem_liftingSpace hxt
  have hH := Graph.finrank_span_rigidityRows_induce_contractHeight hW hqHmain.1 hLH hHc hqtH.1 h3t
    hxt (hendsI W)
  have hproj := hQc n hQt
  have hcouple :=
    PanelHingeFramework.finrank_span_rigidityRows_induce_add_map_extProj_le G W ends n
  refine Graph.x0Attains_of_exists hV ends hends hqtmain hzt ?_
  -- the count: `tgt(G) = 6(|W| − 1) + tgt(G/H)`
  have hrankM : Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 2)
      (G.rigidContract (G.induce W) r)
        (fun e => (Graph.collapseTo r W (ends e).1, Graph.collapseTo r W (ends e).2))
        (fun p => pencilConfigPoint q z' p.1 p.2)).toBodyHinge.rigidityRows) =
      Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 2)
        (G.rigidContract (G.induce W) r) endsc
          (fun p => pencilConfigPoint q z' p.1 p.2)).toBodyHinge.rigidityRows) :=
    PanelHingeFramework.finrank_span_rigidityRows_ofNormals_congr _ hendsM hendsc
      (fun _ _ _ => rfl)
  rw [hrankM] at hproj
  have hcountZ : (V(G.rigidContract (G.induce W) r).ncard : ℤ) =
      ((V(G).ncard : ℤ) - (W.ncard : ℤ)) + 1 := by
    rw [hcount]; push_cast [Nat.cast_sub hWle]; ring
  rw [screwDim_two] at hH hrank' ⊢
  rw [hcountZ, hdefc3] at hrank'
  have hc' : (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 2)
        (G.induce W) ends n).toBodyHinge.rigidityRows) : ℤ) +
      (Module.finrank K ((Submodule.span K (PanelHingeFramework.ofNormals (k := 2)
        (G.deleteEdges E(G.induce W)) ends n).toBodyHinge.rigidityRows).map
          (extProj (K := K) (k := 2) W).dualMap) : ℤ) ≤
      (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 2) G ends
        n).toBodyHinge.rigidityRows) : ℤ) := by exact_mod_cast hcouple
  have hp' : (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 2)
        (G.rigidContract (G.induce W) r) endsc
          (fun p => pencilConfigPoint q z' p.1 p.2)).toBodyHinge.rigidityRows) : ℤ) ≤
      (Module.finrank K ((Submodule.span K (PanelHingeFramework.ofNormals (k := 2)
        (G.deleteEdges E(G.induce W)) ends n).toBodyHinge.rigidityRows).map
          (extProj (K := K) (k := 2) W).dualMap) : ℤ) := by exact_mod_cast hproj
  linarith

end CombinatorialRigidity.Molecular
