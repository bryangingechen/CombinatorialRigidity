/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Contract
public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Cut
public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Flat
public import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.ContractAdditive
public import CombinatorialRigidity.Molecular.Induction.SparseDeficiency
public import CombinatorialRigidity.Molecular.AlgebraicInduction.DeficiencyBound

/-!
# Contraction at an additive core, in every dimension

The lemmas of `sec:pencil-d-contract` (`blueprint/src/chapter/pencil-d.tex`): the induction step
in dimension `m + 2` that contracts a core `H = G.induce W` whose planar deficiencies add up
(`Graph.X0AttainsGrade.of_additiveContract`, `thm:pencil-d-contract-additive`), and its corollary
for a core of planar deficiency zero (`Graph.X0AttainsGrade.of_rigidContract`,
`cor:pencil-d-contract-rigid`). Both are the forms with `m` heights of
`Graph.X0Attains.of_additiveContract` (`MainComponent/ContractAdditive.lean`).

The proof follows the `d = 3` one: pick one picture `q` attaining the three graphs `G`, `H`, `G/H`
at once, move along the polynomial curve `contractPicture W r q t` to `t = 0`, take at `t = 0` one
solution of the matrix `M(0)` per height (the kernel lemma below), lift each to a polynomial
section in `t`, and read the rank at a generic `t` off the core and the surviving rows.

## Main results

* `Graph.finrank_ker_contractLiftingMatrix_zero_eq_and_map_eq`:
  `lem:pencil-contract-additive-kernel`.
* `contractConfigPolyGrade` and `eval_contractConfigPolyGrade`: the configurations along the
  curve, as polynomials in `t`, for `m` heights (`thm:pencil-d-contract-additive`).
* `Graph.X0AttainsGrade.of_additiveContract`: `thm:pencil-d-contract-additive`.
* `Graph.x0AttainsGrade_of_deficiency_two_eq`: `cor:pencil-d-jj-flat`, the corollary of the flat
  rank in every dimension (`Grade/Flat.lean`) that needs Jackson and Jordán's equality
  (`MainComponent/Bridge.lean`), here as `Grade/Flat.lean` sits before `Bridge`.
* `Graph.X0AttainsGrade.of_rigidContract`: `cor:pencil-d-contract-rigid`.
-/

@[expose] public section

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*} {m : ℕ}

/-! ## The configurations along the curve as polynomials in `t`, in every dimension -/

open Classical in
/-- **The configurations along the curve as polynomials in `t`, in every dimension**: the
polynomial curve, and the heights `contractHeight` of `m` families `Z i` of unknowns of `M(t)`,
polynomial in `t`. Its value at `t` is the configuration at `(q(t), z(t))`
(`eval_contractConfigPolyGrade`); with one height it is `contractConfigPoly`. -/
noncomputable def contractConfigPolyGrade (W : Set α) (r : α) (q : α × Fin 2 → K)
    (Z : Fin m → α ⊕ (α × Fin 3) → MvPolynomial Unit K) :
    α × Fin (m + 1 + 2) → MvPolynomial Unit K :=
  fun p => Matrix.vecCons (contractPicturePoly W r q (p.1, 0))
    (Matrix.vecCons (contractPicturePoly W r q (p.1, 1))
      (Fin.snoc (fun i => if p.1 ∈ W then MvPolynomial.X () * Z i (Sum.inl p.1)
        else Z i (Sum.inl p.1)) 1)) p.2

/-- Evaluating the polynomial configuration at `t` gives the configuration point at
`(q(t), z(t))`, in every dimension. -/
theorem eval_contractConfigPolyGrade (W : Set α) (r : α) (q : α × Fin 2 → K)
    (Z : Fin m → α ⊕ (α × Fin 3) → MvPolynomial Unit K) (t : K) :
    (fun p => MvPolynomial.eval (fun _ => t) (contractConfigPolyGrade W r q Z p)) =
      fun p => pencilConfigPointGrade (contractPicture W r q t)
        (fun p => contractHeight W t (fun c => MvPolynomial.eval (fun _ => t) (Z p.2 c)) p.1)
          p.1 p.2 := by
  funext ⟨w, j⟩
  simp only [contractConfigPolyGrade]
  rw [map_vecCons_vecCons_snoc (MvPolynomial.eval fun _ => t)]
  by_cases hw : w ∈ W <;>
    simp [pencilConfigPointGrade, eval_contractPicturePoly, contractHeight_apply, hw]

/-! ## Contraction at an additive core, in every dimension (`thm:pencil-d-contract-additive`) -/

/-- **Contraction at an additive core, in every dimension** (`thm:pencil-d-contract-additive`):
the form with `m` heights of `Graph.X0Attains.of_additiveContract`, with `deficiency 3` replaced
by `deficiency (m + 2)` and `X0Attains` by `X0AttainsGrade K m`. If the core `G.induce W` has
`(m + 2)`-deficiency zero and its planar deficiency adds to that of `G/H` without exceeding that of
`G`, then `G` attains whenever `G.induce W` and `G/H` do. -/
theorem _root_.Graph.X0AttainsGrade.of_additiveContract [Infinite K] [Finite α] [Finite β]
    {G : Graph α β} (hG : G.IsX0Graph) (htec : G.TwoEdgeConnected) {W : Set α} {r : α}
    (hr : r ∈ W) (hWss : W ⊂ V(G)) (hW2 : 2 ≤ W.ncard)
    (hdefd : (G.induce W).deficiency (m + 2) = 0)
    (hadd : (G.induce W).deficiency 2 + (G.rigidContract (G.induce W) r).deficiency 2 ≤
      G.deficiency 2)
    (hatt : ∀ u ∉ W, ∀ c₁ ∈ W, ∀ c₂ ∈ W, G.Adj u c₁ → G.Adj u c₂ → c₁ = c₂)
    (hH : (G.induce W).X0AttainsGrade K m)
    (hc : (G.rigidContract (G.induce W) r).X0AttainsGrade K m) : G.X0AttainsGrade K m := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have : Inhabited α := ⟨r⟩
  have hW : W ⊆ V(G) := hWss.subset
  have hWne : W.Nonempty := ⟨r, hr⟩
  have hV : V(G).Nonempty := hG.connected.nonempty
  have hbb : Graph.bodyBarDim (m + 2) = screwDim (m + 1) := Graph.bodyBarDim_add_one_eq_screwDim _
  -- the pieces
  have hHX := Graph.isX0Graph_induce_of_deficiency_eq_zero hG.simple hW hW2 (n := m + 2)
    (by rw [hbb]; exact one_le_screwDim) hdefd
  have hHS := hHX.simple
  have hH3 := hHX.three_le_ncard_closedNbhd
  have hcS := Graph.rigidContract_induce_simple hG.simple hr hatt
  have hc3 := Graph.three_le_ncard_closedNbhd_rigidContract hG htec hr hWss hatt
  have hrc : r ∈ V(G.rigidContract (G.induce W) r) :=
    (Graph.mem_vertexSet_rigidContract_iff hr hW).mpr (Or.inl rfl)
  have hdefcd : (G.rigidContract (G.induce W) r).deficiency (m + 2) = G.deficiency (m + 2) := by
    have : NeZero (Graph.bodyHingeMult (m + 2)) := ⟨by
      have := two_le_screwDim (k := m + 1) (by omega)
      unfold Graph.bodyHingeMult
      omega⟩
    exact Graph.rigidContract_deficiency_eq ⟨⟨Graph.induce_le hW, hdefd⟩, hW2, hWss⟩ hr
  have hcount : V(G.rigidContract (G.induce W) r).ncard = (V(G).ncard - W.ncard) + 1 :=
    Graph.rigidContract_vertexSet_ncard hr hW
  have hWle : W.ncard ≤ V(G).ncard := Set.ncard_le_ncard hW (Set.toFinite _)
  -- the picture
  obtain ⟨endsc, Pc, hendsc, hPc, hgoodc⟩ := hc
  obtain ⟨endsH, PH, hendsH, hPH, hgoodH⟩ := hH
  obtain ⟨PJc, hPJc, hJc⟩ :=
    Graph.exists_mvPolynomial_finrank_liftingSpace_eq (K := K) hcS ⟨r, hrc⟩ hc3
  obtain ⟨PJH, hPJH, hJH⟩ :=
    Graph.exists_mvPolynomial_finrank_liftingSpace_eq (K := K) hHS hWne hH3
  obtain ⟨Pm, hPm, hmain⟩ := G.exists_mvPolynomial_isMainPicture (K := K)
    hG.simple.toLoopless hG.three_le_ncard_closedNbhd
  obtain ⟨q, hq⟩ := MvPolynomial.exists_eval_ne_zero
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hPc hPJc) hPH) hPJH) hPm)
  simp only [map_mul] at hq
  obtain ⟨hqcadm, Rc, ⟨z₁, hz₁, hRz₁⟩, hattc⟩ := hgoodc q
    (left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hq))))
  obtain ⟨-, hqcdim⟩ := hJc q
    (right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hq))))
  obtain ⟨hqHadm, RH, ⟨zH, hzH, hRzH⟩, hattH⟩ := hgoodH q
    (right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hq)))
  obtain ⟨-, hqHdim⟩ := hJH q (right_ne_zero_of_mul (left_ne_zero_of_mul hq))
  have hPmq := right_ne_zero_of_mul hq
  have hqmain := hmain q hPmq
  -- attaining heights of `G/H`, shifted in each height to vanish at `r`
  -- (`lem:pencil-d-rank-scale-shift`, `T` the identity)
  set a : Fin m → α → K := fun i =>
    (G.rigidContract (G.induce W) r).affineLiftMap q ![0, 0, -z₁ (r, i)] with hadef
  have ha : ∀ i, a i ∈ (G.rigidContract (G.induce W) r).affineLifts q := fun i => ⟨_, rfl⟩
  set z' : α × Fin m → K := fun x =>
    LinearEquiv.refl K (Fin m → K) (fun j => z₁ (x.1, j)) x.2 + a x.2 x.1 with hz'def
  have hz'L : z' ∈ (G.rigidContract (G.induce W) r).liftingSpaceGrade q m := by
    refine Graph.mem_liftingSpaceGrade.2 fun i => ?_
    exact add_mem (Graph.mem_liftingSpaceGrade.1 hz₁ i)
      ((G.rigidContract (G.induce W) r).affineLifts_le_liftingSpace q (ha i))
  have hz'r : ∀ i, z' (r, i) = 0 := by
    intro i
    simp only [hz'def, hadef, LinearEquiv.refl_apply, Graph.affineLiftMap_apply, ite_eq_left hrc]
    simp [pencilPicturePoint, dotProduct, Fin.sum_univ_three]
  have hrank' : (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := m + 1)
      (G.rigidContract (G.induce W) r) endsc (fun p => pencilConfigPointGrade q z' p.1 p.2)
        ).toBodyHinge.rigidityRows) : ℤ) =
      screwDim (m + 1) * ((V(G.rigidContract (G.induce W) r).ncard : ℤ) - 1) -
        (G.rigidContract (G.induce W) r).deficiency (m + 2) := by
    rw [hz'def, Graph.finrank_span_rigidityRows_ofNormals_heights_linearEquiv_add_affineLifts
      hendsc q z₁ (LinearEquiv.refl K _) ha]
    exact hattc z₁ hz₁ hRz₁
  -- the selector of `G`, and its restrictions
  set ends := G.endsOf with hendsdef
  have hends : Graph.RecordsLinks G ends := Graph.recordsLinks_endsOf G
  have hendsD : Graph.RecordsLinks (G.deleteEdges E(G.induce W)) ends :=
    hends.mono Graph.deleteEdges_le
  have hendsM : Graph.RecordsLinks (G.rigidContract (G.induce W) r)
      (fun e => (Graph.collapseTo r W (ends e).1, Graph.collapseTo r W (ends e).2)) :=
    hendsD.map _
  -- the surviving rows near the collapsed placement (`lem:pencil-contract-degenerate-rank`)
  obtain ⟨Qc, hQc₀, hQc⟩ :=
    PanelHingeFramework.exists_rankPolynomial_rigidContract_induce_proj (k := m + 1) G hr hW ends
      hendsD (pencilConfigPointGrade q z')
      (fun e he => hqcadm.supportExtensor_ne_zero_grade hendsM z' he) le_rfl
  -- the kernel at the end of the curve (`lem:pencil-contract-additive-kernel`)
  set L := LinearMap.ker ((G.contractLiftingMatrix K W r q).map
    (MvPolynomial.eval (fun _ => (0 : K)))).mulVecLin with hL
  obtain ⟨hLdim, honto⟩ := Graph.finrank_ker_contractLiftingMatrix_zero_eq_and_map_eq hr hW hadd
    hqmain.1 hqHadm hqcadm hqHdim hqcdim
  -- its tuples, one solution of `M(0)` for each height: `ker M(0)^m`
  set Lm : Submodule K ((α ⊕ (α × Fin 3)) × Fin m → K) :=
    ⨅ i : Fin m, L.comap (LinearMap.funLeft K K fun c => (c, i)) with hLm
  have hmemLm : ∀ X : (α ⊕ (α × Fin 3)) × Fin m → K, X ∈ Lm ↔ ∀ i, (fun c => X (c, i)) ∈ L := by
    intro X
    simp [hLm, Submodule.mem_iInf]
    rfl
  -- two open conditions in `ker M(0)^m` (`lem:pencil-x0-fibre-intersection`)
  set PA : MvPolynomial ((α ⊕ (α × Fin 3)) × Fin m) K :=
    MvPolynomial.rename (fun p : α × Fin m => (Sum.inl p.1, p.2))
      (restrictPoly (Prod.fst ⁻¹' W) RH) with hPAdef
  have hPA : ∀ X : (α ⊕ (α × Fin 3)) × Fin m → K, MvPolynomial.eval X PA =
      MvPolynomial.eval (Graph.liftingRestrict (Prod.fst ⁻¹' W)
        (fun p => X (Sum.inl p.1, p.2))) RH := by
    intro X
    rw [hPAdef, MvPolynomial.eval_rename, eval_restrictPoly]
    rfl
  set PB : MvPolynomial ((α ⊕ (α × Fin 3)) × Fin m) K :=
    MvPolynomial.bind₁ (fun p : α × Fin (m + 1 + 2) =>
      Matrix.vecCons (MvPolynomial.C (contractPicture W r q 0 (p.1, 0)))
        (Matrix.vecCons (MvPolynomial.C (contractPicture W r q 0 (p.1, 1)))
          (Fin.snoc (fun i : Fin m =>
            if p.1 ∈ W then 0 else MvPolynomial.X (Sum.inl p.1, i)) 1)) p.2) Qc with hPBdef
  have hPB : ∀ X : (α ⊕ (α × Fin 3)) × Fin m → K, MvPolynomial.eval X PB =
      MvPolynomial.eval (fun p => pencilConfigPointGrade (contractPicture W r q 0)
        (fun p => contractHeight W 0 (fun c => X (c, p.2)) p.1) p.1 p.2) Qc := by
    intro X
    rw [hPBdef, MvPolynomial.eval_bind₁]
    congr 2
    funext ⟨w, j⟩
    rw [map_vecCons_vecCons_snoc (MvPolynomial.eval X)]
    by_cases hw : w ∈ W <;> simp [pencilConfigPointGrade, contractHeight_apply, hw]
  have hdeg : ∀ X : (α ⊕ (α × Fin 3)) × Fin m → K,
      (∀ i, ∀ w ∉ W, X (Sum.inl w, i) = z' (w, i)) →
      (fun p => pencilConfigPointGrade (contractPicture W r q 0)
        (fun p => contractHeight W 0 (fun c => X (c, p.2)) p.1) p.1 p.2) =
        degeneratePlacement r W (pencilConfigPointGrade q z') := by
    intro X hXz
    funext ⟨w, j⟩
    simp only [degeneratePlacement]
    by_cases hw : w ∈ W
    · rw [collapseTo_of_mem hw]
      simp [pencilConfigPointGrade, contractPicture, contractHeight_apply, hw, hz'r]
    · rw [collapseTo_of_not_mem hw]
      simp [pencilConfigPointGrade, contractPicture, contractHeight_apply, hw, hXz _ w hw]
  have hexA : ∃ X ∈ Lm, MvPolynomial.eval X PA ≠ 0 := by
    have hcol : ∀ i, ∃ x ∈ L, contractCoreRestrict W x = fun w => zH (w, i) := by
      intro i
      have : (fun w => zH (w, i)) ∈ L.map (contractCoreRestrict W) :=
        honto ▸ Graph.mem_liftingSpaceGrade.1 hzH i
      obtain ⟨x, hx, hxz⟩ := this
      exact ⟨x, hx, hxz⟩
    choose x hx hxz using hcol
    refine ⟨fun c => x c.2 c.1, (hmemLm _).2 hx, ?_⟩
    have hρ : Graph.liftingRestrict (Prod.fst ⁻¹' W) (fun p => x p.2 (Sum.inl p.1)) = zH := by
      funext ⟨w, i⟩
      exact congrFun (hxz i) w
    rw [hPA]
    exact hρ ▸ hRzH
  have hexB : ∃ X ∈ Lm, MvPolynomial.eval X PB ≠ 0 := by
    have hcol : ∀ i, ∃ x ∈ L, ∀ w ∉ W, x (Sum.inl w) = z' (w, i) := fun i =>
      Graph.exists_mem_ker_contractLiftingMatrix_zero hr hW hatt
        (Graph.mem_liftingSpaceGrade.1 hz'L i) (hz'r i)
    choose x hx hxz using hcol
    have h := hdeg (fun c => x c.2 c.1) fun i w hw => hxz i w hw
    beta_reduce at h
    exact ⟨fun c => x c.2 c.1, (hmemLm _).2 hx, by rw [hPB, h]; exact hQc₀⟩
  obtain ⟨x₀, hx₀L, hPA₀, hPB₀⟩ := MvPolynomial.exists_mem_eval_ne_zero₂ hexA hexB
  have hx₀ : ∀ i, (G.contractLiftingMatrix K W r q).map (MvPolynomial.eval (fun _ => (0 : K))) *ᵥ
      (fun c => x₀ (c, i)) = 0 := (hmemLm x₀).1 hx₀L
  -- one polynomial section of `M(t)` through each member of `x₀` (`lem:pencil-polynomial-section`)
  have hsec : ∀ i : Fin m, ∃ (D : MvPolynomial Unit K) (Z : α ⊕ (α × Fin 3) → MvPolynomial Unit K),
      MvPolynomial.eval (fun _ => (0 : K)) D ≠ 0 ∧
      (fun c => MvPolynomial.eval (fun _ => (0 : K)) (Z c)) = (fun c => x₀ (c, i)) ∧
      ∀ s : Unit → K, Module.finrank K L ≤ Module.finrank K (LinearMap.ker
          ((G.contractLiftingMatrix K W r q).map (MvPolynomial.eval s)).mulVecLin) →
        MvPolynomial.eval s D ≠ 0 →
          (G.contractLiftingMatrix K W r q).map (MvPolynomial.eval s) *ᵥ
            (fun c => MvPolynomial.eval s (Z c)) = 0 := by
    intro i
    obtain ⟨D, Z, hD₀, hZ₀, -, hZ⟩ :=
      Matrix.exists_mvPolynomial_section_mulVec_eq_zero (G.contractLiftingMatrix K W r q)
        (q₀ := fun _ => (0 : K)) (hx₀ i)
    exact ⟨D, Z, hD₀, hZ₀, hZ⟩
  choose D Z hD₀ hZ₀ hZ using hsec
  have hDne : (∏ i, D i) ≠ 0 := fun h => by
    have := congrArg (MvPolynomial.eval (fun _ => (0 : K))) h
    rw [map_prod, map_zero] at this
    exact Finset.prod_ne_zero_iff.2 (fun i _ => hD₀ i) this
  -- the curve's polynomials
  have hevP : ∀ (P : MvPolynomial (α × Fin 2) K) (t : K),
      MvPolynomial.eval (fun _ => t) (MvPolynomial.bind₁ (contractPicturePoly W r q) P) =
        MvPolynomial.eval (contractPicture W r q t) P := by
    intro P t
    have hf : (fun i => MvPolynomial.eval (fun _ => t) (contractPicturePoly W r q i)) =
        contractPicture W r q t := funext (eval_contractPicturePoly W r q t)
    rw [MvPolynomial.eval_bind₁, hf]
  have hPmC : MvPolynomial.bind₁ (contractPicturePoly W r q) Pm ≠ 0 := fun h => by
    have := hevP Pm 1
    rw [h, map_zero, contractPicture_one] at this
    exact hPmq this.symm
  have hX : (MvPolynomial.X () : MvPolynomial Unit K) ≠ 0 := MvPolynomial.X_ne_zero ()
  have hZx₀ : (fun c : (α ⊕ (α × Fin 3)) × Fin m =>
      MvPolynomial.eval (fun _ => (0 : K)) (Z c.2 c.1)) = x₀ := by
    funext ⟨c, i⟩
    exact congrFun (hZ₀ i) c
  have hPAC : MvPolynomial.bind₁ (fun c : (α ⊕ (α × Fin 3)) × Fin m => Z c.2 c.1) PA ≠ 0 :=
    fun h => by
      have := MvPolynomial.eval_bind₁ (fun _ => (0 : K))
        (fun c : (α ⊕ (α × Fin 3)) × Fin m => Z c.2 c.1) PA
      rw [h, map_zero, hZx₀] at this
      exact hPA₀ this.symm
  have hevQ : ∀ t : K, MvPolynomial.eval (fun _ => t)
      (MvPolynomial.bind₁ (contractConfigPolyGrade W r q Z) Qc) = MvPolynomial.eval
      (fun p => pencilConfigPointGrade (contractPicture W r q t)
        (fun p => contractHeight W t (fun c => MvPolynomial.eval (fun _ => t) (Z p.2 c)) p.1)
          p.1 p.2) Qc := by
    intro t
    rw [MvPolynomial.eval_bind₁, eval_contractConfigPolyGrade]
  have hQcC : MvPolynomial.bind₁ (contractConfigPolyGrade W r q Z) Qc ≠ 0 := fun h => by
    have := hevQ 0
    have h0 : (fun p : α × Fin m =>
        contractHeight W 0 (fun c => MvPolynomial.eval (fun _ => (0 : K)) (Z p.2 c)) p.1) =
        fun p => contractHeight W 0 (fun c => x₀ (c, p.2)) p.1 := by
      funext ⟨w, i⟩
      exact congrArg (fun f => contractHeight W 0 f w) (hZ₀ i)
    rw [h, map_zero, h0, ← hPB] at this
    exact hPB₀ this.symm
  -- one `t` off every zero set
  obtain ⟨s, hs⟩ := MvPolynomial.exists_eval_ne_zero
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hDne hX) hPmC) hPAC) hQcC)
  set t : K := s () with htdef
  have hst : s = fun _ => t := funext fun u => by cases u; rfl
  rw [hst] at hs
  simp only [map_mul, MvPolynomial.eval_X] at hs
  have hQt := right_ne_zero_of_mul hs
  have hPAt := right_ne_zero_of_mul (left_ne_zero_of_mul hs)
  have hPmt := right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hs))
  have ht : t ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul
    (left_ne_zero_of_mul hs)))
  have hDt := left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul
    (left_ne_zero_of_mul hs)))
  rw [map_prod] at hDt
  rw [hevP] at hPmt
  rw [hevQ] at hQt
  rw [MvPolynomial.eval_bind₁, hPA] at hPAt
  have hqtmain := hmain _ hPmt
  -- no jump: each section lies in `ker M(t)`
  have hdim : Module.finrank K L ≤ Module.finrank K (LinearMap.ker
      ((G.contractLiftingMatrix K W r q).map (MvPolynomial.eval (fun _ => t))).mulVecLin) := by
    have hlow := Graph.three_add_deficiency_le_finrank_liftingSpace hqtmain.1 hV
    have hup := Graph.finrank_liftingSpace_le_finrank_ker_contractLiftingMatrix
      (G := G) (W := W) (r := r) (q := q) ht
    have : (Module.finrank K L : ℤ) ≤
        Module.finrank K (G.liftingSpace (contractPicture W r q t)) := by linarith
    have := Nat.cast_le.mp this
    omega
  set xt : Fin m → α ⊕ (α × Fin 3) → K := fun i c => MvPolynomial.eval (fun _ => t) (Z i c)
    with hxtdef
  have hxt : ∀ i, (G.contractLiftingMatrix K W r q).map (MvPolynomial.eval (fun _ => t)) *ᵥ
      xt i = 0 :=
    fun i => hZ i (fun _ => t) hdim (Finset.prod_ne_zero_iff.1 hDt i (Finset.mem_univ i))
  -- the configuration at `t`
  set n : α × Fin (m + 1 + 2) → K := fun p => pencilConfigPointGrade (contractPicture W r q t)
    (fun p => contractHeight W t (xt p.2) p.1) p.1 p.2 with hndef
  have hzt : (fun p : α × Fin m => contractHeight W t (xt p.2) p.1) ∈
      G.liftingSpaceGrade (contractPicture W r q t) m :=
    Graph.mem_liftingSpaceGrade.2 fun i => Graph.contractHeight_mem_liftingSpace (hxt i)
  -- the core's rank: attained over `q`, read along the curve
  -- (`lem:pencil-d-lifting-restrict`, `lem:pencil-d-contract-magnified-rank`)
  have hmemH : Graph.liftingRestrict (Prod.fst ⁻¹' W) (fun p => xt p.2 (Sum.inl p.1)) ∈
      (G.induce W).liftingSpaceGrade q m :=
    Graph.mem_liftingSpaceGrade.2 fun i =>
      Graph.liftingRestrict_mem_liftingSpace_induce_of_contract hW (hxt i)
  have hH0 := hattH _ hmemH hPAt
  rw [PanelHingeFramework.finrank_span_rigidityRows_ofNormals_liftingRestrict_grade (X := W)
    (fun _ h => h) hendsH (hends.induce W)] at hH0
  have hH : (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := m + 1)
      (G.induce W) ends n).toBodyHinge.rigidityRows) : ℤ) =
      screwDim (m + 1) * ((W.ncard : ℤ) - 1) := by
    rw [hndef, Graph.finrank_span_rigidityRows_induce_contractHeightGrade_eq q ht xt
      (hends.induce W), hH0, hdefd, sub_zero]
    rfl
  -- the rows outside the core (`lem:pencil-contract-degenerate-rank`)
  have hproj := hQc n hQt
  have hcouple :=
    PanelHingeFramework.finrank_span_rigidityRows_induce_add_map_extProj_le G W ends n
      (hlinks := by link_tac)
  refine Graph.x0AttainsGrade_of_exists hV ends hends hqtmain hzt ?_
  -- the count: `tgt_d(G) = D(|W| − 1) + tgt_d(G/H)` (`lem:block-rank-contract`)
  have hrankM : Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := m + 1)
      (G.rigidContract (G.induce W) r)
        (fun e => (Graph.collapseTo r W (ends e).1, Graph.collapseTo r W (ends e).2))
        (fun p => pencilConfigPointGrade q z' p.1 p.2)).toBodyHinge.rigidityRows) =
      Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := m + 1)
        (G.rigidContract (G.induce W) r) endsc
          (fun p => pencilConfigPointGrade q z' p.1 p.2)).toBodyHinge.rigidityRows) :=
    PanelHingeFramework.finrank_span_rigidityRows_ofNormals_congr _ hendsM hendsc
      (fun _ _ _ => rfl)
  rw [hrankM] at hproj
  have hcountZ : (V(G.rigidContract (G.induce W) r).ncard : ℤ) =
      ((V(G).ncard : ℤ) - (W.ncard : ℤ)) + 1 := by
    rw [hcount]; push_cast [Nat.cast_sub hWle]; ring
  rw [hcountZ, hdefcd] at hrank'
  have hc' : (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := m + 1)
        (G.induce W) ends n).toBodyHinge.rigidityRows) : ℤ) +
      (Module.finrank K ((Submodule.span K (PanelHingeFramework.ofNormals (k := m + 1)
        (G.deleteEdges E(G.induce W)) ends n).toBodyHinge.rigidityRows).map
          (extProj (K := K) (k := m + 1) W).dualMap) : ℤ) ≤
      (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := m + 1) G ends
        n).toBodyHinge.rigidityRows) : ℤ) := by exact_mod_cast hcouple
  have hp' : (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := m + 1)
        (G.rigidContract (G.induce W) r) endsc
          (fun p => pencilConfigPointGrade q z' p.1 p.2)).toBodyHinge.rigidityRows) : ℤ) ≤
      (Module.finrank K ((Submodule.span K (PanelHingeFramework.ofNormals (k := m + 1)
        (G.deleteEdges E(G.induce W)) ends n).toBodyHinge.rigidityRows).map
          (extProj (K := K) (k := m + 1) W).dualMap) : ℤ) := by exact_mod_cast hproj
  linarith

/-! ## The two deficiencies agree (`cor:pencil-d-jj-flat`) -/

/-- **The general configuration attains in dimension `m + 2` when `def₂(G) = def_(m+2)(G)`**
(`cor:pencil-d-jj-flat`): over an infinite field, if `G` is connected and simple, with at least
three members in every closed neighbourhood. Jackson and Jordán's equality gives a main picture with
`dim L(q) = 3 + def₂(G) = 3 + def_(m+2)(G)` (`Graph.exists_isMainPicture_finrank_liftingSpace_eq`),
and `Graph.x0AttainsGrade_of_finrank_liftingSpace_le` (`cor:pencil-d-flat-attains`) applies. -/
theorem _root_.Graph.x0AttainsGrade_of_deficiency_two_eq [Infinite K] [Finite α] [Finite β]
    {G : Graph α β} (hG : G.Connected) (hSimple : G.Simple)
    (h3 : ∀ v ∈ V(G), 3 ≤ (G.closedNbhd v).ncard)
    (hdef : G.deficiency 2 = G.deficiency (m + 2)) : G.X0AttainsGrade K m := by
  obtain ⟨q, hq, hdim⟩ := Graph.exists_isMainPicture_finrank_liftingSpace_eq (K := K) hSimple
    hG.nonempty h3
  exact Graph.x0AttainsGrade_of_finrank_liftingSpace_le hG hq.1 (by rw [hdim, hdef])

/-! ## Contraction at a core of planar deficiency zero, in every dimension
(`cor:pencil-d-contract-rigid`) -/

/-- **Contraction at a core of planar deficiency zero, in every dimension**
(`cor:pencil-d-contract-rigid`): a core of planar deficiency zero is `X0` and has
`(m + 2)`-deficiency zero, so contracting it preserves the planar deficiency and
`thm:pencil-d-contract-additive` applies, the core attaining by
`Graph.x0AttainsGrade_of_deficiency_two_eq`. -/
theorem _root_.Graph.X0AttainsGrade.of_rigidContract [Infinite K] [Finite α] [Finite β]
    {G : Graph α β} (hG : G.IsX0Graph) (htec : G.TwoEdgeConnected) {W : Set α} {r : α}
    (hr : r ∈ W) (hWss : W ⊂ V(G)) (hW2 : 2 ≤ W.ncard) (hdef : (G.induce W).deficiency 2 = 0)
    (hatt : ∀ u ∉ W, ∀ c₁ ∈ W, ∀ c₂ ∈ W, G.Adj u c₁ → G.Adj u c₂ → c₁ = c₂)
    (hc : (G.rigidContract (G.induce W) r).X0AttainsGrade K m) : G.X0AttainsGrade K m := by
  have hW : W ⊆ V(G) := hWss.subset
  have hHX := Graph.isX0Graph_induce_of_deficiency_eq_zero hG.simple hW hW2 (n := 2)
    (by rw [Graph.bodyBarDim_two]; norm_num) hdef
  have hdefd : (G.induce W).deficiency (m + 2) = 0 :=
    Graph.deficiency_eq_zero_of_deficiency_eq_zero_of_le (n := 2)
      (by rw [Graph.bodyBarDim_two]; norm_num) (by omega) ⟨r, hr⟩ hdef
  have hdefc2 : (G.rigidContract (G.induce W) r).deficiency 2 = G.deficiency 2 := by
    have : NeZero (Graph.bodyHingeMult 2) := ⟨by decide⟩
    exact Graph.rigidContract_deficiency_eq ⟨⟨Graph.induce_le hW, hdef⟩, hW2, hWss⟩ hr
  exact Graph.X0AttainsGrade.of_additiveContract hG htec hr hWss hW2 hdefd
    (by rw [hdef, hdefc2, zero_add]) hatt
    (Graph.x0AttainsGrade_of_deficiency_two_eq hHX.connected hHX.simple
      hHX.three_le_ncard_closedNbhd (by rw [hdef, hdefd])) hc

end CombinatorialRigidity.Molecular
