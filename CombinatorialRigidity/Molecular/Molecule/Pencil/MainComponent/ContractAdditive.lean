/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.ContractCurve

/-!
# Contraction at an additive core

The step of the induction on the general configuration at an additive core
(`thm:pencil-x0-contract-additive`, `sec:main-component-contract`): Katoh and Tanigawa's contraction
case (KT 2011 §6.2, Lemma 6.3) read on configurations. Let `W ⊊ V(G)` with `|W| ≥ 2` induce a core
`H = G[W]` with `def₃(H) = 0`, let `r ∈ W`, and let `G/H = G.rigidContract (G.induce W) r` be the
contraction of `H` to `r`. Let no body outside `W` be adjacent to two bodies of `W` (`hatt`; for a
simple `G`, the simplicity of `G/H`), and let the planar deficiencies of `H` and `G/H` add up to at
most that of `G`, `def₂(H) + def₂(G/H) ≤ def₂(G)`. If the general configurations of `H` and of `G/H`
attain, so does that of `G`. The step at a core of planar deficiency zero
(`cor:pencil-x0-contract-rigid`, `MainComponent/Contract.lean`) is its corollary.

The step follows the scheme of `sec:main-component-cut` (`MainComponent/Cut.lean`) in its picture
and its count, and finds its height along the contraction curve `q(t)`, with the rescaled lifting
system `M(t)` of `MainComponent/ContractCurve.lean`. The kernel of `M(0)` is bounded below by
`3 + def₂(G)`, through the polynomial section of the kernel at the zero vector
(`Matrix.exists_mvPolynomial_section_mulVec_eq_zero`), and above through the core heights of its
solutions (`Graph.finrank_ker_contractLiftingMatrix_zero_add_three_le`). Additivity makes the two
bounds meet, so the core heights of the solutions of `M(0)` are all of `L_H(q)`. The attainment at
`H`, read on the core heights, and the degenerate-rank condition
(`PanelHingeFramework.exists_rankPolynomial_rigidContract_induce_proj`) then meet as two open
conditions inside `ker M(0)` (`MvPolynomial.exists_mem_eval_ne_zero₂`). Along the polynomial section
through a solution where both hold, the core's rank is read at `t ≠ 0` over the fixed picture `q`,
by an invertible linear map of `K⁴`
(`PanelHingeFramework.finrank_span_rigidityRows_ofNormals_linearEquiv`,
`Graph.finrank_span_rigidityRows_induce_contractHeight_eq`), where the general configuration of `H`
attains. The block-triangular rank bound
(`PanelHingeFramework.finrank_span_rigidityRows_induce_add_map_extProj_le`,
`lem:block-rank-contract`) then gives `G` the rank `6(|W| − 1) + tgt(G/H) = tgt(G)`.

## Main results

* `Graph.X0Attains.of_additiveContract`: `thm:pencil-x0-contract-additive`.
-/

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

/-- **Contraction at an additive core** (`thm:pencil-x0-contract-additive`): over an infinite field,
let `G` satisfy the standing hypotheses and be 2-edge-connected, let `W ⊊ V(G)` with `|W| ≥ 2` and
`def₃(G[W]) = 0`, such that no body outside `W` is adjacent to two bodies of `W` (`hatt`), and let
`G/H` be the contraction of `H = G[W]` to `r ∈ W`. If `def₂(H) + def₂(G/H) ≤ def₂(G)` and the
general configurations of `H` and of `G/H` attain, then the general configuration of `G` attains.

Proof. `H` satisfies the standing hypotheses (`Graph.isX0Graph_induce_of_deficiency_eq_zero` at
`n = 3`), `G/H` is simple with at least three members in every closed neighbourhood
(`Graph.rigidContract_induce_simple`, `Graph.three_le_ncard_closedNbhd_rigidContract`), and
`def₃(G/H) = def₃(G)` (`Graph.rigidContract_deficiency_eq`). One picture `q` off the zero sets of
the polynomials of the attainment and of Jackson and Jordán's equality
(`Graph.exists_mvPolynomial_finrank_liftingSpace_eq`) at `H` and at `G/H`, and of the main-picture
polynomial of `G`; an attaining height `z'` of `G/H` with `z'_r = 0`, by an affine shift
(`Graph.finrank_span_rigidityRows_ofNormals_smul_add_affineLifts`). The polynomial section through
the zero vector at `t = 0` gives `dim ker M(t) ≤ dim ker M(0)` off the zero set of a polynomial, so
at a `t ≠ 0` off it where `q(t)` is a main picture of `G`,
`3 + def₂(G) ≤ dim L_G(q(t)) ≤ dim ker M(0)` (`Graph.three_add_deficiency_le_finrank_liftingSpace`,
`Graph.finrank_liftingSpace_le_finrank_ker_contractLiftingMatrix`). With the kernel bound at `t = 0`
(`Graph.finrank_ker_contractLiftingMatrix_zero_add_three_le`), the equality at `H` and at `G/H`, and
additivity, `dim ker M(0) = 3 + def₂(G)`, and the core heights of the solutions of `M(0)` are all of
`L_H(q)`. So the polynomial of the attainment at `H`, read on the core heights, is nonzero somewhere
on `ker M(0)`. So is the polynomial that
`PanelHingeFramework.exists_rankPolynomial_rigidContract_induce_proj` gives at `(q, z')`, read at
the configuration `(q(0), z(0))` of a solution: it is nonzero at the solution that agrees with `z'`
off `W` (`Graph.exists_mem_ker_contractLiftingMatrix_zero`), whose configuration is the collapsed
placement of `(q, z')`. Both are nonzero at some `x₀ ∈ ker M(0)`
(`MvPolynomial.exists_mem_eval_ne_zero₂`). The polynomial section through `x₀` solves `M(t)` at
every `t ≠ 0` off the zero set of its polynomial where `q(t)` is a main picture, as the kernel does
not jump there. At such a `t` where both conditions hold along the section, the heights `z(t)` lie
in `L_G(q(t))` (`Graph.contractHeight_mem_liftingSpace`), `H` has rank `6(|W| − 1)`, read over `q`
(`Graph.finrank_span_rigidityRows_induce_contractHeight_eq`), and the rows of the other edges, with
the columns of `W` deleted, have rank at least `tgt(G/H)`. The block-triangular rank bound
(`PanelHingeFramework.finrank_span_rigidityRows_induce_add_map_extProj_le`) gives `G` rank at least
`6(|W| − 1) + tgt(G/H) = tgt(G)`, as `|V(G/H)| = |V(G)| − |W| + 1`
(`Graph.rigidContract_vertexSet_ncard`), and `Graph.x0Attains_of_exists` concludes. -/
theorem _root_.Graph.X0Attains.of_additiveContract [Infinite K] [Finite α] [Finite β]
    {G : Graph α β} (hG : G.IsX0Graph) (htec : G.TwoEdgeConnected) {W : Set α} {r : α}
    (hr : r ∈ W) (hWss : W ⊂ V(G)) (hW2 : 2 ≤ W.ncard) (hdef3 : (G.induce W).deficiency 3 = 0)
    (hadd : (G.induce W).deficiency 2 + (G.rigidContract (G.induce W) r).deficiency 2 ≤
      G.deficiency 2)
    (hatt : ∀ u ∉ W, ∀ c₁ ∈ W, ∀ c₂ ∈ W, G.Adj u c₁ → G.Adj u c₂ → c₁ = c₂)
    (hH : (G.induce W).X0Attains K)
    (hc : (G.rigidContract (G.induce W) r).X0Attains K) : G.X0Attains K := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have : Inhabited α := ⟨r⟩
  have hW : W ⊆ V(G) := hWss.subset
  have hWne : W.Nonempty := ⟨r, hr⟩
  have hV : V(G).Nonempty := hG.connected.nonempty
  -- standing facts at the core and at the contraction
  have hHX := Graph.isX0Graph_induce_of_deficiency_eq_zero hG.simple hW hW2 (n := 3)
    (by rw [Graph.bodyBarDim_three]; norm_num) hdef3
  have hHS := hHX.simple
  have hH3 := hHX.three_le_ncard_closedNbhd
  have hcS := Graph.rigidContract_induce_simple hG.simple hr hatt
  have hc3 := Graph.three_le_ncard_closedNbhd_rigidContract hG htec hr hWss hatt
  have hrc : r ∈ V(G.rigidContract (G.induce W) r) :=
    (Graph.mem_vertexSet_rigidContract_iff hr hW).mpr (Or.inl rfl)
  -- contracting the core keeps `def₃` (`lem:pencil-contraction-deficiency`)
  have hdefc3 : (G.rigidContract (G.induce W) r).deficiency 3 = G.deficiency 3 := by
    have : NeZero (Graph.bodyHingeMult 3) := ⟨by decide⟩
    exact Graph.rigidContract_deficiency_eq ⟨⟨Graph.induce_le hW, hdef3⟩, hW2, hWss⟩ hr
  have hcount : V(G.rigidContract (G.induce W) r).ncard = (V(G).ncard - W.ncard) + 1 :=
    Graph.rigidContract_vertexSet_ncard hr hW
  have hWle : W.ncard ≤ V(G).ncard := Set.ncard_le_ncard hW (Set.toFinite _)
  -- one generic ambient picture `q`
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
  -- an attaining height of `G/H`, shifted to vanish at `r` (`lem:pencil-rank-scale-shift`)
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
  -- the selector of `G`, and its restrictions
  set ends := G.endsOf with hendsdef
  have hends : ∀ e u w, G.IsLink e u w → G.IsLink e (ends e).1 (ends e).2 :=
    fun e _ _ he => G.isLink_endsOf he.edge_mem
  have hendsI := G.isLink_ends_induce hends
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
  -- the surviving rows near the collapsed placement (`lem:pencil-contract-degenerate-rank`)
  obtain ⟨Qc, hQc₀, hQc⟩ :=
    PanelHingeFramework.exists_rankPolynomial_rigidContract_induce_proj (k := 2) G hr hW ends
      hendsD (pencilConfigPoint q z')
      (fun e he => hqcadm.supportExtensor_ne_zero hendsM z' he) le_rfl
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
  -- the lower bound: `dim ker M(0) ≥ 3 + def₂(G)` (semicontinuity along `t`)
  set L := LinearMap.ker ((G.contractLiftingMatrix K W r q).map
    (MvPolynomial.eval (fun _ => (0 : K)))).mulVecLin with hL
  obtain ⟨D₀, -, hD₀₀, -, hD₀rank, -⟩ :=
    Matrix.exists_mvPolynomial_section_mulVec_eq_zero (G.contractLiftingMatrix K W r q)
      (q₀ := fun _ => (0 : K)) (z₀ := 0) (Matrix.mulVec_zero _)
  have hD₀ne : D₀ ≠ 0 := fun h => hD₀₀ (by rw [h, map_zero])
  have hlow0 : 3 + G.deficiency 2 ≤ (Module.finrank K L : ℤ) := by
    obtain ⟨s, hs⟩ := MvPolynomial.exists_eval_ne_zero (mul_ne_zero (mul_ne_zero hD₀ne hX) hPmC)
    set t : K := s () with htdef
    have hst : s = fun _ => t := funext fun u => by cases u; rfl
    rw [hst] at hs
    simp only [map_mul, MvPolynomial.eval_X] at hs
    rw [hevP] at hs
    have hqt := hmain _ (right_ne_zero_of_mul hs)
    have ht : t ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hs)
    have h1 := hD₀rank (fun _ => t) (left_ne_zero_of_mul (left_ne_zero_of_mul hs))
    have h2 := Graph.finrank_liftingSpace_le_finrank_ker_contractLiftingMatrix
      (G := G) (W := W) (r := r) (q := q) ht
    have h3 := Graph.three_add_deficiency_le_finrank_liftingSpace hqt.1 hV
    have : Module.finrank K (G.liftingSpace (contractPicture W r q t)) ≤ Module.finrank K L :=
      h2.trans h1
    have := Nat.cast_le (α := ℤ).mpr this
    linarith
  -- the upper bound (`lem:pencil-contract-kernel-bound`): the core heights of `ker M(0)` are
  -- all of `L_H(q)`
  have hK3 := Graph.finrank_ker_contractLiftingMatrix_zero_add_three_le hr hW hqHadm hqcadm
  have hmapLe : L.map (contractCoreRestrict W) ≤ (G.induce W).liftingSpace q := by
    rintro _ ⟨x, hx, rfl⟩
    exact Graph.liftingRestrict_mem_liftingSpace_induce_of_contract hW hx
  have hmapfin := Submodule.finrank_mono hmapLe
  have hup0 : (Module.finrank K L : ℤ) ≤ 3 + G.deficiency 2 := by
    have := Nat.cast_le (α := ℤ).mpr hK3
    have := Nat.cast_le (α := ℤ).mpr hmapfin
    push_cast at *
    linarith
  have honto : L.map (contractCoreRestrict W) = (G.induce W).liftingSpace q := by
    refine Submodule.eq_of_le_of_finrank_le hmapLe ?_
    have := Nat.cast_le (α := ℤ).mpr hK3
    push_cast at this
    have h' : (Module.finrank K ((G.induce W).liftingSpace q) : ℤ) ≤
        Module.finrank K (L.map (contractCoreRestrict W)) := by linarith
    exact_mod_cast h'
  -- two open conditions in `ker M(0)` (`lem:pencil-x0-fibre-intersection`)
  set PA : MvPolynomial (α ⊕ (α × Fin 3)) K :=
    MvPolynomial.rename Sum.inl (restrictPoly W RH) with hPAdef
  have hPA : ∀ x, MvPolynomial.eval x PA = MvPolynomial.eval (contractCoreRestrict W x) RH := by
    intro x
    rw [hPAdef, MvPolynomial.eval_rename, eval_restrictPoly, contractCoreRestrict_apply]
    rfl
  set PB : MvPolynomial (α ⊕ (α × Fin 3)) K := MvPolynomial.bind₁ (fun p : α × Fin 4 =>
    ![MvPolynomial.C (contractPicture W r q 0 (p.1, 0)),
      MvPolynomial.C (contractPicture W r q 0 (p.1, 1)),
      if p.1 ∈ W then 0 else MvPolynomial.X (Sum.inl p.1), 1] p.2) Qc with hPBdef
  have hPB : ∀ x, MvPolynomial.eval x PB = MvPolynomial.eval (fun p => pencilConfigPoint
      (contractPicture W r q 0) (contractHeight W 0 x) p.1 p.2) Qc := by
    intro x
    rw [hPBdef, MvPolynomial.eval_bind₁]
    congr 2
    funext ⟨w, i⟩
    fin_cases i
    · simp [pencilConfigPoint]
    · simp [pencilConfigPoint]
    · by_cases hw : w ∈ W <;> simp [pencilConfigPoint, contractHeight_apply, hw]
    · simp [pencilConfigPoint]
  have hdeg : ∀ x, (∀ w ∉ W, x (Sum.inl w) = z' w) →
      (fun p => pencilConfigPoint (contractPicture W r q 0) (contractHeight W 0 x) p.1 p.2) =
        degeneratePlacement r W (pencilConfigPoint q z') := by
    intro x hxz
    funext ⟨w, i⟩
    simp only [degeneratePlacement]
    by_cases hw : w ∈ W
    · rw [collapseTo_of_mem hw]
      fin_cases i <;> simp [pencilConfigPoint, contractPicture, contractHeight_apply, hw, hz'r]
    · rw [collapseTo_of_not_mem hw]
      fin_cases i <;> simp [pencilConfigPoint, contractPicture, contractHeight_apply, hw, hxz w hw]
  have hexA : ∃ x ∈ L, MvPolynomial.eval x PA ≠ 0 := by
    have hzH' : zH ∈ L.map (contractCoreRestrict W) := honto ▸ hzH
    obtain ⟨x, hx, hxz⟩ := hzH'
    exact ⟨x, hx, by rw [hPA, hxz]; exact hRzH⟩
  have hexB : ∃ x ∈ L, MvPolynomial.eval x PB ≠ 0 := by
    obtain ⟨x, hx, hxz⟩ := Graph.exists_mem_ker_contractLiftingMatrix_zero hr hW hatt hz'L hz'r
    exact ⟨x, hx, by rw [hPB, hdeg x hxz]; exact hQc₀⟩
  obtain ⟨x₀, hx₀L, hPA₀, hPB₀⟩ := MvPolynomial.exists_mem_eval_ne_zero₂ hexA hexB
  have hx₀ : (G.contractLiftingMatrix K W r q).map (MvPolynomial.eval (fun _ => (0 : K))) *ᵥ x₀
      = 0 := hx₀L
  -- the polynomial section through `x₀` (`lem:pencil-polynomial-section`)
  obtain ⟨D, Z, hD₀, hZ₀, -, hZ⟩ :=
    Matrix.exists_mvPolynomial_section_mulVec_eq_zero (G.contractLiftingMatrix K W r q)
      (q₀ := fun _ => (0 : K)) hx₀
  have hDne : D ≠ 0 := fun h => hD₀ (by rw [h, map_zero])
  have hPAC : MvPolynomial.bind₁ Z PA ≠ 0 := fun h => by
    have := MvPolynomial.eval_bind₁ (fun _ => (0 : K)) Z PA
    rw [h, map_zero, hZ₀] at this
    exact hPA₀ this.symm
  have hevQ : ∀ t : K, MvPolynomial.eval (fun _ => t)
      (MvPolynomial.bind₁ (contractConfigPoly W r q Z) Qc) = MvPolynomial.eval
      (fun p => pencilConfigPoint (contractPicture W r q t)
        (contractHeight W t (fun c => MvPolynomial.eval (fun _ => t) (Z c))) p.1 p.2) Qc := by
    intro t
    rw [MvPolynomial.eval_bind₁, eval_contractConfigPoly]
  have hQcC : MvPolynomial.bind₁ (contractConfigPoly W r q Z) Qc ≠ 0 := fun h => by
    have := hevQ 0
    rw [h, map_zero, hZ₀, ← hPB] at this
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
  have hDt : MvPolynomial.eval (fun _ => t) D ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul
    (left_ne_zero_of_mul (left_ne_zero_of_mul hs)))
  rw [hevP] at hPmt
  rw [hevQ] at hQt
  rw [MvPolynomial.eval_bind₁, hPA] at hPAt
  have hqtmain := hmain _ hPmt
  -- no jump: the section lies in `ker M(t)`
  have hdim : Module.finrank K L ≤ Module.finrank K (LinearMap.ker
      ((G.contractLiftingMatrix K W r q).map (MvPolynomial.eval (fun _ => t))).mulVecLin) := by
    have hlow := Graph.three_add_deficiency_le_finrank_liftingSpace hqtmain.1 hV
    have hup := Graph.finrank_liftingSpace_le_finrank_ker_contractLiftingMatrix
      (G := G) (W := W) (r := r) (q := q) ht
    have : (Module.finrank K L : ℤ) ≤ Module.finrank K (G.liftingSpace (contractPicture W r q t)) :=
      by linarith
    have := Nat.cast_le.mp this
    omega
  set xt : α ⊕ (α × Fin 3) → K := fun c => MvPolynomial.eval (fun _ => t) (Z c)
  have hxt := hZ (fun _ => t) hdim hDt
  -- the configuration at `t`
  set n : α × Fin 4 → K := fun p =>
    pencilConfigPoint (contractPicture W r q t) (contractHeight W t xt) p.1 p.2
  have hzt := Graph.contractHeight_mem_liftingSpace hxt
  -- the core's rank: attained over `q`, read along the curve (`lem:pencil-contract-magnified-rank`)
  have hmemH := Graph.liftingRestrict_mem_liftingSpace_induce_of_contract hW hxt
  have hH0 := hattH (contractCoreRestrict W xt) (by rw [contractCoreRestrict_apply]; exact hmemH)
    hPAt
  have hVH : V(G.induce W).ncard = W.ncard := rfl
  have hHcongr := PanelHingeFramework.finrank_span_rigidityRows_ofNormals_congr (k := 2)
    (G.induce W) (hendsI W) hendsH
    (q := fun p => pencilConfigPoint q (fun w => xt (Sum.inl w)) p.1 p.2)
    (q' := fun p => pencilConfigPoint q (contractCoreRestrict W xt) p.1 p.2)
    (fun y hy i => by
      rw [contractCoreRestrict_apply]
      exact (pencilConfigPoint_liftingRestrict W _ _ hy i).symm)
  have hH : (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 2)
      (G.induce W) ends n).toBodyHinge.rigidityRows) : ℤ) = screwDim 2 * ((W.ncard : ℤ) - 1) := by
    rw [Graph.finrank_span_rigidityRows_induce_contractHeight_eq q ht xt (hendsI W), hHcongr,
      hH0, hVH, hdef3, sub_zero]
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
