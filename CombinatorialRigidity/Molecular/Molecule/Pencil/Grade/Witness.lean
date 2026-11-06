/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Configuration
public import CombinatorialRigidity.Molecular.AlgebraicInduction.DeficiencyBound

/-!
# One attaining configuration forces the general one, in every dimension

`lem:pencil-d-x0-one-witness` (`blueprint/src/chapter/pencil-d.tex`): if a configuration `(q₀, z₀)`
over a main picture, with `m` heights `z₀ ∈ L(q₀)^m`, has the deficiency rank in dimension `m + 2`
at least, then the general configuration attains (`Graph.X0AttainsGrade`).

## Main results

* `Graph.IsAdmissiblePicture.supportExtensor_ne_zero_grade`: over an admissible picture every hinge
  of a configuration is nonzero, at every grade.
* `Graph.x0AttainsGrade_of_exists`: the one-witness lemma.
-/

@[expose] public section

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*} {m : ℕ}

/-- **The hinges of a configuration over an admissible picture are nonzero, at every grade** (a
step of `lem:pencil-d-x0-one-witness`, whose proof names it): the extensor at a link is nonzero
exactly when the two endpoint points are independent
(`PanelHingeFramework.toBodyHinge_supportExtensor_ne_zero_iff`), and adjacent picture points differ
(`linearIndependent_pencilConfigPointGrade_pair`), as at one height
(`Graph.IsAdmissiblePicture.supportExtensor_ne_zero`). -/
theorem _root_.Graph.IsAdmissiblePicture.supportExtensor_ne_zero_grade {G : Graph α β}
    {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) {ends : β → α × α}
    (hends : Graph.RecordsLinks G ends) (z : α × Fin m → K)
    {e : β} {u v : α} (he : G.IsLink e u v) :
    (PanelHingeFramework.ofNormals (k := m + 1) G ends
      (fun p => pencilConfigPointGrade q z p.1 p.2)).toBodyHinge.supportExtensor e ≠ 0 := by
  rw [PanelHingeFramework.toBodyHinge_supportExtensor_ne_zero_iff]
  exact linearIndependent_pencilConfigPointGrade_pair z (hq.1 e _ _ (hends.isLink he))

/-- A ring map commutes with the block layout `(x, y, u, w)` of a vector of `K^(m+3)`
(`pencilConfigPointGrade`): the coordinates `0` and `1`, the `m` heights, and the last. -/
theorem map_vecCons_vecCons_snoc {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (x y : R) (u : Fin m → R) (w : R) (j : Fin (m + 1 + 2)) :
    f (Matrix.vecCons x (Matrix.vecCons y (Fin.snoc u w)) j) =
      Matrix.vecCons (f x) (Matrix.vecCons (f y) (Fin.snoc (fun i => f (u i)) (f w))) j := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.lastCases ?_ (fun i => ?_) j) j) j
  · simp
  · simp
  · simp only [Matrix.cons_val_succ, Fin.snoc_last]
  · simp only [Matrix.cons_val_succ, Fin.snoc_castSucc]

/-- **One attaining configuration over a main picture makes the general configuration attain, in
every dimension** (`lem:pencil-d-x0-one-witness`): let `G` have a body. If a configuration
`(q₀, z₀)` with `q₀` a main picture and `m` heights `z₀ ∈ L(q₀)^m` has row rank (of
`PanelHingeFramework.ofNormals (k := m + 1)` at `pencilConfigPointGrade q₀ z₀`) at least
`screwDim (m + 1) * (|V(G)| − 1) − def_{m+2}(G)`, then the general configuration of `G` attains in
dimension `m + 2` (`Graph.X0AttainsGrade`).

The proof is that of `Graph.x0Attains_of_exists`, with the polynomial section of the lifting system
(`Matrix.exists_mvPolynomial_section_mulVec_eq_zero`) taken once for each height `i`: the column
`w ↦ z₀ (w, i)` lies in `L(q₀)`, so it lifts to a kernel vector and gets a section `(D i, Z i)`.
Then `P` is the product of the polynomial of admissibility, the `D i` and `Q` at the section
heights, `Q` being the rank polynomial of
`PanelHingeFramework.exists_rankPolynomial_of_le_finrank_linking` (the hinges are nonzero by
`Graph.IsAdmissiblePicture.supportExtensor_ne_zero_grade`), and `R` is `Q` at `(q, ·)`.
The rank never exceeds the target once every hinge is nonzero
(`BodyHingeFramework.finrank_span_rigidityRows_add_deficiency_le`, with
`Graph.bodyBarDim_add_one_eq_screwDim`). -/
theorem _root_.Graph.x0AttainsGrade_of_exists [Finite α] [Finite β] {G : Graph α β}
    (hV : V(G).Nonempty) (ends : β → α × α) (hends : Graph.RecordsLinks G ends)
    {q₀ : α × Fin 2 → K} (hq₀ : G.IsMainPicture q₀) {z₀ : α × Fin m → K}
    (hz₀ : z₀ ∈ G.liftingSpaceGrade q₀ m)
    (hrank : screwDim (m + 1) * ((V(G).ncard : ℤ) - 1) - G.deficiency (m + 2) ≤
      (Module.finrank K (Submodule.span K
        (PanelHingeFramework.ofNormals (k := m + 1) G ends
          (fun p => pencilConfigPointGrade q₀ z₀ p.1 p.2)).toBodyHinge.rigidityRows) : ℤ)) :
    G.X0AttainsGrade K m := by
  have : Fintype α := Fintype.ofFinite α
  -- The rank polynomial, nonzero at `(q₀, z₀)`.
  obtain ⟨Q, hQ₀, hQ⟩ := PanelHingeFramework.exists_rankPolynomial_of_le_finrank_linking G ends
    hends (q₀ := fun p => pencilConfigPointGrade q₀ z₀ p.1 p.2)
    (fun e he => hq₀.1.supportExtensor_ne_zero_grade hends z₀ he) (Int.toNat_le.mpr hrank)
  -- Admissibility near `q₀`.
  obtain ⟨Padm, hPadm₀, hPadm⟩ := hq₀.1.exists_mvPolynomial
  -- One polynomial section of the lifting system through each height of `z₀`.
  have hsec : ∀ i : Fin m, ∃ (D : MvPolynomial (α × Fin 2) K)
      (Z : α ⊕ (α × Fin 3) → MvPolynomial (α × Fin 2) K),
      MvPolynomial.eval q₀ D ≠ 0 ∧ (fun w => MvPolynomial.eval q₀ (Z (Sum.inl w))) =
        (fun w => z₀ (w, i)) ∧
      ∀ q : α × Fin 2 → K,
        Module.finrank K
          (LinearMap.ker ((G.liftingMatrix K).map (MvPolynomial.eval q₀)).mulVecLin) ≤
        Module.finrank K
          (LinearMap.ker ((G.liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin) →
        MvPolynomial.eval q D ≠ 0 →
          Matrix.mulVec ((G.liftingMatrix K).map (MvPolynomial.eval q))
            (fun v => MvPolynomial.eval q (Z v)) = 0 := by
    intro i
    have hzi := Graph.mem_liftingSpaceGrade.1 hz₀ i
    rw [← G.map_ker_liftingMatrix q₀] at hzi
    obtain ⟨x₀, hx₀, hx₀z⟩ := hzi
    obtain ⟨D, Z, hD₀, hZ₀, -, hZ⟩ :=
      Matrix.exists_mvPolynomial_section_mulVec_eq_zero (G.liftingMatrix K) hx₀
    refine ⟨D, Z, hD₀, ?_, hZ⟩
    rw [← hx₀z]
    funext w
    exact congr_fun hZ₀ (Sum.inl w)
  choose D Z hD₀ hZ₀ hZ using hsec
  -- `Q` at the configuration of the sections, as a polynomial in the picture.
  set Qsec : MvPolynomial (α × Fin 2) K := MvPolynomial.bind₁ (fun p : α × Fin (m + 1 + 2) =>
    Matrix.vecCons (MvPolynomial.X (p.1, 0)) (Matrix.vecCons (MvPolynomial.X (p.1, 1))
      (Fin.snoc (fun i : Fin m => Z i (Sum.inl p.1)) 1)) p.2) Q with hQsecdef
  have hQsec : ∀ q, MvPolynomial.eval q Qsec = MvPolynomial.eval
      (fun p => pencilConfigPointGrade q
        (fun r : α × Fin m => MvPolynomial.eval q (Z r.2 (Sum.inl r.1))) p.1 p.2) Q := by
    intro q
    rw [hQsecdef, MvPolynomial.eval_bind₁]
    congr 2
    funext ⟨w, j⟩
    rw [map_vecCons_vecCons_snoc (MvPolynomial.eval q)]
    simp [pencilConfigPointGrade]
  have hZz₀ : (fun r : α × Fin m => MvPolynomial.eval q₀ (Z r.2 (Sum.inl r.1))) = z₀ := by
    funext ⟨w, i⟩
    exact congr_fun (hZ₀ i) w
  refine ⟨ends, Padm * (∏ i, D i) * Qsec, Graph.recordsLinks_iff_forall_isLink.mp hends,
    fun h0 => ?_, fun q hq => ?_⟩
  · -- `P(q₀) ≠ 0`: the sections pass through `z₀`.
    have h := congrArg (MvPolynomial.eval q₀) h0
    rw [map_mul, map_mul, map_prod, hQsec, hZz₀, map_zero] at h
    exact mul_ne_zero (mul_ne_zero hPadm₀ (Finset.prod_ne_zero_iff.2 fun i _ => hD₀ i)) hQ₀ h
  · rw [map_mul, map_mul, map_prod] at hq
    have hadm := hPadm q (left_ne_zero_of_mul (left_ne_zero_of_mul hq))
    have hDq := Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul (left_ne_zero_of_mul hq))
    have hQq := right_ne_zero_of_mul hq
    rw [hQsec] at hQq
    have hdim : Module.finrank K
          (LinearMap.ker ((G.liftingMatrix K).map (MvPolynomial.eval q₀)).mulVecLin) ≤
        Module.finrank K
          (LinearMap.ker ((G.liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin) := by
      rw [Graph.finrank_ker_liftingMatrix hq₀.1, Graph.finrank_ker_liftingMatrix hadm]
      exact hq₀.2 q hadm
    have hmem : (fun r : α × Fin m => MvPolynomial.eval q (Z r.2 (Sum.inl r.1))) ∈
        G.liftingSpaceGrade q m := by
      rw [Graph.mem_liftingSpaceGrade]
      intro i
      rw [← G.map_ker_liftingMatrix q]
      exact ⟨fun v => MvPolynomial.eval q (Z i v), hZ i q hdim (hDq i (Finset.mem_univ i)), rfl⟩
    -- `Q` at the configurations `(q, ·)`, as a polynomial in the heights.
    set R : MvPolynomial (α × Fin m) K := MvPolynomial.bind₁ (fun p : α × Fin (m + 1 + 2) =>
      Matrix.vecCons (MvPolynomial.C (q (p.1, 0))) (Matrix.vecCons (MvPolynomial.C (q (p.1, 1)))
        (Fin.snoc (fun i : Fin m => MvPolynomial.X (p.1, i)) 1)) p.2) Q with hRdef
    have hR : ∀ z, MvPolynomial.eval z R =
        MvPolynomial.eval (fun p => pencilConfigPointGrade q z p.1 p.2) Q := by
      intro z
      rw [hRdef, MvPolynomial.eval_bind₁]
      congr 2
      funext ⟨w, j⟩
      rw [map_vecCons_vecCons_snoc (MvPolynomial.eval z)]
      simp [pencilConfigPointGrade]
    refine ⟨hadm, R, ⟨_, hmem, by rwa [hR]⟩, fun z _ hRz => ?_⟩
    rw [hR] at hRz
    have hup := BodyHingeFramework.finrank_span_rigidityRows_add_deficiency_le
      (PanelHingeFramework.ofNormals (k := m + 1) G ends
        (fun p => pencilConfigPointGrade q z p.1 p.2)).toBodyHinge
      (n := m + 2) (Graph.bodyBarDim_add_one_eq_screwDim (m + 1)) hV
      (fun e u v he _ => hadm.supportExtensor_ne_zero_grade hends z he)
    exact le_antisymm hup ((Int.self_le_toNat _).trans (by exact_mod_cast hQ _ hRz))

end CombinatorialRigidity.Molecular
