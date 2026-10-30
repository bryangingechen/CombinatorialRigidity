/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Witness
public import CombinatorialRigidity.Molecular.AlgebraicInduction.PanelLayer

/-!
# Independence of joins is an open condition, in every dimension

`lem:pencil-d-join-independence-open` (`blueprint/src/chapter/pencil-d.tex`): a finite family of
joins `b_u ∧ b_v ∈ ⋀² K^(m+3)` of configuration points, linearly independent at one picture (resp.
one list of heights), stays independent off the zero set of a polynomial in the picture (resp. the
heights) that is nonzero there. The coordinates of a join are the `2 × 2` minors of the two points
(`normalsJoinPoly`), polynomial in the picture at fixed heights and in the heights at a fixed
picture.

## Main results

* `exists_mvPolynomial_linearIndependent_normalsJoin`: the general form, for points whose
  coordinates are polynomials in the parameters.
* `exists_mvPolynomial_linearIndependent_join_picture_grade` and
  `exists_mvPolynomial_linearIndependent_join_heights_grade`: the two halves.
-/

@[expose] public section

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α : Type*} {m : ℕ}

/-- **Independence of joins of polynomial points is Zariski-open** (the shared step of
`lem:pencil-d-join-independence-open`): if the points `g p w ∈ K^(k+2)` have coordinates `pt w j`
polynomial in the parameters `p : σ → K`, and the joins `g p₀ (u i) ∧ g p₀ (v i)` are linearly
independent, they stay independent off the zero set of a polynomial nonzero at `p₀`: a nonzero
maximal minor of the `2 × 2`-minor coordinates `normalsJoinPoly`
(`exists_polynomial_ne_zero_of_linearIndependent_at_reindex`). -/
theorem exists_mvPolynomial_linearIndependent_normalsJoin {k : ℕ} {σ ι : Type*} [Finite ι]
    (pt : α → Fin (k + 2) → MvPolynomial σ K) (g : (σ → K) → α → Fin (k + 2) → K)
    (hg : ∀ p w j, MvPolynomial.eval p (pt w j) = g p w j) (u v : ι → α) {p₀ : σ → K}
    (h : LinearIndependent K (fun i => normalsJoin (g p₀ (u i)) (g p₀ (v i)))) :
    ∃ P : MvPolynomial σ K, MvPolynomial.eval p₀ P ≠ 0 ∧
      ∀ p, MvPolynomial.eval p P ≠ 0 →
        LinearIndependent K (fun i => normalsJoin (g p (u i)) (g p (v i))) := by
  classical
  set b := (Pi.basisFun K (Fin (k + 2))).exteriorPower 2 with hb
  let _ : Fintype (Set.powersetCard (Fin (k + 2)) 2) := Fintype.ofFinite _
  set e : Fin (Module.finrank K (⋀[K]^2 (Fin (k + 2) → K))) ≃
      Set.powersetCard (Fin (k + 2)) 2 :=
    (finCongr (Module.finrank_eq_card_basis b)).trans (Fintype.equivFin _).symm with he
  set c : ι → Set.powersetCard (Fin (k + 2)) 2 → MvPolynomial σ K :=
    fun i s => MvPolynomial.aeval (R := K) (fun x : α × Fin (k + 2) => pt x.1 x.2)
      (normalsJoinPoly (u i) (v i) s) with hc
  have hg' : ∀ p i s, b.equivFun (normalsJoin (g p (u i)) (g p (v i))) s =
      MvPolynomial.eval p (c i s) := by
    intro p i s
    rw [hc]
    simp only
    have : MvPolynomial.eval p (MvPolynomial.aeval (R := K) (fun x : α × Fin (k + 2) => pt x.1 x.2)
        (normalsJoinPoly (u i) (v i) s)) =
        MvPolynomial.eval (fun x : α × Fin (k + 2) => g p x.1 x.2)
          (normalsJoinPoly (u i) (v i) s) := by
      rw [← MvPolynomial.coe_aeval_eq_eval]
      change MvPolynomial.aeval p (MvPolynomial.aeval _ _) = _
      rw [MvPolynomial.comp_aeval_apply]
      simp [hg]
    rw [this, normalsJoinPoly_eval]
    rfl
  have h' : LinearIndependent K (fun i : (Set.univ : Set ι) =>
      normalsJoin (g p₀ (u i)) (g p₀ (v i))) := h.comp Subtype.val Subtype.val_injective
  obtain ⟨P, hP₀, hP⟩ := exists_polynomial_ne_zero_of_linearIndependent_at_reindex
    e (fun p i => normalsJoin (g p (u i)) (g p (v i))) c b.equivFun hg' h'
  refine ⟨P, hP₀, fun p hp => ?_⟩
  exact (hP p hp).comp (fun i => ⟨i, trivial⟩) (fun _ _ h => congrArg Subtype.val h)

/-- **Independence of joins is Zariski-open in the picture, in every dimension**
(`lem:pencil-d-join-independence-open`, heights fixed): if the joins
`b_(u i) ∧ b_(v i)` of the configuration points (`pencilConfigPointGrade`) are linearly
independent at `(q₀, z)`, they are independent at `(q, z)` whenever `P q ≠ 0`, for a polynomial `P`
in the picture nonzero at `q₀`. The hinges' independence follows, `complementIso` being an
isomorphism. -/
theorem exists_mvPolynomial_linearIndependent_join_picture_grade {ι : Type*} [Finite ι]
    (z : α × Fin m → K) (u v : ι → α) {q₀ : α × Fin 2 → K}
    (h : LinearIndependent K (fun i =>
      normalsJoin (pencilConfigPointGrade q₀ z (u i)) (pencilConfigPointGrade q₀ z (v i)))) :
    ∃ P : MvPolynomial (α × Fin 2) K, MvPolynomial.eval q₀ P ≠ 0 ∧
      ∀ q, MvPolynomial.eval q P ≠ 0 → LinearIndependent K (fun i =>
        normalsJoin (pencilConfigPointGrade q z (u i)) (pencilConfigPointGrade q z (v i))) := by
  refine exists_mvPolynomial_linearIndependent_normalsJoin (k := m + 1)
    (fun w => Matrix.vecCons (MvPolynomial.X (w, 0)) (Matrix.vecCons (MvPolynomial.X (w, 1))
      (Fin.snoc (fun i => MvPolynomial.C (z (w, i))) 1)))
    (fun q w => pencilConfigPointGrade q z w) (fun q w j => ?_) u v h
  rw [map_vecCons_vecCons_snoc (MvPolynomial.eval q)]
  simp [pencilConfigPointGrade]

/-- **Independence of joins is Zariski-open in the heights, in every dimension**
(`lem:pencil-d-join-independence-open`, picture fixed): if the joins of the configuration points
are linearly independent at `(q, z₀)`, they are independent at `(q, z)` whenever `R z ≠ 0`, for a
polynomial `R` in the heights nonzero at `z₀`. -/
theorem exists_mvPolynomial_linearIndependent_join_heights_grade {ι : Type*} [Finite ι]
    (q : α × Fin 2 → K) (u v : ι → α) {z₀ : α × Fin m → K}
    (h : LinearIndependent K (fun i =>
      normalsJoin (pencilConfigPointGrade q z₀ (u i)) (pencilConfigPointGrade q z₀ (v i)))) :
    ∃ R : MvPolynomial (α × Fin m) K, MvPolynomial.eval z₀ R ≠ 0 ∧
      ∀ z, MvPolynomial.eval z R ≠ 0 → LinearIndependent K (fun i =>
        normalsJoin (pencilConfigPointGrade q z (u i)) (pencilConfigPointGrade q z (v i))) := by
  refine exists_mvPolynomial_linearIndependent_normalsJoin (k := m + 1)
    (fun w => Matrix.vecCons (MvPolynomial.C (q (w, 0))) (Matrix.vecCons
      (MvPolynomial.C (q (w, 1))) (Fin.snoc (fun i => MvPolynomial.X (w, i)) 1)))
    (fun z w => pencilConfigPointGrade q z w) (fun z w j => ?_) u v h
  rw [map_vecCons_vecCons_snoc (MvPolynomial.eval z)]
  simp [pencilConfigPointGrade]

end CombinatorialRigidity.Molecular
