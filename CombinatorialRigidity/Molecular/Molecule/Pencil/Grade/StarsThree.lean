/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Stars

/-!
# A span containing two stars, at three interior bodies, in every dimension

The node `lem:pencil-d-stars-three` of `blueprint/src/chapter/pencil-d.tex`, `sec:pencil-d-short`,
in dimension `d = k + 1`, on `V = Fin (k + 2) → K`: `exists_mvPolynomial_starsThree`.

Its proof is that of `lem:pencil-d-stars-four` (`exists_mvPolynomial_starsFour`, `Grade/Stars.lean`)
on the forms on `⋀²`: the dual kernel curve for the family `starsFamily` at two interior points,
the first-order steps `forall_normalsJoin_eq_zero_of_firstOrder` and
`forall_mem_normalsJoin_eq_zero_of_pivot`, and the bound
`finrank_add_two_le_of_forall_ιMulti_eq_zero` of `lem:pencil-d-two-stars` (3). The chapter's
statement and proof follow it (`notes/Cleanup42.md`, R-13, aligned). The source (SHORT-CORE
workbook, S32) reads the annihilators in `⋀^(d-1)` and first finds four independent points, which
takes `κ ≤ 1` and `p_a`, `p_b` independent; here a coordinate of `y₁ ∨ y₃` takes that step's
place, and neither is assumed, nor `d ≥ 4`.
-/

@[expose] public section

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {k : ℕ}

/-- `lem:pencil-d-stars-three` (SHORT-CORE workbook, S32), on forms as
`exists_mvPolynomial_starsFour`, at `d = k + 1` (here `k` is the grade). `Sa = Π_a` and `Sb = Π_b`
have dimension `3` and meet in dimension `κ` with `d + κ ≤ 6`, and `pa ∈ Π_a`, `pb ∈ Π_b`. The
chain `Y 0, Y 1` is `y₁ ∈ Π_a`, `y₃ ∈ Π_b`; `J` is the span of the joins `pa ∨ y₁`, `y₁ ∨ y₃` and
`y₃ ∨ pb`, and `W = ρ + J`. Some polynomial `f`, nonzero at a pair with `y₁ ∈ Π_a` and
`y₃ ∈ Π_b`, has at every such pair with `f ≠ 0`: `y₁`, `y₃` linearly independent, and `W = ⋀²`
whenever `W` holds both stars. Here `f = μ ν`, with `μ` from `exists_mvPolynomial_dual_kernel_curve`
for `starsFamily` at two interior points and `ν` a coordinate of `y₁ ∨ y₃`. A nonzero form `φ₀`
killing `W` has `y₁` and `y₃` in its radical. Moving `y₁` along `u ∈ Π_a` gives a form `φ₁` that
kills `W` once `φ₀ (pa ∨ u) = 0`, and then `u` lies in the radical
(`forall_normalsJoin_eq_zero_of_firstOrder`): `pa` first, then all of `Π_a`
(`forall_mem_normalsJoin_eq_zero_of_pivot`). Moving `y₃` along `Π_b` does the same for `Π_b`. So
`Π_a + Π_b`, of dimension `6 - κ`, lies in the radical of `φ₀ ≠ 0`, and `6 - κ + 2 ≤ d + 1`
(`finrank_add_two_le_of_forall_ιMulti_eq_zero`), against `d + κ ≤ 6`. The source's `κ ≤ 1`,
`p_a`, `p_b` independent and `d ≥ 4` are not assumed (`notes/Cleanup42.md`, R-13). -/
theorem exists_mvPolynomial_starsThree [Infinite K]
    (ρ : Submodule K (⋀[K]^2 (Fin (k + 2) → K))) {Sa Sb : Submodule K (Fin (k + 2) → K)}
    (hSa : Module.finrank K Sa = 3) (hSb : Module.finrank K Sb = 3)
    (hdκ : k + Module.finrank K ↥(Sa ⊓ Sb) ≤ 5)
    {pa pb : Fin (k + 2) → K} (hpa : pa ∈ Sa) (hpb : pb ∈ Sb) :
    ∃ f : MvPolynomial (Fin 2 × Fin (k + 2)) K,
      (∃ Y : Fin 2 → Fin (k + 2) → K, Y 0 ∈ Sa ∧ Y 1 ∈ Sb ∧
        MvPolynomial.eval (fun p => Y p.1 p.2) f ≠ 0) ∧
      ∀ Y : Fin 2 → Fin (k + 2) → K, Y 0 ∈ Sa → Y 1 ∈ Sb →
        MvPolynomial.eval (fun p => Y p.1 p.2) f ≠ 0 →
        LinearIndependent K ![Y 0, Y 1] ∧
        (starGrade (Y 0) ⊔ starGrade (Y 1) ≤ ρ ⊔ Submodule.span K
            (Set.range fun i : Fin 3 =>
              normalsJoin (pathVertex pa Y pb i.castSucc) (pathVertex pa Y pb i.succ)) →
          ρ ⊔ Submodule.span K (Set.range fun i : Fin 3 =>
            normalsJoin (pathVertex pa Y pb i.castSucc) (pathVertex pa Y pb i.succ)) = ⊤) := by
  classical
  have : Module.Free K ρ := Module.Free.of_divisionRing K ρ
  have : Module.Finite K ρ := inferInstance
  obtain ⟨bρ, hbρ⟩ : ∃ bρ : Fin (Module.finrank K ρ) → ⋀[K]^2 (Fin (k + 2) → K),
      bρ = fun i => (Module.finBasis K ρ i : ⋀[K]^2 (Fin (k + 2) → K)) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ := exists_mvPolynomial_repr_starsFamily (n := 0) bρ pa pb
  -- the parameters: the uncurried pair, `Y 0 ∈ Sa`, `Y 1 ∈ Sb`
  obtain ⟨L, hL⟩ : ∃ L : Submodule K (Fin 2 × Fin (k + 2) → K), ∀ y, y ∈ L ↔
      (fun j => y (0, j)) ∈ Sa ∧ (fun j => y (1, j)) ∈ Sb :=
    ⟨Sa.comap (LinearMap.funLeft K K fun j => ((0 : Fin 2), j)) ⊓
      Sb.comap (LinearMap.funLeft K K fun j => ((1 : Fin 2), j)), fun y => Iff.rfl⟩
  obtain ⟨μ, hμ, hgen⟩ := exists_mvPolynomial_dual_kernel_curve
    ((Pi.basisFun K (Fin (k + 2))).exteriorPower 2) L
    (fun y => starsFamily bρ pa pb (fun i j => y (i, j))) c (fun y i s => hc _ i s)
  have hP1 : ∀ Y : Fin 2 → Fin (k + 2) → K, pathVertex pa Y pb 1 = Y 0 := fun Y =>
    pathVertex_eq_of_val_eq pa pb Y (i := 0) (by simp)
  have hP2 : ∀ Y : Fin 2 → Fin (k + 2) → K, pathVertex pa Y pb 2 = Y 1 := fun Y =>
    pathVertex_eq_of_val_eq pa pb Y (i := 1) (by simp)
  have hFj1 : ∀ Y : Fin 2 → Fin (k + 2) → K,
      starsFamily bρ pa pb Y (Sum.inr (Sum.inl 1)) = normalsJoin (Y 0) (Y 1) := by
    intro Y
    simp only [starsFamily, starsEnds, starsPoint, Sum.elim_inr, Sum.elim_inl]
    exact congrArg₂ normalsJoin (hP1 Y) (hP2 Y)
  -- the minor `ν`: a coordinate of `Y 0 ∨ Y 1`, nonzero at `a ∈ Sa`, `u ∈ Sb ∖ K a`
  have hSa0 : Sa ≠ ⊥ := fun h => by rw [h, finrank_bot] at hSa; omega
  obtain ⟨a, haS, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hSa0
  obtain ⟨u, huS, hu⟩ : ∃ u ∈ Sb, u ∉ K ∙ a := by
    by_contra! h
    have h1 := Submodule.finrank_mono (show Sb ≤ K ∙ a from h)
    rw [hSb, finrank_span_singleton ha0] at h1; omega
  have hau : normalsJoin a u ≠ 0 := by
    rw [normalsJoin_ne_zero_iff, LinearIndependent.pair_iff' ha0]
    intro c hc; exact hu (hc ▸ Submodule.smul_mem _ c (Submodule.mem_span_singleton_self a))
  obtain ⟨s₀, hs₀⟩ : ∃ s₀, ((Pi.basisFun K (Fin (k + 2))).exteriorPower 2).repr
      (normalsJoin a u) s₀ ≠ 0 := by
    by_contra! h
    exact hau (((Pi.basisFun K (Fin (k + 2))).exteriorPower 2).repr.injective
      (by ext s; simp [h]))
  have hYsL : (fun p : Fin 2 × Fin (k + 2) => (![a, u] : Fin 2 → Fin (k + 2) → K) p.1 p.2) ∈ L :=
    (hL _).2 ⟨haS, huS⟩
  have hm₀ : MvPolynomial.eval (fun p : Fin 2 × Fin (k + 2) => (![a, u] : Fin 2 → _) p.1 p.2)
      (c (Sum.inr (Sum.inl 1)) s₀) ≠ 0 := by
    rw [← hc, hFj1]; simpa using hs₀
  obtain ⟨y', hy'L, hy'μ, hy'm⟩ := MvPolynomial.exists_mem_eval_ne_zero₂ hμ ⟨_, hYsL, hm₀⟩
  refine ⟨μ * c (Sum.inr (Sum.inl 1)) s₀,
    ⟨fun i j => y' (i, j), ((hL y').1 hy'L).1, ((hL y').1 hy'L).2,
      by rw [map_mul]; exact mul_ne_zero hy'μ hy'm⟩, fun Y hY0 hY1 hf => ?_⟩
  have hyL : (fun p : Fin 2 × Fin (k + 2) => Y p.1 p.2) ∈ L := (hL _).2 ⟨hY0, hY1⟩
  rw [map_mul] at hf
  have hyμ := left_ne_zero_of_mul hf
  have hym := right_ne_zero_of_mul hf
  rw [← hc, hFj1] at hym
  have hJ01 : normalsJoin (Y 0) (Y 1) ≠ 0 := fun h => hym (by rw [h, map_zero]; rfl)
  refine ⟨(normalsJoin_ne_zero_iff _ _).mp hJ01, fun hle => ?_⟩
  by_contra hne
  obtain ⟨φ₀, hφ₀W, hφ₀⟩ := Submodule.ne_bot_iff _ |>.mp
    ((Submodule.dualAnnihilator_eq_bot_iff).not.mpr hne)
  have hφ₀S := mem_dualAnnihilator_starGrade_sup_starGrade_iff.mp
    (Submodule.dualAnnihilator_anti hle hφ₀W)
  have hφ₀W' := (Submodule.mem_dualAnnihilator φ₀).mp hφ₀W
  have hQ0 : starsPoint pa pb Y (Sum.inl (0 : Fin (0 + 2)).succ.castSucc) = Y 0 := by
    simp only [starsPoint, Sum.elim_inl]; exact pathVertex_succ_castSucc _ _ _ _
  have hQ1 : starsPoint pa pb Y (Sum.inl (1 : Fin (0 + 2)).succ.castSucc) = Y 1 := by
    simp only [starsPoint, Sum.elim_inl]; exact pathVertex_succ_castSucc _ _ _ _
  have hF0 : ∀ i, φ₀ (starsFamily bρ pa pb Y i) = 0 := by
    rintro (i | j | l | l)
    · exact hφ₀W' _ (Submodule.mem_sup_left (by rw [hbρ]; exact (Module.finBasis K ρ i).2))
    · exact hφ₀W' _ (Submodule.mem_sup_right (Submodule.subset_span ⟨j, rfl⟩))
    · simp only [starsFamily, starsEnds, Sum.elim_inr, Sum.elim_inl]
      rw [hQ0]; exact (hφ₀S _).1
    · simp only [starsFamily, starsEnds, Sum.elim_inr]
      rw [hQ1]; exact (hφ₀S _).2
  have hpvL : ∀ (a b : Fin (k + 2) → K) (x : Fin 2 → Fin (k + 2) → K) (j : Fin 3),
      pathVertex a x b j.castSucc = ![a, x 0, x 1] j := by
    intro a b x j; fin_cases j <;> rfl
  have hpvR : ∀ (a b : Fin (k + 2) → K) (x : Fin 2 → Fin (k + 2) → K) (j : Fin 3),
      pathVertex a x b j.succ = ![x 0, x 1, b] j := by
    intro a b x j; fin_cases j <;> rfl
  -- moving the chain along `Y'`: the forms `φ₁` of the dual kernel curve
  have hstep : ∀ Y' : Fin 2 → Fin (k + 2) → K, Y' 0 ∈ Sa → Y' 1 ∈ Sb →
      ∃ φ₁ : Module.Dual K (⋀[K]^2 (Fin (k + 2) → K)), (∀ x ∈ ρ, φ₁ x = 0) ∧
        (∀ j : Fin 3,
          φ₁ (normalsJoin (pathVertex pa Y pb j.castSucc) (pathVertex pa Y pb j.succ)) +
            φ₀ (normalsJoin (pathVertex 0 Y' 0 j.castSucc) (pathVertex pa Y pb j.succ) +
              normalsJoin (pathVertex pa Y pb j.castSucc) (pathVertex 0 Y' 0 j.succ)) = 0) ∧
        (∀ l, φ₁ (normalsJoin (Y 0) (Pi.single l 1)) +
          φ₀ (normalsJoin (Y' 0) (Pi.single l 1)) = 0) ∧
        (∀ l, φ₁ (normalsJoin (Y 1) (Pi.single l 1)) +
          φ₀ (normalsJoin (Y' 1) (Pi.single l 1)) = 0) := by
    intro Y' h0 h1
    have hwL : (fun p : Fin 2 × Fin (k + 2) => Y' p.1 p.2) ∈ L := (hL _).2 ⟨h0, h1⟩
    obtain ⟨φ₁, hφ₁⟩ := hgen _ hyL hyμ _ hwL _ _
      (fun t i => starsFamily_add_smul bρ pa pb Y Y' t i) φ₀ hF0
    have hd0 : starsDir Y' (Sum.inl (0 : Fin (0 + 2)).succ.castSucc) = Y' 0 := by
      simp only [starsDir, Sum.elim_inl]; exact pathVertex_succ_castSucc _ _ _ _
    have hd1 : starsDir Y' (Sum.inl (1 : Fin (0 + 2)).succ.castSucc) = Y' 1 := by
      simp only [starsDir, Sum.elim_inl]; exact pathVertex_succ_castSucc _ _ _ _
    refine ⟨φ₁, fun x hx => ?_, fun j => hφ₁ (Sum.inr (Sum.inl j)), fun l => ?_, fun l => ?_⟩
    · have hρ : φ₁ ∘ₗ ρ.subtype = 0 := (Module.finBasis K ρ).ext fun i => by
        have := hφ₁ (Sum.inl i)
        simpa [starsFamily, hbρ] using this
      exact LinearMap.congr_fun hρ ⟨x, hx⟩
    · have := hφ₁ (Sum.inr (Sum.inr (Sum.inl l)))
      simp only [starsFamily, starsEnds, Sum.elim_inr, Sum.elim_inl] at this
      rw [hQ0, hd0] at this
      simpa [starsDir, starsPoint, normalsJoin_zero_right] using this
    · have := hφ₁ (Sum.inr (Sum.inr (Sum.inr l)))
      simp only [starsFamily, starsEnds, Sum.elim_inr] at this
      rw [hQ1, hd1] at this
      simpa [starsDir, starsPoint, normalsJoin_zero_right] using this
  set W := ρ ⊔ Submodule.span K (Set.range fun i : Fin 3 =>
    normalsJoin (pathVertex pa Y pb i.castSucc) (pathVertex pa Y pb i.succ)) with hWdef
  have hWle : ∀ φ₁ : Module.Dual K (⋀[K]^2 (Fin (k + 2) → K)), (∀ x ∈ ρ, φ₁ x = 0) →
      φ₁ (normalsJoin pa (Y 0)) = 0 → φ₁ (normalsJoin (Y 0) (Y 1)) = 0 →
      φ₁ (normalsJoin (Y 1) pb) = 0 → ∀ x ∈ W, φ₁ x = 0 := by
    intro φ₁ hρ h0 h1 h2
    refine fun x hx => (sup_le (fun x hx => hρ x hx) (Submodule.span_le.mpr ?_) :
      W ≤ LinearMap.ker φ₁) hx
    rintro _ ⟨j, rfl⟩
    simp only [hpvL, hpvR, SetLike.mem_coe, LinearMap.mem_ker]
    fin_cases j <;> simpa
  -- `Sa` lies in the radical of `φ₀`: move `Y 0` along `u ∈ Sa`
  have hSa' : ∀ u ∈ Sa, ∀ v, φ₀ (normalsJoin u v) = 0 := by
    refine forall_mem_normalsJoin_eq_zero_of_pivot hpa fun u hu hpu => ?_
    obtain ⟨φ₁, hρ1, hJ1, hl0, -⟩ := hstep ![u, 0] hu Sb.zero_mem
    have hu1 : φ₀ (normalsJoin u (Y 1)) = 0 := by
      rw [normalsJoin_swap, map_neg, (hφ₀S u).2, neg_zero]
    refine forall_normalsJoin_eq_zero_of_firstOrder (le_sup_left.trans hle)
      (hWle φ₁ hρ1 ?_ ?_ ?_) hl0
    · have h := hJ1 0
      simp only [hpvL, hpvR] at h
      simpa [normalsJoin_zero_left, hpu] using h
    · have h := hJ1 1
      simp only [hpvL, hpvR] at h
      simpa [normalsJoin_zero_right, hu1] using h
    · have h := hJ1 2
      simp only [hpvL, hpvR] at h
      simpa [normalsJoin_zero_left, normalsJoin_zero_right] using h
  -- `Sb` lies in the radical of `φ₀`: move `Y 1` along `w ∈ Sb`
  have hSb' : ∀ w ∈ Sb, ∀ v, φ₀ (normalsJoin w v) = 0 := by
    refine forall_mem_normalsJoin_eq_zero_of_pivot hpb fun w hw hpw => ?_
    obtain ⟨φ₁, hρ1, hJ1, -, hl1⟩ := hstep ![0, w] Sa.zero_mem hw
    have hwb : φ₀ (normalsJoin w pb) = 0 := by
      rw [normalsJoin_swap, map_neg, hpw, neg_zero]
    refine forall_normalsJoin_eq_zero_of_firstOrder (le_sup_right.trans hle)
      (hWle φ₁ hρ1 ?_ ?_ ?_) hl1
    · have h := hJ1 0
      simp only [hpvL, hpvR] at h
      simpa [normalsJoin_zero_left, normalsJoin_zero_right] using h
    · have h := hJ1 1
      simp only [hpvL, hpvR] at h
      simpa [normalsJoin_zero_left, (hφ₀S w).1] using h
    · have h := hJ1 2
      simp only [hpvL, hpvR] at h
      simpa [normalsJoin_zero_right, hwb] using h
  -- so `Sa ⊔ Sb`, of dimension `6 - κ`, lies in the radical, against `k + κ ≤ 5`
  have hA : ∀ x ∈ Sa ⊔ Sb, ∀ v, φ₀ (exteriorPower.ιMulti K 2 ![x, v]) = 0 := by
    intro x hx v
    obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hx
    change φ₀ (normalsJoin (s + t) v) = 0
    rw [normalsJoin_add_left, map_add, hSa' s hs, hSb' t ht, add_zero]
  have h1 := finrank_add_two_le_of_forall_ιMulti_eq_zero hφ₀ hA
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq Sa Sb
  rw [Module.finrank_fin_fun] at h1
  omega

end CombinatorialRigidity.Molecular
