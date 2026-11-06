/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.AlgebraicInduction.PanelLayer

/-!
# The forms that vanish on a hinge, as polynomials in the normals

The second section of the former `PanelLayer.lean`, `lem:rows-polynomial-in-normals`: the forms
`annihRow` that vanish on a hinge, which span its hinge-row block, and the coordinates of the panel
support extensor and of these forms as polynomials of degree two in the normals (`annihRowPoly`).
The panel support extensor itself, its independence and the normals it needs are in
`PanelLayer.lean`.
-/

@[expose] public section

namespace CombinatorialRigidity.Molecular

variable {k' k : ℕ}
variable {K : Type*} [Field K]

/-! ## The forms that vanish on a hinge (`lem:rows-polynomial-in-normals`)

The hinge-row block of an edge whose hinge has the extensor `C` is the space `(span {C})^⊥` of the
forms that vanish at `C` (`def:hinge-row-block`). It is spanned by the forms
`C_{t₁} e_{t₂}^* − C_{t₂} e_{t₁}^*` for the pairs `(t₁, t₂)` of coordinates, where `C_t` is the
coordinate of `C` at `t` and `e_t^*` the dual basis form: each vanishes at `C`, and when `C ≠ 0`
they span the block. They are linear in `C`, so for a panel support extensor their coordinates are
polynomials of degree two in the normals. -/

/-- **The standard basis of the screw space** (the coordinates of `lem:rows-polynomial-in-normals`):
the basis of `⋀^k K^(k+2)` induced by the standard basis of `K^(k+2)`, indexed by the `k`-subsets of
`Fin (k+2)`, transported to `ScrewSpace K k` by `ScrewSpace.equivExteriorPower`. Its coordinates are
those that `panelSupportPoly` gives (`panelSupportPoly_eval`). -/
noncomputable def screwBasis (k : ℕ) :
    Module.Basis (Set.powersetCard (Fin (k + 2)) k) K (ScrewSpace K k) :=
  ((Pi.basisFun K (Fin (k + 2))).exteriorPower k).map (ScrewSpace.equivExteriorPower K k).symm

/-- **The coordinates in `screwBasis` are those in the basis of `⋀^k K^(k+2)`**, by `rfl`, as
`ScrewSpace.equivExteriorPower` is a cast. It lets the lemmas on `panelSupportPoly`, stated in the
second basis, and on `annihRow`, stated in the first, be combined. -/
theorem screwBasis_repr_apply (C : ScrewSpace K k) (t : Set.powersetCard (Fin (k + 2)) k) :
    (screwBasis k).repr C t = ((Pi.basisFun K (Fin (k + 2))).exteriorPower k).repr C t := rfl

/-- **The form of a pair of coordinates that vanishes at a screw** (the forms of
`lem:rows-polynomial-in-normals`): for `C ∈ ScrewSpace K k` and coordinates `t₁`, `t₂`, the form
`C_{t₁} • e_{t₂}^* − C_{t₂} • e_{t₁}^*` in `screwBasis`, that is,
`x ↦ C_{t₁} x_{t₂} − C_{t₂} x_{t₁}`. It vanishes at `C` (`annihRow_apply_self`), the forms of all
pairs span the forms that vanish at `C` when `C ≠ 0` (`span_annihRow_eq_dualAnnihilator`), and it is
linear in `C` (`annihRow_add`, `annihRow_smul`). -/
noncomputable def annihRow (C : ScrewSpace K k) (t₁ t₂ : Set.powersetCard (Fin (k + 2)) k) :
    Module.Dual K (ScrewSpace K k) :=
  (screwBasis k).repr C t₁ • (screwBasis k).coord t₂
    - (screwBasis k).repr C t₂ • (screwBasis k).coord t₁

@[simp]
theorem annihRow_apply (C : ScrewSpace K k) (t₁ t₂ : Set.powersetCard (Fin (k + 2)) k)
    (x : ScrewSpace K k) :
    annihRow C t₁ t₂ x =
      (screwBasis k).repr C t₁ * (screwBasis k).repr x t₂
        - (screwBasis k).repr C t₂ * (screwBasis k).repr x t₁ := by
  simp [annihRow]

/-- **The form `annihRow C t₁ t₂` vanishes at `C`**: its value there is
`C_{t₁} C_{t₂} − C_{t₂} C_{t₁}`. So it lies in the hinge-row block of a hinge with the extensor `C`.
-/
theorem annihRow_apply_self (C : ScrewSpace K k) (t₁ t₂ : Set.powersetCard (Fin (k + 2)) k) :
    annihRow C t₁ t₂ C = 0 := by
  rw [annihRow_apply]; ring

/-- **`annihRow` is additive in the screw**:
`annihRow (C + C') t₁ t₂ = annihRow C t₁ t₂ + annihRow C' t₁ t₂`, as each coordinate is linear. With
`annihRow_smul` and `panelSupportExtensor_add_left`, the forms of Case III's candidate hinge
`C(n_u + t • n', n_r)` are affine in `t`
(`PanelHingeFramework.caseIIICandidate_panelRow_eq_add_smul`). -/
theorem annihRow_add (C C' : ScrewSpace K k) (t₁ t₂ : Set.powersetCard (Fin (k + 2)) k) :
    annihRow (C + C') t₁ t₂ = annihRow C t₁ t₂ + annihRow (k := k) C' t₁ t₂ := by
  simp only [annihRow, map_add, Finsupp.add_apply, add_smul]
  abel

/-- **`annihRow` is homogeneous in the screw**: `annihRow (c • C) t₁ t₂ = c • annihRow C t₁ t₂`, as
each coordinate is linear. -/
theorem annihRow_smul (c : K) (C : ScrewSpace K k) (t₁ t₂ : Set.powersetCard (Fin (k + 2)) k) :
    annihRow (c • C) t₁ t₂ = c • annihRow (k := k) C t₁ t₂ := by
  simp only [annihRow, map_smul, Finsupp.smul_apply, smul_sub, smul_eq_mul, mul_smul]

/-- **`annihRow` changes sign with the screw**: `annihRow (−C) t₁ t₂ = −annihRow C t₁ t₂`, the case
`c = −1` of `annihRow_smul`. With `panelSupportExtensor_swap` and `hingeRow_swap`, it shows that a
panel row does not depend on the order in which the selector records the ends of its edge
(`PanelHingeFramework.ofNormals_panelRow_eq_hingeRow_of_ends_or_swap`). -/
theorem annihRow_neg (C : ScrewSpace K k) (t₁ t₂ : Set.powersetCard (Fin (k + 2)) k) :
    annihRow (-C) t₁ t₂ = -annihRow (k := k) C t₁ t₂ := by
  rw [show (-C) = (-1 : K) • C from (neg_one_smul K C).symm, annihRow_smul]
  module

/-- **The forms `annihRow C t₁ t₂` span the forms that vanish at `C`**
(`lem:rows-polynomial-in-normals`, the spanning): for `C ≠ 0`, their span is `(span {C})^⊥`, the
hinge-row block of a hinge with the extensor `C` (`def:hinge-row-block`). Each vanishes at `C`
(`annihRow_apply_self`). Conversely, take `t₀` with `C_{t₀} ≠ 0`. A form `f` that vanishes at `C` is
`∑_t (f(b_t) / C_{t₀}) • annihRow C t₀ t`: the two sides agree at each basis vector `b_s`, directly
for `s ≠ t₀`, and for `s = t₀` because `∑_t C_t f(b_t) = f C = 0`. -/
theorem span_annihRow_eq_dualAnnihilator (C : ScrewSpace K k) (hC : C ≠ 0) :
    Submodule.span K (Set.range (fun p : Set.powersetCard (Fin (k + 2)) k
        × Set.powersetCard (Fin (k + 2)) k => annihRow C p.1 p.2))
      = (Submodule.span K {C}).dualAnnihilator := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨⟨t₁, t₂⟩, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_dualAnnihilator]
    intro c hc
    rw [Submodule.mem_span_singleton] at hc
    obtain ⟨r, rfl⟩ := hc
    rw [map_smul, annihRow_apply_self, smul_zero]
  · intro f hf
    classical
    rw [Submodule.mem_dualAnnihilator] at hf
    have hfC : f C = 0 := hf C (Submodule.mem_span_singleton_self C)
    -- A coordinate `t₀` with `C_{t₀} ≠ 0`, available because `C ≠ 0`.
    obtain ⟨t₀, ht₀⟩ : ∃ t₀, (screwBasis k).repr C t₀ ≠ 0 := by
      by_contra h
      refine hC (Module.Basis.forall_coord_eq_zero_iff (screwBasis k) |>.1 fun t => ?_)
      rw [Module.Basis.coord_apply]
      exact not_not.1 fun ht => h ⟨t, ht⟩
    -- The Kronecker-delta form of the basis coordinates of a basis vector.
    have hδ : ∀ i j : Set.powersetCard (Fin (k + 2)) k,
        (screwBasis k).repr (screwBasis k i) j = if i = j then (1 : K) else 0 :=
      fun i j => Module.Basis.repr_self_apply (screwBasis k) (i := i) j
    -- `f C = ∑_t C_t · f(b t)` (the dual-basis expansion of `f C`), which is `0`.
    have hfC' : ∑ t, (screwBasis k).repr C t * f (screwBasis k t) = 0 := by
      rw [← hfC]
      conv_rhs => rw [← (screwBasis k).sum_repr C, map_sum]
      exact Finset.sum_congr rfl fun t _ => by rw [map_smul, smul_eq_mul]
    -- `f` is the explicit combination `∑_t (f (b t) / C_{t₀}) • annihRow C t₀ t`.
    have hsum : f = ∑ t, (f (screwBasis k t) / (screwBasis k).repr C t₀) • annihRow C t₀ t := by
      refine (screwBasis k).ext fun s => ?_
      rw [LinearMap.sum_apply]
      simp only [LinearMap.smul_apply, smul_eq_mul, annihRow_apply, hδ]
      rcases eq_or_ne s t₀ with hs | hs
      · subst hs
        -- Each summand is `(f(b x)/C_s)·(C_s·[s=x] − C_x·[s=s])`; split into two sums.
        have hsplit : ∀ x, f (screwBasis k x) / (screwBasis k).repr C s
            * ((screwBasis k).repr C s * (if s = x then (1 : K) else 0)
              - (screwBasis k).repr C x * (if s = s then (1 : K) else 0))
            = f (screwBasis k x) / (screwBasis k).repr C s
                * ((screwBasis k).repr C s * (if s = x then (1 : K) else 0))
              - f (screwBasis k x) / (screwBasis k).repr C s * (screwBasis k).repr C x := by
          intro x; rw [ite_eq_left rfl, mul_one]; ring
        rw [Finset.sum_congr rfl fun x _ => hsplit x, Finset.sum_sub_distrib]
        have h1 : ∑ x, f (screwBasis k x) / (screwBasis k).repr C s
            * ((screwBasis k).repr C s * (if s = x then (1 : K) else 0)) = f (screwBasis k s) := by
          rw [Finset.sum_eq_single s]
          · rw [ite_eq_left rfl, mul_one, div_mul_cancel₀ _ ht₀]
          · intro x _ hxs; rw [ite_eq_right (fun h => hxs h.symm), mul_zero, mul_zero]
          · intro h; exact absurd (Finset.mem_univ s) h
        have h2 : ∑ x, f (screwBasis k x) / (screwBasis k).repr C s
            * (screwBasis k).repr C x = 0 := by
          have hreorg : ∑ x, f (screwBasis k x) / (screwBasis k).repr C s
              * (screwBasis k).repr C x
              = (∑ x, (screwBasis k).repr C x * f (screwBasis k x))
                / (screwBasis k).repr C s := by
            rw [Finset.sum_div]
            exact Finset.sum_congr rfl fun x _ => by ring
          rw [hreorg, hfC', zero_div]
        rw [h1, h2, sub_zero]
      · rw [Finset.sum_eq_single s]
        · rw [ite_eq_left rfl, ite_eq_right hs, mul_zero, sub_zero, mul_one,
            div_mul_cancel₀ _ ht₀]
        · intro t _ hts
          rw [ite_eq_right (fun h => hts h.symm), ite_eq_right hs]; ring
        · intro h; exact absurd (Finset.mem_univ s) h
    rw [hsum]
    refine Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span ⟨(t₀, t), rfl⟩

/-- **The coordinates of the forms `annihRow` as polynomials in the normals** (a step of
`lem:rows-polynomial-in-normals`): for bodies `u`, `v`, the coordinate at the basis vector `b_s` of
`annihRow C(q (u, ·), q (v, ·)) t₁ t₂` is `[t₂ = s] C_{t₁} − [t₁ = s] C_{t₂}`, the value at `q` of
`annihRowPoly u v t₁ t₂ s = [t₂ = s] panelSupportPoly u v t₁ − [t₁ = s] panelSupportPoly u v t₂`
(`annihRowPoly_eval`), of degree at most two (`annihRowPoly_totalDegree_le`). -/
noncomputable def annihRowPoly {α : Type*} (u v : α)
    (t₁ t₂ s : Set.powersetCard (Fin (k + 2)) k) : MvPolynomial (α × Fin (k + 2)) K :=
  (if t₂ = s then panelSupportPoly u v t₁ else 0)
    - (if t₁ = s then panelSupportPoly u v t₂ else 0)

/-- **The value of `annihRowPoly`** (`lem:rows-polynomial-in-normals`): at the normals `q`, it is
the coordinate at `screwBasis k s` of the form `annihRow C(q (u, ·), q (v, ·)) t₁ t₂`
(`panelSupportPoly_eval`). -/
theorem annihRowPoly_eval {α : Type*} (u v : α) (q : α × Fin (k + 2) → K)
    (t₁ t₂ s : Set.powersetCard (Fin (k + 2)) k) :
    MvPolynomial.eval q (annihRowPoly u v t₁ t₂ s) =
      annihRow (panelSupportExtensor (fun i => q (u, i)) (fun i => q (v, i))) t₁ t₂
        (screwBasis k s) := by
  rw [annihRowPoly, annihRow_apply, map_sub,
    Module.Basis.repr_self_apply (screwBasis k) (i := s) t₂,
    Module.Basis.repr_self_apply (screwBasis k) (i := s) t₁,
    apply_ite (MvPolynomial.eval q), apply_ite (MvPolynomial.eval q),
    map_zero, panelSupportPoly_eval, panelSupportPoly_eval, mul_ite, mul_one, mul_zero,
    mul_ite, mul_one, mul_zero, ← screwBasis_repr_apply, ← screwBasis_repr_apply]
  congr 1
  · rcases eq_or_ne t₂ s with h | h
    · rw [ite_eq_left h, ite_eq_left h.symm]
    · rw [ite_eq_right h, ite_eq_right fun h' => h h'.symm]
  · rcases eq_or_ne t₁ s with h | h
    · rw [ite_eq_left h, ite_eq_left h.symm]
    · rw [ite_eq_right h, ite_eq_right fun h' => h h'.symm]

/-- **`annihRowPoly` has degree at most two** (`lem:rows-polynomial-in-normals`): each branch is
`panelSupportPoly`, of degree at most two (`panelSupportPoly_totalDegree_le`), or `0`. No
declaration uses it. -/
theorem annihRowPoly_totalDegree_le {α : Type*} (u v : α)
    (t₁ t₂ s : Set.powersetCard (Fin (k + 2)) k) :
    (annihRowPoly (K := K) u v t₁ t₂ s).totalDegree ≤ 2 := by
  refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_) <;>
    · split
      · exact panelSupportPoly_totalDegree_le u v _
      · rw [MvPolynomial.totalDegree_zero]; omega

end CombinatorialRigidity.Molecular
