/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Polygon
public import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.Lines
public import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.Cut

/-!
# Two stars, the insertion and the kernel curve, in every dimension

The linear algebra of the open ears with four or more interior bodies in
`blueprint/src/chapter/pencil-d.tex`, `sec:pencil-d-short`: the four nodes `lem:pencil-d-two-stars`,
`lem:pencil-d-insertion`, `lem:pencil-d-kernel-curve` and `lem:pencil-d-stars-four`, in dimension
`d = k + 1`, on `V = Fin (k + 2) → K` with `D = screwDim k`. The arguments are those of the
SHORT-CORE workbook (`notes/attacks/short-core/workbook.md`), S1, S6, S19, S22 and S35, as the
chapter cites them.

The *star* of `y` is `starGrade y`, the span of the joins `normalsJoin y u`: the lines through `y`.
An annihilator is a `Submodule.dualAnnihilator` in `Module.Dual K (⋀[K]^2 V)`, the forms on `⋀²`,
as in the chapter, whose section reads them through its perfect pairing of `⋀²` with `⋀^(d-1)`. No
exterior power past `⋀²` is used. The *radical* of a form `φ` on `⋀² V` is the set of `x` with
`φ (x ∧ u) = 0` for every `u`.

* `starGrade`, `starGrade_sup_starGrade_eq_ker`, `finrank_starGrade_sup_starGrade`,
  `dualAnnihilator_starGrade_sup_starGrade`, `mem_dualAnnihilator_starGrade_sup_starGrade_iff`,
  `dualMap_exteriorPower_map_mkQ_injective`, `finrank_add_two_le_of_forall_ιMulti_eq_zero`:
  `lem:pencil-d-two-stars`. (1) Two stars sum to the kernel of `⋀²` of the quotient map by
  `⟨y, y'⟩`, of dimension `2d - 1`; (2) their annihilator is the forms through that map, those with
  `y` and `y'` in their radical; (3) the pullback is injective, and a nonzero form on `⋀² V` whose
  radical holds `A` has `dim A + 2 ≤ dim V`. `starGrade_smul`: the star of a nonzero multiple is the
  same, for the scale invariance of the stars condition (`Grade/Short.lean`).
* `exists_insertion_of_starGrade_sup`: `lem:pencil-d-insertion`, `MainComponent/Lines.lean`'s
  `exists_insertion_gain` and `exists_insertion_of_star_sup_star` at every grade.
* `exists_mvPolynomial_kernel_curve`: `lem:pencil-d-kernel-curve`, its parameters a subspace `L` of
  `σ → K`. `exists_mvPolynomial_dual_kernel_curve` reads it on the forms killing a family.
* `exists_mvPolynomial_starsFour`: `lem:pencil-d-stars-four`, on the family `starsFamily`, with the
  first-order argument `eq_zero_of_starsFour_firstOrder`. The family, at two interior points, also
  serves `lem:pencil-d-stars-three` (`Grade/StarsThree.lean`).
* `not_starGrade_sup_le_of_finrank_le_two`: a step of `thm:pencil-d-open-ear-three`
  (`Grade/ShortThree.lean`). At independent points, `ρ` of dimension at most `2` and the three
  joins of the ear do not span both stars once `d ≥ 4`.

Helpers whose homes are other files, moved with the next commit that edits those files
(`notes/Phase42h.md` *Hand-off*): `pathVertex_zero_single` may stay. The `normalsJoin`
lemmas this file used are in `AlgebraicInduction/PanelLayer.lean`.
-/

@[expose] public section

namespace CombinatorialRigidity.Molecular

open scoped Matrix

variable {K : Type*} [Field K] {k : ℕ}

/-! ## The star of a point and two stars (`lem:pencil-d-two-stars`) -/

/-- The star of `y` (`lem:pencil-d-two-stars`, the section's `star(y)`): the span of the joins
`y ∨ u`, `u ∈ K^(k+2)`, the lines through `y`. -/
noncomputable def starGrade (y : Fin (k + 2) → K) : Submodule K (⋀[K]^2 (Fin (k + 2) → K)) :=
  Submodule.span K (Set.range (normalsJoin y))

/-- A join `y ∨ u` lies in the star of `y`. -/
theorem normalsJoin_mem_starGrade (y u : Fin (k + 2) → K) : normalsJoin y u ∈ starGrade y :=
  Submodule.subset_span ⟨u, rfl⟩

/-- The star of a point is that of any nonzero multiple: `c • y ∨ u = c • (y ∨ u)`, and a span is
unchanged by a unit scalar (`Submodule.span_smul_eq_of_isUnit`). -/
theorem starGrade_smul {c : K} (hc : c ≠ 0) (y : Fin (k + 2) → K) :
    starGrade (c • y) = starGrade y := by
  have h : normalsJoin (c • y) = fun u => c • normalsJoin y u :=
    funext fun u => normalsJoin_smul_left c y u
  rw [starGrade, starGrade, h, ← Set.smul_set_range]
  exact Submodule.span_smul_eq_of_isUnit _ _ hc.isUnit

/-- `lem:pencil-d-two-stars`, part (1), the kernel. For any `y`, `y'`, the sum of their stars is
the kernel of `⋀²` of the quotient map `K^(k+2) → K^(k+2) ⧸ ⟨y, y'⟩`. The stars lie in it, as
`ȳ ∧ ū = 0`. Conversely let `P = s ∘ mkQ` for a linear section `s` of the quotient map. Then
`a ∨ b - P a ∨ P b = (a - P a) ∨ b - (b - P b) ∨ P a`, and `a - P a`, `b - P b ∈ ⟨y, y'⟩`, so every
`ω` is `⋀²P ω` modulo the sum of the stars, and `⋀²P ω = ⋀²s (⋀²mkQ ω)` vanishes on the kernel. The
chapter argues with a basis extending `y`, `y'` instead (`notes/Cleanup42.md`, R-11). -/
theorem starGrade_sup_starGrade_eq_ker (y y' : Fin (k + 2) → K) :
    starGrade y ⊔ starGrade y' =
      LinearMap.ker (exteriorPower.map 2 (Submodule.span K {y, y'}).mkQ) := by
  set N := Submodule.span K {y, y'} with hNdef
  have hN : ∀ n ∈ N, ∀ v, normalsJoin n v ∈ starGrade y ⊔ starGrade y' := by
    intro n hn v
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hn
    rw [normalsJoin_add_left, normalsJoin_smul_left, normalsJoin_smul_left]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.mem_sup_left (normalsJoin_mem_starGrade _ _)))
      (Submodule.smul_mem _ _ (Submodule.mem_sup_right (normalsJoin_mem_starGrade _ _)))
  have hker : ∀ n ∈ N, ∀ u, normalsJoin n u ∈
      LinearMap.ker (exteriorPower.map 2 N.mkQ) := by
    intro n hn u
    rw [LinearMap.mem_ker, normalsJoin, exteriorPower.map_apply_ιMulti]
    exact (exteriorPower.ιMulti K 2).map_coord_zero 0
      (by simpa [Submodule.Quotient.mk_eq_zero] using hn)
  refine le_antisymm (sup_le ?_ ?_) ?_
  · rw [starGrade, Submodule.span_le]; rintro _ ⟨u, rfl⟩
    exact hker y (Submodule.subset_span (by simp)) u
  · rw [starGrade, Submodule.span_le]; rintro _ ⟨u, rfl⟩
    exact hker y' (Submodule.subset_span (by simp)) u
  · obtain ⟨s, hs⟩ := (N.mkQ).exists_rightInverse_of_surjective N.range_mkQ
    set P := s ∘ₗ N.mkQ with hP
    have hsub : ∀ u, u - P u ∈ N := fun u => by
      rw [← Submodule.ker_mkQ N, LinearMap.mem_ker, map_sub, hP, LinearMap.comp_apply,
        ← LinearMap.comp_apply N.mkQ s, hs, LinearMap.id_apply, sub_self]
    have hL : ∀ ω, ω - exteriorPower.map 2 P ω ∈ starGrade y ⊔ starGrade y' := by
      intro ω
      have hω : ω ∈ Submodule.span K (Set.range (exteriorPower.ιMulti K 2)) := by
        rw [exteriorPower.ιMulti_span]; trivial
      induction hω using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨v, rfl⟩ := hx
        have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
        rw [hv, ιMulti_pair_eq_normalsJoin, exteriorPower_map_normalsJoin]
        have : normalsJoin (v 0) (v 1) - normalsJoin (P (v 0)) (P (v 1)) =
            normalsJoin (v 0 - P (v 0)) (v 1) - normalsJoin (v 1 - P (v 1)) (P (v 0)) := by
          rw [normalsJoin_sub_left, normalsJoin_sub_left, normalsJoin_swap (v 1) (P (v 0)),
            normalsJoin_swap (P (v 1)) (P (v 0))]
          abel
        rw [this]
        exact sub_mem (hN _ (hsub _) _) (hN _ (hsub _) _)
      | zero => simp
      | add x x' _ _ hx hx' =>
        convert add_mem hx hx' using 1; rw [map_add]; abel
      | smul a x _ hx =>
        convert Submodule.smul_mem _ a hx using 1; rw [map_smul, smul_sub]
    intro ω hω
    have h0 : exteriorPower.map 2 P ω = 0 := by
      rw [hP, exteriorPower.map_comp, LinearMap.comp_apply, LinearMap.mem_ker.mp hω, map_zero]
    simpa [h0] using hL ω

/-- `lem:pencil-d-two-stars`, part (1), the dimension. For linearly independent `y`, `y'`, the sum
of their stars has dimension `2d - 1 = 2k + 1`, and codimension `binom(d - 1, 2) = k.choose 2` in
`⋀²`, of dimension `D = screwDim k`. By rank–nullity: the sum is the kernel of `⋀²` of the quotient
map (`starGrade_sup_starGrade_eq_ker`), which is onto `⋀²` of a quotient of dimension `k`. -/
theorem finrank_starGrade_sup_starGrade {y y' : Fin (k + 2) → K}
    (hy : LinearIndependent K ![y, y']) :
    Module.finrank K ↥(starGrade y ⊔ starGrade y') = 2 * k + 1 ∧
      Module.finrank K ↥(starGrade y ⊔ starGrade y') + k.choose 2 = screwDim k := by
  set N := Submodule.span K {y, y'} with hNdef
  have hN : Module.finrank K N = 2 := by
    have := finrank_span_eq_card hy
    rwa [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union, Fintype.card_fin] at this
  have hQ : Module.finrank K ((Fin (k + 2) → K) ⧸ N) = k := by
    have := Submodule.finrank_quotient_add_finrank N
    rw [Module.finrank_fin_fun, hN] at this; omega
  have hrn := LinearMap.finrank_range_add_finrank_ker (exteriorPower.map 2 N.mkQ)
  rw [LinearMap.range_eq_top.mpr (exteriorPower.map_surjective N.mkQ_surjective), finrank_top,
    exteriorPower.finrank_eq, hQ, ← starGrade_sup_starGrade_eq_ker,
    finrank_exteriorPower_two_eq_screwDim] at hrn
  have hD : screwDim k = (k + 2).choose 2 := by
    rw [← finrank_exteriorPower_two_eq_screwDim (K := K), exteriorPower.finrank_eq,
      Module.finrank_fin_fun]
  have hc : (k + 2).choose 2 = 2 * k + 1 + k.choose 2 := by
    simp [Nat.choose_succ_succ', Nat.choose_one_right]; omega
  omega

/-- `lem:pencil-d-two-stars`, part (2). The annihilator of the sum of two stars, among the forms on
`⋀²`, is the set of forms that factor through `⋀²` of the quotient map by `⟨y, y'⟩`: the range of
that map's dual, as the sum is its kernel (`starGrade_sup_starGrade_eq_ker`). -/
theorem dualAnnihilator_starGrade_sup_starGrade (y y' : Fin (k + 2) → K) :
    (starGrade y ⊔ starGrade y').dualAnnihilator =
      LinearMap.range (exteriorPower.map 2 (Submodule.span K {y, y'}).mkQ).dualMap := by
  rw [starGrade_sup_starGrade_eq_ker, LinearMap.range_dualMap_eq_dualAnnihilator_ker]

/-- `lem:pencil-d-two-stars`, part (2), as membership. A form `φ` on `⋀²` annihilates the sum of
the stars of `y` and `y'` iff both lie in its radical: `φ (y ∨ u) = φ (y' ∨ u) = 0` for every `u`.
The joins `y ∨ u` and `y' ∨ u` span the sum. -/
theorem mem_dualAnnihilator_starGrade_sup_starGrade_iff {y y' : Fin (k + 2) → K}
    {φ : Module.Dual K (⋀[K]^2 (Fin (k + 2) → K))} :
    φ ∈ (starGrade y ⊔ starGrade y').dualAnnihilator ↔
      ∀ u, φ (normalsJoin y u) = 0 ∧ φ (normalsJoin y' u) = 0 := by
  rw [Submodule.mem_dualAnnihilator]
  refine ⟨fun h u => ⟨h _ (Submodule.mem_sup_left (normalsJoin_mem_starGrade _ _)),
    h _ (Submodule.mem_sup_right (normalsJoin_mem_starGrade _ _))⟩, fun h w hw => ?_⟩
  have hle : starGrade y ⊔ starGrade y' ≤ LinearMap.ker φ := by
    refine sup_le (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_) <;>
      rintro _ ⟨u, rfl⟩
    exacts [(h u).1, (h u).2]
  exact hle hw

/-- `lem:pencil-d-two-stars`, part (3), the pullback. The map `φ ↦ φ ∘ ⋀²mkQ` from the forms on
`⋀²` of the quotient by `⟨y, y'⟩` to the forms on `⋀² K^(k+2)` is injective, as `⋀²mkQ` is onto. -/
theorem dualMap_exteriorPower_map_mkQ_injective (y y' : Fin (k + 2) → K) :
    Function.Injective (exteriorPower.map 2 (Submodule.span K {y, y'}).mkQ).dualMap :=
  LinearMap.dualMap_injective_of_surjective
    (exteriorPower.map_surjective (Submodule.mkQ_surjective _))

/-- A form on `⋀² V` that vanishes at every product `u ∧ w` is zero: the products span `⋀² V`. -/
theorem eq_zero_of_forall_ιMulti_two_eq_zero {V : Type*} [AddCommGroup V] [Module K V]
    {φ : Module.Dual K (⋀[K]^2 V)} (h : ∀ u w, φ (exteriorPower.ιMulti K 2 ![u, w]) = 0) :
    φ = 0 := by
  refine exteriorPower.linearMap_ext ?_
  ext v
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  rw [LinearMap.compAlternatingMap_apply, hv]
  exact h _ _

/-- `lem:pencil-d-two-stars`, part (3), the bound, on any finite-dimensional `V`. A nonzero form
`φ` on `⋀² V` whose radical holds the subspace `A` (`φ (x ∧ u) = 0` for `x ∈ A` and every `u`) has
`dim A + 2 ≤ dim V`. Some `φ (u ∧ w)` is nonzero (`eq_zero_of_forall_ιMulti_two_eq_zero`). Then
`u ∉ A`, and `w ∉ A + K u`, as `φ (u ∧ (a + c u)) = -φ (a ∧ u) = 0` for `a ∈ A`. -/
theorem finrank_add_two_le_of_forall_ιMulti_eq_zero {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {φ : Module.Dual K (⋀[K]^2 V)} (hφ : φ ≠ 0) {A : Submodule K V}
    (hA : ∀ x ∈ A, ∀ u, φ (exteriorPower.ιMulti K 2 ![x, u]) = 0) :
    Module.finrank K A + 2 ≤ Module.finrank K V := by
  set f := φ.compAlternatingMap (exteriorPower.ιMulti K 2) with hf
  have hfv : ∀ u w, f ![u, w] = φ (exteriorPower.ιMulti K 2 ![u, w]) := fun _ _ => rfl
  obtain ⟨u, w, huw⟩ : ∃ u w, f ![u, w] ≠ 0 := by
    by_contra! h
    exact hφ (eq_zero_of_forall_ιMulti_two_eq_zero h)
  have hswap : ∀ a b, f ![a, b] = - f ![b, a] := fun a b => by
    rw [eq_neg_iff_add_eq_zero]
    have := f.map_add_swap (v := ![a, b]) (i := 0) (j := 1) (by decide)
    have e : ![a, b] ∘ Equiv.swap 0 1 = ![b, a] := by funext i; fin_cases i <;> rfl
    rwa [e] at this
  have hself : ∀ a, f ![a, a] = 0 := fun a => f.map_eq_zero_of_eq ![a, a] (i := 0) (j := 1) rfl
    (by decide)
  have huA : u ∉ A := fun h => huw (by rw [hfv]; exact hA u h w)
  have hwA : w ∉ A ⊔ K ∙ u := by
    intro h
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp h
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
    refine huw ?_
    rw [hswap, AlternatingMap.map_vecCons_add, AlternatingMap.map_vecCons_smul, hself, smul_zero,
      add_zero, hfv, hA a ha u, neg_zero]
  have h1 := Submodule.finrank_sup_span_singleton huA
  have h2 := Submodule.finrank_sup_span_singleton hwA
  have h3 := Submodule.finrank_le (A ⊔ K ∙ u ⊔ K ∙ w)
  omega

/-! ## Putting a body back next to a neighbour (`lem:pencil-d-insertion`) -/

/-- A step of `lem:pencil-d-insertion`: if `y` has last coordinate `1` and its star is not in `W`,
some `u` with last coordinate `0` has `y ∨ u ∉ W`, as `y ∨ v = y ∨ (v - v_last • y)`. -/
theorem exists_notMem_normalsJoin_of_not_starGrade_le {y : Fin (k + 2) → K}
    (hy : y (Fin.last (k + 1)) = 1) {W : Submodule K (⋀[K]^2 (Fin (k + 2) → K))}
    (h : ¬ starGrade y ≤ W) :
    ∃ u : Fin (k + 2) → K, u (Fin.last (k + 1)) = 0 ∧ normalsJoin y u ∉ W := by
  rw [starGrade, Submodule.span_le] at h
  obtain ⟨_, ⟨v, rfl⟩, hv⟩ := Set.not_subset.mp h
  refine ⟨v + (-v (Fin.last (k + 1))) • y, by simp [hy], ?_⟩
  rwa [normalsJoin_add_right, normalsJoin_smul_right, normalsJoin_self, smul_zero, add_zero]

/-- The gain in `lem:pencil-d-insertion`'s proof: the proof of `lem:pencil-insertion`
(`exists_insertion_gain`) at every grade, with `R` for `ρ + span F`. If
`y ∨ u ∉ W = R + K (y ∨ y')` over an infinite field, some `t ≠ 0` has
`dim (R + span (y ∨ (y + t u), (y + t u) ∨ y')) ≥ dim W + 1`. That span holds `R`, `y ∨ u` and
`(y + t u) ∨ y'`. If `y ∨ y' ∈ R`, `t = 1` will do; otherwise `y ∨ y' ∉ R + K (y ∨ u)`, and the
line `y ∨ y' + t (u ∨ y')` leaves `R + K (y ∨ u)` at some `t ≠ 0`
(`exists_ne_zero_add_smul_notMem`). -/
theorem exists_insertion_gain_grade [Infinite K] (R : Submodule K (⋀[K]^2 (Fin (k + 2) → K)))
    (y y' u : Fin (k + 2) → K) (hu : normalsJoin y u ∉ R ⊔ K ∙ normalsJoin y y') :
    ∃ t : K, t ≠ 0 ∧ Module.finrank K ↥(R ⊔ K ∙ normalsJoin y y') + 1 ≤
      Module.finrank K ↥(R ⊔ Submodule.span K
        {normalsJoin y (y + t • u), normalsJoin (y + t • u) y'}) := by
  have hle : ∀ t : K, t ≠ 0 → R ⊔ K ∙ normalsJoin y u ⊔ K ∙ normalsJoin (y + t • u) y' ≤
      R ⊔ Submodule.span K {normalsJoin y (y + t • u), normalsJoin (y + t • u) y'} := by
    intro t ht
    refine sup_le (sup_le le_sup_left ?_) ?_ <;> rw [Submodule.span_singleton_le_iff_mem] <;>
      refine Submodule.mem_sup_right ?_
    · have hyu : normalsJoin y (y + t • u) = t • normalsJoin y u := by
        rw [normalsJoin_add_right, normalsJoin_self, zero_add, normalsJoin_smul_right]
      rw [← inv_smul_smul₀ ht (normalsJoin y u), ← hyu]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _))
    · exact Submodule.subset_span (by simp)
  have huR : normalsJoin y u ∉ R := fun h => hu (Submodule.mem_sup_left h)
  by_cases hR : normalsJoin y y' ∈ R
  · refine ⟨1, one_ne_zero, ?_⟩
    rw [sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem _ _).mpr hR),
      ← Submodule.finrank_sup_span_singleton huR]
    exact Submodule.finrank_mono (le_sup_left.trans (hle 1 one_ne_zero))
  · have hS : normalsJoin y y' ∉ R ⊔ K ∙ normalsJoin y u := by
      intro h
      obtain ⟨r, hr, s, hs, hrs⟩ := Submodule.mem_sup.mp h
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hs
      have hc : c ≠ 0 := by rintro rfl; exact hR (by simpa [← hrs] using hr)
      refine hu ?_
      rw [show normalsJoin y u = c⁻¹ • (normalsJoin y y' - r) by
        rw [← hrs, add_sub_cancel_left, inv_smul_smul₀ hc]]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _
        (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)) (Submodule.mem_sup_left hr))
    obtain ⟨t, ht, hnot⟩ := exists_ne_zero_add_smul_notMem hS (normalsJoin u y')
    rw [← normalsJoin_smul_left, ← normalsJoin_add_left] at hnot
    refine ⟨t, ht, ?_⟩
    rw [Submodule.finrank_sup_span_singleton hR, ← Submodule.finrank_sup_span_singleton huR,
      ← Submodule.finrank_sup_span_singleton hnot]
    exact Submodule.finrank_mono (hle t ht)

/-- `lem:pencil-d-insertion` (SHORT-CORE workbook, S19 (c)). Over an infinite field, let `y₁`, `y₃`
have last coordinate `1`, and `W = R + K (y₁ ∨ y₃)`. If `W` holds both stars only when `W = ⋀²`,
some `x₂` with last coordinate `1` has `dim (R + span (y₁ ∨ x₂, x₂ ∨ y₃)) ≥ min (dim W + 1) D`.
When both stars lie in `W`, `W = ⋀²` and `x₂ = y₁` will do. Otherwise some `y ∨ u ∉ W`, with `y`
one of the two points and `u` of last coordinate `0`
(`exists_notMem_normalsJoin_of_not_starGrade_le`), and `x₂ = y + t u` by
`exists_insertion_gain_grade`, the roles of `y₁`, `y₃` exchanged up to sign when `y = y₃`. -/
theorem exists_insertion_of_starGrade_sup [Infinite K] (R : Submodule K (⋀[K]^2 (Fin (k + 2) → K)))
    (y₁ y₃ : Fin (k + 2) → K) (hy₁ : y₁ (Fin.last (k + 1)) = 1) (hy₃ : y₃ (Fin.last (k + 1)) = 1)
    (hG : starGrade y₁ ⊔ starGrade y₃ ≤ R ⊔ K ∙ normalsJoin y₁ y₃ →
      R ⊔ K ∙ normalsJoin y₁ y₃ = ⊤) :
    ∃ x₂ : Fin (k + 2) → K, x₂ (Fin.last (k + 1)) = 1 ∧
      min (Module.finrank K ↥(R ⊔ K ∙ normalsJoin y₁ y₃) + 1) (screwDim k) ≤
      Module.finrank K ↥(R ⊔ Submodule.span K {normalsJoin y₁ x₂, normalsJoin x₂ y₃}) := by
  by_cases hs1 : starGrade y₁ ≤ R ⊔ K ∙ normalsJoin y₁ y₃
  · by_cases hs3 : starGrade y₃ ≤ R ⊔ K ∙ normalsJoin y₁ y₃
    · refine ⟨y₁, hy₁, (min_le_right _ _).trans ?_⟩
      rw [← finrank_exteriorPower_two_eq_screwDim (K := K), ← finrank_top K,
        ← hG (sup_le hs1 hs3)]
      refine Submodule.finrank_mono (sup_le_sup_left ?_ _)
      rw [Submodule.span_singleton_le_iff_mem]
      exact Submodule.subset_span (by simp)
    · have hW : R ⊔ K ∙ normalsJoin y₁ y₃ = R ⊔ K ∙ normalsJoin y₃ y₁ := by
        rw [normalsJoin_swap y₁ y₃, ← Set.neg_singleton, Submodule.span_neg]
      obtain ⟨u, hu3, hu⟩ := exists_notMem_normalsJoin_of_not_starGrade_le hy₃ hs3
      obtain ⟨t, -, ht⟩ := exists_insertion_gain_grade R y₃ y₁ u (hW ▸ hu)
      refine ⟨y₃ + t • u, by simp [hy₃, hu3], (min_le_left _ _).trans ?_⟩
      rwa [hW, normalsJoin_swap (y₃ + t • u) y₁, normalsJoin_swap y₃, ← Set.neg_singleton,
        ← Set.neg_insert, Submodule.span_neg, Set.pair_comm]
  · obtain ⟨u, hu3, hu⟩ := exists_notMem_normalsJoin_of_not_starGrade_le hy₁ hs1
    obtain ⟨t, -, ht⟩ := exists_insertion_gain_grade R y₁ y₃ u hu
    exact ⟨y₁ + t • u, by simp [hy₁, hu3], (min_le_left _ _).trans ht⟩

/-! ## A kernel vector to first order along a line (`lem:pencil-d-kernel-curve`) -/

/-- Rank is open (a step of `lem:pencil-d-kernel-curve`): for a family `G s` whose coordinates in a
basis `b` are polynomials in `s`, if `N ≤ dim span (G s₀)`, some polynomial `Q` with `Q s₀ ≠ 0` has
`N ≤ dim span (G s)` wherever `Q s ≠ 0`. Take `N` members independent at `s₀`; they stay
independent off the zero set of one of their minors
(`exists_polynomial_ne_zero_of_linearIndependent_at_reindex`). -/
theorem exists_mvPolynomial_le_finrank_span_of_repr {σ ι κ E : Type*} [Finite κ]
    [AddCommGroup E] [Module K E] (b : Module.Basis κ K E) (G : (σ → K) → ι → E)
    (c : ι → κ → MvPolynomial σ K)
    (hc : ∀ s i j, b.repr (G s i) j = MvPolynomial.eval s (c i j))
    {s₀ : σ → K} {N : ℕ} (hN : N ≤ Module.finrank K (Submodule.span K (Set.range (G s₀)))) :
    ∃ Q : MvPolynomial σ K, MvPolynomial.eval s₀ Q ≠ 0 ∧ ∀ s, MvPolynomial.eval s Q ≠ 0 →
      N ≤ Module.finrank K (Submodule.span K (Set.range (G s))) := by
  classical
  have : Fintype κ := Fintype.ofFinite κ
  have : Module.Finite K E := Module.Finite.of_basis b
  obtain ⟨f, hfmem, -, hfli⟩ := Submodule.exists_fun_fin_finrank_span_eq K (Set.range (G s₀))
  choose idx hidx using hfmem
  set j : Fin N → ι := fun i => idx (Fin.castLE hN i) with hj
  have hli₀ : LinearIndependent K (fun i : (Set.univ : Set (Fin N)) => G s₀ (j i)) := by
    have : (fun i : (Set.univ : Set (Fin N)) => G s₀ (j i)) =
        f ∘ Fin.castLE hN ∘ Subtype.val := by
      funext i; simp [hj, hidx]
    rw [this]
    exact (hfli.comp _ (Fin.castLE_injective hN)).comp _ Subtype.val_injective
  set e : Fin (Module.finrank K E) ≃ κ :=
    (finCongr (Module.finrank_eq_card_basis b)).trans (Fintype.equivFin κ).symm with he
  obtain ⟨Q, hQ₀, hQ⟩ := exists_polynomial_ne_zero_of_linearIndependent_at_reindex
    (W := E) e (fun s i => G s (j i)) (fun i => c (j i)) b.equivFun
    (fun s i t => by rw [b.equivFun_apply]; exact hc s (j i) t) hli₀
  refine ⟨Q, hQ₀, fun s hs => ?_⟩
  have hli := (hQ s hs).comp (fun i => (⟨i, trivial⟩ : (Set.univ : Set (Fin N))))
    (fun _ _ h => congrArg Subtype.val h)
  calc N = Fintype.card (Fin N) := (Fintype.card_fin N).symm
    _ = Module.finrank K (Submodule.span K (Set.range (fun i => G s (j i)))) :=
        (finrank_span_eq_card hli).symm
    _ ≤ _ := Submodule.finrank_mono (Submodule.span_mono (by
        rintro _ ⟨i, rfl⟩; exact ⟨_, rfl⟩))

open Polynomial in
/-- The first-order step of `lem:pencil-d-kernel-curve`. Over an infinite field, if
no matrix `A + t Mw + t² M₂(t)` has rank above that of `A`, every `ξ₀` with `A ξ₀ = 0` has `ξ₁`
with `A ξ₁ + Mw ξ₀ = 0`. Otherwise `Mw ξ₀ ∉ range A`, so vectors `A u_j` forming a basis of
`range A`, with `Mw ξ₀`, are independent; the family `(A + t Mw + t² M₂(t)) u_j`,
`Mw ξ₀ + t M₂(t) ξ₀`, which is that one at `t = 0`, stays independent at some `t ≠ 0`
(`LinearIndependent.exists_notMem_of_polynomial_repr`). It lies in the range of
`A + t Mw + t² M₂(t)`, which sends `t⁻¹ ξ₀` to `Mw ξ₀ + t M₂(t) ξ₀`, so that rank is above
`rank A`. -/
theorem exists_mulVec_add_mulVec_eq_zero [Infinite K] {ι κ : Type*} [Finite ι] [Fintype κ]
    (A Mw : Matrix ι κ K) (M₂ : Matrix ι κ K[X])
    (hrank : ∀ t : K, (A + t • Mw + t ^ 2 • M₂.map (Polynomial.eval t)).rank ≤ A.rank)
    {ξ₀ : κ → K} (hξ₀ : A *ᵥ ξ₀ = 0) : ∃ ξ₁, A *ᵥ ξ₁ + Mw *ᵥ ξ₀ = 0 := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  by_contra hno
  set R := LinearMap.range A.mulVecLin with hR
  have hnot : Mw *ᵥ ξ₀ ∉ R := by
    rintro ⟨ξ, hξ⟩
    rw [Matrix.mulVecLin_apply] at hξ
    exact hno ⟨-ξ, by rw [Matrix.mulVec_neg, hξ, neg_add_cancel]⟩
  set bR := Module.finBasis K R with hbR
  have hu : ∀ j, ∃ u, A *ᵥ u = (bR j : ι → K) := fun j => by
    obtain ⟨u, hu⟩ := (bR j).2; exact ⟨u, hu⟩
  choose u hu using hu
  set Mt : K → Matrix ι κ K := fun t => A + t • Mw + t ^ 2 • M₂.map (Polynomial.eval t)
    with hMt
  set g : K → Option (Fin (Module.finrank K R)) → ι → K := fun t o =>
    Option.casesOn' o (Mw *ᵥ ξ₀ + t • (M₂.map (Polynomial.eval t) *ᵥ ξ₀))
      (fun j => Mt t *ᵥ u j) with hg
  set P : Option (Fin (Module.finrank K R)) → ι → K[X] := fun o i =>
    Option.casesOn' o (C ((Mw *ᵥ ξ₀) i) + X * (M₂ *ᵥ (fun j => C (ξ₀ j))) i)
      (fun j => C ((A *ᵥ u j) i) + X * C ((Mw *ᵥ u j) i) +
        X ^ 2 * (M₂ *ᵥ (fun l => C (u j l))) i) with hP
  have hev : ∀ t (v : κ → K) i, (M₂.map (Polynomial.eval t) *ᵥ v) i =
      ((M₂ *ᵥ (fun l => C (v l))) i).eval t := by
    intro t v i
    simp [Matrix.mulVec, dotProduct, Polynomial.eval_finsetSum]
  have hgP : ∀ t o i, (Pi.basisFun K ι).repr (g t o) i = (P o i).eval t := by
    intro t o i
    rcases o with _ | j
    · simp [hg, hP, hev]
    · simp [hg, hP, hMt, Matrix.add_mulVec, Matrix.smul_mulVec, hev]
      ring
  have h0 : LinearIndependent K (g 0) := by
    have hg0 : g 0 = fun o => Option.casesOn' o (Mw *ᵥ ξ₀) (fun j => (bR j : ι → K)) := by
      funext o; rcases o with _ | j
      · simp [hg]
      · simp [hg, hMt, hu]
    rw [hg0, linearIndependent_option']
    have hspan : Submodule.span K (Set.range fun j => (bR j : ι → K)) = R := by
      have := congrArg (Submodule.map R.subtype) bR.span_eq
      rwa [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp] at this
    exact ⟨bR.linearIndependent.map' R.subtype (Submodule.ker_subtype R), by rw [hspan]; exact hnot⟩
  obtain ⟨t, -, ht0, hli⟩ :=
    LinearIndependent.exists_notMem_of_polynomial_repr (Pi.basisFun K ι) g P hgP h0 ∅
  have hle : Submodule.span K (Set.range (g t)) ≤ LinearMap.range (Mt t).mulVecLin := by
    rw [Submodule.span_le]; rintro _ ⟨o, rfl⟩
    rcases o with _ | j
    · refine ⟨t⁻¹ • ξ₀, ?_⟩
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_smul, hMt, Matrix.add_mulVec, hξ₀,
        Matrix.smul_mulVec, zero_add, hg, Option.casesOn'_none]
      rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ ht0, one_smul, sq, ← mul_assoc,
        inv_mul_cancel₀ ht0, one_mul]
    · exact ⟨u j, rfl⟩
  have hcard := finrank_span_eq_card hli
  rw [Fintype.card_option, Fintype.card_fin] at hcard
  have h1 := Submodule.finrank_mono hle
  have h2 : Module.finrank K (LinearMap.range (Mt t).mulVecLin) ≤ Module.finrank K R := hrank t
  omega

/-- `lem:pencil-d-kernel-curve` (SHORT-CORE workbook, S6 and S35), with the parameters a subspace
`L` of `σ → K` and the entries of `M` polynomials in the coordinates `σ`. Over an infinite field,
some `μ`, nonzero at a point of `L`, has at every `y₀ ∈ L` with `μ y₀ ≠ 0`: the kernel of `M(y₀)`
has the least dimension over `L`; and for `w ∈ L` with
`M(y₀ + t w) = M(y₀) + t Mw + t² M₂(t)` for every `t`, every `ξ₀` with `M(y₀) ξ₀ = 0` has `ξ₁` with
`M(y₀) ξ₁ + Mw ξ₀ = 0`. The generic rank is the greatest rank over `L` (`Nat.findGreatest`), `μ` a
minor of the rows keeping it (`exists_mvPolynomial_le_finrank_span_of_repr`), and the first-order
step is `exists_mulVec_add_mulVec_eq_zero`, as the line `y₀ + t w` stays in `L`. -/
theorem exists_mvPolynomial_kernel_curve [Infinite K] {σ ι κ : Type*} [Finite ι] [Fintype κ]
    (L : Submodule K (σ → K)) (M : Matrix ι κ (MvPolynomial σ K)) :
    ∃ μ : MvPolynomial σ K, (∃ y ∈ L, MvPolynomial.eval y μ ≠ 0) ∧
      ∀ y₀ ∈ L, MvPolynomial.eval y₀ μ ≠ 0 →
        (∀ y ∈ L, Module.finrank K (LinearMap.ker (M.map (MvPolynomial.eval y₀)).mulVecLin) ≤
          Module.finrank K (LinearMap.ker (M.map (MvPolynomial.eval y)).mulVecLin)) ∧
        ∀ w ∈ L, ∀ (Mw : Matrix ι κ K) (M₂ : Matrix ι κ (Polynomial K)),
          (∀ t : K, M.map (MvPolynomial.eval (y₀ + t • w)) =
            M.map (MvPolynomial.eval y₀) + t • Mw + t ^ 2 • M₂.map (Polynomial.eval t)) →
          ∀ ξ₀, M.map (MvPolynomial.eval y₀) *ᵥ ξ₀ = 0 →
            ∃ ξ₁, M.map (MvPolynomial.eval y₀) *ᵥ ξ₁ + Mw *ᵥ ξ₀ = 0 := by
  classical
  have hrk : ∀ B : Matrix ι κ K,
      B.rank + Module.finrank K (LinearMap.ker B.mulVecLin) = Fintype.card κ := fun B => by
    have := LinearMap.finrank_range_add_finrank_ker B.mulVecLin
    rwa [Module.finrank_fintype_fun_eq_card] at this
  set n := Nat.findGreatest (fun n => ∃ y ∈ L, n ≤ (M.map (MvPolynomial.eval y)).rank)
    (Fintype.card κ) with hn
  have hspec : ∃ y ∈ L, n ≤ (M.map (MvPolynomial.eval y)).rank :=
    Nat.findGreatest_spec (P := fun n => ∃ y ∈ L, n ≤ (M.map (MvPolynomial.eval y)).rank)
      (Nat.zero_le _) ⟨0, L.zero_mem, Nat.zero_le _⟩
  have hmax : ∀ y ∈ L, (M.map (MvPolynomial.eval y)).rank ≤ n := fun y hy =>
    Nat.le_findGreatest (Matrix.rank_le_card_width _) ⟨y, hy, le_rfl⟩
  obtain ⟨ys, hys, hns⟩ := hspec
  rw [Matrix.rank_eq_finrank_span_row] at hns
  obtain ⟨μ, hμ₀, hμ⟩ := exists_mvPolynomial_le_finrank_span_of_repr (Pi.basisFun K κ)
    (fun y => (M.map (MvPolynomial.eval y)).row) (fun i j => M i j) (fun _ _ _ => rfl) hns
  refine ⟨μ, ⟨ys, hys, hμ₀⟩, fun y₀ hy₀ hμy₀ => ?_⟩
  have hgen : n ≤ (M.map (MvPolynomial.eval y₀)).rank := by
    rw [Matrix.rank_eq_finrank_span_row]; exact hμ y₀ hμy₀
  refine ⟨fun y hy => ?_, fun w hw Mw M₂ hcurve ξ₀ hξ₀ => ?_⟩
  · have := hrk (M.map (MvPolynomial.eval y))
    have := hrk (M.map (MvPolynomial.eval y₀))
    have := hmax y hy
    omega
  · refine exists_mulVec_add_mulVec_eq_zero _ Mw M₂ (fun t => ?_) hξ₀
    rw [← hcurve t]
    exact (hmax _ (L.add_mem hy₀ (L.smul_mem t hw))).trans hgen

/-- The kernel curve read on forms (a step of `lem:pencil-d-stars-four`). Let `F y` be a family in
`E` whose coordinates in a basis `b` are polynomials `c` in `y`. Some `μ`, nonzero at a point of
`L`, has at every `y₀ ∈ L` with `μ y₀ ≠ 0`, for `w ∈ L` with
`F (y₀ + t w) = F y₀ + t F₁ + t² F₂` for every `t`: every form `φ₀` killing `F y₀` has a form `φ₁`
with `φ₁ (F y₀ i) + φ₀ (F₁ i) = 0` for each `i`. A form is the vector `ξ` of its values on `b`, and
the matrix of coordinates sends `ξ` to its values on the family; `μ` and `φ₁` come from
`exists_mvPolynomial_kernel_curve` for that matrix. -/
theorem exists_mvPolynomial_dual_kernel_curve [Infinite K] {σ ι κ E : Type*} [Finite ι]
    [Finite κ] [AddCommGroup E] [Module K E] (b : Module.Basis κ K E) (L : Submodule K (σ → K))
    (F : (σ → K) → ι → E) (c : ι → κ → MvPolynomial σ K)
    (hc : ∀ y i s, b.repr (F y i) s = MvPolynomial.eval y (c i s)) :
    ∃ μ : MvPolynomial σ K, (∃ y ∈ L, MvPolynomial.eval y μ ≠ 0) ∧
      ∀ y₀ ∈ L, MvPolynomial.eval y₀ μ ≠ 0 → ∀ w ∈ L, ∀ F₁ F₂ : ι → E,
        (∀ (t : K) i, F (y₀ + t • w) i = F y₀ i + t • F₁ i + t ^ 2 • F₂ i) →
        ∀ φ₀ : Module.Dual K E, (∀ i, φ₀ (F y₀ i) = 0) →
          ∃ φ₁ : Module.Dual K E, ∀ i, φ₁ (F y₀ i) + φ₀ (F₁ i) = 0 := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have : Fintype κ := Fintype.ofFinite κ
  obtain ⟨μ, hμ, hgen⟩ := exists_mvPolynomial_kernel_curve L (Matrix.of c)
  refine ⟨μ, hμ, fun y₀ hy₀ hμ₀ w hw F₁ F₂ hcurve φ₀ hφ₀ => ?_⟩
  -- a form `φ` is the vector `s ↦ φ (b s)`, and `φ v = ∑ s, b.repr v s * φ (b s)`
  have hφ : ∀ (φ : Module.Dual K E) v, φ v = ∑ s, b.repr v s * φ (b s) := by
    intro φ v
    conv_lhs => rw [← b.sum_repr v]
    rw [map_sum]; simp only [map_smul, smul_eq_mul]
  set Mw : Matrix ι κ K := Matrix.of fun i s => b.repr (F₁ i) s
  set M₂ : Matrix ι κ (Polynomial K) := Matrix.of fun i s => Polynomial.C (b.repr (F₂ i) s)
  have hN : ∀ y, (Matrix.of c).map (MvPolynomial.eval y) = Matrix.of fun i s => b.repr (F y i) s :=
    fun y => by ext i s; simp [hc]
  obtain ⟨ξ₁, hξ₁⟩ := (hgen y₀ hy₀ hμ₀).2 w hw Mw M₂ (fun t => by
      rw [hN, hN]; ext i s
      simp [Mw, M₂, hcurve t i]) (fun s => φ₀ (b s)) (by
      rw [hN]; funext i
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
      rw [← hφ, hφ₀])
  refine ⟨∑ s, ξ₁ s • b.coord s, fun i => ?_⟩
  have h := congrFun hξ₁ i
  rw [hN] at h
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.add_apply, Pi.zero_apply, Mw] at h
  rw [hφ φ₀ (F₁ i), ← h]
  simp [LinearMap.sum_apply, Module.Basis.coord_apply, mul_comm]

/-! ## A span containing two stars, at four or more interior bodies (`lem:pencil-d-stars-four`) -/

/-- A form on `⋀² K^(k+2)` that vanishes at every join is zero. -/
theorem eq_zero_of_forall_normalsJoin_eq_zero {φ : Module.Dual K (⋀[K]^2 (Fin (k + 2) → K))}
    (h : ∀ u w, φ (normalsJoin u w) = 0) : φ = 0 :=
  eq_zero_of_forall_ιMulti_two_eq_zero h

/-- A step of the first-order argument of `lem:pencil-d-stars-three`
(`eq_zero_of_starsFour_firstOrder` makes it inline for `lem:pencil-d-stars-four`). Let the form `φ₁`
kill a subspace `W` that holds the star of `y`, with `φ₁ (y ∨ e_l) + φ₀ (u ∨ e_l) = 0` for each
standard basis vector `e_l`. Then `u` lies in the radical of `φ₀`: by linearity
`φ₁ (y ∨ v) + φ₀ (u ∨ v) = 0` for every `v`, and `y ∨ v ∈ W`. -/
theorem forall_normalsJoin_eq_zero_of_firstOrder {y u : Fin (k + 2) → K}
    {W : Submodule K (⋀[K]^2 (Fin (k + 2) → K))} (hle : starGrade y ≤ W)
    {φ₀ φ₁ : Module.Dual K (⋀[K]^2 (Fin (k + 2) → K))} (hW : ∀ x ∈ W, φ₁ x = 0)
    (hl : ∀ l, φ₁ (normalsJoin y (Pi.single l 1)) + φ₀ (normalsJoin u (Pi.single l 1)) = 0) :
    ∀ v, φ₀ (normalsJoin u v) = 0 := by
  have hlin : φ₁ ∘ₗ normalsJoinLin y + φ₀ ∘ₗ normalsJoinLin u = 0 :=
    (Pi.basisFun K (Fin (k + 2))).ext fun l => by simpa [normalsJoinLin] using hl l
  intro v
  have h := LinearMap.congr_fun hlin v
  simp only [LinearMap.add_apply, LinearMap.comp_apply, normalsJoinLin, LinearMap.coe_mk,
    AddHom.coe_mk, LinearMap.zero_apply] at h
  rwa [hW _ (hle (normalsJoin_mem_starGrade y v)), zero_add] at h

/-- The pivot of the first-order argument of `lem:pencil-d-stars-three` (as at `Y 2` in
`eq_zero_of_starsFour_firstOrder`). Let `p ∈ S`, and let each `u ∈ S` with `φ₀ (p ∨ u) = 0` lie in
the radical of `φ₀`. Then all of `S` does: `p` does, as `p ∨ p = 0`, and then `φ₀ (p ∨ u) = 0` for
every `u`. -/
theorem forall_mem_normalsJoin_eq_zero_of_pivot {S : Submodule K (Fin (k + 2) → K)}
    {p : Fin (k + 2) → K} (hp : p ∈ S) {φ₀ : Module.Dual K (⋀[K]^2 (Fin (k + 2) → K))}
    (h : ∀ u ∈ S, φ₀ (normalsJoin p u) = 0 → ∀ v, φ₀ (normalsJoin u v) = 0) :
    ∀ u ∈ S, ∀ v, φ₀ (normalsJoin u v) = 0 := by
  have hp' := h p hp (by rw [normalsJoin_self, map_zero])
  exact fun u hu => h u hu (hp' u)

/-- The points of the stars family (a step of `lem:pencil-d-stars-four` and
`lem:pencil-d-stars-three`): the path `pa, Y 0, …, Y (n + 1), pb`, then the standard basis
vectors `e_l`. -/
noncomputable def starsPoint {n : ℕ} (pa pb : Fin (k + 2) → K) (Y : Fin (n + 2) → Fin (k + 2) → K) :
    Fin (n + 4) ⊕ Fin (k + 2) → Fin (k + 2) → K :=
  Sum.elim (pathVertex pa Y pb) (fun l => Pi.single l 1)

/-- The direction of `starsPoint` when the chain moves along `Y + t Y'`: `pathVertex 0 Y' 0` on the
path, `0` on the basis vectors. -/
noncomputable def starsDir {n : ℕ} (Y' : Fin (n + 2) → Fin (k + 2) → K) :
    Fin (n + 4) ⊕ Fin (k + 2) → Fin (k + 2) → K :=
  Sum.elim (pathVertex 0 Y' 0) 0

/-- The ends of the joins of the stars family, as indices of `starsPoint`: the `n + 3` joins of
consecutive points of the path, then `Y 0 ∨ e_l` and `Y 1 ∨ e_l` for each `l`. -/
def starsEnds {n : ℕ} :
    Fin (n + 3) ⊕ Fin (k + 2) ⊕ Fin (k + 2) →
      (Fin (n + 4) ⊕ Fin (k + 2)) × (Fin (n + 4) ⊕ Fin (k + 2)) :=
  Sum.elim (fun j => (Sum.inl j.castSucc, Sum.inl j.succ))
    (Sum.elim (fun l => (Sum.inl (0 : Fin (n + 2)).succ.castSucc, Sum.inr l))
      (fun l => (Sum.inl (1 : Fin (n + 2)).succ.castSucc, Sum.inr l)))

/-- The stars family (a step of `lem:pencil-d-stars-four` and `lem:pencil-d-stars-three`): the
vectors `bρ`, a basis of `ρ` where the proof uses it, the `n + 3` joins of the path
`pa, Y 0, …, Y (n + 1), pb`, which span `J(y)`, and the joins `Y 0 ∨ e_l`, `Y 1 ∨ e_l`, which span
the stars of `y₁ = Y 0` and `y₃ = Y 1`. Stars-four takes it at `n + 1`, stars-three at `n = 0`. -/
noncomputable def starsFamily {n r : ℕ} (bρ : Fin r → ⋀[K]^2 (Fin (k + 2) → K))
    (pa pb : Fin (k + 2) → K) (Y : Fin (n + 2) → Fin (k + 2) → K) :
    Fin r ⊕ (Fin (n + 3) ⊕ Fin (k + 2) ⊕ Fin (k + 2)) → ⋀[K]^2 (Fin (k + 2) → K) :=
  Sum.elim bρ fun i => normalsJoin (starsPoint pa pb Y (starsEnds i).1)
    (starsPoint pa pb Y (starsEnds i).2)

/-- `starsPoint` along `Y + t Y'` is `starsPoint Y + t starsDir Y'`. -/
theorem starsPoint_add_smul {n : ℕ} (pa pb : Fin (k + 2) → K) (Y Y' : Fin (n + 2) → Fin (k + 2) → K)
    (t : K) (e) : starsPoint pa pb (Y + t • Y') e = starsPoint pa pb Y e + t • starsDir Y' e := by
  rcases e with idx | l
  · simp only [starsPoint, starsDir, Sum.elim_inl, pathVertex_add_smul]; rfl
  · simp [starsPoint, starsDir]

/-- The stars family along `Y + t Y'`, expanded in `t`: the vectors `bρ` do not move, and a
join `p ∨ q` moves by `t (p' ∨ q + p ∨ q') + t² (p' ∨ q')`, with `p'`, `q'` the directions of its
ends (`normalsJoin_add_smul_add_smul`). -/
theorem starsFamily_add_smul {n r : ℕ} (bρ : Fin r → ⋀[K]^2 (Fin (k + 2) → K))
    (pa pb : Fin (k + 2) → K) (Y Y' : Fin (n + 2) → Fin (k + 2) → K) (t : K) (i) :
    starsFamily bρ pa pb (Y + t • Y') i = starsFamily bρ pa pb Y i +
      t • Sum.elim (fun _ => 0) (fun i => normalsJoin (starsDir Y' (starsEnds i).1)
        (starsPoint pa pb Y (starsEnds i).2) + normalsJoin (starsPoint pa pb Y (starsEnds i).1)
          (starsDir Y' (starsEnds i).2)) i +
      t ^ 2 • Sum.elim (fun _ => 0) (fun i => normalsJoin (starsDir Y' (starsEnds i).1)
        (starsDir Y' (starsEnds i).2)) i := by
  rcases i with i | i
  · simp [starsFamily]
  · simp only [starsFamily, Sum.elim_inr, starsPoint_add_smul, normalsJoin_add_smul_add_smul]

/-- The coordinates of the stars family, in the basis of `⋀²` that the standard basis induces,
are polynomials `c` in the points of the chain `Y`: constants for the vectors `bρ`, and for a join
`normalsJoinPoly` at the path's points, which are polynomial in `Y`. -/
theorem exists_mvPolynomial_repr_starsFamily {n r : ℕ} (bρ : Fin r → ⋀[K]^2 (Fin (k + 2) → K))
    (pa pb : Fin (k + 2) → K) :
    ∃ c : Fin r ⊕ (Fin (n + 3) ⊕ Fin (k + 2) ⊕ Fin (k + 2)) → Set.powersetCard (Fin (k + 2)) 2 →
        MvPolynomial (Fin (n + 2) × Fin (k + 2)) K,
      ∀ (Y : Fin (n + 2) → Fin (k + 2) → K) i s,
        ((Pi.basisFun K (Fin (k + 2))).exteriorPower 2).repr (starsFamily bρ pa pb Y i) s =
          MvPolynomial.eval (fun p => Y p.1 p.2) (c i s) := by
  classical
  set b := (Pi.basisFun K (Fin (k + 2))).exteriorPower 2
  set PP : Fin (n + 4) ⊕ Fin (k + 2) → Fin (k + 2) → MvPolynomial (Fin (n + 2) × Fin (k + 2)) K :=
    Sum.elim (pathVertex (fun j => MvPolynomial.C (pa j)) (fun i j => MvPolynomial.X (i, j))
      (fun j => MvPolynomial.C (pb j)))
      (fun l j => MvPolynomial.C ((Pi.single l 1 : Fin (k + 2) → K) j)) with hPP
  have hPPe : ∀ (Y : Fin (n + 2) → Fin (k + 2) → K) e j,
      MvPolynomial.eval (fun p => Y p.1 p.2) (PP e j) = starsPoint pa pb Y e j := by
    intro Y e j
    rcases e with idx | l
    · rcases pathVertex_cases (fun j => MvPolynomial.C (pa j)) (fun i j => MvPolynomial.X (i, j))
        (fun j => MvPolynomial.C (pb j)) idx with ⟨h0, h⟩ | ⟨i, hi, h⟩ | ⟨hl, h⟩ <;>
      rcases pathVertex_cases pa Y pb idx with ⟨h0', h'⟩ | ⟨i', hi', h'⟩ | ⟨hl', h'⟩ <;>
      simp only [hPP, starsPoint, Sum.elim_inl, h, h'] <;> try omega
      · simp
      · have : i = i' := Fin.ext (by omega)
        subst this; simp
      · simp
    · simp [hPP, starsPoint]
  refine ⟨Sum.elim (fun i s => MvPolynomial.C (b.repr (bρ i) s)) (fun i s =>
      MvPolynomial.aeval (fun p : (Fin (n + 4) ⊕ Fin (k + 2)) × Fin (k + 2) => PP p.1 p.2)
        (normalsJoinPoly (K := K) (starsEnds i).1 (starsEnds i).2 s)), fun Y i s => ?_⟩
  rcases i with i | i
  · simp [starsFamily, b]
  · simp only [starsFamily, Sum.elim_inr]
    have : MvPolynomial.eval (fun p => Y p.1 p.2) (MvPolynomial.aeval
        (fun p : (Fin (n + 4) ⊕ Fin (k + 2)) × Fin (k + 2) => PP p.1 p.2)
        (normalsJoinPoly (K := K) (starsEnds i).1 (starsEnds i).2 s)) =
        MvPolynomial.eval (fun p : (Fin (n + 4) ⊕ Fin (k + 2)) × Fin (k + 2) =>
          starsPoint pa pb Y p.1 p.2)
          (normalsJoinPoly (K := K) (starsEnds i).1 (starsEnds i).2 s) := by
      rw [← MvPolynomial.coe_aeval_eq_eval]
      change MvPolynomial.aeval _ (MvPolynomial.aeval _ _) = _
      rw [MvPolynomial.comp_aeval_apply]
      simp [hPPe]
    rw [this, normalsJoinPoly_eval]

/-- The direction of the path sequence when only the interior body `x 1` moves, along `w`: `w` at
index `2`, `0` elsewhere. -/
theorem pathVertex_zero_single {n : ℕ} (w : Fin (k + 2) → K) (idx : Fin (n + 5)) :
    pathVertex 0 (Pi.single (1 : Fin (n + 3)) w) 0 idx = if (idx : ℕ) = 2 then w else 0 := by
  rcases pathVertex_cases (0 : Fin (k + 2) → K) (Pi.single (1 : Fin (n + 3)) w) 0 idx with
    ⟨h0, h⟩ | ⟨i, hi, h⟩ | ⟨hl, h⟩ <;> rw [h]
  · simp [h0]
  · by_cases h1 : i = 1
    · subst h1; simp [hi]
    · have : (idx : ℕ) ≠ 2 := fun h2 => h1 (Fin.ext (by simp; omega))
      simp [h1, this]
  · have : (idx : ℕ) ≠ 2 := by omega
    simp [this]

/-- The first-order argument of `lem:pencil-d-stars-four`. Let `W = ρ + J(y)`, `J(y)` the span of
the joins `J_j` of the path `pa, Y 0, …, Y (n + 2), pb`, hold the stars of `Y 0` and `Y 1`, and let
`Y 0` lie in the radical of the form `φ₀`. Suppose that for every `w` some form `φ₁` kills `ρ`, has
`φ₁ J_j + φ₀ J_j' = 0` for each `j`, `J_j'` the coefficient of `t` in `J_j` when `Y 1` moves to
`Y 1 + t w`, and has `φ₁ (Y 1 ∨ u) + φ₀ (w ∨ u) = 0` for every `u`. Then `φ₀ = 0`. If
`φ₀ (w ∨ Y 2) = 0`, then `φ₁` kills every `J_j`, as only `Y 0 ∨ Y 1` and `Y 1 ∨ Y 2` move, by
`Y 0 ∨ w` and `w ∨ Y 2`; so `φ₁` kills `W ∋ Y 1 ∨ u`, and `w` lies in the radical of `φ₀`. At
`w = Y 2` this puts `Y 2` in the radical, and then every `w`. -/
theorem eq_zero_of_starsFour_firstOrder {n : ℕ} (ρ : Submodule K (⋀[K]^2 (Fin (k + 2) → K)))
    (pa pb : Fin (k + 2) → K) (Y : Fin (n + 3) → Fin (k + 2) → K)
    {φ₀ : Module.Dual K (⋀[K]^2 (Fin (k + 2) → K))} (hY0 : ∀ u, φ₀ (normalsJoin (Y 0) u) = 0)
    (hle : starGrade (Y 0) ⊔ starGrade (Y 1) ≤ ρ ⊔ Submodule.span K
      (Set.range fun j : Fin (n + 4) =>
        normalsJoin (pathVertex pa Y pb j.castSucc) (pathVertex pa Y pb j.succ)))
    (hfo : ∀ w : Fin (k + 2) → K, ∃ φ₁ : Module.Dual K (⋀[K]^2 (Fin (k + 2) → K)),
      (∀ x ∈ ρ, φ₁ x = 0) ∧
      (∀ j : Fin (n + 4),
        φ₁ (normalsJoin (pathVertex pa Y pb j.castSucc) (pathVertex pa Y pb j.succ)) +
          φ₀ (normalsJoin (pathVertex 0 (Pi.single 1 w) 0 j.castSucc) (pathVertex pa Y pb j.succ) +
            normalsJoin (pathVertex pa Y pb j.castSucc)
              (pathVertex 0 (Pi.single 1 w) 0 j.succ)) = 0) ∧
      (∀ u, φ₁ (normalsJoin (Y 1) u) + φ₀ (normalsJoin w u) = 0)) :
    φ₀ = 0 := by
  have key : ∀ w : Fin (k + 2) → K, φ₀ (normalsJoin w (Y 2)) = 0 →
      ∀ u, φ₀ (normalsJoin w u) = 0 := by
    intro w hw2 u
    obtain ⟨φ₁, h1, h2, h3⟩ := hfo w
    have hJ : ∀ j : Fin (n + 4),
        φ₁ (normalsJoin (pathVertex pa Y pb j.castSucc) (pathVertex pa Y pb j.succ)) = 0 := by
      intro j
      have h := h2 j
      rw [pathVertex_zero_single, pathVertex_zero_single] at h
      simp only [Fin.val_castSucc, Fin.val_succ] at h
      by_cases hj2 : (j : ℕ) = 2
      · have e1 := pathVertex_eq_of_val_eq pa pb Y (i := 2) (idx := j.succ)
          (by simp [Fin.val_succ, hj2])
        simpa [hj2, e1, normalsJoin_zero_right, hw2] using h
      · by_cases hj1 : (j : ℕ) = 1
        · have e0 := pathVertex_eq_of_val_eq pa pb Y (i := 0) (idx := j.castSucc) (by simp [hj1])
          simpa [hj1, e0, normalsJoin_zero_left, hY0] using h
        · have : (j : ℕ) + 1 ≠ 2 := by omega
          simpa [hj2, this, normalsJoin_zero_left, normalsJoin_zero_right] using h
    have hW : ρ ⊔ Submodule.span K (Set.range fun j : Fin (n + 4) =>
        normalsJoin (pathVertex pa Y pb j.castSucc) (pathVertex pa Y pb j.succ)) ≤
        LinearMap.ker φ₁ := by
      refine sup_le (fun x hx => h1 x hx) (Submodule.span_le.mpr ?_)
      rintro _ ⟨j, rfl⟩; exact hJ j
    have := h3 u
    rw [hW (hle (Submodule.mem_sup_right (normalsJoin_mem_starGrade _ _))), zero_add] at this
    exact this
  have hY2 := key (Y 2) (by rw [normalsJoin_self, map_zero])
  exact eq_zero_of_forall_normalsJoin_eq_zero fun w u =>
    key w (by rw [normalsJoin_swap, map_neg, hY2, neg_zero]) u

/-- `lem:pencil-d-stars-four` (SHORT-CORE workbook, S35), for `n + 4` interior bodies, the
chapter's `k` (here `k` is the grade, `d = k + 1`). The chain `Y 0, Y 1, …, Y (n + 2)` is
`y₁, y₃, …, y_{n+4}`, with `y₁` in `Sa = Π_a ≠ 0` and the last in `Sb = Π_b`; `J(y)` is the span
of the `n + 4` joins of the path `pa, y₁, y₃, …, y_{n+4}, pb`, and `W(y) = ρ + J(y)`. Some
polynomial `f` in the chain, nonzero at a chain with `y₁ ∈ Π_a` and `y_{n+4} ∈ Π_b`, has at every
such chain with `f ≠ 0`: `y₁`, `y₃` linearly independent, and
`W(y) = ⋀²` whenever `W(y)` holds both stars. Here `f = μ ν`, with `μ` from
`exists_mvPolynomial_dual_kernel_curve` for `starsFamily`, and `ν` a coordinate of `y₁ ∨ y₃`
nonzero at `y₁ = a ≠ 0` in `Π_a`, `y₃ ∉ K a`, the two nonzero together on the chains by
`MvPolynomial.exists_mem_eval_ne_zero₂`. A nonzero form `φ₀` killing `W(y)` kills both stars, so has
`y₁` and `y₃` in its radical (`mem_dualAnnihilator_starGrade_sup_starGrade_iff`) and kills the
family; moving `y₃` along each `w` gives the forms `φ₁` of `eq_zero_of_starsFour_firstOrder`, and
`φ₀ = 0`. -/
theorem exists_mvPolynomial_starsFour [Infinite K] {n : ℕ}
    (ρ : Submodule K (⋀[K]^2 (Fin (k + 2) → K))) {Sa Sb : Submodule K (Fin (k + 2) → K)}
    (hSa : Sa ≠ ⊥) (pa pb : Fin (k + 2) → K) :
    ∃ f : MvPolynomial (Fin (n + 3) × Fin (k + 2)) K,
      (∃ Y : Fin (n + 3) → Fin (k + 2) → K, Y 0 ∈ Sa ∧ Y (Fin.last (n + 2)) ∈ Sb ∧
        MvPolynomial.eval (fun p => Y p.1 p.2) f ≠ 0) ∧
      ∀ Y : Fin (n + 3) → Fin (k + 2) → K, Y 0 ∈ Sa → Y (Fin.last (n + 2)) ∈ Sb →
        MvPolynomial.eval (fun p => Y p.1 p.2) f ≠ 0 →
        LinearIndependent K ![Y 0, Y 1] ∧
        (starGrade (Y 0) ⊔ starGrade (Y 1) ≤ ρ ⊔ Submodule.span K
            (Set.range fun i : Fin (n + 4) =>
              normalsJoin (pathVertex pa Y pb i.castSucc) (pathVertex pa Y pb i.succ)) →
          ρ ⊔ Submodule.span K (Set.range fun i : Fin (n + 4) =>
            normalsJoin (pathVertex pa Y pb i.castSucc) (pathVertex pa Y pb i.succ)) = ⊤) := by
  classical
  have : Module.Free K ρ := Module.Free.of_divisionRing K ρ
  have : Module.Finite K ρ := inferInstance
  obtain ⟨bρ, hbρ⟩ : ∃ bρ : Fin (Module.finrank K ρ) → ⋀[K]^2 (Fin (k + 2) → K),
      bρ = fun i => (Module.finBasis K ρ i : ⋀[K]^2 (Fin (k + 2) → K)) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ := exists_mvPolynomial_repr_starsFamily (n := n + 1) bρ pa pb
  -- the parameters: the uncurried chain, `Y 0 ∈ Sa`, `Y (n + 2) ∈ Sb`
  obtain ⟨L, hL⟩ : ∃ L : Submodule K (Fin (n + 3) × Fin (k + 2) → K), ∀ y, y ∈ L ↔
      (fun j => y (0, j)) ∈ Sa ∧ (fun j => y (Fin.last (n + 2), j)) ∈ Sb :=
    ⟨Sa.comap (LinearMap.funLeft K K fun j => ((0 : Fin (n + 3)), j)) ⊓
      Sb.comap (LinearMap.funLeft K K fun j => (Fin.last (n + 2), j)), fun y => Iff.rfl⟩
  obtain ⟨μ, hμ, hgen⟩ := exists_mvPolynomial_dual_kernel_curve
    ((Pi.basisFun K (Fin (k + 2))).exteriorPower 2) L
    (fun y => starsFamily bρ pa pb (fun i j => y (i, j))) c (fun y i s => hc _ i s)
  -- the minor: `Y 0 ∨ Y 1` is the path join at `1`
  have hFj1 : ∀ Y : Fin (n + 3) → Fin (k + 2) → K,
      starsFamily bρ pa pb Y (Sum.inr (Sum.inl 1)) = normalsJoin (Y 0) (Y 1) := by
    intro Y
    simp only [starsFamily, starsEnds, starsPoint, Sum.elim_inr, Sum.elim_inl]
    rw [pathVertex_eq_of_val_eq pa pb Y (i := 0) (by simp),
      pathVertex_eq_of_val_eq pa pb Y (i := 1) (by simp)]
  obtain ⟨a, haS, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hSa
  obtain ⟨u, hu⟩ : ∃ u : Fin (k + 2) → K, u ∉ K ∙ a := by
    by_contra! h
    have htop : (K ∙ a) = ⊤ := eq_top_iff.mpr fun v _ => h v
    have h1 := finrank_span_singleton (K := K) ha0
    rw [htop, finrank_top, Module.finrank_fin_fun] at h1; omega
  have hau : normalsJoin a u ≠ 0 := by
    rw [normalsJoin_ne_zero_iff, LinearIndependent.pair_iff' ha0]
    intro c hc; exact hu (hc ▸ Submodule.smul_mem _ c (Submodule.mem_span_singleton_self a))
  obtain ⟨s₀, hs₀⟩ : ∃ s₀, ((Pi.basisFun K (Fin (k + 2))).exteriorPower 2).repr
      (normalsJoin a u) s₀ ≠ 0 := by
    by_contra! h
    exact hau (((Pi.basisFun K (Fin (k + 2))).exteriorPower 2).repr.injective
      (by ext s; simp [h]))
  have hlast0 : (Fin.last (n + 2) : Fin (n + 3)) ≠ 0 := fun h => by
    simpa using congrArg Fin.val h
  have hlast1 : (Fin.last (n + 2) : Fin (n + 3)) ≠ 1 := fun h => by
    have := congrArg Fin.val h; simp at this
  have h01 : (0 : Fin (n + 3)) ≠ 1 := fun h => by simpa using congrArg Fin.val h
  set Ys : Fin (n + 3) → Fin (k + 2) → K := fun i => if i = 0 then a else if i = 1 then u else 0
    with hYs
  have hYsL : (fun p : Fin (n + 3) × Fin (k + 2) => Ys p.1 p.2) ∈ L := by
    refine (hL _).2 ⟨by simpa [hYs] using haS, ?_⟩
    convert Sb.zero_mem using 1; funext j; simp [hYs, hlast0, hlast1]
  have hm₀ : MvPolynomial.eval (fun p : Fin (n + 3) × Fin (k + 2) => Ys p.1 p.2)
      (c (Sum.inr (Sum.inl 1)) s₀) ≠ 0 := by
    rw [← hc, hFj1]; simpa [hYs, h01.symm] using hs₀
  obtain ⟨y', hy'L, hy'μ, hy'm⟩ := MvPolynomial.exists_mem_eval_ne_zero₂ hμ ⟨_, hYsL, hm₀⟩
  refine ⟨μ * c (Sum.inr (Sum.inl 1)) s₀,
    ⟨fun i j => y' (i, j), ((hL y').1 hy'L).1, ((hL y').1 hy'L).2,
      by rw [map_mul]; exact mul_ne_zero hy'μ hy'm⟩, fun Y hY0 hYl hf => ?_⟩
  have hyL : (fun p : Fin (n + 3) × Fin (k + 2) => Y p.1 p.2) ∈ L := (hL _).2 ⟨hY0, hYl⟩
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
  refine hφ₀ (eq_zero_of_starsFour_firstOrder ρ pa pb Y (fun u => (hφ₀S u).1) hle fun w => ?_)
  -- the family is killed by `φ₀`
  have hP0 : starsPoint pa pb Y (Sum.inl (0 : Fin (n + 3)).succ.castSucc) = Y 0 := by
    simp only [starsPoint, Sum.elim_inl]; exact pathVertex_succ_castSucc _ _ _ _
  have hP1 : starsPoint pa pb Y (Sum.inl (1 : Fin (n + 3)).succ.castSucc) = Y 1 := by
    simp only [starsPoint, Sum.elim_inl]; exact pathVertex_succ_castSucc _ _ _ _
  have hF0 : ∀ i, φ₀ (starsFamily bρ pa pb Y i) = 0 := by
    rintro (i | j | l | l)
    · exact hφ₀W' _ (Submodule.mem_sup_left (by rw [hbρ]; exact (Module.finBasis K ρ i).2))
    · exact hφ₀W' _ (Submodule.mem_sup_right (Submodule.subset_span ⟨j, rfl⟩))
    · simp only [starsFamily, starsEnds, Sum.elim_inr, Sum.elim_inl]
      rw [hP0]; exact (hφ₀S _).1
    · simp only [starsFamily, starsEnds, Sum.elim_inr]
      rw [hP1]; exact (hφ₀S _).2
  -- the direction `Y 1 ↦ Y 1 + t w`
  have hwL : (fun p : Fin (n + 3) × Fin (k + 2) =>
      (Pi.single (1 : Fin (n + 3)) w : Fin (n + 3) → Fin (k + 2) → K) p.1 p.2) ∈ L :=
    (hL _).2 ⟨by convert Sa.zero_mem using 1; funext j; simp [h01],
      by convert Sb.zero_mem using 1; funext j; simp [hlast1]⟩
  obtain ⟨φ₁, hφ₁⟩ := hgen _ hyL hyμ _ hwL _ _
    (fun t i => starsFamily_add_smul bρ pa pb Y (Pi.single 1 w) t i) φ₀ hF0
  refine ⟨φ₁, fun x hx => ?_, fun j => hφ₁ (Sum.inr (Sum.inl j)), fun v => ?_⟩
  · have hρ : φ₁ ∘ₗ ρ.subtype = 0 := (Module.finBasis K ρ).ext fun i => by
      have := hφ₁ (Sum.inl i)
      simpa [starsFamily, hbρ] using this
    exact LinearMap.congr_fun hρ ⟨x, hx⟩
  · have hl : ∀ l, φ₁ (normalsJoin (Y 1) (Pi.single l 1)) + φ₀ (normalsJoin w (Pi.single l 1)) =
        0 := by
      intro l
      have := hφ₁ (Sum.inr (Sum.inr (Sum.inr l)))
      have hd : starsDir (Pi.single (1 : Fin (n + 3)) w)
          (Sum.inl (1 : Fin (n + 3)).succ.castSucc) = w := by
        simp only [starsDir, Sum.elim_inl]; rw [pathVertex_succ_castSucc]; simp
      have hr : starsDir (Pi.single (1 : Fin (n + 3)) w) (Sum.inr l) = 0 := rfl
      have hs : starsPoint pa pb Y (Sum.inr l) = Pi.single l 1 := rfl
      simp only [starsFamily, starsEnds, Sum.elim_inr] at this
      rw [hP1, hd, hr, hs, normalsJoin_zero_right, add_zero] at this
      exact this
    have hlin : φ₁ ∘ₗ normalsJoinLin (Y 1) + φ₀ ∘ₗ normalsJoinLin w = 0 :=
      (Pi.basisFun K (Fin (k + 2))).ext fun l => by simpa [normalsJoinLin] using hl l
    simpa [normalsJoinLin] using LinearMap.congr_fun hlin v

/-! ## The stars condition when `ρ` is small (a step of `thm:pencil-d-open-ear-three`) -/

/-- **The stars condition when `ρ` is small** (a step of `thm:pencil-d-open-ear-three`, at
`r ≤ 2`): in dimension `d = k + 1 ≥ 4`, at linearly independent `y₁ = Y 0`, `y₃ = Y 1`, the span
`W` of `ρ` and the joins `pa ∨ y₁`, `y₁ ∨ y₃` and `y₃ ∨ pb` does not hold both stars when
`dim ρ ≤ 2`: the stars span `2d − 1 = 2k + 1` dimensions (`finrank_starGrade_sup_starGrade`), and
`W` at most `dim ρ + 3 ≤ 5`. -/
theorem not_starGrade_sup_le_of_finrank_le_two (hk : 3 ≤ k)
    {ρ : Submodule K (⋀[K]^2 (Fin (k + 2) → K))} (hρ : Module.finrank K ρ ≤ 2)
    (pa pb : Fin (k + 2) → K) {Y : Fin 2 → Fin (k + 2) → K}
    (hY : LinearIndependent K ![Y 0, Y 1]) :
    ¬ starGrade (Y 0) ⊔ starGrade (Y 1) ≤ ρ ⊔ Submodule.span K
        (Set.range fun i : Fin 3 =>
          normalsJoin (pathVertex pa Y pb i.castSucc) (pathVertex pa Y pb i.succ)) := by
  intro hle
  have h1 := (finrank_starGrade_sup_starGrade hY).1
  have h2 := Submodule.finrank_mono hle
  have h3 := Submodule.finrank_add_le_finrank_add_finrank ρ (Submodule.span K
    (Set.range fun i : Fin 3 =>
      normalsJoin (pathVertex pa Y pb i.castSucc) (pathVertex pa Y pb i.succ)))
  have h4 := finrank_range_le_card (R := K) fun i : Fin 3 =>
    normalsJoin (pathVertex pa Y pb i.castSucc) (pathVertex pa Y pb i.succ)
  rw [Fintype.card_fin] at h4
  change Module.finrank K _ ≤ 3 at h4
  omega

end CombinatorialRigidity.Molecular
