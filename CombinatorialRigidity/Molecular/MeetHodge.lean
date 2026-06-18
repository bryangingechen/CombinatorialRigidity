/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Meet
public import CombinatorialRigidity.Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-!
# The metric (Hodge) layer over `Meet.lean` (`sec:molecular-meet`)

Phase 23b CHAIN-3, OD-8 route-(α). `Meet.lean`'s `complementIso` is the Hodge star
`⋆` for the standard Euclidean structure on `ℝ^{k+2}` (the standard volume form
`screwAlgebraTopEquiv` and the standard dot product `Pi.basisFun.toDual`), so the
panel-meet range-membership leaf `complementIso_extensor_mem_range_map_subtype`
(OD-8 (h-3)) is the genuine Hodge fact "`⋆` of a decomposable is the decomposable
of the orthogonal complement". The route lifts the LANDED standard-frame
range-membership `complementIso_exteriorPower_basis_mem_range_map_subtype` along an
*orthogonal* change of frame, via the O(n)-equivariance `complementIso_map_orthogonal_eq`
(h-1, in `Meet.lean`).

This file houses the metric-using leaves of that route — it cannot live in the
metric-free `Meet.lean`, because importing `Mathlib.Analysis.InnerProductSpace.PiL2`
into `Meet.lean` makes the `PiLp 2` / `EuclideanSpace` instances on `Fin (k+2) → ℝ`
defeq-visible to `⋀`-term elaboration and regresses a pre-existing exterior-algebra
proof to a `whnf` timeout (TACTICS-QUIRKS § 59). The pure metric↔`toDual` glue
(`EuclideanSpace.{inner_eq_basisFun_toDual, toDualOrthogonal_ofLinearIsometryEquiv}`)
stays in the `Mathlib/` mirror; this file is the downstream consumer.

Deliverables, in dependency order (OD-8 (h-2)+(h-3); see `notes/Phase23b.md`):

1. **`exists_orthonormalBasis_span_pair_eq`** (h-2, this commit) — the
   Gram–Schmidt span-control existence. For a linearly independent pair `n : Fin 2 →
   EuclideanSpace ℝ (Fin (k+2))`, there is an `OrthonormalBasis (Fin (k+2)) ℝ
   (EuclideanSpace ℝ (Fin (k+2)))` whose first two vectors span the same plane as
   `n 0, n 1`. Its `repr` is the frame-alignment L²-isometry that
   `EuclideanSpace.toDualOrthogonal_ofLinearIsometryEquiv` (the LANDED transport
   bridge) converts to the `toDual`-orthogonal `O` that the O(n)-equivariance
   `complementIso_map_orthogonal_eq` (h-1) consumes.

(h-3) the target leaf `complementIso_extensor_mem_range_map_subtype` and (h-4) the
assembly `extensor_join_proportional_complementIso_meet` follow downstream.
-/

@[expose] public section

namespace CombinatorialRigidity.Molecular

open scoped RealInnerProductSpace

theorem exists_orthonormalBasis_span_pair_eq {k : ℕ}
    (n : Fin 2 → EuclideanSpace ℝ (Fin (k + 2)))
    (hn : LinearIndependent ℝ n) :
    ∃ b : OrthonormalBasis (Fin (k + 2)) ℝ (EuclideanSpace ℝ (Fin (k + 2))),
      Submodule.span ℝ {b 0, b 1} = Submodule.span ℝ {n 0, n 1} := by
  classical
  -- The family `f` extending the pair `n` by zeros past index `1`.
  set f : Fin (k + 2) → EuclideanSpace ℝ (Fin (k + 2)) :=
    fun i => if h : (i : ℕ) < 2 then n ⟨i, h⟩ else 0 with hf
  have hf0 : f 0 = n 0 := by simp [hf]
  have hval1 : ((1 : Fin (k + 2)) : ℕ) = 1 := Fin.val_one _
  have hf1 : f 1 = n 1 := by
    simp only [hf, hval1]
    norm_num
  -- `0 ≠ 1` in `Fin (k+2)`, used below.
  have h01 : (0 : Fin (k + 2)) ≠ 1 := by
    simp only [Ne, Fin.ext_iff, Fin.val_zero, hval1]; omega
  -- `Set.Iic 1 = {0, 1}` on `Fin (k+2)`.
  have hIic : Set.Iic (1 : Fin (k + 2)) = {0, 1} := by
    ext i
    simp only [Set.mem_Iic, Set.mem_insert_iff, Set.mem_singleton_iff, Fin.le_def, hval1,
      Fin.ext_iff, Fin.val_zero]
    omega
  -- The index map `e = ![0, 1]` of the initial segment, injective with range `{0, 1}`.
  set e : Fin 2 → Fin (k + 2) := ![0, 1] with he
  have he_inj : Function.Injective e := injective_pair_iff_ne.2 h01
  have hfe : f ∘ e = n := by
    funext i; fin_cases i <;> simp [he, hf0, hf1]
  have hrange_e : Set.range e = Set.Iic (1 : Fin (k + 2)) := by
    rw [he, Matrix.range_cons_cons_empty, hIic]
  -- The restriction of `f` to `Set.Iic 1` is linearly independent (it is `n` reindexed).
  have hIO : LinearIndepOn ℝ f (Set.Iic (1 : Fin (k + 2))) := by
    rw [← hrange_e, linearIndepOn_range_iff he_inj, hfe]; exact hn
  -- Hence the first two `gramSchmidtNormed` vectors are nonzero.
  have hne : ∀ i : Fin (k + 2), (i : ℕ) ≤ 1 →
      InnerProductSpace.gramSchmidtNormed ℝ f i ≠ 0 := by
    intro i hi
    have hsub : Set.Iic i ⊆ Set.Iic (1 : Fin (k + 2)) :=
      Set.Iic_subset_Iic.2 (Fin.le_def.2 (by simpa [Fin.val_one] using hi))
    have hrestr : LinearIndependent ℝ (f ∘ ((↑) : Set.Iic i → Fin (k + 2))) :=
      linearIndependent_restrict_iff.2 (hIO.mono hsub)
    have hlen : ‖InnerProductSpace.gramSchmidtNormed ℝ f i‖ = 1 :=
      InnerProductSpace.gramSchmidtNormed_unit_length_coe (𝕜 := ℝ) i hrestr
    exact fun hz => by simp [hz] at hlen
  -- `finrank = card`, the hypothesis `gramSchmidtOrthonormalBasis` consumes.
  have card_h : Module.finrank ℝ (EuclideanSpace ℝ (Fin (k + 2)))
      = Fintype.card (Fin (k + 2)) := by simp
  set b := InnerProductSpace.gramSchmidtOrthonormalBasis card_h f with hbdef
  refine ⟨b, ?_⟩
  -- `f` on `Set.Iic 1` is exactly the pair `{n 0, n 1}`.
  have hrange : f '' Set.Iic (1 : Fin (k + 2)) = {n 0, n 1} := by
    rw [hIic, Set.image_insert_eq, Set.image_singleton, hf0, hf1]
  -- `b` agrees with `gramSchmidtNormed f` on `{0, 1}`, so the spans match through `Set.Iic 1`.
  have hb0 : b 0 = InnerProductSpace.gramSchmidtNormed ℝ f 0 :=
    InnerProductSpace.gramSchmidtOrthonormalBasis_apply card_h (hne 0 (by simp))
  have hb1 : b 1 = InnerProductSpace.gramSchmidtNormed ℝ f 1 :=
    InnerProductSpace.gramSchmidtOrthonormalBasis_apply card_h (hne 1 (by rw [hval1]))
  -- `{b 0, b 1} = gramSchmidtNormed f '' Set.Iic 1` (the image collapses to the pair).
  have himg : ({b 0, b 1} : Set (EuclideanSpace ℝ (Fin (k + 2))))
      = InnerProductSpace.gramSchmidtNormed ℝ f '' Set.Iic (1 : Fin (k + 2)) := by
    rw [hIic, Set.image_insert_eq, Set.image_singleton, hb0, hb1]
  rw [himg, InnerProductSpace.span_gramSchmidtNormed, InnerProductSpace.span_gramSchmidt_Iic,
    hrange]

end CombinatorialRigidity.Molecular
