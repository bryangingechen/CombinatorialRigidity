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

/-- **The `toDual`-perp of two independent normals in `ℝ^{k+2}` has dimension `k`**
(CHAIN-3, OD-8, the shared `finrank` step of the (h-3)/(h-4) leaves). For a linearly independent
pair `n : Fin 2 → ℝ^{k+2}`, the submodule `⨅ j, ker (toDual.flip (n j))` (the standard-pairing
orthogonal complement of `{n 0, n 1}`, expressed kernel-of-`flip`-wise) has dimension `k`.

Proved by transporting the bare-carrier perp `Q` to the metric orthogonal complement
`(span{ne 0, ne 1})ᗮ` of the `EuclideanSpace`-side normals `ne j = equiv.symm (n j)` (via
`EuclideanSpace.inner_eq_basisFun_toDual` + the `toDual`-symmetry `inner_comm`), then
`finrank_add_finrank_orthogonal` against `finrank (EuclideanSpace _) = k + 2` and
`finrank (span{ne 0, ne 1}) = 2` (the pair is independent). Factored out of the two CHAIN-3
range-membership leaves (`complementIso_extensor_mem_range_map_subtype` and
`extensor_join_proportional_complementIso_meet`), which carried byte-identical copies of this
~55-line transport before. -/
theorem finrank_toDualPerp_pair_eq {k : ℕ} {n : Fin 2 → Fin (k + 2) → ℝ}
    (hn : LinearIndependent ℝ n) :
    Module.finrank ℝ
        (⨅ j : Fin 2, LinearMap.ker ((Pi.basisFun ℝ (Fin (k + 2))).toDual.flip (n j))
          : Submodule ℝ (Fin (k + 2) → ℝ)) = k := by
  classical
  set Q : Submodule ℝ (Fin (k + 2) → ℝ) :=
    ⨅ j, LinearMap.ker ((Pi.basisFun ℝ (Fin (k + 2))).toDual.flip (n j)) with hQ
  -- Transport `Q` to the metric orthogonal complement `(span{ne 0, ne 1})ᗮ`.
  set ne : Fin 2 → EuclideanSpace ℝ (Fin (k + 2)) :=
    fun i => (EuclideanSpace.equiv (Fin (k + 2)) ℝ).symm (n i) with hne
  set P' : Submodule ℝ (EuclideanSpace ℝ (Fin (k + 2))) := Submodule.span ℝ {ne 0, ne 1} with hP'
  have hsymm : ∀ w v : Fin (k + 2) → ℝ,
      (Pi.basisFun ℝ (Fin (k + 2))).toDual w v = (Pi.basisFun ℝ (Fin (k + 2))).toDual v w := by
    intro w v
    set ε := EuclideanSpace.equiv (Fin (k + 2)) ℝ
    have h1 := EuclideanSpace.inner_eq_basisFun_toDual (ε.symm w) (ε.symm v)
    have h2 := EuclideanSpace.inner_eq_basisFun_toDual (ε.symm v) (ε.symm w)
    simp only [ε, ContinuousLinearEquiv.apply_symm_apply] at h1 h2
    rw [← h1, ← h2, real_inner_comm]
  have hinner : ∀ (x : EuclideanSpace ℝ (Fin (k + 2))) (j : Fin 2),
      (inner ℝ (ne j) x : ℝ)
        = (Pi.basisFun ℝ (Fin (k + 2))).toDual
            ((EuclideanSpace.equiv (Fin (k + 2)) ℝ) x) (n j) := by
    intro x j
    rw [EuclideanSpace.inner_eq_basisFun_toDual,
      show (EuclideanSpace.equiv (Fin (k + 2)) ℝ) (ne j) = n j from rfl, hsymm]
  have hQmap : Submodule.map
      (↑(EuclideanSpace.equiv (Fin (k + 2)) ℝ).symm.toLinearEquiv :
        (Fin (k + 2) → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin (k + 2))) Q
      = Submodule.orthogonal P' := by
    ext x
    rw [Submodule.mem_map_equiv, Submodule.mem_orthogonal]
    simp only [hQ, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply]
    constructor
    · intro hx u hu
      induction hu using Submodule.span_induction with
      | mem y hy =>
          rcases hy with rfl | rfl
          · rw [hinner]; exact hx 0
          · rw [hinner]; exact hx 1
      | zero => simp
      | add a b _ _ ha hb => rw [inner_add_left, ha, hb, add_zero]
      | smul c a _ ha => rw [inner_smul_left, ha, mul_zero]
    · intro hx j
      have := hx (ne j) (Submodule.subset_span (by fin_cases j <;> simp))
      rw [hinner] at this
      exact this
  have hni : LinearIndependent ℝ ne :=
    hn.map' (EuclideanSpace.equiv (Fin (k + 2)) ℝ).symm.toLinearMap
      (EuclideanSpace.equiv (Fin (k + 2)) ℝ).symm.ker
  have hP'dim : Module.finrank ℝ P' = 2 := by
    have hrange : (Set.range ne) = {ne 0, ne 1} := by
      ext y; constructor
      · rintro ⟨i, rfl⟩; fin_cases i <;> simp
      · rintro (rfl | rfl); exacts [⟨0, rfl⟩, ⟨1, rfl⟩]
    rw [hP', ← hrange, finrank_span_eq_card hni, Fintype.card_fin]
  have h1 : Module.finrank ℝ Q = Module.finrank ℝ (Submodule.orthogonal P') := by
    rw [← hQmap, LinearEquiv.finrank_map_eq]
  have h2 := Submodule.finrank_add_finrank_orthogonal P'
  rw [hP'dim, finrank_euclideanSpace_fin] at h2
  rw [h1]; omega

/-- **The `complementIso` of an arbitrary grade-2 decomposable `extensor n` lands in `⋀^k W` for
`W` the `toDual`-orthogonal complement of `{n 0, n 1}`** (`def:meet-complement-iso`, CHAIN-3, OD-8
(h-3), the panel-meet range-membership leaf). For two line-normals `n : Fin 2 → ℝ^{k+2}` and a
submodule `W ⊆ ℝ^{k+2}` that is `toDual`-orthogonal to both (`hWperp`) and of dimension `k`
(`hWdim`, forcing `W = {n 0, n 1}^⊥`), the `complementIso (j := 2)` image of the panel-meet
`extensor n` lies in the range of the inclusion
`exteriorPower.map k W.subtype : ⋀^k W →ₗ ⋀^k ℝ^{k+2}`.

This is the genuine Hodge fact "`⋆` of a decomposable is the decomposable of the orthogonal
complement", proved by an *orthogonal change of frame* (`complementIso` is the Hodge `⋆` —
O(n)-natural but not GL-natural, `complementIso_map_orthogonal_eq`): a Gram–Schmidt orthonormal
basis `b` aligns `span{n 0, n 1}` to the coordinate `2`-plane
(`exists_orthonormalBasis_span_pair_eq`), the frame map `O = ofLinearIsometryEquiv b.repr.symm`
carries the coordinate complement into
`W = {n 0, n 1}^⊥` and the coordinate blade to `extensor ![b 0, b 1]` (proportional to
`extensor n` by `exists_smul_extensor_eq_of_mem_span_range`, same plane), so the LANDED
standard-frame membership
`complementIso_exteriorPower_basis_mem_range_map_subtype` transports through `O` by the O(n)-
equivariance and the range push-forward `exteriorPower_map_mem_range_map_subtype_of_mapsTo`. The
dependent (`extensor n = 0`) case is trivial (`complementIso 0 = 0 ∈ range`). Feeds CHAIN-3's
assembly `extensor_join_proportional_complementIso_meet` (the per-line join=meet duality KT leaves
implicit). -/
theorem complementIso_extensor_mem_range_map_subtype {k : ℕ}
    (n : Fin 2 → Fin (k + 2) → ℝ)
    (W : Submodule ℝ (Fin (k + 2) → ℝ))
    (hWperp : ∀ w ∈ W, ∀ j, (Pi.basisFun ℝ (Fin (k + 2))).toDual w (n j) = 0)
    (hWdim : Module.finrank ℝ W = k) :
    complementIso (k := k) (j := 2) (by omega)
        ⟨extensor n, extensor_mem_exteriorPower n⟩
      ∈ LinearMap.range (exteriorPower.map k W.subtype) := by
  -- Dependent case: `extensor n = 0`, so `complementIso 0 = 0 ∈ range`.
  by_cases hn : LinearIndependent ℝ n
  swap
  · have h0 : (⟨extensor n, extensor_mem_exteriorPower n⟩ : ⋀[ℝ]^2 (Fin (k + 2) → ℝ)) = 0 := by
      rw [Subtype.ext_iff]; exact extensor_eq_zero_of_not_linearIndependent hn
    rw [h0, map_zero]
    exact Submodule.zero_mem _
  set ne : Fin 2 → EuclideanSpace ℝ (Fin (k + 2)) :=
    fun i => (EuclideanSpace.equiv (Fin (k + 2)) ℝ).symm (n i) with hne
  -- `ne` is linearly independent (transport `hn` across the carrier equiv).
  have hni : LinearIndependent ℝ ne :=
    hn.map' (EuclideanSpace.equiv (Fin (k + 2)) ℝ).symm.toLinearMap
      (EuclideanSpace.equiv (Fin (k + 2)) ℝ).symm.ker
  -- The `toDual`-perp `Q` of `{n 0, n 1}` in the bare carrier.
  set Q : Submodule ℝ (Fin (k + 2) → ℝ) :=
    ⨅ j, LinearMap.ker ((Pi.basisFun ℝ (Fin (k + 2))).toDual.flip (n j)) with hQ
  have hWQ : W ≤ Q := by
    intro w hw
    simp only [hQ, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply]
    exact hWperp w hw
  -- `finrank Q = k`: the shared `toDual`-perp dimension count.
  have hQdim : Module.finrank ℝ Q = k := finrank_toDualPerp_pair_eq hn
  -- `W = Q` (both `k`-dim, `W ≤ Q`).
  have hWQeq : W = Q := Submodule.eq_of_le_of_finrank_eq hWQ (by rw [hWdim, hQdim])
  -- The orthonormal frame `b` aligning `span{n 0, n 1}` to the coordinate `2`-plane.
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_span_pair_eq ne hni
  -- The frame map `O` on the bare carrier; `O (basisFun i) = bf i := equiv (b i)`.
  set O : (Fin (k + 2) → ℝ) →ₗ[ℝ] (Fin (k + 2) → ℝ) :=
    (EuclideanSpace.ofLinearIsometryEquiv b.repr.symm).toLinearMap with hO
  set bf : Fin (k + 2) → Fin (k + 2) → ℝ :=
    fun i => (EuclideanSpace.equiv (Fin (k + 2)) ℝ) (b i) with hbf
  have hObasis : ∀ i, O (Pi.basisFun ℝ (Fin (k + 2)) i) = bf i := by
    intro i
    rw [hO, hbf, LinearEquiv.coe_coe, EuclideanSpace.ofLinearIsometryEquiv]
    simp
  -- `O` preserves the standard `toDual` pairing.
  have hOorth : ∀ x y, (Pi.basisFun ℝ (Fin (k + 2))).toDual (O x) (O y)
      = (Pi.basisFun ℝ (Fin (k + 2))).toDual x y :=
    EuclideanSpace.toDualOrthogonal_ofLinearIsometryEquiv b.repr.symm
  -- `span{bf 0, bf 1} = span{n 0, n 1}` (transport `hb` across the carrier equiv).
  have hspanbf : Submodule.span ℝ {bf 0, bf 1} = Submodule.span ℝ {n 0, n 1} := by
    have key := congrArg (Submodule.map
      (↑(EuclideanSpace.equiv (Fin (k + 2)) ℝ).toLinearEquiv :
        EuclideanSpace ℝ (Fin (k + 2)) →ₗ[ℝ] (Fin (k + 2) → ℝ))) hb
    rwa [Submodule.map_span, Submodule.map_span, Set.image_pair, Set.image_pair] at key
  -- `![bf 0, bf 1]` is linearly independent.
  have hbf01 : LinearIndependent ℝ ![bf 0, bf 1] := by
    have hbli : LinearIndependent ℝ bf :=
      (b.orthonormal.linearIndependent).map'
        (EuclideanSpace.equiv (Fin (k + 2)) ℝ).toLinearMap
        (EuclideanSpace.equiv (Fin (k + 2)) ℝ).ker
    have : ![bf 0, bf 1] = bf ∘ ![0, 1] := by funext i; fin_cases i <;> rfl
    rw [this]
    refine hbli.comp _ (injective_pair_iff_ne.2 ?_)
    simp only [Ne, Fin.ext_iff, Fin.val_zero, Fin.val_one]; omega
  -- The coordinate `2`-subset `S = {0, 1}` and its enumerated frame vectors `vS`.
  set S : Set.powersetCard (Fin (k + 2)) 2 :=
    ⟨{0, 1}, by simp [Finset.card_insert_of_notMem, show (0 : Fin (k + 2)) ≠ 1 from by
      simp only [Ne, Fin.ext_iff, Fin.val_zero, Fin.val_one]; omega]⟩ with hS
  set vS : Fin 2 → Fin (k + 2) → ℝ :=
    Pi.basisFun ℝ (Fin (k + 2)) ∘ Set.powersetCard.ofFinEmbEquiv.symm S with hvS
  -- `e_S = ⟨extensor (basisFun ∘ ofFinEmbEquiv.symm S), _⟩`.
  have heS : ((Pi.basisFun ℝ (Fin (k + 2))).exteriorPower 2 S
      : ⋀[ℝ]^2 (Fin (k + 2) → ℝ))
      = ⟨extensor vS, extensor_mem_exteriorPower vS⟩ := by
    rw [exteriorPower.basis_apply]; rfl
  -- `wS := O ∘ vS = bf ∘ ofFinEmbEquiv.symm S`, the frame vectors enumerated by `S`.
  set wS : Fin 2 → Fin (k + 2) → ℝ := fun j => O (vS j) with hwS
  have hwSbf : ∀ j, wS j = bf (Set.powersetCard.ofFinEmbEquiv.symm S j) := by
    intro j
    change O (vS j) = _
    rw [hvS]; exact hObasis _
  -- The enumeration `e := ofFinEmbEquiv.symm S` of `S = {0, 1}` sends `0 ↦ 0`, `1 ↦ 1`
  -- (the unique strictly-increasing enumeration of `{0, 1}`).
  set e := Set.powersetCard.ofFinEmbEquiv.symm S with he
  have hmemS : ∀ j : Fin 2, e j ∈ ({0, 1} : Finset (Fin (k + 2))) := by
    intro j
    have := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem S (e j)).mp ⟨j, rfl⟩
    rwa [hS] at this
  have hmem01 : ∀ x : Fin (k + 2), x ∈ ({0, 1} : Finset (Fin (k + 2))) → x = 0 ∨ x = 1 := by
    intro x hx; simpa only [Finset.mem_insert, Finset.mem_singleton] using hx
  have he01 : e 0 < e 1 := e.strictMono (by norm_num)
  have he0 : e 0 = 0 := by
    rcases hmem01 _ (hmemS 0) with h | h
    · exact h
    · exfalso
      rcases hmem01 _ (hmemS 1) with h' | h'
      · rw [h, h'] at he01; exact absurd he01 (by norm_num)
      · rw [h, h'] at he01; exact absurd he01 (lt_irrefl _)
  have he1 : e 1 = 1 := by
    rcases hmem01 _ (hmemS 1) with h | h
    · exfalso; rw [he0, h] at he01; exact absurd he01 (lt_irrefl _)
    · exact h
  have hwSeq : wS = ![bf 0, bf 1] := by
    funext j
    rw [hwSbf]
    fin_cases j
    · exact congrArg bf he0
    · exact congrArg bf he1
  -- `bf` is `toDual`-orthonormal (the orthonormal basis transported through the inner product).
  have hbforth : ∀ i₁ i₂, (Pi.basisFun ℝ (Fin (k + 2))).toDual (bf i₁) (bf i₂)
      = if i₁ = i₂ then 1 else 0 := by
    intro i₁ i₂
    rw [hbf, ← EuclideanSpace.inner_eq_basisFun_toDual]
    exact b.inner_eq_ite i₁ i₂
  -- Every complementary frame vector `bf t` (`t ∉ {0, 1}`) lies in `W`.
  have hbfW : ∀ t ∈ (Set.powersetCard.compl (n := 2) (m := k)
      (by rw [Fintype.card_fin]) S : Finset (Fin (k + 2))), bf t ∈ W := by
    intro t ht
    -- `t ∉ {0, 1}`, so `bf t ⊥ bf 0, bf 1`.
    have htne : t ≠ 0 ∧ t ≠ 1 := by
      have hnotS : t ∉ (S : Finset (Fin (k + 2))) := Set.powersetCard.mem_compl.mp ht
      rw [hS] at hnotS
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnotS
      exact hnotS
    -- `bf t` is `toDual`-orthogonal to all of `span{bf 0, bf 1} = span{n 0, n 1}`.
    have hperp : ∀ y ∈ Submodule.span ℝ {bf 0, bf 1},
        (Pi.basisFun ℝ (Fin (k + 2))).toDual (bf t) y = 0 := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem z hz =>
          rcases hz with rfl | rfl
          · rw [hbforth]; exact if_neg fun h => htne.1 h
          · rw [hbforth]; exact if_neg fun h => htne.2 h
      | zero => simp
      | add a c _ _ ha hc => rw [map_add, ha, hc, add_zero]
      | smul r a _ ha => rw [map_smul, ha, smul_zero]
    rw [hWQeq, hQ, Submodule.mem_iInf]
    intro j
    rw [LinearMap.mem_ker, LinearMap.flip_apply]
    exact hperp (n j) (by rw [hspanbf]; exact Submodule.subset_span (by fin_cases j <;> simp))
  -- `map 2 O` pushes a `2`-extensor forward to the `2`-extensor of the image family.
  have hmapextensor : ∀ v : Fin 2 → Fin (k + 2) → ℝ,
      exteriorPower.map 2 O ⟨extensor v, extensor_mem_exteriorPower v⟩
        = ⟨extensor (fun i => O (v i)), extensor_mem_exteriorPower _⟩ := by
    intro v
    have hv2 : (⟨extensor v, extensor_mem_exteriorPower v⟩ : ⋀[ℝ]^2 (Fin (k + 2) → ℝ))
        = exteriorPower.ιMulti ℝ 2 v := by
      apply Subtype.ext; rw [exteriorPower.ιMulti_apply_coe]; rfl
    apply Subtype.ext
    rw [hv2, exteriorPower.map_apply_ιMulti, exteriorPower.ιMulti_apply_coe]
    rfl
  -- `⟨extensor ![bf 0, bf 1], _⟩ = map 2 O (e_S)`.
  have hmapeS : (exteriorPower.map 2 O) ((Pi.basisFun ℝ (Fin (k + 2))).exteriorPower 2 S)
      = ⟨extensor ![bf 0, bf 1], extensor_mem_exteriorPower _⟩ := by
    rw [heS, hmapextensor]
    apply Subtype.ext
    change extensor (fun i => O (vS i)) = extensor ![bf 0, bf 1]
    have : (fun i => O (vS i)) = wS := rfl
    rw [this, hwSeq]
  -- The coordinate-complement subspace `W₀` (spanned by `basisFun t` for `t ∈ Sᶜ`), with
  -- `O(W₀) ⊆ W` (each generator maps to `bf t ∈ W`).
  set complS := (Set.powersetCard.compl (n := 2) (m := k) (by rw [Fintype.card_fin]) S :
    Finset (Fin (k + 2))) with hcomplS
  set W₀ : Submodule ℝ (Fin (k + 2) → ℝ) :=
    Submodule.span ℝ (↑(complS.image (Pi.basisFun ℝ (Fin (k + 2)))) :
      Set (Fin (k + 2) → ℝ)) with hW₀
  have hW₀mem : ∀ t ∈ complS, Pi.basisFun ℝ (Fin (k + 2)) t ∈ W₀ :=
    fun t ht => Submodule.subset_span
      (by rw [Finset.coe_image]; exact ⟨t, ht, rfl⟩)
  have hOW₀ : ∀ w ∈ W₀, O w ∈ W := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
        simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
        obtain ⟨t, ht, rfl⟩ := hx
        rw [hObasis]; exact hbfW t ht
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a c _ _ ha hc => rw [map_add]; exact Submodule.add_mem _ ha hc
    | smul r a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha
  -- The standard-frame range-membership for the coordinate blade `e_S`.
  have hstd : complementIso (k := k) (j := 2) (by omega)
      ((Pi.basisFun ℝ (Fin (k + 2))).exteriorPower 2 S)
      ∈ LinearMap.range (exteriorPower.map k W₀.subtype) :=
    complementIso_exteriorPower_basis_mem_range_map_subtype S W₀ hW₀mem
  -- Input proportionality: `extensor n = c • extensor ![bf 0, bf 1]`.
  have hrangebf : Set.range ![bf 0, bf 1] = {bf 0, bf 1} := by
    ext z; constructor
    · rintro ⟨j, rfl⟩; fin_cases j <;> simp
    · rintro (rfl | rfl); exacts [⟨0, rfl⟩, ⟨1, rfl⟩]
  have hu : ∀ i, n i ∈ Submodule.span ℝ (Set.range ![bf 0, bf 1]) := by
    intro i
    rw [hrangebf, hspanbf]
    exact Submodule.subset_span (by fin_cases i <;> simp)
  obtain ⟨c, hc⟩ := exists_smul_extensor_eq_of_mem_span_range n ![bf 0, bf 1] hbf01 hu
  -- Assemble: rewrite the panel-meet by the proportionality, push `complementIso` through `O`.
  rw [← hc, map_smul]
  refine Submodule.smul_mem _ _ ?_
  rw [← hmapeS, complementIso_map_orthogonal_eq (by omega) O hOorth]
  refine Submodule.smul_mem _ _ ?_
  exact exteriorPower_map_mem_range_map_subtype_of_mapsTo O W₀ W hOW₀ hstd

/-- **The per-line point-join ↔ panel-meet duality at general `d`** (`lem:case-III-claim612-line-in-
panel-union`, CHAIN-3, OD-8 (h-4) — the assembly closing CHAIN-3). For the two normals
`n : Fin 2 → ℝ^{k+2}` cutting out a line `L` (homogeneous span `dim k = d−1`) inside a panel and the
`k = d−1` points `p : Fin k → ℝ^{k+2}` spanning `L` (each `toDual`-orthogonal to both normals,
`hperp`), the panel-meet `complementIso (j := 2) ⟨extensor n, _⟩` and the point-join
`⟨extensor p, _⟩` are proportional in `⋀^k (Fin (k+2) → ℝ)`: `∃ c, c • (panel-meet) = (point-join)`.

This is the join=meet equality KT leave implicit reading eq. (6.45)/(6.66)/(6.67) — `C(Lᵢ)` is
written agnostically as both the *meet* of the 2 panels cutting out `Lᵢ` (the rank side, CHAIN-2)
and the *join* of the `d−1` points spanning `Lᵢ` (the `D`-span side, CHAIN-4); this lemma is the one
step the Lean must spell out (a `BlueprintExposition`-grade node). Replaces the `d=3`-only
`complementIso_smul_eq_extensor_join` (whose `Φ̃`/`Ω = dualAnnihilator` route is a `dim Ω = C(d−1,2)
= 1`-at-`d=3` artifact, kept green as the `d=3` wrapper).

The `⋀^{d−1}W`-is-a-line route (NOT the withdrawn `Φ̃` route): with `W = {n 0, n 1}^⊥` (`dim W = k`,
the `toDual`-perp of the 2 independent normals via the metric transport of the (h-3) leaf), both the
point-join (`p i ∈ W` from `hperp`, `extensor_mem_range_map_subtype_of_mem_grade`) and the
panel-meet (`complementIso_extensor_mem_range_map_subtype`, the (h-3) leaf) land in the line
`range (exteriorPower.map k W.subtype)` (`⋀^k W` is `1`-dimensional, by
`finrank_exteriorPower_self_eq_one`);
the point-join is nonzero (`hp` + `extensor_ne_zero_iff_linearIndependent`), so
`exists_smul_eq_of_mem_range_map_subtype_grade` yields the scalar. Zero new count — the three landed
`_grade` bricks plus the (h-3) leaf. Lives in `MeetHodge.lean` because the `finrank W = k` step uses
the metric transport (TACTICS-QUIRKS § 59). Feeds CHAIN-4's discriminator. -/
theorem extensor_join_proportional_complementIso_meet {k : ℕ}
    (n : Fin 2 → Fin (k + 2) → ℝ)
    (p : Fin k → Fin (k + 2) → ℝ)
    (hp : LinearIndependent ℝ p)
    (hpair : LinearIndependent ℝ n)
    (hperp : ∀ i j, (Pi.basisFun ℝ (Fin (k + 2))).toDual (p i) (n j) = 0) :
    ∃ c : ℝ, c • (complementIso (k := k) (j := 2) (by omega)
        ⟨extensor n, extensor_mem_exteriorPower n⟩)
      = (⟨extensor p, extensor_mem_exteriorPower p⟩ : ⋀[ℝ]^k (Fin (k + 2) → ℝ)) := by
  classical
  -- `W = {n 0, n 1}^⊥`, the `toDual`-perp of the two normals.
  set W : Submodule ℝ (Fin (k + 2) → ℝ) :=
    ⨅ j, LinearMap.ker ((Pi.basisFun ℝ (Fin (k + 2))).toDual.flip (n j)) with hW
  have hWmem : ∀ w, w ∈ W ↔ ∀ j, (Pi.basisFun ℝ (Fin (k + 2))).toDual w (n j) = 0 := by
    intro w
    simp only [hW, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply]
  -- `hWperp` for the (h-3) leaf is the membership characterization.
  have hWperp : ∀ w ∈ W, ∀ j, (Pi.basisFun ℝ (Fin (k + 2))).toDual w (n j) = 0 :=
    fun w hw => (hWmem w).1 hw
  -- `finrank W = k`: the shared `toDual`-perp dimension count.
  have hWdim : Module.finrank ℝ W = k := finrank_toDualPerp_pair_eq hpair
  -- Panel-meet membership (the (h-3) leaf).
  have hmeet : complementIso (k := k) (j := 2) (by omega)
      ⟨extensor n, extensor_mem_exteriorPower n⟩
      ∈ LinearMap.range (exteriorPower.map k W.subtype) :=
    complementIso_extensor_mem_range_map_subtype n W hWperp hWdim
  -- Point-join membership (`p i ∈ W` from `hperp`).
  have hjoin : (⟨extensor p, extensor_mem_exteriorPower p⟩ : ⋀[ℝ]^k (Fin (k + 2) → ℝ))
      ∈ LinearMap.range (exteriorPower.map k W.subtype) :=
    extensor_mem_range_map_subtype_of_mem_grade (d := k + 1) W p
      fun i => (hWmem (p i)).2 (hperp i)
  -- Point-join `≠ 0` (`hp`); panel-meet `≠ 0` (`complementIso` injective + `extensor n ≠ 0` from
  -- `hpair`), so the proportionality scalar is invertible.
  have hjoinne : (⟨extensor p, extensor_mem_exteriorPower p⟩ : ⋀[ℝ]^k (Fin (k + 2) → ℝ)) ≠ 0 := by
    rw [Ne, Subtype.ext_iff]; exact (extensor_ne_zero_iff_linearIndependent p).2 hp
  have hmeetne : complementIso (k := k) (j := 2) (by omega)
      ⟨extensor n, extensor_mem_exteriorPower n⟩ ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (complementIso (k := k) (j := 2) (by omega)).injective,
      Subtype.ext_iff]
    exact (extensor_ne_zero_iff_linearIndependent n).2 hpair
  -- Both members of the line `range (⋀^k W ↪)`; the point-join is nonzero, so it generates the
  -- line and the panel-meet is a multiple of it. Invert the (nonzero) scalar to orient the
  -- proportionality `(panel-meet) ↦ (point-join)` (the form CHAIN-4's discriminator consumes).
  obtain ⟨c, hc⟩ :=
    exists_smul_eq_of_mem_range_map_subtype_grade (d := k + 1) W hWdim hjoin hjoinne hmeet
  have hcne : c ≠ 0 := by
    rintro rfl; rw [zero_smul] at hc; exact hmeetne hc.symm
  refine ⟨c⁻¹, ?_⟩
  rw [inv_smul_eq_iff₀ hcne]; exact hc.symm

end CombinatorialRigidity.Molecular
