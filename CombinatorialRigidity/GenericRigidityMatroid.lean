/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.LinearRigidityMatroid
import CombinatorialRigidity.BodyBar.KFrame

/-!
# The generic bar-joint rigidity matroid

Phase 24. Packages the *generic* (dimension-general) bar-joint rigidity matroid, on the
`Framework`/`Matroid.ofFun` substrate of `Framework.lean` and `LinearRigidityMatroid.lean`. In
dimension 2 that substrate was measured against the combinatorial `(2, 3)`-count matroid
(`LinearRigidityMatroid.exists_uniform_rowIndependent_placement_dim_two`); in general dimension
no combinatorial description is known, so a placement is declared *generic for row independence*
directly — every edge set row-independent at some placement is row-independent at it — and such
placements exist by the same linear-interpolation argument, with witness placements supplied by
the defining property itself rather than by a sparsity characterization.

This file lands the forward-mode chapter `blueprint/src/chapter/bar-joint-3d.tex` end to end:
`IsGenericPlacement`, its existence `exists_isGenericPlacement`, the matroid
`genericRigidityMatroid` (`Matroid.ofFun` packaging at a chosen generic placement), its
independence characterization `genericRigidityMatroid_indep_iff`, placement-independence
`linearRigidityMatroid_eq_genericRigidityMatroid`, the dimension-two reconciliation
`genericRigidityMatroid_two_eq_rigidityMatroid` with the combinatorial planar rigidity matroid,
and the rank function `genericRank` with its row-space form `genericRank_eq_finrank_span`
(reusing Phase 14's `Matroid.Rep.finrank_span_image_eq_rk`, `BodyBar/KFrame.lean`).

Non-`module`: imports `LinearRigidityMatroid.lean`, which is itself non-`module` (blocked on
`apnelson1/Matroid`'s `Matroid.Representation.Map`; see `notes/PERFORMANCE.md`), and a `module`
file cannot import a non-`module` one.

See `ROADMAP.md` §24, `notes/Phase24.md`, and `blueprint/src/chapter/bar-joint-3d.tex`.
-/

namespace SimpleGraph

variable {V : Type*} {d : ℕ}

/-- A placement `p : Framework V d` is **generic for row independence** if every edge subset
`I ⊆ E(K_V)` that is row-independent at *some* placement is row-independent at `p`.

A placement with algebraically independent coordinates would realize every row rank that any
placement realizes; this definition asks only for that consequence — all the matroid
construction (`genericRigidityMatroid` and downstream) uses — so existence
(`exists_isGenericPlacement`) is provable by an elementary perturbation argument rather than by
transcendence degree. -/
def IsGenericPlacement (p : Framework V d) : Prop :=
  ∀ I : Set (⊤ : SimpleGraph V).edgeSet,
    (∃ q : Framework V d, (⊤ : SimpleGraph V).EdgeSetRowIndependent q I) →
      (⊤ : SimpleGraph V).EdgeSetRowIndependent p I

/-- **Existence of generic placements.** For every finite `V` and every dimension `d` there is a
placement `p : Framework V d` generic for row independence.

Induction on the cardinality of the finite family
`F := {I ⊆ E(K_V) | I is row-independent at some placement}` (`Set (⊤ : SimpleGraph V).edgeSet` is
finite since `V` is finite, so this comprehension is too), matching the shape of
`LinearRigidityMatroid.exists_uniform_rowIndependent_placement_dim_two`'s dimension-2 induction:
here a member `I ∈ F` carries its witness placement by definition, so no sparsity bridge is
needed. Given `p₀` row-independent on every member of a subfamily and a new member `I₀` with
witness `q`, each condition "`S` is row-independent at `p_t := p₀ + t • (q - p₀)`" is the
non-vanishing of a one-variable polynomial in `t` (the affine-path helper
`LinearIndependent.finite_setOf_not_along_affine_path`), nonzero at `t = 0` for the subfamily
members and at `t = 1` for `I₀`; a `t` avoiding the finitely many roots enlarges the subfamily. -/
theorem exists_isGenericPlacement {V : Type*} [Finite V] (d : ℕ) :
    ∃ p : Framework V d, IsGenericPlacement p := by
  haveI : Fintype V := Fintype.ofFinite V
  -- Auxiliary: for any finite family `F` of edge subsets each row-independent at some
  -- placement, there is a single placement `p` simultaneously row-independent on every `I ∈ F`.
  suffices h_aux : ∀ F : Finset (Set (⊤ : SimpleGraph V).edgeSet),
      (∀ I ∈ F, ∃ q : Framework V d, (⊤ : SimpleGraph V).EdgeSetRowIndependent q I) →
      ∃ p : Framework V d, ∀ I ∈ F, (⊤ : SimpleGraph V).EdgeSetRowIndependent p I by
    -- `{I | ∃ q, row-LI at q}` is a subset of the finite type `Set (⊤).edgeSet`, hence finite.
    haveI : Finite (Sym2 V) := inferInstance
    haveI : Finite ((⊤ : SimpleGraph V).edgeSet : Type _) :=
      Set.Finite.to_subtype (Set.toFinite _)
    let F : Finset (Set (⊤ : SimpleGraph V).edgeSet) :=
      (Set.toFinite
        {I | ∃ q : Framework V d, (⊤ : SimpleGraph V).EdgeSetRowIndependent q I}).toFinset
    have hF_ex : ∀ I ∈ F, ∃ q : Framework V d, (⊤ : SimpleGraph V).EdgeSetRowIndependent q I := by
      intro I hI
      simpa [F, Set.Finite.mem_toFinset] using hI
    obtain ⟨p, hp⟩ := h_aux F hF_ex
    refine ⟨p, fun I hI_ex => hp I ?_⟩
    simpa [F, Set.Finite.mem_toFinset] using hI_ex
  -- Prove the auxiliary by induction on the size of `F`.
  intro F hF_ex
  induction F using Finset.induction_on with
  | empty => exact ⟨0, fun I hI => absurd hI (Finset.notMem_empty I)⟩
  | insert I₀ F' hI₀_notMem ih =>
    obtain ⟨q, hq⟩ := hF_ex I₀ (Finset.mem_insert_self _ _)
    obtain ⟨p₀, hp₀⟩ := ih (fun I hI => hF_ex I (Finset.mem_insert_of_mem hI))
    -- Interpolation `p_t := p₀ + t • r`, `r := q - p₀`. At `t = 0`, `p_t = p₀`; at `t = 1`,
    -- `p_t = q`.
    set r : Framework V d := q - p₀ with hr_def
    have h_pt_zero : p₀ + (0 : ℝ) • r = p₀ := by rw [zero_smul, add_zero]
    have h_pt_one : p₀ + (1 : ℝ) • r = q := by rw [hr_def, one_smul]; abel
    -- Bridge `EdgeSetRowIndependent (p₀ + t • r) I` to `LinearIndependent` of the affine family
    -- `e ↦ rigidityRow p₀ e + t • rigidityRow r e`, then apply the polynomial-along-line helper.
    have h_eqOn : ∀ t : ℝ, Set.EqOn
        ((⊤ : SimpleGraph V).rigidityRow (p₀ + t • r))
        (fun e => (⊤ : SimpleGraph V).rigidityRow p₀ e +
          t • (⊤ : SimpleGraph V).rigidityRow r e)
        Set.univ :=
      fun t e _ => (⊤ : SimpleGraph V).rigidityRow_add_smul p₀ r t e
    have h_iff : ∀ (t : ℝ) (I : Set (⊤ : SimpleGraph V).edgeSet),
        (⊤ : SimpleGraph V).EdgeSetRowIndependent (p₀ + t • r) I ↔
          LinearIndependent ℝ fun i : I =>
            (⊤ : SimpleGraph V).rigidityRow p₀ i.val +
              t • (⊤ : SimpleGraph V).rigidityRow r i.val := by
      intro t I
      rw [edgeSetRowIndependent_iff_linearIndepOn_rigidityRow,
        linearIndepOn_congr ((h_eqOn t).mono (Set.subset_univ _))]
      rfl
    -- Per-`I` bad-`t`-set finiteness, from a witness `t_w` (`1` for `I = I₀`, `0` for `I ∈ F'`).
    have h_bad_finite : ∀ I ∈ insert I₀ F',
        {t : ℝ | ¬ (⊤ : SimpleGraph V).EdgeSetRowIndependent (p₀ + t • r) I}.Finite := by
      intro I hI
      obtain ⟨t_w, h_w⟩ : ∃ t_w : ℝ,
          (⊤ : SimpleGraph V).EdgeSetRowIndependent (p₀ + t_w • r) I := by
        rcases Finset.mem_insert.mp hI with rfl | hI'
        · exact ⟨1, by rw [h_pt_one]; exact hq⟩
        · exact ⟨0, by rw [h_pt_zero]; exact hp₀ I hI'⟩
      rw [h_iff t_w I] at h_w
      refine (LinearIndependent.finite_setOf_not_along_affine_path h_w).subset ?_
      intro t ht
      simp only [Set.mem_setOf_eq] at ht ⊢
      exact fun hLI => ht ((h_iff t I).mpr hLI)
    -- The union of bad-`t` sets across `I ∈ insert I₀ F'` is finite; `ℝ` is infinite, so there's
    -- a `t` outside it, and the placement `p₀ + t • r` works on every `I ∈ insert I₀ F'`.
    let bad : Set ℝ :=
      ⋃ I ∈ (insert I₀ F' : Finset _),
        {t : ℝ | ¬ (⊤ : SimpleGraph V).EdgeSetRowIndependent (p₀ + t • r) I}
    have h_bad_set_finite : bad.Finite :=
      (Finset.finite_toSet _).biUnion fun I hI => h_bad_finite I hI
    obtain ⟨t, ht_good⟩ := h_bad_set_finite.exists_notMem
    refine ⟨p₀ + t • r, fun I hI => ?_⟩
    by_contra h_not_LI
    apply ht_good
    simp only [bad, Set.mem_iUnion]
    exact ⟨I, hI, h_not_LI⟩

/-! ### The generic rigidity matroid and its rank function

The matroid `Matroid.ofFun`-packaging at a chosen generic placement (any placement works, by
`linearRigidityMatroid_eq_genericRigidityMatroid` below), and the identification of its
independent sets with "row-independent at some placement"
(`genericRigidityMatroid_indep_iff`). -/

/-- The **generic (`d`-dimensional bar-joint) rigidity matroid** of a finite vertex set `V`: the
linear rigidity matroid (`LinearRigidityMatroid.linearRigidityMatroid`) at a placement generic for
row independence (`exists_isGenericPlacement`). By `linearRigidityMatroid_eq_genericRigidityMatroid`
the matroid does not depend on the choice of generic placement. -/
noncomputable def genericRigidityMatroid (V : Type*) [Finite V] (d : ℕ) : Matroid (Sym2 V) :=
  linearRigidityMatroid V d (exists_isGenericPlacement d).choose

@[simp]
theorem genericRigidityMatroid_ground (V : Type*) [Finite V] (d : ℕ) :
    (genericRigidityMatroid V d).E = (⊤ : SimpleGraph V).edgeSet :=
  linearRigidityMatroid_ground V d _

/-- **Independence in the generic rigidity matroid.** An edge subset `I ⊆
(⊤ : SimpleGraph V).edgeSet` is independent in `genericRigidityMatroid V d` if and only if it is
row-independent at *some* placement `q : Framework V d`.

Independence in `linearRigidityMatroid V d p` (`p` the chosen generic placement) is row
independence at `p` (`linearRigidityMatroid_indep_iff_edgeSetRowIndependent`); row independence at
`p` exhibits the witness `q := p`, and conversely genericity of `p` transfers row independence at
any witness placement to `p`. -/
theorem genericRigidityMatroid_indep_iff {V : Type*} [Finite V] {d : ℕ}
    {I : Set (⊤ : SimpleGraph V).edgeSet} :
    (genericRigidityMatroid V d).Indep (Subtype.val '' I) ↔
      ∃ q : Framework V d, (⊤ : SimpleGraph V).EdgeSetRowIndependent q I := by
  rw [genericRigidityMatroid, linearRigidityMatroid_indep_iff_edgeSetRowIndependent]
  exact ⟨fun h => ⟨_, h⟩, fun ⟨q, hq⟩ => (exists_isGenericPlacement d).choose_spec I ⟨q, hq⟩⟩

/-- **Placement independence.** For every placement `p : Framework V d` generic for row
independence, `linearRigidityMatroid V d p = genericRigidityMatroid V d`.

Both matroids have ground set `(⊤ : SimpleGraph V).edgeSet`, so by `Matroid.ext_indep` it suffices
to identify their independent sets. Independence in `linearRigidityMatroid V d p` is row
independence at `p` (`linearRigidityMatroid_indep_iff_edgeSetRowIndependent`), which by genericity
of `p` is equivalent to row independence at some placement, i.e. to independence in
`genericRigidityMatroid V d` (`genericRigidityMatroid_indep_iff`). -/
theorem linearRigidityMatroid_eq_genericRigidityMatroid {V : Type*} [Finite V] {d : ℕ}
    {p : Framework V d} (hp : IsGenericPlacement p) :
    linearRigidityMatroid V d p = genericRigidityMatroid V d := by
  refine Matroid.ext_indep ?_ fun J hJ => ?_
  · rw [linearRigidityMatroid_ground, genericRigidityMatroid_ground]
  · rw [linearRigidityMatroid_ground] at hJ
    set I : Set (⊤ : SimpleGraph V).edgeSet := Subtype.val ⁻¹' J with hI_def
    have hI_image : Subtype.val '' I = J :=
      Set.image_preimage_eq_of_subset (by rw [Subtype.range_coe]; exact hJ)
    rw [← hI_image, linearRigidityMatroid_indep_iff_edgeSetRowIndependent,
      genericRigidityMatroid_indep_iff]
    exact ⟨fun h => ⟨p, h⟩, fun ⟨q, hq⟩ => hp I ⟨q, hq⟩⟩

/-- **Dimension-2 generic rigidity matroid equals the combinatorial planar rigidity matroid.**

The matroid `genericRigidityMatroid V 2` at the chosen generic placement coincides with
`SimpleGraph.rigidityMatroid V`, the `(2, 3)`-count matroid. Both have ground set
`(⊤ : SimpleGraph V).edgeSet`, and both independence predicates say "row-independent at some
placement" (`genericRigidityMatroid_indep_iff` and
`rigidityMatroid_indep_iff_edgeSetRowIndependent`). By `Matroid.ext_indep` they are equal. -/
theorem genericRigidityMatroid_two_eq_rigidityMatroid {V : Type*} [Finite V] :
    genericRigidityMatroid V 2 = SimpleGraph.rigidityMatroid V := by
  refine Matroid.ext_indep ?_ fun J hJ => ?_
  · rw [genericRigidityMatroid_ground, SimpleGraph.rigidityMatroid]
    simp only [SimpleGraph.countMatroid_E]
  · rw [genericRigidityMatroid_ground] at hJ
    set I : Set (⊤ : SimpleGraph V).edgeSet := Subtype.val ⁻¹' J with hI_def
    have hI_image : Subtype.val '' I = J :=
      Set.image_preimage_eq_of_subset (by rw [Subtype.range_coe]; exact hJ)
    rw [← hI_image, genericRigidityMatroid_indep_iff,
      SimpleGraph.rigidityMatroid_indep_iff_edgeSetRowIndependent]

/-! ### The generic rank function

The rank function of `genericRigidityMatroid` (`def:genericRank`) and its row-space
characterization (`lem:genericRank-eq-finrank-span`), closing the chapter. -/

/-- The **generic (`d`-dimensional bar-joint) rank** of a graph `H` on `V`: the rank of `E(H)` in
`genericRigidityMatroid V d`. At `d = 3` this is the rank function `r(·)` of the molecule rank
formula (KT Corollary 5.7, Phase 26). -/
noncomputable def genericRank {V : Type*} [Finite V] (H : SimpleGraph V) (d : ℕ) : ℕ :=
  (genericRigidityMatroid V d).rk H.edgeSet

/-- **Row-space form of the generic rank.** For every placement `p : Framework V d` generic for
row independence and every graph `H` on `V`, `H.genericRank d` is the `ℝ`-dimension of the span of
the rigidity rows of `H`'s edges at `p`.

By `linearRigidityMatroid_eq_genericRigidityMatroid`, `genericRigidityMatroid V d =
linearRigidityMatroid V d p = Matroid.ofFun ℝ (⊤ : SimpleGraph V).edgeSet (linearRigidityRow p)`.
The vendored `Matroid.repOfFun` packages `linearRigidityRow p` as a representation of that matroid,
so `Matroid.Rep.finrank_span_image_eq_rk` (`BodyBar/KFrame.lean`) identifies the rank of `E(H)`
with the dimension of the span of `linearRigidityRow p '' E(H)`. That span agrees with the span of
the `(⊤).rigidityRow p`-image of `E(H)`, since `linearRigidityRow p` restricts to `rigidityRow` on
`E(K_V)` (`linearRigidityRow_subtype_val`) and `E(H) ⊆ E(K_V)`. -/
theorem genericRank_eq_finrank_span {V : Type*} [Finite V] {d : ℕ} {p : Framework V d}
    (hp : IsGenericPlacement p) (H : SimpleGraph V) :
    H.genericRank d = Module.finrank ℝ (Submodule.span ℝ
      ((⊤ : SimpleGraph V).rigidityRow p '' (Subtype.val ⁻¹' H.edgeSet :
        Set (⊤ : SimpleGraph V).edgeSet))) := by
  haveI hMFin : (Matroid.ofFun ℝ (⊤ : SimpleGraph V).edgeSet (linearRigidityRow p)).Finite :=
    Matroid.ofFun_finite _ _ (Set.toFinite _)
  set v := Matroid.repOfFun ℝ (⊤ : SimpleGraph V).edgeSet (linearRigidityRow p) with hv_def
  have hrep := v.finrank_span_image_eq_rk H.edgeSet
  have hHE : H.edgeSet ⊆ (⊤ : SimpleGraph V).edgeSet := edgeSet_mono le_top
  have hHE_image :
      Subtype.val '' (Subtype.val ⁻¹' H.edgeSet : Set (⊤ : SimpleGraph V).edgeSet) = H.edgeSet :=
    Set.image_preimage_eq_of_subset (by rw [Subtype.range_coe]; exact hHE)
  have himg : v '' H.edgeSet = (⊤ : SimpleGraph V).rigidityRow p ''
      (Subtype.val ⁻¹' H.edgeSet : Set (⊤ : SimpleGraph V).edgeSet) := by
    have hind : v '' H.edgeSet = linearRigidityRow p '' H.edgeSet := by
      rw [hv_def, Matroid.repOfFun_coeFun_eq]
      exact Set.image_congr fun e he => Set.indicator_of_mem (hHE he) _
    rw [hind]
    conv_lhs => rw [← hHE_image]
    rw [Set.image_image]
    congr 1
    funext e
    exact linearRigidityRow_subtype_val p e
  rw [genericRank, ← linearRigidityMatroid_eq_genericRigidityMatroid hp]
  change (Matroid.ofFun ℝ (⊤ : SimpleGraph V).edgeSet (linearRigidityRow p)).rk H.edgeSet = _
  rw [← hrep, himg]

/-- **The generic rank dominates the rank at any placement.** For *every* placement `p :
Framework V d` (not necessarily generic for row independence) and every graph `H` on `V`, the
dimension of the span of `H`'s rigidity rows at `p` is at most `H`'s generic rank `H.genericRank
d`; equivalently `rank R(H, p) ≤ r_d(H)` for the bar-joint rigidity matrix at `p`.

Same row-span computation as `genericRank_eq_finrank_span` (via
`Matroid.Rep.finrank_span_image_eq_rk` on the *specific*, possibly non-generic,
`linearRigidityMatroid V d p`), landing at its matroid rank `(linearRigidityMatroid V d
p).rk H.edgeSet` rather than converting to `genericRigidityMatroid V d`.
The inequality closes the gap: a subset of `H.edgeSet` independent at `p` is row-independent at
*some* placement (namely `p` itself), hence independent in `genericRigidityMatroid V d`
(`genericRigidityMatroid_indep_iff`), so its cardinality is at most the generic rank
(`Indep.ncard_le_rk_of_subset`). -/
theorem finrank_span_rigidityRow_le_genericRank {V : Type*} [Finite V] {d : ℕ}
    (p : Framework V d) (H : SimpleGraph V) :
    Module.finrank ℝ (Submodule.span ℝ
      ((⊤ : SimpleGraph V).rigidityRow p '' (Subtype.val ⁻¹' H.edgeSet :
        Set (⊤ : SimpleGraph V).edgeSet))) ≤ H.genericRank d := by
  haveI hMFin : (Matroid.ofFun ℝ (⊤ : SimpleGraph V).edgeSet (linearRigidityRow p)).Finite :=
    Matroid.ofFun_finite _ _ (Set.toFinite _)
  set v := Matroid.repOfFun ℝ (⊤ : SimpleGraph V).edgeSet (linearRigidityRow p) with hv_def
  have hrep := v.finrank_span_image_eq_rk H.edgeSet
  have hHE : H.edgeSet ⊆ (⊤ : SimpleGraph V).edgeSet := edgeSet_mono le_top
  have hHE_image :
      Subtype.val '' (Subtype.val ⁻¹' H.edgeSet : Set (⊤ : SimpleGraph V).edgeSet) = H.edgeSet :=
    Set.image_preimage_eq_of_subset (by rw [Subtype.range_coe]; exact hHE)
  have himg : v '' H.edgeSet = (⊤ : SimpleGraph V).rigidityRow p ''
      (Subtype.val ⁻¹' H.edgeSet : Set (⊤ : SimpleGraph V).edgeSet) := by
    have hind : v '' H.edgeSet = linearRigidityRow p '' H.edgeSet := by
      rw [hv_def, Matroid.repOfFun_coeFun_eq]
      exact Set.image_congr fun e he => Set.indicator_of_mem (hHE he) _
    rw [hind]
    conv_lhs => rw [← hHE_image]
    rw [Set.image_image]
    congr 1
    funext e
    exact linearRigidityRow_subtype_val p e
  rw [← himg, hrep]
  change (linearRigidityMatroid V d p).rk H.edgeSet ≤ H.genericRank d
  haveI : (linearRigidityMatroid V d p).Finite := hMFin
  haveI hMFinG : (genericRigidityMatroid V d).Finite :=
    Matroid.ofFun_finite _ _ (Set.toFinite _)
  rw [genericRank, Matroid.rk_le_iff]
  intro I hI_sub hI_indep
  have hI_top : I ⊆ (⊤ : SimpleGraph V).edgeSet := hI_sub.trans hHE
  set I' : Set (⊤ : SimpleGraph V).edgeSet := Subtype.val ⁻¹' I with hI'_def
  have hI'_image : Subtype.val '' I' = I :=
    Set.image_preimage_eq_of_subset (by rw [Subtype.range_coe]; exact hI_top)
  have hI_indep' : (linearRigidityMatroid V d p).Indep (Subtype.val '' I') := by
    rw [hI'_image]; exact hI_indep
  rw [linearRigidityMatroid_indep_iff_edgeSetRowIndependent] at hI_indep'
  have hgen : (genericRigidityMatroid V d).Indep (Subtype.val '' I') :=
    genericRigidityMatroid_indep_iff.mpr ⟨p, hI_indep'⟩
  rw [hI'_image] at hgen
  exact hgen.ncard_le_rk_of_subset hI_sub

/-- **Row rank equals column rank, `RigidityMap`-range form.** For every placement `p :
Framework V d` and every graph `H` on `V`, `finrank (range (H.RigidityMap p))` — the rank of `H`'s
rigidity matrix at `p` — equals the dimension of the span of the *ambient* `(⊤ : SimpleGraph V)`'s
rigidity rows restricted to `E(H)`. Converts row rank to column rank (`span_range_rigidityRow` +
`LinearMap.finrank_range_dualMap_eq_finrank_range`), reconciling `H`'s own `rigidityRow` family
with the ambient one via the graph-independence of `rigidityRow` (`rigidityRow_congr`). The shared
computation behind `finrank_range_rigidityMap_le_genericRank` and
`finrank_range_rigidityMap_eq_genericRank`, which each combine it with a domination or an equality
for the row-span side. -/
private theorem finrank_range_rigidityMap_eq_finrank_span_rigidityRow {V : Type*} [Finite V]
    {d : ℕ} (H : SimpleGraph V) (p : Framework V d) :
    Module.finrank ℝ (LinearMap.range (H.RigidityMap p)) = Module.finrank ℝ (Submodule.span ℝ
      ((⊤ : SimpleGraph V).rigidityRow p '' (Subtype.val ⁻¹' H.edgeSet :
        Set (⊤ : SimpleGraph V).edgeSet))) := by
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Fintype H.edgeSet := Set.Finite.fintype H.edgeSet.toFinite
  have hHE : H.edgeSet ⊆ (⊤ : SimpleGraph V).edgeSet := edgeSet_mono le_top
  have hset : Set.range (H.rigidityRow p) =
      (⊤ : SimpleGraph V).rigidityRow p '' (Subtype.val ⁻¹' H.edgeSet :
        Set (⊤ : SimpleGraph V).edgeSet) := by
    ext x
    constructor
    · rintro ⟨⟨e, he⟩, rfl⟩
      exact ⟨⟨e, hHE he⟩, he, rigidityRow_congr (⊤ : SimpleGraph V) H p (hHE he) he⟩
    · rintro ⟨⟨e, heTop⟩, heH, rfl⟩
      exact ⟨⟨e, heH⟩, rigidityRow_congr H (⊤ : SimpleGraph V) p heH heTop⟩
  rw [← LinearMap.finrank_range_dualMap_eq_finrank_range, ← H.span_range_rigidityRow p, hset]

/-- **The generic rank dominates the realized rank at any placement, `RigidityMap` form.** For
every placement `p : Framework V d` (not necessarily generic) and every graph `H` on `V`, the rank
of `H`'s rigidity matrix at `p` — `finrank (range (H.RigidityMap p))` — is at most `H`'s generic
rank. -/
theorem finrank_range_rigidityMap_le_genericRank {V : Type*} [Finite V] {d : ℕ}
    (H : SimpleGraph V) (p : Framework V d) :
    Module.finrank ℝ (LinearMap.range (H.RigidityMap p)) ≤ H.genericRank d := by
  rw [finrank_range_rigidityMap_eq_finrank_span_rigidityRow]
  exact finrank_span_rigidityRow_le_genericRank p H

/-- **The generic rank equals the realized rank at a generic placement, `RigidityMap` form.** For
every placement `p : Framework V d` generic for row independence and every graph `H` on `V`, the
rank of `H`'s rigidity matrix at `p` — `finrank (range (H.RigidityMap p))` — equals `H`'s generic
rank; the `RigidityMap`-range restatement of `genericRank_eq_finrank_span`. -/
theorem finrank_range_rigidityMap_eq_genericRank {V : Type*} [Finite V] {d : ℕ}
    (H : SimpleGraph V) {p : Framework V d} (hp : IsGenericPlacement p) :
    Module.finrank ℝ (LinearMap.range (H.RigidityMap p)) = H.genericRank d := by
  rw [finrank_range_rigidityMap_eq_finrank_span_rigidityRow]
  exact (genericRank_eq_finrank_span hp H).symm

end SimpleGraph
