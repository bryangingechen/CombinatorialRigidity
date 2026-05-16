/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.MatroidIdentification
import CombinatorialRigidity.Mathlib.LinearAlgebra.Matrix.Rank
import Matroid.Representation.Map

/-!
# Linear-matroid framing of the planar rigidity matroid

Phase 8. Packages the planar rigidity matroid as the linear matroid `Matroid.ofFun` of the
rigidity-row function at a chosen placement, using the `apnelson1/Matroid` library
(see `DESIGN.md` *Phase 8: `apnelson1/Matroid` dependency*). The matroid identification
`linearRigidityMatroid V 2 p = SimpleGraph.rigidityMatroid V` (Lovász–Yemini, linear-matroid
form) at a generic placement `p` is the eventual Phase 8 target; this file lands the
definition skeleton plus the independence bridge that identifies the linear matroid's
independent sets with the project's `EdgeSetRowIndependent` predicate at the same placement.

`Matroid.ofFun` consumes a function on the full type `Sym2 V` and a ground set; we use
`(⊤ : SimpleGraph V).edgeSet` as the ground set (matching `SimpleGraph.rigidityMatroid`'s
ground set) and extend `(⊤).rigidityRow p` by zero off the edge set via `linearRigidityRow`.

See `ROADMAP.md` §8, `notes/Phase8.md`, and the *Linear-matroid framing* subsection of
`blueprint/src/chapter/rigidity-matroid.tex`.
-/

namespace SimpleGraph

variable {V : Type*} {d : ℕ}

/-- Extension of `(⊤ : SimpleGraph V).rigidityRow p` from the subtype `(⊤).edgeSet` to all of
`Sym2 V` by zero off the edge set, via `Function.extend` along the subtype embedding
`Subtype.val`. Used as the underlying linear-row function of `linearRigidityMatroid V d p`;
`Matroid.ofFun` consumes a function on the full type, and the matroid only depends on the
function's values on its ground set (`Matroid.ofFun_indicator`), so the off-edge-set zero
extension is harmless. -/
noncomputable def linearRigidityRow (p : Framework V d) :
    Sym2 V → Module.Dual ℝ (Framework V d) :=
  Function.extend Subtype.val ((⊤ : SimpleGraph V).rigidityRow p) 0

@[simp]
theorem linearRigidityRow_subtype_val (p : Framework V d)
    (e : (⊤ : SimpleGraph V).edgeSet) :
    linearRigidityRow p e.val = (⊤ : SimpleGraph V).rigidityRow p e :=
  Subtype.val_injective.extend_apply _ _ e

theorem linearRigidityRow_of_mem (p : Framework V d) {e : Sym2 V}
    (h : e ∈ (⊤ : SimpleGraph V).edgeSet) :
    linearRigidityRow p e = (⊤ : SimpleGraph V).rigidityRow p ⟨e, h⟩ :=
  Subtype.val_injective.extend_apply _ _ ⟨e, h⟩

/-- The **linear rigidity matroid** at a placement `p : Framework V d`: the representable
matroid on `Sym2 V` with ground set `(⊤ : SimpleGraph V).edgeSet` and row function
`linearRigidityRow p`. Built via `Matroid.ofFun` from the `apnelson1/Matroid` library.

The matroid identification `linearRigidityMatroid V 2 p = SimpleGraph.rigidityMatroid V`
(Lovász–Yemini, linear-matroid form) at a generic placement is the Phase 8 target; the
independence bridge that powers it lives in
`linearRigidityMatroid_indep_iff_edgeSetRowIndependent`. -/
noncomputable def linearRigidityMatroid (V : Type*) (d : ℕ)
    (p : Framework V d) : Matroid (Sym2 V) :=
  Matroid.ofFun ℝ (⊤ : SimpleGraph V).edgeSet (linearRigidityRow p)

@[simp]
theorem linearRigidityMatroid_ground (V : Type*) (d : ℕ)
    (p : Framework V d) :
    (linearRigidityMatroid V d p).E = (⊤ : SimpleGraph V).edgeSet :=
  Matroid.ofFun_ground_eq

/-- **Linear-matroid independence iff row-LI.** An edge subset `I ⊆ (⊤ : SimpleGraph V).edgeSet`
is independent in `linearRigidityMatroid V d p` if and only if its underlying edges form a
row-independent family at `p`. The image-of-subtype packaging on the left-hand side matches
`SimpleGraph.rigidityMatroid_indep_iff_edgeSetRowIndependent`, so this lemma is the linear-
matroid analogue of the matroid-form Lovász–Yemini bridge. -/
theorem linearRigidityMatroid_indep_iff_edgeSetRowIndependent
    {V : Type*} {d : ℕ} {p : Framework V d}
    {I : Set (⊤ : SimpleGraph V).edgeSet} :
    (linearRigidityMatroid V d p).Indep (Subtype.val '' I) ↔
      (⊤ : SimpleGraph V).EdgeSetRowIndependent p I := by
  rw [edgeSetRowIndependent_iff_linearIndepOn_rigidityRow, linearRigidityMatroid,
    Matroid.ofFun_indep_iff,
    and_iff_left (by rintro _ ⟨e, _, rfl⟩; exact e.property)]
  refine ⟨fun hli => ?_, fun hli => ?_⟩
  · refine (hli.comp_of_image Subtype.val_injective.injOn).congr ?_
    intro e _
    exact linearRigidityRow_subtype_val p e
  · refine LinearIndepOn.image_of_comp _ _ (hli.congr ?_)
    intro e _
    exact (linearRigidityRow_subtype_val p e).symm

/-- **Uniformly generic placement, dim 2.** There exists a placement `p : Framework V 2` at
which *every* `(2, 3)`-sparse edge subset of `K_V` is simultaneously row-independent.

The auxiliary that powers the matroid identification `linearRigidityMatroid_eq_rigidityMatroid`
below: a placement satisfying the conclusion makes the linear matroid's independent sets coincide
with the combinatorial $(2, 3)$-count matroid's independent sets at a single witness, collapsing
the existential `∃ p', row-LI at p'` in `rigidityMatroid_indep_iff_edgeSetRowIndependent` to
`row-LI at p`.

Proof sketch (linear-interpolation perturbation on the finite family of sparse subsets, per
blueprint `lem:exists-uniform-rowIndependent-placement`): induct on the cardinality of
`{I ⊆ E(K_V) | fromEdgeSet I is (2, 3)-sparse}`. At the inductive step, interpolate between
the inductive-hypothesis witness `p₀` (row-LI on the `n`-element subfamily) and a fresh row-LI
witness `q` for the new subset `I₀` (from `IsSparse.exists_rowIndependent_placement`); each
"row-LI on `S`" condition along `p_t := (1-t) p₀ + t q` is the non-vanishing of a polynomial in
`t`, nonzero at `t = 0` for `S` in the IH subfamily and at `t = 1` for `S = I₀`, so cofinitely
many `t` work for the enlarged subfamily. -/
theorem exists_uniform_rowIndependent_placement_dim_two {V : Type*} [Finite V] :
    ∃ p : Framework V 2,
      ∀ I : Set (⊤ : SimpleGraph V).edgeSet,
        (SimpleGraph.fromEdgeSet (Subtype.val '' I)).IsSparse 2 3 →
          (⊤ : SimpleGraph V).EdgeSetRowIndependent p I := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  -- Auxiliary: for any finite family `F` of sparse-bearing edge subsets, there is a single
  -- placement `p` simultaneously row-LI on every `I ∈ F`. The main statement follows by
  -- taking `F` to be the (finite) family of *all* sparse-bearing subsets.
  suffices h_aux : ∀ F : Finset (Set (⊤ : SimpleGraph V).edgeSet),
      (∀ I ∈ F, (SimpleGraph.fromEdgeSet (Subtype.val '' I)).IsSparse 2 3) →
      ∃ p : Framework V 2, ∀ I ∈ F, (⊤ : SimpleGraph V).EdgeSetRowIndependent p I by
    -- `{I | sparse}` is a subset of the finite type `Set (⊤).edgeSet`, hence finite.
    haveI : Finite (Sym2 V) := inferInstance
    haveI : Finite ((⊤ : SimpleGraph V).edgeSet : Type _) :=
      Set.Finite.to_subtype (Set.toFinite _)
    let F : Finset (Set (⊤ : SimpleGraph V).edgeSet) :=
      (Set.toFinite
        {I | (SimpleGraph.fromEdgeSet (Subtype.val '' I)).IsSparse 2 3}).toFinset
    have hF_sparse : ∀ I ∈ F, (SimpleGraph.fromEdgeSet (Subtype.val '' I)).IsSparse 2 3 := by
      intro I hI
      simpa [F, Set.Finite.mem_toFinset] using hI
    obtain ⟨p, hp⟩ := h_aux F hF_sparse
    refine ⟨p, fun I hI_sparse => hp I ?_⟩
    simpa [F, Set.Finite.mem_toFinset] using hI_sparse
  -- Prove the auxiliary by induction on the size of `F`.
  intro F hF_sparse
  induction F using Finset.induction_on with
  | empty => exact ⟨0, fun I hI => absurd hI (Finset.notMem_empty I)⟩
  | insert I₀ F' hI₀_notMem ih =>
    have hI₀_sparse : (SimpleGraph.fromEdgeSet (Subtype.val '' I₀)).IsSparse 2 3 :=
      hF_sparse I₀ (Finset.mem_insert_self _ _)
    have hF'_sparse :
        ∀ I ∈ F', (SimpleGraph.fromEdgeSet (Subtype.val '' I)).IsSparse 2 3 :=
      fun I hI => hF_sparse I (Finset.mem_insert_of_mem hI)
    obtain ⟨p₀, hp₀⟩ := ih hF'_sparse
    obtain ⟨q, hq⟩ := (edgeSet_rowIndependent_iff_isSparse_dim_two _ I₀).mpr hI₀_sparse
    -- Interpolation `p_t := p₀ + t • (q - p₀)`. At `t = 0`, `p_t = p₀`; at `t = 1`, `p_t = q`.
    set r : Framework V 2 := q - p₀ with hr_def
    have h_pt_zero : p₀ + (0 : ℝ) • r = p₀ := by rw [zero_smul, add_zero]
    have h_pt_one : p₀ + (1 : ℝ) • r = q := by rw [hr_def, one_smul]; abel
    -- For each `I`, the bad-`t` set `{t | ¬ EdgeSetRowIndependent (p₀ + t • r) I}` is finite,
    -- using the vector-form polynomial-along-line helper at `t = 0` (for `I ∈ F'`) or
    -- `t = 1` (for `I = I₀`).
    -- Per-`I` bad-`t`-set finiteness. We bridge `EdgeSetRowIndependent (p₀ + t • r) I`
    -- through `LinearIndepOn` of the affine family `e ↦ rigidityRow p₀ e + t • rigidityRow r e`
    -- (via `rigidityRow_add_smul` and `linearIndepOn_congr`), then apply the
    -- polynomial-along-line helper to that affine family.
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
    have h_bad_finite : ∀ I ∈ insert I₀ F',
        {t : ℝ | ¬ (⊤ : SimpleGraph V).EdgeSetRowIndependent (p₀ + t • r) I}.Finite := by
      intro I hI
      rcases Finset.mem_insert.mp hI with rfl | hI'
      · -- `I = I₀`: LI witness is at `t = 1` (`p₀ + 1 • r = q`, where `r = q - p₀`).
        have hq_LI : LinearIndependent ℝ fun i : I =>
            (⊤ : SimpleGraph V).rigidityRow q i.val :=
          (edgeSetRowIndependent_iff_linearIndepOn_rigidityRow _ _ _).mp hq
        have hLI_one : LinearIndependent ℝ fun i : I =>
            (⊤ : SimpleGraph V).rigidityRow p₀ i.val +
              (1 : ℝ) • (⊤ : SimpleGraph V).rigidityRow r i.val := by
          convert hq_LI using 1
          funext i
          rw [hr_def, ← (⊤ : SimpleGraph V).rigidityRow_add_smul p₀ (q - p₀) 1 i.val, one_smul,
            add_sub_cancel]
        refine (LinearIndependent.finite_setOf_not_along_affine_path hLI_one).subset ?_
        intro t ht
        simp only [Set.mem_setOf_eq] at ht ⊢
        exact fun hLI => ht ((h_iff t I).mpr hLI)
      · -- `I ∈ F'`: LI witness is at `t = 0` (`p₀ + 0 • r = p₀`).
        have hp₀_LI : LinearIndependent ℝ fun i : I =>
            (⊤ : SimpleGraph V).rigidityRow p₀ i.val :=
          (edgeSetRowIndependent_iff_linearIndepOn_rigidityRow _ _ _).mp (hp₀ I hI')
        have hLI_zero : LinearIndependent ℝ fun i : I =>
            (⊤ : SimpleGraph V).rigidityRow p₀ i.val +
              (0 : ℝ) • (⊤ : SimpleGraph V).rigidityRow r i.val := by
          convert hp₀_LI using 1
          funext i
          rw [zero_smul, add_zero]
        refine (LinearIndependent.finite_setOf_not_along_affine_path hLI_zero).subset ?_
        intro t ht
        simp only [Set.mem_setOf_eq] at ht ⊢
        exact fun hLI => ht ((h_iff t I).mpr hLI)
    -- The union of bad-`t` sets across `I ∈ insert I₀ F'` is finite (finite union of finites).
    let bad : Set ℝ :=
      ⋃ I ∈ (insert I₀ F' : Finset _),
        {t : ℝ | ¬ (⊤ : SimpleGraph V).EdgeSetRowIndependent (p₀ + t • r) I}
    have h_bad_set_finite : bad.Finite :=
      (Finset.finite_toSet _).biUnion fun I hI => h_bad_finite I hI
    -- ℝ is infinite, so there's a `t : ℝ` outside the finite bad set.
    obtain ⟨t, ht_good⟩ : (badᶜ).Nonempty := by
      rw [Set.nonempty_compl]
      exact fun h_eq_univ => Set.infinite_univ (h_bad_set_finite.subset h_eq_univ.symm.le)
    -- The placement `p₀ + t • r` works on every `I ∈ insert I₀ F'`.
    refine ⟨p₀ + t • r, fun I hI => ?_⟩
    by_contra h_not_LI
    apply ht_good
    simp only [bad, Set.mem_iUnion]
    exact ⟨I, hI, h_not_LI⟩

/-- **Lovász–Yemini, linear-matroid form, dim 2.** There exists a placement `p : Framework V 2`
at which the linear rigidity matroid coincides with the combinatorial planar rigidity matroid:
`linearRigidityMatroid V 2 p = SimpleGraph.rigidityMatroid V`.

The Phase 8 target. Combines the uniform-genericity witness
`exists_uniform_rowIndependent_placement_dim_two` with `Matroid.ext_indep`: both matroids have
ground set `(⊤ : SimpleGraph V).edgeSet`, so it suffices to identify their independent sets. The
$(\Rightarrow)$ direction collapses by taking the existential placement in
`rigidityMatroid_indep_iff_edgeSetRowIndependent` to be `p`; the $(\Leftarrow)$ direction
collapses by uniform genericity, which carries any $(2, 3)$-sparse `I` to row-LI at `p`. -/
theorem linearRigidityMatroid_eq_rigidityMatroid {V : Type*} [Finite V] :
    ∃ p : Framework V 2, linearRigidityMatroid V 2 p = SimpleGraph.rigidityMatroid V := by
  obtain ⟨p, hp_uniform⟩ := exists_uniform_rowIndependent_placement_dim_two (V := V)
  refine ⟨p, Matroid.ext_indep ?_ fun J hJ => ?_⟩
  · rw [linearRigidityMatroid_ground]; rfl
  · rw [linearRigidityMatroid_ground] at hJ
    -- Factor `J : Set (Sym2 V)` with `J ⊆ (⊤).edgeSet` as `Subtype.val '' I` for
    -- `I := Subtype.val ⁻¹' J : Set (⊤).edgeSet`.
    set I : Set (⊤ : SimpleGraph V).edgeSet := Subtype.val ⁻¹' J with hI_def
    have hI_image : Subtype.val '' I = J :=
      Set.image_preimage_eq_of_subset (by rw [Subtype.range_coe]; exact hJ)
    rw [← hI_image, linearRigidityMatroid_indep_iff_edgeSetRowIndependent,
      SimpleGraph.rigidityMatroid_indep_iff_edgeSetRowIndependent]
    refine ⟨fun h => ⟨p, h⟩, fun ⟨_, hp'⟩ => ?_⟩
    -- Row-LI at *some* placement ⟹ sparse spanning subgraph (Phase 7's
    -- `edgeSet_rowIndependent_iff_isSparse_dim_two`, (⇒)) ⟹ row-LI at our uniform-generic `p`.
    exact hp_uniform _ ((edgeSet_rowIndependent_iff_isSparse_dim_two _ _).mp ⟨_, hp'⟩)

end SimpleGraph
