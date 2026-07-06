/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.LinearRigidityMatroid

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

This file lands the first four nodes of the forward-mode chapter
`blueprint/src/chapter/bar-joint-3d.tex`: `IsGenericPlacement`, its existence
`exists_isGenericPlacement`, the matroid `genericRigidityMatroid` (`Matroid.ofFun` packaging at a
chosen generic placement), its independence characterization `genericRigidityMatroid_indep_iff`,
and placement-independence `linearRigidityMatroid_eq_genericRigidityMatroid`. The remaining
chapter (the dimension-two reconciliation and the rank function) lands in later Phase 24 commits.

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

end SimpleGraph
