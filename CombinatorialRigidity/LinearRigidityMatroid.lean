/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.MatroidIdentification
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
  sorry

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
