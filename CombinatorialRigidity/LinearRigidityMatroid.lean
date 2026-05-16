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

end SimpleGraph
