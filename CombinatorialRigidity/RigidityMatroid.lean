/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Framework
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# The rigidity matroid

Linear-algebra infrastructure used by the `(⇒)` direction of Laman's theorem
(`IsGenericallyRigid.exists_isLaman_le` in `LamanTheorem.lean`). The eventual
home for the rigidity-matroid side of Lovász–Yemini's identification of the
rigidity matroid in dimension 2 with the `(2, 3)`-count matroid.

## Project context

Phase 4 (`Framework.lean`) deliberately kept the abstract rigidity matroid
out of the core framework API; Phase 6 stands this file up alongside it.
Per `notes/Phase6.md` *Architectural choices*, we stay matroid-agnostic in
the proof body and defer the `Mathlib.Combinatorics.Matroid` packaging:
closing `exists_isLaman_le` needs only the row-independence relation and
two linear-algebra facts (a rank lower bound at a generically rigid
placement, and `(2, 3)`-sparsity-from-row-independence). Building the
abstract `Matroid` instance is reusable infrastructure but not on the
critical path.

See `ROADMAP.md` §6, `notes/Phase6.md`, and the `(⇒)` subsection of
`blueprint/src/chapter/laman-theorem.tex`.
-/

open Module

namespace SimpleGraph

variable {V : Type*} {d : ℕ}

/-- An edge set `I ⊆ G.edgeSet` is **row-independent at a placement `p`** when the family
of edge-rows `(motion ↦ G.RigidityMap p motion e)_{e ∈ I}` — viewed as linear functionals
on `Framework V d` — is linearly independent over `ℝ`.

Equivalently (in finite dimension), the composition of `G.RigidityMap p` with the column
projection `(G.edgeSet → ℝ) → (I → ℝ)` has full rank `|I|`. The Lovász–Yemini matroid
view of rigidity declares such `I` to be the *independent sets* of the rigidity matroid of
`(G, p)`; we keep the predicate-only formulation since the Phase 6 `(⇒)` direction does not
need the abstract `Matroid` packaging. -/
def EdgeSetRowIndependent (G : SimpleGraph V) (p : Framework V d) (I : Set G.edgeSet) : Prop :=
  LinearIndepOn ℝ
    (fun e : G.edgeSet => fun motion : Framework V d => G.RigidityMap p motion e) I

/-- Row-independence at `p` is inherited by edge subsets: dropping rows from a linearly
independent family leaves a linearly independent family. -/
theorem EdgeSetRowIndependent.mono {G : SimpleGraph V} {p : Framework V d}
    {I J : Set G.edgeSet} (hI : G.EdgeSetRowIndependent p I) (h : J ⊆ I) :
    G.EdgeSetRowIndependent p J :=
  LinearIndepOn.mono hI h

/-- The empty edge set is row-independent at every placement. -/
theorem edgeSetRowIndependent_empty (G : SimpleGraph V) (p : Framework V d) :
    G.EdgeSetRowIndependent p ∅ :=
  linearIndepOn_empty ℝ _

/-- The natural injection from linear functionals to plain functions, packaged as an `ℝ`-linear
map. Mathlib provides `FunLike.coe` but not this `ℝ`-linear envelope; we use it to bridge the
function-valued `EdgeSetRowIndependent` predicate to the linear-functional `rigidityRow` family,
which lives in the finite-dimensional dual where the `dualMap` rank identities apply. -/
private noncomputable def dualToFunₗ (M : Type*) [AddCommGroup M] [Module ℝ M] :
    Module.Dual ℝ M →ₗ[ℝ] (M → ℝ) where
  toFun f := ⇑f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
private theorem dualToFunₗ_apply (M : Type*) [AddCommGroup M] [Module ℝ M]
    (f : Module.Dual ℝ M) : dualToFunₗ M f = ⇑f := rfl

private theorem dualToFunₗ_injective (M : Type*) [AddCommGroup M] [Module ℝ M] :
    Function.Injective (dualToFunₗ M) := fun _ _ h => LinearMap.ext (congrFun h)

/-- The `e`-th row of the rigidity matrix at placement `p`, viewed as a linear functional
`Framework V d →ₗ[ℝ] ℝ`. As a function, it sends `motion ↦ G.RigidityMap p motion e`. -/
noncomputable def rigidityRow (G : SimpleGraph V) (p : Framework V d) :
    G.edgeSet → Module.Dual ℝ (Framework V d) :=
  fun e => (LinearMap.proj e).comp (G.RigidityMap p)

@[simp]
theorem rigidityRow_apply (G : SimpleGraph V) (p : Framework V d) (e : G.edgeSet)
    (motion : Framework V d) : G.rigidityRow p e motion = G.RigidityMap p motion e := rfl

/-- Row-independence in the function module is equivalent to linear independence in the dual
module: the bridge between the blueprint's set-of-functions formulation and the linear-functional
`rigidityRow` family. -/
theorem edgeSetRowIndependent_iff_linearIndepOn_rigidityRow
    (G : SimpleGraph V) (p : Framework V d) (I : Set G.edgeSet) :
    G.EdgeSetRowIndependent p I ↔ LinearIndepOn ℝ (G.rigidityRow p) I := by
  change LinearIndepOn ℝ
      (fun e : G.edgeSet => dualToFunₗ (Framework V d) (G.rigidityRow p e)) I ↔ _
  exact (dualToFunₗ (Framework V d)).linearIndepOn_iff_of_injOn
    ((dualToFunₗ_injective _).injOn)

/-- The rigidity rows span the range of the transpose map. Combined with
`LinearMap.finrank_range_dualMap_eq_finrank_range` this is the row-rank-equals-column-rank
identity for the rigidity matrix. -/
theorem span_range_rigidityRow (G : SimpleGraph V) [Finite G.edgeSet] (p : Framework V d) :
    Submodule.span ℝ (Set.range (G.rigidityRow p)) =
      LinearMap.range (G.RigidityMap p).dualMap := by
  classical
  haveI : Fintype G.edgeSet := Fintype.ofFinite _
  -- Each rigidityRow e is `R.dualMap ((Pi.basisFun ℝ G.edgeSet).dualBasis e)`; the dual basis
  -- spans the whole dual; so the image under `R.dualMap` of the dual basis spans `range R.dualMap`.
  set b : Basis G.edgeSet ℝ (G.edgeSet → ℝ) := Pi.basisFun ℝ G.edgeSet
  have h_dualBasis_eq : ∀ e : G.edgeSet,
      b.dualBasis e = (LinearMap.proj e : (G.edgeSet → ℝ) →ₗ[ℝ] ℝ) := by
    intro e
    refine LinearMap.ext fun x => ?_
    simp [b, Pi.basisFun_repr]
  have h_row_eq : ∀ e : G.edgeSet,
      G.rigidityRow p e = (G.RigidityMap p).dualMap (b.dualBasis e) := by
    intro e
    refine LinearMap.ext fun x => ?_
    simp [rigidityRow, h_dualBasis_eq]
  have h_range_dualBasis : Submodule.span ℝ (Set.range b.dualBasis) = ⊤ := b.dualBasis.span_eq
  have h_range : Set.range (G.rigidityRow p) =
      (G.RigidityMap p).dualMap '' Set.range b.dualBasis := by
    ext x
    simp [h_row_eq, Set.mem_range, Set.mem_image]
  rw [h_range, Submodule.span_image, h_range_dualBasis, Submodule.map_top]

/-- **Rank lower bound at a generically rigid placement, dim 2.** If `G` is
generically rigid in dimension 2, some framework `p` realises the bound
`2 * #V ≤ rank (G.RigidityMap p) + 3`.

This is the rank half of `IsGenericallyRigid.card_mul_le_two`: the same
rank-nullity argument that gives `2 * #V ≤ #E + 3`, stopping one step
earlier (before replacing `rank` by `#E` via `rigidityMap_finrank_range_le`).
The Phase 6 `(⇒)` direction uses this lemma to extract a row-independent
edge basis of size `2 * #V - 3` from the rigidity matrix's rows. -/
theorem rigidityMap_finrank_range_ge_of_isGenericallyRigid_two [Fintype V]
    {G : SimpleGraph V} (hG : G.IsGenericallyRigid 2) :
    ∃ p : Framework V 2,
      2 * Fintype.card V ≤ Module.finrank ℝ (LinearMap.range (G.RigidityMap p)) + 3 := by
  obtain ⟨p, h_ker⟩ := hG
  refine ⟨p, ?_⟩
  have h_ker : Module.finrank ℝ (LinearMap.ker (G.RigidityMap p)) ≤ 3 := h_ker
  have h_total : Module.finrank ℝ (Framework V 2) = 2 * Fintype.card V := by
    rw [Framework.finrank, mul_comm]
  have h_rn := LinearMap.finrank_range_add_finrank_ker (G.RigidityMap p)
  omega

/-- **Row-independent edge basis at a generically rigid placement, dim 2.** If `G` is generically
rigid in dimension 2, there is a placement `p` and a row-independent edge set `I ⊆ G.edgeSet` of
size exactly `2 * #V - 3`.

Proof outline: the rank lower bound `rigidityMap_finrank_range_ge_of_isGenericallyRigid_two` gives
`2 * #V ≤ finrank ℝ (range R) + 3`. Row rank equals column rank for `R` via
`LinearMap.finrank_range_dualMap_eq_finrank_range` (after `span_range_rigidityRow` identifies the
row span with the dual-map range). Applying `exists_linearIndepOn_extension` to the row family
extracts a spanning LI subset `b`, whose cardinality is the row rank; truncating to size
`2 * #V - 3` via `Set.exists_subset_ncard_eq` yields the witness. -/
theorem exists_edgeSetRowIndependent_basis_dim_two [Fintype V] {G : SimpleGraph V}
    (hG : G.IsGenericallyRigid 2) :
    ∃ (p : Framework V 2) (I : Set G.edgeSet),
      I.ncard = 2 * Fintype.card V - 3 ∧ G.EdgeSetRowIndependent p I := by
  classical
  haveI : Fintype G.edgeSet := Set.Finite.fintype G.edgeSet.toFinite
  obtain ⟨p, hp⟩ := rigidityMap_finrank_range_ge_of_isGenericallyRigid_two hG
  refine ⟨p, ?_⟩
  -- Extend ∅ to a row-LI subset `b ⊆ univ` whose image spans the whole row family.
  obtain ⟨b, _hb_sub, _, h_range_sub, hb_li⟩ :=
    exists_linearIndepOn_extension (linearIndepOn_empty ℝ (G.rigidityRow p))
      (Set.empty_subset (Set.univ : Set G.edgeSet))
  haveI : Fintype ↥b := Fintype.ofFinite _
  -- The span of `rigidityRow '' b` equals `range R.dualMap`: forward inclusion is monotonicity
  -- of `span` (from `rigidityRow '' b ⊆ Set.range rigidityRow`) plus `span_range_rigidityRow`;
  -- reverse uses the `rigidityRow '' univ ⊆ span ...` output of `exists_linearIndepOn_extension`.
  have h_span_b : Submodule.span ℝ (G.rigidityRow p '' b) =
      LinearMap.range (G.RigidityMap p).dualMap := by
    rw [← G.span_range_rigidityRow p]
    refine le_antisymm (Submodule.span_mono (Set.image_subset_range _ _)) ?_
    rw [Submodule.span_le, ← Set.image_univ]
    exact h_range_sub
  -- `b` is an LI family spanning that submodule, so its cardinality is the finrank.
  have h_card_b : Fintype.card ↥b =
      finrank ℝ (Submodule.span ℝ (G.rigidityRow p '' b)) := by
    have h :=
      (linearIndependent_iff_card_eq_finrank_span
        (b := fun e : ↥b => G.rigidityRow p e.val)).mp hb_li
    rwa [Set.finrank, ← Set.image_eq_range] at h
  -- Chain `Fintype.card ↥b = finrank (range R.dualMap) = finrank (range R) ≥ 2 * #V - 3`.
  have h_le_card : 2 * Fintype.card V - 3 ≤ b.ncard := by
    have h1 := h_card_b
    rw [h_span_b, LinearMap.finrank_range_dualMap_eq_finrank_range] at h1
    rw [Set.ncard_eq_card_coe]
    omega
  -- Truncate `b` to a subset `I ⊆ b` with `|I| = 2 * #V - 3`.
  obtain ⟨I, hI_sub, hI_card⟩ := Set.exists_subset_card_eq h_le_card
  refine ⟨I, hI_card, ?_⟩
  exact (edgeSetRowIndependent_iff_linearIndepOn_rigidityRow G p I).mpr (hb_li.mono hI_sub)

end SimpleGraph
