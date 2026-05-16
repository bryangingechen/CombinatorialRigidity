/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.GroupTheory.CosetCover
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Upstream candidate: affine version of `Subspace.biUnion_ne_univ_of_top_notMem`

Mathlib's `Mathlib.GroupTheory.CosetCover` proves that a vector space over an infinite
division ring cannot be covered by finitely many proper linear subspaces
(`Subspace.biUnion_ne_univ_of_top_notMem`). The same statement holds for proper *affine*
subspaces, with essentially the same proof: each non-empty affine subspace is a coset
of its direction submodule, so an affine cover lifts to an additive-coset cover, and the
general `AddSubgroup.exists_finiteIndex_of_leftCoset_cover` finishes via the usual
finite-quotient / infinite-base contradiction.

The affine version subsumes the "finite union of points plus proper linear subspaces"
shape that arises in generic-position arguments, since each point is a 0-dim affine
subspace.

Upstream target: a new file `Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Cover.lean`
(parallel to `Mathlib/GroupTheory/CosetCover.lean` but in the affine-space hierarchy,
importing `GroupTheory.CosetCover` for the underlying `AddSubgroup` machinery and
`AffineSubspace.Defs` for the affine API).

## Main results

* `AffineSubspace.biUnion_ne_univ_of_top_notMem` — a vector space over an infinite
  division ring is not a finite union of proper affine subspaces.
* `AffineSubspace.affineSpan_ne_top_of_ncard_le_finrank` — a finite set in a
  finite-dimensional vector space whose cardinality is at most `finrank` has an
  affine span that is not the whole space. Natural upstream home is
  `Mathlib/LinearAlgebra/AffineSpace/FiniteDimensional.lean` (alongside
  `finrank_vectorSpan_image_finset_le`).
-/

@[expose] public section

open scoped Pointwise

namespace AffineSubspace

variable {k V : Type*} [DivisionRing k] [Infinite k]
    [AddCommGroup V] [Module k V]
    {s : Finset (AffineSubspace k V)}

/-- A vector space over an infinite division ring cannot be a finite union of proper
affine subspaces. -/
theorem biUnion_ne_univ_of_top_notMem (hs : ⊤ ∉ s) :
    ⋃ p ∈ s, (p : Set V) ≠ Set.univ := by
  intro hcovers
  classical
  -- Drop empty affine subspaces from the cover; they contribute nothing.
  set s' : Finset (AffineSubspace k V) :=
    s.filter (fun p : AffineSubspace k V => (p : Set V).Nonempty) with hs'_def
  have hs'_sub : s' ⊆ s := Finset.filter_subset _ _
  have h_top_notmem' : ⊤ ∉ s' := fun h => hs (hs'_sub h)
  have hs'_cov : ⋃ p ∈ s', (p : Set V) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    have hx : x ∈ ⋃ p ∈ s, (p : Set V) := hcovers ▸ Set.mem_univ x
    rcases Set.mem_iUnion₂.mp hx with ⟨p, hp, hxp⟩
    exact Set.mem_iUnion₂.mpr
      ⟨p, Finset.mem_filter.mpr ⟨hp, ⟨x, hxp⟩⟩, hxp⟩
  -- Choose a basepoint for each non-empty subspace.
  choose b hb using fun p (hp : p ∈ s') => (Finset.mem_filter.mp hp).2
  -- Each non-empty `p ∈ s'` is the coset `b p hp +ᵥ p.direction.toAddSubgroup`.
  have hcoset : ∀ p (hp : p ∈ s'),
      (p : Set V) = b p hp +ᵥ (p.direction.toAddSubgroup : Set V) := by
    intro p hp
    ext x
    rw [Set.mem_vadd_set]
    refine ⟨fun hx => ⟨x - b p hp, ?_, by simp⟩, ?_⟩
    · have := AffineSubspace.vsub_mem_direction hx (hb p hp)
      simpa using this
    · rintro ⟨d, hd, rfl⟩
      have : d +ᵥ b p hp ∈ p :=
        AffineSubspace.vadd_mem_of_mem_direction (by simpa using hd) (hb p hp)
      simpa [add_comm] using this
  -- Re-express the cover with cosets of direction submodules, indexed by `s'.attach`.
  have h_addcov : ⋃ q ∈ s'.attach, b q.1 q.2 +ᵥ
      (q.1.direction.toAddSubgroup : Set V) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    have hx : x ∈ ⋃ p ∈ s', (p : Set V) := hs'_cov ▸ Set.mem_univ x
    rcases Set.mem_iUnion₂.mp hx with ⟨p, hp, hxp⟩
    refine Set.mem_iUnion₂.mpr ⟨⟨p, hp⟩, Finset.mem_attach _ _, ?_⟩
    rw [hcoset p hp] at hxp
    exact hxp
  -- Apply the additive coset-cover theorem and contradict.
  obtain ⟨q, _hq_mem, _hq_fi⟩ :=
    AddSubgroup.exists_finiteIndex_of_leftCoset_cover h_addcov
  set p := q.1 with hp_def
  have hp_in_s' : p ∈ s' := q.2
  have hp_ne_top : p ≠ ⊤ := fun h => h_top_notmem' (h ▸ hp_in_s')
  have hdir_ne_top : p.direction ≠ ⊤ := by
    intro hdir
    apply hp_ne_top
    rw [← AffineSubspace.mk'_eq (hb p hp_in_s'), hdir]
    simp
  have : Finite (V ⧸ p.direction) := AddSubgroup.finite_quotient_of_finiteIndex
  have : Nontrivial (V ⧸ p.direction) :=
    Submodule.Quotient.nontrivial_iff.mpr hdir_ne_top
  have : Infinite (V ⧸ p.direction) := Module.Free.infinite k (V ⧸ p.direction)
  exact not_finite (V ⧸ p.direction)

end AffineSubspace

section ProperAffineSpan

variable {k V : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]

open Module in
/-- A finite set in a finite-dimensional vector space whose cardinality does not exceed
`finrank` has an affine span that is not the whole space. Generalizes "a single point
spans no more than itself" and "two points span at most a line" — useful for ruling out
`affineSpan k s = ⊤` from a cardinality bound, e.g., the proper-affine-subspaces
side-condition of `AffineSubspace.biUnion_ne_univ_of_top_notMem`. -/
theorem AffineSubspace.affineSpan_ne_top_of_ncard_le_finrank
    [FiniteDimensional k V] [Nontrivial V]
    {s : Set V} (hsf : s.Finite) (hs : s.ncard ≤ finrank k V) :
    affineSpan k s ≠ ⊤ := by
  intro h_top
  rcases s.eq_empty_or_nonempty with rfl | hs_ne
  · -- `s = ∅`: `affineSpan = ⊥ ≠ ⊤`.
    exact AffineSubspace.bot_ne_top _ _ _ ((AffineSubspace.span_empty k V V) ▸ h_top)
  · -- `s` nonempty: `finrank (vectorSpan k s) + 1 ≤ s.ncard`, but `vectorSpan = ⊤` from
    -- `h_top` would force `finrank V + 1 ≤ s.ncard ≤ finrank V`, contradiction.
    haveI : Fintype s := hsf.fintype
    haveI : Nonempty s := hs_ne.to_subtype
    have h_le : finrank k (vectorSpan k s) + 1 ≤ s.ncard := by
      have h := finrank_vectorSpan_range_add_one_le k (Subtype.val : s → V)
      rw [Subtype.range_val] at h
      rwa [Set.ncard_eq_toFinset_card s hsf, hsf.card_toFinset]
    rw [(AffineSubspace.vectorSpan_eq_top_of_affineSpan_eq_top _ _ _ h_top), finrank_top] at h_le
    omega

end ProperAffineSpan
