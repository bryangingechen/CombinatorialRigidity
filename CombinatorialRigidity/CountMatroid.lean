/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Sparsity
import Mathlib.Combinatorics.Matroid.IndepAxioms

/-!
# The `(k, ℓ)`-count matroid

Phase 7 (Commit 18). The abstract `(k, ℓ)`-count matroid on a finite vertex set `V`, in the
matroidal regime `ℓ < 2 * k` (Whiteley 1996, Lee–Streinu 2008). Its ground set is the off-
diagonal symmetric pairs `(⊤ : SimpleGraph V).edgeSet ⊆ Sym2 V`, and its independent sets are
exactly the edge subsets `I` such that `fromEdgeSet I` is `(k, ℓ)`-sparse.

Existence as a matroid is by mathlib's `IndepMatroid.ofFinite` applied to the four axioms:
* `indep_empty` — `fromEdgeSet ∅ = ⊥` is vacuously sparse (`bot_isSparse`).
* `indep_subset` — sparsity is monotone in the edge set (`IsSparse.mono_left` via
  `fromEdgeSet_mono`).
* `indep_aug` — the matroidal-regime augmentation lemma
  `IsSparse.exists_aug_of_lt_two_mul` (Sparsity.lean, Commit 17c).
* `subset_ground` — definitional from the predicate's first conjunct.

## Main definitions

* `SimpleGraph.countMatroid V k ℓ hℓ` — the `(k, ℓ)`-count matroid on `V`, where `[Finite V]`
  and `hℓ : ℓ < 2 * k`.

## Main lemmas

* `SimpleGraph.countMatroid_E` — the ground set is `(⊤ : SimpleGraph V).edgeSet`.
* `SimpleGraph.countMatroid_indep_iff` — `I` is independent iff `I ⊆ (⊤).edgeSet ∧
  (fromEdgeSet I).IsSparse k ℓ`.

The planar specialisation `SimpleGraph.rigidityMatroid V := countMatroid V 2 3 (by omega)` and
the matroid-form Lovász–Yemini live in `MatroidIdentification.lean` (Commit 19).

See `ROADMAP.md` §7, `notes/Phase7.md`, and the blueprint chapter
`blueprint/src/chapter/count-matroid.tex`.
-/

namespace SimpleGraph

variable (V : Type*) [Finite V]

/-- The `(k, ℓ)`-**count matroid** on a finite vertex set `V`, in the matroidal regime
`ℓ < 2 * k`.

Its ground set is the off-diagonal symmetric pairs `(⊤ : SimpleGraph V).edgeSet`, and an
edge set `I ⊆ Sym2 V` is independent iff `I` is contained in the ground set and `fromEdgeSet I`
is `(k, ℓ)`-sparse (`SimpleGraph.IsSparse`).

In the matroidal regime, the `(k, ℓ)`-sparse subsets are exactly the independent sets of a
matroid on `Sym2 V`; outside the regime (`ℓ ≥ 2 * k`), the augmentation axiom can fail
(e.g.\ `(3, 6)` in 3-dimensional rigidity).

See `countMatroid_indep_iff` for the independence characterisation and
`SimpleGraph.IsSparse.exists_aug_of_lt_two_mul` for the augmentation axiom that powers this
construction. -/
def countMatroid (k ℓ : ℕ) (hℓ : ℓ < 2 * k) : Matroid (Sym2 V) :=
  (IndepMatroid.ofFinite
    (E := (⊤ : SimpleGraph V).edgeSet)
    (hE := (⊤ : SimpleGraph V).edgeSet.toFinite)
    (Indep := fun I => I ⊆ (⊤ : SimpleGraph V).edgeSet ∧ (fromEdgeSet I).IsSparse k ℓ)
    (indep_empty := by
      refine ⟨Set.empty_subset _, ?_⟩
      rw [fromEdgeSet_empty]
      exact bot_isSparse k ℓ)
    (indep_subset := by
      rintro I J ⟨hJ_off, hJ_sp⟩ hIJ
      exact ⟨hIJ.trans hJ_off, hJ_sp.mono_left (fromEdgeSet_mono hIJ)⟩)
    (indep_aug := by
      classical
      rintro I J ⟨hI_off, hI_sp⟩ ⟨hJ_off, hJ_sp⟩ hcard
      obtain ⟨e, ⟨heJ, heI⟩, h_sp⟩ :=
        hI_sp.exists_aug_of_lt_two_mul hℓ hJ_sp hI_off hJ_off hcard
      refine ⟨e, heJ, heI, Set.insert_subset (hJ_off heJ) hI_off, h_sp⟩)
    (subset_ground := fun _ h => h.1)).matroid

variable {V}

@[simp] theorem countMatroid_E (k ℓ : ℕ) (hℓ : ℓ < 2 * k) :
    (countMatroid V k ℓ hℓ).E = (⊤ : SimpleGraph V).edgeSet := rfl

/-- **Independent sets of the `(k, ℓ)`-count matroid.** In the matroidal regime `ℓ < 2 * k`, an
edge subset `I ⊆ Sym2 V` is independent in `countMatroid V k ℓ` iff `I` is off-diagonal and
`fromEdgeSet I` is `(k, ℓ)`-sparse. -/
@[simp] theorem countMatroid_indep_iff (k ℓ : ℕ) (hℓ : ℓ < 2 * k) {I : Set (Sym2 V)} :
    (countMatroid V k ℓ hℓ).Indep I ↔
      I ⊆ (⊤ : SimpleGraph V).edgeSet ∧ (fromEdgeSet I).IsSparse k ℓ := Iff.rfl

end SimpleGraph
