/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.Data.Set.Card

/-!
# Upstream candidates: small `Set.ncard` lemmas

The Lean namespace is the upstream one (`Set`), so promotion to mathlib is a
copy-paste. See `DESIGN.md` "Mirror directory".

## Contents (target file: `Mathlib/Data/Set/Card.lean`)

* `Set.ncard_pair_le` — `({a, b} : Set α).ncard ≤ 2`. Unconditional companion
  to `Set.ncard_pair` (which gives `= 2` under `a ≠ b`); collapses the
  `ncard_insert_le` + `ncard_singleton` boilerplate when bounding the
  cardinality of a literal pair without first ruling out collisions.
* `Set.ncard_triple_le` — `({a, b, c} : Set α).ncard ≤ 3`. Same pattern,
  one level deeper.
* `Set.ncard_eq_card_coe` — `s.ncard = Fintype.card s` under `[Fintype s]`.
  Bridges `Set.ncard` to the `Fintype.card`-based dimension lemmas
  (`Module.finrank_pi`, `LinearMap.toMatrix`) without the
  `Set.ncard_eq_toFinset_card'` / `Set.toFinset_card` two-step rewrite.
* `Set.exists_injective_fin_of_le_ncard` — from `n ≤ s.ncard`, index `n`
  distinct elements of `s` by `Fin n`. Companion to `Set.exists_subset_card_eq`
  (which returns the subset); collapses the `exists_subset_card_eq` →
  `Set.Finite.fintype` → `Set.ncard_eq_toFinset_card'` /
  `Set.toFinset_card` → `Fintype.equivFinOfCardEq` chain.
* `Set.ncard_union_range_of_injective` — adding `k` new elements, listed injectively by
  `Fin k`, adds `k` to the cardinality: `(s ∪ range z).ncard = s.ncard + k`. Fuses
  `Set.ncard_union_eq`, the disjointness of `s` and `range z`, `Set.ncard_range_of_injective`
  and `Nat.card_fin`. The combinatorial-rigidity project uses it to count the bodies of an ear
  or of a chain of bridges in `Molecular/Molecule/Pencil/MainComponent/` (`Cut.lean`,
  `Ear.lean`, `Short.lean`, `Orbit.lean`, `SplitOff.lean`).
-/

@[expose] public section

namespace Set

variable {α : Type*}

/-- An unconditional bound for the cardinality of a literal pair: it is at most `2`
regardless of whether `a = b`. The companion `Set.ncard_pair` gives the exact `= 2`
under `a ≠ b`. -/
theorem ncard_pair_le (a b : α) : ({a, b} : Set α).ncard ≤ 2 :=
  (ncard_insert_le _ _).trans (by rw [ncard_singleton])

/-- An unconditional bound for the cardinality of a literal triple: it is at most `3`
regardless of any equalities among `a, b, c`. -/
theorem ncard_triple_le (a b c : α) : ({a, b, c} : Set α).ncard ≤ 3 :=
  (ncard_insert_le _ _).trans (Nat.add_le_add_right (ncard_pair_le _ _) _)

/-- A direct bridge between `Set.ncard` and `Fintype.card`: `s.ncard = Fintype.card ↥s`
under `[Fintype s]`. The `Set.ncard_eq_toFinset_card'` (`s.ncard = s.toFinset.card`) +
`Set.toFinset_card` (`s.toFinset.card = Fintype.card s`) two-step rewrite collapses to
this one lemma. -/
theorem ncard_eq_card_coe (s : Set α) [Fintype s] : s.ncard = Fintype.card s := by
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]

/-- From `n ≤ s.ncard`, index `n` distinct elements of `s` by `Fin n`. Companion to
`Set.exists_subset_card_eq`: that lemma returns the size-`n` subset; this one returns
the `Fin n`-indexing of its elements. -/
theorem exists_injective_fin_of_le_ncard {s : Set α} {n : ℕ} (hns : n ≤ s.ncard) :
    ∃ q : Fin n → α, Function.Injective q ∧ ∀ i, q i ∈ s := by
  obtain ⟨t, hts, hcard⟩ := Set.exists_subset_card_eq hns
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  · have ht_fin : t.Finite := Set.finite_of_ncard_pos (hcard ▸ hn)
    have : Fintype t := ht_fin.fintype
    have h_card_eq : Fintype.card t = n := (Set.ncard_eq_card_coe t).symm.trans hcard
    let e : Fin n ≃ t := (Fintype.equivFinOfCardEq h_card_eq).symm
    exact ⟨fun i => (e i).val, fun _ _ hij => e.injective (Subtype.ext hij),
      fun i => hts (e i).property⟩

/-- Adding `k` new elements, listed injectively by `Fin k`, to a finite set adds `k` to its
cardinality: `s` and `range z` are disjoint, and `range z` has `k` elements. -/
theorem ncard_union_range_of_injective {s : Set α} {k : ℕ} {z : Fin k → α}
    (hz : Function.Injective z) (hzs : ∀ i, z i ∉ s) (hs : s.Finite := by toFinite_tac) :
    (s ∪ range z).ncard = s.ncard + k := by
  rw [ncard_union_eq (disjoint_right.mpr (forall_mem_range.mpr hzs)) hs
    (image_univ (f := z) ▸ finite_univ.image z), ncard_range_of_injective hz, Nat.card_fin]

end Set
