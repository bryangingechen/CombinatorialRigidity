/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
# Upstream candidates: cardinality of the complement of a singleton finset, and of ordered pairs

Companion of `Finset.coe_compl_singleton` in
`CombinatorialRigidity/Mathlib/Data/Finset/BooleanAlgebra.lean`. The
`card` form requires `Fintype α`, so it lands next to `Finset.card_compl`
in `Mathlib/Data/Fintype/Card.lean`.

`Fintype.card_subtype_fst_lt_snd` counts the strictly-increasing ordered pairs of a linearly-ordered
fintype as `(Fintype.card α).choose 2`, via the bijection with two-element subsets
(`Fintype.card_finset_len`). It belongs alongside `Sym2.card` / `Fintype.card_finset_len`.

The Lean namespaces are the upstream ones (`Finset`, `Fintype`), not the project's, so
promotion is a copy-paste alongside `Finset.card_compl` / `Fintype.card_finset_len`. See
`DESIGN.md` "Mirror directory".

## Contents (target files: `Mathlib/Data/Fintype/Card.lean`, `Mathlib/Data/Fintype/Powerset.lean`)

* `Finset.card_compl_singleton` — `(({a} : Finset α)ᶜ).card = Fintype.card α - 1`.
* `Fintype.card_subtype_fst_lt_snd` —
  `Fintype.card {q : α × α // q.1 < q.2} = (Fintype.card α).choose 2`.
-/

@[expose] public section

namespace Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

@[simp]
theorem card_compl_singleton (a : α) :
    (({a} : Finset α)ᶜ).card = Fintype.card α - 1 := by
  rw [card_compl, card_singleton]

end Finset

namespace Fintype

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- **The strictly-increasing ordered pairs of a linearly-ordered fintype number
`(Fintype.card α).choose 2`.** The subtype `{q : α × α // q.1 < q.2}` of ordered pairs is in
bijection with the two-element subsets `{s : Finset α // s.card = 2}` — a pair `(i, j)` with
`i < j` maps to `{i, j}`, and a two-element set maps to its increasing enumeration
`(orderEmbOfFin 0, orderEmbOfFin 1)` — so the count is `(Fintype.card α).choose 2`
(`Fintype.card_finset_len`). -/
theorem card_subtype_fst_lt_snd :
    Fintype.card {q : α × α // q.1 < q.2} = (Fintype.card α).choose 2 := by
  classical
  -- The increasing enumeration of the pair `{i, j}` (with `i < j`) is `![i, j]`.
  have hemb : ∀ {i j : α} (hij : i < j),
      (({i, j} : Finset α).orderEmbOfFin
        (Finset.card_pair (ne_of_lt hij)) : Fin 2 → α) = ![i, j] :=
    fun {i j} hij => (Finset.orderEmbOfFin_unique _
      (fun x => by fin_cases x <;> simp)
      (by intro x y hxy; fin_cases x <;> fin_cases y <;> simp_all)).symm
  rw [← Fintype.card_finset_len (α := α) 2]
  apply Fintype.card_congr
  refine
    { toFun := fun q => ⟨{q.1.1, q.1.2}, by rw [Finset.card_pair (ne_of_lt q.2)]⟩
      invFun := fun s =>
        ⟨(s.1.orderEmbOfFin s.2 0, s.1.orderEmbOfFin s.2 1), by
          exact (s.1.orderEmbOfFin s.2).strictMono (by decide)⟩
      left_inv := ?_
      right_inv := ?_ }
  · rintro ⟨⟨i, j⟩, hij⟩
    simp only [Subtype.mk.injEq, Prod.mk.injEq]
    rw [hemb hij]
    exact ⟨rfl, rfl⟩
  · rintro ⟨s, hs⟩
    -- `orderEmbOfFin 0`, `orderEmbOfFin 1` are exactly the two elements of `s` (its range), so
    -- `{orderEmbOfFin 0, orderEmbOfFin 1} = s`.
    refine Subtype.ext ?_
    rw [← Finset.coe_inj, Finset.coe_insert, Finset.coe_singleton,
      ← Finset.range_orderEmbOfFin s hs]
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
    constructor
    · rintro (rfl | rfl); exacts [⟨0, rfl⟩, ⟨1, rfl⟩]
    · rintro ⟨y, rfl⟩; fin_cases y <;> simp

end Fintype
