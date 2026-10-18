/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.Data.Fin.Basic

/-!
# Mirror file: `Mathlib/Data/Fin/Basic.lean`

Upstream-eligible `OfNat` ↔ `Fin.mk` bridge lemmas. See `DESIGN.md` *Mirror directory* for
the project convention. For a `Fin n` whose `NeZero n` follows only from an inequality
hypothesis (not from a syntactic `_ + 1` shape that instance search sees), the `OfNat` numeral
literal `(i : Fin n)` is **not** defeq to `⟨i, h⟩` at a symbolic `n`: `Fin.ofNat n i =
⟨i % n, _⟩` needs `Nat.mod_eq_of_lt` to collapse the `%`, and `%` does not reduce at the
kernel level against a variable `n`. Mathlib already ships the `Nat.cast` sibling
(`Fin.natCast_eq_mk`) and the literal-`1` case (`Fin.one_eq_mk_of_lt`); this file adds the
general `OfNat.ofNat` form and its literal-`2` case.
-/

@[expose] public section

namespace Fin

/-- The general `OfNat` ↔ `Fin.mk` bridge: an `OfNat` numeral literal `(i : Fin n)` collapses
to `⟨i, h⟩` once `i < n` is known — the `NeZero n` instance needed to state the literal is
derived from `h` itself, so no instance needs to be in scope beforehand. The `OfNat` form of
`Fin.natCast_eq_mk`, and the generalization of `Fin.one_eq_mk_of_lt` (the literal-`1` case) to
an arbitrary literal `i`. -/
theorem ofNat_eq_mk {n i : ℕ} (h : i < n) :
    have : NeZero n := ⟨Nat.ne_zero_of_lt h⟩
    (OfNat.ofNat i : Fin n) = ⟨i, h⟩ := by
  have : NeZero n := ⟨Nat.ne_zero_of_lt h⟩
  apply Fin.ext
  rw [show (OfNat.ofNat i : Fin n) = Fin.ofNat n i from rfl, Fin.val_ofNat, Nat.mod_eq_of_lt h]

/-- The literal-`2` specialization of `ofNat_eq_mk`, the sibling of mathlib's own
`one_eq_mk_of_lt` at the next index. -/
theorem two_eq_mk_of_lt {n : ℕ} (h : 2 < n) :
    have : NeZero n := ⟨Nat.ne_zero_of_lt h⟩
    (2 : Fin n) = ⟨2, h⟩ :=
  ofNat_eq_mk h

end Fin
