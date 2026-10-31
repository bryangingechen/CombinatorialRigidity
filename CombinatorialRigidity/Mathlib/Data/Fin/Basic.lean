/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.Data.Fin.SuccPred

/-!
# Upstream candidates: `i + 1` in `Fin` across `succAbove`

The project inserts a vertex into a closed polygon (`Fin.insertNth` into a `Fin n`-indexed
cycle, `Molecular/Molecule/Pencil/Grade/Polygon.lean`), so it reads the cyclic successor `j + 1`
of an index before and after `i.succ.succAbove`. These are the index facts that make the
inserted polygon's edges line up with the old ones.

The Lean namespace is the upstream one (`Fin`), so promotion to mathlib is a copy-paste. See
`DESIGN.md` "Mirror directory".

## Contents (target file: `Mathlib/Data/Fin/Basic.lean`)

* `Fin.val_add_one'` — the value of `a + 1` in `Fin (n + 1)`: `0` at the top, else `a + 1`
  (the `Nat.mod`-free companion of `Fin.val_add_one`).
* `Fin.val_succ_succAbove` — the value of `i.succ.succAbove j`: `j` up to `i`, else `j + 1`.
* `Fin.succ_succAbove_add_one` — for `j ≠ i`, `i.succ.succAbove j + 1 = i.succ.succAbove (j + 1)`:
  the cyclic successor commutes with the insertion away from the insertion point.
* `Fin.succ_add_one_eq_succAbove` — `i.succ + 1 = i.succ.succAbove (i + 1)`: the successor of the
  inserted point is the old successor of `i`.
* `Fin.succ_succAbove_self` — `i.succ.succAbove i = i.castSucc`: the old `i` stays at `i`.
-/

@[expose] public section

namespace Fin

theorem val_add_one' {n : ℕ} (a : Fin (n + 1)) :
    ((a + 1 : Fin (n + 1)) : ℕ) = if (a : ℕ) = n then 0 else (a : ℕ) + 1 := by
  split_ifs with h
  · obtain rfl : a = Fin.last n := Fin.ext h
    simp
  · have := a.isLt
    rw [Fin.val_add_one_of_lt (Fin.lt_def.2 (by simp only [Fin.val_last]; omega))]

theorem val_succ_succAbove {n : ℕ} (i j : Fin (n + 1)) :
    ((i.succ.succAbove j : Fin (n + 2)) : ℕ) = if (j : ℕ) ≤ i then (j : ℕ) else (j : ℕ) + 1 := by
  unfold Fin.succAbove
  have := j.isLt
  split_ifs with h1 h2 h2 <;>
    simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at h1 ⊢ <;> omega

theorem succ_succAbove_add_one {n : ℕ} (i j : Fin (n + 1)) (h : j ≠ i) :
    i.succ.succAbove j + 1 = i.succ.succAbove (j + 1) := by
  have h' : (j : ℕ) ≠ i := fun e => h (Fin.ext e)
  have hj := j.isLt
  have hi := i.isLt
  rw [Fin.ext_iff, Fin.val_add_one', Fin.val_succ_succAbove, Fin.val_succ_succAbove,
    Fin.val_add_one']
  split_ifs <;> omega

theorem succ_add_one_eq_succAbove {n : ℕ} (i : Fin (n + 1)) :
    i.succ + 1 = i.succ.succAbove (i + 1) := by
  have hi := i.isLt
  rw [Fin.ext_iff, Fin.val_add_one', Fin.val_succ_succAbove, Fin.val_add_one', Fin.val_succ]
  split_ifs <;> omega

theorem succ_succAbove_self {n : ℕ} (i : Fin (n + 1)) :
    i.succ.succAbove i = i.castSucc :=
  Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_succ)

end Fin
