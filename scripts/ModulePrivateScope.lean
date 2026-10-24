/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.Order.Antichain

/-!
# Which proofs inside an exposed definition may name a private declaration

A witness for `CombinatorialRigidity/LEAN-OPS.md` *What a conversion breaks*, written for Phase
41a's item P5 (`notes/PERFORMANCE.md` *The conversion, layers 19–38*). Under the file-wide
`@[expose] public section`, a `def`'s body is public scope. A proof inside it is too, a `have` in
its tactic block included, even one proved by a nested `by`; only a `by` block given as a term,
such as a proof argument, is elaborated in private scope. So `flatScrewEquiv`
(`Pencil/MainComponent/Flat.lean`) could not name its private helpers in a `have`, while
`Matroid.ofSubmodular` (`Matroid/Constructions/Submodular.lean`) names its own inside proof
arguments.

Run `lake lean scripts/ModulePrivateScope.lean` from the repository root. Expected (Lean
v4.36.0-rc1): `Unknown identifier` at `d1`, `d2` and `d3`, and nothing at `d4`.
-/

@[expose] public section

private theorem privThm (n : Nat) : 0 ≤ n := Nat.zero_le n

/-- A term-mode `have` in a definition's tactic body: public scope. -/
def d1 : Nat := by
  have _h : 0 ≤ 1 := privThm 1
  exact 1

/-- The same `have`, proved by a nested `by`: still public scope. -/
def d2 : Nat := by
  have _h : 0 ≤ 1 := by exact privThm 1
  exact 1

/-- A proof field given as a term: public scope. -/
def d3 : {n : Nat // 0 ≤ n} := ⟨1, privThm 1⟩

/-- A proof field given as a `by` block: private scope, so the private theorem resolves. -/
def d4 : {n : Nat // 0 ≤ n} := ⟨1, by exact privThm 1⟩
