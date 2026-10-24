/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.Order.Antichain
public import Mathlib.Data.Finset.Basic

/-!
# A private name in an exposed body resolves to a public homonym

A witness for `CombinatorialRigidity/LEAN-OPS.md` *What a conversion breaks*, written for Phase
41a's item P3 (`notes/PERFORMANCE.md` *The conversion, layers 0–8*). Under the file-wide
`@[expose] public section`, a `def`'s body is public scope, where a `private` declaration does not
resolve. When a public declaration of the same name sits in an enclosing namespace, the name
resolves to it instead. Here the private lemma copies the one that
`Matroid/Constructions/Submodular` carried until P3, and mathlib's root `setOf_minimal_antichain`
is a deprecated alias.

Run `lake lean scripts/ModulePrivateHomonym.lean` from the repository root. Expected: exactly one
warning, the deprecation, at `exposedUse`; `proofUse`, a theorem's proof and so private scope, uses
the private lemma silently. Deleting the `module` line, the `public` keywords and the `@[expose]
public section` line gives a non-`module` copy, which does not warn (beyond Lake's advice to add
`module` to a file that imports mathlib).
-/

@[expose] public section

namespace Matroid

variable {α : Type*}

private lemma setOf_minimal_antichain (P : Finset α → Prop) :
    IsAntichain (· ⊆ ·) {C | Minimal P C} := by
  intro C₁ hC₁ C₂ hC₂ hne hle
  exact hne <| le_antisymm hle (hC₂.2 hC₁.1 hle)

/-- An exposed body: the name resolves to mathlib's deprecated root alias. -/
def exposedUse (P : Finset α → Prop) : Unit :=
  have _h := setOf_minimal_antichain P
  ()

/-- A theorem's proof is private scope: the name resolves to the private lemma. -/
theorem proofUse (P : Finset α → Prop) : IsAntichain (· ⊆ ·) {C | Minimal P C} :=
  setOf_minimal_antichain P

end Matroid
