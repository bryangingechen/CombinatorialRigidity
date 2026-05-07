/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import Mathlib.Data.Sym.Sym2

/-!
# Upstream candidates: pointwise reasoning about `Sym2.map f e = s(x, y)`

Mathlib has `Sym2.mem_map` for membership of a single element of `β` in
`Sym2.map f z`, and `Sym2.coe_map` for the underlying-set coercion. What was
missing — and repeatedly needed in the combinatorial-rigidity project — is a
*pointwise* characterization, in terms of `f`-preimages, of the situation
"there is an `e` with property `P` such that `Sym2.map f e` equals a specific
ordered pair `s(x, y)`."

The main lemma here is `Sym2.exists_and_map_eq_mk_iff`:

```
(∃ e, P e ∧ Sym2.map f e = s(x, y)) ↔ ∃ p q, f p = x ∧ f q = y ∧ P s(p, q)
```

This is the form that `simp` reaches automatically: starting from
`s(x, y) ∈ Sym2.map f '' S`, the lemma `Set.mem_image` (a `@[simp]` lemma)
unfolds to `∃ e, e ∈ S ∧ Sym2.map f e = s(x, y)`, after which membership in `S`
may have been further unfolded by other simp lemmas (e.g. `Set.mem_diff` if `S`
is a difference). The predicate-form lemma matches regardless.

We also provide the more direct (non-`@[simp]`) form
`Sym2.mk_mem_image_map_iff`, which talks about image membership before
`Set.mem_image` fires; it is convenient for hand-driven rewriting. The `f =
some` specializations close the loop for the `Option`-vertex extensions used in
this project.

The Lean namespace is the upstream one (`Sym2`), so promotion to mathlib is a
copy-paste alongside `Sym2.mem_map` / `Sym2.coe_map`. See
`Archive/CombinatorialRigidity/DESIGN.md` "Mirror directory".

## Contents (target file: `Mathlib/Data/Sym/Sym2.lean`)

* `Sym2.exists_and_map_eq_mk_iff` — `(∃ e, P e ∧ Sym2.map f e = s(x, y)) ↔
  ∃ p q, f p = x ∧ f q = y ∧ P s(p, q)`. Tagged `@[simp]`.
* `Sym2.mk_mem_image_map_iff` — image-membership form:
  `s(x, y) ∈ Sym2.map f '' S ↔ ∃ p q, f p = x ∧ f q = y ∧ s(p, q) ∈ S`.
* `Sym2.mk_mem_image_map_some_iff` — `f = some` specialization, recasting the
  `f p = x` / `f q = y` clauses with `some` on the right (the orientation that
  matches `rcases x with _ | u` case splits).
-/

namespace Sym2

variable {α β : Type*}

/-- "Predicate-form" pointwise inverse of `Sym2.map`: a value `s(x, y)` is in
the image of an `e` satisfying `P` iff there is a preimage pair `(p, q)` with
`f p = x`, `f q = y`, and `P s(p, q)`. The asymmetry in `(p, q)` is harmless by
`Sym2.eq_swap`.

This is the form that survives `simp`'s unfolding of `Set.mem_image` and any
further unfolding of the membership predicate (e.g. `Set.mem_diff` for set
differences). Tagged `@[simp]` so image-membership goals close in one pass. -/
@[simp]
lemma exists_and_map_eq_mk_iff {f : α → β} {P : Sym2 α → Prop} {x y : β} :
    (∃ e, P e ∧ Sym2.map f e = s(x, y)) ↔ ∃ p q, f p = x ∧ f q = y ∧ P s(p, q) := by
  constructor
  · rintro ⟨e, hP, hmap⟩
    induction e with | h α' β' => ?_
    rw [Sym2.map_mk, Sym2.eq_iff] at hmap
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hmap
    · exact ⟨_, _, rfl, rfl, hP⟩
    · exact ⟨_, _, rfl, rfl, by rwa [Sym2.eq_swap]⟩
  · rintro ⟨p, q, rfl, rfl, hP⟩
    exact ⟨s(p, q), hP, by rw [Sym2.map_mk]⟩

/-- An ordered-pair edge `s(x, y)` lies in `Sym2.map f '' S` iff there is a
preimage pair `(p, q)` with `f p = x`, `f q = y`, and `s(p, q) ∈ S`.

This is the "natural" hand-driven form. The companion `simp`-form
`Sym2.exists_and_map_eq_mk_iff` is what fires inside an automated rewrite. -/
lemma mk_mem_image_map_iff {f : α → β} {S : Set (Sym2 α)} {x y : β} :
    s(x, y) ∈ Sym2.map f '' S ↔ ∃ p q, f p = x ∧ f q = y ∧ s(p, q) ∈ S := by
  rw [Set.mem_image]
  exact exists_and_map_eq_mk_iff

/-- `Option`-edge specialization of `Sym2.mk_mem_image_map_iff`: the membership
question for `Sym2.map (some : α → Option α) '' S` factors cleanly through
"both endpoints are `some _`" plus membership of the corresponding honest edge.
The `x = some p` orientation (rather than `some p = x`) matches what `rcases x
with _ | u` produces. -/
lemma mk_mem_image_map_some_iff {S : Set (Sym2 α)} {x y : Option α} :
    s(x, y) ∈ Sym2.map (some : α → Option α) '' S ↔
      ∃ p q, x = some p ∧ y = some q ∧ s(p, q) ∈ S := by
  rw [mk_mem_image_map_iff]
  exact exists₂_congr fun _ _ => and_congr eq_comm (and_congr eq_comm Iff.rfl)

end Sym2
