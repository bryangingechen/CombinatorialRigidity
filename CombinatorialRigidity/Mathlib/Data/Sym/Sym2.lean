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
`DESIGN.md` "Mirror directory".

## Contents (target file: `Mathlib/Data/Sym/Sym2.lean`)

* `Sym2.exists_and_map_eq_mk_iff` — `(∃ e, P e ∧ Sym2.map f e = s(x, y)) ↔
  ∃ p q, f p = x ∧ f q = y ∧ P s(p, q)`. Tagged `@[simp]`.
* `Sym2.mk_mem_image_map_iff` — image-membership form:
  `s(x, y) ∈ Sym2.map f '' S ↔ ∃ p q, f p = x ∧ f q = y ∧ s(p, q) ∈ S`.
* `Sym2.mk_mem_image_map_some_iff` — `f = some` specialization, recasting the
  `f p = x` / `f q = y` clauses with `some` on the right (the orientation that
  matches `rcases x with _ | u` case splits).
* `Sym2.map_some_injective` — `Sym2.map (some : α → Option α)` is injective.
  A common specialization that otherwise reads as
  `Sym2.map.injective (Option.some_injective _)`.
* `Sym2.notMem_map_some` — `none ∉ Sym2.map some e`. Tagged `@[simp]`.
* `Sym2.disjoint_image_map_some` — disjointness packaging: `Sym2.map some '' S`
  is disjoint from any `T` whose elements all contain `none`.
* `Sym2.coe_toFinset` — the `Set`-coercion of `z.toFinset` equals the
  `SetLike` coercion of `z`. Tagged `@[simp]` so `e.toFinset ⊆ C` and
  `(↑e : Set α) ⊆ (↑C : Set α)` interconvert in one rewrite (paired with
  `Finset.coe_subset`).
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

/-- `Sym2.map (some : α → Option α)` is injective. The named specialization of
`Sym2.map.injective` that arises whenever an `Option`-vertex extension counts edges
via `Set.ncard_image_of_injective`. -/
lemma map_some_injective : Function.Injective (Sym2.map (some : α → Option α)) :=
  Sym2.map.injective (Option.some_injective α)

/-- `none` is never an endpoint of `Sym2.map some e`: the image of any edge `e : Sym2 α`
under `some : α → Option α` has both endpoints in the `some`-branch of `Option α`. -/
lemma notMem_map_some (e : Sym2 α) :
    none ∉ Sym2.map (some : α → Option α) e := by
  rw [Sym2.mem_map]
  rintro ⟨_, _, h⟩
  exact Option.some_ne_none _ h

/-- The image `Sym2.map some '' S` is disjoint from any `T ⊆ Sym2 (Option α)` whose
elements all contain `none` as an endpoint. The typical use is when `T` is a literal
set of "fresh" edges of the form `s(none, some _)`. -/
theorem disjoint_image_map_some {S : Set (Sym2 α)} {T : Set (Sym2 (Option α))}
    (hT : ∀ e ∈ T, none ∈ e) : Disjoint (Sym2.map some '' S) T := by
  rw [Set.disjoint_left]
  rintro _ ⟨e, _, rfl⟩ heT
  exact notMem_map_some e (hT _ heT)

/-- The `Set`-coercion of `z.toFinset` equals the `SetLike` coercion of `z` itself.
Tagged `@[simp]` so the `Sym2.toFinset` cast canonicalizes to the underlying `SetLike`
coercion in goals like `e.toFinset ⊆ C ↔ (↑e : Set α) ⊆ (↑C : Set α)`. Not `norm_cast`
because both sides are coe functions; `norm_cast`'s direction-of-simplification heuristic
requires the RHS to have strictly fewer coes than the LHS. -/
@[simp]
lemma coe_toFinset [DecidableEq α] (z : Sym2 α) : (z.toFinset : Set α) = (↑z : Set α) := by
  ext x
  rw [Finset.mem_coe, Sym2.mem_toFinset, SetLike.mem_coe]

end Sym2
