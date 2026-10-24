/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.Chart

/-!
# Distinct standard basis vectors in the slots of a selector

A step of the proof of part (a) of `lem:pencil-generic-steer` (`sec:main-component-statements`): for
a hub `h` of `G` with two neighbours `w₁` and `w₂`, whose other neighbours are not hubs, parameters
of the chart at which the points of `h`, `w₁` and `w₂` are linearly independent. Each body `w` has
the standard basis vector `e_{idx w}` of `K⁴` as its `hubNormal`, for an index map
`idx : α → Fin 4`, and the empty slots of the hub selectors at the three bodies are standard basis
vectors too, so that at each of them the three slots are distinct basis vectors other than some
`e_d`, with a different `d` at each body. The point of each is then a nonzero multiple of its `e_d`
(`exists_smul_pencilChartPoint_of_hubSlotNormal_eq_pi_single`, `Engine.lean`), and the three points
are independent.

This file gives the indices of the slots (`exists_injective_extension_of_isFin3SelectorOf`): for a
selector of a set on which `idx` is injective and differs from `d`, an injective `σ : Fin 3 → Fin 4`
that differs from `d` and is `idx w` at the slot of each member `w`. The empty slots take indices
that the members leave, as `Fin 4` has four elements and at most three are taken. Which these are
depends on the indices of the members, so the proof takes the eight cases of which slots are empty.
`exists_coord_linearIndependent_pencilChartPoint_of_other_nonhub`
(`MainComponent/GenericSteer.lean`) uses it.
-/

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K]
variable {α β : Type*}

/-! ## The indices of the slots of a selector -/

/-- **An element of `Fin 4` other than three given ones**, as `Fin 4` has four elements. It is the
index of the empty slot of a selector with two members, and gives the next two lemmas. -/
private theorem exists_fin4_ne_ne_ne (a b c : Fin 4) : ∃ x : Fin 4, x ≠ a ∧ x ≠ b ∧ x ≠ c := by
  by_contra hcon
  push Not at hcon
  have hsub : (Finset.univ : Finset (Fin 4)) ⊆ {a, b, c} := by
    intro x _
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases hxa : x = a
    · exact Or.inl hxa
    by_cases hxb : x = b
    · exact Or.inr (Or.inl hxb)
    exact Or.inr (Or.inr (hcon x hxa hxb))
  have hle := Finset.card_le_card hsub
  have h3 : ({a, b, c} : Finset (Fin 4)).card ≤ 3 :=
    (Finset.card_insert_le _ _).trans (Nat.add_le_add_right
      ((Finset.card_insert_le _ _).trans (Nat.add_le_add_right
        (Finset.card_singleton c).le 1)) 1)
  rw [Finset.card_univ, Fintype.card_fin] at hle
  omega

/-- **Two distinct elements of `Fin 4` other than two given ones**: the indices of the empty slots
of a selector with one member. -/
private theorem exists_fin4_pair_ne_ne (a b : Fin 4) : ∃ x y : Fin 4,
    x ≠ y ∧ x ≠ a ∧ x ≠ b ∧ y ≠ a ∧ y ≠ b := by
  obtain ⟨x, hxa, hxb, -⟩ := exists_fin4_ne_ne_ne a b b
  obtain ⟨y, hya, hyb, hyx⟩ := exists_fin4_ne_ne_ne a b x
  exact ⟨x, y, hyx.symm, hxa, hxb, hya, hyb⟩

/-- **Three distinct elements of `Fin 4` other than a given one**: the indices of the slots of a
selector with no member. -/
private theorem exists_fin4_triple_ne (d : Fin 4) : ∃ x y z : Fin 4,
    x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ x ≠ d ∧ y ≠ d ∧ z ≠ d := by
  obtain ⟨x, hxd, -, -⟩ := exists_fin4_ne_ne_ne d d d
  obtain ⟨y, hyd, hyx, -⟩ := exists_fin4_ne_ne_ne d x x
  obtain ⟨z, hzd, hzx, hzy⟩ := exists_fin4_ne_ne_ne d x y
  exact ⟨x, y, z, hyx.symm, hzx.symm, hzy.symm, hxd, hyd, hzd⟩

/-- **`![x, y, z]` is injective when `x`, `y` and `z` are distinct.** -/
private theorem injective_vec3 {x y z : Fin 4} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    Function.Injective (![x, y, z] : Fin 3 → Fin 4) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exact absurd hij hxy
  · exact absurd hij hxz
  · exact absurd hij.symm hxy
  · rfl
  · exact absurd hij hyz
  · exact absurd hij.symm hxz
  · exact absurd hij.symm hyz
  · rfl

/-- **`![x, y, z]` differs from `d` at every index when `x`, `y` and `z` do.** -/
private theorem vec3_ne {x y z d : Fin 4} (hx : x ≠ d) (hy : y ≠ d) (hz : z ≠ d) :
    ∀ i, (![x, y, z] : Fin 3 → Fin 4) i ≠ d := by
  intro i
  fin_cases i
  · exact hx
  · exact hy
  · exact hz

/-- **Distinct indices other than `d` for the slots of a selector** (a step of
`lem:pencil-generic-steer`): for a selector `sel` of `S` and an index map `idx` injective on `S`
with `idx w ≠ d` for `w ∈ S`, there is an injective `σ : Fin 3 → Fin 4` with `σ i ≠ d` for every `i`
and `σ i = idx w` whenever `sel` puts `w` in slot `i`. With `e_{σ i}` in slot `i`, the three slots
are distinct standard basis vectors other than `e_d`, and their `cross₃` is a nonzero multiple of
`e_d` (`exists_smul_cross₃_pi_single`, `Engine.lean`). The indices of the empty slots depend on
those of the members, as an index fixed for a slot alone can be that of a member in another slot.
The proof takes the eight cases of which slots are empty, and the three lemmas above give the
indices of the empty ones. -/
theorem exists_injective_extension_of_isFin3SelectorOf {S : Set α} {sel : Fin 3 → Option α}
    (hsel : IsFin3SelectorOf S sel) {idx : α → Fin 4} {d : Fin 4}
    (hd : ∀ w ∈ S, idx w ≠ d) (hinj : Set.InjOn idx S) :
    ∃ σ : Fin 3 → Fin 4, Function.Injective σ ∧ (∀ i, σ i ≠ d) ∧
      ∀ i w, sel i = some w → σ i = idx w := by
  have hkey : ∀ {i j : Fin 3} {x y : α}, sel i = some x → sel j = some y → i ≠ j →
      idx x ≠ idx y := by
    intro i j x y hx hy hij hxy
    obtain rfl : x = y := hinj (hsel.1 i x hx) (hsel.1 j y hy) hxy
    exact hij (hsel.2.2 i j x hx hy)
  have hopt : ∀ o : Option α, o = none ∨ ∃ x, o = some x := by
    intro o
    cases o
    · exact Or.inl rfl
    · exact Or.inr ⟨_, rfl⟩
  have hmatch3 : ∀ {σ : Fin 3 → Fin 4} {o0 o1 o2 : Option α},
      sel 0 = o0 → sel 1 = o1 → sel 2 = o2 →
      (∀ w, o0 = some w → σ 0 = idx w) →
      (∀ w, o1 = some w → σ 1 = idx w) →
      (∀ w, o2 = some w → σ 2 = idx w) →
      ∀ i w, sel i = some w → σ i = idx w := by
    intro σ o0 o1 o2 hs0 hs1 hs2 hm0 hm1 hm2 i w hw
    fin_cases i
    · exact hm0 w (by rw [← hs0]; exact hw)
    · exact hm1 w (by rw [← hs1]; exact hw)
    · exact hm2 w (by rw [← hs2]; exact hw)
  have hnone : ∀ (σv : Fin 4) (w : α), (none : Option α) = some w → σv = idx w :=
    fun _ w hw => nomatch hw
  have hsome : ∀ (σv : Fin 4) (u : α), σv = idx u → ∀ w, some u = some w → σv = idx w := by
    intro σv u hσ w hw
    obtain rfl := Option.some_injective _ hw
    exact hσ
  rcases hopt (sel 0) with h0 | ⟨a, h0⟩ <;> rcases hopt (sel 1) with h1 | ⟨b, h1⟩ <;>
    rcases hopt (sel 2) with h2 | ⟨c, h2⟩
  · -- `none, none, none`
    obtain ⟨x, y, z, hxy, hxz, hyz, hxd, hyd, hzd⟩ := exists_fin4_triple_ne d
    exact ⟨![x, y, z], injective_vec3 hxy hxz hyz, vec3_ne hxd hyd hzd,
      hmatch3 h0 h1 h2 (hnone _) (hnone _) (hnone _)⟩
  · -- `none, none, some c`
    have hcd := hd c (hsel.1 2 c h2)
    obtain ⟨x, y, hxy, hxc, hxd, hyc, hyd⟩ := exists_fin4_pair_ne_ne (idx c) d
    exact ⟨![x, y, idx c], injective_vec3 hxy hxc hyc, vec3_ne hxd hyd hcd,
      hmatch3 h0 h1 h2 (hnone _) (hnone _) (hsome _ c rfl)⟩
  · -- `none, some b, none`
    have hbd := hd b (hsel.1 1 b h1)
    obtain ⟨x, y, hxy, hxb, hxd, hyb, hyd⟩ := exists_fin4_pair_ne_ne (idx b) d
    exact ⟨![x, idx b, y], injective_vec3 hxb hxy hyb.symm, vec3_ne hxd hbd hyd,
      hmatch3 h0 h1 h2 (hnone _) (hsome _ b rfl) (hnone _)⟩
  · -- `none, some b, some c`
    have hbd := hd b (hsel.1 1 b h1)
    have hcd := hd c (hsel.1 2 c h2)
    have hbc : idx b ≠ idx c := hkey h1 h2 (by decide)
    obtain ⟨x, hxb, hxc, hxd⟩ := exists_fin4_ne_ne_ne (idx b) (idx c) d
    exact ⟨![x, idx b, idx c], injective_vec3 hxb hxc hbc, vec3_ne hxd hbd hcd,
      hmatch3 h0 h1 h2 (hnone _) (hsome _ b rfl) (hsome _ c rfl)⟩
  · -- `some a, none, none`
    have had := hd a (hsel.1 0 a h0)
    obtain ⟨x, y, hxy, hxa, hxd, hya, hyd⟩ := exists_fin4_pair_ne_ne (idx a) d
    exact ⟨![idx a, x, y], injective_vec3 hxa.symm hya.symm hxy, vec3_ne had hxd hyd,
      hmatch3 h0 h1 h2 (hsome _ a rfl) (hnone _) (hnone _)⟩
  · -- `some a, none, some c`
    have had := hd a (hsel.1 0 a h0)
    have hcd := hd c (hsel.1 2 c h2)
    have hac : idx a ≠ idx c := hkey h0 h2 (by decide)
    obtain ⟨x, hxa, hxc, hxd⟩ := exists_fin4_ne_ne_ne (idx a) (idx c) d
    exact ⟨![idx a, x, idx c], injective_vec3 hxa.symm hac hxc, vec3_ne had hxd hcd,
      hmatch3 h0 h1 h2 (hsome _ a rfl) (hnone _) (hsome _ c rfl)⟩
  · -- `some a, some b, none`
    have had := hd a (hsel.1 0 a h0)
    have hbd := hd b (hsel.1 1 b h1)
    have hab : idx a ≠ idx b := hkey h0 h1 (by decide)
    obtain ⟨x, hxa, hxb, hxd⟩ := exists_fin4_ne_ne_ne (idx a) (idx b) d
    exact ⟨![idx a, idx b, x], injective_vec3 hab hxa.symm hxb.symm, vec3_ne had hbd hxd,
      hmatch3 h0 h1 h2 (hsome _ a rfl) (hsome _ b rfl) (hnone _)⟩
  · -- `some a, some b, some c`
    have had := hd a (hsel.1 0 a h0)
    have hbd := hd b (hsel.1 1 b h1)
    have hcd := hd c (hsel.1 2 c h2)
    have hab : idx a ≠ idx b := hkey h0 h1 (by decide)
    have hac : idx a ≠ idx c := hkey h0 h2 (by decide)
    have hbc : idx b ≠ idx c := hkey h1 h2 (by decide)
    exact ⟨![idx a, idx b, idx c], injective_vec3 hab hac hbc, vec3_ne had hbd hcd,
      hmatch3 h0 h1 h2 (hsome _ a rfl) (hsome _ b rfl) (hsome _ c rfl)⟩

end CombinatorialRigidity.Molecular
