/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.Engine

/-!
# The collision-free slot assignment on the pencil chart (Phase 39 PENCIL, W5-L5 L5-cut-v-b)

The padding mechanism for explicit chart seeds (`notes/Phase39-design.md` §"W5 leaf
decomposition" L5-cut-v, the "v-b construction recipe", as corrected): assign bodies standard basis
vectors of `K⁴` as hub normals through an index map `idx`, and fill each padding slot with a fresh
basis vector, so that a body's slot triple consists of three *distinct* basis vectors avoiding a
designated target index `d`. `cross₃` of such a triple is a nonzero multiple of `e_d`
(`exists_smul_cross₃_pi_single`), so distinct targets give independent points
(`linearIndependent_pi_single_triple` + `LinearIndependent.units_smul`).

`exists_injective_extension_of_isFin3SelectorOf`: given any selector for a body's closed
hub-neighbourhood whose selected members carry distinct non-target indices, the slot-indexed index
map extends to an *injective* `Fin 3 → Fin 4` avoiding the target — an eight-way case split on the
selector's `some`/`none` shape, each padding slot picked fresh by a `4 > 3` counting argument over
`Fin 4`. The one case split lives here, abstractly, instead of being repeated per body and per
hub-status combination. Its consumer is the hub witness (MC-188),
`exists_coord_linearIndependent_pencilChartPoint_of_other_nonhub`
(`MainComponent/GenericSteer.lean`).

See `notes/Phase39.md`, `notes/Phase39-design.md` (§"W5 leaf decomposition" L5-cut-v), and
`blueprint/src/chapter/main-component.tex` (`lem:pencil-generic-steer`; no blueprint node of its
own — unnamed technical infra).
-/

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K]
variable {α β : Type*}

/-! ## The collision-free slot assignment (Phase 39 W5-L5, L5-cut-v-b)

The padding-slot extension lemma and its three `Fin 4` pick facts. The pick facts are `4 > 3`
counting statements over `Fin 4`; the extension lemma does the one `some`/`none` shape split the
whole construction needs. -/

/-- **`Fin 4` has an element avoiding any three** (Phase 39 W5-L5, L5-cut-v-b pick fact, a
counting argument — `4 > 3`): used to fill the single padding slot of an arity-`2` selector,
and the base pick the other two pick facts iterate. -/
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

/-- **`Fin 4` has two distinct elements avoiding any two** (Phase 39 W5-L5, L5-cut-v-b pick fact,
iterating the base pick): used to fill the two padding slots of an arity-`1` selector. -/
private theorem exists_fin4_pair_ne_ne (a b : Fin 4) : ∃ x y : Fin 4,
    x ≠ y ∧ x ≠ a ∧ x ≠ b ∧ y ≠ a ∧ y ≠ b := by
  obtain ⟨x, hxa, hxb, -⟩ := exists_fin4_ne_ne_ne a b b
  obtain ⟨y, hya, hyb, hyx⟩ := exists_fin4_ne_ne_ne a b x
  exact ⟨x, y, hyx.symm, hxa, hxb, hya, hyb⟩

/-- **`Fin 4` has three distinct elements avoiding any one** (Phase 39 W5-L5, L5-cut-v-b pick
fact, iterating the base pick): used to fill all three padding slots of an arity-`0` selector. -/
private theorem exists_fin4_triple_ne (d : Fin 4) : ∃ x y z : Fin 4,
    x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ x ≠ d ∧ y ≠ d ∧ z ≠ d := by
  obtain ⟨x, hxd, -, -⟩ := exists_fin4_ne_ne_ne d d d
  obtain ⟨y, hyd, hyx, -⟩ := exists_fin4_ne_ne_ne d x x
  obtain ⟨z, hzd, hzx, hzy⟩ := exists_fin4_ne_ne_ne d x y
  exact ⟨x, y, z, hyx.symm, hzx.symm, hzy.symm, hxd, hyd, hzd⟩

/-- **A `Fin 3`-vector of pairwise-distinct values is injective** (Phase 39 W5-L5, L5-cut-v-b
technical glue for the extension lemma below). -/
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

/-- **A `Fin 3`-vector of values avoiding `d` avoids `d` at every index** (Phase 39 W5-L5,
L5-cut-v-b technical glue for the extension lemma below). -/
private theorem vec3_ne {x y z d : Fin 4} (hx : x ≠ d) (hy : y ≠ d) (hz : z ≠ d) :
    ∀ i, (![x, y, z] : Fin 3 → Fin 4) i ≠ d := by
  intro i
  fin_cases i
  · exact hx
  · exact hy
  · exact hz

/-- **A selector-compatible basis-index assignment extends to an injective slot map**
(Phase 39 W5-L5, L5-cut-v-b, the padding mechanism): given a `Fin 3`-selector for `S` and an
index map `idx` that is injective on `S` and avoids a designated target index `d` there, there is
an *injective* `σ : Fin 3 → Fin 4`, still avoiding `d`, that reads `idx w` at every slot the
selector assigns to a member `w` — the padding slots are filled with fresh indices by the pick
facts above, per the selector's eight `some`/`none` shapes. Consumed with
`Pi.single (σ i) 1` as slot `i`'s normal: the slot triple is then three distinct standard basis
vectors avoiding `e_d`, so its `cross₃` is a nonzero multiple of `e_d`
(`exists_smul_cross₃_pi_single`). This is the corrected form of the design doc's padding plans:
no fixed function of the slot index alone can avoid collisions (a pigeonhole fact), and the
assignment here depends on the selector's actual shape. -/
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
