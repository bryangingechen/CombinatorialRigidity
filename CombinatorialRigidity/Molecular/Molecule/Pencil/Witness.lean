/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.Engine

/-!
# The pendant-cut somewhere-witnesses on the pencil chart (Phase 39 PENCIL, W5-L5 L5-cut-v)

The L5-cut-v chart-steering discharge's somewhere-witness constructions
(`notes/Phase39-design.md` §"W5 leaf decomposition" L5 "Cut-arm route verdict", the L5-cut-v
bullet): explicit seeds at which the chart's constructed data is nondegenerate at the pendant-cut
configuration's three distinguished bodies, feeding the polynomial-steering leaves (v-d/v-e/v-f)
through `pencilChartPointPoly`'s eval identity. This file carries **witness (i)** (L5-cut-v-b):
on `G`'s own chart, under the sub-case-4 pendant configuration (`G.degree u_c = 3`, cut edge
`e_c : u_c–v_c`, the two `V₁`-links `e₁ : u_c–w₁`, `e₂ : u_c–w₂`), some seed coordinate `q` makes
the three constructed points at `u_c`, `w₁`, `w₂` linearly independent —
`exists_coord_linearIndependent_pencilChartPoint_of_pendant_deg3`.

**The construction** (the design doc's "v-b construction recipe", as corrected): assign every
body a standard basis vector of `K⁴` as its hub normal via a global index map `idx` —
`u_c ↦ e₀`, `w₁ ↦ e₁`, `w₂ ↦ e₂`, a hub `v_c ↦` whichever of `e₁`/`e₂` is not claimed by a hub
`w₁`/`w₂`, and every third-party hub `↦ e₃` — and fill each padding slot with a fresh basis
vector so that each of the three bodies' slot triples consists of three *distinct* basis vectors
avoiding a designated target index (`3` at `u_c`, `2` at `w₁`, `1` at `w₂`). `cross₃` of such a
triple is a nonzero multiple of the target basis vector (`exists_smul_cross₃_pi_single`), and the
three targets are distinct, so the three points are independent
(`linearIndependent_pi_single_triple` + `LinearIndependent.units_smul`).

Two combinatorial exclusions make the assignment injective on each closed hub-neighbourhood
(re-derived in `notes/Phase39-design.md`, "the two facts that make this watertight"): a non-hub
`w₁`/`w₂` has at most one extra hub-neighbour beyond `u_c` (`Graph.PencilHub`'s own degree bound,
sharper than the blanket `ncard ≤ 3` feasibility bound), and neither `w₁` nor `w₂` is adjacent to
the other when either is a hub (else `u_c, w₁, w₂` is a triangle with two adjacent hubs,
infeasible by `not_pencilNondegFeasible_of_triangle_two_hubs`, the v-a lemma); `v_c` is never
adjacent to `w₁`/`w₂` at all (`Graph.not_adj_of_ne_of_mem_of_cutEdges_le_one`, a second crossing
edge would violate the `≤ 1` cut bound).

**The padding mechanism** (`exists_injective_extension_of_isFin3SelectorOf`): given any selector
for a body's closed hub-neighbourhood whose selected members carry distinct non-target basis
indices, the slot-indexed index map extends to an *injective* `Fin 3 → Fin 4` avoiding the
target — an eight-way case split on the selector's `some`/`none` shape, each padding slot picked
fresh by a `4 > 3` counting argument over `Fin 4`. This supersedes both the flat `index`-formula
plan and the `fin_cases`-per-vertex plan the design doc's earlier passes recorded: the one case
split lives here, abstractly, instead of being repeated per body and per hub-status combination.

See `notes/Phase39.md`, `notes/Phase39-design.md` (§"W5 leaf decomposition" L5-cut-v), and
`blueprint/src/chapter/pencil.tex` (no blueprint node — unnamed technical infra, as the sibling
L5-cut leaves).
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

/-! ## Witness (i): the somewhere-witness on `G`'s chart (Phase 39 W5-L5, L5-cut-v-b) -/

/-- **The pendant-cut somewhere-witness on `G`'s chart** (Phase 39 W5-L5, L5-cut-v-b; the pinned
witness (i) of `notes/Phase39-design.md` §"W5 leaf decomposition" L5-cut-v): under the sub-case-4
pendant configuration (`G.degree u_c = 3`, cut edge `e_c : u_c–v_c` the only crossing edge, the
two `V₁`-links `e₁ : u_c–w₁`, `e₂ : u_c–w₂`) with `G` simple and nondegeneracy-feasible, and for
*any* hub selector correct at every body, some seed coordinate `q` makes the chart's constructed
points at `u_c`, `w₁`, `w₂` linearly independent. Feeds the steering leaves (v-d/v-e) through
`pencilChartPointPoly_eval`: linear independence at one seed makes the corresponding rows-minor
polynomial somewhere-nonzero.

Construction: the file docstring's global basis-index assignment `idx` and per-body slot
extensions. Feasibility enters three times, always through combinatorics: the `≤ 3` cardinality
bound (`ncard_closedHubNbhd_le_three_of_isNondegPencilRealization`) bars all three of
`v_c, w₁, w₂` being hubs (and third parties at a hub `w₁`/`w₂`), and the v-a triangle lemma
(`not_pencilNondegFeasible_of_triangle_two_hubs`) bars `w₁ ~ w₂` whenever either is a hub —
exactly the collision `idx` could not otherwise avoid. -/
theorem exists_coord_linearIndependent_pencilChartPoint_of_pendant_deg3
    [Finite α] [Finite β] {G : Graph α β} {V₁ : Set α} {e_c e₁ e₂ : β} {u_c v_c w₁ w₂ : α}
    (hSimple : G.Simple) (hfeas : PencilNondegFeasible K G)
    (hl_c : G.IsLink e_c u_c v_c) (hu_c : u_c ∈ V₁) (hv_c : v_c ∉ V₁)
    (hcut : (G.cutEdges V₁).ncard ≤ 1) (hdeg : G.degree u_c = 3)
    (hl₁ : G.IsLink e₁ u_c w₁) (hl₂ : G.IsLink e₂ u_c w₂)
    (hw₁ : w₁ ∈ V₁) (hw₂ : w₂ ∈ V₁) (hw12 : w₁ ≠ w₂)
    (hubSel : α → Fin 3 → Option α)
    (hHubSel : ∀ v, IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v)) :
    ∃ q : α × Fin 4 × Fin 4 → K,
      LinearIndependent K
        ![pencilChartPoint (PencilSeed.ofCoord q) hubSel u_c,
          pencilChartPoint (PencilSeed.ofCoord q) hubSel w₁,
          pencilChartPoint (PencilSeed.ofCoord q) hubSel w₂] := by
  classical
  haveI := hSimple
  -- Distinctness of the four named vertices, and `u_c`'s hub status.
  have hw1u : w₁ ≠ u_c := hl₁.ne.symm
  have hw2u : w₂ ≠ u_c := hl₂.ne.symm
  have hvcu : v_c ≠ u_c := hl_c.ne.symm
  have hv1 : v_c ≠ w₁ := by rintro rfl; exact hv_c hw₁
  have hv2 : v_c ≠ w₂ := by rintro rfl; exact hv_c hw₂
  have hub_u : G.PencilHub u_c := ⟨hl_c.left_mem, by omega⟩
  -- The feasibility cardinality bound at every body.
  obtain ⟨F₀, nrm₀, pt₀, hnd₀⟩ := id hfeas
  have hcard : ∀ v ∈ V(G), (G.closedHubNbhd v).ncard ≤ 3 := fun v hv =>
    ncard_closedHubNbhd_le_three_of_isNondegPencilRealization hnd₀ hv
  -- `u_c`'s neighbours are exactly `{v_c, w₁, w₂}` (degree `3` + `Simple`).
  have hN : N(G, u_c) = ({v_c, w₁, w₂} : Set α) :=
    Graph.neighbor_eq_of_degree_eq_three hSimple hl_c hl₁ hl₂ hv1 hv2 hw12 hdeg
  have hSu : ∀ x ∈ G.closedHubNbhd u_c, x = u_c ∨ x = v_c ∨ x = w₁ ∨ x = w₂ := by
    rintro x ⟨-, h | ⟨e, he⟩⟩
    · exact Or.inl h
    · have hxN : x ∈ N(G, u_c) := he.adj
      rw [hN] at hxN
      rcases hxN with rfl | rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
  -- Not all three of `v_c, w₁, w₂` are hubs (the `≤ 3` bound at `u_c` itself).
  have hnotall : ¬ (G.PencilHub v_c ∧ G.PencilHub w₁ ∧ G.PencilHub w₂) := by
    rintro ⟨hcv, hh1, hh2⟩
    have hsub : ({u_c, v_c, w₁, w₂} : Set α) ⊆ G.closedHubNbhd u_c := by
      rintro z (rfl | rfl | rfl | rfl)
      · exact ⟨hub_u, Or.inl rfl⟩
      · exact ⟨hcv, Or.inr ⟨e_c, hl_c⟩⟩
      · exact ⟨hh1, Or.inr ⟨e₁, hl₁⟩⟩
      · exact ⟨hh2, Or.inr ⟨e₂, hl₂⟩⟩
    have h4card : ({u_c, v_c, w₁, w₂} : Set α).ncard = 4 := by
      rw [Set.ncard_insert_of_notMem (by simp [Ne.symm hvcu, Ne.symm hw1u, Ne.symm hw2u]),
        Set.ncard_insert_of_notMem (by simp [hv1, hv2]),
        Set.ncard_insert_of_notMem (by simp [hw12]), Set.ncard_singleton]
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    have hb := hcard u_c hl_c.left_mem
    rw [h4card] at hle
    omega
  -- The v-a triangle exclusions: `w₁ ~ w₂` is barred whenever either is a hub.
  have hw2_nadj1 : G.PencilHub w₂ → ¬ G.Adj w₁ w₂ := by
    rintro hh2 ⟨e₃, he₃⟩
    exact not_pencilNondegFeasible_of_triangle_two_hubs hw1u (Ne.symm hw2u) hw12
      hl₁.symm hl₂ he₃.symm hub_u hh2 hfeas
  have hw1_nadj2 : G.PencilHub w₁ → ¬ G.Adj w₂ w₁ := by
    rintro hh1 ⟨e₃, he₃⟩
    exact not_pencilNondegFeasible_of_triangle_two_hubs hw2u (Ne.symm hw1u) (Ne.symm hw12)
      hl₂.symm hl₁ he₃.symm hub_u hh1 hfeas
  -- The cut-bound exclusion: `v_c` is adjacent to no `V₁`-member other than `u_c`.
  have hvc_nadj : ∀ x, x ∈ V₁ → x ≠ u_c → ¬ G.Adj v_c x := fun x hx hxu =>
    Graph.not_adj_of_ne_of_mem_of_cutEdges_le_one hl_c hu_c hv_c hcut hx hxu
  -- Membership exclusions at `w₁`'s and `w₂`'s closed hub-neighbourhoods.
  have hnvc_1 : v_c ∉ G.closedHubNbhd w₁ := by
    rintro ⟨-, h | ⟨e, he⟩⟩
    · exact hv1 h
    · exact hvc_nadj w₁ hw₁ hw1u ⟨e, he.symm⟩
  have hnvc_2 : v_c ∉ G.closedHubNbhd w₂ := by
    rintro ⟨-, h | ⟨e, he⟩⟩
    · exact hv2 h
    · exact hvc_nadj w₂ hw₂ hw2u ⟨e, he.symm⟩
  have hnw2_1 : w₂ ∉ G.closedHubNbhd w₁ := by
    rintro ⟨hh2, h | ⟨e, he⟩⟩
    · exact hw12 h.symm
    · exact hw2_nadj1 hh2 ⟨e, he⟩
  have hnw1_2 : w₁ ∉ G.closedHubNbhd w₂ := by
    rintro ⟨hh1, h | ⟨e, he⟩⟩
    · exact hw12 h
    · exact hw1_nadj2 hh1 ⟨e, he⟩
  -- At most one third-party member at `w₁` (hub: the `≤ 3` bound; non-hub: degree `≤ 2`).
  have huniq_1 : ∀ x ∈ G.closedHubNbhd w₁, ∀ y ∈ G.closedHubNbhd w₁,
      x ≠ u_c → x ≠ w₁ → y ≠ u_c → y ≠ w₁ → x = y := by
    intro x hx y hy hxu hxw hyu hyw
    by_contra hxy
    obtain ⟨hxhub, hx' | ⟨ex, hex⟩⟩ := hx
    · exact hxw hx'
    obtain ⟨hyhub, hy' | ⟨ey, hey⟩⟩ := hy
    · exact hyw hy'
    by_cases h1 : G.PencilHub w₁
    · have hsub4 : ({w₁, u_c, x, y} : Set α) ⊆ G.closedHubNbhd w₁ := by
        rintro z (rfl | rfl | rfl | rfl)
        · exact ⟨h1, Or.inl rfl⟩
        · exact ⟨hub_u, Or.inr ⟨e₁, hl₁.symm⟩⟩
        · exact ⟨hxhub, Or.inr ⟨ex, hex⟩⟩
        · exact ⟨hyhub, Or.inr ⟨ey, hey⟩⟩
      have h4card : ({w₁, u_c, x, y} : Set α).ncard = 4 := by
        rw [Set.ncard_insert_of_notMem (by simp [hw1u, Ne.symm hxw, Ne.symm hyw]),
          Set.ncard_insert_of_notMem (by simp [Ne.symm hxu, Ne.symm hyu]),
          Set.ncard_insert_of_notMem (by simp [hxy]), Set.ncard_singleton]
      have hle := Set.ncard_le_ncard hsub4 (Set.toFinite _)
      have hb := hcard w₁ hl₁.right_mem
      rw [h4card] at hle
      omega
    · have hdeg1 : G.degree w₁ ≤ 2 := by
        by_contra hcon
        exact h1 ⟨hl₁.right_mem, by omega⟩
      have hsub3 : ({u_c, x, y} : Set α) ⊆ N(G, w₁) := by
        rintro z (rfl | rfl | rfl)
        · exact hl₁.symm.adj
        · exact ⟨ex, hex⟩
        · exact ⟨ey, hey⟩
      have h3card : ({u_c, x, y} : Set α).ncard = 3 :=
        Set.ncard_eq_three.mpr ⟨u_c, x, y, Ne.symm hxu, Ne.symm hyu, hxy, rfl⟩
      have hle := Set.ncard_le_ncard hsub3 (Set.toFinite _)
      rw [h3card, ← Graph.degree_eq_ncard_adj] at hle
      omega
  -- At most one third-party member at `w₂` (the mirror argument).
  have huniq_2 : ∀ x ∈ G.closedHubNbhd w₂, ∀ y ∈ G.closedHubNbhd w₂,
      x ≠ u_c → x ≠ w₂ → y ≠ u_c → y ≠ w₂ → x = y := by
    intro x hx y hy hxu hxw hyu hyw
    by_contra hxy
    obtain ⟨hxhub, hx' | ⟨ex, hex⟩⟩ := hx
    · exact hxw hx'
    obtain ⟨hyhub, hy' | ⟨ey, hey⟩⟩ := hy
    · exact hyw hy'
    by_cases h2 : G.PencilHub w₂
    · have hsub4 : ({w₂, u_c, x, y} : Set α) ⊆ G.closedHubNbhd w₂ := by
        rintro z (rfl | rfl | rfl | rfl)
        · exact ⟨h2, Or.inl rfl⟩
        · exact ⟨hub_u, Or.inr ⟨e₂, hl₂.symm⟩⟩
        · exact ⟨hxhub, Or.inr ⟨ex, hex⟩⟩
        · exact ⟨hyhub, Or.inr ⟨ey, hey⟩⟩
      have h4card : ({w₂, u_c, x, y} : Set α).ncard = 4 := by
        rw [Set.ncard_insert_of_notMem (by simp [hw2u, Ne.symm hxw, Ne.symm hyw]),
          Set.ncard_insert_of_notMem (by simp [Ne.symm hxu, Ne.symm hyu]),
          Set.ncard_insert_of_notMem (by simp [hxy]), Set.ncard_singleton]
      have hle := Set.ncard_le_ncard hsub4 (Set.toFinite _)
      have hb := hcard w₂ hl₂.right_mem
      rw [h4card] at hle
      omega
    · have hdeg2 : G.degree w₂ ≤ 2 := by
        by_contra hcon
        exact h2 ⟨hl₂.right_mem, by omega⟩
      have hsub3 : ({u_c, x, y} : Set α) ⊆ N(G, w₂) := by
        rintro z (rfl | rfl | rfl)
        · exact hl₂.symm.adj
        · exact ⟨ex, hex⟩
        · exact ⟨ey, hey⟩
      have h3card : ({u_c, x, y} : Set α).ncard = 3 :=
        Set.ncard_eq_three.mpr ⟨u_c, x, y, Ne.symm hxu, Ne.symm hyu, hxy, rfl⟩
      have hle := Set.ncard_le_ncard hsub3 (Set.toFinite _)
      rw [h3card, ← Graph.degree_eq_ncard_adj] at hle
      omega
  -- The global basis-index assignment.
  set idx : α → Fin 4 := fun x =>
    if x = u_c then 0 else if x = w₁ then 1 else if x = w₂ then 2
    else if x = v_c then (if G.PencilHub w₁ then 2 else 1) else 3 with hidx_def
  have hidx_u : idx u_c = 0 := by simp [hidx_def]
  have hidx_1 : idx w₁ = 1 := by simp [hidx_def, hw1u]
  have hidx_2 : idx w₂ = 2 := by simp [hidx_def, hw2u, Ne.symm hw12]
  have hidx_v : idx v_c = if G.PencilHub w₁ then 2 else 1 := by
    simp [hidx_def, hvcu, hv1, hv2]
  have hidx_vor : idx v_c = 2 ∨ idx v_c = 1 := by
    rw [hidx_v]
    by_cases h : G.PencilHub w₁ <;> simp [h]
  have hidx_x : ∀ x, x ≠ u_c → x ≠ w₁ → x ≠ w₂ → x ≠ v_c → idx x = 3 := by
    intro x h1 h2 h3 h4
    simp [hidx_def, h1, h2, h3, h4]
  -- Classification at `w₁`/`w₂`: members are `u_c`, the body itself, or a third party at `e₃`.
  have hSw1 : ∀ x ∈ G.closedHubNbhd w₁, x = u_c ∨ x = w₁ ∨ idx x = 3 := by
    intro x hx
    by_cases h1 : x = u_c
    · exact Or.inl h1
    by_cases h2 : x = w₁
    · exact Or.inr (Or.inl h2)
    refine Or.inr (Or.inr (hidx_x x h1 h2 ?_ ?_))
    · rintro rfl; exact hnw2_1 hx
    · rintro rfl; exact hnvc_1 hx
  have hSw2 : ∀ x ∈ G.closedHubNbhd w₂, x = u_c ∨ x = w₂ ∨ idx x = 3 := by
    intro x hx
    by_cases h1 : x = u_c
    · exact Or.inl h1
    by_cases h2 : x = w₂
    · exact Or.inr (Or.inl h2)
    refine Or.inr (Or.inr (hidx_x x h1 ?_ h2 ?_))
    · rintro rfl; exact hnw1_2 hx
    · rintro rfl; exact hnvc_2 hx
  -- The per-body target avoidance and injectivity.
  have hd_u : ∀ x ∈ G.closedHubNbhd u_c, idx x ≠ (3 : Fin 4) := by
    intro x hx
    rcases hSu x hx with rfl | rfl | rfl | rfl
    · rw [hidx_u]; decide
    · rcases hidx_vor with h | h <;> rw [h] <;> decide
    · rw [hidx_1]; decide
    · rw [hidx_2]; decide
  have hinj_u : Set.InjOn idx (G.closedHubNbhd u_c) := by
    intro x hx y hy hxy
    rcases hSu x hx with rfl | rfl | rfl | rfl <;> rcases hSu y hy with rfl | rfl | rfl | rfl
    · rfl
    · rcases hidx_vor with h | h <;> rw [hidx_u, h] at hxy <;> exact absurd hxy (by decide)
    · rw [hidx_u, hidx_1] at hxy; exact absurd hxy (by decide)
    · rw [hidx_u, hidx_2] at hxy; exact absurd hxy (by decide)
    · rcases hidx_vor with h | h <;> rw [h, hidx_u] at hxy <;> exact absurd hxy (by decide)
    · rfl
    · rw [hidx_v, hidx_1, ite_eq_left hy.1] at hxy; exact absurd hxy (by decide)
    · have hnh1 : ¬ G.PencilHub w₁ := fun h => hnotall ⟨hx.1, h, hy.1⟩
      rw [hidx_v, hidx_2, ite_eq_right hnh1] at hxy; exact absurd hxy (by decide)
    · rw [hidx_1, hidx_u] at hxy; exact absurd hxy (by decide)
    · rw [hidx_1, hidx_v, ite_eq_left hx.1] at hxy; exact absurd hxy (by decide)
    · rfl
    · rw [hidx_1, hidx_2] at hxy; exact absurd hxy (by decide)
    · rw [hidx_2, hidx_u] at hxy; exact absurd hxy (by decide)
    · have hnh1 : ¬ G.PencilHub w₁ := fun h => hnotall ⟨hy.1, h, hx.1⟩
      rw [hidx_2, hidx_v, ite_eq_right hnh1] at hxy; exact absurd hxy (by decide)
    · rw [hidx_2, hidx_1] at hxy; exact absurd hxy (by decide)
    · rfl
  have hd_1 : ∀ x ∈ G.closedHubNbhd w₁, idx x ≠ (2 : Fin 4) := by
    intro x hx
    rcases hSw1 x hx with rfl | rfl | h3
    · rw [hidx_u]; decide
    · rw [hidx_1]; decide
    · rw [h3]; decide
  have hinj_1 : Set.InjOn idx (G.closedHubNbhd w₁) := by
    intro x hx y hy hxy
    rcases hSw1 x hx with rfl | rfl | hx3 <;> rcases hSw1 y hy with rfl | rfl | hy3
    · rfl
    · rw [hidx_u, hidx_1] at hxy; exact absurd hxy (by decide)
    · rw [hidx_u, hy3] at hxy; exact absurd hxy (by decide)
    · rw [hidx_1, hidx_u] at hxy; exact absurd hxy (by decide)
    · rfl
    · rw [hidx_1, hy3] at hxy; exact absurd hxy (by decide)
    · rw [hx3, hidx_u] at hxy; exact absurd hxy (by decide)
    · rw [hx3, hidx_1] at hxy; exact absurd hxy (by decide)
    · have hxu : x ≠ u_c := by rintro rfl; rw [hidx_u] at hx3; exact absurd hx3 (by decide)
      have hxw : x ≠ w₁ := by rintro rfl; rw [hidx_1] at hx3; exact absurd hx3 (by decide)
      have hyu : y ≠ u_c := by rintro rfl; rw [hidx_u] at hy3; exact absurd hy3 (by decide)
      have hyw : y ≠ w₁ := by rintro rfl; rw [hidx_1] at hy3; exact absurd hy3 (by decide)
      exact huniq_1 x hx y hy hxu hxw hyu hyw
  have hd_2 : ∀ x ∈ G.closedHubNbhd w₂, idx x ≠ (1 : Fin 4) := by
    intro x hx
    rcases hSw2 x hx with rfl | rfl | h3
    · rw [hidx_u]; decide
    · rw [hidx_2]; decide
    · rw [h3]; decide
  have hinj_2 : Set.InjOn idx (G.closedHubNbhd w₂) := by
    intro x hx y hy hxy
    rcases hSw2 x hx with rfl | rfl | hx3 <;> rcases hSw2 y hy with rfl | rfl | hy3
    · rfl
    · rw [hidx_u, hidx_2] at hxy; exact absurd hxy (by decide)
    · rw [hidx_u, hy3] at hxy; exact absurd hxy (by decide)
    · rw [hidx_2, hidx_u] at hxy; exact absurd hxy (by decide)
    · rfl
    · rw [hidx_2, hy3] at hxy; exact absurd hxy (by decide)
    · rw [hx3, hidx_u] at hxy; exact absurd hxy (by decide)
    · rw [hx3, hidx_2] at hxy; exact absurd hxy (by decide)
    · have hxu : x ≠ u_c := by rintro rfl; rw [hidx_u] at hx3; exact absurd hx3 (by decide)
      have hxw : x ≠ w₂ := by rintro rfl; rw [hidx_2] at hx3; exact absurd hx3 (by decide)
      have hyu : y ≠ u_c := by rintro rfl; rw [hidx_u] at hy3; exact absurd hy3 (by decide)
      have hyw : y ≠ w₂ := by rintro rfl; rw [hidx_2] at hy3; exact absurd hy3 (by decide)
      exact huniq_2 x hx y hy hxu hxw hyu hyw
  -- The three per-body slot extensions.
  obtain ⟨σu, hσu_inj, hσu_d, hσu_match⟩ :=
    exists_injective_extension_of_isFin3SelectorOf (hHubSel u_c) hd_u hinj_u
  obtain ⟨σ1, hσ1_inj, hσ1_d, hσ1_match⟩ :=
    exists_injective_extension_of_isFin3SelectorOf (hHubSel w₁) hd_1 hinj_1
  obtain ⟨σ2, hσ2_inj, hσ2_d, hσ2_match⟩ :=
    exists_injective_extension_of_isFin3SelectorOf (hHubSel w₂) hd_2 hinj_2
  -- The seed: hub normals from `idx`, fills from the per-body extensions.
  set fill : α → Fin 3 → Fin 4 → K := fun v =>
    if v = u_c then fun j => Pi.single (σu j) (1 : K)
    else if v = w₁ then fun j => Pi.single (σ1 j) (1 : K)
    else if v = w₂ then fun j => Pi.single (σ2 j) (1 : K)
    else fun _ _ => 0 with hfill_def
  have hfill_u : fill u_c = fun j => Pi.single (σu j) (1 : K) := by simp [hfill_def]
  have hfill_1 : fill w₁ = fun j => Pi.single (σ1 j) (1 : K) := by simp [hfill_def, hw1u]
  have hfill_2 : fill w₂ = fun j => Pi.single (σ2 j) (1 : K) := by
    simp [hfill_def, hw2u, Ne.symm hw12]
  set q : α × Fin 4 × Fin 4 → K :=
    fun p => Fin.cases (motive := fun _ => K)
      ((Pi.single (idx p.1) (1 : K) : Fin 4 → K) p.2.2)
      (fun j => fill p.1 j p.2.2) p.2.1
    with hq_def
  refine ⟨q, ?_⟩
  have hHubN : ∀ v : α, (PencilSeed.ofCoord q).hubNormal v = Pi.single (idx v) (1 : K) := by
    intro v
    funext i
    simp [PencilSeed.ofCoord, hq_def]
  have hFillH : ∀ (v : α) (j : Fin 3), (PencilSeed.ofCoord q).fillHub v j = fill v j := by
    intro v j
    funext i
    simp [PencilSeed.ofCoord, hq_def]
  -- Each body's slot triple reads back the extension's basis vectors.
  have hslot : ∀ (v : α) (σv : Fin 3 → Fin 4), fill v = (fun j => Pi.single (σv j) (1 : K)) →
      (∀ i w, hubSel v i = some w → σv i = idx w) →
      ∀ i, hubSlotNormal (PencilSeed.ofCoord q) hubSel v i = Pi.single (σv i) (1 : K) := by
    intro v σv hfv hmatch i
    cases hcase : hubSel v i with
    | none => simp only [hubSlotNormal, hcase, hFillH, hfv]
    | some w =>
        simp only [hubSlotNormal, hcase]
        rw [hHubN, hmatch i w hcase]
  have hslot_u := hslot u_c σu hfill_u hσu_match
  have hslot_1 := hslot w₁ σ1 hfill_1 hσ1_match
  have hslot_2 := hslot w₂ σ2 hfill_2 hσ2_match
  -- The three constructed points are nonzero multiples of three distinct basis vectors.
  have hPu : ∃ cc : K, cc ≠ 0 ∧ pencilChartPoint (PencilSeed.ofCoord q) hubSel u_c
      = cc • (Pi.single (3 : Fin 4) 1 : Fin 4 → K) := by
    have h01 : σu 0 ≠ σu 1 := fun h => absurd (hσu_inj h) (by decide)
    have h02 : σu 0 ≠ σu 2 := fun h => absurd (hσu_inj h) (by decide)
    have h12 : σu 1 ≠ σu 2 := fun h => absurd (hσu_inj h) (by decide)
    obtain ⟨cc, hcc, hcross⟩ :=
      exists_smul_cross₃_pi_single (K := K) (hσu_d 0) (hσu_d 1) (hσu_d 2) h01 h02 h12
    refine ⟨cc, hcc, ?_⟩
    rw [pencilChartPoint, hslot_u 0, hslot_u 1, hslot_u 2, hcross]
  have hP1 : ∃ cc : K, cc ≠ 0 ∧ pencilChartPoint (PencilSeed.ofCoord q) hubSel w₁
      = cc • (Pi.single (2 : Fin 4) 1 : Fin 4 → K) := by
    have h01 : σ1 0 ≠ σ1 1 := fun h => absurd (hσ1_inj h) (by decide)
    have h02 : σ1 0 ≠ σ1 2 := fun h => absurd (hσ1_inj h) (by decide)
    have h12 : σ1 1 ≠ σ1 2 := fun h => absurd (hσ1_inj h) (by decide)
    obtain ⟨cc, hcc, hcross⟩ :=
      exists_smul_cross₃_pi_single (K := K) (hσ1_d 0) (hσ1_d 1) (hσ1_d 2) h01 h02 h12
    refine ⟨cc, hcc, ?_⟩
    rw [pencilChartPoint, hslot_1 0, hslot_1 1, hslot_1 2, hcross]
  have hP2 : ∃ cc : K, cc ≠ 0 ∧ pencilChartPoint (PencilSeed.ofCoord q) hubSel w₂
      = cc • (Pi.single (1 : Fin 4) 1 : Fin 4 → K) := by
    have h01 : σ2 0 ≠ σ2 1 := fun h => absurd (hσ2_inj h) (by decide)
    have h02 : σ2 0 ≠ σ2 2 := fun h => absurd (hσ2_inj h) (by decide)
    have h12 : σ2 1 ≠ σ2 2 := fun h => absurd (hσ2_inj h) (by decide)
    obtain ⟨cc, hcc, hcross⟩ :=
      exists_smul_cross₃_pi_single (K := K) (hσ2_d 0) (hσ2_d 1) (hσ2_d 2) h01 h02 h12
    refine ⟨cc, hcc, ?_⟩
    rw [pencilChartPoint, hslot_2 0, hslot_2 1, hslot_2 2, hcross]
  obtain ⟨cu, hcu0, hcu⟩ := hPu
  obtain ⟨c1, hc10, hc1⟩ := hP1
  obtain ⟨c2, hc20, hc2⟩ := hP2
  -- Assemble: three distinct basis directions, rescaled by nonzero scalars, are independent.
  have hbase := (linearIndependent_pi_single_triple (K := K) (a := 3) (b := 2) (c := 1)
    (by decide) (by decide) (by decide)).units_smul
    ![Units.mk0 cu hcu0, Units.mk0 c1 hc10, Units.mk0 c2 hc20]
  have heq : ((![Units.mk0 cu hcu0, Units.mk0 c1 hc10, Units.mk0 c2 hc20] : Fin 3 → Kˣ) •
      ![(Pi.single (3 : Fin 4) (1 : K) : Fin 4 → K), Pi.single 2 1, Pi.single 1 1])
      = ![pencilChartPoint (PencilSeed.ofCoord q) hubSel u_c,
          pencilChartPoint (PencilSeed.ofCoord q) hubSel w₁,
          pencilChartPoint (PencilSeed.ofCoord q) hubSel w₂] := by
    funext i
    fin_cases i <;> simp [Units.smul_def, hcu, hc1, hc2]
  rwa [heq] at hbase

/-! ## Witness (ii): the somewhere-witness on `H`'s chart (Phase 39 W5-L5, L5-cut-v-c)

The output somewhere-witness. Two small linear-independence engines feed it: a nonzero-scaled
family of standard basis vectors indexed by an injective direction map is `LinearIndepOn`
(`linearIndepOn_smul_pi_single`, over a set) / `LinearIndependent` (over a `Fin m` family,
`linearIndependent_smul_pi_single_of_injective`). -/

/-- **A nonzero-scaled family of distinct standard basis vectors is linearly independent (over a
set)** (Phase 39 W5-L5, L5-cut-v-c engine): if `J` is injective on `S` and `c` is nonzero there,
`fun x => c x • e_{J x}` is `LinearIndepOn K · S`. Via `Pi.basisFun`'s independence composed along
the injective `J` and rescaled by units (`LinearIndependent.units_smul`). -/
theorem linearIndepOn_smul_pi_single {ι : Type*} {n : ℕ}
    {S : Set ι} {J : ι → Fin n} {c : ι → K}
    (hJ : Set.InjOn J S) (hc : ∀ x ∈ S, c x ≠ 0) :
    LinearIndepOn K (fun x => c x • (Pi.single (J x) 1 : Fin n → K)) S := by
  have hbase : LinearIndependent K (fun x : S => (Pi.single (J x) 1 : Fin n → K)) := by
    have hcomp := (Pi.basisFun K (Fin n)).linearIndependent.comp
      (fun x : S => J x) (hJ.injective)
    have heq2 : (⇑(Pi.basisFun K (Fin n)) ∘ (fun x : S => J x))
        = fun x : S => (Pi.single (J x) 1 : Fin n → K) := by
      funext x; rw [Function.comp_apply, Pi.basisFun_apply]
    rwa [heq2] at hcomp
  have h := hbase.units_smul (fun x : S => Units.mk0 (c x) (hc x x.2))
  have heq : ((fun x : S => Units.mk0 (c x) (hc x x.2)) •
      fun x : S => (Pi.single (J x) 1 : Fin n → K))
      = fun x : S => c x • (Pi.single (J x) 1 : Fin n → K) := by
    funext x; simp [Units.smul_def]
  rw [heq] at h
  exact h

/-- **A nonzero-scaled family of distinct standard basis vectors is linearly independent (over a
`Fin m` family)** (Phase 39 W5-L5, L5-cut-v-c engine): the `Fin m`-indexed sibling of
`linearIndepOn_smul_pi_single`, consumed for the demoted body's forced-`cross₃` LI premise. -/
theorem linearIndependent_smul_pi_single_of_injective {m n : ℕ}
    {T : Fin m → Fin n} {cs : Fin m → K}
    (hT : Function.Injective T) (hcs : ∀ i, cs i ≠ 0) :
    LinearIndependent K (fun i => cs i • (Pi.single (T i) 1 : Fin n → K)) := by
  have hbase : LinearIndependent K (fun i : Fin m => (Pi.single (T i) 1 : Fin n → K)) := by
    have hcomp := (Pi.basisFun K (Fin n)).linearIndependent.comp T hT
    have heq2 : (⇑(Pi.basisFun K (Fin n)) ∘ T) = fun i => (Pi.single (T i) 1 : Fin n → K) := by
      funext i; rw [Function.comp_apply, Pi.basisFun_apply]
    rwa [heq2] at hcomp
  have h := hbase.units_smul (fun i => Units.mk0 (cs i) (hcs i))
  have heq : ((fun i => Units.mk0 (cs i) (hcs i)) •
      fun i : Fin m => (Pi.single (T i) 1 : Fin n → K))
      = fun i => cs i • (Pi.single (T i) 1 : Fin n → K) := by
    funext i; simp [Units.smul_def]
  rwa [heq] at h

/-- **The pendant-cut somewhere-witness on `H := G.induce V₁`'s chart** (Phase 39 W5-L5, L5-cut-v-c;
the pinned witness (ii) of `notes/Phase39-design.md` §"W5 leaf decomposition" L5-cut-v): under the
sub-case-4 **pendant** configuration (`V(G) = V₁ ∪ {v_c}`, so `v_c` is the far-side pendant,
`G.degree u_c = 3`, cut edge `e_c : u_c–v_c` the only crossing edge, the two `V₁`-links
`e₁ : u_c–w₁`, `e₂ : u_c–w₂`) with `G` simple and nondegeneracy-feasible, and for *any* WF-correct
`hubSel`/`nbrSel` pair for `H := G.induce V₁`, some seed coordinate `q` makes the chart's
constructed normals `LinearIndepOn` over each of `u_c`, `w₁`, `w₂`'s closed hub-neighbourhood
**in `G`** (the stronger set — `H.closedHubNbhd v ⊆ G.closedHubNbhd v`, so the eventual `H`-side
consumer gets its `H.closedHubNbhd v` conjunct by `LinearIndepOn.mono`). Feeds the output-half
steering leaves (v-d/v-f) through `pencilChartPointPoly`/normal-polynomial eval identities.

The pendant hypothesis `hVG` (matching sub-case 3's producer,
`hasGenericPencilRealization_of_isNondegPencilRealization_induce_pendant`, and in scope at the
sub-case-4 discharge) makes `v_c` a degree-`1` non-hub, so it never enters any family — the design
doc's composition finding "every promoted family is `fillNbr`-free" holds exactly there, since the
only non-hub family member is the demoted `u_c`, whose neighbour selector `nbrSel u_c` is fully
assigned (`H.closedNbhd u_c = {u_c, w₁, w₂}`). The family function `pencilChartNormal ... H` needs
no by-cases: at an `H`-hub it reads the free seed normal `e_{idx}`; at the demoted `u_c` its
non-hub branch is the forced `cross₃` of the three demoted-triple points, which the seed steers to
`±e_0` (the three points being steered to `±e_3`, `±e_2`, `±e_1`, exactly the v-b construction).
The direction map is v-b's `idx` (`u_c ↦ 0`, `w₁ ↦ 1`, `w₂ ↦ 2`, else `3`), so the per-family
injectivity is v-b's own combinatorics (the `≤ 3` cardinality bound and the v-a triangle
exclusion). -/
theorem exists_coord_linearIndependent_pencilChartNormal_of_pendant_deg3
    [Finite α] [Finite β] {G : Graph α β} {V₁ : Set α} {e_c e₁ e₂ : β} {u_c v_c w₁ w₂ : α}
    (hSimple : G.Simple) (hfeas : PencilNondegFeasible K G)
    (hl_c : G.IsLink e_c u_c v_c) (hu_c : u_c ∈ V₁) (hv_c : v_c ∉ V₁)
    (hVG : V(G) = V₁ ∪ {v_c}) (hcut : (G.cutEdges V₁).ncard ≤ 1) (hdeg : G.degree u_c = 3)
    (hl₁ : G.IsLink e₁ u_c w₁) (hl₂ : G.IsLink e₂ u_c w₂)
    (hw₁ : w₁ ∈ V₁) (hw₂ : w₂ ∈ V₁) (hw12 : w₁ ≠ w₂)
    (hubSel nbrSel : α → Fin 3 → Option α)
    (hHubSel : ∀ v, IsFin3SelectorOf ((G.induce V₁).closedHubNbhd v) (hubSel v))
    (hNbrSel : ∀ v, ¬ (G.induce V₁).PencilHub v →
      IsFin3SelectorOf ((G.induce V₁).closedNbhd v) (nbrSel v)) :
    ∃ q : α × Fin 4 × Fin 4 → K,
      ∀ v ∈ ({u_c, w₁, w₂} : Set α),
        LinearIndepOn K
          (pencilChartNormal (PencilSeed.ofCoord q) hubSel nbrSel (G.induce V₁))
          (G.closedHubNbhd v) := by
  classical
  haveI := hSimple
  haveI : G.LocallyFinite := inferInstance
  -- Distinctness and `u_c`'s ambient hub status.
  have hw1u : w₁ ≠ u_c := hl₁.ne.symm
  have hw2u : w₂ ≠ u_c := hl₂.ne.symm
  have hvcu : v_c ≠ u_c := hl_c.ne.symm
  have hv1 : v_c ≠ w₁ := by rintro rfl; exact hv_c hw₁
  have hv2 : v_c ≠ w₂ := by rintro rfl; exact hv_c hw₂
  have hub_u : G.PencilHub u_c := ⟨hl_c.left_mem, by omega⟩
  -- The bare induced side `H := G.induce V₁`.
  have hV₁G : V₁ ⊆ V(G) := by rw [hVG]; exact Set.subset_union_left
  have hle : G.induce V₁ ≤ G := Graph.induce_le hV₁G
  have hVH_mem : ∀ x ∈ V₁, x ∈ V(G.induce V₁) := by
    intro x hx; rw [Graph.vertexSet_induce]; exact hx
  have hdegH_uc : (G.induce V₁).degree u_c = 2 := by
    have h := Graph.degree_eq_degree_induce_succ hl_c hu_c hv_c hcut; omega
  have hnothub_uc : ¬ (G.induce V₁).PencilHub u_c := fun h => by
    have := h.2; rw [hdegH_uc] at this; omega
  -- `v_c` is a degree-`1` pendant, hence never a hub.
  have hvc_deg : G.degree v_c = 1 := by
    have hGeq : G.induce (V₁ ∪ {v_c}) = G := by rw [← hVG]; exact Graph.induce_vertexSet G
    have h := Graph.degree_induce_union_singleton_far hl_c hu_c hv_c hcut
    rwa [hGeq] at h
  have hvc_nothub : ¬ G.PencilHub v_c := fun h => by have := h.2; rw [hvc_deg] at this; omega
  -- Feasibility cardinality bound and `u_c`'s neighbours.
  obtain ⟨F₀, nrm₀, pt₀, hnd₀⟩ := id hfeas
  have hcard : ∀ v ∈ V(G), (G.closedHubNbhd v).ncard ≤ 3 := fun v hv =>
    ncard_closedHubNbhd_le_three_of_isNondegPencilRealization hnd₀ hv
  have hN : N(G, u_c) = ({v_c, w₁, w₂} : Set α) :=
    Graph.neighbor_eq_of_degree_eq_three hSimple hl_c hl₁ hl₂ hv1 hv2 hw12 hdeg
  -- Family classification at `u_c` (`v_c` excluded, being a non-hub).
  have hSu : ∀ x ∈ G.closedHubNbhd u_c, x = u_c ∨ x = w₁ ∨ x = w₂ := by
    rintro x ⟨hxhub, h | ⟨e, he⟩⟩
    · exact Or.inl h
    · have hxN : x ∈ N(G, u_c) := he.adj
      rw [hN] at hxN
      rcases hxN with rfl | rfl | rfl
      · exact absurd hxhub hvc_nothub
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
  -- The v-a triangle exclusions: `w₁ ~ w₂` is barred whenever either is a hub.
  have hw2_nadj1 : G.PencilHub w₂ → ¬ G.Adj w₁ w₂ := by
    rintro hh2 ⟨e₃, he₃⟩
    exact not_pencilNondegFeasible_of_triangle_two_hubs hw1u (Ne.symm hw2u) hw12
      hl₁.symm hl₂ he₃.symm hub_u hh2 hfeas
  have hw1_nadj2 : G.PencilHub w₁ → ¬ G.Adj w₂ w₁ := by
    rintro hh1 ⟨e₃, he₃⟩
    exact not_pencilNondegFeasible_of_triangle_two_hubs hw2u (Ne.symm hw1u) (Ne.symm hw12)
      hl₂.symm hl₁ he₃.symm hub_u hh1 hfeas
  have hnw2_1 : w₂ ∉ G.closedHubNbhd w₁ := by
    rintro ⟨hh2, h | ⟨e, he⟩⟩
    · exact hw12 h.symm
    · exact hw2_nadj1 hh2 ⟨e, he⟩
  have hnw1_2 : w₁ ∉ G.closedHubNbhd w₂ := by
    rintro ⟨hh1, h | ⟨e, he⟩⟩
    · exact hw12 h
    · exact hw1_nadj2 hh1 ⟨e, he⟩
  -- At most one third-party member at `w₁`/`w₂` (v-b's degree/cardinality bookkeeping).
  have huniq_1 : ∀ x ∈ G.closedHubNbhd w₁, ∀ y ∈ G.closedHubNbhd w₁,
      x ≠ u_c → x ≠ w₁ → y ≠ u_c → y ≠ w₁ → x = y := by
    intro x hx y hy hxu hxw hyu hyw
    by_contra hxy
    obtain ⟨hxhub, hx' | ⟨ex, hex⟩⟩ := hx
    · exact hxw hx'
    obtain ⟨hyhub, hy' | ⟨ey, hey⟩⟩ := hy
    · exact hyw hy'
    by_cases h1 : G.PencilHub w₁
    · have hsub4 : ({w₁, u_c, x, y} : Set α) ⊆ G.closedHubNbhd w₁ := by
        rintro z (rfl | rfl | rfl | rfl)
        · exact ⟨h1, Or.inl rfl⟩
        · exact ⟨hub_u, Or.inr ⟨e₁, hl₁.symm⟩⟩
        · exact ⟨hxhub, Or.inr ⟨ex, hex⟩⟩
        · exact ⟨hyhub, Or.inr ⟨ey, hey⟩⟩
      have h4card : ({w₁, u_c, x, y} : Set α).ncard = 4 := by
        rw [Set.ncard_insert_of_notMem (by simp [hw1u, Ne.symm hxw, Ne.symm hyw]),
          Set.ncard_insert_of_notMem (by simp [Ne.symm hxu, Ne.symm hyu]),
          Set.ncard_insert_of_notMem (by simp [hxy]), Set.ncard_singleton]
      have hle4 := Set.ncard_le_ncard hsub4 (Set.toFinite _)
      have hb := hcard w₁ hl₁.right_mem
      rw [h4card] at hle4
      omega
    · have hdeg1 : G.degree w₁ ≤ 2 := by
        by_contra hcon
        exact h1 ⟨hl₁.right_mem, by omega⟩
      have hsub3 : ({u_c, x, y} : Set α) ⊆ N(G, w₁) := by
        rintro z (rfl | rfl | rfl)
        · exact hl₁.symm.adj
        · exact ⟨ex, hex⟩
        · exact ⟨ey, hey⟩
      have h3card : ({u_c, x, y} : Set α).ncard = 3 :=
        Set.ncard_eq_three.mpr ⟨u_c, x, y, Ne.symm hxu, Ne.symm hyu, hxy, rfl⟩
      have hle3 := Set.ncard_le_ncard hsub3 (Set.toFinite _)
      rw [h3card, ← Graph.degree_eq_ncard_adj] at hle3
      omega
  have huniq_2 : ∀ x ∈ G.closedHubNbhd w₂, ∀ y ∈ G.closedHubNbhd w₂,
      x ≠ u_c → x ≠ w₂ → y ≠ u_c → y ≠ w₂ → x = y := by
    intro x hx y hy hxu hxw hyu hyw
    by_contra hxy
    obtain ⟨hxhub, hx' | ⟨ex, hex⟩⟩ := hx
    · exact hxw hx'
    obtain ⟨hyhub, hy' | ⟨ey, hey⟩⟩ := hy
    · exact hyw hy'
    by_cases h2 : G.PencilHub w₂
    · have hsub4 : ({w₂, u_c, x, y} : Set α) ⊆ G.closedHubNbhd w₂ := by
        rintro z (rfl | rfl | rfl | rfl)
        · exact ⟨h2, Or.inl rfl⟩
        · exact ⟨hub_u, Or.inr ⟨e₂, hl₂.symm⟩⟩
        · exact ⟨hxhub, Or.inr ⟨ex, hex⟩⟩
        · exact ⟨hyhub, Or.inr ⟨ey, hey⟩⟩
      have h4card : ({w₂, u_c, x, y} : Set α).ncard = 4 := by
        rw [Set.ncard_insert_of_notMem (by simp [hw2u, Ne.symm hxw, Ne.symm hyw]),
          Set.ncard_insert_of_notMem (by simp [Ne.symm hxu, Ne.symm hyu]),
          Set.ncard_insert_of_notMem (by simp [hxy]), Set.ncard_singleton]
      have hle4 := Set.ncard_le_ncard hsub4 (Set.toFinite _)
      have hb := hcard w₂ hl₂.right_mem
      rw [h4card] at hle4
      omega
    · have hdeg2 : G.degree w₂ ≤ 2 := by
        by_contra hcon
        exact h2 ⟨hl₂.right_mem, by omega⟩
      have hsub3 : ({u_c, x, y} : Set α) ⊆ N(G, w₂) := by
        rintro z (rfl | rfl | rfl)
        · exact hl₂.symm.adj
        · exact ⟨ex, hex⟩
        · exact ⟨ey, hey⟩
      have h3card : ({u_c, x, y} : Set α).ncard = 3 :=
        Set.ncard_eq_three.mpr ⟨u_c, x, y, Ne.symm hxu, Ne.symm hyu, hxy, rfl⟩
      have hle3 := Set.ncard_le_ncard hsub3 (Set.toFinite _)
      rw [h3card, ← Graph.degree_eq_ncard_adj] at hle3
      omega
  -- The direction map (v-b's `idx`, simplified: `v_c` is not a hub, so it needs no own index).
  set idx : α → Fin 4 := fun x =>
    if x = u_c then 0 else if x = w₁ then 1 else if x = w₂ then 2 else 3 with hidx_def
  have hidx_u : idx u_c = 0 := by simp [hidx_def]
  have hidx_1 : idx w₁ = 1 := by simp [hidx_def, hw1u]
  have hidx_2 : idx w₂ = 2 := by simp [hidx_def, hw2u, Ne.symm hw12]
  have hidx_o : ∀ x, x ≠ u_c → x ≠ w₁ → x ≠ w₂ → idx x = 3 := by
    intro x h1 h2 h3; simp [hidx_def, h1, h2, h3]
  -- Classification at `w₁`/`w₂`.
  have hSw1 : ∀ x ∈ G.closedHubNbhd w₁, x = u_c ∨ x = w₁ ∨ idx x = 3 := by
    intro x hx
    by_cases h1 : x = u_c
    · exact Or.inl h1
    by_cases h2 : x = w₁
    · exact Or.inr (Or.inl h2)
    refine Or.inr (Or.inr (hidx_o x h1 h2 ?_))
    rintro rfl; exact hnw2_1 hx
  have hSw2 : ∀ x ∈ G.closedHubNbhd w₂, x = u_c ∨ x = w₂ ∨ idx x = 3 := by
    intro x hx
    by_cases h1 : x = u_c
    · exact Or.inl h1
    by_cases h2 : x = w₂
    · exact Or.inr (Or.inl h2)
    refine Or.inr (Or.inr (hidx_o x h1 ?_ h2))
    rintro rfl; exact hnw1_2 hx
  -- Target-avoidance and injectivity of `idx` on each family (over `G`).
  have hdG_u : ∀ x ∈ G.closedHubNbhd u_c, idx x ≠ (3 : Fin 4) := by
    intro x hx
    rcases hSu x hx with rfl | rfl | rfl
    · rw [hidx_u]; decide
    · rw [hidx_1]; decide
    · rw [hidx_2]; decide
  have hinjG_u : Set.InjOn idx (G.closedHubNbhd u_c) := by
    intro x hx y hy hxy
    rcases hSu x hx with rfl | rfl | rfl <;> rcases hSu y hy with rfl | rfl | rfl
    · rfl
    · rw [hidx_u, hidx_1] at hxy; exact absurd hxy (by decide)
    · rw [hidx_u, hidx_2] at hxy; exact absurd hxy (by decide)
    · rw [hidx_1, hidx_u] at hxy; exact absurd hxy (by decide)
    · rfl
    · rw [hidx_1, hidx_2] at hxy; exact absurd hxy (by decide)
    · rw [hidx_2, hidx_u] at hxy; exact absurd hxy (by decide)
    · rw [hidx_2, hidx_1] at hxy; exact absurd hxy (by decide)
    · rfl
  have hdG_1 : ∀ x ∈ G.closedHubNbhd w₁, idx x ≠ (2 : Fin 4) := by
    intro x hx
    rcases hSw1 x hx with rfl | rfl | h3
    · rw [hidx_u]; decide
    · rw [hidx_1]; decide
    · rw [h3]; decide
  have hinjG_1 : Set.InjOn idx (G.closedHubNbhd w₁) := by
    intro x hx y hy hxy
    rcases hSw1 x hx with rfl | rfl | hx3 <;> rcases hSw1 y hy with rfl | rfl | hy3
    · rfl
    · rw [hidx_u, hidx_1] at hxy; exact absurd hxy (by decide)
    · rw [hidx_u, hy3] at hxy; exact absurd hxy (by decide)
    · rw [hidx_1, hidx_u] at hxy; exact absurd hxy (by decide)
    · rfl
    · rw [hidx_1, hy3] at hxy; exact absurd hxy (by decide)
    · rw [hx3, hidx_u] at hxy; exact absurd hxy (by decide)
    · rw [hx3, hidx_1] at hxy; exact absurd hxy (by decide)
    · have hxu : x ≠ u_c := by rintro rfl; rw [hidx_u] at hx3; exact absurd hx3 (by decide)
      have hxw : x ≠ w₁ := by rintro rfl; rw [hidx_1] at hx3; exact absurd hx3 (by decide)
      have hyu : y ≠ u_c := by rintro rfl; rw [hidx_u] at hy3; exact absurd hy3 (by decide)
      have hyw : y ≠ w₁ := by rintro rfl; rw [hidx_1] at hy3; exact absurd hy3 (by decide)
      exact huniq_1 x hx y hy hxu hxw hyu hyw
  have hdG_2 : ∀ x ∈ G.closedHubNbhd w₂, idx x ≠ (1 : Fin 4) := by
    intro x hx
    rcases hSw2 x hx with rfl | rfl | h3
    · rw [hidx_u]; decide
    · rw [hidx_2]; decide
    · rw [h3]; decide
  have hinjG_2 : Set.InjOn idx (G.closedHubNbhd w₂) := by
    intro x hx y hy hxy
    rcases hSw2 x hx with rfl | rfl | hx3 <;> rcases hSw2 y hy with rfl | rfl | hy3
    · rfl
    · rw [hidx_u, hidx_2] at hxy; exact absurd hxy (by decide)
    · rw [hidx_u, hy3] at hxy; exact absurd hxy (by decide)
    · rw [hidx_2, hidx_u] at hxy; exact absurd hxy (by decide)
    · rfl
    · rw [hidx_2, hy3] at hxy; exact absurd hxy (by decide)
    · rw [hx3, hidx_u] at hxy; exact absurd hxy (by decide)
    · rw [hx3, hidx_2] at hxy; exact absurd hxy (by decide)
    · have hxu : x ≠ u_c := by rintro rfl; rw [hidx_u] at hx3; exact absurd hx3 (by decide)
      have hxw : x ≠ w₂ := by rintro rfl; rw [hidx_2] at hx3; exact absurd hx3 (by decide)
      have hyu : y ≠ u_c := by rintro rfl; rw [hidx_u] at hy3; exact absurd hy3 (by decide)
      have hyw : y ≠ w₂ := by rintro rfl; rw [hidx_2] at hy3; exact absurd hy3 (by decide)
      exact huniq_2 x hx y hy hxu hxw hyu hyw
  -- The point-construction slot extensions over `H`'s closed hub-neighbourhoods (v-b's toolkit).
  have hdH_u : ∀ x ∈ (G.induce V₁).closedHubNbhd u_c, idx x ≠ (3 : Fin 4) :=
    fun x hx => hdG_u x (Graph.closedHubNbhd_mono hle u_c hx)
  have hinjH_u : Set.InjOn idx ((G.induce V₁).closedHubNbhd u_c) :=
    hinjG_u.mono (Graph.closedHubNbhd_mono hle u_c)
  have hdH_1 : ∀ x ∈ (G.induce V₁).closedHubNbhd w₁, idx x ≠ (2 : Fin 4) :=
    fun x hx => hdG_1 x (Graph.closedHubNbhd_mono hle w₁ hx)
  have hinjH_1 : Set.InjOn idx ((G.induce V₁).closedHubNbhd w₁) :=
    hinjG_1.mono (Graph.closedHubNbhd_mono hle w₁)
  have hdH_2 : ∀ x ∈ (G.induce V₁).closedHubNbhd w₂, idx x ≠ (1 : Fin 4) :=
    fun x hx => hdG_2 x (Graph.closedHubNbhd_mono hle w₂ hx)
  have hinjH_2 : Set.InjOn idx ((G.induce V₁).closedHubNbhd w₂) :=
    hinjG_2.mono (Graph.closedHubNbhd_mono hle w₂)
  obtain ⟨σu, hσu_inj, hσu_d, hσu_match⟩ :=
    exists_injective_extension_of_isFin3SelectorOf (hHubSel u_c) hdH_u hinjH_u
  obtain ⟨σ1, hσ1_inj, hσ1_d, hσ1_match⟩ :=
    exists_injective_extension_of_isFin3SelectorOf (hHubSel w₁) hdH_1 hinjH_1
  obtain ⟨σ2, hσ2_inj, hσ2_d, hσ2_match⟩ :=
    exists_injective_extension_of_isFin3SelectorOf (hHubSel w₂) hdH_2 hinjH_2
  -- The seed (v-b's seed verbatim; the simpler `idx`).
  set fill : α → Fin 3 → Fin 4 → K := fun v =>
    if v = u_c then fun j => Pi.single (σu j) (1 : K)
    else if v = w₁ then fun j => Pi.single (σ1 j) (1 : K)
    else if v = w₂ then fun j => Pi.single (σ2 j) (1 : K)
    else fun _ _ => 0 with hfill_def
  have hfill_u : fill u_c = fun j => Pi.single (σu j) (1 : K) := by simp [hfill_def]
  have hfill_1 : fill w₁ = fun j => Pi.single (σ1 j) (1 : K) := by simp [hfill_def, hw1u]
  have hfill_2 : fill w₂ = fun j => Pi.single (σ2 j) (1 : K) := by
    simp [hfill_def, hw2u, Ne.symm hw12]
  set q : α × Fin 4 × Fin 4 → K :=
    fun p => Fin.cases (motive := fun _ => K)
      ((Pi.single (idx p.1) (1 : K) : Fin 4 → K) p.2.2)
      (fun j => fill p.1 j p.2.2) p.2.1
    with hq_def
  have hHubN : ∀ v : α, (PencilSeed.ofCoord q).hubNormal v = Pi.single (idx v) (1 : K) := by
    intro v; funext i; simp [PencilSeed.ofCoord, hq_def]
  have hFillH : ∀ (v : α) (j : Fin 3), (PencilSeed.ofCoord q).fillHub v j = fill v j := by
    intro v j; funext i; simp [PencilSeed.ofCoord, hq_def]
  have hslot : ∀ (v : α) (σv : Fin 3 → Fin 4), fill v = (fun j => Pi.single (σv j) (1 : K)) →
      (∀ i w, hubSel v i = some w → σv i = idx w) →
      ∀ i, hubSlotNormal (PencilSeed.ofCoord q) hubSel v i = Pi.single (σv i) (1 : K) := by
    intro v σv hfv hmatch i
    cases hcase : hubSel v i with
    | none => simp only [hubSlotNormal, hcase, hFillH, hfv]
    | some w =>
        simp only [hubSlotNormal, hcase]
        rw [hHubN, hmatch i w hcase]
  have hslot_u := hslot u_c σu hfill_u hσu_match
  have hslot_1 := hslot w₁ σ1 hfill_1 hσ1_match
  have hslot_2 := hslot w₂ σ2 hfill_2 hσ2_match
  -- The three chart points are nonzero multiples of `e₃`, `e₂`, `e₁`.
  obtain ⟨cu, hcu0, hpt_u⟩ : ∃ cc : K, cc ≠ 0 ∧
      pencilChartPoint (PencilSeed.ofCoord q) hubSel u_c
        = cc • (Pi.single (3 : Fin 4) 1 : Fin 4 → K) := by
    have h01 : σu 0 ≠ σu 1 := fun h => absurd (hσu_inj h) (by decide)
    have h02 : σu 0 ≠ σu 2 := fun h => absurd (hσu_inj h) (by decide)
    have h12 : σu 1 ≠ σu 2 := fun h => absurd (hσu_inj h) (by decide)
    obtain ⟨cc, hcc, hcross⟩ :=
      exists_smul_cross₃_pi_single (K := K) (hσu_d 0) (hσu_d 1) (hσu_d 2) h01 h02 h12
    exact ⟨cc, hcc, by rw [pencilChartPoint, hslot_u 0, hslot_u 1, hslot_u 2, hcross]⟩
  obtain ⟨c1, hc10, hpt_1⟩ : ∃ cc : K, cc ≠ 0 ∧
      pencilChartPoint (PencilSeed.ofCoord q) hubSel w₁
        = cc • (Pi.single (2 : Fin 4) 1 : Fin 4 → K) := by
    have h01 : σ1 0 ≠ σ1 1 := fun h => absurd (hσ1_inj h) (by decide)
    have h02 : σ1 0 ≠ σ1 2 := fun h => absurd (hσ1_inj h) (by decide)
    have h12 : σ1 1 ≠ σ1 2 := fun h => absurd (hσ1_inj h) (by decide)
    obtain ⟨cc, hcc, hcross⟩ :=
      exists_smul_cross₃_pi_single (K := K) (hσ1_d 0) (hσ1_d 1) (hσ1_d 2) h01 h02 h12
    exact ⟨cc, hcc, by rw [pencilChartPoint, hslot_1 0, hslot_1 1, hslot_1 2, hcross]⟩
  obtain ⟨c2, hc20, hpt_2⟩ : ∃ cc : K, cc ≠ 0 ∧
      pencilChartPoint (PencilSeed.ofCoord q) hubSel w₂
        = cc • (Pi.single (1 : Fin 4) 1 : Fin 4 → K) := by
    have h01 : σ2 0 ≠ σ2 1 := fun h => absurd (hσ2_inj h) (by decide)
    have h02 : σ2 0 ≠ σ2 2 := fun h => absurd (hσ2_inj h) (by decide)
    have h12 : σ2 1 ≠ σ2 2 := fun h => absurd (hσ2_inj h) (by decide)
    obtain ⟨cc, hcc, hcross⟩ :=
      exists_smul_cross₃_pi_single (K := K) (hσ2_d 0) (hσ2_d 1) (hσ2_d 2) h01 h02 h12
    exact ⟨cc, hcc, by rw [pencilChartPoint, hslot_2 0, hslot_2 1, hslot_2 2, hcross]⟩
  -- `H.closedNbhd u_c = {u_c, w₁, w₂}`, so `nbrSel u_c` is fully assigned.
  have hNH_uc : (G.induce V₁).closedNbhd u_c = ({u_c, w₁, w₂} : Set α) := by
    ext x
    simp only [Graph.closedNbhd, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (rfl | ⟨e, he⟩)
      · exact Or.inl rfl
      · obtain ⟨heG, -, hxV₁⟩ := (Graph.induce_isLink G V₁ e u_c x).mp he
        have hxN : x ∈ N(G, u_c) := heG.adj
        rw [hN] at hxN
        rcases hxN with rfl | rfl | rfl
        · exact absurd hxV₁ hv_c
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
    · rintro (hx | hx | hx)
      · exact Or.inl hx
      · refine Or.inr ⟨e₁, ?_⟩
        rw [hx]; exact (Graph.induce_isLink G V₁ e₁ u_c w₁).mpr ⟨hl₁, hu_c, hw₁⟩
      · refine Or.inr ⟨e₂, ?_⟩
        rw [hx]; exact (Graph.induce_isLink G V₁ e₂ u_c w₂).mpr ⟨hl₂, hu_c, hw₂⟩
  have hselNbr : IsFin3SelectorOf ({u_c, w₁, w₂} : Set α) (nbrSel u_c) := by
    have := hNbrSel u_c hnothub_uc; rwa [hNH_uc] at this
  -- Every slot of `nbrSel u_c` is `some` (three members fill three slots).
  obtain ⟨iu, hiu⟩ := hselNbr.2.1 u_c (by simp)
  obtain ⟨i1, hi1⟩ := hselNbr.2.1 w₁ (by simp)
  obtain ⟨i2, hi2⟩ := hselNbr.2.1 w₂ (by simp)
  have hiu1 : iu ≠ i1 := by
    rintro rfl; rw [hiu] at hi1; exact hw1u (Option.some.inj hi1).symm
  have hiu2 : iu ≠ i2 := by
    rintro rfl; rw [hiu] at hi2; exact hw2u (Option.some.inj hi2).symm
  have hi12 : i1 ≠ i2 := by
    rintro rfl; rw [hi1] at hi2; exact hw12 (Option.some.inj hi2)
  have huniv : ({iu, i1, i2} : Finset (Fin 3)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_insert_of_notMem (by simp [hiu1, hiu2]),
      Finset.card_insert_of_notMem (by simp [hi12]), Finset.card_singleton, Fintype.card_fin]
  have hall : ∀ i : Fin 3, i = iu ∨ i = i1 ∨ i = i2 := by
    intro i
    have : i ∈ ({iu, i1, i2} : Finset (Fin 3)) := huniv ▸ Finset.mem_univ i
    simpa using this
  have hns_some : ∀ i, ∃ z, nbrSel u_c i = some z := by
    intro i; rcases hall i with rfl | rfl | rfl
    exacts [⟨u_c, hiu⟩, ⟨w₁, hi1⟩, ⟨w₂, hi2⟩]
  choose mem hmem using hns_some
  have hmem_inj : Function.Injective mem := fun i j hij =>
    hselNbr.2.2 i j (mem i) (hmem i) (hij ▸ hmem j)
  have hmem_mem : ∀ i, mem i = u_c ∨ mem i = w₁ ∨ mem i = w₂ := by
    intro i; have := hselNbr.1 i (mem i) (hmem i); simpa using this
  -- The nbr-slot points, read as scaled basis vectors, and the forced normal at `u_c`.
  set tgt : α → Fin 4 := fun z => if z = u_c then 3 else if z = w₁ then 2 else 1 with htgt_def
  set T : Fin 3 → Fin 4 := fun i => tgt (mem i) with hT_def
  set cs : Fin 3 → K := fun i => if mem i = u_c then cu else if mem i = w₁ then c1 else c2
    with hcs_def
  have hcs_ne : ∀ i, cs i ≠ 0 := by
    intro i; simp only [hcs_def]
    rcases hmem_mem i with h | h | h
    · rw [ite_eq_left h]; exact hcu0
    · rw [ite_eq_right (by rw [h]; exact hw1u), ite_eq_left h]; exact hc10
    · rw [ite_eq_right (by rw [h]; exact hw2u),
        ite_eq_right (by rw [h]; exact Ne.symm hw12)]
      exact hc20
  have hT_ne : ∀ i, T i ≠ (0 : Fin 4) := by
    intro i; simp only [hT_def, htgt_def]
    rcases hmem_mem i with h | h | h
    · rw [ite_eq_left h]; decide
    · rw [ite_eq_right (by rw [h]; exact hw1u), ite_eq_left h]; decide
    · rw [ite_eq_right (by rw [h]; exact hw2u),
        ite_eq_right (by rw [h]; exact Ne.symm hw12)]
      decide
  have hT_val : ∀ i, (mem i = u_c ∧ T i = 3) ∨ (mem i = w₁ ∧ T i = 2) ∨
      (mem i = w₂ ∧ T i = 1) := by
    intro i
    rcases hmem_mem i with h | h | h
    · exact Or.inl ⟨h, by simp [hT_def, htgt_def, h]⟩
    · exact Or.inr (Or.inl ⟨h, by simp [hT_def, htgt_def, h, hw1u]⟩)
    · exact Or.inr (Or.inr ⟨h, by simp [hT_def, htgt_def, h, hw2u, Ne.symm hw12]⟩)
  have hT_inj : Function.Injective T := by
    intro i j hij
    apply hmem_inj
    rcases hT_val i with ⟨hmi, hti⟩ | ⟨hmi, hti⟩ | ⟨hmi, hti⟩ <;>
      rcases hT_val j with ⟨hmj, htj⟩ | ⟨hmj, htj⟩ | ⟨hmj, htj⟩ <;>
      rw [hmi, hmj] <;>
      first
        | rfl
        | (rw [hti, htj] at hij; exact absurd hij (by decide))
  have hnsp_eq : ∀ i, nbrSlotPoint (PencilSeed.ofCoord q) hubSel nbrSel u_c i
      = cs i • (Pi.single (T i) 1 : Fin 4 → K) := by
    intro i
    have h0 : nbrSlotPoint (PencilSeed.ofCoord q) hubSel nbrSel u_c i
        = pencilChartPoint (PencilSeed.ofCoord q) hubSel (mem i) := by
      simp only [nbrSlotPoint, hmem i]
    rcases hmem_mem i with h | h | h
    · have hcsi : cs i = cu := by simp [hcs_def, h]
      have hTi : T i = (3 : Fin 4) := by simp [hT_def, htgt_def, h]
      rw [h0, h, hpt_u, hcsi, hTi]
    · have hcsi : cs i = c1 := by simp [hcs_def, h, hw1u]
      have hTi : T i = (2 : Fin 4) := by simp [hT_def, htgt_def, h, hw1u]
      rw [h0, h, hpt_1, hcsi, hTi]
    · have hcsi : cs i = c2 := by simp [hcs_def, h, hw2u, Ne.symm hw12]
      have hTi : T i = (1 : Fin 4) := by simp [hT_def, htgt_def, h, hw2u, Ne.symm hw12]
      rw [h0, h, hpt_2, hcsi, hTi]
  have hNu : ∃ cc : K, cc ≠ 0 ∧
      pencilChartNormal (PencilSeed.ofCoord q) hubSel nbrSel (G.induce V₁) u_c
        = cc • (Pi.single (0 : Fin 4) 1 : Fin 4 → K) := by
    rw [pencilChartNormal_of_not_pencilHub _ _ _ hnothub_uc]
    have hLI3 : LinearIndependent K
        ![nbrSlotPoint (PencilSeed.ofCoord q) hubSel nbrSel u_c 0,
          nbrSlotPoint (PencilSeed.ofCoord q) hubSel nbrSel u_c 1,
          nbrSlotPoint (PencilSeed.ofCoord q) hubSel nbrSel u_c 2] := by
      have hfam : (![nbrSlotPoint (PencilSeed.ofCoord q) hubSel nbrSel u_c 0,
          nbrSlotPoint (PencilSeed.ofCoord q) hubSel nbrSel u_c 1,
          nbrSlotPoint (PencilSeed.ofCoord q) hubSel nbrSel u_c 2] : Fin 3 → Fin 4 → K)
          = fun i => cs i • (Pi.single (T i) 1 : Fin 4 → K) := by
        funext i; fin_cases i <;> exact hnsp_eq _
      rw [hfam]; exact linearIndependent_smul_pi_single_of_injective hT_inj hcs_ne
    have he0_ne : (Pi.single (0 : Fin 4) 1 : Fin 4 → K) ≠ 0 := by
      intro h; have := congrFun h 0; simp at this
    have horth : ∀ i, (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K) ⬝ᵥ
        nbrSlotPoint (PencilSeed.ofCoord q) hubSel nbrSel u_c i = 0 := by
      intro i
      rw [hnsp_eq i, dotProduct_smul, dotProduct_single_one]
      simp only [Pi.single_apply]
      rw [ite_eq_right (hT_ne i), smul_zero]
    obtain ⟨cc, hcc, hcross⟩ :=
      exists_smul_cross₃_eq_of_linearIndependent hLI3 he0_ne (horth 0) (horth 1) (horth 2)
    exact ⟨cc, hcc, hcross⟩
  -- Assemble the three families.
  obtain ⟨cu_n, hcu_n0, hNu_eq⟩ := hNu
  set cfam : α → K := fun x => if x = u_c then cu_n else 1 with hcfam_def
  have hcfam_ne : ∀ x, cfam x ≠ 0 := by
    intro x; simp only [hcfam_def]; split
    · exact hcu_n0
    · exact one_ne_zero
  have hval : ∀ x, G.PencilHub x → (x = u_c ∨ x ∈ V₁) →
      pencilChartNormal (PencilSeed.ofCoord q) hubSel nbrSel (G.induce V₁) x
        = cfam x • (Pi.single (idx x) 1 : Fin 4 → K) := by
    intro x hxhub _
    by_cases hxu : x = u_c
    · subst hxu; rw [hNu_eq]; simp only [hcfam_def, ite_eq_left rfl, hidx_u]
    · have hxV₁ : x ∈ V₁ := by
        have hxVG : x ∈ V(G) := hxhub.1
        rw [hVG] at hxVG
        rcases hxVG with h | h
        · exact h
        · rw [Set.mem_singleton_iff] at h; exact absurd (h ▸ hxhub) hvc_nothub
      have hxHhub : (G.induce V₁).PencilHub x := by
        refine ⟨hVH_mem x hxV₁, ?_⟩
        rw [Graph.degree_induce_eq_of_ne hl_c hu_c hv_c hcut hxV₁ hxu]; exact hxhub.2
      rw [pencilChartNormal_of_pencilHub _ _ _ hxHhub, hHubN]
      simp only [hcfam_def, ite_eq_right hxu, one_smul]
  refine ⟨q, fun v hv => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  have hval' : ∀ x ∈ G.closedHubNbhd v,
      pencilChartNormal (PencilSeed.ofCoord q) hubSel nbrSel (G.induce V₁) x
        = cfam x • (Pi.single (idx x) 1 : Fin 4 → K) := by
    intro x hx
    refine hval x hx.1 ?_
    by_cases hxu : x = u_c
    · exact Or.inl hxu
    · right
      have hxVG : x ∈ V(G) := hx.1.1
      rw [hVG] at hxVG
      rcases hxVG with h | h
      · exact h
      · rw [Set.mem_singleton_iff] at h; exact absurd (h ▸ hx.1) hvc_nothub
  have hinj : Set.InjOn idx (G.closedHubNbhd v) := by
    rcases hv with rfl | rfl | rfl
    exacts [hinjG_u, hinjG_1, hinjG_2]
  exact (linearIndepOn_smul_pi_single (J := idx) (c := cfam) hinj
    (fun x _ => hcfam_ne x)).congr (fun x hx => (hval' x hx).symm)

/-! ## The general-position core (Phase 39 W5-L6b-ii)

The reusable core of the v-b/v-c constructions above, extracted for the split arm's feasibility
producer `pencilNondegFeasible_of_ncard_closedHubNbhd_le_three_of_triangleFree`
(`notes/Phase39-design.md` §"W5 leaf decomposition" L6b). Its conclusion,
`∃ q, LinearIndepOn K (pencilChartPoint (PencilSeed.ofCoord q) hubSel) S`, is exactly the shape of
the two "satisfiable-somewhere" chart-point-LI families that the landed L6b-i assembly
`pencilNondegFeasible_of_selectors_of_satisfiable` (`Pencil/Steer.lean`) consumes. The **later**
L6b-ii commits build the per-set-shape direction/target maps (`{v}` / `closedNbhd v` per body,
`{p.1, p.2}` per adjacent pair) from `hcard` + triangle-freeness and wire the headline; this lemma
is the char-free general position engine they all call. -/

/-- **The general-position core of the pendant-cut somewhere-witness** (Phase 39 W5-L5/L6b-ii; the
reusable core of `exists_coord_linearIndependent_pencilChartPoint_of_pendant_deg3` and its `H`-side
sibling): given a direction map `idx` and a target-index map `dtgt`, both respected on the whole of
each body `s ∈ S`'s closed hub-neighbourhood — `idx` injective there and avoiding `dtgt s`, and the
targets `dtgt` distinct across `S` — some seed coordinate `q` makes each `s ∈ S`'s chart point a
nonzero multiple of the distinct standard basis vector `e_{dtgt s}`, hence the chart points
`LinearIndepOn` over `S`.

The construction is v-b's verbatim: `idx` becomes the seed's hub normals, and each body's
selector-induced slots are padded to an injective avoiding-`dtgt s` triple
(`exists_injective_extension_of_isFin3SelectorOf`), so its `cross₃` point is a nonzero multiple of
`e_{dtgt s}` (`exists_smul_cross₃_pi_single`); distinctness of the `dtgt` targets then gives
independence (`linearIndepOn_smul_pi_single`). Unlike v-b/v-c it fixes no configuration: the
per-set-shape callers supply `idx`/`dtgt` and the two combinatorial facts, so this lemma is entirely
char-free general position with no feasibility or graph structure of its own beyond `hHubSel`. -/
theorem exists_coord_linearIndepOn_pencilChartPoint_of_idx
    {G : Graph α β} {S : Set α} {idx dtgt : α → Fin 4}
    (hubSel : α → Fin 3 → Option α)
    (hHubSel : ∀ v, IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v))
    (hdinj : Set.InjOn dtgt S)
    (havoid : ∀ s ∈ S, ∀ x ∈ G.closedHubNbhd s, idx x ≠ dtgt s)
    (hinj : ∀ s ∈ S, Set.InjOn idx (G.closedHubNbhd s)) :
    ∃ q : α × Fin 4 × Fin 4 → K,
      LinearIndepOn K (pencilChartPoint (PencilSeed.ofCoord q) hubSel) S := by
  classical
  -- Per body in `S`, pull out the injective avoiding-`dtgt s` slot extension.
  have hex : ∀ s : α, ∃ σ : Fin 3 → Fin 4, s ∈ S →
      Function.Injective σ ∧ (∀ i, σ i ≠ dtgt s) ∧
        (∀ i w, hubSel s i = some w → σ i = idx w) := by
    intro s
    by_cases hs : s ∈ S
    · obtain ⟨σ, hσinj, hσd, hσm⟩ :=
        exists_injective_extension_of_isFin3SelectorOf (hHubSel s) (havoid s hs) (hinj s hs)
      exact ⟨σ, fun _ => ⟨hσinj, hσd, hσm⟩⟩
    · exact ⟨fun _ => 0, fun h => absurd h hs⟩
  choose σfam hσfam using hex
  -- The seed: hub normals from `idx`, fills from the per-body extensions (v-b's seed).
  set q : α × Fin 4 × Fin 4 → K :=
    fun p => Fin.cases (motive := fun _ => K)
      ((Pi.single (idx p.1) (1 : K) : Fin 4 → K) p.2.2)
      (fun j => (Pi.single (σfam p.1 j) (1 : K) : Fin 4 → K) p.2.2) p.2.1
    with hq_def
  refine ⟨q, ?_⟩
  have hHubN : ∀ v : α, (PencilSeed.ofCoord q).hubNormal v = Pi.single (idx v) (1 : K) := by
    intro v; funext i; simp [PencilSeed.ofCoord, hq_def]
  have hFillH : ∀ (v : α) (j : Fin 3),
      (PencilSeed.ofCoord q).fillHub v j = Pi.single (σfam v j) (1 : K) := by
    intro v j; funext i; simp [PencilSeed.ofCoord, hq_def]
  -- Each body's slot triple reads back the extension's basis vectors.
  have hslot : ∀ (v : α), (∀ i w, hubSel v i = some w → σfam v i = idx w) →
      ∀ i, hubSlotNormal (PencilSeed.ofCoord q) hubSel v i = Pi.single (σfam v i) (1 : K) := by
    intro v hmatch i
    cases hcase : hubSel v i with
    | none => simp only [hubSlotNormal, hcase, hFillH]
    | some w =>
        simp only [hubSlotNormal, hcase]
        rw [hHubN, hmatch i w hcase]
  -- On each `s ∈ S`, the chart point is a nonzero multiple of `e_{dtgt s}`.
  have hpt : ∀ s : α, ∃ cc : K, s ∈ S →
      cc ≠ 0 ∧ pencilChartPoint (PencilSeed.ofCoord q) hubSel s
        = cc • (Pi.single (dtgt s) 1 : Fin 4 → K) := by
    intro s
    by_cases hs : s ∈ S
    · obtain ⟨hσinj, hσd, hσm⟩ := hσfam s hs
      have hsl := hslot s hσm
      have h01 : σfam s 0 ≠ σfam s 1 := fun h => absurd (hσinj h) (by decide)
      have h02 : σfam s 0 ≠ σfam s 2 := fun h => absurd (hσinj h) (by decide)
      have h12 : σfam s 1 ≠ σfam s 2 := fun h => absurd (hσinj h) (by decide)
      obtain ⟨cc, hcc, hcross⟩ :=
        exists_smul_cross₃_pi_single (K := K) (hσd 0) (hσd 1) (hσd 2) h01 h02 h12
      exact ⟨cc, fun _ => ⟨hcc, by rw [pencilChartPoint, hsl 0, hsl 1, hsl 2, hcross]⟩⟩
    · exact ⟨1, fun h => absurd h hs⟩
  choose ccfam hccfam using hpt
  -- Distinct targets, rescaled by nonzero scalars, are independent.
  exact (linearIndepOn_smul_pi_single (K := K) (J := dtgt) (c := ccfam) hdinj
    (fun x hx => (hccfam x hx).1)).congr (fun x hx => ((hccfam x hx).2).symm)

/-! ## The per-set-shape callers (Phase 39 W5-L6b-ii)

The two "satisfiable-somewhere" chart-point-LI families that the landed L6b-i assembly
`pencilNondegFeasible_of_selectors_of_satisfiable` (`Pencil/Steer.lean`) consumes, built by
supplying the general-position core `exists_coord_linearIndepOn_pencilChartPoint_of_idx` with a
per-set-shape direction map `idx` and target map `dtgt`. This commit lands the **adjacent-pair**
family (`hsat_adj`'s shape); the per-body family (`hsat_pt`) and the headline wiring are the next
pieces (`notes/Phase39-design.md` §"W5 leaf decomposition" L6b-ii).

For the adjacent pair `{u, v}` (`u ~ v`), the two closed hub-neighbourhoods overlap only in
`{u, v}`: a common third hub `w` (a hub adjacent to both `u` and `v`) would close a triangle
`u–v–w`, excluded by triangle-freeness (`htf`). So the direction map `idx` can be built by a single
injection of `closedHubNbhd u` into a `3`-value palette avoiding `dtgt u`, plus a second injection
of the (disjoint) rest of `closedHubNbhd v` into the values avoiding both `dtgt v` and the image of
the overlap — the exact cardinalities coming from the `≤ 3` bound (`hcard`). -/

/-- **Inject a finite set into a finite set of no-smaller cardinality** (Phase 39 W5-L6b-ii helper;
upstream-eligible, `notes/FRICTION.md` [mirror-candidate]): if `T.ncard ≤ P.ncard`, there is a total
`f` injective on `T` and mapping `T` into `P` (junk `default` off `T`). Used to build the
per-set-shape direction maps `idx` the general-position core consumes. -/
theorem exists_injOn_mapsTo_of_ncard_le {γ δ : Type*} [Inhabited δ] {T : Set γ} {P : Set δ}
    (hT : T.Finite) (hP : P.Finite) (hle : T.ncard ≤ P.ncard) :
    ∃ f : γ → δ, Set.InjOn f T ∧ ∀ x ∈ T, f x ∈ P := by
  classical
  haveI := hT.fintype
  haveI := hP.fintype
  have hc : Fintype.card T ≤ Fintype.card P := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
      Nat.card_coe_set_eq]
    exact hle
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hc
  refine ⟨fun x => if h : x ∈ T then (e ⟨x, h⟩ : δ) else default, ?_, ?_⟩
  · intro x hx y hy hxy
    simp only [dite_eq_left hx, dite_eq_left hy] at hxy
    exact Subtype.ext_iff.mp (e.injective (Subtype.ext hxy))
  · intro x hx
    simp only [dite_eq_left hx]
    exact (e ⟨x, hx⟩).2

/-- **The direction/target maps for an adjacent pair** (Phase 39 W5-L6b-ii combinatorial core): for
distinct `u, v` whose two `≤ 3`-cardinality sets `U, V` overlap only inside `{u, v}` (`hcap` — the
triangle-freeness exclusion at the call site), there are direction/target maps `idx dtgt` with
`dtgt` injective on `{u, v}`, `idx` injective on each of `U, V` and avoiding the respective target.
`idx` sends `U` injectively into `{0, 1, 3}` (avoiding `dtgt u = 2`) via
`exists_injOn_mapsTo_of_ncard_le`, picks `dtgt v` outside `{2} ∪ idx '' (U ∩ V)`, and sends the
disjoint remainder `V \ U` into the values avoiding `dtgt v` and `idx '' (U ∩ V)` — the palette
sizes matching `V \ U` exactly because `|U ∩ V|` cancels (`≤ 3` on each side). -/
theorem exists_idx_dtgt_pair [Finite α] {u v : α} (huv : u ≠ v) {U V : Set α}
    (hcap : U ∩ V ⊆ ({u, v} : Set α)) (hU3 : U.ncard ≤ 3) (hV3 : V.ncard ≤ 3) :
    ∃ idx dtgt : α → Fin 4,
      Set.InjOn dtgt {u, v} ∧
      (∀ x ∈ U, idx x ≠ dtgt u) ∧ (∀ x ∈ V, idx x ≠ dtgt v) ∧
      Set.InjOn idx U ∧ Set.InjOn idx V := by
  classical
  -- `fu`: inject `U` into `{0, 1, 3}` (avoiding `dtgt u = 2`).
  have hPu : ({0, 1, 3} : Set (Fin 4)).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨0, 1, 3, by decide, by decide, by decide, rfl⟩
  obtain ⟨fu, hfu_inj, hfu_map⟩ :=
    exists_injOn_mapsTo_of_ncard_le (T := U) (P := ({0, 1, 3} : Set (Fin 4)))
      (Set.toFinite _) (Set.toFinite _) (hU3.trans hPu.ge)
  have hfu_ne2 : ∀ x ∈ U, fu x ≠ 2 := by
    intro x hx h2
    have hm := hfu_map x hx
    rw [h2] at hm
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with h | h | h <;> exact absurd h (by decide)
  set m := (U ∩ V).ncard with hm_def
  have hm2 : m ≤ 2 := by
    have h := Set.ncard_le_ncard hcap (Set.toFinite _)
    rwa [Set.ncard_pair huv] at h
  have hfuimg : (fu '' (U ∩ V)).ncard = m := (hfu_inj.mono Set.inter_subset_left).ncard_image
  have hXcard : (insert (2 : Fin 4) (fu '' (U ∩ V))).ncard ≤ 3 := by
    refine (Set.ncard_insert_le _ _).trans ?_
    rw [hfuimg]; omega
  obtain ⟨dtgtv, hdtgtv⟩ : ∃ d : Fin 4, d ∉ insert (2 : Fin 4) (fu '' (U ∩ V)) := by
    by_contra hcon
    push Not at hcon
    have huniv : (insert (2 : Fin 4) (fu '' (U ∩ V))) = Set.univ := Set.eq_univ_of_forall hcon
    rw [huniv, Set.ncard_univ] at hXcard
    simp [Nat.card_eq_fintype_card] at hXcard
  rw [Set.mem_insert_iff] at hdtgtv
  push Not at hdtgtv
  obtain ⟨hdtgtv2, hdtgtv_img⟩ := hdtgtv
  set Y := insert dtgtv (fu '' (U ∩ V)) with hY_def
  have hVU_add : (V \ U).ncard + m = V.ncard := by
    rw [hm_def, ← Set.sdiff_self_inter (s := V) (t := U), Set.inter_comm V U]
    exact Set.ncard_sdiff_add_ncard_of_subset Set.inter_subset_right (Set.toFinite _)
  have hY_card : Y.ncard = m + 1 := by
    rw [hY_def, Set.ncard_insert_of_notMem hdtgtv_img (Set.toFinite _), hfuimg]
  have hPv_add : (Set.univ \ Y).ncard + Y.ncard = 4 := by
    have h := Set.ncard_sdiff_add_ncard_of_subset (Set.subset_univ Y)
      (Set.toFinite (Set.univ : Set (Fin 4)))
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h
  obtain ⟨gv, hgv_inj, hgv_map⟩ :=
    exists_injOn_mapsTo_of_ncard_le (T := V \ U) (P := Set.univ \ Y)
      (Set.toFinite _) (Set.toFinite _) (by omega)
  have hgv_ne : ∀ x ∈ V \ U, gv x ≠ dtgtv ∧ gv x ∉ fu '' (U ∩ V) := by
    intro x hx
    have h := (hgv_map x hx).2
    rw [hY_def, Set.mem_insert_iff] at h
    push Not at h
    exact h
  -- The maps, with evaluation lemmas.
  set idx : α → Fin 4 := fun x => if x ∈ U then fu x else gv x with hidx_def
  set dtgt : α → Fin 4 := fun x => if x = u then (2 : Fin 4) else dtgtv with hdtgt_def
  have hidxU : ∀ x, x ∈ U → idx x = fu x := fun x hx => by rw [hidx_def]; exact ite_eq_left hx
  have hidxnU : ∀ x, x ∉ U → idx x = gv x := fun x hx => by rw [hidx_def]; exact ite_eq_right hx
  have hdtu : dtgt u = 2 := by rw [hdtgt_def]; exact ite_eq_left rfl
  have hdtv : dtgt v = dtgtv := by rw [hdtgt_def]; exact ite_eq_right huv.symm
  refine ⟨idx, dtgt, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · rw [hdtu, hdtv] at hxy; exact absurd hxy hdtgtv2.symm
    · rw [hdtu, hdtv] at hxy; exact absurd hxy hdtgtv2
    · rfl
  · intro x hx
    rw [hidxU x hx, hdtu]; exact hfu_ne2 x hx
  · intro x hx
    rw [hdtv]
    by_cases hxU : x ∈ U
    · rw [hidxU x hxU]
      have him : fu x ∈ fu '' (U ∩ V) := Set.mem_image_of_mem fu ⟨hxU, hx⟩
      intro h; rw [h] at him; exact hdtgtv_img him
    · rw [hidxnU x hxU]; exact (hgv_ne x ⟨hx, hxU⟩).1
  · intro x hx y hy hxy
    rw [hidxU x hx, hidxU y hy] at hxy
    exact hfu_inj hx hy hxy
  · intro x hx y hy hxy
    by_cases hxU : x ∈ U <;> by_cases hyU : y ∈ U
    · rw [hidxU x hxU, hidxU y hyU] at hxy; exact hfu_inj hxU hyU hxy
    · exfalso
      rw [hidxU x hxU, hidxnU y hyU] at hxy
      have h1 : fu x ∈ fu '' (U ∩ V) := Set.mem_image_of_mem fu ⟨hxU, hx⟩
      exact (hgv_ne y ⟨hy, hyU⟩).2 (hxy ▸ h1)
    · exfalso
      rw [hidxnU x hxU, hidxU y hyU] at hxy
      have h1 : fu y ∈ fu '' (U ∩ V) := Set.mem_image_of_mem fu ⟨hyU, hy⟩
      exact (hgv_ne x ⟨hx, hxU⟩).2 (hxy ▸ h1)
    · rw [hidxnU x hxU, hidxnU y hyU] at hxy
      exact hgv_inj ⟨hx, hxU⟩ ⟨hy, hyU⟩ hxy

/-- **The direction/target maps for a non-hub body and its (≤ 2) neighbours** (Phase 39 W5-L6b-ii
combinatorial core, the three-set analogue of `exists_idx_dtgt_pair`): for a non-hub centre `v`
with neighbours `a`, `b` (all distinct), whose closed hub-neighbourhoods `Xa`, `Xb` are `≤ 3` and
overlap in `≤ 2` *external* hubs (`hcap`; neither `a ∈ Xb` nor `b ∈ Xa`, by triangle-freeness),
and whose own closed hub-neighbourhood `Xv ⊆ {a, b}` sits inside `Xa`/`Xb` (`haXv`/`hbXv` — a hub
neighbour of `v` is a hub, hence in its own set), there are direction/target maps `idx dtgt` with
`dtgt` injective on `{v, a, b}` and `idx` injective on each of `Xv`, `Xa`, `Xb` avoiding the
respective target.

`Xa` injects into `{0, 1, 2}` (avoiding `dtgt a = 3`); `dtgt b` is picked as `idx a` when `a ∈ Xa`
(so `idx b`, forced off `dtgt b`, differs from `idx a`, giving injectivity on `Xv`) and otherwise
off `{3} ∪ idx '' (Xa ∩ Xb)`; the disjoint remainder `Xb \ Xa` fills the values avoiding `dtgt b`
and `idx '' (Xa ∩ Xb)`; `dtgt v` avoids `{3, dtgt b, idx b}`. The palette sizes match because
`(Xa ∩ Xb).ncard` cancels — `≤ 3` on each side against a `≤ 2` overlap, exactly the pair core's
arithmetic with the third set layered on. -/
theorem exists_idx_dtgt_triple [Finite α] {v a b : α}
    (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b) {Xv Xa Xb : Set α}
    (hXv : Xv ⊆ ({a, b} : Set α))
    (haXv : a ∈ Xv → a ∈ Xa) (hbXv : b ∈ Xv → b ∈ Xb)
    (haXb : a ∉ Xb) (hbXa : b ∉ Xa)
    (hcap : (Xa ∩ Xb).ncard ≤ 2) (hXa3 : Xa.ncard ≤ 3) (hXb3 : Xb.ncard ≤ 3) :
    ∃ idx dtgt : α → Fin 4,
      Set.InjOn dtgt ({v, a, b} : Set α) ∧
      (∀ x ∈ Xv, idx x ≠ dtgt v) ∧ (∀ x ∈ Xa, idx x ≠ dtgt a) ∧ (∀ x ∈ Xb, idx x ≠ dtgt b) ∧
      Set.InjOn idx Xv ∧ Set.InjOn idx Xa ∧ Set.InjOn idx Xb := by
  classical
  -- Inject `Xa` into `{0, 1, 2}` (avoiding `dtgt a = 3`).
  have hPa : ({0, 1, 2} : Set (Fin 4)).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨0, 1, 2, by decide, by decide, by decide, rfl⟩
  obtain ⟨fa, hfa_inj, hfa_map⟩ :=
    exists_injOn_mapsTo_of_ncard_le (T := Xa) (P := ({0, 1, 2} : Set (Fin 4)))
      (Set.toFinite _) (Set.toFinite _) (hXa3.trans hPa.ge)
  have hfa_ne3 : ∀ x ∈ Xa, fa x ≠ 3 := by
    intro x hx h3
    have hm := hfa_map x hx
    rw [h3] at hm
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with h | h | h <;> exact absurd h (by decide)
  set m := (Xa ∩ Xb).ncard with hm_def
  have hfaimg : (fa '' (Xa ∩ Xb)).ncard = m := (hfa_inj.mono Set.inter_subset_left).ncard_image
  -- `dtgt b`: `idx a` when `a ∈ Xa` (forcing `idx b ≠ idx a`), else off `{3} ∪ idx '' (Xa ∩ Xb)`.
  obtain ⟨db, hdb_notin, hdb_a⟩ :
      ∃ db : Fin 4, db ∉ insert (3 : Fin 4) (fa '' (Xa ∩ Xb)) ∧ (a ∈ Xa → db = fa a) := by
    by_cases ha : a ∈ Xa
    · refine ⟨fa a, ?_, fun _ => rfl⟩
      simp only [Set.mem_insert_iff, not_or]
      refine ⟨hfa_ne3 a ha, ?_⟩
      rintro ⟨w, hw, hwa⟩
      have hweqa : w = a := hfa_inj (Set.inter_subset_left hw) ha hwa
      exact haXb (hweqa ▸ Set.inter_subset_right hw)
    · have hins_le : (insert (3 : Fin 4) (fa '' (Xa ∩ Xb))).ncard ≤ 3 := by
        refine (Set.ncard_insert_le _ _).trans ?_
        rw [hfaimg]; omega
      obtain ⟨db, hdb⟩ : ∃ d : Fin 4, d ∉ insert (3 : Fin 4) (fa '' (Xa ∩ Xb)) := by
        by_contra hcon
        push Not at hcon
        have huniv : insert (3 : Fin 4) (fa '' (Xa ∩ Xb)) = Set.univ := Set.eq_univ_of_forall hcon
        rw [huniv, Set.ncard_univ] at hins_le
        simp [Nat.card_eq_fintype_card] at hins_le
      exact ⟨db, hdb, fun h => absurd h ha⟩
  rw [Set.mem_insert_iff] at hdb_notin
  push Not at hdb_notin
  obtain ⟨hdb3, hdb_img⟩ := hdb_notin
  -- The `dtgt b`-avoiding palette for the disjoint remainder `Xb \ Xa`.
  set Y := insert db (fa '' (Xa ∩ Xb)) with hY_def
  have hbXa_add : (Xb \ Xa).ncard + m = Xb.ncard := by
    rw [hm_def, ← Set.sdiff_self_inter (s := Xb) (t := Xa), Set.inter_comm Xa Xb]
    exact Set.ncard_sdiff_add_ncard_of_subset Set.inter_subset_left (Set.toFinite _)
  have hY_card : Y.ncard = m + 1 := by
    rw [hY_def, Set.ncard_insert_of_notMem hdb_img (Set.toFinite _), hfaimg]
  have hPrem_add : (Set.univ \ Y).ncard + Y.ncard = 4 := by
    have h := Set.ncard_sdiff_add_ncard_of_subset (Set.subset_univ Y)
      (Set.toFinite (Set.univ : Set (Fin 4)))
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h
  obtain ⟨gb, hgb_inj, hgb_map⟩ :=
    exists_injOn_mapsTo_of_ncard_le (T := Xb \ Xa) (P := Set.univ \ Y)
      (Set.toFinite _) (Set.toFinite _) (by omega)
  have hgb_ne : ∀ x ∈ Xb \ Xa, gb x ≠ db ∧ gb x ∉ fa '' (Xa ∩ Xb) := by
    intro x hx
    have h := (hgb_map x hx).2
    rw [hY_def, Set.mem_insert_iff] at h
    push Not at h
    exact h
  -- The index map, with evaluation lemmas.
  set idx : α → Fin 4 := fun x => if x ∈ Xa then fa x else gb x with hidx_def
  have hidxXa : ∀ x, x ∈ Xa → idx x = fa x := fun x hx => by rw [hidx_def]; exact ite_eq_left hx
  have hidxnXa : ∀ x, x ∉ Xa → idx x = gb x := fun x hx => by rw [hidx_def]; exact ite_eq_right hx
  have hidxb : idx b = gb b := hidxnXa b hbXa
  -- `dtgt v` avoiding `{3, db, idx b}`.
  obtain ⟨dv, hdv⟩ : ∃ d : Fin 4, d ∉ ({3, db, idx b} : Set (Fin 4)) := by
    have hle : ({3, db, idx b} : Set (Fin 4)).ncard ≤ 3 := by
      refine (Set.ncard_insert_le _ _).trans ?_
      refine Nat.add_le_add_right ((Set.ncard_insert_le _ _).trans ?_) 1
      simp
    by_contra hcon
    push Not at hcon
    have huniv : ({3, db, idx b} : Set (Fin 4)) = Set.univ := Set.eq_univ_of_forall hcon
    rw [huniv, Set.ncard_univ] at hle
    simp [Nat.card_eq_fintype_card] at hle
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hdv
  obtain ⟨hdv3, hdv_db, hdv_idxb⟩ := hdv
  -- The target map, with evaluation lemmas.
  set dtgt : α → Fin 4 := fun x => if x = v then dv else if x = a then (3 : Fin 4) else db
    with hdtgt_def
  have hdtv : dtgt v = dv := by rw [hdtgt_def]; exact ite_eq_left rfl
  have hdta : dtgt a = 3 := by
    rw [hdtgt_def]; exact (ite_eq_right (Ne.symm hva)).trans (ite_eq_left rfl)
  have hdtb : dtgt b = db := by
    rw [hdtgt_def]; exact (ite_eq_right (Ne.symm hvb)).trans (ite_eq_right (Ne.symm hab))
  refine ⟨idx, dtgt, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `dtgt` injective on `{v, a, b}`.
    intro x hx y hy hxy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · rfl
    · rw [hdtv, hdta] at hxy; exact absurd hxy hdv3
    · rw [hdtv, hdtb] at hxy; exact absurd hxy hdv_db
    · rw [hdtv, hdta] at hxy; exact absurd hxy.symm hdv3
    · rfl
    · rw [hdta, hdtb] at hxy; exact absurd hxy (Ne.symm hdb3)
    · rw [hdtv, hdtb] at hxy; exact absurd hxy.symm hdv_db
    · rw [hdta, hdtb] at hxy; exact absurd hxy.symm (Ne.symm hdb3)
    · rfl
  · -- avoid at `v`.
    intro x hx
    rw [hdtv]
    have hxab := hXv hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxab
    rcases hxab with rfl | rfl
    · rw [hidxXa x (haXv hx), ← hdb_a (haXv hx)]; exact Ne.symm hdv_db
    · exact Ne.symm hdv_idxb
  · -- avoid at `a`.
    intro x hx
    rw [hidxXa x hx, hdta]
    exact hfa_ne3 x hx
  · -- avoid at `b`.
    intro x hx
    rw [hdtb]
    by_cases hxXa : x ∈ Xa
    · rw [hidxXa x hxXa]
      intro heq
      exact hdb_img (heq ▸ Set.mem_image_of_mem fa ⟨hxXa, hx⟩)
    · rw [hidxnXa x hxXa]
      exact (hgb_ne x ⟨hx, hxXa⟩).1
  · -- `idx` injective on `Xv`.
    intro x hx y hy hxy
    have hxab := hXv hx
    have hyab := hXv hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxab hyab
    rcases hxab with hxa | hxb
    · rcases hyab with hya | hyb
      · rw [hxa, hya]
      · exfalso
        have hax : a ∈ Xv := hxa ▸ hx
        have hby : b ∈ Xv := hyb ▸ hy
        rw [hxa, hyb, hidxXa a (haXv hax), ← hdb_a (haXv hax), hidxb] at hxy
        exact (hgb_ne b ⟨hbXv hby, hbXa⟩).1 hxy.symm
    · rcases hyab with hya | hyb
      · exfalso
        have hbx : b ∈ Xv := hxb ▸ hx
        have hay : a ∈ Xv := hya ▸ hy
        rw [hxb, hya, hidxXa a (haXv hay), ← hdb_a (haXv hay), hidxb] at hxy
        exact (hgb_ne b ⟨hbXv hbx, hbXa⟩).1 hxy
      · rw [hxb, hyb]
  · -- `idx` injective on `Xa`.
    intro x hx y hy hxy
    rw [hidxXa x hx, hidxXa y hy] at hxy
    exact hfa_inj hx hy hxy
  · -- `idx` injective on `Xb`.
    intro x hx y hy hxy
    by_cases hxXa : x ∈ Xa <;> by_cases hyXa : y ∈ Xa
    · rw [hidxXa x hxXa, hidxXa y hyXa] at hxy; exact hfa_inj hxXa hyXa hxy
    · exfalso
      rw [hidxXa x hxXa, hidxnXa y hyXa] at hxy
      exact (hgb_ne y ⟨hy, hyXa⟩).2 (hxy ▸ Set.mem_image_of_mem fa ⟨hxXa, hx⟩)
    · exfalso
      rw [hidxnXa x hxXa, hidxXa y hyXa] at hxy
      exact (hgb_ne x ⟨hx, hxXa⟩).2 (hxy ▸ Set.mem_image_of_mem fa ⟨hyXa, hy⟩)
    · rw [hidxnXa x hxXa, hidxnXa y hyXa] at hxy
      exact hgb_inj ⟨hx, hxXa⟩ ⟨hy, hyXa⟩ hxy

open Classical in
/-- **The adjacent-pair somewhere-witness family** (Phase 39 W5-L6b-ii; the `hsat_adj` input of
`pencilNondegFeasible_of_selectors_of_satisfiable`): for any ordered pair `p`, some seed coordinate
`q` makes the chart points linearly independent over `{p.1, p.2}` when the two are adjacent (over
`∅` otherwise, trivially). Adjacency plus triangle-freeness (`htf`) confine the two closed
hub-neighbourhoods' overlap to `{p.1, p.2}`, so `exists_idx_dtgt_pair` builds the direction/target
maps the general-position core `exists_coord_linearIndepOn_pencilChartPoint_of_idx` consumes; the
`≤ 3` bound is `hcard`. -/
theorem exists_coord_linearIndepOn_pencilChartPoint_adjacentPair
    [Finite α] [Finite β] {G : Graph α β} [G.Loopless]
    (hcard : ∀ v, (G.closedHubNbhd v).ncard ≤ 3)
    (htf : ∀ e₁ e₂ e₃ x y z, x ≠ y → y ≠ z → x ≠ z →
      G.IsLink e₁ x y → G.IsLink e₂ y z → G.IsLink e₃ z x → False)
    (hubSel : α → Fin 3 → Option α)
    (hHubSel : ∀ v, IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v))
    (p : α × α) :
    ∃ q : α × Fin 4 × Fin 4 → K,
      LinearIndepOn K (pencilChartPoint (PencilSeed.ofCoord q) hubSel)
        (if G.Adj p.1 p.2 then ({p.1, p.2} : Set α) else ∅) := by
  classical
  obtain ⟨u, v⟩ := p
  by_cases hadj : G.Adj u v
  · rw [ite_eq_left hadj]
    obtain ⟨e_uv, hl_uv⟩ := hadj
    have huv : u ≠ v := hl_uv.ne
    -- Triangle-freeness confines the two hub-neighbourhoods' overlap to `{u, v}`.
    have hcap : G.closedHubNbhd u ∩ G.closedHubNbhd v ⊆ ({u, v} : Set α) := by
      intro w hw
      by_cases hwu : w = u
      · exact Or.inl hwu
      by_cases hwv : w = v
      · exact Or.inr hwv
      obtain ⟨e_uw, hl_uw⟩ := hw.1.2.resolve_left hwu
      obtain ⟨e_vw, hl_vw⟩ := hw.2.2.resolve_left hwv
      exact (htf e_uv e_vw e_uw u v w huv (Ne.symm hwv) (Ne.symm hwu)
        hl_uv hl_vw hl_uw.symm).elim
    obtain ⟨idx, dtgt, hdinj, hav_u, hav_v, hinj_u, hinj_v⟩ :=
      exists_idx_dtgt_pair huv hcap (hcard u) (hcard v)
    refine exists_coord_linearIndepOn_pencilChartPoint_of_idx (S := ({u, v} : Set α))
      (idx := idx) (dtgt := dtgt) hubSel hHubSel hdinj ?_ ?_
    · intro s hs
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with rfl | rfl
      · exact hav_u
      · exact hav_v
    · intro s hs
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with rfl | rfl
      · exact hinj_u
      · exact hinj_v
  · rw [ite_eq_right hadj]
    exact ⟨fun _ => 0, linearIndepOn_empty K _⟩

/-! ## The per-body somewhere-witness (Phase 39 W5-L6b-ii)

The `hsat_pt` input of the L6b-i assembly `pencilNondegFeasible_of_selectors_of_satisfiable`
(`Pencil/Steer.lean`): a per-body chart-point-LI family over `{v}` at a hub and over `closedNbhd v`
at a non-hub. The hub / degree-`0` cases are the trivial singleton witness; a non-hub of degree `1`
reuses the two-set core `exists_idx_dtgt_pair`; a non-hub of degree `2` uses the three-set core
`exists_idx_dtgt_triple`, whose overlap hypotheses triangle-freeness (`htf`) and the `≤ 3` bounds
(`hcard`, `ncard_closedNbhd_le_three_of_not_pencilHub`) discharge. -/

/-- **The singleton somewhere-witness** (Phase 39 W5-L6b-ii helper): the trivial one-set case — at
any body `v`, some seed coordinate makes the chart point independent over `{v}` (nonzero), by
injecting `closedHubNbhd v` (`≤ 3` by `hcard`) into `{0, 1, 2}` and targeting `3`. Used for the hub
branch (`{v}`) and the degree-`0` non-hub branch (`closedNbhd v = {v}`) of the per-body family. -/
private theorem exists_coord_linearIndepOn_pencilChartPoint_hubSingleton [Finite α]
    {G : Graph α β} (hcard : ∀ v, (G.closedHubNbhd v).ncard ≤ 3)
    (hubSel : α → Fin 3 → Option α)
    (hHubSel : ∀ v, IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v)) (v : α) :
    ∃ q : α × Fin 4 × Fin 4 → K,
      LinearIndepOn K (pencilChartPoint (PencilSeed.ofCoord q) hubSel) ({v} : Set α) := by
  obtain ⟨idx, hidx_inj, hidx_map⟩ :=
    exists_injOn_mapsTo_of_ncard_le (T := G.closedHubNbhd v) (P := ({0, 1, 2} : Set (Fin 4)))
      (Set.toFinite _) (Set.toFinite _)
      ((hcard v).trans (Set.ncard_eq_three.mpr ⟨0, 1, 2, by decide, by decide, by decide, rfl⟩).ge)
  refine exists_coord_linearIndepOn_pencilChartPoint_of_idx (S := ({v} : Set α))
    (idx := idx) (dtgt := fun _ => 3) hubSel hHubSel ?_ ?_ ?_
  · intro x hx y hy _
    rw [Set.mem_singleton_iff] at hx hy
    rw [hx, hy]
  · intro s hs x hx
    rw [Set.mem_singleton_iff] at hs
    subst hs
    intro heq
    have hm := hidx_map x hx
    rw [heq] at hm
    simp at hm
  · intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    exact hidx_inj

open Classical in
/-- **The per-body somewhere-witness family** (Phase 39 W5-L6b-ii; the `hsat_pt` input of
`pencilNondegFeasible_of_selectors_of_satisfiable`): for any body `v`, some seed coordinate `q`
makes the chart points independent over `{v}` at a hub (point nonvanishing) and over the closed
neighbourhood `closedNbhd v` at a non-hub. The hub / degree-`0` cases reduce to the singleton
witness; a non-hub of degree `1` (`closedNbhd v = {v, a}`) reuses the two-set core
`exists_idx_dtgt_pair`; a non-hub of degree `2` (`closedNbhd v = {v, a, b}`) uses the three-set
core `exists_idx_dtgt_triple` — its overlap hypotheses discharged by triangle-freeness (`htf`
excludes `a ~ b` and any common hub-neighbour closing a triangle) and the `≤ 3` bounds. -/
theorem exists_coord_linearIndepOn_pencilChartPoint_perBody
    [Finite α] [Finite β] {G : Graph α β} [G.Loopless]
    (hcard : ∀ v, (G.closedHubNbhd v).ncard ≤ 3)
    (htf : ∀ e₁ e₂ e₃ x y z, x ≠ y → y ≠ z → x ≠ z →
      G.IsLink e₁ x y → G.IsLink e₂ y z → G.IsLink e₃ z x → False)
    (hubSel : α → Fin 3 → Option α)
    (hHubSel : ∀ v, IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v))
    (v : α) :
    ∃ q : α × Fin 4 × Fin 4 → K,
      LinearIndepOn K (pencilChartPoint (PencilSeed.ofCoord q) hubSel)
        (if G.PencilHub v then ({v} : Set α) else G.closedNbhd v) := by
  classical
  by_cases hv : G.PencilHub v
  · rw [ite_eq_left hv]
    exact exists_coord_linearIndepOn_pencilChartPoint_hubSingleton hcard hubSel hHubSel v
  · rw [ite_eq_right hv]
    -- `v` non-hub: `closedNbhd v = insert v N(G,v)`, `|N(G,v)| ≤ 2`.
    have hdeg : G.degree v ≤ 2 := by
      by_contra hcon
      push Not at hcon
      by_cases hvV : v ∈ V(G)
      · exact hv ⟨hvV, by omega⟩
      · have h0 := Graph.degree_eq_zero_of_notMem (G := G) hvV
        omega
    have hNle : (N(G, v)).encard ≤ G.eDegree v :=
      (Graph.encard_adj_le_encard_inc).trans (Graph.encard_inc_le_eDegree)
    have heDeg : (G.degree v : ℕ∞) = G.eDegree v := Graph.natCast_degree_eq G v
    rw [← heDeg] at hNle
    have hcast : (G.degree v : ℕ∞) ≤ (2 : ℕ∞) := by exact_mod_cast hdeg
    have hNle2 : (N(G, v)).encard ≤ (2 : ℕ∞) := hNle.trans hcast
    obtain ⟨hNfin, hNcard⟩ := Set.encard_le_coe_iff_finite_ncard_le.mp hNle2
    obtain h0 | h1 | h2 :
        (N(G, v)).ncard = 0 ∨ (N(G, v)).ncard = 1 ∨ (N(G, v)).ncard = 2 := by
      rcases Nat.lt_or_ge (N(G, v)).ncard 1 with h | h
      · exact Or.inl (by omega)
      · rcases Nat.lt_or_ge (N(G, v)).ncard 2 with h' | h'
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr (le_antisymm hNcard h'))
    · -- degree `0`: `closedNbhd v = {v}`.
      have hcn : G.closedNbhd v = insert v (N(G, v)) := rfl
      have hS : G.closedNbhd v = ({v} : Set α) := by
        rw [hcn, (Set.ncard_eq_zero hNfin).mp h0]; simp
      rw [hS]
      exact exists_coord_linearIndepOn_pencilChartPoint_hubSingleton hcard hubSel hHubSel v
    · -- degree `1`: `closedNbhd v = {v, a}`, two-set core.
      obtain ⟨a, h1eq⟩ := Set.ncard_eq_one.mp h1
      have haN : a ∈ N(G, v) := by rw [h1eq]; simp
      obtain ⟨e_a, hl_a⟩ : G.Adj v a := haN
      have hva : v ≠ a := hl_a.ne
      have hcn : G.closedNbhd v = insert v (N(G, v)) := rfl
      have hS : G.closedNbhd v = ({v, a} : Set α) := by rw [hcn, h1eq]
      have hcap : G.closedHubNbhd v ∩ G.closedHubNbhd a ⊆ ({v, a} : Set α) := by
        intro w hw
        rcases hw.1.2 with heq | ⟨e_vw, hl_vw⟩
        · exact Or.inl heq
        · have hwN : w ∈ N(G, v) := hl_vw.adj
          rw [h1eq] at hwN
          exact Or.inr hwN
      obtain ⟨idx, dtgt, hdinj, hav_u, hav_a, hinj_u, hinj_a⟩ :=
        exists_idx_dtgt_pair hva hcap (hcard v) (hcard a)
      rw [hS]
      refine exists_coord_linearIndepOn_pencilChartPoint_of_idx (S := ({v, a} : Set α))
        (idx := idx) (dtgt := dtgt) hubSel hHubSel hdinj ?_ ?_
      · intro s hs x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl
        · exact hav_u x hx
        · exact hav_a x hx
      · intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl
        · exact hinj_u
        · exact hinj_a
    · -- degree `2`: `closedNbhd v = {v, a, b}`, three-set core.
      obtain ⟨a, b, hab, h2eq⟩ := Set.ncard_eq_two.mp h2
      have haN : a ∈ N(G, v) := by rw [h2eq]; simp
      have hbN : b ∈ N(G, v) := by rw [h2eq]; simp
      obtain ⟨e_a, hl_a⟩ : G.Adj v a := haN
      obtain ⟨e_b, hl_b⟩ : G.Adj v b := hbN
      have hva : v ≠ a := hl_a.ne
      have hvb : v ≠ b := hl_b.ne
      have hcn : G.closedNbhd v = insert v (N(G, v)) := rfl
      have hS : G.closedNbhd v = ({v, a, b} : Set α) := by rw [hcn, h2eq]
      have hXv : G.closedHubNbhd v ⊆ ({a, b} : Set α) := by
        intro w hw
        rcases hw.2 with heq | ⟨e_vw, hl_vw⟩
        · exact absurd (heq ▸ hw.1) hv
        · have hwN : w ∈ N(G, v) := hl_vw.adj
          rw [h2eq] at hwN
          exact hwN
      have haXv : a ∈ G.closedHubNbhd v → a ∈ G.closedHubNbhd a := fun h => ⟨h.1, Or.inl rfl⟩
      have hbXv : b ∈ G.closedHubNbhd v → b ∈ G.closedHubNbhd b := fun h => ⟨h.1, Or.inl rfl⟩
      have haXb : a ∉ G.closedHubNbhd b := by
        intro haCHb
        rcases haCHb.2 with heq | ⟨e_ba, hl_ba⟩
        · exact hab heq
        · exact htf e_a e_ba e_b v a b hva hab hvb hl_a hl_ba.symm hl_b.symm
      have hbXa : b ∉ G.closedHubNbhd a := by
        intro hbCHa
        rcases hbCHa.2 with heq | ⟨e_ab, hl_ab⟩
        · exact hab heq.symm
        · exact htf e_b e_ab e_a v b a hvb hab.symm hva hl_b hl_ab.symm hl_a.symm
      have hcap : (G.closedHubNbhd a ∩ G.closedHubNbhd b).ncard ≤ 2 := by
        have hsub : G.closedHubNbhd a ∩ G.closedHubNbhd b ⊆ G.closedHubNbhd a \ {a} := by
          intro w hw
          refine ⟨hw.1, ?_⟩
          intro hwa
          rw [Set.mem_singleton_iff] at hwa
          exact haXb (hwa ▸ hw.2)
        refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
        by_cases hha : G.PencilHub a
        · have haa : a ∈ G.closedHubNbhd a := ⟨hha, Or.inl rfl⟩
          rw [Set.ncard_sdiff_singleton_of_mem haa]
          have := hcard a; omega
        · have haCN : a ∈ G.closedNbhd a := Or.inl rfl
          have hsub2 : G.closedHubNbhd a \ {a} ⊆ G.closedNbhd a \ {a} := by
            intro w hw
            exact ⟨hw.1.2, hw.2⟩
          refine (Set.ncard_le_ncard hsub2 (Set.toFinite _)).trans ?_
          rw [Set.ncard_sdiff_singleton_of_mem haCN]
          have := ncard_closedNbhd_le_three_of_not_pencilHub hha
          omega
      obtain ⟨idx, dtgt, hdinj, hav_v, hav_a, hav_b, hinj_v, hinj_a, hinj_b⟩ :=
        exists_idx_dtgt_triple hva hvb hab hXv haXv hbXv haXb hbXa hcap (hcard a) (hcard b)
      rw [hS]
      refine exists_coord_linearIndepOn_pencilChartPoint_of_idx (S := ({v, a, b} : Set α))
        (idx := idx) (dtgt := dtgt) hubSel hHubSel hdinj ?_ ?_
      · intro s hs x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl | rfl
        · exact hav_v x hx
        · exact hav_a x hx
        · exact hav_b x hx
      · intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl | rfl
        · exact hinj_v
        · exact hinj_a
        · exact hinj_b

end CombinatorialRigidity.Molecular
