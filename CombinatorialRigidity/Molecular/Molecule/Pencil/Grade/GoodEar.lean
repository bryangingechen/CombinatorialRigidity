/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.GoodEar

/-!
# A body of degree two in a minimal planar-rigid set, with the set

The node `lem:pencil-d-good-ear` of `blueprint/src/chapter/pencil-d.tex`, `sec:pencil-d-generic`:
the good ear of `lem:pencil-rigid-good-ear`, returning the minimal planar-rigid set `W₀` and with
the extra clauses (iii) to (v) that the ear's lift needs (`Graph.IsPencilGoodEar`). The proof
starts from `Graph.IsX0Graph.exists_minimalRigid_ear_or_pendantTriangle`, which returns `W₀`.

* (iii): the ends keep two neighbours in `X = W₀ \ {x}` by the triangle step
  (`Graph.exists_eq_triple_of_minimal`, with `a` not adjacent to `b`); `s(X) = 1`
  (`Graph.partitionDef_two_induce_insert_id`); `def₂(G[X]) = 1`
  (`Graph.deficiency_two_induce_le_one_of_tight`); `G[X]` is connected, as a cut with no edge
  would add `D = 3` to the deficiency (`Graph.preconnected_of_deficiency_two_lt`).
* (iv): `G[X]` is rigid at every `d ≥ 3` (`Graph.deficiency_three_induce_eq_zero_of_tight`,
  `Graph.deficiency_eq_zero_of_deficiency_eq_zero_of_le`), so
  `def_d(G - x) ≤ def_d(G)` (`Graph.deficiencyMerged_eq_deficiency_of_mem`,
  `Graph.IsOpenEar.deficiency_induce_le`), and a partition of `V(G)` has value at most that of
  its restriction (`Graph.partitionDef_induce_insert`).
* (v): from (i), the degrees, and the hub condition `hF1`.

## Main results

* `Graph.IsPencilGoodEar`: `W₀`, `x`, `a`, `b` with the clauses (i) to (v) of the node.
* `Graph.IsX0Graph.exists_goodEar_or_pendantTriangle`: `lem:pencil-d-good-ear`.
-/

@[expose] public section

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {α β : Type*}

/-- **A body of degree two in a minimal planar-rigid set** (`lem:pencil-d-good-ear`, parts (i) to
(v), second outcome): `W₀`, `x ∈ W₀` and the neighbours `a`, `b` of `x`. The singleton value `s`
of the node, at `D = 3`, is `partitionDef 2 id` (`bodyBarDim 2 = 3`); `deficiency n` is `def_d` at
`d = n`, with `D = Graph.bodyBarDim n`. -/
structure _root_.Graph.IsPencilGoodEar (G : Graph α β) (W₀ : Set α) (x a b : α) : Prop where
  subset : W₀ ⊆ V(G)
  /-- (i): `s(W₀) ≤ 0`. -/
  partitionDef_le : (G.induce W₀).partitionDef 2 id ≤ 0
  /-- (i): `s(Z) ≥ 1` for `Z ⊊ W₀` with `|Z| ≥ 2`. -/
  one_le_partitionDef : ∀ Z ⊆ W₀, Z ≠ W₀ → 2 ≤ Z.ncard → 1 ≤ (G.induce Z).partitionDef 2 id
  /-- (i): every body of `W₀` has two neighbours in `W₀`. -/
  two_le_nbrs : ∀ v ∈ W₀, 2 ≤ {w | w ∈ W₀ ∧ G.Adj v w}.ncard
  /-- (ii) -/
  mem : x ∈ W₀
  degree_eq : G.degree x = 2
  adj_a : G.Adj x a
  adj_b : G.Adj x b
  ne : a ≠ b
  a_mem : a ∈ W₀
  b_mem : b ∈ W₀
  hub_a : G.PencilHub a
  hub_b : G.PencilHub b
  not_adj : ¬ G.Adj a b
  /-- (iii) -/
  three_le : 3 ≤ (W₀ \ {x}).ncard
  connected : (G.induce (W₀ \ {x})).Connected
  two_le_degree : ∀ v ∈ W₀ \ {x}, 2 ≤ (G.induce (W₀ \ {x})).degree v
  partitionDef_eq : (G.induce (W₀ \ {x})).partitionDef 2 id = 1
  deficiency_eq : (G.induce (W₀ \ {x})).deficiency 2 = 1
  deficiency_ne : ∀ Z ⊆ W₀ \ {x}, 2 ≤ Z.ncard → (G.induce Z).deficiency 2 ≠ 0
  /-- (iv): `def_d(G - x) = def_d(G)` for every `d ≥ 3`. -/
  deficiency_delete : ∀ n, 3 ≤ n → (G.induce (V(G) \ {x})).deficiency n = G.deficiency n
  /-- (v) -/
  outside : ∀ u ∈ V(G) \ W₀, {w | w ∈ W₀ ∧ G.Adj u w}.ncard ≤ 2 ∧
    ∀ w ∈ W₀, G.Adj u w → G.PencilHub w
  hub_of_outside : ∀ w ∈ W₀, (∃ u ∈ V(G) \ W₀, G.Adj w u) → G.PencilHub w

/-- **Links into a set are at most its neighbours there** (a step of `lem:pencil-d-good-ear` (i)):
in a simple graph, the edges from `v` into `W` are at most as many as the neighbours of `v` in
`W`. -/
theorem _root_.Graph.ncard_setOf_isLink_le_ncard_adj [Finite α] {G : Graph α β} [G.Simple]
    (v : α) (W : Set α) :
    ({e | ∃ z ∈ W, G.IsLink e v z} : Set β).ncard ≤ ({w | w ∈ W ∧ G.Adj v w} : Set α).ncard := by
  classical
  refine Set.ncard_le_ncard_of_injOn
    (fun e => if h : ∃ z, z ∈ W ∧ G.IsLink e v z then h.choose else v) ?_ ?_ (Set.toFinite _)
  · rintro e ⟨z, hz, hl⟩
    have h : ∃ z, z ∈ W ∧ G.IsLink e v z := ⟨z, hz, hl⟩
    simp only [h, ↓reduceDIte]
    exact ⟨h.choose_spec.1, _, h.choose_spec.2⟩
  · rintro e₁ ⟨z₁, hz₁, hl₁⟩ e₂ ⟨z₂, hz₂, hl₂⟩ heq
    have h₁ : ∃ z, z ∈ W ∧ G.IsLink e₁ v z := ⟨z₁, hz₁, hl₁⟩
    have h₂ : ∃ z, z ∈ W ∧ G.IsLink e₂ v z := ⟨z₂, hz₂, hl₂⟩
    simp only [h₁, h₂, ↓reduceDIte] at heq
    have h := h₁.choose_spec.2
    rw [heq] at h
    exact h.unique_edge h₂.choose_spec.2

/-- **A graph of deficiency below `D` is preconnected** (a step of `lem:pencil-d-good-ear` (iii)):
if `H` is not preconnected, the component `V'` of a body is a proper part with no edge across, so
`def₂(H) = def₂(H[V']) + def₂(H[V(H) \ V']) + 3 ≥ 3`
(`Graph.deficiency_eq_of_cutEdges_ncard_le_one`, `Graph.deficiency_nonneg`). -/
theorem _root_.Graph.preconnected_of_deficiency_two_lt [Finite α] [Finite β] {H : Graph α β}
    (h : H.deficiency 2 < 3) : H.Preconnected := by
  by_contra hcon
  simp only [Graph.Preconnected, not_forall] at hcon
  obtain ⟨x, y, hx, hy, hxy⟩ := hcon
  set V' : Set α := {z | H.ConnBetween x z} with hV'def
  have hxV' : x ∈ V' := Graph.ConnBetween.refl hx
  have hyV' : y ∉ V' := hxy
  have hsub : V' ⊆ V(H) := fun z hz => (show H.ConnBetween x z from hz).right_mem
  have hssub : V' ⊂ V(H) := by
    refine hsub.ssubset_of_ne fun heq => hyV' ?_
    rw [heq]; exact hy
  have hempty : H.cutEdges V' = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro e ⟨_, u, v, hlink, huV', hvV'⟩
    have hxu : H.ConnBetween x u := huV'
    exact hvV' (hxu.trans hlink.connBetween)
  have hdec := Graph.deficiency_eq_of_cutEdges_ncard_le_one (n := 2) hssub
    (by rw [hempty, Set.ncard_empty]; omega)
  rw [hempty, Set.ncard_empty, Graph.bodyBarDim_two] at hdec
  have h1 : 0 ≤ (H.induce V').deficiency 2 := Graph.deficiency_nonneg _ 2 ⟨x, hxV'⟩
  have h2 : 0 ≤ (H.induce (V(H) \ V')).deficiency 2 :=
    Graph.deficiency_nonneg _ 2 ⟨y, hy, hyV'⟩
  push_cast at hdec
  linarith

/-- **A tight set has planar deficiency at most one** (a step of `lem:pencil-d-good-ear` (iii)):
let `s(Z) ≥ 1` for every `Z ⊆ X` with `|Z| ≥ 2` and `s(X) ≤ 1`. A labeling injective on `X` has the
value `s(X)`, a constant one the value `0`, and otherwise a part `Z` with `2 ≤ |Z| < |X|` has value
at most `s(X) - s(Z) ≤ 0` (`Graph.partitionDef_add_partitionDef_induce_id_le`,
`lem:deficiency-singleton-bound`). -/
theorem _root_.Graph.deficiency_two_induce_le_one_of_tight [Finite α] [Finite β] {G : Graph α β}
    {X : Set α} (hSv : ∀ Z ⊆ X, 2 ≤ Z.ncard → 1 ≤ (G.induce Z).partitionDef 2 id)
    (hX1 : (G.induce X).partitionDef 2 id ≤ 1) : (G.induce X).deficiency 2 ≤ 1 := by
  have : Nonempty (α → α) := ⟨id⟩
  have hnn := Graph.partitionDef_induce_id_nonneg hSv
  refine ciSup_le fun f => ?_
  by_cases hinj : Set.InjOn f X
  · have hid2 : (G.induce X).partitionDef 2 f = (G.induce X).partitionDef 2 id := by
      have := Graph.partitionDef_comp_of_injOn (G := G.induce X) (n := 2) (f := id) (g := f)
        (by simpa using hinj)
      simpa using this
    rw [hid2]
    exact hX1
  · simp only [Set.InjOn, not_forall] at hinj
    obtain ⟨u, hu, w, hw, hfuw, huw⟩ := hinj
    by_cases hall : ∀ y ∈ X, f y = f u
    · exact (Graph.partitionDef_eq_zero_of_forall_eq (G := G.induce X) hu hall).le.trans
        zero_le_one
    push Not at hall
    have hZ₀X : {z ∈ V(G.induce X) | f z = f u} ⊆ X := fun z hz => hz.1
    have hK := Graph.partitionDef_add_partitionDef_induce_id_le (G := G.induce X) (n := 2) f hu
      (fun Z hZ hZne => by
        have hZX : Z ⊆ X := hZ.trans Set.sdiff_subset
        rw [Graph.induce_induce_of_subset G hZX]
        exact hnn Z hZX hZne)
    rw [Graph.induce_induce_of_subset G hZ₀X] at hK
    have hZ₀2 : 2 ≤ ({z ∈ V(G.induce X) | f z = f u}).ncard := by
      have hsub : ({u, w} : Set α) ⊆ {z ∈ V(G.induce X) | f z = f u} := by
        rintro z (rfl | rfl)
        · exact ⟨hu, rfl⟩
        · exact ⟨hw, hfuw.symm⟩
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      rwa [Set.ncard_pair huw] at this
    have hZ₀ := hSv _ hZ₀X hZ₀2
    linarith

/-- `3 ≤ D` for `d ≥ 3`. -/
lemma three_le_bodyBarDim {n : ℕ} (hn : 3 ≤ n) : 3 ≤ Graph.bodyBarDim n := by
  unfold Graph.bodyBarDim
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  nlinarith

/-- **A body of degree two in a minimal planar-rigid set, with the set, or a pendant triangle**
(`lem:pencil-d-good-ear`): let `G` satisfy the standing hypotheses and be two-edge-connected on at
least four bodies, with every closed hub-neighbourhood of at most three members, no triangle
containing two pencil hubs, and a planar-rigid set. Then `G` has a pendant triangle, or a set `W₀`
and `x`, `a`, `b` with `Graph.IsPencilGoodEar`.

The set is that of `Graph.IsX0Graph.exists_minimalRigid_ear_or_pendantTriangle`, and (i) and (ii)
are its output. (iii) is the triangle step at `x` and an end that had one neighbour in `W₀ \ {x}`,
then the singleton values; (iv) `X = W₀ \ {x}` is rigid at every `d ≥ 3`, so
`def_d(G - x; a, b) = def_d(G - x) ≤ def_d(G)`, and a partition of `V(G)` has value at most that
of its restriction to `V(G) \ {x}`; (v) the degrees, and `hF1`. -/
theorem _root_.Graph.IsX0Graph.exists_goodEar_or_pendantTriangle [Finite α] [Finite β]
    {G : Graph α β} (hG : G.IsX0Graph) (htec : G.TwoEdgeConnected) (h4 : 4 ≤ V(G).ncard)
    (hF1 : ∀ v, (G.closedHubNbhd v).ncard ≤ 3)
    (hF2 : ∀ e₁ e₂ e₃ x y z, x ≠ y → y ≠ z → x ≠ z → G.IsLink e₁ x y → G.IsLink e₂ y z →
      G.IsLink e₃ z x → G.PencilHub y → G.PencilHub z → False)
    (hrig : ∃ Y ⊆ V(G), 2 ≤ Y.ncard ∧ (G.induce Y).deficiency 2 = 0) :
    (∃ x₁ x₂ c, G.degree x₁ = 2 ∧ G.degree x₂ = 2 ∧ G.Adj x₁ x₂ ∧ G.Adj x₁ c ∧ G.Adj x₂ c ∧
      4 ≤ G.degree c) ∨
    ∃ W₀ x a b, G.IsPencilGoodEar W₀ x a b := by
  have hGs := hG.simple
  rcases hG.exists_minimalRigid_ear_or_pendantTriangle htec h4 hF1 hF2 hrig with
    ⟨W₀, y, a, b, e₁, e₂, hW₀V, hW₀v, hS, ht2, hy, hy2, haX, hbX, h₁, h₂, hab, ha, hb, hX3, hX1⟩ |
    ⟨y, u, w, hy2, hu2, hyu, hyw, huw, hc⟩
  swap
  · exact Or.inl ⟨y, u, w, hy2, hu2, hyu, hyw, huw, hc⟩
  right
  refine ⟨W₀, y, a, b, ?_⟩
  have hyV := hW₀V hy
  have hyX : y ∉ W₀ \ {y} := fun h => h.2 rfl
  have hya : y ≠ a := fun h => haX.2 h.symm
  have hyb : y ≠ b := fun h => hbX.2 h.symm
  have hne : e₁ ≠ e₂ := by
    rintro rfl
    exact hab (h₁.right_unique h₂)
  have hyE := Graph.isLink_eq_of_degree_eq_two hy2 hne h₁ h₂
  -- the neighbours of `y` are `a` and `b`
  have hyN : ∀ z, G.Adj y z → z = a ∨ z = b := by
    rintro z ⟨e, he⟩
    rcases hyE e z he with rfl | rfl
    · exact Or.inl (h₁.right_unique he).symm
    · exact Or.inr (h₂.right_unique he).symm
  have hnadj : ¬ G.Adj a b := by
    rintro ⟨g, hg⟩
    exact hF2 e₁ g e₂ y a b hya hab hyb h₁ hg h₂.symm ha hb
  have hSX : ∀ Z ⊆ W₀ \ {y}, 2 ≤ Z.ncard → 1 ≤ (G.induce Z).partitionDef 2 id :=
    fun Z hZ hZ2 => hS Z (hZ.trans Set.sdiff_subset)
      (fun h => hyX (hZ (by rw [h]; exact hy))) hZ2
  have hXV : W₀ \ {y} ⊆ V(G) \ {y} := fun v hv => ⟨hW₀V hv.1, hv.2⟩
  have hXd := Graph.deficiency_three_induce_eq_zero_of_tight hSX hX3 hX1
  have hX2 : 2 ≤ (W₀ \ {y}).ncard := by omega
  have hW3 : 3 ≤ W₀.ncard := by
    have := Set.ncard_sdiff_singleton_add_one hy (Set.toFinite W₀)
    omega
  have hpd1 : (G.induce (W₀ \ {y})).partitionDef 2 id = 1 := by
    have := hSX (W₀ \ {y}) subset_rfl hX2
    omega
  have hdef2 : (G.induce (W₀ \ {y})).deficiency 2 = 1 :=
    le_antisymm (Graph.deficiency_two_induce_le_one_of_tight hSX hX1)
      (hpd1 ▸ Graph.partitionDef_le_deficiency _ 2 id)
  -- (i): two neighbours in `W₀`
  have hnbrs : ∀ v ∈ W₀, 2 ≤ ({w | w ∈ W₀ ∧ G.Adj v w} : Set α).ncard := by
    intro v hv
    have h := (ht2 v hv).trans (Graph.ncard_setOf_isLink_le_ncard_adj (G := G) v (W₀ \ {v}))
    exact h.trans (Set.ncard_le_ncard (fun w hw => ⟨hw.1.1, hw.2⟩) (Set.toFinite _))
  -- an end keeps two neighbours in `X`, or `W₀` is a triangle on `x`, `a` and `b`
  have hkey : ∀ p q : α, p ∈ W₀ \ {y} → (∀ z, G.Adj y z → z = p ∨ z = q) → ¬ G.Adj p q →
      2 ≤ ({w | w ∈ W₀ \ {y} ∧ G.Adj p w} : Set α).ncard := by
    intro p q hp hpq hpq'
    by_contra hlt
    push Not at hlt
    have hyp : y ≠ p := fun h => hp.2 h.symm
    have hty := Graph.ncard_setOf_isLink_le_one hGs (x := y) (W := W₀ \ {y, p})
      (fun c₁ hc₁ c₂ hc₂ h₁ h₂ => by
        have hc₁' : c₁ = q := (hpq c₁ h₁).resolve_left (fun h => hc₁.2 (Or.inr h))
        have hc₂' : c₂ = q := (hpq c₂ h₂).resolve_left (fun h => hc₂.2 (Or.inr h))
        rw [hc₁', hc₂'])
    have htp := Graph.ncard_setOf_isLink_le_one hGs (x := p) (W := W₀ \ {y, p})
      (fun c₁ hc₁ c₂ hc₂ h₁ h₂ => by
        have hsub : ({w | w ∈ W₀ \ {y} ∧ G.Adj p w} : Set α).Subsingleton :=
          Set.ncard_le_one_iff_subsingleton.mp (by omega)
        exact hsub ⟨⟨hc₁.1, fun h => hc₁.2 (Or.inl h)⟩, h₁⟩
          ⟨⟨hc₂.1, fun h => hc₂.2 (Or.inl h)⟩, h₂⟩)
    obtain ⟨w, -, -, hwp, hyw, hpw, -⟩ :=
      Graph.exists_eq_triple_of_minimal hGs hS hW₀v hW3 hy hp.1 hyp hty htp
    exact hpq' (((hpq w hyw).resolve_left hwp) ▸ hpw)
  have hXnbrs : ∀ v ∈ W₀ \ {y}, 2 ≤ ({w | w ∈ W₀ \ {y} ∧ G.Adj v w} : Set α).ncard := by
    intro v hv
    by_cases hva : v = a
    · subst hva
      exact hkey v b haX hyN hnadj
    by_cases hvb : v = b
    · subst hvb
      exact hkey v a hbX (fun z hz => (hyN z hz).symm) (fun h => hnadj h.symm)
    refine (hnbrs v hv.1).trans (Set.ncard_le_ncard (fun w hw => ⟨⟨hw.1, ?_⟩, hw.2⟩)
      (Set.toFinite _))
    rintro rfl
    obtain ⟨e, he⟩ := hw.2
    rcases hyN v ⟨e, he.symm⟩ with h | h
    exacts [hva h, hvb h]
  -- (iv), the lower bound: a partition of `V(G)` is at most its restriction
  have hge : ∀ n, 3 ≤ n → G.deficiency n ≤ (G.induce (V(G) \ {y})).deficiency n := by
    intro n hn
    have hD : (3 : ℤ) ≤ Graph.bodyBarDim n := by exact_mod_cast three_le_bodyBarDim hn
    have : Nonempty (α → α) := ⟨id⟩
    refine ciSup_le fun f => ?_
    have hyX' : y ∉ V(G) \ {y} := fun h => h.2 rfl
    have hins := Graph.partitionDef_induce_insert (G := G) (n := n) hyX' f
    rw [Set.insert_sdiff_singleton, Set.insert_eq_of_mem hyV, Graph.induce_vertexSet] at hins
    rw [hins]
    refine le_trans ?_ (Graph.partitionDef_le_deficiency _ n f)
    split_ifs with h
    · have : (0 : ℤ) ≤ ((Graph.bodyBarDim n : ℤ) - 1) *
          ({e | ∃ z ∈ V(G) \ {y}, G.IsLink e y z ∧ f z ≠ f y} : Set β).ncard :=
        mul_nonneg (by linarith) (by positivity)
      linarith
    · have hsub : ({e₁, e₂} : Set β) ⊆ {e | ∃ z ∈ V(G) \ {y}, G.IsLink e y z ∧ f z ≠ f y} := by
        rintro e (rfl | rfl)
        · exact ⟨a, hXV haX, h₁, fun h' => h ⟨a, hXV haX, h'⟩⟩
        · exact ⟨b, hXV hbX, h₂, fun h' => h ⟨b, hXV hbX, h'⟩⟩
      have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_pair hne] at h2
      have h2' : (2 : ℤ) ≤ ({e | ∃ z ∈ V(G) \ {y}, G.IsLink e y z ∧ f z ≠ f y} : Set β).ncard :=
        by exact_mod_cast h2
      nlinarith
  -- (v)
  have hhub : ∀ w ∈ W₀, ∀ u ∈ V(G) \ W₀, G.Adj w u → G.PencilHub w := by
    intro w hw u hu hwu
    refine ⟨hW₀V hw, ?_⟩
    have huT : u ∉ ({z | z ∈ W₀ ∧ G.Adj w z} : Set α) := fun h => hu.2 h.1
    have hsub : insert u ({z | z ∈ W₀ ∧ G.Adj w z} : Set α) ⊆ N(G, w) := by
      rintro z (rfl | ⟨-, hz⟩)
      exacts [hwu, hz]
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_insert_of_notMem huT (Set.toFinite _), ← Graph.degree_eq_ncard_adj] at this
    have := hnbrs w hw
    omega
  refine
    { subset := hW₀V
      partitionDef_le := hW₀v
      one_le_partitionDef := hS
      two_le_nbrs := hnbrs
      mem := hy
      degree_eq := hy2
      adj_a := ⟨e₁, h₁⟩
      adj_b := ⟨e₂, h₂⟩
      ne := hab
      a_mem := haX.1
      b_mem := hbX.1
      hub_a := ha
      hub_b := hb
      not_adj := hnadj
      three_le := hX3
      connected := ?_
      two_le_degree := ?_
      partitionDef_eq := hpd1
      deficiency_eq := hdef2
      deficiency_ne := ?_
      deficiency_delete := ?_
      outside := ?_
      hub_of_outside := ?_ }
  · refine Graph.connected_iff.mpr ⟨⟨a, haX⟩, Graph.preconnected_of_deficiency_two_lt ?_⟩
    rw [hdef2]; norm_num
  · intro v hv
    have : (G.induce (W₀ \ {y})).Simple := inferInstance
    rw [Graph.degree_eq_ncard_adj]
    refine (hXnbrs v hv).trans (Set.ncard_le_ncard (fun w hw => ?_) (Set.toFinite _))
    obtain ⟨e, he⟩ := hw.2
    exact ⟨e, (Graph.induce_isLink G _ e v w).mpr ⟨he, hv, hw.1⟩⟩
  · intro Z hZ hZ2 hd
    have hs : (G.induce Z).partitionDef 2 id ≤ 0 := hd ▸ Graph.partitionDef_le_deficiency _ 2 id
    have hZne : Z ≠ W₀ := fun h => hyX (hZ (by rw [h]; exact hy))
    have := hS Z (hZ.trans Set.sdiff_subset) hZne hZ2
    omega
  · intro n hn
    have hD1 : 1 ≤ Graph.bodyBarDim n := by have := three_le_bodyBarDim hn; omega
    have hXn := Graph.deficiency_eq_zero_of_deficiency_eq_zero_of_le (n := 3) (m := n)
      (G := G.induce (W₀ \ {y})) (by decide) hn ⟨a, haX⟩ hXd
    have hear := hG.isOpenEar_one hy2 h₁.symm h₂ hab
    have hδ := Graph.deficiencyMerged_eq_deficiency_of_mem (G := G.induce (V(G) \ {y}))
      (n := n) hD1 hXV (by rw [Graph.induce_induce_of_subset G hXV]; exact hXn) haX hbX
    exact le_antisymm (hear.deficiency_induce_le hδ) (hge n hn)
  · intro u hu
    refine ⟨?_, fun w hw hwu => hhub w hw u hu hwu.symm⟩
    by_contra hlt
    push Not at hlt
    obtain ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr⟩ :=
      (Set.two_lt_ncard_iff (Set.toFinite _)).mp hlt
    have hpub := hhub p hp.1 u hu hp.2.symm
    have hqub := hhub q hq.1 u hu hq.2.symm
    have hrub := hhub r hr.1 u hu hr.2.symm
    have hsub3 : ({p, q, r} : Set α) ⊆ N(G, u) := by
      rintro z (rfl | rfl | rfl)
      exacts [hp.2, hq.2, hr.2]
    have h3 : ({p, q, r} : Set α).ncard = 3 := Set.ncard_eq_three.mpr ⟨p, q, r, hpq, hpr, hqr, rfl⟩
    have hdeg := Set.ncard_le_ncard hsub3 (Set.toFinite _)
    rw [← Graph.degree_eq_ncard_adj, h3] at hdeg
    have huh : G.PencilHub u := ⟨hu.1, hdeg⟩
    have hsub : ({u, p, q, r} : Set α) ⊆ G.closedHubNbhd u := by
      rintro z (rfl | rfl | rfl | rfl)
      · exact ⟨huh, Or.inl rfl⟩
      · exact ⟨hpub, Or.inr hp.2⟩
      · exact ⟨hqub, Or.inr hq.2⟩
      · exact ⟨hrub, Or.inr hr.2⟩
    have huS : u ∉ ({p, q, r} : Set α) := by
      rintro (rfl | rfl | rfl)
      exacts [hu.2 hp.1, hu.2 hq.1, hu.2 hr.1]
    have h4' : ({u, p, q, r} : Set α).ncard = 4 := by
      rw [Set.ncard_insert_of_notMem huS, h3]
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    have := hF1 u
    omega
  · rintro w hw ⟨u, hu, hwu⟩
    exact hhub w hw u hu hwu

end CombinatorialRigidity.Molecular
