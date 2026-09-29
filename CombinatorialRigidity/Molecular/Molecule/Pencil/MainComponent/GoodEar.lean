/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.CoverageTheoremS

/-!
# A minimal planar-rigid set has a good ear (Phase 40p REDUCE+CLOSE)

(MC-129) at a two-edge-connected graph (`blueprint/src/chapter/main-component.tex`,
`sec:main-component-statements`): a minimal planar-rigid set of a graph satisfying the standing
hypotheses gives a one-body open ear at hub ends across which the deficiency does not drop, or a
pendant triangle at a body of degree at least four.

## Main statements

* `Graph.exists_eq_triple_of_minimal` — (MC-129) step 3, by the singleton count: a set of
  singleton value at most `0` whose proper subsets of two or more bodies have singleton value at
  least `1`, with two adjacent bodies each with at most one neighbour among the rest, is a
  triangle.
* `Graph.exists_closedEar_two_of_triangle` — a pendant triangle of a two-edge-connected graph on
  at least four bodies: two adjacent bodies of degree two with a common neighbour form a closed
  two-ear, and the common neighbour has degree at least four.
* `Graph.IsX0Graph.exists_oneEar_or_pendantTriangle` — (MC-129) itself, `lem:pencil-rigid-good-ear`.

See `notes/Phase40p.md` and `ROADMAP.md` §40 for the phase.
-/

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {α β : Type*}

/-- **The triangle step** ((MC-129) step 3, by the singleton count): in a set `W₀` of singleton
value at most `0` whose proper subsets of two or more bodies have singleton value at least `1`,
two adjacent bodies each with at most one neighbour among the rest span, with a third body, all of
`W₀`, and the three are pairwise adjacent. -/
theorem _root_.Graph.exists_eq_triple_of_minimal [Finite α] [Finite β] {G : Graph α β}
    (hG : G.Simple) {W₀ : Set α}
    (hS : ∀ Z ⊆ W₀, Z ≠ W₀ → 2 ≤ Z.ncard → 1 ≤ (G.induce Z).partitionDef 2 id)
    (hW₀v : (G.induce W₀).partitionDef 2 id ≤ 0) (hW₀3 : 3 ≤ W₀.ncard)
    {y u : α} (hy : y ∈ W₀) (hu : u ∈ W₀) (hyu : y ≠ u)
    (hty : ({e | ∃ z ∈ W₀ \ {y, u}, G.IsLink e y z} : Set β).ncard ≤ 1)
    (htu : ({e | ∃ z ∈ W₀ \ {y, u}, G.IsLink e u z} : Set β).ncard ≤ 1) :
    ∃ w, W₀ = {y, u, w} ∧ w ≠ y ∧ w ≠ u ∧ G.Adj y w ∧ G.Adj u w ∧ G.Adj u y := by
  classical
  have hone : ∀ u q : α, ({e | ∃ y ∈ ({q} : Set α), G.IsLink e u y} : Set β).ncard ≤ 1 :=
    fun u q => Graph.ncard_setOf_isLink_le_one hG (x := u) (W := {q})
      (by rintro c₁ rfl c₂ rfl - -; rfl)
  have hpos : ∀ u (Y : Set α), 1 ≤ ({e | ∃ y ∈ Y, G.IsLink e u y} : Set β).ncard →
      ∃ y ∈ Y, G.Adj u y := by
    intro u Y h
    obtain ⟨e, y, hy, hl⟩ := Set.nonempty_of_ncard_ne_zero (s := {e | ∃ y ∈ Y, G.IsLink e u y})
      (by omega)
    exact ⟨y, hy, e, hl⟩
  set Z := W₀ \ {y, u} with hZ
  have hyZ : y ∉ Z := fun h => h.2 (Or.inl rfl)
  have huZ : u ∉ Z := fun h => h.2 (Or.inr rfl)
  have huyZ : u ∉ insert y Z := by
    rintro (h | h)
    · exact hyu h.symm
    · exact huZ h
  have hW : W₀ = insert u (insert y Z) := by
    ext v
    constructor
    · intro hv
      by_cases hvu : v = u
      · exact Or.inl hvu
      by_cases hvy : v = y
      · exact Or.inr (Or.inl hvy)
      exact Or.inr (Or.inr ⟨hv, fun h => h.elim hvy hvu⟩)
    · rintro (rfl | rfl | ⟨hv, -⟩)
      exacts [hu, hy, hv]
  have hcardZ : W₀.ncard = Z.ncard + 2 := by
    rw [hW, Set.ncard_insert_of_notMem huyZ, Set.ncard_insert_of_notMem hyZ]
  have e1 := Graph.partitionDef_two_induce_insert_id (G := G) hyZ
  have e2 := Graph.partitionDef_two_induce_insert_id (G := G) huyZ
  rw [← hW] at e2
  have hsplit : ({e | ∃ z ∈ insert y Z, G.IsLink e u z} : Set β) ⊆
      {e | ∃ z ∈ ({y} : Set α), G.IsLink e u z} ∪ {e | ∃ z ∈ Z, G.IsLink e u z} := by
    rintro e ⟨z, (rfl | hz), hl⟩
    · exact Or.inl ⟨z, rfl, hl⟩
    · exact Or.inr ⟨z, hz, hl⟩
  have htu' := (Set.ncard_le_ncard hsplit (Set.toFinite _)).trans (Set.ncard_union_le _ _)
  have hsing := hone u y
  rcases Nat.lt_or_ge Z.ncard 2 with hZ2 | hZ2
  · obtain ⟨w, hw⟩ : ∃ w, Z = {w} := Set.ncard_eq_one.mp (by omega)
    have hwZ : w ∈ Z := by rw [hw]; rfl
    rw [hw, Graph.partitionDef_induce_singleton_id] at e1
    rw [hw] at hty htu htu' e2
    have hyw : 1 ≤ ({e | ∃ z ∈ ({w} : Set α), G.IsLink e y z} : Set β).ncard := by omega
    have huw : 1 ≤ ({e | ∃ z ∈ ({w} : Set α), G.IsLink e u z} : Set β).ncard := by omega
    have huy : 1 ≤ ({e | ∃ z ∈ ({y} : Set α), G.IsLink e u z} : Set β).ncard := by omega
    obtain ⟨z₁, hz₁, hyw'⟩ := hpos y {w} hyw
    obtain ⟨z₂, hz₂, huw'⟩ := hpos u {w} huw
    obtain ⟨z₃, hz₃, huy'⟩ := hpos u {y} huy
    rw [Set.mem_singleton_iff] at hz₁ hz₂ hz₃
    rw [hz₁] at hyw'
    rw [hz₂] at huw'
    rw [hz₃] at huy'
    refine ⟨w, ?_, fun h => hyZ (h ▸ hwZ), fun h => huZ (h ▸ hwZ), hyw', huw', huy'⟩
    rw [hW, hw, Set.insert_comm]
  · have := hS Z Set.sdiff_subset (fun h => hyZ (by rw [h]; exact hy)) hZ2
    omega

/-- **A pendant triangle of a two-edge-connected graph on at least four bodies**: two adjacent
bodies `y`, `u` of degree two with a common neighbour `w` form a closed two-ear at `w`, and `w`
has degree at least four (the triangle is crossed by at least two edges, all at `w`). -/
theorem _root_.Graph.exists_closedEar_two_of_triangle [Finite β]
    {G : Graph α β} (hS : G.Simple) (htec : G.TwoEdgeConnected) (h4 : 4 ≤ V(G).ncard)
    {y u w : α} (hy2 : G.degree y = 2) (hu2 : G.degree u = 2) (hyu : y ≠ u) (hwy : w ≠ y)
    (hwu : w ≠ u) (hyw : G.Adj y w) (huw : G.Adj u w) (huy : G.Adj u y) :
    ∃ (V₁ : Set α) (x : Fin 2 → α) (c : α) (e : Fin 3 → β),
      V(G) = V₁ ∪ Set.range x ∧ Function.Injective x ∧ (∀ i, x i ∉ V₁) ∧ c ∈ V₁ ∧
      (∀ i : Fin 3, G.IsLink (e i) (pathVertex c x c i.castSucc) (pathVertex c x c i.succ)) ∧
      (∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁) ∧ 4 ≤ G.degree c := by
  classical
  have := hS
  obtain ⟨g₁, hg₁⟩ := hyw
  obtain ⟨g₂, hg₂⟩ := huw
  obtain ⟨g₃, hg₃⟩ := huy
  have hg13 : g₁ ≠ g₃ := by
    rintro rfl
    exact hwu (hg₁.right_unique hg₃.symm)
  have hg23 : g₂ ≠ g₃ := by
    rintro rfl
    exact hwy (hg₂.right_unique hg₃)
  have hg12 : g₁ ≠ g₂ := by
    rintro rfl
    exact hyu (hg₁.symm.right_unique hg₂.symm)
  have hyE := Graph.isLink_eq_of_degree_eq_two hy2 hg13 hg₁ hg₃.symm
  have huE := Graph.isLink_eq_of_degree_eq_two hu2 hg23 hg₂ hg₃
  have hyV : y ∈ V(G) := hg₁.left_mem
  have huV : u ∈ V(G) := hg₂.left_mem
  have hwV : w ∈ V(G) := hg₁.right_mem
  refine ⟨V(G) \ {y, u}, ![y, u], w, ![g₁, g₃, g₂], ?_, ?_, ?_,
    ⟨hwV, fun h => h.elim hwy hwu⟩, ?_, ?_, ?_⟩
  · ext v
    simp only [Set.mem_union, Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor
    · intro hv
      by_cases hvy : v = y
      · exact Or.inr (Or.inl hvy.symm)
      by_cases hvu : v = u
      · exact Or.inr (Or.inr hvu.symm)
      exact Or.inl ⟨hv, fun h => h.elim hvy hvu⟩
    · rintro (⟨hv, -⟩ | rfl | rfl)
      exacts [hv, hyV, huV]
  · intro i j hij
    fin_cases i <;> fin_cases j
    exacts [rfl, (hyu hij).elim, (hyu hij.symm).elim, rfl]
  · intro i
    fin_cases i
    · exact fun h => h.2 (Or.inl rfl)
    · exact fun h => h.2 (Or.inr rfl)
  · intro i
    fin_cases i
    exacts [hg₁.symm, hg₃.symm, hg₂]
  · intro f' p q hl hne
    have h0 : f' ≠ g₁ := hne 0
    have h1 : f' ≠ g₃ := hne 1
    have h2 : f' ≠ g₂ := hne 2
    have hnot : ∀ p q, G.IsLink f' p q → p ∉ ({y, u} : Set α) := by
      intro p q hl
      rintro (rfl | rfl)
      · rcases hyE f' q hl with h | h
        · exact h0 h
        · exact h1 h
      · rcases huE f' q hl with h | h
        · exact h2 h
        · exact h1 h
    exact ⟨⟨hl.left_mem, hnot p q hl⟩, ⟨hl.right_mem, hnot q p hl.symm⟩⟩
  · -- two-edge-connectivity at the triangle
    set T : Set α := {y, u, w} with hT
    have hT3 : T.ncard = 3 := Set.ncard_eq_three.mpr ⟨y, u, w, hyu, hwy.symm, hwu.symm, rfl⟩
    have hTV : T ⊆ V(G) := by
      rintro v (rfl | rfl | rfl)
      exacts [hyV, huV, hwV]
    have hss : T ⊂ V(G) := hTV.ssubset_of_ne fun h => by rw [h] at hT3; omega
    have hcut := htec T ⟨y, Or.inl rfl⟩ hss
    have hsub1 : G.cutEdges T ⊆ {e | ∃ z ∈ V(G) \ T, G.IsLink e w z} := by
      rintro e ⟨-, p, q, hl, hp, hq⟩
      rcases hp with rfl | rfl | rfl
      · exfalso
        rcases hyE e q hl with rfl | rfl
        · exact hq (Or.inr (Or.inr (hg₁.right_unique hl).symm))
        · exact hq (Or.inr (Or.inl (hg₃.symm.right_unique hl).symm))
      · exfalso
        rcases huE e q hl with rfl | rfl
        · exact hq (Or.inr (Or.inr (hg₂.right_unique hl).symm))
        · exact hq (Or.inl (hg₃.right_unique hl).symm)
      · exact ⟨q, ⟨hl.right_mem, hq⟩, hl⟩
    have hsub2 : ({g₁, g₂} : Set β) ∪ {e | ∃ z ∈ V(G) \ T, G.IsLink e w z} ⊆
        {e | ∃ z ∈ V(G) \ {w}, G.IsLink e w z} := by
      rintro e ((rfl | rfl) | ⟨z, hz, hl⟩)
      · exact ⟨y, ⟨hyV, hwy.symm⟩, hg₁.symm⟩
      · exact ⟨u, ⟨huV, hwu.symm⟩, hg₂.symm⟩
      · exact ⟨z, ⟨hz.1, fun h => hz.2 (Or.inr (Or.inr h))⟩, hl⟩
    have hdisj : Disjoint ({g₁, g₂} : Set β) {e | ∃ z ∈ V(G) \ T, G.IsLink e w z} := by
      rw [Set.disjoint_left]
      rintro e (rfl | rfl) ⟨z, hz, hl⟩
      · exact hz.2 ((hg₁.symm.right_unique hl) ▸ Or.inl rfl)
      · exact hz.2 ((hg₂.symm.right_unique hl) ▸ Or.inr (Or.inl rfl))
    have h1 := Set.ncard_le_ncard hsub2 (Set.toFinite _)
    rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), Set.ncard_pair hg12] at h1
    have h2 := Graph.ncard_setOf_isLink_le_degree (G := G) (x := w) (Y := V(G) \ {w})
      (fun h => h.2 rfl)
    have h3 := Set.ncard_le_ncard hsub1 (Set.toFinite _)
    omega

/-- **(MC-129) at a two-edge-connected graph**: a planar-rigid set and at least four bodies give a
one-body open ear at hub ends with `def₃(G[V₁]) ≤ def₃(G)`, or a pendant triangle at a body of
degree at least four. -/
theorem _root_.Graph.IsX0Graph.exists_oneEar_or_pendantTriangle [Finite α] [Finite β]
    {G : Graph α β} (hG : G.IsX0Graph) (htec : G.TwoEdgeConnected) (h4 : 4 ≤ V(G).ncard)
    (hF1 : ∀ v, (G.closedHubNbhd v).ncard ≤ 3)
    (hF2 : ∀ e₁ e₂ e₃ x y z, x ≠ y → y ≠ z → x ≠ z → G.IsLink e₁ x y → G.IsLink e₂ y z →
      G.IsLink e₃ z x → G.PencilHub y → G.PencilHub z → False)
    (hrig : ∃ Y ⊆ V(G), 2 ≤ Y.ncard ∧ (G.induce Y).deficiency 2 = 0) :
    (∃ (V₁ : Set α) (x : Fin 1 → α) (a b : α) (e : Fin 2 → β), G.IsOpenEar V₁ x a b e ∧
      G.PencilHub a ∧ G.PencilHub b ∧ (G.induce V₁).deficiency 3 ≤ G.deficiency 3) ∨
    (∃ (V₁ : Set α) (x : Fin 2 → α) (c : α) (e : Fin 3 → β),
      V(G) = V₁ ∪ Set.range x ∧ Function.Injective x ∧ (∀ i, x i ∉ V₁) ∧ c ∈ V₁ ∧
      (∀ i : Fin 3, G.IsLink (e i) (pathVertex c x c i.castSucc) (pathVertex c x c i.succ)) ∧
      (∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁) ∧ 4 ≤ G.degree c) := by
  classical
  have := hG.simple
  -- `W₀`, a minimal planar-rigid set
  obtain ⟨W₀, ⟨hW₀V, hW₀2, hW₀d⟩, hmin⟩ := Set.exists_min_image
    {Y : Set α | Y ⊆ V(G) ∧ 2 ≤ Y.ncard ∧ (G.induce Y).deficiency 2 = 0} Set.ncard
    (Set.toFinite _) (by obtain ⟨Y, hY, h2, hd⟩ := hrig; exact ⟨Y, hY, h2, hd⟩)
  -- (S) on the proper subsets of `W₀`
  have hS : ∀ Z ⊆ W₀, Z ≠ W₀ → 2 ≤ Z.ncard → 1 ≤ (G.induce Z).partitionDef 2 id := by
    intro Z hZ hne hZ2
    by_contra hlt
    push Not at hlt
    obtain ⟨Y, hYZ, hY2, hYd⟩ :=
      Graph.exists_deficiency_induce_eq_zero_of_partitionDef_id_nonpos (G := G) (n := 2)
        (hZ.trans hW₀V) hZ2 (by omega)
    have h1 := hmin Y ⟨hYZ.trans (hZ.trans hW₀V), hY2, hYd⟩
    have h2 : Z.ncard < W₀.ncard := Set.ncard_lt_ncard (hZ.ssubset_of_ne hne)
    have h3 := Set.ncard_le_ncard hYZ (Set.toFinite _)
    omega
  have hW₀v : (G.induce W₀).partitionDef 2 id ≤ 0 :=
    hW₀d ▸ Graph.partitionDef_le_deficiency _ 2 id
  -- `|W₀| ≥ 3`: a pair of a simple graph is not planar-rigid
  have hW₀3 : 3 ≤ W₀.ncard := by
    by_contra h
    obtain ⟨p, q, hpq, rfl⟩ := (Set.ncard_eq_two (s := W₀)).mp (by omega)
    have hq : p ∉ ({q} : Set α) := by simpa using hpq
    have e1 := Graph.partitionDef_two_induce_insert_id (G := G) hq
    rw [Graph.partitionDef_induce_singleton_id] at e1
    have := Graph.ncard_setOf_isLink_le_one hG.simple (x := p) (W := {q})
      (by rintro c₁ rfl c₂ rfl - -; rfl)
    have : (G.induce {p, q}).partitionDef 2 id ≤ 0 := hW₀v
    omega
  -- every body of `W₀` sends two edges into the rest of `W₀`
  have ht2 : ∀ y ∈ W₀, 2 ≤ ({e | ∃ z ∈ W₀ \ {y}, G.IsLink e y z} : Set β).ncard := by
    intro y hy
    have hyX : y ∉ W₀ \ {y} := fun h => h.2 rfl
    have h := Graph.partitionDef_two_induce_insert_id (G := G) hyX
    rw [Set.insert_sdiff_singleton, Set.insert_eq_of_mem hy] at h
    have hX2 : 2 ≤ (W₀ \ {y}).ncard := by
      have := Set.ncard_sdiff_singleton_add_one hy (Set.toFinite W₀)
      omega
    have := hS (W₀ \ {y}) Set.sdiff_subset (fun h => hyX (by rw [h]; exact hy)) hX2
    omega
  by_cases hnh : ∃ y ∈ W₀, ¬ G.PencilHub y
  · obtain ⟨y, hy, hyh⟩ := hnh
    have hyV := hW₀V hy
    have hy2 : G.degree y = 2 := by
      have := hG.two_le_degree y hyV
      have : ¬ 3 ≤ G.degree y := fun h => hyh ⟨hyV, h⟩
      omega
    -- the two links from `y` into `W₀`
    obtain ⟨e₁, e₂, ⟨a, haX, h₁⟩, ⟨b, hbX, h₂⟩, he⟩ :=
      (Set.one_lt_ncard_iff (s := {e | ∃ z ∈ W₀ \ {y}, G.IsLink e y z})).mp
        (by have := ht2 y hy; omega)
    have hab : a ≠ b := by
      rintro rfl
      exact he (h₁.unique_edge h₂)
    have hya : y ≠ a := fun h => haX.2 h.symm
    have hyb : y ≠ b := fun h => hbX.2 h.symm
    by_cases hab_hub : G.PencilHub a ∧ G.PencilHub b
    · -- **the one-body ear**: `W₀ − y` is tight, hence `def₃`-rigid
      obtain ⟨ha, hb⟩ := hab_hub
      left
      have hyX : y ∉ W₀ \ {y} := fun h => h.2 rfl
      have hins := Graph.partitionDef_two_induce_insert_id (G := G) hyX
      rw [Set.insert_sdiff_singleton, Set.insert_eq_of_mem hy] at hins
      have htdeg := Graph.ncard_setOf_isLink_le_degree (G := G) (x := y) (Y := W₀ \ {y}) hyX
      have hX1 : (G.induce (W₀ \ {y})).partitionDef 2 id ≤ 1 := by omega
      have hXcard := Set.ncard_sdiff_singleton_add_one hy (Set.toFinite W₀)
      have hSX : ∀ Z ⊆ W₀ \ {y}, 2 ≤ Z.ncard → 1 ≤ (G.induce Z).partitionDef 2 id :=
        fun Z hZ hZ2 => hS Z (hZ.trans Set.sdiff_subset)
          (fun h => hyX (hZ (by rw [h]; exact hy))) hZ2
      rcases Nat.lt_or_ge (W₀ \ {y}).ncard 3 with hX3 | hX3
      · exfalso
        have hXab : W₀ \ {y} = {a, b} := (Set.eq_of_subset_of_ncard_le (Set.pair_subset haX hbX)
          (by rw [Set.ncard_pair hab]; omega) (Set.toFinite _)).symm
        have hbna : a ∉ ({b} : Set α) := hab
        have e1 := Graph.partitionDef_two_induce_insert_id (G := G) hbna
        rw [Graph.partitionDef_induce_singleton_id, ← hXab] at e1
        obtain ⟨g, z, hz, hg⟩ := Set.nonempty_of_ncard_ne_zero
          (s := {e | ∃ z ∈ ({b} : Set α), G.IsLink e a z}) (by omega)
        rw [Set.mem_singleton_iff] at hz
        rw [hz] at hg
        exact hF2 e₁ g e₂ y a b hya hab hyb h₁ hg h₂.symm ha hb
      · have hXd := Graph.deficiency_three_induce_eq_zero_of_tight hSX hX3 hX1
        have hear := hG.isOpenEar_one hy2 h₁.symm h₂ hab
        have hXV : W₀ \ {y} ⊆ V(G) \ {y} := fun v hv => ⟨hW₀V hv.1, hv.2⟩
        have hδ := Graph.deficiencyMerged_eq_deficiency_of_mem (G := G.induce (V(G) \ {y}))
          (n := 3) (by decide) hXV
          (by rw [Graph.induce_induce_of_subset G hXV]; exact hXd) haX hbX
        exact ⟨_, _, a, b, _, hear, ha, hb, hear.deficiency_induce_le hδ⟩
    · -- **the pendant triangle**, at a neighbour `u` of `y` that is not a hub
      right
      obtain ⟨u, hu, f, hf, huh⟩ : ∃ u ∈ W₀ \ {y}, ∃ f, G.IsLink f y u ∧ ¬ G.PencilHub u := by
        rcases not_and_or.mp hab_hub with ha | hb
        · exact ⟨a, haX, e₁, h₁, ha⟩
        · exact ⟨b, hbX, e₂, h₂, hb⟩
      have huV := hW₀V hu.1
      have hu2 : G.degree u = 2 := by
        have := hG.two_le_degree u huV
        have : ¬ 3 ≤ G.degree u := fun h => huh ⟨huV, h⟩
        omega
      have hyu : y ≠ u := fun h => hu.2 h.symm
      -- a body of degree two has at most one neighbour besides a given one
      have hnbr2 : ∀ v, G.degree v = 2 → ∀ u c₁ c₂, G.Adj v u → G.Adj v c₁ → G.Adj v c₂ →
          u ≠ c₁ → u ≠ c₂ → c₁ = c₂ := by
        intro v hv u c₁ c₂ hu h₁ h₂ hu₁ hu₂
        by_contra h12
        have hsub : ({u, c₁, c₂} : Set α) ⊆ N(G, v) := by
          rintro z (rfl | rfl | rfl)
          exacts [hu, h₁, h₂]
        have h3 : ({u, c₁, c₂} : Set α).ncard = 3 :=
          Set.ncard_eq_three.mpr ⟨u, c₁, c₂, hu₁, hu₂, h12, rfl⟩
        have := Set.ncard_le_ncard hsub (Set.toFinite _)
        rw [← Graph.degree_eq_ncard_adj, hv, h3] at this
        omega
      have hty := Graph.ncard_setOf_isLink_le_one hG.simple (x := y) (W := W₀ \ {y, u})
        (fun c₁ hc₁ c₂ hc₂ h₁ h₂ => hnbr2 y hy2 u c₁ c₂ ⟨f, hf⟩ h₁ h₂
          (fun h => hc₁.2 (Or.inr h.symm)) (fun h => hc₂.2 (Or.inr h.symm)))
      have htu := Graph.ncard_setOf_isLink_le_one hG.simple (x := u) (W := W₀ \ {y, u})
        (fun c₁ hc₁ c₂ hc₂ h₁ h₂ => hnbr2 u hu2 y c₁ c₂ ⟨f, hf.symm⟩ h₁ h₂
          (fun h => hc₁.2 (Or.inl h.symm)) (fun h => hc₂.2 (Or.inl h.symm)))
      obtain ⟨w, -, hwy, hwu, hyw, huw, huy⟩ :=
        Graph.exists_eq_triple_of_minimal hG.simple hS hW₀v hW₀3 hy hu.1 hyu hty htu
      exact Graph.exists_closedEar_two_of_triangle hG.simple htec h4 hy2 hu2 hyu hwy hwu hyw huw
        huy
  · -- every body of `W₀` a hub: a triangle of hubs, excluded by (F2)
    push Not at hnh
    exfalso
    -- (F1): a hub has at most one hub neighbour besides a given one
    have hnbrH : ∀ v, G.PencilHub v → ∀ u c₁ c₂, G.Adj v u → G.Adj v c₁ → G.Adj v c₂ →
        G.PencilHub u → G.PencilHub c₁ → G.PencilHub c₂ →
        v ≠ u → v ≠ c₁ → v ≠ c₂ → u ≠ c₁ → u ≠ c₂ → c₁ = c₂ := by
      intro v hv u c₁ c₂ ⟨f, hf⟩ ⟨f₁, hf₁⟩ ⟨f₂, hf₂⟩ hu h₁ h₂ hvu hv₁ hv₂ hu₁ hu₂
      by_contra h12
      have hsub : ({v, u, c₁, c₂} : Set α) ⊆ G.closedHubNbhd v := by
        rintro z (rfl | rfl | rfl | rfl)
        · exact ⟨hv, Or.inl rfl⟩
        · exact ⟨hu, Or.inr ⟨f, hf⟩⟩
        · exact ⟨h₁, Or.inr ⟨f₁, hf₁⟩⟩
        · exact ⟨h₂, Or.inr ⟨f₂, hf₂⟩⟩
      have hvS : v ∉ ({u, c₁, c₂} : Set α) := by
        rintro (h | h | h)
        · exact hvu h
        · exact hv₁ h
        · exact hv₂ h
      have h4' : ({v, u, c₁, c₂} : Set α).ncard = 4 := by
        rw [Set.ncard_insert_of_notMem hvS,
          Set.ncard_eq_three.mpr ⟨u, c₁, c₂, hu₁, hu₂, h12, rfl⟩]
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      have := hF1 v
      omega
    obtain ⟨y, hy⟩ : W₀.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
    obtain ⟨f, u, hu, hf⟩ := Set.nonempty_of_ncard_ne_zero
      (s := {e | ∃ z ∈ W₀ \ {y}, G.IsLink e y z}) (by have := ht2 y hy; omega)
    have hyu : y ≠ u := fun h => hu.2 h.symm
    have hty := Graph.ncard_setOf_isLink_le_one hG.simple (x := y) (W := W₀ \ {y, u})
      (fun c₁ hc₁ c₂ hc₂ h₁ h₂ => hnbrH y (hnh y hy) u c₁ c₂ ⟨f, hf⟩ h₁ h₂ (hnh u hu.1)
        (hnh c₁ hc₁.1) (hnh c₂ hc₂.1) hyu (fun h => hc₁.2 (Or.inl h.symm))
        (fun h => hc₂.2 (Or.inl h.symm)) (fun h => hc₁.2 (Or.inr h.symm))
        (fun h => hc₂.2 (Or.inr h.symm)))
    have htu := Graph.ncard_setOf_isLink_le_one hG.simple (x := u) (W := W₀ \ {y, u})
      (fun c₁ hc₁ c₂ hc₂ h₁ h₂ => hnbrH u (hnh u hu.1) y c₁ c₂ ⟨f, hf.symm⟩ h₁ h₂ (hnh y hy)
        (hnh c₁ hc₁.1) (hnh c₂ hc₂.1) (Ne.symm hyu) (fun h => hc₁.2 (Or.inr h.symm))
        (fun h => hc₂.2 (Or.inr h.symm)) (fun h => hc₁.2 (Or.inl h.symm))
        (fun h => hc₂.2 (Or.inl h.symm)))
    obtain ⟨w, hW, hwy, hwu, ⟨g₁, hg₁⟩, ⟨g₂, hg₂⟩, ⟨g₃, hg₃⟩⟩ :=
      Graph.exists_eq_triple_of_minimal hG.simple hS hW₀v hW₀3 hy hu.1 hyu hty htu
    have hwW : w ∈ W₀ := by rw [hW]; exact Or.inr (Or.inr rfl)
    exact hF2 g₃ g₂ g₁ y u w hyu (Ne.symm hwu) (Ne.symm hwy) hg₃.symm hg₂ hg₁.symm (hnh u hu.1)
      (hnh w hwW)

end CombinatorialRigidity.Molecular
