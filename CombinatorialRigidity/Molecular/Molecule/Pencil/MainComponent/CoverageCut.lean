/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.CoverageChain

/-!
# Cut arguments and the standing hypotheses at a chain's smaller graphs (Phase 40m CHAINS B2)

The gate that gives (H) at a cut-off side of a graph, and the two consequences the covering
theorem needs at a chain: (H) at the chain's own smaller graph `G[V₁]`, and (H) after splitting
off at a body's two non-adjacent neighbours (`blueprint/src/chapter/main-component.tex`,
`sec:main-component-coverage`; (MC-79)ff).

## Main statements

* `Graph.Connected.induce_of_gate` — **one gate**: in a connected graph, a set of bodies whose
  only body with a neighbour outside it is `g` induces a connected graph.
* `Graph.IsChain.isX0Graph_induce` — **(H) at a chain's smaller graph**
  (`lem:pencil-x0-chain-standing`(1)): `G[V₁]` satisfies (H), through `G − x₀` and the one gate `b`.
* `Graph.IsX0Graph.splitOff` — **(H) after splitting off at non-adjacent ends**
  (`lem:pencil-x0-chain-standing`(2)).
-/

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {α β : Type*}

/-! ## Cut arguments -/

/-- **One gate**: in a connected graph, a set of bodies whose only body with a neighbour outside
it is `g` induces a connected graph. -/
theorem _root_.Graph.Connected.induce_of_gate {H : Graph α β} (hH : H.Connected) {W : Set α}
    (hW : W ⊆ V(H)) {g : α} (hg : g ∈ W)
    (hgate : ∀ y z, H.Adj y z → y ∈ W → z ∉ W → y = g) : (H.induce W).Connected := by
  refine (Graph.connected_iff_forall_exists_adj ⟨g, hg⟩).mpr fun X hXW hXne => ?_
  have hHc := (Graph.connected_iff_forall_exists_adj hH.nonempty).mp hH
  change X ⊂ W at hXW
  have hadj : ∀ y z, H.Adj y z → y ∈ W → z ∈ W → (H.induce W).Adj y z :=
    fun y z ⟨f, hf⟩ hy hz => ⟨f, by rw [Graph.induce_isLink]; exact ⟨hf, hy, hz⟩⟩
  by_cases hgX : g ∈ X
  · obtain ⟨w, hwW, hwX⟩ := Set.exists_of_ssubset hXW
    obtain ⟨y, hy, z, hz, hyz⟩ := hHc (W \ X)
      ((Set.sdiff_subset.trans hW).ssubset_of_ne fun h => (h ▸ hW hg : g ∈ W \ X).2 hgX)
      ⟨w, hwW, hwX⟩
    have hzW : z ∈ W := by
      by_contra hzW
      exact hy.2 (hgate y z hyz hy.1 hzW ▸ hgX)
    have hzX : z ∈ X := by
      by_contra hzX
      exact hz.2 ⟨hzW, hzX⟩
    exact ⟨z, hzX, y, hy, hadj z y hyz.symm hzW hy.1⟩
  · obtain ⟨y, hy, z, hz, hyz⟩ := hHc X
      ((hXW.subset.trans hW).ssubset_of_ne fun h => hgX (h ▸ hW hg)) hXne
    have hzW : z ∈ W := by
      by_contra hzW
      exact hgX (hgate y z hyz (hXW.subset hy) hzW ▸ hy)
    exact ⟨y, hy, z, ⟨hzW, hz.2⟩, hadj y z hyz (hXW.subset hy) hzW⟩

/-- A body all of whose neighbours lie in `W` keeps its degree in `G[W]`. -/
theorem _root_.Graph.degree_le_degree_induce [Finite α] {G : Graph α β} [G.Simple] {W : Set α}
    {y : α} (hy : y ∈ W) (hN : ∀ z, G.Adj y z → z ∈ W) : G.degree y ≤ (G.induce W).degree y := by
  rw [Graph.degree_eq_ncard_adj, Graph.degree_eq_ncard_adj]
  refine Set.ncard_le_ncard (fun z hz => ?_) (Set.toFinite _)
  obtain ⟨f, hf⟩ := hz
  exact ⟨f, by rw [Graph.induce_isLink]; exact ⟨hf, hy, hN z ⟨f, hf⟩⟩⟩

/-- A body all of whose neighbours but `p` lie in `W` loses at most one from its degree. -/
theorem _root_.Graph.degree_le_degree_induce_add_one [Finite α] {G : Graph α β} [G.Simple]
    {W : Set α} {y p : α} (hy : y ∈ W) (hN : ∀ z, G.Adj y z → z ∈ W ∨ z = p) :
    G.degree y ≤ (G.induce W).degree y + 1 := by
  rw [Graph.degree_eq_ncard_adj, Graph.degree_eq_ncard_adj]
  have hsub : N(G, y) ⊆ insert p N(G.induce W, y) := by
    intro z hz
    rcases hN z hz with h | h
    · obtain ⟨f, hf⟩ := hz
      exact Or.inr ⟨f, by rw [Graph.induce_isLink]; exact ⟨hf, hy, h⟩⟩
    · exact Or.inl h
  exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_insert_le _ _)

/-- **(H) at a side with one gate**: if `g` is the only body of `W` with a neighbour outside `W`,
and `g` keeps degree at least two in `G[W]`, then `G[W]` satisfies (H). -/
theorem _root_.Graph.IsX0Graph.induce_of_gate [Finite α] {G : Graph α β} (hG : G.IsX0Graph)
    {W : Set α} (hW : W ⊆ V(G)) {g : α} (hg : g ∈ W)
    (hgate : ∀ y z, G.Adj y z → y ∈ W → z ∉ W → y = g)
    (hdeg : 2 ≤ (G.induce W).degree g) : (G.induce W).IsX0Graph := by
  have := hG.simple
  refine ⟨inferInstance, hG.connected.induce_of_gate hW hg hgate, fun y hy => ?_⟩
  by_cases hyg : y = g
  · exact hyg ▸ hdeg
  · exact (hG.two_le_degree y (hW hy)).trans (Graph.degree_le_degree_induce hy fun z hz => by
      by_contra h
      exact hyg (hgate y z hz hy h))

/-! ## The standing hypotheses at a chain's smaller graphs -/

/-- (H) at `G′ = G[V₁]` for a chain of a 2-connected (H)-graph ((MC-79)'s "`G′` satisfies (H)"):
`G − x₀` is connected and `b` is the only gate of `V₁` in it; the ends lose one neighbour each. -/
theorem _root_.Graph.IsChain.isX0Graph_induce [Finite α] {G : Graph α β}
    (hG : G.IsX0Graph) (h2c : ∀ v ∈ V(G), (G.induce (V(G) \ {v})).Connected) {V₁ : Set α}
    {k : ℕ} {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β} (hC : G.IsChain V₁ x a b e) :
    (G.induce V₁).IsX0Graph := by
  have := hG.simple
  have h := hC.toIsOpenEar
  have hk := hC.one_le
  have hV : V₁ ⊆ V(G) := h.cover ▸ Set.subset_union_left
  have h1 : pathVertex a x b 1 = x ⟨0, hk⟩ := pathVertex_eq_of_val_eq_succ a x b (by simp)
  have hx₀V : x ⟨0, hk⟩ ∈ V(G) := h.cover ▸ Or.inr ⟨_, rfl⟩
  have hV₁H : V₁ ⊆ V(G) \ {x ⟨0, hk⟩} := fun y hy =>
    ⟨hV hy, fun hy' => h.notMem ⟨0, hk⟩ (Set.mem_singleton_iff.mp hy' ▸ hy)⟩
  refine ⟨inferInstance, ?_, fun y hy => ?_⟩
  · -- connectivity, through `G − x₀`, with `b` the one gate
    have hconn := (h2c _ hx₀V).induce_of_gate (W := V₁) hV₁H h.right_mem ?_
    · rwa [Graph.induce_induce_of_subset G hV₁H] at hconn
    rintro y z ⟨f, hf⟩ hy hz
    rw [Graph.induce_isLink] at hf
    rcases h.exists_eq_of_isLink_notMem hy hf.1 hz with ⟨rfl, rfl⟩ | ⟨rfl, -⟩
    · exact absurd (h1 ▸ h.isLink_first.right_unique hf.1).symm hf.2.2.2
    · rfl
  · -- degrees: the ends lose one neighbour, every other body none
    have hN := fun z (hz : G.Adj y z) (hzV : z ∉ V₁) =>
      h.exists_eq_of_isLink_notMem hy hz.choose_spec hzV
    by_cases hya : y = a
    · subst hya
      have := Graph.degree_le_degree_induce_add_one (W := V₁) (p := pathVertex y x b 1) hy
        fun z hz => by
          by_cases hzV : z ∈ V₁
          · exact Or.inl hzV
          · rcases hN z hz hzV with ⟨-, h'⟩ | ⟨h', -⟩
            · exact Or.inr (h.isLink_first.right_unique (h' ▸ hz.choose_spec)).symm
            · exact absurd h' h.ne
      have := hC.three_le_degree_left
      omega
    by_cases hyb : y = b
    · subst hyb
      have := Graph.degree_le_degree_induce_add_one (W := V₁)
        (p := pathVertex a x y (Fin.last k).castSucc) hy fun z hz => by
          by_cases hzV : z ∈ V₁
          · exact Or.inl hzV
          · rcases hN z hz hzV with ⟨h', -⟩ | ⟨-, h'⟩
            · exact absurd h'.symm h.ne
            · exact Or.inr (h.isLink_last.right_unique (h' ▸ hz.choose_spec)).symm
      have := hC.three_le_degree_right
      omega
    · refine (hG.two_le_degree y (hV hy)).trans (Graph.degree_le_degree_induce hy fun z hz => ?_)
      by_contra hzV
      rcases hN z hz hzV with ⟨h', -⟩ | ⟨h', -⟩
      · exact hya h'
      · exact hyb h'

/-- **(H) after splitting off at non-adjacent ends** (the tracked item: SHORT's, ORBIT's and
SPLITOFF's antecedents). -/
theorem _root_.Graph.IsX0Graph.splitOff [Finite α] {G : Graph α β} (hG : G.IsX0Graph) {v u w : α}
    {e₁ e₂ : β} (h₁ : G.IsLink e₁ v u) (h₂ : G.IsLink e₂ v w) (hne : e₁ ≠ e₂)
    (honly : ∀ f y, G.IsLink f v y → f = e₁ ∨ f = e₂) (huw : u ≠ w) (hnadj : ¬ G.Adj u w) :
    (G.splitOff v u w e₁).IsX0Graph := by
  classical
  have hloop := hG.simple.toLoopless
  have hvu : v ≠ u := fun h => hloop.not_isLoopAt e₁ v (h ▸ h₁)
  have hvw : v ≠ w := fun h => hloop.not_isLoopAt e₂ v (h ▸ h₂)
  have huV : u ∈ V(G) := h₁.right_mem
  have hwV : w ∈ V(G) := h₂.right_mem
  set S := G.splitOff v u w e₁ with hS
  -- links of `S`
  have hSl : ∀ f x y, S.IsLink f x y ↔ (f ≠ e₁ ∧ G.IsLink f x y ∧ x ≠ v ∧ y ≠ v) ∨
      (f = e₁ ∧ ((x = u ∧ y = w) ∨ (x = w ∧ y = u))) := by
    intro f x y
    rw [hS, Graph.splitOff_isLink]
    constructor
    · rintro (h | ⟨hf, -, -, -, -, hxy⟩)
      · exact Or.inl h
      · exact Or.inr ⟨hf, hxy⟩
    · rintro (h | ⟨hf, hxy⟩)
      · exact Or.inl h
      · exact Or.inr ⟨hf, hvu.symm, hvw.symm, huV, hwV, hxy⟩
  -- an old link not at `v` is not `e₁`
  have hold : ∀ f x y, G.IsLink f x y → x ≠ v → y ≠ v → f ≠ e₁ := by
    rintro f x y hl hx hy rfl
    rcases hl.eq_and_eq_or_eq_and_eq h₁ with ⟨h, -⟩ | ⟨-, h⟩
    · exact hx h
    · exact hy h
  have hsimple : S.Simple := by
    refine { not_isLoopAt := fun f x hfx => ?_, eq_of_isLink := fun f f' x y hf hf' => ?_ }
    · rcases (hSl f x x).mp hfx with ⟨-, hl, -, -⟩ | ⟨-, ⟨rfl, h⟩ | ⟨rfl, h⟩⟩
      · exact hloop.not_isLoopAt f x hl
      · exact huw h
      · exact huw h.symm
    · rcases (hSl f x y).mp hf with ⟨hfe, hl, hx, hy⟩ | ⟨rfl, hxy⟩ <;>
        rcases (hSl f' x y).mp hf' with ⟨hfe', hl', hx', hy'⟩ | ⟨rfl, hxy'⟩
      · exact hG.simple.eq_of_isLink hl hl'
      · rcases hxy' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact absurd ⟨f, hl⟩ hnadj
        · exact absurd ⟨f, hl.symm⟩ hnadj
      · rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact absurd ⟨f', hl'⟩ hnadj
        · exact absurd ⟨f', hl'.symm⟩ hnadj
      · rfl
  -- neighbourhoods
  have hNv : ∀ y, G.Adj v y → y = u ∨ y = w := by
    rintro y ⟨f, hf⟩
    rcases honly f y hf with rfl | rfl
    · exact Or.inl (h₁.right_unique hf).symm
    · exact Or.inr (h₂.right_unique hf).symm
  have hadjS : ∀ x y, S.Adj x y ↔ (G.Adj x y ∧ x ≠ v ∧ y ≠ v) ∨
      ((x = u ∧ y = w) ∨ (x = w ∧ y = u)) := by
    intro x y
    constructor
    · rintro ⟨f, hf⟩
      rcases (hSl f x y).mp hf with ⟨-, hl, hx, hy⟩ | ⟨-, hxy⟩
      · exact Or.inl ⟨⟨f, hl⟩, hx, hy⟩
      · exact Or.inr hxy
    · rintro (⟨⟨f, hl⟩, hx, hy⟩ | hxy)
      · exact ⟨f, (hSl f x y).mpr (Or.inl ⟨hold f x y hl hx hy, hl, hx, hy⟩)⟩
      · exact ⟨e₁, (hSl e₁ x y).mpr (Or.inr ⟨rfl, hxy⟩)⟩
  refine ⟨hsimple, ?_, ?_⟩
  · -- connectivity, by cuts
    have hSV : V(S) = V(G) \ {v} := rfl
    refine (Graph.connected_iff_forall_exists_adj ⟨u, by rw [hSV]; exact ⟨huV, hvu.symm⟩⟩).mpr ?_
    intro X hXS hXne
    have hXV : X ⊆ V(G) \ {v} := hSV ▸ hXS.subset
    obtain ⟨z, hzS, hzX⟩ := Set.exists_of_ssubset hXS
    have hGc := (Graph.connected_iff_forall_exists_adj hG.connected.nonempty).mp hG.connected
    by_cases hu : u ∈ X <;> by_cases hw : w ∈ X
    · -- both in `X`: cut `X ∪ {v}` in `G`
      have hXv : insert v X ⊂ V(G) := by
        refine (Set.insert_subset h₁.left_mem (hXV.trans Set.sdiff_subset)).ssubset_of_ne ?_
        intro h
        have : z ∈ insert v X := h ▸ (hSV ▸ hzS).1
        rcases this with rfl | h'
        · exact (hSV ▸ hzS).2 rfl
        · exact hzX h'
      obtain ⟨x, hx, y, hy, hxy⟩ := hGc _ hXv ⟨v, Set.mem_insert _ _⟩
      have hyv : y ≠ v := fun h => hy.2 (h ▸ Set.mem_insert _ _)
      have hyX : y ∉ X := fun h => hy.2 (Set.mem_insert_of_mem _ h)
      rcases hx with rfl | hxX
      · rcases hNv y hxy with rfl | rfl
        · exact absurd hu hyX
        · exact absurd hw hyX
      · exact ⟨x, hxX, y, ⟨⟨hy.1, hyv⟩, hyX⟩,
          (hadjS x y).mpr (Or.inl ⟨hxy, (hXV hxX).2, hyv⟩)⟩
    · exact ⟨u, hu, w, ⟨⟨hwV, hvw.symm⟩, hw⟩, (hadjS u w).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    · exact ⟨w, hw, u, ⟨⟨huV, hvu.symm⟩, hu⟩, (hadjS w u).mpr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
    · -- neither in `X`: cut `X` in `G`
      obtain ⟨x, hxX, y, hy, hxy⟩ := hGc X ((hXV.trans Set.sdiff_subset).ssubset_of_ne
        fun h => (hXV (h ▸ h₁.left_mem)).2 rfl) hXne
      have hyv : y ≠ v := by
        rintro rfl
        rcases hNv x hxy.symm with rfl | rfl
        · exact hu hxX
        · exact hw hxX
      exact ⟨x, hxX, y, ⟨⟨hy.1, hyv⟩, hy.2⟩, (hadjS x y).mpr (Or.inl ⟨hxy, (hXV hxX).2, hyv⟩)⟩
  · -- degrees, through neighbourhoods
    intro y hy
    have hyV : y ∈ V(G) := hy.1
    have hyv : y ≠ v := hy.2
    rw [Graph.degree_eq_ncard_adj]
    have hdG := hG.two_le_degree y hyV
    rw [@Graph.degree_eq_ncard_adj _ _ _ _ hG.simple] at hdG
    by_cases hyu : y = u
    · subst hyu
      have : N(S, y) = insert w (N(G, y) \ {v}) := by
        ext z
        simp only [Graph.Neighbor, Set.mem_ofPred_eq, hadjS, Set.mem_insert_iff, Set.mem_sdiff,
          Set.mem_singleton_iff]
        tauto
      rw [this, Set.ncard_insert_of_notMem (fun h => hnadj h.1) (Set.toFinite _),
        Set.ncard_sdiff_singleton_of_mem (show v ∈ N(G, y) from ⟨e₁, h₁.symm⟩)]
      omega
    by_cases hyw : y = w
    · subst hyw
      have : N(S, y) = insert u (N(G, y) \ {v}) := by
        ext z
        simp only [Graph.Neighbor, Set.mem_ofPred_eq, hadjS, Set.mem_insert_iff, Set.mem_sdiff,
          Set.mem_singleton_iff]
        tauto
      rw [this, Set.ncard_insert_of_notMem (fun h => hnadj h.1.symm) (Set.toFinite _),
        Set.ncard_sdiff_singleton_of_mem (show v ∈ N(G, y) from ⟨e₂, h₂.symm⟩)]
      omega
    · have : N(S, y) = N(G, y) := by
        ext z
        simp only [Graph.Neighbor, Set.mem_ofPred_eq, hadjS]
        constructor
        · rintro (⟨h, -, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩)
          · exact h
          · exact absurd rfl hyu
          · exact absurd rfl hyw
        · intro h
          refine Or.inl ⟨h, hyv, fun hz => ?_⟩
          subst hz
          rcases hNv y h.symm with rfl | rfl
          · exact hyu rfl
          · exact hyw rfl
      rw [this]
      exact hdG

/-- (H) at SHORT's four-body antecedent. -/
theorem _root_.Graph.IsOpenEar.isX0Graph_splitOff_four [Finite α] {G : Graph α β} (hG : G.IsX0Graph)
    {V₁ : Set α} {x : Fin 4 → α} {a b : α} {e : Fin 5 → β}
    (hear : G.IsOpenEar V₁ x a b e) : (G.splitOff (x 1) (x 0) (x 2) (e 1)).IsX0Graph := by
  have l0 : G.IsLink (e 0) a (x 0) := hear.isLink 0
  have l1 : G.IsLink (e 1) (x 0) (x 1) := hear.isLink 1
  have l2 : G.IsLink (e 2) (x 1) (x 2) := hear.isLink 2
  have hne : e 1 ≠ e 2 := by
    intro h; rw [h] at l1
    rcases l1.left_eq_or_eq l2 with h' | h'
    · exact absurd (hear.inj h') (by decide)
    · exact absurd (hear.inj h') (by decide)
  refine hG.splitOff l1.symm l2 hne (fun f y hf => hear.isLink_interior 1 hf)
    (fun h => absurd (hear.inj h) (by decide)) ?_
  rintro ⟨f, hf⟩
  rcases hear.isLink_interior 0 hf with rfl | rfl
  · exact hear.notMem 2 ((l0.symm.right_unique hf) ▸ hear.left_mem)
  · exact absurd (hear.inj (l1.right_unique hf)) (by decide)

/-- (H) at SHORT's three-body antecedent. -/
theorem _root_.Graph.IsOpenEar.isX0Graph_splitOff_three [Finite α] {G : Graph α β}
    (hG : G.IsX0Graph)
    {V₁ : Set α} {x : Fin 3 → α} {a b : α} {e : Fin 4 → β}
    (hear : G.IsOpenEar V₁ x a b e) : (G.splitOff (x 1) (x 0) (x 2) (e 1)).IsX0Graph := by
  have l0 : G.IsLink (e 0) a (x 0) := hear.isLink 0
  have l1 : G.IsLink (e 1) (x 0) (x 1) := hear.isLink 1
  have l2 : G.IsLink (e 2) (x 1) (x 2) := hear.isLink 2
  have hne : e 1 ≠ e 2 := by
    intro h; rw [h] at l1
    rcases l1.left_eq_or_eq l2 with h' | h'
    · exact absurd (hear.inj h') (by decide)
    · exact absurd (hear.inj h') (by decide)
  refine hG.splitOff l1.symm l2 hne (fun f y hf => hear.isLink_interior 1 hf)
    (fun h => absurd (hear.inj h) (by decide)) ?_
  rintro ⟨f, hf⟩
  rcases hear.isLink_interior 0 hf with rfl | rfl
  · exact hear.notMem 2 ((l0.symm.right_unique hf) ▸ hear.left_mem)
  · exact absurd (hear.inj (l1.right_unique hf)) (by decide)

/-- (H) at ORBIT's antecedent. -/
theorem _root_.Graph.IsOpenEar.isX0Graph_splitOff_orbit [Finite α] {G : Graph α β}
    (hG : G.IsX0Graph)
    {V₁ : Set α} {x : Fin 2 → α} {a b : α} {e : Fin 3 → β}
    (hear : G.IsOpenEar V₁ x a b e) : (G.splitOff (x 1) (x 0) b (e 1)).IsX0Graph := by
  have l0 : G.IsLink (e 0) a (x 0) := hear.isLink 0
  have l1 : G.IsLink (e 1) (x 0) (x 1) := hear.isLink 1
  have l2 : G.IsLink (e 2) (x 1) b := hear.isLink 2
  have hne : e 1 ≠ e 2 := by
    intro h; rw [h] at l1
    rcases l1.left_eq_or_eq l2 with h' | h'
    · exact absurd (hear.inj h') (by decide)
    · exact hear.notMem 0 (h' ▸ hear.right_mem)
  refine hG.splitOff l1.symm l2 hne (fun f y hf => hear.isLink_interior 1 hf)
    (fun h => hear.notMem 0 (h ▸ hear.right_mem)) ?_
  rintro ⟨f, hf⟩
  rcases hear.isLink_interior 0 hf with rfl | rfl
  · exact hear.ne (l0.symm.right_unique hf)
  · exact hear.notMem 1 ((l1.right_unique hf) ▸ hear.right_mem)

/-- (H) at SPLITOFF's antecedent. -/
theorem _root_.Graph.IsOpenEar.isX0Graph_splitOff_one [Finite α] {G : Graph α β} (hG : G.IsX0Graph)
    {V₁ : Set α} {x : Fin 1 → α} {a b : α} {e : Fin 2 → β}
    (hear : G.IsOpenEar V₁ x a b e) (hnadj : ¬ G.Adj a b) :
    (G.splitOff (x 0) a b (e 0)).IsX0Graph := by
  have l0 : G.IsLink (e 0) a (x 0) := hear.isLink 0
  have l1 : G.IsLink (e 1) (x 0) b := hear.isLink 1
  have hne : e 0 ≠ e 1 := by
    intro h; rw [h] at l0
    rcases l0.left_eq_or_eq l1 with h' | h'
    · exact hear.notMem 0 (h' ▸ hear.left_mem)
    · exact hear.ne h'
  exact hG.splitOff l0.symm l1 hne (fun f y hf => hear.isLink_interior 0 hf) hear.ne hnadj

end CombinatorialRigidity.Molecular
