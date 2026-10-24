/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.CoverageChain

/-!
# The standing hypotheses at the smaller graphs of a chain, and graphs that are not 2-connected

The standing hypotheses at the smaller graphs that a chain gives (`lem:pencil-x0-chain-standing`),
and the two cases of the structural coverage at a graph that is not 2-connected
(`lem:pencil-x0-cut-reduces`), both in `sec:main-component-coverage`.

Both rest on one fact (`Graph.Connected.induce_of_gate`): in a connected graph, a set of bodies
whose only body with a neighbour outside it is `g` induces a connected graph. So a set `W` of that
form satisfies the standing hypotheses when `g` has degree at least two in `G[W]`, as every other
body of `W` keeps all its neighbours (`Graph.IsX0Graph.induce_of_gate`). For a chain
`a − x 0 − ⋯ − x (k − 1) − b` on `V₁` of a graph with `G − v` connected for every body `v`, the set
`V₁` has that form in `G − x 0`, with `b` as `g`, and the ends keep degree at least two in `G[V₁]`,
as they have degree at least three in `G` and lose one neighbour each. Splitting off a body whose
links are one to each of two distinct bodies that are not adjacent keeps the standing hypotheses
(`Graph.IsX0Graph.splitOff`). At an open ear with one to four interior bodies this gives them at the
graph with an interior body suppressed, which the ear and split-off steps at a usable chain assume
(`lem:pencil-x0-chain-reduces`).

A graph that is not 2-edge-connected has a nonempty proper set of bodies left by exactly one link.
That link is a chain of bridges with no path body between the two sides. It grows through bodies of
degree two at its ends until both ends have degree at least three, and then each side is smaller
than `G` (the clause `Graph.X0Reduces.bridgePath`). A 2-edge-connected graph with a cut vertex `v`
has two sides that meet in `v`. The body `v` sends at least two links into each, and each is smaller
than `G` (the clause `Graph.X0Reduces.cutVertex`).

## Main results

* `Graph.Connected.induce_of_gate`: a step of `lem:pencil-x0-chain-standing` and
  `lem:pencil-x0-cut-reduces`, a set whose only body with a neighbour outside it is `g` induces a
  connected graph.
* `Graph.IsChain.isX0Graph_induce`: `lem:pencil-x0-chain-standing`(1), if `G` satisfies the standing
  hypotheses and `G − v` is connected for every body `v`, then `G[V₁]` satisfies them for every
  chain on `V₁`.
* `Graph.IsX0Graph.splitOff`: `lem:pencil-x0-chain-standing`(2), splitting off a body whose links
  are one to each of two distinct bodies that are not adjacent keeps the standing hypotheses.
* `Graph.IsX0Graph.x0Reduces_of_not_twoEdgeConnected`: `lem:pencil-x0-cut-reduces`(1), a graph
  satisfying the standing hypotheses that is not 2-edge-connected reduces to the graphs smaller than
  it.
* `Graph.IsX0Graph.x0Reduces_of_not_connected`: `lem:pencil-x0-cut-reduces`(2), so does a
  2-edge-connected one with `G − v` disconnected for some body `v`.
-/

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {α β : Type*}

/-! ## A set whose only body with a neighbour outside it is `g` -/

/-- **A set whose only body with a neighbour outside it is `g` induces a connected graph** (a step
of `lem:pencil-x0-chain-standing` and `lem:pencil-x0-cut-reduces`): in a connected graph `H`, let
`W ⊆ V(H)` contain `g`, and let every link of `H` from a body `y ∈ W` to a body outside `W` have
`y = g`. Then `H[W]` is connected. A nonempty proper part of `W` that avoids `g` (the part itself,
or its complement in `W` when it contains `g`) is left by a link of `H`, as `H` is connected; that
link starts at a body other than `g`, so it ends in `W`, and it is a link of `H[W]` between the part
and the rest of `W`. -/
theorem _root_.Graph.Connected.induce_of_gate {H : Graph α β} (hH : H.Connected) {W : Set α}
    (hW : W ⊆ V(H)) {g : α} (hg : g ∈ W)
    (hgate : ∀ y z, H.Adj y z → y ∈ W → z ∉ W → y = g) : (H.induce W).Connected := by
  refine (Graph.connected_iff_forall_exists_adj ⟨g, hg⟩).mpr fun X hXW hXne => ?_
  have hHc := (Graph.connected_iff_forall_exists_adj hH.nonempty).mp hH
  rw [Graph.vertexSet_induce] at hXW
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

/-- **The standing hypotheses at a set whose only body with a neighbour outside it is `g`** (a step
of `lem:pencil-x0-cut-reduces`): let `G` satisfy the standing hypotheses, and let `g ∈ W ⊆ V(G)` be
the only body of `W` with a neighbour outside `W`. If `g` has degree at least two in `G[W]`, then
`G[W]` satisfies the standing hypotheses: it is connected (`Graph.Connected.induce_of_gate`), and
every other body of `W` keeps all its neighbours. -/
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

/-! ## The standing hypotheses at the smaller graphs of a chain (`lem:pencil-x0-chain-standing`) -/

/-- **The standing hypotheses at `G[V₁]` for a chain on `V₁`** (`lem:pencil-x0-chain-standing`(1)):
if `G` satisfies the standing hypotheses and `G − v` is connected for every body `v`, then `G[V₁]`
satisfies them for every chain `a − x 0 − ⋯ − x (k − 1) − b` on `V₁`. In `G − x 0` no body of `V₁`
other than `b` has a neighbour outside `V₁`, so `G[V₁]` is connected
(`Graph.Connected.induce_of_gate`). The ends lose one neighbour each and keep degree at least two,
as they have degree at least three in `G`, and every other body of `V₁` keeps all its neighbours. -/
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
  · -- connectivity, through `G − x 0`, in which only `b` of `V₁` has a neighbour outside `V₁`
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

/-- **The standing hypotheses after splitting off** (`lem:pencil-x0-chain-standing`(2)): let `G`
satisfy the standing hypotheses, and let the links at a body `v` be `e₁`, to `u`, and `e₂`, to `w`,
where `u ≠ w` are not adjacent. Then the splitting-off `G.splitOff v u w e₁`, whose new link
`u − w` takes the label `e₁`, satisfies the standing hypotheses. The new link is not parallel to an
old one, as `u` and `w` are not adjacent; `u` and `w` each exchange the link to `v` for the new
link, and every other body keeps its neighbours. A set of bodies left by no link of the
splitting-off contains both or neither of `u` and `w`, and then, with `v` added in the first case,
it is left by no link of `G`. -/
theorem _root_.Graph.IsX0Graph.splitOff [Finite α] {G : Graph α β} (hG : G.IsX0Graph) {v u w : α}
    {e₁ e₂ : β} (h₁ : G.IsLink e₁ v u) (h₂ : G.IsLink e₂ v w)
    (honly : ∀ f y, G.IsLink f v y → f = e₁ ∨ f = e₂) (huw : u ≠ w) (hnadj : ¬ G.Adj u w) :
    (G.splitOff v u w e₁).IsX0Graph := by
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
      rw [this, Set.ncard_insert_of_notMem (fun (h : w ∈ N(G, y) \ {v}) => hnadj h.1)
          (Set.toFinite _),
        Set.ncard_sdiff_singleton_of_mem (show v ∈ N(G, y) from ⟨e₁, h₁.symm⟩)]
      omega
    by_cases hyw : y = w
    · subst hyw
      have : N(S, y) = insert u (N(G, y) \ {v}) := by
        ext z
        simp only [Graph.Neighbor, Set.mem_ofPred_eq, hadjS, Set.mem_insert_iff, Set.mem_sdiff,
          Set.mem_singleton_iff]
        tauto
      rw [this, Set.ncard_insert_of_notMem (fun (h : u ∈ N(G, y) \ {v}) => hnadj h.1.symm)
          (Set.toFinite _),
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

/-- The standing hypotheses at `G` with `x 1` suppressed, for an open ear with four interior bodies
(a step of `lem:pencil-x0-chain-reduces`, for `Graph.X0Reduces.openEarFour`): `x 0` and `x 2` are
not adjacent, as the only links at `x 0` are `e 0`, to `a`, and `e 1`, to `x 1`. -/
theorem _root_.Graph.IsOpenEar.isX0Graph_splitOff_four [Finite α] {G : Graph α β} (hG : G.IsX0Graph)
    {V₁ : Set α} {x : Fin 4 → α} {a b : α} {e : Fin 5 → β}
    (hear : G.IsOpenEar V₁ x a b e) : (G.splitOff (x 1) (x 0) (x 2) (e 1)).IsX0Graph := by
  have l0 : G.IsLink (e 0) a (x 0) := hear.isLink 0
  have l1 : G.IsLink (e 1) (x 0) (x 1) := hear.isLink 1
  have l2 : G.IsLink (e 2) (x 1) (x 2) := hear.isLink 2
  refine hG.splitOff l1.symm l2 (fun f y hf => hear.isLink_interior 1 hf)
    (fun h => absurd (hear.inj h) (by decide)) ?_
  rintro ⟨f, hf⟩
  rcases hear.isLink_interior 0 hf with rfl | rfl
  · exact hear.notMem 2 ((l0.symm.right_unique hf) ▸ hear.left_mem)
  · exact absurd (hear.inj (l1.right_unique hf)) (by decide)

/-- The standing hypotheses at `G` with `x 1` suppressed, for an open ear with three interior bodies
(a step of `lem:pencil-x0-chain-reduces`, for `Graph.X0Reduces.openEarThree`): `x 0` and `x 2` are
not adjacent, as the only links at `x 0` are `e 0`, to `a`, and `e 1`, to `x 1`. -/
theorem _root_.Graph.IsOpenEar.isX0Graph_splitOff_three [Finite α] {G : Graph α β}
    (hG : G.IsX0Graph)
    {V₁ : Set α} {x : Fin 3 → α} {a b : α} {e : Fin 4 → β}
    (hear : G.IsOpenEar V₁ x a b e) : (G.splitOff (x 1) (x 0) (x 2) (e 1)).IsX0Graph := by
  have l0 : G.IsLink (e 0) a (x 0) := hear.isLink 0
  have l1 : G.IsLink (e 1) (x 0) (x 1) := hear.isLink 1
  have l2 : G.IsLink (e 2) (x 1) (x 2) := hear.isLink 2
  refine hG.splitOff l1.symm l2 (fun f y hf => hear.isLink_interior 1 hf)
    (fun h => absurd (hear.inj h) (by decide)) ?_
  rintro ⟨f, hf⟩
  rcases hear.isLink_interior 0 hf with rfl | rfl
  · exact hear.notMem 2 ((l0.symm.right_unique hf) ▸ hear.left_mem)
  · exact absurd (hear.inj (l1.right_unique hf)) (by decide)

/-- The standing hypotheses at `G` with `x 1` suppressed, for an open ear with two interior bodies
(a step of `lem:pencil-x0-chain-reduces`, for `Graph.X0Reduces.openEarTwoSplitOff`): `x 0` and `b`
are not adjacent, as the only links at `x 0` are `e 0`, to `a ≠ b`, and `e 1`, to `x 1`. -/
theorem _root_.Graph.IsOpenEar.isX0Graph_splitOff_orbit [Finite α] {G : Graph α β}
    (hG : G.IsX0Graph)
    {V₁ : Set α} {x : Fin 2 → α} {a b : α} {e : Fin 3 → β}
    (hear : G.IsOpenEar V₁ x a b e) : (G.splitOff (x 1) (x 0) b (e 1)).IsX0Graph := by
  have l0 : G.IsLink (e 0) a (x 0) := hear.isLink 0
  have l1 : G.IsLink (e 1) (x 0) (x 1) := hear.isLink 1
  have l2 : G.IsLink (e 2) (x 1) b := hear.isLink 2
  refine hG.splitOff l1.symm l2 (fun f y hf => hear.isLink_interior 1 hf)
    (fun h => hear.notMem 0 (h ▸ hear.right_mem)) ?_
  rintro ⟨f, hf⟩
  rcases hear.isLink_interior 0 hf with rfl | rfl
  · exact hear.ne (l0.symm.right_unique hf)
  · exact hear.notMem 1 ((l1.right_unique hf) ▸ hear.right_mem)

/-- The standing hypotheses at `G` with `x 0` suppressed, for an open ear with one interior body
whose ends `a` and `b` are not adjacent (a step of `lem:pencil-x0-chain-reduces`, for
`Graph.X0Reduces.splitOff`). -/
theorem _root_.Graph.IsOpenEar.isX0Graph_splitOff_one [Finite α] {G : Graph α β} (hG : G.IsX0Graph)
    {V₁ : Set α} {x : Fin 1 → α} {a b : α} {e : Fin 2 → β}
    (hear : G.IsOpenEar V₁ x a b e) (hnadj : ¬ G.Adj a b) :
    (G.splitOff (x 0) a b (e 0)).IsX0Graph := by
  have l0 : G.IsLink (e 0) a (x 0) := hear.isLink 0
  have l1 : G.IsLink (e 1) (x 0) b := hear.isLink 1
  exact hG.splitOff l0.symm l1 (fun f y hf => hear.isLink_interior 0 hf) hear.ne hnadj

/-! ## A graph that is not 2-edge-connected (`lem:pencil-x0-cut-reduces`(1)) -/

/-- On a chain of bridges from `a ∈ V₁` to `b ∈ V₂`, given as an open ear on `V₁ ∪ V₂` every other
link of which lies inside `V₁` or inside `V₂`, the only link leaving `V₁` is `e 0`, at `a`. -/
private theorem bridge_gate_left {G : Graph α β} {V₁ V₂ : Set α} {k : ℕ} {x : Fin k → α} {a b : α}
    {e : Fin (k + 1) → β} (h : G.IsOpenEar (V₁ ∪ V₂) x a b e) (hd : Disjoint V₁ V₂)
    (hb : b ∈ V₂)
    (hs : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → (u ∈ V₁ ∧ w ∈ V₁) ∨ (u ∈ V₂ ∧ w ∈ V₂))
    {y z : α} {f : β} (hy : y ∈ V₁) (hf : G.IsLink f y z) (hz : z ∉ V₁) : y = a ∧ f = e 0 := by
  by_cases hfe : ∃ i, f = e i
  · have hxV₁ : ∀ i, x i ∉ V₁ := fun i hi => h.notMem i (Or.inl hi)
    obtain ⟨i, rfl⟩ := hfe
    rcases hf.eq_and_eq_or_eq_and_eq (h.isLink i) with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · rcases val_eq_zero_or_of_pathVertex_mem hxV₁ hy with h0 | h0
      · exact ⟨pathVertex_eq_of_val_eq_zero _ _ _ h0, congrArg e (Fin.ext (by simpa using h0))⟩
      · simp only [Fin.val_castSucc] at h0; omega
    · rcases val_eq_zero_or_of_pathVertex_mem hxV₁ hy with h0 | h0
      · simp at h0
      · have hbV₁ : b ∈ V₁ := by rw [← pathVertex_eq_of_val_eq_last a x b h0]; exact hy
        exact absurd hb (Set.disjoint_left.mp hd hbV₁)
  · push Not at hfe
    rcases hs f y z hf hfe with ⟨-, hz'⟩ | ⟨hy', -⟩
    · exact absurd hz' hz
    · exact absurd hy' (Set.disjoint_left.mp hd hy)

/-- The side `V₁` of a chain of bridges from `a ∈ V₁` to `b ∈ V₂` is smaller than `G` when `a` has
degree at least three: `G[V₁]` satisfies the standing hypotheses, as `a` is its only body with a
neighbour outside it and loses only the next body on the path, and it lacks `b`. -/
private theorem x0Below_induce_bridge_left [Finite α] {G : Graph α β} (hG : G.IsX0Graph)
    {V₁ V₂ : Set α} {k : ℕ} {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β}
    (h : G.IsOpenEar (V₁ ∪ V₂) x a b e) (hd : Disjoint V₁ V₂) (ha : a ∈ V₁) (hb : b ∈ V₂)
    (hs : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → (u ∈ V₁ ∧ w ∈ V₁) ∨ (u ∈ V₂ ∧ w ∈ V₂))
    (ha3 : 3 ≤ G.degree a) : G.X0Below (G.induce V₁) := by
  have := hG.simple
  have hVG : V₁ ∪ V₂ ⊆ V(G) := h.cover ▸ Set.subset_union_left
  have hV₁ : V₁ ⊆ V(G) := Set.subset_union_left.trans hVG
  refine ⟨hG.induce_of_gate hV₁ ha
    (fun y z (hyz : G.Adj y z) hy hz => (bridge_gate_left h hd hb hs hy hyz.choose_spec hz).1)
    ?_, ?_⟩
  · have := Graph.degree_le_degree_induce_add_one (W := V₁) (p := pathVertex a x b 1) ha
      fun z (hz' : G.Adj a z) => by
        obtain ⟨f, hf⟩ := hz'
        by_cases hz : z ∈ V₁
        · exact Or.inl hz
        · obtain ⟨-, rfl⟩ := bridge_gate_left h hd hb hs ha hf hz
          exact Or.inr (h.isLink_first.right_unique hf).symm
    omega
  · exact Set.ncard_lt_ncard (hV₁.ssubset_of_ne fun hEq =>
      Set.disjoint_left.mp hd (hEq ▸ hVG (Or.inr hb)) hb)

/-- A chain of bridges read from its other end. -/
private theorem bridge_symm {G : Graph α β} {V₁ V₂ : Set α} {k : ℕ} {x : Fin k → α} {a b : α}
    {e : Fin (k + 1) → β} (h : G.IsOpenEar (V₁ ∪ V₂) x a b e) (hd : Disjoint V₁ V₂)
    (hs : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → (u ∈ V₁ ∧ w ∈ V₁) ∨ (u ∈ V₂ ∧ w ∈ V₂)) :
    G.IsOpenEar (V₂ ∪ V₁) (x ∘ Fin.rev) b a (e ∘ Fin.rev) ∧ Disjoint V₂ V₁ ∧
      ∀ f u w, G.IsLink f u w → (∀ i, f ≠ (e ∘ Fin.rev) i) →
        (u ∈ V₂ ∧ w ∈ V₂) ∨ (u ∈ V₁ ∧ w ∈ V₁) :=
  ⟨Set.union_comm V₁ V₂ ▸ h.symm, hd.symm,
    fun f u w hf hfe => (hs f u w hf fun i => by simpa using hfe i.rev).symm⟩

/-- A chain of bridges whose end `a` has degree two extends into `V₁`: the other link at `a` ends at
a body `a' ∈ V₁ \ {a}`, which becomes the new end, and `a` becomes a path body. -/
private theorem bridge_cons [Finite β] {G : Graph α β} [G.Simple] {V₁ V₂ : Set α} {k : ℕ}
    {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β} (h : G.IsOpenEar (V₁ ∪ V₂) x a b e)
    (hd : Disjoint V₁ V₂) (ha : a ∈ V₁) (hb : b ∈ V₂)
    (hs : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → (u ∈ V₁ ∧ w ∈ V₁) ∨ (u ∈ V₂ ∧ w ∈ V₂))
    (ha2 : G.degree a = 2) :
    ∃ a' g, G.IsOpenEar ((V₁ \ {a}) ∪ V₂) (Fin.cons a x) a' b (Fin.cons g e) ∧
      Disjoint (V₁ \ {a}) V₂ ∧ a' ∈ V₁ \ {a} ∧
      ∀ f u w, G.IsLink f u w → (∀ i, f ≠ (Fin.cons g e : Fin (k + 2) → β) i) →
        (u ∈ V₁ \ {a} ∧ w ∈ V₁ \ {a}) ∨ (u ∈ V₂ ∧ w ∈ V₂) := by
  obtain ⟨a', g, hg, ha'a, hge, honly⟩ := h.exists_isLink_of_degree_eq_two ha2
  have haV₂ : a ∉ V₂ := Set.disjoint_left.mp hd ha
  have ha' : a' ∈ V₁ := by
    rcases hs g a a' hg hge with ⟨-, h'⟩ | ⟨h', -⟩
    · exact h'
    · exact absurd h' haV₂
  have hset : (V₁ ∪ V₂) \ {a} = (V₁ \ {a}) ∪ V₂ := by
    ext y
    simp only [Set.mem_sdiff, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hy | hy, hya⟩
      · exact Or.inl ⟨hy, hya⟩
      · exact Or.inr hy
    · rintro (⟨hy, hya⟩ | hy)
      · exact ⟨Or.inl hy, hya⟩
      · exact ⟨Or.inr hy, fun hya => haV₂ (hya ▸ hy)⟩
  have hear := h.cons hg.symm (Or.inl ha') ha'a
    (fun h' => Set.disjoint_left.mp hd (h' ▸ ha') hb) honly
  rw [hset] at hear
  refine ⟨a', g, hear, Set.disjoint_of_subset_left Set.sdiff_subset hd, ⟨ha', ha'a⟩, ?_⟩
  intro f u w hf hfe
  have hfg : f ≠ g := by simpa using hfe 0
  have hfe' : ∀ i, f ≠ e i := fun i => by simpa using hfe i.succ
  rcases hs f u w hf hfe' with ⟨hu, hw⟩ | h'
  · refine Or.inl ⟨⟨hu, fun hua => ?_⟩, ⟨hw, fun hwa => ?_⟩⟩
    · rw [Set.mem_singleton_iff] at hua
      rw [hua] at hf
      rcases honly f w hf with h' | h'
      · exact hfe' 0 h'
      · exact hfg h'
    · rw [Set.mem_singleton_iff] at hwa
      rw [hwa] at hf
      rcases honly f u hf.symm with h' | h'
      · exact hfe' 0 h'
      · exact hfg h'
  · exact Or.inr h'

/-- **The maximal chain of bridges** (a step of `lem:pencil-x0-cut-reduces`(1)): if `G` satisfies
the standing hypotheses and has a chain of bridges from `a ∈ V₁` to `b ∈ V₂`, given as an open ear
on `V₁ ∪ V₂` every other link of which lies inside `V₁` or inside `V₂`, then `G` reduces to the
graphs smaller than it. By strong induction on `|V₁| + |V₂|`: an end of degree two extends the chain
into its side, and once both ends have degree at least three, both sides are smaller than `G` and
the clause `Graph.X0Reduces.bridgePath` applies. -/
private theorem x0Reduces_of_bridgeEar [Finite α] [Finite β] {G : Graph α β} (hG : G.IsX0Graph) :
    ∀ (n : ℕ) {V₁ V₂ : Set α} {k : ℕ} {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β},
    V₁.ncard + V₂.ncard = n → G.IsOpenEar (V₁ ∪ V₂) x a b e → Disjoint V₁ V₂ → a ∈ V₁ →
    b ∈ V₂ →
    (∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → (u ∈ V₁ ∧ w ∈ V₁) ∨ (u ∈ V₂ ∧ w ∈ V₂)) →
    G.X0Reduces G.X0Below := by
  have := hG.simple
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V₁ V₂ k x a b e hn h hd ha hb hs
  have hVG : V₁ ∪ V₂ ⊆ V(G) := h.cover ▸ Set.subset_union_left
  obtain ⟨h', hd', hs'⟩ := bridge_symm h hd hs
  by_cases ha3 : 3 ≤ G.degree a
  · by_cases hb3 : 3 ≤ G.degree b
    · refine .bridgePath (V₁ := V₁) (V₂ := V₂) ?_ hd (fun i hi => h.notMem i (Or.inl hi))
        (fun i hi => h.notMem i (Or.inr hi)) h.inj ha hb h.isLink hs
        (x0Below_induce_bridge_left hG h hd ha hb hs ha3)
        (x0Below_induce_bridge_left hG h' hd' hb ha hs' hb3)
      rw [h.cover]
      ext y
      simp only [Set.mem_union]
      tauto
    · have hb2 : G.degree b = 2 := by
        have := hG.two_le_degree b (hVG (Or.inr hb)); omega
      obtain ⟨b', g, h'', hd'', hb'', hs''⟩ := bridge_cons h' hd' hb ha hs' hb2
      have hlt := Set.ncard_sdiff_singleton_lt_of_mem hb (Set.toFinite _)
      exact ih ((V₂ \ {b}).ncard + V₁.ncard) (by omega) rfl h'' hd'' hb'' ha hs''
  · have ha2 : G.degree a = 2 := by
      have := hG.two_le_degree a (hVG (Or.inl ha)); omega
    obtain ⟨a', g, h'', hd'', ha'', hs''⟩ := bridge_cons h hd ha hb hs ha2
    have hlt := Set.ncard_sdiff_singleton_lt_of_mem ha (Set.toFinite _)
    exact ih ((V₁ \ {a}).ncard + V₂.ncard) (by omega) rfl h'' hd'' ha'' hb hs''

/-- **A graph that is not 2-edge-connected** (`lem:pencil-x0-cut-reduces`(1)): if `G` satisfies the
standing hypotheses and is not 2-edge-connected, then `G` reduces to the graphs smaller than it, by
the clause of a chain of bridges. As `G` is connected, some nonempty proper set `V'` of bodies is
left by exactly one link `e₀`, from `u ∈ V'` to `v ∉ V'`. That link is a chain of bridges with no
path body between the sides `V'` and `V(G) \ V'`, and it grows into a maximal one. -/
theorem _root_.Graph.IsX0Graph.x0Reduces_of_not_twoEdgeConnected [Finite α] [Finite β]
    {G : Graph α β} (hG : G.IsX0Graph) (htec : ¬ G.TwoEdgeConnected) :
    G.X0Reduces G.X0Below := by
  simp only [Graph.TwoEdgeConnected, not_forall, not_le] at htec
  obtain ⟨V', hne, hss, hlt⟩ := htec
  obtain ⟨u, hu, v, hv, e₀, he₀⟩ :=
    (Graph.connected_iff_forall_exists_adj hG.connected.nonempty).mp hG.connected V' hss hne
  have he₀c : e₀ ∈ G.cutEdges V' := ⟨he₀.edge_mem, u, v, he₀, hu, hv.2⟩
  have hcut : ∀ f ∈ G.cutEdges V', f = e₀ := fun f hf =>
    (Set.ncard_le_one (s := G.cutEdges V') (Set.toFinite _)).mp (by omega) f hf e₀ he₀c
  have hVV : V' ∪ (V(G) \ V') = V(G) := Set.union_sdiff_cancel hss.subset
  have huv : u ≠ v := fun h => hv.2 (h ▸ hu)
  refine x0Reduces_of_bridgeEar hG _ (V₁ := V') (V₂ := V(G) \ V') (x := Fin.elim0) (a := u)
    (b := v) (e := ![e₀]) rfl ⟨?_, fun i => i.elim0, fun i => i.elim0, Or.inl hu, Or.inr hv, huv,
      ?_, fun f p q hf _ => by rw [hVV]; exact ⟨hf.left_mem, hf.right_mem⟩⟩
      Set.disjoint_sdiff_right hu hv ?_
  · rw [hVV, Set.range_eq_empty, Set.union_empty]
  · intro i
    fin_cases i
    simpa [pathVertex, Fin.snoc] using he₀
  · intro f p q hf hfe
    have hfe₀ : f ≠ e₀ := hfe 0
    by_cases hp : p ∈ V' <;> by_cases hq : q ∈ V'
    · exact Or.inl ⟨hp, hq⟩
    · exact absurd (hcut f ⟨hf.edge_mem, p, q, hf, hp, hq⟩) hfe₀
    · exact absurd (hcut f ⟨hf.edge_mem, q, p, hf.symm, hq, hp⟩) hfe₀
    · exact Or.inr ⟨⟨hf.left_mem, hp⟩, ⟨hf.right_mem, hq⟩⟩

/-! ## A cut vertex (`lem:pencil-x0-cut-reduces`(2)) -/

/-- **A cut vertex** (`lem:pencil-x0-cut-reduces`(2)): if `G` satisfies the standing hypotheses and
is 2-edge-connected, and `G − v` is disconnected for a body `v`, then `G` reduces to the graphs
smaller than it, by the cut-vertex clause at `v` (`Graph.X0Reduces.cutVertex`). A nonempty set `X`
of bodies of `G − v`, closed under adjacency there and not all of its bodies, gives the sides
`X ∪ {v}` and `V(G) \ X`, which meet in `v`. The body `v` sends at least two links into each side,
as `G` is 2-edge-connected, and every other body keeps all its neighbours. Each side is connected,
as `v` is its only body with a neighbour outside it (`Graph.IsX0Graph.induce_of_gate`), and has
fewer bodies than `G`. -/
theorem _root_.Graph.IsX0Graph.x0Reduces_of_not_connected [Finite α] [Finite β] {G : Graph α β}
    (hG : G.IsX0Graph) (htec : G.TwoEdgeConnected) {v : α}
    (hdisc : ¬ (G.induce (V(G) \ {v})).Connected) : G.X0Reduces G.X0Below := by
  have := hG.simple
  -- off `V(G)`, `G − v` is `G`, which is connected
  have hv : v ∈ V(G) := by
    by_contra hv
    rw [Set.sdiff_singleton_eq_self hv, Graph.induce_vertexSet] at hdisc
    exact hdisc hG.connected
  obtain ⟨c₀, e₀, hc₀⟩ : ∃ c e, G.IsLink e v c := by
    have h2 := hG.two_le_degree v hv
    rw [Graph.degree_eq_ncard_adj] at h2
    obtain ⟨c, hc⟩ := Set.nonempty_of_ncard_ne_zero (s := N(G, v)) (by omega)
    obtain ⟨e, he⟩ := hc
    exact ⟨c, e, he⟩
  have hc₀v : c₀ ≠ v := fun h => Graph.Loopless.not_isLoopAt e₀ v (h ▸ hc₀)
  obtain ⟨X, hXH, hXne, hXcl⟩ := Graph.exists_of_not_connected hdisc
    ⟨c₀, hc₀.right_mem, hc₀v⟩
  have hXV : X ⊆ V(G) \ {v} := hXH.subset
  have hXG : X ⊆ V(G) := hXV.trans Set.sdiff_subset
  have hvX : v ∉ X := fun h => (hXV h).2 rfl
  have hcl : ∀ u w, u ∈ X → G.Adj u w → w ≠ v → w ∈ X := fun u w hu ⟨f, hf⟩ hw =>
    hXcl hu ⟨f, by rw [Graph.induce_isLink]; exact ⟨hf, hXV hu, hf.right_mem, hw⟩⟩
  obtain ⟨w₀, hw₀H, hw₀X⟩ := Set.exists_of_ssubset hXH
  have hw₀v : w₀ ≠ v := hw₀H.2
  have hdeg : ∀ {W Y : Set α}, v ∈ W → Y.Nonempty → Y ⊂ V(G) →
      (∀ f p q, G.IsLink f p q → p ∈ Y → q ∉ Y → q = v ∧ p ∈ W) →
      2 ≤ (G.induce W).degree v := by
    intro W Y hvW hYne hYV hY
    rw [Graph.degree_eq_ncard_inc]
    refine (htec Y hYne hYV).trans (Set.ncard_le_ncard (fun f hf => ?_) (Set.toFinite _))
    obtain ⟨-, p, q, hl, hp, hq⟩ := hf
    obtain ⟨rfl, hpW⟩ := hY f p q hl hp hq
    exact ⟨p, by rw [Graph.induce_isLink]; exact ⟨hl.symm, hvW, hpW⟩⟩
  refine .cutVertex (V₁ := insert v X) (V₂ := V(G) \ X) (v := v) ?_ ?_ ?_ ⟨?_, ?_⟩ ⟨?_, ?_⟩
  · ext y
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_sdiff]
    constructor
    · rintro ((rfl | hy) | ⟨hy, -⟩)
      · exact hv
      · exact hXG hy
      · exact hy
    · intro hy
      by_cases hyX : y ∈ X
      · exact Or.inl (Or.inr hyX)
      · exact Or.inr ⟨hy, hyX⟩
  · ext y
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨rfl | hy, -, hy'⟩
      · rfl
      · exact absurd hy hy'
    · rintro rfl
      exact ⟨Or.inl rfl, hv, hvX⟩
  · intro f p q hf
    by_cases hp : p ∈ X <;> by_cases hq : q ∈ X
    · exact Or.inl ⟨Or.inr hp, Or.inr hq⟩
    · by_cases hqv : q = v
      · exact Or.inl ⟨Or.inr hp, Or.inl hqv⟩
      · exact absurd (hcl p q hp hf.adj hqv) hq
    · by_cases hpv : p = v
      · exact Or.inl ⟨Or.inl hpv, Or.inr hq⟩
      · exact absurd (hcl q p hq hf.symm.adj hpv) hp
    · exact Or.inr ⟨⟨hf.left_mem, hp⟩, ⟨hf.right_mem, hq⟩⟩
  · refine hG.induce_of_gate (Set.insert_subset hv hXG) (Set.mem_insert v X) ?_ ?_
    · rintro y z hyz (rfl | hy) hz
      · rfl
      · by_contra hyv
        exact hz (Or.inr (hcl y z hy hyz fun hzv => hz (Or.inl hzv)))
    · refine hdeg (Set.mem_insert v X) hXne (hXG.ssubset_of_ne fun h => hvX (h ▸ hv)) ?_
      intro f p q hl hp hq
      by_contra hqv
      exact hq (hcl p q hp hl.adj (fun h => hqv ⟨h, Or.inr hp⟩))
  · exact Set.ncard_lt_ncard ((Set.insert_subset hv hXG).ssubset_of_ne fun h =>
      (h ▸ hw₀H.1 : w₀ ∈ insert v X).elim hw₀v hw₀X)
  · refine hG.induce_of_gate Set.sdiff_subset ⟨hv, hvX⟩ ?_ ?_
    · rintro y z hyz ⟨hy, hyX⟩ hz
      by_contra hyv
      exact hyX (hcl z y (by by_contra h; exact hz ⟨hyz.right_mem, h⟩) hyz.symm hyv)
    · refine hdeg ⟨hv, hvX⟩ (Y := (V(G) \ {v}) \ X) ⟨w₀, hw₀H, hw₀X⟩
        ((Set.sdiff_subset.trans Set.sdiff_subset).ssubset_of_ne fun h => by
          have hvY : v ∈ (V(G) \ {v}) \ X := by rw [h]; exact hv
          exact hvY.1.2 rfl) ?_
      intro f p q hl ⟨⟨hpV, hpv⟩, hpX⟩ hq
      refine ⟨?_, hpV, hpX⟩
      by_contra hqv
      refine hq ⟨⟨hl.right_mem, hqv⟩, fun hqX => hpX ?_⟩
      exact hcl q p hqX hl.symm.adj hpv
  · exact Set.ncard_lt_ncard (Set.sdiff_subset.ssubset_of_ne fun h => by
      obtain ⟨y, hy⟩ := hXne
      have hy' : y ∈ V(G) \ X := by rw [h]; exact hXG hy
      exact hy'.2 hy)

end CombinatorialRigidity.Molecular
