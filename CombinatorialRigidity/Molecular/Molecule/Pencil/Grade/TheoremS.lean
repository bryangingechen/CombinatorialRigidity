/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.SparseCount

/-!
# Cores in every dimension

The lemmas that find a core in every dimension `d = n` (`sec:pencil-d-deficiency`,
`blueprint/src/chapter/pencil-d.tex`), with `D = bodyBarDim n`. A set `W` is *rigid at `n`* if
`def(G̃[W]) = 0` at `n`. A *core at `n`* is a set `W ⊊ V(G)` of at least two bodies, rigid at `n`,
with no body outside `W` adjacent to two bodies of `W`, and a body `r ∈ W` with
`def₂(G[W]) + def₂(G / G[W]) ≤ def₂(G)`: rigidity is read at `D`, additivity in the plane. At
`n = 3` it is the core of `Graph.IsX0Graph.exists_additiveCore` (`thm:pencil-x0-theorem-s`,
`MainComponent/CoverageTheoremS.lean`), whose proof finds it by the lemmas here at `n = 3`; they
also give the core of `Graph.IsX0Graph.exists_chain_or_core` (`thm:pencil-d-chain-or-core`,
`Grade/Chains.lean`).

A maximal set rigid at `n` that avoids at most one body, of degree at most two, is a core, by the
core bound at `n` (`lem:deficiency-core-bound-d`, `Molecular/Induction/SparseDeficiency.lean`). It
gives the core at an open ear with two or more interior bodies whose side holds a set rigid at `n`,
which is SHORT-CORE's S52 (`notes/attacks/short-core/`). The core of a graph with `def₃(G) > 0` and
no two bodies of degree two adjacent, a set of least singleton value among those rigid at `n`, is
ONE-CLASS's lemma (`notes/Phase42-design.md` §2.3); it reads the parts of a tight partition at
`n = 3`, which are rigid at every `n ≥ 3` (`lem:deficiency-rigid-higher`).

## Main results

* `Graph.IsX0Graph.exists_additiveCore_of_rigidAt`: `lem:pencil-d-maximal-rigid-core`, a maximal
  set rigid at `n` that avoids at most one body, of degree at most two, is a core at `n`.
* `Graph.IsX0Graph.exists_core_of_deficiency_three_pos`: `lem:pencil-d-core-positive-deficiency`, a
  core at every `n ≥ 3` when `def₃(G) > 0` and no two bodies of degree two are adjacent.
* `Graph.IsOpenEar.exists_additiveCoreAt_of_deficiency_induce_eq_zero`,
  `Graph.IsOpenEar.exists_additiveCoreAt_of_partitionDef_nonpos`: `lem:pencil-d-chain-core`, a core
  at `n` avoiding the first interior body of an open ear with two or more interior bodies whose side
  `V₁` holds a set of two or more bodies rigid at `n` (1), or has `s_D(V₁) ≤ 0` (2).
-/

@[expose] public section

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {α β : Type*} [Finite α] [Finite β]

/-! ## A maximal rigid set is a core -/

/-- **A maximal set rigid at `n` is a core at `n`** (`lem:pencil-d-maximal-rigid-core`): let
`D ≥ 3`, and let `G` satisfy the standing hypotheses and be sparse. Let `X₀` be a set of at most
one body, each of degree at most two and with at most one neighbour in every set rigid at `n` that
avoids `X₀`, and let `X₀` be nonempty when `def_n(G) = 0`. Let `Y` be a set of at least two bodies,
rigid at `n` and avoiding `X₀`. Then a maximal set `W` among those rigid at `n` that contain `Y` and
avoid `X₀` is a core at `n` that avoids `X₀`, with any `r ∈ W` as the body of the contraction.

A body outside `W` and `X₀`
with two neighbours in `W` would enlarge it (`Graph.deficiency_induce_insert_eq_zero`,
`lem:deficiency-add-body`); then `s(W) ≤ s(X)` for every `X ⊇ W`
(`Graph.partitionDef_induce_id_le_of_maximal_of_three_le_bodyBarDim`,
`lem:deficiency-core-bound-d`), and `Graph.deficiency_induce_add_deficiency_rigidContract_le`
(`lem:deficiency-additive-core`) gives the inequality. -/
theorem _root_.Graph.IsX0Graph.exists_additiveCore_of_rigidAt {G : Graph α β}
    (hG : G.IsX0Graph) {n : ℕ} (hD : 3 ≤ Graph.bodyBarDim n)
    (hSv : ∀ X ⊆ V(G), 2 ≤ X.ncard → 1 ≤ (G.induce X).partitionDef 2 id)
    {X₀ Y : Set α} (hX₀ : X₀.Subsingleton) (hX₀V : X₀ ⊆ V(G)) (hYX₀ : Y ⊆ V(G) \ X₀)
    (hY2 : 2 ≤ Y.ncard) (hYd : (G.induce Y).deficiency n = 0)
    (hprop : X₀ = ∅ → G.deficiency n ≠ 0) (hdeg : ∀ x ∈ X₀, G.degree x ≤ 2)
    (hattX : ∀ x ∈ X₀, ∀ W ⊆ V(G) \ X₀, 2 ≤ W.ncard → (G.induce W).deficiency n = 0 →
      ∀ c₁ ∈ W, ∀ c₂ ∈ W, G.Adj x c₁ → G.Adj x c₂ → c₁ = c₂) :
    ∃ W r, W ⊆ V(G) \ X₀ ∧ r ∈ W ∧ W ⊂ V(G) ∧ 2 ≤ W.ncard ∧ (G.induce W).deficiency n = 0 ∧
      (G.induce W).deficiency 2 + (G.rigidContract (G.induce W) r).deficiency 2 ≤
        G.deficiency 2 ∧
      ∀ u ∉ W, ∀ c₁ ∈ W, ∀ c₂ ∈ W, G.Adj u c₁ → G.Adj u c₂ → c₁ = c₂ := by
  obtain ⟨W, hYW, hWU, hWd, hmax⟩ := G.exists_maximal_deficiency_induce_eq_zero n hYX₀ hYd
  have hWV : W ⊆ V(G) := hWU.trans Set.sdiff_subset
  have hW2 : 2 ≤ W.ncard := hY2.trans (Set.ncard_le_ncard hYW (Set.toFinite _))
  obtain ⟨r, hr⟩ : W.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  have hWX₀ : Disjoint W X₀ := Set.disjoint_left.mpr fun w hw hwX₀ => (hWU hw).2 hwX₀
  have hWss : W ⊂ V(G) := by
    refine hWV.ssubset_of_ne fun hWeq => ?_
    have hX₀e : X₀ = ∅ := Set.eq_empty_of_forall_notMem fun x hx =>
      Set.disjoint_left.mp hWX₀ (hWeq ▸ hX₀V hx) hx
    apply hprop hX₀e
    rw [← Graph.induce_vertexSet G, ← hWeq]
    exact hWd
  have hattW : ∀ u ∉ W, ∀ c₁ ∈ W, ∀ c₂ ∈ W, G.Adj u c₁ → G.Adj u c₂ → c₁ = c₂ := by
    intro u hu c₁ hc₁ c₂ hc₂ h₁ h₂
    by_cases huX₀ : u ∈ X₀
    · exact hattX u huX₀ W hWU hW2 hWd c₁ hc₁ c₂ hc₂ h₁ h₂
    by_contra hne
    have hins := Graph.deficiency_induce_insert_eq_zero hD hWd hu hc₁ hc₂ hne h₁ h₂
    have := hmax (insert u W) (Set.subset_insert _ _)
      (Set.insert_subset ⟨h₁.left_mem, huX₀⟩ hWU) hins
    exact hu (this ▸ Set.mem_insert u W)
  have hmono := Graph.partitionDef_induce_id_le_of_maximal_of_three_le_bodyBarDim hD hSv ⟨r, hr⟩
    hWX₀ hWd hmax hX₀
    (fun x hx Y' hxY' => (Graph.ncard_setOf_isLink_le_degree hxY').trans (hdeg x hx))
    (fun x hx => Graph.ncard_setOf_isLink_le_one hG.simple (hattX x hx W hWU hW2 hWd))
  exact ⟨W, r, hWU, hr, hWss, hW2, hWd,
    Graph.deficiency_induce_add_deficiency_rigidContract_le hSv hWV hr hmono, hattW⟩

/-! ## A core when the deficiency at `n = 3` is positive -/

/-- **A core at every `n ≥ 3` when `def₃(G) > 0`** (`lem:pencil-d-core-positive-deficiency`): let
`n ≥ 3`, and let `G` satisfy the standing hypotheses and be sparse, with no two bodies of degree two
adjacent. If `def₃(G) > 0`, then `G` has a core at `n`. It is a set `W` of least singleton value
`s(W)` among the sets of at least two bodies rigid at `n`.

Each part of a tight partition `P` at `n = 3` is rigid at `n = 3`
(`Graph.IsTightPartition.deficiency_induce_eq_zero`, `lem:deficiency-tight-part`), so at `n`. The
singletons have value `6(|V(G)| − 1) − 5|E(G)| < 0` (the count of `lem:pencil-x0-sparse-count`),
so some part `Z` has two or more bodies, and `s(Z) < s(V(G))`, as `P` has planar value at least one
(`lem:deficiency-singleton-bound`). So `s(W) ≤ s(Z) < s(V(G))` and `W ≠ V(G)`. A set `X ⊇ W` with
`s(X) < s(W)`, of least size, would be rigid at `n` (`Graph.deficiency_induce_eq_zero_of_le`,
`lem:deficiency-core-bound-d`), against the choice of `W`. So `s(W) ≤ s(X)` for every `X ⊇ W`: no
body outside `W` has two neighbours in it (`lem:deficiency-add-body`), and
`Graph.deficiency_induce_add_deficiency_rigidContract_le` (`lem:deficiency-additive-core`) gives the
inequality. -/
theorem _root_.Graph.IsX0Graph.exists_core_of_deficiency_three_pos {G : Graph α β}
    (hG : G.IsX0Graph) {n : ℕ} (hn : 3 ≤ n)
    (hSv : ∀ X ⊆ V(G), 2 ≤ X.ncard → 1 ≤ (G.induce X).partitionDef 2 id)
    (hhubs : ∀ v w, G.degree v = 2 → G.Adj v w → 3 ≤ G.degree w)
    (hpos : 0 < G.deficiency 3) :
    ∃ W r, r ∈ W ∧ W ⊂ V(G) ∧ 2 ≤ W.ncard ∧ (G.induce W).deficiency n = 0 ∧
      (G.induce W).deficiency 2 + (G.rigidContract (G.induce W) r).deficiency 2 ≤
        G.deficiency 2 ∧
      ∀ u ∉ W, ∀ c₁ ∈ W, ∀ c₂ ∈ W, G.Adj u c₁ → G.Adj u c₂ → c₁ = c₂ := by
  have hD : 3 ≤ Graph.bodyBarDim n := by have := Graph.six_le_bodyBarDim hn; omega
  have hnn := Graph.partitionDef_induce_id_nonneg hSv
  obtain ⟨f, hf⟩ := G.exists_isTightPartition 3
  have hfv : G.partitionDef 3 f = G.deficiency 3 := hf
  -- the singletons have negative value at `n = 3`
  have hsing : G.partitionDef 3 id < 0 := by
    have hval : G.partitionDef 3 id = 6 * ((V(G).ncard : ℤ) - 1) - 5 * E(G).ncard := by
      simp only [Graph.partitionDef, Graph.numParts, Set.image_id, hG.crossingEdges_id,
        Graph.bodyBarDim_three]
      push_cast; ring
    have h1 := hG.three_mul_sub_le_two_mul_ncard
    have h2 := hG.two_mul_ncard_le_ncard_edgeSet hhubs
    have h2' : (2 : ℤ) * ({v ∈ V(G) | G.degree v = 2} : Set α).ncard ≤ E(G).ncard := by
      exact_mod_cast h2
    linarith
  -- so `f` is not injective on `V(G)`
  obtain ⟨u, hu, w, hw, hfuw, huw⟩ : ∃ u ∈ V(G), ∃ w ∈ V(G), f u = f w ∧ u ≠ w := by
    by_contra hno
    push Not at hno
    have hinj : Set.InjOn f V(G) := fun u hu w hw h => hno u hu w hw h
    have := Graph.partitionDef_comp_of_injOn (G := G) (n := 3) (f := id) (g := f)
      (by simpa using hinj)
    simp only [Function.comp_id] at this
    linarith
  set Z : Set α := {z ∈ V(G) | f z = f u} with hZ
  have hZV : Z ⊆ V(G) := fun z hz => hz.1
  have huZ : u ∈ Z := ⟨hu, rfl⟩
  have hZ2 : 2 ≤ Z.ncard := by
    have := Set.ncard_le_ncard (Set.pair_subset huZ (show w ∈ Z from ⟨hw, hfuw.symm⟩))
      (Set.toFinite _)
    rwa [Set.ncard_pair huw] at this
  have hZd := Graph.deficiency_eq_zero_of_deficiency_eq_zero_of_le (by decide) hn ⟨u, huZ⟩
    (hf.deficiency_induce_eq_zero hu)
  -- `s(Z) < s(V)`
  have hv2 : 1 ≤ G.partitionDef 2 f := by
    have := Graph.partitionDef_three_eq G f
    have : (0 : ℤ) ≤ (G.crossingEdges f).ncard := by positivity
    linarith
  have hK := Graph.partitionDef_add_partitionDef_induce_id_le (G := G) (n := 2) f hu
    (fun Y hY hne => hnn Y (hY.trans Set.sdiff_subset) hne)
  rw [← Graph.induce_vertexSet G] at hK
  -- a set of least `s` among those rigid at `n`
  obtain ⟨W, ⟨hWV, hW2, hWd⟩, hWmin⟩ := Set.exists_min_image
    {W : Set α | W ⊆ V(G) ∧ 2 ≤ W.ncard ∧ (G.induce W).deficiency n = 0}
    (fun W => (G.induce W).partitionDef 2 id) (Set.toFinite _) ⟨Z, hZV, hZ2, hZd⟩
  have hWZ := hWmin Z ⟨hZV, hZ2, hZd⟩
  obtain ⟨r, hr⟩ : W.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  have hWss : W ⊂ V(G) := by
    refine hWV.ssubset_of_ne fun hWeq => ?_
    rw [hWeq] at hWZ
    simp only [Graph.induce_vertexSet] at hWZ hK
    linarith
  -- `s(W) ≤ s(X)` for every `X ⊇ W`
  have hmono : ∀ X, W ⊆ X → X ⊆ V(G) →
      (G.induce W).partitionDef 2 id ≤ (G.induce X).partitionDef 2 id := by
    by_contra hbad
    push Not at hbad
    obtain ⟨X, ⟨hWX, hXV, hXlt⟩, hXmin⟩ := Set.exists_min_image
      {X : Set α | W ⊆ X ∧ X ⊆ V(G) ∧
        (G.induce X).partitionDef 2 id < (G.induce W).partitionDef 2 id}
      Set.ncard (Set.toFinite _) (by obtain ⟨X, h1, h2, h3⟩ := hbad; exact ⟨X, h1, h2, h3⟩)
    have hXd : (G.induce X).deficiency n = 0 :=
      Graph.deficiency_induce_eq_zero_of_le hD (fun Z hZ => hSv Z (hZ.trans hXV)) hWX
        ⟨r, hr⟩ hWd hXlt.le fun Q hWQ hQX => by
          by_contra hQ
          push Not at hQ
          have := hXmin Q ⟨hWQ, hQX.subset.trans hXV, hQ⟩
          have := Set.ncard_lt_ncard hQX (Set.toFinite _)
          omega
    have hX2 : 2 ≤ X.ncard := hW2.trans (Set.ncard_le_ncard hWX (Set.toFinite _))
    have := hWmin X ⟨hXV, hX2, hXd⟩
    linarith
  refine ⟨W, r, hr, hWss, hW2, hWd,
    Graph.deficiency_induce_add_deficiency_rigidContract_le hSv hWV hr hmono, ?_⟩
  intro x hx c₁ hc₁ c₂ hc₂ h₁ h₂
  by_contra hne
  obtain ⟨e₁, he₁⟩ := h₁
  obtain ⟨e₂, he₂⟩ := h₂
  have hne' : e₁ ≠ e₂ := by
    rintro rfl
    rcases he₁.right_eq_or_eq he₂ with h' | h'
    · exact hx (h' ▸ hc₁)
    · exact hne h'
  have hsub : ({e₁, e₂} : Set β) ⊆ {e | ∃ y ∈ W, G.IsLink e x y} := by
    rintro e (rfl | rfl)
    · exact ⟨c₁, hc₁, he₁⟩
    · exact ⟨c₂, hc₂, he₂⟩
  have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_pair hne'] at h2
  have h2' : (2 : ℤ) ≤ ({e | ∃ y ∈ W, G.IsLink e x y} : Set β).ncard := by exact_mod_cast h2
  have hins := Graph.partitionDef_two_induce_insert_id (G := G) hx
  have := hmono (insert x W) (Set.subset_insert _ _)
    (Set.insert_subset he₁.left_mem hWV)
  linarith

/-! ## A core at a long chain -/

/-- **A core at an open ear of two or more interior bodies, from a rigid set in its side**
(`lem:pencil-d-chain-core` (1)): let `D ≥ 3`, let `G` satisfy the standing hypotheses and be
sparse, and let `a − x 0 − ⋯ − x (k − 1) − b` be an open ear of `G` on `V₁` with `k ≥ 2`. If a set
`Y ⊆ V₁` of at least two bodies is rigid at `n` (`def(G̃[Y]) = 0`), then `G` has a core at `n` that
avoids `x 0`.

The neighbours of `x 0` are `a` and `x 1` (`Graph.IsOpenEar.isLink_interior`), and `x 1` lies in no
set rigid at `n` that avoids `x 0`: it would have two neighbours there
(`Graph.two_le_degree_of_isKDof_zero`, `lem:deficiency-zero-connected`), but its other neighbour is
`x 0`. So `x 0` has at most one neighbour in such a set, and
`Graph.IsX0Graph.exists_additiveCore_of_rigidAt` with `X₀ = {x 0}` gives the core. -/
theorem _root_.Graph.IsOpenEar.exists_additiveCoreAt_of_deficiency_induce_eq_zero {G : Graph α β}
    (hG : G.IsX0Graph) {n : ℕ} (hD : 3 ≤ Graph.bodyBarDim n)
    (hSv : ∀ X ⊆ V(G), 2 ≤ X.ncard → 1 ≤ (G.induce X).partitionDef 2 id)
    {V₁ : Set α} {k : ℕ} {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β}
    (hear : G.IsOpenEar V₁ x a b e) (hk : 2 ≤ k) {Y : Set α} (hYV₁ : Y ⊆ V₁)
    (hY2 : 2 ≤ Y.ncard) (hYd : (G.induce Y).deficiency n = 0) :
    ∃ W r, x ⟨0, by omega⟩ ∉ W ∧ r ∈ W ∧ W ⊂ V(G) ∧ 2 ≤ W.ncard ∧
      (G.induce W).deficiency n = 0 ∧
      (G.induce W).deficiency 2 + (G.rigidContract (G.induce W) r).deficiency 2 ≤
        G.deficiency 2 ∧
      ∀ u ∉ W, ∀ c₁ ∈ W, ∀ c₂ ∈ W, G.Adj u c₁ → G.Adj u c₂ → c₁ = c₂ := by
  have := hG.simple
  have := hG.simple.toLoopless
  set i₁ : Fin k := ⟨0, by omega⟩ with hi₁
  set i₂ : Fin k := ⟨1, by omega⟩ with hi₂
  have hV₁ : V₁ ⊆ V(G) := hear.cover ▸ Set.subset_union_left
  -- the links at `x 0` go to `a` and `x 1`
  have hl₁ : G.IsLink (e 0) (x i₁) a := by
    have := hear.isLink_first
    rw [pathVertex_eq_of_val_eq_succ a x b (i := i₁) (by simp [hi₁])] at this
    exact this.symm
  have hl₂ : G.IsLink (e 1) (x i₁) (x i₂) := by
    have := hear.isLink 1
    rwa [pathVertex_eq_of_val_eq_succ a x b (i := i₁) (by simp [hi₁]; omega),
      pathVertex_eq_of_val_eq_succ a x b (i := i₂) (by simp [hi₂]; omega)] at this
  have hnbr : ∀ c, G.Adj (x i₁) c → c = a ∨ c = x i₂ := by
    rintro c ⟨f, hf⟩
    rcases hear.isLink_interior i₁ hf with rfl | rfl
    · rw [show i₁.castSucc = 0 from Fin.ext (by simp [hi₁])] at hf
      exact Or.inl (hf.right_unique hl₁)
    · have h1 : i₁.succ = 1 := by
        ext
        simp only [Fin.val_succ, hi₁, Fin.val_one', Nat.mod_eq_of_lt (show 1 < k + 1 by omega)]
      rw [h1] at hf
      exact Or.inr (hf.right_unique hl₂)
  refine hG.exists_additiveCore_of_rigidAt hD hSv (X₀ := {x i₁}) Set.subsingleton_singleton
    (Set.singleton_subset_iff.mpr (hear.cover ▸ Or.inr ⟨i₁, rfl⟩))
    (fun y hy => ⟨hV₁ (hYV₁ hy),
      fun h => hear.notMem i₁ (Set.mem_singleton_iff.mp h ▸ hYV₁ hy)⟩) hY2 hYd
    (fun h => absurd h (Set.singleton_ne_empty _))
    (fun y hy => by rw [Set.mem_singleton_iff.mp hy, hear.degree_eq_two]) ?_ |>.imp
      fun W ⟨r, hWX₀, h⟩ => ⟨r, fun hx => (hWX₀ hx).2 rfl, h⟩
  rintro y hy W hW hW2 hWd c₁ hc₁ c₂ hc₂ h₁ h₂
  rw [Set.mem_singleton_iff] at hy
  subst hy
  -- `x 1` has at most one neighbour in `W`, so it lies outside the rigid set `W`
  have hx₂W : x i₂ ∉ W := by
    intro hx₂
    have h2 := Graph.two_le_degree_of_isKDof_zero (G := G.induce W) (n := n) (by omega)
      hWd hx₂ hW2
    have hlt := Graph.degree_induce_lt_of_adj hx₂ (fun h => (hW h).2 rfl) ⟨e 1, hl₂.symm⟩
    have := hear.degree_eq_two i₂
    omega
  have ha : ∀ c ∈ W, G.Adj (x i₁) c → c = a := fun c hc hadj =>
    (hnbr c hadj).resolve_right fun h => hx₂W (h ▸ hc)
  rw [ha c₁ hc₁ h₁, ha c₂ hc₂ h₂]

/-- **A core at an open ear of two or more interior bodies** (`lem:pencil-d-chain-core` (2)): let
`D ≥ 3`, let `G` satisfy the standing hypotheses and be sparse, and let
`a − x 0 − ⋯ − x (k − 1) − b` be an open ear of `G` on `V₁` with `k ≥ 2` and `s_D(V₁) ≤ 0`. Then
`G` has a core at `n` that avoids `x 0`.

`V₁` contains a set rigid at `n`
(`Graph.exists_deficiency_induce_eq_zero_of_partitionDef_id_nonpos`, `lem:deficiency-sparse`), which
avoids `x 0` and gives the core by
`Graph.IsOpenEar.exists_additiveCoreAt_of_deficiency_induce_eq_zero`. -/
theorem _root_.Graph.IsOpenEar.exists_additiveCoreAt_of_partitionDef_nonpos {G : Graph α β}
    (hG : G.IsX0Graph) {n : ℕ} (hD : 3 ≤ Graph.bodyBarDim n)
    (hSv : ∀ X ⊆ V(G), 2 ≤ X.ncard → 1 ≤ (G.induce X).partitionDef 2 id)
    {V₁ : Set α} {k : ℕ} {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β}
    (hear : G.IsOpenEar V₁ x a b e) (hk : 2 ≤ k) (hs : (G.induce V₁).partitionDef n id ≤ 0) :
    ∃ W r, x ⟨0, by omega⟩ ∉ W ∧ r ∈ W ∧ W ⊂ V(G) ∧ 2 ≤ W.ncard ∧
      (G.induce W).deficiency n = 0 ∧
      (G.induce W).deficiency 2 + (G.rigidContract (G.induce W) r).deficiency 2 ≤
        G.deficiency 2 ∧
      ∀ u ∉ W, ∀ c₁ ∈ W, ∀ c₂ ∈ W, G.Adj u c₁ → G.Adj u c₂ → c₁ = c₂ := by
  have hV₁2 : 2 ≤ V₁.ncard := by
    have := Set.ncard_le_ncard (Set.pair_subset hear.left_mem hear.right_mem) (Set.toFinite _)
    rwa [Set.ncard_pair hear.ne] at this
  obtain ⟨Y, hYV₁, hY2, hYd⟩ := Graph.exists_deficiency_induce_eq_zero_of_partitionDef_id_nonpos
    (hear.cover ▸ Set.subset_union_left) hV₁2 hs
  exact hear.exists_additiveCoreAt_of_deficiency_induce_eq_zero hG hD hSv hk hYV₁ hY2 hYd

end CombinatorialRigidity.Molecular
