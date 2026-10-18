/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Induction.ReducibleVertex
import CombinatorialRigidity.Mathlib.Combinatorics.Graph.Delete

/-!
# The deficiency of a sparse graph

Estimates on the values of partitions (`def:D-deficiency`) that the main-component induction uses
(`sec:main-component-sparse`), stated with `partitionDef` (`Molecular/Deficiency.lean`). For
`X ⊆ V(G)`, the *singleton value* `s_D(X) = (G.induce X).partitionDef n id` is the value
`D(|X| - 1) - (D - 1)e(X)` of the partition of `G[X]` into single vertices, and `s = s_3` is its
case `n = 2`. We write `def₂` and `def₃` for `deficiency 2` and `deficiency 3`, and `def₂(G; a, b)`
and `def₃(G; a, b)` for `deficiencyMerged 2 a b` and `deficiencyMerged 3 a b`. A set `W` is *rigid*
if `def₃(G[W]) = 0`, and `G` is *sparse* if `s(X) ≥ 1` for every `X ⊆ V(G)` with `|X| ≥ 2`; a set
`X` of at least three vertices is *tight* if `G[X]` is sparse and `s(X) = 1`.

## Main statements

* `Graph.partitionDef_le_partitionDef_id`, `Graph.partitionDef_add_partitionDef_induce_id_le`
  (`lem:deficiency-singleton-bound`): when the singleton values are nonnegative, the singletons
  bound every partition, and a part `Z` splits off with the value `s_D(Z)`.
* `Graph.partitionDef_induce_insert`, `Graph.deficiency_induce_insert_eq_zero`,
  `Graph.partitionDef_two_induce_insert_id` (`lem:deficiency-add-body`): the value after adding a
  vertex, and a vertex with two neighbours in a set of deficiency zero joins it when `D ≥ 3`.
* `Graph.exists_deficiency_induce_eq_zero_of_partitionDef_id_nonpos`,
  `Graph.one_le_partitionDef_induce_id` (`lem:deficiency-sparse`): a set of nonpositive singleton
  value contains a set of deficiency zero, so with no such set of two or more vertices, every such
  set has singleton value at least `1`.
* `Graph.exists_partitionDef_le_mergeOn`, `Graph.deficiencyMerged_eq_deficiency_of_mem`
  (`lem:deficiency-merge-rigid`): merging the parts that meet a set of deficiency zero does not
  lower the value, so two vertices of such a set have `deficiencyMerged = deficiency`.
* `Graph.deficiency_three_induce_eq_zero_of_tight` (`lem:deficiency-tight-rigid`): a tight set is
  rigid.
* `Graph.deficiency_three_induce_eq_zero_of_le`, `Graph.partitionDef_induce_id_le_of_maximal`
  (`lem:deficiency-core-bound`): a maximal rigid set `W` avoiding a set `X₀` of at most one vertex
  has `s(W) ≤ s(X)` for every `X ⊇ W`.
* `Graph.deficiency_induce_add_deficiency_rigidContract_le` (`lem:deficiency-additive-core`):
  `def₂(G[W]) + def₂(G / G[W]) ≤ def₂(G)` under that bound.
* `Graph.not_adj_and_deficiencyMerged_two_add_two_le`, `Graph.deficiencyMerged_three_add_five_le`
  (`lem:deficiency-one-body-chain`) and `Graph.deficiencyMerged_two_add_two_le`
  (`lem:deficiency-two-body-chain`): the merged deficiencies at the ends of a chain of one or two
  vertices.

`Graph.deficiencyMerged_le_deficiency` and `Graph.partitionDef_map`, which
`lem:deficiency-merge-rigid` and `lem:deficiency-additive-core` also pin, are in
`Molecular/Deficiency.lean`.
-/

open scoped Graph

namespace Graph

variable {α β : Type*}

/-! ## The singletons bound the partitions (`lem:deficiency-singleton-bound`) -/

/-- **A constant labeling has value zero** (a step of `lem:deficiency-singleton-bound`): if
`f w = f v` for every `w ∈ V(G)` and `v ∈ V(G)`, then `G.partitionDef n f = 0`. -/
lemma partitionDef_eq_zero_of_forall_eq {G : Graph α β} {n : ℕ} {f : α → α} {v : α}
    (hv : v ∈ V(G)) (hf : ∀ w ∈ V(G), f w = f v) : G.partitionDef n f = 0 := by
  rw [partitionDef_congr (g := fun _ => f v) (fun w hw => hf w hw)]
  exact partitionDef_one G n (f v) ⟨v, hv⟩

/-- **The singletons are optimal when no singleton value is negative**
(`lem:deficiency-singleton-bound`): if every nonempty `Z ⊆ V(G)` has `s_D(Z) ≥ 0`, then every
labeling `f` has value at most `s_D(V(G))`. By induction on `|V(G)|`: the part `Z₀` of a vertex `v`
splits off both partitions (`partitionDef_split_of_sides`), with the values `0` and `s_D(Z₀) ≥ 0` on
`G[Z₀]`. -/
theorem partitionDef_le_partitionDef_id [Finite α] [Finite β] {n : ℕ} :
    ∀ {G : Graph α β}, (∀ Z ⊆ V(G), Z.Nonempty → 0 ≤ (G.induce Z).partitionDef n id) →
      ∀ f : α → α, G.partitionDef n f ≤ G.partitionDef n id := by
  intro G
  induction h : V(G).ncard using Nat.strong_induction_on generalizing G with
  | _ m ih =>
  intro hS f
  rcases V(G).eq_empty_or_nonempty with hV | ⟨v, hv⟩
  · exact (partitionDef_congr (by rw [hV]; exact Set.eqOn_empty _ _)).le
  set Z₀ : Set α := {w ∈ V(G) | f w = f v} with hZ₀
  have hZ₀V : Z₀ ⊆ V(G) := fun w hw => hw.1
  have hsf : ∀ x ∈ Z₀, ∀ y ∈ V(G) \ Z₀, f x ≠ f y := by
    rintro x ⟨-, hx⟩ y ⟨hy, hyZ⟩ hxy
    exact hyZ ⟨hy, hxy ▸ hx⟩
  have hsi : ∀ x ∈ Z₀, ∀ y ∈ V(G) \ Z₀, id x ≠ id y := by
    rintro x hx y ⟨-, hyZ⟩ rfl
    exact hyZ hx
  rw [partitionDef_split_of_sides hZ₀V hsf, partitionDef_split_of_sides hZ₀V hsi]
  have h0 : (G.induce Z₀).partitionDef n f = 0 :=
    partitionDef_eq_zero_of_forall_eq (G := G.induce Z₀) (v := v) ⟨hv, rfl⟩
      fun w hw => hw.2
  have hlt : V(G.induce (V(G) \ Z₀)).ncard < m := by
    rw [← h]
    exact Set.ncard_lt_ncard (Set.sdiff_ssubset_left_iff.mpr ⟨v, hv, hv, rfl⟩)
  have hIH := ih _ hlt rfl (G := G.induce (V(G) \ Z₀)) (fun Z hZ hne => by
    have hZ' : Z ⊆ V(G) \ Z₀ := hZ
    rw [induce_induce_of_subset G hZ']
    exact hS Z (hZ'.trans Set.sdiff_subset) hne) f
  have hZ := hS Z₀ hZ₀V ⟨v, hv, rfl⟩
  linarith

/-- **A part splits off with its singleton value** (`lem:deficiency-singleton-bound`): let `Z₀` be
the part of `v ∈ V(G)` under `f`. If every nonempty set of vertices outside `Z₀` has nonnegative
singleton value, then `G.partitionDef n f + s_D(Z₀) ≤ s_D(V(G))`. -/
theorem partitionDef_add_partitionDef_induce_id_le [Finite α] [Finite β] {G : Graph α β}
    {n : ℕ} (f : α → α) {v : α} (hv : v ∈ V(G))
    (hS : ∀ Z ⊆ V(G) \ {w | f w = f v}, Z.Nonempty → 0 ≤ (G.induce Z).partitionDef n id) :
    G.partitionDef n f + (G.induce {w ∈ V(G) | f w = f v}).partitionDef n id ≤
      G.partitionDef n id := by
  set Z₀ : Set α := {w ∈ V(G) | f w = f v} with hZ₀
  have hZ₀V : Z₀ ⊆ V(G) := fun w hw => hw.1
  have hsf : ∀ x ∈ Z₀, ∀ y ∈ V(G) \ Z₀, f x ≠ f y := by
    rintro x ⟨-, hx⟩ y ⟨hy, hyZ⟩ hxy
    exact hyZ ⟨hy, hxy ▸ hx⟩
  have hsi : ∀ x ∈ Z₀, ∀ y ∈ V(G) \ Z₀, id x ≠ id y := by
    rintro x hx y ⟨-, hyZ⟩ rfl
    exact hyZ hx
  rw [partitionDef_split_of_sides hZ₀V hsf, partitionDef_split_of_sides hZ₀V hsi]
  have h0 : (G.induce Z₀).partitionDef n f = 0 :=
    partitionDef_eq_zero_of_forall_eq (G := G.induce Z₀) (v := v) ⟨hv, rfl⟩
      fun w hw => hw.2
  have hIH := partitionDef_le_partitionDef_id (n := n) (G := G.induce (V(G) \ Z₀))
    (fun Z hZ hne => by
    have hZ : Z ⊆ V(G) \ Z₀ := hZ
    rw [induce_induce_of_subset G hZ]
    refine hS Z (fun z hz => ⟨(hZ hz).1, fun hfz => (hZ hz).2 ⟨(hZ hz).1, hfz⟩⟩) hne) f
  linarith

/-! ## A set of nonpositive singleton value (`lem:deficiency-sparse`) -/

/-- **A single vertex has singleton value zero** (a step of `lem:deficiency-sparse`):
`(G.induce {v}).partitionDef n id = 0`. -/
lemma partitionDef_induce_singleton_id (G : Graph α β) (n : ℕ) (v : α) :
    (G.induce {v}).partitionDef n id = 0 :=
  partitionDef_eq_zero_of_forall_eq (G := G.induce {v}) (v := v) rfl fun w hw => by
    simpa using hw

/-- **A set of nonpositive singleton value contains a set of deficiency zero**
(`lem:deficiency-sparse`): if `X ⊆ V(G)`, `|X| ≥ 2` and `s_D(X) ≤ 0`, then some `Y ⊆ X` with
`|Y| ≥ 2` has `def(G̃[Y]) = 0`. A minimal such `Y` works: its nonempty proper subsets have
nonnegative singleton value, so a partition of `Y` with a part `Z ⊊ Y` has value at most
`s_D(Y) - s_D(Z) ≤ 0` (`partitionDef_add_partitionDef_induce_id_le`). -/
theorem exists_deficiency_induce_eq_zero_of_partitionDef_id_nonpos [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} :
    ∀ {X : Set α}, X ⊆ V(G) → 2 ≤ X.ncard → (G.induce X).partitionDef n id ≤ 0 →
      ∃ Y ⊆ X, 2 ≤ Y.ncard ∧ (G.induce Y).deficiency n = 0 := by
  intro X
  induction h : X.ncard using Nat.strong_induction_on generalizing X with
  | _ m ih =>
  intro hX hX2 hval
  by_cases hsub : ∃ Y ⊂ X, 2 ≤ Y.ncard ∧ (G.induce Y).partitionDef n id ≤ 0
  · obtain ⟨Y, hYX, hY2, hYv⟩ := hsub
    obtain ⟨Z, hZY, hZ2, hZd⟩ :=
      ih _ (h ▸ Set.ncard_lt_ncard hYX) rfl (hYX.subset.trans hX) hY2 hYv
    exact ⟨Z, hZY.trans hYX.subset, hZ2, hZd⟩
  push Not at hsub
  have hpos : ∀ Z ⊂ X, Z.Nonempty → 0 ≤ (G.induce Z).partitionDef n id := by
    intro Z hZX hZne
    rcases Nat.lt_or_ge Z.ncard 2 with hZ | hZ
    · obtain ⟨z, rfl⟩ : ∃ z, Z = {z} := Set.ncard_eq_one.mp (by
        have := (Set.ncard_pos (Set.toFinite Z)).mpr hZne; omega)
      exact (partitionDef_induce_singleton_id G n z).ge
    · exact (hsub Z hZX hZ).le
  have : Nonempty (α → α) := ⟨id⟩
  have hX2' : 2 ≤ X.ncard := by omega
  refine ⟨X, subset_rfl, hX2', le_antisymm ?_ (deficiency_nonneg _ n ?_)⟩
  · refine ciSup_le fun f => ?_
    obtain ⟨v, hv⟩ : X.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
    by_cases hall : ∀ w ∈ X, f w = f v
    · exact (partitionDef_eq_zero_of_forall_eq (G := G.induce X) hv hall).le
    push Not at hall
    obtain ⟨w, hwX, hw⟩ := hall
    have hK := partitionDef_add_partitionDef_induce_id_le (G := G.induce X) (n := n) f hv
      (fun Z hZ hZne => by
        have hZX : Z ⊆ X := hZ.trans Set.sdiff_subset
        rw [induce_induce_of_subset G hZX]
        refine hpos Z (hZX.ssubset_of_ne ?_) hZne
        rintro rfl
        exact (hZ hv).2 rfl)
    have hZ₀X : {w ∈ V(G.induce X) | f w = f v} ⊆ X := fun w hw => hw.1
    rw [induce_induce_of_subset G hZ₀X] at hK
    have := hpos _ (hZ₀X.ssubset_of_ne fun heq => hw (heq ▸ hwX).2) ⟨v, hv, rfl⟩
    linarith
  · exact Set.nonempty_of_ncard_ne_zero (s := X) (by omega)

/-- **With no set of deficiency zero, the singleton values are positive** (`lem:deficiency-sparse`):
if no `X ⊆ V(G)` with `|X| ≥ 2` has `def(G̃[X]) = 0`, then `s_D(X) ≥ 1` for every such `X`; at
`n = 2`, `G` is sparse. -/
theorem one_le_partitionDef_induce_id [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hS : ∀ X ⊆ V(G), 2 ≤ X.ncard → (G.induce X).deficiency n ≠ 0) :
    ∀ X ⊆ V(G), 2 ≤ X.ncard → 1 ≤ (G.induce X).partitionDef n id := by
  intro X hX hX2
  by_contra hlt
  obtain ⟨Y, hYX, hY2, hYd⟩ :=
    exists_deficiency_induce_eq_zero_of_partitionDef_id_nonpos (n := n) hX hX2 (by omega)
  exact hS Y (hYX.trans hX) hY2 hYd

/-! ## Merging along a set of deficiency zero (`lem:deficiency-merge-rigid`) -/

/-- **Merging along a set of deficiency zero** (`lem:deficiency-merge-rigid`): let `D ≥ 1`, and let
`W ⊆ V(G)` be nonempty with `def(G̃[W]) = 0`. Every labeling `f` has a coarsening `g`, with `W` in
one part, of at least its value. Merging the parts that meet `W` lowers the value by at most the
value of `f` on `G[W]` (`partitionDef_merge`), which is at most zero. -/
theorem exists_partitionDef_le_mergeOn [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hn : 1 ≤ bodyBarDim n) {W : Set α} (hW : W ⊆ V(G)) (hdef : (G.induce W).deficiency n = 0)
    (f : α → α) (hWne : W.Nonempty) :
    ∃ g : α → α, (∀ u w, f u = f w → g u = g w) ∧ (∀ u ∈ W, ∀ w ∈ W, g u = g w) ∧
      G.partitionDef n f ≤ G.partitionDef n g := by
  classical
  obtain ⟨w₀, hw₀⟩ := hWne
  set c : α → α := fun y => if y ∈ f '' W then f w₀ else y with hc
  refine ⟨c ∘ f, fun u w h => by simp only [Function.comp, h], fun u hu w hw => ?_, ?_⟩
  · change c (f u) = c (f w)
    simp only [hc]
    rw [ite_eq_left (Set.mem_image_of_mem f hu), ite_eq_left (Set.mem_image_of_mem f hw)]
  have hS : f '' W ⊆ f '' V(G) := Set.image_mono hW
  have hmerge := partitionDef_merge (G := G) (n := n) (f := f) (c := c) hS
    (Set.mem_image_of_mem f hw₀) (fun y hy => by simp only [hc]; rw [ite_eq_left hy])
    (fun y hy => by simp only [hc]; rw [ite_eq_right hy])
  have hval : (G.induce W).partitionDef n f ≤ 0 := hdef ▸ partitionDef_le_deficiency _ n f
  have hsub : (G.induce W).crossingEdges f ⊆ G.crossingEdgesWithin f (f '' W) := by
    rintro e ⟨-, x, y, hl, hne⟩
    rw [induce_isLink] at hl
    exact ⟨hl.1.edge_mem, x, y, hl.1, ⟨x, hl.2.1, rfl⟩, ⟨y, hl.2.2, rfl⟩, hne⟩
  have hcard := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hD : (1 : ℤ) ≤ bodyBarDim n := by exact_mod_cast hn
  have hmul : ((bodyBarDim n : ℤ) - 1) * ((G.induce W).crossingEdges f).ncard ≤
      ((bodyBarDim n : ℤ) - 1) * (G.crossingEdgesWithin f (f '' W)).ncard :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) (by linarith)
  rw [hmerge]
  rw [Graph.partitionDef, Graph.numParts, Graph.vertexSet_induce] at hval
  linarith

/-- **Two vertices of a set of deficiency zero** (`lem:deficiency-merge-rigid`): let `D ≥ 1`, and
let `Y ⊆ V(G)` have `def(G̃[Y]) = 0`. For `a, b ∈ Y`, `deficiencyMerged n a b = deficiency n`:
merging a partition attaining `def(G̃)` along `Y` (`exists_partitionDef_le_mergeOn`) puts `a` and
`b` in one part, and `deficiencyMerged_le_deficiency` is the other bound. -/
theorem deficiencyMerged_eq_deficiency_of_mem [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hn : 1 ≤ bodyBarDim n) {Y : Set α} (hY : Y ⊆ V(G)) (hdef : (G.induce Y).deficiency n = 0)
    {a b : α} (ha : a ∈ Y) (hb : b ∈ Y) : G.deficiencyMerged n a b = G.deficiency n := by
  refine le_antisymm (G.deficiencyMerged_le_deficiency n a b) ?_
  obtain ⟨f, hf⟩ := G.exists_isTightPartition n
  obtain ⟨g, -, hgY, hfg⟩ := exists_partitionDef_le_mergeOn hn hY hdef f ⟨a, ha⟩
  calc G.deficiency n = G.partitionDef n f := hf.symm
    _ ≤ G.partitionDef n g := hfg
    _ ≤ G.deficiencyMerged n a b := G.partitionDef_le_deficiencyMerged n (hgY a ha b hb)

/-! ## Two facts on values -/

/-- **The value at `n = 3` from the value at `n = 2`** (a step of `lem:deficiency-tight-rigid`):
`val₃(f) = 2 val₂(f) - d(f)`, with `d(f)` the number of edges across `f`, as `D = 6` at `n = 3` and
`D = 3` at `n = 2`. -/
lemma partitionDef_three_eq (G : Graph α β) (f : α → α) :
    G.partitionDef 3 f = 2 * G.partitionDef 2 f - (G.crossingEdges f).ncard := by
  simp only [partitionDef, bodyBarDim_two, bodyBarDim_three]
  push_cast
  ring

/-- **Positive singleton values on the larger sets give nonnegative ones** (a step of
`lem:deficiency-tight-rigid`): if every `Z ⊆ X` with `|Z| ≥ 2` has `s_D(Z) ≥ 1`, then every nonempty
`Z ⊆ X` has `s_D(Z) ≥ 0`, as a single vertex has singleton value zero
(`partitionDef_induce_singleton_id`). -/
lemma partitionDef_induce_id_nonneg [Finite α] {G : Graph α β} {n : ℕ} {X : Set α}
    (hSv : ∀ Z ⊆ X, 2 ≤ Z.ncard → 1 ≤ (G.induce Z).partitionDef n id) :
    ∀ Z ⊆ X, Z.Nonempty → 0 ≤ (G.induce Z).partitionDef n id := by
  intro Z hZ hne
  rcases Nat.lt_or_ge Z.ncard 2 with h | h
  · obtain ⟨z, rfl⟩ : ∃ z, Z = {z} := Set.ncard_eq_one.mp (by
      have := (Set.ncard_pos (Set.toFinite Z)).mpr hne; omega)
    exact (partitionDef_induce_singleton_id G n z).ge
  · exact (hSv Z hZ h).trans' (by norm_num)

/-! ## Adding one vertex (`lem:deficiency-add-body`) -/

/-- **The edges of `G[S]` across a labeling** (a step of `lem:deficiency-add-body`): an edge of `G`
with both ends in `S` whose ends have different labels under `g`. -/
lemma mem_crossingEdges_induce {G : Graph α β} {S : Set α} {g : α → α} {e : β} :
    e ∈ (G.induce S).crossingEdges g ↔ ∃ x y, G.IsLink e x y ∧ x ∈ S ∧ y ∈ S ∧ g x ≠ g y := by
  constructor
  · rintro ⟨-, x, y, hl, hne⟩
    rw [induce_isLink] at hl
    exact ⟨x, y, hl.1, hl.2.1, hl.2.2, hne⟩
  · rintro ⟨x, y, hl, hx, hy, hne⟩
    have hl' : (G.induce S).IsLink e x y := by rw [induce_isLink]; exact ⟨hl, hx, hy⟩
    exact ⟨hl'.edge_mem, x, y, hl', hne⟩

open Classical in
/-- **Adding one vertex** (`lem:deficiency-add-body`): for `u ∉ X` and a labeling `g`,
`val_{G[X ∪ u]}(g) = val_{G[X]}(g) + D·[g u is a new label] - (D - 1)·t`, where `t` is the number of
edges from `u` to the vertices of `X` with a label other than `g u`. -/
theorem partitionDef_induce_insert [Finite α] [Finite β] {G : Graph α β} {n : ℕ} {X : Set α}
    {u : α} (huX : u ∉ X) (g : α → α) :
    (G.induce (insert u X)).partitionDef n g =
      (G.induce X).partitionDef n g + (if g u ∈ g '' X then 0 else (bodyBarDim n : ℤ)) -
        ((bodyBarDim n : ℤ) - 1) * ({e | ∃ y ∈ X, G.IsLink e u y ∧ g y ≠ g u}).ncard := by
  set T : Set β := {e | ∃ y ∈ X, G.IsLink e u y ∧ g y ≠ g u} with hT
  have hce : (G.induce (insert u X)).crossingEdges g = (G.induce X).crossingEdges g ∪ T := by
    ext e
    rw [Set.mem_union, mem_crossingEdges_induce, mem_crossingEdges_induce]
    constructor
    · rintro ⟨x, y, hl, hx, hy, hne⟩
      rcases hx with rfl | hx
      · rcases hy with rfl | hy
        · exact absurd rfl hne
        · exact Or.inr ⟨y, hy, hl, Ne.symm hne⟩
      · rcases hy with rfl | hy
        · exact Or.inr ⟨x, hx, hl.symm, hne⟩
        · exact Or.inl ⟨x, y, hl, hx, hy, hne⟩
    · rintro (⟨x, y, hl, hx, hy, hne⟩ | ⟨y, hy, hl, hne⟩)
      · exact ⟨x, y, hl, Or.inr hx, Or.inr hy, hne⟩
      · exact ⟨u, y, hl, Or.inl rfl, Or.inr hy, Ne.symm hne⟩
  have hdisj : Disjoint ((G.induce X).crossingEdges g) T := by
    rw [Set.disjoint_left]
    rintro e he ⟨y, -, hl, -⟩
    obtain ⟨x, x', hl', hx, hx', -⟩ := mem_crossingEdges_induce.mp he
    rcases hl.left_eq_or_eq hl' with h | h
    · exact huX (h ▸ hx)
    · exact huX (h ▸ hx')
  have hcard : ((G.induce (insert u X)).crossingEdges g).ncard =
      ((G.induce X).crossingEdges g).ncard + T.ncard := by
    rw [hce, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
  have hparts : ((G.induce (insert u X)).numParts g : ℤ) =
      (G.induce X).numParts g + (if g u ∈ g '' X then 0 else 1) := by
    simp only [numParts, vertexSet_induce, Set.image_insert_eq]
    split_ifs with h
    · rw [Set.insert_eq_of_mem h]; simp
    · rw [Set.ncard_insert_of_notMem h (Set.toFinite _)]; push_cast; ring
  simp only [partitionDef]
  rw [hcard, hparts]
  split_ifs <;> push_cast <;> ring

/-- **The singleton value after adding one vertex** (`lem:deficiency-add-body`): for `u ∉ Y`,
`s(Y ∪ u) = s(Y) + 3 - 2t`, with `t` the number of edges from `u` into `Y`
(`partitionDef_induce_insert` at `n = 2` and the singletons). -/
theorem partitionDef_two_induce_insert_id [Finite α] [Finite β] {G : Graph α β}
    {u : α} {Y : Set α} (huY : u ∉ Y) :
    (G.induce (insert u Y)).partitionDef 2 id =
      (G.induce Y).partitionDef 2 id + 3 - 2 * ({e | ∃ y ∈ Y, G.IsLink e u y} : Set β).ncard := by
  rw [partitionDef_induce_insert (n := 2) huY id, ite_eq_right (by simpa using huY),
    bodyBarDim_two]
  have hset : ({e | ∃ y ∈ Y, G.IsLink e u y ∧ id y ≠ id u} : Set β) =
      {e | ∃ y ∈ Y, G.IsLink e u y} := by
    ext e
    exact ⟨fun ⟨y, hy, hl, _⟩ => ⟨y, hy, hl⟩,
      fun ⟨y, hy, hl⟩ => ⟨y, hy, hl, fun h' => huY ((show y = u from h') ▸ hy)⟩⟩
  rw [hset]; push_cast; ring

/-- **A vertex with two neighbours in a set of deficiency zero joins it**
(`lem:deficiency-add-body`): let `D ≥ 3` and `def(G̃[W]) = 0`, and let `u ∉ W` be adjacent to
distinct `c₁, c₂ ∈ W`. Then `def(G̃[W ∪ u]) = 0`: a labeling under which `u` shares its label with a
vertex of `W` has value at most its value on `G[W]`, and one with `u` alone has both edges to `c₁`
and `c₂` across, so value at most `D - 2(D - 1) < 0`. -/
theorem deficiency_induce_insert_eq_zero [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hn : 3 ≤ bodyBarDim n) {W : Set α} (hdef : (G.induce W).deficiency n = 0) {u c₁ c₂ : α}
    (huW : u ∉ W) (hc₁ : c₁ ∈ W) (hc₂ : c₂ ∈ W) (hne : c₁ ≠ c₂) (h₁ : G.Adj u c₁)
    (h₂ : G.Adj u c₂) : (G.induce (insert u W)).deficiency n = 0 := by
  have : Nonempty (α → α) := ⟨id⟩
  refine le_antisymm (ciSup_le fun f => ?_) (deficiency_nonneg _ n ⟨u, Or.inl rfl⟩)
  rw [partitionDef_induce_insert (n := n) huW f]
  have hW : (G.induce W).partitionDef n f ≤ 0 := hdef ▸ partitionDef_le_deficiency _ n f
  have hD : (3 : ℤ) ≤ bodyBarDim n := by exact_mod_cast hn
  split_ifs with h
  · have : (0 : ℤ) ≤ ((bodyBarDim n : ℤ) - 1) *
        ({e | ∃ y ∈ W, G.IsLink e u y ∧ f y ≠ f u}).ncard :=
      mul_nonneg (by linarith) (by positivity)
    linarith
  · obtain ⟨e₁, he₁⟩ := h₁
    obtain ⟨e₂, he₂⟩ := h₂
    have hne' : e₁ ≠ e₂ := by
      rintro rfl
      rcases he₁.right_eq_or_eq he₂ with h' | h'
      · exact huW (h' ▸ hc₁)
      · exact hne h'
    have hsub : ({e₁, e₂} : Set β) ⊆ {e | ∃ y ∈ W, G.IsLink e u y ∧ f y ≠ f u} := by
      rintro e (rfl | rfl)
      · exact ⟨c₁, hc₁, he₁, fun h' => h ⟨c₁, hc₁, h'⟩⟩
      · exact ⟨c₂, hc₂, he₂, fun h' => h ⟨c₂, hc₂, h'⟩⟩
    have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_pair hne'] at h2
    have h2' : (2 : ℤ) ≤ ({e | ∃ y ∈ W, G.IsLink e u y ∧ f y ≠ f u} : Set β).ncard := by
      exact_mod_cast h2
    nlinarith

/-- **A maximal set of deficiency zero between `Y` and `U`**: if `Y ⊆ U` and `def(G̃[Y]) = 0`, then
some `W` with `Y ⊆ W ⊆ U` and `def(G̃[W]) = 0` is maximal among such sets. -/
theorem exists_maximal_deficiency_induce_eq_zero [Finite α] (G : Graph α β) (n : ℕ)
    {Y U : Set α} (hYU : Y ⊆ U) (hY : (G.induce Y).deficiency n = 0) :
    ∃ W, Y ⊆ W ∧ W ⊆ U ∧ (G.induce W).deficiency n = 0 ∧
      ∀ W', W ⊆ W' → W' ⊆ U → (G.induce W').deficiency n = 0 → W' = W := by
  obtain ⟨W, ⟨hYW, hWU, hWd⟩, hmax⟩ := Set.exists_max_image
    {W : Set α | Y ⊆ W ∧ W ⊆ U ∧ (G.induce W).deficiency n = 0} Set.ncard (Set.toFinite _)
    ⟨Y, subset_rfl, hYU, hY⟩
  refine ⟨W, hYW, hWU, hWd, fun W' hWW' hW'U hW'd => ?_⟩
  exact (Set.eq_of_subset_of_ncard_le hWW' (hmax W' ⟨hYW.trans hWW', hW'U, hW'd⟩)
    (Set.toFinite _)).symm

/-! ## Relabelling -/

/-- **The value depends only on the partition** (a step of `lem:deficiency-one-body-chain`):
labelings `f` and `g` that give the same pairs of vertices of `V(G)` the same label have the same
value. -/
lemma partitionDef_eq_of_forall_iff {G : Graph α β} {n : ℕ} {f g : α → α}
    (h : ∀ u ∈ V(G), ∀ w ∈ V(G), f u = f w ↔ g u = g w) :
    G.partitionDef n f = G.partitionDef n g := by
  classical
  set ι : α → α := fun ℓ => if hh : ∃ u ∈ V(G), f u = ℓ then g hh.choose else ℓ with hι
  have hιf : ∀ u ∈ V(G), ι (f u) = g u := by
    intro u hu
    have hh : ∃ w ∈ V(G), f w = f u := ⟨u, hu, rfl⟩
    simp only [hι, dite_eq_left hh]
    exact (h _ hh.choose_spec.1 u hu).mp hh.choose_spec.2
  have hinj : Set.InjOn ι (f '' V(G)) := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨w, hw, rfl⟩ huw
    rw [hιf u hu, hιf w hw] at huw
    exact (h u hu w hw).mpr huw
  rw [← partitionDef_comp_of_injOn (g := ι) hinj]
  exact partitionDef_congr fun u hu => hιf u hu

/-- **Gluing two labelings** (a step of `lem:deficiency-one-body-chain`): some labeling `h`
separates `X` from `V(G) \ X`, gives two vertices of `X` the same label exactly when `g` does, and
two vertices of `V(G) \ X` the same label exactly when `f` does. -/
lemma exists_glue (G : Graph α β) (X : Set α) (g f : α → α) :
    ∃ h : α → α, (∀ x ∈ X, ∀ y ∈ V(G) \ X, h x ≠ h y) ∧
      (∀ u ∈ X, ∀ w ∈ X, h u = h w ↔ g u = g w) ∧
      (∀ u ∈ V(G) \ X, ∀ w ∈ V(G) \ X, h u = h w ↔ f u = f w) := by
  classical
  set σ : α → α := fun ℓ => if hh : ∃ u ∈ X, g u = ℓ then hh.choose else ℓ with hσ
  set τ : α → α := fun ℓ => if hh : ∃ u ∈ V(G) \ X, f u = ℓ then hh.choose else ℓ with hτ
  have hσm : ∀ u ∈ X, σ (g u) ∈ X ∧ g (σ (g u)) = g u := by
    intro u hu
    have hh : ∃ w ∈ X, g w = g u := ⟨u, hu, rfl⟩
    simp only [hσ, dite_eq_left hh]
    exact hh.choose_spec
  have hτm : ∀ u ∈ V(G) \ X, τ (f u) ∈ V(G) \ X ∧ f (τ (f u)) = f u := by
    intro u hu
    have hh : ∃ w ∈ V(G) \ X, f w = f u := ⟨u, hu, rfl⟩
    simp only [hτ, dite_eq_left hh]
    exact hh.choose_spec
  refine ⟨fun w => if w ∈ X then σ (g w) else τ (f w), ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    simp only [ite_eq_left hx, ite_eq_right hy.2] at hxy
    exact (hτm y hy).1.2 (hxy ▸ (hσm x hx).1)
  · intro u hu w hw
    simp only [ite_eq_left hu, ite_eq_left hw]
    refine ⟨fun h' => ?_, fun h' => by rw [h']⟩
    rw [← (hσm u hu).2, ← (hσm w hw).2, h']
  · intro u hu w hw
    simp only [ite_eq_right hu.2, ite_eq_right hw.2]
    refine ⟨fun h' => ?_, fun h' => by rw [h']⟩
    rw [← (hτm u hu).2, ← (hτm w hw).2, h']

/-! ## A tight set is rigid (`lem:deficiency-tight-rigid`) -/

/-- **A tight set is rigid** (`lem:deficiency-tight-rigid`): let `X` have at least three vertices,
let `s(Z) ≥ 1` for every `Z ⊆ X` with `|Z| ≥ 2`, and let `s(X) ≤ 1`. Then `def₃(G[X]) = 0`. A
partition with a part `Z`, `2 ≤ |Z| < |X|`, has planar value at most `s(X) - s(Z) ≤ 0`, so its value
at `n = 3` is at most `0` (`partitionDef_three_eq`). For the singletons, `s(X) ≤ 1` gives
`2e(X) ≥ 3|X| - 4 ≥ 5`, so their value at `n = 3`, `2s(X) - e(X)`, is negative. The partition `{X}`
has value zero. -/
theorem deficiency_three_induce_eq_zero_of_tight [Finite α] [Finite β] {G : Graph α β}
    {X : Set α} (hSv : ∀ Z ⊆ X, 2 ≤ Z.ncard → 1 ≤ (G.induce Z).partitionDef 2 id)
    (hX3 : 3 ≤ X.ncard) (hX1 : (G.induce X).partitionDef 2 id ≤ 1) :
    (G.induce X).deficiency 3 = 0 := by
  have : Nonempty (α → α) := ⟨id⟩
  have hnn := partitionDef_induce_id_nonneg hSv
  refine le_antisymm (ciSup_le fun f => ?_) (deficiency_nonneg _ 3
    (Set.nonempty_of_ncard_ne_zero (s := X) (by omega)))
  by_cases hinj : Set.InjOn f X
  · -- all singletons
    have hid : (G.induce X).partitionDef 3 f = (G.induce X).partitionDef 3 id := by
      have := partitionDef_comp_of_injOn (G := G.induce X) (n := 3) (f := id) (g := f)
        (by simpa using hinj)
      simpa using this
    have hid2 : (G.induce X).partitionDef 2 f = (G.induce X).partitionDef 2 id := by
      have := partitionDef_comp_of_injOn (G := G.induce X) (n := 2) (f := id) (g := f)
        (by simpa using hinj)
      simpa using this
    rw [hid]
    have h3 := partitionDef_three_eq (G.induce X) id
    have hp : (G.induce X).numParts id = X.ncard := by simp [numParts]
    have h2 : (G.induce X).partitionDef 2 id =
        3 * ((X.ncard : ℤ) - 1) - 2 * ((G.induce X).crossingEdges id).ncard := by
      simp only [partitionDef, bodyBarDim_two, hp]; push_cast; ring
    have : (5 : ℤ) ≤ 2 * ((G.induce X).crossingEdges id).ncard := by
      have : (3 : ℤ) ≤ X.ncard := by exact_mod_cast hX3
      linarith
    linarith
  · simp only [Set.InjOn, not_forall] at hinj
    obtain ⟨u, hu, w, hw, hfuw, huw⟩ := hinj
    by_cases hall : ∀ y ∈ X, f y = f u
    · exact (partitionDef_eq_zero_of_forall_eq (G := G.induce X) hu hall).le
    push Not at hall
    obtain ⟨y, hyX, hy⟩ := hall
    have hZ₀X : {z ∈ V(G.induce X) | f z = f u} ⊆ X := fun z hz => hz.1
    have hK := partitionDef_add_partitionDef_induce_id_le (G := G.induce X) (n := 2) f hu
      (fun Z hZ hZne => by
        have hZX : Z ⊆ X := hZ.trans Set.sdiff_subset
        rw [induce_induce_of_subset G hZX]
        exact hnn Z hZX hZne)
    rw [induce_induce_of_subset G hZ₀X] at hK
    have hZ₀2 : 2 ≤ ({z ∈ V(G.induce X) | f z = f u}).ncard := by
      have hsub : ({u, w} : Set α) ⊆ {z ∈ V(G.induce X) | f z = f u} := by
        rintro z (rfl | rfl)
        · exact ⟨hu, rfl⟩
        · exact ⟨hw, hfuw.symm⟩
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      rwa [Set.ncard_pair huw] at this
    have hZ₀ := hSv _ hZ₀X hZ₀2
    have h3 := partitionDef_three_eq (G.induce X) f
    have : (0 : ℤ) ≤ ((G.induce X).crossingEdges f).ncard := by positivity
    linarith

/-! ## The core bound (`lem:deficiency-core-bound`) -/

/-- **A set above a rigid set with no smaller singleton value is rigid**
(`lem:deficiency-core-bound` (1)): let `s(Z) ≥ 1` for every `Z ⊆ Y` with `|Z| ≥ 2`, let `W ⊆ Y` be
nonempty and rigid, let `s(Y) ≤ s(W)`, and let `s(W) ≤ s(Q)` for every `Q` with `W ⊆ Q ⊊ Y`. Then
`def₃(G[Y]) = 0`. Merging the parts of a partition that meet `W` does not lower its value
(`exists_partitionDef_le_mergeOn`), and the part `Q ⊇ W` of the result bounds its planar value by
`s(Y) - s(Q) ≤ 0` if `Q ≠ Y`. -/
theorem deficiency_three_induce_eq_zero_of_le [Finite α] [Finite β] {G : Graph α β}
    {W Y : Set α} (hSv : ∀ Z ⊆ Y, 2 ≤ Z.ncard → 1 ≤ (G.induce Z).partitionDef 2 id)
    (hWY : W ⊆ Y) (hWne : W.Nonempty) (hWd : (G.induce W).deficiency 3 = 0)
    (hY : (G.induce Y).partitionDef 2 id ≤ (G.induce W).partitionDef 2 id)
    (hmin : ∀ Q, W ⊆ Q → Q ⊂ Y →
      (G.induce W).partitionDef 2 id ≤ (G.induce Q).partitionDef 2 id) :
    (G.induce Y).deficiency 3 = 0 := by
  have : Nonempty (α → α) := ⟨id⟩
  have hnn := partitionDef_induce_id_nonneg hSv
  obtain ⟨w₀, hw₀⟩ := hWne
  refine le_antisymm (ciSup_le fun f => ?_) (deficiency_nonneg _ 3 ⟨w₀, hWY hw₀⟩)
  have hWd' : ((G.induce Y).induce W).deficiency 3 = 0 := by
    rwa [induce_induce_of_subset G hWY]
  obtain ⟨g, -, hgW, hfg⟩ := exists_partitionDef_le_mergeOn (G := G.induce Y) (by decide)
    hWY hWd' f ⟨w₀, hw₀⟩
  refine hfg.trans ?_
  have hQY : {z ∈ V(G.induce Y) | g z = g w₀} ⊆ Y := fun z hz => hz.1
  have hWQ : W ⊆ {z ∈ V(G.induce Y) | g z = g w₀} := fun z hz => ⟨hWY hz, hgW z hz w₀ hw₀⟩
  by_cases hall : ∀ z ∈ Y, g z = g w₀
  · exact (partitionDef_eq_zero_of_forall_eq (G := G.induce Y) (hWY hw₀) hall).le
  push Not at hall
  obtain ⟨z, hzY, hz⟩ := hall
  have hK := partitionDef_add_partitionDef_induce_id_le (G := G.induce Y) (n := 2) g
    (hWY hw₀) (fun Z hZ hZne => by
      have hZY : Z ⊆ Y := hZ.trans Set.sdiff_subset
      rw [induce_induce_of_subset G hZY]
      exact hnn Z hZY hZne)
  rw [induce_induce_of_subset G hQY] at hK
  have hQ := hmin _ hWQ (hQY.ssubset_of_ne fun heq => hz (heq ▸ hzY).2)
  have h3 := partitionDef_three_eq (G.induce Y) g
  have : (0 : ℤ) ≤ ((G.induce Y).crossingEdges g).ncard := by positivity
  linarith

/-- **A maximal rigid set bounds the singleton values above it** (`lem:deficiency-core-bound` (2)):
let `G` be sparse, let `W` be nonempty and rigid, and let `X₀` be empty or one vertex outside `W`
that sends at most two edges into each set avoiding it and at most one into `W`. If `W` is maximal
among the rigid sets that contain it and avoid `X₀`, then `s(W) ≤ s(X)` for every `X` with
`W ⊆ X ⊆ V(G)`. The proof takes a smallest counterexample `X` and applies
`deficiency_three_induce_eq_zero_of_le` to `X`, or to `X` less the vertex of `X₀`
(`partitionDef_induce_insert`). -/
theorem partitionDef_induce_id_le_of_maximal [Finite α] [Finite β] {G : Graph α β}
    (hSv : ∀ X ⊆ V(G), 2 ≤ X.ncard → 1 ≤ (G.induce X).partitionDef 2 id)
    {W X₀ : Set α} (hWne : W.Nonempty) (hWX₀ : Disjoint W X₀)
    (hWd : (G.induce W).deficiency 3 = 0)
    (hmax : ∀ W', W ⊆ W' → W' ⊆ V(G) \ X₀ → (G.induce W').deficiency 3 = 0 → W' = W)
    (hX₀ : X₀.Subsingleton)
    (hdeg : ∀ x ∈ X₀, ∀ Y : Set α, x ∉ Y → ({e | ∃ y ∈ Y, G.IsLink e x y} : Set β).ncard ≤ 2)
    (hatt : ∀ x ∈ X₀, ({e | ∃ y ∈ W, G.IsLink e x y} : Set β).ncard ≤ 1) :
    ∀ X, W ⊆ X → X ⊆ V(G) →
      (G.induce W).partitionDef 2 id ≤ (G.induce X).partitionDef 2 id := by
  intro X
  induction h : X.ncard using Nat.strong_induction_on generalizing X with
  | _ m ih =>
  intro hWX hXV
  by_contra hlt
  push Not at hlt
  have hsub : ∀ Z ⊆ X, 2 ≤ Z.ncard → 1 ≤ (G.induce Z).partitionDef 2 id :=
    fun Z hZ => hSv Z (hZ.trans hXV)
  have hIH : ∀ Q, W ⊆ Q → Q ⊂ X →
      (G.induce W).partitionDef 2 id ≤ (G.induce Q).partitionDef 2 id := fun Q hWQ hQX =>
    ih _ (h ▸ Set.ncard_lt_ncard hQX) Q rfl hWQ (hQX.subset.trans hXV)
  have hWX' : W ≠ X := by rintro rfl; exact lt_irrefl _ hlt
  -- the id-value of adding one body
  have hins : ∀ (u : α) (Y : Set α), u ∉ Y → (G.induce (insert u Y)).partitionDef 2 id =
      (G.induce Y).partitionDef 2 id + 3 - 2 * ({e | ∃ y ∈ Y, G.IsLink e u y} : Set β).ncard := by
    intro u Y huY
    rw [partitionDef_induce_insert (n := 2) huY id, ite_eq_right (by simpa using huY),
      bodyBarDim_two]
    have hset : ({e | ∃ y ∈ Y, G.IsLink e u y ∧ id y ≠ id u} : Set β) =
        {e | ∃ y ∈ Y, G.IsLink e u y} := by
      ext e
      exact ⟨fun ⟨y, hy, hl, _⟩ => ⟨y, hy, hl⟩,
        fun ⟨y, hy, hl⟩ => ⟨y, hy, hl, fun h' => huY ((show y = u from h') ▸ hy)⟩⟩
    rw [hset]; push_cast; ring
  by_cases hx : ∃ x ∈ X₀, x ∈ X
  · obtain ⟨x, hxX₀, hxX⟩ := hx
    set Y := X \ {x} with hYdef
    have hxY : x ∉ Y := fun h' => h'.2 rfl
    have hXY : X = insert x Y := by
      rw [hYdef, Set.insert_sdiff_singleton, Set.insert_eq_of_mem hxX]
    have hWY : W ⊆ Y := fun w hw => ⟨hWX hw, fun h' => Set.disjoint_left.mp hWX₀ hw (h' ▸ hxX₀)⟩
    have hYX : Y ⊂ X := hXY ▸ Set.ssubset_insert hxY
    have hval := hins x Y hxY
    rw [← hXY] at hval
    by_cases hYW : Y = W
    · have := hatt x hxX₀
      rw [← hYW] at this
      have : ((({e | ∃ y ∈ Y, G.IsLink e x y} : Set β).ncard : ℕ) : ℤ) ≤ 1 := by exact_mod_cast this
      rw [hYW] at hval this
      linarith
    · have hYle := hIH Y hWY hYX
      have hdg : ((({e | ∃ y ∈ Y, G.IsLink e x y} : Set β).ncard : ℕ) : ℤ) ≤ 2 := by
        exact_mod_cast hdeg x hxX₀ Y hxY
      have hYd : (G.induce Y).deficiency 3 = 0 :=
        deficiency_three_induce_eq_zero_of_le (fun Z hZ => hsub Z (hZ.trans hYX.subset)) hWY
          hWne hWd (by linarith) fun Q hWQ hQY => hIH Q hWQ (hQY.trans hYX)
      have hYsub : Y ⊆ V(G) \ X₀ := fun y hy => ⟨hXV hy.1, fun hyX₀ =>
        hy.2 (hX₀ hyX₀ hxX₀)⟩
      exact hYW (hmax Y hWY hYsub hYd)
  · push Not at hx
    have hXd : (G.induce X).deficiency 3 = 0 :=
      deficiency_three_induce_eq_zero_of_le hsub hWX hWne hWd hlt.le hIH
    exact hWX' (hmax X hWX (fun y hy => ⟨hXV hy, fun hyX₀ => hx y hyX₀ hy⟩) hXd).symm

/-! ## The additive core (`lem:deficiency-additive-core`) -/

/-- **Deleting the edges of `G[W]` keeps the value of a labeling constant on `W`** (a step of
`lem:deficiency-additive-core`): none of the deleted edges is across the labeling. -/
lemma partitionDef_deleteEdges_induce_eq {G : Graph α β} {n : ℕ} {W : Set α} {f : α → α}
    (hf : ∀ u ∈ W, ∀ w ∈ W, f u = f w) :
    (G.deleteEdges E(G.induce W)).partitionDef n f = G.partitionDef n f := by
  have hce : (G.deleteEdges E(G.induce W)).crossingEdges f = G.crossingEdges f := by
    ext e
    simp only [crossingEdges, Set.mem_ofPred_eq, deleteEdges_isLink, edgeSet_deleteEdges,
      Set.mem_sdiff]
    constructor
    · rintro ⟨⟨he, -⟩, x, y, ⟨hl, -⟩, hne⟩
      exact ⟨he, x, y, hl, hne⟩
    · rintro ⟨he, x, y, hl, hne⟩
      have hnot : e ∉ E(G.induce W) := by
        rintro ⟨x', y', hl', hx', hy'⟩
        obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hl.eq_and_eq_or_eq_and_eq hl'
        · exact hne (hf _ hx' _ hy')
        · exact hne (hf _ hy' _ hx')
      exact ⟨⟨he, hnot⟩, x, y, ⟨hl, hnot⟩, hne⟩
  simp only [partitionDef, numParts, vertexSet_deleteEdges, hce]

/-- **The planar deficiencies of a core and its contraction** (`lem:deficiency-additive-core` (2)):
let `G` be sparse, let `r ∈ W ⊆ V(G)`, and let `s(W) ≤ s(X)` for every `X` with `W ⊆ X ⊆ V(G)`. Then
`def₂(G[W]) + def₂(G / G[W]) ≤ def₂(G)`, where `G / G[W]` contracts `G[W]` to `r`. The singletons
are optimal, so `def₂(G[W]) ≤ s(W)` (`partitionDef_le_partitionDef_id`); a partition of `G / G[W]`
pulls back to one of `V(G)` with `W` in one part `Z`, of value at most
`s(V(G)) - s(Z) ≤ s(V(G)) - s(W)`; and `s(V(G)) ≤ def₂(G)`. -/
theorem deficiency_induce_add_deficiency_rigidContract_le [Finite α] [Finite β]
    {G : Graph α β} (hSv : ∀ X ⊆ V(G), 2 ≤ X.ncard → 1 ≤ (G.induce X).partitionDef 2 id)
    {W : Set α} (hW : W ⊆ V(G)) {r : α} (hr : r ∈ W)
    (hmono : ∀ X, W ⊆ X → X ⊆ V(G) →
      (G.induce W).partitionDef 2 id ≤ (G.induce X).partitionDef 2 id) :
    (G.induce W).deficiency 2 + (G.rigidContract (G.induce W) r).deficiency 2 ≤
      G.deficiency 2 := by
  have : Nonempty (α → α) := ⟨id⟩
  have hnn := partitionDef_induce_id_nonneg hSv
  have h1 : (G.induce W).deficiency 2 ≤ (G.induce W).partitionDef 2 id :=
    ciSup_le fun f => partitionDef_le_partitionDef_id (G := G.induce W) (fun Z hZ hne => by
      have hZ' : Z ⊆ W := hZ
      rw [induce_induce_of_subset G hZ']
      exact hnn Z (hZ'.trans hW) hne) f
  have h2 : (G.rigidContract (G.induce W) r).deficiency 2 ≤
      G.partitionDef 2 id - (G.induce W).partitionDef 2 id := by
    refine ciSup_le fun g => ?_
    rw [rigidContract, partitionDef_map]
    set f := g ∘ collapseTo r V(G.induce W) with hfdef
    have hfW : ∀ w ∈ W, f w = g r := fun w hw => by
      simp only [hfdef, Function.comp, collapseTo, vertexSet_induce, ite_eq_left hw]
    rw [partitionDef_deleteEdges_induce_eq fun u hu w hw => (hfW u hu).trans (hfW w hw).symm]
    have hK := partitionDef_add_partitionDef_induce_id_le (G := G) (n := 2) f (hW hr)
      (fun Z hZ hne => hnn Z (hZ.trans Set.sdiff_subset) hne)
    have hWZ : W ⊆ {w ∈ V(G) | f w = f r} := fun w hw =>
      ⟨hW hw, (hfW w hw).trans (hfW r hr).symm⟩
    have := hmono _ hWZ fun w hw => hw.1
    linarith
  have h3 : G.partitionDef 2 id ≤ G.deficiency 2 := partitionDef_le_deficiency _ _ _
  linarith

/-! ## The chains of one and two vertices (`lem:deficiency-one-body-chain`,
`lem:deficiency-two-body-chain`) -/

/-- **The merged deficiency at a vertex of degree two, at `n = 3`** (`lem:deficiency-one-body-chain`
(2)): let `V₁ ⊆ V(G)`, and let `x ∉ V₁` be joined by edges to `a ≠ b` in `V₁`. If no set of at least
two vertices containing `x` is rigid, then `def₃(G[V₁]; a, b) + 5 ≤ def₃(G[V₁])`. Otherwise let `Q`
be the part of `a` and `b` in a partition attaining the merged deficiency. Every labeling then has
value at most `4` on `G[Q]`, and at most `0` if it gives `a` and `b` the same label (`exists_glue`,
`partitionDef_split_of_sides`), and so `G[Q ∪ x]` is rigid (`partitionDef_induce_insert`). -/
theorem deficiencyMerged_three_add_five_le [Finite α] [Finite β] {G : Graph α β}
    {V₁ : Set α} {x a b : α} {e₀ e₁ : β} (hV₁ : V₁ ⊆ V(G)) (hxV₁ : x ∉ V₁) (ha : a ∈ V₁)
    (hb : b ∈ V₁) (hab : a ≠ b) (h₀ : G.IsLink e₀ x a) (h₁ : G.IsLink e₁ x b)
    (hno : ∀ Y ⊆ V(G), x ∈ Y → 2 ≤ Y.ncard → (G.induce Y).deficiency 3 ≠ 0) :
    (G.induce V₁).deficiencyMerged 3 a b + 5 ≤ (G.induce V₁).deficiency 3 := by
  have : Nonempty (α → α) := ⟨id⟩
  by_contra hlt
  push Not at hlt
  set G' := G.induce V₁ with hG'
  have : Nonempty {f : α → α // f a = f b} := ⟨⟨fun _ => a, rfl⟩⟩
  obtain ⟨⟨f, hfab⟩, hf⟩ := exists_eq_ciSup_of_finite
    (f := fun f : {f : α → α // f a = f b} => G'.partitionDef 3 f.1)
  rw [← Graph.deficiencyMerged] at hf
  set Q : Set α := {w ∈ V₁ | f w = f a} with hQ
  have hQV₁ : Q ⊆ V₁ := fun w hw => hw.1
  have haQ : a ∈ Q := ⟨ha, rfl⟩
  have hbQ : b ∈ Q := ⟨hb, hfab.symm⟩
  have hxQ : x ∉ Q := fun h' => hxV₁ h'.1
  -- the value of `g` on `G[Q]` is the value of a glued labeling of `G'`, less `m`
  have hkey : ∀ g : α → α, ∃ h : α → α, (g a = g b → h a = h b) ∧
      (G.induce Q).partitionDef 3 g = G'.partitionDef 3 h - G'.partitionDef 3 f := by
    intro g
    obtain ⟨h, hsep, hQk, hRk⟩ := exists_glue G' Q g f
    refine ⟨h, fun hg => (hQk a haQ b hbQ).mpr hg, ?_⟩
    have hsf : ∀ y ∈ Q, ∀ z ∈ V(G') \ Q, f y ≠ f z := by
      rintro y ⟨-, hy⟩ z ⟨hz, hzQ⟩ hyz
      exact hzQ ⟨hz, hyz ▸ hy⟩
    have hQG' : Q ⊆ V(G') := hQV₁
    rw [partitionDef_split_of_sides hQG' hsep, partitionDef_split_of_sides hQG' hsf,
      induce_induce_of_subset G hQV₁]
    have h0 : (G.induce Q).partitionDef 3 f = 0 :=
      partitionDef_eq_zero_of_forall_eq (G := G.induce Q) haQ fun w hw => hw.2
    have h1 : (G.induce Q).partitionDef 3 h = (G.induce Q).partitionDef 3 g :=
      partitionDef_eq_of_forall_iff hQk
    have h2 : (G'.induce (V(G') \ Q)).partitionDef 3 h =
        (G'.induce (V(G') \ Q)).partitionDef 3 f :=
      partitionDef_eq_of_forall_iff hRk
    rw [h0, h1, h2]
    ring
  have hbd : ∀ g : α → α, (G.induce Q).partitionDef 3 g ≤ 4 ∧
      (g a = g b → (G.induce Q).partitionDef 3 g ≤ 0) := by
    intro g
    obtain ⟨h, hab', hval⟩ := hkey g
    refine ⟨?_, fun hg => ?_⟩
    · have := G'.partitionDef_le_deficiency 3 h
      linarith
    · have := G'.partitionDef_le_deficiencyMerged 3 (hab' hg)
      linarith
  -- `G[Q ∪ x]` is rigid
  have hYd : (G.induce (insert x Q)).deficiency 3 = 0 := by
    refine le_antisymm (ciSup_le fun g => ?_) (deficiency_nonneg _ 3 ⟨x, Or.inl rfl⟩)
    rw [partitionDef_induce_insert (n := 3) hxQ g, bodyBarDim_three]
    push_cast
    set T : Set β := {e | ∃ y ∈ Q, G.IsLink e x y ∧ g y ≠ g x} with hT
    have he : e₀ ≠ e₁ := by
      rintro rfl
      rcases h₀.right_eq_or_eq h₁ with h' | h'
      · exact hxV₁ (h' ▸ ha)
      · exact hab h'
    have hT0 : g a ≠ g x → e₀ ∈ T := fun h' => ⟨a, haQ, h₀, h'⟩
    have hT1 : g b ≠ g x → e₁ ∈ T := fun h' => ⟨b, hbQ, h₁, h'⟩
    obtain ⟨hb4, hb0⟩ := hbd g
    split_ifs with hgx
    · by_cases hg : g a = g b
      · have : (0 : ℤ) ≤ T.ncard := by positivity
        linarith [hb0 hg]
      · have hne : g a ≠ g x ∨ g b ≠ g x := by
          by_contra hc; push Not at hc; exact hg (hc.1.trans hc.2.symm)
        have hT1' : 1 ≤ T.ncard := by
          rcases hne with h' | h'
          · simpa using Set.ncard_le_ncard (Set.singleton_subset_iff.mpr (hT0 h'))
              (Set.toFinite T)
          · simpa using Set.ncard_le_ncard (Set.singleton_subset_iff.mpr (hT1 h'))
              (Set.toFinite T)
        have : (1 : ℤ) ≤ T.ncard := by exact_mod_cast hT1'
        linarith
    · have ha' : g a ≠ g x := fun h' => hgx ⟨a, haQ, h'⟩
      have hb' : g b ≠ g x := fun h' => hgx ⟨b, hbQ, h'⟩
      have hsub : ({e₀, e₁} : Set β) ⊆ T := by
        rintro e (rfl | rfl)
        · exact hT0 ha'
        · exact hT1 hb'
      have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_pair he] at h2
      have h2' : (2 : ℤ) ≤ T.ncard := by exact_mod_cast h2
      by_cases hg : g a = g b
      · linarith [hb0 hg]
      · linarith
  refine hno (insert x Q) (Set.insert_subset h₀.left_mem (hQV₁.trans hV₁)) (Or.inl rfl) ?_ hYd
  have hsub : ({x, a} : Set α) ⊆ insert x Q :=
    Set.insert_subset_insert (Set.singleton_subset_iff.mpr haQ)
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rwa [Set.ncard_pair (a := x) (b := a) (fun h' : x = a => hxV₁ (h' ▸ ha))] at this

/-- **A non-adjacent pair outside every rigid set** (`lem:deficiency-two-body-chain`): let `G` be
sparse, and let `a ≠ b` be non-adjacent vertices with `def₃(G; a, b) ≠ def₃(G)`. Then
`def₂(G; a, b) + 2 ≤ def₂(G)`. Otherwise the part `Z` of `a` and `b` in a partition attaining the
planar merged deficiency has `s(Z) ≤ 1`. As `s({a, b}) = 3`, `|Z| ≥ 3`, so `Z` is rigid
(`deficiency_three_induce_eq_zero_of_tight`), and then `def₃(G; a, b) = def₃(G)`
(`deficiencyMerged_eq_deficiency_of_mem`). -/
theorem deficiencyMerged_two_add_two_le [Finite α] [Finite β] {G : Graph α β}
    (hSv : ∀ X ⊆ V(G), 2 ≤ X.ncard → 1 ≤ (G.induce X).partitionDef 2 id) {a b : α}
    (ha : a ∈ V(G)) (hb : b ∈ V(G)) (hab : a ≠ b) (hnadj : ¬ G.Adj a b)
    (hδ : G.deficiencyMerged 3 a b ≠ G.deficiency 3) :
    G.deficiencyMerged 2 a b + 2 ≤ G.deficiency 2 := by
  have : Nonempty (α → α) := ⟨id⟩
  have hnn := partitionDef_induce_id_nonneg hSv
  by_contra hlt
  push Not at hlt
  have : Nonempty {f : α → α // f a = f b} := ⟨⟨fun _ => a, rfl⟩⟩
  obtain ⟨⟨f, hfab⟩, hf⟩ := exists_eq_ciSup_of_finite
    (f := fun f : {f : α → α // f a = f b} => G.partitionDef 2 f.1)
  rw [← Graph.deficiencyMerged] at hf
  set Z : Set α := {w ∈ V(G) | f w = f a} with hZ
  have hK := partitionDef_add_partitionDef_induce_id_le (G := G) (n := 2) f ha
    (fun Y hY hne => hnn Y (hY.trans Set.sdiff_subset) hne)
  have hid := G.partitionDef_le_deficiency 2 id
  have hZ1 : (G.induce Z).partitionDef 2 id ≤ 1 := by linarith
  have hZV : Z ⊆ V(G) := fun w hw => hw.1
  have haZ : a ∈ Z := ⟨ha, rfl⟩
  have hbZ : b ∈ Z := ⟨hb, hfab.symm⟩
  have hZ2 : 2 ≤ Z.ncard := by
    have := Set.ncard_le_ncard (Set.pair_subset haZ hbZ) (Set.toFinite _)
    rwa [Set.ncard_pair hab] at this
  rcases Nat.lt_or_ge Z.ncard 3 with hZ3 | hZ3
  · -- `Z = {a, b}`, a pair with no edge, has `s = 3`
    have hZab : Z = {a, b} := (Set.eq_of_subset_of_ncard_le (Set.pair_subset haZ hbZ)
      (by rw [Set.ncard_pair hab]; omega) (Set.toFinite _)).symm
    have hbna : b ∉ ({a} : Set α) := fun h' => hab (Set.mem_singleton_iff.mp h').symm
    have hval := partitionDef_induce_insert (G := G) (n := 2) hbna id
    rw [ite_eq_right (by simpa using hbna), bodyBarDim_two,
      partitionDef_induce_singleton_id] at hval
    have hT : ({e | ∃ y ∈ ({a} : Set α), G.IsLink e b y ∧ id y ≠ id b} : Set β) = ∅ := by
      ext e
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, exists_eq_left,
        Set.mem_empty_iff_false, iff_false, not_and]
      exact fun hl _ => hnadj ⟨e, hl.symm⟩
    rw [hT, Set.ncard_empty] at hval
    push_cast at hval
    rw [hZab, Set.pair_comm] at hZ1
    linarith
  · have hZd := deficiency_three_induce_eq_zero_of_tight
      (fun Y hY => hSv Y (hY.trans hZV)) hZ3 hZ1
    exact hδ (deficiencyMerged_eq_deficiency_of_mem (by decide) hZV hZd haZ hbZ)

/-- **The planar merged deficiency at a vertex of degree two** (`lem:deficiency-one-body-chain`
(1)): let `G` be sparse, let `V₁ ⊆ V(G)`, and let `x ∉ V₁` be joined by edges to `a ≠ b` in `V₁`.
Then `a` and `b` are not adjacent, and `def₂(G[V₁]; a, b) + 2 ≤ def₂(G[V₁])`. An edge `ab` would
give the triangle `{x, a, b}` singleton value `0`. Adding `x` to a set containing `a` and `b` lowers
its singleton value by at least one, so the part `Z` of `a` and `b` in a partition attaining the
merged deficiency has `s(Z) ≥ 2`, and its value is at most `s(V₁) - s(Z)`
(`partitionDef_add_partitionDef_induce_id_le`). -/
theorem not_adj_and_deficiencyMerged_two_add_two_le [Finite α] [Finite β] {G : Graph α β}
    (hSv : ∀ X ⊆ V(G), 2 ≤ X.ncard → 1 ≤ (G.induce X).partitionDef 2 id) {V₁ : Set α}
    {x a b : α} {e₀ e₁ : β} (hV₁ : V₁ ⊆ V(G)) (hxV₁ : x ∉ V₁) (ha : a ∈ V₁) (hb : b ∈ V₁)
    (hab : a ≠ b) (h₀ : G.IsLink e₀ x a) (h₁ : G.IsLink e₁ x b) :
    ¬ G.Adj a b ∧
      (G.induce V₁).deficiencyMerged 2 a b + 2 ≤ (G.induce V₁).deficiency 2 := by
  have : Nonempty (α → α) := ⟨id⟩
  have hxV : x ∈ V(G) := h₀.left_mem
  have he : e₀ ≠ e₁ := by
    rintro rfl
    rcases h₀.right_eq_or_eq h₁ with h' | h'
    · exact hxV₁ (h' ▸ ha)
    · exact hab h'
  -- adding `x` to a set containing `a, b` lowers `s` by at least one
  have hx : ∀ Z ⊆ V₁, a ∈ Z → b ∈ Z → (G.induce (insert x Z)).partitionDef 2 id ≤
      (G.induce Z).partitionDef 2 id - 1 := by
    intro Z hZ haZ hbZ
    have hxZ : x ∉ Z := fun h' => hxV₁ (hZ h')
    rw [partitionDef_induce_insert (n := 2) hxZ id, ite_eq_right (by simpa using hxZ),
      bodyBarDim_two]
    push_cast
    have hsub : ({e₀, e₁} : Set β) ⊆ {e | ∃ y ∈ Z, G.IsLink e x y ∧ id y ≠ id x} := by
      rintro e (rfl | rfl)
      · exact ⟨a, haZ, h₀, fun h' => hxV₁ ((show a = x from h') ▸ ha)⟩
      · exact ⟨b, hbZ, h₁, fun h' => hxV₁ ((show b = x from h') ▸ hb)⟩
    have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_pair he] at h2
    have h2' : (2 : ℤ) ≤ ({e | ∃ y ∈ Z, G.IsLink e x y ∧ id y ≠ id x} : Set β).ncard := by
      exact_mod_cast h2
    linarith
  have hins3 : ∀ Z ⊆ V₁, a ∈ Z → b ∈ Z → 1 ≤ (G.induce (insert x Z)).partitionDef 2 id := by
    intro Z hZ haZ hbZ
    refine hSv _ (Set.insert_subset hxV (hZ.trans hV₁)) ?_
    have := Set.ncard_le_ncard (Set.insert_subset_insert (Set.singleton_subset_iff.mpr haZ))
      (Set.toFinite (insert x Z))
    rwa [Set.ncard_pair (a := x) (b := a) (fun h' : x = a => hxV₁ (h' ▸ ha))] at this
  refine ⟨fun ⟨f, hf⟩ => ?_, ?_⟩
  · -- a triangle `x a b` would have `s ≤ 0`
    have hpair : (G.induce {a, b}).partitionDef 2 id ≤ 1 := by
      have hbna : b ∉ ({a} : Set α) := fun h' => hab (Set.mem_singleton_iff.mp h').symm
      rw [show ({a, b} : Set α) = insert b {a} from Set.pair_comm a b,
        partitionDef_induce_insert (n := 2) hbna id, ite_eq_right (by simpa using hbna),
        bodyBarDim_two, partitionDef_induce_singleton_id]
      push_cast
      have hsub : ({f} : Set β) ⊆ {e | ∃ y ∈ ({a} : Set α), G.IsLink e b y ∧ id y ≠ id b} :=
        Set.singleton_subset_iff.mpr ⟨a, rfl, hf.symm, hab⟩
      have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_singleton] at h1
      have h1' : (1 : ℤ) ≤
          ({e | ∃ y ∈ ({a} : Set α), G.IsLink e b y ∧ id y ≠ id b} : Set β).ncard := by
        exact_mod_cast h1
      linarith
    have := hx {a, b} (Set.pair_subset ha hb) (Or.inl rfl) (Or.inr rfl)
    have := hins3 {a, b} (Set.pair_subset ha hb) (Or.inl rfl) (Or.inr rfl)
    linarith
  · set G' := G.induce V₁ with hG'
    have : Nonempty {f : α → α // f a = f b} := ⟨⟨fun _ => a, rfl⟩⟩
    obtain ⟨⟨f, hfab⟩, hf⟩ := exists_eq_ciSup_of_finite
      (f := fun f : {f : α → α // f a = f b} => G'.partitionDef 2 f.1)
    rw [← Graph.deficiencyMerged] at hf
    have hnn : ∀ Z ⊆ V(G'), Z.Nonempty → 0 ≤ (G'.induce Z).partitionDef 2 id := by
      intro Z hZ hne
      have hZ' : Z ⊆ V₁ := hZ
      rw [hG', induce_induce_of_subset G hZ']
      exact partitionDef_induce_id_nonneg (X := V(G)) hSv Z (hZ'.trans hV₁) hne
    have hK := partitionDef_add_partitionDef_induce_id_le (G := G') (n := 2) f
      (show a ∈ V(G') from ha) (fun Z hZ hne => hnn Z (hZ.trans Set.sdiff_subset) hne)
    have hZV : {w ∈ V(G') | f w = f a} ⊆ V₁ := fun w hw => hw.1
    rw [hG', induce_induce_of_subset G hZV] at hK
    have h1 := hx _ hZV ⟨ha, rfl⟩ ⟨hb, hfab.symm⟩
    have h2 := hins3 _ hZV ⟨ha, rfl⟩ ⟨hb, hfab.symm⟩
    have hid := G'.partitionDef_le_deficiency 2 id
    rw [hG'] at hid hf
    linarith

end Graph
