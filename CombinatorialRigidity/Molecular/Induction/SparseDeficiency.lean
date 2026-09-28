/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Induction.ReducibleVertex
import CombinatorialRigidity.Mathlib.Combinatorics.Graph.Delete

/-!
# The deficiency kit — value calculus (Phase 40l COVERAGE-REDUCE B2, `sec:main-component-sparse`)

The value form of the deficiency machinery COVERAGE's REDUCE sub-phase supplies to the `X₀`
induction (`blueprint/src/chapter/main-component.tex`, `sec:main-component-sparse`;
Katoh–Tanigawa 2011): the singleton-optimal bound, the sparse-set-is-rigid step, the
merge-along-a-rigid-set step, and the add-one-body identity, each stated at the `partitionDef`
value level (`Molecular/Deficiency.lean`) rather than as a `deficiency`-only inequality. B3 adds
the tight-set, core-bound, additive-core, and one- and two-body-chain layer on top, in this same
file.

## Main statements

* `Graph.partitionDef_le_partitionDef_id` / `Graph.partitionDef_add_partitionDef_induce_id_le`
  (`lem:deficiency-singleton-bound`) — if every nonempty subset has nonnegative singleton value,
  singletons are the optimal partition, and the distinguished part `Z₀ ∋ v` of any `f` can be
  split off without loss.
* `Graph.partitionDef_induce_insert` / `Graph.deficiency_induce_insert_eq_zero`
  (`lem:deficiency-add-body`) — the value identity for adding one body `u` to `X`, and (MC-75)(i):
  a body with two neighbours in a rigid set joins it.
* `Graph.exists_deficiency_induce_eq_zero_of_partitionDef_id_nonpos` /
  `Graph.one_le_partitionDef_induce_id` (`lem:deficiency-sparse`) — a minimal set of nonpositive
  singleton value is rigid, hence (MC-76): a rigid-set-free graph has singleton value at least
  `1` on every set of two or more bodies.
* `Graph.exists_partitionDef_le_mergeOn` / `Graph.deficiencyMerged_eq_deficiency_of_mem`
  (`lem:deficiency-merge-rigid`) — merging the parts that meet a rigid set does not lower the
  value, hence (MC-79)(i): two bodies in a common rigid set have `deficiencyMerged = deficiency`
  (with `Graph.deficiencyMerged_le_deficiency`, `Molecular/Deficiency.lean`, the other direction).

## Project context

See `notes/Phase40l.md` and `ROADMAP.md` §40 for the phase; the D5 pin discharged in this file
is `Graph.deficiencyMerged_le_deficiency` (`Molecular/Deficiency.lean`), confirmed to resolve
rather than re-derived.
-/

open scoped Graph

namespace Graph

variable {α β : Type*}

/-! ## Singleton-optimal partitions (`lem:deficiency-singleton-bound`) -/

/-- **A constant labeling has zero value**: if `f w = f v` for every `w ∈ V(G)`, then
`G.partitionDef n f = 0`. -/
lemma partitionDef_eq_zero_of_forall_eq {G : Graph α β} {n : ℕ} {f : α → α} {v : α}
    (hv : v ∈ V(G)) (hf : ∀ w ∈ V(G), f w = f v) : G.partitionDef n f = 0 := by
  rw [partitionDef_congr (g := fun _ => f v) (fun w hw => hf w hw)]
  exact partitionDef_one G n (f v) ⟨v, hv⟩

/-- **Singletons are optimal when no set has negative singleton value**: if every nonempty
`Z ⊆ V(G)` has `0 ≤ val_{G[Z]}(singletons)`, then `val_G(f) ≤ val_G(singletons)` for every `f`. -/
theorem partitionDef_le_partitionDef_id [Finite α] [Finite β] {n : ℕ} :
    ∀ {G : Graph α β}, (∀ Z ⊆ V(G), Z.Nonempty → 0 ≤ (G.induce Z).partitionDef n id) →
      ∀ f : α → α, G.partitionDef n f ≤ G.partitionDef n id := by
  classical
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

/-- **The distinguished-part bound** (the value identity's consumed form): if every nonempty set
of bodies outside the part `Z₀ ∋ v` of `f` has nonnegative singleton value, then
`val_G(f) + val_{G[Z₀]}(singletons) ≤ val_G(singletons)`. -/
theorem partitionDef_add_partitionDef_induce_id_le [Finite α] [Finite β] {G : Graph α β}
    {n : ℕ} (f : α → α) {v : α} (hv : v ∈ V(G))
    (hS : ∀ Z ⊆ V(G) \ {w | f w = f v}, Z.Nonempty → 0 ≤ (G.induce Z).partitionDef n id) :
    G.partitionDef n f + (G.induce {w ∈ V(G) | f w = f v}).partitionDef n id ≤
      G.partitionDef n id := by
  classical
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

/-! ## A minimal counterexample to (S) is rigid (`lem:deficiency-sparse`) -/

/-- **A singleton part has zero value**: `(G.induce {v}).partitionDef n id = 0`. -/
lemma partitionDef_induce_singleton_id (G : Graph α β) (n : ℕ) (v : α) :
    (G.induce {v}).partitionDef n id = 0 :=
  partitionDef_eq_zero_of_forall_eq (G := G.induce {v}) (v := v) rfl fun w hw => by
    simpa using hw

/-- **A set of nonpositive singleton value contains a rigid set** ((MC-76)'s minimal-counterexample
step, at any `n`): a minimal `Y ⊆ X`, `|Y| ≥ 2`, with `val_{G[Y]}(singletons) ≤ 0` is rigid. -/
theorem exists_deficiency_induce_eq_zero_of_partitionDef_id_nonpos [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} :
    ∀ {X : Set α}, X ⊆ V(G) → 2 ≤ X.ncard → (G.induce X).partitionDef n id ≤ 0 →
      ∃ Y ⊆ X, 2 ≤ Y.ncard ∧ (G.induce Y).deficiency n = 0 := by
  classical
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

/-- **(MC-76), the direction consumed**: no rigid set of two or more bodies gives (S) in value
form. -/
theorem one_le_partitionDef_induce_id [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hS : ∀ X ⊆ V(G), 2 ≤ X.ncard → (G.induce X).deficiency n ≠ 0) :
    ∀ X ⊆ V(G), 2 ≤ X.ncard → 1 ≤ (G.induce X).partitionDef n id := by
  intro X hX hX2
  by_contra hlt
  obtain ⟨Y, hYX, hY2, hYd⟩ :=
    exists_deficiency_induce_eq_zero_of_partitionDef_id_nonpos (n := n) hX hX2 (by omega)
  exact hS Y (hYX.trans hX) hY2 hYd

/-! ## Merging along a rigid set (`lem:deficiency-merge-rigid`) -/

/-- **Merging the parts that meet a rigid set does not lower the value** (the coarsening step of
(MC-77) and (MC-79)(i); (MC-67)(b)'s one line). -/
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
  change (bodyBarDim n : ℤ) * (((f '' W).ncard : ℤ) - 1) -
    ((bodyBarDim n : ℤ) - 1) * ((G.induce W).crossingEdges f).ncard ≤ 0 at hval
  linarith

/-- (MC-79)(i), the direction consumed: two bodies in a common rigid set have `δ = 0`. -/
theorem deficiencyMerged_eq_deficiency_of_mem [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hn : 1 ≤ bodyBarDim n) {Y : Set α} (hY : Y ⊆ V(G)) (hdef : (G.induce Y).deficiency n = 0)
    {a b : α} (ha : a ∈ Y) (hb : b ∈ Y) : G.deficiencyMerged n a b = G.deficiency n := by
  refine le_antisymm (G.deficiencyMerged_le_deficiency n a b) ?_
  obtain ⟨f, hf⟩ := G.exists_isTightPartition n
  obtain ⟨g, -, hgY, hfg⟩ := exists_partitionDef_le_mergeOn hn hY hdef f ⟨a, ha⟩
  calc G.deficiency n = G.partitionDef n f := hf.symm
    _ ≤ G.partitionDef n g := hfg
    _ ≤ G.deficiencyMerged n a b := G.partitionDef_le_deficiencyMerged n (hgY a ha b hb)

/-! ## Value-calculus helpers -/

/-- `bodyBarDim 2 = 3`: two translations plus one planar rotation. -/
lemma bodyBarDim_two : bodyBarDim 2 = 3 := rfl

/-- `bodyBarDim 3 = 6`: three translations plus three spatial rotations. -/
lemma bodyBarDim_three : bodyBarDim 3 = 6 := rfl

/-- `val₃(f) = 2 val₂(f) − d(f)`. -/
lemma partitionDef_three_eq (G : Graph α β) (f : α → α) :
    G.partitionDef 3 f = 2 * G.partitionDef 2 f - (G.crossingEdges f).ncard := by
  simp only [partitionDef, bodyBarDim_two, bodyBarDim_three]
  push_cast
  ring

/-- **Singleton value propagates to every nonempty subset**: if every `Z ⊆ X` with `2 ≤ |Z|` has
`1 ≤ val_{G[Z]}(id)`, then every nonempty `Z ⊆ X` has `0 ≤ val_{G[Z]}(id)` (singletons by
`partitionDef_induce_singleton_id`, the rest by hypothesis). -/
lemma partitionDef_induce_id_nonneg [Finite α] {G : Graph α β} {n : ℕ} {X : Set α}
    (hSv : ∀ Z ⊆ X, 2 ≤ Z.ncard → 1 ≤ (G.induce Z).partitionDef n id) :
    ∀ Z ⊆ X, Z.Nonempty → 0 ≤ (G.induce Z).partitionDef n id := by
  intro Z hZ hne
  rcases Nat.lt_or_ge Z.ncard 2 with h | h
  · obtain ⟨z, rfl⟩ : ∃ z, Z = {z} := Set.ncard_eq_one.mp (by
      have := (Set.ncard_pos (Set.toFinite Z)).mpr hne; omega)
    exact (partitionDef_induce_singleton_id G n z).ge
  · exact (hSv Z hZ h).trans' (by norm_num)

/-! ## Adding one body (`lem:deficiency-add-body`) -/

/-- Membership in `(G.induce S).crossingEdges g`: an edge of `G` with both ends in `S` carrying
different `g`-labels. -/
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
/-- **Adding one body** (the vertex count behind (MC-75)(i), (MC-79)(ii) and the core bound):
`val_{G[X ∪ u]}(g) = val_{G[X]}(g) + D·[g u is a new label] − (D − 1)·t`, with `t` the edges from
`u` into `X` whose far end has a different label. -/
theorem partitionDef_induce_insert [Finite α] [Finite β] {G : Graph α β} {n : ℕ} {X : Set α}
    {u : α} (huX : u ∉ X) (g : α → α) :
    (G.induce (insert u X)).partitionDef n g =
      (G.induce X).partitionDef n g + (if g u ∈ g '' X then 0 else (bodyBarDim n : ℤ)) -
        ((bodyBarDim n : ℤ) - 1) * ({e | ∃ y ∈ X, G.IsLink e u y ∧ g y ≠ g u}).ncard := by
  classical
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

/-- **(MC-75)(i)**: a body with two neighbours in a rigid set joins it (`D ≥ 3`). -/
theorem deficiency_induce_insert_eq_zero [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hn : 3 ≤ bodyBarDim n) {W : Set α} (hdef : (G.induce W).deficiency n = 0) {u c₁ c₂ : α}
    (huW : u ∉ W) (hc₁ : c₁ ∈ W) (hc₂ : c₂ ∈ W) (hne : c₁ ≠ c₂) (h₁ : G.Adj u c₁)
    (h₂ : G.Adj u c₂) : (G.induce (insert u W)).deficiency n = 0 := by
  classical
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

/-- **A maximal rigid superset inside `U`**: given `Y ⊆ U` rigid, some `W` with `Y ⊆ W ⊆ U` is
rigid and maximal among rigid subsets of `U` containing `Y`. -/
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

/-! ## Re-indexing helpers -/

/-- **Value depends only on the kernel**: labelings `f`, `g` inducing the same partition of
`V(G)` (agreeing on which vertices share a label) give the same value. -/
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

/-- **Gluing two labelings across a side split**: a side-separated labeling with the kernel of
`g` on `X` and of `f` off `X`. -/
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

end Graph
