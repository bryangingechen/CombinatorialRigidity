/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Deficiency.Cut

/-!
# Tight partitions, and the deficiency as the corank of `M(G̃)` (`sec:molecular-deficiency`)

The deficiency `def(G̃)` of `Molecular/Deficiency.lean` against the rank of `M(G̃)` (Katoh–Tanigawa
2011, *A proof of the molecular conjecture*, Discrete Comput. Geom. **45**, §2.5): the partitions
of largest value (tight partitions), the rank of the edges inside the parts of a partition, the
deficiency as the dimension grows, weak duality and its reverse, which give KT eq. (2.4), and its
consequences: a minimal spanning subgraph of the same deficiency and KT Proposition 2.2. The
blueprint presents the file in `sec:molecular-deficiency`, except the structure of tight
partitions (`sec:jacobs-tight-partitions`).

## Main definitions

* `Graph.IsTightPartition` (`def:tight-partition`).

## Main results

* `Graph.rank_add_deficiency_eq`, `Graph.isBase_ncard_add_deficiency_eq` — KT eq. (2.4),
  `rank M(G̃) + def(G̃) = D(|V(G)| - 1)` for `D ≥ 1` and `V(G)` nonempty (`thm:def-eq-corank`),
  from weak duality (`rank_add_deficiency_le`) and its reverse (`le_rank_add_deficiency`).
* `Graph.exists_isMinimalKDof_spanning_subgraph` — a minimal spanning subgraph of the same
  deficiency (`lem:minimal-kdof-spanning-subgraph`).
* `Graph.deficiency_eq_zero_iff_exists_spanningTrees` — KT Proposition 2.2: for `D ≥ 2` and
  `V(G)` nonempty, `def(G̃) = 0` iff `G̃` contains `D` edge-disjoint spanning trees
  (`lem:deficiency-zero-iff-tree-packing`).
-/

@[expose] public section

namespace Graph

open Set Matroid

variable {α β : Type*}

/-! ## Tight partitions (`def:tight-partition`, `sec:jacobs-tight-partitions`)

A partition of `V(G)` is *tight* when its value is the deficiency (`def:tight-partition`, after
Jackson and Jordán 2008, §2), and tight partitions exist (`lem:exists-tight-partition`). The rest of
the section is `sec:jacobs-tight-partitions`: the change in value when several parts are merged into
one (`lem:partitionDef-merge`), and from it Jackson and Jordán's Lemma 3.2(a)
(`lem:tight-partition-subfamily`), a consequence of its part (b) (`lem:tight-partition-parts`), and
two consequences of part (a) that they draw in the proofs of their Theorems 3.4 and 5.3: two parts
are joined by at most one edge (`lem:tight-partition-cross-pair-mult`), and two vertices in distinct
parts have at most one common neighbor (`lem:tight-partition-cross-pair-nbr`). Jackson and Jordán
take Lemma 3.2 from their paper *Brick partitions of graphs* (their reference [10]). The lemmas
hold for every `D = bodyBarDim n`, each with the bound on `D` that it assumes; `jacobs.tex` applies
them at `D = 6`. `IsTightPartition.parts` and `IsTightPartition.eq_of_common_nbr` also assume `G`
simple, as their nodes do. -/

/-- A **tight partition** (`def:tight-partition`; Jackson and Jordán 2008, §2): a labeling `f`
whose value `partitionDef` is the deficiency, `def_{G̃}(P_f) = def(G̃)`. The lemmas of
`sec:jacobs-tight-partitions` below are stated for such an `f`. -/
def IsTightPartition (G : Graph α β) (n : ℕ) (f : α → α) : Prop :=
  G.partitionDef n f = G.deficiency n

/-- **Tight partitions exist** (`lem:exists-tight-partition`), when `α` is finite. The labelings
`α → α` form a finite nonempty type (`id` is one), so some labeling has the largest value
(`Finite.exists_max`), and that value is the deficiency (`partitionDef_le_deficiency` and
`ciSup_le`). The lemma does not ask `V(G)` to be nonempty, unlike its node
(`fmlnote:tight-partition-consumed-forms`): when it is empty, every labeling has value `-D`, which
is then the deficiency. -/
theorem exists_isTightPartition [Finite α] (G : Graph α β) (n : ℕ) :
    ∃ f, G.IsTightPartition n f := by
  have : Nonempty (α → α) := ⟨id⟩
  obtain ⟨f, hf⟩ := Finite.exists_max (G.partitionDef n)
  exact ⟨f, le_antisymm (G.partitionDef_le_deficiency n f) (ciSup_le hf)⟩

/-- The set of edges of `G` **joining distinct members of a family of parts**
(`def:crossing-edges-within`): for a set `S` of labels, the edges `e ∈ E(G)` with ends `x, y` such
that `f x, f y ∈ S` and `f x ≠ f y`. For the family `Q` of the parts of the partition encoded by `f`
whose labels lie in `S`, it is Jackson and Jordán's `E_G(Q)` (2008, §2), and its size is their
`e_G(Q)`. -/
def crossingEdgesWithin (G : Graph α β) (f : α → α) (S : Set α) : Set β :=
  {e ∈ E(G) | ∃ x y, G.IsLink e x y ∧ f x ∈ S ∧ f y ∈ S ∧ f x ≠ f y}

/-- A step of `lem:partitionDef-merge`: a map `c` that sends every label of `S ⊆ T` to one
`a ∈ S` and fixes every label outside `S` sends `T` to `insert a (T \ S)`. -/
private lemma image_const_of_subset {T S : Set α} {c : α → α} {a : α}
    (hS : S ⊆ T) (ha : a ∈ S) (hc_mem : ∀ y ∈ S, c y = a) (hc_not_mem : ∀ y ∉ S, c y = y) :
    c '' T = insert a (T \ S) := by
  ext y
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_sdiff]
  constructor
  · rintro ⟨x, hxT, rfl⟩
    by_cases hxS : x ∈ S
    · exact Or.inl (hc_mem x hxS)
    · rw [hc_not_mem x hxS]; exact Or.inr ⟨hxT, hxS⟩
  · rintro (hy | ⟨hyT, hyS⟩)
    · exact ⟨a, hS ha, (hc_mem a ha).trans hy.symm⟩
    · exact ⟨y, hyT, hc_not_mem y hyS⟩

/-- **Deficiency under coarsening** (`lem:partitionDef-merge`). Let `f` be a labeling,
`S ⊆ f '' V(G)` a set of its labels on `V(G)` (the family `Q` of their parts), and `c : α → α` a
map that sends every label of `S` to one `a ∈ S` and fixes every label outside `S`, so that `c ∘ f`
merges the members of `Q` into one part. Then
`def_{G̃}(P_{c ∘ f}) = def_{G̃}(P_f) - (D(|S| - 1) - (D-1)·e_G(Q))`, where
`e_G(Q) = |crossingEdgesWithin G f S|`: the merged partition has `|S| - 1` fewer parts, and its
crossing edges are those of `f` that do not join two members of `Q`. `S` is nonempty as `a ∈ S`;
when `|S| = 1`, `c ∘ f` is `f`. Read from right to left, the identity gives the change in value when
a part is split into several (`IsTightPartition.parts`). -/
theorem partitionDef_merge [Finite α] [Finite β] {G : Graph α β} {n : ℕ} {f c : α → α}
    {S : Set α} {a : α} (hS : S ⊆ f '' V(G)) (ha : a ∈ S)
    (hc_mem : ∀ y ∈ S, c y = a) (hc_not_mem : ∀ y ∉ S, c y = y) :
    G.partitionDef n (c ∘ f) = G.partitionDef n f -
      ((bodyBarDim n : ℤ) * ((S.ncard : ℤ) - 1)
        - ((bodyBarDim n : ℤ) - 1) * (G.crossingEdgesWithin f S).ncard) := by
  -- Step 1: `numParts` of the coarsened labeling.
  have himg : (c ∘ f) '' V(G) = insert a (f '' V(G) \ S) := by
    rw [Set.image_comp]; exact image_const_of_subset hS ha hc_mem hc_not_mem
  have ha_notin : a ∉ f '' V(G) \ S := fun h => h.2 ha
  have hnp : G.numParts (c ∘ f) = (f '' V(G) \ S).ncard + 1 := by
    unfold numParts
    rw [himg, Set.ncard_insert_of_notMem ha_notin]
  have hnp' : (f '' V(G) \ S).ncard + S.ncard = G.numParts f := by
    unfold numParts
    exact Set.ncard_sdiff_add_ncard_of_subset hS
  -- Step 2: `crossingEdges` of the coarsened labeling.
  have hwithin_sub : G.crossingEdgesWithin f S ⊆ G.crossingEdges f := by
    rintro e ⟨heE, x, y, hlink, hxS, hyS, hfne⟩
    exact ⟨heE, x, y, hlink, hfne⟩
  have hce : G.crossingEdges (c ∘ f) = G.crossingEdges f \ G.crossingEdgesWithin f S := by
    ext e
    simp only [crossingEdges, crossingEdgesWithin, Function.comp, Set.mem_ofPred_eq, Set.mem_sdiff]
    constructor
    · rintro ⟨heE, x, y, hlink, hcne⟩
      have hfne : f x ≠ f y := fun he => hcne (congrArg c he)
      refine ⟨⟨heE, x, y, hlink, hfne⟩, ?_⟩
      rintro ⟨_, x', y', hlink', hx'S, hy'S, _⟩
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hlink.eq_and_eq_or_eq_and_eq hlink'
      · exact hcne ((hc_mem _ hx'S).trans (hc_mem _ hy'S).symm)
      · exact hcne ((hc_mem _ hy'S).trans (hc_mem _ hx'S).symm)
    · rintro ⟨⟨heE, x, y, hlink, hfne⟩, hnotwithin⟩
      have hnboth : ¬ (f x ∈ S ∧ f y ∈ S) :=
        fun ⟨hxS, hyS⟩ => hnotwithin ⟨heE, x, y, hlink, hxS, hyS, hfne⟩
      refine ⟨heE, x, y, hlink, ?_⟩
      by_cases hxS : f x ∈ S
      · have hyS : f y ∉ S := fun hy => hnboth ⟨hxS, hy⟩
        rw [hc_mem _ hxS, hc_not_mem _ hyS]
        exact fun h => hyS (by rw [← h]; exact ha)
      · by_cases hyS : f y ∈ S
        · rw [hc_not_mem _ hxS, hc_mem _ hyS]
          exact fun h => hxS (by rw [h]; exact ha)
        · rw [hc_not_mem _ hxS, hc_not_mem _ hyS]
          exact hfne
  have hce_ncard : (G.crossingEdges (c ∘ f)).ncard + (G.crossingEdgesWithin f S).ncard
      = (G.crossingEdges f).ncard := by
    rw [hce]; exact Set.ncard_sdiff_add_ncard_of_subset hwithin_sub
  -- Step 3: assemble.
  simp only [partitionDef]
  rw [hnp, ← hnp', ← hce_ncard]
  push_cast
  ring

/-- **Subfamilies of a tight partition** (`lem:tight-partition-subfamily`; Jackson and Jordán 2008,
Lemma 3.2(a)). Let `f` be a tight labeling and `S ⊆ f '' V(G)` a set of its labels on `V(G)` (the
family `Q` of their parts) with `2 ≤ |S|`. Then `(D-1)·e_G(Q) ≤ D(|S| - 1)`, where
`e_G(Q) = |crossingEdgesWithin G f S|`. Merging the members of `Q` (`partitionDef_merge`) gives a
partition of value at most `def(G̃)` (`partitionDef_le_deficiency`), which is the value of `f`, as
`f` is tight; so the change in value, `(D-1)·e_G(Q) - D(|S| - 1)`, is at most `0`. -/
theorem IsTightPartition.subfamily_le [Finite α] [Finite β] {G : Graph α β} {n : ℕ} {f : α → α}
    (hf : G.IsTightPartition n f) {S : Set α} (hS : S ⊆ f '' V(G)) (hS2 : 2 ≤ S.ncard) :
    ((bodyBarDim n : ℤ) - 1) * (G.crossingEdgesWithin f S).ncard ≤
      (bodyBarDim n : ℤ) * ((S.ncard : ℤ) - 1) := by
  classical
  obtain ⟨a, ha⟩ := Set.nonempty_of_ncard_ne_zero (by omega : S.ncard ≠ 0)
  have hmerge := partitionDef_merge (n := n) (c := fun x => if x ∈ S then a else x) hS ha
    (fun y hy => ite_eq_left hy) (fun y hy => ite_eq_right hy)
  have hle : G.partitionDef n ((fun x => if x ∈ S then a else x) ∘ f) ≤ G.deficiency n :=
    G.partitionDef_le_deficiency n _
  have hf' : G.partitionDef n f = G.deficiency n := hf
  linarith [hmerge, hle, hf']

/-- A step of `lem:tight-partition-parts`: if two distinct vertices `v, w` of `G` have the same
label, some label `b` is the label of no vertex of `G`. Indeed `f '' V(G) = f '' (V(G) \ {w})` has
at most `|V(G)| - 1 < |α|` elements, `α` being finite. `IsTightPartition.parts` gives `v` the
label `b` (`Function.update f v b`), to split `v` off its part. -/
private theorem exists_fresh_label [Finite α] (G : Graph α β) (f : α → α) {v w : α}
    (hv : v ∈ V(G)) (hw : w ∈ V(G)) (hvw : v ≠ w) (hfw : f w = f v) :
    ∃ b, b ∉ f '' V(G) := by
  have himg : f '' V(G) = f '' (V(G) \ {w}) := by
    refine subset_antisymm ?_ (Set.image_mono Set.sdiff_subset)
    rintro _ ⟨x, hx, rfl⟩
    by_cases hxw : x = w
    · exact ⟨v, Set.mem_sdiff_singleton.mpr ⟨hv, hvw⟩, ((congrArg f hxw).trans hfw).symm⟩
    · exact ⟨x, Set.mem_sdiff_singleton.mpr ⟨hx, hxw⟩, rfl⟩
  have hcard_le : (f '' V(G)).ncard ≤ (V(G) \ {w}).ncard := himg ▸ Set.ncard_image_le
  have hcard_diff : (V(G) \ {w}).ncard = V(G).ncard - 1 := Set.ncard_sdiff_singleton_of_mem hw
  have hVpos : 0 < V(G).ncard := (show V(G).Nonempty from ⟨v, hv⟩).ncard_pos
  have hVle : V(G).ncard ≤ Nat.card α := by
    rw [← Set.ncard_univ α]; exact Set.ncard_le_ncard (Set.subset_univ _)
  have hlt : (f '' V(G)).ncard < Nat.card α := by omega
  have hne : f '' V(G) ≠ Set.univ := by
    intro h
    rw [h, Set.ncard_univ] at hlt
    omega
  exact (Set.ne_univ_iff_exists_notMem _).mp hne

/-- **Parts of a tight partition** (`lem:tight-partition-parts`; a consequence of Jackson and
Jordán 2008, Lemma 3.2(b), which they draw in the proof of their Theorem 5.3). Let `D ≥ 2`, let `G`
be simple, let `f` be a tight labeling, and let `v ≠ w` be vertices of `G` with the same label, so
that the part of `v` has at least two vertices. Then that part has at least three vertices, and at
least two edges join `v` to other vertices of it.

Give `v` a label `b` that no vertex of `G` has (`exists_fresh_label`), in
`f' = Function.update f v b`. Merging the labels `b` and `f v` of `f'` (`partitionDef_merge`) gives
back the partition of `f` (`partitionDef_congr`), and as `f` is tight the value of `f'` is at most
that of `f`. So `D ≤ (D-1)·d`, where `d` is the number of edges joining `v` to the rest of its
part, and `d ≥ 2`. As `G` is simple, these edges have distinct other ends (`Simple.eq_of_isLink`),
so the part has at least `d + 1 ≥ 3` vertices. -/
theorem IsTightPartition.parts [Finite α] [Finite β] {G : Graph α β} {n : ℕ} {f : α → α}
    (hf : G.IsTightPartition n f) (hD : 2 ≤ bodyBarDim n) (hG : G.Simple)
    {v w : α} (hv : v ∈ V(G)) (hw : w ∈ V(G)) (hvw : w ≠ v) (hfw : f w = f v) :
    3 ≤ {x ∈ V(G) | f x = f v}.ncard ∧
      2 ≤ {e ∈ E(G) | ∃ y, y ≠ v ∧ f y = f v ∧ G.IsLink e v y}.ncard := by
  classical
  obtain ⟨b, hb⟩ := exists_fresh_label G f hv hw hvw.symm hfw
  set f' : α → α := Function.update f v b with hf'_def
  have hf'_v : f' v = b := Function.update_self v b f
  have hf'_ne : ∀ x, x ≠ v → f' x = f x := fun x hx => Function.update_of_ne hx b f
  set S : Set α := {b, f v} with hS_def
  have hbv : b ≠ f v := fun h => hb (h ▸ ⟨v, hv, rfl⟩)
  have hb_mem : b ∈ S := Set.mem_insert _ _
  have ha_mem : f v ∈ S := Set.mem_insert_iff.mpr (Or.inr rfl)
  have hc_fix : ∀ y, y ≠ b → (if y ∈ S then f v else y) = y := by
    intro y hy
    split_ifs with hyS
    · rw [hS_def] at hyS
      rcases hyS with rfl | rfl
      exacts [absurd rfl hy, rfl]
    · rfl
  have hS_sub : S ⊆ f' '' V(G) := by
    rw [hS_def]
    rintro y (rfl | rfl)
    · exact ⟨v, hv, hf'_v⟩
    · exact ⟨w, hw, (hf'_ne w hvw).trans hfw⟩
  have hmerge := partitionDef_merge (n := n) (f := f') (c := fun x => if x ∈ S then f v else x)
    hS_sub ha_mem (fun y hy => ite_eq_left hy) (fun y hy => ite_eq_right hy)
  have heq : Set.EqOn ((fun x => if x ∈ S then f v else x) ∘ f') f V(G) := by
    intro x hx
    simp only [Function.comp_apply]
    by_cases hxv : x = v
    · rw [hxv, hf'_v, ite_eq_left hb_mem]
    · rw [hf'_ne x hxv]
      exact hc_fix (f x) (fun h => hb (h ▸ ⟨x, hx, rfl⟩))
  have hfeq : G.partitionDef n ((fun x => if x ∈ S then f v else x) ∘ f') = G.partitionDef n f :=
    partitionDef_congr heq
  have htight : G.partitionDef n f = G.deficiency n := hf
  have hle : G.partitionDef n f' ≤ G.deficiency n := G.partitionDef_le_deficiency n f'
  have hScard : S.ncard = 2 := by rw [hS_def]; exact Set.ncard_pair hbv
  set e := (G.crossingEdgesWithin f' S).ncard with he_def
  have hDe : (bodyBarDim n : ℤ) ≤ ((bodyBarDim n : ℤ) - 1) * (e : ℤ) := by
    have hScard' : (S.ncard : ℤ) = 2 := by exact_mod_cast hScard
    rw [hScard'] at hmerge
    linarith [hmerge, hfeq, htight, hle]
  have he2 : 2 ≤ e := by
    by_contra hcon
    have hcon' : e < 2 := by omega
    interval_cases e <;> omega
  have hmem_S_iff : ∀ z ∈ V(G), z ≠ v → (f' z ∈ S ↔ f z = f v) := by
    intro z hz hzv
    rw [hf'_ne z hzv, hS_def, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (h | h)
      · exact absurd h (fun h' => hb (h' ▸ ⟨z, hz, rfl⟩))
      · exact h
    · exact fun h => Or.inr h
  have hset_eq : G.crossingEdgesWithin f' S =
      {e ∈ E(G) | ∃ y, y ≠ v ∧ f y = f v ∧ G.IsLink e v y} := by
    ext e'
    simp only [crossingEdgesWithin, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨heE, x, y, hlink, hxS, hyS, hne⟩
      by_cases hxv : x = v
      · have hyv : y ≠ v := fun h => hne (by rw [hxv, h])
        rw [hxv] at hlink
        exact ⟨heE, y, hyv, (hmem_S_iff y hlink.right_mem hyv).mp hyS, hlink⟩
      · by_cases hyv : y = v
        · have hlink' : G.IsLink e' v x := hyv ▸ hlink.symm
          exact ⟨heE, x, hxv, (hmem_S_iff x hlink.left_mem hxv).mp hxS, hlink'⟩
        · exfalso
          apply hne
          rw [hf'_ne x hxv, hf'_ne y hyv, (hmem_S_iff x hlink.left_mem hxv).mp hxS,
            (hmem_S_iff y hlink.right_mem hyv).mp hyS]
    · rintro ⟨heE, y, hyv, hfy, hlink⟩
      refine ⟨heE, v, y, hlink, by rw [hf'_v]; exact hb_mem,
        (hmem_S_iff y hlink.right_mem hyv).mpr hfy, ?_⟩
      rw [hf'_v, hf'_ne y hyv, hfy]
      exact hbv
  have he_eq : e = {e ∈ E(G) | ∃ y, y ≠ v ∧ f y = f v ∧ G.IsLink e v y}.ncard :=
    he_def.trans (congrArg Set.ncard hset_eq)
  refine ⟨?_, he_eq ▸ he2⟩
  -- Cardinality half: inject the in-part edges of `v` into the rest of the part.
  set T : Set β := {e ∈ E(G) | ∃ y, y ≠ v ∧ f y = f v ∧ G.IsLink e v y} with hT_def
  have hTcard : 2 ≤ T.ncard := he_eq ▸ he2
  have hφ_exists : ∀ e' ∈ T, ∃ y, y ≠ v ∧ f y = f v ∧ G.IsLink e' v y := fun e' he' => he'.2
  let φ : β → α := fun e' => if h : ∃ y, y ≠ v ∧ f y = f v ∧ G.IsLink e' v y then h.choose else v
  have hφ_spec : ∀ e' ∈ T, φ e' ≠ v ∧ f (φ e') = f v ∧ G.IsLink e' v (φ e') := by
    intro e' he'
    have hex := hφ_exists e' he'
    simp only [φ, dite_eq_left hex]
    exact hex.choose_spec
  have hφ_maps : ∀ e' ∈ T, φ e' ∈ {x ∈ V(G) | f x = f v} \ {v} := by
    intro e' he'
    obtain ⟨hne, hfeq', hlink⟩ := hφ_spec e' he'
    exact ⟨⟨hlink.right_mem, hfeq'⟩, hne⟩
  have hφ_inj : Set.InjOn φ T := by
    intro e1 he1 e2 he2' hφeq
    obtain ⟨hne1, hfeq1, hlink1⟩ := hφ_spec e1 he1
    obtain ⟨hne2, hfeq2, hlink2⟩ := hφ_spec e2 he2'
    have hlink2' : G.IsLink e2 v (φ e1) := hφeq ▸ hlink2
    exact hG.eq_of_isLink hlink1 hlink2'
  have hcard_le' : T.ncard ≤ ({x ∈ V(G) | f x = f v} \ {v}).ncard :=
    Set.ncard_le_ncard_of_injOn φ hφ_maps hφ_inj (Set.toFinite _)
  have hv_mem_fiber : v ∈ {x ∈ V(G) | f x = f v} := ⟨hv, rfl⟩
  have hdiff_card : ({x ∈ V(G) | f x = f v} \ {v}).ncard =
      {x ∈ V(G) | f x = f v}.ncard - 1 := Set.ncard_sdiff_singleton_of_mem hv_mem_fiber
  have hfiber_pos : 0 < {x ∈ V(G) | f x = f v}.ncard :=
    (show ({x ∈ V(G) | f x = f v} : Set α).Nonempty from ⟨v, hv_mem_fiber⟩).ncard_pos
  omega

/-- **At most one edge between two parts of a tight partition**
(`lem:tight-partition-cross-pair-mult`; a consequence of Jackson and Jordán 2008, Lemma 3.2(a),
which they draw in the proof of their Theorem 3.4). Let `D ≥ 3`, let `f` be a tight labeling, and
let `a ≠ b` be two of its labels on `V(G)`. Then at most one edge of `G` joins the parts labeled `a`
and `b`: `e_G(Q) ≤ 1` for `Q` the two parts, `|crossingEdgesWithin G f {a, b}| ≤ 1`. This holds for
every multigraph, with parallel edges counted (`fmlnote:tight-partition-consumed-forms`). Two such
edges would give `2(D-1) ≤ D` (`IsTightPartition.subfamily_le` at `S = {a, b}`), that is,
`D ≤ 2`. -/
theorem IsTightPartition.crossingEdgesWithin_pair_le_one [Finite α] [Finite β] {G : Graph α β}
    {n : ℕ} {f : α → α} (hf : G.IsTightPartition n f) (hD : 3 ≤ bodyBarDim n)
    {a b : α} (ha : a ∈ f '' V(G)) (hb : b ∈ f '' V(G)) (hab : a ≠ b) :
    (G.crossingEdgesWithin f {a, b}).ncard ≤ 1 := by
  have hS : ({a, b} : Set α) ⊆ f '' V(G) := by
    rintro x (rfl | rfl) <;> assumption
  have hScard : ({a, b} : Set α).ncard = 2 := Set.ncard_pair hab
  have h := hf.subfamily_le hS (le_of_eq hScard.symm)
  have hScard' : (({a, b} : Set α).ncard : ℤ) = 2 := by exact_mod_cast hScard
  rw [hScard'] at h
  rcases Nat.lt_or_ge (G.crossingEdgesWithin f {a, b}).ncard 2 with hlt | hge
  · omega
  · exfalso
    have h2 : (2 : ℤ) ≤ (G.crossingEdgesWithin f {a, b}).ncard := by exact_mod_cast hge
    have hD' : (3 : ℤ) ≤ (bodyBarDim n : ℤ) := by exact_mod_cast hD
    nlinarith

/-- A step of `lem:tight-partition-cross-pair-nbr`: an edge `e` with ends `a, b` and an edge `g`
with ends `c, d` are different edges when `{a, b} ≠ {c, d}` as unordered pairs, that is, when
`a ≠ c ∨ b ≠ d` and `a ≠ d ∨ b ≠ c`; an edge determines its ends up to order
(`IsLink.eq_and_eq_or_eq_and_eq`). It assumes nothing of `G`. -/
private theorem isLink_ne_of_ne_ends {G : Graph α β} {e g : β} {a b c d : α}
    (he : G.IsLink e a b) (hg : G.IsLink g c d) (h1 : a ≠ c ∨ b ≠ d) (h2 : a ≠ d ∨ b ≠ c) :
    e ≠ g := by
  rintro rfl
  rcases he.eq_and_eq_or_eq_and_eq hg with ⟨hac, hbd⟩ | ⟨had, hbc⟩
  · exact h1.elim (· hac) (· hbd)
  · exact h2.elim (· had) (· hbc)

/-- A step of `lem:tight-partition-cross-pair-nbr`: two distinct edges joining the parts of two
labels `a ≠ b` of a tight labeling contradict `IsTightPartition.crossingEdgesWithin_pair_le_one`,
which needs `D ≥ 3`. -/
private theorem false_of_two_crossing [Finite α] [Finite β] {G : Graph α β} {n : ℕ} {f : α → α}
    (hf : G.IsTightPartition n f) (hD5 : 5 ≤ bodyBarDim n)
    {a b : α} (hab : a ≠ b) (ha : a ∈ f '' V(G)) (hb : b ∈ f '' V(G))
    {e1 e2 : β} (h1 : e1 ∈ G.crossingEdgesWithin f {a, b})
    (h2 : e2 ∈ G.crossingEdgesWithin f {a, b}) (hne : e1 ≠ e2) : False := by
  have hle := hf.crossingEdgesWithin_pair_le_one (by omega) ha hb hab
  have hWsub : ({e1, e2} : Set β) ⊆ G.crossingEdgesWithin f {a, b} := by
    rintro x (rfl | rfl) <;> assumption
  have hWcard : ({e1, e2} : Set β).ncard = 2 := Set.ncard_pair hne
  have hWc := Set.ncard_le_ncard hWsub (Set.toFinite _)
  omega

/-- A step of `lem:tight-partition-cross-pair-nbr`: three distinct edges, each joining two of the
parts of three distinct labels of a tight labeling, contradict `D ≥ 5`, as
`IsTightPartition.subfamily_le` gives `3(D-1) ≤ 2D`, that is, `D ≤ 3`. -/
private theorem false_of_three_crossing [Finite α] [Finite β] {G : Graph α β} {n : ℕ} {f : α → α}
    (hf : G.IsTightPartition n f) (hD5 : 5 ≤ bodyBarDim n)
    {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a ∈ f '' V(G)) (hb : b ∈ f '' V(G)) (hc : c ∈ f '' V(G))
    {e1 e2 e3 : β} (h1 : e1 ∈ G.crossingEdgesWithin f {a, b, c})
    (h2 : e2 ∈ G.crossingEdgesWithin f {a, b, c}) (h3 : e3 ∈ G.crossingEdgesWithin f {a, b, c})
    (h12 : e1 ≠ e2) (h13 : e1 ≠ e3) (h23 : e2 ≠ e3) : False := by
  have hS : ({a, b, c} : Set α) ⊆ f '' V(G) := by
    rintro x (rfl | rfl | rfl) <;> assumption
  have hScard : ({a, b, c} : Set α).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩
  have hsub := hf.subfamily_le hS (by omega)
  have hWsub : ({e1, e2, e3} : Set β) ⊆ G.crossingEdgesWithin f {a, b, c} := by
    rintro x (rfl | rfl | rfl) <;> assumption
  have hWcard : ({e1, e2, e3} : Set β).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨e1, e2, e3, h12, h13, h23, rfl⟩
  have hWc := Set.ncard_le_ncard hWsub (Set.toFinite _)
  have hke : 3 ≤ (G.crossingEdgesWithin f {a, b, c}).ncard := by omega
  have hD' : (5 : ℤ) ≤ (bodyBarDim n : ℤ) := by exact_mod_cast hD5
  have hke' : (3 : ℤ) ≤ (G.crossingEdgesWithin f {a, b, c}).ncard := by exact_mod_cast hke
  rw [hScard] at hsub
  push_cast at hsub
  nlinarith [hsub, hke', hD']

/-- A step of `lem:tight-partition-cross-pair-nbr`: four distinct edges, each joining two of the
parts of four distinct labels of a tight labeling, contradict `D ≥ 5`, as
`IsTightPartition.subfamily_le` gives `4(D-1) ≤ 3D`, that is, `D ≤ 4`. -/
private theorem false_of_four_crossing [Finite α] [Finite β] {G : Graph α β} {n : ℕ} {f : α → α}
    (hf : G.IsTightPartition n f) (hD5 : 5 ≤ bodyBarDim n)
    {a b c d : α} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) (ha : a ∈ f '' V(G)) (hb : b ∈ f '' V(G)) (hc : c ∈ f '' V(G))
    (hd : d ∈ f '' V(G)) {e1 e2 e3 e4 : β} (h1 : e1 ∈ G.crossingEdgesWithin f {a, b, c, d})
    (h2 : e2 ∈ G.crossingEdgesWithin f {a, b, c, d})
    (h3 : e3 ∈ G.crossingEdgesWithin f {a, b, c, d})
    (h4 : e4 ∈ G.crossingEdgesWithin f {a, b, c, d}) (h12 : e1 ≠ e2) (h13 : e1 ≠ e3)
    (h14 : e1 ≠ e4) (h23 : e2 ≠ e3) (h24 : e2 ≠ e4) (h34 : e3 ≠ e4) : False := by
  have hS : ({a, b, c, d} : Set α) ⊆ f '' V(G) := by
    rintro x (rfl | rfl | rfl | rfl) <;> assumption
  have hScard : ({a, b, c, d} : Set α).ncard = 4 :=
    Set.ncard_eq_four.mpr ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩
  have hsub := hf.subfamily_le hS (by omega)
  have hWsub : ({e1, e2, e3, e4} : Set β) ⊆ G.crossingEdgesWithin f {a, b, c, d} := by
    rintro x (rfl | rfl | rfl | rfl) <;> assumption
  have hWcard : ({e1, e2, e3, e4} : Set β).ncard = 4 :=
    Set.ncard_eq_four.mpr ⟨e1, e2, e3, e4, h12, h13, h14, h23, h24, h34, rfl⟩
  have hWc := Set.ncard_le_ncard hWsub (Set.toFinite _)
  have hke : 4 ≤ (G.crossingEdgesWithin f {a, b, c, d}).ncard := by omega
  have hD' : (5 : ℤ) ≤ (bodyBarDim n : ℤ) := by exact_mod_cast hD5
  have hke' : (4 : ℤ) ≤ (G.crossingEdgesWithin f {a, b, c, d}).ncard := by exact_mod_cast hke
  rw [hScard] at hsub
  push_cast at hsub
  nlinarith [hsub, hke', hD']

/-- **The common neighbor of two vertices in distinct parts** (`lem:tight-partition-cross-pair-nbr`;
a consequence of Jackson and Jordán 2008, Lemma 3.2(a), which they draw in the proof of their
Theorem 5.3). Let `D ≥ 5`, let `G` be simple, let `f` be a tight labeling, and let `u, w` be
vertices with `f u ≠ f w`. Then any two common neighbors `v, v'` of `u` and `w` are equal. Jackson
and Jordán take `u` and `w` nonadjacent; the proof does not use it
(`fmlnote:tight-partition-consumed-forms`), and it uses simplicity only through looplessness.

Suppose that `v ≠ v'`. The vertices `u, v, w, v'` are then distinct, as `G` has no loops and
`f u ≠ f w`, so the edges `uv, vw, uv', v'w` are distinct (`isLink_ne_of_ne_ends`). In each case
of which of the labels `f u, f v, f w, f v'` are equal, either two of these edges join the same two
parts (`false_of_two_crossing`), or three or four of them join parts of three or four distinct
labels (`false_of_three_crossing`, `false_of_four_crossing`); each contradicts `D ≥ 5`. -/
theorem IsTightPartition.eq_of_common_nbr [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    {f : α → α} (hf : G.IsTightPartition n f) (hD5 : 5 ≤ bodyBarDim n) (hG : G.Simple)
    {u w v v' : α} (hfuw : f u ≠ f w)
    (huv : G.Adj u v) (hvw : G.Adj v w) (huv' : G.Adj u v') (hv'w : G.Adj v' w) :
    v = v' := by
  have := hG.toLoopless
  by_contra hne
  obtain ⟨e_uv, h_uv⟩ := huv
  obtain ⟨e_vw, h_vw⟩ := hvw
  obtain ⟨e_uv', h_uv'⟩ := huv'
  obtain ⟨e_v'w, h_v'w⟩ := hv'w
  have hu : u ∈ V(G) := h_uv.left_mem
  have hv : v ∈ V(G) := h_uv.right_mem
  have hw : w ∈ V(G) := h_vw.right_mem
  have hv' : v' ∈ V(G) := h_uv'.right_mem
  have huv_ne : u ≠ v := h_uv.ne
  have hvw_ne : v ≠ w := h_vw.ne
  have huv'_ne : u ≠ v' := h_uv'.ne
  have hv'w_ne : v' ≠ w := h_v'w.ne
  have huw_ne : u ≠ w := fun h => hfuw (h ▸ rfl)
  have hfu : f u ∈ f '' V(G) := ⟨u, hu, rfl⟩
  have hfv : f v ∈ f '' V(G) := ⟨v, hv, rfl⟩
  have hfw : f w ∈ f '' V(G) := ⟨w, hw, rfl⟩
  have hfv' : f v' ∈ f '' V(G) := ⟨v', hv', rfl⟩
  -- The four canonical edges are pairwise distinct.
  have h_uv_vw : e_uv ≠ e_vw := isLink_ne_of_ne_ends h_uv h_vw (Or.inl huv_ne) (Or.inl huw_ne)
  have h_uv_uv' : e_uv ≠ e_uv' := isLink_ne_of_ne_ends h_uv h_uv' (Or.inr hne) (Or.inl huv'_ne)
  have h_uv_v'w : e_uv ≠ e_v'w := isLink_ne_of_ne_ends h_uv h_v'w (Or.inl huv'_ne) (Or.inl huw_ne)
  have h_vw_uv' : e_vw ≠ e_uv' :=
    isLink_ne_of_ne_ends h_vw h_uv' (Or.inl huv_ne.symm) (Or.inl hne)
  have h_vw_v'w : e_vw ≠ e_v'w := isLink_ne_of_ne_ends h_vw h_v'w (Or.inl hne) (Or.inl hvw_ne)
  have h_uv'_v'w : e_uv' ≠ e_v'w :=
    isLink_ne_of_ne_ends h_uv' h_v'w (Or.inl huv'_ne) (Or.inl huw_ne)
  rcases eq_or_ne (f v) (f v') with hqs | hqs
  · -- `f v = f v'`: split on whether `u`'s part avoids the collision.
    rcases eq_or_ne (f u) (f v) with hpq | hpq
    · -- `f u = f v = f v'`: use the pair `{f v, f w}`.
      have hqr : f v ≠ f w := fun h => hfuw (hpq.trans h)
      refine false_of_two_crossing hf hD5 hqr hfv hfw ?_ ?_ h_vw_v'w
      · exact ⟨h_vw.edge_mem, v, w, h_vw, by simp, by simp, hqr⟩
      · exact ⟨h_v'w.edge_mem, v', w, h_v'w, by rw [← hqs]; simp, by simp,
          by rw [← hqs]; exact hqr⟩
    · -- `f u ≠ f v`: use the pair `{f u, f v}`.
      refine false_of_two_crossing hf hD5 hpq hfu hfv ?_ ?_ h_uv_uv'
      · exact ⟨h_uv.edge_mem, u, v, h_uv, by simp, by simp, hpq⟩
      · exact ⟨h_uv'.edge_mem, u, v', h_uv', by simp, by rw [← hqs]; simp,
          by rw [← hqs]; exact hpq⟩
  · -- `f v ≠ f v'`.
    rcases eq_or_ne (f v) (f u) with hqp | hqp
    · -- `f v = f u`.
      have hsp : f v' ≠ f u := fun h => hqs (hqp.trans h.symm)
      rcases eq_or_ne (f v') (f w) with hsr | hsr
      · -- `f v' = f w`: pair `{f u, f w}`.
        refine false_of_two_crossing hf hD5 hfuw hfu hfw ?_ ?_ h_vw_uv'
        · exact ⟨h_vw.edge_mem, v, w, h_vw, by rw [hqp]; simp, by simp,
            by rw [hqp]; exact hfuw⟩
        · exact ⟨h_uv'.edge_mem, u, v', h_uv', by simp, by rw [hsr]; simp,
            by rw [hsr]; exact hfuw⟩
      · -- `f v' ∉ {f u, f w}`: three-element instance, `S = {f u, f w, f v'}`.
        refine false_of_three_crossing hf hD5 hfuw hsp.symm hsr.symm hfu hfw hfv' ?_ ?_ ?_
          h_vw_v'w h_vw_uv' h_uv'_v'w.symm
        · exact ⟨h_vw.edge_mem, v, w, h_vw, by rw [hqp]; simp, by simp, by rw [hqp]; exact hfuw⟩
        · exact ⟨h_v'w.edge_mem, v', w, h_v'w, by simp, by simp, hsr⟩
        · exact ⟨h_uv'.edge_mem, u, v', h_uv', by simp, by simp, hsp.symm⟩
    · -- `f v ≠ f u`.
      rcases eq_or_ne (f v) (f w) with hqr | hqr
      · -- `f v = f w`.
        rcases eq_or_ne (f v') (f u) with hsp | hsp
        · -- `f v' = f u`: pair `{f u, f w}`.
          refine false_of_two_crossing hf hD5 hfuw hfu hfw ?_ ?_ h_uv_v'w
          · exact ⟨h_uv.edge_mem, u, v, h_uv, by simp, by rw [hqr]; simp, by rw [hqr]; exact hfuw⟩
          · exact ⟨h_v'w.edge_mem, v', w, h_v'w, by rw [hsp]; simp, by simp,
              by rw [hsp]; exact hfuw⟩
        · -- `f v' ≠ f u`: three-element instance, `S = {f u, f w, f v'}`.
          have hsr2 : f v' ≠ f w := fun h => hqs (h.trans hqr.symm).symm
          refine false_of_three_crossing hf hD5 hfuw hsp.symm hsr2.symm hfu hfw hfv' ?_ ?_ ?_
            h_uv_v'w h_uv_uv' h_uv'_v'w.symm
          · exact ⟨h_uv.edge_mem, u, v, h_uv, by simp, by rw [hqr]; simp, by rw [hqr]; exact hfuw⟩
          · exact ⟨h_v'w.edge_mem, v', w, h_v'w, by simp, by simp, hsr2⟩
          · exact ⟨h_uv'.edge_mem, u, v', h_uv', by simp, by simp, hsp.symm⟩
      · -- `f v ∉ {f u, f w}`.
        rcases eq_or_ne (f v') (f u) with hsp | hsp
        · -- `f v' = f u`: three-element instance, `S = {f u, f v, f w}`.
          refine false_of_three_crossing hf hD5 hqp.symm hfuw hqr hfu hfv hfw ?_ ?_ ?_
            h_uv_vw h_uv_v'w h_vw_v'w
          · exact ⟨h_uv.edge_mem, u, v, h_uv, by simp, by simp, hqp.symm⟩
          · exact ⟨h_vw.edge_mem, v, w, h_vw, by simp, by simp, hqr⟩
          · exact ⟨h_v'w.edge_mem, v', w, h_v'w, by rw [hsp]; simp, by simp,
              by rw [hsp]; exact hfuw⟩
        · -- `f v' ≠ f u`.
          rcases eq_or_ne (f v') (f w) with hsr | hsr
          · -- `f v' = f w`: three-element instance, `S = {f u, f v, f w}`.
            refine false_of_three_crossing hf hD5 hqp.symm hfuw hqr hfu hfv hfw ?_ ?_ ?_
              h_uv_vw h_uv_uv' h_vw_uv'
            · exact ⟨h_uv.edge_mem, u, v, h_uv, by simp, by simp, hqp.symm⟩
            · exact ⟨h_vw.edge_mem, v, w, h_vw, by simp, by simp, hqr⟩
            · exact ⟨h_uv'.edge_mem, u, v', h_uv', by simp, by rw [hsr]; simp,
                by rw [hsr]; exact hfuw⟩
          · -- fully generic: four-element instance, `S = {f u, f v, f w, f v'}`.
            refine false_of_four_crossing hf hD5 hqp.symm hfuw hsp.symm hqr hqs hsr.symm
              hfu hfv hfw hfv' ?_ ?_ ?_ ?_ h_uv_vw h_uv_v'w h_uv_uv' h_vw_v'w h_vw_uv'
              h_uv'_v'w.symm
            · exact ⟨h_uv.edge_mem, u, v, h_uv, by simp, by simp, hqp.symm⟩
            · exact ⟨h_vw.edge_mem, v, w, h_vw, by simp, by simp, hqr⟩
            · exact ⟨h_v'w.edge_mem, v', w, h_v'w, by simp, by simp, hsr⟩
            · exact ⟨h_uv'.edge_mem, u, v', h_uv', by simp, by simp, hsp.symm⟩

/-- **An upper bound on the rank of `M(G̃)`** (`lem:rank-matroidMG-le`): for `V(G)` nonempty,
`rank M(G̃) ≤ D(|V(G)| - 1)`, in `ℕ`. An independent set `I` of `M(G̃)` has `G̃ ↾ I`
`(D, D)`-sparse (`matroidMG_indep_iff`). If `I` is nonempty, sparsity applied to `I` itself gives
`|I| + D ≤ D·|V(I)| ≤ D·|V(G)|`. -/
theorem rank_matroidMG_le [DecidableEq β] [Finite α] [Finite β] (G : Graph α β) (n : ℕ)
    (hne : V(G).Nonempty) :
    (G.matroidMG n).rank ≤ bodyBarDim n * (V(G).ncard - 1) := by
  rw [Matroid.rank_def, Matroid.rk_le_iff]
  intro I hIsub hIndep
  rw [matroidMG_indep_iff] at hIndep
  obtain ⟨hsub, hsparse⟩ := hIndep
  rcases I.eq_empty_or_nonempty with rfl | hIne
  · simp
  -- Apply `(D,D)`-sparsity to `I` itself (`E(G̃ ↾ I) = I`): `|I| + D ≤ D·|spanningVerts I|`.
  have hIedge : E(G.mulTilde n ↾ I) = I := by rw [edgeSet_restrict, inter_eq_right.mpr hsub]
  have hkey := hsparse I hIedge.ge hIne
  -- The spanned vertices sit inside `V(G̃ ↾ I) = V(G̃) = V(G)`, so their count is `≤ |V|`.
  have hspanV : (G.mulTilde n ↾ I).spanningVerts I ⊆ V(G) := by
    refine ((G.mulTilde n ↾ I).spanningVerts_subset_vertexSet I).trans ?_
    rw [vertexSet_restrict]; exact subset_rfl
  have hcardV : ((G.mulTilde n ↾ I).spanningVerts I).ncard ≤ V(G).ncard :=
    Set.ncard_le_ncard hspanV V(G).toFinite
  -- `1 ≤ |V|` (nonempty), so `D·(|V|-1) = D·|V| - D` and the bound `|I| + D ≤ D·|V|` rearranges.
  have hV1 : 1 ≤ V(G).ncard := hne.ncard_pos
  calc I.ncard ≤ bodyBarDim n * V(G).ncard - bodyBarDim n := by
        have := Nat.mul_le_mul_left (bodyBarDim n) hcardV
        omega
    _ = bodyBarDim n * (V(G).ncard - 1) := by rw [Nat.mul_sub, Nat.mul_one]

/-! ## The rank of the edges inside the parts of a partition (`lem:rk-within-parts`)

Let `r` be the rank function of the cycle matroid of `G̃`, and let `Y` be a set of edges of `G̃`
whose ends lie in one part of the partition `P` encoded by `f`. Then `r(Y) ≤ |V(G)| - |P|`. The
restriction `G̃ ↾ Y` has all the vertices of `G` and `|V(G)| - r(Y)` components, and each component
lies in one part, so there are at least `|P|` of them. Weak duality (`lem:weak-duality`) applies
this to the edges of `G̃` inside the parts of `P`, and the reverse inequality of
`thm:def-eq-corank` to a set `Y₀` at which the rank of a matroid union attains its minimum. -/

/-- **The parts of a labeling constant along `Y` number at most the components of `H ↾ Y`** (a step
of `lem:rk-within-parts` and of `lem:deficiency-antitone`). If the labeling `f` agrees on the ends
of every edge of `Y`, it is constant on each component of the restriction `H ↾ Y`
(`ConnBetween.eq_of_forall_isLink`), so the map sending a label to the component of one of its
vertices is injective on `f '' V(H)`. -/
theorem encard_image_le_numberOfComponents_restrict {H : Graph α β} {Y : Set β} {f : α → α}
    (hY : ∀ e ∈ Y, ∀ x y, H.IsLink e x y → f x = f y) : (f '' V(H)).encard ≤ c(H ↾ Y) := by
  -- A representative vertex for each label.
  have hrep : ∀ ℓ : α, ∃ x : α, ℓ ∈ f '' V(H) → x ∈ V(H) ∧ f x = ℓ := by
    intro ℓ
    by_cases hℓ : ℓ ∈ f '' V(H)
    · obtain ⟨x, hx, rfl⟩ := hℓ; exact ⟨x, fun _ => ⟨hx, rfl⟩⟩
    · exact ⟨ℓ, fun h => (hℓ h).elim⟩
  choose rep hrep using hrep
  have hmaps : Set.MapsTo (fun ℓ => (H ↾ Y).walkable (rep ℓ)) (f '' V(H)) (H ↾ Y).Components :=
    fun ℓ hℓ => mem_components_iff_isCompOf.mpr
      (walkable_isCompOf (x := rep ℓ) (by rw [vertexSet_restrict]; exact (hrep ℓ hℓ).1))
  refine Set.encard_le_encard_of_injOn hmaps fun ℓ hℓ ℓ' hℓ' heq => ?_
  -- `rep ℓ'` lies in the component of `rep ℓ`, so the two reps carry the same label.
  have hmem : rep ℓ' ∈ V((H ↾ Y).walkable (rep ℓ)) := by
    rw [show (H ↾ Y).walkable (rep ℓ) = (H ↾ Y).walkable (rep ℓ') from heq,
      mem_walkable_self_iff, vertexSet_restrict]
    exact (hrep ℓ' hℓ').1
  have hff := (mem_walkable_iff.mp hmem).symm.eq_of_forall_isLink (s := f) fun e x y hl => by
    rw [restrict_isLink] at hl; exact hY e hl.1 x y hl.2
  rw [(hrep ℓ hℓ).2, (hrep ℓ' hℓ').2] at hff
  exact hff.symm

/-- **The rank of the edges inside the parts of a partition** (`lem:rk-within-parts`): let `r` be
the rank function of the cycle matroid of `G̃ = (D-1)·G`, and let `Y ⊆ E(G̃)` be a set of edges each
of which joins two vertices with the same label under `f`. Then `r(Y) + |P| ≤ |V(G)|`, where
`|P| = numParts G f`. The restriction `G̃ ↾ Y` keeps every vertex, so
`r(Y) + c(G̃ ↾ Y) = |V(G)|` (`eRank_cycleMatroid_add_numberOfComponents`), and
`|P| ≤ c(G̃ ↾ Y)` (`encard_image_le_numberOfComponents_restrict`). -/
theorem rk_cycleMatroid_within_parts_le [Finite α] [Finite β] (G : Graph α β)
    (n : ℕ) {Y : Set (β × Fin (bodyHingeMult n))} (hYE : Y ⊆ E(G.mulTilde n)) {f : α → α}
    (hY : ∀ p ∈ Y, ∀ x y, (G.mulTilde n).IsLink p x y → f x = f y) :
    (G.mulTilde n).cycleMatroid.rk Y + G.numParts f ≤ V(G).ncard := by
  have : Fintype α := Fintype.ofFinite α
  classical
  set H := G.mulTilde n with hH
  have hVH : V(H) = V(G) := by rw [hH, mulTilde]; rfl
  -- Rank–component identity on `H ↾ Y` (vertices preserved): `rk Y + c(H ↾ Y) = |V(G)|`.
  have hrank : H.cycleMatroid.eRk Y = (H ↾ Y).cycleMatroid.eRank := by
    rw [cycleMatroid_restrict, inter_eq_right.mpr hYE, Matroid.eRank_restrict]
  have hid : (H ↾ Y).cycleMatroid.eRank + c(H ↾ Y) = V(G).encard := by
    rw [eRank_cycleMatroid_add_numberOfComponents (H ↾ Y), vertexSet_restrict, hVH]
  -- Labels are constant on the components of `H ↾ Y`, so they number at most `c(H ↾ Y)`.
  have hle_enc : (f '' V(G)).encard ≤ c(H ↾ Y) := by
    have h := encard_image_le_numberOfComponents_restrict hY
    rwa [hVH] at h
  -- Cast to `ℕ`: everything is finite since `V(G).encard` is.
  have hfinV : V(G).encard ≠ ⊤ := by rw [Set.encard_ne_top_iff]; exact V(G).toFinite
  have hnp : (G.numParts f : ℕ∞) ≤ c(H ↾ Y) := by
    rw [numParts, Set.Finite.cast_ncard_eq ((f '' V(G)).toFinite)]; exact hle_enc
  -- `eRk Y = rk Y`, and `rk Y + numParts ≤ rk Y + c = |V(G)|`.
  have hrk_eq : (H.cycleMatroid.rk Y : ℕ∞) = (H ↾ Y).cycleMatroid.eRank := by
    rw [Matroid.cast_rk_eq_eRk_of_finite _ (Set.toFinite Y), hrank]
  have hsum : (H.cycleMatroid.rk Y : ℕ∞) + (G.numParts f : ℕ∞) ≤ (V(G).ncard : ℕ∞) := by
    rw [Set.Finite.cast_ncard_eq V(G).toFinite, ← hid, hrk_eq]
    gcongr
  exact_mod_cast hsum

/-! ## The deficiency does not increase with the dimension (`lem:deficiency-antitone`)

A partition of a connected graph into `p` parts is crossed by at least `p − 1` edges. So for
`D ≤ D′` the value of a partition `P` at `D′` minus its value at `D` is
`(D′ − D)(|P| − 1 − d_G(P)) ≤ 0`. In particular `def₃(G) ≤ def₂(G)`, the deficiencies at `D = 6`
and `D = 3`, which `sec:main-component` compares. -/

/-- **A partition of a connected graph into `p` parts is crossed by at least `p − 1` edges**
(`lem:deficiency-antitone`). Deleting the crossing edges leaves at least `p` components
(`encard_image_le_numberOfComponents_restrict`), and in the cycle matroid each deleted edge
lowers the rank `|V| − c` by at most one (`Matroid.eRk_union_le_eRk_add_eRk`,
`Matroid.eRk_le_encard`), from `|V| − 1` for the connected `G`. -/
theorem Connected.numParts_le_ncard_crossingEdges_add_one [Finite α] [Finite β] {G : Graph α β}
    (hG : G.Connected) (f : α → α) : G.numParts f ≤ (G.crossingEdges f).ncard + 1 := by
  set Y := E(G) \ G.crossingEdges f with hYdef
  have hYE : Y ⊆ E(G) := sdiff_subset
  have hY : ∀ e ∈ Y, ∀ x y, G.IsLink e x y → f x = f y := by
    rintro e ⟨heE, hnc⟩ x y hl
    by_contra h
    exact hnc ⟨heE, x, y, hl, h⟩
  have hnp := encard_image_le_numberOfComponents_restrict hY
  -- the rank–component identities on `G ↾ Y` and on the connected `G`
  have h1 : G.cycleMatroid.eRk Y + c(G ↾ Y) = V(G).encard := by
    rw [show G.cycleMatroid.eRk Y = (G ↾ Y).cycleMatroid.eRank by
      simp only [cycleMatroid_restrict, inter_eq_right.mpr hYE, Matroid.eRank_restrict],
      eRank_cycleMatroid_add_numberOfComponents (G ↾ Y), vertexSet_restrict]
  have h2 := eRank_cycleMatroid_add_numberOfComponents G
  rw [numberOfComponents_eq_one_iff.mpr hG] at h2
  -- deleting the crossing edges lowers the rank by at most their number
  have h3 : G.cycleMatroid.eRank ≤ G.cycleMatroid.eRk Y + (G.crossingEdges f).encard := by
    rw [← Matroid.eRk_ground, show G.cycleMatroid.E = Y ∪ G.crossingEdges f by
      rw [cycleMatroid_E, hYdef, sdiff_union_self,
        union_eq_left.mpr fun e (he : e ∈ G.crossingEdges f) => he.1]]
    refine (Matroid.eRk_union_le_eRk_add_eRk _ _ _).trans ?_
    gcongr
    exact Matroid.eRk_le_encard _ _
  have hYfin : G.cycleMatroid.eRk Y ≠ ⊤ :=
    ne_top_of_le_ne_top (encard_ne_top_iff.mpr (toFinite Y)) (Matroid.eRk_le_encard _ _)
  have hc : c(G ↾ Y) ≤ (G.crossingEdges f).encard + 1 := by
    have : G.cycleMatroid.eRk Y + c(G ↾ Y) ≤
        G.cycleMatroid.eRk Y + ((G.crossingEdges f).encard + 1) := by
      rw [h1, ← h2, ← add_assoc]; gcongr
    exact (WithTop.add_le_add_iff_left hYfin).mp this
  have := hnp.trans hc
  rw [numParts]
  rw [← Finite.cast_ncard_eq (toFinite _), ← Finite.cast_ncard_eq (toFinite _)] at this
  exact_mod_cast this

/-- **On a connected graph the deficiency does not increase with the dimension**
(`lem:deficiency-antitone`): for `n ≤ m`, `def_m(G) ≤ def_n(G)`. For each labeling `f`,
`partitionDef m f − partitionDef n f = (D_m − D_n)(|P| − 1 − d_G(P)) ≤ 0`, since `bodyBarDim` is
monotone and `|P| − 1 ≤ d_G(P)` (`Connected.numParts_le_ncard_crossingEdges_add_one`). -/
theorem Connected.deficiency_le_deficiency_of_le [Finite α] [Finite β] {G : Graph α β}
    (hG : G.Connected) {n m : ℕ} (hnm : n ≤ m) : G.deficiency m ≤ G.deficiency n := by
  have hD : (bodyBarDim n : ℤ) ≤ bodyBarDim m := by exact_mod_cast bodyBarDim_mono hnm
  have : Nonempty α := ⟨hG.nonempty.some⟩
  refine ciSup_le fun f => le_trans ?_ (G.partitionDef_le_deficiency n f)
  have hp : ((G.numParts f : ℤ) - 1) ≤ (G.crossingEdges f).ncard := by
    have := hG.numParts_le_ncard_crossingEdges_add_one f
    omega
  unfold partitionDef
  nlinarith

/-- **`def₃ ≤ def₂` on a connected graph** (`lem:deficiency-antitone`): the deficiency at `n = 3`
(`D = 6`) is at most that at `n = 2` (`D = 3`). -/
theorem Connected.deficiency_three_le_deficiency_two [Finite α] [Finite β] {G : Graph α β}
    (hG : G.Connected) : G.deficiency 3 ≤ G.deficiency 2 :=
  hG.deficiency_le_deficiency_of_le (by norm_num)

/-- **The deficiency stops changing** (`lem:deficiency-stable`; this project's, `notes/Strata.md`
Result 16): on a connected graph, for `n' ≤ n` with
`def₂(G) + 3 ≤ bodyBarDim n'`, `def_{n'}(G) = def_n(G)`. The value of a partition `P` at `D` is
`|P| − 1 − (D − 1)·c(P)` with `c(P) = d_G(P) − (|P| − 1) ≥ 0`. At `D ≥ bodyBarDim n'` it is at
most `0` when `c(P) ≥ 1` (it is at most `def₂(G) − (D − 3)·c(P)` by the value at `D = 3`), and
`|P| − 1`, independent of `D`, when `c(P) = 0`. `G` connected is needed: two bodies and no edge
have `def_n = bodyBarDim n`. -/
theorem Connected.deficiency_eq_of_deficiency_two_add_three_le [Finite α] [Finite β]
    {G : Graph α β} (hG : G.Connected) {n' n : ℕ} (hn : n' ≤ n)
    (h : G.deficiency 2 + 3 ≤ (bodyBarDim n' : ℤ)) : G.deficiency n' = G.deficiency n := by
  have : Nonempty α := ⟨hG.nonempty.some⟩
  refine le_antisymm ?_ (hG.deficiency_le_deficiency_of_le hn)
  refine ciSup_le fun f => ?_
  have hc := hG.numParts_le_ncard_crossingEdges_add_one f
  have h2 := G.partitionDef_le_deficiency 2 f
  have hD : (bodyBarDim n' : ℤ) ≤ bodyBarDim n := by exact_mod_cast bodyBarDim_mono hn
  have hb2 : (bodyBarDim 2 : ℤ) = 3 := by simp [bodyBarDim]
  unfold partitionDef at h2 ⊢
  rw [hb2] at h2
  set p : ℤ := (G.numParts f : ℤ) with hp
  set m : ℤ := ((G.crossingEdges f).ncard : ℤ) with hm
  have hpm : p - 1 ≤ m := by rw [hp, hm]; omega
  rcases eq_or_lt_of_le hpm with heq | hlt
  · -- a tree quotient: the same value at every dimension
    have := G.partitionDef_le_deficiency n f
    unfold partitionDef at this
    rw [← hp, ← hm, ← heq] at this
    rw [← heq]
    nlinarith
  · -- a cycle in the quotient: value at most `0`
    have hdef_nn := G.deficiency_nonneg 2 hG.nonempty
    have h0 := G.deficiency_nonneg n hG.nonempty
    nlinarith

/-- **The deficiency stops changing, design-doc form** (`lem:deficiency-stable`, "in particular"):
on a connected graph, for `n' ≤ n` with `2 + def₂(G) ≤ n'`, `def_{n'}(G) = def_n(G)`. Here
`bodyBarDim n' ≥ n' + 1 ≥ def₂(G) + 3`, as `def₂(G) ≥ 0` forces `n' ≥ 2`. -/
theorem Connected.deficiency_eq_of_two_add_deficiency_two_le [Finite α] [Finite β]
    {G : Graph α β} (hG : G.Connected) {n' n : ℕ} (hn : n' ≤ n)
    (h : 2 + G.deficiency 2 ≤ (n' : ℤ)) : G.deficiency n' = G.deficiency n := by
  have h0 := G.deficiency_nonneg 2 hG.nonempty
  have h2 : 2 ≤ n' := by omega
  refine hG.deficiency_eq_of_deficiency_two_add_three_le hn ?_
  have : n' + 1 ≤ bodyBarDim n' := by
    unfold bodyBarDim
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    nlinarith
  have : ((n' + 1 : ℕ) : ℤ) ≤ bodyBarDim n' := by exact_mod_cast this
  push_cast at this
  omega

/-! ## Weak duality (`lem:weak-duality`)

For `D ≥ 1`, `V(G)` nonempty and every partition `P` of `V(G)`,
`rank M(G̃) + def_{G̃}(P) ≤ D(|V(G)| - 1)`, and so `rank M(G̃) + def(G̃) ≤ D(|V(G)| - 1)`, the
inequality `≤` of KT eq. (2.4). Let `Y` be the set of the copies of the edges of `G` inside the
parts of `P`. The rank of a matroid union (`thm:matroid-partition-rank`, `Union_pow_rk_eq`), for
the `D` copies of the cycle matroid of `G̃` at `E(G̃)`, gives
`rank M(G̃) ≤ D·r(Y) + |E(G̃) ∖ Y|`. Then `r(Y) ≤ |V(G)| - |P|` (`rk_cycleMatroid_within_parts_le`),
and `|E(G̃) ∖ Y| = (D-1)·d_G(P)`, as each crossing edge has `D - 1` copies. -/

/-- A step of `lem:weak-duality` and of `thm:def-eq-corank`: the copies in `G̃` of the edges of `G`
crossing the partition encoded by `f` number `(D-1)·d_G(P)`, as each of the
`d_G(P) = |crossingEdges G f|` crossing edges has `D - 1 = bodyHingeMult n` copies. They are the
edges of `G̃` outside the set of the copies of the edges inside the parts. -/
private theorem ncard_crossing_fibers (G : Graph α β) (n : ℕ) (f : α → α) :
    {p : β × Fin (bodyHingeMult n) | p.1 ∈ G.crossingEdges f}.ncard =
      bodyHingeMult n * (G.crossingEdges f).ncard := by
  have hprod : {p : β × Fin (bodyHingeMult n) | p.1 ∈ G.crossingEdges f} =
      (G.crossingEdges f) ×ˢ (Set.univ : Set (Fin (bodyHingeMult n))) := by
    ext ⟨e, i⟩; simp
  rw [hprod, Set.ncard_prod, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin,
    mul_comm]

/-- **Weak duality at a partition** (`lem:weak-duality`): for `D ≥ 1`, `V(G)` nonempty and the
partition `P` encoded by a labeling `f`, `rank M(G̃) + def_{G̃}(P) ≤ D(|V(G)| - 1)`. Let
`Y = {p | p.1 ∈ E(G), p.1 ∉ crossingEdges G f}`, the copies of the edges inside the parts. The rank
of a matroid union (`Union_pow_rk_eq`), at `E(G̃)` and `Y`, gives
`rank M(G̃) ≤ D·r(Y) + |E(G̃) ∖ Y|` for the rank function `r` of the cycle matroid of `G̃`. Then
`r(Y) ≤ |V(G)| - |P|` (`rk_cycleMatroid_within_parts_le`) and
`|E(G̃) ∖ Y| = (D-1)·d_G(P)` (`ncard_crossing_fibers`). -/
theorem rank_add_partitionDef_le [DecidableEq β] [Finite α] [Finite β] (G : Graph α β)
    (n : ℕ) (hD : 1 ≤ bodyBarDim n) (hne : V(G).Nonempty) (f : α → α) :
    (G.matroidMG n).rank + G.partitionDef n f ≤ bodyBarDim n * ((V(G).ncard : ℤ) - 1) := by
  have : Fintype α := Fintype.ofFinite α
  classical
  -- `rank M(G̃) = (Union).rk E(G̃)` (restrict to the ground set is the rank).
  have hrank : (G.matroidMG n).rank =
      (Matroid.Union (fun _ : Fin (bodyBarDim n) ↦ (G.mulTilde n).cycleMatroid)).rk
        E(G.mulTilde n) := by
    rw [matroidMG, Matroid.rank_def, Matroid.restrict_ground_eq,
      Matroid.restrict_rk_eq _ subset_rfl]
  -- The non-crossing fibers `Y ⊆ E(G̃)`.
  set Y : Set (β × Fin (bodyHingeMult n)) :=
    {p | p.1 ∈ E(G) ∧ p.1 ∉ G.crossingEdges f} with hY
  have hYsub : Y ⊆ E(G.mulTilde n) := by
    intro p hp; rw [mem_edgeSet_mulTilde]; exact hp.1
  -- `E(G̃) ∖ Y = {p | p.1 ∈ crossingEdges}`: crossing edges have `p.1 ∈ E(G)`.
  have hdiff : E(G.mulTilde n) \ Y = {p : β × Fin (bodyHingeMult n) | p.1 ∈ G.crossingEdges f} := by
    ext p
    simp only [hY, Set.mem_sdiff, mem_edgeSet_mulTilde, Set.mem_ofPred_eq, not_and,
      not_not]
    constructor
    · rintro ⟨hpE, h⟩; exact h hpE
    · intro hp; exact ⟨(by exact hp.1 : p.1 ∈ E(G)), fun _ => hp⟩
  -- The rank of a matroid union: `rk_Union(E(G̃)) ≤ D·r_cycle(Y) + |E(G̃) ∖ Y|`.
  obtain ⟨_, hle⟩ := Union_pow_rk_eq (G.mulTilde n).cycleMatroid (bodyBarDim n) E(G.mulTilde n)
  have hbound := hle Y hYsub
  -- `rk_cycleMatroid_within_parts_le`'s hypothesis: an edge of `Y` joins vertices with one label.
  have hwithin : ∀ p ∈ Y, ∀ x y, (G.mulTilde n).IsLink p x y → f x = f y := by
    intro p hp x y hlink
    have hG : G.IsLink p.1 x y := by rw [mulTilde_isLink] at hlink; exact hlink
    by_contra hxy
    exact hp.2 ⟨hp.1, x, y, hG, hxy⟩
  have hpiece1 := G.rk_cycleMatroid_within_parts_le n hYsub hwithin
  -- Cardinality of the crossing fibers.
  have hcard : (E(G.mulTilde n) \ Y).ncard = bodyHingeMult n * (G.crossingEdges f).ncard := by
    rw [hdiff, ncard_crossing_fibers]
  -- Assemble in `ℕ`, then cast. `D = bodyBarDim n`, `D - 1 = bodyHingeMult n`.
  rw [hrank, partitionDef, numParts]
  -- `rank ≤ D·r_cycle(Y) + (D-1)·d_G(P)` and `r_cycle(Y) + |P| ≤ |V|`.
  have hkey : (Matroid.Union (fun _ : Fin (bodyBarDim n) ↦ (G.mulTilde n).cycleMatroid)).rk
      E(G.mulTilde n) ≤ bodyBarDim n * (G.mulTilde n).cycleMatroid.rk Y +
        bodyHingeMult n * (G.crossingEdges f).ncard := by
    rw [← hcard]; exact hbound
  -- `|V| ≥ 1` (nonempty); unfold `numParts` in `hpiece1` to match the goal's `(f '' V).ncard`.
  have hV1 : 1 ≤ V(G).ncard := hne.ncard_pos
  rw [numParts] at hpiece1
  -- `bodyHingeMult n = D - 1` as ℤ (clean since `D ≥ 1`).
  have hHM : (bodyHingeMult n : ℤ) = (bodyBarDim n : ℤ) - 1 := by rw [bodyHingeMult]; omega
  zify at hkey hpiece1
  rw [hHM] at hkey
  -- `r_cycle(Y) ≤ |V| - |P|` (`hpiece1`) and `rank ≤ D·r + (D-1)·d` (`hkey`); combine.
  set R : ℤ := ((G.mulTilde n).cycleMatroid.rk Y : ℤ) with hR
  set D : ℤ := (bodyBarDim n : ℤ) with hDdef
  nlinarith [hkey, hpiece1, mul_le_mul_of_nonneg_left
    (show R ≤ (V(G).ncard : ℤ) - (f '' V(G)).ncard by linarith)
    (show (0:ℤ) ≤ D by positivity)]

/-- **Weak duality** (`lem:weak-duality`): for `D ≥ 1` and `V(G)` nonempty,
`rank M(G̃) + def(G̃) ≤ D(|V(G)| - 1)`, that is, `def(G̃)` is at most the corank
`D(|V(G)| - 1) - rank M(G̃)`. It is `rank_add_partitionDef_le` at every partition (`ciSup_le`).
This is the inequality `≤` of KT eq. (2.4) (`thm:def-eq-corank`), whose reverse is
`le_rank_add_deficiency`. -/
theorem rank_add_deficiency_le [DecidableEq β] [Finite α] [Finite β] (G : Graph α β)
    (n : ℕ) (hD : 1 ≤ bodyBarDim n) (hne : V(G).Nonempty) :
    (G.matroidMG n).rank + G.deficiency n ≤ bodyBarDim n * ((V(G).ncard : ℤ) - 1) := by
  have : Nonempty (α → α) := ⟨fun _ => hne.choose⟩
  rw [deficiency]
  -- `⨆ def_P ≤ bound - rank` by `ciSup_le` on `rank_add_partitionDef_le`.
  have hbound : ⨆ f : α → α, G.partitionDef n f ≤
      bodyBarDim n * ((V(G).ncard : ℤ) - 1) - (G.matroidMG n).rank :=
    ciSup_le fun f => by linarith [G.rank_add_partitionDef_le n hD hne f]
  linarith

/-! ## The reverse inequality (`thm:def-eq-corank`)

For `D ≥ 1` and `V(G)` nonempty, some partition `P` of `V(G)` has
`rank M(G̃) + def_{G̃}(P) ≥ D(|V(G)| - 1)`, so `def(G̃)` is at least the corank of `M(G̃)`. Let `r`
be the rank function of the cycle matroid of `G̃`. The rank of a matroid union (`Union_pow_rk_eq`,
`thm:matroid-partition-rank`) gives a set `Y₀ ⊆ E(G̃)` with
`D·r(Y₀) + |E(G̃) ∖ Y₀| ≤ rank M(G̃)`. Let `P` be the partition of `V(G)` into the vertex sets of
the components of `G̃ ↾ Y₀`. Then `r(Y₀) = |V(G)| - |P|`, and the `D - 1` copies of an edge of `G`
crossing `P` lie outside `Y₀`, so `(D-1)·d_G(P) ≤ |E(G̃) ∖ Y₀|`. Together these give the
inequality at `P`. -/

/-- A chosen vertex of a graph `K` (the component graph in `componentLabel`), or an arbitrary
element of `α` if `K` has no vertex. It is a function of the graph, so that `componentLabel`, which
applies it to the component `H.walkable x` of `x`, is constant on a component by `congrArg`. -/
private noncomputable def pickVertex {α γ : Type*} [Nonempty α] (K : Graph α γ) : α := by
  classical exact if h : V(K).Nonempty then h.choose else Classical.arbitrary α

/-- The **component labeling** of a graph `H`: `componentLabel H x` is a chosen vertex of the
component `H.walkable x` of `x`. It is constant on each component
(`componentLabel_eq_of_connBetween`), and each vertex `x` of `H` is connected to its label
(`connBetween_componentLabel`), so its parts on `V(H)` are the vertex sets of the components. It is
the labeling of the partition into components in the proof of `le_rank_add_deficiency`
(`thm:def-eq-corank`'s formalization note). -/
private noncomputable def componentLabel {α γ : Type*} [Nonempty α] (H : Graph α γ) (x : α) : α :=
  pickVertex (H.walkable x)

private theorem pickVertex_mem {α γ : Type*} [Nonempty α] {K : Graph α γ} (h : V(K).Nonempty) :
    pickVertex K ∈ V(K) := by
  rw [pickVertex]; classical rw [dite_eq_left h]; exact h.choose_spec

private theorem connBetween_componentLabel {α γ : Type*} [Nonempty α] {H : Graph α γ} {x : α}
    (hx : x ∈ V(H)) : H.ConnBetween x (componentLabel H x) :=
  mem_walkable_iff.mp (pickVertex_mem ⟨x, mem_walkable hx⟩)

private theorem componentLabel_eq_of_connBetween {α γ : Type*} [Nonempty α] {H : Graph α γ}
    {x y : α} (h : H.ConnBetween x y) : componentLabel H x = componentLabel H y :=
  congrArg pickVertex h.walkable_eq_walkable

private theorem connBetween_of_componentLabel_eq {α γ : Type*} [Nonempty α] {H : Graph α γ}
    {x y : α} (hx : x ∈ V(H)) (hy : y ∈ V(H))
    (heq : componentLabel H x = componentLabel H y) : H.ConnBetween x y :=
  ((connBetween_componentLabel hx).trans (heq ▸ (connBetween_componentLabel hy).symm))

/-- A step of `thm:def-eq-corank`: the components of `H = G̃ ↾ Y` number at most the parts of its
component labeling `f`. The map sending a component to the label of its chosen vertex is injective
on the components, as two vertices with the same label are connected
(`connBetween_of_componentLabel_eq`). This is the reverse of the inequality `|P| ≤ c(H)` in
`rk_cycleMatroid_within_parts_le`, and it gives the equality `r(Y) + |P| = |V(G)|` for the
component labeling (`rk_add_numParts_componentLabel`). -/
private theorem numberOfComponents_le_numParts [Finite α] [Nonempty α] (G : Graph α β)
    (n : ℕ) {Y : Set (β × Fin (bodyHingeMult n))} :
    c((G.mulTilde n) ↾ Y) ≤ (G.numParts (componentLabel ((G.mulTilde n) ↾ Y)) : ℕ∞) := by
  classical
  set H := (G.mulTilde n) ↾ Y with hHdef
  have hVH : V(H) = V(G) := by rw [hHdef, vertexSet_restrict, mulTilde]; rfl
  set f := componentLabel H with hf
  -- A chosen representative vertex of each component.
  set rep : Graph α (β × Fin (bodyHingeMult n)) → α :=
    fun C => pickVertex C with hrep
  have hrepmem : ∀ C : Graph α (β × Fin (bodyHingeMult n)), C.IsCompOf H → rep C ∈ V(C) :=
    fun C hC => pickVertex_mem hC.nonempty
  -- Inject components into the label image `f '' V(G)`.
  have hmaps : Set.MapsTo (fun C => f (rep C)) H.Components (f '' V(G)) := by
    intro C hC
    have hCco : C.IsCompOf H := mem_components_iff_isCompOf.mp hC
    exact ⟨rep C, hVH ▸ vertexSet_mono hCco.le (hrepmem C hCco), rfl⟩
  have hinj : Set.InjOn (fun C => f (rep C)) H.Components := by
    intro C hC C' hC' heq
    have hCco : C.IsCompOf H := mem_components_iff_isCompOf.mp hC
    have hC'co : C'.IsCompOf H := mem_components_iff_isCompOf.mp hC'
    have hc := hrepmem C hCco
    have hc' := hrepmem C' hC'co
    have hconn := connBetween_of_componentLabel_eq (vertexSet_mono hCco.le hc)
      (vertexSet_mono hC'co.le hc') heq
    refine hCco.eq_of_not_disjoint hC'co (Set.not_disjoint_iff.mpr ⟨rep C, hc, ?_⟩)
    rw [hC'co.eq_walkable_of_mem_walkable hc', mem_walkable_iff]
    exact hconn.symm
  -- Components inject into the label image, so `c ≤ |f '' V|`.
  rw [NumberOfComponents, numParts, Set.Finite.cast_ncard_eq ((f '' V(G)).toFinite)]
  exact Set.encard_le_encard_of_injOn hmaps hinj

/-- A step of `thm:def-eq-corank`: for `Y ⊆ E(G̃)` and the component labeling `f` of `G̃ ↾ Y`,
`r(Y) + |P| = |V(G)|`, where `r` is the rank function of the cycle matroid of `G̃` and
`|P| = numParts G f`. The inequality `≤` is `rk_cycleMatroid_within_parts_le`, as an edge of `Y`
joins two vertices of one component, which have the same label; the inequality `≥` is
`numberOfComponents_le_numParts` with `r(Y) + c(G̃ ↾ Y) = |V(G)|`. With the equality, the bound of
`rk_cycleMatroid_within_parts_le` that weak duality uses becomes the bound the reverse inequality
needs. -/
private theorem rk_add_numParts_componentLabel [Finite α] [Finite β] [Nonempty α] (G : Graph α β)
    (n : ℕ) {Y : Set (β × Fin (bodyHingeMult n))} (hYE : Y ⊆ E(G.mulTilde n)) :
    (G.mulTilde n).cycleMatroid.rk Y + G.numParts (componentLabel ((G.mulTilde n) ↾ Y))
      = V(G).ncard := by
  classical
  set H := (G.mulTilde n) ↾ Y with hHdef
  have hVH : V(H) = V(G) := by rw [hHdef, vertexSet_restrict, mulTilde]; rfl
  set f := componentLabel H with hf
  -- The fibers of `Y` join equally-labeled vertices (same component, `componentLabel` constant).
  have hwithin : ∀ p ∈ Y, ∀ x y, (G.mulTilde n).IsLink p x y → f x = f y := by
    intro p hp x y hlink
    have hHlink : H.IsLink p x y := by rw [hHdef, restrict_isLink]; exact ⟨hp, hlink⟩
    exact componentLabel_eq_of_connBetween (H := H) hHlink.connBetween
  -- `≤` from `rk_cycleMatroid_within_parts_le`.
  have hle := G.rk_cycleMatroid_within_parts_le n hYE hwithin
  -- `≥` via the rank–component identity and `c ≤ numParts`.
  have hrank : (G.mulTilde n).cycleMatroid.eRk Y = H.cycleMatroid.eRank := by
    rw [hHdef, cycleMatroid_restrict, inter_eq_right.mpr hYE, Matroid.eRank_restrict]
  have hid : H.cycleMatroid.eRank + c(H) = V(G).encard := by
    rw [eRank_cycleMatroid_add_numberOfComponents H, hVH]
  have hrk_eq : ((G.mulTilde n).cycleMatroid.rk Y : ℕ∞) = H.cycleMatroid.eRank := by
    rw [Matroid.cast_rk_eq_eRk_of_finite _ (Set.toFinite Y), hrank]
  have hcle : c(H) ≤ (G.numParts f : ℕ∞) := G.numberOfComponents_le_numParts n (Y := Y)
  -- `|V| = eRank + c ≤ rk + numParts` in `ℕ∞`.
  have hge : (V(G).ncard : ℕ∞) ≤
      ((G.mulTilde n).cycleMatroid.rk Y : ℕ∞) + (G.numParts f : ℕ∞) := by
    rw [hrk_eq, Set.Finite.cast_ncard_eq V(G).toFinite]
    calc V(G).encard = H.cycleMatroid.eRank + c(H) := hid.symm
      _ ≤ H.cycleMatroid.eRank + (G.numParts f : ℕ∞) := by gcongr
  -- Combine `≤` (`hle`) and `≥` into the equality, in `ℕ`.
  have hge' : V(G).ncard ≤ (G.mulTilde n).cycleMatroid.rk Y + G.numParts f := by
    exact_mod_cast hge
  omega

/-- **The deficiency is at least the corank** (`thm:def-eq-corank`, the reverse inequality of KT
eq. (2.4)): for `D ≥ 1` and `V(G)` nonempty, `rank M(G̃) + def(G̃) ≥ D(|V(G)| - 1)`. With
`rank_add_deficiency_le` it gives `rank_add_deficiency_eq`.

The rank of a matroid union (`Union_pow_rk_eq`) gives a set `Y₀ ⊆ E(G̃)` with
`D·r(Y₀) + |E(G̃) ∖ Y₀| ≤ rank M(G̃)`, where `r` is the rank function of the cycle matroid of `G̃`.
Let `f` be the component labeling of `G̃ ↾ Y₀`, and `P` its partition. Then
`r(Y₀) + |P| = |V(G)|` (`rk_add_numParts_componentLabel`). The ends of an edge of `G` crossing `P`
lie in different components, so its `D - 1` copies lie outside `Y₀`, and
`(D-1)·d_G(P) ≤ |E(G̃) ∖ Y₀|` (`ncard_crossing_fibers`). Hence
`rank M(G̃) ≥ D(|V(G)| - |P|) + (D-1)·d_G(P) = D(|V(G)| - 1) - def_{G̃}(P)`, and
`def_{G̃}(P) ≤ def(G̃)`. -/
theorem le_rank_add_deficiency [DecidableEq β] [Finite α] [Finite β] (G : Graph α β)
    (n : ℕ) (hD : 1 ≤ bodyBarDim n) (hne : V(G).Nonempty) :
    bodyBarDim n * ((V(G).ncard : ℤ) - 1) ≤ (G.matroidMG n).rank + G.deficiency n := by
  have : Fintype α := Fintype.ofFinite α
  have : Nonempty α := ⟨hne.choose⟩
  classical
  -- `rank M(G̃) = (Union).rk E(G̃)`.
  have hrank : (G.matroidMG n).rank =
      (Matroid.Union (fun _ : Fin (bodyBarDim n) ↦ (G.mulTilde n).cycleMatroid)).rk
        E(G.mulTilde n) := by
    rw [matroidMG, Matroid.rank_def, Matroid.restrict_ground_eq,
      Matroid.restrict_rk_eq _ subset_rfl]
  -- A set `Y₀ ⊆ E(G̃)` at which the rank of the matroid union attains its minimum.
  obtain ⟨⟨Y₀, hY₀sub, hY₀le⟩, _⟩ :=
    Union_pow_rk_eq (G.mulTilde n).cycleMatroid (bodyBarDim n) E(G.mulTilde n)
  set f := componentLabel ((G.mulTilde n) ↾ Y₀) with hf
  -- `r_cycle(Y₀) + numParts f = |V|`.
  have heq := G.rk_add_numParts_componentLabel n hY₀sub
  -- Crossing fibers sit inside `E(G̃) ∖ Y₀`.
  have hcrosssub : {p : β × Fin (bodyHingeMult n) | p.1 ∈ G.crossingEdges f}
      ⊆ E(G.mulTilde n) \ Y₀ := by
    rintro p hp
    obtain ⟨hpE, x, y, hlink, hxy⟩ := hp
    refine ⟨by rw [mem_edgeSet_mulTilde]; exact hpE, fun hpY₀ => hxy ?_⟩
    -- If `p ∈ Y₀`, its endpoints `x, y` are connected in `G̃ ↾ Y₀`, hence equally labeled.
    have hGlink : (G.mulTilde n).IsLink p x y := by rw [mulTilde_isLink]; exact hlink
    have hHlink : ((G.mulTilde n) ↾ Y₀).IsLink p x y := by
      rw [restrict_isLink]; exact ⟨hpY₀, hGlink⟩
    exact componentLabel_eq_of_connBetween (H := (G.mulTilde n) ↾ Y₀) hHlink.connBetween
  have hcrosscard : (bodyHingeMult n) * (G.crossingEdges f).ncard
      ≤ (E(G.mulTilde n) \ Y₀).ncard := by
    rw [← G.ncard_crossing_fibers n f]
    exact Set.ncard_le_ncard hcrosssub (E(G.mulTilde n) \ Y₀).toFinite
  -- The deficiency dominates this partition's deficiency.
  have hdef := G.partitionDef_le_deficiency n f
  rw [partitionDef, numParts] at hdef
  -- `|V| ≥ 1` and `D - 1 = bodyHingeMult n`.
  have hV1 : 1 ≤ V(G).ncard := hne.ncard_pos
  have hHM : (bodyHingeMult n : ℤ) = (bodyBarDim n : ℤ) - 1 := by rw [bodyHingeMult]; omega
  rw [hrank]
  -- Assemble in `ℤ`. `numParts f = (f '' V(G)).ncard`.
  rw [← hf, numParts] at heq
  zify at hY₀le hcrosscard heq
  rw [hHM] at hcrosscard
  set D : ℤ := (bodyBarDim n : ℤ) with hDdef
  set R : ℤ := ((G.mulTilde n).cycleMatroid.rk Y₀ : ℤ) with hR
  set NP : ℤ := ((f '' V(G)).ncard : ℤ) with hNP
  set RKU : ℤ := ((Matroid.Union (fun _ : Fin (bodyBarDim n) ↦ (G.mulTilde n).cycleMatroid)).rk
    E(G.mulTilde n) : ℤ) with hRKU
  set DC : ℤ := ((G.crossingEdges f).ncard : ℤ) with hDC
  set ED : ℤ := ((E(G.mulTilde n) \ Y₀).ncard : ℤ) with hED
  -- hY₀le : D * R + ED ≤ RKU ; heq : R + NP = |V| ; hcrosscard : (D-1)*DC ≤ ED
  -- hdef : def_P = D*(NP-1) - (D-1)*DC ≤ deficiency
  nlinarith [hdef, hY₀le, heq, hcrosscard]

/-! ## The deficiency is the corank of `M(G̃)` (`thm:def-eq-corank`) -/

/-- **`rank M(G̃) + def(G̃) = D(|V(G)| - 1)`** (`thm:def-eq-corank`; Katoh–Tanigawa 2011,
eq. (2.4), p. 655), for `D ≥ 1` and `V(G)` nonempty: weak duality (`rank_add_deficiency_le`) and its
reverse (`le_rank_add_deficiency`). Katoh and Tanigawa observe it from their Proposition 2.3. As
the independent sets of `M(G̃)` are the unions of `D` forests of `G̃`, it is the classical formula
for the largest size of such a union (Jackson and Jordán 2010, Theorem 4.1(a), p. 580, who cite
Nash-Williams 1961 and 1964 and Tutte 1961), applied to `G̃`. -/
theorem rank_add_deficiency_eq [DecidableEq β] [Finite α] [Finite β] (G : Graph α β)
    (n : ℕ) (hD : 1 ≤ bodyBarDim n) (hne : V(G).Nonempty) :
    (G.matroidMG n).rank + G.deficiency n = bodyBarDim n * ((V(G).ncard : ℤ) - 1) :=
  le_antisymm (G.rank_add_deficiency_le n hD hne) (G.le_rank_add_deficiency n hD hne)

/-- **`|B| + def(G̃) = D(|V(G)| - 1)` for a base `B` of `M(G̃)`** (`thm:def-eq-corank`;
Katoh–Tanigawa 2011, eq. (2.4), p. 655), for `D ≥ 1` and `V(G)` nonempty, as
`|B| = rank M(G̃)` (`rank_add_deficiency_eq`). So the deficiency is the corank
`D(|V(G)| - 1) - |B|`, and `def(G̃) = 0` iff `|B| = D(|V(G)| - 1)`. -/
theorem isBase_ncard_add_deficiency_eq [DecidableEq β] [Finite α] [Finite β] (G : Graph α β)
    (n : ℕ) (hD : 1 ≤ bodyBarDim n) (hne : V(G).Nonempty) {B : Set (β × Fin (bodyHingeMult n))}
    (hB : (G.matroidMG n).IsBase B) :
    (B.ncard : ℤ) + G.deficiency n = bodyBarDim n * ((V(G).ncard : ℤ) - 1) := by
  rw [hB.ncard]; exact G.rank_add_deficiency_eq n hD hne

/-- **A spanning `0`-dof subgraph of a minimal `0`-dof-graph is the graph** (a step of
`lem:claim-6-6`): for `D ≥ 1`, if `G` is a minimal `0`-dof-graph and `G'' ≤ G` is a `0`-dof-graph
with `V(G'') = V(G)`, then `G = G''`. It is the step "the minimality of `G` implies `G = G''`" of
Katoh and Tanigawa's proof of their Claim 6.6 (2011, p. 676), which
`exists_degree_two_removeVertex_of_no_simple_contraction` takes.

Suppose that `g ∈ E(G) ∖ E(G'')`, and let `B''` be a base of `M(G̃'')`. It is independent in
`M(G̃)` (`matroidMG_restrict_mulTilde`). As `G''` and `G` are `0`-dof-graphs on the same vertices,
KT eq. (2.4) (`isBase_ncard_add_deficiency_eq`, `rank_add_deficiency_eq`) gives
`|B''| = D(|V(G)| - 1) = rank M(G̃)`, so `B''` is a base of `M(G̃)`. As `G` is minimal, `B''` meets
the copies `g̃` of `g`; but `B'' ⊆ E(G̃'')`, so `g ∈ E(G'')`. -/
theorem eq_of_isMinimalKDof_of_le_of_vertexSet_eq_of_isKDof [DecidableEq β] [Finite α]
    [Finite β] {G G'' : Graph α β} {n : ℕ}
    (hD : 1 ≤ bodyBarDim n) (hG : G.IsMinimalKDof n 0) (hle : G'' ≤ G)
    (hV : V(G'') = V(G)) (h0 : G''.IsKDof n 0) : G = G'' := by
  -- Apply `ext_of_le_le`: it suffices to show `E(G) = E(G'')`.
  refine ext_of_le_le le_rfl hle hV.symm ?_
  -- `E(G'') ⊆ E(G)` from `hle`; prove `E(G) ⊆ E(G'')` by contradiction.
  apply (Set.Subset.antisymm hle.edgeSet_mono _).symm
  by_contra hlt
  -- There exists `g ∈ E(G) ∖ E(G'')`.
  obtain ⟨g, hg, hgne⟩ := Set.not_subset.mp hlt
  -- `V(G).Nonempty`: derive from `g ∈ E(G)`.
  have hne_G : V(G).Nonempty := by
    obtain ⟨x, _, hlink⟩ := G.exists_isLink_of_mem_edgeSet hg
    exact ⟨x, hlink.left_mem⟩
  have hne_G'' : V(G'').Nonempty := hV ▸ hne_G
  -- Get a base `B''` of `M(G̃'')`.
  have hMFin : (G.matroidMG n).Finite := Matroid.finite_of_finite (M := G.matroidMG n)
  obtain ⟨B'', hB''⟩ := (G''.matroidMG n).exists_isBase
  -- `B''` is `M(G̃)`-independent via the restriction identity `M(G̃) ↾ E(G̃'') = M(G̃'')`.
  have hBindep : (G.matroidMG n).Indep B'' := by
    have hrestr : ((G.matroidMG n) ↾ E(G''.mulTilde n)).Indep B'' := by
      rw [matroidMG_restrict_mulTilde hle]; exact hB''.indep
    exact (restrict_indep_iff.mp hrestr).1
  -- `|B''| = D·(|V(G)| − 1)`: the 0-dof size count on `G''` with `|V(G'')| = |V(G)|`.
  have hBsize : (B''.ncard : ℤ) = (bodyBarDim n : ℤ) * ((V(G).ncard : ℤ) - 1) := by
    have heq := G''.isBase_ncard_add_deficiency_eq n hD hne_G'' hB''
    rw [h0, hV] at heq; linarith
  -- `rank M(G̃) = D·(|V(G)| − 1)` since `G` is `0`-dof.
  have hrank_D : (G.matroidMG n).rank + (0 : ℤ) =
      bodyBarDim n * ((V(G).ncard : ℤ) - 1) := by
    have heq' := G.rank_add_deficiency_eq n hD hne_G
    rw [hG.deficiency_eq] at heq'; linarith
  -- `B''` is a base of `M(G̃)`.
  have hBbase : (G.matroidMG n).IsBase B'' := by
    apply hBindep.isBase_of_ncard
    have hpos : 0 ≤ (bodyBarDim n : ℤ) * ((V(G).ncard : ℤ) - 1) := by linarith [hrank_D]
    zify [Int.toNat_of_nonneg hpos]
    linarith [hBsize, hrank_D]
  -- Minimality of `G`: `B'' ∩ ẽ_g ≠ ∅`.
  obtain ⟨p, hpB'', hpe⟩ := hG.2 B'' hBbase g hg
  -- But `p ∈ B'' ⊆ E(G̃'')`, so `p.1 ∈ E(G'')`, contradicting `g ∉ E(G'')`.
  have hpGS : p ∈ E(G''.mulTilde n) := hB''.subset_ground hpB''
  rw [mem_edgeSet_mulTilde] at hpGS
  rw [mem_edgeFiber] at hpe
  exact hgne (hpe ▸ hpGS)

/-- **A minimal spanning subgraph of the same deficiency** (`lem:minimal-kdof-spanning-subgraph`;
the first step of Katoh and Tanigawa's proof of their Theorem 5.6, 2011, p. 670): for `D ≥ 1` and
`V(G)` nonempty, `G` has a subgraph `G' ≤ G` with `V(G') = V(G)` that is a minimal
`def(G̃)`-dof-graph. Katoh and Tanigawa delete edges while the deficiency stays the same.
`subgraph_minimality` (KT Lemma 3.3) needs `G` minimal already.

Among the sets `F ⊆ E(G)` with `def((G ↾ F)~) = def(G̃)`, such as `E(G)`, choose one, `F₀`, of
least size (`Set.exists_min_image`; `β` is finite), and let `G' = G ↾ F₀`. If a base `B` of
`M(G̃')` missed the copies `ẽ` of an edge `e` of `G'`, then `B ⊆ E(G̃'')` for
`G'' = G' ↾ (F₀ ∖ {e})`, and `B` would be independent in `M(G̃'')`
(`matroidMG_restrict_mulTilde`). KT eq. (2.4) (`isBase_ncard_add_deficiency_eq`,
`rank_add_deficiency_eq`) would give `def(G̃'') ≤ def(G̃')`, and deleting an edge does not lower
the deficiency (`deficiency_le_deficiency_of_le_vertexSet_eq`), so `F₀ ∖ {e}` would keep the
deficiency of `G`, against the choice of `F₀`. -/
theorem exists_isMinimalKDof_spanning_subgraph [DecidableEq β] [Finite α] [Finite β]
    (G : Graph α β) (n : ℕ) (hD : 1 ≤ bodyBarDim n) (hne : V(G).Nonempty) :
    ∃ G' : Graph α β, G' ≤ G ∧ V(G') = V(G) ∧
      G'.IsMinimalKDof n (G.deficiency n) := by
  classical
  -- Edge subsets of `E(G)` whose restriction keeps the deficiency. `F = E(G)` is in the set.
  set S : Set (Set β) := {F | F ⊆ E(G) ∧ (G ↾ F).deficiency n = G.deficiency n} with hS_def
  have hEG : (G ↾ E(G)).deficiency n = G.deficiency n := by rw [restrict_self]
  have hSne : S.Nonempty := ⟨E(G), subset_rfl, hEG⟩
  -- Pick `F₀ ∈ S` of minimal cardinality.
  obtain ⟨F₀, ⟨hF₀sub, hF₀def⟩, hF₀min⟩ :=
    Set.exists_min_image S Set.ncard (Set.toFinite S) hSne
  refine ⟨G ↾ F₀, restrict_le, vertexSet_restrict .., ?_, fun B hB e he ↦ ?_⟩
  · -- `def((G ↾ F₀)~) = def(G̃)` is the selection predicate.
    exact hF₀def
  -- Base/fiber meeting: a base `B` of `M((G ↾ F₀)~)` meets the fiber of every edge `e ∈ F₀`.
  set G' := G ↾ F₀ with hG'_def
  have hG'le : G' ≤ G := restrict_le
  have hVG' : V(G') = V(G) := vertexSet_restrict ..
  have hEG' : E(G') = F₀ := by rw [hG'_def, edgeSet_restrict, Set.inter_eq_right.mpr hF₀sub]
  have hne' : V(G').Nonempty := hVG' ▸ hne
  -- Suppose for contradiction `B` avoids the fiber `ẽ`.
  by_contra hBe
  rw [Set.not_nonempty_iff_eq_empty] at hBe
  -- The de-edged graph `G'' := G' ↾ (F₀ ∖ {e})`, a subgraph of `G'` whose edge set drops `e`.
  set F₁ : Set β := F₀ \ {e} with hF₁_def
  have heF₀ : e ∈ F₀ := hEG' ▸ he
  set G'' := G' ↾ F₁ with hG''_def
  have hG''le : G'' ≤ G' := restrict_le
  have hVG'' : V(G'') = V(G) := by rw [hG''_def, vertexSet_restrict, hVG']
  have hne'' : V(G'').Nonempty := hVG'' ▸ hne
  have hEG'' : E(G'') = F₁ := by
    rw [hG''_def, edgeSet_restrict, hEG', Set.inter_eq_right.mpr Set.sdiff_subset]
  -- `B ⊆ E(G̃'')`: every `p ∈ B` has `p.1 ∈ F₀` (ground) and `p.1 ≠ e` (avoids the fiber).
  have hBfiber : ∀ p ∈ B, p ∉ edgeFiber e n := fun p hp hpf ↦ by
    rw [Set.eq_empty_iff_forall_notMem] at hBe; exact hBe p ⟨hp, hpf⟩
  have hBsub'' : B ⊆ E(G''.mulTilde n) := by
    intro p hp
    have hpG' : p ∈ E(G'.mulTilde n) := hB.subset_ground hp
    rw [mem_edgeSet_mulTilde] at hpG' ⊢
    rw [hEG''] at *
    refine ⟨hEG' ▸ hpG', fun (hpe : p.1 = e) ↦ ?_⟩
    exact hBfiber p hp (by rw [mem_edgeFiber]; exact hpe)
  -- `B` is `M(G̃'')`-independent via the restriction identity `M(G̃') ↾ E(G̃'') = M(G̃'')`.
  have hBindep'' : (G''.matroidMG n).Indep B := by
    have hrestr : ((G'.matroidMG n) ↾ E(G''.mulTilde n)).Indep B :=
      restrict_indep_iff.mpr ⟨hB.indep, hBsub''⟩
    rwa [matroidMG_restrict_mulTilde hG''le] at hrestr
  -- `|B| = rank M(G̃') = D(|V| − 1) − def(G̃')`.
  have hBcard : (B.ncard : ℤ) = bodyBarDim n * ((V(G).ncard : ℤ) - 1) - G'.deficiency n := by
    have := G'.isBase_ncard_add_deficiency_eq n hD hne' hB
    rw [hVG'] at this; linarith
  -- `def(G̃'') ≥ def(G̃')` (fewer edges at fixed vertex set raise the deficiency).
  have hdef_ge : G'.deficiency n ≤ G''.deficiency n :=
    deficiency_le_deficiency_of_le_vertexSet_eq hD hG''le (hVG''.trans hVG'.symm)
  -- `|B| ≤ rank M(G̃'') = D(|V| − 1) − def(G̃'')`, so `def(G̃'') ≤ def(G̃')`, forcing equality.
  have : (G''.matroidMG n).Finite := Matroid.finite_of_finite (M := G''.matroidMG n)
  have hBrank : (B.ncard : ℤ) ≤ (G''.matroidMG n).rank := by exact_mod_cast hBindep''.ncard_le_rank
  have hrankdef'' : ((G''.matroidMG n).rank : ℤ) + G''.deficiency n =
      bodyBarDim n * ((V(G).ncard : ℤ) - 1) := by
    have := G''.rank_add_deficiency_eq n hD hne''; rw [hVG''] at this; exact this
  have hdef_le : G''.deficiency n ≤ G'.deficiency n := by
    have : (B.ncard : ℤ) ≤ bodyBarDim n * ((V(G).ncard : ℤ) - 1) - G''.deficiency n := by
      linarith [hBrank, hrankdef'']
    linarith [hBcard]
  have hdef_eq : G''.deficiency n = G'.deficiency n := le_antisymm hdef_le hdef_ge
  -- So `F₁ = F₀ ∖ {e} ∈ S` with strictly smaller cardinality — contradicting minimality.
  have hF₁S : F₁ ∈ S := by
    refine ⟨Set.sdiff_subset.trans hF₀sub, ?_⟩
    have : (G ↾ F₁).deficiency n = G''.deficiency n := by
      rw [hG''_def, hG'_def, restrict_restrict, Set.inter_eq_right.mpr Set.sdiff_subset]
    rw [this, hdef_eq, hF₀def]
  have hlt : F₁.ncard < F₀.ncard := by
    rw [hF₁_def]
    exact Set.ncard_sdiff_singleton_lt_of_mem heF₀ (Set.toFinite F₀)
  exact absurd (hF₀min F₁ hF₁S) (not_le.mpr hlt)

/-- **A base of `M(H̃)` for a `0`-dof-graph `H` is `D` forests with `D(|V(H)| - 1)` edges** (a
step of `lem:deficiency-zero-iff-tree-packing`): for `D ≥ 2` (`[NeZero (bodyHingeMult n)]`, that
is, `D - 1 ≥ 1`) and `V(H)` nonempty, some base `B` of `M(H̃)` has `H̃ ↾ B` a union of `D`
edge-disjoint forests and `|B| = D(|V(H)| - 1)`. Every base will do: it is independent, so
`H̃ ↾ B` is `(D, D)`-sparse (`matroidMG_indep_iff`) and is a union of `D` forests
(`tutte_nash_williams`), and KT eq. (2.4) (`isBase_ncard_add_deficiency_eq`) gives its size. The
restriction to `B` is needed: `H̃` itself need not be sparse, as `H` may have edges that a minimal
`0`-dof-graph would not. -/
theorem IsKDof.exists_isBase_isForestPacking [DecidableEq β] [Finite α] [Finite β]
    {H : Graph α β} {n : ℕ} [NeZero (bodyHingeMult n)]
    (hrig : H.IsKDof n 0) (hne : V(H).Nonempty) :
    ∃ B, (H.matroidMG n).IsBase B ∧ ((H.mulTilde n) ↾ B).IsForestPacking (bodyBarDim n) ∧
      (B.ncard : ℤ) = bodyBarDim n * ((V(H).ncard : ℤ) - 1) := by
  have hmult : 1 ≤ bodyHingeMult n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hD : 1 ≤ bodyBarDim n := by rw [bodyHingeMult] at hmult; omega
  obtain ⟨B, hB⟩ := (H.matroidMG n).exists_isBase
  refine ⟨B, hB, ?_, ?_⟩
  · -- `B` independent ⟹ `H̃ ↾ B` is `(D,D)`-sparse ⟹ packs `D` edge-disjoint forests.
    rw [tutte_nash_williams]
    exact ((matroidMG_indep_iff H n).mp hB.indep).2
  · -- `|B| = rank M(H̃) = D(|V(H)| − 1)` since `def(H̃) = 0`.
    have hcount := H.isBase_ncard_add_deficiency_eq n hD hne hB
    rw [hrig] at hcount
    linarith

/-! ## Deficiency zero and `D` edge-disjoint spanning trees (`lem:deficiency-zero-iff-tree-packing`)

For `D ≥ 2` and `V(G)` nonempty, `def(G̃) = 0` iff `G̃` contains `D` edge-disjoint spanning trees:
KT Proposition 2.2, the theorem of Tutte and Nash-Williams, at `G̃` (Katoh–Tanigawa 2011, p. 655).
`cor:bodyhinge-generic-tree-packing` applies it. If `def(G̃) = 0`, a base of `M(G̃)` has
`D(|V(G)| - 1)` elements (`IsKDof.exists_isBase_isForestPacking`) and is `(D, D)`-sparse, so
`G̃` restricted to it is `(D, D)`-tight; it is then connected (`IsTight.connected`), and its `D`
maximal forests are spanning trees (`isSpanningTreePacking_of_isTight`). Conversely, the union of
`D` edge-disjoint spanning trees is independent in `M(G̃)` with `D(|V(G)| - 1)` elements, so it is a
base, and KT eq. (2.4) gives `def(G̃) = 0`. -/

/-- **`def(G̃) = 0` iff `G̃` contains `D` edge-disjoint spanning trees**
(`lem:deficiency-zero-iff-tree-packing`; KT Proposition 2.2 at `G̃`, Katoh–Tanigawa 2011, p. 655),
for `D ≥ 2` (`[NeZero (bodyHingeMult n)]`) and `V(G)` nonempty. The trees are spanning subgraphs
`Ts i ≤s G̃` with pairwise disjoint edge sets; the section docstring gives the proof. -/
theorem deficiency_eq_zero_iff_exists_spanningTrees [Finite α] [Finite β]
    (G : Graph α β) (n : ℕ) [NeZero (bodyHingeMult n)] (hne : V(G).Nonempty) :
    G.deficiency n = 0 ↔
      ∃ Ts : Fin (bodyBarDim n) → Graph α (β × Fin (bodyHingeMult n)),
        (∀ i, Ts i ≤s G.mulTilde n) ∧ (∀ i, (Ts i).IsTree) ∧
          Pairwise (Function.onFun Disjoint fun i => E(Ts i)) := by
  classical
  have hmult : 1 ≤ bodyHingeMult n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hD : 1 ≤ bodyBarDim n := by rw [bodyHingeMult] at hmult; omega
  constructor
  · intro hdef
    obtain ⟨B, hB, -, hcardZ⟩ := IsKDof.exists_isBase_isForestPacking hdef hne
    set H := (G.mulTilde n) ↾ B with hHdef
    have hVH : V(H) = V(G) := by rw [hHdef, vertexSet_restrict, mulTilde]; rfl
    have hBsub : B ⊆ E(G.mulTilde n) := ((matroidMG_indep_iff G n).mp hB.indep).1
    have hEH : E(H) = B := by rw [hHdef, edgeSet_restrict, Set.inter_eq_right.mpr hBsub]
    have hneH : V(H).Nonempty := hVH ▸ hne
    have hsparseH : H.IsSparse (bodyBarDim n) (bodyBarDim n) := by
      rw [hHdef]; exact ((matroidMG_indep_iff G n).mp hB.indep).2
    have htightcount0 : B.ncard + bodyBarDim n = bodyBarDim n * V(G).ncard := by
      have hZ : (B.ncard : ℤ) + bodyBarDim n = bodyBarDim n * V(G).ncard := by
        rw [hcardZ]; ring
      exact_mod_cast hZ
    have htightcount : E(H).ncard + bodyBarDim n = bodyBarDim n * V(H).ncard := by
      rw [hEH, hVH]; exact htightcount0
    have htight : H.IsTight (bodyBarDim n) (bodyBarDim n) := ⟨hsparseH, htightcount⟩
    have hconn : H.Connected := htight.connected hD hneH
    obtain ⟨Fs, hcover, hdisjFs, hmaxacyc⟩ := isSpanningTreePacking_of_isTight hconn htight
    have hFsub : ∀ i, Fs i ⊆ B := fun i => by rw [← hEH]; exact (hmaxacyc i).subset
    have hFsubG : ∀ i, Fs i ⊆ E(G.mulTilde n) := fun i => (hFsub i).trans hBsub
    have hFsEdge : ∀ i, E((G.mulTilde n) ↾ Fs i) = Fs i := fun i => by
      rw [edgeSet_restrict]; exact Set.inter_eq_right.mpr (hFsubG i)
    refine ⟨fun i => (G.mulTilde n) ↾ (Fs i),
      fun i => ⟨restrict_le, vertexSet_restrict (G.mulTilde n) (Fs i)⟩, fun i => ?_,
      fun i j hij => ?_⟩
    · change (G.mulTilde n ↾ (Fs i)).IsTree
      have heq : H ↾ (Fs i) = (G.mulTilde n) ↾ (Fs i) := by
        rw [hHdef, restrict_restrict, Set.inter_eq_right.mpr (hFsub i)]
      rw [← heq]
      exact Connected.isTree_of_maximal_isAcyclicSet hconn (hmaxacyc i)
    · simp only [Function.onFun, hFsEdge]
      exact hdisjFs hij
  · rintro ⟨Ts, hspan, htree, hdisjTs⟩
    have hVeq : V(G.mulTilde n) = V(G) := by rw [mulTilde]; rfl
    have hMTfin : (G.mulTilde n).Finite :=
      { edgeSet_finite := Set.toFinite _, vertexSet_finite := Set.toFinite _ }
    have hTfin : ∀ i, (Ts i).Finite := fun i => hMTfin.mono (hspan i).le
    have hTcard : ∀ i, (E(Ts i)).ncard = V(G).ncard - 1 := by
      intro i
      have := hTfin i
      have hnv := (htree i).ncard_vertexSet
      rw [(hspan i).vertexSet_eq, hVeq] at hnv
      omega
    have hacyc : ∀ i, (G.mulTilde n).IsAcyclicSet (E(Ts i)) := by
      intro i
      have hself : (Ts i).IsAcyclicSet (E(Ts i)) := by
        rw [isAcyclicSet_iff]
        exact ⟨subset_rfl, by rw [restrict_self]; exact (htree i).isForest⟩
      exact hself.mono (hspan i).le
    have hBsub : (⋃ i, E(Ts i)) ⊆ E(G.mulTilde n) := Set.iUnion_subset fun i => (hacyc i).subset
    have hBunion :
        (Matroid.Union (fun _ : Fin (bodyBarDim n) => (G.mulTilde n).cycleMatroid)).Indep
          (⋃ i, E(Ts i)) := by
      rw [Matroid.union_indep_iff]
      exact ⟨fun i => E(Ts i), rfl, fun i => by rw [cycleMatroid_indep]; exact hacyc i⟩
    have hBindep : (G.matroidMG n).Indep (⋃ i, E(Ts i)) := by
      rw [matroidMG, Matroid.restrict_indep_iff]
      exact ⟨hBunion, hBsub⟩
    have hBcard : (⋃ i, E(Ts i)).ncard = bodyBarDim n * (V(G).ncard - 1) := by
      rw [Set.ncard_iUnion_of_fintype (fun i => Set.toFinite _) hdisjTs]
      simp [hTcard, Finset.sum_const, Finset.card_univ]
    have hcast : ((⋃ i, E(Ts i)).ncard : ℤ) = (bodyBarDim n : ℤ) * ((V(G).ncard : ℤ) - 1) := by
      have h1 : 0 < V(G).ncard := by rw [Set.ncard_pos]; exact hne
      rw [hBcard]
      push_cast [Nat.cast_sub h1]
      ring
    have hrle : (G.matroidMG n).rank ≤ (⋃ i, E(Ts i)).ncard := by
      have heq := G.rank_add_deficiency_eq n hD hne
      have hdefnn := G.deficiency_nonneg n hne
      have : ((G.matroidMG n).rank : ℤ) ≤ ((⋃ i, E(Ts i)).ncard : ℤ) := by
        rw [hcast]; linarith
      exact_mod_cast this
    have hBbase : (G.matroidMG n).IsBase (⋃ i, E(Ts i)) := hBindep.isBase_of_ncard hrle
    have heqb := G.isBase_ncard_add_deficiency_eq n hD hne hBbase
    rw [hcast] at heqb
    linarith

end Graph
