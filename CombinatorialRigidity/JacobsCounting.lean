/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
-- Plain (legacy) `import`, not the module system: `Molecular/{Deficiency,Molecule/Carrier}.lean`
-- are not `module` files, and a `module` file cannot import a non-`module` one. Do not convert
-- this file to `module`/`public import` until those dependencies are converted first.
module

public import CombinatorialRigidity.Jacobs
public import CombinatorialRigidity.Molecular.Deficiency
public import CombinatorialRigidity.Molecular.Molecule.Carrier

/-!
# The counting bound for Laman squares (`sec:jacobs-counting`)

Jackson–Jordán 2008 (*On the rigidity of molecular graphs*, Combinatorica **28**) prove their
counting bound (Theorem 5.3) by classifying the edges of `G²` against a partition of `V` that
attains the deficiency, and counting each class part by part. This file proves the bound
(`laman_square_count`, `thm:laman-square-count`); the blueprint presents it in
`sec:jacobs-counting`.

## Tight partitions of a simple graph

A tight partition of `V` at `D = 6` is a labeling `f : V → V` that is a tight partition of the
multigraph `G.shadowGraph` of `lem:molecule-graph-carrier` at `n = 3` (where
`bodyBarDim 3 = 6`); the predicate is `SimpleGraph.IsSquareTightPartition`. That multigraph has
vertex set `univ` and the adjacencies of `G` (`shadowGraph_adj_iff`), so the lemmas on tight
partitions of `Molecular/Deficiency.lean`, stated for every `D` over `Graph α β`, transport to
`SimpleGraph` and `f : V → V`: the uniqueness of a common neighbor
(`IsSquareTightPartition.eq_of_common_nbr`), the parts (`IsSquareTightPartition.parts`), and the
two consequences of `lem:tight-partition-cross-pair-mult` and `lem:tight-partition-subfamily`
that `lem:singleton-part-neighborhood` uses (`IsSquareTightPartition.not_adj_adj_of_same_part`,
`IsSquareTightPartition.not_adj_triangle`).

## The four edge classes

Following Jackson–Jordán §5, an edge `e = uw` of `G²` is classified by whether its endpoints
share a part (`(e.map f).IsDiag`, i.e. `f u = f w`) and whether `e` is an edge of `G`:

* `squareInPartEdges` — edges of `G²` inside a part;
* `squareGCrossEdges` — edges of `G` joining distinct parts (their number is `d_G(P)`);
* `squareCrossEdges` — **cross edges**: edges of `G²` joining distinct parts that are not edges
  of `G`. Such an edge has a common neighbor (`exists_apex_of_mem_squareCrossEdges`), unique
  for a tight partition (`IsSquareTightPartition.eq_of_common_nbr`).

A cross edge `uw` with common neighbor `v` is **normal** if `v` shares a part with an endpoint
(`f v ∈ e.map f`) and **special** otherwise: `squareNormalCrossEdges`, `squareSpecialCrossEdges`.
The classes are defined for every partition, from *some* common neighbor
(`fmlnote:normal-cross-split`).

## Main results

* `SimpleGraph.square_edgeSet_eq_union` — `E(G²)` is the union of the in-part, `G`-cross and
  cross classes, pairwise disjoint (`disjoint_inPart_gCross`, `disjoint_inPart_cross`,
  `disjoint_gCross_cross`). With `squareCrossEdges_eq_union` (normal and special cross edges),
  `squareNormalCrossEdges_disjoint_special` (disjoint for a tight partition),
  `squareGCrossEdges_ncard_eq_crossingEdges` (the `G`-cross class numbers `d_G(P)`), and
  `squareSpecialCrossEdges_singleton_part`, `squareNormalCrossEdges_part_three_le` (where the
  common neighbor of a special and of a normal cross edge lies), this is
  `lem:square-cross-classification`.
* `SimpleGraph.IsSquareTightPartition.mem_squareSpecialCrossEdges_of_singleton_part` and
  `SimpleGraph.exists_unique_singleton_part_of_mem_squareSpecialCrossEdges` — the special cross
  edges at a singleton part and their converse (`lem:singleton-part-neighborhood`,
  `lem:singleton-part-converse`; JJ eqs. (5) and (7)).
* `SimpleGraph.IsSquareTightPartition.ncard_normalCrossEdgesRootedAt_eq_two_mul_gCutEdges` — a
  part `A` with `|A| ≥ 3` roots exactly `2 d_G(A)` normal cross edges (`lem:normal-cross-count`;
  JJ eq. (6)), from the lemmas `lem:normal-cross-count-rooted` to
  `lem:normal-cross-count-partition`.
* `SimpleGraph.laman_square_count` — **the counting bound for Laman squares** (JJ Theorem 5.3,
  `thm:laman-square-count`): for `G` of minimum degree at least two on a finite `V` with `G²`
  Laman, `|E(G²)| ≤ 3|V| - 6 - def(G̃)`.

## The proof of the bound

The arithmetic of `thm:laman-square-count` needs the finite set of labels of a partition
(`partLabels`), two handshakes (`sum_gCutEdges_eq_two_mul_squareGCrossEdges`,
`sum_ncard_eq_card`), the bound on the edges of `G²` inside a part (`edgesIn_square_part_le` for
a part of at least three vertices, `edgesIn_square_singleton_part_eq_zero` for a singleton), and
a decomposition over `partLabels f` of three of the classes, each by an `_eq_biUnion`, a
`_pairwiseDisjoint` and a sum lemma: the in-part class (`squareInPartEdges_eq_biUnion`), the
normal cross edges (`squareNormalCrossEdges_eq_biUnion`, through the edges **rooted** at a part,
`squareNormalCrossEdgesRootedAt`), and the special ones (`squareSpecialCrossEdges_eq_biUnion`,
through `squareSpecialCrossEdgesRootedAt`, which indexes a special cross edge by the label of its
common neighbor, as `def:rooted-cross-edges` does). Four facts at one part
(`gCutEdges_singleton_part_ncard_eq_degree`,
`squareNormalCrossEdgesRootedAt_eq_empty_of_lt_three`,
`squareSpecialCrossEdgesRootedAt_eq_empty_of_three_le`,
`IsSquareTightPartition.squareSpecialCrossEdgesRootedAt_eq_edgesIn_neighborSet`) and the
dichotomy of the parts (`IsSquareTightPartition.ncard_eq_one_or_three_le`) give the inequality at
a part, `IsSquareTightPartition.perPart_le`, which `IsSquareTightPartition.sum_perPart_le` sums.
The classification's count (`square_ncard_eq_sum_classes`) and the number of parts
(`partLabels_card_eq_numParts`) close the arithmetic in `SimpleGraph.laman_square_count`. These
are steps of the proof of `thm:laman-square-count`; no other node states them.
-/

@[expose] public section

open scoped Graph

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-! ## Tight partitions of a simple graph -/

/-- **A tight partition of `V` at `D = 6`**: a labeling `f : V → V` that is a tight partition
(`Graph.IsTightPartition`, `def:tight-partition`) of the multigraph `G.shadowGraph` of
`lem:molecule-graph-carrier` at `n = 3`, where `bodyBarDim 3 = 6` is the `D` of
`def:D-deficiency`. This is the partition against which the counting bound (JJ Theorem 5.3)
classifies the edges of `G²`. -/
def IsSquareTightPartition (G : SimpleGraph V) (f : V → V) : Prop :=
  G.shadowGraph.IsTightPartition 3 f

/-- Adjacency in `G.shadowGraph` is exactly adjacency in `G`: `G.shadowGraph.Adj u v ↔ G.Adj u v`.
Unfolds `Graph.Adj` to `∃ e, IsLink e u v` and applies `shadowGraph_isLink_iff`. -/
theorem shadowGraph_adj_iff (u v : V) : G.shadowGraph.Adj u v ↔ G.Adj u v := by
  rw [Graph.Adj]
  exact shadowGraph_isLink_iff G u v

/-- **Uniqueness of the common neighbor of a cross pair**, in `SimpleGraph` terms
(`lem:tight-partition-cross-pair-nbr` for `G.shadowGraph`). Two vertices `u, w` in distinct parts of
a tight partition (`f u ≠ f w`) have at most one common neighbor: any two common neighbors `v, v'`
coincide. This makes the common neighbor of a cross edge — and hence the normal/special dichotomy —
well defined.

`bodyBarDim 3 = 6 ≥ 5` supplies the `D ≥ 5` hypothesis of `Graph.IsTightPartition.eq_of_common_nbr`;
`G.shadowGraph` is simple, and its adjacencies are `G`'s (`shadowGraph_adj_iff`). -/
theorem IsSquareTightPartition.eq_of_common_nbr [Finite V] {f : V → V}
    (hf : G.IsSquareTightPartition f) {u w v v' : V} (hfuw : f u ≠ f w)
    (huv : G.Adj u v) (hwv : G.Adj w v) (huv' : G.Adj u v') (hwv' : G.Adj w v') :
    v = v' :=
  Graph.IsTightPartition.eq_of_common_nbr hf (by decide) G.shadowGraph_simple hfuw
    ((shadowGraph_adj_iff u v).mpr huv) ((shadowGraph_adj_iff v w).mpr hwv.symm)
    ((shadowGraph_adj_iff u v').mpr huv') ((shadowGraph_adj_iff v' w).mpr hwv'.symm)

/-- For the two lemmas below: an edge of `G` between vertices with distinct labels in `S` is a
crossing edge of `G.shadowGraph` within `S`. -/
private theorem mem_crossingEdgesWithin_shadowGraph {f : V → V} {S : Set V} {x y : V}
    (hxy : G.Adj x y) (hx : f x ∈ S) (hy : f y ∈ S) (hne : f x ≠ f y) :
    (Sum.inl s(x, y) : Sym2 V ⊕ Fin (6 * (Nat.card V - 1) + 1)) ∈
      G.shadowGraph.crossingEdgesWithin f S :=
  ⟨⟨x, y, hxy, rfl⟩, x, y, ⟨hxy, rfl⟩, hx, hy, hne⟩

/-- **Two neighbors in one other part** (a step of `lem:singleton-part-neighborhood` and
`lem:normal-cross-count-producer`, by `lem:tight-partition-cross-pair-mult`). If `v` is adjacent
to two distinct vertices `u, w` (`u ≠ w`) that share a part (`f u = f w`) other than `v`'s own
(`f v ≠ f u`), tightness is violated: the edges `vu`, `vw` both join the parts `f v` and `f u`,
exceeding the bound of one of `Graph.IsTightPartition.crossingEdgesWithin_pair_le_one`
(`D = 6 ≥ 3`). -/
theorem IsSquareTightPartition.not_adj_adj_of_same_part [Finite V] {f : V → V}
    (hf : G.IsSquareTightPartition f) {u v w : V} (hfvu : f v ≠ f u) (hfuw : f u = f w)
    (hvu : G.Adj v u) (hvw : G.Adj v w) (huw : u ≠ w) : False := by
  have hfvw : f v ≠ f w := by rw [← hfuw]; exact hfvu
  have hle := Graph.IsTightPartition.crossingEdgesWithin_pair_le_one hf (by decide)
    (⟨v, Set.mem_univ v, rfl⟩ : f v ∈ f '' V(G.shadowGraph))
    (⟨u, Set.mem_univ u, rfl⟩ : f u ∈ f '' V(G.shadowGraph)) hfvu
  have h1 := mem_crossingEdgesWithin_shadowGraph (S := {f v, f u}) hvu (Set.mem_insert _ _)
    (Set.mem_insert_iff.mpr (Or.inr rfl)) hfvu
  have h2 := mem_crossingEdgesWithin_shadowGraph (S := {f v, f u}) hvw (Set.mem_insert _ _)
    (Set.mem_insert_iff.mpr (Or.inr hfuw.symm)) hfvw
  have hne : (Sum.inl s(v, u) : Sym2 V ⊕ Fin (6 * (Nat.card V - 1) + 1)) ≠ Sum.inl s(v, w) := by
    intro h
    rw [Sum.inl.injEq] at h
    rcases Sym2.eq_iff.mp h with ⟨_, huw'⟩ | ⟨hvw', _⟩
    · exact huw huw'
    · exact hvw.ne hvw'
  have hsub : ({Sum.inl s(v, u), Sum.inl s(v, w)} :
      Set (Sym2 V ⊕ Fin (6 * (Nat.card V - 1) + 1))) ⊆
      G.shadowGraph.crossingEdgesWithin f {f v, f u} := by
    rintro e (rfl | rfl)
    exacts [h1, h2]
  have hcard : ({Sum.inl s(v, u), Sum.inl s(v, w)} :
      Set (Sym2 V ⊕ Fin (6 * (Nat.card V - 1) + 1))).ncard = 2 := Set.ncard_pair hne
  have hle2 := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

/-- **No triangle across three parts** (a step of `lem:singleton-part-neighborhood`, by
`lem:tight-partition-subfamily`). Three pairwise adjacent vertices `u, v, w` with pairwise
distinct labels violate tightness: the edges `uv`, `vw`, `uw` all join members of the subfamily
`{f u, f v, f w}`, exceeding the bound of `Graph.IsTightPartition.subfamily_le` (`(D-1)*3 ≤ D*2`
forces `D ≤ 3`, against `D = 6`). This is the step of `lem:singleton-part-neighborhood` that
shows two neighbors of a singleton part nonadjacent. -/
theorem IsSquareTightPartition.not_adj_triangle [Finite V] {f : V → V}
    (hf : G.IsSquareTightPartition f) {u v w : V}
    (hfuv : f u ≠ f v) (hfvw : f v ≠ f w) (hfuw : f u ≠ f w)
    (huv : G.Adj u v) (hvw : G.Adj v w) (huw : G.Adj u w) : False := by
  have huv_ne : u ≠ v := huv.ne
  have hvw_ne : v ≠ w := hvw.ne
  have huw_ne : u ≠ w := huw.ne
  have hS : ({f u, f v, f w} : Set V) ⊆ f '' V(G.shadowGraph) := by
    rintro x (rfl | rfl | rfl)
    exacts [⟨u, Set.mem_univ u, rfl⟩, ⟨v, Set.mem_univ v, rfl⟩, ⟨w, Set.mem_univ w, rfl⟩]
  have hScard : ({f u, f v, f w} : Set V).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨f u, f v, f w, hfuv, hfuw, hfvw, rfl⟩
  have hsub := Graph.IsTightPartition.subfamily_le hf hS (by rw [hScard]; omega)
  have h1 := mem_crossingEdgesWithin_shadowGraph (S := {f u, f v, f w}) huv
    (Set.mem_insert _ _) (Set.mem_insert_iff.mpr (Or.inr (Set.mem_insert _ _))) hfuv
  have h2 := mem_crossingEdgesWithin_shadowGraph (S := {f u, f v, f w}) hvw
    (Set.mem_insert_iff.mpr (Or.inr (Set.mem_insert _ _)))
    (Set.mem_insert_iff.mpr (Or.inr (Set.mem_insert_iff.mpr (Or.inr rfl)))) hfvw
  have h3 := mem_crossingEdgesWithin_shadowGraph (S := {f u, f v, f w}) huw
    (Set.mem_insert _ _)
    (Set.mem_insert_iff.mpr (Or.inr (Set.mem_insert_iff.mpr (Or.inr rfl)))) hfuw
  have h12 : (Sum.inl s(u, v) : Sym2 V ⊕ Fin (6 * (Nat.card V - 1) + 1)) ≠ Sum.inl s(v, w) := by
    intro h
    rw [Sum.inl.injEq] at h
    rcases Sym2.eq_iff.mp h with ⟨huv', _⟩ | ⟨huw', _⟩
    · exact huv_ne huv'
    · exact huw_ne huw'
  have h13 : (Sum.inl s(u, v) : Sym2 V ⊕ Fin (6 * (Nat.card V - 1) + 1)) ≠ Sum.inl s(u, w) := by
    intro h
    rw [Sum.inl.injEq] at h
    rcases Sym2.eq_iff.mp h with ⟨_, hvw'⟩ | ⟨huw', _⟩
    · exact hvw_ne hvw'
    · exact huw_ne huw'
  have h23 : (Sum.inl s(v, w) : Sym2 V ⊕ Fin (6 * (Nat.card V - 1) + 1)) ≠ Sum.inl s(u, w) := by
    intro h
    rw [Sum.inl.injEq] at h
    rcases Sym2.eq_iff.mp h with ⟨hvu', _⟩ | ⟨hvw', _⟩
    · exact huv_ne hvu'.symm
    · exact hvw_ne hvw'
  have hWsub : ({Sum.inl s(u, v), Sum.inl s(v, w), Sum.inl s(u, w)} :
      Set (Sym2 V ⊕ Fin (6 * (Nat.card V - 1) + 1))) ⊆
      G.shadowGraph.crossingEdgesWithin f {f u, f v, f w} := by
    rintro e (rfl | rfl | rfl)
    exacts [h1, h2, h3]
  have hWcard : ({Sum.inl s(u, v), Sum.inl s(v, w), Sum.inl s(u, w)} :
      Set (Sym2 V ⊕ Fin (6 * (Nat.card V - 1) + 1))).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨_, _, _, h12, h13, h23, rfl⟩
  have hWc := Set.ncard_le_ncard hWsub (Set.toFinite _)
  rw [hScard] at hsub
  have hD_eq : Graph.bodyBarDim 3 = 6 := by decide
  rw [hD_eq] at hsub
  push_cast at hsub
  have hke : (3 : ℤ) ≤ (G.shadowGraph.crossingEdgesWithin f {f u, f v, f w}).ncard := by
    have hke0 : (3 : ℕ) ≤ (G.shadowGraph.crossingEdgesWithin f {f u, f v, f w}).ncard := by
      rw [← hWcard]; exact hWc
    exact_mod_cast hke0
  nlinarith [hsub, hke]

/-! ## The four edge classes

An edge `e = s(u, w)` of `G²` has `(e.map f).IsDiag ↔ f u = f w` (its endpoints share a part)
and `e ∈ G.edgeSet ↔ G.Adj u w`. The classes below partition `E(G²)` by these two criteria. -/

/-- Edges of `G²` inside a part (`f u = f w`). -/
def squareInPartEdges (G : SimpleGraph V) (f : V → V) : Set (Sym2 V) :=
  {e ∈ G.square.edgeSet | (e.map f).IsDiag}

/-- Edges of `G` joining distinct parts. Their number is the chapter's `d_G(P)` (JJ write
`e_G(P)`). As `G` is a subgraph of `G²`, these are edges of `G²`. -/
def squareGCrossEdges (G : SimpleGraph V) (f : V → V) : Set (Sym2 V) :=
  {e ∈ G.edgeSet | ¬ (e.map f).IsDiag}

/-- **Cross edges**: edges of `G²` joining distinct parts that are not edges of `G`. A cross
edge's endpoints have a common neighbor, unique for a tight partition
(`exists_apex_of_mem_squareCrossEdges`, `IsSquareTightPartition.eq_of_common_nbr`). -/
def squareCrossEdges (G : SimpleGraph V) (f : V → V) : Set (Sym2 V) :=
  {e ∈ G.square.edgeSet | ¬ (e.map f).IsDiag ∧ e ∉ G.edgeSet}

/-- **Normal cross edges**: cross edges with a common neighbor `v` whose part contains an
endpoint (`f v ∈ e.map f`, i.e. `f v = f u` or `f v = f w`). -/
def squareNormalCrossEdges (G : SimpleGraph V) (f : V → V) : Set (Sym2 V) :=
  {e ∈ G.squareCrossEdges f | ∃ v, (∀ z ∈ e, G.Adj z v) ∧ f v ∈ e.map f}

/-- **Special cross edges**: cross edges with a common neighbor `v` in a part containing neither
endpoint (`f v ∉ e.map f`). -/
def squareSpecialCrossEdges (G : SimpleGraph V) (f : V → V) : Set (Sym2 V) :=
  {e ∈ G.squareCrossEdges f | ∃ v, (∀ z ∈ e, G.Adj z v) ∧ f v ∉ e.map f}

theorem mem_squareInPartEdges {f : V → V} {u w : V} :
    s(u, w) ∈ G.squareInPartEdges f ↔ G.square.Adj u w ∧ f u = f w := by
  simp only [squareInPartEdges, Set.mem_ofPred_eq, mem_edgeSet, Sym2.map_mk, Sym2.mk_isDiag_iff]

theorem mem_squareGCrossEdges {f : V → V} {u w : V} :
    s(u, w) ∈ G.squareGCrossEdges f ↔ G.Adj u w ∧ f u ≠ f w := by
  simp only [squareGCrossEdges, Set.mem_ofPred_eq, mem_edgeSet, Sym2.map_mk, Sym2.mk_isDiag_iff]

theorem mem_squareCrossEdges {f : V → V} {u w : V} :
    s(u, w) ∈ G.squareCrossEdges f ↔ G.square.Adj u w ∧ f u ≠ f w ∧ ¬ G.Adj u w := by
  simp only [squareCrossEdges, Set.mem_ofPred_eq, mem_edgeSet, Sym2.map_mk, Sym2.mk_isDiag_iff]

/-! ## The classification: the disjoint union

`E(G²)` splits into the in-part, `G`-cross, and cross classes (`square_edgeSet_eq_union`),
pairwise disjoint; the cross class splits further into normal and special
(`squareCrossEdges_eq_union`), disjointly for a tight partition. This is the first sentence of
`lem:square-cross-classification`; its *moreover* clause is the next section. -/

/-- Every cross edge has a common neighbor: a `G²`-edge that is not a `G`-edge joins two vertices
at graph distance exactly two, which by definition of the square share a neighbor in `G`. -/
theorem exists_apex_of_mem_squareCrossEdges {f : V → V} {e : Sym2 V}
    (h : e ∈ G.squareCrossEdges f) : ∃ v, ∀ z ∈ e, G.Adj z v := by
  induction e with | h u w =>
  simp only [squareCrossEdges, Set.mem_ofPred_eq, mem_edgeSet, square_adj] at h
  obtain ⟨⟨_, hor⟩, _, hnadj⟩ := h
  rcases hor with hadj | hcn
  · exact absurd hadj hnadj
  · obtain ⟨v, hv⟩ := hcn
    rw [mem_commonNeighbors] at hv
    exact ⟨v, by simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq]; exact ⟨hv.1, hv.2⟩⟩

theorem disjoint_inPart_gCross (f : V → V) :
    Disjoint (G.squareInPartEdges f) (G.squareGCrossEdges f) := by
  rw [Set.disjoint_left]
  rintro e ⟨_, hdiag⟩ ⟨_, hndiag⟩
  exact hndiag hdiag

theorem disjoint_inPart_cross (f : V → V) :
    Disjoint (G.squareInPartEdges f) (G.squareCrossEdges f) := by
  rw [Set.disjoint_left]
  rintro e ⟨_, hdiag⟩ ⟨_, hndiag, _⟩
  exact hndiag hdiag

theorem disjoint_gCross_cross (f : V → V) :
    Disjoint (G.squareGCrossEdges f) (G.squareCrossEdges f) := by
  rw [Set.disjoint_left]
  rintro e ⟨hG, _⟩ ⟨_, _, hnG⟩
  exact hnG hG

/-- **`E(G²)` is the union of the in-part, `G`-cross, and cross classes**
(`lem:square-cross-classification`). An edge of `G²` is in-part or crosses parts; a cross edge is an
edge of `G` (`G`-cross) or not (cross). -/
theorem square_edgeSet_eq_union (f : V → V) :
    G.square.edgeSet =
      G.squareInPartEdges f ∪ G.squareGCrossEdges f ∪ G.squareCrossEdges f := by
  ext e
  simp only [squareInPartEdges, squareGCrossEdges, squareCrossEdges, Set.mem_union,
    Set.mem_ofPred_eq]
  constructor
  · intro he
    by_cases hdiag : (e.map f).IsDiag
    · exact Or.inl (Or.inl ⟨he, hdiag⟩)
    · by_cases hG : e ∈ G.edgeSet
      · exact Or.inl (Or.inr ⟨hG, hdiag⟩)
      · exact Or.inr ⟨he, hdiag, hG⟩
  · rintro ((⟨he, _⟩ | ⟨hG, _⟩) | ⟨he, _⟩)
    · exact he
    · exact edgeSet_subset_edgeSet.mpr G.le_square hG
    · exact he

/-- **Cross edges split as normal ∪ special** (`lem:square-cross-classification`). Every cross edge
has a common neighbor (`exists_apex_of_mem_squareCrossEdges`), whose part either contains an
endpoint (normal) or does not (special). -/
theorem squareCrossEdges_eq_union (f : V → V) :
    G.squareCrossEdges f = G.squareNormalCrossEdges f ∪ G.squareSpecialCrossEdges f := by
  ext e
  simp only [squareNormalCrossEdges, squareSpecialCrossEdges, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · intro he
    obtain ⟨v, hv⟩ := exists_apex_of_mem_squareCrossEdges he
    by_cases hfv : f v ∈ e.map f
    · exact Or.inl ⟨he, v, hv, hfv⟩
    · exact Or.inr ⟨he, v, hv, hfv⟩
  · rintro (⟨he, _⟩ | ⟨he, _⟩) <;> exact he

/-- **Normal and special cross edges are disjoint** for a tight partition
(`lem:square-cross-classification`). A cross edge in both would have a common neighbor `v` inside an
endpoint's part and a common neighbor `v'` outside both; by uniqueness of the common neighbor
(`IsSquareTightPartition.eq_of_common_nbr`) `v = v'`, a contradiction. -/
theorem squareNormalCrossEdges_disjoint_special [Finite V] {f : V → V}
    (hf : G.IsSquareTightPartition f) :
    Disjoint (G.squareNormalCrossEdges f) (G.squareSpecialCrossEdges f) := by
  rw [Set.disjoint_left]
  rintro e ⟨hcross, v, hv, hfv⟩ ⟨_, v', hv', hfv'⟩
  induction e with | h u w =>
  simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq] at hv hv'
  rw [mem_squareCrossEdges] at hcross
  have hvv' : v = v' := hf.eq_of_common_nbr hcross.2.1 hv.1 hv.2 hv'.1 hv'.2
  rw [hvv'] at hfv
  exact hfv' hfv

/-- **The `G`-cross class numbers `d_G(P)`** (`lem:square-cross-classification`). The edges of
`G` joining distinct parts biject, via `s(x, y) ↦ Sum.inl s(x, y)`, with the crossing edges
`G.shadowGraph.crossingEdges f`, whose number is `d_G(P)` (the `crossingEdges` term of
`partitionDef` and `deficiency`; JJ write `e_G(P)`). The proof of `thm:laman-square-count` uses
it to identify that term. -/
theorem squareGCrossEdges_ncard_eq_crossingEdges (f : V → V) :
    (G.squareGCrossEdges f).ncard = (G.shadowGraph.crossingEdges f).ncard := by
  have himg : G.shadowGraph.crossingEdges f =
      (Sum.inl : Sym2 V → Sym2 V ⊕ Fin (6 * (Nat.card V - 1) + 1)) '' (G.squareGCrossEdges f) := by
    ext e
    simp only [Graph.crossingEdges, squareGCrossEdges, Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨_, x, y, ⟨hadj, hlink⟩, hne⟩
      exact ⟨s(x, y), ⟨hadj, hne⟩, hlink⟩
    · rintro ⟨e', ⟨hadj, hne⟩, rfl⟩
      refine e'.ind (fun x y => ?_) hadj hne
      intro hadj hne
      exact ⟨⟨x, y, hadj, rfl⟩, x, y, ⟨hadj, rfl⟩, hne⟩
  rw [himg, (Sum.inl_injective.injOn).ncard_image]

/-! ## The classification: the common neighbors

The part of the common neighbor of a special cross edge is a singleton, and that of a normal
cross edge has at least three vertices and contains exactly one endpoint. Both rest on the parts
of a tight partition (`IsSquareTightPartition.parts`); the special case also uses the degree
bound (`IsLaman3.degree_le_three`). This is the *moreover* clause of
`lem:square-cross-classification`. -/

/-- **The parts of a tight partition** (`lem:tight-partition-parts` for `G.shadowGraph`). If two
distinct vertices `v ≠ w` share a part (`f w = f v`), then `v`'s part has at least three vertices
and `v` has at least two neighbors inside it. The first half rewrites the part of
`Graph.IsTightPartition.parts` within `V(G.shadowGraph) = univ`; the second converts its count of
edges of `G.shadowGraph` through the bijection `y ↦ Sum.inl s(v, y)` between those edges at `v`
inside the part and `v`'s neighbors in `G` inside it. -/
theorem IsSquareTightPartition.parts [Finite V] {f : V → V} (hf : G.IsSquareTightPartition f)
    {v w : V} (hvw : w ≠ v) (hfw : f w = f v) :
    3 ≤ {x | f x = f v}.ncard ∧ 2 ≤ {y | G.Adj v y ∧ f y = f v}.ncard := by
  obtain ⟨hpart, hedge⟩ := Graph.IsTightPartition.parts hf (n := 3) (by decide)
    G.shadowGraph_simple (Set.mem_univ v) (Set.mem_univ w) hvw hfw
  refine ⟨?_, ?_⟩
  · rwa [show {x ∈ V(G.shadowGraph) | f x = f v} = {x | f x = f v} from by
      rw [shadowGraph_vertexSet]; exact Set.sep_univ] at hpart
  · set T_e := {e ∈ E(G.shadowGraph) | ∃ y, y ≠ v ∧ f y = f v ∧ G.shadowGraph.IsLink e v y}
      with hTe
    set T_v : Set V := {y | G.Adj v y ∧ f y = f v} with hTv
    have himg : T_e = (fun y : V => (Sum.inl s(v, y) :
        Sym2 V ⊕ Fin (6 * (Nat.card V - 1) + 1))) '' T_v := by
      ext e
      simp only [hTe, hTv, Set.mem_ofPred_eq, Set.mem_image]
      constructor
      · rintro ⟨_, y, hyv, hfy, hadj, hlink⟩
        exact ⟨y, ⟨hadj, hfy⟩, hlink⟩
      · rintro ⟨y, ⟨hadj, hfy⟩, rfl⟩
        exact ⟨⟨v, y, hadj, rfl⟩, y, hadj.ne', hfy, hadj, rfl⟩
    have hinj : Set.InjOn (fun y : V => (Sum.inl s(v, y) :
        Sym2 V ⊕ Fin (6 * (Nat.card V - 1) + 1))) T_v := by
      intro y1 hy1 y2 hy2 heq
      simp only [Sum.inl.injEq] at heq
      rcases Sym2.eq_iff.mp heq with ⟨_, h⟩ | ⟨h1, h2⟩
      · exact h
      · exact h2.trans h1
    calc (2 : ℕ) ≤ T_e.ncard := hedge
      _ = T_v.ncard := by rw [himg, hinj.ncard_image]

/-- **The common neighbor of a special cross edge forms a singleton part**
(`lem:square-cross-classification`). The common neighbor `v` of a special cross edge `s(u, w)` forms
a singleton part: every vertex with label `f v` is `v` itself.

Both `u` and `w` lie outside `v`'s part (special), so `v` has the two distinct out-of-part
neighbors `u ≠ w`; if `v`'s part were not a singleton, `v` would have two further in-part
neighbors (`IsSquareTightPartition.parts`), giving `v` degree at least four and contradicting the
Laman degree bound `IsLaman3.degree_le_three`. -/
theorem squareSpecialCrossEdges_singleton_part [Finite V] {f : V → V}
    (hf : G.IsSquareTightPartition f) (hlaman : G.square.IsLaman3)
    {u w v : V} (he : s(u, w) ∈ G.squareSpecialCrossEdges f)
    (huv : G.Adj u v) (hwv : G.Adj w v) :
    ∀ x, f x = f v → x = v := by
  classical
  have : Fintype ↥(G.neighborSet v) := Fintype.ofFinite _
  rw [squareSpecialCrossEdges, Set.mem_ofPred_eq] at he
  obtain ⟨hcross, v', hapex', hfv'⟩ := he
  rw [mem_squareCrossEdges] at hcross
  obtain ⟨hsq, hfuw, hnadj⟩ := hcross
  simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq] at hapex'
  rw [Sym2.map_mk, Sym2.mem_iff, not_or] at hfv'
  have hvv' : v = v' := hf.eq_of_common_nbr hfuw huv hwv hapex'.1 hapex'.2
  subst hvv'
  intro x hfx
  by_contra hxv
  obtain ⟨_, hinpart⟩ := hf.parts hxv hfx
  set inPart : Set V := {y | G.Adj v y ∧ f y = f v} with hIP
  have huw : u ≠ w := by rintro rfl; exact hfuw rfl
  have hsub : inPart ∪ {u, w} ⊆ G.neighborSet v := by
    rintro y (⟨hy, _⟩ | rfl | rfl)
    · exact hy
    · exact huv.symm
    · exact hwv.symm
  have hdisj : Disjoint inPart ({u, w} : Set V) := by
    rw [Set.disjoint_right]
    rintro y (rfl | rfl) ⟨_, hfy⟩
    · exact hfv'.1 hfy.symm
    · exact hfv'.2 hfy.symm
  have hunion : (inPart ∪ {u, w}).ncard = inPart.ncard + 2 := by
    rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), Set.ncard_pair huw]
  have hle : (inPart ∪ {u, w}).ncard ≤ (G.neighborSet v).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have hdeg : (G.neighborSet v).ncard = G.degree v := ncard_neighborSet_eq_degree G v
  have hle3 : G.degree v ≤ 3 := hlaman.degree_le_three v
  omega

/-- **The common neighbor of a normal cross edge** (`lem:square-cross-classification`). The
common neighbor `v` of a normal cross edge `s(u, w)` shares a part with exactly one endpoint
(the endpoints lie in distinct parts, `f u ≠ f w`), and that part has at least three vertices.

`v` shares its part with the endpoint `u` (or `w`) it is `f`-equal to; those two are adjacent and
distinct, so the part is not a singleton, hence has ≥ 3 vertices
(`IsSquareTightPartition.parts`). -/
theorem squareNormalCrossEdges_part_three_le [Finite V] {f : V → V}
    (hf : G.IsSquareTightPartition f)
    {u w v : V} (he : s(u, w) ∈ G.squareNormalCrossEdges f)
    (huv : G.Adj u v) (hwv : G.Adj w v) :
    3 ≤ {x | f x = f v}.ncard ∧ ((f u = f v ∧ f w ≠ f v) ∨ (f w = f v ∧ f u ≠ f v)) := by
  rw [squareNormalCrossEdges, Set.mem_ofPred_eq] at he
  obtain ⟨hcross, v', hapex', hfv'⟩ := he
  rw [mem_squareCrossEdges] at hcross
  obtain ⟨hsq, hfuw, hnadj⟩ := hcross
  simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq] at hapex'
  rw [Sym2.map_mk, Sym2.mem_iff] at hfv'
  have hvv' : v = v' := hf.eq_of_common_nbr hfuw huv hwv hapex'.1 hapex'.2
  subst hvv'
  have hone : (f u = f v ∧ f w ≠ f v) ∨ (f w = f v ∧ f u ≠ f v) := by
    rcases hfv' with h | h
    · exact Or.inl ⟨h.symm, fun hc => hfuw (hc.trans h).symm⟩
    · exact Or.inr ⟨h.symm, fun hc => hfuw (hc.trans h)⟩
  refine ⟨?_, hone⟩
  rcases hfv' with h | h
  · exact (hf.parts huv.ne h.symm).1
  · exact (hf.parts hwv.ne h.symm).1

/-! ## Special cross edges at a singleton part (`lem:singleton-part-neighborhood`)

For a singleton part `{v}`, `N_G(v)` is a clique of `G²` (`isClique_neighborSet_square`, for
every graph) with `2 d_G(v) - 3` edges when `G²` is Laman and `d_G(v) ≥ 2`
(`ncard_edgesIn_neighborSet_square`, `Jacobs.lean`, for no partition). The singleton part makes
each of those edges a *special cross* edge with common neighbor `v` (JJ eqs. (5) and (7)): two
neighbors of `v` lie in distinct parts (else two edges would join one part and `v`'s singleton
part, `not_adj_adj_of_same_part`) and are nonadjacent in `G` (else a triangle would join three
parts, `not_adj_triangle`), so the edge between them is a cross edge; it is special because
`v`'s singleton part contains neither endpoint, and `v` is its only common neighbor by
`eq_of_common_nbr`. -/

/-- **Special cross edges at a singleton part** (`lem:singleton-part-neighborhood`; JJ eqs. (5) and
(7)). For a singleton part `{v}` (`∀ x, f x = f v → x = v`), two distinct neighbors `u, w` of `v`
form a special cross edge of `G²` whose unique common neighbor is `v`. -/
theorem IsSquareTightPartition.mem_squareSpecialCrossEdges_of_singleton_part [Finite V]
    {f : V → V} (hf : G.IsSquareTightPartition f) {v : V} (hsing : ∀ x, f x = f v → x = v)
    {u w : V} (hu : u ∈ G.neighborSet v) (hw : w ∈ G.neighborSet v) (huw : u ≠ w) :
    s(u, w) ∈ G.squareSpecialCrossEdges f ∧
      ∀ z, (∀ y ∈ (s(u, w) : Sym2 V), G.Adj y z) → z = v := by
  have hvu : G.Adj v u := (mem_neighborSet G v u).mp hu
  have hvw : G.Adj v w := (mem_neighborSet G v w).mp hw
  have hu_ne_v : u ≠ v := hvu.ne'
  have hw_ne_v : w ≠ v := hvw.ne'
  have hfuv : f u ≠ f v := fun h => hu_ne_v (hsing u h)
  have hfwv : f w ≠ f v := fun h => hw_ne_v (hsing w h)
  have hfvu : f v ≠ f u := hfuv.symm
  have hfvw : f v ≠ f w := hfwv.symm
  have hfuw : f u ≠ f w := fun h => hf.not_adj_adj_of_same_part hfvu h hvu hvw huw
  have hnadj : ¬ G.Adj u w := fun h => hf.not_adj_triangle hfuv hfvw hfuw hvu.symm hvw h
  have hsqadj : G.square.Adj u w := isClique_neighborSet_square G v hu hw huw
  have hcross : s(u, w) ∈ G.squareCrossEdges f := mem_squareCrossEdges.mpr ⟨hsqadj, hfuw, hnadj⟩
  have hspecial : s(u, w) ∈ G.squareSpecialCrossEdges f := by
    rw [squareSpecialCrossEdges, Set.mem_ofPred_eq]
    refine ⟨hcross, v, ?_, ?_⟩
    · simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq]
      exact ⟨hvu.symm, hvw.symm⟩
    · rw [Sym2.map_mk, Sym2.mem_iff, not_or]
      exact ⟨hfvu, hfvw⟩
  refine ⟨hspecial, ?_⟩
  intro z hz
  simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq] at hz
  exact (hf.eq_of_common_nbr hfuw hvu.symm hvw.symm hz.1 hz.2).symm

/-! ## The converse: special cross edges come from singleton parts (`lem:singleton-part-converse`)
-/

/-- **Every special cross edge arises from exactly one singleton part**
(`lem:singleton-part-converse`). Existence takes the common neighbor `v` given by the membership
`he` and applies `squareSpecialCrossEdges_singleton_part` for the singleton part and
`mk_mem_edgesIn` for the membership in `edgesIn`; uniqueness is
`IsSquareTightPartition.eq_of_common_nbr` applied to any other such vertex `v'`. -/
theorem exists_unique_singleton_part_of_mem_squareSpecialCrossEdges [Finite V] {f : V → V}
    (hf : G.IsSquareTightPartition f) (hlaman : G.square.IsLaman3) {e : Sym2 V}
    (he : e ∈ G.squareSpecialCrossEdges f) :
    ∃! v, (∀ x, f x = f v → x = v) ∧ e ∈ G.square.edgesIn (G.neighborSet v) := by
  induction e with | h u w =>
  have he' := he
  rw [squareSpecialCrossEdges, Set.mem_ofPred_eq] at he'
  obtain ⟨hcross, v, hapex, hfv⟩ := he'
  simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq] at hapex
  obtain ⟨hsqadj, hfuw, hnadj⟩ := mem_squareCrossEdges.mp hcross
  have hsing : ∀ x, f x = f v → x = v :=
    squareSpecialCrossEdges_singleton_part hf hlaman he hapex.1 hapex.2
  have hu : u ∈ G.neighborSet v := (mem_neighborSet G v u).mpr hapex.1.symm
  have hw : w ∈ G.neighborSet v := (mem_neighborSet G v w).mpr hapex.2.symm
  have hmem : s(u, w) ∈ G.square.edgesIn (G.neighborSet v) := mk_mem_edgesIn hsqadj hu hw
  refine ⟨v, ⟨hsing, hmem⟩, ?_⟩
  rintro v' ⟨_, hmem'⟩
  obtain ⟨_, hsub⟩ := mem_edgesIn.mp hmem'
  rw [Sym2.coe_mk] at hsub
  obtain ⟨hu', hw'⟩ := Set.insert_subset_iff.mp hsub
  rw [Set.singleton_subset_iff] at hw'
  have huv' : G.Adj u v' := ((mem_neighborSet G v' u).mp hu').symm
  have hwv' : G.Adj w v' := ((mem_neighborSet G v' w).mp hw').symm
  exact (hf.eq_of_common_nbr hfuw hapex.1 hapex.2 huv' hwv').symm

/-! ## Normal cross edges rooted at a part (`lem:normal-cross-count`)

A normal cross edge, unlike a special one, has its common neighbor `v` in the *same* part as one
of its endpoints. Following Jackson–Jordán, the edge is **rooted** at the part containing `v`
(labeled `f v`); the root is unique (`IsSquareTightPartition.rootedAt_inj`, by the uniqueness of
the common neighbor) and, by the *moreover* clause of `lem:square-cross-classification`
(`squareNormalCrossEdges_part_three_le`), a part of at least three vertices.

The normal cross edges rooted at a part `A` with `|A| ≥ 3` number `2 · d_G(A)` (JJ eq. (6)),
where `d_G(A)` is the number of edges of `G` with exactly one endpoint in `A`. Each edge `vw` of
`G` with `v ∈ A`, `w ∉ A` gives the two edges `s(u, w)`, `u ∈ N_G(v) ∩ A`
(`ncard_inPartNeighbors_eq_two`, `mk_mem_squareNormalCrossEdgesRootedAt`,
`ncard_normalCrossEdges_of_crossing_eq_two`), and every normal cross edge rooted at `A` arises
from exactly one such edge (`squareNormalCrossEdgesRootedAt_eq_biUnion`,
`squareCutPairs_pairwiseDisjoint`). -/

/-- **Normal cross edges rooted at a part** (`def:rooted-cross-edges`). A normal cross edge is
**rooted** at the part `{x | f x = a}` when a common neighbor `v` of its endpoints has the
label `a` (`f v = a`). For a tight partition the common neighbor, and hence the root, is unique
(`IsSquareTightPartition.rootedAt_inj`). -/
def squareNormalCrossEdgesRootedAt (G : SimpleGraph V) (f : V → V) (a : V) : Set (Sym2 V) :=
  {e ∈ G.squareNormalCrossEdges f | ∃ v, (∀ z ∈ e, G.Adj z v) ∧ f v = a}

/-- **The root of a normal cross edge is unique** (`lem:normal-cross-count-rooted`; its last clause
is `squareNormalCrossEdges_part_three_le`). If a normal cross edge is rooted at both `a` and `a'`,
then `a = a'`: its two witnessing common neighbors coincide by
`IsSquareTightPartition.eq_of_common_nbr` (the endpoints lie in distinct parts, so `f u ≠ f w`),
hence have the same label. -/
theorem IsSquareTightPartition.rootedAt_inj [Finite V] {f : V → V}
    (hf : G.IsSquareTightPartition f) {a a' : V} {e : Sym2 V}
    (h : e ∈ G.squareNormalCrossEdgesRootedAt f a)
    (h' : e ∈ G.squareNormalCrossEdgesRootedAt f a') : a = a' := by
  induction e with | h u w =>
  obtain ⟨hnormal, v, hv, hfv⟩ := h
  obtain ⟨_, v', hv', hfv'⟩ := h'
  simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq] at hv hv'
  obtain ⟨hcross, -⟩ := hnormal
  obtain ⟨_, hfuw, _⟩ := mem_squareCrossEdges.mp hcross
  have hvv' : v = v' := hf.eq_of_common_nbr hfuw hv.1 hv.2 hv'.1 hv'.2
  rw [← hfv, ← hfv', hvv']

/-- **Two neighbors in the part** (`lem:normal-cross-count-local`). Let `v` lie in a part of at
least two vertices (witnessed by a vertex `v₀ ≠ v` with `f v₀ = f v`) and have a neighbor `w`
outside its part (`G.Adj v w`, `f w ≠ f v`). Then `v` has **exactly two** neighbors inside its
own part.

Lower bound: the second half of `IsSquareTightPartition.parts`. Upper bound: `v`'s neighbors
inside and outside its part partition `N_G(v)`, whose size is `d_G(v) ≤ 3`
(`IsLaman3.degree_le_three`); the outside is nonempty (it holds `w`), leaving at most two
neighbors inside the part. -/
theorem IsSquareTightPartition.ncard_inPartNeighbors_eq_two [Finite V] {f : V → V}
    (hf : G.IsSquareTightPartition f) (hlaman : G.square.IsLaman3)
    {v v₀ w : V} (hv₀ : v₀ ≠ v) (hfv₀ : f v₀ = f v)
    (hvw : G.Adj v w) (hfw : f w ≠ f v) :
    {u | G.Adj v u ∧ f u = f v}.ncard = 2 := by
  classical
  have : Fintype ↥(G.neighborSet v) := Fintype.ofFinite _
  have hlow : 2 ≤ {u | G.Adj v u ∧ f u = f v}.ncard := (hf.parts hv₀ hfv₀).2
  have hunion : {u | G.Adj v u ∧ f u = f v} ∪ {u | G.Adj v u ∧ f u ≠ f v}
      = G.neighborSet v := by
    ext u
    simp only [Set.mem_union, Set.mem_ofPred_eq, mem_neighborSet]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      by_cases he : f u = f v
      · exact Or.inl ⟨h, he⟩
      · exact Or.inr ⟨h, he⟩
  have hdisj : Disjoint {u | G.Adj v u ∧ f u = f v} {u | G.Adj v u ∧ f u ≠ f v} := by
    rw [Set.disjoint_left]
    rintro u ⟨_, h1⟩ ⟨_, h2⟩
    exact h2 h1
  have hncard : {u | G.Adj v u ∧ f u = f v}.ncard + {u | G.Adj v u ∧ f u ≠ f v}.ncard
      = (G.neighborSet v).ncard := by
    rw [← hunion, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
  have houtpos : 0 < {u | G.Adj v u ∧ f u ≠ f v}.ncard :=
    (show ({u | G.Adj v u ∧ f u ≠ f v} : Set V).Nonempty from ⟨w, hvw, hfw⟩).ncard_pos
  have hdeg : (G.neighborSet v).ncard = G.degree v := ncard_neighborSet_eq_degree G v
  have hle3 : G.degree v ≤ 3 := hlaman.degree_le_three v
  omega

/-- **A normal cross edge from two edges at a vertex** (`lem:normal-cross-count-producer`). Let
`v` have a neighbor `u` inside its part (`G.Adj v u`, `f u = f v`) and a neighbor `w` outside it
(`G.Adj v w`, `f w ≠ f v`). Then `s(u, w)` is a normal cross edge rooted at `v`'s part (label
`f v`), and `v` is its unique common neighbor.

`s(u, w)` is a `G²`-edge (`u, w ∈ N_G(v)`, `u ≠ w`, `isClique_neighborSet_square`), joins
distinct parts (`f u = f v ≠ f w`), and is not a `G`-edge — otherwise `vw` and `uw` would be two
edges between `v`'s part and `w`'s (`not_adj_adj_of_same_part`). Its common neighbor `v` lies in
`u`'s part (`f v = f u`), so the edge is normal and rooted at `f v`; uniqueness of the common
neighbor is `eq_of_common_nbr`. This is the map `(vw, u) ↦ s(u, w)` of the double count of
`lem:normal-cross-count`, over the `d_G(A)` edges leaving the part. -/
theorem IsSquareTightPartition.mk_mem_squareNormalCrossEdgesRootedAt [Finite V] {f : V → V}
    (hf : G.IsSquareTightPartition f) {v u w : V}
    (hu : G.Adj v u) (hfu : f u = f v) (hw : G.Adj v w) (hfw : f w ≠ f v) :
    s(u, w) ∈ G.squareNormalCrossEdgesRootedAt f (f v) ∧
      ∀ z, (∀ y ∈ (s(u, w) : Sym2 V), G.Adj y z) → z = v := by
  have huw : u ≠ w := fun h => hfw (h ▸ hfu)
  have hu' : u ∈ G.neighborSet v := (mem_neighborSet G v u).mpr hu
  have hw' : w ∈ G.neighborSet v := (mem_neighborSet G v w).mpr hw
  have hsqadj : G.square.Adj u w := isClique_neighborSet_square G v hu' hw' huw
  have hfuw : f u ≠ f w := fun h => hfw (h.symm.trans hfu)
  have hnadj : ¬ G.Adj u w := fun hadj =>
    hf.not_adj_adj_of_same_part hfw hfu.symm hw.symm hadj.symm hu.ne
  have hcross : s(u, w) ∈ G.squareCrossEdges f := mem_squareCrossEdges.mpr ⟨hsqadj, hfuw, hnadj⟩
  have hnormal : s(u, w) ∈ G.squareNormalCrossEdges f := by
    rw [squareNormalCrossEdges, Set.mem_ofPred_eq]
    refine ⟨hcross, v, ?_, ?_⟩
    · simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq]
      exact ⟨hu.symm, hw.symm⟩
    · rw [Sym2.map_mk, Sym2.mem_iff]
      exact Or.inl hfu.symm
  refine ⟨?_, ?_⟩
  · rw [squareNormalCrossEdgesRootedAt, Set.mem_ofPred_eq]
    refine ⟨hnormal, v, ?_, rfl⟩
    simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq]
    exact ⟨hu.symm, hw.symm⟩
  · intro z hz
    simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq] at hz
    exact (hf.eq_of_common_nbr hfuw hu.symm hw.symm hz.1 hz.2).symm

/-- **The edges of `G` leaving a part** (`def:g-cut-edges`; their number is Jackson–Jordán's
degree `d_G(A)` of the part). For a labeling `f` and a label `a`, these are the edges of `G` with
*exactly one* endpoint in the part `{x | f x = a}`: edges `s(x, y)` with `f x = a` and
`f y ≠ a`. The double count of `lem:normal-cross-count` runs over them (each gives two rooted
normal cross edges). -/
def gCutEdges (G : SimpleGraph V) (f : V → V) (a : V) : Set (Sym2 V) :=
  {e ∈ G.edgeSet | ∃ x y, e = s(x, y) ∧ f x = a ∧ f y ≠ a}

/-- **Two normal cross edges for each edge leaving a part** (`lem:normal-cross-count-fiber`, a
fiber of the double count `2·d_G(A)`). For an edge `vw` of `G` with `v` in a part of at least two
vertices (witnessed by `v₀ ≠ v` with `f v₀ = f v`) and `w` outside it, the edges `s(u, w)` for the
neighbors `u` of `v` in its part (the image of `{u | G.Adj v u ∧ f u = f v}` under
`u ↦ s(u, w)`) number exactly two and are normal cross edges rooted at the part.

The map `u ↦ s(u, w)` is injective on the in-part neighbors (shared endpoint `w`, and `u ≠ w`
since `f u = f v ≠ f w`), so `Set.InjOn.ncard_image` transfers the count
`ncard_inPartNeighbors_eq_two`; each image edge is a rooted normal cross edge by
`mk_mem_squareNormalCrossEdgesRootedAt`. -/
theorem IsSquareTightPartition.ncard_normalCrossEdges_of_crossing_eq_two [Finite V] {f : V → V}
    (hf : G.IsSquareTightPartition f) (hlaman : G.square.IsLaman3)
    {v v₀ w : V} (hv₀ : v₀ ≠ v) (hfv₀ : f v₀ = f v)
    (hvw : G.Adj v w) (hfw : f w ≠ f v) :
    ((fun u => s(u, w)) '' {u | G.Adj v u ∧ f u = f v}).ncard = 2 ∧
      (fun u => s(u, w)) '' {u | G.Adj v u ∧ f u = f v} ⊆
        G.squareNormalCrossEdgesRootedAt f (f v) := by
  have hinj : Set.InjOn (fun u => s(u, w)) {u | G.Adj v u ∧ f u = f v} := by
    intro u1 hu1 u2 _ heq
    simp only [Sym2.eq_iff] at heq
    rcases heq with ⟨h, -⟩ | ⟨h1, -⟩
    · exact h
    · simp only [Set.mem_ofPred_eq] at hu1
      exact absurd (h1 ▸ hu1.2) hfw
  refine ⟨?_, ?_⟩
  · rw [hinj.ncard_image]
    exact hf.ncard_inPartNeighbors_eq_two hlaman hv₀ hfv₀ hvw hfw
  · rintro e ⟨u, hu, rfl⟩
    simp only [Set.mem_ofPred_eq] at hu
    exact (hf.mk_mem_squareNormalCrossEdgesRootedAt hu.1 hu.2 hvw hfw).1

/-! ## Rooted normal cross edges by the edges leaving a part (`lem:normal-cross-count-partition`)

The normal cross edges rooted at part `a` are the disjoint union, over the pairs `(v, w)` leaving
the part (`squareCutPairs`: `f v = a`, `f w ≠ a`, `G.Adj v w`), of the fibers
`(fun u => s(u, w)) '' {u | G.Adj v u ∧ f u = f v}`. With the count of two in each fiber
(`ncard_normalCrossEdges_of_crossing_eq_two`) and the bijection of these pairs with the edges
`gCutEdges f a` leaving the part (`ncard_squareCutPairs_eq_gCutEdges`, so there are `d_G(A)` of
them), summing over the disjoint union gives `2·d_G(A)`. -/

/-- **The pairs leaving a part** (`def:g-cut-edges`): the pairs `(v, w)` with `v` in the part
`{x | f x = a}`, `w` outside it, and `vw ∈ E(G)`. These index the fibers of the double count of
`lem:normal-cross-count`; the map `(v, w) ↦ s(v, w)` is a bijection onto `gCutEdges f a`
(`ncard_squareCutPairs_eq_gCutEdges`), so there are `d_G(A)` of them. -/
def squareCutPairs (G : SimpleGraph V) (f : V → V) (a : V) : Set (V × V) :=
  {p | f p.1 = a ∧ f p.2 ≠ a ∧ G.Adj p.1 p.2}

/-- **The pairs leaving a part number `d_G(A)`** (`lem:normal-cross-count-partition`, the
bijection). The map `(v, w) ↦ s(v, w)` is a bijection from `squareCutPairs f a` onto
`gCutEdges f a`: injective because the labeling fixes the order (`f v = a ≠ f w`), and surjective
because an edge leaving the part has one endpoint in it and one outside. -/
theorem ncard_squareCutPairs_eq_gCutEdges (f : V → V) (a : V) :
    (G.squareCutPairs f a).ncard = (G.gCutEdges f a).ncard := by
  have hinj : Set.InjOn (fun p : V × V => s(p.1, p.2)) (G.squareCutPairs f a) := by
    rintro ⟨v, w⟩ hp ⟨v', w'⟩ hq heq
    simp only [Sym2.eq_iff, Prod.mk.injEq] at heq ⊢
    obtain ⟨hfv, _, _⟩ := hp
    obtain ⟨_, hfw', _⟩ := hq
    rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h1, h2⟩
    · exact absurd (h1 ▸ hfv) hfw'
  have himg : (fun p : V × V => s(p.1, p.2)) '' G.squareCutPairs f a = G.gCutEdges f a := by
    ext e
    simp only [squareCutPairs, gCutEdges, Set.mem_image, Set.mem_ofPred_eq, Prod.exists]
    constructor
    · rintro ⟨v, w, ⟨hfv, hfw, hadj⟩, rfl⟩
      exact ⟨G.mem_edgeSet.mpr hadj, v, w, rfl, hfv, hfw⟩
    · rintro ⟨he, u, z, rfl, hfu, hfz⟩
      exact ⟨u, z, ⟨hfu, hfz, G.mem_edgeSet.mp he⟩, rfl⟩
  rw [← himg, hinj.ncard_image]

/-- **The normal cross edges rooted at a part are the union of the fibers over the pairs leaving
it** (`lem:normal-cross-count-partition`, the union). Every normal cross edge rooted at `a` is
`s(u, w)` for a pair `(v, w) ∈ squareCutPairs f a` and a neighbor `u ∈ N_G(v)` with `f u = f v`
(the pair is unique by `squareCutPairs_pairwiseDisjoint`); conversely each such edge is a rooted
normal cross edge (`mk_mem_squareNormalCrossEdgesRootedAt`).

Forward: the common neighbor `v` of the rooted edge has `f v = a` and exactly one endpoint in
`v`'s part (`squareNormalCrossEdges_part_three_le`), so the pair is `v` with the other endpoint.
Backward: `mk_mem_squareNormalCrossEdgesRootedAt`. -/
theorem IsSquareTightPartition.squareNormalCrossEdgesRootedAt_eq_biUnion [Finite V] {f : V → V}
    (hf : G.IsSquareTightPartition f) (a : V) :
    G.squareNormalCrossEdgesRootedAt f a =
      ⋃ p ∈ G.squareCutPairs f a, (fun u => s(u, p.2)) '' {u | G.Adj p.1 u ∧ f u = f p.1} := by
  ext e
  induction e with | h u w =>
  simp only [Set.mem_iUnion, Set.mem_image, Set.mem_ofPred_eq, exists_prop, squareCutPairs]
  constructor
  · intro he
    obtain ⟨hnormal, v, hv, hfv⟩ := he
    simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq] at hv
    obtain ⟨_, hone⟩ := squareNormalCrossEdges_part_three_le hf hnormal hv.1 hv.2
    rcases hone with ⟨hfu, hfw⟩ | ⟨hfw', hfu'⟩
    · exact ⟨(v, w), ⟨hfv, by rw [← hfv]; exact hfw, hv.2.symm⟩, u, ⟨hv.1.symm, hfu⟩, rfl⟩
    · exact ⟨(v, u), ⟨hfv, by rw [← hfv]; exact hfu', hv.1.symm⟩, w, ⟨hv.2.symm, hfw'⟩,
        Sym2.eq_swap⟩
  · rintro ⟨p, ⟨hfp1, hfp2, hadjp⟩, u', ⟨hadju', hfu'⟩, hs⟩
    rw [← hs, ← hfp1]
    exact (hf.mk_mem_squareNormalCrossEdgesRootedAt hadju' hfu' hadjp (by rw [hfp1]; exact hfp2)).1

/-- **The fibers over distinct pairs leaving a part are disjoint**
(`lem:normal-cross-count-partition`, the disjointness). If `s(u, w)` lies in the fibers of both
`(v, w)` and `(v', w')`, then `{u, w} = {u', w'}` as endpoint sets; the labeling forces `u = u'`,
`w = w'` (the in-part vertex `u` has `f u = a`, the out vertex `w` has `f w ≠ a`), and then `v = v'`
by uniqueness of the common neighbor (`eq_of_common_nbr`), so `(v, w) = (v', w')`. -/
theorem IsSquareTightPartition.squareCutPairs_pairwiseDisjoint [Finite V] {f : V → V}
    (hf : G.IsSquareTightPartition f) (a : V) :
    (G.squareCutPairs f a).PairwiseDisjoint
      (fun p => (fun u => s(u, p.2)) '' {u | G.Adj p.1 u ∧ f u = f p.1}) := by
  rintro ⟨v, w⟩ hp ⟨v', w'⟩ hq hpq
  simp only [squareCutPairs, Set.mem_ofPred_eq] at hp hq
  obtain ⟨hfv, hfw, hvw⟩ := hp
  obtain ⟨hfv', hfw', hv'w'⟩ := hq
  simp only [Function.onFun, Set.disjoint_left, Set.mem_image, Set.mem_ofPred_eq]
  rintro e ⟨u, ⟨hvu, hfu⟩, rfl⟩ ⟨u', ⟨hv'u', hfu'⟩, heq⟩
  have hfua : f u = a := hfu.trans hfv
  have hfu'a : f u' = a := hfu'.trans hfv'
  rw [Sym2.eq_iff] at heq
  rcases heq with ⟨hu'u, hw'w⟩ | ⟨hu'w, _⟩
  · have hfuw : f u ≠ f w := by rw [hfua]; exact fun h => hfw h.symm
    have hvv' : v = v' := hf.eq_of_common_nbr hfuw hvu.symm hvw.symm
      (hu'u ▸ hv'u' : G.Adj v' u).symm (hw'w ▸ hv'w' : G.Adj v' w).symm
    exact hpq (by rw [hvv', hw'w])
  · exact hfw (hu'w ▸ hfu'a)

/-- **Normal cross edges rooted at a part** (`lem:normal-cross-count`; JJ eq. (6)). For a part
`A` with `|A| ≥ 3`, the normal cross edges rooted at `A` number exactly `2 · d_G(A)`. They are
the disjoint union of the fibers over the `d_G(A)` pairs leaving `A`
(`squareNormalCrossEdgesRootedAt_eq_biUnion`, `squareCutPairs_pairwiseDisjoint`,
`ncard_squareCutPairs_eq_gCutEdges`), and each fiber has exactly two elements
(`ncard_normalCrossEdges_of_crossing_eq_two`, with a second vertex of the part taken from
`hbig`). -/
theorem IsSquareTightPartition.ncard_normalCrossEdgesRootedAt_eq_two_mul_gCutEdges [Finite V]
    {f : V → V} (hf : G.IsSquareTightPartition f) (hlaman : G.square.IsLaman3) {a : V}
    (hbig : 3 ≤ {x | f x = a}.ncard) :
    (G.squareNormalCrossEdgesRootedAt f a).ncard = 2 * (G.gCutEdges f a).ncard := by
  rw [hf.squareNormalCrossEdgesRootedAt_eq_biUnion a,
    Set.Finite.ncard_biUnion (Set.toFinite _) (fun _ _ => Set.toFinite _)
      (hf.squareCutPairs_pairwiseDisjoint a)]
  have hfiber : ∀ p ∈ G.squareCutPairs f a,
      ((fun u => s(u, p.2)) '' {u | G.Adj p.1 u ∧ f u = f p.1}).ncard = 2 := by
    rintro ⟨v, w⟩ hp
    simp only [squareCutPairs, Set.mem_ofPred_eq] at hp
    obtain ⟨hfv, hfw, hadj⟩ := hp
    obtain ⟨v₀, hv₀mem, hv₀ne⟩ :=
      Set.exists_ne_of_one_lt_ncard (by omega : 1 < {x | f x = a}.ncard) v
    rw [Set.mem_ofPred_eq] at hv₀mem
    have hfv₀ : f v₀ = f v := by rw [hv₀mem, hfv]
    exact (hf.ncard_normalCrossEdges_of_crossing_eq_two hlaman hv₀ne hfv₀ hadj
      (by rw [hfv]; exact hfw)).1
  rw [finsum_mem_congr rfl hfiber, ← ncard_squareCutPairs_eq_gCutEdges, ← finsum_one,
    mul_finsum_mem]
  simp

/-! ## The labels of a partition and the handshake identity

The arithmetic of `thm:laman-square-count` sums the degree `d_G(P_i)` of each part (`gCutEdges`)
over the parts of a tight partition and needs the total to be `2 d_G(P)` (twice the number of
edges of `G` joining distinct parts, `squareGCrossEdges`), since each such edge is counted once
from each endpoint's part. `V` need not have a `Fintype` instance (only `[Finite V]`), so the
finite set of labels in use is a `Finset` via `Set.Finite.toFinset` (`partLabels`), and the
handshake identity is proved by double-counting the ordered pairs `(v, w)` with `G.Adj v w` and
`f v ≠ f w`: grouped by the part `f p.1` they are the pairs leaving each part (`squareCutPairs`),
which number `d_G(A)` (`ncard_squareCutPairs_eq_gCutEdges`); grouped by the edge `s(p.1, p.2)`
they are two for each edge of `G` joining distinct parts. -/

/-- **The finite label set of a partition.** For a labeling `f : V → V` (`V` finite but not
necessarily tagged `Fintype`), the parts actually in use — the image of `f` — packaged as a
`Finset V`. Depends only on `f` (not on a graph), unlike the rest of this file's definitions; it
indexes the sums of the proof of `thm:laman-square-count`. -/
noncomputable def partLabels (f : V → V) [Finite V] : Finset V :=
  (Set.finite_univ.image f).toFinset

theorem mem_partLabels [Finite V] (f : V → V) (a : V) :
    a ∈ partLabels f ↔ a ∈ Set.range f := by
  rw [partLabels, Set.Finite.mem_toFinset, Set.image_univ]

/-- **The handshake identity.** Summing the degree `d_G(A)` (`gCutEdges`) over every part `A` of
`f` counts each edge of `G` joining distinct parts exactly twice, once from each endpoint's
part. -/
theorem sum_gCutEdges_eq_two_mul_squareGCrossEdges [Finite V] (f : V → V) :
    ∑ a ∈ partLabels f, (G.gCutEdges f a).ncard = 2 * (G.squareGCrossEdges f).ncard := by
  classical
  have hDfin : ({p : V × V | G.Adj p.1 p.2 ∧ f p.1 ≠ f p.2} : Set (V × V)).Finite :=
    Set.toFinite _
  have hSfin : (G.squareGCrossEdges f).Finite := Set.toFinite _
  have hDmem : ∀ p : V × V, p ∈ hDfin.toFinset ↔ G.Adj p.1 p.2 ∧ f p.1 ≠ f p.2 :=
    fun _ => hDfin.mem_toFinset
  have hSmem : ∀ e : Sym2 V, e ∈ hSfin.toFinset ↔ e ∈ G.squareGCrossEdges f :=
    fun _ => hSfin.mem_toFinset
  -- Step 1: fiber the oriented cross pairs by the part `f p.1`, recovering the per-part cut sets.
  have hfiber1 : ∀ p ∈ hDfin.toFinset, f p.1 ∈ partLabels f := fun p _ =>
    (mem_partLabels f (f p.1)).mpr ⟨p.1, rfl⟩
  have hfilter1 : ∀ a ∈ partLabels f,
      (hDfin.toFinset.filter (fun p => f p.1 = a)).card = (G.gCutEdges f a).ncard := by
    intro a _
    have hSCPfin : (G.squareCutPairs f a).Finite := Set.toFinite _
    rw [← ncard_squareCutPairs_eq_gCutEdges, Set.ncard_eq_toFinset_card _ hSCPfin]
    congr 1
    ext ⟨x, y⟩
    rw [Finset.mem_filter, hDmem, hSCPfin.mem_toFinset]
    constructor
    · rintro ⟨⟨hxy, hfxy⟩, hfxa⟩
      exact ⟨hfxa, by rw [← hfxa]; exact hfxy.symm, hxy⟩
    · rintro ⟨hfxa, hfya, hxy⟩
      exact ⟨⟨hxy, by rw [hfxa]; exact hfya.symm⟩, hfxa⟩
  -- Step 2: fiber the oriented cross pairs by the underlying edge, 2-to-1 onto the cross edges.
  have hfiber2 : ∀ p ∈ hDfin.toFinset, s(p.1, p.2) ∈ hSfin.toFinset := by
    intro p hp
    rw [hSmem, mem_squareGCrossEdges]
    exact (hDmem p).mp hp
  have hfilter2 : ∀ e ∈ hSfin.toFinset,
      (hDfin.toFinset.filter (fun p => s(p.1, p.2) = e)).card = 2 := by
    intro e he
    rw [hSmem] at he
    induction e with
    | h x y =>
    rw [mem_squareGCrossEdges] at he
    obtain ⟨hxy, hfxy⟩ := he
    have hset : hDfin.toFinset.filter (fun p => s(p.1, p.2) = s(x, y)) = {(x, y), (y, x)} := by
      ext ⟨u, v⟩
      simp only [Finset.mem_filter, hDmem, Sym2.eq_iff, Finset.mem_insert, Finset.mem_singleton,
        Prod.mk.injEq]
      constructor
      · rintro ⟨-, h⟩
        exact h
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact ⟨⟨hxy, hfxy⟩, Or.inl ⟨rfl, rfl⟩⟩
        · exact ⟨⟨hxy.symm, hfxy.symm⟩, Or.inr ⟨rfl, rfl⟩⟩
    have hnotmem : (x, y) ∉ ({(y, x)} : Finset (V × V)) := by
      simp only [Finset.mem_singleton, Prod.mk.injEq]
      exact fun h => hxy.ne h.1
    rw [hset, Finset.card_insert_of_notMem hnotmem, Finset.card_singleton]
  have hcard1 : hDfin.toFinset.card =
      ∑ a ∈ partLabels f, (hDfin.toFinset.filter (fun p => f p.1 = a)).card :=
    Finset.card_eq_sum_card_fiberwise hfiber1
  have hcard2 : hDfin.toFinset.card =
      ∑ e ∈ hSfin.toFinset, (hDfin.toFinset.filter (fun p => s(p.1, p.2) = e)).card :=
    Finset.card_eq_sum_card_fiberwise hfiber2
  calc ∑ a ∈ partLabels f, (G.gCutEdges f a).ncard
      = ∑ a ∈ partLabels f, (hDfin.toFinset.filter (fun p => f p.1 = a)).card :=
        Finset.sum_congr rfl (fun a ha => (hfilter1 a ha).symm)
    _ = hDfin.toFinset.card := hcard1.symm
    _ = ∑ e ∈ hSfin.toFinset, (hDfin.toFinset.filter (fun p => s(p.1, p.2) = e)).card := hcard2
    _ = ∑ _e ∈ hSfin.toFinset, 2 := Finset.sum_congr rfl hfilter2
    _ = 2 * (G.squareGCrossEdges f).ncard := by
        rw [Finset.sum_const, smul_eq_mul, Set.ncard_eq_toFinset_card _ hSfin]
        ring

/-! ## The vertex handshake and the edges inside a part

Two more facts for the arithmetic of `thm:laman-square-count`. The vertex handshake
`∑_i |P_i| = |V|` (`sum_ncard_eq_card`) is proved like the edge handshake above, by counting
fiberwise, but one-to-one rather than two-to-one: every vertex lies in exactly one part. The bound
on the edges of `G²` inside a part `{x | f x = a}` has the two cases a part of a tight partition
can take (`IsSquareTightPartition.parts`: a singleton or at least three vertices): at
`|P_a| ≥ 3` it is the Laman condition for a `Set` (`IsLaman3.ncard_edgesIn_le`, `Jacobs.lean`);
a singleton part spans no edge (`edgesIn_singleton`), for any partition. -/

/-- **The vertex handshake.** Summing the part sizes `|P_a|` over every label `a` used by `f`
counts each vertex exactly once. -/
theorem sum_ncard_eq_card [Finite V] (f : V → V) :
    ∑ a ∈ partLabels f, {x : V | f x = a}.ncard = Nat.card V := by
  classical
  have hVfin : (Set.univ : Set V).Finite := Set.finite_univ
  have hfiber : ∀ x ∈ hVfin.toFinset, f x ∈ partLabels f := fun x _ =>
    (mem_partLabels f (f x)).mpr ⟨x, rfl⟩
  have hfilter : ∀ a ∈ partLabels f,
      (hVfin.toFinset.filter (fun x => f x = a)).card = {x : V | f x = a}.ncard := by
    intro a _
    rw [Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
    congr 1
    ext x
    simp [hVfin.mem_toFinset]
  calc ∑ a ∈ partLabels f, {x : V | f x = a}.ncard
      = ∑ a ∈ partLabels f, (hVfin.toFinset.filter (fun x => f x = a)).card :=
        Finset.sum_congr rfl (fun a ha => (hfilter a ha).symm)
    _ = hVfin.toFinset.card := (Finset.card_eq_sum_card_fiberwise hfiber).symm
    _ = Nat.card V := by rw [← Set.ncard_eq_toFinset_card _ hVfin, Set.ncard_univ]

/-- **The edges inside a part of at least three vertices.** If `G²` is Laman and a part
`{x | f x = a}` has at least three vertices, `G²`'s edges inside it number at most `3|P_a| - 6`
(additive form). An application of `IsLaman3.ncard_edgesIn_le`, for any partition. -/
theorem edgesIn_square_part_le [Finite V] {f : V → V} (hlaman : G.square.IsLaman3) {a : V}
    (h3 : 3 ≤ {x : V | f x = a}.ncard) :
    (G.square.edgesIn {x : V | f x = a}).ncard + 6 ≤ 3 * {x : V | f x = a}.ncard :=
  hlaman.ncard_edgesIn_le (Set.toFinite _) h3

/-- **The edges inside a singleton part.** A singleton part spans no edge of `G²`: `edgesIn` of a
one-vertex set is empty. -/
theorem edgesIn_square_singleton_part_eq_zero {f : V → V} {a : V}
    (h1 : {x : V | f x = a}.ncard = 1) : (G.square.edgesIn {x : V | f x = a}).ncard = 0 := by
  obtain ⟨v, hv⟩ := Set.ncard_eq_one.mp h1
  rw [hv, edgesIn_singleton, Set.ncard_empty]

/-! ## The edges inside the parts, part by part

The edges of `squareInPartEdges f` split, by their shared label, into the sets
`G.square.edgesIn {x | f x = a}` of edges inside each part. Unlike the cross classes, this needs
no common neighbor: either endpoint gives an edge's label, so distinct labels give disjoint edge
sets. -/

/-- **`squareInPartEdges` is the union of the edges inside the parts.** -/
theorem squareInPartEdges_eq_biUnion [Finite V] (f : V → V) :
    G.squareInPartEdges f =
      ⋃ a ∈ (↑(partLabels f) : Set V), G.square.edgesIn {x : V | f x = a} := by
  ext e
  induction e with | h u w =>
  simp only [mem_squareInPartEdges, Set.mem_iUnion, exists_prop, mem_edgesIn,
    mem_edgeSet, Sym2.coe_mk, Set.insert_subset_iff, Set.singleton_subset_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hadj, hfe⟩
    exact ⟨f u, (mem_partLabels f (f u)).mpr ⟨u, rfl⟩, hadj, rfl, hfe.symm⟩
  · rintro ⟨a, -, hadj, hu, hw⟩
    exact ⟨hadj, hu.trans hw.symm⟩

/-- **Distinct labels give disjoint sets of edges inside the parts.** -/
theorem squareInPartEdges_pairwiseDisjoint [Finite V] (f : V → V) :
    (↑(partLabels f) : Set V).PairwiseDisjoint (fun a => G.square.edgesIn {x : V | f x = a}) := by
  intro a _ a' _ hne
  simp only [Function.onFun, Set.disjoint_left]
  rintro e hea hea'
  induction e with | h u w =>
  simp only [mem_edgesIn, Sym2.coe_mk, Set.insert_subset_iff, Set.singleton_subset_iff,
    Set.mem_ofPred_eq] at hea hea'
  exact hne (hea.2.1.symm.trans hea'.2.1)

/-- **`squareInPartEdges` is the sum of the edges inside each part.** The analogue of the vertex
handshake `sum_ncard_eq_card` for the edges of `G²` inside the parts: each lies in exactly one
part (its shared label), so summing over the parts gives the total, with no factor of two. -/
theorem sum_ncard_edgesIn_part_eq_ncard_squareInPartEdges [Finite V] (f : V → V) :
    ∑ a ∈ partLabels f, (G.square.edgesIn {x : V | f x = a}).ncard =
      (G.squareInPartEdges f).ncard := by
  rw [G.squareInPartEdges_eq_biUnion f,
    (partLabels f).finite_toSet.ncard_biUnion (fun a _ => Set.toFinite _)
      (G.squareInPartEdges_pairwiseDisjoint f),
    finsum_mem_coe_finset]

/-! ## The normal cross edges, part by part

The edges of `squareNormalCrossEdges f` split, by their root, into the sets
`squareNormalCrossEdgesRootedAt f a` of `lem:normal-cross-count`: every normal cross edge has
*some* root by definition (the union needs no tightness), and two distinct parts do not root the
same edge (`IsSquareTightPartition.rootedAt_inj`, which needs tightness). The proof is that of
the in-part decomposition above (`Set.Finite.ncard_biUnion`, `finsum_mem_coe_finset`). -/

/-- **`squareNormalCrossEdges` is the union of the rooted normal cross edges of the parts.** No
tightness is needed: every normal cross edge has *some* root by the definition of
`squareNormalCrossEdges` (the disjointness that makes the root unique is
`IsSquareTightPartition.squareNormalCrossEdgesRootedAt_pairwiseDisjoint`). -/
theorem squareNormalCrossEdges_eq_biUnion [Finite V] (f : V → V) :
    G.squareNormalCrossEdges f =
      ⋃ a ∈ (↑(partLabels f) : Set V), G.squareNormalCrossEdgesRootedAt f a := by
  ext e
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · intro he
    have he' := he
    rw [squareNormalCrossEdges, Set.mem_ofPred_eq] at he'
    obtain ⟨-, v, hv, hfv⟩ := he'
    refine ⟨f v, (mem_partLabels f (f v)).mpr ⟨v, rfl⟩, ?_⟩
    rw [squareNormalCrossEdgesRootedAt, Set.mem_ofPred_eq]
    exact ⟨he, v, hv, rfl⟩
  · rintro ⟨a, -, ha⟩
    rw [squareNormalCrossEdgesRootedAt, Set.mem_ofPred_eq] at ha
    exact ha.1

/-- **Distinct parts give disjoint rooted normal cross edge sets.** Immediate from the uniqueness
of the root for a tight partition (`IsSquareTightPartition.rootedAt_inj`). -/
theorem IsSquareTightPartition.squareNormalCrossEdgesRootedAt_pairwiseDisjoint [Finite V]
    {f : V → V} (hf : G.IsSquareTightPartition f) :
    (↑(partLabels f) : Set V).PairwiseDisjoint (fun a => G.squareNormalCrossEdgesRootedAt f a) := by
  intro a _ a' _ hne
  simp only [Function.onFun, Set.disjoint_left]
  intro e hea hea'
  exact hne (hf.rootedAt_inj hea hea')

/-- **`squareNormalCrossEdges` is the sum of the rooted normal cross edges of the parts.** As
`sum_ncard_edgesIn_part_eq_ncard_squareInPartEdges`, but the disjointness comes from the common
neighbor (`rootedAt_inj`) rather than from the labels, so this one needs tightness. -/
theorem IsSquareTightPartition.sum_ncard_rootedAt_eq_ncard_normalCrossEdges
    [Finite V] {f : V → V} (hf : G.IsSquareTightPartition f) :
    ∑ a ∈ partLabels f, (G.squareNormalCrossEdgesRootedAt f a).ncard =
      (G.squareNormalCrossEdges f).ncard := by
  rw [G.squareNormalCrossEdges_eq_biUnion f,
    (partLabels f).finite_toSet.ncard_biUnion (fun a _ => Set.toFinite _)
      hf.squareNormalCrossEdgesRootedAt_pairwiseDisjoint,
    finsum_mem_coe_finset]

/-! ## Two facts at one part

The inequality at a part (`IsSquareTightPartition.perPart_le`) needs the degree of a singleton
part to be the degree of its vertex, and a part of fewer than three vertices to root no normal
cross edge. -/

/-- **The edges leaving a singleton part are the edges at its vertex.** For a singleton part
`{v}` (`f v = a`, `∀ x, f x = a → x = v`), every edge of `G` at `v` leaves the part, its other
endpoint lying outside it, and conversely; so `gCutEdges f a` is in bijection with
`G.neighborSet v` via `w ↦ s(v, w)`, giving `(gCutEdges f a).ncard = deg_G(v)`. -/
theorem gCutEdges_singleton_part_ncard_eq_degree {f : V → V} {a v : V}
    [Fintype (G.neighborSet v)] (hfv : f v = a) (hsing : ∀ x, f x = a → x = v) :
    (G.gCutEdges f a).ncard = G.degree v := by
  have himg : G.gCutEdges f a = (fun w => s(v, w)) '' G.neighborSet v := by
    ext e
    simp only [gCutEdges, Set.mem_ofPred_eq, Set.mem_image, mem_neighborSet]
    constructor
    · rintro ⟨he, x, y, rfl, hfx, hfy⟩
      obtain rfl := hsing x hfx
      rw [G.mem_edgeSet] at he
      exact ⟨y, he, rfl⟩
    · rintro ⟨w, hvw, rfl⟩
      refine ⟨G.mem_edgeSet.mpr hvw, v, w, rfl, hfv, fun hfw => hvw.ne (hsing w hfw).symm⟩
  have hinj : Set.InjOn (fun w => s(v, w)) (G.neighborSet v) := by
    intro w1 _ w2 _ heq
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨-, h⟩ | ⟨h1, h2⟩
    · exact h
    · exact h2.trans h1
  rw [himg, hinj.ncard_image, ncard_neighborSet_eq_degree]

/-- **No normal cross edge is rooted at a part of fewer than three vertices.** If
`{x | f x = a}.ncard < 3`, no normal cross edge is rooted at `a`: the *moreover* clause of the
classification (`squareNormalCrossEdges_part_three_le`) makes every root a part of at least three
vertices. -/
theorem squareNormalCrossEdgesRootedAt_eq_empty_of_lt_three [Finite V] {f : V → V}
    (hf : G.IsSquareTightPartition f) {a : V} (ha : {x : V | f x = a}.ncard < 3) :
    G.squareNormalCrossEdgesRootedAt f a = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro e he
  induction e with | h u w =>
  rw [squareNormalCrossEdgesRootedAt, Set.mem_ofPred_eq] at he
  obtain ⟨hnormal, v, hv, hfv⟩ := he
  simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq] at hv
  obtain ⟨h3, -⟩ := squareNormalCrossEdges_part_three_le hf hnormal hv.1 hv.2
  rw [hfv] at h3
  omega

/-! ## The special cross edges, part by part

The edges of `squareSpecialCrossEdges f` split, by the label of their common neighbor (unique for
a tight partition), into the sets `squareSpecialCrossEdgesRootedAt f a`, as the normal ones do
(`IsSquareTightPartition.eq_of_common_nbr` gives uniqueness here too, since the endpoints of a
cross edge have distinct labels). Indexing by the label lets this class join the other two in one
sum over `partLabels f`. -/

/-- **Special cross edges rooted at a part** (`def:rooted-cross-edges`). A special cross edge is
**rooted** at the part `{x | f x = a}` when a common neighbor `v` of its endpoints has the
label `a` (`f v = a`). For a tight partition the common neighbor, and hence the root, is unique
(`IsSquareTightPartition.specialRootedAt_inj`). -/
def squareSpecialCrossEdgesRootedAt (G : SimpleGraph V) (f : V → V) (a : V) : Set (Sym2 V) :=
  {e ∈ G.squareSpecialCrossEdges f | ∃ v, (∀ z ∈ e, G.Adj z v) ∧ f v = a}

/-- **The root of a special cross edge is unique.** As `IsSquareTightPartition.rootedAt_inj`: the
two common neighbors coincide by `eq_of_common_nbr` (a special cross edge is a cross edge, so its
endpoints have distinct labels), hence have the same label. -/
theorem IsSquareTightPartition.specialRootedAt_inj [Finite V] {f : V → V}
    (hf : G.IsSquareTightPartition f) {a a' : V} {e : Sym2 V}
    (h : e ∈ G.squareSpecialCrossEdgesRootedAt f a)
    (h' : e ∈ G.squareSpecialCrossEdgesRootedAt f a') : a = a' := by
  induction e with | h u w =>
  obtain ⟨hspecial, v, hv, hfv⟩ := h
  obtain ⟨_, v', hv', hfv'⟩ := h'
  simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq] at hv hv'
  obtain ⟨hcross, -⟩ := hspecial
  obtain ⟨_, hfuw, _⟩ := mem_squareCrossEdges.mp hcross
  have hvv' : v = v' := hf.eq_of_common_nbr hfuw hv.1 hv.2 hv'.1 hv'.2
  rw [← hfv, ← hfv', hvv']

/-- **`squareSpecialCrossEdges` is the union of the rooted special cross edges of the parts.** As
`squareNormalCrossEdges_eq_biUnion`: no tightness is needed, every special cross edge has *some*
root by definition. -/
theorem squareSpecialCrossEdges_eq_biUnion [Finite V] (f : V → V) :
    G.squareSpecialCrossEdges f =
      ⋃ a ∈ (↑(partLabels f) : Set V), G.squareSpecialCrossEdgesRootedAt f a := by
  ext e
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · intro he
    have he' := he
    rw [squareSpecialCrossEdges, Set.mem_ofPred_eq] at he'
    obtain ⟨-, v, hv, hfv⟩ := he'
    refine ⟨f v, (mem_partLabels f (f v)).mpr ⟨v, rfl⟩, ?_⟩
    rw [squareSpecialCrossEdgesRootedAt, Set.mem_ofPred_eq]
    exact ⟨he, v, hv, rfl⟩
  · rintro ⟨a, -, ha⟩
    rw [squareSpecialCrossEdgesRootedAt, Set.mem_ofPred_eq] at ha
    exact ha.1

/-- **Distinct parts give disjoint rooted special cross edge sets.** As
`IsSquareTightPartition.squareNormalCrossEdgesRootedAt_pairwiseDisjoint`. -/
theorem IsSquareTightPartition.squareSpecialCrossEdgesRootedAt_pairwiseDisjoint [Finite V]
    {f : V → V} (hf : G.IsSquareTightPartition f) :
    (↑(partLabels f) : Set V).PairwiseDisjoint
      (fun a => G.squareSpecialCrossEdgesRootedAt f a) := by
  intro a _ a' _ hne
  simp only [Function.onFun, Set.disjoint_left]
  intro e hea hea'
  exact hne (hf.specialRootedAt_inj hea hea')

/-- **`squareSpecialCrossEdges` is the sum of the rooted special cross edges of the parts.** As
`IsSquareTightPartition.sum_ncard_rootedAt_eq_ncard_normalCrossEdges`. -/
theorem IsSquareTightPartition.sum_ncard_specialRootedAt_eq_ncard_specialCrossEdges
    [Finite V] {f : V → V} (hf : G.IsSquareTightPartition f) :
    ∑ a ∈ partLabels f, (G.squareSpecialCrossEdgesRootedAt f a).ncard =
      (G.squareSpecialCrossEdges f).ncard := by
  rw [G.squareSpecialCrossEdges_eq_biUnion f,
    (partLabels f).finite_toSet.ncard_biUnion (fun a _ => Set.toFinite _)
      hf.squareSpecialCrossEdgesRootedAt_pairwiseDisjoint,
    finsum_mem_coe_finset]

/-- **No special cross edge is rooted at a part of at least three vertices.** If
`3 ≤ {x | f x = a}.ncard`, no special cross edge is rooted at `a`: the common neighbor of a
special cross edge forms a singleton part (`squareSpecialCrossEdges_singleton_part`). -/
theorem squareSpecialCrossEdgesRootedAt_eq_empty_of_three_le [Finite V] {f : V → V}
    (hf : G.IsSquareTightPartition f) (hlaman : G.square.IsLaman3) {a : V}
    (ha : 3 ≤ {x : V | f x = a}.ncard) :
    G.squareSpecialCrossEdgesRootedAt f a = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro e he
  induction e with | h u w =>
  obtain ⟨hspecial, v, hv, hfv⟩ := he
  simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq] at hv
  have hsing := squareSpecialCrossEdges_singleton_part hf hlaman hspecial hv.1 hv.2
  have heq : {x : V | f x = f v} = {v} := Set.eq_singleton_iff_unique_mem.mpr ⟨rfl, hsing⟩
  have h1 : {x : V | f x = f v}.ncard = 1 := by rw [heq, Set.ncard_singleton]
  rw [hfv] at h1
  omega

/-- **The special cross edges rooted at a singleton part are the edges of `G²` inside the
neighborhood of its vertex.** For a vertex `v` forming a singleton part
(`∀ x, f x = f v → x = v`), the special cross edges rooted at `v`'s part are exactly the edges of
`G²` inside `N_G(v)` (`edgesIn (neighborSet v)`): a root `v'` has `f v' = f v`, so `v' = v` and
the edge lies inside `N_G(v)`; conversely `mem_squareSpecialCrossEdges_of_singleton_part` makes
each such edge a special cross edge with common neighbor `v`. -/
theorem IsSquareTightPartition.squareSpecialCrossEdgesRootedAt_eq_edgesIn_neighborSet [Finite V]
    {f : V → V} (hf : G.IsSquareTightPartition f) {v : V} (hsing : ∀ x, f x = f v → x = v) :
    G.squareSpecialCrossEdgesRootedAt f (f v) = G.square.edgesIn (G.neighborSet v) := by
  ext e
  induction e with | h u w =>
  constructor
  · rintro ⟨hspecial, v', hv', hfv'⟩
    obtain rfl := (hsing v' hfv').symm
    simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq] at hv'
    have hspecial' := hspecial
    rw [squareSpecialCrossEdges, Set.mem_ofPred_eq] at hspecial'
    obtain ⟨hcross, -⟩ := hspecial'
    obtain ⟨hsq, -, -⟩ := mem_squareCrossEdges.mp hcross
    exact mk_mem_edgesIn hsq ((mem_neighborSet G v u).mpr hv'.1.symm)
      ((mem_neighborSet G v w).mpr hv'.2.symm)
  · intro he
    rw [mem_edgesIn, G.square.mem_edgeSet] at he
    obtain ⟨hadj, hsub⟩ := he
    rw [Sym2.coe_mk, Set.insert_subset_iff, Set.singleton_subset_iff] at hsub
    obtain ⟨hu, hw⟩ := hsub
    obtain ⟨hspecial, -⟩ :=
      hf.mem_squareSpecialCrossEdges_of_singleton_part hsing hu hw hadj.ne
    refine ⟨hspecial, v, ?_, rfl⟩
    simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq]
    exact ⟨((mem_neighborSet G v u).mp hu).symm, ((mem_neighborSet G v w).mp hw).symm⟩

/-! ## The inequality at a part

Every part of a tight partition is a singleton or has at least three vertices
(`IsSquareTightPartition.parts`: no part has two). With the bound on the edges inside a part and
the counts of the normal and special cross edges, this gives the inequality at a part, which the
proof of `thm:laman-square-count` sums over `partLabels f`. -/

/-- **A part is a singleton or has at least three vertices.** -/
theorem IsSquareTightPartition.ncard_eq_one_or_three_le [Finite V] {f : V → V}
    (hf : G.IsSquareTightPartition f) {a : V} (ha : a ∈ partLabels f) :
    {x : V | f x = a}.ncard = 1 ∨ 3 ≤ {x : V | f x = a}.ncard := by
  obtain ⟨v, hv⟩ := (mem_partLabels f a).mp ha
  by_cases hw : ∃ w, w ≠ v ∧ f w = f v
  · obtain ⟨w, hwv, hfw⟩ := hw
    right
    have h3 := (hf.parts hwv hfw).1
    rwa [hv] at h3
  · left
    push Not at hw
    have heq : {x : V | f x = a} = {v} := by
      rw [← hv]
      refine Set.eq_singleton_iff_unique_mem.mpr ⟨rfl, fun x hx => ?_⟩
      by_contra hxv
      exact hw x hxv hx
    rw [heq, Set.ncard_singleton]

/-- **The inequality at a part** (additive form, avoiding `ℕ`-subtraction): at a part
`{x | f x = a}`, the edges of `G²` inside it, the normal cross edges rooted there and the special
cross edges rooted there number at most `3|P_a| - 6 + 2 d_G(A)`. At a part of size `≥ 3`: the Laman
bound (`edgesIn_square_part_le`) covers the in-part edges, the normal-cross count is *exact*
(`ncard_normalCrossEdgesRootedAt_eq_two_mul_gCutEdges`), and no special cross edge roots there
(`squareSpecialCrossEdgesRootedAt_eq_empty_of_three_le`). At a singleton part `{v}`: the in-part and
normal-cross counts are `0`, and the special-cross count is *exactly* `2 deg_G(v) - 3`
(`ncard_edgesIn_neighborSet_square`, via `squareSpecialCrossEdgesRootedAt_eq_edgesIn_neighborSet`) —
equal to `(3 · 1 - 6) + 2 d_G(A)` since `d_G(A) = deg_G(v)`
(`gCutEdges_singleton_part_ncard_eq_degree`). -/
theorem IsSquareTightPartition.perPart_le {f : V → V} [Fintype V] [DecidableRel G.Adj]
    (hf : G.IsSquareTightPartition f)
    (hlaman : G.square.IsLaman3) (hmin : ∀ v, 2 ≤ G.degree v) {a : V} (ha : a ∈ partLabels f) :
    (G.square.edgesIn {x : V | f x = a}).ncard + (G.squareNormalCrossEdgesRootedAt f a).ncard +
        (G.squareSpecialCrossEdgesRootedAt f a).ncard + 6 ≤
      3 * {x : V | f x = a}.ncard + 2 * (G.gCutEdges f a).ncard := by
  rcases hf.ncard_eq_one_or_three_le ha with h1 | h3
  · obtain ⟨v, hv⟩ := Set.ncard_eq_one.mp h1
    have hfv : f v = a := by
      have hvmem : v ∈ {x : V | f x = a} := by rw [hv]; rfl
      exact hvmem
    have hsing : ∀ x, f x = f v → x = v := by
      intro x hfx
      have hxmem : x ∈ {x : V | f x = a} := hfx.trans hfv
      rw [hv] at hxmem
      exact hxmem
    have hsing' : ∀ x, f x = a → x = v := by rw [← hfv]; exact hsing
    have hinpart : (G.square.edgesIn {x : V | f x = a}).ncard = 0 :=
      edgesIn_square_singleton_part_eq_zero h1
    have hrooted : (G.squareNormalCrossEdgesRootedAt f a).ncard = 0 := by
      rw [squareNormalCrossEdgesRootedAt_eq_empty_of_lt_three hf (by omega)]
      exact Set.ncard_empty _
    have hspecial : (G.squareSpecialCrossEdgesRootedAt f a).ncard + 3 = 2 * G.degree v := by
      rw [← hfv, hf.squareSpecialCrossEdgesRootedAt_eq_edgesIn_neighborSet hsing]
      exact ncard_edgesIn_neighborSet_square hlaman (hmin v)
    have hcut : (G.gCutEdges f a).ncard = G.degree v :=
      gCutEdges_singleton_part_ncard_eq_degree hfv hsing'
    omega
  · have hinpart := edgesIn_square_part_le hlaman h3
    have hrooted : (G.squareNormalCrossEdgesRootedAt f a).ncard =
        2 * (G.gCutEdges f a).ncard :=
      hf.ncard_normalCrossEdgesRootedAt_eq_two_mul_gCutEdges hlaman h3
    have hspecial : (G.squareSpecialCrossEdgesRootedAt f a).ncard = 0 := by
      rw [squareSpecialCrossEdgesRootedAt_eq_empty_of_three_le hf hlaman h3]
      exact Set.ncard_empty _
    omega

/-! ## The sum over the parts and the theorem -/

/-- **Summing the inequality at a part over `partLabels f`.** Folds the four sums over the parts
into the classes' total `ncard`s (`sum_ncard_edgesIn_part_eq_ncard_squareInPartEdges`,
`sum_ncard_rootedAt_eq_ncard_normalCrossEdges`,
`sum_ncard_specialRootedAt_eq_ncard_specialCrossEdges`) and the two handshakes (`sum_ncard_eq_card`,
`sum_gCutEdges_eq_two_mul_squareGCrossEdges`). -/
theorem IsSquareTightPartition.sum_perPart_le {f : V → V} [Fintype V] [DecidableRel G.Adj]
    (hf : G.IsSquareTightPartition f) (hlaman : G.square.IsLaman3) (hmin : ∀ v, 2 ≤ G.degree v) :
    (G.squareInPartEdges f).ncard + (G.squareNormalCrossEdges f).ncard +
        (G.squareSpecialCrossEdges f).ncard + 6 * (partLabels f).card ≤
      3 * Nat.card V + 4 * (G.squareGCrossEdges f).ncard := by
  have h1 : ∑ a ∈ partLabels f,
      ((G.square.edgesIn {x : V | f x = a}).ncard + (G.squareNormalCrossEdgesRootedAt f a).ncard +
          (G.squareSpecialCrossEdgesRootedAt f a).ncard + 6) ≤
        ∑ a ∈ partLabels f, (3 * {x : V | f x = a}.ncard + 2 * (G.gCutEdges f a).ncard) :=
    Finset.sum_le_sum (fun a ha => hf.perPart_le hlaman hmin ha)
  have hL1 : ∑ a ∈ partLabels f, (G.square.edgesIn {x : V | f x = a}).ncard =
      (G.squareInPartEdges f).ncard := sum_ncard_edgesIn_part_eq_ncard_squareInPartEdges f
  have hL2 : ∑ a ∈ partLabels f, (G.squareNormalCrossEdgesRootedAt f a).ncard =
      (G.squareNormalCrossEdges f).ncard := hf.sum_ncard_rootedAt_eq_ncard_normalCrossEdges
  have hL3 : ∑ a ∈ partLabels f, (G.squareSpecialCrossEdgesRootedAt f a).ncard =
      (G.squareSpecialCrossEdges f).ncard :=
    hf.sum_ncard_specialRootedAt_eq_ncard_specialCrossEdges
  have hL4 : ∑ _a ∈ partLabels f, (6 : ℕ) = 6 * (partLabels f).card := by
    rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hR1 : ∑ a ∈ partLabels f, {x : V | f x = a}.ncard = Nat.card V := sum_ncard_eq_card f
  have hR2 : ∑ a ∈ partLabels f, (G.gCutEdges f a).ncard =
      2 * (G.squareGCrossEdges f).ncard := sum_gCutEdges_eq_two_mul_squareGCrossEdges f
  simp only [Finset.sum_add_distrib, hL1, hL2, hL3, hL4, ← Finset.mul_sum, hR1, hR2] at h1
  linarith [h1]

/-- **The classification, summed to a single `ncard` identity.** `E(G²)` splits into the four
classes, pairwise disjoint. -/
theorem square_ncard_eq_sum_classes [Finite V] {f : V → V} (hf : G.IsSquareTightPartition f) :
    G.square.edgeSet.ncard = (G.squareInPartEdges f).ncard + (G.squareGCrossEdges f).ncard +
      (G.squareNormalCrossEdges f).ncard + (G.squareSpecialCrossEdges f).ncard := by
  have hAB := Set.ncard_union_eq (disjoint_inPart_gCross f) (Set.toFinite (G.squareInPartEdges f))
    (Set.toFinite (G.squareGCrossEdges f))
  have hCD : (G.squareCrossEdges f).ncard =
      (G.squareNormalCrossEdges f).ncard + (G.squareSpecialCrossEdges f).ncard := by
    conv_lhs => rw [squareCrossEdges_eq_union f]
    exact Set.ncard_union_eq (squareNormalCrossEdges_disjoint_special hf) (Set.toFinite _)
      (Set.toFinite _)
  have hABvsCD :
      Disjoint (G.squareInPartEdges f ∪ G.squareGCrossEdges f) (G.squareCrossEdges f) :=
    Set.disjoint_union_left.mpr ⟨disjoint_inPart_cross f, disjoint_gCross_cross f⟩
  have hfull := Set.ncard_union_eq hABvsCD
    (Set.toFinite (G.squareInPartEdges f ∪ G.squareGCrossEdges f))
    (Set.toFinite (G.squareCrossEdges f))
  rw [square_edgeSet_eq_union f]
  omega

/-- **The number of labels in use is `numParts` of the labeling of `G.shadowGraph`.** -/
theorem partLabels_card_eq_numParts [Finite V] (f : V → V) :
    (partLabels f).card = G.shadowGraph.numParts f := by
  simp only [Graph.numParts, shadowGraph_vertexSet, partLabels,
    ← Set.ncard_eq_toFinset_card (f '' Set.univ) (Set.finite_univ.image f)]

/-- **The counting bound for Laman squares** (`thm:laman-square-count`; Jackson–Jordán 2008
Theorem 5.3). Let `G` be a simple graph of minimum degree at least two on a finite vertex set
`V`, and suppose `G²` is Laman. Then `|E(G²)| ≤ 3|V| - 6 - def(G̃)`, with `def(G̃)` the
deficiency of `G.shadowGraph` at `n = 3` (`D = 6`). `V` need not be nonempty: for `V = ∅` both
sides are `0`, as the empty partition has value `-6` (`fmlnote:normal-cross-split`). Against a
tight partition (`Graph.exists_isTightPartition`), the four classes
(`square_ncard_eq_sum_classes`) are bounded by `IsSquareTightPartition.sum_perPart_le`. -/
theorem laman_square_count {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hmin : ∀ v, 2 ≤ G.degree v) (hlaman : G.square.IsLaman3) :
    (G.square.edgeSet.ncard : ℤ) ≤ 3 * (Nat.card V : ℤ) - 6 - G.shadowGraph.deficiency 3 := by
  obtain ⟨f, hf0⟩ := G.shadowGraph.exists_isTightPartition 3
  have hf : G.IsSquareTightPartition f := hf0
  have hsum := hf.sum_perPart_le hlaman hmin
  have hclass := G.square_ncard_eq_sum_classes hf
  have hgcross : (G.squareGCrossEdges f).ncard = (G.shadowGraph.crossingEdges f).ncard :=
    squareGCrossEdges_ncard_eq_crossingEdges f
  have hparts : (partLabels f).card = G.shadowGraph.numParts f := partLabels_card_eq_numParts f
  have hdef : G.shadowGraph.deficiency 3 = G.shadowGraph.partitionDef 3 f := hf.symm
  rw [Graph.partitionDef, show Graph.bodyBarDim 3 = 6 from by decide] at hdef
  omega

end SimpleGraph
