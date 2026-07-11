/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
-- Plain (legacy) `import`, not the module system: `Molecular/{Deficiency,Molecule/Carrier}.lean`
-- are not `module` files, and a `module` file cannot import a non-`module` one. Do not convert
-- this file to `module`/`public import` until those dependencies are converted first.
import CombinatorialRigidity.Jacobs
import CombinatorialRigidity.Molecular.Deficiency
import CombinatorialRigidity.Molecular.Molecule.Carrier

/-!
# The counting bound for Laman squares: edge classification (`sec:jacobs-counting`)

Phase 32. Jackson–Jordán 2008 (*On the rigidity of molecular graphs*, Combinatorica **28**)
prove their counting bound (Theorem 5.3) by classifying the edges of `G²` against a partition
of `V` attaining the deficiency. This file lays the foundations that classification needs:
the bridge from the `SimpleGraph V` square `G²` to the `Graph`-carrier tight-partition
machinery of `Molecular/Deficiency.lean`, and the four edge classes with the structural facts
that make them well defined.

## The shadow-carrier bridge (encoding decision (b))

A "tight partition of `V` at `D = 6`" is, concretely, a labeling `f : V → V` that is a tight
partition of the shadowing multigraph `G.shadowGraph` (`Molecular/Molecule/Carrier.lean`) at
`n = 3` (where `bodyBarDim 3 = 6`); the packaged predicate is `SimpleGraph.IsSquareTightPartition`.
The shadow graph has `V(G.shadowGraph) = univ` and `G.shadowGraph.Adj = G.Adj`
(`shadowGraph_adj_iff`), so the tight-partition lemmas of `Molecular/Deficiency.lean` — stated
`D`-generically over `Graph α β` — transport directly to `SimpleGraph`/`f : V → V` language. The
one transported here is common-neighbor uniqueness (`IsTightPartition.eq_of_common_nbr`, JJ
Lemma 3.2 at `D ≥ 5`): `IsSquareTightPartition.eq_of_common_nbr`.

## The four edge classes (encoding decision (a))

Following Jackson–Jordán §5, an edge `e = uw` of `G²` is classified by two binary criteria — do
its endpoints share a part (`(e.map f).IsDiag`, i.e. `f u = f w`), and is `e` an edge of `G`:

* `squareInPartEdges` — edges of `G²` inside a part;
* `squareGCrossEdges` — edges of `G` joining distinct parts (their count is `d_G(P)`);
* `squareCrossEdges` — **cross edges**: edges of `G²` joining distinct parts that are not edges
  of `G`. Such an edge has a common neighbor (`exists_apex_of_mem_squareCrossEdges`), unique
  under tightness (`IsSquareTightPartition.eq_of_common_nbr`).

A cross edge `uw` with common neighbor `v` is **normal** if `v` shares a part with an endpoint
(`f v ∈ e.map f`) and **special** otherwise:

* `squareNormalCrossEdges`, `squareSpecialCrossEdges`.

## Main results

* `SimpleGraph.square_edgeSet_eq_union` — `E(G²)` is the union of the in-part, `G`-cross, and
  cross classes, pairwise disjoint (`disjoint_inPart_gCross`, `disjoint_inPart_cross`,
  `disjoint_gCross_cross`).
* `SimpleGraph.squareCrossEdges_eq_union` — cross edges split as normal ∪ special,
* `SimpleGraph.squareNormalCrossEdges_disjoint_special` — disjointly, under tightness;
* `SimpleGraph.squareGCrossEdges_ncard_eq_crossingEdges` — the `G`-cross class numbers `d_G(P)`.

Together these are the disjoint-union half of `lem:square-cross-classification`. The *moreover*
clause is the common-neighbor-part characterization, established here by transporting
`Graph.IsTightPartition.parts` (`SimpleGraph.IsSquareTightPartition.parts`) and using
`SimpleGraph.IsLaman3.degree_le_three`:

* `SimpleGraph.squareSpecialCrossEdges_singleton_part` — the common neighbor of a special cross
  edge forms a singleton part;
* `SimpleGraph.squareNormalCrossEdges_part_three_le` — the common neighbor of a normal cross
  edge lies in a part of ≥ 3 vertices, together with exactly one endpoint of the edge.

This completes `lem:square-cross-classification`. The JJ eq. (5)–(7) counting lemmas
(`lem:singleton-part-neighborhood`, `lem:normal-cross-count`) build on it in later commits. See
`notes/Phase32.md` and `blueprint/src/chapter/jacobs.tex` (`sec:jacobs-counting`).
-/

open scoped Graph

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-! ## The shadow-carrier tight partition -/

/-- **A tight partition of `V` at `D = 6`**: a labeling `f : V → V` that is a tight partition
(`Graph.IsTightPartition`) of the shadowing multigraph `G.shadowGraph` at `n = 3`, where
`bodyBarDim 3 = 6` is Jackson–Jordán's `D`. This is the partition against which the counting
bound (JJ Theorem 5.3) classifies the edges of `G²`. -/
def IsSquareTightPartition (G : SimpleGraph V) (f : V → V) : Prop :=
  G.shadowGraph.IsTightPartition 3 f

/-- Adjacency in the shadow carrier is exactly adjacency in `G`: `G.shadowGraph.Adj u v ↔
G.Adj u v`. Unfolds `Graph.Adj` to `∃ e, IsLink e u v` and applies `shadowGraph_isLink_iff`. -/
theorem shadowGraph_adj_iff [Finite V] (u v : V) : G.shadowGraph.Adj u v ↔ G.Adj u v := by
  rw [Graph.Adj]
  exact shadowGraph_isLink_iff G u v

/-- **Uniqueness of the common neighbor of a cross pair**, in `SimpleGraph` terms
(`lem:tight-partition-cross-pair-nbr` transported through the shadow carrier). Two vertices
`u, w` in distinct parts of a tight partition (`f u ≠ f w`) have at most one common neighbor:
any two common neighbors `v, v'` coincide. This makes the common neighbor of a cross edge —
and hence the normal/special dichotomy — well defined.

`bodyBarDim 3 = 6 ≥ 5` supplies the `D ≥ 5` hypothesis of `Graph.IsTightPartition.eq_of_common_nbr`;
`G.shadowGraph` is simple, and its adjacencies are `G`'s (`shadowGraph_adj_iff`). -/
theorem IsSquareTightPartition.eq_of_common_nbr [Finite V] {f : V → V}
    (hf : G.IsSquareTightPartition f) {u w v v' : V} (hfuw : f u ≠ f w)
    (huv : G.Adj u v) (hwv : G.Adj w v) (huv' : G.Adj u v') (hwv' : G.Adj w v') :
    v = v' :=
  Graph.IsTightPartition.eq_of_common_nbr hf (by decide) G.shadowGraph_simple hfuw
    ((shadowGraph_adj_iff u v).mpr huv) ((shadowGraph_adj_iff v w).mpr hwv.symm)
    ((shadowGraph_adj_iff u v').mpr huv') ((shadowGraph_adj_iff v' w).mpr hwv'.symm)

/-- Helper for the pair-multiplicity and triangle-exclusion transports below: an edge of `G`
between vertices carrying two labels in `S` is a shadow-graph crossing edge within `S`. -/
private theorem mem_crossingEdgesWithin_shadowGraph [Finite V] {f : V → V} {S : Set V} {x y : V}
    (hxy : G.Adj x y) (hx : f x ∈ S) (hy : f y ∈ S) (hne : f x ≠ f y) :
    (Sum.inl s(x, y) : Sym2 V ⊕ Fin (6 * (Nat.card V - 1) + 1)) ∈
      G.shadowGraph.crossingEdgesWithin f S :=
  ⟨⟨x, y, hxy, rfl⟩, x, y, ⟨hxy, rfl⟩, hx, hy, hne⟩

/-- **At most one edge between two parts, transported** (`lem:tight-partition-cross-pair-mult`).
If `v` is adjacent to two distinct vertices `u, w` (`u ≠ w`) that share a part (`f u = f w`)
different from `v`'s own (`f v ≠ f u`), tightness is violated: the edges `vu`, `vw` both cross
between the parts `f v` and `f u`, exceeding
`Graph.IsTightPartition.crossingEdgesWithin_pair_le_one`'s bound of one (`D = 6 ≥ 3`). This is
the "two neighbors in one part put two edges between it and `{v}`" step of
`lem:singleton-part-neighborhood`. -/
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

/-- **No triangle across three distinct parts, transported** (`lem:tight-partition-subfamily`).
Three pairwise-adjacent vertices `u, v, w` carrying three pairwise distinct labels violate
tightness: the edges `uv`, `vw`, `uw` all cross within the three-label subfamily
`{f u, f v, f w}`, exceeding `Graph.IsTightPartition.subfamily_le`'s bound (`(D-1)*3 ≤ D*2`
forces `D ≤ 3`, contradicting `D = 6`). This is the "nonadjacent" step of
`lem:singleton-part-neighborhood`. -/
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

/-- Edges of `G` joining distinct parts. Their number is Jackson–Jordán's `d_G(P)`. As `G` is a
subgraph of `G²`, these are edges of `G²`. -/
def squareGCrossEdges (G : SimpleGraph V) (f : V → V) : Set (Sym2 V) :=
  {e ∈ G.edgeSet | ¬ (e.map f).IsDiag}

/-- **Cross edges**: edges of `G²` joining distinct parts that are not edges of `G`. A cross
edge's endpoints have a (unique, under tightness) common neighbor
(`exists_apex_of_mem_squareCrossEdges`, `IsSquareTightPartition.eq_of_common_nbr`). -/
def squareCrossEdges (G : SimpleGraph V) (f : V → V) : Set (Sym2 V) :=
  {e ∈ G.square.edgeSet | ¬ (e.map f).IsDiag ∧ e ∉ G.edgeSet}

/-- **Normal cross edges**: a cross edge with a common neighbor `v` whose part contains an
endpoint (`f v ∈ e.map f`, i.e. `f v = f u` or `f v = f w`). -/
def squareNormalCrossEdges (G : SimpleGraph V) (f : V → V) : Set (Sym2 V) :=
  {e ∈ G.squareCrossEdges f | ∃ v, (∀ z ∈ e, G.Adj z v) ∧ f v ∈ e.map f}

/-- **Special cross edges**: a cross edge with a common neighbor `v` in a part containing neither
endpoint (`f v ∉ e.map f`). -/
def squareSpecialCrossEdges (G : SimpleGraph V) (f : V → V) : Set (Sym2 V) :=
  {e ∈ G.squareCrossEdges f | ∃ v, (∀ z ∈ e, G.Adj z v) ∧ f v ∉ e.map f}

theorem mem_squareInPartEdges {f : V → V} {u w : V} :
    s(u, w) ∈ G.squareInPartEdges f ↔ G.square.Adj u w ∧ f u = f w := by
  simp only [squareInPartEdges, Set.mem_setOf_eq, mem_edgeSet, Sym2.map_mk, Sym2.mk_isDiag_iff]

theorem mem_squareGCrossEdges {f : V → V} {u w : V} :
    s(u, w) ∈ G.squareGCrossEdges f ↔ G.Adj u w ∧ f u ≠ f w := by
  simp only [squareGCrossEdges, Set.mem_setOf_eq, mem_edgeSet, Sym2.map_mk, Sym2.mk_isDiag_iff]

theorem mem_squareCrossEdges {f : V → V} {u w : V} :
    s(u, w) ∈ G.squareCrossEdges f ↔ G.square.Adj u w ∧ f u ≠ f w ∧ ¬ G.Adj u w := by
  simp only [squareCrossEdges, Set.mem_setOf_eq, mem_edgeSet, Sym2.map_mk, Sym2.mk_isDiag_iff]

/-! ## The classification (disjoint-union half)

`E(G²)` splits into the in-part, `G`-cross, and cross classes (`square_edgeSet_eq_union`),
pairwise disjoint; the cross class splits further into normal and special
(`squareCrossEdges_eq_union`), disjointly under tightness. This is the first sentence of
`lem:square-cross-classification`; its *moreover* clause is deferred. -/

/-- Every cross edge has a common neighbor: a `G²`-edge that is not a `G`-edge joins two vertices
at graph distance exactly two, which by definition of the square share a neighbor in `G`. -/
theorem exists_apex_of_mem_squareCrossEdges {f : V → V} {e : Sym2 V}
    (h : e ∈ G.squareCrossEdges f) : ∃ v, ∀ z ∈ e, G.Adj z v := by
  induction e with | h u w =>
  simp only [squareCrossEdges, Set.mem_setOf_eq, mem_edgeSet, square_adj] at h
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

/-- **`E(G²)` is the union of the in-part, `G`-cross, and cross classes.** An edge of `G²` is
in-part or crosses parts; a cross edge is an edge of `G` (`G`-cross) or not (cross). -/
theorem square_edgeSet_eq_union (f : V → V) :
    G.square.edgeSet =
      G.squareInPartEdges f ∪ G.squareGCrossEdges f ∪ G.squareCrossEdges f := by
  ext e
  simp only [squareInPartEdges, squareGCrossEdges, squareCrossEdges, Set.mem_union,
    Set.mem_setOf_eq]
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

/-- **Cross edges split as normal ∪ special.** Every cross edge has a common neighbor
(`exists_apex_of_mem_squareCrossEdges`), whose part either contains an endpoint (normal) or does
not (special). -/
theorem squareCrossEdges_eq_union (f : V → V) :
    G.squareCrossEdges f = G.squareNormalCrossEdges f ∪ G.squareSpecialCrossEdges f := by
  ext e
  simp only [squareNormalCrossEdges, squareSpecialCrossEdges, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · intro he
    obtain ⟨v, hv⟩ := exists_apex_of_mem_squareCrossEdges he
    by_cases hfv : f v ∈ e.map f
    · exact Or.inl ⟨he, v, hv, hfv⟩
    · exact Or.inr ⟨he, v, hv, hfv⟩
  · rintro (⟨he, _⟩ | ⟨he, _⟩) <;> exact he

/-- **Normal and special cross edges are disjoint**, under tightness. A cross edge in both would
have a common neighbor `v` inside an endpoint's part and a common neighbor `v'` outside both; by
uniqueness of the common neighbor (`IsSquareTightPartition.eq_of_common_nbr`) `v = v'`, a
contradiction. -/
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

/-- **The `G`-cross class numbers `d_G(P)`.** The `G`-edges joining distinct parts biject, via
`s(x, y) ↦ Sum.inl s(x, y)`, with the crossing edges `G.shadowGraph.crossingEdges f` of the
shadow carrier — whose count is Jackson–Jordán's `d_G(P)` (the `crossingEdges` term of
`partitionDef`/`deficiency`). This is the "numbering `d_G(P)`" clause of
`lem:square-cross-classification` and the crossing-count bridge the Thm 5.3 assembly consumes. -/
theorem squareGCrossEdges_ncard_eq_crossingEdges (f : V → V) :
    (G.squareGCrossEdges f).ncard = (G.shadowGraph.crossingEdges f).ncard := by
  have himg : G.shadowGraph.crossingEdges f =
      (Sum.inl : Sym2 V → Sym2 V ⊕ Fin (6 * (Nat.card V - 1) + 1)) '' (G.squareGCrossEdges f) := by
    ext e
    simp only [Graph.crossingEdges, squareGCrossEdges, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨_, x, y, ⟨hadj, hlink⟩, hne⟩
      exact ⟨s(x, y), ⟨hadj, hne⟩, hlink⟩
    · rintro ⟨e', ⟨hadj, hne⟩, rfl⟩
      refine e'.ind (fun x y => ?_) hadj hne
      intro hadj hne
      exact ⟨⟨x, y, hadj, rfl⟩, x, y, ⟨hadj, rfl⟩, hne⟩
  rw [himg, (Sum.inl_injective.injOn).ncard_image]

/-! ## The classification (moreover clause)

The common-neighbor part of a special cross edge is a singleton, and of a normal cross edge a
part of ≥ 3 vertices containing exactly one endpoint. Both rest on the tight-partition part
dichotomy transported through the shadow bridge (`IsSquareTightPartition.parts`); the special
case additionally uses the Laman degree bound (`IsLaman3.degree_le_three`). This is the
*moreover* clause of `lem:square-cross-classification`. -/

/-- **Part dichotomy for the square's tight partition** (`lem:tight-partition-parts` transported
through the shadow carrier). If two distinct vertices `v ≠ w` share a part (`f w = f v`), then
`v`'s part has at least three vertices and `v` has at least two neighbors inside it. The vertex
half rewrites `Graph.IsTightPartition.parts`'s `V(G.shadowGraph) = univ` slice; the neighbor
half converts its shadow-edge count through the bijection `y ↦ Sum.inl s(v, y)` between `v`'s
in-part shadow-edges and `v`'s in-part `G`-neighbors. -/
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
      simp only [hTe, hTv, Set.mem_setOf_eq, Set.mem_image]
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

/-- **Special cross edge ⇒ singleton common-neighbor part.** The common neighbor `v` of a special
cross edge `s(u, w)` forms a singleton part: every vertex with label `f v` is `v` itself.

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
  haveI : Fintype ↥(G.neighborSet v) := Fintype.ofFinite _
  rw [squareSpecialCrossEdges, Set.mem_setOf_eq] at he
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

/-- **Normal cross edge ⇒ common neighbor in a part of ≥ 3 vertices, with exactly one endpoint.**
The common neighbor `v` of a normal cross edge `s(u, w)` shares a part with exactly one endpoint
(the endpoints lie in distinct parts, `f u ≠ f w`), and that part has at least three vertices.

`v` shares its part with the endpoint `u` (or `w`) it is `f`-equal to; those two are adjacent and
distinct, so the part is not a singleton, hence has ≥ 3 vertices
(`IsSquareTightPartition.parts`). -/
theorem squareNormalCrossEdges_part_three_le [Finite V] {f : V → V}
    (hf : G.IsSquareTightPartition f)
    {u w v : V} (he : s(u, w) ∈ G.squareNormalCrossEdges f)
    (huv : G.Adj u v) (hwv : G.Adj w v) :
    3 ≤ {x | f x = f v}.ncard ∧ ((f u = f v ∧ f w ≠ f v) ∨ (f w = f v ∧ f u ≠ f v)) := by
  rw [squareNormalCrossEdges, Set.mem_setOf_eq] at he
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

For a singleton part `{v}`, `N_G(v)` is a clique of `G²` (`isClique_neighborSet_square`,
unconditional) numbering `2 d_G(v) - 3` edges (`ncard_edgesIn_neighborSet_square`, Phase 32's
`Jacobs.lean`, also unconditional). What the singleton-part hypothesis supplies is that every
one of those clique edges is a *special cross* edge with common neighbor `v`
(JJ eq. (5), (7)): two neighbors of `v` lie in distinct parts (else two edges would cross
between one part and `v`'s singleton part, `not_adj_adj_of_same_part`) and are themselves
nonadjacent in `G` (else a triangle would cross a three-part subfamily,
`not_adj_triangle`), so the edge between them is a cross edge; it is special because `v`'s
singleton part contains neither endpoint, and unique to `v` by `eq_of_common_nbr`. -/

/-- **Special cross edges at a singleton part; JJ eq. (5), (7)**
(`lem:singleton-part-neighborhood`). For a singleton part `{v}` (`∀ x, f x = f v → x = v`), two
distinct neighbors `u, w` of `v` form a special cross edge of `G²` whose unique common neighbor
is `v`. -/
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
    rw [squareSpecialCrossEdges, Set.mem_setOf_eq]
    refine ⟨hcross, v, ?_, ?_⟩
    · simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq]
      exact ⟨hvu.symm, hvw.symm⟩
    · rw [Sym2.map_mk, Sym2.mem_iff, not_or]
      exact ⟨hfvu, hfvw⟩
  refine ⟨hspecial, ?_⟩
  intro z hz
  simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq] at hz
  exact (hf.eq_of_common_nbr hfuw hvu.symm hvw.symm hz.1 hz.2).symm

/-! ## The converse: every special cross edge arises from a unique singleton part
(`lem:singleton-part-converse`) -/

/-- **Every special cross edge arises from exactly one singleton part**
(`lem:singleton-part-converse`). Existence unfolds the special-cross-edge apex `v` given by the
membership `he` and applies
`squareSpecialCrossEdges_singleton_part` for the singleton-part half, `mk_mem_edgesIn` for the
`edgesIn`-membership half; uniqueness is `IsSquareTightPartition.eq_of_common_nbr` applied to any
other witnessing common neighbor `v'`. -/
theorem exists_unique_singleton_part_of_mem_squareSpecialCrossEdges [Finite V] {f : V → V}
    (hf : G.IsSquareTightPartition f) (hlaman : G.square.IsLaman3) {e : Sym2 V}
    (he : e ∈ G.squareSpecialCrossEdges f) :
    ∃! v, (∀ x, f x = f v → x = v) ∧ e ∈ G.square.edgesIn (G.neighborSet v) := by
  induction e with | h u w =>
  have he' := he
  rw [squareSpecialCrossEdges, Set.mem_setOf_eq] at he'
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
of its endpoints. Following Jackson–Jordán, say the edge is **rooted** at the part containing `v`
(labeled `f v`); the root is well defined (`IsSquareTightPartition.rootedAt_inj`, via
common-neighbor uniqueness) and — by the *moreover* clause of `lem:square-cross-classification`
(`squareNormalCrossEdges_part_three_le`) — a part of at least three vertices.

The count of normal cross edges rooted at a fixed part `A` with `|A| ≥ 3` is `2 · d_G(A)`
(JJ eq. (6)), where `d_G(A)` is the number of `G`-edges with exactly one endpoint in `A`. The
`fmlnote:normal-cross-split` decomposition splits that count into the **local count** — each
crossing edge `vw` at `A` (`v ∈ A`, `w ∉ A`) contributes exactly two pairs `(vw, u)`, indexed by
the in-part neighbors `u ∈ N_G(v) ∩ A` of `v` (`ncard_inPartNeighbors_eq_two`) — and the global
injectivity of the pair-to-edge assignment `(vw, u) ↦ s(u, w)`. This commit lands the "rooted
at" definition, the well-definedness of the root, and the local count; the global assembly is a
later slice. -/

/-- **Normal cross edges rooted at a part.** A normal cross edge is **rooted** at the part
`{x | f x = a}` when its common neighbor `v` carries the label `a` (`f v = a`). Under tightness
the common neighbor — and hence the root — is unique (`IsSquareTightPartition.rootedAt_inj`). -/
def squareNormalCrossEdgesRootedAt (G : SimpleGraph V) (f : V → V) (a : V) : Set (Sym2 V) :=
  {e ∈ G.squareNormalCrossEdges f | ∃ v, (∀ z ∈ e, G.Adj z v) ∧ f v = a}

/-- **The root of a normal cross edge is unique** (the "rooted at exactly one part" clause of
`lem:normal-cross-count`). If a normal cross edge is rooted at both `a` and `a'`, then `a = a'`:
its two witnessing common neighbors coincide by `IsSquareTightPartition.eq_of_common_nbr` (the
endpoints lie in distinct parts, so `f u ≠ f w`), hence carry the same label. -/
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

/-- **The local count: each crossing edge at a big part contributes exactly two pairs** (the
local half of `lem:normal-cross-count` / JJ eq. (6), per `fmlnote:normal-cross-split`). Let `v`
lie in a part of at least two vertices (witnessed by a distinct part-mate `v₀`, `f v₀ = f v`) and
have an out-of-part neighbor `w` (`G.Adj v w`, `f w ≠ f v`) — i.e. `v` lies on a crossing edge of
its part. Then `v` has **exactly two** neighbors inside its own part.

Lower bound: the in-part-neighbor half of `IsSquareTightPartition.parts`. Upper bound: `v`'s
in-part and out-of-part neighbors partition `N_G(v)`, whose size is `d_G(v) ≤ 3`
(`IsLaman3.degree_le_three`); the out-of-part side is nonempty (it holds `w`), leaving at most two
neighbors inside the part. -/
theorem IsSquareTightPartition.ncard_inPartNeighbors_eq_two [Finite V] {f : V → V}
    (hf : G.IsSquareTightPartition f) (hlaman : G.square.IsLaman3)
    {v v₀ w : V} (hv₀ : v₀ ≠ v) (hfv₀ : f v₀ = f v)
    (hvw : G.Adj v w) (hfw : f w ≠ f v) :
    {u | G.Adj v u ∧ f u = f v}.ncard = 2 := by
  classical
  haveI : Fintype ↥(G.neighborSet v) := Fintype.ofFinite _
  have hlow : 2 ≤ {u | G.Adj v u ∧ f u = f v}.ncard := (hf.parts hv₀ hfv₀).2
  have hunion : {u | G.Adj v u ∧ f u = f v} ∪ {u | G.Adj v u ∧ f u ≠ f v}
      = G.neighborSet v := by
    ext u
    simp only [Set.mem_union, Set.mem_setOf_eq, mem_neighborSet]
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

/-- **Producing a normal cross edge from a crossing edge and an in-part neighbor** (the
constructive core of `lem:normal-cross-count`, JJ eq. (6)). Let `v` have an in-part neighbor `u`
(`G.Adj v u`, `f u = f v`) and an out-of-part neighbor `w` (`G.Adj v w`, `f w ≠ f v`). Then
`s(u, w)` is a normal cross edge rooted at `v`'s part (label `f v`), and `v` is its unique common
neighbor.

`s(u, w)` is a `G²`-edge (`u, w ∈ N_G(v)`, `u ≠ w`, `isClique_neighborSet_square`), joins
distinct parts (`f u = f v ≠ f w`), and is not a `G`-edge — otherwise `vw` and `uw` would be two
edges between `v`'s part and `w`'s (`not_adj_adj_of_same_part`). Its common neighbor `v` lies in
`u`'s part (`f v = f u`), so the edge is normal and rooted at `f v`; uniqueness of the common
neighbor is `eq_of_common_nbr`. This is the map `(vw, u) ↦ s(u, w)` of the double count; the
residual global assembly (`lem:normal-cross-count`) sums it over `A`'s `d_G(A)` crossing edges. -/
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
    rw [squareNormalCrossEdges, Set.mem_setOf_eq]
    refine ⟨hcross, v, ?_, ?_⟩
    · simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq]
      exact ⟨hu.symm, hw.symm⟩
    · rw [Sym2.map_mk, Sym2.mem_iff]
      exact Or.inl hfu.symm
  refine ⟨?_, ?_⟩
  · rw [squareNormalCrossEdgesRootedAt, Set.mem_setOf_eq]
    refine ⟨hnormal, v, ?_, rfl⟩
    simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq]
    exact ⟨hu.symm, hw.symm⟩
  · intro z hz
    simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq] at hz
    exact (hf.eq_of_common_nbr hfuw hu.symm hw.symm hz.1 hz.2).symm

end SimpleGraph
