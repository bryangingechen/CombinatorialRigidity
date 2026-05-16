/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.EdgesIn
import CombinatorialRigidity.Mathlib.Combinatorics.SimpleGraph.Finite
import CombinatorialRigidity.Mathlib.Data.Finset.Card
import CombinatorialRigidity.Mathlib.Data.Sym.Sym2
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Card.Arithmetic

/-!
# `(k, ℓ)`-sparsity and `(k, ℓ)`-tightness

A simple graph `G` is `(k, ℓ)`-**sparse** if every finite set `s` of
vertices spans at most `k * #s − ℓ` edges, whenever the bound is
non-negative. It is `(k, ℓ)`-**tight** if it is sparse and the total edge
count meets the bound exactly: `#E + ℓ = k * #V`.

These count conditions are the combinatorial side of the rigidity
matroid. The Laman case `(k, ℓ) = (2, 3)` is treated downstream in
`Laman.lean`.

## Main definitions

* `SimpleGraph.IsSparse G k ℓ` — for every finite `s : Finset V` with
  `ℓ ≤ k * #s`, `(G.edgesIn ↑s).ncard + ℓ ≤ k * #s`. Phrased additively
  to avoid `ℕ`-subtraction.
* `SimpleGraph.IsTight G k ℓ` — sparse and `(G.edgeSet).ncard + ℓ = k * Nat.card V`.
* `SimpleGraph.IsTightOn G k ℓ s` — `s : Finset V` is a tight subset:
  `(G.edgesIn ↑s).ncard + ℓ = k * s.card`. The localised version of `IsTight`.

## Main lemmas

* `SimpleGraph.bot_isSparse` — the empty graph is sparse for every `(k, ℓ)`.
* `SimpleGraph.IsSparse.mono_left` — sparsity is preserved under subgraph
  inclusion.
* `SimpleGraph.bot_isTight_iff` — characterisation of when the empty graph is tight.
* `SimpleGraph.IsSparse.edgeSet_ncard_add_le` — global edge count bound.
* `SimpleGraph.IsSparse.exists_one_le_degree_le_three` — strengthening for sparse graphs
  with at least one edge: some vertex has degree in `{1, 2, 3}`.
* `SimpleGraph.IsSparse.exists_degree_le_three` — every `(2, 3)`-sparse graph on
  `n ≥ 2` vertices has a vertex of degree at most 3.
* `SimpleGraph.IsSparse.exists_nonadj_among_three_neighbors` — in a `(2, 3)`-sparse
  graph, three pairwise distinct neighbors of any vertex contain a non-adjacent pair.
* `SimpleGraph.IsSparse.deleteEdges` — sparsity preserved under edge deletion.
* `SimpleGraph.IsTight.not_isSparse_of_lt` — proper supergraph of a tight graph is not sparse.
* `SimpleGraph.IsSparse.iso`, `SimpleGraph.IsTight.iso` — sparsity and tightness are
  preserved under graph isomorphism.
* `SimpleGraph.IsSparse.isTightOn_of_le` — in a `(k, ℓ)`-sparse graph, a Finset whose
  edge count meets the sparsity bound from below is exactly tight. The "squeeze" used by
  the Phase 5 typeII-reverse blocker to extract a tight set from a sparsity violation
  on a candidate graph.
* `SimpleGraph.IsTightOn.union_inter` — tight subsets are closed under union and
  intersection in a `(k, ℓ)`-sparse graph (subject to the standard `ℓ ≤ k * #(s ∩ t)`
  size proviso). The tight-set lattice closure that the Phase 5 Henneberg-blocker
  argument runs on.
* `SimpleGraph.IsTightOn.union_inter_of_pair` — matroidal-regime specialization
  (`ℓ < 2 * k`): two tight sets sharing a pair of distinct vertices have tight union
  and intersection. The size proviso of `IsTightOn.union_inter` is auto-discharged.
* `SimpleGraph.IsSparse.exists_isTightOn_of_insert_not_sparse` — violation extraction:
  if `fromEdgeSet I` is `(k, ℓ)`-sparse but inserting an off-diagonal edge `s(u, v) ∉ I`
  breaks sparsity, then some Finset containing `u` and `v` is `(fromEdgeSet I)`-tight.
  Builds the "I-block" that anchors the `(k, ℓ)`-count matroid augmentation argument
  (Phase 7).
* `SimpleGraph.maxBlock`, `SimpleGraph.IsSparse.maxBlock_isTightOn`,
  `SimpleGraph.IsSparse.maxBlock_eq_of_subset_maxBlock` — matroidal-regime maximal
  `I`-block (a.k.a. *I-component*) anchored at a Finset; the union-closure of all
  `I`-tight Finsets containing an anchor `X` with `|X| ≥ 2` is itself `I`-tight, and
  distinct `I`-components are edge-disjoint.
* `SimpleGraph.IsSparse.exists_aug_of_lt_two_mul` — the `(k, ℓ)`-count matroid
  augmentation axiom in the matroidal regime `ℓ < 2 * k`: for `(k, ℓ)`-sparse `I, J`
  with `|I| < |J|`, some `e ∈ J \ I` extends `I` to a `(k, ℓ)`-sparse edge set.
  Proved by I-component decomposition (Whiteley 1996, Lee–Streinu 2008).
* `SimpleGraph.image_edgesIn_comap` — `Sym2.map`-image of `(G.comap f).edgesIn s'` is
  `G.edgesIn (f '' s')`; the comap analogue of `Iso.image_edgesIn`, used by the typeII-
  reverse blocker to pump edge counts back along the subtype embedding.
* `SimpleGraph.IsSparse.typeII_reverse_blocker` — per-pair tight-blocker witness for the
  typeII Henneberg reverse, sparse form: a sparsity violation on the candidate graph
  `(G ↾ {v}ᶜ) ⊔ {bridge(x, y)}` extracts a tight set in `G` containing both `x` and `y`.
  Phase 5 originally shipped a Laman wrapper (`IsLaman.typeII_reverse_blocker`) routing
  the edge count through the typeII iso; Phase 7 lifted the core to `IsSparse` and the
  Laman wrapper was deleted in favor of the flat-form
  `IsLaman.exists_typeI_or_typeII_reverse` consuming `IsSparse.typeII_reverse_blocker`
  directly.

## Implementation notes

`IsSparse`, `IsTight`, and `IsTightOn` are non-reducible `def`s, so `grind`
will not unfold them. To break a goal involving `IsTight` into its sparse and
edge-count components, use `refine ⟨?_, ?_⟩` (or pattern-match `⟨h1, h2⟩`);
to surface the underlying equation of an `IsTightOn`, use `unfold IsTightOn`
(it is a one-equation `def`, not an And). See `TACTICS.md` § 4 for related
guidance.

## Project context

See `ROADMAP.md` for the project plan and `notes/Phase1.md` for the
Phase 1 work log (this file's content is Phase 1).
-/

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- A simple graph `G` is `(k, ℓ)`-sparse if every finite set `s` of vertices spans at most
`k * #s − ℓ` edges. The hypothesis `ℓ ≤ k * #s` keeps the bound nonnegative; the conclusion is
phrased additively to avoid `ℕ`-subtraction. -/
def IsSparse (k ℓ : ℕ) : Prop :=
  ∀ s : Finset V, ℓ ≤ k * s.card → (G.edgesIn ↑s).ncard + ℓ ≤ k * s.card

/-- A simple graph `G` is `(k, ℓ)`-tight if it is `(k, ℓ)`-sparse and its total edge count is
exactly `k * #V − ℓ`. -/
def IsTight (k ℓ : ℕ) : Prop :=
  G.IsSparse k ℓ ∧ G.edgeSet.ncard + ℓ = k * Nat.card V

/-- A finite vertex set `s` is `(k, ℓ)`-**tight in** `G` if it spans exactly `k * #s − ℓ`
edges. Subset-tight sets form a lattice in any `(k, ℓ)`-sparse graph subject to the standard
`ℓ ≤ k * #(s ∩ t)` size proviso; see `IsTightOn.union_inter`. -/
def IsTightOn (k ℓ : ℕ) (s : Finset V) : Prop :=
  (G.edgesIn (↑s : Set V)).ncard + ℓ = k * s.card

variable {G}

/-- The empty graph is `(k, ℓ)`-sparse for any parameters. -/
theorem bot_isSparse (k ℓ : ℕ) : (⊥ : SimpleGraph V).IsSparse k ℓ := by
  intro s hs
  simpa using hs

/-- A subgraph of a `(k, ℓ)`-sparse graph is itself `(k, ℓ)`-sparse. -/
theorem IsSparse.mono_left {G G' : SimpleGraph V} (h : G ≤ G') {k ℓ : ℕ}
    (hG' : G'.IsSparse k ℓ) : G.IsSparse k ℓ := by
  intro s hs
  refine (Nat.add_le_add_right ?_ ℓ).trans (hG' s hs)
  refine Set.ncard_le_ncard ?_ (G'.edgesIn_finite s)
  exact fun _ ⟨he₁, he₂⟩ ↦ ⟨edgeSet_subset_edgeSet.mpr h he₁, he₂⟩

theorem IsTight.isSparse {G : SimpleGraph V} {k ℓ : ℕ} (h : G.IsTight k ℓ) :
    G.IsSparse k ℓ := h.1

theorem IsTight.edgeSet_ncard {G : SimpleGraph V} {k ℓ : ℕ} (h : G.IsTight k ℓ) :
    G.edgeSet.ncard + ℓ = k * Nat.card V := h.2

/-- The empty graph is `(k, ℓ)`-tight precisely when `ℓ = k * #V`. -/
@[simp] theorem bot_isTight_iff (k ℓ : ℕ) :
    (⊥ : SimpleGraph V).IsTight k ℓ ↔ ℓ = k * Nat.card V := by
  refine ⟨fun ⟨_, h⟩ ↦ by simpa using h, fun h ↦ ⟨bot_isSparse k ℓ, by simpa using h⟩⟩

/-! ### The global edge bound and consequences -/

/-- The global edge count of a `(k, ℓ)`-sparse graph is bounded by `k * #V − ℓ`,
provided `ℓ ≤ k * #V`. This is sparsity applied at `s = univ`. -/
theorem IsSparse.edgeSet_ncard_add_le [Finite V] {G : SimpleGraph V} {k ℓ : ℕ}
    (h : G.IsSparse k ℓ) (hV : ℓ ≤ k * Nat.card V) :
    G.edgeSet.ncard + ℓ ≤ k * Nat.card V := by
  have : Fintype V := Fintype.ofFinite V
  have := h Finset.univ
  grind only [= Finset.card_univ, Nat.card_eq_fintype_card, !Finset.coe_univ, edgesIn_univ]

/-- Deleting edges from a `(k, ℓ)`-sparse graph yields a `(k, ℓ)`-sparse graph. -/
theorem IsSparse.deleteEdges {G : SimpleGraph V} {k ℓ : ℕ}
    (h : G.IsSparse k ℓ) (s : Set (Sym2 V)) : (G.deleteEdges s).IsSparse k ℓ :=
  h.mono_left (G.deleteEdges_le s)

/-! ### Low-degree vertex in `(2, 3)`-sparse graphs

A `(2, 3)`-sparse graph on `n ≥ 2` vertices has `#E ≤ 2n − 3`, so by handshake the
average degree is `< 4` and some vertex has degree at most 3. Both the Phase 5 Henneberg
induction on Laman graphs (`IsLaman.exists_two_le_degree_le_three`) and the Phase 7
sparse-graph reverse decomposition (Jordán Lemma 2.1.4) depend on this. -/

/-- In a `(2, 3)`-sparse graph on `n ≥ 2` vertices, some vertex has degree at most 3.
The handshake identity gives `∑ deg = 2 #E ≤ 4n − 6`, so the average is `< 4` and some
vertex has degree `≤ 3`. -/
theorem IsSparse.exists_degree_le_three [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (h : G.IsSparse 2 3)
    (hV : 2 ≤ Fintype.card V) :
    ∃ v, G.degree v ≤ 3 := by
  by_contra hcontra
  push Not at hcontra
  -- Sum of degrees ≥ 4n; handshake + sparsity gives sum ≤ 4n - 6 < 4n.
  have h4n : ∑ _ : V, (4 : ℕ) ≤ ∑ v, G.degree v :=
    Finset.sum_le_sum (fun v _ => by have := hcontra v; omega)
  simp at h4n
  have hsum := G.sum_degrees_eq_twice_card_edges
  have hEcoe := G.ncard_edgeSet_eq_card_edgeFinset
  have hE := h.edgeSet_ncard_add_le (by rw [Nat.card_eq_fintype_card]; omega)
  grind only [Nat.card_eq_fintype_card]

/-- In a `(2, 3)`-sparse graph with at least one edge, some vertex has degree in `{1, 2, 3}`.
Strengthens `exists_degree_le_three` by ruling out the isolated case (`G.degree v = 0`):
restricting the handshake / sparsity bound to `S := {v | 1 ≤ G.degree v}` gives
`∑_{v ∈ S} G.degree v = ∑_v G.degree v = 2 |E|`, all edges sit inside `edgesIn ↑S`, and
sparsity at `S` (size ≥ 2 from any edge) gives `|E| + 3 ≤ 2 |S|`. If every vertex in `S`
had degree ≥ 4 the sum would be `≥ 4 |S|`, contradicting `2 |E| ≤ 4 |S| − 6`. The
positive-degree restriction is what the Phase 7 3-way sparse reverse decomposition needs
to distinguish pendant (`deg = 1`) from Type I proper (`deg = 2`). -/
theorem IsSparse.exists_one_le_degree_le_three [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (h : G.IsSparse 2 3)
    (hE : G.edgeSet.Nonempty) :
    ∃ v, 1 ≤ G.degree v ∧ G.degree v ≤ 3 := by
  classical
  by_contra hcontra
  push Not at hcontra
  -- `S`: positive-degree vertices. By `hcontra`, every `v ∈ S` has `G.degree v ≥ 4`.
  set S : Finset V := Finset.univ.filter (fun v => 1 ≤ G.degree v) with hS_def
  -- An edge gives two distinct positive-degree vertices, hence `|S| ≥ 2`.
  obtain ⟨e, he⟩ := hE
  induction e with | h u v => ?_
  rw [mem_edgeSet] at he
  have huv : u ≠ v := G.ne_of_adj he
  have hdu : 1 ≤ G.degree u := (G.degree_pos_iff_exists_adj u).mpr ⟨v, he⟩
  have hdv : 1 ≤ G.degree v := (G.degree_pos_iff_exists_adj v).mpr ⟨u, he.symm⟩
  have hu_in : u ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdu⟩
  have hv_in : v ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdv⟩
  have hS_ge2 : 2 ≤ S.card := by
    rw [show (2 : ℕ) = ({u, v} : Finset V).card from (Finset.card_pair huv).symm]
    refine Finset.card_le_card ?_
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  -- Every edge has both endpoints in `S`, so `edgesIn ↑S = edgeSet`.
  have h_edgesIn : G.edgesIn (↑S : Set V) = G.edgeSet := by
    refine Set.eq_of_subset_of_subset (fun _ he => he.1) (fun e he => mem_edgesIn.mpr ⟨he, ?_⟩)
    induction e with | h x y => ?_
    rw [mem_edgeSet] at he
    rw [Sym2.coe_mk]
    rintro w (rfl | rfl)
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (G.degree_pos_iff_exists_adj _).mpr ⟨_, he⟩⟩)
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (G.degree_pos_iff_exists_adj _).mpr ⟨_, he.symm⟩⟩)
  -- Sum-of-degrees ≥ 4 |S| from the by-contradiction hypothesis.
  have h_deg_4 : ∀ w ∈ S, 4 ≤ G.degree w := fun w hw => by
    have h1 := (Finset.mem_filter.mp hw).2
    have := hcontra w h1; omega
  have h_sum_4 : (∑ _ ∈ S, (4 : ℕ)) ≤ ∑ w ∈ S, G.degree w :=
    Finset.sum_le_sum h_deg_4
  simp at h_sum_4
  -- Restriction is harmless: vertices outside `S` have degree 0.
  have h_sum_eq : ∑ w ∈ S, G.degree w = ∑ w, G.degree w := by
    rw [hS_def]; exact Finset.sum_filter_of_ne fun w _ hw => by omega
  have hsum := G.sum_degrees_eq_twice_card_edges
  have hEcoe := G.ncard_edgeSet_eq_card_edgeFinset
  have h_sparse_S := h S (by omega)
  rw [h_edgesIn] at h_sparse_S
  omega

/-! ### Non-adjacent pair among three neighbors

In a `(2, 3)`-sparse graph, any three neighbors of a single vertex contain a non-adjacent
pair. This is the combinatorial input for the Type II Henneberg reverse move: given a
degree-3 vertex with neighbors `a, b, c`, we use this lemma to pick the two non-adjacent
ones to bridge with a fresh edge. Both `IsLaman.exists_typeI_or_typeII_reverse`
(Phase 5 milestone 1) and `IsSparse.exists_typeI_or_typeII_reverse` (Phase 7) depend on
this; the proof uses sparsity, not tightness. -/

/-- In a `(2, 3)`-sparse graph, three pairwise distinct neighbors of any vertex contain
a non-adjacent pair. Apply sparsity to the 4-set `{v, a, b, c}` (size 4, so at most
`2·4 − 3 = 5` edges); the three edges `v-a`, `v-b`, `v-c` are present, so among
`{a, b, c}` there are at most 2 edges, hence at least one of the three possible pairs is
missing. -/
theorem IsSparse.exists_nonadj_among_three_neighbors [Finite V]
    {G : SimpleGraph V} (h : G.IsSparse 2 3) {v a b c : V}
    (ha : G.Adj v a) (hb : G.Adj v b) (hc : G.Adj v c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ G.Adj a b ∨ ¬ G.Adj a c ∨ ¬ G.Adj b c := by
  classical
  have : Fintype V := Fintype.ofFinite V
  by_contra hall
  push Not at hall
  obtain ⟨hab_e, hac_e, hbc_e⟩ := hall
  have hva : v ≠ a := G.ne_of_adj ha
  have hvb : v ≠ b := G.ne_of_adj hb
  have hvc : v ≠ c := G.ne_of_adj hc
  -- The 4-set `{v, a, b, c}` has cardinality 4.
  have hs_card : ({v, a, b, c} : Finset V).card = 4 := by
    grind [Finset.card_insert_of_notMem, Finset.card_singleton]
  -- The 6 candidate edges form a 6-element Finset, all contained in `G.edgesIn ↑{v,a,b,c}`.
  set E : Finset (Sym2 V) :=
    {s(v, a), s(v, b), s(v, c), s(a, b), s(a, c), s(b, c)} with hE_def
  have hE_card : E.card = 6 := by
    rw [hE_def]
    grind [Finset.card_insert_of_notMem, Finset.card_singleton, Sym2.eq_iff]
  have hE_sub : (↑E : Set (Sym2 V)) ⊆ G.edgesIn (↑({v, a, b, c} : Finset V) : Set V) := by
    intro e he
    simp only [hE_def, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
               Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact mem_edgesIn.mpr ⟨by rwa [mem_edgeSet],
        by rw [Sym2.coe_mk]; rintro _ (rfl | rfl) <;> simp⟩
  have hsparse := h {v, a, b, c} (by omega)
  have h6_le : 6 ≤ (G.edgesIn (↑({v, a, b, c} : Finset V) : Set V)).ncard := by
    rw [← hE_card, ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hE_sub
  omega

/-- A proper supergraph of a `(k, ℓ)`-tight graph cannot be `(k, ℓ)`-sparse: the global edge bound
is already saturated, so any extra edge violates it. -/
theorem IsTight.not_isSparse_of_lt [Finite V] {G H : SimpleGraph V} {k ℓ : ℕ}
    (hG : G.IsTight k ℓ) (h : G < H) : ¬ H.IsSparse k ℓ := fun hH => by
  have := hG.edgeSet_ncard
  have := hH.edgeSet_ncard_add_le (by grind only)
  have := Set.ncard_lt_ncard (edgeSet_ssubset_edgeSet.mpr h) (Set.toFinite H.edgeSet)
  grind only

/-! ### Transport along graph isomorphism

`IsSparse` and `IsTight` are preserved under graph isomorphism. The transport is mediated by
`Sym2.map φ` between edge sets and by `φ.toEquiv` between vertex types. -/

namespace Iso

variable {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Under a graph iso, the `Sym2.map`-image of `G.edgesIn s` is `H.edgesIn (φ '' s)`. The
`edgesIn` analogue of `Iso.image_neighborSet`. -/
lemma image_edgesIn (φ : G ≃g H) (s : Set V) :
    Sym2.map φ '' G.edgesIn s = H.edgesIn (φ '' s) := by
  ext e
  induction e with | h u v => ?_
  simp only [Sym2.mk_mem_image_map_iff, mem_edgesIn, mem_edgeSet, Sym2.coe_mk]
  constructor
  · rintro ⟨p, q, rfl, rfl, h_adj, hsub⟩
    refine ⟨φ.map_adj_iff.mpr h_adj, ?_⟩
    rintro x (rfl | rfl)
    · exact ⟨p, hsub (Or.inl rfl), rfl⟩
    · exact ⟨q, hsub (Or.inr rfl), rfl⟩
  · rintro ⟨h_adj, hsub⟩
    obtain ⟨p, hp, rfl⟩ := hsub (Or.inl rfl)
    obtain ⟨q, hq, rfl⟩ := hsub (Or.inr rfl)
    exact ⟨p, q, rfl, rfl, φ.map_adj_iff.mp h_adj,
      fun x hx => by rcases hx with rfl | rfl <;> assumption⟩

end Iso

/-- Under graph comap, the `Sym2.map`-image of `(G.comap f).edgesIn s'` is `G.edgesIn (f '' s')`.
The image-form equality holds without an injectivity hypothesis on `f`; injectivity lifts to the
ncard equality used downstream (via `Set.ncard_image_of_injective` on `Sym2.map f`). The
non-iso analogue of `Iso.image_edgesIn`; the Phase 5 / Phase 7 typeII-reverse blocker pumps the
candidate graph's edge count back through `G` along the subtype embedding via this lemma. -/
lemma image_edgesIn_comap (G : SimpleGraph V) {V' : Type*} (f : V' → V) (s' : Set V') :
    Sym2.map f '' ((G.comap f).edgesIn s') = G.edgesIn (f '' s') := by
  ext e
  refine e.ind fun p q => ?_
  rw [Sym2.mk_mem_image_map_iff]
  simp only [mem_edgesIn, mem_edgeSet, comap_adj, Sym2.coe_mk, Set.insert_subset_iff,
             Set.singleton_subset_iff, Set.mem_image]
  constructor
  · rintro ⟨u, w, rfl, rfl, hadj, hu, hw⟩
    exact ⟨hadj, ⟨u, hu, rfl⟩, ⟨w, hw, rfl⟩⟩
  · rintro ⟨hadj, ⟨u, hu, rfl⟩, ⟨w, hw, rfl⟩⟩
    exact ⟨u, w, rfl, rfl, hadj, hu, hw⟩

/-- A graph isomorphism preserves `(k, ℓ)`-sparsity. -/
theorem IsSparse.iso {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ≃g H) {k ℓ : ℕ} (h : G.IsSparse k ℓ) : H.IsSparse k ℓ := by
  classical
  intro s hs
  set s' : Finset V := s.image φ.symm
  have hs'_card : s'.card = s.card :=
    Finset.card_image_of_injective s φ.symm.toEquiv.injective
  have h_eq : (H.edgesIn (↑s : Set W)).ncard = (G.edgesIn (↑s' : Set V)).ncard := by
    rw [show (↑s' : Set V) = φ.symm '' ↑s from Finset.coe_image, ← Iso.image_edgesIn φ.symm,
      Set.ncard_image_of_injective _ (Sym2.map.injective φ.symm.injective)]
  rw [h_eq, ← hs'_card]
  exact h s' (hs'_card ▸ hs)

/-- A graph isomorphism preserves `(k, ℓ)`-tightness. -/
theorem IsTight.iso {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ≃g H) {k ℓ : ℕ} (h : G.IsTight k ℓ) : H.IsTight k ℓ := by
  refine ⟨h.1.iso φ, ?_⟩
  have hE : H.edgeSet.ncard = G.edgeSet.ncard := by
    simp only [← Nat.card_coe_set_eq]
    exact Nat.card_congr φ.mapEdgeSet.symm
  have hV : Nat.card W = Nat.card V := Nat.card_congr φ.toEquiv.symm
  grind only [h.2]

/-- The comap of a `(k, ℓ)`-sparse graph along an injective vertex map is `(k, ℓ)`-sparse.
The proof transports a candidate Finset on the source side to its `f`-image on the target,
and reads off `(G.comap f)`'s edge count via `image_edgesIn_comap`. The directional analogue
of `IsSparse.iso`; specialized to `Subtype.val : {w // w ≠ v} → V` by the Phase 7 sparse-graph
reverse decomposition. -/
theorem IsSparse.comap {V' : Type*} {G : SimpleGraph V} {k ℓ : ℕ} (h : G.IsSparse k ℓ)
    {f : V' → V} (hf : Function.Injective f) : (G.comap f).IsSparse k ℓ := by
  classical
  intro s' hs'
  set S : Finset V := s'.image f with hS_def
  have hS_card : S.card = s'.card := Finset.card_image_of_injective s' hf
  have h_link : ((G.comap f).edgesIn (↑s' : Set V')).ncard = (G.edgesIn (↑S : Set V)).ncard := by
    rw [hS_def, Finset.coe_image, ← image_edgesIn_comap,
        Set.ncard_image_of_injective _ (Sym2.map.injective hf)]
  rw [h_link, ← hS_card]
  exact h S (hS_card ▸ hs')

/-- **Squeeze: lower bound forces tight.** In a `(k, ℓ)`-sparse graph, if a Finset `s`
attains the sparsity upper bound from below, it must be exactly `(k, ℓ)`-tight. Used by
the Phase 5 typeII-reverse blocker to convert a sparsity violation on a candidate graph
into a tight set in `G`. -/
theorem IsSparse.isTightOn_of_le {G : SimpleGraph V} {k ℓ : ℕ}
    (hG : G.IsSparse k ℓ) {s : Finset V} (hs : ℓ ≤ k * s.card)
    (h_le : k * s.card ≤ (G.edgesIn ↑s).ncard + ℓ) :
    G.IsTightOn k ℓ s := by
  grind only [IsTightOn, hG s hs]

/-! ### The tight-subset lattice

In a `(k, ℓ)`-sparse graph, the tight subsets are closed under union and intersection
(subject to a standard size proviso on the intersection). The squeeze is between two
inequalities: supermodularity of edge counts (`edgesIn_ncard_add_le`) lower-bounds the
edge sum on `s ∪ t` and `s ∩ t` by the same sum on `s` and `t`, while sparsity
upper-bounds it by the cardinality target. The bridging identity is the standard
Finset-cardinality fact `s.card + t.card = (s ∪ t).card + (s ∩ t).card`. -/

/-- **Tight subsets are closed under union and intersection.** In a `(k, ℓ)`-sparse graph,
if `s, t : Finset V` are both `(k, ℓ)`-tight subsets and the intersection is large enough
that sparsity applies there (`ℓ ≤ k * #(s ∩ t)`), then so are `s ∪ t` and `s ∩ t`. The
edge-arithmetic input is `edgesIn_ncard_add_le` (supermodularity); the cardinality input
is `Finset.card_union_add_card_inter`. -/
theorem IsTightOn.union_inter [Finite V] [DecidableEq V] {G : SimpleGraph V} {k ℓ : ℕ}
    {s t : Finset V} (hs : G.IsTightOn k ℓ s) (ht : G.IsTightOn k ℓ t)
    (hG : G.IsSparse k ℓ) (h_inter : ℓ ≤ k * (s ∩ t).card) :
    G.IsTightOn k ℓ (s ∪ t) ∧ G.IsTightOn k ℓ (s ∩ t) := by
  have h_super := G.edgesIn_ncard_add_le (↑s : Set V) (↑t : Set V)
  rw [← Finset.coe_union, ← Finset.coe_inter] at h_super
  have h_sparse_inter := hG (s ∩ t) h_inter
  have h_sparse_union := hG (s ∪ t)
    (h_inter.trans (Nat.mul_le_mul_left k (Finset.card_le_card Finset.inter_subset_union)))
  have h_card_mul : k * s.card + k * t.card = k * (s ∪ t).card + k * (s ∩ t).card := by
    rw [← Nat.mul_add, ← Nat.mul_add, Finset.card_union_add_card_inter]
  unfold IsTightOn at hs ht ⊢
  refine ⟨?_, ?_⟩ <;> omega

/-- **Tight union with bonus edges.** Generalizes `IsTightOn.union_inter`'s union half: instead of
requiring `ℓ ≤ k * #(s ∩ t)` to extract sparsity at the intersection, allow the user to supply a
finite set `F` of "bonus" edges in `edgesIn (S₁ ∪ S₂)` disjoint from `edgesIn S₁ ∪ edgesIn S₂` and
ask only that `F` plus the intersection accounting close the gap, i.e.
`|F| + k * #(S₁ ∩ S₂) ≥ |edgesIn (S₁ ∩ S₂)| + ℓ`. Specializes to
`IsTightOn.union_inter`'s union conclusion at `F = ∅` (the size proviso then provides the
close-the-gap inequality via sparsity at `S₁ ∩ S₂`). -/
theorem IsTightOn.union_with_bonus [Finite V] [DecidableEq V] {G : SimpleGraph V} {k ℓ : ℕ}
    {S₁ S₂ : Finset V} (h₁ : G.IsTightOn k ℓ S₁) (h₂ : G.IsTightOn k ℓ S₂)
    (hG : G.IsSparse k ℓ) {F : Set (Sym2 V)}
    (hF_sub : F ⊆ G.edgesIn (↑(S₁ ∪ S₂) : Set V))
    (hF_disj : Disjoint F (G.edgesIn (↑S₁ : Set V) ∪ G.edgesIn (↑S₂ : Set V)))
    (hF_finite : F.Finite)
    (h_close : (G.edgesIn (↑(S₁ ∩ S₂) : Set V)).ncard + ℓ ≤
               F.ncard + k * (S₁ ∩ S₂).card) :
    G.IsTightOn k ℓ (S₁ ∪ S₂) := by
  -- Step 1: refined supermodular bound. The bonus edges enlarge the union side by `|F|`.
  have h_un_sub :
      G.edgesIn (↑S₁ : Set V) ∪ G.edgesIn (↑S₂ : Set V) ⊆ G.edgesIn (↑(S₁ ∪ S₂) : Set V) := by
    rw [Finset.coe_union]
    exact Set.union_subset (edgesIn_mono Set.subset_union_left)
                           (edgesIn_mono Set.subset_union_right)
  have h_combined_sub :
      G.edgesIn (↑S₁ : Set V) ∪ G.edgesIn (↑S₂ : Set V) ∪ F ⊆ G.edgesIn (↑(S₁ ∪ S₂) : Set V) :=
    Set.union_subset h_un_sub hF_sub
  have h_inter_eq : G.edgesIn (↑S₁ : Set V) ∩ G.edgesIn (↑S₂ : Set V) =
                    G.edgesIn (↑(S₁ ∩ S₂) : Set V) := by
    rw [Finset.coe_inter]; exact (edgesIn_inter _ _).symm
  have h_un_card :
      (G.edgesIn (↑S₁ : Set V) ∪ G.edgesIn (↑S₂ : Set V)).ncard +
        (G.edgesIn (↑(S₁ ∩ S₂) : Set V)).ncard =
        (G.edgesIn (↑S₁ : Set V)).ncard + (G.edgesIn (↑S₂ : Set V)).ncard := by
    rw [← h_inter_eq]; exact Set.ncard_union_add_ncard_inter _ _
  have h_combined_card :
      (G.edgesIn (↑S₁ : Set V) ∪ G.edgesIn (↑S₂ : Set V) ∪ F).ncard =
        (G.edgesIn (↑S₁ : Set V) ∪ G.edgesIn (↑S₂ : Set V)).ncard + F.ncard :=
    Set.ncard_union_eq hF_disj.symm
      ((G.edgesIn_finite S₁).union (G.edgesIn_finite S₂)) hF_finite
  have h_le_union :=
    Set.ncard_le_ncard h_combined_sub (G.edgesIn_finite (S₁ ∪ S₂))
  -- Step 2: cardinality identity for the union/intersection split.
  have h_card_mul : k * S₁.card + k * S₂.card = k * (S₁ ∪ S₂).card + k * (S₁ ∩ S₂).card := by
    rw [← Nat.mul_add, ← Nat.mul_add, Finset.card_union_add_card_inter]
  -- Step 3: squeeze to tightness via `IsSparse.isTightOn_of_le`.
  have h_S1_size : ℓ ≤ k * S₁.card := by unfold IsTightOn at h₁; omega
  have h_union_size : ℓ ≤ k * (S₁ ∪ S₂).card :=
    h_S1_size.trans (Nat.mul_le_mul_left k (Finset.card_le_card Finset.subset_union_left))
  refine hG.isTightOn_of_le h_union_size ?_
  grind only [IsTightOn]

/-- **Tight extension by a vertex with `k` boundary edges.** If `S` is `(k, ℓ)`-tight and a fresh
vertex `w ∉ S` can be added with at least `k` "new" edges `F ⊆ edgesIn (insert w S)` disjoint from
`edgesIn S`, then `insert w S` is itself `(k, ℓ)`-tight. The `|F| ≥ k` hypothesis is exactly the
edge-count needed to absorb the extra vertex while staying on the sparsity locus. -/
theorem IsTightOn.insert_vertex_with_edges [Finite V] [DecidableEq V] {G : SimpleGraph V}
    {k ℓ : ℕ} {S : Finset V} (h : G.IsTightOn k ℓ S) (hG : G.IsSparse k ℓ)
    {w : V} (hw : w ∉ S) {F : Set (Sym2 V)}
    (hF_sub : F ⊆ G.edgesIn (↑(insert w S) : Set V))
    (hF_disj : Disjoint F (G.edgesIn (↑S : Set V)))
    (hF_finite : F.Finite) (h_card : k ≤ F.ncard) :
    G.IsTightOn k ℓ (insert w S) := by
  have h_S_sub : G.edgesIn (↑S : Set V) ⊆ G.edgesIn (↑(insert w S) : Set V) := by
    refine edgesIn_mono ?_; rw [Finset.coe_insert]; exact Set.subset_insert _ _
  have h_combined_sub :
      G.edgesIn (↑S : Set V) ∪ F ⊆ G.edgesIn (↑(insert w S) : Set V) :=
    Set.union_subset h_S_sub hF_sub
  have h_combined_card :
      (G.edgesIn (↑S : Set V) ∪ F).ncard = (G.edgesIn (↑S : Set V)).ncard + F.ncard :=
    Set.ncard_union_eq hF_disj.symm (G.edgesIn_finite S) hF_finite
  have h_le := Set.ncard_le_ncard h_combined_sub (G.edgesIn_finite (insert w S))
  have h_card_insert : (insert w S).card = S.card + 1 := Finset.card_insert_of_notMem hw
  have h_size : ℓ ≤ k * (insert w S).card := by
    unfold IsTightOn at h
    rw [h_card_insert, Nat.mul_add, Nat.mul_one]; omega
  refine hG.isTightOn_of_le h_size ?_
  rw [h_card_insert, Nat.mul_add, Nat.mul_one] at h_size ⊢
  grind only [IsTightOn]

/-! ### Matroidal-regime block closure (`ℓ < 2 * k`)

In the matroidal regime `ℓ < 2 * k`, the size proviso `ℓ ≤ k * #(s ∩ t)` of
`IsTightOn.union_inter` is automatically discharged for two tight sets sharing a common pair
of distinct vertices: `#(s ∩ t) ≥ 2 ≥ ⌈ℓ/k⌉` for any `ℓ < 2k`. This is the combinatorial
foundation of the `(k, ℓ)`-count matroid (Whiteley 1996, Lee–Streinu 2008): blocks of an
edge set `I` containing a fixed pair `{u, v}` are closed under intersection and union,
so the family has a unique maximum element — the *I-component* of `{u, v}` —
that drives the augmentation argument of Phase 7. -/

/-- **Block closure under a shared pair (matroidal regime).** For `ℓ < 2 * k` and two
`(k, ℓ)`-tight finite sets `s, t` both containing distinct vertices `u ≠ v`, both `s ∪ t` and
`s ∩ t` are `(k, ℓ)`-tight. Specialization of `IsTightOn.union_inter` whose size proviso
`ℓ ≤ k * #(s ∩ t)` is auto-discharged via `#(s ∩ t) ≥ #{u, v} = 2` and `ℓ < 2k = k * 2`. -/
theorem IsTightOn.union_inter_of_pair [Finite V] [DecidableEq V] {G : SimpleGraph V}
    {k ℓ : ℕ} (hℓ : ℓ < 2 * k) {s t : Finset V}
    (hs : G.IsTightOn k ℓ s) (ht : G.IsTightOn k ℓ t) (hG : G.IsSparse k ℓ)
    {u v : V} (huv : u ≠ v)
    (hu_s : u ∈ s) (hv_s : v ∈ s) (hu_t : u ∈ t) (hv_t : v ∈ t) :
    G.IsTightOn k ℓ (s ∪ t) ∧ G.IsTightOn k ℓ (s ∩ t) := by
  refine hs.union_inter ht hG ?_
  have h_uv_sub : ({u, v} : Finset V) ⊆ s ∩ t := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨hu_s, hu_t⟩
    · exact Finset.mem_inter.mpr ⟨hv_s, hv_t⟩
  have h_card : 2 ≤ (s ∩ t).card :=
    (Finset.card_pair huv).symm ▸ Finset.card_le_card h_uv_sub
  calc ℓ ≤ 2 * k := hℓ.le
       _ = k * 2 := Nat.mul_comm 2 k
       _ ≤ k * (s ∩ t).card := Nat.mul_le_mul_left k h_card

/-- **Add-an-edge identity for `fromEdgeSet.edgeSet`.** Adding an off-diagonal edge `s(u, v)`
to an edge set `I` inserts exactly the singleton `{s(u, v)}` into the resulting `edgeSet`
of `fromEdgeSet`. The `fromEdgeSet` constructor drops diagonals; the `u ≠ v` hypothesis keeps
`s(u, v)` off the diagonal. -/
lemma edgeSet_fromEdgeSet_insert {I : Set (Sym2 V)} {u v : V} (huv : u ≠ v) :
    (fromEdgeSet (insert s(u, v) I)).edgeSet = insert s(u, v) (fromEdgeSet I).edgeSet := by
  rw [edgeSet_fromEdgeSet, edgeSet_fromEdgeSet,
      Set.insert_diff_of_notMem _ (Sym2.mem_diagSet.not.mpr (Sym2.mk_isDiag_iff.not.mpr huv))]

/-- **I-block extraction from a sparsity violation (matroidal building block).** If
`fromEdgeSet I` is `(k, ℓ)`-sparse but adding a single off-diagonal edge `s(u, v) ∉ I`
breaks sparsity, then there is a `(fromEdgeSet I)`-tight Finset containing both `u` and `v`
— the "I-block" that the `(k, ℓ)`-count matroid augmentation argument anchors on. -/
theorem IsSparse.exists_isTightOn_of_insert_not_sparse [Finite V]
    {k ℓ : ℕ} {I : Set (Sym2 V)} (hI : (fromEdgeSet I).IsSparse k ℓ)
    {u v : V} (huv : u ≠ v) (he_notin : s(u, v) ∉ I)
    (h_violation : ¬ (fromEdgeSet (insert s(u, v) I)).IsSparse k ℓ) :
    ∃ S : Finset V, u ∈ S ∧ v ∈ S ∧ (fromEdgeSet I).IsTightOn k ℓ S := by
  unfold IsSparse at h_violation
  push Not at h_violation
  obtain ⟨S, h_size, h_lt⟩ := h_violation
  have hI_at_S := hI S h_size
  have h_new_notin_old : s(u, v) ∉ (fromEdgeSet I).edgeSet :=
    fun h => he_notin ((edgeSet_fromEdgeSet I) ▸ h).1
  have h_edgeSet_eq := edgeSet_fromEdgeSet_insert (I := I) huv
  -- Case-split on `{u, v} ⊆ S`. The "⊄" case contradicts `I`-sparsity at `S`; the "⊆"
  -- case extracts the I-block.
  by_cases h_uv : u ∈ S ∧ v ∈ S
  · obtain ⟨hu, hv⟩ := h_uv
    refine ⟨S, hu, hv, ?_⟩
    have h_uv_in_sym2 : s(u, v) ∈ (↑S : Set V).sym2 := by
      rw [Set.mem_sym2_iff_subset, Sym2.coe_mk]
      exact Set.insert_subset_iff.mpr ⟨hu, Set.singleton_subset_iff.mpr hv⟩
    have h_edges_eq : (fromEdgeSet (insert s(u, v) I)).edgesIn (↑S : Set V) =
        insert s(u, v) ((fromEdgeSet I).edgesIn (↑S : Set V)) := by
      unfold edgesIn
      rw [h_edgeSet_eq, Set.insert_inter_of_mem h_uv_in_sym2]
    have h_new_notin_old_edgesIn : s(u, v) ∉ (fromEdgeSet I).edgesIn (↑S : Set V) :=
      fun h => h_new_notin_old h.1
    have h_ncard_eq : ((fromEdgeSet (insert s(u, v) I)).edgesIn (↑S : Set V)).ncard =
        ((fromEdgeSet I).edgesIn (↑S : Set V)).ncard + 1 := by
      rw [h_edges_eq, Set.ncard_insert_of_notMem h_new_notin_old_edgesIn
        ((fromEdgeSet I).edgesIn_finite S)]
    unfold IsTightOn
    omega
  · exfalso
    have h_uv_notin_sym2 : s(u, v) ∉ (↑S : Set V).sym2 := by
      rw [Set.mem_sym2_iff_subset, Sym2.coe_mk]
      exact fun h_sub => h_uv
        ⟨h_sub (Set.mem_insert _ _), h_sub (Set.mem_insert_of_mem _ rfl)⟩
    have h_edges_eq : (fromEdgeSet (insert s(u, v) I)).edgesIn (↑S : Set V) =
        (fromEdgeSet I).edgesIn (↑S : Set V) := by
      unfold edgesIn
      rw [h_edgeSet_eq, Set.insert_inter_of_notMem h_uv_notin_sym2]
    rw [h_edges_eq] at h_lt
    omega

/-! ### Three-neighbor obstruction and contradiction templates

For a vertex `v` with three distinct neighbors `a, b, c` in a `(2, 3)`-sparse graph,
inserting `v` into any tight set `T ⊆ V \ {v}` containing `{a, b, c}` overshoots the
sparsity bound: `IsSparse.no_isTightOn_excluding_three_neighbors`. The three contradiction
templates below each derive `False` from a configuration of one, two, or three tight
blockers covering pairs of `{a, b, c}`; they reduce to the primitive by building a tight
set in `V \ {v}` that contains all three neighbors. The unified dispatcher
`IsSparse.False_of_pairwise_blocker_or_edge` packages all three by case-splitting on the
adj-or-blocker disjunction for each pair.

These primitives drive both Phase 5 milestone 1 (`IsLaman.exists_typeI_or_typeII_reverse`)
and Phase 7's sparse-graph reverse decomposition (Jordán Lemma 2.1.4(b)); both targets sit
in `Henneberg.lean`. -/

/-- **Three-neighbor obstruction.** In a `(2, 3)`-sparse graph, no `(2, 3)`-tight set
`T ⊆ V \ {v}` can contain three distinct neighbors `a, b, c` of `v`: inserting `v` adds
1 vertex but at least 3 edges (the incident edges `s(v, a), s(v, b), s(v, c)`),
overshooting the `(2, 3)`-sparsity bound at `insert v T`. -/
theorem IsSparse.no_isTightOn_excluding_three_neighbors
    {G : SimpleGraph V} (h : G.IsSparse 2 3) {v a b c : V}
    (ha : G.Adj v a) (hb : G.Adj v b) (hc : G.Adj v c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {T : Finset V} (hvT : v ∉ T) (haT : a ∈ T) (hbT : b ∈ T) (hcT : c ∈ T)
    (hT : G.IsTightOn 2 3 T) : False := by
  classical
  have hva : v ≠ a := G.ne_of_adj ha
  have hvb : v ≠ b := G.ne_of_adj hb
  have hvc : v ≠ c := G.ne_of_adj hc
  set T' : Finset V := insert v T with hT'_def
  have hT'_card : T'.card = T.card + 1 := Finset.card_insert_of_notMem hvT
  set E3 : Set (Sym2 V) := {s(v, a), s(v, b), s(v, c)} with hE3_def
  have hne_ab : s(v, a) ≠ s(v, b) := fun h => (Sym2.eq_iff.mp h).elim
    (fun ⟨_, h2⟩ => hab h2) (fun ⟨h1, _⟩ => hvb h1)
  have hne_ac : s(v, a) ≠ s(v, c) := fun h => (Sym2.eq_iff.mp h).elim
    (fun ⟨_, h2⟩ => hac h2) (fun ⟨h1, _⟩ => hvc h1)
  have hne_bc : s(v, b) ≠ s(v, c) := fun h => (Sym2.eq_iff.mp h).elim
    (fun ⟨_, h2⟩ => hbc h2) (fun ⟨h1, _⟩ => hvc h1)
  have hE3_card : E3.ncard = 3 := by
    rw [hE3_def, Set.ncard_insert_of_notMem (by simp [hne_ab, hne_ac]) (Set.toFinite _),
        Set.ncard_pair hne_bc]
  have h_T_sub_T' : (↑T : Set V) ⊆ (↑T' : Set V) := by
    intro x hx
    rw [hT'_def, Finset.coe_insert]
    exact Or.inr hx
  have h_v_in_T' : v ∈ (↑T' : Set V) := by
    rw [hT'_def, Finset.coe_insert]; exact Set.mem_insert _ _
  have h_a_in_T' : a ∈ (↑T' : Set V) := h_T_sub_T' (Finset.mem_coe.mpr haT)
  have h_b_in_T' : b ∈ (↑T' : Set V) := h_T_sub_T' (Finset.mem_coe.mpr hbT)
  have h_c_in_T' : c ∈ (↑T' : Set V) := h_T_sub_T' (Finset.mem_coe.mpr hcT)
  have h_E3_in : E3 ⊆ G.edgesIn (↑T' : Set V) := by
    rintro e (rfl | rfl | rfl)
    · exact G.mk_mem_edgesIn ha h_v_in_T' h_a_in_T'
    · exact G.mk_mem_edgesIn hb h_v_in_T' h_b_in_T'
    · exact G.mk_mem_edgesIn hc h_v_in_T' h_c_in_T'
  have h_disj : Disjoint E3 (G.edgesIn (↑T : Set V)) := by
    rw [Set.disjoint_left]
    rintro e he h_mem
    obtain ⟨_, hsub⟩ := mem_edgesIn.mp h_mem
    have hv_in_e : v ∈ (e : Set V) := by
      rcases he with rfl | rfl | rfl <;> (rw [Sym2.coe_mk]; exact Set.mem_insert _ _)
    exact hvT (Finset.mem_coe.mp (hsub hv_in_e))
  have h_edgesIn_sub : G.edgesIn (↑T : Set V) ⊆ G.edgesIn (↑T' : Set V) :=
    edgesIn_mono h_T_sub_T'
  have h_ncard_ge : (G.edgesIn (↑T : Set V)).ncard + 3 ≤ (G.edgesIn (↑T' : Set V)).ncard :=
    calc (G.edgesIn (↑T : Set V)).ncard + 3
        = (G.edgesIn (↑T : Set V)).ncard + E3.ncard := by rw [hE3_card]
      _ = (G.edgesIn (↑T : Set V) ∪ E3).ncard :=
          (Set.ncard_union_eq h_disj.symm (G.edgesIn_finite T) (Set.toFinite _)).symm
      _ ≤ (G.edgesIn (↑T' : Set V)).ncard :=
          Set.ncard_le_ncard (Set.union_subset h_edgesIn_sub h_E3_in) (G.edgesIn_finite T')
  have hT_card_ge : 3 ≤ T.card :=
    Finset.three_le_card_of_three_distinct_mem hab hac hbc haT hbT hcT
  have hT'_sparse := h T' (by rw [hT'_card]; omega)
  unfold IsTightOn at hT
  omega

/-- **1-pair contradiction template.** A single blocker `S` containing two neighbors
`x, y` of `v`, with the third neighbor `z` connected to both `x` and `y` by edges of `G`:
case-split on `z ∈ S`. If yes, `S` already contains `{x, y, z}` and the primitive closes.
If no, extend to `T := insert z S`; the two edges `s(x, z)` and `s(y, z)` are in
`edgesIn T` but not in `edgesIn S` (since `z ∉ S`), giving `#(edgesIn T) ≥ #(edgesIn S) + 2`,
which combined with tightness of `S` saturates the squeeze at `T`. -/
theorem IsSparse.contradiction_one_pair
    [Finite V] {G : SimpleGraph V} (h : G.IsSparse 2 3) {v x y z : V}
    (hx : G.Adj v x) (hy : G.Adj v y) (hz : G.Adj v z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxz_adj : G.Adj x z) (hyz_adj : G.Adj y z)
    {S : Finset V} (hvS : v ∉ S) (hxS : x ∈ S) (hyS : y ∈ S)
    (hS_tight : G.IsTightOn 2 3 S) : False := by
  classical
  by_cases hzS : z ∈ S
  · exact IsSparse.no_isTightOn_excluding_three_neighbors h hx hy hz hxy hxz hyz
      hvS hxS hyS hzS hS_tight
  · set T : Finset V := insert z S with hT_def
    have hvT : v ∉ T := by
      simp only [hT_def, Finset.mem_insert, not_or]
      exact ⟨G.ne_of_adj hz, hvS⟩
    have hzT : z ∈ T := Finset.mem_insert_self z S
    have hxT : x ∈ T := Finset.mem_insert_of_mem hxS
    have hyT : y ∈ T := Finset.mem_insert_of_mem hyS
    have hxz_in_T : s(x, z) ∈ G.edgesIn (↑T : Set V) := G.mk_mem_edgesIn hxz_adj hxT hzT
    have hyz_in_T : s(y, z) ∈ G.edgesIn (↑T : Set V) := G.mk_mem_edgesIn hyz_adj hyT hzT
    have hxz_ne_yz : s(x, z) ≠ s(y, z) := fun heq =>
      (Sym2.eq_iff.mp heq).elim
        (fun ⟨h1, _⟩ => hxy h1)
        (fun ⟨h1, _⟩ => hxz h1)
    have hzS_set : z ∉ (↑S : Set V) := fun h => hzS (Finset.mem_coe.mp h)
    have hF_disj : Disjoint ({s(x, z), s(y, z)} : Set (Sym2 V)) (G.edgesIn (↑S : Set V)) := by
      rw [Set.disjoint_left]; rintro e (rfl | rfl)
      · exact notMem_edgesIn_mk_of_right_notMem hzS_set
      · exact notMem_edgesIn_mk_of_right_notMem hzS_set
    have hF_card : ({s(x, z), s(y, z)} : Set (Sym2 V)).ncard = 2 :=
      Set.ncard_pair hxz_ne_yz
    have hT_tight : G.IsTightOn 2 3 T :=
      hT_def ▸ hS_tight.insert_vertex_with_edges h hzS
        (F := {s(x, z), s(y, z)})
        (Set.insert_subset hxz_in_T (Set.singleton_subset_iff.mpr hyz_in_T))
        hF_disj (Set.toFinite _) (by rw [hF_card])
    exact IsSparse.no_isTightOn_excluding_three_neighbors h hx hy hz hxy hxz hyz
      hvT hxT hyT hzT hT_tight

/-- **2-pair contradiction template.** Two blockers sharing a vertex `z` (the third neighbor):
`Sxz` contains `{x, z}` and `Syz` contains `{y, z}`, with the third pair `(x, y)` adjacent.
Case-split on `2 ≤ #(Sxz ∩ Syz)`. If yes, `IsTightOn.union_inter` gives `Sxz ∪ Syz` tight,
which contains `{x, y, z}`. If no, the intersection is exactly `{z}` (size 1, contains `z`),
forcing `x ∉ Syz` and `y ∉ Sxz`; the cross-edge `s(x, y)` lies in `edgesIn (Sxz ∪ Syz)` but in
neither `edgesIn Sxz` nor `edgesIn Syz`, saturating the squeeze at `T := Sxz ∪ Syz`. -/
theorem IsSparse.contradiction_two_pair
    [Finite V] {G : SimpleGraph V} (h : G.IsSparse 2 3) {v x y z : V}
    (hx : G.Adj v x) (hy : G.Adj v y) (hz : G.Adj v z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxy_adj : G.Adj x y)
    {Sxz : Finset V} (hvSxz : v ∉ Sxz) (hxSxz : x ∈ Sxz) (hzSxz : z ∈ Sxz)
    (hSxz_tight : G.IsTightOn 2 3 Sxz)
    {Syz : Finset V} (hvSyz : v ∉ Syz) (hySyz : y ∈ Syz) (hzSyz : z ∈ Syz)
    (hSyz_tight : G.IsTightOn 2 3 Syz) : False := by
  classical
  set T : Finset V := Sxz ∪ Syz with hT_def
  have hvT : v ∉ T := by
    simp only [hT_def, Finset.mem_union, not_or]
    exact ⟨hvSxz, hvSyz⟩
  have hxT : x ∈ T := Finset.mem_union_left _ hxSxz
  have hyT : y ∈ T := Finset.mem_union_right _ hySyz
  have hzT : z ∈ T := Finset.mem_union_left _ hzSxz
  by_cases h_big : 2 ≤ (Sxz ∩ Syz).card
  · have ⟨hT_tight, _⟩ := hSxz_tight.union_inter hSyz_tight h (by omega)
    exact IsSparse.no_isTightOn_excluding_three_neighbors h hx hy hz hxy hxz hyz
      hvT hxT hyT hzT hT_tight
  · push Not at h_big
    have hz_inter : z ∈ Sxz ∩ Syz := Finset.mem_inter.mpr ⟨hzSxz, hzSyz⟩
    have h_inter_card : (Sxz ∩ Syz).card = 1 := by
      have h_ge : 1 ≤ (Sxz ∩ Syz).card := Finset.card_pos.mpr ⟨z, hz_inter⟩
      omega
    have h_inter_eq : Sxz ∩ Syz = {z} :=
      Finset.eq_singleton_of_mem_of_card_le_one hz_inter (by omega)
    have hx_nin_Syz : x ∉ Syz := by
      intro hx_in
      have : x ∈ Sxz ∩ Syz := Finset.mem_inter.mpr ⟨hxSxz, hx_in⟩
      rw [h_inter_eq, Finset.mem_singleton] at this
      exact hxz this
    have hy_nin_Sxz : y ∉ Sxz := by
      intro hy_in
      have : y ∈ Sxz ∩ Syz := Finset.mem_inter.mpr ⟨hy_in, hySyz⟩
      rw [h_inter_eq, Finset.mem_singleton] at this
      exact hyz this
    have hxy_in_T : s(x, y) ∈ G.edgesIn (↑T : Set V) :=
      G.mk_mem_edgesIn hxy_adj (hT_def ▸ hxT) (hT_def ▸ hyT)
    have hF_disj : Disjoint ({s(x, y)} : Set (Sym2 V))
        (G.edgesIn (↑Sxz : Set V) ∪ G.edgesIn (↑Syz : Set V)) := by
      rw [Set.disjoint_left]; rintro e rfl
      rintro (h_in_Sxz | h_in_Syz)
      · exact notMem_edgesIn_mk_of_right_notMem
          (fun h => hy_nin_Sxz (Finset.mem_coe.mp h)) h_in_Sxz
      · exact notMem_edgesIn_mk_of_left_notMem
          (fun h => hx_nin_Syz (Finset.mem_coe.mp h)) h_in_Syz
    have h_e_inter : (G.edgesIn (↑(Sxz ∩ Syz) : Set V)).ncard = 0 := by
      rw [h_inter_eq, Finset.coe_singleton, edgesIn_singleton]
      exact Set.ncard_empty _
    have hT_tight : G.IsTightOn 2 3 T :=
      hT_def ▸ hSxz_tight.union_with_bonus hSyz_tight h
        (Set.singleton_subset_iff.mpr hxy_in_T) hF_disj (Set.finite_singleton _)
        (by rw [Set.ncard_singleton, h_inter_card]; omega)
    exact IsSparse.no_isTightOn_excluding_three_neighbors h hx hy hz hxy hxz hyz
      hvT hxT hyT hzT hT_tight

/-- **3-pair contradiction template.** Three blockers covering all three pairs of `v`'s neighbors;
non-adjacency is only required at the "outer" pair `(b, c)`. If any pairwise intersection has
size `≥ 2`, that pair's union is tight (`IsTightOn.union_inter`) and contains `{a, b, c}`.
Otherwise all three pairwise intersections are singletons, the pairwise-disjoint edge sets
accumulate without overlap, and the third-pair intersection `(Sab ∪ Sac) ∩ Sbc = {b, c}`
contributes zero edges (since `(b, c)` is non-adj here), saturating the squeeze at
`T := Sab ∪ Sac ∪ Sbc`. -/
theorem IsSparse.contradiction_three_pair
    [Finite V] {G : SimpleGraph V} (h : G.IsSparse 2 3) {v a b c : V}
    (ha : G.Adj v a) (hb : G.Adj v b) (hc : G.Adj v c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hbc_nadj : ¬ G.Adj b c)
    {Sab : Finset V} (hvSab : v ∉ Sab) (haSab : a ∈ Sab) (hbSab : b ∈ Sab)
    (hSab_tight : G.IsTightOn 2 3 Sab)
    {Sac : Finset V} (hvSac : v ∉ Sac) (haSac : a ∈ Sac) (hcSac : c ∈ Sac)
    (hSac_tight : G.IsTightOn 2 3 Sac)
    {Sbc : Finset V} (hvSbc : v ∉ Sbc) (hbSbc : b ∈ Sbc) (hcSbc : c ∈ Sbc)
    (hSbc_tight : G.IsTightOn 2 3 Sbc) : False := by
  classical
  by_cases h_ab_ac : 2 ≤ (Sab ∩ Sac).card
  · have ⟨hT_tight, _⟩ := hSab_tight.union_inter hSac_tight h (by omega)
    exact IsSparse.no_isTightOn_excluding_three_neighbors h ha hb hc hab hac hbc
      (by simp only [Finset.mem_union, not_or]; exact ⟨hvSab, hvSac⟩)
      (Finset.mem_union_left _ haSab)
      (Finset.mem_union_left _ hbSab)
      (Finset.mem_union_right _ hcSac) hT_tight
  by_cases h_ab_bc : 2 ≤ (Sab ∩ Sbc).card
  · have ⟨hT_tight, _⟩ := hSab_tight.union_inter hSbc_tight h (by omega)
    exact IsSparse.no_isTightOn_excluding_three_neighbors h ha hb hc hab hac hbc
      (by simp only [Finset.mem_union, not_or]; exact ⟨hvSab, hvSbc⟩)
      (Finset.mem_union_left _ haSab)
      (Finset.mem_union_left _ hbSab)
      (Finset.mem_union_right _ hcSbc) hT_tight
  by_cases h_ac_bc : 2 ≤ (Sac ∩ Sbc).card
  · have ⟨hT_tight, _⟩ := hSac_tight.union_inter hSbc_tight h (by omega)
    exact IsSparse.no_isTightOn_excluding_three_neighbors h ha hb hc hab hac hbc
      (by simp only [Finset.mem_union, not_or]; exact ⟨hvSac, hvSbc⟩)
      (Finset.mem_union_left _ haSac)
      (Finset.mem_union_right _ hbSbc)
      (Finset.mem_union_left _ hcSac) hT_tight
  push Not at h_ab_ac h_ab_bc h_ac_bc
  have hab_ac_card : (Sab ∩ Sac).card = 1 := by
    have : 1 ≤ (Sab ∩ Sac).card :=
      Finset.card_pos.mpr ⟨a, Finset.mem_inter.mpr ⟨haSab, haSac⟩⟩
    omega
  have hab_bc_card : (Sab ∩ Sbc).card = 1 := by
    have : 1 ≤ (Sab ∩ Sbc).card :=
      Finset.card_pos.mpr ⟨b, Finset.mem_inter.mpr ⟨hbSab, hbSbc⟩⟩
    omega
  have hac_bc_card : (Sac ∩ Sbc).card = 1 := by
    have : 1 ≤ (Sac ∩ Sbc).card :=
      Finset.card_pos.mpr ⟨c, Finset.mem_inter.mpr ⟨hcSac, hcSbc⟩⟩
    omega
  have hab_ac_eq : Sab ∩ Sac = {a} :=
    Finset.eq_singleton_of_mem_of_card_le_one
      (Finset.mem_inter.mpr ⟨haSab, haSac⟩) (by omega)
  have hab_bc_eq : Sab ∩ Sbc = {b} :=
    Finset.eq_singleton_of_mem_of_card_le_one
      (Finset.mem_inter.mpr ⟨hbSab, hbSbc⟩) (by omega)
  have hac_bc_eq : Sac ∩ Sbc = {c} :=
    Finset.eq_singleton_of_mem_of_card_le_one
      (Finset.mem_inter.mpr ⟨hcSac, hcSbc⟩) (by omega)
  have h_e_inter_ab_ac : (G.edgesIn (↑(Sab ∩ Sac) : Set V)).ncard = 0 := by
    rw [hab_ac_eq, Finset.coe_singleton, edgesIn_singleton]
    exact Set.ncard_empty _
  have h_super_12 : (G.edgesIn (↑Sab : Set V)).ncard + (G.edgesIn (↑Sac : Set V)).ncard
      ≤ (G.edgesIn (↑(Sab ∪ Sac) : Set V)).ncard := by
    have h_super := G.edgesIn_ncard_add_le (↑Sab : Set V) (↑Sac : Set V)
    have h_eq_union : (↑(Sab ∪ Sac) : Set V) = ↑Sab ∪ ↑Sac := Finset.coe_union _ _
    have h_eq_inter : (G.edgesIn (↑Sab ∩ ↑Sac : Set V)).ncard = 0 := by
      rw [← Finset.coe_inter]; exact h_e_inter_ab_ac
    rw [h_eq_union]
    omega
  have hT12_card : (Sab ∪ Sac).card = Sab.card + Sac.card - 1 := by
    have h1 := Finset.card_union_add_card_inter Sab Sac
    rw [hab_ac_card] at h1
    omega
  have h_T12_inter_Sbc_eq : (Sab ∪ Sac) ∩ Sbc = ({b, c} : Finset V) := by
    rw [Finset.union_inter_distrib_right, hab_bc_eq, hac_bc_eq]
    rfl
  have h_T12_inter_Sbc_card : ((Sab ∪ Sac) ∩ Sbc).card = 2 := by
    rw [h_T12_inter_Sbc_eq, Finset.card_pair hbc]
  have h_e_inter_T12_Sbc : (G.edgesIn (↑((Sab ∪ Sac) ∩ Sbc) : Set V)).ncard = 0 := by
    suffices h : G.edgesIn (↑((Sab ∪ Sac) ∩ Sbc) : Set V) = ∅ by
      rw [h]; exact Set.ncard_empty _
    rw [h_T12_inter_Sbc_eq]
    ext e
    refine e.ind fun p q => ?_
    simp only [Finset.coe_insert, Finset.coe_singleton, mem_edgesIn, mem_edgeSet, Sym2.coe_mk,
               Set.insert_subset_iff, Set.singleton_subset_iff, Set.mem_insert_iff,
               Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro h_adj h_p h_q
    rcases h_p with rfl | rfl <;> rcases h_q with rfl | rfl
    · exact G.loopless.irrefl _ h_adj
    · exact hbc_nadj h_adj
    · exact hbc_nadj h_adj.symm
    · exact G.loopless.irrefl _ h_adj
  set T : Finset V := (Sab ∪ Sac) ∪ Sbc with hT_def
  have h_super_T : (G.edgesIn (↑(Sab ∪ Sac) : Set V)).ncard +
      (G.edgesIn (↑Sbc : Set V)).ncard ≤ (G.edgesIn (↑T : Set V)).ncard := by
    have h_super := G.edgesIn_ncard_add_le (↑(Sab ∪ Sac) : Set V) (↑Sbc : Set V)
    have h_eq_union : (↑T : Set V) = ↑(Sab ∪ Sac) ∪ ↑Sbc := by
      rw [hT_def]; exact Finset.coe_union _ _
    have h_eq_inter : (G.edgesIn (↑(Sab ∪ Sac) ∩ ↑Sbc : Set V)).ncard = 0 := by
      rw [← Finset.coe_inter]; exact h_e_inter_T12_Sbc
    rw [h_eq_union]
    omega
  have hT_card : T.card = Sab.card + Sac.card + Sbc.card - 3 := by
    have h1 := Finset.card_union_add_card_inter (Sab ∪ Sac) Sbc
    rw [h_T12_inter_Sbc_card, hT12_card, ← hT_def] at h1
    have hT12_ge : 1 ≤ (Sab ∪ Sac).card :=
      Finset.card_pos.mpr ⟨a, Finset.mem_union_left _ haSab⟩
    omega
  have hvT : v ∉ T := by
    simp only [hT_def, Finset.mem_union, not_or]
    exact ⟨⟨hvSab, hvSac⟩, hvSbc⟩
  have haT : a ∈ T := Finset.mem_union_left _ (Finset.mem_union_left _ haSab)
  have hbT : b ∈ T := Finset.mem_union_left _ (Finset.mem_union_left _ hbSab)
  have hcT : c ∈ T := Finset.mem_union_left _ (Finset.mem_union_right _ hcSac)
  have hT_card_ge : 3 ≤ T.card :=
    Finset.three_le_card_of_three_distinct_mem hab hac hbc haT hbT hcT
  have hT_tight : G.IsTightOn 2 3 T := h.isTightOn_of_le (by omega) (by
    unfold IsTightOn at hSab_tight hSac_tight hSbc_tight; omega)
  exact IsSparse.no_isTightOn_excluding_three_neighbors h ha hb hc hab hac hbc
    hvT haT hbT hcT hT_tight

/-- **Unified contradiction from per-pair adj-or-blocker.** Given three distinct neighbors
`a, b, c` of a vertex `v` in a `(2, 3)`-sparse graph, with each pair `(a,b), (a,c), (b,c)`
either adjacent in `G` or witnessed by a tight blocker not containing `v`, and at least one
pair non-adjacent, derive `False`.

Dispatches across 8 leaves: the all-adjacent leaf contradicts `h_some_nonadj`; the other
seven fan out by blocker count (1-pair, 2-pair, 3-pair) into the corresponding contradiction
template. Replaces the 14-branch nested `by_cases` of the degree-3 dispatcher in
`IsLaman.exists_typeI_or_typeII_reverse` and will be reused by Phase 7's sparse-graph
reverse decomposition. -/
theorem IsSparse.False_of_pairwise_blocker_or_edge
    [Finite V] {G : SimpleGraph V} (h : G.IsSparse 2 3) {v a b c : V}
    (ha_adj : G.Adj v a) (hb_adj : G.Adj v b) (hc_adj : G.Adj v c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h_ab : G.Adj a b ∨ ∃ S : Finset V, v ∉ S ∧ a ∈ S ∧ b ∈ S ∧ G.IsTightOn 2 3 S)
    (h_ac : G.Adj a c ∨ ∃ S : Finset V, v ∉ S ∧ a ∈ S ∧ c ∈ S ∧ G.IsTightOn 2 3 S)
    (h_bc : G.Adj b c ∨ ∃ S : Finset V, v ∉ S ∧ b ∈ S ∧ c ∈ S ∧ G.IsTightOn 2 3 S)
    (h_some_nonadj : ¬ G.Adj a b ∨ ¬ G.Adj a c ∨ ¬ G.Adj b c) :
    False := by
  rcases h_ab with hab_adj | ⟨Sab, hvSab, haSab, hbSab, hSab_tight⟩
  · rcases h_ac with hac_adj | ⟨Sac, hvSac, haSac, hcSac, hSac_tight⟩
    · rcases h_bc with hbc_adj | ⟨Sbc, hvSbc, hbSbc, hcSbc, hSbc_tight⟩
      · rcases h_some_nonadj with h' | h' | h'
        · exact h' hab_adj
        · exact h' hac_adj
        · exact h' hbc_adj
      · exact IsSparse.contradiction_one_pair h hb_adj hc_adj ha_adj hbc hab.symm hac.symm
          hab_adj.symm hac_adj.symm hvSbc hbSbc hcSbc hSbc_tight
    · rcases h_bc with hbc_adj | ⟨Sbc, hvSbc, hbSbc, hcSbc, hSbc_tight⟩
      · exact IsSparse.contradiction_one_pair h ha_adj hc_adj hb_adj hac hab hbc.symm
          hab_adj hbc_adj.symm hvSac haSac hcSac hSac_tight
      · exact IsSparse.contradiction_two_pair h ha_adj hb_adj hc_adj hab hac hbc
          hab_adj
          hvSac haSac hcSac hSac_tight
          hvSbc hbSbc hcSbc hSbc_tight
  · rcases h_ac with hac_adj | ⟨Sac, hvSac, haSac, hcSac, hSac_tight⟩
    · rcases h_bc with hbc_adj | ⟨Sbc, hvSbc, hbSbc, hcSbc, hSbc_tight⟩
      · exact IsSparse.contradiction_one_pair h ha_adj hb_adj hc_adj hab hac hbc
          hac_adj hbc_adj hvSab haSab hbSab hSab_tight
      · exact IsSparse.contradiction_two_pair h ha_adj hc_adj hb_adj hac hab hbc.symm
          hac_adj
          hvSab haSab hbSab hSab_tight
          hvSbc hcSbc hbSbc hSbc_tight
    · rcases h_bc with hbc_adj | ⟨Sbc, hvSbc, hbSbc, hcSbc, hSbc_tight⟩
      · exact IsSparse.contradiction_two_pair h hb_adj hc_adj ha_adj hbc hab.symm hac.symm
          hbc_adj
          hvSab hbSab haSab hSab_tight
          hvSac hcSac haSac hSac_tight
      · rcases h_some_nonadj with hab_nadj | hac_nadj | hbc_nadj
        · exact IsSparse.contradiction_three_pair h hc_adj ha_adj hb_adj hac.symm hbc.symm hab
            hab_nadj
            hvSac hcSac haSac hSac_tight
            hvSbc hcSbc hbSbc hSbc_tight
            hvSab haSab hbSab hSab_tight
        · exact IsSparse.contradiction_three_pair h hb_adj ha_adj hc_adj hab.symm hbc hac
            hac_nadj
            hvSab hbSab haSab hSab_tight
            hvSbc hbSbc hcSbc hSbc_tight
            hvSac haSac hcSac hSac_tight
        · exact IsSparse.contradiction_three_pair h ha_adj hb_adj hc_adj hab hac hbc
            hbc_nadj
            hvSab haSab hbSab hSab_tight
            hvSac haSac hcSac hSac_tight
            hvSbc hbSbc hcSbc hSbc_tight

/-! ### Per-pair tight-blocker witness (typeII reverse, sparse form)

The combinatorial heart of the typeII Henneberg reverse: given a `(2, 3)`-sparse graph `G`,
a vertex `v`, a pair of distinct vertices `x, y` both `≠ v`, and a *failed* candidate
`G' := (G ↾ {v}ᶜ) ⊔ {bridge(x, y)}` — i.e. `¬ G'.IsSparse 2 3` — extract a `(2, 3)`-tight set
`S ⊆ V \ {v}` in `G` containing both `x` and `y`. The proof lifts a sparsity-violating Finset
of `G'` along `Subtype.val` to a Finset of `V \ {v}`, then case-splits on whether the bridge
edge survives the lift (`xs, ys ∈ s'`): on the bridge-surviving side the squeeze closes via
`IsSparse.isTightOn_of_le`; on the other side the bridge is forced out and `G`'s sparsity
contradicts directly.

The Phase-5 Laman-flavored shell `IsLaman.typeII_reverse_blocker` (in `Henneberg.lean`)
routed `¬ G'.IsLaman` through the typeII iso + global edge count to derive
`¬ G'.IsSparse 2 3` and call this lemma; Phase 7 lifted the entire reverse-decomposition
pipeline (Jordán Lemma 2.1.4) to the sparse layer and the shell was deleted in Commit 6 of
that phase. -/

/-- **Per-pair tight-blocker witness for the typeII Henneberg reverse (sparse form).**

Inputs: a `(2, 3)`-sparse graph `G`; distinct vertices `x, y` both `≠ v`; a sparsity violation
on the typeII-reverse candidate `G' := (G ↾ {v}ᶜ) ⊔ {bridge(x, y)}`.

Output: a `(2, 3)`-tight set `S` in `G` with `v ∉ S` and `{x, y} ⊆ S`.

The proof extracts a violating Finset `s'` from `¬ G'.IsSparse 2 3` and lifts it to
`S := s'.image Subtype.val ⊆ V \ {v}`. The bound `(G'.edgesIn ↑s').ncard ≤ (G.edgesIn ↑S).ncard
+ 1` (case `xs, ys ∈ s'`) combined with `G`'s sparsity at `S` gives tightness via
`IsSparse.isTightOn_of_le`; the remaining case (one of `xs, ys` outside `s'`) drops the `+1` and
contradicts `G`'s sparsity directly. -/
theorem IsSparse.typeII_reverse_blocker
    [Finite V] {G : SimpleGraph V} (h : G.IsSparse 2 3) {v x y : V}
    (hxv : x ≠ v) (hyv : y ≠ v)
    (h_not_sparse : ¬ (G.comap (Subtype.val : {w : V // w ≠ v} → V) ⊔
                       fromEdgeSet ({s(⟨x, hxv⟩, ⟨y, hyv⟩)} : Set (Sym2 _))).IsSparse 2 3) :
    ∃ S : Finset V, v ∉ S ∧ x ∈ S ∧ y ∈ S ∧ G.IsTightOn 2 3 S := by
  classical
  set f : {w : V // w ≠ v} → V := Subtype.val with hf_def
  set xs : {w : V // w ≠ v} := ⟨x, hxv⟩ with hxs_def
  set ys : {w : V // w ≠ v} := ⟨y, hyv⟩ with hys_def
  set bridge : Sym2 {w : V // w ≠ v} := s(xs, ys) with hbridge_def
  set G' : SimpleGraph {w : V // w ≠ v} :=
    G.comap f ⊔ fromEdgeSet ({bridge} : Set _) with hG'_def
  -- Extract violating Finset from `¬ G'.IsSparse 2 3`.
  unfold IsSparse at h_not_sparse
  push Not at h_not_sparse
  obtain ⟨s', hs'_card, hviol⟩ := h_not_sparse
  -- Lift to S = s'.image Subtype.val ⊆ V \ {v}.
  set S : Finset V := s'.image f with hS_def
  have hS_card : S.card = s'.card :=
    Finset.card_image_of_injective s' Subtype.val_injective
  have hvS : v ∉ S := by
    intro hmem
    obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hmem
    exact w.2 hw
  -- (G.comap f).edgesIn ↑s' has the same ncard as G.edgesIn ↑S.
  have h_link : ((G.comap f).edgesIn (↑s' : Set _)).ncard = (G.edgesIn (↑S : Set V)).ncard := by
    rw [hS_def, Finset.coe_image, ← image_edgesIn_comap,
        Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)]
  -- G's sparsity at S.
  have hS_sparse : (G.edgesIn (↑S : Set V)).ncard + 3 ≤ 2 * S.card := by
    have := h S (by rw [hS_card]; exact hs'_card)
    exact this
  -- Case-split on whether both xs, ys ∈ s'.
  by_cases h_both : xs ∈ s' ∧ ys ∈ s'
  · -- Case 1: bridge potentially in G'.edgesIn ↑s'. Bound by (G.edgesIn ↑S).ncard + 1.
    obtain ⟨hxs_in, hys_in⟩ := h_both
    have h_subset : G'.edgesIn (↑s' : Set _) ⊆
        (G.comap f).edgesIn (↑s' : Set _) ∪ ({bridge} : Set _) := by
      intro e he
      rw [mem_edgesIn] at he
      obtain ⟨he_edge, he_sub⟩ := he
      rw [hG'_def, edgeSet_sup] at he_edge
      rcases he_edge with hin_comap | hin_bridge
      · exact Or.inl (mem_edgesIn.mpr ⟨hin_comap, he_sub⟩)
      · rw [edgeSet_fromEdgeSet] at hin_bridge
        exact Or.inr (Set.diff_subset hin_bridge)
    have h_ncard_bound : (G'.edgesIn (↑s' : Set _)).ncard ≤
        (G.edgesIn (↑S : Set V)).ncard + 1 :=
      calc (G'.edgesIn (↑s' : Set _)).ncard
          ≤ ((G.comap f).edgesIn (↑s' : Set _) ∪ ({bridge} : Set _)).ncard :=
            Set.ncard_le_ncard h_subset (Set.toFinite _)
        _ ≤ ((G.comap f).edgesIn (↑s' : Set _)).ncard + ({bridge} : Set _).ncard :=
            Set.ncard_union_le _ _
        _ = (G.edgesIn (↑S : Set V)).ncard + 1 := by
            rw [h_link, Set.ncard_singleton]
    have hx_in_S : x ∈ S := by
      simp only [hS_def, Finset.mem_image]
      exact ⟨xs, hxs_in, rfl⟩
    have hy_in_S : y ∈ S := by
      simp only [hS_def, Finset.mem_image]
      exact ⟨ys, hys_in, rfl⟩
    refine ⟨S, hvS, hx_in_S, hy_in_S, ?_⟩
    refine h.isTightOn_of_le ?_ ?_
    · rw [hS_card]; exact hs'_card
    · rw [hS_card]; omega
  · -- Case 2: one of xs, ys not in s'. Bridge excluded; bound by (G.edgesIn ↑S).ncard.
    have h_subset : G'.edgesIn (↑s' : Set _) ⊆ (G.comap f).edgesIn (↑s' : Set _) := by
      intro e he
      rw [mem_edgesIn] at he ⊢
      obtain ⟨he_edge, he_sub⟩ := he
      refine ⟨?_, he_sub⟩
      rw [hG'_def, edgeSet_sup] at he_edge
      rcases he_edge with hin_comap | hin_bridge
      · exact hin_comap
      · rw [edgeSet_fromEdgeSet, Set.mem_diff, Set.mem_singleton_iff] at hin_bridge
        obtain ⟨rfl, _⟩ := hin_bridge
        rw [hbridge_def, Sym2.coe_mk, Set.insert_subset_iff,
            Set.singleton_subset_iff, Finset.mem_coe, Finset.mem_coe] at he_sub
        exact absurd he_sub h_both
    have h_ncard_bound : (G'.edgesIn (↑s' : Set _)).ncard ≤
        (G.edgesIn (↑S : Set V)).ncard := by
      rw [← h_link]
      exact Set.ncard_le_ncard h_subset (Set.toFinite _)
    exfalso
    rw [hS_card] at hS_sparse
    omega

/-! ### Flat-form Henneberg reverse decomposition

In a `(2, 3)`-sparse graph with at least one edge, a Henneberg reverse step exists distinguished
by `G.degree v ∈ {1, 2, 3}`: pendant reverse (delete a degree-1 vertex), Type I reverse (delete
a degree-2 vertex), or Type II reverse (split a degree-3 vertex with a non-adjacent neighbour
pair). The sparse analogue of Phase 5 milestone 1 (`IsLaman.exists_typeI_or_typeII_reverse` in
`Henneberg.lean`), stated in **flat form** per `DESIGN.md` *Statement-form conventions*: the
conclusion describes the smaller graph by its edges directly (`G - v` as `G.comap Subtype.val`,
the typeII candidate as `G.comap Subtype.val ⊔ fromEdgeSet {bridge}`) rather than via the
`typeI` / `typeII` Henneberg operations.

Proof structure (Jordán Lemma 2.1.4): pick a vertex `v` with `1 ≤ G.degree v ≤ 3` via
`IsSparse.exists_one_le_degree_le_three`; split on `G.degree v ∈ {1, 2, 3}`. The pendant
(`= 1`) and Type I (`= 2`) cases close via `IsSparse.comap` after extracting neighbour data
from `card_eq_one` / `card_eq_two`. The `= 3` case runs the per-pair witness-or-blocker
dispatch using `IsSparse.typeII_reverse_blocker` and combines three blockers via
`IsSparse.False_of_pairwise_blocker_or_edge`. -/

/-- **Flat-form Henneberg reverse decomposition (Jordán Lemma 2.1.4).** Every `(2, 3)`-sparse
graph with at least one edge admits a Henneberg reverse to a smaller `(2, 3)`-sparse graph,
distinguished by `G.degree v ∈ {1, 2, 3}`:

* **Pendant reverse** (`G.degree v = 1`): the unique neighbour `a` of `v` is exposed and
  the induced subgraph on `{w // w ≠ v}` is `(2, 3)`-sparse.
* **Type I reverse** (`G.degree v = 2`): the two distinct neighbours `a ≠ b` of `v` are
  exposed and the induced subgraph on `{w // w ≠ v}` is `(2, 3)`-sparse.
* **Type II reverse** (`G.degree v = 3`): three neighbours `x, y, c` of `v` are exposed,
  along with a non-adjacent pair `(x, y)`, such that the induced subgraph augmented with the
  bridging edge `s(x, y)` is `(2, 3)`-sparse.

The sparse analogue of Phase 5 milestone 1's `IsLaman.exists_typeI_or_typeII_reverse`. Stated
in flat form: the smaller graphs are described by their explicit edge constructions rather
than via the typeI / typeII Henneberg operations (see `DESIGN.md` *Statement-form
conventions*). Phase 7's row-LI lift consumers reconstruct the operation form at each step
via `typeI_iso_of_two_neighbors` / `typeII_iso_of_three_neighbors` in `Henneberg.lean`. The
pendant branch invokes `typeI_iso_of_two_neighbors` at `a = b` (the unique neighbour);
`typeI G' a a` joins the new vertex to a single old vertex, modelling the pendant
attachment used by Lovász–Yemini to reverse a degree-1 vertex. -/
theorem IsSparse.exists_typeI_or_typeII_reverse [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (h : G.IsSparse 2 3)
    (hE : G.edgeSet.Nonempty) :
    ∃ v : V,
      (G.degree v = 1 ∧
        ∃ a : {w : V // w ≠ v},
          (∀ w : V, G.Adj v w ↔ w = a.val) ∧
          (G.comap (Subtype.val : {w : V // w ≠ v} → V)).IsSparse 2 3)
      ∨
      (G.degree v = 2 ∧
        ∃ a b : {w : V // w ≠ v}, a ≠ b ∧
          (∀ w : V, G.Adj v w ↔ w = a.val ∨ w = b.val) ∧
          (G.comap (Subtype.val : {w : V // w ≠ v} → V)).IsSparse 2 3)
      ∨
      (G.degree v = 3 ∧
        ∃ x y c : {w : V // w ≠ v}, x ≠ y ∧ c ≠ x ∧ c ≠ y ∧
          (∀ w : V, G.Adj v w ↔ w = x.val ∨ w = y.val ∨ w = c.val) ∧
          ¬ G.Adj x.val y.val ∧
          (G.comap (Subtype.val : {w : V // w ≠ v} → V) ⊔
            fromEdgeSet ({s(x, y)} : Set _)).IsSparse 2 3) := by
  classical
  obtain ⟨v, hv1, hv3⟩ := h.exists_one_le_degree_le_three hE
  refine ⟨v, ?_⟩
  -- Case split on `G.degree v ∈ {1, 2, 3}`. Pendant and Type I close via `IsSparse.comap` after
  -- extracting neighbour data; Type II runs the existing per-pair witness/blocker dispatch.
  rcases (show G.degree v = 1 ∨ G.degree v = 2 ∨ G.degree v = 3 from by omega)
    with hdeg1 | hdeg2 | hdeg3
  · -- Pendant branch: `card_eq_one` extracts the unique neighbour `a`.
    obtain ⟨a, hN_eq⟩ := Finset.card_eq_one.mp hdeg1
    have hN_iff : ∀ w, G.Adj v w ↔ w = a := fun w => by
      rw [← mem_neighborFinset, hN_eq]; simp
    have ha_adj : G.Adj v a := (hN_iff a).mpr rfl
    have hva : v ≠ a := G.ne_of_adj ha_adj
    exact Or.inl ⟨hdeg1, ⟨a, hva.symm⟩, hN_iff, h.comap Subtype.val_injective⟩
  · -- Type I branch: `card_eq_two` extracts the two distinct neighbours `a, b`.
    obtain ⟨a, b, hab, hN_eq⟩ := Finset.card_eq_two.mp hdeg2
    have hN_iff : ∀ w, G.Adj v w ↔ w = a ∨ w = b := fun w => by
      rw [← mem_neighborFinset, hN_eq]; simp
    have ha_adj : G.Adj v a := (hN_iff a).mpr (Or.inl rfl)
    have hb_adj : G.Adj v b := (hN_iff b).mpr (Or.inr rfl)
    have hva : v ≠ a := G.ne_of_adj ha_adj
    have hvb : v ≠ b := G.ne_of_adj hb_adj
    have hab_s : (⟨a, hva.symm⟩ : {w : V // w ≠ v}) ≠ ⟨b, hvb.symm⟩ :=
      fun heq => hab (Subtype.mk.injEq .. |>.mp heq)
    exact Or.inr (Or.inl ⟨hdeg2, ⟨a, hva.symm⟩, ⟨b, hvb.symm⟩, hab_s, hN_iff,
      h.comap Subtype.val_injective⟩)
  · -- Type II branch: degree v = 3. For each pair of neighbors, dispatch
    -- `witness ∨ Adj ∨ blocker`; short-circuit on any witness; otherwise feed the three
    -- `Adj ∨ blocker` disjunctions to `IsSparse.False_of_pairwise_blocker_or_edge` together
    -- with the non-adj disjunction from `IsSparse.exists_nonadj_among_three_neighbors`.
    refine Or.inr (Or.inr ⟨hdeg3, ?_⟩)
    obtain ⟨a, b, c, hab, hac, hbc, hN_eq⟩ := Finset.card_eq_three.mp hdeg3
    have hN_iff : ∀ w, G.Adj v w ↔ w = a ∨ w = b ∨ w = c := fun w => by
      rw [← mem_neighborFinset, hN_eq]; simp
    have ha_adj : G.Adj v a := (hN_iff a).mpr (Or.inl rfl)
    have hb_adj : G.Adj v b := (hN_iff b).mpr (Or.inr (Or.inl rfl))
    have hc_adj : G.Adj v c := (hN_iff c).mpr (Or.inr (Or.inr rfl))
    have hva : v ≠ a := G.ne_of_adj ha_adj
    have hvb : v ≠ b := G.ne_of_adj hb_adj
    have hvc : v ≠ c := G.ne_of_adj hc_adj
    have hN_iff_acb : ∀ w, G.Adj v w ↔ w = a ∨ w = c ∨ w = b := fun w => by
      rw [hN_iff]; tauto
    have hN_iff_bca : ∀ w, G.Adj v w ↔ w = b ∨ w = c ∨ w = a := fun w => by
      rw [hN_iff]; tauto
    -- Result type for a non-adjacent-pair typeII reverse witness.
    let WitnessType := ∃ x y c' : {w : V // w ≠ v}, x ≠ y ∧ c' ≠ x ∧ c' ≠ y ∧
      (∀ w : V, G.Adj v w ↔ w = x.val ∨ w = y.val ∨ w = c'.val) ∧
      ¬ G.Adj x.val y.val ∧
      (G.comap (Subtype.val : {w : V // w ≠ v} → V) ⊔
        fromEdgeSet ({s(x, y)} : Set _)).IsSparse 2 3
    -- Per-pair dispatch: `witness ∨ Adj ∨ blocker`. The blocker side feeds into
    -- `False_of_pairwise_blocker_or_edge`; the witness side short-circuits.
    have h_ab : WitnessType ∨ G.Adj a b ∨
        ∃ S : Finset V, v ∉ S ∧ a ∈ S ∧ b ∈ S ∧ G.IsTightOn 2 3 S := by
      by_cases hab_adj : G.Adj a b
      · exact Or.inr (Or.inl hab_adj)
      · by_cases hsparse : (G.comap (Subtype.val : {w : V // w ≠ v} → V) ⊔
            fromEdgeSet ({s(⟨a, hva.symm⟩, ⟨b, hvb.symm⟩)} : Set _)).IsSparse 2 3
        · exact Or.inl ⟨⟨a, hva.symm⟩, ⟨b, hvb.symm⟩, ⟨c, hvc.symm⟩,
            fun heq => hab (Subtype.mk.injEq .. |>.mp heq),
            fun heq => hac.symm (Subtype.mk.injEq .. |>.mp heq),
            fun heq => hbc.symm (Subtype.mk.injEq .. |>.mp heq),
            hN_iff, hab_adj, hsparse⟩
        · exact Or.inr (Or.inr (h.typeII_reverse_blocker hva.symm hvb.symm hsparse))
    have h_ac : WitnessType ∨ G.Adj a c ∨
        ∃ S : Finset V, v ∉ S ∧ a ∈ S ∧ c ∈ S ∧ G.IsTightOn 2 3 S := by
      by_cases hac_adj : G.Adj a c
      · exact Or.inr (Or.inl hac_adj)
      · by_cases hsparse : (G.comap (Subtype.val : {w : V // w ≠ v} → V) ⊔
            fromEdgeSet ({s(⟨a, hva.symm⟩, ⟨c, hvc.symm⟩)} : Set _)).IsSparse 2 3
        · exact Or.inl ⟨⟨a, hva.symm⟩, ⟨c, hvc.symm⟩, ⟨b, hvb.symm⟩,
            fun heq => hac (Subtype.mk.injEq .. |>.mp heq),
            fun heq => hab.symm (Subtype.mk.injEq .. |>.mp heq),
            fun heq => hbc (Subtype.mk.injEq .. |>.mp heq),
            hN_iff_acb, hac_adj, hsparse⟩
        · exact Or.inr (Or.inr (h.typeII_reverse_blocker hva.symm hvc.symm hsparse))
    have h_bc : WitnessType ∨ G.Adj b c ∨
        ∃ S : Finset V, v ∉ S ∧ b ∈ S ∧ c ∈ S ∧ G.IsTightOn 2 3 S := by
      by_cases hbc_adj : G.Adj b c
      · exact Or.inr (Or.inl hbc_adj)
      · by_cases hsparse : (G.comap (Subtype.val : {w : V // w ≠ v} → V) ⊔
            fromEdgeSet ({s(⟨b, hvb.symm⟩, ⟨c, hvc.symm⟩)} : Set _)).IsSparse 2 3
        · exact Or.inl ⟨⟨b, hvb.symm⟩, ⟨c, hvc.symm⟩, ⟨a, hva.symm⟩,
            fun heq => hbc (Subtype.mk.injEq .. |>.mp heq),
            fun heq => hab (Subtype.mk.injEq .. |>.mp heq),
            fun heq => hac (Subtype.mk.injEq .. |>.mp heq),
            hN_iff_bca, hbc_adj, hsparse⟩
        · exact Or.inr (Or.inr (h.typeII_reverse_blocker hvb.symm hvc.symm hsparse))
    rcases h_ab with witness | h_ab
    · exact witness
    rcases h_ac with witness | h_ac
    · exact witness
    rcases h_bc with witness | h_bc
    · exact witness
    exact absurd
      (h.False_of_pairwise_blocker_or_edge ha_adj hb_adj hc_adj hab hac hbc h_ab h_ac h_bc
        (h.exists_nonadj_among_three_neighbors ha_adj hb_adj hc_adj hab hac hbc)) id

/-! ### Matroidal-regime maximal I-blocks (I-components)

For a `(k, ℓ)`-sparse edge set `I` in the matroidal regime `ℓ < 2 * k`, the family of
`(fromEdgeSet I)`-tight Finsets containing a fixed Finset `X ⊆ V` with `|X| ≥ 2` is
closed under pairwise union (`IsTightOn.union_inter_of_pair`); the union of the whole
family — `G.maxBlock k ℓ X` — is therefore itself `G`-tight when
non-empty, the maximal `I`-block containing `X` (or *I-component* of `X`, in
Lee–Streinu's terminology). Distinct I-components share at most one vertex, hence are
edge-disjoint: each non-free I-edge lies in a unique I-component. This scaffolding
drives Phase 7's `(k, ℓ)`-augmentation lemma `IsSparse.exists_aug_of_lt_two_mul`
(Commit 17c). -/

section IComponents

variable [Finite V]

/-- Predicate: some `G`-tight Finset contains `X`. The `maxBlock X` is non-empty
exactly when this holds. Defined for any graph; the matroidal-regime closure
properties (`IsSparse.maxBlock_isTightOn` and friends) need additional sparsity. -/
def HasBlock (G : SimpleGraph V) (k ℓ : ℕ) (X : Finset V) : Prop :=
  ∃ S : Finset V, G.IsTightOn k ℓ S ∧ X ⊆ S

/-- **Maximal block at a Finset `X`** (a.k.a. *`G`-component of `X`* in the
matroidal regime when `G` is sparse), as a Set. The union of all `G`-tight
Finsets containing `X`, viewed as vertices of `V`. The `Finset`-valued version
(after finiteness) is `maxBlock` below. -/
def maxBlockSet (G : SimpleGraph V) (k ℓ : ℕ) (X : Finset V) : Set V :=
  ⋃ (S : Finset V) (_ : G.IsTightOn k ℓ S ∧ X ⊆ S), (↑S : Set V)

/-- `maxBlockSet` is finite when `V` is. -/
lemma maxBlockSet_finite (G : SimpleGraph V) (k ℓ : ℕ) (X : Finset V) :
    (G.maxBlockSet k ℓ X).Finite :=
  (Set.toFinite (Set.univ : Set V)).subset (Set.subset_univ _)

/-- **Maximal block at `X`**, as a `Finset`. -/
noncomputable def maxBlock (G : SimpleGraph V) (k ℓ : ℕ) (X : Finset V) : Finset V :=
  (G.maxBlockSet_finite k ℓ X).toFinset

/-- Membership in `maxBlock`. -/
lemma mem_maxBlock {G : SimpleGraph V} {k ℓ : ℕ} {X : Finset V} {x : V} :
    x ∈ G.maxBlock k ℓ X ↔ ∃ S : Finset V,
      G.IsTightOn k ℓ S ∧ X ⊆ S ∧ x ∈ S := by
  unfold maxBlock
  rw [Set.Finite.mem_toFinset]
  unfold maxBlockSet
  simp [Set.mem_iUnion, and_assoc]

/-- Every `G`-tight Finset containing `X` is contained in `maxBlock X`. -/
lemma subset_maxBlock {G : SimpleGraph V} {k ℓ : ℕ} {X S : Finset V}
    (hS : G.IsTightOn k ℓ S) (hXS : X ⊆ S) :
    S ⊆ G.maxBlock k ℓ X := fun x hxS => by
  rw [mem_maxBlock]
  exact ⟨S, hS, hXS, hxS⟩

/-- `X ⊆ maxBlock X` whenever `HasBlock X`. -/
lemma subset_maxBlock_of_hasBlock {G : SimpleGraph V} {k ℓ : ℕ} {X : Finset V}
    (hB : G.HasBlock k ℓ X) :
    X ⊆ G.maxBlock k ℓ X := by
  obtain ⟨S, hS, hXS⟩ := hB
  exact hXS.trans (subset_maxBlock hS hXS)

/-- **`maxBlock X` is `G`-tight** in the matroidal regime `ℓ < 2*k`, for sparse
`G`, provided `|X| ≥ 2` and some `G`-tight Finset contains `X`. The proof reduces
to "the Set-union of pairwise-union-closed `G`-tight Finsets is itself a
`G`-tight Finset" — a Finset-level closure argument. -/
lemma IsSparse.maxBlock_isTightOn {G : SimpleGraph V} {k ℓ : ℕ}
    (hI : G.IsSparse k ℓ) (hℓ : ℓ < 2 * k)
    {X : Finset V} (hX_card : 2 ≤ X.card) (hB : G.HasBlock k ℓ X) :
    G.IsTightOn k ℓ (G.maxBlock k ℓ X) := by
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hX_card
  -- The maxBlock equals the join of the Finset family {S | G-tight ∧ X ⊆ S}.
  -- We prove the equality `maxBlock X = F.sup id` for an explicit Finset F via
  -- a separate auxiliary lemma path, then run `Finset.sup_mem`.
  -- Strategy: use a noncomputable Fintype instance to express the family as a
  -- `Finset (Finset V)`, then prove the maxBlock coincides with its `Finset.sup`.
  letI : Fintype V := Fintype.ofFinite V
  classical
  set F : Finset (Finset V) := (Finset.univ : Finset (Finset V)).filter
    (fun S => G.IsTightOn k ℓ S ∧ X ⊆ S) with hF_def
  -- maxBlock X = F.sup id as Finsets (set extensionality).
  have h_maxBlock_eq : G.maxBlock k ℓ X = F.sup id := by
    apply Finset.ext
    intro x
    rw [mem_maxBlock]
    simp only [Finset.mem_sup, hF_def, Finset.mem_filter, Finset.mem_univ, true_and,
      id_eq]
    constructor
    · rintro ⟨S, hS, hXS, hxS⟩; exact ⟨S, ⟨hS, hXS⟩, hxS⟩
    · rintro ⟨S, ⟨hS, hXS⟩, hxS⟩; exact ⟨S, hS, hXS, hxS⟩
  rw [h_maxBlock_eq]
  -- Auxiliary predicate P closed under (∅, ⊔) containing every G-tight S ⊇ X.
  let P : Set (Finset V) :=
    { T | T = ∅ ∨ (G.IsTightOn k ℓ T ∧ X ⊆ T) }
  have hP_bot : (∅ : Finset V) ∈ P := Or.inl rfl
  have hP_join : ∀ T₁ ∈ P, ∀ T₂ ∈ P, T₁ ⊔ T₂ ∈ P := by
    intro T₁ hT₁ T₂ hT₂
    rcases hT₁ with hT₁ | ⟨hT₁_tight, hT₁_X⟩
    · subst hT₁; simpa using hT₂
    · rcases hT₂ with hT₂ | ⟨hT₂_tight, hT₂_X⟩
      · subst hT₂; simpa using Or.inr ⟨hT₁_tight, hT₁_X⟩
      · refine Or.inr ⟨?_, hT₁_X.trans Finset.subset_union_left⟩
        exact (hT₁_tight.union_inter_of_pair hℓ hT₂_tight hI huv
          (hT₁_X hu) (hT₁_X hv) (hT₂_X hu) (hT₂_X hv)).1
  have hP_id : ∀ S ∈ F, (id S) ∈ P := by
    intro S hS
    rcases Finset.mem_filter.mp hS with ⟨_, hS_tight, hS_X⟩
    exact Or.inr ⟨hS_tight, hS_X⟩
  have h_sup_in_P : F.sup id ∈ P := Finset.sup_mem P hP_bot hP_join F id hP_id
  -- F.sup id is non-empty since hB witnesses non-emptiness.
  obtain ⟨S₀, hS₀_tight, hS₀_X⟩ := hB
  have h_S₀_in_F : S₀ ∈ F :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS₀_tight, hS₀_X⟩
  have h_u_in_sup : u ∈ F.sup id :=
    (Finset.le_sup (f := id) h_S₀_in_F) (hS₀_X hu)
  rcases h_sup_in_P with h_empty | ⟨h_tight, _⟩
  · rw [h_empty] at h_u_in_sup
    exact absurd h_u_in_sup (Finset.notMem_empty u)
  · exact h_tight

/-- **Edge-disjointness of distinct components.** For sparse `G` in the
matroidal regime, if `Y ⊆ maxBlock X` with both `|X|, |Y| ≥ 2`, then
`maxBlock Y = maxBlock X`. Two distinct non-empty components therefore share
at most one vertex (and so contain no common off-diagonal edge of `K_V`). -/
lemma IsSparse.maxBlock_eq_of_subset_maxBlock {G : SimpleGraph V} {k ℓ : ℕ}
    (hI : G.IsSparse k ℓ) (hℓ : ℓ < 2 * k)
    {X Y : Finset V} (hX_card : 2 ≤ X.card) (hY_card : 2 ≤ Y.card)
    (hBX : G.HasBlock k ℓ X) (hY_sub : Y ⊆ G.maxBlock k ℓ X) :
    G.maxBlock k ℓ Y = G.maxBlock k ℓ X := by
  classical
  have h_X_in_maxX : X ⊆ G.maxBlock k ℓ X := subset_maxBlock_of_hasBlock hBX
  have h_maxX_tight : G.IsTightOn k ℓ (G.maxBlock k ℓ X) :=
    hI.maxBlock_isTightOn hℓ hX_card hBX
  -- `maxBlock X` itself is a G-tight Finset ⊇ Y, hence ⊆ maxBlock Y.
  have h_maxX_sub_maxY : G.maxBlock k ℓ X ⊆ G.maxBlock k ℓ Y :=
    subset_maxBlock h_maxX_tight hY_sub
  -- Reverse: maxBlock Y is G-tight (HasBlock Y witnessed by maxBlock X), and shares
  -- ≥ 2 vertices with maxBlock X, so their union is G-tight + ⊇ X + ⊆ maxBlock X.
  have h_BY : G.HasBlock k ℓ Y := ⟨G.maxBlock k ℓ X, h_maxX_tight, hY_sub⟩
  have h_maxY_tight : G.IsTightOn k ℓ (G.maxBlock k ℓ Y) :=
    hI.maxBlock_isTightOn hℓ hY_card h_BY
  have h_Y_in_maxY : Y ⊆ G.maxBlock k ℓ Y := subset_maxBlock_of_hasBlock h_BY
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hY_card
  have h_union := (h_maxX_tight.union_inter_of_pair hℓ h_maxY_tight hI huv
    (hY_sub hu) (hY_sub hv) (h_Y_in_maxY hu) (h_Y_in_maxY hv)).1
  have h_union_X : X ⊆ G.maxBlock k ℓ X ∪ G.maxBlock k ℓ Y :=
    h_X_in_maxX.trans Finset.subset_union_left
  have h_maxY_sub_maxX : G.maxBlock k ℓ Y ⊆ G.maxBlock k ℓ X :=
    Finset.subset_union_right.trans (subset_maxBlock h_union h_union_X)
  exact Finset.Subset.antisymm h_maxY_sub_maxX h_maxX_sub_maxY

end IComponents

/-! ### Augmentation in the matroidal regime (`ℓ < 2 * k`)

The combinatorial heart of the `(k, ℓ)`-count matroid (Whiteley 1996, Lee–Streinu 2008):
for `(k, ℓ)`-sparse edge sets `I, J ⊆ E(K_V)` with `|I| < |J|`, some `e ∈ J \ I` extends
`I` to a sparser set. The proof argues by contradiction via the *I-component* partition
(`SimpleGraph.maxBlock` from the previous section): if no augmentation exists, every
`e ∈ J \ I` forces its endpoints into a (non-trivial) I-component, which then accounts
for `e`. J-sparsity at each I-component vs I-tightness at the same component bounds the
J-edge count from above by the I-edge count; the free edges (no endpoints in any
I-component) on the J-side embed into the I-side; summing gives `|J| ≤ |I|`. -/

section Augmentation

variable [Finite V]

/-- **Off-diagonality of edges gives `u ≠ v`.** Convenience unfold of
`(⊤ : SimpleGraph V).edgeSet = Sym2.diagSetᶜ` at a pair edge. -/
private lemma ne_of_mem_top_edgeSet {V : Type*} {u v : V}
    (he : s(u, v) ∈ (⊤ : SimpleGraph V).edgeSet) : u ≠ v := by
  rw [edgeSet_top, Set.mem_compl_iff, Sym2.mem_diagSet, Sym2.mk_isDiag_iff] at he
  exact he

/-- **`(fromEdgeSet I).edgeSet = I` for off-diagonal `I`.** -/
private lemma edgeSet_fromEdgeSet_of_off_diag {V : Type*} {I : Set (Sym2 V)}
    (hI_off : I ⊆ (⊤ : SimpleGraph V).edgeSet) :
    (fromEdgeSet I).edgeSet = I := by
  rw [edgeSet_fromEdgeSet, sdiff_eq_left, Set.disjoint_left]
  intro e he_I he_diag
  have he_off : e ∈ Sym2.diagSetᶜ := edgeSet_top (V := V) ▸ hI_off he_I
  exact he_off he_diag

/-- **Matroid augmentation in the matroidal regime.** For finite `V` and `ℓ < 2 * k`,
if `I, J ⊆ E(K_V)` are both `(k, ℓ)`-sparse with `|I| < |J|`, then some `e ∈ J \ I`
extends `I` to a `(k, ℓ)`-sparse edge set: `(fromEdgeSet (insert e I)).IsSparse k ℓ`.

The combinatorial axiom of the `(k, ℓ)`-count matroid (Whiteley 1996, Lee–Streinu 2008).
Proof via the I-component decomposition: assuming no augmentation, every `e ∈ J \ I` is
forced into a component (`SimpleGraph.maxBlock` of its endpoints), and the partition
identity `|J| = ∑_C |edgesIn(J) C| + |J_free| ≤ ∑_C |edgesIn(I) C| + |I_free| = |I|`
contradicts `|I| < |J|`. -/
theorem IsSparse.exists_aug_of_lt_two_mul {k ℓ : ℕ} (hℓ : ℓ < 2 * k)
    {I J : Set (Sym2 V)} (hI : (fromEdgeSet I).IsSparse k ℓ)
    (hJ : (fromEdgeSet J).IsSparse k ℓ)
    (hI_off : I ⊆ (⊤ : SimpleGraph V).edgeSet)
    (hJ_off : J ⊆ (⊤ : SimpleGraph V).edgeSet)
    (hcard : I.ncard < J.ncard) :
    ∃ e ∈ J \ I, (fromEdgeSet (insert e I)).IsSparse k ℓ := by
  by_contra h_no_aug
  push Not at h_no_aug
  -- Setup: V is a Fintype, top.edgeSet is finite, so I, J are finite.
  letI : Fintype V := Fintype.ofFinite V
  classical
  have h_top_fin : ((⊤ : SimpleGraph V).edgeSet).Finite := (⊤ : SimpleGraph V).edgeSet.toFinite
  have hI_fin : I.Finite := h_top_fin.subset hI_off
  have hJ_fin : J.Finite := h_top_fin.subset hJ_off
  -- (Step 1) For each e ∈ J \ I, the I-component `maxBlock e.toFinset` is well-defined.
  -- `hBlock e he_diff : HasBlock e.toFinset`.
  have hBlock : ∀ {e : Sym2 V}, e ∈ J \ I → (fromEdgeSet I).HasBlock k ℓ e.toFinset := by
    intro e ⟨he_J, he_I⟩
    induction e with | h u v => ?_
    rw [Sym2.toFinset_mk_eq]
    have huv : u ≠ v := ne_of_mem_top_edgeSet (hJ_off he_J)
    obtain ⟨S, hu_S, hv_S, hS_tight⟩ :=
      hI.exists_isTightOn_of_insert_not_sparse huv he_I (h_no_aug s(u, v) ⟨he_J, he_I⟩)
    refine ⟨S, hS_tight, ?_⟩
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  -- Anchor finset of an edge: `{u, v}` for `e = s(u, v)`. Has card 2 off-diag.
  have h_toFinset_card_two : ∀ {e : Sym2 V}, e ∈ J \ I → 2 ≤ e.toFinset.card := by
    intro e he_diff
    have he_off : e ∈ (⊤ : SimpleGraph V).edgeSet := hJ_off he_diff.1
    rw [edgeSet_top, Set.mem_compl_iff] at he_off
    rw [Sym2.card_toFinset_of_not_isDiag e (fun h => he_off (Sym2.mem_diagSet.mpr h))]
  -- (Step 2) Comps: the Finset of distinct I-components of edges in J \ I.
  -- Using J as the indexing source; for e ∉ J\I we'll see this never matters.
  have hdiff_fin : (J \ I).Finite := hJ_fin.subset Set.diff_subset
  set diff_fin : Finset (Sym2 V) := hdiff_fin.toFinset with hdiff_def
  set Comps : Finset (Finset V) :=
    diff_fin.image (fun e => (fromEdgeSet I).maxBlock k ℓ e.toFinset) with hComps_def
  have hmem_diff : ∀ {e : Sym2 V}, e ∈ diff_fin ↔ e ∈ J \ I := by
    intro e; rw [hdiff_def]; exact Set.Finite.mem_toFinset _
  -- (Step 3) Each C ∈ Comps is I-tight (non-empty), has |C| ≥ 2.
  have hC_tight : ∀ C ∈ Comps, (fromEdgeSet I).IsTightOn k ℓ C := by
    intro C hC
    rw [hComps_def, Finset.mem_image] at hC
    obtain ⟨e, he_diff, rfl⟩ := hC
    rw [hmem_diff] at he_diff
    exact hI.maxBlock_isTightOn hℓ (h_toFinset_card_two he_diff) (hBlock he_diff)
  have hC_card_two : ∀ C ∈ Comps, 2 ≤ C.card := by
    intro C hC
    rw [hComps_def, Finset.mem_image] at hC
    obtain ⟨e, he_diff, rfl⟩ := hC
    rw [hmem_diff] at he_diff
    -- maxBlock contains the anchor, which has card 2.
    have h_anchor_sub : e.toFinset ⊆ (fromEdgeSet I).maxBlock k ℓ e.toFinset :=
      subset_maxBlock_of_hasBlock (hBlock he_diff)
    exact (h_toFinset_card_two he_diff).trans (Finset.card_le_card h_anchor_sub)
  -- (Step 4) Edge-disjointness: every off-diag e ∈ K_V is in at most one C ∈ Comps,
  -- where "e is in C" means `e.toFinset ⊆ C`.
  have h_edge_uniq : ∀ {e : Sym2 V}, e ∈ (⊤ : SimpleGraph V).edgeSet →
      ∀ C₁ ∈ Comps, ∀ C₂ ∈ Comps,
        e.toFinset ⊆ C₁ → e.toFinset ⊆ C₂ → C₁ = C₂ := by
    intro e he_top C₁ hC₁ C₂ hC₂ h1 h2
    -- Both C₁ and C₂ are maxBlocks; e.toFinset ⊆ both ∩ has card 2.
    rw [hComps_def, Finset.mem_image] at hC₁ hC₂
    obtain ⟨e₁, he₁_diff, rfl⟩ := hC₁
    obtain ⟨e₂, he₂_diff, rfl⟩ := hC₂
    rw [hmem_diff] at he₁_diff he₂_diff
    -- Reduce both equalities to `maxBlock e.toFinset`.
    have he_card_two : 2 ≤ e.toFinset.card := by
      rw [edgeSet_top, Set.mem_compl_iff] at he_top
      rw [Sym2.card_toFinset_of_not_isDiag e (fun h => he_top (Sym2.mem_diagSet.mpr h))]
    have h_eq₁ : (fromEdgeSet I).maxBlock k ℓ e.toFinset
        = (fromEdgeSet I).maxBlock k ℓ e₁.toFinset :=
      hI.maxBlock_eq_of_subset_maxBlock hℓ (h_toFinset_card_two he₁_diff) he_card_two
        (hBlock he₁_diff) h1
    have h_eq₂ : (fromEdgeSet I).maxBlock k ℓ e.toFinset
        = (fromEdgeSet I).maxBlock k ℓ e₂.toFinset :=
      hI.maxBlock_eq_of_subset_maxBlock hℓ (h_toFinset_card_two he₂_diff) he_card_two
        (hBlock he₂_diff) h2
    rw [← h_eq₁, ← h_eq₂]
  -- (Step 5) "edgesIn(fromEdgeSet X) C = X ∩ (↑C).sym2" for X off-diag.
  have h_edgesIn_eq : ∀ {X : Set (Sym2 V)}, X ⊆ (⊤ : SimpleGraph V).edgeSet →
      ∀ (S : Set V), (fromEdgeSet X).edgesIn S = X ∩ S.sym2 := by
    intro X hX S
    unfold edgesIn
    rw [edgeSet_fromEdgeSet_of_off_diag hX]
  -- (Step 6) Partition pieces and disjointness.
  -- The "components piece" for X: ⋃_{C ∈ Comps} X ∩ ↑C.sym2.
  -- For e off-diag in C.sym2, e.toFinset ⊆ C.
  have h_toFinset_sub_iff : ∀ {e : Sym2 V} {C : Finset V},
      e ∈ (⊤ : SimpleGraph V).edgeSet → (e ∈ ((↑C : Set V).sym2) ↔ e.toFinset ⊆ C) := by
    intro e C _
    rw [Set.mem_sym2_iff_subset]
    constructor
    · intro h_sub x hx
      rw [Sym2.mem_toFinset] at hx
      exact_mod_cast h_sub hx
    · intro h_sub x hx
      exact_mod_cast h_sub (Sym2.mem_toFinset.mpr hx)
  -- The components partition: pairwise disjoint X ∩ ↑C.sym2.
  have h_pairwiseDisjoint : ∀ {X : Set (Sym2 V)}, X ⊆ (⊤ : SimpleGraph V).edgeSet →
      (↑Comps : Set (Finset V)).PairwiseDisjoint (fun C : Finset V => X ∩ (↑C : Set V).sym2) := by
    intro X hX C₁ hC₁ C₂ hC₂ hC12
    refine Set.disjoint_left.mpr ?_
    intro e ⟨he_X, he_C₁⟩ ⟨_, he_C₂⟩
    refine hC12 ?_
    have he_top := hX he_X
    have h1 := (h_toFinset_sub_iff he_top).mp he_C₁
    have h2 := (h_toFinset_sub_iff he_top).mp he_C₂
    exact h_edge_uniq he_top C₁ hC₁ C₂ hC₂ h1 h2
  -- (Step 7) For each C ∈ Comps: J-card on C ≤ I-card on C (I-tightness + J-sparsity).
  have h_C_ineq : ∀ C ∈ Comps,
      (J ∩ (↑C : Set V).sym2).ncard ≤ (I ∩ (↑C : Set V).sym2).ncard := by
    intro C hC
    have hC_I_tight := hC_tight C hC
    have hC_size : ℓ ≤ k * C.card := by unfold IsTightOn at hC_I_tight; omega
    have hC_J_sparse := hJ C hC_size
    rw [h_edgesIn_eq hJ_off (↑C : Set V)] at hC_J_sparse
    rw [← h_edgesIn_eq hI_off (↑C : Set V)]
    unfold IsTightOn at hC_I_tight
    omega
  -- (Step 8) Decompose I and J into "in some component" + "free", and count.
  -- For X (= I or J), Xfree := X \ ⋃_{C ∈ Comps} (↑C).sym2.
  set CompsUnion : Set (Sym2 V) :=
    ⋃ (C : Finset V) (_ : C ∈ Comps), ((↑C : Set V).sym2) with hCU_def
  -- (Step 8a) Partition each X = (X ∩ CompsUnion) ⊔ (X \ CompsUnion).
  have h_split : ∀ {X : Set (Sym2 V)}, X.Finite →
      X.ncard = (X ∩ CompsUnion).ncard + (X \ CompsUnion).ncard := fun {X} hX_fin =>
    (Set.ncard_inter_add_ncard_diff_eq_ncard X CompsUnion hX_fin).symm
  -- (Step 8b) X ∩ CompsUnion = ⋃_C (X ∩ ↑C.sym2); pairwise disjoint by edge-uniqueness.
  -- Therefore (X ∩ CompsUnion).ncard = ∑_C (X ∩ ↑C.sym2).ncard.
  have h_compsUnion_ncard : ∀ {X : Set (Sym2 V)}, X ⊆ (⊤ : SimpleGraph V).edgeSet → X.Finite →
      (X ∩ CompsUnion).ncard = ∑ C ∈ Comps, (X ∩ (↑C : Set V).sym2).ncard := by
    intro X hX hX_fin
    have h_inter_iUnion : X ∩ CompsUnion =
        ⋃ C ∈ (↑Comps : Set (Finset V)), X ∩ (↑C : Set V).sym2 := by
      rw [hCU_def]
      ext e
      simp only [Set.mem_inter_iff, Set.mem_iUnion, Finset.mem_coe]
      tauto
    rw [h_inter_iUnion]
    have h_pd : (↑Comps : Set (Finset V)).PairwiseDisjoint
        (fun C : Finset V => X ∩ (↑C : Set V).sym2) := h_pairwiseDisjoint hX
    have h_finset_fin : Set.Finite (↑Comps : Set (Finset V)) := Comps.finite_toSet
    have h_each_fin : ∀ C ∈ (↑Comps : Set (Finset V)), (X ∩ (↑C : Set V).sym2).Finite :=
      fun _ _ => hX_fin.subset Set.inter_subset_left
    rw [Set.Finite.ncard_biUnion h_finset_fin h_each_fin h_pd, finsum_mem_coe_finset]
  -- (Step 8c) The free part: every e ∈ J \ CompsUnion lies in I (and outside CompsUnion).
  -- Because every e ∈ J \ I would (by contradiction hypothesis) be inside some I-component.
  have h_free_sub : J \ CompsUnion ⊆ I \ CompsUnion := by
    intro e ⟨he_J, he_notIn⟩
    refine ⟨?_, he_notIn⟩
    by_contra he_notI
    -- e ∈ J \ I, so e.toFinset ⊆ maxBlock e.toFinset ∈ Comps, so e ∈ ↑C.sym2 ⊆ CompsUnion.
    have he_diff : e ∈ J \ I := ⟨he_J, he_notI⟩
    have h_block := hBlock he_diff
    have h_sub : e.toFinset ⊆ (fromEdgeSet I).maxBlock k ℓ e.toFinset :=
      subset_maxBlock_of_hasBlock h_block
    have he_top : e ∈ (⊤ : SimpleGraph V).edgeSet := hJ_off he_J
    have he_in : e ∈ (↑((fromEdgeSet I).maxBlock k ℓ e.toFinset) : Set V).sym2 :=
      (h_toFinset_sub_iff he_top).mpr h_sub
    apply he_notIn
    rw [hCU_def]
    refine Set.mem_iUnion.mpr ⟨(fromEdgeSet I).maxBlock k ℓ e.toFinset, ?_⟩
    refine Set.mem_iUnion.mpr ⟨?_, he_in⟩
    rw [hComps_def]
    refine Finset.mem_image.mpr ⟨e, ?_, rfl⟩
    rw [hmem_diff]; exact he_diff
  -- (Step 9) Assemble: |J| ≤ |I|.
  have hI_compsUnion := h_compsUnion_ncard hI_off hI_fin
  have hJ_compsUnion := h_compsUnion_ncard hJ_off hJ_fin
  have hJ_split := h_split hJ_fin
  have hI_split := h_split hI_fin
  have h_diff_le : (J \ CompsUnion).ncard ≤ (I \ CompsUnion).ncard :=
    Set.ncard_le_ncard h_free_sub (hI_fin.subset Set.diff_subset)
  have h_sum_le : ∑ C ∈ Comps, (J ∩ (↑C : Set V).sym2).ncard ≤
      ∑ C ∈ Comps, (I ∩ (↑C : Set V).sym2).ncard :=
    Finset.sum_le_sum h_C_ineq
  have h_total : J.ncard ≤ I.ncard := by
    rw [hJ_split, hI_split, hJ_compsUnion, hI_compsUnion]
    exact Nat.add_le_add h_sum_le h_diff_le
  omega

end Augmentation

end SimpleGraph
