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

end SimpleGraph
