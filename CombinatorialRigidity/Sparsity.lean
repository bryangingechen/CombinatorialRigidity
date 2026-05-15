/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.EdgesIn
import CombinatorialRigidity.Mathlib.Combinatorics.SimpleGraph.Finite
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

end SimpleGraph
