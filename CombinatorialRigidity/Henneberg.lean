/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Laman
import CombinatorialRigidity.Mathlib.Data.Finset.Card
import CombinatorialRigidity.Mathlib.Data.Finset.Option
import CombinatorialRigidity.Mathlib.Data.Set.Card
import CombinatorialRigidity.Mathlib.Data.Sym.Sym2
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finite.Card
import Mathlib.Logic.Equiv.Option

/-!
# Henneberg moves

Two vertex-extension operations on simple graphs that, iterated from `K₂`,
construct exactly the Laman graphs (Henneberg's theorem; future work).

* **Type I** adds a fresh vertex of degree 2 joined to two existing
  vertices `a` and `b`.
* **Type II** deletes an edge `{a, b}` and adds a fresh vertex of degree 3
  joined to `a`, `b`, and a third existing vertex `c`.

The fresh vertex is represented as `none : Option V`, with old vertices
embedded via `some`. This is mathlib's canonical "add one element" idiom
(cf. `Equiv.optionEquivSumPUnit`); it avoids a freshness side-condition on
every move and keeps the type signatures readable.

## Main definitions

* `SimpleGraph.Henneberg.typeI G a b : SimpleGraph (Option V)`.
* `SimpleGraph.Henneberg.typeII G a b c : SimpleGraph (Option V)`.

## Project context

See `ROADMAP.md` for the project plan and `notes/Phase3.md` for the
Phase 3 work log.
-/

namespace SimpleGraph

variable {V : Type*}

namespace Henneberg

/-- The **Type I Henneberg move**: extend `G : SimpleGraph V` by a fresh vertex
of degree 2 joined to two existing vertices `a` and `b`. The output graph lives
on `Option V`, with the new vertex represented as `none`.

When `a = b`, the new vertex has degree 1 (the parallel edges collapse); the
move preserves the Laman property only under `a ≠ b`. -/
def typeI (G : SimpleGraph V) (a b : V) : SimpleGraph (Option V) where
  Adj
    | some u, some v => G.Adj u v
    | some u, none => u = a ∨ u = b
    | none, some v => v = a ∨ v = b
    | none, none => False
  symm := by
    rintro (_ | u) (_ | v) h
    · exact h
    · exact h
    · exact h
    · exact h.symm
  loopless := ⟨fun
    | none => id
    | some u => G.loopless.irrefl u⟩

/-- The **Type II Henneberg move**: extend `G : SimpleGraph V` by deleting the
edge `s(a, b)` and adding a fresh vertex of degree 3 joined to `a`, `b`, and a
third vertex `c`. The output graph lives on `Option V`.

The move is well-defined for any `a b c : V`. It preserves the Laman property
only under `a ≠ b`, `c ≠ a`, `c ≠ b`, and `G.Adj a b`. -/
def typeII (G : SimpleGraph V) (a b c : V) : SimpleGraph (Option V) where
  Adj
    | some u, some v => G.Adj u v ∧ s(u, v) ≠ s(a, b)
    | some u, none => u = a ∨ u = b ∨ u = c
    | none, some v => v = a ∨ v = b ∨ v = c
    | none, none => False
  symm := by
    rintro (_ | u) (_ | v) h
    · exact h
    · exact h
    · exact h
    · exact ⟨h.1.symm, fun heq => h.2 (Sym2.eq_swap.trans heq)⟩
  loopless := ⟨fun
    | none => id
    | some u => fun h => G.loopless.irrefl u h.1⟩

/-! ### Adjacency unfolding -/

variable {G : SimpleGraph V} {a b c u v : V}

@[simp] lemma typeI_adj_some_some : (typeI G a b).Adj (some u) (some v) ↔ G.Adj u v := Iff.rfl

@[simp] lemma typeI_adj_some_none : (typeI G a b).Adj (some u) none ↔ u = a ∨ u = b := Iff.rfl

@[simp] lemma typeI_adj_none_some : (typeI G a b).Adj none (some v) ↔ v = a ∨ v = b := Iff.rfl

lemma typeI_not_adj_none_none : ¬ (typeI G a b).Adj none none := id

@[simp] lemma typeII_adj_some_some :
    (typeII G a b c).Adj (some u) (some v) ↔ G.Adj u v ∧ s(u, v) ≠ s(a, b) := Iff.rfl

@[simp] lemma typeII_adj_some_none :
    (typeII G a b c).Adj (some u) none ↔ u = a ∨ u = b ∨ u = c := Iff.rfl

@[simp] lemma typeII_adj_none_some :
    (typeII G a b c).Adj none (some v) ↔ v = a ∨ v = b ∨ v = c := Iff.rfl

lemma typeII_not_adj_none_none : ¬ (typeII G a b c).Adj none none := id

instance instDecidableTypeIAdj [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : V) : DecidableRel (typeI G a b).Adj := fun u v =>
  match u, v with
  | some u, some v => (inferInstance : Decidable (G.Adj u v))
  | some u, none => (inferInstance : Decidable (u = a ∨ u = b))
  | none, some v => (inferInstance : Decidable (v = a ∨ v = b))
  | none, none => instDecidableFalse

instance instDecidableTypeIIAdj [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b c : V) : DecidableRel (typeII G a b c).Adj := fun u v =>
  match u, v with
  | some u, some v => (inferInstance : Decidable (G.Adj u v ∧ s(u, v) ≠ s(a, b)))
  | some u, none => (inferInstance : Decidable (u = a ∨ u = b ∨ u = c))
  | none, some v => (inferInstance : Decidable (v = a ∨ v = b ∨ v = c))
  | none, none => instDecidableFalse

/-! ### Sparsity helpers for the `_isLaman` proofs

`typeI_isLaman` and `typeII_isLaman` decompose `(typeI/II _).edgesIn ↑s` into "old" edges (image
under `some`) plus the subset of fresh edges (each of the form `s(none, some _)`) that lie in
`s.sym2`. The three helpers below isolate the recurring set-cardinality steps used in the
sparsity case analysis. They are stated against `s.eraseNone` (mathlib's name for the
some-preimage of a `Finset (Option V)`) so callers can pass the produced equalities /
non-memberships directly. -/

/-- If `none ∉ s`, no fresh edge `s(none, some _)` lies in `s.sym2`, so any subset of fresh edges
intersected with `s.sym2` has cardinality `0`. -/
private lemma fresh_sym2_ncard_eq_zero_of_none_notMem [Finite V] {s : Finset (Option V)}
    (hnone : none ∉ s) (xs : Set (Sym2 (Option V))) (h_xs : ∀ e ∈ xs, none ∈ e) :
    (xs ∩ ((↑s : Set (Option V)).sym2)).ncard = 0 := by
  rw [Set.ncard_eq_zero, Set.eq_empty_iff_forall_notMem]
  rintro e ⟨he, hsub⟩
  exact hnone (Set.mem_sym2_iff_subset.mp hsub (h_xs e he))

/-- If `s.eraseNone = {w}`, every fresh edge `s(none, some x)` that lies in `s.sym2` satisfies
`x = w`, so the intersection with `s.sym2` is contained in `{s(none, some w)}`. -/
private lemma fresh_sym2_subset_singleton {s : Finset (Option V)} {w : V}
    (hw : s.eraseNone = {w})
    (xs : Set (Sym2 (Option V))) (h_xs : ∀ e ∈ xs, ∃ x : V, e = s(none, some x)) :
    xs ∩ ((↑s : Set (Option V)).sym2) ⊆ ({s(none, some w)} : Set _) := by
  rintro e ⟨he, hsub⟩
  obtain ⟨x, rfl⟩ := h_xs e he
  rw [Set.mem_sym2_iff_subset, Sym2.coe_mk] at hsub
  have hx : x ∈ s.eraseNone := Finset.mem_eraseNone.mpr (hsub (Or.inr rfl))
  rw [hw, Finset.mem_singleton] at hx
  exact hx ▸ rfl

/-- The triple-fresh-edges intersection is bounded by `2` when at least one of the three vertices
sits outside `s.eraseNone`: that vertex's edge fails the `s.sym2` membership, leaving at most the
other two. -/
private lemma fresh_sym2_triple_inter_ncard_le_two {s : Finset (Option V)}
    {x y z : V} (hx : x ∉ s.eraseNone) :
    (({s(none, some x), s(none, some y), s(none, some z)} : Set _) ∩
        ((↑s : Set (Option V)).sym2)).ncard ≤ 2 := by
  refine (Set.ncard_le_ncard (?_ : _ ⊆
      ({s(none, some y), s(none, some z)} : Set _))).trans (Set.ncard_pair_le _ _)
  rintro e ⟨hpair, hsub⟩
  have hsubV : (e : Set (Option V)) ⊆ ↑s := Set.mem_sym2_iff_subset.mp hsub
  rcases hpair with rfl | rfl | rfl
  · exact (hx (Finset.mem_eraseNone.mpr (hsubV (by simp)))).elim
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ rfl

/-! ### Edge set of `typeI`

The edge set of `typeI G a b` decomposes into the image of `G.edgeSet` under `some` plus the two
new edges joining `none` to `some a` and `some b`. -/

/-- Edge set of `typeI G a b`: the old edges (image of `G.edgeSet` under `some`) together with the
two new edges joining `none` to `some a` and `some b`. -/
lemma typeI_edgeSet (G : SimpleGraph V) (a b : V) :
    (typeI G a b).edgeSet =
      (Sym2.map some '' G.edgeSet) ∪ {s(none, some a), s(none, some b)} := by
  ext e
  induction e with | h x y => ?_
  rcases x with _ | u <;> rcases y with _ | v <;> simp

/-- Cardinality of `typeI G a b`'s edge set: under `a ≠ b`, two new edges are added. -/
lemma typeI_edgeSet_ncard [Finite V] (G : SimpleGraph V) {a b : V} (hab : a ≠ b) :
    ((typeI G a b).edgeSet).ncard = G.edgeSet.ncard + 2 := by
  have hDisj : Disjoint (Sym2.map some '' G.edgeSet)
      ({s(none, some a), s(none, some b)} : Set (Sym2 (Option V))) :=
    Sym2.disjoint_image_map_some (by rintro e (rfl | rfl) <;> simp)
  rw [typeI_edgeSet, Set.ncard_union_eq hDisj,
    Set.ncard_image_of_injective _ Sym2.map_some_injective, Set.ncard_pair (by simp [hab])]

/-- Cardinality decomposition of `(typeI G a b).edgesIn ↑s`: the old `G`-edges with both endpoints
in `s.eraseNone`, plus the fresh edges `{s(none, some a), s(none, some b)}` that lie in `↑s`. The
two summands are disjoint by `Sym2.disjoint_image_map_some`. -/
private lemma typeI_edgesIn_ncard_decomp [Finite V] (G : SimpleGraph V) (a b : V)
    (s : Finset (Option V)) :
    ((typeI G a b).edgesIn (↑s : Set (Option V))).ncard =
      (G.edgesIn (↑s.eraseNone : Set V)).ncard +
      (({s(none, some a), s(none, some b)} : Set (Sym2 (Option V))) ∩
        ((↑s : Set (Option V)).sym2)).ncard := by
  set T : Set (Sym2 (Option V)) :=
    ({s(none, some a), s(none, some b)} : Set _) ∩ ((↑s : Set (Option V)).sym2)
  have h_decomp : (typeI G a b).edgesIn (↑s : Set (Option V)) =
      Sym2.map some '' G.edgesIn (↑s.eraseNone : Set V) ∪ T := by
    ext e
    induction e with | h x y => ?_
    rcases x with _ | u <;> rcases y with _ | v <;> simp [edgesIn, T]
  have h_disj : Disjoint (Sym2.map some '' G.edgesIn (↑s.eraseNone : Set V)) T :=
    Sym2.disjoint_image_map_some fun _ ⟨hpair, _⟩ => by rcases hpair with rfl | rfl <;> simp
  rw [h_decomp, Set.ncard_union_eq h_disj,
    Set.ncard_image_of_injective _ Sym2.map_some_injective]

/-! ### Type I preserves the Laman property -/

/-- The Type I Henneberg move preserves the Laman property: if `G` is Laman and `a ≠ b`, then
`typeI G a b` is Laman. Tightness follows from `typeI_edgeSet_ncard` and `Finite.card_option`;
sparsity is by case analysis on `none ∈ s` and on the cardinality of `s.eraseNone` (the
some-preimage `s'`). -/
theorem typeI_isLaman [Finite V] {G : SimpleGraph V} (h : G.IsLaman)
    {a b : V} (hab : a ≠ b) : (typeI G a b).IsLaman := by
  have : Fintype V := Fintype.ofFinite V
  refine ⟨fun s hs_pre => ?_, ?_⟩
  · -- Sparsity. `s' := s.eraseNone` is the some-preimage; `T` is the fresh edges in `↑s`.
    set s' : Finset V := s.eraseNone
    set T : Set (Sym2 (Option V)) :=
      ({s(none, some a), s(none, some b)} : Set _) ∩ ((↑s : Set (Option V)).sym2)
    have h_ncard : ((typeI G a b).edgesIn (↑s : Set (Option V))).ncard =
        (G.edgesIn (↑s' : Set V)).ncard + T.ncard :=
      typeI_edgesIn_ncard_decomp G a b s
    have hT_le_2 : T.ncard ≤ 2 :=
      (Set.ncard_le_ncard Set.inter_subset_left).trans (Set.ncard_pair_le _ _)
    -- Case-split on whether `none ∈ s`.
    by_cases hnone : none ∈ s
    · -- Case `none ∈ s`. Then `s.card = s'.card + 1`.
      have hsc : s.card = s'.card + 1 := (Finset.card_eraseNone_add_one_of_mem hnone).symm
      -- Sub-case on `s'.card`: 0 (vacuous), 1 (singleton), ≥ 2 (use sparsity).
      rcases (show s'.card = 0 ∨ s'.card = 1 ∨ 2 ≤ s'.card from by omega)
        with h0 | h1 | hge
      · -- s'.card = 0: precondition fails (`s.card = 1`).
        omega
      · -- s'.card = 1: `s' = {w}`. Then `(G.edgesIn ↑s').ncard = 0` and `T.ncard ≤ 1`.
        obtain ⟨w, hw⟩ : ∃ w, s' = {w} := Finset.card_eq_one.mp h1
        have hG_empty : (G.edgesIn (↑s' : Set V)).ncard = 0 := by rw [hw]; simp
        have hT_sub : T ⊆ ({s(none, some w)} : Set _) :=
          fresh_sym2_subset_singleton hw _
            (by rintro e (rfl | rfl) <;> exact ⟨_, rfl⟩)
        have hT_le_1 : T.ncard ≤ 1 :=
          (Set.ncard_le_ncard hT_sub).trans (le_of_eq (Set.ncard_singleton _))
        omega
      · -- s'.card ≥ 2: apply `G`'s sparsity on `s'`.
        have hG := h.isSparse s' (by omega)
        omega
    · -- Case `none ∉ s`. Then `T.ncard = 0` and `s.card = s'.card`.
      have hsc : s.card = s'.card := (Finset.card_eraseNone_of_not_mem hnone).symm
      have hT_empty : T.ncard = 0 :=
        fresh_sym2_ncard_eq_zero_of_none_notMem hnone _ (by rintro e (rfl | rfl) <;> simp)
      have hG := h.isSparse s' (by omega)
      omega
  · -- Tightness.
    grind only [!typeI_edgeSet_ncard, !Finite.card_option, h.edgeSet_ncard]

/-- Inverse of `typeI_isLaman`: if a Type I move on `G` produces a Laman graph (with the two
existing endpoints `a ≠ b` distinct), then `G` itself is Laman. The two facts together give
`typeI_isLaman_iff` below.

The proof is dual to `typeI_isLaman` and reuses `typeI_edgesIn_ncard_decomp`: an arbitrary
`s' : Finset V` lifts to `s := s'.image some : Finset (Option V)`, where `none ∉ s` collapses the
fresh-edge contribution to zero and the edges-in count of `(typeI G a b)` on `s` equals that of `G`
on `s'`. -/
theorem typeI_reverse_isLaman [Finite V] {G : SimpleGraph V} {a b : V} (hab : a ≠ b)
    (h : (typeI G a b).IsLaman) : G.IsLaman := by
  classical
  refine ⟨fun s' hs' => ?_, ?_⟩
  · -- Sparsity. Lift `s'` to `s := s'.image some` and apply `(typeI G a b)`'s sparsity there.
    set s : Finset (Option V) := s'.image some
    have hs_card : s.card = s'.card :=
      Finset.card_image_of_injective s' (Option.some_injective _)
    have hnone : none ∉ s := by simp [s]
    have hT_zero : (({s(none, some a), s(none, some b)} : Set (Sym2 (Option V))) ∩
        ((↑s : Set (Option V)).sym2)).ncard = 0 :=
      fresh_sym2_ncard_eq_zero_of_none_notMem hnone _ (by rintro e (rfl | rfl) <;> simp)
    have h_decomp := typeI_edgesIn_ncard_decomp G a b s
    rw [Finset.eraseNone_image_some, hT_zero, add_zero] at h_decomp
    have hsparse := h.isSparse s (by rw [hs_card]; exact hs')
    rw [h_decomp, hs_card] at hsparse
    exact hsparse
  · -- Tightness.
    grind only [!typeI_edgeSet_ncard, !Finite.card_option, h.edgeSet_ncard]

/-- The Type I Henneberg move and its underlying graph are simultaneously Laman: under `a ≠ b`,
`(typeI G a b).IsLaman ↔ G.IsLaman`. -/
theorem typeI_isLaman_iff [Finite V] {G : SimpleGraph V} {a b : V} (hab : a ≠ b) :
    (typeI G a b).IsLaman ↔ G.IsLaman :=
  ⟨typeI_reverse_isLaman hab, fun h => typeI_isLaman h hab⟩

/-! ### Edge set of `typeII`

The edge set of `typeII G a b c` decomposes into the image of `G.edgeSet \ {s(a, b)}` under `some`
plus the three new edges joining `none` to `some a`, `some b`, and `some c`. -/

/-- Edge set of `typeII G a b c`: the old edges other than `s(a, b)` (image under `some`) together
with the three new edges joining `none` to `some a`, `some b`, and `some c`. -/
lemma typeII_edgeSet (G : SimpleGraph V) (a b c : V) :
    (typeII G a b c).edgeSet =
      (Sym2.map some '' (G.edgeSet \ {s(a, b)})) ∪
        {s(none, some a), s(none, some b), s(none, some c)} := by
  ext e
  induction e with | h x y => ?_
  rcases x with _ | u <;> rcases y with _ | v <;> simp

/-- Cardinality of `typeII G a b c`'s edge set: the deletion-then-`+3-new-edges` arithmetic. The
hypotheses force the three new edges to be pairwise distinct; the deletion is recorded in the
right-hand side as `G.edgeSet \ {s(a, b)}`, so this lemma does not assume `G.Adj a b`. -/
lemma typeII_edgeSet_ncard [Finite V] (G : SimpleGraph V) {a b c : V}
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    ((typeII G a b c).edgeSet).ncard = (G.edgeSet \ {s(a, b)}).ncard + 3 := by
  have hDisj : Disjoint (Sym2.map some '' (G.edgeSet \ {s(a, b)}))
      ({s(none, some a), s(none, some b), s(none, some c)} :
        Set (Sym2 (Option V))) :=
    Sym2.disjoint_image_map_some (by rintro e (rfl | rfl | rfl) <;> simp)
  rw [typeII_edgeSet, Set.ncard_union_eq hDisj,
    Set.ncard_image_of_injective _ Sym2.map_some_injective,
    Set.ncard_insert_of_notMem (by simp [hab, hca.symm]) (by simp),
    Set.ncard_pair (by simp [hcb.symm])]

/-- Cardinality decomposition of `(typeII G a b c).edgesIn ↑s`: the old `G`-edges (less `s(a, b)`)
with both endpoints in `s.eraseNone`, plus the fresh edges
`{s(none, some a), s(none, some b), s(none, some c)}` that lie in `↑s`. The two summands are
disjoint by `Sym2.disjoint_image_map_some`. -/
private lemma typeII_edgesIn_ncard_decomp [Finite V] (G : SimpleGraph V) (a b c : V)
    (s : Finset (Option V)) :
    ((typeII G a b c).edgesIn (↑s : Set (Option V))).ncard =
      (G.edgesIn (↑s.eraseNone : Set V) \ {s(a, b)}).ncard +
      (({s(none, some a), s(none, some b), s(none, some c)} : Set (Sym2 (Option V))) ∩
        ((↑s : Set (Option V)).sym2)).ncard := by
  set T' : Set (Sym2 (Option V)) :=
    ({s(none, some a), s(none, some b), s(none, some c)} : Set _) ∩
      ((↑s : Set (Option V)).sym2)
  have h_decomp : (typeII G a b c).edgesIn (↑s : Set (Option V)) =
      Sym2.map some '' (G.edgesIn (↑s.eraseNone : Set V) \ {s(a, b)}) ∪ T' := by
    ext e
    induction e with | h x y => ?_
    rcases x with _ | u <;> rcases y with _ | v <;>
      (simp [edgesIn, T']; try tauto)
  have h_disj : Disjoint (Sym2.map some '' (G.edgesIn (↑s.eraseNone : Set V) \ {s(a, b)})) T' :=
    Sym2.disjoint_image_map_some
      fun _ ⟨hpair, _⟩ => by rcases hpair with rfl | rfl | rfl <;> simp
  rw [h_decomp, Set.ncard_union_eq h_disj,
    Set.ncard_image_of_injective _ Sym2.map_some_injective]

/-! ### Type II preserves the Laman property -/

/-- The Type II Henneberg move preserves the Laman property: if `G` is Laman, `a, b, c` are
pairwise distinct, and `G.Adj a b`, then `typeII G a b c` is Laman. The proof structure mirrors
`typeI_isLaman`; the main wrinkle is that the deletion of `s(a, b)` interacts with the new edges,
but a uniform `+ 2` bound holds: either `s(a, b)` was inside `G.edgesIn ↑s'` (loses 1, gains up
to 3), or it wasn't (loses 0, but then one of `a, b` is outside `s'` so gains at most 2). -/
theorem typeII_isLaman [Finite V] {G : SimpleGraph V} (h : G.IsLaman) {a b c : V}
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) (hG_ab : G.Adj a b) :
    (typeII G a b c).IsLaman := by
  have : Fintype V := Fintype.ofFinite V
  refine ⟨fun s hs_pre => ?_, ?_⟩
  · -- Sparsity. `s' := s.eraseNone` is the some-preimage; `T'` is the fresh edges in `↑s`.
    set s' : Finset V := s.eraseNone
    set T' : Set (Sym2 (Option V)) :=
      ({s(none, some a), s(none, some b), s(none, some c)} : Set _) ∩
        ((↑s : Set (Option V)).sym2) with hT'_def
    have h_ncard : ((typeII G a b c).edgesIn (↑s : Set (Option V))).ncard =
        (G.edgesIn (↑s' : Set V) \ {s(a, b)}).ncard + T'.ncard :=
      typeII_edgesIn_ncard_decomp G a b c s
    have hT'_le_3 : T'.ncard ≤ 3 :=
      (Set.ncard_le_ncard Set.inter_subset_left).trans (Set.ncard_triple_le _ _ _)
    -- Case-split on whether `none ∈ s`.
    by_cases hnone : none ∈ s
    · -- Case `none ∈ s`. Then `s.card = s'.card + 1`.
      have hsc : s.card = s'.card + 1 := (Finset.card_eraseNone_add_one_of_mem hnone).symm
      -- Sub-case on `s'.card`.
      rcases (show s'.card = 0 ∨ s'.card = 1 ∨ 2 ≤ s'.card from by omega)
        with h0 | h1 | hge
      · omega -- vacuous: precondition fails
      · -- s'.card = 1: `s' = {w}`. Singleton means no `G`-edges; `T' ⊆ {s(none, some w)}`.
        obtain ⟨w, hw⟩ : ∃ w, s' = {w} := Finset.card_eq_one.mp h1
        have hG_empty : (G.edgesIn (↑s' : Set V) \ {s(a, b)}).ncard = 0 := by
          rw [hw]; simp
        have hT'_sub : T' ⊆ ({s(none, some w)} : Set _) :=
          fresh_sym2_subset_singleton hw _
            (by rintro e (rfl | rfl | rfl) <;> exact ⟨_, rfl⟩)
        have hT'_le_1 : T'.ncard ≤ 1 :=
          (Set.ncard_le_ncard hT'_sub).trans (le_of_eq (Set.ncard_singleton _))
        omega
      · -- s'.card ≥ 2: case-split on whether `s(a, b) ∈ G.edgesIn ↑s'`.
        have hG := h.isSparse s' (by omega)
        by_cases h_ab_in : s(a, b) ∈ G.edgesIn (↑s' : Set V)
        · -- `s(a, b) ∈ G.edgesIn ↑s'`: deletion removes one, `T'.ncard ≤ 3` works.
          have hdiff := Set.ncard_diff_singleton_of_mem h_ab_in (s := G.edgesIn (↑s' : Set V))
          have hG_ne_zero : (G.edgesIn (↑s' : Set V)).ncard ≠ 0 :=
            Set.ncard_ne_zero_of_mem h_ab_in
          omega
        · -- `s(a, b) ∉ G.edgesIn ↑s'`: deletion is a no-op, but `a ∉ s'` or `b ∉ s'`, so the
          -- corresponding new edge `s(none, some a)` or `s(none, some b)` is also missing.
          -- Hence `T'.ncard ≤ 2`.
          have hdiff : (G.edgesIn (↑s' : Set V) \ {s(a, b)}).ncard =
              (G.edgesIn (↑s' : Set V)).ncard := by
            rw [Set.diff_singleton_eq_self h_ab_in]
          -- Since `s(a, b) ∈ G.edgeSet` (from `hG_ab`) but not in `G.edgesIn ↑s'`,
          -- it must fail the subset condition: `a ∉ s'` or `b ∉ s'`.
          have h_or : a ∉ s' ∨ b ∉ s' := by
            by_contra h_both
            push Not at h_both
            exact h_ab_in (G.mk_mem_edgesIn hG_ab h_both.1 h_both.2)
          -- Then T'.ncard ≤ 2: whichever of `a, b` is not in `s'` contributes no edge to `T'`.
          -- For the `b ∉ s'` arm, reorder T' as `{s(none, some b), s(none, some a), …} ∩ s.sym2`
          -- (the underlying `Set` is unchanged) so the helper applies with `x = b`.
          have hT'_le_2 : T'.ncard ≤ 2 := by
            rcases h_or with ha | hb
            · exact fresh_sym2_triple_inter_ncard_le_two ha
            · rw [hT'_def, Set.insert_comm s(none, some a) s(none, some b)]
              exact fresh_sym2_triple_inter_ncard_le_two hb
          omega
    · -- Case `none ∉ s`. Then `T'.ncard = 0` and `s.card = s'.card`.
      have hsc : s.card = s'.card := (Finset.card_eraseNone_of_not_mem hnone).symm
      have hT'_empty : T'.ncard = 0 :=
        fresh_sym2_ncard_eq_zero_of_none_notMem hnone _ (by rintro e (rfl | rfl | rfl) <;> simp)
      have hG := h.isSparse s' (by omega)
      have hdiff_le : (G.edgesIn (↑s' : Set V) \ {s(a, b)}).ncard ≤
          (G.edgesIn (↑s' : Set V)).ncard :=
        Set.ncard_diff_singleton_le _ _
      omega
  · -- Tightness.
    have hab_in : s(a, b) ∈ G.edgeSet := hG_ab
    grind only [!typeII_edgeSet_ncard, !Finite.card_option,
      !Set.ncard_diff_singleton_of_mem, h.edgeSet_ncard]

/-! ### Decomposition iso constructors

`typeI_iso_of_two_neighbors` and `typeII_iso_of_three_neighbors` package, given neighborhood
data at a chosen vertex `v`, the canonical iso `G ≃g typeI G' a b` (resp.
`G ≃g typeII G' a b c`) along the equivalence `(Equiv.optionSubtypeNe v).symm`. They are the
bridge between flat-form reverse decomposition theorems (which describe the smaller graph
`G'` directly via `G.comap Subtype.val` and `fromEdgeSet`) and operation-form forward-
preservation theorems (`typeI_isGenericallyRigidInj_two` / `typeII_isGenericallyRigidInj_two`,
which operate on `typeI G' a b` / `typeII G' a b c`). The forward = operation / reverse = flat
split is documented in `DESIGN.md` *Statement-form conventions*. -/

/-- Build a graph iso `G ≃g H` along the canonical `V ≃ Option {w : V // w ≠ v}` equivalence,
given the adjacency-equivalence at each of the four `(u, w)` cases w.r.t. `v`. The `(none, none)`
case is `H` losing the loop, and the `(none, some)` and `(some, none)` cases are related by
adjacency-symmetry, so only one of them is asked for. The `(some, some)` case carries any
move-specific bridging-edge logic. -/
private def isoOfOptionSubtypeNe [DecidableEq V] {G : SimpleGraph V} (v : V)
    {H : SimpleGraph (Option {w : V // w ≠ v})}
    (hnone : ¬ H.Adj none none)
    (hns : ∀ w (hw : w ≠ v), H.Adj none (some ⟨w, hw⟩) ↔ G.Adj v w)
    (hss : ∀ {u w} (hu : u ≠ v) (hw : w ≠ v),
        H.Adj (some ⟨u, hu⟩) (some ⟨w, hw⟩) ↔ G.Adj u w) :
    G ≃g H where
  toEquiv := (Equiv.optionSubtypeNe v).symm
  map_rel_iff' {u w} := by
    by_cases hu : u = v <;> by_cases hw : w = v
    · subst hu; subst hw
      -- `simp` uses `hnone` (and `G.irrefl`) from context; explicit hints would be redundant.
      simp
    · subst hu
      rw [Equiv.optionSubtypeNe_symm_self, Equiv.optionSubtypeNe_symm_of_ne hw]
      exact hns w hw
    · subst hw
      rw [Equiv.optionSubtypeNe_symm_of_ne hu, Equiv.optionSubtypeNe_symm_self,
        H.adj_comm, G.adj_comm]
      exact hns u hu
    · rw [Equiv.optionSubtypeNe_symm_of_ne hu, Equiv.optionSubtypeNe_symm_of_ne hw]
      exact hss hu hw

/-- Iso from `G` to a Type I move applied to its induced subgraph on `{w // w ≠ v}`, when `v` is a
degree-2 vertex with neighbors `a, b`. The membership-style hypothesis `hN` says `N(v) = {a, b}`. -/
def typeI_iso_of_two_neighbors [DecidableEq V] {G : SimpleGraph V} {v a b : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hN : ∀ w, G.Adj v w ↔ w = a ∨ w = b) :
    G ≃g typeI (G.comap (Subtype.val : {w : V // w ≠ v} → V))
      ⟨a, hva.symm⟩ ⟨b, hvb.symm⟩ :=
  isoOfOptionSubtypeNe v (by simp)
    (fun w _ => by simp [hN])
    (fun _ _ => Iff.rfl)

/-- Iso from `G` to a Type II move applied to (induced subgraph + bridging edge `s(a, b)`), when
`v` has degree 3 with neighbors `a, b, c` and `a, b` are non-adjacent in `G`. -/
def typeII_iso_of_three_neighbors [DecidableEq V] {G : SimpleGraph V} {v a b c : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hvc : v ≠ c) (hab : a ≠ b)
    (hN : ∀ w, G.Adj v w ↔ w = a ∨ w = b ∨ w = c) (hnab : ¬ G.Adj a b) :
    G ≃g typeII (G.comap (Subtype.val : {w : V // w ≠ v} → V) ⊔
        fromEdgeSet ({s(⟨a, hva.symm⟩, ⟨b, hvb.symm⟩)} : Set (Sym2 _)))
      ⟨a, hva.symm⟩ ⟨b, hvb.symm⟩ ⟨c, hvc.symm⟩ :=
  isoOfOptionSubtypeNe v (by simp)
    (fun w _ => by simp [hN])
    (fun {u w} _ _ => by
      rw [typeII_adj_some_some, sup_adj, comap_adj, fromEdgeSet_adj, Set.mem_singleton_iff]
      -- Forward: contradiction from the deletion clause. Backward: lift the subtype-level Sym2
      -- equality through `Subtype.val` to `s(u, w) = s(a, b)`, then case-split to hit `¬G.Adj a b`.
      refine ⟨fun h => h.1.elim id (fun ⟨hL, _⟩ => absurd hL h.2),
        fun hadj => ⟨Or.inl hadj, fun heq => ?_⟩⟩
      have : s(u, w) = s(a, b) := by simpa using congrArg (Sym2.map Subtype.val) heq
      rcases Sym2.eq_iff.mp this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> grind [G.adj_symm])

/-! ### Flat-form Henneberg reverse decomposition for Laman graphs

Every Laman graph on `n ≥ 3` vertices admits a Henneberg reverse to another Laman graph on
one fewer vertex. Thin shell over `IsSparse.exists_typeI_or_typeII_reverse`: applies the sparse
flat-form decomposition to `h.isSparse`, discards the pendant branch via `IsLaman.two_le_degree`,
and bumps `G'.IsSparse 2 3` to `G'.IsLaman` via the typeI iso combined with `typeI_isLaman_iff`
(Type I) or the typeII iso combined with `typeII_edgeSet_ncard` plus the bridge-edge count
(Type II).

**Phase 5 milestone 1.** Phase 7 re-presented the sparse decomposition as a 3-way split (Commit
12), so the Laman shell here drops the pendant branch (`G.degree v = 1`) by contradicting
`IsLaman.two_le_degree`; the surviving Type I / Type II branches consume the sparse 3-way
exactly as before. Callers reconstruct the iso to `typeI G' a b` / `typeII G' a b c` via
`typeI_iso_of_two_neighbors` / `typeII_iso_of_three_neighbors` at the callsite, before invoking
the operation-form forward-preservation theorems (`typeI_isGenericallyRigidInj_two` /
`typeII_isGenericallyRigidInj_two`) and transporting along the iso. See `DESIGN.md`
*Statement-form conventions* for the forward = operation / reverse = flat split. -/

/-- **Strengthened decomposition theorem (flat form).** Every Laman graph `G` on `n ≥ 3`
vertices admits a Henneberg reverse to another Laman graph on the subtype `{w // w ≠ v}`:
either some vertex `v` has degree exactly 2 with two distinct neighbors `a, b` such that the
induced subgraph `G.comap Subtype.val` is Laman (Type I reverse), or some vertex `v` has
degree exactly 3 with three distinct neighbors `x, y, c` and a non-adjacent pair `(x, y)` such
that the induced subgraph augmented with the bridging edge `s(x, y)` is Laman (Type II reverse).

The Laman analogue of `IsSparse.exists_typeI_or_typeII_reverse`. Proof: apply the sparse
3-way version to `h.isSparse` (`G.edgeSet` is nonempty since Laman tight gives
`|E| = 2|V| - 3 ≥ 3` under `|V| ≥ 3`). The pendant branch (`deg v = 1`) is impossible since
`IsLaman.two_le_degree` forces `2 ≤ deg v`; dispatch via `absurd`. The Type I branch
(`deg v = 2`) feeds directly into `typeI_isLaman_iff` after iso transport. In the Type II
branch, the typeII iso transports `G`'s Laman to `(typeII G' x y c).IsLaman`, and
`typeII_edgeSet_ncard` plus the bridge-edge presence pins down `G'`'s tight edge count.

**Phase 5 milestone 1.** -/
theorem IsLaman.exists_typeI_or_typeII_reverse [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (h : G.IsLaman)
    (hV : 3 ≤ Fintype.card V) :
    ∃ v : V,
      (G.degree v = 2 ∧
        ∃ a b : {w : V // w ≠ v}, a ≠ b ∧
          (∀ w : V, G.Adj v w ↔ w = a.val ∨ w = b.val) ∧
          (G.comap (Subtype.val : {w : V // w ≠ v} → V)).IsLaman)
      ∨
      (G.degree v = 3 ∧
        ∃ x y c : {w : V // w ≠ v}, x ≠ y ∧ c ≠ x ∧ c ≠ y ∧
          (∀ w : V, G.Adj v w ↔ w = x.val ∨ w = y.val ∨ w = c.val) ∧
          ¬ G.Adj x.val y.val ∧
          (G.comap (Subtype.val : {w : V // w ≠ v} → V) ⊔
            fromEdgeSet ({s(x, y)} : Set _)).IsLaman) := by
  classical
  -- `G` has at least one edge: Laman tightness + `|V| ≥ 3` gives `|E| = 2|V| - 3 ≥ 3 ≥ 1`.
  have hE : G.edgeSet.Nonempty := by
    have h_eq := h.edgeSet_ncard
    rw [Nat.card_eq_fintype_card] at h_eq
    exact Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨v, hbranch⟩ := h.isSparse.exists_typeI_or_typeII_reverse hE
  refine ⟨v, ?_⟩
  rcases hbranch with
    ⟨hdeg1, _, _, _⟩ |
    ⟨hdeg2, a, b, hab, hN_iff, hG'sparse⟩ |
    ⟨hdeg3, x, y, c, hxy, hcx, hcy, hN, hnxy, hG'sparse⟩
  · -- Pendant branch: impossible since `IsLaman.two_le_degree` forces `2 ≤ deg v`.
    exact absurd hdeg1 (by have := h.two_le_degree hV v; omega)
  · -- Type I branch. Extract the two neighbours from `hN_iff` and
    -- bump `G'.IsSparse` to `G'.IsLaman` via `typeI_isLaman_iff` and the typeI iso.
    have ha_adj : G.Adj v a.val := (hN_iff a.val).mpr (Or.inl rfl)
    have hb_adj : G.Adj v b.val := (hN_iff b.val).mpr (Or.inr rfl)
    have hG'_laman : (G.comap (Subtype.val : {w : V // w ≠ v} → V)).IsLaman :=
      (typeI_isLaman_iff hab).mp
        (IsLaman.iso (typeI_iso_of_two_neighbors (G.ne_of_adj ha_adj) (G.ne_of_adj hb_adj)
          hN_iff) h)
    exact Or.inl ⟨hdeg2, a, b, hab, hN_iff, hG'_laman⟩
  · -- Type II branch. Build the typeII iso, transport `G.IsLaman` to `(typeII G' x y c).IsLaman`,
    -- and reconstruct `G'`'s tight edge count from `typeII_edgeSet_ncard` plus the bridge.
    refine Or.inr ⟨hdeg3, x, y, c, hxy, hcx, hcy, hN, hnxy, ?_⟩
    set G' : SimpleGraph {w : V // w ≠ v} :=
      G.comap (Subtype.val : {w : V // w ≠ v} → V) ⊔
        fromEdgeSet ({s(x, y)} : Set _) with hG'_def
    have h_iso : G ≃g typeII G' x y c :=
      typeII_iso_of_three_neighbors x.property.symm y.property.symm c.property.symm
        (fun heq => hxy (Subtype.ext heq)) hN hnxy
    have h_typeII_laman : (typeII G' x y c).IsLaman := IsLaman.iso h_iso h
    have h_count := h_typeII_laman.edgeSet_ncard
    rw [typeII_edgeSet_ncard G' hxy hcx hcy, Finite.card_option] at h_count
    have hbridge : s(x, y) ∈ G'.edgeSet := by
      change G'.Adj x y
      rw [hG'_def, sup_adj]
      exact Or.inr ((fromEdgeSet_adj _).mpr ⟨rfl, hxy⟩)
    have h_diff : (G'.edgeSet \ {s(x, y)}).ncard + 1 = G'.edgeSet.ncard :=
      Set.ncard_diff_singleton_add_one hbridge (Set.toFinite _)
    exact ⟨hG'sparse, by omega⟩

end Henneberg

/-! ### K₄ minus one edge is Laman

A worked example: `(⊤ : SimpleGraph (Fin 4)).deleteEdges {s(2, 3)}` is Laman. The proof
applies `typeI_isLaman` twice from `top_fin_two_isLaman` to get a Laman graph on
`Option (Option (Fin 2))`, then transports it to `Fin 4` via `IsLaman.iso`. -/

private def Henneberg.fin4equiv : Option (Option (Fin 2)) ≃ Fin 4 where
  toFun
    | none => 3
    | some none => 2
    | some (some 0) => 0
    | some (some 1) => 1
  invFun
    | 0 => some (some 0)
    | 1 => some (some 1)
    | 2 => some none
    | 3 => none
  left_inv := by decide
  right_inv := by decide

/-- Graph isomorphism from the iterated Type I extension of `K₂` to `K₄ \ {s(2, 3)}`. -/
private def Henneberg.fin4iso :
    (Henneberg.typeI (Henneberg.typeI (⊤ : SimpleGraph (Fin 2)) 0 1) (some 0) (some 1))
      ≃g ((⊤ : SimpleGraph (Fin 4)).deleteEdges {s(2, 3)}) where
  toEquiv := Henneberg.fin4equiv
  map_rel_iff' := by
    rintro (_ | _ | a) (_ | _ | b) <;> first
      | decide
      | (fin_cases a <;> decide)
      | (fin_cases b <;> decide)
      | (fin_cases a <;> fin_cases b <;> decide)

/-- The complete graph on four vertices minus one edge is Laman. The witness construction is
two iterated Type I Henneberg moves applied to `K₂`. -/
theorem top_fin_four_minus_edge_isLaman :
    ((⊤ : SimpleGraph (Fin 4)).deleteEdges {s(2, 3)}).IsLaman :=
  IsLaman.iso Henneberg.fin4iso <|
    Henneberg.typeI_isLaman
      (Henneberg.typeI_isLaman top_fin_two_isLaman (by decide))
      (by decide)

end SimpleGraph
