/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Framework
import CombinatorialRigidity.Laman
import CombinatorialRigidity.Mathlib.Data.Finset.Option
import CombinatorialRigidity.Mathlib.Data.Set.Card
import CombinatorialRigidity.Mathlib.Data.Sym.Sym2
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finite.Card
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Logic.Equiv.Option
import Mathlib.Tactic.IntervalCases

set_option linter.style.longFile 1700

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

@[simp] lemma typeI_not_adj_none_none : ¬ (typeI G a b).Adj none none := id

@[simp] lemma typeII_adj_some_some :
    (typeII G a b c).Adj (some u) (some v) ↔ G.Adj u v ∧ s(u, v) ≠ s(a, b) := Iff.rfl

@[simp] lemma typeII_adj_some_none :
    (typeII G a b c).Adj (some u) none ↔ u = a ∨ u = b ∨ u = c := Iff.rfl

@[simp] lemma typeII_adj_none_some :
    (typeII G a b c).Adj none (some v) ↔ v = a ∨ v = b ∨ v = c := Iff.rfl

@[simp] lemma typeII_not_adj_none_none : ¬ (typeII G a b c).Adj none none := id

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
  classical
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
  classical
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
  classical
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
  classical
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
            exact h_ab_in (mem_edgesIn.mpr ⟨hG_ab, by
              simp [Sym2.coe_mk, Set.insert_subset_iff, h_both.1, h_both.2]⟩)
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

/-! ### Decomposition iso (without a Laman claim about `G'`)

A Laman graph on `n ≥ 3` vertices is, up to canonical relabelling, the result of a Type I or
Type II Henneberg move applied to *some* underlying graph `G'` on one fewer vertex. The graph `G'`
is the natural choice (the induced subgraph on `{w | w ≠ v}`, plus the bridging edge `s(a, b)` for
Type II). The underlying equivalence is `(Equiv.optionSubtypeNe v).symm : V ≃ Option {w // w ≠ v}`,
which sends the chosen low-degree vertex `v` to `none`.

This statement does **not** claim `G'.IsLaman`; the Laman-preservation half of Henneberg's
theorem is the deeper combinatorial direction (the choice of which non-adjacent neighbor pair to
bridge in the Type II case is not arbitrary). It is deferred to a future phase. See
`notes/Phase3.md` and `notes/FRICTION.md` for details. -/

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
private def typeI_iso_of_two_neighbors [DecidableEq V] {G : SimpleGraph V} {v a b : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hN : ∀ w, G.Adj v w ↔ w = a ∨ w = b) :
    G ≃g typeI (G.comap (Subtype.val : {w : V // w ≠ v} → V))
      ⟨a, hva.symm⟩ ⟨b, hvb.symm⟩ :=
  isoOfOptionSubtypeNe v (by simp)
    (fun w _ => by simp [hN])
    (fun _ _ => Iff.rfl)

/-- Iso from `G` to a Type II move applied to (induced subgraph + bridging edge `s(a, b)`), when
`v` has degree 3 with neighbors `a, b, c` and `a, b` are non-adjacent in `G`. -/
private def typeII_iso_of_three_neighbors [DecidableEq V] {G : SimpleGraph V} {v a b c : V}
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

/-- The typeI side of `IsLaman.exists_typeI_or_typeII_iso`: package the iso witness for a
degree-2 vertex `v` with neighbors `{a, b}`. -/
private theorem typeI_branch_of_two_neighbors {G : SimpleGraph V} {v a b : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (hN_iff : ∀ w, G.Adj v w ↔ w = a ∨ w = b) :
    ∃ G' : SimpleGraph {w : V // w ≠ v},
      ∃ a' b' : {w : V // w ≠ v}, a' ≠ b' ∧ Nonempty (G ≃g typeI G' a' b') := by
  classical
  exact ⟨_, ⟨a, hva.symm⟩, ⟨b, hvb.symm⟩,
    fun heq => hab (Subtype.mk.injEq .. |>.mp heq),
    ⟨typeI_iso_of_two_neighbors hva hvb hN_iff⟩⟩

/-- The typeII side of `IsLaman.exists_typeI_or_typeII_iso`: package the iso witness for a
degree-3 vertex `v` with neighbors `{a, b, c}` and a known non-adjacent pair `{a, b}`. The three
distinctness assumptions are taken in the order matching the goal `a' ≠ b' ∧ c' ≠ a' ∧ c' ≠ b'`. -/
private theorem typeII_branch_of_nonadj {G : SimpleGraph V} {v a b c : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hvc : v ≠ c)
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (hN_iff : ∀ w, G.Adj v w ↔ w = a ∨ w = b ∨ w = c)
    (hnab : ¬ G.Adj a b) :
    ∃ G' : SimpleGraph {w : V // w ≠ v},
      ∃ a' b' c' : {w : V // w ≠ v}, a' ≠ b' ∧ c' ≠ a' ∧ c' ≠ b' ∧ G'.Adj a' b' ∧
        Nonempty (G ≃g typeII G' a' b' c') := by
  classical
  exact ⟨_, ⟨a, hva.symm⟩, ⟨b, hvb.symm⟩, ⟨c, hvc.symm⟩,
    fun heq => hab (Subtype.mk.injEq .. |>.mp heq),
    fun heq => hca (Subtype.mk.injEq .. |>.mp heq),
    fun heq => hcb (Subtype.mk.injEq .. |>.mp heq),
    Or.inr ⟨rfl, fun heq => hab (Subtype.mk.injEq .. |>.mp heq)⟩,
    ⟨typeII_iso_of_three_neighbors hva hvb hvc hab hN_iff hnab⟩⟩

/-- Every Laman graph on `n ≥ 3` vertices is isomorphic to a Type I or Type II Henneberg move
applied to some graph `G'` on `{w : V // w ≠ v}` (for some chosen `v`). The Laman-ness of `G'` is
**not** asserted; that is the deeper Henneberg-reverse direction, deferred to a later phase.

Proof outline:
* Pick a vertex `v` of degree 2 or 3 via `IsLaman.exists_two_le_degree_le_three`.
* Degree 2: `G'` is the induced subgraph and `a, b` are the two `v`-neighbors.
* Degree 3: pick a non-adjacent neighbor pair `{a, b}` (via
  `IsLaman.exists_nonadj_among_three_neighbors`) and the third neighbor `c`; `G'` is the induced
  subgraph augmented with the bridging edge `s(a, b)`. -/
theorem IsLaman.exists_typeI_or_typeII_iso [Fintype V]
    {G : SimpleGraph V} (h : G.IsLaman)
    (hV : 3 ≤ Fintype.card V) :
    ∃ (v : V) (G' : SimpleGraph {w : V // w ≠ v}),
      ((∃ a b : {w : V // w ≠ v}, a ≠ b ∧ Nonempty (G ≃g typeI G' a b)) ∨
       (∃ a b c : {w : V // w ≠ v}, a ≠ b ∧ c ≠ a ∧ c ≠ b ∧ G'.Adj a b ∧
        Nonempty (G ≃g typeII G' a b c))) := by
  classical
  obtain ⟨v, hv2, hv3⟩ := h.exists_two_le_degree_le_three hV
  refine ⟨v, ?_⟩
  rcases (show G.degree v = 2 ∨ G.degree v = 3 from by omega) with hdeg | hdeg
  · -- Degree-2 case: Type I reverse.
    obtain ⟨a, b, hab, hN_eq⟩ := Finset.card_eq_two.mp hdeg
    have hN_iff : ∀ w, G.Adj v w ↔ w = a ∨ w = b := fun w => by
      rw [← mem_neighborFinset, hN_eq]; simp
    have ha_adj : G.Adj v a := (hN_iff a).mpr (Or.inl rfl)
    have hb_adj : G.Adj v b := (hN_iff b).mpr (Or.inr rfl)
    exact (typeI_branch_of_two_neighbors (G.ne_of_adj ha_adj) (G.ne_of_adj hb_adj) hab hN_iff).imp
      fun _ => Or.inl
  · -- Degree-3 case: Type II reverse. Pick a non-adjacent pair among `{a, b, c}` and rotate
    -- the names so it is `(a, b)`; each rcases branch invokes `typeII_branch_of_nonadj` with
    -- the appropriate relabelling.
    obtain ⟨a, b, c, hab, hac, hbc, hN_eq⟩ := Finset.card_eq_three.mp hdeg
    have hN_iff : ∀ w, G.Adj v w ↔ w = a ∨ w = b ∨ w = c := fun w => by
      rw [← mem_neighborFinset, hN_eq]; simp
    have ha_adj : G.Adj v a := (hN_iff a).mpr (Or.inl rfl)
    have hb_adj : G.Adj v b := (hN_iff b).mpr (Or.inr (Or.inl rfl))
    have hc_adj : G.Adj v c := (hN_iff c).mpr (Or.inr (Or.inr rfl))
    have hva : v ≠ a := G.ne_of_adj ha_adj
    have hvb : v ≠ b := G.ne_of_adj hb_adj
    have hvc : v ≠ c := G.ne_of_adj hc_adj
    rcases h.exists_nonadj_among_three_neighbors ha_adj hb_adj hc_adj hab hac hbc with
      hnab | hnac | hnbc
    · exact (typeII_branch_of_nonadj hva hvb hvc hab hac.symm hbc.symm hN_iff hnab).imp
        fun _ => Or.inr
    · exact (typeII_branch_of_nonadj hva hvc hvb hac hab.symm hbc
        (fun w => by rw [hN_iff]; tauto) hnac).imp fun _ => Or.inr
    · exact (typeII_branch_of_nonadj hvb hvc hva hbc hab hac
        (fun w => by rw [hN_iff]; tauto) hnbc).imp fun _ => Or.inr

/-! ### Per-pair tight-blocker witness (typeII reverse, Laman claim)

The Phase 5 milestone-1 deep step. The lemma `IsLaman.typeII_reverse_blocker` says: in a Laman
graph `G` with a degree-3 vertex `v` and non-adjacent pair `(x, y)` among `v`'s neighbors, if the
typeII-reverse candidate `G' := (G ↾ {v}ᶜ) ⊔ {bridge(x, y)}` is *not* Laman, then there exists a
`(2, 3)`-tight set `S ⊆ V \ {v}` containing both `x` and `y` in `G`. (The third neighbor `c`
plus the full neighbor-set characterization is taken explicitly to allow the typeII iso transfer
from `G` to `typeII G' xs ys cs`, which is how `G'`'s correct edge count is established.)

The case-split on how many of the three pairs `{(x,y), (x,c), (y,c)}` are non-adjacent will then
combine such per-pair witnesses via `IsTightOn.union_inter` to force a contradiction with `G`'s
sparsity, completing the strengthened decomposition
`IsLaman.exists_typeI_or_typeII_reverse`. -/

/-- Edges of `G.comap f` on `s'` correspond (via `Sym2.map f`) to edges of `G` on `f '' s'`.
The image-form equality holds without an injectivity hypothesis on `f`; injectivity is what lifts
the ncard equality (used downstream). -/
private lemma image_edgesIn_comap (G : SimpleGraph V) {V' : Type*} (f : V' → V) (s' : Set V') :
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

/-- **Per-pair tight-blocker witness for the typeII Henneberg reverse.**

Inputs: a Laman graph `G`; a vertex `v` whose three distinct neighbors are exactly `{x, y, c}`;
a non-adjacent pair `(x, y)` among the neighbors; a *failed* candidate `G'` (the induced subgraph
on `{w // w ≠ v}` plus the bridging edge `s(⟨x⟩, ⟨y⟩)`) — i.e. `¬ G'.IsLaman`.

Output: a `(2, 3)`-tight set `S` in `G` with `v ∉ S` and `{x, y} ⊆ S`.

The proof routes the edge count of `G'` through the typeII iso `G ≃g typeII G' xs ys cs`,
transfers Laman, and uses `typeII_edgeSet_ncard` to deduce `G'.edgeSet.ncard + 3 =
2 * Nat.card {w // w ≠ v}`. Hence `¬ G'.IsLaman` collapses to `¬ G'.IsSparse 2 3`, giving a
violating Finset `s'`. Lifting `s'` to `S := s'.image Subtype.val ⊆ V \ {v}`, the bound
`(G'.edgesIn ↑s').ncard ≤ (G.edgesIn ↑S).ncard + 1` (case `xs, ys ∈ s'`) combined with `G`'s
sparsity gives tightness via `IsSparse.isTightOn_of_le`; the remaining cases (one of `xs, ys`
outside `s'`) drop the `+1` and contradict `G`'s sparsity directly. -/
theorem IsLaman.typeII_reverse_blocker
    [Finite V] {G : SimpleGraph V} (h : G.IsLaman) {v : V}
    {x y c : V} (hxv : x ≠ v) (hyv : y ≠ v) (hcv : c ≠ v)
    (hxy : x ≠ y) (hcx : c ≠ x) (hcy : c ≠ y)
    (hN : ∀ w, G.Adj v w ↔ w = x ∨ w = y ∨ w = c)
    (hnxy : ¬ G.Adj x y)
    (h_not_laman : ¬ (G.comap (Subtype.val : {w : V // w ≠ v} → V) ⊔
                       fromEdgeSet ({s(⟨x, hxv⟩, ⟨y, hyv⟩)} : Set (Sym2 _))).IsLaman) :
    ∃ S : Finset V, v ∉ S ∧ x ∈ S ∧ y ∈ S ∧ G.IsTightOn 2 3 S := by
  classical
  set f : {w : V // w ≠ v} → V := Subtype.val with hf_def
  set xs : {w : V // w ≠ v} := ⟨x, hxv⟩ with hxs_def
  set ys : {w : V // w ≠ v} := ⟨y, hyv⟩ with hys_def
  set cs : {w : V // w ≠ v} := ⟨c, hcv⟩
  set bridge : Sym2 {w : V // w ≠ v} := s(xs, ys) with hbridge_def
  set G' : SimpleGraph {w : V // w ≠ v} :=
    G.comap f ⊔ fromEdgeSet ({bridge} : Set _) with hG'_def
  have hxs_ne_ys : xs ≠ ys := fun heq => hxy (Subtype.mk.injEq .. |>.mp heq)
  have hcs_ne_xs : cs ≠ xs := fun heq => hcx (Subtype.mk.injEq .. |>.mp heq)
  have hcs_ne_ys : cs ≠ ys := fun heq => hcy (Subtype.mk.injEq .. |>.mp heq)
  -- Bridge is an edge of G'.
  have hbridge_in_G' : bridge ∈ G'.edgeSet := by
    change G'.Adj xs ys
    rw [hG'_def, sup_adj]
    exact Or.inr ((fromEdgeSet_adj _).mpr ⟨rfl, hxs_ne_ys⟩)
  -- Edge count of G' via the typeII iso: G ≃g typeII G' xs ys cs.
  have h_iso : G ≃g typeII G' xs ys cs :=
    typeII_iso_of_three_neighbors hxv.symm hyv.symm hcv.symm hxy hN hnxy
  have h_typeII_laman : (typeII G' xs ys cs).IsLaman := IsLaman.iso h_iso h
  have h_typeII_count := h_typeII_laman.edgeSet_ncard
  rw [typeII_edgeSet_ncard G' hxs_ne_ys hcs_ne_xs hcs_ne_ys,
      Finite.card_option, ← hbridge_def] at h_typeII_count
  have h_diff : (G'.edgeSet \ {bridge}).ncard + 1 = G'.edgeSet.ncard :=
    Set.ncard_diff_singleton_add_one hbridge_in_G' (Set.toFinite _)
  have hG'_count : G'.edgeSet.ncard + 3 = 2 * Nat.card {w : V // w ≠ v} := by omega
  -- ¬G'.IsLaman + edge count → ¬G'.IsSparse 2 3.
  have hG'_not_sparse : ¬ G'.IsSparse 2 3 :=
    fun hsp => h_not_laman ⟨hsp, hG'_count⟩
  unfold IsSparse at hG'_not_sparse
  push Not at hG'_not_sparse
  obtain ⟨s', hs'_card, hviol⟩ := hG'_not_sparse
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
    have := h.isSparse S (by rw [hS_card]; exact hs'_card)
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
    refine h.isSparse.isTightOn_of_le ?_ ?_
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

/-! ### Strengthened decomposition: `G'` is also Laman

The main payload of Phase 5 milestone 1. Combines the iso-only decomposition
`IsLaman.exists_typeI_or_typeII_iso` with `typeI_isLaman_iff` (degree-2 branch) and
the typeII-reverse blocker argument (degree-3 branch, via `typeII_reverse_blocker` +
the "no tight set in `V \ {v}` can contain three neighbors of `v`" overshoot helper). -/

/-- **Per-pair witness-or-blocker dispatcher.** For a Laman graph `G` with a degree-3 vertex
`v` whose three distinct neighbors are exactly `{x, y, c}`, and a non-adjacent pair `(x, y)`:
either the typeII-reverse candidate `G'_xy := (G ↾ {v}ᶜ) ⊔ {bridge(x, y)}` is Laman (yielding
the full typeII decomposition witness with `G'.IsLaman`), or it isn't (yielding a `(2, 3)`-tight
blocker `S ⊆ V \ {v}` with `{x, y} ⊆ S` via `IsLaman.typeII_reverse_blocker`).

The case-split that drives `exists_typeI_or_typeII_reverse`'s degree-3 branch: invoke per
non-adjacent pair; on success, return the witness; on failure, accumulate blockers and combine
them into a tight set contradicting `IsLaman.no_isTightOn_excluding_three_neighbors`. -/
private theorem IsLaman.typeII_reverse_witness_or_blocker
    [Finite V] {G : SimpleGraph V} (h : G.IsLaman) {v x y c : V}
    (hxv : x ≠ v) (hyv : y ≠ v) (hcv : c ≠ v)
    (hxy : x ≠ y) (hcx : c ≠ x) (hcy : c ≠ y)
    (hN : ∀ w, G.Adj v w ↔ w = x ∨ w = y ∨ w = c)
    (hnxy : ¬ G.Adj x y) :
    (∃ G' : SimpleGraph {w : V // w ≠ v}, G'.IsLaman ∧
       ∃ x' y' c' : {w : V // w ≠ v}, x' ≠ y' ∧ c' ≠ x' ∧ c' ≠ y' ∧ G'.Adj x' y' ∧
         Nonempty (G ≃g typeII G' x' y' c')) ∨
    (∃ S : Finset V, v ∉ S ∧ x ∈ S ∧ y ∈ S ∧ G.IsTightOn 2 3 S) := by
  classical
  set G' : SimpleGraph {w : V // w ≠ v} :=
    G.comap (Subtype.val : {w : V // w ≠ v} → V) ⊔
      fromEdgeSet ({s(⟨x, hxv⟩, ⟨y, hyv⟩)} : Set _) with hG'_def
  have hxy_s : (⟨x, hxv⟩ : {w : V // w ≠ v}) ≠ ⟨y, hyv⟩ :=
    fun heq => hxy (Subtype.mk.injEq .. |>.mp heq)
  have hcx_s : (⟨c, hcv⟩ : {w : V // w ≠ v}) ≠ ⟨x, hxv⟩ :=
    fun heq => hcx (Subtype.mk.injEq .. |>.mp heq)
  have hcy_s : (⟨c, hcv⟩ : {w : V // w ≠ v}) ≠ ⟨y, hyv⟩ :=
    fun heq => hcy (Subtype.mk.injEq .. |>.mp heq)
  by_cases h_lam : G'.IsLaman
  · -- Success: G'_xy is Laman; package the typeII witness.
    refine Or.inl ⟨G', h_lam, ⟨x, hxv⟩, ⟨y, hyv⟩, ⟨c, hcv⟩, hxy_s, hcx_s, hcy_s, ?_,
      ⟨typeII_iso_of_three_neighbors hxv.symm hyv.symm hcv.symm hxy hN hnxy⟩⟩
    show G'.Adj _ _
    rw [hG'_def, sup_adj]
    exact Or.inr ((fromEdgeSet_adj _).mpr ⟨rfl, hxy_s⟩)
  · -- Failure: G'_xy is not Laman; extract the blocker.
    exact Or.inr (IsLaman.typeII_reverse_blocker h hxv hyv hcv hxy hcx hcy hN hnxy h_lam)

/-- **Overshoot helper.** In a Laman graph `G`, no `(2, 3)`-tight set `T ⊆ V \ {v}` can
contain three distinct neighbors `a, b, c` of `v`: inserting `v` would add 1 vertex but
at least 3 edges (the incident edges `s(v, a), s(v, b), s(v, c)`), overshooting the
`(2, 3)`-sparsity bound at `insert v T`.

The contradiction primitive that the typeII-reverse case-split argument reduces to. -/
private lemma IsLaman.no_isTightOn_excluding_three_neighbors
    {G : SimpleGraph V} (h : G.IsLaman) {v a b c : V}
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
  -- Set of three new edges va, vb, vc.
  set E3 : Set (Sym2 V) := {s(v, a), s(v, b), s(v, c)} with hE3_def
  -- |E3| = 3 (pairwise distinct since a, b, c distinct from v and each other).
  have hne_ab : s(v, a) ≠ s(v, b) := fun h => (Sym2.eq_iff.mp h).elim
    (fun ⟨_, h2⟩ => hab h2) (fun ⟨h1, _⟩ => hvb h1)
  have hne_ac : s(v, a) ≠ s(v, c) := fun h => (Sym2.eq_iff.mp h).elim
    (fun ⟨_, h2⟩ => hac h2) (fun ⟨h1, _⟩ => hvc h1)
  have hne_bc : s(v, b) ≠ s(v, c) := fun h => (Sym2.eq_iff.mp h).elim
    (fun ⟨_, h2⟩ => hbc h2) (fun ⟨h1, _⟩ => hvc h1)
  have hE3_card : E3.ncard = 3 := by
    rw [hE3_def, Set.ncard_insert_of_notMem (by simp [hne_ab, hne_ac]) (Set.toFinite _),
        Set.ncard_pair hne_bc]
  -- Containment helpers.
  have h_T_sub_T' : (↑T : Set V) ⊆ (↑T' : Set V) := by
    intro x hx
    rw [hT'_def, Finset.coe_insert]
    exact Or.inr hx
  have h_v_in_T' : v ∈ (↑T' : Set V) := by
    rw [hT'_def, Finset.coe_insert]; exact Set.mem_insert _ _
  have h_a_in_T' : a ∈ (↑T' : Set V) := h_T_sub_T' (Finset.mem_coe.mpr haT)
  have h_b_in_T' : b ∈ (↑T' : Set V) := h_T_sub_T' (Finset.mem_coe.mpr hbT)
  have h_c_in_T' : c ∈ (↑T' : Set V) := h_T_sub_T' (Finset.mem_coe.mpr hcT)
  -- Each edge in E3 lies in G.edgesIn ↑T'.
  have h_E3_in : E3 ⊆ G.edgesIn (↑T' : Set V) := by
    rintro e (rfl | rfl | rfl) <;> refine mem_edgesIn.mpr ⟨?_, ?_⟩
    · exact ha
    · rw [Sym2.coe_mk]
      exact Set.insert_subset_iff.mpr ⟨h_v_in_T', Set.singleton_subset_iff.mpr h_a_in_T'⟩
    · exact hb
    · rw [Sym2.coe_mk]
      exact Set.insert_subset_iff.mpr ⟨h_v_in_T', Set.singleton_subset_iff.mpr h_b_in_T'⟩
    · exact hc
    · rw [Sym2.coe_mk]
      exact Set.insert_subset_iff.mpr ⟨h_v_in_T', Set.singleton_subset_iff.mpr h_c_in_T'⟩
  -- E3 is disjoint from G.edgesIn ↑T (since v ∉ T).
  have h_disj : Disjoint E3 (G.edgesIn (↑T : Set V)) := by
    rw [Set.disjoint_left]
    rintro e he h_mem
    obtain ⟨_, hsub⟩ := mem_edgesIn.mp h_mem
    have hv_in_e : v ∈ (e : Set V) := by
      rcases he with rfl | rfl | rfl <;> (rw [Sym2.coe_mk]; exact Set.mem_insert _ _)
    exact hvT (Finset.mem_coe.mp (hsub hv_in_e))
  -- G.edgesIn ↑T ⊆ G.edgesIn ↑T'.
  have h_edgesIn_sub : G.edgesIn (↑T : Set V) ⊆ G.edgesIn (↑T' : Set V) :=
    edgesIn_mono h_T_sub_T'
  -- Combine: ncard ↑T' ≥ ncard ↑T + 3.
  have h_ncard_ge : (G.edgesIn (↑T : Set V)).ncard + 3 ≤ (G.edgesIn (↑T' : Set V)).ncard :=
    calc (G.edgesIn (↑T : Set V)).ncard + 3
        = (G.edgesIn (↑T : Set V)).ncard + E3.ncard := by rw [hE3_card]
      _ = (G.edgesIn (↑T : Set V) ∪ E3).ncard :=
          (Set.ncard_union_eq h_disj.symm (G.edgesIn_finite T) (Set.toFinite _)).symm
      _ ≤ (G.edgesIn (↑T' : Set V)).ncard :=
          Set.ncard_le_ncard (Set.union_subset h_edgesIn_sub h_E3_in) (G.edgesIn_finite T')
  -- Sparsity at T': need 3 ≤ 2 * T'.card. Since {a, b, c} ⊆ T, T.card ≥ 3, so T'.card ≥ 4.
  have h3_sub_T : ({a, b, c} : Finset V) ⊆ T := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have h3_card : ({a, b, c} : Finset V).card = 3 := by
    rw [show ({a, b, c} : Finset V) = insert a (insert b {c}) from rfl,
        Finset.card_insert_of_notMem (by simp [hab, hac]),
        Finset.card_insert_of_notMem (by simp [hbc])]
    rfl
  have hT_card_ge : 3 ≤ T.card := h3_card ▸ Finset.card_le_card h3_sub_T
  have hT'_sparse := h.isSparse T' (by rw [hT'_card]; omega)
  unfold IsTightOn at hT
  omega

/-! ### Contradiction templates for the typeII-reverse case analysis

For a Laman graph with degree-3 vertex `v` and neighbors `a, b, c`, each non-adjacent pair
either gives a typeII-reverse witness or a tight blocker via the dispatcher above. The three
templates below absorb every combination of blockers (one, two-with-shared-vertex, or three),
build a tight `T ⊆ V \ {v}` containing `{a, b, c}`, and contradict
`no_isTightOn_excluding_three_neighbors`. All four helpers (the primitive + the three
templates) are `private`: they are scaffolding for `exists_typeI_or_typeII_reverse`. -/

/-- **Squeeze form of the overshoot helper.** Given `T : Finset V` containing three distinct
neighbors `a, b, c` of `v` (with `v ∉ T`) and the squeeze inequality
`2 * #T ≤ #(edgesIn T) + 3`, applying `IsSparse.isTightOn_of_le` upgrades to
`T.IsTightOn 2 3` and `no_isTightOn_excluding_three_neighbors` closes. The contradiction
templates below each reduce to this primitive after building `T` and verifying the squeeze. -/
private lemma IsLaman.False_of_three_neighbor_squeeze
    {G : SimpleGraph V} (h : G.IsLaman) {v a b c : V}
    (ha : G.Adj v a) (hb : G.Adj v b) (hc : G.Adj v c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {T : Finset V} (hvT : v ∉ T) (haT : a ∈ T) (hbT : b ∈ T) (hcT : c ∈ T)
    (h_squeeze : 2 * T.card ≤ (G.edgesIn (↑T : Set V)).ncard + 3) : False := by
  classical
  have h3_sub_T : ({a, b, c} : Finset V) ⊆ T := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have h3_card : ({a, b, c} : Finset V).card = 3 := by
    rw [show ({a, b, c} : Finset V) = insert a (insert b {c}) from rfl,
        Finset.card_insert_of_notMem (by simp [hab, hac]),
        Finset.card_insert_of_notMem (by simp [hbc])]
    rfl
  have hT_card_ge : 3 ≤ T.card := h3_card ▸ Finset.card_le_card h3_sub_T
  have hT_tight : G.IsTightOn 2 3 T :=
    h.isSparse.isTightOn_of_le (by omega) h_squeeze
  exact IsLaman.no_isTightOn_excluding_three_neighbors h ha hb hc hab hac hbc
    hvT haT hbT hcT hT_tight

/-- **1-pair contradiction template.** A single blocker `S` containing two neighbors `x, y` of `v`,
with the third neighbor `z` connected to both `x` and `y` by edges of `G`: case-split on `z ∈ S`.
If yes, `S` already contains `{x, y, z}` and the primitive closes. If no, extend to
`T := insert z S`; the two edges `s(x, z)` and `s(y, z)` are in `edgesIn T` but not in `edgesIn S`
(since `z ∉ S`), giving `#(edgesIn T) ≥ #(edgesIn S) + 2`, which combined with tightness of `S`
saturates the squeeze at `T`. -/
private lemma IsLaman.contradiction_one_pair
    {G : SimpleGraph V} (h : G.IsLaman) {v x y z : V}
    (hx : G.Adj v x) (hy : G.Adj v y) (hz : G.Adj v z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxz_adj : G.Adj x z) (hyz_adj : G.Adj y z)
    {S : Finset V} (hvS : v ∉ S) (hxS : x ∈ S) (hyS : y ∈ S)
    (hS_tight : G.IsTightOn 2 3 S) : False := by
  classical
  by_cases hzS : z ∈ S
  · refine IsLaman.False_of_three_neighbor_squeeze h hx hy hz hxy hxz hyz hvS hxS hyS hzS ?_
    unfold IsTightOn at hS_tight; omega
  · set T : Finset V := insert z S with hT_def
    have hvT : v ∉ T := by
      simp only [hT_def, Finset.mem_insert, not_or]
      exact ⟨G.ne_of_adj hz, hvS⟩
    have hzT : z ∈ T := Finset.mem_insert_self z S
    have hxT : x ∈ T := Finset.mem_insert_of_mem hxS
    have hyT : y ∈ T := Finset.mem_insert_of_mem hyS
    have hT_card : T.card = S.card + 1 := Finset.card_insert_of_notMem hzS
    have hxz_in_T : s(x, z) ∈ G.edgesIn (↑T : Set V) := by
      rw [mem_edgesIn]
      refine ⟨hxz_adj, ?_⟩
      rw [Sym2.coe_mk]
      exact Set.insert_subset_iff.mpr ⟨hxT, Set.singleton_subset_iff.mpr hzT⟩
    have hyz_in_T : s(y, z) ∈ G.edgesIn (↑T : Set V) := by
      rw [mem_edgesIn]
      refine ⟨hyz_adj, ?_⟩
      rw [Sym2.coe_mk]
      exact Set.insert_subset_iff.mpr ⟨hyT, Set.singleton_subset_iff.mpr hzT⟩
    have hxz_nin_S : s(x, z) ∉ G.edgesIn (↑S : Set V) := by
      intro hmem
      rw [mem_edgesIn] at hmem
      have h_z_in : z ∈ (s(x, z) : Set V) := by
        rw [Sym2.coe_mk]; exact Set.mem_insert_of_mem _ rfl
      exact hzS (Finset.mem_coe.mp (hmem.2 h_z_in))
    have hyz_nin_S : s(y, z) ∉ G.edgesIn (↑S : Set V) := by
      intro hmem
      rw [mem_edgesIn] at hmem
      have h_z_in : z ∈ (s(y, z) : Set V) := by
        rw [Sym2.coe_mk]; exact Set.mem_insert_of_mem _ rfl
      exact hzS (Finset.mem_coe.mp (hmem.2 h_z_in))
    have hxz_ne_yz : s(x, z) ≠ s(y, z) := fun heq =>
      (Sym2.eq_iff.mp heq).elim
        (fun ⟨h1, _⟩ => hxy h1)
        (fun ⟨h1, _⟩ => hxz h1)
    set E : Set (Sym2 V) := {s(x, z), s(y, z)} with hE_def
    have hE_card : E.ncard = 2 := by rw [hE_def, Set.ncard_pair hxz_ne_yz]
    have hE_in_T : E ⊆ G.edgesIn (↑T : Set V) := by
      rintro e (rfl | rfl)
      · exact hxz_in_T
      · exact hyz_in_T
    have hE_disj : Disjoint E (G.edgesIn (↑S : Set V)) := by
      rw [Set.disjoint_left]
      rintro e (rfl | rfl)
      · exact hxz_nin_S
      · exact hyz_nin_S
    have h_edgesIn_sub : G.edgesIn (↑S : Set V) ⊆ G.edgesIn (↑T : Set V) := by
      apply edgesIn_mono
      simp [hT_def, Finset.coe_insert, Set.subset_insert]
    have h_count : (G.edgesIn (↑S : Set V)).ncard + 2 ≤ (G.edgesIn (↑T : Set V)).ncard := by
      calc (G.edgesIn (↑S : Set V)).ncard + 2
          = (G.edgesIn (↑S : Set V)).ncard + E.ncard := by rw [hE_card]
        _ = (G.edgesIn (↑S : Set V) ∪ E).ncard :=
            (Set.ncard_union_eq hE_disj.symm (G.edgesIn_finite S) (Set.toFinite _)).symm
        _ ≤ (G.edgesIn (↑T : Set V)).ncard :=
            Set.ncard_le_ncard (Set.union_subset h_edgesIn_sub hE_in_T) (G.edgesIn_finite T)
    refine IsLaman.False_of_three_neighbor_squeeze h hx hy hz hxy hxz hyz hvT hxT hyT hzT ?_
    unfold IsTightOn at hS_tight
    omega

/-- **2-pair contradiction template.** Two blockers sharing a vertex `z` (the third neighbor):
`Sxz` contains `{x, z}` and `Syz` contains `{y, z}`, with the third pair `(x, y)` adjacent.
Case-split on `2 ≤ #(Sxz ∩ Syz)`. If yes, `IsTightOn.union_inter` gives `Sxz ∪ Syz` tight,
which contains `{x, y, z}`. If no, the intersection is exactly `{z}` (size 1, contains `z`),
forcing `x ∉ Syz` and `y ∉ Sxz`; the cross-edge `s(x, y)` lies in `edgesIn (Sxz ∪ Syz)` but in
neither `edgesIn Sxz` nor `edgesIn Syz`, saturating the squeeze at `T := Sxz ∪ Syz`. -/
private lemma IsLaman.contradiction_two_pair
    [Finite V] {G : SimpleGraph V} (h : G.IsLaman) {v x y z : V}
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
  · have ⟨hT_tight, _⟩ := hSxz_tight.union_inter hSyz_tight h.isSparse (by omega)
    refine IsLaman.False_of_three_neighbor_squeeze h hx hy hz hxy hxz hyz hvT hxT hyT hzT ?_
    unfold IsTightOn at hT_tight
    rw [hT_def]; omega
  · push Not at h_big
    have hz_inter : z ∈ Sxz ∩ Syz := Finset.mem_inter.mpr ⟨hzSxz, hzSyz⟩
    have h_inter_card : (Sxz ∩ Syz).card = 1 := by
      have h_ge : 1 ≤ (Sxz ∩ Syz).card := Finset.card_pos.mpr ⟨z, hz_inter⟩
      omega
    have h_inter_eq : Sxz ∩ Syz = {z} :=
      (Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr hz_inter)
        (by rw [Finset.card_singleton]; omega)).symm
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
    have hT_card : T.card = Sxz.card + Syz.card - 1 := by
      have h1 := Finset.card_union_add_card_inter Sxz Syz
      rw [← hT_def, h_inter_card] at h1
      omega
    have h_e_inter : (G.edgesIn (↑(Sxz ∩ Syz) : Set V)).ncard = 0 := by
      rw [h_inter_eq, Finset.coe_singleton, edgesIn_singleton]
      exact Set.ncard_empty _
    have h_super : (G.edgesIn (↑Sxz : Set V)).ncard + (G.edgesIn (↑Syz : Set V)).ncard ≤
                   (G.edgesIn (↑T : Set V)).ncard +
                   (G.edgesIn (↑(Sxz ∩ Syz) : Set V)).ncard := by
      have h_ncard := G.edgesIn_ncard_add_le (↑Sxz : Set V) (↑Syz : Set V)
      rw [show (↑T : Set V) = ↑Sxz ∪ ↑Syz from by rw [hT_def]; exact Finset.coe_union _ _,
          show (↑(Sxz ∩ Syz) : Set V) = ↑Sxz ∩ ↑Syz from Finset.coe_inter _ _]
      exact h_ncard
    have hxy_in_T : s(x, y) ∈ G.edgesIn (↑T : Set V) := by
      rw [mem_edgesIn]
      refine ⟨hxy_adj, ?_⟩
      rw [Sym2.coe_mk]
      exact Set.insert_subset_iff.mpr ⟨hxT, Set.singleton_subset_iff.mpr hyT⟩
    have hxy_nin_Sxz : s(x, y) ∉ G.edgesIn (↑Sxz : Set V) := by
      intro hmem
      rw [mem_edgesIn] at hmem
      have hy_in : y ∈ (s(x, y) : Set V) := by
        rw [Sym2.coe_mk]; exact Set.mem_insert_of_mem _ rfl
      exact hy_nin_Sxz (Finset.mem_coe.mp (hmem.2 hy_in))
    have hxy_nin_Syz : s(x, y) ∉ G.edgesIn (↑Syz : Set V) := by
      intro hmem
      rw [mem_edgesIn] at hmem
      have hx_in : x ∈ (s(x, y) : Set V) := by
        rw [Sym2.coe_mk]; exact Set.mem_insert _ _
      exact hx_nin_Syz (Finset.mem_coe.mp (hmem.2 hx_in))
    -- |edgesIn Sxz ∪ edgesIn Syz| = e(Sxz) + e(Syz) - e(Sxz ∩ Syz) = e(Sxz) + e(Syz).
    have h_union_card : (G.edgesIn (↑Sxz : Set V) ∪ G.edgesIn (↑Syz : Set V)).ncard +
        (G.edgesIn (↑(Sxz ∩ Syz) : Set V)).ncard =
        (G.edgesIn (↑Sxz : Set V)).ncard + (G.edgesIn (↑Syz : Set V)).ncard := by
      have h1 := Set.ncard_union_add_ncard_inter
        (G.edgesIn (↑Sxz : Set V)) (G.edgesIn (↑Syz : Set V))
      have h2 : G.edgesIn (↑Sxz : Set V) ∩ G.edgesIn (↑Syz : Set V) =
                G.edgesIn (↑(Sxz ∩ Syz) : Set V) := by
        rw [Finset.coe_inter, edgesIn_inter]
      rw [h2] at h1; exact h1
    have h_union_sub_T : G.edgesIn (↑Sxz : Set V) ∪ G.edgesIn (↑Syz : Set V)
        ⊆ G.edgesIn (↑T : Set V) := by
      rw [hT_def, Finset.coe_union]
      exact Set.union_subset (edgesIn_mono Set.subset_union_left)
                             (edgesIn_mono Set.subset_union_right)
    have hxy_nin_union : s(x, y) ∉ G.edgesIn (↑Sxz : Set V) ∪ G.edgesIn (↑Syz : Set V) := by
      rintro (h_in_Sxz | h_in_Syz)
      · exact hxy_nin_Sxz h_in_Sxz
      · exact hxy_nin_Syz h_in_Syz
    have h_combined_sub : G.edgesIn (↑Sxz : Set V) ∪ G.edgesIn (↑Syz : Set V) ∪
        {s(x, y)} ⊆ G.edgesIn (↑T : Set V) :=
      Set.union_subset h_union_sub_T (Set.singleton_subset_iff.mpr hxy_in_T)
    have h_disj_singleton : Disjoint
        (G.edgesIn (↑Sxz : Set V) ∪ G.edgesIn (↑Syz : Set V))
        ({s(x, y)} : Set (Sym2 V)) := by
      rw [Set.disjoint_right]; rintro e rfl; exact hxy_nin_union
    have h_combined_card : (G.edgesIn (↑Sxz : Set V) ∪ G.edgesIn (↑Syz : Set V) ∪
        {s(x, y)}).ncard =
        (G.edgesIn (↑Sxz : Set V) ∪ G.edgesIn (↑Syz : Set V)).ncard + 1 := by
      rw [Set.ncard_union_eq h_disj_singleton
        (Set.Finite.union (G.edgesIn_finite Sxz) (G.edgesIn_finite Syz)) (Set.toFinite _),
        Set.ncard_singleton]
    have h_count : (G.edgesIn (↑Sxz : Set V)).ncard + (G.edgesIn (↑Syz : Set V)).ncard + 1 ≤
                   (G.edgesIn (↑T : Set V)).ncard := by
      have h_card_combined_le :=
        Set.ncard_le_ncard h_combined_sub (G.edgesIn_finite T)
      omega
    refine IsLaman.False_of_three_neighbor_squeeze h hx hy hz hxy hxz hyz hvT hxT hyT hzT ?_
    unfold IsTightOn at hSxz_tight hSyz_tight
    omega

/-- **3-pair contradiction template.** Three blockers covering all three pairs of `v`'s neighbors,
all non-adjacent in `G`. If any pairwise intersection has size `≥ 2`, that pair's union is tight
(`IsTightOn.union_inter`) and contains `{a, b, c}`. Otherwise all three pairwise intersections are
singletons, the pairwise-disjoint edge sets accumulate without overlap, and the third-pair
intersection `(Sab ∪ Sac) ∩ Sbc = {b, c}` contributes zero edges (since `(b, c)` is non-adj here),
saturating the squeeze at `T := Sab ∪ Sac ∪ Sbc`. -/
private lemma IsLaman.contradiction_three_pair
    [Finite V] {G : SimpleGraph V} (h : G.IsLaman) {v a b c : V}
    (ha : G.Adj v a) (hb : G.Adj v b) (hc : G.Adj v c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hab_nadj : ¬ G.Adj a b) (hac_nadj : ¬ G.Adj a c) (hbc_nadj : ¬ G.Adj b c)
    {Sab : Finset V} (hvSab : v ∉ Sab) (haSab : a ∈ Sab) (hbSab : b ∈ Sab)
    (hSab_tight : G.IsTightOn 2 3 Sab)
    {Sac : Finset V} (hvSac : v ∉ Sac) (haSac : a ∈ Sac) (hcSac : c ∈ Sac)
    (hSac_tight : G.IsTightOn 2 3 Sac)
    {Sbc : Finset V} (hvSbc : v ∉ Sbc) (hbSbc : b ∈ Sbc) (hcSbc : c ∈ Sbc)
    (hSbc_tight : G.IsTightOn 2 3 Sbc) : False := by
  classical
  -- Sub-case A: some pairwise intersection ≥ 2. Apply union_inter and reduce to primitive.
  by_cases h_ab_ac : 2 ≤ (Sab ∩ Sac).card
  · have ⟨hT_tight, _⟩ := hSab_tight.union_inter hSac_tight h.isSparse (by omega)
    refine IsLaman.False_of_three_neighbor_squeeze h ha hb hc hab hac hbc
      (by simp only [Finset.mem_union, not_or]; exact ⟨hvSab, hvSac⟩)
      (Finset.mem_union_left _ haSab)
      (Finset.mem_union_left _ hbSab)
      (Finset.mem_union_right _ hcSac) ?_
    unfold IsTightOn at hT_tight; omega
  by_cases h_ab_bc : 2 ≤ (Sab ∩ Sbc).card
  · have ⟨hT_tight, _⟩ := hSab_tight.union_inter hSbc_tight h.isSparse (by omega)
    refine IsLaman.False_of_three_neighbor_squeeze h ha hb hc hab hac hbc
      (by simp only [Finset.mem_union, not_or]; exact ⟨hvSab, hvSbc⟩)
      (Finset.mem_union_left _ haSab)
      (Finset.mem_union_left _ hbSab)
      (Finset.mem_union_right _ hcSbc) ?_
    unfold IsTightOn at hT_tight; omega
  by_cases h_ac_bc : 2 ≤ (Sac ∩ Sbc).card
  · have ⟨hT_tight, _⟩ := hSac_tight.union_inter hSbc_tight h.isSparse (by omega)
    refine IsLaman.False_of_three_neighbor_squeeze h ha hb hc hab hac hbc
      (by simp only [Finset.mem_union, not_or]; exact ⟨hvSac, hvSbc⟩)
      (Finset.mem_union_left _ haSac)
      (Finset.mem_union_right _ hbSbc)
      (Finset.mem_union_left _ hcSac) ?_
    unfold IsTightOn at hT_tight; omega
  -- Sub-case B: all pairwise intersections have size 1 (singletons).
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
    (Finset.eq_of_subset_of_card_le
      (Finset.singleton_subset_iff.mpr (Finset.mem_inter.mpr ⟨haSab, haSac⟩))
      (by rw [Finset.card_singleton]; omega)).symm
  have hab_bc_eq : Sab ∩ Sbc = {b} :=
    (Finset.eq_of_subset_of_card_le
      (Finset.singleton_subset_iff.mpr (Finset.mem_inter.mpr ⟨hbSab, hbSbc⟩))
      (by rw [Finset.card_singleton]; omega)).symm
  have hac_bc_eq : Sac ∩ Sbc = {c} :=
    (Finset.eq_of_subset_of_card_le
      (Finset.singleton_subset_iff.mpr (Finset.mem_inter.mpr ⟨hcSac, hcSbc⟩))
      (by rw [Finset.card_singleton]; omega)).symm
  -- Step 1: bound e(Sab ∪ Sac) ≥ e(Sab) + e(Sac) using e(Sab ∩ Sac) = e({a}) = 0.
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
  -- Step 2: (Sab ∪ Sac) ∩ Sbc = {b, c}, which has 0 edges since (b, c) is non-adjacent.
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
  refine IsLaman.False_of_three_neighbor_squeeze h ha hb hc hab hac hbc hvT haT hbT hcT ?_
  unfold IsTightOn at hSab_tight hSac_tight hSbc_tight
  omega

/-- **Strengthened decomposition theorem.** Every Laman graph on `n ≥ 3` vertices is iso to a
Type I or Type II Henneberg move applied to a **Laman** graph `G'` on `{w : V // w ≠ v}`.

Strengthens `IsLaman.exists_typeI_or_typeII_iso` by additionally asserting `G'.IsLaman`. The
degree-2 branch closes via `typeI_isLaman_iff` (iso transport from `G`'s Laman to
`(typeI G' a b).IsLaman` then peel off typeI). The degree-3 branch is the deep step: pick a
non-adjacent neighbor pair via `IsLaman.exists_nonadj_among_three_neighbors`; if its typeII
reverse is Laman, return; if not, the per-pair `typeII_reverse_blocker` yields a tight
blocker, and case analysis on the three pairs assembles a tight set in `V \ {v}` containing
all three neighbors of `v`, contradicting `IsLaman.no_isTightOn_excluding_three_neighbors`.

**Phase 5 milestone 1.** -/
theorem IsLaman.exists_typeI_or_typeII_reverse [Fintype V]
    {G : SimpleGraph V} (h : G.IsLaman)
    (hV : 3 ≤ Fintype.card V) :
    ∃ (v : V) (G' : SimpleGraph {w : V // w ≠ v}), G'.IsLaman ∧
      ((∃ a b : {w : V // w ≠ v}, a ≠ b ∧ Nonempty (G ≃g typeI G' a b)) ∨
       (∃ a b c : {w : V // w ≠ v}, a ≠ b ∧ c ≠ a ∧ c ≠ b ∧ G'.Adj a b ∧
        Nonempty (G ≃g typeII G' a b c))) := by
  classical
  obtain ⟨v, hv2, hv3⟩ := h.exists_two_le_degree_le_three hV
  refine ⟨v, ?_⟩
  rcases (show G.degree v = 2 ∨ G.degree v = 3 from by omega) with hdeg | hdeg
  · -- Degree-2 case: Type I reverse on the induced subgraph.
    obtain ⟨a, b, hab, hN_eq⟩ := Finset.card_eq_two.mp hdeg
    have hN_iff : ∀ w, G.Adj v w ↔ w = a ∨ w = b := fun w => by
      rw [← mem_neighborFinset, hN_eq]; simp
    have ha_adj : G.Adj v a := (hN_iff a).mpr (Or.inl rfl)
    have hb_adj : G.Adj v b := (hN_iff b).mpr (Or.inr rfl)
    have hva : v ≠ a := G.ne_of_adj ha_adj
    have hvb : v ≠ b := G.ne_of_adj hb_adj
    have hab_s : (⟨a, hva.symm⟩ : {w : V // w ≠ v}) ≠ ⟨b, hvb.symm⟩ :=
      fun heq => hab (Subtype.mk.injEq .. |>.mp heq)
    refine ⟨G.comap (Subtype.val : {w : V // w ≠ v} → V), ?_, ?_⟩
    · exact (typeI_isLaman_iff hab_s).mp
        (IsLaman.iso (typeI_iso_of_two_neighbors hva hvb hN_iff) h)
    · exact Or.inl ⟨⟨a, hva.symm⟩, ⟨b, hvb.symm⟩, hab_s,
        ⟨typeI_iso_of_two_neighbors hva hvb hN_iff⟩⟩
  · -- Degree-3 case: case-split on the three pairs' adjacency. For each non-adjacent pair invoke
    -- `typeII_reverse_witness_or_blocker`; on success return the witness; on failure collect a
    -- blocker. Combine the accumulated blockers via the appropriate `contradiction_*_pair`
    -- helper. The all-adjacent leaf contradicts `exists_nonadj_among_three_neighbors`.
    obtain ⟨a, b, c, hab, hac, hbc, hN_eq⟩ := Finset.card_eq_three.mp hdeg
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
    by_cases hab_adj : G.Adj a b
    · by_cases hac_adj : G.Adj a c
      · -- (a, b), (a, c) adj → (b, c) non-adj by `exists_nonadj`.
        have hbc_nadj : ¬ G.Adj b c := by
          rcases h.exists_nonadj_among_three_neighbors ha_adj hb_adj hc_adj hab hac hbc with
            h' | h' | h'
          · exact absurd hab_adj h'
          · exact absurd hac_adj h'
          · exact h'
        rcases IsLaman.typeII_reverse_witness_or_blocker h hvb.symm hvc.symm hva.symm
            hbc hab hac hN_iff_bca hbc_nadj with
          ⟨G', hG'_lam, hwit⟩ | ⟨S_bc, hv_bc, hb_bc, hc_bc, hSbc_tight⟩
        · exact ⟨G', hG'_lam, Or.inr hwit⟩
        · -- 1-pair: only (b, c) non-adj; blocker for it.
          exact absurd
            (IsLaman.contradiction_one_pair h hb_adj hc_adj ha_adj hbc hab.symm hac.symm
              hab_adj.symm hac_adj.symm hv_bc hb_bc hc_bc hSbc_tight) id
      · -- (a, b) adj, (a, c) non-adj.
        rcases IsLaman.typeII_reverse_witness_or_blocker h hva.symm hvc.symm hvb.symm
            hac hab.symm hbc hN_iff_acb hac_adj with
          ⟨G', hG'_lam, hwit⟩ | ⟨S_ac, hv_ac, ha_ac, hc_ac, hSac_tight⟩
        · exact ⟨G', hG'_lam, Or.inr hwit⟩
        · by_cases hbc_adj : G.Adj b c
          · -- 1-pair: only (a, c) non-adj; blocker for it.
            exact absurd
              (IsLaman.contradiction_one_pair h ha_adj hc_adj hb_adj hac hab hbc.symm
                hab_adj hbc_adj.symm hv_ac ha_ac hc_ac hSac_tight) id
          · rcases IsLaman.typeII_reverse_witness_or_blocker h hvb.symm hvc.symm hva.symm
                hbc hab hac hN_iff_bca hbc_adj with
              ⟨G', hG'_lam, hwit⟩ | ⟨S_bc, hv_bc, hb_bc, hc_bc, hSbc_tight⟩
            · exact ⟨G', hG'_lam, Or.inr hwit⟩
            · -- 2-pair: (a, c), (b, c) non-adj, c shared; (a, b) adj.
              exact absurd
                (IsLaman.contradiction_two_pair h ha_adj hb_adj hc_adj hab hac hbc
                  hab_adj
                  hv_ac ha_ac hc_ac hSac_tight
                  hv_bc hb_bc hc_bc hSbc_tight) id
    · -- (a, b) non-adj.
      rcases IsLaman.typeII_reverse_witness_or_blocker h hva.symm hvb.symm hvc.symm
          hab hac.symm hbc.symm hN_iff hab_adj with
        ⟨G', hG'_lam, hwit⟩ | ⟨S_ab, hv_ab, ha_ab, hb_ab, hSab_tight⟩
      · exact ⟨G', hG'_lam, Or.inr hwit⟩
      · by_cases hac_adj : G.Adj a c
        · by_cases hbc_adj : G.Adj b c
          · -- 1-pair: only (a, b) non-adj; blocker for it.
            exact absurd
              (IsLaman.contradiction_one_pair h ha_adj hb_adj hc_adj hab hac hbc
                hac_adj hbc_adj hv_ab ha_ab hb_ab hSab_tight) id
          · rcases IsLaman.typeII_reverse_witness_or_blocker h hvb.symm hvc.symm hva.symm
                hbc hab hac hN_iff_bca hbc_adj with
              ⟨G', hG'_lam, hwit⟩ | ⟨S_bc, hv_bc, hb_bc, hc_bc, hSbc_tight⟩
            · exact ⟨G', hG'_lam, Or.inr hwit⟩
            · -- 2-pair: (a, b), (b, c) non-adj, b shared; (a, c) adj.
              exact absurd
                (IsLaman.contradiction_two_pair h ha_adj hc_adj hb_adj hac hab hbc.symm
                  hac_adj
                  hv_ab ha_ab hb_ab hSab_tight
                  hv_bc hc_bc hb_bc hSbc_tight) id
        · -- (a, b), (a, c) non-adj.
          rcases IsLaman.typeII_reverse_witness_or_blocker h hva.symm hvc.symm hvb.symm
              hac hab.symm hbc hN_iff_acb hac_adj with
            ⟨G', hG'_lam, hwit⟩ | ⟨S_ac, hv_ac, ha_ac, hc_ac, hSac_tight⟩
          · exact ⟨G', hG'_lam, Or.inr hwit⟩
          · by_cases hbc_adj : G.Adj b c
            · -- 2-pair: (a, b), (a, c) non-adj, a shared; (b, c) adj.
              exact absurd
                (IsLaman.contradiction_two_pair h hb_adj hc_adj ha_adj hbc hab.symm hac.symm
                  hbc_adj
                  hv_ab hb_ab ha_ab hSab_tight
                  hv_ac hc_ac ha_ac hSac_tight) id
            · rcases IsLaman.typeII_reverse_witness_or_blocker h hvb.symm hvc.symm hva.symm
                  hbc hab hac hN_iff_bca hbc_adj with
                ⟨G', hG'_lam, hwit⟩ | ⟨S_bc, hv_bc, hb_bc, hc_bc, hSbc_tight⟩
              · exact ⟨G', hG'_lam, Or.inr hwit⟩
              · -- 3-pair: all three pairs non-adj.
                exact absurd
                  (IsLaman.contradiction_three_pair h ha_adj hb_adj hc_adj hab hac hbc
                    hab_adj hac_adj hbc_adj
                    hv_ab ha_ab hb_ab hSab_tight
                    hv_ac ha_ac hc_ac hSac_tight
                    hv_bc hb_bc hc_bc hSbc_tight) id

/-! ### Rigidity preservation under Henneberg moves (dim 2)

Phase 5 milestone 2. The Type I move preserves generic rigidity in the plane: extend a rigid
placement `p` of `G` by placing the new vertex (image of `none`) at a point `q` for which the
displacements `q - p a` and `q - p b` are linearly independent. The kernel of the rigidity map
does not grow under this extension — the two new rigidity-matrix rows pin down the new vertex's
infinitesimal motion completely.

The conditional `typeI_isInfinitesimallyRigid_extend` is the rank-nullity heart of the
preservation argument. The existence-of-good-`q` step (a `q` with the requisite linear
independence, plus injectivity to feed into the next inductive step) is the dimension-2 placement
ingredient; the unconditional `typeI_isGenericallyRigid_two` waits on that piece. -/

open scoped InnerProductSpace

/-- In `EuclideanSpace ℝ (Fin 2)`, a vector `u` orthogonal to two linearly independent vectors is
zero. The size-2 LI family spans (`Fin 2`'s cardinality matches `finrank`), so the orthogonal
complement is `⊥`. -/
private lemma eq_zero_of_orthogonal_dim_two
    {v₁ v₂ u : EuclideanSpace ℝ (Fin 2)}
    (hLI : LinearIndependent ℝ ![v₁, v₂])
    (h₁ : ⟪v₁, u⟫_ℝ = 0) (h₂ : ⟪v₂, u⟫_ℝ = 0) : u = 0 := by
  have h_span_top : Submodule.span ℝ (Set.range ![v₁, v₂]) = ⊤ :=
    hLI.span_eq_top_of_card_eq_finrank (by simp)
  have h_u_perp : u ∈ (Submodule.span ℝ (Set.range ![v₁, v₂]))ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      rcases hw with ⟨i, rfl⟩
      fin_cases i
      · simpa using h₁
      · simpa using h₂
    | zero => exact inner_zero_left _
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul c x _ hx => rw [inner_smul_left, hx]; simp
  rwa [h_span_top, Submodule.top_orthogonal_eq_bot, Submodule.mem_bot] at h_u_perp

/-- **Conditional Type I rigidity preservation in dim 2.** If `p : Framework V 2` is
infinitesimally rigid for `G` and `q : EuclideanSpace ℝ (Fin 2)` is a placement of the new vertex
for which the displacements `q - p a` and `q - p b` are linearly independent, then the extended
placement `fun w => w.elim q p` is infinitesimally rigid for `typeI G a b`.

The rank-nullity heart of `typeI_isGenericallyRigid_two`. The proof builds a linear injection
from `ker ((typeI G a b).RigidityMap p_ext)` into `ker (G.RigidityMap p)` via the restriction
`x ↦ x ∘ some`: it lands in the right kernel because every `G`-edge lifts to a `typeI G a b`-edge
with the same rigidity-row formula, and it is injective because the two new edges through `none`
pin down `x none` completely whenever `q - p a` and `q - p b` are linearly independent. -/
theorem typeI_isInfinitesimallyRigid_extend [Fintype V] {G : SimpleGraph V}
    {p : Framework V 2} (hp : G.IsInfinitesimallyRigid p) {a b : V}
    {q : EuclideanSpace ℝ (Fin 2)}
    (hLI : LinearIndependent ℝ ![q - p a, q - p b]) :
    (typeI G a b).IsInfinitesimallyRigid (fun w : Option V => w.elim q p) := by
  classical
  set p_ext : Framework (Option V) 2 := fun w : Option V => w.elim q p with hp_ext_def
  -- The restriction map `x ↦ x ∘ some` lands in `ker (G.RigidityMap p)`: every `G`-edge `s(u, v)`
  -- lifts to `s(some u, some v) ∈ (typeI G a b).edgeSet` with the same rigidity-row formula.
  have h_into : ∀ x : Framework (Option V) 2,
      x ∈ LinearMap.ker ((typeI G a b).RigidityMap p_ext) →
        x ∘ some ∈ LinearMap.ker (G.RigidityMap p) := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    ext ⟨e, he⟩
    induction e with
    | h u v =>
      have h_some : s(some u, some v) ∈ (typeI G a b).edgeSet := he
      have key := congr_fun hx ⟨s(some u, some v), h_some⟩
      simp only [rigidityMap_apply, Pi.zero_apply] at key
      simpa [rigidityMap_apply] using key
  -- Kernel-to-kernel linear map.
  let restrict : LinearMap.ker ((typeI G a b).RigidityMap p_ext) →ₗ[ℝ]
      LinearMap.ker (G.RigidityMap p) :=
    { toFun := fun x => ⟨x.1 ∘ some, h_into x.1 x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  -- Injectivity: any two kernel elements agreeing on `some _` agree at `none` too, because the
  -- two new edges through `none` orthogonalize `x.1 none - y.1 none` against the LI pair
  -- `(q - p a, q - p b)`, forcing the difference to vanish.
  have h_inj : Function.Injective restrict := by
    intro x y hxy
    apply Subtype.ext
    funext w
    have h_some : ∀ v, x.1 (some v) = y.1 (some v) := fun v =>
      congr_fun (congrArg Subtype.val hxy) v
    rcases w with _ | v
    swap
    · exact h_some v
    -- Case `w = none`. Extract the two new-edge constraints for both `x` and `y`.
    have h_a_edge : s((none : Option V), some a) ∈ (typeI G a b).edgeSet := by simp
    have h_b_edge : s((none : Option V), some b) ∈ (typeI G a b).edgeSet := by simp
    have hxa := congr_fun (LinearMap.mem_ker.mp x.2) ⟨s(none, some a), h_a_edge⟩
    have hxb := congr_fun (LinearMap.mem_ker.mp x.2) ⟨s(none, some b), h_b_edge⟩
    have hya := congr_fun (LinearMap.mem_ker.mp y.2) ⟨s(none, some a), h_a_edge⟩
    have hyb := congr_fun (LinearMap.mem_ker.mp y.2) ⟨s(none, some b), h_b_edge⟩
    simp only [rigidityMap_apply, Pi.zero_apply] at hxa hxb hya hyb
    -- `p_ext none = q`, `p_ext (some _) = p _` by defeq through `set`.
    change ⟪q - p a, x.1 none - x.1 (some a)⟫_ℝ = 0 at hxa
    change ⟪q - p b, x.1 none - x.1 (some b)⟫_ℝ = 0 at hxb
    change ⟪q - p a, y.1 none - y.1 (some a)⟫_ℝ = 0 at hya
    change ⟪q - p b, y.1 none - y.1 (some b)⟫_ℝ = 0 at hyb
    have h_perp_a : ⟪q - p a, x.1 none - y.1 none⟫_ℝ = 0 := by
      have hsubst : x.1 none - y.1 none =
          (x.1 none - x.1 (some a)) - (y.1 none - y.1 (some a)) := by
        rw [h_some a]; abel
      rw [hsubst, inner_sub_right, hxa, hya, sub_zero]
    have h_perp_b : ⟪q - p b, x.1 none - y.1 none⟫_ℝ = 0 := by
      have hsubst : x.1 none - y.1 none =
          (x.1 none - x.1 (some b)) - (y.1 none - y.1 (some b)) := by
        rw [h_some b]; abel
      rw [hsubst, inner_sub_right, hxb, hyb, sub_zero]
    exact sub_eq_zero.mp (eq_zero_of_orthogonal_dim_two hLI h_perp_a h_perp_b)
  -- Rank-nullity: `finrank (ker (typeI _)) ≤ finrank (ker G) ≤ 3`.
  change Module.finrank ℝ (LinearMap.ker ((typeI G a b).RigidityMap p_ext)) ≤ 2 * (2 + 1) / 2
  exact (LinearMap.finrank_le_finrank_of_injective h_inj).trans hp

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
