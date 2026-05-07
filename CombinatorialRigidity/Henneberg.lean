/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Laman
import CombinatorialRigidity.Mathlib.Data.Set.Card
import CombinatorialRigidity.Mathlib.Data.Sym.Sym2
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finite.Card
import Mathlib.Logic.Equiv.Option
import Mathlib.Tactic.IntervalCases

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
`s.sym2`. The two helpers below isolate the recurring set-cardinality steps used in the sparsity
case analysis. -/

/-- If `none ∉ s`, no fresh edge `s(none, some _)` lies in `s.sym2`, so any subset of fresh edges
intersected with `s.sym2` has cardinality `0`. -/
private lemma fresh_sym2_ncard_eq_zero_of_none_notMem [Finite V] {s : Finset (Option V)}
    (hnone : none ∉ s) (xs : Set (Sym2 (Option V))) (h_xs : ∀ e ∈ xs, none ∈ e) :
    (xs ∩ ((↑s : Set (Option V)).sym2)).ncard = 0 := by
  rw [Set.ncard_eq_zero, Set.eq_empty_iff_forall_notMem]
  rintro e ⟨he, hsub⟩
  exact hnone (Set.mem_sym2_iff_subset.mp hsub (h_xs e he))

/-- If the `some`-preimage of `s` is the singleton `{w}`, every fresh edge `s(none, some x)` that
lies in `s.sym2` satisfies `x = w`, so the intersection with `s.sym2` is contained in
`{s(none, some w)}`. -/
private lemma fresh_sym2_subset_singleton {s : Finset (Option V)} {s' : Finset V}
    (hmem : ∀ v : V, v ∈ s' ↔ some v ∈ s) {w : V} (hw : s' = {w})
    (xs : Set (Sym2 (Option V))) (h_xs : ∀ e ∈ xs, ∃ x : V, e = s(none, some x)) :
    xs ∩ ((↑s : Set (Option V)).sym2) ⊆ ({s(none, some w)} : Set _) := by
  rintro e ⟨he, hsub⟩
  obtain ⟨x, rfl⟩ := h_xs e he
  rw [Set.mem_sym2_iff_subset, Sym2.coe_mk] at hsub
  have hx : x ∈ s' := (hmem _).mpr (hsub (Or.inr rfl))
  rw [hw, Finset.mem_singleton] at hx
  exact hx ▸ rfl

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
      ({s(none, some a), s(none, some b)} : Set (Sym2 (Option V))) := by
    rw [Set.disjoint_left]
    rintro e he hpair
    rcases hpair with rfl | rfl <;> simp at he
  rw [typeI_edgeSet, Set.ncard_union_eq hDisj,
    Set.ncard_image_of_injective _ Sym2.map_some_injective, Set.ncard_pair (by simp [hab])]

/-! ### Type I preserves the Laman property -/

/-- The Type I Henneberg move preserves the Laman property: if `G` is Laman and `a ≠ b`, then
`typeI G a b` is Laman. Tightness follows from `typeI_edgeSet_ncard` and `Finite.card_option`;
sparsity is by case analysis on `none ∈ s` and on the cardinality of the `some`-preimage `s'`. -/
theorem typeI_isLaman [Finite V] {G : SimpleGraph V} (h : G.IsLaman)
    {a b : V} (hab : a ≠ b) : (typeI G a b).IsLaman := by
  classical
  have : Fintype V := Fintype.ofFinite V
  refine ⟨fun s hs_pre => ?_, ?_⟩
  · -- Sparsity. Define `s'` to be the `some`-preimage of `s` (the "old" vertices in `s`).
    set s' : Finset V := s.preimage some (Option.some_injective V).injOn with hs'_def
    have hmem : ∀ v : V, v ∈ s' ↔ some v ∈ s := fun _ => Finset.mem_preimage
    have hcoe : (s' : Set V) = some ⁻¹' (↑s : Set (Option V)) := Finset.coe_preimage s _
    -- Decompose `(typeI G a b).edgesIn ↑s` as old edges (image of `G.edgesIn ↑s'`) plus new edges
    -- (a subset of `{s(none, some a), s(none, some b)}` constrained to lie in `(↑s).sym2`).
    set T : Set (Sym2 (Option V)) :=
      ({s(none, some a), s(none, some b)} : Set _) ∩ ((↑s : Set (Option V)).sym2) with hT_def
    have h_decomp : (typeI G a b).edgesIn (↑s : Set (Option V)) =
        Sym2.map some '' G.edgesIn (↑s' : Set V) ∪ T := by
      ext e
      induction e with | h x y => ?_
      rcases x with _ | u <;> rcases y with _ | v <;>
        simp [edgesIn, hcoe, Set.mem_preimage, T]
    have h_disj : Disjoint (Sym2.map some '' G.edgesIn (↑s' : Set V)) T := by
      rw [Set.disjoint_left]
      rintro e he ⟨hpair, _⟩
      rcases hpair with rfl | rfl <;> simp at he
    have h_ncard : ((typeI G a b).edgesIn (↑s : Set (Option V))).ncard =
        (G.edgesIn (↑s' : Set V)).ncard + T.ncard := by
      rw [h_decomp, Set.ncard_union_eq h_disj,
        Set.ncard_image_of_injective _ Sym2.map_some_injective]
    -- `T.ncard ≤ 2`: `T` is a subset of a 2-element set.
    have hT_le_2 : T.ncard ≤ 2 :=
      (Set.ncard_le_ncard Set.inter_subset_left).trans (Set.ncard_pair_le _ _)
    -- Case-split on whether `none ∈ s`.
    by_cases hnone : none ∈ s
    · -- Case `none ∈ s`. Then `s = insert none (s'.image some)`, so `s.card = s'.card + 1`.
      have hni : none ∉ s'.image some := by simp
      have hs_eq : s = insert none (s'.image some) := by
        ext x; cases x <;> simp [hmem, hnone]
      have hsc : s.card = s'.card + 1 := by
        rw [hs_eq, Finset.card_insert_of_notMem hni,
            Finset.card_image_of_injective _ (Option.some_injective V)]
      -- Sub-case on `s'.card`: 0 (vacuous), 1 (singleton), ≥ 2 (use sparsity).
      rcases (show s'.card = 0 ∨ s'.card = 1 ∨ 2 ≤ s'.card from by omega)
        with h0 | h1 | hge
      · -- s'.card = 0: precondition fails (`s.card = 1`).
        omega
      · -- s'.card = 1: `s' = {w}`. Then `(G.edgesIn ↑s').ncard = 0` and `T.ncard ≤ 1`.
        obtain ⟨w, hw⟩ : ∃ w, s' = {w} := Finset.card_eq_one.mp h1
        have hG_empty : (G.edgesIn (↑s' : Set V)).ncard = 0 := by rw [hw]; simp
        have hT_sub : T ⊆ ({s(none, some w)} : Set _) :=
          fresh_sym2_subset_singleton hmem hw _
            (by rintro e (rfl | rfl); exacts [⟨a, rfl⟩, ⟨b, rfl⟩])
        have hT_le_1 : T.ncard ≤ 1 :=
          (Set.ncard_le_ncard hT_sub).trans (le_of_eq (Set.ncard_singleton _))
        omega
      · -- s'.card ≥ 2: apply `G`'s sparsity on `s'`.
        have hG := h.isSparse s' (by omega)
        omega
    · -- Case `none ∉ s`. Then `T.ncard = 0` and `s.card = s'.card`.
      have hs_eq : s = s'.image some := by
        ext x; cases x
        · simp [hnone]
        · simp [hmem]
      have hsc : s.card = s'.card := by
        rw [hs_eq, Finset.card_image_of_injective _ (Option.some_injective V)]
      have hT_empty : T.ncard = 0 :=
        fresh_sym2_ncard_eq_zero_of_none_notMem hnone _ (by rintro e (rfl | rfl) <;> simp)
      have hG := h.isSparse s' (by omega)
      omega
  · -- Tightness.
    grind only [!typeI_edgeSet_ncard, !Finite.card_option, h.edgeSet_ncard]

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
        Set (Sym2 (Option V))) := by
    rw [Set.disjoint_left]
    rintro e he hpair
    rcases hpair with rfl | rfl | rfl <;> simp at he
  rw [typeII_edgeSet, Set.ncard_union_eq hDisj,
    Set.ncard_image_of_injective _ Sym2.map_some_injective,
    Set.ncard_insert_of_notMem (by simp [hab, hca.symm]) (by simp),
    Set.ncard_pair (by simp [hcb.symm])]

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
  · -- Sparsity.
    set s' : Finset V := s.preimage some (Option.some_injective V).injOn with hs'_def
    have hmem : ∀ v : V, v ∈ s' ↔ some v ∈ s := fun _ => Finset.mem_preimage
    have hcoe : (s' : Set V) = some ⁻¹' (↑s : Set (Option V)) := Finset.coe_preimage s _
    -- Decompose `(typeII G a b c).edgesIn ↑s` as deleted-old-edges (image of `G.edgesIn ↑s'` minus
    -- `s(a, b)`) plus new edges (a subset of `{s(none, some a), s(none, some b), s(none, some c)}`
    -- constrained to lie in `(↑s).sym2`).
    set T' : Set (Sym2 (Option V)) :=
      ({s(none, some a), s(none, some b), s(none, some c)} : Set _) ∩
        ((↑s : Set (Option V)).sym2) with hT'_def
    have h_decomp : (typeII G a b c).edgesIn (↑s : Set (Option V)) =
        Sym2.map some '' (G.edgesIn (↑s' : Set V) \ {s(a, b)}) ∪ T' := by
      ext e
      induction e with | h x y => ?_
      rcases x with _ | u <;> rcases y with _ | v <;>
        (simp [edgesIn, hcoe, Set.mem_preimage, T']; try tauto)
    have h_disj : Disjoint (Sym2.map some '' (G.edgesIn (↑s' : Set V) \ {s(a, b)})) T' := by
      rw [Set.disjoint_left]
      rintro e he ⟨hpair, _⟩
      rcases hpair with rfl | rfl | rfl <;> simp at he
    have h_ncard : ((typeII G a b c).edgesIn (↑s : Set (Option V))).ncard =
        (G.edgesIn (↑s' : Set V) \ {s(a, b)}).ncard + T'.ncard := by
      rw [h_decomp, Set.ncard_union_eq h_disj,
        Set.ncard_image_of_injective _ Sym2.map_some_injective]
    -- `T'.ncard ≤ 3` always.
    have hT'_le_3 : T'.ncard ≤ 3 :=
      (Set.ncard_le_ncard Set.inter_subset_left).trans (Set.ncard_triple_le _ _ _)
    -- Case-split on whether `none ∈ s`.
    by_cases hnone : none ∈ s
    · -- Case `none ∈ s`. Then `s.card = s'.card + 1`.
      have hni : none ∉ s'.image some := by simp
      have hs_eq : s = insert none (s'.image some) := by
        ext x; cases x <;> simp [hmem, hnone]
      have hsc : s.card = s'.card + 1 := by
        rw [hs_eq, Finset.card_insert_of_notMem hni,
            Finset.card_image_of_injective _ (Option.some_injective V)]
      -- Sub-case on `s'.card`.
      rcases (show s'.card = 0 ∨ s'.card = 1 ∨ 2 ≤ s'.card from by omega)
        with h0 | h1 | hge
      · omega -- vacuous: precondition fails
      · -- s'.card = 1: `s' = {w}`. Singleton means no `G`-edges; `T' ⊆ {s(none, some w)}`.
        obtain ⟨w, hw⟩ : ∃ w, s' = {w} := Finset.card_eq_one.mp h1
        have hG_empty : (G.edgesIn (↑s' : Set V) \ {s(a, b)}).ncard = 0 := by
          have : (G.edgesIn (↑s' : Set V)) = ∅ := by rw [hw]; simp
          rw [this]; simp
        have hT'_sub : T' ⊆ ({s(none, some w)} : Set _) :=
          fresh_sym2_subset_singleton hmem hw _
            (by rintro e (rfl | rfl | rfl); exacts [⟨a, rfl⟩, ⟨b, rfl⟩, ⟨c, rfl⟩])
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
            refine h_ab_in ⟨hG_ab, Set.mem_sym2_iff_subset.mpr ?_⟩
            rw [Sym2.coe_mk]
            rintro _ (rfl | rfl)
            exacts [h_both.1, h_both.2]
          -- Then T'.ncard ≤ 2: whichever of `a, b` is not in `s'` contributes no edge to `T'`.
          have hT'_le_2 : T'.ncard ≤ 2 := by
            rcases h_or with ha | hb
            · -- `a ∉ s'`: `s(none, some a) ∉ T'`. So T' ⊆ {s(none, some b), s(none, some c)}.
              refine (Set.ncard_le_ncard (?_ : T' ⊆
                  ({s(none, some b), s(none, some c)} : Set _))).trans
                (Set.ncard_pair_le _ _)
              rintro e ⟨hpair, hsub⟩
              have hsubV : (e : Set (Option V)) ⊆ ↑s := Set.mem_sym2_iff_subset.mp hsub
              rcases hpair with rfl | rfl | rfl
              · exact (ha ((hmem a).mpr (hsubV (by simp)))).elim
              · exact Set.mem_insert _ _
              · exact Set.mem_insert_of_mem _ rfl
            · -- `b ∉ s'`: `s(none, some b) ∉ T'`. So T' ⊆ {s(none, some a), s(none, some c)}.
              refine (Set.ncard_le_ncard (?_ : T' ⊆
                  ({s(none, some a), s(none, some c)} : Set _))).trans
                (Set.ncard_pair_le _ _)
              rintro e ⟨hpair, hsub⟩
              have hsubV : (e : Set (Option V)) ⊆ ↑s := Set.mem_sym2_iff_subset.mp hsub
              rcases hpair with rfl | rfl | rfl
              · exact Set.mem_insert _ _
              · exact (hb ((hmem b).mpr (hsubV (by simp)))).elim
              · exact Set.mem_insert_of_mem _ rfl
          omega
    · -- Case `none ∉ s`. Then `T'.ncard = 0` and `s.card = s'.card`.
      have hs_eq : s = s'.image some := by
        ext x; cases x
        · simp [hnone]
        · simp [hmem]
      have hsc : s.card = s'.card := by
        rw [hs_eq, Finset.card_image_of_injective _ (Option.some_injective V)]
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

/-- Iso from `G` to a Type I move applied to its induced subgraph on `{w // w ≠ v}`, when `v` is a
degree-2 vertex with neighbors `a, b`. The membership-style hypothesis `hN` says `N(v) = {a, b}`. -/
private def typeI_iso_of_two_neighbors [DecidableEq V] {G : SimpleGraph V} {v a b : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hN : ∀ w, G.Adj v w ↔ w = a ∨ w = b) :
    G ≃g typeI (G.comap (Subtype.val : {w : V // w ≠ v} → V))
      ⟨a, hva.symm⟩ ⟨b, hvb.symm⟩ where
  toEquiv := (Equiv.optionSubtypeNe v).symm
  map_rel_iff' {u w} := by
    by_cases hu : u = v <;> by_cases hw : w = v
    · subst hu; subst hw
      simp
    · subst hu
      rw [Equiv.optionSubtypeNe_symm_self, Equiv.optionSubtypeNe_symm_of_ne hw,
        typeI_adj_none_some, hN]
      simp
    · subst hw
      rw [Equiv.optionSubtypeNe_symm_of_ne hu, Equiv.optionSubtypeNe_symm_self,
        typeI_adj_some_none, ← G.adj_comm, hN]
      simp
    · rw [Equiv.optionSubtypeNe_symm_of_ne hu, Equiv.optionSubtypeNe_symm_of_ne hw,
        typeI_adj_some_some, comap_adj]

/-- Iso from `G` to a Type II move applied to (induced subgraph + bridging edge `s(a, b)`), when
`v` has degree 3 with neighbors `a, b, c` and `a, b` are non-adjacent in `G`. -/
private def typeII_iso_of_three_neighbors [DecidableEq V] {G : SimpleGraph V} {v a b c : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hvc : v ≠ c)
    (hab : a ≠ b)
    (hN : ∀ w, G.Adj v w ↔ w = a ∨ w = b ∨ w = c) (hnab : ¬ G.Adj a b) :
    G ≃g typeII (G.comap (Subtype.val : {w : V // w ≠ v} → V) ⊔
        fromEdgeSet ({s(⟨a, hva.symm⟩, ⟨b, hvb.symm⟩)} : Set (Sym2 _)))
      ⟨a, hva.symm⟩ ⟨b, hvb.symm⟩ ⟨c, hvc.symm⟩ where
  toEquiv := (Equiv.optionSubtypeNe v).symm
  map_rel_iff' {u w} := by
    by_cases hu : u = v <;> by_cases hw : w = v
    · subst hu; subst hw
      simp
    · subst hu
      rw [Equiv.optionSubtypeNe_symm_self, Equiv.optionSubtypeNe_symm_of_ne hw,
        typeII_adj_none_some, hN]
      simp
    · subst hw
      rw [Equiv.optionSubtypeNe_symm_of_ne hu, Equiv.optionSubtypeNe_symm_self,
        typeII_adj_some_none, ← G.adj_comm, hN]
      simp
    · rw [Equiv.optionSubtypeNe_symm_of_ne hu, Equiv.optionSubtypeNe_symm_of_ne hw,
        typeII_adj_some_some, sup_adj, comap_adj, fromEdgeSet_adj,
        Set.mem_singleton_iff]
      -- Forward: contradiction from the deletion clause. Backward: lift the subtype-level Sym2
      -- equality through `Subtype.val` to `s(u, w) = s(a, b)`, then case-split to hit `¬G.Adj a b`.
      refine ⟨fun h => h.1.elim id (fun ⟨hL, _⟩ => absurd hL h.2),
        fun hadj => ⟨Or.inl hadj, fun heq => ?_⟩⟩
      have : s(u, w) = s(a, b) := by simpa using congrArg (Sym2.map Subtype.val) heq
      rcases Sym2.eq_iff.mp this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      exacts [hnab hadj, hnab hadj.symm]

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
