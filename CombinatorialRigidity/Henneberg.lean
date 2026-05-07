/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Laman
import CombinatorialRigidity.Mathlib.Data.Sym.Sym2
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finite.Card
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
  classical
  have hG_fin : G.edgeSet.Finite := G.edgeSet.toFinite
  have hImg_fin : (Sym2.map some '' G.edgeSet).Finite := hG_fin.image _
  have hPair_fin : ({s(none, some a), s(none, some b)} :
      Set (Sym2 (Option V))).Finite := Set.toFinite _
  have hDisj : Disjoint (Sym2.map some '' G.edgeSet)
      ({s(none, some a), s(none, some b)} : Set (Sym2 (Option V))) := by
    rw [Set.disjoint_left]
    rintro e he hpair
    rcases hpair with rfl | rfl <;> simp at he
  rw [typeI_edgeSet, Set.ncard_union_eq hDisj hImg_fin hPair_fin,
    Set.ncard_image_of_injective _ (Sym2.map.injective (Option.some_injective V))]
  congr 1
  refine Set.ncard_pair (fun h => hab ?_)
  rw [Sym2.eq_iff] at h
  simpa using h

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
    have h_image_fin : (Sym2.map some '' G.edgesIn (↑s' : Set V)).Finite :=
      (G.edgesIn_finite s').image _
    have h_T_fin : T.Finite := ((Set.toFinite _ :
      ({s(none, some a), s(none, some b)} : Set _).Finite).inter_of_left _)
    have h_ncard : ((typeI G a b).edgesIn (↑s : Set (Option V))).ncard =
        (G.edgesIn (↑s' : Set V)).ncard + T.ncard := by
      rw [h_decomp, Set.ncard_union_eq h_disj h_image_fin h_T_fin,
        Set.ncard_image_of_injective _ (Sym2.map.injective (Option.some_injective V))]
    -- `T.ncard ≤ 2`: `T` is a subset of a 2-element set.
    have hT_le_2 : T.ncard ≤ 2 := by
      refine (Set.ncard_le_ncard Set.inter_subset_left (Set.toFinite _)).trans ?_
      calc ({s(none, some a), s(none, some b)} : Set _).ncard
          ≤ ({s(none, some b)} : Set _).ncard + 1 := Set.ncard_insert_le _ _
        _ = 2 := by rw [Set.ncard_singleton]
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
        -- `T ⊆ {s(none, some w)}`: each `e ∈ T` is `s(none, some v)` with `some v ∈ s`, so `v = w`.
        have hT_sub : T ⊆ ({s(none, some w)} : Set (Sym2 (Option V))) := by
          rintro e ⟨hpair, hsub⟩
          have hsubV : (e : Set (Option V)) ⊆ ↑s := Set.mem_sym2_iff_subset.mp hsub
          rcases hpair with rfl | rfl
          · have ha : a ∈ s' := (hmem a).mpr (hsubV (by simp))
            rw [hw, Finset.mem_singleton] at ha; exact ha ▸ rfl
          · have hb : b ∈ s' := (hmem b).mpr (hsubV (by simp))
            rw [hw, Finset.mem_singleton] at hb; exact hb ▸ rfl
        have hT_le_1 : T.ncard ≤ 1 :=
          (Set.ncard_le_ncard hT_sub (Set.toFinite _)).trans
            (le_of_eq (Set.ncard_singleton _))
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
      have hT_empty : T.ncard = 0 := by
        rw [Set.ncard_eq_zero h_T_fin, Set.eq_empty_iff_forall_notMem]
        rintro e ⟨hpair, hsub⟩
        have hsubV : (e : Set (Option V)) ⊆ ↑s := Set.mem_sym2_iff_subset.mp hsub
        rcases hpair with rfl | rfl
        · exact hnone (hsubV (by simp))
        · exact hnone (hsubV (by simp))
      have hG := h.isSparse s' (by omega)
      omega
  · -- Tightness.
    have hE := h.edgeSet_ncard
    rw [Nat.card_eq_fintype_card] at hE
    rw [typeI_edgeSet_ncard G hab, Finite.card_option, Nat.card_eq_fintype_card]
    omega

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
  classical
  have hG_fin : (G.edgeSet \ {s(a, b)}).Finite := G.edgeSet.toFinite.diff
  have hImg_fin : (Sym2.map some '' (G.edgeSet \ {s(a, b)})).Finite := hG_fin.image _
  have hTriple_fin : ({s(none, some a), s(none, some b), s(none, some c)} :
      Set (Sym2 (Option V))).Finite := Set.toFinite _
  have hDisj : Disjoint (Sym2.map some '' (G.edgeSet \ {s(a, b)}))
      ({s(none, some a), s(none, some b), s(none, some c)} :
        Set (Sym2 (Option V))) := by
    rw [Set.disjoint_left]
    rintro e he hpair
    rcases hpair with rfl | rfl | rfl <;> simp at he
  rw [typeII_edgeSet, Set.ncard_union_eq hDisj hImg_fin hTriple_fin,
    Set.ncard_image_of_injective _ (Sym2.map.injective (Option.some_injective V))]
  congr 1
  have hne_ab : s(none, some a) ≠ s(none, some b) := by simp [hab]
  have hne_ac : s(none, some a) ≠ s(none, some c) := by simp [hca.symm]
  have hne_bc : s(none, some b) ≠ s(none, some c) := by simp [hcb.symm]
  rw [show ({s(none, some a), s(none, some b), s(none, some c)} : Set (Sym2 (Option V))) =
    insert s(none, some a) (insert s(none, some b) {s(none, some c)}) from rfl,
    Set.ncard_insert_of_notMem (by simp [hne_ab, hne_ac]) (by simp),
    Set.ncard_insert_of_notMem (by simp [hne_bc]) (by simp), Set.ncard_singleton]

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
    have h_image_fin : (Sym2.map some '' (G.edgesIn (↑s' : Set V) \ {s(a, b)})).Finite :=
      ((G.edgesIn_finite s').diff).image _
    have h_T'_fin : T'.Finite := ((Set.toFinite _ :
      ({s(none, some a), s(none, some b), s(none, some c)} : Set _).Finite).inter_of_left _)
    have h_ncard : ((typeII G a b c).edgesIn (↑s : Set (Option V))).ncard =
        (G.edgesIn (↑s' : Set V) \ {s(a, b)}).ncard + T'.ncard := by
      rw [h_decomp, Set.ncard_union_eq h_disj h_image_fin h_T'_fin,
        Set.ncard_image_of_injective _ (Sym2.map.injective (Option.some_injective V))]
    -- `T'.ncard ≤ 3` always.
    have hT'_le_3 : T'.ncard ≤ 3 := by
      refine (Set.ncard_le_ncard Set.inter_subset_left (Set.toFinite _)).trans ?_
      calc ({s(none, some a), s(none, some b), s(none, some c)} : Set _).ncard
          ≤ ({s(none, some b), s(none, some c)} : Set _).ncard + 1 := Set.ncard_insert_le _ _
        _ ≤ ({s(none, some c)} : Set _).ncard + 1 + 1 :=
            Nat.add_le_add_right (Set.ncard_insert_le _ _) _
        _ = 3 := by rw [Set.ncard_singleton]
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
        have hT'_sub : T' ⊆ ({s(none, some w)} : Set (Sym2 (Option V))) := by
          rintro e ⟨hpair, hsub⟩
          have hsubV : (e : Set (Option V)) ⊆ ↑s := Set.mem_sym2_iff_subset.mp hsub
          rcases hpair with rfl | rfl | rfl
          · have ha : a ∈ s' := (hmem a).mpr (hsubV (by simp))
            rw [hw, Finset.mem_singleton] at ha; exact ha ▸ rfl
          · have hb : b ∈ s' := (hmem b).mpr (hsubV (by simp))
            rw [hw, Finset.mem_singleton] at hb; exact hb ▸ rfl
          · have hc : c ∈ s' := (hmem c).mpr (hsubV (by simp))
            rw [hw, Finset.mem_singleton] at hc; exact hc ▸ rfl
        have hT'_le_1 : T'.ncard ≤ 1 :=
          (Set.ncard_le_ncard hT'_sub (Set.toFinite _)).trans
            (le_of_eq (Set.ncard_singleton _))
        omega
      · -- s'.card ≥ 2: case-split on whether `s(a, b) ∈ G.edgesIn ↑s'`.
        have hG := h.isSparse s' (by omega)
        by_cases h_ab_in : s(a, b) ∈ G.edgesIn (↑s' : Set V)
        · -- `s(a, b) ∈ G.edgesIn ↑s'`: deletion removes one, `T'.ncard ≤ 3` works.
          have hdiff : (G.edgesIn (↑s' : Set V) \ {s(a, b)}).ncard =
              (G.edgesIn (↑s' : Set V)).ncard - 1 :=
            Set.ncard_diff_singleton_of_mem h_ab_in
          have hG_pos : 0 < (G.edgesIn (↑s' : Set V)).ncard :=
            (Set.ncard_pos (G.edgesIn_finite s')).mpr ⟨_, h_ab_in⟩
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
            exact h_ab_in ⟨hG_ab, by
              rw [Set.mem_sym2_iff_subset]
              intro x hx
              rw [Sym2.coe_mk] at hx
              rcases hx with rfl | rfl
              · exact h_both.1
              · exact h_both.2⟩
          -- Then T'.ncard ≤ 2: whichever of `a, b` is not in `s'` contributes no edge to `T'`.
          have hT'_le_2 : T'.ncard ≤ 2 := by
            rcases h_or with ha | hb
            · -- `a ∉ s'`: `s(none, some a) ∉ T'`. So T' ⊆ {s(none, some b), s(none, some c)}.
              refine (Set.ncard_le_ncard (?_ : T' ⊆
                  ({s(none, some b), s(none, some c)} : Set _)) (Set.toFinite _)).trans ?_
              · rintro e ⟨hpair, hsub⟩
                have hsubV : (e : Set (Option V)) ⊆ ↑s := Set.mem_sym2_iff_subset.mp hsub
                rcases hpair with rfl | rfl | rfl
                · exact (ha ((hmem a).mpr (hsubV (by simp)))).elim
                · exact Set.mem_insert _ _
                · exact Set.mem_insert_of_mem _ rfl
              · calc ({s(none, some b), s(none, some c)} : Set _).ncard
                    ≤ ({s(none, some c)} : Set _).ncard + 1 := Set.ncard_insert_le _ _
                  _ = 2 := by rw [Set.ncard_singleton]
            · -- `b ∉ s'`: `s(none, some b) ∉ T'`. So T' ⊆ {s(none, some a), s(none, some c)}.
              refine (Set.ncard_le_ncard (?_ : T' ⊆
                  ({s(none, some a), s(none, some c)} : Set _)) (Set.toFinite _)).trans ?_
              · rintro e ⟨hpair, hsub⟩
                have hsubV : (e : Set (Option V)) ⊆ ↑s := Set.mem_sym2_iff_subset.mp hsub
                rcases hpair with rfl | rfl | rfl
                · exact Set.mem_insert _ _
                · exact (hb ((hmem b).mpr (hsubV (by simp)))).elim
                · exact Set.mem_insert_of_mem _ rfl
              · calc ({s(none, some a), s(none, some c)} : Set _).ncard
                    ≤ ({s(none, some c)} : Set _).ncard + 1 := Set.ncard_insert_le _ _
                  _ = 2 := by rw [Set.ncard_singleton]
          omega
    · -- Case `none ∉ s`. Then `T'.ncard = 0` and `s.card = s'.card`.
      have hs_eq : s = s'.image some := by
        ext x; cases x
        · simp [hnone]
        · simp [hmem]
      have hsc : s.card = s'.card := by
        rw [hs_eq, Finset.card_image_of_injective _ (Option.some_injective V)]
      have hT'_empty : T'.ncard = 0 := by
        rw [Set.ncard_eq_zero h_T'_fin, Set.eq_empty_iff_forall_notMem]
        rintro e ⟨hpair, hsub⟩
        have hsubV : (e : Set (Option V)) ⊆ ↑s := Set.mem_sym2_iff_subset.mp hsub
        rcases hpair with rfl | rfl | rfl
        all_goals exact hnone (hsubV (by simp))
      have hG := h.isSparse s' (by omega)
      have hdiff_le : (G.edgesIn (↑s' : Set V) \ {s(a, b)}).ncard ≤
          (G.edgesIn (↑s' : Set V)).ncard :=
        Set.ncard_diff_singleton_le _ _
      omega
  · -- Tightness.
    have hE := h.edgeSet_ncard
    rw [Nat.card_eq_fintype_card] at hE
    have hab_in : s(a, b) ∈ G.edgeSet := hG_ab
    have hG_pos : 0 < G.edgeSet.ncard :=
      (Set.ncard_pos G.edgeSet.toFinite).mpr ⟨_, hab_in⟩
    have hdiff : (G.edgeSet \ {s(a, b)}).ncard = G.edgeSet.ncard - 1 :=
      Set.ncard_diff_singleton_of_mem hab_in
    rw [typeII_edgeSet_ncard G hab hca hcb, hdiff,
        Finite.card_option, Nat.card_eq_fintype_card]
    omega

end Henneberg

end SimpleGraph
