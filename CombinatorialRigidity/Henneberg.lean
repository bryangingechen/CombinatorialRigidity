/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Laman
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Maps

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
  refine e.ind fun x y => ?_
  simp only [mem_edgeSet, Set.mem_union, Set.mem_image, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · intro hAdj
    rcases x with _ | u <;> rcases y with _ | v
    · exact (hAdj : False).elim
    · refine Or.inr ((typeI_adj_none_some.mp hAdj).imp ?_ ?_) <;>
        rintro rfl <;> rw [Sym2.eq_iff] <;> tauto
    · refine Or.inr ((typeI_adj_some_none.mp hAdj).imp ?_ ?_) <;>
        rintro rfl <;> rw [Sym2.eq_iff] <;> tauto
    · exact Or.inl ⟨s(u, v), typeI_adj_some_some.mp hAdj, rfl⟩
  · rintro (⟨e', heG, hmap⟩ | hnew)
    · revert hmap heG
      refine e'.ind fun p q heG hmap => ?_
      rw [Sym2.map_mk] at hmap
      rcases x with _ | u <;> rcases y with _ | v <;>
        rw [Sym2.eq_iff] at hmap
      · simp_all
      · simp_all
      · simp_all
      · simp only [Option.some.injEq] at hmap
        rcases hmap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact heG
        · exact heG.symm
    · rcases hnew with hnew | hnew <;> rw [Sym2.eq_iff] at hnew <;>
        rcases x with _ | u <;> rcases y with _ | v <;> simp_all

/-- An edge of the form `Sym2.map some e'` cannot equal an edge with `none` as an endpoint. This is
the keystone for disjointness arguments separating "old" and "new" edges in `typeI`/`typeII`. -/
private lemma sym2_map_some_ne_pair_with_none {α : Type*} (e' : Sym2 α) (x : α) :
    Sym2.map some e' ≠ s(none, some x) := by
  refine e'.ind fun p q heq => ?_
  rw [Sym2.map_mk, Sym2.eq_iff] at heq
  simp at heq

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
    rintro e ⟨e', _, rfl⟩ hpair
    rcases hpair with hpair | hpair
    · exact sym2_map_some_ne_pair_with_none e' a hpair
    · exact sym2_map_some_ne_pair_with_none e' b hpair
  rw [typeI_edgeSet, Set.ncard_union_eq hDisj hImg_fin hPair_fin,
    Set.ncard_image_of_injective _ (Sym2.map.injective (Option.some_injective V))]
  congr 1
  refine Set.ncard_pair (fun h => hab ?_)
  rw [Sym2.eq_iff] at h
  simpa using h

end Henneberg

end SimpleGraph
