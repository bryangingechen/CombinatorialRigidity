/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Data.Set.Card

/-!
# Upstream candidates: deleting the incidence set of a degree-≤-one vertex

Phase 32 (`sec:jacobs-degree-one`, L2 slice plan T2). Jackson–Jordán 2008's tree/degree-one
rank formulas (Lemma 4.2) peel a degree-one (*leaf*) vertex `v` one at a time via
`G.deleteIncidenceSet v`, tracking how a neighbor `u`'s degree and the graph's set of
degree-one vertices change under the peel. Mathlib's `Mathlib/Combinatorics/SimpleGraph/
DeleteEdges.lean` already supplies `deleteIncidenceSet` and its edge-set / support-subset
facts; this file supplies the leaf-peel-specific companions: how `neighborSet`, `degree`, and
`support` behave *exactly* (not just up to a subset/bound) once the peeled vertex has degree
at most one, plus how the set of degree-one vertices changes across the peel.

The Lean namespace is the upstream one (`SimpleGraph`), so promotion to mathlib is a
copy-paste alongside `deleteIncidenceSet_adj` / `support_deleteIncidenceSet_subset`. See
`DESIGN.md` "Mirror directory".

See `notes/Phase32.md` (the L2 slice plan, T2) for the phase plan.

## Contents (target file: `Mathlib/Combinatorics/SimpleGraph/DeleteEdges.lean`)

* `neighborSet_deleteIncidenceSet_of_ne` / `neighborSet_deleteIncidenceSet_self` — exact
  neighbor-set identities for `G.deleteIncidenceSet v` (companions to the mathlib
  `support_deleteIncidenceSet_subset`, which is only a subset bound).
* `degree_deleteIncidenceSet_of_ne_of_ne` / `degree_deleteIncidenceSet_add_one_of_adj` /
  `degree_deleteIncidenceSet_self` — the three degree corollaries of a degree-one peel at
  `v` with neighbor `u`: every other vertex's degree is unchanged, `u`'s drops by exactly
  one, and `v`'s drops to zero.
* `support_deleteIncidenceSet_of_degree_eq_one` — the exact support identity for a
  degree-one peel whose neighbor `u` keeps degree at least two after the peel (companion to
  the mathlib `support_deleteIncidenceSet_subset`, sharpened to equality under this
  hypothesis).
* `ncard_edgeSet_deleteIncidenceSet` — the `Set.ncard` form of the mathlib
  `card_edgeFinset_deleteIncidenceSet`: the peel deletes exactly `G.degree v` edges.
* `setOf_degree_eq_one_deleteIncidenceSet_of_three_le_degree` /
  `setOf_degree_eq_one_deleteIncidenceSet_of_degree_eq_two` — how the set of degree-one
  vertices changes across a degree-one peel at `v` with neighbor `u`: it loses `v` outright
  when `u` keeps degree at least three, and swaps `v` for `u` when `u`'s degree was exactly
  two (so `u` becomes a new leaf).
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-! ## Neighbor sets -/

/-- The neighbor set of any vertex `w ≠ v` is unchanged by deleting `v`'s incidence set, apart
from possibly losing `v` itself: `v` is the only vertex whose incidence with `w` `deleteIncidenceSet
v` could remove. -/
theorem neighborSet_deleteIncidenceSet_of_ne {v w : V} (h : w ≠ v) :
    (G.deleteIncidenceSet v).neighborSet w = G.neighborSet w \ {v} := by
  ext x
  simp [mem_neighborSet, deleteIncidenceSet_adj, h]

/-- Deleting `v`'s own incidence set leaves `v` with no neighbors. -/
theorem neighborSet_deleteIncidenceSet_self {v : V} :
    (G.deleteIncidenceSet v).neighborSet v = ∅ := by
  ext x
  simp [mem_neighborSet, deleteIncidenceSet_adj]

/-! ## Degree corollaries of a degree-one peel -/

/-- Peeling a degree-one vertex `v` (with neighbor `u`) leaves every other vertex's degree
unchanged: `v` cannot be a neighbor of `w` without being `w`'s *only* neighbor `u` (since `v`
has a unique neighbor), so if `w ≠ u` then `v` was never a neighbor of `w` to begin with. -/
theorem degree_deleteIncidenceSet_of_ne_of_ne {v u w : V} [Fintype (G.neighborSet v)]
    [Fintype (G.neighborSet w)] [Fintype ((G.deleteIncidenceSet v).neighborSet w)]
    (hv : G.degree v = 1) (hu : G.Adj v u) (hw1 : w ≠ v) (hw2 : w ≠ u) :
    (G.deleteIncidenceSet v).degree w = G.degree w := by
  have hnotMem : v ∉ G.neighborSet w := by
    rw [mem_neighborSet]
    intro hadj
    exact hw2 (eq_of_adj_of_degree_le_one hv.le hadj.symm hu)
  rw [← ncard_neighborSet_eq_degree, ← ncard_neighborSet_eq_degree,
      neighborSet_deleteIncidenceSet_of_ne hw1, Set.diff_singleton_eq_self hnotMem]

/-- Peeling a vertex `v` adjacent to `u` drops `u`'s degree by exactly one. -/
theorem degree_deleteIncidenceSet_add_one_of_adj {v u : V} [Fintype (G.neighborSet u)]
    [Fintype ((G.deleteIncidenceSet v).neighborSet u)] (hu : G.Adj v u) :
    (G.deleteIncidenceSet v).degree u + 1 = G.degree u := by
  rw [← ncard_neighborSet_eq_degree, ← ncard_neighborSet_eq_degree,
      neighborSet_deleteIncidenceSet_of_ne hu.ne']
  exact Set.ncard_diff_singleton_add_one ((mem_neighborSet G u v).mpr hu.symm)

/-- Peeling `v`'s own incidence set drops `v`'s degree to zero. -/
theorem degree_deleteIncidenceSet_self {v : V}
    [Fintype ((G.deleteIncidenceSet v).neighborSet v)] :
    (G.deleteIncidenceSet v).degree v = 0 := by
  rw [← ncard_neighborSet_eq_degree, neighborSet_deleteIncidenceSet_self, Set.ncard_empty]

/-! ## Support -/

/-- If `v` has degree one with neighbor `u`, and `u` keeps degree at least two, then peeling
`v`'s incidence set removes exactly `v` from the support (sharpening the unconditional
mathlib subset bound `support_deleteIncidenceSet_subset` to an equality): `u` still has a
neighbor other than `v` (from its degree bound), and no other support vertex `w` could have
lost its only witness of support to the peel, since that would force `w = u` by `v`'s
unique-neighbor property. -/
theorem support_deleteIncidenceSet_of_degree_eq_one {v u : V} [Fintype (G.neighborSet v)]
    [Fintype (G.neighborSet u)] (hv : G.degree v = 1) (hu : G.Adj v u) (h2 : 2 ≤ G.degree u) :
    (G.deleteIncidenceSet v).support = G.support \ {v} := by
  refine le_antisymm (support_deleteIncidenceSet_subset G v) ?_
  rintro w ⟨hw_supp, hwv⟩
  simp only [Set.mem_singleton_iff] at hwv
  by_cases hwu : w = u
  · subst hwu
    have hnontriv : (G.neighborSet w).Nontrivial :=
      Set.one_lt_ncard_iff_nontrivial.mp (by rw [ncard_neighborSet_eq_degree]; omega)
    obtain ⟨x, hx_mem, hx_ne⟩ := hnontriv.exists_ne v
    exact (mem_support (G.deleteIncidenceSet v)).mpr
      ⟨x, deleteIncidenceSet_adj.mpr ⟨(mem_neighborSet G w x).mp hx_mem, hwv, hx_ne⟩⟩
  · obtain ⟨x, hx⟩ := (mem_support G).mp hw_supp
    by_cases hxv : x = v
    · subst hxv
      exact absurd (eq_of_adj_of_degree_le_one hv.le hx.symm hu) hwu
    · exact (mem_support (G.deleteIncidenceSet v)).mpr
        ⟨x, deleteIncidenceSet_adj.mpr ⟨hx, hwv, hxv⟩⟩

/-! ## Edge count across a peel -/

/-- `Set.ncard` form of `card_edgeFinset_deleteIncidenceSet`: deleting the incidence set of
the vertex `v` deletes exactly `G.degree v` edges. -/
theorem ncard_edgeSet_deleteIncidenceSet [Fintype V] [DecidableRel G.Adj] (v : V) :
    (G.deleteIncidenceSet v).edgeSet.ncard = G.edgeSet.ncard - G.degree v := by
  classical
  rw [ncard_edgeSet_eq_card_edgeFinset, ncard_edgeSet_eq_card_edgeFinset,
    card_edgeFinset_deleteIncidenceSet]

/-! ## The set of degree-one vertices across a peel -/

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- If `v` has degree one with neighbor `u`, and `u` keeps degree at least three after losing
its edge to `v`, then peeling `v`'s incidence set simply removes `v` from the set of
degree-one vertices: `v` itself drops to degree zero (`degree_deleteIncidenceSet_self`), `u`
stays above degree one (`degree_deleteIncidenceSet_add_one_of_adj`), and every other vertex's
degree is unchanged (`degree_deleteIncidenceSet_of_ne_of_ne`). -/
theorem setOf_degree_eq_one_deleteIncidenceSet_of_three_le_degree {v u : V}
    (hv : G.degree v = 1) (hu : G.Adj v u) (h3 : 3 ≤ G.degree u) :
    {w | (G.deleteIncidenceSet v).degree w = 1} = {w | G.degree w = 1} \ {v} := by
  ext w
  simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_singleton_iff]
  by_cases hwv : w = v
  · subst hwv
    exact iff_of_false (by simp [degree_deleteIncidenceSet_self]) (by simp)
  · by_cases hwu : w = u
    · subst hwu
      have hdeg := degree_deleteIncidenceSet_add_one_of_adj (v := v) hu
      exact iff_of_false (by omega) (by simp; omega)
    · rw [degree_deleteIncidenceSet_of_ne_of_ne hv hu hwv hwu]
      simp [hwv]

/-- If `v` has degree one with neighbor `u`, and `u` has degree exactly two, then peeling
`v`'s incidence set swaps `v` for `u` in the set of degree-one vertices: `v` drops to degree
zero while `u` drops to degree exactly one, becoming a new leaf, and every other vertex's
degree is unchanged. -/
theorem setOf_degree_eq_one_deleteIncidenceSet_of_degree_eq_two {v u : V}
    (hv : G.degree v = 1) (hu : G.Adj v u) (h2 : G.degree u = 2) :
    {w | (G.deleteIncidenceSet v).degree w = 1} = insert u ({w | G.degree w = 1} \ {v}) := by
  ext w
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_diff, Set.mem_singleton_iff]
  by_cases hwv : w = v
  · subst hwv
    exact iff_of_false (by simp [degree_deleteIncidenceSet_self]) (by simp [hu.ne])
  · by_cases hwu : w = u
    · subst hwu
      have hdeg := degree_deleteIncidenceSet_add_one_of_adj (v := v) hu
      exact iff_of_true (by omega) (Or.inl rfl)
    · rw [degree_deleteIncidenceSet_of_ne_of_ne hv hu hwv hwu]
      simp [hwv, hwu]

end SimpleGraph
