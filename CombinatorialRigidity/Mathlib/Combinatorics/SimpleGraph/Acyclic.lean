/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Set.Subsingleton

/-!
# Upstream candidates: leaf existence on a graph's own support

Phase 32 (`sec:jacobs-degree-one`, L2 slice plan T2 second half). Jackson–Jordán 2008's
degree-one rank formulas (Lemma 4.2) peel a leaf at each inductive step; this file supplies
the existence half — an acyclic graph whose support has at least two vertices and is
reachability-connected (the support-relative strengthening the induction runs on, rather than
`G.Connected` on all of `V`) has a degree-one vertex, obtained by restricting mathlib's
`IsTree.exists_vert_degree_one_of_nontrivial` to the induced subgraph on the support.

The Lean namespace is the upstream one (`SimpleGraph`), so promotion to mathlib is a
copy-paste alongside `IsTree.exists_vert_degree_one_of_nontrivial`. See `DESIGN.md` "Mirror
directory".

See `notes/Phase32.md` (the L2 slice plan, T2) for the phase plan.

## Contents (target file: `Mathlib/Combinatorics/SimpleGraph/Acyclic.lean`)

* `exists_degree_eq_one` — an acyclic graph with a reachability-connected support of at least
  two vertices has a degree-one support vertex: the induced subgraph on the support is a
  nontrivial tree (`connected_induce_support` + `IsAcyclic.induce`), so
  `IsTree.exists_vert_degree_one_of_nontrivial` supplies a degree-one vertex there, and
  `degree_induce_of_support_subset` transports its degree back to `G`.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- An acyclic graph with a reachability-connected support of at least two vertices has a
degree-one support vertex. The induced subgraph on the support is connected
(`connected_induce_support`) and acyclic (`IsAcyclic.induce`), hence a nontrivial tree, so
`IsTree.exists_vert_degree_one_of_nontrivial` supplies a degree-one vertex there; its degree
agrees with its `G`-degree since the support already contains all of its neighbors
(`degree_induce_of_support_subset`). -/
theorem exists_degree_eq_one [Fintype V] [DecidableRel G.Adj]
    (hconn : ∀ x ∈ G.support, ∀ y ∈ G.support, G.Reachable x y)
    (hac : G.IsAcyclic) (h2 : 2 ≤ G.support.ncard) :
    ∃ v ∈ G.support, G.degree v = 1 := by
  classical
  have hne : G.support.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  haveI : Nontrivial ↥G.support := Set.nontrivial_coe_sort.mpr (by
    rw [← Set.one_lt_ncard_iff_nontrivial]; omega)
  have htree : (G.induce G.support).IsTree :=
    ⟨connected_induce_support hconn hne, hac.induce G.support⟩
  obtain ⟨v, hv⟩ := htree.exists_vert_degree_one_of_nontrivial
  have hdeg : (G.induce G.support).degree v = G.degree v.val :=
    degree_induce_of_support_subset (le_refl G.support) v
  exact ⟨v.val, v.property, hdeg.symm.trans hv⟩

end SimpleGraph
