/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Deficiency

/-!
# The shadowing multigraph carrier (`lem:molecule-graph-carrier`)

Phase 26, leaf F4 (the carrier bridge; `notes/Phase26.md`). The molecular / panel-hinge
machinery (`Molecular/Molecule/{Modelling,Dictionary}.lean`) is stated over a multigraph
`Graph V β` with a separate edge-label set, while the square graph `G²` and its `3`-D
generic bar-joint rigidity matroid (Phase 24) live over a `SimpleGraph V`. This file supplies
the canonical bridge between them: a multigraph `G.shadowGraph` on the same vertex set `V`
with one edge for every adjacency of `G` and strictly more than `6(|V|-1)` edge labels
available in total — enough to meet the label-supply hypothesis
`hcard : 6 * (Nat.card α - 1) < Nat.card β` of Theorem 5.6's general-position producer
`exists_molecular_rankHypothesis_generalPosition`.

The label type is `Sym2 V ⊕ Fin (6 * (Nat.card V - 1) + 1)`: the `Sym2 V` half carries one
label per unordered pair of vertices (so `G.shadowGraph` is spanning and simple, with an edge
between distinct `u, v` iff `G.Adj u v`), and the `Fin (6 * (Nat.card V - 1) + 1)` half is
pure padding — never linked to anything — whose sole purpose is to push the label count
strictly above `6(|V|-1)`, since `Sym2 V` alone is too small on a sparse graph (e.g. for
`Nat.card V ≤ 10`, `Nat.card (Sym2 V) = Nat.card V * (Nat.card V + 1) / 2` does not exceed
`6 * (Nat.card V - 1)`).

See `notes/Phase26.md` and `blueprint/src/chapter/molecule-application.tex`
(`lem:molecule-graph-carrier`). The companion fact that `deficiency` is thereby a
well-defined adjacency-only invariant (any two such carriers agree) is not formalized here —
the rank-formula assembly fixes a single carrier throughout, so that invariance is not on the
critical path; see `notes/Phase26.md` for the pin.

## Main results

* `SimpleGraph.shadowGraph` — the canonical shadowing multigraph carrier.
* `SimpleGraph.shadowGraph_simple` — it is simple.
* `SimpleGraph.shadowGraph_vertexSet` — it is spanning.
* `SimpleGraph.shadowGraph_isLink_iff` — its links realize exactly the adjacencies of `G`.
* `SimpleGraph.card_shadowLabel_lt` — its label supply exceeds `6(|V|-1)`.
-/

open scoped Graph

namespace SimpleGraph

variable {V : Type*} [Finite V]

/-- **The shadowing multigraph carrier** (`lem:molecule-graph-carrier`) of a simple graph `G` on
a finite vertex set: the multigraph on `V` with label type `Sym2 V ⊕ Fin (6*(|V|-1)+1)` whose
links realize exactly the adjacencies of `G`, each tagged by its (unordered) endpoint pair in the
`Sym2 V` summand. The `Fin (6*(|V|-1)+1)` summand supplies pure padding labels, never linked to
anything, so that the total label count strictly exceeds `6*(|V|-1)` regardless of how sparse `G`
is. -/
def shadowGraph (G : SimpleGraph V) :
    Graph V (Sym2 V ⊕ Fin (6 * (Nat.card V - 1) + 1)) where
  vertexSet := Set.univ
  IsLink e x y := G.Adj x y ∧ Sum.inl s(x, y) = e
  isLink_symm e _ x y h :=
    ⟨h.1.symm, (congrArg Sum.inl (Sym2.eq_swap (a := y) (b := x))).trans h.2⟩
  eq_or_eq_of_isLink_of_isLink e x y v w h1 h2 := by
    have hs : s(x, y) = s(v, w) := Sum.inl_injective (h1.2.trans h2.2.symm)
    rcases Sym2.eq_iff.mp hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  left_mem_of_isLink _ x _ _ := Set.mem_univ x

omit [Finite V] in
/-- `G.shadowGraph` is simple: distinct edges never share both endpoints (the `Sym2 V` tag
determines the edge), and no edge is a loop (`G.Adj` is irreflexive). -/
theorem shadowGraph_simple (G : SimpleGraph V) : G.shadowGraph.Simple where
  not_isLoopAt _ _x h := h.1.ne rfl
  eq_of_isLink _ _ _ _ he hf := he.2.symm.trans hf.2

omit [Finite V] in
/-- `G.shadowGraph` is spanning: its vertex set is all of `V`. -/
@[simp] theorem shadowGraph_vertexSet (G : SimpleGraph V) : V(G.shadowGraph) = Set.univ := rfl

omit [Finite V] in
/-- `G.shadowGraph` has an edge between `x` and `y` iff `G.Adj x y` — the defining shadow
property. (True unconditionally; the `x ≠ y` guard some consumers carry follows since `G.Adj`
is irreflexive.) -/
theorem shadowGraph_isLink_iff (G : SimpleGraph V) (x y : V) :
    (∃ e, G.shadowGraph.IsLink e x y) ↔ G.Adj x y :=
  ⟨fun ⟨_, h⟩ => h.1, fun h => ⟨Sum.inl s(x, y), h, rfl⟩⟩

/-- The label supply of `G.shadowGraph` strictly exceeds `6*(|V|-1)`, regardless of `G`: the
`Fin (6*(|V|-1)+1)` padding summand alone already has that many labels. -/
theorem card_shadowLabel_lt (V : Type*) [Finite V] :
    6 * (Nat.card V - 1) < Nat.card (Sym2 V ⊕ Fin (6 * (Nat.card V - 1) + 1)) := by
  rw [Nat.card_sum, Nat.card_fin]
  omega

end SimpleGraph
