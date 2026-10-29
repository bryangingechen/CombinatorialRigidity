/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset
public import Matroid.Graph.Simple

/-!
# A simple graph as a multigraph

The multigraph `G.shadowGraph` of a simple graph `G` on a finite set `V`, as
`sec:molecule-application-carrier` presents it (`lem:molecule-graph-carrier`). The square `G²` and
the generic rank are defined for a `SimpleGraph V`, and the deficiency and the molecular and
panel-hinge frameworks for a multigraph `Graph V β`, whose edges are drawn from a type `β` of
labels; the molecule rank formula (`Application.lean`) applies the latter to `G.shadowGraph`.

The labels of `G.shadowGraph` are `Sym2 V ⊕ Fin (6 * (Nat.card V - 1) + 1)`. Its link between
adjacent vertices `u` and `v` of `G` is labelled `s(u, v)`, so it is simple, has vertex set `V`, and
links exactly the adjacent pairs of `G`. No link has a label of the second summand: those labels
bring the number of labels above `6(|V| - 1)` (`card_shadowLabel_lt`). No result needs that bound,
as the molecular realization (`exists_molecular_rankHypothesis_generalPosition`,
`thm:panel-hinge-iff-molecular`) assumes nothing of the labels; the second summand stays so that the
label type, which `lem:molecule-graph-carrier` states, does not change.

## Main results

* `SimpleGraph.shadowGraph`: the multigraph of `G`.
* `SimpleGraph.shadowGraph_simple`: it is simple.
* `SimpleGraph.shadowGraph_vertexSet`: its vertex set is `V`.
* `SimpleGraph.shadowGraph_isLink_iff`: it links exactly the adjacent pairs of `G`.
* `SimpleGraph.card_shadowLabel_lt`: its labels number more than `6(|V| - 1)`.
-/

@[expose] public section

open scoped Graph

namespace SimpleGraph

variable {V : Type*} [Finite V]

/-- **The multigraph of a simple graph** (`lem:molecule-graph-carrier`): the multigraph on `V`, with
the labels `Sym2 V ⊕ Fin (6 * (|V| - 1) + 1)`, that links `x` and `y` by the label `s(x, y)` when
`G.Adj x y`. No link has a label of the second summand; those labels bring the number of labels
above `6(|V| - 1)` for every finite `V` (`card_shadowLabel_lt`), which no result needs. -/
def shadowGraph (G : SimpleGraph V) :
    Graph V (Sym2 V ⊕ Fin (6 * (Nat.card V - 1) + 1)) where
  vertexSet := Set.univ
  IsLink e x y := G.Adj x y ∧ Sum.inl s(x, y) = e
  isLink_symm e _ := ⟨fun x y h =>
    ⟨h.1.symm, (congrArg Sum.inl (Sym2.eq_swap (a := y) (b := x))).trans h.2⟩⟩
  eq_or_eq_of_isLink_of_isLink e x y v w h1 h2 := by
    have hs : s(x, y) = s(v, w) := Sum.inl_injective (h1.2.trans h2.2.symm)
    rcases Sym2.eq_iff.mp hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  left_mem_of_isLink _ x _ _ := Set.mem_univ x

omit [Finite V] in
/-- **The multigraph of a simple graph is simple** (`lem:molecule-graph-carrier`): two links with
the same ends have the same label `s(x, y)`, and there is no loop, as `G.Adj` is irreflexive. -/
theorem shadowGraph_simple (G : SimpleGraph V) : G.shadowGraph.Simple where
  not_isLoopAt _ _x h := h.1.ne rfl
  eq_of_isLink _ _ _ _ he hf := he.2.symm.trans hf.2

omit [Finite V] in
/-- **The vertex set of the multigraph of a simple graph** (`lem:molecule-graph-carrier`): it is all
of `V`. -/
@[simp] theorem shadowGraph_vertexSet (G : SimpleGraph V) : V(G.shadowGraph) = Set.univ := rfl

omit [Finite V] in
/-- **The links of the multigraph of a simple graph** (`lem:molecule-graph-carrier`):
`G.shadowGraph` links `x` and `y` iff `G.Adj x y`. The equivalence needs no `x ≠ y`: both sides fail
at `x = y`. -/
theorem shadowGraph_isLink_iff (G : SimpleGraph V) (x y : V) :
    (∃ e, G.shadowGraph.IsLink e x y) ↔ G.Adj x y :=
  ⟨fun ⟨_, h⟩ => h.1, fun h => ⟨Sum.inl s(x, y), h, rfl⟩⟩

/-- **The labels of the multigraph of a simple graph** (`lem:molecule-graph-carrier`): they number
more than `6(|V| - 1)` for every finite `V`, since the summand `Fin (6 * (|V| - 1) + 1)` alone has
`6(|V| - 1) + 1`. -/
theorem card_shadowLabel_lt (V : Type*) [Finite V] :
    6 * (Nat.card V - 1) < Nat.card (Sym2 V ⊕ Fin (6 * (Nat.card V - 1) + 1)) := by
  rw [Nat.card_sum, Nat.card_fin]
  omega

end SimpleGraph
