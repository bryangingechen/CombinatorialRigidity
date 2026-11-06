/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.Combinatorics.Graph.Delete

/-!
# Upstream candidate: an endpoint selector that records the links of a multigraph

Mathlib's multigraph `Graph α β` (`Mathlib/Combinatorics/Graph/Basic.lean`) keeps the ends of an
edge as a relation, `G.IsLink e x y`, with no map from an edge to its ends. A selector
`ends : β → α × α` *records the links* of `G` (`RecordsLinks`) when it gives each edge of `G` its
two ends, in either order. The combinatorial-rigidity project's panel-hinge frameworks read the
ends of an edge off such a selector (`fmlnote:panel-hinge-nondegenerate`): the condition is the
field `PanelHingeFramework.isLink_ends` (`Molecular/AlgebraicInduction/PanelHinge.lean`), whose
tactic `link_tac` proves it from a hypothesis in scope.

The condition has two forms at the links of the multigraph (`recordsLinks_iff_forall_isLink`,
`recordsLinks_iff_eq_or_swap`), the total and pair forms give it (`RecordsLinks.of_forall`,
`RecordsLinks.of_pair`), and it gives the pair form (`RecordsLinks.eq_pair_or_swap`). It passes
to a graph with fewer links (`RecordsLinks.of_isLink_imp`), a subgraph (`RecordsLinks.mono`) and an
induced subgraph (`RecordsLinks.induce`).

Three of its lemmas are in `Molecular/Induction/Operations.lean`: its forms at the project's
endpoint choice `Graph.endsOf` (`recordsLinks_endsOf`) and splitting off
(`RecordsLinks.update_splitOff`), beside those operations, and at the image under a map of the
vertices (`RecordsLinks.map`). The project's `Graph.map` is the `Matroid` package's
(`Matroid/Graph/Map.lean`), which mathlib's `Graph.map` (`Mathlib/Combinatorics/Graph/Maps.lean`)
cannot be imported beside: both declare `Graph.map_map`. Upstream, `RecordsLinks.map` would be
stated for mathlib's `Graph.map`, in this file.

The Lean namespace is the upstream one (`Graph`), so promotion to mathlib is a copy-paste. The
target is a new file `Mathlib/Combinatorics/Graph/RecordsLinks.lean`, importing `Delete.lean` (for
`Graph.induce`) and `Maps.lean`. See `DESIGN.md` "Mirror directory".
-/

@[expose] public section

namespace Graph

variable {α β : Type*}

/-- **A selector that records the links of a multigraph** (the condition on the selector of
`fmlnote:panel-hinge-nondegenerate`): every edge `e` of `G` links the two bodies that `ends` gives
it, `G.IsLink e (ends e).1 (ends e).2`. The condition is asked of the edges of `G` only, and puts
none on a label outside `E(G)`. -/
def RecordsLinks (G : Graph α β) (ends : β → α × α) : Prop :=
  ∀ e ∈ E(G), G.IsLink e (ends e).1 (ends e).2

variable {G G' : Graph α β} {ends : β → α × α}

/-- **A recorded link** (`fmlnote:panel-hinge-nondegenerate`): if `ends` records the links of `G`
and `e` links `u` and `v` in `G`, then `e` links the two bodies that `ends` gives it. -/
theorem RecordsLinks.isLink (h : RecordsLinks G ends) {e : β} {u v : α} (he : G.IsLink e u v) :
    G.IsLink e (ends e).1 (ends e).2 :=
  h e he.edge_mem

/-- **The condition at the links** (`fmlnote:panel-hinge-nondegenerate`): `ends` records the links
of `G` iff, at every link of `G` at `e`, `e` links the two bodies that `ends` gives it. An edge of
`G` has two ends (`Graph.exists_isLink_of_mem_edgeSet`). -/
theorem recordsLinks_iff_forall_isLink :
    RecordsLinks G ends ↔ ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2 := by
  refine ⟨fun h _ _ _ => h.isLink, fun h e he => ?_⟩
  obtain ⟨x, y, hxy⟩ := Graph.exists_isLink_of_mem_edgeSet he
  exact h e x y hxy

/-- **A recorded link, up to order** (`fmlnote:panel-hinge-nondegenerate`): if `ends` records the
links of `G` and `e` links `u` and `v` in `G`, then `ends e` is `(u, v)` or `(v, u)`. The ends of an
edge are determined up to order (`IsLink.eq_and_eq_or_eq_and_eq`). -/
theorem RecordsLinks.eq_or_swap (h : RecordsLinks G ends) {e : β} {u v : α}
    (he : G.IsLink e u v) :
    ((ends e).1 = u ∧ (ends e).2 = v) ∨ ((ends e).1 = v ∧ (ends e).2 = u) :=
  (h.isLink he).eq_and_eq_or_eq_and_eq he

/-- **The condition up to order** (`fmlnote:panel-hinge-nondegenerate`): `ends` records the links of
`G` iff, at every link of `G` at `e` from `u` to `v`, `ends e` is `(u, v)` or `(v, u)`. It is a base
form of `link_tac`. -/
theorem recordsLinks_iff_eq_or_swap :
    RecordsLinks G ends ↔ ∀ e u v, G.IsLink e u v →
      ((ends e).1 = u ∧ (ends e).2 = v) ∨ ((ends e).1 = v ∧ (ends e).2 = u) := by
  refine ⟨fun h _ _ _ => h.eq_or_swap, fun h => recordsLinks_iff_forall_isLink.mpr ?_⟩
  intro e u v he
  rcases h e u v he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]; exact he
  · rw [h1, h2]; exact he.symm

/-- **The condition passes to a graph with fewer links** (`fmlnote:panel-hinge-nondegenerate`): if
`ends` records the links of `G` and every link of `G'` is one of `G` (`hG'`), then `ends` records
the links of `G'`, as it gives a link of `G'` the same two ends in some order. -/
theorem RecordsLinks.of_isLink_imp (h : RecordsLinks G ends)
    (hG' : ∀ e u v, G'.IsLink e u v → G.IsLink e u v) : RecordsLinks G' ends := by
  refine recordsLinks_iff_forall_isLink.mpr fun e u v he => ?_
  rcases h.eq_or_swap (hG' e u v he) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]; exact he
  · rw [h1, h2]; exact he.symm

/-- **The total form gives the condition** (`fmlnote:panel-hinge-nondegenerate`): if every label `e`
links in `G` the two bodies that `ends` gives it, then `ends` records the links of `G`. The total
form asks every label to be an edge of `G`, which the condition does not. -/
theorem RecordsLinks.of_forall (h : ∀ e, G.IsLink e (ends e).1 (ends e).2) :
    RecordsLinks G ends :=
  fun e _ => h e

/-- **The condition from the pair form** (`fmlnote:panel-hinge-nondegenerate`): if at every link of
`G` at `e` from `u` to `v` the pair `ends e` is `(u, v)` or `(v, u)`, then `ends` records the links
of `G`. `RecordsLinks.eq_pair_or_swap` is the converse; `recordsLinks_iff_eq_or_swap` compares the
pair coordinatewise. -/
theorem RecordsLinks.of_pair (h : ∀ e u v, G.IsLink e u v → ends e = (u, v) ∨ ends e = (v, u)) :
    RecordsLinks G ends := by
  refine recordsLinks_iff_eq_or_swap.mpr fun e u v he => ?_
  rcases h e u v he with h' | h' <;> simp [h']

/-- **A recorded link, as a pair** (`fmlnote:panel-hinge-nondegenerate`): if `ends` records the
links of `G` and `e` links `u` and `v` in `G`, then `ends e` is `(u, v)` or `(v, u)`. The converse
of `RecordsLinks.of_pair`; `RecordsLinks.eq_or_swap` gives the same coordinatewise. -/
theorem RecordsLinks.eq_pair_or_swap (h : RecordsLinks G ends) {e : β} {u v : α}
    (he : G.IsLink e u v) : ends e = (u, v) ∨ ends e = (v, u) :=
  (h.eq_or_swap he).imp (fun h => Prod.ext h.1 h.2) fun h => Prod.ext h.1 h.2

/-- **The condition from a subgraph and two edges at a body** (a step of
`lem:case-III-candidate-dispatch-d3` and `lem:case-III-chain-dispatch`, through
`case_III_realization_of_rank`): let `ends` record the links of `G'`, every link of `G'` be one of
`G` (`hle`), `e_a` and `e_b` link `v` to `a` and to `b` in `G` with `ends e_a = (v, a)` and
`ends e_b = (v, b)`, and every link of `G` be at `e_a`, at `e_b` or a link of `G'` (`hsplit`). Then
`ends` records the links of `G`. In Case III, `G'` is `G − v` and `e_a`, `e_b` are the two edges at
the body `v` of degree two. -/
theorem RecordsLinks.of_split (hG' : RecordsLinks G' ends)
    (hle : ∀ e u w, G'.IsLink e u w → G.IsLink e u w)
    {e_a e_b : β} {v a b : α} (hG_ea : G.IsLink e_a v a) (hends_ea : ends e_a = (v, a))
    (hG_eb : G.IsLink e_b v b) (hends_eb : ends e_b = (v, b))
    (hsplit : ∀ e u w, G.IsLink e u w → e = e_a ∨ e = e_b ∨ G'.IsLink e u w) :
    RecordsLinks G ends := by
  refine recordsLinks_iff_forall_isLink.mpr fun e u w he => ?_
  rcases hsplit e u w he with rfl | rfl | h
  · rw [hends_ea]; exact hG_ea
  · rw [hends_eb]; exact hG_eb
  · exact hle _ _ _ (hG'.isLink h)

/-- **Selectors that agree at the links** (`fmlnote:panel-hinge-nondegenerate`): if `ends` records
the links of `G` and `ends'` agrees with it at every link of `G` (`hagree`), then `ends'` records
them too. Case III changes a selector at labels that are not links of `G − v`
(`case_III_candidate_dispatch`, `chainData_dispatch_interior_of_discriminator`,
`chainData_dispatch_floor_of_discriminator`). -/
theorem RecordsLinks.congr {ends' : β → α × α} (h : RecordsLinks G ends)
    (hagree : ∀ e u v, G.IsLink e u v → ends e = ends' e) : RecordsLinks G ends' := by
  refine recordsLinks_iff_forall_isLink.mpr fun e u v he => ?_
  rw [← hagree e u v he]
  exact h.isLink he

/-- **The condition passes to a subgraph** (`fmlnote:panel-hinge-nondegenerate`): if `ends` records
the links of `G` and `G' ≤ G`, then `ends` records the links of `G'`, as a link of `G'` is one of
`G` (`IsLink.mono`). -/
theorem RecordsLinks.mono (h : RecordsLinks G ends) (hle : G' ≤ G) : RecordsLinks G' ends :=
  h.of_isLink_imp fun _ _ _ he => he.mono hle

/-- **The condition passes to an induced subgraph** (a step of `thm:pencil-x0-cut`,
`thm:pencil-x0-bridge`, `thm:pencil-x0-contract-additive` and the open-ear steps, from
`thm:pencil-x0-open-ear` to the steps at one to four interior bodies): if `ends` records the links
of `G`, it records those of `G.induce X`, as a link of `G.induce X` is one of `G` with both ends in
`X`. -/
theorem RecordsLinks.induce (h : RecordsLinks G ends) (X : Set α) :
    RecordsLinks (G.induce X) ends :=
  h.of_isLink_imp fun _ _ _ he => he.1

end Graph
