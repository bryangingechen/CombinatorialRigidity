/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.BodyBar.TreePacking
import Mathlib.Combinatorics.Graph.Basic

/-!
# Body-hinge Tay–Whiteley theorem — edge multiplication `m · G` (`def:edge-multiply`)

Phase 16. The body-hinge / panel-hinge Tay–Whiteley theorem in `n`-space reduces
to the body-bar Tay theorem (Phase 15) through a single combinatorial device:
replace each hinge by a bundle of `δ - 1` coincident body-bars, where
`δ = bodyBarDim n`. Combinatorially this is **parallel-edge multiplication** of
the underlying multigraph — the `(δ-1) · G` of Katoh–Tanigawa 2011's molecular
conjecture statement.

This file lands the leaf-most node of the `body-hinge.tex` dep-graph
(`def:edge-multiply`): the multiplied multigraph `m · G` on the carrier
`Graph α β` (mathlib core), and its three transport facts.

## `m · G` (`def:edge-multiply`)

For `m : ℕ`, `G.edgeMultiply m : Graph α (β × Fin m)` keeps the vertex set of `G`
and replaces each edge `e` by the `m` parallel copies `(e, 0), …, (e, m-1)`, each
linking the same endpoints as `e`. The edge type is `β × Fin m`; the incidence
`(m · G).IsLink (e, i) x y` holds exactly when `G.IsLink e x y`. The three
transport facts the hinge-to-bar reduction reaches for:

- `vertexSet_edgeMultiply` — `V(m · G) = V(G)` (definitionally).
- `edgeMultiply_edgeSet_ncard` — `|E(m · G)| = m · |E(G)|`.
- `spanningVerts_edgeMultiply` — a bar set `E'` in `G` spans the same vertices as
  its preimage `(· .1 ∈ E')` in `m · G`.

Phrased `Set`-side throughout (`Set.ncard`, `[Finite]`) to line up with the
Phase-13 `Graph.IsSparse` predicate (`def:graph-sparse`). See `ROADMAP.md` §16 /
`notes/Phase16.md` and the `sec:body-hinge` dep-graph of `body-hinge.tex`.
-/

namespace Graph

open Set

variable {α β : Type*}

/-- **Parallel-edge multiplication** `m · G` (`def:edge-multiply`): the multigraph
on the same vertex set as `G : Graph α β` in which each edge `e` is replaced by `m`
parallel copies indexed by `Fin m`. The edge type is `β × Fin m`, and
`(m · G).IsLink (e, i) x y` holds exactly when `G.IsLink e x y`. The hinge-to-bar
reduction of the body-hinge Tay–Whiteley theorem takes `m = bodyBarDim n - 1`. -/
@[simps! vertexSet isLink]
def edgeMultiply (G : Graph α β) (m : ℕ) : Graph α (β × Fin m) where
  vertexSet := V(G)
  IsLink p x y := G.IsLink p.1 x y
  edgeSet := {p | p.1 ∈ E(G)}
  isLink_symm := by
    rintro ⟨e, i⟩ he x y h
    exact h.symm
  eq_or_eq_of_isLink_of_isLink := by
    rintro ⟨e, i⟩ x y v w h h'
    exact h.left_eq_or_eq h'
  edge_mem_iff_exists_isLink := by
    rintro ⟨e, i⟩
    simp only [Set.mem_setOf_eq]
    exact ⟨fun he ↦ by obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet he; exact ⟨x, y, h⟩,
      fun ⟨x, y, h⟩ ↦ h.edge_mem⟩
  left_mem_of_isLink := by
    rintro ⟨e, i⟩ x y h
    exact h.left_mem

@[simp]
lemma edgeMultiply_edgeSet (G : Graph α β) (m : ℕ) :
    E(G.edgeMultiply m) = {p : β × Fin m | p.1 ∈ E(G)} := rfl

lemma edgeMultiply_inc (G : Graph α β) (m : ℕ) {p : β × Fin m} {x : α} :
    (G.edgeMultiply m).Inc p x ↔ G.Inc p.1 x := Iff.rfl

/-- `|E(m · G)| = m · |E(G)|` (`def:edge-multiply`): each of the `|E(G)|` edges of
`G` is replaced by `m` parallel copies. -/
lemma edgeMultiply_edgeSet_ncard (G : Graph α β) (m : ℕ) :
    E(G.edgeMultiply m).ncard = m * E(G).ncard := by
  rw [edgeMultiply_edgeSet]
  have : {p : β × Fin m | p.1 ∈ E(G)} = E(G) ×ˢ (Set.univ : Set (Fin m)) := by
    ext ⟨e, i⟩; simp
  rw [this, Set.ncard_prod, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin,
    mul_comm]

/-- A bar set `E'` in `G` spans the same vertices as its preimage under the first
projection in `m · G` (`def:edge-multiply`): `spanningVerts` transports across edge
multiplication. Requires `m ≠ 0` so each `G`-edge has at least one parallel copy
(for `m = 0` the multiplied graph is edgeless); the reduction uses
`m = bodyBarDim n - 1 ≥ 1`. -/
@[simp]
lemma spanningVerts_edgeMultiply (G : Graph α β) (m : ℕ) [NeZero m] (E' : Set β) :
    (G.edgeMultiply m).spanningVerts {p : β × Fin m | p.1 ∈ E'} = G.spanningVerts E' := by
  ext x
  simp only [mem_spanningVerts, edgeMultiply_inc, Set.mem_setOf_eq]
  constructor
  · rintro ⟨p, hp, hinc⟩; exact ⟨p.1, hp, hinc⟩
  · rintro ⟨e, he, hinc⟩; exact ⟨(e, ⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩), he, hinc⟩

end Graph
