/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.BodyBar.TreePacking
import CombinatorialRigidity.BodyBar.Framework
import CombinatorialRigidity.BodyBar.TayTheorem
import Mathlib.Combinatorics.Graph.Basic

/-!
# Body-hinge Tay–Whiteley theorem — edge multiplication and body-hinge frameworks

The body-hinge Tay–Whiteley theorem in `n`-space (Tay 1989, §7; Whiteley 1988, Theorem 10)
reduces to the body-bar Tay theorem through Whiteley's device (1988, proof of Theorem 10,
p. 244): a hinge leaves its two bodies one relative degree of freedom, so it acts as a bundle of
`δ - 1` bars, `δ = bodyBarDim n`. Combinatorially this is **parallel-edge multiplication** of
the underlying multigraph — the `(δ-1) · G`, written `G̃`, of Katoh and Tanigawa (2011, §1).

The file holds the four nodes of `body-hinge.tex`:

- `def:edge-multiply` — the multiplied multigraph `m · G` on the carrier
  `Graph α β` (mathlib core), and the facts about it below.
- `def:body-hinge-framework` — the body-hinge framework `Graph.BodyHingeFramework`
  as a thin wrapper over the induced `Graph.BodyBarFramework` on `(δ-1)·G`
  (`toBodyBar`), with independence and infinitesimal rigidity read off it.
- `lem:edge-multiply-sparse` — `edgeMultiply_isSparse_iff`, the body-hinge ⇔
  body-bar existential transport (`exists_toBodyBar_iff`) composed with the
  body-bar Tay theorem (`tay_witness`) on `(δ-1)·G`.
- `thm:body-hinge-tay` — `body_hinge_tay`: `edgeMultiply_isSparse_iff` with
  `(δ-1)·G`'s sparsity read as a forest packing (`tutte_nash_williams` on `(δ-1)·G`).

## `m · G` (`def:edge-multiply`)

For `m : ℕ`, `G.edgeMultiply m : Graph α (β × Fin m)` keeps the vertex set of `G`
and replaces each edge `e` by the `m` parallel copies `(e, 0), …, (e, m-1)`, each
linking the same endpoints as `e`. The edge type is `β × Fin m`; the incidence
`(m · G).IsLink (e, i) x y` holds exactly when `G.IsLink e x y`. The facts about it:

- `vertexSet_edgeMultiply` — `V(m · G) = V(G)` (definitionally).
- `edgeMultiply_edgeSet_ncard` — `|E(m · G)| = m · |E(G)|`.
- `spanningVerts_edgeMultiply` — a bar set `E'` in `G` spans the same vertices as
  its preimage `(· .1 ∈ E')` in `m · G`, for `m ≠ 0`.
- `edgeMultiply_inc` and `edgeMultiply_mono` — incidence, and monotonicity in the subgraph
  order.

Phrased `Set`-side throughout (`Set.ncard`, `[Finite]`) to line up with the
`Graph.IsSparse` predicate (`def:graph-sparse`). The blueprint presents the file in
`sec:body-hinge`.
-/

namespace Graph

open Set

variable {α β : Type*}

/-- **Parallel-edge multiplication** `m · G` (`def:edge-multiply`): the multigraph
on the same vertex set as `G : Graph α β` in which each edge `e` is replaced by `m`
parallel copies indexed by `Fin m`. The edge type is `β × Fin m`, and
`(m · G).IsLink (e, i) x y` holds exactly when `G.IsLink e x y`. The hinge-to-bar
reduction of the body-hinge Tay–Whiteley theorem takes `m = bodyBarDim n - 1`
(`bodyHingeMult n`). -/
@[simps! vertexSet isLink]
def edgeMultiply (G : Graph α β) (m : ℕ) : Graph α (β × Fin m) where
  vertexSet := V(G)
  IsLink p x y := G.IsLink p.1 x y
  edgeSet := {p | p.1 ∈ E(G)}
  isLink_symm := by
    rintro ⟨e, i⟩ he
    exact ⟨fun x y h => h.symm⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro ⟨e, i⟩ x y v w h h'
    exact h.left_eq_or_eq h'
  edge_mem_iff_exists_isLink := by
    rintro ⟨e, i⟩
    simp only [Set.mem_ofPred_eq]
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
  simp only [this, Set.ncard_prod, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin,
    mul_comm]

/-- A bar set `E'` in `G` spans the same vertices as its preimage under the first
projection in `m · G` (`def:edge-multiply`): `spanningVerts` transports across edge
multiplication. Requires `m ≠ 0` so each `G`-edge has at least one parallel copy
(for `m = 0` the multiplied graph is edgeless); `m = bodyBarDim n - 1` is at least `2` for
`n ≥ 2`. -/
@[simp]
lemma spanningVerts_edgeMultiply (G : Graph α β) (m : ℕ) [NeZero m] (E' : Set β) :
    (G.edgeMultiply m).spanningVerts {p : β × Fin m | p.1 ∈ E'} = G.spanningVerts E' := by
  ext x
  simp only [mem_spanningVerts, edgeMultiply_inc, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨p, hp, hinc⟩; exact ⟨p.1, hp, hinc⟩
  · rintro ⟨e, he, hinc⟩; exact ⟨(e, ⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩), he, hinc⟩

/-- Edge multiplication is **monotone** in the subgraph order: `H ≤ G` implies
`m · H ≤ m · G`. Each parallel copy of a link of `H` is the corresponding copy of the
same link of `G`, and the vertex sets are inherited verbatim. -/
@[gcongr]
lemma edgeMultiply_mono {H G : Graph α β} (h : H ≤ G) (m : ℕ) :
    H.edgeMultiply m ≤ G.edgeMultiply m where
  vertexSet_mono := h.vertexSet_mono
  isLink_mono p x y hp := (IsLink.mono h hp : G.IsLink p.1 x y)

/-! ## Body-hinge frameworks (`def:body-hinge-framework`)

A **body-hinge framework** in `ℝⁿ` on a multigraph `G : Graph α β` (`def:body-hinge-framework`)
joins bodies by hinges, `(n-2)`-dimensional affine subspaces (Whiteley 1988, §3.3). A hinge
constrains all but one of the `δ` relative screw freedoms of the two bodies it joins,
`δ = bodyBarDim n`, so it behaves like a bundle of `δ - 1` bars meeting the hinge whose Plücker
vectors are linearly independent (Whiteley 1988, proof of Theorem 10, p. 244). Combinatorially
this is the parallel-edge multiplication `(δ-1)·G` (`edgeMultiply` above).

The formalization records a body-hinge framework by the vectors of these bars alone: it *is* a
body-bar framework on `(δ-1)·G`, with no hinge and no condition on the `δ - 1` vectors of an
edge (they need not span a hinge's space, nor be independent). Independence and infinitesimal
rigidity are those of this body-bar framework (`BodyBar/Framework.lean`). -/

/-- The edge-multiplication factor of the body-hinge reduction: `δ - 1`, where
`δ = bodyBarDim n`. A hinge constrains all but one of a body's `δ` relative screw
freedoms, so each hinge becomes `bodyHingeMult n` bars. For `n ≥ 2` this is `≥ 2`
(`δ ≥ 3`); the lemmas that need a copy of every edge assume `[NeZero (bodyHingeMult n)]`. -/
def bodyHingeMult (n : ℕ) : ℕ := bodyBarDim n - 1

/-- A **body-hinge framework** in `ℝⁿ` on a multigraph `G : Graph α β`
(`def:body-hinge-framework`; Whiteley 1988, §3.3). The combinatorial data is
the multigraph `G`; the geometric data is a **placement** assigning each of the
`δ - 1` parallel bars of every hinge a vector of `ℝᵈ`, `d = bodyBarDim n`. In the source a
hinge's `δ - 1` vectors are a basis of the span of the Plücker vectors of the lines meeting the
hinge; here they are arbitrary, and no hinge is recorded.

The placement is typed as a placement on the multiplied multigraph `(δ-1)·G`
(`graph.edgeMultiply (bodyHingeMult n)`, edge type `β × Fin (δ-1)`); the induced
body-bar framework `toBodyBar` is then *literally* the `Graph.BodyBarFramework` on
`(δ-1)·G` carrying that placement, and all rigidity notions are inherited from it. -/
structure BodyHingeFramework (n : ℕ) (α β : Type*) where
  /-- The underlying multigraph: bodies are vertices, hinges are edges. -/
  graph : Graph α β
  /-- The placement: each of the `δ - 1` parallel bars of every hinge gets a
  vector of `ℝᵈ`, `d = bodyBarDim n`. Equivalently a placement on the multiplied
  multigraph `(δ-1)·G`; the vectors are unconstrained. -/
  placement : E(graph.edgeMultiply (bodyHingeMult n)) →
    EuclideanSpace ℝ (Fin (bodyBarDim n))

namespace BodyHingeFramework

variable {n : ℕ} {α β : Type*}

/-- The **induced body-bar framework** of a body-hinge framework on `(δ-1)·G`
(`def:body-hinge-framework`): the `Graph.BodyBarFramework` on the multiplied
multigraph `(δ-1)·G` carrying `F`'s per-bar placement. Its rigidity map
(`Graph.BodyBarFramework.rigidityMap`) is the body-hinge framework's, and `IsIndependent` and
`IsInfinitesimallyRigid` below are read off it. -/
def toBodyBar (F : BodyHingeFramework n α β) :
    Graph.BodyBarFramework n α (β × Fin (bodyHingeMult n)) where
  graph := F.graph.edgeMultiply (bodyHingeMult n)
  placement := F.placement

@[simp]
theorem toBodyBar_graph (F : BodyHingeFramework n α β) :
    F.toBodyBar.graph = F.graph.edgeMultiply (bodyHingeMult n) := rfl

@[simp]
theorem toBodyBar_placement (F : BodyHingeFramework n α β) :
    F.toBodyBar.placement = F.placement := rfl

/-- A body-hinge framework `F` is **independent** at an orientation `D` of `(δ-1)·G`
(`def:body-hinge-framework`'s independence) when its induced body-bar framework is: the rows of
all the bars of `(δ-1)·G` are linearly independent. Inherited verbatim
from `Graph.BodyBarFramework.IsIndependent`. -/
def IsIndependent (F : BodyHingeFramework n α β)
    (D : Graph.orientation (F.graph.edgeMultiply (bodyHingeMult n))) : Prop :=
  F.toBodyBar.IsIndependent D

/-- A body-hinge framework `F` is **infinitesimally rigid** at an orientation `D` of
`(δ-1)·G` (`def:body-hinge-framework`'s infinitesimal rigidity) when its induced body-bar
framework is: `rank + δ = δ·b` for `δ = bodyBarDim n` and `b` the number of bodies. Inherited
verbatim from `Graph.BodyBarFramework.IsInfinitesimallyRigid`; `[Finite α]` is the
same semantic contract guard as there (finite body set). -/
def IsInfinitesimallyRigid [Finite α] (F : BodyHingeFramework n α β)
    (D : Graph.orientation (F.graph.edgeMultiply (bodyHingeMult n))) : Prop :=
  F.toBodyBar.IsInfinitesimallyRigid D

/-- A body-bar framework on the multiplied multigraph `(δ-1)·G` arises from a body-hinge
framework on `G`: a property `P` holds at `toBodyBar` of some body-hinge framework on `G` iff
it holds at some body-bar framework on `(δ-1)·G` (the placement passes through unchanged).
This is the existential transport of `lem:edge-multiply-sparse`'s proof: the body-hinge
frameworks on `G` and the body-bar frameworks on `(δ-1)·G` are *the same data*. -/
theorem exists_toBodyBar_iff (G : Graph α β)
    (P : BodyBarFramework n α (β × Fin (bodyHingeMult n)) → Prop) :
    (∃ F : BodyHingeFramework n α β, F.graph = G ∧ P F.toBodyBar) ↔
      (∃ Fb : BodyBarFramework n α (β × Fin (bodyHingeMult n)),
        Fb.graph = G.edgeMultiply (bodyHingeMult n) ∧ P Fb) := by
  constructor
  · rintro ⟨F, rfl, hP⟩
    exact ⟨F.toBodyBar, rfl, hP⟩
  · rintro ⟨Fb, hgraph, hP⟩
    refine ⟨⟨G, hgraph ▸ Fb.placement⟩, rfl, ?_⟩
    convert hP using 1
    cases Fb with
    | mk graph placement => cases hgraph; rfl

/-- **Tay's theorem for the multiplied multigraph** (`lem:edge-multiply-sparse`; the reduction of
Whiteley 1988, proof of Theorem 10). For `δ = bodyBarDim n`, a multigraph `G` carries an
*independent* body-hinge
framework in `ℝⁿ` **iff** `(δ-1)·G` is `(δ,δ)`-sparse, and an *isostatic* one **iff** `(δ-1)·G`
is `(δ,δ)`-tight. The proof is the body-bar Tay theorem (`tay_witness`) applied to the multiplied
multigraph `(δ-1)·G`, transported across the body-hinge ⇔ body-bar existential bijection
(`exists_toBodyBar_iff`): a body-hinge framework on `G` *is* a body-bar framework on `(δ-1)·G`, so
independence and isostaticity read off node-for-node.

The count of `def:edge-multiply` makes the tightness concrete: `|E((δ-1)·G)| = (δ-1)|E(G)|`
(`edgeMultiply_edgeSet_ncard`), so `(δ,δ)`-tightness of `(δ-1)·G` reads
`(δ-1)|E(G)| + δ = δ·|V(G)|`, i.e. `(δ-1)|E(G)| = δ(|V(G)|-1)`. -/
theorem edgeMultiply_isSparse_iff [Finite α] [Finite β] (G : Graph α β) :
    ((∃ (F : BodyHingeFramework n α β) (_ : F.graph = G)
        (D : Graph.orientation (F.graph.edgeMultiply (bodyHingeMult n))), F.IsIndependent D) ↔
      (G.edgeMultiply (bodyHingeMult n)).IsSparse (bodyBarDim n) (bodyBarDim n)) ∧
    ((∃ (F : BodyHingeFramework n α β) (_ : F.graph = G)
        (D : Graph.orientation (F.graph.edgeMultiply (bodyHingeMult n))),
          F.IsIndependent D ∧ F.IsInfinitesimallyRigid D) ↔
      (G.edgeMultiply (bodyHingeMult n)).IsTight (bodyBarDim n) (bodyBarDim n)) := by
  obtain ⟨hsparse, htight⟩ :=
    BodyBarFramework.tay_witness (n := n) (G.edgeMultiply (bodyHingeMult n))
  refine ⟨?_, ?_⟩
  · rw [← hsparse]
    constructor
    · rintro ⟨F, rfl, D, hD⟩; exact ⟨F.toBodyBar, rfl, D, hD⟩
    · rintro ⟨Fb, hg, D, hD⟩
      obtain ⟨F, rfl, hP⟩ :=
        (exists_toBodyBar_iff G (fun Fb => ∃ D, Fb.IsIndependent D)).mpr ⟨Fb, hg, D, hD⟩
      exact ⟨F, rfl, hP⟩
  · rw [← htight]
    constructor
    · rintro ⟨F, rfl, D, hD⟩; exact ⟨F.toBodyBar, rfl, D, hD⟩
    · rintro ⟨Fb, hg, D, hD⟩
      obtain ⟨F, rfl, hP⟩ :=
        (exists_toBodyBar_iff G
          (fun Fb => ∃ D, Fb.IsIndependent D ∧ Fb.IsInfinitesimallyRigid D)).mpr ⟨Fb, hg, D, hD⟩
      exact ⟨F, rfl, hP⟩

/-- **Body-hinge Tay–Whiteley theorem** (`thm:body-hinge-tay`; Tay 1989, §7, and Whiteley
1988, Theorem 10). For `δ = bodyBarDim n = n(n+1)/2`, a multigraph `G` carries an
*independent* body-hinge framework in `ℝⁿ` **iff** `E((δ-1)·G)` is the edge-disjoint union of
`δ` forests (`Graph.IsForestPacking`), and an *isostatic* one **iff** `(δ-1)·G` is
`(δ,δ)`-tight. As the definition records a body-hinge framework by its bars alone, the
frameworks need not come from hinges.

The sparse/tight characterizations are `edgeMultiply_isSparse_iff` (the body-hinge ⇔ body-bar
reduction composed with the body-bar Tay theorem `tay_witness` on `(δ-1)·G`); the forest-packing
reformulation is `tutte_nash_williams` applied to `(δ-1)·G`. When `(δ-1)·G` is connected, the
tight case is a packing of `δ` spanning trees by `isSpanningTreePacking_of_isTight` applied to
`(δ-1)·G`. -/
theorem body_hinge_tay [Finite α] [Finite β] (G : Graph α β) :
    ((∃ (F : BodyHingeFramework n α β) (_ : F.graph = G)
        (D : Graph.orientation (F.graph.edgeMultiply (bodyHingeMult n))), F.IsIndependent D) ↔
      (G.edgeMultiply (bodyHingeMult n)).IsForestPacking (bodyBarDim n)) ∧
    ((∃ (F : BodyHingeFramework n α β) (_ : F.graph = G)
        (D : Graph.orientation (F.graph.edgeMultiply (bodyHingeMult n))),
          F.IsIndependent D ∧ F.IsInfinitesimallyRigid D) ↔
      (G.edgeMultiply (bodyHingeMult n)).IsTight (bodyBarDim n) (bodyBarDim n)) := by
  obtain ⟨hsparse, htight⟩ := edgeMultiply_isSparse_iff (n := n) G
  exact ⟨hsparse.trans tutte_nash_williams.symm, htight⟩

end BodyHingeFramework

end Graph
