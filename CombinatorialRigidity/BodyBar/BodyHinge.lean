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

Phase 16. The body-hinge / panel-hinge Tay–Whiteley theorem in `n`-space reduces
to the body-bar Tay theorem (Phase 15) through a single combinatorial device:
replace each hinge by a bundle of `δ - 1` coincident body-bars, where
`δ = bodyBarDim n`. Combinatorially this is **parallel-edge multiplication** of
the underlying multigraph — the `(δ-1) · G` of Katoh–Tanigawa 2011's molecular
conjecture statement.

This file lands the lower `body-hinge.tex` dep-graph nodes:

- `def:edge-multiply` — the multiplied multigraph `m · G` on the carrier
  `Graph α β` (mathlib core), and its three transport facts.
- `def:body-hinge-framework` — the body-hinge framework `Graph.BodyHingeFramework`
  as a thin wrapper over the induced `Graph.BodyBarFramework` on `(δ-1)·G`
  (`toBodyBar`), with independence / infinitesimal rigidity inherited verbatim.

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

/-! ## Body-hinge frameworks (`def:body-hinge-framework`)

A **body-hinge framework** in `ℝⁿ` on a multigraph `G : Graph α β` assigns each
hinge (edge) `e` an `(δ-1)`-dimensional space of bar coordinates dual to the hinge,
`δ = bodyBarDim n`. Following Whiteley 1988's matroid-union reduction (specialized
to the standard-basis witness; see `notes/Phase16.md`), a hinge constrains all but
one of the `δ` relative screw freedoms of the two bodies it joins, so it behaves
like a bundle of `δ - 1` coincident body-bars whose two-extensor coordinates span
the hinge's dual space. Combinatorially this is the parallel-edge multiplication
`(δ-1)·G` (`edgeMultiply` above): the body-hinge framework is *defined* as the
induced body-bar framework on `(δ-1)·G`, with the `δ - 1` bars of each hinge
carrying a basis of its dual space.

No new linear algebra: rigidity, independence, and infinitesimal rigidity are
**inherited verbatim** from the induced `Graph.BodyBarFramework` on `(δ-1)·G`
(Phase 15, `BodyBar/Framework.lean`). The standard-basis witness on `(δ-1)·G`
routes through without glue — the only Phase-16-specific data is the
edge-multiplication device and the per-hinge placement, both bookkeeping. -/

/-- The edge-multiplication factor of the body-hinge reduction: `δ - 1`, where
`δ = bodyBarDim n`. A hinge constrains all but one of a body's `δ` relative screw
freedoms, so each hinge becomes `bodyHingeMult n` coincident body-bars. For `n ≥ 2`
this is `≥ 2` (`δ ≥ 3`), so `[NeZero (bodyHingeMult n)]` is available downstream and
`spanningVerts_edgeMultiply` applies. -/
def bodyHingeMult (n : ℕ) : ℕ := bodyBarDim n - 1

/-- A **body-hinge framework** in `ℝⁿ` on a multigraph `G : Graph α β`
(`def:body-hinge-framework`; Whiteley 1988, Tay 1989). The combinatorial data is
the multigraph `G`; the geometric data is a **placement** assigning each of the
`δ - 1` parallel bars of every hinge a two-extensor (Plücker) coordinate in `ℝᵈ`,
`d = bodyBarDim n`. Per the reduction, the `δ - 1` bars of a hinge collectively
carry a basis of the `(δ-1)`-dimensional space dual to the hinge.

The placement is typed as a placement on the multiplied multigraph `(δ-1)·G`
(`graph.edgeMultiply (bodyHingeMult n)`, edge type `β × Fin (δ-1)`); the induced
body-bar framework `toBodyBar` is then *literally* the `Graph.BodyBarFramework` on
`(δ-1)·G` carrying that placement, and all rigidity notions are inherited from it.
Degenerate two-extensors are permitted (existence-of-realization scope), matching
`Graph.BodyBarFramework`. -/
structure BodyHingeFramework (n : ℕ) (α β : Type*) where
  /-- The underlying multigraph: bodies are vertices, hinges are edges. -/
  graph : Graph α β
  /-- The placement: each of the `δ - 1` parallel bars of every hinge gets a
  two-extensor coordinate in `ℝᵈ`, `d = bodyBarDim n`. Equivalently a placement on
  the multiplied multigraph `(δ-1)·G`; degenerate coordinates are permitted. -/
  placement : E(graph.edgeMultiply (bodyHingeMult n)) →
    EuclideanSpace ℝ (Fin (bodyBarDim n))

namespace BodyHingeFramework

variable {n : ℕ} {α β : Type*}

/-- The **induced body-bar framework** of a body-hinge framework on `(δ-1)·G`
(`def:body-hinge-framework`): the `Graph.BodyBarFramework` on the multiplied
multigraph `(δ-1)·G` carrying `F`'s per-bar placement. The body-hinge rigidity map
is *defined* as this framework's body-bar rigidity map
(`Graph.BodyBarFramework.rigidityMap`); the hinge-to-bar reduction reads all
rigidity data off `toBodyBar`. -/
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
when its induced body-bar framework is (`def:body-hinge-framework`): the bar-constraint
rows of the `δ - 1` bars of every hinge are linearly independent. Inherited verbatim
from `Graph.BodyBarFramework.IsIndependent`. -/
def IsIndependent (F : BodyHingeFramework n α β)
    (D : Graph.orientation (F.graph.edgeMultiply (bodyHingeMult n))) : Prop :=
  F.toBodyBar.IsIndependent D

/-- A body-hinge framework `F` is **infinitesimally rigid** at an orientation `D` of
`(δ-1)·G` when its induced body-bar framework is (`def:body-hinge-framework`):
`rank + δ = δ·b` for `δ = bodyBarDim n` and `b` the number of bodies. Inherited
verbatim from `Graph.BodyBarFramework.IsInfinitesimallyRigid`; `[Finite α]` is the
same semantic contract guard as there (finite body set). -/
def IsInfinitesimallyRigid [Finite α] (F : BodyHingeFramework n α β)
    (D : Graph.orientation (F.graph.edgeMultiply (bodyHingeMult n))) : Prop :=
  F.toBodyBar.IsInfinitesimallyRigid D

/-- A body-bar framework on the multiplied multigraph `(δ-1)·G` arises from a body-hinge
framework on `G`: `toBodyBar` is a bijection from `BodyHingeFramework`s with `graph = G`
onto `BodyBarFramework`s with `graph = (δ-1)·G`, given by passing the placement through
unchanged. This is the existential transport underlying `lem:edge-multiply-sparse`: the
body-hinge frameworks on `G` and the body-bar frameworks on `(δ-1)·G` are *the same data*. -/
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

/-- **Sparsity transports across edge multiplication** (`lem:edge-multiply-sparse`; Tay 1989 §7,
Whiteley 1988). For `δ = bodyBarDim n`, a multigraph `G` carries an *independent* body-hinge
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

/-- **Body-hinge Tay–Whiteley theorem, independent form** (`thm:body-hinge-tay`;
Tay 1989 §7, Whiteley 1988). For `n ≥ 2` and `δ = bodyBarDim n = n(n+1)/2`, a multigraph
`G` carries an *independent* body-hinge framework in `ℝⁿ` **iff** `(δ-1)·G` is
`(δ,δ)`-sparse — equivalently the edge-disjoint union of `δ` forests
(`Graph.IsForestPacking`) — and an *isostatic* one **iff** `(δ-1)·G` is `(δ,δ)`-tight.

The chapter target of Phase 16. The sparse/tight characterizations are
`edgeMultiply_isSparse_iff` (the body-hinge ⇔ body-bar reduction composed with the
body-bar Tay theorem `tay_witness` on `(δ-1)·G`); the forest-packing reformulation is
`tutte_nash_williams` applied to `(δ-1)·G`. The connected-tight spanning-tree refinement
(each of the `δ` forests upgrades to a spanning tree) is `isSpanningTreePacking_of_isTight`
applied to `(δ-1)·G`, available at the call site under `(δ-1)·G).Connected`. -/
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
