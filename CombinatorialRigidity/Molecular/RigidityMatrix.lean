/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.Combinatorics.Graph.Basic
public import CombinatorialRigidity.Molecular.Extensor

/-!
# The panel-hinge rigidity matrix `R(G,p)` (`sec:molecular-rigidity-matrix`)

Phase 18, the second phase of the molecular-conjecture program (Phases 17–26; see
`notes/MolecularConjecture.md`). Where the body-hinge chapter (Phase 16,
`BodyBar/BodyHinge.lean`) *defined* rigidity by reduction to body-bar on the
multiplied graph `(δ-1)·G` (a standard-basis witness, no honest geometry — the
*existence* form), this file builds the **genuine** panel-hinge / body-hinge
rigidity matrix `R(G,p)` of Katoh–Tanigawa 2011 (*A proof of the molecular
conjecture*, Discrete Comput. Geom. **45**, §2.2–2.4), on a realization `p`
assigning a `(d-2)`-dimensional affine *hinge* subspace to each edge.

This file lands the `sec:molecular-rigidity-matrix` dep-graph in dependency order.
The leaf node landing here:

* `BodyHingeFramework` (`def:hinge-constraint`) — a `d`-dimensional body-hinge
  framework `(G,p)` is a multigraph `G : Graph α β` together with a map `p`
  assigning each edge a *hinge*: a `(d-1)`-point family in `ℝ^d` whose affine span
  is a `(d-2)`-dimensional affine subspace. Reparametrizing `d = k+1` to clear the
  `ℕ`-subtraction, a hinge is `Fin k → Fin (k+1) → ℝ` (`k` points in `ℝ^(k+1)`),
  homogenizing to `ℝ^(k+2)`; its supporting `(d-1)`-extensor is the `k`-extensor
  `C(p(e)) = affineSubspaceExtensor (p e) ∈ ⋀^k ℝ^(k+2)` of Phase 17.
* `hingeConstraint` (`def:hinge-constraint`) — identifying an infinitesimal motion
  of a rigid body with a `D`-dimensional *screw center* `S(v)` living in the
  exterior algebra `ExteriorAlgebra ℝ (Fin (k+2) → ℝ)` (where `C(p(e))` lives), the
  hinge `p(e)` constrains the two screw centers `S(u), S(v)` of its endpoints
  `e = uv` to satisfy
  `S(u) - S(v) ∈ span C(p(e)) = Submodule.span ℝ {affineSubspaceExtensor (p e)}`.

## Carrier and dimension

Infinitesimal motions are `D`-dimensional screw centers with `D = (d+1 choose 2)`,
matching Phase 17's extensor space `⋀^(d-1) ℝ^(d+1) ≅ ℝ^D` (here, with `d = k+1`,
`⋀^k ℝ^(k+2)`). We carry the screw center as a full element of
`ExteriorAlgebra ℝ (Fin (k+2) → ℝ)` rather than as a coordinate vector in `ℝ^D`;
`span C(p(e))` is then literally a `Submodule` of that algebra and the hinge
constraint is a membership, with no coordinate identification needed yet. The
concrete `⋀^k ℝ^(k+2) ≅ ℝ^D` identification (and the orthogonal-complement block
`r(p(e))`) is deferred to `def:hinge-row-block` / `def:rigidity-matrix`.

Carrier for the multigraph: mathlib core `Graph α β` (the Phase 13–16 carrier).
Carrier for points: `Fin (k+1) → ℝ`, matching Phase 17's `affineSubspaceExtensor`.
-/

@[expose] public section

namespace CombinatorialRigidity.Molecular

open scoped Matrix

/-- The **screw-center space** of `d = k+1`-dimensional body-hinge rigidity: the
exterior algebra `ExteriorAlgebra ℝ (Fin (k+2) → ℝ)` in which the supporting
extensors `C(·) = affineSubspaceExtensor` of the hinges live. An infinitesimal
motion of a rigid body is a `D`-dimensional *screw center* `S(v)` in this space,
`D = (d+1 choose 2) = (k+2 choose 2)`; we carry the full algebra element rather
than a coordinate vector in `ℝ^D` so that `span C(p(e))` is literally a
`Submodule` of it (`def:hinge-constraint`). -/
abbrev ScrewSpace (k : ℕ) : Type :=
  ExteriorAlgebra ℝ (Fin (k + 2) → ℝ)

/-- A **`d = k+1`-dimensional body-hinge framework** `(G,p)` (`def:hinge-constraint`):
a multigraph `G : Graph α β` together with a *hinge assignment* `hinge` sending each
edge `e : β` to a family of `k` points in `ℝ^(k+1)`, whose affine span is the
`(d-2) = (k-1)`-dimensional affine *hinge* subspace `p(e)`. The supporting
`(d-1) = k`-extensor of the hinge is `C(p(e)) = affineSubspaceExtensor (hinge e)`
(Phase 17), an element of the screw space `⋀^k ℝ^(k+2)`.

The dimension is reparametrized `d = k + 1` (so points live in `ℝ^(k+1)`,
homogenizing to `ℝ^(k+2)`) to clear the `ℕ`-subtractions `d-1`, `d-2` that the
hinge / extensor arities would otherwise carry, matching the Phase 17
`omitTwoExtensor` reparametrization. -/
structure BodyHingeFramework (k : ℕ) (α β : Type*) where
  /-- The underlying multigraph; bodies are vertices, hinges are edges. -/
  graph : Graph α β
  /-- The hinge assignment: each edge `e` gets `k` points in `ℝ^(k+1)` spanning a
  `(k-1)`-dimensional affine hinge subspace. -/
  hinge : β → Fin k → Fin (k + 1) → ℝ

namespace BodyHingeFramework

variable {k : ℕ} {α β : Type*}

/-- The **supporting extensor** `C(p(e))` of the hinge at edge `e`
(`def:hinge-constraint`): the `(d-1) = k`-extensor `affineSubspaceExtensor (hinge e)`
of Phase 17, an element of the screw space `⋀^k ℝ^(k+2)`. It is nonzero exactly when
the `k` hinge points are affinely independent (`affineSubspaceExtensor_ne_zero_iff`),
i.e. when the hinge is a genuine `(k-1)`-dimensional affine subspace. -/
def supportExtensor (F : BodyHingeFramework k α β) (e : β) : ScrewSpace k :=
  affineSubspaceExtensor (F.hinge e)

theorem supportExtensor_apply (F : BodyHingeFramework k α β) (e : β) :
    F.supportExtensor e = affineSubspaceExtensor (F.hinge e) := rfl

/-- The **hinge constraint** at an edge `e = uv` (`def:hinge-constraint`): a screw
assignment `S : α → ScrewSpace k` meets the hinge constraint at `e` between
endpoints `u v : α` when the relative screw center lies in the span of the
supporting extensor,
`S u - S v ∈ span C(p(e)) = Submodule.span ℝ {C(p(e))}`.

This is the honest geometric constraint that the panel-hinge rigidity matrix
`R(G,p)` (`def:rigidity-matrix`) encodes; it supersedes Phase 16's
reduction-form `BodyBar/BodyHinge.lean` definition. -/
def hingeConstraint (F : BodyHingeFramework k α β) (S : α → ScrewSpace k)
    (e : β) (u v : α) : Prop :=
  S u - S v ∈ Submodule.span ℝ {F.supportExtensor e}

theorem hingeConstraint_iff (F : BodyHingeFramework k α β) (S : α → ScrewSpace k)
    (e : β) (u v : α) :
    F.hingeConstraint S e u v ↔
      S u - S v ∈ Submodule.span ℝ {affineSubspaceExtensor (F.hinge e)} :=
  Iff.rfl

end BodyHingeFramework

end CombinatorialRigidity.Molecular
