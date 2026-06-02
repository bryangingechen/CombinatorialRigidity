/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import Mathlib.Combinatorics.Graph.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Matroid.Graph.Matrix

/-!
# Body-bar frameworks (`def:body-bar-framework`)

Phase 15. Following Whiteley 1988 (*The union of matroids and the rigidity of
frameworks*, SIAM J. Disc. Math. **1**) §3 and Tay 1984 (*Rigidity of
multi-graphs. I*, J. Combin. Theory Ser. B **36**) §5, a **body-bar framework**
in `ℝⁿ` on a multigraph `G : Graph α β` pairs `G` with a *placement* assigning
each bar `e ∈ E(G)` a two-extensor (Plücker) coordinate in `ℝᵈ`, where
`d = n(n+1)/2` is the dimension of the space of infinitesimal rigid motions of
`ℝⁿ` (translations + infinitesimal rotations).

A two-extensor is a point of the Plücker embedding of `Gr(2, n+1)` into `ℝᵈ`;
geometrically it records the line carrying the bar together with its direction.
Per ROADMAP §15 / `notes/Phase15.md`, we handle the Plücker coordinates
**inline** with **degenerate coordinates permitted** — i.e. the placement is an
unconstrained map into `ℝᵈ`, not a map into the Plücker variety. This is the
"existence-of-realization" scope: Tay's theorem (`thm:tay-witness`) is witnessed
by the standard-basis specialization `b_e = e_{j(e)}`, whose coordinates are
themselves degenerate two-extensors, so no variety-membership constraint is
needed for the existence direction (Whiteley's "almost all realizations are
rigid" lift via the irreducible Plücker variety is deferred — see ROADMAP §15).

## Main definitions

* `Graph.bodyBarDim` — the body-bar dimension `d = n(n+1)/2` of `ℝⁿ`.
* `Graph.BodyBarFramework` — a body-bar framework: a multigraph `G` together
  with a placement `E(G) → EuclideanSpace ℝ (Fin (bodyBarDim n))`.
* `Graph.BodyBarFramework.rigidityMap` — the bar-constraint rigidity map, an
  `ℝ`-linear map from body motions (`α → ℝᵈ`) to bar constraints
  (`E(G) → ℝ`), one row per bar (Whiteley §3).

## Project context

See `ROADMAP.md` §15, `notes/Phase15.md`, and the
§`sec:body-bar-framework` subsection of `blueprint/src/chapter/body-bar.tex`.
The body-bar **infinitesimal rigidity** (`def:infinitesimally-rigid-body-bar`)
builds on the rigidity map, en route to **Tay's theorem**
(`thm:tay-witness`).
-/

open scoped InnerProductSpace

namespace Graph

variable {α β : Type*}

/-- The **body-bar dimension** of `ℝⁿ`: `d = n(n+1)/2`, the dimension of the
space of infinitesimal rigid motions of `ℝⁿ` (the `n` translations plus the
`n(n-1)/2` independent infinitesimal rotations). Equivalently the dimension of
the Plücker space `ℝᵈ` into which two-extensors of `ℝⁿ⁺¹` embed; a bar in `ℝⁿ`
carries a two-extensor coordinate in this space. -/
def bodyBarDim (n : ℕ) : ℕ := n * (n + 1) / 2

/-- A **body-bar framework** in `ℝⁿ` on a multigraph `G : Graph α β`
(Whiteley 1988 §3, Tay 1984 §5; `def:body-bar-framework`): the multigraph `G`
together with a **placement** `p` assigning each bar `e ∈ E(G)` a two-extensor
(Plücker) coordinate in `ℝᵈ`, `d = n(n+1)/2` (`Graph.bodyBarDim n`).

The placement is an unconstrained map into `EuclideanSpace ℝ (Fin (bodyBarDim n))`
— degenerate two-extensors are permitted, so no Plücker-variety membership
constraint is imposed (existence-of-realization scope; see the module
docstring). The bundled `G` matches the Phase-13/14 `Graph`-native style, where
the multigraph carries the combinatorial data the matroid-union route consumes. -/
structure BodyBarFramework (n : ℕ) (α β : Type*) where
  /-- The underlying multigraph: bodies are vertices, bars are edges. -/
  graph : Graph α β
  /-- The placement: each bar `e ∈ E(graph)` gets a two-extensor coordinate in
  `ℝᵈ`, `d = n(n+1)/2`. Degenerate coordinates are permitted. -/
  placement : E(graph) → EuclideanSpace ℝ (Fin (bodyBarDim n))

namespace BodyBarFramework

variable {n : ℕ}

/-- A **body motion** of a body-bar framework in `ℝⁿ`: an assignment of a
velocity in `ℝᵈ`, `d = n(n+1)/2`, to each body. As in the bar-joint case
(`SimpleGraph.Framework`), the motion is a map out of the full vertex type
`α`; only the values on `V(graph)` enter the bar constraints, but typing the
domain as `α` avoids subtype coercions on the endpoints `Graph.orientation.dInc`
returns. -/
abbrev Motion (n : ℕ) (α : Type*) : Type _ := α → EuclideanSpace ℝ (Fin (bodyBarDim n))

/-- The `(u, v)`-**bar row** of a body-bar framework as a linear functional on
body motions: `m ↦ ⟪bₑ, m u - m v⟫_ℝ`, where `bₑ` is the bar's two-extensor
coordinate. The body-bar analogue of `SimpleGraph.edgeRow`; with the
infinitesimal-rotation factor absorbed into `bₑ`'s Plücker coordinates the
constraint is just the inner product of `bₑ` against the relative body velocity
(Whiteley~1988 §3). Internal building block for `rigidityMap`. -/
noncomputable def barRow (bₑ : EuclideanSpace ℝ (Fin (bodyBarDim n))) (u v : α) :
    Motion n α →ₗ[ℝ] ℝ :=
  ((innerSL ℝ bₑ).toLinearMap).comp
    ((LinearMap.proj u : Motion n α →ₗ[ℝ] EuclideanSpace ℝ (Fin (bodyBarDim n))) -
      LinearMap.proj v)

@[simp]
theorem barRow_apply (bₑ : EuclideanSpace ℝ (Fin (bodyBarDim n))) (u v : α)
    (m : Motion n α) : barRow bₑ u v m = ⟪bₑ, m u - m v⟫_ℝ := rfl

/-- The **rigidity map** of a body-bar framework `F` for a choice of orientation
`D` (Whiteley~1988 §3; `def:rigidity-map-body-bar`): the `ℝ`-linear map sending a
body motion `m : Motion n α` to the family of bar constraints
`e ↦ ⟪F.placement e, m u - m v⟫_ℝ` indexed by the bars `e ∈ E(F.graph)`, where
`(u, v) = D.dInc e` are the bar's oriented endpoints.

One row per bar. Built compositionally as `LinearMap.pi` over the per-bar
`barRow`s, so linearity in `m` is inherited from the `LinearMap` API. The
orientation `D` only fixes the sign of each constraint (swapping `u, v` negates
the row); the kernel and rank — the data infinitesimal rigidity reads off — are
orientation-independent. -/
noncomputable def rigidityMap {α β : Type*} (F : BodyBarFramework n α β)
    (D : Graph.orientation F.graph) :
    Motion n α →ₗ[ℝ] (E(F.graph) → ℝ) :=
  LinearMap.pi fun e : E(F.graph) =>
    barRow (F.placement e) (D.dInc e).1 (D.dInc e).2

/-- The rigidity map evaluated at a bar `e` is the inner product
`⟪F.placement e, m u - m v⟫_ℝ` of the bar's two-extensor coordinate against the
relative body velocity at its oriented endpoints `(u, v) = D.dInc e`. -/
@[simp]
theorem rigidityMap_apply {α β : Type*} (F : BodyBarFramework n α β)
    (D : Graph.orientation F.graph) (m : Motion n α) (e : E(F.graph)) :
    F.rigidityMap D m e = ⟪F.placement e, m (D.dInc e).1 - m (D.dInc e).2⟫_ℝ := rfl

/-- A body-bar framework `F` is **independent** at an orientation `D` when its
rigidity map has full row rank — `rank = |E(F.graph)|`, i.e. its bar-constraint
rows are linearly independent (no redundant bars). This is the body-bar analogue
of `SimpleGraph.EdgeSetRowIndependent` on the whole edge set; it is the notion of
"independent body-bar framework" in Tay's theorem (`thm:tay-witness`). The rank is
orientation-independent (see `rigidityMap`), so independence does not depend on the
choice of `D`. -/
def IsIndependent {α β : Type*} (F : BodyBarFramework n α β)
    (D : Graph.orientation F.graph) : Prop :=
  Module.finrank ℝ (LinearMap.range (F.rigidityMap D)) = E(F.graph).ncard

/-- A body-bar framework `F` on `b = F.graph.vertexSet.ncard` bodies is
**infinitesimally rigid** (Whiteley~1988 §3; `def:infinitesimally-rigid-body-bar`)
when its rigidity map for an orientation `D` has rank `d·b − d`, `d = bodyBarDim n` —
equivalently its kernel is exactly the `d`-dimensional space of trivial screw
motions of `ℝⁿ` (the body-bar analogue of `SimpleGraph.IsInfinitesimallyRigid`'s
kernel bound). Following the project's no-ℕ-subtraction convention, the count
`d·b − d` is phrased as the equality `rank + d = d·b`.

The orientation `D` only fixes per-row signs, so the rank — and hence this
predicate — is orientation-independent (see `rigidityMap`). -/
-- `[Finite α]` is a semantic contract guard: with `α` infinite the body-motion
-- space `Motion n α = α → ℝᵈ` is infinite-dimensional and the rank count is
-- meaningless. It is not consumed by elaboration of the body, so the
-- `unusedArguments` env-linter fires; the guard prevents callers from applying
-- this to an infinite body set. (Same disposition as `Framework.lean`'s
-- `SimpleGraph.IsInfinitesimallyRigid`; once `unusedFintypeInType` extends to
-- `def`s this would migrate to `set_option linter.unusedFintypeInType false`.)
@[nolint unusedArguments]
def IsInfinitesimallyRigid {α β : Type*} [Finite α] (F : BodyBarFramework n α β)
    (D : Graph.orientation F.graph) : Prop :=
  Module.finrank ℝ (LinearMap.range (F.rigidityMap D)) + bodyBarDim n
    = bodyBarDim n * F.graph.vertexSet.ncard

end BodyBarFramework

end Graph
