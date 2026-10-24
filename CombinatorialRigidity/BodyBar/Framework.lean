/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Matroid.Graph.Matrix

/-!
# Body-bar frameworks (`def:body-bar-framework`)

Following Tay 1984 (*Rigidity of multi-graphs. I*, J. Combin. Theory Ser. B **36**,
Definition 5.1) and Whiteley 1988 (*The union of matroids and the rigidity of frameworks*,
SIAM J. Disc. Math. **1**, §3), a **body-bar framework** in `ℝⁿ` on a multigraph
`G : Graph α β` pairs `G` with a *placement* assigning each bar `e ∈ E(G)` a vector of `ℝᵈ`,
where `d = n(n+1)/2` is the dimension of the space of infinitesimal rigid motions of `ℝⁿ`
(translations + infinitesimal rotations).

Whiteley takes for each bar the Plücker coordinates of its line, a two-extensor: a vector of
`ℝᵈ`, the space into which the Plücker embedding sends the lines of projective `n`-space, that
satisfies the quadratic Plücker relations. As Tay does, the placement here is an unconstrained
map into `ℝᵈ`, not a map into the Plücker variety. The existence half of Tay's theorem
(`thm:tay-witness`) is witnessed by the standard-basis placement `b_e = e_{j(e)}`; each standard
basis vector satisfies the Plücker relations and is the Plücker vector of a line (Whiteley 1988,
proof of Theorem 8, p. 243), so the theorem also holds for bars that are lines. Its generic form
for bars given by their endpoints is `BodyBar/GenericLift.lean`'s.

## Main definitions

* `Graph.bodyBarDim` — the body-bar dimension `d = n(n+1)/2` of `ℝⁿ`.
* `Graph.BodyBarFramework` — a body-bar framework: a multigraph `G` together
  with a placement `E(G) → EuclideanSpace ℝ (Fin (bodyBarDim n))`.
* `Graph.BodyBarFramework.rigidityMap` — the bar-constraint rigidity map, an
  `ℝ`-linear map from body motions (`α → ℝᵈ`) to bar constraints
  (`E(G) → ℝ`), one row per bar (`def:rigidity-map-body-bar`).
* `Graph.BodyBarFramework.IsIndependent`, `Graph.BodyBarFramework.IsInfinitesimallyRigid` —
  independence and infinitesimal rigidity, by the rank of the rigidity map
  (`def:independent-body-bar`, `def:infinitesimally-rigid-body-bar`).

The blueprint presents the file in `sec:body-bar-framework`.
-/

@[expose] public section

open scoped InnerProductSpace

namespace Graph

variable {α β : Type*}

/-- The **body-bar dimension** of `ℝⁿ`: `d = n(n+1)/2`, the dimension of the
space of infinitesimal rigid motions of `ℝⁿ` (the `n` translations plus the
`n(n-1)/2` independent infinitesimal rotations). Equivalently the dimension of
the space `ℝᵈ` of the two-extensors of `ℝⁿ⁺¹`, the Plücker coordinates of lines; a bar in
`ℝⁿ` carries a vector of this space. -/
def bodyBarDim (n : ℕ) : ℕ := n * (n + 1) / 2

/-- `bodyBarDim 2 = 3`: two translations plus one planar rotation. -/
lemma bodyBarDim_two : bodyBarDim 2 = 3 := rfl

/-- `bodyBarDim 3 = 6`: three translations plus three spatial rotations. -/
lemma bodyBarDim_three : bodyBarDim 3 = 6 := rfl

/-- **The body-bar dimension is at least `6` once `n ≥ 3`**: `bodyBarDim` is the increasing
sequence `0, 1, 3, 6, 10, …`. This turns the hypothesis `3 ≤ n` that a caller states into the
bound `6 ≤ bodyBarDim n` that the theorems for `n ≥ 3` use. -/
theorem six_le_bodyBarDim {n : ℕ} (hn : 3 ≤ n) : 6 ≤ bodyBarDim n := by
  rw [bodyBarDim, Nat.le_div_iff_mul_le (by norm_num)]
  calc 6 * 2 = 3 * 4 := by norm_num
    _ ≤ n * (n + 1) := Nat.mul_le_mul hn (by omega)

/-- **The body-bar dimension is at least `3` once `n ≥ 2`**, the bound the theorems for
`n ≥ 2` use (`bodyBarDim 2 = 3`). From `2 · bodyBarDim n = n(n+1)` by `nlinarith`. -/
theorem three_le_bodyBarDim_of_two_le {n : ℕ} (hn : 2 ≤ n) : 3 ≤ bodyBarDim n := by
  have hbb : 2 * bodyBarDim n = n * (n + 1) := by
    rw [bodyBarDim, Nat.mul_div_cancel' (Nat.even_mul_succ_self n).two_dvd]
  nlinarith

/-- A **body-bar framework** in `ℝⁿ` on a multigraph `G : Graph α β`
(`def:body-bar-framework`; Tay 1984, Definition 5.1): the multigraph `G` together with a
**placement** assigning each bar `e ∈ E(G)` a vector of `ℝᵈ`, `d = n(n+1)/2`
(`Graph.bodyBarDim n`).

The placement is an unconstrained map into `EuclideanSpace ℝ (Fin (bodyBarDim n))`: a bar's
vector need not satisfy the Plücker relations that make it the Plücker vector of a line, as
Whiteley's bars do (1988, §3; see the module docstring). -/
structure BodyBarFramework (n : ℕ) (α β : Type*) where
  /-- The underlying multigraph: bodies are vertices, bars are edges. -/
  graph : Graph α β
  /-- The placement: each bar `e ∈ E(graph)` gets a vector of `ℝᵈ`, `d = n(n+1)/2`, any
  vector, not only the Plücker vector of a line. -/
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
body motions: `m ↦ ⟪bₑ, m u - m v⟫_ℝ`, where `bₑ` is the bar's vector. The body-bar
analogue of `SimpleGraph.edgeRow`: with the screws written in dual coordinates the constraint
is the inner product of `bₑ` with the relative body velocity (Whiteley 1988, §3). Internal
building block for `rigidityMap`. -/
noncomputable def barRow (bₑ : EuclideanSpace ℝ (Fin (bodyBarDim n))) (u v : α) :
    Motion n α →ₗ[ℝ] ℝ :=
  ((innerSL ℝ bₑ).toLinearMap).comp
    ((LinearMap.proj u : Motion n α →ₗ[ℝ] EuclideanSpace ℝ (Fin (bodyBarDim n))) -
      LinearMap.proj v)

@[simp]
theorem barRow_apply (bₑ : EuclideanSpace ℝ (Fin (bodyBarDim n))) (u v : α)
    (m : Motion n α) : barRow bₑ u v m = ⟪bₑ, m u - m v⟫_ℝ := rfl

/-- The **rigidity map** of a body-bar framework `F` for a choice of orientation
`D` (`def:rigidity-map-body-bar`; Whiteley 1988, §3): the `ℝ`-linear map sending a
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

/-- A body-bar framework `F` is **independent** at an orientation `D`
(`def:independent-body-bar`) when its rigidity map has full row rank — `rank = |E(F.graph)|`,
i.e. its bar-constraint rows are linearly independent (no redundant bars). This is the body-bar
analogue of `SimpleGraph.EdgeSetRowIndependent` on the whole edge set, and the notion of
independence in Tay's theorem (`thm:tay-witness`). Reversing a bar negates its row, so
independence does not depend on the choice of `D`. -/
def IsIndependent {α β : Type*} (F : BodyBarFramework n α β)
    (D : Graph.orientation F.graph) : Prop :=
  Module.finrank ℝ (LinearMap.range (F.rigidityMap D)) = E(F.graph).ncard

/-- A body-bar framework `F` on `b = F.graph.vertexSet.ncard` bodies is
**infinitesimally rigid** (`def:infinitesimally-rigid-body-bar`; Whiteley 1988, §3)
when its rigidity map for an orientation `D` has rank `d·b − d`, `d = bodyBarDim n` (the
body-bar analogue of `SimpleGraph.IsInfinitesimallyRigid`'s rank count). When every element of
`α` is a body and there is at least one, this says that the kernel is the `d`-dimensional space
of constant motions, Whiteley's trivial motions; a motion is a function on all of `α`, so its
values off `V(F.graph)` also lie in the kernel. Following the project's no-ℕ-subtraction
convention, the count `d·b − d` is phrased as the equality `rank + d = d·b`.

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
