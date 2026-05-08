/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Sparsity
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Frameworks and infinitesimal rigidity

A `d`-dimensional **framework** on a vertex set `V` is a placement
`p : V → EuclideanSpace ℝ (Fin d)`. Given a graph `G : SimpleGraph V`, the
**rigidity map** at `p` sends an infinitesimal motion `p' : Framework V d`
to the family of edge-length derivatives `e ↦ ⟪p u - p v, p' u - p' v⟫`
indexed by the edges `e = s(u, v) ∈ G.edgeSet`. Geometrically, this is the
differential at `p` of the squared-edge-length map (modulo a factor of two);
we define it directly via the explicit entry formula to avoid `fderiv` and
the differentiability machinery — none of which the rank/kernel arguments
downstream need.

A framework is **infinitesimally rigid** when the kernel of the rigidity
map has dimension at most `d (d+1) / 2`, the dimension of trivial Euclidean
motions (translations + infinitesimal rotations). It is **generically
rigid** when *some* placement is infinitesimally rigid.

These definitions are stated for general dimension `d`; the Laman-relevant
specialization to `d = 2` happens at the Phase 5 boundary.

## Main definitions

* `Framework V d` — placement type, `abbrev` for `V → EuclideanSpace ℝ (Fin d)`.
* `SimpleGraph.RigidityMap G p` — the rigidity map as an `ℝ`-linear map.
* `SimpleGraph.IsInfinitesimallyRigid G p` — kernel-dimension bound.
* `SimpleGraph.IsGenericallyRigid G d` — existence of a rigid placement.

## Project context

See `ROADMAP.md` for the project plan and `notes/Phase4.md` for the Phase 4
work log.
-/

open scoped InnerProductSpace

namespace SimpleGraph

variable {V : Type*} {d : ℕ}

/-- A `d`-dimensional **framework** on a vertex set `V` is a placement of `V`
into `EuclideanSpace ℝ (Fin d)`.

`abbrev` so that the Pi-`Module ℝ`, `AddCommGroup`, and finite-dimensional
instances on `V → EuclideanSpace ℝ (Fin d)` apply transparently. -/
abbrev Framework (V : Type*) (d : ℕ) : Type _ := V → EuclideanSpace ℝ (Fin d)

/-- The **rigidity map** of a framework `p`: an `ℝ`-linear map sending an
infinitesimal motion `p' : Framework V d` to the family
`e ↦ ⟪p u - p v, p' u - p' v⟫_ℝ` indexed by the edges `e = s(u, v) ∈ G.edgeSet`. -/
noncomputable def RigidityMap (G : SimpleGraph V) (p : Framework V d) :
    Framework V d →ₗ[ℝ] (G.edgeSet → ℝ) where
  toFun p' e := Sym2.lift
    ⟨fun u v => ⟪p u - p v, p' u - p' v⟫_ℝ, fun u v => by
      change ⟪p u - p v, p' u - p' v⟫_ℝ = ⟪p v - p u, p' v - p' u⟫_ℝ
      rw [← neg_sub (p u) (p v), ← neg_sub (p' u) (p' v), inner_neg_neg]⟩
    e.val
  map_add' p₁ p₂ := by
    funext e
    obtain ⟨e, _⟩ := e
    induction e with
    | h u v =>
      change ⟪p u - p v, (p₁ + p₂) u - (p₁ + p₂) v⟫_ℝ =
          ⟪p u - p v, p₁ u - p₁ v⟫_ℝ + ⟪p u - p v, p₂ u - p₂ v⟫_ℝ
      rw [show (p₁ + p₂) u - (p₁ + p₂) v = (p₁ u - p₁ v) + (p₂ u - p₂ v) by
            simp only [Pi.add_apply]; abel,
          inner_add_right]
  map_smul' c p' := by
    funext e
    obtain ⟨e, _⟩ := e
    induction e with
    | h u v =>
      change ⟪p u - p v, (c • p') u - (c • p') v⟫_ℝ = c * ⟪p u - p v, p' u - p' v⟫_ℝ
      rw [show (c • p') u - (c • p') v = c • (p' u - p' v) by
            simp [smul_sub],
          real_inner_smul_right]

/-- A framework `p` is **infinitesimally rigid** for `G` if the kernel of the
rigidity map has dimension at most `d (d+1) / 2`, the dimension of trivial
Euclidean motions (translations + infinitesimal rotations).

When this kernel is *equal* to the trivial motions, the framework is rigid in
the textbook sense; the inequality formulation is the always-correct upper
bound and is what fits naturally into the rank-nullity argument used
downstream. -/
def IsInfinitesimallyRigid [Fintype V] (G : SimpleGraph V) (p : Framework V d) : Prop :=
  Module.finrank ℝ (LinearMap.ker (G.RigidityMap p)) ≤ d * (d + 1) / 2

/-- A graph `G` is **generically rigid** in dimension `d` if some placement is
infinitesimally rigid.

This avoids the algebraic-geometry machinery of "generic placement"; the
equivalence to "rank max on a Zariski-open set of placements" is downstream
and not needed for either direction of Laman's theorem under the present plan. -/
def IsGenericallyRigid [Fintype V] (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∃ p : Framework V d, G.IsInfinitesimallyRigid p

end SimpleGraph
