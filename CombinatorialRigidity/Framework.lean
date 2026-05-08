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

/-- The dimension of the framework space: `#V` copies of `EuclideanSpace ℝ (Fin d)`. -/
@[simp]
theorem Framework.finrank [Fintype V] :
    Module.finrank ℝ (Framework V d) = Fintype.card V * d := by
  simp [Module.finrank_pi_fintype]

/-- The `(u, v)`-row of the rigidity matrix as a linear functional on framework
motions: `x ↦ ⟪p u - p v, x u - x v⟫_ℝ`. Internal building block for
`RigidityMap`; consumers go through `rigidityMap_apply` instead. -/
private noncomputable def edgeRow (p : Framework V d) (u v : V) :
    Framework V d →ₗ[ℝ] ℝ :=
  ((innerSL ℝ (p u - p v)).toLinearMap).comp
    ((LinearMap.proj u : Framework V d →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) -
      LinearMap.proj v)

@[simp]
private theorem edgeRow_apply (p : Framework V d) (u v : V) (x : Framework V d) :
    edgeRow p u v x = ⟪p u - p v, x u - x v⟫_ℝ := rfl

private theorem edgeRow_symm (p : Framework V d) (u v : V) :
    edgeRow p u v = edgeRow p v u := by
  ext x
  rw [edgeRow_apply, edgeRow_apply, ← neg_sub (p u) (p v), ← neg_sub (x u) (x v),
      inner_neg_neg]

/-- The **rigidity map** of a framework `p`: an `ℝ`-linear map sending an
infinitesimal motion `p' : Framework V d` to the family
`e ↦ ⟪p u - p v, p' u - p' v⟫_ℝ` indexed by the edges `e = s(u, v) ∈ G.edgeSet`.

Built compositionally as `LinearMap.pi` over the per-edge `edgeRow`s, so
linearity in `p'` is inherited from the existing `LinearMap` API. -/
noncomputable def RigidityMap (G : SimpleGraph V) (p : Framework V d) :
    Framework V d →ₗ[ℝ] (G.edgeSet → ℝ) :=
  LinearMap.pi fun e : G.edgeSet =>
    Sym2.lift ⟨edgeRow p, edgeRow_symm p⟩ e.val

/-- The rigidity map evaluated at an explicit edge `s(u, v)` is the inner product
`⟪p u - p v, p' u - p' v⟫_ℝ`. -/
@[simp]
theorem rigidityMap_apply (G : SimpleGraph V) (p p' : Framework V d) (u v : V)
    (huv : s(u, v) ∈ G.edgeSet) :
    G.RigidityMap p p' ⟨s(u, v), huv⟩ = ⟪p u - p v, p' u - p' v⟫_ℝ := by
  simp [RigidityMap]

/-- The rigidity map's kernel shrinks under graph inclusion: adding edges can only
add constraints, never remove them. -/
theorem rigidityMap_ker_mono {G G' : SimpleGraph V} (h : G ≤ G') (p : Framework V d) :
    LinearMap.ker (G'.RigidityMap p) ≤ LinearMap.ker (G.RigidityMap p) := by
  intro p' hp'
  rw [LinearMap.mem_ker] at hp' ⊢
  funext ⟨e, he⟩
  exact congr_fun hp' ⟨e, edgeSet_mono h he⟩

/-- The rank of the rigidity map is bounded by the number of edges. -/
theorem rigidityMap_finrank_range_le [Finite V] (G : SimpleGraph V) (p : Framework V d) :
    Module.finrank ℝ (LinearMap.range (G.RigidityMap p)) ≤ G.edgeSet.ncard := by
  classical
  haveI : Fintype G.edgeSet := Set.Finite.fintype G.edgeSet.toFinite
  calc Module.finrank ℝ (LinearMap.range (G.RigidityMap p))
      ≤ Module.finrank ℝ (G.edgeSet → ℝ) := Submodule.finrank_le _
    _ = Fintype.card G.edgeSet := Module.finrank_pi ℝ
    _ = G.edgeSet.ncard := by
        rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]

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

/-- Adding edges preserves infinitesimal rigidity at the same placement. -/
theorem IsInfinitesimallyRigid.mono [Fintype V] {G G' : SimpleGraph V} (h : G ≤ G')
    {p : Framework V d} (hG : G.IsInfinitesimallyRigid p) : G'.IsInfinitesimallyRigid p :=
  (Submodule.finrank_mono (rigidityMap_ker_mono h p)).trans hG

/-- Adding edges preserves generic rigidity. -/
theorem IsGenericallyRigid.mono [Fintype V] {G G' : SimpleGraph V} (h : G ≤ G')
    (hG : G.IsGenericallyRigid d) : G'.IsGenericallyRigid d :=
  hG.imp fun _ => IsInfinitesimallyRigid.mono h

/-- A generically rigid graph in dimension `d` on `n` vertices has at least
`d * n − d(d+1)/2` edges. Phrased additively per the no-`ℕ`-subtraction rule.

The proof is rank-nullity: pick an infinitesimally rigid placement `p`; then
`d * n = dim Framework = dim range + dim ker ≤ #E + d(d+1)/2`. -/
theorem IsGenericallyRigid.card_mul_le [Fintype V] {G : SimpleGraph V}
    (hG : G.IsGenericallyRigid d) :
    d * Fintype.card V ≤ G.edgeSet.ncard + d * (d + 1) / 2 := by
  obtain ⟨p, h_ker⟩ := hG
  have h_ker : Module.finrank ℝ (LinearMap.ker (G.RigidityMap p)) ≤ d * (d + 1) / 2 := h_ker
  have h_total : Module.finrank ℝ (Framework V d) = d * Fintype.card V := by
    rw [Framework.finrank, mul_comm]
  have h_rn := LinearMap.finrank_range_add_finrank_ker (G.RigidityMap p)
  have h_range := G.rigidityMap_finrank_range_le p
  omega

/-- The K₂ worked example: the complete graph on two vertices is generically
rigid in any dimension `d`. For `d ≥ 1` we use the placement `p 0 = 0`,
`p 1 = e₀` (first standard basis vector); for `d = 0` the framework space is
itself zero-dimensional and any placement is vacuously rigid. -/
theorem top_fin_two_isGenericallyRigid (d : ℕ) :
    (⊤ : SimpleGraph (Fin 2)).IsGenericallyRigid d := by
  rcases d with _ | d
  · -- d = 0: framework space is zero-dimensional, so any placement is rigid.
    refine ⟨0, ?_⟩
    change Module.finrank ℝ (LinearMap.ker _) ≤ 0
    have h_total : Module.finrank ℝ (Framework (Fin 2) 0) = 0 := by
      rw [Framework.finrank]; simp
    exact (Submodule.finrank_le _).trans_eq h_total
  · -- d ≥ 1: place vertices at 0 and e₀.
    set p : Framework (Fin 2) (d + 1) := ![0, EuclideanSpace.single 0 1] with hp_def
    refine ⟨p, ?_⟩
    change Module.finrank ℝ (LinearMap.ker
      ((⊤ : SimpleGraph (Fin 2)).RigidityMap p)) ≤ (d + 1) * (d + 2) / 2
    have h_edge : s((0 : Fin 2), 1) ∈ (⊤ : SimpleGraph (Fin 2)).edgeSet := by simp
    have h_total : Module.finrank ℝ (Framework (Fin 2) (d + 1)) = 2 * (d + 1) := by
      rw [Framework.finrank]; simp
    have h_rn :=
      LinearMap.finrank_range_add_finrank_ker ((⊤ : SimpleGraph (Fin 2)).RigidityMap p)
    have h_range_pos :
        1 ≤ Module.finrank ℝ (LinearMap.range
          ((⊤ : SimpleGraph (Fin 2)).RigidityMap p)) := by
      rw [Submodule.one_le_finrank_iff, Ne, LinearMap.range_eq_bot]
      intro h_eq
      have h_val :
          (⊤ : SimpleGraph (Fin 2)).RigidityMap p ![EuclideanSpace.single 0 1, 0]
            ⟨s(0, 1), h_edge⟩ = -1 := by
        simp [rigidityMap_apply, hp_def, inner_neg_left]
      have h_zero :
          (⊤ : SimpleGraph (Fin 2)).RigidityMap p ![EuclideanSpace.single 0 1, 0]
            ⟨s(0, 1), h_edge⟩ = 0 := by rw [h_eq]; rfl
      linarith
    -- bound: 2*(d+1) - 1 = 2d+1 ≤ (d+1)(d+2)/2 for all d ≥ 0
    have h_quadratic : 4 * d + 2 ≤ (d + 1) * (d + 2) := by
      have : (d + 1) * (d + 2) = d * d + 3 * d + 2 := by ring
      have := Nat.le_mul_self d
      omega
    omega

end SimpleGraph
