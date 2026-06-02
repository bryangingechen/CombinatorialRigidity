/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.BodyBar.TreePacking
import Matroid.Representation.Map
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# The generic `k`-frame matroid (`def:k-frame-matroid`)

Phase 14. Whiteley 1988 (*The union of matroids and the rigidity of frameworks*,
SIAM J. Disc. Math. **1**, Theorem 1) introduces, for a multigraph `G : Graph α β`
and `k ≥ 1`, the generic **`k`-frame matroid** `F(G, X)`: the linear matroid (via
`Matroid.ofFun`, the same `apnelson1/Matroid` constructor `LinearRigidityMatroid.lean`
uses for the planar case) of the formal `k · |V|`-column matrix whose row for a bar
`e` carries indeterminate coefficients across `k` vertex blocks, with each block
placing a copy of the (signed) graph-incidence pattern of `e`.

This file ships the definition; the identification `F(G, X) = ⋃ⱼ G.cycleMatroid`
(`thm:k-frame-union-cycle`, the single remaining Phase-14 node) is deferred.

## Coefficient encoding

The genericity is realized over **true indeterminates**, not a real placement (cf.
the Phase-8 `linearRigidityMatroid`, which parametrizes by `p : Framework V d` and
proves genericity by a separate ℝ-perturbation): the coefficient field is

  `K := FractionRing (MvPolynomial (β × Fin k) ℚ)`,

with one indeterminate `X (e, j)` per (bar, block) pair. The row for bar `e` in block
`j` is `X (e, j) • D.signedIncMatrix K e` — the indeterminate scaling of the signed
incidence row of `e` for a chosen orientation `D` of `G` (the same row vector
`Graph.cycleMatroidRep` represents `G.cycleMatroid` by). The orientation is picked by
`G.orientation_nonempty.some`, matching `cycleMatroidRep`; the choice is harmless for
the generic matroid (orientations differ only by a per-row sign). The row vector lives
in `Fin k → α → K`, the `k`-fold copy of the incidence-row space `α → K` —
`k · |V|`-dimensional, the blueprint's "`k` vertex blocks".

This indeterminate encoding is what powers the deferred
`thm:k-frame-union-cycle`'s column-reorder / nonzero-monomial argument (Whiteley §2.1):
a nonzero monomial of an `|E|`-minor's determinant, with its variables set to `1` and
the rest to `0`, exhibits a block-diagonal forest-incidence matrix.

See `ROADMAP.md` §14, `notes/Phase14.md`, and the *The `k`-frame matroid as a union of
cycle matroids* subsection of `blueprint/src/chapter/body-bar.tex`.
-/

namespace Graph

open Matroid

variable {α β : Type*}

/-- The coefficient field of the generic `k`-frame matroid: the field of fractions of
the multivariate polynomial ring `MvPolynomial (β × Fin k) ℚ`, carrying one indeterminate
`MvPolynomial.X (e, j)` per (bar, block) pair `(e, j) : β × Fin k`. A genuine field (the
fraction field of an integral domain), as `Matroid.ofFun` requires a `DivisionRing`. -/
abbrev KFrameField (β : Type*) (k : ℕ) : Type _ :=
  FractionRing (MvPolynomial (β × Fin k) ℚ)

/-- The indeterminate `X_{(e, j)}` of `KFrameField β k`, the generic coefficient on the
incidence row of bar `e` in vertex block `j`. -/
noncomputable def kFrameIndet (k : ℕ) (e : β) (j : Fin k) : KFrameField β k :=
  algebraMap (MvPolynomial (β × Fin k) ℚ) (KFrameField β k) (MvPolynomial.X (e, j))

/-- The **`k`-frame row function** for an orientation `D` of `G`: the row for bar `e`,
as a vector in the `k · |V|`-dimensional space `Fin k → α → KFrameField β k`, places in
each vertex block `j` the indeterminate scaling `X_{(e, j)} • (signed incidence row of e)`
of `e`'s signed graph-incidence row (`Graph.orientation.signedIncMatrix`). Off the edge
set the signed incidence row is `0`, so the row is `0` there. -/
noncomputable def kFrameRow {G : Graph α β} (k : ℕ) (D : Graph.orientation G) :
    β → (Fin k → α → KFrameField β k) :=
  letI : DecidableEq α := Classical.decEq α
  letI : DecidablePred (· ∈ E(G)) := Classical.decPred _
  fun e j => kFrameIndet k e j • D.signedIncMatrix (KFrameField β k) e

/-- The **generic `k`-frame matroid** `F(G, X)` of a multigraph `G : Graph α β`
(Whiteley 1988, Theorem 1; `def:k-frame-matroid`): the linear matroid on the bar type
`β`, with ground set `E(G)`, of the `k`-frame row function over the indeterminate
coefficient field `KFrameField β k`. Built via `Matroid.ofFun`, like the planar
`SimpleGraph.linearRigidityMatroid`. The orientation is picked by
`G.orientation_nonempty.some`, matching `Graph.cycleMatroidRep`.

The identification `kFrameMatroid G k = Matroid.Union (fun _ : Fin k ↦ G.cycleMatroid)`
(`thm:k-frame-union-cycle`) is the remaining Phase-14 target. -/
noncomputable def kFrameMatroid (G : Graph α β) (k : ℕ) : Matroid β :=
  Matroid.ofFun (KFrameField β k) E(G) (kFrameRow k G.orientation_nonempty.some)

@[simp]
theorem kFrameMatroid_ground (G : Graph α β) (k : ℕ) :
    (G.kFrameMatroid k).E = E(G) := by
  rw [kFrameMatroid, Matroid.ofFun_ground_eq]

section Forward

open Submodule

variable {G : Graph α β} {k : ℕ} {D : Graph.orientation G}

/-- The `Fin k`-fold product subspace whose `j`-th block is the `KFrameField β k`-span of
all signed incidence rows of `G`. The `k`-frame row of every bar lives in this subspace
(`kFrameRow_mem_blockPiSpan`), so the whole `k`-frame row space is contained in it
(`span_kFrameRow_le_blockPiSpan`); its `K`-dimension is `k · (dim of the incidence-row
span)`, the upper bound in Whiteley §2.1's rank count. -/
noncomputable def blockPiSpan (G : Graph α β) (k : ℕ) (D : Graph.orientation G) :
    Submodule (KFrameField β k) (Fin k → α → KFrameField β k) :=
  letI : DecidableEq α := Classical.decEq α
  letI : DecidablePred (· ∈ E(G)) := Classical.decPred _
  Submodule.pi Set.univ
    (fun _ : Fin k ↦ span (KFrameField β k) (Set.range (D.signedIncMatrix (KFrameField β k))))

/-- Each `k`-frame row `kFrameRow k D e` lies in the block-diagonal product subspace
`blockPiSpan`: in each block `j`, the row is the scalar multiple
`X_{(e,j)} • signedIncMatrix e`, which lies in the span of the incidence rows. This is the
per-row half of the rank-counting bound for the forward direction of Whiteley §2.1
(`lem:k-frame-nonzero-monomial-forest`). -/
theorem kFrameRow_mem_blockPiSpan (e : β) :
    kFrameRow k D e ∈ blockPiSpan G k D := by
  classical
  rw [blockPiSpan, Submodule.mem_pi]
  intro j _
  rw [kFrameRow]
  exact Submodule.smul_mem _ _ (subset_span ⟨e, rfl⟩)

/-- The span of all `k`-frame rows is contained in the block-diagonal product subspace
`blockPiSpan`. Combined with the dimension count `finrank (blockPiSpan) = k · (incidence
row span dimension)`, this gives the upper half of Whiteley §2.1's count for the forward
direction of `lem:k-frame-nonzero-monomial-forest`: linear independence of the `k`-frame
rows on `E'` forces `|E'| ≤ k · r_{cycleMatroid}(E')`. -/
theorem span_kFrameRow_le_blockPiSpan :
    span (KFrameField β k) (Set.range (kFrameRow k D)) ≤ blockPiSpan G k D := by
  rw [span_le]
  rintro _ ⟨e, rfl⟩
  exact kFrameRow_mem_blockPiSpan e

end Forward

end Graph
