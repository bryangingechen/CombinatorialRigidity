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

/-- The `Fin k`-fold constant product subspace `Submodule.pi univ (fun _ ↦ W)` is linearly
equivalent to the plain product `Fin k → ↥W` of the block submodule with itself. The forward
map projects each block; the inverse re-bundles. Generic-block helper for the dimension count
`finrank (constPiSpan) = k · finrank W`. -/
noncomputable def constPiSpanEquiv {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (n : ℕ) (W : Submodule R M) :
    (Submodule.pi Set.univ (fun _ : Fin n ↦ W) : Submodule R (Fin n → M)) ≃ₗ[R] (Fin n → W) where
  toFun f i := ⟨f.1 i, f.2 i (Set.mem_univ i)⟩
  invFun g := ⟨fun i ↦ (g i : M), fun i _ ↦ (g i).2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The `K`-dimension of the constant `Fin k`-fold product subspace is `k` times the dimension of
the block submodule `W`. Piece (1) of the forward rank count of Whiteley §2.1
(`lem:k-frame-nonzero-monomial-forest`): applied with `W` the `K`-span of the signed incidence
rows of a bar set, it turns the `blockPiSpan` upper bound into `k · (incidence-span dimension)`. -/
theorem finrank_constPiSpan {R M : Type*} [DivisionRing R] [AddCommGroup M] [Module R M]
    (n : ℕ) (W : Submodule R M) [Module.Finite R W] :
    Module.finrank R (Submodule.pi Set.univ (fun _ : Fin n ↦ W) : Submodule R (Fin n → M))
      = n * Module.finrank R W := by
  rw [(constPiSpanEquiv n W).finrank_eq, Module.finrank_pi_fintype R]
  simp

/-- The `Fin k`-fold product subspace whose `j`-th block is the `KFrameField β k`-span of the
signed incidence rows indexed by a bar set `Y` (the `Y`-restricted analogue of `blockPiSpan`).
For `e ∈ Y` the `k`-frame row `kFrameRow k D e` lies in this subspace
(`kFrameRow_mem_blockPiSpanOn`), so the span of the `k`-frame rows on `Y` is contained in it
(`span_kFrameRowOn_le_blockPiSpanOn`); its `K`-dimension is `k` times the dimension of the
`Y`-incidence-row span, i.e. `k · r_{cycleMatroid}(Y)` — the per-`Y` upper bound in
Whiteley §2.1's rank count. -/
noncomputable def blockPiSpanOn (G : Graph α β) (k : ℕ) (D : Graph.orientation G) (Y : Set β) :
    Submodule (KFrameField β k) (Fin k → α → KFrameField β k) :=
  letI : DecidableEq α := Classical.decEq α
  letI : DecidablePred (· ∈ E(G)) := Classical.decPred _
  Submodule.pi Set.univ
    (fun _ : Fin k ↦ span (KFrameField β k) ((D.signedIncMatrix (KFrameField β k)) '' Y))

/-- Each `k`-frame row `kFrameRow k D e` of a bar `e ∈ Y` lies in the `Y`-restricted
block-diagonal product subspace `blockPiSpanOn G k D Y`: in each block `j` the row is the scalar
multiple `X_{(e,j)} • signedIncMatrix e`, which lies in the span of the incidence rows over `Y`
(since `e ∈ Y`). The `Y`-restricted analogue of `kFrameRow_mem_blockPiSpan`. -/
theorem kFrameRow_mem_blockPiSpanOn {Y : Set β} {e : β} (he : e ∈ Y) :
    kFrameRow k D e ∈ blockPiSpanOn G k D Y := by
  classical
  rw [blockPiSpanOn, Submodule.mem_pi]
  intro j _
  rw [kFrameRow]
  exact Submodule.smul_mem _ _ (subset_span ⟨e, he, rfl⟩)

/-- The span of the `k`-frame rows indexed by `Y` is contained in the `Y`-restricted
block-diagonal product subspace `blockPiSpanOn G k D Y`. The `Y`-restricted analogue of
`span_kFrameRow_le_blockPiSpan`, with `r(Y)` in place of `r(E(G))`. -/
theorem span_kFrameRowOn_le_blockPiSpanOn {Y : Set β} :
    span (KFrameField β k) (kFrameRow k D '' Y) ≤ blockPiSpanOn G k D Y := by
  rw [span_le]
  rintro _ ⟨e, he, rfl⟩
  exact kFrameRow_mem_blockPiSpanOn he

/-- **Span finrank = matroid rank, via a representation** (`lem:k-frame-nonzero-monomial-forest`,
piece (2)). For any finite-rank matroid `M` with a representation `v : M.Rep K W`, the `K`-dimension
of the span of `v '' Y` equals the matroid rank `M.rk Y`. A basis `I` of `Y` has `v '' Y ⊆ span (v
'' I)` and `LinearIndepOn K v I` (`Rep.isBasis'_iff`), so the two spans coincide; the LI image has
`finrank = (v '' I).ncard = I.ncard = M.rk Y` (`finrank_span_set_eq_card` + `IsBasis'.card`). -/
theorem _root_.Matroid.Rep.finrank_span_image_eq_rk {γ K W : Type*} [Field K] [AddCommGroup W]
    [Module K W] {M : Matroid γ} [M.RankFinite] (v : M.Rep K W) (Y : Set γ) :
    Module.finrank K (Submodule.span K (v '' Y)) = M.rk Y := by
  classical
  obtain ⟨I, hI⟩ := M.exists_isBasis' Y
  obtain ⟨_, hindep, hsub⟩ := v.isBasis'_iff.mp hI
  have hfinI : I.Finite := hI.indep.finite
  haveI : Fintype (v '' I) := (hfinI.image v).fintype
  have hspan : Submodule.span K (v '' Y) = Submodule.span K (v '' I) :=
    le_antisymm (Submodule.span_le.mpr hsub)
      (Submodule.span_mono (Set.image_mono hI.subset))
  rw [hspan, finrank_span_set_eq_card hindep.id_image, ← Set.ncard_eq_toFinset_card',
    hindep.injOn.ncard_image, hI.card]

/-- **Incidence-span finrank = cycle-matroid rank** (`lem:k-frame-nonzero-monomial-forest`,
piece (2)). For the orientation `G.orientation_nonempty.some` underlying `cycleMatroidRep` (the same
one `kFrameMatroid` / `blockPiSpan` use), the `K`-dimension of the span of the signed incidence rows
indexed by `Y` equals the cycle-matroid rank `G.cycleMatroid.rk Y`. This is the cycle-matroid
specialization of `Matroid.Rep.finrank_span_image_eq_rk` to `Graph.cycleMatroidRep`, whose
representation map is exactly `signedIncMatrix` for that orientation; it turns the
`finrank blockPiSpan = k · (incidence-span finrank)` bound of the forward rank count into
`k · r_{cycleMatroid}(Y)`. -/
theorem finrank_span_signedIncMatrix_eq_cycleMatroid_rk [Finite β] (K : Type*) [Field K]
    (Y : Set β) :
    letI : DecidableEq α := Classical.decEq α
    letI : DecidablePred (· ∈ E(G)) := Classical.decPred _
    Module.finrank K
        (Submodule.span K ((G.orientation_nonempty.some.signedIncMatrix K) '' Y))
      = G.cycleMatroid.rk Y := by
  classical
  haveI : G.EdgeFinite := by
    rw [edgeFinite_iff]; exact Set.toFinite _
  have hrep := (G.cycleMatroidRep K).finrank_span_image_eq_rk Y
  have he : ⇑(G.cycleMatroidRep K) = G.orientation_nonempty.some.signedIncMatrix K := rfl
  rw [he] at hrep
  exact hrep

/-- The `K`-dimension of the `Y`-restricted block-diagonal product subspace is `k` times the
dimension of the `Y`-incidence-row span, which is `k · r_{cycleMatroid}(Y)` (pieces (1) and (2)
of the forward rank count). Assembled from `finrank_constPiSpan` and
`finrank_span_signedIncMatrix_eq_cycleMatroid_rk`. -/
theorem finrank_blockPiSpanOn [Finite β] (Y : Set β) :
    Module.finrank (KFrameField β k)
        (blockPiSpanOn G k (G.orientation_nonempty.some) Y)
      = k * G.cycleMatroid.rk Y := by
  classical
  haveI : Module.Finite (KFrameField β k)
      (span (KFrameField β k)
        ((G.orientation_nonempty.some.signedIncMatrix (KFrameField β k)) '' Y)) :=
    Module.Finite.span_of_finite _ ((Set.toFinite Y).image _)
  rw [blockPiSpanOn, finrank_constPiSpan]
  congr 1
  exact finrank_span_signedIncMatrix_eq_cycleMatroid_rk (G := G) (KFrameField β k) Y

/-- **Generic independence ⟹ forest count** (`lem:k-frame-nonzero-monomial-forest`, the forward
half of Whiteley §2.1 by the rank count). If the generic `k`-frame rows on a bar set `E'` are
linearly independent over `K`, then `|Y| ≤ k · r_{cycleMatroid}(Y)` for every `Y ⊆ E'`.

Restricting `hLI` to `Y` keeps the `|Y|` rows independent, so `|Y| = finrank (span (kFrameRow ''
Y))` (`finrank_span_set_eq_card`); that span sits inside the `Y`-restricted block-diagonal product
subspace (`span_kFrameRowOn_le_blockPiSpanOn`), whose dimension is `k · r_{cycleMatroid}(Y)`
(`finrank_blockPiSpanOn`), giving the bound by `Submodule.finrank_mono`. -/
theorem forest_count_of_linearIndepOn_kFrameRow [Finite β] {E' : Set β}
    (hLI : LinearIndepOn (KFrameField β k) (kFrameRow k (G.orientation_nonempty.some)) E')
    {Y : Set β} (hYE' : Y ⊆ E') :
    Y.ncard ≤ k * G.cycleMatroid.rk Y := by
  classical
  set D := G.orientation_nonempty.some with hD
  set v := kFrameRow k (G := G) D with hv
  have hLIY : LinearIndepOn (KFrameField β k) v Y := hLI.mono hYE'
  -- `Y.ncard = finrank (span (v '' Y))`, via the LI image cardinality.
  haveI : Fintype (v '' Y) := (Set.toFinite (v '' Y)).fintype
  have hcard : Module.finrank (KFrameField β k) (span (KFrameField β k) (v '' Y)) = Y.ncard := by
    rw [finrank_span_set_eq_card hLIY.id_image, ← Set.ncard_eq_toFinset_card',
      hLIY.injOn.ncard_image]
  -- The block-product subspace is finite-dimensional (transport along `constPiSpanEquiv`).
  haveI : Module.Finite (KFrameField β k)
      (span (KFrameField β k)
        ((D.signedIncMatrix (KFrameField β k)) '' Y)) :=
    Module.Finite.span_of_finite _ ((Set.toFinite Y).image _)
  haveI : Module.Finite (KFrameField β k) (blockPiSpanOn G k D Y) := by
    rw [blockPiSpanOn]
    exact Module.Finite.equiv (constPiSpanEquiv k _).symm
  -- `finrank (span (v '' Y)) ≤ finrank (blockPiSpanOn) = k · r(Y)`.
  have hle := Submodule.finrank_mono (R := KFrameField β k)
    (span_kFrameRowOn_le_blockPiSpanOn (D := D) (Y := Y))
  rw [hcard, finrank_blockPiSpanOn] at hle
  exact hle

end Forward

end Graph
