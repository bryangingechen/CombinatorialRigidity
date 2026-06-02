/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.BodyBar.Framework
import CombinatorialRigidity.BodyBar.KFrame
import CombinatorialRigidity.Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Tay's theorem, existence form (`thm:tay-witness`)

Phase 15. Whiteley 1988 (*The union of matroids and the rigidity of frameworks*,
SIAM J. Disc. Math. **1**, Theorem 8), in the existence-of-realization form: for
`n ≥ 2` and `d = bodyBarDim n = n(n+1)/2`, a multigraph `G` carries an independent
body-bar framework in `ℝⁿ` iff it is `(d, d)`-sparse (equivalently — Phase 13 — the
edge-disjoint union of `d` forests), and an isostatic one iff `(d, d)`-tight (the
union of `d` spanning trees).

## Witness construction

The witness specializes each bar's two-extensor coordinate to a **standard basis
vector** `b_e = e_{j(e)} ∈ ℝᵈ`, where `j(e)` is the index of `e`'s forest in a
chosen tree-packing partition (`thm:tutte-nash-williams`). These degenerate
two-extensors lie on the Plücker variety vacuously (existence-of-realization scope;
see `Framework.lean`'s module docstring), so they form a valid body-bar realization.

With this placement the rigidity-map row for a bar `e` collapses to the single
coordinate `j(e)` of the relative body velocity (`stdPlacement_rigidityMap_apply`):
`⟪e_{j(e)}, m u − m v⟫ = (m u − m v)(j e)`. The rigidity matrix is therefore
**block-diagonal** across the `d` coordinates, the block at index `j` being the
signed incidence matrix of the forest `Fs j` (over `ℝ`). Each block has full row
rank (a forest's incidence rows are linearly independent —
`Graph.orientation.isAcyclicSet_linearIndepOn`), so the row rank of the whole matrix
is `Σⱼ |Fs j| = |E|`, i.e. the framework is independent. This is the reverse
direction of `thm:k-frame-union-cycle`
(`Graph.linearIndepOn_kFrameRow_of_isSparse_restrict`) lifted from indeterminate to
real coefficients.

## Contents

This file ships the witness placement, the bar-row reduction, the block-diagonal
rank count (`stdFramework_finrank_range`), both the **existence (⟸) direction**
(`prop:tay-witness-exists`: `exists_isIndependent_of_isSparse` and
`exists_isIsostatic_of_isTight`, the standard-basis witness on a tree packing) and
the **converse (⟹) direction** (`isSparse_of_isIndependent`, the block-diagonal rank
upper bound forcing `(d, d)`-sparsity), and hence the full `thm:tay-witness` iff
(`tay_witness`). See `notes/Phase15.md` and the §`sec:body-bar-tay` subsection of
`blueprint/src/chapter/body-bar.tex`.
-/

open scoped InnerProductSpace

namespace Graph

namespace BodyBarFramework

variable {α β : Type*} {n : ℕ}

/-- The **standard-basis placement** of a multigraph `G` from a forest-index map
`j : E(G) → Fin (bodyBarDim n)`: each bar `e` is assigned the standard basis
vector `e_{j(e)} = EuclideanSpace.single (j e) 1 ∈ ℝᵈ`, `d = bodyBarDim n`. This is
the witness placement of Tay's theorem (Whiteley 1988 §3): `j(e)` is the index of
`e`'s forest in a tree-packing partition, and `e_{j(e)}` is a (degenerate)
two-extensor. -/
noncomputable def stdPlacement (G : Graph α β) (n : ℕ)
    (j : E(G) → Fin (bodyBarDim n)) :
    E(G) → EuclideanSpace ℝ (Fin (bodyBarDim n)) :=
  fun e => EuclideanSpace.single (j e) (1 : ℝ)

/-- The **standard-basis body-bar framework** of `G` for a forest-index map `j`:
the body-bar framework whose placement is `stdPlacement G n j`. The witness object
of Tay's theorem. -/
noncomputable def stdFramework (G : Graph α β) (n : ℕ)
    (j : E(G) → Fin (bodyBarDim n)) : BodyBarFramework n α β where
  graph := G
  placement := stdPlacement G n j

@[simp]
theorem stdFramework_graph (G : Graph α β) (n : ℕ)
    (j : E(G) → Fin (bodyBarDim n)) : (stdFramework G n j).graph = G := rfl

@[simp]
theorem stdFramework_placement (G : Graph α β) (n : ℕ)
    (j : E(G) → Fin (bodyBarDim n)) :
    (stdFramework G n j).placement = stdPlacement G n j := rfl

/-- **Bar-row reduction at a standard-basis placement** (the foundational step of
the witness argument). With each bar `e` placed at the standard basis vector
`e_{j(e)}`, the rigidity-map row at `e` evaluated at a motion `m` collapses to the
single coordinate `j(e)` of the relative body velocity at `e`'s oriented endpoints
`(u, v) = D.dInc e`:
`(stdFramework G n j).rigidityMap D m e = (m u − m v) (j e)`.

This is what makes the rigidity matrix block-diagonal across the `d = bodyBarDim n`
coordinates: the row for `e` is supported entirely in coordinate `j(e)`, where it is
the signed incidence row of `e`. Over `ℝ`, `EuclideanSpace.inner_single_left` gives
`⟪e_{j(e)}, w⟫ = conj 1 · w (j e) = w (j e)`. -/
theorem stdPlacement_rigidityMap_apply (G : Graph α β) (n : ℕ)
    (j : E(G) → Fin (bodyBarDim n)) (D : Graph.orientation G)
    (m : Motion n α) (e : E(G)) :
    (stdFramework G n j).rigidityMap D m e
      = (m (D.dInc e).1 - m (D.dInc e).2) (j e) := by
  rw [rigidityMap_apply, stdFramework_placement, stdPlacement,
    EuclideanSpace.inner_single_left]
  simp

/-! ### Block-diagonal rank count

The independent-form half of `thm:tay-witness`: at the standard-basis placement of a
*disjoint forest packing*, the body-bar rigidity map has rank `|E(G)|`, so the framework
is independent. The argument is the reverse direction of `thm:k-frame-union-cycle`
(`Graph.linearIndepOn_kFrameRow_of_isSparse_restrict`) at the single real specialization
`b_e = e_{j(e)}`: the rigidity matrix is block-diagonal across the `d = bodyBarDim n`
coordinates, the block at index `j` being the signed incidence matrix of the forest
`Fs j` — full row rank by `Graph.orientation.isAcyclicSet_linearIndepOn` — so the rows
are linearly independent and the rank is `Σⱼ |Fs j| = |E(G)|`.

We follow Phase 6's `RigidityMatroid.lean` route to relate the row rank to the rank of
the map: the `e`-th `rigidityRow` is the functional `m ↦ rigidityMap D m e`, the span of
the rows is the range of the map's `dualMap`, and `finrank_range_dualMap_eq_finrank_range`
identifies the two ranks. -/

/-- The `e`-th **row** of the body-bar rigidity matrix at orientation `D`, as a linear
functional `m ↦ F.rigidityMap D m e` on body motions. The body-bar analogue of
`SimpleGraph.rigidityRow` (`RigidityMatroid.lean`). -/
noncomputable def rigidityRow (F : BodyBarFramework n α β) (D : Graph.orientation F.graph) :
    E(F.graph) → Module.Dual ℝ (Motion n α) :=
  fun e => (LinearMap.proj e).comp (F.rigidityMap D)

@[simp]
theorem rigidityRow_apply (F : BodyBarFramework n α β) (D : Graph.orientation F.graph)
    (e : E(F.graph)) (m : Motion n α) : F.rigidityRow D e m = F.rigidityMap D m e := rfl

/-- The rigidity rows span the range of the rigidity map's transpose. Combined with
`LinearMap.finrank_range_dualMap_eq_finrank_range` this is the row-rank-equals-column-rank
identity for the body-bar rigidity matrix; in span form it is
`LinearMap.range_dualMap_eq_span_image_dualBasis` applied to `Pi.basisFun ℝ E(F.graph)`.
Mirror of `SimpleGraph.span_range_rigidityRow`. -/
theorem span_range_rigidityRow (F : BodyBarFramework n α β) [Finite E(F.graph)]
    (D : Graph.orientation F.graph) :
    Submodule.span ℝ (Set.range (F.rigidityRow D)) =
      LinearMap.range (F.rigidityMap D).dualMap := by
  classical
  have h_row : F.rigidityRow D =
      (F.rigidityMap D).dualMap ∘ (Pi.basisFun ℝ E(F.graph)).dualBasis := by
    funext e; ext _; simp [rigidityRow]
  rw [h_row]
  exact (LinearMap.range_dualMap_eq_span_image_dualBasis (Pi.basisFun ℝ E(F.graph)) _).symm

/-- The **block-pairing map** `S w m = ∑ₓ ∑_c w c x · (m x) c`, sending a block-matrix
`w : Fin d → α → ℝ` (a row of the block-diagonal rigidity matrix, in transposed
coordinate-major form) to the linear functional on body motions that pairs it against the
motion `m : Motion n α`, coordinate by coordinate. Injective (`blockPairing_injective`),
so it carries a linearly independent family of block rows to a linearly independent family
of row functionals. The standard-basis rigidity row factors through it
(`stdFramework_rigidityRow_eq`). -/
def blockPairing (α : Type*) [Fintype α] (d : ℕ) :
    (Fin d → α → ℝ) →ₗ[ℝ] Module.Dual ℝ (α → EuclideanSpace ℝ (Fin d)) where
  toFun w :=
    { toFun := fun m => ∑ x : α, ∑ c : Fin d, w c x * (m x) c
      map_add' := by
        intro a b
        simp only [Pi.add_apply, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun x _ =>
          Finset.sum_congr rfl fun c _ => by simp only [PiLp.add_apply]; ring
      map_smul' := by
        intro r a
        simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        refine Finset.sum_congr rfl fun c _ => ?_
        simp only [PiLp.smul_apply, smul_eq_mul]; ring }
  map_add' a b := by
    ext m
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, Pi.add_apply,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ =>
      Finset.sum_congr rfl fun c _ => by ring
  map_smul' r a := by
    ext m
    simp only [LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply,
      Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ =>
      Finset.sum_congr rfl fun c _ => by ring

@[simp]
theorem blockPairing_apply {α : Type*} [Fintype α] {d : ℕ} (w : Fin d → α → ℝ)
    (m : α → EuclideanSpace ℝ (Fin d)) :
    blockPairing α d w m = ∑ x : α, ∑ c : Fin d, w c x * (m x) c := rfl

/-- `blockPairing` is injective: evaluating `S w` at the standard-basis motion supported at
`(x, c)` recovers the entry `w c x`, so `S w = 0` forces `w = 0`. -/
theorem blockPairing_injective {α : Type*} [Fintype α] {d : ℕ} :
    Function.Injective (blockPairing α d) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  funext c x
  have h := DFunLike.congr_fun hw (fun x' => if x' = x then EuclideanSpace.single c 1 else 0)
  simp only [blockPairing_apply, LinearMap.zero_apply] at h
  rw [Finset.sum_eq_single x, Finset.sum_eq_single c] at h
  · simpa using h
  · intro c' _ hc'
    simp [hc']
  · simp
  · intro x' _ hx'
    rw [if_neg hx']
    simp
  · simp

/-- **The standard-basis rigidity row is the block-pairing of a block-`single` incidence
row** (up to sign). With `b_e = e_{j(e)}`, the rigidity row `m ↦ rigidityMap D m e` equals
`-(blockPairing (Pi.single (j e) (signedIncMatrix ℝ e)))`: the row lives entirely in block
`j(e)`, where it is `e`'s signed incidence row. This is what feeds the block-diagonal
matrix of `specRow_linearIndependent` into the rank count. -/
theorem stdFramework_rigidityRow_eq [Fintype α] [DecidableEq α] {G : Graph α β}
    [DecidablePred (· ∈ E(G))] (j : E(G) → Fin (bodyBarDim n))
    (D : Graph.orientation G) (e : E(G)) :
    (stdFramework G n j).rigidityRow D e =
      -(blockPairing α (bodyBarDim n)
        (Pi.single (j e) (D.signedIncMatrix ℝ (e : β)))) := by
  refine LinearMap.ext fun m => ?_
  rw [rigidityRow_apply, stdPlacement_rigidityMap_apply, LinearMap.neg_apply,
    blockPairing_apply]
  have he : (e : β) ∈ E(G) := e.2
  -- Only the block `c = j e` survives the inner `Pi.single`, leaving `e`'s signed incidence row.
  rw [D.signedIncMatrix_apply_of_mem he,
    Finset.sum_congr rfl fun x _ => Finset.sum_eq_single (a := j e)
      (fun c _ hc => by rw [Pi.single_eq_of_ne hc]; simp)
      (fun h => absurd (Finset.mem_univ _) h)]
  simp only [Pi.single_eq_same]
  -- Expand the signed incidence row vertex-by-vertex and collapse via the indicator sums.
  simp only [Pi.sub_apply, Function.update_apply, Pi.zero_apply, sub_mul,
    Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, neg_sub]
  rfl

/-- **The standard-basis rigidity rows of a disjoint forest packing are linearly
independent.** If `Fs : Fin (bodyBarDim n) → Set β` is a *disjoint* packing of `G` into
`bodyBarDim n` forests that covers `E(G)`, and `j` is the forest-index map
(`(e : β) ∈ Fs (j e)`), then the rigidity rows of `stdFramework G n j` at any orientation
`D` are linearly independent. This is the reverse direction of `thm:k-frame-union-cycle`
(`Graph.linearIndepOn_kFrameRow_of_isSparse_restrict`) at the single real specialization
`b_e = e_{j(e)}`: each row is the block-`single` incidence row
(`stdFramework_rigidityRow_eq`), and the block-diagonal family is linearly independent
over `ℝ` by `specRow_linearIndependent` (`Graph.orientation.isAcyclicSet_linearIndepOn`),
reindexed along the disjoint-cover bijection `Set.unionEqSigmaOfDisjoint`. -/
theorem stdFramework_rigidityRow_linearIndependent [Finite α] [Finite β] {G : Graph α β}
    {Fs : Fin (bodyBarDim n) → Set β} (hcover : ⋃ i, Fs i = E(G))
    (hdisj : Pairwise (Function.onFun Disjoint Fs)) (hacyc : ∀ i, G.IsAcyclicSet (Fs i))
    (j : E(G) → Fin (bodyBarDim n)) (hj : ∀ e : E(G), (e : β) ∈ Fs (j e))
    (D : Graph.orientation G) :
    LinearIndependent ℝ ((stdFramework G n j).rigidityRow D) := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  -- The disjoint cover gives `↥E(G) ≃ Σ i, Fs i`; the index `(eqv e).1` is the forest of `e`.
  let eqv : E(G) ≃ Σ i : Fin (bodyBarDim n), (Fs i : Set β) :=
    (Equiv.setCongr hcover.symm).trans (Set.unionEqSigmaOfDisjoint hdisj)
  have hsnd : ∀ e : E(G), ((eqv e).2 : β) = (e : β) := fun e => by
    simp only [eqv, Equiv.trans_apply, Set.coe_snd_unionEqSigmaOfDisjoint, Equiv.setCongr_apply]
  -- `j e = (eqv e).1`: both forests contain `e`, and the packing is disjoint.
  have hjeq : ∀ e : E(G), j e = (eqv e).1 := fun e => by
    by_contra h
    have h1 : (e : β) ∈ Fs (eqv e).1 := by rw [← hsnd e]; exact (eqv e).2.2
    exact (hdisj h).ne_of_mem (hj e) h1 rfl
  -- The block-`single` incidence rows are LI over ℝ (`specRow`), reindexed along `eqv`.
  have hbase := specRow_linearIndependent (G := G) (D := D) ℝ Fs hacyc
  have hvec : LinearIndependent ℝ
      (fun e : E(G) => Pi.single (j e) (D.signedIncMatrix ℝ (e : β)) :
        E(G) → Fin (bodyBarDim n) → α → ℝ) := by
    have heq : (fun e : E(G) => Pi.single (j e) (D.signedIncMatrix ℝ (e : β)) :
        E(G) → Fin (bodyBarDim n) → α → ℝ) =
        (fun ji : Σ i : Fin (bodyBarDim n), (Fs i : Set β) =>
          (Pi.single ji.1 (D.signedIncMatrix ℝ (ji.2 : β)) : Fin (bodyBarDim n) → α → ℝ))
            ∘ eqv := by
      funext e
      simp only [Function.comp_apply, hjeq e, hsnd e]
    rw [heq]
    exact hbase.comp eqv eqv.injective
  -- Each row is `-(blockPairing (block-single row))`; `blockPairing` injective, negation a unit.
  have hrow : (stdFramework G n j).rigidityRow D =
      fun e => -(blockPairing α (bodyBarDim n)
        (Pi.single (j e) (D.signedIncMatrix ℝ (e : β)))) :=
    funext fun e => stdFramework_rigidityRow_eq j D e
  rw [hrow]
  exact (hvec.map' (blockPairing α (bodyBarDim n))
    (LinearMap.ker_eq_bot.mpr blockPairing_injective)).neg

/-- **Block-diagonal rank count for the standard-basis witness** (the independent-form half
of `thm:tay-witness`). For a disjoint forest packing `Fs` of `G` into `d = bodyBarDim n`
forests covering `E(G)`, with forest-index map `j`, the body-bar rigidity map of the
standard-basis framework `stdFramework G n j` at any orientation `D` has rank exactly
`|E(G)|`, so the framework is independent. The rank equals the dimension of the span of the
linearly independent rigidity rows (`stdFramework_rigidityRow_linearIndependent`), via the
row-rank-equals-column-rank identity `span_range_rigidityRow` +
`LinearMap.finrank_range_dualMap_eq_finrank_range`. -/
theorem stdFramework_finrank_range [Finite α] [Finite β] {G : Graph α β}
    {Fs : Fin (bodyBarDim n) → Set β} (hcover : ⋃ i, Fs i = E(G))
    (hdisj : Pairwise (Function.onFun Disjoint Fs)) (hacyc : ∀ i, G.IsAcyclicSet (Fs i))
    (j : E(G) → Fin (bodyBarDim n)) (hj : ∀ e : E(G), (e : β) ∈ Fs (j e))
    (D : Graph.orientation G) :
    Module.finrank ℝ (LinearMap.range ((stdFramework G n j).rigidityMap D)) = E(G).ncard := by
  haveI : Fintype E(G) := Fintype.ofFinite _
  haveI : Fintype E((stdFramework G n j).graph) := Fintype.ofFinite _
  have hLI := stdFramework_rigidityRow_linearIndependent hcover hdisj hacyc j hj D
  -- finrank (range R) = finrank (range R.dualMap) = finrank (span rows) = #E(G) = |E(G)|.
  rw [← LinearMap.finrank_range_dualMap_eq_finrank_range,
    ← span_range_rigidityRow (stdFramework G n j) D, finrank_span_eq_card hLI,
    ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  exact Fintype.card_congr (Equiv.refl _)

/-! ### Block-diagonal rank upper bound (the converse infrastructure)

The body-bar analogue of `rigidityMap_finrank_range_le_of_affinelySpanning`
(`RigidityMatroid.lean`): a rank *upper* bound `finrank (span (rows on E')) ≤ d · r(E')`
on the rigidity rows of an *arbitrary* body-bar framework restricted to a bar set `E'`,
`d = bodyBarDim n` and `r(E')` the cycle-matroid rank. Unlike the witness placement,
the placement here is unconstrained: the row for a bar `e` is the inner product
`m ↦ ⟪b_e, m u − m v⟫`, a real-coefficient combination across the `d` coordinate blocks of
`e`'s signed incidence row, so it factors through `blockPairing` exactly as in the
witness case — `rigidityRow_eq` — but with the block-`single` of `stdFramework_rigidityRow_eq`
replaced by the full block vector `fun c ↦ (b_e)_c • signedIncMatrix e`.

The bound is the real specialization of Whiteley §2.1's forward rank count
(`Graph.forest_count_of_linearIndepOn_kFrameRow`): each pushed-back row lies in the
block-diagonal product subspace whose `ℝ`-dimension is `d · r(E')` (the real analogue of
`Graph.finrank_blockPiSpanOn`, assembled from the *field-generic* helpers
`Graph.finrank_constPiSpan` + `Graph.finrank_span_signedIncMatrix_eq_cycleMatroid_rk`). -/

open Submodule in
/-- **General-placement rigidity-row identity.** For *any* body-bar framework `F` with
placement `b = F.placement`, the rigidity row at `e` is the block-pairing of the block
vector `fun c ↦ (b_e)_c • signedIncMatrix e` (up to sign):
`F.rigidityRow D e = -(blockPairing α d (fun c ↦ F.placement e c • D.signedIncMatrix ℝ e))`.
The arbitrary-placement generalization of `stdFramework_rigidityRow_eq` (which is this with
`b_e = e_{j(e)}`, so the block vector is `Pi.single (j e) (signedIncMatrix e)`); the row for
`e` is the real-coefficient combination `∑_c (b_e)_c · (block-`c` incidence row of e)`,
mirroring the indeterminate `kFrameRow = ∑_j X_{(e,j)} • (block-`j` incidence row)`. -/
theorem rigidityRow_eq [Fintype α] [DecidableEq α] {F : BodyBarFramework n α β}
    [DecidablePred (· ∈ E(F.graph))] (D : Graph.orientation F.graph) (e : E(F.graph)) :
    F.rigidityRow D e =
      -(blockPairing α (bodyBarDim n)
        (fun c => F.placement e c • D.signedIncMatrix ℝ (e : β))) := by
  refine LinearMap.ext fun m => ?_
  rw [rigidityRow_apply, rigidityMap_apply, LinearMap.neg_apply, blockPairing_apply,
    PiLp.inner_apply]
  have he : (e : β) ∈ E(F.graph) := e.2
  -- Expand the inner product coordinatewise; over ℝ each component pairing is `b·w`.
  simp only [RCLike.inner_apply, conj_trivial, PiLp.sub_apply]
  -- Swap the order of summation and push the negation into the coordinate sum, then expand
  -- the signed incidence row vertex-by-vertex and collapse via the indicator sums.
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [D.signedIncMatrix_apply_of_mem he]
  simp only [Pi.smul_apply, Pi.sub_apply, Function.update_apply, Pi.zero_apply, smul_eq_mul]
  -- Each summand `(b_e c * (ite_v − ite_u)) * m x c` is `if x = v then … else if x = u …`;
  -- collapse the indicator sums to the two endpoint contributions.
  rw [show (∑ x, (F.placement e).ofLp c
        * ((if x = (D.dInc ⟨↑e, he⟩).2 then (1:ℝ) else 0)
          - if x = (D.dInc ⟨↑e, he⟩).1 then (1:ℝ) else 0) * (m x).ofLp c)
      = (F.placement e).ofLp c * (m (D.dInc e).2).ofLp c
        - (F.placement e).ofLp c * (m (D.dInc e).1).ofLp c from by
      simp only [mul_assoc, ← Finset.mul_sum, mul_sub, sub_mul, ite_mul, one_mul, zero_mul,
        Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]]
  ring

/-- **The signed incidence-row span is orientation-independent.** Over any commutative ring `𝔽`,
the span of the signed incidence rows on a bar set `E'` is the same submodule for any two
orientations `D, D'` of `G`: for each edge `e`, the two orientations' `dInc` pairs agree or swap
(`Graph.IsLink.eq_and_eq_or_eq_and_eq`), so `signedIncMatrix D' e = ± signedIncMatrix D e`, and a
generator and its negative span the same line. Lets `finrank_realBlockPiSpanOn` reuse the
`G.orientation_nonempty.some`-pinned `finrank_span_signedIncMatrix_eq_cycleMatroid_rk` at an
arbitrary `D`. -/
theorem span_signedIncMatrix_image_eq_of_orientation {𝔽 : Type*} [CommRing 𝔽] {G : Graph α β}
    [DecidablePred (· ∈ E(G))] [DecidableEq α] (D D' : Graph.orientation G) (E' : Set β) :
    Submodule.span 𝔽 ((D.signedIncMatrix 𝔽) '' E') =
      Submodule.span 𝔽 ((D'.signedIncMatrix 𝔽) '' E') := by
  -- Each generator on one side is `±` a generator on the other; `span` swallows the sign.
  have key : ∀ (E₁ E₂ : Graph.orientation G) (f : β), f ∈ E' →
      E₁.signedIncMatrix 𝔽 f ∈ Submodule.span 𝔽 ((E₂.signedIncMatrix 𝔽) '' E') := by
    intro E₁ E₂ f hf
    by_cases hfE : f ∈ E(G)
    · have hlink := E₁.isLink_of_dInc ⟨f, hfE⟩
      have hlink' := E₂.isLink_of_dInc ⟨f, hfE⟩
      have hmem : E₂.signedIncMatrix 𝔽 f ∈ Submodule.span 𝔽 ((E₂.signedIncMatrix 𝔽) '' E') :=
        Submodule.subset_span ⟨f, hf, rfl⟩
      rw [E₁.signedIncMatrix_apply_of_mem hfE]
      rw [E₂.signedIncMatrix_apply_of_mem hfE] at hmem
      rcases hlink.eq_and_eq_or_eq_and_eq hlink' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact hmem
      · rw [h1, h2]
        have hneg : (Function.update (0 : α → 𝔽) (E₂.dInc ⟨f, hfE⟩).1 1
            - Function.update (0 : α → 𝔽) (E₂.dInc ⟨f, hfE⟩).2 1)
            = -(Function.update (0 : α → 𝔽) (E₂.dInc ⟨f, hfE⟩).2 1
              - Function.update (0 : α → 𝔽) (E₂.dInc ⟨f, hfE⟩).1 1) := by ring
        rw [hneg]; exact Submodule.neg_mem _ hmem
    · rw [E₁.signedIncMatrix_apply_of_not_mem hfE]; exact Submodule.zero_mem _
  exact Submodule.span_eq_span
    (Set.image_subset_iff.mpr fun f hf => key D D' f hf)
    (Set.image_subset_iff.mpr fun f hf => key D' D f hf)

open Submodule in
/-- **Real block-diagonal product subspace dimension** = `d · r(E')`. The `ℝ`-dimension of the
`Fin d`-fold product subspace whose each block is the `ℝ`-span of the signed incidence rows on a
bar set `E'` is `d` times the cycle-matroid rank `r(E')`. The real analogue of
`Graph.finrank_blockPiSpanOn`, assembled from the *field-generic* `Graph.finrank_constPiSpan` and
`Graph.finrank_span_signedIncMatrix_eq_cycleMatroid_rk` (both stated over an arbitrary field, here
`ℝ`); the chosen orientation is replaced by `G.orientation_nonempty.some` via
`span_signedIncMatrix_image_eq_of_orientation`. This caps the row span in the converse rank bound
`finrank_rigidityRow_span_le`. -/
theorem finrank_realBlockPiSpanOn [Finite α] [Finite β] {G : Graph α β}
    (D : Graph.orientation G) (E' : Set β) :
    letI : DecidableEq α := Classical.decEq α
    letI : DecidablePred (· ∈ E(G)) := Classical.decPred _
    Module.finrank ℝ
        (Submodule.pi Set.univ
          (fun _ : Fin (bodyBarDim n) => span ℝ ((D.signedIncMatrix ℝ) '' E')) :
          Submodule ℝ (Fin (bodyBarDim n) → α → ℝ))
      = bodyBarDim n * G.cycleMatroid.rk E' := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  haveI : Module.Finite ℝ (span ℝ ((D.signedIncMatrix ℝ) '' E')) :=
    Module.Finite.span_of_finite _ ((Set.toFinite E').image _)
  rw [Graph.finrank_constPiSpan]
  congr 1
  -- The per-block incidence-row span has `ℝ`-dimension `r(E')`; replace `D` by the pinned
  -- orientation (the span — and hence its dimension — is orientation-independent).
  rw [span_signedIncMatrix_image_eq_of_orientation D (G.orientation_nonempty.some) E',
    Graph.finrank_span_signedIncMatrix_eq_cycleMatroid_rk (G := G) ℝ E']

open Submodule in
/-- **Block-diagonal rank upper bound on a bar set** (the converse rank bound). For *any* body-bar
framework `F` on `G = F.graph` and any bar set `E' ⊆ E(G)`, the `ℝ`-dimension of the span of the
rigidity rows on `E'` is at most `d · r(E')`, `d = bodyBarDim n` and `r` the cycle-matroid rank.
The body-bar analogue of the rank-upper-bound half of Phase 6's
`rigidityMap_finrank_range_le_of_affinelySpanning`, proved at the real specialization rather than
through trivial motions: each row factors through `blockPairing` (`rigidityRow_eq`) as the
block vector `fun c ↦ (b_e)_c • signedIncMatrix e`, which lies in the real block-diagonal product
subspace of dimension `d · r(E')` (`finrank_realBlockPiSpanOn`). -/
theorem finrank_rigidityRow_span_le [Finite α] [Finite β] (F : BodyBarFramework n α β)
    (D : Graph.orientation F.graph) (E' : Set E(F.graph)) :
    Module.finrank ℝ (span ℝ (F.rigidityRow D '' E')) ≤ bodyBarDim n * F.graph.cycleMatroid.rk
      (Subtype.val '' E') := by
  haveI : Fintype α := Fintype.ofFinite α
  letI : DecidableEq α := Classical.decEq α
  letI : DecidablePred (· ∈ E(F.graph)) := Classical.decPred _
  set W : Submodule ℝ (Fin (bodyBarDim n) → α → ℝ) :=
    Submodule.pi Set.univ
      (fun _ : Fin (bodyBarDim n) => span ℝ ((D.signedIncMatrix ℝ) '' (Subtype.val '' E')))
    with hW
  haveI : Module.Finite ℝ (span ℝ ((D.signedIncMatrix ℝ) '' (Subtype.val '' E'))) :=
    Module.Finite.span_of_finite _ ((Set.toFinite _).image _)
  haveI : Module.Finite ℝ W := by rw [hW]; exact inferInstance
  -- The pushed-back row vectors `w_e = fun c ↦ (b_e)_c • signedIncMatrix e` all lie in `W`.
  have hmem : ∀ e : E(F.graph), e ∈ E' →
      (fun c => F.placement e c • D.signedIncMatrix ℝ (e : β)) ∈ W := by
    intro e he
    rw [hW, Submodule.mem_pi]
    intro c _
    exact Submodule.smul_mem _ _ (subset_span ⟨(e : β), ⟨e, he, rfl⟩, rfl⟩)
  -- Bound `finrank (span rows) ≤ finrank (blockPairing '' W) ≤ finrank W = d · r(E')`.
  have himg : span ℝ (F.rigidityRow D '' E') ≤
      Submodule.map (blockPairing α (bodyBarDim n)) W := by
    rw [span_le]
    rintro _ ⟨e, he, rfl⟩
    rw [rigidityRow_eq]
    exact ⟨-(fun c => F.placement e c • D.signedIncMatrix ℝ (e : β)),
      Submodule.neg_mem _ (hmem e he), by simp⟩
  calc Module.finrank ℝ (span ℝ (F.rigidityRow D '' E'))
      ≤ Module.finrank ℝ (Submodule.map (blockPairing α (bodyBarDim n)) W) :=
        Submodule.finrank_mono himg
    _ ≤ Module.finrank ℝ W := Submodule.finrank_map_le _ _
    _ = bodyBarDim n * F.graph.cycleMatroid.rk (Subtype.val '' E') := by
        rw [hW]; exact finrank_realBlockPiSpanOn D (Subtype.val '' E')

/-! ### Tay's theorem (existence-of-realization form)

The chapter target, `thm:tay-witness`, in its existence-of-realization direction
(`⟸`): a `(d, d)`-sparse multigraph carries an *independent* body-bar framework in
`ℝⁿ`, and a `(d, d)`-tight connected multigraph carries an *isostatic* (independent
and infinitesimally rigid) one. Both are witnessed by the standard-basis framework
`stdFramework G n j` on a tree-packing partition (`thm:tutte-nash-williams`); the
content is `stdFramework_finrank_range` (rank `= |E(G)|`).

The converse direction (an independent framework forces `(d, d)`-sparsity) is the
Lovász–Yemini-style rank-upper-bound argument (`finrank_rigidityRow_span_le`), the body-bar
analogue of Phase 6's `isSparse_of_edgeSetRowIndependent_dim_two`. -/

/-- **Tay's theorem, independent existence direction** (`thm:tay-witness` `⟸`). For
`d = bodyBarDim n`, a `(d, d)`-sparse multigraph `G` carries an independent body-bar
framework in `ℝⁿ`: the standard-basis framework `stdFramework G n j` on a tree-packing
partition of `G` (`thm:tutte-nash-williams`) is independent (`IsIndependent`, rank
`= |E(G)|`) at any orientation.

By `tutte_nash_williams`, `(d, d)`-sparsity gives a disjoint acyclic cover `Fs` of
`E(G)` by `d` forests; choosing the forest index `j e` of each bar `e` and applying
`stdFramework_finrank_range` makes the rigidity matrix block-diagonal with full-rank
forest-incidence blocks, so the framework is independent. -/
theorem exists_isIndependent_of_isSparse [Finite α] [Finite β] {G : Graph α β}
    (hsparse : G.IsSparse (bodyBarDim n) (bodyBarDim n)) :
    ∃ (F : BodyBarFramework n α β) (_ : F.graph = G) (D : Graph.orientation F.graph),
      F.IsIndependent D := by
  obtain ⟨Fs, hcover, hdisj, hacyc⟩ := tutte_nash_williams.mpr hsparse
  -- Choose the forest index `j e` of each bar from the cover `⋃ i, Fs i = E(G)`.
  have hmem : ∀ e : E(G), ∃ i, (e : β) ∈ Fs i := fun e => by
    have he : (e : β) ∈ ⋃ i, Fs i := by rw [hcover]; exact e.2
    simpa using he
  choose j hj using hmem
  refine ⟨stdFramework G n j, rfl, Classical.choice Graph.orientation_nonempty, ?_⟩
  exact stdFramework_finrank_range hcover hdisj hacyc j hj _

/-- **Tay's theorem, isostatic existence direction** (`thm:tay-witness` `⟸`, count
form). For `d = bodyBarDim n`, a connected `(d, d)`-tight multigraph `G` carries an
*isostatic* body-bar framework in `ℝⁿ` — one that is both independent (`IsIndependent`)
and infinitesimally rigid (`IsInfinitesimallyRigid`), the count `|E| = d(b - 1)` of
Tay 1984. The witness is again the standard-basis framework on the tree-packing (here,
by `cor:k-spanning-trees`, a *spanning-tree* packing).

Independence is `exists_isIndependent_of_isSparse` applied to `htight.isSparse`; the
infinitesimal-rigidity count `rank + d = d·b` then follows from independence (`rank =
|E|`) and tightness (`|E| + d = d·|V|`), since `b = |V(G)|`. -/
theorem exists_isIsostatic_of_isTight [Finite α] [Finite β] {G : Graph α β}
    (htight : G.IsTight (bodyBarDim n) (bodyBarDim n)) :
    ∃ (F : BodyBarFramework n α β) (_ : F.graph = G) (D : Graph.orientation F.graph),
      F.IsIndependent D ∧ F.IsInfinitesimallyRigid D := by
  obtain ⟨F, hF, D, hindep⟩ := exists_isIndependent_of_isSparse htight.isSparse
  refine ⟨F, hF, D, hindep, ?_⟩
  -- `IsInfinitesimallyRigid`: `rank + d = d·b`. Independence gives `rank = |E(F.graph)|`;
  -- transport across `hF : F.graph = G` and use tightness `|E(G)| + d = d·|V(G)|`.
  change Module.finrank ℝ (LinearMap.range (F.rigidityMap D)) + bodyBarDim n
    = bodyBarDim n * F.graph.vertexSet.ncard
  rw [hindep, hF]
  exact htight.2

/-- **Independence ⟹ the full rigidity-row family is linearly independent.** If `F` is independent
at `D` (`rank (rigidityMap D) = |E(F.graph)|`), then the rigidity rows `rigidityRow D` form a
linearly independent family in `Module.Dual ℝ (Motion n α)`. The rows span `range dualMap`, whose
`ℝ`-dimension equals `rank (rigidityMap D)` (`span_range_rigidityRow` +
`finrank_range_dualMap_eq_finrank_range`); independence makes this `|E(F.graph)| = #rows`, so the
spanning family of `#rows` rows is a basis, hence linearly independent. -/
theorem rigidityRow_linearIndependent [Finite α] [Finite β] {F : BodyBarFramework n α β}
    {D : Graph.orientation F.graph} (hindep : F.IsIndependent D) :
    LinearIndependent ℝ (F.rigidityRow D) := by
  haveI : Fintype E(F.graph) := Fintype.ofFinite _
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, span_range_rigidityRow,
    LinearMap.finrank_range_dualMap_eq_finrank_range, hindep, ← Nat.card_coe_set_eq,
    Nat.card_eq_fintype_card]

/-- **Tay's theorem, sparsity (converse) direction** (`thm:tay-witness` `⟹`). For `d = bodyBarDim
n`, an independent body-bar framework `F` on `G = F.graph` forces `G` to be `(d, d)`-sparse: every
non-empty bar set `E' ⊆ E(G)` spanning `V'` satisfies `|E'| + d ≤ d · |V'|`.

The body-bar analogue of Phase 6's `isSparse_of_edgeSetRowIndependent_dim_two`. Independence makes
the rigidity rows linearly independent (`rigidityRow_linearIndependent`), so on each `E'` the
`|E'|` rows are linearly independent and span an `|E'|`-dimensional subspace; the block-diagonal
rank upper bound `finrank_rigidityRow_span_le` caps this by `d · r(E')`, and the cycle-matroid rank
bound `cycleMatroid_rk_add_one_le_spanningVerts_ncard` gives `r(E') + 1 ≤ |V'|`, so
`|E'| ≤ d · r(E') ≤ d · (|V'| − 1)`, i.e. `|E'| + d ≤ d · |V'|`. -/
theorem isSparse_of_isIndependent [Finite α] [Finite β] {F : BodyBarFramework n α β}
    {D : Graph.orientation F.graph} (hindep : F.IsIndependent D) :
    F.graph.IsSparse (bodyBarDim n) (bodyBarDim n) := by
  haveI : Fintype E(F.graph) := Fintype.ofFinite _
  have hLI := rigidityRow_linearIndependent hindep
  intro E' hE'G hne
  -- Pull `E' : Set β` back to `E'ₛ : Set ↥E(F.graph)`; `Subtype.val '' E'ₛ = E'` since `E' ⊆ E(G)`.
  set E'ₛ : Set E(F.graph) := Subtype.val ⁻¹' E' with hE'ₛ
  haveI : Fintype E'ₛ := Fintype.ofFinite _
  have himg : Subtype.val '' E'ₛ = E' := by
    rw [hE'ₛ, Subtype.image_preimage_coe]
    exact Set.inter_eq_right.mpr hE'G
  have hcard : (E'ₛ : Set E(F.graph)).ncard = E'.ncard := by
    rw [← himg, Set.ncard_image_of_injective _ Subtype.val_injective]
  -- The `|E'|` rigidity rows on `E'ₛ` are linearly independent, so their span has dim `|E'|`.
  have hLIon : LinearIndependent ℝ (fun e : E'ₛ => F.rigidityRow D e.val) :=
    hLI.comp _ Subtype.val_injective
  have hfin_eq : Module.finrank ℝ (Submodule.span ℝ (F.rigidityRow D '' E'ₛ)) = E'.ncard := by
    rw [Set.image_eq_range, finrank_span_eq_card hLIon, ← hcard, Set.ncard_eq_toFinset_card',
      Set.toFinset_card]
  -- Block-diagonal rank upper bound `|E'| ≤ d · r(E')` + cycle-matroid bound `r(E') + 1 ≤ |V'|`.
  have hle1 : E'.ncard ≤ bodyBarDim n * F.graph.cycleMatroid.rk E' := by
    have h := finrank_rigidityRow_span_le F D E'ₛ
    rw [hfin_eq, himg] at h
    exact h
  have hle2 : F.graph.cycleMatroid.rk E' + 1 ≤ (F.graph.spanningVerts E').ncard :=
    cycleMatroid_rk_add_one_le_spanningVerts_ncard hE'G hne
  calc E'.ncard + bodyBarDim n
      ≤ bodyBarDim n * F.graph.cycleMatroid.rk E' + bodyBarDim n := by omega
    _ = bodyBarDim n * (F.graph.cycleMatroid.rk E' + 1) := by ring
    _ ≤ bodyBarDim n * (F.graph.spanningVerts E').ncard := Nat.mul_le_mul_left _ hle2

/-- **Tay's theorem, existence-of-realization form** (`thm:tay-witness`; Whiteley 1988 Theorem 8,
Tay 1984). For `n` and `d = bodyBarDim n = n(n+1)/2`, a multigraph `G` carries an *independent*
body-bar framework in `ℝⁿ` **iff** `G` is `(d, d)`-sparse — equivalently (Phase 13,
`tutte_nash_williams`) the edge-disjoint union of `d` forests. It carries an *isostatic*
(independent + infinitesimally rigid) body-bar framework iff `G` is `(d, d)`-tight — equivalently
(`cor:k-spanning-trees`) the union of `d` spanning trees, the count `|E| = d(b − 1)` of Tay 1984.

The (`⟸`) existence directions are `exists_isIndependent_of_isSparse` /
`exists_isIsostatic_of_isTight` (the standard-basis witness on a tree packing); the (`⟹`)
converses are `isSparse_of_isIndependent` (the block-diagonal rank upper bound) and, for the
isostatic count, the independence-plus-rigidity arithmetic `|E| + d = d·|V|`. -/
theorem tay_witness [Finite α] [Finite β] (G : Graph α β) :
    ((∃ (F : BodyBarFramework n α β) (_ : F.graph = G) (D : Graph.orientation F.graph),
        F.IsIndependent D) ↔ G.IsSparse (bodyBarDim n) (bodyBarDim n)) ∧
      ((∃ (F : BodyBarFramework n α β) (_ : F.graph = G) (D : Graph.orientation F.graph),
        F.IsIndependent D ∧ F.IsInfinitesimallyRigid D) ↔
          G.IsTight (bodyBarDim n) (bodyBarDim n)) := by
  refine ⟨⟨?_, exists_isIndependent_of_isSparse⟩, ⟨?_, exists_isIsostatic_of_isTight⟩⟩
  · -- Independent ⟹ `(d, d)`-sparse: the block-diagonal rank upper bound.
    rintro ⟨F, rfl, D, hindep⟩
    exact isSparse_of_isIndependent hindep
  · -- Isostatic ⟹ `(d, d)`-tight: sparse from independence + the global count from rigidity.
    rintro ⟨F, rfl, D, hindep, hrigid⟩
    refine ⟨isSparse_of_isIndependent hindep, ?_⟩
    -- `|E| + d = d·|V|`: independence (`rank = |E|`) substituted into rigidity (`rank + d = d·b`).
    have h : Module.finrank ℝ (LinearMap.range (F.rigidityMap D)) + bodyBarDim n
        = bodyBarDim n * F.graph.vertexSet.ncard := hrigid
    rwa [hindep] at h

end BodyBarFramework

end Graph
