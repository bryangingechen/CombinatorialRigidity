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

## Current state (Phase 15, in progress)

This file ships the witness placement, the bar-row reduction, the block-diagonal
rank count (`stdFramework_finrank_range`), and the **existence (⟸) direction** of
Tay's theorem (`prop:tay-witness-exists`): `exists_isIndependent_of_isSparse` and
`exists_isIsostatic_of_isTight`. The converse (⟹: an independent framework forces
`(d, d)`-sparsity) — and hence the full `thm:tay-witness` iff — is the next
sub-step; see `ROADMAP.md` §15, `notes/Phase15.md`, and the §`sec:body-bar-tay`
subsection of `blueprint/src/chapter/body-bar.tex`.
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

variable {α β : Type*}

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
noncomputable def blockPairing (α : Type*) [Fintype α] (d : ℕ) :
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
  classical
  haveI : Fintype E(G) := Fintype.ofFinite _
  haveI : Fintype E((stdFramework G n j).graph) := Fintype.ofFinite _
  have hLI := stdFramework_rigidityRow_linearIndependent hcover hdisj hacyc j hj D
  -- finrank (range R) = finrank (range R.dualMap) = finrank (span rows) = #E(G) = |E(G)|.
  rw [← LinearMap.finrank_range_dualMap_eq_finrank_range,
    ← span_range_rigidityRow (stdFramework G n j) D, finrank_span_eq_card hLI,
    ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  exact Fintype.card_congr (Equiv.refl _)

/-! ### Tay's theorem (existence-of-realization form)

The chapter target, `thm:tay-witness`, in its existence-of-realization direction
(`⟸`): a `(d, d)`-sparse multigraph carries an *independent* body-bar framework in
`ℝⁿ`, and a `(d, d)`-tight connected multigraph carries an *isostatic* (independent
and infinitesimally rigid) one. Both are witnessed by the standard-basis framework
`stdFramework G n j` on a tree-packing partition (`thm:tutte-nash-williams`); the
content is `stdFramework_finrank_range` (rank `= |E(G)|`).

The converse direction (an independent framework forces `(d, d)`-sparsity) is the
Lovász–Yemini-style rank-upper-bound argument — the body-bar analogue of Phase 6's
`isSparse_of_edgeSetRowIndependent_dim_two` — and is deferred; see `notes/Phase15.md`. -/

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
  classical
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

end BodyBarFramework

end Graph
