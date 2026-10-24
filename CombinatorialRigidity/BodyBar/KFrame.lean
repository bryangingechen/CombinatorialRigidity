/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.BodyBar.TreePacking
public import CombinatorialRigidity.Mathlib.LinearAlgebra.Matrix.Rank
public import Matroid.Representation.Map
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# The generic `k`-frame matroid (`def:k-frame-matroid`)

Whiteley's general `k`-frame (Whiteley 1988, *The union of matroids and the rigidity of
frameworks*, SIAM J. Disc. Math. **1**, Definition 2.2): for a multigraph `G : Graph α β`, the
matrix with `k · |V|` columns whose row for a bar `e` carries indeterminate coefficients across
`k` vertex blocks, each block holding a copy of the signed incidence pattern of `e`. Its
**`k`-frame matroid** `F(G, X)` is the linear matroid of the rows (via `Matroid.ofFun`, the
`apnelson1/Matroid` constructor `LinearRigidityMatroid.lean` uses for the planar case), and
Whiteley's Theorem 1 identifies it with the union of `k` copies of the cycle matroid:
`F(G, X) = (⋃ⱼ G.cycleMatroid) ↾ E(G)` (`thm:k-frame-union-cycle`,
`kFrameMatroid_eq_unionPow_cycleMatroid`). The blueprint presents the file in
`sec:body-bar-k-frame`.

## Coefficient encoding

The genericity is realized over **true indeterminates**, not a real placement (cf.
`SimpleGraph.linearRigidityMatroid`, which is parametrized by a placement
`p : Framework V d`): the coefficient field is

  `K := FractionRing (MvPolynomial (β × Fin k) ℚ)`,

with one indeterminate `X (e, j)` per (bar, block) pair. The row for bar `e` in block
`j` is `X (e, j) • D.signedIncMatrix K e` — the indeterminate scaling of the signed
incidence row of `e` for a chosen orientation `D` of `G` (the same row vector
`Graph.cycleMatroidRep` represents `G.cycleMatroid` by). The orientation is picked by
`G.orientation_nonempty.some`, matching `cycleMatroidRep`; the choice is harmless for
the generic matroid (orientations differ only by a per-row sign). The row vector lives
in `Fin k → α → K`, the `k`-fold copy of the incidence-row space `α → K` —
`k · |V|`-dimensional, the blueprint's "`k` vertex blocks".

The two directions of the identification: independent rows on a bar set `E'` give the count
`|Y| ≤ k · r(Y)` on every `Y ⊆ E'` by a dimension bound (`forest_count_of_linearIndepOn_kFrameRow`;
Whiteley proves this direction from a nonzero minor instead), and a `(k, k)`-sparse `E'` has
independent rows by Whiteley's specialization (his proof of Theorem 1, p. 239): on a disjoint
forest packing, setting `X (e, j)` to `1` when `e` lies in the `j`-th forest and to `0`
otherwise gives a block-diagonal matrix of forest incidence rows
(`linearIndepOn_kFrameRow_of_isSparse_restrict`).
-/

@[expose] public section

namespace Graph

open Matroid

variable {α β : Type*}

/-- The coefficient field of the generic `k`-frame matroid: the field of fractions of
the multivariate polynomial ring `MvPolynomial (β × Fin k) ℚ`, carrying one indeterminate
`MvPolynomial.X (e, j)` per (bar, block) pair `(e, j) : β × Fin k`. A field (the
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
(`def:k-frame-matroid`; Whiteley 1988, Definition 2.2): the linear matroid on the bar type
`β`, with ground set `E(G)`, of the `k`-frame row function over the indeterminate
coefficient field `KFrameField β k`. Built via `Matroid.ofFun`, like the planar
`SimpleGraph.linearRigidityMatroid`. The orientation is picked by
`G.orientation_nonempty.some`, matching `Graph.cycleMatroidRep`.

The identification `kFrameMatroid G k = (Matroid.Union (fun _ : Fin k ↦ G.cycleMatroid)) ↾ E(G)`
is `kFrameMatroid_eq_unionPow_cycleMatroid` (`thm:k-frame-union-cycle`). -/
noncomputable def kFrameMatroid (G : Graph α β) (k : ℕ) : Matroid β :=
  Matroid.ofFun (KFrameField β k) E(G) (kFrameRow k G.orientation_nonempty.some)

@[simp]
theorem kFrameMatroid_ground (G : Graph α β) (k : ℕ) :
    (G.kFrameMatroid k).E = E(G) := by
  simp only [kFrameMatroid, Matroid.ofFun_ground_eq]

section Forward

open Submodule

variable {G : Graph α β} {k : ℕ} {D : Graph.orientation G}

/-- **A product subspace as a product** (`lem:k-frame-pi-finrank`): the `Fin n`-fold constant
product subspace `Submodule.pi univ (fun _ ↦ W)` is linearly equivalent to the plain product
`Fin n → ↥W` of the block submodule with itself. The forward map projects each block; the
inverse re-bundles. It gives the dimension count `finrank_constPiSpan`. -/
def constPiSpanEquiv {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (n : ℕ) (W : Submodule R M) :
    (Submodule.pi Set.univ (fun _ : Fin n ↦ W) : Submodule R (Fin n → M)) ≃ₗ[R] (Fin n → W) where
  toFun f i := ⟨f.1 i, f.2 i (Set.mem_univ i)⟩
  invFun g := ⟨fun i ↦ (g i : M), fun i _ ↦ (g i).2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The dimension of a product subspace** (`lem:k-frame-pi-finrank`): the dimension of the
constant `Fin n`-fold product subspace over a division ring `R` is `n` times the dimension of
the block submodule `W`. Piece (1) of the rank count of `lem:k-frame-nonzero-monomial-forest`:
applied with `W` the `K`-span of the signed incidence rows of a bar set, it turns the
`blockPiSpanOn` upper bound into `k · (incidence-span dimension)`. -/
theorem finrank_constPiSpan {R M : Type*} [DivisionRing R] [AddCommGroup M] [Module R M]
    (n : ℕ) (W : Submodule R M) [Module.Finite R W] :
    Module.finrank R (Submodule.pi Set.univ (fun _ : Fin n ↦ W) : Submodule R (Fin n → M))
      = n * Module.finrank R W := by
  simp [(constPiSpanEquiv n W).finrank_eq, Module.finrank_pi_fintype R]

/-- **The product of incidence spans on a bar set** (`lem:k-frame-span-le-pi`'s `A_Y^k`): the
`Fin k`-fold product subspace whose `j`-th block is the `KFrameField β k`-span of the
signed incidence rows indexed by a bar set `Y`. For `e ∈ Y` the `k`-frame row `kFrameRow k D e`
lies in this subspace (`kFrameRow_mem_blockPiSpanOn`), so the span of the `k`-frame rows on `Y`
is contained in it (`span_kFrameRowOn_le_blockPiSpanOn`); its `K`-dimension is `k` times the
dimension of the `Y`-incidence-row span, i.e. `k · r_{cycleMatroid}(Y)` — the per-`Y` upper bound
in the rank count of `lem:k-frame-nonzero-monomial-forest`. -/
noncomputable def blockPiSpanOn (G : Graph α β) (k : ℕ) (D : Graph.orientation G) (Y : Set β) :
    Submodule (KFrameField β k) (Fin k → α → KFrameField β k) :=
  letI : DecidableEq α := Classical.decEq α
  letI : DecidablePred (· ∈ E(G)) := Classical.decPred _
  Submodule.pi Set.univ
    (fun _ : Fin k ↦ span (KFrameField β k) ((D.signedIncMatrix (KFrameField β k)) '' Y))

/-- **The `k`-frame row of a bar of `Y` lies in `blockPiSpanOn G k D Y`**
(`lem:k-frame-span-le-pi`): in each block `j` the row is the scalar
multiple `X_{(e,j)} • signedIncMatrix e`, which lies in the span of the incidence rows over `Y`
(since `e ∈ Y`). -/
theorem kFrameRow_mem_blockPiSpanOn {Y : Set β} {e : β} (he : e ∈ Y) :
    kFrameRow k D e ∈ blockPiSpanOn G k D Y := by
  rw [blockPiSpanOn, Submodule.mem_pi]
  intro j _
  rw [kFrameRow]
  exact Submodule.smul_mem _ _ (subset_span ⟨e, he, rfl⟩)

/-- **The span of the `k`-frame rows indexed by `Y` lies in `blockPiSpanOn G k D Y`**
(`lem:k-frame-span-le-pi`). -/
theorem span_kFrameRowOn_le_blockPiSpanOn {Y : Set β} :
    span (KFrameField β k) (kFrameRow k D '' Y) ≤ blockPiSpanOn G k D Y := by
  rw [span_le]
  rintro _ ⟨e, he, rfl⟩
  exact kFrameRow_mem_blockPiSpanOn he

/-- **Span finrank = matroid rank, via a representation** (`lem:k-frame-incidence-finrank-rk`;
piece (2) of `lem:k-frame-nonzero-monomial-forest`'s rank count). For any finite-rank matroid `M`
with a representation `v : M.Rep K W`, the `K`-dimension of the span of `v '' Y` equals the
matroid rank `M.rk Y`. A basis `I` of `Y` has `v '' Y ⊆ span (v '' I)` and
`LinearIndepOn K v I` (`Rep.isBasis'_iff`), so the two spans coincide; the LI image has
`finrank = (v '' I).ncard = I.ncard = M.rk Y` (`finrank_span_set_eq_card` + `IsBasis'.card`). -/
theorem _root_.Matroid.Rep.finrank_span_image_eq_rk {γ K W : Type*} [Field K] [AddCommGroup W]
    [Module K W] {M : Matroid γ} [M.RankFinite] (v : M.Rep K W) (Y : Set γ) :
    Module.finrank K (Submodule.span K (v '' Y)) = M.rk Y := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' Y
  obtain ⟨_, hindep, hsub⟩ := v.isBasis'_iff.mp hI
  have hfinI : I.Finite := hI.indep.finite
  have : Fintype (v '' I) := (hfinI.image v).fintype
  have hspan : Submodule.span K (v '' Y) = Submodule.span K (v '' I) :=
    le_antisymm (Submodule.span_le.mpr hsub)
      (Submodule.span_mono (Set.image_mono hI.subset))
  rw [hspan, finrank_span_set_eq_card hindep.id_image, ← Set.ncard_eq_toFinset_card',
    hindep.injOn.ncard_image, hI.card]

/-- **Incidence-span finrank = cycle-matroid rank** (`lem:k-frame-incidence-finrank-rk`, its
second statement; piece (2) of `lem:k-frame-nonzero-monomial-forest`'s rank count). For the
orientation `G.orientation_nonempty.some` underlying `cycleMatroidRep` (the same
one `kFrameMatroid` uses), the `K`-dimension of the span of the signed incidence rows indexed by `Y`
equals the cycle-matroid rank `G.cycleMatroid.rk Y`. This is the cycle-matroid
specialization of `Matroid.Rep.finrank_span_image_eq_rk` to `Graph.cycleMatroidRep`, whose
representation map is exactly `signedIncMatrix` for that orientation; it turns the
`finrank blockPiSpanOn = k · (incidence-span finrank)` bound of the rank count into
`k · r_{cycleMatroid}(Y)`. Stated over any field `K`, so the body-bar converse uses it over `ℝ`. -/
theorem finrank_span_signedIncMatrix_eq_cycleMatroid_rk [Finite β] (K : Type*) [Field K]
    (Y : Set β) :
    letI : DecidableEq α := Classical.decEq α
    letI : DecidablePred (· ∈ E(G)) := Classical.decPred _
    Module.finrank K
        (Submodule.span K ((G.orientation_nonempty.some.signedIncMatrix K) '' Y))
      = G.cycleMatroid.rk Y := by
  classical
  have : G.EdgeFinite := by
    rw [edgeFinite_iff]; exact Set.toFinite _
  have hrep := (G.cycleMatroidRep K).finrank_span_image_eq_rk Y
  have he : ⇑(G.cycleMatroidRep K) = G.orientation_nonempty.some.signedIncMatrix K := rfl
  rw [he] at hrep
  exact hrep

/-- The `K`-dimension of the `Y`-restricted block-diagonal product subspace is `k` times the
dimension of the `Y`-incidence-row span, which is `k · r_{cycleMatroid}(Y)` (a step of
`lem:k-frame-nonzero-monomial-forest`: pieces (1) and (2) of its rank count). Assembled from
`finrank_constPiSpan` and `finrank_span_signedIncMatrix_eq_cycleMatroid_rk`. -/
theorem finrank_blockPiSpanOn [Finite β] (Y : Set β) :
    Module.finrank (KFrameField β k)
        (blockPiSpanOn G k (G.orientation_nonempty.some) Y)
      = k * G.cycleMatroid.rk Y := by
  classical
  have : Module.Finite (KFrameField β k)
      (span (KFrameField β k)
        ((G.orientation_nonempty.some.signedIncMatrix (KFrameField β k)) '' Y)) :=
    Module.Finite.span_of_finite _ ((Set.toFinite Y).image _)
  rw [blockPiSpanOn, finrank_constPiSpan]
  congr 1
  exact finrank_span_signedIncMatrix_eq_cycleMatroid_rk (G := G) (KFrameField β k) Y

/-- **Generic independence ⟹ the count** (`lem:k-frame-nonzero-monomial-forest`; the direction of
Whiteley's Theorem 1 that he proves from a nonzero minor, here by a dimension bound). If the
generic `k`-frame rows on a bar set `E'` are linearly independent over `K`, then
`|Y| ≤ k · r_{cycleMatroid}(Y)` for every `Y ⊆ E'`.

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
  have : Fintype (v '' Y) := (Set.toFinite (v '' Y)).fintype
  have hcard : Module.finrank (KFrameField β k) (span (KFrameField β k) (v '' Y)) = Y.ncard := by
    simp only [finrank_span_set_eq_card hLIY.id_image, ← Set.ncard_eq_toFinset_card',
      hLIY.injOn.ncard_image]
  -- The block-product subspace is finite-dimensional (transport along `constPiSpanEquiv`).
  have : Module.Finite (KFrameField β k)
      (span (KFrameField β k)
        ((D.signedIncMatrix (KFrameField β k)) '' Y)) :=
    Module.Finite.span_of_finite _ ((Set.toFinite Y).image _)
  have : Module.Finite (KFrameField β k) (blockPiSpanOn G k D Y) := by
    rw [blockPiSpanOn]
    exact Module.Finite.equiv (constPiSpanEquiv k _).symm
  -- `finrank (span (v '' Y)) ≤ finrank (blockPiSpanOn) = k · r(Y)`.
  have hle := Submodule.finrank_mono (R := KFrameField β k)
    (span_kFrameRowOn_le_blockPiSpanOn (D := D) (Y := Y))
  rw [hcard, finrank_blockPiSpanOn] at hle
  exact hle

end Forward

section Reverse

open Submodule

variable {G : Graph α β} {k : ℕ} {D : Graph.orientation G}

/-- **Block-diagonal specialization of the `k`-frame rows on a forest packing**
(`lem:k-frame-specialize-li`, the linear-algebra core of the converse half of Whiteley's proof of
his Theorem 1). Given a `k`-tuple of acyclic bar sets `Fs : Fin k → Set β`, the rows obtained
by placing, for a bar `e ∈ Fs j`, the signed incidence row `signedIncMatrix D e` in block `j` and
`0` elsewhere — i.e. `Pi.single j (signedIncMatrix D e)` — are linearly independent over any
field `𝔽`, indexed by the disjoint union `Σ j, ↥(Fs j)`.

This is the specialized-to-full-rank matrix of the converse half: setting the block-`j`
indeterminate `X_{(e,j)}` to `1` on `Fs j` and `0` elsewhere turns each generic `k`-frame row
`kFrameRow k D e` into exactly this block-`single` row, and the resulting block-diagonal matrix
has full row rank because each block is the signed-incidence matrix of a forest
(`Graph.orientation.isAcyclicSet_linearIndepOn`, linearly independent), assembled across blocks by
`Pi.linearIndependent_single`. The step that a specialization of full rank witnesses generic
linear independence over `K` is `linearIndepOn_kFrameRow_of_isSparse_restrict`. -/
theorem specRow_linearIndependent (𝔽 : Type*) [Field 𝔽]
    (Fs : Fin k → Set β) (hFs : ∀ j, G.IsAcyclicSet (Fs j)) :
    letI : DecidableEq α := Classical.decEq α
    letI : DecidablePred (· ∈ E(G)) := Classical.decPred _
    LinearIndependent 𝔽
      (fun ji : Σ j : Fin k, (Fs j : Set β) ↦
        (Pi.single ji.1 (D.signedIncMatrix 𝔽 (ji.2 : β)) :
          Fin k → α → 𝔽)) :=
  letI : DecidableEq α := Classical.decEq α
  letI : DecidablePred (· ∈ E(G)) := Classical.decPred _
  Pi.linearIndependent_single
    (fun (j : Fin k) (e : (Fs j : Set β)) ↦ D.signedIncMatrix 𝔽 (e : β))
    (fun j ↦ D.isAcyclicSet_linearIndepOn (𝔽 := 𝔽) (hFs j))

/-- **Generic `k`-frame independence reduces to independence over the polynomial ring**
(`lem:k-frame-li-over-poly-ring`, the first half of the genericity-lift step of the converse
direction). The coefficient field `KFrameField β k = FractionRing (MvPolynomial (β × Fin k) ℚ)`
is the field of fractions of the polynomial ring `R = MvPolynomial (β × Fin k) ℚ`, and the
`k`-frame rows of any bar set `E'` are linearly independent over `KFrameField β k` **iff** they
are linearly independent over `R`. This is `LinearIndependent.iff_fractionRing` applied to the
fixed row family in the `K`-module `Fin k → α → KFrameField β k` (which is also an `R`-module via
the algebra map, with the scalar tower `IsScalarTower R K M` inherited from the `Pi` structure).

The point is to move the remaining nonzero-minor / specialization argument off the fraction field
(awkward — no general ring hom extends to it) and onto the integral domain `R`, where the
indeterminate-coefficient minors are honest polynomials. That step — that a
forest-packing specialization of full rank witnesses linear independence of the generic rows over
`R` (a nonzero polynomial minor specializing to a nonzero value cannot vanish identically) — is
`linearIndepOn_kFrameRow_of_isSparse_restrict`. -/
theorem linearIndepOn_kFrameRow_iff_over_polyRing (E' : Set β) :
    LinearIndepOn (KFrameField β k) (kFrameRow k D) E'
      ↔ LinearIndepOn (MvPolynomial (β × Fin k) ℚ) (kFrameRow k D) E' :=
  (LinearIndependent.iff_fractionRing (MvPolynomial (β × Fin k) ℚ) (KFrameField β k)
    (b := kFrameRow k D ∘ ((↑) : E' → β))).symm

/-- **Ring-hom naturality of the signed incidence matrix.** The signed incidence row of a bar
`e` has entries in `{0, 1, -1}`, so applying any ring homomorphism `φ : R →+* S` entrywise turns
`signedIncMatrix R e` into `signedIncMatrix S e`. The converse half specializes the
indeterminate-coefficient `k`-frame matrix down to `ℚ` via an `MvPolynomial`-evaluation hom; this
lemma is what lets that specialization commute past the incidence pattern (which is the same over
every ring). Local to this file — a statement about the `apnelson1/Matroid`-package
`Graph.orientation.signedIncMatrix`, not a mathlib fact. -/
theorem signedIncMatrix_map {R S : Type*} [CommRing R] [CommRing S]
    [DecidableEq α] [DecidablePred (· ∈ E(G))]
    (φ : R →+* S) (D : Graph.orientation G) (e : β) :
    (fun x => φ (D.signedIncMatrix R e x)) = D.signedIncMatrix S e := by
  ext x
  by_cases he : e ∈ E(G)
  · rw [Graph.orientation.signedIncMatrix_apply_of_mem he,
      Graph.orientation.signedIncMatrix_apply_of_mem he]
    simp only [Pi.sub_apply, map_sub]
    by_cases hx1 : x = (D.dInc ⟨e, he⟩).1 <;> by_cases hx2 : x = (D.dInc ⟨e, he⟩).2 <;>
      simp_all
  · rw [Graph.orientation.signedIncMatrix_apply_of_not_mem he,
      Graph.orientation.signedIncMatrix_apply_of_not_mem he]
    simp

/-- The **`k`-frame row function over the polynomial ring** `R = MvPolynomial (β × Fin k) ℚ`
(`lem:k-frame-specialize-identity`'s `R`-valued rows): the row for bar `e` places in each vertex
block `j` the indeterminate scaling `X_{(e, j)} • signedIncMatrix R e` of `e`'s signed incidence
row. This is the `R`-valued analogue
of `kFrameRow` (which is its image under `algebraMap R (KFrameField β k)`, by
`kFrameRow_eq_map_kFrameRowR`); moving the row family onto the integral domain `R` is what makes the
converse half's determinant / specialization argument (over `R`, then `φ`-specialized to `ℚ`)
available. -/
noncomputable def kFrameRowR (k : ℕ) (D : Graph.orientation G) :
    β → (Fin k → α → MvPolynomial (β × Fin k) ℚ) :=
  letI : DecidableEq α := Classical.decEq α
  letI : DecidablePred (· ∈ E(G)) := Classical.decPred _
  fun e j => (MvPolynomial.X (e, j) : MvPolynomial (β × Fin k) ℚ) •
    D.signedIncMatrix (MvPolynomial (β × Fin k) ℚ) e

/-- The generic `k`-frame row `kFrameRow k D e` is the image of the polynomial-ring row
`kFrameRowR k D e` under `algebraMap R (KFrameField β k)` applied entrywise. Both the
indeterminate coefficient `X_{(e, j)}` (`kFrameIndet`, defined as `algebraMap … (X (e, j))`) and
the incidence pattern (`signedIncMatrix_map`) push through the algebra map, so the two rows agree.
This is the bridge that lets `linearIndepOn_kFrameRow_iff_over_polyRing` be combined with an
`R`-level independence argument. -/
theorem kFrameRow_eq_map_kFrameRowR (e : β) :
    kFrameRow k D e = fun j x =>
      algebraMap (MvPolynomial (β × Fin k) ℚ) (KFrameField β k) (kFrameRowR k D e j x) := by
  classical
  ext j x
  rw [kFrameRow, kFrameRowR]
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  simp only [kFrameIndet, ← signedIncMatrix_map
    (algebraMap (MvPolynomial (β × Fin k) ℚ) (KFrameField β k)) D e]

/-- The **forest-packing specialization homomorphism** `R →+* ℚ` of a `k`-tuple
`Fs : Fin k → Set β` (`lem:k-frame-specialize-identity`'s `φ`): the `MvPolynomial`-evaluation
sending each indeterminate `X_{(e, j)}` to `1` if `e ∈ Fs j` and `0` otherwise. Specializing the
polynomial-ring `k`-frame matrix `kFrameRowR` along this hom turns the generic rows into the
block-diagonal forest matrix of `specRow_linearIndependent`
(`forestEval_kFrameRowR_eq_single`). -/
noncomputable def forestEval (Fs : Fin k → Set β) :
    MvPolynomial (β × Fin k) ℚ →+* ℚ :=
  letI : DecidablePred (fun p : β × Fin k => p.1 ∈ Fs p.2) := Classical.decPred _
  MvPolynomial.eval (fun p : β × Fin k => if p.1 ∈ Fs p.2 then (1 : ℚ) else 0)

/-- **The forest-packing specialization sends `kFrameRowR` to the block-single row**
(`lem:k-frame-specialize-identity`, the specialization identity of the converse half). For a
*disjoint* `k`-forest packing `Fs` and a bar `e ∈ Fs j₀`, applying `forestEval Fs` entrywise to the
polynomial-ring row `kFrameRowR k D e` yields exactly `Pi.single j₀ (signedIncMatrix ℚ e)` — the
block-`single` row that `specRow_linearIndependent` proves linearly independent. In block `j₀` the
coefficient `X_{(e, j₀)}` evaluates to `1` (as `e ∈ Fs j₀`), leaving the real signed incidence row;
in every other block `j ≠ j₀` disjointness gives `e ∉ Fs j`, so `X_{(e, j)}` evaluates to `0` and
the block vanishes. Incidence-pattern commutation with the evaluation hom is `signedIncMatrix_map`.
With the minor-nonvanishing engine
`Matrix.linearIndependent_rows_of_specialized_submatrix_det_ne_zero`, this identity finishes the
converse half. -/
theorem forestEval_kFrameRowR_eq_single (Fs : Fin k → Set β)
    (hdisj : Pairwise (Function.onFun Disjoint Fs)) {e : β} {j₀ : Fin k} (he : e ∈ Fs j₀) :
    letI : DecidableEq α := Classical.decEq α
    letI : DecidablePred (· ∈ E(G)) := Classical.decPred _
    (fun j x => forestEval Fs (kFrameRowR k D e j x)) =
      Pi.single j₀ (D.signedIncMatrix ℚ e) := by
  classical
  ext j x
  rw [kFrameRowR, forestEval]
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, MvPolynomial.eval_X]
  rw [← signedIncMatrix_map (MvPolynomial.eval
    (fun p : β × Fin k => if p.1 ∈ Fs p.2 then (1 : ℚ) else 0)) D e]
  by_cases hj : j = j₀
  · subst hj
    simp only [ite_eq_left he, one_mul, Pi.single_eq_same]
  · have hne : e ∉ Fs j := fun hmem => (hdisj hj).ne_of_mem hmem he rfl
    simp only [ite_eq_right hne, zero_mul, Pi.single_eq_of_ne hj, Pi.zero_apply]

/-- **Forest decomposition ⟹ generic independence** (`lem:k-frame-specialize-forest`, the converse
half of Whiteley's proof of his Theorem 1, 1988, p. 239). If the edge-restriction `G ↾ E'` is
`(k, k)`-sparse, then the generic `k`-frame rows on `E'` are linearly independent over the
coefficient field `K = KFrameField β k`.

The proof combines the converse-half lemmas. By `linearIndepOn_kFrameRow_iff_over_polyRing` it
suffices to argue over the polynomial ring `R = MvPolynomial (β × Fin k) ℚ`, and via
`kFrameRow_eq_map_kFrameRowR` (the generic row is the entrywise `algebraMap R K`-image of the
`R`-valued row `kFrameRowR`) over the `R`-valued rows. Those are passed, in uncurried
`Fin k × α` matrix form, to the minor-nonvanishing engine
`Matrix.linearIndependent_rows_of_specialized_submatrix_det_ne_zero` with the forest-packing
evaluation hom `forestEval Fs` (`Fs` a *disjoint* forest packing covering `E'`, from
`exists_forestPacking_cover_of_isSparse_restrict`): by `forestEval_kFrameRowR_eq_single` the
specialized rows are the block-`single` forest matrix, which is LI over ℚ
(`specRow_linearIndependent`, reindexed along the disjoint-cover bijection
`Set.unionEqSigmaOfDisjoint`), so it has a nonsingular maximal minor
(`Matrix.exists_submatrix_det_ne_zero_of_linearIndependent_rows`) — the nonzero specialized
determinant the engine takes. -/
theorem linearIndepOn_kFrameRow_of_isSparse_restrict [Finite α] [Finite β]
    {E' : Set β} (hE' : E' ⊆ E(G)) (hsparse : (G ↾ E').IsSparse k k) :
    LinearIndepOn (KFrameField β k) (kFrameRow k (G.orientation_nonempty.some)) E' := by
  classical
  have : Fintype β := Fintype.ofFinite β
  have : Fintype α := Fintype.ofFinite α
  have : Fintype E' := (Set.toFinite E').fintype
  set D := G.orientation_nonempty.some with hD
  set R := MvPolynomial (β × Fin k) ℚ with hR
  -- A disjoint forest packing covering `E'`.
  obtain ⟨Fs, hFcover, hgdisj, hFacyc⟩ :=
    exists_forestPacking_cover_of_isSparse_restrict hE' hsparse
  -- The disjoint cover gives `↥(⋃ Fs) ≃ Σ j, Fs j`; compose with `E' = ⋃ Fs`.
  let eqv : ↥E' ≃ Σ j : Fin k, (Fs j : Set β) :=
    (Set.equivOfEq hFcover.symm).trans (Set.unionEqSigmaOfDisjoint hgdisj)
  -- STEP 1 (engine): the `R`-valued rows over `E'`, in uncurried matrix form, are LI over `R`.
  have hR_uncurry : LinearIndependent R
      (fun e : E' => fun jx : Fin k × α => kFrameRowR k D (e : β) jx.1 jx.2) := by
    -- The specialization hom and its evaluated matrix (block-`single` forest rows).
    set φ := forestEval Fs with hφ
    -- Specialized matrix as rows indexed by `E'`.
    set Mspec : E' → (Fin k × α) → ℚ :=
      fun e jx => φ (kFrameRowR k D (e : β) jx.1 jx.2) with hMspec
    -- For `e ∈ E'`, `e ∈ Fs (eqv e).1`, so the specialized row is block-`single`.
    have hsingle : ∀ e : E', Mspec e =
        fun jx : Fin k × α =>
          (Pi.single (eqv e).1 (D.signedIncMatrix ℚ (e : β)) : Fin k → α → ℚ) jx.1 jx.2 := by
      intro e
      have hmem : (e : β) ∈ Fs (eqv e).1 := by
        have h1 : ((eqv e).2 : β) ∈ Fs (eqv e).1 := (eqv e).2.2
        have h2 : ((eqv e).2 : β) = (e : β) := by
          simp only [eqv, Equiv.trans_apply, Set.coe_snd_unionEqSigmaOfDisjoint,
            Set.equivOfEq_apply]
        rwa [h2] at h1
      funext jx
      have := forestEval_kFrameRowR_eq_single (D := D) Fs hgdisj hmem
      exact congrFun (congrFun this jx.1) jx.2
    -- The specialized rows are LI over ℚ, by reindexing `specRow_linearIndependent` along `eqv`.
    have hMspec_LI : LinearIndependent ℚ Mspec := by
      have hbase := specRow_linearIndependent (G := G) (D := D) ℚ Fs hFacyc
      -- `Mspec = (uncurry-of block-single) ∘ eqv`, an LI family precomposed with an equiv.
      have hcomp : Mspec =
          (⇑(LinearEquiv.curry ℚ ℚ (Fin k) α).symm ∘
            (fun ji : Σ j : Fin k, (Fs j : Set β) =>
              (Pi.single ji.1 (D.signedIncMatrix ℚ (ji.2 : β)) : Fin k → α → ℚ)))
            ∘ eqv := by
        funext e jx
        rw [Function.comp_apply, Function.comp_apply, hsingle e]
        have h2 : ((eqv e).2 : β) = (e : β) := by
          simp only [eqv, Equiv.trans_apply, Set.coe_snd_unionEqSigmaOfDisjoint,
            Set.equivOfEq_apply]
        rw [LinearEquiv.coe_curry_symm, Function.uncurry_apply_pair, h2]
      rw [hcomp]
      -- the uncurried block-single family is LI over ℚ (uncurry is an equiv)
      refine LinearIndependent.comp ?_ eqv eqv.injective
      exact (LinearMap.linearIndependent_iff _
        (LinearEquiv.ker (LinearEquiv.curry ℚ ℚ (Fin k) α).symm)).mpr hbase
    -- Maximal minor: a column selection with nonzero specialized det.
    obtain ⟨c, hc⟩ :=
      Matrix.exists_submatrix_det_ne_zero_of_linearIndependent_rows (M := Matrix.of Mspec)
        hMspec_LI
    -- Feed the engine: `φ (det of R-minor) = det of specialized minor ≠ 0`.
    refine Matrix.linearIndependent_rows_of_specialized_submatrix_det_ne_zero
      (fun e : E' => fun jx : Fin k × α => kFrameRowR k D (e : β) jx.1 jx.2) φ c ?_
    rw [RingHom.map_det]
    exact hc
  -- STEP 2: transfer the uncurried R-LI to the nested K-valued `kFrameRow`.
  rw [linearIndepOn_kFrameRow_iff_over_polyRing, LinearIndepOn]
  -- `kFrameRow ∘ (↑) = ψ ∘ (uncurried R rows)` for an injective `R`-linear `ψ`.
  -- ψ = curry (uncurried R → nested R) then entrywise `algebraMap R K` (nested R → nested K).
  let ψ : ((Fin k × α) → R) →ₗ[R] (Fin k → α → KFrameField β k) :=
    (((Algebra.linearMap R (KFrameField β k)).compLeft α).compLeft (Fin k)).comp
      (LinearEquiv.curry R R (Fin k) α).toLinearMap
  have halg_inj : Function.Injective ⇑(Algebra.linearMap R (KFrameField β k)) :=
    FaithfulSMul.algebraMap_injective R (KFrameField β k)
  have hentry_inj : Function.Injective
      ⇑(((Algebra.linearMap R (KFrameField β k)).compLeft α).compLeft (Fin k)) := by
    simp [← LinearMap.ker_eq_bot, LinearMap.ker_compLeft, LinearMap.ker_eq_bot.mpr halg_inj]
  have hψ_inj : Function.Injective ψ :=
    hentry_inj.comp (LinearEquiv.curry R R (Fin k) α).injective
  have hcomp : (fun e : E' => kFrameRow k D (e : β)) =
      ψ ∘ (fun e : E' => fun jx : Fin k × α => kFrameRowR k D (e : β) jx.1 jx.2) := by
    funext e
    rw [kFrameRow_eq_map_kFrameRowR (e : β)]
    rfl
  rw [hcomp]
  exact hR_uncurry.map' ψ (LinearMap.ker_eq_bot.mpr hψ_inj)

end Reverse

section Identification

variable {G : Graph α β} {k : ℕ}

/-- **Generic `k`-frame independence by the count** (`lem:k-frame-indep-iff-count`). A bar set
`E' ⊆ E(G)` is independent in the generic `k`-frame matroid `F(G, X)` if and only if the
edge-restriction `G ↾ E'` is `(k, k)`-sparse. The two directions of Whiteley's Theorem 1, by
`lem:k-frame-nonzero-monomial-forest` and `lem:k-frame-specialize-forest`: the
`Matroid.ofFun` independence predicate unfolds to linear independence of the generic `k`-frame rows
on `E'`, the forward direction (`forest_count_of_linearIndepOn_kFrameRow`) reads off the count
`∀ Y ⊆ E', |Y| ≤ k · r_{cycleMatroid}(Y)`, and the converse
(`linearIndepOn_kFrameRow_of_isSparse_restrict`) recovers linear independence from sparsity. The
count is exactly what `unionPow_cycleMatroid_indep_iff_isSparse_restrict` (via
`Matroid.Union_pow_indep_iff_count`) attaches to `(k, k)`-sparsity, which is what makes
`thm:k-frame-union-cycle` collapse to matroid extensionality. -/
theorem kFrameMatroid_indep_iff_isSparse_restrict [Finite α] [Finite β]
    {E' : Set β} (hE' : E' ⊆ E(G)) :
    (G.kFrameMatroid k).Indep E' ↔ (G ↾ E').IsSparse k k := by
  classical
  rw [kFrameMatroid, Matroid.ofFun_indep_iff, and_iff_left hE']
  refine ⟨fun hLI ↦ ?_, fun hsparse ↦ ?_⟩
  · rw [← unionPow_cycleMatroid_indep_iff_isSparse_restrict hE',
      Matroid.Union_pow_indep_iff_count]
    exact fun Y hY ↦ forest_count_of_linearIndepOn_kFrameRow hLI hY
  · exact linearIndepOn_kFrameRow_of_isSparse_restrict hE' hsparse

/-- **The generic `k`-frame matroid is the `k`-fold cycle-matroid union**
(`thm:k-frame-union-cycle`; Whiteley 1988, Theorem 1). For every multigraph
`G : Graph α β` and `k`, the generic `k`-frame matroid `F(G, X)` equals the
`k`-fold union `⋃ⱼ G.cycleMatroid` of the cycle matroid, **restricted to** the
bar set `E(G)`. Both sides are matroids on the edge type `β` with ground set
`E(G)`.

The `↾ E(G)` is bookkeeping forced by the ground-set convention of the vendored
`Matroid.Union` (`Matroid.Union Ms = (Matroid.sum' Ms).adjMap _ univ`, so its
ground set is `univ : Set β`, not `E(G)` — elements of `univ \ E(G)` sit in the
union as loops). Restricting to `E(G)` discards those loops and recovers the
ground set `E(G)` of `kFrameMatroid` (`Matroid.ofFun … E(G) …`). On `E' ⊆ E(G)`
both sides are independent exactly when `G ↾ E'` is `(k, k)`-sparse: the
`kFrameMatroid` side is `kFrameMatroid_indep_iff_isSparse_restrict` (both directions), the
union side is `unionPow_cycleMatroid_indep_iff_isSparse_restrict`, so the equality is
`Matroid.ext_indep`. -/
theorem kFrameMatroid_eq_unionPow_cycleMatroid [DecidableEq β] [Finite α] [Finite β] :
    G.kFrameMatroid k = (Matroid.Union (fun _ : Fin k ↦ G.cycleMatroid)) ↾ E(G) := by
  refine Matroid.ext_indep ?_ fun I hI ↦ ?_
  · simp only [kFrameMatroid_ground, Matroid.restrict_ground_eq]
  · rw [kFrameMatroid_ground] at hI
    simp only [Matroid.restrict_indep_iff, and_iff_left hI,
      unionPow_cycleMatroid_indep_iff_isSparse_restrict hI,
      ← kFrameMatroid_indep_iff_isSparse_restrict hI]

end Identification

end Graph
