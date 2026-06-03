/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Polynomial
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Real.Basic

/-!
# Upstream candidates: rectangular linear independence via rank and the Gram determinant

`Mathlib.LinearAlgebra.Matrix.NonsingularInverse` has `Matrix.linearIndependent_rows_iff_isUnit`
for **square** matrices over a field (rows are LI iff the matrix is a unit, iff its determinant
is a unit, iff over a field it is nonzero). The corresponding **rectangular** characterizations
— that rows of `A : Matrix m n R` are LI iff `A.rank = #m`, and over an ordered field iff
`(A * Aᵀ).det ≠ 0` (the *Gram determinant* form) — are direct consequences of
`Matrix.rank_self_mul_transpose` / `Matrix.rank_eq_finrank_span_row` /
`LinearIndependent.rank_matrix` in `Mathlib.LinearAlgebra.Matrix.Rank`, but are not packaged
in mathlib as iff lemmas.

The combinatorial-rigidity project uses the Gram determinant form to characterize "the rows
of an affine polynomial matrix `M(t) = A + t • B` are LI at `t`" as the non-vanishing of a
single one-variable polynomial in `t`, then concludes via `Polynomial.finite_setOf_isRoot`
that the bad-`t` set is finite — the linear-interpolation-perturbation step of the Phase 8
target `linearRigidityMatroid_eq_rigidityMatroid` (see `LinearRigidityMatroid.lean`).

The Phase-21b genericity device (Katoh–Tanigawa 2011 Claim 6.4/6.9) needs the *rank-form*
generalization of the cofiniteness lemma — lower semicontinuity of `finrank` of the span of
an affine vector family along the path, not just the full-rank (LI) case. That is
`LinearIndependent.le_finrank_span_along_affine_path_cofinite` below: a single realization
at the target rank lifts to cofinitely many parameter values at *at least* that rank, the
"generic point attains the maximum rank" mechanism the device runs on.

Mirror path: `Mathlib/LinearAlgebra/Matrix/Rank.lean`. Promotion to mathlib is a copy-paste
into the upstream file, alongside `Matrix.rank_self_mul_transpose` and
`LinearIndependent.rank_matrix`.
-/

@[expose] public section

namespace Matrix

variable {R : Type*} {m n : Type*}

/-- The rows of a rectangular matrix over a field are linearly independent iff the matrix's
rank equals the number of rows. Iff form of `LinearIndependent.rank_matrix`, derived from
`Matrix.rank_eq_finrank_span_row` + `linearIndependent_iff_card_eq_finrank_span`. -/
theorem linearIndependent_rows_iff_rank_eq_card
    [Field R] [Fintype m] [Fintype n] (A : Matrix m n R) :
    LinearIndependent R A.row ↔ A.rank = Fintype.card m := by
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, ← rank_eq_finrank_span_row,
    eq_comm]

/-- **Rectangular linear independence via the Gram determinant.** The rows of `A : Matrix m n R`
over a linearly ordered field are linearly independent iff `det (A * Aᵀ) ≠ 0`. Rectangular
analogue of `Matrix.linearIndependent_rows_iff_isUnit` (the square case, where the rows are LI
iff `det A ≠ 0` directly). Routes through `rank_self_mul_transpose` and the square
`linearIndependent_rows_iff_isUnit` at `A * Aᵀ`. -/
theorem linearIndependent_rows_iff_det_mul_transpose_ne_zero
    [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype m] [DecidableEq m] [Fintype n] (A : Matrix m n R) :
    LinearIndependent R A.row ↔ (A * Aᵀ).det ≠ 0 := by
  rw [linearIndependent_rows_iff_rank_eq_card, ← rank_self_mul_transpose,
    ← linearIndependent_rows_iff_rank_eq_card, linearIndependent_rows_iff_isUnit,
    isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

/-- **Linear independence is cofinite along an affine path.** Let `A B : Matrix m n ℝ`.
If the rows of `A + t₀ • B` are linearly independent for some `t₀ : ℝ`, then the rows
of `A + t • B` are linearly independent for all but finitely many `t : ℝ`.

The Gram-det characterization (`linearIndependent_rows_iff_det_mul_transpose_ne_zero`)
turns "rows LI" into the non-vanishing of `((A + t • B) * (A + t • B)ᵀ).det`, the evaluation
at `t` of a single polynomial in `Polynomial ℝ` (the determinant of the polynomial-entry matrix
`(X • C(B) + C(A)) * (X • C(B) + C(A))ᵀ`). The polynomial is nonzero (since nonzero at
`t₀`) and hence has finitely many roots by `Polynomial.finite_setOf_isRoot`. -/
theorem finite_setOf_not_linearIndependent_rows_along_affine_path
    [Finite m] [Finite n] (A B : Matrix m n ℝ) {t₀ : ℝ}
    (h : LinearIndependent ℝ (A + t₀ • B).row) :
    {t : ℝ | ¬ LinearIndependent ℝ (A + t • B).row}.Finite := by
  classical
  haveI : Fintype m := Fintype.ofFinite m
  haveI : Fintype n := Fintype.ofFinite n
  -- Polynomial-entry matrix `P` whose evaluation at `t` is `A + t • B`.
  let P : Matrix m n (Polynomial ℝ) :=
    (Polynomial.X : Polynomial ℝ) • B.map Polynomial.C + A.map Polynomial.C
  -- Gram-det polynomial `Q := det(P * Pᵀ) ∈ Polynomial ℝ`.
  let Q : Polynomial ℝ := (P * Pᵀ).det
  -- Each entry of `P` evaluates to `(A + t • B)[i,j]` at `t`.
  have hP_eval : ∀ t : ℝ, P.map ⇑(Polynomial.evalRingHom t) = A + t • B := by
    intro t
    ext i j
    change Polynomial.eval t (P i j) = (A + t • B) i j
    simp only [P, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
    ring
  -- `Q.eval t = det((A + t • B) * (A + t • B)ᵀ)`, via `RingHom.map_det` +
  -- `RingHom.mapMatrix_apply` (the `mapMatrix → Matrix.map` bridge) + `Matrix.map_mul` +
  -- `Matrix.transpose_map` + `hP_eval`.
  have hQ_eval : ∀ t : ℝ, Q.eval t = ((A + t • B) * (A + t • B)ᵀ).det := by
    intro t
    change (Polynomial.evalRingHom t) Q = _
    rw [(Polynomial.evalRingHom t).map_det, RingHom.mapMatrix_apply, Matrix.map_mul,
      Matrix.transpose_map, hP_eval]
  -- `Q ≠ 0`: at `t = t₀`, `Q.eval t₀ = det((A + t₀ • B) * (A + t₀ • B)ᵀ) ≠ 0` by hypothesis.
  have hQ_ne : Q ≠ 0 := fun hQ_zero => by
    have := hQ_eval t₀
    rw [hQ_zero, Polynomial.eval_zero] at this
    exact ((linearIndependent_rows_iff_det_mul_transpose_ne_zero _).mp h) this.symm
  -- The bad-`t` set is contained in `Q`'s root set, which is finite.
  refine (Polynomial.finite_setOf_isRoot hQ_ne).subset fun t ht => ?_
  rw [Set.mem_setOf_eq] at ht
  rw [Set.mem_setOf_eq, Polynomial.IsRoot, hQ_eval]
  by_contra h_ne
  exact ht ((linearIndependent_rows_iff_det_mul_transpose_ne_zero _).mpr h_ne)

/-- **Linear independence of rows from a specialized nonzero minor.** Let `M : ι → κ → R` be
a (possibly rectangular) family of rows over an integral domain `R`, with `ι` finite. If there
is a column selection `e : ι → κ` and a ring homomorphism `φ : R →+* S` into a nontrivial
commutative ring `S` such that the square submatrix `(i, j) ↦ M i (e j)` has a determinant whose
image under `φ` is nonzero, then the rows `M` are linearly independent over `R`.

This is the "a polynomial minor with a nonzero specialization is itself nonzero, hence the generic
rows are independent" reflection: a nonzero specialized minor det forces the `R`-det to be nonzero
(`φ 0 = 0`), so the chosen square submatrix has independent rows
(`linearIndependent_rows_of_det_ne_zero`), and the full rows are independent by composing with the
column-projection linear map `(κ → R) → (ι → R)` (`LinearIndependent.of_comp`). No coefficient-wise
reflection along `φ` is used — that would be false when `φ` has a nontrivial kernel; the argument
routes through the minor's determinant instead. -/
theorem linearIndependent_rows_of_specialized_submatrix_det_ne_zero
    {ι κ R S : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [IsDomain R]
    [CommRing S] [Nontrivial S] (M : ι → κ → R) (φ : R →+* S) (e : ι → κ)
    (hdet : φ (Matrix.of (fun i j : ι => M i (e j))).det ≠ 0) :
    LinearIndependent R M := by
  have hRne : (Matrix.of (fun i j : ι => M i (e j))).det ≠ 0 := fun h => hdet (by rw [h, map_zero])
  let f : (κ → R) →ₗ[R] (ι → R) := LinearMap.pi (fun i => LinearMap.proj (e i))
  refine LinearIndependent.of_comp f ?_
  have hcomp : (f ∘ M) = (fun i j : ι => M i (e j)) := by funext i j; rfl
  rw [hcomp]
  exact Matrix.linearIndependent_rows_of_det_ne_zero hRne

/-- **A matrix with linearly independent rows over a field has a nonsingular maximal minor.**
Let `M : Matrix m n K` over a field `K` with `m` finite. If the rows of `M` are linearly
independent, then there is a square column selection `e : m → n` such that the `m × m` submatrix
`(i, j) ↦ M i (e j)` has nonzero determinant.

This is the "full row rank ⟹ nonzero square minor" extraction: the columns `Mᵀ.row : n → (m → K)`
span a subspace of `K`-dimension `M.rank = #m` (`LinearIndependent.rank_matrix` + `rank_transpose`),
which is all of `m → K`, so `Mᵀ.row` is a spanning family. Extracting a linearly independent
spanning subfamily (`exists_linearIndependent'`) gives a basis, necessarily of size `#m`; reindexing
it by `m` yields `e : m → n` with `Mᵀ.row ∘ e` linearly independent, i.e. the transpose of the
selected minor has independent rows, i.e. the minor has nonzero determinant
(`linearIndependent_rows_iff_isUnit` + `det_transpose` + `isUnit_iff_ne_zero`). -/
theorem exists_submatrix_det_ne_zero_of_linearIndependent_rows
    {m n K : Type*} [Field K] [Fintype m] [DecidableEq m] [Finite n] {M : Matrix m n K}
    (h : LinearIndependent K M.row) :
    ∃ e : m → n, (Matrix.of (fun i j : m => M i (e j))).det ≠ 0 := by
  classical
  haveI : Fintype n := Fintype.ofFinite n
  -- The columns of `M` (= rows of `Mᵀ`) span all of `m → K`.
  have hrank : Module.finrank K (Submodule.span K (Set.range Mᵀ.row)) = Fintype.card m := by
    rw [← Mᵀ.rank_eq_finrank_span_row, rank_transpose, h.rank_matrix]
  have hspan : Submodule.span K (Set.range Mᵀ.row) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [hrank, Module.finrank_fintype_fun_eq_card])
  -- Extract a linearly independent spanning subfamily of the columns.
  obtain ⟨κ, a, _, hsp, hli⟩ := exists_linearIndependent' K Mᵀ.row
  rw [hspan] at hsp
  -- It is a basis of `m → K`, so it has exactly `#m` elements: `κ ≃ m`.
  let b : Module.Basis κ K (m → K) := Module.Basis.mk hli (by rw [hsp])
  haveI : Fintype κ := FiniteDimensional.fintypeBasisIndex b
  have hcard : Fintype.card κ = Fintype.card m := by
    rw [← Module.finrank_eq_card_basis b, Module.finrank_fintype_fun_eq_card]
  let em : m ≃ κ := (Fintype.equivOfCardEq hcard).symm
  refine ⟨a ∘ em, ?_⟩
  -- The transpose of the selected minor has rows `Mᵀ.row ∘ a ∘ em`, which are LI.
  set N : Matrix m m K := Matrix.of (fun i j : m => M i ((a ∘ em) j)) with hN
  have hrow : Nᵀ.row = Mᵀ.row ∘ a ∘ em := rfl
  have hLIN : LinearIndependent K Nᵀ.row := by rw [hrow]; exact hli.comp ⇑em em.injective
  have : IsUnit Nᵀ := Matrix.linearIndependent_rows_iff_isUnit.mp hLIN
  rw [← Matrix.det_transpose]
  exact isUnit_iff_ne_zero.mp (Nᵀ.isUnit_iff_isUnit_det.mp this)

end Matrix

/-- **Vector-form polynomial-along-line.** For a finite-dim ℝ-vector space `W` and an
affine family `t ↦ fun i => a i + t • b i : ℝ → ι → W` (with `ι` finite), if the family
is linearly independent at some `t₀ : ℝ`, then it is LI for all but finitely many `t : ℝ`.

Vector analogue of `Matrix.finite_setOf_not_linearIndependent_rows_along_affine_path`,
derived by pulling along a basis-induced isomorphism `W ≃ₗ[ℝ] (Fin (finrank ℝ W) → ℝ)`. -/
theorem LinearIndependent.finite_setOf_not_along_affine_path
    {ι W : Type*} [Finite ι] [AddCommGroup W] [Module ℝ W] [Module.Finite ℝ W]
    {a b : ι → W} {t₀ : ℝ}
    (h : LinearIndependent ℝ (fun i => a i + t₀ • b i)) :
    {t : ℝ | ¬ LinearIndependent ℝ (fun i => a i + t • b i)}.Finite := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  -- Pick a basis of `W` and identify `W` with `Fin n → ℝ`.
  let φ : W ≃ₗ[ℝ] (Fin (Module.finrank ℝ W) → ℝ) := (Module.finBasis ℝ W).equivFun
  let A : Matrix ι (Fin (Module.finrank ℝ W)) ℝ := Matrix.of (fun i j => φ (a i) j)
  let B : Matrix ι (Fin (Module.finrank ℝ W)) ℝ := Matrix.of (fun i j => φ (b i) j)
  -- The affine matrix family `A + t • B` has rows `φ ∘ (a · + t • b ·)`.
  have h_row : ∀ t : ℝ, (A + t • B).row = ⇑φ ∘ fun i => a i + t • b i := by
    intro t
    funext i j
    change A i j + t • B i j = φ (a i + t • b i) j
    rw [map_add, map_smul]
    rfl
  -- LI of the affine family ↔ LI of matrix rows, via the LinearEquiv `φ`.
  have h_iff : ∀ t : ℝ,
      LinearIndependent ℝ (fun i => a i + t • b i) ↔
      LinearIndependent ℝ (A + t • B).row := by
    intro t
    rw [h_row t]
    exact (LinearMap.linearIndependent_iff φ.toLinearMap (LinearEquiv.ker φ)).symm
  -- Apply the matrix-form helper.
  refine (Matrix.finite_setOf_not_linearIndependent_rows_along_affine_path A B
    ((h_iff t₀).mp h)).subset fun t ht => ?_
  rw [Set.mem_setOf_eq] at ht ⊢
  rwa [← h_iff]

/-- **Rank lower semicontinuity along an affine path.** For a finite-dim ℝ-vector space `W`
and an affine vector family `t ↦ fun i => a i + t • b i : ℝ → ι → W` (with `ι` finite), if
the subfamily indexed by a subset `s : Set ι` is linearly independent at some `t₀ : ℝ`, then
for all but finitely many `t : ℝ` the span of the *full* family at `t` has `finrank` at least
`#s`. I.e. `finrank` of the span is cofinitely bounded below by any rank witnessed once.

This is the rank-form generalization of `LinearIndependent.finite_setOf_not_along_affine_path`
(which handles only the full-rank case where `s` is all of `ι` and the bound is "the family is
LI"): a maximal independent subfamily witnessing `finrank ≥ r` at `t₀` stays independent for
cofinitely many `t` (the LI lemma applied to that subfamily), and an LI subfamily of size `#s`
forces the full span's `finrank ≥ #s` (`finrank_span_eq_card` + `Submodule.finrank_mono`).
This is the analytic core of the Phase-21b genericity device (Katoh–Tanigawa 2011 Claim
6.4/6.9): the panel-hinge rigidity matrix's entries are polynomials in the panel coordinates,
so a single realization at the target rank lifts to the generic realization at *at least* that
rank — the "generic point attains the maximum rank over the parametrized family" step the
device supplies to `lem:case-I`'s gluing, `lem:case-II`'s span membership, and the
generic-rank lower bound of `prop:rigidity-matrix-prop11`. -/
theorem LinearIndependent.le_finrank_span_along_affine_path_cofinite
    {ι W : Type*} [Finite ι] [AddCommGroup W] [Module ℝ W] [Module.Finite ℝ W]
    {a b : ι → W} {t₀ : ℝ} {s : Set ι}
    (h : LinearIndependent ℝ (fun i : s => a i + t₀ • b i)) :
    {t : ℝ | Module.finrank ℝ (Submodule.span ℝ
      (Set.range (fun i => a i + t • b i))) < Nat.card s}.Finite := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  haveI : Fintype s := Fintype.ofFinite s
  refine (LinearIndependent.finite_setOf_not_along_affine_path
    (a := fun i : s => a i) (b := fun i : s => b i) (t₀ := t₀) h).subset (fun t ht => ?_)
  rw [Set.mem_setOf_eq] at ht ⊢
  intro hLI
  have hcard : Module.finrank ℝ (Submodule.span ℝ (Set.range (fun i : s => a i + t • b i)))
      = Nat.card s := by
    rw [finrank_span_eq_card hLI, Nat.card_eq_fintype_card]
  have hmono : Module.finrank ℝ (Submodule.span ℝ (Set.range (fun i : s => a i + t • b i)))
      ≤ Module.finrank ℝ (Submodule.span ℝ (Set.range (fun i => a i + t • b i))) :=
    Submodule.finrank_mono (Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨i, rfl⟩))
  omega
