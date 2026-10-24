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
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Basic.Real.Basic
public import CombinatorialRigidity.Mathlib.Algebra.MvPolynomial.Funext

/-!
# Rectangular linear independence via rank, polynomial-entry matrices, and block row operations

`Mathlib.LinearAlgebra.Matrix.NonsingularInverse` has `Matrix.linearIndependent_rows_iff_isUnit`
for **square** matrices over a field. The **rectangular** characterizations — the rows of
`A : Matrix m n R` are linearly independent iff `A.rank = #m`, and over a linearly ordered field
iff `(A * Aᵀ).det ≠ 0` (the Gram determinant) — follow from `Matrix.rank_self_mul_transpose`,
`Matrix.rank_eq_finrank_span_row` and `LinearIndependent.rank_matrix` in
`Mathlib.LinearAlgebra.Matrix.Rank`, but are not packaged in mathlib as iff lemmas.

Most of the file concerns polynomial-entry matrices, over **any field `K`**: that the rows of
`P(t)` (or of `P(p)`, with a multivariate parameter) are linearly independent at a parameter value
is witnessed by one minor. A column selection `e` at which the rows are independent at a base point
(`exists_submatrix_det_ne_zero_of_linearIndependent_rows`) picks out the minor
`Q := det (P selected on columns e)`, whose evaluation is the specialized minor's determinant, and
the rows are independent wherever that determinant is nonzero
(`linearIndependent_rows_of_specialized_submatrix_det_ne_zero`). Unlike the Gram determinant,
this needs no linear order on `K`.

* **Along a line** (`finite_setOf_not_linearIndependent_rows_along_affine_path`, `_of_polynomial`
  and their vector forms) the parameters where independence fails are finitely many
  (`Polynomial.finite_setOfPred_isRoot`), with no hypothesis on `K`. The combinatorial-rigidity
  project uses the vector form for `exists_uniform_rowIndependent_placement_dim_two`, the step
  behind `linearRigidityMatroid_eq_rigidityMatroid` (`LinearRigidityMatroid.lean`), and for the
  generic placements of `GenericRigidityMatroid.lean`.
* **Over a multivariate parameter** (`Matrix.exists_linearIndependent_rows_specialize`,
  `exists_le_finrank_span_polynomial`, `exists_finrank_dualCoannihilator_polynomial`) some point is
  good when `K` is infinite: the minor is a nonzero `MvPolynomial`, so it does not vanish somewhere
  (`MvPolynomial.exists_eval_ne_zero`). `exists_polynomial_ne_zero_of_linearIndependent_at`
  returns the minor instead, so that the minors of several families can be multiplied and one
  common non-root chosen. The project's genericity device (the blueprint's
  `lem:genericity-device`, after Katoh–Tanigawa 2011, §5.1) rests on these lemmas: the entries of
  the panel-hinge rigidity matrix are polynomials in the panel coordinates, so a rank attained at
  one realization is attained at a generic one, and no single line need reach the realizations
  the device is applied to.
* **Block matrices**: the elementary row operation `[1, -L₀; 0, 1]`, its unit determinant and its
  extension along a row injection, and the rows of a matrix whose left columns vanish. No
  declaration of the project uses them.

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
`linearIndependent_rows_iff_isUnit` at `A * Aᵀ`.

The order is needed: over `ℂ` the single row `(1, i)` is independent, while `A * Aᵀ = 1 + i² = 0`.
The lemmas below use a maximal minor instead, which needs no order. -/
theorem linearIndependent_rows_iff_det_mul_transpose_ne_zero
    [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype m] [DecidableEq m] [Fintype n] (A : Matrix m n R) :
    LinearIndependent R A.row ↔ (A * Aᵀ).det ≠ 0 := by
  rw [linearIndependent_rows_iff_rank_eq_card, ← rank_self_mul_transpose,
    ← linearIndependent_rows_iff_rank_eq_card, linearIndependent_row_iff_isUnit,
    isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

/-- **Linear independence of rows from a specialized nonzero minor.** Let `M : ι → κ → R` be
a (possibly rectangular) family of rows over an integral domain `R`, with `ι` finite. If there
is a column selection `e : ι → κ` and a ring homomorphism `φ : R →+* S` into a commutative ring
`S` such that the square submatrix `(i, j) ↦ M i (e j)` has a determinant whose
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
    [CommRing S] (M : ι → κ → R) (φ : R →+* S) (e : ι → κ)
    (hdet : φ (Matrix.of (fun i j : ι => M i (e j))).det ≠ 0) :
    LinearIndependent R M := by
  have hRne : (Matrix.of (fun i j : ι => M i (e j))).det ≠ 0 := fun h => hdet (by rw [h, map_zero])
  let f : (κ → R) →ₗ[R] (ι → R) := LinearMap.pi (fun i => LinearMap.proj (e i))
  refine LinearIndependent.of_comp f ?_
  have hcomp : (f ∘ M) = (fun i j : ι => M i (e j)) := by funext i j; rfl
  rw [hcomp]
  exact Matrix.linearIndependent_rows_of_det_ne_zero hRne

/-- **A matrix with linearly independent rows over a field has a nonsingular maximal minor.**
Let `M : Matrix m n K` over a field `K` with `m` and `n` finite. If the rows of `M` are linearly
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
  have : Fintype n := Fintype.ofFinite n
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
  have : Fintype κ := FiniteDimensional.fintypeBasisIndex b
  have hcard : Fintype.card κ = Fintype.card m := by
    rw [← Module.finrank_eq_card_basis b, Module.finrank_fintype_fun_eq_card]
  let em : m ≃ κ := (Fintype.equivOfCardEq hcard).symm
  refine ⟨a ∘ em, ?_⟩
  -- The transpose of the selected minor has rows `Mᵀ.row ∘ a ∘ em`, which are LI.
  set N : Matrix m m K := Matrix.of (fun i j : m => M i ((a ∘ em) j)) with hN
  have hrow : Nᵀ.row = Mᵀ.row ∘ a ∘ em := rfl
  have hLIN : LinearIndependent K Nᵀ.row := by rw [hrow]; exact hli.comp ⇑em em.injective
  have : IsUnit Nᵀ := Matrix.linearIndependent_row_iff_isUnit.mp hLIN
  rw [← Matrix.det_transpose]
  exact isUnit_iff_ne_zero.mp (Nᵀ.isUnit_iff_isUnit_det.mp this)

/-- **Linear independence is cofinite along an affine path.** Let `A B : Matrix m n K` over a
field `K`. If the rows of `A + t₀ • B` are linearly independent for some `t₀ : K`, then the rows
of `A + t • B` are linearly independent for all but finitely many `t : K`.

The proof uses a maximal minor rather than the Gram determinant
(`linearIndependent_rows_iff_det_mul_transpose_ne_zero`, which needs a linear order): a column
selection `e` witnessing the rows LI at `t₀`
(`exists_submatrix_det_ne_zero_of_linearIndependent_rows`) picks out a *single* minor
`Q := det (P selected on columns e) : Polynomial K` of the
polynomial-entry matrix `P := X • C(B) + C(A)`, whose evaluation at `t` is the specialized minor's
determinant (`(evalRingHom t).map_det`). `Q` is nonzero (nonzero at `t₀`), hence has finitely many
roots (`Polynomial.finite_setOfPred_isRoot`); at any non-root `t` the specialized minor is
nonsingular, so the rows are LI there too
(`linearIndependent_rows_of_specialized_submatrix_det_ne_zero`). No infiniteness or characteristic
hypothesis on `K` is needed: the argument only uses that a nonzero univariate polynomial has
finitely many roots. -/
theorem finite_setOf_not_linearIndependent_rows_along_affine_path
    {K : Type*} [Field K] [Finite m] [Finite n] (A B : Matrix m n K) {t₀ : K}
    (h : LinearIndependent K (A + t₀ • B).row) :
    {t : K | ¬ LinearIndependent K (A + t • B).row}.Finite := by
  classical
  have : Fintype m := Fintype.ofFinite m
  have : Fintype n := Fintype.ofFinite n
  -- Column selection witnessing LI at `t₀`.
  obtain ⟨e, he⟩ := exists_submatrix_det_ne_zero_of_linearIndependent_rows h
  -- Polynomial-entry matrix `P` whose evaluation at `t` is `A + t • B`.
  let P : Matrix m n (Polynomial K) :=
    (Polynomial.X : Polynomial K) • B.map Polynomial.C + A.map Polynomial.C
  -- The single witnessing minor polynomial `Q := det (P selected on columns `e`)`.
  let Q : Polynomial K := (Matrix.of (fun i j : m => P i (e j))).det
  have hP_eval : ∀ t : K, P.map (Polynomial.evalRingHom t) = A + t • B := by
    intro t; ext i j
    change Polynomial.eval t (P i j) = (A + t • B) i j
    simp only [P, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
    ring
  have hQ_eval : ∀ t : K, Q.eval t = (Matrix.of (fun i j : m => (A + t • B) i (e j))).det := by
    intro t
    change (Polynomial.evalRingHom t) Q = _
    rw [(Polynomial.evalRingHom t).map_det, RingHom.mapMatrix_apply]
    congr 1
    ext i j
    change Polynomial.eval t (P i (e j)) = (A + t • B) i (e j)
    have := congrFun (congrFun (hP_eval t) i) (e j)
    simpa [Matrix.map_apply] using this
  have hQ_ne : Q ≠ 0 := fun hQ0 => by
    have := hQ_eval t₀
    rw [hQ0, Polynomial.eval_zero] at this
    exact he this.symm
  -- The bad-`t` set is contained in `Q`'s finite root set.
  refine (Polynomial.finite_setOfPred_isRoot hQ_ne).subset fun t ht => ?_
  rw [Set.mem_ofPred_eq] at ht
  rw [Set.mem_ofPred_eq, Polynomial.IsRoot, hQ_eval]
  by_contra h_ne
  exact ht (linearIndependent_rows_of_specialized_submatrix_det_ne_zero
    (A + t • B).row (RingHom.id K) e (by rwa [RingHom.id_apply]))

/-- **Linear independence of rows is cofinite along a polynomial-entry family.** Generalizes
`finite_setOf_not_linearIndependent_rows_along_affine_path` from the affine family `A + t • B` to an
arbitrary polynomial-entry matrix `P : Matrix m n (Polynomial K)` over a field `K`: if the rows of
the specialization `P.map (eval t₀)` are linearly independent at some `t₀ : K`, then the rows of
`P.map (eval t)` are linearly independent for all but finitely many `t : K`.

The same maximal-minor argument as the affine case: a column selection `e` witnessing LI at `t₀`
(`exists_submatrix_det_ne_zero_of_linearIndependent_rows`) picks out the single minor
`Q := det (P selected on columns e) : Polynomial K`, whose evaluation at `t` is the specialized
minor's determinant; `Q` is nonzero (nonzero at `t₀`), so `Polynomial.finite_setOfPred_isRoot`
bounds the bad-`t` set, and at any non-root `t`
`linearIndependent_rows_of_specialized_submatrix_det_ne_zero` gives LI. The affine case is
`P = X • B.map C + A.map C`. No infiniteness or characteristic hypothesis on `K` is needed. -/
theorem finite_setOf_not_linearIndependent_rows_of_polynomial
    {K : Type*} [Field K] [Finite m] [Finite n] (P : Matrix m n (Polynomial K)) {t₀ : K}
    (h : LinearIndependent K (P.map (Polynomial.evalRingHom t₀)).row) :
    {t : K | ¬ LinearIndependent K (P.map (Polynomial.evalRingHom t)).row}.Finite := by
  classical
  have : Fintype m := Fintype.ofFinite m
  have : Fintype n := Fintype.ofFinite n
  obtain ⟨e, he⟩ := exists_submatrix_det_ne_zero_of_linearIndependent_rows h
  let Q : Polynomial K := (Matrix.of (fun i j : m => P i (e j))).det
  have hQ_eval : ∀ t : K, Q.eval t
      = (Matrix.of (fun i j : m => (P.map (Polynomial.evalRingHom t)) i (e j))).det := by
    intro t
    change (Polynomial.evalRingHom t) Q = _
    rw [(Polynomial.evalRingHom t).map_det, RingHom.mapMatrix_apply]
    congr 1
  have hQ_ne : Q ≠ 0 := fun hQ0 => by
    have := hQ_eval t₀
    rw [hQ0, Polynomial.eval_zero] at this
    exact he this.symm
  refine (Polynomial.finite_setOfPred_isRoot hQ_ne).subset fun t ht => ?_
  rw [Set.mem_ofPred_eq] at ht
  rw [Set.mem_ofPred_eq, Polynomial.IsRoot, hQ_eval]
  by_contra h_ne
  exact ht (linearIndependent_rows_of_specialized_submatrix_det_ne_zero
    (P.map (Polynomial.evalRingHom t)).row (RingHom.id K) e (by rwa [RingHom.id_apply]))

/-- **Linear independence of rows is attained at a generic specialization** (multivariate
analogue of `finite_setOf_not_linearIndependent_rows_along_affine_path`). Let `K` be an infinite
field and `P : Matrix m n (MvPolynomial σ K)` a polynomial-entry matrix. If the rows of the
specialization `P.map (eval p₀)` are linearly independent at some point `p₀ : σ → K`, then there
is a point `p : σ → K` at which the rows of `P.map (eval p)` are linearly independent.

The same maximal-minor argument, with an existence step in place of the finiteness step: a
column selection `e` witnessing LI at `p₀` picks out the single minor
`Q := det (P selected on columns e) : MvPolynomial σ K`. `Q` is nonzero (nonzero at `p₀`), hence
non-vanishing at some point `p` (`MvPolynomial.exists_eval_ne_zero`, the contrapositive of
`MvPolynomial.funext` over the infinite domain `K`, where `[Infinite K]` is used); there
`linearIndependent_rows_of_specialized_submatrix_det_ne_zero` gives LI. Unlike the univariate
(affine-line) case, the bad set `{p | rows dependent}` is generally not finite — it is the zero
locus of `Q`, whose complement is merely *nonempty* — so the conclusion is `∃ p, …` rather than
`{bad}.Finite`. -/
theorem exists_linearIndependent_rows_specialize {K σ : Type*} [Field K] [Infinite K]
    [Finite m] [Finite n]
    (P : Matrix m n (MvPolynomial σ K)) {p₀ : σ → K}
    (h : LinearIndependent K (P.map (MvPolynomial.eval p₀)).row) :
    ∃ p : σ → K, LinearIndependent K (P.map (MvPolynomial.eval p)).row := by
  classical
  have : Fintype m := Fintype.ofFinite m
  have : Fintype n := Fintype.ofFinite n
  obtain ⟨e, he⟩ := exists_submatrix_det_ne_zero_of_linearIndependent_rows h
  let Q : MvPolynomial σ K := (Matrix.of (fun i j : m => P i (e j))).det
  have hQ_eval : ∀ p : σ → K, MvPolynomial.eval p Q
      = (Matrix.of (fun i j : m => (P.map (MvPolynomial.eval p)) i (e j))).det := by
    intro p
    rw [(MvPolynomial.eval p).map_det, RingHom.mapMatrix_apply]
    congr 1
  have hQ_ne : Q ≠ 0 := by
    intro hQ0
    have := hQ_eval p₀
    rw [hQ0, map_zero] at this
    exact he this.symm
  -- `Q` is non-vanishing at some `p`; there the rows are LI.
  obtain ⟨p, hp⟩ := MvPolynomial.exists_eval_ne_zero hQ_ne
  have hdet : (Matrix.of (fun i j : m => (P.map (MvPolynomial.eval p)) i (e j))).det ≠ 0 := by
    rw [← hQ_eval]; exact hp
  exact ⟨p, linearIndependent_rows_of_specialized_submatrix_det_ne_zero
    (P.map (MvPolynomial.eval p)).row (RingHom.id K) e (by rwa [RingHom.id_apply])⟩

/-- **The block elementary row operation `[1, -L₀; 0, 1]` has unit determinant.** The
block-upper-triangular matrix subtracting `L₀ ·` (the lower `m₂`-row block) from the upper `m₁`-row
block is unimodular: its determinant is `det 1 · det 1 = 1` (via `Matrix.det_fromBlocks_zero₂₁`),
hence a unit, so as a left factor it preserves rank (`rank_mul_eq_right_of_isUnit_det`). -/
theorem rowOp_isUnit_det {K m₁ m₂ : Type*} [Field K] [Fintype m₁] [Fintype m₂] [DecidableEq m₁]
    [DecidableEq m₂] (L₀ : Matrix m₁ m₂ K) :
    IsUnit (Matrix.fromBlocks (1 : Matrix m₁ m₁ K) (-L₀) 0 (1 : Matrix m₂ m₂ K)).det := by
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_one, mul_one]
  exact isUnit_one

/-- **The block elementary row operation zeros the upper-right block.** Left-multiplying a block
matrix `fromBlocks A B C D` by `[1, -L₀; 0, 1]` subtracts `L₀ ·` the lower row block from the upper
one: the new top-left is `A − L₀ C` and the new top-right is `B − L₀ D`, which is `0` when
`B = L₀ D` (`hB`); the lower blocks `C`, `D` are untouched. Pure `Matrix.fromBlocks_multiply` + `hB`
arithmetic. This is the shape of the row operation of Katoh–Tanigawa 2011, (6.63), which adds a
weighted sum of the lower rows to a corner row so that its entries off the columns of `vᵢ` vanish
(by their (6.52)). -/
theorem rowOp_zeroes_upperRight {K m₁ m₂ n₁ n₂ : Type*} [Field K] [Fintype m₁] [Fintype m₂]
    [DecidableEq m₁] [DecidableEq m₂]
    {A : Matrix m₁ n₁ K} {B : Matrix m₁ n₂ K} {C : Matrix m₂ n₁ K} {D : Matrix m₂ n₂ K}
    (L₀ : Matrix m₁ m₂ K) (hB : B = L₀ * D) :
    Matrix.fromBlocks (1 : Matrix m₁ m₁ K) (-L₀) 0 (1 : Matrix m₂ m₂ K) * Matrix.fromBlocks A B C D
      = Matrix.fromBlocks (A - L₀ * C) 0 C D := by
  rw [Matrix.fromBlocks_multiply, hB]
  simp [sub_eq_add_neg]

/-- **The block elementary row operation `[1, -L₀; 0, 1]` extends along a row injection to a
unit-det row operation on the full index, fixing the rows outside the image.**
A unit-det left factor `Lrow : Matrix p p K` acts on the *full* row index `p`, while the block
matrix `[1, -L₀; 0, 1]` acts only on the rows the injection `re : m₁ ⊕ m₂ → p` selects. When `re`
is not surjective there is no bijection `(m₁ ⊕ m₂) ≃ p` to reindex along; this lemma uses instead
the equivalence
`e' : (m₁ ⊕ m₂) ⊕ ↥(Set.range re)ᶜ ≃ p` (`Equiv.ofInjective re` onto `range re`, then
`Equiv.Set.sumCompl`), and takes `Lrow := reindex e' e' (fromBlocks [1, -L₀; 0, 1] 0 0 1)`, the
operation on the image of `re` and the identity on its complement.

It gives `IsUnit Lrow.det` (`det_reindex_self` and `det_fromBlocks_zero₂₁` reduce it to the inner
block, whose determinant is `1`), `Lrow.submatrix re re = [1, -L₀; 0, 1]` (since
`re = ⇑e' ∘ Sum.inl`, the double relabelling cancels), and `Lrow (re i) x = 0` for `x ∉ range re`
(the upper-right block of the extended matrix is `0`), which lets
`rowOp_strictInjection_submatrix_eq_fromBlocks_zero₁₂` split a product through `re`. The indices
`m₁`, `m₂` need only be `Finite`; `Fintype.ofFinite` supplies the instances inside the proof. -/
theorem exists_rowOp_of_strictInjection {K p m₁ m₂ : Type*} [Field K] [Fintype p] [DecidableEq p]
    [Finite m₁] [Finite m₂] [DecidableEq m₁] [DecidableEq m₂]
    {re : m₁ ⊕ m₂ → p} (hre : Function.Injective re) (L₀ : Matrix m₁ m₂ K) :
    ∃ Lrow : Matrix p p K, IsUnit Lrow.det ∧
      Lrow.submatrix re re =
        Matrix.fromBlocks (1 : Matrix m₁ m₁ K) (-L₀) 0 (1 : Matrix m₂ m₂ K) ∧
      (∀ (i : m₁ ⊕ m₂) (x : p), x ∉ Set.range re → Lrow (re i) x = 0) := by
  classical
  have : Fintype m₁ := Fintype.ofFinite m₁
  have : Fintype m₂ := Fintype.ofFinite m₂
  -- the inner block op on the extended index `(m₁ ⊕ m₂) ⊕ ↥(range re)ᶜ`
  set B₀ : Matrix (m₁ ⊕ m₂) (m₁ ⊕ m₂) K :=
    Matrix.fromBlocks (1 : Matrix m₁ m₁ K) (-L₀) 0 (1 : Matrix m₂ m₂ K) with hB₀
  set Bext : Matrix ((m₁ ⊕ m₂) ⊕ ↥(Set.range re)ᶜ) ((m₁ ⊕ m₂) ⊕ ↥(Set.range re)ᶜ) K :=
    Matrix.fromBlocks B₀ 0 0 1 with hBext
  -- the extended equivalence `(m₁ ⊕ m₂) ⊕ ↥(range re)ᶜ ≃ p`
  set e' : ((m₁ ⊕ m₂) ⊕ ↥(Set.range re)ᶜ) ≃ p :=
    ((Equiv.ofInjective re hre).sumCongr (Equiv.refl _)).trans (Equiv.Set.sumCompl (Set.range re))
      with he'
  have hreEq : ∀ x, e'.symm (re x) = Sum.inl x := by
    intro x
    have : re x = e' (Sum.inl x) := by
      simp [he', Equiv.Set.sumCompl_apply_inl]
    rw [this, Equiv.symm_apply_apply]
  refine ⟨Matrix.reindex e' e' Bext, ?_, ?_, ?_⟩
  · -- unit determinant
    rw [Matrix.det_reindex_self, hBext, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one,
      hB₀, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_one, mul_one]
    exact isUnit_one
  · -- the `re`-selected block reads the raw row op
    ext i j
    rw [Matrix.submatrix_apply, Matrix.reindex_apply, Matrix.submatrix_apply, hreEq i, hreEq j,
      hBext, Matrix.fromBlocks_apply₁₁]
  · -- image rows vanish off image columns (`Bext`'s upper-right block is `0`)
    intro i x hx
    -- `e'.symm x` is on the complement side, so `Bext (Sum.inl i) (e'.symm x) = 0`
    obtain ⟨c, hc⟩ : ∃ c, e'.symm x = Sum.inr c := by
      cases h : e'.symm x with
      | inl y =>
        exact absurd ⟨y, by rw [← hreEq y] at h; exact e'.symm.injective h.symm⟩ hx
      | inr c => exact ⟨c, rfl⟩
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, hreEq i, hc, hBext,
      Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]

/-- **A row operation extended along a row injection zeros the upper-right block of the selected
rows.** For `Lrow` with the two properties `exists_rowOp_of_strictInjection` provides, the selected
block `hLsub : Lrow.submatrix re re = [1, -L₀; 0, 1]` and the vanishing
`hzero : ∀ i x, x ∉ range re → Lrow (re i) x = 0`, if `M'.submatrix re en = fromBlocks A B C D`
and `B = L₀ * D`, then `(Lrow * M').submatrix re en = fromBlocks (A - L₀ * C) 0 C D`.

The product splits *entrywise* by `Fintype.sum_of_injective`: the contracted sum
`∑ x : p, Lrow (re i) x * M' x (en j)` drops to
`∑ k : m₁ ⊕ m₂, [1, -L₀; 0, 1] i k * (M'.submatrix re en) k j` (the terms outside the image vanish
by `hzero`; the others reindex by `re`, with `Lrow (re i) (re k) = [1, -L₀; 0, 1] i k` from
`hLsub`), i.e. `(Lrow * M').submatrix re en = [1, -L₀; 0, 1] * M'.submatrix re en`, and
`rowOp_zeroes_upperRight` closes it. When `re` is bijective this is the split
`submatrix_mul_equiv` gives. -/
theorem rowOp_strictInjection_submatrix_eq_fromBlocks_zero₁₂
    {K p q m₁ m₂ n₁ n₂ : Type*} [Field K] [Fintype p] [Finite m₁] [Fintype m₂]
    [DecidableEq m₁] [DecidableEq m₂]
    (M' : Matrix p q K) (Lrow : Matrix p p K) {re : m₁ ⊕ m₂ → p} (hre : Function.Injective re)
    (en : (n₁ ⊕ n₂) → q) (L₀ : Matrix m₁ m₂ K)
    (hLsub : Lrow.submatrix re re =
      Matrix.fromBlocks (1 : Matrix m₁ m₁ K) (-L₀) 0 (1 : Matrix m₂ m₂ K))
    (hzero : ∀ (i : m₁ ⊕ m₂) (x : p), x ∉ Set.range re → Lrow (re i) x = 0)
    {A : Matrix m₁ n₁ K} {B : Matrix m₁ n₂ K} {C : Matrix m₂ n₁ K} {D : Matrix m₂ n₂ K}
    (hM' : M'.submatrix re en = Matrix.fromBlocks A B C D) (hB : B = L₀ * D) :
    (Lrow * M').submatrix re en = Matrix.fromBlocks (A - L₀ * C) 0 C D := by
  classical
  have : Fintype m₁ := Fintype.ofFinite m₁
  -- split the product entrywise through the injection: `(Lrow * M').submatrix re en = B₀ * (…)`
  have hsplit : (Lrow * M').submatrix re en
      = Matrix.fromBlocks (1 : Matrix m₁ m₁ K) (-L₀) 0 (1 : Matrix m₂ m₂ K) *
          M'.submatrix re en := by
    ext i j
    rw [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.mul_apply]
    refine (Fintype.sum_of_injective re hre
      (fun k => Matrix.fromBlocks (1 : Matrix m₁ m₁ K) (-L₀) 0 (1 : Matrix m₂ m₂ K) i k *
        (M'.submatrix re en) k j)
      (fun x => Lrow (re i) x * M' x (en j)) ?_ ?_).symm
    · intro x hx
      simp only [hzero i x hx, zero_mul]
    · intro k
      simp only [Matrix.submatrix_apply, ← hLsub]
  rw [hsplit, hM']
  exact rowOp_zeroes_upperRight L₀ hB

/-- **Dropping all-zero left columns preserves row linear independence.** For `N : Matrix m
(n₁ ⊕ n₂) R` whose left-block columns all vanish (`N i (Sum.inl j) = 0` for every row `i` and left
column `j`), the rows of `N` are linearly independent iff the rows of the right-column submatrix
`N.submatrix id Sum.inr` are. The all-zero left columns contribute nothing: each `N.row i` is the
zero-extension `Sum.elim 0 (right row)` of the corresponding submatrix row, and the zero-extension
linear map `Sum.elimZeroLeft : (n₂ → R) →ₗ[R] (n₁ ⊕ n₂ → R)` is injective (its kernel is `⊥`), so it
preserves and reflects linear independence (`LinearMap.linearIndependent_iff`). -/
theorem linearIndependent_row_of_zero_left_cols
    {R m n₁ n₂ : Type*} [CommRing R]
    (N : Matrix m (n₁ ⊕ n₂) R)
    (hz : ∀ i j, N i (Sum.inl j) = 0) :
    LinearIndependent R N.row ↔ LinearIndependent R (N.submatrix id Sum.inr).row := by
  rw [← LinearMap.linearIndependent_iff (Sum.elimZeroLeft (ι := n₂) (κ := n₁) (R := R))
    (by
      rw [LinearMap.ker_eq_bot']
      intro g hg
      funext j
      simpa [Sum.elimZeroLeft_apply] using congrFun hg (Sum.inr j))]
  have hrow : N.row
      = ⇑(Sum.elimZeroLeft (ι := n₂) (κ := n₁) (R := R)) ∘ (N.submatrix id Sum.inr).row := by
    funext i c
    cases c with
    | inl j => simp [Matrix.row, Function.comp, Sum.elimZeroLeft_apply, hz i j]
    | inr j => simp [Matrix.row, Function.comp, Sum.elimZeroLeft_apply, Matrix.submatrix]
  rw [hrow]

end Matrix

/-- **Vector-form polynomial-along-line.** For a finite-dim `W`-vector space over a field `K` and
an affine family `t ↦ fun i => a i + t • b i : K → ι → W` (with `ι` finite), if the family
is linearly independent at some `t₀ : K`, then it is LI for all but finitely many `t : K`.

Vector analogue of `Matrix.finite_setOf_not_linearIndependent_rows_along_affine_path`,
derived by pulling along a basis-induced isomorphism `W ≃ₗ[K] (Fin (finrank K W) → K)`. No
infiniteness or characteristic hypothesis on `K` is needed. -/
theorem LinearIndependent.finite_setOf_not_along_affine_path
    {K ι W : Type*} [Field K] [Finite ι] [AddCommGroup W] [Module K W] [Module.Finite K W]
    {a b : ι → W} {t₀ : K}
    (h : LinearIndependent K (fun i => a i + t₀ • b i)) :
    {t : K | ¬ LinearIndependent K (fun i => a i + t • b i)}.Finite := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  -- Pick a basis of `W` and identify `W` with `Fin n → K`.
  let φ : W ≃ₗ[K] (Fin (Module.finrank K W) → K) := (Module.finBasis K W).equivFun
  let A : Matrix ι (Fin (Module.finrank K W)) K := Matrix.of (fun i j => φ (a i) j)
  let B : Matrix ι (Fin (Module.finrank K W)) K := Matrix.of (fun i j => φ (b i) j)
  -- The affine matrix family `A + t • B` has rows `φ ∘ (a · + t • b ·)`.
  have h_row : ∀ t : K, (A + t • B).row = ⇑φ ∘ fun i => a i + t • b i := by
    intro t
    funext i j
    change A i j + t • B i j = φ (a i + t • b i) j
    rw [map_add, map_smul]
    rfl
  -- LI of the affine family ↔ LI of matrix rows, via the LinearEquiv `φ`.
  have h_iff : ∀ t : K,
      LinearIndependent K (fun i => a i + t • b i) ↔
      LinearIndependent K (A + t • B).row := by
    intro t
    rw [h_row t]
    exact (LinearMap.linearIndependent_iff φ.toLinearMap (LinearEquiv.ker φ)).symm
  -- Apply the matrix-form helper.
  refine (Matrix.finite_setOf_not_linearIndependent_rows_along_affine_path A B
    ((h_iff t₀).mp h)).subset fun t ht => ?_
  rw [Set.mem_ofPred_eq] at ht ⊢
  rwa [← h_iff]

/-- **Rank lower semicontinuity along an affine path.** For a finite-dim `W`-vector space over a
field `K` and an affine vector family `t ↦ fun i => a i + t • b i : K → ι → W` (with `ι` finite),
if the subfamily indexed by a subset `s : Set ι` is linearly independent at some `t₀ : K`, then
for all but finitely many `t : K` the span of the *full* family at `t` has `finrank` at least
`#s`. I.e. `finrank` of the span is cofinitely bounded below by any rank witnessed once.

This is the rank-form generalization of `LinearIndependent.finite_setOf_not_along_affine_path`
(which handles only the full-rank case where `s` is all of `ι` and the bound is "the family is
LI"): the subfamily on `s` stays independent for cofinitely many `t` (the LI lemma applied to that
subfamily), and an LI subfamily of size `#s` forces the full span's `finrank ≥ #s`
(`finrank_span_eq_card` + `Submodule.finrank_mono`). No infiniteness or characteristic
hypothesis on `K` is needed. -/
theorem LinearIndependent.le_finrank_span_along_affine_path_cofinite
    {K ι W : Type*} [Field K] [Finite ι] [AddCommGroup W] [Module K W] [Module.Finite K W]
    {a b : ι → W} {t₀ : K} {s : Set ι}
    (h : LinearIndependent K (fun i : s => a i + t₀ • b i)) :
    {t : K | Module.finrank K (Submodule.span K
      (Set.range (fun i => a i + t • b i))) < Nat.card s}.Finite := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have : Fintype s := Fintype.ofFinite s
  refine (LinearIndependent.finite_setOf_not_along_affine_path
    (a := fun i : s => a i) (b := fun i : s => b i) (t₀ := t₀) h).subset (fun t ht => ?_)
  rw [Set.mem_ofPred_eq] at ht ⊢
  intro hLI
  have hcard : Module.finrank K (Submodule.span K (Set.range (fun i : s => a i + t • b i)))
      = Nat.card s := by
    rw [finrank_span_eq_card hLI, Nat.card_eq_fintype_card]
  have hmono : Module.finrank K (Submodule.span K (Set.range (fun i : s => a i + t • b i)))
      ≤ Module.finrank K (Submodule.span K (Set.range (fun i => a i + t • b i))) :=
    Submodule.finrank_mono (Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨i, rfl⟩))
  omega

/-- **Codimension form: kernel finrank is cofinitely bounded above along an affine path.**
The dual of `LinearIndependent.le_finrank_span_along_affine_path_cofinite`, stated for an affine
family of *linear functionals* `t ↦ fun i => a i + t • b i : K → ι → Module.Dual K V` over a
field `K` (with `ι` finite and `V` finite-dimensional). If the subfamily indexed by `s : Set ι`
is linearly independent at some `t₀ : K`, then for all but finitely many `t : K` the common
kernel of the *full* functional family at `t` — packaged as the dual coannihilator
`(span (range (fun i => a i + t • b i))).dualCoannihilator = {x : V | ∀ i, (a i + t • b i) x = 0}`
(`Submodule.coe_dualCoannihilator_span`) — has `finrank` at most `finrank V - #s`. I.e. the
null-space dimension is cofinitely bounded *above* by any corank witnessed once.

The span and its coannihilator have complementary dimension at *every* `t`
(`Subspace.finrank_add_finrank_dualAnnihilator_eq` + `Subspace.finrank_dualCoannihilator_eq`:
`finrank coann + finrank span = finrank (Dual K V) = finrank V`), so "span finrank ≥ #s
cofinitely" turns into "coann finrank ≤ finrank V − #s cofinitely" verbatim. The exceptional set
is stated in the additive form `finrank V < #s + finrank coann` to sidestep `ℕ`-subtraction. No
infiniteness or characteristic hypothesis on `K` is needed. -/
theorem LinearIndependent.finrank_dualCoannihilator_along_affine_path_cofinite
    {K ι V : Type*} [Field K] [Finite ι] [AddCommGroup V] [Module K V] [Module.Finite K V]
    {a b : ι → Module.Dual K V} {t₀ : K} {s : Set ι}
    (h : LinearIndependent K (fun i : s => a i + t₀ • b i)) :
    {t : K | Module.finrank K V < Nat.card s + Module.finrank K
      (Submodule.span K (Set.range (fun i => a i + t • b i))).dualCoannihilator}.Finite := by
  classical
  refine (h.le_finrank_span_along_affine_path_cofinite (a := a) (b := b)).subset (fun t ht => ?_)
  rw [Set.mem_ofPred_eq] at ht ⊢
  -- complementary-dimension identity: coann finrank + span finrank = finrank V, at this `t`.
  set Φ : Subspace K (Module.Dual K V) :=
    Submodule.span K (Set.range (fun i => a i + t • b i)) with hΦ
  have hcompl : Module.finrank K Φ.dualCoannihilator + Module.finrank K Φ
      = Module.finrank K V := by
    rw [Subspace.finrank_dualCoannihilator_eq, add_comm,
      Subspace.finrank_add_finrank_dualAnnihilator_eq, Subspace.dual_finrank_eq]
  omega

/-- **Vector-form multivariate rank attainment.** For a finite-dim `W`-vector space over an
infinite field `K` and a *polynomial-coordinate* family `g : (σ → K) → ι → W` whose basis
coordinates are multivariate polynomial evaluations — fixed
`c : ι → Fin (finrank K W) → MvPolynomial σ K` and a basis identification
`φ : W ≃ₗ[K] (Fin (finrank K W) → K)` with `φ (g p i) j = eval p (c i j)` — if the subfamily
indexed by a subset `s : Set ι` is linearly independent at some point `p₀ : σ → K`, then there is
a point `p : σ → K` at which the span of the *full* family `g p` has `finrank` at least `#s`.

This is the multivariate analogue of `LinearIndependent.le_finrank_span_along_affine_path_cofinite`
(which handles a single affine line and concludes `{bad}.Finite`): here the parameter ranges over
all of `σ → K` and a *single* good point is produced (`∃ p`, not a cofinite set), by
`Matrix.exists_linearIndependent_rows_specialize`, whence the `[Infinite K]`. The subfamily on `s`
is LI at the produced `p`, forcing the full span's `finrank ≥ #s` (`finrank_span_eq_card` +
`Submodule.finrank_mono`). -/
theorem exists_le_finrank_span_polynomial
    {K ι W σ : Type*} [Field K] [Infinite K] [Finite ι] [AddCommGroup W] [Module K W]
    [Module.Finite K W]
    (g : (σ → K) → ι → W) (c : ι → Fin (Module.finrank K W) → MvPolynomial σ K)
    (φ : W ≃ₗ[K] (Fin (Module.finrank K W) → K))
    (hg : ∀ p i j, φ (g p i) j = MvPolynomial.eval p (c i j))
    {p₀ : σ → K} {s : Set ι}
    (h : LinearIndependent K (fun i : s => g p₀ i)) :
    ∃ p : σ → K, Nat.card s ≤ Module.finrank K (Submodule.span K (Set.range (g p))) := by
  classical
  have : Fintype s := Fintype.ofFinite s
  -- Submatrix on `s`: rows indexed by `s`, columns by `Fin (finrank K W)`.
  let P : Matrix s (Fin (Module.finrank K W)) (MvPolynomial σ K) :=
    Matrix.of (fun i j => c (i : ι) j)
  -- The specialized rows of `P` are `φ ∘ (g p)` restricted to `s`.
  have hrow : ∀ p : σ → K,
      (P.map (MvPolynomial.eval p)).row = ⇑φ ∘ (fun i : s => g p i) := by
    intro p; funext i j
    change MvPolynomial.eval p (c (i : ι) j) = φ (g p i) j
    rw [hg]
  -- LI of the vector subfamily ↔ LI of the matrix rows, via the LinearEquiv `φ`.
  have hiff : ∀ p : σ → K, LinearIndependent K (fun i : s => g p i)
      ↔ LinearIndependent K (P.map (MvPolynomial.eval p)).row := by
    intro p; rw [hrow p]
    exact (LinearMap.linearIndependent_iff φ.toLinearMap (LinearEquiv.ker φ)).symm
  -- Produce a good point from the matrix form.
  obtain ⟨p, hp⟩ := P.exists_linearIndependent_rows_specialize ((hiff p₀).mp h)
  have hsubLI : LinearIndependent K (fun i : s => g p i) := (hiff p).mpr hp
  refine ⟨p, ?_⟩
  have hcard : Module.finrank K (Submodule.span K (Set.range (fun i : s => g p i)))
      = Nat.card s := by
    rw [finrank_span_eq_card hsubLI, Nat.card_eq_fintype_card]
  have hmono : Module.finrank K (Submodule.span K (Set.range (fun i : s => g p i)))
      ≤ Module.finrank K (Submodule.span K (Set.range (g p))) :=
    Submodule.finrank_mono (Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨i, rfl⟩))
  omega

/-- **Codimension form: null-space finrank is attained at a generic specialization.** The dual of
`exists_le_finrank_span_polynomial`, stated for a polynomial-coordinate family of *linear
functionals* `g : (σ → K) → ι → Module.Dual K V` over an infinite field `K` (with `V`
finite-dimensional). If the subfamily indexed by `s : Set ι` is linearly independent at some
`p₀ : σ → K`, then there is a point `p : σ → K` at which the common kernel of the full functional
family — the dual coannihilator
`(span (range (g p))).dualCoannihilator = {x : V | ∀ i, g p i x = 0}`
(`Submodule.coe_dualCoannihilator_span`) — has `finrank` at most `finrank V − #s`.

The span form `exists_le_finrank_span_polynomial` is dualized here (inheriting its
`[Infinite K]`). The span and its coannihilator have complementary dimension
(`Subspace.finrank_add_finrank_dualAnnihilator_eq` + `Subspace.finrank_dualCoannihilator_eq`:
`finrank coann + finrank span = finrank (Dual K V) = finrank V`), so "span finrank ≥ #s at the
produced `p`" turns into "coann finrank ≤ finrank V − #s" verbatim. The conclusion is stated
additively (`#s + finrank coann ≤ finrank V`) to sidestep `ℕ`-subtraction — the same shape as
`LinearIndependent.finrank_dualCoannihilator_along_affine_path_cofinite`, but as `∃ p` rather than
`{bad}.Finite`. The combinatorial-rigidity project's genericity device, `exists_good_realization`
(`Molecular/AlgebraicInduction/GenericityDevice.lean`), applies it with `V` the space of screw
assignments, where the coannihilator contains the infinitesimal motions. -/
theorem exists_finrank_dualCoannihilator_polynomial
    {K ι V σ : Type*} [Field K] [Infinite K] [Finite ι] [AddCommGroup V] [Module K V]
    [Module.Finite K V]
    (g : (σ → K) → ι → Module.Dual K V)
    (c : ι → Fin (Module.finrank K (Module.Dual K V)) → MvPolynomial σ K)
    (φ : Module.Dual K V ≃ₗ[K] (Fin (Module.finrank K (Module.Dual K V)) → K))
    (hg : ∀ p i j, φ (g p i) j = MvPolynomial.eval p (c i j))
    {p₀ : σ → K} {s : Set ι}
    (h : LinearIndependent K (fun i : s => g p₀ i)) :
    ∃ p : σ → K, Nat.card s + Module.finrank K
      (Submodule.span K (Set.range (g p))).dualCoannihilator ≤ Module.finrank K V := by
  obtain ⟨p, hp⟩ := exists_le_finrank_span_polynomial g c φ hg h
  refine ⟨p, ?_⟩
  set Φ : Subspace K (Module.Dual K V) := Submodule.span K (Set.range (g p)) with hΦ
  have hcompl : Module.finrank K Φ.dualCoannihilator + Module.finrank K Φ
      = Module.finrank K V := by
    rw [Subspace.finrank_dualCoannihilator_eq, add_comm,
      Subspace.finrank_add_finrank_dualAnnihilator_eq, Subspace.dual_finrank_eq]
  omega

/-- **Vector-form rank-witnessing polynomial.** For a finite-dim `W`-vector space over a field `K`
and a *polynomial-coordinate* family `g : (σ → K) → ι → W` whose basis coordinates are
multivariate polynomial evaluations — fixed `c : ι → Fin (finrank K W) → MvPolynomial σ K` and a
basis identification `φ : W ≃ₗ[K] (Fin (finrank K W) → K)` with `φ (g p i) j = eval p (c i j)` —
if the subfamily indexed by a subset `s : Set ι` is linearly independent at some point
`p₀ : σ → K`, then there is a *single* multivariate polynomial `Q : MvPolynomial σ K` that is
**nonzero at `p₀`** (`eval p₀ Q ≠ 0`) and at *every* non-vanishing point of which the
`s`-subfamily `g p` is again linearly independent.

This is the *constructive* refinement of `exists_le_finrank_span_polynomial` (which produces a
single good point `p` via `MvPolynomial.exists_eval_ne_zero`, discarding the polynomial, and so
needs `[Infinite K]`): here the witnessing minor
`Q := det (P.submatrix on a maximal column selection)` is exposed instead, so several families'
polynomials can be **multiplied** and `MvPolynomial.exists_eval_ne_zero` applied to the product
once elsewhere, producing one shared non-vanishing point at which *all* the families are
independent. This lemma itself never picks a point, so it needs no infiniteness or characteristic
hypothesis on `K`. `Q` is built by selecting, via
`exists_submatrix_det_ne_zero_of_linearIndependent_rows`, a square column subset `e` of the
polynomial-entry submatrix `P : Matrix s (Fin (finrank K W)) (MvPolynomial σ K)` whose specialized
minor at `p₀` is nonsingular; `eval p Q` is then the specialized minor's determinant
(`(eval p).map_det`), so `eval p₀ Q ≠ 0` by construction and
`linearIndependent_rows_of_specialized_submatrix_det_ne_zero` upgrades any other non-root `p` back
to row independence. The LI of vectors ↔ LI of `φ`-coordinate rows is the same `φ`-pullback used in
`exists_le_finrank_span_polynomial`. The combinatorial-rigidity project applies it through
`exists_rankPolynomial_of_rigidOn_linking` and its variants
(`Molecular/AlgebraicInduction/GenericityDevice.lean`), and Case I of its algebraic induction
(`CaseI.lean`) multiplies such minors, so that one point serves the two realizations that
Katoh–Tanigawa 2011 combine in (6.6), in the proof of their Lemma 6.3. -/
theorem exists_polynomial_ne_zero_of_linearIndependent_at
    {K ι W σ : Type*} [Field K] [Finite ι] [AddCommGroup W] [Module K W]
    (g : (σ → K) → ι → W) (c : ι → Fin (Module.finrank K W) → MvPolynomial σ K)
    (φ : W ≃ₗ[K] (Fin (Module.finrank K W) → K))
    (hg : ∀ p i j, φ (g p i) j = MvPolynomial.eval p (c i j))
    {p₀ : σ → K} {s : Set ι}
    (h : LinearIndependent K (fun i : s => g p₀ i)) :
    ∃ Q : MvPolynomial σ K, MvPolynomial.eval p₀ Q ≠ 0 ∧
      ∀ p : σ → K, MvPolynomial.eval p Q ≠ 0 → LinearIndependent K (fun i : s => g p i) := by
  classical
  have : Fintype s := Fintype.ofFinite s
  -- Submatrix on `s`: rows indexed by `s`, columns by `Fin (finrank K W)`.
  let P : Matrix s (Fin (Module.finrank K W)) (MvPolynomial σ K) :=
    Matrix.of (fun i j => c (i : ι) j)
  -- The specialized rows of `P` at `p` are `φ ∘ (g p)` restricted to `s`.
  have hrow : ∀ p : σ → K,
      (P.map (MvPolynomial.eval p)).row = ⇑φ ∘ (fun i : s => g p i) := by
    intro p; funext i j
    change MvPolynomial.eval p (c (i : ι) j) = φ (g p i) j
    rw [hg]
  -- LI of the vector subfamily ↔ LI of the matrix rows, via the LinearEquiv `φ`.
  have hiff : ∀ p : σ → K, LinearIndependent K (fun i : s => g p i)
      ↔ LinearIndependent K (P.map (MvPolynomial.eval p)).row := by
    intro p; rw [hrow p]
    exact (LinearMap.linearIndependent_iff φ.toLinearMap (LinearEquiv.ker φ)).symm
  -- At `p₀` the rows are LI, so a maximal column selection gives a nonsingular specialized minor.
  obtain ⟨e, he⟩ :=
    Matrix.exists_submatrix_det_ne_zero_of_linearIndependent_rows ((hiff p₀).mp h)
  -- Evaluating the polynomial minor at `p` is the det of the specialized minor at `p`.
  have heval : ∀ p : σ → K, MvPolynomial.eval p (Matrix.of (fun i j : s => P i (e j))).det
      = (Matrix.of (fun i j : s => (P.map (MvPolynomial.eval p)).row i (e j))).det := by
    intro p; rw [(MvPolynomial.eval p).map_det]; rfl
  -- The witnessing minor polynomial `Q := det (P selected on columns `e`)`.
  refine ⟨(Matrix.of (fun i j : s => P i (e j))).det, ?_, fun p hp => ?_⟩
  · -- `eval p₀ Q = det ((P.map (eval p₀)) selected on `e`) ≠ 0` by `he`.
    rw [heval p₀]; exact he
  · -- At any non-root `p`, the specialized minor is nonsingular, so the rows are LI.
    rw [hiff p]
    refine Matrix.linearIndependent_rows_of_specialized_submatrix_det_ne_zero
      (P.map (MvPolynomial.eval p)).row (RingHom.id K) e ?_
    rw [RingHom.id_apply, ← heval p]
    exact hp

/-- **`exists_polynomial_ne_zero_of_linearIndependent_at`, basis-flexible column-index form.**
The reindexing companion of `exists_polynomial_ne_zero_of_linearIndependent_at`, as
`exists_good_realization_reindex` is of `exists_good_realization`
(`Molecular/AlgebraicInduction/GenericityDevice.lean`): it accepts the coordinate
identification `φ` against an *arbitrary* finite basis index `ν` (with the cardinality bridge
`e : Fin (finrank K W) ≃ ν`) rather than forcing the canonical `Fin (finrank K W)` literally, since
a concrete basis (e.g. `b.dualBasis.equivFun` for a project-supplied basis `b`) is indexed by
whatever type `b` itself is indexed by, not by `Fin (finrank K W)` up to defeq. Reduces to the base
lemma by precomposing `φ` with the index reindexing `LinearEquiv.funCongrLeft K K e` and pulling `c`
back along `e`, exactly as `exists_good_realization_reindex` does. The combinatorial-rigidity
project's abundance lemmas (`SimpleGraph.exists_isGenericPlacement_abundance` and its body-bar,
panel and hinge analogues) and the files of `Molecular/Molecule/Pencil/` use it. -/
theorem exists_polynomial_ne_zero_of_linearIndependent_at_reindex
    {K ι W σ ν : Type*} [Field K] [Finite ι] [AddCommGroup W] [Module K W]
    (e : Fin (Module.finrank K W) ≃ ν)
    (g : (σ → K) → ι → W) (c : ι → ν → MvPolynomial σ K)
    (φ : W ≃ₗ[K] (ν → K))
    (hg : ∀ p i j, φ (g p i) j = MvPolynomial.eval p (c i j))
    {p₀ : σ → K} {s : Set ι}
    (h : LinearIndependent K (fun i : s => g p₀ i)) :
    ∃ Q : MvPolynomial σ K, MvPolynomial.eval p₀ Q ≠ 0 ∧
      ∀ p : σ → K, MvPolynomial.eval p Q ≠ 0 → LinearIndependent K (fun i : s => g p i) :=
  exists_polynomial_ne_zero_of_linearIndependent_at g (fun i j => c i (e j))
    (φ.trans (LinearEquiv.funCongrLeft K K e))
    (fun p i j => by rw [LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply,
      LinearMap.funLeft_apply, hg]) h

/-- **The determinant of a matrix with entries in the range of a ring hom is in the range.** If
every entry of `M : Matrix n n S` lies in `f.range` for a ring hom `f : R →+* S`, so does `M.det`:
choose a preimage matrix `M₀ : Matrix n n R` (`M = M₀.map f`) and apply `RingHom.map_det`. -/
theorem Matrix.det_mem_range_of_entries {R S : Type*} [CommRing R] [CommRing S] {n : Type*}
    [Fintype n] [DecidableEq n] (f : R →+* S) (M : Matrix n n S)
    (hM : ∀ i j, M i j ∈ f.range) : M.det ∈ f.range := by
  classical
  choose M₀ hM₀ using hM
  refine ⟨(Matrix.of M₀).det, ?_⟩
  rw [RingHom.map_det]
  exact congrArg Matrix.det (Matrix.ext fun i j => hM₀ i j)

/-- **One-variable rank transfer along a polynomial-coordinate family.** For a basis
`b : Basis κ K M` over an infinite field `K` (with `κ` finite) and a family `g : K → ι → M`
(with `ι` finite) whose basis coordinates are *univariate-polynomial
evaluations* — a fixed `P : ι → κ → Polynomial K` with `b.repr (g t i) j = (P i j).eval t` — if the
family `g 0` is linearly independent at `t = 0`, then there is a `t` avoiding any prescribed finite
bad set and nonzero (`t ∉ bad`, `t ≠ 0`) at which `g t` is again linearly independent.

The proof pulls `g t` back along `φ := b.equivFun : M ≃ₗ[K] (κ → K)` (so
`φ (g t i) j = b.repr (g t i) j = (P i j).eval t`, i.e. `φ ∘ g t` is the row family of
`(Matrix.of P).map (evalRingHom t)`); LI transfers across `φ` (`LinearMap.linearIndependent_iff`),
so `finite_setOf_not_linearIndependent_rows_of_polynomial` makes the dependent-`t` set finite
(needing no infiniteness itself), and since `K` is infinite (`Set.Finite.infinite_compl`) some `t`
lies outside that set and the finite `bad ∪ {0}`.

This is the polynomial form of a step in the proof of Katoh–Tanigawa 2011, Lemma 5.2 (p. 669),
where each minor of `R(G, pₜ)` is a continuous function of `t`. The combinatorial-rigidity project
applies it along the one-parameter shear of Case III (`caseIIICandidate_exists_good_shear` in
`Molecular/AlgebraicInduction/CaseIII/Candidate.lean`): the family is independent at `t = 0`, and
the bad set holds the shears at which the sheared normal is parallel to another
(`setOf_not_shear_linearIndependent_subsingleton` in `PanelLayer.lean`). -/
theorem LinearIndependent.exists_notMem_of_polynomial_repr
    {K ι κ M : Type*} [Field K] [Infinite K] [Finite ι] [Finite κ] [AddCommGroup M] [Module K M]
    (b : Module.Basis κ K M) (g : K → ι → M) (P : ι → κ → Polynomial K)
    (hg : ∀ t i j, b.repr (g t i) j = (P i j).eval t)
    (h0 : LinearIndependent K (g 0)) (bad : Finset K) :
    ∃ t : K, t ∉ bad ∧ t ≠ 0 ∧ LinearIndependent K (g t) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have : Fintype κ := Fintype.ofFinite κ
  -- Basis identification `φ : M ≃ₗ[K] (κ → K)` and the polynomial-entry matrix `Pm := of P`.
  let φ : M ≃ₗ[K] (κ → K) := b.equivFun
  let Pm : Matrix ι κ (Polynomial K) := Matrix.of P
  -- The specialized rows of `Pm` at `t` are `φ ∘ (g t)`.
  have hrow : ∀ t : K, (Pm.map (Polynomial.evalRingHom t)).row = ⇑φ ∘ g t := by
    intro t; funext i j
    change (P i j).eval t = φ (g t i) j
    rw [← hg, b.equivFun_apply]
  -- LI of the vector family ↔ LI of the matrix rows, via the LinearEquiv `φ`.
  have hiff : ∀ t : K, LinearIndependent K (g t)
      ↔ LinearIndependent K (Pm.map (Polynomial.evalRingHom t)).row := by
    intro t; rw [hrow t]
    exact (LinearMap.linearIndependent_iff φ.toLinearMap (LinearEquiv.ker φ)).symm
  -- The set of `t` at which `g t` is dependent is finite, since `g 0` is independent.
  have hfin : {t : K | ¬ LinearIndependent K (g t)}.Finite := by
    refine (Matrix.finite_setOf_not_linearIndependent_rows_of_polynomial Pm
      (t₀ := 0) ((hiff 0).mp h0)).subset fun t ht => ?_
    rw [Set.mem_ofPred_eq] at ht ⊢
    rwa [hiff] at ht
  -- `K` is infinite, so there is a `t` outside the finite union of bad sets.
  have hbad : ({t : K | ¬ LinearIndependent K (g t)}
      ∪ ((bad : Set K) ∪ {0})).Finite :=
    hfin.union (bad.finite_toSet.union (Set.finite_singleton 0))
  obtain ⟨t, ht⟩ := hbad.infinite_compl.nonempty
  rw [Set.mem_compl_iff, Set.mem_union, Set.mem_union, Set.mem_ofPred_eq, not_or, not_or,
    not_not, Finset.mem_coe, Set.mem_singleton_iff] at ht
  exact ⟨t, ht.2.1, ht.2.2, ht.1⟩

