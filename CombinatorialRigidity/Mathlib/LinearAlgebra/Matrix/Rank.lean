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
# Rectangular linear independence via rank, polynomial-entry matrices, and block-triangular rank

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
* **Block-triangular matrices**: the rank is at least the row counts of two diagonal blocks with
  independent rows, also through unit-determinant row and column operations. The project applies
  these lemmas to the rigidity matrix in the block forms of Katoh–Tanigawa 2011, (6.60)–(6.64), in
  `Molecular/RigidityMatrix/Concrete.lean`.

Mirror path: `Mathlib/LinearAlgebra/Matrix/Rank.lean`. Promotion to mathlib is a copy-paste
into the upstream file, alongside `Matrix.rank_self_mul_transpose` and
`LinearIndependent.rank_matrix`.
-/

@[expose] public section

/-- **A finite family spanning a `finrank`-`N` subspace has a linearly independent `Fin N`-indexed
selection** (the indexed-family / fixed-cardinality companion of
`exists_linearIndependent'`). For a family `χ : ι → V` over a finite index `ι` whose span has
`Module.finrank` exactly `N`, there is an injective selection `sel : Fin N → ι` such that the
selected subfamily `χ ∘ sel` is linearly independent (and, being of size `N = finrank (span χ)`,
necessarily spans the same subspace, so `finrank (span (χ ∘ sel)) = N` follows immediately by
`finrank_span_eq_card`).

Unlike `exists_submatrix_det_ne_zero_of_linearIndependent_rows`, whose family spans the whole
coordinate space `m → K`, here the span is any finite-dimensional subspace, so the selection is
built as a basis of that submodule (`Module.Basis.mk` on the co-restricted family). The
combinatorial-rigidity project uses it to choose rows of a bottom block with independent rows
(`bottom_selection_of_crossFramework_span` in `Molecular/RigidityMatrix/Concrete.lean`). -/
theorem exists_finCard_linearIndependent_selection
    {K ι V : Type*} [Field K] [Finite ι] [AddCommGroup V] [Module K V]
    (χ : ι → V) {N : ℕ}
    (hrank : Module.finrank K (Submodule.span K (Set.range χ)) = N) :
    ∃ sel : Fin N → ι, Function.Injective sel ∧ LinearIndependent K (χ ∘ sel) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have : FiniteDimensional K (Submodule.span K (Set.range χ)) :=
    FiniteDimensional.span_of_finite K (Set.finite_range χ)
  -- A linearly independent subfamily `χ ∘ a` spanning `span (range χ)` (mathlib's
  -- `exists_linearIndependent'`), corestricted into that finite-dimensional submodule.
  obtain ⟨κ, a, ha_inj, hsp, hli⟩ := exists_linearIndependent' K χ
  have hsub : ∀ i, (χ ∘ a) i ∈ Submodule.span K (Set.range χ) := by
    intro i; rw [← hsp]; exact Submodule.subset_span ⟨i, rfl⟩
  let χ' : κ → Submodule.span K (Set.range χ) := fun i => ⟨(χ ∘ a) i, hsub i⟩
  have hli' : LinearIndependent K χ' := by
    rw [linearIndependent_iff'] at hli ⊢
    intro s g hg i hi
    refine hli s g ?_ i hi
    have := congrArg (Submodule.subtype _) hg
    simpa [χ'] using this
  -- `χ'` spans the submodule (it spans the same set `χ ∘ a` does, lifted into the submodule).
  have hsp' : Submodule.span K (Set.range χ') = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    rw [← hsp] at hx
    have hmem : x ∈ Submodule.span K (Set.range (χ ∘ a)) := hx
    refine Submodule.span_induction
      (p := fun y hy => (⟨y, by rw [← hsp]; exact Submodule.span_mono (by rfl) hy⟩ :
        Submodule.span K (Set.range χ)) ∈ Submodule.span K (Set.range χ')) ?_ ?_ ?_ ?_ hmem
    · rintro _ ⟨i, rfl⟩; exact Submodule.subset_span ⟨i, rfl⟩
    · exact Submodule.zero_mem _
    · intro y z _ _ hy hz; exact Submodule.add_mem _ hy hz
    · intro c y _ hy; exact Submodule.smul_mem _ c hy
  -- It is a basis of the submodule, so `κ` has exactly `N` elements: `Fin N ≃ κ`.
  let b : Module.Basis κ K (Submodule.span K (Set.range χ)) := Module.Basis.mk hli' (by rw [hsp'])
  have : Fintype κ := FiniteDimensional.fintypeBasisIndex b
  have hcardκ : Fintype.card κ = N := by rw [← hrank, ← Module.finrank_eq_card_basis b]
  let e : Fin N ≃ κ := (Fintype.equivFinOfCardEq hcardκ).symm
  refine ⟨a ∘ e, ha_inj.comp e.injective, ?_⟩
  have hcomp : χ ∘ (a ∘ e) = (χ ∘ a) ∘ e := by ext; simp
  rw [hcomp]; exact hli.comp e e.injective

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

/-- **Block-triangular rank additivity, as an inequality.** For a block-triangular matrix
`fromBlocks A B 0 D` over a field (lower-left block zero), if the rows of the diagonal blocks `A`
and `D` are each linearly independent, then the rank of the whole matrix is at least the sum of the
two diagonal-block row counts:
`#m₁ + #m₂ ≤ (fromBlocks A B 0 D).rank`.

`A`'s LI rows give a full-rank square minor (column selection `e₁`, nonzero det), `D`'s give
another (`e₂`); the combined `(m₁ ⊕ m₂)`-square minor of `fromBlocks A B 0 D` over those columns is
itself block-triangular, so its determinant is the product of the two minor dets
(`Matrix.det_fromBlocks_zero₂₁`), nonzero. Hence the minor has linearly independent rows, rank
`#m₁ + #m₂`, and `rank ≤ (fromBlocks A B 0 D).rank` by `rank_submatrix_le`. The span form is
`Submodule.finrank_add_card_le_of_linearIndependent_mkQ`. -/
theorem rank_fromBlocks_zero₂₁_ge_of_linearIndependent_rows
    {K m₁ m₂ n₁ n₂ : Type*} [Field K] [Fintype m₁] [Fintype m₂]
    [Fintype n₁] [Fintype n₂] {A : Matrix m₁ n₁ K} (B : Matrix m₁ n₂ K) {D : Matrix m₂ n₂ K}
    (hA : LinearIndependent K A.row) (hD : LinearIndependent K D.row) :
    Fintype.card m₁ + Fintype.card m₂ ≤ (Matrix.fromBlocks A B 0 D).rank := by
  classical
  -- Full-rank square minors of the diagonal blocks.
  obtain ⟨e₁, he₁⟩ := Matrix.exists_submatrix_det_ne_zero_of_linearIndependent_rows hA
  obtain ⟨e₂, he₂⟩ := Matrix.exists_submatrix_det_ne_zero_of_linearIndependent_rows hD
  -- The combined column selection of `fromBlocks A B 0 D` over rows `m₁ ⊕ m₂`.
  set c : m₁ ⊕ m₂ → n₁ ⊕ n₂ := Sum.elim (fun i => Sum.inl (e₁ i)) (fun j => Sum.inr (e₂ j)) with hc
  set M : Matrix (m₁ ⊕ m₂) (n₁ ⊕ n₂) K := Matrix.fromBlocks A B 0 D with hM
  -- The combined `(m₁ ⊕ m₂)`-square minor is block-triangular.
  set N : Matrix (m₁ ⊕ m₂) (m₁ ⊕ m₂) K := Matrix.of (fun i j => M i (c j)) with hN
  have hNblock : N = Matrix.fromBlocks (Matrix.of fun (i j : m₁) => A i (e₁ j))
      (Matrix.of fun (i : m₁) (j : m₂) => B i (e₂ j)) 0
      (Matrix.of fun (i j : m₂) => D i (e₂ j)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [hN, hM, hc, Matrix.fromBlocks]
  -- Its determinant is the product of the two minor dets (`det_fromBlocks_zero₂₁`), nonzero.
  have hNdet : N.det ≠ 0 := by
    rw [hNblock, Matrix.det_fromBlocks_zero₂₁]
    exact mul_ne_zero he₁ he₂
  -- LI rows of `N`, so `N.rank = #(m₁ ⊕ m₂)`.
  have hNli : LinearIndependent K N.row := Matrix.linearIndependent_rows_of_det_ne_zero hNdet
  have hNrank : N.rank = Fintype.card m₁ + Fintype.card m₂ := by
    rw [hNli.rank_matrix, Fintype.card_sum]
  -- `N` is the column-submatrix of `M`, so `N.rank ≤ M.rank`.
  have hNsub : N = M.submatrix id c := rfl
  calc Fintype.card m₁ + Fintype.card m₂ = N.rank := hNrank.symm
    _ ≤ M.rank := by
        rw [hNsub]
        exact Matrix.rank_submatrix_le (n₀ := m₁ ⊕ m₂) M id c

/-- **Block-triangular rank lower bound through a unit-det column operation.** For a matrix `M`
over a field, a *unit-determinant* square matrix `U` (an invertible column operation), and
reindexing equivalences `em`, `en` exhibiting `M * U` in the block-triangular shape
`fromBlocks A B 0 D` with the rows of both diagonal blocks `A`, `D` linearly independent, the rank
of the *original* `M` is at least the sum of the two diagonal-block row counts:
`#m₁ + #m₂ ≤ M.rank`.

The proof is a single `calc`: `rank_fromBlocks_zero₂₁_ge_of_linearIndependent_rows` bounds
`rank (fromBlocks A B 0 D)` below by `#m₁ + #m₂`, then `rank_reindex` and
`rank_mul_eq_left_of_isUnit_det` (the reindexing and the column operation preserve rank) transfer
that bound to `M.rank`.

The combinatorial-rigidity project applies it to the rigidity matrix with `U` the column
operation of Katoh–Tanigawa 2011 that takes (6.60) to (6.61), adding the columns of `vᵢ` to those
of `vᵢ₊₁` (`finrank_span_rigidityRows_ge_of_edge_fromBlocks` in
`Molecular/RigidityMatrix/Concrete.lean`). -/
-- `unusedArguments` FALSE POSITIVE: the `Fintype.ofFinite` bridge in the proof body
-- needs this instance to elaborate; it does not survive into the proof term.
@[nolint unusedArguments]
theorem rank_ge_of_isUnit_mul_reindex_fromBlocks
    {K p q m₁ m₂ n₁ n₂ : Type*} [Field K] [Finite p] [Fintype q] [DecidableEq q]
    [Fintype m₁] [Fintype m₂] [Finite n₁] [Finite n₂]
    (M : Matrix p q K) (U : Matrix q q K) (hU : IsUnit U.det)
    (em : p ≃ m₁ ⊕ m₂) (en : q ≃ n₁ ⊕ n₂)
    {A : Matrix m₁ n₁ K} {B : Matrix m₁ n₂ K} {D : Matrix m₂ n₂ K}
    (hblock : (M * U).reindex em en = fromBlocks A B 0 D)
    (hA : LinearIndependent K A.row) (hD : LinearIndependent K D.row) :
    Fintype.card m₁ + Fintype.card m₂ ≤ M.rank := by
  classical
  have : Fintype p := Fintype.ofFinite p
  have : Fintype n₁ := Fintype.ofFinite n₁
  have : Fintype n₂ := Fintype.ofFinite n₂
  calc Fintype.card m₁ + Fintype.card m₂
      ≤ (fromBlocks A B 0 D).rank :=
        rank_fromBlocks_zero₂₁_ge_of_linearIndependent_rows B hA hD
    _ = ((M * U).reindex em en).rank := by rw [hblock]
    _ = (M * U).rank := rank_reindex em en (M * U)
    _ = M.rank := rank_mul_eq_left_of_isUnit_det U M hU

/-- **Block-triangular rank lower bound through a unit-det column operation, row-submatrix
form.** The generalization of `rank_ge_of_isUnit_mul_reindex_fromBlocks` from a row *equivalence*
`em : p ≃ m₁ ⊕ m₂`, which places *every* row of the column-operated matrix `M * U` in one of the
blocks, to an arbitrary row map `re : m₁ ⊕ m₂ → p`: given a column equivalence
`en : (n₁ ⊕ n₂) ≃ q` exhibiting the *row submatrix* `(M * U).submatrix re en` in the
block-triangular shape `fromBlocks A B 0 D`, with the rows of both diagonal blocks `A`, `D`
linearly independent, the same lower bound `#m₁ + #m₂ ≤ M.rank` holds.

Rows outside the range of `re` are ignored, so `M` may have more rows than the two blocks hold, and
rows that would break the zero block can be left out. This is
`rank_fromBlocks_zero₂₁_ge_of_linearIndependent_rows`'s *column*-submatrix step
(`N = M.submatrix id c`) on the rows: both keep only the rows and columns the block-triangular minor
needs.

The proof is the same `calc` as the `reindex` form, with `Matrix.rank_submatrix_le` (a row submatrix
can only drop the rank) in place of the rank-preserving `rank_reindex`. The combinatorial-rigidity
project applies it in `finrank_span_rigidityRows_ge_of_edge_submatrix_fromBlocks`
(`Molecular/RigidityMatrix/Concrete.lean`). -/
theorem rank_ge_of_isUnit_mul_submatrix_fromBlocks
    {K p q m₁ m₂ n₁ n₂ : Type*} [Field K] [Fintype q] [DecidableEq q]
    [Fintype m₁] [Fintype m₂] [Finite n₁] [Finite n₂]
    (M : Matrix p q K) (U : Matrix q q K) (hU : IsUnit U.det)
    (re : m₁ ⊕ m₂ → p) (en : (n₁ ⊕ n₂) ≃ q)
    {A : Matrix m₁ n₁ K} {B : Matrix m₁ n₂ K} {D : Matrix m₂ n₂ K}
    (hblock : (M * U).submatrix re en = fromBlocks A B 0 D)
    (hA : LinearIndependent K A.row) (hD : LinearIndependent K D.row) :
    Fintype.card m₁ + Fintype.card m₂ ≤ M.rank := by
  classical
  have : Fintype n₁ := Fintype.ofFinite n₁
  have : Fintype n₂ := Fintype.ofFinite n₂
  calc Fintype.card m₁ + Fintype.card m₂
      ≤ (fromBlocks A B 0 D).rank :=
        rank_fromBlocks_zero₂₁_ge_of_linearIndependent_rows B hA hD
    _ = ((M * U).submatrix re en).rank := by rw [hblock]
    _ ≤ (M * U).rank := rank_submatrix_le (M * U) re en
    _ = M.rank := rank_mul_eq_left_of_isUnit_det U M hU

/-- **Block-triangular rank additivity, upper-right-zero form.** For a block-triangular matrix
`fromBlocks A 0 C D` over a field (*upper-right* block zero, the transpose of
`rank_fromBlocks_zero₂₁_ge_of_linearIndependent_rows`'s lower-left-zero shape), if the rows of the
diagonal blocks `A` and `D` are each linearly independent, then the rank of the whole matrix is at
least the sum of the two diagonal-block row counts:
`#m₁ + #m₂ ≤ (fromBlocks A 0 C D).rank`.

The proof is that of `rank_fromBlocks_zero₂₁_ge_of_linearIndependent_rows` with
`Matrix.det_fromBlocks_zero₁₂` for the combined minor's determinant: `A`'s LI rows give a full-rank
square minor (columns `e₁`), `D`'s give another (`e₂`), the combined `(m₁ ⊕ m₂)`-square minor of
`fromBlocks A 0 C D` over those columns is block-triangular, so its determinant is the product of
the two minor dets (nonzero) and the minor has rank `#m₁ + #m₂ ≤ (fromBlocks A 0 C D).rank` by
`rank_submatrix_le`.

This is the shape of Katoh–Tanigawa 2011, (6.64), where the rows of the corner block `Mᵢ` vanish off
the columns of `vᵢ`, and the bound they draw after (6.65),
`rank R(G, pᵢ) ≥ rank Mᵢ + rank R(G₁ ∖ {(v₀v₂)ᵢ*}, q₁)`. -/
theorem rank_fromBlocks_zero₁₂_ge_of_linearIndependent_rows
    {K m₁ m₂ n₁ n₂ : Type*} [Field K] [Fintype m₁] [Fintype m₂]
    [Fintype n₁] [Fintype n₂] {A : Matrix m₁ n₁ K} {D : Matrix m₂ n₂ K} (C : Matrix m₂ n₁ K)
    (hA : LinearIndependent K A.row) (hD : LinearIndependent K D.row) :
    Fintype.card m₁ + Fintype.card m₂ ≤ (Matrix.fromBlocks A 0 C D).rank := by
  classical
  -- Full-rank square minors of the diagonal blocks.
  obtain ⟨e₁, he₁⟩ := Matrix.exists_submatrix_det_ne_zero_of_linearIndependent_rows hA
  obtain ⟨e₂, he₂⟩ := Matrix.exists_submatrix_det_ne_zero_of_linearIndependent_rows hD
  -- The combined column selection of `fromBlocks A 0 C D` over rows `m₁ ⊕ m₂`.
  set c : m₁ ⊕ m₂ → n₁ ⊕ n₂ := Sum.elim (fun i => Sum.inl (e₁ i)) (fun j => Sum.inr (e₂ j)) with hc
  set M : Matrix (m₁ ⊕ m₂) (n₁ ⊕ n₂) K := Matrix.fromBlocks A 0 C D with hM
  -- The combined `(m₁ ⊕ m₂)`-square minor is upper-triangular.
  set N : Matrix (m₁ ⊕ m₂) (m₁ ⊕ m₂) K := Matrix.of (fun i j => M i (c j)) with hN
  have hNblock : N = Matrix.fromBlocks (Matrix.of fun (i j : m₁) => A i (e₁ j)) 0
      (Matrix.of fun (i : m₂) (j : m₁) => C i (e₁ j))
      (Matrix.of fun (i j : m₂) => D i (e₂ j)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [hN, hM, hc, Matrix.fromBlocks]
  -- Its determinant is the product of the two minor dets (`det_fromBlocks_zero₁₂`), nonzero.
  have hNdet : N.det ≠ 0 := by
    rw [hNblock, Matrix.det_fromBlocks_zero₁₂]
    exact mul_ne_zero he₁ he₂
  -- LI rows of `N`, so `N.rank = #(m₁ ⊕ m₂)`.
  have hNli : LinearIndependent K N.row := Matrix.linearIndependent_rows_of_det_ne_zero hNdet
  have hNrank : N.rank = Fintype.card m₁ + Fintype.card m₂ := by
    rw [hNli.rank_matrix, Fintype.card_sum]
  -- `N` is the column-submatrix of `M`, so `N.rank ≤ M.rank`.
  have hNsub : N = M.submatrix id c := rfl
  calc Fintype.card m₁ + Fintype.card m₂ = N.rank := hNrank.symm
    _ ≤ M.rank := by
        rw [hNsub]
        exact Matrix.rank_submatrix_le (n₀ := m₁ ⊕ m₂) M id c

/-- **Block-triangular rank lower bound through unit-det row and column operations,
upper-right-zero row-submatrix form.** The `fromBlocks A 0 C D` (upper-right zero) analogue of
`rank_ge_of_isUnit_mul_submatrix_fromBlocks`, with a *unit-determinant* left factor as well: for a
matrix `M` over a field, a unit-det square row operation `Lrow : Matrix p p K`, a unit-det square
column operation `U : Matrix q q K`, a row map `re : m₁ ⊕ m₂ → p` and a column equivalence
`en : (n₁ ⊕ n₂) ≃ q` exhibiting the row submatrix `(Lrow * M * U).submatrix re en` in the
block-triangular shape `fromBlocks A 0 C D` with the rows of both diagonal blocks `A`, `D` linearly
independent, the rank of the original `M` is at least the sum of the two diagonal-block row counts:
`#m₁ + #m₂ ≤ M.rank`.

The proof extends the `calc` of the column-operation version by two rank-invariance rewrites:
`rank_mul_eq_left_of_isUnit_det` removes the column operation `U`, then
`rank_mul_eq_right_of_isUnit_det` the row operation `Lrow`. In Katoh–Tanigawa 2011 the column
operation takes (6.60) to (6.61), whose corner rows need not vanish off the columns of `vᵢ`, and
the row operation (6.63) then gives the upper-right zero of (6.64);
`exists_rowOp_of_strictInjection` builds such an `Lrow` from the block operation of
`rowOp_zeroes_upperRight`. The combinatorial-rigidity project applies
it in `finrank_span_rigidityRows_ge_of_edge_submatrix_fromBlocks_zero₁₂`
(`Molecular/RigidityMatrix/Concrete.lean`). -/
theorem rank_ge_of_isUnit_mul_submatrix_fromBlocks_zero₁₂
    {K p q m₁ m₂ n₁ n₂ : Type*} [Field K] [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    [Fintype m₁] [Fintype m₂] [Finite n₁] [Finite n₂]
    (M : Matrix p q K) (Lrow : Matrix p p K) (hLrow : IsUnit Lrow.det)
    (U : Matrix q q K) (hU : IsUnit U.det)
    (re : m₁ ⊕ m₂ → p) (en : (n₁ ⊕ n₂) ≃ q)
    {A : Matrix m₁ n₁ K} {C : Matrix m₂ n₁ K} {D : Matrix m₂ n₂ K}
    (hblock : (Lrow * M * U).submatrix re en = fromBlocks A 0 C D)
    (hA : LinearIndependent K A.row) (hD : LinearIndependent K D.row) :
    Fintype.card m₁ + Fintype.card m₂ ≤ M.rank := by
  classical
  have : Fintype n₁ := Fintype.ofFinite n₁
  have : Fintype n₂ := Fintype.ofFinite n₂
  calc Fintype.card m₁ + Fintype.card m₂
      ≤ (fromBlocks A 0 C D).rank :=
        rank_fromBlocks_zero₁₂_ge_of_linearIndependent_rows C hA hD
    _ = ((Lrow * M * U).submatrix re en).rank := by rw [hblock]
    _ ≤ (Lrow * M * U).rank := rank_submatrix_le (Lrow * M * U) re en
    _ = (Lrow * M).rank := rank_mul_eq_left_of_isUnit_det U (Lrow * M) hU
    _ = M.rank := rank_mul_eq_right_of_isUnit_det Lrow M hLrow

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

/-- **A matrix whose every row is a fixed-weight linear combination of another matrix's rows
factors as `L₀ * D`.** Given `D : Matrix m₂ n K` and a weight family `w : m₁ → m₂ → K` such that
each row `B i` is the `w i`-weighted combination of `D`'s rows
(`hcomb : ∀ i j, B i j = ∑ i', w i i' * D i' j`), then `B = Matrix.of w * D`. Immediate from
`Matrix.mul_apply` and `Matrix.ext`. It turns a per-row linear-combination hypothesis into the
product `B = L₀ * D` that `rowOp_zeroes_upperRight` needs, with `L₀ := Matrix.of w`; the
combinatorial-rigidity project applies it to rigidity-matrix rows in `matrix_eq_mul_of_span_mem`
and `matrix_eq_mul_of_dual_row_comb` (`Molecular/RigidityMatrix/Concrete.lean`). -/
theorem of_eq_mul_of_row_comb {K m₁ m₂ n : Type*} [Fintype m₂] [CommRing K]
    (B : Matrix m₁ n K) (D : Matrix m₂ n K) (w : m₁ → m₂ → K)
    (hcomb : ∀ i j, B i j = ∑ i', w i i' * D i' j) :
    B = Matrix.of w * D := by
  ext i j
  rw [Matrix.mul_apply, hcomb]
  rfl

/-- **The block elementary row operation `[1, -L₀; 0, 1]` extends along a row injection to a
unit-det row operation on the full index, fixing the rows outside the image.**
`rank_ge_of_isUnit_mul_submatrix_fromBlocks_zero₁₂` takes a unit-det left factor
`Lrow : Matrix p p K` on the *full* row index `p`, while the block matrix `[1, -L₀; 0, 1]` acts
only on the rows the injection `re : m₁ ⊕ m₂ → p` selects. When `re` is not surjective there is no
bijection `(m₁ ⊕ m₂) ≃ p` to reindex along; this lemma uses instead the equivalence
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
preserves and reflects linear independence (`LinearMap.linearIndependent_iff`). The
independence companion of `rank_submatrix_inr_of_zero_left_cols`. -/
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

/-- **Dropping all-zero left columns preserves rank.** For `N : Matrix m (n₁ ⊕ n₂) R` (with
`n₁`, `n₂` finite) whose left-block columns all vanish (`N i (Sum.inl j) = 0`), the right-column
submatrix `N.submatrix id Sum.inr` has the same `Matrix.rank` as `N`. The column span of `N` is
generated by `N`'s columns; the left-block columns are the zero vector (and so lie in any
submodule), and the right-block columns are exactly the columns of the submatrix, so the two column
spans coincide and `Matrix.rank_eq_finrank_span_cols` gives equal ranks.

The combinatorial-rigidity project uses it to drop the columns of a body on which the rows of a
bottom block vanish (`rank_columnOp_toBlocks₂₂_eq_finrank_span_mixedBottom` and
`rank_columnOp_toBlocks₂₂_eq_finrank_span_Gab` in `Molecular/RigidityMatrix/Concrete.lean`). -/
theorem rank_submatrix_inr_of_zero_left_cols
    {R m n₁ n₂ : Type*} [CommRing R] [Fintype n₁] [Fintype n₂]
    (N : Matrix m (n₁ ⊕ n₂) R)
    (hz : ∀ i j, N i (Sum.inl j) = 0) :
    (N.submatrix id Sum.inr).rank = N.rank := by
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
  have hspan : Submodule.span R (Set.range (N.submatrix id Sum.inr).col)
      = Submodule.span R (Set.range N.col) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      apply Submodule.subset_span
      exact ⟨Sum.inr j, by funext i; simp [Matrix.col, Matrix.submatrix]⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨c, rfl⟩
      cases c with
      | inl j =>
        have hc : N.col (Sum.inl j) = 0 := by funext i; simp [Matrix.col, hz i j]
        rw [hc]; exact Submodule.zero_mem _
      | inr j =>
        apply Submodule.subset_span
        exact ⟨j, by funext i; simp [Matrix.col, Matrix.submatrix]⟩
  rw [hspan]

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
`exists_rankPolynomial_of_rigidOn` and its variants
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

