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
public import Mathlib.Data.Real.Basic
public import CombinatorialRigidity.Mathlib.Algebra.MvPolynomial.Funext

/-!
# Upstream candidates: rectangular linear independence via rank, and the genericity engine

`Mathlib.LinearAlgebra.Matrix.NonsingularInverse` has `Matrix.linearIndependent_rows_iff_isUnit`
for **square** matrices over a field (rows are LI iff the matrix is a unit, iff its determinant
is a unit, iff over a field it is nonzero). The corresponding **rectangular** characterizations
— that rows of `A : Matrix m n R` are LI iff `A.rank = #m`, and over an ordered field iff
`(A * Aᵀ).det ≠ 0` (the *Gram determinant* form) — are direct consequences of
`Matrix.rank_self_mul_transpose` / `Matrix.rank_eq_finrank_span_row` /
`LinearIndependent.rank_matrix` in `Mathlib.LinearAlgebra.Matrix.Rank`, but are not packaged
in mathlib as iff lemmas. The Gram-determinant form (`linearIndependent_rows_iff_det_mul_transpose_
ne_zero`) is genuinely ordered-field-only (it can vanish on full-rank isotropic rows outside an
ordered field) and is retained below as an upstream candidate in its own right, but the
genericity engine this file exists for no longer routes through it.

The combinatorial-rigidity project's genericity engine characterizes "the rows of a
polynomial-entry matrix `P(t)` (or `P(p)`, multivariate) are LI at a parameter value" as the
non-vanishing of a single witnessing minor polynomial — over **any field `K`** (any
characteristic; infinite only where a point must actually be *produced*, not merely shown
cofinite). The engine reroutes off the Gram-determinant iff onto the **maximal-minor twin**
(`exists_submatrix_det_ne_zero_of_linearIndependent_rows` +
`linearIndependent_rows_of_specialized_submatrix_det_ne_zero`): a single column selection `e`
witnessing the rows LI at the base point picks out one minor `Q := det (P selected on columns e)`,
whose evaluation is the specialized minor's determinant; the "minor nonzero ⟹ rows LI" direction
of the twin is all the reverse implication ever needs — no per-minor union, no
product-of-minors polynomial. The univariate case (`finite_setOf_not_linearIndependent_rows_
along_affine_path` / `_of_polynomial`) concludes `{bad parameters}.Finite` via
`Polynomial.finite_setOf_isRoot` — the linear-interpolation-perturbation step of the Phase 8
target `linearRigidityMatroid_eq_rigidityMatroid` (see `LinearRigidityMatroid.lean`) — needing no
infiniteness or characteristic hypothesis on `K` at all.

The Phase-21b genericity device (Katoh–Tanigawa 2011 Claim 6.4/6.9) needs the *rank-form*
generalization of the cofiniteness lemma — lower semicontinuity of `finrank` of the span of
an affine vector family along the path, not just the full-rank (LI) case. That is
`LinearIndependent.le_finrank_span_along_affine_path_cofinite` below: a single realization
at the target rank lifts to cofinitely many parameter values at *at least* that rank, the
"generic point attains the maximum rank" mechanism the device runs on.

The affine engine handles only a single line `t ↦ a i + t • b i`. The genuine Claim 6.4 is the
**multivariate** statement: the panel-hinge rigidity-matrix entries are degree-two polynomials in
the panel coordinates `p : σ → K`, so no single affine line reaches the consumers' realizations.
The multivariate bricks below mirror the affine engine's shape but over `MvPolynomial σ K`-entry
families: `Matrix.exists_linearIndependent_rows_specialize` (matrix `∃`-form),
`exists_le_finrank_span_polynomial` (vector rank-`#s` `∃`-form), the consumer-facing
`exists_finrank_dualCoannihilator_polynomial` (codimension/null-space form), and the *constructive*
`exists_polynomial_ne_zero_of_linearIndependent_at` (exposes the witnessing minor polynomial
itself, so several families' polynomials can be multiplied and the funext step applied once to
the product). Where the affine lemmas conclude `{bad parameters}.Finite`, the multivariate lemmas
conclude `∃ p, good` directly: the witnessing minor is a *nonzero* `MvPolynomial`, hence
non-vanishing at *some* point by `MvPolynomial.exists_eval_ne_zero` (the contrapositive of
`MvPolynomial.funext` over the infinite domain `K` — the **only** place `[Infinite K]` enters the
matrix-level engine; a second, independent locus lives in the univariate consumer
`LinearIndependent.exists_notMem_of_polynomial_repr`, which picks a generic parameter out of a
cofinite set via `Set.Finite.infinite_compl`).

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

This is the *free maximal-rank basis-pick* the Phase-23f Case-III bottom-block selection needs
(`notes/Phase23-design.md` §(4.58.E) **BOT-2**; Katoh–Tanigawa 2011 §6.4.2 eqs. (6.61)–(6.64)): the
operated `(6.64)` bottom block `toBlocks₂₂` is row-LI once a `card m₂`-element subfamily of the
candidate's `a`-shifted edge functionals is independent, and the spanning identity
(`span_range_hingeRow_crossFramework_eq_rigidityRows`, **BOT-1**) plus the def-`0` rank count
`finrank (span R(Gab).rigidityRows) = card m₂` certify that the full family spans a space of
`finrank = card m₂` — so a free LI selection of that size exists. Unlike
`exists_submatrix_det_ne_zero_of_linearIndependent_rows` (whose family spans the *whole* coordinate
space `m → K`, so the selection is a basis of `⊤`), here the span is a proper finite-dimensional
subspace, so the selection is built as a basis of that submodule (`Module.Basis.mk` on the
co-restricted family) rather than of `⊤`. No matrix structure; carrier-agnostic. -/
theorem exists_finCard_linearIndependent_selection
    {K ι V : Type*} [Field K] [Finite ι] [AddCommGroup V] [Module K V]
    (χ : ι → V) {N : ℕ}
    (hrank : Module.finrank K (Submodule.span K (Set.range χ)) = N) :
    ∃ sel : Fin N → ι, Function.Injective sel ∧ LinearIndependent K (χ ∘ sel) := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  haveI : FiniteDimensional K (Submodule.span K (Set.range χ)) :=
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
  haveI : Fintype κ := FiniteDimensional.fintypeBasisIndex b
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

The project's genericity engine (below) has been rerouted onto the maximal-minor twin
(`exists_submatrix_det_ne_zero_of_linearIndependent_rows` +
`linearIndependent_rows_of_specialized_submatrix_det_ne_zero`), which works over any field — the
Gram form genuinely needs the linear order (it can vanish on full-rank isotropic rows outside an
ordered field), so this lemma is retained at its correct maximal generality even though the
reroute leaves it with no in-project caller; it is an upstream candidate in its own right
(Phase 33 PROSPECT G1 sweep adjudication). -/
theorem linearIndependent_rows_iff_det_mul_transpose_ne_zero
    [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype m] [DecidableEq m] [Fintype n] (A : Matrix m n R) :
    LinearIndependent R A.row ↔ (A * Aᵀ).det ≠ 0 := by
  rw [linearIndependent_rows_iff_rank_eq_card, ← rank_self_mul_transpose,
    ← linearIndependent_rows_iff_rank_eq_card, linearIndependent_rows_iff_isUnit,
    isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

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

/-- **Linear independence is cofinite along an affine path.** Let `A B : Matrix m n K` over a
field `K`. If the rows of `A + t₀ • B` are linearly independent for some `t₀ : K`, then the rows
of `A + t • B` are linearly independent for all but finitely many `t : K`.

Routes through the maximal-minor twin rather than the ordered-field Gram determinant
(`linearIndependent_rows_iff_det_mul_transpose_ne_zero`, which needs a linear order and so cannot
generalize past `ℝ`/`ℚ`): a column selection `e` witnessing the rows LI at `t₀`
(`exists_submatrix_det_ne_zero_of_linearIndependent_rows`) picks out a *single* minor
`Q := det (P selected on columns e) : Polynomial K` of the polynomial-entry matrix
`P := X • C(B) + C(A)`, whose evaluation at `t` is the specialized minor's determinant
(`(evalRingHom t).map_det`). `Q` is nonzero (nonzero at `t₀`), hence has finitely many roots
(`Polynomial.finite_setOf_isRoot`); at any non-root `t` the specialized minor is nonsingular, so
the rows are LI there too (`linearIndependent_rows_of_specialized_submatrix_det_ne_zero`, the
reverse direction of the twin). No infiniteness or characteristic hypothesis on `K` is needed —
the argument only ever uses that a nonzero univariate polynomial has finitely many roots. -/
theorem finite_setOf_not_linearIndependent_rows_along_affine_path
    {K : Type*} [Field K] [Finite m] [Finite n] (A B : Matrix m n K) {t₀ : K}
    (h : LinearIndependent K (A + t₀ • B).row) :
    {t : K | ¬ LinearIndependent K (A + t • B).row}.Finite := by
  classical
  haveI : Fintype m := Fintype.ofFinite m
  haveI : Fintype n := Fintype.ofFinite n
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
  refine (Polynomial.finite_setOf_isRoot hQ_ne).subset fun t ht => ?_
  rw [Set.mem_setOf_eq] at ht
  rw [Set.mem_setOf_eq, Polynomial.IsRoot, hQ_eval]
  by_contra h_ne
  exact ht (linearIndependent_rows_of_specialized_submatrix_det_ne_zero
    (A + t • B).row (RingHom.id K) e (by rwa [RingHom.id_apply]))

/-- **Linear independence of rows is cofinite along a polynomial-entry family.** Generalizes
`finite_setOf_not_linearIndependent_rows_along_affine_path` from the affine family `A + t • B` to an
arbitrary polynomial-entry matrix `P : Matrix m n (Polynomial K)` over a field `K`: if the rows of
the specialization `P.map (eval t₀)` are linearly independent at some `t₀ : K`, then the rows of
`P.map (eval t)` are linearly independent for all but finitely many `t : K`.

Same maximal-minor-twin argument as the affine case: a column selection `e` witnessing LI at `t₀`
(`exists_submatrix_det_ne_zero_of_linearIndependent_rows`) picks out the single minor
`Q := det (P selected on columns e) : Polynomial K`, whose evaluation at `t` is the specialized
minor's determinant; `Q` is nonzero (nonzero at `t₀`), so `Polynomial.finite_setOf_isRoot` bounds
the bad-`t` set, and at any non-root `t` the reverse twin
(`linearIndependent_rows_of_specialized_submatrix_det_ne_zero`) certifies LI. The affine engine is
the special case `P = X • B.map C + A.map C`. No infiniteness or characteristic hypothesis on `K`
is needed. -/
theorem finite_setOf_not_linearIndependent_rows_of_polynomial
    {K : Type*} [Field K] [Finite m] [Finite n] (P : Matrix m n (Polynomial K)) {t₀ : K}
    (h : LinearIndependent K (P.map (Polynomial.evalRingHom t₀)).row) :
    {t : K | ¬ LinearIndependent K (P.map (Polynomial.evalRingHom t)).row}.Finite := by
  classical
  haveI : Fintype m := Fintype.ofFinite m
  haveI : Fintype n := Fintype.ofFinite n
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
  refine (Polynomial.finite_setOf_isRoot hQ_ne).subset fun t ht => ?_
  rw [Set.mem_setOf_eq] at ht
  rw [Set.mem_setOf_eq, Polynomial.IsRoot, hQ_eval]
  by_contra h_ne
  exact ht (linearIndependent_rows_of_specialized_submatrix_det_ne_zero
    (P.map (Polynomial.evalRingHom t)).row (RingHom.id K) e (by rwa [RingHom.id_apply]))

/-- **Linear independence of rows is attained at a generic specialization** (multivariate
analogue of `finite_setOf_not_linearIndependent_rows_along_affine_path`). Let `K` be an infinite
field and `P : Matrix m n (MvPolynomial σ K)` a polynomial-entry matrix. If the rows of the
specialization `P.map (eval p₀)` are linearly independent at some point `p₀ : σ → K`, then there
is a point `p : σ → K` at which the rows of `P.map (eval p)` are linearly independent.

Same maximal-minor-twin argument, but the finiteness step is replaced by an existence step: a
column selection `e` witnessing LI at `p₀` picks out the single minor
`Q := det (P selected on columns e) : MvPolynomial σ K`. `Q` is nonzero (nonzero at `p₀`), hence
non-vanishing at some point `p` (`MvPolynomial.exists_eval_ne_zero`, the contrapositive of
`MvPolynomial.funext` over the infinite domain `K` — the one place `[Infinite K]` enters this
engine); there the reverse twin
(`linearIndependent_rows_of_specialized_submatrix_det_ne_zero`) certifies LI. Unlike the univariate
(affine-line) case, the bad set `{p | rows dependent}` is generally not finite — it is the zero
locus of `Q`, whose complement is merely *nonempty* — so the conclusion is `∃ p, …` rather than
`{bad}.Finite`. -/
theorem exists_linearIndependent_rows_specialize {K σ : Type*} [Field K] [Infinite K]
    [Finite m] [Finite n]
    (P : Matrix m n (MvPolynomial σ K)) {p₀ : σ → K}
    (h : LinearIndependent K (P.map (MvPolynomial.eval p₀)).row) :
    ∃ p : σ → K, LinearIndependent K (P.map (MvPolynomial.eval p)).row := by
  classical
  haveI : Fintype m := Fintype.ofFinite m
  haveI : Fintype n := Fintype.ofFinite n
  obtain ⟨e, he⟩ := exists_submatrix_det_ne_zero_of_linearIndependent_rows h
  let Q : MvPolynomial σ K := (Matrix.of (fun i j : m => P i (e j))).det
  have hQ_eval : ∀ p : σ → K, MvPolynomial.eval p Q
      = (Matrix.of (fun i j : m => (P.map (MvPolynomial.eval p)) i (e j))).det := by
    intro p
    change (MvPolynomial.eval p) Q = _
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

/-- **Block-triangular rank additivity, as an inequality** (Katoh–Tanigawa 2011 eq. (6.64);
Phase 23d route-A piece A3). For a block-triangular matrix `fromBlocks A B 0 D` over a field
(lower-left block zero), if the rows of the diagonal blocks `A` and `D` are each linearly
independent, then the rank of the whole matrix is at least the sum of the two diagonal-block
row counts:
`#m₁ + #m₂ ≤ (fromBlocks A B 0 D).rank`.

This is the matrix-level analogue of the dual-space block cert
`Submodule.finrank_add_card_le_of_linearIndependent_mkQ`: where the dual-space version expresses
KT's (6.61) submatrix-containment as a span *membership* (which walled — see
`notes/Phase23-design.md` §(4.18)–(4.30)), the matrix version is a structural fact about a literal
block matrix and never forms a membership. The proof is exactly the (6.64) block-triangular minor
argument: `A`'s LI rows give a full-rank square minor (column selection `e₁`, nonzero det), `D`'s
give another (`e₂`); the combined `(m₁ ⊕ m₂)`-square minor of `fromBlocks A B 0 D` over those
columns is itself block-triangular, so its determinant is the product of the two minor dets
(`Matrix.det_fromBlocks_zero₂₁`) — nonzero — hence the minor has linearly independent rows, rank
`#m₁ + #m₂`, and `rank ≤ (fromBlocks A B 0 D).rank` by `rank_submatrix_le`.

In the KT application `A = Mᵢ` is the full-rank `D × D` corner block and `D` is the IH's
bottom-block `R(G₁ ＼ row, q₁)` (both full row rank), so the LI-rows hypotheses are exactly what
the realization arm supplies. -/
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

/-- **Block-triangular rank lower bound through a unit-det column operation** (Katoh–Tanigawa 2011
eqs. (6.61)→(6.64); Phase 23d route-A piece A4, the column-op bridge into A3). For a matrix `M`
over a field, a *unit-determinant* square matrix `U` (the explicit invertible column operation —
KT (6.61)'s "add `vᵢ`'s columns to `vᵢ₊₁`'s"), and reindexing equivalences `em`, `en` exhibiting
`M * U` (after the column op) in the block-triangular shape `fromBlocks A B 0 D` with the rows of
both diagonal blocks `A`, `D` linearly independent, the rank of the *original* `M` is at least the
sum of the two diagonal-block row counts:
`#m₁ + #m₂ ≤ M.rank`.

This is the matrix-level realization of KT's "(6.61) submatrix containment is not difficult to
see": where the dual-space chain cert was forced to read (6.61) as a *span membership* (which
walled — `notes/Phase23-design.md` §(4.18)–(4.30)), the literal-`Matrix` model reads it as a
*right-multiply by a unit-det column-operation matrix* (`Matrix.rank_mul_eq_left_of_isUnit_det`,
rank-invariant) followed by a *structural reindexing* into `fromBlocks` — never a membership, so
the override-meets-gate collision never arises. The proof is a single `calc`: A3
(`rank_fromBlocks_zero₂₁_ge_of_linearIndependent_rows`) bounds `rank (fromBlocks A B 0 D)` below
by `#m₁ + #m₂`, then `rank_reindex` (the reindexing is rank-preserving) and
`rank_mul_eq_left_of_isUnit_det` (the column op is rank-preserving) carry that bound back to
`M.rank`.

In the KT application `M = R(G,pᵢ)` (the concrete panel-hinge rigidity matrix), `U` is the (6.61)
column-operation matrix, `A = Mᵢ` is the full-rank `D × D` corner block, and `D` is the IH's
bottom-block `R(G₁ ＼ row, q₁)` — both with linearly independent rows — so the hypotheses are
exactly what the realization arm supplies. The rigidity-matrix consumer is
`BodyHingeFramework.rigidityMatrix_mul_rank` (`Molecular/RigidityMatrix/Concrete.lean`), the
column-op rank-invariance specialized to `R(G,p)`. -/
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
  haveI : Fintype p := Fintype.ofFinite p
  haveI : Fintype n₁ := Fintype.ofFinite n₁
  haveI : Fintype n₂ := Fintype.ofFinite n₂
  calc Fintype.card m₁ + Fintype.card m₂
      ≤ (fromBlocks A B 0 D).rank :=
        rank_fromBlocks_zero₂₁_ge_of_linearIndependent_rows B hA hD
    _ = ((M * U).reindex em en).rank := by rw [hblock]
    _ = (M * U).rank := rank_reindex em en (M * U)
    _ = M.rank := rank_mul_eq_left_of_isUnit_det U M hU

/-- **Block-triangular rank lower bound through a unit-det column operation — row-submatrix form**
(Katoh–Tanigawa 2011 eqs. (6.61)→(6.64); Phase 23d route-A piece A4 in its row-*submatrix* shape,
option (4b′)). This is the row-injection generalization of
`rank_ge_of_isUnit_mul_reindex_fromBlocks`: instead of a row *equivalence* `em : p ≃ m₁ ⊕ m₂`
exhibiting the *whole* column-operated matrix `M * U` as `fromBlocks A B 0 D`, it takes an arbitrary
row map `re : m₁ ⊕ m₂ → p` (an *injection* in the application — selecting a row subset) and a column
equivalence `en : (n₁ ⊕ n₂) ≃ q`, exhibiting the *row submatrix* `(M * U).submatrix re en` in the
block-triangular shape, with the rows of both diagonal blocks `A`, `D` linearly independent. The
conclusion is the same lower bound `#m₁ + #m₂ ≤ M.rank`.

The motivation for the row-submatrix shape over the total-bijection `reindex` shape is that the
realization arm is *isostatic* (`(D−1)·|E(G)| = D·(|V(G)|−1)`), so a total row bijection of all edge
rows would force the *whole* edge matrix to be full row rank at the degenerate `t = 0` shear — which
is **false**: there are `D − 2` surplus rows incident to the re-inserted body that become dependent
(the redundancy KT Claim 6.11 exploits). KT's (6.64) block-additivity is a *subspace* statement that
ignores those surplus rows, so the certificate must select a row subset — the `D` corner rows plus
the `D·(|V_Gv|−1)` IH-bottom rows — and drop the surplus (`notes/Phase23-design.md` §I.8.24(4.33)).
This mirrors `rank_fromBlocks_zero₂₁_ge_of_linearIndependent_rows`'s *column*-submatrix step
(`N = M.submatrix id c`): both keep only the rows/columns the block-triangular minor needs.

The proof is the same `calc` as the `reindex` form, with `Matrix.rank_submatrix_le` (a row submatrix
can only drop the rank) in place of the rank-preserving `rank_reindex`. -/
theorem rank_ge_of_isUnit_mul_submatrix_fromBlocks
    {K p q m₁ m₂ n₁ n₂ : Type*} [Field K] [Finite p] [Fintype q] [DecidableEq q]
    [Fintype m₁] [Fintype m₂] [Finite n₁] [Finite n₂]
    (M : Matrix p q K) (U : Matrix q q K) (hU : IsUnit U.det)
    (re : m₁ ⊕ m₂ → p) (en : (n₁ ⊕ n₂) ≃ q)
    {A : Matrix m₁ n₁ K} {B : Matrix m₁ n₂ K} {D : Matrix m₂ n₂ K}
    (hblock : (M * U).submatrix re en = fromBlocks A B 0 D)
    (hA : LinearIndependent K A.row) (hD : LinearIndependent K D.row) :
    Fintype.card m₁ + Fintype.card m₂ ≤ M.rank := by
  classical
  haveI : Fintype n₁ := Fintype.ofFinite n₁
  haveI : Fintype n₂ := Fintype.ofFinite n₂
  calc Fintype.card m₁ + Fintype.card m₂
      ≤ (fromBlocks A B 0 D).rank :=
        rank_fromBlocks_zero₂₁_ge_of_linearIndependent_rows B hA hD
    _ = ((M * U).submatrix re en).rank := by rw [hblock]
    _ ≤ (M * U).rank := rank_submatrix_le (M * U) re en
    _ = M.rank := rank_mul_eq_left_of_isUnit_det U M hU

/-- **Block-triangular rank additivity, upper-right-zero (A3-transposed) form** (Katoh–Tanigawa 2011
eq. (6.64); Phase 23e route, the A3-transposed cert leaf). For a block-triangular matrix
`fromBlocks A 0 C D` over a field (*upper-right* block zero, the transpose of
`rank_fromBlocks_zero₂₁_ge_of_linearIndependent_rows`'s lower-left-zero shape), if the rows of the
diagonal blocks `A` and `D` are each linearly independent, then the rank of the whole matrix is at
least the sum of the two diagonal-block row counts:
`#m₁ + #m₂ ≤ (fromBlocks A 0 C D).rank`.

The proof is the trivial mirror of `rank_fromBlocks_zero₂₁_ge_of_linearIndependent_rows`, swapping
`Matrix.det_fromBlocks_zero₂₁ → Matrix.det_fromBlocks_zero₁₂` for the combined block-triangular
minor's determinant: `A`'s LI rows give a full-rank square minor (columns `e₁`), `D`'s give another
(`e₂`), the combined `(m₁ ⊕ m₂)`-square minor of `fromBlocks A 0 C D` over those columns is
upper-triangular, so its determinant is the product of the two minor dets (nonzero) and the minor
has rank `#m₁ + #m₂ ≤ (fromBlocks A 0 C D).rank` by `rank_submatrix_le`.

This is the cert shape Phase 23e adopts (`notes/Phase23-design.md` §(4.49)): the zero *upper-right*
block is produced by a row op zeroing the corner's off-`v` content `B` (leaving the bottom `[C D]`
untouched as the landed full-rank `mixedBottom` block), so `A = A'` is the row-op'd `Mᵢ` corner and
`[C D]` is the IH bottom block — both full row rank. -/
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

/-- **Block-triangular rank lower bound through a unit-det row *and* column operation —
upper-right-zero (A3-transposed), row-submatrix form** (Katoh–Tanigawa 2011 eqs. (6.61)→(6.64);
Phase 23e route, the A3-transposed A4 leaf with the threaded LEFT row op). The `fromBlocks A 0 C D`
(upper-right zero) analogue of `rank_ge_of_isUnit_mul_submatrix_fromBlocks`, additionally threading
a *unit-determinant* LEFT factor `Lrow` (the block elementary row op zeroing the corner's off-`v`
content, `rowOp_isUnit_det`/`rowOp_zeroes_upperRight`): for a matrix `M` over a field, a unit-det
square row op `Lrow : Matrix p p K`, a unit-det square column op `U : Matrix q q K`, a row injection
`re : m₁ ⊕ m₂ → p` and a column equivalence `en : (n₁ ⊕ n₂) ≃ q` exhibiting the row submatrix
`(Lrow * M * U).submatrix re en` in the block-triangular shape `fromBlocks A 0 C D` with the rows of
both diagonal blocks `A`, `D` linearly independent, the rank of the original `M` is at least the sum
of the two diagonal-block row counts: `#m₁ + #m₂ ≤ M.rank`.

The LEFT factor is needed because the cert's `hblock` is producible only after a row op zeros the
upper-right block (the column op alone gives the *lower*-left-zero shape; `notes/Phase23-design.md`
§(4.53)). The proof extends the `calc` of the column-op-only version by *two* rank-invariance
rewrites: `rank_mul_eq_left_of_isUnit_det` carries the column op `U` back, then
`rank_mul_eq_right_of_isUnit_det` carries the row op `Lrow` back — both unit-det multiplies preserve
rank. In the Phase 23e application `A = A' = A − L₀C` is the row-op'd full-rank `D × D` corner block
(`Mᵢ`, the `e_a` panel rows + the adjusted `±r` corner row) and `[C D]` is the IH's full-rank
`mixedBottom` block (`R(Gab, q₁)`, untouched by the row op), so the LI-rows hypotheses are exactly
what the realization arm supplies (`notes/Phase23-design.md` §(4.49)–(4.53)). -/
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
  haveI : Fintype n₁ := Fintype.ofFinite n₁
  haveI : Fintype n₂ := Fintype.ofFinite n₂
  calc Fintype.card m₁ + Fintype.card m₂
      ≤ (fromBlocks A 0 C D).rank :=
        rank_fromBlocks_zero₁₂_ge_of_linearIndependent_rows C hA hD
    _ = ((Lrow * M * U).submatrix re en).rank := by rw [hblock]
    _ ≤ (Lrow * M * U).rank := rank_submatrix_le (Lrow * M * U) re en
    _ = (Lrow * M).rank := rank_mul_eq_left_of_isUnit_det U (Lrow * M) hU
    _ = M.rank := rank_mul_eq_right_of_isUnit_det Lrow M hLrow

/-- **The block elementary row operation `[1, -L₀; 0, 1]` has unit determinant** (Katoh–Tanigawa
2011 eq. (6.63); Phase 23e route, the row-op factor's invertibility). The block-upper-triangular
matrix subtracting `L₀ ·` (the lower `m₂`-row block) from the upper `m₁`-row block is unimodular:
its determinant is `det 1 · det 1 = 1` (via `Matrix.det_fromBlocks_zero₂₁`), hence a unit. This is
the unit-det `Lrow` left factor the A3-transposed cert threads to zero the corner's off-`v` block
without changing the rank (`notes/Phase23-design.md` §(4.53), LEAF-RowOp-1). -/
theorem rowOp_isUnit_det {K m₁ m₂ : Type*} [Field K] [Fintype m₁] [Fintype m₂] [DecidableEq m₁]
    [DecidableEq m₂] (L₀ : Matrix m₁ m₂ K) :
    IsUnit (Matrix.fromBlocks (1 : Matrix m₁ m₁ K) (-L₀) 0 (1 : Matrix m₂ m₂ K)).det := by
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_one, mul_one]
  exact isUnit_one

/-- **The block elementary row operation zeros the upper-right block** (Katoh–Tanigawa 2011 eq.
(6.63); Phase 23e route, the row-op action). Left-multiplying a block matrix `fromBlocks A B C D` by
`[1, -L₀; 0, 1]` subtracts `L₀ ·` the lower row block from the upper one: the new top-left is
`A − L₀ C` and the new top-right is `B − L₀ D`, which is `0` exactly when `B = L₀ D` (`hB`); the
lower blocks `C`, `D` are untouched. Pure `Matrix.fromBlocks_multiply` + `hB` arithmetic. In the
Phase 23e application `B` is the corner's off-`v` `ab`-fill, `D` is the (full-rank) `mixedBottom`
bottom block, and `L₀` is the `cGv`-weighted combination realizing `B = L₀ D`, so the row op zeros
the corner's upper-right block leaving the bottom untouched — the cert's `fromBlocks A' 0 C D` shape
(`notes/Phase23-design.md` §(4.53), LEAF-RowOp-2). -/
theorem rowOp_zeroes_upperRight {K m₁ m₂ n₁ n₂ : Type*} [Field K] [Fintype m₁] [Fintype m₂]
    [DecidableEq m₁] [DecidableEq m₂]
    {A : Matrix m₁ n₁ K} {B : Matrix m₁ n₂ K} {C : Matrix m₂ n₁ K} {D : Matrix m₂ n₂ K}
    (L₀ : Matrix m₁ m₂ K) (hB : B = L₀ * D) :
    Matrix.fromBlocks (1 : Matrix m₁ m₁ K) (-L₀) 0 (1 : Matrix m₂ m₂ K) * Matrix.fromBlocks A B C D
      = Matrix.fromBlocks (A - L₀ * C) 0 C D := by
  rw [Matrix.fromBlocks_multiply, hB]
  simp [sub_eq_add_neg]

/-- **A matrix whose every row is a fixed-weight linear combination of another matrix's rows
factors as `L₀ * D`** (Phase 23e route, the `B = L₀ * D` matrix-conversion the row op
`rowOp_zeroes_upperRight` consumes; Katoh–Tanigawa 2011 eq. (6.63)/(6.66)). Given
`D : Matrix m₂ n K` and a weight family `w : m₁ → m₂ → K` such that each row `B i` is the
`w i`-weighted combination of
`D`'s rows (`hcomb : ∀ i j, B i j = ∑ i', w i i' * D i' j`), then `B = Matrix.of w * D`. This is the
matrix-algebra step that turns a *per-row* linear-combination hypothesis — the form the Case-III
`cGv` widening produces (`hingeRow a b ρ = ∑ⱼ cGv j • hingeRow (uvGv j) (vvGv j) (rvGv j)`, KT eq.
(6.66), each summand a bottom `Gv`-row) — into the matrix product `B = L₀ * D` that the block
elementary row op `[1, -L₀; 0, 1]` needs to zero the corner's off-`v` upper-right block. Immediate
from `Matrix.mul_apply` and `Matrix.ext`: the row op factor is `L₀ := Matrix.of w`. The bottom-row
index `m₂` is the cert's `mixedBottom` rows; the weight `w i i'` selects the `cGv`-coefficient of
the `i'`-th bottom row in the `i`-th corner row's expansion (zero on the rows the corner row doesn't
use). NO rank argument; this is pure matrix arithmetic, separable from the arm's `re`/`m₂`
construction. -/
theorem of_eq_mul_of_row_comb {K m₁ m₂ n : Type*} [Fintype m₂] [CommRing K]
    (B : Matrix m₁ n K) (D : Matrix m₂ n K) (w : m₁ → m₂ → K)
    (hcomb : ∀ i j, B i j = ∑ i', w i i' * D i' j) :
    B = Matrix.of w * D := by
  ext i j
  rw [Matrix.mul_apply, hcomb]
  rfl

/-- **The block elementary row op `[1, -L₀; 0, 1]` lifts along a strict row INJECTION to a unit-det
row op on the full index, leaving the off-image rows fixed** (Katoh–Tanigawa 2011 eq. (6.63); Phase
23f route, the strict-injection unit-det / rank-invariance bridge, geometry leaf **B1**). The
A3-transposed cert (`rank_ge_of_isUnit_mul_submatrix_fromBlocks_zero₁₂`) threads a unit-det LEFT row
op `Lrow : Matrix p p K` over the *full* row index `p`, but the `m₁ ⊕ m₂` block elementary matrix
`[1, -L₀; 0, 1]` acts only on the rows the injection `re : m₁ ⊕ m₂ → p` selects. For the general
Case-III arm `re` is a **strict** injection — `card m₁ + card m₂ = D(|V|−1) ≤ (D−1)|E| = card p` is
an inequality, not forced equality (`notes/Phase23-design.md` §(4.55)), so no bijection
`(m₁ ⊕ m₂) ≃ p` exists and a row op carried by such a bijection (`Matrix.reindex e e`, needing one)
does NOT serve. This lemma replaces the missing bijection with the **extended** equivalence
`e' : (m₁ ⊕ m₂) ⊕ ↥(Set.range re)ᶜ ≃ p` (`Equiv.ofInjective re` onto `range re`, then
`Equiv.Set.sumCompl`), carries the row op as the block-diagonal `Lrow := reindex e' e' (fromBlocks
[1, -L₀; 0, 1] 0 0 1)` (the op on the `re`-image block, identity on the off-image complement), and
re-selects the `re`-image block back out.

It produces the facts the wrapper / leaf B2 need: `IsUnit Lrow.det` (via `det_reindex_self` +
`det_fromBlocks_zero₂₁` reducing the block-diagonal to the inner block, then the landed
`rowOp_isUnit_det` for `[1, -L₀; 0, 1]`), `Lrow.submatrix re re = [1, -L₀; 0, 1]` (since
`re = ⇑e' ∘ Sum.inl` the double relabelling cancels to `toBlocks₁₁ (fromBlocks …)`), **and** the
off-image vanishing `Lrow (re i) x = 0` for `x ∉ range re` (the image rows touch only image columns,
because `Bext`'s upper-right block is `0`) — the structural fact leaf B2 uses to split the matrix
product through the injection without an `Equiv`. The cert derives rank invariance
`(Lrow * M).rank = M.rank` itself from `IsUnit Lrow.det` (`rank_mul_eq_right_of_isUnit_det`), so B1
need not export it.
Carrier/field-agnostic; the `m₁`/`m₂`
indices carry `[Finite]` (only `p` is type-relevant, `Fintype.ofFinite` recovers the proof-side
instances) — the project's standing `unusedFintypeInType` fix. Separable from the arm's `re`/`L₀`
construction (`notes/Phase23-design.md` §(4.55), `notes/Phase23f.md` leaf B1). -/
theorem exists_rowOp_of_strictInjection {K p m₁ m₂ : Type*} [Field K] [Fintype p] [DecidableEq p]
    [Finite m₁] [Finite m₂] [DecidableEq m₁] [DecidableEq m₂]
    {re : m₁ ⊕ m₂ → p} (hre : Function.Injective re) (L₀ : Matrix m₁ m₂ K) :
    ∃ Lrow : Matrix p p K, IsUnit Lrow.det ∧
      Lrow.submatrix re re =
        Matrix.fromBlocks (1 : Matrix m₁ m₁ K) (-L₀) 0 (1 : Matrix m₂ m₂ K) ∧
      (∀ (i : m₁ ⊕ m₂) (x : p), x ∉ Set.range re → Lrow (re i) x = 0) := by
  classical
  haveI : Fintype m₁ := Fintype.ofFinite m₁
  haveI : Fintype m₂ := Fintype.ofFinite m₂
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

/-- **The strict-injection row op zeros the upper-right block of a row-selected column matrix**
(Katoh–Tanigawa 2011 eq. (6.63)/(6.66); Phase 23f, the strict-injection `hblock` reducer, geometry
leaf **B2**). The `_zero₁₂` reducer for the strict-injection `Lrow` that leaf **B1**
(`exists_rowOp_of_strictInjection`) builds. The bijection variant splits the product through a
middle **bijection** `e : (m₁ ⊕ m₂) ≃ p` (`submatrix_mul_equiv`); for the general Case-III arm `re`
is a
**strict** injection (`card m₁ + card m₂ ≤ card p`, an inequality — `notes/Phase23-design.md`
§(4.55)), so no such `e` exists. Instead B2 consumes B1's two structural facts about `Lrow` — the
selected block `hLsub : Lrow.submatrix re re = [1, -L₀; 0, 1]` and the off-image vanishing
`hzero : ∀ i x, x ∉ range re → Lrow (re i) x = 0` — and splits the matrix product *entrywise* by
`Fintype.sum_of_injective`: the contracted sum `∑ x : p, Lrow (re i) x * M' x (en j)` drops to
`∑ k : m₁ ⊕ m₂, [1, -L₀; 0, 1] i k * (M'.submatrix re en) k j` (the off-image columns vanish by
`hzero`; the image columns reindex by `re` with `Lrow (re i) (re k) = [1, -L₀; 0, 1] i k` from
`hLsub`), i.e. `(Lrow * M').submatrix re en = [1, -L₀; 0, 1] * M'.submatrix re en`. Then `hM' : =
fromBlocks A B C D` and leaf (i)'s `hB : B = L₀ * D` close it via `rowOp_zeroes_upperRight`.

Subsumes the bijection special case (when `re` is bijective the off-image set
is empty and the `Fintype.sum_of_injective` reindex is the `submatrix_mul_equiv` split). Carrier/
field-agnostic; separable from the arm's `re`/`L₀`/`en` construction (`notes/Phase23-design.md`
§(4.55), `notes/Phase23f.md` leaf B2). -/
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
  haveI : Fintype m₁ := Fintype.ofFinite m₁
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
`N.submatrix id Sum.inr` are. The all-zero left columns carry no information: each `N.row i` is the
zero-extension `Sum.elim 0 (right row)` of the corresponding submatrix row, and the zero-extension
linear map `Sum.elimZeroLeft : (n₂ → R) →ₗ[R] (n₁ ⊕ n₂ → R)` is injective (its kernel is `⊥`), so it
preserves and reflects linear independence (`LinearMap.linearIndependent_iff`).

Phase 23d `R(Gab)`-bottom reshape, the **L-hD** support lemma: the (6.64) bottom block `toBlocks₂₂`
drops the re-inserted body `v`'s `D` columns from the full product-column matrix, and every bottom
row reads zero on body `v` (its support extensor lives off `v` after the column op), so its row-LI
is unchanged by the column restriction. -/
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

Phase 23d `R(Gab)`-bottom reshape, the **L-rank** support lemma: it carries the full product-column
rank (where `Matrix.rank_of_coordEquiv` computes the row-functional span finrank) down to the
column-restricted (6.64) bottom block `toBlocks₂₂`, whose dropped body-`v` columns are zero. -/
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
  haveI : Fintype ι := Fintype.ofFinite ι
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
  rw [Set.mem_setOf_eq] at ht ⊢
  rwa [← h_iff]

/-- **Rank lower semicontinuity along an affine path.** For a finite-dim `W`-vector space over a
field `K` and an affine vector family `t ↦ fun i => a i + t • b i : K → ι → W` (with `ι` finite),
if the subfamily indexed by a subset `s : Set ι` is linearly independent at some `t₀ : K`, then
for all but finitely many `t : K` the span of the *full* family at `t` has `finrank` at least
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
generic-rank lower bound of `prop:rigidity-matrix-prop11`. No infiniteness or characteristic
hypothesis on `K` is needed. -/
theorem LinearIndependent.le_finrank_span_along_affine_path_cofinite
    {K ι W : Type*} [Field K] [Finite ι] [AddCommGroup W] [Module K W] [Module.Finite K W]
    {a b : ι → W} {t₀ : K} {s : Set ι}
    (h : LinearIndependent K (fun i : s => a i + t₀ • b i)) :
    {t : K | Module.finrank K (Submodule.span K
      (Set.range (fun i => a i + t • b i))) < Nat.card s}.Finite := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  haveI : Fintype s := Fintype.ofFinite s
  refine (LinearIndependent.finite_setOf_not_along_affine_path
    (a := fun i : s => a i) (b := fun i : s => b i) (t₀ := t₀) h).subset (fun t ht => ?_)
  rw [Set.mem_setOf_eq] at ht ⊢
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

This is the exact shape the Phase-21b genericity device feeds its consumers: each carries an
*upper* bound on a null-space dimension (`dim Z(G,p) ≤ …`, the codimension/rank-nullity reading
of `rank R(G,p) ≥ …`), so the span-form `le_finrank_span_along_affine_path_cofinite` is dualized
here once. The span and its coannihilator have complementary dimension at *every* `t`
(`Subspace.finrank_add_finrank_dualAnnihilator_eq` + `Subspace.finrank_dualCoannihilator_eq`:
`finrank coann + finrank span = finrank (Dual K V) = finrank V`), so "span finrank ≥ #s
cofinitely" turns into "coann finrank ≤ finrank V − #s cofinitely" verbatim. The conclusion is
stated in the additive form `finrank V < #s + finrank coann` to sidestep `ℕ`-subtraction. No
infiniteness or characteristic hypothesis on `K` is needed. -/
theorem LinearIndependent.finrank_dualCoannihilator_along_affine_path_cofinite
    {K ι V : Type*} [Field K] [Finite ι] [AddCommGroup V] [Module K V] [Module.Finite K V]
    {a b : ι → Module.Dual K V} {t₀ : K} {s : Set ι}
    (h : LinearIndependent K (fun i : s => a i + t₀ • b i)) :
    {t : K | Module.finrank K V < Nat.card s + Module.finrank K
      (Submodule.span K (Set.range (fun i => a i + t • b i))).dualCoannihilator}.Finite := by
  classical
  refine (h.le_finrank_span_along_affine_path_cofinite (a := a) (b := b)).subset (fun t ht => ?_)
  rw [Set.mem_setOf_eq] at ht ⊢
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
all of `σ → K` and a *single* good point is produced (`∃ p`, not a cofinite set), via the matrix
brick `Matrix.exists_linearIndependent_rows_specialize` — the site `[Infinite K]` enters this decl
from. The subfamily on `s` is LI at the produced `p`, forcing the full span's `finrank ≥ #s`
(`finrank_span_eq_card` + `Submodule.finrank_mono`). This is the analytic core of the Phase-21b
genericity device (Katoh–Tanigawa 2011 Claim 6.4/6.9): the panel-hinge rigidity-matrix entries are
degree-two polynomials in the panel coordinates, so a single realization at the target rank lifts
to a *generic* realization at *at least* that rank. -/
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
  haveI : Fintype s := Fintype.ofFinite s
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
  -- Produce a good point from the matrix brick.
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

This is the exact shape the Phase-21b genericity device feeds its consumers: each carries an
*upper* bound on a null-space dimension (`dim Z(G,p) ≤ …`, the codimension/rank-nullity reading of
`rank R(G,p) ≥ …`), so the span-form `exists_le_finrank_span_polynomial` is dualized here once
(inheriting its `[Infinite K]`). The span and its coannihilator have complementary dimension
(`Subspace.finrank_add_finrank_dualAnnihilator_eq` + `Subspace.finrank_dualCoannihilator_eq`:
`finrank coann + finrank span = finrank (Dual K V) = finrank V`), so "span finrank ≥ #s at the
produced `p`" turns into "coann finrank ≤ finrank V − #s" verbatim. The conclusion is stated
additively (`#s + finrank coann ≤ finrank V`) to sidestep `ℕ`-subtraction — the same shape as
`LinearIndependent.finrank_dualCoannihilator_along_affine_path_cofinite`, but as `∃ p` rather than
`{bad}.Finite`. -/
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
`Q := det (P.submatrix on a maximal column selection)` is exposed instead, so several legs'
polynomials can be **multiplied** and the funext step (`MvPolynomial.exists_eval_ne_zero`) applied
to the product once elsewhere, producing one shared non-vanishing point at which *all* legs are
independent — this decl itself never picks a point, so it needs no infiniteness or characteristic
hypothesis on `K`. `Q` is built by selecting, via
`exists_submatrix_det_ne_zero_of_linearIndependent_rows`, a square column subset `e` of the
polynomial-entry submatrix `P : Matrix s (Fin (finrank K W)) (MvPolynomial σ K)` whose specialized
minor at `p₀` is nonsingular; `eval p Q` is then the specialized minor's determinant
(`(eval p).map_det`), so `eval p₀ Q ≠ 0` by construction and
`linearIndependent_rows_of_specialized_submatrix_det_ne_zero` upgrades any other non-root `p` back
to row independence. The LI of vectors ↔ LI of `φ`-coordinate rows is the same `φ`-pullback used in
`exists_le_finrank_span_polynomial`. This is the per-leg "rigid locus ⟹ nonzero rank polynomial"
brick the Phase-22 Case-I seed witness-transfer couples across its two legs (Katoh–Tanigawa 2011
§6.2, eq. (6.6)). -/
theorem exists_polynomial_ne_zero_of_linearIndependent_at
    {K ι W σ : Type*} [Field K] [Finite ι] [AddCommGroup W] [Module K W] [Module.Finite K W]
    (g : (σ → K) → ι → W) (c : ι → Fin (Module.finrank K W) → MvPolynomial σ K)
    (φ : W ≃ₗ[K] (Fin (Module.finrank K W) → K))
    (hg : ∀ p i j, φ (g p i) j = MvPolynomial.eval p (c i j))
    {p₀ : σ → K} {s : Set ι}
    (h : LinearIndependent K (fun i : s => g p₀ i)) :
    ∃ Q : MvPolynomial σ K, MvPolynomial.eval p₀ Q ≠ 0 ∧
      ∀ p : σ → K, MvPolynomial.eval p Q ≠ 0 → LinearIndependent K (fun i : s => g p i) := by
  classical
  haveI : Fintype s := Fintype.ofFinite s
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
    rw [heval p₀]; convert he using 2
  · -- At any non-root `p`, the specialized minor is nonsingular, so the rows are LI.
    rw [hiff p]
    refine Matrix.linearIndependent_rows_of_specialized_submatrix_det_ne_zero
      (P.map (MvPolynomial.eval p)).row (RingHom.id K) e ?_
    rw [RingHom.id_apply, ← heval p]
    exact hp

/-- **`exists_polynomial_ne_zero_of_linearIndependent_at`, basis-flexible column-index form**
(Phase 34 PROSPECT G3, the abundance-lemma helper). The reindexing companion of
`exists_polynomial_ne_zero_of_linearIndependent_at`, matching the
`exists_good_realization`/`exists_good_realization_reindex` pair above: it accepts the coordinate
identification `φ` against an *arbitrary* finite basis index `ν` (with the cardinality bridge
`e : Fin (finrank K W) ≃ ν`) rather than forcing the canonical `Fin (finrank K W)` literally, since
a concrete basis (e.g. `b.dualBasis.equivFun` for a project-supplied basis `b`) is indexed by
whatever type `b` itself is indexed by, not by `Fin (finrank K W)` up to defeq. Reduces to the base
lemma by precomposing `φ` with the index reindexing `LinearEquiv.funCongrLeft K K e` and pulling `c`
back along `e`, exactly as `exists_good_realization_reindex` does. -/
theorem exists_polynomial_ne_zero_of_linearIndependent_at_reindex
    {K ι W σ ν : Type*} [Field K] [Finite ι] [AddCommGroup W] [Module K W] [Module.Finite K W]
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
choose a preimage matrix `M₀ : Matrix n n R` (`M = M₀.map f`) and apply `RingHom.map_det`. A general
`Matrix`-namespaced subring-closure fact (mirrored, `notes/FRICTION.md`); no live consumer in this
project as of the Phase 30 RELAX slice (e) sweep. Its former use was a rationality refinement of
`exists_polynomial_ne_zero_of_linearIndependent_at`, certifying the witnessing polynomial rational
under a rationality hypothesis on the coordinate family — deleted in that sweep once the
hypothesis's own consumer (KT's footnote-6 algebraically-independent-seed transfer) was retired
(Phase 30 RELAX slice (d)), leaving the refinement an exact duplicate of the plain engine. -/
theorem Matrix.det_mem_range_of_entries {R S : Type*} [CommRing R] [CommRing S] {n : Type*}
    [Fintype n] [DecidableEq n] (f : R →+* S) (M : Matrix n n S)
    (hM : ∀ i j, M i j ∈ f.range) : M.det ∈ f.range := by
  classical
  choose M₀ hM₀ using hM
  refine ⟨(Matrix.of M₀).det, ?_⟩
  rw [RingHom.map_det]
  exact congrArg Matrix.det (Matrix.ext fun i j => hM₀ i j)

/-- **One-variable rank transfer along a polynomial-coordinate family** (Phase-22h leaf B, the
KT-Lemma-5.2 transfer brick — Katoh–Tanigawa 2011 pp. 668–669: each minor of `R(G, p_t)` is
continuous in `t`). For a basis `b : Basis κ K M` over an infinite field `K` (with `κ` finite) and
a family `g : K → ι → M` (with `ι` finite) whose basis coordinates are *univariate-polynomial
evaluations* — a fixed `P : ι → κ → Polynomial K` with `b.repr (g t i) j = (P i j).eval t` — if the
family `g 0` is linearly independent at `t = 0`, then there is a `t` avoiding any prescribed finite
bad set and nonzero (`t ∉ bad`, `t ≠ 0`) at which `g t` is again linearly independent.

The basis-free, graph-free shape the molecular Case-III realization (KT §6.4.1) consumes: the
`t = 0` hinge-level family is certified independent, then transferred along the one-parameter shear,
the bad `t` intersected with the good-`t` set of `exists_shear_linearIndependent_pair`. The proof
pulls `g t` back along `φ := b.equivFun : M ≃ₗ[K] (κ → K)` (so `φ (g t i) j = b.repr (g t i) j =
(P i j).eval t`, i.e. `φ ∘ g t` is the row family of `(Matrix.of P).map (evalRingHom t)`); LI
transfers across `φ` (`LinearMap.linearIndependent_iff`), so
`finite_setOf_not_linearIndependent_rows_of_polynomial` makes the dependent-`t` set finite (needing
no infiniteness itself), and `K`'s infinitude (`[Infinite K]` — the second point-extractor
`Set.Finite.infinite_compl` needs, alongside `Matrix.exists_linearIndependent_rows_specialize`'s
`MvPolynomial.exists_eval_ne_zero` site) supplies a `t` outside that set together with the finite
`bad ∪ {0}`. -/
theorem LinearIndependent.exists_notMem_of_polynomial_repr
    {K ι κ M : Type*} [Field K] [Infinite K] [Finite ι] [Finite κ] [AddCommGroup M] [Module K M]
    (b : Module.Basis κ K M) (g : K → ι → M) (P : ι → κ → Polynomial K)
    (hg : ∀ t i j, b.repr (g t i) j = (P i j).eval t)
    (h0 : LinearIndependent K (g 0)) (bad : Finset K) :
    ∃ t : K, t ∉ bad ∧ t ≠ 0 ∧ LinearIndependent K (g t) := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  haveI : Fintype κ := Fintype.ofFinite κ
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
    rw [Set.mem_setOf_eq] at ht ⊢
    rwa [hiff] at ht
  -- `K` is infinite, so there is a `t` outside the finite union of bad sets.
  have hbad : ({t : K | ¬ LinearIndependent K (g t)}
      ∪ ((bad : Set K) ∪ {0})).Finite :=
    hfin.union (bad.finite_toSet.union (Set.finite_singleton 0))
  obtain ⟨t, ht⟩ := hbad.infinite_compl.nonempty
  rw [Set.mem_compl_iff, Set.mem_union, Set.mem_union, Set.mem_setOf_eq, not_or, not_or,
    not_not, Finset.mem_coe, Set.mem_singleton_iff] at ht
  exact ⟨t, ht.2.1, ht.2.2, ht.1⟩

