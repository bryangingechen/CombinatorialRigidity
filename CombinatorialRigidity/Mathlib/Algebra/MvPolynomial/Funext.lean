/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Upstream candidate: a nonzero multivariate polynomial has a non-vanishing point

`Mathlib.Algebra.MvPolynomial.Funext` proves `MvPolynomial.funext`: over an infinite integral
domain, two multivariate polynomials that agree on every point are equal. Its immediate
contrapositive — *a nonzero `MvPolynomial` over an infinite integral domain has a point where its
evaluation is nonzero* — is the multivariate analogue of `Polynomial.exists_eval_ne_zero_of_…`
but is not packaged in mathlib as a standalone lemma.

This `MvPolynomial.exists_eval_ne_zero` is the foundational brick of the Phase-21b genericity
device (Katoh–Tanigawa 2011 Claim 6.4/6.9): the panel-hinge rigidity matrix `R(G,p)` has entries
that are polynomials in the panel coordinates `p`, so a Gram-determinant minor that is nonzero at
one realization is a *nonzero* `MvPolynomial`, hence non-vanishing at a generic `p` — the "generic
point attains the maximum rank" mechanism. It feeds the matrix/vector specialization lemmas in
`Mathlib/LinearAlgebra/Matrix/Rank.lean`.

Mirror path: `Mathlib/Algebra/MvPolynomial/Funext.lean`. Promotion to mathlib is a copy-paste into
the upstream `Funext` file, directly below `MvPolynomial.funext`.
-/

@[expose] public section

namespace MvPolynomial

variable {R : Type*} [CommRing R] [IsDomain R] [Infinite R] {σ : Type*}

/-- **A nonzero multivariate polynomial has a non-vanishing point.** Over an infinite integral
domain `R`, a nonzero `p : MvPolynomial σ R` evaluates to a nonzero value at some point
`x : σ → R`. This is the contrapositive of `MvPolynomial.funext` (if `p` vanished everywhere it
would agree with the zero polynomial at every point, hence equal `0`). -/
theorem exists_eval_ne_zero {p : MvPolynomial σ R} (hp : p ≠ 0) :
    ∃ x : σ → R, MvPolynomial.eval x p ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  exact hp (MvPolynomial.funext fun x => by rw [h x, map_zero])

/-- **Simultaneous non-vanishing point for a finite family.** Over an infinite integral domain
`R`, if each of finitely many multivariate polynomials `p i : MvPolynomial σ R` is nonzero, there
is a single point `x : σ → R` at which *every* `p i` evaluates to a nonzero value.

Proof: the product `∏ i, p i` is nonzero because `R` is a domain, so `exists_eval_ne_zero` supplies
a common non-root, and `map_prod` factors the evaluation of the product.

This is the "pick a common non-root of finitely many nonzero polynomials" combinator underlying the
genericity-device seed shots (Katoh–Tanigawa 2011): it turns the per-factor nonzero hypotheses
directly into per-factor `eval ≠ 0` facts at one seed, replacing the hand-written
`mul_ne_zero` + `map_mul` + `ring` chains. The fixed-arity forms `exists_eval_ne_zero₂/₃/₄` below
are the ergonomic wrappers for the small arities that occur in practice. -/
theorem exists_eval_ne_zero_of_forall_ne_zero {ι : Type*} [Finite ι]
    (p : ι → MvPolynomial σ R) (hp : ∀ i, p i ≠ 0) :
    ∃ x : σ → R, ∀ i, MvPolynomial.eval x (p i) ≠ 0 := by
  have := Fintype.ofFinite ι
  obtain ⟨x, hx⟩ :=
    exists_eval_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => hp i : ∏ i, p i ≠ 0)
  rw [map_prod] at hx
  exact ⟨x, fun i h => hx (Finset.prod_eq_zero (Finset.mem_univ i) h)⟩

/-- Two-factor form of `exists_eval_ne_zero_of_forall_ne_zero`: a common non-root of two nonzero
multivariate polynomials over an infinite integral domain. -/
theorem exists_eval_ne_zero₂ {p₁ p₂ : MvPolynomial σ R} (h₁ : p₁ ≠ 0) (h₂ : p₂ ≠ 0) :
    ∃ x : σ → R, MvPolynomial.eval x p₁ ≠ 0 ∧ MvPolynomial.eval x p₂ ≠ 0 := by
  obtain ⟨x, hx⟩ :=
    exists_eval_ne_zero_of_forall_ne_zero ![p₁, p₂] (by intro i; fin_cases i <;> assumption)
  exact ⟨x, by simpa using hx 0, by simpa using hx 1⟩

/-- Three-factor form of `exists_eval_ne_zero_of_forall_ne_zero`. -/
theorem exists_eval_ne_zero₃ {p₁ p₂ p₃ : MvPolynomial σ R}
    (h₁ : p₁ ≠ 0) (h₂ : p₂ ≠ 0) (h₃ : p₃ ≠ 0) :
    ∃ x : σ → R, MvPolynomial.eval x p₁ ≠ 0 ∧ MvPolynomial.eval x p₂ ≠ 0 ∧
      MvPolynomial.eval x p₃ ≠ 0 := by
  obtain ⟨x, hx⟩ :=
    exists_eval_ne_zero_of_forall_ne_zero ![p₁, p₂, p₃] (by intro i; fin_cases i <;> assumption)
  exact ⟨x, by simpa using hx 0, by simpa using hx 1, by simpa using hx 2⟩

/-- Four-factor form of `exists_eval_ne_zero_of_forall_ne_zero`. -/
theorem exists_eval_ne_zero₄ {p₁ p₂ p₃ p₄ : MvPolynomial σ R}
    (h₁ : p₁ ≠ 0) (h₂ : p₂ ≠ 0) (h₃ : p₃ ≠ 0) (h₄ : p₄ ≠ 0) :
    ∃ x : σ → R, MvPolynomial.eval x p₁ ≠ 0 ∧ MvPolynomial.eval x p₂ ≠ 0 ∧
      MvPolynomial.eval x p₃ ≠ 0 ∧ MvPolynomial.eval x p₄ ≠ 0 := by
  obtain ⟨x, hx⟩ :=
    exists_eval_ne_zero_of_forall_ne_zero ![p₁, p₂, p₃, p₄] (by intro i; fin_cases i <;> assumption)
  exact ⟨x, by simpa using hx 0, by simpa using hx 1, by simpa using hx 2, by simpa using hx 3⟩

end MvPolynomial
