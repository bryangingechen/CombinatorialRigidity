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

end MvPolynomial
