/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.Defs

/-!
# Upstream candidate: an algebraically independent family is a non-root of every nonzero polynomial

`Mathlib.RingTheory.AlgebraicIndependent.Defs` proves
`AlgebraicIndependent.eq_zero_of_aeval_eq_zero`: if `x : ι → A` is algebraically independent over
`R` and `MvPolynomial.aeval x p = 0`, then `p = 0`. Its immediate contrapositive — *an
algebraically independent family evaluates a nonzero polynomial to a nonzero element* — is the
form actually consumed downstream, but is not packaged in mathlib as a standalone lemma.

This `AlgebraicIndependent.aeval_ne_zero` is the leaf brick of the Phase-22d KT-Claim-6.11 analytic
kernel (Katoh–Tanigawa 2011, footnote 6 / eq. (6.22)). KT's inductive realization takes the panel
coordinates `q : σ → ℝ` algebraically independent over `ℚ`; such a `q` then lies off the zero locus
of *every* nonzero rational polynomial, so it is automatically a non-root of any subgraph's rank
polynomial. That is exactly "the inductively-fixed generic seed attains the matroid-predicted rank":
a Gram-determinant minor that is nonzero at one realization is a nonzero `MvPolynomial ι ℚ`, hence
`aeval q`-nonzero at the alg.-independent `q`. (This is the `R = ℚ`, `A = ℝ` instance; the lemma is
stated over an arbitrary `R`-algebra `A`. The same-ring `eval` form would force `ι` empty, since
every element of `R` is algebraic over `R`, so the `aeval` form is the one with content.)

Mirror path: `Mathlib/RingTheory/AlgebraicIndependent/Defs.lean`. Promotion to mathlib is a
copy-paste into the upstream `Defs` file, directly below
`AlgebraicIndependent.eq_zero_of_aeval_eq_zero`.
-/

@[expose] public section

variable {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {x : ι → A}

/-- **An algebraically independent family is a non-root of every nonzero polynomial.** If
`x : ι → A` is algebraically independent over `R`, then `MvPolynomial.aeval x` sends every nonzero
`p : MvPolynomial ι R` to a nonzero element of `A`. This is the contrapositive of
`AlgebraicIndependent.eq_zero_of_aeval_eq_zero`. -/
theorem AlgebraicIndependent.aeval_ne_zero (h : AlgebraicIndependent R x)
    {p : MvPolynomial ι R} (hp : p ≠ 0) : MvPolynomial.aeval x p ≠ 0 :=
  fun hp0 => hp (h.eq_zero_of_aeval_eq_zero p hp0)
