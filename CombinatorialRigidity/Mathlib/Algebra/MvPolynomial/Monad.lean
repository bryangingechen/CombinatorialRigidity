/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.Algebra.MvPolynomial.Monad

/-!
# Upstream candidate: evaluating a substitution

`Mathlib.Algebra.MvPolynomial.Monad` has `MvPolynomial.aeval_bind₁` and
`MvPolynomial.eval₂Hom_bind₁` — evaluating `bind₁ g φ` is evaluating `φ` at the evaluated
substitutes — but not the `eval` form, which is what a substitution into a polynomial over a
field and a pointwise evaluation meet as. It is `aeval_bind₁` up to the definitional
`aeval f = eval f` over the base ring, which `rw` does not see.

The combinatorial-rigidity project uses it to evaluate a rank polynomial at configuration points
built from a picture and a height (`Graph.x0Attains_of_exists`,
`Molecular/Molecule/Pencil/MainComponent/Carrier.lean`).

Mirror path: `Mathlib/Algebra/MvPolynomial/Monad.lean`. Promotion to mathlib is a copy-paste into
the upstream file, next to `MvPolynomial.aeval_bind₁`.
-/

@[expose] public section

namespace MvPolynomial

variable {σ τ R : Type*} [CommSemiring R]

/-- **Evaluating a substitution**: `eval f (bind₁ g φ) = eval (fun i => eval f (g i)) φ`. The
`eval` form of `MvPolynomial.aeval_bind₁`. -/
theorem eval_bind₁ (f : τ → R) (g : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) :
    eval f (bind₁ g φ) = eval (fun i => eval f (g i)) φ :=
  aeval_bind₁ f g φ

end MvPolynomial
