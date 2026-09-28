/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.Algebra.MvPolynomial.Polynomial

/-!
# Upstream candidate: evaluating a substitution by univariate polynomials

`Mathlib.Algebra.MvPolynomial.Polynomial` has `MvPolynomial.polynomial_eval_eval₂`, the `eval₂`
form of substituting each variable by a univariate polynomial and then evaluating at a point, but
not the `aeval` form — the one a substitution over a commutative semiring's own polynomial ring
meets as, since `aeval` is definitionally `eval₂` at the algebra map.

The combinatorial-rigidity project uses it to specialize the planar rank theorem's non-vanishing
polynomial along a univariate curve of normals (the curve-limit lemma,
`PanelHingeFramework.finite_setOf_finrank_lt_of_curve`,
`Molecular/Molecule/Pencil/MainComponent/Bridge.lean`, Phase 40j SPLITOFF): substituting the curve
`c : α × Fin (k + 2) → Polynomial K` into the rank polynomial and evaluating at `t` agrees with
evaluating the rank polynomial directly at the curve's value `c · eval t`.

Mirror path: `Mathlib/Algebra/MvPolynomial/Polynomial.lean`. Promotion to mathlib is a copy-paste
into the upstream file, next to `MvPolynomial.polynomial_eval_eval₂`.
-/

@[expose] public section

namespace MvPolynomial

variable {R σ : Type*} [CommSemiring R]

/-- **Evaluating a substitution by univariate polynomials**: substituting each variable `i` of
`Q` by a univariate polynomial `c i` and evaluating the result at `t` agrees with evaluating `Q`
directly at the point `fun i => (c i).eval t`. The `aeval` form of
`MvPolynomial.polynomial_eval_eval₂` (`aeval f = eval₂ (algebraMap R _) f` at the algebra map). -/
theorem polynomial_eval_aeval (c : σ → Polynomial R) (Q : MvPolynomial σ R) (t : R) :
    (MvPolynomial.aeval c Q).eval t = MvPolynomial.eval (fun i => (c i).eval t) Q := by
  rw [MvPolynomial.aeval_def, ← Polynomial.coe_evalRingHom, MvPolynomial.hom_eval₂]
  congr 1
  ext a
  simp [Polynomial.coe_evalRingHom]

end MvPolynomial
