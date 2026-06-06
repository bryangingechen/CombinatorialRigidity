/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.RingTheory.MvPolynomial.Tower

/-!
# Upstream candidate: evaluating the base-ring image of a polynomial along the algebra map

`Mathlib.RingTheory.MvPolynomial.Tower` proves `MvPolynomial.aeval_map_algebraMap`:
`aeval x (map (algebraMap R A) p) = aeval x p` for `x : σ → B` in a scalar tower. Specialised to
the self-tower `A = B` it descends an `eval` over `A` to an `aeval` over the base ring `R`:
*the `A`-valued evaluation of the `algebraMap R A`-image of a base-ring polynomial `Q₀` equals
its `aeval` over `R`* (`eval_map_algebraMap`), together with the fact that this image is nonzero
exactly when `Q₀` is (`map_algebraMap_ne_zero_iff`, via injectivity of a faithful `algebraMap`).
Neither is packaged in mathlib as a standalone lemma.

This pair is the leaf brick of the Phase-22d KT-Claim-6.11 analytic kernel's *rationality bridge*
(Katoh–Tanigawa 2011, footnote 6). The genericity device builds an `ℝ`-typed rank polynomial
`Q : MvPolynomial σ ℝ` whose coefficients are structural change-of-basis constants — rational, but
not manifestly so in the term. To certify `eval q Q ≠ 0` from `q` being algebraically independent
over `ℚ` (`AlgebraicIndependent.aeval_ne_zero`, which lives over `ℚ`), one exhibits `Q` as the
`algebraMap ℚ ℝ`-image of some `Q₀ : MvPolynomial σ ℚ`: then `eval q Q = aeval q Q₀`
(`eval_map_algebraMap` at `R = ℚ`, `A = ℝ`) and `Q ≠ 0` transfers to `Q₀ ≠ 0`
(`map_algebraMap_ne_zero_iff`, using `FaithfulSMul ℚ ℝ`), so leaf (i) applies. This is the
`R = ℚ`, `A = ℝ` instance; both lemmas are stated over an arbitrary base ring.

Mirror path: `Mathlib/RingTheory/MvPolynomial/Tower.lean`. Promotion to mathlib is a copy-paste
into the upstream `Tower` file, directly below `MvPolynomial.aeval_map_algebraMap`.
-/

public section

namespace MvPolynomial

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] {σ : Type*}

/-- **Evaluation descends along the algebra map.** For `Q₀ : MvPolynomial σ R`, the `A`-valued
evaluation of its `algebraMap R A`-image at `q : σ → A` equals the `R`-algebra evaluation
`aeval q Q₀`. This is `aeval_map_algebraMap` specialised to the self-tower `A = B`, rewritten
through `aeval_eq_eval` on the `A`-side. -/
theorem eval_map_algebraMap (q : σ → A) (Q₀ : MvPolynomial σ R) :
    eval q (map (algebraMap R A) Q₀) = aeval q Q₀ := by
  rw [← aeval_map_algebraMap A q Q₀, aeval_eq_eval]

/-- **The algebra-map image of a polynomial is nonzero iff the polynomial is.** When `algebraMap
R A` is injective (e.g. `FaithfulSMul R A`), `map (algebraMap R A) Q₀ = 0 ↔ Q₀ = 0`, so the
image is nonzero exactly when `Q₀` is. -/
theorem map_algebraMap_ne_zero_iff [FaithfulSMul R A] {Q₀ : MvPolynomial σ R} :
    map (algebraMap R A) Q₀ ≠ 0 ↔ Q₀ ≠ 0 :=
  (map_eq_zero_iff _ (map_injective _ (FaithfulSMul.algebraMap_injective R A))).not

end MvPolynomial
