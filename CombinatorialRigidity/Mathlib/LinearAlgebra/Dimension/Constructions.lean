/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Finrank of a constant (non-dependent) `Pi` type, and an independent `Fin`-family inside a
  finite-dimensional submodule

Upstream-eligible mirrors:

* `Module.finrank_pi_const` — mathlib has `Module.finrank_pi_fintype` for a *dependent*
  finite product `(i : ι) → M i` (a sum of the fibers' finranks) and `Module.finrank_pi`
  for the scalar case `ι → R` (= `Fintype.card ι`), but no fused lemma for the constant
  non-dependent product `ι → M`. This file supplies it. When promoted upstream this lives
  beside `Module.finrank_pi_fintype` in
  `Mathlib/LinearAlgebra/Dimension/Constructions.lean`; the namespace stays `Module`.

* `Submodule.exists_linearIndependent_fin_of_finrank_eq` — a finite-dimensional subspace `W`
  of finrank `n` (over a field) carries a linearly independent family `Fin n → V` of vectors,
  *valued in the ambient space* but all lying in `W`. This is the basis `W` owns, with its
  vectors coerced out into the ambient space. Stated this way (an existence statement over the
  abstract field, with no reference to a concrete carrier) it lets a downstream consumer obtain
  `n` independent ambient vectors inside `W` without ever unfolding the carrier's definition —
  important when the ambient space is a heavy `abbrev` (e.g. a `Module.Dual` of an exterior
  power) whose `whnf` is expensive. The basis-coercion is `Basis.linearIndependent.map'` along
  the injective `Submodule.subtype`. When promoted upstream this lives beside the
  `FiniteDimensional` basis API; the namespace stays `Submodule`.
-/

@[expose] public section

namespace Module

variable (R : Type*) [Semiring R] [StrongRankCondition R]
variable {ι : Type*} [Fintype ι] {M : Type*} [AddCommMonoid M] [Module R M]
  [Module.Free R M] [Module.Finite R M]

/-- The finrank of a constant finite product `ι → M` is `Fintype.card ι * finrank R M`.
The non-dependent specialization of `Module.finrank_pi_fintype`. -/
theorem finrank_pi_const :
    Module.finrank R (ι → M) = Fintype.card ι * Module.finrank R M := by
  rw [Module.finrank_pi_fintype R, Finset.sum_const, Finset.card_univ, smul_eq_mul]

end Module

namespace Submodule

/-- A finite-dimensional subspace `W` of finrank `n` carries a linearly independent family
`Fin n → V` of *ambient* vectors all lying in `W` (the basis `W` owns, coerced into the ambient
space). Existence form so the consumer never unfolds `V`'s carrier; the LI is the basis
independence pushed along the injective inclusion `W.subtype`. -/
theorem exists_linearIndependent_fin_of_finrank_eq {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (W : Submodule K V) [Module.Finite K W] {n : ℕ}
    (hn : Module.finrank K W = n) :
    ∃ f : Fin n → V, LinearIndependent K f ∧ ∀ i, f i ∈ W := by
  haveI : Module.Free K W := Module.Free.of_divisionRing K W
  let b : Module.Basis (Fin n) K W := Module.finBasisOfFinrankEq K W hn
  exact ⟨fun i => (b i : V), b.linearIndependent.map' W.subtype (Submodule.ker_subtype _),
    fun i => (b i).2⟩

end Submodule
