/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.RankAndCardinality
public import Mathlib.Algebra.FreeAlgebra.Cardinality
public import Mathlib.Analysis.Real.Cardinality

/-!
# Upstream candidate: a finite algebraically independent family of reals over the rationals

`ℝ` has uncountable transcendence degree over `ℚ`, so for *any* finite index type `σ` there is an
injective family `q : σ → ℝ` that is algebraically independent over `ℚ`
(`exists_injective_algebraicIndependent_real`). Mathlib packages the transcendence-basis existence
(`exists_isTranscendenceBasis'`), the reindex-stability of algebraic independence
(`AlgebraicIndependent.comp`), and the cardinality bounds, but not this finite-family existence
form as a standalone lemma.

This is the substitute the Phase-22d KT-Claim-6.11 analytic kernel needs in place of a moment-curve
seed (Katoh–Tanigawa 2011, footnote 6). KT fixes the inductive realization with panel coordinates
algebraically independent over `ℚ`, so that one seed is automatically a non-root of *every*
subgraph's rank polynomial (`AlgebraicIndependent.aeval_ne_zero`). The project's explicit
general-position witness, the moment curve `q (a, i) = (param a) ^ i`, is **not** algebraically
independent: its coordinates satisfy rational relations (`q (a, 0) = 1`, `q (a, 2) = q (a, 1) ^ 2`,
…). So the alg.-independent seed must come from a transcendence basis instead, which this lemma
exhibits at any finite cardinality. (The moment curve is still the right *general-position* witness;
the two roles — general position vs. algebraic independence — are now supplied by different points.)

Mirror path: `Mathlib/RingTheory/AlgebraicIndependent/TranscendenceBasis.lean` (the
`infinite_index_of_transcendenceBasis_real` cardinality fact would slot beside the existing
transcendence-degree results; the finite-family existence corollary follows it).
-/

@[expose] public section

open Cardinal

/-- **A transcendence basis of `ℝ` over `ℚ` is infinite.** Were the index type `ι` finite, the field
`ℝ` would be algebraic over the countable subalgebra `ℚ[range x]` and hence countable, contradicting
the uncountability of `ℝ`. -/
theorem infinite_index_of_transcendenceBasis_real {ι : Type*} {x : ι → ℝ}
    (hx : IsTranscendenceBasis ℚ x) : Infinite ι := by
  rw [← not_finite_iff_infinite]
  intro hfin
  have halg : Algebra.IsAlgebraic (Algebra.adjoin ℚ (Set.range x)) ℝ := hx.isAlgebraic
  haveI : Finite (Set.range x) := Set.finite_range x
  -- `ℝ` is algebraic over the finitely-generated (hence countable) subalgebra `ℚ[range x]`.
  have hadj : #(Algebra.adjoin ℚ (Set.range x)) ≤ #ℚ ⊔ #(Set.range x) ⊔ ℵ₀ :=
    Algebra.cardinalMk_adjoin_le ℚ _
  have hrange : #(Set.range x) ≤ ℵ₀ := (Cardinal.lt_aleph0_of_finite _).le
  have hadj' : #(Algebra.adjoin ℚ (Set.range x)) ≤ ℵ₀ := by
    refine hadj.trans ?_
    simp [hrange]
  have hmax : #ℝ ≤ max #(Algebra.adjoin ℚ (Set.range x)) ℵ₀ :=
    Algebra.IsAlgebraic.cardinalMk_le_max _ ℝ
  have hℝ : #ℝ ≤ ℵ₀ := hmax.trans (by simp [hadj'])
  rw [Cardinal.mk_real] at hℝ
  exact absurd hℝ (not_le.mpr Cardinal.aleph0_lt_continuum)

/-- **A finite algebraically independent family of reals over the rationals.** For any finite index
type `σ` there is an injective `q : σ → ℝ` algebraically independent over `ℚ`. Such a `q` is a
non-root of every nonzero polynomial over `ℚ` (`AlgebraicIndependent.aeval_ne_zero`) — the seed
genericity the Phase-22d KT-Claim-6.11 kernel needs, in place of the (non-algebraically-independent)
moment curve. Built by restricting a transcendence basis of `ℝ` over `ℚ` — which is infinite
(`infinite_index_of_transcendenceBasis_real`) — along an embedding `σ ↪ ι`; algebraic independence
is preserved under reindexing by an injection (`AlgebraicIndependent.comp`). -/
theorem exists_injective_algebraicIndependent_real (σ : Type*) [Finite σ] :
    ∃ q : σ → ℝ, Function.Injective q ∧ AlgebraicIndependent ℚ q := by
  obtain ⟨ι, x, hx⟩ := exists_isTranscendenceBasis' ℚ ℝ
  haveI : Infinite ι := infinite_index_of_transcendenceBasis_real hx
  obtain ⟨f⟩ : Nonempty (σ ↪ ι) := by
    rw [← Cardinal.lift_mk_le']
    exact (Cardinal.lift_lt_aleph0.mpr (Cardinal.lt_aleph0_of_finite σ)).le.trans
      (Cardinal.aleph0_le_lift.mpr (Cardinal.aleph0_le_mk ι))
  exact ⟨x ∘ f, hx.1.injective.comp f.injective, hx.1.comp f f.injective⟩
