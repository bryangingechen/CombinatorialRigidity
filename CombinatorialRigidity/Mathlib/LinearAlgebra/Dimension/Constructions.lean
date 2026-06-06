/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Finrank of a constant (non-dependent) `Pi` type, an independent `Fin`-family inside a
  finite-dimensional submodule, and a finrank pigeonhole for redundant family members

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

* `Submodule.finrank_map_mkQ` — the finrank of the image `S.map W.mkQ` of a submodule under the
  quotient projection `W.mkQ : V → V ⧸ W` is `finrank (W ⊔ S) − finrank W`. (Rank–nullity on
  `W.mkQ ∘ S.subtype`, whose range is `S.map W.mkQ` and whose kernel is `W ⊓ S`, against
  `finrank_sup_add_finrank_inf_eq`.) When promoted upstream this lives beside the quotient
  finrank API in `Mathlib/LinearAlgebra/Dimension/RankNullity.lean`; namespace `Submodule`.

* `Submodule.exists_mem_sup_span_image_compl_of_finrank_lt` — a finrank pigeonhole: if a finite
  family `g : ι → V` raises the finrank of a subspace `W` by strictly fewer than `|ι|` (i.e.
  `finrank (W ⊔ span (range g)) < finrank W + |ι|`), then some member `g i` is *redundant
  modulo `W` and the others* — it lies in `W ⊔ span (g '' {j ≠ i})`. The contrapositive runs in
  the quotient `V ⧸ W`: if no member were redundant, the image family `W.mkQ ∘ g` would be
  linearly independent (`linearIndependent_iff_notMem_span`), forcing
  `finrank (span (range (W.mkQ ∘ g))) = |ι|` and hence
  `finrank (W ⊔ span (range g)) = finrank W + |ι|` (via `finrank_map_mkQ`). When promoted
  upstream this lives beside the finrank/span API; the namespace stays `Submodule`.
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

/-- The finrank of the image `S.map W.mkQ` of a submodule under the quotient projection
`W.mkQ : V → V ⧸ W` is `finrank (W ⊔ S) − finrank W`. Rank–nullity on `W.mkQ ∘ S.subtype`,
whose range is `S.map W.mkQ` and whose kernel is `W ⊓ S`, against the
sup/inf finrank identity. -/
theorem finrank_map_mkQ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] (W S : Submodule K V) :
    Module.finrank K (S.map W.mkQ)
      = Module.finrank K (W ⊔ S : Submodule K V) - Module.finrank K W := by
  set f : S →ₗ[K] (V ⧸ W) := W.mkQ ∘ₗ S.subtype with hf
  have hrange : LinearMap.range f = S.map W.mkQ := by
    rw [hf, LinearMap.range_comp, Submodule.range_subtype]
  have hkereq : LinearMap.ker f = W.comap S.subtype := by
    rw [hf, LinearMap.ker_comp, Submodule.ker_mkQ]
  -- `W.comap S.subtype` (a submodule of `S`) is isomorphic to `W ⊓ S`.
  have hkerrank : Module.finrank K (W.comap S.subtype)
      = Module.finrank K (W ⊓ S : Submodule K V) := by
    have hcomap : W.comap S.subtype = (W ⊓ S).comap S.subtype := by
      ext x
      simp only [Submodule.mem_comap, Submodule.coe_subtype, Submodule.mem_inf]
      exact ⟨fun h => ⟨h, x.2⟩, fun h => h.1⟩
    rw [hcomap]
    exact (Submodule.comapSubtypeEquivOfLe inf_le_right).finrank_eq
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, hkereq, hkerrank] at hrn
  have h1 : Module.finrank K (W ⊓ S : Submodule K V) + Module.finrank K (W ⊔ S : Submodule K V)
      = Module.finrank K W + Module.finrank K S := by
    rw [add_comm]; exact Submodule.finrank_sup_add_finrank_inf_eq W S
  omega

/-- A finrank pigeonhole. If a finite family `g : ι → V` raises the finrank of a subspace `W`
by strictly fewer than `|ι|` — `finrank (W ⊔ span (range g)) < finrank W + |ι|` — then some
member `g i` is redundant modulo `W` and the rest: `g i ∈ W ⊔ span (g '' {j ≠ i})`.

The contrapositive runs in the quotient `V ⧸ W`: were no member redundant, the image family
`W.mkQ ∘ g` would be linearly independent (`linearIndependent_iff_notMem_span`), so its span
would have finrank `|ι|`, forcing `finrank (W ⊔ span (range g)) = finrank W + |ι|`
(via `finrank_map_mkQ`) and contradicting the hypothesis. -/
theorem exists_mem_sup_span_image_compl_of_finrank_lt {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Module.Finite K V] {ι : Type*} [Fintype ι] (W : Submodule K V) (g : ι → V)
    (h : Module.finrank K (W ⊔ Submodule.span K (Set.range g) : Submodule K V)
      < Module.finrank K W + Fintype.card ι) :
    ∃ i, g i ∈ W ⊔ Submodule.span K (g '' {j | j ≠ i}) := by
  by_contra hcon
  push Not at hcon
  -- `W.mkQ (g i)` lies in the span of the image of the others iff `g i ∈ W ⊔ span (others)`.
  have hmemiff : ∀ (i : ι) (T : Set ι),
      W.mkQ (g i) ∈ Submodule.span K ((W.mkQ ∘ g) '' T) ↔
        g i ∈ W ⊔ Submodule.span K (g '' T) := fun i T => by
    rw [Set.image_comp, ← Submodule.map_span, ← Submodule.mem_comap, Submodule.comap_map_mkQ]
  -- No member is redundant, so the image family is linearly independent in `V ⧸ W`.
  have hLI : LinearIndependent K (W.mkQ ∘ g) := by
    rw [linearIndependent_iff_notMem_span]
    intro i hmem
    refine hcon i ?_
    rw [Function.comp_apply, hmemiff i (Set.univ \ {i})] at hmem
    convert hmem using 4
    ext j
    simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_univ, Set.mem_singleton_iff, true_and]
  -- An independent family's span has finrank `|ι|`; translate back to the ambient finrank.
  have hcard : Module.finrank K (Submodule.span K (Set.range (W.mkQ ∘ g))) = Fintype.card ι :=
    finrank_span_eq_card hLI
  have hspaneq : Submodule.span K (Set.range (W.mkQ ∘ g))
      = (Submodule.span K (Set.range g)).map W.mkQ := by
    rw [Set.range_comp, Submodule.map_span]
  rw [hspaneq, finrank_map_mkQ] at hcard
  have hle : Module.finrank K W
      ≤ Module.finrank K (W ⊔ Submodule.span K (Set.range g) : Submodule K V) :=
    Submodule.finrank_mono le_sup_left
  omega

end Submodule
