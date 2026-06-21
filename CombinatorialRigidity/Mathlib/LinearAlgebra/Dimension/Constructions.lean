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

* `Submodule.finrank_add_card_le_of_linearIndependent_mkQ` — a basis-free **block-rank-additivity
  lower bound**: for a subspace `W ≤ S` of a finite-dimensional space and a finite family
  `g : ι → V` lying in `S` (`∀ i, g i ∈ S`) whose images mod `W` are linearly independent
  (`LinearIndependent K (W.mkQ ∘ g)`), the rank of `S` is at least the rank of the corner block
  `W` plus the size of the independent-modulo-`W` family: `finrank W + |ι| ≤ finrank S`. This is
  the rank-decomposition shape `rank S ≥ rank(corner W) + dim(quotient block)` (with the quotient
  block exhibited by the `|ι|` members of `g` independent modulo `W`). The proof exhibits the
  intermediate `W ⊔ span (range g) ≤ S`, computes `finrank (W ⊔ span (range g)) = finrank W + |ι|`
  via `finrank_map_mkQ` + `finrank_span_eq_card`, and monotones up to `S`. When promoted upstream
  this lives beside the quotient finrank API in
  `Mathlib/LinearAlgebra/Dimension/RankNullity.lean`; the namespace stays `Submodule`.

* `Submodule.exists_le_finrank_eq_card_of_injective_map` — package the image of a linearly
  independent family under an injective linear map `L : V →ₗ[K] W` (landing in a target submodule
  `S`) as a *subspace* `W' ≤ S` of known finrank `|ι|`: given `LinearIndependent K f`, `L`
  injective, and `∀ i, L (f i) ∈ S`, there is a `W' ≤ S` with `finrank W' = |ι|`. The base block
  the block-rank-additivity lower bound (`finrank_add_card_le_of_linearIndependent_mkQ`) consumes
  as its `W` when the corner sits *over* a relabel-image base: `L = (funLeft σ⁻¹).dualMap` carries
  a base rigidity-row family to candidate rows, and the image span is the `W` of finrank
  `D(m−1)`. The image family is LI of the same card (`LinearIndependent.map'` along the injective
  `L`, the pattern the `d=3` `M₃` arm uses for its `w`), so `finrank_span_eq_card` reads off the
  finrank and `span_le` gives `W' ≤ S`. When promoted upstream this lives beside the
  `LinearIndependent`/finrank-span API; the namespace stays `Submodule`.

* `Submodule.linearIndependent_mkQ_sumElim_unit_of_notMem_span` — append-one linear independence
  modulo `W`: extend a family `f : ι → V` independent mod `W` by one extra vector `x` whose class
  mod `W` is *not* in the span of the others' classes, and the augmented `ι ⊕ Unit`-family
  `Sum.elim f (fun _ : Unit => x)` is still independent mod `W`. The corner-block independence
  criterion the block-rank-additivity lower bound consumes as its `hLI` when the corner is a
  panel-row family augmented by a single redundancy / `±r` row (KT 2011 (6.65): the `Mᵢ` block is
  full-rank `⟺ r ∉ rowspace r(Lᵢ)`). A push through `W.mkQ` + the `Sum`-append independence
  (`LinearIndependent.sum_type` with `disjoint_span_singleton'`). When promoted upstream this lives
  beside the `LinearIndependent` `Sum`/`Option` API; the namespace stays `Submodule`.
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

/-- A basis-free block-rank-additivity lower bound. For a subspace `W ≤ S` of a
finite-dimensional space and a finite family `g : ι → V` lying in `S` whose images mod `W` are
linearly independent, the rank of `S` is at least `finrank W + |ι|` — KT's
`rank R(G,pᵢ) ≥ rank Mᵢ + rank(base ∖ row)` block decomposition (6.64–6.65) in span/`finrank`
form, with `W` the base-minus-redundant-row block and the `|ι|` images of `g` the corner block
independent modulo `W`.

The intermediate `W ⊔ span (range g)` has finrank exactly `finrank W + |ι|`: its quotient image
`(span (range g)).map W.mkQ` equals `span (range (W.mkQ ∘ g))` of finrank `|ι|`
(`finrank_span_eq_card` on the hypothesis), and `finrank_map_mkQ` reads that off as
`finrank (W ⊔ span (range g)) − finrank W`. Since `W ⊔ span (range g) ≤ S`, `finrank_mono`
finishes. -/
theorem finrank_add_card_le_of_linearIndependent_mkQ {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Module.Finite K V] {ι : Type*} [Fintype ι] {W S : Submodule K V} (hWS : W ≤ S)
    {g : ι → V} (hg : ∀ i, g i ∈ S) (hLI : LinearIndependent K (W.mkQ ∘ g)) :
    Module.finrank K W + Fintype.card ι ≤ Module.finrank K S := by
  -- The intermediate `W ⊔ span (range g)` sits inside `S`.
  have hsub : (W ⊔ Submodule.span K (Set.range g) : Submodule K V) ≤ S :=
    sup_le hWS (Submodule.span_le.mpr (Set.range_subset_iff.mpr hg))
  -- Its quotient image has finrank `|ι|` (the independent family's span), so by `finrank_map_mkQ`
  -- the intermediate finrank is `finrank W + |ι|`.
  have hcard : Module.finrank K (Submodule.span K (Set.range (W.mkQ ∘ g))) = Fintype.card ι :=
    finrank_span_eq_card hLI
  have hspaneq : Submodule.span K (Set.range (W.mkQ ∘ g))
      = (Submodule.span K (Set.range g)).map W.mkQ := by
    rw [Set.range_comp, Submodule.map_span]
  rw [hspaneq, finrank_map_mkQ] at hcard
  have hle : Module.finrank K W
      ≤ Module.finrank K (W ⊔ Submodule.span K (Set.range g) : Submodule K V) :=
    Submodule.finrank_mono le_sup_left
  have hmono := Submodule.finrank_mono hsub
  omega

/-- Package the image of a linearly independent family under an injective linear map as a subspace
of known finrank inside a target submodule. For `f : ι → V` linearly independent, `L : V →ₗ[K] W`
injective, and `S : Submodule K W` containing every image `L (f i)`, there is a subspace `W' ≤ S`
with `finrank W' = |ι|` — namely `W' = span (range (L ∘ f))`.

This is the base-block packaging the block-rank-additivity lower bound
(`finrank_add_card_le_of_linearIndependent_mkQ`) consumes as its `W` when the corner block sits
over a relabel-image base: `L` carries an LI base family to candidate rows, and the resulting `W'`
is the relabel-image base block with the matching finrank. The image family is linearly
independent of the same cardinality (`LinearIndependent.map'` along the injective `L`), so
`finrank_span_eq_card` reads off `finrank W' = |ι|`, and `span_le` gives `W' ≤ S`. -/
theorem exists_le_finrank_eq_card_of_injective_map {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] {ι : Type*} [Fintype ι]
    {f : ι → V} (hf : LinearIndependent K f) {L : V →ₗ[K] W} (hL : Function.Injective L)
    {S : Submodule K W} (hS : ∀ i, L (f i) ∈ S) :
    ∃ W' : Submodule K W, W' ≤ S ∧ Module.finrank K W' = Fintype.card ι :=
  ⟨Submodule.span K (Set.range (L ∘ f)),
    Submodule.span_le.mpr (Set.range_subset_iff.mpr fun i => by simpa using hS i),
    finrank_span_eq_card (hf.map' L (LinearMap.ker_eq_bot.2 hL))⟩

/-- **Append-one linear independence modulo `W`.** Extend a family `f : ι → V` whose images mod
`W` are linearly independent by a single extra vector `x` whose class mod `W` lies *outside* the
span of the others' classes: the augmented `ι ⊕ Unit`-family
`Sum.elim f (fun _ : Unit => x)` is still linearly independent modulo `W`.

This is the corner-block independence criterion the block-rank-additivity lower bound
(`finrank_add_card_le_of_linearIndependent_mkQ`) consumes as its `hLI` when the corner block is a
panel-row family `f` (independent mod the base `W`) augmented by KT's single redundancy / `±r` row
`x`: the augment stays independent precisely because the `±r` row's class mod `W` is not in the
panel rows' span (KT 2011 (6.65): the `Mᵢ` block has full rank `⟺ r ∉ rowspace r(Lᵢ)`). The push
through `W.mkQ` turns `Sum.elim f (·)` into `Sum.elim (W.mkQ ∘ f) (·)`, then
`LinearIndependent.sum_type` reduces to the single-vector independence
(`x`'s class nonzero, from the `notMem_span` hypothesis) and the span-disjointness
(`disjoint_span_singleton'`, again from `notMem_span`). -/
theorem linearIndependent_mkQ_sumElim_unit_of_notMem_span {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] (W : Submodule K V) {ι : Type*} {f : ι → V}
    (hf : LinearIndependent K (W.mkQ ∘ f)) {x : V}
    (hx : W.mkQ x ∉ Submodule.span K (Set.range (W.mkQ ∘ f))) :
    LinearIndependent K (W.mkQ ∘ Sum.elim f (fun _ : Unit => x)) := by
  have hcomp : W.mkQ ∘ Sum.elim f (fun _ : Unit => x)
      = Sum.elim (W.mkQ ∘ f) (fun _ : Unit => W.mkQ x) := by
    funext j; cases j <;> rfl
  rw [hcomp]
  have hne : W.mkQ x ≠ 0 := fun h => hx (h ▸ Submodule.zero_mem _)
  refine hf.sum_type (LinearIndependent.of_subsingleton (i := ()) hne) ?_
  rw [Set.range_const]
  exact (Submodule.disjoint_span_singleton' hne).mpr hx

end Submodule
