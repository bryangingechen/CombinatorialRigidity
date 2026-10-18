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
  finite-dimensional submodule, and finrank bounds modulo a subspace

Upstream-eligible mirrors:

* `Module.finrank_pi_const` — mathlib has `Module.finrank_pi_fintype` for a *dependent*
  finite product `(i : ι) → M i` (a sum of the fibers' finranks) and `Module.finrank_pi`
  for the scalar case `ι → R` (= `Fintype.card ι`), but no fused lemma for the constant
  non-dependent product `ι → M`. This file supplies it. When promoted upstream this lives
  beside `Module.finrank_pi_fintype` in
  `Mathlib/LinearAlgebra/Dimension/Constructions.lean`; the namespace stays `Module`.

* `Submodule.exists_linearIndependent_fin_of_finrank_eq` — a finite-dimensional subspace `W`
  of finrank `n` (over a field) carries a linearly independent family `Fin n → V` of vectors,
  *valued in the ambient space* but all lying in `W`: the basis `W` owns, with its vectors coerced
  out into the ambient space (`Basis.linearIndependent.map'` along the injective
  `Submodule.subtype`). Stated as an existence statement over the abstract field, it lets a caller
  obtain `n` independent ambient vectors inside `W` without unfolding the definition of the
  ambient space, which matters when that space is an `abbrev` whose `whnf` is expensive (e.g. a
  `Module.Dual` of an exterior power). When promoted upstream this lives beside the
  `FiniteDimensional` basis API; the namespace stays `Submodule`. Its companions for a named
  basis are `Module.Basis.linearIndependent_coe_subtype` and `Module.Basis.span_coe_eq`.

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

* `Submodule.finrank_add_card_le_of_linearIndependent_mkQ` — a basis-free lower bound for the rank
  of a block-triangular family: for a subspace `W ≤ S` of a finite-dimensional space and a finite
  family `g : ι → V` lying in `S` whose images mod `W` are linearly independent
  (`LinearIndependent K (W.mkQ ∘ g)`), `finrank W + |ι| ≤ finrank S`. The proof computes
  `finrank (W ⊔ span (range g)) = finrank W + |ι|` via `finrank_map_mkQ` + `finrank_span_eq_card`
  and goes up to `S` by monotonicity. When promoted upstream this lives beside the quotient
  finrank API in `Mathlib/LinearAlgebra/Dimension/RankNullity.lean`; the namespace stays
  `Submodule`.

* `Submodule.exists_le_finrank_eq_card_of_injective_map` — the image of a linearly independent
  family under an injective linear map `L : V →ₗ[K] W`, landing in a submodule `S`, spans a
  subspace `W' ≤ S` of finrank `|ι|` (`LinearIndependent.map'` along `L`, then
  `finrank_span_eq_card` and `span_le`). It supplies the `W` of
  `finrank_add_card_le_of_linearIndependent_mkQ` when that subspace is the image of a known
  independent family. When promoted upstream this lives beside the `LinearIndependent`/finrank-span
  API; the namespace stays `Submodule`.

* `Submodule.linearIndependent_mkQ_sumElim_unit_of_notMem_span` — appending one vector `x` to a
  family `f : ι → V` independent mod `W` keeps it independent mod `W` when the class of `x` mod
  `W` is not in the span of the others' classes: the family `Sum.elim f (fun _ : Unit => x)` is
  independent mod `W`. A push through `W.mkQ` + the `Sum`-append independence
  (`LinearIndependent.sum_type` with `disjoint_span_singleton'`). When promoted upstream this lives
  beside the `LinearIndependent` `Sum`/`Option` API; the namespace stays `Submodule`.

* `Submodule.linearIndependent_mkQ_of_comp` — independence modulo `W` from independence after a
  linear map that *kills* `W`: if `LinearIndependent K (T ∘ f)` for a linear map
  `T : V →ₗ[K] W'` with `W ≤ ker T`, then `LinearIndependent K (W.mkQ ∘ f)`. The factor map is the
  quotient lift `W.liftQ T hW`, which satisfies `(W.liftQ T hW) ∘ W.mkQ = T` (`liftQ_mkQ`), so
  `LinearIndependent.of_comp` applied to it turns the post-`T` independence into the modulo-`W`
  independence. When promoted upstream this lives beside the `LinearIndependent`/quotient API; the
  namespace stays `Submodule`.

The last four give the rank bound of Katoh–Tanigawa 2011 drawn after (6.65) from the block form
(6.64), `rank R(G, pᵢ) ≥ rank Mᵢ + rank R(G₁ ∖ {(v₀v₂)ᵢ*}, q₁)`, in span form: `W` is spanned by
rows of the bottom block, and `g` holds the rows of the corner block. The combinatorial-rigidity
project applies them in `Molecular/AlgebraicInduction/CaseIII/Candidate.lean`
(`finrank_span_rigidityRows_ge_of_corner`,
`exists_le_finrank_span_rigidityRows_eq_card_of_injective_map`,
`linearIndependent_mkQ_corner_of_gate`, `linearIndependent_mkQ_panelRow_of_edge`), and the
pigeonhole in `exists_redundant_panelRow_of_edge_of_finrank_lt` there.
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
space). Stated as an existence so the caller never unfolds the type `V`; the LI is the basis
independence pushed along the injective inclusion `W.subtype`. -/
theorem exists_linearIndependent_fin_of_finrank_eq {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (W : Submodule K V) [Module.Finite K W] {n : ℕ}
    (hn : Module.finrank K W = n) :
    ∃ f : Fin n → V, LinearIndependent K f ∧ ∀ i, f i ∈ W := by
  have : Module.Free K W := Module.Free.of_divisionRing K W
  let b : Module.Basis (Fin n) K W := Module.finBasisOfFinrankEq K W hn
  exact ⟨fun i => (b i : V), b.linearIndependent.map' W.subtype (Submodule.ker_subtype _),
    fun i => (b i).2⟩

/-- The vectors of a basis of a submodule `W ≤ V`, coerced into the ambient space `V`, form a
linearly independent family in `V`. This is `Basis.linearIndependent` pushed along the injective
inclusion `W.subtype` (`Submodule.ker_subtype`). Stated over the abstract `V` so the caller can
instantiate it at a type whose `whnf` is expensive (e.g. a `Module.Dual` of an exterior power)
without ever forcing that `whnf`: the `Basis.linearIndependent.map'` step is elaborated *here*,
against the abstract `V`, not at the call site. The named-family complement of
`exists_linearIndependent_fin_of_finrank_eq` (which gives only an *existence* form): a caller that
needs the LI of a *specific* submodule basis applies this lemma directly. When promoted upstream
this lives beside the `Module.Basis` ambient-coercion API; the namespace stays `Module.Basis`. -/
theorem _root_.Module.Basis.linearIndependent_coe_subtype {K V ι : Type*} [Field K]
    [AddCommGroup V] [Module K V] {W : Submodule K V} (b : Module.Basis ι K W) :
    LinearIndependent K (fun i => (b i : V)) := by
  have h := b.linearIndependent.map' W.subtype (Submodule.ker_subtype _)
  rwa [Submodule.coe_subtype] at h

/-- The vectors of a basis of a submodule `W ≤ V`, coerced into the ambient space `V`, span exactly
`W`. This is `Basis.span_eq` (which spans `⊤` *inside* `W`) pushed along the inclusion `W.subtype`
via `Submodule.span_image` and `Submodule.map_subtype_top`. The span companion of
`Module.Basis.linearIndependent_coe_subtype`: the two together say a coerced submodule basis is a
basis of `W` *as a subset of the ambient `V`*, in the form `span (range (coerced basis)) = W`,
without unfolding the ambient type (e.g. a `Module.Dual` of an exterior power). When promoted
upstream this lives beside the `Module.Basis` ambient-coercion API; the namespace stays
`Module.Basis`. -/
theorem _root_.Module.Basis.span_coe_eq {K V ι : Type*} [Field K]
    [AddCommGroup V] [Module K V] {W : Submodule K V} (b : Module.Basis ι K W) :
    Submodule.span K (Set.range (fun i => (b i : V))) = W := by
  rw [show (fun i => (b i : V)) = W.subtype ∘ b from rfl, Set.range_comp, Submodule.span_image,
    b.span_eq, Submodule.map_subtype_top]

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
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and]
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

/-- A basis-free lower bound for the rank of a block-triangular family. For a subspace `W ≤ S` of
a finite-dimensional space and a finite family `g : ι → V` lying in `S` whose images mod `W` are
linearly independent, the rank of `S` is at least `finrank W + |ι|`. In the span form of the bound
Katoh–Tanigawa 2011 draw after (6.65) from the block form (6.64),
`rank R(G, pᵢ) ≥ rank Mᵢ + rank R(G₁ ∖ {(v₀v₂)ᵢ*}, q₁)`, `W` is spanned by rows of the bottom block
and `g` holds the rows of the corner block, independent modulo `W`.

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

The image family is linearly independent of the same cardinality (`LinearIndependent.map'` along
the injective `L`), so `finrank_span_eq_card` reads off `finrank W' = |ι|`, and `span_le` gives
`W' ≤ S`. It supplies the `W` of `finrank_add_card_le_of_linearIndependent_mkQ` when that subspace
is the image of a known independent family. -/
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

It gives the hypothesis `hLI` of `finrank_add_card_le_of_linearIndependent_mkQ` when the corner
block is a family `f` independent mod `W` with one more row `x`. In the proof of
Katoh–Tanigawa 2011, (6.65), the corner block `Mᵢ` is the rows of `r(Lᵢ)` with one more row,
`r` or (by (6.66)) `±r`, and `Mᵢ` has full rank iff `r` is not in the row space of `r(Lᵢ)`. The
push through `W.mkQ` turns `Sum.elim f (·)` into `Sum.elim (W.mkQ ∘ f) (·)`, then
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

/-- **Linear independence modulo `W` from independence after a `W`-killing map.** If a family
`f : ι → V` is linearly independent after applying a linear map `T : V →ₗ[K] W'` that kills `W`
(`W ≤ ker T` and `LinearIndependent K (T ∘ f)`), then `f` is linearly independent *modulo* `W`
(`LinearIndependent K (W.mkQ ∘ f)`).

With `linearIndependent_mkQ_sumElim_unit_of_notMem_span` it gives the hypothesis `hLI` of
`finrank_add_card_le_of_linearIndependent_mkQ`: rows that are independent after restriction to
the columns of one body (`T`), on which the rows spanning `W` vanish, are independent modulo `W`,
as for the columns of `v` in the block form of Katoh–Tanigawa 2011, (6.16), where the rows of
`Ev` vanish. The proof factors `T` through the quotient: the lift
`W.liftQ T hW : V ⧸ W →ₗ[K] W'` satisfies `(W.liftQ T hW) ∘ W.mkQ = T` (`liftQ_mkQ`), so
`(W.liftQ T hW) ∘ (W.mkQ ∘ f) = T ∘ f`, and `LinearIndependent.of_comp (W.liftQ T hW)` recovers
the independence of `W.mkQ ∘ f` from that of `T ∘ f`. -/
theorem linearIndependent_mkQ_of_comp {K V W' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W'] [Module K W']
    (W : Submodule K V) {ι : Type*} {f : ι → V}
    {T : V →ₗ[K] W'} (hW : W ≤ LinearMap.ker T)
    (hf : LinearIndependent K (T ∘ f)) :
    LinearIndependent K (W.mkQ ∘ f) := by
  refine LinearIndependent.of_comp (W.liftQ T hW) ?_
  have hcomp : (W.liftQ T hW) ∘ (W.mkQ ∘ f) = T ∘ f := by
    funext i
    simp only [Function.comp_apply]
    rw [← LinearMap.comp_apply, Submodule.liftQ_mkQ]
  rw [hcomp]
  exact hf

end Submodule
