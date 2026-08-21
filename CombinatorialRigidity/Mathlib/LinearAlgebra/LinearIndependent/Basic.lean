/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Algebra.Module.Torsion.Field

/-!
# Upstream candidates: independent-family facts

Six facts about linearly independent families, all upstream-eligible.

`LinearIndependent.disjoint_span_range_ker` is the converse companion of mathlib's
`LinearIndependent.map`: if the composite `f ∘ v` is linearly independent, then the span of
`v` meets `ker f` trivially (`Disjoint (span R (range v)) (ker f)`). `LinearIndependent.map`
supplies the forward direction (span-disjoint-from-kernel makes `f ∘ v` independent when `v`
is); this reads the disjointness back off the composite's independence. The rigidity project's
zero-extension lift (`RigidityMatroid.lean`) uses it to discharge the span-disjointness of the
`LinearIndepOn.union` splitting the square's edge rows into the non-incident block and the star
at the new vertex — the star rows survive a test-motion detector `Ψ` whose kernel contains the
non-incident block, so `Ψ ∘ (star rows)` is independent and this lemma turns that into the
required disjointness.

`linearIndependent_sumElim_unit_iff` is the row-space criterion for appending a
single vector to a linearly independent family: over a division ring, augmenting
an independent `v` with one more vector `x` (packaged as `Sum.elim v (fun _ : Unit
=> x)`) stays independent **iff** `x` is not already in the span of `v`. It is the
`Sum.elim … (fun _ : Unit => x)` companion of mathlib's `LinearIndepOn.notMem_span_iff`
(which is phrased for `insert a s`); the `Sum.elim`-of-a-`Unit`-singleton shape is the
one the rigidity project's block-assembly functionals come in (the new block plus one
augmenting candidate row, `RigidityMatrix.lean`'s candidate-completion).

The proof is `linearIndependent_sum` (the iff splitting an `ι ⊕ ι'` family into the two
sub-families plus span-disjointness) specialised to `ι' = Unit`, where the second
sub-family is the singleton `{x}` and span-disjointness `Disjoint (span (range v)) (K ∙ x)`
collapses to `x ∉ span (range v)` by `Submodule.disjoint_span_singleton'`.

`linearIndependent_sumElim_block_swap` is the block row-operation fact: for a base family
`base` and a candidate block `cand` with `Sum.elim base cand` independent, replacing `cand` by
any `cand'` whose entries differ from `cand`'s index-wise by members of `span (range base)`
keeps the augmented family independent. It is the "adding to each candidate row a combination of
the base rows preserves rank" fact; the proof passes to `M ⧸ span (range base)` (where `cand` and
`cand'` have the same image) and rebuilds via `LinearIndependent.sumElim_of_quotient`. The
rigidity project's general-`d` Case III consumes it (in the `Sum.elim (Sum.elim rn cand) ro`
shape, `RigidityMatrix/Basic.lean`'s `linearIndependent_sumElim_candidateBlock_swap`) as the
length-`d` chain row-correspondence.

`linearIndependent_sum_smul_ne_zero` is the elementary fact that a finite linear
combination `∑ j, c j • v j` of a linearly independent family with at least one
nonzero coefficient `c i ≠ 0` is nonzero (the contrapositive of
`Fintype.linearIndependent_iff`: a vanishing combination forces all coefficients to
vanish, in particular `c i`).

`exists_smul_combination_eq_sub_of_mem_span_image_compl` turns a membership
`w ∈ span (v '' {j ≠ i})` into the explicit unit-normalized vanishing combination it
witnesses: over a nontrivial ring, for an independent family `v` and an index `i`, if
`w` lies in the span of the other vectors `{v j : j ≠ i}` then there is a coefficient
family `lam` with `lam i = 1` and `∑ j, lam j • v j = v i - w` — and this combination is
nonzero (the unit coefficient at `i`, via `linearIndependent_sum_smul_ne_zero`). It is
the coefficient-extraction (`Fintype.mem_span_image_iff_exists_fun` to get the `j ≠ i`
coefficients, extended by `lam i = 1`) the rigidity project's redundant-row decomposition
consumes (KT eqs. (6.24)/(6.25): the redundant row `v i` minus its expansion `w` over the
others is the candidate vector `r̂`, with the redundant index's coefficient pinned to `1`).

`LinearIndepOn.units_smul` is the `LinearIndepOn` companion of mathlib's own
`LinearIndependent.units_smul`/`units_smul_iff` (stated only for the unrestricted
`LinearIndependent`): rescaling each member of an independent-on-`s` family `v` by a
per-index unit `w i` keeps it independent on `s`. Immediate from the mathlib lemma applied
to the restricted family `s.restrict v`, since `LinearIndepOn` unfolds to exactly that. The
rigidity project's cut-arm transport (`Molecule/Pencil/Motive.lean`, Phase 39 W5-L5) uses
it for the per-body projective-scalar congruence a chart reproduction needs.

Promotion to mathlib: copy-paste into `Mathlib/LinearAlgebra/LinearIndependent/Basic.lean`
(it imports `linearIndependent_sum` there, `disjoint_span_singleton'` from `Span.Basic`,
`Fintype.linearIndependent_iff`, and `Fintype.mem_span_image_iff_exists_fun` from
`Finsupp.LinearCombination`). `linearIndependent_sumElim_block_swap` additionally needs
`Submodule.mkQ`/`ker_mkQ` from `Quotient.Basic` and `LinearIndependent.sumElim_of_quotient`
from `Dimension.Constructions` (so it would land downstream of those, not in `Basic`).
`LinearIndepOn.units_smul` needs only `LinearIndependent.units_smul` itself, already in the
same file.

See `notes/FRICTION.md` *Mirrored* and `DESIGN.md` *Mirror directory*.
-/

@[expose] public section

/-- **A linear combination of an independent family with a nonzero coefficient is
nonzero.** Over a ring, for a linearly independent family `v : ι → M` indexed by a
`Fintype` and coefficients `c : ι → R` with some `c i ≠ 0`, the combination
`∑ j, c j • v j` is nonzero. (Contrapositive of `Fintype.linearIndependent_iff`: a
vanishing combination forces every coefficient — in particular `c i` — to be `0`.) -/
theorem linearIndependent_sum_smul_ne_zero {R M ι : Type*} [Ring R] [AddCommGroup M]
    [Module R M] [Fintype ι] {v : ι → M} (hv : LinearIndependent R v) {c : ι → R} {i : ι}
    (hci : c i ≠ 0) : ∑ j, c j • v j ≠ 0 :=
  fun h => hci (Fintype.linearIndependent_iff.1 hv c h i)

/-- **The unit-normalized vanishing combination witnessed by a span-of-the-others
membership.** Over a nontrivial ring, for a linearly independent family `v : ι → M`
(indexed by a `Fintype`), an index `i`, and a vector `w` in the span of the *other*
vectors `{v j : j ≠ i}`, there is a coefficient family `lam : ι → R` with `lam i = 1`
whose combination `∑ j, lam j • v j` equals `v i - w` — and is nonzero (it carries the
unit coefficient `1` at the independent index `i`,
`linearIndependent_sum_smul_ne_zero`). The coefficients on `{j ≠ i}` come from
`Fintype.mem_span_image_iff_exists_fun` (negated), extended by `lam i = 1`. -/
theorem exists_smul_combination_eq_sub_of_mem_span_image_compl {R M ι : Type*} [Ring R]
    [Nontrivial R] [AddCommGroup M] [Module R M] [Fintype ι] {v : ι → M}
    (hv : LinearIndependent R v) {i : ι} {w : M}
    (hw : w ∈ Submodule.span R (v '' {j | j ≠ i})) :
    ∃ lam : ι → R, lam i = 1 ∧ (∑ j, lam j • v j) = v i - w ∧ (∑ j, lam j • v j) ≠ 0 := by
  classical
  obtain ⟨c, hc⟩ := (Fintype.mem_span_image_iff_exists_fun R).1 hw
  set c' : ι → R := fun j => if hj : j = i then 0 else c ⟨j, hj⟩ with hc'def
  have hc'sum : ∑ j, c' j • v j = w := by
    have key : ∑ j ∈ Finset.univ.filter (· ≠ i), c' j • v j = w := by
      rw [Finset.sum_subtype (p := fun j => j ≠ i) (Finset.univ.filter (· ≠ i))
        (fun x => by simp) (fun j => c' j • v j), ← hc]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      simp only [hc'def, dif_neg a.2, Subtype.coe_eta]
    rw [← key]
    refine (Finset.sum_subset (Finset.filter_subset _ _) (fun j _ hj => ?_)).symm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hj
    simp [hc'def, hj]
  set lam : ι → R := fun j => if j = i then 1 else -c' j with hlamdef
  have hlam_i : lam i = 1 := by simp [hlamdef]
  refine ⟨lam, hlam_i, ?_, linearIndependent_sum_smul_ne_zero hv (hlam_i ▸ one_ne_zero)⟩
  rw [eq_sub_iff_add_eq, ← hc'sum, ← Finset.sum_add_distrib,
    show v i = ∑ j, (if j = i then (1 : R) else 0) • v j by simp [Finset.sum_ite_eq']]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← add_smul]
  by_cases hj : j = i <;> simp [hlamdef, hj, hc'def]

/-- **The span of a family meets a linear map's kernel trivially when the composite is
independent.** Over a ring, if `f ∘ v` is linearly independent then
`Disjoint (span R (range v)) (ker f)`. Converse companion of `LinearIndependent.map` (which
proves `f ∘ v` independent from `v` independent and this disjointness); here the disjointness
is read back off the composite's independence: an element of the intersection is a finite
combination `∑ cᵢ • v i` sent to `0` by `f`, so `∑ cᵢ • f (v i) = 0`, forcing every `cᵢ = 0`
by independence of `f ∘ v`, hence the element is `0`. -/
theorem LinearIndependent.disjoint_span_range_ker {R M M' ι : Type*} [Ring R]
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    {v : ι → M} {f : M →ₗ[R] M'} (h : LinearIndependent R (f ∘ v)) :
    Disjoint (Submodule.span R (Set.range v)) (LinearMap.ker f) := by
  rw [Submodule.disjoint_def]
  intro x hx hxk
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hx
  obtain ⟨c, rfl⟩ := hx
  rw [LinearMap.mem_ker, ← Finsupp.linearCombination_apply,
    Finsupp.apply_linearCombination] at hxk
  rw [linearIndependent_iff] at h
  rw [h c hxk]; simp

variable {K M ι : Type*} [DivisionRing K] [AddCommGroup M] [Module K M]

/-- **Appending one vector to an independent family stays independent iff the vector is
fresh.** Over a division ring, for a linearly independent family `v : ι → M` and a vector
`x : M`, the augmented family `Sum.elim v (fun _ : Unit => x)` is linearly independent iff
`x ∉ Submodule.span K (Set.range v)`. -/
theorem linearIndependent_sumElim_unit_iff {v : ι → M} (hv : LinearIndependent K v) (x : M) :
    LinearIndependent K (Sum.elim v (fun _ : Unit => x)) ↔
      x ∉ Submodule.span K (Set.range v) := by
  rw [linearIndependent_sum]
  -- The `inr`-side range span is `K ∙ x`; the `inl`-side range span is `span (range v)`.
  have hspan : Submodule.span K (Set.range ((Sum.elim v fun _ : Unit => x) ∘ Sum.inr))
      = K ∙ x := by simp [Set.range_const]
  have hcomp : Submodule.span K (Set.range ((Sum.elim v fun _ : Unit => x) ∘ Sum.inl))
      = Submodule.span K (Set.range v) := by congr 1
  constructor
  · rintro ⟨_, hr, hdisj⟩
    have hx : x ≠ 0 := by simpa using hr.ne_zero (default : Unit)
    rw [hspan, hcomp] at hdisj
    exact (Submodule.disjoint_span_singleton' hx).1 hdisj
  · intro hx
    have hx0 : x ≠ 0 := fun h => hx (h ▸ Submodule.zero_mem _)
    refine ⟨by simpa using hv,
      LinearIndependent.of_subsingleton (default : Unit) (by simpa using hx0), ?_⟩
    rw [hspan, hcomp]
    exact (Submodule.disjoint_span_singleton' hx0).2 hx

/-- **A block row operation preserves independence: swapping a candidate block by members
of the base block's span.** Over a division ring, for a base family
`base : ι → M` and a candidate block `cand : ιc → M` with `Sum.elim base cand` linearly
independent, if a second candidate block `cand'` differs from `cand` index-wise by members of
`span (range base)` (each `cand' i - cand i ∈ span (range base)`), then `Sum.elim base cand'`
is again linearly independent.

This is the block form of "adding to each candidate row a combination of the base rows does
not change the rank." The proof passes to the quotient `Q := M ⧸ span (range base)`: there
`mkQ ∘ cand' = mkQ ∘ cand` (the differences vanish in `Q`), and `Sum.elim base cand`
independence makes `mkQ ∘ cand` independent in `Q`, so `LinearIndependent.sumElim_of_quotient`
rebuilds `Sum.elim base cand'` from the (submodule-valued) base block and the unchanged
quotient block. -/
theorem linearIndependent_sumElim_block_swap {ιc : Type*}
    {base : ι → M} {cand cand' : ιc → M}
    (hindep : LinearIndependent K (Sum.elim base cand))
    (hdiff : ∀ i, cand' i - cand i ∈ Submodule.span K (Set.range base)) :
    LinearIndependent K (Sum.elim base cand') := by
  set P : Submodule K M := Submodule.span K (Set.range base) with hP
  -- The base block lands in `P` and is independent there (a sub-block of the augmented family).
  have hbase : LinearIndependent K base := by
    have := hindep.comp Sum.inl Sum.inl_injective
    simpa using this
  have hbaseP : ∀ i, base i ∈ P := fun i => Submodule.subset_span ⟨i, rfl⟩
  set f : ι → P := fun i => ⟨base i, hbaseP i⟩ with hf
  have hfindep : LinearIndependent K f :=
    LinearIndependent.of_comp P.subtype (by simpa [hf, Function.comp_def] using hbase)
  -- The quotient map `π : M → M ⧸ P`.
  set π := P.mkQ with hπ
  -- In the quotient `Q = M ⧸ P`, the candidate block's image is independent.
  have hcandQ : LinearIndependent K (π ∘ cand) := by
    have hsplit := linearIndependent_sum.1 hindep
    have hci : LinearIndependent K cand := by simpa using hsplit.2.1
    have hdisj : Disjoint P (Submodule.span K (Set.range cand)) := by
      simpa [hP] using hsplit.2.2
    rw [linearIndependent_iff'] at hci ⊢
    intro s g hg i hi
    -- `π (∑ g_i cand_i) = 0`, so `∑ g_i cand_i ∈ P ∩ span (range cand) = 0`.
    have hmem : (∑ l ∈ s, g l • cand l) ∈ P := by
      rw [← Submodule.ker_mkQ P, LinearMap.mem_ker, map_sum]
      simp only [map_smul]
      simpa [hπ, Function.comp_def] using hg
    have hspan : (∑ l ∈ s, g l • cand l) ∈ Submodule.span K (Set.range cand) :=
      Submodule.sum_mem _ fun l _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
    have hzero : (∑ l ∈ s, g l • cand l) = 0 :=
      (Submodule.disjoint_def.1 hdisj) _ hmem hspan
    exact hci s g hzero i hi
  -- `cand'` has the same quotient image (the differences vanish), so it is independent in `Q`.
  have heq : (π ∘ cand') = π ∘ cand := by
    funext i
    rw [Function.comp_apply, Function.comp_apply, ← sub_eq_zero, ← map_sub, hπ, P.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    simpa [hP] using hdiff i
  have hcand'Q : LinearIndependent K (π ∘ cand') := heq ▸ hcandQ
  -- Rebuild `Sum.elim base cand'` from the base block (in `P`) and the quotient block.
  have hrebuild := hfindep.sumElim_of_quotient cand'
    (by simpa [hπ, Function.comp_def, P.mkQ_apply] using hcand'Q)
  simpa [hf] using hrebuild

/-- **A unit-rescaling congruence for `LinearIndepOn`.** Over a ring, for a family `v : ι → M`
independent on a set `s` and a per-index unit rescaling `w : ι → Rˣ`, the rescaled family `w • v`
is again independent on `s`. The `LinearIndepOn` companion of mathlib's own
`LinearIndependent.units_smul` (stated only for the unrestricted `LinearIndependent`); immediate
from that lemma applied to the restricted family `s.restrict v`, since `LinearIndepOn R v s`
unfolds to exactly `LinearIndependent R (s.restrict v)` and restriction commutes with the
pointwise `•`. -/
theorem LinearIndepOn.units_smul {R M ι : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {v : ι → M} {s : Set ι} (hv : LinearIndepOn R v s) (w : ι → Rˣ) :
    LinearIndepOn R (w • v) s :=
  LinearIndependent.units_smul hv fun x : s => w x
