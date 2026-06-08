/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.Module.Torsion.Field

/-!
# Upstream candidates: independent-family facts

Three facts about linearly independent families, all upstream-eligible.

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

Promotion to mathlib: copy-paste into `Mathlib/LinearAlgebra/LinearIndependent/Basic.lean`
(it imports `linearIndependent_sum` there, `disjoint_span_singleton'` from `Span.Basic`,
`Fintype.linearIndependent_iff`, and `Fintype.mem_span_image_iff_exists_fun` from
`Finsupp.LinearCombination`).

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
