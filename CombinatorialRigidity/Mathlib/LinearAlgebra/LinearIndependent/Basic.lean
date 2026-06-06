/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Algebra.Module.Torsion.Field

/-!
# Upstream candidate: extending an independent family by one vector

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

Promotion to mathlib: copy-paste into `Mathlib/LinearAlgebra/LinearIndependent/Basic.lean`
(it imports both `linearIndependent_sum` there and `disjoint_span_singleton'` from
`Span.Basic`).

See `notes/FRICTION.md` *Mirrored* and `DESIGN.md` *Mirror directory*.
-/

@[expose] public section

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
