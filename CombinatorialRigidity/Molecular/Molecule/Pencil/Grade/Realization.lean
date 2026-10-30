/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Statement

/-!
# A screw element through a subspace

The realization chain of `sec:pencil-d` (`blueprint/src/chapter/pencil-d.tex`), whose leaf is
`def:extensor-through-flat`: a screw element passes through a subspace `A` of `K^(k+2)` when it is
the extensor of `k` vectors whose span contains `A`. This is `ExtensorThroughPoint`
(`Pencil/Statement.lean`) with a subspace in place of the point, and it agrees with it on the span
of one vector (`lem:extensor-through-flat-point`).

## Main results

* `ExtensorThroughSubspace`: `def:extensor-through-flat`.
* `extensorThroughSubspace_span_singleton_iff`: `lem:extensor-through-flat-point`.
-/

@[expose] public section

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K]

/-- **A screw element passes through a subspace** (`def:extensor-through-flat`): a `k`-extensor
`C ∈ ScrewSpace K k` passes through the subspace `A` of `K^(k+2)` when it is the extensor of `k`
vectors whose span contains `A`. It is `ExtensorThroughPoint` with a subspace in place of the point,
with the same form of witness, so a screw element that passes through a subspace is decomposable.
The zero element is not excluded: a family of `k` vectors that is dependent has extensor `0`, so
`0` passes through each subspace spanned by such a family, and a nonzero hinge is asked for
separately (as for `ExtensorThroughPoint`, and `HasCoplanarPanelRealization`). -/
def ExtensorThroughSubspace {k : ℕ} (C : ScrewSpace K k) (A : Submodule K (Fin (k + 2) → K)) :
    Prop :=
  ∃ p : Fin k → Fin (k + 2) → K,
    C.val = extensor p ∧ A ≤ Submodule.span K (Set.range p)

/-- **Through the span of one vector** (`lem:extensor-through-flat-point`): a screw element passes
through the span of `q` exactly when it passes through the point `q`. -/
theorem extensorThroughSubspace_span_singleton_iff {k : ℕ} (C : ScrewSpace K k)
    (q : Fin (k + 2) → K) :
    ExtensorThroughSubspace C (Submodule.span K {q}) ↔ ExtensorThroughPoint C q := by
  simp only [ExtensorThroughSubspace, ExtensorThroughPoint, Submodule.span_singleton_le_iff_mem]

end CombinatorialRigidity.Molecular
