/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.Algebra.Module.Submodule.Union

/-!
# Upstream candidate: a submodule is never covered by two proper subsubmodules

Mathlib's `Mathlib/Algebra/Module/Submodule/Union.lean` proves that a module
over an *infinite* field is not a finite union of proper submodules
(`Submodule.exists_forall_notMem_of_forall_ne_top`) and the cardinality-refined
`Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt`. For exactly **two**
submodules no size hypothesis on the scalars is needed at all: the classical
exchange argument (`u ∈ S \ U`, `w ∈ S \ W`, else `u + w` escapes both) works
over any ring. The relative form below — an element of `S` avoiding both `U`
and `W` whenever neither contains `S` — is the workhorse the
combinatorial-rigidity project's repositioning constructions use to pick frame
vectors subject to two span avoidances over an arbitrary field (Phase 39
W5-L5, the cut arm's strengthened repositioning lemma).

The Lean namespace is the upstream one (`Submodule`), so promotion to mathlib
is a copy-paste alongside its union lemmas. See `DESIGN.md` "Mirror directory".

## Contents (target file: `Mathlib/Algebra/Module/Submodule/Union.lean`)

* `Submodule.exists_mem_notMem_notMem` — if `¬ S ≤ U` and `¬ S ≤ W` then some
  `z ∈ S` lies in neither `U` nor `W`.
-/

@[expose] public section

namespace Submodule

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- **A submodule is never covered by two submodules not containing it** (no
hypothesis on the scalar ring — contrast the infinite-field
`Submodule.exists_forall_notMem_of_forall_ne_top`): if `¬ S ≤ U` and
`¬ S ≤ W`, some `z ∈ S` avoids both `U` and `W`. Exchange argument: pick
`u ∈ S \ U` and `w ∈ S \ W`; if either also avoids the other submodule we are
done, and otherwise `u + w` avoids both (membership of the sum in `U` would
force `u = (u + w) - w ∈ U`, and in `W` would force `w ∈ W`). -/
theorem exists_mem_notMem_notMem {S U W : Submodule R M}
    (hU : ¬ S ≤ U) (hW : ¬ S ≤ W) : ∃ z ∈ S, z ∉ U ∧ z ∉ W := by
  obtain ⟨u, huS, huU⟩ := SetLike.not_le_iff_exists.mp hU
  obtain ⟨w, hwS, hwW⟩ := SetLike.not_le_iff_exists.mp hW
  by_cases huW : u ∈ W
  · by_cases hwU : w ∈ U
    · refine ⟨u + w, S.add_mem huS hwS, fun h => huU ?_, fun h => hwW ?_⟩
      · have := U.sub_mem h hwU; simpa using this
      · have := W.sub_mem h huW; simpa using this
    · exact ⟨w, hwS, hwU, hwW⟩
  · exact ⟨u, huS, huU, huW⟩

end Submodule
