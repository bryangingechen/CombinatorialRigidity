/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.Combinatorics.Graph.Delete

/-!
# Upstream candidate: `Graph.induce` idempotence along nested vertex sets

Mathlib's multigraph `Graph.induce` (`Mathlib/Combinatorics/Graph/Delete.lean`)
carries `induce_vertexSet` (`G.induce V(G) = G`) but no composition law for two
successive induces. The lemma below is the idempotence `(G.induce S).induce T =
G.induce T` for `T ⊆ S`, which the combinatorial-rigidity project's cut-edge
deficiency bookkeeping needs (Phase 39 W5-L5: the edge-closed side
`Gᵢ⁺ = G.induce (Vᵢ ∪ {far})` re-induced on its own side `Vᵢ` recovers
`G.induce Vᵢ`).

The Lean namespace is the upstream one (`Graph`), so promotion to mathlib is a
copy-paste alongside `Graph.induce_vertexSet`. See `DESIGN.md` "Mirror
directory".

## Contents (target file: `Mathlib/Combinatorics/Graph/Delete.lean`)

* `induce_induce_of_subset` — `(G.induce S).induce T = G.induce T` for `T ⊆ S`.
-/

@[expose] public section

namespace Graph

variable {α β : Type*}

/-- Inducing twice along nested vertex sets collapses to the inner induce:
`(G.induce S).induce T = G.induce T` when `T ⊆ S`. Both sides have vertex set `T`
definitionally, and a `T`-internal link of `G.induce S` is exactly a `T`-internal
link of `G`, since `T ⊆ S` makes the outer `S`-membership constraints redundant. -/
lemma induce_induce_of_subset (G : Graph α β) {S T : Set α} (hTS : T ⊆ S) :
    (G.induce S).induce T = G.induce T :=
  Graph.ext rfl fun e x y => by
    simp only [induce_isLink]
    exact ⟨fun ⟨⟨hl, _, _⟩, hx, hy⟩ => ⟨hl, hx, hy⟩,
      fun ⟨hl, hx, hy⟩ => ⟨⟨hl, hTS hx, hTS hy⟩, hx, hy⟩⟩

end Graph
