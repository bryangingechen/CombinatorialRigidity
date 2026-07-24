/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.Motive

/-!
# The conditioned-pair arm re-derivations and successor (Phase 39 PENCIL, W5-L5)

New leaf, opened for the W5-L5 milestone (`notes/Phase39.md` *Hand-off*,
`notes/Phase39-design.md` §"W5 leaf decomposition" L5): the W3-L7 successor
`pencil_conjecture_of_arms_pair` (spiked in the design doc; red node
`thm:pencil-conditional-realization-pair` in `pencil.tex`) needs each of
`Graph.pencil_reduction`'s loop/base/cut arms re-derived against the `PencilPair`
conditioned-pair motive (`Molecule/Pencil/Motive.lean`), since the bare-motive arms
(`Molecule/Pencil/Arms.lean`, W3) only ever produce/consume `HasPencilRealization`, not the
generic conjunct the pair's first component asks for. Builds on `Molecule/Pencil/Motive.lean`
(hence transitively on `Statement.lean`/`Arms.lean`); does not need the grade-0 chart
(`Chart.lean`/`Engine.lean`/`Reseed.lean`) — the arm re-derivations below are pure
graph-surgery + the motive's own vacuity/forgetful facts, not chart constructions.

This leaf lands the loop arm first (free, per the design doc: a loop already breaks
`PencilNondegFeasible`, so its generic obligation is vacuous). The base arm's generic half
(small: single-edge/empty producers, parallel classes nondegeneracy-infeasible hence vacuous),
the cut arm's generic half (moderate: mirrors the landed panel-side
`case_cut_edge_realization_gp_gen`, reusing the W3-L4 transport/nondegeneracy/rank infra), and the
successor assembly itself remain open — see `notes/Phase39.md` *Hand-off*.

See `notes/Phase39.md`, `notes/Phase39-design.md` (§"W5 leaf decomposition"), and
`blueprint/src/chapter/pencil.tex`.
-/

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K]
variable {α β : Type*}

/-! ## W5-L5: the loop arm against the conditioned-pair motive (Phase 39 PENCIL) -/

/-- **The loop arm of the pencil reduction, conditioned-pair motive** (Phase 39 W5-L5; the
`PencilPair` analogue of the bare-motive `hasPencilRealization_of_isLoopAt`, W3-L3). Let `e` be a
loop of `G` at `v`. If `G ＼ {e}` satisfies the conditioned pair at rank `n`, so does `G`: the bare
half is `hasPencilRealization_of_isLoopAt` applied to the recursive bare half unchanged, and the
generic half is **free** — `G` has a loop at `v`, so `not_pencilNondegFeasible_of_isLoopAt` already
refutes `PencilNondegFeasible K G`, making the implication `PencilNondegFeasible K G →
HasGenericPencilRealization K n G` vacuously true without consulting `hrec` at all. This is exactly
the design doc's "loop arm free" verdict (`notes/Phase39-design.md` §"W5 leaf decomposition" L5). -/
theorem pencilPair_of_isLoopAt {G : Graph α β} {n : ℕ} {e : β} {v : α}
    (hloop : G.IsLoopAt e v) (hrec : PencilPair K n (G ＼ ({e} : Set β))) :
    PencilPair K n G :=
  ⟨fun hfeas => absurd hfeas (not_pencilNondegFeasible_of_isLoopAt hloop),
    hasPencilRealization_of_isLoopAt hloop hrec.2⟩

end CombinatorialRigidity.Molecular
