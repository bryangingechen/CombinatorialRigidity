/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.X0
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.CoverageTheoremS

/-!
# The distinct main-component statement (Phase 40n MOTIVES, M0)

`X0Dist` needs only landed pieces, with no hypothesis on the number of edge labels `β`: the
covering theorem (`Graph.X0Attains.of_twoEdgeConnected`, `MainComponent/CoverageTheoremS.lean`)
gives that the general configuration of a simple two-edge-connected graph on at least three bodies
attains, and one attaining configuration is already an adjacent-distinct pencil realization
(`Graph.X0Attains.hasDistinctPencilRealization`, `MainComponent/Configuration.lean`). `X0Gen` is
discharged separately, inside the pencil reduction's own induction (route B; MOTIVES-EARS,
MOTIVES-REDUCE+CLOSE).

## Main statements

* `x0Dist` — the distinct main-component statement.

See `notes/Phase40n.md`, `notes/pencil/workbook/K-main-MC19.md` (route B, (MC-183)–(MC-187)), and
`blueprint/src/chapter/main-component.tex` (`sec:main-component-statements`).
-/

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

/-- **The distinct main-component statement** (`lem:pencil-x0-distinct-statement`; Phase 40n
MOTIVES M0). Every simple two-edge-connected multigraph on at least three bodies has a pencil
realization at the deficiency rank with adjacent concurrency points distinct, over an infinite
field: one attaining configuration of the covering theorem is such a realization, with no
hypothesis on the number of edge labels. -/
theorem x0Dist [Finite α] [Finite β] [Infinite K] : X0Dist K α β :=
  fun _ hS hV htec => (Graph.X0Attains.of_twoEdgeConnected hS hV htec).hasDistinctPencilRealization

end CombinatorialRigidity.Molecular
