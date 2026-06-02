/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import Mathlib.Combinatorics.Graph.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Body-bar frameworks (`def:body-bar-framework`)

Phase 15. Following Whiteley 1988 (*The union of matroids and the rigidity of
frameworks*, SIAM J. Disc. Math. **1**) §3 and Tay 1984 (*Rigidity of
multi-graphs. I*, J. Combin. Theory Ser. B **36**) §5, a **body-bar framework**
in `ℝⁿ` on a multigraph `G : Graph α β` pairs `G` with a *placement* assigning
each bar `e ∈ E(G)` a two-extensor (Plücker) coordinate in `ℝᵈ`, where
`d = n(n+1)/2` is the dimension of the space of infinitesimal rigid motions of
`ℝⁿ` (translations + infinitesimal rotations).

A two-extensor is a point of the Plücker embedding of `Gr(2, n+1)` into `ℝᵈ`;
geometrically it records the line carrying the bar together with its direction.
Per ROADMAP §15 / `notes/Phase15.md`, we handle the Plücker coordinates
**inline** with **degenerate coordinates permitted** — i.e. the placement is an
unconstrained map into `ℝᵈ`, not a map into the Plücker variety. This is the
"existence-of-realization" scope: Tay's theorem (`thm:tay-witness`) is witnessed
by the standard-basis specialization `b_e = e_{j(e)}`, whose coordinates are
themselves degenerate two-extensors, so no variety-membership constraint is
needed for the existence direction (Whiteley's "almost all realizations are
rigid" lift via the irreducible Plücker variety is deferred — see ROADMAP §15).

## Main definitions

* `Graph.bodyBarDim` — the body-bar dimension `d = n(n+1)/2` of `ℝⁿ`.
* `Graph.BodyBarFramework` — a body-bar framework: a multigraph `G` together
  with a placement `E(G) → EuclideanSpace ℝ (Fin (bodyBarDim n))`.

## Project context

See `ROADMAP.md` §15, `notes/Phase15.md`, and the
§`sec:body-bar-framework` subsection of `blueprint/src/chapter/body-bar.tex`.
The body-bar **rigidity map** (`def:rigidity-map-body-bar`) and **infinitesimal
rigidity** (`def:infinitesimally-rigid-body-bar`) build on this definition, en
route to **Tay's theorem** (`thm:tay-witness`).
-/

namespace Graph

variable {α β : Type*}

/-- The **body-bar dimension** of `ℝⁿ`: `d = n(n+1)/2`, the dimension of the
space of infinitesimal rigid motions of `ℝⁿ` (the `n` translations plus the
`n(n-1)/2` independent infinitesimal rotations). Equivalently the dimension of
the Plücker space `ℝᵈ` into which two-extensors of `ℝⁿ⁺¹` embed; a bar in `ℝⁿ`
carries a two-extensor coordinate in this space. -/
def bodyBarDim (n : ℕ) : ℕ := n * (n + 1) / 2

/-- A **body-bar framework** in `ℝⁿ` on a multigraph `G : Graph α β`
(Whiteley 1988 §3, Tay 1984 §5; `def:body-bar-framework`): the multigraph `G`
together with a **placement** `p` assigning each bar `e ∈ E(G)` a two-extensor
(Plücker) coordinate in `ℝᵈ`, `d = n(n+1)/2` (`Graph.bodyBarDim n`).

The placement is an unconstrained map into `EuclideanSpace ℝ (Fin (bodyBarDim n))`
— degenerate two-extensors are permitted, so no Plücker-variety membership
constraint is imposed (existence-of-realization scope; see the module
docstring). The bundled `G` matches the Phase-13/14 `Graph`-native style, where
the multigraph carries the combinatorial data the matroid-union route consumes. -/
structure BodyBarFramework (n : ℕ) (α β : Type*) where
  /-- The underlying multigraph: bodies are vertices, bars are edges. -/
  graph : Graph α β
  /-- The placement: each bar `e ∈ E(graph)` gets a two-extensor coordinate in
  `ℝᵈ`, `d = n(n+1)/2`. Degenerate coordinates are permitted. -/
  placement : E(graph) → EuclideanSpace ℝ (Fin (bodyBarDim n))

end Graph
