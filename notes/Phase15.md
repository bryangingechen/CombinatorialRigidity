# Phase 15 — Body-bar Tay theorem (existence form) (work log)

**Status:** in progress (just opened).

## Current state

The leaf-most red node `def:body-bar-framework` is **green**:
`BodyBar/Framework.lean` ships `Graph.bodyBarDim n = n(n+1)/2` and the
`Graph.BodyBarFramework n α β` structure (a multigraph `graph : Graph α β`
paired with an unconstrained `placement : E(graph) → EuclideanSpace ℝ
(Fin (bodyBarDim n))` — degenerate two-extensors permitted, no Plücker-
variety constraint, per the existence-of-realization scope). Blueprint
node flipped (`\lean{...}` + `\leanok`); file added to the top-level
`CombinatorialRigidity.lean` import aggregator. This is the original
Phase-12 target, unblocked by the Phase 12–14 chain. Forward-mode phase:
the lemma index lives in `blueprint/src/chapter/body-bar.tex`
§`sec:body-bar-framework` and §`sec:body-bar-tay`. All prerequisite nodes
(`thm:k-frame-union-cycle`, `thm:tutte-nash-williams`,
`cor:k-spanning-trees`, the whole `sec:body-bar-k-frame` and
`sec:body-bar-tree-packing` subsections) are green.

The chapter has **three red nodes** left, in dependency order:
- `def:rigidity-map-body-bar` (`\uses{def:body-bar-framework}`)
- `def:infinitesimally-rigid-body-bar` (`\uses{def:rigidity-map-body-bar}`)
- `thm:tay-witness` (the target; `\uses` the three defs +
  `def:graph-sparse`, `thm:tutte-nash-williams`, `cor:k-spanning-trees`;
  proof `\uses{thm:k-frame-union-cycle, …}`).

**Next concrete commit:** the next leaf-most red node
`def:rigidity-map-body-bar` in `BodyBar/Framework.lean` — the
bar-constraint rigidity map, an `ℝ`-linear map from body motions
(`V(graph) → ℝ^d`) to bar constraints (`E(graph) → ℝ`), one row per bar
(Whiteley §3). Add/flip its `\lean{...}` + `\leanok` in the same commit.
Then `def:infinitesimally-rigid-body-bar` (kernel = `d`-dim trivial screw
motions, rank `= d·b − d`).

## Architectural choices made up front

Migrated from the old Phase-12 notes / ROADMAP §15:

- **Carrier = mathlib core `Graph α β`** (`Mathlib/Combinatorics/Graph/
  Basic.lean`), matching Phases 13–14 (on which `cycleMatroid` sits);
  Phases 1–11 stay on `SimpleGraph`. See `DESIGN.md` *Migrating
  Phases 1–11 …*.
- **Plücker / two-extensor coordinates handled inline**, standard-basis
  specialization only — no separate phase, no irreducible-variety
  infrastructure.
- **Existence-of-realization form only.** Whiteley's "almost all
  realizations are rigid" lift (Proposition 6, irreducible-variety
  machinery) is **deferred**, re-assessed when the body-hinge phase
  (Phase 16) opens.
- **Graph-level defs under `namespace Graph`** (dot-notation on
  `G : Graph α β`); framework defs under `CombinatorialRigidity` /
  `BodyBar`. Departs from the "everything under `SimpleGraph`/
  `CombinatorialRigidity`" convention (Phases 13–15). See ROADMAP §15
  and the Phases-12–15 exception in ROADMAP *Engineering conventions*.

## Lemma checklist

Leaf-level to-do list = the `body-bar.tex` §`sec:body-bar-framework` +
§`sec:body-bar-tay` dep-graph (4 red nodes as of phase-open).

- [x] `def:body-bar-framework` — body-bar framework (placement = two-extensor
      per bar). `BodyBar/Framework.lean` (`Graph.bodyBarDim`,
      `Graph.BodyBarFramework`).
- [ ] `def:rigidity-map-body-bar` — bar-constraint rigidity map.
      **Next concrete commit.** `BodyBar/Framework.lean`.
- [ ] `def:infinitesimally-rigid-body-bar` — rank `= d·b − d`.
- [ ] `thm:tay-witness` — Tay's theorem, existence form (Whiteley Thm 8).
      Standard-basis specialization of `thm:k-frame-union-cycle`'s reverse
      direction lifted from indeterminate to real coefficients.

## Decisions made during this phase

- **`BodyBarFramework` is a bundled `structure`, not an `abbrev` for the
  placement type.** Phase-4 `SimpleGraph.Framework` is an `abbrev` for `V →
  EuclideanSpace …` because the graph `G` is a separate explicit argument
  everywhere downstream. Here the multigraph carries the combinatorial data
  the matroid-union route (Phases 13–14) consumes, so bundling `graph` with
  `placement : E(graph) → ℝ^d` keeps the body-bar pair as one object and
  matches the `Graph`-native style. Revisit if the rigidity-map def wants
  `G` and `p` split.
- **`bodyBarDim n := n*(n+1)/2` as a plain `def`.** ℕ-division is exact here
  (`n(n+1)` always even), and the Tay count `|E| = d(b−1)` only needs `d` as
  an opaque ℕ. No need for a `Nat.choose`-style reformulation yet; revisit
  if a proof needs the evenness / closed form.
- **Placement unconstrained (degenerate two-extensors permitted).** No
  Plücker-variety membership in the type — the existence-of-realization
  scope (ROADMAP §15) is witnessed by standard-basis `b_e`, themselves
  degenerate two-extensors. The "almost all realizations" lift is deferred.

## Blockers / open questions

- **Plücker / two-extensor encoding in Lean.** The reverse direction of
  `thm:k-frame-union-cycle` (`Graph.linearIndepOn_kFrameRow_of_isSparse_restrict`)
  already specializes the indeterminate row coefficients to a block-diagonal
  forest-packing pattern over `ℝ`; the body-bar framework's two-extensor
  placement should reuse that specialization (standard-basis `b_e = e_{j(e)}`
  per the proof sketch in `thm:tay-witness`). Confirm whether the existing
  `specRow` / `forestEval` machinery from Phase 14 lifts directly or needs a
  thin Plücker-coordinate wrapper. Assess once `def:body-bar-framework` lands.

## Hand-off / next phase

`def:body-bar-framework` is green (`BodyBar/Framework.lean`). **Next
concrete commit:** formalize the next leaf-most red node
`def:rigidity-map-body-bar` in `BodyBar/Framework.lean` (the bar-constraint
rigidity map, one row per bar), then flip its blueprint node green
(`\lean{...}` + `\leanok`) in the same commit. Proceed up the dep-graph:
`def:infinitesimally-rigid-body-bar` → `thm:tay-witness`. The phase closes
when `thm:tay-witness` is green.

Follow-on: **Phase 16** (body-hinge / panel-hinge Tay–Whiteley), en route
to **Phase 17** (molecular conjecture, Katoh–Tanigawa 2011). Neither is
opened.
