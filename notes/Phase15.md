# Phase 15 — Body-bar Tay theorem (existence form) (work log)

**Status:** in progress (just opened).

## Current state

Two leaf nodes are **green** in `BodyBar/Framework.lean`:
- `def:body-bar-framework` — `Graph.bodyBarDim n = n(n+1)/2` and the
  `Graph.BodyBarFramework n α β` structure (a multigraph `graph : Graph α β`
  paired with an unconstrained `placement : E(graph) → EuclideanSpace ℝ
  (Fin (bodyBarDim n))` — degenerate two-extensors permitted, no Plücker-
  variety constraint, per the existence-of-realization scope).
- `def:rigidity-map-body-bar` — `Graph.BodyBarFramework.rigidityMap`, the
  bar-constraint `ℝ`-linear map from body motions (`Motion n α = α → ℝ^d`)
  to bar constraints (`E(graph) → ℝ`), one row per bar. Takes an explicit
  orientation `D : Graph.orientation F.graph` (apnelson1/Matroid's
  `Matroid.Graph.Matrix`) to supply each bar's ordered endpoints
  `(u, v) = D.dInc e`; the row is `m ↦ ⟪placement e, m u − m v⟫`. Built
  compositionally (`barRow` + `LinearMap.pi`) mirroring Phase 4's
  `edgeRow`/`RigidityMap`; `barRow_apply` / `rigidityMap_apply` are
  `@[simp] := rfl`. Blueprint node flipped (`\lean{...}` + `\leanok`).

`BodyBar/Framework.lean` is in the top-level `CombinatorialRigidity.lean`
import aggregator. Forward-mode phase: the lemma index lives in
`blueprint/src/chapter/body-bar.tex` §`sec:body-bar-framework` and
§`sec:body-bar-tay`. All `sec:body-bar-k-frame` /
`sec:body-bar-tree-packing` prerequisites are green.

The chapter has **two red nodes** left, in dependency order:
- `def:infinitesimally-rigid-body-bar` (`\uses{def:rigidity-map-body-bar}`)
- `thm:tay-witness` (the target; `\uses` the three defs +
  `def:graph-sparse`, `thm:tutte-nash-williams`, `cor:k-spanning-trees`;
  proof `\uses{thm:k-frame-union-cycle, …}`).

**Next concrete commit:** `def:infinitesimally-rigid-body-bar` in
`BodyBar/Framework.lean` — a body-bar framework on `b` bodies is
infinitesimally rigid when `rigidityMap D` has rank `d·b − d` (kernel =
the `d`-dim space of trivial screw motions). Add/flip its
`\lean{...}` + `\leanok` in the same commit.

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
- [x] `def:rigidity-map-body-bar` — bar-constraint rigidity map.
      `BodyBar/Framework.lean` (`BodyBarFramework.rigidityMap`, `barRow`).
- [ ] `def:infinitesimally-rigid-body-bar` — rank `= d·b − d`.
      **Next concrete commit.** `BodyBar/Framework.lean`.
- [ ] `thm:tay-witness` — Tay's theorem, existence form (Whiteley Thm 8).
      Standard-basis specialization of `thm:k-frame-union-cycle`'s reverse
      direction lifted from indeterminate to real coefficients.

## Decisions made during this phase

- **`rigidityMap` takes an explicit orientation `D`; motions are
  `Motion n α = α → ℝ^d` over the full vertex type.** The bar row is
  *antisymmetric* in the endpoint pair (sign flips with the order), so —
  unlike Phase 4's `RigidityMap`, which lifts a symmetric `edgeRow` over
  `Sym2` — there is no canonical unordered row. We reuse the apnelson1
  `Graph.orientation` (already the Phase-14 source of ordered endpoints
  via `dInc`) to fix the order; the orientation is a sign convention only,
  so kernel/rank stay orientation-independent. Domain `α` (not `↥V(G)`)
  mirrors Phase-4 `Framework V d = V → ℝ^d` and dodges subtype coercions
  on `dInc`'s `α × α` output. Pulled in `import Matroid.Graph.Matrix`
  (keeps the file non-`module`, as KFrame already is).
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

`def:body-bar-framework` and `def:rigidity-map-body-bar` are green
(`BodyBar/Framework.lean`). **Next concrete commit:** formalize the next
leaf-most red node `def:infinitesimally-rigid-body-bar` in
`BodyBar/Framework.lean` — a body-bar framework on `b` bodies is
infinitesimally rigid when `rigidityMap D` has rank `d·b − d` (kernel = the
`d`-dim space of trivial screw motions; the body-bar analogue of
`SimpleGraph.IsInfinitesimallyRigid`'s kernel bound). Likely shape: a `def`
predicate on `(F, D)` via `Module.finrank` of the range/kernel — confirm
whether it should be stated against rank or kernel-dim, and whether `b` is
`Nat.card V(F.graph)` or carried as a parameter. Then flip its blueprint
node green (`\lean{...}` + `\leanok`) in the same commit. Last red node is
`thm:tay-witness`; the phase closes when it is green.

Follow-on: **Phase 16** (body-hinge / panel-hinge Tay–Whiteley), en route
to **Phase 17** (molecular conjecture, Katoh–Tanigawa 2011). Neither is
opened.
