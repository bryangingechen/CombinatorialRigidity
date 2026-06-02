# Phase 15 — Body-bar Tay theorem (existence form) (work log)

**Status:** in progress (3 of 4 nodes green; target `thm:tay-witness` left;
witness placement + bar-row reduction landed in `BodyBar/TayTheorem.lean`).

## Current state

Three leaf nodes are **green** in `BodyBar/Framework.lean`:
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
- `def:infinitesimally-rigid-body-bar` —
  `Graph.BodyBarFramework.IsInfinitesimallyRigid F D`, a `Prop` predicate:
  `finrank ℝ (range (rigidityMap D)) + bodyBarDim n = bodyBarDim n *
  F.graph.vertexSet.ncard` (the count `rank = d·b − d` phrased as `rank + d
  = d·b` to dodge ℕ-subtraction; `b = #bodies = vertexSet.ncard`). Mirrors
  Phase 4's `SimpleGraph.IsInfinitesimallyRigid`, incl. the `[Finite α]`
  contract guard + `@[nolint unusedArguments]` (same disposition note).
  Stated against **rank** (not kernel-dim) to match the blueprint's `d·b −
  d` phrasing. Blueprint node flipped (`\lean{...}` + `\leanok`).

`BodyBar/Framework.lean` is in the top-level `CombinatorialRigidity.lean`
import aggregator. Forward-mode phase: the lemma index lives in
`blueprint/src/chapter/body-bar.tex` §`sec:body-bar-framework` and
§`sec:body-bar-tay`. All `sec:body-bar-k-frame` /
`sec:body-bar-tree-packing` prerequisites are green.

The chapter has **one red node** left — the target:
- `thm:tay-witness` (`\uses` the three defs + `def:graph-sparse`,
  `thm:tutte-nash-williams`, `cor:k-spanning-trees`; proof
  `\uses{thm:k-frame-union-cycle, …}`). The phase closes when it is green.

`BodyBar/TayTheorem.lean` (new this session) holds the **witness
placement** and the **bar-row reduction** — the foundational step toward
`thm:tay-witness`:
- `stdPlacement G n j` / `stdFramework G n j` — the standard-basis
  placement `b_e = e_{j(e)} = EuclideanSpace.single (j e) 1` from a
  forest-index map `j : E(G) → Fin (bodyBarDim n)`, and its bundled
  `BodyBarFramework`.
- `stdPlacement_rigidityMap_apply` — the row collapse: with `b_e = e_{j(e)}`,
  `(stdFramework G n j).rigidityMap D m e = (m u − m v) (j e)` (single
  coordinate `j(e)` of the relative velocity, via
  `EuclideanSpace.inner_single_left`). This exposes the block-diagonal
  structure: the row for `e` lives entirely in coordinate `j(e)`, where it
  is `e`'s signed incidence row.

The blueprint node `thm:tay-witness` is **still red** (no Lean theorem
declaration yet) — `TayTheorem.lean` is infrastructure below it, so no
`\lean{...}`/`\leanok` flip this commit.

**Next concrete commit:** the **block-diagonal rank count**. Relate
`finrank (range (stdFramework G n j).rigidityMap D)` to `Σⱼ |Fs j|` for a
disjoint forest packing `Fs` with `j(e) =` the forest index of `e`. The
shape to aim for: the rigidity matrix (rows = bars, cols = (coordinate,
body)) reindexes — via `stdPlacement_rigidityMap_apply` — to the
block-diagonal matrix whose block `j` is the `ℝ`-signed-incidence matrix of
`Fs j`, the **real-coefficient analogue of `specRow_linearIndependent`**
(which is already stated over an arbitrary `Field 𝔽`, so it applies at
`𝔽 = ℝ` directly — see *Blockers*, resolved). Land the
independent-form half (`(d,d)`-sparse ⟹ `rigidityMap` injective on the
witness / rank `= |E|`) first, then the `thm:tay-witness` iff + isostatic
refinement via `cor:k-spanning-trees`.

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
- [x] `def:infinitesimally-rigid-body-bar` — rank `= d·b − d`
      (`IsInfinitesimallyRigid`). `BodyBar/Framework.lean`.
- [ ] `thm:tay-witness` — Tay's theorem, existence form (Whiteley Thm 8).
      Standard-basis specialization of `thm:k-frame-union-cycle`'s reverse
      direction lifted from indeterminate to real coefficients.
      - [x] Witness placement + bar-row reduction (`stdPlacement`,
            `stdFramework`, `stdPlacement_rigidityMap_apply`) —
            `BodyBar/TayTheorem.lean`. The row collapse to coordinate `j(e)`.
      - [ ] **Next:** block-diagonal rank count
            (`rank (rigidityMap) = Σⱼ |Fs j| = |E|`), via the ℝ-instance of
            `specRow_linearIndependent`.
      - [ ] The `thm:tay-witness` iff + isostatic refinement
            (`cor:k-spanning-trees`). Phase closes here.

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
- **`IsInfinitesimallyRigid` stated against rank, not kernel-dim, and `b`
  computed from `vertexSet.ncard`.** The blueprint phrases rigidity as rank
  `= d·b − d`, so the def reads `finrank (range (rigidityMap D)) + d = d·b`
  (the `+ d = d·b` form sidesteps ℕ-subtraction). `b` is read off the
  framework as `F.graph.vertexSet.ncard` rather than a parameter — the body
  set is intrinsic to `F.graph`. Predicate takes the orientation `D`
  explicitly (matching `rigidityMap`); rank is `D`-independent. Mirrors
  Phase-4 `SimpleGraph.IsInfinitesimallyRigid`'s `[Finite α]` guard +
  `@[nolint unusedArguments]` disposition verbatim.

## Blockers / open questions

- **Plücker / two-extensor encoding — RESOLVED (no wrapper needed).** The
  standard-basis placement `b_e = e_{j(e)}` is an unconstrained vector in `ℝᵈ`
  (`stdPlacement`, `BodyBar/TayTheorem.lean`); the existence-of-realization
  scope (degenerate two-extensors permitted) means no Plücker-variety wrapper
  is required. The bar-row reduction `stdPlacement_rigidityMap_apply` collapses
  each row to a single signed-incidence coordinate, so the rigidity matrix is
  block-diagonal directly — no need to route through `kFrameRow` /
  `kFrameRowR` / `forestEval` at all. The relevant Phase-14 lemma to reuse for
  the per-block full-rank fact is `specRow_linearIndependent` (or, more
  directly, `Graph.orientation.isAcyclicSet_linearIndepOn`): it is stated over
  an arbitrary `[Field 𝔽]`, so it applies at `𝔽 = ℝ` with no lift. The
  fraction-field machinery (`KFrameField`, `linearIndepOn_kFrameRow_*`) is
  *not* needed for the real witness — that infrastructure was for the generic
  *matroid* identification (Phase 14), whereas Tay's witness works at a single
  real specialization.

## Hand-off / next phase

The three `sec:body-bar-framework` defs are green
(`BodyBar/Framework.lean`); the witness placement + bar-row reduction are
green (`BodyBar/TayTheorem.lean`). The **first sub-step is done**: the
Phase-14 block-diagonal machinery lifts to `ℝ` with no Plücker wrapper
(see *Blockers*, RESOLVED — `specRow_linearIndependent` /
`isAcyclicSet_linearIndepOn` are already field-generic), and the witness
row collapses to a single signed-incidence coordinate via
`stdPlacement_rigidityMap_apply`.

**Next concrete commit:** the **block-diagonal rank count** — prove
`finrank (range ((stdFramework G n j).rigidityMap D)) = Σⱼ |Fs j| = |E|`
for a disjoint forest packing `Fs` and `j(e) =` forest index of `e`. This
is the independent-form half (`(d,d)`-sparse ⟹ rank `= |E|`, hence
independent). The matrix (rows = bars, cols = (coordinate, body)) reindexes
along `stdPlacement_rigidityMap_apply` to the block-diagonal matrix whose
block `j` is the ℝ-signed-incidence matrix of `Fs j`; each block is LI
(`specRow_linearIndependent` at `𝔽 = ℝ`). Then the `thm:tay-witness` iff
(both directions) + isostatic refinement via `cor:k-spanning-trees` is the
phase-closing commit. Flip `thm:tay-witness` green (`\lean{...}` +
`\leanok`) when the iff lands; the phase closes on that commit.

Follow-on: **Phase 16** (body-hinge / panel-hinge Tay–Whiteley), en route
to **Phase 17** (molecular conjecture, Katoh–Tanigawa 2011). Neither is
opened.
