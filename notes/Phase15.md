# Phase 15 — Body-bar Tay theorem (existence form) (work log)

**Status:** ✓ Complete. Tay's theorem in existence-of-realization form is green as
`thm:tay-witness` (`Graph.BodyBarFramework.tay_witness`, `BodyBar/TayTheorem.lean`):
the iff of the standard-basis existence directions (`prop:tay-witness-exists`:
`exists_isIndependent_of_isSparse` / `exists_isIsostatic_of_isTight`) with the converse
(`lem:tay-isSparse-of-independent`: `isSparse_of_isIndependent`). All
`sec:body-bar-framework` + `sec:body-bar-tay` nodes are green; no `sorry`s, no warnings,
`lake lint` clean. `tay_witness` checks against only `propext`/`Classical.choice`/`Quot.sound`.

## Current state

**Phase 15 is complete.** Forward-mode phase; the authoritative dep-graph
and lemma index is `body-bar.tex` §`sec:body-bar-framework` +
§`sec:body-bar-tay` (this file does not duplicate the node list). The full
per-node landing sequence is the commit log `e83bde2..fa4cfc3` (6
forward-work commits). `BodyBar/{Framework,TayTheorem}.lean`, both in the
top-level `CombinatorialRigidity.lean` aggregator; all
`sec:body-bar-k-frame` / `sec:body-bar-tree-packing` prerequisites green.

Route summary (the `thm:tay-witness` iff over the standard-basis witness):
- **Framework** (`Framework.lean`): `bodyBarDim n = n(n+1)/2`; the bundled
  `BodyBarFramework` (unconstrained `placement : E(graph) → ℝ^d`,
  degenerate two-extensors permitted); `rigidityMap D` (one bar row
  `m ↦ ⟪b_e, m u − m v⟫`, endpoints `(u,v) = D.dInc e` from an explicit
  orientation, `barRow` + `LinearMap.pi`); `IsInfinitesimallyRigid`
  (`rank + d = d·b`, `b = vertexSet.ncard`); `IsIndependent`
  (`rank = |E(G)|`).
- **Witness + block-diagonal rank** (`TayTheorem.lean`): `stdPlacement` /
  `stdFramework` (`b_e = e_{j(e)}`); `stdPlacement_rigidityMap_apply` (row
  collapses to coordinate `j(e)`); `rigidityRow` /
  `span_range_rigidityRow`; the injective `blockPairing`;
  `stdFramework_rigidityRow_eq` + `_linearIndependent` (rows LI for a
  disjoint forest packing via `specRow_linearIndependent` at `ℝ`);
  `stdFramework_finrank_range` (`rank = |E(G)|`).
- **Existence (⟸)** (`prop:tay-witness-exists`):
  `exists_isIndependent_of_isSparse` / `exists_isIsostatic_of_isTight` —
  `tutte_nash_williams.mpr` gives the disjoint forest cover, `choose` the
  index `j`, then `stdFramework_finrank_range` + the tight count.
- **Converse (⟹)** (`lem:tay-isSparse-of-independent`,
  `isSparse_of_isIndependent`): the rank-upper-bound route, not
  affine-spanning trivial motions. `rigidityRow_eq` (general-placement row
  = real-coefficient block-combination of incidence rows) factors each row
  through `blockPairing`; `finrank_rigidityRow_span_le` bounds
  `finrank(span rows on E') ≤ d·r(E')` (via `finrank_realBlockPiSpanOn` +
  `span_signedIncMatrix_image_eq_of_orientation`); restricting row-LI to
  `E'` then `cycleMatroid_rk_add_one_le_spanningVerts_ncard`
  (`r(E')+1 ≤ |V'|`) gives `|E'| + d ≤ d·|V'|`.
- **Full iff** `tay_witness` (`thm:tay-witness`): existence ↔ sparse/tight;
  the isostatic converse adds the global `|E| + d = d·|V|` count.

Axioms: `propext`, `Classical.choice`, `Quot.sound` (no `sorryAx`).

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

**Phase 15 is complete.** Green: the three `sec:body-bar-framework` defs +
`def:independent-body-bar` (`BodyBar/Framework.lean`); the full
`sec:body-bar-tay` chain (`BodyBar/TayTheorem.lean`) — witness placement,
bar-row reduction, block-diagonal rank count, existence direction
`prop:tay-witness-exists`, the converse rank-upper-bound infra
(`rigidityRow_eq`, `span_signedIncMatrix_image_eq_of_orientation`,
`finrank_realBlockPiSpanOn`, `finrank_rigidityRow_span_le`,
`rigidityRow_linearIndependent`), the converse `isSparse_of_isIndependent`
(`lem:tay-isSparse-of-independent`), and the full iff `thm:tay-witness`
(`tay_witness`). No `sorry`s; `lake build` warning-clean; `lake lint` clean;
blueprint `checkdecls` passes (`blueprint/verify.sh`).

**Converse-route note for the next phase:** the converse avoided the
affine-spanning / trivial-motions machinery of Phase 6's
`rigidityMap_finrank_range_le_of_affinelySpanning`. The body-bar rows are
single inner-product functionals, so they factor cleanly through `blockPairing`
as real-coefficient block combinations of incidence rows; the rank upper bound is
then the *real specialization* of Phase 14's generic forward count
(`forest_count_of_linearIndepOn_kFrameRow`), reusing the field-generic
`finrank_constPiSpan` / `finrank_span_signedIncMatrix_eq_cycleMatroid_rk` at `ℝ`.
The `−d` slack comes from `cycleMatroid_rk_add_one_le_spanningVerts_ncard`
(`r(E')+1 ≤ |V'|`), not a trivial-motion dimension count — no body-bar
screw-motion infrastructure was needed.

**Possible cleanup-round item (not a blocker):** `stdFramework_rigidityRow_eq` is
now the `b_e = e_{j(e)}` special case of the general `rigidityRow_eq`. It could be
derived from `rigidityRow_eq` (`Pi.single (j e) v = fun c ↦ (e_{j e} c) • v` after
the std-basis collapse) rather than reproved standalone; left as-is this phase
since both are short and the std proof predates the general one.

Follow-on: **Phase 16** (body-hinge / panel-hinge Tay–Whiteley), where Whiteley's
"almost all realizations are rigid" irreducible-variety lift (deferred here) is
re-assessed; en route to **Phase 17** (molecular conjecture, Katoh–Tanigawa 2011).
Neither is opened.
