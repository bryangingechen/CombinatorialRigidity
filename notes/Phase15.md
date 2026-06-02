# Phase 15 — Body-bar Tay theorem (existence form) (work log)

**Status:** in progress (just opened).

## Current state

Phase 15 opens here (notes + status-surface sync only; no Lean this
commit). This is the original Phase-12 target, unblocked by the
Phase 12–14 chain (matroid foundations → tree-packing → `k`-frame =
`k`-fold cycle union). Forward-mode phase: the lemma index lives in
`blueprint/src/chapter/body-bar.tex` §`sec:body-bar-framework` and
§`sec:body-bar-tay` (already scoped, nodes red — they are the to-do
list). All prerequisite nodes (`thm:k-frame-union-cycle`,
`thm:tutte-nash-williams`, `cor:k-spanning-trees`, the whole
`sec:body-bar-k-frame` and `sec:body-bar-tree-packing` subsections)
are green.

The chapter has **four red nodes**, in dependency order:
- `def:body-bar-framework` (leaf — no `\uses`)
- `def:rigidity-map-body-bar` (`\uses{def:body-bar-framework}`)
- `def:infinitesimally-rigid-body-bar` (`\uses{def:rigidity-map-body-bar}`)
- `thm:tay-witness` (the target; `\uses` the three defs +
  `def:graph-sparse`, `thm:tutte-nash-williams`, `cor:k-spanning-trees`;
  proof `\uses{thm:k-frame-union-cycle, …}`).

**Next concrete commit:** the leaf-most red node `def:body-bar-framework`
in a new `BodyBar/Framework.lean` — the body-bar framework structure
(a multigraph `G : Graph α β` paired with a placement assigning each
edge a two-extensor / Plücker coordinate in `ℝ^d`, `d = n(n+1)/2`,
degenerate coordinates permitted). Add/flip its `\lean{...}` + `\leanok`
in the same commit. Then `def:rigidity-map-body-bar` (the bar-constraint
linear map, one row per bar) and `def:infinitesimally-rigid-body-bar`
(kernel = `d`-dim trivial screw motions, rank `= d·b − d`).

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

- [ ] `def:body-bar-framework` — body-bar framework (placement = two-extensor
      per bar). **Next concrete commit.** `BodyBar/Framework.lean`.
- [ ] `def:rigidity-map-body-bar` — bar-constraint rigidity map.
- [ ] `def:infinitesimally-rigid-body-bar` — rank `= d·b − d`.
- [ ] `thm:tay-witness` — Tay's theorem, existence form (Whiteley Thm 8).
      Standard-basis specialization of `thm:k-frame-union-cycle`'s reverse
      direction lifted from indeterminate to real coefficients.

## Decisions made during this phase

(none yet — phase just opened)

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

Phase just opened. **Next concrete commit:** formalize
`def:body-bar-framework` in a new `BodyBar/Framework.lean` (the leaf-most
red node), then flip its blueprint node green (`\lean{...}` + `\leanok`)
in the same commit. Proceed up the dep-graph:
`def:rigidity-map-body-bar` → `def:infinitesimally-rigid-body-bar` →
`thm:tay-witness`. The phase closes when `thm:tay-witness` is green.

Follow-on: **Phase 16** (body-hinge / panel-hinge Tay–Whiteley), en route
to **Phase 17** (molecular conjecture, Katoh–Tanigawa 2011). Neither is
opened.
