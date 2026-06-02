# Phase 14 — k-frame matroid = k-fold cycle-matroid union (work log)

**Status:** in progress.

Forward-mode phase. The authoritative dep-graph and lemma index is the
*The $k$-frame matroid as a union of cycle matroids* subsection
(`sec:body-bar-k-frame`) of `blueprint/src/chapter/body-bar.tex`; this
file carries current state, decisions, blockers, and hand-off, and does
**not** duplicate the lemma list.

## Current state

`def:k-frame-matroid` is **done** (`Graph.kFrameMatroid` in the new
`BodyBar/KFrame.lean`, blueprint node green). The Phase 13 chain
(`BodyBar/TreePacking.lean`) remains the upstream dependency: it proves
the tree-packing corollary and the `Graph`-native `(k, k)`-sparsity ↔
`k`-fold-`cycleMatroid`-union independence bridge
(`Graph.unionPow_cycleMatroid_indep_iff_isSparse_restrict`).

Phase 14's target is Whiteley 1988 Theorem 1
(`thm:k-frame-union-cycle`): the generic `k`-frame matroid `F(G, X)` on
a multigraph `Graph α β` equals the `k`-fold union of `Graph.cycleMatroid`.
This is now the **single remaining red node** in `body-bar.tex`'s
`sec:body-bar-k-frame`.

## Architectural choices made up front

Carried from ROADMAP §14–§15 and `DESIGN.md`:
- **Carrier = mathlib core `Graph α β`** (same as Phase 13), on which
  `apnelson1/Matroid`'s `cycleMatroid` sits. Phases 1–11 stay on
  `SimpleGraph`.
- **Coefficient ring / genericity.** The `k`-frame matroid is defined
  via `Matroid.ofFun` over indeterminate coefficients; Whiteley §2.1's
  column-reorder / nonzero-monomial argument drives the equality. The
  exact coefficient encoding (which scalar field, how the indeterminates
  index the `k` blocks) is the first design decision the
  `def:k-frame-matroid` commit must pin — assess against the
  `LinearRigidityMatroid.lean` `Matroid.ofFun` precedent before
  committing.
- **`Matroid`-namespace / `Graph`-namespace split** (Phases 12–15
  exception to the all-under-`SimpleGraph` rule): graph-level
  `kFrameMatroid` under `namespace Graph` for dot-notation beside
  `Graph.cycleMatroid`.

## Lemma checklist

The authoritative checklist is the `sec:body-bar-k-frame` dep-graph in
`body-bar.tex`. Top-level nodes, in dependency order:
- [x] `def:k-frame-matroid` — generic `k`-frame matroid via
  `Matroid.ofFun` (`Graph.kFrameMatroid`, `BodyBar/KFrame.lean`).
- [ ] `thm:k-frame-union-cycle` — Whiteley Theorem 1: `F(G, X) = ⋃ⱼ
  G.cycleMatroid`. Column-reorder / nonzero-monomial argument
  (Whiteley §2.1), routed through `lem:union-indep-iff` (Phase 12).
  **Next concrete commit.**

## Decisions made during this phase

- **Coefficient encoding (pinned).** The generic `k`-frame matroid is
  realized over **true indeterminates**, not a real placement (departing
  from Phase 8's `linearRigidityMatroid`, which parametrizes by
  `p : Framework V d`): the field is `KFrameField β k :=
  FractionRing (MvPolynomial (β × Fin k) ℚ)`, one indeterminate
  `X_{(e,j)}` per (bar, block) pair. The row for bar `e` in block `j`
  (`kFrameRow`) is `X_{(e,j)} • D.signedIncMatrix K e` — the
  indeterminate scaling of the signed graph-incidence row that
  `Graph.cycleMatroidRep` represents `cycleMatroid` by, so the row space
  is `Fin k → α → K` (`k` copies of the `|V|`-dim incidence-row space).
  The orientation `D` is picked by `G.orientation_nonempty.some`
  (matching `cycleMatroidRep`); harmless for the generic matroid. This
  reuse-of-`signedIncMatrix` is what should make `thm:k-frame-union-cycle`
  reduce cleanly to `k` independent `cycleMatroid` representations rather
  than re-deriving the incidence pattern from scratch.

### Promoted to FRICTION
- *`signedIncMatrix` decidability instances inside a `noncomputable def`
  body* → FRICTION `[matroid]` *`Graph.orientation.signedIncMatrix` needs
  `[DecidableEq α]` + `[DecidablePred (· ∈ E(G))]` …* (term-level `letI`
  with `Classical.dec*`, keeping the def signature binder-free).

## Blockers / open questions

- **`thm:k-frame-union-cycle` genericity argument.** The remaining node
  needs Whiteley's column-reorder / nonzero-monomial argument over the
  indeterminate field. Whether to route it through the
  `Matroid.ofFun_indep_iff` row-LI characterization directly (LI of the
  indeterminate-scaled incidence rows ⟺ existence of a nonzero block
  permanent), or to first build a `kFrameMatroid`-side `Rep` analogue of
  `cycleMatroidRep` for the `k`-block space, is open — assess against
  `lem:union-indep-iff` (`Matroid.Union_pow_indep_iff_count`), the
  intended target shape.

## Hand-off / next phase

`def:k-frame-matroid` landed (`Graph.kFrameMatroid`, `BodyBar/KFrame.lean`;
blueprint node green). Next concrete commit: **`thm:k-frame-union-cycle`**
— prove `Graph.kFrameMatroid G k = Matroid.Union (fun _ : Fin k ↦
G.cycleMatroid)` (the single remaining red node), via the
column-reorder / nonzero-monomial argument routed through
`Matroid.Union_pow_indep_iff_count` (Phase 12 `lem:union-indep-iff`); pin
the proof route per the blocker above, flip the `body-bar.tex` node green
in the same commit. That commit closes Phase 14 and unblocks Phase 15
(body-bar Tay theorem, existence form) — so it also carries the
phase-completion checklist (ROADMAP row ✓, status surfaces, compress
ROADMAP §14).
