# Phase 14 — k-frame matroid = k-fold cycle-matroid union (work log)

**Status:** in progress.

Forward-mode phase. The authoritative dep-graph and lemma index is the
*The $k$-frame matroid as a union of cycle matroids* subsection
(`sec:body-bar-k-frame`) of `blueprint/src/chapter/body-bar.tex`; this
file carries current state, decisions, blockers, and hand-off, and does
**not** duplicate the lemma list.

## Current state

Phase opened. The Phase 13 chain (`BodyBar/TreePacking.lean`) is green
and unblocks this phase: it already proves the tree-packing corollary
and the `Graph`-native `(k, k)`-sparsity ↔ `k`-fold-`cycleMatroid`-union
independence bridge (`Graph.unionPow_cycleMatroid_indep_iff_isSparse_restrict`).

Phase 14's target is Whiteley 1988 Theorem 1
(`thm:k-frame-union-cycle`): the generic `k`-frame matroid `F(G, X)` on
a multigraph `Graph α β` equals the `k`-fold union of `Graph.cycleMatroid`.
Both `def:k-frame-matroid` and `thm:k-frame-union-cycle` are red nodes in
`body-bar.tex`. The leaf-most red node — and the next concrete Lean
commit — is **`def:k-frame-matroid`**: the linear matroid (via
`Matroid.ofFun`, the same constructor `LinearRigidityMatroid.lean` uses
for the planar case) of the formal `k · |V|`-column matrix whose row for
edge `e = (u, v)` carries indeterminate coefficients across the `k`
vertex blocks. New file: `CombinatorialRigidity/BodyBar/KFrame.lean`.

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
- [ ] `def:k-frame-matroid` — generic `k`-frame matroid via
  `Matroid.ofFun`. **Next concrete commit.**
- [ ] `thm:k-frame-union-cycle` — Whiteley Theorem 1: `F(G, X) = ⋃ⱼ
  G.cycleMatroid`. Column-reorder / nonzero-monomial argument
  (Whiteley §2.1), routed through `lem:union-indep-iff` (Phase 12).

## Decisions made during this phase

_(none yet)_

## Blockers / open questions

- **Coefficient encoding for `def:k-frame-matroid`.** Whiteley's
  indeterminate row coefficients need a concrete Lean realization
  through `Matroid.ofFun`. Open until the def commit pins it; the
  `LinearRigidityMatroid.linearRigidityRow` / `Matroid.ofFun` pattern is
  the precedent to start from. The genericity argument (nonzero monomial
  of a determinant) parallels Phase 8's uniform-genericity perturbation
  but over a formal/indeterminate ring rather than ℝ — confirm whether
  the existing `Mathlib/LinearAlgebra/Matrix/Rank.lean` mirror lemmas
  carry over or whether a polynomial-ring analogue is needed.

## Hand-off / next phase

Next concrete commit: formalize **`def:k-frame-matroid`** in a new
`CombinatorialRigidity/BodyBar/KFrame.lean` (the leaf-most red node),
pinning the coefficient encoding per the blocker above, and flip its
`body-bar.tex` node green (`\lean{...}` + `\leanok`) in the same commit.
Then `thm:k-frame-union-cycle` is the single remaining Phase-14 node.
Phase 14 closing unblocks Phase 15 (body-bar Tay theorem, existence
form).
