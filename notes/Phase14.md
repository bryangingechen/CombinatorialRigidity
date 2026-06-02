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
This top theorem was found **too large for a single commit** and has been
**re-scoped** (coordinator decision, user-approved) into an intermediate
dependency chain — see *Re-scoping of `thm:k-frame-union-cycle`* below.
The four nodes (`lem:k-frame-nonzero-monomial-forest`,
`lem:k-frame-specialize-forest`, `lem:k-frame-indep-iff-count`, then
`thm:k-frame-union-cycle`) are now the red frontier in `body-bar.tex`'s
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
`body-bar.tex`. Nodes, in dependency order (post re-scoping):
- [x] `def:k-frame-matroid` — generic `k`-frame matroid via
  `Matroid.ofFun` (`Graph.kFrameMatroid`, `BodyBar/KFrame.lean`).
- [ ] `lem:k-frame-nonzero-monomial-forest` — **leaf-most; next concrete
  commit.** Forward half of Whiteley §2.1: generic rows of `E'` LI over
  `K` ⟹ a nonzero `|E'|`-minor has a nonzero monomial whose per-bar
  variable selects a block `j(e)`; specializing those variables to `1`
  (rest `0`) gives a block-diagonal real signed-incidence matrix, so
  `E'` is a `k`-forest decomposition / satisfies the count
  `∀ Y ⊆ E', |Y| ≤ k · r(Y)`. Depends only on `def:k-frame-matroid`.
- [ ] `lem:k-frame-specialize-forest` — reverse half of Whiteley §2.1:
  a `k`-forest decomposition `E' = ⨆ⱼ E'ⱼ` specializes the generic rows
  (block-`j` vars `1` on `E'ⱼ`, `0` else) to a block-diagonal full-rank
  incidence matrix; a specialization of full rank ⟹ generic rows LI over
  `K`. Depends only on `def:k-frame-matroid`.
- [ ] `lem:k-frame-indep-iff-count` — packages both directions:
  `(kFrameMatroid G k).Indep E' ↔ (G ↾ E').IsSparse k k` (the
  `Matroid.ofFun` LI predicate ⟺ the union-side count). Depends on the
  two halves above + `thm:unionPow-cycle-indep-iff-sparse` (Phase 13).
- [ ] `thm:k-frame-union-cycle` — Whiteley Theorem 1: `F(G, X) = ⋃ⱼ
  G.cycleMatroid`. Now a `Matroid.ext_indep` matching the two
  count-characterizations (`lem:k-frame-indep-iff-count` vs
  `thm:unionPow-cycle-indep-iff-sparse`); same ground set `E(G)`. This
  commit closes Phase 14.

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

### Re-scoping of `thm:k-frame-union-cycle`

- **Why.** The monolithic theorem bundles (i) Whiteley §2.1's generic
  column-reorder / nonzero-monomial argument over `K = Frac ℚ[X_{e,j}]`,
  in *both* directions, with (ii) the matroid-equality plumbing. Too
  much for one subagent commit; re-scoped (user-approved) into the
  4-node chain in the *Lemma checklist*.
- **Routing decision (resolves the prior blocker).** Go through the
  `Matroid.ofFun_indep_iff` row-LI characterization, **not** a bespoke
  `kFrameMatroid` `Rep`. The two genericity halves
  (`lem:k-frame-nonzero-monomial-forest` /
  `lem:k-frame-specialize-forest`) produce/consume the *count* form
  `∀ Y ⊆ E', |Y| ≤ k · r_{cycleMatroid}(Y)`, which is exactly what
  Phase 13's `thm:unionPow-cycle-indep-iff-sparse`
  (`unionPow_cycleMatroid_indep_iff_isSparse_restrict`, via
  `Matroid.Union_pow_indep_iff_count`) attaches to the union side. So
  the count is the shared interface; `lem:k-frame-indep-iff-count` is
  the bridge node and `thm:k-frame-union-cycle` collapses to
  `Matroid.ext_indep` (both ground sets are `E(G)` by
  `kFrameMatroid_ground` / `unionPow` ground).
- **Reuse.** `def:k-frame-matroid`'s row is `X_{(e,j)} •
  D.signedIncMatrix K e` — the same signed-incidence row
  `Graph.cycleMatroidRep` uses; the block-diagonal specialization in
  both halves is therefore `k` copies of the cycle-matroid
  representation, not a re-derivation of the incidence pattern.

### Promoted to FRICTION
- *`signedIncMatrix` decidability instances inside a `noncomputable def`
  body* → FRICTION `[matroid]` *`Graph.orientation.signedIncMatrix` needs
  `[DecidableEq α]` + `[DecidablePred (· ∈ E(G))]` …* (term-level `letI`
  with `Classical.dec*`, keeping the def signature binder-free).

## Blockers / open questions

- **Genericity-argument routing — resolved.** The "route via
  `Matroid.ofFun_indep_iff` vs a bespoke `Rep`" question is settled in
  favour of the former; see *Re-scoping of `thm:k-frame-union-cycle`*.
  The substantive remaining risk is purely formalization cost of the
  nonzero-monomial / variable-specialization argument in the two
  genericity halves (`lem:k-frame-nonzero-monomial-forest` /
  `lem:k-frame-specialize-forest`); these may each themselves want
  further splitting once `lean_goal` exploration shows the real shape
  of the `MvPolynomial` determinant-expansion step.

## Hand-off / next phase

`thm:k-frame-union-cycle` was re-scoped into a 4-node chain (this is a
planning-only commit; no Lean landed). Resume the standard
one-commit-per-subagent loop against the **leaf-most red node**:

Next concrete commit: **`lem:k-frame-nonzero-monomial-forest`** (forward
half of Whiteley §2.1). State and prove, in `BodyBar/KFrame.lean`, that
linear independence of the generic `k`-frame rows of `E' ⊆ E(G)` over
`KFrameField β k` implies the union-side count
`∀ Y ⊆ E', |Y| ≤ k · r_{G.cycleMatroid}(Y)` (equivalently a `k`-forest
decomposition of `E'`), via the nonzero-monomial / per-bar block
selection / variable-specialization argument. Depends only on
`def:k-frame-matroid`; flip its `body-bar.tex` node green in the same
commit. Explore the `Matroid.ofFun_indep_iff` LI predicate and the
`MvPolynomial` determinant-expansion shape with `lean_goal` first — the
node may itself want further splitting (see Blockers).

After the two genericity halves and `lem:k-frame-indep-iff-count` land,
`thm:k-frame-union-cycle` is a short `Matroid.ext_indep`; **that** commit
closes Phase 14 and unblocks Phase 15 (body-bar Tay theorem, existence
form), so it carries the phase-completion checklist (ROADMAP row ✓,
status surfaces, compress ROADMAP §14).
