# Phase 14 — k-frame matroid = k-fold cycle-matroid union (work log)

**Status:** in progress.

Forward-mode phase. The authoritative dep-graph and lemma index is the
*The $k$-frame matroid as a union of cycle matroids* subsection
(`sec:body-bar-k-frame`) of `blueprint/src/chapter/body-bar.tex`; this
file carries current state, decisions, blockers, and hand-off, and does
**not** duplicate the lemma list.

## Current state

`def:k-frame-matroid` is **done** (`Graph.kFrameMatroid` in the new
`BodyBar/KFrame.lean`, blueprint node green). The forward node
`lem:k-frame-nonzero-monomial-forest` was found too large for one commit and
**re-split**: its self-contained linear-algebra core landed as a new green
sub-node `lem:k-frame-span-le-pi` (`Graph.blockPiSpan` + `kFrameRow_mem_blockPiSpan`
+ `span_kFrameRow_le_blockPiSpan` in `BodyBar/KFrame.lean`) — the span of the
`k`-frame rows lies in the `Fin k`-fold product of the incidence-row span. The
forward node itself was re-cast to a **rank-counting** route (cleaner than
Whiteley's nonzero-monomial expansion; both give the same bound) and remains
red. **Piece (1) of the rank count is now also landed** as a second green
sub-node `lem:k-frame-pi-finrank` (`Graph.constPiSpanEquiv` +
`Graph.finrank_constPiSpan` in `BodyBar/KFrame.lean`): the constant `Fin k`-fold
product subspace has `K`-dimension `k · dim_K W` (via a `LinearEquiv` onto
`Fin k → W` + `Module.finrank_pi_fintype`). **Piece (2) is now also landed** as a
third green sub-node `lem:k-frame-incidence-finrank-rk`: a general matroid-rep bridge
`Matroid.Rep.finrank_span_image_eq_rk` (`finrank (span (v '' Y)) = M.rk Y` for any
`[M.RankFinite]` rep, via a basis of `Y`) plus its cycle-matroid specialization
`Graph.finrank_span_signedIncMatrix_eq_cycleMatroid_rk` (since `⇑(cycleMatroidRep K) =
signedIncMatrix` by `rfl`), both in `BodyBar/KFrame.lean`. **The forward node
`lem:k-frame-nonzero-monomial-forest` is now also landed (green):
`Graph.forest_count_of_linearIndepOn_kFrameRow` assembles the three pieces** — for `Y ⊆ E'`,
restricting the generic LI to `Y` (`LinearIndepOn.mono`) gives `Y.ncard = finrank (span
(kFrameRow '' Y))`, bounded by the new `Y`-restricted block span `Graph.blockPiSpanOn`
(`span_kFrameRowOn_le_blockPiSpanOn` + `Submodule.finrank_mono`) whose dim is
`k · r_{cycleMatroid}(Y)` (`finrank_blockPiSpanOn`, from pieces (1)+(2)). The forward half of
Whiteley §2.1 is complete. The reverse half (`lem:k-frame-specialize-forest`) was found
comparably large and has been **re-split**: its self-contained linear-algebra core landed as a new
green sub-node `lem:k-frame-specialize-li` (`Graph.specRow_linearIndependent` in
`BodyBar/KFrame.lean`) — the block-diagonal specialization (`Pi.single j (signedIncMatrix e)` for
`e ∈ Fs j` over a forest packing `Fs : Fin k → Set β`, indexed by `Σ j, ↥(Fs j)`) is LI over `K`,
via mathlib's `Pi.linearIndependent_single` + the Matroid-pkg `Graph.orientation.isAcyclicSet_linearIndepOn`.
The remaining red frontier is the genericity-lift step that finishes `lem:k-frame-specialize-forest`
(a specialization of full rank witnesses generic LI over `K = Frac ℚ[X]`), then
`lem:k-frame-indep-iff-count`, then `thm:k-frame-union-cycle`. The Phase 13 chain
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
- [x] `lem:k-frame-span-le-pi` — **landed.** Rank-counting core of the forward
  half: the span of the generic `k`-frame rows lies in `blockPiSpan`, the
  `Fin k`-fold product whose `j`-th block is the `K`-span of the signed
  incidence rows (`Graph.blockPiSpan` + `kFrameRow_mem_blockPiSpan` +
  `span_kFrameRow_le_blockPiSpan`). Depends only on `def:k-frame-matroid`.
- [x] `lem:k-frame-pi-finrank` — **landed.** Piece (1) of the forward rank
  count: `finrank (Submodule.pi univ (fun _ : Fin k ↦ W)) = k · finrank W`
  (`Graph.finrank_constPiSpan` via the `LinearEquiv` `Graph.constPiSpanEquiv`
  onto `Fin k → W` + `Module.finrank_pi_fintype`). General over a `DivisionRing`;
  needs `[Module.Finite R W]` (supplied at the call site by `Finite α`).
- [x] `lem:k-frame-incidence-finrank-rk` — **landed.** Piece (2) of the forward
  rank count: the general rep bridge `Matroid.Rep.finrank_span_image_eq_rk`
  (`finrank (span (v '' Y)) = M.rk Y` for any `[M.RankFinite]` rep) + its
  cycle-matroid specialization `Graph.finrank_span_signedIncMatrix_eq_cycleMatroid_rk`
  (`⇑(cycleMatroidRep K) = signedIncMatrix` by `rfl`), both in `BodyBar/KFrame.lean`.
  Routes via `exists_isBasis'` + `Rep.isBasis'_iff` + `finrank_span_set_eq_card`.
- [x] `lem:k-frame-nonzero-monomial-forest` — **landed.** Forward half of
  Whiteley §2.1 by the **rank count**: generic rows of `E'` LI over `K` ⟹
  `∀ Y ⊆ E', |Y| ≤ k · r(Y)` (`Graph.forest_count_of_linearIndepOn_kFrameRow`).
  Assembly of the three pieces via a new `Y`-restricted block span
  `Graph.blockPiSpanOn` (+ `kFrameRow_mem_blockPiSpanOn`,
  `span_kFrameRowOn_le_blockPiSpanOn`, `finrank_blockPiSpanOn`): restrict LI to `Y`
  (`LinearIndepOn.mono`), `|Y| = finrank (span (kFrameRow '' Y))`
  (`finrank_span_set_eq_card`), then `Submodule.finrank_mono` into `blockPiSpanOn`
  whose dim is `k · r_{cycleMatroid}(Y)`. Block-pi finiteness transported via
  `constPiSpanEquiv`.
- [x] `lem:k-frame-specialize-li` — **landed.** Linear-algebra core of the reverse half:
  the block-diagonal specialization `Pi.single j (signedIncMatrix e)` (for `e ∈ Fs j` over a
  forest packing `Fs : Fin k → Set β`, indexed by `Σ j, ↥(Fs j)`) is LI over `K`
  (`Graph.specRow_linearIndependent`, `BodyBar/KFrame.lean`). Via mathlib's
  `Pi.linearIndependent_single` (disjoint-block assembly) + the Matroid-pkg
  `Graph.orientation.isAcyclicSet_linearIndepOn` (each forest's incidence rows LI). Two-line term
  proof; `letI`-in-statement instance pattern (as `finrank_span_signedIncMatrix_eq_cycleMatroid_rk`).
- [ ] `lem:k-frame-specialize-forest` — reverse half of Whiteley §2.1; **LI core done**
  (`lem:k-frame-specialize-li`). Remaining: the genericity-lift — a specialization of full rank
  (the block-diagonal matrix of `lem:k-frame-specialize-li`, obtained by setting block-`j` vars `1`
  on `Fs j`, `0` else) ⟹ generic rows LI over `K = Frac ℚ[X]`. Needs the "evaluation of a polynomial
  minor is nonzero ⟹ the minor is a nonzero polynomial ⟹ generic LI" argument (no off-the-shelf
  mathlib/Matroid-pkg lemma; likely its own commit(s)).
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
  The forward half was re-cast from the nonzero-monomial determinant
  expansion to a **rank-counting** argument (avoids the `MvPolynomial`
  determinant machinery entirely); all three linear-algebra pieces
  (`lem:k-frame-span-le-pi`, piece (1) `lem:k-frame-pi-finrank`, piece (2)
  `lem:k-frame-incidence-finrank-rk`) and the **assembly forward node**
  `lem:k-frame-nonzero-monomial-forest` are now all landed. The `r(E(G))`-vs-`r(Y)`
  wrinkle was resolved by adding the `Y`-restricted block span `Graph.blockPiSpanOn`
  (block `W_Y = span (signedIncMatrix '' Y)`), so piece (2) applies with the correct
  `r(Y)`; the original full-row `blockPiSpan` + `span_kFrameRow_le_blockPiSpan` stay
  (blueprinted under `lem:k-frame-span-le-pi`). The reverse half `lem:k-frame-specialize-forest`
  has been re-split: its LI core `lem:k-frame-specialize-li` (`Graph.specRow_linearIndependent`) is
  landed; the remaining open work is the genericity-lift (specialization of full rank ⟹ generic LI
  over `K`), which needs the polynomial-minor non-vanishing argument and has no off-the-shelf
  mathlib/Matroid-pkg lemma.

## Hand-off / next phase

The **entire forward half** of Whiteley §2.1 is now landed:
`lem:k-frame-span-le-pi` (`Graph.span_kFrameRow_le_blockPiSpan`), piece (1)
`lem:k-frame-pi-finrank` (`Graph.finrank_constPiSpan`), piece (2)
`lem:k-frame-incidence-finrank-rk`
(`Matroid.Rep.finrank_span_image_eq_rk` +
`Graph.finrank_span_signedIncMatrix_eq_cycleMatroid_rk`), and the assembly
`lem:k-frame-nonzero-monomial-forest`
(`Graph.forest_count_of_linearIndepOn_kFrameRow`, via the `Y`-restricted block span
`Graph.blockPiSpanOn` and `finrank_blockPiSpanOn`).

The reverse half's **linear-algebra core** `lem:k-frame-specialize-li`
(`Graph.specRow_linearIndependent`) is now landed: the block-diagonal specialization on a forest
packing is LI over `K`, assembled from per-forest incidence-row LI
(`Graph.orientation.isAcyclicSet_linearIndepOn`) by `Pi.linearIndependent_single`.

The next concrete commit is the **genericity-lift** that finishes `lem:k-frame-specialize-forest`
(leaf-most red node): from `(G ↾ E').IsSparse k k` extract a forest packing `Fs : Fin k → Set β` of
`E'` (via `unionPow_cycleMatroid_indep_iff_isSparse_restrict` + `Matroid.union_indep_iff`, as in
`tutte_nash_williams`), then lift `lem:k-frame-specialize-li` (the specialization has full rank) to
generic LI of `kFrameRow` over `E'`. The lift is the "a polynomial minor with a nonzero
specialization is a nonzero polynomial, so the generic rows are LI over `K = Frac ℚ[X]`" argument —
**no off-the-shelf mathlib/Matroid-pkg lemma exists for this**, so it likely needs its own
sub-lemma(s) (a `RingHom`/`AlgHom`-mediated `LinearIndependent`-reflection over the fraction field,
or an `MvPolynomial.eval`-based minor-nonvanishing helper). Flip `lem:k-frame-specialize-forest`
green when the lift lands; if it overshoots one commit, re-split as the forward half was.

After it, `lem:k-frame-indep-iff-count` packages both halves against
`thm:unionPow-cycle-indep-iff-sparse` (Phase 13); then `thm:k-frame-union-cycle`
closes Phase 14 (a short `Matroid.ext_indep`) and carries the phase-completion
checklist (ROADMAP ✓, status surfaces, compress §14).

After the two genericity halves and `lem:k-frame-indep-iff-count` land,
`thm:k-frame-union-cycle` is a short `Matroid.ext_indep`; **that** commit
closes Phase 14 and unblocks Phase 15 (body-bar Tay theorem, existence
form), so it carries the phase-completion checklist (ROADMAP row ✓,
status surfaces, compress ROADMAP §14).
