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
**The first half of the genericity-lift is now also landed** as a new green sub-node
`lem:k-frame-li-over-poly-ring` (`Graph.linearIndepOn_kFrameRow_iff_over_polyRing` in
`BodyBar/KFrame.lean`): generic LI of `kFrameRow` over `K = Frac R` ⟺ LI over the polynomial ring
`R = MvPolynomial (β × Fin k) ℚ`, via `LinearIndependent.iff_fractionRing` on the fixed row family
(the `K`-module `Fin k → α → K` is an `R`-module via the algebra map, scalar tower inherited from
the product). This moves the remaining nonzero-minor argument off the fraction field and onto the
integral domain `R`. **The forest-extraction step of the reverse half is now also landed** as a
new green sub-node `lem:k-frame-forest-packing-of-sparse`
(`Graph.exists_forestPacking_cover_of_isSparse_restrict` in `BodyBar/KFrame.lean`): from
`(G ↾ E').IsSparse k k` it produces a `k`-tuple `Fs : Fin k → Set β` of acyclic bar sets covering
`E'` exactly, via `unionPow_cycleMatroid_indep_iff_isSparse_restrict` (Phase 13) +
`Matroid.union_indep_iff` + `cycleMatroid_indep`. **The abstract minor-nonvanishing engine is now
also landed** as a mirror lemma `Matrix.linearIndependent_rows_of_specialized_submatrix_det_ne_zero`
(`Mathlib/LinearAlgebra/Matrix/Rank.lean`): for rows `M : ι → κ → R` over a domain `R`, a column
selection `e : ι → κ`, and a ring hom `φ : R →+* S` (`S` nontrivial), if `φ (submatrix (M∘e)).det
≠ 0` then `LinearIndependent R M` (the determinant-routed reflection; the coefficient-wise one is
false — see FRICTION). **The specialization-identity sub-node is now also landed (green):
`Graph.forestEval_kFrameRowR_eq_single`** — the `R`-lift half of the wiring step. It introduces the
`R = MvPolynomial (β × Fin k) ℚ`-valued row `Graph.kFrameRowR` (`X_{(e,j)} • signedIncMatrix R e`),
the bridge `Graph.kFrameRow_eq_map_kFrameRowR` (`kFrameRow` is `kFrameRowR` under `algebraMap R K`
entrywise, via the ring-hom naturality helper `Graph.signedIncMatrix_map`), the forest-packing
evaluation hom `Graph.forestEval Fs : R →+* ℚ` (`X_{(e,j)} ↦ 1` on `Fs j` else `0`), and the
identity that for a **disjoint** packing and `e ∈ Fs j₀`, `forestEval`-specializing `kFrameRowR k D
e` entrywise yields exactly the block-`single` row `Pi.single j₀ (signedIncMatrix ℚ e)` of
`specRow_linearIndependent`. The remaining red frontier is the **minor / det step** that finishes
`lem:k-frame-specialize-forest`: pick a disjoint forest packing (disjointify
`exists_forestPacking_cover_of_isSparse_restrict`, or reuse Phase 13's `IsForestPacking`), feed
`forestEval Fs` + the identity above + a square column selection to the engine
`Matrix.linearIndependent_rows_of_specialized_submatrix_det_ne_zero`, where the specialized minor
det is nonzero because the block-diagonal forest rows are LI over ℚ (`specRow_linearIndependent` →
`LinearIndependent.rank_matrix`, picking a maximal nonsingular minor). Then
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
- [x] `lem:k-frame-li-over-poly-ring` — **landed.** First half of the genericity-lift:
  generic LI of `kFrameRow` over `K = Frac R` ⟺ LI over `R = MvPolynomial (β × Fin k) ℚ`
  (`Graph.linearIndepOn_kFrameRow_iff_over_polyRing`), via `LinearIndependent.iff_fractionRing`
  on the fixed row family. Moves the nonzero-minor argument off the fraction field onto the
  integral domain `R`.
- [x] `lem:k-frame-forest-packing-of-sparse` — **landed.** Forest-extraction step of the reverse
  half: `(G ↾ E').IsSparse k k` ⟹ `∃ Fs : Fin k → Set β, ⋃ Fs i = E' ∧ ∀ i, G.IsAcyclicSet (Fs i)`
  (`Graph.exists_forestPacking_cover_of_isSparse_restrict`, `BodyBar/KFrame.lean`). Via
  `unionPow_cycleMatroid_indep_iff_isSparse_restrict` (Phase 13) + `Matroid.union_indep_iff` +
  `cycleMatroid_indep`. Supplies the `Fs` on which `lem:k-frame-specialize-li` places its block-
  diagonal full-rank matrix.
- [x] `lem:k-frame-specialize-identity` — **landed.** The `R`-lift / specialization-identity
  sub-node of the reverse half: `Graph.forestEval_kFrameRowR_eq_single` (`BodyBar/KFrame.lean`),
  grouped with the `R`-valued row `Graph.kFrameRowR`, the algebra-map bridge
  `Graph.kFrameRow_eq_map_kFrameRowR`, the eval hom `Graph.forestEval`, and the ring-hom naturality
  helper `Graph.signedIncMatrix_map`. For a disjoint `k`-forest packing `Fs` and `e ∈ Fs j₀`,
  entrywise-`forestEval`-specializing `kFrameRowR k D e` gives exactly `Pi.single j₀
  (signedIncMatrix ℚ e)` — the block-`single` row of `lem:k-frame-specialize-li`.
- [ ] `lem:k-frame-specialize-forest` — reverse half of Whiteley §2.1; **LI core done**
  (`lem:k-frame-specialize-li`), **fraction-field reduction done** (`lem:k-frame-li-over-poly-ring`),
  **forest extraction done** (`lem:k-frame-forest-packing-of-sparse`), the **abstract
  minor-nonvanishing engine done** (`Matrix.linearIndependent_rows_of_specialized_submatrix_det_ne_zero`,
  mirror in `Mathlib/LinearAlgebra/Matrix/Rank.lean`), and the **specialization identity done**
  (`lem:k-frame-specialize-identity`). Remaining: the **minor / det step** — pick a disjoint forest
  packing, feed `forestEval Fs` + the identity + a square column selection to the engine, where the
  specialized minor det is nonzero because the forest blocks are LI over ℚ
  (`specRow_linearIndependent` → `LinearIndependent.rank_matrix`, maximal nonsingular minor).
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
  has been re-split: its LI core `lem:k-frame-specialize-li` (`Graph.specRow_linearIndependent`) and
  the fraction-field reduction `lem:k-frame-li-over-poly-ring`
  (`Graph.linearIndepOn_kFrameRow_iff_over_polyRing`, via `LinearIndependent.iff_fractionRing`) and
  the forest-extraction step `lem:k-frame-forest-packing-of-sparse`
  (`Graph.exists_forestPacking_cover_of_isSparse_restrict`) are landed, and the abstract
  **minor-nonvanishing engine** `Matrix.linearIndependent_rows_of_specialized_submatrix_det_ne_zero`
  (mirror in `Mathlib/LinearAlgebra/Matrix/Rank.lean`) is now landed too — the determinant-routed
  reflection that turns "the φ-specialized minor det is nonzero" into "the generic rows are LI over
  `R`" (the coefficient-wise reflection is false; see FRICTION). The remaining open work is the
  **wiring step**: instantiate that engine on the `kFrameRow`-over-`R` matrix with the forest-packing
  column selection and the `MvPolynomial`-eval specialization to finish `lem:k-frame-specialize-forest`.

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
(`Graph.specRow_linearIndependent`) is landed: the block-diagonal specialization on a forest
packing is LI over `K`, assembled from per-forest incidence-row LI
(`Graph.orientation.isAcyclicSet_linearIndepOn`) by `Pi.linearIndependent_single`. The **first
half of the genericity-lift** `lem:k-frame-li-over-poly-ring`
(`Graph.linearIndepOn_kFrameRow_iff_over_polyRing`) is also landed: generic LI over
`K = Frac R` ⟺ LI over `R = MvPolynomial (β × Fin k) ℚ`, via `LinearIndependent.iff_fractionRing`
on the fixed row family. This moves the remaining argument off the fraction field onto the
integral domain `R`. The **forest-extraction step** `lem:k-frame-forest-packing-of-sparse`
(`Graph.exists_forestPacking_cover_of_isSparse_restrict`) is also landed: from
`(G ↾ E').IsSparse k k` it produces a `k`-tuple `Fs : Fin k → Set β` of acyclic bar sets covering
`E'` exactly (via `unionPow_cycleMatroid_indep_iff_isSparse_restrict` + `Matroid.union_indep_iff` +
`cycleMatroid_indep`) — the family on which `lem:k-frame-specialize-li` places its block-diagonal
full-rank matrix.

The **abstract minor-nonvanishing engine** is now landed too:
`Matrix.linearIndependent_rows_of_specialized_submatrix_det_ne_zero`
(`Mathlib/LinearAlgebra/Matrix/Rank.lean`) — for rows `M : ι → κ → R` over a domain `R`, a column
selection `e : ι → κ`, and a ring hom `φ : R →+* S` (`S` nontrivial), `φ (submatrix (M∘e)).det ≠ 0`
⟹ `LinearIndependent R M`. This is the determinant-routed reflection the whole reverse half hinges
on (the coefficient-wise reflection is *false* when `φ` has a nontrivial kernel — see FRICTION).

The **specialization identity** `lem:k-frame-specialize-identity`
(`Graph.forestEval_kFrameRowR_eq_single`) is now landed — the `R`-lift half of the wiring step. It
introduces the `R = MvPolynomial (β × Fin k) ℚ`-valued row `Graph.kFrameRowR`, the algebra-map
bridge `Graph.kFrameRow_eq_map_kFrameRowR` (via the ring-hom naturality helper
`Graph.signedIncMatrix_map`), the forest-packing evaluation hom `Graph.forestEval`, and the identity
that, for a **disjoint** `k`-forest packing and `e ∈ Fs j₀`, entrywise-`forestEval`-specializing
`kFrameRowR k D e` gives exactly the block-`single` row `Pi.single j₀ (signedIncMatrix ℚ e)` of
`specRow_linearIndependent`.

The next concrete commit is the **minor / det step** that finishes `lem:k-frame-specialize-forest`
(now the leaf-most red node). Given `(G ↾ E').IsSparse k k`, target `LinearIndepOn K (kFrameRow k D)
E'` via `linearIndepOn_kFrameRow_iff_over_polyRing` (reduce to `R`) + `kFrameRow_eq_map_kFrameRowR`
(work with the `R`-row `kFrameRowR`). Concretely: (i) get a **disjoint** forest packing covering
`E'` — disjointify `exists_forestPacking_cover_of_isSparse_restrict` via
`Fintype.exists_disjointed_le` (as in `tutte_nash_williams`), or reuse Phase 13's `IsForestPacking`
on `G ↾ E'`; (ii) reindex `LinearIndepOn R (kFrameRowR k D) E'` to `LinearIndependent R (M : E' → κ →
R)`, `κ = Fin k × α`; (iii) feed the engine
`Matrix.linearIndependent_rows_of_specialized_submatrix_det_ne_zero` the hom `forestEval Fs`, where
by `forestEval_kFrameRowR_eq_single` the specialized rows are the block-`single` `specRow` matrix
(reindexed via the disjoint cover bijection `E' ≃ Σ j, Fs j`); (iv) the square column selection +
nonzero specialized det come from the forest rows being LI over ℚ (`specRow_linearIndependent` →
`LinearIndependent.rank_matrix`, then a maximal nonsingular minor — the one remaining "LI rows ⟹
nonzero square minor" step to locate/prove). If it overshoots, the maximal-minor step is the natural
further split.

After it, `lem:k-frame-indep-iff-count` packages both halves against
`thm:unionPow-cycle-indep-iff-sparse` (Phase 13); then `thm:k-frame-union-cycle`
closes Phase 14 (a short `Matroid.ext_indep`) and carries the phase-completion
checklist (ROADMAP ✓, status surfaces, compress §14).

After the two genericity halves and `lem:k-frame-indep-iff-count` land,
`thm:k-frame-union-cycle` is a short `Matroid.ext_indep`; **that** commit
closes Phase 14 and unblocks Phase 15 (body-bar Tay theorem, existence
form), so it carries the phase-completion checklist (ROADMAP row ✓,
status surfaces, compress ROADMAP §14).
