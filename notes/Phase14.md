# Phase 14 — k-frame matroid = k-fold cycle-matroid union (work log)

**Status:** ✓ Complete.

Forward-mode phase. The authoritative dep-graph and lemma index is the
*The $k$-frame matroid as a union of cycle matroids* subsection
(`sec:body-bar-k-frame`) of `blueprint/src/chapter/body-bar.tex`; this
file carries current state, decisions, and hand-off, and does **not**
duplicate the lemma list. The full per-node landing sequence is the
commit log `17178ef..b90516d` (14 forward-work commits, one per
blueprint node); read it for the build order.

## Current state

**Phase 14 is complete.** Whiteley 1988 Theorem 1
(`Graph.kFrameMatroid_eq_unionPow_cycleMatroid`, `BodyBar/KFrame.lean`):
the generic `k`-frame matroid `F(G, X)` on a multigraph `Graph α β`
(`Matroid.ofFun` over `KFrameField β k = FractionRing (MvPolynomial
(β × Fin k) ℚ)`) equals `(Matroid.Union (fun _ : Fin k ↦
G.cycleMatroid)) ↾ E(G)`. The `↾ E(G)` is **mathematically forced**
(the vendored `Matroid.Union` has ground `univ : Set β`); see
*Decisions → Ground-set restriction*.

The proof routes through the count interface (Whiteley §2.1), not a
bespoke `kFrameMatroid` `Rep`:
- Forward (`forest_count_of_linearIndepOn_kFrameRow`): generic row-LI
  over `K` ⟹ `∀ Y ⊆ E', |Y| ≤ k · r_{cycleMatroid}(Y)`, by a
  **rank count** (`blockPiSpanOn` + `finrank_blockPiSpanOn`), replacing
  Whiteley's nonzero-monomial determinant expansion.
- Reverse (`linearIndepOn_kFrameRow_of_isSparse_restrict`):
  `(G ↾ E').IsSparse k k` ⟹ row-LI, by a disjoint forest-packing
  block-diagonal specialization (`specRow_linearIndependent`) fed
  through the minor-nonvanishing engine
  (`Matrix.linearIndependent_rows_of_specialized_submatrix_det_ne_zero`,
  mirror in `Mathlib/LinearAlgebra/Matrix/Rank.lean`).
- Bridge (`kFrameMatroid_indep_iff_isSparse_restrict`): packages both
  via `Matroid.ofFun_indep_iff` + Phase 13's
  `unionPow_cycleMatroid_indep_iff_isSparse_restrict` /
  `Matroid.Union_pow_indep_iff_count`; the top theorem then collapses
  to `Matroid.ext_indep` on the shared ground set `E(G)`.

Axioms: `propext`, `Classical.choice`, `Quot.sound` (no `sorryAx`).
Phase 13 (`BodyBar/TreePacking.lean`) is the upstream dependency.

## Architectural choices made up front

Carried from ROADMAP §14–§15 and `DESIGN.md`:
- **Carrier = mathlib core `Graph α β`** (same as Phase 13), on which
  `apnelson1/Matroid`'s `cycleMatroid` sits. Phases 1–11 stay on
  `SimpleGraph`.
- **Coefficient ring / genericity** via `Matroid.ofFun` over
  indeterminate coefficients — the exact encoding is pinned in
  *Decisions → Coefficient encoding* below.
- **`Matroid`-namespace / `Graph`-namespace split** (Phases 12–15
  exception): graph-level `kFrameMatroid` under `namespace Graph` for
  dot-notation beside `Graph.cycleMatroid`.

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
  reuse-of-`signedIncMatrix` is what makes `thm:k-frame-union-cycle`
  reduce cleanly to `k` independent `cycleMatroid` representations
  rather than re-deriving the incidence pattern. **Load-bearing for
  Phase 15** (the Plücker / two-extensor specialization specializes
  these indeterminates).

- **Ground-set restriction on the union side (`thm:k-frame-union-cycle`).** The
  documented target `G.kFrameMatroid k = Matroid.Union (fun _ ↦ G.cycleMatroid)`
  is **not provable as a bare equality**: the vendored `Matroid.Union Ms =
  (sum' Ms).adjMap _ univ` has ground set `univ : Set β` (`adjMap_ground_eq`),
  whereas `kFrameMatroid` (`Matroid.ofFun … E(G) …`) has ground `E(G)`. The two
  agree on independent sets (both `⊆ E(G)`) but differ on ground (non-edges of
  `β` are loops in the union, absent from `kFrameMatroid`). The honest theorem
  restricts the union to `E(G)`:
  `G.kFrameMatroid k = (Matroid.Union (fun _ ↦ G.cycleMatroid)) ↾ E(G)`. Both
  sides then have ground `E(G)` and the `Matroid.ext_indep` goes through. Needs
  `[DecidableEq β]` in the signature (the `Matroid.Union` term in the *type*
  demands it, unlike the count-bridge node where it only appeared in the body).
  **Load-bearing for Phase 15** (if `Matroid.Union`'s `univ` ground recurs,
  the `↾ E(G)` restriction pattern is the fix).

### Re-scoping of `thm:k-frame-union-cycle`

- **Why.** The monolithic theorem bundles (i) Whiteley §2.1's generic
  column-reorder / nonzero-monomial argument over `K = Frac ℚ[X_{e,j}]`,
  in *both* directions, with (ii) the matroid-equality plumbing. Too
  much for one subagent commit; re-scoped (user-approved) into the
  node chain now green in `sec:body-bar-k-frame`.
- **Routing decision.** Go through the `Matroid.ofFun_indep_iff` row-LI
  characterization, **not** a bespoke `kFrameMatroid` `Rep`. The two
  genericity halves produce/consume the *count* form
  `∀ Y ⊆ E', |Y| ≤ k · r_{cycleMatroid}(Y)`, which is exactly what
  Phase 13's `unionPow_cycleMatroid_indep_iff_isSparse_restrict` (via
  `Matroid.Union_pow_indep_iff_count`) attaches to the union side. So
  the count is the shared interface; `lem:k-frame-indep-iff-count` is
  the bridge node and `thm:k-frame-union-cycle` collapses to
  `Matroid.ext_indep`.
- **Forward route re-cast to a rank count.** The forward half was
  re-cast from Whiteley's nonzero-monomial determinant expansion to a
  **rank-counting** argument (avoids the `MvPolynomial` determinant
  machinery entirely; both give the same bound). The `r(E(G))`-vs-`r(Y)`
  wrinkle was resolved by the `Y`-restricted block span
  `Graph.blockPiSpanOn` (block `W_Y = span (signedIncMatrix '' Y)`).

### Promoted to FRICTION
- *`signedIncMatrix` decidability instances inside a `noncomputable def`
  body* → FRICTION `[matroid]` *`Graph.orientation.signedIncMatrix` needs
  `[DecidableEq α]` + `[DecidablePred (· ∈ E(G))]` …* (term-level `letI`
  with `Classical.dec*`, keeping the def signature binder-free).
- *Minor-nonvanishing reflection is determinant-routed, not
  coefficient-wise* → FRICTION (the coefficient-wise reflection is
  false; the det-routed mirror
  `Matrix.linearIndependent_rows_of_specialized_submatrix_det_ne_zero` +
  `Matrix.exists_submatrix_det_ne_zero_of_linearIndependent_rows` are
  the correct bridge).

## Blockers / open questions

<none — all resolved at phase close. The genericity-argument routing
(`Matroid.ofFun_indep_iff` vs bespoke `Rep`) and the forward-route
re-cast to a rank count are recorded in *Re-scoping* above.>

## Hand-off / next phase

**Phase 14 is complete.** `thm:k-frame-union-cycle`
(`Graph.kFrameMatroid_eq_unionPow_cycleMatroid`, `BodyBar/KFrame.lean`) landed as a
`Matroid.ext_indep`: `G.kFrameMatroid k = (Matroid.Union (fun _ : Fin k ↦ G.cycleMatroid)) ↾ E(G)`.
The ground-set obligation closes by `kFrameMatroid_ground` + `Matroid.restrict_ground_eq`; the
indep-iff obligation rewrites through `Matroid.restrict_indep_iff` + `and_iff_left hI`, then matches
the two count-characterizations (`kFrameMatroid_indep_iff_isSparse_restrict` and Phase 13's
`unionPow_cycleMatroid_indep_iff_isSparse_restrict`) on `E' ⊆ E(G)`. **The `↾ E(G)` is mathematically
forced**, not a convenience — see *Decisions → Ground-set restriction on the union side*.

**Next phase: Phase 15 (Body-bar Tay theorem).** Now unblocked — `thm:tay-witness` in `body-bar.tex`
consumes `thm:k-frame-union-cycle` (via the standard-basis Plücker / two-extensor specialization of
the indeterminate `k`-frame coefficients) alongside `thm:tutte-nash-williams` / `cor:k-spanning-trees`.
See ROADMAP §15 for the architectural decisions (carrier `Graph α β`, inline Plücker coordinates,
existence-of-realization form only). The smallest first commit there opens Phase 15:
`notes/Phase15.md` + the framework definitions (`def:body-bar-framework`,
`def:infinitesimally-rigid-body-bar`) under `BodyBar/Framework.lean`. If `Matroid.Union`'s `univ`
ground recurs in Phase 15, the `↾ E(G)` restriction pattern from this phase is the fix.
