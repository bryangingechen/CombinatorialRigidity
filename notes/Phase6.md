# Phase 6 — Laman's theorem, (⇒) direction (work log)

**Status:** in progress.

This file is the per-phase work record. See `../ROADMAP.md` §6 for the
high-level plan and `../DESIGN.md` for cross-cutting design choices.

**Workflow:** Phase 6 runs in **forward blueprint mode** (Option C,
hybrid skeleton) per `../blueprint/DESIGN.md`. The blueprint chapter
`chapter/laman-theorem.tex` (its $\Rightarrow$-direction subsection)
is the authoritative dep-graph and lemma index; this file does **not**
duplicate it. Each Lean session picks a leaf-most red node from the
dep-graph, formalizes it, and adds `\lean{...}` + `\leanok` to its
blueprint entry. Phase-end pass: write 1–3-sentence prose proofs per
entry against the now-stable Lean.

## Current state

Phase 5 closed with the iff statement
`isGenericallyRigid_two_iff_exists_isLaman_le` composed but
`sorry`-blocked on `IsGenericallyRigid.exists_isLaman_le`
(`LamanTheorem.lean:122`). That one `sorry` is the entire Phase 6
target — the project has no other unproved declarations.

**Through commit 16 (this commit):** task-3 of the Lean-simplification
pass is landed (commit 14) and `TrivialMotions.lean` got a TACTICS § 1
grind-default golf pass alongside (commit 15). Tasks 1–3 of the
simplification pass are now all resolved; task 4 (the d-general lift
of the affinely-spanning placement) is in progress — its mirror
infrastructure landed this commit (16); the d-general theorem body
and the retire-dim-2 pass remain. The linear-algebra side is closed d-general (rank bounds,
kernel bound, basis-pick); the analysis side is closed at dim 2
(affinely-spanning rigid placement). The only red nodes left in
`chapter/laman-theorem.tex` are `lem:isSparse-of-rowIndependent-two`
(the substantive sparsity step) and the assembly target
`thm:isGenericallyRigid-exists-isLaman-le`. See *Done* below for
per-commit detail and *Hand-off / next phase* for the sparsity sketch,
the d-general lift of the affinely-spanning placement (task 4), and a
low-priority "project-wide grind sweep" note added under *Future
polish*.

## Architectural choices made up front

These extend `../DESIGN.md` *Choices to revisit*; if any turns out
wrong, revisit there.

- **Forward-mode blueprint authoring** (Option C). The blueprint
  chapter's $\Rightarrow$-direction subsection becomes the
  authoritative dep-graph from Phase 6 commit 1; `\lean{...}` and
  `\leanok` get added as each Lean lemma lands. Prose proofs are
  deferred to a phase-end pass. Rationale lives in
  `../blueprint/DESIGN.md` *Recommendation for Phase 6*. We do
  **not** maintain a parallel lemma checklist in this file — the
  dep-graph is the single source of truth, and parallel lists rot.

- **New file `RigidityMatroid.lean`.** Per ROADMAP §6 and DESIGN.md
  *Notion- and matroid-agnostic core* / *Why Henneberg, not matroid*.
  Phase 4 deliberately kept the abstract rigidity matroid out of
  `Framework.lean`; Phase 6 stands the file up alongside it. Lives
  at `CombinatorialRigidity/RigidityMatroid.lean`; imported by
  `LamanTheorem.lean`.

- **Stay matroid-agnostic in the proof body; defer the abstract
  `Matroid` packaging.** The honest minimum surface area for closing
  `exists_isLaman_le` is two linear-algebra ingredients
  (a rank lower bound for generically-rigid placements, and a
  $(2,3)$-sparsity-from-row-independence lemma); neither requires
  `Mathlib.Combinatorics.Matroid`. Building the `Matroid` instance is
  reusable infrastructure but not on the critical path. Defer; revisit
  at end of Phase 6 if it ends up trivial once the supporting
  lemmas land.

- **Lovász–Yemini's "easy direction" only.** Closing
  `exists_isLaman_le` needs only *row-independent in rigidity matroid
  $\Rightarrow$ $(2,3)$-sparse subgraph*. The harder converse
  $(2,3)$-sparse $\Rightarrow$ row-independent at a generic placement
  is the deep half of Lovász–Yemini and is **not needed** for the iff;
  Phase 6 ships without it. If a future phase wants the full
  equality, that's a separate milestone.

- **`TrivialMotions` Phase 4 deferred API may need to land here.**
  The $(2,3)$-sparsity argument uses the rank bound
  $\rk\,R_{H[S]}(p|_S) \le 2|S| - 3$ for $|S| \ge 3$, which goes
  through the affinely-spanning-implies-$\dim\,\mathrm{TrivialMotions} = 3$
  identity (Phase 4 *Lemma checklist*, deferred). Exact form is TBD;
  flagged under *Blockers* below.

## Lemma checklist

**Maintained in the blueprint, not here.** The authoritative checklist
is `chapter/laman-theorem.tex`'s $\Rightarrow$-direction subsection,
visible as a dep-graph at `blueprint/web/dep_graph_document.html`
after `inv bp && inv web`. A red node = not yet formalized; a green
node = formalized and `\leanok`-tagged. Pick leaf-most red.

Status snapshot at commit 13: the remaining red nodes in
`chapter/laman-theorem.tex` are `lem:isSparse-of-rowIndependent-two`
and the assembly target `thm:isGenericallyRigid-exists-isLaman-le`.
Sparsity stacks on the d-general rank upper bound at `d = 2` plus
the affinely-spanning placement (commit 11); assembly stacks on
sparsity plus the basis-pick (commit 6).

## Decisions made during this phase

### Phase-local choices and proof techniques

- **d-general only; no d=2 corollary surface.** Commit 10 retired the
  d=2 corollaries of the rank bounds and the kernel bound; callers at
  `d = 2` consume the d-general lemmas directly because
  `2 * (2 + 1) / 2` reduces to `3` by `rfl` on `Nat` literals. See
  commit 10 *Done* entry for the deleted symbols and *Design pattern
  established* (file end) for the forward-looking rule. *Asymmetry:*
  the rank/kernel bounds are general infrastructure where
  `d (d + 1) / 2` is parametric; the basis-pick
  `exists_edgeSetRowIndependent_basis_dim_two` stays dim-2-shaped
  because its conclusion `|I| = 2 * #V - 3` is structurally dim-2.

- **Dual-bridge for the basis-pick.** `EdgeSetRowIndependent` is stated
  as `LinearIndepOn` of a family of plain functions `Framework V d →
  ℝ` (matching the blueprint), but the rank identities we need
  (`LinearMap.finrank_range_dualMap_eq_finrank_range`,
  `Pi.basisFun.dualBasis`) require viewing the rows as linear
  functionals (`Module.Dual ℝ (Framework V d)`). The basis-pick proof
  works in the dual module throughout (via `rigidityRow` and
  `span_range_rigidityRow`), then transports the LI back to the
  function-module form via
  `edgeSetRowIndependent_iff_linearIndepOn_rigidityRow`. The function-
  to-dual envelope uses mathlib's `LinearMap.ltoFun ℝ _ ℝ ℝ` +
  `DFunLike.coe_injective` (discovered in commit 12; an earlier
  private `dualToFunₗ` scaffold has been retired).

- **`apnelson1/Matroid` investigated, not adopted.** The external repo
  ships `Module.matroid` (in `Matroid/Representation/Map.lean`) — a
  `Matroid W` whose ground set is a vector space and whose
  independence is linear independence — and the derived `Matroid.ofFun
  𝔽 E f` for an arbitrary function `f : α → W`, both built on top of
  `IndepMatroid.ofFinitaryCardAugment`. Toolchain pin
  (`leanprover/lean4:v4.30.0-rc2`) matches ours exactly. *Not adopted*
  because the abstraction does not collapse the hard step: the
  basis-pick lemma needs column-rank-to-row-rank
  (`LinearMap.finrank_range_dualMap_eq_finrank_range`,
  `Mathlib/LinearAlgebra/Dual/Lemmas.lean:918`) either way, and going
  through `Matroid.ofFun` would only hide that step inside
  `Matroid.ofFun`'s rank API rather than remove it. Branch (c) of the
  *Hand-off* plan wins on cost: ~30 lines of pure linear algebra, no
  new dep, no new mirror.

- **TrivialMotions API in its own file, d-general.** Per the user's
  Phase 6 design-pivot (commit 7), the trivial-motions API lives in
  `CombinatorialRigidity/TrivialMotions.lean` (parallel to
  `Framework.lean`) rather than buried inside `RigidityMatroid.lean`.
  The motions are general framework infrastructure, not matroid-
  specific; the submodule formulation lets `trivialMotions_le_ker`
  ship as one unconditional lemma and the finrank bound as a
  `Submodule.finrank_mono` one-liner. The blueprint chapter
  `chapter/trivial-motions.tex` mirrors the Lean file 1:1.

- **`rotJTwo` defined directly, not via `Matrix.toEuclideanLin`.** First
  attempt routed `rotJTwo := Matrix.toEuclideanLin !![0, -1; 1, 0]`,
  which left downstream `simp` calls fighting `Matrix.mulVec` /
  `Matrix.dotProduct` / `Matrix.vecHead` unfolding. Switched to a
  direct `LinearMap.mk' (fun v => !₂[-(v 1), v 0])` so that
  `rotJTwo_apply_zero/one` are `rfl`-simp lemmas; downstream proofs
  then close coordinates without matrix-unfolding hints. FRICTION
  entry filed (*Defining the 2×2 90° rotation via `Matrix.toEuclideanLin`
  blocks coordinate simp*).

- **Skew-sum + affine-spanning route for the d-general LI.** The
  d-general `trivialMotionFamily_linearIndependent` (commit 8)
  routes through an intermediate skew-sum endomorphism `S` of
  `EuclideanSpace ℝ (Fin d)`: the vanishing combination at vertex
  `v` reads `t + S(p v) = 0`, subtracting at two vertices kills `t`
  and yields `S = 0` on differences, then affine spanning +
  `LinearMap.eqOn_span` extends to `S = 0`. The named-linear-map
  abstraction is doing real work — the affine-spanning step is
  naturally stated about a linear map vanishing on a spanning set —
  so the pure-coordinate alternative was rejected. See commit 8
  *Done* entry.

### Promoted to TACTICS / FRICTION / DESIGN

*(none yet — the trivial-motions specifics stay phase-local; the FRICTION
entries opened in commit 7 are the cross-cutting record.)*

### Cleanup pass summaries

*(none yet)*

## Blockers / open questions

All four phase-start blockers resolved: linear-algebra basis-pick
(commit 6), `TrivialMotions` Phase 4 deferred API (commit 7),
d-general finrank lower bound (commit 8), and generic-placement
affine-spanning lemma (commit 11). See the corresponding *Done*
entries for resolution details.

## Hand-off / next phase

**Done:**
- *Commit 0 (`fdbcbd9`):* Phase 6 notes seeded; ROADMAP Status row
  flipped; forward-mode workflow surfaced in top-level `CLAUDE.md`.
- *Commit 1 (`39b2152`):* forward-mode blueprint skeleton for the
  $\Rightarrow$ direction — six red nodes in `chapter/laman-theorem.tex`
  with `\uses{...}` chains.
- *Commit 2 (`cd0398f`):* bibliography + attribution chain
  (Laman 1970 / Asimow–Roth 1978 / Jordán 2016 §1.3.1; Lovász–Yemini
  1982 acknowledged for the matroid framing).
- *Commit 3 (`93908d8`):* `RigidityMatroid.lean` +
  `rigidityMap_finrank_range_ge_of_isGenericallyRigid_two`
  (one-liner via rank-nullity + `Framework.finrank` + `omega`).
- *Commit 4 (`e3918d1`):* `EdgeSetRowIndependent G p I` plus
  `.mono` / `_empty` helpers.
- *Commit 5 (`5f11c6b`):* `apnelson1/Matroid` investigation (notes-only)
  → branch (c), matroid-agnostic. See *Decisions*.
- *Commit 6 (`7a687fa`):* basis-pick
  `exists_edgeSetRowIndependent_basis_dim_two` plus `rigidityRow` /
  `span_range_rigidityRow` /
  `edgeSetRowIndependent_iff_linearIndepOn_rigidityRow`, with a
  private `dualToFunₗ` bridge (later retired in commit 12). FRICTION
  entry filed.
- *Commit 7 (`49c693a`):* `TrivialMotions.lean` — d-general
  `translationMotion` / `infinitesimalRotation` / `trivialMotions`,
  the unconditional `trivialMotions_le_ker`, and dim-2 surface
  (`rotJTwo` via direct `LinearMap.mk'`, plus the two
  `_three_le_finrank/ker_of_affinelySpanning_two` lemmas — all
  retired in commit 10). New blueprint chapter
  `chapter/trivial-motions.tex` mirrors the file 1:1. Three new
  FRICTION entries.
- *Commit 8 (`6b104da`):* d-general finrank lower bound
  `trivialMotions_finrank_ge_of_affinelySpanning`. Routes the LI of
  `trivialMotionFamily` through a skew-sum endomorphism `S` that
  vanishes on differences `p v - p w` and extends to `S = 0` via
  affine spanning + `LinearMap.eqOn_span`; rotation coefficients
  extracted via `(S e_{j'}).ofLp i`; cardinality from
  `Finset.sum_range_id`. New `elemSkewMap (i j : Fin d)` +
  `inner_elemSkewMap_self`. Subsumes the ~100 LoC dim-2 proof from
  commit 7 (now a one-line corollary). Six new green blueprint
  nodes in `chapter/trivial-motions.tex`.
- *Commit 9 (`f87c09f`):* rank upper bound `_le_of_affinelySpanning_two`
  in `RigidityMatroid.lean` — ~5 lines of `omega` over the same
  rank-nullity + `Framework.finrank` template as commit 3, fed by
  commit 7's kernel lemma. The `|V| ≥ 2` hypothesis on the blueprint
  statement was dropped (affine-span forces `|V| ≥ 3`). *(d=2 form
  retired in commit 10; the d-general
  `rigidityMap_finrank_range_le_of_affinelySpanning` replaces it.)*
- *Commit 10:* d-general lift; d=2 corollary surface retired. New
  `rigidityMap_ker_finrank_ge_of_affinelySpanning` in
  `TrivialMotions.lean`. Generalised commits 3 and 9's rank bounds
  to their d-general statements; the d=2 corollaries are deleted
  (callers consume the d-general lemmas at `d = 2` with zero
  specialisation ceremony — see *Design pattern established*
  below). Six declarations removed:
  `trivialMotions_three_le_finrank/ker_of_affinelySpanning_two`,
  `rigidityMap_finrank_range_ge/le_..._two`, `rotJTwo` + apply
  lemmas + `inner_rotJTwo_self`. `EuclideanDist` import dropped
  from `TrivialMotions.lean`. Blueprint chapters updated.
- *Commit 11:* analysis leaf — affinely-spanning rigid placement
  `exists_affinelySpanning_rigid_placement_two`. Vandermonde
  perturbation `w v = (φ v, (φ v)²)`; the per-triple collinearity
  determinant is a quadratic in `t` with leading coefficient
  `(φ b − φ a)(φ c − φ a)(φ c − φ b) ≠ 0`; finite union of
  per-triple bad sets avoided by a point in `(0, ε) \ bad`. ~150
  LoC alongside two private helpers `finite_zeros_quadratic` and
  `linearIndependent_pair_of_det_ne_zero`. Imports
  `Mathlib.Algebra.Polynomial.Roots` + `…AffineSpace.FiniteDimensional`.
  Dim-2-shaped; d-general lift is task 4 of the pending pass.
- *Commit 12:* Lean-simplification task 2 (*"small dual bridge
  isn't small"*). The ~16-line private `dualToFunₗ` scaffold
  collapsed to `LinearMap.ltoFun ℝ _ ℝ ℝ` +
  `DFunLike.coe_injective` (discovered via `lean_loogle` on
  `(_ →ₗ[_] _) →ₗ[_] (_ → _)`); the matrix-level
  `Matrix.rank_transpose` alternative was assessed and declined;
  `rigidityRow` / `span_range_rigidityRow` /
  `edgeSetRowIndependent_iff_linearIndepOn_rigidityRow` promoted to
  named blueprint concepts under new subsubsection *The rigidity
  rows as a family in the algebraic dual* in
  `chapter/laman-theorem.tex`; `span_range_rigidityRow` shrunk
  from ~22 to ~10 lines via the `Set.range_comp` +
  `Submodule.span_image` + `Basis.dualBasis.span_eq` +
  `Submodule.map_top` chain. FRICTION *No packaged ℝ-linear
  injection* flipped to **[resolved]**.
- *Commit 13 (`c27c20e`):* mirror the two upstream-eligible
  linear-algebra lemmas surfaced by task 2. New file
  `CombinatorialRigidity/Mathlib/LinearAlgebra/Dual/Basis.lean`
  carries `Pi.basisFun_dualBasis` (`@[simp]`) and
  `LinearMap.range_dualMap_eq_span_image_dualBasis` (Part 1 of
  Strang's FTLA in span form). `span_range_rigidityRow` consumes
  the second directly; its body shrinks from ~10 to ~4 lines.
  FRICTION *Mirrored* gains a combined entry. Both verified
  genuinely absent from upstream (`Dual/Basis.lean` does not even
  import `StdBasis.lean`, which is the structural reason gap #1
  was unfilled).
- *Commit 14 (`f6a24b5`):* Lean-simplification task 3
  (*"cross-terms vanish hides a 30-line case-split"*). Hoisted
  candidate-2 from the task list: new named lemma
  `elemSkewMap_ofLp_inr_apply` (~33 lines) captures the
  cross-term-vanishing fact "evaluating
  `elemSkewMap s.1 ⟨s.2.val, _⟩` at the basis vector
  `e_{⟨j.val, _⟩}` and reading coord `i` gives the
  single indicator `if s = ⟨i, j⟩ then 1 else 0`". The rotation
  branch of `trivialMotionFamily_linearIndependent` then collapses
  from ~50 lines (`Finset.sum_eq_single` + 30-line `split_ifs` +
  `omega` over `Fin.val` comparisons) to ~14 lines (one
  `simp_rw [elemSkewMap_ofLp_inr_apply ...]` + `Finset.sum_ite_eq'`).
  The helper proof uses `simp only [Sigma.mk.injEq, heq_eq_eq,
  Fin.ext_iff, true_and]` to align the sigma- and Fin-level
  equalities (a `rw [Fin.mk.injEq]` motive-typing issue forced the
  `simp` route — `if-then-else` inner Props don't admit the rewrite
  cleanly). Three `omega` closers replaced with `grind only`
  per TACTICS § 1. The `set j' := ⟨j.val, _⟩` scaffold in the
  outer proof is retired in favour of the explicit form so the
  helper's literal `⟨j.val, j.isLt.trans i.isLt⟩` shape matches.
- *Commit 16 (this commit):* task-4 (d-general lift) infrastructure.
  Mirror lemma `Matrix.det_powerDifferences` lands under
  `CombinatorialRigidity/Mathlib/LinearAlgebra/Vandermonde.lean`: for
  `v : Fin (n + 1) → R` over a `CommRing`, the `n × n` matrix
  `M i j = v i.succ ^ (j.val + 1) - v 0 ^ (j.val + 1)` has
  `det M = ∏_{0 ≤ i < j ≤ n} (v j - v i)`. The proof realises `M` as
  the `(Fin.succ, Fin.succ)`-minor of the
  `Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde` evaluation
  matrix on the polynomial family `p 0 = 1`,
  `p k.succ = X^(k.val + 1) - C (v 0 ^ (k.val + 1))`, then
  cofactor-expands along the sparse row 0 via `det_succ_row_zero` +
  `Finset.sum_eq_single 0`. `nontriviality R` discharges the
  trivial-ring case. FRICTION *Mirrored* gains a combined entry.
  Substantively, this is the *leading-coefficient* half of task 4
  (the dim-2 `γ = (φ b − φ a)(φ c − φ a)(φ c − φ b)` factoring goes
  d-general); the AffineIndependent ↔ det bridge and the theorem
  assembly remain. (Task-3 search of mathlib located the
  polynomial-of-det machinery already in
  `Mathlib/LinearAlgebra/Matrix/Polynomial.lean`:
  `natDegree_det_X_add_C_le`, `coeff_det_X_add_C_zero/card` — no
  mirror needed there.)

- *Commit 15 (`ac194c1`):* TACTICS § 1 golf pass over
  `TrivialMotions.lean` (this file did most of its proof work
  before TACTICS § 1's "default to `grind`" rule landed in current
  form). Net 37 lines deleted, no logic changes:
  * `elemSkewMap_ofLp_inr_apply` body collapses from ~17 lines
    (`rcases` + two case-bodies with three `have`s + `split_ifs` +
    `absurd` + `all_goals rfl`) to a single one-liner:
    `rcases eq_or_ne i a with rfl | hia <;> split_ifs <;> grind`.
    `grind` solves every leaf of the case-tree using `b.isLt` /
    `j.isLt` directly from the ordered-pair-type subtyping.
  * `inner_elemSkewMap_self`'s `i ≠ j` branch: closing `simp; ring`
    becomes `grind`.
  * `trivialMotionFamily_linearIndependent`'s Steps 1–5 are
    rewritten in `fun … => by simpa [...]` / `simpa [...] using …`
    term-mode style; `ht_coord` / `h_combine` / `h_S_diff` /
    `h_t_zero` / the rotation extraction all shrink to one or two
    lines. The redundant `Finset.sum_ite_eq` rewrites (it's a
    `simp` lemma) are dropped from `ht_coord` and the rotation
    extraction. The intermediate `hS` (`S (e_{j'}) = 0`)
    disappears: `rw [h_S_zero] at h_extract` substitutes `S = 0`
    directly into the closed-form extraction, then `simpa using
    h_extract.symm` finishes.

**Encoding choice rationale (`I : Set G.edgeSet`).** The index type
sits inside `G.edgeSet`, matching the blueprint's "$I \subseteq E(G)$".
Downstream, the spanning-subgraph construction needs `Set (Sym2 V)`
not `Set G.edgeSet`, so the assembly proof will transport via
`Subtype.val '' I`. We pay that adapter cost once at assembly rather
than carry it through the basis lemma + sparsity lemma + every
intermediate API.

**Pending Lean-simplification pass (before or alongside the sparsity
work).** A session-start blueprint↔Lean review flagged three points
where the Lean is more involved than the blueprint prose suggests.
Per the project rule (`blueprint/CLAUDE.md` *Proof verbosity*), the
first response is to make the Lean as painless as the math — better
proof strategy, upstreamable helper, sharper mathlib tactic /
proof-automation use — and only on failure to add a prose aside.
Tasks, ordered by severity (heaviest first):

1. ~~**`exists_affinelySpanning_rigid_placement_two` — AffineIndependent
   $\Leftrightarrow$ nonzero $2\times 2$ det elided.**~~ **Substantially
   resolved** (commit `48ee391`) via mathlib's `finSuccAboveEquiv` +
   `linearIndependent_equiv` (FRICTION *AffineIndependent ↔
   LinearIndependent reindex* now [resolved]). Two remaining
   sub-candidates — mirror `linearIndependent_pair_of_det_ne_zero`,
   inline the eight `set` scalars — are deliberately deferred in
   favour of task 4 (the d-general lift subsumes both: the helper is
   superseded by `Matrix.linearIndependent_rows_of_det_ne_zero` and
   the scalars dissolve into `Matrix.det (M_0 + t · M_1)`).

2. ~~**`exists_edgeSetRowIndependent_basis_dim_two` — "small dual
   bridge" isn't small.**~~ **Resolved** (commits 12 and 13). The
   ~60-line bridge dropped to ~25 lines via `LinearMap.ltoFun`
   replacing the private `dualToFunₗ` scaffold, a tightened
   `span_range_rigidityRow` proof, and blueprint promotion of
   `rigidityRow` to a named concept. The matrix-level
   `Matrix.rank_transpose` alternative was assessed and declined.
   Two upstream-eligible lemmas (`Pi.basisFun_dualBasis`,
   `LinearMap.range_dualMap_eq_span_image_dualBasis`) mirrored under
   `Mathlib/LinearAlgebra/Dual/Basis.lean`. See commit-12 / commit-13
   *Done* entries.

3. ~~**`trivialMotionFamily_linearIndependent` — "cross-terms vanish"
   hides a 30-line case-split.**~~ **Resolved** (commit 14). Candidate
   2 (hoist a named lemma) won outright. New
   `elemSkewMap_ofLp_inr_apply` (~33 lines) captures the
   cross-term-vanishing fact directly; the rotation branch of the
   LI proof collapses from ~50 lines to ~14 lines via
   `simp_rw [elemSkewMap_ofLp_inr_apply ...]` +
   `Finset.sum_ite_eq'`. The math now reads as math at both levels:
   the helper's docstring spells out the
   `i.val < s.1.val < i.val` contradiction once, and the LI proof
   reads "apply the cross-term lemma, then `sum_ite_eq'`
   collapses." See commit-14 *Done* entry.

4. **D-general lift of `exists_affinelySpanning_rigid_placement_two`**
   (promoted from *Deferred follow-up*). *In progress.* The blueprint's
   "the determinant is a polynomial in $t$ whose leading coefficient is
   the Vandermonde determinant" maps clause-for-clause to a clean
   matrix-level proof at d-general, but our dim-2 specialization
   expands it by hand and accumulates the bookkeeping noted in task 1.
   **Matrix reframing.** The eight scalars $A_0, A_1, B_0, B_1, X, Y, U, Z$
   are entries of two $2\times 2$ matrices:
   - $M_0$ rows: $p_0(b) - p_0(a)$ and $p_0(c) - p_0(a)$ (constant offset).
   - $M_1$ rows: $w(b) - w(a)$ and $w(c) - w(a)$ (perturbation direction).

   Then $\det(M_0 + t \cdot M_1) \in \R[t]$ has degree $\le 2$ and its
   leading coefficient is $\det M_1$. At dim-2, $\det M_1$ is the
   Vandermonde-difference determinant on $(\phi a, \phi b, \phi c)$,
   factoring as $(\phi b - \phi a)(\phi c - \phi a)(\phi c - \phi b)$;
   at d-general, it is the full $d \times d$ Vandermonde-difference
   determinant on $(\phi v_0, \ldots, \phi v_d)$, factoring as
   $\prod_{i < j} (\phi v_j - \phi v_i)$ by `Matrix.det_vandermonde`.

   **API needed — status snapshot (commit 16):**
   - ~~**`det(M_0 + t \cdot M_1)` as a polynomial in $t$**~~. *Resolved*:
     mathlib already ships this under
     `Mathlib/LinearAlgebra/Matrix/Polynomial.lean` —
     `natDegree_det_X_add_C_le` gives `natDegree ≤ Fintype.card n`, and
     `coeff_det_X_add_C_zero` / `coeff_det_X_add_C_card` give the `t^0`
     / `t^n` coefficients. The polynomial is
     `(X • A.map C + B.map C).det : R[X]`; eval at `t` recovers
     `(t • A + B).det` via `RingHom.map_det` on `Polynomial.evalRingHom`
     (one-liner at the call site, no mirror needed).
   - ~~**Vandermonde-difference factoring**~~. *Resolved* (this commit):
     `Matrix.det_powerDifferences` under
     `Mathlib/LinearAlgebra/Vandermonde.lean`.
   - **AffineIndependent ↔ nonzero det of difference matrix** at
     d-general: route through `affineIndependent_iff_linearIndependent_vsub`
     + `Matrix.linearIndependent_rows_of_det_ne_zero` +
     `WithLp.linearEquiv` to bridge `EuclideanSpace ↔ Fin d → ℝ`.
     ~15 LoC. *Pending* — likely the next session's first piece.

   **What dissolves at d-general:**
   - The eight scratch scalars (absorbed into `M_0`, `M_1`).
   - The private helper `linearIndependent_pair_of_det_ne_zero`
     (superseded by `Matrix.linearIndependent_rows_of_det_ne_zero` +
     bridge).
   - The private helper `finite_zeros_quadratic` (superseded by
     direct use of `Polynomial.finite_setOf_isRoot` on the degree-$d$
     polynomial built from `coeff_det_X_add_C_card`).
   - The hand-rolled `ring` factoring of $\gamma$ (replaced by
     `Matrix.det_powerDifferences`).
   - The intermediate `have hu0, hu1, hv0, hv1` decompositions
     (absorbed into the matrix-of-differences definition).

**Bar for each task:** try the candidate fixes in order; commit the
fix that lands. If all candidates fail for a given point, file a
FRICTION entry naming the blocker and add the blueprint aside.

**Sequencing.** Task 3 is independent of task 4 and may go in either
order, including before the sparsity lemma. Task 4 (d-general lift,
likely 2–3 sessions) subsumes the residual task-1 cleanup work; do
**not** inline the eight scalars or mirror the dim-2 private helpers
before it lands. Task 4 itself can interleave with or follow the
sparsity lemma; sparsity consumes the *existence* of the affinely-
spanning placement, not its proof internals.

**Future polish (low-priority, not blocking).** Two cleanup
opportunities surfaced during the commit-15 TACTICS § 1 golf pass
on `TrivialMotions.lean`; both are deliberately deferred behind the
sparsity lemma and task 4:

- *Project-wide grind-default sweep.* TACTICS § 1's "default to
  `grind` for closing `simp`/`omega`/`linarith`" rule landed (in
  current form) after most Phases 1–5 work was written. The
  commit-15 pass on `TrivialMotions.lean` netted 37 lines deleted
  with no logic changes; a similar pass on other phase files
  (`Sparsity.lean`, `Henneberg.lean`, `Framework.lean`, …) is
  likely to find comparable wins. Method: `grep -n` for bare
  `omega` / `simp` / `simp; ring` / `linarith` closers, then
  `lean_multi_attempt` with `["grind", "grind only", <current>]`
  at each, and apply when grind succeeds and the current tactic
  is multi-line. Cost: ~1 session for a thorough pass; risk: low
  (every change is verified by `lake build` and `lake lint`).
- *Mathlib gap: `LinearMap.eq_zero_iff_eqOn_spanning`.*
  `trivialMotionFamily_linearIndependent`'s `h_S_zero` block goes
  `LinearMap.ext` → `LinearMap.eqOn_span` → close on generators,
  with an explicit `vectorSpan = ⊤` + `vectorSpan_def` detour.
  A direct lemma "if `S = 0` on a set `s` with
  `Submodule.span R s = ⊤`, then `S = 0`" would collapse the
  ~10-line block to ~3 lines. Likely already exists upstream
  under a different name (`Submodule.eq_top_iff_…` / `LinearMap.ext_on`);
  worth a `lean_loogle` search before mirroring.

**Next session — the sparsity-side lemma
`lem:isSparse-of-rowIndependent-two`.** With the affinely-spanning
placement existence landed (commit 11), the remaining substantial
work is the combinatorial sparsity argument: for `I ⊆ G.edgeSet`
row-independent at `p` (where `p` affinely spans on every size-`≥ 3`
subset, as supplied by commit 11), show the spanning subgraph
`H = fromEdgeSet (Subtype.val '' I)` is `(2, 3)`-sparse. The argument
splits by `|s|`:

- `|s| = 2`: `H.edgesIn ↑s` has at most one edge (simple graph), so
  `1 + 3 ≤ 4 = 2 * 2`.
- `|s| ≥ 3`: the rows of `G.RigidityMap p` indexed by
  `H.edgesIn ↑s` are LI (subset of `I`) and supported on `s`-columns,
  hence factor through `H[s].RigidityMap p|_s` and are LI there too.
  The d-general rank upper bound
  `rigidityMap_finrank_range_le_of_affinelySpanning` at `d = 2`
  applied to `H[s]` at `p|_s` (using the affine-span hypothesis at
  `↑s`) bounds the rank by `2|s| - 3`, hence `|H.edgesIn ↑s| ≤ 2|s| - 3`.

The technical bridge is the "row supported on columns of `s` factors
through `Framework s 2`" argument; this likely needs a custom
restriction linear map and the precomposition factoring trick.
`SimpleGraph.induce` can supply `H[s]`.

After the sparsity lemma, the assembly theorem
`thm:isGenericallyRigid-exists-isLaman-le` combines it with the
basis-pick (commit 6) and affinely-spanning placement (commit 11)
to close the iff. The sparsity-side lemma is the last step with
genuine combinatorial content; the assembly is mechanical glue.

**Phase 6 completion remains uncertain in scope.** The analysis side
is closed (commit 11), the linear-algebra side is closed (commits
6–10); the remaining substantive work is the sparsity lemma plus the
mechanical assembly. Reassess scope once the sparsity lemma's first
attempt lands.

**Design pattern established (commit 10).** When a Phase 6 helper has
a d-general statement that holds verbatim with no extra hypotheses
beyond what the d=2 critical path already provides, ship it
d-general and skip the d=2 corollary. The `rfl` reduction
`2 * (2 + 1) / 2 → 3` on `Nat` literals means callers consume
d-general lemmas at `d = 2` with zero specialisation ceremony. The
dim-2-shaped statements that *do* deserve a dedicated d=2 surface are
those where the dim-2 conclusion is structurally specific (e.g.,
`exists_edgeSetRowIndependent_basis_dim_two`'s `|I| = 2 * #V - 3`).
Apply this rule going forward when adding helpers for the remaining
two leaves.
