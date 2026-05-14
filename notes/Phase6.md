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

**Through commit 11 (this commit):** the analysis leaf
`lem:exists-affinelySpanning-rigid-placement-two` lands in
`RigidityMatroid.lean`. The Vandermonde-perturbation argument
(perturb the IR witness along `w(v) = (φ v, (φ v)²)`; for each
ordered triple the collinearity determinant is a quadratic in `t`
with leading coefficient `(φ b − φ a)(φ c − φ a)(φ c − φ b) ≠ 0`,
so the per-triple bad-`t` set is finite; the finite union over
triples is finite, and any point of the open IR-neighborhood
interval outside it works). Two private helpers ride along:
`finite_zeros_quadratic` (zero set of a real quadratic with nonzero
leading coefficient, via `Polynomial.finite_setOf_isRoot`) and
`linearIndependent_pair_of_det_ne_zero` (the dim-2 LI characterization
in coordinates). Lemma is dim-2-shaped; d-general lift via the
moment curve + `Matrix.det_vandermonde` is deferred follow-up. The
blueprint chapter `chapter/laman-theorem.tex` flips the leaf to
`\leanok` with a prose proof.

**Through commit 10:** the linear-algebra side is closed
**d-general**. `CombinatorialRigidity/TrivialMotions.lean` ships the
full d-general API: translations, infinitesimal rotations, the
`trivialMotions` submodule, the unconditional `trivialMotions_le_ker`,
the finrank lower bound `trivialMotions_finrank_ge_of_affinelySpanning`
(`d * (d + 1) / 2 ≤ finrank ℝ (trivialMotions p)` under affine
spanning), and the kernel bound `rigidityMap_ker_finrank_ge_of_affinelySpanning`.
`CombinatorialRigidity/RigidityMatroid.lean` ships
`EdgeSetRowIndependent`, the row-rank-column-rank identification, the
d-general rank lower bound
`rigidityMap_finrank_range_ge_of_isGenericallyRigid`, the d-general
rank upper bound `rigidityMap_finrank_range_le_of_affinelySpanning`,
and the basis-pick `exists_edgeSetRowIndependent_basis_dim_two`
(latter is dim-2-specific because the conclusion `|I| = 2 * #V - 3`
is dim-2-shaped; the rank lemma it consumes is d-general). Commit 10
also retired the d=2 corollary chain
(`trivialMotions_three_le_finrank/ker_of_affinelySpanning_two`,
`rigidityMap_finrank_range_ge/le_..._two`, `rotJTwo` + apply lemmas):
`2 * (2 + 1) / 2` reduces to `3` by `rfl` on `Nat` literals, so
d=2 callers consume the d-general lemmas with zero specialisation
ceremony. The blueprint chapters mirror this state.
Citations chain (Laman 1970 → Asimow–Roth 1978 → Jordán 2016) was
researched and added in commit 2; we stay matroid-agnostic per the
commit-5 investigation.

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

Status snapshot at commit-11 (affinely-spanning placement lands):
the remaining red nodes in `chapter/laman-theorem.tex` are
`lem:isSparse-of-rowIndependent-two` and the assembly target
`thm:isGenericallyRigid-exists-isLaman-le`. The sparsity lemma stacks
on the d-general rank upper bound at `d = 2` plus the new
affinely-spanning placement existence; the assembly theorem stacks on
the sparsity lemma plus the basis-pick (commit 6).

## Decisions made during this phase

### Phase-local choices and proof techniques

- **d-general only; no d=2 corollary surface.** Commit 10 retired the
  d=2 corollaries of the rank bounds and the kernel bound after the
  user's design pivot. `2 * (2 + 1) / 2` reduces to `3` by `rfl` on
  `Nat` literals (verified via `lean_multi_attempt`: `example (n : ℕ)
  (h : 2 * n ≤ 5 + 2 * (2 + 1) / 2) : 2 * n ≤ 5 + 3 := h` typechecks),
  so d=2 callers consume the d-general lemmas with no ceremony.
  Concretely deleted: `trivialMotions_three_le_finrank_of_affinelySpanning_two`,
  `trivialMotions_three_le_ker_of_affinelySpanning_two`,
  `rigidityMap_finrank_range_ge_of_isGenericallyRigid_two`,
  `rigidityMap_finrank_range_le_of_affinelySpanning_two`, and the
  orphaned `rotJTwo` + `rotJTwo_apply_zero/one` + `inner_rotJTwo_self`
  (the dim-2 explicit generator was infrastructure for commit 7's
  direct-coord proof, which commit 8 retired). The basis-pick
  `exists_edgeSetRowIndependent_basis_dim_two` stays dim-2-shaped
  because its *conclusion* `|I| = 2 * #V - 3` is dim-2-specific; only
  its body switched to the d-general rank lemma. Asymmetry rationale:
  the rank/kernel bounds are general infrastructure where the constant
  `d (d + 1) / 2` is parametric; the basis-pick and the downstream
  sparsity / assembly lemmas live on the Phase 6 dim-2 critical path
  where `2 * #V - 3` is the structural shape, not a `d`-parametrised
  expression.

- **Dual-bridge for the basis-pick.** `EdgeSetRowIndependent` is stated
  as `LinearIndepOn` of a family of plain functions `Framework V d →
  ℝ` (matching the blueprint), but the rank identities we need
  (`LinearMap.finrank_range_dualMap_eq_finrank_range`,
  `Pi.basisFun.dualBasis`) require viewing the rows as linear
  functionals (`Module.Dual ℝ (Framework V d)`). The basis-pick proof
  works in the dual module throughout (via `rigidityRow` and
  `span_range_rigidityRow`), then transports the resulting LI back to
  the function-module form via `edgeSetRowIndependent_iff_linearIndepOn_rigidityRow`.
  The bridge needed a private `dualToFunₗ : Module.Dual ℝ M →ₗ[ℝ] (M
  → ℝ)` since mathlib doesn't ship the `ℝ`-linear envelope of
  `FunLike.coe` directly (see FRICTION *No packaged ℝ-linear
  injection*).

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
  its own `CombinatorialRigidity/TrivialMotions.lean` (parallel to
  `Framework.lean`) rather than buried inside `RigidityMatroid.lean`.
  Three reasons. (a) The motions are *general* infrastructure on
  frameworks, not specifically a matroid concept. (b) The definitions
  (`translationMotion`, `infinitesimalRotation`, `trivialMotions`) are
  d-general; only the finrank lower bound (`rotJTwo` + the LI of three
  motions) is dim-2-specific, and it's natural to keep the d-general
  surface separate from the dim-2 specialisation. (c) The submodule
  formulation lets `trivialMotions_le_ker` ship as one unconditional
  lemma and `3 ≤ finrank ker` as a clean one-liner from
  `Submodule.finrank_mono`, rather than inlining three motion-checks
  in the kernel lemma. The blueprint chapter
  `chapter/trivial-motions.tex` mirrors the Lean file's structure
  one-to-one. The finrank lower bound is shipped dim-2-specific in
  commit 7; *Blockers* records the d-general generalisation as
  deferred follow-up work (the dim-2 lemma is the `d = 2` instance).

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
  d-general LI argument
  (`trivialMotionFamily_linearIndependent`, commit 8) uses an
  intermediate `set S := ∑ s, c_R s • elemSkewMap s.1 (cast s.2)` as
  a linear endomorphism of `EuclideanSpace ℝ (Fin d)`. The vanishing
  combination at vertex `v` then reads `t + S(p v) = 0`; subtracting
  at two vertices kills `t` and shows `S(p v - p w) = 0`. Affine
  spanning + `vectorSpan_def` + `LinearMap.eqOn_span` extends this to
  `S = 0` everywhere. Rotation coefficient extraction is via
  `(S (PiLp.single 2 j' 1)).ofLp i = c_R ⟨i, j⟩`, where the
  ordered-pair index range (`j.val < i.val`) forces the off-diagonal
  cross-terms to vanish. The alternative pure-coordinate route
  (no named linear map, just `congrFun hc v ; congrFun ... m` and
  matrix-style bookkeeping) was rejected as too fiddly: the
  abstraction `S` is doing real work because the affine-spanning step
  is naturally stated about a linear map vanishing on a spanning set.
  The dim-2 lemma (commit 7's `_three_le_finrank_of_affinelySpanning_two`)
  was redone as a one-line `:= trivialMotions_finrank_ge_of_affinelySpanning hp`
  corollary; its ~100 LoC of direct-coord argument is now subsumed.

### Promoted to TACTICS / FRICTION / DESIGN

*(none yet — the trivial-motions specifics stay phase-local; the FRICTION
entries opened in commit 7 are the cross-cutting record.)*

### Cleanup pass summaries

*(none yet)*

## Blockers / open questions

- ~~**`TrivialMotions` Phase 4 deferred API.**~~ Resolved in commit 7
  via path (2): the `TrivialMotions` API landed d-general in its own
  file `CombinatorialRigidity/TrivialMotions.lean` with a dim-2
  specialisation. *(Commit 10 retired the dim-2 specialisation in
  favour of d-general callers; `rigidityMap_ker_finrank_ge_of_affinelySpanning`
  is now the canonical kernel bound.)* See the *Done* list under
  *Hand-off* and the blueprint chapter `chapter/trivial-motions.tex`.

- ~~**D-general finrank lower bound (deferred).**~~ Resolved in
  commit 8. `trivialMotions_finrank_ge_of_affinelySpanning` ships
  `d * (d + 1) / 2 ≤ finrank ℝ (trivialMotions p)` for an
  arbitrary affinely-spanning placement in any dimension. Built on
  `elemSkewMap (i j : Fin d)` and `trivialMotionFamily` indexed by
  `Fin d ⊕ Σ i : Fin d, Fin i.val`; the LI proof routes through a
  skew sum `S : Eucl d →ₗ[ℝ] Eucl d`, kills it on differences
  `p v - p w`, extends to `S = 0` via `LinearMap.eqOn_span` against
  `vectorSpan ℝ (Set.range p) = ⊤`, then extracts each rotation
  coefficient as `(S e_{j'}).ofLp i`. Cardinality reshuffled to
  `∑_{i ∈ range (d + 1)} i = d (d + 1) / 2`. The dim-2 lemma
  `trivialMotions_three_le_finrank_of_affinelySpanning_two` is now a
  one-line corollary at `d = 2`.

- ~~**Generic-placement affine-spanning lemma.**~~ Resolved in
  commit 11. `exists_affinelySpanning_rigid_placement_two` ships the
  combined witness (IR + affinely-spanning restriction on every
  $|S| \ge 3$ subset) via Vandermonde perturbation of an IR witness.
  See *Done* commit 11 entry.

- ~~**Linear-algebra basis-pick.**~~ Resolved in commit 6 via the
  matroid-agnostic path: `exists_linearIndepOn_extension` plus
  `LinearMap.finrank_range_dualMap_eq_finrank_range` plus the
  standard-basis-of-dual identification via `Pi.basisFun.dualBasis`.
  See `exists_edgeSetRowIndependent_basis_dim_two` in
  `RigidityMatroid.lean` and the *Done* list under *Hand-off*.

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
  `exists_edgeSetRowIndependent_basis_dim_two` plus
  `rigidityRow` / `span_range_rigidityRow` /
  `edgeSetRowIndependent_iff_linearIndepOn_rigidityRow` and the
  private `dualToFunₗ` bridge (FRICTION entry filed).
- *Commit 7 (`49c693a`):* `TrivialMotions.lean` — d-general
  `translationMotion`, `infinitesimalRotation`, `trivialMotions`,
  `trivialMotions_le_ker`; dim-2 `rotJTwo` (direct `LinearMap.mk'`,
  not `Matrix.toEuclideanLin`), `inner_rotJTwo_self`,
  `trivialMotions_three_le_finrank_of_affinelySpanning_two`, and
  `trivialMotions_three_le_ker_of_affinelySpanning_two`. New
  blueprint chapter `chapter/trivial-motions.tex` mirrors the
  file 1:1. Three FRICTION entries.
- *Commit 8 (`6b104da`):* d-general finrank lower bound. Added
  `elemSkewMap (i j : Fin d) : Eucl d →ₗ[ℝ] Eucl d` and
  `inner_elemSkewMap_self`. Built the d-general `trivialMotionFamily`
  indexed by `Fin d ⊕ Σ i : Fin d, Fin i.val`, proved
  `_mem_trivialMotions` and joint LI
  `trivialMotionFamily_linearIndependent` (skew-sum + affine-spanning
  route; see *Decisions*). Cardinality
  `fintype_card_trivialMotionFamilyIndex = d(d+1)/2` via
  `Finset.sum_range_succ` + `Finset.sum_range_id`. Main lemma
  `trivialMotions_finrank_ge_of_affinelySpanning` lifts via
  `LinearIndependent.fintype_card_le_finrank`. Dim-2 lemma
  `trivialMotions_three_le_finrank_of_affinelySpanning_two` reduced
  to a one-line corollary (~100 LoC of direct-coord argument
  retired). Six new green blueprint nodes in
  `chapter/trivial-motions.tex`. No new FRICTION entries.
- *Commit 9 (`f87c09f`):* rank upper bound (d=2 form). Added
  `rigidityMap_finrank_range_le_of_affinelySpanning_two` in
  `RigidityMatroid.lean` — `finrank range + 3 ≤ 2 * #V` at any
  affinely-spanning placement, via the same rank-nullity +
  `Framework.finrank` template as the commit-3 lower bound, fed by
  commit 7's `trivialMotions_three_le_ker_of_affinelySpanning_two` on
  the kernel side. ~5 lines of `omega` over three `have`s; no new
  ideas. The blueprint entry
  `lem:rigidityMap-finrank-range-le-of-affinelySpanning-two` flipped
  green; the `|V| ≥ 2` hypothesis on the blueprint statement was
  dropped (the affine-span hypothesis already forces `|V| ≥ 3`). No
  new FRICTION entries. *(d=2 form retired in commit 10; the d-general
  `rigidityMap_finrank_range_le_of_affinelySpanning` replaces it.)*
- *Commit 11 (this commit):* affinely-spanning rigid placement
  (`lem:exists-affinelySpanning-rigid-placement-two`). Added to
  `RigidityMatroid.lean` (~150 LoC) alongside two private helpers
  `finite_zeros_quadratic` (real-quadratic zero set is finite, via
  `Polynomial.finite_setOf_isRoot`) and
  `linearIndependent_pair_of_det_ne_zero` (dim-2 LI from nonzero
  determinant; mathlib has no direct version). Vandermonde
  perturbation in dim 2: leading $t^{2}$ coefficient factors as
  $(\phi b - \phi a)(\phi c - \phi a)(\phi c - \phi b)$ and is nonzero
  by injectivity. Imports added: `Mathlib.Algebra.Polynomial.Roots`
  and `Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional`. Blueprint
  chapter `chapter/laman-theorem.tex` flips the leaf to `\leanok`
  with a prose proof. *(d-general lift via the moment curve is
  follow-up — see `notes/Phase6.md` *Hand-off*.)* User design
  choice: ship dim-2 first, plan to lift later (per the
  commit-10 design pattern, when d-general is materially harder
  than dim-2 the dim-2 surface is the right interim).

- *Commit 10:* d-general lift; d=2 corollary surface
  retired. Added `rigidityMap_ker_finrank_ge_of_affinelySpanning` in
  `TrivialMotions.lean` (~3 lines via `.trans` + `Submodule.finrank_mono`).
  Generalised commit 3's `rigidityMap_finrank_range_ge_of_isGenericallyRigid_two`
  and commit 9's `rigidityMap_finrank_range_le_of_affinelySpanning_two`
  to their d-general statements (`d * #V ≤ finrank range + d (d + 1) / 2`
  / `finrank range + d (d + 1) / 2 ≤ d * #V`); the d=2 corollaries
  are deleted. `exists_edgeSetRowIndependent_basis_dim_two`'s call
  switches to the d-general lower bound with zero ceremony (the
  `+ 2 * (2 + 1) / 2` term is definitionally `+ 3`).
  `trivialMotions_three_le_finrank/ker_of_affinelySpanning_two` and
  `rotJTwo` + apply lemmas + `inner_rotJTwo_self` all deleted (no
  callers). `EuclideanDist` import dropped from `TrivialMotions.lean`
  (it was rotJTwo-only). Blueprint chapters `chapter/trivial-motions.tex`
  and `chapter/laman-theorem.tex` updated to mirror the new state.
  No new FRICTION entries.

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
   resolved.** The dominant friction (~14 lines of hand-rolled
   `{x : Fin 3 // x ≠ 0} ↪ Fin 2` reindex + `convert ... using 1` +
   `funext` + `fin_cases`) collapsed to 5 lines using mathlib's
   `finSuccAboveEquiv (0 : Fin 3) : Fin 2 ≃ { x : Fin 3 // x ≠ 0 }`
   composed with `linearIndependent_equiv`. The FRICTION entry
   *AffineIndependent ↔ LinearIndependent reindex* is now [resolved];
   key lesson: mathlib's `Fin`-indexed-family API is denser than it
   looks, sweep `lean_loogle` / `lean_leanfinder` before mirroring.
   *Two remaining candidate fixes assessed; both deliberately deferred
   in favor of task 4 below (the d-general lift subsumes them):*
   - Mirror `linearIndependent_pair_of_det_ne_zero` (17 lines, private)
     under `CombinatorialRigidity/Mathlib/LinearAlgebra/` as a
     `Fin 2 → R` version. Cost/benefit at d=2: relocates the helper
     without reducing the calling proof's line count (the
     `EuclideanSpace ↔ Fin 2 → ℝ` bridge it'd require at the call site
     negates the code-motion savings). *At d-general*: the helper
     dissolves entirely — superseded by mathlib's
     `Matrix.linearIndependent_rows_of_det_ne_zero`. Defer until task 4.
   - Eliminate the eight `set` scalars $A_0, A_1, B_0, B_1, X, Y, U, Z$
     by inlining + `ring`. *Revised assessment* (after the d-general
     question): the eight scalars are the entries of two $2\times 2$
     matrices $M_0$ (constant offset) and $M_1$ (perturbation
     direction); their existence is symptomatic of *premature dim-2
     specialization*, not math-faithfulness. At d-general they
     dissolve into `Matrix.det (M_0 + t \cdot M_1)`. Inlining at d=2
     would save ~12 LoC but would be discarded by task 4. **Hold off**
     — don't clean d=2 proofs that the d-general lift will rewrite.

2. **`exists_edgeSetRowIndependent_basis_dim_two` — "small dual
   bridge" isn't small.** ~60 lines of infrastructure
   (`dualToFunₗ` + 2 helpers, `rigidityRow` + apply, the bridge
   `edgeSetRowIndependent_iff_linearIndepOn_rigidityRow`,
   `span_range_rigidityRow`). Candidate fixes:
   - Re-check whether mathlib now ships an $\R$-linear envelope of
     `FunLike.coe` for `(M →ₗ[ℝ] ℝ) → (M → ℝ)` (the commit-6 FRICTION
     entry *No packaged ℝ-linear injection* flagged the absence;
     mathlib has had a year of churn since). If yes, delete
     `dualToFunₗ` + apply + injectivity.
   - Search for row-rank-equals-column-rank phrased *without*
     `LinearMap.dualMap` (e.g. via `Matrix.rank` /
     `Matrix.toLinearMap'`, or `Matrix.rank_transpose`). A
     matrix-level route may avoid the dual bridge entirely.
   - If the dual bridge stays, promote `rigidityRow` /
     `span_range_rigidityRow` to a named blueprint concept (its own
     `\begin{definition}` + `\begin{lemma}`) rather than gesturing at
     it as "a small bridge lemma" — the abstraction is real and
     reusable, and earning its own dep-graph node is more honest than
     a one-clause aside.

3. **`trivialMotionFamily_linearIndependent` — "cross-terms vanish"
   hides a 30-line case-split.** Lean (`TrivialMotions.lean:316-348`)
   uses `Finset.sum_eq_single` whose off-term branch is a 30-line
   `split_ifs` + `omega` over `Fin.val` comparisons, handling each
   of `elemSkewMap`'s two `if-then-else` summands separately.
   *Independent of task 4* — this proof is already d-general; the
   d-general lift of the affinely-spanning placement doesn't touch
   `TrivialMotions.lean`. Candidate fixes:
   - Re-express `elemSkewMap i j x` so its application is a single
     `Pi.single`-style expression rather than nested `if`s — e.g.
     `x j • PiLp.single 2 i 1 - x i • PiLp.single 2 j 1`. Then
     `simp [Finset.sum_ite_eq', Pi.single_apply]` should collapse the
     off-diagonal case to one or two lines.
   - Hoist "off-diagonal ordered-pair products of `elemSkewMap`
     vanish" into a named lemma on `elemSkewMap` itself (separate
     from the LI proof), so the LI proof reads at the level of math.
   - If neither, expand the blueprint's terse "the other cross-terms
     vanish for the ordered-pair index range" to one sentence naming
     the `(i, j) ≠ (a, b)` case-split.

4. **D-general lift of `exists_affinelySpanning_rigid_placement_two`**
   (promoted from *Deferred follow-up*). The blueprint's "the
   determinant is a polynomial in $t$ whose leading coefficient is the
   Vandermonde determinant" maps clause-for-clause to a clean
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

   **API needed (~70 LoC, all upstream-eligible):**
   - **`det(M_0 + t \cdot M_1)` as a polynomial in $t$**: package the
     1-parameter family `t \mapsto \det(M_0 + t \cdot M_1)` as
     `Polynomial.eval t p` for some `p : R[X]` of degree $\le d$.
     Mathlib has `Matrix.charpoly` and `Polynomial.det` infrastructure;
     check what's directly usable. ~30 LoC.
   - **Leading-coefficient lemma**: $t^d$ coefficient of
     $\det(M_0 + t \cdot M_1)$ is $\det M_1$. Follows from
     column-linearity of $\det$. ~10 LoC.
   - **AffineIndependent ↔ nonzero det of difference matrix** at
     d-general: route through `affineIndependent_iff_linearIndependent_vsub`
     + `Matrix.linearIndependent_rows_iff_isUnit` +
     `IsUnit ↔ det ≠ 0` (over a field) + `WithLp.linearEquiv` to
     bridge `EuclideanSpace ↔ Fin d → ℝ`. ~15 LoC.
   - **Vandermonde-difference factoring**: glue from
     `Matrix.det_vandermonde` to the "row-0-subtracted" form we
     actually need. ~10 LoC.

   **What dissolves at d-general:**
   - The eight scratch scalars (absorbed into `M_0`, `M_1`).
   - The private helper `linearIndependent_pair_of_det_ne_zero`
     (superseded by `Matrix.linearIndependent_rows_of_det_ne_zero` +
     bridge).
   - The private helper `finite_zeros_quadratic` (superseded by
     direct use of `Polynomial.finite_setOf_isRoot` on the degree-$d$
     polynomial).
   - The hand-rolled `ring` factoring of $\gamma$ (replaced by
     `Matrix.det_vandermonde`).
   - The intermediate `have hu0, hu1, hv0, hv1` decompositions
     (absorbed into the matrix-of-differences definition).

   **Cost estimate**: ~70 LoC of upstream-eligible API, ~80 LoC of
   d-general proof body, replacing the current ~150 LoC dim-2 proof
   plus its two private helpers. Net: comparable LoC, but the proof
   reads exactly like the blueprint prose, and the API is generally
   useful (a Vandermonde-difference factorization + a
   `det(A + t \cdot B)` polynomial framework are both reusable).

**Bar for each task:** try the candidate fixes in order; commit the
fix that lands. If all candidates fail for a given point, file a
FRICTION entry naming the blocker and add the blueprint aside.

**Sequencing.** Tasks 2 and 3 are independent of task 4 and may be
tackled in any order, including before the sparsity lemma. Task 4
(the d-general lift) is heavier (likely 2–3 sessions) and subsumes
the remaining task-1 cleanup work; do **not** inline the eight
scalars or mirror the private helpers at dim-2 before task 4 lands,
since they'd be discarded immediately. Task 4 itself can interleave
with or follow the sparsity-side lemma; sparsity consumes the
*existence* of the affinely-spanning rigid placement, not its proof
internals.

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

**D-general lift of affinely-spanning placement.** Tracked as task 4
of the *Pending Lean-simplification pass* above (promoted from this
former *deferred follow-up* slot). See that task for the matrix
reframing, API sketch, and "what dissolves at d-general" list.

**Phase 6 completion remains uncertain in scope** as of commit 11.
The analysis side is closed (affinely-spanning rigid placement);
the linear-algebra side is closed (basis-pick + rank bounds);
remaining substantial work is the sparsity lemma plus assembly.
Plan to assess scope after the sparsity lemma's first attempt lands.

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
