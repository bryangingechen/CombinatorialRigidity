# Phase 4 — Frameworks and infinitesimal rigidity (work log)

**Status:** complete.

This file is the per-phase work record. See `../ROADMAP.md` for the
high-level plan and `../DESIGN.md` for cross-cutting design choices.

## Current state

Phase 4 closed. `Framework.lean` ships:

* The four core definitions (`Framework V d` as `abbrev`, `RigidityMap G p`
  with full linearity proof, `IsInfinitesimallyRigid`, `IsGenericallyRigid`).
* Basic `RigidityMap` API: `Framework.finrank`, `rigidityMap_apply`,
  `rigidityMap_ker_mono`, `rigidityMap_finrank_range_le`.
* Graph-monotonicity corollaries: `IsInfinitesimallyRigid.mono`,
  `IsGenericallyRigid.mono`.
* The main edge-count theorem `IsGenericallyRigid.card_mul_le`:
  `d * #V ≤ #E + d(d+1)/2` for any generically rigid graph.
* The K₂ worked example `top_fin_two_isGenericallyRigid` for any `d`.

**Strategic re-plan (this session).** Closer reading showed that
`IsGenericallyRigid.card_mul_le` only needs the kernel-dim bound from
`IsInfinitesimallyRigid` plus rank-nullity — **not** the trivial-motions
API. Phase 4 closes on `card_mul_le` + K₂; `TrivialMotions` and
`finrank_trivialMotions_le` are **deferred** as a polish pass that can
be revisited if Phase 5 surfaces a need.

## Architectural choices made up front

These extend `../DESIGN.md` *Choices to revisit*; if either turns out
wrong, revisit there.

- **General `d` first; specialize at the Laman boundary, not before.**
  Every Phase 4 definition and lemma is stated for arbitrary
  dimension `d : ℕ`. The `2 * #V - 3` Laman edge bound is the
  `d = 2` specialization of a general-`d` `d * #V ≤ #E + d(d+1)/2`
  statement that holds for *any* generically rigid graph in
  dimension `d` — same proof, no precondition. The `K₂` worked
  example holds in any `d ≥ 0` for the same reason. So the only
  point at which `d = 2` legitimately enters is the Phase 5 boundary,
  where the count matroid is `(2, 3)` and the connection to Laman
  graphs is made. Specializing earlier hides the underlying linear
  algebra and makes future work in higher dimensions a refactor
  rather than a copy-paste.

- **Future generalization axes (noted, not built).** The plan deliberately
  leaves room for these without paying for them now:

  * **Arbitrary inner product space** in place of `EuclideanSpace ℝ
    (Fin d)`. All proofs go through `Module.finrank ℝ E` rather than
    `d`; the constant `d * (d + 1) / 2` becomes
    `finrank ℝ E * (finrank ℝ E + 1) / 2`. Cheap to refactor later
    *if* we keep `d` threaded through and avoid `decide`-style
    proofs that rely on `Fin d`'s computability. **Keep this in mind
    when writing proofs**: prefer `finrank` arguments over coordinate
    arguments wherever possible.
  * **Other rigidity notions** — local (continuous) rigidity, global
    rigidity, generic global rigidity, redundant rigidity, body-bar
    and body-hinge frameworks. None are touched in Phase 4. Each
    would slot in as a separate `Prop` in its own file
    (`LocalRigidity.lean`, `GlobalRigidity.lean`, …) once the
    underlying motion-space machinery is in scope; the definitions
    we land here (`Framework`, `RigidityMap`, `TrivialMotions`)
    are independent of which `Prop` consumes them. Do *not* try to
    factor `IsInfinitesimallyRigid` through a hypothetical abstract
    "rigidity property" typeclass — premature, and the right
    abstraction will be clearer once at least one alternative
    notion is on disk.
  * **Abstract rigidity matroid** (Whiteley) lives at the
    matroid layer, not here; it's the natural consumer of
    `Mathlib.Combinatorics.Matroid` and would land in a future
    `RigidityMatroid.lean` if Phase 5's hard direction wants it.
    Keep `RigidityMap` and `TrivialMotions` matroid-agnostic so
    such a file can sit on top without refactoring back into
    `Framework.lean`.

- **`Framework V d := V → EuclideanSpace ℝ (Fin d)`, as `abbrev`.** The
  ROADMAP `def`-vs-`abbrev` rule applies to *predicates* (`IsSparse`,
  `IsTight`, `IsLaman`); type aliases are different. With `def`, the
  Pi-`AddCommGroup` / `Module ℝ` instances on `V → EuclideanSpace ℝ
  (Fin d)` do *not* propagate to `Framework V d` (Lean does not unfold
  `def` for instance synthesis), forcing per-instance `instance ... :=
  inferInstanceAs ...` boilerplate. `abbrev` makes the synthesis
  transparent and is what mathlib uses for `EuclideanSpace` itself
  (`abbrev EuclideanSpace 𝕜 n := PiLp 2 fun _ => 𝕜`). The cost
  ("`Framework V d` may unfold in goals") is a feature here:
  linearity proofs of `RigidityMap` rely on `(p₁ + p₂) u = p₁ u + p₂ u`
  via `Pi.add_apply`. The `finrank` is `Fintype.card V * d`
  (one chain through `Module.finrank_pi_fintype` and
  `finrank_euclideanSpace`); landed as `Framework.finrank` in the next
  commit.

- **Rigidity map defined directly via the explicit entry formula —
  *not* as `fderiv` of edge-length-squared.** For an edge `e = s(u,
  v)` and an infinitesimal motion `p' : Framework V d`, the scalar
  output is `⟪p u - p v, p' u - p' v⟫_ℝ`. Symmetric in `u, v` (both
  factors flip sign under swap), so it descends through `Sym2.lift`
  to a function `G.edgeSet → ℝ`. Linear in `p'` for fixed `p`. So:

  ```
  def RigidityMap (G : SimpleGraph V) (p : Framework V d) :
      Framework V d →ₗ[ℝ] (G.edgeSet → ℝ) := …
  ```

  This is a non-`abbrev` `def` for the same reason as `IsSparse` etc.

  The alternative — define
  `lengthSq G p : G.edgeSet → ℝ := fun e => ‖p u - p v‖^2` (lifted
  through `Sym2.lift`), then set `RigidityMap p := fderiv ℝ
  (lengthSq G ·) p` (modulo a factor of 2), then prove the explicit
  entry formula as a theorem — was rejected: it pulls in
  `Mathlib.Analysis.Calculus.FDeriv` plus differentiability
  obligations, none of which the rank/kernel arguments downstream
  need. The "this really is the differential of edge-length-squared"
  framing stays in `Framework.lean`'s module docstring as
  motivation. If a later phase wants the `fderiv` form as a
  *theorem*, add `rigidityMap_eq_fderiv_lengthSq` as a follow-up;
  Phase 5's Laman direction does not need it.

- **Trivial motions defined globally as the image of the rigid-motion
  action.** Concretely, the action map

  ```
  trivialMotionAction p : EuclideanSpace ℝ (Fin d) ×
      ↥(skewAdjointMatricesSubmodule (1 : Matrix (Fin d) (Fin d) ℝ))
      →ₗ[ℝ] Framework V d
  ```

  sends `(t, A) ↦ (v ↦ t + A.val.mulVec (p v))`. `TrivialMotions G p :=
  LinearMap.range (trivialMotionAction p)`.

  The `skewAdjointMatricesSubmodule` here uses `J = 1` (the identity
  bilinear form), giving the standard "matrix is skew-symmetric"
  condition `Aᵀ = -A`. Mathlib's `mem_skewAdjointMatricesSubmodule`
  unfolds it to `IsSkewAdjoint`.

  Trivial motions live in the kernel of `RigidityMap`: translations
  cancel out (`p u - p v` doesn't see translation), and infinitesimal
  rotations preserve squared distances by the skew-symmetry of `A`
  (`⟪Ax, x⟫ = 0`).

- **`IsInfinitesimallyRigid` via the kernel-dimension bound.**

  ```
  def IsInfinitesimallyRigid {V : Type*} [Fintype V] {d : ℕ}
      (G : SimpleGraph V) (p : Framework V d) : Prop :=
    Module.finrank ℝ (LinearMap.ker (RigidityMap G p)) ≤ d * (d + 1) / 2
  ```

  `d` is implicit (recovered from `p`'s type); `IsGenericallyRigid`
  takes it explicit since the placement is what's being existentially
  quantified.

  The combination "kernel dim ≤ `d(d+1)/2`" plus the always-true lower
  bound "trivial motions ⊆ kernel" yields the standard textbook
  definition (kernel = trivial motions) when the trivial motions
  themselves have dim `d(d+1)/2`. This avoids the affine-spanning
  side-condition in the *definition*; it surfaces only when we want
  to identify the kernel with trivial motions concretely (see
  *Affinely spanning side-condition* below).

- **`IsGenericallyRigid` via existence of a max-rank placement.**

  ```
  def IsGenericallyRigid (G : SimpleGraph V) (d : ℕ) : Prop :=
    ∃ p : Framework V d, G.IsInfinitesimallyRigid p d
  ```

  Equivalence to "rank max on a Zariski-open set" is downstream and
  not needed for Phase 5 if (⇒) goes via the rank bound directly.

- **Affinely spanning side-condition.** Several lemmas (in
  particular `finrank_trivialMotions_eq` and the `dim ker ≥ d(d+1)/2`
  lower bound) need the placement to be affinely spanning, i.e.
  `affineSpan ℝ (Set.range p) = ⊤`. This is a *generic* condition
  but requires `#V ≥ d + 1` to have any solution. For `d = 2` and
  `#V = 2` (the `K₂` base case), affine spanning fails but the
  trivial-motions image *still* has dim 3 because skew `2 × 2`
  matrices have no non-zero kernel — record this as a special-case
  branch when we hit it. The clean formulation: state
  `finrank_trivialMotions_le` (always `≤ d(d+1)/2`) and the equality
  *under* an affine-spanning hypothesis; derive the d=2 base case
  separately.

- **Module structure on `G.edgeSet → ℝ`.** `↥G.edgeSet → ℝ` is
  automatically a `Module ℝ` (Pi instance). Module dimension
  (when `[Fintype G.edgeSet]`) is `G.edgeSet.toFinset.card`, equal to
  `G.edgeFinset.card`. Use whichever form is in scope.

## Lemma checklist

Tracking against the ROADMAP §4 bullets, plus what we're adding.

### Definitions (`Framework.lean`, this phase)

- [x] `Framework V d` — placement type alias (as `abbrev`)
- [x] `RigidityMap G p` — differential of edge-length-squared (no `sorry`)
- [x] `IsInfinitesimallyRigid G p`
- [x] `IsGenericallyRigid G d`
- [ ] `RigidityMatrix G p` — matrix view via `LinearMap.toMatrix`
- [ ] `trivialMotionAction p` — `(translation, skew) → motion`
- [ ] `TrivialMotions G p` — `LinearMap.range (trivialMotionAction p)`

### `RigidityMap` API

- [x] `Framework.finrank` — `Module.finrank ℝ (Framework V d) =
  Fintype.card V * d` (under `[Fintype V]`). One `simp
  [Module.finrank_pi_fintype]`.
- [x] `rigidityMap_apply` — `(RigidityMap G p) p' ⟨s(u, v), _⟩ =
  ⟪p u - p v, p' u - p' v⟫_ℝ`. `rfl` after `Sym2.lift_mk` reduction.
- [x] `rigidityMap_ker_mono` — `G ≤ G' → LinearMap.ker (RigidityMap G' p) ≤
  LinearMap.ker (RigidityMap G p)`. Renamed from the planning name
  `rigidityMap_mono` to make the *direction* explicit (kernel shrinks
  as graph grows). The "exists restrict" framing was redundant for
  every downstream use, so dropped.
- [x] `rigidityMap_finrank_range_le` — `Module.finrank ℝ
  (LinearMap.range (RigidityMap G p)) ≤ G.edgeSet.ncard` under
  `[Finite V]`. Renamed from `rigidityMap_ncard_le` to be mathlib-styled
  (LHS-named). Three-step calc through `Submodule.finrank_le` +
  `Module.finrank_pi` + `Set.ncard_eq_toFinset_card'`.

### `TrivialMotions` API

- [ ] `trivialMotions_le_ker` — `TrivialMotions G p ≤
  LinearMap.ker (RigidityMap G p)`. The proof unfolds the action to
  `t + A.mulVec (p v)`; in `RigidityMap`, the difference cancels the
  `t`, and `⟪p u - p v, A.mulVec (p u) - A.mulVec (p v)⟫ = ⟪x, A x⟫ =
  0` for `x = p u - p v` by the skew-symmetry of `A`.
- [ ] `finrank_trivialMotions_le` — `Module.finrank ℝ (TrivialMotions
  G p) ≤ d * (d + 1) / 2`. Always-true upper bound from the action's
  domain dimension `d + d(d-1)/2 = d(d+1)/2` (the `d` is translations,
  `d(d-1)/2` is skew-symmetric `d × d`). Mirror lemma needed: dim of
  `skewAdjointMatricesSubmodule (1 : Matrix (Fin d) (Fin d) ℝ)` is
  `d(d-1)/2`. **Likely upstream-eligible**; mirror under
  `Mathlib/LinearAlgebra/Matrix/SesquilinearForm.lean`.
- [ ] `finrank_trivialMotions_eq_of_affinelySpanning` — equality form
  under `affineSpan ℝ (Set.range p) = ⊤`. The action is injective in
  this case: if `t + A • (p v) = 0` for all `v`, then `A` annihilates
  pairwise differences, hence the affine span direction subspace,
  which is all of `ℝᵈ`; so `A = 0` and then `t = 0`.

### `IsInfinitesimallyRigid` API

- [ ] `isInfinitesimallyRigid_iff_finrank_ker_le` — definitional
  unfolding (named for discoverability, like `isLaman_iff`).
- [ ] `isInfinitesimallyRigid_of_finrank_range` — equivalent
  formulation via rank-nullity: `Module.finrank ℝ (LinearMap.range
  (RigidityMap G p)) ≥ d * #V - d(d+1)/2 → IsInfinitesimallyRigid`.
  Useful for the `#E ≥ 2n - 3` Laman direction.

### `IsGenericallyRigid` API

- [x] `IsInfinitesimallyRigid.mono` — `G ≤ G' → G.IsInfinitesimallyRigid p →
  G'.IsInfinitesimallyRigid p` at the same placement. One-liner from
  `rigidityMap_ker_mono` + `Submodule.finrank_mono`.
- [x] `IsGenericallyRigid.mono` — `G ≤ G' → G.IsGenericallyRigid d →
  G'.IsGenericallyRigid d`. One-liner from `IsInfinitesimallyRigid.mono`.
- [x] `IsGenericallyRigid.card_mul_le` — for *any* `d`: a generically
  rigid graph has `d * #V ≤ #E + d * (d + 1) / 2`. Rank-nullity proof
  via `Framework.finrank` + `LinearMap.finrank_range_add_finrank_ker` +
  `rigidityMap_finrank_range_le`, finished by `omega`. The `d = 2`
  specialization (`2 * #V ≤ #E + 3`) lives at the Phase-5 boundary as
  a one-line corollary, not in `Framework.lean`. Phrased additively
  per the no-`ℕ`-subtraction rule.
- [x] `top_fin_two_isGenericallyRigid` — for *any* `d`: `K₂` is generically
  rigid. Proof case-splits on `d = 0` (framework space is 0-dim, kernel
  is 0-dim trivially) vs `d ≥ 1` (use placement `p 0 = 0, p 1 = e₀`,
  show rigidity map is non-zero by computing
  `⟪0 - e₀, e₀ - 0⟫_ℝ = -1`, hence `dim range ≥ 1` and rank-nullity
  closes with `nlinarith` / `omega` after a `Nat.le_mul_self d` hint
  for the quadratic step `2d + 1 ≤ (d+1)(d+2)/2`).
  (`d = 0`: `-1 ≤ 0`; `d = 1`: `1 ≤ 1`; `d = 2`: `3 ≤ 3`;
  `d ≥ 3`: more slack). The Laman-flavoured corollary
  `top_fin_two_isGenericallyRigid` lives in `Laman.lean` /
  `LamanTheorem.lean` (not here) and just instantiates `d = 2`.

### Independent of `G`: trivial motions and placements

These live in `Framework.lean` but don't touch `SimpleGraph`. Some
may be upstream-eligible mirrors.

- [ ] `Framework.finrank` — `Module.finrank ℝ (Framework V d) =
  Fintype.card V * d`. Upstream-style proof through
  `Module.finrank_pi_fintype` and `finrank_euclideanSpace`.
- [ ] `EuclideanSpace.finrank_eq_card` — already exists upstream as
  `finrank_euclideanSpace`. Just import.
- [ ] (Mirror) `Module.finrank_skewAdjointMatricesSubmodule_one` —
  dim of skew matrices = `d(d-1)/2`. **Open question:** does mathlib
  have this? Search before mirroring. If not, prove via the explicit
  basis indexed by `{(i, j) : Fin d × Fin d | i < j}`.

## Decisions made during this phase

(Phase-local trade-offs; cross-cutting ones go in `../DESIGN.md`.)

### Phase-local choices and proof techniques

- **Rigidity defined via `LinearMap`, matrix as derived view.** See
  *Architectural choices*. The two questions in `DESIGN.md` *Choices
  to revisit* — "Rigidity matrix" and "Generic placement" — are
  resolved (LinearMap; max-rank-placement-exists). `DESIGN.md` already
  reflects this.

- **No affine-spanning side-condition in `IsInfinitesimallyRigid`.**
  Working definition uses the always-true upper bound `dim ker ≤
  d(d+1)/2`. The lower bound (`dim TrivialMotions ≤ dim ker`) holds
  automatically; the equality `dim TrivialMotions = d(d+1)/2`
  requires affine-spanning OR a special case (e.g. `d = 2, #V = 2`).
  Pulling affine-spanning into the definition would force every
  `IsGenericallyRigid` proof to double-witness; pulling it out keeps
  the definition tight and pushes the side-condition to where it's
  needed (the lemmas connecting trivial motions to the kernel).

- **`open scoped InnerProductSpace` in `Framework.lean`.** The `⟪x, y⟫_ℝ`
  notation is `scoped[InnerProductSpace]`; without the open the file
  fails to parse with a cryptic "expected token" error. Mathlib-wide
  idiom; the build-failure → fix iteration was a one-liner so logged
  as a Phase-local decision rather than a FRICTION entry.

### Promoted to TACTICS / FRICTION / DESIGN

- *`RigidityMap` built by hand instead of compositionally* → FRICTION
  *[open]*. Three internal sites within `Framework.lean` (linearity
  proof, K₂ inner-product computation, the `change`-then-`rw` shape
  needed for `Sym2.lift` symmetry); compositional refactor via
  `innerSL` + `LinearMap.proj` + `LinearMap.pi` is the proposed fix.
- *`Set.ncard ↔ Fintype.card` two-rewrite glue* → FRICTION *[open]*.
  Mirror candidate alongside the existing `ncard_incidenceSet_eq_degree`
  pattern.
- *`omega` doesn't auto-commute opaque atoms* → FRICTION *[wontfix]*.
  Surfaced in `card_mul_le` (`Fintype.card V * d` vs `d * Fintype.card V`).
- *`nlinarith` over ℕ struggles with quadratic bounds* → FRICTION
  *[wontfix]*. Surfaced in K₂ closing arithmetic
  (`4 * d + 2 ≤ (d + 1) * (d + 2)`); workaround via `Nat.le_mul_self d`
  + `omega`.

## Blockers / open questions

- **Does mathlib have `finrank` of skew-symmetric matrices?**
  `skewAdjointMatricesSubmodule J` exists in
  `Mathlib/LinearAlgebra/Matrix/SesquilinearForm.lean` (line 647), but
  the survey didn't surface a dimension lemma. If it's missing, the
  cleanest mirror is `finrank_skewAdjointMatricesSubmodule_one_eq` in
  `Mathlib/LinearAlgebra/Matrix/SesquilinearForm.lean` (or
  `BilinearForm.lean`) stating `Module.finrank R
  (skewAdjointMatricesSubmodule (1 : Matrix (Fin n) (Fin n) R)) = n *
  (n - 1) / 2`. **Action:** look once before mirroring; if absent,
  prove via the explicit basis on upper-triangular off-diagonal
  entries. Surfaces at step 4 of the lemma order below.

- **Edge indexing: `↥G.edgeSet → ℝ` vs `G.edgeFinset → ℝ`.** Settled on
  `↥G.edgeSet → ℝ` for the `RigidityMap` codomain (no `[Fintype V]`
  needed for the *definition*); a `[Fintype V] [DecidableRel G.Adj]`
  companion going through `G.edgeFinset` is deferred until the matrix
  view (`RigidityMatrix`) actually arrives. Mirrors the
  `Set.ncard` / `Finset.card` split elsewhere in the project.

## Hand-off / next phase

Phase 4 is closed. Phase 5 starts with Laman's theorem in
`LamanTheorem.lean` (does not yet exist — create it).

**(⇒) edge-count direction** is essentially trivial given Phase 4:
specialize `IsGenericallyRigid.card_mul_le` at `d = 2`, getting
`2 * #V ≤ #E + 3`. Combined with the (2,3)-tightness condition this
yields a Laman spanning subgraph. The hard part is matroid-theoretic
(Lovász–Yemini), see ROADMAP §5.

**(⇐) Henneberg-induction direction** still hinges on
`IsLaman.exists_typeI_or_typeII_reverse` (the strengthened
decomposition that asserts `G'.IsLaman`, not just iso to a Henneberg
move on *some* `G'`). This is the Phase-3-carryover blocker tracked in
ROADMAP §5 and `notes/Phase3.md`. Two routes:

1. Henneberg blocker argument (classical, several pages).
2. Bypass via the rigidity matroid / induction on edge count, using
   `IsGenericallyRigid.mono` to handle supergraph rigidity.

If route 2 is chosen, Phase 4's deferred `TrivialMotions` API is *not*
needed; if Phase 5 ends up wanting it (e.g. for an affinely-spanning
identification of the kernel), come back and fill in the *TrivialMotions
API* checklist.

The first concrete Phase 5 commit: create `LamanTheorem.lean` with the
two-direction `theorem SimpleGraph.IsGenericallyRigid_two_iff_hasLamanSubgraph`
stub and `notes/Phase5.md`. Likely first lemma: the (⇒) `2 * #V ≤ #E + 3`
specialization of `IsGenericallyRigid.card_mul_le`.

Phase 5 is responsible for the `d = 2` specializations
(`top_fin_two_isGenericallyRigid` and `2 * #V ≤ #E + 3`); Phase 4
ships only the general-`d` shapes.

The `finrank_trivialMotions_eq_of_affinelySpanning` lemma is *not* on
the critical path for Laman's theorem if the (⇒) direction goes
through `IsGenericallyRigid.card_mul_le` directly. Defer it unless
Phase 5 needs it.
