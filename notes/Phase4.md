# Phase 4 — Frameworks and infinitesimal rigidity (work log)

**Status:** in progress (planning only this session — no Lean code).

This file is the per-phase work record. See `../ROADMAP.md` for the
high-level plan and `../DESIGN.md` for cross-cutting design choices.

## Current state

Plan-only session. Surveyed mathlib's `EuclideanSpace`, `LinearMap`,
`Matrix.rank`, and `skewAdjointMatricesSubmodule` APIs and settled the
two open Phase 4 design questions in `DESIGN.md` *Choices to revisit*:

* **Rigidity matrix encoding.** Define `RigidityMap G p` as a
  `LinearMap`; derive the matrix view via `LinearMap.toMatrix` only
  where a concrete matrix shape is needed. Rationale: rank-nullity and
  kernel-of-restriction arguments are cleanest on the `LinearMap`
  side; the matrix view costs one `LinearMap.toMatrix` rewrite when a
  `Matrix.rank` fact is needed.
* **"Generic" placement.** `G.IsGenericallyRigid d := ∃ p,
  G.IsInfinitesimallyRigid p d`. Avoids algebraic-geometry
  prerequisites; the equivalence to "Zariski-open set of placements"
  is a downstream theorem (not needed for either Laman direction in
  Phase 5 if the (⇒) direction goes via `LinearMap.range` rank
  bounds).

**Next concrete task** (one sentence): create `Framework.lean` with
the four definitions in *Definitions* below (no proofs yet) and
confirm `lake build CombinatorialRigidity.Framework` succeeds
on a stub file with `sorry` for any non-`def` content.

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

- **`Framework V d := V → EuclideanSpace ℝ (Fin d)`.** A bare type
  alias (a `def`, not `abbrev` — same `def`-vs-`abbrev` rule as the
  rest of the project per `../ROADMAP.md` *Engineering conventions*).
  When `[Fintype V]`, the inner-product / module / finite-dimensional
  instances fire automatically via `PiLp.innerProductSpace` and
  `Module.finrank_pi_fintype`. The `finrank` is `Fintype.card V * d`
  (one chain through `Module.finrank_pi_fintype` and
  `finrank_euclideanSpace`).

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

- [ ] `Framework V d` — placement type alias
- [ ] `RigidityMap G p` — differential of edge-length-squared
- [ ] `RigidityMatrix G p` — matrix view via `LinearMap.toMatrix`
- [ ] `trivialMotionAction p` — `(translation, skew) → motion`
- [ ] `TrivialMotions G p` — `LinearMap.range (trivialMotionAction p)`
- [ ] `IsInfinitesimallyRigid G p d`
- [ ] `IsGenericallyRigid G d`

### `RigidityMap` API

- [ ] `rigidityMap_apply` — `(RigidityMap G p) p' ⟨e, he⟩ = …` for the
  underlying Sym2 lift. The `Sym2.lift` discharge is the standard
  symmetric-bilinear pattern (cf. `Sym2.lift` examples).
- [ ] `rigidityMap_mono` — `G ≤ G' → ∃ restrict, RigidityMap G p =
  restrict ∘ₗ RigidityMap G' p`. Concretely the codomain
  `G'.edgeSet → ℝ` restricts to `G.edgeSet → ℝ` along the inclusion.
  Equivalent shape: `LinearMap.ker (RigidityMap G' p) ≤
  LinearMap.ker (RigidityMap G p)`.
- [ ] `rigidityMap_ncard_le` — bound on rank: `Module.finrank ℝ
  (LinearMap.range (RigidityMap G p)) ≤ G.edgeSet.ncard`. Direct from
  the codomain dimension being `#E`.

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

- [ ] `IsGenericallyRigid.mono` — `G ≤ G' → G.IsGenericallyRigid d →
  G'.IsGenericallyRigid d`. From `rigidityMap_mono`: if `G` is
  generically rigid via placement `p`, then `LinearMap.ker (RigidityMap
  G' p) ≤ LinearMap.ker (RigidityMap G p)`, so the kernel of `G'` has
  dimension ≤ that of `G`'s, hence ≤ `d(d+1)/2`. **One-liner.**
- [ ] `IsGenericallyRigid.card_mul_le` — for *any* `d`: a generically
  rigid graph has `d * #V ≤ #E + d * (d + 1) / 2`. Pick a witness
  `p`, then by rank-nullity `d * #V = dim ker + dim range ≤ d(d+1)/2
  + #E`. **No precondition needed** — the rank bound is unconditional
  on this form (no affine-spanning required because we use
  `IsInfinitesimallyRigid` as the upper bound on `dim ker`). The
  `d = 2` specialization (`2 * #V ≤ #E + 3`) is what feeds Laman's
  theorem; it lives as a one-line corollary at the Phase-5 boundary,
  not in `Framework.lean`. Phrased additively per the
  no-`ℕ`-subtraction rule.
- [ ] `top_fin_two_isInfinitesimallyRigid` — for *any* `d`: `K₂`
  with vertices placed at two distinct points (say
  `![0, …, 0]` and `![1, 0, …, 0]`) is infinitesimally rigid. The
  `RigidityMap` has rank 1 from the single edge, so `dim ker =
  2d - 1`. We need `2d - 1 ≤ d(d+1)/2`, which holds for all `d ≥ 0`
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

- **Rigidity defined via `LinearMap`, matrix as derived view.** See
  *Architectural choices*. The two questions in `DESIGN.md` *Choices
  to revisit* — "Rigidity matrix" and "Generic placement" — are
  resolved (LinearMap; max-rank-placement-exists). Will update
  `DESIGN.md` once Phase 4 lands one usable definition.

- **No affine-spanning side-condition in `IsInfinitesimallyRigid`.**
  Working definition uses the always-true upper bound `dim ker ≤
  d(d+1)/2`. The lower bound (`dim TrivialMotions ≤ dim ker`) holds
  automatically; the equality `dim TrivialMotions = d(d+1)/2`
  requires affine-spanning OR a special case (e.g. `d = 2, #V = 2`).
  Pulling affine-spanning into the definition would force every
  `IsGenericallyRigid` proof to double-witness; pulling it out keeps
  the definition tight and pushes the side-condition to where it's
  needed (the lemmas connecting trivial motions to the kernel).

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
  entries.

- **`Sym2.lift`-based definition of `RigidityMap` may need a glue
  lemma.** The map outputs `⟪p u - p v, p' u - p' v⟫`; to lift through
  `Sym2.lift`, we need to verify symmetry under `(u, v) ↔ (v, u)`,
  which is one `simp [Sym2.lift_mk]` line *if the inner product
  unfolding is in the simp set*. May need an explicit `RigidityMap.symm`
  helper if the standard simp set doesn't close it.

- **Edge indexing: `↥G.edgeSet → ℝ` vs `G.edgeFinset → ℝ`.** The
  former doesn't need `[Fintype V]` for the *definition*; the latter
  is more natural for the matrix view. Plan: define on `↥G.edgeSet`,
  add a `[Fintype V] [DecidableRel G.Adj]` companion that goes through
  `G.edgeFinset` for `LinearMap.toMatrix`. Mirrors the
  `Set.ncard` / `Finset.card` split elsewhere in the project.

- **Does mathlib have a clean `Sym2.lift` for inner products?** The
  pattern `⟪p u - p v, p' u - p' v⟫` is common enough that there might
  be a helper. **Action:** check `Mathlib/Analysis/InnerProductSpace/`
  and `Mathlib/Data/Sym/Sym2.lean` once; if absent, write the lift by
  hand.

## Hand-off / next phase

(Filled in when Phase 4 closes.)

The current Phase 4 entry-point for the next agent: open
`Framework.lean` (does not yet exist — create it). The first commit
should land the four definitions in *Definitions* above, with `sorry`
permitted for the linearity proof of `RigidityMap` only — the other
three are pure type definitions with no proof obligation. Confirm
`lake build CombinatorialRigidity.Framework` succeeds before
proceeding to lemmas.

The recommended lemma order (each commit adds 2–4):

1. `Framework.finrank` and the basic `Module.finrank` ledger.
2. `RigidityMap` definition + `rigidityMap_apply`.
3. `rigidityMap_mono` and `rigidityMap_ncard_le`.
4. `TrivialMotions` definition + `trivialMotions_le_ker` (this is the
   first non-trivial proof — check that `⟪x, A • x⟫ = 0` for skew `A`
   is a one-line mathlib fact or one-line mirror).
5. `finrank_trivialMotions_le` (mirror lemma if needed for skew-matrix
   dimension).
6. `IsInfinitesimallyRigid` and `IsGenericallyRigid` definitions.
7. `IsGenericallyRigid.mono` (one-liner from step 3).
8. `top_fin_two_isInfinitesimallyRigid` worked example (general `d`).
9. `IsGenericallyRigid.card_mul_le` for general `d` — closes Phase 4.

Phase 5 is responsible for the `d = 2` specializations
(`top_fin_two_isGenericallyRigid` and `2 * #V ≤ #E + 3`); Phase 4
ships only the general-`d` shapes.

The `finrank_trivialMotions_eq_of_affinelySpanning` lemma is *not* on
the critical path for Laman's theorem if the (⇒) direction goes
through `IsGenericallyRigid.card_mul_le` directly. Defer it unless
Phase 5 needs it.
