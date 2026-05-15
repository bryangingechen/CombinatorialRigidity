# API and tactic friction log

A long-running record of one-off mathlib API gaps, tactic limitations,
and proof-shape friction encountered while building this project. Each
entry is self-contained: future agents can either add new entries,
work an open one (upstream PR / project helper / refactor), or strike
through one that has been resolved.

This file is **append-mostly**: keep resolved entries with a
strikethrough and a "Resolved by …" note rather than deleting them.
The history is the value — a future agent picking up a similar issue
can see how it was handled before.

> **Scope.** This file holds *one-off* frictions: a specific lemma I
> needed and mirrored, a specific bug I worked around. *Cross-cutting
> lessons* — "always do X", "if you see pattern Y, prefer Z" — belong
> in `TACTICS-GOLF.md` (idioms / golf) or `TACTICS-QUIRKS.md`
> (rescue / build-failure recovery) instead — together they are the
> project's tactical reference.
> Don't bury a general rule in a `[resolved]` entry here; it won't be
> found again.

## How this file is used

- After landing a phase, review what proofs felt awkward. Did you
  reach for the same glue lemma three times? Did `grind` need an
  unusually long hint list? File an entry — and if the lesson is
  cross-cutting, lift it into `TACTICS-GOLF.md` (idioms) or
  `TACTICS-QUIRKS.md` (rescue) instead.
- When starting a new session, optionally browse [Open](#open) for a
  small upstream-able item to land alongside the main work. Skim
  [Anti-patterns / known dead ends](#anti-patterns--known-dead-ends)
  if you're about to try something that might already have been
  rejected.
- Items that turned into actual upstream candidates live under
  `Mathlib/<exact mathlib path>` (project mirror); each entry under
  [Mirrored](#mirrored) links to its mirror file.
- The "Ending a session" step in `ROADMAP.md` includes a friction
  review: do not skip it. Even "no new entries this session" is a
  useful checkpoint.

## Entry format

```
### [STATUS] Short title
- **Where it bit:** which proof / file
- **Friction:** what extra work was needed
- **Proposed fix:** named lemma / tactic / refactor
- **Status:** open / mirrored / upstreamed / wontfix / resolved
- **Mirror file (if any):** path under `Mathlib/`
```

## Sections

- [Open](#open) — actionable items you'd consider working on.
- [Anti-patterns / known dead ends](#anti-patterns--known-dead-ends)
  — wontfix items: tried-and-rejected approaches, deprecated patterns,
  tactic limitations. Worth seeing once so future agents don't
  re-litigate.
- [Mirrored](#mirrored) — upstream-eligible lemmas now living under
  `Mathlib/<path>`. Active reference list — DESIGN.md "Mirror
  directory" points here.
- [FRICTION-archive.md](FRICTION-archive.md) — design history for
  resolved project-internal entries (helper extraction, refactor,
  simp-set tweak). Search-target only, not read-on-load. Moved out
  of this file post-Phase-6 audit once each entry's resolution had a
  real index elsewhere (mirror lemma, project helper, or
  TACTICS-GOLF / TACTICS-QUIRKS § cross-reference).

**Filing rule for new entries.** Pick by what the *next agent* would
do with it: open if you'd act on it; anti-pattern if you wouldn't but
want to warn future agents; mirrored if you mirrored an upstream
lemma; resolved otherwise. File new resolved entries here first
(they may want eyes); migrate to `FRICTION-archive.md` on the next
housekeeping pass once their resolution is fully indexed.

## Open

### [open] `Polynomial.X` in a `set := ... .det` binding needs an explicit type ascription
- **Where it bit:** `exists_affinelySpanning_rigid_placement` in
  `RigidityMatroid.lean`. Writing
  `set P : Polynomial ℝ := (Polynomial.X • M₁.map C + M₀.map C).det`
  fails with `typeclass instance problem is stuck: Semiring ?m`
  because the elaborator picks the type of `Polynomial.X`
  bottom-up from the body without consulting the outer `: Polynomial ℝ`
  ascription.
- **Friction:** the matrix entries `M₁.map C` *do* live in
  `Polynomial ℝ`, so the `•` action is well-typed once the scalar's
  ring is fixed; but the parser commits to elaborating `Polynomial.X`
  before unifying with the action's scalar type. Workaround: annotate
  the `X` literal explicitly:
  `set P : Polynomial ℝ :=
    ((Polynomial.X : Polynomial ℝ) • M₁.map C + M₀.map C).det`.
- **Proposed fix:** none upstream; standard Lean 4 elaboration order
  quirk. If you see this exact error message on a `Polynomial`-valued
  expression, look first for a bare `Polynomial.X` (or `1`, `0`)
  whose containing ring is set by the surrounding context but not
  by the local syntax.
- **Status:** open (project-internal note). Promote to
  `TACTICS-QUIRKS.md` if the same shape bites in a second proof.

### [open] `h ▸ ...` substitutes through ambient terms, oversubstituting when the goal already mentions the rewritten side
- **Where it bit:** `Function.Injective.eventually_update_of_continuousAt`
  in the new `Mathlib/Topology/Separation/Hausdorff.lean` mirror. I had
  `h_eq0 : update p₀ c (f x₀) = p₀` and wanted to produce
  `Injective (update p₀ c (f x₀))` from `hp₀ : Injective p₀` via
  `h_eq0 ▸ hp₀` (or `.symm ▸ hp₀`). Lean inferred a motive that *also*
  rewrote `p₀` inside the surrounding expected type, producing the
  oversubstituted `Injective (update (update p₀ c (f x₀)) c (f x₀))`.
- **Friction:** `▸` in term mode picks the most general motive against
  the expected type from the calling context. When that expected type
  itself contains both sides of the rewrite, `▸` ambiguity bites and
  produces an "oversubstituted" type.
- **Proposed fix / workaround:** isolate the rewrite into a `have`
  whose stated type fixes the motive:
  `have hinj₀ : Injective (update p₀ c (f x₀)) := by rw [h_eq0]; exact hp₀`.
  Then pass `hinj₀` into the outer term. The tactic-mode `rw` does not
  suffer from motive ambiguity because the goal at that point is just
  the stated type, not the surrounding calling context.
- **Status:** open (project-internal note). Promote to
  `TACTICS-QUIRKS.md` if the same shape bites in a second proof.
  Recognition: `▸ ...` errors with "expected type" showing a
  doubly-substituted term (the rewrite target appears nested inside
  itself).

### [resolved] typeII reverse Henneberg move: Laman preservation requires a non-trivial choice
- **Where it bit:** Phase 3 close, while planning
  `IsLaman.exists_typeI_or_typeII_reverse`.
- **Friction:** The Phase-3-start hand-off identified "find non-adjacent
  neighbors among the three degree-3 neighbors" as the tricky piece.
  That part is straightforward (sparsity at `{v, a, b, c}` ⇒ ≤ 2 edges
  among `{a, b, c}` ⇒ a non-adjacent pair exists; see
  `IsSparse.exists_nonadj_among_three_neighbors`). The genuinely hard
  piece is showing that *for some* non-adjacent pair `{a, b}`, the
  reconstructed `G' := (G - v) + edge(a, b)` is Laman. An arbitrary
  non-adjacent pair does **not** suffice: concrete counter-example,
  `V = {v, x, y, z, w₁, w₂}` with edges `{v-x, v-y, v-z, x-z, x-w₁,
  x-w₂, y-w₁, y-w₂, w₁-w₂}` (Laman, `v` of degree 3 to `{x, y, z}`,
  `{x, y}` non-adjacent), and `G' = (G-v) + xy` violates sparsity at
  the 4-set `{x, y, w₁, w₂}` (6 edges where `2·4 - 3 = 5`). Picking
  the other non-adjacent pair `{y, z}` does work — but the
  combinatorial choice is the heart of Henneberg's classical theorem
  and requires several pages of contradiction/blocker reasoning.
- **Resolution:** Phase 5 delivered the Laman-preservation half via
  the Henneberg blocker argument (the per-pair tight-blocker witness
  combined via `IsTightOn.union_inter`); Phase 7 lifted the proof
  core to `IsSparse` (`IsSparse.typeII_reverse_blocker` +
  `IsSparse.exists_typeI_or_typeII_reverse`) and re-presented the
  Laman conclusion in flat form
  (`IsLaman.exists_typeI_or_typeII_reverse`, Henneberg.lean) as a thin
  shell over the sparse version. The operation-form intermediates that
  Phase 5 routed through (`exists_typeI_or_typeII_iso`,
  `IsLaman.typeII_reverse_blocker`, `typeII_reverse_witness_or_blocker`)
  were deleted in Phase 7 Commit 6.
- **Status:** resolved (Phase 5 + Phase 7 Commit 6).

### [resolved] No mathlib `LinearIndependent ![u, v] ↔ det ≠ 0` in dim 2
- **Where it bit:** `exists_affinelySpanning_rigid_placement_two` in
  `RigidityMatroid.lean`. Inside the per-triple finiteness argument
  we needed: from the quadratic determinant `u 0 * v 1 - u 1 * v 0 ≠
  0` (with `u, v : EuclideanSpace ℝ (Fin 2)`) deduce
  `LinearIndependent ℝ ![u, v]`.
- **Resolution:** the right primitive at d-general is
  `Matrix.linearIndependent_rows_of_det_ne_zero` (in
  `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`), bridged to
  `EuclideanSpace` via `WithLp.linearEquiv` and
  `LinearMap.linearIndependent_iff`. The Phase 6 task-4 d-general lift
  replaced the dim-2 private helper `linearIndependent_pair_of_det_ne_zero`
  with the project-private bridge `affineIndependent_of_difference_det_ne_zero`
  that consumes the row-LI lemma directly. The dim-2 helper has been
  retired entirely.
- **Lesson:** same as the `finSuccAboveEquiv` and `LinearMap.ltoFun`
  finds — mathlib's matrix-determinant API is denser than the dim-2
  case-by-case API. When the d-general statement is available, use
  it; the dim-2 specialisation collapses by `rfl` or one-line glue.
- **Lifted to:** TACTICS-GOLF § 3 *Search mathlib before mirroring*
  (one of three case studies cited there).

### [resolved] No packaged `ℝ`-linear injection `Module.Dual ℝ M →ₗ[ℝ] (M → ℝ)`
- **Where it bit:** `edgeSetRowIndependent_iff_linearIndepOn_rigidityRow`
  in `RigidityMatroid.lean`. We needed to bridge `LinearIndepOn` of a
  family in `(Framework V d → ℝ)` (the blueprint's set-of-functions
  formulation of `EdgeSetRowIndependent`) with `LinearIndepOn` of the
  same family viewed in `Module.Dual ℝ (Framework V d)` (where
  `LinearMap.dualMap` rank identities apply).
- **Resolution:** mathlib *does* ship this — as
  `LinearMap.ltoFun R M N A : (M →ₗ[R] N) →ₗ[A] M → N`
  (`Mathlib.Algebra.Module.LinearMap.Basic`). Instantiate
  `R = N = A = ℝ` for the dual case. Injectivity is
  `DFunLike.coe_injective`. The original ~16-line private
  `dualToFunₗ` + `dualToFunₗ_apply` + `dualToFunₗ_injective` scaffold
  collapses to a single call. The Phase 6 task-2 simplification pass
  pulled this in (commit landing alongside the task-2 cleanup);
  the bridge lemma is now 7 lines total.
- **Lesson:** same as the `finSuccAboveEquiv` find — sweep
  `lean_loogle` against the type signature you actually need before
  rolling a project-local helper. The exact type
  `(_ →ₗ[_] _) →ₗ[_] (_ → _)` returned `LinearMap.ltoFun` on the
  first try.
- **Lifted to:** TACTICS-GOLF § 3 *Search mathlib before mirroring*.

### [resolved] `congr_fun` does not apply to `LinearMap` (`Module.Dual` instance)
- **Where it bit:** `typeI_edgeSetRowIndependent_extend` in
  `MatroidIdentification.lean`. The hypothesis `hcd : c • row newEdgeA +
  d • row newEdgeB = 0` is an equation in
  `Module.Dual ℝ (Framework (Option V) 2) = Framework (Option V) 2 →ₗ[ℝ] ℝ`,
  i.e., a `LinearMap`, not a raw `Function`. The first instinct
  `congr_fun hcd test_motion` to extract the per-input equation
  errored with `Application type mismatch`.
- **Resolution:** `DFunLike.congr_fun hcd test_motion`. `LinearMap`
  is `FunLike`, not literally `Function`; even though it coerces to
  one, `congr_fun` needs a literal `Pi`-typed equation. The error
  message does not flag the `FunLike`-vs-`Function` distinction.
  Sibling of the EuclideanSpace = PiLp gotcha (TACTICS-QUIRKS § 9):
  both fall under "acts like a function but isn't literally one."
- **Status:** resolved (project-internal lesson). Same gotcha applies
  to `LinearEquiv`, `AlgHom`, `ContinuousLinearMap`, etc.
- **Lifted to:** TACTICS-QUIRKS § 12 *`congr_fun` does not apply to
  `LinearMap` (or any `FunLike`)*.

### [resolved] `Set.Finite.subset (finite_setOf ...)` leaves metavariables when leading-coeff is the only resolved unknown
- **Where it bit:** `exists_affinelySpanning_rigid_placement_two` in
  `RigidityMatroid.lean`. Inside the per-triple finiteness proof we
  applied `Set.Finite.subset (finite_zeros_quadratic h_γ_ne)` to bound
  the bad-`t` set by the polynomial zero set. `h_γ_ne : γ ≠ 0`
  pins down `γ` in the conclusion's implicit args, but `β` and `α`
  stay as metavariables — Lean leaves three goals (the subset relation
  plus two `⊢ ℝ` placeholders), and the linter (multiGoal-style)
  flags every subsequent step as touching multiple goals.
- **Resolution:** dissolved by the Phase 6 task-4 d-general lift. The
  private `finite_zeros_quadratic` helper retired; the d-general proof
  uses `(Polynomial.finite_setOf_isRoot hP_ne).subset h_bad_sub` with
  a *named* `P : Polynomial ℝ` whose coefficients are fully determined
  by the surrounding `set` bindings. The "unresolved metavariables on
  applying a `Finite.subset (finite_…)`" symptom was a side-effect of
  three free scalars (`γ, β, α`) being passed to a helper that did not
  capture them; the d-general matrix form (`M₀, M₁`) bundles them
  into named matrices, and the polynomial is a single named object.
- **Lesson:** when reaching for a quadratic/cubic/degree-`d` zero-set
  finiteness, prefer `Polynomial.finite_setOf_isRoot` on a fully-named
  `P : Polynomial R` over a hand-rolled `finite_zeros_quadratic`-style
  helper that takes free coefficients as arguments. Mathlib's
  matrix-of-polynomial machinery (`coeff_det_X_add_C_card`,
  `natDegree_det_X_add_C_le`) builds `P` from named matrices, which
  pins down all the implicit arguments at the apply site.

### [resolved] `AffineIndependent` ↔ `LinearIndependent` reindex from `{x : Fin 3 // x ≠ 0}` to `Fin 2`
- **Where it bit:** `exists_affinelySpanning_rigid_placement_two` in
  `RigidityMatroid.lean`. After `affineIndependent_iff_linearIndependent_vsub
  ℝ ![pt t a, pt t b, pt t c] 0` the goal is LI of a family
  indexed by `{x : Fin 3 // x ≠ 0}`, but the natural witness is
  `LinearIndependent ℝ ![u, v]` on `Fin 2`.
- **Resolution:** mathlib *does* ship the canonical reindex — just not
  packaged in the obvious place: `finSuccAboveEquiv (p : Fin (n + 1)) :
  Fin n ≃ { x : Fin (n + 1) // x ≠ p }` in
  `Mathlib.Logic.Equiv.Fin.Basic` plus `linearIndependent_equiv` in
  `Mathlib.LinearAlgebra.LinearIndependent.Defs`. Composing the two
  rewrites the goal directly to `LinearIndependent ℝ ![p_b -ᵥ p_a,
  p_c -ᵥ p_a]`, no hand-rolled reindex needed. The earlier *Proposed
  fix* (mirror a 15-line bridge under `CombinatorialRigidity/Mathlib/`)
  was premature — the right primitives were already upstream; we just
  hadn't searched for them. Discovery routed through
  `EuclideanGeometry.oangle_ne_zero_and_ne_pi_iff_affineIndependent`'s
  proof in mathlib, which uses the same pair.
- **Lesson:** before mirror-ing a bridge under
  `CombinatorialRigidity/Mathlib/`, sweep `lean_loogle` / `lean_leanfinder`
  for the canonical primitives. The "mirror it ourselves" instinct
  bloats the project surface; mathlib's API for `Fin`-indexed families
  is denser than it looks.
- **Lifted to:** TACTICS-GOLF § 3 *Search mathlib before mirroring*.

### [open] `AffineSubspace.nonempty_of_affineSpan_eq_top` takes `(k V P)` explicit

- **Where it bit:** `trivialMotions_three_le_finrank_of_affinelySpanning_two`
  in `TrivialMotions.lean`. Extracting a vertex `v₀ : V` from
  `hp : affineSpan ℝ (Set.range p) = ⊤` to pin down a contradiction
  with "p constant".
- **Friction:** the mathlib lemma sits inside an `AffineSubspace`
  namespace section where `(k V P)` are all explicit. To call it, you
  write `AffineSubspace.nonempty_of_affineSpan_eq_top _ _ _ hp` — three
  underscores plus the proof. With dot notation `hp.nonempty…` would be
  ambiguous (no syntactic anchor for the subject), so the long form is
  the only ergonomic option.
- **Proposed fix:** add a project helper `range_nonempty_of_affineSpan_eq_top`
  that fixes the `(ℝ, V, P)` and exposes a one-arg call, or change the
  upstream signature to make `(k V P)` implicit (they're recoverable
  from `Set.range p`'s element type). Either route would land a
  one-line site at every call.
- **Status:** open. Worked around with `_ _ _` underscores; revisit if
  the same pattern surfaces in the `(2, 3)`-sparsity-side proof or
  the affinely-spanning-rigid-placement lemma.

### [open] `fin_cases i` leaves `⟨n, ⋯⟩` rather than the literal `n`, blocking `rw`

- **Where it bit:** `trivialMotions_three_le_finrank_of_affinelySpanning_two`,
  `h_const : ∀ v, p v = p v₀`. After `ext i; fin_cases i` the goal was
  `(p v).ofLp ⟨0, ⋯⟩ = (p v₀).ofLp ⟨0, ⋯⟩`, but the hypotheses
  `h_const_pv0 v : (p v) 0 = -c 1 / c 2` carry the literal `0`. `rw`
  failed: "did not find an occurrence of the pattern `(p v).ofLp 0`".
- **Friction:** standard pattern-matching glitch — the `⟨0, ⋯⟩` view
  and the literal `0` view are not syntactically equal even though
  Lean prints them identically in some contexts. Worked around with
  `change (p v) 0 = (p v₀) 0` before each `rw`, which forces the
  rewrite-friendly form.
- **Proposed fix:** none upstream; this is a tactic-quirk note. If
  it bites again, document the `match i with | ⟨0, _⟩ => change _; rw …`
  idiom in `TACTICS-QUIRKS.md`.
- **Status:** open (project-internal note). Worth promoting to
  `TACTICS-QUIRKS.md` if it surfaces a third time.

### [open] Defining the 2×2 90° rotation via `Matrix.toEuclideanLin` blocks coordinate simp

- **Where it bit:** `rotJTwo` in `TrivialMotions.lean`. The natural
  first attempt was `noncomputable def rotJTwo := Matrix.toEuclideanLin !![0, -1; 1, 0]`,
  which makes the simp lemmas `rotJTwo_apply_zero/one` non-`rfl`.
  Downstream `simp` calls then had to expand
  `Matrix.toEuclideanLin_apply`, `Matrix.mulVec`, `Matrix.dotProduct`,
  `Fin.sum_univ_two`, plus `Matrix.cons_val_zero/one` to reach
  `(rotJTwo v) 0 = -(v 1)`. Several iterations of "add more simp
  lemmas" failed to close the goal cleanly.
- **Friction:** the `Matrix.toEuclideanLin` route hides the explicit
  coordinate values behind a `Matrix.vecHead`/`Matrix.cons_val_*`
  chain that simp doesn't unfold uniformly without manual hints.
- **Proposed fix:** define `rotJTwo` directly via the `LinearMap`
  structure (`toFun := fun v => !₂[-(v 1), v 0]`, with hand-checked
  `map_add'` and `map_smul'`); then `rotJTwo_apply_zero/one` become
  `rfl`-simp lemmas and downstream `simp` closes coordinates without
  matrix-unfolding hints. We switched to this and it landed cleanly.
- **Status:** open (idiom note). Promote to `TACTICS-GOLF.md` as a
  "concrete 2×2 maps" subsection if a future phase introduces
  another explicit 2D map.

### [open] `IsSparse` is not `Decidable`, blocking small-example proofs by `decide`
- **Where it bit:** Phase 2 attempt at `K₄ \ e` is Laman (deferred).
- **Friction:** `IsSparse` is `∀ s : Finset V, ℓ ≤ k * #s → (G.edgesIn ↑s).ncard + ℓ ≤ k * #s`,
  but `Set.ncard` is noncomputable. Even though the statement is morally
  decidable for finite `V`, we can't close the K₄ \ e example with
  `decide` and instead fall back on a finite case analysis.
- **Proposed fix:** add a project-internal `IsSparse'` companion that
  goes through `Finset.sym2` + `Finset.filter` for the count. Prove
  `IsSparse ↔ IsSparse'` under `[Fintype V] [DecidableRel G.Adj]`.
  Then concrete examples can use `decide`.
- **Status:** open. Acceptable for now (the K₄ \ e example was deferred
  to Phase 3 where Henneberg gives a one-liner), but worth doing if a
  later phase wants to mechanize more concrete graphs.

### ~~[open] No dim-2 "vector orthogonal to two LI vectors is zero" helper~~

- **Where it bit:** Three private helpers in `HennebergRigidity.lean`
  (`exists_not_mem_span_singleton_dim_two`,
  `inner_sub_perp_of_eq`, `eq_zero_of_orthogonal_dim_two`,
  lines 75–118) supporting the typeI/typeII rigidity-preservation
  proofs. The blueprint prose treats "orthogonal to two LI vectors
  in `ℝ²` is zero" as a one-clause math step; the Lean walks
  `Submodule.span_induction` on the orthogonal complement (~20 lines).
- **Friction:** the existing helper rebuilds "orthogonal complement
  of a spanning set is `⊥`" from scratch via `span_induction`
  instead of routing through `Submodule.span_eq_top` +
  `Submodule.top_orthogonal_eq_bot`. The combined dance is heavier
  than necessary.
- **Resolution:** `Submodule.isOrtho_span`
  (`Mathlib.Analysis.InnerProductSpace.Orthogonal`) already packages
  "two spans are orthogonal iff generators pairwise inner-zero", so
  the `span_induction` is unnecessary. The rewritten proof routes
  `span ![v₁, v₂] ⟂ span {u}` through `isOrtho_span` (generators-only
  side-condition) then `h_span_top` + `isOrtho_top_left`
  (`⊤ ⟂ V ↔ V = ⊥`) + `span_singleton_eq_bot` (`ℝ ∙ u = ⊥ ↔ u = 0`).
  21-line body → 10 lines, no mirror lemma needed.
- **Status:** resolved (2026-05-15). No mathlib mirror; pure rewrite
  of the existing helper.
- **Lifted to:** TACTICS-GOLF § 3 *Search mathlib before mirroring*
  (the "spanning set ⇒ orthogonal-complement-trivial" bullet) —
  general rule is *reach for `Submodule.isOrtho_span` before
  `span_induction`*.

### ~~[open] No upstream "generic point off a line in `ℝ²`" helper~~

- **Where it bit:** `exists_off_line_off_finite_dim_two`
  (`HennebergRigidity.lean:195`).
- **Resolution:** mirrored as `AffineSubspace.biUnion_ne_univ_of_top_notMem`.
  See [Mirrored](#mirrored) for the full entry. The sibling
  `exists_typeII_q_on_line_dim_two` (Type II shape) is **not** covered
  by this approach — placing `q` *on* the line is a 1-parameter
  excluded-finite-α argument, naturally `Set.Finite.exists_notMem` in
  `ℝ`, not an affine-cover application — and stays project-internal.

### ~~[open] No `LinearIndepOn` "row-restriction transports LI through dual" helper~~

Resolved by mirroring `LinearIndependent.dualMap_of_surjective` /
`LinearIndepOn.dualMap_of_surjective` — see the corresponding entry in
[Mirrored](#mirrored) below.

### [open] `Function.Injective.option_elim` would clean up Henneberg-move injectivity

- **Where it bit:** `injective_option_elim` (`HennebergRigidity.lean:61`,
  private, ~5 lines). Used in `typeI_isGenericallyRigidInj_two` and
  `typeII_isGenericallyRigidInj_two_of_nonCollinear`. The "4-way
  rintro" shape recurs whenever a Henneberg iso constructor pairs
  an injective old placement with a fresh `q ∉ Set.range`.
- **Friction:** trivial proof, but project-internal and unnamed.
- **Proposed fix:** mirror `Function.Injective.option_elim` under
  `CombinatorialRigidity/Mathlib/Data/Option/Basic.lean`. Statement:
  `{f : α → β} (hf : Function.Injective f) {b : β} (hb : b ∉ Set.range f) :
  Function.Injective (fun o : Option α => o.elim b f)`.
- **Status:** open. **Priority: low**. Cosmetic — only mirror when
  there's a third caller.

### [resolved] Sym2-symmetry case split in `typeII_isInfinitesimallyRigid_extend` understated by blueprint

- **Where it bit:** `typeII_isInfinitesimallyRigid_extend`
  (`HennebergRigidity.lean`). The blueprint prose calls the
  deleted-edge recovery "subtract the second from the first";
  the Lean originally handled a `Sym2.eq_iff` case split on
  `s(u, v) = s(a, b)` *both ways*, and explicitly avoided
  `rcases ⟨rfl, rfl⟩` because the `subst` would eliminate `a`/`b`
  from the context.
- **Friction:** prose-to-Lean gap. The case split + `subst`
  avoidance isn't substantive math but is substantive Lean
  infrastructure.
- **Resolution:** the case split was unnecessary — `RigidityMap` is
  defined via `Sym2.lift` (`Framework.lean`), so Sym2-symmetry is
  baked in at the edge-subtype level. Rewriting
  `⟨s(u, v), he⟩ = ⟨s(a, b), h_eq ▸ he⟩` via `Subtype.ext h_eq` *before*
  unfolding the rigidity-map application lets the deleted-edge branch
  close in three lines (rewrite, `simp [rigidityMap_apply, …]`,
  `exact h_deleted`) rather than nine. No mirror needed; no blueprint
  prose change needed (the blueprint's "subtract the second from the
  first" reading is accurate — the orientation case split was a
  Lean-side artefact of un-lifting too early).
- **Lesson:** when a function is built via `Sym2.lift`, push
  `Sym2 V`-equalities through the subtype layer (`Subtype.ext`) rather
  than `Sym2.eq_iff`-case-splitting after unfolding. The orientation
  symmetry is encoded in the lift's symmetry proof — recovering it
  manually in the unfolded inner-product form duplicates work.
- **Status:** resolved (2026-05-15).
- **Lifted to:** TACTICS-GOLF § 5 *Lifting Subtype-Sym2 equalities*,
  subsection "Pattern (the other direction): `Sym2 V` equality →
  `G.edgeSet` subtype equality".

### [open] "Test motion `x_α`" gadget in Phase 7 understated by blueprint prose

- **Where it bit:** `typeI_edgeSetRowIndependent_extend`
  (`MatroidIdentification.lean:64`). The blueprint prose for new-row
  LI and old-vs-new disjointness invokes "the same trick" — but the
  Lean expands "the trick" into a `set x_α := fun w => w.elim α 0`
  binding plus a 15-line `Submodule.span_le` /
  `LinearMap.mem_ker` argument that the old-row span vanishes at
  `x_α`. The private helper `typeI_new_rows_coeff_zero` packages the
  coefficient-extraction.
- **Friction:** prose-to-Lean gap; the test-motion gadget is a
  substantive construction that should appear in the blueprint
  prose as a named gadget, not as "the same trick".
- **Proposed fix:** *first*, try simplifying the Lean — possibly
  via `Module.Dual.eval`-level API or a "evaluate a span at a
  vector" mathlib lemma. *If not*, add a brief aside to the
  blueprint prose acknowledging the explicit `x_α` test motion.
- **Status:** open. **Priority: medium**.

### [open] `elemSkewMap_ofLp_inr_apply` may already exist as `Matrix.stdBasisMatrix` difference

- **Where it bit:** `trivialMotionFamily_linearIndependent`
  (`TrivialMotions.lean:212`). The `elemSkewMap_ofLp_inr_apply`
  helper unpacks a `Eᵢⱼ - Eⱼᵢ`-style entry into specific coordinate
  cases, closed by `grind`.
- **Friction:** the "skew-symmetric basis matrix" pattern is
  generic linear algebra; the project-internal helper does the
  case analysis from scratch.
- **Proposed fix:** search mathlib (`lean_loogle` for
  `(Matrix.stdBasisMatrix _ _ 1) - (Matrix.stdBasisMatrix _ _ 1)`)
  for an existing API. If found, the helper collapses to one or
  two `simp` calls.
- **Status:** open. **Priority: low–medium**. Cosmetic; affects a
  finished phase.

## Anti-patterns / known dead ends

Tried-and-rejected approaches, deprecated patterns, and tactic
limitations. Worth a once-over so future agents don't re-litigate.

### [wontfix] `omega` doesn't see through nonlinear algebra on opaque atoms
- **Where it bit:**
  - `IsGenericallyRigid.card_mul_le` in `Framework.lean` —
    *commutativity*. `Framework.finrank = Fintype.card V * d`; the
    lemma uses `d * Fintype.card V`. omega treats both as different
    atoms.
  - `IsTightOn.union_inter` in `Sparsity.lean` — *distributivity*.
    omega has `(s ∪ t).card + (s ∩ t).card = s.card + t.card`
    (`Finset.card_union_add_card_inter`) but needs
    `k * #s + k * #t = k * #(s ∪ t) + k * #(s ∩ t)`; the atoms
    `k * #s`, `k * #t`, `k * #(s ∪ t)`, `k * #(s ∩ t)` are unrelated to
    omega without an explicit distributivity step.
- **Proposed fix:** none upstream — this is omega's intended design
  (atomic variables don't carry commutativity or distributivity).
  Workaround: pre-normalize via `rw`/`mul_comm` so the form omega sees
  matches the goal. For *commutativity*, `IsGenericallyRigid.card_mul_le`
  restated `h_total` as `Module.finrank ℝ (Framework V d) = d *
  Fintype.card V` via `rw [Framework.finrank, mul_comm]`. For
  *distributivity*, `IsTightOn.union_inter` stages a `have h_card_mul`
  via the 3-rewrite chain `rw [← Nat.mul_add, ← Nat.mul_add,
  Finset.card_union_add_card_inter]` then hands the multiplied identity
  to omega alongside the unmultiplied facts. `linear_combination k * h.symm`
  is a one-liner alternative but requires `Mathlib.Tactic.LinearCombination`
  which Sparsity does not currently import.
- **Status:** wontfix (intrinsic to omega).
- **Lifted to:** TACTICS-QUIRKS § 2 *`omega` doesn't carry
  commutativity or distributivity on atoms*.

### [wontfix] `omega` treats `set`-aliased terms as opaque atoms
- **Where it bit:** `IsSparse.typeII_reverse_blocker` in `Sparsity.lean`
  (originally the Laman shell `IsLaman.typeII_reverse_blocker` in
  `Henneberg.lean`, Phase 5 milestone 1; the friction was retained when
  Phase 7 lifted the core to `IsSparse`).
- **Friction:** the proof opens `set bridge := s(xs, ys)` and then
  defines `h_diff : (G'.edgeSet \ {bridge}).ncard + 1 = G'.edgeSet.ncard`
  from `Set.ncard_diff_singleton_add_one hbridge_in_G'`. Separately,
  `typeII_edgeSet_ncard` produces `h_typeII_count` mentioning
  `(G'.edgeSet \ {s(xs, ys)}).ncard` (the upstream lemma doesn't know
  about the alias). The two `ncard` terms are *definitionally* equal,
  but `omega` sees them as distinct atoms and can't bridge `h_diff`
  with `h_typeII_count` to derive `G'.edgeSet.ncard + 3 = …`.
- **Proposed fix:** none upstream. Workaround: explicit
  `rw [← hbridge_def] at h_typeII_count` (or `rw [hbridge_def] at
  h_diff`) to fold the literal expression back into the alias before
  invoking omega. The fix is one line once the cause is understood.
  Same pattern applies to `grind` and any tactic that uses syntactic
  atoms — it's a general consequence of `set name := expr` introducing
  a fresh local constant without globally substituting `expr` in
  hypotheses produced by *later* tactic calls.
- **Status:** wontfix (intrinsic to omega/grind's atomic-variable
  model; the `set` tactic's substitution scope is bounded by current
  goals and hypotheses, not future ones).
- **Lifted to:** TACTICS-QUIRKS § 1 *`omega`/`grind` treat
  `set`-aliased terms as opaque atoms*.

### [wontfix] `nlinarith` over ℕ struggles with quadratic bounds
- **Where it bit:** `top_fin_two_isGenericallyRigid` in `Framework.lean`,
  closing the arithmetic step `4 * d + 2 ≤ (d + 1) * (d + 2)` (over ℕ).
- **Friction:** `nlinarith` over ℕ doesn't reliably close this from
  scratch. Mathematically the bound rearranges to `d ≤ d * d` which is
  `0 ≤ d² - d = d(d-1)`, trivial over ℝ/ℤ via `sq_nonneg (d - 1)`, but
  ℕ-subtraction truncates and `nlinarith` can't recover the squaring.
  Workaround: expand `(d+1)*(d+2) = d*d + 3*d + 2` via `ring` (as a
  `have`), surface `d ≤ d*d` via `Nat.le_mul_self d`, then close with
  `omega`.
- **Proposed fix:** none upstream. The pattern is general: any
  ℕ-quadratic bound where one side has `d * d` and the other is linear
  in `d` benefits from `Nat.le_mul_self` as the bridge. Documented here
  so future agents reach for it directly instead of iterating
  `nlinarith` hint lists.
- **Status:** wontfix (intrinsic to `nlinarith`-on-ℕ; workaround is a
  one-liner once you know the trick).
- **Lifted to:** TACTICS-QUIRKS § 3 *`nlinarith` over ℕ on
  quadratic bounds: `Nat.le_mul_self`*.

### [wontfix] `revert` ordering before `e'.ind` is finicky
- **Where it bit:** `typeI_edgeSet` proof, backward direction.
- **Friction:** To do Sym2 induction on a hypothesis `e'` while
  preserving other hypotheses depending on `e'` (here: `heG : e' ∈ S`
  and `hmap : Sym2.map some e' = s(x, y)`), we `revert` the dependent
  hypotheses first. The order of revert determines the order of
  hypotheses in the lambda after `refine e'.ind fun p q ... => ?_`. The
  correct rule is **revert in reverse order of the lambda binders**:
  for lambda `fun p q heG hne hmap`, revert `hmap hne heG`. Forgetting
  this gave a confusing "rewrite failed" error in `typeII` because
  `hmap` ended up bound to a different hypothesis.
- **Proposed fix:** none needed; this is intrinsic to `revert`/`refine`
  semantics. Documented here so the next agent doesn't redo the trial
  and error. Alternative: use `induction e' with | h p q => …` which
  generalizes context automatically.
- **Status:** wontfix (tactic-semantics issue, not a missing lemma).

### [wontfix] `simp` leaves and-grouping in `typeII` `edgesIn` decomposition
- **Where it bit:** `typeII_isLaman` sparsity, `h_decomp` proof.
- **Friction:** the `s(some u, some v)` branch of the Sym2 case-split
  reduces under `simp [edgesIn, hcoe, Set.mem_preimage, T']` to
  `(G.Adj u v ∧ p) ∧ q ↔ (G.Adj u v ∧ q) ∧ p` for the same conjuncts
  `p, q` — `simp` does not re-associate `∧`. The matching `typeI`
  proof closes on bare `simp` because the `Adj` predicate there has
  no extra `s(u, v) ≠ s(a, b)` conjunct. Adding `; try tauto` after
  the simp closes the typeII case in one extra line per branch.
- **Proposed fix:** none upstream-able; this is just `simp` not
  doing classical AC. Documented so the next agent doesn't churn
  on the `simp` set when it inevitably "almost" works. **Tried
  later:** adding `and_assoc, and_left_comm` to the simp set does
  *not* work — they reorder past the `Sym2.map ... = s(some u, some v)`
  conjunct, breaking the `Sym2.exists_and_map_eq_mk_iff` simp pattern,
  so the `(some, some)` case fails to close even with the trailing
  `try tauto`. Stay with the `try tauto` workaround.
- **Status:** wontfix (tactic limitation, not a missing lemma).

### [wontfix] `push_neg` deprecated in favour of `push Not`
- **Where it bit:** `IsLaman.exists_degree_le_three`.
- **Friction:** `push_neg` triggers a deprecation warning. The
  replacement `push Not at hcontra` works but produces `3 < x` rather
  than `4 ≤ x`; an extra `omega` (or `Nat.add_one_le_iff`) is needed
  even though the two forms are defeq in `ℕ`.
- **Proposed fix:** none required from us; this is an upstream
  ergonomics issue. Documented here so future agents know not to
  re-litigate it.
- **Status:** wontfix (upstream concern).

### [wontfix] `lake build` of Phase 5 files is import-floor-bound and timing-noisy
- **Where it bit:** Performance audit in Phase 5's third cleanup pass.
- **Friction:** `Framework.lean`, `HennebergRigidity.lean`, and
  `Laman.lean` each take 20–40 s for a from-scratch `lake build`, but
  `lake env lean` on a stub file with just `Framework.lean`'s imports
  is already ~27 s — so most of the wall-clock is import loading, not
  within-file elaboration (Framework's own work is ~6 s, HR's ~19 s,
  Laman's ~11 s). The within-file portion is *itself* highly variable
  (10–50 s for the same source, depending on lake/OS caches). A/B
  comparing optimization candidates needs many runs per side and still
  often returns ambiguous results.
- **Proposed fix:** The two structural levers that *would* help are
  both multi-file changes: (a) convert the project + its `Mathlib/…`
  mirrors to Lean's `module` + `public import` system, which gives
  downstream files a smaller load surface (Phase 6 added four more
  importers — `TrivialMotions.lean`, `HennebergRigidity.lean`,
  `RigidityMatroid.lean`, `LamanTheorem.lean` — so the amortization
  is plausible now); (b) move the analysis-heavy half of
  `Framework.lean` behind a thinner facade so combinatorial files
  (`Sparsity.lean`, `Laman.lean`, `Henneberg.lean`) don't import the
  finite-dimension normed-module machinery transitively.
- **Status:** wontfix at the current scope; deferred to a dedicated
  perf pass post-Phase-6. The Phase-6 downstream additions cleared
  the "not enough beneficiaries to amortize" objection, but the
  structural change itself remains unmeasured against the noise band.
  Phase 5 third cleanup pass (`notes/Phase5.md`) records the
  per-candidate experiments and what trended where; see also
  `PERFORMANCE.md` *Module-system conversion*.

## Mirrored

### [mirrored] `Function.Injective.eventually_of_continuousAt` and `eventually_update_of_continuousAt` (openness of injectivity)
- **Where it bit:** `exists_nonCollinear_rigid_placement_dim_two`
  (`HennebergRigidity.lean`, the perpendicular-perturbation helper underneath
  `typeII_isGenericallyRigidInj_two`). The blueprint runs ~15 lines of prose;
  the Lean expanded to ~107 lines. The bulk of the gap was a hand-rolled
  "injectivity is eventually preserved" `∀ᶠ`-argument via
  `Finset.eventually_all` + componentwise `ContinuousAt.eventually_ne`, taking
  ~25 lines. Phase 7's Type II row-LI lift will need the same shape.
- **Friction:** mathlib has `Set.InjOn.exists_mem_nhdsSet` (in
  `Mathlib/Topology/Separation/Hausdorff.lean`) — compactness + neighborhood-of-
  a-set form — but no "componentwise-continuous finite-domain family,
  injective at a point, is eventually injective" form. Each Henneberg-rigidity
  move that goes through a perturbation had to re-prove this in place.
- **Resolution:** mirrored as
  - `Function.Injective.eventually_of_continuousAt`: for
    `[Finite V]`, `[T2Space α]`, a family `F : X → V → α` componentwise
    `ContinuousAt` at `x₀` with `Injective (F x₀)` is eventually injective in
    `𝓝 x₀`. Each `(u, v)` with `u ≠ v` contributes a
    `ContinuousAt.prodMk`-driven eventuality that `(F x u, F x v)` stays off
    the diagonal (closed in `α × α` by Hausdorffness); `Finset.eventually_all`
    aggregates.
  - `Function.Injective.eventually_update_of_continuousAt`: corollary for
    `update p₀ c (f x)` with `f x₀ = p₀ c` and `ContinuousAt f x₀`. The
    one-vertex perturbation shape that arises in Henneberg generic-placement
    arguments collapses to one term-mode call.

  The `h_inj_ev` block in `exists_nonCollinear_rigid_placement_dim_two` is now
  a four-line term-mode application of `eventually_update_of_continuousAt`
  (down from ~30 lines).
- **Status:** mirrored.
- **Mirror file:** `Mathlib/Topology/Separation/Hausdorff.lean`. Sits naturally
  alongside `Set.InjOn.exists_mem_nhdsSet` as a dual ("evaluate a parametric
  family at finitely many points" vs. "InjOn on a compact set") perspective on
  openness-of-injectivity.

### [mirrored] `AffineSubspace.biUnion_ne_univ_of_top_notMem` + `affineSpan_ne_top_of_ncard_le_finrank` (affine analogue of `Subspace.biUnion_ne_univ_of_top_notMem` plus a cardinality side-condition)
- **Where it bit:** `exists_off_line_off_finite_dim_two`
  (`HennebergRigidity.lean`, used by Phase 5 `typeI_isGenericallyRigidInj_two`
  and Phase 7 `typeI_edgeSetRowIndependent_lift`). The prose claim "pick a
  point off the line through `pa, pb` and off a finite avoid-set `S`" is one
  geometric step (over an infinite field, a proper line ∪ finitely many
  points doesn't cover the plane). The Lean wrapper expanded to a 35-line
  `pa + t • v` parametric construction with a
  `LinearIndependent.pair_add_smul_add_smul_iff` row-op and a
  `Set.Finite`-bad-set selection.
- **Friction:** mathlib has the linear-subspace cover theorem
  `Subspace.biUnion_ne_univ_of_top_notMem` (in `Mathlib/GroupTheory/CosetCover`)
  — over an infinite division ring, a vector space is not a finite union
  of proper *linear* subspaces — but no affine analogue. The affine version
  uniformly subsumes "proper subspace + finitely many points" as a single
  cover (points are 0-dim affine subspaces), which matches the prose
  one-step argument.
- **Resolution:** mirrored two lemmas.
  - `AffineSubspace.biUnion_ne_univ_of_top_notMem`: for `[DivisionRing k]
    [Infinite k] [AddCommGroup V] [Module k V]` and `{s : Finset
    (AffineSubspace k V)}` with `⊤ ∉ s`, `⋃ p ∈ s, (p : Set V) ≠ Set.univ`.
    Proof drops empty affine subspaces, then writes each non-empty `p` as a
    coset `b p +ᵥ p.direction` (basepoint chosen via `choose`), lifting the
    affine cover to an additive-coset cover;
    `AddSubgroup.exists_finiteIndex_of_leftCoset_cover` then produces a
    `p.direction` with finite index, contradicting infinite `V /
    p.direction` (`Module.Free.infinite k` over an infinite division ring
    with `Nontrivial`).
  - `AffineSubspace.affineSpan_ne_top_of_ncard_le_finrank`: for
    `[FiniteDimensional k V] [Nontrivial V]` and `s : Set V` finite with
    `s.ncard ≤ finrank k V`, `affineSpan k s ≠ ⊤`. Subsumes "a single point
    spans no more than itself" and "two points span at most a line" and
    generalizes to triples in dim 3, etc. — the natural ergonomic way to
    discharge the `⊤ ∉ s_cover` side-condition of the cover lemma when the
    cover is built from a small concrete set. Proof routes through
    `finrank_vectorSpan_image_finset_le` after a `Set.ncard ↔ toFinset.card`
    bridge.
- **Consumer side:** `exists_off_line_off_finite_dim_two` builds the cover
  `{affineSpan {pa, pb}} ∪ {affineSpan {s} | s ∈ S}` (line + finite
  singletons, all proper in dim 2), discharges the `⊤ ∉ s_cover`
  side-condition by two calls to `affineSpan_ne_top_of_ncard_le_finrank`
  (one with `Set.ncard_pair`, one with `Set.ncard_singleton`), applies the
  cover lemma, extracts a `q` outside, and converts off-line to `q - pa ∉
  ℝ ∙ (pb - pa)` followed by one `pair_add_smul_add_smul_iff` row-op.
  Parametric `pa + t • v` machinery is gone.
- **Scope note.** The sibling `exists_typeII_q_on_line_dim_two` (place `q`
  *on* the line) does **not** fit this approach — it's a one-parameter
  `Set.Finite.exists_notMem` in `ℝ`, not an affine-cover application — and
  stays as-is.
- **Status:** mirrored.
- **Mirror file:**
  `Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Cover.lean`. Parallels
  `Mathlib/GroupTheory/CosetCover.lean` but in the affine-space hierarchy:
  the new file imports `GroupTheory.CosetCover` for the underlying
  `AddSubgroup.exists_finiteIndex_of_leftCoset_cover` machinery and
  `AffineSpace.AffineSubspace.Basic` for the affine API. Putting the affine
  application here (rather than extending CosetCover) respects the
  current import direction (linear-algebra basics → affine-space) and
  keeps CosetCover's scope unchanged. The
  `affineSpan_ne_top_of_ncard_le_finrank` helper would naturally land
  upstream in `Mathlib/LinearAlgebra/AffineSpace/FiniteDimensional.lean`
  (alongside `finrank_vectorSpan_image_finset_le`); bundling here keeps
  the project mirror to a single file for now.

### [mirrored] `Set.exists_injective_fin_of_le_ncard` (Fin-indexing of subset elements)
- **Where it bit:** assembly step in `exists_affinelySpanning_rigid_placement`
  (`RigidityMatroid.lean`), the "pick `d + 1` distinct elements of `S` as
  `q : Fin (d + 1) → V`" sub-step; will recur in the upcoming sparsity lemma's
  "pick `d + 1` distinct elements of `s`" steps.
- **Friction:** mathlib's `Set.exists_subset_card_eq` returns a size-`n`
  subset `t ⊆ s` from `n ≤ s.ncard`. Promoting that to "an injective
  `q : Fin n → α` with each `q i ∈ s`" needed `Set.exists_subset_card_eq` →
  `Set.finite_of_ncard_ne_zero` / `Set.Finite.fintype` →
  `Set.ncard_eq_toFinset_card'` / `Set.toFinset_card` →
  `Fintype.equivFinOfCardEq` (~12 lines per call site).
- **Resolution:** mirrored as `Set.exists_injective_fin_of_le_ncard
  {s : Set α} {n : ℕ} (hns : n ≤ s.ncard) : ∃ q : Fin n → α,
  Function.Injective q ∧ ∀ i, q i ∈ s`. The 12-line construction collapses
  to one `obtain`. Internally uses the existing `Set.ncard_eq_card_coe`
  mirror to fold the two-step `ncard ↔ Fintype.card` rewrite to one lemma.
- **Status:** mirrored.
- **Mirror file:** `Mathlib/Data/Set/Card.lean`. Sits naturally alongside the
  existing `Set.exists_subset_card_eq`.

### [mirrored] `Polynomial.eval_det_X_add_C` (eval-at-scalar of `det (X • A.map C + B.map C)`)
- **Where it bit:** `exists_affinelySpanning_rigid_placement` in
  `RigidityMatroid.lean`, the `hP_eval` block bridging the polynomial-form
  bad-`t` set `{t | P.IsRoot t}` to the matrix-form bad-`t` set
  `{t | det (t • M₁ + M₀) = 0}`.
- **Friction:** mathlib's `Mathlib/LinearAlgebra/Matrix/Polynomial.lean`
  carries `natDegree_det_X_add_C_le`, `coeff_det_X_add_C_zero`, and
  `coeff_det_X_add_C_card` (degree and 0/card coefficients of the
  matrix-polynomial determinant `det (X • A.map C + B.map C) ∈ α[X]`) but no
  companion `eval`-at-scalar identity. The first pass went `RingHom.map_det`
  on `evalRingHom t` + `change` to massage the goal + `congr 1; ext i j` +
  nine-lemma `simp only` (~11 lines).
- **Resolution:** mirrored as
  `Polynomial.eval_det_X_add_C (A B : Matrix n n α) (t : α) :
    eval t (det ((X : α[X]) • A.map C + B.map C)) = (t • A + B).det`.
  Proof: rewrite `eval t = evalRingHom t`, apply `RingHom.map_det`, then
  `congr 1; ext i j; simp only [...]` over a focused set of `coe_evalRingHom`
  / `eval_*` / matrix-coordinate lemmas. `hP_eval` collapses to
  `fun t => by rw [hP_def, Polynomial.eval_det_X_add_C]`.
- **Status:** mirrored.
- **Mirror file:** `Mathlib/LinearAlgebra/Matrix/Polynomial.lean`. Sits
  naturally alongside the existing `coeff_*` and `natDegree_*` siblings.

### [mirrored] `Matrix.det_powerDifferences` (row-0-subtracted Vandermonde minor)
- **Where it bit:** Phase 6 task 4, the `d`-general lift of the
  affinely-spanning rigid placement. The perturbation along the
  moment-curve direction `w(v) = (φ v, (φ v)^2, …, (φ v)^d)` produces a
  perturbed difference matrix `M(t) = M_0 + t · M_1` whose
  `t^d`-coefficient is `det M_1`, where `M_1` is the `d × d` matrix
  with entries `(φ v_i)^(j+1) - (φ v_0)^(j+1)` (`i, j ∈ Fin d`). Showing
  `det M_1 ≠ 0` for injective `φ` is the deep step in turning the bad-`t`
  set into the root set of a degree-`d` polynomial.
- **Friction:** mathlib's `Matrix.det_vandermonde` factors the *full*
  `(d+1) × (d+1)` Vandermonde determinant as the symmetric product of
  differences `∏_{i<j} (v j - v i)`. The factorization of the *row-0-
  subtracted* `d × d` minor is the same product (by row reduction +
  cofactor expansion), but mathlib does not ship this identity directly:
  it's a one-step Laplace expansion away from
  `Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde` (which sees
  the sparse-row-0 form for free) but not packaged.
- **Resolution:** mirrored as
  - `Matrix.det_powerDifferences`: for `v : Fin (n + 1) → R` over a
    `CommRing`,
    `(Matrix.of (fun i j : Fin n => v i.succ ^ (j.val + 1) - v 0 ^ (j.val + 1))).det =
      ∏ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i, (v j - v i)`.
    `nontriviality R` discharges the trivial-ring case; the main proof
    instantiates the polynomial family `p 0 = 1`,
    `p k.succ = X^(k.val + 1) - C (v 0 ^ (k.val + 1))` and applies
    `Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde`, then
    cofactor-expands along the sparse row 0 via `det_succ_row_zero` +
    `Finset.sum_eq_single 0`.
- **Status:** mirrored.
- **Mirror file:** `Mathlib/LinearAlgebra/Vandermonde.lean`. Sits
  naturally alongside `det_vandermonde_sub` (the additive shift) — the
  multiplicative-style minor variant.

### [mirrored] `Pi.basisFun_dualBasis` and `LinearMap.range_dualMap_eq_span_image_dualBasis`
- **Where it bit:** `span_range_rigidityRow` in `RigidityMatroid.lean`,
  the constructive (span) form of row-rank-equals-column-rank for the
  rigidity matrix. The original proof rolled both lemmas inline: a
  pointwise `(Pi.basisFun ℝ G.edgeSet).dualBasis e = LinearMap.proj e`
  identification via `LinearMap.ext` + `simp [Pi.basisFun_repr]`, then
  a 4-rewrite chain (`Set.range_comp`, `Submodule.span_image`,
  `b.dualBasis.span_eq`, `Submodule.map_top`) for the span identity.
- **Friction:** both lemmas state genuinely general facts (no
  rigidity-specific content). `Module.Basis.dualBasis` and
  `LinearMap.dualMap` are mathlib-core, and the *dimension-level*
  version of the second fact already exists upstream as
  `LinearMap.finrank_range_dualMap_eq_finrank_range` — but the
  underlying span identity that *implies* it does not. The first
  lemma is missing because `Mathlib/LinearAlgebra/Dual/Basis.lean`
  does not even import `StdBasis.lean` (so there is no upstream
  file where the lemma could naturally live without a new import).
- **Resolution:** mirrored as
  - `Pi.basisFun_dualBasis` (`@[simp]`):
    `(Pi.basisFun R η).dualBasis i = LinearMap.proj i` for
    `[Finite η] [DecidableEq η]`. Two-line proof via `LinearMap.ext`
    + `simp [Pi.basisFun_repr]`.
  - `LinearMap.range_dualMap_eq_span_image_dualBasis` (Part 1 of
    Strang's Fundamental Theorem of Linear Algebra in span form):
    for any `b : Module.Basis ι R N` and `f : M →ₗ[R] N`,
    `LinearMap.range f.dualMap =
       Submodule.span R (Set.range (f.dualMap ∘ b.dualBasis))`.
    One-line proof via `Set.range_comp` + `Submodule.span_image` +
    `Basis.dualBasis.span_eq` + `Submodule.map_top`.

  `span_range_rigidityRow` now consumes the second lemma directly;
  its proof body is ~4 lines.
- **Status:** mirrored.
- **Mirror file:** `Mathlib/LinearAlgebra/Dual/Basis.lean` (with an
  added `import Mathlib.LinearAlgebra.StdBasis` line; upstream PR
  would either add that import to `Dual/Basis.lean` or split
  `Pi.basisFun_dualBasis` to `StdBasis.lean`).

### [mirrored] `Sym2.notMem_map_some` and `Sym2.disjoint_image_map_some`
- **Where it bit:** `typeI_edgeSet_ncard`, `typeII_edgeSet_ncard`,
  `typeI_isLaman` (`h_disj`), `typeII_isLaman` (`h_disj`) — four
  disjointness obligations of the shape
  `Disjoint (Sym2.map some '' S) ({s(none, some _), …} : Set _)`
  (or its `T`/`T'` intersection variant inside `_isLaman`). Each was a
  3–4 line `rw [Set.disjoint_left]; rintro e he hpair; rcases hpair
  with rfl | …; simp at he` block.
- **Friction:** mathlib has `Sym2.mem_map` but no specialization for
  `none ∉ Sym2.map some e`, and no packaged disjointness lemma for
  the recurring "image vs Option-fresh-edges" pattern. The four call
  sites were fundamentally proving the same fact — every element of
  `Sym2.map some '' S` has both endpoints in the `some` branch, so it
  cannot equal a fresh edge containing `none` — but each call site
  re-derived this from `simp at he` after rcases.
- **Resolution:** mirrored as
  - `Sym2.notMem_map_some` (`@[simp]`): `none ∉ Sym2.map some e`.
  - `Sym2.disjoint_image_map_some`: `(∀ e ∈ T, none ∈ e) →
    Disjoint (Sym2.map some '' S) T`.

  Both `_edgeSet_ncard` lemmas now state `hDisj`'s type explicitly
  and consume it via the helper as a one-line term-mode application;
  the `_isLaman` `h_disj` blocks (where `T`/`T'` is `set`-bound and
  the type can be inferred) collapse to one or two lines via
  `Sym2.disjoint_image_map_some fun _ ⟨hpair, _⟩ => by rcases hpair
  …; simp`. Net ~7 lines across the four sites.
- **Status:** mirrored.
- **Mirror file:** `Mathlib/Data/Sym/Sym2.lean`.

### [mirrored] `Finset.card_eraseNone_add_one_of_mem` (addition-form `eraseNone` cardinality)
- **Where it bit:** `typeI_isLaman` and `typeII_isLaman` sparsity, the
  `none ∈ s` branch's `s.card = s'.card + 1` derivation. Each occurrence
  was a 4-line `hni; hs_eq; hsc` block (`hni : none ∉ s'.image some`,
  rebuild `s = insert none (s'.image some)` by `ext; cases x`, then
  `rw [hs_eq, card_insert_of_notMem, card_image_of_injective]`).
- **Friction:** the project was using `s.preimage some _` for the
  some-preimage. Mathlib's `Finset.eraseNone` is the better-named
  computable companion and ships exactly the API needed
  (`mem_eraseNone`, `coe_eraseNone`, `card_eraseNone_of_not_mem`),
  except the `none ∈ s` cardinality lemma is in `ℕ`-subtraction form
  (`#s.eraseNone = #s - 1`). The project's coding convention forbids
  `ℕ`-subtraction, so consumers had to `Nat.sub_add_cancel` it back
  manually. Switched both `_isLaman` proofs to `s.eraseNone` and
  added the addition-form companion as a one-line mirror.
- **Resolution:** mirrored as `Finset.card_eraseNone_add_one_of_mem`
  (`#s.eraseNone + 1 = #s` under `none ∈ s`). Both `_isLaman` proofs
  collapsed each `none ∈ s` and `none ∉ s` `hsc` derivation to one
  line. Net ~9 lines saved in `typeI_isLaman`, ~18 lines in
  `typeII_isLaman`. The `Finset.Preimage` import was dropped in
  favour of `Finset.Option`. Follow-up cleanup: the three private
  `fresh_sym2_*` helpers were taking a generic `s' : Finset V` plus
  `hmem : ∀ v, v ∈ s' ↔ some v ∈ s` to abstract over which
  some-preimage was being used; with `eraseNone` standardised across
  callers, those parameters were dropped, the helpers now state their
  hypotheses directly against `s.eraseNone`, and call sites no longer
  pass `hmem`.
- **Status:** mirrored.
- **Mirror file:** `Mathlib/Data/Finset/Option.lean`.

### [mirrored] `Set.ncard_pair_le` / `Set.ncard_triple_le` (unconditional pair / triple bounds)
- **Where it bit:** `typeI_edgeSet_ncard`, `typeII_edgeSet_ncard`,
  `typeI_isLaman` (`hT_le_2`), `typeII_isLaman` (`hT'_le_3`,
  `hT'_le_2` ×2).
- **Friction:** mathlib has `Set.ncard_pair` (`= 2` under `a ≠ b`)
  but no unconditional `≤ 2` companion. Bounding the cardinality of
  a literal pair/triple of new edges expanded to 3- and 5-line calc
  chains via `Set.ncard_insert_le` + `Set.ncard_singleton`, repeated
  five times across the file (the same 5-line block for each
  `T ⊆ {…, …}` sub-bound).
- **Resolution:** mirrored unconditional `≤` bounds. Each calc
  chain collapses to one `Set.ncard_pair_le _ _` (resp.
  `Set.ncard_triple_le _ _ _`) application.
- **Status:** mirrored.
- **Mirror file:** `Mathlib/Data/Set/Card.lean`.

### [mirrored] `Set.ncard_eq_card_coe` (`Set.ncard ↔ Fintype.card` bridge)
- **Where it bit:** `rigidityMap_finrank_range_le` in `Framework.lean`,
  the final calc step `_ = G.edgeSet.ncard := by rw
  [Set.ncard_eq_toFinset_card', Set.toFinset_card]`.
- **Friction:** mathlib has `Set.ncard_eq_toFinset_card'` (`s.ncard =
  s.toFinset.card`) and `Set.toFinset_card` (`s.toFinset.card =
  Fintype.card s`) but no fused composite. Same shape as the existing
  [mirrored] `ncard_incidenceSet_eq_degree` (Phase 2). Filed
  pre-emptively at Phase 4 close because Phase 5 lemmas bridging
  `LinearMap.toMatrix` / `Module.finrank_pi` (Fintype-based) with the
  project's `edgeSet.ncard` rhetoric will hit it again.
- **Resolution:** mirrored as `Set.ncard_eq_card_coe : s.ncard =
  Fintype.card s` (under `[Fintype s]`); one-line proof via the
  existing two-step composition. The calc step in
  `rigidityMap_finrank_range_le` collapses to
  `(Set.ncard_eq_card_coe _).symm` (term mode). Also retroactively
  applied to the existing `ncard_incidenceSet_eq_degree` mirror, whose
  proof was the same shape routed through `Nat.card` (`rw [←
  Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
  card_incidenceSet_eq_degree]` → `rw [Set.ncard_eq_card_coe,
  card_incidenceSet_eq_degree]`); this is a mirror-importing-mirror
  edge, fine because the upstream `Mathlib/Combinatorics/SimpleGraph/
  Finite.lean` already imports `Mathlib/Data/Set/Card.lean`.
- **Status:** mirrored.
- **Mirror file:** `Mathlib/Data/Set/Card.lean`.

### [mirrored] `Sym2.map_some_injective` (named specialization)
- **Where it bit:** `typeI_edgeSet_ncard`, `typeII_edgeSet_ncard`,
  `typeI_isLaman`, `typeII_isLaman` — every `Set.ncard_image_of_injective`
  application on a `Sym2.map some` image.
- **Friction:** the same four-token incantation
  `Sym2.map.injective (Option.some_injective V)` was written four
  times. It correctly typechecks but is harder to read than the
  intent ("`Sym2.map some` is injective").
- **Status:** mirrored as `Sym2.map_some_injective`.
- **Mirror file:** `Mathlib/Data/Sym/Sym2.lean`.

### [mirrored] `Sym2.exists_and_map_eq_mk_iff` (Sym2 image-membership case analysis)
- **Where it bit:** `typeI_edgeSet` (Phase 3); aborted attempt at
  `typeII_edgeSet`.
- **Friction:** Proving things of the form
  `(typeI G a b).edgeSet = (Sym2.map some '' G.edgeSet) ∪ {s(none, some a), s(none, some b)}`
  required `Sym2.ind` to expose the underlying pair `(x, y)`, then a
  4-way case analysis `rcases x with _ | u <;> rcases y with _ | v`,
  each branch closed by mixed `Sym2.eq_iff` / `Option.some.injEq` /
  `Sym2.map_mk` rewrites and `simp_all`. `aesop`, `tauto`, and bare
  `simp` each got stuck on a different sub-goal.
- **Resolution:** The right shape was a *predicate-form* simp lemma:
  `(∃ e, P e ∧ Sym2.map f e = s(x, y)) ↔ ∃ p q, f p = x ∧ f q = y ∧ P s(p, q)`.
  This is what `simp` reaches after `Set.mem_image` (a `@[simp]` lemma)
  has fired, and after any further unfolding of `e ∈ S` (e.g.
  `Set.mem_diff` for set differences), so the predicate `P` is whatever
  conjunction those unfoldings produce. The earlier sketches (e.g.
  `Sym2.map_some_mem_iff` for the `e = Sym2.map f e'` shape) didn't
  match the simp normal form and so wouldn't fire.

  With the predicate-form lemma tagged `@[simp]`, both
  `typeI_edgeSet` and `typeII_edgeSet` close in three lines:
  `ext e; induction e with | h x y => ?_; rcases x with _ | u <;>
  rcases y with _ | v <;> simp`. The companion non-`simp`
  `Sym2.mk_mem_image_map_iff` for the pre-`Set.mem_image` shape is
  also provided, alongside `f = some` specializations.
- **Status:** mirrored.
- **Mirror file:** `Mathlib/Data/Sym/Sym2.lean`.

### [mirrored] `(G.incidenceSet v).ncard = G.degree v`
- **Where it bit:** `IsLaman.two_le_degree` (Phase 2).
- **Friction:** mathlib has `card_incidenceSet_eq_degree` for
  `Fintype.card`, not for `Set.ncard`. We chained
  `← Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
  card_incidenceSet_eq_degree` every time we needed it.
- **Status:** mirrored as `SimpleGraph.ncard_incidenceSet_eq_degree`.
- **Mirror file:** `Mathlib/Combinatorics/SimpleGraph/Finite.lean`.

### [mirrored] `G.edgeSet.ncard = G.edgeFinset.card`
- **Where it bit:** `IsLaman.exists_degree_le_three` and
  `top_fin_two_isLaman` (Phase 1 + 2).
- **Friction:** trivial composite of `← Set.ncard_coe_finset` and
  `coe_edgeFinset`, but written out by hand each time.
- **Status:** mirrored as `SimpleGraph.ncard_edgeSet_eq_card_edgeFinset`.
- **Mirror file:** `Mathlib/Combinatorics/SimpleGraph/Finite.lean`.

### [mirrored] `(⊤ : SimpleGraph V).edgeSet.ncard = (Fintype.card V).choose 2`
- **Where it bit:** `top_fin_two_isLaman`.
- **Friction:** mathlib's `card_edgeFinset_top_eq_card_choose_two` is
  in `Finset.card` form; the `Set.ncard` companion was missing.
- **Status:** mirrored as `SimpleGraph.ncard_edgeSet_top_eq_card_choose_two`.
- **Mirror file:** `Mathlib/Combinatorics/SimpleGraph/Finite.lean`.

### [mirrored] `Finset.coe_compl_singleton`
- **Where it bit:** `IsLaman.two_le_degree`.
- **Friction:** singleton complement coercion is the standard
  "delete one vertex" idiom, but you have to compose
  `Finset.coe_compl` and `Finset.coe_singleton` by hand.
- **Status:** mirrored.
- **Mirror file:** `Mathlib/Data/Finset/BooleanAlgebra.lean`.

### [mirrored] `Finset.card_compl_singleton`
- **Where it bit:** `IsLaman.two_le_degree`.
- **Friction:** as above for the cardinality side.
- **Status:** mirrored.
- **Mirror file:** `Mathlib/Data/Fintype/Card.lean`.
  (Sibling of `coe_compl_singleton` but lands in a different upstream
  file because `Finset.card_compl` requires `Fintype α` and lives in
  `Fintype/Card.lean`, not `Finset/BooleanAlgebra.lean`.)

### [mirrored] `Finset.eq_singleton_of_mem_of_card_le_one`
- **Where it bit:** `contradiction_two_pair` and `contradiction_three_pair`
  in `Henneberg.lean` (Phase 5 milestone-1 blocker proofs); second cleanup
  pass.
- **Friction:** the `Finset.eq_of_subset_of_card_le
  (Finset.singleton_subset_iff.mpr _) (by rw [Finset.card_singleton]; omega) |>.symm`
  pattern recurs 4 times. The natural reading is "I have a member and a
  ≤ 1 cardinality bound, give me the singleton equality" — but spelled out
  it's a 3-line block per use.
- **Status:** mirrored. Each call site now reads
  `Finset.eq_singleton_of_mem_of_card_le_one hmem (by omega)`.
- **Mirror file:** `Mathlib/Data/Finset/Card.lean`.

### [mirrored] `LinearIndependent.dualMap_of_surjective` / `LinearIndepOn.dualMap_of_surjective`
- **Where it bit:** `typeI_edgeSetRowIndependent_extend`
  (`MatroidIdentification.lean`, Phase 7). The blueprint claims a one-step
  "factor through the restriction map" for old-row LI: linear independence
  of `G'.rigidityRow p'` transports through `restrictMap.dualMap` (where
  `restrictMap = LinearMap.funLeft ℝ _ some`) to linear independence of
  the lifted `(typeI G' a b).rigidityRow p_ext ∘ lift_some`. The original
  Lean expanded this into a four-step chain: `LinearMap.funLeft_surjective_of_injective` →
  `LinearMap.dualMap_injective_of_surjective` → `LinearMap.ker_eq_bot.mpr` →
  `LinearIndependent.map'`. Phase 7's forthcoming Type II row-LI lift will
  hit the same chain.
- **Friction:** mathlib has each link (`dualMap_injective_of_surjective`
  in `Dual/Defs.lean`, `LinearIndependent.map'` in `LinearIndependent/Basic.lean`)
  but no fused `LinearIndependent.dualMap_of_surjective`. The
  `LinearIndepOn`-level companion is also absent.
  The companion big→small direction in `isSparse_of_edgeSetRowIndependent_dim_two`
  (`RigidityMatroid.lean`) uses `LinearIndependent.of_comp restrict.dualMap`
  with no surjectivity hypothesis — already a one-liner upstream, so it
  did not benefit from the new helper.
- **Resolution:** mirrored as
  - `LinearIndependent.dualMap_of_surjective`: `Surjective f → LI v → LI (f.dualMap ∘ v)`.
  - `LinearIndepOn.dualMap_of_surjective`: the `LinearIndepOn` companion.

  The Phase 7 caller collapsed the four-step chain to one
  `h_li_G'.dualMap_of_surjective h_restrict_surj` application; the
  intermediate `h_dualMap_inj` and `with hRest_def` bindings dropped.
- **Status:** mirrored.
- **Mirror file:** `Mathlib/LinearAlgebra/Dual/Lemmas.lean` (with an
  added `import Mathlib.LinearAlgebra.LinearIndependent.Basic` line;
  upstream would slot under existing surjective-dual API in that file).

## Archived: Resolved (project-internal)

The body of this section was moved to
[`FRICTION-archive.md`](FRICTION-archive.md) in a post-Phase-6
housekeeping pass. Each archived entry's resolution is indexed
elsewhere — as a named mirror lemma under
`CombinatorialRigidity/Mathlib/`, a named project-internal helper,
or a `**Lifted to:** TACTICS-GOLF § X` / `TACTICS-QUIRKS § X`
cross-reference — so the archive
is a search target, not a read-on-load file.

Grep the archive when investigating how a specific past friction
was handled; reach for the indexed resolution (via
`lean_local_search` or TACTICS-GOLF / TACTICS-QUIRKS) for normal
mid-proof discovery.
