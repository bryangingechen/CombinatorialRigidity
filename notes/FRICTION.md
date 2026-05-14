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
> in `TACTICS.md` instead, which is the project's tactical reference.
> Don't bury a general rule in a `[resolved]` entry here; it won't be
> found again.

## How this file is used

- After landing a phase, review what proofs felt awkward. Did you
  reach for the same glue lemma three times? Did `grind` need an
  unusually long hint list? File an entry — and if the lesson is
  cross-cutting, lift it into `TACTICS.md` instead.
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
- [Resolved (project-internal)](#resolved-project-internal) — design
  history: friction we resolved in-project (helper extraction,
  refactor, simp-set tweak). No further action; preserved for context.

**Filing rule for new entries.** Pick by what the *next agent* would
do with it: open if you'd act on it; anti-pattern if you wouldn't but
want to warn future agents; mirrored if you mirrored an upstream
lemma; resolved otherwise.

## Open

### [open] typeII reverse Henneberg move: Laman preservation requires a non-trivial choice
- **Where it bit:** Phase 3 close, while planning
  `IsLaman.exists_typeI_or_typeII_reverse`.
- **Friction:** The Phase-3-start hand-off identified "find non-adjacent
  neighbors among the three degree-3 neighbors" as the tricky piece.
  That part is straightforward (sparsity at `{v, a, b, c}` ⇒ ≤ 2 edges
  among `{a, b, c}` ⇒ a non-adjacent pair exists; see
  `IsLaman.exists_nonadj_among_three_neighbors`). The genuinely hard
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
- **Proposed fix:** Phase 3 ships the iso-only half
  (`IsLaman.exists_typeI_or_typeII_iso`); the
  Laman-preservation half is deferred to Phase 5 and may either be
  proved directly (Henneberg blocker) or bypassed via the rigidity
  matroid (see ROADMAP §5 *Carryover from Phase 3*).
- **Status:** open (Phase-5-bound).

### [open] No packaged `ℝ`-linear injection `Module.Dual ℝ M →ₗ[ℝ] (M → ℝ)`
- **Where it bit:** `edgeSetRowIndependent_iff_linearIndepOn_rigidityRow`
  in `RigidityMatroid.lean`. We needed to bridge `LinearIndepOn` of a
  family in `(Framework V d → ℝ)` (the blueprint's set-of-functions
  formulation of `EdgeSetRowIndependent`) with `LinearIndepOn` of the
  same family viewed in `Module.Dual ℝ (Framework V d)` (where
  `LinearMap.dualMap` rank identities apply).
- **Friction:** mathlib has `LinearMap.linearIndepOn_iff_of_injOn`
  shaped around an `ℝ`-linear `f : M →ₗ[ℝ] M'`. The "forget linearity"
  map `(M →ₗ[ℝ] ℝ) → (M → ℝ)` is `FunLike.coe`; it preserves `+` and
  `•` definitionally, and is injective by `LinearMap.ext`. But mathlib
  doesn't ship it packaged as a `LinearMap`, so the LI-transfer lemma
  doesn't apply directly. We unblocked by introducing a `private
  noncomputable def dualToFunₗ` with body `⟨⇑·, rfl, rfl⟩` (4 lines)
  plus a `dualToFunₗ_injective` helper.
- **Proposed fix:** mirror as
  `Module.Dual.toLinearMap : Module.Dual R M →ₗ[R] (M → R)` (4 lines)
  under `CombinatorialRigidity/Mathlib/LinearAlgebra/Dual/Defs.lean`,
  matching the existing `Module.Dual` namespace, and PR upstream.
  Sidesteps re-deriving the helper if the Phase 6 sparsity-side proof
  also needs the bridge.
- **Status:** open. Acceptable as a private helper for now; lift if
  Phase 6's $(2,3)$-sparsity-from-row-independence (the next
  substantive lemma) needs the bridge a second time.

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

### [wontfix] `omega` treats `set`-aliased terms as opaque atoms
- **Where it bit:** `IsLaman.typeII_reverse_blocker` in `Henneberg.lean`
  (Phase 5 milestone 1, typeII blocker).
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
  downstream files a smaller load surface (current beneficiary:
  `LamanTheorem.lean` only); (b) move the analysis-heavy half of
  `Framework.lean` behind a thinner facade so combinatorial files
  (`Sparsity.lean`, `Laman.lean`, `Henneberg.lean`) don't import the
  finite-dimension normed-module machinery transitively. Defer to
  Phase 6 once more downstream files exist to amortize the cost.
- **Status:** wontfix at the current scope; structural change is a
  Phase 6+ decision. Phase 5 third cleanup pass (`notes/Phase5.md`)
  records the per-candidate experiments and what trended where.

## Mirrored

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

## Resolved (project-internal)

### [resolved] Dot notation inside a `Foo.bar`-named theorem resolves to itself, not the parent's `Foo.bar`
- **Where it bit:** `EdgeSetRowIndependent.mono` in `RigidityMatroid.lean`
  (Phase 6).
- **Friction:** wrote `hI.mono h` inside the body of
  `theorem EdgeSetRowIndependent.mono`, intending it to dispatch to
  `LinearIndepOn.mono` via dot notation on `hI`'s unfolded type. Lean
  resolved `.mono` to the function being defined instead (Lean's dot
  notation prefers the head namespace of the term's *stated* type
  before unfolding), turning the body into a recursive call with no
  decreasing argument. Build failed with "well-founded recursion
  cannot be used".
- **Resolution:** spell out the upstream name —
  `LinearIndepOn.mono hI h` — when the wrapper theorem shares a basename
  with the upstream lemma it's calling. Dot notation works fine for
  *other* theorems calling `hI.mono`; the trap is only inside
  `EdgeSetRowIndependent.mono` itself.
- **Status:** resolved (Lean idiom — when wrapping an upstream lemma
  under your own type's namespace, dot-notation inside the wrapper
  recurses; call the upstream name explicitly).

### [resolved] `Exists.imp` doesn't transport across changing-binder-type existentials
- **Where it bit:** `IsGenericallyRigid.iso` in `Framework.lean` (Phase 5 milestone 0).
- **Friction:** tried `h.imp fun _ => IsInfinitesimallyRigid.iso φ`,
  paralleling `IsGenericallyRigid.mono`'s `h.imp fun _ => IsInfinitesimallyRigid.mono h`.
  Failed with a deterministic-isDefEq timeout. Cause: `IsGenericallyRigid` on
  `G : SimpleGraph V` is `∃ p : Framework V d, …`, whereas on `H : SimpleGraph W`
  it's `∃ p : Framework W d, …` — different binder types. `Exists.imp` only
  works when the binder type is preserved (`mono` keeps `V`; `iso` doesn't).
  The elaborator burned heartbeats trying to unify the binder types.
- **Resolution:** use explicit `obtain`+`exact` for the iso form:
  `obtain ⟨p, hp⟩ := h; exact ⟨p ∘ φ.symm, hp.iso φ⟩`. Compiles instantly.
- **Status:** resolved (Lean idiom, not a missing lemma — `Exists.imp`'s
  signature is correct).

### [resolved] `rw [LinearMap.mem_ker]` fails on `SetLike`-coerced membership after `Submodule.mem_map` destructure
- **Where it bit:** first-pass `IsInfinitesimallyRigid.iso` proof in `Framework.lean`,
  using `Submodule.map Φ.toLinearMap` to relate the two kernels.
- **Friction:** after `rintro _ ⟨q', hq', rfl⟩` from `(ker H).map Φ ≤ ker G`,
  the destructured `hq'` had type `q' ∈ ↑(H.RigidityMap (p ∘ φ.symm)).ker`
  (with the SetLike `↑` coercion). `rw [LinearMap.mem_ker] at hq'` failed to
  find a match because the lemma's LHS is `q' ∈ LinearMap.ker f` without the
  `↑`. The two membership forms are defeq but `rw` insists on syntactic match.
- **Resolution:** abandoned the `Submodule.map` route in favour of constructing
  the kernel iso directly as a `LinearEquiv` between the two subtype-`Sort`s
  `LinearMap.ker (H.RigidityMap (p ∘ φ.symm))` and `LinearMap.ker (G.RigidityMap p)`.
  In that form, the membership obligations are field-typed (`q'.2 : q'.1 ∈ ker …`)
  and `LinearMap.mem_ker.mp q'.2` / `.mpr` work directly. Saves the membership-
  form bridging entirely, and `kerEquiv.finrank_eq` closes the bound.
- **Status:** resolved (no missing lemma — `rw` not seeing through the
  SetLike coercion is intrinsic; the project-internal idiom is "build the
  kernel iso directly when transporting `IsInfinitesimallyRigid` across an
  iso, instead of going via `Submodule.map`").

### [resolved] `RigidityMap` defined by hand instead of compositionally
- **Where it bit:** `Framework.lean`, the original `RigidityMap`
  definition (`def RigidityMap … where toFun … map_add' … map_smul' …`)
  and the K₂ worked example (`top_fin_two_isGenericallyRigid`).
- **Friction:** `RigidityMap G p : Framework V d →ₗ[ℝ] (G.edgeSet → ℝ)`
  was built by hand. `toFun p' e := Sym2.lift ⟨…, symm_proof⟩ e.val`,
  plus explicit `map_add'` and `map_smul'` proofs. The symmetry
  obligation for `Sym2.lift ⟨fun u v => f u v, _⟩` arrived in the
  un-reduced form `(fun u v => f u v) u v = (fun u v => f u v) v u`, so
  each linearity proof needed a `change` to beta-reduce the lambda
  before `rw`'s pattern match could fire — three
  `change`-then-`rw`-then-`abel`/`inner_smul_right` chains, ~25 lines
  total. The K₂ inner-product computation `⟪0 - e₀, e₀ - 0⟫_ℝ = -1`
  also required a `change` line plus a four-step
  `rw [zero_sub, sub_zero, inner_neg_left, EuclideanSpace.inner_single_right]`
  chain.
- **Resolution:** rebuilt compositionally via three private helpers
  before `RigidityMap`:
  - `edgeRow p u v : Framework V d →ₗ[ℝ] ℝ` —
    `((innerSL ℝ (p u - p v)).toLinearMap).comp
      ((LinearMap.proj u : Framework V d →ₗ[ℝ] EuclideanSpace ℝ (Fin d))
        - LinearMap.proj v)`. The `LinearMap.proj u` arm needs an
    explicit codomain ascription (Pi-codomain isn't inferred from the
    surrounding `LinearMap.comp`); see the next entry.
  - `edgeRow_apply` — `edgeRow p u v x = ⟪p u - p v, x u - x v⟫_ℝ`.
    Closes by `rfl` (compositional definition reduces directly through
    `LinearMap.comp_apply`, `LinearMap.sub_apply`, `LinearMap.proj_apply`,
    and the `innerSL` coercion). `simp [edgeRow]` *does not* work
    because it triggers `inner_sub_left` and over-distributes the LHS
    past the goal's normal form.
  - `edgeRow_symm` — three-line `LinearMap.ext` + the original
    `← neg_sub`-twice + `inner_neg_neg` argument.

  `RigidityMap` is then a one-liner: `LinearMap.pi fun e : G.edgeSet =>
  Sym2.lift ⟨edgeRow p, edgeRow_symm p⟩ e.val`. Linearity comes free
  from `LinearMap.pi`. `rigidityMap_apply` closes by `simp [RigidityMap]`
  (one line; the underlying `LinearMap.pi_apply` and `Sym2.lift_mk` are
  both `@[simp]`). The K₂ `h_val` block collapses from a 5-line
  `rw [rigidityMap_apply]; change …; rw [zero_sub, sub_zero,
  inner_neg_left, EuclideanSpace.inner_single_right]; simp` to one
  `simp [rigidityMap_apply, hp_def, inner_neg_left]` line —
  `EuclideanSpace.inner_single_right` is no longer needed (simp's
  default set with the framework now in compositional form closes the
  inner product directly).

  Net: ~26 lines of `RigidityMap` definition + linearity proofs → 16
  lines (4 `edgeRow*` helpers + 4-line `RigidityMap` def + 4-line
  `rigidityMap_apply`). K₂ `h_val`: 5 lines → 1.
- **Status:** resolved (project-internal — `RigidityMap` doesn't exist
  upstream, so no mirror; the constituents `innerSL`, `LinearMap.proj`,
  `LinearMap.pi`, `Sym2.lift` all sit upstream).

### [resolved] `LinearMap.proj` Pi-codomain not inferred in subtraction context
- **Where it bit:** `Framework.lean`, building `edgeRow` (the
  compositional `RigidityMap` refactor above).
- **Friction:** writing `(LinearMap.proj u - LinearMap.proj v) :
  Framework V d →ₗ[ℝ] EuclideanSpace ℝ (Fin d)` as a binary subtraction
  with the type ascription on the *whole* expression failed elaboration
  — `typeclass instance problem is stuck: (i : V) → Module ?m (?m i)`.
  The Pi-codomain `φ : V → Type _` of `LinearMap.proj` doesn't get
  pinned down by the outer ascription on the subtraction. Per-leaf
  ascription on the *first* `proj` (`(LinearMap.proj u : Framework V d
  →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) - LinearMap.proj v`) is enough — the
  second proj's type is inferred from the `Sub` instance.
- **Resolution:** ascribe the first `LinearMap.proj` explicitly. Build
  cycle was 1: outer ascription failed → per-leaf ascription on the
  first arg succeeded.
- **Status:** resolved (no missing lemma; ascription idiom). Specific
  enough to `LinearMap.proj`-construction proofs that it stays in
  FRICTION rather than promoting to TACTICS.

### [resolved] `mem_edgesIn.mpr` boilerplate at literal-pair edges
- **Where it bit:** `no_isTightOn_excluding_three_neighbors`,
  `contradiction_one_pair`, `contradiction_two_pair`, `typeII_isLaman`
  (the `s(a, b) ∈ G.edgesIn ↑s'` reconstruction in the `h_or` proof)
  in `Henneberg.lean`. Each call site wrote
  `mem_edgesIn.mpr ⟨h_adj, by rw [Sym2.coe_mk]; exact
  Set.insert_subset_iff.mpr ⟨hx, Set.singleton_subset_iff.mpr hy⟩⟩`
  or a multi-line `refine ⟨h_adj, ?_⟩; rw [Sym2.coe_mk]; exact …`
  expansion — same shape every time.
- **Resolution:** added `SimpleGraph.mk_mem_edgesIn` to
  `EdgesIn.lean`: `(h : G.Adj x y) (hx : x ∈ s) (hy : y ∈ s) : s(x, y)
  ∈ G.edgesIn s`. Six call sites collapsed to one-liners. Net
  file-size win; more importantly the milestone-1 blocker proofs read
  considerably cleaner.
- **Status:** resolved (project-internal — `edgesIn` is project-local,
  so no upstream mirror).

### [resolved] Identical helpers for milestone-2 proof shape (`Option.elim` injectivity, span-singleton non-member)
- **Where it bit:** `typeI_isGenericallyRigidInj_two` /
  `typeII_isGenericallyRigidInj_two_of_nonCollinear` (4-way `rintro
  (_ | u) (_ | v) h` injectivity proof) and
  `exists_off_line_off_finite_dim_two` /
  `exists_nonCollinear_rigid_placement_dim_two` (the
  `finrank_span_singleton` / `finrank_top` / `omega` chain showing
  `Submodule.span ℝ {v} ≠ ⊤` so `SetLike.exists_not_mem_of_ne_top`
  fires).
- **Resolution:** added two private helpers at the top of
  `HennebergRigidity.lean`:
  - `injective_option_elim`: the `Option`-extended `fun w => w.elim q p`
    is injective when `p` is injective and `q ∉ Set.range p`. Pure
    `Option`/`Function.Injective` fact, dim-agnostic.
  - `exists_not_mem_span_singleton_dim_two`: in `EuclideanSpace ℝ
    (Fin 2)`, every `Submodule.span ℝ {v}` with `v ≠ 0` is proper.
    Dim-2-specific.
- **Status:** resolved (project-internal; both helpers are small and
  not obvious upstream candidates without a slightly more general
  framing).

### [resolved] Per-move `_edgesIn_ncard_decomp` extraction
- **Where it bit:** `typeI_isLaman` and `typeII_isLaman` sparsity
  branches in `Henneberg.lean`. Each opened with ~14 lines of
  `h_decomp` / `h_disj` / `h_ncard` plumbing (Sym2 case-split
  establishing the union decomposition, disjointness of the two
  summands, cardinality identity from the disjoint union) before the
  proof's actual math case-split (`none ∈ s` × `s'.card` cases) could
  begin.
- **Friction:** the original Phase 3 decision was *not* to factor (see
  Phase3.md "Inline the `edgesIn` decomposition in each `_isLaman`
  proof"). The reasoning was that the two shapes differ in `T`'s size
  (2 vs 3 fresh edges) and the typeII `\ {s(a, b)}` deletion, so a
  single shared helper wasn't natural. After the `eraseNone` refactor
  cleaned up the surrounding `set s'` / `hcoe` plumbing, the residual
  duplication stood out and the cost-benefit flipped: each helper is
  called exactly once, but expressing the cardinality identity up
  front lets each `_isLaman` sparsity branch lead with its math
  case-split.
- **Resolution:** extracted two private helpers in `Henneberg.lean`,
  each placed between the corresponding `_edgeSet_ncard` and
  `_isLaman`:
  - `typeI_edgesIn_ncard_decomp (G : SimpleGraph V) (a b : V) (s : Finset (Option V))`:
    `((typeI G a b).edgesIn ↑s).ncard = (G.edgesIn ↑s.eraseNone).ncard + (({s(none, some a), s(none, some b)} ∩ (↑s).sym2)).ncard`.
  - `typeII_edgesIn_ncard_decomp` analogue with `\ {s(a, b)}` on the
    first summand and the three-element fresh-edge set on the second.

  Both helpers take `[Finite V]` (needed for the `Set.ncard_union_eq`
  autoparam). The sparsity branches collapsed from ~22 lines of
  plumbing each to ~9 lines (`set s'`, `set T`, `h_ncard` via helper,
  `hT_le_*` bound), after which the math case-split leads. Net file
  size grew slightly (helpers are longer than the inlined uses), but
  the two `_isLaman` proofs read substantially cleaner.
- **Status:** resolved (project-internal — `typeI`/`typeII` don't
  exist upstream, so no mirror).

### [resolved] Lifting subtype-Sym2 equality to underlying-value equality
- **Where it bit:** `typeII_iso_of_three_neighbors` `(some, some)` arm.
- **Friction:** The arm needs to reject `s(⟨u, _⟩, ⟨w, _⟩) = s(⟨a, _⟩,
  ⟨b, _⟩)` (an equality of `Sym2 (Subtype _)`) by reducing to `s(u, w) =
  s(a, b)` (`Sym2 V`) and contradicting `¬G.Adj a b`. The original proof
  chained `rw [Sym2.eq_iff] at heq; rcases heq with ⟨h1, h2⟩ | …; rw
  [Subtype.mk.injEq] at h1 h2; subst h1; subst h2; …` per disjunct —
  ~6 lines of bookkeeping per arm.
- **Resolution:** lift the Sym2 equality through `Sym2.map Subtype.val`
  in one step: `have : s(u, w) = s(a, b) := by simpa using congrArg
  (Sym2.map Subtype.val) heq`. The downstream `rcases Sym2.eq_iff.mp …`
  then case-splits the V-level equality with `⟨rfl, rfl⟩ | ⟨rfl, rfl⟩`
  patterns directly. The `simpa` collapses `Sym2.map Subtype.val
  s(⟨u, _⟩, ⟨w, _⟩)` to `s(u, w)` via `Sym2.map_mk` + `Subtype.coe_mk`.
- **Status:** resolved (project-internal idiom; no upstream lemma is
  missing). Recorded in TACTICS.md § 5.

### [resolved] Recurring duplication across the two `_isLaman` proofs
- **Where it bit:** `typeI_isLaman` and `typeII_isLaman` sparsity case
  analysis — both moves had a `s'.card = 1` sub-case proving `T ⊆
  {s(none, some w)}` by 6–8 lines of explicit Sym2 subset+`Finset.mem_singleton`
  reasoning, and a `none ∉ s` case proving `T.ncard = 0` by another
  6–7 lines of `Set.ncard_eq_zero` + per-edge case analysis. The
  four blocks were textually different (different number of fresh
  edges) but logically identical.
- **Resolution:** extracted two private helpers in `Henneberg.lean`
  (next to the `instDecidable*Adj` instances):
  `fresh_sym2_subset_singleton` and
  `fresh_sym2_ncard_eq_zero_of_none_notMem`. Both abstract over the
  fresh-edge enumeration via `xs : Set (Sym2 (Option V))` plus a
  one-line per-element predicate. Each of the four call sites
  collapses to a 2-line invocation. Phase 3 cleanup pass.
- **Status:** resolved (project-internal — these only make sense
  for `Option V`-vertex extensions, which don't exist upstream).

### [resolved] Repeated existential-witness packaging in `exists_typeI_or_typeII_iso`
- **Where it bit:** the three rcases branches of the degree-3 case in
  `IsLaman.exists_typeI_or_typeII_iso`. Each branch chose a
  non-adjacent neighbor pair, relabelled `(a, b, c)` → `(α, β, γ)` so
  the non-adjacent pair is `(α, β)`, and then unpacked the existential
  `∃ G' a' b' c', a' ≠ b' ∧ c' ≠ a' ∧ c' ≠ b' ∧ G'.Adj a' b' ∧
  Nonempty (G ≃g typeII G' a' b' c')` by hand: ~10 lines per branch
  for four `intro heq; exact … (Subtype.mk.injEq .. |>.mp heq)`
  Subtype-distinctness contradictions plus an `Or.inr ⟨rfl, _⟩`
  adjacency witness.
- **Resolution:** extracted a private `typeII_branch_of_nonadj`
  helper that packages the entire existential given the neighbor
  triple, the three pairwise-distinctness witnesses (in the order
  `a ≠ b, c ≠ a, c ≠ b` matching the goal), the iff-form `hN_iff`,
  and the non-adjacency hypothesis. Each rotation branch then
  collapses to one `(typeII_branch_of_nonadj …).imp fun _ => Or.inr`
  line, with the relabelling encoded in the argument order.
  Companion `typeI_branch_of_two_neighbors` does the same for the
  degree-2 case. Phase 3 cleanup pass.
- **Status:** resolved (project-internal — these helpers are specific
  to the iso-decomposition theorem).

### [resolved] `DecidableRel` for `typeI.Adj` / `typeII.Adj` (project-internal)
- **Where it bit:** `Henneberg.fin4iso`'s `map_rel_iff'` proof (in
  `top_fin_four_minus_edge_isLaman`).
- **Friction:** `typeI.Adj` and `typeII.Adj` are defined by `match` on
  `Option V`. Lean does not auto-derive `DecidableRel` from this shape.
  `decide` for the iso's `map_rel_iff'` succeeded on the
  `(none, _)` / `(_, none)` arms (which reduce to `Or` of equalities)
  but failed on the `(some _, some _)` arms because the
  inner-`Adj` reduction didn't fire under typeclass synthesis. `simp` on
  `typeI_adj_some_some` partially worked but didn't close the goal.
- **Resolution:** added two two-line instance declarations
  `instDecidableTypeIAdj` and `instDecidableTypeIIAdj` next to the
  `typeI` / `typeII` definitions. Each routes the four pattern arms
  through `inferInstance` (for `(some, some)`, `(some, none)`,
  `(none, some)`) and `instDecidableFalse` (for `(none, none)`). After
  this, the K₄ \ e iso's `map_rel_iff'` closes by a single
  `rintro <;> first | decide | (fin_cases _ <;> decide) | …` line.
- **Status:** resolved (project-internal — typeI/typeII don't exist
  upstream, so no mirror).

### [resolved] `IsLaman.iso` factored through `IsSparse.iso` / `IsTight.iso`
- **Where it bit:** designing the iso-preservation lemma for the
  `K₄ \ e` example.
- **Friction:** initial scoping was "add `IsLaman.iso` to `Laman.lean`"
  with the proof inlining sparsity + tightness transport. Those
  arguments are parametric in `(k, ℓ)` and have nothing to do with the
  `2, 3` choice: the natural home is one level below `IsLaman`.
- **Resolution:** added `Iso.image_edgesIn` (the `edgesIn` analogue of
  mathlib's `Iso.image_neighborSet`), `IsSparse.iso`, and `IsTight.iso`
  to `Sparsity.lean`. `IsLaman.iso` in `Laman.lean` is then a one-line
  specialization `IsTight.iso φ h`. `Sparsity.lean` already imports
  `SimpleGraph.Maps` transitively via `DeleteEdges`, so the only new
  import is the project's `Sym2.mk_mem_image_map_iff` mirror.
- **Status:** resolved (project-internal). Lifted as a phase-local
  decision into `notes/Phase3.md`.

### [resolved] 6-edge / 4-set cardinalities in `IsLaman.exists_nonadj_among_three_neighbors`
- **Where it bit:** the cardinality preamble in
  `IsLaman.exists_nonadj_among_three_neighbors` (`Laman.lean`):
  ```
  hs_card : ({v, a, b, c} : Finset V).card = 4
  hE_card : E.card = 6      where E = {s(v,a), s(v,b), …, s(b,c)}
  ```
  was an 8-line `rw [Finset.card_insert_of_notMem ?_, …, card_singleton]`
  chain plus an `all_goals simp only [Finset.mem_insert, mem_singleton,
  Sym2.eq_iff]; tauto` cleanup, repeated at the 4-set case in 4 lines.
- **Friction:** the cardinality bound is mathematically trivial given
  the pairwise distinctness already in scope, but the proof is the
  longest mechanical block in `Laman.lean`. Tried direct `Finset.sym2`
  / off-diagonal-image routes (`Sym2.card_image_offDiag`); they
  require equally long subset-equality preambles. Tried injecting
  from `Fin 6`; same problem. Tried `decide`; doesn't see the
  symbolic disequalities.
- **Resolution:** `grind` with the right hint set closes both:
  ```
  hs_card: grind [Finset.card_insert_of_notMem, Finset.card_singleton]
  hE_card: grind [Finset.card_insert_of_notMem, Finset.card_singleton, Sym2.eq_iff]
  ```
  (`Finset.mem_insert` / `Finset.mem_singleton` are already
  `@[grind =]` upstream, so don't pass them — `grind` warns.) The
  4-set proof drops 4 → 2 lines; the 6-edge proof drops 8 → 3.
- **Status:** resolved (project-internal — Laman-specific application
  of an upstream `grind` tactic).

### [resolved] Dot notation skips sub-namespaces (`h.typeII_reverse_blocker` from `Henneberg.IsLaman.*`)
- **Where it bit:** `IsLaman.typeII_reverse_witness_or_blocker` in `Henneberg.lean`
  (Phase 5 milestone 1).
- **Friction:** the existing helper `IsLaman.typeII_reverse_blocker` is declared
  inside `namespace SimpleGraph.Henneberg`, so its full name is
  `SimpleGraph.Henneberg.IsLaman.typeII_reverse_blocker`. Wrote
  `h.typeII_reverse_blocker hxv …` with `h : G.IsLaman` expecting Lean to find it
  via the current namespace. Lean's dot notation only consults the **type's**
  head namespace (`SimpleGraph.IsLaman`), not the surrounding namespace stack,
  so the lookup fails. The error appears as "`And.typeII_reverse_blocker` not
  found" because Lean unfolds `IsLaman → IsTight → And` while searching.
- **Resolution:** call by explicit name —
  `IsLaman.typeII_reverse_blocker h hxv …` works directly from inside the
  `Henneberg` namespace (the partial-prefix lookup resolves
  `Henneberg.IsLaman.typeII_reverse_blocker`). Promoting the helper to the
  outer `SimpleGraph` namespace would also fix it, but is the wrong choice here
  — `typeII_reverse_blocker` is conceptually a Henneberg-flavoured helper.
- **Status:** resolved (Lean idiom — inside a sub-namespace, use explicit names
  for sub-namespace helpers; dot notation is only for the type's own namespace).

### [resolved] `mem_edgeSet.mp` / `.mpr` dot notation rejected by Lean
- **Where it bit:** `typeI_isInfinitesimallyRigid_extend` in
  `Henneberg.lean` (Phase 5 milestone 2). Inside an `induction e with | h u v
  => ...` block on `e : Sym2 V` with `he : e ∈ G.edgeSet`, the natural one-liner
  was
  `have h_some : s(some u, some v) ∈ (typeI G a b).edgeSet := mem_edgeSet.mpr (mem_edgeSet.mp he)`.
- **Friction:** Lean rejected the dot notation: ``Unknown constant
  `SimpleGraph.mem_edgeSet.mp` `` / ``... .mpr``. Lean was looking for
  `SimpleGraph.mem_edgeSet.mp` as a fully-qualified constant rather than treating
  `mem_edgeSet : Iff _ _` as a term and projecting `Iff.mp`. The cause is unclear
  — possibly elaboration order with no concrete arguments to disambiguate the
  implicit `G, v, w` of `mem_edgeSet`. Surrounding uses (`rw [mem_edgeSet]`)
  worked fine.
- **Resolution:** `mem_edgeSet` is `Iff.rfl`; both sides are *definitionally
  equal*. So a proof `he : s(u, v) ∈ G.edgeSet` doubles as a proof of
  `G.Adj u v`, and since `typeI_adj_some_some` is also `Iff.rfl` (so
  `(typeI G a b).Adj (some u) (some v)` is defeq to `G.Adj u v`), the original
  `he` is directly usable as the goal `s(some u, some v) ∈ (typeI G a b).edgeSet`.
  The final form is the one-liner
  `have h_some : s(some u, some v) ∈ (typeI G a b).edgeSet := he`. Elegant
  consequence of the chain-of-`Iff.rfl`s; no need for `mem_edgeSet` invocations
  at all.
- **Status:** resolved (defeq side-stepped the elaboration glitch; the underlying
  dot-notation failure remains mysterious but is consistently reproducible
  inside `Sym2.ind`/`induction e with` blocks).

### [resolved] `hcoe` `have` line in `_isLaman` proofs
- **Where it bit:** both `typeI_isLaman` and `typeII_isLaman` opened
  with
  ```
  have hcoe : (s' : Set V) = some ⁻¹' (↑s : Set (Option V)) :=
    Finset.coe_eraseNone s
  ```
  and then passed `hcoe` (and `Set.mem_preimage`) to the `simp` inside
  the `h_decomp` proof.
- **Friction:** `set s' := s.eraseNone with hs'_def` introduces `s'`
  as an opaque abbreviation; `simp` in `h_decomp` cannot unfold `↑s'`
  to `↑s.eraseNone` on its own and so does not see the `@[simp]`-
  tagged `Finset.coe_eraseNone`. The `hcoe` `have` worked around this
  by surfacing the equation manually.
- **Resolution:** pass `hs'_def` directly to `simp`. With
  `simp [hs'_def, edgesIn, T]` (and `T'` for typeII) the
  `s' → s.eraseNone` rewrite fires, then `Finset.coe_eraseNone` and
  `Set.mem_preimage` (both upstream `@[simp]`) handle the remaining
  goal automatically. Drops the `hcoe` line from both proofs (~4
  lines total).
- **Status:** resolved (no missing lemma — was a `simp`-set
  oversight).

### [resolved] `simp_all` rewrites backwards with equality hypotheses

- **Where it bit:** the K₂ injective base case `top_fin_two_isGenericallyRigidInj`
  in `Framework.lean`. First-attempt injectivity discharge was
  ```
  fin_cases i <;> fin_cases j <;> simp_all [hp_def]
  ```
  expecting `simp` to reduce `p 0 = p 1` to `0 = EuclideanSpace.single 0 1`
  and then close.
- **Friction:** in the `(0, 1)` case, `simp_all` picked up the goal-hypothesis
  `hij : 0 = EuclideanSpace.single 0 1` and rewrote `0` to `EuclideanSpace.single 0 1`
  *inside `hp_def`*, producing the absurd `hp_def : p = ![single 0 1, single 0 1]`
  in the context — leaving the goal `False` open. `simp_all` is allowed to use any
  hypothesis as a rewrite rule, including in the LHS→RHS direction of an equality;
  with a destructively-rewriting hypothesis like `0 = X` this cross-contaminates
  the rest of the context.
- **Resolution:** discriminate via a derived quantity that doesn't trigger
  cross-rewriting. Used `have h_norm : ‖p i‖ = ‖p j‖ := congrArg _ hij` then
  `revert h_norm <;> simp [hp_def]`, closing in one `simp` per leaf.
- **Status:** resolved (tactic semantics, not a missing lemma). General lesson:
  when `simp_all` produces a confusing residual goal involving a hypothesis you
  expected to eliminate, suspect cross-rewriting from an equality hypothesis.

### [resolved] `congr_fun` does not apply to `EuclideanSpace`

- **Where it bit:** the K₂ injective base case `top_fin_two_isGenericallyRigidInj`
  in `Framework.lean`. First attempt at extracting a coordinate from
  `h : EuclideanSpace.single 0 1 = 0` used `congr_fun h 0` to get
  `(EuclideanSpace.single 0 1) 0 = (0 : EuclideanSpace _) 0`.
- **Friction:** `EuclideanSpace ℝ ι` is `PiLp 2 (fun _ => ℝ)`, *not* `ι → ℝ`. Even
  though the carrier types coerce, `congr_fun` needs the source type to be a Pi
  type literally — it errors out with `Application type mismatch`. The error
  message does not flag the type-vs-`Pi`-application mismatch as the cause.
- **Resolution:** route equality witnesses through a continuous map (here
  `congrArg norm hij`). `Pi`-style projections also work after explicit
  conversion via `EuclideanSpace.equiv` or `PiLp.equiv`, but the norm route is
  shorter when a discriminating norm is available.
- **Status:** resolved (project-internal lesson). Adds to the list of "things
  that act like Pi types but aren't literally Pi types" — alongside `Sym2 V`
  (where `Sym2.lift` is the projection, not `congr_fun`).

### [resolved] `rcases ⟨rfl, rfl⟩` on `Sym2.eq_iff` eliminates the section-level variable, not the case-split variable

- **Where it bit:** `typeII_isInfinitesimallyRigid_extend` in `Henneberg.lean`
  (Phase 5 milestone 2), deleted-edge recovery. After `induction e with | h u v
  =>` and a `by_cases h_eq : s(u, v) = s(a, b)`, the natural pattern was
  ```
  rcases Sym2.eq_iff.mp h_eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- u = a, v = b
    exact h_deleted
  · -- u = b, v = a — use h_deleted via inner-product symmetry
    have hflip : p b - p a = -(p a - p b) := by abel
    ...
  ```
- **Friction:** In the second branch, `rcases ⟨rfl, rfl⟩` substituted `b → u`
  and `a → v` (eliminating the section-level variables `a, b` from the local
  context) rather than `u → b` and `v → a`. The follow-up `have hflip : p b -
  p a = ...` then failed with `Unknown identifier b`. Lean's `subst` heuristic
  on `u = b` (both sides free variables) eliminates the *less-recently-
  introduced* free variable when both qualify — and `b` came earlier (theorem
  binder) than `u` (case-split intro).
- **Resolution:** bind the equalities to named hypotheses and use `rw`, which
  doesn't eliminate from the context:
  ```
  rcases Sym2.eq_iff.mp h_eq with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]; exact h_deleted
  · rw [h1, h2, /- sign flip -/]; exact h_deleted
  ```
  This keeps `a, b` in scope for the subsequent calculation. The first branch
  closes identically to the `rfl`-form; the second branch picks up an explicit
  sign-flip rewrite via `inner_neg_neg`.
- **Status:** resolved (Lean idiom, not a missing lemma). General lesson: when
  `subst` direction matters and both sides of an equation are free variables,
  prefer named hypotheses + `rw` (or explicit `subst h` on a named hypothesis,
  with deliberate side selection) over `rfl` patterns. Cf. line 521 of
  `Henneberg.lean`, where `rcases ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> grind` works
  *because* `grind` closes both branches regardless of which variables remain.

### [resolved] `simp only [rigidityMap_apply, Pi.zero_apply]` leaves `he` in the elaborated goal, blocking later `rw`

- **Where it bit:** `typeII_isInfinitesimallyRigid_extend` in `Henneberg.lean`
  (Phase 5 milestone 2). After
  ```
  ext ⟨e, he⟩
  induction e with | h u v => ...
  ...
  simp only [rigidityMap_apply, Pi.zero_apply, Function.comp_apply]
  ```
  the displayed goal is the clean `⟪p u - p v, x (some u) - x (some v)⟫_ℝ = 0`,
  but a subsequent `rw [h1, h2]` (with `h1 : u = a`) failed with `motive is not
  type correct`, citing an application `⟨s(_a, v), he⟩` that the motive couldn't
  unify.
- **Friction:** `simp only` simplified the surface form but the elaborated term
  retained a residual `⟨s(u, v), he⟩` subterm (likely inside an `Eq` proof that
  `simp` produced). `rw`'s motive synthesis then re-elaborates the goal,
  picking up `he` with its `u`-dependent type, and the abstraction over `u`
  fails because `he` cannot be re-typed at `_a`.
- **Resolution:** insert a `change <clean form>` immediately after the `simp
  only` to surface the displayed goal cleanly, dropping the residual subterm:
  ```
  simp only [rigidityMap_apply, Pi.zero_apply, Function.comp_apply]
  change ⟪p u - p v, x (some u) - x (some v)⟫_ℝ = 0
  rcases ... with ...
  rw [h1, h2]; ...
  ```
  The `change` re-elaborates the goal at the surface type, discarding the
  hidden `he` subterm. `rw` then succeeds.
- **Status:** resolved (Lean idiom). General lesson: when `rw` fails with a
  motive error citing a hypothesis that doesn't appear in the displayed goal,
  suspect a `simp`-produced residual subterm and insert `change` to clean.
  Mirrors the `Sym2`-symmetry residual issue at line 521 (where `grind`
  papered over it).

### [resolved] `interval_cases` on non-variable expression doesn't substitute

- **Where it bit:** `IsLaman.isGenericallyRigidInj_two_of_card` in
  `LamanTheorem.lean` (Phase 5 milestone 3). In the base-case branch
  (`Fintype.card V ≤ 2`), the natural tactic was `interval_cases
  (Fintype.card V)` to enumerate `card V ∈ {0, 1, 2}` and apply the
  K₂ base-case helper `IsLaman.eq_top_of_card_eq_two` in the `= 2`
  arm via `h.eq_top_of_card_eq_two rfl`.
- **Friction:** `rfl` failed to close `Fintype.card V = 2`.
  `interval_cases` on a free variable substitutes the value everywhere
  via `subst`; on a function application like `Fintype.card V`, it
  enumerates the cases but does *not* rewrite the expression in the
  context — so the case-arm's `Fintype.card V` stays abstract and `rfl`
  can't prove it equals `2`.
- **Resolution:** sidestep `interval_cases` entirely. Use `by_cases hV3
  : 3 ≤ Fintype.card V` for the high/low split; in the `< 3` branch,
  use `omega` with `IsLaman.edgeSet_ncard`'s `#E + 3 = 2 * card V`
  (over `ℕ`, so `card V ≤ 1` is infeasible) to derive
  `hcard2 : Fintype.card V = 2` as a named hypothesis. Then
  `h.eq_top_of_card_eq_two hcard2` works.
- **Status:** resolved (use `omega`-derived named hypothesis, not
  `interval_cases`, for value equations on function applications).
  General lesson: `interval_cases` is for free *variables*; for
  function applications, prove the equation explicitly via `omega` or
  similar and name it.

### [resolved] `subst h` on `h : v = c` between two local vars can substitute the variable you want to keep

- **Where it bit:** `exists_nonCollinear_rigid_placement_dim_two` in
  `Henneberg.lean` (Phase 5 milestone 2 closure). After
  `refine continuous_pi (fun v => ?_); by_cases hvc : v = c; · subst hvc`,
  the goal then referenced `c` but Lean reported `Unknown identifier `c``.
- **Friction:** `subst` between two free variables picks one to remove.
  It removed `c` (the function-signature variable) and kept `v` (the
  late-introduced binder), so subsequent uses of `c` (`p_t t c`, `p₀ c`,
  etc.) failed.
- **Resolution:** use `rw [hvc]` (or compose `funext t; rw [hvc, ...]`)
  in place of `subst hvc`. `rw` directionally substitutes per the
  equation hypothesis and leaves both names usable. The `c`-arm of the
  continuity proof now reads:
  ```
  · have h : (fun t : ℝ => p_t t v) = fun t => p₀ c + t • w := by
      funext t; rw [hvc, h_p_t_c]
    rw [h]
    exact continuous_const.add (continuous_id.smul continuous_const)
  ```
- **Status:** resolved (use `rw` over `subst` when both sides of the
  equation are locals you want to keep referencing).

### [resolved] `set p_t := fun t => …` + `simp [p_t]` doesn't unfold the let-binding cleanly

- **Where it bit:** `exists_nonCollinear_rigid_placement_dim_two` in
  `Henneberg.lean`. Initial draft used
  `set p_t : ℝ → Framework V 2 := fun t => Function.update p₀ c (p₀ c + t • w) with hp_t_def`
  and tried `simp [p_t]` to unfold `p_t t c` to `Function.update _ c _ c`
  for follow-up `Function.update_self`. Lean's error was the cryptic
  `⊢ sorry () c = p₀ c + t • w` (the displayed unfolded form, with
  `sorry` indicating an elaboration glitch on the `set` body).
- **Friction:** `simp` on a `set`-introduced name doesn't reliably
  unfold to the body in Lean 4's current behavior; the `simp [p_t]`
  pattern works for some `set`s and not others, especially when the
  body is a lambda.
- **Resolution:** replace `set` with `let`, then state per-case helper
  lemmas explicitly via `Function.update_self` / `Function.update_of_ne`
  and reference *those* in subsequent reasoning (don't try to round-trip
  through `simp [p_t]`):
  ```
  let p_t : ℝ → Framework V 2 := fun t => Function.update p₀ c (p₀ c + t • w)
  have h_p_t_c : ∀ t, p_t t c = p₀ c + t • w := fun _ => Function.update_self c _ p₀
  have h_p_t_ne : ∀ t v, v ≠ c → p_t t v = p₀ v :=
    fun _ v hvc => Function.update_of_ne hvc _ p₀
  ```
- **Status:** resolved (prefer explicit `have`-lemmas over `set`-name
  unfolding when the body is a lambda and downstream goals need beta
  reduction).

### [resolved] `linearIndependent_fin2` leaves `![v₀, v₁] 0` / `![v₀, v₁] 1` unsimplified at the indexing layer

- **Where it bit:** `exists_nonCollinear_rigid_placement_dim_two` in
  `Henneberg.lean`, when extracting the collinearity coefficient from
  the negated LI hypothesis.
- **Friction:** `rw [linearIndependent_fin2] at hLI₀` produces
  `hLI₀ : ¬ (![p₀ b - p₀ a, p₀ c - p₀ a] 1 ≠ 0 ∧ ∀ a, …)`. The Fin-2
  matrix indexing `![…] 0` and `![…] 1` *isn't auto-reduced* — downstream
  `obtain ⟨γ, hγ⟩` then carries `γ • ![v₀, v₁] 1 = ![v₀, v₁] 0` as
  hypothesis, and follow-up `rw [← hγ, …]` fails with
  *Did not find an occurrence of the pattern* because the goal mentions
  `p₀ c - p₀ a` / `p₀ b - p₀ a` directly, not `![…] 1` / `![…] 0`.
- **Resolution:** follow the `linearIndependent_fin2` rewrite with
  `simp only [Matrix.cons_val_zero, Matrix.cons_val_one]`:
  ```
  rw [linearIndependent_fin2] at hLI₀
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hLI₀
  push Not at hLI₀
  obtain ⟨γ, hγ⟩ := hLI₀ hdac_ne_zero
  -- hγ : γ • (p₀ c - p₀ a) = p₀ b - p₀ a   (clean form)
  ```
- **Status:** resolved (always pair `linearIndependent_fin2` with the
  matrix-indexing simp set if the destructured form is going to be
  used in `rw`).

### [resolved] `push_neg` deprecated in favor of `push Not`

- **Where it bit:** several `push_neg at hLI₀` calls in
  `exists_nonCollinear_rigid_placement_dim_two`.
- **Friction:** linter warning rather than error; `push_neg` still
  works but is deprecated. The replacement is `push Not`.
- **Resolution:** swap `push_neg` for `push Not`. Behavior identical
  for the use cases here.
- **Status:** resolved (deprecation cleanup).

### [resolved] Inline kernel-restriction LinearMap built by hand

- **Where it bit:** `typeI_isInfinitesimallyRigid_extend` and
  `typeII_isInfinitesimallyRigid_extend` in `HennebergRigidity.lean`.
  Each builds a `restrict : ker (typeI/II G.RigidityMap p_ext) →ₗ[ℝ]
  ker (G.RigidityMap p)` whose underlying map is `x ↦ x ∘ some`.
- **Friction:** initially constructed as an anonymous-constructor
  LinearMap (`{ toFun := …, map_add' := …, map_smul' := … }`), 5 lines
  per call site with `map_add' / map_smul'` proved by `rfl`. The
  underlying map is precomposition by `some : V → Option V`, which is
  `LinearMap.funLeft`.
- **Resolution:** swap the anonymous structure for
  `((LinearMap.funLeft ℝ _ some).comp _.subtype).codRestrict _ h_into`.
  3 lines per call site; no `rfl`-glue. `LinearMap.funLeft` is the
  canonical "precomposition" linear map; `LinearMap.codRestrict` is
  the canonical "land in a submodule" restriction. Second-cleanup-pass
  resolution of a deferred audit.
- **Status:** resolved.

### [resolved] Affine-line `Function.Injective` proved by `smul_eq_zero` unpacking

- **Where it bit:** `exists_off_line_off_finite_dim_two` and
  `exists_typeII_q_on_line_dim_two` in `HennebergRigidity.lean`. Each
  proves `Function.Injective (fun t : ℝ => p + t • v)` for `v ≠ 0`.
- **Friction:** initial proof did `add_left_cancel`, then
  `sub_smul ... sub_self`, then `smul_eq_zero.mp ... .elim` — 6 lines
  to extract `t₁ = t₂` from `t₁ • v = t₂ • v`.
- **Resolution:** mathlib has `smul_left_injective R (h : v ≠ 0) :
  Function.Injective (fun r : R => r • v)` (in
  `Mathlib/Algebra/Module/Torsion/Free.lean`, applies to any
  torsion-free `R`-module). Each call site collapses to
  `fun _ _ h => smul_left_injective ℝ hv (add_left_cancel h)`.
  Second-cleanup-pass resolution of a deferred audit.
- **Status:** resolved.
