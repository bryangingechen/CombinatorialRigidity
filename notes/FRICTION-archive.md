# API and tactic friction log — archive

This file holds **resolved project-internal** friction entries that
have been preserved for design history. Moved out of
[`FRICTION.md`](FRICTION.md) in a post-Phase-6 housekeeping pass
once each entry's resolution had a real index elsewhere:

- A named mirror lemma under
  `CombinatorialRigidity/Mathlib/<exact mathlib path>` (discoverable
  via `lean_local_search` / `lean_loogle`), or
- A named project-internal helper in the file that owns the relevant
  definition (also discoverable via `lean_local_search`), or
- A `**Lifted to:** TACTICS-GOLF § X` (idiom / golf) or
  `**Lifted to:** TACTICS-QUIRKS § X` (rescue / build-failure
  recovery) cross-reference for any general Lean-idiom lesson.

The entries below are **search targets, not read-on-load.** Grep
when you want to know how a specific past friction was handled; the
indexed resolution is the thing future agents will land on first via
normal proof-writing workflow.

For the **active** friction log — open items, anti-patterns,
mirrored upstream candidates — see [`FRICTION.md`](FRICTION.md).

## Resolved (project-internal)


### [resolved] `LinearMap.ext` + `LinearMap.eqOn_span` re-deriving what `LinearMap.ext_on` already packages
- **Where it bit:** `trivialMotionFamily_linearIndependent`'s `h_S_zero` block
  in `TrivialMotions.lean` (Phase 6).
- **Friction:** to discharge `S = 0` from "`S` vanishes on `(Set.range p) -ᵥ
  (Set.range p)`" plus "span of that set is `⊤`" (via the affine-spanning
  hypothesis), the original proof opened up `LinearMap.ext fun x => …`, then
  derived `x ∈ Submodule.span ℝ ((Set.range p) -ᵥ (Set.range p))` from
  `vectorSpan = ⊤` via `← vectorSpan_def`, then closed with
  `LinearMap.eqOn_span` — a 9-line block.
- **Resolution:** mathlib already packages exactly this pattern as
  `LinearMap.ext_on (hv : Submodule.span R s = ⊤) (h : Set.EqOn f g s) : f = g`
  in `Mathlib/LinearAlgebra/Span/Basic.lean`. The block collapses to 6 lines
  (derive the `Submodule.span … = ⊤` fact via `← vectorSpan_def`, then
  `LinearMap.ext_on hvspan ?_` + the generators dispatch). Companion
  `LinearMap.ext_on_range` handles the `Set.range`-of-a-function shape if
  ever paired with `vectorSpan_range_eq_span_range_vsub_left` / `_right`.
- **Status:** resolved (no missing lemma — `LinearMap.ext_on` was on the
  wrong shelf; `LinearMap.eqOn_span` is the pointwise version, harder to
  discover).
- **Lifted to:** TACTICS-GOLF § 3 *Search mathlib before mirroring*
  (cited as a case where `lean_leanfinder` would have found the
  packaged form).

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
- **Lifted to:** TACTICS-QUIRKS § 8 *Dot notation only consults the
  type's head namespace* (the "same-name wrapper recurses" trap).

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
  missing). Recorded in TACTICS-GOLF.md § 5.

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
- **Lifted to:** TACTICS-QUIRKS § 8 *Dot notation only consults the
  type's head namespace* (the "sub-namespace lookup fails" trap).

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
- **Lifted to:** TACTICS-QUIRKS § 10 *`simp_all` can
  cross-contaminate with destructive equality hypotheses*.

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
- **Lifted to:** TACTICS-QUIRKS § 9 *`congr_fun` does not apply to
  `EuclideanSpace`*.

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
- **Lifted to:** TACTICS-QUIRKS § 4 *`subst` between two free
  variables picks the wrong one* (the `Sym2.eq_iff` case is one of
  two cited traps).

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
- **Lifted to:** TACTICS-QUIRKS § 5 *`simp only` leaves residual
  subterms that block `rw` motives*.

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
- **Lifted to:** TACTICS-QUIRKS § 7 *`interval_cases` is for free
  variables, not function applications*.

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
- **Lifted to:** TACTICS-QUIRKS § 4 *`subst` between two free
  variables picks the wrong one* (the `hvc : v = c` case is one of
  two cited traps).

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
- **Lifted to:** TACTICS-QUIRKS § 6 *`set name := fun t => …` +
  `simp [name]` doesn't unfold lambdas*.

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
- **Lifted to:** TACTICS-QUIRKS § 11 *`linearIndependent_fin2`
  leaves `![v₀, v₁] 0 / 1` unsimplified*.

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

### [resolved] `induction _ using funName.induct` binder count + inner-`let` shadowing

- **Where it bit:** `tryAddEdgeWith_reachable` in
  `CombinatorialRigidity/PebbleGame.lean` (Phase 9, *Reachable*
  preservation chain). `tryAddEdgeWith`'s below-threshold branch
  binds `let P : V → Bool := fun w => …`; the auto-generated
  `tryAddEdgeWith.induct` carries `P` as a `let`/`have` clause in
  three of its five cases. Initial proof attempt (i) omitted `P`
  from the case-binder list for case5 — Lean shifted the remaining
  binders, and the `rw [tryAddEdgeWith, dif_neg hthr] at h` line
  failed with *"Application type mismatch: argument `hthr` has
  type V → Bool"* (the now-misaligned `hthr` was actually `P`).
  After fixing the binder count, (ii) `rw [hu_none, hv_none] at h`
  failed with *"Did not find an occurrence of the pattern
  `D.tryReachPebbleWith P u (toSucc D) ⋯`"* — the inner `let P :=
  …` inside `h` shadowed the case binder `P`, so `hu_none`'s
  pattern (built on the case binder) didn't match. (iii) After
  inlining the inner let with `dsimp only at h` and re-running the
  rewrites, `Option.noConfusion h` failed: the matches with
  `none` discriminees hadn't reduced.
- **Friction:** three closely-related traps that all surface only
  when the function being inducted has a `let` in its body. None
  of TACTICS-QUIRKS § 1–18 covered this combination.
- **Resolved (Phase 9):** the working pattern is (a) name the
  `let`-bound parameter in each affected case's binder list — use
  `#check @funName.induct` or `lean_hover_info` via MCP to see the
  exact let / have / ∀ chain; (b) apply `dsimp only at h` after
  the function-definition unfold to inline the inner `let` so
  subsequent rewrites match; (c) use `nomatch h` (or `cases h`,
  `simp at h`) rather than `Option.noConfusion h` to discharge
  match-with-`none`-discriminee contradictions, since these match
  tactics trigger the match reduction automatically.
- **Lifted to:** TACTICS-QUIRKS.md § 19 *`induction … using
  funName.induct` on a function with `let` in its body*; quirks
  index entry added in `CombinatorialRigidity/CLAUDE.md`.
- **Status:** resolved.

### [resolved] `rw [D.field_eq]` fails motive when a local's type references the field

- **Where it bit:** `PartialOrientation.out_reverse_add` in
  `CombinatorialRigidity/PebbleGame.lean` (Phase-9 main). The path
  `p : DirectedWalk (fun a b => (a, b) ∈ D.arcs) u w` ties `D.arcs`
  into `p`'s type, and the goal contains both `D.arcs.filter (·.1 = v)`
  *and* `p.vertices` (via the `if v ∈ p.vertices ∧ … then 1 else 0`
  clauses). The natural step "decompose `D.arcs` as `D.arcs \
  p.arcsFinset ∪ p.arcsFinset`, then split the filter card" calls
  `rw [h_decomp]` (or `conv_rhs => rw [h_decomp]`) with `h_decomp :
  D.arcs = …`. Lean's motive abstraction tries to rewrite `D.arcs`
  inside `p.vertices`'s carrier (which lives in `p`'s type) and
  fails with *motive is not type correct*.
- **Friction:** the existing motive entries (§ 4, § 5 in
  `TACTICS-QUIRKS.md`, and the FRICTION `subst between two free
  variables` neighbour) are about *names being substituted*;
  this case is about *a structure field being rewritten where the
  field appears in another local's type*. Distinct shape.
- **Resolved (Phase 9):** build the rewritten Finset equation
  via `Finset.ext` + manual disjunction casework, then `rw` the
  equation as a single unit whose motive is `λ s, s.card`
  (trivially type-correct). Pattern is reusable for any subset-
  level reversal lemma that filters `D.arcs` in the presence of
  `p`. **Lifted to:** TACTICS-QUIRKS.md § 18 *`rw [h]` over a
  structure field whose value appears in another local's type*.
- **Status:** resolved.

### [resolved] `rw` over a cons-pattern endpoint variable trips motive on the sibling walk's type
- **Where it bit:** `IsPath.notMem_loop_arcsFinset` and
  `IsPath.notMem_antiparallel_arcsFinset` in
  `CombinatorialRigidity/Search/DFS.lean`. Inside the `cons u_out
  u_int _ _ q ih` branch of an induction on `p : DirectedWalk R u
  w`, the path equalities `(v, v) = (u_out, u_int)` unpack via
  `Prod.mk.inj` to `v = u_out ∧ v = u_int`. The first `rfl`
  substitutes `u_out := v` (cf. `TACTICS-QUIRKS.md` § 4); the
  follow-up `rw [← h_eq]` (with `h_eq : v = u_int`) on a goal `v
  ∈ q.vertices` then fails with *motive is not type correct*,
  because `q : DirectedWalk R u_int w` ties `u_int` to `q`'s
  type, and Lean's motive abstraction tries to rewrite `u_int`
  inside `q`'s type.
- **Friction:** § 4 covers the *direction* of `subst` between two
  free variables, but the symptom here surfaces one tactic *later*
  on a downstream `rw`, not at the `obtain ⟨rfl, _⟩` itself. The
  same shape blocks `cases q <;> simp [vertices]` whenever the
  cons-pattern endpoint has already been substituted away.
- **Resolved (Phase 9):** bind the pair equalities to named
  hypotheses (`have h_uo : v = u_out := (Prod.mk.inj heq).1`),
  compose them into a single `u_out = u_int` equation, and `rw`
  only on `u_out` (which does not appear in `q`'s type — only
  `u_int` does). Factor "the source vertex is in `p.vertices`"
  through a one-line `head_mem_vertices : u ∈ (p : DirectedWalk
  R u w).vertices` helper to skip the `cases q <;> simp` dance
  entirely. The helper is `@[simp]`; reused across the Phase 9
  structural-lemma chain.
- **Lifted to:** TACTICS-QUIRKS.md § 20 *`rw [eq]` after `obtain
  ⟨rfl, _⟩` on a cons-pattern endpoint trips motive on the sibling
  walk's type*; quirks index entry added in
  `CombinatorialRigidity/CLAUDE.md`. § 20 added in Phase 9-cleanup
  D3 lift-on-archive pass.
- **Status:** resolved.

### [resolved] `ring` treats alpha-renamed `Finset.sum` as distinct atoms
- **Where it bit:** `Reachable.independent_brings_pebble` in
  `CombinatorialRigidity/PebbleGame.lean`. After
  `rw [pebOn, ← Finset.sum_sdiff huv_sub, Finset.sum_pair huv]` the
  residual goal was
  `∑ x ∈ V' \ {u, v}, peb k x + (peb u + peb v) = peb u + peb v + ∑ w ∈ V' \ {u, v}, peb k w`
  — an `A + B = B + A` shape modulo alpha-equivalence on the
  `Finset.sum` body (`x` vs `w`). `ring` failed with *"unsolved
  goals"*; the atom-extractor evidently checks syntactic identity on
  lambda bodies, not full defeq.
- **Friction:** the natural Finset.sum-decomposition idiom (rewrite
  via `Finset.sum_sdiff` then `Finset.sum_pair`, finish with `ring`)
  doesn't close. Bound-variable names from the rewrite source
  (Finset.sum_sdiff uses `x`) and from the target's `have` statement
  (chose `w`) don't align, and `ring` doesn't normalize across.
- **Resolved (Phase 9):** Bind the two pieces (`Finset.sum_sdiff`
  and `Finset.sum_pair`) as separate `have` hypotheses and let
  `omega` close the existence-of-witness chain directly — `omega`
  treats each `Finset.sum` as an atomic ℕ term and the surrounding
  linear inequality `0 < ∑ w ∈ V' \ {u, v}, peb k w` is one
  `omega` away.
- **General rule (for the next sum-decomposition that hits this):**
  When `ring` fails on a goal that's *syntactically*
  `Σ + B = B + Σ'` with `Σ`, `Σ'` alpha-equivalent, do not paper
  over with `ring_nf; ring`. Switch to threading the sum identities
  through `have`s and finishing with `omega` (linear over ℕ) or
  `linarith` (ordered field). The atom abstraction does the work
  `ring` won't.
- **Lifted to:** TACTICS-QUIRKS.md § 21 *`ring` fails on
  alpha-renamed `Finset.sum`s — `omega` / `linarith` as atom
  extractor*; quirks index entry added in
  `CombinatorialRigidity/CLAUDE.md`. § 21 added in Phase 9-cleanup
  D3 lift-on-archive pass.
- **Status:** resolved (Phase 9 main, completeness side, Lemma 13).

### [resolved] `Finset.toList` is noncomputable — math/exec layer split
- **Where it bit:** `reachableFindingAux` body in
  `CombinatorialRigidity/Search/DFS.lean`. Enumerating the children
  of `v` for early-termination DFS via `(succ v).attach.toList` (the
  natural shape if `succ : V → Finset V`) would force the whole
  function `noncomputable`, because `Finset.toList` lifts through
  `Multiset.toList`'s `Classical`-flavored `Quotient.lift` (an
  unordered collection has no canonical permutation representative).
- **Friction:** the pebble-game style island in `DESIGN.md`
  aspires to *"`#eval` and `decide` should actually fire on extracted
  certificates"*; first-attempt body fill with
  `succ : V → Finset V` silently downgrades the algorithm to
  `noncomputable`, defeating that goal. Lesson surfaced when the
  user asked whether the DFS could anchor a real `IO`-driven
  implementation (parser → algorithm → output): the answer is yes,
  but only with computability throughout.
- **Resolved (Phase 9):** Math/exec layer split. The DFS now
  takes `succ : V → List V` for child enumeration (exec layer, fully
  computable, `(succ v).attach.findSome?` for the inner loop) and
  keeps `visited : Finset V` for the termination measure
  `(Finset.univ \ visited).card` (math layer, no enumeration, just
  membership + complement). `#eval reachableFinding succEx (· == 2) 0`
  on a `Fin 4` example now returns `some (2, [0, 1, 2])`. Callers
  that hold adjacency data in `Finset` form expose a list projection
  at the DFS boundary (the projection itself can stay noncomputable
  in isolation without contaminating the algorithm). The pebble-
  game algorithm layers (`tryReachPebble`, `tryAddEdge`,
  `runPebbleGame`) inherit the pattern via the `-With` variant
  generalization.
- **Lifted to:** DESIGN.md *Pebble-game style island → Math layer /
  exec layer split* + *The `-With` variant pattern* (the design pin
  documents both the splitting rationale and the orientation-
  indexed `toSucc` generalisation that the pebble-game layers use).
- **Status:** resolved.

### [resolved] `[matroid]` `apnelson1/Matroid` has no `Rep` "finrank of span of image = matroid rank" bridge
- **Where it bit:** Phase 14 forward rank count
  (`lem:k-frame-nonzero-monomial-forest`, piece (2)) needs
  `finrank K (span K (v '' Y)) = M.rk Y` for a representation
  `v : M.Rep K W`. The `Rep.span_*` API in
  `Matroid/Representation/Basic.lean` relates spans to closures but has
  no direct finrank=rk lemma (no loogle hit either).
- **Fix:** built it locally as
  `Matroid.Rep.finrank_span_image_eq_rk` in `BodyBar/KFrame.lean`
  (`[M.RankFinite]`): pick a basis `I` of `Y` (`exists_isBasis'`),
  `Rep.isBasis'_iff` gives `v '' Y ⊆ span (v '' I)` + `LinearIndepOn K v
  I`, so spans agree; `finrank_span_set_eq_card` on the LI image plus
  `InjOn.ncard_image` + `IsBasis'.card` collapse to `M.rk Y`. The
  cycle-matroid specialization
  `Graph.finrank_span_signedIncMatrix_eq_cycleMatroid_rk` follows since
  `⇑(cycleMatroidRep K) = signedIncMatrix` by `rfl`.
- **Upstream-eligible** to `apnelson1/Matroid` (a fact about its `Rep`),
  not mathlib — the package isn't a `Mathlib/` mirror target, so it
  lives in `KFrame.lean` for now.
- **Status:** resolved (project-local). Migrated from `FRICTION.md` in
  the post-Phase-14 cleanup round (D2): resolution indexed by the named
  `Matroid.Rep.finrank_span_image_eq_rk` decl in `KFrame.lean`.

### [resolved] `[matroid]` `apnelson1/Matroid` has no ring-hom naturality lemma for `signedIncMatrix`
- **Where it bit:** Phase 14 reverse half, specialization identity
  (`lem:k-frame-specialize-identity`). To specialize the
  indeterminate-coefficient `k`-frame rows over `R = MvPolynomial …`
  down to `ℚ` (and to lift `kFrameRow` over `K` from the `R`-row
  `kFrameRowR`) I needed `(fun x ↦ φ (signedIncMatrix R e x)) =
  signedIncMatrix S e` for a ring hom `φ : R →+* S`. The package has
  `signedIncMatrix_apply_of_{mem,not_mem}` but no `map`/naturality lemma.
- **Fix:** built `Graph.signedIncMatrix_map` locally in
  `BodyBar/KFrame.lean`. Two-case `by_cases e ∈ E(G)`: off the edge set
  both sides are `0`; on it, `signedIncMatrix_apply_of_mem` exposes
  `update 0 _ 1 - update 0 _ 1`, and `φ` commutes with `sub`/`update 0 _
  1` (entries in `{0, ±1}`) — a 4-way `by_cases` on `x` vs the two
  endpoints + `simp_all [Function.update_apply]` closes it.
- **Upstream-eligible** to `apnelson1/Matroid` (a fact about its
  `signedIncMatrix`), not mathlib; lives in `KFrame.lean` for now,
  beside `signedIncMatrix`'s other Phase-14 consumers.
- **Status:** resolved (project-local). Migrated from `FRICTION.md` in
  the post-Phase-14 cleanup round (D2): resolution indexed by the named
  `Graph.signedIncMatrix_map` decl in `KFrame.lean`.

### [resolved] `Finset.sum_ite_eq'` silently no-ops on `∑ x, c · (if x = a then 1 else 0) · g x`
- **Where it bit:** `BodyBarFramework.rigidityRow_eq` in
  `BodyBar/TayTheorem.lean` (Phase 15 converse rank bound). Expanding a
  signed-incidence row `∑ x, b·((ite_v − ite_u))·m x` to `b·(m v − m u)`,
  the `simp only [Finset.sum_ite_eq', …]` left the sum uncollapsed and
  the linter flagged `Finset.sum_ite_eq'` (and most siblings) as
  *unused* — the indicator was wrapped in a constant factor `b` and a
  trailing `m x`, so it never reached the `∑ x, if x = a then f x else 0`
  shape the lemma matches.
- **Friction:** several build cycles tuning the simp set before realizing
  the collapse lemma fires only on a *bare* indicator summand.
- **Resolution:** factor the constant out with `← Finset.mul_sum` first,
  then `ite_mul` / `one_mul` / `zero_mul` normalize the summand to a bare
  indicator, after which `Finset.sum_ite_eq'` collapses it.
- **Status:** resolved (cross-cutting idiom). Migrated from `FRICTION.md`
  in the post-Phase-15 cleanup round (D2): resolution lifted to
  TACTICS-GOLF § 10, indexed by `rigidityRow_eq`.
- **Lifted to:** TACTICS-GOLF § 10.

### [resolved] Restating a `Pi.single`-indexed subterm in a standalone `have` fails to elaborate
- **Where it bit:** `BodyBarFramework.stdFramework_rigidityRow_eq` in
  `BodyBar/TayTheorem.lean` (Phase 15 block-diagonal rank count). The
  goal contained `∑ c, Pi.single (j e) (signedIncMatrix ℝ e) c x *
  (m x).ofLp c`; an attempted helper `have hinner : ∀ x, (that sum) =
  signedIncMatrix … x * (m x).ofLp (j e)` failed with *"Function
  expected at `Pi.single …`"* even though the identical subterm in the
  goal type-checked.
- **Friction:** the goal's `Pi.single` motive (family type `Fin d →
  (α → ℝ)`) was pinned by the lemma that produced it
  (`blockPairing_apply`, whose statement fixes `w : Fin d → α → ℝ`);
  restating it standalone strips that context and the elaborator picks
  the wrong family.
- **Resolution:** operate on the goal in place — `rw [Finset.sum_congr
  rfl fun x _ => Finset.sum_eq_single …]` collapses the inner sum where
  the motive stays pinned. No standalone `have` of the subterm.
- **Status:** resolved (project-internal lesson). Sibling of the
  FunLike/PiLp "acts like a function but isn't" family
  (TACTICS-QUIRKS §9, §12). Migrated from `FRICTION.md` in the
  post-Phase-15 cleanup round (D2): resolution lifted to TACTICS-QUIRKS
  § 24, indexed by `stdFramework_rigidityRow_eq`.
- **Lifted to:** TACTICS-QUIRKS § 24.

### [resolved] `refine h.trans ?_` over a defeq-but-not-syntactic iff side
- **Where it bit:** `Graph.BodyHingeFramework.edgeMultiply_isSparse_iff`
  (`BodyBar/BodyHinge.lean`, Phase 16). The transport helper
  `exists_toBodyBar_iff` produces an iff whose LHS is the body-hinge
  existential up to `def`-unfolding (`F.IsIndependent` ↦
  `F.toBodyBar.IsIndependent`) and binder-shape (`∃ (_ : p), q` vs
  `p ∧ q`). `refine (exists_toBodyBar_iff …).trans ?_` failed with a
  *"has type `A ↔ ? `, expected `A' ↔ …`"* type mismatch — `Iff.trans`
  matches its component against the goal's LHS only up to reducible
  transparency.
- **Friction:** rewrote the proof to `rw [← hsparse]` (a syntactic
  match on the `IsSparse` side from `tay_witness`), then bridged the
  two existentials with `constructor` + the helper's `.mpr`, never
  `.trans`. Each branch then closes by `exact` up to full defeq.
- **Proposed fix:** none needed — `constructor` + `.mp`/`.mpr` is the
  idiom. Cross-cutting, so lifted.
- **Status:** resolved. Migrated from `FRICTION.md` in the post-Phase-16
  cleanup round (D2): resolution lifted to TACTICS-QUIRKS § 25, indexed
  by the consumer decl `edgeMultiply_isSparse_iff`; no Phase-17 forward
  reference (Phase 17 unopened).
- **Lifted to:** TACTICS-QUIRKS § 25.
