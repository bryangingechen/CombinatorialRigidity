# API and tactic friction log — archive

This file holds **resolved project-internal** friction entries that
have been preserved for design history. Migrated out of
[`FRICTION.md`](FRICTION.md) in periodic housekeeping passes (the
first post-Phase-6) — every `[resolved]`-tagged entry moves here
once its resolution has a real index elsewhere:

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

### [resolved] `simp [← smul_sub]` / `simp [add_sub_add_comm]` stalls on the graded-piece screw subtype (RingQuot-built ops not exposed)
- **Where it bit:** `infinitesimalMotions.smul_mem'` in
  `Molecular/RigidityMatrix.lean`, after Phase 18 refactored
  `ScrewSpace k` from the full `ExteriorAlgebra ℝ (Fin (k+2) → ℝ)` to the
  degree-`k` graded piece `↥(⋀[ℝ]^k (Fin (k+2) → ℝ))` (the
  `screwSpace_finrank` coordinatization). The old proof
  `simpa [Pi.smul_apply, ← smul_sub] using Submodule.smul_mem _ c ‹_›`
  stopped firing: `simp` could not rewrite `c • S u - c • S v` to
  `c • (S u - S v)` because the subtype's `Sub`/`SMul` come through the
  exterior-algebra `RingQuot` and are not exposed (the build prints
  *"definitions were not unfolded because their definition is not
  exposed: RingQuot.instSub"*).
- **Friction / fix:** don't drive the rewrite through `simp`; build the
  membership and `rw` the algebra identity onto the bound hypothesis —
  `have := Submodule.smul_mem (ℝ ∙ F.supportExtensor e) c this;
  rwa [smul_sub] at this` (and the sibling `add_mem'` keeps
  `simpa [add_sub_add_comm]`, which still fires since `add_sub_add_comm`
  is a generic `AddCommGroup` rewrite that `simp` applies at the
  congruence layer without unfolding the subtype op).
- **Status:** resolved (worked around in-proof; no mirror needed — a
  module-system exposure interaction, not a missing mathlib lemma).
  Migrated from `FRICTION.md` in the post-Phase-18 cleanup round (D3):
  the general lesson ("when a carrier becomes a `Submodule`/subtype over
  a `RingQuot`-built algebra, prefer explicit `rw` of the
  `AddCommGroup`/`Module` identity over `simp [← lemma]`") was lifted to
  TACTICS-QUIRKS § 26, indexed by the consumer decls
  `infinitesimalMotions.smul_mem'` / `add_mem'`.
- **Lifted to:** TACTICS-QUIRKS § 26.

### [resolved] Three surviving `maxHeartbeats` overrides on the `ScrewSpace` carrier (Phase 22l opacity flip) → `notes/ScrewSpaceCarrier-design.md`
- **Symptom (index entry).** `case_cut_edge_realization` (was 400000, `Theorem55.lean`),
  `case_cut_edge_realization_gp` (was 600000, `Theorem55.lean`), `case_II_realization_all_k`
  (was 600000, `CaseII.lean`) carried elevated `set_option maxHeartbeats` because of *diffuse
  typeclass re-elaboration* over the reducible-`abbrev` `ScrewSpace` carrier (§38-class;
  no single extractable hotspot).
- **Status.** **Resolved — 0 overrides remain.** Two halves: (1) **Phase 22l** (closed 2026-06-16)
  flipped `abbrev ScrewSpace`→opaque `def`, giving the carrier a distinct non-reducing head so the heavy
  `↥(⋀^k …)` type-expression no longer re-unfolds at every defeq/`simp`/`rw` motive — two caps to
  default, `_gp` 600000→400000. (2) **Follow-up (2026-06-16):** the `_gp` residual was *not* "intrinsic"
  (the §38 "no extractable hotspot" diagnosis was wrong for the cut-decomposition pair) — profiling
  found a single `nlinarith [hrank₁eq, hrank₂eq]` per `|C|=0/1` arm blind-squaring over the heavy
  `finrank (span …)` atoms (~5.8 s). Feeding `linarith` the one `screwDim 2·(|V|−1)` product explicitly
  (`hkey`) dropped `_gp` 13.8 s→3.7 s and under default; same idiom applied to bare
  `case_cut_edge_realization`. **Molecular `maxHeartbeats` count 3→0.** Diagnosis/spike/FLIP recipe in
  **`notes/ScrewSpaceCarrier-design.md`** (general-`d` "part 2" deferred to Phase 23). **Lifted to:**
  TACTICS-GOLF §17 (nlinarith-over-huge-atoms); cross-ref TACTICS-QUIRKS §38; dispatch records
  `notes/model-experiment.md` rows 167–170.

### [resolved] `le_finrank_span_rigidityRows_of_cut` — fused `finrank_sup_of_inf_eq_bot` dropped the `span_induction + finrank_sup` cost below the 200000 default
- **Where it bit:** `RigidityMatrix.lean:3070` (Phase 22i L4a block-triangular rank-addition brick).
- **Mechanism (profiled).** The whole-file `lean --profile` (cut + splice + pinned bricks) is
  `rewriteSeq`-dominated (~7.8s) with a broad algebraic-TC spread (~15s summed) over
  `Module.Dual ℝ (α → ScrewSpace k)` submodule subtypes, plus `FiniteDimensional` resolution for the
  `finrank_sup`/`finrank_mono` chain. Inside the cut brick specifically the over-budget drivers are:
  (a) the `hkey_id` `Submodule.span_induction` over `Sc` with a `hingeRow_eq_dualMap`/`flowSum`
  `conv_rhs` rewrite per case; (b) the disjoint-sup finrank arithmetic run *three times*
  (`S₁⊓S₂`, then `Sc ⊓ (S₁⊔S₂)`, via `finrank_sup_add_finrank_inf_eq` + `rw [hdisj, finrank_bot,
  add_zero]` + `Submodule.finrank_mono`). **Diagnostic correction:** the task brief quoted the §54
  `letI` instance-diamond comment for this decl, but that comment (`RigidityMatrix.lean:3236`) actually
  precedes `le_finrank_span_rigidityRows_of_splice` (3261), whose override was *removed* by audit
  83d5c5c (now builds at default). The cut brick uses **no** `letI`/`domRestrict`/`AddCommGroup`-diamond
  — its in-source cost comment (3059) is the accurate one (`span_induction + finrank_sup + omega over
  Module.Dual submodules`). So §54 is *not* the lever here.
- **Resolution.** Mirrored `Submodule.finrank_sup_of_inf_eq_bot` in
  `CombinatorialRigidity/Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean` (the fused equality
  `p ⊓ q = ⊥ → finrank ↥(p ⊔ q) = finrank ↥p + finrank ↥q`, proved in two lines via
  `finrank_sup_add_finrank_inf_eq` + `rw [h, finrank_bot, add_zero] + omega`). Refactored 6 disjoint-sup
  call-sites across `RigidityMatrix.lean` (4 sites) and `Pinning.lean` (2 sites); collapsed each
  `have h := finrank_sup_add_finrank_inf_eq …; rw [hdisj, finrank_bot, add_zero]` to a single term.
  The `step1`/`step2` two-branch assembly in the |C|=1 arm became direct `have step := finrank_sup_of_inf_eq_bot …`
  without a `by` block. **Heartbeat result: the 400000 override on `le_finrank_span_rigidityRows_of_cut`
  was removed and the brick builds clean at the default 200000.** The diagnosis's "low–medium confidence"
  was over-cautious — the three `rw`-chain reductions plus eliminating the intermediate `h12`/`hc12`
  `have`s together brought the proof term below budget.
- **Status:** resolved — `set_option maxHeartbeats 400000` removed from
  `le_finrank_span_rigidityRows_of_cut`; the fused lemma is mirrored and its FRICTION entry promoted to
  the Mirrored section below.
- **Mirror file:** `CombinatorialRigidity/Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`.

### [resolved] `disjoint Sc (ker f) ↔ InjOn f Sc` is `LinearMap.disjoint_ker_iff_injOn`, not `disjoint_ker'` (deprecated)
- **Where it bit:** `CaseI.lean` L5a-ii (`finrank_span_rigidityRows_map_extProj_dualMap_of_inter_eq_singleton`),
  deriving `Sc ⊓ ker D = ⊥` from the `InjOn` I had just proved.
- **Friction:** the natural-looking `LinearMap.disjoint_ker'` is `@[deprecated (since := "2025-11-07")]`;
  using it would have ridden a deprecation warning into the commit. The live name is
  `LinearMap.disjoint_ker_iff_injOn : Disjoint p (ker f) ↔ Set.InjOn f p`.
- **Proposed fix:** `disjoint_iff.mp (LinearMap.disjoint_ker_iff_injOn.mpr hInjOn)` (caught by grep before
  the build, no cycle paid).
- **Status:** resolved (named the live lemma).

### [resolved] Chained subtraction fails to parse in Graph scope — the package's scoped `G - S` deleteVerts notation poisons `x - a - b`
- **Where it bit:** `ForestSurgery.lean` L1i (`splitOff_isKDof_of_exists_base_inter_fiber_lt`,
  a `have hexp : D * ((c : ℤ) - 1 - 1) = …`); previously L1h, misattributed to a `set`-bound
  variable (the Phase22i L1h build snag note).
- **Friction:** `unexpected token '-'; expected ')', ',' or ':'` at the *second* minus of any
  iterated `x - a - b` in term/type position, plus downstream bogus `HSub ℤ ℕ (Sort ?)` /
  "expected Prop" errors. Root cause: `Matroid/Graph/Subgraph/Defs.lean`'s
  `scoped notation:51 G:100 " - " S:100 => Graph.deleteVerts G S` — level-100 operands make
  `-` non-chaining while in scope. Single subtractions parse, so the failure looks spurious.
- **Proposed fix:** parenthesize `((x - a) - b)`, or produce the term by rewriting
  (`rw [mul_sub, mul_one]`) instead of writing it in source. Upstream-eligible: the fork
  could lower the operand levels (e.g. `G:51 " - " S:100`) to restore chaining.
- **Status:** resolved (workaround); fork-side notation fix not attempted.
- **Lifted to:** TACTICS-QUIRKS § 48.

### [resolved] Bare `Graph.`-prefix in the `Molecular` namespace — `Graph.rigidContract_vertexSet_inter_eq_singleton` landed in `CombinatorialRigidity.Molecular.Graph`, poisoning downstream `import CaseI`
- **Where it bit:** the post-22j `CaseI.lean` file-split blocker. A downstream file that
  `import`s `CaseI` and re-enters the working namespace (`namespace CombinatorialRigidity.Molecular`
  + `open scoped Graph`) could not parse `V(`/`E(`/`↾`, and `exact_mod_cast` failed in the 4 cut-edge
  `hbrickZ` `have`s (`case_cut_edge_realization{,_gp}`) because bare-ℕ `screwDim k - 1` elaborated as
  `Int.subNatNat` rather than `↑(screwDim k - 1)`.
- **Friction:** the lemma `CaseI.lean:1909` was written `theorem Graph.rigidContract_vertexSet_inter_eq_singleton`
  *inside* `namespace CombinatorialRigidity.Molecular`, so it landed in a **sub-namespace**
  `CombinatorialRigidity.Molecular.Graph` (not root `Graph`). That sub-namespace then captured a
  downstream `open scoped Graph` (resolves `Graph` to the nearest match), so mathlib's root-`Graph`
  scoped notations never activated — hence both the notation parse failure and the `binop%` cast flip.
  The monolith escaped it because its file-head `open scoped Graph` ran before the offending decl.
- **Fix (landed):** pin the decl to `_root_.Graph.rigidContract_vertexSet_inter_eq_singleton`. It is
  the only `Graph.`-prefixed decl in the whole `Molecular` tree and is referenced only inside
  `CaseI` by the relative name `Graph.rigidContract_…` (which now resolves to root `Graph`); no
  blueprint pin, no external caller — the namespace move is self-contained. Standard
  `open scoped Graph` is now transparent downstream (no per-file `_root_`/`local notation` boilerplate).
- **Status:** resolved (root-cause fix in the monolith).
- **Lifted to:** TACTICS-QUIRKS § 56.

### [resolved] `subst h` (h : x = a) eliminates the section body `a`, not the local `x` — use the named-variable form `subst x` to control direction
- **Where it bit:** Phase 22h `case_III_bottom_relabel` (W9b, `CaseI.lean`); after
  `by_cases hxa : x = a` on a destructured-link local `x`, `subst hxa` eliminated the section
  variable `a` (replacing it by `x`), breaking the conclusion's `hingeRow c v ρ'` / `q (a, ·)` tags
  that name `a`.
- **Friction:** the conclusion is stated in the section bodies `a`/`c`; eliminating `a` renames them
  and the goal no longer mentions `a` at all (*"Unknown identifier `a`"* downstream).
- **Fix:** `subst x` (the named-variable form) eliminates the local `x` regardless of the equation's
  orientation, keeping `a`/`c` intact. The complement of the § 4 trap (there you avoid subst; here
  you steer it).
- **Status:** resolved. **Lifted to:** TACTICS-QUIRKS § 4.

### [resolved] A multi-branch `Submodule.span_induction` over a heavy `Module.Dual` span hits the cumulative heartbeat budget — bundle the transport as one `LinearMap` `T` + per-branch `simp only`
- **Where it bit:** Phase 22h `funLeft_dualMap_sub_acolumn_mem_span_rigidityRows` (W9a, `CaseI.lean`);
  a `span_induction` concluding in `span Fva.rigidityRows` over `Module.Dual ℝ (α → ScrewSpace k)`,
  generator case dispatching `by_cases x = a / y = a / else`, each with its own chained big-carrier
  `rw [hingeRow_funLeft_dualMap, hingeRow_swap, hingeRow_comp_single_{tail,off}, …]` — declaration-level
  *"timeout at `whnf`"* (first line) + *"tactic execution"* timeout from the second `by_cases` branch
  on (the first branch starves the rest). The default 200000 budget; the Molecular subsystem carries
  zero `maxHeartbeats` overrides.
- **Resolution:** (1) `set T := (funLeft swap).dualMap - (screwDiff v c).dualMap ∘ₗ (single a).dualMap
  with hT`; the `span_induction` predicate is then the light `T ψ ∈ span …`, so `zero/add/smul` close
  by `map_zero/map_add/map_smul` + `Submodule.{zero,add,smul}_mem` with no heavy-term restatement.
  (2) Per generator sub-case, plain `rw [hxa, hyc]` for the cheap *variable* substitutions only, then
  one `simp only [...]` for the heavy rewrite lemmas (one traversal, not N motive abstractions). Avoid
  `subst h` on `h : x = c` (RHS `c` a lemma binder) — it eliminates `c`; use `rw [h]`. **Lifted to:**
  TACTICS-QUIRKS § 38 (*`span_induction` variant*). Opacity + single-traversal, not a heartbeat bump.

### [resolved] A span/rigidity lemma applied with a heavy-carrier row-family argument `whnf`-times-out — `set f := <family>; clear_value f` first
- **Where it bit:** Phase 22h `case_III_arm_realization` (W7, `CaseI.lean`); the final
  `isInfinitesimallyRigidOn_vertexSet_of_span_le_rigidityRows` applied with
  `(a := fun i : ↥s => Ft.panelRow ends i)`, `Ft = caseIIICandidate G ends q …`, `whnf`-timed-out at
  the application even at `maxHeartbeats 4000000`, while every prior `have` (including the membership
  `hmem`/`hsub`) elaborated instantly.
- **Resolution:** `set f := <heavy family> with hf` then `clear_value f` before the application (the
  family's `LinearIndependent`/span hypotheses auto-fold onto `f`); apply the lemma at the *concrete*
  `(ofNormals G ends q₀).toBodyHinge`, not a `set`-bound abbrev. **Lifted to:** TACTICS-QUIRKS § 38
  (*Row-family-argument variant*). Same medicine as the rest of §38: opacity, not a heartbeat bump.
- **Recurrence (Phase 22j S4, `case_II_realization_all_k`):** the new abstract span-transport brick
  `le_finrank_span_rigidityRows_of_pinned_placement` applied to the heavy `FG`/`FGab` `ofNormals`
  frameworks with inline `fun i => FG.panelRow …` / `fun i => FGab.panelRow Q.ends …` families
  `isDefEq`-timed-out even at `maxHeartbeats 6400000`. Fix: `set rn := …` / `set ro := …` (fvars) for
  the two families, then pass them by `(rn := rn) (ro := ro)`. Here **`set` alone sufficed — no
  `clear_value`** — because the brick takes the families as *explicit named args*, so the opaque fvar
  is matched syntactically rather than inferred. Stating `hbrick`'s `Nat.card … ≤ finrank …` type
  explicitly also helps. The original inline `hrank_lb` dodged this by never unifying a lemma
  *parameter* against `FG.rigidityRows` (`Submodule.finrank_mono hcomb_le` had it syntactically).
- **Recurrence + new variant (Phase 22k L8c-2, `case_I_realization_h65`):** the dominant `whnf`
  blowup was NOT a row-family argument but the **final `∃`-witness assembly** — hand-building the
  `HasGenericFullRankRealization` motive as `⟨Q, …, hrank_eq, …⟩` over the heavy `Q = ofNormals G ends q`
  (+ B2 + `le_antisymm` + `▸`/`set`-fold bookkeeping) `whnf`-timed-out even at 6M, and extracting the
  upstream geometric blocks into helpers did not fix it. Fix: **route the witness through the keystone
  `hasGenericFullRankRealization_of_rigidOn_ofNormals`** (takes the data positionally, builds the `∃`
  internally) — feed it a plain "rigid on `V(G)`" obtained from the combined `Sum.elim` block via
  `isInfinitesimallyRigidOn_vertexSet_of_span_le_rigidityRows`. 6M timeout → 55s clean at 800000.
  Also: `convert h using 1; funext; fin_cases <;> simp` on `Fin`-sub-pair LIs hits *max recursion
  depth* inside the 40-hypothesis producer context — extract to a small-context lemma
  (`triLI_subpairs`) where `funext; fin_cases <;> rfl` is cheap. **Lifted to:** TACTICS-QUIRKS § 38
  (*Final-`∃`-witness-assembly variant*).

### [resolved] `AlgHom.map_det` (not `RingHom.map_det`) for `aeval`-based matrix-det bridges; `mvPolynomialX_mapMatrix_aeval` closes the matrix equation
- **Where it bit:** Phase 22h `linearIndependent_normals_of_algebraicIndependent` (`CaseI.lean`),
  proving `det B = aeval (q∘f) P` where `B = (aeval (q∘f)).mapMatrix (mvPolynomialX ..)`.
- **Friction:** `RingHom.map_det f M` says `f M.det = (f.mapMatrix M).det` — correct direction but
  `RingHom.mapMatrix` doesn't unify with `AlgHom.mapMatrix`. Use `AlgHom.map_det f M` (same statement,
  but `f : S →ₐ[R] T`). The matrix equation `(aeval ...).mapMatrix (mvPolynomialX ..) = B` follows from
  `Matrix.mvPolynomialX_mapMatrix_aeval ℚ B`. `convert this using 2` closes any remaining subgoal.
- **Resolution:** `rw [← hφB, AlgHom.map_det]` where `hφB` is from `mvPolynomialX_mapMatrix_aeval`.
- **Status:** resolved (one callsite; logs the `AlgHom` vs `RingHom` distinction for future det-poly proofs).

### [resolved] Proof-term mismatch between two `by tac` closures — use `let`-bound params in the theorem signature to force term identity
- **Where it bit:** Phase 22h `basisFun3_normalsJoin_sorted_family` (`PanelLayer.lean`); the helper
  `normalsJoin_eq_ιMulti_family_pair h` needed `h` to be term-identical to the `h` inside
  `Finset.card_pair (Fin.ne_of_lt h)` in the conclusion. Providing `h01` as an explicit argument
  (`(h01 : ⟨0⟩ < ⟨1⟩ : Fin (k+2))`) caused `exact normalsJoin_eq_ιMulti_family_pair h01` to time
  out under `fin_cases` because the caller's `h01` and the helper's `h` are two separate `by omega`
  elaborations — syntactically distinct even though propositionally equal.
- **Fix:** Declare the proof as a `let`-binding in the theorem statement: `let h01 : P := by tac`.
  After `intro h01` in the proof body, `h01` IS the closed `by tac` term, so `Finset.card_pair
  (Fin.ne_of_lt h01)` in the goal is literally the same term as in `normalsJoin_eq_ιMulti_family_pair h01`.
  The caller uses `rw [sorted_family_eq hk]` and never supplies the proof objects.
- **Status:** resolved. **Lifted to:** TACTICS-QUIRKS § 42.

### [resolved] "row-LI `⟹ A.mulVecLin` surjective" (full row rank ⟹ the pairing map is onto) is not packaged — compose `LinearIndependent.rank_matrix` + `Submodule.eq_top_of_finrank_eq`
- **Where it bit:** Phase 22g `exists_homogeneousIncidence_of_normals` (`RigidityMatrix.lean`), the
  (R1)-core surjectivity step: from `LinearIndependent ℝ n` (`n : Fin 3 → Fin 4 → ℝ`), the pairing
  map `x ↦ (u ↦ n u ⬝ᵥ x) = (Matrix.of n).mulVecLin` must be surjective so any prescribed pairing
  target has a preimage (the incidence side-conditions of the four witness points).
- **Friction:** mathlib has `LinearIndependent.rank_matrix` (`Matrix/Rank.lean`: row-LI ⟹ `A.rank =
  card m`) and `Matrix.rank = finrank (range mulVecLin)` by definition, but not the one-step "row-LI
  ⟹ `mulVecLin` surjective" corollary. The composition is short — `A.rank = 3`, then `range = ⊤` by
  `Submodule.eq_top_of_finrank_eq` (`finrank (range) = 3 = finrank (Fin 3 → ℝ)`), then
  `LinearMap.range_eq_top`. Two incidental gotchas: the lemma is the **root** `sum_dotProduct` (not
  `Matrix.`/`Finset.`-namespaced); and `(A.mulVec x) u = A u ⬝ᵥ x = x ⬝ᵥ n u` needs `dotProduct_comm`
  to match the `⬝ᵥ n u` orientation (same as the perp-pair entry above). Needed the new import
  `Mathlib.LinearAlgebra.Matrix.Rank`.
- **Status:** resolved (inlined; one callsite, below the mirror bar — the rectangular row-rank API is
  already mirrored in `Mathlib/LinearAlgebra/Matrix/Rank.lean`, see the Phase-14 entries below).

### [resolved] `case_III_eq629_conditional` was minted with one shared index type `ιfam` for all three candidate families — the three genuinely differ; generalize to `ιfam₁ ιfam₂ ιfam₃`
- **Where it bit:** Phase 22g L0 `case_III_hsplit_producer` (`CaseI.lean`) — feeding the three
  candidate families (the `M₁` candidate is `(rn ⊕ Unit) ⊕ ro`; `M₂`/`M₃` differ) to the selection
  capstone `BodyHingeFramework.case_III_eq629_conditional` (`RigidityMatrix.lean`).
- **Friction:** the capstone's `{ιfam : Type*} {fam₁ fam₂ fam₃ : ιfam → …}` forced all three families
  to share one index type, so the producer wouldn't typecheck ("Application type mismatch … `fam₃` /
  `?m`", a universe-disagreement symptom of the unification failure).
- **Resolution:** generalized the capstone to `{ιfam₁ ιfam₂ ιfam₃ : Type*}`, one per family. The
  proof (`(case_III_claim612 …).imp hsel₁ (Or.imp hsel₂ hsel₃)`) is index-agnostic, so the single-type
  constraint was gratuitous; one-line signature change, no proof edit. Project-internal (about the
  capstone), below the upstream-mirror bar.

### [resolved] Swapping a wedge factor at the cost of a sign — `extensor ![a, b] = extensor ![b, -a]` — has no `extensor`/`ιMulti` lemma; go through `ExteriorAlgebra.ι_add_mul_swap`
- **Where it bit:** Phase 22f `inf_range_wedgeFixedLeft` (`Meet.lean`), the `⊇` direction —
  showing `a ∧ b = wedgeFixedLeft a b` also lies in `range (wedgeFixedLeft b)` by exhibiting it as
  `wedgeFixedLeft b (−a)`, i.e. proving `extensor ![b, −a] = extensor ![a, b]`.
- **Friction:** no `extensor`/`ιMulti`-level "swap two factors, negate" lemma; `ring` cannot reorder
  (the exterior algebra is noncommutative). The `2`-extensors must be unfolded to bare products.
- **Resolution (idiom):** `rw [coe_wedgeFixedLeft, coe_wedgeFixedLeft, extensor_apply, extensor_apply,
  ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply]` + a `simp only [List.ofFn_succ, …,
  Fin.succ_zero_eq_one]` to reduce the `![·] 1` index to bare products `ι b * ι (−a) = ι a * ι b`,
  then close with `(eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap a b)).symm` (after
  `map_neg, mul_neg`). The `ι_add_mul_swap : ι a * ι b + ι b * ι a = 0` is the only anticommutativity
  fact needed; one-off, below the upstream-mirror bar.

### [resolved] No `Matrix.det_fin_four`: explicit numeric `Fin 4` determinant via `det_succ_row_zero` + `det_fin_three`
- **Where it bit:** Phase 22e N3a-1 `exists_affineIndependent_panel_incidence`
  (`RigidityMatrix.lean`), proving the `4 × 4` homogenization determinant of the standard
  affine `3`-simplex is `≠ 0`. mathlib ships `Matrix.det_fin_two`/`det_fin_three` but **no
  `det_fin_four`**, so the explicit numeric det does not reduce by a single named lemma.
- **Friction:** `decide` fails (`ℝ` is classical, not a concrete decision procedure); a bare
  `norm_num [det_succ_row_zero, …]` leaves `Fin.succAbove 3 2`-style index residuals unreduced.
- **Resolution (idiom):** rewrite the `Matrix.of (homogenize ∘ p)` to an explicit `!![…]`
  literal (`ext i j; fin_cases i <;> fin_cases j <;> simp [homogenize, Fin.snoc]`), then
  `rw [Matrix.det_succ_row_zero]; simp [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove]`
  — one cofactor expansion down to the `3 × 3` named lemma, with `Fin.succAbove` in the simp set
  to clear the index arithmetic. Closes in one shot once the simp set is right.
- **Status:** resolved (idiom). `Matrix.det_fin_four` would be upstream-eligible if the `Fin 4`
  numeric-det pattern recurs; for one site the cofactor idiom is enough.

### [resolved] The orientation flip `hingeRow u v r = hingeRow v u (-r)` was an inline `LinearMap.ext fun S => by rw […]` in three rigidity-row span proofs — named as `hingeRow_swap`
- **Where it bit:** `span_panelRow_eq_rigidityRows` + `span_panelRow_linking_eq_rigidityRows`
  (`Pinning.lean`, Phase 22) and the new `span_rigidityRows_eq_sup_span_panelRow_edge` (`Pinning.lean`,
  Phase 22d Gap-1). Each handles the swapped orientation of a generating rigidity row (endpoints match
  a link only up to swap, `IsLink.eq_and_eq_or_eq_and_eq`) and inlines the *same*
  `show hingeRow u v r = hingeRow v u (-r) from LinearMap.ext fun S => by rw [hingeRow_apply,
  hingeRow_apply, LinearMap.neg_apply, ← map_neg, neg_sub]` proof term.
- **Friction:** a 3-line `LinearMap.ext`-with-`rw`-chain for one mathematical fact (reversing an
  oriented edge negates the block row), reproduced verbatim three times — the multi-rewrite-for-one-fact
  smell.
- **Fix:** named theorem `BodyHingeFramework.hingeRow_swap` in `RigidityMatrix.lean` (where `hingeRow`
  lives), `hingeRow u v r = hingeRow v u (-r)`. All three callsites collapse to a `rw [hingeRow_swap]`.
- **Status:** resolved (project helper `hingeRow_swap`).

### [resolved] A hinge row restricted to a body's screw column — named `hingeRow_comp_single_tail` / `_off`; and `(∑ f).comp g` has no distributing simp lemma (go pointwise)
- **Where it bit:** the eq.-(6.44) node `candidateRow_ac_eq_neg` (`RigidityMatrix.lean`, Phase 22e N8).
  It regroups the eq.-(6.43) vanishing combination by which edge each term sits on; the surviving
  `a`-column terms are the `ab`/`ac`-rows (degree-2-at-`a`). The two restrictions are
  `(hingeRow a b ρ).comp (single a) = ρ` (tail = body `a`) and `(hingeRow u w ρ).comp (single a) = 0`
  (`a ∉ {u,w}`), each a `LinearMap.ext fun x => rw [comp_apply, hingeRow_apply, single_apply,
  Pi.single_eq_same / Pi.single_eq_of_ne, …]` one-liner.
- **Friction:** two distinct one-step facts (column restriction of a hinge row) + a tarpit closing
  the cancellation: `(∑ j, c j • hingeRow a b (rab j)).comp (single a) = ∑ j, c j • rab j` does **not**
  fall to `simp [LinearMap.smul_comp, …]` — there is no `LinearMap.sum_comp` (comp does not distribute
  over a `Finset.sum` in its *left* argument via a named simp lemma), and `map_sum` won't fire on the
  `∑` because `· ∘ₗ single` isn't recognized as the hom being mapped. Lost two `lean_multi_attempt`
  rounds chasing the comp-over-sum rewrite.
- **Fix:** named the two column-restriction leaves `hingeRow_comp_single_tail` / `hingeRow_comp_single_off`
  (`RigidityMatrix.lean`, where `hingeRow` lives). For the cancellation, **go pointwise** —
  `LinearMap.ext fun x => …; have := LinearMap.congr_fun hcol x; simpa only [add_apply, comp_apply,
  sum_apply, smul_apply, <tail-restriction at x>, zero_apply] using this`. Pointwise sidesteps the
  missing comp-over-sum lemma entirely.
- **Lesson:** `(∑ i, f i).comp g` (or any LinearMap identity with a `∘ₗ` outside a `Finset.sum` in the
  left slot) is best discharged pointwise via `LinearMap.ext` + `LinearMap.congr_fun` + `sum_apply`,
  not by hunting a `sum_comp`-style distribution lemma. **Lifted to:** TACTICS-GOLF (comp-over-sum →
  pointwise).
- **Status:** resolved (helpers `hingeRow_comp_single_{tail,off}`; pointwise idiom).

### [resolved] The per-edge panel-row span finrank `= D − 1` computation (`span_panelRow_edge_eq` + `equivMapOfInjective.finrank_eq` + `finrank_hingeRowBlock`) appeared twice — named as `finrank_span_panelRow_edge`
- **Where it bit:** `exists_independent_panelRow_subfamily_of_edge` (`Pinning.lean`, Phase 22c) and
  the new `exists_redundant_panelRow_of_edge_of_finrank_lt` (`CaseI.lean`, Phase 22d Gap-1). Both
  need "the per-edge panel-row span `span {panelRow ends (e, ·, ·)}` has finrank `D − 1`".
- **Friction:** a 4-line rewrite chain (`span_panelRow_edge_eq` → image-preserves-finrank via
  `Submodule.equivMapOfInjective` along `dualMap_injective_of_surjective`/`screwDiff_surjective` →
  `finrank_hingeRowBlock`) reproduced verbatim — the multi-rewrite-for-one-fact smell.
- **Fix:** named lemma `BodyHingeFramework.finrank_span_panelRow_edge` in `Pinning.lean` (where the
  per-edge span lives), `huv`/`hne` ⟹ `finrank (span e-block) = screwDim k − 1`. Both callsites
  collapse to one `exact`.
- **Status:** resolved (project helper `finrank_span_panelRow_edge`).

### [resolved] The `extProj`-dual-map matrix entry `M j l = φ (D (φ⁻¹ eₗ)) j` is rational — extract a *generic* `dualMap_matrix_entry_eq` helper; unfolding `φ` in place `whnf`/`isDefEq`-times-out on `Module.Dual ℝ (α → ScrewSpace k)`
- **Where it bit:** `exists_rankPolynomial_of_rigidOn_linking_set_proj`'s rationality conjunct
  (`Molecular/AlgebraicInduction/CaseI.lean`, Phase 22d (ii-a)). The projected coordinate
  `cD i j = ∑ l, C(M j l) · c i l` is rational iff each matrix entry
  `M j l = φ (D (φ⁻¹ (Pi.single l 1))) j` (`φ` the dual-standard basis iso, `D = (extProj proj).dualMap`)
  is — and `extProj` is a `0`/`proj` projection, so `M j l ∈ {0,1}`.
- **Friction:** unfolding `φ` (`hφ`) + `dualBasis_equivFun` + `dualMap_apply` *in place* inside the
  178 KB file's giant proof context blows the 200 K-heartbeat budget at `isDefEq`/`whnf` on the
  concrete `Module.Dual ℝ (α → ScrewSpace k)` — the same heavy-dual trap as the
  `coord_linearMap_eq_matrix_mulVec` helper (and FRICTION *basis-coercion `map'` over `Module.Dual`*).
- **Fix:** factor the entry computation into a **generic private lemma** stated over an abstract
  `b : Basis ι R W` / `e : Fin n ≃ ι` / `f : W →ₗ[R] W` (no concrete dual):
  `dualMap_matrix_entry_eq : φ (f.dualMap (φ⁻¹ (Pi.single l 1))) j = b.dualBasis (e l) (f (b (e j)))`,
  `φ := b.dualBasis.equivFun.trans (funCongrLeft R R e)`. It elaborates in isolation; the call site
  then only reasons about `b.dualBasis (e l) (extProj proj (B (e j)))` (a Kronecker `0`/`1`).
  `equivFun`/`dualBasis` need `[Finite ι] [DecidableEq ι]` in the *statement* (`Fintype.ofFinite` in
  the proof, else `unusedFintypeInType` fires). **Lifted to:** TACTICS-QUIRKS § 38.
- **Status:** resolved (helper `dualMap_matrix_entry_eq`).

### [resolved] Independence of the pin-a-body column family `panelRow ∘ₗ single v` (N7b-3's `hnewpin`) — strip the shared dual map via `of_comp`, don't fight `map'`
- **Where it bit:** `linearIndependent_panelRow_comp_single_of_edge`
  (`Molecular/AlgebraicInduction/Pinning.lean`, Phase 22c stratum-1 leaf). N7b-1 gives panel rows
  on one edge `e` independent; N7b-3's `hnewpin` wants the same rows independent *after*
  `.comp (LinearMap.single ℝ _ (ends e).1)` (read through body `v = (ends e).1`'s screw column).
- **Friction:** the WANT family is `single`-postcomposed, so `LinearIndependent.map'` is the wrong
  direction (it needs a map *into* the WANT family, injective on the span — not available). Also
  `LinearMap.single` silently needs `[DecidableEq α]` in the lemma *statement* (matching N7b-3).
- **Fix:** since all rows share the *one* edge `e`, they share one relative-screw evaluation
  `screwDiff (ends e).1 (ends e).2`; the pin-at-`v` identity `hingeRow v w r ∘ₗ single v = r`
  (`w ≠ v`, via `Pi.single_eq_same`/`Pi.single_eq_of_ne`) makes the panel rows the
  `(screwDiff …).dualMap`-images of the WANT family. `LinearIndependent.of_comp (… .dualMap)` then
  strips the (injective, `screwDiff_surjective`) dual map and returns the WANT independence. The
  whole thing is `refine of_comp … ; have heq : dualMap ∘ WANT = panelRow := …; rw [heq]; exact hindep`.
- **Status:** resolved (project helper `linearIndependent_panelRow_comp_single_of_edge`).

### [resolved] The eq. (6.12) single-seed coupling: reconcile the IH's existential `ofNormals … q` seed with the one shared `q₀ = update q v (…)` via `ofNormals_update_eq_withNormal` + the `withNormal` null-space invariance
- **Where it bit:** `case_II_placement_eq612` (`Molecular/AlgebraicInduction/CaseI.lean`, Phase 22c
  stratum-1 producer), step (1). The N7b-0/2 bricks consume `ofNormals Gᵥ ends q₀` on the *shared*
  seed `q₀`, but the IH (`exists_rigidOn_ofNormals_of_hasFullRankRealization`) delivers rigidity at
  its *own* seed `q`; `q₀` overrides only `v`'s coordinates.
- **Friction:** `ofNormals` takes a *free assignment* `q : α × Fin (k+2) → ℝ`, `withNormal` a
  *per-body* override `n : Fin (k+2) → ℝ` — different shapes, no direct bridge. The seed `q₀ :=
  fun p ↦ if p.1 = v then n p.2 else q p` (uncurried `update`) had to be shown equal to
  `(ofNormals Gᵥ ends q).withNormal v n` before the null-space invariance lever applies.
- **Fix:** new glue `ofNormals_update_eq_withNormal` (`PanelHinge.lean`, `mk.injEq` + a `by_cases a = v`
  on the `normal` field). Then `toBodyHinge_withNormal_infinitesimalMotions_eq` (its `hv` holds
  because `v ∉ V(Gᵥ)` ⟹ no `Gᵥ`-edge endpoint is `v`) gives equal `infinitesimalMotions`, and
  `IsInfinitesimallyRigidOn` transports through `mem_infinitesimalMotions` (no congruence lemma —
  the same round-trip as the line-167 entry below). `withNormal_supportExtensor_of_ne` likewise
  transports the transversal-hinge hypothesis to `q₀`.
- **Status:** resolved (project helper `ofNormals_update_eq_withNormal`).

### [resolved] The repeated inline "a `panelRow` whose edge links is a rigidity row" membership — named as `panelRow_mem_rigidityRows`
- **Where it bit:** the block-triangular Case-I composer (`hrow_mem`, `CaseI.lean:1764`) and
  `case_II_placement_eq612`'s membership branch both discharge the same fact:
  `F.graph.IsLink i.1 (ends i.1).1 (ends i.1).2 → F.panelRow ends i ∈ F.rigidityRows`.
- **Friction:** a 6-line inline proof (`⟨e', …, annihRow …, hingeRowBlock_apply +
  mem_dualAnnihilator + annihRow_apply_self⟩`) copy-pasted across producers — the API-gap signal.
- **Fix:** named lemma `BodyHingeFramework.panelRow_mem_rigidityRows` in `Pinning.lean` (where
  `panelRow` lives). The block-triangular composer's inline `hrow_mem` is a candidate to refactor
  onto it in a later cleanup pass (left as-is this commit to keep the diff scoped).
- **Status:** resolved (project helper `panelRow_mem_rigidityRows`).

### [resolved] A `(α → ScrewSpace k) →ₗ[ℝ] (α → ScrewSpace k)` defined by a `where`/`toFun` with an `if … then 0 else S a` body leaves the Pi-fiber `Module` stuck (and the `if` needs `Decidable` in the *statement* of any `_apply` lemma)
- **Where it bit:** the block-triangular reframing's exterior-column projection `extProj`
  (`Molecular/AlgebraicInduction/`, Phase 22a §1.14, Piece B). Both the structure-`where` form
  (`toFun S := fun a => if a ∈ t then 0 else S a`) and a separate `extProj_apply` `= if a ∈ t then …`
  lemma fail: the `where` leaves *"failed to synthesize Module ?m …"* on the Pi fiber under the
  `public section` (`0 : ScrewSpace k` doesn't pin the fiber, sibling of TACTICS-QUIRKS § 30), and the
  `if a ∈ t` in the `_apply` *statement* needs `Decidable (a ∈ t)` — which `classical` (a *proof*
  tactic) cannot supply for a statement.
- **Fix:** build the map as `LinearMap.pi fun a => if a ∈ t then (0 : (α → W) →ₗ[ℝ] W) else
  LinearMap.proj a` (the whole-`LinearMap` `0`/`proj` ascription pins the fiber, the §30 fix in `pi`
  form), under a `by classical exact …`. State only the branch you need — `extProj_apply_mem (ha : a ∈ t)
  : extProj t S a = 0` (`rw [extProj, LinearMap.pi_apply, if_pos ha, LinearMap.zero_apply]`) — so no
  `Decidable` appears in any statement.
- **Status:** resolved (`LinearMap.pi` + branch-specific `_apply_mem`).

### [resolved] A `def`/`theorem` that "looks" top-level is actually under `namespace BodyHingeFramework` — referencing it bare from a sibling file fails "Unknown identifier"
- **Where it bit:** wiring the L-wire columnOp bridge (Phase 22g). `columnOp` /
  `comp_columnOp_comp_single` sit between `namespace BodyHingeFramework` (`RigidityMatrix.lean:348`)
  and its `end`, so their full names are `BodyHingeFramework.columnOp` etc. — `columnOp (k := k) hva`
  written in `CaseI.lean` (same `…Molecular` file namespace, but *not* inside `BodyHingeFramework`)
  failed "Unknown identifier `columnOp`", while a theorem *mentioning* it elaborated fine (the name
  is in the theorem's already-checked type, not looked up).
- **Fix:** qualify (`BodyHingeFramework.columnOp`, `BodyHingeFramework.comp_columnOp_comp_single`),
  or for a decl whose first explicit arg is the `F : BodyHingeFramework`, use dot notation
  (`F.linearIndependent_sum_p2_candidateRow`). Same root lesson as the entry below + TACTICS-QUIRKS
  §35: a build-error "Unknown identifier"/"Invalid field" on a sibling-file decl is almost always an
  enclosing-namespace mismatch — check whether the def is inside a `namespace` block.
- **Status:** resolved (qualified the references). **Lifted to:** TACTICS-QUIRKS § 35.

### [resolved] Dot notation `g.foo` doesn't find a `Graph.foo` lemma authored outside a `namespace Graph` block — it re-namespaces to `…Molecular.Graph.foo`, which projection can't reach
- **Where it bit:** the Case-I composer `case_I_realization` (`Molecular/AlgebraicInduction/`,
  Phase 22a N6-G3-G3c-iii-b). A scratch `theorem Graph.exists_ends_of_graph` written under the file's
  enclosing `CombinatorialRigidity.Molecular` namespace landed at `…Molecular.Graph.exists_ends_of_graph`;
  `G.exists_ends_of_graph` then failed with "environment does not contain `Graph.exists_ends_of_graph`"
  although `Graph.exists_ends_of_graph G` (the open-namespace identifier) type-checked.
- **Fix:** the project already had `Graph.endsOf` (in a real `namespace Graph` block in
  `Molecular/Induction/`) + `isLink_endsOf` doing exactly this job, so the helper was dropped and
  the composer reuses `endsOf` (search-before-rolling-your-own; cross-ref the existing `endsOf` entry
  below). The general dot-notation-vs-root-namespace lesson is lifted.
- **Status:** resolved (reused `endsOf`). **Lifted to:** TACTICS-QUIRKS § 35.

### [resolved] The fork's `Graph.Simple` API has no `map`-simplicity lemma — `map` is the one op that breaks `Simple`, so it needs a *conditional* criterion, not an instance
- **Where it bit:** G2b (`rigidContract_simple`, Phase 22a). Needed `(G.rigidContract H r).Simple` where
  `rigidContract = (G ＼ E(H)).map (collapseTo r V(H))`. The fork's `Matroid/Graph/Simple.lean` has
  `Simple` *instances* for `↾`/`＼`/`-`/induce/`noEdge`/`singleEdge` and `Simple.mono` for subgraphs, but
  **nothing for `map`** — and rightly so: vertex-relabel can manufacture both loops (collapse an edge's
  endpoints) and parallel edges (collapse two edges onto one pair), so `(f ''ᴳ G).Simple` is conditional,
  not an instance.
- **Proposed fix:** the positive criterion `Graph.map_simple` — `(f ''ᴳ G).Simple` from
  `hloop : ∀ e x y, G.IsLink e x y → f x ≠ f y` (no edge becomes a loop) and
  `hpar : ∀ e₁ e₂ x₁ y₁ x₂ y₂, G.IsLink e₁ x₁ y₁ → G.IsLink e₂ x₂ y₂ → f x₁ = f x₂ → f y₁ = f y₂ → e₁ = e₂`
  (no two edges collapse to one pair). Proof is a two-field anonymous constructor: `rw [map_isLoopAt]` /
  `rw [map_isLink]` then `rintro`/`obtain` and apply the hypothesis. Lives project-side in `Induction/`
  (alongside `rigidContract`) per *prefer the project-side route*; **upstream-eligible** as a fork-side
  `Graph.map_simple` if the fork's `Simple` API is revisited.
- **Contrapositive companion (Phase 22k, L8a):** the Lemma-6.5 arm needs to *unpack* a
  non-simple contraction, so the negative form `map_not_simple` / `rigidContract_not_simple` joined
  the positive criterion (same file, just after `rigidContract_simple`). It is the mechanical
  `by_contra` + `map_simple` of the two disjuncts (loop: `∃ e x y, IsLink ∧ f x = f y`; parallel:
  `∃ … e₁ ≠ e₂` with collapsed-equal end-pairs). **Caveat:** the loop disjunct cannot carry `x ≠ y`
  — a `map`-level statement makes *no* looplessness assumption on the source `G`, so the underlying
  `G`-edge may be a genuine loop; a caller with `G.Simple` recovers `x ≠ y` from `IsLink.ne` itself.
  (General lesson: a `map`/relabel-level lemma must not bake in a source-graph `Loopless`/`Simple`
  hypothesis the statement doesn't take — push that recovery to the simple-graph caller.)
- **Step-2 extraction consumer (Phase 22k, L8a):** `exists_isLink_pair_of_rigidContract_not_simple`
  (same file) turns `rigidContract_not_simple`'s two-disjunct unpacking into Claim 6.6's
  conclusion — a vertex `v ∉ V(H)` with two distinct edges into `V(H)` — given `G.Simple` + the
  edge-saturation hyp `hHsat` (every `G`-edge inside `V(H)` lies in `E(H)`). The loop disjunct is
  vacuous (a both-ends-in-`V(H)` surviving edge would be in `E(H)`); the parallel disjunct's
  shared-`v` extraction reads off the auxiliary brick `collapseTo_eq_imp_mem_of_ne` (with the
  representative `r ∈ V(H)`, `collapseTo r V(H)` merges two *distinct* vertices only when both lie
  in `V(H)`). Caller supplies `hHsat` from `induce` (the §1.70(c′) saturation).
- **Status:** resolved (project-side `map_simple`/`map_not_simple` + `rigidContract_simple`/
  `rigidContract_not_simple` + `exists_isLink_pair_of_rigidContract_not_simple` consumers;
  fork-API gap noted for potential upstream).

### [resolved] `obtain ⟨a, t⟩ := e j` on a *term* (not a hypothesis) doesn't substitute the term's other occurrences — use `rcases hej : e j with ⟨a, t⟩` then `simp only [hej]`
- **Where it bit:** `exists_rankPolynomial_of_rigidOn` (Phase 22, Case-I per-leg rank polynomial), the
  coordinatization `hg : φ (g q i) j = eval q (c i j)`. After `rw [hc_def]` the RHS panel polynomial
  reads `c i j`, whose body refers to `(e j).1` / `(e j).2` (the reindexed basis vector). The `change`
  surfacing the LHS row turned `e j`-on-the-LHS into `a`, but `obtain ⟨a, t⟩ := e j` left the RHS
  `(e j).1` / `(e j).2` untouched — `obtain`/`rcases` on a *bare term* case-splits but does **not**
  rewrite the term's occurrences elsewhere in the goal — so the `by_cases` arithmetic faced
  `a` (LHS) vs `(e j).fst` (RHS) and left unsolved goals. One build cycle.
- **Proposed fix:** `rcases hej : e j with ⟨a, t⟩` (records `hej : e j = ⟨a, t⟩`), then `simp only [hej]`
  to substitute every `e j` occurrence by `⟨a, t⟩` (the `.fst`/`.snd` projections reduce to `a`/`t`),
  *then* the `change`/`rw` chain. General rule: to destructure a term and have its projections
  collapse goal-wide, capture the equation (`rcases h : t with …`) and `simp only [h]`; a bare
  `obtain ⟨…⟩ := t` only helps when `t` is a local hypothesis. (Sibling of TACTICS-QUIRKS § 4.)
- **Status:** resolved (tactic choice; no lemma needed). **Lifted to:** TACTICS-QUIRKS § 4 (cross-ref).

### [resolved] The Case-I N6b coupling is NOT a clean assembly of the green bricks — `exists_rankPolynomial_of_rigidOn` needs `hends : ∀ e : β, GH.IsLink e …`, which a proper-subgraph leg cannot satisfy
- **Where it bit:** the recon for N6b (Phase 22, the simple Case-I shared-seed coupling the hand-off
  projected as "the assembly commit, no new analytic brick"). The plan: per leg `GH ≤ G`, apply
  `exists_rankPolynomial_of_rigidOn GH ends …` to get a nonzero rank polynomial, multiply the two
  legs' polynomials × the (G2) general-position factor, take a shared non-root, splice.
- **Friction:** `exists_rankPolynomial_of_rigidOn` (and the whole `panelRow` /
  `span_panelRow_eq_rigidityRows` / `exists_independent_panelRow_subfamily_of_rigidOn` chain) requires
  `hends : ∀ e : β, G.IsLink e (ends e).1 (ends e).2` — *every* edge label of the realized graph must
  link — because the panel rows must span **all** rigidity rows. For a *proper-subgraph* leg `GH ≤ G`
  this is false (labels in `E(G) ∖ E(GH)` don't link in `GH`), and the subgraph direction of `IsLink`
  is `GH ≤ G → GH.IsLink e → G.IsLink e` (supergraph), not the reverse — so a leg's `hends` cannot be
  derived from the parent's. The type-level "feed the green bricks together" plan was blind to the
  `β`-quantification. So N6b is *not* a one-commit assembly; it needs a leg-restricted rank polynomial
  (the genuine remaining content of `lem:case-I-splice-placement`).
- **Proposed fix:** decompose math-first. First decomposable green brick landed:
  `PanelHingeFramework.infinitesimalMotions_ofNormals_eq_of_ends_swap` (leg rigidity is invariant under
  swapping an edge's two endpoints, via the span-keyed `infinitesimalMotions_eq_of_isLink_span_supportExtensor`
  + the anti-symmetry `panelSupportExtensor_swap`), which begins re-expressing a leg's IH rigidity at
  the parent's `ends`. The full coupling stays red.
- **Status:** resolved (recon finding recorded; the bricks it surfaced are the path forward). Rule →
  `DESIGN.md` *Constructibility recon before scheduling a producer build* (a fresh application: read the
  *quantifier domain* of a brick's hypotheses, not just its conclusion shape). See `notes/Phase22a.md`
  *Blockers* / *Hand-off*.

### [resolved] `[matroid]` `H.cycleMatroid = G.cycleMatroid ↾ E(H)` for `H ≤ G` — route through `cycleMatroid_isRestriction_of_le` + `IsRestriction.exists_eq_restrict`, then pin the restriction set by ground equality
- **Where it bit:** the rank-saturation specialization `union_cycleMatroid_rk_saturated_of_isKDof_zero`
  (Phase 22, N4c crux input II): needed `G̃.cycleMatroid.rk E(H̃) = H̃.cycleMatroid.rk E(H̃)` to
  compute the connected-graph cycle rank `|V(H)| − 1` in `H̃` (where the conclusion of
  `Connected.eRk_cycleMatroid_restrict_add_one` lands on `V(H)`, not `V(G)`).
- **Friction:** there is no vendored `cycleMatroid_eq_restrict_of_le`. The vendored
  `cycleMatroid_isRestriction_of_le (h : G ≤ H) : G.cycleMatroid ≤r H.cycleMatroid` gives only the
  `≤r` relation; `IsRestriction.exists_eq_restrict` then yields `∃ R, R ⊆ … ∧ H.cyc = G.cyc ↾ R`,
  and the restriction set `R` must be pinned to `E(H)` by `congrArg Matroid.E` (the restriction's
  ground equals `R`, the subgraph's cycle matroid ground equals `E(H)`).
- **Proposed fix:** project helper `Graph.cycleMatroid_mulTilde_eq_restrict` (Induction/) packages
  this for the `mulTilde` case; combine with `Matroid.restrict_rk_eq _ subset_rfl` to move a rank
  across the subgraph. Reusable whenever a connected-component rank must be read in the smaller graph.
- **Status:** resolved (project helper).

### [resolved] The `Set.ncard` of a finite-index `iUnion` is `≤ ∑ ncard` via `Set.ncard_iUnion_le_of_fintype` — don't hand-roll through `toFinset`/`card_biUnion_le`
- **Where it bit:** N4c crux input `Matroid.Union_pow_isBasis'_split_of_rk_saturated` (Phase 22):
  the counting step `|⋃ Jᵢ| ≤ ∑ |Jᵢ|` over `Jᵢ : Fin k → Set α`.
- **Friction:** first hand-rolled it via `Fintype.ofFinite α` + `Set.ncard_eq_toFinset_card'` +
  `Set.toFinset_iUnion` + `Finset.card_biUnion_le` (4 rewrites). The single lemma
  `Set.ncard_iUnion_le_of_fintype : (⋃ i, s i).ncard ≤ ∑ i, (s i).ncard` (only `[Fintype ι]`,
  *no* finiteness/pairwise hyp) does it in one term. Sibling of the existing line-379 entry on
  `Set.ncard_iUnion_of_finite` (the `∑ᶠ` *equality* form), but the *inequality* form is cleaner
  here since the packing argument never needs disjointness.
- **Proposed fix:** `hJunion ▸ Set.ncard_iUnion_le_of_fintype J`.
- **Status:** resolved (no mirror; the lemma is in mathlib). Lesson: `lean_local_search` /
  `exact?` for the exact `ncard` shape *before* converting to `Finset`.

### [resolved] `map_sum` won't push `Basis.repr` (a `LinearEquiv` to `Finsupp`) through a `∑` — route the coordinate through the `ℝ`-valued composite `Finsupp.lapply t ∘ₗ repr.toLinearMap`
- **Where it bit:** B0 sub-commit 2 `panelSupportPoly_eval` (Phase 21b): pushing the `⋀^k`-basis
  coordinate `repr (complementIso (∑ s, c s • b₂ s)) t` through the sum to read it off term-by-term.
  `rw [map_sum]` reports "Did not find an occurrence of the pattern `?g (∑ …)`" on the `repr (∑ …)`;
  forcing it (`rw [map_sum (b.repr)]`) instead fails with "failed to synthesize
  `AddMonoidHomClass (M ≃ₗ[R] (ι →₀ R))`" / a typeclass timeout. The `Finsupp` codomain of
  `Basis.repr` blocks the `AddMonoidHomClass` synthesis `map_sum` needs, so it silently won't unify.
- **Fix:** the coordinate is the `ℝ`-valued functional `Finsupp.lapply t ∘ₗ b.repr.toLinearMap`; fold
  the outer linear maps (`complementIso`) into one composite and rewrite the whole coordinate to it by
  `rw [show repr (L (∑ …)) t = (Finsupp.lapply t ∘ₗ repr.toLinearMap ∘ₗ L.toLinearMap) (∑ …) from rfl,
  map_sum]`, then `Finset.sum_congr` + per-term `map_smul` / `LinearMap.comp_apply` /
  `Finsupp.lapply_apply`. The `show … from rfl` holds because `Finsupp.lapply t (g x) = g x t`
  definitionally. **Lifted to:** TACTICS-QUIRKS § 34.
- **Status:** resolved; sibling of the B0 sub-commit-1 coordinate entry above. General axis: a
  `map_sum`/`map_smul` that silently won't match a `Basis.repr`-of-a-sum is the `Finsupp`-codomain
  class synthesis failing — compose with `Finsupp.lapply t` to drop to the scalar ring first.

### [resolved] `rw [hsub]` over a `Submodule` equation under `finrank ℝ ↥(…)` trips the motive — rewrite the *hypothesis* with the reversed equation instead
- **Where it bit:** the multivariate genericity device `exists_good_realization` (Phase 21b). The
  engine returns `hp : … + finrank ℝ ↥(span (range (g p))).dualCoannihilator ≤ finrank V`; the goal
  carries `finrank ℝ ↥(F p).infinitesimalMotions`, and `hcoord p : (F p).infinitesimalMotions =
  (span (range (g p))).dualCoannihilator`. A `rw [hcoord p]` on the *goal* fails with "motive is not
  type correct" — the `Submodule` sits under the `↥`-coercion-to-type inside `finrank`, so the
  rewrite motive `fun S => finrank ℝ ↥S ≤ …` is not type-correct in general.
- **Fix:** rewrite the **hypothesis** in the opposite direction instead:
  `rw […, ← hcoord p] at hp; exact hp`. The `← hcoord p` turns `hp`'s coannihilator into
  `(F p).infinitesimalMotions`, matching the goal; rewriting `at hp` (a `≤`-Prop, not under a
  fresh motive) sidesteps the type-correctness check entirely. **Lifted to:** TACTICS-QUIRKS § 33.
- **Status:** resolved (same family as § 18/20/27 — `rw` motive traps; the new rescue axis is
  "flip the equation and rewrite the hypothesis, not the goal").

### [resolved] Canonical edge endpoint selector `Graph.endsOf` — the repeated `obtain ⟨x, y, hlink⟩ := exists_isLink_of_mem_edgeSet …` pattern
- **Where it bit:** the from-scratch panel realization `PanelHingeFramework.ofParam G ends param`
  (Phase 21b) takes an `ends : β → α × α` selector; Case I needs it consistent with the graph
  (`IsLink e (ends e).1 (ends e).2`). The per-edge endpoint-choice idiom
  `obtain ⟨x, y, hlink⟩ := exists_isLink_of_mem_edgeSet he` recurs ~a dozen times across
  `Molecular/Induction/`, `BodyBar/TreePacking.lean`.
- **Fix:** landed `Graph.endsOf` (`Classical.choice` on the `IsLink` existence, junk off `E(G)`)
  with `isLink_endsOf` (genuine link on every edge) and `endsOf_eq_or_swap` (matches any named link
  up to order, via `IsLink.eq_and_eq_or_eq_and_eq` + `Prod.ext`) in `Molecular/Induction/`.
  The canonical `ends` argument for `ofParam`.
- **Status:** resolved (project-internal `Graph` primitive; `[Inhabited α]` for the junk default).
  Could be mirrored upstream if a use outside the molecular phase appears.

### [resolved] `Basis.linearIndependent.map' W.subtype` over a `Module.Dual` of an exterior power blows up at `whnf` — factor the basis-coercion into an abstract-field mirror lemma
- **Where it bit:** `exists_independent_rigidityRows_of_edge` in
  `Molecular/RigidityMatrix.lean` (Phase 21b Case-I per-edge brick): coercing a
  basis of the hinge-row block `r(p(e)) ≤ Module.Dual ℝ (ScrewSpace k)` out into
  the ambient dual to get `D − 1` independent ambient functionals.
- **Friction:** building the basis inline (`Module.finBasisOfFinrankEq` +
  `b.linearIndependent.map' W.subtype (Submodule.ker_subtype _)`) hit a
  `(deterministic) timeout at whnf` even at `maxHeartbeats 400000` — `ScrewSpace k`
  is `↥(⋀[ℝ]^k …)`, an `abbrev`, and the `.map'` unification + `Module.Free`/`Module.Finite`
  synthesis on `Module.Dual ℝ (ScrewSpace k)` and its submodule force the exterior
  power to whnf-normalize. Even `Module.Free.of_divisionRing` needed `V` given explicitly
  (the inferred semiring path mismatched `Real.semiring`).
- **Fix:** factor the basis-coercion into an upstream-eligible mirror lemma
  `Submodule.exists_linearIndependent_fin_of_finrank_eq` (existence form, over an
  abstract field, no concrete carrier). Its opaque proof keeps `ScrewSpace` from
  unfolding at the use site — the consumer `obtain`s `⟨c, hc, hmem⟩` and only the
  lemma's *statement* is elaborated.
- **General lesson:** when a `Basis`/`map'`/`Module.Free` step times out at `whnf`
  on a heavy `abbrev` carrier (exterior power, `Module.Dual` of one), state the
  linear-algebra fact over an abstract field as a mirror lemma and apply it — the
  proof's `whnf` cost is paid once, opaquely, not re-paid at every use site.
- **Status:** resolved — mirror lemma landed (see Mirrored).

### [resolved] `complementIso_toDual_eq_zero_of_wedgeProd_eq_zero (by omega) _ _ h` whnf-times-out unifying the `_ _` against `h` — supply `X`/`B` explicitly
- **Where it bit:** the panel-meet `n'`-summand kill inside
  `complementIso_smul_eq_extensor_join` (`Molecular/Meet.lean`, Phase 22f N3b capstone).
- **Friction:** applying the dictionary half with both extensor arguments as `_` and the
  `wedgeProd`-vanishing `h` as the trailing positional arg made elaboration whnf-time-out (200k)
  trying to unify the two `⟨extensor …, …⟩ : ⋀²ℝ⁴` placeholders against `h`'s type.
- **Fix:** pass `(k := 2) (j := 2) (by omega)` and **both** `⟨extensor …, _⟩` arguments explicitly;
  then `h` checks against a fully-known goal with no inference.
- **General lesson:** same heavy-carrier family as TACTICS-QUIRKS § 38 (exterior-power/`Module.Dual`
  whnf blowup), but the remedy is lighter than § 38's extract-a-helper: a heavy carrier punishes
  left-to-right unification of underscored *lemma-application* args, so just name them — no abstract
  restatement needed when the timeout is at the *call site's* unification, not an in-place unfold.
- **Recurred (Phase 22g):** the same call-site timeout, but the offending implicit was a *subtype
  index* `q : {q // q.1 < q.2}` feeding a heavy `omitTwoExtensor (ne_of_lt q.2)` conclusion in
  `exists_hduality_witness_of_panel_incidence` (`Molecular/RigidityMatrix.lean`). Remedy: `fin_cases q`
  then pass `q` as an explicit subtype literal (`⟨(0,1), by decide⟩`) per branch — `q := _` timed out.
- **Recurred (Phase 22k):** a `panelRow ends ↑j ∈ F.rigidityRows` goal where `↑j` is a *coerced
  subtype index* `j : ↥s` — `show … ∈ rigidityRows` / `panelRow_mem_rigidityRows (i := ↑j)` both
  whnf-time-out (the §38 membership-witness variant). Remedy: `rcases x i with ⟨⟨e',t₁,t₂⟩,hj⟩`
  (destructure the index to expose `e'`), `subst (e' = eₐ)`, then `panelRow_mem_rigidityRows_of_link
  ends hva hlink_a t₁ t₂` — the *of_link* form takes `ends e = (u,w)` + the link explicitly, so the
  match is syntactic. Landed in `exists_independent_pinned_two_edge_span_full` (`Pinning.lean`, L8c-1).
- **Status:** resolved — explicit args in the landed proof.
- **Mirror file:** `Mathlib/LinearAlgebra/Dimension/Constructions.lean`.

### [resolved] Iterating cyclic `+1` around `Fin m`: `(j : Fin m)` ascription / `NatCast` / `Fin.induction` all fail; use `Fin.ofNat`-based ℕ-induction
- **Where it bit:** `isTrivialMotion_of_isInfinitesimalMotion_cycle` in
  `Molecular/AlgebraicInduction/` (Phase 21 `m`-body cycle): turning the
  consecutive equality `S i = S (i+1)` (cyclic `Fin m` `+1`) into `S i = S 0`.
- **Friction:** `(j : Fin m)` for `j : ℕ` parses as a type ascription, not a
  coercion (*"Type mismatch j has type ℕ"*); `(↑j : Fin m)` / `Nat.cast` then trip
  *"failed to synthesize NatCast (Fin m)"* (the instance wants the literal `n+1`
  shape, not `Fin m` under `[NeZero m]`); `Fin.induction` uses the non-wrapping
  `Fin.succ`, not cyclic `+1`.
- **Fix:** induct over `Fin.ofNat m j` on `ℕ` (`Fin.ofNat_zero` base,
  `Fin.ofNat_val_eq_self` to return to `i`), with the one-line successor fact
  `Fin.ofNat m p + 1 = Fin.ofNat m (p+1)` by `Fin.ext` + `simp [Fin.add_def,
  Nat.add_mod]`. No `Graph`-walk primitive needed — `Fin m` *is* the cycle.
- **General lesson:** lifted to TACTICS-GOLF § 12.
- **Status:** resolved — landed inline; `Fin.ofNat m p + 1 = …` is a one-liner, no
  separate mirror warranted.

### [resolved] A hypothesis stated on `(ofNormals GH ends q₀).toBodyHinge` passes directly to a brick wanting `(ofNormals G ends q₀).toBodyHinge.withGraph GH` — defeq, no `rw` bridge
- **Where it bit:** `hasFullRankRealization_of_splice_ofNormals` in
  `Molecular/AlgebraicInduction/` (Phase 22 N5 decomposition). The leg-native
  splice variant takes `hblock : (ofNormals GH ends q₀).toBodyHinge.IsInf…RigidOn …`
  and feeds the parent splice brick, which wants
  `((ofNormals G ends q₀).toBodyHinge.withGraph GH).IsInf…RigidOn …`.
- **Friction:** `rw [toBodyHinge_withGraph, ofNormals_withGraph] at hblock ⊢` failed
  ("Did not find … pattern") — `withGraph`/`ofNormals`/`toBodyHinge` are all `rfl`-
  transparent structure projections, so the two forms are *defeq* and the `rw`
  matcher has no syntactic occurrence to rewrite.
- **Fix:** drop the `rw` bridge and pass `hblock`/`hcontract` directly as the brick's
  arguments; application-mode unifies up to defeq. (`ofNormals_withGraph` is still a
  useful named `rfl` lemma for prose/`simp`, but the proof doesn't need it.)
- **Status:** resolved (no lift — recurrence of the "`rw` is syntactic, `exact`/
  application is up-to-defeq" rule already in TACTICS-QUIRKS § 25, and a sibling of
  the `map_eq_zero_iff` entry below. Lifted: TACTICS-QUIRKS § 25).

### [resolved] `LinearEquiv.map_eq_zero_iff` via `rw` fails on a defeq-wrapped codomain (`ScrewSpace k` = `⋀^(k+2−2)`); apply `map_ne_zero_iff … .injective` as a term
- **Where it bit:** `panelSupportExtensor_ne_zero_iff` in
  `Molecular/AlgebraicInduction/` (Phase 21 panel leaf): showing
  `complementIso (j:=2) (normalsJoin n₁ n₂) ≠ 0 ↔ …`, where the result is typed
  `ScrewSpace k` (a `def`-abbrev for `⋀^(k+2−2) (Fin (k+2) → ℝ)`).
- **Friction:** `rw [LinearEquiv.map_eq_zero_iff]` and `rw [map_eq_zero_iff _
  (complementIso _).injective]` both failed with "Did not find an occurrence of the
  pattern `?e ?x = 0`" — the displayed `(complementIso ⋯) (normalsJoin …)` elaborated
  through the `ScrewSpace k`-vs-`⋀^(k+2−2)` defeq, so the `rw` HO-pattern matcher
  couldn't unify.
- **Fix:** apply the lemma as a *term*, not via `rw`: after `rw […, ← normalsJoin_ne_zero_iff]`,
  close with `exact map_ne_zero_iff _ (complementIso (by omega : 2 ≤ k + 2)).injective`.
  Term-mode `exact` unifies up to defeq where `rw` pattern-matching does not.
- **Status:** resolved (no lift — recurrence of the general "`rw` is syntactic, `exact`
  is up-to-defeq" rule already in TACTICS-QUIRKS § 25; this is the `map_eq_zero_iff`
  instance. Lifted: TACTICS-QUIRKS § 25).

### [resolved] `wedgeProd` of two `ιMulti_family` basis vectors → single `extensor`: `change` to surface the `extensor ∘ ofFinEmbEquiv.symm` form before `join_extensor`
- **Where it bit:** `coe_wedgeProd_ιMulti_family` in `Molecular/Meet.lean` (Phase 21a
  ingredient (c)), bridging the graded wedge pairing on standard basis vectors to the
  Phase-17 single-extensor API for the disjointness ⇒ vanishing argument.
- **Friction:** `coe_wedgeProd` rewrites `↑(wedgeProd …)` to `↑A ∨ₑ ↑B`, but the
  factors are `↑(ιMulti_family ℝ j b S)`, which is *defeq* to
  `extensor (b ∘ ofFinEmbEquiv.symm S)` (both unfold to `ExteriorAlgebra.ιMulti ℝ j
  (b ∘ σ)`) yet not syntactically — so `join_extensor` (stated on `extensor a ∨ₑ
  extensor b`) does not fire by `rw` alone.
- **Fix:** a one-line `change (extensor (b ∘ σ_S)) ∨ₑ (extensor (b ∘ σ_T)) = _`
  surfaces the `extensor`-form, after which `rw [join_extensor]` closes it.
- **Status:** resolved (no lift — the `ιMulti_family ↦ extensor ∘ ofFinEmbEquiv.symm`
  defeq is project-local; `coe_wedgeProd_ιMulti_family` is itself the fused bridge so
  the `change` happens once).

### [resolved] A grade-2 `extensor ![a, v]` packaged as `LinearMap.mulLeft ℝ (ι a) ∘ ι`: unfold `ιMulti ℝ 2 ![a,v] = ι a * ι v` by `simp [List.ofFn_succ]`
- **Where it bit:** `wedgeFixedLeft` / `coe_wedgeFixedLeft` in `Molecular/Meet.lean`
  (Phase 22f N3b-2b-α building block, the wedge-with-a-fixed-vector map `v ↦ a ∧ v`).
- **Friction:** to package `v ↦ extensor ![a, v]` as a `→ₗ`, the cleanest carrier is
  `(LinearMap.mulLeft ℝ (ι a)).comp (ι)` (codRestricted to `⋀²`), which needs
  `extensor ![a, v] = ι a * ι v`. `extensor_apply` + `ExteriorAlgebra.ιMulti_apply`
  reduces the LHS to `(List.ofFn fun i ↦ ι (![a,v] i)).prod`, but `List.ofFn` over
  `Fin 2` doesn't compute by `rfl`.
- **Fix:** one `simp [List.ofFn_succ]` (single lemma, found first try) unfolds the
  2-element `List.ofFn` product to `ι a * (ι v * 1) = ι a * ι v`. Below the one-bridge
  threshold; same `ιMulti ↦ ι-product` family as the `coe_wedgeProd_ιMulti_family` entry
  above.
- **Status:** resolved (no lift — `simp [List.ofFn_succ]` is the standard `ιMulti`
  small-arity unfold; `coe_wedgeFixedLeft` is the fused `@[simp]` bridge so it happens once).

### [resolved] `rw [if_pos rfl]` fails on a `(fun i ↦ if i = j then …) j` goal — `simp only [↓reduceIte]`
- **Where it bit:** `Graph.exists_packing_move_of_not_inc` in `Molecular/Induction/`
  (the forest-packing rebalancing move; the re-chosen packing `fun i => if i = j then
  insert x (Fs j) else Fs i \ {x}` evaluated at `j` in the recipient-forest subgoals).
- **Friction:** after `refine ⟨fun i => …, …⟩` + `subst`, the goal still showed the
  un-beta-reduced `(fun i ↦ if i = j then …) j`; `rw [if_pos rfl]` failed ("Did not find an
  occurrence of the pattern" — no `ite` at the surface). `simp only [if_pos rfl]` reduced it
  but flagged `if_pos` as an unused simp arg (`linter.unusedSimpArgs`).
- **Proposed fix:** `simp only [↓reduceIte]` (the simproc beta-reduces and reduces `if (j = j)`
  in one step); use the simproc name, not the `if_pos` lemma.
- **Status:** resolved. **Lifted to:** TACTICS-QUIRKS § 28.

### [resolved] `[matroid]` The vendored `apnelson1/Matroid` package already supplies a full multigraph `Graph.degree` + handshake API — do not roll your own
- **Where it bit:** `Graph.exists_degree_le_two` in `Molecular/Induction/` (Phase 20
  KT 4.6, F″ core). The Phase-20 hand-off note asserted "the project has no `Graph α β`
  degree function" and scoped F″ as building one (degree, the `∑ deg = 2|E|` handshake,
  pigeonhole) from scratch. A first draft did exactly that (`endpointMult`/`degree`/
  `sum_endpointMult_eq_two`/handshake) — then the build reported `Graph.degree` *already
  declared*, resolving to a vendored definition `G.degree v = (G.eDegree v).toNat`.
- **Resolution:** `.lake/packages/Matroid/Matroid/Graph/Degree/Basic.lean` carries the entire
  development: `incFun` (the `α →₀ ℕ` endpoint-multiplicity finsupp, loops count 2),
  `eDegree`/`degree`, `sum_incFun_eq_two`, and the handshake `handshake_eDegree`,
  `handshake_degree_subtype` (`∑ᶠ v ∈ V(G), G.degree v = 2 * E(G).ncard`, needs `[G.Finite]`),
  `handshake_degree_finset`, `handshake`. It is transitively imported via the `cycleMatroid`
  chain, so it is usable in `Induction/` with **zero** new imports. `[G.Finite]` is
  discharged under the project's `[Finite α] [Finite β]` by
  `{ edgeSet_finite := Set.toFinite _, vertexSet_finite := Set.toFinite _ }` (anonymous
  constructor `⟨⟨_⟩, _⟩` mis-elaborates — use named fields).
- **General lesson:** **`grep .lake/packages/Matroid` for any `Graph α β` graph-theory notion
  before building it** — the vendored package is a large, actively-developed graph library
  (degree, connectivity, matching, walks/trails), not just the matroid-union subsystem that
  was originally ported. A stale "the project has no X" hand-off note is not evidence X is
  absent from the dependency closure.
- **Status:** resolved (reused the vendored API; F″ core landed as the pigeonhole on top).

### [resolved] `[matroid]` Fundamental-circuit-swap idioms: finite-min over bases, "indep of full rank ⟹ base", and the `X∩ẽ≠∅` base-meets-fiber move
- **Where it bit:** `Graph.no_rigid_edge_count` in `Molecular/Induction/` (Phase 20
  KT 4.5(i), F′ swap core). KT's proof argues "`X∩ẽ=∅` ⟹ `D` spanning trees avoid `ẽ`,
  contra minimality" (forest language); the prior session read this as a real blocker.
- **Friction / resolution:** three reusable moves, all standard once stated cleanly:
  1. **Min over bases:** `Set.exists_min_image {B | M.IsBase B} (fun B ↦ (ẽ ∩ B).ncard)`;
     finiteness of `{B | IsBase B}` via `(Set.toFinite M.E).finite_subsets` + `subset_ground`,
     nonemptiness via `M.exists_isBase`.
  2. **Indep of full rank ⟹ base:** the manual route is `exists_isBase_superset` to a base
     `B'`, then `Set.eq_of_subset_of_ncard_le` with `|I| = |B*| = |B'|` (all bases share
     cardinality, `IsBase.ncard_eq_ncard_of_isBase`) forces `I = B'`. **When the rank count is
     in hand, prefer the dedicated `Indep.isBase_of_ncard hI (h : M.rank ≤ I.ncard)`** (one
     line; Phase-22d `splitOff_exists_base_inter_fiber_lt`). It needs `[M.RankFinite]`, which on
     a finite ground type is `haveI : M.RankFinite := Matroid.rankFinite_of_finite (M := …)`
     (pass `M` explicitly; `matroidMG`'s `[DecidableEq β]` must be on the *statement*, not just
     `classical`). Trap: `Matroid.finite_of_finite` gives `M.Finite` (a weaker instance), not
     `RankFinite`; the compiler accepts both without complaint, but only `rankFinite_of_finite`
     discharges `[RankFinite M]` (Phase-22i, `splitOff_isMinimalKDof_of_pos`, 3 occurrences).
  3. **`X∩ẽ≠∅` is base-meets-fiber, not forest:** if `X∩ẽ=∅`, `X−ej` is independent of full
     size (tight on `V(X)=V`) ⟹ a base avoiding `ẽ`, contradicting `IsMinimalKDof`'s clause
     (`hG.2`). No `rank M↾(E∖ẽ)` detour.
- **General lesson:** "KT argues by forests" does not mean the Lean must — when the consumed
  fact is a base/fiber statement, route directly through the minimality clause. The base
  exchange itself is `IsBase.exchange_isBase_of_indep` + `Indep.mem_fundCircuit_iff`
  (`ej ∈ fundCircuit f B ↔ Indep(insert f B ∖ {ej})`). These three carry the remaining
  circuit-swap commits (G/H) too.
- **Status:** resolved.

### [resolved] `[matroid]` Transporting circuits between `M(G̃)` and `M(H̃)` for `H ≤ G`; and a rank count that bypasses KT 4.8(i)'s iterated swap
- **Where it bit:** `Graph.circuit_splitOff_meets_fiber` + `Graph.splitOff_isMinimalKDof` in
  `Molecular/Induction/` (Phase 20, KT 4.8(i) splitting-off minimality transport).
- **Friction / resolution — circuit transport:** to move a circuit between `M(G̃)` and `M(H̃)`
  for a graph-level `H ≤ G`, compose mathlib `Matroid.restrict_isCircuit_iff`
  (`(M ↾ R).IsCircuit C ↔ M.IsCircuit C ∧ C ⊆ R`) with the project's
  `matroidMG_restrict_mulTilde` (`M(G̃) ↾ E(H̃) = M(H̃)`). `restrict_isCircuit_iff`'s ground
  side-goal `R ⊆ M.E` is `(edgeMultiply_mono h _).edgeSet_mono`. Same composition for `Indep`
  (`Matroid.restrict_indep_iff`) and for "whole ground independent ⟹ base"
  (`Matroid.ground_indep_iff_isBase`, after `rw [matroidMG, restrict_ground_eq]` to expose the
  ground as `E(H̃)`). KT's (4.10) "every circuit of `M(G̃_v^{ab})` meets `ã̃b`" is most cleanly
  stated/used as "`E(G̃_v)` is independent (circuit-free) in `M(G̃_v^{ab})`" via
  `Matroid.indep_iff_forall_subset_not_isCircuit'`.
- **General lesson — bypass the iterated swap with a rank count.** KT 4.8(i) proves minimality
  by an iterated fundamental-circuit swap (relocate each `ã̃b` copy onto an `ẽ` copy, induction
  on `|B₁ ∩ ã̃b|`). The whole induction is unnecessary: once `E(G̃_v)` is a *base* of `M(G̃_v)`
  (from (4.10)) and `def(G̃_v) > 0` (KT 4.7), any base `B'` of `M(G̃_v^{ab})` avoiding a fiber
  `ẽ` splits as `(B'∩ã̃b) ⊔ (B'∩E(G̃_v))` with `|B'∩ã̃b| ≤ D−1` and `|B'∩E(G̃_v)| ≤ |E(G̃_v)|−(D−1)`
  (when `e≠e₀`) or `B' ⊆ E(G̃_v)` (when `e=e₀`), so `|B'| ≤ |E(G̃_v)|`; through
  `isBase_ncard_add_deficiency_eq` on the two bases this forces `def(G̃_v) ≤ 0` — contradiction.
  Pattern: *an iterated basis-exchange whose only purpose is to relocate redundancy onto a fixed
  set is often replaceable by a single cardinality split across that set's complement.*
- **Status:** resolved.

### [resolved] `[matroid]` Extending a cycle-matroid-independent set by a *pendant* edge: the `Isolated`/bridge idiom
- **Where it bit:** `Graph.acyclicSet_insert_vfiber_of_not_inc` in `Molecular/Induction/`
  (Phase 20, KT 4.1 balanced-packing redistribution kernel).
- **Friction / resolution:** to show `cycleMatroid.Indep (insert x F)` for a forest `F` whose
  edges avoid a vertex `v` and a non-loop `v`-fiber `x : v—w` (`w ≠ v`), the clean route is
  entirely vendored `apnelson1/Matroid` graph API: `Graph.cycleMatroid_indep`
  (`Indep = IsAcyclicSet`) → `Graph.isAcyclicSet_iff` (`= F ⊆ E ∧ (G ↾ F).IsForest`) →
  `Graph.IsForest.of_deleteEdges_singleton (he : bridge x) (hG : (R ＼ {x}).IsForest)`. The
  deleted-graph forest goal closes by `IsForest.anti` after `Graph.restrict_deleteEdges`
  (`(G ↾ F₁) ＼ F₂ = G ↾ (F₁ \ F₂)`) + `Graph.restrict_le_restrict` (needs
  `E ∩ F₁ ⊆ E ∩ F₂`). The bridge closes by `IsLink.isBridge_iff_not_connBetween` then
  `Isolated.connBetween_iff_eq` — the latter is the key lever: a vertex incident to *no* edge
  of the deleted graph is `Graph.Isolated`, so any `ConnBetween v w` forces `v = w`.
- **General lesson:** *for "adding a degree-≤-1 edge keeps a graph acyclic", don't reason
  about cyclic walks directly — go through `Isolated` (the endpoint has no other edge) +
  `Isolated.connBetween_iff_eq` to get a bridge, then `IsForest.of_deleteEdges_singleton`.*
  Gotcha: `Graph.restrict_isLink`/`restrict_inc` put the **set-membership conjunct first**
  (`e ∈ F ∧ G.IsLink e x y`), not the link first.
- **Status:** resolved.

### [resolved] `[matroid]` Transporting acyclicity *down* a subgraph (`IsAcyclicSet.anti_inter`) always intersects with `E(G)` — clean up with `Set.inter_eq_self_of_subset_right`
- **Where it bit:** `Graph.isAcyclicSet_splitOff_of_diff_fiberAtVertex` in `Molecular/Induction/`
  (Phase 20, `lem:forest-surgery-split` reroute wiring step 1 — the `v`-free part of a `G̃`-forest
  transports into `G̃ᵥᵃᵇ`).
- **Friction / resolution:** the vendored `Graph.IsAcyclicSet.anti_inter (hGH : G ≤ H)
  (hF : H.IsAcyclicSet F) : G.IsAcyclicSet (E(G) ∩ F)` is the only "transport acyclicity down a
  subgraph" lemma, and it **always** intersects the set with the smaller graph's edge set. When
  the set already lives in `E(G)` (here `F ∖ fiberAtVertex v ⊆ E((G_v)̃)`, proved separately), the
  produced `E(G) ∩ F` is `F`, but not syntactically — close the gap with
  `rwa [Set.inter_eq_self_of_subset_right hsub] at this`.
- **General lesson:** *`IsAcyclicSet.anti_inter` is the down-a-subgraph transport, but its
  conclusion is `E(G) ∩ F`, not `F`; pair it with `Set.inter_eq_self_of_subset_right` (+ a
  ground-membership `have`). The `up`-a-subgraph direction `IsAcyclicSet.mono` carries no such
  intersection.*
- **Status:** resolved.

### [resolved] `[matroid]` Building a small explicit cyclic walk (`IsCyclicWalk`) needs the full structure tower + a hoisted `IsWalk` `have`
- **Where it bit:** `Graph.isCycleSet_pair_edgeFiber_splitOff` in `Molecular/Induction/`
  (Phase 20 `lem:forest-surgery-split` reroute-count substrate). To exhibit `{p, q}` as a
  cycle of `G̃ᵥᵃᵇ` I constructed the explicit length-2 walk `cons a p (cons b q (nil a))` and
  had to discharge `IsCyclicWalk` directly.
- **Friction:** (1) `IsCyclicWalk` extends `IsTour` extends `IsTrail` extends `IsWalk`, so the
  anonymous constructor is the 4-deep nest `⟨⟨⟨hwalk, edge_nodup⟩, nonempty, isClosed⟩, nodup⟩`
  — easy to mis-count fields (initial `⟨⟨⟨?_,?_,?_⟩,?_⟩,?_⟩` gave "Constructor IsTour.mk has 3
  explicit fields, but only 2 provided"). (2) The `IsWalk` proof must be hoisted into a separate
  `have hwalk`; inlining it as `⟨…, hlinkq.symm.walk_isWalk⟩` type-mismatches because the
  innermost tail is `IsWalk (nil a)`, **not** `q`'s link-walk — close it with `nil_isWalk_iff`
  + `hlinkp.left_mem` (membership of the endpoint). (3) `cons_isWalk_iff` / `nil_isWalk_iff` are
  `Graph.`-namespaced, not `WList.` (first guess `WList.cons_isWalk_iff` was "unknown constant").
- **Fix / general lesson:** for a hand-built short cyclic walk, hoist the `IsWalk` to its own
  `have` (peel with `cons_isWalk_iff` ×k + `nil_isWalk_iff`), then `refine` the `IsCyclicWalk`
  tower as `⟨⟨⟨hwalk, ?_⟩, by simp, ?_⟩, ?_⟩` and close `edge_nodup` / `isClosed` / `nodup` by
  `simp` (feed the edge-distinctness `p ≠ q` and the vertex-distinctness `a ≠ b`). The edge-set
  equation `E(C) = {p, q}` is plain `simp`. Project-internal (about our `splitOff`/`mulTilde`),
  so it lives in `Induction/`; no upstream mirror.
- **Status:** resolved.

### [resolved] `[matroid]` Cycle-lift by edge-substitution (rotate-to-first + cons-substitute + tour-contains-cycle): four naming/`def`-unfold traps
- **Where it bit:** `Graph.isAcyclicSet_splitOff_reroute` in `Molecular/Induction/`
  (Phase 20 `lem:forest-surgery-split` reroute wiring step 2, the `dᶠ(v)=2` cycle-lift crux).
  To show the rerouted forest `(F ∖ {pa,pb}) ∪ {r}` stays acyclic, a hypothetical `G̃ᵥᵃᵇ`-cycle
  `C` through the short-circuit copy `r` is lifted to a closed `G̃`-trail by substituting the
  fresh edge `r` (joining `a,b`) with the `v`-traversing 2-path `a—pa—v—pb—b`, then a contained
  cycle is extracted.
- **Friction (the idiom + four traps):** the idiom is `WList.exists_rotate_firstEdge_eq` (rotate
  `C` so `r` is the first edge) → `nonempty_iff_exists_cons` destructure into `cons x r w'` →
  splice `r` out and `cons a pa (cons v pb w')` in → `IsTour` (closed trail) → `IsTour.exists_isCyclicWalk`
  (a tour contains a cycle as an `IsSublist`). Traps: (1) the walk-down-a-subgraph lemma is
  `Graph.isWalk_deleteEdges_iff` (vendored, `Graph.`-namespaced), **not** `WList.deleteEdges_isWalk_iff`
  (unknown constant). (2) the sublist edge-containment is `WList.IsSublist.edge_subset` (`E(w₁) ⊆ E(w₂)`),
  **not** `…edgeSet_subset`. (3) `WList.IsClosed` is a bare `def` (`first = last`); `simp` "made no
  progress" — peel with `WList.cons_isClosed_iff` (`(cons x e w).IsClosed ↔ x = w.last`) + `last_cons`,
  then close by `hx ▸ hclosed`. (4) membership `p ∈ (cons x e w').edgeSet` from `p ∈ w'.edge` needs
  `WList.cons_edgeSet` (`= insert e E(w)`) + `Set.mem_insert_of_mem` + `WList.mem_edgeSet_iff`, **not**
  `cons_edge` (that's the `.edge` *list*, and the goal is the `edgeSet`).
- **Fix / general lesson:** for an edge-substitution cycle-lift, hoist the substituted walk's
  endpoint orientation (`hwb : w'.first = b`) and rewrite the inner `cons_isWalk_iff` link with it
  (`hwb ▸ hpb`, no `.symm` — the `▸` already lands the direction). `IsTour`'s anonymous constructor
  is `⟨⟨isWalk, edge_nodup⟩, nonempty, isClosed⟩`; the `edge_nodup` for the spliced trail comes from
  `cons_edge`/`nodup_cons` on the original cyclic walk's `edge_nodup` plus the new edges' absence from
  `w'.edge`. Project-internal (about our `splitOff`/`mulTilde`), lives in `Induction/`; no upstream
  mirror. **Lifted to:** TACTICS-QUIRKS § 29.
- **Status:** resolved.

### [resolved] `[matroid]` Reverse cycle-lift swap (KT 4.2): the `concat`/`dropLast`/`reverse` mirror of the forward `cons`-substitution
- **Where it bit:** `Graph.isAcyclicSet_mulTilde_of_splitOff_reroute` in `Molecular/Induction/`
  (Phase 22i L1g, the reverse of `isAcyclicSet_splitOff_reroute`). A `G̃`-cycle `C` in
  `(F'∖{r}) ∪ {pa, pb}` is lifted to a `G̃ᵥᵃᵇ`-cycle inside `F'` by substituting the
  `v`-traversing 2-path `a—pa—v—pb—b` *back* by the single short-circuit edge `r`. Mirrors the
  forward §29 idiom but in the opposite direction, so the substituted edges land at the walk's
  *end* rather than its *front*.
- **Friction (additions over the forward §29 idiom):** (1) the second `v`-edge `pb` is located as
  the **last edge** of the sub-walk via `wab.Nonempty.lastEdge` + `Nonempty.concat_dropLast`
  (`wab.dropLast.concat hw.lastEdge wab.last = wab`) + `concat_isWalk_iff` (`Graph.`-namespaced;
  gives `IsLink (lastEdge) w₂.last v`), not `cons_isWalk_iff` on the front. (2) The two endpoint
  orientations (`pa` joins `v,a` either way around) are unified by reorienting the sub-walk with
  `WList.reverse` (`reverse_first`/`reverse_last`/`reverse_edgeSet`/`reverse_edge` +
  `List.nodup_reverse`), packing `K.IsWalk wab ∧ first ∧ last ∧ edgeSet ∧ Nodup ∧ pa∉edge` into one
  `obtain` so the downstream argument is orientation-free. (3) `wab.edge = w₂.edge ++ [qpb]` (via
  `concat_edge`), so `qpb ∉ w₂.edge` / `w₂.edge.Nodup` come from `List.nodup_append` — whose third
  component is `∀ a ∈ l₁, ∀ b ∈ l₂, a ≠ b` (apply at `qpb`/`List.mem_singleton.mpr rfl`), **not**
  `List.Disjoint`. (4) the "uses exactly one `v`-edge" case is ruled out by the *same* reverse swap
  run from `pb` (its forced other-end edge is `pa`, contradicting `pa ∉ C`); no cycle-degree lemma
  needed. (5) `mulTilde n = edgeMultiply (bodyHingeMult n)` (not `edgeMultiply n`) — feed
  `edgeMultiply_mono h _` with `_` for the multiplicity, and `hK ▸` to defeat the `set K` alias
  blocking the `≤`.
- **Fix / general lesson:** for a reverse edge-substitution cycle-lift, locate the trailing special
  edge as `lastEdge` and decompose with `concat_dropLast`; unify endpoint orientations with one
  `reverse`-or-not `obtain` rather than duplicating the substitution per case. Project-internal
  (about our `splitOff`/`mulTilde`), lives in `Induction/`; no upstream mirror. **See:**
  TACTICS-QUIRKS § 29 (the forward idiom).
- **Status:** resolved.

### [resolved] `[matroid]` no mathlib "base of `M ／ C` lifts to base of `M` via a basis of `C`" — route through `IsBasis'.contract_eq_contract_delete` + loops
- **Where it bit:** `Matroid.IsBase.union_isBasis_of_contract` in
  `Molecular/Induction/` (Phase 20 `lem:contract-minimality-transport`). mathlib
  has `Indep.contract_isBase_iff` (`(M／I).IsBase B ↔ M.IsBase (B∪I) ∧ Disjoint B I`)
  only for **independent** contracted `I`; for a general `C` there is no
  `(M／C).IsBase B' → M.IsBasis' J C → M.IsBase (B'∪J)`. Build it: pick `J` a basis of
  `C` (`exists_isBasis'`), rewrite `M ／ C = M ／ J ＼ (C\J)`
  (`IsBasis'.contract_eq_contract_delete`) + `delete_isBase_iff`; the deleted `C\J` is
  loops of `M ／ J` (`contract_loops_eq` gives `loops = M.closure J \ J ⊇ C\J` since
  `C ⊆ closure J`), so `ground \ (C\J)` is spanning (`closure_diff_loops_eq` +
  `closure_ground`) and `B'` is a base of `M ／ J` (`IsBasis.isBase_of_spanning`); then
  `Indep.contract_isBase_iff` finishes.
- **Fix / general lesson:** `IsBasis'` does **not** give `C ⊆ M.E` (it intersects
  ground internally), so the loops-containment must intersect with ground: prove
  `C ∩ M.E ⊆ M.closure J` (via `IsBasis'.closure_eq_closure` + `subset_closure_of_subset'`
  on `C ∩ M.E`), not `C ⊆ M.closure J`. General: when lifting a contraction base, reduce
  to contracting an *independent* basis of the contracted set and discharge the leftover
  via the loops/spanning route; and remember `IsBasis'` carries no ground containment for
  its `X`.

### [resolved] `[matroid]` contraction rank arithmetic already lives in vendored `Matroid.Minor.Rank`; the `cast_int` form's RHS is ℤ-subtraction, annotate as such
- **Where it bit:** `Matroid.rank_contract_add_rank_restrict` in
  `Molecular/Induction/` (Phase 20 `lem:contraction-minimality` contraction
  arithmetic). The standard matroid identity `r(M/C) = r(M) − r_M(C)` is **not**
  in mathlib's `Matroid` minor files, but the vendored `apnelson1/Matroid`
  package's `Matroid/Minor/Rank.lean` already carries it: `contract_rk_add_eq`
  (`(M／C).rk X + M.rk C = M.rk (X∪C)`) and the `@[simp]`
  `contract_rank_cast_int_eq` (`((M／C).rank : ℤ) = M.rank − M.rk C`). No need to
  re-derive via the `eRelRk_add_eRk_eq` chain rule — search the vendored
  `Minor/Rank.lean` first. Also `restrict_rk_eq M subset_rfl` gives
  `(M↾C).rank = M.rk C` (via `(M↾C).E = C`).
- **Fix / general lesson:** `contract_rank_cast_int_eq`'s RHS is `↑M.rank − ↑(M.rk C)`
  (ℤ-`Sub`), **not** `↑(M.rank − M.rk C)` (cast of ℕ-truncated-sub) — annotating the
  `have` as the latter is a type mismatch. Write the `have` type with explicit ℤ
  casts on each atom (`(M.rank : ℤ) − (M.rk C : ℤ)`) and close the ℕ goal with
  `omega` (it bridges the ℕ `restrict` fact and the ℤ `contract` fact). General:
  for the vendored package's `*_cast_int_eq` rank lemmas, the int form uses honest
  ℤ-subtraction; keep atoms ℤ-cast and let `omega` reconcile.

### [resolved] `[matroid]` Union↔contraction equality: prove via the *count condition* `Union_pow_indep_iff_count`, not via the per-factor `union_indep_iff` matching re-decomposition
- **Where it bit:** `Matroid.Union_pow_contract_eq_contract_of_rk_saturated` in
  `Molecular/Induction/` (Phase 22 N4c crux): show `Union (fun _ : Fin k ↦ M ／ C)`
  and `Union (fun _ : Fin k ↦ M) ／ C` agree on independent sets when `C` *saturates*
  the union rank (`N.rk C = k·M.rk C`). The intuitive route — decompose via
  `union_indep_iff` and re-distribute the per-factor `C`-bases `Jᵢ` — has a genuine
  obstruction in the reverse direction: an arbitrary `union_indep_iff` decomposition
  `Ks` of `I ∪ J` is *not* factor-aligned with the `Jᵢ`, and naive realignments
  (`Ksᵢ \ C`, `Ksᵢ ∩ I`, swapping `Ksᵢ ∩ C` for `Jᵢ`) all fail — `M.Indep (Ksᵢ)` does
  **not** give `(M ／ C).Indep (Ksᵢ \ C)` (an element of `Ksᵢ \ C` can be a loop of
  `M ／ C`). Aligning the matching is real matroid-union augmentation work, buried in the
  package's `AdjIndep.augment` `Finset` layer, not exposed for `Set`-side unions.
- **Fix / general lesson:** the vendored `Union_pow_indep_iff_count`
  (`N.Indep E' ↔ ∀ Y ⊆ E', |Y| ≤ k·M.rk Y`) reduces *both* matroids to **rank-count
  conditions**, making the equivalence a symmetric `rk_submod` + `rk_mono` +
  `contract_rk_cast_int_eq` arithmetic over ℤ (the `k·` is a common factor; multiply the
  submodular inequality by `(k : ℤ) ≥ 0` and finish with `nlinarith`). The
  contracted-side `(N ／ C).Indep I ⟺ N.Indep (I ∪ J)` comes from `IsBasis'.contract_indep_iff`
  for an `N`-basis `J` of `C`; saturation enters only as `|J| = k·M.rk C`. **General:**
  when proving a union-of-matroids identity that the matching layer would make painful,
  check whether `Union_pow_indep_iff_count` turns it into rank arithmetic first — the
  count form sidesteps the per-factor decomposition entirely. (Kept here with the other
  `[matroid]` idioms rather than lifted: the project's matroid-union lessons all live as
  tagged FRICTION entries, there is no matroid section in `TACTICS-GOLF.md`.)

### [resolved] A choice-of-representative label `if h : s.Nonempty then h.choose else _` trips `rw`-motive when you rewrite the set `s` underneath — factor through the *object* so equality is `congrArg`
- **Where it bit:** `componentLabel` in `Molecular/Deficiency.lean` (Phase 19
  `thm:def-eq-corank` piece 3). The component label of a vertex is a chosen
  vertex of its `walkable`-component; proving it constant on a component means
  showing `ConnBetween x y → label x = label y`, where `ConnBetween` gives
  `walkable x = walkable y`. A direct `componentLabel H x := if h :
  V(H.walkable x).Nonempty then h.choose else x` form forces, after `dif_pos`,
  the goal `hx.choose = hy.choose` with `hx : V(walkable x).Nonempty`; rewriting
  the walkable-set equality there is a *"motive is not type correct"* (`rw`
  wants to rewrite inside the type of the `Exists.choose` proof argument).
- **Fix / general lesson:** factor the choice through a function on the *object*
  whose equality you have — `pickVertex (K : Graph) := if h : V(K).Nonempty then
  h.choose else arbitrary`, `componentLabel H x := pickVertex (H.walkable x)`.
  Then constancy is `congrArg pickVertex (h.walkable_eq_walkable)` — no `dite`,
  no motive. Whenever a `Classical.choice`/`Exists.choose`-based selector must be
  proved constant on a fiber, define it as `select ∘ (canonical object map)` and
  reduce to `congrArg select` on an equality of canonical objects, rather than
  carrying the membership proof into the `dite` and rewriting under it.

### [resolved] `ciSup_le` on `deficiency = ⨆ f : α → α, partitionDef …` needs `rw [deficiency]` + `Nonempty α`
- **Where it bit:** `splitOff_deficiency_le` in `Molecular/Induction/`
  (Phase 20 `lem:splitoff-deficiency`, the deficiency-route `≤` direction).
  Bounding `def(H̃) = ⨆ f', H.partitionDef n f'` by `def(G̃)` per-partition
  wants `ciSup_le`, but two things block it: (i) `deficiency` is a plain
  `noncomputable def`, so the `⨆` is hidden — `rw [deficiency]` first; (ii)
  `ciSup_le` needs `[Nonempty (α → α)]`, which `Pi.instNonempty` derives only
  from `Nonempty α` — *not* automatic. Supply `haveI : Nonempty α := ⟨a⟩`
  from any vertex in hand (here `a := hla.right_mem`-style).
- **General lesson:** the prior deficiency lemmas all bounded *from below*
  via `partitionDef_le_deficiency` (`le_ciSup`, no `Nonempty` need); this is
  the first to bound `deficiency` *from above*, so it is the first to want
  `ciSup_le`. The removal bound (commit D) takes the same shape — open with
  `rw [deficiency]; haveI : Nonempty α := ⟨_⟩; refine ciSup_le fun f' => ?_`.
- **Dual shape (commit C, `splitOff_deficiency_ge`, lower bound on the
  *split-off* deficiency):** to lower-bound `def(H̃)` by `def(G̃) − 1` you
  need a *maximizer* of `def(G̃)`, not `ciSup_le`. Get one with
  `obtain ⟨f, hf⟩ := exists_eq_ciSup_of_finite (f := G.partitionDef n)`
  (`Nonempty α` ⟹ `Nonempty (α → α)`, `Finite α` ⟹ `Finite (α → α)`), then
  `rw [deficiency, ← hf]` to expose `def(G̃) = partitionDef f` and bound the
  *target* `def(H̃)` from below by `H.partitionDef_le_deficiency n f`
  (`le_trans`). The deficiency-as-attained-max idiom recurs in the dof
  bookkeeping; reach for `exists_eq_ciSup_of_finite` whenever a partition
  witness for `def(G̃)` itself is needed.

### [resolved] `mulTilde` edge-set / `IsLink` unfold tower recurred ~30× — extracted two fused `@[simp]` mirrors
- **Where it bit:** across `Molecular/Induction/` + `Molecular/Deficiency.lean`
  (Phase 19/20). Reaching `mulTilde`'s edge-set or incidence content needed the
  three-token tower `rw [mulTilde, edgeMultiply_edgeSet, Set.mem_setOf_eq]`
  (membership) or `rw [mulTilde, edgeMultiply_isLink]` (incidence): `mulTilde`
  is a plain non-`@[expose]` `def` wrapping `edgeMultiply`, so neither `simp`
  nor `rw` reaches through it without naming the def first. The Phase-19-B3
  cleanup confirmed this as a no-op "cross-API defeq-unfold" idiom; by Phase 20
  the chain recurred ~30× (18 edgeSet + 14 isLink sites), well past the
  mirror-extraction threshold.
- **Resolved by mirroring** (Phase 20-cleanup B3): added
  `Graph.mem_edgeSet_mulTilde` (`p ∈ E(G.mulTilde n) ↔ p.1 ∈ E(G)`) and
  `Graph.mulTilde_isLink` (`(G.mulTilde n).IsLink p x y ↔ G.IsLink p.1 x y`) in
  `Deficiency.lean` next to `def mulTilde`, both `Iff.rfl` and `@[simp]` (the
  tag lets a bare `simp` reach through the `def` wrapper). Every callsite
  collapses to a single `rw`/`simp only`. One subtlety: at three `simp only`
  sites the dropped `Set.mem_setOf_eq` was *also* unfolding a sibling `setOf`
  (a `crossingEdges` membership), so it had to stay — the fused lemma only
  rewrites the `mulTilde` redex, not every `setOf` in the goal.
- **General lesson:** same threshold rule as the `orderEmbOfFin` entry below —
  a `def`-wrapper unfold tower that recurs is a missing fused mirror, not a
  standing idiom; tag the mirror `@[simp]` so the wrapper stops blocking `simp`.

### [resolved] `[matroid]` `apnelson1/Matroid`'s `WIP/{Union,Submodular}.lean` are unbuildable at every ref — Phase 12 matroid-union mirror (L2a + L2b-union + L2b-rado + L2b-partition all ported; **Phase 12 complete**, all `matroid-union.tex` nodes green)
- **Where it bit:** Phase 12 Layer 1. The plan was to vendor the
  matroid-union machinery (`Matroid.Union`, `union_indep_iff'`, Edmonds
  `matroid_partition'` / `matroid_partition_eRk'`, plus its
  `PolymatroidFn` / `ofSubmodular` / `polymatroid_rank_eq` dependency)
  from `apnelson1/Matroid`'s repo-root `WIP/{Union,Submodular}.lean`,
  fixing one renamed import. The Phase-12 prereq audit recorded these
  as "0 sorries, just import."
- **Friction:** the audit was wrong against every pushed revision.
  Verified at our pin `e6852ce` and at the latest upstream `main`
  (`f3f7df3`): (1) `WIP/Submodular.lean` imports
  `Matroid.Constructions.IsCircuitAxioms`, a module that has **never**
  been committed on any branch (`git log --all -- …/IsCircuitAxioms.lean`
  is empty); (2) its `ofSubmodular` is built on `FinsetCircuitMatroid.*`,
  which is **commented out** in `Matroid/Axioms/Circuit.lean` (>1 yr).
  So `Matroid.Union` etc. are live code at no ref. The only branch with
  a live `ofSubmodular` (`galois`, 2024) has **no** union machinery and
  is on Lean `v4.10` (vs our `v4.30`), so unusable as a pin.
- **Resolution (2026-06, user's call): formalize locally** (option b)
  under `CombinatorialRigidity/Matroid/`, *not* wait for upstream.
  Crucially, the WIP files are **0-sorry** — the proofs exist; the
  blocker is purely that they sit on the superseded
  `FinsetCircuitMatroid` constructor. So the work is a **rebase onto the
  live `FiniteCircuitMatroid`** (the constructor `Graph.cycleMatroid`
  already uses), retaining Peter Nelson's authorship — not a
  from-scratch proof. The package's `Matroid.Intersection` is also live
  (0 sorry), giving an alternative union-from-intersection route; the
  choice is made by a Phase-12 Layer-1 spike. Apache-2.0 throughout, so
  no license issue; attribution via per-file headers + blueprint credit
  (see `DESIGN.md` *Local mirror of the matroid-union subsystem*).
- **Status:** **resolved** — Phase 12 complete (all four port layers
  green/0-sorry, every `matroid-union.tex` node green). See
  `notes/Phase12.md` *Prerequisites audit* + *Layer plan*. Filing an
  upstream courtesy issue (offer the rebase back) is an optional
  follow-up, not blocking. The *downstream* consumption boundary
  (Set/Finset + `rk`/`eRk`/`ncard` rank flavor as Phases 13–15 consume
  this layer) is a cross-cutting design concern, captured in `DESIGN.md`
  *Set/Finset and rank-flavor boundary at the matroid layer (Phases
  13–15)* — not duplicated here per this file's scope rule.
- **L2a progress (2026-06):** `Constructions/Submodular.lean` landed
  green, 0 sorry — `Submodular`, `ofSubmodular` (rebased onto
  `FiniteCircuitMatroid` via the Set-lift `∃ C₀, ↑C₀ = C ∧ Minimal P C₀`),
  `circuit_ofSubmodular_iff`, `indep_ofSubmodular_iff`, plus the three
  revived helpers (`setOf_minimal_antichain`,
  `exists_minimal_satisfying_subset`, `intro_elimination_nontrivial`).
  Two porting gotchas, both bounded: (i) the file's minimal import set
  (`Matroid.*` + `Order.Lattice`) does **not** transitively expose
  `linarith` — needed an explicit `import Mathlib.Tactic.Linarith` (the
  WIP got it via heavier imports); (ii) `LinearOrderedAddCommMonoid` was
  refactored out of this mathlib, so `Submodular`'s bound decomposes to
  `[AddCommMonoid β] [LinearOrder β]` — and the `unusedArguments` linter
  then forces dropping the order-compat `IsOrderedAddMonoid β` (the
  predicate statement uses only `+` and `≤`).
- **L2a polymatroid (2026-06):** `PolymatroidFn` (as a `Prop` structure,
  matching the `[AddCommMonoid β] [LinearOrder β]` split above instead of
  the WIP's `LinearOrderedAddCommMonoid`), `ofPolymatroidFn`, and
  `indep_ofPolymatroidFn_iff` + `ofPolymatroidFn_nonempty_indep_le` landed
  green, 0 sorry. One gotcha: the WIP's `@[simps!]` on `ofPolymatroidFn`
  generates a `..._Indep` projection simp lemma that unfolds the matroid's
  `Indep` field, putting `indep_ofPolymatroidFn_iff`'s LHS out of
  simp-normal form (hard `simpNF` lint error). Fix: restrict to
  `@[simps! E]`, matching the `ofSubmodular` precedent in the same file —
  only the ground-set projection is wanted as a simp lemma.
- **L2a rank lemma (2026-06):** `polymatroid_rank_eq` (+ private
  `polymatroid_rank_eq_on_indep`) landed green, 0 sorry, closing L2a.
  Four porting points, all bounded: (i) the WIP's `Matroid.r` is now
  `Matroid.rk` (the def + every dot-lemma); the relevant renames were
  `Indep.eRk → Indep.eRk_eq_encard`, `IsBasis.r`/`IsBasis.rk_eq_rk →
  IsBasis.ncard_eq_rk` (note: the new lemma is the `ncard = rk`
  *direction*, so the rewrite gives `(↑B).ncard`, cleared with
  `Set.ncard_coe_finset`, lowercase `f`). (ii) The WIP's `self_eq_add_left`
  simp lemma was removed from this mathlib; the `a = 0 + a` residual it
  handled is closed by `simp only [zero_add, true_and]` directly (drop the
  lemma, no replacement needed). (iii) two imports the WIP got transitively
  are not in the minimal set: `Mathlib.Tactic.Cases` (for `induction'`,
  here rewritten to non-prime `induction … using … with | @h₁ Y hY IH`)
  and `Mathlib.Data.Finset.CastCard` (`cast_card_union` / `cast_card_sdiff`).
  (iv) the WIP's two `-- thanks aesop` `simp_all only [...]` lemma lists
  carried stale names (`ofPolymatroidFn_Indep`, `IndepMatroid.ofFinset_indep`)
  from the old `IndepMatroid.ofFinset`-based construction — our matroid is
  `FiniteCircuitMatroid`-built, so those projections don't exist; deleting
  them from the lists leaves `simp_all` closing both goals unchanged. General
  lesson: when porting an aesop-generated `simp_all only [long list]`, treat
  construction-specific projection names in the list as the first thing to
  prune on an "unknown identifier" — the surrounding `simp_all` is usually
  robust to their removal.
- **L2b union construction (2026-06):** `Constructions/Union.lean` —
  `AdjIndep'` + `adjMap_indep_iff'`, `Matroid.Union` / `Matroid.union`,
  `Union_empty`, `union_indep_aux{,'}`, `union_indep_iff` /
  `union_indep_iff'` — landed green, 0 sorry (partition rank theorem
  deferred to a follow-up commit). The construction reuses the live
  `Matroid.Constructions.Matching` (`adjMap` / `AdjIndep` / `IsMatching`)
  and mathlib's `Matroid.sum'`, both unchanged. Porting points, all
  bounded: (i) `Pairwise (Disjoint on t)` failed with *"Unknown identifier
  `on`"* — the ` on ` infix is `scoped` in `Function` (`Function.onFun`),
  so the file needs `open Function` (the WIP got it via a broader open).
  (ii) The WIP's `union_indep_aux'` depended on
  `Matroid.ForMathlib.Set.exists_pairwiseDisjoint_iUnion_eq`, which is
  *commented out* in the live `ForMathlib/Set.lean` (third bit-rot point
  beyond the audit, matching the L2a commented-`ForMathlib/Finset.lean`
  pattern) — reconstructed verbatim as a `private` lemma in the file.
  (iii) The WIP's `Union_empty` (`IsEmpty ι ⇒ Union = loopyOn`) leaned on
  two brittle `simp [adjMap, IndepMatroid.ofFinset, …]`-unfold lists that
  no longer close post-`FiniteCircuitMatroid`; reproved cleanly via
  `eq_loopyOn_iff` + finitarity (`adjMap` is `Finitary`), reducing to: a
  singleton `{x}` independent set would `IsMatching`-match into the empty
  type `ι × α`, contradicting `Set.bijOn_empty_iff_left`. (iv) Followed the
  project `[Finite α]`-in-signature convention over the WIP's `[Fintype α]`
  (bridge `haveI : Fintype β := Fintype.ofFinite β` inside
  `adjMap_indep_iff'`), clearing the `unusedFintypeInType` linter; added
  focus dots + the `simp?`-suggested `simp only` set to clear the
  `style.{multiGoal,flexible}` compile warnings.
- **L2b dependency re-scope (2026-06): the partition-rank target is blocked on
  an un-ported Rado/Hall sub-tree — Phase-12 audit residual.** Planning the
  partition-rank commit (`matroid_partition'` / `matroid_partition_eRk'`)
  surfaced a dependency the *Prerequisites audit* missed: their bridge
  `polymatroid_of_adjMap` (`WIP/Union.lean:258`) builds its matching via the
  **sufficiency** direction of Rado's theorem, calling `(rado M A).mpr …`
  (`WIP/Union.lean:339`). Two decoys to avoid: (i) the live
  `Matroid.Intersection.rado_necessary` is only the *easy* direction; the full
  `rado` / `rado_iff` / `rado_sufficient` there are **commented-out Lean-3**
  resting on further dead machinery (`partition_matroid_on`,
  `exists_common_ind_with_isFlat_right`). (ii) The live `rado` exists *only* in
  the **back half of the same `WIP/Submodular.lean`** L2a ported from
  (`:891`, Oxley Thm 11.2.2) — L2a stopped at `polymatroid_rank_eq` (`:~296`)
  and never reached it. `rado` rests on a self-contained, 0-sorry but ~420-line
  sub-tree (`:323–942`): `generalized_halls_marriage` (deps all in the
  L2a-ported surface), the `PartialTransversal` structure + ~30 lemmas, the
  `Transversal`/`Transverses` family, then `rado` / `rado_v2`. **Lesson:** the
  prereq-audit's "0 sorry, just rebase" reading covered only the *front* of
  `WIP/Submodular.lean`; the proof-by-grep of a vendored file's dependency
  graph must follow `.mpr`/`.1` projections of *named theorems* into the rest
  of the source, not just the import list. L2b re-scoped into L2b-rado
  (port the sub-tree) + L2b-partition (the two targets); see `notes/Phase12.md`
  *Current state* / *Layer plan* / *Hand-off*. No Lean changed this commit.
- **L2b-rado infrastructure (2026-06):** ported `WIP/Submodular.lean:323–740`
  (`generalized_halls_marriage` + `'`; the `PartialTransversal` family) into
  `Constructions/Submodular.lean`, green/0-sorry. Porting points: (i) **the WIP
  source does not build**, so its signatures are *untrustworthy* — several
  `of_fun_*` / `move_*` lemmas were missing the `[DecidableEq α]` /
  `[DecidableEq (ι × α)]` / `[Fintype ι]` instances their bodies need (`univ`,
  `Finset.filter`-decidability, `I = univ`). Lesson: when porting from a
  non-building file, treat every instance binder as a *guess* and let the
  elaborator tell you what's actually required; the `f i` "type mismatch ι vs
  ↑I" errors were a symptom of an instance failure earlier in elaboration, not
  a real binder bug. (ii) `ne_of_mem_of_notMem → ne_of_mem_of_not_mem`.
  (iii) `Fintype.choose` / `Fintype.choose_spec` need `import
  Mathlib.Data.Fintype.Inv` (not in the minimal `Matroid.*` set). (iv) `runLinter`
  gate: dropped `@[simp]` on `of_fun_mem_edges_iff` (simp-can-prove-this) and
  switched `def → lemma` on `of_fun_{left,right}_eq` (`defLemma` + `docBlame`);
  trimmed genuinely-unused `[DecidableEq α]` off `fun_{mem,inj,injective}`.
  (v) `push_neg → push Not`; `simp_wf` in the `decreasing_by` now does nothing
  (removed).
- **L2b-rado warnings sweep (2026-06):** the L2b-rado port above shipped with
  ~24 compile-time style warnings (`unusedSimpArgs` / `flexible` /
  `unusedDecidableInType` / `unusedFintypeInType`); per the warnings-clean
  policy these were all cleared in an amend, file still green/0-sorry. Mostly
  mechanical (drop `tsub_le_iff_right` + `sub_add_cancel` unused-simp pairs in
  the calc; `simp [le_eq_subset] → simp only`; drop `exists_and_right`; drop
  unused `[DecidableEq ι]` from `generalized_halls_marriage{,'}` /
  `card_eq_iff_total`, opening `classical` where the body then needs decidable
  `Function.update` — including a `classical` *inside* `decreasing_by`). The one
  non-obvious step: clearing `unusedFintypeInType` on the WF-recursive
  `generalized_halls_marriage` (swap `[Fintype ι] → [Finite ι]`) breaks its
  `termination_by ∑ i, …` measure, since `Fintype.ofFinite` is a *def* not an
  `instance`; fixed by prefixing the measure `termination_by haveI :=
  Fintype.ofFinite ι; ∑ i, (A i).card`. **Lifted to:** TACTICS-QUIRKS § 16(d).
- **L2b-rado finish (2026-06):** ported `WIP/Submodular.lean:742–942` (the
  `Transversal`/`Transverses`/`Transverses'` family, `rado_v2`, `rado`) into
  `Constructions/Submodular.lean`, green/0-sorry; `rado` is `lem:rado`. Renames
  beyond the standard `Matroid.r → rk` chase: (i) **`IsRkFinite.submod` now takes
  the second set explicitly** — `hX.submod (Y : Set α)`, not a second finiteness
  proof (the WIP passed `(M.IsRkFinite.of_finite …)` as the 2nd arg; that arg is
  now `Y : Set α`). (ii) `Indep.r → Indep.rk_eq_ncard`, `Indep.eRk →
  Indep.eRk_eq_encard`, `M.IsRkFinite.of_finite → M.isRkFinite_of_finite`,
  `Set.ncard_coe_Finset → Set.ncard_coe_finset`. (iii) `[Fintype ι] → [Finite ι]`
  + `haveI := Fintype.ofFinite ι` (statements have no `Fintype.card ι`); the
  `Transverses (image f univ)`-shaped lemmas keep `[Fintype ι]` since `univ :
  Finset ι` is in the *type*. (iv) `runLinter`/warnings: dropped the bit-rotted
  `[DecidableEq ι]` on `Transversal` (`unusedArguments` — the def is decidability-
  free) and the now-unused `[DecidableEq ι]`/`[Fintype α]` on `rado`/`rado_v2`;
  `push_neg → push Not`; `Finset.toSet → (· : Set α)`. (v) An over-aggressive
  `simpa [mem_image, mem_univ, true_and] using x.property` collapsed the hyp to
  `True`; replaced with `obtain ⟨i, _, hi⟩ := mem_image.mp x.property`.
- **L2b-partition finish (2026-06, closes Phase 12):** ported
  `WIP/Union.lean`'s `polymatroid_of_adjMap` (the bridge — `adjMap`-matroid as
  `ofPolymatroidFn` of `f Y = M.rk (N Adj Y)`; sufficiency direction calls
  `(rado …).mpr`), `adjMap_rank_eq`, `sum'_eRk_eq_eRk_sum{_on_indep}` /
  `sum'_rk_eq_rk_sum`, and `matroid_partition'` / `matroid_partition_eRk'`
  (node `thm:matroid-partition-rank`) into `Constructions/Union.lean`,
  green/0-sorry. Also added `PolymatroidFn_of_zero` to `Submodular.lean` (the
  `isEmpty α` branch of `polymatroid_of_adjMap` needs it). Warnings-clean sweep
  (~28 warnings on first build, same class as the L2b-rado sweep): dropped many
  bit-rotted unused `simp only` args (`Classical.not_imp`, `le_eq_subset`,
  `mem_setOf_eq`, `N`/`N_singleton`/`he'` set-aliases, `hf`/`hN`); `[Fintype α]
  → [Finite α]` + `haveI := Fintype.ofFinite α` on the five theorems whose type
  has no `Fintype.card α` (`matroid_partition'` keeps `[Fintype α]` — `Finset.univ
  : Finset α` is in its type); `Finset.toSet → (· : Set _)`,
  `ncard_image_of_injOn → InjOn.ncard_image`; long-line wraps. `lake lint`
  flagged `sum'_eRk_eq_eRk_sum_on_indep` `@[simp]` as simp-can-prove (the general
  `sum'_eRk_eq_eRk_sum` subsumes it) — dropped the `@[simp]` (stays callable by
  name). `#print axioms` on all four targets = `propext`/`Classical.choice`/
  `Quot.sound` only.

### [resolved] `Polynomial.X` in a `set := ... .det` binding needs an explicit type ascription
- **Where it bit:** `exists_affinelySpanning_rigid_placement` in
  `RigidityMatroid.lean` (Phase 6, original site) and
  `finite_setOf_not_linearIndependent_rows_along_affine_path` in
  `Mathlib/LinearAlgebra/Matrix/Rank.lean` (Phase 8, second site).
- **Resolution:** annotate the literal explicitly,
  `(Polynomial.X : Polynomial ℝ) • …`. Two-site recurrence triggered
  promote-to-TACTICS-QUIRKS at post-Phase-8 cleanup D2.
- **Lifted to:** `TACTICS-QUIRKS.md` § 15 *Bare `Polynomial.X`
  (or `0`, `1`) needs explicit type ascription in `let`/`set` of a
  `Polynomial`-valued expression*.

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

### [resolved] No mathlib bridge `AffineIndependent ℝ p ↔ LinearIndependent ℝ (p̄ = (p,1))`
- **Where it bit:** Phase 17, `lem:affine-indep-iff` in
  `Molecular/Extensor.lean`. KT's homogeneous coordinatization
  `p ↦ (p,1)` needs "affinely independent ⇔ homogenized family linearly
  independent". mathlib has the *vsub* form
  (`affineIndependent_iff_linearIndependent_vsub`) but no `(p,1)`-snoc
  homogenization bridge (searched: no `Homogenize`/`snoc`+`AffineIndependent`).
- **Resolution:** no mirror needed — `affineIndependent_iff` (the
  `V → V` self-affine-space characterization: affine indep ⇔ every `w`
  with `∑w=0` and `∑ w•p=0` is zero) *is* the homogenized
  linear-independence condition once you `linearIndependent_iff'` the
  RHS: the last homogeneous coordinate of `∑ w•p̄ = 0` is `∑w=0`, the
  first `d` are `∑ w•p=0`. Split coordinatewise via
  `Fin.lastCases` / `homogenize_last` / `homogenize_castSucc`. The
  `def`-bridge `homogenize := Fin.snoc p 1` is project-specific (KT
  coordinatization), so the lemma stays project-internal in
  `Molecular/`, not mirrored. Determinant form on top via
  `Matrix.linearIndependent_rows_iff_isUnit` + `isUnit_iff_isUnit_det`
  + `isUnit_iff_ne_zero`. The row-identity step `(fun i => …) =
  (Matrix.of …).row` is exactly mathlib's `Matrix.of_row` (used reversed,
  with the function given explicitly so the rewrite metavariable
  resolves) — Phase 17-cleanup B5/B7 replaced the original anonymous
  `show … from rfl` with `← Matrix.of_row _`; a residual bare `rfl`
  still bridges the `.det` side (`Matrix.of`-applied vs bare det, defeq).

### [resolved] `Finset.univ.filter`-of-`Finset V` over `[Finite V]` triggers cascading instance synthesis friction
- **Where it bit:** Phase 7 Commit 17b's `IsSparse.maxBlock`
  (`Sparsity.lean`). Initial attempt defined `maxBlock X` as
  `(Finset.univ : Finset (Finset V)).filter (...).sup id` with
  `letI := Fintype.ofFinite V` inside the `by` body. Cascade:
  (a) `Finset.univ : Finset (Finset V)` needs `Fintype V` (via
  `Fintype.ofFinite`); (b) the `filter` predicate isn't auto-Decidable
  so needs `Classical.decPred`; (c) `Finset.sup` over `Finset V`
  needs `SemilatticeSup (Finset V)` which requires `DecidableEq V`;
  (d) `unfold IsSparse.maxBlock` in proofs exposes the `letI` /
  `Classical`-derived instance terms, and matching against
  proof-side `letI` / `classical` instances either fails defeq or
  times out at `whnf`.
- **Friction:** burned several iterations on `letI`/`haveI` and
  `open Classical in` variants before the `change` tactic timed out
  at 200000 heartbeats trying to match `hI.maxBlock X = F.sup id`.
- **Proposed fix:** define the family as a `Set V`-valued union
  (`⋃ S, ⋃ _, (↑S : Set V)`) — no `Finset.univ`, no `Fintype`, no
  `DecidablePred` — and convert to `Finset V` via
  `Set.Finite.toFinset` (justified by `[Finite V]` + subset of
  univ). The I-tightness proof then bridges to a Finset-join form
  in *one* spot, via `Finset.ext` + a local `Fintype.ofFinite V` +
  `classical`, isolating the instance friction. `mem_maxBlock`
  becomes the standard `Set.Finite.mem_toFinset` + `Set.mem_iUnion`
  + `and_assoc` simp recipe.
- **Status:** resolved (see `SimpleGraph.maxBlock` and surrounding
  lemmas in `Sparsity.lean`; the def was renamed from
  `IsSparse.maxBlock` to `SimpleGraph.maxBlock` in Phase 7 cleanup
  commit B3e). **Lifted to:** TACTICS-QUIRKS § new
  *Finset-of-Finsets over `[Finite V]`*.

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

### [resolved] "Test motion `x_α`" gadget in Phase 7 understated by blueprint prose

- **Where it bit:** `typeI_edgeSetRowIndependent_extend`
  (`MatroidIdentification.lean`). The blueprint prose for new-row LI
  and old-vs-new disjointness invoked "the same trick" — but the Lean
  expanded "the trick" into a `set x_α := fun w => w.elim α 0`
  binding plus a 12-line `Submodule.span_le` / `LinearMap.mem_ker`
  argument that the old-row span vanishes at `x_α`. The private
  helper `typeI_new_rows_coeff_zero` packages the
  coefficient-extraction.
- **Friction:** prose-to-Lean gap; the test-motion gadget is a
  substantive construction that should appear in the blueprint
  prose as a named gadget, not as "the same trick".
- **Resolution:** two-pronged.
  - **Lean (12 lines → 9):** consolidated the `Submodule.span_le`
    block by folding `SetLike.mem_coe` + `LinearMap.mem_ker` +
    `Module.Dual.eval_apply` into a single `simp` set and tightening
    the destructure (`rintro _ ⟨e, ⟨⟨e0, he0⟩, rfl⟩, rfl⟩` skips the
    intermediate `obtain` of the old `g`-binding). The trailing
    `have := h_le hf_old; rwa [...]` collapses to `simpa using h_le
    hf_old`. Cosmetic-ish but the proof now fits on screen as a
    single visual unit.
  - **Blueprint:** named the gadget as a parametric **test motion**
    $x_\alpha$ with $x_\alpha(\mathrm{none}) = \alpha$ and
    $x_\alpha \circ \mathrm{some} = 0$; restructured the proof
    sketch around it so both the new-row LI and the disjointness
    claim cite the same construction explicitly, rather than
    invoking "the same trick".
- **Lesson:** the "span vanishes if generators vanish" pattern has no
  packaged mathlib lemma — `Submodule.span_le` + a kernel-of-`Module.
  Dual.eval` framing is the idiomatic chain. The friction was less
  about Lean depth and more about *naming* the gadget so the
  blueprint matches the structure of the formal proof.
- **Status:** resolved (2026-05-15).

### [resolved] `elemSkewMap_ofLp_inr_apply` proof collapse via wider simp + grind

- **Where it bit:** `trivialMotionFamily_linearIndependent`
  (`TrivialMotions.lean`). The `elemSkewMap_ofLp_inr_apply`
  helper unpacked a `Eᵢⱼ - Eⱼᵢ`-style entry into specific coordinate
  cases, closed by `grind`.
- **Friction:** the original proof ran `change` (to unfold `⟨a, b⟩.fst`
  and `.ofLp i`) → `rw [elemSkewMap_apply]` → `simp only [...]` →
  `rcases ... <;> split_ifs <;> grind`. Six tactic lines for what's
  ultimately one case analysis.
- **Resolution:** stripped to `rcases eq_or_ne i a with rfl | hia <;>
  simp [elemSkewMap_apply] <;> grind`. The `simp [elemSkewMap_apply]`
  (rather than `simp only [...]`) lets the default simp set drop
  `⟨a, b⟩.fst` / `.ofLp i` / `PiLp.single` boilerplate that previously
  needed manual rewrites, and `grind` absorbs the `split_ifs` step.
  Net 6 tactic lines → 1. Tried the `Matrix.stdBasisMatrix`-difference
  framing as the friction entry proposed; not a clean simplification
  (would require an `elemSkewMap = Matrix.toEuclideanLin (E_{ij} -
  E_{ji})` rewrite, which adds `WithLp` / `toLin` bridge overhead and
  changes the rest of the API).
- **Lesson:** when a proof leans on `change` + multi-step `rw` to set
  up a tightly-shaped goal for `grind`, try a wider `simp` (default
  set, not `simp only [...]`) first — the default simp set often
  absorbs the same boilerplate without the explicit bookkeeping. The
  `split_ifs` step is also usually redundant when `grind` follows.
- **Status:** resolved (2026-05-15).
- **Lifted to:** TACTICS-GOLF § 1 *Tricks we've found useful* →
  "Default `simp` before `grind` can subsume `change` + multi-`rw`
  staging".

### [resolved] Extending a function on a subtype to the parent type — `dite` vs `Function.extend`

- **Where it bit:** `linearRigidityRow` (`LinearRigidityMatroid.lean`),
  Phase 8 scaffolding. Needed a function
  `Sym2 V → Module.Dual ℝ (Framework V d)` extending
  `(⊤ : SimpleGraph V).rigidityRow p : (⊤).edgeSet → Module.Dual …`
  by zero off the edge set, to feed `Matroid.ofFun`.
- **Friction:** the dependent `if h : e ∈ (⊤).edgeSet then …⟨e, h⟩ else
  0` shape required `Decidable (e ∈ (⊤ : SimpleGraph V).edgeSet)`,
  which isn't synthesisable for an arbitrary `Set` membership without
  pulling in `Classical` (or a per-graph decidability instance the
  call site can't supply).
- **Resolution:** switched to
  `Function.extend Subtype.val ((⊤).rigidityRow p) 0`. Both the on-set
  characterisation (`linearRigidityRow_subtype_val`) and the
  membership-form (`linearRigidityRow_of_mem`) close in one line via
  `Subtype.val_injective.extend_apply`. No `Decidable` instance
  needed; the def stays `noncomputable` either way.
- **Lesson:** for "extend a function on a subtype to the parent type
  by a constant", prefer `Function.extend (Subtype.val) f c` over
  `dite (· ∈ S) (fun h ↦ f ⟨·, h⟩) (fun _ ↦ c)`. The `dite` form
  forces a `Decidable` instance that's typically classical-only for
  `Set`s; the `Function.extend` form uses
  `Function.Injective.extend_apply` for clean rewriting.
- **Status:** resolved (2026-05-16).

### [resolved] `LinearMap.proj u - LinearMap.proj v` over a Pi type elaborates stuck

`def screwDiff (u v : α) : (α → W) →ₗ[ℝ] W := LinearMap.proj u - LinearMap.proj v`
fails with *"typeclass instance problem is stuck … `(i : α) → Module ?m (?φ i)`"*:
the `-` unifies the two `proj` summands before the declared codomain, leaving the
Pi fiber metavariable. Fixed by type-ascribing the first summand to the full
`LinearMap` type (`(R := ℝ)` alone is insufficient). Hit building
`BodyHingeFramework.screwDiff` in `Molecular/RigidityMatrix.lean` (Phase 21b
rigidity-matrix row-functional plumbing). **Lifted to:** TACTICS-QUIRKS § 30.

### [resolved] `rw [columnOp_apply]` (a `@[simps! apply]` `LinearEquiv` lemma) won't fire on `⇑(columnOp hva) (update S v 0)` — `unfold columnOp` instead, or compute the result pointwise via `show … from by funext`
- **Where it bit:** `comp_columnOp_comp_offProj_of_single_eq_zero` (W6a brick 2,
  `Molecular/RigidityMatrix.lean`, Phase 22h). After reducing `P_v S` to `update S v 0`,
  the goal `g (columnOp hva (update S v 0)) = g S` needed `columnOp hva (update S v 0) =
  update S v (S a)`, but `rw [columnOp_apply]` failed ("Did not find … `(columnOp ?hva)
  ?S ?a`") — the `@[simps! apply]`-generated lemma's LHS coercion form didn't match the
  `⇑e`-applied term here (it fires fine when the `columnOp` is freshly introduced, as in
  `columnOp_apply_single`, but not after the `LinearEquiv.coe_coe`/`hPv`-rewrite cascade).
- **Fix:** `rw [show (columnOp hva) (update S v 0) = update S v (S a) from by funext y;
  unfold columnOp; rcases eq_or_ne y v with rfl | hy; · simp […]; · simp […]]` — `unfold
  columnOp` exposes the raw `toFun` lambda the funext/`simp` then discharge pointwise.
- **Status:** resolved (tactic choice; no lemma needed). Sibling of TACTICS-QUIRKS § 6
  (a `simps`/`def`-bound coercion that `rw` can't see — prefer `unfold` + pointwise, or a
  hand-stated `show … from`).

### [resolved] `set X := e with hX` silently folds `e` in *pre-existing* hypotheses → a later `rw [h]` (whose LHS was `e`) finds no pattern
- **Where it bit:** `exists_candidateRow_bottomRows_of_rigidOn` (W6b, `Molecular/AlgebraicInduction/CaseI.lean`,
  Phase 22h). `set Eb := Submodule.span ℝ (Set.range r)` ran *after* obtaining W5's
  `hrspan : span (range r) = span (panelRow e₀)`, so the `set` rewrote `hrspan` to `Eb = …`; the
  next `rw [hEb, hrspan]` (and a sibling `rw` in `hrow`) then failed to find `span (range r)`.
- **Fix:** drop the redundant `rw` and lean on the fold — `hrspan` already reads `Eb = …`, so the
  chains became `rw [hrspan, …]` (no `rw [hEb]` first). Captured a derived form `hEb'` once.
- **Status:** resolved. **Lifted to:** TACTICS-QUIRKS § 43 (general rule: after a `set`/`subst`/
  `simp only [eqn] at *`, re-read what old hypotheses now say before threading them into a `rw`).

### [resolved] A combining-diacritic identifier (`ρ̂` = `ρ` + U+0302) is rejected by the lexer — *"expected token"*
- **Where it bit:** `case_III_candidate_dispatch` (W10b, `Molecular/AlgebraicInduction/CaseI.lean`,
  Phase 22h). The design doc's normalized candidate functional was written `ρ̂` (base rho + a
  *combining* circumflex, two codepoints); a `obtain ⟨ρ̂, …⟩` failed to parse — Lean's lexer does
  not treat the combining mark as an identifier-continuation character (precomposed letters like
  `ŵ` U+0175 are fine).
- **Fix:** renamed to the ASCII-decorated `ρ0`/`w0` family.
- **Status:** resolved. **Lifted to:** TACTICS-QUIRKS § 45 (incl. the codepoint-dump detection
  one-liner).

### [resolved] `Matrix.cons_val_zero` won't fire on `![…] ⟨0, ⋯⟩` after `fin_cases` (a `Fin.mk`, not the literal)
- **Where it bit:** `case_III_candidate_dispatch` (W10b, `Molecular/AlgebraicInduction/CaseI.lean`,
  Phase 22h). After `fin_cases u` on the discriminator's `u : Fin 3`, the per-branch hypotheses
  read `![na, nb, nc] ⟨0, ⋯⟩` — the anonymous-constructor `Fin.mk`, which `simp only
  [Matrix.cons_val_zero]` reports as unused (its LHS keys on the `0` literal).
- **Fix:** prepend `show (⟨0, by omega⟩ : Fin 3) = 0 from rfl` (resp. `= 1`, `= 2`) to the
  per-branch `simp only` set so the index normalizes first.
- **Status:** resolved. **Lifted to:** TACTICS-QUIRKS § 46.

### [resolved] `letI` (not `haveI`) to shadow `Submodule.addCommMonoid` with `AddCommGroup` for ring-path lemmas on submodule subtypes
- **Where it bit:** Phase 22i L5a-i (`RigidityMatrix.lean`,
  `le_finrank_span_rigidityRows_of_splice`). Calling
  `(D.domRestrict S).ker.finrank_quotient_add_finrank` (which requires `[Ring R] [AddCommGroup M]`)
  or `(D.domRestrict S).quotKerEquivRange` with `S : Submodule ℝ V` where `V` is an `AddCommGroup`
  failed with *"Application type mismatch: … has type `S.addCommMonoid` but expected
  `AddCommGroup.toAddCommMonoid`"* even after `haveI : AddCommGroup ↥S := S.addCommGroup`.
- **Cause:** Two `AddCommMonoid ↥S` instances for a submodule of an `AddCommGroup` module —
  `Submodule.addCommMonoid p` (Semiring/AddSubmonoid path) and
  `Submodule.addCommGroup p |>.toAddCommMonoid` (Ring/AddSubgroup path) — are **not**
  definitionally equal in Lean 4 (the error reports "synthesized `S.addCommMonoid` inferred
  `hSAG.toAddCommMonoid`"). `haveI` enters only the local context; it does not shadow the
  global `Submodule.instAddCommMonoidSubtypeMemSubmodule`. **`letI` does.**
- **Fix:** `letI hSAG : AddCommGroup ↥S := S.addCommGroup` (NOT `haveI`) before any call to
  `domRestrict`, `quotKerEquivRange`, or `finrank_quotient_add_finrank` on a subtype of a
  submodule. Do not `set N := (D.domRestrict S).ker` before `letI` — the `set` re-embeds
  `Submodule.addCommMonoid` into `N`'s type before the shadowing takes effect.
- **Status:** resolved. **Lifted to:** TACTICS-QUIRKS § 54.

### [resolved] ℕ-subtraction in a theorem statement causes `ring` to fail
- **Where it bit:** Phase 22i L1d (`Deficiency.lean`, `partitionDef_split_of_sides`).
  The statement `+ bodyBarDim n - (bodyBarDim n - 1) * c` has `(bodyBarDim n - 1 : ℕ)` as
  ℕ-subtraction, coerced to ℤ as `↑(n - 1 : ℕ)`. After `push_cast`, this differs from
  `(↑n - 1 : ℤ)`, so `ring` sees two distinct atoms and fails.
- **Fix:** write `((bodyBarDim n : ℤ) - 1) * c` in the statement — explicit ℤ subtraction.
  General rule: in theorem *statements* mixing `ℕ` quantities and `ℤ` arithmetic, cast
  before subtracting (`(↑n - 1 : ℤ)`) rather than subtract-then-cast (`↑(n - 1 : ℕ)`).
  **Lifted to:** TACTICS-QUIRKS § 47.
- **Status:** resolved.

### [resolved] "Brick" is a project mnemonic, not KT's term — terminology dictionary and vocabulary gate landed
- **Where it bit:** the post-Phase-22 RigidityMatrix split carved the three rank-addition
  sections into `Molecular/RigidityMatrix/Bricks.lean`; the file name surfaced the question.
- **Friction:** "brick" occurs in KT 2011 *exactly once* — a bibliography entry citing
  Jackson–Jordán *"Brick partitions of graphs"* (2008), an unrelated concept; KT's §6.1 rank
  argument is never "brick" anything (and "block-triangular", which the blueprint pairs with
  it, has 0 hits in KT — also project framing). The term is nonetheless established project
  shorthand: section names `CutEdgeBrick`/`SpliceBrick`/`PinnedPlacementBrick`, "brick" in
  `rigidity-matrix.tex` lemma *titles*, and ~25 notes/source files. The *formal* lemma names
  are KT-faithful (`le_finrank_span_rigidityRows_of_{cut,splice,pinned_placement}`); "brick"
  only ever rides as an informal label.
- **Resolution:** Phase 23-cleanup task D2 settled the terminology dictionary (Phase 23-cleanup post-Phase-23 cleanup round, 2026-07): "brick" → "rank-addition lemma / rank bound (KT §6.1 language)". The entry appears in the canonical table at `blueprint/AUTHORING.md` *Audience & vocabulary*, the authoritative source for reader-facing prose in the molecular chapters. Phase 23-cleanup task P1 implemented the enforcing gate in `blueprint/lint.sh` (check 5a: banned project-internal words), which flags any remaining "brick" occurrences in reader-facing prose except when adjacent to the separator characters of a `\label{}`/`\lean{}`/`\cref{}`/`\uses{}` identifier token (the `intro.tex` carve-out belongs to sub-check 5b, phase self-description — not to 5a). All R-tasks (R0–R11) passed this gate green on 2026-07-05. Lean file/section names (e.g. `Bricks.lean`) remain invisible to blueprint readers and are unaffected by the terminology rule.
- **Status:** resolved (Phase 23-cleanup D2 + P1, 2026-07-05).
