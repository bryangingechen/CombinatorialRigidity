# Phase 3 — Henneberg moves (work log)

**Status:** in progress.

This file is the per-phase work record. See `../ROADMAP.md` for the
high-level plan and `../DESIGN.md` for cross-cutting design choices.

## Current state

Both Henneberg moves provably preserve the Laman property
(`typeI_isLaman`, `typeII_isLaman`), the `K₄ \ e` worked example
(`top_fin_four_minus_edge_isLaman`) lands via iso transport, and the
**iso half of the structural decomposition** is done:
`IsLaman.exists_typeI_or_typeII_iso` says every Laman graph on `n ≥ 3`
vertices is iso to a Type I or Type II move applied to *some* graph
`G'`. **It does not claim `G'.IsLaman`** — that is the deeper
"Laman-preservation under reverse Henneberg moves" direction, which
turned out to be substantially harder than the Phase-start hand-off
suggested and is now deferred to Phase 5.

Supporting helpers added this session:
* `IsLaman.exists_nonadj_among_three_neighbors` (in `Laman.lean`) —
  given a degree-3 neighborhood `{a, b, c}` of `v` in a Laman graph,
  some pair is non-adjacent. Sparsity at `{v, a, b, c}` (size 4, ≤ 5
  edges) minus the three known `v`-edges leaves ≤ 2 edges among
  `{a, b, c}`, hence a non-edge. Counts the 6 candidate edges as a
  literal `Finset` via `Finset.card_insert_of_notMem` chain; pairwise
  distinctness closes by `simp [Sym2.eq_iff]; tauto`.
* `Henneberg.typeI_iso_of_two_neighbors`,
  `Henneberg.typeII_iso_of_three_neighbors` (private, in
  `Henneberg.lean`) — the iso constructions, parameterised on a
  membership-style `hN : ∀ w, G.Adj v w ↔ w = a ∨ w = b (∨ w = c)`
  which is what the surrounding caller can produce from
  `Finset.card_eq_two.mp` / `Finset.card_eq_three.mp` plus
  `mem_neighborFinset`. Underlying equiv is
  `(Equiv.optionSubtypeNe v).symm`.

**Next concrete task** (one sentence): prove
`IsLaman.exists_typeI_or_typeII_reverse` — the strengthened version
that *also* asserts `G'.IsLaman`. This is the remaining Phase-5-bound
task and is genuinely hard: the typeII reverse case can fail for an
arbitrary non-adjacent neighbor pair, so it requires the classical
Henneberg "blocker"/contradiction argument that finds a specific
non-adjacent pair `{a, b}` for which `G'` is Laman. See `FRICTION.md`
entry "[open] typeII reverse Laman preservation" and ROADMAP §5 for
the obstruction.

## Architectural choices made up front

These diverge from the ROADMAP's original wording. Both are recorded in
`../DESIGN.md` "Choices to revisit"; if either turns out wrong, revisit
there.

- **Type-bumping via `Option V`.** The fresh vertex is `none`; old
  vertices embed via `some`. Validated by `typeI`'s clean structural
  Adj definition and the working edgeSet decomposition. The cost
  surfaced is Sym2 case analysis when relating `Sym2.map some` images
  to concrete `s(none, _)` patterns; this is workable but verbose.
- **No `Reachable` inductive.** Henneberg's theorem will be expressed
  via a structural decomposition lemma plus strong induction on
  `Fintype.card V`. Phase 3 builds the preservation half; Phase 5 will
  use the decomposition and induction directly.
- **Structural `Adj` definition (not lattice).** `typeI` and `typeII`
  use a `match`-based `Adj` (e.g. `| some u, some v => G.Adj u v | …`)
  rather than `G.map .some ⊔ fromEdgeSet …`. This makes all eight
  adjacency lemmas `Iff.rfl` and avoids existential elimination
  (`(G.map f).Adj` unfolds to `∃ u' v', …`) in every adjacency proof.
  Cost: edgeSet decomposition needs explicit Sym2 case analysis rather
  than coming free from `edgeSet_sup`/`edgeSet_map`. The earlier
  lattice attempt is documented in commit history.

## Lemma checklist

### Definitions (this session)
- [x] `Henneberg.typeI G a b : SimpleGraph (Option V)`.
- [x] `Henneberg.typeII G a b c : SimpleGraph (Option V)`.

### typeI API (this session)
- [x] `typeI_adj_some_some`, `typeI_adj_some_none`,
  `typeI_adj_none_some`, `typeI_not_adj_none_none` — all `Iff.rfl`.
- [x] `typeI_edgeSet` — `(Sym2.map some '' G.edgeSet) ∪ {s(none, some a), s(none, some b)}`.
- [x] `typeI_edgeSet_ncard` — under `a ≠ b`, `((typeI G a b).edgeSet).ncard = G.edgeSet.ncard + 2`.

### typeII API
- [x] Adjacency lemmas (4, all `Iff.rfl`).
- [x] `typeII_edgeSet` — parallel decomposition with the
  `\ {s(a, b)}` deletion and three new edges, closed by the same
  3-line template as `typeI_edgeSet` once
  `Sym2.exists_and_map_eq_mk_iff` (mirror) is available.
- [x] `typeII_edgeSet_ncard` — under `a ≠ b`, `c ≠ a`, `c ≠ b`,
  `((typeII G a b c).edgeSet).ncard = (G.edgeSet \ {s(a, b)}).ncard + 3`.
  Stated over the deletion-set so the lemma does not require
  `G.Adj a b`; consumers wanting the `+ 2` form (over `G.edgeSet`)
  specialize via `Set.ncard_diff_singleton_add_one` under
  `s(a, b) ∈ G.edgeSet`.

### Phase 1 carryover
- [x] `edgesIn_singleton` (in `EdgesIn.lean`) — `G.edgesIn {v} = ∅`,
  needed for the `s'.card = 1` case of `typeI_isLaman` sparsity.

### Preservation theorems (this session)
- [x] `typeI_isLaman` — Type I preserves Laman, under `a ≠ b`.
  Sparsity is by case split on `none ∈ s` and on `s'.card`; the
  `s'.card = 1, none ∈ s` sub-case requires showing `T ⊆ {s(none, some w)}`
  (where `s' = {w}`) since the trivial `T.ncard ≤ 2` bound is too loose.
- [x] `typeII_isLaman` — Type II preserves Laman, under `a ≠ b`,
  `c ≠ a`, `c ≠ b`, and `G.Adj a b`. Mirrors `typeI_isLaman` with two
  extra wrinkles: (i) the deleted edge `s(a, b)` interacts with the
  three new edges via a uniform `+ 2` bound — either `s(a, b)` was in
  `G.edgesIn ↑s'` (loses 1, T'.ncard ≤ 3) or it wasn't (T'.ncard ≤ 2,
  because `a ∉ s' ∨ b ∉ s'`); (ii) the inline `edgesIn` decomposition
  needs a final `try tauto` to clean up conjunct re-grouping that
  `simp` leaves for the `s(some u, some v)` case.

  Note: `typeI_edgesIn_ncard_le` did not need to be factored as a
  named lemma; the bound is inlined inside the `none ∈ s` branch of
  `typeI_isLaman`. If a third caller materializes (e.g. for the
  decomposition theorem), promote it then.

  Both proofs use `[Finite V]` plus `have : Fintype V := Fintype.ofFinite V`
  so callers don't have to manage a `Fintype` instance.

### Iso-transport infrastructure (this session)
- [x] `SimpleGraph.Iso.image_edgesIn` (in `Sparsity.lean`) —
  `Sym2.map φ '' G.edgesIn s = H.edgesIn (φ '' s)` for any graph iso `φ`.
  The `edgesIn` analogue of mathlib's `Iso.image_neighborSet`.
- [x] `IsSparse.iso`, `IsTight.iso` (in `Sparsity.lean`) — `(k, ℓ)`-
  sparsity / tightness preserved under graph isomorphism. Both are
  one-line consumers of `image_edgesIn` plus standard `Set.ncard` /
  `Nat.card` transport via `Iso.mapEdgeSet` and `φ.toEquiv`.
- [x] `IsLaman.iso` (in `Laman.lean`) — one-liner specialization of
  `IsTight.iso` at `(k, ℓ) = (2, 3)`.

### K₄ \ e worked example (this session)
- [x] `instDecidableTypeIAdj`, `instDecidableTypeIIAdj` —
  `DecidableRel` for the move-graphs given `[DecidableEq V]` and
  `[DecidableRel G.Adj]`. Needed so `decide` can close the `map_rel_iff'`
  branches in the iso construction.
- [x] `Henneberg.fin4equiv` (private), `Henneberg.fin4iso` (private) —
  the explicit bijection and graph iso to `K₄ \ {s(2, 3)}`. The iso's
  `map_rel_iff'` is one `rintro <;> first | decide | …` line.
- [x] `top_fin_four_minus_edge_isLaman` — `IsLaman.iso fin4iso` applied
  to `typeI_isLaman` doubled from `top_fin_two_isLaman`.

### Decomposition iso (this session)
- [x] `IsLaman.exists_nonadj_among_three_neighbors` (in `Laman.lean`)
  — supporting helper for the typeII branch.
- [x] `Henneberg.typeI_iso_of_two_neighbors`,
  `Henneberg.typeII_iso_of_three_neighbors` — private iso helpers.
- [x] `IsLaman.exists_typeI_or_typeII_iso` — main result. Picks `v`
  with `2 ≤ G.degree v ≤ 3`, lifts neighbors via
  `Finset.card_eq_two/three.mp`, and for the typeII branch rotates
  through the three neighbor permutations to land on whichever pair
  is non-adjacent. `G'` is the induced subgraph, plus the bridging
  edge `s(a, b)` for typeII.

### Deferred to a later phase (Phase 5 candidate)
- [ ] `IsLaman.exists_typeI_or_typeII_reverse` — the strengthened
  version that also asserts `G'.IsLaman`. The typeII case requires
  the Henneberg combinatorial argument (a non-adjacent pair `{a, b}`
  whose `G'` is Laman exists; not every non-adjacent pair works). See
  `FRICTION.md` entry on this and ROADMAP §5.

## Decisions made during this phase

(Phase-local trade-offs; cross-cutting ones go in `../DESIGN.md`.)

- **Split the decomposition theorem into iso-only + Laman-claim.**
  The Phase 3 hand-off treated `IsLaman.exists_typeI_or_typeII_reverse`
  as one theorem combining (a) the canonical iso `G ≃g typeI/II G'`
  and (b) `G'.IsLaman`. Working through the proof revealed (b) is
  much harder for typeII than the hand-off implied: an arbitrary
  non-adjacent neighbor pair `{a, b}` does not always give a Laman
  `G'` (concrete 6-vertex counter-example: `V = {v, x, y, z, w₁, w₂}`,
  edges `{v-x, v-y, v-z, x-z, x-w₁, x-w₂, y-w₁, y-w₂, w₁-w₂}` —
  Laman, with `v` of degree 3 to `{x, y, z}`; the pair `{x, y}` is
  non-adjacent but `G' = (G - v) + edge(x, y)` violates sparsity at
  `{x, y, w₁, w₂}` (6 edges where `(2, 3)`-sparsity allows 5)). The
  classical Henneberg theorem chooses a *specific* non-adjacent pair
  via a "blocker" argument (page-long graph theory). We split: this
  phase delivers the iso half (`exists_typeI_or_typeII_iso`); Phase 5
  will need the Laman half if the induction route demands it.

- **Iso construction parameterised on `hN : ∀ w, G.Adj v w ↔ w = a ∨ w = b (∨ w = c)`
  rather than `G.neighborFinset v = {a, b}`.** Both convey "the
  neighbors are `a` and `b`," but the iff form is what
  `typeI_adj_none_some` / `typeII_adj_none_some` reduce to after
  `rw`, so the iso closes by `rw [..., hN]; simp` rather than
  needing extra `mem_neighborFinset` glue. The caller produces `hN`
  in one line from `Finset.card_eq_two.mp`.

- **Iso closes by `rw [Equiv.optionSubtypeNe_symm_*, *_adj_*]; simp` per case.**
  The `(Equiv.optionSubtypeNe v).symm` only has explicit-rewrite
  lemmas (`_symm_self`, `_symm_of_ne`), not simp ones, so we lead
  each case with the appropriate explicit `rw`. After the rewrite
  the goal has only Subtype-equality / disjunction shape left, and
  bare `simp` (or `simp [Subtype.mk.injEq]`) closes it. The
  `(some, some)` arm of typeII needs an extra `constructor` +
  `rcases` since `simp` does not eliminate the `s(...) ≠ s(...)`
  conjunct via the `¬ G.Adj a b` hypothesis on its own.

- **Use the structural `match`-based `Adj` for `typeI`/`typeII`.** First
  attempted the lattice form `G.map .some ⊔ fromEdgeSet …` to inherit
  `edgeSet_sup`/`edgeSet_map` for free, but the resulting adjacency
  proofs needed manual existential elimination on `(G.map f).Adj`'s
  unfolding `∃ u' v', G.Adj u' v' ∧ f u' = u ∧ f v' = v`, which simp
  did not fully discharge. Reverted to the structural form: adjacency
  lemmas become `Iff.rfl`, edgeSet decomposition becomes a one-time
  manual proof.
- **`Sym2.eq_iff` for edgeSet equalities, not the lattice.** Working
  with `Sym2.map some e' = s(x, y)` originally required `Sym2.eq_iff`
  plus `Option.some.injEq` and `Sym2.map_mk` — a fixed but workable
  idiom. The follow-on session resolved this by adding the
  predicate-form simp lemma `Sym2.exists_and_map_eq_mk_iff` to the
  mirror, after which both `edgeSet` decompositions close in three
  lines. See FRICTION.md (resolved entry).

- **Factor the `edgesIn` decomposition out of each `_isLaman` proof.**
  Originally inlined: the `(typeI G a b).edgesIn ↑s = … ∪ T` equality
  is shaped slightly differently per move (T is 2-element for typeI,
  3-element for typeII; typeII also carries the `\ {s(a, b)}` on the
  image side), so a single shared helper wasn't natural and the
  per-move duplication seemed not to pay for itself. After the
  `eraseNone` refactor cleaned up the surrounding `set s'` / `hcoe`
  plumbing, the residual duplication (~14 lines per branch of
  `h_decomp` / `h_disj` / `h_ncard` setup) became the dominant cost.
  Resolved by extracting `typeI_edgesIn_ncard_decomp` and the typeII
  analogue (each placed between the corresponding `_edgeSet_ncard`
  and `_isLaman`), which collapsed each sparsity branch to ~9 lines
  of `set` + bound declaration before the math case-split. Logged in
  FRICTION.md (resolved).

- **`s'.card = 1` sub-case needs explicit subset reasoning.** The
  uniform bound `T.ncard ≤ 2` (resp. `T'.ncard ≤ 3`) is one too loose
  here: when `s' = {w}` and `none ∈ s` we need `T.ncard ≤ 1`. Solved by
  showing `T ⊆ {s(none, some w)}`: each `e ∈ T` is `s(none, some v)`
  with `some v ∈ s`, so `v ∈ s' = {w}`, so `v = w`. Same shape for
  both `typeI` and `typeII`.

- **`tauto` cleanup for `typeII` `edgesIn` decomposition.** The simp
  normal form of `(typeII G a b c).Adj (some u) (some v)` after
  unfolding leaves `(G.Adj u v ∧ p) ∧ q` while the RHS produces
  `(G.Adj u v ∧ q) ∧ p` for the same conjuncts; `simp` does not
  re-associate, so a closing `try tauto` is needed. The matching
  `typeI` proof closes with bare `simp` because the `Adj` predicate
  there has no extra clause. Logged in FRICTION.md.

- **Post-landing refactor: extract `Set.ncard_pair_le` / `_triple_le`
  and `Sym2.map_some_injective` to mirrors.** Five literal-pair /
  triple ncard bounds in this file expanded to 3- and 5-line calc
  chains via `Set.ncard_insert_le` + `Set.ncard_singleton`; the
  `Sym2.map some` injectivity argument was written out as
  `Sym2.map.injective (Option.some_injective V)` four times. Both
  patterns now read as one-token applications of named mirror
  lemmas. See FRICTION.md (resolved entries).

- **Iso transport at `IsSparse`/`IsTight` level, not `IsLaman`.** The
  natural place for the iso-preservation lemma is one level *below*
  `IsLaman`: the parameters `(k, ℓ)` are inert under transport, and the
  edge-count argument is identical. So `IsSparse.iso` and `IsTight.iso`
  live in `Sparsity.lean`, and `IsLaman.iso = IsTight.iso` lands in
  `Laman.lean` as a one-liner. The supporting `edgesIn`-image equality
  (`Iso.image_edgesIn`) sits alongside `IsSparse.iso`, since `Sparsity.lean`
  already imports `SimpleGraph.Maps` (transitively via `DeleteEdges`).

- **`DecidableRel` for `typeI.Adj` / `typeII.Adj` enables `decide` for
  the iso construction.** Lean does not auto-derive `DecidableRel` from
  the `match`-based `Adj` on `Option V`. Adding two two-line instance
  declarations in `Henneberg.lean` (each routes the four pattern arms
  through `inferInstance` / `instDecidableFalse`) lets `decide` close
  every branch of the K₄ \ e iso's `map_rel_iff'`, including the
  4 nested `(some (some _), some (some _))` arms that previously needed
  `simp` on `typeI_adj_some_some`. The instances are project-specific
  (typeI/typeII don't exist upstream), so they live in `Henneberg.lean`
  next to the definitions.

- **Don't hand-pass `Set.Finite` witnesses.** The `_fin` preambles
  in front of every `Set.ncard_*` call were unnecessary: the
  relevant lemmas (`ncard_union_eq`, `ncard_le_ncard`,
  `ncard_eq_zero`, `ncard_pos`, …) all take `(hs : s.Finite := by
  toFinite_tac)`, which finds the witness via `Set.toFinite` from
  the ambient `[Finite V]`. The two `edgeSet_ncard` lemmas dropped
  ~9 and ~10 lines of preamble respectively, and the inline
  `_isLaman` proofs lost three more `_fin` haves each. The one
  trap: when chaining `.mpr` on an iff lemma (`Set.ncard_pos.mpr`),
  the autoparam can't fire — pass the witness manually there or use
  `ncard_ne_zero_of_mem` (which is single-argument). Lifted from
  FRICTION.md into TACTICS.md § 2 as a project-wide rule.

- **Grind closes the tightness branches; arithmetic-heavy `omega`s
  stay.** Per TACTICS.md § 1, ran `grind?` on each closing tactic.
  Both `_isLaman` tightness branches collapsed: `typeI_isLaman` from
  4 lines to 1 (`grind only [!typeI_edgeSet_ncard,
  !Finite.card_option, h.edgeSet_ncard]`), `typeII_isLaman` from 7
  to 3 (grind even pulls in `Set.ncard_ne_zero_of_mem` from a local
  edge-membership hypothesis on its own). The pure-arithmetic
  `omega`s in the sparsity branches stayed: each closes a chain of
  staged `have`s with no equational reasoning to do, the canonical
  `omega` use case. Disjointness proofs also stayed — `grind` cannot
  case-split on Sym2 patterns. Worked examples and the don't-bother
  list are now in TACTICS.md § 1.

- **Post-Phase-3 cleanup pass.** Extracted four project-internal
  private helpers in `Henneberg.lean` to remove duplication that had
  accumulated across the two `_isLaman` proofs and the rotation
  block of `IsLaman.exists_typeI_or_typeII_iso`:
  - `fresh_sym2_subset_singleton` and
    `fresh_sym2_ncard_eq_zero_of_none_notMem` capture the `T ⊆
    {s(none, some w)}` (`s'.card = 1` sub-case) and `T.ncard = 0`
    (`none ∉ s` case) cardinality steps shared by `typeI_isLaman`
    and `typeII_isLaman`. Each call site dropped from 6–8 lines of
    explicit Sym2 case-analysis to a 2-line invocation.
  - `typeI_branch_of_two_neighbors` and `typeII_branch_of_nonadj`
    package the existential-witness construction of
    `exists_typeI_or_typeII_iso`. The three rotation branches in
    the degree-3 case collapsed from ~30 lines (each branch
    repeating 4 `intro heq; exact …` Subtype-equality contradictions
    and a `Or.inr ⟨rfl, _⟩` adjacency witness) to one
    `(typeII_branch_of_nonadj …).imp fun _ => Or.inr` line per
    branch, with the relabelling encoded in the argument order.
  - Tightened the `(some, some)` arm of
    `typeII_iso_of_three_neighbors`: replaced the `rw
    [Subtype.mk.injEq] at h1 h2; subst h1; subst h2` chain with a
    one-line subtype-equality lift `congrArg (Sym2.map
    Subtype.val) heq` followed by `rcases Sym2.eq_iff.mp _`. Saves
    ~5 lines and makes the underlying argument (the equality is at
    the V-level) directly visible.
  - Fused the double `rcases he with rfl | rfl | rfl | rfl | rfl |
    rfl <;> …` in `IsLaman.exists_nonadj_among_three_neighbors`
    `hE_sub` into one rcases that closes both projections in
    parallel. Same proof, two lines shorter.

- **Second cleanup pass: lean harder on `grind`.** Net 15 lines saved
  across the four files via the TACTICS.md "replace `omega` with
  `grind only [...hints...]`" workflow plus a few targeted refactors:
  - `IsLaman.two_le_degree` (`Laman.lean`) — the closing
    `rw`-chain-then-`omega` block (5 staged hypotheses) collapsed to
    one `grind only [Finset.coe_compl_singleton,
    Finset.card_compl_singleton, ncard_incidenceSet_eq_degree,
    Nat.card_eq_fintype_card]`. The simp/coercion lemmas are needed
    as hints because `grind` does not pick up `@[simp]` annotations
    on its own (TACTICS.md § 1).
  - `IsLaman.exists_degree_le_three` (`Laman.lean`) — the three-line
    `calc 4 * Fintype.card V = ∑ _ : V, 4 ≤ ∑ v, G.degree v` chain
    collapsed to a single `Finset.sum_le_sum` line plus `simp at h4n`,
    and the closing `omega` became `grind only [Nat.card_eq_fintype_card]`
    sweeping the staged handshake/edge-count facts.
  - `IsTight.iso` (`Sparsity.lean`) — closing `rw [hE, hV]; exact h.2`
    became `grind only [h.2]`, with hE/hV in context as `have`s.
  - `edgesIn_compl_singleton` (`EdgesIn.lean`) — `simp only [...];
    tauto` became `grind [mem_edgesIn_compl_singleton, incidenceSet]`.
  - `IsLaman.exists_nonadj_among_three_neighbors` (`Laman.lean`) —
    `rw [hs_card] at hsparse` is unnecessary since `omega` reads
    `hs_card` from context; the inner `rw [hE_def]` and
    `rintro/simp only` were also fused.
  - `top_fin_two_isLaman` (`Laman.lean`) — `hsle` is unnecessary if
    we feed `s.card_le_univ` as a `have` directly into the
    `eq_univ_of_card` precondition's `grind only`.
  - `typeII_isLaman` `h_or` block (`Henneberg.lean`) — six lines
    (`refine ... ⟨hG_ab, _⟩`, `rw [Sym2.coe_mk]`, `rintro _ (rfl |
    rfl)`, `exacts [...]`) collapsed to a single
    `mem_edgesIn.mpr ⟨hG_ab, by simp [...]⟩` via simp on
    `Set.insert_subset_iff` over the Sym2 coercion.
  - `typeII_isLaman` `hT'_le_2` block (`Henneberg.lean`) — the
    biggest single win. Extracted a third "fresh-edges" helper,
    `fresh_sym2_triple_inter_ncard_le_two`, alongside the existing
    `fresh_sym2_subset_singleton` and
    `fresh_sym2_ncard_eq_zero_of_none_notMem`. The two duplicated
    11-line branches (`a ∉ s'` and `b ∉ s'`) collapsed to two-line
    helper invocations, with the second arm reordering T' via
    `Set.insert_comm` so the helper applies with `x = b` instead of
    `x = a`. `Set` is unordered so the rewrite is identity-as-Set;
    only the literal expression form changes.
  - `typeII_iso_of_three_neighbors` `(some, some)` arm — the closing
    `exacts [hnab hadj, hnab hadj.symm]` became `<;> grind
    [G.adj_symm]` since both arms only need `hnab : ¬G.Adj a b`,
    `hadj`, and adjacency-symmetry.

  Things `grind` did **not** close (and where I reverted): full
  `Iso.image_edgesIn` (existentials over `φ p = u, φ q = v` need a
  named witness; grind picks the wrong one). Disjointness proofs on
  Sym2 patterns also stay manual per TACTICS.md.

- **Switch `_isLaman` sparsity scaffolds from `s.preimage some _` to
  `s.eraseNone`.** Both `typeI_isLaman` and `typeII_isLaman` originally
  introduced `s' := s.preimage some (Option.some_injective V).injOn` and
  then rebuilt `s = insert none (s'.image some)` (or `s = s'.image some`)
  in 4–5 lines per branch via `ext; cases x; …; rw [card_insert_of_notMem,
  card_image_of_injective]`. Mathlib's `Finset.eraseNone` provides the
  same some-preimage with all the needed API as `@[simp]`-lemmas
  (`mem_eraseNone`, `coe_eraseNone`, `card_eraseNone_of_not_mem`); the
  only missing piece was an addition-form companion to
  `card_eraseNone_of_mem` (mathlib's version uses `ℕ`-subtraction,
  which the project bans). Mirrored that one lemma as
  `Finset.card_eraseNone_add_one_of_mem` and switched both proofs.
  Each `none ∈ s` / `none ∉ s` branch's `hsc` derivation collapsed to
  one line. Net ~27 lines across the two proofs. Logged in FRICTION.md.

- **`and_assoc` / `and_left_comm` cannot replace `try tauto` in the
  typeII `h_decomp`.** Tried `simp [edgesIn, hcoe, Set.mem_preimage,
  T', and_assoc, and_left_comm]` to canonicalize the `(A ∧ p) ∧ q ↔
  (A ∧ q) ∧ p` mismatch flagged in FRICTION. The associativity rewrites
  re-order the conjuncts past the `Sym2.map ... = s(some u, some v)`
  pattern, breaking `Sym2.exists_and_map_eq_mk_iff`'s simp form, so
  the `(some, some)` case fails to close even after a trailing `try
  tauto`. Reverted; FRICTION entry updated with the negative result.

- **Mirror Sym2 disjointness lemma; collapse 4 disjointness blocks.**
  Each of `typeI_edgeSet_ncard`, `typeII_edgeSet_ncard`,
  `typeI_isLaman` (`h_disj`), `typeII_isLaman` (`h_disj`) carried a
  3–4 line `rw [Set.disjoint_left]; rintro e he hpair; rcases hpair
  …; simp at he` proving disjointness between `Sym2.map some '' S`
  and a literal Option-fresh-edge set. Mirrored two upstream-eligible
  lemmas in `Sym2.lean`: `notMem_map_some` (`none ∉ Sym2.map some e`,
  `@[simp]`) and `disjoint_image_map_some` (`(∀ e ∈ T, none ∈ e) →
  Disjoint (Sym2.map some '' S) T`). Each call site collapses to a
  one-line term-mode application of the helper. Net ~7 lines saved.

- **Drop `hcoe` `have` from both `_isLaman` proofs.** `set s' :=
  s.eraseNone with hs'_def` introduces `s'` as an opaque
  abbreviation, so `simp` inside `h_decomp` can't fire
  `Finset.coe_eraseNone` (which is `@[simp]` upstream) on its own —
  the `hcoe` `have` was working around that. Passing `hs'_def`
  directly to the simp set instead (`simp [hs'_def, edgesIn, T]`)
  unfolds `s' → s.eraseNone` first, after which `coe_eraseNone` and
  `Set.mem_preimage` fire automatically. ~4 lines saved across the
  two proofs.

- **Shrink 6-edge / 4-set cardinality computations via `grind`.** The
  `hs_card` (`{v,a,b,c}.card = 4`) and `hE_card` (literal 6-edge
  Finset.card = 6) preambles in
  `IsLaman.exists_nonadj_among_three_neighbors` were 4- and 8-line
  `Finset.card_insert_of_notMem` chains with explicit `notMem`
  side-condition proofs. Both close in one `grind only [...]` line
  with hints `[Finset.card_insert_of_notMem, Finset.card_singleton]`
  (plus `Sym2.eq_iff` for the Sym2 case). `Finset.mem_insert` and
  `Finset.mem_singleton` are already `@[grind =]` upstream, so don't
  pass them. Net ~9 lines saved in `Laman.lean`. Both lifted into
  the FRICTION resolved log.

- **Extract `isoOfOptionSubtypeNe` from the two iso constructors.**
  `typeI_iso_of_two_neighbors` and `typeII_iso_of_three_neighbors`
  both built `G ≃g (move-graph)` along the equivalence
  `(Equiv.optionSubtypeNe v).symm`, with identical 4-case `by_cases`
  scaffolding (`(v, v)`, `(v, w)`, `(u, v)`, `(u, w)`) and identical
  rewrites in cases 1–3 modulo the `Adj` lemma name (`typeI_adj_*`
  vs `typeII_adj_*`). Factored the scaffolding into a private
  helper `isoOfOptionSubtypeNe` taking just three adjacency-condition
  hypotheses: `¬ H.Adj none none` (closes case 1), `H.Adj none (some
  ⟨w, hw⟩) ↔ G.Adj v w` (case 2; case 3 follows by symmetry of both
  Adj relations), and `H.Adj (some ⟨u, hu⟩) (some ⟨w, hw⟩) ↔
  G.Adj u w` (case 4; carries any move-specific bridging logic).

  After extraction:
  - `typeI_iso_of_two_neighbors` is a 6-line term-mode definition
    whose three closing arguments are `(by simp)`, `(fun w _ => by
    simp [hN])`, and `(fun _ _ => Iff.rfl)`.
  - `typeII_iso_of_three_neighbors` keeps the bridging-edge logic
    in its `(some, some)` argument; cases 1 and 2 collapse to
    `(by simp)` and `(fun w _ => by simp [hN])` matching typeI.
  - Net 14 more lines saved, plus a clearer division between
    the iso-construction scaffolding and the move-specific
    adjacency facts. Also removes the slightly subtle `← G.adj_comm`
    rewrite in case 3 (now handled once in the helper, by `rw
    [H.adj_comm, G.adj_comm]; exact hns u hu`).

  The helper's `hnone` parameter is technically unused inside the
  `simp` call — `simp` picks it up from local context as a `P ↔
  False` rewrite. Keeping it as an explicit parameter documents
  the obligation; the inline comment notes this.

## Blockers / open questions

- **typeII reverse Laman preservation needs the Henneberg blocker
  argument.** See `FRICTION.md` entry. Not blocking Phase 3 closure
  (we shipped the iso half); becomes a Phase 5 prerequisite if the
  Laman's-theorem proof needs it explicitly.

## Hand-off / next phase

Phase 3 is **complete**: `IsLaman.exists_typeI_or_typeII_iso` plus
the per-move Laman-preservation theorems
(`typeI_isLaman`, `typeII_isLaman`) and the `K₄ \ e` worked example
land the canonical Henneberg apparatus. The strengthened
`IsLaman.exists_typeI_or_typeII_reverse` (with `G'.IsLaman`) is
deferred and properly belongs in Phase 5 — see ROADMAP §5.

For the next agent: open `notes/Phase4.md` (create it) and start the
`Framework.lean` work. Phase 4 is independent of Phase 3 — it builds
the rigidity-matrix infrastructure needed for the analytical half of
Laman's theorem. ROADMAP §4 lists the lemmas to develop.
