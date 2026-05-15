# Phase 3 — Henneberg moves (work log)

**Status:** complete.

This file is the per-phase work record. See `../ROADMAP.md` for the
high-level plan and `../DESIGN.md` for cross-cutting design choices.
Phase notes are *historical*: don't rewrite them when a phase ends —
they're the reference for "how Phase N actually went."

## Current state

Both Henneberg moves preserve the Laman property
(`typeI_isLaman`, `typeII_isLaman`), the `K₄ \ e` worked example
(`top_fin_four_minus_edge_isLaman`) lands via iso transport, and the
**iso half of the structural decomposition** is done:
`IsLaman.exists_typeI_or_typeII_iso` says every Laman graph on `n ≥ 3`
vertices is iso to a Type I or Type II move applied to *some* graph
`G'`. **It does not claim `G'.IsLaman`** — the deeper
"Laman-preservation under reverse Henneberg moves" direction turned
out to be substantially harder than the Phase-start hand-off
suggested, so it is deferred to Phase 5 (see *Carryover from Phase 3*
in ROADMAP §5, and FRICTION.md "Open" *typeII reverse Henneberg
move*).

Supporting helpers added this phase:
* `IsLaman.exists_nonadj_among_three_neighbors` (in `Laman.lean`) —
  given a degree-3 neighborhood `{a, b, c}` of `v` in a Laman graph,
  some pair is non-adjacent (sparsity at `{v, a, b, c}` minus the
  three `v`-edges bounds edges among `{a, b, c}` by 2).
* `Henneberg.typeI_iso_of_two_neighbors`,
  `Henneberg.typeII_iso_of_three_neighbors` (private, in
  `Henneberg.lean`) — the iso constructions, parameterised on
  `hN : ∀ w, G.Adj v w ↔ w = a ∨ w = b (∨ w = c)`. Underlying equiv
  is `(Equiv.optionSubtypeNe v).symm`. Both factor through the
  shared `isoOfOptionSubtypeNe` helper.

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
  rather than `G.map .some ⊔ fromEdgeSet …`. Adjacency lemmas become
  `Iff.rfl`; cost is one manual `Sym2.ind`-based proof for the
  edgeSet decomposition. The lattice attempt was abandoned because
  `(G.map f).Adj` unfolding to `∃ u' v', …` fought every adjacency
  proof. See DESIGN.md "Choices to revisit" (resolved).

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
  FRICTION.md "Open" *typeII reverse Henneberg move* and ROADMAP §5.

## Decisions made during this phase

(Phase-local trade-offs. Cross-cutting lessons surfaced during the
phase are listed under *Promoted to cross-cutting docs* below; their
explanations live in TACTICS-GOLF / TACTICS-QUIRKS, FRICTION, or DESIGN.)

### Phase-local choices and proof techniques

- **Split the decomposition theorem into iso-only + Laman-claim.**
  The Phase-3-start hand-off planned a single
  `IsLaman.exists_typeI_or_typeII_reverse` combining (a) the iso
  `G ≃g typeI/II G'` and (b) `G'.IsLaman`. Working through the proof
  revealed (b) is much harder for typeII than the hand-off implied:
  an arbitrary non-adjacent neighbor pair can fail to give a Laman
  `G'`. Phase 3 ships only (a) as `exists_typeI_or_typeII_iso`; the
  Laman-preservation half is a Phase-5 prerequisite. See
  FRICTION.md "Open" *typeII reverse Henneberg move* for the
  6-vertex counter-example, and ROADMAP §5 *Carryover from Phase 3*.

- **Iso construction parameterised on
  `hN : ∀ w, G.Adj v w ↔ w = a ∨ w = b (∨ w = c)`,
  not on `G.neighborFinset v = {a, b}`.** Both convey "the neighbors
  are `a` and `b`," but the iff form is what `typeI_adj_none_some` /
  `typeII_adj_none_some` reduce to after `rw`, so the iso closes by
  `rw [..., hN]; simp` rather than needing extra `mem_neighborFinset`
  glue. The caller produces `hN` in one line from
  `Finset.card_eq_two.mp`.

- **Iso closes by `rw [Equiv.optionSubtypeNe_symm_*, *_adj_*]; simp`
  per case.** The `(Equiv.optionSubtypeNe v).symm` only has
  explicit-rewrite lemmas (`_symm_self`, `_symm_of_ne`), not simp
  ones, so we lead each case with the appropriate explicit `rw`.
  After the rewrite the goal has only Subtype-equality / disjunction
  shape left, and bare `simp` (or `simp [Subtype.mk.injEq]`) closes
  it. The `(some, some)` arm of typeII needs an extra `constructor`
  + `rcases` since `simp` does not eliminate the `s(...) ≠ s(...)`
  conjunct via the `¬ G.Adj a b` hypothesis on its own.

- **Extract `isoOfOptionSubtypeNe` from the two iso constructors.**
  `typeI_iso_of_two_neighbors` and `typeII_iso_of_three_neighbors`
  both built `G ≃g (move-graph)` along
  `(Equiv.optionSubtypeNe v).symm`, with identical 4-case `by_cases`
  scaffolding modulo the `Adj` lemma name. Factored the scaffolding
  into a private helper taking three adjacency-condition hypotheses:
  `¬ H.Adj none none` (case 1), `H.Adj none (some ⟨w, hw⟩) ↔ G.Adj v w`
  (cases 2 / 3 by symmetry), and
  `H.Adj (some ⟨u, hu⟩) (some ⟨w, hw⟩) ↔ G.Adj u w` (case 4 with
  any move-specific bridging logic). After extraction
  `typeI_iso_of_two_neighbors` is a 6-line term-mode definition;
  `typeII_iso_of_three_neighbors` keeps the bridging-edge logic in
  its `(some, some)` argument. Net 14 lines saved.

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN

The lessons below surfaced during the phase but proved cross-cutting;
their explanations now live elsewhere. The line is the locus + a
pointer.

- *Sym2 image-membership simp form* → FRICTION [mirrored]
  `Sym2.exists_and_map_eq_mk_iff`.
- *Per-move `_edgesIn_ncard_decomp` extraction* → FRICTION [resolved].
- *`s'.card = 1` sub-case duplication* → FRICTION [resolved]
  *Recurring duplication across the two `_isLaman` proofs*.
- *typeII `edgesIn` decomposition needs `try tauto`* → FRICTION
  [wontfix] *`simp` leaves and-grouping*.
- *Mirror Sym2 disjointness lemma* → FRICTION [mirrored]
  `Sym2.notMem_map_some`, `Sym2.disjoint_image_map_some`.
- *Unconditional pair / triple ncard bounds* → FRICTION [mirrored]
  `Set.ncard_pair_le` / `_triple_le`.
- *`Sym2.map some` injectivity helper* → FRICTION [mirrored]
  `Sym2.map_some_injective`.
- *Iso transport at `IsSparse` / `IsTight` level, not `IsLaman`* →
  FRICTION [resolved] *`IsLaman.iso` factored through
  `IsSparse.iso` / `IsTight.iso`*.
- *`DecidableRel` for `typeI.Adj` / `typeII.Adj`* → FRICTION
  [resolved].
- *Switch to `s.eraseNone` for the some-preimage* → FRICTION
  [mirrored] `Finset.card_eraseNone_add_one_of_mem`.
- *Drop `hcoe` `have` line; pass `hs'_def` to simp* → FRICTION
  [resolved].
- *6-edge / 4-set cardinality computations close via `grind`* →
  FRICTION [resolved].
- *Repeated existential-witness packaging in
  `exists_typeI_or_typeII_iso`* → FRICTION [resolved].
- *Don't hand-pass `Set.Finite` witnesses; use the autoparam* →
  TACTICS-GOLF § 2.
- *`grind only` closes tightness branches; pure-arithmetic `omega`s
  stay* → TACTICS-GOLF § 1.
- *Lifting Subtype-Sym2 equalities via
  `congrArg (Sym2.map Subtype.val)`* → TACTICS-GOLF § 5 (and FRICTION
  [resolved] *Lifting subtype-Sym2 equality to underlying-value
  equality*).

### Cleanup pass summaries

Two cleanup passes ran at Phase-3 close. Cross-cutting items they
surfaced are recorded under *Promoted* above; what follows is the
per-file effect.

- **Pass 1 (project-internal helpers).** Extracted four private
  helpers in `Henneberg.lean` to remove cross-proof duplication:
  `fresh_sym2_subset_singleton` and
  `fresh_sym2_ncard_eq_zero_of_none_notMem` (the
  `T ⊆ {s(none, some w)}` and `T.ncard = 0` cardinality steps shared
  by `typeI_isLaman` and `typeII_isLaman`); `typeI_branch_of_two_neighbors`
  and `typeII_branch_of_nonadj` (the existential-witness construction
  in `IsLaman.exists_typeI_or_typeII_iso`). Plus tightening of the
  `(some, some)` arm of `typeII_iso_of_three_neighbors` via
  `congrArg (Sym2.map Subtype.val)` (TACTICS-GOLF § 5).
- **Pass 2 (`grind` workflow).** ~15 lines saved across four files
  by replacing closing `omega` / `simp` / `tauto` with `grind only`
  and the right hints. Worked targets: `IsLaman.two_le_degree`,
  `IsLaman.exists_degree_le_three`, `IsTight.iso`,
  `edgesIn_compl_singleton`, `IsLaman.exists_nonadj_among_three_neighbors`,
  `top_fin_two_isLaman`, the `typeII_isLaman` `h_or` and `hT'_le_2`
  blocks, and the `(some, some)` arm of
  `typeII_iso_of_three_neighbors`. Things `grind` did *not* close
  (and where the proof reverted): full `Iso.image_edgesIn`
  (existentials need a named witness; grind picks the wrong one),
  Sym2-pattern disjointness (TACTICS-GOLF § 1).

## Blockers / open questions

- **typeII reverse Laman preservation needs the Henneberg blocker
  argument.** See FRICTION.md "Open" *typeII reverse Henneberg
  move*. Not blocking Phase 3 closure (we shipped the iso half);
  becomes a Phase 5 prerequisite if the Laman's-theorem proof needs
  it explicitly.

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
