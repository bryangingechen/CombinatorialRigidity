# Phase 5 — Laman's theorem, (⇐) direction (work log)

**Status:** in progress.

This file is the per-phase work record. See `../ROADMAP.md` for the
high-level plan and `../DESIGN.md` for cross-cutting design choices.

## Current state

Milestone 0, the **typeI half** of milestone 1, the tight-set lattice
infrastructure for the typeII half, *and the per-pair tight-blocker
witness* are complete. Specifically:

* Milestone 0 (LamanTheorem stub + d=2 corollary + iso transport) —
  done in an earlier commit.
* Milestone 1 partial — `typeI_reverse_isLaman` and the companion
  `typeI_isLaman_iff` (in `Henneberg.lean`), giving the degree-2
  branch of the structural decomposition automatically.
* Milestone 1 typeII edge-arithmetic input — `edgesIn_inter` plus
  `edgesIn_ncard_add_le` in `EdgesIn.lean` (supermodularity of edge
  counts); plus `IsTightOn` + `IsTightOn.union_inter` in `Sparsity.lean`
  (the standard tight-subset lattice closure on which the blocker
  argument runs).
* Milestone 1 typeII per-pair blocker — `IsLaman.typeII_reverse_blocker`
  in `Henneberg.lean`: given a degree-3 vertex `v` with neighbors
  `{x, y, c}` and a non-adjacent pair `(x, y)`, if the typeII-reverse
  candidate `(G - v) + edge(x, y)` is *not* Laman, then there exists a
  `(2, 3)`-tight `S ⊆ V \ {v}` with `{x, y} ⊆ S` in `G`. Edge count is
  established via the typeII iso transfer (Phase 3:
  `typeII_iso_of_three_neighbors`); sparsity violation extracts a
  Finset `s'` whose lift to `V` is the witness, tightness via the new
  `IsSparse.isTightOn_of_le` (`Sparsity.lean`).

The remaining typeII-half open task is the case-split that combines
per-pair witnesses (3 / 2 / 1 non-adjacent pairs among `v`'s neighbors)
via `IsTightOn.union_inter` to derive a contradiction with `G`'s
sparsity, completing `IsLaman.exists_typeI_or_typeII_reverse`.
Milestone 2 (per-move rigidity preservation, in `Henneberg.lean`) is
independent and can be worked in parallel.

Phase 5 target: the (⇐) direction of Laman's theorem,

```
theorem IsLaman.isGenericallyRigid_two {V : Type*} [Fintype V]
    {G : SimpleGraph V} (h : G.IsLaman) : G.IsGenericallyRigid 2
```

plus the bridge to the iff statement
`isGenericallyRigid_two_iff_exists_isLaman_le` via
`IsGenericallyRigid.mono`. The (⇒) direction (Lovász–Yemini matroid
duality) is **deferred to Phase 6** — it requires a rigidity-matroid
API that Phase 4 deliberately did not stand up. The iff statement
lands in `LamanTheorem.lean` from the first commit, *composed* from
two named directional theorems (one of which is `sorry`-blocked for
Phase 5 milestone 3, the other for Phase 6).

The proof of (⇐) is a Henneberg induction on `Fintype.card V`:

* **Base.** `K₂` is generically rigid in dim 2
  (Phase 4: `top_fin_two_isGenericallyRigid 2`).
* **Step.** Given Laman `G` on `n ≥ 3` vertices, the strengthened
  decomposition `IsLaman.exists_typeI_or_typeII_reverse` gives Laman
  `G'` on `n − 1` vertices plus a Henneberg-iso `G ≃g typeI/II G' …`.
  Induction on `G'`; the per-move rigidity-preservation lemmas
  (`typeI_isGenericallyRigid_two`, `typeII_isGenericallyRigid_two`)
  plus iso transport lift the conclusion back to `G`.

So (⇐) breaks into three milestones, each likely a small commit
cluster:

1. **Reverse decomposition** — `IsLaman.exists_typeI_or_typeII_reverse`
   (in `Henneberg.lean`) via the Henneberg blocker argument.
2. **Move preservation** — `typeI_isGenericallyRigid_two` and
   `typeII_isGenericallyRigid_two` in `Henneberg.lean`.
3. **Induction** — fill in `IsLaman.isGenericallyRigid_two` (the
   milestone-0 sorry); the iff's (⇐) arm completes automatically
   thanks to the structured composition.

Milestones 1 and 2 are independent and can be worked in either order.

## Architectural choices made up front

These extend `../DESIGN.md` *Choices to revisit*; if any turns out
wrong, revisit there.

- **(⇐) only; (⇒) is Phase 6.** ROADMAP §5 commits to the iff
  statement — that lands in `LamanTheorem.lean` from the first commit
  with the (⇒) arm as `sorry`. (⇒) needs the Lovász–Yemini equality
  "rigidity matroid = (2,3)-count matroid in dim 2," which is its own
  multi-session sub-project on top of a `RigidityMatroid.lean`. Phase 4
  *Architectural choices* explicitly kept the rigidity matroid out of
  scope; reversing that within Phase 5 would balloon the phase. Phase 6
  picks it up if and when warranted.

- **Henneberg-blocker route, not matroid bypass.** The reverse lemma
  is proved combinatorially via the classical Whiteley/Jordán argument:
  if every non-adjacent neighbor pair of a degree-3 vertex `v` blocks
  the Type II reverse, a `(2, 3)`-tight set in `G` is forced to violate
  sparsity. Pure graph theory; matches the project's existing
  `IsSparse` / `IsTight` / `edgesIn` style. Path 2 (matroid bypass)
  was rejected for the same reason as the (⇒) deferral above.
  ROADMAP §5 *Carryover from Phase 3* and DESIGN.md *Why Henneberg*.

- **Specialize to `d = 2` at the Phase 5 boundary.** Per
  Phase 4 *Architectural choices*, every Phase 4 result is general
  in `d`. Phase 5 is responsible for the `d = 2` specializations:
  `IsGenericallyRigid.card_mul_le_two` (`2 * #V ≤ #E + 3`, one-line
  corollary of `IsGenericallyRigid.card_mul_le`) and the per-move
  rigidity-preservation lemmas. The move-rigidity proofs are
  intrinsically d=2 — the "place new vertex off the line through
  neighbors" / rotation-trick arguments are dimension-2 facts.
  General-`d` Henneberg is mathematically harder and not on the
  critical path.

- **Reverse lemma signature.** Same shape as
  `exists_typeI_or_typeII_iso` plus a `G'.IsLaman` conjunct on the
  decomposed graph (full statement under *Milestone 1* below). The
  iso version is *not* superseded — it stays as the natural building
  block; the strengthened version composes the Laman-claim on top.

- **Move-preservation lemmas live in `Henneberg.lean`.** The
  `typeI_isLaman` / `typeII_isLaman` lemmas already live there; the
  `_isGenericallyRigid_two` companions land alongside, exposing the
  per-move parallel structure. Cost: `Henneberg.lean` will need to
  import `Framework.lean` (today it doesn't); `Framework.lean` is a
  leaf in the import DAG so this is a forward edge, not a cycle. An
  alternative was a separate `HennebergRigidity.lean`; rejected
  because the lemma counts are small.

## Lemma checklist

Listed by milestone. Items live in `LamanTheorem.lean` unless tagged
otherwise. Helpers and signatures will refine as proofs open up;
treat the names below as working names.

### Milestone 0 — First commit (smallest concrete unit) — done

- [x] `LamanTheorem.lean` created. Three named theorems per the
  structured-`sorry` layout: `IsLaman.isGenericallyRigid_two`
  (sorry, milestone 3), `IsGenericallyRigid.exists_isLaman_le`
  (sorry, Phase 6), and the composed iff
  `isGenericallyRigid_two_iff_exists_isLaman_le` (no sorry; `mp`
  is `.exists_isLaman_le`, `mpr` rcases's the Laman subgraph and
  routes through `.isGenericallyRigid_two.mono`).
- [x] `IsGenericallyRigid.card_mul_le_two` — one-liner via
  `hG.card_mul_le` (the `d = 2` specialization is defeq;
  `2 * (2+1) / 2 = 3`).
- [x] `IsGenericallyRigid.iso` — iso transport for generic rigidity
  in `Framework.lean`, plus the underlying
  `IsInfinitesimallyRigid.iso`. Built via a direct `LinearEquiv`
  between the two rigidity-map kernels (precomposition with `φ`)
  and `LinearEquiv.finrank_eq`. ~30 lines for the
  `IsInfinitesimallyRigid` half plus a 3-line `obtain`-`exact` for
  the `IsGenericallyRigid` lift.

### Milestone 1 — Reverse decomposition (`Henneberg.lean`)

The Henneberg blocker / "good vertex" argument; cf. Whiteley §3 /
Jordán §3.1. Target signature:

```
theorem IsLaman.exists_typeI_or_typeII_reverse [Fintype V]
    {G : SimpleGraph V} (h : G.IsLaman) (hV : 3 ≤ Fintype.card V) :
    ∃ (v : V) (G' : SimpleGraph {w : V // w ≠ v}), G'.IsLaman ∧
      ((∃ a b, a ≠ b ∧ Nonempty (G ≃g typeI G' a b)) ∨
       (∃ a b c, a ≠ b ∧ c ≠ a ∧ c ≠ b ∧ G'.Adj a b ∧
        Nonempty (G ≃g typeII G' a b c)))
```

- [x] `typeI_reverse_isLaman` and `typeI_isLaman_iff` — the typeI half.
  Dual of `typeI_isLaman`: lift `s' : Finset V` to `s := s'.image some`,
  apply `(typeI G a b).IsLaman.isSparse` at `s`, collapse via
  `typeI_edgesIn_ncard_decomp` (none ∉ s makes the fresh-edge term
  zero; `Finset.eraseNone_image_some` finishes the bridge). Tightness
  is a one-line `grind only` mirroring the typeI direction.

The typeII half (below) is the deep step.

- [x] (Helper) **Modular `edgesIn` inequality** — `edgesIn_ncard_add_le`
  in `EdgesIn.lean`: for any `(S T : Set V)` under `[Finite V]`,
  `(G.edgesIn S).ncard + (G.edgesIn T).ncard ≤
  (G.edgesIn (S ∪ T)).ncard + (G.edgesIn (S ∩ T)).ncard`. Done via
  the named `edgesIn_inter` (the `∩` equality) plus
  `Set.ncard_union_add_ncard_inter` with the `∪ ⊆` containment.
  `[Finite V]` lets the `ncard_*` autoparams fire (per TACTICS § 2).

- [x] (Helper) **`(k, ℓ)`-tight-subset union closure** —
  `IsTightOn.union_inter` in `Sparsity.lean`. Introduced the named
  predicate `IsTightOn G k ℓ s := (G.edgesIn ↑s).ncard + ℓ = k * s.card`
  (mirrors `IsTight` but localized to a Finset). The lemma generalizes
  the size proviso to `ℓ ≤ k * (s ∩ t).card` (specializes to
  `2 ≤ |s ∩ t|` at `(k, ℓ) = (2, 3)`). Proof: supermodularity (lower
  bound on `e(s ∪ t) + e(s ∩ t)`) + two sparsity applications (upper
  bound) + Finset cardinality identity, fused by `omega` once the
  `k * #` form is staged via a 3-rewrite glue step (see FRICTION
  extension under *omega doesn't see through nonlinear algebra on
  opaque atoms*).

- [x] (Helper) **Squeeze: sparsity bound from below ⇒ tight** —
  `IsSparse.isTightOn_of_le` in `Sparsity.lean`: in a `(k, ℓ)`-sparse
  graph, `k * #s ≤ (G.edgesIn ↑s).ncard + ℓ` (the lower bound matching
  the sparsity upper bound) forces `G.IsTightOn k ℓ s`. One-line proof
  via `unfold IsTightOn` + omega. Used by the typeII blocker to convert
  a sparsity violation on the candidate graph into a tight set in `G`.

- [x] **Per-pair tight-blocker witness** —
  `IsLaman.typeII_reverse_blocker` in `Henneberg.lean`. Inputs: a Laman
  graph `G` with degree-3 vertex `v` whose three neighbors are exactly
  `{x, y, c}`, a non-adjacent pair `(x, y)`, and a *failed*
  typeII-reverse candidate (`¬G'.IsLaman` where `G' := (G - v) ⊔
  {bridge(x, y)}`). Output: a `(2, 3)`-tight `S ⊆ V \ {v}` with
  `{x, y} ⊆ S` in `G`. The proof routes the edge count of `G'` through
  the Phase 3 iso `typeII_iso_of_three_neighbors`, transferring `G`'s
  Laman to `(typeII G' xs ys cs).IsLaman` and using `typeII_edgeSet_ncard`
  to deduce the count; `¬G'.IsLaman` then collapses to `¬G'.IsSparse 2 3`,
  giving a violating `s'`. Case-split on `xs, ys ∈ s'` decides between
  tight-set extraction (both in) and contradiction with `G`'s sparsity
  (one out).

- [ ] `IsLaman.exists_typeI_or_typeII_reverse` — strengthened
  decomposition. Degree-2 branch reuses `typeI_reverse_isLaman` +
  the existing `typeI_iso_of_two_neighbors`; degree-3 branch is the
  blocker case analysis below.

**Blocker argument (degree-3, sketch).** With `{a, b, c}` the
neighbors of a degree-3 `v`, define for each non-adjacent pair
`(x, y)` the candidate `G_{xy} := (G - v) + edge(x, y)` on
`{w // w ≠ v}`. The edge count is automatic
(`|E(G_{xy})| + 3 = 2(n − 1)`); only sparsity is at stake. Goal:
*some* non-adjacent pair gives `G_{xy}.IsLaman`. By contradiction,
suppose all fail: each yields a `(2,3)`-subset-tight `S_{xy} ⊆
V \ {v}` containing `{x, y}` (a one-inequality chase against `G`'s
own sparsity).

Case-split on how many of the three pairs are non-adjacent (≥ 1 by
`exists_nonadj_among_three_neighbors`). The general move: combine
the `S_{xy}`'s via the union-closure lemma to build a subset-tight
`T ⊆ V \ {v}` containing two or three of `{a, b, c}`; then `T ∪ {v}`
overshoots `G`'s sparsity by 1 (each extra neighbor of `v` inside
`T` adds one edge but only one vertex). Sub-cases turn on which
pairwise intersections have size ≥ 2 to trigger the closure; the
one-non-adjacent-pair case may also need an expansion argument
absorbing the adjacent third neighbor. Confirm exact structure
against Jordán Thm 3.1.7 while writing.

Expect 1–2 mirror candidates from this work — likely around
`Set.ncard` set-arithmetic and `Sym2` membership in induced
subgraphs.

### Milestone 2 — Move preservation in dim 2 (`Henneberg.lean`)

The classical "Henneberg moves preserve rigidity" arguments. Both go
through a *specific* placement extension; the conclusion is then
"`IsGenericallyRigid` in dim 2" (existence of a rigid placement, not
genericity in the algebraic-geometry sense).

- [ ] `typeI_isGenericallyRigid_two` — Type I preserves generic
  rigidity. Construction: extend a rigid placement `p'` of `G'` to a
  placement `p` of `typeI G' a b` by placing the new vertex off the
  line through `p' a` and `p' b`. The two new rigidity-matrix rows
  are linearly independent; rank-nullity gives `dim ker p = dim ker p'`.
- [ ] `typeII_isGenericallyRigid_two` — Type II preserves generic
  rigidity. Trickier: deletes edge `s(a, b)`, adds three new edges.
  Plan: pick a placement extension where the new vertex's edges
  recover the deleted constraint plus one new constraint
  (rotation/limit argument). Decide the formalization mechanics
  during proof, not during planning.

These are the linear-algebra heart of (⇐). Likely surfaces 1–3 mirror
candidates around `LinearMap.ker` / `Submodule.finrank` rank-counting,
plus possibly an "affinely-independent points off a line" or "rank of
augmented matrix" lemma.

### Milestone 3 — Induction (fills milestone-0 sorry)

- [ ] Replace milestone-0's `sorry` body of
  `IsLaman.isGenericallyRigid_two` with the actual proof. Strong
  induction on `Fintype.card V`. Base: `n = 2` via `top_fin_two_isLaman`
  + `top_fin_two_isGenericallyRigid 2` and `IsLaman.iso` /
  `IsGenericallyRigid.iso`. Step: `exists_typeI_or_typeII_reverse` +
  per-move preservation + iso transport.

No additional theorem is needed for the iff arm: milestone 0's
structured form already routes (⇐) through
`IsLaman.isGenericallyRigid_two`, so once this `sorry` is filled in
the iff's `mpr` arm completes automatically.

## Decisions made during this phase

### Phase-local choices and proof techniques

- **`IsInfinitesimallyRigid.iso` proof structure: build the kernel
  iso directly, not via `Submodule.map`.** First attempt routed the
  proof through `(ker H).map Φ.toLinearMap = ker G` and
  `LinearEquiv.finrank_map_eq`. Stalled on a `SetLike` membership-
  form mismatch after `rintro` (see FRICTION). Refactored to a
  direct `LinearEquiv` between the two kernel subtypes; the
  membership obligations there are `q'.2`-typed and `LinearMap.mem_ker.mp/mpr`
  works without bridging. Cleaner, ~30 lines.

- **typeI reverse Laman lemma reuses `typeI_edgesIn_ncard_decomp`.**
  The proof of `typeI_reverse_isLaman` lifts `s' : Finset V` to
  `s := s'.image some` and applies `(typeI G a b).IsLaman.isSparse`
  at `s`. The existing private helper `typeI_edgesIn_ncard_decomp`
  (Phase 3) does the decomposition heavy lifting; `Finset.eraseNone_image_some`
  and the `none ∉ s.image some` simp fact collapse the fresh-edge
  contribution to zero. Tightness closes in one `grind only` line.
  Total ~15 lines, structurally dual to `typeI_isLaman`.

- **Modular `edgesIn` inequality requires `[Finite V]`.** The natural
  formulation needs `(edgesIn (S ∪ T)).Finite` (otherwise `ncard = 0`
  on the RHS lets `(edgesIn S).ncard + (edgesIn T).ncard` overshoot —
  concrete counter-example: disjoint `S, T` joined by infinitely many
  cross-edges). Chose `[Finite V]` over an explicit `(h : ...Finite)`
  argument so the autoparams in `Set.ncard_union_add_ncard_inter` and
  `Set.ncard_le_ncard` fire automatically (TACTICS § 2). Consumers
  (tight-set union closure, then blocker) live in `[Fintype V]`
  contexts, so `[Finite V]` is free downstream. Lifted `edgesIn_inter`
  out as a named lemma since the `∩` equality is the half that's
  genuinely useful by itself.

- **Introduced `IsTightOn` predicate up front.** The Phase 5 plan
  punted the predicate-vs-unpredicated choice to mid-proof. Chose
  predicate: even in the union-closure lemma alone it appears four
  times in the signature (`hs`, `ht`, plus both conclusions). The
  blocker will instantiate it on each candidate set `S_{x,y}`, so
  multiplicity grows quickly. Since `IsTightOn` is `def := (eqn)`
  (not an And), `refine ⟨?_, ?_⟩` doesn't split it directly; the
  proof uses `unfold IsTightOn at hs ht ⊢` to surface the equation
  for `omega`. (Extending TACTICS § 4 to mention this single-equation
  variant if the pattern recurs in the blocker.)

- **typeII reverse blocker: edge count via the Phase 3 iso, not by
  hand.** The natural alternative was to compute `G'.edgeSet.ncard`
  directly via the chain `Sym2.map Subtype.val '' (G.comap Subtype.val).edgeSet
  = G.edgesIn ({v}ᶜ)` + injectivity + the existing vertex-deletion
  partition + the bridging edge's contribution. That route requires a
  `Nat.card V = Nat.card {w // w ≠ v} + 1` lemma plus the explicit
  `Sym2.map`-image transfer for the comap side. Instead, the proof
  reuses `typeII_iso_of_three_neighbors` (Phase 3): with the third
  neighbor `c` of `v` plus the neighbor-set characterization passed
  in as hypothesis, build `h_iso : G ≃g typeII G' xs ys cs`, transfer
  `G.IsLaman` via `IsLaman.iso`, and read off `G'.edgeSet.ncard + 3 =
  2 * Nat.card {w // w ≠ v}` from `typeII_edgeSet_ncard` plus
  `Finite.card_option`. Saves ~20 lines and the project-internal
  `(G.comap Subtype.val).edgeSet.ncard` helper. Cost: the blocker
  signature carries the third neighbor `c` plus the full neighbor
  predicate `hN : ∀ w, G.Adj v w ↔ w = x ∨ w = y ∨ w = c` rather than
  the lighter `G.degree v = 3` plus `G.Adj v x`, `G.Adj v y`. The
  case-split argument already has `c` and `hN` in scope (from
  `Finset.card_eq_three`), so this is free downstream.

- **Per-pair blocker case structure: split on `xs, ys ∈ s'`.** The
  sparsity violation on `G'` produces some Finset `s'` whose lift `S =
  s'.image Subtype.val ⊆ V \ {v}` has `2 * S.card ≤ (G'.edgesIn ↑s').ncard
  + 2`. The two cases differ in the bridging-edge contribution to
  `G'.edgesIn ↑s'`. If both `xs, ys ∈ s'`, the bridge contributes ≤ 1,
  giving `2 * S.card ≤ (G.edgesIn ↑S).ncard + 3` — combined with `G`'s
  sparsity, equality, so `S` is `IsTightOn 2 3` via the new
  `IsSparse.isTightOn_of_le`. If one of `xs, ys` is outside `s'`, the
  bridge is excluded entirely (its endpoint set `{xs, ys}` is not a
  subset of `↑s'`), giving `2 * S.card ≤ (G.edgesIn ↑S).ncard + 2` — a
  direct contradiction with `G`'s sparsity. The edge-set decomposition
  for both bounds uses the private helper `image_edgesIn_comap`
  (`Sym2.map f '' ((G.comap f).edgesIn s') = G.edgesIn (f '' s')`) to
  bridge `(G.comap Subtype.val).edgesIn ↑s'` to `G.edgesIn ↑S` via
  injectivity of `Sym2.map Subtype.val`.

### Promoted to TACTICS / FRICTION / DESIGN

- *`Exists.imp` doesn't transport across changing-binder-type
  existentials* → FRICTION [resolved].
- *`rw [LinearMap.mem_ker]` fails on `SetLike`-coerced membership
  after `Submodule.mem_map` destructure* → FRICTION [resolved].
- *omega doesn't see through distributivity on `k * #` atoms* →
  FRICTION [wontfix] *omega doesn't see through nonlinear algebra on
  opaque atoms* (extended the existing commutativity entry with the
  distributivity case the `IsTightOn.union_inter` proof hit).
- *`set name := expr` creates a fresh atom for omega: hypotheses
  derived from upstream lemmas after the `set` still mention `expr`,
  not `name`, and omega treats `{name}` and `{expr}` as distinct
  atoms* → FRICTION [wontfix] *omega treats `set`-aliased terms as
  opaque atoms*.

## Blockers / open questions

- **Affine-spanning side condition for Type I preservation.** The
  textbook proof places the new vertex generically, then argues
  "kernel doesn't grow because the new rows are independent." The
  cleanest formalization may want an affinely-spanning hypothesis on
  `p'` (so `p` remains affinely spanning after extension). Phase 4
  did not ship `finrank_trivialMotions_eq_of_affinelySpanning`; if the
  Type I proof wants it, fill in then. Phase 4 hand-off explicitly
  flagged this as the deferred-API surface most likely to be needed.

- **Henneberg-blocker proof length.** Textbook proofs of the reverse
  decomposition are 1–2 pages; the formalization will be
  longer. If milestone 1 sprawls past ~3 sessions, reassess: perhaps
  an internal lemma about tight-set lattices belongs in
  `Sparsity.lean` as a named theorem rather than a private helper, or
  a refactor of `exists_nonadj_among_three_neighbors` is warranted.

## Hand-off / next phase

Milestone 0 (LamanTheorem stub + d=2 corollary + iso transport), the
typeI half of milestone 1 (`typeI_reverse_isLaman` /
`typeI_isLaman_iff`), the modular `edgesIn` inequality
(`edgesIn_inter` + `edgesIn_ncard_add_le` in `EdgesIn.lean`), the
tight-subset lattice closure (`IsTightOn` + `IsTightOn.union_inter`
in `Sparsity.lean`), the sparsity-squeeze helper
(`IsSparse.isTightOn_of_le` in `Sparsity.lean`), and the per-pair
tight-blocker witness (`IsLaman.typeII_reverse_blocker` in
`Henneberg.lean`) are complete.

The next session writes the **case-split argument** —
`IsLaman.exists_typeI_or_typeII_reverse` in `Henneberg.lean`. All
edge-arithmetic inputs are in place. The remaining work is a pure
graph-theory contradiction:

1. Pick `v` of degree 2 or 3 via `IsLaman.exists_two_le_degree_le_three`.
2. Degree 2: reuse `typeI_reverse_isLaman` + `typeI_iso_of_two_neighbors`.
3. Degree 3: with neighbors `{a, b, c}`, suppose for contradiction
   that *every* non-adjacent pair blocks. By
   `IsLaman.exists_nonadj_among_three_neighbors`, at least one pair is
   non-adjacent. For each non-adjacent pair `(x, y) ∈ {(a,b), (a,c),
   (b,c)}`, invoke `IsLaman.typeII_reverse_blocker` to produce a tight
   `S_{x,y} ⊆ V \ {v}` with `{x, y} ⊆ S_{x,y}` in `G`. Combine the
   `S_{x,y}`'s via `IsTightOn.union_inter` to force a tight set `T`
   containing two or three of `{a, b, c}`. Then `T ∪ {v}` overshoots
   `G`'s sparsity (each neighbor of `v` inside `T` adds an edge but
   only one vertex), contradiction. Sub-cases split on how many of
   the three pairs are non-adjacent (3 / 2 / 1).

Likely first concrete commit inside the case-split: the **3
non-adjacent pairs** sub-case (cleanest — all three witnesses
available, `IsTightOn.union_inter` applies twice to merge to
`{a, b, c} ⊆ T`). The 2- and 1-pair cases require care with
asymmetry; sketch them after the 3-pair case lands.

Milestones 1 and 2 are independent — if the case-split proof stalls,
milestone 2 (Type I rigidity preservation in `Henneberg.lean`, which
will also need to import `Framework.lean` for the first time) is a
clean parallel target. Milestone 3 (induction) is ready once
milestone 1 *and* both move-preservation lemmas land.
