# Phase 5 — Laman's theorem, (⇐) direction (work log)

**Status:** in progress.

This file is the per-phase work record. See `../ROADMAP.md` for the
high-level plan and `../DESIGN.md` for cross-cutting design choices.

## Current state

Milestones 0 and 1 are complete; milestone 2's typeI rank-nullity core
has landed (`typeI_isInfinitesimallyRigid_extend`). The remaining
sorries in the Phase-5 chain are milestone 2's wrappers
(`typeI_isGenericallyRigid_two`, `typeII_isGenericallyRigid_two`),
milestone 3 (induction), and Phase 6.

* Milestone 0 (LamanTheorem stub + d=2 corollary + iso transport) —
  done in an earlier commit.
* Milestone 1 — full strengthened decomposition theorem. Pieces:
  * `typeI_reverse_isLaman` / `typeI_isLaman_iff` (`Henneberg.lean`) —
    the degree-2 branch.
  * Edge-arithmetic infrastructure: `edgesIn_inter`,
    `edgesIn_ncard_add_le` (`EdgesIn.lean`); `IsTightOn`,
    `IsTightOn.union_inter`, `IsSparse.isTightOn_of_le`
    (`Sparsity.lean`).
  * Per-pair tight-blocker witness `IsLaman.typeII_reverse_blocker`
    (`Henneberg.lean`).
  * Overshoot primitive `IsLaman.no_isTightOn_excluding_three_neighbors`
    (`Henneberg.lean`, private).
  * Per-pair witness-or-blocker dispatcher
    `IsLaman.typeII_reverse_witness_or_blocker` (private).
  * **Squeeze-form primitive `IsLaman.False_of_three_neighbor_squeeze`**
    (private) — upgrades `2 * #T ≤ #(edgesIn T) + 3` to `T.IsTightOn`
    via `isTightOn_of_le`, then closes via the overshoot helper. The
    common tail every contradiction template reduces to.
  * **Three contradiction templates** (private): `contradiction_one_pair`,
    `contradiction_two_pair`, `contradiction_three_pair`. The 1/2/3-pair
    blocker assembly arguments, each building `T ⊆ V \ {v}` containing
    all three neighbors of `v` and verifying the squeeze, then routing
    through `False_of_three_neighbor_squeeze`.
  * Main theorem `IsLaman.exists_typeI_or_typeII_reverse`: degree-2
    branch via `typeI_isLaman_iff`; degree-3 branch via nested
    `by_cases` on the three pairs' adjacency, with each non-adjacent
    pair dispatched (success returns the typeII witness, failure
    accumulates a blocker) and each failure-leaf routed to the
    appropriate contradiction template. The all-adjacent leaf
    contradicts `exists_nonadj_among_three_neighbors`.

Milestone 2 (per-move rigidity preservation, in `Henneberg.lean`) is
the next concrete target; it is independent of milestone 3.

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

- [x] (Helper) **Overshoot contradiction primitive** —
  `IsLaman.no_isTightOn_excluding_three_neighbors` in `Henneberg.lean`
  (private). The False-form lemma every sub-case contradiction
  reduces to: a Laman `G`, vertex `v` with three distinct neighbors
  `a, b, c`, a `(2, 3)`-tight `T ⊆ V \ {v}` with `{a, b, c} ⊆ T`. The
  proof inserts `v` into `T` (size `+1`, ≥ 3 incident edges added
  disjoint from `G.edgesIn ↑T`) and reads off the contradiction with
  `G`'s sparsity at `insert v T`. ~70 lines; clean.

- [x] (Helper) **Per-pair witness-or-blocker dispatcher** —
  `IsLaman.typeII_reverse_witness_or_blocker` in `Henneberg.lean`
  (private). Wraps the by-case on `(G.comap _ ⊔ bridge).IsLaman` into
  one disjunction: success returns the full typeII decomposition
  witness with `G'.IsLaman` (typeII iso via `typeII_iso_of_three_neighbors`,
  bridge edge via `sup_adj` + `fromEdgeSet_adj`); failure returns the
  `typeII_reverse_blocker` output. Single point where the case-split
  inverts a Laman-or-not test, and the only place that has to package
  the typeII iso for the success branch.

- [x] (Helper) **Squeeze-form overshoot primitive** —
  `IsLaman.False_of_three_neighbor_squeeze` in `Henneberg.lean` (private).
  Sits between `isTightOn_of_le` and `no_isTightOn_excluding_three_neighbors`:
  consumes `2 * #T ≤ #(edgesIn T) + 3` plus `v ∉ T`, `{a, b, c} ⊆ T`,
  derives tight, then derives False. Every contradiction template
  reduces to this; the templates differ only in how they assemble `T`
  and verify the squeeze. ~10 lines.

- [x] (Helper) **1-pair contradiction template** —
  `IsLaman.contradiction_one_pair` in `Henneberg.lean` (private). One
  blocker `S` containing two outer neighbors `(x, y)` of `v`, with the
  third neighbor `z` connected to both by edges of `G`. Case-split on
  `z ∈ S`: if yes, `S` is the witness `T` directly; if no, extend to
  `T := insert z S` and count the two new edges `s(x, z), s(y, z)` to
  saturate the squeeze. ~50 lines.

- [x] (Helper) **2-pair contradiction template** —
  `IsLaman.contradiction_two_pair` in `Henneberg.lean` (private). Two
  blockers sharing a third-neighbor vertex `z`; the third pair `(x, y)`
  is adjacent in `G`. Case-split on `2 ≤ |Sxz ∩ Syz|`: if yes,
  `IsTightOn.union_inter` directly gives tightness of the union; if no
  (intersection is the singleton `{z}`), build `T := Sxz ∪ Syz` and
  invoke the supermodular `edgesIn` bound plus the cross-edge `(x, y)`
  contribution to saturate the squeeze. ~80 lines.

- [x] (Helper) **3-pair contradiction template** —
  `IsLaman.contradiction_three_pair` in `Henneberg.lean` (private).
  All three pairs non-adjacent, three blockers covering them. Three
  sub-cases on which pairwise intersection has size `≥ 2`: each
  triggers `IsTightOn.union_inter` on that pair, with the union
  already containing `{a, b, c}`. Final sub-case (all pairwise
  intersections singletons): `T := (Sab ∪ Sac) ∪ Sbc`, supermodularity
  twice (using `e({a}) = e({b, c}) = 0`) plus inclusion-exclusion for
  `#T` saturates the squeeze. ~110 lines.

- [x] `IsLaman.exists_typeI_or_typeII_reverse` — strengthened
  decomposition. Degree-2 branch via `typeI_isLaman_iff` on the iso
  transport; degree-3 branch via nested `by_cases` on adjacency of
  each of the three pairs (eight leaves), with `typeII_reverse_witness_or_blocker`
  invoked on each non-adjacent pair (success returns the witness,
  failure accumulates a blocker), and contradiction templates applied
  to the accumulated blockers. ~120 lines for the degree-3 branch.

**Blocker argument (degree-3, sketch).** With `{a, b, c}` the
neighbors of a degree-3 `v`, define for each non-adjacent pair
`(x, y)` the candidate `G_{xy} := (G - v) + edge(x, y)` on
`{w // w ≠ v}`. The edge count is automatic
(`|E(G_{xy})| + 3 = 2(n − 1)`); only sparsity is at stake. Goal:
*some* non-adjacent pair gives `G_{xy}.IsLaman`. By contradiction,
suppose all fail: each yields a `(2,3)`-subset-tight `S_{xy} ⊆
V \ {v}` containing `{x, y}` (a one-inequality chase against `G`'s
own sparsity). The 1/2/3-pair templates then build a tight `T ⊆ V \ {v}`
with `{a, b, c} ⊆ T`, overshooting `G`'s sparsity at `insert v T`.

### Milestone 2 — Move preservation in dim 2 (`Henneberg.lean`)

The classical "Henneberg moves preserve rigidity" arguments. Both go
through a *specific* placement extension; the conclusion is then
"`IsGenericallyRigid` in dim 2" (existence of a rigid placement, not
genericity in the algebraic-geometry sense).

- [x] (Helper) **`eq_zero_of_orthogonal_dim_two`** — in
  `EuclideanSpace ℝ (Fin 2)`, a vector orthogonal to two linearly
  independent vectors is zero. Proof:
  `LinearIndependent.span_eq_top_of_card_eq_finrank` (size-2 LI in
  dim 2 spans `⊤`) + `Submodule.top_orthogonal_eq_bot` + a one-shot
  span-induction reducing "perp to the span" to perp to the two
  generators. ~15 lines, private.
- [x] **`typeI_isInfinitesimallyRigid_extend`** — the rank-nullity
  core of typeI rigidity preservation. Given `G.IsInfinitesimallyRigid p`
  and a point `q` with `LinearIndependent ℝ ![q - p a, q - p b]`, the
  extension `fun w => w.elim q p` is infinitesimally rigid for
  `typeI G a b`. Proof: build a linear map
  `ker ((typeI G a b).RigidityMap p_ext) →ₗ[ℝ] ker (G.RigidityMap p)`
  by `x ↦ x ∘ some`, show it lands in the right kernel (every `G`-edge
  lifts), and is injective (the two new edges through `none` orthogonalize
  `x.1 none - y.1 none` against `(q - p a, q - p b)`, which by LI forces
  the difference to vanish). Apply
  `LinearMap.finrank_le_finrank_of_injective` + `hp`. ~70 lines.
- [ ] `typeI_isGenericallyRigid_two` — the unconditional Type I
  preservation. **Blocked on the placement-construction side condition:**
  vanilla `G.IsGenericallyRigid 2` does not guarantee a rigid placement
  with `p a ≠ p b` (let alone the stronger LI condition needed by
  `typeI_isInfinitesimallyRigid_extend`). Resolution path: introduce a
  strengthened predicate `IsGenericallyRigidInj G d := ∃ p, IsInfinitesimallyRigid G p ∧ Function.Injective p`,
  prove move preservation in the strong form, and weaken at milestone 3.
  See *Blockers* below.
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

- **Single squeeze-form primitive consumed by every template.** The
  three contradiction templates (1/2/3-pair) each end with the same
  three-step tail: build `T : Finset V`; verify `2 * #T ≤ #(edgesIn T) + 3`
  (the squeeze); apply `IsSparse.isTightOn_of_le` to get `T.IsTightOn`;
  apply `no_isTightOn_excluding_three_neighbors` to derive `False`.
  Factored as `IsLaman.False_of_three_neighbor_squeeze` so each template
  body only has to assemble `T` and prove the squeeze inequality (the
  template-specific edge accounting). Saves ~10 lines per template and
  isolates the proof-shape decision (squeeze vs. direct tight) in one
  place.

- **Restructured degree-3 main theorem: 3-level `by_cases` over outer
  `rcases exists_nonadj_among_three_neighbors`.** The original skeleton
  used the outer `rcases` to pick the first non-adjacent pair, then
  needed `exfalso` + sub-case analysis inside each of the three failure
  arms. Problem: inside `exfalso`, additional dispatcher invocations
  (needed to gather blockers for 2- and 3-pair templates) can return
  witnesses that should be returned to the outer goal — but the goal
  is `False`, blocking the return. Restructured to `by_cases` on each
  pair's `G.Adj` (8 leaves), with `typeII_reverse_witness_or_blocker`
  invoked only on confirmed non-adjacent pairs and the success arm
  returning the witness immediately at the leaf level. The all-adjacent
  leaf falls back to `exists_nonadj_among_three_neighbors` for a direct
  contradiction. ~120 lines of straight-line case analysis; flatter than
  the alternative.

- **`Sym2.eq_iff` destructure: second case is `⟨x = z, z = y⟩`, not
  `⟨x = y, z = z⟩`.** `Sym2.eq_iff.mp : s(a, b) = s(c, d) → (a = c ∧
  b = d) ∨ (a = d ∧ b = c)`. So for `s(x, z) = s(y, z)`, the second
  disjunct is `x = z ∧ z = y` — both components reference `z`, not just
  one. Forgetting this and using the second-component `z = y` where
  `x = z` was wanted produced a confusing type mismatch in the
  `hxz_ne_yz` proof in `contradiction_one_pair`. Documented as a
  one-line trap.

- **typeI rigidity-preservation core: factor out `eq_zero_of_orthogonal_dim_two`.**
  The injectivity step of `typeI_isInfinitesimallyRigid_extend` boils down to:
  in `EuclideanSpace ℝ (Fin 2)`, a vector orthogonal to two LI vectors is zero.
  Pulling this out into a 15-line lemma keeps the main proof focused on the
  rigidity-map plumbing (edge lifting, kernel restriction, applying the
  rank-nullity bound). The helper uses
  `LinearIndependent.span_eq_top_of_card_eq_finrank` plus
  `Submodule.top_orthogonal_eq_bot` plus a single-purpose `span_induction`
  over the two-element generating set. Dim-2-specific; generalising to dim
  `d` would need a different argument (or extra LI vectors).

- **`set p_ext := fun w => w.elim q p with hp_ext_def` keeps the new
  placement evaluable by `change`.** The two new-edge constraints come out
  with `p_ext none` and `p_ext (some _)`; these are defeq to `q` and
  `p _` (by the `Option.elim` reduction). The `change` tactic surfaces the
  unfolded form for the inner-product subtraction step. Pure `let` works
  too — what matters is that `set` does not block the defeq.

- **Lean dot notation balked on `mem_edgeSet.mp he` inside the proof of
  `typeI_isInfinitesimallyRigid_extend`.** Errors of the form
  `Unknown constant SimpleGraph.mem_edgeSet.mp`: dot notation looked up
  `mem_edgeSet.mp` as a fully qualified name rather than the iff
  projection. The cleanest workaround in our setting is that
  `mem_edgeSet` is `Iff.rfl` — `s(u, v) ∈ G.edgeSet` and `G.Adj u v` are
  definitionally equal — so a proof of `s(u, v) ∈ G.edgeSet` for one
  graph is accepted (via defeq) wherever the latter forms are needed for
  another `Adj`-defeq graph (`typeI_adj_some_some` is `Iff.rfl` too).
  See the FRICTION entry for the underlying elaboration issue.

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
- *Dot notation skips sub-namespaces (`h.typeII_reverse_blocker`
  fails when the helper lives in `Henneberg.IsLaman.*` and `h`'s
  type is `SimpleGraph.IsLaman`)* → FRICTION [resolved] *Dot notation
  skips sub-namespaces*. Inside a sub-namespace, call by explicit
  name; the partial-prefix lookup handles the rest.

## Blockers / open questions

- **Placement-construction side condition for Type I preservation.**
  `typeI_isInfinitesimallyRigid_extend` takes a hypothesis of the form
  `LinearIndependent ℝ ![q - p a, q - p b]`, which (in dim 2) requires
  at minimum `p a ≠ p b`. Vanilla `G.IsGenericallyRigid 2` does not
  guarantee a rigid placement of `G` with `p a ≠ p b`, so the
  unconditional wrapper `typeI_isGenericallyRigid_two` needs a
  *strengthened* hypothesis on `G`. Two routes:
  * **Strong inductive predicate `IsGenericallyRigidInj G d`**
    (existence of an *injective* rigid placement). Both endpoints of
    every Henneberg move are then `p a ≠ p b` for free; placing the
    new vertex outside the line through `p a, p b` and outside the
    finite set `p '' V` gives an injective rigid placement of the
    extension. Forwards-compatible: the milestone-3 induction maintains
    the strong predicate and weakens at the end.
  * **Affinely-spanning predicate**. Stronger; requires Phase 4's
    deferred `finrank_trivialMotions_eq_of_affinelySpanning`. Not
    obviously needed if the injective route closes typeII too.

  Recommended: implement `IsGenericallyRigidInj` in `Framework.lean`
  (with `.toIsGenericallyRigid` and `.iso` companions), prove
  `typeI_isGenericallyRigidInj_two` in `Henneberg.lean` using
  `typeI_isInfinitesimallyRigid_extend` plus a dim-2 "exists `q`
  off-line and off-finite-set" lemma, and defer the typeII parallel
  to its own commit.

- *Resolved.* ~~Affine-spanning side condition for Type I preservation.~~
  Replaced by the broader placement-construction discussion above. The
  affine-spanning route is one option; the injective route is likely
  the lighter lift.

- *Resolved.* ~~Henneberg-blocker proof length: if milestone 1 sprawls
  past ~3 sessions, reassess.~~ Landed in two sessions total
  (infrastructure + helpers in the first; templates + main theorem in
  the second) with `IsTightOn` + `IsTightOn.union_inter` already in
  `Sparsity.lean` and the contradiction templates kept in `Henneberg.lean`
  as private. No further refactor of `exists_nonadj_among_three_neighbors`
  needed.

## Hand-off / next phase

Milestone 2's rank-nullity core has landed
(`typeI_isInfinitesimallyRigid_extend` plus the auxiliary
`eq_zero_of_orthogonal_dim_two`). `Henneberg.lean` now imports
`Framework.lean` (forward edge in the DAG, no cycle). The full
unconditional wrappers `typeI_isGenericallyRigid_two` and
`typeII_isGenericallyRigid_two` are next, but each needs a
placement-construction side condition (see *Blockers* above).

**Next concrete commit**: introduce the strong predicate
`IsGenericallyRigidInj G d` in `Framework.lean` (existence of an
*injective* rigid placement), plus the basic API
(`.toIsGenericallyRigid`, `.iso`, base case
`top_fin_two_isGenericallyRigidInj_two`), then prove
`typeI_isGenericallyRigidInj_two` in `Henneberg.lean` using
`typeI_isInfinitesimallyRigid_extend` plus a small dim-2
"exists `q` off-line and off-finite-set" lemma. The typeII parallel
gets its own commit (it requires either the "Henneberg rotation"
rank-2-substitution argument or a similar strong-predicate-friendly
approach).

If the strong-predicate route turns out to need more bespoke API than
expected, fall back to the affinely-spanning route via Phase 4's
deferred `finrank_trivialMotions_eq_of_affinelySpanning`. The base
case (K₂) is *not* affinely spanning in the plane (only two points),
so that route would require strengthening the induction's base case
in a non-trivial way — a downside that the injective route avoids.

Milestone 3 (induction) becomes ready as soon as both move-preservation
lemmas (in their strong forms) land. The base case (`n = 2`) needs
`top_fin_two_isLaman` + the strong-predicate base case + `IsLaman.iso`
+ the strong-predicate iso transport; the step uses
`exists_typeI_or_typeII_reverse` (now closed) + per-move strong-form
preservation + strong-form iso transport. The unconditional
`IsLaman.isGenericallyRigid_two` (milestone-0 sorry) is then the
weakening of `IsLaman.isGenericallyRigidInj_two` via
`.toIsGenericallyRigid`.
