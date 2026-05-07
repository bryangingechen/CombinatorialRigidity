# Combinatorial Rigidity — Design Notes

This is a **reference document**, not required reading. `ROADMAP.md` is
the must-read hand-off; consult `DESIGN.md` only when you need to
understand or revisit a design choice.

Each section records *why* a particular choice was made, what was
considered as an alternative, and the cost of switching later. New
agents: don't churn on these decisions casually — if you think a
revision is warranted, add an entry to *Choices to revisit* below
rather than silently changing direction.

---

## Why Henneberg, not matroid

We follow the Henneberg construction route to Laman's theorem rather
than the matroid-theoretic route via `Mathlib.Combinatorics.Matroid`.

**For Henneberg:**
- Inductive structure (Type I / Type II moves) decomposes the proof into
  small, independently testable lemmas — each move preserves the Laman
  property, each move preserves generic rigidity, every Laman graph is
  reachable from K₂.
- Elementary; almost no prerequisites beyond what is already in
  `Mathlib.Combinatorics.SimpleGraph`.
- The matching to mathlib idiom is direct: a Henneberg move is a
  `SimpleGraph V → SimpleGraph V'` operation, and its preservation
  lemmas are equalities/inequalities on `edgeSet` and counts.

**Cost vs matroid route:**
- The equivalence "Laman ↔ Henneberg-constructible" is its own theorem
  we have to prove (rather than getting it from matroid bases).
- The proof generalizes less well beyond dimension 2.

**When to reconsider:** Phase 4 planning has confirmed the matrix
arguments — `LinearMap.ker` / `LinearMap.range` rank-nullity, kernel
monotonicity, edge-count bound — go through cleanly *without*
invoking the rigidity matroid as a `Matroid` object, so the trigger
is now **deferred to Phase 5**. The live question is whether the
(⇒) direction of Laman's theorem (`IsGenericallyRigid → contains a
Laman spanning subgraph`) wants the Lovász–Yemini matroid argument.
If so, a future `RigidityMatroid.lean` would sit on top of
`Framework.lean` (whose definitions are deliberately matroid-agnostic
— see *Notion- and matroid-agnostic core* below); refactoring back
into `Framework.lean` is *not* required.

---

## Edge type: `Set (Sym2 V)`

We represent sets of edges as `Set (Sym2 V)`, matching what
`SimpleGraph.edgeSet` already returns. `edgesIn` is also typed
`Set V → Set (Sym2 V)`.

**Why this is right for us:**
- `Sym2 V` is the symmetric square of `V` — the categorically correct
  ambient for an unordered pair of vertices.
- `Set (Sym2 V)` gives boolean-algebra operations (∩, ∪, \\, ⊆) for free,
  which we use heavily: `edgesIn s = G.edgeSet ∩ s.sym2`, monotonicity
  proofs reduce to set-theoretic monotonicity, etc.
- Doesn't force `[Fintype V]`. Sparsity is naturally a *universal*
  statement over finite vertex subsets of an ambient (possibly
  arbitrary) type.
- The rest of mathlib's `SimpleGraph` API (`incidenceSet`,
  `Subgraph.edgeSet`, `fromEdgeSet`, …) lives in this type, so we
  inherit the lemma library at no cost.

**The wart we're accepting.** `Sym2 V` includes the diagonal
`s(v, v)` (loops), which can never be edges of a simple graph. So
`Set (Sym2 V)` is *strictly larger* than the type of "things that
could be an edge." Mathlib enforces irreflexivity by content
(`not_isDiag_of_mem_edgeSet`) rather than at the type level. In
practice this surfaces as the occasional "this isn't a self-loop"
obligation; `not_mem_edgeSet_of_isDiag` is `@[simp]` so it usually
auto-discharges.

**Alternatives considered:**

1. **`Finset (Sym2 V)`.** What `SimpleGraph.edgeFinset` returns when
   `V` is finite. Better for `decide` and for `Finset.card`-based
   counting. *Likely action:* keep `edgesIn` on `Set (Sym2 V)` for the
   *definition* of sparsity (which quantifies over all finite vertex
   subsets), and add a `Finset`-valued companion guarded on
   `[Fintype V] [DecidableRel G.Adj]` once we hit proofs that benefit.

2. **`SimpleGraph V` itself, via the lattice.** mathlib makes
   `SimpleGraph V` a `CompleteAtomicBooleanAlgebra`, so `⊥`, `⊤`,
   `G ⊓ H`, `G \ H` are graphs and `G ≤ H ↔ G.edgeSet ⊆ H.edgeSet`.
   For Henneberg moves (which are graph operations) this is the
   *better* idiom and we should prefer it over raw `Set (Sym2 V)`
   surgery.

3. **`{e : Sym2 V // ¬e.IsDiag}`.** Type-theoretically tightest; rejected
   because mathlib didn't go this way and we'd be inserting
   projections/lifts at every interface.

4. **A bespoke edge type with endpoint maps (multigraphs).** Wrong
   shape: rigidity theory is virtually always phrased on simple
   undirected graphs. `Mathlib.Combinatorics.Graph` exists for the
   multigraph case but is not where we want to live.

**Closest mathlib analogues to `edgesIn`:**
- `((⊤ : G.Subgraph).induce s).edgeSet` — same content, routed through
  the heavier `Subgraph` machinery.
- `(G.induce s).edgeSet` — graph on the *subtype* `↥s`; edges live in
  `Set (Sym2 ↥s)`, requires `Sym2.map Subtype.val` to come back.
- `SimpleGraph.incidenceSet v` — single-vertex version of the same
  pattern, `{e ∈ G.edgeSet | v ∈ e}`.
- `SimpleGraph.interedges` (`Density.lean`) — counting analogue, but
  ordered (`α × α`) and bipartite (two finsets).

The combination "single vertex set, both endpoints in it, returned as
`Set (Sym2 V)`" doesn't appear to exist in mathlib as a named def. If
we ever upstream it, the natural home is alongside `incidenceSet` in
`SimpleGraph/Basic.lean`.

---

## `Set.ncard` over `Finset.card`

`IsSparse` uses `Set.ncard` on `edgesIn`, so the definition does *not*
require `[Fintype V]`. A `Finset.card` reformulation is one rewrite
away whenever a proof has `[Fintype V] [DecidableRel G.Adj]` in scope
(via `Set.ncard_coe_finset` and friends).

**Trade:** ergonomic for definitions, slightly more work in proofs that
genuinely care about computability or `decide`. The sparsity definition
is fundamentally non-computational anyway — you have to quantify over
all vertex subsets — so this is the right side to land on.

**When to reconsider:** if and when we want `IsLaman` to be `Decidable`
on a concrete `Fintype V`, we'll need a decidable reformulation that
goes through `Finset.sym2` and `Finset.filter` rather than `Set.ncard`.
That's an *additional* lemma, not a replacement of the current
definition.

---

## ℕ-arithmetic, no subtraction

`IsSparse` is phrased as `(G.edgesIn ↑s).ncard + ℓ ≤ k * s.card` rather
than `… ≤ k * s.card - ℓ`, with a guarding hypothesis
`ℓ ≤ k * s.card`.

**Why:** `ℕ`-subtraction silently truncates at 0, which would make
small-cardinality cases of the bound vacuously hold for the wrong
reason. The additive form is unambiguous and `omega`-friendly.

**Alternative:** go to `ℤ` and write `(… : ℤ) ≤ k * s.card - ℓ`. Cleaner
algebraically but introduces a coercion at every use site. Not worth
it for a definition that's overwhelmingly used in `ℕ` contexts.

---

## Generality of dimension `d`

From Phase 4 onward, every definition and lemma is stated for
arbitrary dimension `d : ℕ`, not specialized to `d = 2`. The
`2 * #V - 3` Laman edge bound is the `d = 2` specialization of a
general-`d` `d * #V ≤ #E + d(d+1)/2` statement that holds for *any*
generically rigid graph in dimension `d` — same proof, no
preconditions other than the existence of an infinitesimally rigid
placement. The K₂ base case is infinitesimally rigid in any
`d ≥ 0` for the same rank-nullity reasons.

**Why:** specializing earlier hides the underlying linear algebra
(the constant `d(d+1)/2` is just the dimension of the trivial-motions
subspace, not a magic number) and turns any future higher-dimensional
work into a refactor rather than a copy-paste. The boundary at which
`d = 2` enters legitimately is **Phase 5**, where the count matroid
is `(2, 3)` and the connection to *Laman* graphs (specifically) is
made.

**Cost:** none we can see. Phase 4's four ROADMAP lemmas all hold for
general `d` with the same proofs they would have at `d = 2`. The
`#V ≥ d` precondition some lemmas require is the natural
generalization of `#V ≥ 2`; it surfaces only where it would have
under the specialization anyway.

**Practical rule for proofs in `Framework.lean` and beyond:** prefer
`Module.finrank` arguments over coordinate arguments, and `Fintype V`
over `V = Fin n` specializations, so that "ambient inner product
space is `EuclideanSpace ℝ (Fin d)`" can be relaxed to "arbitrary
finite-dim inner product space" later by replacing
`d * (d + 1) / 2` with `finrank ℝ E * (finrank ℝ E + 1) / 2`. We do
*not* make this generalization now (premature; no caller wants it),
but we don't paint ourselves into a corner either.

---

## Notion- and matroid-agnostic core

`Framework V d`, `RigidityMap`, `TrivialMotions`, and
`IsInfinitesimallyRigid` (Phase 4) are deliberately defined without
reference to any specific rigidity notion beyond infinitesimal, and
without invoking `Mathlib.Combinatorics.Matroid`.

**Why:** other rigidity notions — local (continuous), global,
generic global, redundant, body-bar / body-hinge — and the abstract
rigidity matroid are all *consumers* of these definitions. Each
slots in as a separate file (`LocalRigidity.lean`, `GlobalRigidity.lean`,
`RigidityMatroid.lean`, …) once needed; none requires
`Framework.lean` to be refactored. Specifically:

- The rigidity matroid (independence = row-independence of
  `RigidityMap` for generic `p`) is a one-line definition once
  `Framework.lean` exists, but the `Matroid` object isn't needed
  for any Phase 4 lemma and isn't needed for the (⇐) direction of
  Laman's theorem. A `RigidityMatroid.lean` would land only if
  Phase 5's (⇒) direction goes via Lovász–Yemini.
- Local rigidity needs continuous-motions API on top of
  `Framework V d`; global rigidity is a separate `Prop` independent
  of the infinitesimal layer; body-bar / body-hinge frameworks have
  their own parameter spaces. None of these touch the rigidity
  matrix as an abstract object.

**Anti-pattern to avoid:** do *not* introduce a typeclass like
`IsRigidityNotion (P : SimpleGraph V → Prop)` or factor
`IsInfinitesimallyRigid` through an abstract base. The "right"
abstraction will only become clear once at least one alternative
notion is on disk; until then the typeclass would be load-bearing
in exactly one direction. Keep things concrete; add the abstraction
later if multiple consumers materialize.

---

## Mirror directory for missing mathlib lemmas

If, while proving something here, we hit a lemma that *should* exist in
mathlib proper (because it's about `SimpleGraph`, `Sym2`, `Set.ncard`,
etc., and is not specific to rigidity), we put it under

```
Archive/CombinatorialRigidity/Mathlib/<exact mathlib path>
```

For example, a missing lemma about `SimpleGraph.edgeSet` that would
naturally live in `Mathlib/Combinatorics/SimpleGraph/Basic.lean` goes
into `Archive/CombinatorialRigidity/Mathlib/Combinatorics/SimpleGraph/Basic.lean`.

The mirror keeps each candidate lemma in the file it would land in
upstream, so promotion to mathlib is a copy-paste with the file's
existing context. The Lean namespace stays the standard one
(`SimpleGraph`, `Set`, …), not the project's.

Each file in the mirror should open with a docstring stating that the
contents are upstream candidates and which mathlib path they target.

The directory is created lazily — don't pre-populate it. Phase 1
proved without gaps; Phases 2 and 3 together surfaced ~12 upstream
candidates spread over six paths:

- `Mathlib/Combinatorics/SimpleGraph/Finite.lean` — `Set.ncard`
  companions of `card_incidenceSet_eq_degree` and friends
- `Mathlib/Data/Finset/BooleanAlgebra.lean`,
  `Mathlib/Data/Fintype/Card.lean` — `coe` / `card` forms of
  `Finset.compl_singleton`
- `Mathlib/Data/Set/Card.lean` — unconditional `≤ 2` and `≤ 3`
  ncard bounds for pairs / triples
- `Mathlib/Data/Sym/Sym2.lean` — `Sym2.map some` injectivity, the
  predicate-form image-membership `simp` lemma, plus two helpers for
  `none ∉ Sym2.map some _` and the disjointness pattern
- `Mathlib/Data/Finset/Option.lean` — addition-form
  `card_eraseNone_of_mem` (mathlib's version uses `ℕ`-subtraction,
  forbidden by the project)

See `notes/FRICTION.md` "Mirrored" for the per-lemma rationale;
phases 4 and 5 will likely add more (the Phase 4 plan flags one
open question — whether mathlib has `finrank` for
`skewAdjointMatricesSubmodule`).

---

## Choices to revisit

These are *open*: we expect to revise based on how proofs actually
unfold. Add to this list whenever a session surfaces a question; move
to a fixed section above once a question is answered.

- ~~**Vertex insertion in Henneberg moves.**~~ **Resolved (Phase 3 start):**
  Use `Option V`. The fresh vertex is `none`; old vertices embed via
  `some : V ↪ Option V`. Chosen over `V ⊕ Unit` for readability and over
  fixed-`V`-with-`v ∉ G.support` because the latter forces every move to
  carry a freshness side-condition. Mathlib has no precedent for "add a
  single vertex to a `SimpleGraph`"; `Option α` is the canonical "add
  one element" idiom (cf. `Equiv.optionEquivSumPUnit`). Cost: chained
  moves give types `Option (Option …)`; mitigated by working modulo
  isomorphism in the Phase 5 induction. Companion decision: drop the
  `Reachable` inductive in favour of `IsLaman.exists_typeI_or_typeII_reverse`
  + strong induction on `Fintype.card V`, since heterogeneous-type
  reachability has no mathlib precedent.
- ~~**`Reachable` inductive vs structural decomposition.**~~ **Resolved
  (Phase 3 start):** No `Reachable`. Phase 5's Laman's-theorem proof
  uses `IsLaman.exists_typeI_or_typeII_reverse` plus strong induction on
  `Fintype.card V`. See `notes/Phase3.md` "Architectural choices".
- ~~**Structural `Adj` vs lattice `G.map .some ⊔ fromEdgeSet …`.**~~
  **Resolved (Phase 3, mid-session):** Structural. The lattice form was
  attempted and abandoned: `(G.map .some).Adj (some u) (some v)` unfolds
  to `∃ u' v', G.Adj u' v' ∧ some u' = some u ∧ some v' = some v` and
  simp does not always discharge the existential cleanly. Structural
  match-based `Adj` makes all eight adjacency lemmas `Iff.rfl`; the cost
  is one manual `Sym2.ind`-based proof for the edgeSet decomposition.
- ~~**Decomposition theorem: one statement or split?**~~ **Resolved
  (Phase 3 close):** Split. The Phase 3 hand-off planned a single
  `IsLaman.exists_typeI_or_typeII_reverse` that gave both (a) the
  iso `G ≃g typeI/II G'` and (b) `G'.IsLaman`. Working through
  the proof revealed (b) is much harder for typeII than the hand-off
  implied — an arbitrary non-adjacent neighbor pair can fail to give
  a Laman `G'` (concrete counter-example in `notes/Phase3.md`).
  Phase 3 ships only (a) as `IsLaman.exists_typeI_or_typeII_iso`;
  the strengthened (a)+(b) version is a Phase 5 prerequisite. The
  split makes both halves cleanly testable: the iso uses
  `(Equiv.optionSubtypeNe v).symm` and is mechanical, while the
  Laman-preservation half is the Henneberg blocker argument and can
  be approached independently (or bypassed via the matroid route —
  see ROADMAP §5 *Carryover from Phase 3*).
- ~~**Rigidity matrix.**~~ **Resolved (Phase 4 plan):** `LinearMap` for the
  abstract definition, with `LinearMap.toMatrix` deriving the matrix view
  on demand. Rank-nullity and kernel-of-restriction arguments are
  cleanest on the `LinearMap` side; the matrix view costs one
  `LinearMap.toMatrix` rewrite when a `Matrix.rank` fact is needed.
  See `notes/Phase4.md` *Architectural choices*.
- ~~**Generic placement.**~~ **Resolved (Phase 4 plan):** option (c).
  `G.IsGenericallyRigid d := ∃ p : Framework V d, G.IsInfinitesimallyRigid
  p d`. Avoids algebraic-geometry prerequisites (no `MvPolynomial` /
  Zariski-set machinery in scope). The equivalence to "rank max on a
  Zariski-open set" is downstream and not needed for Phase 5 if (⇒) goes
  via the rank bound directly. See `notes/Phase4.md` *Architectural
  choices*.
- **Promoting `edgesIn` upstream.** Once it has a few users in
  `Sparsity.lean` and elsewhere, consider whether to move it to
  `Mathlib.Combinatorics.SimpleGraph.Basic` next to `incidenceSet`.
  Wait until the API has stabilized.
