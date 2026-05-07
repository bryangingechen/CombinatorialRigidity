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

**When to reconsider:** if at Phase 4 we discover that the rigidity
*matrix* arguments are easier as matroid arguments — specifically, if
proving `IsGenericallyRigid → contains a Laman spanning subgraph` ends
up needing the rigidity matroid anyway. In that case the matroid route
might be cheaper end-to-end.

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

The directory is created lazily — don't pre-populate it. As of this
writing the mirror is empty: Phase 1 lemmas proved without any gaps.



These are *open*: we expect to revise based on how proofs actually
unfold. Add to this list whenever a session surfaces a question; move
to a fixed section above once a question is answered.

- **Vertex insertion in Henneberg moves.** Keep `V` fixed and bump
  `Fintype.card` via a labeled new vertex, or pass to `V ⊕ Unit` /
  `Option V`? The right call probably depends on what the induction
  in Henneberg's theorem looks like in practice.
- **Rigidity matrix.** Build via `Matrix` directly, or as a `LinearMap`
  with `LinearMap.toMatrix` for rank arguments? Likely `LinearMap` for
  the abstract definition, `Matrix` for explicit computations on small
  examples.
- **Generic placement.** "Generic" can be (a) a placement avoiding a
  Zariski-closed set, (b) algebraically independent coordinates, or
  (c) a placement at which the rigidity matrix has maximum rank.
  Options (a) and (c) are equivalent and easier to formalize than (b);
  pick when we get to Phase 4.
- **Promoting `edgesIn` upstream.** Once it has a few users in
  `Sparsity.lean` and elsewhere, consider whether to move it to
  `Mathlib.Combinatorics.SimpleGraph.Basic` next to `incidenceSet`.
  Wait until the API has stabilized.
