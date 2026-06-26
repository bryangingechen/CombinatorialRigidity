# Combinatorial Rigidity — Design Notes

This is a **reference document**, not required reading. `CLAUDE.md`
(agent operating manual) and `ROADMAP.md` (status, plan, conventions)
are the must-read hand-offs; consult `DESIGN.md` only when you need
to understand or revisit a design choice.

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

**When to reconsider:** Phase 4 confirmed the matrix arguments —
`LinearMap.ker` / `LinearMap.range` rank-nullity, kernel monotonicity,
edge-count bound — go through cleanly *without* invoking the rigidity
matroid as a `Matroid` object. Phase 5 followed the same line for the
(⇐) direction (Henneberg induction). Phase 6 closed the (⇒) direction
via Lovász–Yemini's easy identification of row-independence with
$(2, 3)$-sparsity; `RigidityMatroid.lean` sits on top of
`Framework.lean` (whose definitions are deliberately matroid-agnostic —
see *Notion- and matroid-agnostic core* below) and packages the
row-independence relation plus its two named facts without
materialising an abstract `Matroid` instance. Refactoring back into
`Framework.lean` is *not* required.

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
  `RigidityMap` for generic `p`) is a one-line relation once
  `Framework.lean` exists, but the abstract `Matroid` object isn't
  needed for any Phase 4 lemma or for Phase 5's (⇐) direction.
  `RigidityMatroid.lean` landed in Phase 6 to support the (⇒)
  direction (Lovász–Yemini); it ships the row-independence relation
  and the rank lemmas without packaging the abstract `Matroid`
  instance — see `notes/Phase6.md` *Architectural choices*.
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

## Statement-form conventions: forward (operation) vs reverse (flat)

Theorems about Henneberg moves split into two categories, and we
state them in different forms. The split is principled, not a
mixture; the principle below pins it down so the next session can
land lemmas without re-litigating the call.

**Forward preservation theorems** — *"`Henneberg.typeI G' a b`
preserves property P"*: `typeI_isLaman`, `typeI_isLaman_iff`,
`typeI_isGenericallyRigidInj_two`, the upcoming row-independence
lifts. Statement form: **operation form** — the named operation
appears in the conclusion. Mathlib analogue: `Finset.image_disjoint`,
`Polynomial.degree_C_mul`. The theorem is *about* the operation; the
operation's name is the subject and must be in the statement.

**Reverse decomposition theorems** — *"every G with property X
admits a smaller G' with property Y"*: `IsLaman.exists_typeI_or_typeII_reverse`,
`IsSparse.exists_typeI_or_typeII_reverse`. Statement form: **flat
form** — the smaller G' is given by its edges (`G.comap` /
`fromEdgeSet`), not via a Henneberg constructor. Mathlib analogue:
`Finset.exists_max_image`, `Polynomial.exists_root_of_natDegree_pos`.
The theorem is *about an arbitrary G* and produces a witness; the
operation is incidental.

**Iso constructors** — `typeI_iso_of_two_neighbors`,
`typeII_iso_of_three_neighbors`. These genuinely *are* iso content;
they live in Henneberg.lean as project-internal bridges between the
two forms.

**Bridging.** A callsite that combines a flat reverse with an
operation-form forward lift (e.g. Phase 5's `IsLaman.isGenericallyRigid_two`
induction, Phase 7's `IsSparse.exists_rowIndependent_placement`
induction) does *one* iso construction per inductive step, via the
project-internal constructors above. This is not a "mixture" — it is
how a "G has structure" claim hands off to an "operation preserves
property" claim, no different in shape from any other point in
mathlib where `Finset.exists_max_image` is followed by a fact about
`Finset.image`.

**Why this split is not a mixture.** Forcing operation form on
reverse decompositions costs strength: `IsSparse.exists_typeI_or_typeII_reverse`
in iso form would need a side hypothesis ruling out matchings +
isolated vertices ($K_{1,5}$ is sparse but iso to no Henneberg move),
weakening the theorem. Forcing flat form on forward preservation
costs reusability: a caller who already has `typeI G' a b` in hand
would have to manually re-verify vertex / neighborhood conditions
that are tautological from the operation. Each form fits its
category; the categories are different.

The full rationale, including the K_{1,5} obstruction and a few more
mathlib analogues, lives in the *Statement-form aside* in
`blueprint/src/chapter/rigidity-matroid.tex` (just before
\S\,\emph{Lifting row-independence through Henneberg moves}).

---

## Mirror directory for missing mathlib lemmas

If, while proving something here, we hit a lemma that *should* exist in
mathlib proper (because it's about `SimpleGraph`, `Sym2`, `Set.ncard`,
etc., and is not specific to rigidity), we put it under

```
CombinatorialRigidity/Mathlib/<exact mathlib path>
```

For example, a missing lemma about `SimpleGraph.edgeSet` that would
naturally live in `Mathlib/Combinatorics/SimpleGraph/Basic.lean` goes
into `CombinatorialRigidity/Mathlib/Combinatorics/SimpleGraph/Basic.lean`.

The mirror keeps each candidate lemma in the file it would land in
upstream, so promotion to mathlib is a copy-paste with the file's
existing context. The Lean namespace stays the standard one
(`SimpleGraph`, `Set`, …), not the project's.

Each file in the mirror should open with a docstring stating that the
contents are upstream candidates and which mathlib path they target.

The directory is created lazily — don't pre-populate it. See
`notes/FRICTION.md` "Mirrored" for the per-lemma rationale and the
authoritative list of paths currently in use; the running tree
under `CombinatorialRigidity/Mathlib/` is the
ground truth.

---

## Local mirror of the matroid-union subsystem (Phase 12)

**Decided 2026-06: formalize the matroid-union prerequisite locally,
in-repo, under `CombinatorialRigidity/Matroid/`.** This is a deliberate
**exception** to the mirror-directory rule above (which is for *small*,
single-lemma upstream candidates about `SimpleGraph`/`Sym2`/`Set.ncard`).
The matroid-union subsystem is a ~1800-line body of proof
(matroid-from-submodular-function + polymatroid rank + matroid union +
Edmonds partition), not a glue lemma.

Context: the body-bar route (Phases 12–15) needs matroid union and
Edmonds' partition theorem. These are **already fully formalized**
(zero-sorry) in Peter Nelson's `apnelson1/Matroid` package, in its
shelved `WIP/{Submodular,Union}.lean` — but those files do not build,
because they rest on a Finset-based circuit-axiom constructor
(`FinsetCircuitMatroid`) that the package commented out and superseded
with the Set-based `FiniteCircuitMatroid` (the constructor
`Graph.cycleMatroid` now uses). So the work is a **port/rebase onto the
live constructor**, not a from-scratch formalization.

Why local, not upstream-first (the user's call): full control and an
immediate unblock, no dependence on maintainer responsiveness. The
trade-off — owning a large chunk of matroid foundations that morally
belongs upstream — is accepted; an upstream contribution of the rebased
machinery can still be offered later (and the per-file headers make the
provenance explicit, so it stays offer-able).

**Route is decided by an in-phase spike** (Phase 12 Layer 1):
submodular-repair (rebase `ofSubmodular` onto `FiniteCircuitMatroid`)
vs. deriving union from the package's already-live `Matroid.Intersection`
via duality. See `notes/Phase12.md`.

**Attribution / license.** The package is Apache-2.0 (as is this
project and mathlib), so there is no license issue; vendoring is
permitted. Apache §4 obligations (retain authorship, state changes) are
met by per-file headers crediting **Peter Nelson** with a provenance +
modifications note, the credit paragraph in
`blueprint/src/chapter/matroid-union.tex`, and the provenance note in
`CLAUDE.md`. This supersedes the old Phase-12 hand-off's "wait for
upstream" option.

---

## Set/Finset and rank-flavor boundary at the matroid layer (Phases 13–15)

**Context.** Phase 12's vendored matroid subsystem (above) is
`Finset`-heavy *internally* — submodular functions `f : Finset α → β`,
Hall/Rado transversal families `A : ι → Finset α`, the circuit
predicate — whereas the project's combinatorial core (Phases 1–11)
deliberately works `Set`-side with `Set.ncard` and `[Finite V]` (see
*`Set.ncard` over `Finset.card`* above and the resolved *Typeclass shape
for finiteness on `V`* note under *Choices to revisit* below). The
question for the downstream body-bar phases
is whether that mismatch leaks across the API boundary. Checked against
the exported Phase-12 signatures (2026-06):

- **Independence is clean `Set`.** `union_indep_iff` /
  `union_indep_iff'` quantify over `Is : ι → Set α` and speak in
  `(Matroid.Union Ms).Indep (I : Set α)`. Consumers touch no `Finset`
  (modulo a `[DecidableEq α]` that `classical` discharges).
- **The partition theorem is *forked*, and the fork is the real
  friction axis** — not `Set`/`Finset` per se, but the *rank flavor*
  coupled to the finiteness typeclass:
  - `matroid_partition'` — `ℕ`-valued, `Finset`-flavored: `∃/∀ Y :
    Finset α`, `M.rk Y`, `(Finset.univ \ Y).card`, `(M₁.union M₂).rank`;
    needs `[DecidableEq α] [Fintype α]`.
  - `matroid_partition_eRk'` — `ℕ∞`-valued, `Set`-flavored: `∃ Y : Set
    α, M₁.eRk Y + M₂.eRk Y + (univ \ Y).encard = (M₁.union M₂).eRank`;
    needs only `[DecidableEq α] [Finite α]`.

  So the genuine recurring cost across Phases 13–15 is the `rk` (ℕ) /
  `eRk` (ℕ∞) / `ncard`·`card` (counting) triple plus the
  `Fintype`+`DecidableEq` vs `Finite` plumbing. `Finset` leaks *only*
  into the `ℕ` form — which is exactly the form tree-packing (Phase 13)
  reaches for, since `(k,ℓ)`-sparsity is a natural-number edge-count
  condition.

**Two decisions that keep this contained — no big refactor.** The
vendored layer already ships *both* bracketing forms (`Finset`/`ℕ`/
`Fintype` and `Set`/`ℕ∞`/`Finite`), so rewriting its internals to `Set`
buys nothing the brackets don't already give; that option is rejected
(it would also cost the byte-closeness to upstream the vendoring
decision values). Instead:

1. **Phase 13's `Graph`-native `(k,ℓ)`-sparsity is defined `Set`-side** —
   `Set.ncard` of edge sets, `ℕ`, `[Finite]` — matching both the
   Phases-1–11 convention and the eventual adapter output, so there is
   exactly one conversion layer (sparsity-count ↔ matroid-rank), not
   two. Reaching for `Finset.card` because the Phase-12 internals are
   `Finset`-flavored is the trap that would double the glue.
2. **A thin rank adapter, built at Phase 13's open** (not speculatively
   now): one file restating the partition theorem in `Set`-`Y` / `ℕ` /
   `Set.ncard` / `[Finite]` idiom for the `k`-fold `cycleMatroid` union
   over a finite edge type, discharging the `Fintype`/`DecidableEq`/
   finite-rank plumbing and the `ℕ∞ → ℕ` conversion once, so Phases
   13–15 see a single clean `ncard`/`ℕ` surface. Reserved, not written
   ahead of its first concrete consumer (cf. *Reshape past results in
   place* — build against a real caller, don't guess the interface).
   Decided 2026-06 ("document now, build at Phase 13 open").

---

## Strengthen the existing lemma, don't proliferate variants

When a downstream proof needs a lemma close to one that already
exists but with slightly different hypotheses — typically *weaker*
hypotheses, e.g. a subset where the existing lemma takes an
equality — the default move is to **broaden the existing lemma in
place**, not to add a `_foo_of_X` variant alongside it.

Concretely:

- If the new hypotheses *strictly imply* the old ones, and the
  existing proof body still works (perhaps with a one-line shim at
  the spot where the old hypothesis was extracted), the lemma is
  strictly more general under the new signature. Update its
  signature, update its call sites to pass the now-broader
  hypotheses (which the existing callers already had under the
  tighter form), and the project's API surface stays small.
- If the lemma's *conclusion* would weaken under the new
  hypotheses, or if the proof needs a real change to accommodate
  the wider input, then it's a different lemma — a new variant is
  fine, but think first about whether the existing lemma should
  just *call* the new general one as a one-line corollary, again
  keeping a single authoritative statement.

The failure mode this rule guards against is API drift — two near-
identical lemmas (`foo_of_eq` and `foo_of_subset`) coexisting,
each used by a different caller, until a third caller can't decide
which to invoke and the project ends up with three. Phase 9's
`span_succ_le_edgesIn_ncard_of_insert` → `_of_subset` refactor
(equality `G.edgeFinset = insert s(u, v) D.underline` →
membership + subset, dropping the redundant `h_fresh` parameter
that was now derivable from existing algorithmic preconditions) is
the canonical example: the conclusion is identical, callers pass
slightly different but equivalent witnesses, and the fold-level
consumer can now apply the lemma directly instead of building an
intermediate-graph shim.

This is independent of whether the new caller is in-phase or
upstream. The same rule applies when a mathlib mirror lemma's
signature turns out to be tighter than needed — relax in place,
update the one or two existing callers.

There are two exceptions worth calling out, both narrow:

1. **Mathlib upstream candidates.** A mirror lemma whose signature
   tries to *match* the eventual mathlib statement should not be
   broadened past what mathlib would accept — the point of the
   mirror is copy-paste-ability. Broaden only if the result still
   reads as a plausible upstream addition.
2. **Already-published API surfaces with many callers.** The cost
   of updating dozens of callsites can outweigh the cost of one
   variant. This is rare in this project (most "many caller"
   lemmas are mathlib's, not ours).

If you find yourself reaching for the variant route as "the easy
path" — the friction signal is exactly the one this rule names —
go back and broaden instead. The next agent shouldn't have to
learn which of `foo_of_eq` / `foo_of_subset` / `foo_of_*` is the
canonical entry point for what is mathematically one lemma.

---

## Reshape past results in place, don't parallel-extract

A sibling rule to *Strengthen the existing lemma, don't proliferate
variants* above, but at a different scale. When a new phase needs to
**enrich the return type or signature of an already-shipped algorithm
or theorem** — typically extending an `Option`-shaped surface with
verdict-carrying witness data, or lifting an iff into the conclusion
of a wrapper — the default move is to **reshape the existing
declaration in place**, not to ship a parallel `*_witness` / `*_with_X`
extraction wrapper alongside the original.

The friction signal is the same — two near-identical declarations
covering what is mathematically one operation, each used by a
different caller — but the failure mode is sharper. A parallel
witness-extraction wrapper duplicates the entire underlying recursion
or fold structure: every case lemma, every invariant-propagation
helper, every workhorse-layer correctness theorem now has *two*
callers that need to be kept in sync. The "easy" route adds an order
of magnitude more code than the in-place reshape, because the
algorithmic infrastructure is *not* small.

Concretely:

- **Phase 7** reshaped Phase 3's `IsLaman.exists_typeI_or_typeII_reverse`
  (originally shipped with the iso-only half, no `G'.IsLaman` claim)
  into the strengthened flat form with `G'.IsLaman`, rather than
  shipping a separate `IsLaman.exists_typeI_or_typeII_reverse_isLaman`
  alongside the iso-only original. Phase 3 and Phase 5 callers
  inherit the strengthened conclusion automatically.
- **Phase 11** reshaped Phase 9/10's
  `runPebbleGame` / `runPebbleGameExec` (originally
  `Option (PartialOrientation V)`-returning) into a verdict-bearing
  `PebbleGameResult G k ℓ`, rather than shipping a parallel
  `runPebbleGameExec_blocking_witness` extraction wrapper. The
  Phase 9 `_isSome` / `_eq_none_imp_exists_witness` existence chain
  (~200 LoC in `Correctness.lean`) is absorbed into the wrapper's
  return type; the Phase 10 certificate-form
  `runPebbleGameExec_correct` iff collapses into the verdict's *type*
  rather than a separately-proven theorem about it. The
  mathematical content (`independent_brings_pebble`, the `Reachable`
  invariants) is preserved verbatim — what changes is the return
  shape, not the math.

The trade is **a phase's worth of restate work on the already-green
surface** — workhorse lemmas, downstream wrappers, blueprint nodes —
versus a permanent doubling of the algorithmic infrastructure plus a
"which entry point?" decision every callsite has to make. In both
recorded cases above, the restate work was the better trade.

There are two exceptions worth calling out:

1. **The reshape's per-Layer cost dominates the duplication cost.**
   If the underlying algorithmic infrastructure is small (a
   one-screen recursion, no fold) and the reshape would touch every
   workhorse correctness theorem, a parallel wrapper may genuinely
   be cheaper. Rare in this project — most algorithm-bearing
   declarations have non-trivial infrastructure behind them.
2. **The original surface is downstream-stable API with many
   external callers.** A reshape would break every caller; the
   variant route preserves backward compatibility. Also rare here —
   the project's wrappers are mostly internal.

The default presumption is reshape. If you find yourself reaching
for the parallel-extraction route as "the easy path" while looking
at infrastructure that took multiple Layers to build the first time,
the rule above is the friction signal — go back and reshape in
place. The next agent (and the blueprint dep-graph) shouldn't have
to navigate two surfaces for what is one algorithm.

This rule pairs with `blueprint/CLAUDE.md` *Extending an existing
chapter → restating existing entries in place*, which carries the
matching blueprint-side discipline for reshape phases.

---

## Pebble-game style island: `[Fintype V] [DecidableEq V]`

The pebble-game line of work — `CombinatorialRigidity/Search/DFS.lean`
(pre-Phase-9 verified DFS) and the
`CombinatorialRigidity/PebbleGame/{Basic, Algorithm, Correctness}.lean`
subdirectory (Phase 9 main work, three-way split for size /
modularity) — is a deliberate style island. Both files take `[Fintype V] [DecidableEq V]`
directly in their algorithm signatures and use `Finset.card`
end-to-end.

The rest of the project follows the `[Finite V]` + inline
`Fintype.ofFinite V` bridge idiom (see *Typeclass shape for finiteness
on `V`* above). The pebble-game files depart because:

- The algorithm body builds `Finset (V × V)`-backed partial
  orientations and iterates over `Finset V` out-neighbourhoods; the
  state machine cannot run at `[Finite V]` strength (no `Finset.univ`,
  no enumeration).
- `#eval` and `decide` should actually fire on extracted certificates,
  which requires the typeclasses end-to-end.
- The certificate-form correctness theorems bridge to the
  noncomputable `IsSparse` / `IsTight` statements via a thin shim
  section; bridge instances propagate one-way (caller `[Fintype V]`
  $\Rightarrow$ callee `[Finite V]` is automatic), so the style island
  does not contaminate the rest of the project's API.

This was foreshadowed in the typeclass-shape section's *Pebble-game
pointer*: "lift signatures to `[Fintype V] [DecidableEq V]`" is
forward-compatible with the present trajectory. The style-island
form keeps that lift localized to the two files that need it rather
than propagating it across the whole project.

**Math layer / exec layer split.** `Finset.toList` is noncomputable
in mathlib (it lifts through `Multiset.toList`'s `Classical`-flavored
`Quotient.lift`; there is no canonical permutation representative of
an unordered collection). A DFS / pebble-game body that enumerates
out-neighbours via `(succ v).attach.toList` therefore propagates
`noncomputable` to the whole algorithm — blocking the `#eval` and
small-graph `decide` goals above. The style island resolves this by
splitting:

- *Exec layer* — algorithm inputs that need enumeration are typed
  `V → List V` (and similarly `List (V × V)` for orientations,
  `List (Sym2 V)` for edge-insertion requests). Fully computable;
  `#eval` fires.
- *Math layer* — internal state that needs set-semantics
  (deduplication, membership, complement) stays `Finset V`. The DFS
  warmup's `visited : Finset V` is the canonical instance: the
  termination measure `(Finset.univ \ visited).card` lives on the
  math layer, while children enumeration `(succ v).attach.findSome?`
  lives on the exec layer.

Callers that hold adjacency data in `Finset` form should expose a
list projection at the algorithm boundary (with an optional `Nodup`
invariant where set semantics matter for downstream proofs); the
projection itself is the only place the `Finset`/`List`
correspondence enters, and stays noncomputable in isolation without
contaminating the algorithm.

**The "`-With` variant" pattern.** A naive `Finset`-derived projection
(e.g. `outList := D.outNbhd.toList`) still propagates `noncomputable`
to every consumer of the algorithm that calls it, which defeats the
point of the exec layer when an IO-driven pipeline (parser →
algorithm → output) wants `#eval` to fire end-to-end. The realised
pattern in `PartialOrientation`'s `tryReachPebble` is to split:

- a *computable workhorse* `tryReachPebbleWith D P v succ h_succ`
  that takes the enumeration `succ : V → List V` and a propositional
  witness `h_succ` of `succ`-vs-`D.arcs` agreement as parameters;
- a *math-layer convenience* `tryReachPebble D P v` that is a
  one-line `noncomputable` wrapper plugging in `succ := D.outList`
  with `D.mem_outList` for the propositional witness.

The propositional witness costs nothing at runtime (it's erased).
Soundness / completeness theorems land on the `-With` workhorse and
inherit to the math-layer wrapper as one-line corollaries for any
concrete `succ`. IO-driven callers reach for `tryReachPebbleWith`
directly with a `List`-shaped adjacency built from their input data,
bypass `outList` entirely, and stay fully computable; abstract
math-layer users reach for `tryReachPebble` and pay nothing extra.

Subsequent pebble-game layers (`tryAddEdge`, `runPebbleGame`) follow
the same `-With` / math-layer-wrapper split, propagating the
caller-supplied `succ` through. At `tryAddEdge` the recursive call's
orientation `D'` is the path-reversal of `D` and therefore different
from `D`; `succ : V → List V` would no longer match `D'.arcs`. The
form generalises to an orientation-indexed
`toSucc : PartialOrientation V → V → List V` with a universally-
quantified agreement witness
`∀ D' a b, b ∈ toSucc D' a ↔ (a, b) ∈ D'.arcs` — one `toSucc` good for
the entire recursion tree. The math-layer wrapper plugs in
`fun D' => D'.outList`; IO callers supply a list-shaped enumeration
parametrised on `D'`. The pattern is the same, just lifted one
abstraction level. See `notes/FRICTION.md` *[resolved] `Finset.toList`
is noncomputable — math/exec layer split* for the design history.

---

## One `Decidable` instance per project predicate

Phase 10 registers `Decidable` instances for `IsSparse k ℓ` (in the
matroidal regime `ℓ < 2 * k`), `IsTight k ℓ`, and `IsLaman`, each
backed by the polynomial-time pebble game `runPebbleGameExec`. The
project rule is: **each of these predicates carries exactly one
canonical `Decidable` instance, the pebble-game-backed one.** Do not
register a second `Decidable` instance for the same predicate, even if
it would type-check.

This is a project-internal *convention* rather than a Lean-level
constraint. Typeclass search picks one of the registered instances by
its own priority logic, and many of these predicates admit multiple
type-correct decision procedures:

- `IsSparse k ℓ` unfolds to
  `∀ s : Finset V, ℓ ≤ k * s.card → (G.edgesIn s).ncard + ℓ ≤ k * s.card`.
  Under `[Fintype V]` plus the appropriate decidable-equality and
  edge-count decidability, this is **brute-force decidable** via
  `Fintype.decidableForallFintype`, iterating all
  $2^{|V|}$ vertex subsets.
- `IsLaman` and `IsTight` are conjunctions of such predicates with a
  decidable arithmetic equation, so they inherit the brute-force
  reduction.

Both the pebble-game instance and the brute-force instance produce a
valid `Decidable` of the same `Prop`; they differ only in the
*reduction body* — what `decide` / `#eval` / `native_decide` actually
unfolds when asked to evaluate. The pebble-game body runs in time
polynomial in `|V| + |E|`; the brute-force body runs in time
exponential in `|V|`. Registering both as `instance` would silently
expose users to the slow path on any code that happened to trigger
typeclass-search priority in the wrong direction — a regression that
is hard to detect in normal code review and easy to introduce.

The project therefore registers **exactly one** canonical instance per
predicate and forbids competitors in the relevant source files'
docstrings. The canonical instances live in
`CombinatorialRigidity/PebbleGame/Exec.lean` and are:

- `SimpleGraph.instDecidableIsSparse` — under
  `[Fact (ℓ < 2 * k)]`, reduces to
  `(runPebbleGameExec G k ℓ h_matroidal.out).isAccept` via the
  verdict-form correctness theorem
  `runPebbleGameExec_isAccept_iff` (Phase 11 Layer 4b absorbed
  Phase 10's `runPebbleGameExec_correct` certificate-form iff into
  the verdict's return type).
- `SimpleGraph.instDecidableIsTight` — conjunction of the
  `IsSparse` instance with a `Nat`-equality check on the edge count.
- `SimpleGraph.instDecidableIsLaman` — specialisation of
  `IsTight` at $(k, \ell) = (2, 3)$.

The pebble game requires the matroidal regime `ℓ < 2 * k` (Phase 7's
hypothesis, threaded through Phase 9's correctness theorem); the
`IsSparse` instance therefore takes a `[Fact (ℓ < 2 * k)]` typeclass
hypothesis rather than an unconditional registration. The blueprint
explainer for the runtime / backend matrix (`#eval` / `lake exe` /
`by decide` / `native_decide`) lives in
`blueprint/src/chapter/executable.tex`
*Runtime and backends* and is the user-facing version of this
rationale.

If a future predicate genuinely needs a competing `Decidable` body
(e.g., a faster specialised algorithm), the right shape is a single
`Decidable` instance whose body branches on the concrete shape of its
inputs — not two separately-registered instances racing for typeclass
priority.

---

## Panel-hinge = hinge-coplanar body-hinge: the coplanarity layer (Phases 21–26)

**The gap (found 2026-06-03, mid-Phase-21).** The Molecular Conjecture
is a statement about *panel-hinge* frameworks, and a panel-hinge
framework is **not** a primitive object. Per Katoh–Tanigawa 2011
(p.647), a body-hinge framework `(G,p)` — `p` assigning each edge a
free `(d−2)`-affine subspace — is **hinge-coplanar** when, *at every
vertex `v`, all hinges incident to `v` lie in a common hyperplane*; a
hinge-coplanar body-hinge framework *is* a panel-hinge framework. The
conjecture (KT Conj 1.2) is exactly that body-hinge rigidity ⟺
panel-hinge rigidity — i.e. the coplanarity constraint can be met
without losing rigidity — and that is the **entire difficulty**: KT
prove it by directly constructing coplanar (panel) realizations through
the §5–6 induction, with *no* body↔panel equivalence shortcut (the
Crapo–Whiteley projective duality is used only for the *molecule*
application, relating panel-hinge to hinge-*concurrent* body-hinge, not
for the general theorem; KT p.648).

Our Phase-18 `BodyHingeFramework` models the free (body-hinge) `p` with
no coplanarity; `RankHypothesis` / `thm:theorem-55` as first drafted
quantify over free realizations. As such they state the **body-hinge**
rank theorem — by Prop 1.1 essentially the Tay–Whiteley + Phase-19
`def=corank` result already in hand — not the molecular conjecture. The
conjecture's defining constraint was absent from the formal statement.
(Not previously in the risk register; a genuine oversight, now risk #7
in `notes/MolecularConjecture.md`.)

**Decision: add a panel layer; reuse all rank infra.** The panel-hinge
regime is *additive* over the existing rigidity-matrix machinery, which
is regime-agnostic (a fact about a given `p`). Two forms were weighed:

- **(A) Predicate form.** Keep `hinge : β → …` free, add
  `IsHingeCoplanar F : Prop` (for each `v`, all incident hinge affine
  subspaces share a hyperplane), and have each construction *prove*
  coplanarity of the `p` it builds.
- **(B) Panel-data form (chosen).** Model a panel realization as
  **per-vertex hyperplanes** (the panel coordinates), with each edge's
  hinge *derived* as the intersection `panel(u) ∩ panel(v)`. This
  produces a `BodyHingeFramework` — so all Phase-17/18 rank infra
  applies verbatim — and is hinge-coplanar *by construction* (both
  hinges at `v` lie in `panel(v)`), discharging coplanarity structurally
  rather than as a per-case proof obligation. It is also the
  parametrization KT's genericity argument presumes (Claim 6.4:
  "entries are polynomials in the panel coordinates").

Form (B) is the primary route; `IsHingeCoplanar` survives as the *spec*
the panel constructor satisfies and as the predicate in which
`thm:theorem-55`/5.6 are stated (`∃ panels, RankHypothesis
(panelRealization panels) k'`). Form (A) alone is rejected as primary:
it neither gives the panel-coordinate parametrization for genericity nor
avoids reproving coplanarity in every case.

**What is reused vs. what changes.**
- *Reused verbatim* (regime-agnostic): `R(G,p)`,
  `Z(G,p)`/`infinitesimalMotions`, rank lemmas 5.1/5.2/5.3,
  `pinnedMotions`/`pinnedMotionsOn`, `withGraph` + monotonicity,
  `lem:case-II-rank-lift`. Each is a fact about a given `p`, and the
  produced panel realization is one.
- *Stays body-hinge*: `prop:rigidity-matrix-prop11` (KT Prop 1.1) — it
  *is* the body-hinge generic-rank statement; the molecular upgrade is
  that the panel realization also attains it (Thm 5.6).
- *Gains the panel requirement*: the realization-existence nodes —
  `thm:theorem-55`, `lem:case-I/II/III`, `lem:cycle-realization`, and
  the base case's "realization" form. Their *rank* content (where
  already green) is intact; assembly into Theorem 5.5 conjoins
  coplanarity / threads the panel constructor.

**Lemma 5.4 (cycle realization) is formalized, not cited** (user
decision 2026-06-03), as genuine panel content. A cycle's panel
realization with linearly independent hinge extensors is precisely the
Crapo–Whiteley projective fact (Grassmann-line-geometry independence of
the panel-intersection hinges), bottoming on Lemma 2.1 (Phase 17). It is
**its own sub-phase**: the panel layer (B) + the extensor *meet* algebra
for hinges-as-panel-intersections + a generic-panel independence
argument. This supersedes both the earlier cite-only call and the
(mistaken) free-hinge "telescoping is trivial" reduction recorded
mid-Phase-21 — that reduction proved only the *body-hinge* cycle
statement, which is too weak.

**The meet foundation (Phase 21a) and its construction chain.** Building
the panel layer (form (B)) and Lemma 5.4 both need the *supporting
extensor of `panel(u) ∩ panel(v)`* — the Grassmann–Cayley **meet**
(regressive product), the dual of the *join* Phase 17 built. mathlib has
neither a meet, a Hodge star, nor a top-power iso (its `exteriorPower`
surface is `Basic` / `Basis` / `Pairing` / `Grading` / `OfAlternating`
only), but it has the primitives. So the meet is its own **foundations
sub-phase, Phase 21a** (the dual sibling of Phase 17), scoped to the
**regressive product only — no metric Hodge star** (projective geometry
is metric-free; only an orientation / top-power volume form is needed).

The decisive structural fact: on `V = ℝ^(k+2)` the irreducible new piece
is a single iso, `complementIso : ⋀ʲ V ≃ ⋀^(N−j) V` (`N = k+2`). With it
and Phase-17 `join`, a panel is a normal vector `nᵥ ∈ V` and
`supportExtensor(e) = complementIso(nᵤ ∧ nᵥ)` (join, grade 2 →
`⋀^(N−2)V = ⋀ᵏV = ScrewSpace k`), with **transversal ⟺ `nᵤ ∧ nᵥ ≠ 0` ⟺
the normals independent** — so coplanarity and the only general-position
condition both live in the extensor algebra, and no affine-subspace
intersection plumbing is needed. The abstract `meet` is then a thin layer
(`meet = complementIso⁻¹ ∘ join ∘ (complementIso × complementIso)`).

`complementIso` is built by **route (ii)** (chosen 2026-06-03 over the
combinatorial `e_S ↦ ±e_(Sᶜ)` route, for the Phase-25 payoff), via the
duality pairing, in dependency order:

1. `topEquiv : ⋀ᴺ V ≃ R` — canonical via the standard basis
   (`Module.Basis.exteriorPower (Pi.basisFun)` + `exteriorPower.finrank_eq`).
   Mirror lemma (mathlib has only `zeroEquiv` / `oneEquiv`).
2. `pairingDualEquiv : ⋀ʲ(V*) ≃ (⋀ʲ V)*` — upgrade mathlib's
   `exteriorPower.pairingDual` (a bare `→ₗ`) to an iso via its dual-basis
   lemmas. Mirror lemma. **This is the projective-duality dictionary entry
   Phase 25 reuses — the reason route (ii) was worth the extra abstraction
   over route (i).**
3. `complementIso` — from the perfect wedge pairing
   `⋀ʲ V × ⋀^(N−j) V → ⋀ᴺ V ≅ R` (via `join` + `topEquiv`), nondegenerate
   for free `V`. The genuinely new core.
4. `meet` + `meet_ne_zero_iff` + the geometric reading above.

Items 1–3 are general free-module facts → mirror directory
(`CombinatorialRigidity/Mathlib/LinearAlgebra/ExteriorPower/…`), natural
mathlib-PR candidates. Detail + checklist: `notes/Phase21a.md`.

Cross-refs: KT 2011 pp.647–649 (definitions), §5–6 (the panel
induction); `notes/MolecularConjecture.md` risk #7 + Phase-21/21a detail;
`notes/Phase21.md` *Decisions / Hand-off*; `notes/Phase21a.md`.

---

## Genericity device (Claim 6.4/6.9) is its own sub-phase (Phase 21b)

**The device.** KT's algebraic induction rests on one analytic crux,
their Claim 6.4 (and its Case-II twin Claim 6.9): the entries of the
panel-hinge rigidity matrix `R(G,p)` are polynomials in the
algebraically independent panel coordinates, so the rank is a lower
semicontinuous function that attains its maximum on a Zariski-open
(generic) set; hence a *single* good realization at the target rank
lifts to a *generic* realization at that rank. This is the
rank/dimension-count argument that every "place the pieces, then make
them generic" step in §5–6 invokes. It is shared, verbatim in spirit,
by `lem:case-I` (block-triangular gluing of a contraction + a pinned
rigid block), `lem:case-II` (the 1-extension's `+D` rank lift,
discharging `hspan`), `thm:theorem-55` (the induction conjoins the
per-case generic realizations), `prop:rigidity-matrix-prop11` (the
generic-rank = `D(|V|−1) − def` reconciliation, JJ 2009 Thm 6.1
geometric side), and `lem:cycle-realization` (the projective assembly
of the cycle's independent extensors into one rigid realization).

**Decision (2026-06-03): scope the device OUT of Phase 21 into a
focused sub-phase, Phase 21b** — the analytic sibling of the Phase-21a
meet sub-phase. Phase 21 closes on the **genericity-free content**: the
per-case reductions are formalized in full, with the genericity device
entering each remaining node as an **explicit cited input / black-box
hypothesis**. The surrounding reductions are then *fully formal modulo
that one device*, exactly as `lem:cycle-realization`'s four Lean pieces
already sit around its cited projective assembly. This is the same
move that worked for the meet (21a): isolate the one genuinely new,
shared, hard ingredient as its own dependency-ordered sub-phase rather
than re-deriving it inline in four places, and let the consumers cite
it.

**Why a sub-phase and not inline.** The device is (i) *shared* by four
nodes — proving it once and citing it avoids four parallel
rank-count derivations; (ii) *genuinely new analytic infrastructure*
(the panel-coordinate parametrization + a generic-max-rank /
lower-semicontinuity argument over it), large enough to warrant its
own forward-mode chapter and notes file; and (iii) *separable* — the
non-genericity reductions (graph ops, block-pin accounting,
edge-substitution bridges, the `hnew`/`hspan` reduction) are
self-contained and already mostly green, so closing Phase 21 on them
does not wait on the device.

**Contract for Phase 21's remaining nodes.** Each red node
(`lem:case-I`, `lem:case-II`, `thm:theorem-55`,
`prop:rigidity-matrix-prop11`) is to be stated/closed with the
genericity conclusion supplied as a named hypothesis or cited lemma
(the Phase-21b deliverable), so that the node is GREEN-modulo-21b: its
Lean either takes the device's conclusion as an input or `\uses` the
forthcoming 21b node. The node-by-node split — what each needs *from*
the device vs. what is genericity-free and formalized in Phase 21 — is
in `notes/Phase21.md` *Hand-off*. `lem:case-III` is unaffected (it was
already deferred to Phases 22–23, where the device is also consumed).

**What Phase 21b will contain (scoped at open).** The panel-coordinate
parametrization of `R(G,p)` (entries as polynomials in the per-vertex
normals), the generic-max-rank lemma over that family (rank lower
semicontinuity / a Zariski-open attainment argument — assess on
contact whether the Phase 6/8 Gram-det perturbation machinery transfers
or a fresh polynomial-rank argument is needed), and the discharge of
each consumer's cited hypothesis (`hspan` for Case II, the
block-triangular generic gluing for Case I, the cycle projective
assembly for `lem:cycle-realization`, the generic-rank reconciliation
for Prop 1.1). Its own notes file `notes/Phase21b.md` and blueprint
section open when the sub-phase starts.

Cross-refs: KT 2011 §6.1 (Claim 6.4), §6.3 (Claim 6.9), Lemma 6.3;
Jackson–Jordán 2009 Thm 6.1 (the Prop 1.1 analytic side);
`notes/MolecularConjecture.md` risk #4/#7 + Phase-21/21b detail;
`notes/Phase21.md` *Hand-off*.

---

## Forward-mode reduction chains: build the keystone first

**The trap.** Forward mode's natural cadence is "one dep-graph node = one
commit = one lemma." That is right when nodes *fan out* and get reused. It
goes wrong when the work is a **linear reduction** — a goal you discharge
one hypothesis at a time. Formalizing each hypothesis-discharge as its own
public lemma then produces a *telescoping chain of single-use wrappers*:
each lemma has exactly one caller (the next link), a 1–6 line proof, and a
large signature, and the chain accretes a new public theorem (with a
blueprint pin and a multi-paragraph docstring) per commit. Phase 21b's
Case-I `hglue_* → hasFullRankRealization_*` stack (≈9 wrapper links + the
`hblock`/`hpin` leaves) is the worked example; the blueprint mirrored it,
cramming a 14-name `\lean` pin onto `lem:genericity-device` and narrating
raw Lean identifiers in `lem:case-I`'s prose.

**Two compounding failures.** (1) *Single-use shims dressed as API* — use
`have`/`obtain` inside one theorem, or the `@[deprecated … (since :=
"narrative-bridge")]` shim pattern (see `CombinatorialRigidity/CLAUDE.md`),
not a named public lemma per step. (2) *Scaffolding ahead of its consumer*
— the chain reduced Case I to "a geometric construction" that itself
needed the (unbuilt) keystone device, so the wrappers were shaped against a
*guessed* final consumer and several became dead weight.

**The rule.** When the remaining work is a linear reduction onto one hard
**keystone** (here: the genericity device), build the keystone — or at
least pin its honest target statement and validate the consumer API against
it — *before* growing the reduction chain. Then collapse single-use steps.
Diagnose early: if a phase is emitting one thin wrapper lemma per commit and
every hand-off says "the real work is still ahead," that is the smell.

**Blueprint corollary.** In forward mode the dep-graph *is* the plan, so a
chain of wrapper-shaped Lean lemmas is usually a symptom that the
*blueprint's* decomposition is the unnatural one. Fixing the blueprint to
the honest mathematical decomposition (few genuine nodes, prose as math, no
Lean identifiers) is causal, not cosmetic — it redirects the formalization.
Cross-refs: `notes/Phase21b.md` *Hand-off*; the 2026-06-04 honesty flip
(commit `ad7cb0d`).

---

## Realization motive must be V(G)-relative, not absolute over the ambient type

**The trap (found 2026-06-04, Phase 21b).** A *realization* theorem proved by
an induction that **reduces the vertex count** must carry its motive **relative
to `V(G)`**, never as an absolute property of the whole ambient body type. The
molecular `theorem_55` carried infinitesimal rigidity as the absolute
null-space equality `dim Z(G,p) = D` over all of `α → ScrewSpace`. That equals
rigidity only when `G` *spans* `α`: a body in `α ∖ V(G)` sits in no hinge
constraint, so it is a free non-trivial motion and `dim Z > D`. But
`minimal_kdof_reduction` reduces to subgraphs with strictly fewer vertices on
the *same fixed* `α`, which do not span it — so the absolute motive is
**unsatisfiable** for every inductive subgraph, and the case-producer premises
(`hbase`/`hsplit`/`hcontract`) cannot be discharged for `card α ≥ 3`. The
capstone was green only as a conditional over unsatisfiable hypotheses; the
symptom was a base-case hypothesis `∀ w, w = u ∨ w = v` (i.e. "`α = {u,v}`").
Verified in Lean by a one-line lemma: an isolated body yields a non-trivial
motion, so a non-spanning framework is never (absolutely) rigid.

**The rule.** Carry such a motive in an `α`-independent form. For a rank/rigidity
motive, the **rank form** `rank R(G,p) = D(|V(G)|−1)` — equivalently
`finrank (span rigidityRows) = D·(|V(G)|−1)`, equivalently "every infinitesimal
motion is constant on `V(G)`" — is `α`-independent (the rigidity rows come only
from `E(G)`, so isolated bodies contribute nothing), composes through the
induction, and (bonus) makes the block-constancy machinery satisfiable (it was
vacuous only because of the global-`α` rigidity). The dual nullity form
`dim Z = D` is the special case `V(G) = α`.

**The general lesson.** When a producer/existence statement is proved by a
size-reducing induction, check that its motive is satisfiable for the *reduced*
instances, not just the top one — and prefer a formulation intrinsic to the
object (`V(G)`) over one referencing a fixed ambient (`α`). This is the
producer-scrutiny honesty gate (`blueprint/CLAUDE.md`) applied to the *motive*,
not just to a single node's hypotheses. Cross-refs: `notes/Phase21b.md`
*Current state* + *Decisions*; the 2026-06-04 realization re-plan.

**Corollary — a standing hypothesis needs a satisfiability witness, not just
green consumers (Phase 22h G5, 2026-06-09).** The same trap one level up: a
*hypothesis* every consumer takes as given is never checked satisfiable by a
green build. `IsProperRigidSubgraph` transcribed KT p. 659's `1 < |V′|` as
`V(H).Nonempty`; a single vertex is vacuously `0`-dof, so the Case-III layer's
standing `hnoRigid : ∀ H, ¬ H.IsProperRigidSubgraph G n` was **unsatisfiable**
for `|V(G)| ≥ 2` — and four phases of conditional theorems built on it stayed
green (the §1.49 design pass caught it with a one-line `lean_run_code` witness,
`Graph.noEdge {u} β`). The rule: when a branch hypothesis *quantifies over* a
transcribed definition ("no X exists", "every X satisfies …"), (a) re-verify
the transcription against the primary source's exact inequality, and (b)
exhibit a satisfying instance of the hypothesis the first time a phase
consumes it — a one-line witness is cheap; churn on a vacuous branch is not.

## Constructibility recon before scheduling a producer build

**The trap (Phase 21b, 2026-06-04; four re-plans).** A realization/existence
producer was scheduled commit-after-commit as "build-shaped" by reasoning about
**node names and types** — "feed N7b-2's transport to the glue N7a" — and the
gap only surfaced mid-build, when a subagent checked whether the conclusion was
actually *constructible* from the inputs. The hard kernel (KT's eq. (6.12)
rank-lift) got relocated four times (N7b-4 e₀-recovery → motion-side M1/M2/M3 →
…) before a math-first pass found the producer was **one row short by an
arithmetic that fits on one line**: the device gives `+(D−1)` rows, the k=0
target needs `+D`. The shortfall was visible from the start; the dep-graph
(type-correct, honesty-gate-clean on hypotheses) was blind to it because no node
checked the *count*.

**The rule.** Before scheduling a producer/existence node (`∃ realization`,
`HasFullRankRealization`, "attains rank `r`") as a *build* commit, run a
**constructibility recon**: trace the conclusion's target quantity (rank, count,
dimension) through the intended construction and confirm the arithmetic
**closes** — not that the `\uses` edges type-check. If the source (KT) states
the step in a few lines, that compression usually *is* the content; expand it to
a complete gap-free argument (against the primary source + the rigidity
literature) *before* decomposing into Lean nodes. Decompose-then-build is right
only when the math is settled (Phases 1–20); when the math is the hard part
(KT §6 realization layer), invert the order. This is the operational gate added
to `blueprint/CLAUDE.md` (the honesty gate's second half: "is the obligation
discharged" covers laundered hypotheses; this covers an invalid/short proof
step). Cross-ref: `notes/Phase21b.md` *Finding A/B*; `notes/FRICTION.md`
*[process] producer constructibility*.

**Corollary — a recon that restates a node's shape must also trace its
hypotheses' discharge (Phase 22g, 2026-06-09).** The constructibility recon
above traces a *count*; this one traces a *carried hypothesis*. When a recon
fixes a green-modulo node's *shape* — its conclusion, or a carried hypothesis it
restates — confirming the restated form *type-checks* is not enough: trace each
load-bearing hypothesis to a concrete discharge at the real instantiation, or
confirm it is a `by_contra`-internal assumption that is never supplied. Phase
22g's first realization recon fixed `case_III_claim612`'s *conclusion* (the
join side) but never traced whether its carried `hduality` could be discharged;
five graph-free leaves were then built on a premise that was dimensionally
**undischargeable** (`hann ⟹ r̂ = 0` for `r̂ ≠ 0`), all off-route once a later
recon traced the discharge. **The tell:** a carried hypothesis that forces the
very nonzero object the lemma is about (here `r̂`) to vanish — it can only ever
live inside a `by_contra`, so a node that takes it as a *supplied premise* is
mis-shaped. Skipping the discharge-trace re-incurs this section's churn one level
up: at the *hypothesis* rather than the *count*.

**Corollary — trace the producer's WIRING, not the green lemmas' statements; a
re-route must re-verify every other obligation (Phase 22g, 2026-06-09).** A
producer-node recon that checks the green inputs' *statements in isolation* —
"`hsplitGP` consumes the GP IH, `case_III_realization_of_line` concludes
full-rank" — repeatedly misses *interaction* holes that only a trace of the
actual producer/IH wiring exposes: what each hypothesis literally is, where it
is sourced, and what the *output type* demands. Phase 22g's three high-level
recons declared "no research-shaped node remains"; tracing the wiring then
surfaced, in succession, that the producer's points needed an affine
de-homogenization (R1-affine), that the triangle-rigidity brick is exactly tight
not a circuit (it dissolved), that the `|V|=3` split graph is reachable and
non-simple (a genuine base-case hole), and that the producer's output conjunct
`AlgebraicIndependent ℚ` clashes with its degenerate seed (GAP 2, resolved by an
existential upgrade). **And the sharpest tell:** when a later recon *dissolves*
one of these by *re-routing* — changing which IH conjunct / hypothesis the
producer consumes (§1.46: "take the bare `.2`, not the generic `.1`, so split
simplicity is never needed") — it must re-verify that the producer's **other**
carried obligations still close under the new route. §1.46's re-route orphaned
`hgab` (the split-leg transversality only the discarded `.1` conjunct supplied,
still required by the candidate placement and by GAP 3's good-`t`); the
"dissolution" did not close. Trace the route end-to-end *each time the route
changes*, not just the node that changed.

**Scale-up: design the LAYER, not just the node (Phase 22, 2026-06-04).** Per-node
constructibility recon is necessary but not sufficient when an entire *layer* of
interlocking producers shares an invariant. Phase 22's Case-I seed was recon'd
node-by-node for ~10 commits — each recon honestly pruned a *local* dead-end (the
moment-curve over-specialization, the forest-row over-count) — yet the binding gap
was structural and invisible to all of them: the shared induction **motive**
`HasFullRankRealization` was too weak (it produced a *bare* rigid realization where
every producer needed a *general-position* one — KT Thm 5.5's "nonparallel, if
simple" conjunct the project had silently dropped). No single node's arithmetic
exposed it, because it is a property of the shared invariant, not of any one
construction. A one-commit **layer design pass**
(`notes/Phase22-realization-design.md`) — read the whole producer family against
the primary source, asking "what does each producer need *from* the motive and
supply *to* it" — surfaced it at once and bounded the rest of the layer. **The
rule:** when a research-shaped producer layer shares a motive/invariant (KT §6's
Cases I/II/III against the realization motive), run that layer-level design pass
*before* the first producer build, not after the per-node recons hit a wall.
Per-node recon catches local short-by-one-row gaps; only the layer pass catches a
too-weak shared invariant. Cross-ref: `notes/Phase22-realization-design.md`;
`notes/Phase22a.md` *Decisions*.

**Verify the recon's load-bearing claims, don't assert them (Phase 22b U3b,
2026-06-05; two recon corrections).** The U3b node was recon'd twice and *both
recons were wrong at their crux* before a third converged: §1.19 declared U3
"plumbing / green-reuse"; §1.21 declared it "a bounded one-line Lemma 5.1
corollary." Neither was short on prose — each named the right bricks and sketched a
plausible layer. They failed because the **load-bearing claim was asserted from
intuition, not checked against the live artifact**, then dressed in confident
scoping words ("retired", "plumbing", "bounded", "no wall") that propagated false
confidence to the next commit:
- §1.19 called U3 *green-reuse* without checking that the reused tool's **output**
  matches the consumer's **required input**:
  `exists_independent_panelRow_subfamily_of_rigidOn_linking_set` produces
  *un-projected* independence, but the composer needs the *projected*
  (`extProj`-dualMap) rows — and projection can drop rank. A **consumer-fit** check
  (write both shapes, confirm they match) catches it in one line.
- §1.21 asserted `finrank Z = D` from "rigid ⟹ trivial-only motions", without
  checking *which set* the rigidity is over: `Qcf'` is rigid on its vertex set
  `sc ⊊ α`, and the exact lemma `finrank_…_vertexSet` gives `D(|scᶜ|+1)`. A
  **quantitative-claim-vs-exact-lemma** check catches it.

**Diagnosis (answering "are we going into enough detail?"): the gap is not detail
*volume* — it is *verification of the crux*.** The recons that held (§1.16 traced
against the engine signature; §1.22 against the live finrank lemmas + mathlib dual
API; the coordinator's from-scratch motion-space decomposition) were grounded in the
artifact; the ones that failed were grounded in memory of "how rigidity works."
**The rule:** a recon may use a feasibility verdict word ("bounded", "green-reuse",
"no wall", "plumbing", "retired") only for a claim it has *checked against ground
truth*, and must say how — otherwise label it "asserted (unverified)". Two cheap,
mandatory checks at every recon crux:
1. **Consumer-fit.** For any "it's just lemma `X`" claim, write `X`'s conclusion and
   the consumer's required hypothesis side by side and confirm the *shapes match*
   (not just that the `\uses` edges type-check). **This check fires at *write time*,
   wherever the claim is written**: a docs-only feed assertion (`hX := lemma_L` in a
   design-doc checklist or hand-off) is a recon crux even when no build is being
   scheduled — it will be consumed as settled fact by a later builder. Calibration
   (Phase-22h postmortem): §1.41(5) asserted `hcontractGP := case_I_realization` in
   a docs pass four days *after* the signature (with its `hcSimple` case hypothesis,
   two lines above the binder the same pass quoted) had landed; one side-by-side
   would have caught it, and it instead survived to the §1.54 feed audit.
2. **Quantitative against the exact lemma.** Any finrank/rank/dimension/count
   equality cites the *exact* lemma yielding it — with its real hypotheses
   (vertex-set vs `α`, `≤` vs `=`) — or is derived from first principles.

Recon at *build fidelity*: read the actual signatures and derive the actual counts,
the way the build would — a from-memory sketch is not a recon. (The build-attempt
subagents caught §1.19/§1.21 precisely because building *forces* this fidelity;
doing it at recon time avoids the churn.) Cross-ref:
`notes/Phase22-realization-design.md` §1.19/§1.21 (the wrong recons) → §1.22 (+
coordinator verification); `notes/Phase22b.md` *Discharge plan*.

**Sharpening: recon the *quantifier domain* of a brick's hypotheses, not just its
conclusion shape (Phase 22, 2026-06-04).** The N6b coupling was projected as a clean
assembly of green bricks because the bricks' *conclusion types* lined up. But the
per-leg producer `exists_rankPolynomial_of_rigidOn` carries a hypothesis
`hends : ∀ e : β, G.IsLink e …` quantified over **all** of `β` (every edge label of
the realized graph must link — the panel rows must span all rigidity rows), which a
*proper-subgraph* leg `GH ≤ G` does not satisfy, and the `IsLink` subgraph direction
is the wrong way to derive it. The type-level "feed the bricks together" plan was blind
to the hypothesis *domain*. **The rule:** when recon'ing whether a producer is a clean
assembly, read each consumed brick's *hypothesis binders* (especially `∀`-domains:
over the ambient type vs. over a subobject) against the actual inputs the assembly
supplies — a conclusion-shape match is necessary but not sufficient. Cross-ref:
`notes/FRICTION.md` *[resolved] The Case-I N6b coupling is NOT a clean assembly …*;
`notes/Phase22a.md` *Decisions* / *Hand-off*.

**Sharpening: trace a producer's *actual output point*, don't assume it inherits a
seed's property (Phase 22a N6-G1a spike, 2026-06-04).** The generic-motive recon
scheduled N6-G1a as a multi-commit task to "re-expose the general-position witness
the genericity device drops" — on the premise that the device realizes at an
`ofParam` moment-curve point (which `isGeneralPosition_ofParam` would make GP). A
one-commit spike *traced the device's output through its call chain*
(`exists_good_realization_ofParam` → `exists_relative_full_count_ofParam` →
`exists_good_realization` → `exists_finrank_dualCoannihilator_polynomial`) and found
the output is an *arbitrary* non-root of a Gram-determinant `MvPolynomial`, **not** a
moment-curve point — so it carries no GP and there was no witness to re-expose. The
premise had reasoned from the device's *seed* (which is GP) to its *output* (which is
not). Tracing the chain surfaced both the false premise and the *cheaper* real route:
realize at the GP seed directly, since the splice glue is genericity-free and already
gives rigidity there — collapsing the planned multi-commit build to one four-tuple.
**The rule:** before scheduling work to "recover/thread a property `P` of a producer's
output," confirm the *output point* actually has `P` by tracing the construction to
where the point is chosen — a seed's property does not automatically survive to a
generically-chosen output, and the survival question often reveals a shorter path.
Cross-ref: `notes/Phase22a.md` *Decisions* → *N6-G1 spike*;
`notes/Phase22-realization-design.md` §1.5 Route 2.

**Sharpening: a "rigid" framework's null-space dimension depends on rigid-on-*what*
— recon the *set* a rigidity hypothesis is stated over, not just the word "rigid"
(Phase 22b U3b build-recon, 2026-06-05).** The U3b recon (§1.21) projected the
pin-the-`r`-column rank-preservation as a one-line Lemma 5.1 corollary, reasoning
"`Qcf'` rigid ⟹ `finrank Z = D` ⟹ `finrank(pinnedMotions r) = 0` ⟹ projection loses
zero rank." The `finrank Z = D` step is the rigid-on-*all-of-`α`* count; `Qcf'` is
rigid only on its **vertex set** `sc ⊊ α`, where the green
`finrank_infinitesimalMotions_of_isInfinitesimallyRigidOn_vertexSet` gives
`finrank Z = D(|scᶜ|+1)` — the `D·|scᶜ|` free-isolated-body dimensions are still
present, so `finrank(pinnedMotions r) = D·|scᶜ| ≠ 0`. The clean conclusion survives,
but via an *exact free-column cancellation* whose real content is a block-pin count
(`finrank(pinnedMotionsOn V(H)) = D(|scᶜ|−|V(H)|+1)`), not a zero-rank-loss pin. **The
rule:** when a recon invokes "`X` is rigid, so `dim Z(X) = c`", read off *which set*
`X`'s rigidity is over and pick the matching count — rigid-on-`α` gives `D`, but
rigid-on-vertex-set gives `D(|Vᶜ|+1)`, and the isolated bodies do not vanish under a
column projection that only drops the graph's bodies. Same family as the N6-G1a "seed
property ≠ output property" trap above. Cross-ref:
`notes/Phase22-realization-design.md` §1.22 (corrects §1.21); `notes/Phase22b.md`
*Discharge plan* U3b.

**A realization motive must carry the selector invariants its consumers read — recon
what a "rigid realization" structurally *guarantees* before scoping a transport off it
(Phase 22b U3a build-recon, 2026-06-05).** The companion to the `V(G)`-relative rule
above. `PanelHingeFramework` carries a *free* endpoint selector `ends : β → α × α` with
no link-recording invariant, and the motive `HasGenericFullRankRealization k G := ∃ Q,
Q.graph = G ∧ Q.IsGeneralPosition ∧ Q.toBodyHinge.IsInfinitesimallyRigidOn V(G)` does not
add one — yet the framework's *motion space* depends on `ends` (the per-edge hinge
constraint `S u − S v ∈ span {supportExtensor e}` reads `supportExtensor e =
panelSupportExtensor (normal (ends e))`). The §1.20 U3a plan assumed an IH realization's
`Q.ends` "records its graph's links" so its rigidity could transport to a relabelled
selector (the `infinitesimalMotions_…_ends_swap` brick); but an arbitrary witness of the
motive can be rigid at a *pathological* `ends`, so the transport is not derivable and
`htransport` is not dischargeable from the present motive. The identical gap is already
*assumed undischarged* as the `H`-leg `hswap` conjunct of the composer's `hbundle`. **The
rule:** before scoping a brick as "transport leg `X`'s rigidity to selector `Y`", check
that the motive supplying `X` actually *guarantees* `X`'s selector records its graph's
links (or whatever invariant the transport reads) — a bare `∃ rigid realization` usually
does not, and the fix is a motive strengthening (a structural, multi-node edit re-typing
every producer), not a leaf commit. Cross-ref: `notes/Phase22-realization-design.md`
§1.23 (corrects §1.20's "alignment RESOLVED in principle"); `notes/Phase22b.md`
*Discharge plan* U3a + *Blockers*.

**Corollary — when a hard core is sliced as "conditional leaf + hypothesis the
consumer discharges", verify the hypothesis is SATISFIABLE for the actual
consumer object before landing the leaf (Phase 23c, 2026-06-22).** A hard
membership/rank step is often packaged as a *true conditional lemma*
`(hyp) → goal` whose `hyp` the consumer supplies later — a legitimate slice, but
only if `hyp` is dischargeable for the consumer's *actual* object. Phase 23c
landed **two** correct-but-mis-targeted `±r`-row leaves this way: the off-slot
GROUP leaf's `htransport` (a surviving genuine off-`{e_c,e_r}` link at the
relabelled endpoints) and the reproduced-slot leaf's `hcollapse` (a full-row
collapse of the *filtered* edge-group) are each **unsatisfiable** for the arm's
real `±r` row — the chain-edge endpoints relabel to the candidate's *reproduced
slot* (not an off-slot link), and the filtered group has *column-only* machinery
(no single-row collapse; only A-1's *full* combination collapses). Both leaves
type-check, pass gates, and match the pinned signature — the gap is purely that
`hyp` cannot be produced for the real consumer. **The check** is the L5b
consumer-grounding rule (settle a route against its consumer) applied at the
*hypothesis* level: before pinning/landing such a leaf, name the consumer's
actual object and confirm `hyp` holds *for it* — a satisfiability trace, not a
signature/decl-existence check (both `±r` leaves passed the latter). The tell: a
leaf whose hypothesis silently re-encodes the hard content the slice was meant to
make progress on (here, the KT eq-(6.66) redundancy-membership) — the
"abstraction defers the crux" anti-pattern, surfaced only when the consumer (the
arm) is finally built. Cross-ref: `notes/Phase23-design.md` §(o‴)(I.8.24)(4.7)–(4.8);
model-exp *Findings* 2026-06-22.

**Corollary — the satisfiability trace must hit the cert's SHAPE/architecture, not
only a leaf's hypothesis; a *sound* kernel lemma can be unsatisfiable for the real
object and hide for many leaves (Phase 23d, 2026-06-25).** Route A's general-`d` rank
cert was architected on A3 — `Matrix.rank_fromBlocks_zero₂₁_ge_of_linearIndependent_rows`,
a *true* lemma (`#m₁+#m₂ ≤ rank` for a block-triangular `fromBlocks A B 0 D` with both
diagonal blocks full-row-LI). It was accepted as the kernel and **~13 leaves were built
on it** (the column op, the product/edge matrices, the rank bridges, the cert), each
gate-clean. Only at the `hblock` assembly did a spike find the cert's `fromBlocks` SHAPE
— a **total** row bijection `em : rows ≃ m₁ ⊕ m₂` with both blocks full-row-LI — is
**unsatisfiable for the real isostatic arm at `D ≥ 3`**: the `D−2` surplus `v`-incident
rows are pure-`v`-column after the op, breaking both the `0` block (`toBlocks₂₁ ≠ 0`) and
the bottom-block LI (`hD`). KT's (6.64) is a *subspace* statement (surplus rows ignored,
via `mkQ`); the matrix cert's total-partition `fromBlocks` is a strictly stronger shape
demanding the WHOLE edge matrix be full-row-rank — false. The fix is a row-SUBMATRIX /
injection reshape of the kernel (`em : m₁ ⊕ m₂ ↪ rows`, ignoring the surplus; ~2–3
leaves, cert-kernel-local). **The rule:** when a recon accepts a *kernel/architecture*
lemma whose shape the whole sub-phase will instantiate, run the satisfiability trace on
the SHAPE against the real object (does a TOTAL partition / full-row-rank / exact-count
actually hold for the actual instance?), not just on individual leaf hypotheses — a
sound-but-too-strong-shaped kernel costs the entire tower built on it. The cheap guard:
at kernel-acceptance, instantiate the shape on the real object's *dimensions* (here:
isostatic `(D−1)|E| = D(|V|−1)`, corner holds `D` of `2(D−1)` `v`-rows ⟹ `D−2` surplus)
and check the partition closes. Cross-ref: `notes/Phase23-design.md` §(4.33); model-exp
*Findings* 2026-06-25.

**Corollary — the too-strong shape can RE-ENTER at the *leaf proof-method* level after the
kernel is reshaped to tolerate the weaker shape (Phase 23f, 2026-06-26).** The corollary above
reshaped the cert *kernel* from a total `fromBlocks` partition (bijection `em : rows ≃ m₁⊕m₂`) to a
row-injection (`re : m₁⊕m₂ ↪ rows`, dropping the `D−2` surplus). But the *leaves built to feed it*
(sessions #38/#39, leaves (ii)/(iv): `reindex_rowOp_isUnit_det` / `reindex_rowOp_submatrix_eq_fromBlocks_zero₁₂`)
silently drifted **back** to a bijection — their proof APIs (`Matrix.det_reindex_self`,
`submatrix_mul_equiv`) need a bijective middle `Equiv`, which re-imposes `card(m₁⊕m₂) = card p`, the
very equality the kernel was reshaped to drop. The leaf *conclusion types* were correct, gates +
sorry-grep + axiom-check all passed, and the abstract §(4.54) satisfiability spike type-checked the
bijection *vacuously* (abstract `m₁`/`m₂`/`p`); only reading the consumer cert's **actual**
`re : m₁⊕m₂ → p` (a general function, with `card(m₁⊕m₂) = D(|V|−1) ≤ (D−1)|E| = card p`) exposed
that no bijection exists generically — the leaves serve only the measure-zero isostatic-tight case.
The fix (B1/B2: `exists_rowOp_of_strictInjection` + `rowOp_strictInjection_submatrix_eq_fromBlocks_zero₁₂`)
carries the row op as a *block op on `range re` + identity on the complement* via the EXTENDED equiv
`(m₁⊕m₂) ⊕ (range re)ᶜ ≃ p`, and splits the product *entrywise* (`Fintype.sum_of_injective`), never
needing an `Equiv` middle index. **The rule:** when a kernel is reshaped to tolerate a *weaker*
structure (injection not bijection, `≤` not `=`, subset not partition), check that the *leaves built
to feed it* don't re-impose the stronger structure through their proof APIs — a leaf's conclusion
type can be correct while its proof METHOD (`det_reindex_self` / `submatrix_mul_equiv` / any
`Equiv`-requiring API) silently demands the `card`-equality the kernel dropped. **The tell:** a leaf
that takes an `Equiv`/bijection where the consumer's signature takes a plain function/injection;
instantiate the consumer's actual index types and compare cardinalities at acceptance — gates *and*
an abstract satisfiability spike both pass the too-strong leaf. Cross-ref:
`notes/Phase23-design.md` §(4.55); model-exp *Findings* / rows 518–520 (2026-06-26).

**Corollary — a *prior recon's* "~N-leaf gate fact via landed lemma X" rating is itself a
satisfiability claim about a BRIDGE; confirm X *produces* the carried fact's exact object before
accepting it, and re-spike at the consumer rather than trusting the settled prose (Phase 23d,
2026-06-25).** Route A's arm carries `hA`/`hD` (corner/bottom row-LI of the *operated row-submatrix*)
as hypotheses; a prior spike (row 473) "settled" them as "~1-leaf gate facts via the A5b LI iff /
`omitTwoExtensor` / the IH". A fresh compiler-checked spike at the arm assembly found that wrong by a
*granularity*: the A5b iff is for the FULL `rigidityProd.row`, not the column-operated, row-injected,
`v`-projected `toBlocks`; `omitTwoExtensor`'s LI lives in extensor space, not `toBlocks₁₁.row` — so each
needs a genuinely-new dual→matrix-row LI *bridge*, and a naive `whnf` on the carrier timed out
(200000 heartbeats), i.e. a blind build would have walled mid-proof. **The rule:** when a hand-off rates
a *carried* gate fact "~N-leaf via landed lemma X", that rating is a satisfiability claim about a bridge
— open X's *conclusion* and the carried fact's *exact object* and confirm X **produces** it (same row
family, same restriction/projection), not just that X is landed; if it is a route-composition in the
defeq-fragile zone, spike-before-build even though a prior recon "settled" it (the settling was at the
wrong granularity — a sound leaf-count estimate is not a sound bridge-existence proof). Cross-ref:
`notes/Phase23-design.md` §(4.34); model-exp *Findings* 2026-06-25 (rows 477–478).

## Match the source's argument structure, not just its conclusion

**The trap (Phase 22a, 2026-06-05; three undischargeable bridges).** The Case-I
realization producer stalled for three consecutive recon/fix passes, each producing
a hypothesis that type-checked and whose *arithmetic closed* but that was **not
dischargeable**: `hcrig` (each leg rigid on the *full* ambient `V`, unsatisfiable
for a proper subgraph) → `hpinc` (a placement-independent complement-isolation
*equality* `finrank(pinnedMotionsOn sc) = D·|scᶜ|`, **false** off a full vertex set —
the contraction leg's interior bodies carry surviving boundary-edge constraints) →
`htransportGP` (`∀` general-position seed ⟹ the leg is rigid, i.e. "GP implies
maximal rank", **false** — `IsGeneralPosition` is pairwise normal independence,
strictly weaker than full rank). Each pass took the green Phase-21b splice glue as
fixed and tried to satisfy *its* obligation; none questioned the glue. The root cause
sat one layer **below** the active nodes: the project formalizes rigidity as a
**motion-space predicate** (`IsInfinitesimallyRigidOn s` = every infinitesimal motion
is constant on `s`), and Phase 21b translated KT's **block-triangular rank-addition**
(eq. 6.3: `rank R(G,p) = rank R(G′,p₁) + rank R(G,p;E∖E′,V∖V′)`, each block at its
*own* leg-wise generic placement) into the motion-space **"overlapping rigid pieces
glue"** `isInfinitesimallyRigidOn_of_splice` (`F` rigid on `s_H` ∧ `F` rigid on `s_c`
⟹ `F` rigid on `s_H ∪ s_c`). These are **not the same argument**: the glue intersects
the motions of *one* framework `F`, so it demands a **single common placement on which
both legs are simultaneously rigid** — exactly what KT's block-triangular structure
never needs (KT builds the placement leg-wise; the ranks add). That common-seed demand
is the impasse, and the diagnostic tell was that **the arithmetic closed but every
pass needed a fresh hypothesis to bridge a gap the source does not have.**

**Why it hid.** The divergence was introduced as a *green* node (the glue) whose hard
half was *split out as a red sibling* (`lem:case-I-splice-placement`, "one `F`
realizing both legs") and mis-scored as "bounded assembly" at the Phase-21b
feasibility pass. Forward-mode discipline (build on green infra) then had every
downstream node build on the green glue's *assumed* shape, so the divergence stayed
invisible at the node level for a whole layer.

**The rule.** When formalizing a published proof, the formalization's **composition
lemma must reproduce the source's argument *structure*, not merely its *conclusion*
and *arithmetic*.** A locally-sound modeling choice (motion-space rigidity — correct
and successful for Phases 4–16, where a single generic placement suffices) can
silently re-express the source's argument as a *different* one with a different,
possibly intractable obligation. At the layer-design / constructibility-recon pass,
explicitly check: *does my composition lemma have the same shape as the source's*
(rank-addition over leg-wise placements vs. common-seed motion glue; matrix-rank-level
vs. null-space-level)? The arithmetic closing is necessary, not sufficient — a
composition that re-expresses the source's *key structural step* is a smell, not
routine assembly, even when its types and counts line up. **Corollary process rule**
(also in `blueprint/CLAUDE.md` *the honesty gate*): a green node that defers its hard
half as a red sibling must have that red half's feasibility **re-verified before
downstream nodes build on the green half's assumed shape** — "green-with-a-red-sibling"
is not "green". Cross-ref: `notes/FRICTION.md` *[process] Phase 22a — motion-space
splice glue vs KT block-triangular*; `notes/Phase22-realization-design.md` §1.12–§1.13;
`notes/Phase22a.md` *Decisions*. This is the sibling of *Constructibility recon …*
above (that gate catches a short-by-one-row count; this one catches a count that
closes over the *wrong structure*).

**Sharpening: a green-modulo residual quantified `∀` over a genericity class is
suspect (Phase 22a, 2026-06-05; four over-claims).** Even after the structure is
right, the *quantifier* on the deferred hypothesis is the next trap. Phase 22a's
realization residual was restated four times (`hcrig` → false `hpinc` → `htransportGP`
→ `hclaim64`-∀-GP), and the last two share a defect: they are universally quantified
over **general position** (`∀ q, GP(q) → …max rank…`), which requires "GP ⟹ maximal
rank" — false (GP is necessary, not sufficient; the *same-kind* sibling leg in the
very same proof gets its rank from a *rank polynomial*, not from GP). The source (KT
Claim 6.4) gives the rank "at the **generic** placement" — a Zariski-**open locus**,
i.e. the non-roots of a rank polynomial — **not** "at every general-position
placement". **The rule:** condition a green-modulo residual on the specific
Zariski-open locus the construction actually lands in (a rank-polynomial non-root,
intersected into the shared seed via the existing triple-product pattern), matching the
source's `∃`/open-locus genericity, never `∀`-over-GP. The tell that you over-quantified:
a *sibling object in the same construction* gets the analogous property from a
narrower condition (a rank-poly non-root) than you are demanding (all of GP) — an
unjustified asymmetry. Cross-ref: `notes/Phase22-realization-design.md` §1.16.

## A degenerate headline case is a target, not a template

**The pattern (the molecular general-`d` lift, Phase 23; surfaced sharply when the
owner asked "are we grounding the routes on what KT did?", 2026-06-20).** The
project formalized Katoh–Tanigawa at `d=3` first (Phase 22h) — the right call, since
`d=3` is the headline result — and then lifted to general `d` (Phase 23). The
single step that has cost the most churn (the Case-III candidate-transport / `hρGv`
slot, mis-pinned across sessions #10–#16: the `ρ²` over-shift, the "invert the fold"
refutation, the residue-link error, a clean-relabel temptation) is exactly the step
where **`d=3` is degenerate in the dimensions that matter**:
- the relabel cycle `shiftPerm 2 = (v₁v₂)` is a **single swap = involution**, so
  `(shiftPerm)⁻¹ = shiftPerm` and the entire base↔candidate *orientation* question is
  invisible;
- the redundancy transport is a **single** degree-2 `a`-column step (one residue), so
  the general `i−1`-step **telescope** is invisible;
- there is no multi-step over-shift to get wrong.

So the `d=3` engine (`case_III_arm_realization_M3`) is a faithful **target** but a
treacherous **template**: generalizing *its proof* rather than *KT's general
argument* repeatedly produced pins that are correct at `i=2` and wrong at `i≥3`.

**The compounding miss.** The transport was designed **bottom-up at the
Lean-scaffolding level** (the `shiftBodyFrameworkAsc` chain, `wstep`, the W9a/W9b
folds, the Fix-A/Fix-B fork) while the **KT row-operation anchor was deferred**. The
blueprint-clarity obligation explicitly flagged that KT's index-shift isos (6.54–6.56)
and ±r chain (6.66) must be materialized — but scheduled it for *phase-close*. So each
recon reconciled a *moving* scaffolding (the W9b chain was built then deleted; the
candidate→base folds built then orphaned) against **no fixed source referent**, and
the special-case intuitions filled the vacuum. The KT-faithfulness recon that finally
stabilized it (2026-06-20) found the redundancy transports by KT's degree-2 `a`-column
cancellation (eq. 6.44) iterated `i−1` times to `±r` (eq. 6.66) — which *is* the
`wstep` residue, so the fold was right all along, but that grounding arrived late,
after the churn.

**The rule.** When lifting a formalized special case to the general statement:
1. **Anchor the general design on the *source's* general argument, written down up
   front** — not on the special case's *proof*. A degenerate headline case supplies
   false intuitions precisely at the steps its degeneracy hides; the source's general
   argument (here KT's 6.44/6.66 row operations) is the only stable referent. If the
   blueprint/design defers that grounding, *pull it forward* — a fixed source anchor
   costs ~1 commit and saves the re-pinning churn (a crux step can otherwise eat parts
   of many sessions).
2. **De-risk every general transport leaf at the first *non-degenerate* case**, never
   the headline one — `i=3` (2 residues, a genuine cycle), not `i=2` (1 residue, an
   involution). Prescribing this is not enough; *execute* it before pinning the general
   signature (a Phase-23b build prescribed the `i=3` de-risk twice, then skipped it and
   bailed into a wrong-direction tangent).
3. **Don't let bottom-up Lean scaffolding lead the design of a crux.** Reconciling
   accreting scaffolding against itself, with the source anchor deferred, is how the
   same crux gets mis-pinned repeatedly. The sibling rule *Match the source's argument
   structure …* (above) is the same lesson at the *composition-lemma* grain; this one
   is at the *special-case-to-general* grain. Cross-ref: `notes/Phase23b.md`
   §(o‴)(I.7.7); `notes/BlueprintExposition.md` (`lem:case-III` general-`d`);
   `notes/model-experiment.md` rows 305–307.

## Phase Case-naming must match KT's k-bookkeeping

**The bug (Phase 21b, 2026-06-04).** The project labelled the reducible-vertex
degree-2 split "Case II" and scoped its realization to Phase 21b, but KT's case
structure keys on the dof `k`: **Case II (Lemma 6.8) is `k>0`** (the split drops
to `(k−1)`-dof and `+(D−1)` rows suffice for the lower target `D(|V|−1)−k`),
while the **`k=0`** split (KT Lemma 4.8(i): `G_v^{ab}` stays minimal `0`-dof,
full-rank target) is **Case III** — one row short via eq. (6.12), needing the
redundant-edge row of Lemma 6.10/6.13. The project's `theorem_55.hsplit` is
`IsMinimalKDof n 0` (k=0), so it is Case III; only Case I (proper rigid subgraph)
reaches full rank without the Case-III extra row. The blueprint `lem:case-II`
prose said "k>0" but was wired to discharge the k=0 `hsplit` — a conflation that
hid the difficulty.

**The rule.** When mirroring a source's case analysis, **pin each project node to
the source's case by the discriminating parameter** (here, the dof `k`), and check
the target/rank arithmetic matches that case — don't inherit a case name by
surface analogy ("it's a degree-2 split, so it's Case II"). Cross-ref:
`notes/Phase21b.md` *Finding B*; the top-level `CLAUDE.md` *Referencing prior
work* attribution bar (this is the rank-arithmetic analogue of verifying a §N
pointer).

## Narrowing an induction motive requires an IH-application census

**The bug (introduced 2026-06-04, surfaced 2026-06-10 as GAP 6, design
§1.50(b)).** KT state Theorem 5.5 / eq. (6.1) for **all** minimal `k`-dof
graphs; the project's `theorem_55` / `minimal_kdof_reduction[_full]` carry the
motive at `k = 0` only. Phase 21 opened (da68934) with the KT-faithful all-`k`
blueprint statement; the narrowing rode in a day later inside the (otherwise
unrelated) Phase-21b `V(G)`-relative motive re-plan (1ed6fed), justified by the
parenthetical "the general minimal `k`-dof statement is recovered the same
way" — plausible, top-down, and **backwards**: KT's Case-III interior applies
(6.1) to the *auxiliary* graph `G_v = G_v^{ab} − ab` — minimal `k'`-dof,
`k' ≤ D−2`, **not a child of the reduction** — at eq. (6.22) (KT p. 684), so
the `0`-dof proof *consumes* the all-`k` statement rather than subsuming it.
The narrowing *was* locally verified at the skeleton level (both reduction
arms preserve `0`-dof, KT Lemma 4.8(i)) — the audit that passed was simply not
the audit that mattered, because the leak is an IH application two lemmas deep
inside one case's interior. Missed catch-point: Phase 22d (2026-06-06)
*formalized the mismatch fact itself* (`splitOff_removeVertex_minimalKDof`:
`G_v` is minimal `k'`-dof) while its deferral note scoped the remaining work
as "applying the geometric IH to `G_v` at the fixed seed" — deferring an
application whose hypothesis (`G_v` in the motive's domain) was already
provably false in-repo.

**The rules.** (1) Before narrowing an induction motive from the source's
(all-`k` → `k = 0`, all-`d` → `d = 3`, …), **census every IH application in
the source's full proof tree** — including applications to auxiliary objects
inside case interiors — and check each target lies in the narrowed domain. The
reduction skeleton's children are not the complete list. (2) When scoping
deferred work as "apply X to Y", **verify Y satisfies X's hypotheses at
scoping time** — "apply the IH to `G_v`" hid GAP 6 for four days and six
sub-phases. Cross-refs: `notes/Phase22-realization-design.md` §1.50(b) (the
gap + resolution options); `notes/Phase22h.md` *Blockers* (adjudication
status); the sibling k-bookkeeping lesson above.

---

## Statement faithfulness to the source (the Phase-22h postmortem)

**The decision (user-adjudicated, 2026-06-11): the project's formalized
statements must match the source's strength — `HasFullRankRealization`
gets a genuine-hinge strengthening, scheduled at the all-`k` motive
redesign (the GAP-6 successor sub-phase), one redesign moment for both
changes.** This section is the canonical postmortem record for the two
gaps the §1.54 feed audit surfaced; the durable rules extracted from it
live at their own homes (pointer list at the end).

**Finding 1 — the vacuous bare motive.** `HasFullRankRealization`
(`PanelHinge.lean`) was born existential at Phase 21 (`1cd26cc`) as
induction rank-bookkeeping and was never checked against KT's
definition of "panel-hinge realization" (genuine hinges, nonzero
extensors): an all-zero-extensor *welded* framework (degenerate
selector `ends := fun _ => (a₀, a₀)`) satisfies it for every connected
graph, so the bare conjunct of the formalized Thm 5.5 was vacuous. It
survived three weeks because (i) the one re-design moment (22a's
two-motive split) re-read KT along a *different* axis
(nonparallel-vs-GP for simple graphs) and never posed the
cheapest-witness question; (ii) the blueprint *masked* the divergence —
`def:rank-hypothesis` carried `\leanok` with paper-strength prose; and
(iii) no gate compares a def's `Prop` body to its prose (the honesty
gate reads hypotheses; `checkdecls` reads names). Containment: the
weakness is isolated to the bare-motive family (`theorem_55`,
`theorem_55_d3`'s `.2`, the `.2` of `theorem_55_generic`); the GP
motive and the Phase 18–22 headline statements are KT-faithful, and the
producer layer's mathematics is real — a statement-selection weakness,
not an empty proof.

**Finding 2 — the orphaned Lemma-6.5 arm.** The 22a recon correctly
identified KT's 6.2/6.3/6.5 trifurcation and even named the right
tracking idiom (carry the case hypothesis explicitly), but the landing
commit reclassified the 6.3-vs-6.5 dispatch + 6.5 arm as "the
coordinator's wiring"; the green-modulo flip minted a red node for
Claim 6.4 only; 22a's close declared Claim 6.4 "the single deferred
obligation" — and the arm vanished from every forward list for five
sub-phases. §1.41(5) then asserted `hcontractGP := case_I_realization`
without a side-by-side against the landed signature (which had carried
`hcSimple` for four days). Of ~15 molecular-phase deferrals, 13 were
properly tracked; the two orphans are exactly the pieces of that one
"wiring" sentence. Diagnosis: rule-compliance failures (the honesty
gate, *Move deferred items*, consumer-fit) plus two genuine gaps, all
five now addressed:

- *Definition-faithfulness gate (cheapest-witness audit)* — new:
  `blueprint/CLAUDE.md` *Static checks*.
- *Case hypotheses are obligations, never ambient* — honesty-gate
  clause: `blueprint/CLAUDE.md` *Static checks*.
- *"Wiring" is not a deferral category* — `CLAUDE.md` *Move deferred
  items to where they will land*.
- *Consumer-fit fires at write time on docs-only feed assertions* —
  this file, *Constructibility recon → the two mandatory checks*.
- What worked (keep doing it): the recon-before-build trigger fired the
  §1.54 audit exactly on schedule, bounding the damage to re-planning —
  no Lean was built on either gap; and the checklist-pre-commit-diff
  rule (model-experiment row 46) is what queued the audit at all.

Scheduling rationale (why not strengthen immediately): the genuine-hinge
conjunct and the all-`k` restructure reshape the same defs, reduction
theorems, and bare producers; two passes would mean designing and
re-touching the motive surface twice — and this postmortem is a study of
what piecemeal motive design costs. 22h closes at its original scope with
the bare slots (`hbase`/`hsplit`/`hcontract`) *carried as named
hypotheses* (not discharged degenerately — the welded brick was cut as
pure throwaway once the strengthening was decided), proving the leaf
suite composes end-to-end before the redesign re-types it. Cross-refs:
`notes/Phase22-realization-design.md` §1.54–§1.55; `notes/Phase22h.md`.

## Frozen contracts must encode the invariants relating their parameters (the Phase-23c LEAF-3 postmortem)

A multi-field contract (here the `ChainData` record + the CHAIN↔ENTRY
dispatch signature, frozen as C.0–C.6 in 23b) must **formalize the
structural relations between its parameters**, not just document them in
prose. The `ChainData` record carried both the chain length `d` (a free
`ℕ`, `hd : 1 ≤ d`) and the ambient dof-regime index `n` (with
`bodyBarDim n = screwDim k`, i.e. `n = k+1`), and its field docstrings
*named* the relationship — `d` is "the body-bar dimension index", `n` "the
`k`-dof regime … **no field references it**". But the identity KT's Case III
forces — `d = n` (chain length = ambient dimension; KT 2011 Lemma 4.6
"chain of length `d`" + Prop 1.1 `D = C(d+1,2)`, so `d = k+1`) — was left
out of the formal contract to keep the record minimal. The contract thus
recorded two quantities *known to be equal* **without the equation between
them**.

The gap stayed invisible until the **first consumer that had to exercise
it**: the general-`d` dispatch (LEAF-3 of `chainData_dispatch`) must match
the discriminator's `Fin (k+1)` panels to the `Fin cd.d` chain candidates,
which is impossible without `d = k+1`. The `d=3` floor had masked it — `d=3
= k+1` holds by construction there, so nothing ever *invoked* the identity.
A build correctly BLOCKED (refusing to guess a frozen-contract change,
per *Constructibility recon …* below); a design-pass + a diverse-lens recon
pair + a coordinator PDF-check of the KT primary source confirmed `d = k+1`
is structural and the fix (add `d = n` to the **record**, populated at
construction). It is a **record field, not a dispatch hypothesis**, because
the ENTRY extractor *builds* the chain to length `k+1` (KT 4.6's truncation
*is* the constructor) — so the field is **set, not proved-after-the-fact**,
which is exactly what keeps it off the satisfiability trap (*Constructibility
recon …*: a hypothesis dischargeable for the actual consumer).

Three durable rules:

1. **Encode the invariant relating free parameters.** A known identity left
   as a docstring aside is a latent gap. "No field references `n`" should
   have triggered the question *which consumer needs the `d`–`n` link, and
   how do they get it?* — not a decision to drop it.
2. **A "frozen" contract is settled only relative to the consumers analyzed
   at freeze time.** C.1 froze `d` free in 23b, before the general-`d`
   dispatch existed; "23d opens against a settled interface" was true only
   for the consumers that then existed. A freeze pass should walk the
   not-yet-built consumers' requirements.
3. **An index-family match between two *different cardinalities* is a
   structural requirement, not "`Fin` arithmetic latitude."** The
   decomposition pass rated the `u : Fin (k+1)` ↔ `i : Fin cd.d` match as
   build-time latitude; it is a contract fact (`d = k+1`). When a pin says
   "match `u` to `i`", confirm the index sets share a cardinality by a
   stated contract fact before rating it latitude.

The operative triggers for rules 1–3 live where they fire (DESIGN.md is
read-on-demand, not at decomposition/freeze time): the `coordinate-phase`
command's step-1 trigger list (coordinator-side) and its design-pass clause
(iii) (the subagent that writes the hand-off). Cross-refs: *Constructibility
recon before scheduling a producer build* (the satisfiability discipline this
specializes to the contract level); `notes/Phase23-design.md` §I.8.24(4.11);
`notes/model-experiment.md` rows 407–410.

## Compiler-checked spike, not prose recon, for "do these objects compose?" questions (the Phase-23c LEAF-4 postmortem)

The recon mechanism (`coordinate-phase` step 1) defaults to a **prose
design-pass** — an agent that reads the landed `def`/`theorem`s and writes a
design-doc verdict naming the route. That is the right tool for a *faithfulness*
or *decomposition* question ("does this match KT?", "what are the buildable
sub-leaves?"). It is the **wrong** tool for a *route-composition* question — "do
these specific Lean objects actually compose to produce goal X?" — in the
defeq-fragile zone, because prose reasons about *types it mischaracterizes*, and
a wrong prose verdict becomes a hand-off the next build trusts, propagating the
error.

The Phase-23c interior-`hρe₀` conjecture crux (KT eq-6.66, the redundancy carry
across the spliced body `vᵢ`) was mis-pinned **3–4 times in a row by prose
recon**: §I.8.24(4.12) called the column-value read "wrong-shape, the dead
`hρGv` hrCol" and *forbade* it; (4.13) re-routed to the incident panels (wrong
panel); (4.15) — a **diverse-lens prose pair** — converged on a value-free chain
induction needing a per-vertex witness producer with no source (Route W). Every
verdict was prose; every one mischaracterized the types. The root error was a
**conflation**: "the column-value read" (an ℝ^D equality `group column = −ρ₀`,
which *is* KT's wall-escape) was labeled the same as "the member-mapping wall" (a
span-membership transport `hingeRow ρ₀ ∈ span(candidate)`, genuinely dead). The
compiler distinguishes them; the prose did not.

A single **compiler-checked spike** — a read-only agent that wrote a scratch
probe, built it, and read the kernel's verdict per seam — **dissolved the entire
route fork**: it proved (sorry-free) that the consumer's `hρe₀` reduces by a
relabel identity to one canonical goal, then *closed that goal in 4 steps* using
the very value read the prose had forbidden, fired one index deeper
(framework-free: the block test reads only `ends`/`q`, so the `vᵢ`-incidence that
"excluded" the spliced edge from `G − vᵢ` is a non-issue when the panel is read
off the seed, not through a framework). The crux 3–4 prose passes could not
settle closed in one spike.

Three durable rules:

1. **Match the recon shape to the question.** *Faithfulness / decomposition* →
   prose design-pass (the compiler can't check faithfulness to a paper).
   *"Do these Lean objects compose?"* → a **compiler-checked spike**: a read-only
   probe (scratch file + lean-lsp MCP) that builds the candidate composition,
   `sorry`s the gaps, and reports the *exact kernel-checked residual goal* — not a
   prose verdict. In the defeq-fragile zone the compiler is the only reliable
   adjudicator of composition.
2. **A prose prohibition born of a conflation steers every successor recon
   wrong.** "Do NOT route through the value read" (from (4.12)'s conflation)
   pushed (4.13)/(4.15) away from the landed solution toward the unbuildable
   Route W. Before enshrining a "do NOT use X" prohibition for a
   *compiler-decidable* route, **spike X** — one probe is cheaper than the
   multi-recon churn a wrong prohibition causes (here ~3 build commits were
   orphaned on the forbidden-route detour).
3. **Salvage a spike's sorry-free work; don't re-derive it.** A read-only probe
   reverts its scratch (correct), but its compiler-checked lemmas are valuable —
   `SendMessage`-resume the *same* agent to re-emit them as real commits rather
   than spawn a fresh agent (it has the source in context). The resume runs in
   the background (no synchronous return); the coordinator re-runs all gates
   after.

Operative triggers live where they fire: the `coordinate-phase` command (step-1
trigger list + the recon-dispatch-shape section) and `notes/coordinate-phase-rescue.md`
§6 (the spike + salvage dispatch shapes). Cross-refs: *Constructibility recon
before scheduling a producer build* (the satisfiability discipline a spike
empirically discharges); `notes/Phase23-design.md` §I.8.24(4.13)–(4.16);
`notes/model-experiment.md` rows 426–428 + Session #28 *Findings*.

## Choices to revisit

These are *open*: we expect to revise based on how proofs actually
unfold. Add to this list whenever a session surfaces a question; move
to a fixed section above once a question is answered.

- ~~**Vertex insertion in Henneberg moves.**~~ **Resolved (Phase 3 start):**
  Use `Option V`. The fresh vertex is `none`; old vertices embed via
  `some : V ↪ Option V`. Chosen over `V ⊕ Unit` for readability and over
  fixed-`V`-with-`v ∉ G.support` because the latter forces every move to
  carry a freshness side-condition. `Option α` is the canonical "add
  one element" idiom (cf. `Equiv.optionEquivSumPUnit`) and we use it
  directly here. Cost: chained moves give types `Option (Option …)`;
  mitigated by working modulo isomorphism in the Phase 5 induction.
  Companion decision: drop the `Reachable` inductive in favour of
  `IsLaman.exists_typeI_or_typeII_reverse` + strong induction on
  `Fintype.card V`, since heterogeneous-type reachability would need
  its own infrastructure to reason about.
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
- ~~**Typeclass shape for finiteness on `V`.**~~ **Resolved (Phase 7
  cleanup):** Follow mathlib style. State every signature at the
  weakest typeclass its *statement* genuinely uses — typically
  `[Finite V]`; use `[Fintype V]` in the signature only when the
  *type* mentions `Fintype.card V`, `Finset.univ : Finset V`, or
  similar `Fintype`-flavored objects. When the proof body needs
  `Fintype V`-strength data, bridge inline via `haveI : Fintype V
  := Fintype.ofFinite V`; for `Finset V` operations needing
  `DecidableEq V`, follow with `classical` (or take `[DecidableEq
  V]` explicitly per-site). This is the mathlib idiom — enforced
  by the `unusedFintypeInType` env linter and visible in mathlib's
  own use of `[Finite V]` + inline bridge throughout. The principle
  is **strongest mathematical claim, maximum generality**: weaker
  hypothesis = more general theorem. The project follows the
  idiom; the Phase 7 cleanup round B1/B2/B5 audits confirmed this
  match (no signature changes needed). Discussion of the considered
  alternatives — and why mathlib style ultimately wins — follows:

  Surfaced by the Phase 7 cleanup round (B1 = 41 `classical` sites,
  B2 = 12 `[Finite V] → Fintype` bridge sites, B5 = `Set` vs
  `Finset` boundaries — see `notes/Phase7-cleanup.md`). The repo
  prior to resolution mixed three forms heterogeneously:
  - `[Finite V]` (e.g. `Sparsity.lean` section `IComponents` at
    line 1269, `EdgeSetRowIndependent.eventually` in
    `RigidityMatroid.lean`) — weakest typeclass. Bodies that need
    `Fintype V`-strength data bridge inline via `haveI : Fintype V
    := Fintype.ofFinite V`, which then needs a paired `classical`
    for `Finset V` decidable-equality operations.
  - `[Fintype V]` (e.g. `IsSparse.exists_rowIndependent_placement`
    in `MatroidIdentification.lean`, much of Laman / framework
    infrastructure) — when the body uses `Fintype.card` /
    `Finset.univ` / `Fintype.card`-based strong induction.
  - `[Fintype V] [DecidableEq V]` (occasional, e.g.
    `IsLaman.two_le_degree`) — signature matches `Finset V` body
    needs directly.

  The status-quo `[Finite V]` + inline bridge idiom spares callers
  a `Fintype` hypothesis at the cost of `haveI` + `classical`
  boilerplate per proof body. The mathlib-style alternative is to
  state each signature at the typeclass the body genuinely uses,
  propagating `[Fintype V]` (and `[DecidableEq V]`) to callers; in
  this project's caller graph (downstream-only, no third-party
  consumers) propagation is mechanical, but it's still an API
  change to N declarations.

  **Pebble-game pointer.** A future pebble-game formalization
  (deciding `(k, ℓ)`-sparsity computationally, the standard
  algorithmic side of rigidity theory) requires
  `[Fintype V] [DecidableEq V] [DecidableRel G.Adj]` end-to-end,
  since the procedure is a state machine on `Finset V` and
  `Finset (Sym2 V)`. So "lift signatures to `[Fintype V]
  [DecidableEq V]`" is forward-compatible with that trajectory;
  retaining `[Finite V]` signatures optimizes for present
  generality at the cost of pebble-game-prep work later.

  This question was foreshadowed in *Edge type: `Set (Sym2 V)`*
  alternative §1 (line 87 above): "add a `Finset`-valued companion
  guarded on `[Fintype V] [DecidableRel G.Adj]` once we hit proofs
  that benefit." Phase 7's row-independence track is when that
  surfaced concretely.

  **Resolution discussion (Phase 7 cleanup).** Concrete data
  gathered: pebble game is "someday" not "soon" (mentioned in
  `count-matroid.tex`, `Phase7.md` as future direction, not on
  ROADMAP). `[Finite V]` footprint was 39 sites, only 12 of which
  did inline `Fintype.ofFinite V` bridges; the other 27 worked at
  `[Finite V]` strength genuinely.

  Two earlier resolution iterations were considered and reversed:

  1. **Uniform `[Fintype V]`** — strengthen every signature to
     `[Fintype V]`, eliminating all 12 inline bridges. Rejected
     after re-weighing the pebble-game forward-compatibility
     argument: the pebble-game *side* needs `[Fintype V]
     [DecidableEq V] [DecidableRel G.Adj]` regardless (the
     procedure's definition can't work at weaker strength), and
     cross-side bridges from `[Fintype V]` callers to `[Finite V]`
     callees work automatically via typeclass propagation, so the
     matroid-side convention is independent of pebble-game scope.
     Uniformity would have strengthened 27 declarations beyond
     what their bodies require, sacrificing mathematical
     generality.

  2. **Per-declaration "state at typeclass body uses"** — lift
     only the 10 declarations whose bodies bridge `[Finite V] →
     Fintype V` inline (6 originally identified `letI/haveI` form
     + 4 missed `have` form). Rejected after re-examining mathlib
     style: this would also weaken the lifted theorems
     (`[Fintype V]` is a stricter hypothesis than `[Finite V]`),
     and mathlib's `unusedFintypeInType` linter exists precisely
     to enforce the opposite direction — "if `[Fintype V]` isn't
     used in the type, state at `[Finite V]` and bridge in the
     proof." mathlib's own corpus follows this convention; the
     existing `[Finite V]` + inline-bridge pattern in our 10
     bridge sites is canonical mathlib idiom, not a smell.

  **Settled resolution:** keep all `[Finite V]` signatures as-is.
  The inline `Fintype.ofFinite V` + `classical` boilerplate is the
  cost of stating theorems at maximum generality, and it's the
  same cost mathlib pays. The audit's value is **verification that
  the project already follows mathlib style**; no API changes
  needed. The 12 bridge sites and 41 `classical` calls all stay.
- ~~**Phase 8: `apnelson1/Matroid` dependency.**~~ **Resolved (Phase 8
  open):** added to `lakefile.toml` at revision
  `e6852cec65742d1ddce7a66122f842b791b1dd37` (apnelson1/Matroid
  HEAD at the time of landing). Provides `Matroid.ofFun` and
  `Module.matroid` in `Matroid/Representation/Map.lean`; builds
  clean against our mathlib pin (`21b745fd…`) despite a 179-commit
  forward gap, so the Phase 6 investigation's prediction held. The
  alternatives — mirror `Matroid.Representation.Map` under our
  `Mathlib/` mirror, or rebuild `Matroid.ofFun` directly on mathlib's
  `IndepMatroid.ofFinitaryCardAugment` — were both considered and
  rejected at the Phase 8 opener (see `notes/Phase8.md`
  *Architectural choices made up front*). **Still open:** track
  upstream merges of `Matroid.ofFun` into mathlib (which would
  obsolete the dep) and re-evaluate the pin whenever mathlib is
  bumped — apnelson1's master tracks mathlib master, so a stale pin
  drifting behind ours is the recurrent failure mode to watch.

  **The predicted drift materialized (Phase 13).** Phase 13 is the
  first phase to import `Matroid.Graphic` (for `Graph.cycleMatroid`);
  nothing earlier touched it, so a mathlib-master-drift breakage in a
  transitive dependency (`Matroid/Uniform/Basic.lean`,
  `unifOn_rankPos_iff` — a `simp` that no longer closed) went
  unexercised through Phase 12. Pin-bumping does not help (upstream
  HEAD leaves the broken proof unchanged); local vendoring of
  `cycleMatroid` is impractical (~2280-job transitive closure). The
  pin therefore points at a **one-commit fork** off `e6852ce`
  (`bryangingechen/Matroid` `combinatorial-rigidity-fix`, `08d517f`)
  carrying just the one-line proof fix. mathlib rev is unchanged, so
  Phases 1–12 are unaffected. No upstream PR (trivial; upstream will
  re-green on its own). **Retire the fork** — back to a direct
  apnelson1 pin — once upstream builds clean against a compatible
  mathlib. See `notes/Phase13.md` *Blockers*.
- **Migrating Phases 1–11 from `SimpleGraph` to mathlib's `Graph`.**
  **Decided against wholesale migration (2026-06); keep Phases 1–11
  on `SimpleGraph`.** Context: Phase 12 (body-bar) adopts mathlib's
  core multigraph type `Graph α β` (PR
  leanprover-community/mathlib4#24122, apnelson1, merged 2025-05-14)
  as its carrier — see `notes/Phase12.md` *Architectural choices*.
  That raised whether the existing ~10.9k-line `SimpleGraph` corpus
  (20 files, 475 `SimpleGraph` occurrences) should follow.

  Decided no, for four reasons: (i) `SimpleGraph` is the
  mathematically correct carrier for bar-joint rigidity — parallel
  edges and loops are meaningless for frameworks, so `Graph` would
  force `Simple`/loopless side-conditions everywhere; (ii)
  `SimpleGraph`'s mathlib API (connectivity, `Subgraph`, walks,
  degrees, `edgeFinset`, the lattice) is far more mature than
  `Graph`'s, whose walk/dart/`GraphLike` API is still being built
  (Zulip #graph theory *"Set in definition of Graph"*, *HasAdj*);
  (iii) that `Graph` API is in active flux — a poor bet for finished
  work; (iv) cross-quote pressure is low — Phase 12 reuses the
  matroid-union / `cycleMatroid` machinery, not the bar-joint
  rigidity results.

  **Sparsity / pebble-game sub-question.** Tay's count
  `|E'| ≤ d(|V'|−1)` is exactly `(d,d)`-tightness, the `ℓ = k` corner
  of the `(k,ℓ)`-sparsity matroid family (Laman is `(2,3)`);
  `(k,k)`-tight ⟺ `k` edge-disjoint spanning trees (Nash–Williams,
  `nashWilliams1961`). So Tay *is* a sparsity theorem. But Phase 12
  proves it by the **matroid-union route** (Whiteley 1988,
  `whiteley1988`): `k`-frame matroid = union of `k` cycle matroids →
  Edmonds matroid-partition count → specialization to realizations.
  It does **not** route through the Lee–Streinu pebble game — the
  pebble game *decides* sparsity, whereas Tay's existence proof is
  *handed* the tree-packing by Edmonds' partition theorem. So
  migrating the ~3.5k-line `SimpleGraph`+`(2,3)` pebble game (Phase
  9/10) to `Graph` buys Phase 12 nothing. The right move for the
  sparsity *predicate* is to **define a `Graph`-native
  `IsSparse`/`IsTight d d` fresh in Phase 12** (so Tay reads as a
  sparsity theorem) rather than migrate Phase 9/10's `SimpleGraph`
  sparsity out from under the Laman / executable stack.

  **Revisit triggers:** (a) mathlib deprecates `SimpleGraph` or lands
  a stable `SimpleGraph`-on-`Graph` story; (b) a phase needs
  same-graph cross-quoting of simple-graph and multigraph rigidity,
  or general multigraph `(k,ℓ)`-pebble games, at scale. **Bridge, not
  phase:** when Phase 12 first needs to relate a simple graph to a
  `Graph`, add a single `SimpleGraph.toGraph` transport (and unify
  the two sparsity predicates by showing the `(2,3)` `SimpleGraph`
  form is its `toGraph` pullback) — a lemma, not a refactor.
