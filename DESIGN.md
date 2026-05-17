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

## Pebble-game style island: `[Fintype V] [DecidableEq V]`

The pebble-game line of work — `CombinatorialRigidity/Search/DFS.lean`
(pre-Phase-9 verified DFS) and the forthcoming
`CombinatorialRigidity/PebbleGame.lean` (Phase 9 main file) — is a
deliberate style island. Both files take `[Fintype V] [DecidableEq V]`
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
