# Phase 9 — Pebble game (work log)

**Status:** in progress.

This file is the per-phase work record. See `../ROADMAP.md` §9 for
the high-level plan and `../DESIGN.md` for cross-cutting design
choices.

**Workflow:** Phase 9 runs in **forward blueprint mode** per
`../blueprint/DESIGN.md`. The new chapter
`chapter/pebble-game.tex` will be the authoritative dep-graph and
lemma index; this file carries architectural choices, decisions,
and hand-off — *not* the lemma checklist. The chapter is opened in
the first Phase 9 commit.

**References.**
- A. Lee, I. Streinu, *Pebble game algorithms and sparse graphs*,
  Discrete Math. **308** (2008) 1425–1437. PDF in
  `../.refs/lee-streinu-2008.pdf`. The phase formalizes the *basic*
  $(k, \ell)$-pebble game of §3–§4 and its correctness theorem
  (Theorem 8).
- D.J. Jacobs, B. Hendrickson, *An algorithm for two-dimensional
  rigidity percolation: the pebble game*, J. Comput. Phys. **137**
  (1997) 346–365 — the original $(2, 3)$ version.
- T. Jordán, *Combinatorial rigidity*, MSJ Memoirs (2016) —
  background survey, `../.refs/jordan-2016-msj-memoirs.pdf`.
- A. Lee, I. Streinu, L. Theran, *Finding and maintaining rigid
  components*, CCCG '05 (2005). PDF in
  `../.refs/lee-streinu-theran-finding-and-maintaining.pdf`.
  Introduces the *union pair-find* data structure for the $O(n^2)$
  *component pebble game*. **Out of scope for Phase 9** (basic
  pebble game only); pointer for any future component-pebble-game
  phase.

## Current state

Phase 9 is in progress. The forward-mode blueprint chapter
`chapter/pebble-game.tex` is the authoritative dep-graph and lemma
index; `PebbleGame.lean` ships the leaf-most state-machine
definitions `PartialOrientation V` (bundled `Finset (V × V)` with
`no_loops` and `no_antiparallel` invariants), the derived pebble
counts `out`, `peb`, `span`, `outOn`, `pebOn` (plus `empty` and
basic `simp`-level lemmas), and the path-reversal move
`PartialOrientation.reverse D p hp` along a simple directed path
`p : DirectedWalk (· ∈ D.arcs) u w` with `hp : p.IsPath`. The two
`PartialOrientation` invariants (`no_loops`, `no_antiparallel`)
survive the reversal. Structural per-vertex / subset lemmas:
`span_reverse_eq` (span of any subset invariant under reversal),
`out_reverse_add` (unified additive identity for the head/tail/
interior cases) and its three corollaries
`out_reverse_of_not_endpoint` / `out_reverse_head` / `out_reverse_tail`,
plus the pebble-count corollaries `peb_reverse_of_not_endpoint` /
`peb_reverse_head` / `peb_reverse_tail` (the last two under the
algorithmic preconditions `D.out u ≤ k` / `D.out w < k` mirroring
`lem:pebble-game-invariants` (1)). Supporting arc-swap and source-
count infrastructure lives in `Search/DFS.lean`:
`mem_arcsFinset_imp`, `reversedArcsFinset_eq_image_swap`,
`card_reversedArcsFinset`, `tail_mem_vertices`,
`fst_mem_vertices_of_mem_reversedArcsFinset`,
`IsPath.notMem_snd_initial`, and the two source-cardinality lemmas
`IsPath.card_arcsFinset_filter_fst` /
`IsPath.card_reversedArcsFinset_filter_fst` (each counts the
source-`v` slice of the corresponding arc set as `0` or `1`
depending on whether `v` lies on `p.vertices` minus the relevant
endpoint). PebbleGame-level glue (`arcsFinset_subset_arcs`,
`disjoint_sdiff_reversedArcsFinset`, `out_eq_card_filter_fst`,
`IsPath.head_ne_tail_of_pos`) sits in `PebbleGame.lean`. The
remaining structural lemma (`pebOn + outOn` invariant on subsets,
feeding `lem:pebble-game-invariants` (2)) is deferred to a
follow-up commit. Blueprint `def:partial-orientation`,
`def:pebble-counts`, and `def:path-reversal` are green.

The phase target is Lee–Streinu Theorem 8 in certificate form:
$\mathtt{runPebbleGame}\,G$ returns either a `PartialOrientation`
satisfying the four invariants (witness of $(k, \ell)$-sparsity) or
a vertex subset $V'$ with $|E(G[V'])| > k|V'| - \ell$ (witness of
non-sparsity). The matroidal-independence corollary against
Phase 7's `CountMatroid` follows as a one-liner.

**Pre-Phase-9 DFS warmup — closed.** `CombinatorialRigidity/Search/DFS.lean`
(~360 LoC) ships `reachableFinding` (the primitive itself,
`(succ v).attach.findSome?` body + `(Finset.univ \ visited).card`
termination measure) and the full correctness theorem
(`reachableFinding_sound` + `reachableFinding_complete`). Build +
lint clean. The function is **fully computable**:
`succ : V → List V` (not `V → Finset V`) for child enumeration,
with `visited : Finset V` retained only for the math-layer
termination measure. `#eval reachableFinding succEx (· == 2) 0` on a
`Fin 4` example returns `some (2, [0, 1, 2])` — directly executable,
satisfying the `IO`-pipeline use case (parser → DFS → emitter) raised
mid-session. See *Decisions made → DFS warmup* below + DESIGN.md
*Pebble-game style island* (math/exec layer split paragraph) +
`FRICTION.md` *[resolved] `Finset.toList` is noncomputable* for the
design history. Blueprint `def:reachable-finding`,
`thm:reachable-finding-correct`, and `def:directed-walk` are all
green; `chapter/dfs.tex`'s dep-graph closes.

**Completeness shape.** Soundness used a strengthened helper +
`reachableFindingAux.induct` (auto-generated three-case recursor on
visited-revisit / `P v` hit / `findSome?` recurse); completeness
uses the same outer recursor, with an *inner* induction on a walk
length bound `n` to handle the recursive case's two sub-cases:
*(i)* walk revisits the current source `v` — extract a strictly
shorter walk from `v` via `DirectedWalk.dropUntilBundle` (a
`Subtype`-bundled truncation carrying its length-bound and
vertex-subset witnesses) and recurse via the inner IH at the
**same** `visited`; *(ii)* walk-tail avoids the enlarged
`insert v visited` and the outer IH at `(insert v visited, v')`
closes. Lifting the user-facing `ReflTransGen` hypothesis to an
explicit `DirectedWalk` uses `Relation.ReflTransGen.head_induction_on`
(head-first recursion, matching `DirectedWalk.cons`).

Next concrete commit: ship the subset-level
`pebOn_add_outOn_reverse_eq` invariant. `outOn` is *not* literally
invariant on every subset — it shifts by `[u_m ∈ V'] - [u_0 ∈ V']`
— but `span` is invariant (already landed) and the sum
`pebOn + outOn` is genuinely invariant on every subset, which is
what `lem:pebble-game-invariants` (2) actually needs. With that in
hand `lem:pebble-game-invariants` becomes the leaf-most red node.
See *Hand-off / next phase*.

## Architectural choices made up front

These extend `../DESIGN.md` *Choices to revisit*; if any turns out
wrong, revisit there.

- **Match Phase 7's matroidal regime: simple graphs, $\ell < 2k$,
  both ranges in scope.** Lee–Streinu state results for *multi-graphs*
  with loops, covering $\ell \in [0, 2k)$. We work in `SimpleGraph V`,
  matching the regime of `CountMatroid.lean` and `Sparsity.lean`
  exactly. Loops in L-S's lower range $\ell < k$ contribute single-
  vertex blocks; their absence in `SimpleGraph`-land changes the
  corner-case structure but not the overall theory — the lower
  range is genuinely interesting (tree-packing / arboricity
  applications, cf. Nash-Williams–Tutte) and stays in scope. Corner-
  case verification of L-S Lemmas 10–14 against `SimpleGraph` is an
  early-Phase 9 task (see *Blockers*). Lifting to multi-graphs is a
  much larger project (no mathlib `MultiGraph` infrastructure
  exists) and is out of scope.

- **Finset-first computability style with `[Fintype V] [DecidableEq V]`.**
  The repo defaults to `Set.ncard` + noncomputable definitions on
  `[Finite V]`. The pebble game needs `Finset (V × V)`-backed
  orientations and decidable equality end-to-end so `#eval` and
  `decide` actually run — the extracted-certificate output requires
  it, and `[Finite V]` carries no algorithmic content (you can't
  enumerate or build `Finset`s from it). `PebbleGame.lean` is a
  deliberate style island: `[Fintype V]` + `[DecidableEq V]` in
  signatures, `Finset.card` over `Set.ncard` in algorithm bodies,
  fully computable. A thin shim section bridges to the noncomputable
  `IsSparse`/`IsTight` statements from `Sparsity.lean`. DESIGN.md
  note expected at first Lean commit.

- **Decouple algorithm state from input-graph shape.**
  `PartialOrientation V` and the algorithm body are defined purely
  on `V` and edge-insertion requests (`List (Sym2 V)` or
  `Multiset (Sym2 V)`), not on a specific `SimpleGraph V`.
  `SimpleGraph` enters only at the statement-level wrapper
  `theorem runPebbleGame_simpleGraph_correct (G : SimpleGraph V) :
  …`. The four invariants (Lemma 10) are stated on orientation
  states, not on the input graph; they port unchanged to a future
  multi-graph version (which would just relax the no-parallel-pair
  invariant on `PartialOrientation`). Hypergraph generalisation
  requires redesigning the orientation shape — out of scope to
  design for, but the input/state decoupling at least does not
  actively block it. Cost: one extra wrapper definition + one
  extra wrapper theorem.

- **Algorithm output: structured `Sum`, not L-S's four-way
  classification.** Lee–Streinu return one of
  `{well-, under-, over-constrained, other}`. We collapse to
  ```
  runPebbleGame : … → CertifiedOrientation V k ℓ ⊕ BlockingWitness G k ℓ
  ```
  where the left branch is a `PartialOrientation V` bundled with
  proof of L-S Invariants (1)–(4), and the right branch is
  `{S : Finset V // |edgesIn S| > k * S.card - ℓ}`. Both branches
  positively certify their conclusions. The well-vs-under-vs-over
  trichotomy is a downstream corollary on the size of `peb(V)` and
  is recovered without changing the algorithm shape. Rejected
  alternative: a `PebbleGameResult` four-case enum — adds API
  surface for content already captured by the certificates.

- **Single-phase scope: basic pebble game, both directions.** Phase 9
  covers L-S §3–§4 end-to-end: definitions (state, moves), the four
  invariants (Lemma 10), soundness (accept $\Rightarrow$ sparse,
  Corollary 12), completeness (sparse $\Rightarrow$ accept,
  Lemmas 13–15), and failure-witness extraction. Deferred to
  potential later phases: the *component pebble game* (§5,
  $O(n^2)$ speedup using rigidity components); the Henneberg-
  sequence application (§6, which generalises Phase 3's
  Laman-specific Henneberg construction); circuit / redundancy
  detection (§6 end). Splitting basic correctness across two phases
  was considered and rejected — soundness and completeness share
  too much state-and-invariant machinery to pay the phase-boundary
  cost.

- **New file `CombinatorialRigidity/PebbleGame.lean`.** Slots after
  `LinearRigidityMatroid.lean` for related-material ordering; no
  dependency on it. Imports `Sparsity.lean` (for `IsSparse`,
  `edgesIn`, and the Phase 7 `IsSparse.maxBlock` / block-edge-
  disjointness API the failure-witness branch reuses) and
  `Mathlib.Data.Finset.Basic` / `Mathlib.Data.Sym.Sym2`. No matroid
  dependency — the correctness theorem is structural; the matroidal-
  independence corollary against `CountMatroid` is a downstream
  one-liner that can live in `PebbleGame.lean` or be deferred.

- **Forward-mode blueprint chapter `chapter/pebble-game.tex`.** Per
  the Phase 6+ convention. Sections mirror L-S: *State and moves*
  → *Invariants* → *Algorithm* → *Soundness* → *Completeness* →
  *Correctness theorem* → *Matroidal-independence corollary*. The
  chapter's dep-graph is the lemma index; this file does not
  duplicate it. The chapter opens in the first Phase 9 commit
  alongside the ROADMAP §9 planning section.

## Lemma checklist

**Maintained in the blueprint, not here.** Forthcoming
`chapter/pebble-game.tex` will carry the dep-graph; once it lands,
this section becomes a pointer (cf. `Phase8.md` §"Lemma checklist").

## Decisions made during this phase

### State and counts (Phase 9 main, opening commit)

- **`PartialOrientation V`: option (i), `Finset (V × V)` bundled
  with `no_loops` + `no_antiparallel`.** Cleanest for definitions
  and invariants — `arcs.filter`-based `out`/`span`/`outOn` and
  `Finset.sum`-based `pebOn` derive directly. Out-adjacency for DFS
  uses a `outNbhd : V → Finset V` view (`arcs.filter (·.1 = v) |>
  .image Prod.snd`); the `outList : V → List V` shim lands with
  `tryReachPebble`. Rejected (ii) `V → Finset V` (forces duplicated
  `(u, v)` / `(v, u)` bookkeeping for `no_antiparallel`) and (iii)
  `V → V → Bool` (hostile to `Finset.card`-based counts).

- **Pebble counts: distinct Lean names per type to break the
  `out_D(v)` / `out_D(V')` overload.** Per-vertex `out v` and
  `peb k v`; per-subset `span V'`, `outOn V'` (arcs *leaving*
  `V'`), `pebOn k V'`. `peb k v := k - out v` uses ℕ-subtraction
  directly — the algorithm's structural `out v ≤ k` invariant
  makes Invariant (1) (`peb + out = k`) follow from
  `Nat.sub_add_cancel`. The "avoid ℕ-subtraction" project
  convention applies to *propositions*, not *definitions*.

### Path reversal (Phase 9 main)

- **Walk-arcs lemmas live in `Search/DFS.lean`, not
  `PebbleGame.lean`.** `DirectedWalk.arcsFinset` /
  `reversedArcsFinset` are pure `DirectedWalk` operations
  (independent of `PartialOrientation`); they belong in DFS.lean
  alongside the inductive itself. The downstream `IsPath`
  guarantees `notMem_loop_arcsFinset` /
  `notMem_antiparallel_arcsFinset` are the two facts the
  `PartialOrientation.reverse` invariants consume; the names sit
  in `DirectedWalk.IsPath` so dot notation `hp.notMem_…` works.

- **`obtain ⟨rfl, rfl⟩ := Prod.mk.inj …` on `(a, b) = (u_out, u_int)`
  in a `DirectedWalk` cons induction triggers motive issues.** The
  cons-pattern indices `u_out, u_int` ride on `q : DirectedWalk R
  u_int w`'s type, so an `rfl` substitution of `u_int := …` (or
  the follow-up `rw [← h_eq]`) tries to rewrite `u_int` in `q`'s
  type and fails with *motive is not type correct*. Same shape as
  `TACTICS-QUIRKS.md` § 4 (subst between two free variables) but
  the failure surfaces at the next `rw`, not at the `obtain`. Fix:
  bind the pair equalities to named hypotheses (`have h_uo : v =
  u_out := (Prod.mk.inj heq).1`), rewrite only in goals whose
  ambient terms don't depend on the substituted variable, and
  factor the "head vertex is in `vertices`" obligation through a
  one-line `head_mem_vertices` helper rather than `cases q <;>
  simp [vertices]`. The helper is `@[simp]`, will be reused by
  the structural-lemma commit. See FRICTION `[resolved] `rw` over a
  cons-pattern endpoint variable trips motive on the sibling
  walk's type`.

- **Source-cardinality lemmas unify head/tail/interior via a single
  `if-then-else` formula keyed on `IsPath`.** For a simple walk
  `p : DirectedWalk R u w`, `(p.arcsFinset.filter (·.1 = v)).card`
  is `1` iff `v ∈ p.vertices ∧ v ≠ w` (and `0` otherwise);
  symmetrically for `reversedArcsFinset` with the `≠ w` clause
  replaced by `≠ u`. The formula handles `nil` walks correctly
  without a special `0 < length` clause (when `nil u`, `v ∈ [u]`
  combined with `v ≠ u` is automatically `False`), so a single
  induction on `p` covers both cases. Pairing the two lemmas gives
  the unified additive identity `out_reverse_add` (new-out + path-
  source = old-out + reversed-source), from which the three
  endpoint corollaries fall out by case-analysis on whether `v` is
  on `p.vertices` and which endpoint it is.

- *`rw [D.field_eq]` motive failure when another local's type
  references `D.field`* → TACTICS-QUIRKS § 18, FRICTION
  *[resolved] `rw [D.field_eq]` fails motive when a local's type
  references the field*. Bit `out_reverse_add` first; the
  `Finset.ext`-based workaround will apply again at the subset-
  level reversal lemma.

### DFS warmup (pre-Phase-9)

- **Style island formalized in DESIGN.md.** Phase 9's architectural
  choice 2 (`[Fintype V] [DecidableEq V]` end-to-end for the pebble-
  game line) is now documented as a fixed section in `../DESIGN.md`
  *Pebble-game style island*. The DFS file is the first instance of
  the style island, so the note landed with the scaffold commit
  rather than waiting for `PebbleGame.lean`. Both files (DFS warmup
  + Phase 9 main) referenced.

- **`DirectedWalk` is inductive, indexed by endpoints.** Mirroring
  `SimpleGraph.Walk`, with `nil`/`cons` constructors and `length` /
  `vertices` / `IsPath := vertices.Nodup` accessors. Rejected
  alternative: `{ p : List V // p ≠ [] ∧ p.Chain' R ∧ … }` subtype —
  more compact but noisier proof-engineering at every `cons` /
  case-split. The inductive shape matches the project / mathlib idiom
  for walks and keeps the API surface low.

- **Relation as `succ : V → List V` plumbed via the predicate
  `fun a b => b ∈ succ a`.** `DirectedWalk` itself stays parametric
  over an abstract `R : V → V → Prop`; the DFS function passes the
  out-neighbour-membership relation to it. The signature uses
  `List V` rather than `Finset V` so the algorithm is fully
  computable — `Finset.toList` is noncomputable in mathlib (see
  *Decisions made → math/exec layer split*), and an enumeration-based
  DFS body propagates that. Callers holding adjacency data in
  `Finset` form expose a list projection at the DFS boundary; the
  projection itself can stay noncomputable in isolation without
  contaminating the algorithm.

- **Predicate `P : V → Bool`, completeness against `ReflTransGen`.**
  `P : V → Bool` matches the blueprint exactly (decidable by
  construction; `decide` fires). The completeness theorem quantifies
  against `Relation.ReflTransGen (fun a b => b ∈ succ a) v w` rather
  than via the walk type itself — separates "is reachable" from
  "carries a walk witness" cleanly.

- **Body: single-function with `List.findSome?` over mutual
  recursion.** Initial attempt used a `mutual` block with separate
  `reachableFindingAux` / `reachableFindingChildren` helpers, but
  structural recursion failed because the children-list parameter
  has type `List {u // u ∈ succ v}` — depending on the function
  parameter `v`. Restructured to a single `reachableFindingAux` that
  iterates children inline via `(succ v).attach.findSome?`, with the
  recursive call inside the lambda. Lean's WF tactic sees through
  `List.findSome?` to the recursive call and the
  `(Finset.univ \ visited).card` measure dispatches in one
  `decreasing_by` proof.

- **Math/exec layer split: `succ : V → List V`, `visited : Finset V`.**
  `Finset.toList` is noncomputable in mathlib (it lifts through
  `Multiset.toList`'s `Classical`-flavored `Quotient.lift`), so an
  enumeration-based DFS body taking `succ : V → Finset V` would
  silently force the whole algorithm `noncomputable`. The DFS warmup
  was first drafted with `Finset` and observed the friction; we
  refactored to `succ : V → List V` (exec layer, computable) while
  keeping `visited : Finset V` (math layer, needed for
  `Finset.univ \ visited`'s cardinality termination measure). Sanity
  check: `#eval reachableFinding succEx (· == 2) 0` returns
  `some (2, [0, 1, 2])` on a `Fin 4` example. Phase 9 main's
  `PartialOrientation V` is expected to follow the same pattern:
  store as `Finset (V × V)` internally for invariants, expose
  `outList : V → List V` at the DFS boundary. See FRICTION.md
  *[resolved] `Finset.toList` is noncomputable* + DESIGN.md
  *Pebble-game style island*.

- **`[Fintype V]` bound explicitly on `reachableFindingAux`, not just
  via `variable`.** Adding `[Fintype V] [DecidableEq V]` as section
  variables and letting them auto-bind to the recursive def produced
  a confusing *"MVar does not look like a recursive call"* error —
  `[Fintype V]`, used only in `termination_by`'s `Finset.univ`,
  landed at the *end* of the auto-bound signature (`... → V → Fintype
  V`), confusing Lean's recursive-call recognition. Pinning the
  typeclasses explicitly on the def fixes it; cheap and clear.

- **`dropUntilBundle` returns a `Subtype`, not separate def +
  lemmas.** Truncating a `DirectedWalk` at the first occurrence of a
  target vertex needs three artefacts: the truncated walk itself
  (changing the `(u, w)` endpoint indices), a length-bound, and a
  vertex-subset witness. First-attempt split this into `dropUntil`
  (def) + `dropUntil_length_le` + `mem_dropUntil_vertices` (lemmas),
  but the def's body uses `subst h` to rewrite the index variable
  (so the inductive case `cons` produces a walk with the *substituted*
  endpoint), and `simp [dropUntil]` doesn't reduce through the tactic-
  mode `subst` cleanly — the lemmas need to chase the same `subst`
  via `rfl`-blocked equational rewrites. Bundling into a single
  `Subtype`-returning definition with one `induction p` handles all
  three obligations per branch (`refine ⟨walk, ?_, ?_⟩` + close each
  with a one-liner) and avoids the equational-rewrite chase entirely.
  Pattern is reusable wherever a dependently-indexed inductive needs
  truncation with auxiliary witnesses.

- **Inner length-induction for completeness's recursive case.**
  Helper `reachableFindingAux_complete` proves the contrapositive:
  if the aux returns `none`, no walk from `v` to a `P`-satisfying
  vertex avoiding `visited` exists. Outer induction is via
  `reachableFindingAux.induct` (same as soundness), but the recursive
  case can't go through directly — when the walk revisits the current
  source `v`, the walk-tail violates `∀ x ∈ p'.vertices,
  x ∉ insert v visited`. Adding an inner induction on a length bound
  `n` lets that branch recurse on the *same* `visited` via
  `dropUntilBundle`, while the *no-revisit* sub-branch hands off to
  the outer IH at `(insert v visited, v')` as expected. The
  `ReflTransGen → DirectedWalk` lift in the user-facing theorem uses
  `Relation.ReflTransGen.head_induction_on` (head-first recursion
  matches `DirectedWalk.cons`'s arc-at-head shape).

## Blockers / open questions

- **Simple-graph vs L-S multi-graph corner cases.** L-S's proofs
  use loops to handle single-vertex blocks (a vertex with $k - \ell$
  loops forms a block in the lower range $\ell < k$). In
  `SimpleGraph`-land single vertices span $0$ edges, so single-
  vertex blocks can't arise — Invariant (4)'s $\mathrm{span}(V')
  \leq k|V'| - \ell$ for $|V'| = 1$ becomes $0 \leq k - \ell$,
  automatic when $\ell \leq k$. For $\ell > k$, L-S restricts
  subset claims to $n' \geq 2$ in Lemma 10's statement, which
  carries over directly. **Action:** in the first Phase 9 session,
  trace L-S Lemmas 10–14 through `SimpleGraph`-eyes for *both*
  ranges. The lower range $\ell < k$ stays in scope (cf. choice 1
  above); work through whatever corner-case gaps surface lemma-by-
  lemma rather than restricting the target prophylactically. If a
  structural gap genuinely forces a regime restriction, document
  the specific obstruction here and revisit.

- **Termination measure for `tryReachPebble`.** Path reversal in
  L-S is bounded informally by "at most $\ell$ DFS searches per
  edge"; for Lean, an explicit decreasing measure is needed. Pattern
  model is `Batteries.UnionFind` (`termination_by self.rankMax -
  self.rank x` — a strictly-decreasing numeric measure on a finite
  data structure). For the inner DFS,
  `(Finset.univ \ visited).card` is the natural measure (visited
  grows monotonically, vertex set is finite). For the outer
  `tryAddEdge` loop, `(ℓ + 1) - (peb u + peb v)` decreases per
  successful path-reversal. The pre-Phase-9 DFS warmup (see
  *Current state*) exercises this pattern in isolation. Friction-
  log entry expected at the termination-proof commit.

- **`PartialOrientation V` representation — resolved as (i).** Bundle
  `arcs : Finset (V × V)` with the two invariants `no_loops` and
  `no_antiparallel`; see *Decisions made → `PartialOrientation V`
  representation*. Out-adjacency uses (ii) only at the DFS boundary
  via a `outNbhd : V → Finset V` shim derived as
  `arcs.filter (·.1 = v) |>.image Prod.snd`, with a `outList`
  projection (List V) to follow when `tryReachPebble` lands. Refactor
  to (ii) or (iii) only if `tryReachPebble`'s termination proof
  surfaces a structural problem.

- **Whether to land the matroidal-independence corollary in
  Phase 9 or defer.** The bridge
  `runPebbleGame G = .inl _ ↔ G.edgeSet ∈ (countMatroid k ℓ).Indep`
  is a direct corollary of L-S Theorem 8 + Phase 7's
  `CountMatroid` indep-iff-sparse. Landing it in Phase 9 ties the
  pebble-game story to the existing matroid scaffolding; deferring
  to a later "applications" phase keeps `PebbleGame.lean`
  matroid-independent. Weak preference for landing it (cheap, ties
  the loop); revisit if `Phase9.md`'s end-state is over budget.

## Hand-off / next phase

Phase 9 main is in progress. `PebbleGame.lean` now carries the
`PartialOrientation V` state and all per-vertex / single-subset
path-reversal structural lemmas: `span_reverse_eq` (span of any
subset invariant), `out_reverse_add` (unified additive identity)
plus three corollaries (`out_reverse_of_not_endpoint` /
`out_reverse_head` / `out_reverse_tail`), and the corresponding
`peb_reverse_*` family. Per-vertex reversal accounting is closed.
Supporting `Search/DFS.lean` infrastructure: arc-swap lemmas
(`mem_arcsFinset_imp`, `reversedArcsFinset_eq_image_swap`,
`card_reversedArcsFinset`), endpoint membership lemmas
(`tail_mem_vertices`, `fst_mem_vertices_of_mem_reversedArcsFinset`,
`IsPath.notMem_snd_initial`), and the two source-cardinality lemmas
(`IsPath.card_arcsFinset_filter_fst` /
`IsPath.card_reversedArcsFinset_filter_fst`) that drive the
`out_reverse_add` arithmetic. PebbleGame-level glue
`arcsFinset_subset_arcs`, `disjoint_sdiff_reversedArcsFinset`,
`out_eq_card_filter_fst`, `IsPath.head_ne_tail_of_pos` rounds out
the bookkeeping layer. Blueprint `def:partial-orientation`,
`def:pebble-counts`, and `def:path-reversal` are green; the
`def:path-reversal` prose was updated to call out the per-vertex
effects and the precondition split for `peb`. Build + lint clean.

Next concrete commit: **subset-level `pebOn_add_outOn_reverse_eq`**.
`outOn` is *not* literally invariant on every subset — it shifts
by `[w ∈ V'] - [u ∈ V']` per the head/tail accounting just landed
— but the sum `pebOn + outOn` is genuinely invariant on every
subset. This is the residual structural piece feeding
`lem:pebble-game-invariants` (2). The proof structure should mirror
`span_reverse_eq` (filter on `D.arcs \ p.arcsFinset` + swap-symmetry
on the reversed-arc image) but the predicate is "source-in-V'
xor target-in-V'" instead of "both in V'".

Subsequent commits descend the dep-graph:
`lem:pebble-game-invariants` (L-S Lemma 10, the substantive part —
trace through both ranges `ℓ < k` and `k ≤ ℓ < 2k` on `SimpleGraph`
per *Blockers → Simple-graph vs L-S multi-graph corner cases*) →
`def:tryReachPebble` (the DFS-plus-path-reversal specialisation via
`reachableFinding`) → `def:tryAddEdge` → `def:runPebbleGame` →
`thm:pebble-game-soundness` → completeness lemmas →
`thm:pebble-game-correct` → `cor:pebble-game-countMatroid-indep`.

Architectural question still open: *whether to land the matroidal-
independence corollary in-phase or defer* (weak preference: land —
cheap, ties the loop to Phase 7's `countMatroid`).
