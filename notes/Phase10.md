# Phase 10 — Executable pebble game (work log)

**Status:** in progress.

This file is the per-phase work record. See `../ROADMAP.md` §10 for
the high-level plan and `../DESIGN.md` for cross-cutting design
choices.

**Workflow:** Phase 10 runs in **forward blueprint mode** per
`../blueprint/DESIGN.md`. The new chapter
`chapter/executable.tex` is the authoritative dep-graph and lemma
index; this file carries architectural choices, decisions, and
hand-off — *not* the lemma checklist. The chapter is opened in the
same first commit as this file.

**References.**
- Phase 9 (`chapter/pebble-game.tex`) carries the certificate-form
  correctness theorem `thm:pebble-game-correct` that Phase 10
  bridges to an actually-runnable decision procedure. The
  pre-existing `-With` workhorses
  (`tryReachPebbleWith` / `tryAddEdgeWith` / `runPebbleGameWith`) are
  already computable; Phase 10 surfaces them through a wrapper at
  `[LinearOrder V]` strength and registers Lean-level `Decidable`
  instances backed by it.
- D.J. Jacobs, B. Hendrickson, *An algorithm for two-dimensional
  rigidity percolation: the pebble game*, J. Comput. Phys. **137**
  (1997) 346–365 — the original `(2, 3)` version this phase
  specialises to at the Laman boundary.

## Current state

Layer 0 audits closed, Layer 1 (computable list views) landed,
Layer 2's workhorse-level correctness restatement landed, Layer 2
itself closed via the exec-layer wrapper `runPebbleGameExec` plus its
certificate-form correctness theorem, and Layer 3 is in progress:
the canonical `Decidable (G.IsSparse k ℓ)` and `Decidable (G.IsTight
k ℓ)` instances are registered; the matching `IsLaman` instance is
the next concrete commit. Per the revised Layer 0 audit \#1 outcome
below, there is **no `Mathlib/` mirror** for Phase 10: mathlib's
existing
`instance : PartialOrder (Sym2 α) := .ofSetLike _ _` occupies the
slot for an order on `Sym2 V` with the (non-total) subset order, so
a competing `LinearOrder (Sym2 V)` cannot be registered. Layer 1
sorts via `Lex (V × V)` on the `(e.inf, e.sup)` projection instead.

`CombinatorialRigidity/PebbleGame/Exec.lean` ships
`PartialOrientation.outListSorted` /
`PartialOrientation.mem_outListSorted` and
`SimpleGraph.edgeListSorted` / `SimpleGraph.mem_edgeListSorted` —
the four blueprint nodes `def:outListSorted`,
`lem:mem-outListSorted`, `def:edgeListSorted`,
`lem:mem-edgeListSorted` (all `\leanok`-green). The
`SimpleGraph` section additionally ships three discharge lemmas
(`edgeListSorted_no_loops` / `edgeListSorted_pairwise` /
`edgeListSorted_map_sym2_toFinset`) packaging the no-loops /
pairwise-Sym2-distinct / Sym2-image-round-trip witnesses that
`runPebbleGameWith_correct` consumes. The `PartialOrientation`
section ships the exec-layer wrapper
`runPebbleGameExec G k ℓ` plus the certificate-form
`runPebbleGameExec_correct` — both blueprint nodes
`def:runPebbleGameExec` and `thm:runPebbleGameExec-correct` are
`\leanok`-green.

`CombinatorialRigidity/PebbleGame/{Algorithm,Correctness}.lean`
ship the four workhorse-level theorems parametrised over a
caller-supplied `toSucc` / `edges` plus three discharges (no-loops,
pairwise Sym2-distinctness, Sym2-image round-trip):
`runPebbleGameWith_underline_eq` (Algorithm.lean),
`runPebbleGameWith_sound`,
`runPebbleGameWith_eq_none_imp_exists_witness_empty`, and
`runPebbleGameWith_correct` (Correctness.lean) — the blueprint node
`thm:runPebbleGameWith-correct` is `\leanok`-green. The four
math-layer wrappers (`runPebbleGame_underline_eq_edgeFinset`,
`runPebbleGame_sound`, `runPebbleGame_eq_none_imp_exists_witness`,
`runPebbleGame_correct`) re-derive cleanly: each plugs the
math-layer enumeration `G.edgeFinset.toList.map Quot.out` with its
`Quot.out_eq`-derived discharges; only
`runPebbleGame_underline_eq_edgeFinset` pays the three-discharge
proof, the rest reuse it.

Layer 3 ships `SimpleGraph.instDecidableIsSparse` in `Exec.lean`,
hypothesised on `[LinearOrder V]` / `[Fintype V]` /
`[Fintype G.edgeSet]` plus a `[Fact (ℓ < 2 * k)]` matroidal-regime
witness for typeclass synthesis. The instance body is
`decidable_of_iff ((runPebbleGameExec G k ℓ).isSome = true)` of the
iff `(runPebbleGameExec G k ℓ).isSome = true ↔ G.IsSparse k ℓ`
obtained by chaining `Option.isSome_iff_exists` against the
certificate-form theorem `runPebbleGameExec_correct`. Smoke-tested
via `#eval (decide ((⊥ : SimpleGraph (Fin 4)).IsSparse 2 3))` → `true`
and `#eval (decide ((⊤ : SimpleGraph (Fin 4)).IsSparse 2 3))` →
`false` (correct: $K_4$ has 6 edges, exceeds $2 \cdot 4 - 3 = 5$); both
reduce through the compiled `runPebbleGameExec` body in well under a
second. The blueprint node `def:isSparse-decidable` is
`\leanok`-green. Companion DESIGN.md section *One `Decidable` instance
per project predicate* (Phase 10 Commit *Layer 3 — open*) carries the
project rule forbidding competing brute-force registrations.

This commit additionally ships `SimpleGraph.instDecidableIsTight` in
the same `Exec.lean`, under the same `[LinearOrder V]` / `[Fintype V]`
/ `[Fintype G.edgeSet]` / `[Fact (ℓ < 2 * k)]` hypotheses. The instance
body is `decidable_of_iff` against the conjunction
`G.IsSparse k ℓ ∧ G.edgeFinset.card + ℓ = k * Fintype.card V`
(decidable: sparsity half via `instDecidableIsSparse`, the `ℕ`
equation as a standard `Nat.decEq`). The `IsTight` definition's
`Set.ncard` / `Nat.card V` form bridges to the `Finset.card` /
`Fintype.card V` form via the project mirror
`ncard_edgeSet_eq_card_edgeFinset` (already used in
`Sparsity.lean`'s global-edge-bound lemmas) and the mathlib lemma
`Nat.card_eq_fintype_card` — both pure rewrites with no algorithmic
content. Smoke-tested via `#eval (decide ((⊥ : SimpleGraph (Fin 4)).
IsTight 2 3))` → `false` (0 edges $\ne 5$),
`#eval (decide ((⊤ : SimpleGraph (Fin 4)).IsTight 2 3))` → `false`
($K_4$ is not even sparse), and
`#eval (decide ((⊤ : SimpleGraph (Fin 2)).IsTight 2 3))` → `true`
($K_2$ has $1 = 2 \cdot 2 - 3$ edges). The blueprint node
`def:isTight-decidable` is now `\leanok`-green.

The phase target is **end-to-end executability** of the pebble game:
a computable wrapper `runPebbleGameExec` whose body avoids
`Finset.toList` / `Quot.out` (the two `noncomputable`-introducing
primitives in Phase 9's math-layer `runPebbleGame`), a `Decidable
G.IsSparse k ℓ` instance backed by it (in the matroidal regime
`ℓ < 2k`), the corollary instances `Decidable G.IsTight` /
`Decidable G.IsLaman`, `#eval`-able worked examples on `Fin n`
graphs, and a `lake exe pebble-game` CLI binary that reads a graph
file and decides.

At the end of Phase 10, `#eval (decide (G.IsLaman))` on a concrete
small graph and `lake exe pebble-game input.txt` should reduce through
the same compiled `runPebbleGameExec` body (different runtimes —
bytecode interpreter vs native code — but the same `def`).

## Architectural choices made up front

These extend `../DESIGN.md` *Choices to revisit*; if any turns out
wrong, revisit there.

- **Computable plug-in via `[LinearOrder V]`, not via a structural
  `outList` field on `PartialOrientation`.** Phase 9's
  `outList := (D.outNbhd v).toList` inherits `noncomputable` from
  `Finset.toList`. The minimal repair is a new
  `outListSorted [LinearOrder V] (D : PartialOrientation V) (v : V) :
  List V := (D.outNbhd v).sort (· ≤ ·)` paired with
  `mem_outListSorted`, plugged into the existing `-With` workhorses
  via the universally-quantified `toSucc` parameter. No change to
  `PartialOrientation`'s structure. The alternative — extending the
  structure with a `outListInternal : V → List V` field carrying a
  `Nodup` + agreement invariant — would be more invasive and
  duplicate state already derivable from `arcs`. The Layer 0 audit
  step (see below) verifies the wrapper-only path is sufficient and
  documents the structural option as considered+rejected; if the
  audit surfaces unexpected friction, revisit.

- **Edge enumeration via `Finset.sort` on the `Lex (V × V)`
  projection of `G.edgeFinset`, not via `Quot.out`.** Phase 9's
  `runPebbleGame` projects `Sym2 V → V × V` via `Quot.out`
  (noncomputable, uses `Classical.choice`). For `[LinearOrder V]`
  the right replacement images each edge under
  `Sym2.sortEquiv`'s forward direction `fun e => (e.inf, e.sup)`,
  views the result as `Lex (V × V)` (so the `Prod.Lex` linear
  order fires), then `Finset.sort (· ≤ ·)`s and `List.map ofLex`s
  back to `List (V × V)`. The Layer 0 audit \#1 outcome (revised
  at Layer 1) below documents why sorting `G.edgeFinset` directly
  via a `LinearOrder (Sym2 V)` instance is structurally blocked:
  mathlib's `instance : PartialOrder (Sym2 α)` from `SetLike` is
  already in the slot with a non-total subset order.

- **One `Decidable` instance per project predicate, pebble-game-
  backed.** `IsSparse`, `IsTight`, `IsLaman` each get exactly one
  registered `Decidable` instance in `PebbleGame/Exec.lean`, backed
  by `runPebbleGameExec` via the correctness theorem of Phase 9.
  Docstrings flag the polynomial-time guarantee and forbid
  introducing competing instances (e.g. the brute-force `∀ Finset`
  iteration via `Fintype.decidableForallFintype` would be a valid
  `Decidable` of the same Prop, but exponential; introducing it
  would silently cause typeclass search to pick the slow path).
  Both instances decide the *same Prop*; the difference is the body
  reduced by `#eval` / `decide` / `native_decide`. See DESIGN.md
  entry below.

- **Runtime / backend matrix to surface in the blueprint, not in
  these notes.** Three invocation paths — `#eval decide …`, `lake
  exe pebble-game`, `by decide` — share the *function body* but route
  through different backends (bytecode interp / native code /
  kernel small-step reduction). All three reduce the *same*
  computable `runPebbleGameExec`; the kernel-reduction path is
  impractically slow on real graphs, so worked examples in
  `Examples.lean` use `#eval` (or `native_decide` for theorem-level
  needs, which trusts the compiled binary identically to the CLI).
  This table reads as a user-facing explainer, not a project-
  internal decision; it lands in `chapter/executable.tex` rather
  than here.

- **CLI is `Fin n`-only and ships a tiny line-oriented parser,
  exposed as `lake exe pebble-game`.** The Lake target name is
  hyphenated (matching `chapter/pebble-game.tex` and the
  `lake exe checkdecls`-style ecosystem convention) and chosen
  over the original placeholder `rigidity` so the binary name
  reflects what it computes — the pebble game — rather than the
  broader topic of the project.
  Input format is one edge per line, two whitespace-separated
  integers, with a leading `n m` line giving vertex count + edge
  count. The parser rejects malformed input with a clear
  diagnostic; vertex labels outside `[0, n)` are an error. No
  named-vertex support, no `.dimacs` or `.graphml`. Output:
  `LAMAN` / `SPARSE_NOT_TIGHT` / `NOT_SPARSE` on stdout; blocking
  witness extraction (Phase 9's deferred work) is in scope to
  attempt during Layer 5 but not committed to — if extracting it
  computably from
  `runPebbleGame_eq_none_imp_exists_witness` is non-trivial, the
  CLI ships without the witness and the extraction stays deferred.

- **New files**
  - `CombinatorialRigidity/PebbleGame/Exec.lean` — computable
    wrappers + `Decidable` instances. Sits below
    `PebbleGame/Correctness.lean` in the import graph.
  - `CombinatorialRigidity/PebbleGame/Examples.lean` — `#eval`
    examples on `Fin n` graphs. Optional but standard practice.
  - `Main.lean` (or `CombinatorialRigidity/Cli/Main.lean`) — `lake
    exe pebble-game` entry point.
  - `blueprint/src/chapter/executable.tex` — forward-mode
    dep-graph.

- **Forward-mode blueprint authoring with a new chapter.** Per the
  Phase 6+ convention. The chapter's dep-graph is the lemma index;
  this file does not duplicate it. Modelled on
  `chapter/pebble-game.tex`'s opener form.

## Layer 0 audits (first non-opener commit)

Before any Lean code lands, three short audits whose outcome
controls Layers 1–2's shape:

1. **`Sym2 V` linear order.** Does mathlib provide `LinearOrder
   (Sym2 V)` from `[LinearOrder V]`? If yes, Layer 1's edge
   enumeration is a one-line `G.edgeFinset.sort` call. If no, mirror
   under `Mathlib/Data/Sym/Sym2.lean`; the order is the obvious
   "lift via `Sym2.toMultiset.lex`" or equivalent.

2. **`runPebbleGame_correct` factoring through a `-With` statement.**
   Phase 9's wrapper-level correctness theorem is stated against
   `runPebbleGame` (math-layer). A clean Phase 10 needs the same
   theorem stated against `runPebbleGameWith` with caller-supplied
   `toSucc` / edge-list parameters, so both `runPebbleGame` and the
   new `runPebbleGameExec` derive as one-line corollaries. Audit:
   does the existing proof factor cleanly, or does Layer 2 need to
   re-prove correctness from scratch? Expected outcome: clean
   factoring; the existing proof already routes through
   `runPebbleGameWith_*` helper lemmas.

3. **Structural-outList option.** Per the *Architectural choices*
   entry above, the wrapper-only path is the default. The audit
   step is verifying that nothing in the algorithm-side proofs
   requires the structurally-bundled `outList` field — i.e. that
   `runPebbleGameExec` plugged with `outListSorted` and its
   agreement witness composes cleanly with the existing
   `tryReachPebbleWith` / `tryAddEdgeWith` / `runPebbleGameWith`
   statements. Expected outcome: yes, the workhorses are already
   universally-quantified over `succ` / `toSucc`.

Outcomes recorded inline in this file under *Decisions made during
this phase* once each audit closes.

## Lemma checklist

**Maintained in the blueprint, not here.** The Phase 10 dep-graph
in `chapter/executable.tex` is the authoritative lemma index;
walking the leaf-most red node green per commit is the forward-mode
discipline.

## Decisions made during this phase

### Phase-local choices and proof techniques

- **Layer 0 audit #1 (revised at Layer 1) — `LinearOrder (Sym2 V)`:
  no mirror, sort via `Lex (V × V)` instead.** The audit's original
  outcome was "mirror needed" via the pullback of the `α × α`-lex
  order along `Sym2.sortEquiv`. Implementing the mirror surfaced a
  structural blocker the audit had missed: mathlib's
  `Mathlib/Data/Sym/Sym2.lean` already registers
  `instance : PartialOrder (Sym2 α) := .ofSetLike (Sym2 α) α` (the
  SetLike-derived subset order — non-total since `s({1,2})` and
  `s({1,3})` are incomparable as sets), so a competing
  `LinearOrder (Sym2 V)` cannot be registered without colliding with
  the SetLike one. The principled response is to skip the mirror
  entirely and sort the `Sym2 V → V × V` inf/sup projection through
  `Lex (V × V)` (which has `Prod.Lex.instLinearOrder` from mathlib).
  Layer 1's `edgeListSorted` composes
  `G.edgeFinset.image (fun e => toLex (e.inf, e.sup))
  : Finset (Lex (V × V))` with `Finset.sort (· ≤ ·) : List (Lex (V
  × V))` and `List.map ofLex` to land in `List (V × V)`. The same
  membership characterisation `(u, v) ∈ edgeListSorted G ↔ u ≤ v ∧
  s(u, v) ∈ G.edgeFinset` falls out, without any new instance file
  under `CombinatorialRigidity/Mathlib/`.

- **Layer 0 audit #2 — workhorse-level factoring: clean.** The
  substantive content of Phase 9's correctness chain
  (`runPebbleGame_sound`, `runPebbleGame_underline_eq_edgeFinset`,
  `runPebbleGame_eq_none_imp_exists_witness`, `runPebbleGame_correct`)
  is already at workhorse level: each piece routes through
  `runPebbleGameWith_*` lemmas universally-quantified over
  `toSucc`/`h_toSucc`. The wrapper layer only adds **three
  discharges** for the `Quot.out`-projected edge list: no-loops
  (from `not_isDiag_of_mem_edgeSet`), pairwise Sym2-distinctness
  (from `Finset.nodup_toList` + the `Quot.out_eq` round-trip), and
  the Sym2-image round-trip
  `(edges.map s(·,·)).toFinset = G.edgeFinset`. Layer 2 lifts the
  three theorems to workhorse-level statements parametrised over
  those three discharges; both `runPebbleGame` and the new
  `runPebbleGameExec` re-derive as one-line corollaries plugging
  in `Quot.out`-style and `Sym2.sortEquiv`-style discharges
  respectively. No re-proving of the algorithm-side content.

- **Layer 0 audit #3 — structural-outList option: not needed.**
  Every workhorse in `PebbleGame/Algorithm.lean` and
  `PebbleGame/Correctness.lean` (`tryReachPebbleWith`,
  `tryAddEdgeWith`, `runPebbleGameWith` and their per-step /
  per-fold reachability, underline, sparsity, isSome, and
  failure-witness lemmas) is already universally-quantified over
  the caller-supplied `succ`/`toSucc` and agreement witness
  `h_succ`/`h_toSucc`. `tryReachPebbleWith` is invoked twice
  inside `tryAddEdgeWith` and the agreement witness threads
  uniformly through the recursion. No structural `outList` field
  on `PartialOrientation` is needed; Layer 1's `outListSorted`
  slots in directly as
  `toSucc := fun D' v => (D'.outNbhd v).sort (· ≤ ·)` with the
  agreement proof `mem_outListSorted`.

- **Layer 3 IsSparse-decidability: `Fact (ℓ < 2 * k)`, not an explicit
  hypothesis.** The pebble game requires the matroidal regime
  `ℓ < 2 * k` (Phase 7 + Phase 9). For the canonical `Decidable
  (G.IsSparse k ℓ)` to be discoverable by typeclass synthesis (so
  `#eval (decide …)` / `native_decide` fire on a bare goal), the
  hypothesis must enter via a typeclass argument. The mathlib idiom
  is `[Fact (ℓ < 2 * k)]` — caller-supplied via
  `instance : Fact (3 < 2 * 2) := ⟨by omega⟩` at concrete
  parameters (or generically when needed). A non-instance `def`
  taking an explicit hypothesis would have forced every callsite to
  rebuild the `Decidable` by hand, defeating the purpose of
  registering it. The IsTight / IsLaman corollaries inherit the
  same `Fact` plumbing; the Laman case at `(k, ℓ) = (2, 3)` will
  ship a top-level `instance : Fact (3 < 2 * 2)` so callers see a
  zero-hypothesis `Decidable G.IsLaman`.

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN

- *`LinearOrder.lift'` on a `SetLike` type silently breaks
  `Decidable (· ≤ ·)`* → TACTICS-QUIRKS § 22 (rescue pattern: sort
  through `Lex (β)` projection, or register on `Lex (α)` instead;
  Layer 1 example: `SimpleGraph.edgeListSorted` in
  `PebbleGame/Exec.lean`).
- *Exactly one canonical `Decidable` instance per project predicate;
  competing brute-force registrations would race for typeclass priority
  and silently expose the slow reduction path* → DESIGN.md *One
  `Decidable` instance per project predicate* (Layer 3 example:
  `SimpleGraph.instDecidableIsSparse` in `PebbleGame/Exec.lean`).

### Cleanup pass summaries

*(Not applicable until after phase close.)*

## Blockers / open questions

- **Layer 0 audits.** ✓ Resolved by the audit-commit. Outcomes
  recorded under *Decisions made during this phase* above; audit
  \#1's outcome was revised at Layer 1 — see the bullet there.

- **`apnelson1/Matroid` non-`module` boundary.** Phase 10's new
  files import only `Sparsity.lean`, `CountMatroid.lean`, and the
  `PebbleGame/` chain — none of which depend on the
  `apnelson1/Matroid` library directly. The CLI binary (`Main.lean`)
  imports the new `Exec.lean` but should not transitively pull in
  the non-`module` `Matroid.Representation.Map`. Verify in the
  lakefile audit step that the executable target builds cleanly.

- **Blocking-witness extraction at the CLI failure branch.** Phase 9
  deferred this; whether the failure-witness `V'` from
  `runPebbleGame_eq_none_imp_exists_witness` extracts computably
  depends on whether `reachClosure` (which uses
  `Classical.decPred`) can be replaced by a computable closure
  routine for the CLI output path. If yes, ship the witness in CLI
  output; if no, stay with `NOT_SPARSE` and document the residual
  gap as a follow-up.

- **Native binary entrypoint shape.** Whether `lake exe pebble-game`
  reads from a positional file argument or stdin (or both) is a
  small CLI choice settled at Layer 5; documented here so the next
  agent does not re-litigate.

## Hand-off / next phase

**Next concrete commit:** close Layer 3 — register the canonical
`Decidable G.IsLaman` instance in `PebbleGame/Exec.lean` as a one-line
corollary at `(k, ℓ) = (2, 3)`. Since `IsLaman := IsTight 2 3` is an
`@[expose] def`, the body unfolds to a call site of
`instDecidableIsTight`; a top-level
`instance : Fact (3 < 2 * 2) := ⟨by omega⟩` ships alongside so the
Laman case is zero-hypothesis at call sites. Flip the
`def:isLaman-decidable` blueprint node's `\lean{...}` and `\leanok` in
the same commit. After Laman lands, Layer 3 closes and Layer 4
(`PebbleGame/Examples.lean` — the four `#eval`-able worked examples
from the chapter, $K_4 \setminus e$ / Moser spindle / $K_4$ / a
5-vertex path) becomes the next concrete commit.

Phase 10 closes when:
- `chapter/executable.tex`'s dep-graph is fully `\leanok`-green;
- `#eval` of `decide G.IsLaman` on a concrete `Fin n` graph
  produces the expected `Bool` and reduces through compiled
  `runPebbleGameExec`;
- `lake exe pebble-game` reads a sample edge-list file and prints
  the expected accept/reject;
- the four user-facing status surfaces (ROADMAP, README,
  home_page, blueprint intro) reflect Phase 10 ✓.

No follow-up phase is queued. Possible directions surfacing during
Phase 10:
- **Blocking-witness extraction in CLI output** (if deferred from
  this phase): finish the computable `reachClosure` and surface the
  witness on `NOT_SPARSE` rejection.
- **Component pebble game** (still deferred from Phase 9): the
  $O(n^2)$ speedup via union pair-find (L-S §5,
  Lee–Streinu–Theran 2005). Out of scope for Phase 10; the basic-
  algorithm Decidable instance already satisfies Phase 10's
  end-to-end-executability target.
- **Benchmarks** against a brute-force `Decidable` baseline on
  small graphs as a sanity check on the polynomial-time claim.
  Useful but not load-bearing; could land as a `bench/` directory.
