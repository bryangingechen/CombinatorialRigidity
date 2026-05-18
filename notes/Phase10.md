# Phase 10 — Executable pebble game (work log)

**Status:** complete.

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

Phase 10 is closed. All six layers landed: Layer 0 audits closed,
Layer 1 (computable list views) landed, Layer 2's workhorse-level
correctness restatement landed and Layer 2 itself closed via the
exec-layer wrapper `runPebbleGameExec` plus its certificate-form
correctness theorem, Layer 3 closed with the three canonical
`Decidable` instances, Layer 4 (worked `#eval` examples) closed —
`CombinatorialRigidity/PebbleGame/Examples.lean` ships the four
blueprint-prescribed worked examples (`k4MinusE`, `moserSpindle`,
`k4`, `path5`) with their `DecidableRel _.Adj` instances and the
corresponding `#eval (decide …)` lines for `IsLaman` / `IsSparse`
/ `IsTight` plus edge-count sanity (all eleven `#eval`s reduce
through the compiled `runPebbleGameExec` body in sub-second wall
time, recorded as `lake build` `info` diagnostics) — and Layer 5
(the CLI binary) closed. The canonical `Decidable (G.IsSparse k ℓ)`,
`Decidable (G.IsTight k ℓ)`, and `Decidable G.IsLaman` instances
are all registered, with a top-level `instance : Fact (3 < 2 * 2)`
making the Laman case zero-hypothesis at call sites. Witness
extraction (both the failure-branch blocking subset and the
success-branch orientation) is deferred to follow-up Phase 11;
see *Hand-off / next phase* below. Per the revised Layer 0 audit
\#1 outcome below, there is **no `Mathlib/` mirror** for Phase 10:
mathlib's existing
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

Layer 3 closes with `SimpleGraph.instDecidableIsLaman` in `Exec.lean`,
under `[LinearOrder V]` / `[Fintype V]` / `[Fintype G.edgeSet]`
hypotheses only — *no caller-supplied `Fact`*. Since
`IsLaman := IsTight 2 3` as an `@[expose] def`, the instance body is
the one-liner `inferInstanceAs (Decidable (G.IsTight 2 3))`; the
matroidal-regime witness at the Laman parameters is supplied by a new
top-level `instance : Fact (3 < 2 * 2) := ⟨by omega⟩` registered in
`Exec.lean` after `instDecidableIsTight`. The combined effect: callers
writing `#eval (decide G.IsLaman)` see a zero-hypothesis `Decidable`
without needing to register their own `Fact`. The new top-level
import `CombinatorialRigidity.Laman` adds no cycle — `Laman.lean`
depends only on `Sparsity` and mathlib, neither of which touches the
pebble game. Smoke-tested via
`#eval (decide ((⊤ : SimpleGraph (Fin 2)).IsLaman))` → `true`
($K_2$, $1 = 2 \cdot 2 - 3$ edges),
`#eval (decide ((⊤ : SimpleGraph (Fin 4)).IsLaman))` → `false`
($K_4$, $6 > 5$),
`#eval (decide ((⊥ : SimpleGraph (Fin 2)).IsLaman))` → `false`
(0 edges $\ne 1$), and
`#eval (decide ((⊥ : SimpleGraph (Fin 4)).IsLaman))` → `false`
(0 edges, not sparse, not tight). All four reduce through the
compiled `runPebbleGameExec` body in sub-second wall time. The
blueprint node `def:isLaman-decidable` is now `\leanok`-green.

Layer 5 — the CLI binary — closes the end-to-end-executability target.
The new top-level `Main.lean` ships the `lake exe pebble-game` entry
point: it parses an edge-list file (leading `n m` header, then `m`
edge lines, with blank/`#`-commented lines tolerated anywhere), builds
a `SimpleGraph (Fin n)` via `SimpleGraph.fromEdgeSet`, and dispatches
on `decide G.IsLaman` then `decide (G.IsSparse 2 3)` to print one of
`LAMAN` / `SPARSE_NOT_TIGHT` / `NOT_SPARSE`. The classification routes
through the same compiled `runPebbleGameExec` body as the Layer 4
`#eval`s. The Lake target is registered in `lakefile.toml` as a
`[[lean_exe]]` block (name = `"pebble-game"`, root = `"Main"`) and
builds against the existing `CombinatorialRigidity` library; no new
project-internal imports beyond `PebbleGame.Exec`. Four sample input
files ship under a new `examples/` directory matching the Layer 4
example set: `k4-minus-e.txt` (→ `LAMAN`), `moser-spindle.txt` (→
`LAMAN`), `k4.txt` (→ `NOT_SPARSE`), and `path5.txt` (→
`SPARSE_NOT_TIGHT`); each runs in sub-second native wall time on a
developer laptop. Error paths are exercised end-to-end (missing file,
no args, malformed header, out-of-range vertex label, declared
edge-count mismatch) and each produces a clear stderr diagnostic with
a non-zero exit. Blocking-witness extraction on the `NOT_SPARSE`
branch is **deferred** (Phase 10 *Architectural choices* originally
flagged this as in-scope-to-attempt but not committed-to): the
`Reach`-closure underlying `runPebbleGame_eq_none_imp_exists_witness`
still uses `Classical.decPred`, so surfacing the witness computably
would require porting that closure to a verified-iterative form
analogous to `reachableFinding` (the Phase 9 DFS warmup). That
follow-up is reasonable next-phase work and is recorded under
*Blockers / open questions* below; the CLI ships `NOT_SPARSE` alone
for now. The new `Main.lean` deliberately stays non-`module`-style
(plain `import`s; no `module` marker) — it has no downstream Lean
importers and module-system discipline gates only the project's
library boundary, not the executable wrapper.

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

- **Layer 4 worked examples: `public meta import` for `#eval` access
  to `Decidable` instances.** Phase 10's `Decidable` instances live
  in `PebbleGame/Exec.lean` (a `module` file with
  `@[expose] public section`), but `#eval` synthesises its decidable
  instances at *meta time* — and a plain `public import X` does not
  expose `X`'s declarations to the importing file's meta-time
  elaboration. Symptom on `#eval (decide G.IsLaman)` from a `module`
  file: *"Invalid `meta` definition `_eval`, `instDecidableIsLaman`
  is not accessible here; consider adding `public meta import
  CombinatorialRigidity.PebbleGame.Exec`"*. The fix is to add the
  second-form import — a `module` file may carry both
  `public import X` (for compile-time, runtime visibility) and
  `public meta import X` (for `#eval` / `#check` / other elaboration
  commands). The Layer-4 file `PebbleGame/Examples.lean` does exactly
  this; the pattern is the closest mathlib precedent is
  `Mathlib/Tactic/Check.lean` and friends (which carry `public meta
  import` for tactic-bearing imports). The alternative — dropping
  `PebbleGame/Examples.lean` from the `module` system — was rejected
  to keep the project's uniform module convention (per
  `PERFORMANCE.md` F3.5).

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

- **Layer 5 `Main.lean` is non-`module`, by design.** The CLI entry
  point uses plain `import` rather than the project's standard
  `module` + `public import` pattern. Non-`module` files can freely
  import `module` files (per `CombinatorialRigidity/CLAUDE.md`
  *Module-system conversion*), so the build is unaffected; and the
  module system's value proposition (opaque public/private interfaces
  between library modules) does not apply to an executable wrapper
  with no downstream Lean importers.

- **Layer 5 CLI input format: blank/`#`-commented lines tolerated
  anywhere.** The `Main.lean` `stripComments` pre-pass drops lines
  that are blank-after-trim or start with `#`, *anywhere in the file*.
  Matches the project's `examples/*.txt` convention (each sample
  leads with a `#`-commented narrative giving the expected
  classification, so the sample files double as self-documenting test
  cases). The blueprint *CLI binary* spec was not explicit about
  comment-line handling; the permissive read stays within its
  *non-comment* content wording.

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
- *`#eval`-bearing `module` files need a `public meta import` next to
  their `public import` to expose the imported `Decidable` instances
  to `#eval`'s meta-time elaboration* → TACTICS-QUIRKS § 23
  *`#eval`-bearing `module` files need `public meta import` for the
  imported `Decidable` / elaboration instances* (Layer 4 example:
  `CombinatorialRigidity/PebbleGame/Examples.lean`).

### Cleanup pass summaries

*(Not applicable until after phase close.)*

## Blockers / open questions

- **Layer 0 audits.** ✓ Resolved by the audit-commit. Outcomes
  recorded under *Decisions made during this phase* above; audit
  \#1's outcome was revised at Layer 1 — see the bullet there.

- **`apnelson1/Matroid` non-`module` boundary.** ✓ Resolved at
  Layer 5: the `lake exe pebble-game` target builds cleanly. The new
  `Main.lean` imports only `CombinatorialRigidity.PebbleGame.Exec`,
  which transitively pulls in `Laman` + `Sparsity` + the `PebbleGame/`
  chain — none of which touch `apnelson1/Matroid`. The
  `LinearRigidityMatroid.lean` non-`module` island stays isolated.

- **Witness extraction (both halves).** *Deferred from Phase 10 to
  Phase 11.* Two halves: (a) the failure-branch blocking subset
  $V'$ on the CLI's `NOT_SPARSE` output (the underlying
  `Reach`-closure in `runPebbleGame_eq_none_imp_exists_witness` uses
  `Classical.decPred`; surfacing the witness computably needs a
  verified-iterative port of `reachClosure` analogous to
  `Search/DFS.lean`'s `reachableFinding`), and (b) the success-branch
  orientation witness $D$ returned by `runPebbleGameExec`. The CLI
  ships `LAMAN` / `SPARSE_NOT_TIGHT` / `NOT_SPARSE` alone for now.
  See *Hand-off / next phase* below.

- **Native binary entrypoint shape.** ✓ Settled at Layer 5: positional
  file-path argument, no stdin support. Blank and `#`-commented lines
  are tolerated anywhere in the file; out-of-range vertex labels and
  edge-count mismatches are hard errors with stderr diagnostics and
  exit 1.

## Hand-off / next phase

Phase 10 is closed. The end-to-end-executability target is met: the
computable wrapper `runPebbleGameExec`, the three canonical
`Decidable` instances, Layer 4's worked `#eval` examples, and the
`lake exe pebble-game` CLI binary all reduce through the same
compiled body; `chapter/executable.tex`'s dep-graph is fully
`\leanok`-green; and the four user-facing status surfaces
(`ROADMAP.md` *Status* table + §10 prose, `README.md` *Project
status*, `home_page/index.md` *Project status* + phase table,
`blueprint/src/chapter/intro.tex` §*Phase plan* + enumerate +
dep-graph line) are all flipped to ✓ in this closing commit.

**Natural next direction — Phase 11: witness extraction.** Two
witness-extraction halves were left on the table during Phase 10:
(a) the **failure-branch blocking subset $V'$** on the CLI's
`NOT_SPARSE` output (the underlying `Reach`-closure in Phase 9's
`runPebbleGame_eq_none_imp_exists_witness` currently uses
`Classical.decPred`, so surfacing the witness computably requires
porting `reachClosure` to a verified-iterative form analogous to
the `Search/DFS.lean` `reachableFinding` Phase 9 warmup), and
(b) the **success-branch orientation witness $D$** (the partial
orientation packaged into the `some` branch of
`runPebbleGameExec`'s return; surfacing it usefully on the
`LAMAN` / `SPARSE_NOT_TIGHT` branches likely needs API for
inspecting / printing the orientation). The full layer plan for
this work belongs in the Phase 11 opener (`notes/Phase11.md`),
not here.

**Other possible directions** (not queued, not load-bearing):

- **Component pebble game** (still deferred from Phase 9): the
  $O(n^2)$ speedup via union pair-find (L-S §5,
  Lee–Streinu–Theran 2005). Out of scope for Phase 10; the basic-
  algorithm Decidable instance already satisfies Phase 10's
  end-to-end-executability target.
- **Benchmarks** against a brute-force `Decidable` baseline on
  small graphs as a sanity check on the polynomial-time claim.
  Useful but not load-bearing; could land as a `bench/` directory.
