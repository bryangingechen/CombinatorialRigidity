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

Layer 0 audits closed (see *Decisions made during this phase*
below): the `LinearOrder (Sym2 V)` mirror is needed under
`Mathlib/Data/Sym/Sym2/Order.lean`; the Phase 9 correctness proof
factors cleanly through workhorse-level statements; the
structural-`outList` option is not needed. Layer 1 (computable
list views `outListSorted` / `edgeListSorted` + membership lemmas)
is unblocked and is the next concrete commit.

The phase target is **end-to-end executability** of the pebble game:
a computable wrapper `runPebbleGameExec` whose body avoids
`Finset.toList` / `Quot.out` (the two `noncomputable`-introducing
primitives in Phase 9's math-layer `runPebbleGame`), a `Decidable
G.IsSparse k ℓ` instance backed by it (in the matroidal regime
`ℓ < 2k`), the corollary instances `Decidable G.IsTight` /
`Decidable G.IsLaman`, `#eval`-able worked examples on `Fin n`
graphs, and a `lake exe rigidity` CLI binary that reads a graph file
and decides.

At the end of Phase 10, `#eval (decide (G.IsLaman))` on a concrete
small graph and `lake exe rigidity input.txt` should reduce through
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

- **Edge enumeration via `Finset.sort` over `Sym2 V`, not via
  `Quot.out`.** Phase 9's `runPebbleGame` projects `Sym2 V → V × V`
  via `Quot.out` (noncomputable, uses `Classical.choice`). For
  `[LinearOrder V]` the right replacement is `Finset.sort`-based
  enumeration of `G.edgeFinset` keyed on a `LinearOrder (Sym2 V)`
  instance, projecting each edge to its lex-smallest ordered pair.
  Whether mathlib already provides `LinearOrder (Sym2 V)` is part of
  the Layer 0 audit; if not, mirror under
  `Mathlib/Data/Sym/Sym2.lean`.

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
  exe rigidity`, `by decide` — share the *function body* but route
  through different backends (bytecode interp / native code /
  kernel small-step reduction). All three reduce the *same*
  computable `runPebbleGameExec`; the kernel-reduction path is
  impractically slow on real graphs, so worked examples in
  `Examples.lean` use `#eval` (or `native_decide` for theorem-level
  needs, which trusts the compiled binary identically to the CLI).
  This table reads as a user-facing explainer, not a project-
  internal decision; it lands in `chapter/executable.tex` rather
  than here.

- **CLI is `Fin n`-only and ships a tiny line-oriented parser.**
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
    exe rigidity` entry point.
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

- **Layer 0 audit #1 — `LinearOrder (Sym2 V)`: mirror needed.**
  Mathlib `Mathlib/Data/Sym/Sym2/Order.lean` provides `Sym2.inf`,
  `Sym2.sup`, and `Sym2.sortEquiv : Sym2 α ≃ { p : α × α // p.1 ≤
  p.2 }` from `[LinearOrder α]`, but no `LinearOrder (Sym2 V)`
  instance. The mirror lives under
  `CombinatorialRigidity/Mathlib/Data/Sym/Sym2/Order.lean` and
  defines the linear order as the pullback of the `α × α`-lex
  order along `sortEquiv.toFun` (equivalently, the lex order on
  `(s.inf, s.sup)`). Layer 1's `edgeListSorted` then composes
  `G.edgeFinset.sort (· ≤ ·) : List (Sym2 V)` with the `Sym2 V →
  V × V` projection `fun e => (e.inf, e.sup)` from `sortEquiv`.

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

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN

*(Empty at phase open.)*

### Cleanup pass summaries

*(Not applicable until after phase close.)*

## Blockers / open questions

- **Layer 0 audits.** ✓ Resolved by the audit-commit. Outcomes
  recorded under *Decisions made during this phase* above.

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

- **Native binary entrypoint shape.** Whether `lake exe rigidity`
  reads from a positional file argument or stdin (or both) is a
  small CLI choice settled at Layer 5; documented here so the next
  agent does not re-litigate.

## Hand-off / next phase

**Next concrete commit:** open Layer 1 — mirror
`LinearOrder (Sym2 V)` under
`CombinatorialRigidity/Mathlib/Data/Sym/Sym2/Order.lean` (as the
pullback of the lex order on `α × α` along `Sym2.sortEquiv`), then
add `outListSorted` / `edgeListSorted` definitions and their
membership / round-trip lemmas to a new
`CombinatorialRigidity/PebbleGame/Exec.lean` (or fold the list
views into `PebbleGame/Basic.lean` if that turns out cleaner once
they're written). Forward-mode discipline: the leaf-most red node
in `chapter/executable.tex` is `def:outListSorted`; flip its
`\lean{...}` and `\leanok` in the same commit as the Lean lands.

Phase 10 closes when:
- `chapter/executable.tex`'s dep-graph is fully `\leanok`-green;
- `#eval` of `decide G.IsLaman` on a concrete `Fin n` graph
  produces the expected `Bool` and reduces through compiled
  `runPebbleGameExec`;
- `lake exe rigidity` reads a sample edge-list file and prints
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
