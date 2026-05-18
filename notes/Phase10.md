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

All five forward-work layers (plus Layer 0 audits) landed; phase
closed. The end-to-end-executability target is met: the computable
wrapper `runPebbleGameExec`, the three canonical `Decidable`
instances (`IsSparse` / `IsTight` / `IsLaman` — the last
zero-hypothesis via a top-level `Fact (3 < 2 * 2)`), Layer 4's
worked `#eval` examples, and the `lake exe pebble-game` CLI binary
all reduce through the same compiled `runPebbleGameExec` body.
`chapter/executable.tex`'s dep-graph is fully `\leanok`-green. The
phase did *not* mirror anything under `Mathlib/` (Layer 0 audit \#1
revised outcome: the `Sym2 V` linear-order slot is occupied by
mathlib's SetLike-derived `PartialOrder (Sym2 α)`, so Layer 1 sorts
via the `Lex (V × V)` projection of `(e.inf, e.sup)` instead). Both
witness-extraction halves (failure-branch blocking $V'$,
success-branch orientation $D$) were deferred and became the focus
of Phase 11. Per-layer landings in *Layer plan* below;
phase-shape decisions in *Architectural choices*.

## Architectural choices made up front

These extend `../DESIGN.md` *Choices to revisit*; if any turns out
wrong, revisit there.

- **Computable plug-in via `[LinearOrder V]`, not via a structural
  `outList` field on `PartialOrientation`.** Phase 9's
  `outList := (D.outNbhd v).toList` inherits `noncomputable` from
  `Finset.toList`. The minimal repair is a new `outListSorted` via
  `Finset.sort (· ≤ ·)` paired with `mem_outListSorted`, plugged
  into the `-With` workhorses via their universally-quantified
  `toSucc` parameter — no structural change to
  `PartialOrientation`. Alternative (`outListInternal : V → List V`
  field with `Nodup` + agreement invariant) rejected as more
  invasive and duplicating state derivable from `arcs`. Layer 0
  audit \#3 confirmed the wrapper-only path is sufficient.

- **Edge enumeration via `Finset.sort` on the `Lex (V × V)`
  projection of `G.edgeFinset`, not via `Quot.out`.** Phase 9's
  `runPebbleGame` uses `Quot.out` (noncomputable). For
  `[LinearOrder V]` the right replacement is the `Sym2.sortEquiv`
  forward direction `e ↦ (e.inf, e.sup)` viewed as `Lex (V × V)`
  (where `Prod.Lex.instLinearOrder` fires), then `Finset.sort
  (· ≤ ·)` + `List.map ofLex` to land in `List (V × V)`. Sorting
  `G.edgeFinset` directly via `LinearOrder (Sym2 V)` is structurally
  blocked — see Layer 0 audit \#1 outcome below.

- **One `Decidable` instance per project predicate, pebble-game-
  backed.** `IsSparse`, `IsTight`, `IsLaman` each get exactly one
  registered `Decidable` instance in `PebbleGame/Exec.lean`, backed
  by `runPebbleGameExec` via the Phase 9 correctness theorem.
  Competing brute-force registrations (e.g. via
  `Fintype.decidableForallFintype`) are forbidden — valid same-Prop
  `Decidable`s, but exponential, and typeclass search would silently
  pick the slow path. Promoted to DESIGN.md *One `Decidable`
  instance per project predicate*.

- **Runtime / backend matrix to surface in the blueprint, not in
  these notes.** Three invocation paths (`#eval decide …`, `lake
  exe pebble-game`, `by decide`) share the function body but route
  through different backends (bytecode / native / kernel
  small-step). The table is a user-facing explainer and lands in
  `chapter/executable.tex`, not here.

- **CLI is `Fin n`-only and ships a tiny line-oriented parser,
  exposed as `lake exe pebble-game`.** Hyphenated Lake target name
  (matching `chapter/pebble-game.tex` and the `lake exe
  checkdecls`-style convention) chosen over the original placeholder
  `rigidity`. Input format: leading `n m` line + `m` edge lines, two
  whitespace-separated integers each. No named-vertex support, no
  `.dimacs` / `.graphml`. Output: trichotomy label on stdout. Witness
  extraction was in scope to attempt during Layer 5 but explicitly
  not committed to; Layer 5 shipped the label alone and punted both
  witness halves to Phase 11.

- **New files.** `CombinatorialRigidity/PebbleGame/Exec.lean`
  (computable wrappers + `Decidable` instances, below
  `PebbleGame/Correctness.lean` in the import graph),
  `CombinatorialRigidity/PebbleGame/Examples.lean` (`#eval` worked
  examples), `Main.lean` (`lake exe pebble-game` entry point), and
  `blueprint/src/chapter/executable.tex` (forward-mode dep-graph,
  per Phase 6+ convention; modelled on `chapter/pebble-game.tex`'s
  opener form).

## Layer 0 audits — outcomes

Three short audits closed in the first non-opener commit before
Layer 1 Lean lands. (1) `Sym2 V` linear order: *original audit
question, revised at Layer 1 — no mirror, sort via `Lex (V × V)`*.
(2) `runPebbleGame_correct` factoring through a workhorse-level
restatement: *clean factoring; the existing proof already routes
through `runPebbleGameWith_*` lemmas universally-quantified over
`toSucc`/`h_toSucc`*. (3) Structural-`outList` option: *not needed;
the workhorses are already universally-quantified over the caller-
supplied `succ`/`toSucc`*. Full outcome write-ups in *Decisions
made during this phase* below.

## Layer plan

- **Layer 0** ✓. Phase opener: notes, ROADMAP §10 + status row,
  README / home_page / intro.tex flips, the
  `chapter/executable.tex` shell opener. No substantive Lean.

- **Layer 1** ✓. `PartialOrientation.outListSorted` /
  `mem_outListSorted` and `SimpleGraph.edgeListSorted` /
  `mem_edgeListSorted` in `PebbleGame/Exec.lean` — the four
  blueprint nodes `def:outListSorted`, `lem:mem-outListSorted`,
  `def:edgeListSorted`, `lem:mem-edgeListSorted`. Plus three
  discharge lemmas (`edgeListSorted_no_loops` /
  `edgeListSorted_pairwise` / `edgeListSorted_map_sym2_toFinset`)
  packaging the no-loops / pairwise-Sym2-distinct / Sym2-image
  round-trip witnesses that `runPebbleGameWith_correct` consumes.

- **Layer 2** ✓. The four workhorse-level theorems
  (`runPebbleGameWith_underline_eq` in `Algorithm.lean`;
  `runPebbleGameWith_sound`,
  `runPebbleGameWith_eq_none_imp_exists_witness_empty`,
  `runPebbleGameWith_correct` in `Correctness.lean`) parametrised
  over caller-supplied `toSucc` / `edges` plus the three Layer 1
  discharges — blueprint node `thm:runPebbleGameWith-correct`. The
  four math-layer wrappers re-derive cleanly via the
  `Quot.out_eq`-derived discharges; only
  `runPebbleGame_underline_eq_edgeFinset` pays the three-discharge
  proof, the rest reuse it. Layer 2 closes with the exec-layer
  wrapper `runPebbleGameExec` + the certificate-form
  `runPebbleGameExec_correct` (`def:runPebbleGameExec`,
  `thm:runPebbleGameExec-correct`).

- **Layer 3** ✓. `SimpleGraph.instDecidableIsSparse` /
  `instDecidableIsTight` / `instDecidableIsLaman` in `Exec.lean`,
  the first two hypothesised on `[LinearOrder V]` / `[Fintype V]` /
  `[Fintype G.edgeSet]` plus `[Fact (ℓ < 2 * k)]`. The IsLaman
  variant is zero-hypothesis via a top-level
  `instance : Fact (3 < 2 * 2) := ⟨by omega⟩`. Bodies are
  `decidable_of_iff` chains routing through `runPebbleGameExec_correct`
  + (for IsTight) a `Set.ncard` ↔ `Finset.card` bridge via
  `ncard_edgeSet_eq_card_edgeFinset` + `Nat.card_eq_fintype_card`.
  Blueprint nodes `def:isSparse-decidable`, `def:isTight-decidable`,
  `def:isLaman-decidable` all `\leanok`-green.

- **Layer 4** ✓. `PebbleGame/Examples.lean` ships the four
  blueprint-prescribed worked examples (`k4MinusE`, `moserSpindle`,
  `k4`, `path5`) with their `DecidableRel _.Adj` instances and the
  eleven `#eval (decide …)` lines for `IsLaman` / `IsSparse` /
  `IsTight` plus edge-count sanity. All reduce through the compiled
  `runPebbleGameExec` body in sub-second wall time, recorded as
  `lake build` `info` diagnostics.

- **Layer 5** ✓. `Main.lean` ships the `lake exe pebble-game` entry
  point: parses an edge-list file (leading `n m` header + `m` edge
  lines; blank/`#`-commented lines tolerated anywhere via a
  `stripComments` pre-pass), builds a `SimpleGraph (Fin n)` via
  `SimpleGraph.fromEdgeSet`, and dispatches on `decide G.IsLaman`
  then `decide (G.IsSparse 2 3)` to print `LAMAN` /
  `SPARSE_NOT_TIGHT` / `NOT_SPARSE`. Lake target registered in
  `lakefile.toml` as `[[lean_exe]] name = "pebble-game"`. Four
  sample input files under `examples/`. Error paths exercised
  end-to-end (missing file, no args, malformed header,
  out-of-range vertex label, declared edge-count mismatch). Both
  witness-extraction halves deferred to Phase 11.

## Lemma checklist

**Maintained in the blueprint, not here.** The Phase 10 dep-graph
in `chapter/executable.tex` is the authoritative lemma index;
walking the leaf-most red node green per commit is the forward-mode
discipline.

## Decisions made during this phase

### Phase-local choices and proof techniques

- **Layer 0 audit #1 (revised at Layer 1) — `LinearOrder (Sym2 V)`:
  no mirror, sort via `Lex (V × V)` instead.** Original outcome was
  "mirror needed" via the `α × α`-lex pullback along
  `Sym2.sortEquiv`. Implementing it surfaced a structural blocker:
  mathlib's `Mathlib/Data/Sym/Sym2.lean` already registers
  `instance : PartialOrder (Sym2 α) := .ofSetLike (Sym2 α) α` (the
  non-total SetLike-derived subset order), so a competing
  `LinearOrder (Sym2 V)` cannot land without slot collision. Layer
  1's `edgeListSorted` composes `G.edgeFinset.image (fun e =>
  toLex (e.inf, e.sup)) : Finset (Lex (V × V))` with `Finset.sort
  (· ≤ ·)` and `List.map ofLex` to land in `List (V × V)`; the same
  membership characterisation falls out, no new `Mathlib/` mirror.
  Promoted to TACTICS-QUIRKS § 22 (see *Promoted* below).

- **Layer 0 audit #2 — workhorse-level factoring: clean.** Phase 9's
  correctness chain (`runPebbleGame_sound`,
  `_underline_eq_edgeFinset`, `_eq_none_imp_exists_witness`,
  `_correct`) is already at workhorse level. The wrapper layer only
  adds **three discharges** for the `Quot.out`-projected edge list:
  no-loops (from `not_isDiag_of_mem_edgeSet`), pairwise
  Sym2-distinctness (from `Finset.nodup_toList` + `Quot.out_eq`
  round-trip), and Sym2-image round-trip
  `(edges.map s(·,·)).toFinset = G.edgeFinset`. Layer 2 lifts the
  theorems to `*With`-level statements parametrised over those three
  discharges; both `runPebbleGame` and `runPebbleGameExec` re-derive
  as one-line corollaries.

- **Layer 0 audit #3 — structural-outList option: not needed.**
  Every workhorse in `PebbleGame/{Algorithm, Correctness}.lean` is
  already universally-quantified over the caller-supplied
  `succ`/`toSucc` and agreement witness; the agreement witness
  threads uniformly through the recursion (`tryReachPebbleWith` is
  invoked twice inside `tryAddEdgeWith`). Layer 1's `outListSorted`
  slots in directly as `toSucc := fun D' v => (D'.outNbhd v).sort
  (· ≤ ·)` with `mem_outListSorted`. No structural change to
  `PartialOrientation`.

- **Layer 3 `IsSparse`-decidability: `Fact (ℓ < 2 * k)`, not an
  explicit hypothesis.** The pebble game requires the matroidal
  regime `ℓ < 2 * k`. For typeclass synthesis to discover the
  canonical `Decidable (G.IsSparse k ℓ)` (so bare-goal
  `#eval (decide …)` / `native_decide` fire), the hypothesis enters
  via `[Fact (ℓ < 2 * k)]` — the mathlib idiom. A non-instance `def`
  taking an explicit hypothesis would force every callsite to
  rebuild the `Decidable` by hand. The IsTight / IsLaman corollaries
  inherit the same `Fact` plumbing; the Laman case at `(2, 3)`
  ships a top-level `instance : Fact (3 < 2 * 2)` in `Exec.lean` so
  callers see a zero-hypothesis `Decidable G.IsLaman`.

- **Layer 5 `Main.lean` is non-`module`, by design.** The CLI uses
  plain `import` rather than the project's `module` + `public import`
  pattern. Non-`module` files freely import `module` files (per
  `CombinatorialRigidity/CLAUDE.md` *Module-system conversion*); the
  module system's value proposition (opaque public/private library
  interfaces) does not apply to an executable with no downstream Lean
  importers.

- **Layer 5 CLI input format: blank/`#`-commented lines tolerated
  anywhere.** `Main.lean`'s `stripComments` pre-pass drops
  blank-after-trim or `#`-leading lines anywhere in the file,
  matching the `examples/*.txt` convention (each sample leads with a
  `#`-commented narrative giving the expected classification, so the
  samples double as self-documenting test cases). The blueprint
  *CLI binary* spec's *non-comment* wording covers the permissive
  read.

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

- **Phase 10+11 cleanup round, D2: `notes/Phase10.md` compression
  (546 → ~330 LoC, within the adaptive 250-350 budget).** Matched
  the Phase 11 D1 template: *Current state* collapsed from a
  ~170-LoC per-layer narrative to a ~15-LoC summary pointing at a
  new *Layer plan* section (per-layer landing record) and
  *Architectural choices*; the substantive landing detail (file
  paths, lemma names) lives in *Layer plan*. *Architectural
  choices* trimmed where individual entries duplicated Layer 0
  audit outcomes recorded in *Decisions made* (the
  `LinearOrder (Sym2 V)` slot-conflict story is now cross-referenced,
  not restated). *Hand-off / next phase*'s Phase-11-candidate
  paragraph collapsed to a pointer at `notes/Phase11.md`. Hand-off
  contract passes: *Current state* + *Layer plan* +
  *Hand-off / next phase* identify the next-phase candidates
  without reading source.

## Blockers / open questions

All Phase 10 blockers closed in-phase. (i) **Layer 0 audits** —
resolved by the audit commit; outcomes under *Decisions made*
above. (ii) **`apnelson1/Matroid` non-`module` boundary** —
resolved at Layer 5: `Main.lean` imports only
`CombinatorialRigidity.PebbleGame.Exec`, transitively pulling
`Laman` + `Sparsity` + `PebbleGame/`, none of which touch
`apnelson1/Matroid`; the `LinearRigidityMatroid.lean` non-`module`
island stays isolated. (iii) **Witness extraction (both halves)**
— deferred from Phase 10 to Phase 11 (failure-branch blocking $V'$
on `NOT_SPARSE` + success-branch orientation $D$). The CLI ships
the trichotomy label alone for Phase 10. Phase 11 closed both
halves; see `notes/Phase11.md`. (iv) **Native binary entrypoint
shape** — settled at Layer 5: positional file-path argument, no
stdin; out-of-range vertex labels and edge-count mismatches are
hard errors with stderr diagnostics and exit 1.

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

**Natural next direction — Phase 11: witness extraction.** Both
witness-extraction halves (failure-branch blocking subset $V'$,
success-branch orientation $D$) deferred during Layer 5 are
Phase 11's substantive work; full layer plan + landing record in
`notes/Phase11.md`. Other directions explored at round close
(component pebble game $O(n^2)$ via union pair-find,
Lee--Streinu--Theran 2005 §5; benchmarks harness against a
brute-force baseline) are not queued and not load-bearing — pick
at the Phase 10+11 cleanup-round close if any becomes ready.
