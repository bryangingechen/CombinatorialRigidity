# Phase 9 cleanup round — work log

**Status:** in progress.

This is the inter-phase cleanup round after Phase 9 closed. See
`../CLEANUP.md` for the round-level operating manual: when to run a
round, the three audit categories (A blueprint-divergence, B
code-smell, C long-proof, D project-organization), and the
per-round workflow. The task list below is the round's "lemma
checklist" equivalent — populated up front per CLEANUP.md's *Sweep
first, fix later* + *Task list discipline* so a session that runs
out of time can hand off cleanly.

Phase 9 added two new files of substantial size — `Search/DFS.lean`
(~770 LoC) and `PebbleGame.lean` (~2500 LoC) — plus a 1459-line
`notes/Phase9.md` that ran far past the 250-LoC soft budget. The
round therefore scopes A–D to the **Phase 9 surface** (the two new
files + new blueprint chapters `chapter/dfs.tex` and
`chapter/pebble-game.tex` + the Phase 9 attribution in
`chapter/rigidity-matroid.tex` / `chapter/count-matroid.tex` if
present) plus a focused D pass to discharge the Phase9.md
compression debt. Project-wide drift was discharged by the Phase 7
and Phase 8 cleanup rounds; Phase 9's contributions to FRICTION /
TACTICS-* (5 resolved FRICTION entries + TACTICS-QUIRKS § 19) are
already lifted in-commit.

The accompanying **perf pass** opens in a parallel work log
(`Phase9-perf.md`); module-system conversion of the two new files
+ the broader cleanup-round-flagged structural levers route through
that pass per `../CLEANUP.md` *What a cleanup round is not* (not a
performance pass).

## Current state

Buckets A + B + C fully closed; bucket D in progress — D1 landed
(notes/Phase9.md compressed 1484 → 381 LoC, sub-organized per
`../notes/CLAUDE.md`, no remaining duplication between *Current
state* / *Architectural choices* / *Decisions made* / *Hand-off*).
D1's commit also lifts the soft length budget in `../notes/CLAUDE.md`
to an adaptive form (short phases sit at 100–200 lines, long phases
at 350–450); Phase 9 calibrates the upper end. D4 closed as no-op:
the three Phase-9-resolved items the round opener parked on D4
(`PartialOrientation V` representation, matroidal-corollary
placement, termination measure) were never queued in `DESIGN.md`
*Choices to revisit* — they lived in `notes/Phase9.md`'s own
*Blockers / open questions* from the start. The full re-skim of
*Choices to revisit*'s 9 entries (8 resolved, 1 open) confirmed no
Phase-9 flips needed, and *Pebble-game style island* was already
Phase-9-calibrated by forward-work commits `9e0ded7` (*-With*
variant pattern) + `b3bfe77` (orientation-indexed `toSucc`). D2,
D3, D5 still to do.
Bucket C's long-proof audit landed
two Lean simplifications. (i) The 11-line `|V'| ≥ 2` derivation
duplicated at `independent_brings_pebble_simpleGraph_form` and
`tryAddEdgeWith_eq_none_imp_exists_witness` case5 collapses to a
one-liner via `Finset.one_lt_card.mpr`, lifted to TACTICS-GOLF § 3
*Search mathlib before mirroring* as a worked example.
(ii) The `tryAddEdgeWith.induct` case3/case4 shared 8-line
preamble across three proofs (six copies, ~48 LoC of duplication)
collapses to one-line `r.reachable_newOrient_of_addEdgePred hD
h_outle` calls via a new `TryReachPebbleResult` helper at
`PebbleGame.lean:1111` — the let-bound `P` problem flagged in
the original audit (forcing a definitional refactor of
`tryAddEdgeWith`) was sidestepped by baking `P`'s specific
lambda directly into the helper's parameter type, which
defeq-unifies with the `.induct` case-binder. Net ~46 LoC saved
across the three consumers; technique lifted to TACTICS-GOLF § 9
*Bake let-bound predicate shapes into helper signatures*.
Refactor (ii) landed in this round after `../CLEANUP.md`'s
*Not a refactor pass* exclusion was relaxed mid-round per the
*Workflow* rule-3 augmentation. All other top-10 PebbleGame
entries and top-6 DFS entries cleared as audit-only. Buckets A + B
detail:
both blueprint chapters track the Lean faithfully, the iff red
node is now green, the SimpleGraph-vs-multi-graph regime
correspondence is documented in the chapter prose, the formalization-aside scan across both chapters surfaced
no Lean-simplification candidates, all 6 `noncomputable def` sites
are forced + minimal + workhorse-exposed, all 5 real 4+-arg `rw`
chains (the *Bucket B* table over-counted PebbleGame.lean by 1 due
to destructuring commas inside anonymous-constructor `rw` args)
are tight structural rewrites with no missing fused lemma, the
`classical` / `Fintype.ofFinite` re-grep confirms zero hits, the
section structure of both new files aligns with the blueprint
chapters (with a stale Phase-9-opening *"scaffold"* paragraph
removed from the PebbleGame.lean header + `reachClosure` added to
DFS.lean's *Main declarations* listing), and all 79 `--` comments
in the two files serve a WHY purpose (anonymous-case-dispatch
label, proof-step roadmap, or TACTICS-QUIRKS rescue cross-ref). Every aside in
`chapter/dfs.tex` + `chapter/pebble-game.tex` is either A1/A2-vetted
structural bookkeeping (`dropUntilBundle`, `DirectedWalk.mapRel`,
`D.reach` post-composition at the failure site), a
`DESIGN.md` *Pebble-game style island* design pin (the three
math-layer convenience / computable-workhorse splits +
narrative-bridge `@[deprecated]` shim), or substantive cost
disclosure that can't be eliminated at the cleanup-round level
(four-runtime-checks at the `runPebbleGame` wrapper, `Option`-vs-
`Sum` return shape on the correctness theorem, subset-form
hypothesis on `lem:pebble-game-failure-witness`, named project-
internal helper attributions in proof prose). The bucket-A audit
closes with no edits to blueprint TeX or Lean source. A2's pebble-game walk verified all 39
`\lean{...}` pins resolve (`checkdecls` green post-`inv web`); the
22 dep-graph nodes
(`def:partial-orientation` through `cor:pebble-game-countMatroid-indep`)
match Lean signatures including the unified `ℓ ≤ k|V'|` size
hypothesis on Invariants (3)/(4), the
`Reachable.{empty, reverse, addArc}` constructor preconditions, and
the broadened subset-form `\underline{D} \subseteq E(G) ∧
\{u,v\} \in E(G)` hypothesis on the failure-witness lemma. The
A1 carry-overs are discharged: both "planned `reachClosure`
helper" mentions (in `def:tryAddEdge` and `def:runPebbleGame`) now
point at the shipped math-layer accessor
`PartialOrientation.reach` (a `Finset V`-wrapped reflexive-
transitive closure wrapping `Search.reachClosure`). No new
`\uses{}` edges added — the chain through `lem:pebble-game-invariants`
+ `lem:pebble-game-independent-brings-pebble-graph` already covers
the math content; surfacing `reachClosure` as its own dep-graph
node would add a low-content bookkeeping entry per the "What to
include vs. skip → structural support, churn-prone" rule.

A2-followup discharged: `lem:pebble-game-tryAddEdge-iff-independent`
(chapter line 768) now pins to a narrative-bridge `@[deprecated]`
shim `PartialOrientation.tryAddEdge_isSome_iff_sparse`
(`PebbleGame.lean:2149`) per `blueprint/CLAUDE.md`
*Narrative-bridge corollaries*. The shim is a one-step wrapper-
form combination of `tryAddEdgeWith_isSome` (⇐) and
`tryAddEdgeWith_isSparse` (⇒) under `toSucc := outList`, marked
`@[deprecated tryAddEdgeWith_isSparse (since := "narrative-bridge")]`
to discourage callsite proliferation in favour of the two halves.
Statement: `(∃ D', D.tryAddEdge ... = some D') ↔ G.IsSparse k ℓ`
under the shared per-edge preconditions (matroidal regime
`ℓ < 2k`, reachability, freshness, `G.edgeFinset = insert s(u,v)
D.underline`). Lemma + proof environments both flipped to `\leanok`;
dep-graph turns green for the node and the chapter is fully green.

A3 discharged: the chapter's opening `\emph{Multigraphs.}`
paragraph now walks L-S Lemma 10 through Lemma 15 in flowing prose
(40-line paragraph), with `\cref{}` anchors into the chapter's
individual lemma blocks rather than a separate bullet inventory.
The user-judgement iteration on the original bullet-list audit
subsection ("more naturally with the rest of the prose") replaced
the inventory format with a paragraph matching the chapter's
`\emph{Out of scope.}` convention. The Phase9.md *Blockers*
prediction (Lemma 10 cleared, Lemmas 13–15 "expected to clear
similarly") is discharged in writing: every L-S lemma in the
matroidal regime specialises directly to SimpleGraph land, with
Invariant (1)'s loop-free `span(v) = 0` collapse and the
size-hypothesis unification `ℓ ≤ k|V'|` as the only two regime
differences. Lemma 15's full sparse/tight/spanning classification
and Corollary 11's block characterisation both route through the
component pebble game (L-S §5, out of Phase 9 scope per chapter
intro). No Lean changes — audit-only per architectural choice #3.

## Architectural choices made up front

These extend `../DESIGN.md` *Choices to revisit*; if any turns out
wrong, revisit there.

- **Scope A–D to Phase 9 surface.** Same rationale as Phase 8-cleanup:
  the project-wide backlog of classical / Fintype / `change` /
  `noncomputable` / `rw`-chain smells was discharged by Phase 7-cleanup.
  Re-running those project-wide would be ~80% re-audit of closed
  resolutions; the marginal find rate doesn't justify it. Buckets A–D
  therefore restrict to the new files (`Search/DFS.lean` +
  `PebbleGame.lean`) and the new blueprint chapters
  (`chapter/dfs.tex` + `chapter/pebble-game.tex`).
- **Bucket D carries Phase9.md compression debt.** At 1459 LoC,
  `notes/Phase9.md` is ~6× over the 250-LoC soft budget — the
  largest single overflow in the project's history. The
  *Current state* commit-narrative and the *Hand-off / next phase*
  recap are both candidates for collapse to per-blueprint-node
  bullets now that the chapter is closed. This is a substantive
  D-bucket task; budget ~1 session.
- **Audit-only for the multigraph corner-case check.** Phase 9's
  architectural choice #1 committed to `SimpleGraph V` + `ℓ < 2k`,
  while Lee--Streinu state results for multi-graphs with loops in
  `ℓ ∈ [0, 2k)`. The formalization landed end-to-end, but a
  defensive statement-by-statement audit of L--S Lemmas 10--15
  against the simple-graph regime is nominally open per
  Phase9.md's *Blockers / open questions*. Lives as A3 below;
  audit-only (document what's used in what regime), not a
  refactor — any actual multi-graph lift is its own (multi-phase)
  project.
- **Perf pass separate.** Module-system conversion of the two new
  files routes through `Phase9-perf.md` per `../CLEANUP.md` *What a
  cleanup round is not*. Cleanup commits can incidentally reduce
  per-file build time but don't measure it; the 4-run A/B protocol
  in `PERFORMANCE.md` is the right gate.
- **Each fix as its own commit.** A cleanup commit obeys the same
  per-commit friction review and build/lint gates as a forward-work
  commit. Cleanup-round value is the trail of small principled
  commits, not a single mega-commit.

## Task checklist

### Bucket A — Blueprint ↔ Lean divergence audit (Phase 9 surface)

- [x] **A1:** `chapter/dfs.tex` ↔ `Search/DFS.lean` walk. Three
  dep-graph nodes: `def:directed-walk`, `def:reachable-finding`,
  `thm:reachable-finding-correct` (plus any newer additions for the
  `reachClosure` / `DirectedWalk.mapRel` family). For each:
  - confirm the `\lean{...}` pin resolves;
  - compare blueprint statement form against Lean signature
    (hypotheses, conclusion form, implicit/explicit binders);
  - re-read prose proof and flag any "the Lean does X via Y where Y
    is harder than X" pattern per `../CLEANUP.md` §A.
  Watch for: the `DirectedWalk.dropUntilBundle` `Subtype`-bundled
  truncation being honestly flagged as a Lean-side bookkeeping
  device (math has implicit truncation, Lean needs the bundle); the
  inner length-induction in `reachableFindingAux_complete` being
  presented faithfully (not glossed over as a one-step argument).

  **Disposition.** All five pinned names resolve under
  `CombinatorialRigidity.Search` (`DirectedWalk`,
  `DirectedWalk.IsPath`, `reachableFinding`, `reachableFinding_sound`,
  `reachableFinding_complete`). Statement forms are faithful:
  the inductive `DirectedWalk` realises the prose "non-empty list
  of vertices satisfying $R\,v_i\,v_{i+1}$"; `IsPath` ≡
  `vertices.Nodup` realises "simple"; `reachableFinding`'s
  `Option (Σ w, DirectedWalk ... v w)` return realises the
  "$\mathrm{some}\,(p, w)\,/\,\mathrm{none}$" prose with a harmless
  presentation gap (prose pair-order `(p, w)` vs Lean's Σ-encoding
  `⟨w, p⟩`); the soundness+completeness multi-pin matches the
  prose's enumerated parts. Prose proof faithfully tracks the Lean:
  outer `reachableFindingAux.induct` (3-case visited / `P v` / else)
  ↔ "outer auto-induction on the DFS recursion"; inner
  `induction n with | zero | succ ih_inner` length bound ↔
  "inner induction on the walk-length bound"; `dropUntilBundle` in
  the `v ∈ p'.vertices` branch honestly flagged as Lean-side
  bookkeeping per `../CLEANUP.md` §A;
  `Relation.ReflTransGen.head_induction_on` lifting in
  `reachableFinding_complete` ↔ prose "lifts to an explicit
  $R$-walk by head-first induction on $\mathrm{ReflTransGen}$".
  No A1-internal Lean simplification opportunities (the flagged
  bookkeeping is structural, not friction). No Lean or blueprint
  changes from A1's own scope; two carry-overs surface for A2,
  recorded inline under A2 below.
- [x] **A2:** `chapter/pebble-game.tex` ↔ `PebbleGame.lean` walk.
  ~20 dep-graph nodes covering: `def:partial-orientation`,
  `def:pebble-counts`, `def:path-reversal`, `def:arc-insertion`,
  `def:reachable-orientation`, `lem:pebble-game-invariants`,
  `def:tryReachPebble`, `def:tryAddEdge`, `def:runPebbleGame`,
  `lem:runPebbleGameWith-underline-subset`,
  `lem:runPebbleGame-underline-eq`, `lem:span-eq-ncard-edgesIn`,
  `thm:pebble-game-soundness`,
  `lem:pebble-game-independent-brings-pebble` (+ -graph variant),
  `lem:pebble-game-tryAddEdgeWith-isSome`,
  `lem:pebble-game-tryAddEdgeWith-isSparse`,
  `lem:pebble-game-tryAddEdge-iff-independent`,
  `lem:pebble-game-failure-witness`, `thm:pebble-game-correct`,
  `cor:pebble-game-countMatroid-indep`. Same three checks per node
  as A1. Watch for: the `Reachable.{...}` invariant lemmas being
  honestly stated under the unified `ℓ ≤ k * V'.card` hypothesis
  (not L--S's regime-split form, see Phase9.md *Decisions →
  Reachability and the four invariants*); the `(V × V)`-list vs
  `(Sym2 V)`-list `runPebbleGameWith` shape being faithfully
  described (or honestly flagged as a `-With`-pattern bookkeeping
  device).

  **Carry-overs from A1 (DFS chapter walk).**
  - `chapter/pebble-game.tex` refers to `reachClosure` twice as a
    *"planned helper"* — once in the `def:tryAddEdge` prose
    ("a planned `reachClosure` helper post-composed at the failure
    site") and once in `def:runPebbleGame` ("deferred to a planned
    `reachClosure` helper, consumed by
    `lem:pebble-game-failure-witness`"). The helper has shipped in
    `Search/DFS.lean` (`reachClosure` + `mem_reachClosure` /
    `self_mem_reachClosure` / `reachClosure_closed`). Update the
    pebble-game prose to drop the "planned" qualifier; the
    follow-up question of whether to surface `reachClosure` as a
    dep-graph node in `chapter/dfs.tex` (so the pebble-game prose's
    `\uses{}` chain can thread through it) is an A2 call. Note
    that the actual blocking-witness extraction in
    `PebbleGame.lean` is `tryReachPebbleWith_eq_none_imp_no_reachable`
    / `runPebbleGame_eq_none_imp_exists_witness`; the chapter's
    *Blocking witness* machinery may have evolved past the
    "planned helper" framing entirely.
  - `chapter/pebble-game.tex` mentions `DirectedWalk.mapRel`
    inline at the `def:tryReachPebble` Lean-encoding aside
    ("transported from `reachableFinding`'s walk on the
    out-neighbour-list relation via `DirectedWalk.mapRel`").
    Honestly flagged, no fix needed.
  - `DirectedWalk.arcsFinset` / `reversedArcsFinset` and their
    `IsPath`-form filter-count lemmas are purely Lean-side
    structural support for `def:path-reversal` and are not
    surfaced in blueprint prose. Per *What to include vs. skip*
    (structural support, churn-prone), skip dep-graph entry; flag
    only if the A2 prose walk surfaces a `\uses{}` chain that
    would benefit from one.

  **Disposition.** All 39 pinned names (across 22 nodes) resolve
  via `checkdecls` post-`inv web` against the current `module`-
  converted Lean. Statement-form check: faithful across the board.
  Highlights of the walk:
  - `def:reachable-orientation`'s constructor preconditions match
    `Reachable.{empty,reverse,addArc}` exactly (`hw : D.out w < k`
    for reversal tail; `huv, hnotin, hnotin_rev, hu_out, hk` for
    arc insertion).
  - `lem:pebble-game-invariants` honestly states Invariants (1)/(2)
    unconditionally and (3)/(4) under the unified
    `h_size : ℓ ≤ k * V'.card` premise, matching the chapter's
    "$\ell \le k|V'|$" prose. No regime-split form lurks in either.
  - `lem:runPebbleGameWith-underline-subset`'s prose-level
    "$\{s(u, v) : (u, v) \in \mathit{edges}\}$" matches the Lean's
    `(edges.map (fun p => s(p.1, p.2))).toFinset`; the per-step
    accept-branch glue `tryAddEdgeWith_underline` returns
    `Dmid.underline = insert s(u, v) D.underline` exactly as the
    prose says.
  - `lem:pebble-game-failure-witness`'s broadened subset-form
    hypothesis (`\underline{D} \subseteq E(G)` plus `\{u,v\} \in E(G)`,
    not the tight equality) matches the Lean's `h_uv, h_sub`
    arguments and supports the fold-level consumer at intermediate
    `runPebbleGame` steps.
  - `cor:pebble-game-countMatroid-indep`'s statement form
    `(countMatroid V k ℓ hℓ).Indep G.edgeSet ↔ ∃ D, runPebbleGame G
    k ℓ = some D` matches the Lean theorem at
    `PebbleGame.lean:2489` (under `_root_.SimpleGraph`).

  Prose proof structure tracks the Lean's `induct`-based
  five-case dispatch on `tryAddEdgeWith` and the structural
  recursion on `edges` for the fold-level lemmas.

  **Carry-over fixes landed:** the two "planned `reachClosure`
  helper" mentions are updated to point at the shipped math-layer
  accessor `PartialOrientation.reach` (defined at
  `PebbleGame.lean:1863` as `reachClosure (fun a b => (a, b) ∈ D.arcs) v`).
  `DirectedWalk.mapRel` mention in `def:tryReachPebble` is
  honestly flagged; `arcsFinset` family stays Lean-side structural.

  **Surfaced follow-up — closed (option 2).**
  `lem:pebble-game-tryAddEdge-iff-independent` (chapter line 768)
  now pins to a narrative-bridge `@[deprecated]` shim
  `tryAddEdge_isSome_iff_sparse` at `PebbleGame.lean:2149`. See
  *Surfaced follow-ups* below for the closing entry.
- [x] **A3:** Multigraph corner-case audit (audit-only, no
  refactor). Walk L--S Lemmas 10--15 statement by statement against
  the simple-graph regime. Document each lemma in the blueprint as
  *either*: (i) stated in a form whose simple-graph specialization
  is exactly what `PebbleGame.lean` proves, with `span(v) = 0`
  collapsing the loop-counted term where applicable; *or* (ii)
  L--S's multi-graph form is strictly more general and Phase 9
  proves a strict specialization (note the difference inline). The
  Phase9.md *Blockers* prose claims Lemma 10 already cleared and
  Lemmas 13--15 "expected to clear similarly" — this audit
  discharges that prediction in writing.

  **Disposition.** The expanded `\emph{Multigraphs.}` paragraph at
  the head of `chapter/pebble-game.tex` (lines 39--79) walks
  Lemma~10 through Lemma~15 in flowing prose, with `\cref{}`
  anchors into the chapter's individual lemma blocks rather than a
  separate bullet inventory. Disposition by L--S statement: (a)
  Lemma~10's Invariant~(1) collapses to `peb(v) + out(v) = k` in
  the loop-free regime (`span(v) = 0`); Invariants~(2)--(4) match
  identically with the size split `n' ≥ 1` / `n' ≥ 2` unified to
  `ℓ ≤ k|V'|` since both ranges of L--S imply it. (b) Lemma~13
  matches identically; the SimpleGraph form
  (`independent_brings_pebble_simpleGraph_form`) discharges the
  `|V'| ≥ 2` half of the size split automatically from `u ≠ v` and
  `ℓ < 2k`. (c) Lemma~14's iff is the narrative-bridge shim
  `tryAddEdge_isSome_iff_sparse` (A2-followup); two halves
  individually formalised. (d) Lemma~15's full input-graph
  classification (under-/well-/over-constrained) specialises in
  this chapter to `runPebbleGame_correct`'s certificate form;
  well-/over-constrained sub-classifications need the component
  pebble game's `I`-component apparatus (L--S~\S~5, out of Phase~9
  scope per chapter intro). (e) Corollary~11 similarly part of the
  component pebble game apparatus, out of scope. No Lean changes —
  audit-only per architectural choice #3. The user-judgement
  iteration on the prose ("more naturally with the rest of the
  prose") replaced the original bullet-list audit subsection with
  the flowing-prose `\emph{Multigraphs.}` paragraph format
  matching the chapter's `\emph{Out of scope.}` convention.
- [x] **A4:** Formalization-aside scan. Re-skim
  `chapter/pebble-game.tex` (and `chapter/dfs.tex`) prose proofs for
  asides flagging Lean-side bookkeeping (custom `Equiv`s,
  named-helper one-step substitutes, case-splits the Lean had to
  take that the math wouldn't). Each is a candidate for either Lean
  simplification (collapse the aside) or a more concrete
  formalization-cost note (make the residual cost honest). Per
  `../blueprint/CLAUDE.md` *Proof verbosity* the bias is *Lean
  simplification first, prose aside only if simplification fails*.

  **Disposition.** Catalog of asides across both chapters, grouped
  by classification, with the Lean-simplification analysis recorded
  in-line so the next round doesn't re-litigate.

  Group 1 — A1/A2-pre-vetted:
  - `DirectedWalk.dropUntilBundle` truncation aside in the inner-
    induction step of `thm:reachable-finding-correct` (`dfs.tex:103`).
    A1 vetted: `Subtype`-bundled walk truncation is structural
    bookkeeping (math has implicit truncation; Lean needs the bundle
    to thread the length-bound and vertex-subset witnesses). No Lean
    simplification surfaced.
  - `DirectedWalk.mapRel` relation-transport aside in
    `def:tryReachPebble` (`pebble-game.tex:330`). A2 vetted:
    `reachableFinding` walks the out-neighbour-list relation;
    `tryReachPebble` walks `D`'s arc relation; the two are
    propositionally equal under the agreement witness but
    definitionally distinct, so a transport step is needed.
    Eliminating would require refactoring `reachableFinding` to
    take a propositional agreement witness, restructuring the DFS
    API; out of scope at the cleanup-round level.
  - `D.reach` materialisation at the failure site in
    `def:tryAddEdge` (`pebble-game.tex:399--404`). A2 carry-over fix:
    the math-layer accessor wraps `Search.reachClosure`; merging
    into `tryReachPebbleWith`'s return type would change the
    algorithm's interface from `Option (PartialOrientation V)` to a
    sum carrying the blocking-witness subset on failure. Out of
    scope; cf. the parallel Option-vs-Sum aside below.

  Group 2 — `DESIGN.md` *Pebble-game style island* design pins:
  - `tryReachPebbleWith` / `tryReachPebble` split (`pebble-game.tex
    :333--347`); `tryAddEdgeWith` / `tryAddEdge` split
    (`386--405`); `runPebbleGameWith` / `runPebbleGame` split
    (`437--455`). All three are math-layer convenience wrappers
    around a computable workhorse parameterised by a caller-supplied
    `succ` / `toSucc` function. The `noncomputable` wrappers plug in
    `D.outList` / `Finset.toList` / `Quot.out`; the workhorses stay
    fully computable for IO callers. Explicit project-wide
    convention in `DESIGN.md`; eliminating the asides would mean
    revising that convention, which is a forward-looking question
    for a future phase, not a cleanup-round task.
  - Narrative-bridge `@[deprecated]` shim aside on
    `lem:pebble-game-tryAddEdge-iff-independent` (`pebble-game.tex
    :810`). A2-followup, user-selected option 2; explicit project
    convention in `blueprint/CLAUDE.md` *Narrative-bridge
    corollaries*. No simplification candidate.

  Group 3 — substantive design rationale (residual cost):
  - Four-runtime-checks aside in `def:runPebbleGame`
    (`pebble-game.tex:456--466`). The wrapper's public signature
    takes only `G`, `k`, `ℓ`; preserving the `∀ x, out_D x ≤ k`
    invariant without runtime checks would require threading a
    `Reachable k ℓ D` instance through the input, breaking the
    "math-layer convenience" interface. The skip-on-fail behaviour
    is a no-op on well-formed input; the lemma
    `runPebbleGameWith_mem_underline` carries the no-skip-fires
    argument. Residual cost honestly disclosed; not eliminable.
  - `Option`-vs-`Sum` aside in `thm:pebble-game-correct`
    (`pebble-game.tex:940--944`). The wrapper returns `Option
    (PartialOrientation V)`; the blocking-witness subset is
    recovered by a separate post-composed theorem
    (`runPebbleGame_eq_none_imp_exists_witness`). Switching to a
    sum return type would change both the wrapper's signature and
    every downstream consumer (Phase 9's `cor:pebble-game-
    countMatroid-indep`, future `(2, 3)`-rigidity callers). Out of
    scope at the cleanup-round level.
  - Subset-form hypothesis rationale on
    `lem:pebble-game-failure-witness` (`pebble-game.tex:841--846`).
    The broadened `underline ⊆ E(G) ∧ {u, v} ∈ E(G)` form (vs the
    tight equality `E(G) = underline ∪ {{u, v}}`) was specifically
    chosen so the fold-level consumer can apply this lemma at an
    intermediate `runPebbleGame` failure step. The hypothesis form
    is load-bearing; eliminating the rationale would silently lose
    the consumer's load-path documentation.
  - Project-internal helper attributions in proof prose:
    `sum_out_eq_span_add_outOn` (`pebble-game.tex:279`),
    `pebOn_add_outOn_reverse_eq` / `pebOn_add_outOn_addArc_add`
    (`286, 288`), `peb_reverse_head` /
    `peb_reverse_of_not_endpoint` (`382--383`),
    `TryReachPebbleResult.reachable_newOrient` /
    `underline_newOrient_eq` (`860--861`),
    `span_succ_le_edgesIn_ncard_of_subset` (`876`). Per
    `blueprint/CLAUDE.md` *Be honest about formalization cost*,
    these are appropriate case-by-case helper attributions in
    multi-case proofs --- not glossing over one-step
    correspondences, but pointing the reader at named auxiliary
    lemmas the proof actually consumes. Appropriate cost
    disclosure; not aside-elimination candidates.

  Group 4 — math-side layering (not Lean cost):
  - "The last is routed through the algebraic identity [Invariant
    (2)]" in `def:path-reversal` (`pebble-game.tex:161--171`):
    subset-level `peb + out` invariance from span invariance plus
    Invariant (2); the routing is genuine math (subset-level `out`
    alone is *not* invariant under reversal).
  - Three additive identities by endpoint position in
    `def:arc-insertion` (`191--202`): faithful description of the
    insertion step's three subset-level shifts.
  - "Invariant (1) reduces to `out_D(v) ≤ k` under truncated
    $\mathbb{N}$-subtraction" in `lem:pebble-game-invariants`
    (`269--272`): notes the truncated-$\mathbb{N}$-subtraction
    semantics that turns the additive identity into the inequality.
  - "(The matroidal-regime assumption `ℓ < 2k` is not used formally
    on the Lean side ...)" in `thm:pebble-game-soundness`
    (`635--637`): honest disclosure that the size-range constraint
    folds into the definition of $(k, \ell)$-sparsity itself
    (`ℓ ≤ k|V'|`).

  Conclusion: audit closes with no Lean source or blueprint TeX
  changes. Every aside is either pre-vetted, a `DESIGN.md`-pinned
  design choice, substantive cost that can't be eliminated at the
  cleanup-round level, or genuinely mathematical layering. The
  catalog is recorded here so a future round (or a post-Phase 9
  reader) doesn't re-walk the same evaluation.

### Bucket B — Code-smell sweep (Phase 9 surface)

Initial grep results pre-sweep, restricted to `Search/DFS.lean` +
`PebbleGame.lean`:

| Smell | `Search/DFS.lean` | `PebbleGame.lean` |
|---|---|---|
| `classical` (top-level) | 0 | 0 |
| `letI`/`haveI Fintype.ofFinite` | 0 | 0 |
| `@[nolint]` / `set_option linter` | 0 | 0 |
| `noncomputable def` | 1 (L749 — `reachClosure`) | 5 (L130, L1087, L1284, L1491, L1863 — `outList`, `tryReachPebble`, `tryAddEdge`, `runPebbleGame`, `reach`) |
| `change`/`show` (coax) | 0 | 0 |
| Multi-step `rw` (4+ args, one step) | 2 (L194, L200, L285) | 4 (L260, L413, L427, L440, L932) |
| `show … from rfl` | 0 | 0 |

Phase 9's "fully-computable workhorse + noncomputable math-layer
wrapper" pattern (the `-With` variant, see `DESIGN.md` *Pebble-game
style island*) accounts for **all 6 `noncomputable def` sites** —
each is the math-layer wrapper specialising a computable workhorse
to a noncomputable enumeration (`Finset.toList` / `Quot.out` /
`Relation.ReflTransGen`). The bucket-B audit on these should
confirm the wrappers are minimal (no body content beyond the
specialisation) and the workhorses stay computable.

- [x] **B1:** `noncomputable def` audit. For each of the 6 Phase 9
  sites, confirm:
  - the `noncomputable` keyword is *forced* (try `def` and read the
    error — `Finset.toList`, `Classical.choice`-flavored
    `Quot.out`, or `Classical.decPred`-via-`Relation.ReflTransGen`);
  - the noncomputable body is a minimal one-liner around a
    computable workhorse, not duplicating logic;
  - the workhorse signature exposes everything callers need without
    going through the noncomputable wrapper.
  Documented disposition: each site to be marked *forced* or *vestigial*
  (latter unlikely given the pattern, but worth verifying).

  **Disposition.** All 6 sites *forced + minimal + workhorse-exposed*;
  no edits.
  - `Search/DFS.lean:749` — `reachClosure R v := Finset.filter
    (Relation.ReflTransGen R v) Finset.univ` (with explicit
    `Classical.decPred _` for the filter predicate). Forced by the
    absence of a general `Decidable (Relation.ReflTransGen R v w)`
    instance. One-liner; no computable workhorse needed because
    consumers route through `reachableFinding` (the verified DFS) for
    the algorithm side, and this finset is only used by the
    completeness side's blocking-witness construction.
  - `PebbleGame.lean:130` — `outList v := (D.outNbhd v).toList`.
    Forced by `Finset.toList`'s use of `Multiset.toList`'s
    `Classical.choice`-flavored `Quotient.lift`. One-liner; consumers
    that need a computable form supply their own `List`-shaped
    adjacency to the `tryReachPebbleWith` / `tryAddEdgeWith` /
    `runPebbleGameWith` workhorses.
  - `PebbleGame.lean:1087` — `tryReachPebble P v := tryReachPebbleWith
    P v D.outList (fun {_ _} => D.mem_outList)`. Forced by
    `D.outList`'s `noncomputable`. One-liner specialisation of the
    `tryReachPebbleWith` workhorse.
  - `PebbleGame.lean:1284` — `tryAddEdge ... := tryAddEdgeWith ...
    (fun D' => D'.outList) (fun D' {_ _} => D'.mem_outList)`. Forced
    by `outList`. One-liner specialisation of the `tryAddEdgeWith`
    workhorse.
  - `PebbleGame.lean:1491` — `runPebbleGame G k ℓ :=
    (empty).runPebbleGameWith k ℓ (fun D' => D'.outList) (fun D'
    {_ _} => D'.mem_outList) (G.edgeFinset.toList.map Quot.out)`.
    Forced by *both* `Finset.toList` (under `outList` and the edge
    enumeration) and `Quot.out` (the `Sym2 V → V × V` projection).
    One-liner specialisation of the `runPebbleGameWith` workhorse.
  - `PebbleGame.lean:1863` — `reach D v := reachClosure (fun a b =>
    (a, b) ∈ D.arcs) v`. Forced via `reachClosure`. One-liner
    specialisation of the `Search.reachClosure` math-layer accessor;
    used only by the completeness-side blocking-witness construction
    (`D.reach u ∪ D.reach v`).

  All six docstrings explicitly call out the noncomputable source
  and direct IO callers to the computable workhorse, consistent
  with `DESIGN.md` *Pebble-game style island* and the `-With`
  variant pattern. No vestigial sites.
- [x] **B2:** Multi-step `rw` chain audit. 6 sites (3 in DFS.lean,
  3 in PebbleGame.lean). Inspect each for a missing fused lemma —
  usually a one-line mirror under `CombinatorialRigidity/Mathlib/`.
  Per `../CLEANUP.md` table row, the common pattern is "rw chain
  across multiple structural unfolds that should compose as one
  named lemma." Phase 9's chain candidates look mostly structural
  (DFS: `mapRel` + `length` + `length` + `ih`; PebbleGame:
  `Finset.sum_congr rfl h` + `Finset.sum_const` + `smul_eq_mul` +
  `mul_comm`) — probably not mirror-eligible, but verify.

  **Disposition.** 5 real 4+-arg chains (the *Bucket B* table's
  PebbleGame count of 4 was over by 1: L413, L427, L440 are 2-arg
  `rw`s false-matched by the regex on destructuring commas inside
  `⟨_, _⟩` anonymous-constructor arguments — `rw [if_pos ⟨hmem,
  hw⟩, if_pos ⟨hmem, hu⟩]` is 2 mathematical rewrites, not 4). All
  5 real chains audited via `lean_multi_attempt` against
  `simp`/`grind`/`omega`/single-tactic candidates; no mirror-eligible
  chain surfaced.
  - `Search/DFS.lean:194` — `rw [mapRel, length, length, ih]`,
    induction step of `mapRel_length`. `simp [mapRel, length, ih]`
    also closes; same effective length, less explicit. Existing
    `rw` form stays.
  - `Search/DFS.lean:200` — `rw [mapRel, vertices, vertices, ih]`,
    induction step of `mapRel_vertices`. Same shape as L194. `simp
    [mapRel, vertices, ih]` also closes; existing form stays.
  - `Search/DFS.lean:285` — `rw [arcsFinset_cons, Finset.image_insert,
    ← ih, reversedArcsFinset_cons]; rfl`, induction step of
    `reversedArcsFinset_eq_image_swap`. `simp [arcsFinset_cons,
    reversedArcsFinset_cons, Finset.image_insert, ih]` collapses
    the `rw; rfl` pair to a single line; same lemma set, same step
    count, no fused lemma. Existing form stays — the explicit `rw`
    form makes the `Prod.swap`-defeq step (the residual `rfl`)
    visible.
  - `PebbleGame.lean:260` — `rw [Finset.sum_congr rfl h,
    Finset.sum_const, smul_eq_mul, mul_comm]` in the `pebOn +
    span + outOn = k|V'|` algebraic identity. Standard sum-of-constant
    idiom (no `Finset.sum_const_nat` substitute available — that
    lemma's signature doesn't fit). `simp [Finset.sum_congr rfl h,
    Finset.sum_const, mul_comm]` also closes; same effective form.
    Existing form stays.
  - `PebbleGame.lean:932` — `rw [pebOn_empty, outOn_empty,
    Nat.add_zero, mul_comm V'.card k]; exact h_size` in the empty
    base case of `Reachable.pebOn_add_outOn_ge`. `simp [pebOn_empty,
    outOn_empty, mul_comm V'.card k]; exact h_size` also closes;
    same line count. Existing form stays.

  False-positive sites (2-arg `rw`, regex matched on inner commas):
  - `PebbleGame.lean:413` — `· rw [if_pos ⟨hmem, hw⟩, if_pos ⟨hmem,
    hu⟩]` in `out_reverse_of_not_endpoint`'s `pos` branch. Two
    matching `if_pos` rewrites with destructured boolean witnesses;
    tight to the call site.
  - `PebbleGame.lean:427` — `rw [if_pos ⟨h_mem, h_ne⟩, if_neg
    (fun ⟨_, h⟩ => h rfl)] at h` in `out_reverse_head`. Paired
    `if_pos`/`if_neg` dispatching the same `h`-equation's two
    `if`-clauses; tight to the call site.
  - `PebbleGame.lean:440` — `rw [if_neg (fun ⟨_, h⟩ => h rfl),
    if_pos ⟨h_mem, h_ne⟩] at h` in `out_reverse_tail`. Mirror of
    L427 (swapped branches); same disposition.

  No mirror-eligible fused lemma surfaced; conclusion matches the
  pre-sweep prediction "probably not mirror-eligible".
- [x] **B3:** `classical` / `haveI Fintype.ofFinite` clean-sweep
  audit. Phase 9 chose `[Fintype V] [DecidableEq V]` as the style
  island (architectural choice #2), so we'd expect zero such
  patterns — but verify nothing crept in during the long phase.
  Initial grep returned zero hits; mark trivially closed if a
  re-grep confirms.

  **Disposition.** Re-grep confirms zero hits in either file. The
  four `grep "classical|Fintype.ofFinite"` matches are all
  doc-comment references explaining the *absence* of these patterns
  (`Search/DFS.lean:63, 737`; `PebbleGame.lean:41, 2426` — each
  pointing the reader at the style-island rationale). Trivially
  closed; no edits.
- [x] **B4:** Phase 9 file headers + section organisation review.
  Both new files run long (770 + 2500 LoC). Spot-check section
  organisation: are sections named consistently with the blueprint
  chapter structure? Are the section transitions documented in
  module docstrings? Any section over ~400 LoC that's a candidate
  for an internal split (no file-level split, just section
  reordering)?

  **Disposition.** Two edits landed; section organisation otherwise
  well-aligned.
  - **`PebbleGame.lean` header**: removed stale Phase-9-opening
    *"This file is currently a **scaffold**"* paragraph that
    described the file as a scaffold with red dep-graph nodes still
    to attack. Replaced with a one-sentence pointer to the
    forward-mode dep-graph confirming Phase 9 closed all 22 nodes.
    The "Style island" + "References" parts of the header stay
    unchanged.
  - **`Search/DFS.lean` Main declarations**: added `reachClosure`
    entry. Phase 9 added the math-layer reachability accessor
    (used by the pebble game's completeness side to build
    `D.reach u ∪ D.reach v`) but the *Main declarations* listing
    in the file header was not updated. The structural support
    (`DirectedWalk.mapRel`, `arcsFinset` / `reversedArcsFinset`
    family) stays out of the listing per A4's *Group 1* disposition
    (Lean-side bookkeeping, not blueprint-surfaced).
  - **Section structure**: both files' `/-! ## ... -/` headers
    match the blueprint chapter's section structure. DFS.lean:
    Directed walks (`def:directed-walk`), Arcs of a walk
    (structural support for `def:path-reversal`), DFS primitive
    (`def:reachable-finding`), Reachability closure (math-layer for
    the pebble-game completeness side). PebbleGame.lean: Path
    reversal (`def:path-reversal`), Arc insertion
    (`def:arc-insertion`), Reachability + invariants
    (`def:reachable-orientation`, `lem:pebble-game-invariants`),
    Try-reach-pebble (`def:tryReachPebble`), Try-add-edge
    (`def:tryAddEdge`), Run-pebble-game (`def:runPebbleGame`),
    Soundness (`thm:pebble-game-soundness`), Completeness (towards
    `lem:pebble-game-failure-witness`), Correctness theorem
    (`thm:pebble-game-correct`), Matroidal-independence corollary
    (`cor:pebble-game-countMatroid-indep`).
  - **Section size**: PebbleGame.lean's *Completeness* section runs
    ~509 LoC (L1835--L2344) and is the only section over the
    informal 400-LoC threshold. The section runs through the
    `Reachable.pebOn_add_outOn_ge` Invariant-(3) substantive piece,
    the `outOn_reach_union_eq_zero` blocking-witness setup, the
    DFS-failure-implies-blocking-witness lemma, the per-edge
    `tryAddEdgeWith_eq_none_imp_exists_witness`, and the fold-level
    `runPebbleGameWith_eq_none_imp_exists_witness`. These are
    tightly coupled (each builds on the previous) and the section
    is the natural unit for the chapter's *Completeness* paragraph;
    splitting would scatter related lemmas across two files. No
    structural change.
- [x] **B5:** `--` comment audit. Phase 9's long files almost
  certainly accumulated some narrative `--` comments that should
  either move to module-level docstrings (`/-! ... -/`) or be
  removed per the CLAUDE.md *no comments by default* rule. Quick
  grep + walk; remove anything explaining WHAT the code does (vs
  documenting a hidden WHY).

  **Disposition.** 79 `--` comments across the two files (21 in
  DFS.lean, 58 in PebbleGame.lean); all retained, no edits. Each
  is one of:
  - **Anonymous-case-dispatch label** in a `rcases` / `rintro`
    chain or an `induction ... using funName.induct` block whose
    auto-generated case names (`case1` / `case2` / ...) carry no
    semantic content. DFS.lean L332--372 (cons-pattern subcases
    in `IsPath.notMem_*_arcsFinset`), L398--511 (induction-step
    subcases in `IsPath.card_*_filter_fst`); PebbleGame.lean
    L1209--1407 (5-case `tryAddEdgeWith` induct dispatches across
    `tryAddEdgeWith_reachable` / `_underline` / `_isSome` /
    `_eq_none_imp_exists_witness`). These give the case its
    meaning since the labels don't.
  - **Proof-step roadmap marker** in a long substantive proof.
    PebbleGame.lean L354--365 (motive-avoidance strategy in
    `out_reverse_add`), L487--544 (proof-step roadmap through the
    `D.arcs` decomposition lemmas), L1675--1703 (round-trip
    enumeration glue inside `runPebbleGame` correctness),
    L2274--2341 (substantive 70-line `case5` of
    `tryAddEdgeWith_eq_none_imp_exists_witness`, the V'-construction
    + algebraic decomposition for the blocking witness).
  - **TACTICS-QUIRKS rescue cross-reference**. PebbleGame.lean
    L628--630 cites the `subst`-direction trap (TACTICS-QUIRKS § 4)
    inline at the point of use; per `../CombinatorialRigidity/CLAUDE.md`
    *Lifted to* discipline, an in-source pointer at the use site
    is the right idiom.
  - **High-level proof-strategy preamble** at the top of a long
    proof. DFS.lean L714--724 in `reachableFinding_complete`
    (lifting `ReflTransGen` via `head_induction_on`, then
    contrapositive against `_complete` helper). PebbleGame.lean
    L582--587 in the `out_reverse_le` consequences (the unified
    equation's two `{0, 1}`-valued cases).

  All retained `--` comments serve a WHY purpose (explain a
  rationale, mark a case in an anonymous dispatch, or cross-
  reference a TACTICS-QUIRKS rescue). Removal would degrade
  proof navigability without saving meaningful prose; no
  candidate fits the *Default to writing no comments* /
  *Don't explain WHAT* bar for removal.

### Bucket C — Long-proof audit (Phase 9 surface)

Rank the top ~10 proofs in `Search/DFS.lean` + `PebbleGame.lean` by
body line count (per the crude `awk` ranking script in
`../CLEANUP.md` §C). Each proof gets four candidate questions per
the manual:
- **API extraction.** Self-contained sub-lemma other proofs would
  call separately?
- **Mathlib lemma we missed.** Run `lean_loogle` / `lean_leanfinder`
  on any 5--10+ line subblock.
- **Tactic substitution.** Could `grind only [...]` / `omega` /
  `fun_prop` collapse a multi-step `rw` chain? Use
  `lean_multi_attempt` to A/B-test without an edit-build cycle.
- **Definitional refactor.** Would a predicate reshape save the
  proof's manual unfolding?

- [x] **C1:** Top proofs ranked via a tightened awk over both
  files (the crude script in `../CLEANUP.md` §C overshoots when a
  short lemma is followed by a long unrelated block before the
  next blank line; pre-resetting on `theorem|lemma|def|...` /
  `section` / `@[` / `/-` markers gives the body-only count).

  `PebbleGame.lean` top 10, by body LoC:

  | LoC | Line | Proof |
  |---:|---:|---|
  | 148 | 2217 | `tryAddEdgeWith_eq_none_imp_exists_witness` |
  | 89  | 2035 | `tryAddEdgeWith_isSome` |
  | 80  | 1298 | `tryAddEdgeWith_reachable` |
  | 63  | 1917 | `span_succ_le_edgesIn_ncard_of_subset` |
  | 62  | 1606 | `runPebbleGameWith_mem_underline` |
  | 62  | 1544 | `runPebbleGameWith_underline_subset` |
  | 59  | 2158 | `tryAddEdge_isSome_iff_sparse` (signature + docstring; real proof 5 lines) |
  | 55  | 1980 | `Reachable.independent_brings_pebble_simpleGraph_form` |
  | 51  | 1668 | `runPebbleGame_underline_eq_edgeFinset` |
  | 49  | 2365 | `runPebbleGameWith_eq_none_imp_exists_witness` |

  `Search/DFS.lean` top 6 (body LoC ≥ 30):

  | LoC | Line | Proof |
  |---:|---:|---|
  | 60  | 656 | `reachableFindingAux_complete` |
  | 49  | 350 | `IsPath.notMem_antiparallel_arcsFinset` |
  | 47  | 591 | `reachableFindingAux_sound` |
  | 47  | 399 | `IsPath.card_arcsFinset_filter_fst` |
  | 46  | 474 | `IsPath.card_reversedArcsFinset_filter_fst` |
  | 39  | 716 | `reachableFinding_complete` |

  `tryAddEdgeWith_underline` (43 LoC, L1378) and
  `Reachable.pebOn_add_outOn_ge` (the work-log-flagged "Invariant (3)
  substantive piece") both sit just under the > 30 LoC bar in the
  body-only count — the former tracks `_reachable`'s case3/case4
  shape verbatim but with `r.underline_newOrient_eq` in place of
  the reachability-preamble; the latter weighs in at 29 LoC of body
  (just below the bar) once the awk resets on `omit`-style
  scope-opener markers.
- [x] **C2:** Walk each of C1's top PebbleGame entries through the
  four CLEANUP.md questions. Two Lean simplifications landed (the
  `Finset.one_lt_card.mpr` inline collapse and the
  `reachable_newOrient_of_addEdgePred` cross-proof unification
  helper, the latter after the CLEANUP.md *Not a refactor pass*
  rule relaxation); the rest cleared as audit-only.

  **Inline collapse landed.** The 11-line `|V'| ≥ 2` block at two
  pre-collapse sites — `Reachable.independent_brings_pebble_simpleGraph_form`
  and `tryAddEdgeWith_eq_none_imp_exists_witness` case5 — collapses
  to a single line via mathlib's
  `Finset.one_lt_card.mpr ⟨u, hu, v, hv, huv⟩`. Both blocks built
  `({u, v} : Finset V).card = 2` by hand and then routed `{u, v} ⊆
  V'` through `card_le_card` with a `Finset.mem_insert` case-split,
  missing
  `Finset.one_lt_card : 1 < s.card ↔ ∃ a ∈ s, ∃ b ∈ s, a ≠ b`
  even though the `.mp` direction was already in use in this
  project at `SparsityIComponents.lean:112, 184`. Saves 20 LoC.
  Lifted to `../TACTICS-GOLF.md § 3 Search mathlib before mirroring`
  as a worked example.

  **Per-entry walk (audit-only beyond the collapse above):**
  - `tryAddEdgeWith_eq_none_imp_exists_witness` (148 LoC) decomposes
    naturally: case1+case2 are 5 LoC of `rw` + `absurd`, case3+case4
    are ~30 LoC of shared IH-step preamble (see *Cross-proof
    unification analysis* below), case5 is ~70 LoC of substantive
    witness construction. Case5's setup — build `V'`, derive
    `D.outOn V' = 0`, prove `D.peb k w = 0` for `w ∈ V' \ {u, v}`,
    algebraic decomposition `pebOn V' = peb u + peb v`, bridge to
    `span_succ_le_edgesIn_ncard_of_subset` — is already routed
    through named auxiliaries; no further API extraction.
  - `tryAddEdgeWith_isSome` (89 LoC) and `tryAddEdgeWith_reachable`
    (80 LoC): same case1/2/3/4/5 dispatch. Case5 of `_isSome`
    discharges via `independent_brings_pebble_simpleGraph_form`
    (the named SimpleGraph wrapper around L-S Lemma 13); case5 of
    `_reachable` closes via `nomatch h`. Tight.
  - `span_succ_le_edgesIn_ncard_of_subset` (63 LoC): linear chain
    through six named auxiliaries (`h_S_sub`, `h_uv_in`,
    `h_uv_notin_S`, `h_combined_sub`, `h_card`, `h_S_card`,
    `h_finite`) into a 4-step `calc`. Each step is one named fact.
    No simplification.
  - `runPebbleGameWith_mem_underline` (62 LoC),
    `runPebbleGameWith_underline_subset` (62 LoC), and
    `runPebbleGameWith_eq_none_imp_exists_witness` (49 LoC):
    structural recursion on the `edges` list argument. Per-step:
    ~10 lines of `hcond` setup + `tryAddEdgeWith` case-match +
    invariant transport. The fold-pattern shape is intrinsic to the
    algorithm; no API extraction surfaces.
  - `tryAddEdge_isSome_iff_sparse` (59 LoC) is a narrative-bridge
    `@[deprecated]` shim — the body is a one-line `⟨..., ...⟩`
    anonymous constructor; the 59-LoC count is signature + docstring.
    No simplification.
  - `Reachable.independent_brings_pebble_simpleGraph_form` (55 LoC)
    builds `V' := D.reach u ∪ D.reach v`, derives `|V'| ≥ 2`
    (collapsed above), `D.outOn V' = 0`, the span/sparsity bound,
    and applies `independent_brings_pebble`. The rest is tight
    composition.
  - `runPebbleGame_underline_eq_edgeFinset` (51 LoC) is the
    round-trip identity for `s((Quot.out e).1, (Quot.out e).2) = e`
    composed with both halves of `runPebbleGameWith_*`. Each input
    hypothesis is named and proved in 2–5 lines.

  **Cross-proof unification helper landed.** The 8-line case3/case4
  preamble shared across `_reachable`, `_isSome`, and
  `_eq_none_imp_exists_witness` (six copies, ~48 LoC of duplication)
  collapses to a single
  `r.reachable_newOrient_of_addEdgePred hD h_outle` call via a new
  `TryReachPebbleResult` helper at `PebbleGame.lean:1111`. The helper
  bundles the `r.hP` decode (`simp only [Bool.and_eq_true,
  decide_eq_true_eq]`) plus the `D.out r.target < k` derivation
  (using `peb k w = k - D.out w` definitionally and `h_outle`) plus
  the `reachable_newOrient` application — once, instead of six times.
  The let-bound `P` problem flagged in the original audit (forcing a
  definitional refactor of `tryAddEdgeWith` to hoist `P` to a
  top-level `private def`) was sidestepped by baking the predicate's
  specific shape `fun w => decide (0 < D.peb k w) && decide (w ≠ u)
  && decide (w ≠ v)` directly into the helper's signature — at each
  callsite the `.induct`-generated case-binder `P` defeq-reduces to
  the lambda, so the helper unifies without an explicit
  `hP_def`-style equation argument or any change to `tryAddEdgeWith`
  /`tryAddEdgeWith.induct`. Net ~46 LoC saved across the three
  consumers; the helper itself is 11 LoC. The same trick would not
  apply to `tryAddEdgeWith_underline` (the fourth `.induct` proof) —
  it threads only `r.underline_newOrient_eq`, no reachability — so
  the refactor covers 3 proofs, not 4. Lifted to
  `../TACTICS-GOLF.md` §9 *Bake let-bound predicate shapes into
  helper signatures* (which uses this refactor as its worked
  example).
- [x] **C3:** Walk DFS.lean top entries. All cleared as
  audit-only.
  - `reachableFindingAux_complete` (60 LoC): three-level nested
    structure — outer `reachableFindingAux.induct` (3 cases),
    inner `induction n` (zero/succ), inner `cases p` (nil/cons).
    Each level is essential: outer follows the algorithm's
    recursion, inner-n bounds the walk-length to make the proof
    well-founded, cases p dispatches the cons head. The two inner
    `succ` sub-cases (`hv_in : v ∈ p'.vertices` revisit branch via
    `dropUntilBundle` vs `hv_in` fresh branch via the IH) are the
    DFS-completeness algebra. No API extraction.
  - `reachableFindingAux_sound` (47 LoC): mirror of `_complete`
    for the soundness direction. Same three-level structure, tight.
  - `IsPath.notMem_antiparallel_arcsFinset` (49 LoC) /
    `IsPath.card_arcsFinset_filter_fst` (47 LoC) /
    `IsPath.card_reversedArcsFinset_filter_fst` (46 LoC):
    `cons`-pattern induction on the walk with case-dispatch on
    whether source/sink coincides with the inserted-arc endpoints.
    These are the structural backbone of the `out_reverse_*`
    family in `PebbleGame.lean`; the case dispatches and the
    `h_uout_not_in` lookups are essential. No simplification.
  - `reachableFinding_complete` (39 LoC): `ReflTransGen` ⇒
    `DirectedWalk` lift via `head_induction_on`, then
    contrapositive against `reachableFindingAux_complete`. Tight.
- [x] **C4:** Cross-reference to B2. B2's bucket-disposition
  already ran `lean_multi_attempt` against the 5 real 4+-arg `rw`
  chains for `simp` / `grind` / `omega` / single-tactic candidates;
  no mirror-eligible fused lemma surfaced. Each existing `rw` form
  was kept because it makes a specific structural step visible
  (`Prod.swap`-defeq, `sum-of-constant` idiom under
  `Finset.sum_congr rfl h`, the `pebOn_empty, outOn_empty, Nat.add_zero,
  mul_comm` arithmetic chain). The C-bucket re-test would replay
  the same A/B candidates and reach the same conclusion. Closed by
  reference.

### Bucket D — Project-organization compression

- [x] **D1:** Compressed `notes/Phase9.md` from 1484 → 381 LoC.
  *Current state* collapsed to a closure paragraph + high-level
  shipped-pieces bullet list (the chapter dep-graph is the
  authoritative lemma index; pre-compression *Current state* was
  457 LoC of commit narrative duplicating per-node detail). *Hand-off
  / next phase* collapsed to forward-looking-only (the ~280-line
  pre-compression bulleted recap re-derived what *Current state* +
  *Decisions made* already covered). *Decisions made* sub-organized
  per `notes/CLAUDE.md` template into *Phase-local choices and proof
  techniques* (14 entries, each ≤ ~10 lines) + *Promoted to ...*
  (8 pointers) + *Cleanup pass summaries* (pointer to Phase9-cleanup
  and Phase9-perf). *Architectural choices* kept largely intact (6
  bullets, ~75 LoC) — these are the up-front design pins, not
  candidates for elimination. *Blockers / open questions* converted
  to a "Resolved" section with one-line pointers + brief
  disposition. **Duplication scrub:** removed matroidal-corollary
  duplication across 4 sections (kept only in *Architectural
  choices → New file `PebbleGame.lean`* + a *Blockers* pointer), the
  `[Fintype V]` style-island duplication (kept in *Architectural
  choices*, dropped from *Promoted to ...*), and the
  per-blueprint-node bullets that duplicated the chapter dep-graph.

  **Companion edit to `notes/CLAUDE.md`** *Soft length budget*: the
  prior hard 250-LoC cap punished long phases for being thorough.
  Updated to an adaptive form — short phases (5–10 forward-work
  commits) sit at 100–200 lines, long phases (20+ commits, multiple
  substantive subsystems) at 350–450 lines, with the per-entry
  ≤8-line rule + *Promoted to ...* lift discipline + hand-off-
  contract surfaces as the operative tests. Phase 9 (25 forward-work
  commits, two new files totaling ~3300 LoC, 22 dep-graph nodes)
  calibrates the upper end at 381 lines.
- [ ] **D2:** Lift-on-promotion check across Phase9.md decisions.
  The CLAUDE.md threshold is "referenced in 2+ files or by 2+
  phases." Phase 9 already lifted: 5 FRICTION entries
  ([resolved] `induction _ using funName.induct`, [resolved]
  `rw [D.field_eq]` motive, [resolved] cons-pattern endpoint subst,
  [resolved] `ring` alpha-renamed sums, [resolved]
  `Finset.toList` noncomputable), 1 TACTICS-QUIRKS section (§ 19),
  1 DESIGN.md section (*Pebble-game style island* + *The `-With`
  variant pattern*). Are there others that should lift? Candidates:
  - The `match h : ... with | pat => ...` substitution shape
    (TACTICS-QUIRKS § 17) bit Phase 9 again in the `runPebbleGame_correct`
    body — already a § entry, but does Phase 9's use add a worked
    example worth appending?
  - The `Reachable k ℓ D` non-motive threading hypothesis pattern
    (introduced before `induction _ using ... generalizing D'`) —
    cross-cutting enough to lift to TACTICS-GOLF?
  - The unified additive identity pattern for state-machine moves
    (single `if-then-else` formula keyed on the move's piecewise
    behaviour, combined with case-analysis at the call site) —
    surfaced twice in Phase 9 (path reversal + arc insertion); is
    this a TACTICS-GOLF / DESIGN.md candidate?
- [ ] **D3:** `FRICTION.md` housekeeping. Phase 9 added 5 resolved
  entries that all have post-resolution indices (mirror files or
  TACTICS-QUIRKS § references). Per the CLAUDE.md *Filing rule for
  new entries*, "migrate to `FRICTION-archive.md` on the next
  housekeeping pass once their resolution is fully indexed." Move
  Phase 9's resolved entries to archive iff their indices are stable;
  leave any whose resolution needs further eyes.
- [x] **D4:** Re-skim `../DESIGN.md` *Choices to revisit*. Phase 9
  resolved several decisions queued there:
  - `PartialOrientation V` representation (option (i) chosen,
    architectural-choice list);
  - matroidal-independence corollary placement (land in-phase, in
    `PebbleGame.lean`);
  - termination measure for `tryReachPebble` (resolved via the DFS
    warmup pattern).
  Update each entry inline; flip them to *resolved (Phase 9)* with
  a one-line pointer to the relevant Phase9.md decision section.

  **Disposition.** No-op for the three named items: all three lived
  in `notes/Phase9.md` *Blockers / open questions* from the start,
  not in `DESIGN.md` *Choices to revisit*. The round-opening task
  description over-predicted DESIGN.md as their parking lot;
  rechecking `git log -S` against `DESIGN.md` confirms none of the
  three was ever queued there. They were resolved in-phase per
  `Phase9.md` *Blockers / open questions* (currently rendered as
  *Resolved* during D1's compression).

  **DESIGN.md *Choices to revisit* re-skim, full pass.** Nine
  entries; eight already resolved (Phases 3, 4, 7, 8); one open
  (*Promoting `edgesIn` upstream*) which Phase 9 doesn't touch
  (`edgesIn` is the `Sparsity.lean` accessor; PebbleGame uses
  `D.underline` over arcs, not `edgesIn`). No flips needed.

  **DESIGN.md *Pebble-game style island* Phase-9 calibration.**
  Already Phase-9-calibrated by forward-work commits — `9e0ded7`
  (Phase 9 `tryReachPebble`) added the *`-With` variant pattern*
  paragraph; `b3bfe77` (Phase 9 `tryAddEdge`) added the
  orientation-indexed `toSucc` generalization. No cleanup-round
  edit needed.

  D5 picks up the question of whether ROADMAP should point at
  *Pebble-game style island* from its engineering-conventions
  section.
- [ ] **D5:** `ROADMAP.md` engineering-conventions re-skim. Does
  Phase 9 surface any new convention that should be documented
  there? Candidates: the `[Fintype V] [DecidableEq V]` style
  island for algorithm files (currently lives in DESIGN.md
  *Pebble-game style island*; should ROADMAP point at it from
  *Engineering conventions → Vertex types*?); the `-With` variant
  pattern (math/exec layer split for algorithms; DESIGN.md
  pin appears sufficient — verify).

## Surfaced follow-ups

- **A2-followup:** `lem:pebble-game-tryAddEdge-iff-independent`
  red-node disposition — *closed (option 2)*. User selected the
  `@[deprecated]` shim over the drop. Landed
  `PartialOrientation.tryAddEdge_isSome_iff_sparse` at
  `PebbleGame.lean:2149`, attribute
  `@[deprecated tryAddEdgeWith_isSparse (since := "narrative-bridge")]`,
  blueprint pinned + `\leanok` flipped. See *Current state* for
  the statement form and rationale; cross-references in the
  docstrings of the two halves (`PebbleGame.lean:2018, 2112`)
  remain in place.

- **C2-followup:** *closed (refactor landed)*. The cross-proof
  unification helper analysed in C2's *Cross-proof unification
  analysis* paragraph landed as
  `TryReachPebbleResult.reachable_newOrient_of_addEdgePred` at
  `PebbleGame.lean:1111`. The original audit's "out of scope"
  reading proposed hoisting `P` to a top-level `private def` —
  this commit took the lighter route of baking `P`'s specific
  lambda directly into the helper's parameter type, which
  defeq-unifies with the `.induct` case-binder without any
  change to `tryAddEdgeWith`'s body or the `.induct` signature.
  All six case3/case4 bodies migrated to a one-line
  `exact ih (r.reachable_newOrient_of_addEdgePred hD h_outle) …`
  call; net ~46 LoC saved across the three consumers. Technique
  lifted to `../TACTICS-GOLF.md` §9.

## Blockers / open questions

- Round in progress; buckets A + B + C fully closed (A1--A4 +
  B1--B5 + C1--C4 all green); bucket D in progress — D1 (Phase9.md
  compression) + D4 (`DESIGN.md` re-skim, no-op) landed; D2, D3, D5
  remain. (`checkdecls` is the always-on per-commit gate per
  `../blueprint/CLAUDE.md` *Static checks before commit*, not a
  separate task.)

## Hand-off / next phase

Round in progress. Phase 9 main is fully closed; this round
addresses the post-closure hygiene. Buckets A + B + C are green:
A1 (DFS chapter walk), A2 (pebble-game chapter walk),
A2-followup (`lem:pebble-game-tryAddEdge-iff-independent` red node,
discharged via the narrative-bridge `@[deprecated]` shim),
A3 (multigraph regime correspondence in the chapter's
`\emph{Multigraphs.}` prose), A4 (formalization-aside scan,
audit-only with the in-line catalog recording the
Lean-simplification analysis for each aside), B1 (six `noncomputable
def` sites forced + minimal + workhorse-exposed, audit-only),
B2 (five real 4+-arg `rw` chains audited against
`simp`/`grind`/`omega`/single-tactic candidates via
`lean_multi_attempt`, no missing fused lemma surfaced, audit-only),
B3 (`classical` / `Fintype.ofFinite` re-grep zero, trivially
closed), B4 (file header + section organisation review;
PebbleGame.lean header *"scaffold"* paragraph dropped +
`reachClosure` added to DFS.lean's *Main declarations*),
B5 (79 `--` comments all WHY-content, retained, audit-only),
C1 (top proofs ranked via a tightened awk over both files),
C2 (PebbleGame.lean walk — two refactors landed: the inline
`Finset.one_lt_card.mpr` collapse at two sites (lifted to
TACTICS-GOLF § 3), and the `tryAddEdgeWith.induct` case3/case4
cross-proof unification helper
`TryReachPebbleResult.reachable_newOrient_of_addEdgePred`,
~46 LoC saved across the three consumers (lifted to TACTICS-GOLF
§ 9); all other walked entries audit-only),
C3 (DFS.lean walk, all audit-only — the three-level
nested structure of `reachableFindingAux_complete` mirrors the
algorithm's recursion and isn't a candidate for compression),
and C4 (cross-reference to B2's `lean_multi_attempt` sweep) are
all green. C2-followup *closed (refactor landed)*; see
*Surfaced follow-ups* for the closing entry.

Bucket D in progress. D1 landed (Phase9.md compression 1484 → 381
LoC + adaptive notes-budget rule in `notes/CLAUDE.md`). D4 closed
no-op: the three Phase-9-resolved items the round-opener parked on
D4 (`PartialOrientation V` representation, matroidal-corollary
placement, termination measure for `tryReachPebble`) were never
queued in `DESIGN.md` *Choices to revisit* — they lived in
`notes/Phase9.md`'s own *Blockers / open questions* throughout
Phase 9; the *Choices to revisit* re-skim found no Phase-9 flips
needed, and *Pebble-game style island* was already Phase-9-
calibrated by forward-work commits. Remaining D-bucket tasks: D2
(lift-on-promotion sweep — candidates: `match h : ... with` worked
example, `Reachable k ℓ D` non-motive threading, unified additive-
identity pattern), D3 (`FRICTION.md` housekeeping — migrate Phase
9's 5 resolved entries to archive if indices stable), D5
(`ROADMAP.md` engineering-conventions re-skim — `[Fintype V]
[DecidableEq V]` style-island pointer + `-With` variant pattern).

The accompanying **Phase 9-perf** pass opens in parallel
(`Phase9-perf.md`) per `../CLEANUP.md` *What a cleanup round is
not*; structural levers (module-system conversion of the two new
files) route through that pass.
