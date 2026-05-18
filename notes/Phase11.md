# Phase 11 — Witness extraction (work log)

**Status:** complete (closed by Layer 5 commit).

This file is the per-phase work record. See `../ROADMAP.md` §11 for
the high-level plan and `../DESIGN.md` for cross-cutting design
choices.

**Workflow:** Phase 11 is a **structural-edit phase**, not the usual
new-theorem-development phase. There is *no new blueprint chapter*;
the substantive Lean work reshapes existing Phase 9/10 algorithms
(`tryAddEdge` / `runPebbleGame` / `runPebbleGameExec`) from
`Option`-shaped to verdict-bearing returns, with the matching
blueprint updates landing **in place** in `chapter/dfs.tex`,
`chapter/pebble-game.tex`, and `chapter/executable.tex` alongside
each Layer's Lean. The phase's authoritative to-do list lives in
the *Layer plan* section below, not in a blueprint chapter.
Forward-mode discipline (dep-graph as the lemma index) still
applies — but the index spans three existing chapters being
restated in step, rather than one new chapter being walked from
red to green.

**References.**
- Phase 9 (`chapter/pebble-game.tex`) carries the existence-form
  failure-witness theorem `runPebbleGame_eq_none_imp_exists_witness`
  whose `V'` is mathematically `D.reach u ∪ D.reach v`, currently
  routed through `Search.reachClosure` (noncomputable, via
  `Classical.decPred`).
- Phase 10 (`chapter/executable.tex`, `notes/Phase10.md`) closed
  end-to-end-executability but ships only the trichotomy label
  `LAMAN` / `SPARSE_NOT_TIGHT` / `NOT_SPARSE`; both witness halves
  (blocking subset on reject, orientation on accept) were
  explicitly deferred.
- D.J. Jacobs, B. Hendrickson, *An algorithm for two-dimensional
  rigidity percolation: the pebble game*, J. Comput. Phys. **137**
  (1997) 346–365 — §4 describes blocking-set extraction at failure
  as the reach-closure of the source vertices in the partial
  orientation's directed digraph.
- A. Lee, I. Streinu, *Pebble game algorithms and sparse graphs*,
  Discrete Math. **308** (2008) 1425–1437 — §3 specifies the same
  in $(k, \ell)$ generality. The algebraic content already lives in
  Phase 9's `Reachable.independent_brings_pebble`; Phase 11 lifts
  the surface return type to carry the witness as data.

## Current state

Layer 1 closed: the verified-iterative computable
`reachClosureComputable` lives in `Search/DFS.lean`, with soundness
and completeness routed through the existing `reachableFinding`
primitive (one DFS invocation per candidate vertex, filtered via
`Finset.univ.filter`). `PartialOrientation.reach` in
`PebbleGame/Correctness.lean` is redefined through it, with the
`mem_reach` iff against `Relation.ReflTransGen` preserved unchanged
so all downstream proofs (`self_mem_reach`, `reach_closed`,
`outOn_reach_union_eq_zero`, the failure-witness chain) re-derive
without modification. `Search.reachClosure` is retired (no external
consumers). Blueprint: `chapter/dfs.tex` gains the
`def:reachClosureComputable` + `lem:mem-reachClosureComputable`
nodes in a new *Reachability closure (computable)* subsection;
`chapter/pebble-game.tex` updates the `def:tryAddEdge` /
`def:runPebbleGame` prose mentioning the closure primitive to refer
to the new name.

Layer 2 closed: `WorkhorseWitness k ℓ V` lives in `PebbleGame/Basic.lean`
(outside `PartialOrientation` since it's parallel state, not derived), and
`WorkhorseWitness.certifies_against` lives in `PebbleGame/Correctness.lean`
(at end of file, after `PartialOrientation` namespace closes — since
`WorkhorseWitness` is in `_root_.CombinatorialRigidity.PebbleGame`, not under
`PartialOrientation`). The witness's `h_pebOn_le : D.pebOn k V' ≤ ℓ` field
strengthens the originally-proposed per-vertex `h_below : peb u + peb v ≤ ℓ`
to subsume the DFS-failure "no free pebble outside `{u, v}` in `V'`"
assertion: Layer 3's case-5 inline witness construction will combine the
per-vertex below-threshold with the no-free-pebble guarantee (via
`Finset.sum_eq_zero` over `V' \ {u, v}`) to build this stronger bound at
once, exactly mirroring the existing `h_zero_outside` step in
`tryAddEdgeWith_eq_none_imp_exists_witness`. The `certifies_against` proof
body is the closing algebra of that lemma, transplanted to consume the
strengthened field; no `simpleGraph_form` proof body was reused verbatim
(its conclusion goes the wrong direction — it builds a free pebble from
sparsity, whereas we need to build non-sparsity from no free pebble).
Blueprint: `chapter/pebble-game.tex` gains `def:workhorseWitness` +
`lem:workhorseWitness-certifies` immediately after
`lem:pebble-game-independent-brings-pebble-graph` in the *Completeness*
subsection.

Layer 3 closed: the workhorse-level reshape landed. `tryAddEdgeWith` now
returns `Sum (WorkhorseWitness k ℓ V) (PartialOrientation V)` with the
case-5 inline witness construction consuming `hD : Reachable k ℓ D` (the
old `h_outle : ∀ x, D.out x ≤ k` hypothesis absorbed via `hD.out_le`) and
the DFS-failure data; `runPebbleGameWith` propagates the `Sum` through the
fold (also taking `hD` and dropping its `(∀ x, D.out x ≤ k)` runtime
check). `tryAddEdge` and `runPebbleGame` math-layer wrappers and
`runPebbleGameExec` exec-layer wrapper restate against the new shape;
`runPebbleGameExec`'s `Decidable` instances re-route through
`Sum.isRight`. The reach-closure machinery (`reach`, `mem_reach`,
`self_mem_reach`, `reach_closed`, `outOn_eq_zero_of_closed`,
`outOn_reach_union_eq_zero`) moves from `PebbleGame/Correctness.lean`
into `PebbleGame/Basic.lean` so the case-5 inline construction in
`Algorithm.lean` can use them. The `tryAddEdgeWith_isSome` /
`tryAddEdgeWith_eq_none_imp_exists_witness` /
`runPebbleGameWith_eq_none_imp_exists_witness*` /
`runPebbleGame_eq_none_imp_exists_witness` chain is eliminated;
`tryAddEdge_isSome_iff_sparse` narrative-bridge shim retired.
`tryAddEdgeWith_isSparse` (the surviving accept-implies-sparse half) and
`runPebbleGame_correct` / `runPebbleGameWith_correct` /
`runPebbleGameExec_correct` / `countMatroid_indep_iff_runPebbleGame`
restated against `.inr`. Two new helper lemmas in `Algorithm.lean`
(`tryAddEdgeWith_witness_uv`, `tryAddEdgeWith_witness_underline_eq`) and
one new bridge lemma in `Correctness.lean`
(`runPebbleGameWith_witness_bridges`) discharge the wrapper-level path
from `.inl w` to `WorkhorseWitness.certifies_against`'s preconditions.
The Phase 11 plan's `_underline_subset` /  `_mem_underline` /
`_underline_eq` lemmas restate against `.inr` with the same proof
structure (using `split at h` to discharge the `match heq : ... with`
shadowing that came with `tryAddEdgeWith`'s recursive call needing
`tryAddEdgeWith_reachable` for the reachability proof of the recursed
orientation).

Blueprint: `chapter/pebble-game.tex`'s `def:tryAddEdge` and
`def:runPebbleGame` restated against the `Sum`-return shape and the
`hD` signature; `lem:pebble-game-tryAddEdgeWith-isSome` and
`lem:pebble-game-tryAddEdge-iff-independent` and
`lem:pebble-game-failure-witness` retired; `thm:pebble-game-correct`
restated against `.inr` / `.inl w` with `WorkhorseWitness` as the
blocking-witness carrier; `cor:pebble-game-countMatroid-indep`
restated. `chapter/executable.tex`'s `thm:runPebbleGameWith-correct` /
`thm:runPebbleGameExec-correct` / `def:isSparse-decidable` restated;
the CLI subsection's "optional refinement" note updated to acknowledge
that Layer 3 has structurally landed the blocking-witness machinery
(Layer 5 will surface it in CLI output).

Layer 4 closed: `PebbleGameResult G k ℓ` inductive (with `.accept ⟨D,
h_underline, h_reach⟩` and `.reject ⟨V', h_size, h_lt⟩` and `.isAccept :
Bool`) lives in `PebbleGame/Correctness.lean` (placement micro-decision:
import structure dictates `Correctness.lean` rather than the plan's
`Exec.lean` — the verdict-bearing wrappers in both math- and exec-layers
need the verdict's return type, so it goes in the lowest file importing
`Sparsity.lean`). Layer 4 originally landed **additively** on top of
Phase 11 Layer 3's `Sum`-returning functions
(`runPebbleGame_result` / `runPebbleGameExec_result` wrappers
alongside the raw `Sum`-returning `runPebbleGame` / `runPebbleGameExec`).

Layer 4b closed: **maximal reshape** per the phase's *Architectural
choices* — the additive Layer 4 wrappers were collapsed into the
verdict-returning `runPebbleGame` / `runPebbleGameExec` directly. The
`Sum`-returning math- and exec-layer wrappers are retired; the
workhorse-level `runPebbleGameWith` keeps the `Sum` return type because
it is `G`-free (the verdict construction happens at the wrapper layer
where `G` is in scope). The math-layer `runPebbleGame_underline_eq_edgeFinset`
helper bundled into a single math-layer-discharge lemma
`runPebbleGame_edges_discharges` (no-loops, pairwise, image triple),
consumed by the verdict construction in `runPebbleGame.aux`. The
certificate-form iff `runPebbleGame_correct` / `runPebbleGameExec_correct`
retired; the workhorse-level `runPebbleGameWith_correct` is the single
source of truth, and the verdict-form iff `runPebbleGame_isAccept_iff` /
`runPebbleGameExec_isAccept_iff` (proved via the same `*_aux_isAccept`
bridge pattern) is the user-facing restatement. Phase 7's
`countMatroid_indep_iff_runPebbleGame` restated against
`PebbleGameResult.isAccept`; the additive `_result` analog retired.
The three `Decidable` instances simplify:
`instDecidableIsSparse`'s reduction body is now
`(runPebbleGameExec G k ℓ h_matroidal.out).isAccept` (no `_result` detour).

Blueprint reshape per the maximal-reshape: `def:runPebbleGame` /
`def:runPebbleGameExec` restated against the verdict return type;
`thm:pebble-game-correct` restated at the workhorse layer (still the
single source of truth, but its `\lean{...}` repointed at
`runPebbleGameWith_correct`); `thm:runPebbleGameExec-correct` and
`def:runPebbleGameExec-result` retired (collapsed into the new
verdict-returning `def:runPebbleGameExec`); `thm:pebbleGameResult-isAccept-iff`
repointed at the new `_isAccept_iff` lemmas;
`cor:pebble-game-countMatroid-indep` retains a single `\lean{...}` pin
(the `_result`-form pin retired). `def:isSparse-decidable`'s
reduction-body equation reflects the new shape.

Implementation notes from the maximal reshape: the dep-graph cannot
accept extra `\uses{}` edges that create diamond explosions —
attempting to add `def:pebbleGameResult` and
`lem:workhorseWitness-certifies` to `def:runPebbleGame`'s `\uses{}`
crashed `inv web` with `RecursionError` in `plastexdepgraph.ancestors`.
The fix was to keep `def:runPebbleGame`'s `\uses{}` minimal
(`def:tryAddEdge, def:workhorseWitness, def:partial-orientation`) and
let the cross-cutting verdict / workhorse-witness dependencies surface
through the verdict-form theorem's `\uses{}` instead.

Layer 5 closed: `Main.lean` patten-matches on the verdict returned by
`PartialOrientation.runPebbleGameExec G 2 3 (by omega)` directly (no
longer routes through the `Decidable G.IsLaman` reduction, since the
verdict's constructor structurally carries both the accept-branch
trichotomy disambiguator and the witness data). On `.accept D _ _`:
emit `LAMAN` (if `G.edgeFinset.card + 3 = 2 * n`) or
`SPARSE_NOT_TIGHT`, followed by one `ARCS u v` line per arc
`(u, v) ∈ D.arcs`, sorted lexicographically via
`(D.arcs.image toLex).sort (· ≤ ·)` then `.map ofLex`. On
`.reject V' _ _`: emit `NOT_SPARSE`, then `BLOCKING <V'.card>`, then
one `VERTEX w` line per `w ∈ V'.sort (· ≤ ·)`. All four `examples/*.txt`
fixtures' commented expected-output blocks updated to the new schema
in full (per *Blockers / open questions* resolution below: kept
complete rather than truncated). Blueprint
`chapter/executable.tex`'s CLI subsection updated to describe the
verdict-direct routing and the new output schema (with a
three-column tabular layout matching the schema notation in
*Architectural choices*).

The phase target is a **maximal reshape** of the pebble-game return
type: replace the `Option`-shaped output of `runPebbleGame` /
`runPebbleGameExec` with a two-constructor inductive
`PebbleGameResult G k ℓ` whose `.accept` constructor carries the
orientation (already there) and whose `.reject` constructor carries
the blocking subset $V'$ with the inline sparsity-violation
certificate. The certificate-form correctness theorem
(`runPebbleGameExec_correct`) ceases to be an iff statement and
collapses into the *type* of the verdict — the verdict's
constructor name IS the certificate.

The substantive Lean content: redefine `PartialOrientation.reach`
through a new verified-iterative *computable* `reachClosureComputable`
in `Search/DFS.lean` (eliminating the `Classical.decPred`
dependency); add a workhorse-side `WorkhorseWitness k ℓ V` structure
carrying the failure-point data; reshape `tryAddEdgeWith` and
`runPebbleGameWith` to return `Sum (WorkhorseWitness k ℓ V)
(PartialOrientation V)`; define the user-facing `PebbleGameResult G
k ℓ` and re-derive `runPebbleGame` / `runPebbleGameExec` against
it; re-route Phase 10's `Decidable` instances and Phase 7's
`countMatroid_indep_iff_runPebbleGame` through the verdict.

The Phase 9/10 split between math-layer (`runPebbleGame`,
`noncomputable`) and exec-layer (`runPebbleGameExec`, computable
via `[LinearOrder V]`) stays — what reshapes is the return type,
not the math/exec boundary.

## Architectural choices made up front

These extend `../DESIGN.md` *Choices to revisit*; if any turns out
wrong, revisit there.

- **Maximal reshape, not parallel extraction.** Phase 11's central
  design choice: replace the `Option (PartialOrientation V)` return
  of `runPebbleGameWith` / `runPebbleGame` / `runPebbleGameExec`
  with a verdict-bearing inductive end-to-end, rather than ship a
  parallel `runPebbleGameExec_blocking_witness` extraction wrapper.
  The duplication-reduction is the substantive one: Phase 9's
  `_isSome` / `_eq_none_imp_exists_witness` chain (~200 LoC in
  `Correctness.lean`) is absorbed into `tryAddEdgeWith`'s case5
  body as inline witness construction, and the `runPebbleGameExec_correct`
  iff (Phase 10) collapses into the verdict's type. Trade: a
  Phase-10-sized restate of the workhorse-level `_reachable` /
  `_underline_*` / `_sound` lemmas against the new return shape,
  plus re-routing Phase 10's `Decidable` instances and Phase 7's
  `countMatroid_indep_iff_runPebbleGame` through the verdict's
  `.isAccept` Boolean projection. The mathematical content
  (`independent_brings_pebble`, the `Reachable` invariants, the
  algebraic core) is preserved verbatim.

- **Blueprint reshape happens in-place, per Layer.** No new
  chapter. Each Phase 11 Layer commit ships its blueprint reshape
  in step with the Lean: Layer 1 updates `chapter/dfs.tex` with
  `def:reachClosureComputable` + `lem:mem-reachClosureComputable`
  (retiring `def:reachClosure` / `lem:mem-reachClosure`); Layer 2
  inserts `def:workhorseWitness` + `lem:workhorseWitness-certifies`
  into `chapter/pebble-game.tex`'s existing *Completeness*
  subsection; Layer 3 restates `chapter/pebble-game.tex`'s
  algorithm-side nodes (`def:tryAddEdge`, `def:runPebbleGame`) to
  the `Sum`-return shape, retiring the obsolete
  `lem:tryAddEdgeWith-isSome` /
  `lem:tryAddEdgeWith-eq-none-imp-exists-witness` /
  `lem:runPebbleGameWith-eq-none-imp-exists-witness` and their
  `_empty` specializations; Layer 4 inserts `def:pebbleGameResult`
  into `chapter/pebble-game.tex` and restates
  `chapter/executable.tex`'s `def:runPebbleGameExec` and three
  `Decidable` instances against the verdict, replacing the
  certificate-form iff theorems (`thm:pebble-game-correct`,
  `thm:runPebbleGameExec-correct`) with a `\begin{remark}` block
  documenting the verdict-type encoding; Layer 5 updates
  `chapter/executable.tex`'s CLI subsection with the witness-bearing
  output schema. Each blueprint update lands in the same commit as
  the Lean it describes, so the dep-graph never has a long-lived
  red region in a chapter that was green.

- **Workhorse witness is algorithm-side data, no `G` parameter.**
  At the workhorse layer (`tryAddEdgeWith`, `runPebbleGameWith`),
  the witness structure is
  ```
  structure WorkhorseWitness (k ℓ : ℕ) (V : Type*) [DecidableEq V] where
    D                : PartialOrientation V       -- orientation at failure
    V'               : Finset V                    -- blocking subset
    uv               : V × V                       -- pending edge that failed
    huv_ne           : uv.1 ≠ uv.2
    hu_mem           : uv.1 ∈ V'
    hv_mem           : uv.2 ∈ V'
    h_outOn_zero     : D.outOn V' = 0              -- closed under D.arcs
    h_below          : D.peb k uv.1 + D.peb k uv.2 ≤ ℓ
    h_pending_fresh  : s(uv.1, uv.2) ∉ D.underline
    h_reachable      : Reachable k ℓ D
  ```
  with no `G : SimpleGraph V` field. The `G`-shaped sparsity-violation
  certificate is recovered by a wrapper-layer lemma
  ```
  WorkhorseWitness.certifies_against (w : WorkhorseWitness k ℓ V)
      (h_mat : ℓ < 2 * k)
      {G : SimpleGraph V} [Fintype G.edgeSet]
      (h_uv_in : s(w.uv.1, w.uv.2) ∈ G.edgeFinset)
      (h_sub : w.D.underline ⊆ G.edgeFinset) :
      ℓ ≤ k * w.V'.card ∧ k * w.V'.card < (G.edgesIn ↑w.V').ncard + ℓ
  ```
  whose body is the existing
  `Reachable.independent_brings_pebble_simpleGraph_form` content,
  unchanged. Decision rationale: the workhorse layer is algorithm-
  shaped and doesn't reference `G`; adding `G` to its signature
  would propagate a `D.underline ⊆ G.edgeFinset` bridge hypothesis
  through every call site for no benefit. The wrapper layer is
  where the `G`-shaped story belongs.

- **User-facing verdict.** The wrapper layer returns
  ```
  inductive PebbleGameResult (G : SimpleGraph V) (k ℓ : ℕ) where
    | accept (D : PartialOrientation V)
             (h_underline : D.underline = G.edgeFinset)
             (h_reach     : Reachable k ℓ D)
    | reject (V' : Finset V)
             (h_size : ℓ ≤ k * V'.card)
             (h_lt   : k * V'.card < (G.edgesIn ↑V').ncard + ℓ)
  ```
  The verdict's constructor *is* the certificate; the certificate-form
  iff theorems (`runPebbleGame_correct`, `runPebbleGameExec_correct`)
  collapse into the *type* of the wrapper's return. Boolean
  projections `.isAccept : PebbleGameResult G k ℓ → Bool` etc. drive
  the `Decidable` instances. Compatibility shim
  `.toOption : PebbleGameResult G k ℓ → Option (PartialOrientation V)`
  bridges any remaining callsite that wants the Phase-10 `Option`
  shape — but the substantive consumers (Phase 7
  `countMatroid_indep_iff_runPebbleGame`, Phase 10 `Decidable`
  instances) re-route through `.isAccept` directly.

- **One unified `D.reach` def, computable.** Redefine
  `PartialOrientation.reach : V → Finset V` (currently
  `noncomputable def` via `reachClosure`) directly through the new
  computable `reachClosureComputable`. The consumer-facing
  `mem_reach` iff against `Relation.ReflTransGen` is preserved
  unchanged; downstream proofs using only the iff are unaffected.
  Decision rationale: Phase 10's *One `Decidable` instance per
  predicate* principle generalises to *one canonical reduction
  body per algorithm-bearing definition*. The
  `[Fintype V] [DecidableEq V]` style island
  (`../DESIGN.md` *Pebble-game style island*) already takes both
  typeclasses on the orientation side, so the computable form is
  in scope at every callsite.

- **`reachClosureComputable` placement.** Add to `Search/DFS.lean`,
  sibling of the existing `reachableFinding`. Both share the
  termination measure `(Finset.univ \ visited).card` and the
  out-neighbour adapter pattern; whether they share a common inner
  recursion (cleaner) or stay as two independent recursions
  (simpler-to-write) is a Layer-1-time call. Current `Search/DFS.lean`
  is 779 LoC; the new primitive + correctness adds ~200–300 LoC,
  pushing the file to ~1000–1100. If the split threshold is hit
  (~1050 per `notes/PERFORMANCE.md` *Split candidates*), break out
  a `Search/Reachability.lean` carrying the closure primitive
  alone.

- **`PebbleGameResult` placement.** Add to `PebbleGame/Exec.lean`
  (where the user-facing wrappers live). The `WorkhorseWitness`
  structure goes in `PebbleGame/Basic.lean` (where state
  structures live). `WorkhorseWitness.certifies_against` lives in
  `PebbleGame/Correctness.lean` (where `independent_brings_pebble`
  already lives).

- **CLI surface (Layer 5).** Bump `Main.lean`'s output format to
  pattern-match on the `PebbleGameResult` constructors and emit
  witness lines after the verdict label. Output schema:
  ```
  LAMAN                 SPARSE_NOT_TIGHT      NOT_SPARSE
  ARCS u₀ v₀            ARCS u₀ v₀            BLOCKING <count>
  ARCS u₁ v₁            ARCS u₁ v₁            VERTEX w₀
  ...                   ...                   VERTEX w₁
                                              ...
  ```
  Backward-incompatible vs Phase 10's trichotomy-only format; the
  four `examples/*.txt`-shipped fixtures' commented expected-output
  blocks update accordingly. Scripts parsing only the trichotomy
  read the first line unchanged.

- **Extended files (Lean side)**
  - `CombinatorialRigidity/Search/DFS.lean` — extended with
    `reachClosureComputable` + correctness (Layer 1). Possible
    split off `Search/Reachability.lean` if size pushes past the
    1050-LoC threshold.
  - `CombinatorialRigidity/PebbleGame/Basic.lean` — extended with
    `WorkhorseWitness k ℓ V` structure (Layer 2) and the
    `reach`-via-`reachClosureComputable` redefinition.
  - `CombinatorialRigidity/PebbleGame/Algorithm.lean` —
    `tryAddEdgeWith` and `runPebbleGameWith` reshaped to return
    `Sum WorkhorseWitness PartialOrientation` (Layer 3).
  - `CombinatorialRigidity/PebbleGame/Correctness.lean` —
    `_reachable` / `_underline_*` / `_underline_eq` / `_sound`
    lemmas restated; `_isSome` / `_eq_none_imp_exists_witness`
    chain absorbed into `tryAddEdgeWith` case5 + a single
    `WorkhorseWitness.certifies_against` lemma (Layer 3).
    `runPebbleGame_correct` collapses into `runPebbleGame`'s return
    type (Layer 4); `countMatroid_indep_iff_runPebbleGame` re-routes
    through `.isAccept` (Layer 4).
  - `CombinatorialRigidity/PebbleGame/Exec.lean` — defines
    `PebbleGameResult G k ℓ`; `runPebbleGameExec` re-derived
    against it; Phase 10's three `Decidable` instances re-routed
    through `.isAccept` (Layer 4).
  - `Main.lean` — bumped output format (Layer 5).
  - `examples/*.txt` — commented expected-output blocks updated
    (Layer 5).

## Layer 0 audits — outcomes

All audits resolved in this opener commit; layer plan below
incorporates the outcomes.

1. **Witness-type unification across algorithm levels.** ✓ Both
   `tryAddEdgeWith`-level failure and `runPebbleGameWith`-level
   failure produce the same existential shape `∃ V', ℓ ≤ k * V'.card
   ∧ k * V'.card < (G.edgesIn V').ncard + ℓ`; the fold-level witness
   is the per-step witness propagated forward unchanged through the
   first `.inl`. One `WorkhorseWitness k ℓ V` structure suffices at
   both levels.

2. **`G`-parameter for `tryAddEdgeWith`.** ✗ Don't add. The workhorse
   layer is `G`-free; the `G`-shaped sparsity-violation certificate
   is wrapper-layer content via `WorkhorseWitness.certifies_against`.

3. **Verdict shape.** ✓ Two-constructor inductive
   `PebbleGameResult G k ℓ` with `.accept ⟨D, h_underline, h_reach⟩`
   and `.reject ⟨V', h_size, h_lt⟩`. The constructor is the
   certificate; no separate iff theorem needed at the wrapper layer.

4. **Math/exec split survives.** ✓ Both `runPebbleGame` (math-layer,
   noncomputable) and `runPebbleGameExec` (exec-layer, computable)
   stay; what reshapes is the return type. The split rationale
   (`../DESIGN.md` *Pebble-game style island*) is orthogonal to the
   verdict reshape.

5. **`D.reach` unification.** ✓ One `def`, computable via
   `reachClosureComputable`. The math-layer noncomputable form
   disappears. Downstream proofs use only the iff
   (`mem_reach ↔ Relation.ReflTransGen`), so the redefinition is
   invisible to them.

6. **Blueprint workflow.** ✓ Phase 11 is a structural-edit phase;
   blueprint changes land in-place in the existing chapters
   alongside each Layer's Lean. No new chapter. The phase's
   authoritative to-do list lives in this file's *Layer plan*
   section.

7. **`reachableFinding` factoring.** ✓ Resolved at Layer 1: route
   the closure through `reachableFinding` itself rather than a
   sibling iterative recursion. Specifically,
   `reachClosureComputable succ v := Finset.univ.filter
   fun w => (reachableFinding succ (· = w) v).isSome`. Soundness
   and completeness are one-step appeals to
   `reachableFinding_sound` / `_complete`, plus a small
   `DirectedWalk.toReflTransGen` bridge lemma. Trade-off: the
   asymptotic cost is $O(n)$ DFS invocations (one per candidate
   vertex), so closure construction is quadratic in the worst case.
   The math-layer `D.reach` is rarely materialised — the algorithm
   side queries reachability once per pending edge via
   `tryReachPebble` — so this is acceptable, and the proof effort
   relative to an accumulating single-DFS variant is far smaller.
   Replacing the implementation with a single-pass accumulating
   form is a future opportunity; the consumer-facing
   `mem_reachClosureComputable` iff insulates downstream code from
   the swap.

8. **`Search/DFS.lean` file split.** ✓ Resolved at Layer 1: stayed
   in-file. The Layer 1 addition (closure primitive + soundness +
   completeness + bridge lemma) was ~110 LoC, keeping
   `Search/DFS.lean` at ~830 LoC, comfortably under the ~1050-LoC
   split threshold.

## Layer plan

- **Layer 0** ✓. Phase opener: notes, ROADMAP §11 +
  status row, README / home_page / intro.tex flips. No Lean, no
  blueprint changes.

- **Layer 1** ✓. Verified-iterative `reachClosureComputable` in
  `Search/DFS.lean` (in-file, ~110 LoC added — well under the
  split threshold). Routed through `reachableFinding` rather than a
  sibling iterative recursion (see audit point 7 above):
  `reachClosureComputable succ v` filters `Finset.univ` by
  `(reachableFinding succ (· = w) v).isSome`. Soundness and
  completeness are direct appeals to the
  `reachableFinding_sound` / `_complete` chain, plus a small bridge
  `DirectedWalk.toReflTransGen`. `PartialOrientation.reach`
  redefined through the new primitive (`reachClosureComputable
  D.outList v`); stays `noncomputable` because of `outList`'s use of
  `Finset.toList`, but the `mem_reach` iff is preserved verbatim and
  downstream proofs (`self_mem_reach`, `reach_closed`) re-derive
  cleanly. `Search.reachClosure` removed (no remaining consumers).
  Blueprint: `chapter/dfs.tex` gains `def:reachClosureComputable` +
  `lem:mem-reachClosureComputable` in a new *Reachability closure
  (computable)* subsection; `chapter/pebble-game.tex` updates the
  closure-primitive mentions in `def:tryAddEdge` and
  `def:runPebbleGame` to the new name.

- **Layer 2** ✓. `WorkhorseWitness k ℓ V` lives in `Basic.lean`
  (outside `PartialOrientation` namespace since the structure is
  parallel state — `D : PartialOrientation V` is a field, not the
  bundling vehicle); `WorkhorseWitness.certifies_against` lives in
  `Correctness.lean` at end-of-file after `PartialOrientation`
  closes (since `WorkhorseWitness` resolves under
  `_root_.CombinatorialRigidity.PebbleGame`, not under
  `PartialOrientation`). The witness's `h_pebOn_le : D.pebOn k V' ≤ ℓ`
  field strengthens the originally-proposed per-vertex `h_below :
  peb u + peb v ≤ ℓ` to absorb the DFS-failure "no free pebble outside
  `{u, v}`" guarantee into a single field — Layer 3's case-5 inline
  construction will build the stronger bound directly via
  `Finset.sum_eq_zero` over `V' \ {u, v}` rather than carry both
  fields separately. The `certifies_against` body is the closing
  algebra of `tryAddEdgeWith_eq_none_imp_exists_witness` (not the
  `simpleGraph_form` proof body, which goes the wrong direction —
  builds a free pebble from sparsity, not non-sparsity from no free
  pebble). Blueprint: `chapter/pebble-game.tex` gains
  `def:workhorseWitness` + `lem:workhorseWitness-certifies`
  immediately after `lem:pebble-game-independent-brings-pebble-graph`
  in the *Completeness* subsection. Total Lean delta: ~80 LoC.

- **Layer 3** ✓. Reshape landed in a single commit. `tryAddEdgeWith`
  returns `Sum (WorkhorseWitness k ℓ V) (PartialOrientation V)`;
  `runPebbleGameWith` propagates the `Sum`; both take
  `hD : Reachable k ℓ D` as a hypothesis (absorbing the old
  `h_outle` argument and the runtime `(∀ x, D.out x ≤ k)` check in
  the fold). The case-5 inline construction in `tryAddEdgeWith`
  builds the `WorkhorseWitness` directly from `hD`, `hthr`, and the
  DFS-failure data; the `V'` field uses `reachClosureComputable`
  (not `D.reach`, which is noncomputable) so the workhorse stays
  computable. The reach-closure-on-orientations API
  (`reach`, `mem_reach`, `self_mem_reach`, `reach_closed`,
  `outOn_eq_zero_of_closed`, `outOn_reach_union_eq_zero`) moved
  from `Correctness.lean` to `Basic.lean` since the case-5
  construction in `Algorithm.lean` needs them. The
  `tryAddEdgeWith_isSome` / `*_eq_none_imp_exists_witness*` /
  `tryAddEdge_isSome_iff_sparse` chain eliminated;
  `tryAddEdgeWith_isSparse` (the surviving accept-implies-sparse
  half) restated against `.inr`. Two new helpers in `Algorithm.lean`
  (`tryAddEdgeWith_witness_uv`,
  `tryAddEdgeWith_witness_underline_eq`) plus one new bridge in
  `Correctness.lean` (`runPebbleGameWith_witness_bridges`) discharge
  the wrapper-level path from `.inl w` to
  `WorkhorseWitness.certifies_against`'s preconditions.
  `runPebbleGame_correct` / `runPebbleGameWith_correct` /
  `runPebbleGameExec_correct` / `countMatroid_indep_iff_runPebbleGame`
  restated against `.inr` instead of `some`. Blueprint:
  `chapter/pebble-game.tex` updated for the new return shape;
  three obsolete `lem:` nodes retired; `thm:pebble-game-correct`
  restated. `chapter/executable.tex`'s wrapper / Decidable nodes
  restated. **Proof technique surfaced**: the `match heq : <expr> with`
  pattern inside `runPebbleGameWith`'s body (needed because the
  recursive call's `Reachable k ℓ`-hypothesis depends on the matched
  result) shadows in downstream proofs — `rw [heq]` fails with
  motive-not-type-correct. Workaround: use `split at h` (which
  introduces the equation hypothesis cleanly) after a
  `simp only [dif_pos hcond]` reduction. Total Lean delta:
  ~+500 LoC across `PebbleGame/{Basic, Algorithm, Correctness,
  Exec}.lean`, ~−300 LoC in `Correctness.lean` from absorption.

- **Layer 4** ✓. `PebbleGameResult G k ℓ` inductive lives in
  `Correctness.lean` (placement micro-decision — see *Decisions made
  during this phase* below). The verdict carries `.accept ⟨D,
  h_underline, h_reach⟩` and `.reject ⟨V', h_size, h_lt⟩` with
  `.isAccept : Bool`. Layer 4 initially shipped *additively* on top of
  Phase 11 Layer 3's `Sum`-returning functions: parallel verdict-bearing
  wrappers `runPebbleGame_result` (math-layer) and
  `runPebbleGameExec_result` (exec-layer) sat alongside the raw
  `runPebbleGame` / `runPebbleGameExec` returning `Sum`. The three
  `Decidable` instances re-routed through `.isAccept` of the
  verdict-bearing wrappers.

- **Layer 4b** ✓. **Maximal reshape** per the phase's *Architectural
  choices: Maximal reshape, not parallel extraction* — Layer 4's
  additive wrappers were collapsed into the verdict-returning
  `runPebbleGame` / `runPebbleGameExec` directly. The raw
  `Sum`-returning math- and exec-layer wrappers retired (the
  workhorse-level `runPebbleGameWith` keeps the `Sum` return type
  because it is `G`-free). The math-layer
  `runPebbleGame_underline_eq_edgeFinset` helper consolidated into a
  single discharge bundle `runPebbleGame_edges_discharges` (no-loops,
  pairwise, Sym2-image triple) consumed by the verdict construction
  inside `runPebbleGame.aux`. The certificate-form
  `runPebbleGame_correct` / `runPebbleGameExec_correct` retired; the
  workhorse-level `runPebbleGameWith_correct` is the single source of
  truth, and the verdict-form `runPebbleGame_isAccept_iff` /
  `runPebbleGameExec_isAccept_iff` (renamed from the `_result_isAccept_iff`
  variants) is the user-facing restatement. Phase 7's
  `countMatroid_indep_iff_runPebbleGame` restated against
  `PebbleGameResult.isAccept`; `_runPebbleGame_result` analog retired.
  Blueprint: `def:runPebbleGame` / `def:runPebbleGameExec` restated
  against the verdict return type; `thm:pebble-game-correct` repointed
  at the workhorse-level `runPebbleGameWith_correct`;
  `thm:runPebbleGameExec-correct` and `def:runPebbleGameExec-result`
  retired (collapsed into the new verdict-returning
  `def:runPebbleGameExec`); `thm:pebbleGameResult-isAccept-iff`
  repointed at the new `_isAccept_iff` lemmas;
  `cor:pebble-game-countMatroid-indep` retains a single `\lean{...}` pin.
  CLI surface (`Main.lean`) unchanged — `decide G.IsLaman` etc. continue
  to reduce through the `Decidable` instances, now via the verdict's
  `.isAccept` directly. Total Lean delta on the maximal reshape:
  ~−150 LoC (the additive wrappers and certificate-form iff theorems
  net out larger than the merged forms).

- **Layer 5** ✓. `Main.lean` bumped: `classify` now invokes
  `PartialOrientation.runPebbleGameExec G 2 3 (by omega)` directly
  (was: `decide G.IsLaman` → `decide (G.IsSparse 2 3)` two-step
  routing through the `Decidable` instances) and pattern-matches the
  returned `PebbleGameResult G 2 3` verdict, emitting `LAMAN` /
  `SPARSE_NOT_TIGHT` (disambiguated on the `.accept` branch by the
  constant-time edge-count check `G.edgeFinset.card + 3 = 2 * n`)
  with arc lines, or `NOT_SPARSE` with `BLOCKING` + `VERTEX` lines.
  Arc-sorting via `(D.arcs.image toLex).sort (· ≤ ·)` against
  `LinearOrder (Lex (Fin n × Fin n))`; vertex-sorting via
  `Finset.sort (· ≤ ·)` directly on `Finset (Fin n)`. Total Lean delta
  to `Main.lean`: ~+50 LoC (mostly schema docstring + helper sorting
  shapes); four `examples/*.txt` fixtures updated to carry the full
  Phase 11 Layer 5 expected output in their leading comment blocks.
  Blueprint `chapter/executable.tex`'s CLI subsection updated with
  the three-column output schema, the verdict-direct invocation step
  in the algorithm-walk enumeration, and a pointer to the
  `examples/` fixtures.

Total estimated delta: ~900–1300 LoC across the pebble-game files
plus `Search/DFS.lean` and `Main.lean`. Of that, the substantive
work is Layer 3 (algorithm reshape) and Layer 1 (computable reach);
Layers 2 and 4 are mostly mechanical packaging; Layer 5 is CLI
plumbing. Math content preserved verbatim.

## Lemma checklist

**Maintained in the blueprint, not here.** The Phase 11 lemma
index is spread across `chapter/dfs.tex` (Layer 1's
`reachClosureComputable` nodes), `chapter/pebble-game.tex`
(Layers 2–4's workhorse-witness, algorithm-reshape, and verdict
nodes), and `chapter/executable.tex` (Layer 4's wrapper-reshape and
Decidable-instance updates, Layer 5's CLI subsection); each
Layer's commit ships its blueprint updates in step. The *Layer
plan* section above is the authoritative to-do list — what each
commit ships, blueprint and Lean.

## Decisions made during this phase

### Phase-local choices and proof techniques

- **Layer 4: `PebbleGameResult` lives in `Correctness.lean`, not `Exec.lean`.**
  The Phase 11 *Architectural choices* originally tagged `PebbleGameResult`'s
  home as `PebbleGame/Exec.lean`; in practice the import structure dictates
  `PebbleGame/Correctness.lean` instead. The math-layer wrapper
  `runPebbleGame_result` needs the verdict's return type and sits above
  `Exec.lean` in the import chain. The exec-layer wrapper in `Exec.lean`
  re-uses the same `PebbleGameResult` definition without re-declaring it. No
  user-facing API change; the placement is mechanically forced by file-import
  order (`Exec.lean` imports `Correctness.lean`).

- **Layer 4b: collapsed to maximal reshape per notes architectural
  choice.** Layer 4 originally landed *additively* — parallel
  verdict-bearing wrappers `runPebbleGame_result` / `runPebbleGameExec_result`
  on top of the Layer 3 `Sum`-returning raw `runPebbleGame` /
  `runPebbleGameExec`. Layer 4b collapses to the maximal-reshape form per
  the phase's *Architectural choices: Maximal reshape, not parallel
  extraction*: the math-layer `runPebbleGame G k ℓ h_matroidal` and
  exec-layer `runPebbleGameExec G k ℓ h_matroidal` now return
  `PebbleGameResult G k ℓ` directly. The raw `Sum`-returning wrappers
  retire; the workhorse-level `runPebbleGameWith` keeps the `Sum` return
  type (it is `G`-free, so the verdict construction belongs one layer
  above). The certificate-form iffs `runPebbleGame_correct` /
  `runPebbleGameExec_correct` collapse into the verdict's type and retire;
  `runPebbleGameWith_correct` (workhorse level) is the single source of
  truth, and the verdict-form `_isAccept_iff` lemmas re-derive from it
  via the same `*_aux_isAccept` bridge as before. Phase 7's
  `countMatroid_indep_iff_runPebbleGame` restated against
  `PebbleGameResult.isAccept` (the additive `_result` analog retired).
  Trade: a one-time API churn (math-layer `runPebbleGame_sound` /
  `runPebbleGame_underline_eq_edgeFinset` retire alongside, since their
  hypotheses no longer type-check; the workhorse-level analogs
  `runPebbleGameWith_sound` / `runPebbleGameWith_underline_eq` remain).
  Benefit: a single API surface per layer, no "raw vs verdict" branching
  for downstream consumers, and the user-facing claim "the verdict's
  constructor IS the certificate" is structurally enforced rather than
  documented-only.

- **Layer 4: `*_result.aux` helper to dodge TACTICS-QUIRKS § 17.** A direct
  term-level `match h_opt : runPebbleGame G k ℓ with | .inr D => ... | .inl
  w => ...` body for `runPebbleGame_result` would put `h_opt` in scope of
  each branch but with the substituted type `<pat> = <pat>` (per § 17), so
  downstream proof references to `h_opt : runPebbleGame G k ℓ = .inr D`
  fail with `Application type mismatch`. The standard fix
  (TACTICS-QUIRKS § 17's recommendation) is `subst`-style routing or
  capturing the equation separately; in this case a `*.aux` helper taking
  the `Sum`-shaped result and its equation as explicit arguments, followed
  by `*_result G k ℓ h_matroidal := *.aux G k ℓ h_matroidal (runPebbleGame
  G k ℓ) rfl`, completely sidesteps the substitution. Pattern carried
  through both math- and exec-layer wrappers.

- **Layer 4 micro-call: verdict-form iff `(... .isAccept)` over
  `@[deprecated]`.** Per *Blockers / open questions*, option (b) was
  picked: the Phase-9-era `runPebbleGame_correct` is restated in verdict
  form as `runPebbleGame_result_isAccept_iff : G.IsSparse k ℓ ↔
  (runPebbleGame_result G k ℓ h_matroidal).isAccept`. The proof bridges
  through a private `runPebbleGame_result_aux_isAccept :
  (runPebbleGame_result.aux _ _ _ _ s _).isAccept = s.isRight`, then
  composes with `runPebbleGame_correct` via `Sum.isRight_iff`. Same
  pattern at the exec layer.

- **Layer 3: `tryAddEdgeWith` / `runPebbleGameWith` take `hD : Reachable k ℓ D`
  as a hypothesis (absorbing `h_outle`).** The case-5 inline witness construction
  needs `Reachable k ℓ D` to populate the witness's `h_reachable` field. Adding
  `hD` to the signature also lets recursive calls (cases 3, 4) compute their
  fresh reachability via `r.reachable_newOrient_of_addEdgePred hD hD.out_le`
  without a separate `h_outle` argument. At the fold layer, `runPebbleGameWith`
  takes `hD` and drops its previous `(∀ x, D.out x ≤ k)` runtime check (which
  was always satisfied along the algorithm's actual paths). Trade: the recursive
  call in `runPebbleGameWith` now goes through `tryAddEdgeWith_reachable` to
  compute the updated `hD` for the next step, making the function definition use
  a `match heq : ... with` pattern that requires `split at h` (not `rw [heq]`)
  in downstream proofs of `_underline_subset` / `_mem_underline` / `_reachable`.

- **Layer 3: case-5 inline `V' := reachClosureComputable (toSucc D) u ∪
  reachClosureComputable (toSucc D) v`, not `D.reach u ∪ D.reach v`.**
  `D.reach` is `noncomputable` (it goes through `outList`); using it in the
  case-5 construction would force `tryAddEdgeWith` itself noncomputable, breaking
  Phase 10's exec-layer claim. Using `reachClosureComputable` against the
  caller-supplied `toSucc D` adjacency keeps the workhorse fully computable.
  The proof obligations (`h_outOn_zero`, `h_pebOn_le`) bridge via
  `mem_reachClosureComputable` + `h_toSucc D`, with a one-line induction on
  `ReflTransGen` showing equivalence between the `toSucc D`-shaped and
  `D.arcs`-shaped reachability relations.

- **Layer 3: `reach`-machinery lives in `Basic.lean`, not `Correctness.lean`.**
  The case-5 construction in `Algorithm.lean` needs
  `outOn_eq_zero_of_closed`, `mem_reachClosureComputable`, etc.; these were
  in `Correctness.lean` originally but `Algorithm.lean` is below
  `Correctness.lean` in the import order. Moved the closure-of-reach API
  (`reach`, `mem_reach`, `self_mem_reach`, `reach_closed`,
  `outOn_eq_zero_of_closed`, `outOn_reach_union_eq_zero`) to a new
  `ReachClosure` section at the end of `Basic.lean`'s `PartialOrientation`
  namespace.

- **Layer 2: `WorkhorseWitness` carries `h_pebOn_le : pebOn V' ≤ ℓ`,
  not the per-vertex `h_below : peb u + peb v ≤ ℓ` initially
  proposed.** The Phase 11 opener proposed the per-vertex form (as in
  L-S Lemma 13's algebraic statement), but at the workhorse layer the
  case-5 data is strictly stronger: the DFS-failure assertion
  ("no free pebble outside `{u, v}` in `V'`") combines with the
  per-vertex below-threshold to force `pebOn V' = peb u + peb v ≤ ℓ`.
  Carrying that stronger bound as a single field (a) keeps
  `certifies_against`'s proof to one `omega` chain (Invariant (2)
  with `outOn V' = 0` rearranges directly to the strict bound), (b)
  removes a redundant "no-free-pebble" field that would otherwise
  need to be carried alongside `h_below`, and (c) doesn't lose
  information at the case-5 construction site (which has the
  no-free-pebble guarantee in hand from
  `tryReachPebbleWith_eq_none_imp` and will package it into
  `h_pebOn_le` via `Finset.sum_eq_zero` in Layer 3, mirroring the
  existing `h_zero_outside` step in
  `tryAddEdgeWith_eq_none_imp_exists_witness`).

- **Layer 1: `reachClosureComputable` routes through
  `reachableFinding`, not a sibling iterative DFS.** The closure
  is defined as `Finset.univ.filter (fun w =>
  (reachableFinding succ (· = w) v).isSome)`. The original Layer 1
  plan envisioned a parallel accumulating DFS in `Search/DFS.lean`,
  but the proof effort for a custom WF recursion with `foldl`-over-
  children (correctness against `Relation.ReflTransGen`) was
  disproportionate to its benefits at the math layer. Filtering
  through the already-iterative `reachableFinding` (which carries
  its own iterative DFS) gives the same iff contract in ~110 LoC
  total. Trade-off documented in audit point 7: $O(n)$ DFS
  invocations per closure, asymptotic cost not visible at the math
  layer (only used for the witness-set blueprint argument). Future
  perf work could swap the implementation behind
  `mem_reachClosureComputable` without touching downstream.

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN

- *Data-building `match h_opt :` quirk fix via `*.aux` helper* →
  TACTICS-QUIRKS § 17 (third bullet of *Fix*). The Layer 4
  `runPebbleGame_result.aux` / `runPebbleGameExec_result.aux` pattern
  takes the scrutinee `s` and its equation `h_opt : foo G = s` as
  separate explicit args, so the outer `match s, h_opt with` binds
  `h_opt` to the un-substituted equation that downstream proof-field
  lemmas need.

*(Likely future promotion candidates: the *Strengthen past results to
reduce duplication* principle that drove the maximal-reshape choice
— a project-philosophy entry for `../DESIGN.md`; and the
*Blueprint reshape in-place per Layer* sequencing decision — a
workflow-mode entry for `../blueprint/DESIGN.md` if the pattern recurs
in future structural-edit phases.)*

### Cleanup pass summaries

*(Not applicable until after phase close.)*

## Blockers / open questions

- **Layer 1 micro-call:** in-file extension vs `Search/Reachability.lean`
  split. Resolved by `Search/DFS.lean` LoC after Layer 1's body
  lands.

- **Layer 4 micro-call:** ✓ Resolved at Layer 4 entry to option (b)
  additively; superseded at Layer 4b by the maximal-reshape collapse
  (the Phase-9-era `runPebbleGame_correct` / `runPebbleGameExec_correct`
  retire alongside the additive `_result` wrappers; the verdict-form
  `runPebbleGame_isAccept_iff` / `runPebbleGameExec_isAccept_iff` are
  the single iff statements, each routing through `*_aux_isAccept`
  chained with `runPebbleGameWith_correct` at the workhorse level).

- **Layer 5 micro-call:** ✓ Resolved at Layer 5 by keeping the
  comment blocks complete (no truncation) on all four fixtures. The
  Moser spindle's 11 ARCS lines and $K_4$'s 4-vertex BLOCKING block
  expand the comment block by 8–11 lines per file, which keeps the
  comment-to-data ratio reasonable (each fixture still fits a single
  screen of input). The benefit is that scripts (and human readers)
  diff-checking the CLI's output against the documented expectation
  see the full schema rendered next to the input — useful both as a
  manual smoke test and as future regression-test seed data should a
  CLI-output golden-file harness ever land.

## Hand-off / next phase

Phase 11 closed at Layer 5. The pebble game's user-facing surface is
now end-to-end witness-bearing: every accept/reject branch carries
structurally-recoverable certificate data, and the CLI prints it. No
deferred work; no `sorry`s; no open friction items specific to this
phase. The dep-graph has every Phase 11 node green across
`chapter/{dfs,pebble-game,executable}.tex`; the structural-edit work
that Layer 3 / 4b put through the existing chapters' previously-green
nodes is fully discharged.

The next phase has no forced ordering. Hand-off candidates, ranked
loosely by what unlocks downstream work:

1. **Component pebble game** (L–S §5; $O(n^2)$ speedup via union
   pair-find maintained across `runPebbleGameWith`'s fold). The
   biggest standalone Phase-12 candidate: takes the Phase-11
   verdict-bearing API as input and improves the constant factor on
   the algorithm. Touches `PebbleGame/Algorithm.lean` (the fold) and
   adds a sibling state structure for component tracking.
2. **Henneberg-sequence extraction** (L–S §6). Composes Phase 11's
   accept-branch orientation $D$ with Phase 3's
   `IsLaman.exists_typeI_or_typeII_reverse` to produce an
   executable Henneberg-construction sequence from a Laman graph.
   The smallest tractable next phase; mostly composition work.
3. **Benchmarks harness** comparing `runPebbleGameExec` against a
   brute-force `Decidable G.IsSparse` baseline on small graphs.
   Lighter, no new math; useful as a runtime sanity check that the
   Phase-10 polynomial-time claim holds on real inputs and as a
   regression detector for future algorithm changes.

The candidate list above is replicated from notes for backward
reference; the live tracking lives in the next-phase's
`notes/PhaseN.md` if/when one opens. As of Phase 11 close, no phase
has been selected.
