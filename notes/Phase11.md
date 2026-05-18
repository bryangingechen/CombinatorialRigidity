# Phase 11 — Witness extraction (work log)

**Status:** in progress.

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

Layers 3–5 ahead. Next concrete commit: Layer 3 — reshape
`tryAddEdgeWith` to return `Sum (WorkhorseWitness k ℓ V) (PartialOrientation V)`
with case-5 inline construction; reshape `runPebbleGameWith` to propagate
the `Sum`; restate `_reachable` / `_underline_*` / `_underline_eq` /
`_sound`; eliminate the existential chains. Blueprint: restate
`chapter/pebble-game.tex`'s `def:tryAddEdge` / `def:runPebbleGame`
against the `Sum`-return shape; retire the `_isSome` /
`_eq_none_imp_exists_witness` nodes and their `_empty` specialisations.

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

- **Layer 3.** Reshape `tryAddEdgeWith` to return
  `Sum (WorkhorseWitness k ℓ V) (PartialOrientation V)`; reshape
  `runPebbleGameWith` to propagate the `Sum`; restate
  `_reachable` / `_underline_*` / `_underline_eq` lemmas against
  the new shape. Eliminate `tryAddEdgeWith_eq_none_imp_exists_witness`
  (its body becomes the inline witness construction in case5 of
  `tryAddEdgeWith`); eliminate
  `runPebbleGameWith_eq_none_imp_exists_witness` (collapses to fold
  propagation). The case5 inline construction is the
  `tryAddEdgeWith_eq_none_imp_exists_witness` proof body verbatim,
  packaged as a `WorkhorseWitness` value. Restate
  `runPebbleGameWith_sound` against `.inr` instead of `some`.
  Blueprint: restate `chapter/pebble-game.tex`'s `def:tryAddEdge` /
  `def:runPebbleGame` against the `Sum`-return shape; retire
  `lem:tryAddEdgeWith-isSome` /
  `lem:tryAddEdgeWith-eq-none-imp-exists-witness` /
  `lem:runPebbleGameWith-eq-none-imp-exists-witness` and their
  `_empty` specializations; restate the soundness/underline-tracking
  lemmas. Estimated ~400–500 LoC Lean delta.

- **Layer 4.** Define `PebbleGameResult G k ℓ` in `Exec.lean`;
  re-derive `runPebbleGame` (math-layer) and `runPebbleGameExec`
  (exec-layer) against it. Re-route Phase 10's three `Decidable`
  instances through `(... ).isAccept`; restate Phase 7's
  `countMatroid_indep_iff_runPebbleGame` against the verdict.
  Decide between `@[deprecated]`-bridging `runPebbleGame_correct`
  vs restating it as `G.IsSparse k ℓ ↔ (runPebbleGame G k ℓ).isAccept`
  (decision at Layer 4 entry; likely the latter for API continuity).
  Blueprint: insert `def:pebbleGameResult` into
  `chapter/pebble-game.tex`; restate `chapter/executable.tex`'s
  `def:runPebbleGameExec` and three `Decidable` instances against
  the verdict; replace `thm:pebble-game-correct` /
  `thm:runPebbleGameExec-correct` with `\begin{remark}` blocks
  documenting the verdict-type encoding; restate
  `cor:pebble-game-countMatroid-indep` against `.isAccept`.
  Estimated ~200–300 LoC Lean delta.

- **Layer 5.** CLI surface bump: `Main.lean` pattern-matches on
  `PebbleGameResult` and emits witness lines. Update
  `examples/*.txt`'s commented expected-output blocks. Confirm the
  new format on each fixture. Blueprint: update
  `chapter/executable.tex`'s CLI subsection to describe the
  witness-bearing output schema. Estimated ~50–100 LoC delta to
  `Main.lean` plus the per-fixture comment updates.

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

*(Filled in as cross-cutting lessons surface. Likely candidates:
the *Strengthen past results to reduce duplication* principle that
drove the maximal-reshape choice — a project-philosophy entry for
`../DESIGN.md` once Layer 3 closes; and the *Blueprint reshape
in-place per Layer* sequencing decision — a workflow-mode entry for
`../blueprint/DESIGN.md` if the pattern recurs in future
structural-edit phases.)*

### Cleanup pass summaries

*(Not applicable until after phase close.)*

## Blockers / open questions

- **Layer 1 micro-call:** in-file extension vs `Search/Reachability.lean`
  split. Resolved by `Search/DFS.lean` LoC after Layer 1's body
  lands.

- **Layer 4 micro-call:** how to phrase `runPebbleGame_correct`'s
  Phase-9-era statement against the verdict. Two options: (a)
  deprecate it (`@[deprecated PebbleGameResult (since :=
  "narrative-bridge")]`); (b) restate it as
  `G.IsSparse k ℓ ↔ (runPebbleGame G k ℓ).isAccept`. Decision at
  Layer 4 entry; (b) is closer to the existing API and likely the
  right call.

- **Layer 5 micro-call:** the four `examples/*.txt` files'
  commented expected-output blocks will grow visibly on the Moser
  spindle / $K_4$ cases (11 ARCS lines and an N-vertex BLOCKING
  block respectively). A Layer-5-time decision whether to truncate
  the comment blocks or keep them complete.

## Hand-off / next phase

*(Filled in at phase close. Phase 11 hand-off candidates:
component pebble game (L–S §5, $O(n^2)$ speedup via union pair-find
maintained across the fold); Henneberg-sequence extraction (L–S §6);
benchmarks harness comparing `runPebbleGameExec` against a
brute-force `Decidable` baseline on small graphs.)*
