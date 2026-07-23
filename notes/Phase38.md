# Phase 38 — Long-proof de-duplication / missing-abstraction extraction (FACTOR, post-program) (work log)

**Status:** in progress (opened 2026-07-23).

## Current state

Next concrete step: **the #4≡#5 cut-edge unification prototype** (Tier 2,
item T2a below) — extract a shared `cutEdge_assemble_rank` helper from
`case_cut_edge_realization_gen` and `case_cut_edge_realization_gp_gen`
(`AlgebraicInduction/Theorem55.lean:1224` / `:1636`), keeping both pinned
names as thin wrappers, and collapse each proof's `|C|=0`/`|C|=1` split.
Target ~400 lines removed. This is the deliberate "validate the biggest
structural bet first" opening move (user directive); the rest of the plan
is sequenced only after the parameterized-engine pattern is proven on it.

Phase scaffolding (this note + ROADMAP row/§38 + queue update) is the
opening commit; no Lean touched yet.

## Architectural choices made up front

- **Internals-only; no headline/axiom change (the phase contract).** Like
  AUTOMATE / AUTOMATE-Z (Phases 36/37), FACTOR changes no headline
  statement. Unlike them it is **not** build-neutral: it *adds* helper
  lemmas, unifies duplicate proofs, and restructures bodies. The invariant
  to hold and re-verify at close: every headline theorem's `#print axioms`
  profile is unchanged (the standard three).
- **Preserve pinned names as thin wrappers (lowest-churn blueprint
  discipline).** Every long proof targeted here is `\lean{...}`-pinned in
  `blueprint/src/chapter/molecular-induction.tex` (and one in the top-level
  API). When a duplicate *pair* is unified, keep **both** original names as
  thin wrappers over the new shared helper — the pins never move, the
  blueprint stays green, and the bodies still collapse. Only mint a repin
  when a name is genuinely retired. The fiber pair (`_fiber_subset` /
  `_fiber_lt`) already shares one node (molecular-induction.tex:745–746),
  so its unified successor can be added to that node's `\lean{}` list
  additively; the cut-edge pair sits on two nodes (:1324, :1358), so both
  wrappers stay.
- **Reader-facing surfaces untouched (matches 36/37).** README /
  home_page / intro.tex / formalization.yaml `scope` narrate math news at
  the arc/chapter level and stop at Phase 35; a proof-engineering refactor
  carries no such news, so this phase touches only ROADMAP (table + §38 +
  queue) and the notes — exactly the 36/37 footprint. This is a
  deliberate application of the jargon-free discipline, **not** a skipped
  phase-open checklist item.

## Per-slice gate (every work commit)

1. **Blueprint pin/docstring gate.** Before committing a slice that renames
   or retires a pinned decl: `grep -rn <name> blueprint/src/` and repoint
   the `\lean{...}` (or, for unifications, extend the node's list with the
   successor); `grep -rn <name>` repo-wide and repoint any surviving
   docstring / comment cross-reference — in the *same* commit
   (CLAUDE.md *deletion/retirement* + *additive-successor* variants).
   Prefer the thin-wrapper pattern above so this reduces to a no-op.
2. **Build + neutrality.** `lake build` green; the refactored proof compiles.
   Watch proof-term/build-time regressions (extracting a helper can change
   defeq exposure — the AUTOMATE-Z fragility catalog, `TACTICS-GOLF.md` §7,
   applies).
3. **Axiom spot-check** on any headline theorem downstream of a touched
   lemma (`#print axioms` / `lean_verify`); full re-verify of all headlines
   at phase close.

## Worklist (ROI-ordered; the analysis behind it is in the phase-open session)

The 10 longest proofs (~3,600 lines total) fall into the patterns below;
conservative addressable total ~1,000–1,500 lines. Sourced from a 4-way
parallel read of the clusters (CaseII giant; CaseIII/Theorem55 realization;
ForestSurgery/splitOff; MatroidIdentification + abstraction survey).

**The recurring patterns (the "why"):**
- P1 **Near-duplicate proofs that should be one parameterized lemma** —
  the dominant waste, in every cluster.
- P2 **No named simp sets anywhere in the project** → the same
  unfold-then-membership micro-idiom hand-written 100s of times.
- P3 **Orientation/sign double-branching** (`ends e = (u,w) ∨ (w,u)`), the
  swap absorbed by hand each time.
- P4 **ℤ↔ℕ rank/deficiency casting** chains.
- P5 **Two combinators**: the product→`exists_eval_ne_zero` seed shot (21×)
  and the disjoint-family `∑|Fs i|=|⋃|` count (6+×).
- Split diagnosis: **Molecular is over-abstracted-but-duplicated**
  (consolidate); the **top-level `Framework`/`rigidityRow` API is missing
  glue** (add lemmas). Different fixes.

### Tier 1 — hoist + name (cheap, broad, low-risk)
- [ ] T1a Hoist `PanelHingeFramework.ofNormals_supportExtensor_eq_panel_of_ends`
  from `CaseIII/Relabel/ForkedArm.lean:123` up to `PanelHinge.lean` (next to
  `toBodyHinge_supportExtensor:95`). Unreachable-by-file-order today ⇒ CaseII
  re-derives it by hand **16×**. ~150–200 lines across CaseII.
- [ ] T1b `@[simp] mem_edgeFiber : p ∈ edgeFiber e n ↔ p.1 = e` (+ a
  `fiberAtVertex`/`edgeFiber` bridge). Kills 35× `rw [edgeFiber, Set.mem_setOf_eq]`.
- [ ] T1c `register_simp_attr` bundles: an `ofNormals_eval` set
  (`ofNormals_normal`/`ofNormals_ends`/`toBodyHinge_supportExtensor`, ~50×)
  and the rigidity-row-apply set. (First `register_simp_attr` in the project.)

### Tier 2 — unify the duplicate pairs (biggest payoff, higher risk)
- [ ] **T2a (FIRST) cut-edge: `cutEdge_assemble_rank` helper** parameterized by
  the assembled `F`, `hcut_le`, the two side finrank equalities, and the
  cut-edge count ∈ {0,1}; `_gen` and `_gp_gen` become thin wrappers; drop the
  `rcases cutEdges` split via `interval_cases`/`omega` on the count. ~400 lines.
- [ ] T2b splitOff extend: `splitOff_reroute_packing` engine; `_fiber_subset`
  = empty-pendant instance of `_fiber_lt`'s pool. ~170–200 lines.
- [ ] T2c reroute mirror: one substitution lemma shared by
  `isAcyclicSet_splitOff_reroute` (:478) and
  `isAcyclicSet_mulTilde_of_splitOff_reroute` (:687). ~60–80 lines.

### Tier 3 — the recurring combinators (spread across clusters)
- [ ] T3a Orientation-agnostic `panelRow_of_isLink` (absorbs the swap once);
  kills the ~14 `rcases … with h|h` in CaseII. ~150 lines.
- [ ] T3b Seed-shot combinator (product → `exists_eval_ne_zero` → per-factor).
- [ ] T3c Disjoint-family count helper (shapes A+B in ForestSurgery).
- [ ] T3d ℤ↔ℕ rank bridge carrying the target dim in both ℕ and ℤ; +
  `IsKDof`/`IsMinimalKDof` body-surfacing helper (matches an existing FRICTION note).

### Tier 4 — the top-level Framework glue (pays off 3×)
- [ ] T4 A small glue layer for `typeII_edgeSetRowIndependent_extend`
  (+ verbatim siblings `typeI_…`, `typeI_pendant_…`): bundled
  new-row-at-elim-motion→scalar reduction; `oldSpan ≤ ker(eval)` lemma;
  finite-set `LinearIndepOn`-peeling sugar. ~90–120 lines × 3 sites.

## Blockers / open questions

- T2a design: does the shared helper want `F : BodyHingeFramework` abstractly,
  or does `_gp_gen`'s `ofNormals … endsOf` build vs `_gen`'s raw `extF` block
  reuse? (The reader flagged `_gen`'s raw `extF` as strictly worse — consider
  rebasing `_gen` onto `ofNormals`/`endsOf` as part of T2a, or defer to a
  follow-up.) Settle during the prototype.

## Hand-off / next phase

First work commit: **T2a** — land `cutEdge_assemble_rank` and rewrite
`case_cut_edge_realization_gen`/`_gp_gen` as thin wrappers, `lake build`
green, axioms of the cut-edge-dependent headline unchanged. If the pattern
holds cleanly, proceed T2b → T1(a/b/c) → T3 → T4; if it fights defeq
(carrier fragility), fall back to Tier 1 cheap wins and reassess T2 scope.

## Decisions made during this phase

### Phase-local choices and proof techniques
- Codename **FACTOR**; opened ahead of the queued PIN phase at the user's
  initiative (PIN now next-after-38), mirroring how 36/37 were spun off.
- First move = validate the biggest bet (T2a) before building the rest
  (user directive), rather than cheap-wins-first.
