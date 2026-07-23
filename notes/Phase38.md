# Phase 38 — Long-proof de-duplication / missing-abstraction extraction (FACTOR, post-program) (work log)

**Status:** in progress (opened 2026-07-23).

## Current state

**T2a landed** (the biggest structural bet, validated first). The shared
rank-arithmetic assembly tail of the two not-2-edge-connected cut-edge
realization producers is now one `private` helper `cutEdge_finrank_assemble`
in `Theorem55.lean`; both `case_cut_edge_realization_gen` / `_gp_gen` keep
byte-identical signatures (blueprint pins untouched) and route their tail
through it, with the cut-edge count kept **abstract** (no per-arm numeral
special-casing). The `_gp_gen` `|C|=0/1` `rcases` collapsed entirely; `_gen`
keeps its split (extF/hlinks genuinely differ per arm, as expected). File
net −67 lines; both headline theorems' axioms unchanged (standard three).
The parameterized-engine pattern is proven: **proceed to T2b** (splitOff
`_fiber_subset`/`_fiber_lt` unification).

Next concrete step: **T2b** — `splitOff_reroute_packing` engine, making
`_fiber_subset` the empty-pendant instance of `_fiber_lt`'s pool
(`Induction/ForestSurgery/*`); ~170–200 lines. If it fights (defeq/carrier
fragility), fall back to Tier 1 cheap wins (T1a/T1b/T1c) and reassess T2c.

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
- [x] **T2a (FIRST) cut-edge: `cutEdge_finrank_assemble` helper** — DONE.
  Parameterized by the assembled `F` (+ `hFgraph`, `hV₂`), `hcut_le`, the brick
  hyps, `hVcard`/`hk_eq`, and the two span-rewrites `hF₁span`/`hF₂span` to
  abstract `S₁`/`S₂` with lower bounds `hlb₁`/`hlb₂`; cut count kept abstract
  (no `interval_cases` needed). `_gp_gen` `rcases` collapsed; `_gen` split kept
  (extF/hlinks differ). File −67 lines net (helper 47 lines absorbs ~131 of
  duplicated tail across the 4 arms).
- [ ] T2a-follow (optional depth, deferred under autopilot): the cut-edge zone
  still has ~150–220 removable lines — the 4 near-identical ~38-line
  `hF₁span`/`hF₂span` blocks (rebase `_gen`'s raw `extF` onto `ofNormals`/`congr 1`,
  the CaseIII agent's item #5) + a fuller `|C|` collapse in `_gen`. Low-priority.
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

- (T2a settled) The helper takes `F : BodyHingeFramework` **abstractly** with
  `hFgraph : F.graph = G`; it does *not* require rebasing `_gen`'s `extF` onto
  `ofNormals`. The abstract-`F` route absorbs both builds cleanly — the side
  ranks enter as span-rewrites + lower bounds, so `_gen` (raw `extF`, equalities)
  and `_gp_gen` (`ofNormals`, `≤` bounds) both feed the same helper. Rebasing
  `_gen` onto `ofNormals` is no longer needed for de-dup; leave as-is.

## Hand-off / next phase

Next work commit: **T2b** — `splitOff_reroute_packing` engine
(`Induction/ForestSurgery/*`); make `isAcyclicSet_..._fiber_subset` the
empty-pendant instance of `_fiber_lt`'s reroute pool. Both share the node at
`molecular-induction.tex:745–746`, so add the unified successor to that node's
`\lean{}` list additively (per the T2 discipline). If it fights defeq/carrier
fragility, fall back to Tier 1 cheap wins (T1a hoist, T1b/T1c simp sets) and
reassess T2c. Sequence after T2b: T1 → T3 → T4.

## Decisions made during this phase

### Phase-local choices and proof techniques
- Codename **FACTOR**; opened ahead of the queued PIN phase at the user's
  initiative (PIN now next-after-38), mirroring how 36/37 were spun off.
- First move = validate the biggest bet (T2a) before building the rest
  (user directive), rather than cheap-wins-first.
- **T2a `cutEdge_finrank_assemble`** (private, `Theorem55.lean`): abstract `F`
  + `hFgraph`/`hV₂` + brick hyps (`hcut_le`/`hFext`/`hFE₁`/`hFcut`/`hFVne`) +
  `hVcard`/`hk_eq` + `hF₁span`/`hF₂span` → `{S₁ S₂}` + `hlb₁`/`hlb₂` ⇒
  `finrank (span F.rigidityRows) = screwDim k · (|V(G)|−1) − c`. Cut count kept
  abstract; `linarith` over the explicit `hkey` product (not `nlinarith`, per
  the fragility note). Both producers keep pinned signatures; `_gp_gen` `rcases`
  collapsed, `_gen` split kept. −67 lines net; axioms unchanged.
- **The parameterized-engine pattern works with `F` abstract** — the key move is
  passing the *span rewrites* `hF₁span`/`hF₂span` (to abstract `S₁`/`S₂`) plus
  side *lower bounds*, so equality-fed (`_gen`) and `≤`-fed (`_gp_gen`) callers
  unify. Reuse this shape for T2b/T2c. The one gotcha (ℕ-sub cast vs `linarith`
  atoms) → TACTICS-QUIRKS § 47 (Variant) / FRICTION [idiom].
