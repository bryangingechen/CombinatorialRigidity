# Phase 38 — Long-proof de-duplication / missing-abstraction extraction (FACTOR, post-program) (work log)

**Status:** in progress (opened 2026-07-23).

## Current state

**Tier 2 complete**; **Tier 1 T1a complete** (T2a/T2b/T2c/T2d and T1a landed — see
*Decisions made*). Next concrete step: **Tier 1 — T1b** — add `@[simp] mem_edgeFiber :
p ∈ edgeFiber e n ↔ p.1 = e` (+ a `fiberAtVertex`/`edgeFiber` bridge), killing the ~35×
`rw [edgeFiber, Set.mem_setOf_eq]`. Then T1c → T3 → T4.

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
- [x] **T1a Hoist `PanelHingeFramework.ofNormals_supportExtensor_eq_panel_of_ends`** —
  DONE. Landed in `PanelHinge.lean` (after `ofNormals_normal`, not beside
  `toBodyHinge_supportExtensor:95` — the lemma needs `ofNormals`/`ofNormals_{normal,ends}`,
  all defined lower in that same file). **14 of 18** hand-chains collapsed (12 in
  `case_II_realization_all_k` + 2 in the `case_II_placement_eq612` sibling); the **4
  general-edge sites** left as hand-chains (they read `(Q.ends e).1/.2`, no concrete
  endpoint pair, so the fused lemma's implicit `{x y}`/`endsσρ` HO-unify to a broken
  `Prod.mk ?x` — see FRICTION [idiom]). `case_II_realization_all_k` ~930 → ~909; CaseII
  file 1228 → 1205 (net −23). Not the ~150–200 estimated (each chain is ~3 physical
  lines, not ~4).
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
- [x] **T2d (cut-edge follow)** — DONE. **(a)** `hFE₁` internalized into
  `cutEdge_finrank_assemble` (derived from its `hFgraph` param; param dropped, the 3
  byte-identical call-site copies deleted). **(b) via Route B1** (not B2): new `private`
  brick `span_rigidityRows_side_eq` (agreement-hypothesis parameterized) collapses the
  4 byte-identical `_gen` span blocks to one-line calls; B2 (`ofNormals` rebase of `_gen`)
  not attempted — B1 was clean first build. File −54 lines; axioms unchanged. **Closes Tier 2.**
- [x] **T2b splitOff extend: `splitOff_reroute_packing` engine** — DONE. Single
  `private` engine does the whole construction; both public arms are thin
  wrappers selecting one of two guarded count-implications. Pendant pool built
  internally (can't be a parameter — depends on internal `S`/`Simg`); shared
  setup + `hfinish` (indep + survivor + count-sum) once; two internal arms via
  `by_cases` on `(I' ∩ ẽ₀).ncard = bodyHingeMult n`. File −155 lines; axioms
  unchanged.
- [x] **T2c reroute mirror: `exists_directedWalk_of_isCyclicWalk_isLink` combinator**
  — DONE (piece 1 only). Shared `private` rotate+reorient brick behind both mirror
  lemmas (forward 1×, reverse 2×); both wrappers keep pinned signatures (:542/:694,
  NO repin). File −61 lines; axioms unchanged. Full substitution unification
  (piece 2) deferred — directions diverge (opposite lifts, 2-path vs 1-edge).

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

- None open. (T2a/T2b/T2c settled — see *Decisions made*.)

## Hand-off / next phase

Tier 2 and Tier 1 T1a are complete. Next work commit: **Tier 1 — T1b** — add
`@[simp] mem_edgeFiber : p ∈ edgeFiber e n ↔ p.1 = e` (in the file that defines
`edgeFiber`), plus a `fiberAtVertex`/`edgeFiber` bridge, to kill the ~35×
`rw [edgeFiber, Set.mem_setOf_eq]` micro-idiom. After T1b: T1c → T3 → T4.

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
- **T2b `splitOff_reroute_packing`** (private, `EdgeSplitting.lean`): engine
  `(hD)(hab hav hbv heab)(hla hlb)(he₀){I'}(hI') ⇒ ∃ I, Indep I ∧ (survivor:
  I∖(ẽₐ∪ẽ_b)=I'∖ẽ₀) ∧ ((I'∩ẽ₀).ncard = bodyHingeMult n → I.ncard+1 = I'.ncard+D)
  ∧ ((I'∩ẽ₀).ncard < bodyHingeMult n → I.ncard = I'.ncard+D ∧ (I∩ẽ_b).ncard =
  (I'∩ẽ₀).ncard+1)`. **Unlike T2a, the delta could not be a parameter**: the
  pendant pool depends on the internal disjointification (`S`/`Simg`/`U`), so
  the engine builds it internally, split by `by_cases (I'∩ẽ₀).ncard =
  bodyHingeMult n` — the two arms' distinct counts (`+D−1` full vs `+D` partial)
  ride two guarded implications; wrappers select one. Shared setup + a `hfinish`
  ∀-family lemma (indep + survivor + count-sum, keyed on `hcore_of_ne`/`hDscore`/
  `hrOf_notin` interface) live once. −155 lines net; axioms unchanged. Gotchas
  → TACTICS-QUIRKS § 98 (rw a `set`-var) / FRICTION [resolved].
- **T2c `exists_directedWalk_of_isCyclicWalk_isLink`** (private, `EdgeSplitting.lean`):
  `(IsCyclicWalk C)(e ∈ C.edgeSet)(IsLink e s t) ⇒ ∃ w, IsWalk w ∧ w.first=t ∧
  w.last=s ∧ w.edgeSet ⊆ C.edgeSet ∧ w.edge.Nodup ∧ e ∉ w.edge`, polymorphic in the
  edge type. Folds rotate-to-first-edge + reverse-or-not reorientation into one brick,
  used 3× (forward 1×, reverse 2×). **Only piece 1 landed**: the full substitution
  unification (piece 2) was not forced — opposite lifts (Ksp→K vs K→Ksp) + 2-path vs
  1-edge resist one wrapper. Fixing output to `t→s` collapsed the forward orientation
  `rcases` (dropped its `a ≠ b` need). −61 lines net; axioms unchanged. Build gotchas
  (both already covered): `subst e'` not `subst hee'` (TACTICS-QUIRKS § 4);
  `IsClosed = first = last` ⇒ `cons_isClosed_iff` gives `x = w'.last`.
- **T2d `span_rigidityRows_side_eq`** (private, `Theorem55.lean`) + `hFE₁` internalized:
  **(a)** `cutEdge_finrank_assemble` now derives `hFE₁` from its `hFgraph` param (the
  `_gp_gen` `rw [hFgraph]` form, valid when `hFgraph` is `rfl` too), so both producers dropped
  the param + their 3 byte-identical copies. **(b) Route B1**: brick `(sideExt)(Fᵢ)(hFᵢg)(hagree:
  ∀ e u v, Gᵢ.IsLink e u v → sideExt e = Fᵢ.supportExtensor e) ⇒ span-rigidityRows equality`;
  simp's projection reduction + the `hagree` rewrite absorb the extensor swap, so the 4
  byte-identical `_gen` span blocks become one-line calls (the agreement lambda picks the `extF`
  branch). B2 (`ofNormals` rebase) not attempted — B1 clean on first build. −54 lines net; axioms
  unchanged. **Closes Tier 2.**
- **T1a hoist `ofNormals_supportExtensor_eq_panel_of_ends`** — DONE. Moved (with docstring)
  from `CaseIII/Relabel/ForkedArm.lean` up to `PanelHinge.lean` (placed after
  `ofNormals_normal`, its lowest dependency in that file; *not* at `toBodyHinge_supportExtensor`
  as the worklist guessed). Name/namespace unchanged, so the 2 ForkedArm callers + blueprint
  (unpinned) are unaffected. CaseII (which imports PanelHinge via CaseI→Coupling→GenericityDevice)
  now reaches it: **14 of 18** hand-chains collapsed to a single `rw`. The **4 general-edge sites**
  (`(Q.ends e).1/.2`, no concrete pair) resist — the fused lemma's implicit `{x y}`/`endsσρ`
  HO-unify to a broken `Prod.mk ?x`; left as hand-chains (FRICTION [idiom]). CaseII 1228 → 1205
  (net −23); axioms of `molecular_conjecture`/`case_II_realization_all_k` unchanged (standard three).

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN
- *A fused `rw` lemma whose target endpoints are implicit collapses only concrete-endpoint
  sites; a self-referential `rfl`/`Prod.mk.eta` `hf` breaks HO unification for the
  function-valued implicit* → FRICTION [idiom] *A fused `rw` lemma whose target endpoints…*
