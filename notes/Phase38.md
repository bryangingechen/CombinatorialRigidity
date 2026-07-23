# Phase 38 — Long-proof de-duplication / missing-abstraction extraction (FACTOR, post-program) (work log)

**Status:** in progress (opened 2026-07-23).

## Current state

**Tier 2 complete; Tier 1 complete; Tier 3 T3a landed** (T2a–d, T1a, T1b, T3a landed;
T1c DROPPED as against-grain — see *Decisions made* / worklist). Next concrete step:
**Tier 3 — T3b** — the seed-shot combinator (product → `exists_eval_ne_zero` → per-factor;
the 21× repetition). Then T3c/T3d → T4.

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
- [x] **T1b `@[simp] mem_edgeFiber : p ∈ edgeFiber e n ↔ p.1 = e`** — DONE. Landed in
  `Deficiency.lean` right after the `edgeFiber` def (`Iff.rfl` proof). `@[simp]` stuck
  clean (no `simpNF`, `lake lint` passing) — precedent: the sibling `mem_fiberAtVertex`
  (`EdgeSplitting.lean:226`) is already `@[simp]` with the identical shape. All 36×
  `rw [edgeFiber, Set.mem_setOf_eq]` sites (5 files) mechanically refactored to
  `mem_edgeFiber`. A dedicated `fiberAtVertex`/`edgeFiber` bridge (step 4, optional) was
  **not** added: `hfibsub`/`hfibdecomp` in `forest_surgery_count` depend on case-specific
  hyps (`hdeg2`, `hla`/`hlb`) tying `v`'s two incident edges to `eₐ`/`e_b` — a generic
  bridge lemma for that shape is Tier-3-sized, not a trivial simp fact; skipped per the
  step's own "skip if not obviously worth it" gate.
- [~] T1c `register_simp_attr` bundles — **DROPPED (against-grain, idiom-fit check failed).**
  The project's landed idiom is `simp only`/`grind only` with an *explicit* lemma
  list precisely to **pin the set + avoid drift** (DESIGN.md §grind-only 754–763,
  TACTICS-GOLF §1; no `@[grind]` ambient tags, no `register_simp_attr` anywhere). A
  named set reintroduces the invisibility+drift that idiom rejects (a stray
  `@[ofNormals_eval]` tag silently changes every callsite). The project's own remedy
  for the ~50× eval-lemma repetition is **fused lemmas** — which is T1a (landed) and
  T3a (queued). Intent redirected to T3a; DESIGN.md grind-only passage extended to
  name this decision.

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
- [x] **T3a Orientation-agnostic `ofNormals_panelRow_eq_hingeRow_of_ends_or_swap`** — DONE.
  Fused row lemma (`PanelHinge.lean`, next to T1a's `ofNormals_supportExtensor_eq_panel_of_ends`)
  keyed on `hends : ends e = (u,w) ∨ (w,u)`, absorbing `panelSupportExtensor_swap` +
  `annihRow_neg` (new, `PanelLayer.lean`) + `hingeRow_swap` once. Collapsed 3 CaseII panelRow
  double-branches (`hrow_a_eq`/`hrow_b_eq`/`he₀_rows_mem`) + removed dead `hFG_eb`.
  `case_II_realization_all_k` 908 → 803 lines; file 1205 → 1100 (net −105). Support-extensor
  sign/nonzero sites (`hFG_ea`/`hso_span`/`hne_G`) left (non-row shape). See *Decisions made*.
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

Tier 2, T1a, T1b, and T3a are complete (T1c dropped). Next work commit: **Tier 3 — T3b**
— the seed-shot combinator abstracting the `product → MvPolynomial.exists_eval_ne_zero →
per-factor eval ≠ 0` shot (21× across the realization producers; the pattern at
`case_II_realization_all_k`'s final assembly, `Q_rk`/`Q_gp` mul + `exists_eval_ne_zero`,
is the canonical instance). Bundle the mul-nonzero + `map_mul` split + per-factor
extraction into one combinator. After T3b: T3c (disjoint-family count), T3d (ℤ↔ℕ rank
bridge), T4 (top-level Framework glue).

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
- **T1b `@[simp] mem_edgeFiber`** — DONE. `@[simp]` stuck (no `simpNF`, `lake lint` clean) —
  matches the sibling `mem_fiberAtVertex`, already `@[simp]` with the identical membership
  shape. All 36 `rw [edgeFiber, Set.mem_setOf_eq]` sites (5 files: `Deficiency.lean`,
  `Operations.lean`, `ReducibleVertex.lean`, `ForestSurgery/{EdgeSplitting,Reduction}.lean`)
  refactored to `rw [mem_edgeFiber]`/`simp only [mem_edgeFiber]` — a mechanical 1:1 site
  substitution since every occurrence was already a single-line `rw`/`simp only`, so this is
  a char-width win, not a line-count one: net **+7 lines** (the new 7-line lemma+docstring;
  the 36 refactored call sites are each still 1 line). The optional `fiberAtVertex`/`edgeFiber`
  bridge (step 4) was skipped — see the T1b worklist entry above.
- **T3a `ofNormals_panelRow_eq_hingeRow_of_ends_or_swap`** — DONE. Fused *row* lemma
  (`PanelHinge.lean`, `PanelHingeFramework` ns, after T1a's `ofNormals_supportExtensor_eq_panel_of_ends`):
  `(G)(ends)(q){e u w}(hends : ends e = (u,w) ∨ (w,u))(t₁ t₂) ⇒ (ofNormals G ends q).toBodyHinge.panelRow
  ends (e,t₁,t₂) = hingeRow u w (annihRow (panelSupportExtensor (q u ·) (q w ·)) t₁ t₂)`. The swapped
  branch's three signs cancel: `panelSupportExtensor_swap` (extensor) + `annihRow_neg` (new, `PanelLayer.lean`,
  `c=-1` companion of `annihRow_smul`) + `hingeRow_swap` (endpoints). **Took `G ends q` all-explicit** —
  the T1a idiom-entry lesson — so the `rw` fires without pinning implicits. Collapsed the 3 CaseII panelRow
  double-branches (`hrow_a_eq`/`hrow_b_eq`/`he₀_rows_mem`; the last MERGES its (a,b)/(b,a) branches into
  one) + removed the dead `hFG_eb` disjunction. `case_II_realization_all_k` 908 → 803; file 1205 → 1100
  (net −105). Left the support-*extensor* sign/nonzero sites (`hFG_ea`, `hso_span`, `hne_G`) — a
  non-row shape the row lemma can't state (T2c "extract the clean win"). Axioms unchanged (standard three).

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN
- *A fused `rw` lemma whose target endpoints are implicit collapses only concrete-endpoint
  sites; a self-referential `rfl`/`Prod.mk.eta` `hf` breaks HO unification for the
  function-valued implicit* → FRICTION [idiom] *A fused `rw` lemma whose target endpoints…*
- *Orientation-agnostic fused row lemma (all-explicit args + disjunction hyp) collapses the
  CaseII `ends = (u,w) ∨ (w,u)` double-branches; needed `annihRow_neg`* → FRICTION [resolved]
  *Orientation-agnostic fused row lemma collapses the CaseII…*
