# Phase 38 — Long-proof de-duplication / missing-abstraction extraction (FACTOR, post-program) (work log)

**Status:** in progress (opened 2026-07-23).

## Current state

**All worklist slices landed** (Tiers 1–4: T2a–d, T1a, T1b, T3a, T3b, T3c, T3d, T4;
T1c DROPPED as against-grain; T3d part (a) skipped-as-diffuse — see *Decisions made* /
worklist). Next concrete step: the **Phase-38 CLOSE checklist** (`PHASE-BOUNDARIES.md`
*When this commit closes a phase*) — re-thin the ROADMAP row + §38, compress this note,
sync status surfaces (`formalization.yaml` alignment via `#print axioms` — already spot-checked
clean), the blueprint-chapter re-read + exposition-ledger, project-organization review. FACTOR
changed no headline, so the reader-facing surfaces stay untouched (see *Architectural choices*).

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
- [x] **T3b Seed-shot combinator** — DONE. `MvPolynomial.exists_eval_ne_zero_of_forall_ne_zero`
  (indexed, `[Finite ι]`) + `exists_eval_ne_zero₂/₃/₄` wrappers added to the mirror
  `Mathlib/Algebra/MvPolynomial/Funext.lean` (mathlib ns, upstream-eligible), next to the base
  `exists_eval_ne_zero`. 13 core seed-shot sites collapsed to one-line `obtain`s (CaseII 1, CaseI 3,
  Theorem55 2, Coupling 5, CaseIII/Realization 2); −59 call-site lines, +47 reusable mirror lines
  (net −12). GenericityDevice.lean had NO actual obtain sites (prose-only). 1 multi-factor site left
  in the non-core `Molecule/Theorem56.lean:144` (2-factor) — candidate T3b-follow. FRICTION
  [mirrored] added; axioms unchanged (standard three).
- [x] **T3c Disjoint-family count helper** — DONE. Mirrored `Set.ncard_iUnion_of_fintype`
  (`Mathlib/Data/Set/Card/Arithmetic.lean`, new mirror file); mathlib search (`lean_loogle`/
  `lean_leanfinder`) confirmed the `[Fintype ι]`/`Finset.sum` equality is absent (only the
  `[Finite ι]`/`finsum` and `[Fintype ι]`/`≤` members exist). All 8 sites (`Deficiency.lean`,
  `EdgeSplitting.lean` ×2, `Reduction.lean` ×3, `Application.lean`) collapsed to a single lemma
  call. See *Decisions made*.
- [x] **T3d `IsKDof.deficiency_eq` / `IsMinimalKDof.deficiency_eq` accessors** — DONE (part (b)).
  **Part (a) ℤ↔ℕ rank bridge SKIPPED as diffuse** (disciplined skip, cf. T1c): the two
  genuinely-repeated shapes (`toNat_le_of_add_pred_eq`, `sub_toNat_eq_of_add_pred_eq`) are already
  in `RigidityMatrix/Basic.lean`; the remaining `toNat`/`Nat.cast_sub` sites each cast a *different*
  subtraction structure (`screwDim−1`, `D·(Gab−1)−(D−2)`, `ncard−1`, whole-expr `.toNat`,
  `D·(V−1)−c.toNat`) — the `hZ_eq` cast-target shape is a singleton, so no bridge collapses ≥3
  sites cleanly. **Part (b)** added the two accessors to `Deficiency.lean` (after each `def`) and
  swept ~35 `hG.1` / `rw [IsKDof]` surfacing sites to `hG.deficiency_eq` (8 files). See *Decisions made*.

### Tier 4 — the top-level Framework glue (pays off 3×)
- [x] **T4 top-level Framework/rigidityRow glue** — DONE. Two glue lemmas in `RigidityMatroid.lean`
  (both `rigidityRow` facts, after the lift-glue section): `rigidityRow_none_some_elim`
  (new-edge row at an elim-motion → `⟪q - p' x, α⟫`) collapses the 5-lemma micro-idiom at ~9
  sites; `oldSpan_le_ker_eval_elim` (span of lifted old rows ≤ ker(eval at elim-motion))
  collapses the ~8-line `span_le`+`rintro`+`induction` block to 3 lines at all 3 sites. **All
  three of the trio refactored** (byte-identical signatures preserved). The 3rd candidate
  helper (finite-set `LinearIndepOn`-peeling) was **not** minted — it doesn't collapse across
  the trio (typeI uses `pair_iff`, pendant `singleton_iff`, only typeII the 3-`insert` chain);
  the typeII `Function.update`-motion + `h_f_eq` collinear-combo sites are non-elim shapes, left
  as-is. `MatroidIdentification.lean` −31 (proof bodies); `RigidityMatroid.lean` +40 (2 reusable
  helpers + docstrings) — a centralization win (the elim-motion inner-product math + old-span
  argument now each live once), not a raw line-count win. Axioms unchanged (standard three).

## Blockers / open questions

- None open. (T2a/T2b/T2c settled — see *Decisions made*.)

## Hand-off / next phase

**All worklist slices landed** (Tiers 1–4; T1c dropped; T3d part (a) skipped-as-diffuse). Next
commit: the **Phase-38 CLOSE checklist** (`PHASE-BOUNDARIES.md` *When this commit closes a
phase*) — flip + re-thin the ROADMAP row, compress §38 + this note, sync status surfaces
(`formalization.yaml` alignment via `#print axioms`; FACTOR changed no headline so README /
home_page / intro.tex stay untouched — see *Architectural choices*), the blueprint-chapter
re-read + exposition-ledger, project-organization review. Possible small follow-ups (not blocking
close): T3b-follow (lone non-core seed-shot at `Molecule/Theorem56.lean:144`, 2-factor).

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
- **T3b `exists_eval_ne_zero_of_forall_ne_zero` (+ `exists_eval_ne_zero₂/₃/₄`)** — DONE. Combinator
  form chosen: **indexed general lemma + n-ary wrappers derived from it** (the wrappers centralize
  the product logic — right shape for a de-dup phase; call sites use the wrappers since all arities
  are fixed 2–4). Added to the mirror `Mathlib/Algebra/MvPolynomial/Funext.lean` (mathlib ns,
  upstream-eligible). Refactored 13 core seed-shot sites (CaseII 1, CaseI 3, Theorem55 2, Coupling 5,
  CaseIII/Realization 2) to one-line `obtain ⟨q, hqA, hqB, …⟩ := exists_eval_ne_zeroₙ …`; each drops
  the `mul_ne_zero` chain + `rw [map_mul…]` + per-factor `fun h => hq (by rw [h]; ring)` peels.
  1 non-core multi-factor site left (`Molecule/Theorem56.lean:144`). −59 call-site lines / +47 mirror
  (net −12). FRICTION [mirrored]. Axioms unchanged.
- **T3c `Set.ncard_iUnion_of_fintype`** — DONE. Mathlib search first (`lean_loogle`/`lean_leanfinder`
  against `Set.ncard (⋃ i, s i) = Finset.sum`) confirmed the equality member of the `[Fintype ι]` /
  `Finset.sum` family is absent from `Mathlib/Data/Set/Card/Arithmetic.lean` (only `ncard_iUnion_of_finite`
  `[Finite ι]`/`finsum` and `ncard_iUnion_le_of_fintype` `[Fintype ι]`/`≤∑` exist) — mirrored, matching
  that file's naming family. `(hs : ∀ i, (s i).Finite) (h : Pairwise (Function.onFun Disjoint s)) :
  (⋃ i, s i).ncard = ∑ i, (s i).ncard`, one-line proof fusing `ncard_iUnion_of_finite` +
  `finsum_eq_sum_of_fintype`. Refactored all 8 sites (`Deficiency.lean` 1, `EdgeSplitting.lean` 2,
  `Reduction.lean` 3, `Application.lean` 1); each was already a single `rw`/`rw[←…]`, so the win is
  chain-width (2 rewrites → 1, or → a bare `.symm` term) not line-count: −2 net across the 4 call-site
  files, +41 new mirror-file lines. FRICTION [mirrored]. Axioms unchanged (standard three).
- **T3d `IsKDof.deficiency_eq` / `IsMinimalKDof.deficiency_eq`** — DONE (part (b)). Two body-surfacing
  accessors in `Deficiency.lean` (after each `def`): `IsKDof.deficiency_eq (h) := h`,
  `IsMinimalKDof.deficiency_eq (h) := h.1` (both `: G.deficiency n = k`, defeq-trivial). Swept ~35
  `def`-opacity surfacing sites (`have := hG.1`, `rw [hG.1]`, `rw [← hG.1]`, `hG.1 ▸`,
  `hG.1.symm(.trans)`, `rw [IsKDof] at h`) across 8 files to `hG.deficiency_eq`. **Left** the
  `hG.1`-as-k-dof-*value* argument sites (`two_le_degree_of_isKDof_zero … hG.1`, etc.) — accessor is
  for the *equation* only. Net **+13** Lean lines (accessors + one long-line split; the call-site
  swaps are char-width, cf. T1b) — a friction/readability win, not line-count. Axioms unchanged.
  **Part (a) ℤ↔ℕ rank bridge SKIPPED as diffuse** (cf. T1c disciplined skip): repeated shapes already
  in `Basic.lean` (`toNat_le_of_add_pred_eq`, `sub_toNat_eq_of_add_pred_eq`); remaining cast sites
  each differ (singleton `hZ_eq` cast-target shape), no ≥3-site clean collapse.

- **T4 `rigidityRow_none_some_elim` / `oldSpan_le_ker_eval_elim`** (`RigidityMatroid.lean`, after
  the lift-glue section, general `d`) — detail in the worklist [x] T4 entry + FRICTION [resolved].
  Verdict: two internal `rigidityRow` glue lemmas collapse the recurring elim-motion→scalar and
  lifted-old-span≤ker reductions across all three of the trio (byte-identical signatures kept). The
  `LinearIndepOn`-peeling candidate was skipped (trio arities differ; no shared peeler). Needed
  `open scoped InnerProductSpace` in `RigidityMatroid.lean`. −31 bodies / +40 helpers (centralization
  win, not raw lines). Axioms unchanged (verified via `#print axioms` on the trio + the two
  matroid-identification headlines + `isGenericallyRigid_two_iff_exists_isLaman_le`).

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN
- *Top-level Henneberg row-LI lifts hand-wrote the elim-motion→scalar + lifted-old-span≤ker
  reductions → two glue lemmas in `RigidityMatroid.lean`* → FRICTION [resolved] *Top-level
  Henneberg row-LI lifts hand-wrote the same "elim-motion → scalar inner product"…*
- *A fused `rw` lemma whose target endpoints are implicit collapses only concrete-endpoint
  sites; a self-referential `rfl`/`Prod.mk.eta` `hf` breaks HO unification for the
  function-valued implicit* → FRICTION [idiom] *A fused `rw` lemma whose target endpoints…*
- *Orientation-agnostic fused row lemma (all-explicit args + disjunction hyp) collapses the
  CaseII `ends = (u,w) ∨ (w,u)` double-branches; needed `annihRow_neg`* → FRICTION [resolved]
  *Orientation-agnostic fused row lemma collapses the CaseII…*
- *`IsKDof`/`IsMinimalKDof` def-opacity surfacing → `.deficiency_eq` accessor; keep `.1` for
  k-dof-value args* → TACTICS-GOLF §4 (note updated) + FRICTION [resolved] *`IsKDof` /
  `IsMinimalKDof` def-opacity … `.deficiency_eq`*
