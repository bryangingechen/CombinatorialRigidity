# Phase 22l — ScrewSpace carrier opacity, part 1: the d=3 API + migration (work log)

**Status:** ✓ complete (opened + closed 2026-06-16).

Structural-edit phase (no new math, no new blueprint chapter): reshape the `ScrewSpace`
carrier from a reducible `abbrev` into an **opaque `def`** with a `mk`/`val`/`≃ₗ` API, then
migrate the existing `d = 3` tree onto it file-by-file along the import spine. The motivation,
the opacity spike, mathlib precedents, the drafted API surface, the per-file recon, and the
now-vs-later analysis are **canonical in `notes/ScrewSpaceCarrier-design.md`** — this note points
there (the API spec is §5; the spike §3; the spine §5; the residual risks OQ1–OQ3) and does
**not** duplicate it. The to-do list lives in the *Layer plan* below (`CLAUDE.md`
*Structural-edit phases*).

## Current state

**✓ COMPLETE — the FLIP landed (2026-06-16).** `abbrev ScrewSpace` → opaque `def` in
`RigidityMatrix.lean` + `ScrewSpace_def` rfl-bridge + 3 `inferInstanceAs` instances
(`AddCommGroup`/`Module`/`FiniteDimensional`); `mk`/`val`/`val_mem` route their Subtype coercion through
`ScrewSpace_def k ▸ …`; `equivExteriorPower` is now the `cast (ScrewSpace_def k)` `≃ₗ` with `cast`-RHS
`_apply`/`_symm_apply` (design doc §5 *L7 refinement*). The whole d=3 spine builds + lints clean on the
opaque carrier. **OQ1 banked:** `case_II_realization_all_k` 600000→default, `case_cut_edge_realization`
400000→default, `case_cut_edge_realization_gp` 600000→400000 (one step, not droppable to default). The
`screwSpace_finrank` `change`-expose was re-tested and **kept** (still needed: the opaque head does not
reduce to the graded-piece head at `rw`'s reducible transparency). The molecular `maxHeartbeats` count is
now **3→1** (the only survivor is `_gp` at 400000). Blueprint untouched (pure implementation refactor;
all statements/types stable).

The FLIP was mechanical because L0a–L9 made the whole spine opacity-ready (L2/L3/L5/L6/L7/L8/L9
migration-free; L0a/L0b/L1/L4 needed edits), and the L9 probe had already exercised the exact RigidityMatrix
recipe end-to-end. Per-layer detail in *Decisions made*; the recon (Shape-1 dead, Shape-2 the only path)
and the recurring gap classes / probe method are canonical in `notes/ScrewSpaceCarrier-design.md` §5.

## Architectural choices made up front

- **Shape 2, API-first then flip-last** (revised at L0a, 2026-06-16). The original plan was
  "flip the carrier to `def` first, then migrate one file green at a time bottom-up." L0a found
  that order **cannot keep the project green**: opacity blocks the bare `⟨val,proof⟩`
  anonymous-constructor idiom *everywhere at once* (~300 reach-in sites across 7 files), so a
  flip-first commit reds the whole downstream chain until L9 — failing CI and the per-commit
  handoff contract. The corrected order: **(1)** land the `mk`/`val`/`equivExteriorPower` API on the
  *still-`abbrev`* carrier (additive, defeq-thin, project-green) — **done, L0a**; **(2)** migrate
  each file's reach-ins onto the API one file at a time down the spine, each commit project-green
  (the abbrev keeps `mk`/`val` defeq no-ops, so a half-migrated tree still builds); **(3)** flip
  `abbrev ScrewSpace`→opaque `def` + add the 3 `inferInstanceAs` instances **last**, once no
  anonymous-constructor / `Subtype`-coercion reach-in remains — a single small mechanical commit
  that lands the perf win and resolves OQ1. (The `inferInstanceAs` named instances are deferred to
  the flip: on the `abbrev` they would be redundant/harmful self-paths; they are only meaningful on
  the distinct opaque head.) The `.val` projection on the abbrev must be written `Subtype.val (C : …)`,
  not `C.val` — the latter recurses into the decl being defined (dot-notation collision with the
  abbrev's underlying `Subtype.val`).
- **Import spine (unchanged):** **RigidityMatrix → PanelLayer → Pinning → PanelHinge →
  GenericityDevice → Coupling → CaseI → CaseII → CaseIII → Theorem55**. `Meet.lean` is pass-through
  (operates on the bare `⋀[ℝ]^j V` Subtype, never returns a `ScrewSpace`-typed value — and its
  anonymous constructors of `⋀[ℝ]^j V`, e.g. the `complementIso` inputs in `RigidityMatrix.lean`,
  survive the flip since only `ScrewSpace` becomes opaque) and `Extensor.lean` / `Deficiency.lean` /
  `Induction/` sit below or beside the carrier — **untouched**.
- **The API surface is canonical in the design doc** (`notes/ScrewSpaceCarrier-design.md` §5
  *The drafted API surface*): `def ScrewSpace`, `ScrewSpace_def`, the 3 named instances,
  `ScrewSpace.mk`/`.val` + simp lemmas, `equivExteriorPower`, the transported `screwBasis`. Do
  not restate it here; refine it *in the design doc* as L0/L1 land if reality diverges.
- **d = 3 scope only; general-`d` API deferred to the Phase-23 design boundary.** Every existing
  `ScrewSpace` reach-in is at `k = 2` / `d = 3`. Freezing an opaque API now against d=3-only usage
  was the design doc's chief argument *against* doing the migration now (§6) — this phase
  **neutralizes** that by building/migrating only the d=3 material and explicitly *not* freezing
  the general-`d` API. Phase 23's design recon decides the general-`d` API shape; the general-`d`
  build (the "part 2" of this refactor) lands with or after it. This is the user's reordering of
  the design doc's three-way call (2026-06-16).
- **Leave the ~10 §38 carrier-whnf workarounds in place** (TACTICS-QUIRKS §38: `set`/`clear_value`,
  abstract-basis helpers, consumer-routing the final `∃`-witness, the `T`-bundle). Opacity renders
  many *unnecessary* but harmless; **removing** them is where much of the clarity payoff lives but
  is additional needs-thought work (design doc OQ2) — a deferred sub-fork, **out of scope for 22l**
  unless a layer's migration forces a specific one's removal.

## Layer plan (structural-edit; this is the to-do list)

Build order = the import spine. Each layer opens with an **opacity probe** (local `abbrev`→opaque
flip + the 3 named instances in `RigidityMatrix.lean`, scoped `lake build` of that layer's module,
then revert) — established at L2 as the only pre-FLIP signal for opacity-readiness; green-on-`abbrev`
alone is blind to it (L1 shipped three uncaught `PanelLayer.lean` breaks). The probe drives the
reach-in recon (mechanical-vs-needs-thought split per the design doc's category map (a)–(e)); the
layer ends with the file building green **on the `abbrev`** after the probe-surfaced gaps are
pre-migrated. The opening commit does **not** enumerate all ~150–200 sites — it pins the spine + the
hard-part concentrations + the exit criterion. The four recurring gap classes the probe catches
(`.val`-smul/add/zero simp lemmas, `change`-expose, `noncomputable` propagation, `equivExteriorPower`
LI-transport) are catalogued in `notes/ScrewSpaceCarrier-design.md` §5 *L2 refinement*.

- [x] **L0a — `RigidityMatrix.lean`: the carrier API foundation (project-green).** `ScrewSpace.mk`/
  `.val`/`val_mk`/`val_mem`/`mk_val`/`val_injective`/`@[ext]` + `equivExteriorPower` (+ `_apply`/
  `_symm_apply`), all on the still-`abbrev` carrier; migrated this file's two genuine
  `ScrewSpace`-constructor sites (`span_omitTwoExtensor_eq_top`, `ofHinge`) onto `mk`. **Done
  2026-06-16** — whole project builds + lints clean.
- [x] **L0b — `RigidityMatrix.lean`: remaining-idiom migration.** Migrated the file's two
  `(C : ExteriorAlgebra)` carrier-coercion idioms over a `ScrewSpace`-typed `C` onto `.val`:
  `ExtensorInPanel`'s defining equation and `ofHinge_supportExtensor_coe`→`_val`. (The
  `Module.Dual`-ext lemmas — `dualMap_eq_comp_single_proj_of_vanish_off`, `comp_columnOp_comp_single`,
  `columnOp`, … — are category (c): they operate at the `α → ScrewSpace k` *module* level via
  `LinearMap.ext`/`single`/`proj`, opacity-neutral, no carrier reach-in, so no migration needed.) The
  `complementIso`-input anonymous constructors (`⟨extensor …, extensor_mem_exteriorPower _⟩ :
  ⋀[ℝ]^2 …`) are NOT `ScrewSpace`-typed and stay. **Done 2026-06-16** — whole project builds + lints
  clean.
- [x] **FLIP (last) — `abbrev ScrewSpace`→opaque `def` + `ScrewSpace_def` bridge + 3 `inferInstanceAs`
  instances + the `cast`-form `equivExteriorPower` (recipe pinned at L7, design doc §5 *L7 refinement*;
  the RigidityMatrix part exercised live during the L9 probe).** Single mechanical commit; **phase exit +
  OQ1 resolution.** Caps banked: `case_II_realization_all_k` 600000→default; `case_cut_edge_realization`
  400000→default; `case_cut_edge_realization_gp` 600000→**400000** (partial — not droppable to default).
  `screwSpace_finrank` `change`-expose re-tested + kept. **Done 2026-06-16** — whole project builds + lints
  clean on the opaque carrier. (Was "L0, first" in the original plan — see *Architectural choices*.)
- [x] **L1 — `PanelLayer.lean`.** `screwBasis` `abbrev`→`def` (`.map (equivExteriorPower k).symm`)
  + `rfl` bridge `screwBasis_repr_apply`; `annihRow` + `@[simp]` family ported verbatim
  (opacity-neutral); five construction reach-ins `⟨extensor …⟩`→`mk` / coercion→`.val`; forced
  `Theorem55.lean` consumer fixups (3× `set … := ⟨extensor …⟩`→`mk`). **Hard-part (d) confirmed
  mechanical (OQ3 held).** **Done 2026-06-16** — whole project builds + lints clean.
- [x] **L2 — `Pinning.lean`.** Probe confirmed `Pinning.lean` **migration-free** (all reach-ins
  opacity-neutral). Closed three probe-surfaced L0/L1 gaps on the `abbrev`: carrier `val_smul`/
  `val_add`/`val_zero` API + the `exists_extensor_eq_panelSupportExtensor` re-route; the
  `screwSpace_finrank` `change`-expose; `noncomputable` on 5 carrier-valued defs; the
  `exists_linearIndependent_extensor_pair_perp` LI-transport via `equivExteriorPower`. **Done
  2026-06-16** — whole project builds + lints clean.
- [x] **L3 — `PanelHinge.lean`.** Probe confirmed **migration-free** (like `Pinning.lean`): the
  realization predicates `HasPanelRealization` / `HasGenericFullRankRealization` and the
  `PanelHingeFramework` API embed `ScrewSpace` only *structurally* (through
  `supportExtensor`/`panelSupportExtensor`-valued fields, abstractly consumed) — no carrier reach-in.
  Its `ScrewSpace`-touching sites are all opacity-neutral: type ascription (`{S : α → ScrewSpace k}`),
  module-level `Submodule.span ℝ {…}` membership, and `Function.update P.normal …` over the plain
  `α → Fin (k+2) → ℝ` normals (not carrier-valued). Probe surfaced **zero** new gaps in the
  already-migrated lower layers. **Done 2026-06-16** — whole project builds + lints clean (docs-only commit).
- [x] **L4 — `GenericityDevice.lean`.** Probe broke at exactly 2 sites (the M4 forgetful map
  `hasPanelRealization_of_generic`'s L0b coercion idiom `(C : ExteriorAlgebra ℝ _) = extensor p` via
  `congr_arg Subtype.val …` → `(C).val = … / congr_arg ScrewSpace.val …`). **OQ3 held at d=3**: the 5×
  `change … (Pi.single a (screwBasis k t)) = …` basis blocks survived *verbatim* on the opaque carrier
  (category (d) needed zero edits), as did the module-level `Module.Dual`/`Submodule.span` work (category
  (c), opacity-neutral). **Done 2026-06-16** — whole project builds + lints clean.
- [x] **L5 — `Coupling.lean`.** Probe confirmed **migration-free** (third negative outcome, like
  `Pinning.lean`/`PanelHinge.lean`): all reach-ins opacity-neutral module-level work — `α → ScrewSpace k`
  type ascriptions, `Module.Dual ℝ (ScrewSpace k)` row functionals, and the `extProj` column projection
  (`LinearMap.pi`/`proj`/`comp`). No category (a)/(d) site. Probe surfaced zero new gaps in lower layers.
  **Done 2026-06-16** — whole spine-to-Coupling builds clean on the opaque carrier; docs-only commit.
- [x] **L6 — `CaseI.lean`.** Probe confirmed **migration-free** (fourth negative outcome, like
  `Pinning.lean`/`PanelHinge.lean`/`Coupling.lean`): all reach-ins opacity-neutral — a
  `Module.Dual ℝ (ScrewSpace k)` / `ScrewSpace k` type ascription (b), module-level
  `Module.Dual`/`extProj`/`Pi.basis`-of-`screwBasis` coupling (c)/(e), and one opacity-neutral
  `change … (Pi.single a (screwBasis k t')) = …` block (d, per L4 OQ3). No category (a)/(b)-coercion
  carrier-construction site. Probe surfaced zero new gaps in lower layers. **Done 2026-06-16** — whole
  spine-to-CaseI builds clean on the opaque carrier; docs-only commit.
- [x] **L7 — `CaseII.lean`** — holds `case_II_realization_all_k` (`maxHeartbeats 600000`). Probe
  confirmed **migration-free** (fifth negative outcome, like the other assembly files), and gave the
  **first OQ1 cap-drop measurement**: on the opaque carrier `case_II_realization_all_k` re-elaborated
  green at the default `200000` (vs. the committed 3× `600000`). The probe also pinned down the FLIP's
  `equivExteriorPower` opaque-head form (design doc §5 *L7 refinement*). **Done 2026-06-16** — whole
  project builds + lints clean (docs-only commit).
- [x] **L8 — `CaseIII.lean`** — the Case-III geometry/construction layer, first non-assembly file since
  L4. Probe confirmed **migration-free** (sixth negative outcome): the ~113 `ScrewSpace` mentions are all
  opacity-neutral — `Module.Dual ℝ (α → ScrewSpace k)` row functionals + `Submodule.span`/`⊔`
  membership (b)/(c)/(e), `LinearMap.single`/`proj`/`id` and `Function.update (0 : α → ScrewSpace k) v x`
  module-level maps over carrier-typed values, and `ScrewSpace k`/`Module.Dual ℝ (ScrewSpace k)` type
  ascriptions (b). No category (a) `⟨v,h⟩`-construction, (d) `screwBasis`-coordinate, or
  carrier-`.val`/`congr_arg Subtype.val` site — the Case-III geometry consumes carriers abstractly, with
  the constructing sites all in the lower layers. **Done 2026-06-16** — whole spine-to-CaseIII builds
  clean on the opaque carrier; docs-only commit.
- [x] **L9 — `Theorem55.lean`** — holds `case_cut_edge_realization` (400000) +
  `case_cut_edge_realization_gp` (600000). Probe confirmed **migration-free** (seventh, last
  negative outcome): its `ScrewSpace.mk` construction sites are already migrated (L1 consumer
  fixups) and the rest are opacity-neutral (`Module.Dual` row functionals, `Function.update`
  module-level maps, `supportExtensor`/`.choose`-built `extF`, type ascriptions). **Both caps
  measured probe-live on the opaque carrier:** `case_cut_edge_realization` drops to the **default
  200000** (committed 400000); `case_cut_edge_realization_gp` drops to **400000** (committed 600000)
  — partial, not all the way to default. Banked at the FLIP. **Done 2026-06-16** — whole project
  builds + lints clean on the `abbrev` (docs-only commit).

## Blockers / open questions

- **OQ1 — RESOLVED at the FLIP (positive, partial on one cap).** The end-to-end cap drop the spike could
  only proxy is now banked: `case_II_realization_all_k` 600000→default, `case_cut_edge_realization`
  400000→default, `case_cut_edge_realization_gp` 600000→400000 (one step, not droppable to default — the
  cap is partly intrinsic to its GP seed + per-side rank-polynomial case analysis, not solely
  carrier-whnf). Molecular `maxHeartbeats` count 3→1.
- **OQ2 (deferred sub-fork) — remove the §38 workarounds, or leave them?** Default: left (see
  *Architectural choices*). The opaque carrier renders many of the ~10 §38 carrier-whnf workarounds
  *unnecessary* but harmless; removing them is where much of the clarity payoff lives but is unbudgeted
  needs-thought work — a follow-up cleanup, out of 22l scope.
- **Blueprint untouched (confirmed).** The carrier flip is implementation-only; no blueprint-pinned decl's
  statement or type changed (`screwSpace_finrank`, `screwBasis`, `ExtensorInPanel`, etc. all stable). No
  `\lean{...}` restate needed; `blueprint/src/` not edited this phase.

## Hand-off / next phase

**Phase 22l is closed.** The math frontier (`notes/MolecularConjecture.md`) is **unchanged** by this
phase: the next phase is **Phase 23 — Case III general `d`, KT Lemma 6.13** (entirely unbuilt). 22l was
a pure implementation refactor (no math, no blueprint change).

**What 22l unlocks (but does not start): the general-`d` "part 2" carrier migration.** The opaque
`ScrewSpace` API is frozen only against the *d=3* usage surface; the general-`d` API shape is deferred to
the **Phase-23 design boundary** (once the general-`k` reach-in surface is known). The part-2 build lands
with or after Phase 23. Concretely, Phase 23's design recon decides whether the d=3 opaque API extends
unchanged to general `k` or needs reshaping (the `screwBasis`/`annihRow` coordinate machinery gets
exercised symbolically for the first time at general `k` — design doc §6).

**L2–L9 calibration of the per-layer method** (kept as the durable lesson). Green-on-`abbrev` is **blind
to opacity-readiness**, so each layer ran an opacity probe up front (L1 skipped it and left three
`PanelLayer.lean` breaks the probe later caught). The probe's *negative* outcome — a layer that builds
clean on the opaque carrier needs **no migration** — held for 7 of 10 spine files: a file that only
*consumes* `ScrewSpace`-typed values abstractly (type ascription, module-level span / `Module.Dual` row
functionals, `LinearMap.pi`/`proj`/`comp` column maps, predicates embedding the carrier through framework
fields, and `ScrewSpace.mk`-already-migrated construction sites) cracks none open. The recurring migration
idiom (L0b/L4): route `(C : ExteriorAlgebra ℝ _)` coercions and `congr_arg Subtype.val` onto `.val` /
`congr_arg ScrewSpace.val`; a trailing `rfl`-close after moving `(⟨v,h⟩ : ScrewSpace).val` onto `mk`/`val`
may need an explicit `ScrewSpace.val_mk` (the `def`s are semireducible). OQ3 held operationally at d=3: the
category-(d) `change … (screwBasis k t) …` basis blocks survive verbatim on the opaque carrier (zero
edits). The four recurring gap classes are catalogued in `notes/ScrewSpaceCarrier-design.md` §5.

## Decisions made during this phase

### Phase-local choices and proof techniques

- **FLIP + phase close (2026-06-16, opus).** Flipped `abbrev ScrewSpace` → opaque `def` in
  `RigidityMatrix.lean` + `ScrewSpace_def := rfl` bridge + 3 `noncomputable inferInstanceAs` instances;
  `mk`/`val`/`val_mem` route their Subtype coercion through `ScrewSpace_def k ▸ …`; `equivExteriorPower`
  became the `cast (ScrewSpace_def k)` `≃ₗ` (`map_add'`/`map_smul'` `rfl`, `simp [ScrewSpace_def]` for
  the inverse laws) with `cast`-RHS `_apply`/`_symm_apply`. Whole d=3 spine builds + lints clean on the
  opaque carrier in one mechanical commit — exactly as the L9 probe predicted (it had exercised this
  RigidityMatrix recipe live). OQ1 banked: CaseII + `case_cut_edge_realization` caps dropped to default,
  `_gp` 600000→400000 (molecular `maxHeartbeats` 3→1). The `screwSpace_finrank` `change`-expose was
  re-tested and **kept** (no unused-warning; still needed — opaque head doesn't reduce to the graded-piece
  head at `rw`'s reducible transparency). Blueprint untouched; no friction surfaced (the flip behaved
  exactly as the design recon + L7/L9 probes predicted).

- **Phase-open (2026-06-16, opus).** Opened 22l as the d=3-scoped first part of the
  carrier-opacity refactor, per the user's reordering of the design doc's three-way now-vs-later
  call (`notes/ScrewSpaceCarrier-design.md` §6): do the d=3 API + migration now (banks the perf
  win + resolves OQ1 by greening the cap-holding spine end-to-end), defer the general-`d` API to
  the Phase-23 design boundary (neutralizes the doc's chief objection — freezing an API against
  d=3-only usage — by *not* freezing the general-`d` surface). Confirmed the import spine is
  linear (RigidityMatrix → … → Theorem55) and matches the design doc §5 corrected spine; laid the
  L0–L9 Layer plan along it. Docs-only opening commit; no Lean/blueprint touched. Updated the
  design doc Status header + §6 to record the decision.

- **L0a + plan reorder to API-first / flip-last (2026-06-16, opus).** Landed the carrier API
  (`ScrewSpace.mk`/`.val`/`val_mk`/`val_mem`/`mk_val`/`val_injective`/`@[ext]` +
  `equivExteriorPower`) in `RigidityMatrix.lean` and migrated its two genuine
  `ScrewSpace`-anonymous-constructor sites onto `mk`. **Reordered the plan**: the original
  "flip-the-`abbrev`-to-`def`-first, migrate bottom-up" order cannot keep the project green —
  opacity blocks the `⟨val,proof⟩` idiom at ~300 sites across 7 files *simultaneously*, so a
  flip-first commit reds the whole downstream chain (CI fail / broken handoff). Corrected order:
  API on the still-`abbrev` carrier (additive, project-green) → per-file reach-in migration onto the
  API (each commit green, abbrev keeps `mk`/`val` defeq) → flip last. The API only types cleanly
  with `.val` written as `Subtype.val (C : …)` (dot-notation `C.val` recurses into the decl on the
  abbrev). The LI-through-the-carrier transport now routes through
  `equivExteriorPower` (`ker (subtype.comp equiv) = ⊥` via `ker_comp`/`comap_bot`/`LinearEquiv.ker`)
  — the forward-compatible idiom later layers reuse.

- **L0b — `RigidityMatrix.lean` carrier-coercion migration (2026-06-16, opus).** Migrated the
  file's two `(C : ExteriorAlgebra …)` carrier-coercion idioms over a `ScrewSpace`-typed `C` onto
  `.val`: `ExtensorInPanel`'s defining equation and `ofHinge_supportExtensor_coe` (renamed
  `_val`, no external consumers). Found these are the file's *only* such reach-ins; the file's
  `Module.Dual`-ext lemmas (`dualMap_eq_comp_single_proj_of_vanish_off`, `comp_columnOp_comp_single`,
  `columnOp`) are category (c) — `α → ScrewSpace k` *module*-level `LinearMap.ext`/`single`/`proj`,
  opacity-neutral, no migration. Project-green because `.val` is defeq to the old coercion while the
  carrier is `abbrev`, so all downstream `ExtensorInPanel` witnesses (`⟨p, rfl, …⟩` at Theorem55,
  the `exists_extensor_eq_panelSupportExtensor`-fed pair at PanelLayer:621) typecheck unchanged.
  `ExtensorInPanel`'s blueprint pin survives (implementation-only change). No friction surfaced —
  the planned mechanical swap behaved exactly as the design recon predicted.

- **L1 — `PanelLayer.lean` migration (2026-06-16, opus).** Flipped `screwBasis` from a reducible
  `abbrev` (`(Pi.basisFun …).exteriorPower k`, accepted as a basis *of* `ScrewSpace k` only by
  reducible defeq) to a `def` transporting it through the boundary `≃ₗ`
  (`.map (equivExteriorPower k).symm`) — the §5-drafted shape. OQ3 held: the transport is defeq-free,
  so a single `rfl` bridge `screwBasis_repr_apply` ((`screwBasis k).repr = (direct exterior
  basis).repr`) reconciles the two coordinate vocabularies — `panelSupportPoly`/`panelSupportPoly_eval`
  stay stated in the *direct* exterior basis (they precede `screwBasis` in the file), while
  `annihRow`/`annihRowPoly_eval` use `screwBasis`; the bridge closes the one mixed proof
  (`annihRowPoly_eval`). `annihRow` + its `@[simp]` family (`annihRow_apply`, `_self`, `_add`,
  `_smul`, `span_…`) are abstract `Module.Basis` API — opacity-neutral, ported verbatim. Five
  construction reach-ins → `mk`/`.val`; the `complementIso`-input `⟨extensor …⟩ : ⋀[ℝ]^2` constructors
  stay. Forced consumer fixups in `Theorem55.lean` (producer statement changed): 3× `set … :=
  ⟨extensor …⟩`→`ScrewSpace.mk`. Migration idiom (recurs L2+): a `(⟨v,h⟩ : ScrewSpace).val` migrated
  to `mk`/`val` may need an explicit `ScrewSpace.val_mk` to close a trailing `rfl`-step, since
  `mk`/`val` are semireducible `def`s (unlike the reducible `Subtype` ops `rw`'s auto-`rfl` unfolds).

- **L2 — `Pinning.lean` (no migration) + the opacity-probe method + three L0/L1 gap closures
  (2026-06-16, opus).** Introduced the **opacity probe** (local `abbrev`→opaque flip + 3
  `inferInstanceAs` instances, scoped `lake build` of the layer module, revert) as the standing
  per-layer opening step — the only pre-FLIP signal for opacity-readiness, since green-on-`abbrev` is
  blind to it (L1 had skipped it). The probe confirmed `Pinning.lean` is **migration-free** (every
  `ScrewSpace` reach-in opacity-neutral: type ascriptions, `annihRow`/abstract-basis API,
  `inferInstance`→named instance, `iInfKerProjEquiv`/`single`/`proj` module-level), and surfaced three
  gaps in the already-"migrated" L0/L1 files — all pre-migrated on the `abbrev` this commit:
  (1) added `@[simp] ScrewSpace.{val_smul,val_add,val_zero}` (`:= rfl`) and re-routed
  `exists_extensor_eq_panelSupportExtensor` off the opacity-dead `simp [ScrewSpace.val,
  Submodule.coe_smul]`; (2) `change`-exposed `screwSpace_finrank`'s carrier head (`change`, not `show`
  — style linter); (3) `noncomputable`-tagged 5 carrier-valued `Submodule`/`Dual`/`≃ₗ` defs (the named
  instances are `noncomputable`); (4) composed `exists_linearIndependent_extensor_pair_perp`'s
  LI-transport with `equivExteriorPower`. Gap classes + method recorded in
  `notes/ScrewSpaceCarrier-design.md` §5 *L2 refinement* (canonical) + the *Layer plan* preamble.

- **L3 — `PanelHinge.lean` (no migration) (2026-06-16, opus).** The opacity probe built the whole
  spine-to-PanelHinge green on the *opaque* carrier (zero errors/warnings), confirming the file is
  **migration-free** — the second negative-probe outcome after L2's `Pinning.lean`. Its `ScrewSpace`
  reach-ins are all opacity-neutral: a type ascription (`{S : α → ScrewSpace k}` in Case-II `hnew`),
  module-level `Submodule.span ℝ {…}` over `supportExtensor`-valued sets (category (c)), and
  `Function.update P.normal v n` — `withNormal` overrides a *normal* (`α → Fin (k+2) → ℝ`), not a
  carrier value. The realization predicates that *structurally embed* the carrier
  (`HasPanelRealization`/`HasGenericFullRankRealization`/`HasFullRankRealization`) quantify a
  `BodyHingeFramework` + normal assignment and read its `ScrewSpace`-typed fields abstractly — never
  constructing or coordinate-accessing one — so the structural embedding is opacity-neutral too.
  Docs-only commit; no Lean/blueprint touched. The recon's predicted-mechanical Shape-2 estimate
  holds: PanelHinge had no category (a)/(d)/(e) reach-in despite *defining* the predicates that thread
  the carrier through the whole import chain.

- **L5 — `Coupling.lean` (no migration) (2026-06-16, opus).** The opacity probe built the whole
  spine-to-Coupling green on the *opaque* carrier (zero errors/warnings) — the **third** negative-probe
  outcome after L2 `Pinning.lean` / L3 `PanelHinge.lean`. `Coupling.lean`'s `ScrewSpace` reach-ins are all
  opacity-neutral module-level work: `(α → ScrewSpace k)` type ascriptions, `Module.Dual ℝ (ScrewSpace k)`
  row functionals (`hingeRow_comp_extProj_eq_zero`, `hingeRow_collapseTo_comp_extProj_eq`), and the
  block-triangular column projection `extProj` (`LinearMap.pi`/`LinearMap.proj`/`LinearMap.comp`,
  categories (b)/(c)/(e)). No category (a) `⟨v,h⟩`-construction or (d) `screwBasis`-coordinate site — the
  two `ScrewSpace.mk`/`equivExteriorPower` uses in `span_omitTwoExtensor_eq_top` live in
  `RigidityMatrix.lean` (L0a/L0b). Probe surfaced zero new gaps in the migrated lower layers. Docs-only
  commit; no Lean/blueprint touched. Calibrates the design doc §3 prediction that the column/dual coupling
  layer, like the predicate-defining `PanelHinge.lean`, threads the carrier without cracking it open.

- **L7 — `CaseII.lean` (no migration; OQ1 cap-drop first measured; FLIP-`equivExteriorPower` pinned)
  (2026-06-16, opus).** The opacity probe built the whole spine-to-CaseII green on the *opaque* carrier
  (zero errors/warnings) — the **fifth** negative-probe outcome (assembly file, like CaseI). All
  reach-ins opacity-neutral; no category (a)/(b)-coercion carrier construction. **OQ1 first measurable
  signal:** with the probe flip live, `case_II_realization_all_k` re-elaborated green at the **default
  `maxHeartbeats 200000`** (committed `abbrev` carries a 3× `600000` override) — the opacity cap drop is
  real, banked only at the FLIP. The probe also pinned the design doc §5 `…`-left FLIP piece:
  `equivExteriorPower` cannot stay `LinearEquiv.refl` on the opaque head (`_apply`/`_symm_apply` lose
  `rfl`); it becomes a `cast (ScrewSpace_def k)` `≃ₗ` with `cast`-form apply lemmas (and `mk`/`val`/
  `val_mem` route their coercion through `ScrewSpace_def k ▸ …`). With that fix `RigidityMatrix.lean` and
  the whole spine build clean. Docs-only commit; no Lean/blueprint touched (probe reverted). Design doc
  §5 *L7 refinement* carries the FLIP recipe.

- **L8 — `CaseIII.lean` (no migration) (2026-06-16, opus).** The opacity probe built the whole
  spine-to-CaseIII green on the *opaque* carrier (zero errors/warnings) — the **sixth** negative-probe
  outcome, and the **first non-assembly file since L4 `GenericityDevice.lean`** to confirm it (the
  Case-III geometric-construction layer). All ~113 `ScrewSpace` reach-ins opacity-neutral: `Module.Dual ℝ
  (α → ScrewSpace k)` row functionals + `Submodule.span`/`⊔` membership (b)/(c)/(e),
  `LinearMap.single`/`proj`/`id` and `Function.update (0 : α → ScrewSpace k) v x` module-level maps over
  carrier-typed values, and `ScrewSpace k`/`Module.Dual ℝ (ScrewSpace k)` type ascriptions (b). **No
  category (a) `⟨v,h⟩`-construction, (d) `screwBasis`-coordinate, or carrier-`.val`/`congr_arg
  Subtype.val` site** — the carrier-constructing sites all live in the lower layers (RigidityMatrix
  L0a/L0b, PanelLayer L1). Probe surfaced zero new gaps in the migrated lower layers. Docs-only commit; no
  Lean/blueprint touched (probe reverted).

- **L9 — `Theorem55.lean` (no migration; both Theorem55 caps measured; OQ1 fully resolved) (2026-06-16,
  opus).** The opacity probe built the whole spine-to-Theorem55 green on the *opaque* carrier (zero
  errors/warnings) — the **seventh and final** negative-probe outcome, despite `Theorem55.lean` holding
  the two surviving caps and the L1 forced `ScrewSpace.mk` consumer fixups. Those `mk` construction sites
  (lines 65/66/189/1802/1803) are already migrated; every other carrier touch is opacity-neutral —
  `Module.Dual ℝ (α → ScrewSpace 2)` row functionals, `Function.update (0 : α → ScrewSpace 2) v x`
  module-level maps, `set extF : β → ScrewSpace 2 := fun e => …` built from `supportExtensor`/`.choose`
  carrier accessors (no bare `⟨v,h⟩`), and `: ScrewSpace 2` type ascriptions; no category (a)/(d)/(b)-
  coercion or `congr_arg Subtype.val` site. **OQ1 cap-drop measured probe-live (banked at the FLIP):**
  with the two caps temporarily lowered and the flip live, `case_cut_edge_realization` re-elaborated
  green at the **default 200000** (committed 400000 — full drop), and `case_cut_edge_realization_gp` at
  **400000** (committed 600000 — drops one step but still times out at 200000, so it stays at 400000 in
  the FLIP). With CaseII's L7 drop-to-default, OQ1 is now fully measured: 2/3 caps to default, the third
  −33%. Docs-only commit; no Lean/blueprint touched (probe reverted).

- **L6 — `CaseI.lean` (no migration) (2026-06-16, opus).** The opacity probe built the whole
  spine-to-CaseI green on the *opaque* carrier (zero errors/warnings) — the **fourth** negative-probe
  outcome after L2 `Pinning.lean` / L3 `PanelHinge.lean` / L5 `Coupling.lean`, and the first *assembly*
  file to confirm the design doc §3 prediction that the Case-I/II/Theorem55 assembly layer carries ~0
  break-prone constructs. `CaseI.lean`'s `ScrewSpace` reach-ins are all opacity-neutral: a
  `{r : Module.Dual ℝ (ScrewSpace k)} {C : ScrewSpace k}` type ascription (category (b)), module-level
  `Module.Dual`/`extProj`/`Pi.basis`-of-`screwBasis` coupling work (categories (c)/(e)), and one
  `change … (Pi.single a (screwBasis k t')) = …` category-(d) block that built verbatim on the opaque
  carrier (per L4's OQ3 confirmation at d=3). No category (a) `⟨v,h⟩`-construction or (b)-coercion
  carrier-construction site — the carrier-constructing sites all live in the lower layers
  (RigidityMatrix L0a/L0b, PanelLayer L1). Probe surfaced zero new gaps in the migrated lower layers.
  Docs-only commit; no Lean/blueprint touched.

- **L4 — `GenericityDevice.lean` (2-site migration; OQ3 confirmed operationally) (2026-06-16, opus).**
  The opacity probe broke at *exactly two* sites, both the L0b carrier-coercion idiom in the M4
  forgetful map `hasPanelRealization_of_generic`'s proof body: `hval : (Q.toBodyHinge.supportExtensor e
  : ExteriorAlgebra ℝ _) = extensor p := congr_arg Subtype.val hsupp ▸ hp`. Migrated each to
  `(…).val = extensor p / congr_arg ScrewSpace.val hsupp ▸ hp` — the `ExtensorInPanel` witness's first
  conjunct is `C.val = extensor p`, so `.val` is the right projection and `hsupp` (a `ScrewSpace 2`
  equation) is mapped through `ScrewSpace.val` rather than `Subtype.val`. **OQ3 confirmed at d=3 (the
  headline):** the 5× `change … (Pi.single a (screwBasis k t)) = …` basis blocks — the recon's
  feared-hardest category (d) — built *verbatim* on the opaque carrier (default-transparency defeq
  holds), needing zero edits; the file's `Module.Dual`/`Submodule.span` work (category (c)) is
  opacity-neutral. Implementation-only (proof body); no statement, consumer, or blueprint pin changed.
