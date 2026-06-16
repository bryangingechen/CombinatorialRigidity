# Phase 22l — ScrewSpace carrier opacity, part 1: the d=3 API + migration (work log)

**Status:** in progress (opened 2026-06-16).

Structural-edit phase (no new math, no new blueprint chapter): reshape the `ScrewSpace`
carrier from a reducible `abbrev` into an **opaque `def`** with a `mk`/`val`/`≃ₗ` API, then
migrate the existing `d = 3` tree onto it file-by-file along the import spine. The motivation,
the opacity spike, mathlib precedents, the drafted API surface, the per-file recon, and the
now-vs-later analysis are **canonical in `notes/ScrewSpaceCarrier-design.md`** — this note points
there (the API spec is §5; the spike §3; the spine §5; the residual risks OQ1–OQ3) and does
**not** duplicate it. The to-do list lives in the *Layer plan* below (`CLAUDE.md`
*Structural-edit phases*).

## Current state

**Next concrete step: L7 — `CaseII.lean`.** L6 closed: the opacity probe on `CaseI.lean` built the whole
spine-to-CaseI **green with zero errors/warnings** on the opaque carrier — `CaseI.lean` is
**migration-free** (the fourth negative-probe outcome after L2 `Pinning.lean` / L3 `PanelHinge.lean` /
L5 `Coupling.lean`), exactly as the design doc §3 predicted for an *assembly* file. Its `ScrewSpace`
reach-ins are all opacity-neutral: a `{r : Module.Dual ℝ (ScrewSpace k)} {C : ScrewSpace k}` type
ascription (category (b)), `Module.Dual`/`extProj`/`Pi.basis`-of-`screwBasis` module-level coupling work
(categories (c)/(e)), and the one `change … (Pi.single a (screwBasis k t')) = …` category-(d) block
(opacity-neutral at d=3, per L4's OQ3 confirmation). No category (a) `⟨v,h⟩`-construction or
`(C : ExteriorAlgebra)`-coercion site in the file — the carrier-constructing sites all live in the lower
layers (RigidityMatrix L0a/L0b, PanelLayer L1). Probe surfaced **zero** new gaps in the migrated lower
layers. Each commit keeps the project green (carrier still `abbrev`); the **FLIP lands LAST**.

**L6 landed (2026-06-16): `CaseI.lean` verified migration-free, project green (docs-only).** Opacity
probe (local flip + 3 named instances → scoped `lake build` of the CaseI module rebuilds the full
spine-to-CaseI → revert) built **green with zero errors/warnings** on the opaque carrier — the fourth
negative-probe outcome. The Case-I realization *assembly* file only consumes the carrier abstractly; no
break-prone construct, matching the design doc §3 assembly-file prediction.

**L5 landed (2026-06-16): `Coupling.lean` verified migration-free, project green (docs-only).** Opacity
probe (local flip + 3 named instances → scoped `lake build` of the Coupling module → revert) built clean.

**L4 landed (2026-06-16): `GenericityDevice.lean` migrated (2 sites), project green.** The opacity
probe broke at exactly two sites — both the L0b coercion idiom in the M4 forgetful map
`hasPanelRealization_of_generic`: `(Q.toBodyHinge.supportExtensor e : ExteriorAlgebra ℝ _) = extensor p`
proved via `congr_arg Subtype.val hsupp ▸ hp`. Migrated each to `(…).val = extensor p` /
`congr_arg ScrewSpace.val hsupp ▸ hp` (the `ExtensorInPanel` witness's first conjunct is `C.val =
extensor p`). **OQ3 held at d=3:** the 5× `change … (Pi.single a (screwBasis k t)) = …` basis blocks and
all the module-level `Module.Dual`/`Submodule.span` work built clean on the opaque carrier, no edits.
Implementation-only (proof body of a forgetful map); no statement, no consumer, no blueprint pin changed.

**L3 landed (2026-06-16): `PanelHinge.lean` verified migration-free, project green (docs-only).** The
opacity probe (local flip + 3 named instances → scoped `lake build` of the PanelHinge module → revert)
built the whole spine-to-PanelHinge green on the *opaque* carrier with zero errors/warnings. The file's
`ScrewSpace` reach-ins are all opacity-neutral (design-doc categories (b)-type-ascription and (c)-span,
no (a)/(d)/(e)): `{S : α → ScrewSpace k}` type ascription (Case-II `hnew`), `Submodule.span ℝ {…}`
membership over `supportExtensor`-valued sets (module-level), and `Function.update P.normal v n` over
the plain `α → Fin (k+2) → ℝ` normals — `withNormal` updates a *normal*, not a `ScrewSpace`. The
realization predicates that *structurally embed* the carrier (`HasPanelRealization`,
`HasGenericFullRankRealization`, `HasFullRankRealization`) quantify a `BodyHingeFramework`/normal
assignment and read its `ScrewSpace`-typed fields abstractly, never constructing or coordinate-accessing
a carrier value. No new gaps surfaced in the migrated lower layers (RigidityMatrix/PanelLayer/Pinning).
No blueprint pin changed.

**L2 landed (2026-06-16): `Pinning.lean` verified migration-free + three L0/L1 opacity gaps closed,
project green.** The probe-surfaced gaps (canonical in `notes/ScrewSpaceCarrier-design.md` §5 *L2
refinement*): (1) carrier API gained `@[simp] ScrewSpace.val_smul`/`val_add`/`val_zero` (`:= rfl`) so
the `.val`-through-smul idiom survives opacity (`PanelLayer.exists_extensor_eq_panelSupportExtensor`
re-routed off the now-opacity-dead `simp [ScrewSpace.val, Submodule.coe_smul]`); (2) `screwSpace_finrank`
got a leading `change … ↥(⋀[ℝ]^k …) …` to expose the graded-piece head for `exteriorPower.finrank_eq`;
(3) `noncomputable` propagated onto the carrier-valued `Submodule`/`Dual`/`≃ₗ` defs (`hingeRowBlock`,
`screwDiff`, `hingeRow`, `columnOp`, `partitionMotions`) since the named instances are `noncomputable`;
plus `PanelLayer.exists_linearIndependent_extensor_pair_perp`'s LI-transport composed with
`equivExteriorPower` (the L0a idiom). No blueprint pin changed.

**L1 landed (2026-06-16): `PanelLayer.lean` migrated, project green.** `screwBasis` flipped from a
reducible `abbrev` to a `def` transporting the direct exterior basis through `equivExteriorPower`
(`.map (equivExteriorPower k).symm`); a `rfl` bridge `screwBasis_repr_apply` reconciles the
`panelSupportPoly` machinery (stated in the *direct* exterior basis) with the `annihRow`/`screwBasis`
machinery — used in `panelSupportPoly_eval`→`annihRowPoly_eval`. The `annihRow` + `@[simp]` family is
opacity-neutral (abstract `Module.Basis` API, no carrier reach-in) and ported verbatim. The five
construction reach-ins migrated `⟨extensor …⟩ : ScrewSpace 2`→`ScrewSpace.mk` and the
`exists_extensor_eq_panelSupportExtensor` coercion→`.val`; the `complementIso`-input `⟨extensor …⟩ :
⋀[ℝ]^2` anonymous constructors stay (not `ScrewSpace`-typed). **Forced consumer fixups in
`Theorem55.lean`** (L9 territory, but `exists_linearIndependent_extensor_pair_perp`'s statement
changed): the three `set Ce/Cf/C := ⟨extensor …⟩`→`ScrewSpace.mk` swaps at lines 65/66, 189,
1802/1803 (`simpa … hpq_li.ne_zero` matches the producer's new `mk`-form). No blueprint pin changed
(implementation-only; `screwBasis`/`annihRow` *types* stable).

**L0a + L0b landed (2026-06-16): the carrier API + `RigidityMatrix.lean` migration, project green.**
`ScrewSpace.mk` / `.val` / `val_mk` / `val_mem` / `mk_val` / `val_injective` / `@[ext]` +
`equivExteriorPower` (+ `_apply`/`_symm_apply` simp) on the still-`abbrev` carrier; this file's two
`ScrewSpace`-constructor sites onto `mk`, its two `(C : ExteriorAlgebra …)` coercion idioms
(`ExtensorInPanel`'s defining equation, `ofHinge_supportExtensor_coe`→`_val`) onto `.val`. The
`⋀[ℝ]^2`-Subtype anonymous constructors at `complementIso` inputs are NOT `ScrewSpace`-typed and stay.

The design recon (`notes/ScrewSpaceCarrier-design.md` §5) is complete and **killed the surgical
"localized wrapper" option** (Shape 1): the realization predicates the capped decls return *and*
consume structurally embed `ScrewSpace k`, so the opaque head cannot be localized to the assembly
files. The only coherent path is **Shape 2** (full opaque carrier, ~3–5 sessions). The
`screwBasis`-transport micro-spike (§5 OQ3) confirmed the transport is **defeq-free**, so the
recon's feared-hardest category (hard-part (d)) is essentially mechanical.

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
- [ ] **FLIP (last) — `abbrev ScrewSpace`→opaque `def` + 3 `inferInstanceAs` instances.** Lands
  after the whole spine has adopted the API; a single mechanical commit. **Phase exit + OQ1
  resolution.** (Was "L0, first" in the original plan — see *Architectural choices*.)
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
- [ ] **L7 — `CaseII.lean`** — holds `case_II_realization_all_k` (`maxHeartbeats 600000`). Confirm
  the cap drop here (part of OQ1).
- [ ] **L8 — `CaseIII.lean`** (Case-III geometry/construction reach-ins).
- [ ] **L9 — `Theorem55.lean`** — holds `case_cut_edge_realization` (400000) +
  `case_cut_edge_realization_gp` (600000). Last file to adopt the API; once it does, the **FLIP**
  step above lands. **Phase exit criterion:** the full d=3 spine builds on the opaque carrier *and*
  the three surviving `maxHeartbeats` overrides (`notes/ScrewSpaceCarrier-design.md` §1) are dropped
  or lowered toward default — the end-to-end cap drop that OQ1 could not confirm on synthetic
  benches.

## Blockers / open questions

- **OQ1 (the dominant residual risk) — cap drop unconfirmed until the spine is green.** The opacity
  spike got 5–60× on *synthetic* benches but could not reach a survivor; the three caps sit at the
  *top* of the spine (CaseII, Theorem55). This phase greens that exact spine, so **22l is the
  resolution of OQ1** — the cap audit at L7/L9 is the payoff measurement, not a separate task.
  Risk: if the cap drop fails to materialize, the migration still leaves a cleaner carrier but the
  perf justification weakens; reassess at L7 (first survivor reached).
- **OQ2 (deferred sub-fork) — remove the §38 workarounds, or leave them?** Default: leave (see
  *Architectural choices*). Revisit only if a layer forces a specific removal, or schedule as a
  follow-up cleanup.
- **Per-slice blueprint grep gate.** Statements of blueprint-pinned decls don't change (carrier
  flip is implementation-only; `screwSpace_finrank`, `screwBasis`'s *type* are stable). But if a
  layer changes a *pinned* decl's statement (e.g. if `screwBasis`'s signature shifts), grep
  `blueprint/src/` for that `\lean{...}` name and restate in the same commit (`CLAUDE.md`
  *Structural-edit phases*). Expectation: the blueprint is untouched by this phase.

## Hand-off / next phase

**Smallest next commit: L7 — `CaseII.lean`.** L0a/L0b/L1/L2/L3/L4/L5/L6 (RigidityMatrix, PanelLayer,
Pinning, PanelHinge, GenericityDevice, Coupling, CaseI) are now opacity-ready (L2/L3/L5/L6 were
migration-free; L0a/L0b/L1/L4 needed edits, L4 just the 2-site L0b idiom). L7 is the next file down the
spine — the Case-II (`k>0` splitting / Whiteley 1-extension) realization assembly, and the **first
capped-survivor layer**: it holds `case_II_realization_all_k` (`maxHeartbeats 600000`), so L7 is where
the OQ1 cap-drop audit first becomes measurable (re-elaborate on the opaque carrier and see whether the
cap can drop/lower toward default). **Open it with the opacity probe** (local flip + 3 instances →
`lake build CombinatorialRigidity.Molecular.AlgebraicInduction.CaseII` → revert); the probe drives the
recon and catches the four gap classes (design doc §5 *L2 refinement*). If it breaks, pre-migrate on the
`abbrev`: swap `⟨v,h⟩ : ScrewSpace k`→`ScrewSpace.mk v h` / `(C : ExteriorAlgebra)`→`C.val` /
`congr_arg Subtype.val …`→`congr_arg ScrewSpace.val …`, add `noncomputable` to any carrier-valued
`Submodule`/`Dual`/`≃ₗ` def, route `.val`-arithmetic through `val_smul`/`val_add`/`val_zero`, and
LI/`ker`-transport through `equivExteriorPower`. Each commit keeps the project green on the `abbrev`. The
API shape is fixed (L0a/L1/L2) — every later layer is the probe + mechanical pre-migration. Note CaseII
is an *assembly* file: the design doc §3 predicts assembly files (CaseI/II/Theorem55) carry ~0
break-prone constructs (L6 CaseI confirmed this — fourth negative probe), so it may well be another
negative probe — but the cap drop still cannot be banked until the FLIP lands at end-of-spine.

**L2/L3/L4/L5/L6 calibration of the per-layer method.** The lesson is the *method*, not a site count:
green-on-`abbrev` is **blind to opacity-readiness**, so each remaining layer must run the opacity
probe up front (L1 had skipped it and left three `PanelLayer.lean` breaks the probe then caught). The
four recurring gap classes are catalogued (design doc §5). The probe also has a *negative* outcome —
a layer that builds clean on the opaque carrier needs **no migration** (L2 `Pinning.lean`, L3
`PanelHinge.lean`, L5 `Coupling.lean`, L6 `CaseI.lean`): a file that only *consumes* `ScrewSpace`-typed
values abstractly
(type ascription, module-level span/`Module.Dual` row functionals, `LinearMap.pi`/`proj`/`comp` column
maps, predicates embedding the carrier through framework fields) reaches into the carrier nowhere and is
opacity-neutral. The L0b/L4 idiom that recurs in files that *do* migrate: route
`(C : ExteriorAlgebra ℝ _)` coercions and `congr_arg Subtype.val` onto `C.val` / `congr_arg
ScrewSpace.val` (the `.val` projection); and after moving a `(⟨v,h⟩ : ScrewSpace).val` onto `mk`/`val`,
a trailing `rfl`-close may need an explicit `ScrewSpace.val_mk` rewrite (`mk`/`val` are semireducible
`def`s, so `rw`'s auto-`rfl` does not unfold them). L4 also confirmed OQ3 *operationally* at d=3: the
`change … (screwBasis k t) …` category-(d) blocks survive verbatim, so the recon's feared-hardest
category needs no edits in the existing tree. The `abbrev`→opaque-`def` **FLIP lands last**, after the
whole spine adopts the API, as a single small commit that banks the perf win and resolves OQ1.

**At phase close:** the d=3 tree builds on the opaque `ScrewSpace` carrier; the three
`maxHeartbeats` survivors are dropped/lowered (OQ1 resolved); the general-`d` API is *not* frozen,
leaving Phase 23's design recon free to shape it. This unblocks — but does not start — the
general-`d` "part 2" migration, which lands with/after Phase 23. The math frontier
(`notes/MolecularConjecture.md`) is **unchanged** by this phase: still Phase 23 (Case III general
`d`, KT Lemma 6.13).

## Decisions made during this phase

### Phase-local choices and proof techniques

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
