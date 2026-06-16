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

**L0b landed (2026-06-16): `RigidityMatrix.lean`'s remaining carrier-coercion idioms migrated onto
`.val`, project green.** The two category-(b)/(e) carrier reach-ins in the file — `ExtensorInPanel`'s
defining equation `(C : ExteriorAlgebra …) = extensor p` (now `C.val = extensor p`) and the
`ofHinge_supportExtensor_coe` API lemma (renamed `ofHinge_supportExtensor_val`, LHS now `.val`) — are
the only `(C : ExteriorAlgebra …)` coercions over a `ScrewSpace`-typed `C` in this file (the
`⋀[ℝ]^2`-Subtype anonymous constructors at the `complementIso` inputs are NOT `ScrewSpace`-typed and
stay). **Whole project builds + lints clean**: `.val` is defeq to the old coercion while the carrier
is still an `abbrev`, so every downstream `ExtensorInPanel` witness (`⟨p, rfl, hp_perp⟩` at
`Theorem55.lean` 93/94/192/1806/1807; the `exists_extensor_eq_panelSupportExtensor`-fed pair at
`PanelLayer.lean`:621) typechecks unchanged. `ExtensorInPanel` is blueprint-pinned
(`panel-layer.tex`:207) but only its *implementation* changed, not its statement — pin survives,
no restate.

**L0a landed (2026-06-16): the carrier API foundation is in `RigidityMatrix.lean`, project green.**
`ScrewSpace.mk` / `.val` / `val_mk` / `val_mem` / `mk_val` / `val_injective` / `@[ext]` +
`equivExteriorPower` (+ its `_apply`/`_symm_apply` simp) are landed on the carrier; this file's two
genuine `ScrewSpace`-anonymous-constructor sites (`span_omitTwoExtensor_eq_top`, `ofHinge`) are
migrated onto `mk`, and the former's LI transport now routes through `equivExteriorPower`.

**Next concrete step: L1 — `PanelLayer.lean`.** With `RigidityMatrix.lean` fully on the API,
proceed down the spine. L1 transports `screwBasis` through `equivExteriorPower` (defeq-free per OQ3
→ mechanical), the `annihRow` + `@[simp]` family on `.repr`/`.coord`, and the file's construction
reach-ins (incl. `exists_extensor_eq_panelSupportExtensor`'s `(panelSupportExtensor … : ScrewSpace 2
: ExteriorAlgebra …)` coercion → `.val`, and the `⟨extensor …, _⟩ : ScrewSpace 2` anonymous
constructors → `mk`). **Hard-part (d) lives here** — de-risked to mechanical by OQ3. Each commit
keeps the project green (the carrier is still an `abbrev`). **The `abbrev`→opaque-`def` flip lands
LAST**, after the whole spine adopts the API (see *Architectural choices*).

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

Build order = the import spine. Each layer opens with its own reach-in recon of that file (the
mechanical-vs-needs-thought split per the design doc's category map (a)–(e)) and ends with the
file building green. The opening commit does **not** enumerate all ~150–200 sites — it pins the
spine + the hard-part concentrations + the exit criterion.

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
- [ ] **L1 — `PanelLayer.lean`.** Transport `screwBasis` through `equivExteriorPower` (defeq-free
  per OQ3 → mechanical), the `annihRow` + `@[simp]` family (`annihRow_apply`, `_apply_self`,
  `_add`, …) on `.repr`/`.coord`, the construction reach-ins. **Hard-part (d) lives here** —
  de-risked to mechanical by OQ3.
- [ ] **L2 — `Pinning.lean`.**
- [ ] **L3 — `PanelHinge.lean`** (defines `supportExtensor`; the realization predicates
  `HasPanelRealization` / `HasGenericFullRankRealization` that structurally embed `ScrewSpace`).
- [ ] **L4 — `GenericityDevice.lean`** (the 5× near-identical `change … (Pi.single a (screwBasis k t))`
  basis blocks → `rw`/`simp` once the basis vector is no longer defeq-transparent; OQ3 confirms a
  `change`/`rfl` onto the direct basis vector still lands at default transparency).
- [ ] **L5 — `Coupling.lean`.**
- [ ] **L6 — `CaseI.lean`.**
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

**Smallest next commit: L1 — `PanelLayer.lean`.** `RigidityMatrix.lean` is now fully on the API
(L0a + L0b). L1 is the first geometry file down the spine: transport `screwBasis` through
`equivExteriorPower` (defeq-free per OQ3 → mechanical), migrate the `annihRow` + `@[simp]` family on
`.repr`/`.coord`, and swap the construction reach-ins
(`exists_extensor_eq_panelSupportExtensor`'s `(panelSupportExtensor … : ScrewSpace 2 :
ExteriorAlgebra …)` coercion → `.val`; the `⟨extensor …, _⟩ : ScrewSpace 2` anonymous constructors →
`ScrewSpace.mk`). **Hard-part (d) lives here** — de-risked to mechanical by OQ3. Each commit keeps
the project green (the carrier is still an `abbrev`, so partial migration builds). The API shape is
fixed (L0a) — every later layer is the mechanical `⟨v,h⟩`→`ScrewSpace.mk v h` /
`(C : ExteriorAlgebra)`→`C.val` swap. The `abbrev`→opaque-`def` **FLIP lands last**, after the whole
spine adopts the API, as a single small commit that banks the perf win and resolves OQ1. Reassess the
per-layer estimate against the first real (non-synthetic) reach-in counts as L1 lands.

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
