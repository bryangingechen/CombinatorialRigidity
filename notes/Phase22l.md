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

**Next concrete step: L0 — flip the carrier and build the API foundation in
`RigidityMatrix.lean`** (`abbrev ScrewSpace`→`def` + the 3 `inferInstanceAs` instances + the
`ScrewSpace_def` defeq bridge + `mk`/`val`/`val_mk`/`mk_val`/`val_injective` + `equivExteriorPower`;
migrate that file's ~3 mechanical reach-in sites and the `Module.Dual`-ext lemmas it holds;
get `RigidityMatrix.lean` green). Nothing migrated yet — this is the phase-open commit (docs only).

The design recon (`notes/ScrewSpaceCarrier-design.md` §5) is complete and **killed the surgical
"localized wrapper" option** (Shape 1): the realization predicates the capped decls return *and*
consume structurally embed `ScrewSpace k`, so the opaque head cannot be localized to the assembly
files. The only coherent path is **Shape 2** (full opaque carrier, bottom-up), ~3–5 sessions.
The `screwBasis`-transport micro-spike (§5 OQ3) confirmed the transport is **defeq-free**, so the
recon's feared-hardest category (hard-part (d)) is essentially mechanical.

## Architectural choices made up front

- **Shape 2, bottom-up.** Migrate one file green at a time along the confirmed-linear import
  spine **RigidityMatrix → PanelLayer → Pinning → PanelHinge → GenericityDevice → Coupling →
  CaseI → CaseII → CaseIII → Theorem55**. `Meet.lean` is pass-through (operates on the bare
  `⋀[ℝ]^j V` Subtype, never returns a `ScrewSpace`-typed value) and `Extensor.lean` /
  `Deficiency.lean` / `Induction/` sit below or beside the carrier — **untouched**.
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

- [ ] **L0 — `RigidityMatrix.lean`: the opaque-carrier API foundation.** The carrier flip + the
  full API (`def`, `ScrewSpace_def`, 3 instances, `mk`/`val`/simp/`val_injective`,
  `equivExteriorPower`) + this file's ~3 mechanical reach-ins + its `Module.Dual`-ext lemmas.
  Exit: `RigidityMatrix.lean` builds opaque. **Needs-thought concentration:** the API design +
  the `Module.Dual`-ext lemmas (category (e), the §38 cost site).
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
  `case_cut_edge_realization_gp` (600000). **Phase exit criterion:** the full d=3 spine builds on
  the opaque carrier *and* the three surviving `maxHeartbeats` overrides
  (`notes/ScrewSpaceCarrier-design.md` §1) are dropped or lowered toward default — the end-to-end
  cap drop that OQ1 could not confirm on synthetic benches.

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

**Smallest next commit: L0** — the carrier flip + API foundation in `RigidityMatrix.lean`, green.
This is the de-risk-everything-else commit: it fixes the API shape every later layer mechanically
follows. After L0 lands, reassess the per-layer estimate against the first real (non-synthetic)
reach-in counts.

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
