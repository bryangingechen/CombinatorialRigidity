# Phase 15 cleanup round (work log)

**Status:** in progress (round opened — sweep complete, task list
recorded; no fixes started yet).

Between-phases cleanup round, run after Phase 15 (body-bar Tay theorem,
existence form) closed in `fa4cfc3` and before Phase 16 (body-hinge /
panel-hinge Tay–Whiteley) opens. Round manual: `CLEANUP.md`. The
per-commit friction review (`CombinatorialRigidity/CLAUDE.md`) still
fires on every commit in this round.

## Current state

Round just opened (this commit = log skeleton + swept A–D task list per
`CLEANUP.md` *Workflow* rules 1+2). No fixes landed yet. Build is green +
warning-clean on the Phase-15 surface (`lake build
CombinatorialRigidity.BodyBar.TayTheorem`, verified at round open). All
sweep findings are in the task list below; a fresh session can resume
from this log alone. The smallest concrete next commit is named in
*Hand-off / next phase*.

## Scope

Phase 15 surface — two new Lean files + the Phase-15 blueprint nodes.
No new `CombinatorialRigidity/Mathlib/` adders shipped in Phase 15 (the
phase reused Phase-6/14 mirrors and `apnelson1/Matroid` API), so the
mirror-directory leg of the usual sweep is empty.

- **(A) Blueprint ↔ Lean divergence** — `body-bar.tex`
  §`sec:body-bar-framework` (4 nodes: `def:body-bar-framework`,
  `def:rigidity-map-body-bar`, `def:infinitesimally-rigid-body-bar`,
  `def:independent-body-bar`) + §`sec:body-bar-tay` (3 nodes:
  `thm:tay-witness`, `prop:tay-witness-exists`,
  `lem:tay-isSparse-of-independent`). All green at phase close; expect
  mostly no-op, but the per-node signature compare + prose re-read +
  formalization-aside scan is the audit gate. One *known candidate*
  divergence to confirm (A1): blueprint `def:rigidity-map-body-bar`
  describes motions as `m : G.vertexSet → ℝᵈ`, whereas the Lean
  `Motion n α = α → ℝᵈ` is over the full vertex type `α` — `notes/
  Phase15.md` *Decisions made* documents the `α`-vs-`↥V` choice (dodges
  `dInc` subtype coercions); confirm the prose is an acceptable gloss or
  reword.
- **(B) Code-smell sweep** — `BodyBar/{Framework,TayTheorem}.lean`.
  Greps already run at round open (findings in the task list).
- **(C) Long-proof audit** — the three 30+-line proofs in
  `TayTheorem.lean` surfaced by the LoC ranking.
- **(D) Project-organization compression** — `notes/Phase15.md` is 272
  lines, over the 250 soft budget; compress now that the phase is closed.
  Re-skim `FRICTION.md` status sections for the two Phase-15 `[resolved]`
  entries fully indexed elsewhere. Plus the known carry-over derivation
  item (`stdFramework_rigidityRow_eq` from `rigidityRow_eq`).

## Task list

### A. Blueprint ↔ Lean divergence audit

- [ ] A1 — per-node `\lean{}` signature compare for all 7 Phase-15 nodes
  (`sec:body-bar-framework` 4 + `sec:body-bar-tay` 3). Confirm every
  `\lean{}` name resolves and each blueprint statement form matches its
  Lean signature. **Known candidate to resolve:** `def:rigidity-map-body-bar`
  prose says motions are `G.vertexSet → ℝᵈ`; Lean `Motion n α = α → ℝᵈ`
  is over the full vertex type (documented decision in `notes/Phase15.md`).
  Either confirm the prose is an acceptable gloss or reword to match the
  `α`-domain Lean (prefer: keep the math reading, note the `α` domain only
  if it reads as a substantive divergence). `checkdecls` is the per-commit
  gate, not an A-task — only run it if this commit touches a `\lean{}` pin.
- [ ] A2 — re-read each Phase-15 node's prose proof for "the Lean does X
  via Y" smoothness glosses and "formalization aside" remarks. First
  response to any aside is a Lean-simplification attempt (`CLEANUP.md` §A);
  only if that fails does the aside stay (made concrete). Spot-check the
  `thm:tay-witness` / `prop:tay-witness-exists` / `lem:tay-isSparse-of-independent`
  proof prose against the (now-landed) converse infra — confirm no stale
  "next sub-step" / "in progress" asides survive from the incremental
  build (cf. Phase-14-cleanup A2, which found six such staleness asides).
  Note: the `TayTheorem.lean` module docstring *Current state* block still
  reads "Phase 15, in progress" and "The converse … is the next sub-step"
  (lines 41–49) — stale now the phase is closed; reword in A2 (Lean-side,
  no blueprint touch) or fold into a B-tidy commit.

### B. Code-smell sweep (greps run at round open)

- [ ] B1 — `classical` invocations (9 sites, all `TayTheorem.lean`:
  L146, 197, 256, 305, 423, 447, 507, 549, 568). For each: is
  `[DecidableEq α]` / `[DecidablePred (· ∈ E(G))]` a cleaner signature
  boundary, or is the `classical` load-bearing (def-unfold or
  statement-level instance needed for `Finset`/`Fintype` ops)? Expect
  most forced per `DESIGN.md` *Typeclass shape* + the Phase-14-cleanup
  precedent; verify by a strip build that each is genuinely needed
  (Phase-14-cleanup B2 found 3 stray `classical`s this way).
- [ ] B2 — `haveI : Fintype … := Fintype.ofFinite _` bridges (8 sites,
  all `TayTheorem.lean`: L257, 306, 307, 424, 448, 550, 569, 574). These
  are the `[Finite] → Fintype` inline bridge the `DESIGN.md` *Vertex
  types* convention prescribes. Confirm each is forced (a body step needs
  `Finset.univ` / `Fintype.card`) and that the repeated `Fintype E(F.graph)`
  bridge (L550, 569 + the `stdFramework`-graph variants L306/307) isn't a
  single-helper candidate. Likely no-op confirm.
- [ ] B3 — `@[nolint unusedArguments]` on `IsInfinitesimallyRigid`
  (`Framework.lean` L161). Already carries a 6-line justification comment
  (semantic `[Finite α]` contract guard, mirrors `Framework.lean`'s
  `SimpleGraph.IsInfinitesimallyRigid` disposition). Confirm the
  justification still holds / matches the bar-joint precedent verbatim;
  expect no-op.
- [ ] B4 — `noncomputable def` (6 sites: `Framework.lean` `barRow` L98,
  `rigidityMap` L119; `TayTheorem.lean` `stdPlacement` L66, `stdFramework`
  L74, `rigidityRow` L129, `blockPairing` L160). Confirm each is forced
  (`innerSL`/`LinearMap.pi` for the first two, `EuclideanSpace.single` /
  bundled-placement for `stdPlacement`/`stdFramework`, `LinearMap.proj`-comp
  for `rigidityRow`, the explicit-`toFun` `blockPairing` may be the
  accidental one — cf. Phase-14-cleanup B3 which found `constPiSpanEquiv`
  accidental). Check `blockPairing` specifically: is its `noncomputable`
  forced (it's built from explicit `toFun`/`map_add'`/`map_smul'` over
  `ℝ`, no `Classical`/`span`/`FractionRing` ingredient)?
- [ ] B5 — `change` tactic (1 site: `TayTheorem.lean` L535 in
  `exists_isIsostatic_of_isTight`, `change Module.finrank … = …` to
  unfold `IsInfinitesimallyRigid`). This is the `def`-predicate-unfold
  pattern flagged in `TACTICS-GOLF.md` § 4 / the `CombinatorialRigidity/
  CLAUDE.md` *Concrete signals* list. Question: could a project-internal
  `IsInfinitesimallyRigid` unfold lemma (or `show`/`refine` reshape)
  replace the `change`, or is it the accepted predicate-unfold idiom
  (matching the `IsLaman`/`IsTight` precedent)? Likely accepted-idiom
  no-op, but record the disposition.
- [ ] B6 — duplicate `variable {α β : Type*}` declaration: `TayTheorem.lean`
  L58 (`variable {α β : Type*} {n : ℕ}`) and again L124 (`variable {α β :
  Type*}`). The L124 redeclaration (inside the same `namespace
  BodyBarFramework`) shadows L58's `α β` redundantly. Drop the redundant
  L124 binder if it's genuinely a no-op re-bind (verify the block between
  doesn't `clear`/rescope `α β`); a small tidy. *(Non-grep-target item,
  surfaced during the B sweep.)*
- [ ] B7 — no-op confirm: 3+-arg single-step `rw` chains and `show … from
  rfl` both came back **clean** (zero hits) on both files at round open.
  Record as no-op; no task beyond this note.

### C. Long-proof audit

Top LoC ranking (over the §C 50-line screening threshold none reach;
top three are the audit gate per `CLEANUP.md` *Calibration* — expect
mostly no-op confirming forced structural shape):

- [ ] C1 — `stdFramework_rigidityRow_linearIndependent` (~40 lines,
  `TayTheorem.lean` L250). Four-question walk: API extraction (the
  `eqv`/`hsnd`/`hjeq` disjoint-cover reindex + `heq` block-single
  rewrite — already feed named lemmas `specRow_linearIndependent` /
  `stdFramework_rigidityRow_eq`); missed mathlib lemma; tactic
  substitution; cross-proof unification (vs. C2/C3). Likely forced
  reindex wiring per the Phase-14-cleanup *Calibration* precedent.
- [ ] C2 — `finrank_rigidityRow_span_le` (~36 lines, L443). Four-question
  walk. The `W`-subspace setup + `hmem`/`himg` membership + `calc`
  finrank-chain. Check the `calc` for a missed `Submodule.finrank_map_le`
  composition; check the converse partner `isSparse_of_isIndependent`
  (C3) for cross-proof unification (they share the `E'ₛ`/`Subtype.val ''`
  bar-set restriction backbone — likely the one genuine unification
  spot-check this round).
- [ ] C3 — `isSparse_of_isIndependent` (~32 lines, L565). Four-question
  walk. The `E'ₛ` pullback + `hfin_eq` LI-span dim + the `omega`/`ring`
  count `calc`. Cross-proof spot-check vs. C2 (shared `E'ₛ` restriction);
  confirm the `calc` arithmetic isn't a missed `Nat.mul_le_mul` /
  fused-bound lemma.

### D. Project-organization compression

- [ ] D1 — compress `notes/Phase15.md` (272 → under 250 budget). The
  closed phase no longer needs its narrated *Current state* (lines 11–121,
  a per-commit build-history narration restating every landed lemma) nor
  the per-node *Lemma checklist* (lines 143–178) at full density. Collapse
  to a commit-log pointer (`e83bde2..fa4cfc3`, the 6 forward-work commits)
  + a witness/rank-count/existence/converse route summary, matching the
  Phase-14-cleanup D1 model (329 → 152). Preserve *Architectural choices
  made up front*, *Decisions made during this phase* (≤8-line entries),
  *Blockers* (resolved), and the *Hand-off / next phase* + *Converse-route
  note* sections.
- [ ] D2 — re-skim `FRICTION.md` status sections. Two Phase-15 `[resolved]`
  entries are candidates (both already `Lifted to:` a TACTICS section):
  - `Finset.sum_ite_eq' silently no-ops …` (L79; Lifted to TACTICS-GOLF
    § 10) — cross-cutting idiom, indexed by `rigidityRow_eq`.
  - `Restating a Pi.single-indexed subterm in a standalone have fails to
    elaborate` (L96; Lifted to TACTICS-QUIRKS § 24) — project-internal
    lesson, indexed by `stdFramework_rigidityRow_eq`.
  Decide migrate-to-archive (fully indexed elsewhere, no Phase-16 forward
  reference) vs. keep-active per the Phase-14-cleanup D2 criterion. Also
  re-confirm the four Phase-13/14 `[resolved]` entries kept active for
  Phase 15 (`Matroid.Union` `[DecidableEq β]`-binder, `signedIncMatrix`
  decidability-`letI`, `Matroid.Union`-ground-is-`univ`, `Graph.Components`-
  `Finite`) — do any now lose their forward reference with Phase 15 closed?
- [ ] D3 — **carry-over derivation item** (from Phase 15 notes *Possible
  cleanup-round item*): `stdFramework_rigidityRow_eq` (the `b_e = e_{j(e)}`
  block-`single` row identity, `TayTheorem.lean` L218) is now the special
  case of the general `rigidityRow_eq` (L342). Derive it from `rigidityRow_eq`
  (`Pi.single (j e) v = fun c ↦ (e_{j e} c) • v` after the std-basis
  collapse) rather than reproving it standalone — removes ~21 lines of
  duplicated incidence-row expansion. **Disposition call:** this is a
  genuine in-round refactor (`CLEANUP.md` *What a cleanup round is not* →
  surfaced-refactor exception), so land it as its own commit if the
  derivation is clean; if the `Pi.single`-vs-block-vector reshape proves
  more than a few lines of glue (the `Pi.single (j e) v = fun c ↦ …`
  rewrite is exactly the elaboration-fragile shape FRICTION L96 warns
  about), record what was tried and leave both standalone.

### Non-A–D items noted during the sweep

- **Both `BodyBar/{Framework,TayTheorem}.lean` are non-`module`** (no
  `module` marker, plain `import`, no `@[expose] public section`). This is
  **forced, not a regression**: every `BodyBar/` file (TreePacking, KFrame,
  Framework, TayTheorem) and the whole Phase 13–15 subtree depend on the
  `apnelson1/Matroid` package, which is only ~4 % `module`-converted (a
  `module` file cannot `import` a non-`module` file — same constraint as
  `LinearRigidityMatroid.lean`, documented in `CombinatorialRigidity/
  CLAUDE.md` *Module-system conversion* → *Some external dependencies block
  conversion*). No action; recorded so the next round doesn't re-investigate.

## Decisions made during this round

<none yet — round just opened>

## Blockers / open questions

<none at round open>

## Hand-off / next phase

**Round just opened** (this commit: log skeleton + A–D task list only, no
fixes — per `CLEANUP.md` *Workflow* rules 1+2 "sweep first, record the
task list before starting fixes"). Build green + warning-clean on the
Phase-15 surface at open.

**Smallest concrete next commit:** land **A2** — reword the stale "Phase
15, in progress" / "the converse … is the next sub-step" *Current state*
block in `TayTheorem.lean`'s module docstring (lines 41–49) to reflect the
closed phase (the converse + full iff are landed). Doc-only, single file,
no blueprint pin touched (so no `checkdecls`), build trivially green —
a clean first fix that also discharges the A2 staleness scan. Then proceed
B → C → D in order; D3 (the `stdFramework_rigidityRow_eq` derivation) is
the one substantive refactor candidate and should land late (after the
A/B/C no-op confirms), as its own commit, with a try-and-record fallback
if the `Pi.single` reshape fights the elaborator.
