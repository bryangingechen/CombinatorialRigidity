# Phase 15 cleanup round (work log)

**Status:** in progress (A landed; B1+B6 landed; B2–B5/B7 no-op confirms + C/D remain).

Between-phases cleanup round, run after Phase 15 (body-bar Tay theorem,
existence form) closed in `fa4cfc3` and before Phase 16 (body-hinge /
panel-hinge Tay–Whiteley) opens. Round manual: `CLEANUP.md`. The
per-commit friction review (`CombinatorialRigidity/CLAUDE.md`) still
fires on every commit in this round.

## Current state

A complete (A1 + A2 both legs). A1: per-node `\lean{}` signature compare
for all 7 Phase-15 nodes — all 7 resolve and match (no-op confirms; the
known `def:rigidity-map-body-bar` `G.vertexSet → ℝᵈ`-vs-`α`-domain
candidate confirmed as a kept math-reading gloss, not a divergence — see
*Decisions made*). A2 blueprint leg: re-read of the 7 node proofs for
staleness asides surfaced one genuine stale aside in the **chapter
intro** (`body-bar.tex` L8–12: "Its nodes are currently *red* (stated,
not yet formalized) … the to-do list … turns green as the matching Lean
lands") — a forward-mode to-do snapshot left over from when the chapter
opened, now false (Phases 13–15 all complete, every node green).
Reworded to "All three phases are complete: every node below is
formalized (green) …". Doc-only blueprint edit; no `\lean{}` pin touched,
so `checkdecls` not required; `inv web` builds clean.

B1+B6 landed (this commit, the one substantive B-sweep finding):
strip-build sweep of the 9 `classical` sites found 4 load-bearing
(kept) and **5 stray** (`stdFramework_finrank_range`,
`finrank_rigidityRow_span_le`, `exists_isIndependent_of_isSparse`,
`rigidityRow_linearIndependent`, `isSparse_of_isIndependent`) — dropped
all 5; plus B6 dropped the redundant L124 `variable {α β : Type*}`
re-bind. Build + lint warning-clean. The remaining B items (B2 `Fintype`
bridges, B3 `nolint`, B4 `noncomputable`, B5 `change`, B7 zero-hit
greps) are expected no-op confirms and ride the next commit as a batch;
then C → D. A fresh session can resume from this log alone; the smallest
concrete next commit is named in *Hand-off / next phase*.

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

- [x] A1 — per-node `\lean{}` signature compare for all 7 Phase-15 nodes
  (`sec:body-bar-framework` 4 + `sec:body-bar-tay` 3): **all 7 resolve and
  match, no-op.** `def:body-bar-framework` (`bodyBarDim`, `BodyBarFramework`),
  `def:rigidity-map-body-bar` (`rigidityMap`), `def:infinitesimally-rigid-body-bar`
  (`IsInfinitesimallyRigid`, prose `d·b − d` = Lean `rank + d = d·b`),
  `def:independent-body-bar` (`IsIndependent`, `rank = |E|`), `thm:tay-witness`
  (`tay_witness`, two-iff conjunction), `prop:tay-witness-exists`
  (`exists_isIndependent_of_isSparse` / `exists_isIsostatic_of_isTight`),
  `lem:tay-isSparse-of-independent` (`isSparse_of_isIndependent`). **Known
  candidate resolved:** `def:rigidity-map-body-bar` prose `m : G.vertexSet → ℝᵈ`
  vs. Lean `Motion n α = α → ℝᵈ` — kept as a math-reading gloss (not a
  divergence); see *Decisions made*. `checkdecls` not run (no `\lean{}` pin
  touched this commit; only intro prose).
- [ ] A2 — re-read each Phase-15 node's prose proof for "the Lean does X
  via Y" smoothness glosses and "formalization aside" remarks. First
  response to any aside is a Lean-simplification attempt (`CLEANUP.md` §A);
  only if that fails does the aside stay (made concrete). Spot-check the
  `thm:tay-witness` / `prop:tay-witness-exists` / `lem:tay-isSparse-of-independent`
  proof prose against the (now-landed) converse infra — confirm no stale
  "next sub-step" / "in progress" asides survive from the incremental
  build (cf. Phase-14-cleanup A2, which found six such staleness asides).
  **Done (both legs).** *Lean-side leg* (prior commit): the `TayTheorem.lean`
  module docstring *Current state* block (read "Phase 15, in progress" / "The
  converse … is the next sub-step") was reworded to a *Contents* block
  reflecting the closed phase. *Blueprint-prose leg* (this commit): re-read of
  the 7 node proofs surfaced **one genuine stale aside** in the chapter intro
  (`body-bar.tex` L8–12, "Its nodes are currently *red* (stated, not yet
  formalized) … the to-do list … turns green as the matching Lean lands") —
  a forward-mode to-do snapshot now false with Phases 13–15 all green;
  reworded to "All three phases are complete: every node below is formalized
  (green) …". The 7 node-level proof bodies (the `\begin{proof}` blocks) carried
  **no** stale "next sub-step"/"in progress" asides; line 553's "deferred"
  (Whiteley's irreducible-variety lift) is a legitimate documented deferral
  (ROADMAP §15), kept. (cf. Phase-14-cleanup A2, which found six staleness
  asides — Phase 15's incremental build left only the one chapter-intro one.)

### B. Code-smell sweep (greps run at round open)

- [x] B1 — `classical` invocations (9 sites). **Strip-build sweep
  (Phase-14-cleanup B2 method): 4 load-bearing, 5 stray (dropped).**
  Commenting all 9 out and building isolated the load-bearing ones by
  "failed to synthesize instance" errors: `span_range_rigidityRow`
  (the `Pi.basisFun … dualBasis` needs `DecidableEq E(F.graph)`),
  `blockPairing_injective` (the `if x' = x then … else 0` test motion),
  `stdFramework_rigidityRow_linearIndependent`, and
  `finrank_realBlockPiSpanOn` — these 4 keep their `classical`.
  Re-stripping only the remaining 5 (`stdFramework_finrank_range`,
  `finrank_rigidityRow_span_le`, `exists_isIndependent_of_isSparse`,
  `rigidityRow_linearIndependent`, `isSparse_of_isIndependent`) built
  warning-clean: those 5 `classical`s were **stray** — each proof's
  decidability needs are already met by its `haveI : Fintype … :=
  Fintype.ofFinite _` bridges plus the explicit `letI : DecidableEq α`
  / `letI : DecidablePred …` (in `finrank_rigidityRow_span_le`), or
  aren't needed at all. Dropped all 5. Substantive change → own commit
  (not folded with the no-op confirms). Mirrors Phase-14-cleanup B2
  (which found 3 stray `classical`s the same way).
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
- [x] B6 — duplicate `variable {α β : Type*}` declaration: `TayTheorem.lean`
  L58 (`variable {α β : Type*} {n : ℕ}`) and again L124 (`variable {α β :
  Type*}`). **Dropped the L124 re-bind.** Verified no `clear`/rescope of
  `α β` between L58 and L124 (only the three `stdFramework*` decls + the
  block-rank docstring); dropping L124 leaves `α β n` all from L58.
  Build + lint clean. Folded into the B1 commit (both are real edits in
  the same file / same sweep, neither a no-op confirm).
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

- **A1 (`def:rigidity-map-body-bar` motion-domain gloss).** Blueprint prose
  says body motions are `m : G.vertexSet → ℝᵈ`; Lean `Motion n α = α → ℝᵈ`
  is over the full vertex type `α`. Kept as a math-reading gloss, **not**
  reworded: `G.vertexSet → ℝᵈ` is the faithful mathematical statement (a
  motion assigns a velocity to each body), and the `α`-domain is a documented
  formalization convenience (only values on `V(G)` enter the bar constraints;
  the `α` domain dodges `dInc` subtype coercions — `notes/Phase15.md`
  *Decisions made*). Does not read as a substantive divergence, so the prose
  stays as-is per the A1 "keep the math reading" preference.
- **A2 (blueprint-prose staleness leg).** Reworded `body-bar.tex`'s chapter
  intro (L8–12): the stale forward-mode "Its nodes are currently *red*
  (stated, not yet formalized) … the to-do list … turns green as the matching
  Lean lands" → "All three phases are complete: every node below is formalized
  (green) …". Doc-only; no `\lean{}` pin touched (so no `checkdecls`); `inv
  web` builds clean. The 7 Phase-15 node proof bodies carried no staleness
  asides; the only stale prose was the chapter-level to-do snapshot.
- **A2 (Lean-side staleness leg).** Reworded `TayTheorem.lean`'s module
  docstring *Current state (Phase 15, in progress)* block to a *Contents*
  block: dropped the "the converse … is the next sub-step" forward-looking
  prose and the stale `ROADMAP.md §15` pointer, now names both directions
  (`exists_isIndependent_of_isSparse`/`exists_isIsostatic_of_isTight`,
  `isSparse_of_isIndependent`) and the full iff (`tay_witness`). Doc-only,
  build green + warning-clean. No friction (no Lean code touched).

- **B1 (5 stray `classical`s dropped).** Strip-build sweep over the 9
  sites: 4 load-bearing (`span_range_rigidityRow`,
  `blockPairing_injective`, `stdFramework_rigidityRow_linearIndependent`,
  `finrank_realBlockPiSpanOn`), 5 stray. The stray proofs' decidability
  needs are already met by their `Fintype.ofFinite _` bridges / explicit
  `letI`s, so `classical` was dead. Same disposition + method as
  Phase-14-cleanup B2. No friction (mechanical removal, build/lint clean).
- **B6 (redundant `variable` re-bind dropped).** The second `variable {α
  β : Type*}` (L124, after the block-rank docstring) re-bound `α β`
  already in scope from L58's `variable {α β : Type*} {n : ℕ}`; no
  intervening `clear`/rescope, so a no-op tidy. Folded with B1.

## Blockers / open questions

<none at round open>

## Hand-off / next phase

**A complete; B1+B6 landed** (the one substantive B-sweep finding —
5 stray `classical`s + the redundant `variable` re-bind dropped; build +
lint warning-clean).

**Smallest concrete next commit:** the **B2–B5 + B7 no-op confirm
batch** — one commit recording each disposition in the work log (per the
coordinator no-op-batch rule), no code change expected:
- **B2** — 8 `haveI : Fintype … := Fintype.ofFinite _` bridges: confirm
  each is forced (a body step needs `Finset.univ` / `Fintype.card`) and
  that the repeated `Fintype E(F.graph)` bridge isn't a single-helper
  candidate. *(NB the B1 commit removed the `classical` lines above
  several of these; the bridges themselves stay — re-grep for current
  line numbers.)*
- **B3** — `@[nolint unusedArguments]` on `IsInfinitesimallyRigid`: the
  6-line justification matches the bar-joint `Framework.lean` precedent
  verbatim (semantic `[Finite α]` contract guard +
  `unusedFintypeInType`-migration note). **Already verified this round:**
  no-op.
- **B4** — 6 `noncomputable def` sites; check `blockPairing` specifically
  (built from explicit `toFun`/`map_add'`/`map_smul'` over `ℝ`, no
  `Classical`/`span` ingredient — is its `noncomputable` forced or
  accidental, cf. Phase-14-cleanup B3's `constPiSpanEquiv`?).
- **B5** — the 1 `change` site in `exists_isIsostatic_of_isTight`
  (unfold `IsInfinitesimallyRigid`): accepted predicate-unfold idiom vs.
  a project-internal unfold lemma. Likely accepted-idiom no-op.
- **B7** — record the zero-hit greps (3+-arg `rw` chains; `show … from
  rfl`) as no-op.

Then C → D in order; D3 (the `stdFramework_rigidityRow_eq` derivation
from `rigidityRow_eq`) is the one substantive refactor candidate and
should land late, as its own commit, with a try-and-record fallback if
the `Pi.single` reshape fights the elaborator.
