# Phase 15 cleanup round (work log)

**Status:** in progress (A landed; B1+B6 landed; B4 landed; B2/B3/B5/B7 no-op confirms landed; C1/C2/C3 no-op confirms landed; D1 landed; D2 landed; D3 remains — closes round).

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

B1+B6 landed (`c1fdaf2`, the first substantive B-sweep finding):
strip-build sweep of the 9 `classical` sites found 4 load-bearing
(kept) and **5 stray** — dropped all 5; plus B6 dropped the redundant
L124 `variable {α β : Type*}` re-bind. B4 landed (this commit, the
second substantive B-sweep finding): the strip-build sweep over the 4
`TayTheorem.lean` `noncomputable def`s found `blockPairing`'s
`noncomputable` **accidental** (the other three forced) — dropped it.
Build warning-clean + lint clean. The remaining B items (B2 `Fintype`
bridges, B3 `nolint`, B5 `change`, B7 zero-hit greps) landed this commit
as a no-op confirm batch (all four confirmed no-op; no code change).
All of B is now closed; next is the **C long-proof audit** (C1–C3),
then **D**. A fresh session can resume from this log alone; the smallest
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
- [x] B2 — `haveI : Fintype … := Fintype.ofFinite _` bridges (8 sites,
  all `TayTheorem.lean`: L256, 304, 305, 422, 445, 545, 563, 568 after
  the B1/B4 line shifts). **No-op confirm:** all 8 forced, not a
  single-helper candidate — see *Decisions made* B2/B3/B5/B7 batch. These
  are the `[Finite] → Fintype` inline bridge the `DESIGN.md` *Vertex
  types* convention prescribes. Confirm each is forced (a body step needs
  `Finset.univ` / `Fintype.card`) and that the repeated `Fintype E(F.graph)`
  bridge (L550, 569 + the `stdFramework`-graph variants L306/307) isn't a
  single-helper candidate. Likely no-op confirm.
- [x] B3 — `@[nolint unusedArguments]` on `IsInfinitesimallyRigid`
  (`Framework.lean` L161). Already carries a 6-line justification comment
  (semantic `[Finite α]` contract guard, mirrors `Framework.lean`'s
  `SimpleGraph.IsInfinitesimallyRigid` disposition). **No-op confirm:**
  justification (L154–160) matches the bar-joint precedent verbatim.
- [x] B4 — `noncomputable def` (6 sites: `Framework.lean` `barRow` L98,
  `rigidityMap` L119; `TayTheorem.lean` `stdPlacement` L67, `stdFramework`
  L75, `rigidityRow` L128, `blockPairing` L159). **Strip-build sweep:
  `blockPairing`'s `noncomputable` is accidental — dropped.** Removing all
  four `TayTheorem.lean` markers and forcing a recompile errored on exactly
  three (`stdPlacement` ← `Real.instRCLike` via `EuclideanSpace.single`;
  `stdFramework` ← `stdPlacement`; `rigidityRow` ← `rigidityMap`), and
  **not** `blockPairing` — it is the explicit-`toFun`/`map_add'`/`map_smul'`
  bundling over `ℝ` with no `Classical`/`span`/`EuclideanSpace`-norm
  ingredient, so it is computable. `barRow`/`rigidityMap` (`Framework.lean`)
  are forced (`innerSL`/`LinearMap.pi`). Substantive change → own commit
  (not folded with the no-op confirms). Mirrors Phase-14-cleanup B3
  (accidental `noncomputable` on `constPiSpanEquiv`).
- [x] B5 — `change` tactic (1 site: `TayTheorem.lean` L531 after the
  B1/B4 line shifts, in `exists_isIsostatic_of_isTight`, `change
  Module.finrank … = …` to unfold `IsInfinitesimallyRigid`). This is the
  `def`-predicate-unfold pattern flagged in `TACTICS-GOLF.md` § 4 / the
  `CombinatorialRigidity/CLAUDE.md` *Concrete signals* list. **No-op
  confirm:** accepted predicate-unfold idiom (matches the `IsLaman`/
  `IsTight` precedent); no project-internal unfold lemma warranted.
- [x] B6 — duplicate `variable {α β : Type*}` declaration: `TayTheorem.lean`
  L58 (`variable {α β : Type*} {n : ℕ}`) and again L124 (`variable {α β :
  Type*}`). **Dropped the L124 re-bind.** Verified no `clear`/rescope of
  `α β` between L58 and L124 (only the three `stdFramework*` decls + the
  block-rank docstring); dropping L124 leaves `α β n` all from L58.
  Build + lint clean. Folded into the B1 commit (both are real edits in
  the same file / same sweep, neither a no-op confirm).
- [x] B7 — no-op confirm: 3+-arg single-step `rw` chains and `show … from
  rfl` both came back **clean** (zero hits) on both files; re-confirmed
  this commit. Record as no-op; no task beyond this note.

### C. Long-proof audit

Top LoC ranking (over the §C 50-line screening threshold none reach;
top three are the audit gate per `CLEANUP.md` *Calibration* — expect
mostly no-op confirming forced structural shape):

- [x] C1 — `stdFramework_rigidityRow_linearIndependent` (~40 lines,
  `TayTheorem.lean` L249). **No-op confirm.** API extraction already done
  (`specRow_linearIndependent`, `stdFramework_rigidityRow_eq`,
  `blockPairing_injective` are all named lemmas); the `eqv`/`hsnd`/`hjeq`/
  `heq` block is forced disjoint-cover reindex wiring (no `Set.unionEqSigmaOfDisjoint`-
  fusing lemma exists), matching the Phase-14-cleanup *Calibration* precedent.
  No missed mathlib lemma; tactics already minimal (`simp only`, `funext`,
  `.comp`/`.map'`/`.neg`). No cross-proof unification (C1 is the witness LI,
  C2/C3 the converse bound — disjoint shapes).
- [x] C2 — `finrank_rigidityRow_span_le` (~34 lines, L441). **No-op
  confirm.** The `W`-subspace + `hmem`/`himg` + `calc` finrank-chain
  (`finrank_mono` → `finrank_map_le` → `finrank_realBlockPiSpanOn`) has
  **no** fused-lemma collapse: `loogle` for `finrank _ ≤ finrank (map _ _)
  → finrank _ ≤ finrank _` returns empty, so the two-step `calc` is forced.
  The C2↔C3 "shared `E'ₛ`/`Subtype.val ''` backbone" resolves as
  **C3-delegates-to-C2** (C3 calls `finrank_rigidityRow_span_le F D E'ₛ`),
  not duplication — already unified, no shared lemma to extract.
- [x] C3 — `isSparse_of_isIndependent` (~30 lines, L560). **No-op
  confirm.** The `E'ₛ` pullback + `hfin_eq` LI-span dim + the count `calc`
  is the standard sparsity-count shape; the `omega`/`ring`/`Nat.mul_le_mul_left`
  steps are each a distinct rewrite (no missed fused `Nat.mul_le_mul` bound).
  Cross-proof spot-check vs. C2: delegates to C2 (see C2), so no duplicated
  backbone.

### D. Project-organization compression

- [x] D1 — compress `notes/Phase15.md` (273 → **167** lines, under the 250
  budget; matches the Phase-14-cleanup D1 model 329 → 152). Collapsed the
  narrated *Current state* (per-commit build-history narration restating
  every landed lemma) to a commit-log pointer (`e83bde2..fa4cfc3`, the 6
  forward-work commits) + a five-bullet witness/rank-count/existence/
  converse/iff route summary + the axiom line; **dropped** the per-node
  *Lemma checklist* entirely (the leaf to-do list lives in the
  `body-bar.tex` dep-graph, not duplicated here — Phase-14-cleanup
  precedent). Preserved *Architectural choices made up front*, *Decisions
  made* (all ≤8-line entries, untouched), *Blockers* (resolved), and the
  *Hand-off* + *Converse-route note* + *Possible cleanup-round item* (the
  D3 reference) sections verbatim.
- [x] D2 — re-skimmed `FRICTION.md` status sections. **Migrated the two
  Phase-15 `[resolved]` entries to `FRICTION-archive.md`** (both fully
  indexed by a TACTICS section, both consumer decls in `TayTheorem.lean`,
  no Phase-16 forward reference):
  - `Finset.sum_ite_eq' silently no-ops …` → TACTICS-GOLF § 10, indexed
    by `rigidityRow_eq`.
  - `Restating a Pi.single-indexed subterm in a standalone have fails to
    elaborate` → TACTICS-QUIRKS § 24, indexed by `stdFramework_rigidityRow_eq`.
  **Kept active** the four Phase-13/14 `[resolved]` entries (`Matroid.Union`
  `[DecidableEq β]`-binder, `signedIncMatrix` decidability-`letI`,
  `Matroid.Union`-ground-is-`univ`, `Graph.Components`-`Finite`): each is an
  `apnelson1/Matroid`-API idiom the body-bar chain reuses, so each is a live
  **Phase-16** (body-hinge) forward reference — same disposition logic as
  Phase-14-cleanup D2 (which kept them as live Phase-15 references). No
  TACTICS lift (the two migrated entries are already lifted; the four kept
  are type-specific project idioms, not general rules).
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
- **B4 (accidental `noncomputable` on `blockPairing` dropped).**
  Strip-build sweep over the 4 `TayTheorem.lean` `noncomputable def`s:
  recompiling with all four stripped errored on exactly `stdPlacement`
  (`Real.instRCLike` via `EuclideanSpace.single`), `stdFramework` (depends
  on `stdPlacement`), and `rigidityRow` (depends on `rigidityMap`) — those
  three stay. `blockPairing` is the explicit-`toFun` bundling over `ℝ` with
  no noncomputable ingredient, so its `noncomputable` was dead; dropped.
  `Framework.lean`'s `barRow`/`rigidityMap` are forced. Same
  disposition + method as Phase-14-cleanup B3 (`constPiSpanEquiv`). No
  friction (mechanical removal, build warning-clean + lint clean).
- **C1/C2/C3 (long-proof no-op confirm batch).** All three top-LoC
  proofs closed no-op (matches `CLEANUP.md` *Calibration*: top-10 rankings
  surface structural shape, not extraction debt). C1's reindex wiring is
  forced (already feeds named lemmas; no cover-fusing lemma). C2's `calc`
  has no fused `finrank (map) ≤ finrank` collapse (`loogle` empty). The
  C2↔C3 "shared backbone" is C3-delegates-to-C2 (C3 calls C2 on the `E'ₛ`
  pullback), already unified — not a duplicated backbone needing extraction.
  No code change; build green + lint clean.

- **B2/B3/B5/B7 (no-op confirm batch).** B2: all 8 `Fintype.ofFinite`
  bridges forced — `Fintype α` (L256/422/445) feeds the block-product
  dimension lemmas (`finrank_constPiSpan` / `finrank_realBlockPiSpanOn`)
  and the `specRow` block reindex; the `Fintype E(…)` bridges
  (L304/305/545/563/568) feed `Fintype.card_congr` / `finrank_span_eq_card`
  / `Set.toFinset_card` via `Nat.card_eq_fintype_card`. The repeated
  bridges live in distinct theorems with no shared scope, so not a
  single-helper candidate. B3: the `IsInfinitesimallyRigid` `@[nolint
  unusedArguments]` justification (Framework.lean L154–160) still matches
  the bar-joint precedent verbatim. B5: the L531 `change` is the accepted
  `def`-predicate-unfold idiom (cf. `IsLaman`/`IsTight`, TACTICS-GOLF §4).
  B7: zero-hit greps re-confirmed (3+-arg `rw` chains, `show … from rfl`).
  No code change; build green.

- **D2 (FRICTION.md re-skim, doc-only).** Migrated the two Phase-15
  `[resolved]` entries (`Finset.sum_ite_eq'` no-op → TACTICS-GOLF § 10,
  indexed by `rigidityRow_eq`; `Pi.single`-indexed standalone `have` →
  TACTICS-QUIRKS § 24, indexed by `stdFramework_rigidityRow_eq`) to
  `FRICTION-archive.md` — both fully indexed by a TACTICS section + a named
  `TayTheorem.lean` consumer decl, neither forward-referenced by Phase 16.
  Kept the four Phase-13/14 entries active: each is an `apnelson1/Matroid`-API
  idiom the body-bar chain (Phase 16 body-hinge) reuses — same keep-active
  logic Phase-14-cleanup D2 applied for Phase 15. No TACTICS lift; pure §D
  housekeeping, no Lean code touched.

## Blockers / open questions

<none at round open>

## Hand-off / next phase

**A complete; all of B closed; C complete; D1 + D2 landed (D2 this
commit, notes-only).** D2 migrated the two Phase-15 `[resolved]` FRICTION
entries to `FRICTION-archive.md` (both TACTICS-indexed + decl-indexed, no
Phase-16 forward ref) and kept the four Phase-13/14 `apnelson1/Matroid`-API
entries active (live Phase-16 body-hinge references). No Lean code touched.

**Smallest concrete next commit:** **D3** (the
`stdFramework_rigidityRow_eq` derivation from `rigidityRow_eq`,
`TayTheorem.lean` L218 vs L342) — the one substantive refactor candidate of
the round, as its own commit. Goal: derive the `b_e = e_{j(e)}` block-`single`
row identity as the special case of the general `rigidityRow_eq` (after the
std-basis collapse `Pi.single (j e) v = fun c ↦ (e_{j e} c) • v`) instead of
reproving it standalone, removing ~21 lines of duplicated incidence-row
expansion. **Try-and-record fallback:** if the `Pi.single`-vs-block-vector
reshape proves more than a few lines of glue (it is exactly the
elaboration-fragile shape now archived under FRICTION → TACTICS-QUIRKS § 24),
record what was tried and leave both standalone. D3 closes the round.
