# Phase 22j — the shared eq.-(6.12) placement abstraction (work log)

**Status:** in progress (opened 2026-06-14 at the 22i close; one work log active at a time).

## Current state

**Next: a recon/design-pass to scope the split-refactor plan (then execute).** User decision
(2026-06-15, `coordinate-phase` option c): do BOTH suppression refactors within 22j, then assess
whether the molecular-conjecture files/proofs warrant further splitting (build-time / unwieldiness).
The heartbeats refactor = split the L6b producer into helper lemmas, which is a concrete instance of the
wider split question — so the recon scopes both at once; the longLine reflow lands *after* the split (it
changes line counts). Coordinator-measured: **CaseI.lean is 10,346 lines** (the prime split candidate;
next-largest molecular files ≈3.4–3.8k) with four raised heartbeat budgets (:3723 3.2M above the
producer, plus 400k/800k/800k for later decls). The dead-code half of the cleanup bundle landed (deleted
`hso_ne_sn` + its trailing stale comment block + the stale `h_hnewpin_v`/TODO lines in
`case_II_realization_all_k`). The **suppression drops are both infeasible as a mechanical P≈1 cleanup** —
empirically verified 2026-06-15, the note's "retry post-S4a" premise was wrong:
- **`maxHeartbeats 3200000` drop FAILS the build.** Reverting to the default 200000 ceiling times out at
  three positions in the producer (`isDefEq` ~:4205, tactic exec ~:4189, `whnf` at the decl head). The
  86s wall-clock figure does *not* mean it fits the default heartbeat budget — wall-clock ≠ heartbeats.
  Dropping this needs profiling + optimizing the hot tactic blocks (or splitting the producer into
  helper lemmas) to fit a smaller budget.
- **`linter.style.longLine false` drop would emit ~80 warnings.** The producer body still has ≈80
  over-length (>100-char) lines — section-divider comments padded with `─`, long explanatory comments,
  and several genuine code lines. Dropping the suppression needs reflowing all ~80 lines (not mechanical;
  the code lines must wrap without breaking proofs).

Both are real refactor sub-steps, not P≈1 drops. The `CLEANUP.md` §C-note refresh (coordinator-authored)
still applies for the slimmed producer.

**Landed** (per-slice detail in the *Layer plan* checklist + *Decisions made* below; the design is
§1.68): S1 Brick A (`le_finrank_span_rigidityRows_of_pinned_placement` + `_augment`) → S2 its blueprint
node → S4a consolidated the L6b producer's `hrank_lb` onto Brick A → **S4b skipped** (a net-negative
one-call-site extraction) → S5 retired the dead L6a (`case_II_placement_eq612_kdof`), leaving the rigid
witness `case_II_placement_eq612` untouched (§1.68(f)'s "re-prove through Brick A" was a shape error —
the load-bearing invariant below). Only the cleanup bundle remains.

22j's arc: introduce the shared span-transport "pinned placement" rank brick (Brick A) the
Case-II / Lemma-6.8 producers should have shared — the L6b producer inlined a ≈1010-line placement
because no shared brick fit the split-off `Gab ⋬ G` — refactor L6b's rank half onto it, retire the
dead L6a, land the cleanup. **22k's Case III consumes Brick A**, so the abstraction lands first.

## Architectural choices made up front

Canonical design: **`notes/Phase22-realization-design.md` §1.68** (the recon verdict — the TWO-brick
family, Brick A's signature + proof skeleton, the per-case `hold_span` discharge map, why Case I stays
separate, the retrofit/blueprint impact). Point at it; do not duplicate. Load-bearing invariants:
- **Brick A is span-level** (NEW-pinned + OLD-in-span interface → a `finrank` lower bound); its proof
  is L6b's `hrank_lb` skeleton lifted out — **no new math**. The genuinely-new content is the
  *callers'* discharge of `hold_span` (L6b's `e₀ = e_a + e_b` row decomposition).
- **DO NOT delete OR re-prove the rigid `case_II_placement_eq612`** — it is the `\leanok` witness for
  `lem:case-II-realization-placement` (`\uses`'d across `case-iii.tex` = 22k's Case-III chain). Leave it
  **untouched** (already green + axiom-clean). The original §1.68(f) "re-express through Brick A" was a
  **shape error**: Brick A returns a bare `finrank` bound (shape A), but the decl exposes a literal `∃ s`
  panel-row subfamily (shape B) — Brick A loses the `∃ s` (recon-settled 2026-06-14; full verdict §1.68(f)).
- **Brick B** (`case_III_old_new_blocks`, the literal-`panelRow` device-feed shape) is NOT unified
  with Brick A and is left untouched here; its deficiency-aware generalization (S3) is **22k's**.

## Layer plan / task list (with dispatch shape per slice — for `coordinate-phase 22j`)

Full task list, populated before any build (CLEANUP.md discipline). Difficulty P≈N for the
model-experiment. Each slice's gate is `lake build` + `lake lint` **warning-clean** + axiom-clean
(+ `blueprint/verify.sh` where a blueprint pointer is touched).

- [x] **S1 — build Brick A** `le_finrank_span_rigidityRows_of_pinned_placement` (+ the `_augment`
  variant for Case III's `+1`) in `RigidityMatrix.lean` (`section PinnedPlacementBrick`, beside
  `le_finrank_span_rigidityRows_of_splice`). **DONE.** Lifted L6b's `hrank_lb` skeleton
  (CaseI.lean:4708–4749) to the abstract span-transport interface (§1.68(c)):
  `linearIndependent_sum_pinned_block`(`_augment`) → `finrank_span_eq_card` → `Submodule.finrank_mono`.
  Open risk (`Nat.card`/`Fintype`, §1.68(g)(i)) resolved cleanly via the standard
  `Nat.card_eq_fintype_card`+`Fintype.card_sum` bridge.
- [x] **S2 — blueprint node** `lem:rigidityRows-pinned-placement-rank-add` in `rigidity-matrix.tex`,
  beside `lem:rigidityRows-splice-rank-add`; `\lean{}` (both bricks) + `\leanok` + `\uses`
  (`lem:case-II-placement-block-independent` base, `lem:case-III-conditional-block` augment, plus
  `def:rigidity-matrix`). **DONE.** All `verify.sh` gates green.
- [x] **S4a — Brick-A rank consolidation** (`case_II_realization_all_k`, CaseI.lean): `hrank_lb` now
  calls `le_finrank_span_rigidityRows_of_pinned_placement` (NEW = e_b pinned through `v`, OLD = the
  IH's N Gab-rows via `hso_span`); dead inline `hN_FG` + intermediate `hunion` deleted. **DONE.** Gates
  green; §38 *row-family* `isDefEq` blowup fixed by `set rn`/`set ro` + explicit `hbrick` type (no
  `clear_value` — explicit named args; FRICTION + TACTICS-QUIRKS §38 *Abstract-brick call-site*).
- [~] **S4b — extract `he₀_rows_mem` as a named top-level helper — SKIPPED** (coordinator re-scope
  2026-06-14; rationale in *Current state*): the `e₀ = e_a + e_b` decomposition is consumed by only
  `case_II_realization_all_k`, so a top-level helper would be a ~7-arg / one-call-site net-negative
  abstraction; the design's "named discharge" goal is already met by the inline named `have`. Stays
  inline; the Brick-A *value* of S4 landed in S4a.
- [x] **S5 — retire L6a (delete-only) — DONE** (this commit): deleted the dead
  `case_II_placement_eq612_kdof` (doc-comment + decl; no live caller — `case_II_realization_all_k`
  inlines its steps) and reworded the two now-dangling `_kdof` references in the producer's docstring
  so no prose points at a deleted decl. `case_II_placement_eq612` (:3520) left untouched (already green
  + axiom-clean; the §1.68(f) "re-prove through Brick A" route is a shape error — bare `finrank` bound
  vs the decl's literal `∃ s` subfamily). No blueprint pin moved (`_kdof` had no pin, rigid decl
  untouched); gates green (build warning-clean, `lake lint`, producer axiom-clean).
- [x] **Cleanup bundle — dead-code half DONE** (2026-06-15): deleted the dead `hso_ne_sn` have + its
  trailing stale "Hmm, we need a lemma…" comment block + the stale `h_hnewpin_v`/`TODO: pin direction`
  lines inside `case_II_realization_all_k` (31 lines). Gates green (build warning-clean, `lake lint`,
  producer axiom-clean: `propext`/`Classical.choice`/`Quot.sound` only).
- [ ] **Suppression drops — DEFERRED, need a real refactor (NOT mechanical).** See *Current state*: the
  `maxHeartbeats 3200000` drop fails the build (default-200000 timeout at 3 positions); the
  `linter.style.longLine false` drop would emit ~80 over-length-line warnings. Each is a refactor
  sub-step (profile/split the producer for heartbeats; reflow ~80 lines for longLine), not a P≈1 drop.
- [ ] **`CLEANUP.md` §C-note refresh** (coordinator-authored) for the slimmed producer.

**S3 is 22k, not 22j:** generalizing Brick B (`case_III_old_new_blocks` → rank input + `hleG`
transport) is deferred — Case III's rank path consumes the `hρGv`/`hwmem` span-interface, and S3 risks
the `_of_line` device-feed; settle it against 22k's Case III (§1.68(f)).

## Blockers / open questions

- ~~**S1 `Nat.card`/`Fintype` resolution**~~ — RESOLVED at the S1 build (standard
  `Nat.card_eq_fintype_card`+`Fintype.card_sum` bridge; Brick A's interface keys on `Nat.card`, both
  call sites supply `[Finite ιn] [Finite ιo]`).
- **Cleanup suppression-drop is BLOCKED on a refactor** (re-assessed 2026-06-15; the prior "now
  unblocked at 86s" claim was wrong — wall-clock ≠ heartbeats). Dropping `maxHeartbeats 3200000` times
  out at the default 200000 ceiling (3 positions); dropping `linter.style.longLine false` emits ~80
  warnings. Neither is a mechanical drop — see *Current state* for the two refactor sub-steps required.

## Hand-off / next phase

**Next concrete step: a recon/design-pass (docs) scoping the split-refactor plan** — written to
`notes/PERFORMANCE.md` (beside its *Split candidates ranked by leverage* / *Factors to weigh when
ranking splits* / *Import graph* sections), covering (1) the L6b producer heartbeats split (profile →
named helper lemmas with signatures, to drop/lower `maxHeartbeats`), (2) a CaseI.lean file split (10,346
lines — the prime candidate), and (3) a ranked survey of other molecular split candidates for a
follow-up perf round. **User decision (2026-06-15, `coordinate-phase` option c):** do both suppression
refactors within 22j, then assess wider splitting. After the recon, the execution order is: the producer
helper-split (drop/lower `maxHeartbeats`) → longLine reflow on the lines that remain (drop
`linter.style.longLine false`) → the wider file-split recommendation goes to the user for sign-off →
`CLEANUP.md` §C-note refresh + the phase-close checklist. (S1/S2/S4a/S5 + the dead-code cleanup landed;
S4b skipped.)

After 22j: open **Phase 22k** (completing the honest all-`k` Theorem 5.5 — the L7–L10 layer plan in
`notes/Phase22i.md`, consuming Brick A; S3 = the deficiency-aware Brick B lands there), then Phase 23
(general `d`). (S1 + S2 + S4a landed; **S4b skipped** — see *Current state*; S5 + the dead-code cleanup
done.)

### coordinate-phase note (`coordinate-phase 22j`)

Drives this log via the *Hand-off* pivot. **User decided (2026-06-15, option c): do both suppression
refactors within 22j, then assess wider molecular-files splitting.** The cleanup bundle's dead-code half
landed; the two suppression drops are refactors, not mechanical (the "retry post-S4a / 86s" premise was
a wall-clock-≠-heartbeats error). **Next dispatch = a recon/design-pass** (docs design-pass commit to
`notes/PERFORMANCE.md`; opus per override, design-settle): scope the producer heartbeats split + a
CaseI.lean (10,346-line) file split + a ranked survey of other molecular split candidates, with buildable
slices and 22j-vs-follow-up scope. Then execute the producer split → longLine reflow → surface the wider
file-split recommendation to the user → `CLEANUP.md` §C refresh + phase-close. **Phase-close checklist**
(when 22j actually closes): flip 22j ✓ across ROADMAP / README / home_page / intro.tex /
MolecularConjecture; compress ROADMAP §22j; write the model-experiment *Findings* for 22j; then (after
user confirm) open **Phase 22k**. The model-experiment is **running** (opus-only override this session;
availability check recorded 2026-06-15 in the log's repo-local config).

## Decisions made during this phase

### Phase-local choices and proof techniques
- **Phase open (2026-06-14):** the §1.68 recon verdict — a TWO-brick family (Brick A span-rank new +
  Brick B device-feed kept; Case I stays separate). Canonical: §1.68. Verified read-only against the
  landed signatures before opening.
- **S1 — Brick A landed (2026-06-14):** `le_finrank_span_rigidityRows_of_pinned_placement` +
  `_augment` in `RigidityMatrix.lean` (`section PinnedPlacementBrick`). The proof is L6b's `hrank_lb`
  skeleton lifted verbatim — span-transport interface (`hold`/`hnewpin`/`holdindep` +
  `hnew_span`/`hold_span`), conclusion `Nat.card ιn + Nat.card ιo ≤ finrank (span F.rigidityRows)` (no
  literal-`rigidityRows` membership), no new math. `_augment` reuses
  `linearIndependent_sum_pinned_block_augment` for the `+1`.
- **S2 — blueprint node landed (2026-06-14):** `lem:rigidityRows-pinned-placement-rank-add` in
  `rigidity-matrix.tex`, beside the splice node. Both bricks (`…of_pinned_placement` + `_augment`)
  under one `\lean{}` (corner-case grouping); `\uses` the existing pin-a-body block-independence
  nodes — `lem:case-II-placement-block-independent` (base, = `linearIndependent_sum_pinned_block`) +
  `lem:case-III-conditional-block` (augment, = `linearIndependent_sum_pinned_block_augment`) + `def:
  rigidity-matrix`. Prose frames it as the pin-a-body (split) analogue of the collapse-geometry
  splice brick (KT Lemma 6.2 vs 6.8). All `verify.sh` gates green.
- **S4a — Brick-A rank consolidation landed (2026-06-14):** `case_II_realization_all_k`'s `hrank_lb`
  now calls `le_finrank_span_rigidityRows_of_pinned_placement FG` (NEW = e_b pinned through `v`'s screw
  column `hnewpin_eb`, OLD = the IH's N Gab-rows, `hold`/`hso_indep`/`hso_span`); deleted the dead
  inline `hN_FG` and the intermediate `hunion` (the brick computes the pin-a-body split internally).
  `Nat.card sn + Nat.card so = (D−1)+N` then closes via `hsn_card`/`hso_card`/`hNpD` (§1.68(c)).
  Axiom-clean; the inline `he₀_rows_mem`/`hso_span` `hold_span` discharge is untouched (S4b extracts
  it). **Lifted to:** TACTICS-QUIRKS §38 *Abstract-brick call-site* / FRICTION (the §38 row-family
  `isDefEq` blowup recurred at the abstract-brick call; `set rn`/`set ro` fvars + explicit `hbrick`
  type fix it — `set` alone, no `clear_value`, since the brick takes the families as explicit args).
- **S5 — L6a retired (delete-only, 2026-06-14):** deleted the dead `case_II_placement_eq612_kdof`
  (CaseI.lean) — no live caller (`case_II_realization_all_k` inlines its steps). Reworded the producer
  docstring's two `_kdof` references to describe the inline eq.-(6.12) placement + why a
  `case_II_placement_eq612`-shaped brick (needs `hGv : Gv ≤ G`) cannot be reused for the split-off
  `Gab ⋬ G`. The rigid `case_II_placement_eq612` (:3520) left untouched (already green + axiom-clean;
  the §1.68(f) "re-prove through Brick A" route is a shape error — bare `finrank` bound vs the decl's
  literal `∃ s` subfamily). No blueprint pin moved (`_kdof` had no pin). Gates green (build
  warning-clean, `lake lint`, producer axiom-clean). No friction (pure delete + docstring tidy).
- **Cleanup bundle — dead-code half landed; suppression drops found infeasible (2026-06-15):** deleted
  the dead `hso_ne_sn` have + its trailing "Hmm, we need a lemma…" comment block + the stale
  `h_hnewpin_v`/`TODO: pin direction` lines in `case_II_realization_all_k` (31 lines; gates green —
  warning-clean build, `lake lint`, producer axiom-clean). The two suppression drops are **NOT** the
  mechanical P≈1 the note assumed: dropping `maxHeartbeats 3200000` times out at the default-200000
  ceiling (3 positions — empirically verified, `whnf`/`isDefEq`/tactic-exec), and dropping
  `linter.style.longLine false` emits ~80 warnings (the producer still has ≈80 >100-char lines). Each is
  a refactor sub-step (perf-profile/split for heartbeats; reflow ~80 lines for longLine), deferred.
  **Lesson:** an 86s wall-clock build does not imply fitting the default heartbeat budget — verify a
  `maxHeartbeats` drop with an actual build, never infer it from build time.
