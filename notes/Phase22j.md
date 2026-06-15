# Phase 22j — the shared eq.-(6.12) placement abstraction (work log)

**Status:** in progress (opened 2026-06-14 at the 22i close; one work log active at a time).

## Current state

**A0+A1+A2 LANDED (2026-06-15); BOTH suppression refactors now done. Next = A3 (`CLEANUP.md` §C-note
refresh, coordinator-authored) → phase-close, then surface file-split plan (B) to the user.** The
ranked split-refactor plan is in `notes/PERFORMANCE.md` *Molecular `CaseI.lean` perf recon
(2026-06-15…)*. User decision (2026-06-15, `coordinate-phase` option c): do BOTH suppression refactors
within 22j, then assess wider splitting.

The L6b producer `PanelHingeFramework.case_II_realization_all_k` now carries **neither suppression** as
a stopgap: A0+A1 cut its `maxHeartbeats` budget 3.2M (16×) → **600000 (3×)** (A0 free 3.2M→800000, A1
extracting the two ℤ/ℕ rank-cast bridges `toNat_le_of_add_pred_eq` + `sub_toNat_eq_of_add_pred_eq` in
`RigidityMatrix.lean`); A2 reflowed its 37 over-100-codepoint lines and dropped
`set_option linter.style.longLine false in`. The 600000 budget stays (NOT a stopgap): the cost is
*diffuse* (3 over-budget sites, recon-confirmed), so it is the honest bisected minimum, with a
documented justifying comment. Only A3 (the §C-note refresh) and phase-close remain.

**Landed before this session** (per-slice detail in the *Layer plan* checklist + *Decisions made* below;
the design is §1.68): S1 Brick A (`le_finrank_span_rigidityRows_of_pinned_placement` + `_augment`) → S2
its blueprint node → S4a consolidated the L6b producer's `hrank_lb` onto Brick A → **S4b skipped** (a
net-negative one-call-site extraction) → S5 retired the dead L6a → the cleanup bundle's dead-code half.

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
- [x] **A0 — free budget lower** `maxHeartbeats 3200000` → `800000` (:3723), no other change.
  **DONE** (2026-06-15): bisection confirmed — 800000 builds clean (68s, warning-free), `lake lint`
  clean, producer axiom-clean (`propext`/`Classical.choice`/`Quot.sound`). Suppression now 4× default.
- [x] **A1 — Helper 1 (the heartbeats refactor) — DONE** (2026-06-15): landed
  `toNat_le_of_add_pred_eq` (the `_le` companion) + `sub_toNat_eq_of_add_pred_eq` (the eq) in
  `RigidityMatrix.lean` (`section RankArithmetic`, before `namespace BodyHingeFramework` — pure scalar
  ℤ/ℕ plumbing, kept *out* of the rigidity namespace). Both are keyed on the rank equation
  `N + (D−1) = D·(V−1) − k` (general `D`, not `screwDim`-specific). Rewrote `hrank_lb_nat` (:4497) +
  `hrankge_int` (:4634) to call them. Re-bisect: the producer budget drops **800000 → 600000** (was
  ∈(600000, 800000], now ∈(400000, 600000]). The whole-decl `set_option maxHeartbeats` stays at 600000
  (3× default) — default 200000 FAILS at 3 sites (:4209/:4193 geometric middle + :4474 Brick-A), and a
  per-`have` localized budget on the Brick-A call does NOT suffice (the cost is **diffuse** across the
  geometric Steps, recon-confirmed; the localized-only build still timed out at :4209/:4193). Gates
  green (build warning-clean 67s, full project warning-clean, `lake lint`, all three decls axiom-clean).
- [x] **A2 — longLine reflow — DONE** (2026-06-15): reflowed the producer's **37** over-100-codepoint
  lines (comment/divider rewrap + code breaks at natural delimiters) and dropped the producer's
  `set_option linter.style.longLine false in` (+ its now-stale stopgap comment). The recon's "72 long
  lines" was a byte-count over-report — the longLine linter counts **codepoints** (lifted: TACTICS-
  QUIRKS §55). Geometric Step 12–15 middle left inline (S4b trap). Gates green (CaseI + full project
  build warning-clean 67s, `lake lint`, producer axiom-clean propext/Classical.choice/Quot.sound).
- [ ] **(B) follow-up — CaseI.lean file split (NOT 22j; user sign-off after close).** 10,346 lines →
  5-file `AlgebraicInduction/` chain. Plan + verified DAG + leverage in the PERFORMANCE.md recon.
- [x] **`CLEANUP.md` §C-note refresh — DONE** (2026-06-15, coordinator-authored): added a §C
  *Long-proof audit* calibration entry for the L6b producer — only one small sub-lemma was extractable
  (the rank-cast bridge), the rest is diffuse / non-factoring, so the lever is a **file split** (ranked
  in `notes/PERFORMANCE.md`), not sub-lemma extraction. **User decision (option a):** close 22j now;
  the CaseI.lean file split (B) + C candidates land in a dedicated follow-up perf round.

**S3 is 22k, not 22j:** generalizing Brick B (`case_III_old_new_blocks` → rank input + `hleG`
transport) is deferred — Case III's rank path consumes the `hρGv`/`hwmem` span-interface, and S3 risks
the `_of_line` device-feed; settle it against 22k's Case III (§1.68(f)).

## Blockers / open questions

None open. All resolved: S1 `Nat.card`/`Fintype` (standard `Nat.card_eq_fintype_card`+`Fintype.card_sum`
bridge); the suppression-drop "blocker" (was a refactor, now both done — A0+A1 heartbeats, A2 longLine);
and the flagged "localized vs whole-decl budget" decision (A1 confirmed *diffuse* cost → whole-decl
600000, no localized per-`have` budget). Only A3 (§C-note refresh) + phase-close remain — see *Hand-off*.

## Hand-off / next phase

**A0+A1+A2 LANDED (2026-06-15); both suppression refactors done; next concrete step = A3
(`CLEANUP.md` §C-note refresh, coordinator-authored) → phase-close checklist.** The split-refactor
plan is in `notes/PERFORMANCE.md` *Molecular `CaseI.lean` perf recon (2026-06-15, Phase 22j
design-pass)*. The producer now carries only the justified `maxHeartbeats 600000` (its diffuse-cost
bisected minimum) and no longLine suppression.

**A3 — `CLEANUP.md` §C-note refresh** (coordinator-authored) → phase-close checklist.
**Plan (B)** — the `CaseI.lean` 10,346-line file split into a 5-file `AlgebraicInduction/` chain
(`Coupling`/`CaseI`/`CaseII`/`CaseIII`/`Theorem55`; verified clean forward DAG, zero downstream-import
benefit but very high factor-2/3/4 leverage, pure rename-free move so blueprint pins/`checkdecls`
unaffected) — is a **separate follow-up perf round**: surface to the user for sign-off after 22j closes,
do not fold into 22j. (S1/S2/S4a/S5 + the dead-code cleanup + A0/A1/A2 landed; S4b skipped.)

After 22j: open **Phase 22k** (completing the honest all-`k` Theorem 5.5 — the L7–L10 layer plan in
`notes/Phase22i.md`, consuming Brick A; S3 = the deficiency-aware Brick B lands there), then Phase 23
(general `d`). (S1 + S2 + S4a landed; **S4b skipped** — see *Current state*; S5 + the dead-code cleanup
done.)

### coordinate-phase note (`coordinate-phase 22j`)

Drives this log via the *Hand-off* pivot. **User decided (2026-06-15, option c): do both suppression
refactors within 22j, then assess wider molecular-files splitting.** Both suppression refactors are
**DONE**: the heartbeats refactor (A0 free 3.2M→800000 + A1 the scalar rank-cast helpers, dropping the
budget to 600000 = 3× default; the residual is diffuse-cost defeq, not a missing lemma, so the budget
stays — a localized per-`have` budget was tried and does not suffice) and the longLine reflow (A2,
37 codepoint-over-100 lines reflowed, suppression dropped). **Next dispatch = A3** (`CLEANUP.md` §C
refresh, coordinator-authored). Then surface the file-split recommendation (B) to the user →
phase-close. **Phase-close checklist**
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
- **Recon/design-pass landed (2026-06-15, docs-only):** the ranked split-refactor plan is in
  `notes/PERFORMANCE.md` *Molecular `CaseI.lean` perf recon (2026-06-15…)* — verified against landed
  source (decl bodies + import edges, profiler, `maxHeartbeats` bisection, all reverted). Findings: (1)
  the L6b producer's cost is **diffuse `CoeT`/typeclass inference** (~7.7 s `CoeT`, 21 s typeclass), not
  one hot block; it needs ∈(600000, 800000] heartbeats → 3.2M can drop to 800000 free, and to default
  after extracting **one** scalar helper (the ℤ/ℕ rank-cast bridge `toNat_screwDim_mul_pred_sub_eq`,
  the :4522 site); the :4473 Brick-A call site is §38-defeq, localize not extract; the geometric Step
  12–15 middle is the S4b ~15-arg net-negative trap (leave inline). (2) The 72 long lines (49
  comment/divider + 23 code) wrap mechanically. (3) **CaseI.lean (10,346 LoC) file split** = a clean
  forward-DAG 5-file `AlgebraicInduction/` chain, zero downstream-import benefit but top factor-2/3/4
  leverage, rename-free move (pins/`checkdecls` unaffected) — recommended as a **separate follow-up
  round** for user sign-off, not folded into 22j. Plan (A) execution order: A0 (free budget lower) → A1
  (helper) → A2 (reflow) → A3 (§C refresh).
- **A0+A1 — heartbeats refactor landed (2026-06-15):** A0 dropped the producer budget 3.2M → 800000
  (free, bisection-confirmed). A1 extracted the two shared ℤ/ℕ rank-cast bridges
  `toNat_le_of_add_pred_eq` + `sub_toNat_eq_of_add_pred_eq` (keyed on the rank equation
  `N + (D−1) = D·(V−1) − k`, general `D`) into `RigidityMatrix.lean` `section RankArithmetic` (pure
  scalar, kept out of `BodyHingeFramework`), rewriting `hrank_lb_nat` + `hrankge_int` to call them. The
  budget drops 800000 → **600000 (3× default)**. It does **not** reach default: the producer's cost is
  diffuse (3 over-budget sites — the Brick-A `isDefEq` + the geometric middle), so a per-`have` localized
  budget on the Brick-A call alone fails. The whole-decl 600000 is the honest bisected minimum. **Lesson
  (lifted):** a `maxHeartbeats` drop blocked by *diffuse* cost can't be rescued by a localized per-`have`
  budget — lower the whole-decl budget to the bisected minimum. Rename `le_or_lt`→`le_or_gt` → TACTICS-
  QUIRKS §50.
- **A2 — longLine reflow landed (2026-06-15):** reflowed the producer's **37** over-100-codepoint lines
  (comment/divider rewrap, `─`-divider trims, code breaks at natural delimiters — dotted-prefix breaks
  `(Foo.bar baz\n  q).method`, `rw [a,\n b, c]`, type `have h :\n T := by`) and dropped its
  `set_option linter.style.longLine false in` + the stale stopgap comment. No proof restructured; the
  geometric Step 12–15 middle stays inline. The recon's "72 lines" was a **byte over-count** — the
  longLine linter flags by Unicode codepoint (strict `column > 100`), so `awk length` over-reports on
  this glyph-heavy file (lifted → TACTICS-QUIRKS §55). Gates green (CaseI + full project build
  warning-clean, `lake lint`, producer axiom-clean).
