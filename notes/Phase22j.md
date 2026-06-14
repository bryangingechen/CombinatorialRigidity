# Phase 22j — the shared eq.-(6.12) placement abstraction (work log)

**Status:** in progress (opened 2026-06-14 at the 22i close; one work log active at a time).

## Current state

**Next: S5 — retire L6a (delete-only; the rigid placement is left untouched)** (CaseI.lean): delete the
dead `case_II_placement_eq612_kdof` (doc-comment + decl, :3723–3910). **Leave `case_II_placement_eq612`
(:3520) untouched** — it is already green and axiom-clean, and the §1.68(f) "re-prove through Brick A
(option (i))" route is a **shape error** (recon-settled 2026-06-14): Brick A returns a bare `finrank`
bound (shape A), but the decl's conclusion exposes a literal `∃ s` panel-row subfamily (shape B) — Brick A
loses the `∃ s`. Recovering it via Brick A → W6e (`exists_independent_panelRow_subfamily_of_le_finrank`)
is net more work + a less-structured `s` (full verdict in §1.68(f)). So S5 is delete-only; the
`\leanok` witness `lem:case-II-realization-placement` stays green untouched (no blueprint pin moves —
`_kdof` has no pin). *No blueprint pin changes in S5; `lake build` + `lake lint` warning-clean +
axiom-clean only. P≈1.* Then the cleanup bundle, then 22j closes.

**S4b SKIPPED (coordinator re-scope, 2026-06-14).** The optional `he₀_rows_mem` top-level extraction is
**not worth doing** and is dropped: per §1.68(d) the `e₀`-decomposition is consumed by *only*
`case_II_realization_all_k` (Case III/22k uses a different already-isolated discharge, the
`hρGv`/`hwmem` interface; the rigid placement uses `subset_span`), so a top-level helper would be a
~7-arg-signature decl with exactly one call site — a net-negative abstraction. The design's "named
`hold_span` discharge" goal is already met by the inline named `have`, and S4a already brought the
producer under the heartbeat budget (86s), so S4b is not a cleanup prerequisite either. The Brick-A
*value* of S4 landed in S4a.

**S4a — Brick-A rank consolidation — DONE** (this commit): `case_II_realization_all_k`'s `hrank_lb`
now calls `le_finrank_span_rigidityRows_of_pinned_placement` (NEW block = e_b pinned through `v`'s
screw column, OLD block = the IH's N Gab-rows via `hso_span`); the dead inline `hN_FG` and the
intermediate `hunion` are deleted. Gates green (build warning-clean, `lake lint`, axiom-clean — the
three standard axioms). The §38 *row-family* `isDefEq` blowup recurred (6.4M timed out); fixed by
`set rn`/`set ro` (fvars) + explicit `hbrick` type — **no `clear_value` needed** here since the brick
takes the families as explicit named args (FRICTION + TACTICS-QUIRKS §38 *Abstract-brick call-site*).

**S2 — blueprint node — DONE** (this commit): `lem:rigidityRows-pinned-placement-rank-add` landed in
`rigidity-matrix.tex`, beside `lem:rigidityRows-splice-rank-add`; `\lean{}` (both
`le_finrank_span_rigidityRows_of_pinned_placement` + `_augment`) + `\leanok` + `\uses` (the pin-a-body
block-independence nodes `lem:case-II-placement-block-independent` for the base half,
`lem:case-III-conditional-block` for the augment). All gates green (`blueprint/verify.sh` — lint +
checkdecls + TeX build).

**S1 — Brick A — DONE:** `le_finrank_span_rigidityRows_of_pinned_placement` +
`_augment` landed in `RigidityMatrix.lean` (`section PinnedPlacementBrick`, beside the splice brick),
build + lint warning-clean, axiom-clean (the three standard axioms only). The §1.68(g)(i)
`Nat.card`/`Fintype` open risk resolved cleanly — the established `Nat.card_eq_fintype_card` +
`Fintype.card_sum` bridge (the CaseI.lean:4745 idiom). The `_augment` variant routes through
`linearIndependent_sum_pinned_block_augment` for Case III's `+1`.

22j introduces the span-transport "pinned placement" rank brick the Case-II / Lemma-6.8 producers
should have shared — the L6b producer `case_II_realization_all_k` inlined a ≈1010-line placement
because no shared brick fit the split-off `Gab = G.splitOff v a b e₀ ⋬ G` — then refactors L6b + the
rigid placement onto it, retires the dead L6a, and lands the bundled cleanup. **22k's Case III
consumes Brick A**, so the abstraction lands first.

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
- [ ] **S5 — retire L6a (delete-only).** Delete the dead `case_II_placement_eq612_kdof` (CaseI.lean,
  doc-comment + decl, :3723–3910; no live caller — `case_II_realization_all_k` inlines its steps).
  **Leave `case_II_placement_eq612` (:3520) untouched** — already green + axiom-clean; the §1.68(f)
  "re-prove through Brick A (option (i))" route is a **shape error** (Brick A returns a bare `finrank`
  bound, but the decl exposes a literal `∃ s` subfamily — recon-settled 2026-06-14, full verdict in
  §1.68(f)). `lem:case-II-realization-placement` stays green untouched. *Standard build dispatch; **no
  blueprint pin moves** (`_kdof` has no pin, rigid decl untouched) so no `verify.sh` needed — `lake build`
  + `lake lint` warning-clean + axiom-clean only; P≈1.*
- [ ] **Cleanup bundle.** Drop the L6b `set_option maxHeartbeats 3200000` (:3911) +
  `linter.style.longLine false` (:3915) suppressions (retry post-S4); delete dead `hso_ne_sn` (:4613)
  + the stale comment block (:4628–4640) + the stale TODO (:4656); refresh the `CLEANUP.md` §C
  long-proof note for the slimmed producer. *Standard build dispatch for the `.lean` edits (gates);
  the §C-note refresh is coordinator-authored. P≈1.*

**S3 is 22k, not 22j:** generalizing Brick B (`case_III_old_new_blocks` → rank input + `hleG`
transport) is deferred — Case III's rank path consumes the `hρGv`/`hwmem` span-interface, and S3 risks
the `_of_line` device-feed; settle it against 22k's Case III (§1.68(f)).

## Blockers / open questions

- ~~**S1 `Nat.card`/`Fintype` resolution**~~ — RESOLVED at the S1 build (standard
  `Nat.card_eq_fintype_card`+`Fintype.card_sum` bridge; Brick A's interface keys on `Nat.card`, both
  call sites supply `[Finite ιn] [Finite ιo]`).
- **Cleanup suppression-drop** (the `maxHeartbeats 3200000`/`longLine` removal) is now unblocked —
  S4a's Brick-A call builds well under the 3.2M budget at 86s; confirm the drop builds clean in the
  cleanup bundle.

## Hand-off / next phase

**Next concrete commit: S5 — retire L6a (delete-only)** (`CaseI.lean`): delete the dead
`case_II_placement_eq612_kdof` (doc-comment + decl, :3723–3910; no live caller). **Leave
`case_II_placement_eq612` (:3520) untouched** — already green + axiom-clean; the original §1.68(f)
"re-prove through Brick A (option (i))" route was a **shape error** (Brick A → bare `finrank` bound vs
the decl's literal `∃ s` subfamily; recovering it via Brick A → W6e is net more work + less structure —
recon-settled 2026-06-14, full verdict in §1.68(f)). The `\leanok` witness
`lem:case-II-realization-placement` stays green untouched. **No blueprint pin moves** (`_kdof` has no
pin; rigid decl untouched), so `lake build` + `lake lint` warning-clean + axiom-clean only — no
`verify.sh`. Standard build dispatch (P≈1). Then the cleanup bundle (S1 + S2 + S4a landed; **S4b
skipped** — see *Current state*), which closes 22j. At 22j close: open **Phase 22k** (completing the honest all-`k`
Theorem 5.5 — the L7–L10 layer plan in `notes/Phase22i.md`, consuming Brick A; S3 = the
deficiency-aware Brick B lands there), then Phase 23 (general `d`).

### coordinate-phase note (`coordinate-phase 22j`)

Drives this log via the *Hand-off* pivot. **Dispatch shapes:** S1/S4/S5 + the cleanup `.lean` edits are
**standard build dispatch** (the fixed prompt; subagent commits); only S2 touched a blueprint pointer
(the subagent runs `verify.sh`) — **S5 no longer does** (delete-only, rigid decl untouched, `_kdof` has
no pin); the §C-note refresh is **coordinator-authored** (rescue §6). The
model-experiment is **running** — rate S/P/B per slice (difficulties pre-rated above; honor any
standing rung override). S1 is a build (design settled in §1.68), so the step-1 research-shape trigger
should **not** fire — if it seems to, re-read §1.68 rather than dispatching a recon.

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
