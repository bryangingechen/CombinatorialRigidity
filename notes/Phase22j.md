# Phase 22j — the shared eq.-(6.12) placement abstraction (work log)

**Status:** in progress (opened 2026-06-14 at the 22i close; one work log active at a time).

## Current state

**Next: S2 — the blueprint node** `lem:rigidityRows-pinned-placement-rank-add` in
`rigidity-matrix.tex`, beside `lem:rigidityRows-splice-rank-add`; `\lean{}` + `\leanok` + `\uses` (the
pin-a-body block-independence node `linearIndependent_sum_pinned_block`). Touches a blueprint pointer
→ run `blueprint/verify.sh`.

**S1 — Brick A — DONE** (this commit): `le_finrank_span_rigidityRows_of_pinned_placement` +
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
- **DO NOT delete the rigid `case_II_placement_eq612`** — it is the `\leanok` witness for
  `lem:case-II-realization-placement` (`\uses`'d across `case-iii.tex` = 22k's Case-III chain).
  Re-express it through Brick A, keeping the node green.
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
- [ ] **S2 — blueprint node** `lem:rigidityRows-pinned-placement-rank-add` in `rigidity-matrix.tex`,
  beside `lem:rigidityRows-splice-rank-add`; `\lean{}` + `\leanok` + `\uses` (the pin-a-body
  block-independence node). *Standard build dispatch — touches a blueprint pointer, so runs
  `verify.sh`; P≈1.*
- [ ] **S4 — refactor L6b onto Brick A** (`case_II_realization_all_k`, CaseI.lean): replace the inlined
  `hN_FG` (:4513–4526) + `hrank_lb` (:4708–4749) with a Brick A call, and **extract `he₀_rows_mem`
  (:4380–4509) as a named helper** (`…case_II_placement_e0_row_in_span` or similar) discharging Brick
  A's `hold_span`. *The one genuinely-new slice. Standard build dispatch; P≈3 (preserve the
  orientation case-split, §1.68(g)(ii); trace `D(|V|−1)−k` closes, §1.68(c)).*
- [ ] **S5 — retire L6a + re-express the rigid placement.** Delete the dead
  `case_II_placement_eq612_kdof` (CaseI.lean:3735). Re-prove `case_II_placement_eq612` (:3520) through
  Brick A (option (i), §1.68(f)), **keeping `lem:case-II-realization-placement` green** (checkdecls +
  honesty gate; its `hGv ≤ G` stays a genuine hypothesis discharging `hold_span` via `subset_span`).
  *Standard build dispatch — the blueprint pin survives, so `verify.sh`; P≈2.*
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
- **S4 orientation case-split** must survive the `he₀_rows_mem` extraction (§1.68(g)(ii)).
- **Cleanup is gated on S4** having slimmed the proof — sequence the suppression removal after S4.

## Hand-off / next phase

**Next concrete commit: S2 — the blueprint node** `lem:rigidityRows-pinned-placement-rank-add` in
`rigidity-matrix.tex`, beside `lem:rigidityRows-splice-rank-add`; `\lean{}` (both
`le_finrank_span_rigidityRows_of_pinned_placement` + `_augment`) + `\leanok` + `\uses` (the pin-a-body
block-independence node). Touches a blueprint pointer → run `blueprint/verify.sh` (+ `checkdecls`).
Then S4 → S5 → cleanup, in order (S1 — Brick A — landed). At 22j close: open **Phase 22k** (completing
the honest all-`k` Theorem 5.5 — the L7–L10 layer plan in `notes/Phase22i.md`, consuming Brick A; S3 =
the deficiency-aware Brick B lands there), then Phase 23 (general `d`).

### coordinate-phase note (`coordinate-phase 22j`)

Drives this log via the *Hand-off* pivot. **Dispatch shapes:** S1/S4/S5 + the cleanup `.lean` edits are
**standard build dispatch** (the fixed prompt; subagent commits); S2 and S5 touch a blueprint pointer
(the subagent runs `verify.sh`); the §C-note refresh is **coordinator-authored** (rescue §6). The
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
