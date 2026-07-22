# Phase 36 — Proof automation: `grind` adoption + tactic-smell sweep (AUTOMATE, post-program) (work log)

**Status:** ✓ Complete (opened 2026-07-21 recon-first; closed 2026-07-22
— recon/design-pass, four build-neutral sweep slices, then this close).
Internals-only, **structural-edit style** — no new blueprint chapter, no
new mathematics. Every headline statement and its axiom profile is
unchanged; all 17 headline theorems re-verified at the three standard
axioms (`propext`, `Classical.choice`, `Quot.sound`) at close.

## What the phase delivered

A top-rung recon settled the automation policy (verdicts A–D below); a
strict build-neutral-gated *deterministic-smell* sweep then ran across
the non-fragile files. **66 `rw→simp only` / `unfold→grind only`
collapses landed** (slice 1 combinatorial-core 5; slice 2 Jacobs 15;
slice 3 BodyBar 31; slice 4 matroid/pebble 15), each per-file
4-run-median build-neutral and warning-clean. Three defeq-fragility
shapes surfaced and were reverted cleanly (heartbeat timeout,
max-recursion depth, structure-projection auto-reduction) — all
consolidated in `TACTICS-GOLF.md` §7 as the reference for future
fragile-zone work. The `@[grind]`/`@[grind =]` annotation set resolves to
**∅** (a measured no-op), and no custom tactic cleared the
built-ins-first bar, so the phase added zero attributes and zero macros.

**Slice 5 (`Mathlib/` mirror files) — SKIP by policy.** The mirror
subtree holds lemmas *missing* from mathlib, kept copy-paste-ready as
upstream candidates (`DESIGN.md` *Mirror directory*); their tactic style
is a choice for the eventual mathlib PR, not an internal sweep — there is
no upstream proof to match, the mirror *is* the proposed form. 0
collapses by design.

**Slice 6 (`Molecular/` fragility zone) — DEFERRED** to the queued
**AUTOMATE-Z** phase (user decision 2026-07-22): ~351 four-plus-arg `rw`
chains + ~154 `change`/`show` sites across `AlgebraicInduction/` /
`RigidityMatrix/` / ScrewSpace-carrier files, default NO-GO under strict
build-neutrality. Not swept.

## Hand-off / next phase

Phase 36 is closed. **PIN is the next queued phase to open** (the 2-d
molecular conjecture via Jackson–Jordán 2008; ROADMAP *Queued
post-program phases*) — opening it starts with its own survey/planning
note. The deferred `Molecular/` fragility-zone sweep is queued as
**AUTOMATE-Z** (default NO-GO; the three fragility shapes catalogued in
`TACTICS-GOLF.md` §7 are its go-in reference — revert on sight, don't
fight).

## Decisions made during this phase

### Recon verdicts (settled; measured at `leanprover/lean4:v4.30.0-rc2`)
- **A. Annotation policy → ∅ (measured).** `grind only` ignores ambient
  `@[grind]`/`@[grind =]` tags (compiler-witnessed), so a global tag is a
  no-op for every landed proof; the explicit `grind only [Def]`
  unfold-hint is strictly better (local, deterministic, no retag drift).
  The `def` non-reducibility pin survives untouched (`@[expose]` ≠
  `@[reducible]`). → TACTICS-GOLF §1 / DESIGN.md *Predicates are `def`s*.
- **B. Build-time A/B gate → two recipes** (per-file for a local swap;
  whole-downstream-closure for a global attribute) →
  `notes/PERFORMANCE.md` *grind-adoption A/B recipes*. Recipe (ii)
  unexercised this phase (attribute set ∅).
- **C. Pilot build-neutral.** `Sparsity.lean` `unfold→grind only
  [IsTightOn]` collapses; hot 4-run median Δ≈0. The sweep is selective
  per-site — goal-shaping chains and arithmetic `have`s do not collapse.
- **D. No custom tactic.** The Sym2-subtype lift recurs once and is
  already a 2-line idiom (§5); nothing cleared the built-ins-first bar.
  No `CombinatorialRigidity/Tactics.lean`.

### Sweep results (settled; per-site detail in git + TACTICS-GOLF §7)
- **Slice 1** combinatorial-core: 5 collapses, all `Sparsity.lean`
  (`unfold IsTightOn [at h]; …; omega` → `grind only [IsTightOn]`); the
  other 5 files clean. Lesson: only the *closing* `unfold;…;omega` shape
  collapses reliably; goal-shaping `rw`-chains feeding a later term-mode
  step do not.
- **Slice 2** Jacobs cluster: 15 of 18. Discriminator refined to
  *closing* vs *goal-shaping* (not file identity); one collapse reused
  the mirror `Set.ncard_congr'`; the looping-simp (twice-mentioned-lemma)
  trap found.
- **Slice 3** BodyBar: 31 collapse, ~13 reverted. First `change`/`show`
  work — one root-cause fix (`GenericLift`, rw→simp beta-reduction); the
  `IsIndependent`/`IsInfinitesimallyRigid`-unfold sites confirmed
  load-bearing (§4). Two new fragility shapes: structure-projection
  auto-reduction; heartbeat timeout even outside `Molecular/`.
- **Slice 4** matroid/pebble: 15 of 19 tested. Third fragility shape
  (max-recursion depth); the duplicate-mention de-dup pattern (a `simp
  only` single mention closes a positional `rw` double-mention).

### Promoted to TACTICS-GOLF / DESIGN / PERFORMANCE
- *`grind only` ignores ambient `@[grind]`/`@[grind =]` tags; keep
  explicit `grind only [Def]` hints* → TACTICS-GOLF §1.
- *Predicates stay `def`; `@[expose]` ≠ `@[reducible]`, so no tactic
  auto-unfolds them* → DESIGN.md *Predicates are `def`s, not `abbrev`s*
  (section created).
- *grind-adoption A/B gate recipes* → `notes/PERFORMANCE.md`.
- *rw→simp collapse discriminator (closing vs goal-shaping), the
  duplicate-mention nuance (looping trap vs de-dup opportunity), and the
  three defeq-fragility shapes (structure-projection auto-reduction,
  heartbeat timeout, max-recursion depth), consolidated into one coherent
  subsection* → TACTICS-GOLF §7.

### Landed ahead of the recon (2026-07-21, user-initiated)
- **Two surviving `maxHeartbeats 400000` overrides removed (`Meet.lean`)
  → zero project-wide.** A targeted profile-then-fix, no policy change:
  the Phase-33 "diffuse, no single `whnf` site" comment was stale —
  `complementIso_smul_eq_extensor_join` was ~80% one `simp_all`, replaced
  with a goal-only `simp only […]` + `exact`; the other override's cost
  was extracted to the reusable `exteriorPower_map_two_extensor`. Both
  build at default. → TACTICS-GOLF §21.
