# Phase 36 — Proof automation: `grind` adoption + tactic-smell sweep (AUTOMATE, post-program) (work log)

**Status:** in progress (opened 2026-07-21; commit 1 recon/design-pass landed 2026-07-22).

Internals-only, **structural-edit style** — no new blueprint chapter, no
new mathematics. Every headline statement and its axiom profile is
unchanged; re-verify the `formalization.yaml` headlines at the three
standard axioms at close (Phase 31 precedent). Inserted ahead of the
queued **PIN** phase at the user's initiative; PIN stays queued.

## Current state

Commit 1 (the recon/design-pass) **landed**: the `grind`-adoption policy,
the build-time A/B gate, the custom-tactic decision, and the measured
pilot are all settled (see *Recon verdicts* below). **Headline result: the
global `@[grind]`/`@[grind =]` annotation policy resolves to the empty set
— it is a measured no-op, not a judgement call** (see verdict A). The
phase's remaining work is therefore the *deterministic-smell* sweep only
(rw-chain collapse + `change`/`show` elimination + selective
`grind only [Def]` unfold-hint collapse), all per-file-gated, plus the
gated fragility-zone go/no-go.

Next concrete commit: **slice 1 — combinatorial-core sweep** (see the
*Lemma / work checklist*): a Sonnet-appropriate, per-file-gated mechanical
pass over `Sparsity`/`Laman`/`Henneberg`/`EdgesIn`/`TrivialMotions`/
`HennebergReverse`. The pilot already verified two `Sparsity.lean`
collapse sites and one non-collapsible site (hand-off list below).

## Architectural choices made up front (user-adjudicated 2026-07-21)

1. **Single recon-first phase** (not split upfront). Commit 1 = the
   design/recon pass + measured pilot (done); the low-risk sweeps follow;
   the **molecular fragility-zone** tactic swaps
   (`Molecular/AlgebraicInduction/` esp. `CaseIII/` + `Theorem55.lean`,
   `Molecular/RigidityMatrix/`, any ScrewSpace-carrier edit — the
   coordinate-phase playbook's defeq-fragile zone) are **gated to a
   follow-on decided *after* the pilot numbers** (default NO-GO; see E-6).
2. **Strict build-time-neutral gate.** A change lands only if the
   affected build's 4-run median (`notes/PERFORMANCE.md` protocol) is
   neutral-or-better (≤ ~1–2% noise, and sub-5s deltas are noise). Anything
   that regresses is reverted. Readability alone never buys a build-time
   regression. Per-file for a local tactic swap; whole-downstream-closure
   for any global attribute (moot this phase — attribute set is ∅).
3. **Built-ins first.** Prefer explicit `grind only [Def]` / `simp` hints
   and fused mirror lemmas over new tactics. (Custom-tactic verdict D: none.)

## Recon verdicts (commit 1, 2026-07-22)

Measured at the pinned toolchain `leanprover/lean4:v4.30.0-rc2`. Full
measurement record + the compiler-witness probes are in *Decisions made*;
cross-cutting rules were promoted (see *Promoted to …*).

- **A. `grind` maturity + annotation policy → tag set is ∅ (measured).**
  `grind` is stable and fully-featured at v4.30.0-rc2 (complete `@[grind]`
  modifier syntax — `=`, `_=_`, `←`, `→`, `cases`, `intro`, `ext`, `inj`,
  `norm`, …; proofs are kernel-checked, no soundness caveat). **The
  `@[grind]` def-tag set and the `@[grind =]` equation-lemma set are both
  EMPTY**, decided from measurement, because the project's landed idiom is
  `grind only` (TACTICS-GOLF §1), and **`grind only` ignores ambient
  `@[grind]`/`@[grind =]` attributes** (compiler-witnessed). A global tag
  is therefore a *no-op* for every landed proof; only the 12 bare-`grind`
  sites could ever see it, and tagging them globally would incur the
  whole-downstream E-matching cost for a readability change we can get
  locally. The explicit `grind only [Def]` unfold-hint (already at
  `Sparsity.lean:421/497/525`) is strictly better: local, deterministic,
  no mathlib-retag drift, faster. Also measured: a *bare* `@[grind]` on a
  `Prop`-def does not even reproduce the `grind only [Def]` unfold, and a
  `@[grind =]` tag on the def fails to unfold it at all. **The `def`
  non-reducibility pin (`DESIGN.md`) SURVIVES untouched** — tagging never
  changes reducibility, and `@[expose]` (which the predicates carry)
  exposes the body for module-*import* but is not `@[reducible]`, so
  tactics still won't auto-unfold. Verdict: **CONFIRM the no-annotations
  convention, now measured** (previously a stale "Archive directory"
  hand-wave). TACTICS-GOLF §1 wording updated; the dangling
  `DESIGN.md "Predicates as def's"` cross-reference was created.
- **B. Build-time A/B gate — two recipes, now in `notes/PERFORMANCE.md`**
  (*grind-adoption A/B recipes*): (i) **per-file** for a local `rw→simp` /
  `unfold→grind only [Def]` swap — 4-run median of `lake build <module>`;
  (ii) **whole-downstream-closure** for any global `attribute [grind] Foo`
  — build every transitive importer that runs `grind`, because the tag
  changes E-matching for all of them. Recipe (ii) is documented but
  *unexercised this phase* (tag set is ∅); it is the gate any future
  reconsideration of tagging must pass.
- **C. Measured pilot (`Sparsity.lean`, non-fragile) → build-NEUTRAL.**
  Two `unfold X; …; omega`→`grind only [IsTightOn]` collapses landed and
  verified (lines 447–448 → one line; 493). Hot 4-run medians (cache
  confound controlled by re-measuring baseline hot): baseline wall 3.88s /
  user 7.05s; treatment wall 3.70s / user 7.04s → **Δ ≈ 0, neutral**. LoC
  −1; readability net-positive (documented TACTICS-GOLF §4 pattern).
  **Negative findings that shape the sweep:** (1) a third candidate (the
  `insert w S` size `have`, line 520) did *not* collapse — `grind` cannot
  do the `card_insert` + `mul_add` arithmetic the explicit `rw […]; omega`
  does; (2) the sole 4+-arg `rw`-chain in the file (1108) is a legitimate
  targeted `rw […] at h` (membership manipulation), not a `simp` candidate.
  **The sweep is selective per-site, NOT bulk-mechanical.**
- **D. Custom tactic → NONE.** The Sym2-subtype lift
  (`congrArg (Sym2.map Subtype.val)`; the Phase36-open "strongest macro
  candidate") occurs **once** as a live proof step (`HennebergReverse.lean:112`)
  and is already a tidy 2-line idiom (TACTICS-GOLF §5) — not a recurring
  6-line hand-pattern. Predicate-destructure is subsumed by `grind only [Def]`
  / `refine ⟨?_,?_⟩`; cardinality/coercion bridges are fused mirror lemmas
  (mirror-first practice). No `CombinatorialRigidity/Tactics.lean` is created.
- **E. Sweep decomposition** — the *Lemma / work checklist* below.

## Why this phase — the tactic-landscape survey (counts re-measured 2026-07-22)

Across 108 files / ~81k lines (corrects the Phase-open estimates):

| Tactic | Uses | Note |
|---|---|---|
| `grind` | 28 tactic uses (16 `grind only`, 12 bare; +4 comment mentions) | and **0** `@[grind]` attributes in-tree |
| `omega` | 2483 | heavily (and appropriately) adopted |
| `rw [` 4+-arg chains | **444 lines**, of which **351 (79%) in `Molecular/`** | the fragility zone; **93 non-fragile** (~18 in `Mathlib/` mirrors → ~75 project) |
| `change` / `show` (tactic-pos) | 123 / 73 | **89 / 65 in `Molecular/`**; **~42 non-fragile** total |
| `maxHeartbeats` overrides | **0** | (5 residual *comment* mentions of the removal; zero real `set_option`) |

The decisive re-measured fact: **the deterministic smells are ~79%
inside the molecular fragility zone**, so the non-fragile sweep is
genuinely small (~75 rw-chains + ~42 change/show, minus the selective
non-smell sites C found). The `grind`-scarcity is convention-driven
(`grind only` idiom) and, per verdict A, correctly stays that way.

## Lemma / work checklist (step-E sweep decomposition)

Each slice is **per-file build-neutral-gated** (4-run median; revert on
regression) and **warning-clean**. The grind-tagging slice and the
custom-tactic slice from the Phase-open provisional plan are **removed**
(verdicts A / D). Ratings: S = Sonnet-appropriate mechanical; P = probe
non-fragility per file first; B = opus-minimum, gated.

- [x] **commit 1** — recon/design-pass: A–E (top rung / fable). LANDED 2026-07-22.
- [ ] **slice 1 — combinatorial-core sweep (S).** `Sparsity`, `Laman`,
      `Henneberg`, `EdgesIn`, `TrivialMotions`, `HennebergReverse`.
      Collapse `unfold X; …; omega`→`grind only [X]` where it *builds*
      (per-site, not blind); collapse genuine multi-`rw` chains to
      `simp`/fused mirror lemmas. **Pilot hand-off:** `Sparsity.lean`
      447–448 and 493 collapse (verified); line 520 (`insert w S` size
      `have`) and the 1108 `rw`-chain do **not** — leave them.
- [ ] **slice 2 — Jacobs cluster rw-chain sweep (S).** `JacobsZeroExtension`
      (11), `JacobsCounting` (4), `Jacobs` (2), `JacobsDegreeOne` (1).
      Multigraph files, non-fragile.
- [ ] **slice 3 — BodyBar rw + change/show sweep (P).** `BodyBar/TreePacking`
      (7), `GenericLift` (7), `TayTheorem` (5), `KFrame` (3), `BodyHinge`,
      `Framework`. Body-bar/Tay track — probe each file's fragility
      (rigidity-matrix-adjacent constructions) before swapping.
- [ ] **slice 4 — matroid/pebble rw-chain sweep (S).** `MatroidIdentification`
      (8), `RigidityMatroid` (1), `PebbleGame/Basic` (5), `PebbleGame/Exec`
      (1), `Search/DFS` (4), `HennebergRigidity` (4).
- [ ] **slice 5 — `Mathlib/` mirror files (P, likely SKIP).** `Rank` (6),
      `Dimension/Constructions` (3), `LinearIndependent/Basic` (2), etc.
      Collapsing a mirror's `rw`-chain **diverges from the upstream
      copy-paste goal** (DESIGN.md *Mirror directory*) — default LEAVE
      unless the collapse matches an upstream form.
- [ ] **slice 6 — fragility zone (`Molecular/`) — GATED / DEFERRED (B).**
      ~351 rw + ~154 change/show. Decide GO/NO-GO **after** slices 1–4
      land clean. **Default NO-GO** under strict build-neutrality
      (defeq-fragile; coordinate-phase playbook). If GO: a gated set of
      opus-minimum per-file slices (or defer to a Phase 37). Surface the
      decision + estimate to the user.
- [ ] **close** — re-verify `formalization.yaml` headlines at the three
      standard axioms (`#print axioms`); ROADMAP row → ✓.

## Blockers / open questions

- **Answered by the recon:** global `@[grind]` never pays under our
  `grind only` convention (it is ignored) — the phase's original pivot
  question is resolved negatively; there is no tagging slice.
- **Open (decide after slices 1–4):** is the fragility zone admissible at
  all under strict build-neutrality? Default NO-GO (slice 6).

## Hand-off / next phase

The next concrete commit is **slice 1 (combinatorial-core sweep)** —
dispatch at S=1 (Sonnet). It is a per-file-gated mechanical pass; the
pilot handed off the exact `Sparsity.lean` collapse/leave sites above.
When Phase 36 closes, the queued **PIN** phase is next to open.

## Decisions made during this phase

### Phase-local choices and proof techniques
- **`grind only` ignores ambient `@[grind]` attributes → the annotation
  policy is ∅** (verdict A, 2026-07-22). Compiler-witnessed at
  v4.30.0-rc2 (scratch probes, now deleted): with `edgesIn_univ` tagged
  `@[grind =]` but dropped from the `grind only […]` list, the goal fails;
  with `IsTightOn` tagged `@[grind]`, `grind only [derived-fact]` leaves
  `¬IsTightOn` opaque (full `grind` picks the tag up, but the project uses
  `grind only`). So a global tag helps no landed proof and only risks the
  whole-build E-matching cost. Keep explicit `grind only [Def]` unfold
  hints. The `def` non-reducibility pin is unaffected (`@[expose]` ≠
  `@[reducible]`). → TACTICS-GOLF §1 / DESIGN.md *Predicates are `def`s*.
- **Pilot build-neutral (verdict C, 2026-07-22).** `Sparsity.lean` two
  `unfold→grind only [IsTightOn]` collapses; hot 4-run median Δ≈0 (baseline
  user 7.05s / treatment 7.04s). The earlier "speedup" (wall 7.5s→3.7s) was
  pure OS-page-cache warming across the baseline run — controlled by
  re-measuring baseline hot. Cache confound = the standing PERFORMANCE.md
  caveat. Sweep is selective per-site (two collapse, one `have` + one
  `rw`-chain do not).
- **No custom tactic (verdict D).** Sym2-lift recurs once, already a
  2-line idiom; nothing clears the built-ins-first bar.
- **Survey drift corrected.** rw 4+-arg chains 444 (not 240), 79% in
  `Molecular/`; change/show 123/73 (tactic-pos); `maxHeartbeats` truly 0.

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN
- *`grind only` ignores ambient `@[grind]`/`@[grind =]` tags; global
  def/equation tags are a no-op under the project's `grind only` idiom —
  keep passing defs/lemmas as explicit `grind only [Def]` hints* →
  TACTICS-GOLF §1 (stale "Archive directory / no annotations" wording
  replaced with the measured rule).
- *Predicates (`IsSparse`/`IsTight`/`IsLaman`/…) stay `def` (not `abbrev`),
  and `@[expose]` ≠ `@[reducible]`, so no tactic auto-unfolds them; the
  reducibility trade-off + Phase-36 grind-tag confirmation* → DESIGN.md
  *Predicates are `def`s, not `abbrev`s* (section created; resolves the
  dangling TACTICS-GOLF §4 / phase-note cross-reference).
- *grind-adoption A/B gate: per-file recipe for a local swap;
  whole-downstream-closure recipe for a global attribute* →
  `notes/PERFORMANCE.md` *grind-adoption A/B recipes*.

### Landed ahead of the recon (2026-07-21, user-initiated)
- **The two surviving `maxHeartbeats 400000` overrides (`Meet.lean`) removed → zero
  project-wide** (separate from the gated grind sweep; a targeted profile-then-fix, no
  policy change). In-context profiling found the Phase-33 "diffuse, no single `whnf` site"
  comment **stale**: `complementIso_smul_eq_extensor_join` was ~80 % one `have` closed by
  `simp_all` over the big carrier context — replaced with a goal-only `simp only
  [Fin.forall_fin_two, …]` + `exact`; `complementIso_extensor_mem_range_map_subtype`'s
  largest cost was extracted to the reusable `exteriorPower_map_two_extensor`. Both build
  at default; module time neutral. Technique → TACTICS-GOLF § 21.
