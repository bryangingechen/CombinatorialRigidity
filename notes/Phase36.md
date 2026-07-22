# Phase 36 — Proof automation: `grind` adoption + tactic-smell sweep (AUTOMATE, post-program) (work log)

**Status:** in progress (opened 2026-07-21; commit 1 recon/design-pass landed
2026-07-22; commit 2 / slice 1 landed 2026-07-22; commit 3 / slice 2 landed
2026-07-22; commit 4 / slice 3 landed 2026-07-22).

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

**Slice 1 (combinatorial-core sweep) landed 2026-07-22.** Result: **5
collapses, all in `Sparsity.lean`; the other 5 files are already clean**
(swept, 0 sites). Per-file detail in the checklist below and the *Slice 1
sweep results* decision entry.

**Slice 2 (Jacobs cluster rw-chain sweep) landed 2026-07-22.** Result: **15
of 18 rw-chain candidates collapsed** — much higher yield than slice 1's
non-`Sparsity` files, because the discriminator is "closing" vs
"goal-shaping" shape, not file identity (see *Slice 2 sweep results*
below). Zero `unfold` sites found in any of the four files (the
`unfold X; …; omega` → `grind only [X]` shape slice 1 found doesn't occur
here at all).

**Slice 3 (BodyBar rw + change/show sweep) landed 2026-07-22.** Result: **31
sites collapsed** across the six files (`TreePacking` 9, `GenericLift` 6
rw + 2 `show` + 1 `change` = 9, `TayTheorem` 3, `KFrame` 9, `BodyHinge` 1,
`Framework` 0 — already clean), **~13 reverted** on a failed real `lake build`
(functional mismatches, not fragility, except two heartbeat-timeout fragility
flags in `TayTheorem` — see *Slice 3 sweep results*). First `change`/`show`
elimination of the phase: one genuine root-cause fix in `GenericLift`
(rw→simp beta-reduction removed the need for a `change`); the two
`IsInfinitesimallyRigid`/`IsIndependent`-unfolding `change` sites in
`GenericLift`/`TayTheorem` confirmed **load-bearing** (the established
def-opacity idiom, not a smell). Next concrete commit: **slice 4 —
matroid/pebble rw-chain sweep** (see the *Lemma / work checklist*).

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
- [x] **slice 1 — combinatorial-core sweep (S).** LANDED 2026-07-22.
      `Sparsity`: 5 collapses (`unfold IsTightOn [at h]; …; omega` →
      `grind only [IsTightOn]`, the 2 pilot sites plus 3 more found by
      the same pattern-grep: `IsTightOn.union_inter`,
      `IsSparse.exists_isTightOn_of_insert_not_sparse`,
      `IsSparse.no_isTightOn_excluding_three_neighbors`,
      `IsSparse.contradiction_three_pair`, `IsTightOn.union_with_bonus`).
      Build-neutral (4-run hot median: user 7.11s→7.19s, wall 3.87s→3.95s,
      both sub-1s/noise). `Laman`/`Henneberg`/`EdgesIn`/`TrivialMotions`/
      `HennebergReverse`: swept, **0 sites** — every 4+-arg `rw`-chain and
      `unfold`+goal-shaping candidate tested (edit + real `lake build`,
      not just `lean_multi_attempt`) either failed to collapse (unsolved
      goals / type mismatch against a later `exact`) or was structurally
      load-bearing for a following `refine`/`exact`. See *Decisions made*.
- [x] **slice 2 — Jacobs cluster rw-chain sweep (S).** LANDED 2026-07-22.
      `JacobsZeroExtension`: 11 candidates → **9 collapsed** (7
      `rw […]`→`simp only […]` swaps on closing chains, plus 2 sites — the
      duplicated `hB_card` proof in two theorems — replaced by the
      existing mirror lemma `Set.ncard_congr'` instead of the
      `Nat.card_congr`/`Nat.card_coe_set_eq` round-trip), 2 left
      load-bearing (a goal-shaping `rw … at heB` feeding a later `exact`;
      an `ext u; rw […]` that closes but loops `simp` on a
      twice-mentioned lemma pair — see TACTICS-GOLF §7 addendum).
      `JacobsCounting`: 4 candidates → **3 collapsed** (folded into 2
      edits: two `rw … at h1` calls merged into one `simp only […] at h1`;
      one closing `rw` → `simp only`), 1 left (a `finsum_mem_congr`
      chain whose `simp` normal form unfolds `ncard` into nested
      `finsum`s instead of matching the rewrite target).
      `Jacobs`: 2 candidates → **2 collapsed**. `JacobsDegreeOne`: 1
      candidate → **1 collapsed**. **Zero `unfold` sites** in any of the
      four files (no `unfold X; …; omega` shape here at all — the sweep
      instruction's first playbook item had nothing to act on). Build-
      neutral on all four files (4-run hot user-time medians, each
      within noise): JacobsZeroExtension 18.41s→17.33s; JacobsCounting
      6.20s→6.27s; Jacobs 1.32s→1.30s; JacobsDegreeOne 3.97s→3.94s.
      Warning-clean, `lake lint` clean. See *Slice 2 sweep results*.
- [x] **slice 3 — BodyBar rw + change/show sweep (P).** LANDED 2026-07-22.
      `TreePacking`: 9 collapsed (`unfold`/multi-arg `rw`-chains closing a
      `have` or the tail of a lemma → `simp only [...]`), 2 left (a
      twice-mentioned-lemma-pair chain — the established looping-`simp`
      trap, same shape as `GenericLift`'s below — and a nested `by rw […]`
      inside an outer chain, too risky to disentangle). `GenericLift`: 6
      rw-chain collapsed + 2 `show` removed (the `funext i; show q (…) = _;
      rw […]` idiom — the `show` was redundant once `rw` ran; `simp only`
      wasn't tried since the `rw` after it stayed a `rw`) + 1 `change`
      eliminated via a **root-cause fix**, not a swap: the earlier `rw
      [hφ, …, hg_def, …]` (unfolding a `set`-bound row function) left an
      un-reduced beta-redex that the `change` existed only to peel off;
      converting that `rw` to `simp only` (which beta-reduces) made the
      `change` unnecessary and let the following two `rw` chains merge into
      one. 2 rw-chain reverted — a new failure mode, **structure-projection
      auto-reduction**: `simp only [hpe, …]` where `hpe`'s LHS mentions a
      structure projection (`.placement`/`.rigidityRow`) fails because simp
      auto-iota-reduces the projection to its constructor argument
      (`stdPlacement …`/`mapPlacement`-unfolded form) *before* trying the
      lemma list, so the lemma's un-reduced-projection LHS never matches —
      `rw` has no such auto-reduction and matches the syntactic term as
      written. 1 duplicate-lemma-pair chain left untested (known trap).
      `TayTheorem`: 3 collapsed (an `if_neg` branch, two identical `hcard`
      `Set.ncard_image_of_injective` sites), **7 reverted**, of which
      **2 are heartbeat-timeout fragility flags** — `stdFramework_finrank_range`
      and `isIndependent_iff_linearIndependent_rigidityRow`, both chains
      through `LinearMap.finrank_range_dualMap_eq_finrank_range` /
      `span_range_rigidityRow` — converting either to `simp only` triggered
      `(deterministic) timeout at whnf` at the *default* 200000 heartbeats;
      reverted immediately per the revert-on-fragility rule, not fought.
      The other 5 reverts were plain functional mismatches (unsolved goals /
      `simp` made no progress), not fragility. Both `change` sites
      (`IsInfinitesimallyRigid`/`IsIndependent` unfolds) confirmed
      load-bearing, same idiom as `GenericLift`. `KFrame`: 9 collapsed
      (incl. the `forestEval` `if_pos`/`if_neg` branches and an
      `hentry_inj` chain with a duplicate lemma merged to one mention,
      safe under `simp only`'s repetition-tolerant semantics), 2 reverted
      (a `finrank`-span chain: "simp made no progress"; an `hcomp` chain:
      `Function.uncurry_apply_pair` didn't match `simp`'s normal form for a
      variable-pair argument the way `rw` did). `BodyHinge`: 1 collapsed
      (the `edgeMultiply_edgeSet_ncard` tail), 0 `change`/`show` sites.
      `Framework`: swept, **0 sites** — the file is mostly definitions plus
      one small numeral lemma whose `rw` is goal-shaping. All five touched
      files build-neutral (4-run hot user-time medians, deltas ≤ ~1.6s,
      within the sub-5s noise floor) and warning-clean; `lake build`
      (full project) + `lake lint` both green. See *Slice 3 sweep results*.
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

The next concrete commit is **slice 4 (matroid/pebble rw-chain sweep)** —
`MatroidIdentification` (8), `RigidityMatroid` (1), `PebbleGame/Basic` (5),
`PebbleGame/Exec` (1), `Search/DFS` (4), `HennebergRigidity` (4); dispatch at
S=1 (Sonnet), rated **S** (mechanical — these are combinatorial/pebble-game
files, not the rigidity-matrix-adjacent body-bar track slice 3 covered, so
the lighter fragility posture of slices 1–2 applies). Per-file
build-neutral-gate + real-`lake build`-confirms-every-collapse discipline,
same as slices 1–3. Apply the closing-vs-goal-shaping discriminator
(TACTICS-GOLF §7 addendum) — test a rw-chain candidate only if it's the
*entire* tactic body or immediately followed only by a closer; skip a
candidate feeding a later `refine`/`exact`/`rw … at h`. **Two new failure
modes slice 3 found, worth checking for here too** (TACTICS-GOLF §7 should
carry both by the time slice 4 starts — promote them in this commit if not
already done): (1) **structure-projection auto-reduction** — a `simp only`
whose lemma list mentions a structure-projection LHS (`.field`) can fail
where the analogous `rw` succeeds, because simp auto-iota-reduces the
projection before matching; (2) a `finrank_range_dualMap`/`span_range_row`-
shaped chain can be a genuine **heartbeat-timeout fragility** site under
`simp only` even outside `Molecular/` — revert immediately, don't fight it,
per the standing rule. `change`/`show` elimination is now a proven pattern
(one root-cause fix landed in slice 3) but the `IsIndependent`/
`IsInfinitesimallyRigid`-unfold sites are confirmed load-bearing wherever
they recur — don't re-attempt those specific two defs' `change` sites in
slice 4's files without a new angle. When Phase 36 closes, the queued
**PIN** phase is next to open.

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
- **Slice 1 sweep results (2026-07-22).** Landed the pilot's 2
  `Sparsity.lean` collapses (they had been measured-then-reverted in
  commit 1) plus 3 more found by grepping the same `unfold IsTightOn
  [at h]; …; omega` shape file-wide: `IsTightOn.union_inter`,
  `IsSparse.exists_isTightOn_of_insert_not_sparse`,
  `IsSparse.no_isTightOn_excluding_three_neighbors`,
  `IsTightOn.union_with_bonus`, `IsSparse.contradiction_three_pair` — 5
  total, build-neutral (4-run hot median, user 7.11s→7.19s). The other 5
  files' candidate 4+-arg `rw`-chains (`Henneberg` ×2, `EdgesIn` ×1,
  `HennebergReverse` ×2) all failed a real `lake build` when swapped for
  `simp`/`simp only` with the same lemma list: `simp`'s normal form
  doesn't match the specific goal shape a later `refine`/`exact` expects.
  `TrivialMotions`/`Laman` had no candidates at all (already
  grind-idiomatic). Net: **only the `unfold X; …; omega`→`grind only [X]`
  shape collapses reliably; goal-shaping `rw`-chains feeding a later
  term-mode step generally don't** — confirms the pilot's own "one `have`
  + one `rw`-chain don't collapse" finding generalizes, not an accident
  of those two sites. → TACTICS-GOLF §7 (`lean_multi_attempt` false-positive
  caveat: 3 of these "successes" only surfaced as failures under a real
  `lake build`).
- **Slice 2 sweep results (2026-07-22).** Jacobs cluster (`JacobsZeroExtension`
  11, `JacobsCounting` 4, `Jacobs` 2, `JacobsDegreeOne` 1 = 18 candidates):
  **15 collapsed**, only 3 left load-bearing — the opposite yield from
  slice 1's non-`Sparsity` files. Refines (doesn't contradict) slice 1's
  finding: the real discriminator is *closing* (entire tactic body, or
  immediately followed only by a closer) vs *goal-shaping* (feeds a later
  `refine`/`exact`/`rw … at h`) — slice 1's failures were all goal-shaping,
  its wins all closing; slice 2's file set just happened to have far more
  closing-shaped one-`have` proofs. One collapse used an existing mirror
  lemma (`Set.ncard_congr'`) instead of `simp`, replacing a
  `Nat.card_congr`/`Nat.card_coe_set_eq` round-trip. New failure mode: a
  closing chain can still fail if it mentions a lemma or lemma-pair twice
  (`simp` loops to a fixpoint instead of `rw`'s one-shot positional
  application). Zero `unfold` sites in any of the four files. TACTICS-GOLF
  §7 addendum has the discriminator + the looping-simp trap.
- **Slice 3 sweep results (2026-07-22).** BodyBar track (`TreePacking`,
  `GenericLift`, `TayTheorem`, `KFrame`, `BodyHinge`, `Framework`): **31
  sites collapsed, ~13 reverted**, per-file counts in the checklist above.
  Two **new** failure modes beyond slice 2's duplicate-lemma trap: (1)
  **structure-projection auto-reduction** — `simp only [h, …]` fails where
  `rw [h, …]` succeeds when `h`'s LHS mentions a structure projection
  (`.placement`/`.rigidityRow`), because simp auto-iota-reduces the
  projection to its constructor argument *before* trying the lemma list, so
  the un-reduced-projection pattern never matches (2 sites, `GenericLift`);
  (2) a `finrank_range_dualMap`/`span_range_rigidityRow`-shaped chain is a
  genuine **heartbeat-timeout fragility** site under `simp only` *outside*
  `Molecular/` (2 sites, `TayTheorem`) — reverted per the standing
  revert-on-fragility rule, not fought. First `change`/`show` elimination
  of the phase: one **root-cause** fix (`GenericLift` — converting the `rw`
  that *produced* an un-reduced beta-redex to `simp only`, which
  beta-reduces, removed the need for the `change` that existed only to
  peel the redex off, rather than swapping the `change` itself); the
  `IsIndependent`/`IsInfinitesimallyRigid`-unfold `change` sites (3 more,
  `GenericLift`+`TayTheorem`) are **load-bearing** — the established
  def-opacity idiom (TACTICS-GOLF §4), not a smell to remove. All five
  touched files build-neutral, warning-clean; full-project `lake build` +
  `lake lint` green. → TACTICS-GOLF §7 addendum (the two new traps).

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
- *rw-chain→simp collapse discriminator refined to closing-vs-goal-shaping
  (not file-specific), plus the twice-mentioned-lemma looping-simp trap* →
  TACTICS-GOLF §7 addendum.
- *Two new rw→simp-only failure modes: structure-projection auto-reduction
  (simp iota-reduces a projection before the lemma list can match it), and
  a `finrank_range_dualMap`/`span_range_rigidityRow`-shaped chain as a
  heartbeat-timeout fragility site even outside `Molecular/`* →
  TACTICS-GOLF §7 addendum.

### Landed ahead of the recon (2026-07-21, user-initiated)
- **The two surviving `maxHeartbeats 400000` overrides (`Meet.lean`) removed → zero
  project-wide** (separate from the gated grind sweep; a targeted profile-then-fix, no
  policy change). In-context profiling found the Phase-33 "diffuse, no single `whnf` site"
  comment **stale**: `complementIso_smul_eq_extensor_join` was ~80 % one `have` closed by
  `simp_all` over the big carrier context — replaced with a goal-only `simp only
  [Fin.forall_fin_two, …]` + `exact`; `complementIso_extensor_mem_range_map_subtype`'s
  largest cost was extracted to the reusable `exteriorPower_map_two_extensor`. Both build
  at default; module time neutral. Technique → TACTICS-GOLF § 21.
