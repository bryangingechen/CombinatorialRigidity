# Phase 36 — Proof automation: `grind` adoption + tactic-smell sweep (AUTOMATE, post-program) (work log)

**Status:** in progress (opened 2026-07-21; recon-first).

Internals-only, **structural-edit style** — no new blueprint chapter, no
new mathematics. Every headline statement and its axiom profile is
unchanged; re-verify the `formalization.yaml` headlines at the three
standard axioms at close (Phase 31 precedent). Inserted ahead of the
queued **PIN** phase at the user's initiative; PIN stays queued.

## Current state

Next concrete commit: **commit 1, the recon/design-pass** (top rung /
fable — a design-settle that reverses a pinned convention, so it is out
of scope for a build agent). It settles the `grind`-adoption policy, the
build-time A/B gate, the custom-tactic decision, and runs a **measured
pilot** on non-fragile files. Deliverable: a written policy (into this
note's *Architectural choices* / *Decisions*, or a `notes/Phase36-design.md`
if the survey grows past ~1500 lines) **plus the pilot's build-time
numbers**, which gate every sweep after it and the fragility-zone
go/no-go. The recon itself has not been built yet.

**Landed ahead of the recon (2026-07-21, user-initiated).** The two surviving
`maxHeartbeats 400000` overrides in `Meet.lean` were removed as a standalone
internals fix (**not** part of the gated grind sweep — a targeted profile-then-fix,
no policy change), taking the project to **zero `maxHeartbeats` overrides
project-wide**. See *Decisions made* for the technique; the recon (commit 1)
remains the next planned step.

## Architectural choices made up front (user-adjudicated 2026-07-21)

1. **Single recon-first phase** (not split upfront). Commit 1 = the
   design/recon pass + measured pilot; the low-risk sweeps follow; the
   **molecular fragility-zone** tactic swaps
   (`Molecular/AlgebraicInduction/` esp. `CaseIII/` + `Theorem55.lean`,
   `Molecular/RigidityMatrix/`, any ScrewSpace-carrier edit — the
   coordinate-phase playbook's defeq-fragile zone) are **gated to a
   follow-on decided *after* the pilot numbers**, not committed to now.
2. **Strict build-time-neutral gate.** A change lands only if the
   affected build's 4-run median (`notes/PERFORMANCE.md` protocol) is
   neutral-or-better (≤ ~1–2% noise). Anything that regresses is
   reverted. Readability alone never buys a build-time regression. See
   the *global-attribute caveat* below — this gate is measured
   whole-build for any `@[grind]`/`@[simp]` attribute, per-file for a
   local tactic swap.
3. **Built-ins first.** Prefer tagging defs/lemmas for `grind`/`simp`
   and adding fused mirror lemmas over new tactics. Write a custom
   macro/tactic ONLY where the recon proves built-ins genuinely cannot
   cover a recurring hand-pattern.

## Why this phase — the tactic-landscape survey (2026-07-21)

Across 106 files / ~81k lines:

| Tactic | Uses | Note |
|---|---|---|
| `grind` | 28 | and **0** `@[grind]` attributes anywhere in-tree |
| `omega` | 2469 | heavily (and appropriately) adopted |
| `rw [` | 5071 | of which **240** are 4+-arg chains = one math step |
| `simp only` / `simp` | 1208 / 1928 | |
| `change` / `show` | 98 / 73 | **68 / 65** of these sit in `Molecular/` (the fragility zone) |
| `linarith` / `nlinarith` | 160 / 39 | `linear_combination` 5, `field_simp` 2, `gcongr` 8, `positivity` 10 |
| `maxHeartbeats` overrides | 0 | the two `Meet.lean` 400k caps removed 2026-07-21 ahead of the recon (see *Decisions*); **zero project-wide** |

The `grind` scarcity is **convention-driven, not accidental**:
`TACTICS-GOLF.md` §1 says *"We don't add annotations in this directory;
we pass lemmas as hints instead"* (stale "Archive directory" wording),
and `DESIGN.md` *Predicates are `def`s, not `abbrev`s* pins
`IsSparse/IsTight/IsLaman/IsKDof/IsMinimalKDof/edgesIn` as non-reducible
so `grind` cannot see through them. The recurring friction (grind/linarith
can't unfold our predicates → manual `refine ⟨?_,?_⟩` + `have h : <body>`
everywhere; `TACTICS-GOLF.md` §4) is a *direct consequence*. Reconsidering
`grind` therefore means reconsidering those conventions — a design-settle,
which is why commit 1 is a top-rung recon and not a sweep.

**Honest expectation to set for the coordinator** (so the phase doesn't
chase a doomed goal): under the strict gate the wins will concentrate on
the *deterministic* smells — collapsing the 240 multi-`rw` chains to
`simp` / fused mirror lemmas, and eliminating `change`/`show` — plus
*selective* `grind` tagging where measured neutral. A blanket
`omega → grind` swap will mostly be *rejected* by the gate (`omega` is
faster on pure arithmetic; `TACTICS-GOLF.md` §1 already says keep it).
`grind`'s value here is readability where it *replaces* a manual unfold +
multi-step closer, not raw closing power we lack.

## The recon/design-pass mandate (commit 1)

The recon (consult the pinned toolchain's Lean source where useful — the
local elan toolchain for `leanprover/lean4:v4.30.0-rc2`) must deliver, in
one docs commit:

- **A. `grind` maturity + annotation policy at v4.30.0-rc2.**
  - Confirm `grind` is stable/appropriate at the pinned toolchain (it is
    an rc; check for known perf/soundness caveats that touch our goals).
  - Decide the **`@[grind]` def-tag set** from measurement. Candidates:
    `IsSparse`, `IsTight`, `IsTightOn`, `IsLaman` (`Sparsity.lean` /
    `Laman.lean`); `edgesIn` (`EdgesIn.lean`); `IsInfinitesimallyRigid`
    (`Framework.lean`); `IsKDof`, `IsMinimalKDof` (`Molecular/Deficiency.lean`);
    `Graph.IsSparse`/`Graph.IsTight` (`BodyBar/TreePacking.lean`). Note:
    `grind only [IsTightOn]` (passing the def name as a *hint*) already
    works (`TACTICS-GOLF.md` §4) — the question is whether the *global*
    `@[grind]` attribute is a net win vs. per-call hints.
  - Decide the **`@[grind =]` equation-lemma set** (project simp/rewrite
    lemmas worth exposing to E-matching); derive from `grind?` suggestions
    on real goals, not guesswork. Candidates to probe: the `mem_edgesIn`
    family, `edgesIn_univ`, `rigidityMap_apply`, `Set.ncard`↔`Finset.card`
    bridges.
  - Confirm compatibility with `DESIGN.md` *Predicates are `def`s* —
    tagging `@[grind]` does **not** change a def's reducibility for other
    tactics, so the pin survives; state this explicitly and update the
    stale `TACTICS-GOLF.md` §1 "no annotations" note + `DESIGN.md` if the
    policy flips.
- **B. Build-time A/B gate (make the strict gate operational).** Pin the
  measurement recipe (reuse `notes/PERFORMANCE.md`'s 4-run median). **The
  global-attribute caveat is the crux:** `attribute [grind] Foo` is a
  *global* attribute — it changes E-matching for **every** downstream
  proof that runs `grind`, so its build-time impact must be measured at
  the **whole-downstream-closure** level, not one file. A local `rw → simp`
  swap in one proof is measured per-file. Write both recipes down.
- **C. The measured pilot.** Apply the candidate policy to 1–2
  representative **non-fragile** files (candidates: `Sparsity.lean`,
  `Laman.lean`, `Henneberg.lean`, or a `BodyBar/` file) — tag defs, swap
  select closers to `grind`, collapse `rw`-chains — and **report the
  build-time / LoC / readability deltas**. These numbers gate the mass
  sweep and the fragility-zone go/no-go. This is the de-risking step: it
  tells us whether `grind` tagging is neutral before we touch the corpus.
- **D. Custom-tactic decision (built-ins first).** For each recurring
  hand-pattern, decide *covered-by-a-tag/mirror* vs *needs-a-macro*:
  - Sym2-subtype lift (`congrArg (Sym2.map Subtype.val)`; `TACTICS-GOLF.md`
    §5) — the strongest macro candidate (a ~6-line pattern that recurs).
  - Predicate-destructure (`refine ⟨?_,?_⟩` opener for our defs) — likely
    subsumed by the `@[grind]` def-tag; confirm and prefer the tag.
  - Cardinality/coercion bridges — likely a fused mirror lemma, not a
    tactic. Output a concrete list of what (if anything) gets written.
- **E. Sweep decomposition for the coordinator.** Produce the ordered,
  buildable sweep-slice list with **exact file targets**, each rated
  S/P/B, with the fragility zone explicitly marked **gated/deferred**
  pending the pilot. This is the artifact that lets subsequent slices
  dispatch at S=1 (sonnet where non-fragile & mechanical; opus-minimum in
  the fragility zone if it is later admitted).

## Lemma / work checklist (provisional — the recon's step E refines this)

- [ ] **commit 1** — recon/design-pass: A–E above (top rung / fable).
- [ ] **rw-chain sweep, non-fragile** — collapse 4+-arg `rw` chains to
      `simp` / fused mirror lemmas outside `Molecular/` (the 240 total,
      minus the fragility zone). Deterministic; per-file strict gate.
- [ ] **change/show sweep, non-fragile** — eliminate `change`/`show`
      outside `Molecular/` (≈33 of the 171 sit outside it) via simp
      lemmas / grind-unfold.
- [ ] **grind adoption, non-fragile** — apply the settled A-policy
      (def-tags + `@[grind =]` set) to non-fragile files; each attribute
      addition measured whole-build, kept only if neutral.
- [ ] **custom tactic(s)** — only those D greenlit (expected: at most the
      Sym2-lift macro). New file `CombinatorialRigidity/Tactics.lean` if any.
- [ ] **fragility-zone decision** — after the pilot, decide GO/NO-GO on
      molecular tactic swaps; if GO, a gated set of opus-minimum slices
      (or defer to a Phase 37). Surface the decision + estimate to the user.
- [ ] **close** — re-verify `formalization.yaml` headlines at the three
      standard axioms (`#print axioms`); doc sweep (TACTICS-GOLF §1 /
      DESIGN.md policy text); ROADMAP row → ✓.

## Blockers / open questions

- Does the global `@[grind]` attribute pay for itself whole-build under
  the strict gate? (The pilot answers this — it is the phase's pivot.)
- Is the fragility zone admissible at all under strict build-neutrality,
  or does its defeq-fragility make even neutral `grind` swaps too risky?
  (Decide after the pilot; default NO-GO.)

## Hand-off / next phase

The next concrete commit is **commit 1, the recon/design-pass** (A–E
above). Dispatch via `/coordinate-phase 36`: it is a top-rung
(`recon-fable`) read-plus-design-pass commit that settles policy + runs
the pilot + writes the sweep decomposition; it is NOT a build. Everything
downstream is gated on its pilot numbers. When Phase 36 closes, the
queued **PIN** phase is next to open.

## Decisions made during this phase

### Phase-local choices and proof techniques
- **The two surviving `maxHeartbeats 400000` overrides (`Meet.lean`) removed → zero
  project-wide** (2026-07-21, ahead of the recon, user-initiated; separate from the gated
  grind sweep). In-context profiling (`trace.profiler`) found the Phase-33 "diffuse, no single
  `whnf` site" comment **stale**: `complementIso_smul_eq_extensor_join` was ~80 % one `have`
  closed by `simp_all` over the big `Ω`/`Φ`/`hkills` carrier context — replaced with a goal-only
  `simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]` + `exact`.
  `complementIso_extensor_mem_range_map_subtype`'s largest cost was a context-free `have`
  extracted to the reusable top-level `exteriorPower_map_two_extensor`. Both then build at
  default; module build time neutral. Technique → TACTICS-GOLF § 21.

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN
- *`simp_all` in a big-carrier-hypothesis proof is a heartbeat multiplier; use goal-only `simp
  only` + `Fin.forall_fin_two` + `exact`, and extract context-free heavy `have`s to top level* →
  TACTICS-GOLF § 21 / FRICTION [resolved].
