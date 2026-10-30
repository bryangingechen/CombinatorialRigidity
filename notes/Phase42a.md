# Phase 42a — PD-RECON: does Phase 40's induction run in every `Pᵈ`? (work log)

**Status:** ✓ closed 2026-10-30 (opened 2026-10-29 with the PI, attended), a sub-phase of Phase
42, which stays in progress with no sub-phase open. Research only: no Lean, no blueprint. The route
is the PI's (R2's steps, the embedding as the base row), and the coverage's only new mathematics,
SHORT-CORE, is proved by hand at `d = 4` by its attack track (closed 2026-10-30,
`notes/attacks/short-core/state.md`). PD-STATE (42b) and PD-STABLE (42c) ran beside it, both
closed 2026-10-30. Next (*Hand-off*): which sub-phase opens as 42d goes to the PI. Plan and
decisions: `notes/Phase42-design.md`; evidence: `notes/Strata.md`.

## Current state

**Closed.** What the research settled, each with its home:
- **The step table** (design doc §2.1, 22 rows) and the route (§2.2, the PI's call in §1): R2's
  induction with Result 15's embedding as the base row; an outer induction on `d` is Tier 2's.
- **The tests** T1–T5 (§2.4; `Strata.md` Results 20–26) and the content range (§2.5): every graph
  built to carry a failing row's configuration attains, so the obstruction is the proof's.
- **The obligations** (§2.3): CERT holds at `d ≤ 6`, its open ears at `d ≥ 7` left to PD-STEPS;
  ONE-CLASS is Phase 40's (Result 27), so ONE-EAR leaves the coverage for GENERIC; SHORT's X3 holds
  for `k ≥ C(d − 1, 2) + 3`, and **SHORT-CORE** below it:
  - `d = 4`, `k = 3, 4, 5`: proved by hand (workbook S1–S21, S35), read by three readers.
  - `k ≥ 4` in every `d`, every `ρ` (S35); `k = 3` at `d = 5, 6` (S28–S33).
  - From `d = 5` on the coverage never needs the `k = 3` short row, nor row 15 (S52–S53, given
    CERT's open ears); so G1 (`k = 3`, `d ≥ 7`) is parked, its revival trigger CERT failing at
    some `d ≥ 7` (workbook S56).
- **The second read of rows 9 and 12** (§2.1): no gap; both need only CARRIER's restatements.

## Architectural choices made up front

- **Research rules.** `HARNESS.md` *Evidence* and *Reproducibility* bound the phase; SHORT-CORE,
  the one step that needed a new argument, was split off as an attack track (the PI, §1).
- **One home per kind.** The step table and verdicts live in the design doc §2; `Strata.md`'s
  Results are cited by number; SHORT-CORE's results by workbook S-number
  (`notes/attacks/short-core/workbook.md`).

## Lemma checklist

- [x] **The step table** (design doc §2.1): 22 rows over `main-component.tex` and `pencil.tex`.
- [x] **Phase 39's reduction in `Pᵈ`**: `d`-general for the bare and distinct conjuncts given
  CARRIER (row 19); route B's generic conjunct fails as written and is separable (row 22).
- [x] **The route verdict** (§2.2), taken by the PI (§1).
- [x] **The thresholds and the content range** (§2.5).
- [x] **T1, T2** (Results 20–21), **the content-range graphs** (Result 22), **T4** (Results 23,
  25), **T3** (Result 24, X3's range proved), **T5** (Result 26, Theorem S at `D` proved).
- [x] **A second read of rows 9 and 12** (§2.1): no gap.
- [x] **ONE-CLASS** (§2.3; Result 27, `oneclass.py`): ONE-EAR leaves the coverage.
- [x] **SHORT-CORE** (§2.3): the attack track, closed 2026-10-30 at its review 3 on the PI's word;
  `d = 4` proved by hand, and from `d = 5` on the `k = 3` row is never needed (workbook S53, S56).

## Blockers / open questions

- None. 42d opens at the PI's word (*Hand-off*).

## Hand-off / next phase

Phase 42 has no open sub-phase. **The next concrete task is putting 42d's open to the PI**: which
of PD-CARRIER, PD-STEPS and PD-COVERAGE (Phase 40's carrier, steps and coverage in `Pᵈ` on R2's
steps, design doc §3) opens first, toward Tier 1's `P⁴` theorem; PD-REDUCTION and PD-HEAD come
after. What 42a leaves them, each listed in design doc §3:
- **PD-STEPS:** the `Pᵈ` short-ear step, from SHORT-CORE's workbook (S56 lists what each `k` and
  `d` uses); `lem:deficiency-core-bound` at every `D ≥ 3` (row 17; S52 (iv) uses it, its Lean is
  pinned at `deficiency 3`); CERT's uniform `m`-gons and open ears at `d ≥ 7` (§2.3).
- **PD-COVERAGE:** Theorem S at `D` (§2.4 T5), ONE-CLASS (Result 27), and SHORT-CORE's S53 at
  `d ≥ 5`.
- **GENERIC**, deferred: ONE-EAR (the motive, a `Pᵈ` insertion lemma, X2) and route B (row 22).
- **Tier 2, parked:** SHORT-CORE's G1 (`notes/attacks/short-core/state.md`), only if CERT's open
  ears fail at some `d ≥ 7`.

## Decisions made during this phase

- The open's decisions, ONE-CLASS over ONE-EAR, the route, and SHORT-CORE's rulings are the PI's,
  verbatim in the design doc §1 and in SHORT-CORE's workbook (S25, S50, S56).
- The step table's rows are the four recon passes' readings, cited by row (design doc §2.1).
- One driver mode per test, so earlier figures do not move: `strata.py --content`, `--oneear`,
  `--orbit`, `--short`, `--coverage`; `oneclass.py`; SHORT-CORE's `drivers/` (`Strata.md`
  *Evidence*).
- The second reads ran as two parallel read-only recons, each briefed to refute (the PI, §1).
- Proved where possible, not read off a point: T4's one miss, T5's two reductions, ONE-CLASS and
  SHORT-CORE are proofs by hand, each checked by its driver.
