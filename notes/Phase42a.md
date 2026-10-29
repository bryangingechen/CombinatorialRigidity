# Phase 42a — PD-RECON: does Phase 40's induction run in every `Pᵈ`? (work log)

**Status:** in progress, opened 2026-10-29 with the PI, attended. Research only: no Lean, no
blueprint. The step table (design doc §2.1–§2.4) and the thresholds (§2.5) have landed. Next
concrete task: one `strata.py` mode with T1, T2 and the content-range graphs. The PI's defaults
for the sessions after it are the design doc's §1. Plan and decisions: `notes/Phase42-design.md`;
evidence: `notes/Strata.md`.

## Current state

**Next: T1, T2 and the content-range graphs (design doc §2.4, §2.5), one commit.** A new
`strata.py` mode with exact rank at a seeded point:
- **T1** checks row 5's two flat formulas at `d = 4` on the `--d4` population (R2's flat rank
  `10(n−1) + 3 − dim L(q)`, R1's base `10(n−1) − def[6]`).
- **T2** builds CERT's certificates at `d = 4, 5, 6` (closed `m`-gons for `m ≤ D_d`, the long ear
  at `k = D_d − 1`).
- **The content-range graphs** measure the pencil rank at `d = 4, 5, 6` against
  `D(n−1) − def[D]`: `θ(2, 2, k)`, `θ(2, 2, 2, k)`, diamond rings at `m = 6, 7` and D's witness.
  Use the DP oracle under the cap and `D(n−1)` past it. They go in the new mode, not `--pd`'s
  population, so `--pd`'s figures do not move.

All three are cheap. They settle rows 5 and 10–12, and give the first evidence where the failing
rows bite. **After it, by the PI's defaults** (design doc §1): PD-STATE and PD-STABLE open beside
the research as the next sub-phase (its letter minted at open), and T3 and T4 run at `d = 4, 5` on
the content range. **Landed:** the step table, its route verdict (§2.2: R2's step structure, R1's
base row) and §2.5. The steps break at `d = 4` (SHORT) and `d = 5` (ONE-EAR). At `d` the content
is `def[3] ≥ d − 2`, measured so far on graphs that bind the pencil condition at few bodies.

## Architectural choices made up front

- **Research rules.** `HARNESS.md` *Evidence* and *Reproducibility* bind; this is not an attack
  track. A step that turns out to need a new argument may be split off as one (the PI, §1).
- **One home per kind.** The step table and the recon's verdicts live in the design doc §2; this
  note carries the checklist and the hand-off. `notes/Strata.md`'s Results are cited by number.

## Lemma checklist

- [x] **The step table** (design doc §2.1): 22 rows over `main-component.tex` and `pencil.tex`.
- [x] **Phase 39's reduction in `Pᵈ`**: `d`-general for the bare and distinct conjuncts given
  CARRIER (row 19); route B's generic conjunct fails as written and is separable (row 22).
- [x] **The route verdict** (§2.2): neither closes as written; R2's induction with R1's base row is
  the recon's proposal, the PI's call.
- [x] **The thresholds and the content range** (§2.5).
- [ ] **T1, T2** (§2.4): the flat formulas at `d = 4`; CERT's certificates at `d = 4, 5, 6`.
- [ ] **The content-range graphs** (§2.5): `θ(2, 2, k)`, `θ(2, 2, 2, k)`, diamond rings at
  `m = 6, 7`, D's witness, at `d = 4, 5, 6`.
- [ ] **T3, T4, T5** (§2.4), on graphs with `def[3] ≥ d − 2` only: SHORT at `d = 4, 5`, ONE-EAR
  at `d = 4, 5` (and T4's `d = 5, 6` half), the coverage rows at `D = 10, 15`. Each sizes an
  obligation before any attack on it.
- [ ] **A second read of rows 9 and 12** (contraction; (⋆) and the two-body ear), before an attack
  track or PD-CARRIER builds on them.
- [ ] **SHORT, ONE-EAR** (§2.3): attack tracks once T3 and T4 size them, SHORT at `d = 4` and
  ONE-EAR at `d = 5`.

## Blockers / open questions

- None blocking. Still open for the PI: the route (design doc §4); the defaults (§1) work inside
  §2.2's proposal.

## Hand-off / next phase

Land T1, T2 and the content-range graphs as one `strata.py` mode, committed with its figures
(`HARNESS.md` *Reproducibility*). If a content-range graph stays below target at several seeds
(one point's shortfall proves nothing), take it to the PI before anything else. Otherwise the next two commits are open in either order: PD-STATE's
open (the next sub-phase, `PHASE-BOUNDARIES.md` *When this commit opens a phase*) and T3 and T4 at
`d = 4, 5`. Whether SHORT and ONE-EAR take one session or several is unknown until T3 and T4 size
them.

## Decisions made during this phase

- The open's decisions are the PI's, recorded verbatim in the design doc §1.
- The step table's rows are the four recon passes' readings, cited by row; the coordinator's own
  checks are listed under §2.1.
- **The PI's planning defaults** (design doc §1, 2026-10-29): content-range tests first; three
  tiered targets; GENERIC after; PD-STATE and PD-STABLE beside the research once T1 and T2 land;
  a second read of rows 9 and 12.
