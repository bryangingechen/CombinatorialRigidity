# Phase 42a — PD-RECON: does Phase 40's induction run in every `Pᵈ`? (work log)

**Status:** in progress, opened 2026-10-29 with the PI, attended. Research only: no Lean, no
blueprint. Landed: the step table and thresholds (design doc §2.1–§2.5); T1, T2 and the
content-range graphs (`Strata.md` Results 20–22), with no shortfall.
Next concrete task: T4's first half at `d = 4, 5`, or PD-STATE's open, in either order.
Plan and decisions: `notes/Phase42-design.md`; evidence: `notes/Strata.md`.

## Current state

**Next, in either order** (the PI's defaults, design doc §1):
- **T4's first half** (design doc §2.4), one `strata.py` commit with its figures. At `d = 4, 5`,
  on Result 22's `θ(2, 2, k)` and `θ(2, 2, 2, k)` (a one-body ear `a − x − b` whose ends share a
  neighbour), take a configuration of `G` and measure `G[V₁] = G − x` there against its target,
  with `dim(Π_a ∩ Π_b)`. Then T3 (SHORT, `d = 4, 5`) and T4's `d = 5, 6` half; each sizes an
  obligation before any attack track.
- **PD-STATE's open** beside the research, its letter minted then (`PHASE-BOUNDARIES.md` *When
  this commit opens a phase*): check the dual-form carrier (§2.3 CARRIER) against the definition
  bodies, and lay out PD-STABLE.

**Landed:** the step table, its route verdict (§2.2: R2's step structure, R1's base row) and
§2.5; then T1, T2 and the content-range graphs as one mode, `strata.py --content`. Row 5's
formulas hold. CERT holds at `d ≤ 6` over every field, its `D`-gon by a construction in every `d`
(§2.3). All 38 new content cells attain, on graphs carrying rows 14's and 22's configurations, so
the obstruction measured so far is the proof's, not the statement's. The steps break at `d = 4`
(SHORT) and `d = 5` (ONE-EAR).

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
- [x] **T1, T2** (§2.4): the flat formulas at `d = 4, 5, 6`; CERT's certificates at `d = 3..6`,
  over every field (`Strata.md` Results 20–21).
- [x] **The content-range graphs** (§2.5): 38 content cells at `d = 4, 5, 6`, all at target
  (Result 22).
- [ ] **T3, T4, T5** (§2.4), on graphs with `def[3] ≥ d − 2` only: SHORT at `d = 4, 5`, ONE-EAR
  at `d = 4, 5` (and T4's `d = 5, 6` half), the coverage rows at `D = 10, 15`. Each sizes an
  obligation before any attack on it. T4's first half is next (*Current state*).
- [ ] **A second read of rows 9 and 12** (contraction; (⋆) and the two-body ear), before an attack
  track or PD-CARRIER builds on them.
- [ ] **SHORT, ONE-EAR** (§2.3): attack tracks once T3 and T4 size them, SHORT at `d = 4` and
  ONE-EAR at `d = 5`.

## Blockers / open questions

- None blocking. Still open for the PI: the route (design doc §4); the defaults (§1) work inside
  §2.2's proposal.

## Hand-off / next phase

Two commits are open, in either order (*Current state*). One is T4's first half, a new
`strata.py` mode committed with its figures (`HARNESS.md` *Reproducibility*), on Result 22's
thetas. The other is PD-STATE's open as the next sub-phase. A `G[V₁]` cell below target at
several seeds would rule out ONE-EAR's first option at `d = 4`, the motive asking `G[V₁]` to attain
on that locus (design doc §2.3), leaving another step (one point's shortfall proves nothing). Whether SHORT and ONE-EAR take one session or several is unknown
until T3 and T4 size them.

## Decisions made during this phase

- The open's decisions are the PI's, recorded verbatim in the design doc §1.
- The step table's rows are the four recon passes' readings, cited by row; the coordinator's own
  checks are listed under §2.1.
- **The PI's planning defaults** (design doc §1, 2026-10-29): content-range tests first; three
  tiered targets; GENERIC after; PD-STATE and PD-STABLE beside the research once T1 and T2 land;
  a second read of rows 9 and 12.
- **T1, T2 and the content range share one mode**, `strata.py --content`, so `--pd`'s figures do
  not move. T2's searches are seeded by `(d, m)` alone, the same at every `--seed`, and its
  `D`-gon is built (`cert_top`), not searched: a `{−1, 0, 1}` search found none at `d = 5, 6` in
  5000 tries (measured, script not retained). Independence is checked over every field (Smith
  invariant factors), as Phase 40's certificates are.
