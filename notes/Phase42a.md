# Phase 42a — PD-RECON: does Phase 40's induction run in every `Pᵈ`? (work log)

**Status:** in progress, opened 2026-10-29 with the PI, attended. Research only: no Lean, no
blueprint. Landed: the step table and thresholds (design doc §2.1–§2.5); T1, T2 and the
content-range graphs (`Strata.md` Results 20–22), with no shortfall; T4's first half (Result 23),
where ONE-EAR's first option holds at every cell meeting the `d = 3` step's merged hypothesis; T3
(Result 24), where SHORT's obstruction never occurs and SHORT shrinks to SHORT-CORE.
Next concrete task: T4's second half, or PD-STATE's open, in either order.
Plan and decisions: `notes/Phase42-design.md`; evidence: `notes/Strata.md`.

## Current state

**Next, in either order** (the PI's defaults, design doc §1):
- **T4's second half** (ONE-EAR; design doc §2.4), one `strata.py` mode committed with its
  figures: at `d = 5, 6`, `dim(ρ + Λ²(A+B))` against `3 + f − def[D](G)` on the content range,
  and Result 23's two `d = 4` cells where (⋆) at `k = 1` asks for 3. T5 (coverage) after.
- **PD-STATE's open** beside the research, its letter minted then (`PHASE-BOUNDARIES.md` *When
  this commit opens a phase*): check the dual-form carrier (§2.3 CARRIER) against the definition
  bodies, and lay out PD-STABLE.

**Landed:** the step table, its route verdict (§2.2: R2's step structure, R1's base row) and
§2.5; then T1, T2 and the content-range graphs as one mode, `strata.py --content`. Row 5's
formulas hold. CERT holds at `d ≤ 6` over every field, its `D`-gon by a construction in every `d`
(§2.3). All 38 new content cells attain, on graphs carrying rows 14's and 22's configurations, so
the obstruction measured so far is the proof's, not the statement's. The steps break at `d = 4`
(SHORT) and `d = 5` (ONE-EAR). Then T4's first half, `strata.py --oneear` (Result 23, §2.4): on
`θ(2, 2, k)` and `θ(2, 3, k)` `G[V₁]` attains on the incidence locus at all 26 cells, `d = 4, 5`;
on `θ(2, 2, 2, k)`, where the merged hypothesis fails, it misses once, provably (`k = 10`, `d = 4`).
Then T3, `strata.py --short` (Result 24, §2.3–2.4): on 198 danger cells at `d = 4, 5`, six
families, `W` never contains a star unless `W = Λ²`, and `x₂` put back gains what (⋆) needs. X3
is proved for `k ≥ C(d−1, 2) + 3` (a CERT polygon in the quotient by the stars), so SHORT's open
part is SHORT-CORE, `k = 3–5` at `d = 4` (`3–8` at `d = 5`), where `ρ` must fill that quotient.

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
- [x] **T4's first half** (§2.4): `G[V₁]` on `G`'s configurations at `d = 4, 5` (Result 23).
- [x] **T3** (§2.4): SHORT's danger cells at `d = 3, 4, 5` (Result 24); X3 for
  `k ≥ C(d−1, 2) + 3` proved (§2.3).
- [ ] **T4's second half, T5** (§2.4), on graphs with `def[3] ≥ d − 2` only: T4 at `d = 5, 6`,
  the coverage rows at `D = 10, 15`. Each sizes an obligation before any attack on it. T4's
  second half is next (*Current state*).
- [ ] **A second read of rows 9 and 12** (contraction; (⋆) and the two-body ear), before an attack
  track or PD-CARRIER builds on them.
- [ ] **SHORT-CORE, ONE-EAR** (§2.3): attack tracks, SHORT-CORE at `d = 4` (`k = 3, 4, 5`;
  sized by T3) and ONE-EAR at `d = 5` once T4's second half sizes it.

## Blockers / open questions

- None blocking. Still open for the PI: the route (design doc §4); the defaults (§1) work inside
  §2.2's proposal.

## Hand-off / next phase

Two commits are open, in either order (*Current state*). One is T4's second half, a new
`strata.py` mode committed with its figures (`HARNESS.md` *Reproducibility*); the other is
PD-STATE's open as the next sub-phase. T4's first half left ONE-EAR's first option standing where
the step's merged hypothesis holds; its insertion count is the second half's. T3 sized SHORT: an
attack track on SHORT-CORE at `d = 4` (`k = 3, 4, 5`), whose `d = 3` model is the chapter's
`k = 3` case split on `ρ`. Whether ONE-EAR takes one session or several is unknown until T4's
second half sizes it.

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
- **T4's first half is its own mode**, `strata.py --oneear`, so `--content`'s figures do not
  move. It adds `θ(2, 3, k)` as a control (ends sharing no neighbour) and reports the `d = 3`
  step's two hypotheses per cell, since the motive is needed only where that step is taken. Its
  one miss is proved from asserted premises, not read off a point. A past-cap cell is certified
  when `G₁`'s own configuration reaches `D(n₁ − 1)`, so it is marked `<`, not `?`.
- **T3 tests only the danger cells**, `strata.py --short`: off them the `d`-general insertion
  lemma already settles the step. Its graphs are mostly past the DP cap, so each deficiency is
  a partition's value matched by a generic-hinge rank. Cells come from a box search seeded by
  `(family, d, k)` alone, and a failed degeneracy guard redraws the point (`~`), as the
  three-collinear picture at seed 2 did.
