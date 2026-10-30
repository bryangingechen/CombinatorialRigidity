# Phase 42a — PD-RECON: does Phase 40's induction run in every `Pᵈ`? (work log)

**Status:** in progress, opened 2026-10-29 with the PI, attended. Research only: no Lean, no
blueprint. Landed: the step table and thresholds (design doc §2.1–§2.5); T1, T2 and the
content-range graphs (`Strata.md` Results 20–22), with no shortfall; T3 (Result 24), where SHORT's
obstruction never occurs and SHORT shrinks to SHORT-CORE; T4 (Results 23, 25), where ONE-EAR's
first option holds wherever the merged hypothesis M does, `d = 3..6`; T5 (Result 26), where the
coverage never needs ONE-EAR's third part and, at `D ≥ 10`, needs ONE-EAR only on ONE-CLASS.
Next concrete task: PD-STATE's open; the PI's call on ONE-CLASS (design doc §4).
Plan and decisions: `notes/Phase42-design.md`; evidence: `notes/Strata.md`.

## Current state

**Next** (the PI's defaults, design doc §1):
- **PD-STATE's open** beside the research, its letter minted then (`PHASE-BOUNDARIES.md` *When
  this commit opens a phase*): check the dual-form carrier (§2.3 CARRIER) against the definition
  bodies, and lay out PD-STABLE.
- **For the PI** (design doc §4): ONE-EAR's attack at `d = 5`, or ONE-CLASS first (§2.3), a
  lemma on deficiencies that would take ONE-EAR out of the coverage. Ask before either track.

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
Then T4's second half, `strata.py --orbit` (Result 25, §2.3–2.4): the orbit ears at `d = 3..6`.
At 46 one-body cells `G[V₁]` attains on the locus and `(⋆)` holds; at 69 two-body cells Phase
40's route (`G₁` on the locus, then `x₂` put back) reaches `min(s + 1, dim(ρ + Λ²(A+B)))`, which
is `(⋆)` at all 62 with M. The 7 without M fail as at `d = 3`: the locus forces `Π_a = Π_b`.
Then T5, `strata.py --coverage` (Result 26, §2.4): Theorem S holds at every `D ≥ 6`, so ONE-EAR's
third part is never needed, and at `D ≥ 10` a graph with no GEN row has a chain with `k ≥ 3` or
lies in ONE-CLASS's shape (both by hand). On subdivisions of ten cores every cell at `d = 4, 5, 6`
has a GEN row, a core at every one; Petersen's 4- and 6-path subdivisions need SHORT-CORE.

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
- [x] **T4's second half** (§2.4): the orbit cells at `d = 3..6` (Result 25); ONE-EAR sized as
  the motive, the insertion and X2 (§2.3).
- [x] **T5** (§2.4): the coverage at `D = 6..21` on subdivisions of ten cores (Result 26);
  Theorem S at `D` and the `D ≥ 10` reduction proved by hand.
- [ ] **A second read of rows 9 and 12** (contraction; (⋆) and the two-body ear), before an attack
  track or PD-CARRIER builds on them. T5's cover rests on row 9 at every cell at `d ≥ 4`.
- [ ] **SHORT-CORE** (§2.3): an attack track at `d = 4` (`k = 3, 4, 5`; sized by T3, needed by
  T5's Petersen cells).
- [ ] **ONE-EAR or ONE-CLASS** (§2.3): ONE-EAR's attack at `d = 5` (the motive, the insertion,
  X2; sized by T4), or ONE-CLASS's lemma, which T5 found holding at all 542 cells of its box.
  The PI's call (design doc §4).

## Blockers / open questions

- None blocking. Still open for the PI (design doc §4): the route, where the defaults (§1) work
  inside §2.2's proposal; and ONE-EAR's attack or ONE-CLASS, raised by T5.

## Hand-off / next phase

The next commit is PD-STATE's open as the next sub-phase (*Current state*). T3–T5 have sized the
attack tracks. SHORT-CORE is at `d = 4` (`k = 3, 4, 5`), its `d = 3` model the chapter's `k = 3`
case split on `ρ`, and T5 shows the coverage needs it. ONE-EAR is at `d = 5`, three lemmas (design
doc §2.3): the motive, which is new mathematics; a `Pᵈ` insertion lemma; and X2, measured only.
T5 confines what the coverage asks of it to row 14 on ONE-CLASS, a combinatorial statement
measured true wherever tested. Whether to attack ONE-EAR or ONE-CLASS first is the PI's call;
ONE-CLASS's size (one session or several) is unknown, and it is unattempted.

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
- **T4's second half is its own mode**, `strata.py --orbit`, on T3's families, so `--short`'s
  figures do not move. Only orbit cells (`def[D](G[V₁]) > def[D](G)`, where row 12 does not apply),
  at `k = 2` only those with no slack (`def[D](G₁) = def[D](G)`). The danger class reads the meet
  at a configuration seeded with the cell: a prediction from shared neighbours missed the
  diamond-edge cells. M is certified past the DP cap as `def_3(G[V₁]) − def_3(G[V₁] + ab) = 2`.
- **T5 is exact combinatorics**, `strata.py --coverage`: deficiencies of subdivisions by a DP
  over the core (`core_def`, proved exact, checked against the `3^n` DP under the cap), each
  row's obligation read off §2.1's verdicts (`cov_tag`), and the population every length vector
  on five small cores and 60 drawn on five more, so nothing varies with the seed. Two hand
  arguments carry it past the population (§2.4); its Petersen cells test the second's sharpness.
- **T3 tests only the danger cells**, `strata.py --short`: off them the `d`-general insertion
  lemma already settles the step. Its graphs are mostly past the DP cap, so each deficiency is
  a partition's value matched by a generic-hinge rank. Cells come from a box search seeded by
  `(family, d, k)` alone, and a failed degeneracy guard redraws the point (`~`), as the
  three-collinear picture at seed 2 did.
