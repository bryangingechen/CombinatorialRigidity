# Phase 42a — PD-RECON: does Phase 40's induction run in every `Pᵈ`? (work log)

**Status:** in progress, opened 2026-10-29 with the PI, attended. Research only: no Lean, no
blueprint. Landed: the step table and thresholds (design doc §2.1–§2.5); T1–T5 (`Strata.md`
Results 20–26), with no shortfall: SHORT shrinks to SHORT-CORE, ONE-EAR's first option holds
wherever M does, and at `D ≥ 10` the coverage needs ONE-EAR only on ONE-CLASS. Then, at the PI's
call, ONE-CLASS's lemma (Result 27), which takes ONE-EAR out of the coverage; then the PI took the
route (R2's steps, the embedding as the base row). Next concrete task:
PD-STATE's open; the research next is SHORT-CORE's attack track, its brief drafted for the PI's
reading. Plan and decisions: `notes/Phase42-design.md`; evidence: `notes/Strata.md`.

## Current state

**Next** (the PI's defaults, design doc §1):
- **PD-STATE's open** beside the research, its letter minted then (`PHASE-BOUNDARIES.md` *When
  this commit opens a phase*): check the dual-form carrier (§2.3 CARRIER) against the definition
  bodies, and lay out PD-STABLE.
- **SHORT-CORE's attack track** (`/attack`, design doc §2.3), the coverage's only new mathematics
  at `d ≥ 4` since Result 27. Rows 9 and 12, which T5's cover rests on, passed a second read.
  Its brief is `notes/attacks/short-core/brief.md`, a DRAFT: once the PI has read it,
  `/attack short-core` runs in its own worktree (branch `attack-short-core`), with no Lean build
  there, beside PD-STATE's Lean in the main checkout.

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
Then ONE-CLASS, at the PI's call (Result 27, §2.3–2.4): a graph whose chains are all one-body has
a core at every `D ≥ 6` or `def[6] = 0`, so Phase 40 embeds; checked by `oneclass.py`. Then the
second read of rows 9 and 12 (§2.1), by two recons in parallel: no gap. Contraction holds under
R2 at every `d ≥ 4`; the two-body ear at every `d`, and longer ears up to `k = D − 2` given CERT,
proved at `d ≤ 6`. Both need only CARRIER's restatements.

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
  the recon's proposal, taken by the PI (design doc §1), the induction on `d` left to Tier 2.
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
- [x] **A second read of rows 9 and 12** (design doc §2.1): no gap; GEN|CARRIER, row 12's
  `3 ≤ k ≤ D − 2` given CERT's open ears (proved at `d ≤ 6`).
- [ ] **SHORT-CORE** (§2.3): an attack track at `d = 4` (`k = 3, 4, 5`; sized by T3, needed by
  T5's Petersen cells). Brief drafted (`notes/attacks/short-core/brief.md`), awaiting the PI.
- [x] **ONE-CLASS** (§2.3; the PI's call over ONE-EAR): proved, `Strata.md` Result 27, checked
  by `oneclass.py`. ONE-EAR leaves the coverage and waits for GENERIC.

## Blockers / open questions

- None. The route is settled (the PI, design doc §1 and §4).

## Hand-off / next phase

The next commit is PD-STATE's open as the next sub-phase (*Current state*). On the research side,
Result 27 leaves SHORT-CORE as the coverage's only new mathematics at `d ≥ 4`: `k = 3, 4, 5` at
`d = 4`, its `d = 3` model the chapter's `k = 3` case split on `ρ`, needed by T5's Petersen cells.
Rows 9 and 12, on which T5's cover rests, passed a second read, so its attack track can open once
the PI has read its DRAFT brief (`notes/attacks/short-core/brief.md`); it builds on (⋆) and the X3
range (design doc §2.3). PD-STABLE states the embedding
at every `d′ ≤ d` (the route), its `d′ = 3` case as the coverage consumes it, `def[6] = def[D]`
(design doc §3). CERT's open ears at
`d ≥ 7` (§2.3) are PD-STEPS's, for the every-`d` tier. ONE-EAR (the motive, a `Pᵈ` insertion
lemma, X2) is GENERIC's now, deferred with it.

## Decisions made during this phase

- The open's decisions are the PI's, recorded verbatim in the design doc §1, as are the call of
  ONE-CLASS over ONE-EAR (after T5) and the route (after the second reads), both 2026-10-29.
- The step table's rows are the four recon passes' readings, cited by row; the coordinator's own
  checks are listed under §2.1.
- **The PI's planning defaults** (design doc §1, 2026-10-29): content-range tests first; three
  tiered targets; GENERIC after; PD-STATE and PD-STABLE beside the research once T1 and T2 land;
  a second read of rows 9 and 12.
- **One driver mode per test, so earlier figures do not move:** `strata.py --content` (T1, T2),
  `--oneear` and `--orbit` (T4), `--short` (T3, danger cells only), `--coverage` (T5), and a new
  driver, `oneclass.py` (ONE-CLASS). Supports, fences and seeds: `Strata.md` *Evidence*. Every
  cell is seeded by itself alone, and T5 and ONE-CLASS draw no point. T2's `D`-gon is built
  (`cert_top`): a `{−1, 0, 1}` search found none at `d = 5, 6` in 5000 tries (measured, script
  not retained).
- **The second reads ran as two parallel read-only recons** (the PI, design doc §1), each briefed
  to refute and to form its verdict before reading the table's; their probes are not retained.
- **Proved where possible, not read off a point:** T4's one miss is forced from asserted premises;
  T5's two reductions and ONE-CLASS's lemma are proofs by hand (design doc §2.3–2.4), checked by
  their drivers. `oneclass.py` checks the proof's own set, not only a core's existence, and adds
  necklaces, as small cores never have `def_6 > 0`. The lemma first posed for ONE-CLASS (empty
  at `D ≥ 15`) gave way to the one that holds, `def_6 = 0`.
