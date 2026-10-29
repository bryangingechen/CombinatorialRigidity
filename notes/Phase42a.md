# Phase 42a — PD-RECON: does Phase 40's induction run in every `Pᵈ`? (work log)

**Status:** in progress, opened 2026-10-29 with the PI, attended. Research only: no Lean, no
blueprint. The step table has landed (design doc §2.1–§2.4). Next concrete task: T1 and T2, one
`strata.py` mode; the PI's calls are the design doc's §4. Plan and decisions:
`notes/Phase42-design.md`; evidence: `notes/Strata.md`.

## Current state

**Next: T1 and T2 (design doc §2.4), one commit.** A `strata.py` mode with exact rank at a seeded
point: T1 checks row 5's two flat formulas at `d = 4` on the `--d4` population (R2's flat rank
`10(n−1) + 3 − dim L(q)`, R1's base `10(n−1) − def[6]`); T2 builds CERT's certificates at
`d = 4, 5, 6` (closed `m`-gons for `m ≤ D_d`, the long ear at `k = D_d − 1`). Both are cheap and
settle rows 5 and 10–12. **Landed:** the step table, from four read-only recon passes. Ten of its
22 rows generalize as they stand and six given routine or formal work. Four fail as written: the
short ears (row 13), the one-body and orbit ears (14–15) and route B (22). The verdict on the
routes is §2.2: the step structure is R2's, and R1 contributes a base row.

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
- [ ] **T1, T2** (§2.4): the flat formulas at `d = 4`; CERT's certificates at `d = 4, 5, 6`.
- [ ] **T3, T4, T5** (§2.4): SHORT and ONE-EAR at `d = 4` (and `d = 5` for T4); the coverage rows
  at `D = 10, 15`. Each sizes an obligation before any attack on it.
- [ ] **SHORT, ONE-EAR** (§2.3): the new mathematics, recon or attack track as the PI decides.

## Blockers / open questions

- None blocking T1–T5. The PI's calls are the design doc's §4: the route, attack tracks for
  SHORT and ONE-EAR, `d = 4` first, the headline without GENERIC first, and nondegeneracy's lift.

## Hand-off / next phase

Land T1 and T2 as one `strata.py` mode, committed with its figures (`HARNESS.md`
*Reproducibility*), then T3 and T4 at `d = 4`. Whether SHORT and ONE-EAR take one session or
several is unknown until T3 and T4 size them.

## Decisions made during this phase

- The open's decisions are the PI's, recorded verbatim in the design doc §1.
- The step table's rows are the four recon passes' readings, cited by row; the coordinator's own
  checks are listed under §2.1.
