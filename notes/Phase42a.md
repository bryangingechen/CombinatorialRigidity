# Phase 42a — PD-RECON: does Phase 40's induction run in every `Pᵈ`? (work log)

**Status:** in progress, opened 2026-10-29 with the PI, attended. Research only: no Lean, no
blueprint. Next concrete task: the step table (`notes/Phase42-design.md` §2). Plan, the PI's
decisions and the layers: `notes/Phase42-design.md`; evidence: `notes/Strata.md`.

## Current state

**Next: the step table**, one commit, into `notes/Phase42-design.md` §2. For each step of Phase
40's induction and its two lemmas, read the blueprint proof in `main-component.tex` and record
where it uses `d = 3` beyond the screw dimension `D = 6` and the flat base, with a verdict for R1
(induction on `d`) per step. Nothing else has landed: the open only moved the program from
`notes/Strata.md` to the design doc.

## Architectural choices made up front

- **Research rules.** `HARNESS.md` *Evidence* and *Reproducibility* bind; this is not an attack
  track. A step that turns out to need a new argument may be split off as one (the PI, §1).
- **One home per kind.** The step table and the recon's verdicts live in the design doc §2; this
  note carries the checklist and the hand-off. `notes/Strata.md`'s Results are cited by number.

## Lemma checklist

- [ ] **The step table** (design doc §2): rows for the cut and bridge-chain scheme
  (`sec:main-component-cut`), contraction at an additive core (`sec:main-component-contract`), the
  cycle and long ear (`sec:main-component-chain`), the short ears (`sec:main-component-short`),
  the orbit ear (`sec:main-component-orbit`), the split-off (`sec:main-component-splitoff`), the
  sparse-deficiency estimates and the coverage, and the two lemmas
  (`lem:pencil-x0-one-witness`, `lem:pencil-x0-fibre-intersection`).
- [ ] **Phase 39's reduction in `Pᵈ`**: is the multigraph reduction (`pencil.tex`) `d`-general?
- [ ] **The route verdict**: R1, R2, or a certificate against both, per step from the table.

## Blockers / open questions

- None blocking. Open: the route (design doc §4).

## Hand-off / next phase

Land the step table as one commit (design doc §2, the checklist's first item). Whether the recon
then takes one more session or several is unknown until the table exists.

## Decisions made during this phase

- The open's decisions are the PI's, recorded verbatim in the design doc §1.
