# Phase 21b — Genericity device (Claim 6.4/6.9) (work log)

**Status:** in progress (opened 2026-06-03).

Sub-phase scoped out of Phase 21 on 2026-06-03 (user decision, risk
#4/#7), the **analytic sibling** of the Phase-21a meet sub-phase. The one
genuinely new analytic crux of Katoh–Tanigawa's algebraic induction
(KT 2011 §6.1 Claim 6.4, §6.3 Claim 6.9): the entries of the panel-hinge
rigidity matrix `R(G,p)` are polynomials in the algebraically independent
panel coordinates (the per-vertex normals), so the rank is lower
semicontinuous and attains its maximum on a Zariski-open (generic) set —
hence a *single* good realization at the target rank lifts to a *generic*
one. This is the shared black-box that Phase 21 left cited in `lem:case-I`
(`hglue`), `lem:case-II` (`hspan`), `thm:theorem-55` (transitively),
`prop:rigidity-matrix-prop11` (`hub`/`hgen`), and the projective assembly
of `lem:cycle-realization`. Phase 21b discharges it once; the consumers
flip GREEN-modulo-21b → GREEN.

Program-level plan, reuse map, citations, risk register:
`notes/MolecularConjecture.md` *Phase 21b*. Scope-out rationale + the
node-by-node consumer split: `DESIGN.md` *Genericity device (Claim
6.4/6.9) is its own sub-phase (Phase 21b)* and `notes/Phase21.md`
*Hand-off*. Forward-mode dep-graph node:
`blueprint/src/chapter/algebraic-induction.tex`
(`lem:genericity-device`, `sec:molecular-algebraic-induction-genericity`).
Lean lands in `CombinatorialRigidity/Molecular/AlgebraicInduction.lean`
(beside the consumers) unless it grows enough to warrant its own file.

## Current state

**Phase opened (2026-06-03), no Lean yet.** This commit is the
phase-opening commit per CLAUDE.md *When this commit opens a phase*:
creates this notes file, adds the forward-mode `lem:genericity-device`
blueprint node (red — the device the four Phase-21 consumers `\uses`),
flips the 21b status row to *in progress*, and syncs the user-facing
surfaces. No Lean lands here; the first Lean brick is the
reuse-to-assess below.

## Architectural choices made up front

- **Forward-mode, node beside the consumers.** A single
  `lem:genericity-device` node in `algebraic-induction.tex` (its own
  `sec:molecular-algebraic-induction-genericity` subsection, before
  Case III) that the four Phase-21 consumers `\uses`. If the device's
  Lean grows past a handful of lemmas, split it into its own
  `.lean` + `.tex` per the one-file-per-molecular-phase convention.
- **Discharge the consumers' explicit hypotheses.** Each Phase-21 node
  is GREEN-modulo-21b with the device's conclusion taken as a named
  hypothesis (`hglue`/`hspan`/`hub`/`hgen`). The device must produce
  exactly those: this fixes the device's *target statement* before its
  *proof strategy* — pin the API the consumers already expect.

## Lemma checklist

Forward-mode: the authoritative node list is `algebraic-induction.tex`
(`sec:molecular-algebraic-induction-genericity`). Tracked here for
hand-off convenience.

- [ ] `lem:genericity-device` — Claim 6.4/6.9: the entries of `R(G,p)`
  are polynomials in the panel coordinates ⇒ the rank attains its max on
  a generic set; a single good realization lifts to a generic one. Red
  (the phase's target).

The consumer-side discharge targets (each currently a named hypothesis
in the Phase-21 Lean, to be supplied by the device):
- [ ] `hglue` for Case I — block-triangular generic gluing
  (`finrank Z ≤ D + finrank (pinnedMotionsOn s)`).
- [ ] `hspan` for Case II — each base-`v`-pinned motion lands in the two
  new edges' panel-support spans (false pointwise; holds by the
  rank/dimension count, via `exists_independent_panelSupportExtensor`).
- [ ] `hub`/`hgen` for Prop 1.1 — the generic-rank reconciliation
  (`hgen` = Thm 5.5 pushed through the device).
- [ ] the projective assembly of `lem:cycle-realization` (its four Lean
  pieces are green; only the cited CW82/Whiteley99 projective assembly
  is non-Lean).

## Decisions made during this phase

### Phase-local choices and proof techniques
- *(none yet — opened this commit.)*

## Blockers / open questions

- **Reuse-to-assess (first concrete brick).** Whether the Phase-6/8
  Gram-det perturbation machinery
  (`Mathlib/LinearAlgebra/Matrix/Rank.lean`, the
  `exists_uniform_rowIndependent_placement`-style cofiniteness-of-LI-
  along-a-line argument) transfers to the panel-coordinate
  parametrization of `R(G,p)`, or whether a fresh polynomial-rank /
  Zariski-open-attainment argument is needed. The Phase-21a finding was
  that the *cycle* genericity was purely exterior-algebraic (no
  perturbation); assess on contact whether the panel-coordinate rank
  argument reduces similarly or is genuinely polynomial-perturbation.
  See `notes/MolecularConjecture.md` *Phase 21b*.

## Hand-off / next phase

**Smallest next concrete commit:** assess the reuse-to-assess above —
read `Mathlib/LinearAlgebra/Matrix/Rank.lean`'s Gram-det LI-cofiniteness
lemmas (the Phase-8 `exists_uniform_rowIndependent_placement` route) and
the panel-coordinate entry structure of `R(G,p)` (Phase 18
`Molecular/RigidityMatrix.lean`), and decide whether to (a) reuse that
machinery for the panel-coordinate parametrization or (b) write a fresh
polynomial-rank argument. Record the call as the first *Decisions made*
entry, then land the chosen first linear-algebra brick. The device's
*target statement* is fixed: produce the consumers' `hglue`/`hspan`/
`hub`/`hgen` hypotheses (see *Lemma checklist*).

**Also consumed by Phases 22–23** (Case III candidate-framework
genericity, Claims 6.11/6.12), so building the device standalone pays
forward; for Case III's share it bottoms on Lemma 2.1 (Phase 17 green).
