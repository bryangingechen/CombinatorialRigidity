# Phase 40b — PENCIL-X0 / CARRIER: planar pictures, the lifting space, `X₀`, and "the general point attains" (work log)

**Status:** ✓ complete (opened design-first and closed 2026-09-26). The geometric layer of the
`X₀` argument landed in `Molecule/Pencil/MainComponent/Carrier.lean` (later split into
`Configuration.lean`, 40h PI decision 5): admissible planar pictures, the lifting space `L(q)`,
the open set `U` of main pictures, `Graph.X0Attains` with its one-witness upgrade, each
configuration read as a pencil realization (the `X0Dist` leg), and the fibre-intersection lemma;
DUAL-K made the polarity field-general. `thm:pencil-x0-main-component` is green at its formalized
content. Phase 40 continued with **FLAT** (`notes/Phase40c.md`, closed 2026-09-26) and on through
the phase's own close, 2026-09-29 (`notes/Phase40-design.md` §3, ROADMAP §40).

## Current state

**Closed.** Slices C1a–C5′, DUAL-K and the close commit landed; `main-component.tex`
§`sec:main-component-carrier` is all green (five definitions, eleven lemmas, the restated
`thm:pencil-x0-main-component`, and two remarks: `rem:pencil-hinge-affine`,
`rem:pencil-x0-main-component`). Headline axioms were re-verified at the close on 22 declarations
(the eighteen `formalization.yaml` main results plus the four new pins), each exactly
`[propext, Classical.choice, Quot.sound]`.

## Architectural choices made up front

The coordinator's adjudication (2026-09-26), settling the design recon:

- **Uncurried picture coordinates** `q : α × Fin 2 → K` (not curried): composes directly with
  `PanelHingeFramework.ofNormals`, whose rank polynomial lives in `MvPolynomial (α × Fin 2) K`.
- **A single `X0Attains` predicate** carrying a Zariski-open set of attaining heights via a nonzero
  `MvPolynomial (α × Fin 2) K`, with fibre-genericity/semicontinuity proved once in
  `Graph.x0Attains_of_exists` (not two defs).
- **The picture→normal map is `cross₃`** of homogeneous config points — polynomial,
  denominator-free.
- **β-headroom fix, planned, never built**: the `_of_card` triple (`x0Dist_of_card`,
  `x0Gen_of_card`, `pencil_conjecture_of_card`) was retired by MOTIVES' recon
  (`notes/Phase40-design.md` §3).

Landed in slices **C1a**, **C1b**, **C2**, **DUAL-K**, **C3**, **C4**, **C5′** (see *Decisions
made*).

## Decisions made during this phase

- **2026-09-26 C1a.** The rank is read at `ofNormals` of the configuration points, not the plane
  normals (a zero hinge would weld a def₂-rigid subgraph); `U` is a definition; `X0Attains` carries
  fibre-openness via a per-picture `R`; `L(q)` vanishes off `V(G)`; `ends` is link-relative.
- **2026-09-26 C1b.** The Cramer section uses a left inverse, not a maximal minor
  (`TACTICS-GOLF.md` §25).
- **2026-09-26 C2.** Moment-curve witness, `Nat.sInf` minimizer, the section mirror at `0`; the
  codim bound dropped (now `notes/Phase40-design.md` §3 FLAT).
- **2026-09-26 DUAL-K.** The duality recon: the polarity is field-free; `ProjectiveInvariance.lean`
  generalized in place (frozen-doc citations ruled out a restatement) — `notes/Phase40-design.md`
  §4.
- **2026-09-26 C3.** Item 3 needs only `z ∈ L(q)`.
- **2026-09-26 C4.** The polar/primal rank equality needs no `hends`; the patch off `E(G)` is
  forced by `HasCoplanarPanelRealization`.
- **2026-09-26 C5′.** `exists_mem_eval_ne_zero₂`, `mem_liftingSpace_of_coplanar`,
  `exists_smul_eq_interpolant`, transcribed from a compiler-checked scope-pin recon.
- **2026-09-26 — the PI's close adjudication, verbatim** (`notes/pencil/adjudications.md`): 2
  commits (C5′ was commit 1); restate and keep `thm:pencil-x0-main-component`; leave the public
  surfaces.
- **2026-09-26 — the close.** `thm:pencil-x0-main-component` restated to its formalized content
  and pinned to four declarations; (MC-3)'s augmented-matrix rank split became
  `rem:pencil-hinge-affine` (no Lean object).

## Hand-off / next phase

**40b is closed.** Phase 40 continued with **FLAT** (`notes/Phase40c.md`, closed 2026-09-26) and
on through the phase's own close, 2026-09-29 — `notes/Phase40-design.md` §3 carries the full layer
list and proof map, ROADMAP §40 the final state.
