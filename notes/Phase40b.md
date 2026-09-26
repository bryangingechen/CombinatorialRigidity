# Phase 40b — PENCIL-X0 / CARRIER: planar pictures, the lifting space, `X₀`, and "the general point attains" (work log)

**Status:** ✓ complete (opened design-first and closed 2026-09-26). The geometric layer of the
`X₀` argument landed in `Molecule/Pencil/MainComponent/Carrier.lean`: admissible planar pictures,
the lifting space `L(q)`, the open set `U` of main pictures, `Graph.X0Attains` with its one-witness
upgrade, each configuration read as a pencil realization (the `X0Dist` leg), and the
fibre-intersection lemma; DUAL-K made the polarity field-general. `thm:pencil-x0-main-component` is
green at its formalized content; `thm:pencil-x0-generic-attains` waits, red, in the chapter's final
stub subsection. **Next: FLAT**, Phase 40's next layer (`notes/Phase40-design.md` §3), **not yet
opened** — see *Hand-off*.

## Current state

**Closed.** C1a–C5′, DUAL-K and the close commit landed. `blueprint/src/chapter/main-component.tex`
§`sec:main-component-carrier` is all green (five definitions, eleven lemmas, the restated
`thm:pencil-x0-main-component`, and two remarks: `rem:pencil-hinge-affine`, which replaced the
red (MC-3) lemma, and `rem:pencil-x0-main-component`, the geometry of `X₀`). The final stub
subsection `sec:main-component-statements` holds the red `thm:pencil-x0-generic-attains`, whose
first sentence is COVERAGE's and whose "granting this" clause is MOTIVES's. Headline axioms were
re-verified at the close on 22 declarations: the eighteen `formalization.yaml` main results
(the seventeen headline theorems plus `pencil_conjecture_of_X0`) and the four new pins of
`thm:pencil-x0-main-component`. Each is exactly `[propext, Classical.choice, Quot.sound]`
(*measured, script not retained*: one `#print axioms` line per declaration under
`import CombinatorialRigidity`, run with `lake env lean` on the built tree).

## Architectural choices made up front

The coordinator's adjudication (2026-09-26), settling the design recon:

- **Uncurried picture coordinates `q : α × Fin 2 → K`** (not curried `α → Fin 2 → K`).
  `PanelHingeFramework.ofNormals` takes `q : α × Fin (k+2) → K` and the rank polynomial lives in
  `MvPolynomial (α × Fin 2) K`, so uncurried composes directly with the landed machinery.
- **A single `X0Attains` predicate** carrying a nonzero `MvPolynomial (α × Fin 2) K`, with
  fibre-genericity/semicontinuity proved once in a mirror lemma `x0Attains_of_exists` (NOT two defs
  `X0Attains` + `X0GenericAttains`). `X0Dist` consumes one attaining `(q, z)`; `X0Gen` consumes the
  fibre-open clause (C1a verdict, *Decisions*).
- **The picture→normal map is `cross₃` of homogeneous config points** — polynomial, denominator-free.
  "Rational parametrization" collapses to a fibre polynomial at a fixed admissible `q`; the Cramer
  chart lives in the proof, not the def.
- **β-headroom fix: an additive-successor `_of_card` triple** (`x0Dist_of_card`, `x0Gen_of_card`,
  `pencil_conjecture_of_card`) concluding the UNCHANGED L0 predicates `X0Dist`/`X0Gen` and reusing the
  protected `pencil_conjecture_of_X0` verbatim. L0 is protected: not edited, not made
  unprovable-as-stated. These are MOTIVES leaves (`notes/Phase40-design.md` §3 MOTIVES, with the
  two open questions). Mirrors `molecular_conjecture_multigraph`'s `hcard`+`hspan` shape.

## Lemma checklist

All in `Carrier.lean` unless noted; signatures in its module docstring.

- [x] **C1a** — the seven definitions. **C1b** — `Graph.x0Attains_of_exists`.
- [x] **C2** — `Graph.exists_mvPolynomial_isMainPicture` and the lifting-space API.
- [x] **DUAL-K** — `screwComplementIso` and `ProjectiveInvariance.lean` at `[Field K]`.
- [x] **C3** — the picture→normal API, incl. `pencilNormalOfPicturePoly`.
- [x] **C4** — `pencilConfigFramework`, its rank equality, `Graph.X0Attains.hasDistinctPencilRealization`.
- [x] **C5′** — `MvPolynomial.exists_mem_eval_ne_zero₂` (`Mathlib/Algebra/MvPolynomial/Funext.lean`);
  `lem:pencil-condition-linear` green.
- [x] **Commit 2 — the close** (docs only): the old C5 content moved to FLAT; the (MC-3) lemma a
  remark; `thm:pencil-x0-main-component` restated and green; `thm:pencil-x0-generic-attains` moved
  to the stub subsection; the public surfaces left unchanged (PI).

## Blockers / open questions

- None for CARRIER. The two questions deferred to the MOTIVES pre-build recon (the exact `hcard`
  constant; the headroom's root cause) moved at the close to `notes/Phase40-design.md` §3
  MOTIVES, and three STEPS items to §3 STEPS.

## Hand-off / next phase

**40b is closed. Next: open FLAT design-first** (its pre-build recon carries the questions in
`Phase40-design.md` §3 FLAT). The commit that opens it mints its letter and its work log. FLAT's
deliverables include the old C5 item (`X0Attains` at the flat witness `(q, 0)`) and the 40a pin
debt, both in §3 FLAT.

## Decisions made during this phase

- **2026-09-26 — the PI's close adjudication, verbatim.** Close shape: "2 commits (Recommended)"
  (C5′, `532d63fe`, was commit 1; the close is commit 2). `thm:pencil-x0-main-component`: "Let's
  restate and keep." Public surfaces (README, `home_page`, `intro.tex`, `formalization.yaml`):
  "Leave them".
- **2026-09-26 — the close.** `thm:pencil-x0-main-component` restated to its formalized content,
  pinned to four declarations and green; the geometry of `X₀` is `rem:pencil-x0-main-component`.
  (MC-3)'s lemma became `rem:pencil-hinge-affine` (its rank split has no Lean object).
  Project-organization review: no new item; the auto-loaded CLAUDE.md suite is unchanged since
  40a's review (1 695 lines), whose open FRICTION entry on `blueprint/CLAUDE.md` still covers it.
- **2026-09-26 — C5′:** `exists_mem_eval_ne_zero₂`, `mem_liftingSpace_of_coplanar`,
  `exists_smul_eq_interpolant`, transcribed from a compiler-checked scope-pin recon.
- **2026-09-26 — C4:** the polar/primal rank equality needs no `hends`; the patch off `E(G)` is
  forced by `HasCoplanarPanelRealization`.
- **2026-09-26 — C3:** item 3 needs only `z ∈ L(q)`.
- **2026-09-26 — C2:** moment-curve witness, `Nat.sInf` minimizer, the section mirror at `0`; the
  codim bound dropped (now §3 FLAT).
- **2026-09-26 — C1b:** the Cramer section uses a left inverse, not a maximal minor (TACTICS-GOLF
  § 25).
- **2026-09-26 — opened design-first; C1a shapes.** The rank is read at `ofNormals` of the
  configuration points, not the plane normals (a zero hinge would weld a def₂-rigid subgraph);
  `U` is a def; `X0Attains` carries fibre-openness via a per-picture `R`; `L(q)` vanishes off
  `V(G)`; `ends` is link-relative.
- **2026-09-26 — duality recon and DUAL-K** (`Phase40-design.md` §4): the polarity is field-free;
  `ProjectiveInvariance.lean` was generalized in place (frozen-doc citations ruled out a restatement).
