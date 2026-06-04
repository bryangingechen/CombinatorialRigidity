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
Lean is in `CombinatorialRigidity/Molecular/AlgebraicInduction.lean`
(beside the consumers) + mirror bricks under
`CombinatorialRigidity/Mathlib/{Algebra/MvPolynomial,LinearAlgebra/Matrix}/`.

## Current state

**The multivariate genericity device is GREEN (2026-06-04).** `lem:genericity-device`
is rebuilt on the genuine multivariate engine and re-pinned green; the four
genericity-free consumers (`lem:case-I`, `lem:case-II`, `thm:theorem-55`,
`prop:rigidity-matrix-prop11`) that took the device's conclusion as a hypothesis
now have all statement-deps green. The two remaining red nodes on the chapter are
the Case-I contraction splice (`lem:case-I-realization`, Hand-off 3) and the
deferred Case III (`lem:case-III`, Phases 22–23).

The device is `exists_good_realization` (multivariate keystone) +
`exists_good_realization_const` (constant-family closure the Case-I chain consumes)
in `AlgebraicInduction.lean`, both axiom-clean. They compose the multivariate
engine `exists_finrank_dualCoannihilator_polynomial` (route (a), landed `86f1221`)
with the coannihilator coordinatization `infinitesimalMotions_eq_dualCoannihilator`
and `finrank_screwAssignment` (`finrank (α → ScrewSpace k) = D|V|`). The device's
`hcoord` expresses `(F p).infinitesimalMotions` as the coannihilator of a
polynomial-coordinate functional family `g p` (panel coordinates `p : σ → ℝ` the
`MvPolynomial` vars, degree-2 rigidity entries the coefficients `c`); the conclusion
is `∃ p, #s + dim Z(F p) ≤ D|V|`.

**Wrapper chain consolidated (partial, Hand-off 2 mostly done this commit).** The
affine-special-case device + bridges (`genericityDevice`,
`hcoord_of_rigidityRows_affine`, `hspan_const_of_span_eq`, `hcoord_const`, the
affine `exists_good_realization`, the intermediate `hglue_of_genericityDevice`)
are *removed*: the constant-family path is now packaged once in
`exists_good_realization_const`, and `hglue_of_realization` folds in the old
`hglue_of_genericityDevice` arithmetic directly. The surviving Case-I chain is
`exists_good_realization{,_const}` → `hglue_of_realization` →
`hglue_of_independent_rigidityRows` → `hglue_of_forest` (each a genuine reduction,
no longer single-use affine plumbing).

**Route (a) analytic core (commit `86f1221`, unchanged)** — four upstream-eligible
mirror bricks (axiom-clean): `MvPolynomial.exists_eval_ne_zero`
(`…/MvPolynomial/Funext.lean`), and in `…/Matrix/Rank.lean`:
`Matrix.exists_linearIndependent_rows_specialize`,
`exists_le_finrank_span_polynomial`, `exists_finrank_dualCoannihilator_polynomial`.

The full inventory of landed green bricks — the `R(G,p)` coannihilator
coordinatization, the rigid-block forest linear-algebra, general position /
moment-curve / `ofParam`, the realization-motive producers, the
block-pin↔rigidity bridges, the `endsOf` graph selector — is in the
*Lemma checklist*.

## Architectural choices made up front

- **Forward-mode, node beside the consumers.** A single `lem:genericity-device`
  node (its own `sec:molecular-algebraic-induction-genericity` subsection) that
  the Phase-21 consumers `\uses`. The Lean has grown into new mirror files; if
  it grows further, split into its own `.lean`/`.tex`.
- **Discharge the consumers' explicit hypotheses.** Each Phase-21 node is
  GREEN-modulo-21b with the device's conclusion taken as a named hypothesis
  (`hglue`/`hspan`/`hub`/`hgen`). The device must produce exactly those — this
  fixes the device's *target statement* (the consumer API) before its proof.

## Lemma checklist

Forward-mode: the authoritative node list is `algebraic-induction.tex`
(`sec:molecular-algebraic-induction-genericity`); tracked here for hand-off.
All `[x]` bricks are axiom-clean {propext, Classical.choice, Quot.sound}.

**Blueprint nodes:**
- [x] `lem:genericity-device` — **GREEN**. Genuine multivariate Claim 6.4, pinned to
  `exists_good_realization` + `exists_good_realization_const`.
- [ ] `lem:case-I-realization` — **RED**. Contraction splice (KT 6.2/6.6) attains
  full rank; the geometric Case-I to-do (Hand-off, item 1).
- [x] `lem:case-I` — the iff-realization (green; device dep now green).

**Analytic core — multivariate (genuine Claim 6.4, route (a)):**
- [x] `MvPolynomial.exists_eval_ne_zero` (`…/MvPolynomial/Funext.lean`) — nonzero
  `MvPolynomial σ ℝ` ⇒ non-vanishing point (contrapositive of `MvPolynomial.funext`).
- [x] `Matrix.exists_linearIndependent_rows_specialize` — polynomial-entry matrix:
  LI rows at `p₀` ⇒ `∃ p`, LI rows (bad set = zero locus of Gram-det poly).
- [x] `exists_le_finrank_span_polynomial` — vector rank-`#s` `∃`-form, abstract `W`.
- [x] `exists_finrank_dualCoannihilator_polynomial` — codimension dual,
  `∃ p, #s + dim coann ≤ finrank V`; **the engine the device is built on.**

**Analytic core — affine/univariate (special case, no longer used by the device):**
- [x] `…le_finrank_span_along_affine_path_cofinite` / `…finrank_dualCoannihilator_along_affine_path_cofinite`
  (`…/Matrix/Rank.lean`) — `{bad t}.Finite` form; the univariate predecessor, kept
  as a mirror but no longer consumed (the device is multivariate).

**Device + Case-I chain (`AlgebraicInduction.lean`) — multivariate (consolidated):**
- [x] `exists_good_realization` (multivariate keystone), `exists_good_realization_const`
  (constant-family closure), `hglue_of_realization` (folds the old affine
  `hglue_of_genericityDevice` arithmetic), `hglue_of_independent_rigidityRows`,
  `hglue_of_forest`. The affine device + bridges (`genericityDevice`,
  `hcoord_of_rigidityRows_affine`, `hspan_const_of_span_eq`, `hcoord_const`,
  `hglue_of_genericityDevice`) were removed.

**`R(G,p)` coordinatization & rigid-block rows (`RigidityMatrix.lean`):**
- [x] `screwDiff`/`hingeRow`/`rigidityRows` + `infinitesimalMotions_eq_dualCoannihilator`
  — `Z(G,p) = (span rigidityRows).dualCoannihilator`.
- [x] `finrank_hingeRowBlock` (per-edge count `D−1`), `linearIndependent_hingeRow`,
  `exists_independent_rigidityRows_of_edge`, `linearIndependent_hingeRow_star`,
  `linearIndependent_hingeRow_forest`, `exists_independent_rigidityRows_of_forest`
  (assembled `|J|·(D−1)` LI rows), `exists_finite_spanning_rigidityRows`.

**Graph-side / geometric (`Induction.lean`, `AlgebraicInduction.lean`):**
- [x] `Graph.endsOf` (+ `isLink_endsOf`, `endsOf_eq_or_swap`) — canonical endpoint
  selector `ofParam` consumes (reusable; replaces inline `exists_isLink_of_mem_edgeSet`).
- [x] `IsGeneralPosition` + `supportExtensor_ne_zero_of_isGeneralPosition`;
  `momentCurve` + `withMomentNormals` + `isGeneralPosition_withMomentNormals`
  (dimension-free general position at an injective `param`);
  `ofParam` + `isGeneralPosition_ofParam` (from-scratch constructor).
- [x] `…_iff_pinnedMotionsOn_of_generalPosition`, `ofParam_rankHypothesis_iff_pinnedMotionsOn`
  — Case-I iff with purely-combinatorial signature `(G, ends)` + forest data + `hmatch`.

**Realization-motive producers + bridges (`AlgebraicInduction.lean`):**
- [x] `hasFullRankRealization_ofParam_of_pinnedMotionsOn` (`hpin`+`hmatch` form),
  `…_of_isInfinitesimallyRigid` (rigidity form), `hasFullRankRealization_of_pinnedMotionsOn`
  (internalizes injective `param` via mirror `Countable.exists_injective_real`).
- [x] `pinnedMotionsOn_eq_bot_of_isInfinitesimallyRigid` (+ `finrank_…`) — `hpin`
  from rigidity; `isInfinitesimallyRigid_of_le_withGraph` (graph-side leg);
  `isInfinitesimallyRigid_of_block_of_pinnedMotionsOn_eq_bot` (rigidity-producing
  converse); `isConstantOnBlock_of_isInfinitesimalMotion_of_rigid_subgraph`
  (`hblock` brick) + `isInfinitesimallyRigid_of_rigid_subgraph_of_pinnedMotionsOn_eq_bot`;
  `pinnedMotionsOn_withGraph_eq_of_block_internal` + `…_eq_bot_of_block_internal_rigid`
  (`hpin` from contraction rigidity).

**Consumer discharge targets (named hypotheses, supplied by the device):**
- [~] `hglue` (Case I) — all non-geometric inputs discharged; residual is the
  splice (Hand-off 3), bottoming on the multivariate device.
- [ ] `hspan` (Case II), `hub`/`hgen` (Prop 1.1) — reuse the device with a
  per-consumer bridge; target statements fixed in the Lean.
- [ ] projective assembly of `lem:cycle-realization` (four Lean pieces green;
  only the cited CW82/Whiteley99 projective assembly is non-Lean).

## Decisions made during this phase

### Phase-local choices and proof techniques
- **Coordinatize `R(G,p)` as a functional family, not a coordinate matrix.**
  Rows are `hingeRow u v r = r ∘ₗ screwDiff u v`; `Z(G,p) =
  (span rigidityRows).dualCoannihilator`. Keeps the screw space the graded-piece
  element (no `⋀^k ≅ ℝ^D` basis forced). Elaboration gotcha (`proj − proj`
  stuck): TACTICS-QUIRKS § 30. `ext`-on-`Module.Dual`: TACTICS-QUIRKS § 32.
- **Dualize the analytic engine once into the codimension shape.** Every consumer
  hypothesis is an upper bound `dim Z ≤ …` (codimension reading of `rank R ≥ …`).
  Taken once as the `…dualCoannihilator…` lemmas, stated additively to avoid
  `ℕ`-subtraction.
- **The device's *target statement* (consumer API) is fixed before its proof.**
  The device lands with `hcoord` *receiving* the functional family — this pinned
  the consumer-facing shape early, validated against the consumer API before the
  multivariate proof was wired in.
- **The constant family IS a valid multivariate family.** Route (a)'s "no real
  line is traversed" reading survives the multivariate rebuild: a single hand-built
  realization `F₀` is the constant family `F p = F₀` over `σ := Unit`, with
  polynomial coords the constants `c i j = C (φ (a i) j)` (`hg` = `eval_C`). This is
  `exists_good_realization_const`, the form the Case-I chain consumes — the
  multivariate keystone subsumes the old affine constant-path bridges.
- **`rw` over a `Submodule` equation under `finrank ℝ ↥(…)` trips the motive** —
  flip the equation and rewrite the hypothesis. → TACTICS-QUIRKS § 33.

### Promoted
- *Forward-mode + linear reduction chain → single-use wrapper sprawl; build the
  keystone first.* → `DESIGN.md` *Forward-mode reduction chains*.
- *`rw [hsub]` over a `Submodule` under `finrank ℝ ↥(…)` trips the motive; flip and
  rewrite the hypothesis.* → TACTICS-QUIRKS § 33.

## Blockers / open questions

- **Device: RESOLVED.** `lem:genericity-device` green on the multivariate engine
  `exists_finrank_dualCoannihilator_polynomial` (route (a)); consolidation of the
  old affine chain done in the same commit.
- **Open:** the geometric Case-I splice (`lem:case-I-realization`, Hand-off item 1)
  and the per-consumer wiring of the device for Case II (`hspan`) / Prop 1.1
  (`hub`/`hgen`) — the device's conclusion is the shape each needs, but each carries
  a per-consumer bridge to construct.

## Hand-off / next phase

The device is green. **The next concrete commit is the Case-I splice
(`lem:case-I-realization`).** Two work items remain, in dependency order.

1. **Splice realization** (`lem:case-I-realization`, red, KT eqs. 6.2/6.6) —
   *the next commit.* The geometric Case-I to-do: the contraction splice (`p₁` on
   `E(H)`, `p₂` on the interior, panel intersection
   `Π_{G/E(H),p₂}(u) ∩ Π_{H,p₁}(v)` on `δ_G(V(H))`) attains full rank, discharging
   `thm:theorem-55`'s `hcontract`. Bottoms on the now-green device — rigidity is
   panel-dependent, so the rigid-block placement and the contraction-transport both
   need generic max-rank. The reduction plumbing
   (`hasFullRankRealization_ofParam_of_isInfinitesimallyRigid`, the
   block-pin↔rigidity bridges, the `endsOf` selector) and the Case-I `hglue` chain
   (`hglue_of_forest`) are all landed; what's missing is the geometric construction
   + its generic rigidity, plus the `(G, ends)` gluing (orient block hinges along
   the spanning forest, link inter-block hinges to the contracted vertex) and the
   count `hmatch`.
2. **Per-consumer wiring of the device for Case II / Prop 1.1** — Case II's `hspan`
   (span-membership of base-pinned motions) and Prop 1.1's `hub`/`hgen` reuse the
   device's `∃ p, #s + dim Z(F p) ≤ D|V|` conclusion through a per-consumer bridge
   analogous to the Case-I `hglue_of_*` chain. Smaller than item 1; can follow it.

**Process lesson (don't repeat).** The single-use affine wrapper chain (now
collapsed) came from formalizing a *linear reduction* one hypothesis-discharge per
commit in forward mode. The fix: build the **keystone** (the multivariate device)
and validate the consumer API against it *first*, then collapse the affine bridges
into the constant-family closure. Promoted to `DESIGN.md` *Forward-mode reduction
chains*; also relevant to Phases 22–23.

**Also consumed by Phases 22–23** (Case III genericity, Claims 6.11/6.12); the
multivariate device pays forward (Case III bottoms on Lemma 2.1, Phase 17 green).

**Session note.** `origin/master` was inadvertently pushed once this session
(the local-only convention was otherwise kept; commits since are local). Match
author `bryangingechen@gmail.com`; do **not** push without asking.
