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

**Blueprint flipped to the honest KT §6.2 structure (2026-06-04); route (a)
multivariate analytic engine landed.** Two things happened this session:

1. **The device is genuinely *multivariate*.** The panel-matrix entries are
   degree-2 (bilinear in the per-vertex normals), so the consumers' realizations
   are *not* reached along any affine line — the affine/univariate engine landed
   earlier (`…along_affine_path_cofinite`) is only a special case and does **not**
   prove Claim 6.4. The genuine engine is multivariate Zariski-open
   non-vanishing (route (a)).
2. **Blueprint honesty flip.** `lem:genericity-device` had been prematurely marked
   `\leanok` (green) on that affine special case, with a 14-name wrapper-chain
   `\lean` pin; the Case-I prose embedded raw Lean identifiers. Rewritten to the
   honest decomposition (commit `ad7cb0d`).

Node status after the flip:
- `lem:genericity-device` — **RED**: genuine multivariate Claim 6.4. The landed
  `genericityDevice` + the `hglue_*` route-(a) chain are the affine special case
  only, now temporarily unblueprinted.
- `lem:case-I-realization` — **new RED node** (KT eqs. 6.2/6.6): the contraction
  splice attains full rank, discharging `thm:theorem-55`'s `hcontract`.
- `lem:case-I` — **green** but depends on red `lem:genericity-device`; pin trimmed
  to the two genuine iff lemmas.

**Route (a) analytic core landed (commit `86f1221`)** — four upstream-eligible
mirror bricks (axiom-clean, no `sorry`): `MvPolynomial.exists_eval_ne_zero`
(new file `…/MvPolynomial/Funext.lean`), and in `…/Matrix/Rank.lean`:
`Matrix.exists_linearIndependent_rows_specialize`,
`exists_le_finrank_span_polynomial`, and the consumer-facing codimension form
`exists_finrank_dualCoannihilator_polynomial` (`∃ p, #s + dim coann ≤ finrank V`).
Where the affine lemmas conclude `{bad t}.Finite`, these conclude `∃ p, good`
(via the non-vanishing point of a nonzero `MvPolynomial`, `MvPolynomial.funext`).
**Not yet wired** into the device/consumers — that is the next step (Hand-off 1).

The full inventory of landed green bricks — the affine engine, the `R(G,p)`
coannihilator coordinatization, the route-(a) `hglue` plumbing chain, the
rigid-block forest linear-algebra, general position / moment-curve / `ofParam`,
the realization-motive producers, the block-pin↔rigidity bridges, the `endsOf`
graph selector — is in the *Lemma checklist*. Most of the `hglue_* /
hasFullRankRealization_*` chain is single-use wrapper plumbing slated for
consolidation (Hand-off 2).

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
- [ ] `lem:genericity-device` — **RED**. Genuine multivariate Claim 6.4. The
  landed `genericityDevice` is the affine special case only; rebuild on the
  multivariate engine (Hand-off 1).
- [ ] `lem:case-I-realization` — **RED**. Contraction splice (KT 6.2/6.6) attains
  full rank; the geometric Case-I to-do (Hand-off 3).
- [x] `lem:case-I` — the iff-realization (green, depends on red device).

**Analytic core — multivariate (genuine Claim 6.4, route (a)):**
- [x] `MvPolynomial.exists_eval_ne_zero` (`…/MvPolynomial/Funext.lean`) — nonzero
  `MvPolynomial σ ℝ` ⇒ non-vanishing point (contrapositive of `MvPolynomial.funext`).
- [x] `Matrix.exists_linearIndependent_rows_specialize` — polynomial-entry matrix:
  LI rows at `p₀` ⇒ `∃ p`, LI rows (bad set = zero locus of Gram-det poly).
- [x] `exists_le_finrank_span_polynomial` — vector rank-`#s` `∃`-form, abstract `W`.
- [x] `exists_finrank_dualCoannihilator_polynomial` — codimension dual,
  `∃ p, #s + dim coann ≤ finrank V`; **the engine the device must be rebuilt on.**

**Analytic core — affine/univariate (special case, superseded as the device):**
- [x] `…le_finrank_span_along_affine_path_cofinite` / `…finrank_dualCoannihilator_along_affine_path_cofinite`
  (`…/Matrix/Rank.lean`) — `{bad t}.Finite` form; runs only on a single affine line.

**Device + route-(a) chain (`AlgebraicInduction.lean`) — affine special case:**
- [x] `genericityDevice` (codimension form, affine), `exists_good_realization`,
  `hglue_of_genericityDevice`, `hcoord_of_rigidityRows_affine`, `hcoord_const`,
  `hspan_const_of_span_eq`, `hglue_of_realization`,
  `hglue_of_independent_rigidityRows`, `hglue_of_forest`. *Single-use telescoping
  chain — consolidation target (Hand-off 2).*

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
  `genericityDevice` lands with `hcoord` *receiving* the functional family — this
  pinned the consumer-facing shape early. (See *Process lesson* in Hand-off: this
  was right, but discharging it via a per-hypothesis wrapper chain was not.)

### Promoted
- *Forward-mode + linear reduction chain → single-use wrapper sprawl; build the
  keystone first.* → `DESIGN.md` *Forward-mode reduction chains*.

## Blockers / open questions

- **Reuse-to-assess: RESOLVED.** Route (a) — the Phase-6/8 Gram-det mechanism,
  lifted to *rank* form and generalized *multivariate* via `MvPolynomial.funext`
  (the affine/univariate lift was insufficient: panel rows are bilinear, so the
  consumers' realizations are not on any affine line). Engine landed (`86f1221`).
- **Route a/b: RESOLVED → route (a) multivariate.** (Supersedes the earlier
  "degenerate constant path" reading: the constant/affine path only restates the
  rank at a hand-built realization and cannot *produce* a generic one, which is
  what the splice and the other consumers need.) Engine is the four multivariate
  bricks; the device must be rebuilt on `exists_finrank_dualCoannihilator_polynomial`.
- **Open:** wiring the multivariate engine into the device (Hand-off 1), the
  wrapper-chain consolidation (Hand-off 2), and the geometric splice (Hand-off 3).

## Hand-off / next phase

The blueprint states the honest target. Three work items remain, in dependency
order. **Item 1 is the smallest next concrete commit.**

1. **Rebuild the device multivariate** (`lem:genericity-device`, red → green) —
   *the next commit.* Restate `genericityDevice` / `exists_good_realization` in
   `AlgebraicInduction.lean` against the landed multivariate engine
   `exists_finrank_dualCoannihilator_polynomial`, replacing the affine/constant-path
   version. The coordinatization `hcoord` must express `(F p).infinitesimalMotions`
   as the coannihilator of a *polynomial-coordinate* functional family
   `g : (σ → ℝ) → ι → Module.Dual ℝ (α → ScrewSpace k)` with
   `φ (g p i) j = eval p (c i j)` — the panel coordinates `p` are the σ-vars, the
   degree-2 rigidity entries the `c i j`. Then re-pin `lem:genericity-device`
   green. The analytic content is done; this is coordinatization + statement-reshape.
2. **Consolidate the Lean wrapper chain** (no blueprint change). The ~17 names
   removed from the device/Case-I pins are a single-use telescoping
   `hglue_* / hasFullRankRealization_*` stack. Once the multivariate device lands,
   collapse them (inline single-use steps as `have`/`obtain`; keep only genuinely
   reusable API — the forest linear-algebra, general position, `ofParam`, the
   block-pin bound, the Case-I iff) and re-pin survivors.
3. **Splice realization** (`lem:case-I-realization`, red, KT eqs. 6.2/6.6) — the
   geometric Case-I to-do: the contraction splice (`p₁` on `E(H)`, `p₂` on the
   interior, panel intersection `Π_{G/E(H),p₂}(u) ∩ Π_{H,p₁}(v)` on `δ_G(V(H))`)
   attains full rank, discharging `thm:theorem-55`'s `hcontract`. Bottoms on the
   device (item 1) — rigidity is panel-dependent, so the rigid-block placement and
   the contraction-transport both need generic max-rank. The reduction plumbing
   (`hasFullRankRealization_ofParam_of_isInfinitesimallyRigid`, the
   block-pin↔rigidity bridges, the `endsOf` selector) is all landed; what's missing
   is the geometric construction + its generic rigidity, plus the `(G, ends)`
   gluing (orient block hinges along the spanning forest, link inter-block hinges
   to the contracted vertex) and the count `hmatch`.

**Process lesson (don't repeat).** The single-use wrapper chain (item 2's debt)
came from formalizing a *linear reduction* one hypothesis-discharge per commit in
forward mode. The fix, applied mid-session: build the **keystone** (the device)
and validate the consumer API against it *first*, then collapse. Promoted to
`DESIGN.md` *Forward-mode reduction chains*; also relevant to Phases 22–23.

**Also consumed by Phases 22–23** (Case III genericity, Claims 6.11/6.12); the
multivariate device pays forward (Case III bottoms on Lemma 2.1, Phase 17 green).

**Session note.** `origin/master` was inadvertently pushed once this session
(the local-only convention was otherwise kept; commits since are local). Match
author `bryangingechen@gmail.com`; do **not** push without asking.
