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

The abstract device and the entire Case-I `hglue` route are green. Landed
(all build/lint/checkdecls clean, axioms {propext, Classical.choice,
Quot.sound}; itemized with file locations + proof sketches in *Lemma
checklist*): the analytic engine + its codimension dual (`Rank.lean`),
the coannihilator coordinatization of `R(G,p)`
(`infinitesimalMotions_eq_dualCoannihilator`, `screwDiff`/`hingeRow`/
`rigidityRows`), the abstract `genericityDevice` (`dim Z(F t) ≤ D|V| − #s`
cofinitely), the route-(a) constant-path capstone
(`hglue_of_realization` via `hcoord_const`/`hspan_const_of_span_eq`),
input-(2) finite spanning family (`exists_finite_spanning_rigidityRows`),
and the per-edge → cross-hinge `hindep` bricks (`finrank_hingeRowBlock`,
`linearIndependent_hingeRow`, `exists_independent_rigidityRows_of_edge`,
`linearIndependent_hingeRow_star`, and now `linearIndependent_hingeRow_forest`
— the multi-body rigid block, hinges spanning many bodies via a private-endpoint
forest, the general `hindep` shape). The **route a/b decision is RESOLVED**
(route (a), constant path; bilinearity sidestepped — see *Decisions* /
*Blockers*). What remains is purely combinatorial-geometric: supply
`hglue_of_realization`'s remaining inputs (the realization `F₀` and the
matching-size independent subfamily `s`) for Case I, then the analogous
per-consumer bridges for Case II / Prop 1.1. **Next concrete commit: see
*Hand-off*** — extend the star combination to a rigid block whose hinges
span multiple bodies.

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

- [x] `lem:genericity-device` — Claim 6.4/6.9, codimension form:
  `genericityDevice` (`Molecular/AlgebraicInduction.lean`). Along an affine
  functional family coordinatizing the null spaces, a witnessed corank
  bounds `dim Z(G,p_t) ≤ D|V| − #s` cofinitely. Green; thin composition of
  the two bricks below + `finrank_screwAssignment`. (The per-consumer wiring
  — presenting the *panel* rows as such an affine family despite their
  bilinear dependence on the normals — is the residual open piece; see
  *Hand-off*.)
- [x] `LinearIndependent.le_finrank_span_along_affine_path_cofinite`
  (`Mathlib/LinearAlgebra/Matrix/Rank.lean`) — the rank-form analytic
  core: `finrank` of the span of an affine vector family is cofinitely
  bounded below by any rank witnessed once. Green; mirror lemma (no
  blueprint node).
- [x] `LinearIndependent.finrank_dualCoannihilator_along_affine_path_cofinite`
  (`Mathlib/LinearAlgebra/Matrix/Rank.lean`) — the codimension dual:
  the common kernel (`dualCoannihilator` of the span of an affine
  functional family) has `finrank` cofinitely bounded *above* by
  `finrank V − #s`. The consumer-facing shape (`dim ker ≤ value`).
  Green; mirror lemma (no blueprint node).
- [x] RigidityMatrix coordinatization (step (i),
  `Molecular/RigidityMatrix.lean`): `screwDiff`, `hingeRow`,
  `rigidityRows`, and `infinitesimalMotions_eq_dualCoannihilator`
  (`Z(G,p) = (span rigidityRows).dualCoannihilator`). Green; folded
  into the `def:rigidity-matrix` node's `\lean{...}` pin (no new node).

- [x] `exists_good_realization` + `hglue_of_genericityDevice`
  (`Molecular/AlgebraicInduction.lean`): the device's generic-point form
  (`∃ t, dim Z(F t) ≤ D|V| − #s`) and the Case-I block-triangular bridge
  (route (a): `hmatch` rank-match collapses it to `hglue`). Green; folded into
  `lem:genericity-device`'s `\lean{...}` pin (no new node).

- [x] `hcoord_of_rigidityRows_affine` (`Molecular/AlgebraicInduction.lean`):
  step-(i) bridge — discharges the device's `hcoord` from an affine functional
  family whose span equals `span (rigidityRows (F t))` at every `t` (`hspan`),
  via `infinitesimalMotions_eq_dualCoannihilator`. Reduces the per-consumer
  `hcoord` obligation to an *equality of spans*. Green; folded into
  `lem:genericity-device`'s `\lean{...}` pin (no new node).

- [x] `finrank_hingeRowBlock` (`Molecular/RigidityMatrix.lean`): per-edge row-count brick —
  `finrank ℝ (hingeRowBlock e) = screwDim k − 1` when `supportExtensor e ≠ 0` (transversal hinge),
  the basis-free `(D−1) × D` block-row count. The brick that counts the rigidity rows of a rigid
  block (source of the matching-size independent subfamily for Case-I `hindep`/`hmatch`). Green;
  folded into `def:hinge-row-block`'s `\lean{...}` pin (no new node).

- [x] `linearIndependent_hingeRow` (+ glue `screwDiff_surjective`, `hingeRow_eq_dualMap`)
  (`Molecular/RigidityMatrix.lean`): the Case-I `hindep` brick — for a genuine edge `u ≠ v`, an LI
  family of hinge-row-block functionals induces an LI family of rigidity rows `hingeRow u v (r i)`,
  via surjectivity of `screwDiff u v` + dual-map injectivity + `LinearIndependent.map'`. Turns
  independent supporting extensors of a rigid block (`exists_independent_panelSupportExtensor`,
  through the `(D−1)`-dim hinge-row block) into the independent rigidity-row subfamily
  `hglue_of_realization` needs. Green; folded into `def:rigidity-matrix`'s `\lean{...}` pin (glue
  lemmas skipped per the blueprint skip-glue rule).

- [x] `exists_independent_rigidityRows_of_edge` (`Molecular/RigidityMatrix.lean`): per-edge
  independent-rows brick — a single transversal hinge `e = uv` (`u ≠ v`, `supportExtensor e ≠ 0`)
  yields `D − 1` LI rigidity rows in `F.rigidityRows`. Composes `finrank_hingeRowBlock` (count) +
  `linearIndependent_hingeRow` (lift) through the new mirror lemma
  `Submodule.exists_linearIndependent_fin_of_finrank_eq` (basis-coercion in abstract-field form,
  avoiding the `whnf` blow-up on the exterior-power dual). The per-edge unit of Case-I
  `hindep`/`hmatch`. Green; folded into `def:rigidity-matrix`'s `\lean{...}` pin (mirror lemma
  skipped).

- [x] `linearIndependent_hingeRow_star` (`Molecular/RigidityMatrix.lean`): the cross-hinge `hindep`
  step — for a star of edges at a common body `v` with distinct other endpoints, per-hinge LI row
  families remain jointly LI, via the pin-a-body / disjoint-support count
  (`Fintype.sum_sigma` + `Finset.sum_eq_single` + `Fintype.linearIndependent_iff`). The substantive
  cross-hinge combination the hand-off flagged; `linearIndependent_hingeRow`'s single-edge argument
  does not extend (distinct `screwDiff`). Green; folded into `def:rigidity-matrix`'s `\lean{...}` pin
  (no new node).

- [x] `linearIndependent_hingeRow_forest` (`Molecular/RigidityMatrix.lean`): the multi-body
  generalization of the star — each hinge `j` oriented from a *private endpoint* `u j` (the child
  vertex of a spanning forest of the rigid block, `u` injective) to an arbitrary `other j`, with
  the forest-separation hypothesis `hsep : ∀ j j', other j ≠ u j'`. Per-hinge LI row families stay
  jointly LI by the *same* pin-a-body count, pinning `u j₀` (the star is the special case `u = w`,
  `other = const v`). This is the cross-hinge `hindep` for a genuine rigid block whose hinges span
  *multiple* bodies (the hand-off's next sub-brick). Green; folded into `def:rigidity-matrix`'s
  `\lean{...}` pin (no new node).

- [x] `exists_finite_spanning_rigidityRows` (`Molecular/RigidityMatrix.lean`): input (2) of
  `hglue_of_realization` — a finite family `a : Fin n → Dual ℝ (α → ScrewSpace k)` with
  `span (range a) = span F.rigidityRows`, from finite-dimensionality of the dual (`α` finite ⇒
  screw-assignment space finite-dim ⇒ dual finite-dim ⇒ every submodule FG) via
  `Submodule.fg_iff_exists_fin_generating_family`. Green; folded into `def:rigidity-matrix`'s
  `\lean{...}` pin (no new node).

- [x] `hspan_const_of_span_eq` + `hcoord_const` + `hglue_of_realization`
  (`Molecular/AlgebraicInduction.lean`): the **route-(a) constant-path** discharge.
  `hcoord_const` gives the device's `hcoord` for the constant family `F t = F₀`
  (`b = 0`) from any finite family spanning `rigidityRows F₀`; `hglue_of_realization`
  composes it into `hglue_of_genericityDevice` to land Case I's `hglue` inequality at
  a single hand-built realization `F₀` (witness from
  `exists_independent_panelSupportExtensor`, no path construction). Green; folded into
  `lem:genericity-device`'s `\lean{...}` pin (`hcoord_const`, `hglue_of_realization`).

The consumer-side discharge targets (each currently a named hypothesis
in the Phase-21 Lean, to be supplied by the device):
- [~] `hglue` for Case I — block-triangular generic gluing
  (`finrank Z ≤ D + finrank (pinnedMotionsOn s)`). **Route-(a) capstone done**
  (`hglue_of_realization` via constant path `hcoord_const` /
  `hspan_const_of_span_eq`): the `hglue` inequality holds at a single hand-built
  realization `F₀`, all affine-path plumbing discharged. The finite spanning row family `a`
  (`hspanrows`) is now also discharged generically by `exists_finite_spanning_rigidityRows` for any
  `F₀`. The `hindep` *bridge* is now also in hand (`linearIndependent_hingeRow`): per genuine edge,
  independent extensors → independent rigidity rows. Residual is purely combinatorial-geometric —
  exhibit the realization `F₀` and the matching-size independent subfamily `s` from the contraction
  realization + rigid block (combine `linearIndependent_hingeRow` across the block's hinges for
  `hindep`, count via `finrank_hingeRowBlock` for `hmatch`); no path construction remains.
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
- **Reuse-to-assess resolved: rank-form of the Phase-8 Gram-det
  machinery, not a fresh perturbation.** The cycle-genericity *existence*
  (independent supporting extensors) was already purely
  exterior-algebraic in Phase 21 (`exists_independent_panelSupportExtensor`,
  a basis choice on `⋀²`, no perturbation). What remains — the device's
  actual content — is *generic-max-rank attainment*: each consumer
  hypothesis (`hglue` rank-`≤`, `hspan` span-membership, `hub`/`hgen`)
  fails pointwise but holds at a generic point. That *is* the Phase-8
  polynomial-root-set mechanism (`finite_setOf_…_along_affine_path`),
  but the Phase-8 lemmas stop at the full-rank/LI case; the device needs
  the `finrank ≥ r` lower-bound case. So: **reuse the mechanism, lift it
  to rank form**. First brick:
  `LinearIndependent.le_finrank_span_along_affine_path_cofinite` — a
  maximal LI subfamily witnessing `finrank ≥ #s` at `t₀` stays LI
  cofinitely (the LI lemma on the subfamily) and an LI subfamily of size
  `#s` forces full-span `finrank ≥ #s`. Mirror-directory, upstream-
  eligible, beside its LI sibling; no blueprint node (mirror lemma).
- **Dualize the analytic engine once, into the consumer-facing
  codimension shape.** Every consumer hypothesis (`hglue`/`hgen`/`hub`)
  is an *upper* bound on a null-space dimension (`dim Z(G,p) ≤ …`), the
  codimension reading of `rank R ≥ …`, not a span lower bound. Rather
  than re-derive the rank-nullity flip at each consumer, the dual is
  taken once as a mirror lemma:
  `finrank_dualCoannihilator_along_affine_path_cofinite`. The kernel of
  an affine functional family is the `dualCoannihilator` of the span of
  the functionals (`Submodule.coe_dualCoannihilator_span`), and span +
  coann have complementary finrank at *every* `t`, so the span brick's
  "≥ #s cofinitely" becomes "coann ≤ finrank V − #s cofinitely"
  verbatim. Conclusion stated additively (`finrank V < #s + finrank
  coann`) to avoid `ℕ`-subtraction.
- **Coordinatize `R(G,p)` as a functional family, not a coordinate
  matrix.** Step (i): the rows are `hingeRow u v r = r ∘ₗ screwDiff u v`
  on `α → ScrewSpace k` (`screwDiff = proj u − proj v`), one per
  link × hinge-row-block element; `rigidityRows` is their set, and
  `infinitesimalMotions_eq_dualCoannihilator` reads `Z(G,p)` off as
  `(span rigidityRows).dualCoannihilator`. This keeps the screw space the
  graded-piece element (no `⋀^k ≅ ℝ^D` basis forced) and matches the
  coannihilator brick's shape exactly. Folded into `def:rigidity-matrix`
  (forward-mode plumbing for an existing node, not a new node), parallel
  to the two Rank.lean bricks being node-free mirror lemmas.
  Elaboration gotcha (`proj − proj` stuck): TACTICS-QUIRKS § 30.
- **The abstract device is `genericityDevice`: one lemma, `hcoord` carries
  the affine family.** Rather than wire the device inseparably into the
  first consumer, it lands as a standalone framework-facing lemma whose
  `hcoord` hypothesis *receives* the affine functional family
  `t ↦ a i + t • b i` coordinatizing each `(F t).infinitesimalMotions`.
  This fixes the device's target shape (the consumer-facing
  `dim Z ≤ D|V| − #s` cofinitely) before committing to a wiring shape, and
  isolates the genuinely-open piece (building the affine family from
  *panel* normals) as the consumer's obligation, not the device's. The
  device proof is then a 3-line composition of the two bricks +
  `finrank_screwAssignment`. Why this and not "wire Case I first": the
  panel rows are *bilinear* (degree-2) in the normals, so there is no
  single affine path to feed Case I's `hglue` without first choosing a
  restriction — the assessment the hand-off flagged. Landing the abstract
  device makes that assessment explicit and unblocks all four consumers
  uniformly once the affine-presentation route is chosen.

## Blockers / open questions

- **Reuse-to-assess: RESOLVED** (see *Decisions made*). The device
  reuses the Phase-8 Gram-det polynomial-root-set mechanism, lifted to
  rank form, in both the span and codimension shapes. Both bricks
  landed.
- **Route a/b decision RESOLVED: route (a), degenerate constant path.** The
  bilinearity caveat (a generic line through normal-space gives a quadratic
  row family) is *sidestepped, not solved* — Case I's witness realization is
  hand-built by `exists_independent_panelSupportExtensor` (a `⋀²` basis
  choice, not perturbation), so no real line is traversed: the device runs on
  `F t = F₀` (`b = 0`) and reads off the corank at the one realization. Route
  (b) (multivariate Zariski-open) is unneeded for Case I, but may be cleaner
  if a future consumer genuinely requires a non-constant path.
- **The single open piece for Case I is now purely combinatorial-geometric**:
  supplying `hglue_of_realization`'s inputs — the single realization `F₀`, a
  *finite* family `a` spanning `rigidityRows F₀`, and an independent subfamily `s`
  of the matching size `#s = D(|V|−1) − dim Z_s` (`hspanrows` + `hindep` +
  `hmatch`) — from the contraction realization plus the rigidly-placed block
  `V(H)`. No affine-path construction remains.

## Hand-off / next phase

The abstract device `lem:genericity-device` (`genericityDevice`) and the
full Case-I `hglue` route are GREEN (route-(a) constant path; see *Current
state* + *Blockers* + *Lemma checklist*). Input (2) (`exists_finite_spanning_rigidityRows`)
and the per-edge/cross-hinge `hindep` bricks are landed, so no affine-path
or finite-spanning-family construction remains for any consumer — what's
left is the per-consumer geometric assembly of `hglue_of_realization`'s
remaining inputs.

**Smallest next concrete commit: supply `hglue_of_realization`'s *remaining* inputs for Case I (the
geometric construction).** From the contraction realization (`G/E(H)` at its inductive
`RankHypothesis`) plus the rigid block `V(H)` placed rigidly, exhibit:
1. the single realization `F₀` (a `BodyHingeFramework`/`PanelHingeFramework`-via-`toBodyHinge`), and
2. an independent subfamily `s` of the finite spanning family `a` (from
   `exists_finite_spanning_rigidityRows`) with `#s = D(|V|−1) − dim Z_s` (`hindep` + `hmatch`), the
   independent rigidity rows coming from `exists_independent_panelSupportExtensor` through the
   hinge-row block — each transversal hinge contributing `D − 1` rows (`finrank_hingeRowBlock`, now
   green).
No affine-path construction and no finite-spanning-family construction remain. This is the
genuinely-geometric Case-I assembly (KT §6.2/6.5); likely more than one commit — assess once `F₀` is
in hand and `s` is being matched to the corank. The per-edge and cross-hinge sub-bricks toward (2)
are now landed: `linearIndependent_hingeRow` (independent supporting extensors → independent
`hingeRow u v r` per edge), `exists_independent_rigidityRows_of_edge` (one transversal hinge ⇒
`D − 1` LI rigidity rows in `rigidityRows`), and now `linearIndependent_hingeRow_star` (the
cross-hinge combination: rows from *distinct* hinges at a common pinned body, distinct other
endpoints, are jointly LI by the pin-a-body / disjoint-support count), and now
`linearIndependent_hingeRow_forest` (the multi-body extension: a rigid block whose hinges span
*multiple* bodies, oriented along a private-endpoint spanning forest, jointly LI by the same
pin-a-body count). **Next: assemble the forest `hindep` into the matching-size subfamily `s` and
match the count.** Combine `exists_independent_rigidityRows_of_edge` across the spanning forest's
transversal hinges through `linearIndependent_hingeRow_forest`, then match
`#s = D(|V|−1) − dim Z_s` (`hmatch`) using the `D−1` per-edge count against the contraction's
inductive rank, and exhibit `F₀`. (For the genuine cycle case, the `m ≤ D` extensor-independence of
`lem:cycle-realization` + `exists_independent_panelSupportExtensor` general position controls the
cross-body interaction; `eq_zero_of_mem_span_singleton_of_sum_eq_zero` is the existing screw-space
telescoping core.) The other
consumers (`hspan` for Case II, `hgen` for Prop 1.1) reuse the same constant-path chain
(`hcoord_const` → device) with an analogous per-consumer bridge; the device's *target statements*
are fixed (the named hypotheses in `AlgebraicInduction.lean`).

**Update (2026-06-03, this commit):** the cross-hinge `hindep` brick is now complete in its
general form — `linearIndependent_hingeRow_forest` covers a rigid block whose hinges span multiple
bodies (private-endpoint forest, the star being the one-common-body special case). All `hindep`
sub-bricks toward (2) are landed. The **smallest next concrete commit** is now the `hmatch` count
plus the `F₀` exhibit: (a) wire `exists_independent_rigidityRows_of_edge` across a spanning
forest's transversal hinges through `linearIndependent_hingeRow_forest` to produce the
matching-size independent subfamily `s` with `#s = D(|V|−1) − dim Z_s` (the per-edge `D−1` count
against the contraction's inductive `RankHypothesis`); and (b) exhibit the realization `F₀` (a
`PanelHingeFramework`-via-`toBodyHinge`) from the contraction realization plus the rigidly-placed
block `V(H)`. (a) and (b) together discharge `hglue_of_realization`'s remaining inputs for Case I
(KT §6.2/6.5); likely more than one commit — assess once the forest `hindep` is assembled into `s`
and the `D−1` count is being matched to the corank.

**Also consumed by Phases 22–23** (Case III candidate-framework
genericity, Claims 6.11/6.12), so building the device standalone pays
forward; for Case III's share it bottoms on Lemma 2.1 (Phase 17 green).
