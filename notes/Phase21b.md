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
`linearIndependent_hingeRow_star`, `linearIndependent_hingeRow_forest`,
`exists_independent_rigidityRows_of_forest` — the assembled rigid-block form: a
spanning forest of `|J|` transversal hinges yields `(D−1)·|J|` independent rigidity
rows in `F.rigidityRows`). The **index gap is now closed**: the consumer bridge
`hglue_of_independent_rigidityRows` feeds *any* finite independent family `r : κ →
Dual` with `range r ⊆ span F₀.rigidityRows` (the forest rows) directly into the
`hglue` inequality — it concatenates `a := Sum.elim r a₀` (`a₀` from
`exists_finite_spanning_rigidityRows`), takes the subfamily at `s := range Sum.inl`
(= `r`, independent), so `hglue_of_realization`'s `hspanrows`/`hindep` are discharged
and only the count match `hmatch` (`Nat.card κ = D(|V|−1) − dim Z_s`) and the choice of
`F₀` remain. The **route a/b decision is RESOLVED** (route (a), constant path;
bilinearity sidestepped — see *Decisions* / *Blockers*). **As of this commit the last
*generic* reduction is also landed** (`hglue_of_forest`): it composes
`exists_independent_rigidityRows_of_forest` straight into
`hglue_of_independent_rigidityRows`, so the whole Case-I `hglue` reduces to the *forest
data itself* (the private-endpoint `u`/`other`/`e` of `V(H)`'s transversal hinges +
`Function.Injective u` / the separation `other j ≠ u j'` / transversality
`supportExtensor (e j) ≠ 0`) plus the count `hmatch` keyed to `|J|·(D−1)`. What remains is
purely geometric: exhibit the realization `F₀` (a `PanelHingeFramework`-via-`toBodyHinge`)
and its spanning-forest data + `hmatch` count for Case I, then the analogous per-consumer
bridges for Case II / Prop 1.1. The **first geometric brick is now landed**
(`IsGeneralPosition` + `supportExtensor_ne_zero_of_isGeneralPosition`): the panel-layer
general-position predicate and the transversality consequence discharging `hglue_of_forest`'s
`he` once the block's normals are in general position. What remains is the `F₀` *construction*
(gluing the contraction realization with the rigidly-placed block), the spanning-forest data
`u`/`other`/`e`, the count `hmatch`, and a general-position normal *assignment* for the block.
**Next concrete commit: see *Hand-off*.**

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

- [x] `exists_independent_rigidityRows_of_forest` (`Molecular/RigidityMatrix.lean`): the **assembled
  rigid-block `hindep`/`hmatch` family** — composes `exists_independent_rigidityRows_of_edge` (per
  edge `D−1` rows) with `linearIndependent_hingeRow_forest` (joint across the forest) to produce a
  single LI family of rigidity rows indexed by `Σ j, Fin (screwDim k − 1)`, all in `F.rigidityRows`.
  Cardinality `|J|·(D−1)` (`Nat.card_sigma`) is the matching-size subfamily `s` that
  `hglue_of_realization` consumes (`hindep` = the joint LI, `hmatch` count = `|J|·(D−1)`). Per-edge
  block bases via `choose` + `exists_linearIndependent_fin_of_finrank_eq`, witnessed as rows through
  `hlink`/block membership. Green; folded into `def:rigidity-matrix`'s `\lean{...}` pin (no new node).

- [x] `hglue_of_independent_rigidityRows` (`Molecular/AlgebraicInduction.lean`): the **consumer
  bridge closing the index gap** between the assembled forest family and the route-(a) capstone.
  `hglue_of_realization` wants the independent subfamily to index into the *spanning* family `a`;
  the forest rows `r : κ → Dual` instead live in `span F₀.rigidityRows` without being a subfamily of
  any enumeration. The bridge concatenates `a := Sum.elim r a₀` (`a₀` from
  `exists_finite_spanning_rigidityRows`): `range r ⊆ span (range a₀)` keeps the concatenation
  spanning (`hspanrows`), and the subfamily at `s := range Sum.inl` is exactly `r` (independent,
  reindexed via `Set.rangeSplitting` — FRICTION). So Case I now needs only `r` (the forest), the
  realization `F₀`, and the count `hmatch` (`Nat.card κ = D(|V|−1) − dim Z_s`). Green; folded into
  `lem:genericity-device`'s `\lean{...}` pin (route-(a) bridge, no new node).

- [x] `IsGeneralPosition` + `supportExtensor_ne_zero_of_isGeneralPosition`
  (`Molecular/AlgebraicInduction.lean`, `PanelHingeFramework` namespace): the **first geometric
  brick of the `F₀` exhibition** — the panel-layer general-position predicate (any two normals at
  distinct bodies are linearly independent) and its consequence: every hinge `e` joining two
  distinct bodies (`(P.ends e).1 ≠ (P.ends e).2`) has `P.toBodyHinge.supportExtensor e ≠ 0`. This is
  the realization-side source of `hglue_of_forest`'s transversality input `he` (and of
  `exists_independent_rigidityRows_of_edge`'s `he`): once the rigid block's normals are in general
  position, every forest hinge is genuine. One-liner (`mpr` of `toBodyHinge_supportExtensor_ne_zero_iff`
  + pairwise independence). Green; folded into `def:panel-hinge-framework`'s `\lean{...}` pin. **Does
  not yet construct** a general-position assignment for arbitrary `|α|` — that is the polynomial
  non-vanishing belonging with the genericity argument (standard-basis vectors only cover
  `|α| ≤ k+2`), deliberately left to the `F₀`-glue commit.

- [x] `hglue_of_forest` (`Molecular/AlgebraicInduction.lean`): the **last generic Case-I
  reduction** — composes `exists_independent_rigidityRows_of_forest` (the rigid block's
  `(D−1)·|J|` independent rigidity rows, indexed by `Σ _ : J, Fin (screwDim k − 1)`) directly into
  `hglue_of_independent_rigidityRows`, reducing the whole Case-I `hglue` to the *forest data* (the
  private-endpoint spanning forest `u`/`other`/`e` of `V(H)`'s transversal hinges, with `hu`/`hsep`/
  `he`) plus the count `hmatch` keyed to `Nat.card J * (screwDim k − 1)`. Cardinality
  `Nat.card (Σ _ : J, Fin (D−1)) = |J|·(D−1)` is `simp [Nat.card_eq_fintype_card]` after
  `Fintype.ofFinite J`; row membership is `Submodule.subset_span ∘ hmem`. This is the last
  graph-and-hinge-agnostic step; what remains is the geometric `F₀` exhibition. Green; folded into
  `lem:genericity-device`'s `\lean{...}` pin (route-(a) bridge, no new node).

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
  independent extensors → independent rigidity rows. The **index gap is now closed**
  (`hglue_of_independent_rigidityRows`): the assembled forest family `r`
  (`exists_independent_rigidityRows_of_forest`) feeds the `hglue` inequality directly via the
  `Sum.elim r a₀` concatenation, discharging `hspanrows` + `hindep` for *any* `F₀`. **The last
  generic reduction is `hglue_of_forest`**: it composes the forest assembly into that bridge, so the
  whole `hglue` now reduces to the forest *data* (`u`/`other`/`e` + `hu`/`hsep`/`he`) plus the count
  `hmatch` keyed to `|J|·(D−1)`. Residual is purely geometric — exhibit the realization `F₀` and its
  spanning-forest data + the count `hmatch` (`|J|·(D−1) = D(|V|−1) − dim Z_s`) from the contraction
  realization + rigid block; no path construction, no spanning-family/subfamily-index bookkeeping,
  and no forest-assembly plumbing remains.
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
- **The single open piece for Case I is now purely geometric**: the index gap is
  closed by `hglue_of_independent_rigidityRows`, and the forest assembly is composed in by
  `hglue_of_forest`, so all that remains is to exhibit the realization `F₀` *together with* its
  spanning-forest data (`u`/`other`/`e` + `hu`/`hsep`/`he`) and the count `hmatch`
  (`|J|·(D−1) = D(|V|−1) − dim Z_s`) from the contraction realization plus the rigidly-placed block
  `V(H)`. No affine-path, spanning-family, subfamily-index, or forest-assembly construction remains
  — only the geometric `F₀` + forest-data exhibition.

## Hand-off / next phase

The abstract device `lem:genericity-device` (`genericityDevice`) and the full Case-I `hglue`
*plumbing* are GREEN (route-(a) constant path; see *Current state* + *Blockers* + *Lemma
checklist*). All non-geometric inputs are now discharged: the affine path (constant,
`hcoord_const`), the finite spanning family (`exists_finite_spanning_rigidityRows`), the assembled
forest `hindep` family (`exists_independent_rigidityRows_of_forest`, `(D−1)·|J|` LI rows), the
**index gap** between them (`hglue_of_independent_rigidityRows`), and — as of this commit — the
**forest assembly composed in** (`hglue_of_forest`: the whole Case-I `hglue` now reduces to forest
*data* `u`/`other`/`e` + `hu`/`hsep`/`he` plus the count `hmatch` keyed to `|J|·(D−1)`). This was the
last generic (graph-and-hinge-agnostic) reduction.

The **first geometric brick** landed this commit: `IsGeneralPosition` (pairwise-independent panel
normals) + `supportExtensor_ne_zero_of_isGeneralPosition` (every distinct-endpoint hinge transversal
under it), which sources `hglue_of_forest`'s `he` once the block's normals are in general position.

**Smallest next concrete commit: a general-position normal *assignment* for the rigid block** — a
constructor producing a `P.normal : α → Fin (k+2) → ℝ` (or its restriction to `V(H)`) satisfying
`IsGeneralPosition`. Standard-basis vectors cover only `|α| ≤ k+2`; the general case is the
polynomial non-vanishing (a moment-curve / Vandermonde assignment is the clean witness — `t ↦
(1, t, t², …)` at distinct reals gives pairwise-independent normals for any `|α|`). Landing this
isolates the genericity from the gluing. After it: exhibit (a) the single realization `F₀` (a
`PanelHingeFramework`-via-`toBodyHinge`) gluing the contraction realization (`G/E(H)` at its
inductive `RankHypothesis`) with the rigidly-placed block `V(H)`, (b) the private-endpoint spanning
forest `u`/`other`/`e` of `V(H)`'s transversal hinges (`u` injective, `other j ≠ u j'`, `he` now from
`supportExtensor_ne_zero_of_isGeneralPosition`), and (c) the count `hmatch` (`|J|·(D−1) = D(|V|−1) −
dim Z_s`) against the contraction's inductive `RankHypothesis`. Feed (a)+(b)+(c) through
`hglue_of_forest` → `toBodyHinge_rankHypothesis_iff_finrank_pinnedMotionsOn`. This is the
genuinely-geometric Case-I assembly (KT §6.2/6.5); likely more than one commit — assess once `F₀` is
in hand and the count is being matched to the corank. (For the genuine cycle case, the `m ≤ D` extensor-independence of
`lem:cycle-realization` + `exists_independent_panelSupportExtensor` general position controls the
cross-body interaction; `eq_zero_of_mem_span_singleton_of_sum_eq_zero` is the screw-space
telescoping core.) The other consumers (`hspan` for Case II, `hgen` for Prop 1.1) reuse the same
constant-path chain (`hcoord_const` → device) with an analogous per-consumer bridge; the device's
*target statements* are fixed (the named hypotheses in `AlgebraicInduction.lean`).

**Also consumed by Phases 22–23** (Case III candidate-framework
genericity, Claims 6.11/6.12), so building the device standalone pays
forward; for Case III's share it bottoms on Lemma 2.1 (Phase 17 green).
