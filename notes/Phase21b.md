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

**Analytic engine landed in both span (rank) and coannihilator
(codimension) form (2026-06-03).** The reuse-to-assess is resolved
(see *Decisions made* below): the device reuses the Phase-6/8 Gram-det
polynomial-root-set machinery, but at the *rank* level rather than the
full-rank (LI) level the Phase-8 lemmas stop at. Two bricks now sit in
`Mathlib/LinearAlgebra/Matrix/Rank.lean` (upstream-eligible, beside
their LI-form sibling):
- `LinearIndependent.le_finrank_span_along_affine_path_cofinite` — the
  *rank* form: finrank of the span of an affine vector family is
  cofinitely bounded *below* by any rank witnessed once.
- `LinearIndependent.finrank_dualCoannihilator_along_affine_path_cofinite`
  — the *codimension/null-space* dual: the common kernel (packaged as
  the `dualCoannihilator` of the span of an affine functional family)
  has finrank cofinitely bounded *above* by `finrank V − #s`, via the
  complementary-dimension identity `finrank coann + finrank span =
  finrank V` (`Subspace.finrank_dualCoannihilator_eq` +
  `Subspace.finrank_add_finrank_dualAnnihilator_eq` +
  `Subspace.dual_finrank_eq`). This is the exact shape the consumers
  carry (each is a `dim Z(G,p) ≤ …` upper bound on a null-space dim,
  the codimension reading of `rank R ≥ …`).
Both green, build warning-clean + lint clean, axioms {propext,
Classical.choice, Quot.sound}. The `lem:genericity-device` node stays
red (this is infrastructure, not yet the device's API); the analytic
engine is now complete in the consumer-facing shape — what remains is
the RigidityMatrix coordinatization that connects `infinitesimalMotions`
to a `dualCoannihilator` of a panel-parametrized functional family (see
*Hand-off*).

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

## Blockers / open questions

- **Reuse-to-assess: RESOLVED** (see *Decisions made*). The device
  reuses the Phase-8 Gram-det polynomial-root-set mechanism, lifted to
  rank form, in both the span and codimension shapes. Both bricks
  landed.
- **Open: coordinatizing `infinitesimalMotions` as a `dualCoannihilator`
  of a panel-parametrized functional family** (the split-off step (i),
  now the *next* concrete commit — see *Hand-off*). The two bricks
  parametrize by a single scalar `t` along an affine path `a i + t•b i`.
  The panel-hinge rigidity matrix's entries are polynomials in *many*
  panel coordinates (the per-vertex normals), not one scalar. To feed
  the consumers, the device must (a) express
  `F.infinitesimalMotions` as `dualCoannihilator (span rows)` with rows
  affine/polynomial in the panel coordinates, (b) pick an affine path
  through panel-coordinate space hitting the good realization
  `exists_independent_panelSupportExtensor` supplies, then (c) read the
  consumer hypothesis (`hglue`/`hspan`/`hub`) off the cofinite-`t`
  conclusion of `finrank_dualCoannihilator_along_affine_path_cofinite`.
  Whether a *single* affine path suffices or a multivariate Zariski-open
  argument is needed is still the thing to assess on contact for step
  (b) — the single-path route worked for Phase-8's uniform-generic
  placement (`exists_uniform_rowIndependent_placement`), so try it
  first. Step (a) is the load-bearing piece and is its own commit.

## Hand-off / next phase

**Smallest next concrete commit (the split-off step (i) plumbing):**
the abstract analytic engine is now complete in *both* the span (rank)
and coannihilator (codimension) forms; what is left to connect it to
the consumers is the RigidityMatrix coordinatization. Concretely:
express `F.infinitesimalMotions` (the basis-free
`IsInfinitesimalMotion` kernel) as the `dualCoannihilator` of the span
of an explicit, panel-coordinate-parametrized functional family on the
screw-assignment space `α → ScrewSpace k` — i.e. give a coordinatized
row-vector view of `hingeConstraint` / `hingeRowBlock` whose entries
are affine (indeed polynomial) in the per-vertex panel normals. This is
the step (i) plumbing the previous hand-off flagged as "its own brick";
it is the load-bearing new `RigidityMatrix.lean` work and is one
focused commit (a `LinearMap`/functional view of the per-edge hinge
row block + the identity `infinitesimalMotions = dualCoannihilator
(span rows)`).

Once that view lands, the per-consumer discharge is short: (ii) choose
an affine path through panel-coordinate space whose `t₀` is the good
realization `exists_independent_panelSupportExtensor` already supplies;
(iii) apply `finrank_dualCoannihilator_along_affine_path_cofinite` to
get cofinitely-many `t` with `dim Z(G,p_t) ≤ target`, pick one real `t`
off the finite bad set, and read off the consumer's hypothesis. Start
with **one** consumer — `hglue` for Case I
(`rankHypothesis_iff_finrank_pinnedMotionsOn`) is the cleanest target
since it is a single `finrank` inequality. The device's *target
statements* are fixed: the consumers' `hglue`/`hspan`/`hub`/`hgen`
hypotheses (see *Lemma checklist* + the named hypotheses in
`AlgebraicInduction.lean`).

**Also consumed by Phases 22–23** (Case III candidate-framework
genericity, Claims 6.11/6.12), so building the device standalone pays
forward; for Case III's share it bottoms on Lemma 2.1 (Phase 17 green).
