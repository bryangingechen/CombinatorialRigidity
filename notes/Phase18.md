# Phase 18 — Panel-hinge rigidity matrix `R(G,p)` (work log)

**Status:** in progress (just opened).

This is the **second phase of the molecular-conjecture program**
(Phases 17–26). The program-level plan — target, five-strata
architecture, phase breakdown, reuse map, risk register — lives in
`notes/MolecularConjecture.md`; read that first (especially the
*Phase 18* per-phase detail and risk-register items 3 and 4). This file
is the Phase-18 work log only.

## Current state

Phase 18 is **in progress**. The leaf node `def:hinge-constraint` has
**landed** (`Molecular/RigidityMatrix.lean`); the remaining
`sec:molecular-rigidity-matrix` nodes are still red.

Landed so far:
- `def:hinge-constraint` — `Molecular/RigidityMatrix.lean`:
  `BodyHingeFramework k α β` (multigraph `Graph α β` + per-edge hinge
  `β → Fin k → Fin (k+1) → ℝ`, i.e. `k = d−1` points spanning the
  `(d−2)`-affine hinge), `supportExtensor` = Phase 17's
  `affineSubspaceExtensor (hinge e)` (the `C(·)`), and `hingeConstraint`
  (`S u − S v ∈ Submodule.span ℝ {C(p e)}`). Screw space `ScrewSpace k =
  ExteriorAlgebra ℝ (Fin (k+2) → ℝ)` carried as the full algebra element,
  so `span C(p(e))` is literally a `Submodule` — no coordinate `ℝ^D`
  identification yet. File wired into `CombinatorialRigidity.lean`.

The opening commit (prior) created this work log, opened the
`sec:molecular-rigidity-matrix` dep-graph (all red), added the two bib
entries (`whiteWhiteley1987` [29], `jacksonJordan2009` [15]), and ran the
phase-open status-surface sync.

The next concrete commit is the next red node `def:hinge-row-block` —
`r(p(e))`, a basis of `(span C(p(e)))^⊥ ⊆ ℝ^D`, restating the hinge
constraint as `D−1` linear equations `(S u − S v) · r_i(p(e)) = 0`. This
forces the concrete `⋀^k ℝ^(k+2) ≅ ℝ^D` coordinate identification
(carrier-compatibility open question below); decide it when this node
lands.

## Scope (Phase 18 only)

Katoh–Tanigawa 2011 §2.2–2.4 (plus the §5 rank lemmas that the
algebraic induction reuses): the **genuine** panel-hinge / body-hinge
rigidity matrix `R(G,p)`. Stratum 2 of the five (see
`notes/MolecularConjecture.md`). Concretely:
- the hinge constraint via the supporting `(d−1)`-extensor `C(p(e))`
  (Phase 17), the orthogonal-complement block `r(p(e))` (`(D−1)×D`),
  the `(D−1)|E| × D|V|` block matrix `R(G,p)`, the null space `Z(G,p)`;
- the `D` trivial motions `S*_i`, the `rank R ≤ D(|V|−1)` bound, degree
  of freedom, infinitesimal rigidity, generic realizations;
- the three rank lemmas: **5.1** (deleting one body's `D` columns
  preserves rank — most-reused), **5.3** (two general-position parallel
  hinges → full block `D`, base case), **5.2** (rank
  lower-semicontinuity under a one-parameter panel rotation);
- **reconciliation with Phase 16's reduction-form Prop 1.1**: the rank
  form `rank R(G,p) = D(|V|−1)` reproduces the existence form
  (`(δ−1)·G` is `(δ,δ)`-tight, `thm:body-hinge-tay`), `δ = D`.

`R(G,p)` **supersedes** Phase 16's reduction-only `BodyHingeFramework`
(standard-basis witness, no geometry). Keep the Phase-16 def as the
existence form; the new one is the rank form. The reconciliation is real
work, not a rename.

Reuse: Phase 4 `Framework.lean` (rigidity map, infinitesimal rigidity);
Phase 6–8 rank/genericity machinery + the
`Mathlib/LinearAlgebra/Matrix/Rank.lean` Gram-det LI mirrors; Phase 17
`extensor` / `affineSubspaceExtensor`; Phase 13/14 union +
Tutte–Nash-Williams for the Prop-2.3 corank bridge; Phase 16
`edgeMultiply` / `bodyHingeMult` for the Prop 1.1 reconciliation.
Carrier: mathlib core `Graph α β` (Phases 13–16 carrier).

## Architectural choices made up front

- **Extend the molecular chapter, don't open a new one.** Phase 18 is
  the second phase of the same program and the same blueprint chapter
  (`molecular.tex`); its nodes go in a new `\section{}`
  (`sec:molecular-rigidity-matrix`) after the Phase-17 §2.1 sections,
  forward-mode (red until Lean lands). Matches the program structure in
  `notes/MolecularConjecture.md`.
- **Screw carrier `ℝ^D`, `D = (d+1 choose 2)`.** Infinitesimal motions
  are `D`-dimensional screw centers `S(v) ∈ ℝ^D`, matching Phase 17's
  extensor space `⋀^(d−1) ℝ^(d+1) ≅ ℝ^D` and the body-bar/body-hinge
  `δ = bodyBarDim n`. Decide the concrete identification when the first
  rank-bearing node lands.
- **Lemma 5.2 (risk register item 3): prefer genericity over analytic
  perturbation.** Entries of `R(G,p)` are polynomials in the panel
  coordinates, so a nonvanishing minor at one realization persists
  generically (the Phase-6/8 genericity idiom). Reconfirm when the node
  lands; only fall back to analytic semicontinuity if that stalls.
- **Externals (risk register item 4): formalize the Prop 1.1
  reconciliation via the project's own union machinery, not by
  axiomatizing J–J [15].** The corank bridge `def(G̃) = corank M(G̃)`
  is the `D`-fold graphic union of Phases 13/14; the upper bound the
  conjecture needs is already in Phase 16's `edgeMultiply_isSparse_iff`.
  Decide per-node whether Lemma 5.1's [29] pin-a-body fact is proved or
  taken as hypothesis (it is reused heavily downstream).

## Lemma checklist

Forward-mode: the authoritative dep-graph is the
`sec:molecular-rigidity-matrix` section of
`blueprint/src/chapter/molecular.tex`. This list mirrors its nodes in
intended dependency order; flip each `\leanok` (and add `\lean{}`) as
the Lean lands.

- [x] `def:hinge-constraint` — body-hinge framework `(G,p)` +
      `S(u) − S(v) ∈ span C(p(e))`. **Landed**
      (`Molecular/RigidityMatrix.lean`).
- [ ] `def:hinge-row-block` — `r(p(e))`, a basis of
      `(span C(p(e)))^⊥`; constraint as `(D−1)` linear equations.
      **Next commit.**
- [ ] `def:rigidity-matrix` — `R(G,p)`, the `(D−1)|E| × D|V|` block
      matrix; `Z(G,p) = ker R`.
- [ ] `lem:trivial-motions-rank-bound` — the `D` trivial motions
      `S*_i`; `rank R ≤ D(|V|−1)`, equality iff infinitesimally rigid.
- [ ] `def:dof-generic` — degree of freedom `D(|V|−1) − rank R`;
      generic realization.
- [ ] `lem:rank-delete-vertex` — **Lemma 5.1** (pin a body, delete `D`
      columns, rank unchanged); [29] White–Whiteley.
- [ ] `lem:rank-parallel-full` — **Lemma 5.3** (two general-position
      parallel hinges → full block `D`); via `lem:extensor-independence`.
- [ ] `lem:rank-rotation-semicont` — **Lemma 5.2** (rank
      lower-semicontinuity under a panel rotation; genericity form).
- [ ] `prop:rigidity-matrix-prop11` — reconcile rank form with Phase
      16's existence form (`thm:body-hinge-tay`); via Prop 2.3
      [15] + Phase 13/14 union.

## Decisions made during this phase

### Phase-local choices and proof techniques
- **Reparametrize dimension `d = k+1`** (à la Phase 17's
  `omitTwoExtensor`). A hinge is `k = d−1` points in `ℝ^(k+1)`, the
  supporting extensor is a `k`-extensor in `⋀^k ℝ^(k+2)`. Clears the
  `d−1` / `d−2` `ℕ`-subtractions in the hinge / extensor arities; the
  `affineSubspaceExtensor (p : Fin k → Fin (k+1) → ℝ)` arity matches
  directly.
- **Screw center = full `ExteriorAlgebra` element**, not a coordinate
  vector in `ℝ^D` (`ScrewSpace k := ExteriorAlgebra ℝ (Fin (k+2) → ℝ)`).
  Then `span C(p(e))` is literally `Submodule.span ℝ {C(p e)}` and the
  hinge constraint is a `Submodule` membership — no `⋀^k ℝ^(k+2) ≅ ℝ^D`
  identification needed at this node. That identification is deferred to
  `def:hinge-row-block` / `def:rigidity-matrix`, where `r(p(e))` (a basis
  of the orthogonal complement in `ℝ^D`) forces it.
- **Body-hinge framework as a `Graph`-native `structure`** (graph +
  `hinge` field), mirroring Phase 16's `Graph.BodyHingeFramework` shape
  but in the `Molecular` namespace and carrying honest hinge *geometry*
  (the point family) rather than the reduction-only standard-basis
  witness. The two coexist (Phase 16 = existence form, Phase 18 = rank
  form); the reconciliation `prop:rigidity-matrix-prop11` is the real
  bridge, not a rename.

### Citations verified this phase
- **[29] White, N., Whiteley, W.**, *The algebraic geometry of motions
  of bar-and-body frameworks*, SIAM J. Algebraic Discrete Methods **8**
  (1987), no. 1, 1–32 (DOI 10.1137/0608001). Added as
  `whiteWhiteley1987`. The pin-a-body motion-space fact behind Lemma 5.1.
- **[15] Jackson, B., Jordán, T.**, *The generic rank of
  body–bar-and-hinge frameworks*, European J. Combin. **31** (2009),
  no. 2, 574–588 (DOI 10.1016/j.ejc.2009.03.030). Added as
  `jacksonJordan2009`. Proposition 2.3 (the def = corank = generic-rank
  bridge) reused in the Prop 1.1 reconciliation.

## Blockers / open questions

- **Lemma 5.2 perturbation vs genericity** (risk register item 3) —
  decide when `lem:rank-rotation-semicont` lands. Leaning genericity.
- **External-fact boundary** (risk register item 4) — per-node decision
  whether to prove or hypothesize the [29] pin-a-body fact (Lemma 5.1)
  and the [15] (i)⇔(ii) half of Prop 2.3. The conjecture needs only the
  upper bound, which Phase 16 may already supply.
- **Carrier compatibility** — Phase 4's `Framework V d` uses
  `EuclideanSpace ℝ (Fin d)`; Phase 17's extensors use `Fin (d+1) → ℝ`.
  Confirm the screw-space identification `⋀^(d−1) ℝ^(d+1) ≅ ℝ^D` is
  frictionless before the `def:rigidity-matrix` node.

## Hand-off / next phase

`def:hinge-constraint` has landed (`Molecular/RigidityMatrix.lean`:
`BodyHingeFramework` / `supportExtensor` / `hingeConstraint`). The next
concrete commit is the next red node `def:hinge-row-block`: in the same
file, define `r(p(e))` — a basis of the orthogonal complement
`(span C(p(e)))^⊥ ⊆ ℝ^D` — and restate the hinge constraint as the `D−1`
linear equations `(S u − S v) · r_i(p(e)) = 0`. This node forces the
concrete `⋀^k ℝ^(k+2) ≅ ℝ^D` coordinate identification (carrier
compatibility, open question above) — decide the explicit basis /
inner-product structure on the screw space when it lands; the natural
choice is the `pluckerVector` coordinatization (Phase 17) giving the `ℝ^D`
isomorphism. Then `def:rigidity-matrix` assembles the `(D−1)|E| × D|V|`
block matrix and `Z(G,p) = ker R`. The three rank lemmas (5.1/5.3/5.2)
and the Prop 1.1 reconciliation are the load-bearing targets. See
`notes/MolecularConjecture.md` *Phase 18* for the per-lemma detail and
the reuse map.
