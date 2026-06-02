# Phase 18 — Panel-hinge rigidity matrix `R(G,p)` (work log)

**Status:** in progress (just opened).

This is the **second phase of the molecular-conjecture program**
(Phases 17–26). The program-level plan — target, five-strata
architecture, phase breakdown, reuse map, risk register — lives in
`notes/MolecularConjecture.md`; read that first (especially the
*Phase 18* per-phase detail and risk-register items 3 and 4). This file
is the Phase-18 work log only.

## Current state

Phase 18 is **in progress**. Four nodes (`def:hinge-constraint`,
`def:hinge-row-block`, `def:rigidity-matrix`,
`lem:trivial-motions-rank-bound`) have **landed**
(`Molecular/RigidityMatrix.lean`), plus the rigidity-predicate half of
`def:dof-generic`; the remaining `sec:molecular-rigidity-matrix` nodes
(the numeric dof / generic, the three rank lemmas 5.1/5.3/5.2, and the
Prop 1.1 reconciliation) are still red. The numeric `rank R ≤ D(|V|−1)`
is the first genuinely-blocked piece — it IS the deferred
`⋀^k ℝ^(k+2) ≅ ℝ^D` coordinatization (see *Hand-off*).

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
- `def:hinge-row-block` — same file: `hingeRowBlock F e` =
  `(span C(p(e))).dualAnnihilator ⊆ Module.Dual ℝ (ScrewSpace k)`, the
  **basis-free** orthogonal complement (rows `r_i = functionals`), plus
  the restatement `hingeConstraint_iff_hingeRowBlock`:
  `hingeConstraint S e u v ↔ ∀ r ∈ hingeRowBlock e, r (S u − S v) = 0`.
  Proof is `Subspace.dualAnnihilator_dualCoannihilator_eq` (field-level
  `(span C)^⊥⊥ = span C`) + `Submodule.mem_dualCoannihilator`; added
  `import Mathlib.LinearAlgebra.Dual.Lemmas`. The `⋀^k ℝ^(k+2) ≅ ℝ^D`
  coordinatization stays deferred (see *Decisions* / open questions).
- `def:rigidity-matrix` — same file: `IsInfinitesimalMotion F S`
  (`S : α → ScrewSpace k` meets `hingeConstraint` at every edge, i.e.
  `∀ e u v, G.IsLink e u v → S u − S v ∈ span C(p(e))`) and the
  submodule `infinitesimalMotions F = Z(G,p) = ker R(G,p)` of all
  motions. Carried **basis-free** — `R(G,p)` is the per-edge constraint
  *family*, not an explicit `(D−1)|E| × D|V|` real coordinate matrix
  (the matrix-vector-product vanishing is exactly the per-edge
  constraint), so the `⋀^k ℝ^(k+2) ≅ ℝ^D` coordinatization stays
  deferred. Orientation-independence via `hingeConstraint_comm` (span
  closed under negation) makes the predicate well-defined on the
  undirected multigraph; `Submodule` via fixed-subspace-membership
  closure. Adds `mem_infinitesimalMotions` + `isInfinitesimalMotion_iff`.

The opening commit created this work log, opened the
`sec:molecular-rigidity-matrix` dep-graph (all red), added the two bib
entries (`whiteWhiteley1987` [29], `jacksonJordan2009` [15]), and ran the
phase-open status-surface sync.

Landed `lem:trivial-motions-rank-bound` (same file) basis-free:
`IsTrivialMotion S` (`∀ u v, S u = S v`),
`isInfinitesimalMotion_of_isTrivialMotion` (trivial ⇒ in `Z(G,p)`), the
`trivialMotions` submodule + `trivialMotions_le_infinitesimalMotions`
(the always-true `{trivial} ⊆ Z(G,p)`), `trivialMotions_eq_range_const`
(trivial motions = the diagonal `range (s ↦ (_ ↦ s))`, the basis-free
stand-in for "determined by one common value"), and
`IsInfinitesimallyRigid` (`Z(G,p) ⊆ trivialMotions`, the reverse
inclusion) with `infinitesimalMotions_eq_trivialMotions_iff` (rigidity ↔
`Z(G,p) = trivialMotions`). The numeric `rank R ≤ D(|V|−1)` (and `D =
(k+2 choose 2)` itself) is the **one** piece that stays deferred — it is
exactly the `⋀^k ℝ^(k+2) ≅ ℝ^D` coordinatization, since
`ScrewSpace k = ExteriorAlgebra ℝ (Fin (k+2) → ℝ)` has `finrank 2^(k+2)`,
not `D`, so a `finrank` count on the full algebra over-counts. The
basis-free skeleton (containments + the diagonal iso + equality-iff-rigid)
carries everything that does not need the numeral.

The next concrete commit is `def:dof-generic`'s numeric half (degree of
freedom `D(|V|−1) − rank R`, generic realization), or — equivalently — the
deferred coordinatization itself: pick the `⋀^k ℝ^(k+2) ≅ ℝ^D`
identification (the `pluckerVector` route of Phase 17) **or** prove
`finrank (trivialMotions) = D` / `finrank (α → ScrewSpace) = D·|V|`
directly. Once that lands, the numeric `rank R ≤ D(|V|−1)` and the dof/
generic numerics follow from the basis-free skeleton already in place.

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
- [x] `def:hinge-row-block` — `r(p(e))`, a basis of
      `(span C(p(e)))^⊥`; constraint as `(D−1)` linear equations.
      **Landed** (`hingeRowBlock` + `hingeConstraint_iff_hingeRowBlock`,
      basis-free as the dual annihilator).
- [x] `def:rigidity-matrix` — `R(G,p)`, the `(D−1)|E| × D|V|` block
      matrix; `Z(G,p) = ker R`. **Landed** (`IsInfinitesimalMotion` +
      `infinitesimalMotions`, basis-free as the per-edge constraint
      family; `R(G,p)` not built as an explicit real coordinate matrix).
- [x] `lem:trivial-motions-rank-bound` — the `D` trivial motions
      `S*_i`; `rank R ≤ D(|V|−1)`, equality iff infinitesimally rigid.
      **Landed** basis-free (`IsTrivialMotion` / `trivialMotions` /
      `trivialMotions_le_infinitesimalMotions` /
      `trivialMotions_eq_range_const` / `IsInfinitesimallyRigid` /
      `infinitesimalMotions_eq_trivialMotions_iff`); the numeric
      `rank R ≤ D(|V|−1)` deferred to the coordinatization.
- [ ] `def:dof-generic` — degree of freedom `D(|V|−1) − rank R`;
      generic realization. `IsInfinitesimallyRigid` half **landed**;
      numeric dof / generic still red (needs coordinatization).
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
- **Hinge-row block as the dual annihilator, not an explicit basis.**
  `def:hinge-row-block` defines `r(p(e))` as `(span C(p(e))).dualAnnihilator`
  in `Module.Dual ℝ (ScrewSpace k)` — the orthogonal complement taken
  basis-free. This keeps the screw space the full `ExteriorAlgebra` element
  (no `⋀^k ℝ^(k+2) ≅ ℝ^D` coordinatization, no inner product) at this node;
  the blueprint's `(S u − S v) · r_i = 0` becomes `r (S u − S v) = 0` for
  `r` ranging over the annihilator, and the iff is the field-level
  double-annihilator identity `Subspace.dualAnnihilator_dualCoannihilator_eq`.
  The explicit `(D−1)×D` matrix / coordinatization was *expected* to be
  forced at `def:rigidity-matrix` — but it was not (see next entry); the
  basis-free thread runs further than anticipated.
- **`R(G,p)` carried basis-free as the per-edge constraint family, not
  an explicit coordinate matrix** (`def:rigidity-matrix`). The null space
  `Z(G,p) = ker R(G,p)` is realized as the submodule `infinitesimalMotions`
  of `S : α → ScrewSpace k` cut out by `IsInfinitesimalMotion` (the
  per-edge `hingeConstraint` over `G.IsLink`). Since the vanishing of
  `R(G,p)`'s matrix-vector product *is* the per-edge constraint, no
  honest `(D−1)|E| × D|V|` real matrix — hence no `⋀^k ℝ^(k+2) ≅ ℝ^D`
  coordinatization — is needed for the kernel itself. The coordinatization
  is now expected to land only at `lem:trivial-motions-rank-bound` /
  `def:dof-generic`, where a `rank` / `finrank` count first appears.
  Orientation-independence (`hingeConstraint_comm`, span closed under
  negation) makes the predicate well-defined on the undirected
  multigraph.
- **Trivial motions carried basis-free; `IsInfinitesimallyRigid` as a
  submodule inclusion** (`lem:trivial-motions-rank-bound`). A trivial
  motion is a constant assignment (`IsTrivialMotion S := ∀ u v, S u = S v`);
  `trivialMotions` is their submodule, always `≤ infinitesimalMotions`.
  Infinitesimal rigidity is the *reverse* inclusion `Z(G,p) ⊆ trivialMotions`,
  upgrading to the equality `Z(G,p) = trivialMotions`
  (`infinitesimalMotions_eq_trivialMotions_iff`) — the basis-free form of
  `rank R = D(|V|−1)`. `trivialMotions_eq_range_const` identifies the space
  with the diagonal `range (s ↦ (_ ↦ s))` (the "one common value"
  determination). `trivialMotions` carries the framework `F` only for
  `F.trivialMotions` dot-notation parity (it depends only on `α, k`), hence
  `@[nolint unusedArguments]` (the `IsInfinitesimallyRigid`/`Framework.lean`
  precedent for an API-shape arg the linter can't see the need for).
- **The numeric `rank R ≤ D(|V|−1)` IS the deferred coordinatization, not a
  separate step.** `ScrewSpace k = ExteriorAlgebra ℝ (Fin (k+2) → ℝ)` has
  `finrank 2^(k+2)`, not `D = (k+2 choose 2)` — a `finrank` count on the
  full algebra over-counts. So the screw genuinely lives in the degree-`k`
  graded piece `⋀^k ℝ^(k+2)` (dim `D`), and the numeric bound needs the
  `⋀^k ℝ^(k+2) ≅ ℝ^D` identification. The basis-free skeleton (containments,
  diagonal iso, equality-iff-rigid) carries the full *structural* content of
  KT's lemma without the numeral; the numeral waits on the coordinatization
  (the first genuinely-blocked node, as the hand-off anticipated).
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
  frictionless — now deferred to `lem:trivial-motions-rank-bound` /
  `def:dof-generic` (the first `rank` / `finrank` node), since
  `def:rigidity-matrix` landed basis-free without it.

## Hand-off / next phase

`def:hinge-constraint`, `def:hinge-row-block`, `def:rigidity-matrix`, and
the structural half of `lem:trivial-motions-rank-bound` /
`def:dof-generic` have landed (`Molecular/RigidityMatrix.lean`). The
trivial-motion layer is basis-free: `IsTrivialMotion`, `trivialMotions`
(≤ `infinitesimalMotions`), `trivialMotions_eq_range_const` (the diagonal
iso), `IsInfinitesimallyRigid` (`Z(G,p) ⊆ trivialMotions`), and
`infinitesimalMotions_eq_trivialMotions_iff` (rigidity ↔ `Z = trivial`).

The next concrete commit is **the deferred coordinatization** — now the
first genuinely-blocked node and the gate for every remaining numeric: pick
the `⋀^k ℝ^(k+2) ≅ ℝ^D` identification (natural choice: the `pluckerVector`
coordinatization of Phase 17) **or** prove `finrank (trivialMotions) = D`
and `finrank (α → ScrewSpace) = D·|V|` directly on the screw-assignment
space (note `ScrewSpace k` is the *full* exterior algebra, `finrank
2^(k+2)`, so the screw must be cut down to the degree-`k` graded piece
`⋀^k ℝ^(k+2)` of dim `D = (k+2 choose 2)` first). Once the `D`-count lands,
the numeric `rank R ≤ D(|V|−1)` and the dof / generic numerics of
`def:dof-generic` follow from the basis-free skeleton already in place.
After that: the three rank lemmas (5.1/5.3/5.2) and the Prop 1.1
reconciliation (the load-bearing targets). See `notes/MolecularConjecture.md`
*Phase 18* for the per-lemma detail and the reuse map.
