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
`def:dof-generic`. The **deferred `⋀^k ℝ^(k+2) ≅ ℝ^D` coordinatization
has now landed**: `ScrewSpace k` was refactored from the full exterior
algebra to the degree-`k` graded piece `↥(⋀[ℝ]^k (Fin (k+2) → ℝ))` (where
the supporting extensors actually live), and `screwSpace_finrank :
finrank ℝ (ScrewSpace k) = screwDim k = (k+2).choose 2` realizes the
identification as a `finrank` equality (not an explicit basis). This is
the numeric gate for the remaining red nodes (the three rank lemmas
5.1/5.3/5.2 and the Prop 1.1 reconciliation), all still red. The numeric
finrank counts have now **landed**: `finrank_trivialMotions`
(`finrank (trivialMotions) = D`, via the diagonal iso
`trivialMotions_eq_range_const` + injectivity `injective_const_pi` +
`screwSpace_finrank`) and `finrank_screwAssignment`
(`finrank (α → ScrewSpace) = D·|V|`, via the mirrored
`Module.finrank_pi_const` + `screwSpace_finrank`). Together they give the
`D`-dimensional trivial kernel inside the `D·|V|`-dimensional
screw-assignment space — the codimension form of `rank R ≤ D(|V|−1)`.
**Lemma 5.3 (`lem:rank-parallel-full`) has now landed**: two parallel
hinges in general position (linearly-independent supporting extensors)
have constraint spans meeting only at `0`
(`span_inf_span_eq_bot_of_linearIndependent`, via `disjoint_span_singleton'`
+ `pair_iff'`), so a screw meeting both forces `S u = S v`
(`eq_of_hingeConstraint_two_parallel`) — the `|V|=2` base case.
**Lemma 5.1 (`lem:rank-delete-vertex`, pin-a-body) has now landed**: the
null space `Z(G,p)` decomposes as the internal direct sum of the `D`
trivial motions and the body-`v`-pinned motions (`pinnedMotions v`,
those vanishing on `v`), giving `finrank (pinnedMotions v) + D =
finrank Z(G,p)` (`finrank_pinnedMotions_add_screwDim`) — the codimension
form of "deleting body `v`'s `D` columns preserves rank". The [29]
pin-a-body fact is *proved* via the normalization `S u ↦ S u - S v`
staying a motion (`isInfinitesimalMotion_sub_const`).
**Lemma 5.2 (`lem:rank-rotation-semicont`) has now landed**, basis-free
as span-refinement monotonicity: if two frameworks share a graph and
`F`'s hinge spans are contained in `F'`'s at every edge (`F'` the more
general/generic realization), then `F'.infinitesimalMotions ≤
F.infinitesimalMotions` (`infinitesimalMotions_mono_of_span_le`), hence
`finrank Z(G,p') ≤ finrank Z(G,p)` (`finrank_infinitesimalMotions_le_of_span_le`,
via `Submodule.finrank_mono`) — i.e. `rank R(G,p) ≤ rank R(G,p')`: the
generic member of a rotation family has the largest supporting spans and
the maximal rank. Carried as the monotonicity core (matching the 5.1/5.3
basis-free treatment), not the literal analytic one-parameter
semicontinuity — the genericity-over-perturbation choice avoids the
parametrized polynomial-entry coordinate matrix the design defers. Only
`prop:rigidity-matrix-prop11` (the Prop 1.1 reconciliation) remains red;
see *Hand-off*.

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
      The `⋀^k ℝ^(k+2) ≅ ℝ^D` coordinatization now also landed here:
      `ScrewSpace` refactored to the degree-`k` graded piece +
      `screwSpace_finrank : finrank ℝ (ScrewSpace k) = screwDim k`.
- [x] `lem:trivial-motions-rank-bound` — the `D` trivial motions
      `S*_i`; `rank R ≤ D(|V|−1)`, equality iff infinitesimally rigid.
      **Landed** basis-free (`IsTrivialMotion` / `trivialMotions` /
      `trivialMotions_le_infinitesimalMotions` /
      `trivialMotions_eq_range_const` / `IsInfinitesimallyRigid` /
      `infinitesimalMotions_eq_trivialMotions_iff`); the numeric counts
      `finrank_trivialMotions` (`= D`) + `finrank_screwAssignment`
      (`= D·|V|`) now **landed** (the codimension form of
      `rank R ≤ D(|V|−1)`).
- [~] `def:dof-generic` — degree of freedom `D(|V|−1) − rank R`;
      generic realization. `IsInfinitesimallyRigid` half **landed**; the
      numeric dimension counts `finrank_trivialMotions` (`= D`) and
      `finrank_screwAssignment` (`= D·|V|`) now **landed** too (the
      codimension form of `rank R ≤ D(|V|−1)`). The maximum-rank *generic*
      realization condition is the only remaining red part.
- [x] `lem:rank-delete-vertex` — **Lemma 5.1** (pin a body, delete `D`
      columns, rank unchanged); [29] White–Whiteley. **Landed**
      (`pinnedMotions` + `trivialMotions_inf_pinnedMotions_eq_bot` +
      `trivialMotions_sup_pinnedMotions` + `finrank_pinnedMotions_add_screwDim`):
      the null space `Z(G,p)` is the internal direct sum of the `D`
      trivial motions and the body-`v`-pinned motions, so
      `finrank (pinnedMotions v) + D = finrank Z(G,p)` — the codimension
      form of rank-preservation. The [29] pin-a-body fact is *proved*,
      not hypothesized: the normalization `S u ↦ S u - S v` stays a
      motion (`isInfinitesimalMotion_sub_const`) since the hinge
      constraint only sees relative screws.
- [x] `lem:rank-parallel-full` — **Lemma 5.3** (two general-position
      parallel hinges → full block `D`); via `lem:extensor-independence`.
      **Landed** (`span_inf_span_eq_bot_of_linearIndependent` + framework
      corollary `eq_of_hingeConstraint_two_parallel`): the two constraint
      spans of linearly-independent supporting extensors meet only at `0`
      (`disjoint_span_singleton'` + `pair_iff'`), so a screw meeting both
      hinge constraints has `S u = S v`.
- [x] `lem:rank-rotation-semicont` — **Lemma 5.2** (rank
      lower-semicontinuity under a panel rotation). **Landed** basis-free
      as span-refinement monotonicity (`infinitesimalMotions_mono_of_span_le`
      + `finrank_infinitesimalMotions_le_of_span_le`): refining the hinge
      spans (toward general position) shrinks the motion space, so
      `rank R(G,p) ≤ rank R(G,p')` with `p'` the generic realization. Via
      `Submodule.finrank_mono`; the genericity-over-perturbation choice
      (risk register item 3) resolved in the monotonicity direction.
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
- **Coordinatization landed: `ScrewSpace` is the graded piece, `D` via
  `exteriorPower.finrank_eq`.** Refactored `ScrewSpace k` from
  `ExteriorAlgebra ℝ (Fin (k+2) → ℝ)` to the degree-`k` graded piece
  `↥(⋀[ℝ]^k (Fin (k+2) → ℝ))` — the subspace where the supporting extensors
  already live (`affineSubspaceExtensor_mem_exteriorPower`, added to
  `Extensor.lean`). `supportExtensor` now returns the subtype element
  `⟨affineSubspaceExtensor _, _⟩`. The `⋀^k ℝ^(k+2) ≅ ℝ^D` identification is the
  `finrank` equality `screwSpace_finrank : finrank ℝ (ScrewSpace k) = screwDim k
  = (k+2).choose 2`, proved by `exteriorPower.finrank_eq` (`(k+2).choose k`) +
  `Nat.choose_symm` (`= (k+2).choose 2`). No explicit basis. Refactor friction:
  `simp [← smul_sub]` stalled on the subtype's `RingQuot`-built ops (not
  exposed) → FRICTION *`simp [← smul_sub]` … graded-piece screw subtype*.
- **Numeric trivial-kernel / column counts via the diagonal iso, not a
  basis.** `finrank_trivialMotions = D` is `LinearMap.finrank_range_of_inj`
  applied to the constant-assignment map `s ↦ (fun _ => s)`
  (`trivialMotions_eq_range_const` + injectivity `injective_const_pi`,
  needing `Nonempty α`) composed with `screwSpace_finrank`;
  `finrank_screwAssignment = D·|V|` is `Module.finrank_pi_const` (mirrored
  — mathlib has only the dependent-`∑` `finrank_pi_fintype` and the scalar
  `ι → R` case) + `screwSpace_finrank`. The codimension of the
  `D`-dimensional trivial kernel is the basis-free `rank R ≤ D(|V|−1)`. See
  FRICTION *`Module.finrank_pi_const`*.
- **Body-hinge framework as a `Graph`-native `structure`** (graph +
  `hinge` field), mirroring Phase 16's `Graph.BodyHingeFramework` shape
  but in the `Molecular` namespace and carrying honest hinge *geometry*
  (the point family) rather than the reduction-only standard-basis
  witness. The two coexist (Phase 16 = existence form, Phase 18 = rank
  form); the reconciliation `prop:rigidity-matrix-prop11` is the real
  bridge, not a rename.

- **Lemma 5.1 (pin-a-body) carried basis-free as an internal direct-sum
  decomposition of `Z(G,p)`** (`lem:rank-delete-vertex`). Rather than an
  explicit column-deletion on a coordinate matrix, "pinning body `v`" is
  the submodule `pinnedMotions v` of motions vanishing at `v`. The
  [29] White–Whiteley normalization is `isInfinitesimalMotion_sub_const`:
  subtracting the constant `S v` keeps a motion (the hinge constraint only
  sees relative screws `S u − S w`). This gives
  `trivialMotions ⊔ pinnedMotions v = infinitesimalMotions` and
  `trivialMotions ⊓ pinnedMotions v = ⊥`, hence (via
  `Submodule.finrank_sup_add_finrank_inf_eq` + `finrank_trivialMotions`)
  `finrank (pinnedMotions v) + D = finrank Z(G,p)` — rank-preservation in
  codimension form, with the `D` pinned columns the dropped trivial-motion
  dimensions. The [29] fact is *proved*, resolving the prove-vs-hypothesize
  question (risk register item 4) for Lemma 5.1 in the prove direction.

- **Lemma 5.2 (rotation semicontinuity) carried basis-free as
  span-refinement monotonicity** (`lem:rank-rotation-semicont`). Rather
  than a parametrized one-parameter rotation family with the rigidity
  matrix as a polynomial-entry coordinate matrix (the analytic /
  literal-minor form), the lemma is `infinitesimalMotions_mono_of_span_le`:
  two frameworks `F, F'` on the same graph with `span C(p(e)) ≤ span C(p'(e))`
  at every edge (so `F'` is the *more general* realization) have
  `F'.infinitesimalMotions ≤ F.infinitesimalMotions` — refining the spans
  toward general position only shrinks the motion space. The rank form
  `finrank Z(G,p') ≤ finrank Z(G,p)` is then `Submodule.finrank_mono`
  (`finrank_infinitesimalMotions_le_of_span_le`). This resolves risk
  register item 3 in the genericity direction (the monotonicity core),
  matching the basis-free treatment of 5.1/5.3 and avoiding the
  parametrized polynomial coordinate matrix the design defers. No
  friction (two one-liners reusing the existing motion-space API).

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
  **resolved** in the monotonicity direction: `lem:rank-rotation-semicont`
  landed basis-free as span-refinement monotonicity
  (`infinitesimalMotions_mono_of_span_le` + the `Submodule.finrank_mono`
  rank corollary), not an analytic perturbation. See *Decisions*.
- **External-fact boundary** (risk register item 4) — the [29]
  pin-a-body fact (Lemma 5.1) was **proved**, not hypothesized
  (`isInfinitesimalMotion_sub_const`, the relative-screw normalization).
  Remaining open: the [15] (i)⇔(ii) half of Prop 2.3 (Prop 1.1
  reconciliation). The conjecture needs only the upper bound, which
  Phase 16 may already supply.
- **Carrier compatibility** — Phase 4's `Framework V d` uses
  `EuclideanSpace ℝ (Fin d)`; Phase 17's extensors use `Fin (d+1) → ℝ`.
  The screw-space identification `⋀^(d−1) ℝ^(d+1) ≅ ℝ^D` is now landed
  (`screwSpace_finrank`): `ScrewSpace k = ↥(⋀[ℝ]^k (Fin (k+2) → ℝ))`, the
  graded-piece subtype, with `finrank = (k+2).choose 2`. Frictionless apart
  from the subtype-op `simp` interaction logged in FRICTION.

## Hand-off / next phase

`def:hinge-constraint`, `def:hinge-row-block`, `def:rigidity-matrix` (now
**including** the `⋀^k ℝ^(k+2) ≅ ℝ^D` coordinatization), the full
`lem:trivial-motions-rank-bound` (structural skeleton + numeric finrank
counts), and the rigidity-predicate + numeric-dimension parts of
`def:dof-generic` have landed (`Molecular/RigidityMatrix.lean`). The screw space is the degree-`k` graded
piece `↥(⋀[ℝ]^k (Fin (k+2) → ℝ))`; `screwSpace_finrank : finrank ℝ
(ScrewSpace k) = screwDim k = (k+2).choose 2` is the numeric gate. The
trivial-motion layer is basis-free: `trivialMotions` (≤ `infinitesimalMotions`),
`trivialMotions_eq_range_const` (the diagonal iso `ScrewSpace ≃ trivialMotions`
for `Nonempty α`), `IsInfinitesimallyRigid`, `infinitesimalMotions_eq_trivialMotions_iff`.

The numeric finrank counts have now **landed**: `finrank_trivialMotions`
(`finrank (F.trivialMotions) = screwDim k = D`, via the diagonal iso
`trivialMotions_eq_range_const` + injectivity `injective_const_pi` +
`screwSpace_finrank`, for `Nonempty α`) and `finrank_screwAssignment`
(`finrank (α → ScrewSpace) = D·|V|`, via the mirrored
`Module.finrank_pi_const` + `screwSpace_finrank`, for `Fintype α`).
Together they are the codimension form of `rank R ≤ D(|V|−1)` — the
basis-free skeleton plus the two numerals. `lem:trivial-motions-rank-bound`
is fully green; the numeric-dimension part of `def:dof-generic` is landed
(only its maximum-rank *generic* realization condition remains red).

`lem:rank-parallel-full` (KT Lemma 5.3) has now **landed**
(`span_inf_span_eq_bot_of_linearIndependent` + `eq_of_hingeConstraint_two_parallel`,
basis-free): the constraint spans of two linearly-independent supporting
extensors meet only at `0`, so a screw meeting both hinge constraints has
`S u = S v` — the `|V|=2` base case. The hypothesis is taken directly as
`LinearIndependent ℝ ![C(e₁), C(e₂)]`; specializing Phase 17's
`omitTwoExtensor_linearIndependent` to two hinges to *derive* that
independence from affine-general-position of the hinge points is a small
follow-on, deferred to where Case II/III consume it.

`lem:rank-delete-vertex` (KT Lemma 5.1, pin-a-body) has now **landed**
(`pinnedMotions` + `trivialMotions_inf_pinnedMotions_eq_bot` +
`trivialMotions_sup_pinnedMotions` + `finrank_pinnedMotions_add_screwDim`,
basis-free): `Z(G,p)` is the internal direct sum of the `D` trivial
motions and the body-`v`-pinned motions, so
`finrank (pinnedMotions v) + D = finrank Z(G,p)` — the codimension form
of "deleting body `v`'s `D` columns preserves rank". The [29]
White–Whiteley pin-a-body fact is *proved*, via the relative-screw
normalization `isInfinitesimalMotion_sub_const`.

`lem:rank-rotation-semicont` (KT Lemma 5.2) has now **landed**
basis-free as span-refinement monotonicity
(`infinitesimalMotions_mono_of_span_le` +
`finrank_infinitesimalMotions_le_of_span_le`): on a shared graph,
refining the hinge spans toward general position (the generic realization
`p'` with the larger supporting spans) shrinks the motion space, so
`rank R(G,p) ≤ rank R(G,p')` — the rank can only rise toward the generic
member of a rotation family. Via `Submodule.finrank_mono`; resolves risk
register item 3 in the monotonicity (genericity) direction.

**One node remains red: `prop:rigidity-matrix-prop11`** (KT Prop 1.1),
the reconciliation of the honest rank form (`rank R(G,p) = D(|V|−1)`,
`def:dof-generic` / `infinitesimalMotions_eq_trivialMotions_iff`) with
Phase 16's reduction-form existence statement `thm:body-hinge-tay`
(`(δ−1)·G` is `(δ,δ)`-tight), `δ = D = screwDim k`. This is the next and
final Phase-18 concrete commit. It is the heavier integration: the bridge
is Prop 2.3 of Jackson–Jordán [15] (`jacksonJordan2009`), whose deficiency
`def(G̃)` is the corank of the `D`-fold graphic-matroid union `M(G̃)` on
`(D−1)·G` — exactly the Phase 13/14 `unionPow_cycleMatroid` +
`tutte_nash_williams` machinery, with `def = 0` ⇔ `(δ,δ)`-tightness
matching `BodyBar/BodyHinge.lean`'s `edgeMultiply_isSparse_iff`. The
conjecture itself needs only the upper-bound half (which Phase 16 may
already supply); decide the prove-vs-hypothesize boundary for the [15]
(i)⇔(ii) generic-rank half when the node lands (the [29] pin-a-body half
is already *proved*, Lemma 5.1). The smallest concrete first step is to
state the reconciliation `iff` against the two existing forms and assess
whether the `M(G̃)` corank bridge needs Phase 19's `M(G̃)` machinery first
(it may — Prop 2.3's deficiency is a Phase-19 object); if so, this node
defers to Phase 19 and **Phase 18 closes here** with the rank-matrix
skeleton, the trivial-motion / numeric layer, and the three rank lemmas
5.1/5.2/5.3 all green. See `notes/MolecularConjecture.md` *Phase 18* /
*Phase 19* for the per-lemma detail and reuse map.
