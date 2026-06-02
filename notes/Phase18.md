# Phase 18 — Panel-hinge rigidity matrix `R(G,p)` (work log)

**Status:** ✓ Complete. The rank-matrix skeleton, the trivial-motion /
numeric-dimension layer, and the three rank lemmas (KT 5.1/5.2/5.3) are
all green in `Molecular/RigidityMatrix.lean`. The single remaining node
`prop:rigidity-matrix-prop11` (KT Prop 1.1 reconciliation) is **deferred
to Phase 19** — its bridge is JJ [15] Thm 6.1 / Cor 6.2's
`def(G̃) = corank M(G̃)`, a Phase-19 object — recorded as a Phase-19
deliverable in `notes/MolecularConjecture.md` *Phase 19*. See *Hand-off*.

This is the **second phase of the molecular-conjecture program**
(Phases 17–26). The program-level plan — target, five-strata
architecture, phase breakdown, reuse map, risk register — lives in
`notes/MolecularConjecture.md`; read that first (the *Phase 18* per-phase
detail and risk-register items 3 and 4). This file is the Phase-18 work
log only.

## Current state

Phase 18 is **complete**, closed by deferring the last node to Phase 19.
Eight of nine `sec:molecular-rigidity-matrix` nodes are green in
`Molecular/RigidityMatrix.lean` (the file is wired into
`CombinatorialRigidity.lean`); `prop:rigidity-matrix-prop11` is red and
marked deferred. The decisive architectural fact of the phase is that the
whole rigidity matrix **stays basis-free**: `R(G,p)` is never built as an
explicit `(D−1)|E| × D|V|` real coordinate matrix — it is the per-edge
constraint family, and `Z(G,p) = ker R(G,p)` is the submodule cut out by
it. The `⋀^k ℝ^(k+2) ≅ ℝ^D` coordinatization was deferred node-by-node
until it was finally forced by the first `finrank` count, where it landed
as the single `finrank` equality `screwSpace_finrank` (no explicit basis).
See *Lemma checklist* for the per-node landed state and *Hand-off* for the
deferral rationale.

## Scope (Phase 18 only)

Katoh–Tanigawa 2011 §2.2–2.4 plus the §5 rank lemmas the algebraic
induction reuses: the **genuine** panel-hinge / body-hinge rigidity matrix
`R(G,p)` (Stratum 2 of the program's five). Concretely the hinge
constraint via the supporting `(d−1)`-extensor `C(p(e))` (Phase 17), the
orthogonal-complement block `r(p(e))`, the matrix `R(G,p)` and its null
space `Z(G,p)`, the `D` trivial motions, the `rank R ≤ D(|V|−1)` bound,
degree of freedom / infinitesimal rigidity / generic realizations, the
three rank lemmas **5.1** (pin-a-body, most-reused), **5.3** (two
general-position parallel hinges → full block, base case), **5.2** (rank
lower-semicontinuity), and the **reconciliation with Phase 16's
reduction-form Prop 1.1** (deferred — see *Hand-off*).

`R(G,p)` **supersedes** Phase 16's reduction-only `BodyHingeFramework`
(standard-basis witness, no geometry): keep the Phase-16 def as the
existence form, the new one is the rank form, and the reconciliation is
real work, not a rename. Reuse: Phase 4 `Framework.lean`; Phase 6–8
rank/genericity; Phase 17 `extensor` / `affineSubspaceExtensor`; Phase
13/14 union + Tutte–Nash-Williams and Phase 16 `edgeMultiply` for the
deferred Prop 1.1 reconciliation. Carrier: mathlib core `Graph α β`.

## Architectural choices made up front

- **Extend the molecular chapter, don't open a new one.** Phase 18's nodes
  go in a new `\section{}` (`sec:molecular-rigidity-matrix`) of
  `molecular.tex` after the Phase-17 §2.1 sections, forward-mode.
- **Reparametrize dimension `d = k+1`** (à la Phase 17's `omitTwoExtensor`).
  A hinge is `k = d−1` points in `ℝ^(k+1)`; the supporting extensor is a
  `k`-extensor in `⋀^k ℝ^(k+2)`. Clears the `d−1`/`d−2` `ℕ`-subtractions.
- **Screw carrier `ℝ^D`, `D = (k+2 choose 2)`.** Infinitesimal motions are
  `D`-dimensional screw centers matching Phase 17's extensor space; the
  concrete identification was deferred to the first rank-bearing node
  (landed as `screwSpace_finrank`, *Decisions*).
- **Lemma 5.2 (risk item 3): prefer genericity over analytic perturbation.**
  Resolved in the monotonicity direction (*Decisions*).
- **Externals (risk item 4): formalize the Prop 1.1 reconciliation via the
  project's own union machinery, not by axiomatizing JJ [15].** Decide
  per-node whether [29]'s pin-a-body fact is proved or hypothesized
  (it was *proved* for Lemma 5.1).

## Lemma checklist

Forward-mode: the authoritative dep-graph is the
`sec:molecular-rigidity-matrix` section of
`blueprint/src/chapter/molecular.tex`. Names below are the landed Lean
decls in `Molecular/RigidityMatrix.lean`.

- [x] `def:hinge-constraint` — `BodyHingeFramework k α β` (multigraph +
      per-edge hinge), `supportExtensor` (= Phase 17's
      `affineSubspaceExtensor`), `hingeConstraint`
      (`S u − S v ∈ span C(p(e))`).
- [x] `def:hinge-row-block` — `hingeRowBlock F e =
      (span C(p(e))).dualAnnihilator`, the **basis-free** orthogonal
      complement, with `hingeConstraint_iff_hingeRowBlock` (via the
      field-level double-annihilator identity
      `Subspace.dualAnnihilator_dualCoannihilator_eq`).
- [x] `def:rigidity-matrix` — `IsInfinitesimalMotion F S` + the submodule
      `infinitesimalMotions F = Z(G,p) = ker R(G,p)`, basis-free as the
      per-edge constraint family. The `⋀^k ℝ^(k+2) ≅ ℝ^D` coordinatization
      landed here: `ScrewSpace` refactored to the degree-`k` graded piece
      `↥(⋀[ℝ]^k (Fin (k+2) → ℝ))` + `screwSpace_finrank :
      finrank ℝ (ScrewSpace k) = screwDim k = (k+2).choose 2`.
- [x] `lem:trivial-motions-rank-bound` — `IsTrivialMotion` /
      `trivialMotions` / `trivialMotions_le_infinitesimalMotions` /
      `trivialMotions_eq_range_const` / `IsInfinitesimallyRigid` /
      `infinitesimalMotions_eq_trivialMotions_iff`, plus the numeric counts
      `finrank_trivialMotions` (`= D`) and `finrank_screwAssignment`
      (`= D·|V|`) — the codimension form of `rank R ≤ D(|V|−1)`.
- [x] `def:dof-generic` — degree of freedom `D(|V|−1) − rank R`, generic
      realization. The `IsInfinitesimallyRigid` half and the two numeric
      dimension counts landed; the maximum-rank *generic* realization
      condition is the only part carried to a later phase.
- [x] `lem:rank-delete-vertex` — **Lemma 5.1** (pin a body, delete `D`
      columns, rank unchanged) [29]. `pinnedMotions` +
      `trivialMotions_inf/sup_pinnedMotions` +
      `finrank_pinnedMotions_add_screwDim`: `Z(G,p)` is the internal direct
      sum of the `D` trivial motions and the body-`v`-pinned motions, so
      `finrank (pinnedMotions v) + D = finrank Z(G,p)`. The [29] fact is
      *proved* via `isInfinitesimalMotion_sub_const`.
- [x] `lem:rank-parallel-full` — **Lemma 5.3** (two general-position
      parallel hinges → full block) via `lem:extensor-independence`.
      `span_inf_span_eq_bot_of_linearIndependent` +
      `eq_of_hingeConstraint_two_parallel`: the constraint spans of two
      linearly-independent supporting extensors meet only at `0`, so a
      screw meeting both forces `S u = S v` (the `|V|=2` base case).
- [x] `lem:rank-rotation-semicont` — **Lemma 5.2** basis-free as
      span-refinement monotonicity:
      `infinitesimalMotions_mono_of_span_le` +
      `finrank_infinitesimalMotions_le_of_span_le` (via
      `Submodule.finrank_mono`) — refining the spans toward general
      position shrinks the motion space, so `rank R(G,p) ≤ rank R(G,p')`.
- [→] `prop:rigidity-matrix-prop11` — reconcile rank form with Phase 16's
      existence form (`thm:body-hinge-tay`); via JJ [15] Thm 6.1 / Cor 6.2
      + Phase 13/14 union. **Deferred to Phase 19** (its bridge
      `def(G̃) = corank M(G̃)` is a Phase-19 object); blueprint node red,
      marked deferred. See *Hand-off*.

## Decisions made during this phase

### Phase-local choices and proof techniques

- **The whole rigidity matrix runs basis-free, further than anticipated.**
  Both `def:hinge-row-block` (dual annihilator, not an explicit basis) and
  `def:rigidity-matrix` (`R(G,p)` as the per-edge constraint family, with
  the vanishing of the matrix-vector product *being* the per-edge
  constraint) avoid the `⋀^k ℝ^(k+2) ≅ ℝ^D` coordinatization. The screw
  space is the full `ExteriorAlgebra` element throughout this layer, so
  `span C(p(e))` is literally a `Submodule.span`. Orientation-independence
  via `hingeConstraint_comm` (span closed under negation) makes the
  predicate well-defined on the undirected multigraph.
- **The numeric `rank R ≤ D(|V|−1)` IS the deferred coordinatization.**
  `ScrewSpace k = ExteriorAlgebra ℝ (Fin (k+2) → ℝ)` has `finrank 2^(k+2)`,
  not `D`, so a `finrank` count over-counts. The screw genuinely lives in
  the degree-`k` graded piece `⋀^k ℝ^(k+2)` (dim `D`); the basis-free
  skeleton (containments, diagonal iso, equality-iff-rigid) carries the
  full *structural* content without the numeral, and the numeral waits on
  the coordinatization.
- **Coordinatization landed: `ScrewSpace` is the graded piece, `D` via
  `exteriorPower.finrank_eq`.** Refactored `ScrewSpace k` to
  `↥(⋀[ℝ]^k (Fin (k+2) → ℝ))` (where the supporting extensors live —
  `affineSubspaceExtensor_mem_exteriorPower`, added to `Extensor.lean`);
  `supportExtensor` returns the subtype element. The identification is the
  `finrank` equality `screwSpace_finrank = (k+2).choose 2`
  (`exteriorPower.finrank_eq` + `Nat.choose_symm`), no explicit basis.
- **Trivial motions carried basis-free; `IsInfinitesimallyRigid` as a
  submodule inclusion.** A trivial motion is a constant assignment;
  `trivialMotions` is always `≤ infinitesimalMotions`, and infinitesimal
  rigidity is the *reverse* inclusion, upgrading to the equality
  `Z(G,p) = trivialMotions` — the basis-free form of `rank R = D(|V|−1)`.
  `trivialMotions_eq_range_const` identifies it with the diagonal
  `range (s ↦ (_ ↦ s))`. `trivialMotions` carries `F` only for
  dot-notation parity (depends only on `α, k`), hence
  `@[nolint unusedArguments]`.
- **Numeric trivial-kernel / column counts via the diagonal iso, not a
  basis.** `finrank_trivialMotions = D` is `LinearMap.finrank_range_of_inj`
  on the constant-assignment map (`trivialMotions_eq_range_const` +
  `injective_const_pi`, needs `Nonempty α`) ∘ `screwSpace_finrank`;
  `finrank_screwAssignment = D·|V|` is the mirrored `Module.finrank_pi_const`
  + `screwSpace_finrank`. → FRICTION [mirrored] *`Module.finrank_pi_const`*.
- **Lemma 5.1 (pin-a-body) as an internal direct-sum decomposition of
  `Z(G,p)`.** "Pinning body `v`" is the submodule `pinnedMotions v` of
  motions vanishing at `v`; the [29] normalization
  `isInfinitesimalMotion_sub_const` (subtracting the constant `S v` keeps a
  motion — the constraint sees only relative screws) gives
  `trivialMotions ⊕ pinnedMotions v = infinitesimalMotions`, hence
  `finrank (pinnedMotions v) + D = finrank Z(G,p)` (via
  `Submodule.finrank_sup_add_finrank_inf_eq`). Resolves the
  prove-vs-hypothesize question (risk item 4) for Lemma 5.1 in the prove
  direction.
- **Lemma 5.2 (rotation semicontinuity) as span-refinement monotonicity.**
  Rather than a parametrized one-parameter rotation family with a
  polynomial-entry coordinate matrix, the lemma is
  `infinitesimalMotions_mono_of_span_le`: on a shared graph with
  `span C(p(e)) ≤ span C(p'(e))` at every edge (`F'` the more general
  realization), `F'.infinitesimalMotions ≤ F.infinitesimalMotions`. The
  rank form is `Submodule.finrank_mono`. Resolves risk item 3 in the
  genericity direction; matches the 5.1/5.3 basis-free treatment.
- **Body-hinge framework as a `Graph`-native `structure`** (graph + `hinge`
  field), mirroring Phase 16's `Graph.BodyHingeFramework` shape but in the
  `Molecular` namespace and carrying honest hinge *geometry* rather than the
  reduction-only standard-basis witness. The two coexist (Phase 16 =
  existence form, Phase 18 = rank form).

### Promoted to FRICTION

- *`simp [← smul_sub]` / `simp [add_sub_add_comm]` stalls on the
  graded-piece screw subtype (RingQuot-built ops not exposed)* → FRICTION
  [resolved], the `def:rigidity-matrix` `ScrewSpace`-refactor friction.
- *`Module.finrank_pi_const` (constant non-dependent `ι → M` finrank)* →
  FRICTION [mirrored], used by `finrank_screwAssignment`.

### Citations verified this phase

- **[29] White, N., Whiteley, W.**, *The algebraic geometry of motions of
  bar-and-body frameworks*, SIAM J. Algebraic Discrete Methods **8** (1987),
  no. 1, 1–32 (DOI 10.1137/0608001). Added as `whiteWhiteley1987`. The
  pin-a-body motion-space fact behind Lemma 5.1.
- **[15] Jackson, B., Jordán, T.**, *The generic rank of
  body–bar-and-hinge frameworks*, European J. Combin. **31** (2009), no. 2,
  574–588 (DOI 10.1016/j.ejc.2009.03.030). Added as `jacksonJordan2009`.
  The rank↔deficiency bridge (Thm 6.1 `r(G,q) = D(|V|−1) − def_D(G_H)`,
  Cor 6.2 rigid iff `D` edge-disjoint spanning trees) is reused in the
  deferred Prop 1.1 reconciliation. *(The paper has no Propositions; an
  earlier "Prop 2.3" attribution was a phantom, fixed in the Phase-18
  cleanup round — see `notes/Phase18-cleanup.md` A5.)*

## Blockers / open questions

- **Lemma 5.2 perturbation vs genericity** (risk item 3) — **resolved** in
  the monotonicity direction (`lem:rank-rotation-semicont`, basis-free
  span-refinement monotonicity, not analytic perturbation).
- **External-fact boundary** (risk item 4) — the [29] pin-a-body fact
  (Lemma 5.1) was **proved**, not hypothesized. Remaining open: the [15]
  generic-rank half (Thm 6.1) for the Prop 1.1 reconciliation; the
  conjecture needs only the upper bound, which Phase 16 may already supply.
- **Carrier compatibility** — the screw-space identification
  `⋀^(d−1) ℝ^(d+1) ≅ ℝ^D` is landed (`screwSpace_finrank`); frictionless
  apart from the subtype-op `simp` interaction in FRICTION.

## Hand-off / next phase

**Phase 18 closes here.** Eight of nine `sec:molecular-rigidity-matrix`
nodes are green in `Molecular/RigidityMatrix.lean`: the hinge-constraint /
hinge-row-block / rigidity-matrix layer (including the `⋀^k ℝ^(k+2) ≅ ℝ^D`
coordinatization as `screwSpace_finrank`), `lem:trivial-motions-rank-bound`
(structural skeleton + the `D` / `D·|V|` finrank counts), the
rigidity-predicate + numeric-dimension parts of `def:dof-generic`, and the
three rank lemmas **5.1** (pin-a-body, `finrank_pinnedMotions_add_screwDim`,
[29] fact proved), **5.3** (parallel hinges,
`eq_of_hingeConstraint_two_parallel`), **5.2** (span-refinement
monotonicity, `infinitesimalMotions_mono_of_span_le`).

The one remaining node `prop:rigidity-matrix-prop11` (KT Prop 1.1) — the
reconciliation of the honest rank form (`rank R(G,p) = D(|V|−1)`) with
Phase 16's reduction-form existence statement `thm:body-hinge-tay`
(`(δ−1)·G` is `(δ,δ)`-tight, `δ = D = screwDim k`) — was assessed per the
prior hand-off's "smallest concrete first step" and **deferred to
Phase 19**. The bridge is JJ [15] (Thm 6.1 / Cor 6.2), whose deficiency
`def(G̃)` is the corank of the `D`-fold graphic-matroid union `M(G̃)` on
`(D−1)·G`. `M(G̃)`, the deficiency, and the `def = corank` bridge are all
**Phase-19 objects** (`notes/MolecularConjecture.md` *Phase 19*, KT
§2.5/§3): equating the geometric `rank R` to the combinatorial tightness
of `(δ−1)·G` *requires* the matroid-union corank identity, so there is no
Phase-18-only bridge. The node defers as an inherited Phase-19 deliverable;
the blueprint node stays red, marked deferred.

**Next concrete task (Phase 19, when opened):** build `M(G̃)` (the `(D,D)`
count matroid at the boundary `ℓ = 2k = D`, routed through the Phase 13/14
`unionPow_cycleMatroid` + `tutte_nash_williams` union — *not*
`CountMatroid.lean`, which is `ℓ<2k`) and the `def = corank` bridge, then
land `prop:rigidity-matrix-prop11` against the now-available deficiency.
The conjecture needs only the upper-bound half (which Phase 16's
`edgeMultiply_isSparse_iff` may already supply); decide the
prove-vs-hypothesize boundary for the [15] (Thm 6.1) generic-rank half
when the node lands (the [29] pin-a-body half is already *proved*, Lemma
5.1). Phase 19's `M(G̃)`/deficiency machinery should go in a **new file**
(`Molecular/Deficiency.lean`), not bloat `RigidityMatrix.lean`. See
`notes/MolecularConjecture.md` *Phase 19* for the per-lemma detail and
reuse map.
</content>
</invoke>
