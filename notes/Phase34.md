# Phase 34 — PROSPECT G3: the generic lift (work log)

**Status:** ✓ complete (opened 2026-07-17 recon-first, closed 2026-07-18).

Planning input: `notes/Prospect.md` — the Tier-2 **G3** entry (queue position
user-adjudicated 2026-07-10, re-confirmed at opening). Primary source:
Jackson–Jordán, *The generic rank of body-bar-and-hinge frameworks*, Eur. J.
Combin. **31** (2010), 574–588 (`jacksonJordan2009`).

## Current state

**The phase is closed.** All four layers of the blueprint chapter
`generic-lift.tex` (forward mode) are fully green — the project's
existence-form realization statements are upgraded to the generic
("almost all realizations") form via the JJ 2010 coordinate route,
avoiding Whiteley 1988's variety-irreducibility machinery:

- **Layer M** (molecular / bar-joint `G²`, d = 3, ℝ; four nodes):
  `Molecular/Molecule/Application.lean` + `GenericRigidityMatroid.lean`.
  Headliners `SimpleGraph.molecule_generic_rank` /
  `molecule_generic_rigid` / `molecule_generic_square_packing` (JJ 2010
  p. 586: every generic bar-joint realization of `G²` in ℝ³ is rigid
  whenever `5G` packs six edge-disjoint spanning trees).
- **Layer P** (panel-and-hinge over normals, `[Field K] [Infinite K]`;
  seven nodes): `Molecular/GenericLift/PanelGeneric.lean`. Headliners
  `finrank_span_rigidityRows_ofNormals_of_isGenericNormals` /
  `isInfinitesimallyRigidOn_ofNormals_isGenericNormals_iff` (JJ Thm 7.2
  analogue, sharpened to an iff).
- **Layer BB** (body-bar at ℝ, endpoint-parameterized; nine nodes):
  `BodyBar/GenericLift.lean` + `TayTheorem.lean` adders. Headliners
  `linearIndependent_rigidityRow_ofEndpoints_iff` /
  `isIndependent_and_isInfinitesimallyRigid_ofEndpoints_iff` (generic
  Tay: "almost all bar endpoint choices").
- **Layer BH** (geometric body-hinge over `ofHinge` hinge points,
  `[Field K] [Infinite K]`; twelve nodes + the `deficiency.tex` packing
  bridge): `Molecular/GenericLift/HingeGeneric.lean` +
  `Molecular/Extensor.lean` adders +
  `Graph.deficiency_eq_zero_iff_exists_spanningTrees` (`Deficiency.lean`).
  Capstone
  `isInfinitesimallyRigidOn_ofHinge_isGenericHingePoints_iff_spanningTrees`
  (JJ Thm 6.1 / Cor 6.3 in every-generic form: every generic hinge-point
  realization is rigid iff `(D-1)·G` packs `D` edge-disjoint spanning
  trees), closed 2026-07-18.

All headline theorems `#print axioms`-verified at close (propext /
Classical.choice / Quot.sound only). Per-slice friction is promoted
(TACTICS-QUIRKS §38-variants, §90–§97; FRICTION.md incl. the
nonzero-functional-as-coordinate recipe and the `RingHomInvPair`-diamond
workaround) — this note does not duplicate it.

## Work-item checklist

- [x] **R0 — the opening recon** (2026-07-17; verdict in *Decisions made*).
- [x] **Scope + route adjudication** (user, 2026-07-17, verbatim below).
- [x] **Chapter-open** — `generic-lift.tex`, forward mode, Layer-M grain.
- [x] **Layer M** (closed 2026-07-17, four nodes).
- [x] **Layer P** (closed 2026-07-17, seven nodes).
- [x] **Layer BB** (closed 2026-07-17, nine nodes over five slices).
- [x] **Layer BH** (closed 2026-07-18, twelve nodes + the packing bridge).

## Blockers / open questions

- None.

## Hand-off / next phase

**Phase 34 closed the PROSPECT queue** (G3 was its last grouping; G2
planar was dropped by Phase 31's sizing recon). The successor,
**Phase 35 — COPLANAR** (multigraph strength for KT Conjecture 1.2 /
Theorem 5.6 in KT's own hinge-coplanar panel model), opened 2026-07-18,
recon-first — see `notes/Phase35.md`. Still queued (ROADMAP *Queued
post-program phases*): **PIN**, **UPSTREAM**, **VERSO**.

## Decisions made during this phase

- **User adjudication (2026-07-17, verbatim; overrode any conflicting
  phase-note text):** (1) statement strength = **abundance polynomial**
  (existence + every-generic + one nonzero MvPolynomial `P` with
  `{P ≠ 0} ⊆ {generic}`; the ℝ Lebesgue-null upgrade NOT in scope);
  (2) parameter spaces **fully JJ-faithful** (BH over `ofHinge` hinge
  points AND BB over bar endpoints `T(p,p')`); (3) BB/BH-combinatorial
  stated **at ℝ**, Molecular-side layers stay `[Field K] [Infinite K]`;
  (4) all four layers, order M → P → BB → BH; (5) rigidity-vs-rank form
  decided per layer at chapter-open.
- **R0 verdict (2026-07-17): the Phase-30 product route substitutes;
  alg-indep does not return.** JJ 2010's "generic" is a max-rank
  definition at all four layers; alg-indep over ℚ appears only in
  abundance remarks. Definition shape = the Phase-24 transfer form
  (`SimpleGraph.IsGenericPlacement`); the formal "almost all" is the
  abundance polynomial via `MvPolynomial.exists_eval_ne_zero`.
- **Chapter-open grain: Layer M only; P/BB/BH as chapter-extension
  design passes** (the Phase-32 lesson: minting exact shapes at
  chapter-open would be unrecon'd transcription). Paid off twice — the
  BB pass refuted the R0-era `±T` claim, the BH pass caught a §8-vs-§6
  mis-citation, both before any Lean was built on them.
- **Per-layer strength calls:** M both forms + the p. 586 packing
  corollary; P both forms; BB per-subset independence iff + the Tay
  pair with rigid-iff-tight as **isostatic**-iff-tight (literal
  rigid-iff-tight is false: two bodies, `D+1` parallel bars); BH all
  three forms (rank, rigidity iff, tree-packing iff) + the
  genuine-hinge abundance conjunct.
- **BB witness = Whiteley-remark change of extensor coordinates**
  (R0-era `±T` claim refuted at the chapter-extension recon: per JJ's
  Lemma-5.1 entry table only `[c₀,c_k]` segments give `±` basis vectors
  and no segment yields a pure moment vector). Landed as
  `lem:coordinate-extensor-basis` (a spanning argument, not JJ's staged
  elimination) + `lem:extensor-map-rows` (adjoint precomposition).
- **BH witness = the KT Theorem-5.6 panel witness transplanted** (JJ
  Thm 6.4 not re-proved): per-edge meet decomposition into `k` spanning
  points, one coordinate change moving all hinges off the hyperplane at
  infinity simultaneously (the JJ Lemma-7.1 device), affine points read
  off. The BB row-family invariance does not port (`annihRow` is
  basis-pinned); the row-*span-rank* invariance (`mapSupport`) does and
  suffices. `hingePointRow`/`panelRow` bridge is `rfl`.
- **Layer-P witness = the link-recording KT 5.6 form**
  (`..._recordsLinks_...`; the base variant's `reaimSub` off-edge
  fallback breaks the per-edge sign comparison). Its missing blueprint
  pin was repaired by extending `thm:theorem-55-6-genuine`'s `\lean{}`
  list (additive-successor gate). JJ Thm 6.5 + Lemma 7.1 detour
  confirmed unnecessary.
- **Graph-free row families (P/BH):** the annihilator-row family reads
  only `(ends, q)`, so `IsGenericNormals`/`IsGenericHingePoints` take no
  graph; consumers instantiate via an `hends` link hypothesis. BB's
  `IsGenericEndpoints` pins an orientation and quantifies over
  `Set ↥E(G)`.
- **Polynomial-family shapes:** BB = the `2×2` minors of the homogeneous
  pair through `pairIdxEquiv`; BH = the `k×k` minors of the homogenized
  hinge-point matrix via `exteriorPower.ιMultiDual_apply_ιMulti`, no
  `complementIso` staging.
- **Layer-BH citation corrected:** source is JJ 2010 §6 (Thm 6.1,
  Cor 6.2/6.3, Thm 6.4), not §8 (the molecular corollaries — Layer M's
  territory).
- **Unrecon'd-transcription flags all discharged:** (i) the packing
  corollary landed as a literal spanning-tree family, not the
  covering-shaped `IsSpanningTreePacking`; (ii) abundance landed on the
  maximal-minor engine + a `..._reindex` companion, not the sketched
  Gram determinant; (iii) Layer-P nondegeneracy landed with a direct
  two-point moment-curve seed, no `[Infinite K]`.
- **Packing bridge** `Graph.deficiency_eq_zero_iff_exists_spanningTrees`
  landed via the flagged route: `→` through
  `IsKDof.exists_isBase_isForestPacking` + the new
  `Graph.IsTight.connected` helper (`BodyBar/TreePacking.lean`,
  two-component sparsity count); `←` generalizes
  `molecule_generic_square_packing`'s `hdef` block to general `n`.
  Needed a fresh `import Matroid.Graph.Tree` in `Deficiency.lean`.
- **Dep-graph primacy:** the transfer form is the *definition*; the
  abundance polynomial is a *lemma* node.
