# Phase 34 — PROSPECT G3: the generic lift (work log)

**Status:** in progress (opened 2026-07-17, recon-first; R0 answered and
scope adjudicated 2026-07-17; Layers M, P, BB closed and Layer BH at
11/12 nodes as of 2026-07-18).

Planning input: `notes/Prospect.md` — the Tier-2 **G3** entry and its open
recon question. Queue position user-adjudicated 2026-07-10 (`notes/Prospect.md`
*Hand-off* item 4); the queue order re-confirmed with the user at this
opening (2026-07-17). Primary source: Jackson–Jordán, *The generic rank of
body-bar-and-hinge frameworks*, Eur. J. Combin. **31** (2010), 574–588 —
already the project's `jacksonJordan2009` bib entry / `formalization.yaml`
source (the def = corank bridge came from it in Phase 19).

## Current state

**Next concrete commit: `cor:bodyhinge-generic-tree-packing`** — see
*Hand-off*. This is the last node of Layer BH and of the phase.

The blueprint chapter `generic-lift.tex` is open (forward mode) and carries
all four layers; **Layers M, P, and BB are fully green** and **Layer BH is
at eleven of twelve nodes green**:

- **Layer M** (closed 2026-07-17, four nodes): `Molecular/Molecule/Application.lean`
  + `GenericRigidityMatroid.lean`. Routes/shapes: *Decisions made*.
- **Layer P** (closed 2026-07-17, seven nodes):
  `Molecular/GenericLift/PanelGeneric.lean` (new file). The rank-formula
  pinch there (`finrank_span_rigidityRows_ofNormals_of_isGenericNormals`)
  is the template the remaining BH statement nodes mirror.
- **Layer BB** (closed 2026-07-17, nine nodes over five slices):
  `BodyBar/GenericLift.lean` (new file) + three `TayTheorem.lean` additions
  (the `E'`-restricted generalizations + the `IsIndependent`↔rows bridge).
  Witness = JJ Lemma 5.1's coordinate segments via the Whiteley-remark
  change of extensor coordinates (the R0-era `±T` claim is refuted —
  *Decisions made*).
- **Layer BH** (chapter extension + 10 slices landed 2026-07-17/18):
  `Molecular/GenericLift/HingeGeneric.lean` (new file) +
  `Molecular/Extensor.lean` adders (`extensor_update_add_smul`,
  `extensor_shear`, `exists_affineSubspaceExtensor_eq_smul_extensor`).
  Green: coordinatization (`hingeExtensorPoly`), definition
  (`hingePointRow`/`IsGenericHingePoints`), abundance + existence (with the
  genuine-hinge affine-independence conjunct), nondegeneracy, the witness
  trio (`mapSupport` rank invariance, `exists_linearEquiv_forall_last_ne_zero`,
  the extensor affine representation), the witness assembly
  `exists_hingePoints_independent_hingePointRow` (incl. the
  `screwEquivOfLinearEquiv` plumbing), and the rank/rigidity pair
  `finrank_span_rigidityRows_ofHinge_of_isGenericHingePoints` /
  `isInfinitesimallyRigidOn_ofHinge_isGenericHingePoints_iff` (the Layer-P
  pinch verbatim; the witness assembly already reports the target rank as
  the extracted subfamily's cardinality, so no separate row-count
  recomputation was needed here unlike Layer P's `hrank0`), and the packing
  bridge `deficiency_eq_zero_iff_exists_spanningTrees` (2026-07-18,
  `Deficiency.lean`, namespace `Graph` — see *Decisions made*). Remaining:
  the tree-packing corollary (checklist).

Per-slice friction from all layers is promoted (TACTICS-QUIRKS §38-variants,
§90–§97; FRICTION.md entries incl. the nonzero-functional-as-coordinate
recipe and the `RingHomInvPair`-diamond workaround) — the phase note does
not duplicate it.

## What the phase targets (statement surface)

Upgrade the project's **existence-form** realization statements to the
**generic** ("almost all realizations") form, via the Jackson–Jordán 2010
coordinate route (their Thms 5.2, 6.1/6.4, 7.2 and the §8 molecular
corollaries), which avoids Whiteley 1988's variety-irreducibility machinery
(the lift `body-bar.tex` and `body-hinge.tex` defer with "not pursued
here", standing since Phases 15/16). The affected surface: Tay's body-bar
theorem (Phase 15), the body-hinge Tay–Whiteley statement (Phase 16 —
**R0 caution:** the Phase-16 object is the bar-bundle reduction; the
JJ-faithful generic body-hinge statement runs on the molecular
`BodyHingeFramework K k α β` via `ofHinge`, Layer BH), and the molecular
statements (JJ 2010 p. 586: every generic bar-joint realization of `G²` in
ℝ³ is rigid whenever `5G` packs six edge-disjoint spanning trees).

Carriers (adjudicated): the BB surface stays at ℝ (no ℝ→K sweep of
`BodyBar/*.lean`); the Molecular-side layers stay `[Field K] [Infinite K]`
as landed (Phase 33).

## Work-item checklist

- [x] **R0 — the opening recon**: verdict ACCEPTED 2026-07-17 (*Decisions made*).
- [x] **Adjudicate scope + route on R0's verdict**: done 2026-07-17
  (*Decisions made*, verbatim).
- [x] **Chapter-open** (2026-07-17) — `generic-lift.tex`, forward mode,
  Layer-M grain (*Decisions made*).
- [x] **Layer M** — molecular / bar-joint `G²` (d = 3, ℝ). Closed 2026-07-17,
  four nodes green (`SimpleGraph.molecule_generic_rank`/`molecule_generic_rigid`/
  `molecule_generic_square_packing`, `Molecular/Molecule/Application.lean`;
  `SimpleGraph.exists_isGenericPlacement_abundance`, `GenericRigidityMatroid.lean`).
- [x] **Layer P** — panel-and-hinge over normals, `[Field K] [Infinite K]`
  (JJ Thm 7.2 analogue). Closed 2026-07-17, seven nodes green
  (`Molecular/GenericLift/PanelGeneric.lean`; statement decls
  `finrank_span_rigidityRows_ofNormals_of_isGenericNormals` /
  `isInfinitesimallyRigidOn_ofNormals_isGenericNormals_iff`).
- [x] **Layer BB** — body-bar at ℝ, endpoint-parameterized ("almost all bar
  endpoint choices"). Closed 2026-07-17, nine nodes green
  (`BodyBar/GenericLift.lean` + `TayTheorem.lean` adders; statement decls
  `linearIndependent_rigidityRow_ofEndpoints_iff` /
  `isIndependent_and_isInfinitesimallyRigid_ofEndpoints_iff`). Ground-truth
  signatures are the Lean files themselves.
- [ ] **Layer BH** — geometric body-hinge over `ofHinge` hinge points,
  `[Field K] [Infinite K]`; JJ 2010 §6 (Thm 6.1 / Cor 6.3 / Thm 6.4 — the
  "Thm 8.1/8.2" pointer was a corrected mis-attribution, *Decisions made*).
  Chapter extension landed 2026-07-17 (`sec:generic-lift-bodyhinge`, twelve
  nodes, plus `lem:deficiency-zero-iff-tree-packing` in `deficiency.tex`;
  Lean home `Deficiency.lean`). **Eleven of the twelve chapter nodes green**
  — see *Current state*; ground truth `Molecular/GenericLift/HingeGeneric.lean`.
  `thm:bodyhinge-generic-rank` / `cor:bodyhinge-generic-rigid` landed
  2026-07-18 (`finrank_span_rigidityRows_ofHinge_of_isGenericHingePoints` /
  `isInfinitesimallyRigidOn_ofHinge_isGenericHingePoints_iff`,
  `HingeGeneric.lean`). The separate packing-bridge node
  `lem:deficiency-zero-iff-tree-packing` also landed 2026-07-18
  (`Graph.deficiency_eq_zero_iff_exists_spanningTrees`, `Deficiency.lean` —
  see *Decisions made*). **Remaining: the chapter's last node**
  (`cor:bodyhinge-generic-tree-packing`), target signature:

  ```
  -- cor:bodyhinge-generic-tree-packing (HingeGeneric.lean, namespace
  --   BodyHingeFramework; JJ Cor 6.3 in every-generic form; compose
  --   isInfinitesimallyRigidOn_ofHinge_isGenericHingePoints_iff with the landed
  --   packing bridge deficiency_eq_zero_iff_exists_spanningTrees)
  theorem isInfinitesimallyRigidOn_ofHinge_isGenericHingePoints_iff_spanningTrees
      [Infinite K] … (same setting, no q) :
      (∀ q : β × Fin k × Fin (k + 1) → K, IsGenericHingePoints ends q →
          (ofHinge G fun e a b => q (e, a, b)).IsInfinitesimallyRigidOn V(G))
        ↔ ∃ Ts : Fin (bodyBarDim n) → Graph α (β × Fin (bodyHingeMult n)),
            (∀ i, Ts i ≤s G.mulTilde n) ∧ (∀ i, (Ts i).IsTree) ∧
              Pairwise (Function.onFun Disjoint fun i => E(Ts i))
  ```

**Shared definition shape (all layers, R0 recommendation, accepted):** the
Phase-24 transfer form — `IsGeneric (p : Params) := ∀ s : Set ι,
(∃ q, LinearIndependent K (fun i : s => rows q i)) →
LinearIndependent K (fun i : s => rows p i)` (the
`SimpleGraph.IsGenericPlacement` shape; subsumes JJ's edge-induced-submatrix
clause, basis-canonical on the project's row families) — plus the
adjudicated **abundance lemma** `∃ P : MvPolynomial σ K, P ≠ 0 ∧
∀ p, MvPolynomial.eval p P ≠ 0 → IsGeneric p` as the formal "almost all"
(one `MvPolynomial.exists_eval_ne_zero` shot on the product of witnessing
minors gives both existence and abundance).

## Blockers / open questions

- None. The packing bridge's flagged `IsTight`-connectivity helper landed as
  `Graph.IsTight.connected` (`BodyBar/TreePacking.lean`, two-component
  sparsity count via `Graph.Separation`) — see *Decisions made*.

## Hand-off / next phase

Layers M, P, and BB are all fully green; Layer BH has one node left. The
rank/rigidity pair and the packing bridge
(`lem:deficiency-zero-iff-tree-packing`,
`Graph.deficiency_eq_zero_iff_exists_spanningTrees`, `Deficiency.lean`)
landed 2026-07-18.

- **Next concrete commit: `cor:bodyhinge-generic-tree-packing`**
  (`isInfinitesimallyRigidOn_ofHinge_isGenericHingePoints_iff_spanningTrees`,
  `HingeGeneric.lean`, namespace `BodyHingeFramework`; target signature in
  the Layer-BH checklist item) — compose
  `isInfinitesimallyRigidOn_ofHinge_isGenericHingePoints_iff` with
  `Graph.deficiency_eq_zero_iff_exists_spanningTrees`. **Closing this node
  closes Layer BH and the phase** (run the `PHASE-BOUNDARIES.md`
  phase-close checklist on that commit).

## Decisions made during this phase

- **User adjudication (2026-07-17, verbatim; overrides any conflicting
  phase-note text):**
  1. "Almost all" statement strength: **(b) abundance polynomial** —
     existence of generic + every-generic-rigid + the lemma
     `{p : P(p) ≠ 0} ⊆ {generic}` for one nonzero MvPolynomial P. (The ℝ
     Lebesgue-null upgrade (c) is NOT in scope.)
  2. Parameter-space faithfulness: **fully JJ-faithful** — body-hinge over
     the `ofHinge` hinge-point parameterization AND body-bar over an
     endpoint-parameterized segment layer `T(p,p')` (the "new modest
     layer" your verdict described; the statement should read "almost all
     bar endpoint choices"). This deliberately goes beyond your mixed
     recommendation.
  3. Carrier for BB/BH-combinatorial: **state at ℝ** — no ℝ→K sweep of
     `BodyBar/*.lean`; the Molecular-side layers stay
     `[Field K] [Infinite K]` as landed.
  4. Layers: **all four, M → P → BB → BH** (your cost-ranked order);
     sub-letter at the body-bar-vs-molecular seam if the phase runs long,
     per the existing phase-note seam entry.
  5. Rigidity form vs rank-formula form: not separately adjudicated —
     your recommendation stands as the default: decide per layer at
     chapter-open.
- **Seam adjudication (user, 2026-07-17): Layer P continued in this phase
  number** — no sub-letter; the body-bar boundary passed without one.
- **R0 verdict (2026-07-17): ACCEPTED — the product route substitutes;
  alg-indep does not return.** JJ 2010's "generic" is a *max-rank*
  definition at all four layers; alg-indep over ℚ appears only in "thus
  'almost all'" abundance remarks, never in a theorem's proof. Project
  precedent `SimpleGraph.IsGenericPlacement` (Phase 24); the formal
  "almost all" is the abundance polynomial via
  `MvPolynomial.exists_eval_ne_zero`. Nothing in Phase 30's deletion
  inventory is needed. Full reasoning: the R0 dispatch return (git history)
  + the JJ PDF.
- **Chapter-open grain (2026-07-17): Layer M only; P/BB/BH as
  chapter-extension design passes.** Their exact statement shapes were
  recorded build-time opens — minting them at chapter-open would be
  unrecon'd transcription (the Phase-32 lesson). This paid off twice: the
  Layer-BB pass refuted the R0-era `±T` claim and the Layer-BH pass caught
  the §8-vs-§6 mis-citation, both before any Lean was built on them.
- **Per-layer strength calls (adjudication item 5).** Layer M: both forms +
  the JJ p. 586 packing corollary (the rank form is a one-step composition,
  costs nothing). Layer P: both forms (the witness/B2 pinch *is* the rank
  formula; the iff is a thin rank–nullity corollary). Layer BB: per-subset
  independence characterization + the Tay pair, with "rigid iff tight"
  implemented as **isostatic** iff tight (literal rigid-iff-tight is false —
  two bodies, `D+1` parallel bars — and there is no `def_D` carrier for
  plain multigraphs, so no rank formula; the matroid content is the
  per-subset iff against `thm:unionPow-cycle-indep-iff-sparse`, closing
  prose only). Layer BH: all three forms (rank, rigidity iff, tree-packing
  iff — JJ Cor 6.3 sharpened to every-generic) plus the genuine-hinge
  abundance conjunct (per-edge affine independence as one more
  reference-minor product factor).
- **R0-era `±T` witness claim refuted; Whiteley-remark reroute (2026-07-17,
  Layer-BB chapter-extension recon).** Per JJ's Lemma-5.1 entry table
  (p. 581), only `[c₀, c_k]` segments give `±` basis vectors, and no
  segment yields a pure moment basis vector (zero direction ⟹ zero
  extensor) — so the landed standard-basis witness is not `±T`-image.
  Landed route: the `D` coordinate-segment extensors form a basis
  (`lem:coordinate-extensor-basis`, landed as a **spanning** argument, not
  JJ's staged elimination; blueprint rewritten to match) + a fixed
  invertible extensor-space map preserves row independence via adjoint
  precomposition (`lem:extensor-map-rows`) — the change of coordinates JJ's
  Remark attributes to Whiteley, reusing the landed `stdFramework` chain.
- **Layer-BH citation corrected (2026-07-17): source is JJ 2010 §6**
  (Thm 6.1 max rank, p. 583 generic definition, Cor 6.2/6.3 credited to
  Tay 1989 + Whiteley 1988, Thm 6.4), not Thm 8.1/8.2 (§8 = the molecular
  corollaries, Layer M's territory). The earlier checklist pointer was a
  mis-attribution.
- **Layer-BH witness route (2026-07-17, landed 2026-07-18): transplant the
  KT Theorem-5.6 panel witness; do not re-prove JJ Thm 6.1/6.4.** Per edge,
  the panel meet decomposes into `k` spanning points
  (`exists_extensor_eq_panelSupportExtensor_gen`); one coordinate change
  moves all hinges off the hyperplane at infinity simultaneously (the JJ
  Lemma-7.1 device); affine points are read off
  (`exists_affineSubspaceExtensor_eq_smul_extensor`). The BB
  `lem:extensor-map-rows` row-family shape does **not** port (`annihRow` is
  basis-pinned); the invariance that holds — and suffices, W6e consumes a
  rank bound — is row-*span-rank* level (`mapSupport`). The
  `hingePointRow`/`panelRow` bridge is `rfl`, no ± transport (unlike
  Layer P); the assembly's per-edge factor is a genuine `Kˣ` scalar.
- **Layer P witness = the link-recording KT 5.6 form** (2026-07-17,
  chapter-extension recon; also consumed by the BH witness). The base
  `rankHypothesis_genuine_of_theorem_55_gen` is refuted for transplant use:
  its `reaimSub` off-edge fallback puts a foreign-panel extensor on
  re-added edges, breaking the per-edge sign comparison. The
  `..._recordsLinks_...` variant restores it; its missing blueprint pin was
  repaired by extending `thm:theorem-55-6-genuine`'s `\lean{}` list
  (additive-successor gate). The JJ Thm 6.5 + Lemma 7.1 detour is
  confirmed unnecessary with this refinement.
- **Graph-free row families (Layers P/BH definitions).** The
  annihilator-row family reads only the endpoint selector and the parameter
  assignment (verified against `panelRow`/`ofNormals`/`ofHinge` bodies), so
  `IsGenericNormals`/`IsGenericHingePoints` take `(ends, q)` only;
  consumers instantiate over `G` via an `hends` link hypothesis. Layer BB's
  `IsGenericEndpoints` pins an orientation `D` (row signs) and quantifies
  over `Set ↥E(G)`.
- **Polynomial-family shapes (both build-time opens, settled at the
  respective chapter extensions).** BB: `T(p,p')` = the `2×2` minors of the
  homogeneous pair, indexed through the fixed `pairIdxEquiv` enumeration
  (any equiv works — the coordinate formula is the contract); direction
  degree 1, moment degree 2; parameters flattened `q : β × Bool × Fin n → ℝ`.
  BH: the screw-basis coordinates of the `ofHinge` extensor are the `k×k`
  minors of the homogenized hinge-point matrix (degree ≤ k), computed
  directly via `exteriorPower.ιMultiDual_apply_ιMulti` +
  `exteriorPower.basis_repr_apply` — no `complementIso` staging; annihilator
  assembly mirrors `annihRowPoly`.
- **Dep-graph primacy (2026-07-17): the transfer form is primary.**
  `def:generic-placement` (and its per-layer instantiations) is the
  *definition*; the abundance polynomial is a *lemma* node.
- **Unrecon'd-transcription flags: all discharged** (the Phase-32 guard).
  (i) the packing corollary's hypothesis shape — landed as a literal
  spanning-tree family (`Ts : Fin 6 → …`, spanning-subgraph + tree +
  pairwise-disjoint), NOT the covering-shaped `IsSpanningTreePacking`
  (stronger than JJ's "contains six"); `hmin` derived *from* `hdef` via the
  KT Lemma 4.6 machinery rather than a fresh pigeonhole (blueprint
  reordered to match). (ii) the abundance product route — landed on the
  maximal-minor engine (`exists_polynomial_ne_zero_of_linearIndependent_at`
  + new `..._reindex` companion), not the sketched Gram determinant
  (blueprint updated). (iii) Layer-P nondegeneracy — landed with a direct
  two-point moment-curve seed, no `[Infinite K]`, no
  `IsGeneralPosition`/`ofParam` detour (blueprint statement + proof
  rewritten to match).
- **Packing bridge landed via the flagged route, no detours (2026-07-18).**
  `Graph.deficiency_eq_zero_iff_exists_spanningTrees` (`Deficiency.lean`):
  `→` assembles `IsKDof.exists_isBase_isForestPacking`'s base into a
  spanning-tree packing via the new `Graph.IsTight.connected` helper (the
  flagged two-component sparsity count, via `Graph.Separation`;
  `BodyBar/TreePacking.lean`, next to `isSpanningTreePacking_of_isTight`);
  `←` generalizes `molecule_generic_square_packing`'s `hdef` block verbatim
  to general `n` (no `|V|=1` special case needed — that branch was for the
  *rigidity* conclusion, not the deficiency count). Needed a fresh `import
  Matroid.Graph.Tree` (`Connected.isTree_of_maximal_isAcyclicSet` isn't
  transitively pulled in by `Matroid.Graphic`, unlike `IsTree` itself).
  Blueprint `lem:deficiency-zero-iff-tree-packing` flipped green, matching
  proof verbatim.
