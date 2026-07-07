# Phase 25 — projective duality + the molecule modelling equivalence (work log)

**Status:** ✓ Complete (opened 2026-07-06; closed 2026-07-06).

## Current state

**Closed.** All 12 nodes of the forward-mode chapter
`blueprint/src/chapter/molecule-modelling.tex` (`sec:molecule-modelling`) are
green, and the phase-close checklist (`PHASE-BOUNDARIES.md`) has run: ROADMAP
row + §25 compressed, status surfaces synced, the end-to-end chapter re-read
passed with no collapse edits (the prose was authored math-first against the
settled design), and the three exposition-ledger entries are written + `done`
(`notes/BlueprintExposition.md` §`molecule-modelling.tex`).

What the phase delivered, in one paragraph: the `ℝ³` chain *bar-joint of `G²`
↔ molecular (hinge-concurrent body-hinge) of `G` ↔ panel-hinge of `G`*, at the
**rank/motion-space level**. The two cruxes are the screw-velocity API
(`Molecular/Molecule/ScrewVelocity.lean`) and the dictionary iso Φ
(`Molecule/Dictionary.lean`, closing `thm:molecular-iff-square-bar-joint` =
`molecular_finrank_motions_eq_square_ker`); around them sit the
extensor-transport projective invariance (`Molecule/ProjectiveInvariance.lean`,
CW §3.6), the square graph (`SquareGraph.lean`), general-position placements
(`GeneralPositionPlacement.lean`), the general-position Theorem 5.6
(`Molecule/{GeneralPosition4,Theorem56}.lean`,
`exists_rankHypothesis_isGeneralPosition4`), and the projective-duality +
pole-bridge endpoints (`Molecule/{Duality,Modelling}.lean`, closing
`thm:panel-hinge-iff-molecular` =
`exists_molecular_rankHypothesis_generalPosition`).

## Architectural choices (record)

- **Scope `ℝ³` only** (`k = 2`): KT §1.2 / p. 671 are specific to three
  dimensions (except W1/W2, kept dimension-general for free).
- **Rank-level chain over realizability-iff chain** — the recon's central
  verdict (design doc §2; exposition-ledger entry): the iff shape cannot feed
  Cor 5.7 without formalizing two further Jackson–Jordán papers.
- **Formalize-everything frame** (user directive, 2026-07-06): OD-25-1 was a
  *route* question only; it settled as the extensor-transport family with the
  polarity already in tree (`panelSupportExtensor = complementIso ∘
  normalsJoin`).

## Hand-off / next phase

**Next: open Phase 26** (Cor 5.7, the molecule-application capstone) per the
standard protocol (`PHASE-BOUNDARIES.md` *When this commit opens a phase*);
it gates only on this phase. What Phase 26 consumes is pinned in
`notes/Phase25-design.md` §2.6 (kept live there): the two endpoint theorems —
`molecular_finrank_motions_eq_square_ker` (`Molecule/Dictionary.lean`) and
`exists_molecular_rankHypothesis_generalPosition` (`Molecule/Modelling.lean`)
— plus the matroid glue (`genericRank` vs rank-at-a-placement), the `β`-label
supply, the carrier-bridge choice (design flag F4), and the Cor 5.7 statement
(formula attributed to Jackson–Jordán 2008, conjecture-resolution to KT).

Also still open, for a future cleanup round at a phase boundary (not
Phase-26 work): the molecular-layer dead-code/liveness sweep deferred from
`notes/Phase23-cleanup.md`.

## Decisions made during this phase

One-line verdicts (the reasoning lives in the Lean sources, the chapter
prose, `notes/Phase25-design.md`, and git history). Build ran W2/W3/W5 →
W1 → W4, W6, W7, matching the design §3 leaf table.

### Phase-local choices and proof techniques

- **W3** (`SquareGraph.lean`): `square` via `Set.Nonempty (G.commonNeighbors
  u v)`; `closedNeighborSet = insert v (G.neighborSet v)`; mirror lemma
  `ncard_neighborSet_eq_degree` added to the `Mathlib/…/Finite.lean`
  upstream-candidate file.
- **W2** (`Molecule/ProjectiveInvariance.lean`): `mapExtensor F Λ` transport
  along `ScrewSpace k ≃ₗ ScrewSpace k`; core
  `infinitesimalMotions_mapExtensor`; rescaling sibling
  `infinitesimalMotions_scaleExtensor`. Non-module file (needs the
  non-module `Pinning.lean`'s `RankHypothesis`); dimension-general.
- **W5** (`GeneralPositionPlacement.lean`): order-≤4 moment-curve affine
  independence (`affineIndependent_momentCurve3_of_injective`, Vandermonde)
  lifted to all `≤4`-subfamilies by padding with `V ⊕ Fin 4`; combined
  existence re-runs Phase 24's interpolation with a second finite bad-`t`
  family.
- **W1** (`Molecule/ScrewVelocity.lean`, module file): `screwOmega`/`screwTau`
  as lifts of hand-rolled `Fin 2` alternating forms;
  `screwCoord_injective` via the explicit right inverse `rebuild` +
  rank–nullity; brick (4) `existsUnique_screwVel_eq` by the explicit
  cross-product `ω`-construction (`exists_crossProduct_eq`, vector triple
  product) — no bar-joint triangle-rank fact needed (design flag F2
  bypassed).
- **W4** (`Molecule/Dictionary.lean`, non-module): `molecularOfCentres` +
  `Φ = molecularVel c` as `LinearMap.pi` of `screwVelL`; well-definedness by
  reduction to a common body (`exists_mem_closedNeighborSet_of_square_adj` +
  `screwVel_eq_zero_of_link`); injective by min-degree-2 + GP + brick (3);
  surjective by per-clique `∃!` screws + brick-(2) reverse; finrank equality
  via `LinearEquiv.ofBijective`. GP → LI bridges live in
  `GeneralPositionPlacement.lean`. F3 (PiLp glue): the real inner product on
  `EuclideanSpace ℝ (Fin 3)` is `ofLp a ⬝ᵥ ofLp b`.
- **W6** (`Molecule/{GeneralPosition4,Theorem56}.lean` + `Theorem55.lean`):
  `IsGeneralPosition4` + the avoidance polynomial
  (`exists_generalPosition4_polynomial`, leading `j×j` minors at the moment
  curve + last-coord product); the **F1 fix** — the base genuine Thm-5.5
  producer's `ends` failed `hends` on re-added edges, fixed by the sibling
  link-recording producer `rankHypothesis_genuine_recordsLinks_of_theorem_55_gen`
  (`reaimSubLink`); assembly `exists_rankHypothesis_isGeneralPosition4` =
  CaseII-style rank pinch at an alg-indep seed, plus a fresh single-body
  branch (edgeless, `def = 0`, moment-curve normals).
- **W7** (`Molecule/{Duality,Modelling}.lean`): the dual lemma is the W2
  transport at `Λ := screwComplementIso` (`screwComplementIso_lineExtensor`
  closes by `rfl` after unfolding); the **pole bridge** dehomogenizes Thm-5.6
  normals by their nonzero last coord to centres, transfers `RankHypothesis`
  via equal hinge spans (`panelSupportExtensor_smul_left` + mono both ways)
  + `rankHypothesis_ofNormals_homogenize_iff`, and GP via
  `affineIndependent_iff_linearIndependent_homogenize`.

### Promoted to TACTICS-QUIRKS / FRICTION / the exposition ledger

- Dot-notation `mem_commonNeighbors.mpr` failure → TACTICS-QUIRKS § 75.
- FRICTION idioms captured per slice (all under *[idiom]*): equiv-transport
  `▸` over-rewrite (state a `T`-form iff variant); computing lifted
  alternating-form values on `mk (extensor v)`; `map_smul` over-firing on
  bilinear `crossProduct`; `⨯₃` is U+2A2F; `dotProduct`/`.det` namespace
  traps; `set` + `rw` pattern search; `EuclideanSpace` inner product =
  `ofLp ⬝ᵥ ofLp`; `WithLp.linearEquiv` `invFun` residual; Finset-subfamily →
  `Fin m` LI transport; no `rw` of a `Finset`-value equation under a
  dependent binder; viewing an ∃-bound framework as `ofNormals`;
  `BodyHingeFramework` equality via `congrArg mk`;
  `LinearIndependent.units_smul` rescaling; `AffineIndependent.map'` across
  the `toLp` boundary.
- Exposition-ledger entries (3, all `done`):
  `notes/BlueprintExposition.md` §`molecule-modelling.tex` — the unpublished-
  [35] reconstruction + sharp order-4 hypothesis; the rank-level-chain
  verdict; the "nonparallel" one-word compression (KT p. 671).
