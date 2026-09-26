# Phase 40b — PENCIL-X0 / CARRIER: planar pictures, the lifting space, `X₀`, and "the general point attains" (work log)

**Status:** in progress (opened design-first 2026-09-26). C1a, C1b, C2 (both the `U`-open
lemma and the lifting-space API), DUAL-K (the polarity over every field), C3 (the picture→normal
API), and C4 (the configuration as a pencil framework, with (MC-3)'s scale-and-shift rank
invariance) landed 2026-09-26. **C1–C4 and DUAL-K are DONE.** **Next: C5 (`X0Attains` at the flat
witness, opus/fragility).** Plan: `notes/Phase40-design.md` §3.

## Current state

**Next concrete step: C5 (`X0Attains` at the flat witness)** (*Hand-off*); every CARRIER slice
before it is landed. All Lean is in
`CombinatorialRigidity/Molecular/Molecule/Pencil/MainComponent/Carrier.lean` (~1280 lines):
C1a's seven definitions and `Graph.mem_liftingSpace`; C1b's one-witness upgrade
`Graph.x0Attains_of_exists`; C2's `U`-open lemma and lifting-space API (`Aff(q) ⊆ L(q)`,
`dim Aff(q) = 3`, `3 ≤ dim L(q)`; the codim bound is **dropped**, *Decisions made*); C3's
picture→normal API; and C4's configuration framework, its rank equality with `ofNormals`, the
bridge to `HasDistinctPencilRealization`, the `X0Dist` leg `Graph.X0Attains.hasDistinctPencilRealization`,
and (MC-3)'s scale-and-shift invariance (checklist below). DUAL-K generalized the polarity
`screwComplementIso` and `ProjectiveInvariance.lean` to `[Field K]` in place.

`blueprint/src/chapter/main-component.tex` carries five green definition nodes and the green
lemmas `lem:pencil-lifting-space-affine` (C2), `lem:pencil-x0-one-witness` (C1b),
`lem:pencil-x0-main-picture-open` (C2), `lem:pencil-selector-plane-contains-nbhd` /
`lem:pencil-selector-independent-scalar` (C3), and C4's four: `lem:pencil-config-point-join-rank`,
`lem:pencil-config-distinct-realization`, `lem:pencil-rank-scale-shift`, and
`lem:pencil-x0-attains-distinct` (the `X0Dist` half of `thm:pencil-x0-generic-attains`'s
"granting this" clause). Red: `lem:pencil-condition-linear` (only its forward direction is
proved), `lem:pencil-hinge-affine` (only its last clause, now `lem:pencil-rank-scale-shift`),
`thm:pencil-x0-main-component`, and `thm:pencil-x0-generic-attains` (the `X0Gen` half and the
induction are open).

## Architectural choices made up front

The coordinator's adjudication (2026-09-26), settling the design recon:

- **Uncurried picture coordinates `q : α × Fin 2 → K`** (not curried `α → Fin 2 → K`).
  `PanelHingeFramework.ofNormals` takes `q : α × Fin (k+2) → K` and the rank polynomial lives in
  `MvPolynomial (α × Fin 2) K`, so uncurried composes directly with the landed machinery.
- **A single `X0Attains` predicate** carrying a nonzero `MvPolynomial (α × Fin 2) K`, with
  fibre-genericity/semicontinuity proved once in a mirror lemma `x0Attains_of_exists` (NOT two defs
  `X0Attains` + `X0GenericAttains`). `X0Dist` consumes one attaining `(q, z)`; `X0Gen` consumes the
  fibre-open clause (C1a verdict, *Decisions*).
- **The picture→normal map is `cross₃` of homogeneous config points** — polynomial, denominator-free.
  "Rational parametrization" collapses to a fibre polynomial at a fixed admissible `q`; the Cramer
  chart lives in the proof, not the def.
- **β-headroom fix: an additive-successor `_of_card` triple** (`x0Dist_of_card`, `x0Gen_of_card`,
  `pencil_conjecture_of_card`) concluding the UNCHANGED L0 predicates `X0Dist`/`X0Gen` and reusing the
  protected `pencil_conjecture_of_X0` verbatim. L0 is protected: not edited, not made
  unprovable-as-stated. These are MOTIVES leaves — the planned signatures are recorded, they do not
  land here. Mirrors `molecular_conjecture_multigraph`'s `hcard`+`hspan` shape (type-checked in the
  recon, only the MOTIVES bodies sorried).

## Lemma checklist

Leaf plan in dependency order (from the recon; rungs and fragility flags noted). Fragility zone =
anything touching `ScrewSpace`/the opaque carrier or `rigidityRows` rank arithmetic → opus minimum.

- [x] **C1a–C3, DUAL-K** (landed 2026-09-26; signatures in `Carrier.lean`'s module docstring and
  its declarations). C1a: the seven definitions. C1b: `Graph.x0Attains_of_exists` (no
  `[Infinite K]`), with `Graph.IsAdmissiblePicture.{exists_mvPolynomial, supportExtensor_ne_zero}`
  and `Graph.liftingMatrix`. C2: `Graph.exists_mvPolynomial_isMainPicture` (`[Infinite K]`, taking
  `hloop : G.Loopless`, `h3 : ∀ v ∈ V(G), 3 ≤ (G.closedNbhd v).ncard`; STEPS uses it) and
  `Graph.{affineLifts_le_liftingSpace, finrank_affineLifts, three_le_finrank_liftingSpace}`; the
  codim bound is dropped (FLAT's (MC-4)(b) subsumes it; FLAT's recon may reinstate it). C3:
  `pencilNormalOfPicture_ne_zero_iff`, the picture→configuration independence transport,
  `dotProduct_pencilNormalOfPicture_eq_zero_of_mem_closedNbhd`,
  `exists_smul_pencilNormalOfPicture_eq_of_mem_closedNbhd`, and `pencilNormalOfPicturePoly` (the
  shape `X0Gen`'s fibre intersection needs). DUAL-K: `screwComplementIso` and
  `ProjectiveInvariance.lean` at `[Field K]`, names unchanged.
- [x] **C4 — the config as a pencil framework** (landed 2026-09-26, opus); the coordinator's
  scope-pin, final signatures (`p := pencilConfigPoint q z`), all in `Carrier.lean`:
  1. `pencilConfigFramework G ends q z : BodyHingeFramework K 2 α β` (hinge `mk (extensor ![p (ends
     e).1, p (ends e).2])` on `E(G)`, the standard-basis join off it; no `[Inhabited α]`), and
     `Graph.IsAdmissiblePicture.pencilConfigFramework_supportExtensor_ne_zero hq hends z e`.
  2. `finrank_span_rigidityRows_pencilConfigFramework G ends q z` — `finrank` of its row span `=`
     that of `(ofNormals (k := 2) G ends (fun p => pencilConfigPoint q z p.1 p.2)).toBodyHinge`;
     **no `hends`** (*Decisions*). Via `ofNormals_toBodyHinge_eq_mapSupport_pointJoinFramework`.
  3. `Graph.IsAdmissiblePicture.hasDistinctPencilRealization hq hends (hz : z ∈ G.liftingSpace q)
     (hrank : (finrank … : ℤ) = screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency 3) :
     HasDistinctPencilRealization K 3 G`; its realization half,
     `Graph.IsAdmissiblePicture.hasPencilPanelRealization_pencilConfigFramework hq hends hz hsel`,
     takes any selector with `hsel : ∀ v ∈ V(G), (∀ i, sel v i ∈ G.closedNbhd v) ∧
     LinearIndependent K (fun i => pencilPicturePoint q (sel v i))`, for `X0Gen` to reuse.
  4. `Graph.X0Attains.hasDistinctPencilRealization [Infinite K] (h : G.X0Attains K) :
     HasDistinctPencilRealization K 3 G` (`lem:pencil-x0-attains-distinct`).
  5. **Fit, landed:** `Graph.finrank_span_rigidityRows_ofNormals_smul_add_affineLifts hends q z
     (ht : t ≠ 0) (ha : a ∈ G.affineLifts q)`, rank at `(q, t • z + a)` `=` rank at `(q, z)`
     (`lem:pencil-rank-scale-shift`); `lem:pencil-hinge-affine` stays red.
  6. **Dropped:** the `→` of "support extensor `≠ 0 ↔ q_u ≠ q_v`" (no consumer; item 3 did not
     need it). Hygiene: C3's unused `_hLI` dropped, caller updated.
- [ ] **C5 — `X0Attains` at the flat witness** (opus, fragility): `X0Attains` holds at a flat config
  `(q, 0)` from a single seed; rank arithmetic on `rigidityRows`. Enters through C1b (`0 ∈ L(q)`,
  `q` main). The entry point STEPS extends.

Blueprint red nodes for the four MC labels stay in `main-component.tex`; each flips to `\lean{}` +
`\leanok` in the commit that lands its Lean.

## Blockers / open questions

Two questions are recorded for the **MOTIVES pre-build recon**, deliberately NOT resolved now (both
recons disagreed; settle against the landed SPINE2 threading at MOTIVES, not now):

- **(a) The exact `hcard` constant.** The opus recon read it as `bodyBarDim 3 · (|α|−1)` (= `6·`,
  matching `molecular_conjecture_multigraph` and `freshEdgeSupply_of_card_lt_of_noRigid_of_degree_two`,
  `Molecule/Pencil/Escape.lean`); the fable recon read `3 · (|α|−1)`. Pin against the SPINE2
  producer's actual `hfresh`/`hcard` threading when MOTIVES builds the `_of_card` triple.
- **(b) The headroom root cause.** The opus recon attributed the fresh-edge need to the split-off's
  `e₀ ∉ E(G)` (the `hK`/`hbareSplit` slots in `Escape.lean`); the fable recon read `splitOff`'s body
  (`Induction/Operations.lean:770`) and argued split-off can reuse a freed label, locating the real
  source in BRIDGE consuming SPINE2's `hfresh`. Plus the opus recon's sub-gap: the landed fresh-edge
  supply lemma keys on *sparsity* (no proper rigid subgraph), while the X₀ split-off step is applied
  at `δ ≥ 5` — MOTIVES settles which supply lemma discharges `e₀ ∉ E(G)`.

## Hand-off / next phase

**C1–C4 and DUAL-K are DONE.** **Next commit: C5 (`X0Attains` at the flat witness, opus/
fragility)**, per its checklist item: `X0Attains` at a flat configuration `(q, 0)` from a single
seed, entering through C1b's `Graph.x0Attains_of_exists` (`0 ∈ L(q)`, `q` main). How its rank is
read bears on C4's `finrank_span_rigidityRows_pencilConfigFramework` (`ofNormals` rank = point-join
rank) and on the flat-or-cone choice (`Phase40-design.md` §3, FLAT's recon bullet). `Carrier.lean`
is ~1280 lines: if C5 runs past ~220 lines, put it in a sibling `MainComponent/` file importing
`Carrier.lean`. Do NOT open FLAT or any successor layer; CARRIER closes after C5.

## Decisions made during this phase

- **2026-09-26 — C4 closes: the polar/primal rank equality needs no `hends`, and (MC-3) fit.** The
  patch agrees with the unpatched point-join framework on every link whatever `ends` names, so
  the pinned `hends` on item 2 was dropped (unused argument); items 3–5 keep it (orientation,
  and endpoints in `V(G)` for the affine shift). `HasCoplanarPanelRealization` needs a nonzero
  hinge on every label of `β`, hence the patch. Four scoped green nodes; the MC nodes stay red.
- **2026-09-26 — C3: item 3 needs only `z ∈ L(q)`** (four vectors of `K³` are dependent); its
  unused `_hLI` was dropped in C4. `lem:pencil-condition-linear` stays red.
- **2026-09-26 — C2: moment-curve admissible picture, `Nat.sInf` minimizer, reused section mirror
  at the kernel vector `0`; `Aff(q)` as a linear map's range; codim bound dropped** (scope-pin).
- **2026-09-26 — C1b: the Cramer section uses a left inverse, not a maximal minor** (TACTICS-GOLF
  § 25).
- **2026-09-26 — opened design-first; C1a shapes.** The rank is read at `ofNormals` of the
  configuration points, not the plane normals (a zero hinge would weld a def₂-rigid subgraph);
  `U` is a def; `X0Attains` carries fibre-openness via a per-picture `R`; `L(q)` vanishes off
  `V(G)`; `ends` is link-relative.
- **2026-09-26 — duality recon and DUAL-K** (`Phase40-design.md` §4): the polarity is field-free;
  `ProjectiveInvariance.lean` was generalized in place (frozen-doc citations ruled out a restatement).
