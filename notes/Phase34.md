# Phase 34 — PROSPECT G3: the generic lift (work log)

**Status:** in progress (opened 2026-07-17, recon-first; R0 answered and
scope adjudicated 2026-07-17).

Planning input: `notes/Prospect.md` — the Tier-2 **G3** entry and its open
recon question. Queue position user-adjudicated 2026-07-10 (`notes/Prospect.md`
*Hand-off* item 4); the queue order re-confirmed with the user at this
opening (2026-07-17). Primary source: Jackson–Jordán, *The generic rank of
body-bar-and-hinge frameworks*, Eur. J. Combin. **31** (2010), 574–588 —
already the project's `jacksonJordan2009` bib entry / `formalization.yaml`
source (the def = corank bridge came from it in Phase 19).

## Current state

**The blueprint chapter is open** (2026-07-17;
`blueprint/src/chapter/generic-lift.tex`, forward mode). R0 and the scope
adjudication are settled (*Decisions made*): the product route substitutes
for JJ 2010's alg-indep layer; all four layers **M → P → BB → BH**,
JJ-faithful parameter spaces, abundance-polynomial statement strength.

**First Layer-M slice landed** (2026-07-17): `thm:molecule-generic-rank` /
`cor:molecule-generic-rigid` are green, as thin compositions
(`SimpleGraph.molecule_generic_rank` / `SimpleGraph.molecule_generic_rigid`,
`Molecular/Molecule/Application.lean`) over the landed
`finrank_range_rigidityMap_eq_genericRank` and `molecule_rank_formula` —
confirmed both build warning-free on the first attempt, no friction. The
carrier-faithfulness check on "`G̃ = 5·G`" passed: `G.shadowGraph.deficiency 3`
computes `def` with the `(bodyBarDim 3 - 1) = 5` crossing-edge multiplier baked
into `partitionDef` (`Molecular/Deficiency.lean`), and `shadowGraph` shares
`G`'s adjacency structure one-for-one, so the two together match the
blueprint's `5·G` phrasing exactly — no TeX fix needed.

**The abundance node landed** (2026-07-17): `lem:generic-placement-abundance` is green
(`SimpleGraph.exists_isGenericPlacement_abundance`, `GenericRigidityMatroid.lean`). The
Gram-determinant route flagged at chapter-open did not survive contact with the API — it has no
in-project caller (`Mathlib/LinearAlgebra/Matrix/Rank.lean`'s own docstring records the reroute);
the landed proof instead multiplies, over the finitely many edge subsets `I ⊆ E(K_V)`
row-independent at some witness placement, a per-`I` nonzero witnessing-minor polynomial from
`exists_polynomial_ne_zero_of_linearIndependent_at` (the maximal-minor engine, same substance —
one nonzero polynomial per witnessed subset, multiplied — different determinant). That engine
needs its coordinate basis literally indexed by `Fin (finrank K W)`; since the natural basis here
(`Module.finBasis ℝ (Framework V d)`'s dual) is indexed by `Fin n` for a *propositionally* (not
definitionally) equal `n`, a new reindexing companion
`exists_polynomial_ne_zero_of_linearIndependent_at_reindex` was added to `Rank.lean`, mirroring the
existing `exists_good_realization`/`exists_good_realization_reindex` pair. Blueprint proof sketch
updated to match (`Mathlib/LinearAlgebra/Matrix/Rank.lean`'s docstring note is now the pointer).

**Layer M closed** (2026-07-17): `cor:molecule-generic-square-packing` is green
(`SimpleGraph.molecule_generic_square_packing`, `Molecular/Molecule/Application.lean`) — see
*Decisions made* for the hypothesis-shape choice and the `hmin`-derivation reroute (a shortcut off
the hand-off's suggested route, recorded there). Layer M is now fully green; the phase's seam
decision (sub-letter at the body-bar-vs-molecular boundary, or continue into Layer P in this same
phase number) is live — see *Hand-off*.

## What the phase targets (statement surface)

Upgrade the project's **existence-form** realization statements to the
**generic** ("almost all realizations") form, via the Jackson–Jordán 2010
coordinate route (their Thms 5.2, 6.4, 7.2, 8.1/8.2), which avoids
Whiteley 1988's variety-irreducibility machinery (the lift `body-bar.tex`
and `body-hinge.tex` defer with "not pursued here", standing since
Phases 15/16). The affected surface:

- **Tay's body-bar theorem** (Phase 15, `thm:tay-witness`,
  `Graph.BodyBarFramework.tay_witness`) — existence-of-realization form.
- **Body-hinge Tay–Whiteley** (Phase 16, `thm:body-hinge-tay`,
  `Graph.BodyHingeFramework.body_hinge_tay`) — same form, via the
  `(δ−1)·G` reduction. **R0 caution:** the Phase-16 object is the
  bar-bundle reduction, not a geometric hinge model — the JJ-faithful
  generic body-hinge statement runs on the molecular
  `BodyHingeFramework K k α β` via `ofHinge` (Layer BH), not on it.
- **The molecular statements** — JJ 2010 p. 586 remark: with
  Conjecture 1.1 now a theorem, every generic bar-joint realization of
  `G²` in ℝ³ is infinitesimally rigid whenever `5G` packs six
  edge-disjoint spanning trees (the Cor 5.7 sharpening).

Carriers (adjudicated): the BB/BH-combinatorial surface stays at ℝ (no
ℝ→K sweep of `BodyBar/*.lean`); the Molecular-side layers stay
`[Field K] [Infinite K]` as landed (Phase 33). Likely seam if the phase
runs long (codes-until-open, not pre-divided): the body-bar/body-hinge
layer vs. the molecular layer (`notes/Prospect.md` *Hand-off*).

## Work-item checklist

- [x] **R0 — the opening recon**: verdict ACCEPTED 2026-07-17
  (*Decisions made*; full reasoning in the dispatch return / git history).
- [x] **Adjudicate scope + route on R0's verdict**: done 2026-07-17
  (*Decisions made*, verbatim).
- [x] **Chapter-open** (2026-07-17) — `blueprint/src/chapter/generic-lift.tex`,
  forward mode, Layer M's nodes as the leaf-most red ones; grain decision
  under *Decisions made*.
- [x] **Layer M** — molecular / bar-joint `G²` (d = 3, ℝ). Fully green: `thm:molecule-generic-rank`,
  `cor:molecule-generic-rigid`, `lem:generic-placement-abundance`
  (`SimpleGraph.molecule_generic_rank`/`molecule_generic_rigid`,
  `Molecular/Molecule/Application.lean`; `SimpleGraph.exists_isGenericPlacement_abundance`,
  `GenericRigidityMatroid.lean`), and now `cor:molecule-generic-square-packing`
  (`SimpleGraph.molecule_generic_square_packing`, same file) — hypothesis-shape choice and the
  `hmin`-derivation reroute are under *Decisions made*.
- [ ] **Layer P** — panel-and-hinge over normals, `[Field K] [Infinite K]`
  (JJ Thm 7.2 analogue). Polynomial row coordinatization landed
  (`annihRowPoly` via `PanelHingeFramework.exists_good_realization_ofParam`);
  witness from the Theorem-5.6 chain
  (`rankHypothesis_genuine_of_theorem_55_gen`); upper bound
  `BodyHingeFramework.finrank_span_rigidityRows_add_deficiency_le`. New:
  `IsGeneric`-over-normals + abundance product + the statement "every
  generic panel realization rigid on `V(G)` iff `def(G̃) = 0`". JJ's
  Thm 6.5 + Lemma 7.1 detour not needed (KT chain supplies the witness).
- [ ] **Layer BB** — body-bar at ℝ, **endpoint-parameterized** (adjudicated
  JJ-faithful form: "almost all bar endpoint choices"). New modest layer:
  the two-extensor map `T(p,p')` (2×2 minors; rows degree-2 in endpoints),
  witness = JJ Lemma 5.1's coordinate points (the landed standard-basis
  witness vectors are `±T` of coordinate-point pairs); converse
  `isSparse_of_isIndependent` landed. Statement: at generic endpoints,
  edge set independent iff `(D,D)`-sparse, rigid iff tight.
- [ ] **Layer BH** — geometric body-hinge over `ofHinge` hinge points,
  `[Field K] [Infinite K]`. Needs (new): an `MvPolynomial` coordinatization
  of the `ofHinge` annihilator rows in the hinge points
  (`affineSubspaceExtensor` coordinates are minors in the points), and the
  genuine-hinge conjunct as one more product factor (affine independence).
  Landed: the deficiency/packing bridge and the B2 upper bound. Statement:
  every generic hinge-point realization rigid iff `def(G̃) = 0` iff
  `(D−1)·G` packs `D` spanning trees.

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

- None blocking. One **build-time open** (settle at each layer's
  chapter-extension/slice, not now): the exact polynomial-family shapes
  for `T(p,p')` (Layer BB) and the `affineSubspaceExtensor` rows
  (Layer BH). (The dep-graph-primacy open is resolved — *Decisions made*.)
- Rigidity-form vs rank-formula strength for the *unopened* layers
  (P/BB/BH): per layer at its chapter-extension commit (adjudication
  item 5; Layer M's call is under *Decisions made*).

## Hand-off / next phase

Layer M is fully green (all four nodes). Next concrete commit: the phase's
seam decision is live — either sub-letter at the body-bar-vs-molecular
boundary, or continue straight into **Layer P** (panel-and-hinge over
normals, `[Field K] [Infinite K]`, JJ Thm 7.2 analogue) in this same phase
number, per the existing seam entry (*What the phase targets*). Layer P's
checklist (new decls needed: `IsGeneric`-over-normals, the abundance-product
instance, the iff-statement) is the next concrete work once that call is
made.

## Decisions made during this phase

- **Blueprint chapter-opening deferred until the R0 verdict** (2026-07-17,
  at open; the Phase-32 chapter-open trap + `CLAUDE.md`'s transcribed-proof
  caveat). Discharged: R0 landed same day; the chapter opened 2026-07-17.
- **Chapter-open grain (2026-07-17): Layer M only.** The chapter
  (`generic-lift.tex`) carries the shared preamble (all four layers named
  mathematically), the abundance root node, and Layer M's nodes; the
  P/BB/BH sections land as chapter-extension commits with their own
  layers. Rationale: their exact statement shapes are the recorded
  build-time opens — minting them now would be unrecon'd transcription
  (the Phase-32 lesson). The landed bridge lemma is restated green in
  `bar-joint-3d.tex` per the chapter-of-the-owning-file rule.
- **Layer M strength (adjudication item 5, 2026-07-17): both forms.** The
  realized rank-formula form (`thm:molecule-generic-rank`) *and* the
  rigidity form (`cor:molecule-generic-rigid`) + the JJ p. 586 packing
  corollary (`cor:molecule-generic-square-packing`). Rationale: at this
  layer the rank form is a one-step composition of landed decls, so the
  stronger statement costs nothing.
- **Dep-graph primacy (2026-07-17, resolves a build-time open): the
  transfer form is primary.** `def:generic-placement` (and its per-layer
  instantiations to come) stays the *definition*; the abundance
  polynomial is a *lemma* node (`lem:generic-placement-abundance`).
- **Unrecon'd-transcription flags (the Phase-32 chapter-open guard).**
  Authored beyond R0's pins, verified at slice time: (i)
  `cor:molecule-generic-square-packing`'s hypothesis shape — **discharged
  2026-07-17**, both the `|V| = 1` case and the packing shape, see the
  dedicated entry below; (ii) `lem:generic-placement-abundance`'s product
  route — **discharged 2026-07-17**, but not as sketched: the
  Gram-determinant form had no in-project caller
  (`Mathlib/LinearAlgebra/Matrix/Rank.lean`'s own docstring records the
  reroute onto the maximal-minor twin), so the landed proof multiplies
  per-subset witnessing-minor polynomials from
  `exists_polynomial_ne_zero_of_linearIndependent_at` instead (new
  reindexing companion `..._reindex` added alongside, mirroring
  `exists_good_realization`/`_reindex`); blueprint proof sketch updated
  to match.
- **`cor:molecule-generic-square-packing` hypothesis shape (2026-07-17):
  a literal spanning-tree family, not the covering-shaped
  `Graph.IsSpanningTreePacking`/`IsForestPacking` (those require the trees'
  edges to cover all of `E(G̃)`, stronger than JJ's "contains six").
  Landed as `Ts : Fin 6 → Graph V _`, `hspan : ∀ i, Ts i ≤s
  G.shadowGraph.mulTilde 3` (spanning subgraph — pins `V(Ts i) = univ`),
  `hTtree : ∀ i, (Ts i).IsTree`, pairwise-disjoint `E(Ts i)` — the direct,
  literal Lean reading of "six edge-disjoint spanning trees of `5·G`".
  **`hmin`-derivation reroute**: rather than the hand-off's suggested
  direct count (six trees each touch every vertex ⟹ `deg_{5G} ≥ 6` ⟹
  `deg_G ≥ 2`, a pigeonhole through the `mulTilde` parallel-copy index),
  the landed proof derives `hdef` (`def(G̃) = 0`) *first* — from the
  independent-set-of-size-`6(|V|-1)` argument the chapter proof already
  sketches (`IsTree.ncard_vertexSet` for the per-tree edge count,
  `Matroid.union_indep_iff`/`cycleMatroid_indep` for independence,
  `Indep.isBase_of_ncard` + `isBase_ncard_add_deficiency_eq` for the
  base/deficiency-zero step) — then derives `hmin` *from* `hdef` via the
  already-landed KT Lemma 4.6 machinery
  (`Graph.two_le_degree_of_isKDof_zero`, `def:cut-edges-2ec`: a `0`-dof
  graph is `2`-edge-connected, hence min degree `≥ 2`), bridged to `G`'s
  own degree via `Graph.degree_eq_ncard_adj` + `shadowGraph_isLink_iff` +
  `ncard_neighborSet_eq_degree`. This reuses existing infrastructure
  instead of a fresh pigeonhole argument through `mulTilde`'s copy index,
  and is mathematically equivalent (both routes conclude `hmin ∧ hdef`).
  Blueprint proof reordered to match (`def:cut-edges-2ec` added to the
  proof's `\uses`).
- **R0 verdict (2026-07-17): ACCEPTED — the product route substitutes;
  alg-indep does not return.** JJ 2010's "generic" is a *max-rank*
  definition at all four layers (body-bar p. 582, body-hinge p. 583,
  panel p. 584, molecular p. 585); alg-indep over ℚ appears only in
  "thus 'almost all'" abundance remarks, never in a theorem's proof
  (Thm 5.2 = upper bound + Lemma-5.1 witness; Thm 7.2 closes by "since G
  has one rigid realization, all generic ones are"). The project precedent
  is `SimpleGraph.IsGenericPlacement` (Phase 24, alg-indep-free); the
  formal "almost all" is the abundance polynomial via
  `MvPolynomial.exists_eval_ne_zero`. Nothing in Phase 30's deletion
  inventory is needed. Full reasoning: the R0 dispatch return (git
  history) + the JJ PDF.
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
