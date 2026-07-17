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
the hand-off's suggested route, recorded there). The seam call is settled (user adjudication,
*Decisions made*): Layer P continues in this phase number.

**Layer-P chapter extension landed** (2026-07-17): `generic-lift.tex` now carries
`sec:generic-lift-panel` with seven red nodes — `def:generic-normals`,
`lem:generic-normals-abundance`, `lem:exists-generic-normals`,
`lem:generic-normals-nondegenerate`, `lem:panel-witness-transplant`,
`thm:panel-generic-rank`, `cor:panel-generic-rigid` — decomposed against the landed carrier
(target signatures below). Strength call and the witness-variant finding are under *Decisions
made*; same commit extends `thm:theorem-55-6-genuine`'s `\lean{}` list with the landed
link-recording strengthening the route consumes (additive-successor gate).

**First Layer-P Lean slice landed** (2026-07-17): the definition-plus-abundance leaf group is green
— `def:generic-normals`, `lem:generic-normals-abundance`, `lem:exists-generic-normals`
(`CombinatorialRigidity.Molecular.PanelHingeFramework.{normalRow, IsGenericNormals,
exists_isGenericNormals_abundance, exists_isGenericNormals}`, new file
`Molecular/GenericLift/PanelGeneric.lean`, added to the root import list). `normalRow` is graph-free
(reads only `ends`/`q`) with the `rfl` bridge `normalRow_eq_panelRow` to
`(ofNormals G ends q).toBodyHinge.panelRow ends`; the abundance proof reuses the genericity device's
`annihRowPoly` coordinate family + eval identity verbatim (the graph-free `normalRow` in place of
`panelRow`) and multiplies the per-subfamily minors of
`exists_polynomial_ne_zero_of_linearIndependent_at_reindex`, exactly the bar-joint
`exists_isGenericPlacement_abundance` product shape. No friction; built and linted clean first
attempt after one metavariable-pin fix (the `∃ q` needed its type annotated to fix `k`/`K`).

**`lem:generic-normals-nondegenerate` landed** (2026-07-17):
`supportExtensor_ofNormals_ne_zero_of_isGenericNormals` (same file). Simpler route than the
chapter-extension sketch — see *Decisions made* for the dropped `[Infinite K]` hypothesis and the
per-edge two-point moment-curve seed (rather than `IsGeneralPosition`/`ofParam` over all of `α`).

**`lem:panel-witness-transplant` landed** (2026-07-17):
`exists_independent_normalRow_of_le_finrank` (same file), as pinned — extraction at OUR `ends` +
per-edge ± transport. Hit and resolved a TACTICS-QUIRKS §38 heavy-carrier recurrence; see *Decisions
made*.

**Layer P closed** (2026-07-17): `thm:panel-generic-rank` /
`finrank_span_rigidityRows_ofNormals_of_isGenericNormals` and `cor:panel-generic-rigid` /
`isInfinitesimallyRigidOn_ofNormals_isGenericNormals_iff` are green (same file), assembled from the
already-landed bricks exactly per the chapter-extension's proof sketch — see the Layer-P checklist
item for the assembly shape. Next: Layer BB (body-bar, endpoint-parameterized).

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
- [x] **Layer P** — panel-and-hinge over normals, `[Field K] [Infinite K]`
  (JJ Thm 7.2 analogue). Fully green (2026-07-17): `def:generic-normals`,
  `lem:generic-normals-abundance`, `lem:exists-generic-normals`,
  `lem:generic-normals-nondegenerate`, `lem:panel-witness-transplant`,
  `thm:panel-generic-rank`, `cor:panel-generic-rigid`
  (`finrank_span_rigidityRows_ofNormals_of_isGenericNormals` /
  `isInfinitesimallyRigidOn_ofNormals_isGenericNormals_iff`,
  `Molecular/GenericLift/PanelGeneric.lean`). The rank-formula assembly pinches the
  witness transplant's lower bound (transported to `q` by genericity, then to a
  rigidity-row lower bound via `finrank_span_eq_card` + `Submodule.finrank_mono`) against
  the B2 upper bound — the same `le_antisymm` shape `Theorem56.lean`'s
  `exists_rankHypothesis_isGeneralPosition4_of_two_le` uses for its sibling
  general-position realization. The rigidity corollary is the rank–nullity iff via
  `isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows`. No route surprises:
  the chapter-extension's proof sketch (`\uses` lists + prose) matched exactly, needing
  only two mechanical fixes — an explicit `(K := K)` pin on the Theorem-55 witness call and
  an explicit `q`'s-type annotation on the corollary's `∀ q` (the same metavariable-pin
  shape as the earlier abundance lemma's `∃ q`).
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
  (BB/BH): per layer at its chapter-extension commit (adjudication
  item 5; Layer M's and Layer P's calls are under *Decisions made*).

## Hand-off / next phase

Layers M and P are both fully green. Next concrete commit: open **Layer BB**
(body-bar at ℝ, endpoint-parameterized — JJ-faithful "almost all bar endpoint
choices" form, per the user adjudication). Per *What the phase targets* / the
Layer-BB checklist item: a new modest layer built around the two-extensor map
`T(p,p')` (2×2 minors; rows degree-2 in endpoints), witnessed by JJ Lemma 5.1's
coordinate points (the landed standard-basis witness vectors are `±T` of
coordinate-point pairs); the converse `isSparse_of_isIndependent` is already
landed. Start with a chapter-extension commit (`sec:generic-lift-bodybar` or
similar) decomposing the statement — "at generic endpoints, edge set
independent iff `(D,D)`-sparse, rigid iff tight" — against the landed
`BodyBar/*.lean` carrier, per the file header's open build-time item (the
exact polynomial-family shape for `T(p,p')`).

## Decisions made during this phase

- **`lem:panel-witness-transplant` landed as pinned** (2026-07-17,
  `exists_independent_normalRow_of_le_finrank`): the extraction is
  `exists_independent_panelRow_subfamily_of_le_finrank` (W6e) applied to
  `Q.toBodyHinge` at OUR `ends` (its unconditional `hends`/`hC` are stronger
  than that lemma's linking-edge-only hypotheses); the per-edge ± sign
  between `Q.toBodyHinge.panelRow ends` and the graph-free `normalRow ends q`
  transports via `IsLink.eq_and_eq_or_eq_and_eq` (both `ends e` and `Q.ends e`
  witness the same `G`-link) + `panelSupportExtensor_swap`, packaged as a
  per-index `Kˣ`-scaling and closed by `LinearIndependent.units_smul_iff`.
  **Hit TACTICS-QUIRKS §38's heavy-carrier `whnf` blowup** at the final
  `units_smul_iff` step (`Q.toBodyHinge`/`normalRow` are `def`s, not fvars,
  over the generic `Module.Dual K (α → ScrewSpace K k)` carrier) — confirmed
  via real `lake build` timing (not an LSP artifact) up to `maxHeartbeats
  1600000` still timing out at ~170s; fixed by the documented `set`/
  `clear_value` medicine (opaque the target family + sign weights right
  before the `units_smul_iff` call), after which the whole proof builds
  under the *default* 200000 heartbeats — no override needed. New
  TACTICS-QUIRKS §90 for a separate `rw [neg_one_smul]` pattern-search gotcha
  hit along the way (explicit-ring-argument lemma; fix is `exact lemma R x`
  or the `module` tactic, not a bare `rw`).
- **Seam adjudication (user, 2026-07-17): Layer P continues in this phase
  number** — no sub-letter now; revisit at the body-bar boundary per the
  existing seam entry (*What the phase targets*).
- **Layer P strength (adjudication item 5, 2026-07-17): both forms.** The
  rank-formula form (`thm:panel-generic-rank`, JJ's
  `rank R(G,q) = D(|V|−1) − def(G̃)` at every generic assignment) *and*
  the rigidity iff-form (`cor:panel-generic-rigid`). Rationale: the
  witness/upper-bound sandwich the route proves anyway *is* the rank
  formula (the witness `RankHypothesis` is an equality, B2 the matching
  bound); the iff is then a thin rank–nullity corollary, so the stronger
  pair costs nothing — same situation as Layer M.
- **Layer P witness = the link-recording KT 5.6 form** (2026-07-17,
  chapter-extension recon). The base
  `rankHypothesis_genuine_of_theorem_55_gen` is **refuted** for the
  transplant leaf: its `reaimSub` off-edge fallback `(x₀, y₀)` puts a
  foreign-panel extensor on the re-added edges, so the per-edge
  extensor-sign comparison against the fixed selector fails there. The
  landed `..._recordsLinks_...` variant (Phase 25 F1) records an actual
  link on every edge, restoring the up-to-swap agreement
  (`IsLink.eq_and_eq_or_eq_and_eq` + `panelSupportExtensor_swap`). Its
  missing blueprint pin was repaired by extending
  `thm:theorem-55-6-genuine`'s `\lean{}` list (additive-successor gate);
  the JJ Thm 6.5 + Lemma 7.1 detour is confirmed unnecessary with this
  refinement.
- **`IsGenericNormals` is graph-free** (2026-07-17): the annihilator-row
  family reads only the endpoint selector and the normal assignment (the
  N7b-2 observation, verified against `panelRow`/`ofNormals` bodies), so
  the definition takes `(ends, q)` only — a `G`-parametric def would
  provably not depend on `G`. Consumers instantiate over `G` via `hends`.
  Existence comes from abundance + `MvPolynomial.exists_eval_ne_zero`
  (no interpolation-along-lines analogue needed, unlike Layer M).
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
  to match; (iii) `lem:generic-normals-nondegenerate`'s route — **discharged
  2026-07-17**, but not as sketched: the landed proof needs no
  `[Infinite K]` (dropped from the Lean statement — the blueprint's "let
  $K$ be infinite" was never used, only `hk1 : 1 ≤ k`) and does not go
  through `IsGeneralPosition`/`ofParam` over all of `α` at all; it builds a
  seed placing just the one edge's two (loopless-distinct) endpoints at
  moment-curve parameters `0`/`1` directly, picks a nonzero `screwBasis`
  coordinate of the resulting nonzero support extensor (using `D ≥ 2` from
  `two_le_screwDim hk1` to find a second index), and transports that
  one-row witness through `hingeRow`/`screwDiff_surjective`. Blueprint
  statement and proof rewritten to match (`\uses` now cites
  `lem:moment-curve-general-position` in place of the unused
  `lem:general-position-support-nonzero` / `lem:rows-polynomial-in-normals`).
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
