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

**Layer M closed** (2026-07-17, all four nodes green): `thm:molecule-generic-rank` /
`cor:molecule-generic-rigid` (thin compositions, `Molecular/Molecule/Application.lean`),
`lem:generic-placement-abundance` (`SimpleGraph.exists_isGenericPlacement_abundance`,
`GenericRigidityMatroid.lean` — the Gram-determinant sketch rerouted onto the maximal-minor engine's
new reindexing companion `exists_polynomial_ne_zero_of_linearIndependent_at_reindex`, `Rank.lean`),
and `cor:molecule-generic-square-packing` (`SimpleGraph.molecule_generic_square_packing`, same
file). Full detail (the hypothesis-shape choice, the `hmin`-derivation reroute) is in *Decisions
made*. The seam call is settled (user adjudication, *Decisions made*): Layer P continues in this
phase number.

**Layer P closed** (2026-07-17, all seven nodes green), `Molecular/GenericLift/PanelGeneric.lean`:
`def:generic-normals` (`normalRow`/`IsGenericNormals`, graph-free with the `rfl` bridge
`normalRow_eq_panelRow`), `lem:generic-normals-abundance`/`lem:exists-generic-normals`
(`exists_isGenericNormals_abundance`/`exists_isGenericNormals`, the same maximal-minor product
route as Layer M), `lem:generic-normals-nondegenerate`
(`supportExtensor_ofNormals_ne_zero_of_isGenericNormals`, simpler route than sketched — *Decisions
made*), `lem:panel-witness-transplant` (`exists_independent_normalRow_of_le_finrank`, hit and
resolved a TACTICS-QUIRKS §38 heavy-carrier recurrence — *Decisions made*), and
`thm:panel-generic-rank`/`cor:panel-generic-rigid` (assembled from the already-landed bricks exactly
per the chapter-extension's proof sketch).

**Layer-BB chapter extension landed** (2026-07-17): `generic-lift.tex` now carries
`sec:generic-lift-bodybar` with nine red nodes — `def:two-extensor`, `def:generic-endpoints`,
`lem:generic-endpoints-abundance`, `lem:exists-generic-endpoints`,
`lem:coordinate-extensor-basis`, `lem:extensor-map-rows`, `lem:endpoint-witness`,
`thm:bodybar-generic-independence`, `cor:bodybar-generic-tay` — decomposed against the landed
`BodyBar/*.lean` carrier (target signatures in the Layer-BB checklist item). The `T(p,p')`
polynomial-family shape is settled and the R0-era "±T of coordinate-point pairs" claim is
**refuted** (JJ's Lemma-5.1 entry table, verified against the PDF) — route rerouted through the
Whiteley-remark change of extensor coordinates; strength call under *Decisions made*.

**First Layer-BB Lean slice landed** (2026-07-17): the definition-plus-abundance leaf group is
green — `def:two-extensor` (`Graph.BodyBarFramework.pairIdxEquiv`/`twoExtensor`/`twoExtensorPoly`,
plus the bridge `twoExtensorPoly_eval`), `def:generic-endpoints` (`ofEndpoints`/
`IsGenericEndpoints`), `lem:generic-endpoints-abundance`
(`exists_isGenericEndpoints_abundance`), `lem:exists-generic-endpoints`
(`exists_isGenericEndpoints`) — new file `Molecular`-sibling
`CombinatorialRigidity/BodyBar/GenericLift.lean`, added to the root import list. `pairIdxEquiv` is
built via `Fintype.equivFinOfCardEq` off a from-scratch cardinality proof (the increasing-pairs
subtype ≃ `Σ j, {i // i < j}` ≃ a Gauss sum via `Finset.sum_range_id`) rather than transcribing JJ's
concrete enumeration — the docstring's "any equiv works" licenses this. Two friction points, both
resolved without a route change: (i) `Fin.cons 1 p` applied at a compound index
(`((pairIdxEquiv n).symm m).1.1`) fails motive inference (a higher-order-unification gap, not a
parenthesization bug) — fixed by pinning `Fin.cons`'s non-dependent type through a top-level
`homLift`/`homLiftPoly` helper rather than inlining; (ii) marking `ofEndpoints` `@[reducible]` (needed
so `Set ↥E(G)`'s elements coerce into `(ofEndpoints G q').rigidityRow`'s domain per the checklist's
pinned `IsGenericEndpoints` shape) makes the companion `ofEndpoints_graph` simp lemma's LHS reduce to
the bare variable `G` — `lake lint`'s `simpVarHead` catch, fixed by dropping its `@[simp]` tag (the
fact stays available by name). No other friction. Next: assess the witness slice
(*Hand-off*).

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
  JJ-faithful form: "almost all bar endpoint choices"). Chapter extension
  landed 2026-07-17 (`sec:generic-lift-bodybar`, nine red nodes; the
  dep-graph is the to-do list). Witness = JJ Lemma 5.1's coordinate
  segments via the Whiteley-remark change of extensor coordinates (the
  R0-era `±T` claim is refuted — *Decisions made*); converse
  `isSparse_of_isIndependent` landed with exactly the corollary's `⟹`
  shape (`F.IsIndependent D → F.graph.IsSparse d d`, verified). The
  per-subset `⟹` arm and the witness's subfamily independence need
  `E'`-restricted generalizations of `isSparse_of_isIndependent` /
  `stdFramework_rigidityRow_linearIndependent` (both `TayTheorem.lean`;
  mechanical — their proofs already run per-subset internally).
  **Definition-plus-abundance leaf group landed 2026-07-17**:
  `def:two-extensor`, `def:generic-endpoints`, `lem:generic-endpoints-abundance`,
  `lem:exists-generic-endpoints` (`Graph.BodyBarFramework.pairIdxEquiv`/
  `twoExtensor`/`twoExtensorPoly`/`ofEndpoints`/`IsGenericEndpoints`/
  `exists_isGenericEndpoints_abundance`/`exists_isGenericEndpoints`,
  `BodyBar/GenericLift.lean`) — see *Decisions made* for the two friction
  points. Remaining: the witness slice (`lem:coordinate-extensor-basis`,
  `lem:extensor-map-rows`, `lem:endpoint-witness`,
  `thm:bodybar-generic-independence`, `cor:bodybar-generic-tay`) and the two
  `TayTheorem.lean` subfamily generalizations. Target signatures (landed
  ones now implemented as described above; remaining ones unchanged):

  ```
  -- (namespace Graph.BodyBarFramework; new file CombinatorialRigidity/BodyBar/GenericLift.lean,
  --  except the two TayTheorem.lean generalizations above; ℝ throughout, adjudication item 3;
  --  [Finite α] [Finite β] on everything from abundance down)
  -- def:two-extensor (the pair enumeration is any fixed equiv — the coordinate formula is the
  --   contract; twoExtensorPoly is the MvPolynomial coordinatization the abundance engine reads)
  noncomputable def pairIdxEquiv (n : ℕ) :
      {ij : Fin (n + 1) × Fin (n + 1) // ij.1 < ij.2} ≃ Fin (bodyBarDim n)
  noncomputable def twoExtensor (p p' : Fin n → ℝ) : EuclideanSpace ℝ (Fin (bodyBarDim n))
    -- coordinate at pairIdxEquiv ⟨(i, j), _⟩ = h p i * h p' j − h p j * h p' i, h p = Fin.cons 1 p
  noncomputable def twoExtensorPoly (e : β) (m : Fin (bodyBarDim n)) :
      MvPolynomial (β × Bool × Fin n) ℝ
    -- eval q (twoExtensorPoly e m) = twoExtensor (fun i => q (e, false, i)) (fun i => q (e, true, i)) m
  -- def:generic-endpoints
  noncomputable def ofEndpoints (G : Graph α β) (q : β × Bool × Fin n → ℝ) :
      BodyBarFramework n α β :=
    ⟨G, fun e => twoExtensor (fun i => q (e, false, i)) (fun i => q (e, true, i))⟩
  def IsGenericEndpoints (G : Graph α β) (D : Graph.orientation G)
      (q : β × Bool × Fin n → ℝ) : Prop :=
    ∀ s : Set ↥E(G), (∃ q', LinearIndependent ℝ fun e : s => (ofEndpoints G q').rigidityRow D e) →
      LinearIndependent ℝ fun e : s => (ofEndpoints G q).rigidityRow D e
  -- lem:generic-endpoints-abundance (engine:
  --   exists_polynomial_ne_zero_of_linearIndependent_at_reindex over the dual basis of
  --   Pi.basis (fun _ : α => EuclideanSpace.basisFun ..), c = incidence sign • twoExtensorPoly —
  --   the Layer-P shape, rows quadratic instead of linear)
  theorem exists_isGenericEndpoints_abundance (G : Graph α β) (D : Graph.orientation G) :
      ∃ P : MvPolynomial (β × Bool × Fin n) ℝ, P ≠ 0 ∧
        ∀ q, MvPolynomial.eval q P ≠ 0 → IsGenericEndpoints G D q
  -- lem:exists-generic-endpoints (MvPolynomial.exists_eval_ne_zero, ℝ infinite)
  theorem exists_isGenericEndpoints (G : Graph α β) (D : Graph.orientation G) :
      ∃ q : β × Bool × Fin n → ℝ, IsGenericEndpoints G D q
  -- lem:coordinate-extensor-basis (coordPoint n = Fin.cases 0 (Function.update 0 · 1);
  --   triangular elimination on the JJ Lemma-5.1 entry table: moment coordinates private,
  --   then distinct direction coordinates)
  theorem linearIndependent_twoExtensor_coordPoint (n : ℕ) :
      LinearIndependent ℝ fun ij : {ij : Fin (n + 1) × Fin (n + 1) // ij.1 < ij.2} =>
        twoExtensor (coordPoint n ij.1.1) (coordPoint n ij.1.2)
  -- lem:extensor-map-rows (mapPlacement F M := ⟨F.graph, fun e => M (F.placement e)⟩;
  --   ⟪M b, w⟫ = ⟪b, M† w⟫ makes the new row the old row precomposed with the bodywise-M†
  --   motion equiv; LinearIndependent.map' along its dualMap)
  theorem linearIndependent_rigidityRow_mapPlacement {F : BodyBarFramework n α β}
      (D : Graph.orientation F.graph)
      (M : EuclideanSpace ℝ (Fin (bodyBarDim n)) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (bodyBarDim n)))
      {s : Set ↥E(F.graph)} (h : LinearIndependent ℝ fun e : s => F.rigidityRow D e) :
      LinearIndependent ℝ fun e : s => (F.mapPlacement M).rigidityRow D e
  -- lem:endpoint-witness (forest packing of E' via exists_forestPacking_cover_of_isSparse_restrict
  --   + Fintype.exists_disjointed_le, reindexed along pairIdxEquiv.symm; std rows on the subfamily
  --   via the TayTheorem.lean generalization; transported by
  --   linearIndependent_rigidityRow_mapPlacement at M = the coordinate-segment basis)
  theorem exists_endpoints_linearIndependent_rigidityRow {G : Graph α β}
      (D : Graph.orientation G) {E' : Set β} (hE' : E' ⊆ E(G))
      (hsparse : (G ↾ E').IsSparse (bodyBarDim n) (bodyBarDim n)) :
      ∃ q : β × Bool × Fin n → ℝ,
        LinearIndependent ℝ fun e : (Subtype.val ⁻¹' E' : Set ↥E(G)) =>
          (ofEndpoints G q).rigidityRow D e
  -- thm:bodybar-generic-independence (⟸ = witness + the transfer at s = val ⁻¹' E';
  --   ⟹ = the E'-restricted isSparse_of_isIndependent generalization, genericity-free)
  theorem linearIndependent_rigidityRow_ofEndpoints_iff {G : Graph α β}
      {D : Graph.orientation G} {q : β × Bool × Fin n → ℝ} (hq : IsGenericEndpoints G D q)
      {E' : Set β} (hE' : E' ⊆ E(G)) :
      (LinearIndependent ℝ fun e : (Subtype.val ⁻¹' E' : Set ↥E(G)) =>
          (ofEndpoints G q).rigidityRow D e)
        ↔ (G ↾ E').IsSparse (bodyBarDim n) (bodyBarDim n)
  -- cor:bodybar-generic-tay (two decls, one node; E' = E(G) + restrict_self, then the
  --   tay_witness rank/count arithmetic verbatim; ⟹ arms are the landed
  --   isSparse_of_isIndependent + the rank substitution)
  theorem isIndependent_ofEndpoints_iff {G : Graph α β} {D : Graph.orientation G}
      {q : β × Bool × Fin n → ℝ} (hq : IsGenericEndpoints G D q) :
      (ofEndpoints G q).IsIndependent D ↔ G.IsSparse (bodyBarDim n) (bodyBarDim n)
  theorem isIndependent_and_isInfinitesimallyRigid_ofEndpoints_iff {G : Graph α β}
      {D : Graph.orientation G} {q : β × Bool × Fin n → ℝ} (hq : IsGenericEndpoints G D q) :
      ((ofEndpoints G q).IsIndependent D ∧ (ofEndpoints G q).IsInfinitesimallyRigid D)
        ↔ G.IsTight (bodyBarDim n) (bodyBarDim n)
  ```
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

- None blocking. One **build-time open** (settle at the Layer-BH
  chapter-extension/slice, not now): the exact polynomial-family shape
  for the `affineSubspaceExtensor` rows (Layer BH). (The `T(p,p')` shape
  is settled — *Decisions made*; the dep-graph-primacy open is resolved.)
- Rigidity-form vs rank-formula strength for the *unopened* layer (BH):
  at its chapter-extension commit (adjudication item 5; the M/P/BB calls
  are under *Decisions made*).

## Hand-off / next phase

Layers M and P are fully green; the Layer-BB chapter extension is landed
(`sec:generic-lift-bodybar`, nine red nodes), and its definition-plus-abundance
leaf group is now green too (`def:two-extensor`, `def:generic-endpoints`,
`lem:generic-endpoints-abundance`, `lem:exists-generic-endpoints`;
`BodyBar/GenericLift.lean`). Next concrete commit: the **witness slice** —
`lem:coordinate-extensor-basis` (the coordinate-segment two-extensors form a
basis of `ℝ^(bodyBarDim n)`) and `lem:extensor-map-rows` (a fixed invertible
extensor-space map preserves row independence via adjoint precomposition on
motions), then `lem:endpoint-witness` (the forest-packing witness, needing the
two `TayTheorem.lean` `E'`-restricted generalizations of
`isSparse_of_isIndependent` / `stdFramework_rigidityRow_linearIndependent`
flagged in the Layer-BB checklist item), then the closing
`thm:bodybar-generic-independence` / `cor:bodybar-generic-tay` pair. Assess
whether the witness slice fits one commit or needs splitting once
`lem:coordinate-extensor-basis`'s JJ-Lemma-5.1 entry-table elimination is
attempted in Lean.

## Decisions made during this phase

- **Layer BB strength (adjudication item 5, 2026-07-17): the per-subset
  independence characterization + the Tay pair.** The theorem
  (`thm:bodybar-generic-independence`) is per-subset — rows on `E'`
  independent iff `G ↾ E'` is `(D,D)`-sparse, JJ's own generic-realization
  strength (every edge-induced submatrix at max rank); the corollary
  (`cor:bodybar-generic-tay`) is the generic `tay_witness` pair. The
  adjudicated "rigid iff tight" is implemented as **isostatic** iff tight:
  literal rigid-iff-tight is false (two bodies joined by `D + 1` parallel
  bars are rigid at generic endpoints but not tight), and the `tay_witness`
  pairing is the reading. No deficiency rank formula at this layer — JJ
  Thm 5.2's `def_D(G)` has no carrier for plain multigraphs (the landed
  deficiency is the molecular `(D−1)`-multiplier shadow form), and the
  matroid content is already the per-subset iff against
  `thm:unionPow-cycle-indep-iff-sparse` (recorded in closing prose only).
- **R0-era witness claim refuted; Whiteley-remark reroute (2026-07-17,
  the chapter-extension recon).** The landed standard-basis witness
  vectors are **not** `±T` of coordinate-point pairs: per JJ's Lemma-5.1
  entry table (verified against the PDF, p. 581), only the `[c₀, c_k]`
  segments give `±` basis vectors; `[c_h, c_k]` with `h ≥ 1` has three
  `±1` entries, and no segment yields a pure moment ("line at infinity")
  basis vector at all — zero direction forces equal endpoints, hence a
  zero extensor. Landed route instead: the `D` coordinate-segment
  extensors form a basis (`lem:coordinate-extensor-basis`, triangular on
  private moment coordinates), and a fixed invertible extensor-space map
  preserves row independence via adjoint precomposition on motions
  (`lem:extensor-map-rows`) — the change-of-coordinates route JJ's Remark
  attributes to Whiteley, reusing the landed `stdFramework` block chain
  instead of re-proving JJ's staged elimination.
- **`T(p,p')` polynomial-family shape settled (2026-07-17, closes the
  Layer-BB build-time open).** `T` = the `2×2` minors of the homogeneous
  pair `(h(p), h(p'))`, `h(p) = (1, p)`, indexed by pairs `0 ≤ i < j ≤ n`
  through a fixed enumeration equiv onto `Fin (bodyBarDim n)`
  (`pairIdxEquiv`; any fixed equiv — the coordinate formula is the
  contract). Direction coordinates `(0, j)` are degree 1, moment
  coordinates degree 2. Parameter space flattened as
  `q : β × Bool × Fin n → ℝ` (the Layer-P raw-coordinate shape:
  MvPolynomial-ready, no `equivFun` plumbing), the `false`/`true`
  components the two endpoints; `IsGenericEndpoints` pins an orientation
  `D` (row signs only) and quantifies over `Set ↥E(G)`.
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
