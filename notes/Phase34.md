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

**Layer M closed** (2026-07-17, all four nodes green — `thm:molecule-generic-rank`,
`cor:molecule-generic-rigid`, `lem:generic-placement-abundance`,
`cor:molecule-generic-square-packing`; `Molecular/Molecule/Application.lean` +
`GenericRigidityMatroid.lean`). Detail in *Decisions made*.

**Layer P closed** (2026-07-17, all seven nodes green, `Molecular/GenericLift/PanelGeneric.lean` —
`def:generic-normals`, `lem:generic-normals-abundance`/`lem:exists-generic-normals`,
`lem:generic-normals-nondegenerate`, `lem:panel-witness-transplant`,
`thm:panel-generic-rank`/`cor:panel-generic-rigid`). Detail in *Decisions made*.

**Layer BB closed** (2026-07-17, all nine nodes green over five slices;
`BodyBar/GenericLift.lean`, new file, plus three `TayTheorem.lean` additions —
the `E'`-restricted generalizations `stdFramework_rigidityRow_linearIndependent_restrict` /
`isSparse_of_isIndependent_restrict` and the bidirectional bridge
`isIndependent_iff_linearIndependent_rigidityRow`). Witness = JJ Lemma 5.1's
coordinate segments via the Whiteley-remark change of extensor coordinates;
the coordinate-basis proof landed as a **spanning** argument (blueprint rewritten
to match), the row-map proof via a genuine two-sided `adjointEquiv` lifted bodywise.
Slice friction all promoted (TACTICS-QUIRKS §9-ext, §91–§95; §93 = the recurring
`@[reducible]`-on-framework-constructors statement-elaboration pin, hit for
`ofEndpoints`/`mapPlacement`/`stdFramework`); one unpromoted micro-lesson: `Fin.cons`
at a compound index fails motive inference — pin through a top-level `homLift` helper.
Per-slice detail: git history (`b6454b02..010b378f`); routes/strength: *Decisions made*.

**Layer-BH chapter extension landed** (2026-07-17): `generic-lift.tex` carries
`sec:generic-lift-bodyhinge` (twelve red nodes) plus the packing bridge
`lem:deficiency-zero-iff-tree-packing` in `deficiency.tex` (Lean home `Deficiency.lean`).
Decomposed against the landed `ofHinge`/`affineSubspaceExtensor`/`panelRow`/B2 carrier (target
signatures in the Layer-BH checklist item); both build-time opens settled and one citation
mis-pointer corrected against the JJ PDF — *Decisions made*.

**First Layer-BH Lean slice landed** (2026-07-17, new file
`Molecular/GenericLift/HingeGeneric.lean`): the coordinatization-plus-definition-plus-abundance
leaf group — `lem:hinge-rows-polynomial-in-points` (`hingeExtensorPoly`/`hingeExtensorPoly_eval`),
`def:generic-hinge-points` (`hingePointRow`/`hingePointRow_eq_panelRow`/`IsGenericHingePoints`),
`lem:generic-hinge-points-abundance`, `lem:exists-generic-hinge-points` — all green. Two
mechanical elaboration opens beyond the target signatures, both promotable if they recur:
(i) a bare `Fin.snoc (fun b => X (e,i,b)) 1` needs an explicit `Fin (k+2) → MvPolynomial …`
ascription wherever applied to a column index (the dependent-motive elaborator otherwise
leaves unresolved metavariables); (ii) the abundance proof's per-edge annihilator polynomial
needed its own named `hingeAnnihRowPoly`/`hingeAnnihRowPoly_eval` (mirroring
`annihRowPoly`/`annihRowPoly_eval`) rather than an inline if-then-else difference — inlined, it
hit an `HSub`/`binop%` "ambiguous term" error and a stray `map_sub` rewriting the wrong side's
subtraction at the `hg` call site.

**`lem:generic-hinge-points-nondegenerate` landed** (2026-07-17, same file):
`supportExtensor_ofHinge_ne_zero_of_isGenericHingePoints`, a direct transplant of the reference-point
construction (`pRef`/`hpRefAffInd`/`refExt`/`tref`/`htref`) already built for the abundance proof's
genuine-hinge conjunct, replacing Layer P's moment-curve seed (per the blueprint proof: the reference
points are already free parameters, so no moment curve is needed). One mechanical fix beyond the
target signature: the `change`-tactic goal `annihRow ((ofHinge …).supportExtensor e) tref t1` needs
explicit inner parens around `(ofHinge …).supportExtensor e` — without them the postfix `.supportExtensor
e` field-projection swallows `tref`/`t1` too, feeding `annihRow` four arguments instead of three (a
"wrong number of args" symptom worth a TACTICS-QUIRKS entry if it recurs).

**`lem:screw-map-rows` landed** (2026-07-17, same file): `mapSupport` (the screw-transformed
framework) + `finrank_span_rigidityRows_mapSupport`, via the internal `bodyMap`/`dualBodyMap`
(precomposition with the body-wise application of `M⁻¹`) and the set-level row identity
`mapSupport_rigidityRows`. Two mechanical opens beyond the target signatures: (i) a coercion
mismatch (`rw [← Submodule.map_span f s]` fails to find the equiv's own `⇑f` against the
`⇑(f : V →ₗ[K] W)` the lemma is keyed on) needs a `show … from …` term instead of a bare `rw`;
(ii) composing `Submodule.map_span` + `LinearEquiv.finrank_map_eq` directly against the heavy
`Module.Dual K (α → ScrewSpace K k)` carrier `whnf`-times out even under `set`/`clear_value` (the
blowup is in *forming* the named heavy term, not in a later lemma application) — fixed by factoring
the whole composite into a `private` lemma over abstract `{V W}` (TACTICS-QUIRKS §38, new variant;
`notes/FRICTION.md`). `lem:simultaneous-affine-position` and `lem:extensor-affine-representation`
are the remaining witness-trio members.

**Witness trio complete** (2026-07-18): `lem:simultaneous-affine-position`
(`BodyHingeFramework.exists_linearEquiv_forall_last_ne_zero`, `HingeGeneric.lean`) and
`lem:extensor-affine-representation` (`exists_affineSubspaceExtensor_eq_smul_extensor`,
`Extensor.lean`) both landed, closing the three-lemma group the hand-off named. The
simultaneous-affine-position route needed a mathlib combination not covered by any single lemma —
`Module.Dual.finrank_ker_add_one_of_ne_zero` + `FiniteDimensional.nonempty_linearEquiv_of_finrank_eq`
+ `Submodule.exists_linearEquiv_restrict_eq` realizes a nonzero functional as a coordinate after an
ambient automorphism (FRICTION.md, new entry); the extensor-affine-representation route needed two
new general exterior-algebra facts, `extensor_update_add_smul` (a single-slot "add a multiple of one
column to another" elementary operation, via `AlternatingMap.map_update_add`/`_smul`/`_self`) and
`extensor_shear` (iterating it over a `Finset.induction` to shear every other slot toward a fixed
pivot at once) — both added to `Extensor.lean` alongside the existing `extensor_update_smul`. Both
files built warning-clean on the first or second attempt with no `maxHeartbeats` overrides needed.

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
- [x] **Layer BB** — body-bar at ℝ, **endpoint-parameterized** (adjudicated
  JJ-faithful form: "almost all bar endpoint choices"). **Closed 2026-07-17**,
  all nine nodes green (`BodyBar/GenericLift.lean` + `BodyBar/TayTheorem.lean`'s
  bridge lemma): `def:two-extensor`, `def:generic-endpoints`,
  `lem:generic-endpoints-abundance`, `lem:exists-generic-endpoints`,
  `lem:coordinate-extensor-basis`, `lem:extensor-map-rows`,
  `lem:endpoint-witness`, `thm:bodybar-generic-independence`,
  `cor:bodybar-generic-tay`. Witness = JJ Lemma 5.1's coordinate segments via
  the Whiteley-remark change of extensor coordinates (the R0-era `±T` claim is
  refuted — *Decisions made*). Per-node routes and friction (TACTICS-QUIRKS
  §90–§95) are in *Decisions made*; ground-truth signatures are
  `BodyBar/GenericLift.lean` itself.
- [ ] **Layer BH** — geometric body-hinge over `ofHinge` hinge points,
  `[Field K] [Infinite K]`. Chapter extension landed 2026-07-17
  (`sec:generic-lift-bodyhinge`, twelve red nodes, plus
  `lem:deficiency-zero-iff-tree-packing` in `deficiency.tex`; the dep-graph is
  the to-do list). **Eight of twelve nodes green** (2026-07-17/18, same file
  `Molecular/GenericLift/HingeGeneric.lean` except as noted):
  `lem:hinge-rows-polynomial-in-points`, `def:generic-hinge-points`,
  `lem:generic-hinge-points-abundance`, `lem:exists-generic-hinge-points`,
  `lem:generic-hinge-points-nondegenerate`
  (`supportExtensor_ofHinge_ne_zero_of_isGenericHingePoints`), `lem:screw-map-rows`
  (`mapSupport`/`finrank_span_rigidityRows_mapSupport`),
  `lem:simultaneous-affine-position` (`exists_linearEquiv_forall_last_ne_zero`),
  `lem:extensor-affine-representation`
  (`exists_affineSubspaceExtensor_eq_smul_extensor`, `Molecular/Extensor.lean`) —
  see *Current state*. The witness-trio group is complete; only the assembly
  (`lem:hinge-point-witness`) and the rank/rigidity/packing nodes downstream of it remain.
  Source: JJ 2010 §6 (Thm 6.1 / Cor 6.3 / Thm 6.4 — the
  "Thm 8.1/8.2" pointer is corrected, *Decisions made*). Witness route:
  transplant of the KT Theorem-5.6 panel witness through the meet
  decomposition (`exists_extensor_eq_panelSupportExtensor_gen`), a
  simultaneous off-infinity coordinate change, and the affine representation;
  extraction via W6e (`exists_independent_panelRow_subfamily_of_le_finrank`)
  at OUR selector — no ± sign transport (the `hingePointRow`/`panelRow`
  bridge is `rfl`, unlike Layer P). Slice-time flags: (i) the tight ⟹
  connected step of the packing bridge may need a small `IsTight`-connectivity
  helper; (ii) the screw-space equiv induced by `g : K^(k+2) ≃ₗ K^(k+2)`
  needs `exteriorPower.map` functoriality plumbing (equiv from `map g ∘ map
  g⁻¹ = id`) — name-hunt at slice time.
  Target signatures:

  ```
  -- (namespace CombinatorialRigidity.Molecular.BodyHingeFramework unless noted; new file
  --  CombinatorialRigidity/Molecular/GenericLift/HingeGeneric.lean, except
  --  lem:extensor-affine-representation → Molecular/Extensor.lean and the packing bridge →
  --  Molecular/Deficiency.lean (namespace Graph); [Field K] throughout, adjudication items 2/3;
  --  shorthand ν := Set.powersetCard (Fin (k+2)) k)
  -- lem:hinge-rows-polynomial-in-points (settles the build-time open: the extensor coordinates
  --   are the k×k minors of the homogenized point matrix, degree ≤ k; eval route =
  --   screwBasis_repr_apply + exteriorPower.basis_repr_apply + ιMultiDual_apply_ιMulti +
  --   RingHom.map_det — the grade-k form of normalsJoin_basis_repr, no complementIso staging)
  noncomputable def hingeExtensorPoly (e : β) (t : ν) : MvPolynomial (β × Fin k × Fin (k + 1)) K
    -- := (Matrix.of fun i j => Fin.snoc (fun b => X (e, i, b)) 1 ((t : Finset _).orderEmbOfFin t.2 j)).det
  theorem hingeExtensorPoly_eval (e : β) (q : β × Fin k × Fin (k + 1) → K) (t : ν) :
      MvPolynomial.eval q (hingeExtensorPoly e t)
        = (screwBasis k).repr (ScrewSpace.mk (affineSubspaceExtensor fun i b => q (e, i, b))
            (affineSubspaceExtensor_mem_exteriorPower _)) t
  -- def:generic-hinge-points (graph-free row family, the pinned transfer form; the framework
  --   bridge is rfl because ofHinge's supportExtensor IS the ScrewSpace.mk below)
  noncomputable def hingePointRow (ends : β → α × α) (q : β × Fin k × Fin (k + 1) → K)
      (i : β × ν × ν) : Module.Dual K (α → ScrewSpace K k)
    -- := hingeRow (ends i.1).1 (ends i.1).2 (annihRow (ScrewSpace.mk
    --      (affineSubspaceExtensor fun a b => q (i.1, a, b)) _) i.2.1 i.2.2)
  theorem hingePointRow_eq_panelRow (G : Graph α β) (ends) (q) (i) :
      hingePointRow ends q i = (ofHinge G fun e a b => q (e, a, b)).panelRow ends i  -- rfl
  def IsGenericHingePoints (ends : β → α × α) (q : β × Fin k × Fin (k + 1) → K) : Prop :=
    ∀ s : Set (β × ν × ν),
      (∃ q', LinearIndependent K fun i : s => hingePointRow ends q' i) →
        LinearIndependent K fun i : s => hingePointRow ends q i
  -- lem:generic-hinge-points-abundance (Layer-P engine, c = incidence sign •
  --   (guarded hingeExtensorPoly difference, the annihRowPoly shape); PLUS the genuine-hinge
  --   conjunct: one reference-minor factor per edge, reference = k affinely independent points
  --   of K^(k+1), e.g. 0, e₀, …, e_(k−2))
  theorem exists_isGenericHingePoints_abundance [Finite α] [Finite β] (ends : β → α × α) :
      ∃ P : MvPolynomial (β × Fin k × Fin (k + 1)) K, P ≠ 0 ∧
        ∀ q, MvPolynomial.eval q P ≠ 0 → IsGenericHingePoints ends q ∧
          ∀ e, AffineIndependent K fun i : Fin k => (fun b => q (e, i, b))
  -- lem:exists-generic-hinge-points
  theorem exists_isGenericHingePoints [Infinite K] [Finite α] [Finite β] (ends : β → α × α) :
      ∃ q : β × Fin k × Fin (k + 1) → K, IsGenericHingePoints ends q ∧
        ∀ e, AffineIndependent K fun i : Fin k => (fun b => q (e, i, b))
  -- lem:generic-hinge-points-nondegenerate (mirror of Layer P's, seed = the reference points on
  --   every edge — no moment curve; singleton transfer + annihRow-linear-in-C readback)
  theorem supportExtensor_ofHinge_ne_zero_of_isGenericHingePoints (hk1 : 1 ≤ k)
      (ends : β → α × α) {G : Graph α β} (hloop : G.Loopless)
      (hends : ∀ e, G.IsLink e (ends e).1 (ends e).2) {q : β × Fin k × Fin (k + 1) → K}
      (hq : IsGenericHingePoints ends q) :
      ∀ e, (ofHinge G fun e' a b => q (e', a, b)).supportExtensor e ≠ 0
  -- lem:screw-map-rows (RANK-level, not the BB row-family shape — annihRow is basis-pinned, so
  --   the indexed family does not transform member-to-member; the per-edge blocks
  --   (span C)^⊥ do: r ∘ M ∈ (span C)^⊥ ↔ r ∈ (span (M C))^⊥, and
  --   hingeRow u v (r ∘ M) = hingeRow u v r ∘ (bodywise M); Submodule.map_span +
  --   LinearEquiv.finrank_eq close)
  noncomputable def mapSupport (F : BodyHingeFramework K k α β)
      (M : ScrewSpace K k ≃ₗ[K] ScrewSpace K k) : BodyHingeFramework K k α β
    -- := ⟨F.graph, fun e => M (F.supportExtensor e)⟩
  theorem finrank_span_rigidityRows_mapSupport (F) (M) :
      Module.finrank K (Submodule.span K (F.mapSupport M).rigidityRows)
        = Module.finrank K (Submodule.span K F.rigidityRows)
  -- lem:extensor-affine-representation (Extensor.lean; column reduction on the last coordinate —
  --   scale u₀ to last-coord 1, kill the others' last coords, add u₀ back; extensor_update_smul
  --   + an add-column-multiple step)
  theorem exists_affineSubspaceExtensor_eq_smul_extensor {k : ℕ}
      {u : Fin k → Fin (k + 2) → K} (h0 : ∃ i, u i (Fin.last (k + 1)) ≠ 0) :
      ∃ (p : Fin k → Fin (k + 1) → K) (c : Kˣ),
        affineSubspaceExtensor p = (c : K) • extensor u
  -- lem:simultaneous-affine-position (product of the linear forms ⟨w e, ·⟩ +
  --   MvPolynomial.exists_eval_ne_zero; complete the non-root functional to an invertible map
  --   whose last coordinate row it is)
  theorem exists_linearEquiv_forall_last_ne_zero [Infinite K] {ι : Type*} [Finite ι]
      (w : ι → Fin (k + 2) → K) (hw : ∀ e, w e ≠ 0) :
      ∃ g : (Fin (k + 2) → K) ≃ₗ[K] (Fin (k + 2) → K),
        ∀ e, g (w e) (Fin.last (k + 1)) ≠ 0
  -- lem:hinge-point-witness (producer rankHypothesis_genuine_recordsLinks_of_theorem_55_gen →
  --   meet decomposition per edge (nonzero extensor ⟹ LI normals,
  --   panelSupportExtensor_ne_zero_iff, then exists_extensor_eq_panelSupportExtensor_gen,
  --   NeZero k from hk1) → mover g on the leading points (LI family members are nonzero) →
  --   ⋀^k g on screws preserves the row-span rank (mapSupport) → affine points per edge; the
  --   hinge blocks are span-scale-invariant so ofHinge G q₀'s rigidityRows span has the
  --   producer's rank (rank read off RankHypothesis via
  --   finrank_span_rigidityRows_add_finrank_infinitesimalMotions, the Layer-P hrank0 shape) →
  --   W6e at OUR ends + the rfl bridge)
  theorem exists_hingePoints_independent_hingePointRow [Infinite K]
      [Nonempty α] [Finite α] [Finite β] [DecidableEq β] {n : ℕ}
      (hk1 : 1 ≤ k) (hD : 6 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim k)
      (hfresh : ∀ (c : ℤ) (G' : Graph α β), G'.IsMinimalKDof n c → ∃ e₀ : β, e₀ ∉ E(G'))
      (G : Graph α β) (hV : 2 ≤ V(G).ncard) (hspan : V(G) = Set.univ) (hSimple : G.Simple)
      (ends : β → α × α) (hends : ∀ e, G.IsLink e (ends e).1 (ends e).2) :
      ∃ (q₀ : β × Fin k × Fin (k + 1) → K) (s : Set (β × ν × ν)),
        (Nat.card s : ℤ) = screwDim k * (V(G).ncard - 1 : ℤ) - G.deficiency n ∧
        LinearIndependent K fun i : s => hingePointRow ends q₀ i
  -- thm:bodyhinge-generic-rank (the Layer-P pinch verbatim: witness + transfer +
  --   panelRow_mem_rigidityRows_of_link for ≥; B2 finrank_span_rigidityRows_add_deficiency_le +
  --   nondegeneracy for ≤)
  theorem finrank_span_rigidityRows_ofHinge_of_isGenericHingePoints [Infinite K]
      [Nonempty α] [Finite α] [Finite β] [DecidableEq β] {n : ℕ}
      (hk1 : 1 ≤ k) (hD : 6 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim k)
      (hfresh : ∀ (c : ℤ) (G' : Graph α β), G'.IsMinimalKDof n c → ∃ e₀ : β, e₀ ∉ E(G'))
      (G : Graph α β) (hV : 2 ≤ V(G).ncard) (hspan : V(G) = Set.univ) (hSimple : G.Simple)
      (ends : β → α × α) (hends : ∀ e, G.IsLink e (ends e).1 (ends e).2)
      {q : β × Fin k × Fin (k + 1) → K} (hq : IsGenericHingePoints ends q) :
      (Module.finrank K (Submodule.span K
          (ofHinge G fun e a b => q (e, a, b)).rigidityRows) : ℤ)
        = screwDim k * (V(G).ncard - 1 : ℤ) - G.deficiency n
  -- cor:bodyhinge-generic-rigid (rank–nullity via
  --   isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows, mirror of Layer P)
  theorem isInfinitesimallyRigidOn_ofHinge_isGenericHingePoints_iff
      [Infinite K] … (same setting, no q) :
      (∀ q : β × Fin k × Fin (k + 1) → K, IsGenericHingePoints ends q →
          (ofHinge G fun e a b => q (e, a, b)).IsInfinitesimallyRigidOn V(G))
        ↔ G.deficiency n = 0
  -- lem:deficiency-zero-iff-tree-packing (Deficiency.lean, namespace Graph; → via a base +
  --   IsKDof.exists_isBase_isForestPacking-style decomposition + the tight upgrade
  --   isSpanningTreePacking_of_isTight (tight ⟹ connected: two-component sparsity count —
  --   flag (i)); ← generalizes molecule_generic_square_packing's hdef derivation to general n
  --   (IsTree.ncard_vertexSet, Matroid.union_indep_iff/cycleMatroid_indep,
  --   Indep.isBase_of_ncard + isBase_ncard_add_deficiency_eq + deficiency_nonneg))
  theorem Graph.deficiency_eq_zero_iff_exists_spanningTrees [DecidableEq β] [Finite α] [Finite β]
      (G : Graph α β) (n : ℕ) [NeZero (bodyHingeMult n)] (hne : V(G).Nonempty) :
      G.deficiency n = 0 ↔
        ∃ Ts : Fin (bodyBarDim n) → Graph α (β × Fin (bodyHingeMult n)),
          (∀ i, Ts i ≤s G.mulTilde n) ∧ (∀ i, (Ts i).IsTree) ∧
            Pairwise (Function.onFun Disjoint fun i => E(Ts i))
  -- cor:bodyhinge-generic-tree-packing (JJ Cor 6.3 in every-generic form; compose the two)
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

- None blocking; no build-time opens (both Layer-BH opens settled at the
  chapter-extension commit — *Decisions made*). Two slice-time flags are
  recorded in the Layer-BH checklist item (the `IsTight`-connectivity helper;
  the `exteriorPower.map` equiv plumbing).

## Hand-off / next phase

Layers M, P, and BB are all fully green; the Layer-BH chapter extension is landed,
and eight of its twelve nodes (coordinatization + definition + abundance +
existence + nondegeneracy + the full witness trio: `lem:screw-map-rows`,
`lem:simultaneous-affine-position`, `lem:extensor-affine-representation`) are
green (`Molecular/GenericLift/HingeGeneric.lean` + `Molecular/Extensor.lean` —
see *Current state*). The remaining work is the witness assembly and the
downstream rank/rigidity/packing nodes.

- **Next concrete commit: the witness assembly, `lem:hinge-point-witness`**
  (`exists_hingePoints_independent_hingePointRow`, `HingeGeneric.lean`; target
  signature in the Layer-BH checklist item). Route (per *Decisions made*,
  "Layer-BH witness route"): the KT Theorem-5.6 panel witness
  (`rankHypothesis_genuine_recordsLinks_of_theorem_55_gen`) decomposes each
  edge's supporting extensor as a meet of two panels
  (`exists_extensor_eq_panelSupportExtensor_gen`), giving `k` spanning points
  per edge; apply `lem:simultaneous-affine-position` to move every edge's
  leading spanning point off the hyperplane at infinity in one invertible map
  `g`; `mapSupport g` (via `lem:screw-map-rows`) carries every supporting
  extensor along, preserving the rigidity-row span's rank; apply
  `lem:extensor-affine-representation` to read each moved extensor as an
  affine hinge-point family; extract the independent subfamily over OUR
  selector via W6e (`exists_independent_panelRow_subfamily_of_le_finrank`).
  This is a substantial single-lemma assembly (five nontrivial routing steps
  through prior results) — if it doesn't fit one sitting, land the meet-
  decomposition + coordinate-move half first and defer the extraction half,
  or return BLOCKED naming the exact step that doesn't close. After the
  assembly: the packing bridge (`Deficiency.lean`); the rank-formula theorem +
  two corollaries (the Layer-P pinch verbatim). Closing Layer BH closes the
  phase.

## Decisions made during this phase

- **Layer BH strength (adjudication item 5, 2026-07-17): all three forms,
  plus the genuine-hinge conjunct.** The rank-formula theorem
  (`thm:bodyhinge-generic-rank`, JJ Thm 6.1's `D(|V|−1) − def(G̃)` at every
  generic hinge-point assignment), the rigidity iff-form
  (`cor:bodyhinge-generic-rigid`), and the tree-packing iff-form
  (`cor:bodyhinge-generic-tree-packing`, JJ Cor 6.3 sharpened to
  every-generic), via one new graph-theoretic bridge
  (`lem:deficiency-zero-iff-tree-packing`) assembled from landed pieces.
  Rationale: the Layer-P situation exactly — the witness/B2 pinch *is* the
  rank formula; the iffs are thin corollaries; the packing form is JJ's
  headline body-hinge statement. The abundance node additionally carries
  per-edge affine independence (the dispatch-adjudicated genuine-hinge
  conjunct) as one more reference-minor product factor — graph-free extra
  content the nondegeneracy lemma (which needs a linked loopless `G`) does
  not subsume.
- **Layer-BH citation corrected (2026-07-17, against the JJ PDF): the layer's
  source is JJ 2010 §6, not Thm 8.1/8.2.** §6 carries the body-and-hinge
  statements — Thm 6.1 (max rank `D(|V|−1) − def_D(G^H)`), the p. 583 generic
  definition, Cor 6.2/6.3 (rigid iff `(D−1)G` has `D` edge-disjoint spanning
  trees; JJ credit Tay 1989 + Whiteley 1988), Thm 6.4 (a max-rank realization
  with hinges on coordinate-simplex facets). Thms 8.1/8.2 (§8) are the
  *molecular* corollaries — Layer M's territory (the p. 586 remark) — and the
  earlier checklist pointer to them for this layer was a mis-attribution.
- **Hinge-point polynomial family settled (2026-07-17, closes the Layer-BH
  build-time open).** The screw-basis coordinates of the `ofHinge` support
  extensor are the `k×k` minors of the homogenized hinge-point matrix
  (Plücker coordinates; one constant column of `1`s, so total degree ≤ `k`),
  computed *directly* by mathlib's `exteriorPower.ιMultiDual_apply_ιMulti`
  determinant formula through the project's `exteriorPower.basis_repr_apply`
  mirror — the grade-`k` form of `normalsJoin_basis_repr`, with **no
  complementIso staging** (unlike the panel layer's `panelSupportPoly`).
  Annihilator-row assembly then mirrors `annihRowPoly` verbatim.
- **Layer-BH witness route (2026-07-17): transplant the KT Theorem-5.6 panel
  witness into the hinge-point space; do not re-prove JJ Thm 6.1/6.4.** Per
  edge, the panel meet decomposes into `k` spanning points
  (`exists_extensor_eq_panelSupportExtensor_gen`); a hinge whose span lies in
  the hyperplane at infinity is `ofHinge`-unreachable (the BB
  line-at-infinity analogue), so one coordinate change moves all hinges off
  infinity simultaneously (a product-of-linear-forms non-root, the JJ
  Lemma-7.1 coordinate-choice device) before affine points are read off. The
  BB `lem:extensor-map-rows` row-family shape does **not** port — `annihRow`
  is pinned to exterior-basis coordinate pairs, so the indexed family does
  not transform member-to-member; the invariance that holds (and suffices,
  since W6e consumes a rank bound) is at the *row-span rank* level
  (`lem:screw-map-rows`/`mapSupport`), because each edge block is the
  scale-invariant annihilator of the extensor's span. Same span-invariance
  makes the `hingePointRow`/`panelRow` bridge `rfl` with no ± transport
  (unlike Layer P's swap signs).
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
  extensors form a basis (`lem:coordinate-extensor-basis`; landed as a
  **spanning** argument over the entry table, not JJ's triangular
  elimination — every standard basis vector is a two-extensor combination,
  see *Current state*), and a fixed invertible extensor-space map
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
