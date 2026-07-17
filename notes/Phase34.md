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

Remaining Layer-M work: the **abundance node**
(`lem:generic-placement-abundance`) and the **packing corollary**
(`cor:molecule-generic-square-packing`) are still red — both flagged
unrecon'd at chapter-open (*Decisions made*), verify before green-flipping.
Next concrete step: the abundance lemma (*Hand-off*).

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
- [ ] **Layer M** — molecular / bar-joint `G²` (d = 3, ℝ). Tracked by the
  chapter dep-graph: `thm:molecule-generic-rank` and `cor:molecule-generic-rigid`
  are green (`SimpleGraph.molecule_generic_rank`/`molecule_generic_rigid`,
  `Molecular/Molecule/Application.lean`); `lem:generic-placement-abundance` and
  `cor:molecule-generic-square-packing` remain red.
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

Next concrete commit: the **abundance lemma**
(`lem:generic-placement-abundance`) — formalize the Gram-determinant product
route flagged at chapter-open (*Decisions made*, "unrecon'd-transcription
flags" item (ii)): for each edge subset `I` row-independent at some placement,
the Gram determinant of its rigidity rows is a nonzero polynomial `P_I` in the
placement coordinates; the finite product `P = ∏ P_I` over the (finitely many)
such `I` is a nonzero `MvPolynomial` witnessing `IsGenericPlacement` via
`MvPolynomial.exists_eval_ne_zero`-style abundance. Verify the Gram-determinant
route against the Lean `rigidityRow`/`EdgeSetRowIndependent` API before writing
the proof (the flagged step is elementary but not yet compiler-checked). After
that, `cor:molecule-generic-square-packing` is the last Layer-M node — verify
its flagged hypothesis-shape (*Decisions made*, item (i): no min-degree
hypothesis; the `|V| = 1` case and packing-implies-min-degree-2 live in the
proof) before green-flipping.

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
  Authored beyond R0's pins, to verify at slice time before the green
  flip: (i) `cor:molecule-generic-square-packing`'s hypothesis shape — no
  min-degree hypothesis; the `|V| = 1` trivial case and the
  packing-implies-min-degree-2 step live in the proof; (ii)
  `lem:generic-placement-abundance`'s Gram-determinant route (product of
  per-subset Gram polynomials). Both elementary but not compiler-checked.
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
