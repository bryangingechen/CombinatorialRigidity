# Phase 42f — PD-STEPS: cut vertices, bridges and contraction in every dimension (work log)

**Status:** in progress, opened 2026-10-30 at the PI's word ("-cut + -contract (Recommended)",
design doc §1), a sub-phase of Phase 42 and the first of PD-STEPS. Forward mode, the Lean under
`/coordinate-phase`: the six red nodes of `blueprint/src/chapter/pencil-d.tex` in
`sec:pencil-d-cut` and `sec:pencil-d-contract` (Phase 40e/40f/40k in `Pᵈ`), on the `Pencil/Grade/`
carrier. The open's consistency read found every proof routing through the argument its statement
claims (*Consistency read at the open*). At the PI's word the open also cut three step nodes no
coverage step uses, leaving PD-STEPS 25 nodes. The pre-build recon pinned all six Lean signatures
and spiked each complete, with no `sorry` (*Lemma checklist*). Next (*Hand-off*): land
`Pencil/Grade/Cut.lean`, the restriction, the cut vertex and the chain of bridges.

## Current state

**Next: land `Pencil/Grade/Cut.lean`** (*Hand-off*). The pre-build recon pinned the Lean of all
six nodes and checked it under `lake lean`: no `sorry`, no warning, `#lint` clean (15 linters),
`#print axioms` `[propext, Classical.choice, Quot.sound]` on every pinned name. The two spikes are
complete in the gitignored `scratch/42f/`: `Cut.lean` (three nodes, to become `Grade/Cut.lean`)
and `ContractAdditive.lean` (three nodes, to become `Grade/ContractAdditive.lean`; it repeats three
lemmas of `Cut.lean` verbatim, to drop for `import …Grade.Cut`). Their docstrings are short; the
builds write the full ones. If the spikes are gone, the signatures and routes under *Lemma
checklist* rebuild them. Both are new files: no landed Lean file changes but the root import
list. The chapter is the lemma index (forward mode). The rest of PD-STEPS, `-short` (12) and `-long` (7), stays mapped by section
in design doc §3, with no letter minted.

## Architectural choices made up front

- **Scope** (the PI's, verbatim in design doc §1): the six nodes above.
- **The cut** (the PI's, verbatim in design doc §1): `thm:pencil-d-splitoff`,
  `thm:pencil-d-open-ear-deficiency` and `lem:pencil-d-polygon-ear` are deleted with their sections
  `sec:pencil-d-splitoff` and `sec:pencil-d-ear-deficiency` (the text is in git, last at
  `eeb82ae2`). The coverage section keeps one sentence: from `d = 4` on, no step is needed at a
  chain with one or two interior bodies (`thm:pencil-x0-splitoff`, `thm:pencil-x0-open-ear-two`).
- **Encoding** as 42b, 42c and 42e: `m = d − 2` heights at grade `k = m + 1`,
  `D = screwDim (m + 1)`, `def_d` is `G.deficiency (m + 2)` and `def_2` is `G.deficiency 2`.
  Attaining is `Graph.X0AttainsGrade K m`, its witness lemma `Graph.x0AttainsGrade_of_exists` (rank
  at least the target). As in 42e the Lean may hold at every `m` while the nodes keep `d ≥ 3`.

## Consistency read at the open

The red-node consistency gate (`PHASE-BOUNDARIES.md`): each node read in full against the landed
carrier (`Pencil/Grade/`, 42b–42e) and the `main-component.tex` node it generalizes, with every Lean
name below opened at its declaration. **All six PASS**; no proof fails against the carrier, and no
`\uses` reaches a superseded node (`blueprint/lint.sh`, check 3). Every dependency outside the six
is green.
- **`lem:pencil-d-lifting-restrict`** generalizes `lem:pencil-lifting-restrict` (`MainComponent/Cut.lean`:
  `Graph.liftingRestrict_mem_liftingSpace`, `pencilConfigPoint_liftingRestrict`,
  `eval_restrictPoly`). Each part holds height by height. (1): `L(q)^m` is the per-column `⨅`
  (`Graph.mem_liftingSpaceGrade`); Lean's `L(q)` holds heights vanishing off `V(G)`, and `z'`
  vanishes off `V(G')` by construction, as at `d = 3`. (2): `pencilConfigPointGrade` reads only `w`'s
  picture point and heights, and `PanelHingeFramework.finrank_span_rigidityRows_ofNormals_congr` is
  `k`-general, as the proof claims. (3): `restrictPoly`'s substitution on `MvPolynomial (α × Fin m)`.
  No grade Lean yet.
- **`thm:pencil-d-cut`** generalizes `thm:pencil-x0-cut` (`Graph.X0Attains.of_cutVertex`). The
  heights lift per column by `Graph.exists_liftingRestrict_eq_of_cutVertex` (planar, any picture);
  the two `R`s meet on `G.liftingSpaceGrade q m` (`MvPolynomial.exists_mem_eval_ne_zero₂` takes any
  submodule); the count uses `BodyHingeFramework.finrank_span_rigidityRows_cutVertex_eq` (any `k`)
  and `Graph.deficiency_eq_add_of_cutVertex` (any `n`; the `d = 3` Lean's `…_add_le_…` also closes,
  as the witness lemma takes rank ≥ target).
- **`thm:pencil-d-bridge`** generalizes `thm:pencil-x0-bridge` (`Graph.X0Attains.of_bridgePath`).
  Heights as at a cut vertex, by `Graph.exists_liftingRestrict_eq_of_bridgePath` (from `b` by
  `pathVertex_rev`); hinges nonzero by `Graph.IsAdmissiblePicture.supportExtensor_ne_zero_grade`
  (admissibility alone; the proof's "and `z ∈ L_G(q)^{d−2}`" is true, unused); the counts by
  `BodyHingeFramework.le_finrank_span_rigidityRows_of_cut`,
  `…add_le_finrank_span_rigidityRows_induce_union_range_of_bridgePath` (any `d`) and
  `Graph.deficiency_eq_of_cutEdges_ncard_le_one`, `Graph.deficiency_induce_union_range_of_bridgePath`
  (any `n`).
- **`lem:pencil-contract-additive-kernel`** extracts the two kernel bounds that
  `Graph.X0Attains.of_additiveContract` (`MainComponent/ContractAdditive.lean`, `hlow0`, `hup0`,
  `honto`) proves inline. One height, planar: no grade. The lower bound needs only admissibility at
  `q(t)` (`Graph.three_add_deficiency_le_finrank_liftingSpace`), so the node's `A` is
  `Graph.IsAdmissiblePicture.exists_mvPolynomial` (unpinned; the prose after
  `def:pencil-admissible-picture`) where the `d = 3` proof used the main-picture polynomial. The
  upper bound is `Graph.finrank_ker_contractLiftingMatrix_zero_add_three_le` with
  `Graph.liftingRestrict_mem_liftingSpace_induce_of_contract`; additivity closes the chain.
- **`thm:pencil-d-contract-additive`** transcribes `Graph.X0Attains.of_additiveContract` with `m`
  heights. The pieces hold at `n = m + 2` (`Graph.isX0Graph_induce_of_deficiency_eq_zero`,
  `Graph.rigidContract_deficiency_eq`); the shift is the landed scale-shift with `T` the identity;
  `ρ` maps `ker M(0)^m` onto `L_H(q)^m` columnwise; `Graph.exists_mem_ker_contractLiftingMatrix_zero`
  per height gives the collapsed placement; `PanelHingeFramework.exists_rankPolynomial_rigidContract_induce_proj`
  and `…induce_add_map_extProj_le` are `k`-general; the core's rank along the curve is the landed
  `Graph.finrank_span_rigidityRows_induce_contractHeightGrade_eq`. Wording only: "So every hinge …
  is nonzero, and the rank of `G/H` at `b′` is `tgt_d(G/H)`": the second clause is `z′` attaining
  (the paragraph before), not the hinges; true as written.
- **`cor:pencil-d-contract-rigid`** generalizes `cor:pencil-x0-contract-rigid`
  (`Graph.X0Attains.of_rigidContract`) through landed Lean only:
  `Graph.isX0Graph_induce_of_deficiency_two_eq_zero`, `Graph.deficiency_eq_zero_of_deficiency_eq_zero_of_le`
  at `n = 2`, `Graph.x0AttainsGrade_of_deficiency_two_eq` (42e) and `Graph.rigidContract_deficiency_eq`
  at `n = 2`.

## Lemma checklist

Shorthand, exact by substitution. Every declaration is in
`namespace CombinatorialRigidity.Molecular`, with `variable {K : Type*} [Field K] {α β : Type*}
{m : ℕ}`, under `@[expose] public section`; `Graph.` names are `_root_.Graph.…`. `hends` is `∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1
(ends e).2` (at the graph named); `rk(H, ends, q, z)` is `Module.finrank K (Submodule.span K
(PanelHingeFramework.ofNormals (k := m + 1) H ends (fun p => pencilConfigPointGrade q z p.1 p.2)
).toBodyHinge.rigidityRows)`. `z|X` is `Graph.liftingRestrict (Prod.fst ⁻¹' X) z`, the restriction
of `m` heights (*Blockers*, 1). `G/H` is `G.rigidContract (G.induce W) r`; `ker M(0)` is
`LinearMap.ker ((G.contractLiftingMatrix K W r q).map (MvPolynomial.eval fun _ => (0 : K)))
.mulVecLin`; `hatt` is `∀ u ∉ W, ∀ c₁ ∈ W, ∀ c₂ ∈ W, G.Adj u c₁ → G.Adj u c₂ → c₁ = c₂`.

- [x] **Pre-build recon** (this commit): the signatures below, every spike complete.
- [ ] `lem:pencil-d-lifting-restrict`, in the new `Pencil/Grade/Cut.lean` (imports
  `Grade.Witness`, `MainComponent.Cut`). Pin `Graph.liftingRestrict_mem_liftingSpaceGrade`
  (`{G G'} (hle : G' ≤ G) {q} {z : α × Fin m → K} (hz : z ∈ G.liftingSpaceGrade q m) :
  z|V(G') ∈ G'.liftingSpaceGrade q m`), `pencilConfigPointGrade_liftingRestrict`
  (`(X q z) {x} (hx : x ∈ X) : pencilConfigPointGrade q (z|X) x = pencilConfigPointGrade q z x`),
  `PanelHingeFramework.finrank_span_rigidityRows_ofNormals_liftingRestrict_grade`
  (`[Finite α] {G' X} (hX : V(G') ⊆ X) {ends ends'} hends hends' (q z) :
  rk(G', ends, q, z|X) = rk(G', ends', q, z)`) and the landed `eval_restrictPoly` (part (3) as
  it stands, at `α × Fin m`), the last three pinned with the `CombinatorialRigidity.Molecular.`
  prefix. Two helpers: `Graph.liftingRestrict_preimage_fst_apply` (`rfl`: column
  `i` of `z|X` is `Graph.liftingRestrict X` of column `i`) and
  `Graph.exists_liftingRestrict_preimage_fst_eq` (`(hlift : ∀ y ∈ G'.liftingSpace q, ∃ z ∈
  G.liftingSpace q, Graph.liftingRestrict X z = y) (hy : y ∈ G'.liftingSpaceGrade q m) :
  ∃ z ∈ G.liftingSpaceGrade q m, z|X = y`), the "height by height" of the cut and the bridge.
- [ ] `thm:pencil-d-cut`, in `Grade/Cut.lean`. Pin `Graph.X0AttainsGrade.of_cutVertex`: the
  hypotheses of `Graph.X0Attains.of_cutVertex` verbatim (`[Infinite K] [Finite α] [Finite β]`,
  `hG`, `hcover`, `hoverlap`, `hsep`), with `h₁ : (G.induce V₁).X0AttainsGrade K m`,
  `h₂ : (G.induce V₂).X0AttainsGrade K m`, concluding `G.X0AttainsGrade K m`. Route: the `d = 3`
  proof, with the helper over `Graph.exists_liftingRestrict_eq_of_cutVertex`,
  `restrictPoly (Prod.fst ⁻¹' V₁)`, the rank lemma above at `(X := V(G.induce V₁))` (`rw` needs
  that form, not `V₁`), `Graph.deficiency_add_le_of_cutVertex … (m + 2)`, and
  `screwDim (m + 1) * (|V₁| + |V₂|) = screwDim (m + 1) * (|V(G)| + 1)` given to `linarith`.
- [ ] `thm:pencil-d-bridge`, in `Grade/Cut.lean`. Pin `Graph.X0AttainsGrade.of_bridgePath`: the
  hypotheses of `Graph.X0Attains.of_bridgePath` verbatim, with `X0AttainsGrade K m` at both sides
  and in the conclusion. Route: the `d = 3` proof, with
  `Graph.IsAdmissiblePicture.supportExtensor_ne_zero_grade`, `(n := m + 2)` throughout,
  `(Graph.bodyBarDim (m + 2) : ℤ) = screwDim (m + 1)` (`Graph.bodyBarDim_add_one_eq_screwDim`)
  and `push_cast [Nat.cast_sub one_le_screwDim]` for the `D − 1` terms.
- [ ] `lem:pencil-contract-additive-kernel`, in the new `Pencil/Grade/ContractAdditive.lean`
  (imports `Grade.Cut`, `Grade.Contract`, `Grade.Flat`, `Molecular.Induction.SparseDeficiency`).
  Pin `Graph.finrank_ker_contractLiftingMatrix_zero_eq_and_map_eq`: `[Infinite K] [Fintype α]
  [Finite β] {G W r} (hr : r ∈ W) (hW : W ⊆ V(G)) (hadd : (G.induce W).deficiency 2 +
  (G/H).deficiency 2 ≤ G.deficiency 2) {q} (hqG : G.IsAdmissiblePicture q)
  (hqH : (G.induce W).IsAdmissiblePicture q) (hqc : (G/H).IsAdmissiblePicture q)
  (hdimH : (Module.finrank K ((G.induce W).liftingSpace q) : ℤ) = 3 + (G.induce W).deficiency 2)
  (hdimc : (Module.finrank K ((G/H).liftingSpace q) : ℤ) = 3 + (G/H).deficiency 2) :
  (Module.finrank K (ker M(0)) : ℤ) = 3 + G.deficiency 2 ∧
  (ker M(0)).map (contractCoreRestrict W) = (G.induce W).liftingSpace q`. `[Fintype α]`, as the
  statement's `mulVecLin` needs one. Route: `hlow0`, `hup0` and `honto` of
  `Graph.X0Attains.of_additiveContract`, with `A := hqG.exists_mvPolynomial` read along the curve.
- [ ] `thm:pencil-d-contract-additive`, in `Grade/ContractAdditive.lean`. Pin
  `Graph.X0AttainsGrade.of_additiveContract`: the hypotheses of `Graph.X0Attains.of_additiveContract`
  verbatim but `hdefd : (G.induce W).deficiency (m + 2) = 0` for `hdef3`, with `hH`, `hc` and the
  conclusion at `X0AttainsGrade K m`. The tuple machinery: unknowns uncurried,
  `(α ⊕ (α × Fin 3)) × Fin m → K`, for the fibre lemma, and curried, `Fin m → α ⊕ (α × Fin 3) → K`,
  for the curve (`Graph.finrank_span_rigidityRows_induce_contractHeightGrade_eq` takes that form);
  `ker M(0)^m` a local `set Lm := ⨅ i : Fin m, L.comap (LinearMap.funLeft K K fun c => (c, i))`;
  `PA := MvPolynomial.rename (fun p => (Sum.inl p.1, p.2)) (restrictPoly (Prod.fst ⁻¹' W) RH)`;
  `PB` is `Qc` at the configuration at `t = 0`, a `bind₁` through `map_vecCons_vecCons_snoc`; one
  section per height by `choose` over `Matrix.exists_mvPolynomial_section_mulVec_eq_zero`, with
  `∏ i, D i`; and a new `contractConfigPolyGrade W r q (Z : Fin m → α ⊕ (α × Fin 3) →
  MvPolynomial Unit K) : α × Fin (m + 1 + 2) → MvPolynomial Unit K` (`open Classical in`; blocks
  as `pencilConfigPointGrade`) with `eval_contractConfigPolyGrade`. The shift is
  `Graph.finrank_span_rigidityRows_ofNormals_heights_linearEquiv_add_affineLifts` at
  `LinearEquiv.refl`, `a i := (G/H).affineLiftMap q ![0, 0, -z₁ (r, i)]`;
  `NeZero (Graph.bodyHingeMult (m + 2))` from `two_le_screwDim`.
- [ ] `cor:pencil-d-contract-rigid`, in `Grade/ContractAdditive.lean`. Pin
  `Graph.X0AttainsGrade.of_rigidContract`: the hypotheses of `Graph.X0Attains.of_rigidContract`
  verbatim, with `hc` and the conclusion at `X0AttainsGrade K m`. Route:
  `Graph.isX0Graph_induce_of_deficiency_eq_zero (n := 2)` (the pin of
  `lem:pencil-contract-standing-rigid`), `Graph.deficiency_eq_zero_of_deficiency_eq_zero_of_le
  (n := 2)` (hence the `SparseDeficiency` import), `Graph.rigidContract_deficiency_eq` at `n = 2`,
  `Graph.x0AttainsGrade_of_deficiency_two_eq`.
- [ ] **Close** 42f, an intermediate sub-phase close (`PHASE-BOUNDARIES.md`).

## Blockers / open questions

- None. The open's four questions, resolved by the recon:
  1. **The tuple restriction needs no definition.** `Graph.liftingRestrict` and `restrictPoly` are
     generic in the type of bodies, so at `α × Fin m` with `Prod.fst ⁻¹' X` they are the tuple
     forms, and `eval_restrictPoly` is part (3) as it stands. Home: the new `Grade/Cut.lean`, with
     the cut and the bridge.
  2. **The kernel lemma goes in a new file**, `Grade/ContractAdditive.lean`, not beside
     `Graph.X0Attains.of_additiveContract`: a new declaration there rebuilds that file's 12
     importers (`MainComponent/Contract.lean`, the coverage files, `Grade/Stable.lean`,
     `Grade/TheoremS.lean`, `Nonvacuity.lean`), the 42e precedent for deferring a fold. The
     `d = 3` proof keeps its inline copy.
  3. **The contraction is one build commit**: its spike is complete, the theorem with its
     corollary and the kernel lemma.
  4. **No 42f build edits `Grade/Configuration.lean` or `Grade/Carrier.lean`**: both builds are
     new files, and `contractConfigPolyGrade` lives in the new one. The `gradeSigma` /
     `pictureProj` fold stays deferred (design doc §3) to the first commit that edits either.

## Hand-off / next phase

The next concrete commit is the **first build**: `Pencil/Grade/Cut.lean` from
`scratch/42f/Cut.lean` (full docstrings, the root import in `CombinatorialRigidity.lean`), pinning
and greening `lem:pencil-d-lifting-restrict`, `thm:pencil-d-cut` and `thm:pencil-d-bridge`. Then
`Pencil/Grade/ContractAdditive.lean` from `scratch/42f/ContractAdditive.lean`, its three copied
lemmas dropped for `import …Grade.Cut`, greening `lem:pencil-contract-additive-kernel`,
`thm:pencil-d-contract-additive` and `cor:pencil-d-contract-rigid`. Then the close. So two builds,
where the option the PI chose estimated about 4–8 (the coordinator's estimate, design doc §1).
Each build adds its nodes' `\lean{}` and `\leanok` and runs the per-commit gates, among them
`scripts/check-docstring-labels.py` against its parent's report.

## Decisions made during this phase

- **The open** (the PI, 2026-10-30; verbatim in design doc §1): 42f opens as PD-STEPS's `-cut` and
  `-contract`, six nodes; `-short` and `-long` stay mapped by section, no letter minted.
- **The cut** (the PI, 2026-10-30; verbatim in design doc §1, superseding the PI's 42d "(a) Keep
  standalone", `notes/Phase42d.md`): the `Pᵈ` split-off and the open-ear step that assumes
  `def_d(G[V₁]) ≤ def_d(G)`, with `lem:pencil-d-polygon-ear`, deleted with their sections; PD-STEPS
  goes from 28 nodes to 25.
- **The pre-build recon** (spikes in `scratch/42f/`, all complete): no tuple restriction defined
  (the generic `Graph.liftingRestrict` at `α × Fin m`); two new files, so no landed file edited
  and the 42e fold stays deferred; the kernel lemma not extracted into the `d = 3` file (12
  importers); the contraction one build. The open's read held; two of its names route otherwise:
  the corollary takes `Graph.isX0Graph_induce_of_deficiency_eq_zero (n := 2)`, as
  `…_two_eq_zero` sits in `MainComponent/Contract.lean`, outside the imports, and the cut takes
  `Graph.deficiency_add_le_of_cutVertex`, as the open allowed.
