# Phase 42f — PD-STEPS: cut vertices, bridges and contraction in every dimension (work log)

**Status:** in progress, opened 2026-10-30 at the PI's word ("-cut + -contract (Recommended)",
design doc §1), a sub-phase of Phase 42 and the first of PD-STEPS. Forward mode, the Lean under
`/coordinate-phase`: the six red nodes of `blueprint/src/chapter/pencil-d.tex` in
`sec:pencil-d-cut` and `sec:pencil-d-contract` (Phase 40e/40f/40k in `Pᵈ`), on the `Pencil/Grade/`
carrier. The open's consistency read found every proof routing through the argument its statement
claims (*Consistency read at the open*). At the PI's word the open also cut three step nodes no
coverage step uses, leaving PD-STEPS 25 nodes. Next (*Hand-off*): the pre-build recon pinning the
six Lean signatures.

## Current state

**Next: the pre-build recon** (*Hand-off*). Opened; no Lean yet. The six targets, leaf-first:
`lem:pencil-d-lifting-restrict` and `lem:pencil-contract-additive-kernel` have every dependency
green; `thm:pencil-d-cut` and `thm:pencil-d-bridge` rest on the first;
`thm:pencil-d-contract-additive` on both; `cor:pencil-d-contract-rigid` on the theorem. The chapter
is the lemma index (forward mode). The rest of PD-STEPS, `-short` (12) and `-long` (7), stays mapped
by section in design doc §3, with no letter minted.

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

- [ ] **Pre-build recon**: exact Lean signatures for the six nodes, their files, and spikes of the
  two leaves and of the contraction's tuple machinery (*Blockers*).
- [ ] `lem:pencil-d-lifting-restrict`, a leaf.
- [ ] `lem:pencil-contract-additive-kernel`, a leaf.
- [ ] `thm:pencil-d-cut` and `thm:pencil-d-bridge`, on the restriction.
- [ ] `thm:pencil-d-contract-additive`, on both leaves; possibly two commits (*Blockers*).
- [ ] `cor:pencil-d-contract-rigid`, on the theorem.
- [ ] **Close** 42f, an intermediate sub-phase close (`PHASE-BOUNDARIES.md`).

## Blockers / open questions

- None blocking. For the recon:
  - The grade restriction: a tuple form of `Graph.liftingRestrict` (per column, or
    `if p.1 ∈ X then z p else 0`) and of `restrictPoly` on `MvPolynomial (α × Fin m) K`, and the
    file (a new `Grade/` file importing `MainComponent/Cut.lean`).
  - The kernel lemma's home: extracted beside `Graph.X0Attains.of_additiveContract`, which could
    then call it (an edit to a `P³` file, which rebuilds its dependents), or a new file importing
    `MainComponent/ContractCurve.lean`.
  - The contraction's size: tuples of unknowns `Fin m → α ⊕ (α × Fin 3) → K`, `ker M(0)^m` as a
    submodule (the fibre lemma takes any), one polynomial section per height (the precedent is
    `hsec` in `Graph.x0AttainsGrade_of_exists`), and a grade `contractConfigPoly`. One build commit
    or two.
  - 42e's deferral (design doc §3): a 42f commit that edits `Grade/Configuration.lean` or
    `Grade/Carrier.lean` carries the `gradeSigma` / `pictureProj` fold.

## Hand-off / next phase

The next concrete commit is the **pre-build recon** (a `recon-opus` dispatch, read-only or a
design-pass commit at the coordinator's choice): pin the exact Lean signatures of the six nodes
against the landed `Pencil/Grade/` API and Phase 40's `MainComponent/Cut.lean`, `Contract.lean`,
`ContractCurve.lean` and `ContractAdditive.lean`; spike the two leaves and the contraction's tuple
machinery under `lake lean`; settle the questions under *Blockers*; and record the signatures here.
Then build leaf-first, about 4–8 commits by the PI's estimate: `lem:pencil-d-lifting-restrict`, then
the cut and the bridge (together or apart), `lem:pencil-contract-additive-kernel`, the contraction
theorem, and its corollary. Each build adds its node's `\lean{}` and `\leanok`.

## Decisions made during this phase

- **The open** (the PI, 2026-10-30; verbatim in design doc §1): 42f opens as PD-STEPS's `-cut` and
  `-contract`, six nodes; `-short` and `-long` stay mapped by section, no letter minted.
- **The cut** (the PI, 2026-10-30; verbatim in design doc §1, superseding the PI's 42d "(a) Keep
  standalone", `notes/Phase42d.md`): the `Pᵈ` split-off and the open-ear step that assumes
  `def_d(G[V₁]) ≤ def_d(G)`, with `lem:pencil-d-polygon-ear`, deleted with their sections; PD-STEPS
  goes from 28 nodes to 25.
