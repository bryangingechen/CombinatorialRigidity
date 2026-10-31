# Phase 42e — PD-CARRIER: the setting and the flat rank in every dimension (work log)

**Status:** in progress, opened 2026-10-30 at the PI's word ("PD-CARRIER only (Recommended)",
design doc §1), a sub-phase of Phase 42 and the first layer formalizing 42d's proof. Forward mode,
the Lean under `/coordinate-phase`: the four red nodes of `blueprint/src/chapter/pencil-d.tex` in
`sec:pencil-d-induction` and `sec:pencil-d-flat` (Phase 40b–40d in `Pᵈ`), on 42b's carrier in
`Pencil/Grade/`. The open's consistency read found every proof routing through the argument its
statement claims (*Consistency read at the open*). Next (*Hand-off*): the pre-build recon pinning
the four Lean signatures.

## Current state

**Next: the pre-build recon** (*Hand-off*). Opened; no Lean yet. The four targets, leaf-first:
`lem:pencil-d-condition-linear` and `thm:pencil-d-flat-rank` have every dependency green;
`cor:pencil-d-flat-attains` rests on the flat rank, and `cor:pencil-d-jj-flat` on that corollary.
The chapter is the lemma index (forward mode). The other red nodes of the chapter map to PD-STEPS,
PD-COVERAGE, PD-REDUCTION and PD-HEAD by section in design doc §3 (*The red nodes by layer*), with
no letter minted.

## Architectural choices made up front

- **Scope** (the PI's, verbatim in design doc §1): PD-CARRIER only, the four nodes above.
  `rem:pencil-d-flat-class` is a remark, which the dependency graph does not draw (plastexdepgraph
  draws definitions, lemmas, propositions, theorems and corollaries; no remark in the blueprint
  carries a `\lean` pin), so it is not a target. Its claim checks (below), and nothing uses it.
- **Encoding** as 42b and 42c: `m = d − 2` heights at grade `k = m + 1`, `D = screwDim (m + 1)`,
  `def_d` is `G.deficiency (m + 2)` and `def_2` is `G.deficiency 2` (`notes/Phase42b.md`,
  `notes/Phase42c.md` *Architectural choices*). Attaining is `Graph.X0AttainsGrade K m`.

## Consistency read at the open

The red-node consistency gate (`PHASE-BOUNDARIES.md`): each node read in full against the landed
carrier (42b's and 42c's green nodes, `Pencil/Grade/`) and the `main-component.tex` node it
generalizes. Every Lean name below was opened at its declaration. No proof fails; no `\uses`
reaches a superseded node (`blueprint/lint.sh`, check 3).
- **`lem:pencil-d-condition-linear`** generalizes `lem:pencil-condition-linear` (40b), whose Lean
  is `Graph.IsAdmissiblePicture.mem_liftingSpace_iff_coplanar` and `.exists_smul_eq_interpolant`
  (`MainComponent/Configuration.lean`), through one normal (`pencilNormalOfPicture`,
  `finrank_toDualPerp_triple_eq`, both at `K⁴`). The proof routes through its claim: admissibility
  makes `π` (first, second, last coordinate) onto `K³` on the span `S`, so `dim S ≤ 3` makes `π`
  an isomorphism whose inverse `σ` gives the affine functions; conversely `σ_v` is injective with
  image `S`; the `n^i` are independent, and `dim Π_v^⊥ = d − 2`. The one-normal route does not
  generalize, as the proof says. Grade Lean already landed: `π` is the private `pictureProj`
  (`Grade/Configuration.lean`); the "if" half's bound is
  `finrank_span_pencilConfigPointGrade_closedNbhd_le`, whose map
  `c ↦ gradeMk (c 0) (c 1) (h_i ⬝ᵥ c) (c 2)` is `σ_v`; three independent points are
  `linearIndependent_pencilConfigPointGrade_of_linearIndependent_pencilPicturePoint`; `finrank_dotPerp`
  gives `Π_v^⊥`. Carrier: Lean's `Graph.liftingSpace` holds heights vanishing off `V(G)`, so the
  "in particular" takes that hypothesis per height, as the `d = 3` Lean's `hs` does; the chapter's
  heights live on `V(G)`, so no statement changes. Its consumers, `thm:pencil-d-open-ear-four` and
  `lem:pencil-d-planes-meet` (PD-STEPS), read `σ_a` and `σ_b` explicitly.
- **`thm:pencil-d-flat-rank`** generalizes `thm:pencil-flat-rank` (40c FLAT):
  `Graph.finrank_span_rigidityRows_ofNormals_flat`, `_flat_le` and `_flat_eq_iff`
  (`MainComponent/Flat.lean`), through the `K⁴` split `flatScrewEquiv`. The proof's first paragraph
  composes green Lean: the rank with no height, `3|V| − dim L(q)`
  (`Graph.finrank_span_rigidityRows_ofNormals_pencilPicturePoint`), plus `(D − 3)(|V| − 1)` for the
  zero heights (`Graph.finrank_span_rigidityRows_ofNormals_pencilConfigPointGrade_padHeights` at
  `m' = 0`), and the bound by `Graph.three_add_deficiency_le_finrank_liftingSpace`; the sum
  closes. Its second paragraph, the `d = 3` split in dimension `d` (a complement of `Λ²Ĥ` of
  dimension `D − 3`), also checks, but needs no Lean. To bridge: `pencilConfigPointGrade_eq_pencilPicturePoint`
  at `m = 0`, `padHeights m z₀ = 0` for `z₀ : α × Fin 0 → K`, and frameworks at `k := 0 + 1`
  against `k := 1` (the `_one` lemma's docstring records `rfl` exhausting heartbeats at `1 + 1`).
- **`cor:pencil-d-flat-attains`** generalizes `cor:pencil-flat-attains` (40c FLAT):
  `Graph.finrank_liftingSpace_eq_three_add_deficiency_three_iff` and
  `Graph.x0Attains_of_finrank_liftingSpace_le`. Its proof transcribes theirs: the exact rank (the
  `d = 3` `_flat_eq_iff` already takes any deficiency index), the lower bound with
  `Graph.Connected.deficiency_le_deficiency_of_le` at `2 ≤ m + 2`, then a main picture, the zero
  heights in `L(q)^{d−2}` and `Graph.x0AttainsGrade_of_exists` (`lem:pencil-d-x0-one-witness`).
- **`cor:pencil-d-jj-flat`** generalizes `cor:pencil-jj-flat` (40d BRIDGE):
  `Graph.x0Attains_of_deficiency_two_eq_three` (`MainComponent/Bridge.lean`). Its proof is Jackson
  and Jordán's equality, planar and unchanged (`Graph.exists_isMainPicture_finrank_liftingSpace_eq`),
  then `cor:pencil-d-flat-attains`. The remark after it gives a second route, dimension three and
  then `Graph.X0AttainsGrade.of_le`, by `rem:pencil-d-flat-class`, whose partition count holds; the
  node's own route is the first. Consumers: `cor:pencil-d-contract-rigid` and
  `thm:pencil-d-coverage`, later layers.

## Lemma checklist

- [ ] **Pre-build recon**: exact Lean target signatures for the four nodes against `Pencil/Grade/`
  and 40c's and 40d's Lean, with their files and the three bridges above spiked in scratch.
- [ ] `lem:pencil-d-condition-linear`, a leaf.
- [ ] `thm:pencil-d-flat-rank`, a leaf.
- [ ] `cor:pencil-d-flat-attains`, on the flat rank.
- [ ] `cor:pencil-d-jj-flat`, on the corollary.
- [ ] **Close** 42e, an intermediate sub-phase close (`PHASE-BOUNDARIES.md`).

## Blockers / open questions

- None blocking. For the recon: the form of `lem:pencil-d-condition-linear` that PD-STEPS reads
  (`σ_v` or `Π_v` exposed, not only the equivalence); whether the flat rank is stated at every `m`
  (it holds at `m = 0`) or at `1 ≤ m`, as the node says `d ≥ 3`; and the home of the new
  declarations (a new `Grade/` file, or `Grade/Configuration.lean`, where `pictureProj` is private).

## Hand-off / next phase

The next concrete commit is the **pre-build recon** of the PI's plan (a `recon-opus` dispatch,
read-only or a design-pass commit at the coordinator's choice): pin the exact Lean signatures of
the four nodes against the landed `Pencil/Grade/` API and Phase 40c's and 40d's Lean, spike the
three flat-rank bridges under `lake lean`, settle the three questions under *Blockers*, and record
the signatures here. Then build leaf-first, about 3–6 commits by the PI's estimate: likely
`thm:pencil-d-flat-rank` (all green below it), then `lem:pencil-d-condition-linear`, then the two
corollaries, which may land together. Each build flips its node's `\lean{}` and `\leanok`.

## Decisions made during this phase

- **The open** (the PI, 2026-10-30; verbatim in design doc §1): 42e opens as PD-CARRIER only; the
  other layers are mapped by section in design doc §3, no letters minted.
