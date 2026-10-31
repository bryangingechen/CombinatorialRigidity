# Phase 42e — PD-CARRIER: the setting and the flat rank in every dimension (work log)

**Status:** in progress, opened 2026-10-30 at the PI's word ("PD-CARRIER only (Recommended)",
design doc §1), a sub-phase of Phase 42 and the first layer formalizing 42d's proof. Forward mode,
the Lean under `/coordinate-phase`: the four red nodes of `blueprint/src/chapter/pencil-d.tex` in
`sec:pencil-d-induction` and `sec:pencil-d-flat` (Phase 40b–40d in `Pᵈ`), on 42b's carrier in
`Pencil/Grade/`. The pre-build recon pinned all four Lean signatures and spiked each with no
`sorry` (*Lemma checklist*). Next (*Hand-off*): land `Pencil/Grade/Flat.lean`, the flat rank and
its two corollaries.

## Current state

**Next: land `Pencil/Grade/Flat.lean`** (*Hand-off*). The pre-build recon pinned the Lean of all
four nodes and checked it under `lake lean`: no `sorry`, no warning, `#lint` clean (15 linters),
and `scripts/check-docstring-labels.py` at 0 findings on a copy of the tree carrying the pins
below. The two spikes are land-ready, with header and docstrings, in the gitignored
`scratch/42e/`: `FlatRank.lean` (three nodes, to become `Grade/Flat.lean`) and
`ConditionLinear.lean` (one node, to become `Grade/ConditionLinear.lean`). If they are gone, the
signatures and routes under *Lemma checklist* rebuild them. Both are new files: no landed Lean
file changes. The chapter is the lemma index (forward mode). The other red nodes of the chapter
map to PD-STEPS, PD-COVERAGE, PD-REDUCTION and PD-HEAD by section in design doc §3 (*The red
nodes by layer*), with no letter minted.

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
  dimension `D − 3`), also checks, but needs no Lean. Three bridges, all holding (the recon,
  *Decisions made*): `pencilConfigPointGrade_eq_pencilPicturePoint` at `m = 0`,
  `padHeights m z₀ = 0` for `z₀ : α × Fin 0 → K`, and frameworks at `k := 0 + 1` against `k := 1`
  (the `_one` lemma's docstring records `rfl` exhausting heartbeats at `1 + 1`).
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

Shorthand, exact by substitution: `hends` is
`(hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2)`, and `rk(q, z)` is the rank
`Graph.X0AttainsGrade` reads,
`(Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := m + 1) G ends
(fun p => pencilConfigPointGrade q z p.1 p.2)).toBodyHinge.rigidityRows) : ℤ)`; `|V|` is
`(V(G).ncard : ℤ)` and `finrank L(q)` is `(Module.finrank K (G.liftingSpace q) : ℤ)`. Every
declaration is in `namespace CombinatorialRigidity.Molecular`, with `variable {K : Type*} [Field K]
{α β : Type*} {m : ℕ}`, under `@[expose] public section`; `Graph.` names are `_root_.Graph.…`.

- [x] **Pre-build recon** (this commit): the signatures below, all spiked; the three bridges hold
  (*Decisions made*).
- [ ] `thm:pencil-d-flat-rank`, in the new `Pencil/Grade/Flat.lean` (imports `Grade.ZeroHeights`
  and `MainComponent.Bridge`; nothing of `Grade/` imports `Flat.lean` or `Bridge.lean` today).
  Pin `Graph.finrank_span_rigidityRows_ofNormals_flat_grade`, `…_flat_le_grade`,
  `…_flat_eq_iff_grade`. With `[Finite α] (hG : G.Connected) {q} (hq : G.IsAdmissiblePicture q)
  {ends} hends`, at `z = (0 : α × Fin m → K)`:
  `_flat_grade`: `rk(q, 0) = screwDim (m + 1) * ((V(G).ncard : ℤ) - 1) + 3 - finrank L(q)`;
  `_flat_le_grade` (adds `[Finite β]`): `rk(q, 0) ≤ screwDim (m + 1) * (|V| - 1) - G.deficiency 2`;
  `_flat_eq_iff_grade (n : ℕ)`: `rk(q, 0) = screwDim (m + 1) * (|V| - 1) - G.deficiency n ↔
  finrank L(q) = 3 + G.deficiency n`. Route: `…_pencilConfigPointGrade_padHeights` at `m' = 0`,
  `z = 0 : α × Fin 0 → K`; rewrite `padHeights m 0 = 0` (`funext p; simp [padHeights]`) and the
  normals by `pencilConfigPointGrade_eq_pencilPicturePoint` (a `funext` `have`, as the `_one`
  lemma does); then `rw [Graph.finrank_span_rigidityRows_ofNormals_pencilPicturePoint hq hends]`
  matches the `k := 0 + 1` term with no cast; `simp only [zero_add, screwDim_one]`, `push_cast`,
  `ring`. The bound and the iff: `Graph.three_add_deficiency_le_finrank_liftingSpace`, `linarith`.
- [ ] `cor:pencil-d-flat-attains`, in `Grade/Flat.lean`. Pin `…_flat_eq_iff_grade` (its first
  equivalence, at `n = m + 2`), `Graph.finrank_liftingSpace_eq_three_add_deficiency_iff`,
  `Graph.x0AttainsGrade_of_finrank_liftingSpace_le`. The iff, with `[Finite α] [Finite β] hG hq
  {n : ℕ} (hn : 2 ≤ n)`: `finrank L(q) = 3 + G.deficiency n ↔ finrank L(q) = 3 + G.deficiency 2 ∧
  G.deficiency 2 = G.deficiency n`. The attaining, with `[Finite α] [Finite β] hG hq
  (hL : finrank L(q) ≤ 3 + G.deficiency (m + 2))`: `G.X0AttainsGrade K m`. Route: the `d = 3`
  proofs (`MainComponent/Flat.lean`) with `Graph.Connected.deficiency_le_deficiency_of_le` at
  `2 ≤ m + 2`, then `Graph.x0AttainsGrade_of_exists hV G.endsOf hends hmain
  (G.liftingSpaceGrade q m).zero_mem` and `_flat_grade`.
- [ ] `cor:pencil-d-jj-flat`, in `Grade/Flat.lean`. Pin `Graph.x0AttainsGrade_of_deficiency_two_eq`:
  `[Infinite K] [Finite α] [Finite β] hG (hSimple : G.Simple)
  (h3 : ∀ v ∈ V(G), 3 ≤ (G.closedNbhd v).ncard) (hdef : G.deficiency 2 = G.deficiency (m + 2)) :
  G.X0AttainsGrade K m`. Route: `Graph.exists_isMainPicture_finrank_liftingSpace_eq`, then the
  attaining corollary.
- [ ] `lem:pencil-d-condition-linear`, in the new `Pencil/Grade/ConditionLinear.lean` (imports
  `Grade.Configuration`; `pictureProj` stays private there). Pin `gradeSigma`, `gradeSigmaPerp`,
  `dotPerp_range_gradeSigma` (all `CombinatorialRigidity.Molecular.`),
  `Graph.IsAdmissiblePicture.finrank_span_pencilConfigPointGrade_closedNbhd_le_iff`,
  `…span_pencilConfigPointGrade_closedNbhd_eq_range`,
  `…mem_liftingSpaceGrade_iff_finrank_span_closedNbhd_le` (a bare-label lead unpinned is a
  docstring-label finding). Definitions, for `h : Fin m → Fin 3 → K`: `gradeSigma h :
  (Fin 3 → K) →ₗ[K] (Fin (m + 1 + 2) → K)`, `c ↦ gradeMk (c 0) (c 1) (fun i => h i ⬝ᵥ c) (c 2)`
  (`σ_v`; `gradeSigma_apply` is `rfl`); `gradeSigmaPerp h i := gradeMk (h i 0) (h i 1)
  (-Pi.single i 1) (h i 2)` (`n^i`). Lemmas: `gradeSigma_injective`, `finrank_range_gradeSigma`
  (`= 3`), `gradeSigmaPerp_dotProduct_gradeMk` (`= h i 0 * x + h i 1 * y - u i + h i 2 * w`),
  `linearIndependent_gradeSigmaPerp`, `dotPerp_range_gradeSigma : dotPerp (range (gradeSigma h)) =
  span K (Set.range (gradeSigmaPerp h))`, `pencilConfigPointGrade_eq_gradeSigma_iff q z h w :
  pencilConfigPointGrade q z w = gradeSigma h (pencilPicturePoint q w) ↔ ∀ i, z (w, i) = h i ⬝ᵥ
  pencilPicturePoint q w`. With `(hq : G.IsAdmissiblePicture q) (hv : v ∈ V(G))` and
  `hh : ∀ i, ∀ w ∈ G.closedNbhd v, z (w, i) = h i ⬝ᵥ pencilPicturePoint q w`:
  `_eq_range hq hv hh : span K (pencilConfigPointGrade q z '' G.closedNbhd v) =
  range (gradeSigma h)`; `_le_iff hq z hv : finrank (that span) ≤ 3 ↔ ∃ h, hh`; and with
  `(hs : ∀ i, ∀ w ∉ V(G), z (w, i) = 0)`, `_le hq hs : z ∈ G.liftingSpaceGrade q m ↔ ∀ v ∈ V(G),
  finrank (that span) ≤ 3`. Route of the "only if": the local projection
  `LinearMap.funLeft K K ![0, 1, Fin.last (m + 2)]` restricted to the span is onto `K³` (three
  admissible points, `LinearIndependent.span_eq_top_of_card_eq_finrank`), so bijective
  (`LinearMap.injective_iff_surjective_of_finrank_eq_finrank`); the height coordinates of its
  inverse are linear forms, `h i ⬝ᵥ ·` by `LinearMap.pi_apply_eq_sum_univ`. Its proof may add
  `\uses{lem:pencil-d-config-realization}` (an edge, not a statement change): the Lean calls
  `linearIndependent_pencilConfigPointGrade_of_linearIndependent_pencilPicturePoint`.
- [ ] **Close** 42e, an intermediate sub-phase close (`PHASE-BOUNDARIES.md`). Its organization
  review weighs one duplication the new file leaves: `gradeSigma` is the inline map of
  `finrank_span_pencilConfigPointGrade_closedNbhd_le` and its projection `pictureProj`'s, both in
  `Grade/Configuration.lean`; folding them means moving `gradeSigma` beside `gradeMk` in
  `Grade/Carrier.lean`, which rebuilds the `Grade/` stack.

## Blockers / open questions

- None. The recon settled the open's three questions (*Decisions made*).

## Hand-off / next phase

The next concrete commit lands **`CombinatorialRigidity/Molecular/Molecule/Pencil/Grade/Flat.lean`**
from `scratch/42e/FlatRank.lean` as it stands (or rebuilt from *Lemma checklist*), adds its
`public import` to `CombinatorialRigidity.lean`, and flips `thm:pencil-d-flat-rank`,
`cor:pencil-d-flat-attains` and `cor:pencil-d-jj-flat` with the pins listed there (`\lean{}` and
`\leanok` on statement and proof). One session's work, a transcription: no landed Lean file
changes, so nothing rebuilds but the new module and the root. It touches neither the ScrewSpace
carrier nor `Molecular/RigidityMatrix/`, nor any file whose PD-STABLE deferral fires on an edit
(design doc §3). The honesty gate finds no laundered hypothesis: each one is the node's own. Then
`Grade/ConditionLinear.lean` the same way (one node), then the close; the two lands are
independent, and may go in either order or together.

## Decisions made during this phase

- **The pre-build recon** (2026-10-30; spikes in `scratch/42e/`): the open's three questions.
  (1) PD-STEPS reads `σ_v` and `Π_v` exposed: `def:pencil-d-ear-data` takes maps keeping the
  first, second and last coordinate, and `lem:pencil-d-planes-meet` reads `σ_a`'s height forms, so
  `σ_h` is a `def` (`gradeSigma`) and `Π_v` its `range`, beside the equivalence. (2) Every `m`, no
  `1 ≤ m`: no proof uses `d ≥ 3`, and `m = 0` is the plane (as `Graph.X0AttainsGrade.of_le` takes
  any `m' ≤ m`). (3) Two new `Grade/` files: the "only if" half projects locally, so `pictureProj`
  stays private. The three bridges hold: `rw` matches `k := 0 + 1` against `k := 1` once the
  normals are rewritten.
- **The open** (the PI, 2026-10-30; verbatim in design doc §1): 42e opens as PD-CARRIER only; the
  other layers are mapped by section in design doc §3, no letters minted.
