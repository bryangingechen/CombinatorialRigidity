# Phase 40f — PENCIL-X0 / CONTRACT-R: contraction at a `def₂`-rigid core (work log)

**Status:** in progress (opened design-first 2026-09-26). STEPS' second group (`notes/Phase40-design.md`
§3 STEPS). It lands the contraction step at a core of planar deficiency zero, (MC-59)(d) with
(MC-39): if `X₀(G/H)` attains, `X₀(G)` attains, for `H = G[W]` with `def₂(H) = 0` and `G/H` simple.
The design recon's spike proves the whole step sorry-free, so the build is one commit, a
transcription with the placement moves. **Next: the build commit** — see *Hand-off*.

## Current state

**Opened.** Twelve red nodes, with statements from `ledger.py --brief '(MC-34)' … '(MC-39)'
'(MC-59)'` and Step MC12's construction:
- eight in `main-component.tex` §`sec:main-component-contract` (before the final stub), plus its
  remark on the unformalized parts;
- `def:pencil-weighted-lifting-system` in the same chapter's §`sec:main-component-carrier`;
- `lem:block-rank-contract` and `lem:rank-polynomial-proj-eval` in `rigidity-matrix.tex`;
- `lem:deficiency-zero-connected` in `deficiency.tex`.

No Lean has landed. **The next concrete commit is the build**: `scratch/S40fContract.lean`
transcribed per the placement decisions, turning all twelve nodes green.

## Architectural choices made up front

- **The route** (the recon's verdict, compiled at `3caa99c8`; `notes/Phase40-design.md` §3 STEPS).
  - One ambient picture `q`, generic for `G/H` and `H` and main for `G`.
  - The curve `q_c(t) = (1−t)q_r + t·q_c` on `W` collapses the core at `r`'s picture point, and
    `q(1) = q`.
  - The rescaled lifting system `M(t)` gives heights in `L_G(q(t))`, onto at `t ≠ 0`. At `t = 0`,
    `dim ker M(0) ≤ dim L_{G/H}(q)`, and the flat-core extension of any `z ∈ L_{G/H}(q)` with
    `z_r = 0` is a kernel vector.
  - The no-jump chain: Jackson–Jordán at `G/H`, `rigidContract_deficiency_eq` at `n = 2`, and
    (MC-4)(b) at `G`.
  - Cramer's section along `t`; the core's rank is its flat rank; the degenerate placement is
    nonzero for the new projected rank polynomial; the block coupling adds the ranks; the step ends
    at `Graph.x0Attains_of_exists`.
- **Unlike the step contract**, the picture moves along `q(t)`, and `exists_mem_eval_ne_zero₂` is
  not used; one product polynomial in `t` picks the parameter. No collineation lemma is needed for
  the core's rank.
- **The PI's decisions, verbatim** (2026-09-26; also `notes/pencil/adjudications.md`):

  ```adjudication
  PI decisions, 2026-09-26, on the CONTRACT-R design recon's verdict (verbatim answers to the coordinator's questions):
  1. Placement — "Where should the new general pieces live? There are four: the projected rank-polynomial sibling, the block coupling, the weighted lifting matrix, and the laws that def₂ = 0 implies connected and degree ≥ 2.": "Convention everywhere (Recommended)" — each goes beside its definition. The sibling becomes an additive successor in CaseI.lean, with its parent re-proved as a 3-line corollary. The coupling goes in Coupling.lean beside extProj, with the pure linear-algebra lemma in the Mathlib mirror. weightedLiftingMatrix goes in Carrier.lean, and the def₂ = 0 laws are general IsKDof laws in Deficiency.lean.
  2. Hypothesis shape — "What shape should the 'G/H is simple' hypothesis have?": "Let's build this as spiked but leave a TODO for readability / understandability later".
  3. Side claims — "Include (MC-39)'s side claims (H and G/H satisfy (H), G/H is 2-edge-connected, and |V(G/H)| = |V| − |W| + 1) in 40f?": "Include (Recommended)".
  4. CONTRACT-A — "When should the shared part of the assembly be factored out?": "Later, at CONTRACT-A (Recommended)".
  ```
- **Decision 8 (the coordinator's):** a fresh opus builder lands the spike as **one build commit**,
  as in 40e build 1. The rung is opus because of the `CaseI.lean` and `Coupling.lean` edits (the
  fragile zone). It is not sliced.
- **Decision 2's TODO** is tracked in `notes/Phase40-design.md` §3 STEPS (revisit `hatt` as
  `(G/H).Simple`); not a 40f close gate.

## Lemma checklist

Planned names from the spike (exit 0, no warnings, standard axioms). Pins in **bold**; the other
names are helpers, unpinned.

- [ ] **Weighted lifting system** (`Carrier.lean`, beside `Graph.liftingMatrix`):
  **`Graph.weightedLiftingMatrix`**, `…_mulVec_eq_zero_iff` → `def:pencil-weighted-lifting-system`.
- [ ] **0-dof connected** (`Deficiency.lean`, after `preconnected_of_isKDof_zero`): new
  **`Graph.connected_of_isKDof_zero`** (any `n`, `1 ≤ bodyBarDim n`, `V(G)` nonempty; it
  replaces the spike's `Graph.induce_connected_of_deficiency_two_eq_zero`), with the landed and so
  far unpinned **`Graph.two_le_degree_of_isKDof_zero`** → `lem:deficiency-zero-connected`.
- [ ] **The sibling** (`CaseI.lean`, before its parent):
  **`PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking_set_proj_eval`** (conclusion
  `MvPolynomial.eval q₀ Qc ≠ 0 ∧ …`). The parent `…_set_proj` is re-proved from it in 3 lines;
  CaseI's own private `coord_linearMap_eq_matrix_mulVec` replaces the spike's copy →
  `lem:rank-polynomial-proj-eval`.
- [ ] **Block coupling**: `finrank_add_finrank_map_le_of_le_ker` into the Mathlib mirror
  `Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean` (namespace `Submodule`, beside
  `finrank_sup_of_inf_eq_bot`); **`PanelHingeFramework.finrank_span_rigidityRows_induce_add_map_extProj_le`**
  in `Coupling.lean` beside `extProj` → `lem:block-rank-contract`.
- The rest in a new `Molecule/Pencil/MainComponent/Contract.lean`:
  - [ ] **`Graph.contractLiftingMatrix`**, **`contractPicture`**, **`contractHeight`**;
    `Graph.coreNbhd`, `Graph.contractWeightAt`, `Graph.contractWeight`, the `eval` and unfolding
    lemmas → `def:pencil-contract-lifting-system`.
  - [ ] **`Graph.contractHeight_mem_liftingSpace`**, **`Graph.exists_contractHeight_eq`**,
    `Graph.finrank_liftingSpace_le_finrank_ker_contractLiftingMatrix` →
    `lem:pencil-contract-lifting-kernel`.
  - [ ] **`Graph.exists_core_plane`**; the plane helpers (`eq_zero_of_dotProduct_pencilPicturePoint`,
    `Graph.IsAdmissiblePicture.eq_zero_of_forall_closedNbhd`, `…eq_of_forall_closedNbhd`,
    `Graph.closedNbhd_induce_subset`) → `lem:pencil-contract-core-plane`.
  - [ ] **`Graph.finrank_ker_contractLiftingMatrix_zero_le`**,
    **`Graph.exists_mem_ker_contractLiftingMatrix_zero`**; `contractLimitMap` and its two lemmas;
    the `collapseTo` helpers → `lem:pencil-contract-limit`.
  - [ ] **`Graph.finrank_span_rigidityRows_induce_contractHeight`** →
    `lem:pencil-contract-core-rank`.
  - [ ] **`PanelHingeFramework.exists_rankPolynomial_rigidContract_induce_proj`** →
    `lem:pencil-contract-degenerate-rank`.
  - [ ] **`Graph.isX0Graph_induce_of_deficiency_two_eq_zero`**,
    **`Graph.isX0Graph_rigidContract_induce`**, **`Graph.twoEdgeConnected_rigidContract_induce`**;
    `Graph.rigidContract_induce_simple` (the appendix's compiled lemma),
    `Graph.three_le_ncard_closedNbhd_rigidContract`, `Graph.connected_rigidContract_induce`, the
    closed-neighbourhood and vertex-set helpers of `G/H`, and the landed
    `Graph.rigidContract_vertexSet_ncard` → `lem:pencil-contract-standing`.
  - [ ] **`Graph.X0Attains.of_rigidContract`**; the curve polynomials `contractPicturePoly`,
    `contractConfigPoly` and their `eval` lemmas, `contractPicture_one` →
    `thm:pencil-x0-contract-rigid`.
- **Not 40f's, tracked elsewhere:** decision 2's `hatt` TODO (design doc §3 STEPS).

## Blockers / open questions

- None. The spike compiles the whole step. What remains is transcription plus the placement moves.

## Hand-off / next phase

**Next: the build — land `scratch/S40fContract.lean` per the placement decisions (fresh opus
builder).** The spike is untracked in `scratch/` and stays untracked until the build lands; the
build's commit removes `scratch/`. `S40fContract.lean` is generated by `python3 scratch/cat.py` from
`S40fM.lean` (the lifting system), `S40fR.lean` (the rank side) and `S40fA.lean` (the core's rank,
the standing facts, the assembly). The re-run command is `python3 scratch/cat.py && lake env lean
scratch/S40fContract.lean`: exit 0, and the only output is the axioms line. Chores before landing:
- **Placement** per the checklist, which edits `Carrier.lean`, `Deficiency.lean`, `CaseI.lean`,
  `Coupling.lean` and the mirror file. That rebuilds most of the tree, and `CaseI`/`Coupling` are
  the fragile zone.
- **The new file** `Molecule/Pencil/MainComponent/Contract.lean` imports `…MainComponent.Cut`,
  with the root import after `Cut`. Keep the `open scoped` lines outside the namespace (inside it,
  `Matrix` is ambiguous).
- **Docstrings**: a module docstring listing the statements (the `Cut.lean` pattern), and one per
  declaration.
- **Long lines**: judge by `lake lint`, not `awk` (TACTICS-QUIRKS §55).
- **The two fragile-zone traps the spike hit**, both kept in its proofs:
  - `exact panelRow_collapseTo_comp_extProj_dualMap …` against a framework over
    `G.rigidContract (G.induce W) r` times out at `isDefEq`. Rewrite `rigidContract` to
    `(G.deleteEdges E(G.induce W)).map (collapseTo r W)` and `V(G.induce W)` to `W`, both by `rfl`,
    before using it.
  - `V(G).ncard - W.ncard + 1` does not parse (TACTICS-QUIRKS §48); keep the parentheses.
- **Pin and flip** the twelve nodes, and record the headline axioms here. Gates: `lake build`,
  `lake lint`, `blueprint/verify.sh`, `blueprint/lint.sh`, `notes/check-phase-note.py`.

**Then 40f's close.** At CONTRACT-A (decision 4): `M(t)`, K1, K2, K4, the degenerate rank and the
coupling are general, and the core-plane, K3 and core-rank lemmas are specific to the flat core.

## Decisions made during this phase

- **2026-09-26 — opened design-first from one opus recon.** The coordinator re-ran its spike: exit 0,
  only the axioms line, and no `sorry`/`admit`/`axiom`/`maxHeartbeats`. It also traced by hand the
  recon's satisfiability instance: a triangle core on `{0,1,2}` in `G` = triangle plus the path
  `1–3–4–0`, whose `G/H` is a triangle.
