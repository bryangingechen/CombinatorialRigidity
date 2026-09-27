# Phase 40f — PENCIL-X0 / CONTRACT-R: contraction at a `def₂`-rigid core (work log)

**Status:** in progress (opened design-first 2026-09-26). STEPS' second group (`notes/Phase40-design.md`
§3 STEPS). It lands the contraction step at a core of planar deficiency zero, (MC-59)(d) with
(MC-39): if `X₀(G/H)` attains, `X₀(G)` attains, for `H = G[W]` with `def₂(H) = 0` and `G/H` simple.
The build landed the whole step in one commit, and all twelve nodes are green. **Next: 40f's
close** — see *Hand-off*.

## Current state

**Built.** Twelve nodes, with statements from `ledger.py --brief '(MC-34)' … '(MC-39)' '(MC-59)'`
and Step MC12's construction, all green:
- eight in `main-component.tex` §`sec:main-component-contract`, whose closing remark keeps the
  unformalized parts;
- `def:pencil-weighted-lifting-system` in the same chapter's §`sec:main-component-carrier`;
- `lem:block-rank-contract` and `lem:rank-polynomial-proj-eval` in `rigidity-matrix.tex`;
- `lem:deficiency-zero-connected` in `deficiency.tex`.

**Headline axioms** (`#print axioms` under `import CombinatorialRigidity`, probe not retained):
`Graph.X0Attains.of_rigidContract` and every pinned declaration, the sibling's parent and the
mirror lemma: `[propext, Classical.choice, Quot.sound]`.

**The next concrete commit is 40f's close** (*Hand-off*).

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

All landed in the build (standard axioms). Pins in **bold**; the other names are helpers.

- [x] **Weighted lifting system** (`Carrier.lean`, after `Graph.finrank_ker_liftingMatrix`):
  **`Graph.weightedLiftingMatrix`**, `…_mulVec_eq_zero_iff` → `def:pencil-weighted-lifting-system`.
- [x] **0-dof connected** (`Deficiency.lean`, after `preconnected_of_isKDof_zero`):
  **`Graph.connected_of_isKDof_zero`**, **`Graph.two_le_degree_of_isKDof_zero`** →
  `lem:deficiency-zero-connected`.
- [x] **The sibling** (`CaseI.lean`, before its parent):
  **`PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking_set_proj_eval`**, with CaseI's own
  private `coord_linearMap_eq_matrix_mulVec`; the parent is its three-line corollary, statement
  unchanged → `lem:rank-polynomial-proj-eval`.
- [x] **Block coupling**: `Submodule.finrank_add_finrank_map_le_of_le_ker` in the mirror
  `Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`;
  **`PanelHingeFramework.finrank_span_rigidityRows_induce_add_map_extProj_le`** in `Coupling.lean`
  after `hingeRow_comp_extProj_eq_zero` → `lem:block-rank-contract`.
- [x] The rest in the new `Molecule/Pencil/MainComponent/Contract.lean` (root import after `Cut`):
  **`Graph.contractLiftingMatrix`**, **`contractPicture`**, **`contractHeight`** →
  `def:pencil-contract-lifting-system`; **`Graph.contractHeight_mem_liftingSpace`**,
  **`Graph.exists_contractHeight_eq`** → `lem:pencil-contract-lifting-kernel`;
  **`Graph.exists_core_plane`** → `lem:pencil-contract-core-plane`;
  **`Graph.finrank_ker_contractLiftingMatrix_zero_le`**,
  **`Graph.exists_mem_ker_contractLiftingMatrix_zero`** → `lem:pencil-contract-limit`;
  **`Graph.finrank_span_rigidityRows_induce_contractHeight`** → `lem:pencil-contract-core-rank`;
  **`PanelHingeFramework.exists_rankPolynomial_rigidContract_induce_proj`** →
  `lem:pencil-contract-degenerate-rank`; **`Graph.isX0Graph_induce_of_deficiency_two_eq_zero`**,
  **`Graph.isX0Graph_rigidContract_induce`**, **`Graph.twoEdgeConnected_rigidContract_induce`** →
  `lem:pencil-contract-standing`; **`Graph.X0Attains.of_rigidContract`** →
  `thm:pencil-x0-contract-rigid`.
- **Not 40f's, tracked elsewhere:** decision 2's `hatt` TODO (design doc §3 STEPS; also named in
  `Contract.lean`'s module docstring).

## Blockers / open questions

- None.

## Hand-off / next phase

**Next: 40f's close** — a sub-phase close (`PHASE-BOUNDARIES.md` *When this commit closes a
phase*, the sub-phase adaptations):
- advance the ROADMAP Status cell (40f ✓, name the next STEPS group) and compress §40f to a
  summary; mark CONTRACT-R closed in `notes/Phase40-design.md` §3 STEPS and in its opening roster;
- re-verify the headline axioms on the landed declarations (the build's list is in *Current
  state*), and sync `notes/MolecularConjecture.md`;
- the end-to-end re-read of §`sec:main-component-contract` and the exposition-ledger check
  (`notes/BlueprintExposition.md`); `thm:pencil-x0-contract-rigid` is a candidate;
- two files sit at the ~1500-line tripwire: `Carrier.lean` (1496 lines) and `Contract.lean`
  (1496). Both are sectioned; record a split plan, or its deferral, at the close.

**Then** the next STEPS group per the design doc's provisional grouping. At CONTRACT-A
(decision 4): `M(t)`, K1, K2, K4, the degenerate rank and the coupling are general, and the
core-plane, K3 and core-rank lemmas are specific to the flat core.

## Decisions made during this phase

- **2026-09-26 — opened design-first from one opus recon.** The coordinator re-ran its spike: exit 0,
  only the axioms line, and no `sorry`/`admit`/`axiom`/`maxHeartbeats`. It also traced by hand the
  recon's satisfiability instance: a triangle core on `{0,1,2}` in `G` = triangle plus the path
  `1–3–4–0`, whose `G/H` is a triangle.
- **2026-09-26 — the build: the spike transcribed, a few proofs shortened.**
  `Graph.connected_of_isKDof_zero` replaced `induce_connected_of_deficiency_two_eq_zero`, and the
  assembly reads the core's connectivity, simplicity and `h3` off
  `Graph.isX0Graph_induce_of_deficiency_two_eq_zero` (the spike's `h3` helper is gone).
  `collapseTo_mem_closedNbhd_rigidContract` is a corollary of `Graph.isLink_rigidContract_of_isLink`.
  One flexible `simp` the spike never showed became `simp only` (TACTICS-QUIRKS §55). The
  `rigidContract` defeq trap is TACTICS-QUIRKS §38 (*contraction-carrier variant*).
