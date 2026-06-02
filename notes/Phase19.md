# Phase 19 — `M(G̃)`, deficiency, `k`-dof graphs (work log)

**Status:** in progress (first Lean node `def:matroid-MG` landed).

This phase is stratum 3 of the molecular-conjecture program (KT §2.5,
§3). The program-level plan, reuse map, citations, and risk register
live in `notes/MolecularConjecture.md` *Phase 19*; read that first.
This file carries Phase-19-local state, the lemma checklist, decisions,
and hand-off. The forward-mode dep-graph / lemma index is the new
blueprint chapter `blueprint/src/chapter/deficiency.tex`
(`sec:molecular-deficiency`); its red nodes are the live to-do list.

## Current state

`Molecular/Deficiency.lean` created; the first forward-mode node
`def:matroid-MG` is green. It defines `Graph.mulTilde G n = (D−1)·G`
(`= G.edgeMultiply (bodyHingeMult n)`, edge type `β × Fin (D−1)`) and
`Graph.matroidMG G n` as the `D`-fold cycle-matroid union of `G̃`
restricted to `E(G̃)`, with `D = bodyBarDim n`. The **boundary-regime
cleanliness check** `matroidMG_indep_iff` confirms (risk #2) that
`M(G̃).Indep E' ↔ E' ⊆ E(G̃) ∧ (G̃ ↾ E').IsSparse D D` — the boundary
regime `ℓ = 2k = D` is clean and routes through Phase 13's
`unionPow_cycleMatroid_indep_iff_isSparse_restrict` (+ Tutte–Nash-Williams),
**not** `CountMatroid.lean` (`ℓ < 2k`).

Next concrete step: `def:D-deficiency` — `def_G̃(P) = D(|P|−1) −
(D−1)·d_G(P)` over partitions `P` of `V(G)`, and `def(G̃) = maxₚ`.
Then `def:k-dof`, `def:rigid-subgraph`, the structural lemmas
(KT 3.1/3.3/3.4), and the bridge `thm:def-eq-corank`.

## Architectural choices made up front

- **`M(G̃)` via the union construction, NOT `CountMatroid.lean`.** The
  matroid `M(G̃)` is the `(D,D)` count matroid at the boundary regime
  `ℓ = 2k = D`. `CountMatroid.lean` is for the matroidal regime
  `ℓ < 2k` and does not cover `ℓ = 2k`. Route through the `D`-fold
  graphic-matroid union of Phases 13/14 (`unionPow_cycleMatroid`) +
  Tutte–Nash-Williams (`tutte_nash_williams`) on `(D−1)·G`. (Risk #2
  in `notes/MolecularConjecture.md`.)
- **New file `Molecular/Deficiency.lean`.** Phase 19 Lean does not
  append to `RigidityMatrix.lean` (one `.lean`/`.tex` per molecular
  phase, established by the post-Phase-18 cleanup-round split).
- **`def(G̃) = corank M(G̃)` is the project framing of JJ09 Thm 6.1 /
  Cor 6.2** (Jackson–Jordán 2009, European J. Combin. 31, 574–588). The
  rank-deficiency identity `|B| + def(G̃) = D(|V|−1)`. Decide the
  prove-vs-hypothesize boundary for the JJ09 generic-rank half when the
  `prop:rigidity-matrix-prop11` node lands (risk #4); the conjecture
  (Thm 5.6) needs only the upper-bound half, which Phase 16's
  `edgeMultiply_isSparse_iff` may already supply.

## Lemma checklist

Forward-mode: the authoritative node list is `deficiency.tex`
(`sec:molecular-deficiency`). Tracked here for hand-off convenience;
flip to `[x]` as each lands `\leanok` in the chapter.

- [x] `def:matroid-MG` — `M(G̃)`, the `D`-fold graphic union on
  `(D−1)·G` at the boundary `ℓ = 2k = D`. (`Graph.matroidMG` +
  boundary-regime cleanliness `Graph.matroidMG_indep_iff`.)
- [ ] `def:D-deficiency` — `def_G̃(P) = D(|P|−1) − (D−1)·d_G(P)`;
  `def(G̃) = maxₚ def_G̃(P)`.
- [ ] `def:k-dof` — `k`-dof / `0`-dof (= body-hinge rigid) / minimal
  `k`-dof (every base of `M(G̃)` meets every edge-fiber `ẽ`).
- [ ] `def:rigid-subgraph` — rigid + proper rigid subgraph; circuits;
  2-edge-connectivity.
- [ ] `thm:def-eq-corank` — the def = corank bridge (JJ09 Thm 6.1 /
  Cor 6.2): `|B| + def(G̃) = D(|V|−1)`.
- [ ] `lem:two-edge-conn` — KT Lemma 3.1 (2-edge-connectivity).
- [ ] `lem:subgraph-minimality` — KT Lemma 3.3 (subgraph minimality
  via restriction).
- [ ] `lem:circuit-rigid` — KT Lemma 3.4 (circuit ⇒ rigid subgraph).
- [ ] `prop:rigidity-matrix-prop11` — KT Prop 1.1 reconciliation
  (**inherited from Phase 18**; node lives in
  `rigidity-matrix.tex`, flips green once `thm:def-eq-corank` lands).
- (off the Thm-4.9 critical path; schedule late or with Phase 21):
  KT Lemma 3.2 (not 3-edge-connected), Lemma 3.6 (partition
  decomposition — needed only by Case 6.1, schedule with Phase 21),
  Lemma 3.5 (rigid-subgraph contraction preserves minimality — Case I
  engine; may land here or early Phase 20).
- New graph ops (splitting-off, edge-splitting, removal, contraction)
  may start here or in Phase 20.

## Decisions made during this phase

- **`G̃` named `mulTilde`, a thin wrapper over `edgeMultiply`.**
  `Graph.mulTilde G n := G.edgeMultiply (bodyHingeMult n)` fixes the
  multiplication factor at `D − 1 = bodyHingeMult n` so the chapter
  reads `G̃` directly without re-spelling the body-hinge factor at each
  node. `matroidMG` and downstream nodes are stated over `mulTilde`.
- **`M(G̃)` via the union-then-restrict shape of Phase 14's
  `kFrameMatroid`.** `matroidMG = (Union (fun _ : Fin D ↦
  G̃.cycleMatroid)) ↾ E(G̃)`. The `↾ E(G̃)` is forced the same way as
  Phase 14: `Matroid.Union` has ground `univ`, so without it every
  non-edge is a loop. Boundary regime confirmed clean (risk #2) by
  `matroidMG_indep_iff` — no friction; it is a one-`rw`
  (`Matroid.restrict_indep_iff`) reduction to Phase 13's
  `unionPow_cycleMatroid_indep_iff_isSparse_restrict`.

## Blockers / open questions

- ~~**Boundary regime `ℓ = 2k = D`** (risk #2)~~: **resolved** by
  `matroidMG_indep_iff` — the `D`-fold cycle-matroid union +
  Tutte–Nash-Williams covers the boundary regime cleanly; no
  `CountMatroid.lean` (`ℓ < 2k`) involvement.
- **Externals: prove vs hypothesize** (risk #4): JJ09 Thm 6.1 /
  Cor 6.2 generic-rank bridge — re-confirm per node whether to
  formalize or take as a hypothesis. The conjecture needs only the
  upper-bound half.

## Hand-off / next phase

`def:matroid-MG` is green (`Graph.matroidMG` + the boundary-regime
cleanliness check `matroidMG_indep_iff`), in `Molecular/Deficiency.lean`.
The next concrete commit is `def:D-deficiency` in the same file:
`def_G̃(P) = D(|P|−1) − (D−1)·d_G(P)` for a partition `P` of `V(G)`
(`d_G(P)` = edges of `G` crossing `P`), and `def(G̃) = maxₚ def_G̃(P)`.
Phrase additively to avoid `ℕ`-subtraction (per ROADMAP conventions);
decide how to model partitions (likely `Setoid`/`Finpartition` of
`V(G)`). Phase 20 (combinatorial induction → Theorem 4.9) is unblocked
once `M(G̃)`, deficiency, and the def = corank bridge are green.
