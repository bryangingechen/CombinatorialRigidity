# Phase 19 — `M(G̃)`, deficiency, `k`-dof graphs (work log)

**Status:** in progress (opened; no Lean landed yet).

This phase is stratum 3 of the molecular-conjecture program (KT §2.5,
§3). The program-level plan, reuse map, citations, and risk register
live in `notes/MolecularConjecture.md` *Phase 19*; read that first.
This file carries Phase-19-local state, the lemma checklist, decisions,
and hand-off. The forward-mode dep-graph / lemma index is the new
blueprint chapter `blueprint/src/chapter/deficiency.tex`
(`sec:molecular-deficiency`); its red nodes are the live to-do list.

## Current state

Phase opened: `notes/Phase19.md` created, `deficiency.tex` added with
the §2.5–§3 red dep-graph nodes, ROADMAP / README / `home_page` /
`intro.tex` status surfaces synced to *in progress*. **No Lean has
landed yet** — the Lean for this phase lives in a new
`Molecular/Deficiency.lean` (per the one-`.tex`-per-phase /
one-`.lean`-per-phase convention; not appended to `RigidityMatrix.lean`).

Next concrete step: formalize the leaf-most red node in
`deficiency.tex` — the matroid `M(G̃)` itself, as the `D`-fold graphic
union of Phase 13/14 on `(D−1)·G` at the boundary regime `ℓ = 2k = D`.
Confirm the boundary regime is clean before relying on it (risk #2):
`CountMatroid.lean` is built for `ℓ < 2k` and will *not* cover this —
route through `unionPow_cycleMatroid` + `tutte_nash_williams`.

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

- [ ] `def:matroid-MG` — `M(G̃)`, the `D`-fold graphic union on
  `(D−1)·G` at the boundary `ℓ = 2k = D`.
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

_(none yet; phase just opened)_

## Blockers / open questions

- **Boundary regime `ℓ = 2k = D`** (risk #2): confirm the project's
  union/tree-packing covers it before relying on it; do NOT assume
  `CountMatroid.lean` (`ℓ < 2k`) applies. First Lean node should
  validate this.
- **Externals: prove vs hypothesize** (risk #4): JJ09 Thm 6.1 /
  Cor 6.2 generic-rank bridge — re-confirm per node whether to
  formalize or take as a hypothesis. The conjecture needs only the
  upper-bound half.

## Hand-off / next phase

Phase just opened. The next concrete commit is the first forward-mode
Lean node: formalize `M(G̃)` (`def:matroid-MG`) in a new
`Molecular/Deficiency.lean` as the `D`-fold graphic union on `(D−1)·G`
(`unionPow_cycleMatroid` + `tutte_nash_williams`, Phases 13/14), flip
its `deficiency.tex` node to `\leanok`, and confirm the boundary regime
`ℓ = 2k = D` is clean as the very first step. Phase 20 (combinatorial
induction → Theorem 4.9) is unblocked once `M(G̃)`, deficiency, and the
def = corank bridge are green.
