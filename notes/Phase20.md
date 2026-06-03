# Phase 20 — Combinatorial induction → Theorem 4.9 (work log)

**Status:** in progress (just opened).

This phase is stratum 4 of the molecular-conjecture program (KT §3
Lemmas 3.4/3.5 full forms, §4). The program-level plan, reuse map,
citations, and risk register live in `notes/MolecularConjecture.md`
*Phase 20*; read that first. This file carries Phase-20-local state,
the lemma checklist, decisions, and hand-off. The forward-mode
dep-graph / lemma index is the new blueprint chapter
`blueprint/src/chapter/molecular-induction.tex`
(`sec:molecular-induction`); its red nodes are the live to-do list.

## Current state

Phase just opened: the scaffolding commit creates this file, the new
forward-mode chapter `molecular-induction.tex` (all nodes red — the
to-do list), wires it into `main.tex`, flips the ROADMAP §20 row to
*in progress*, and syncs the three user-facing surfaces. **No Lean
yet** — `Molecular/Induction.lean` does not exist; it is created when
the first node lands.

Next concrete step: the leaf-most red node whose statement
dependencies are all green. The two inherited structural lemmas open
the chapter — `lem:circuit-induces-rigid` (KT 3.4 full form) and
`lem:contraction-minimality` (KT 3.5) — both unblocked by Phase 19's
`thm:def-eq-corank` (the JJ09 reverse `le_rank_add_deficiency` supplies
the lower bound KT 3.4's tightness equality waited on). KT 3.4 full
form additionally needs a **vertex-induced-subgraph-from-an-edge-set
construction** on `Graph α β` (no existing analogue) — that
construction is the realistic first piece of Lean to build, since both
inherited lemmas and the graph operations want it.

## Architectural choices made up front

- **New file `Molecular/Induction.lean`.** Per the one-`.lean` /
  one-`.tex` per molecular phase convention (post-Phase-18 cleanup
  split). Carrier: mathlib core `Graph α β`, matching Phases 13–19.
- **Graph operations as `Graph α β` constructions, reusing the matroid
  layer.** Splitting-off / edge-splitting / removal / rigid-contraction
  are graph-level ops; their *deficiency* behaviour routes through the
  matroid `M(G̃)` (Phase 19) and matroid restriction/contraction +
  fundamental circuits (mathlib `Matroid.restrict`, `Matroid.contract`,
  `Matroid.fundCircuit`) + the vendored union subsystem
  (`Matroid/Constructions/Union.lean`). `edgeMultiply` / `mulTilde`
  carry the `(D−1)·G` plumbing already.
- **Forest surgery (4.1/4.2) is the hard new pure combinatorics** — no
  existing analogue, budget the most time (flagged in
  `notes/MolecularConjecture.md` *Phase 20* hard-core). Decide the
  packing-vs-matroid framing (explicit `D` forests vs. base of the
  `D`-fold cycle-matroid union) when the first surgery node lands.

## Lemma checklist

Forward-mode: the authoritative node list is `molecular-induction.tex`
(`sec:molecular-induction`). Tracked here for hand-off convenience;
flip to `[x]` as each lands `\leanok` in the chapter.

Inherited from Phase 19 (schedule early):
- [ ] `lem:circuit-induces-rigid` — KT 3.4 full form: a circuit `X`
  induces a rigid `G[V(X)]` (tightness equality `|X−e| = D(|V(X)|−1)`).
  Unblocked by `thm:def-eq-corank` (lower bound) + needs the
  vertex-induced-subgraph construction.
- [ ] `lem:contraction-minimality` — KT 3.5: contracting a proper rigid
  subgraph preserves minimal `k`-dof (Case I engine).

Graph operations:
- [ ] `def:graph-operations` — removal `G_v`, splitting-off `G_v^{ab}`,
  edge-splitting `H_{ab}^v` (inverse of splitting-off).
- [ ] `def:rigid-contraction` — rigid-subgraph contraction `G/E(H)`.

Forest surgery (hard core):
- [ ] `lem:forest-surgery-split` — KT 4.1, splitting-off direction
  (explicit forest surgery at a degree-2 vertex).
- [ ] `lem:forest-surgery-unsplit` — KT 4.2, edge-splitting direction
  (the inverse; makes split/unsplit inverse on deficiency).

Dof tracking:
- [ ] `lem:dof-tracking` — KT 4.3–4.5, deficiency under removal /
  splitting-off.
- [ ] `lem:reducible-vertex` — KT 4.6, existence of a reducible
  degree-2 vertex (maximal-chain / degree-sequence count).
- [ ] `lem:reduction-step` — KT 4.7–4.8, reduction preserves minimality
  (two circuit-swap arguments; the 4.8 capstone).

Capstone:
- [ ] `thm:minimal-kdof-reduction` — KT Theorem 4.9: every minimal
  `k`-dof-graph reduces to the two-vertex double edge.

(Off the Thm-4.9 critical path; schedule with Phase 21:) KT Lemma 3.2
(not 3-edge-connected), Lemma 3.6 (partition decomposition — needed
only by Case 6.1).

## Decisions made during this phase

(none yet — phase just opened)

## Blockers / open questions

- **Vertex-induced-subgraph-from-an-edge-set construction on
  `Graph α β`** — no existing analogue. Needed by `lem:circuit-induces-rigid`
  (KT 3.4 full form) and by the graph operations. First piece of Lean to
  build; check mathlib `Graph` API for `induce` / `vertexDelete` before
  hand-rolling.
- **Forest-surgery framing** (risk: more abstract machinery than the
  explicit `D`-forest argument needs). Decide explicit-forests vs.
  matroid-base framing when `lem:forest-surgery-split` lands.

## Hand-off / next phase

Phase 20 just opened. Next agent's first concrete commit: build the
**vertex-induced-subgraph-from-an-edge-set construction** on `Graph α β`
(check mathlib `Graph.induce` / `vertexDelete` first) in a new
`Molecular/Induction.lean`, then land the leaf-most inherited lemma —
`lem:circuit-induces-rigid` (KT 3.4 full form): a circuit `X` of
`M(G̃)` induces a rigid `G[V(X)]`, upper bound from `lem:circuit-rigid`
(Phase 19) + lower bound from `thm:def-eq-corank`'s JJ09 reverse. Flip
its node `\leanok` in `molecular-induction.tex` in the same commit. The
forest-surgery core (4.1/4.2) is the budget-the-most-time piece;
schedule after the inherited lemmas + graph-operation defs are green.
