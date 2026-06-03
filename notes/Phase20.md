# Phase 20 — Combinatorial induction → Theorem 4.9 (work log)

**Status:** in progress.

This phase is stratum 4 of the molecular-conjecture program (KT §3
Lemmas 3.4/3.5 full forms, §4). The program-level plan, reuse map,
citations, and risk register live in `notes/MolecularConjecture.md`
*Phase 20*; read that first. This file carries Phase-20-local state,
the lemma checklist, decisions, and hand-off. The forward-mode
dep-graph / lemma index is the new blueprint chapter
`blueprint/src/chapter/molecular-induction.tex`
(`sec:molecular-induction`); its red nodes are the live to-do list.

## Current state

`Molecular/Induction.lean` has the first two structural nodes plus the
**graph operations** green: the vertex-induced-subgraph construction
(`def:induced-span`), the full form of KT Lemma 3.4
(`lem:circuit-induces-rigid`), and now the four graph operations
(`def:graph-operations` + `def:rigid-contraction`).

- **`def:induced-span`** — `Graph.fiberSpan G n X = (G.mulTilde n).spanningVerts X`
  (the vertices `V(X)` spanned by a fiber set `X` of `G̃`) and
  `Graph.inducedSpan G n X = G.induce (G.fiberSpan n X)` (the induced subgraph
  `G[V(X)]` of the *original* `G`). The construction is **mathlib's
  `Graph.induce`** (`Mathlib.Combinatorics.Graph.Delete`) — no new graph
  machinery needed, contra the phase-open expectation; `inducedSpan` is a thin
  wrapper plus the simp lemma `vertexSet_inducedSpan`.
- **`lem:circuit-induces-rigid`** (`Graph.circuit_induces_isTight`, KT 3.4 full
  form) — for a circuit `X` of `M(G̃)` and `e ∈ X`, the tightness equality
  `|X − e| + D = D·|V(X)|` (i.e. `|X − e| = D(|V(X)| − 1)`), so `X − e` packs `D`
  spanning trees on `V(X)` and `G[V(X)]` is rigid. **Did NOT need
  `thm:def-eq-corank`** (the phase-open / blueprint `\uses` was overcautious): the
  lower bound `|X| > D(|V(X)| − 1)` is the matroidal circuit-minimality fact
  `circuit_ncard_gt`, proved directly from `matroidMG_indep_iff` (every proper
  subset of `X` is independent ⟹ `(D,D)`-sparse, so the dependent `X`'s sparsity
  failure is at `X` itself). Upper bound from Phase 19's
  `isSparse_diff_singleton_of_isCircuit`. Axiom-free.

- **`def:graph-operations` / `def:rigid-contraction`** — the four ops:
  `Graph.removeVertex` (= mathlib `deleteVerts {v}`), `Graph.splitOff v a b e₀`
  (delete `v`, add fresh edge `e₀` joining `a,b`), `Graph.edgeSplit a b v e₀ e₁ e₂`
  (subdivide `e₀` by fresh `v` via fresh `e₁,e₂`), and `Graph.rigidContract G H r`
  (= `(G.deleteEdges E(H)).map (collapseTo r V(H))`, collapse `V(H)` to representative
  `r`). `removeVertex` and `rigidContract` are thin mathlib compositions
  (`deleteVerts` / `deleteEdges` + `map`); `splitOff` / `edgeSplit` are structure
  literals (no graph union/`addEdge` in mathlib). Each has `vertexSet_*`/`*_isLink`
  simp lemmas. Axiom-free.

Next concrete step: the other inherited lemma `lem:contraction-minimality` (KT 3.5,
uses `thm:def-eq-corank` + `lem:subgraph-minimality`). The forest-surgery core
(4.1/4.2) is the budget-the-most-time piece, scheduled after KT 3.5.

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
- [x] `lem:circuit-induces-rigid` — KT 3.4 full form: a circuit `X`
  induces a rigid `G[V(X)]` (tightness equality `|X−e| = D(|V(X)|−1)`).
  `Graph.circuit_induces_isTight`; lower bound is the direct circuit-minimality
  fact `Graph.circuit_ncard_gt` (NOT `thm:def-eq-corank`).
- [ ] `lem:contraction-minimality` — KT 3.5: contracting a proper rigid
  subgraph preserves minimal `k`-dof (Case I engine).

Graph operations:
- [x] `def:induced-span` — vertex-induced subgraph `G[V(X)]` from a fiber set
  `X` of `G̃` (`Graph.fiberSpan` / `Graph.inducedSpan`, via mathlib `Graph.induce`).
- [x] `def:graph-operations` — removal `G_v` (`Graph.removeVertex`), splitting-off
  `G_v^{ab}` (`Graph.splitOff`), edge-splitting `H_{ab}^v` (`Graph.edgeSplit`,
  inverse of splitting-off).
- [x] `def:rigid-contraction` — rigid-subgraph contraction `G/E(H)`
  (`Graph.rigidContract`, via `deleteEdges` + `map (collapseTo …)`).

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

- **Vertex-induced subgraph = mathlib `Graph.induce`, not a hand-rolled
  construction.** The phase-open blocker ("no existing analogue") was wrong:
  `Mathlib.Combinatorics.Graph.Delete` has `Graph.induce (X : Set α)` with the
  full API (`vertexSet_induce`, `induce_isLink`, `edgeSet_induce`, `induce_le`).
  `Graph.inducedSpan G n X := G.induce (G.fiberSpan n X)` is a thin wrapper;
  `fiberSpan` reuses Phase 16's `spanningVerts` on `mulTilde`. Reach for mathlib's
  `induce` before hand-rolling in the graph-operations nodes too.
- **KT 3.4 lower bound is the direct circuit-minimality fact, NOT
  `thm:def-eq-corank`.** A circuit `X` is a *minimal* dependent set, so every
  proper subset is independent ⟹ `(D,D)`-sparse (`matroidMG_indep_iff`); the
  dependent `X`'s sparsity failure is therefore at `X` itself, giving `|X| >
  D(|V(X)|−1)` (`circuit_ncard_gt`). This matches KT's "see [21]" (a count-matroid
  fact), not the JJ09 min–max. Blueprint `\uses` corrected to drop
  `thm:def-eq-corank`. (The def=corank reverse is still the engine for KT 3.5's
  rank-conservation, scheduled next.)

- **Graph operations: reuse mathlib where possible, structure-literal where not.**
  `removeVertex = deleteVerts {v}` and `rigidContract = (deleteEdges E(H)).map
  (collapseTo r V(H))` are thin compositions of mathlib `Graph` ops (mathlib's `map`
  realizes the vertex-collapse). `splitOff` / `edgeSplit` *add* edges/vertices, and
  mathlib's `Graph` has no union/join (`SemilatticeInf` only) or `addEdge`, so they
  are structure literals with explicit fresh edge labels (`e₀` for splitting-off;
  `e₁,e₂` for edge-splitting). `collapseTo r S` uses `open Classical in` for the
  membership `if`. Deficiency behaviour is deferred to the later surgery nodes.

### Promoted to FRICTION
- *`IsCircuit.subset_ground` for `M(G̃)` gives a restrict-ground `⊆`, defeq-but-not-
  syntactic to `E(G̃)` — ascribe once* → FRICTION `[resolved] [matroid]
  IsCircuit.subset_ground for M(G̃) …`.
- *Hand-rolled `Graph` with several fresh edge labels needs a distinctness guard in a
  clause, else `eq_or_eq_of_isLink_of_isLink` is unprovable* → FRICTION `[resolved] A
  hand-rolled Graph α β with several fresh edge labels …`.

## Blockers / open questions

- **Forest-surgery framing** (risk: more abstract machinery than the
  explicit `D`-forest argument needs). Decide explicit-forests vs.
  matroid-base framing when `lem:forest-surgery-split` lands.

## Hand-off / next phase

Green in `Molecular/Induction.lean`, axiom-free, blueprint nodes `\leanok`:
`def:induced-span`, `lem:circuit-induces-rigid` (KT 3.4 full form), and the four
graph operations `def:graph-operations` (`Graph.removeVertex` / `splitOff` /
`edgeSplit`) + `def:rigid-contraction` (`Graph.rigidContract`, via the auxiliary
`collapseTo`). Each op has `vertexSet_*` / `*_isLink` simp lemmas.

Next agent's concrete commit: the inherited lemma `lem:contraction-minimality`
(KT 3.5 — rigid-subgraph contraction preserves minimal `k`-dof). It uses
`thm:def-eq-corank` (rank conservation under contraction: contracting a rigid `H`
removes `D(|V(H)|−1)` from both `rank M(G̃)` and the ambient `D(|V|−1)`, so the
corank/deficiency is unchanged) + `lem:subgraph-minimality` (minimality transport).
The new `Graph.rigidContract` is the graph-side object it operates on; the matroid
side is `Matroid.contract` on `M(G̃)`. The forest-surgery core (4.1/4.2,
`lem:forest-surgery-split`/`-unsplit`) is the budget-the-most-time piece; schedule
after KT 3.5. Decide the explicit-`D`-forests-vs-matroid-base framing when the first
surgery node lands (see Blockers).
