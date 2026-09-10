## Shared dictionary (used by every section of both workbooks)

Body-hinge at `d = 3`: `D = bodyBarDim 3 = 6`, hinge multiplicity `5`.
For a graph `H`,

```
def(H) = max over partitions P of V(H) of [ 6(|P| − 1) − 5·d(P) ]
```

(`Molecular/Deficiency.lean`), `d(P)` = number of edges crossing `P`; `H` is
**rigid** (`H.IsKDof 3 0`) iff `def(H) = 0` iff `5H` packs 6 edge-disjoint
spanning trees (Tay; `thm:body-hinge-tay`). Writing `f(W) = 5|E(W)| −
6(|W| − 1)` for a vertex set `W`, one has `def(H) = 6(|V|−1) − 5|E| +
max { Σ_parts f(part) }`, so `def(H) = 0` forces `f(V(H)) ≥ 0`.

Consequences used throughout (all elementary, all numerically re-checked in
`notes/scripts/w4/nogood_subdiv.py --validate`):

- **(R1) min degree.** A rigid `H` with `2 ≤ |V(H)|` has `deg_H(v) ≥ 2`
  everywhere and is connected (`{v}`-vs-rest gives `6 − 5·deg ≥ 1 > 0`;
  components give `6(p−1) > 0`). Landed as
  `two_le_degree_of_isKDof_zero` (`Deficiency.lean:1306`).
- **(R2) size bound.** A rigid `H` with cycle rank `c = |E| − |V| + 1`
  satisfies `|V(H)| ≤ 5c + 1`, and has at most `2c − 2` vertices of
  `H`-degree `≥ 3`.
- **(R3) short cycles.** `def(C_k) = max(0, k − 6)`: `C_k` is rigid iff
  `k ≤ 6` (the classical 6R-loop count). `C₃` and `C₄` are landed
  (`isKDof_zero_of_triangle`, `c4_isProperRigidSubgraph`).
- **(R4) `hcard` restated.** `PencilNondegFeasible K G` gives `∀ v ∈ V(G),
  (G.closedHubNbhd v).ncard ≤ 3` (`ncard_closedHubNbhd_le_three_of_
  isNondegPencilRealization`). At a **non**-hub the bound is automatic
  (`closedHubNbhd v ⊆ N(v)`, of size `≤ 2`), so `hcard` says exactly:
  **every hub has at most two hub neighbours** — the subgraph induced on
  `{v : deg v ≥ 3}` has maximum degree `≤ 2`. Hence a `2`-edge-connected
  feasible `G` is a **subdivision** of a multigraph `G°` on its hubs (or a
  bare cycle), and hub-hub adjacency is confined to paths/cycles.
- **(R5) feasible triangles are pendant.** `not_pencilNondegFeasible_of_
  triangle_two_hubs` says a triangle of a feasible `G` has `≤ 1` hub, so
  two of its vertices have degree exactly `2`: every triangle is either the
  spanning `C₃` or a two-vertex ear hanging at one vertex.
- **(SD-6) branches are short: length `≤ 5`.** *(New 2026-08-06; §(K-ann)
  calls it **(ANH-8)** and points here — this is the only copy. The `SD-`
  form is forced by `notes/Pencil-labels.md` clause L1: `(R6)` is taken by
  `Pencil-strategy.md` §4.6.)* Let `β` be a branch (maximal degree-2 chain)
  of a class member `G` — tight, `def = 0`, `hnoRigid`, `|V| ≥ 2` — of
  length `ℓ`. Then `ℓ ≤ 5`.
  *Proof.* `G` is 2-edge-connected: a bridge would split `V` into `A, B`
  with `f(A) + f(B) = f(V) + 1 = 1 > 0`, so one side violates sparsity.
  Hence `G′ := G − int(β)` is connected (two edge-disjoint `u`–`w` paths
  cannot both use an edge of `β`). Counting,
  `f(V(G′)) = f(V(G)) − 5ℓ + 6(ℓ−1) = ℓ − 6`. For `ℓ ≥ 7` that is `> 0`,
  contradicting sparsity; for `ℓ = 6` it is `0`, so `def(G′) = 0` and `G′`
  is a **proper** rigid subgraph (`V(G′) ⊊ V(G)` because `β` has interior
  vertices; `|V(G′)| ≥ 2` because `G` has two hubs), contradicting
  `hnoRigid`. ∎ Verified over 4296 triples plus a past-length-6 stress test
  (`notes/scripts/w4/annih.py --census`; §(K-ann) *Step A6*).

### Test shapes `W19` and `S29` (canonical definitions)

Two explicit graphs recur as **test shapes** across both workbooks. They were
built as the W4 residual arc's counterexamples — their certification, their
role there, and their robustness/minimality records are
`notes/Pencil-W4-informal.md` §`hnoGood'` vacuity *Step 3* and §(SAFE-RES)
*Step 2* — and the (K) sections below reuse them as residual-habitat probes
(they are the (K-res) habitat's two named members). **This is their canonical
definition; neither workbook redefines them.**

**`W19`** — `|V| = 19`, `|E| = 22`, `f(V) = 2`, `def = 0`;
`notes/scripts/w4/nogood_subdiv.py --witness` builds it.

```
core       C₄ :  c0 – c1 – c2 – c3 – c0
poles      z0, z1 attached to c0 ;  z2 attached to c2
paths      z0 –w0_0 w0_1 w0_2 w0_3– z1
           z1 –w1_0 w1_1 w1_2 w1_3– z2
           z2 –w2_0 w2_1 w2_2 w2_3– z0
```

Degrees `c0 ↦ 4`, `c2 ↦ 3`, `z0,z1,z2 ↦ 3`, all others `2`. Hubs:
`{c0, c2, z0, z1, z2}`. Its only proper rigid subgraph is the core `C₄`.

**`S29`** — `|V| = 29`, `|E| = 34`, `f(V) = 2`, `def = 0`;
`notes/scripts/w4/saferes.py --witness` builds it.

```
core    C₄ :  A – m1 – B – m2 – A            (A deg 4, B deg 3)
poles   hub edges  A–z0,  A–z1,  B–z2
ring    z0 – y0 – z1 – y1 – z2 – y2 – z0,  every leg 2-subdivided
spokes  y0–p, y1–p, y2–p,                  every spoke 2-subdivided
```

Hubs (9): `A, B, z0, z1, z2, y0, y1, y2, p`; every one of the 14 branches
carries `0`, `1` or `2` interior vertices. Its only proper rigid subgraph is
the core `C₄`.
