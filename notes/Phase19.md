# Phase 19 — `M(G̃)`, deficiency, `k`-dof graphs (work log)

**Status:** in progress (all four definition nodes + four structural lemmas
+ the rank upper bound + the **full def = corank bridge** landed:
`lem:matroid-restrict-subgraph`, `lem:subgraph-minimality` (KT 3.3),
`lem:two-edge-conn` (KT 3.1, cut form), `lem:circuit-rigid` (KT 3.4, matroidal
core), `lem:rank-matroidMG-le`; plus all three pieces of the `thm:def-eq-corank`
sub-plan — `lem:rk-within-parts` (piece 1), `lem:weak-duality` (piece 2, `def ≤
corank`), and the JJ09 reverse `def ≥ corank` (piece 3, `le_rank_add_deficiency`),
assembled into `thm:def-eq-corank` (`rank_add_deficiency_eq` /
`isBase_ncard_add_deficiency_eq`). All `deficiency.tex` nodes are now green.
The inherited Phase-18 node `prop:rigidity-matrix-prop11` is **not** fully closed
by this — its matroidal half (`def = corank M(G̃)`) is green, but its *analytic*
half (`rank R(G,p) = D(|V|-1) − def(G̃)`, JJ09 Thm 6.1 geometric side, wiring the
rigidity-matrix rank to the matroid corank) is a separate object scheduled with the
algebraic induction.)

This phase is stratum 3 of the molecular-conjecture program (KT §2.5,
§3). The program-level plan, reuse map, citations, and risk register
live in `notes/MolecularConjecture.md` *Phase 19*; read that first.
This file carries Phase-19-local state, the lemma checklist, decisions,
and hand-off. The forward-mode dep-graph / lemma index is the new
blueprint chapter `blueprint/src/chapter/deficiency.tex`
(`sec:molecular-deficiency`); its red nodes are the live to-do list.

## Current state

`Molecular/Deficiency.lean` has two forward-mode nodes green:
`def:matroid-MG` and `def:D-deficiency`. `def:matroid-MG` defines
`Graph.mulTilde G n = (D−1)·G` (`= G.edgeMultiply (bodyHingeMult n)`,
edge type `β × Fin (D−1)`) and `Graph.matroidMG G n` as the `D`-fold
cycle-matroid union of `G̃` restricted to `E(G̃)`, with `D = bodyBarDim n`;
the **boundary-regime cleanliness check** `matroidMG_indep_iff` confirms
(risk #2) that `M(G̃).Indep E' ↔ E' ⊆ E(G̃) ∧ (G̃ ↾ E').IsSparse D D` —
clean, routing through Phase 13's
`unionPow_cycleMatroid_indep_iff_isSparse_restrict` (+ Tutte–Nash-Williams),
**not** `CountMatroid.lean` (`ℓ < 2k`).

`def:D-deficiency` defines `Graph.partitionDef G n f` =
`D(|P|−1) − (D−1)·d_G(P)` (`ℤ`-valued) and `Graph.deficiency G n` =
`⨆ f, partitionDef`, with partitions encoded as labelings `f : α → α`
(fibers = parts): `numParts G f = |f '' V(G)|`, `crossingEdges G f` =
edges with differently-labeled endpoints. `partitionDef_one` is the
`def ≥ 0` witness (trivial one-part partition gives `0`).

`def:k-dof` is now also green: `Graph.IsKDof G n k := deficiency G n = k`
(`0`-dof = body-hinge rigid), `Graph.edgeFiber e n := {p | p.1 = e}` (the `D-1`
parallel copies of `e`), and `Graph.IsMinimalKDof` = `IsKDof` plus every base
`B` of `M(G̃)` meeting every edge-fiber of an edge `e ∈ E(G)`
(`(B ∩ edgeFiber e n).Nonempty`, over `Matroid.IsBase`).

`def:rigid-subgraph` is now green: `Graph.IsRigidSubgraph H G n := H ≤ G ∧ H.IsKDof n 0`
(rigid = subgraph + `0`-dof, keyed off the multigraph `Graph.IsSubgraph`/`≤` order)
and `Graph.IsProperRigidSubgraph H G n` = rigid plus `V(H).Nonempty ∧ V(H) ⊂ V(G)`.
A *circuit* of `M(G̃)` is mathlib's `Matroid.IsCircuit (G.matroidMG n)` (no project
def needed); 2-edge-connectivity is the still-red `lem:two-edge-conn` (KT 3.1), not
this commit.

The first structural-lemma engine is now green: `lem:matroid-restrict-subgraph`
(`Graph.matroidMG_restrict_mulTilde`), the matroid identity `M(G̃) ↾ E(H̃) = M(H̃)`
for `H ≤ G` that KT Lemma 3.3 runs on. Proved via `Matroid.ext_indep` routing both
sides through `matroidMG_indep_iff`; the `IsSparse`-agreement engine is the private
`isSparse_restrict_mulTilde_congr` (edge sets + `spanningVerts` agree because `Inc` on
`E(H̃)` is shared, via `hHG.inc_congr`). New supporting lemma `edgeMultiply_mono` in
`BodyBar/BodyHinge.lean` (`H ≤ G → m·H ≤ m·G`).

`lem:subgraph-minimality` (KT 3.3) is now green: `Graph.subgraph_minimality`. A subgraph
`H ≤ G` of a minimal `k`-dof-graph `G`, with `def(H̃) = k'`, is a minimal `k'`-dof-graph
(rigid `k'=0` case feeds Cases I/III). The deficiency half is a hypothesis (it defines `k'`);
the content is the base/fiber-meeting transport over the green restriction identity. A base
`B'` of `M(H̃) = M(G̃) ↾ E(H̃)` is an `M(G̃)`-basis of `E(H̃)` (`Matroid.isBase_restrict_iff'`),
extends to a base `B ⊇ B'` of `M(G̃)` (`Indep.exists_isBase_superset`) with `B' = B ∩ E(H̃)`
(`IsBasis'.eq_of_subset_indep`); each fiber `ẽ` of `e ∈ E(H) ⊆ E(G)` lies in `E(H̃)`, so
`G`'s minimality `B ∩ ẽ ≠ ∅` descends to `B' ∩ ẽ = B ∩ ẽ ≠ ∅`. No base-extension friction.

The deficiency-attainment API is now green: `bddAbove_range_partitionDef` (the range of
`partitionDef` is finite under `[Finite α]`, so the `iSup` is a genuine attained max, not
junk), `partitionDef_le_deficiency` (the `le_ciSup` half — every partition is a deficiency
lower bound), and `deficiency_nonneg` (`def(G̃) ≥ 0` for `V(G).Nonempty`, via the trivial
partition + `partitionDef_le_deficiency`). These are supporting lemmas (no standalone
blueprint node — the `def ≥ 0` fact already lives in the `def:D-deficiency` prose); they
de-risk the `iSup` model and are the prerequisite every remaining node needs (the
`{V', V∖V'}` cut-partition lower bound for `lem:two-edge-conn`, the deficiency side of the
corank bridge).

`lem:two-edge-conn` (KT 3.1) is now green: `Graph.two_le_crossingEdges_of_isKDof_zero`. A
body-hinge-rigid (`0`-dof) graph admits no bridge cut — for a nonempty proper `V' ⊊ V(G)`
separating `V(G)`, `d_G(V') ≥ 2`. Phrased directly in cut form (mathlib has no
edge-connectivity predicate for `Graph α β`, only `SimpleGraph`): the cut `{V', V∖V'}` is a
two-part partition (`Graph.cutLabeling` / `Graph.numParts_cutLabeling`), so `def ≥ D - (D-1)d`;
`d ≤ 1` forces `def ≥ 1 > 0`, contradicting `def = 0` (via `partitionDef_le_deficiency`). Needs
only `D = bodyBarDim n ≥ 1`. No new graph machinery — runs entirely on the green
deficiency-attainment API.

The rank upper bound `lem:rank-matroidMG-le` (`Graph.rank_matroidMG_le`) is now green:
`rank M(G̃) ≤ D·(|V(G)| - 1)` for `V(G).Nonempty`. Via `Matroid.rank_def` + `rk_le_iff`,
every independent `I ⊆ E(G̃)` is `(D,D)`-sparse (`matroidMG_indep_iff`); applying sparsity
to `I` itself gives `|I| + D ≤ D·|spanningVerts I| ≤ D·|V|`, hence `|I| ≤ D(|V|-1)`. This is
the matroidal mirror of Phase 18's analytic `rank R ≤ D(|V|-1)` and the **upper-bound half**
of the def = corank bridge that the conjecture (Thm 5.6) needs. The prove-vs-hypothesize
decision (risk #4): the reverse direction of the full JJ09 min–max (a partition attaining the
rank) is **deferred** until a downstream node needs the full equality, since the conjecture
needs only this upper bound — so `thm:def-eq-corank` (full equality) stays red.

`lem:circuit-rigid` (KT 3.4) is now green in matroidal-core form:
`Graph.isSparse_diff_singleton_of_isCircuit`. For a circuit `X` of `M(G̃)` and `e ∈ X`,
`X \ {e}` is `(D,D)`-sparse, equivalently an `M(G̃)`-basis of `X` — a circuit is exactly
one edge short of independent on its span. Two-line term-mode composition of
`IsCircuit.diff_singleton_indep` + `matroidMG_indep_iff` (sparse half) and
`IsCircuit.diff_singleton_isBasis` (basis half). This is the upper-bound / maximal-sparse
form KT's fundamental-circuit arguments (4.5, 6.10–6.11, Phases 21–22) consume. The full
KT 3.4 — `G[V(X)]` rigid, i.e. the tightness *equality* `|X−e| = D(|V(X)|−1)` and
`def(G[V(X)]̃) = 0` — needs the **lower** bound `|X| > D(|V(X)|−1)` forced by `X`
dependent, which is the reverse direction of the full `def = corank` min–max
(`thm:def-eq-corank`, JJ09, risk #4); deferred with that node, and would also need a
vertex-induced-subgraph-from-edge-set construction (no existing analogue).

Piece 1 of the `thm:def-eq-corank` sub-plan is now green: `lem:rk-within-parts`
(`Graph.rk_cycleMatroid_within_parts_le`). For a labeling `f` and the non-crossing-fiber
edge set `Y` of `G̃` (every fiber of `Y` joins two equally-`f`-labelled vertices),
`r_cycle(Y) + numParts f ≤ |V(G)|`. Proof: the rank–component identity
`eRank(G̃ ↾ Y) + c(G̃ ↾ Y) = |V(G)|` (the edge-restriction `G̃ ↾ Y` keeps every vertex,
so `V(G̃ ↾ Y) = V(G̃) = V(G)`, via `eRank_cycleMatroid_add_numberOfComponents`), plus
`c(G̃ ↾ Y) ≥ numParts f` from the components-refine-the-partition injection. The injection
engine is the private `label_eq_of_connBetween` (`f` is constant on each `G̃ ↾ Y` component,
by walk induction since each cons-edge is a within-part fiber), then label `↦` `walkable(rep)`
is `InjOn` via `mem_walkable_iff` + `Set.encard_le_encard_of_injOn`. Stated generally on
`G̃ = mulTilde` (not an abstract `H`) since `numParts`/`mulTilde` are the deficiency-side
objects; all building blocks (`cycleMatroid_restrict`, the rank–component identity,
`walkable`/`ConnBetween` API) are upstream in `apnelson1/Matroid`, no new mirror needed.

Piece 2 of the `thm:def-eq-corank` sub-plan is now green: `lem:weak-duality`
(`Graph.rank_add_partitionDef_le` single-partition + `Graph.rank_add_deficiency_le`
maximised) — `rank M(G̃) + def(G̃) ≤ D(|V|−1)`, i.e. `def ≤ corank`. Via `Union_pow_rk_eq`
(Phase 13) on `X := E(G̃)` with `Y :=` the non-crossing fibers: `rank ≤ D·r_cycle(Y) +
|E(G̃)∖Y|`, where piece 1 bounds `r_cycle(Y) ≤ |V| − numParts f` and the bookkeeping leaf
`|E(G̃)∖Y| = (D−1)·d_G(P)` is `Graph.ncard_crossing_fibers` (each crossing edge `↦` its `D−1`
fibers, the `crossingEdges ×ˢ univ` ncard pattern). The deficiency form maximises the
single-partition bound by `ciSup_le` on the green attainment API. **Needs `1 ≤ bodyBarDim n`**
— the bound is genuinely false at `D = 0` (then `G̃` is edgeless, `rank = 0`, but
`partitionDef = d`); see FRICTION. The conjecture runs at `D ≥ 3`, so the hypothesis is free.

Piece 3 (`thm:def-eq-corank`, the JJ09 reverse) is now green:
`Graph.le_rank_add_deficiency` (`def ≥ corank`) assembled with `lem:weak-duality`
into `Graph.rank_add_deficiency_eq` (`rank M(G̃) + def(G̃) = D(|V|−1)`) and its
base form `Graph.isBase_ncard_add_deficiency_eq` (`|B| + def(G̃) = D(|V|−1)`). The
reverse runs on the Edmonds-optimal `Y₀` (existence half of `Union_pow_rk_eq`): the
partition `P` into the components of `G̃ ↾ Y₀` is attaining. For `P` the within-part
fibers are exactly `Y₀` (so `r_cycle(Y₀) + numParts f = |V|` *exactly* —
`rk_add_numParts_componentLabel`, the `≤` from piece 1, the `≥` from the
components-refine-partition injection run in reverse, `numberOfComponents_le_numParts`),
and every crossing edge's `D−1` fibers all lie outside `Y₀`, so `(D−1)·d_G(P) ≤
|E(G̃)∖Y₀|`; substituting into the Edmonds bound gives `rank ≥ D(|V|−1) − def_P`. The
component labeling is the private `componentLabel` (representative of the `walkable`
component, factored through `pickVertex` so constancy-on-component is a `congrArg`).
Axiom-free (`propext`/`Classical.choice`/`Quot.sound` only). See *Hand-off* below.

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
- [x] `def:D-deficiency` — `def_G̃(P) = D(|P|−1) − (D−1)·d_G(P)`;
  `def(G̃) = maxₚ def_G̃(P)`. (`Graph.partitionDef` + `Graph.deficiency`,
  partitions as labelings `f : α → α`; `numParts` / `crossingEdges` +
  `partitionDef_one` witness.)
- [x] `def:k-dof` — `k`-dof / `0`-dof (= body-hinge rigid) / minimal
  `k`-dof (every base of `M(G̃)` meets every edge-fiber `ẽ`). (`Graph.IsKDof`,
  `Graph.edgeFiber`, `Graph.IsMinimalKDof`.)
- [x] `def:rigid-subgraph` — rigid + proper rigid subgraph (circuits via
  mathlib's `Matroid.IsCircuit`; 2-edge-connectivity deferred to
  `lem:two-edge-conn`). (`Graph.IsRigidSubgraph` / `Graph.IsProperRigidSubgraph`.)
- [x] `thm:def-eq-corank` — the def = corank bridge (JJ09 Thm 6.1 /
  Cor 6.2): `|B| + def(G̃) = D(|V|−1)`. Green: `Graph.rank_add_deficiency_eq`
  (`rank + def = D(|V|−1)`) + `Graph.isBase_ncard_add_deficiency_eq` (base form),
  `le_antisymm` of `lem:weak-duality` and the JJ09 reverse
  `Graph.le_rank_add_deficiency` (piece 3, via the component-partition of the
  Edmonds-optimal `Y₀`; helpers `rk_add_numParts_componentLabel`,
  `numberOfComponents_le_numParts`, `componentLabel`/`pickVertex`).
- [x] `lem:rk-within-parts` — piece 1 of `thm:def-eq-corank`: the
  partition-respecting cycle-matroid rank bound `r_cycle(Y) + numParts f ≤ |V|`
  for the non-crossing-fiber set `Y` (`Graph.rk_cycleMatroid_within_parts_le`,
  via the rank–component identity + the components-refine-partition injection).
- [x] `lem:weak-duality` — piece 2 of `thm:def-eq-corank`: `rank M(G̃) + def(G̃) ≤
  D(|V|−1)` (`def ≤ corank`). `Graph.rank_add_partitionDef_le` (single partition, via
  `Union_pow_rk_eq` + piece 1 + the `(D−1)·d` crossing-fiber count
  `Graph.ncard_crossing_fibers`) maximised to `Graph.rank_add_deficiency_le` by `ciSup_le`.
  Needs `1 ≤ bodyBarDim n` (false at `D=0`).
- [x] `lem:rank-matroidMG-le` — the rank upper bound `rank M(G̃) ≤ D(|V|−1)`
  (`Graph.rank_matroidMG_le`), the conjecture-relevant half of the bridge:
  every base is `(D,D)`-sparse, so `|B| + D ≤ D·|spanningVerts B| ≤ D·|V|`.
- [x] `lem:two-edge-conn` — KT Lemma 3.1 (2-edge-connectivity, cut form):
  `Graph.two_le_crossingEdges_of_isKDof_zero` (+ `cutLabeling` / `numParts_cutLabeling`).
  A `0`-dof graph has `d_G(V') ≥ 2` for every separating `V' ⊊ V(G)`.
- [x] `lem:matroid-restrict-subgraph` — the engine of KT 3.3:
  `M(G̃) ↾ E(H̃) = M(H̃)` for `H ≤ G`. (`Graph.matroidMG_restrict_mulTilde`,
  via `Matroid.ext_indep` + `matroidMG_indep_iff`.)
- [x] `lem:subgraph-minimality` — KT Lemma 3.3 (subgraph minimality
  via restriction). (`Graph.subgraph_minimality`: base/fiber-meeting
  transport over the green restriction identity + base extension.)
- [x] `lem:circuit-rigid` — KT Lemma 3.4 (matroidal core):
  `Graph.isSparse_diff_singleton_of_isCircuit` — for a circuit `X` and `e ∈ X`,
  `X \ {e}` is `(D,D)`-sparse / an `M(G̃)`-basis of `X` (one edge short of independent).
  The full `G[V(X)]`-rigid tightness *equality* is deferred with `thm:def-eq-corank`
  (needs the JJ09 lower bound + a vertex-induced-subgraph construction).
- [ ] `prop:rigidity-matrix-prop11` — KT Prop 1.1 reconciliation
  (**inherited from Phase 18**; node lives in `rigidity-matrix.tex`).
  Matroidal half (`def = corank M(G̃)`) now green via `thm:def-eq-corank`; the
  remaining **analytic** half — `rank R(G,p) = D(|V|−1) − def(G̃)` (JJ09 Thm 6.1
  geometric side), wiring the rigidity-matrix rank to the matroid corank — is a
  separate object (not closeable by `thm:def-eq-corank` alone). Scheduled with the
  algebraic induction (Phase 21+); the node prose is updated to flag the split.
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
- **Partitions modeled as labelings `f : α → α`, not `Setoid` /
  `Finpartition`.** `def:D-deficiency` encodes a partition of `V(G)` by
  the kernel of a labeling `f : α → α` (fibers = parts): `numParts G f =
  (f '' V(G)).ncard` and `crossingEdges G f = {e ∈ E(G) | ∃ x y, IsLink
  e x y ∧ f x ≠ f y}`. This stays in the project's `Set.ncard` idiom and
  gives clean `|P|` / `d_G(P)` counts; `Setoid.IsPartition` partitions
  all of `α` (covers `univ`), not just `V(G)`, and `Finpartition` would
  drag in `Finset` / `DecidableEq` plumbing. Fixing the label type at
  `α` (rather than an arbitrary `ι`) keeps the `⨆` over partitions
  well-typed and finite under `[Finite α]`; every partition of `V(G)`
  into `≤ |α|` parts is realized by some `f : α → α`.
- **`def_G̃(P)` is `ℤ`-valued (genuinely signed).** A fine partition
  crossing many edges has *negative* deficiency, so `partitionDef : ℤ`
  and `deficiency = ⨆ f, partitionDef` over the
  `ConditionallyCompleteLinearOrder` `ℤ`. `def(G̃) ≥ 0` via the trivial
  one-part partition (`partitionDef_one`). The ROADMAP "avoid
  ℕ-subtraction" rule is for ℕ; here the honest model is signed. `iSup`
  needs no `[Finite α]` to typecheck (junk-on-unbounded), so the
  instance is dropped from the `deficiency` signature (the env linter
  flagged it as unused) and reintroduced where lemmas need attainment.

- **`edgeFiber e n := {p | p.1 = e}` is not `G`-parametrized; `IsKDof`'s `k`
  is `ℤ`.** The edge-fiber of `e` in `G̃` depends only on `e` and `n` (it is the
  `D−1` parallel copies `{p : β × Fin (bodyHingeMult n) | p.1 = e}`), so
  `edgeFiber` takes no `Graph` argument and is called positionally
  (`edgeFiber e n`, not `G.edgeFiber`). `IsKDof G n k` keeps `k : ℤ` to match
  the `ℤ`-valued `deficiency` (the trivial-partition lower bound is `≥ 0` but
  the def is over signed `partitionDef`); callers needing `0 ≤ k` add it as a
  hypothesis. `IsMinimalKDof` takes `[DecidableEq β]` (inherited from
  `matroidMG`) and phrases fiber-meeting as `(B ∩ edgeFiber e n).Nonempty` over
  `Matroid.IsBase`, restricted to `e ∈ E(G)`.

- **Rigid subgraph keyed off `H ≤ G`, not edge-restriction.** `IsRigidSubgraph H G n
  := H ≤ G ∧ H.IsKDof n 0` uses the mathlib multigraph subgraph order (`Graph.IsSubgraph`,
  i.e. `≤`) so `deficiency`/`IsKDof` apply to `H` directly (both already take a bare
  `Graph α β`). No new edge-restriction machinery. *Proper* adds `V(H).Nonempty ∧
  V(H) ⊂ V(G)`. The *circuit* notion is mathlib's `Matroid.IsCircuit (G.matroidMG n)`
  — no project def; only the rigid/proper-rigid `def`s are new. 2-edge-connectivity is
  prose in the node (the lemma `lem:two-edge-conn` is separate, still red), and mathlib
  has no edge-connectivity API for `Graph α β` (only `SimpleGraph`) — flagged for that
  node's scoping.

- **KT 3.1 stated in cut form, not via a connectivity predicate.** `lem:two-edge-conn`
  (`two_le_crossingEdges_of_isKDof_zero`) phrases 2-edge-connectivity directly as "every
  separating `V' ⊊ V(G)` has `d_G(V') ≥ 2`", because mathlib has no edge-connectivity API
  for `Graph α β` (only `SimpleGraph`). This is exactly the form KT's proof uses (the bridge
  cut `{V', V∖V'}`), so no predicate is lost. The cut partition is encoded by a `cutLabeling`
  helper (collapse `V'`→`a`, complement→`b`); `numParts_cutLabeling = 2` then drives the
  `def ≥ D-(D-1)d` lower bound through `partitionDef_le_deficiency`. Self-contained on the
  green deficiency-attainment API — no new graph machinery, and `D ≥ 1` suffices (KT uses
  `D ≥ 3`, but `D ≥ 1` already gives `(D-1)·d < D` when `d ≤ 1`).

- **KT 3.3 split into engine + node; both green.** `lem:subgraph-minimality`
  (KT Lemma 3.3) is two pieces: the matroid identity `M(G̃) ↾ E(H̃) = M(H̃)`
  (engine, green as `lem:matroid-restrict-subgraph` / `matroidMG_restrict_mulTilde`)
  and the minimality transport built on it (`subgraph_minimality`). The identity
  is proved by `Matroid.ext_indep` through `matroidMG_indep_iff` (not a
  `Matroid.Union`-restrict-commute lemma — the vendored union has no such
  lemma and ground `univ`), so it never touches the union internals: both
  sides reduce to `(D,D)`-sparsity of `·̃ ↾ E'`, which agree by the private
  `isSparse_restrict_mulTilde_congr`. The transport `\uses` the engine: a base
  `B'` of `M(H̃) = M(G̃) ↾ E(H̃)` is an `M(G̃)`-basis of `E(H̃)`
  (`Matroid.isBase_restrict_iff'`), extends to a base `B ⊇ B'` of `M(G̃)`
  (`Indep.exists_isBase_superset`), and equals `B ∩ E(H̃)` by maximality
  (`IsBasis'.eq_of_subset_indep`); each fiber `ẽ` of `e ∈ E(H) ⊆ E(G)` sits in
  `E(H̃)`, so `G`-minimality `B ∩ ẽ ≠ ∅` descends to `B'`. The Lean is the
  general KT 3.3 form (any subgraph with `def(H̃) = k'` is minimal `k'`-dof), not
  just the rigid `k'=0` specialization. *Lifted:* the `edgeMultiply.IsLink`
  defeq-ascription lesson → FRICTION.

- **KT 3.4 landed in matroidal-core (sparse / basis) form, full `G[V(X)]`-rigid deferred.**
  `isSparse_diff_singleton_of_isCircuit`: a circuit `X` minus any `e ∈ X` is `(D,D)`-sparse,
  equivalently an `M(G̃)`-basis of `X`. Two-line term composition over `matroidMG_indep_iff`
  + mathlib's `IsCircuit.{diff_singleton_indep, diff_singleton_isBasis}` — no friction. This
  is exactly what KT's fundamental-circuit consumers (4.5, 6.10–6.11) use (`X−e` independent /
  maximal). The full KT 3.4 (`G[V(X)]` rigid, the *equality* `|X−e| = D(|V(X)|−1)`) needs
  (a) the lower bound `|X| > D(|V(X)|−1)` from `X` dependent — the JJ09 min–max reverse,
  deferred with `thm:def-eq-corank` (risk #4) — and (b) a vertex-induced-subgraph-from-an-
  edge-set construction with no existing `Graph α β` analogue. Both land with the bridge.

- **Piece 1 (`lem:rk-within-parts`) via rank–components, not direct-sum-over-parts.**
  The leaf `r_cycle(Y) + numParts f ≤ |V|` for non-crossing fibers `Y` is proved through
  the graphic rank–component identity `eRank(G̃ ↾ Y) + c(G̃ ↾ Y) = |V(G)|`
  (`eRank_cycleMatroid_add_numberOfComponents`; the edge-restriction keeps every vertex,
  so `V(G̃ ↾ Y) = V(G)`) plus `c ≥ numParts` from a components-refine-partition injection
  (label `↦` `walkable(rep)`, `InjOn` via `mem_walkable_iff` + `Set.encard_le_encard_of_injOn`).
  The injection's correctness is the private `label_eq_of_connBetween`: `f` is constant on
  each `G̃ ↾ Y` component, by `IsWalk` induction (each cons-edge is a within-part fiber).
  Stated on `mulTilde`/`numParts` directly (deficiency-side objects), not an abstract `H`.
  Building blocks all upstream in `apnelson1/Matroid`; no new mirror, axiom-free.

- **Piece 2 (`lem:weak-duality`) via the single-partition bound + `ciSup_le`.**
  `rank_add_partitionDef_le` proves `rank + def_P ≤ D(|V|−1)` for one labeling `f` by feeding
  `Union_pow_rk_eq` (Phase 13) on `X := E(G̃)`, `Y :=` non-crossing fibers `{p | p.1 ∈ E(G) ∧
  p.1 ∉ crossingEdges}` to get `rank ≤ D·r_cycle(Y) + |E(G̃)∖Y|`, then piece 1
  (`r_cycle(Y) ≤ |V| − numParts`) + the crossing-fiber count `|E(G̃)∖Y| = (D−1)·d_G(P)`
  (`ncard_crossing_fibers`, the `crossingEdges ×ˢ univ` ncard pattern). `rank M(G̃) =
  rk_Union(E(G̃))` via `rank_def` + `restrict_rk_eq`. `rank_add_deficiency_le` maximises by
  `ciSup_le` on the attainment API. **Needs `1 ≤ bodyBarDim n`** — false at `D=0` (FRICTION).
  *Lifted:* the `D=0`-degeneracy lesson → FRICTION.

- **Piece 3 (JJ09 reverse `def ≥ corank`) via the component partition of the Edmonds-optimal
  `Y₀`.** The reverse min–max direction translates the Edmonds optimal *edge subset* `Y₀`
  (existence half of `Union_pow_rk_eq`) into the deficiency *vertex partition*: `P =` the
  components of `G̃ ↾ Y₀`. Two facts make `P` attaining — `r_cycle(Y₀) + numParts f = |V|`
  *exactly* (`rk_add_numParts_componentLabel`: piece 1 gives `≤`, the reverse injection
  components→labels `numberOfComponents_le_numParts` gives `≥`), and every crossing edge's
  `D−1` fibers avoid `Y₀` (same-component endpoints ⇒ equal label), so `(D−1)d_G(P) ≤
  |E(G̃)∖Y₀|`. `nlinarith` over the Edmonds bound, the exact-vertex identity, and the
  crossing-fiber bound closes `rank ≥ D(|V|−1) − def_P`. Assembled with `lem:weak-duality`
  by `le_antisymm` into `rank_add_deficiency_eq` + base form `isBase_ncard_add_deficiency_eq`.
  Axiom-free; resolves risk #4 in full (no axiom, no deferral). The full `thm:def-eq-corank`
  is now green.

- **`componentLabel` factored through `pickVertex` (a function on the component *graph*)
  so constancy-on-a-component is a `congrArg`.** `componentLabel H x = pickVertex (H.walkable x)`;
  since `ConnBetween x y ⇒ walkable x = walkable y` (`ConnBetween.walkable_eq_walkable`),
  `componentLabel H x = componentLabel H y` is `congrArg pickVertex …` — sidestepping the
  `dite`-motive trip that a direct `if h : V(walkable x).Nonempty …` form hits on rewriting
  the walkable set under the chosen `Exists.choose`. *Lifted:* → FRICTION.

## Blockers / open questions

- ~~**Boundary regime `ℓ = 2k = D`** (risk #2)~~: **resolved** by
  `matroidMG_indep_iff` — the `D`-fold cycle-matroid union +
  Tutte–Nash-Williams covers the boundary regime cleanly; no
  `CountMatroid.lean` (`ℓ < 2k`) involvement.
- **Externals: prove vs hypothesize** (risk #4) — **RESOLVED (user,
  2026-06-02): prove `thm:def-eq-corank` in-repo, axiom-free**, per the
  "fully formalize, not citation-stubbed" scope. The **upper-bound half**
  is already green (`lem:rank-matroidMG-le`, `rank M(G̃) ≤ D(|V|−1)`); the
  reverse direction (JJ09 Thm 6.1 / Cor 6.2 min–max — a vertex-partition
  attaining the rank) is now a sequenced multi-commit sub-plan (see
  *Hand-off*), NOT an axiom and NOT deferred to a downstream phase. Core
  machinery in hand: Edmonds matroid-partition rank (Phase 12,
  `Matroid/Constructions/Union.lean`) + `Union_pow_rank_eq` (Phase 13)
  over the same `D`-fold graphic union.

## Hand-off / next phase

All four definition nodes of `deficiency.tex` are green in `Molecular/Deficiency.lean`
(`Graph.matroidMG` / `matroidMG_indep_iff`; `Graph.partitionDef` / `Graph.deficiency` /
`numParts` / `crossingEdges` / `partitionDef_one`; `Graph.IsKDof` / `Graph.edgeFiber` /
`Graph.IsMinimalKDof`; `Graph.IsRigidSubgraph` / `Graph.IsProperRigidSubgraph`), plus five
structural lemmas: the restriction identity `matroidMG_restrict_mulTilde`
(`lem:matroid-restrict-subgraph`), the full KT 3.3 node `subgraph_minimality`
(`lem:subgraph-minimality`), the KT 3.1 cut-form node
`two_le_crossingEdges_of_isKDof_zero` (`lem:two-edge-conn`, with `cutLabeling` /
`numParts_cutLabeling`), the KT 3.4 matroidal-core node
`isSparse_diff_singleton_of_isCircuit` (`lem:circuit-rigid`: `X − e` is `(D,D)`-sparse /
an `M(G̃)`-basis of the circuit `X`), the rank upper bound `rank_matroidMG_le`
(`lem:rank-matroidMG-le`, the conjecture-relevant half of the corank bridge), and
**weak duality** `rank_add_partitionDef_le` / `rank_add_deficiency_le` (`lem:weak-duality`,
piece 2: `rank M(G̃) + def(G̃) ≤ D(|V|−1)`, i.e. `def ≤ corank`, via `Union_pow_rk_eq` +
piece 1 + the crossing-fiber count `ncard_crossing_fibers`; carries `1 ≤ bodyBarDim n`). The
deficiency-attainment API
(`bddAbove_range_partitionDef` / `partitionDef_le_deficiency` / `deficiency_nonneg`) is
also in place — the `iSup`-model `deficiency` is now a usable attained max, and "a partition
witnesses a deficiency lower bound" is one `partitionDef_le_deficiency` call.

The full equality `thm:def-eq-corank` is now green (`Graph.rank_add_deficiency_eq`
+ base form `isBase_ncard_add_deficiency_eq`), via `le_antisymm` of `lem:weak-duality`
(piece 2, `def ≤ corank`) and the JJ09 reverse `Graph.le_rank_add_deficiency`
(piece 3, `def ≥ corank`). **All `deficiency.tex` nodes are green.** Risk #4 is
resolved in full — proved in-repo, axiom-free, no deferral.

**`prop:rigidity-matrix-prop11` (inherited from Phase 18) is NOT closed by this.** Its
*matroidal* half (`def = corank M(G̃)`) is now green, but reconciling the honest analytic
rank form requires the *analytic* generic-rank equality `rank R(G,p) = D(|V|−1) − def(G̃)`
(JJ09 Thm 6.1 geometric side) — a wiring of the rigidity-matrix rank `R(G,p)` (Phase 18,
`Molecular/RigidityMatrix.lean`) to the matroid corank, a distinct object with no Lean yet.
Earlier hand-off prose claimed closing `thm:def-eq-corank` would flip prop11; that was
optimistic — prop11 needs this analytic link in addition. The node prose in
`rigidity-matrix.tex` is updated to flag the split (matroidal half done, analytic half
scheduled with the algebraic induction, Phase 21+).

**Next concrete step — CLOSE PHASE 19 (user decision, 2026-06-02).** The `deficiency.tex`
chapter is fully green; the user has ratified closing the phase and **relocating
`prop:rigidity-matrix-prop11` forward** out of the completed Phase-18 chapter. The closing
commit(s) do, on top of the standard per-commit checklist:

1. **Relocate `prop:rigidity-matrix-prop11` forward.** It is a top-of-DAG reconciliation
   corollary (KT Prop 1.1, stated in KT §1 as a signpost but dependent on the analytic
   generic-rank theorem); leaving a red node stranded in the otherwise-complete Phase-18
   `rigidity-matrix.tex` reads as "stuck in Phase 18". Remove the `\begin{proposition}`
   node (`rigidity-matrix.tex` ~ll. 248–286) and rewrite the §*Status* paragraph
   (~ll. 24–36) so the chapter reads as a **complete** Phase-18 chapter (no dangling red
   node, no "deferred to Phase 19"); fix the dangling `\cref{prop:rigidity-matrix-prop11}`
   in `deficiency.tex` (the "this bridge closes the reconciliation node" sentence) to a
   forward-pointing prose note. Re-home prop11 as a **planned Phase-21+ deliverable** of the
   algebraic-induction chapter in `notes/MolecularConjecture.md` (its analytic half =
   `rank R(G,p) = D(|V|−1) − def(G̃)`, the genericity/generic-max-rank argument deferred
   since Phase 15–16, lands with Claim 6.4); the node itself gets (re)created in that phase's
   chapter when Phase 21 opens. Run the blueprint static checks (`blueprint/verify.sh` +
   the `\uses`/`\cref` label check) so no reference dangles.
2. **Run the full phase-close checklist** (top-level `CLAUDE.md` *When this commit closes a
   phase*): flip the ROADMAP §19 row to ✓ and compress its §19 planning section to a
   one-paragraph summary + pointer to this file; sync the three user-facing surfaces
   (`README.md` *Project status*; `home_page/index.md` status prose + phase table;
   `intro.tex` phase-plan prose + enumerate + dep-graph-status line) flipping Phase 19 → ✓;
   re-read `deficiency.tex` end-to-end as a domain mathematician and collapse any accumulated
   per-commit formalization asides (basis-free-narration anti-pattern per `blueprint/CLAUDE.md`
   *Proof verbosity*); review project organization (re-skim ROADMAP / TACTICS-GOLF /
   TACTICS-QUIRKS / FRICTION; check this file against the lift-on-promotion threshold).
3. **Record the forward-scheduled deliverables in their homes**, so the hand-off contract
   stays honest: full KT 3.4 (`G[V(X)]` rigid, tightness *equality*; vertex-induced-subgraph
   construction — now unblocked, the JJ09 reverse `le_rank_add_deficiency` supplies the
   lower bound it waited on) and KT 3.5 (contraction preserves minimality, Case I engine)
   → **early Phase 20**; `prop:rigidity-matrix-prop11` → **Phase 21+**. These belong in
   `notes/MolecularConjecture.md` *Phase 20* / *Phase 21*, not stranded under closed Phase 19.

This may be one closing commit or split across two (e.g. relocation + checklist); use
judgment. Phase 20 (combinatorial induction → Theorem 4.9) is unblocked: `M(G̃)`, deficiency,
and the def = corank bridge are all green.
