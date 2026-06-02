# Phase 19 — `M(G̃)`, deficiency, `k`-dof graphs (work log)

**Status:** in progress (all four definition nodes + four structural lemmas
+ the rank upper bound landed: `lem:matroid-restrict-subgraph`,
`lem:subgraph-minimality` (KT 3.3), `lem:two-edge-conn` (KT 3.1, cut form),
`lem:circuit-rigid` (KT 3.4, matroidal core), `lem:rank-matroidMG-le`
(conjecture-relevant half of `thm:def-eq-corank`); the full `thm:def-eq-corank`
equality is the one remaining node).

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

Next concrete step: the full `thm:def-eq-corank` equality (JJ09 min–max reverse direction).

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
- [ ] `thm:def-eq-corank` — the def = corank bridge (JJ09 Thm 6.1 /
  Cor 6.2): `|B| + def(G̃) = D(|V|−1)`. Full equality still red; the
  conjecture-relevant upper-bound half is `lem:rank-matroidMG-le` below.
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

- **`thm:def-eq-corank` split: prove the upper bound, defer the JJ09 reverse (risk #4).**
  The full equality `|B| + def(G̃) = D(|V|−1)` is a min–max duality (Edmonds rank over
  edge-subsets vs deficiency over vertex-partitions) — the hard JJ09 generic-rank content.
  Per risk #4 the conjecture (Thm 5.6) needs only the **upper-bound half**
  `rank M(G̃) ≤ D(|V|−1)`, which landed as `lem:rank-matroidMG-le` (`Matroid.rank_def` +
  `rk_le_iff` + `matroidMG_indep_iff` sparsity, applied to the base itself). Decision: keep
  `thm:def-eq-corank` (full equality) red; the reverse direction (a partition attaining the
  rank) is deferred until a downstream node demands the full equality rather than the bound.

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
an `M(G̃)`-basis of the circuit `X`), and the rank upper bound `rank_matroidMG_le`
(`lem:rank-matroidMG-le`, the conjecture-relevant half of the corank bridge). The
deficiency-attainment API
(`bddAbove_range_partitionDef` / `partitionDef_le_deficiency` / `deficiency_nonneg`) is
also in place — the `iSup`-model `deficiency` is now a usable attained max, and "a partition
witnesses a deficiency lower bound" is one `partitionDef_le_deficiency` call.

The one remaining `deficiency.tex` node is the **full** equality `thm:def-eq-corank`
(its conjecture-relevant upper-bound half is green as `lem:rank-matroidMG-le`; the KT 3.4
matroidal core is green as `lem:circuit-rigid`). **Decision is settled (risk #4, see
Blockers): prove it in-repo, axiom-free.** It is a sequenced multi-commit sub-plan — do the
next *unfinished* piece each commit, not the whole bridge at once:

1. **Partition-respecting `cycleMatroid` component-rank bound.** For a labeling `f : α → α`
   (the `partitionDef` partition model) and the within-part edge set `Y`, the graphic-matroid
   rank `r_cycle(Y) ≤ |V| − numParts f` (rank ≤ vertices − components, components ≥ #parts).
   No existing project/mathlib lemma covers the labeling-encoded partition; this is the new
   leaf the weak-duality half bottoms out on. Likely its own commit (possibly a small
   `Graph`/`cycleMatroid` helper or a mirror lemma).
2. **Weak duality `rank M(G̃) + def(G̃) ≤ D(|V|−1)`** (equivalently `def ≤ corank`), summing
   per-part sparsity / piece-1's component bound over the `D`-fold union with the `(D−1)`-fiber
   multiplicity bookkeeping. Pairs with the already-green `lem:rank-matroidMG-le`.
3. **The JJ09 reverse (`def ≥ corank`): a vertex-partition attaining the rank**, via Edmonds
   matroid-partition rank (Phase 12 `Matroid/Constructions/Union.lean`) + `Union_pow_rank_eq`
   (Phase 13) over the `D`-fold graphic union — translating Edmonds' optimal *edge subset* into
   the deficiency *vertex partition*. Then assemble `|B| + def(G̃) = D(|V|−1)`, flip
   `thm:def-eq-corank` green.

Each piece is a normal forward-mode commit (Lean + blueprint node/`\leanok` + notes). If piece 1
or 3 itself proves to be multi-commit on contact, split it and keep going. Closing
`thm:def-eq-corank` also flips the Phase-18-inherited `prop:rigidity-matrix-prop11`. Two further
pieces are still deferred behind the full equality and are **early-Phase-20** deliverables, not
Phase 19: (i) the *full* KT 3.4 (`G[V(X)]` rigid, the tightness *equality* `|X−e| =
D(|V(X)|−1)`), which needs a vertex-induced-subgraph-from-an-edge-set construction (no existing
`Graph α β` analogue); (ii) KT 3.5 (rigid-subgraph contraction preserves minimality — Case I
engine).

Phase 20 (combinatorial induction → Theorem 4.9) is unblocked once `M(G̃)`, deficiency,
and the def = corank bridge are all green.
