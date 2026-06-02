# Phase 13 — Tutte–Nash-Williams tree-packing (work log)

**Status:** ✓ complete. All four owned `body-bar.tex` tree-packing nodes are green
(`def:graph-sparse`, `thm:unionPow-cycle-indep-iff-sparse`, `thm:tutte-nash-williams`,
`cor:k-spanning-trees`). Build + lint + `blueprint/verify.sh` clean. Unblocks Phase 14.

This phase specializes Phase 12's Edmonds matroid-partition theorem to
`k` copies of `Graph.cycleMatroid`, recovering the **Tutte–Nash-Williams
tree-packing theorem** (Tutte 1961, Nash-Williams 1961): a multigraph is
the edge-disjoint union of `k` forests iff it is `(k,k)`-sparse, with a
spanning-tree refinement under `(k,k)`-tightness. It is the second link
of the body-bar chain opened in Phase 12:

| Phase | Content |
|---|---|
| 12 (done) | submodular → matroid; matroid union / Edmonds partition |
| **13** (this) | Tutte–Nash-Williams tree-packing; `Graph`-native `(k,ℓ)`-sparsity |
| 14 | `k`-frame matroid = `k`-fold cycle-matroid union (Whiteley Thm 1) |
| 15 | body-bar frameworks + Tay's theorem (existence form) |

**Workflow:** forward-mode. The blueprint chapter
`blueprint/src/chapter/body-bar.tex` (its *Tree-packing as a corollary*
subsection, `def:graph-sparse` through `cor:k-spanning-trees`) is the
authoritative dep-graph and lemma index; this file carries everything
else. The body-bar chapter is shared across Phases 13–15; Phase 13 owns
the `def:graph-sparse` / `thm:unionPow-cycle-indep-iff-sparse` /
`thm:tutte-nash-williams` / `cor:k-spanning-trees` nodes.

**References** (all classical; verify per `../CLAUDE.md` *Referencing
prior work* before citing in blueprint/notes):
- Tutte 1961, *On the problem of decomposing a graph into n connected
  factors* — tree-packing.
- Nash-Williams 1961, *Edge-disjoint spanning trees of finite graphs* —
  tree-packing (independent).
- Edmonds 1965, *Minimum partition of a matroid into independent
  subsets* — the partition theorem we specialize (Phase 12).
- Oxley 2011, *Matroid Theory* (2nd ed.) — matroid-theory cross-check
  (`.refs/oxley-2011-matroid-theory.pdf`).

## Current state

✓ Complete. All four owned `body-bar.tex` tree-packing nodes are green; the
per-node lemma map is the *Lemma checklist* below, and the per-commit narrative
is the commit log (`git log --oneline`, `feat(phase13):` from `4b1cbc8` through
`6fade93`). `BodyBar/TreePacking.lean` ships the full Phase-13 surface:

- the `Graph`-native `(k,ℓ)`-sparsity/tightness predicate (`def:graph-sparse`),
- the two `eRk`-form cycle-matroid rank formulas (full-`V(G)` and
  `spanningVerts`-side, the latter via the isolated-vertex cancellation lemma)
  and the `ℕ`/`ncard` rank-bound corollaries — internal glue, no blueprint node,
- the `k`-fold-union rank adapter (`Matroid.Union_pow_rank_eq` /
  `_rk_eq` / `_indep_iff_count`, generic over `Matroid α`, beside
  `matroid_partition'` / in `TreePacking.lean`),
- the union-independence ⟺ sparsity iff
  (`unionPow_cycleMatroid_indep_iff_isSparse_restrict`: easy graphic half +
  forward + hard reverse via component decomposition, assembled),
- Tutte–Nash-Williams (`tutte_nash_williams`),
- the spanning-tree refinement (`isSpanningTreePacking_of_isTight`).

Build + lint + `blueprint/verify.sh` all clean.

## Architectural choices made up front

- **Carrier = mathlib core `Graph α β`** (the `apnelson1/Matroid`
  `cycleMatroid` carrier), not `SimpleGraph`. Phases 1–11 stay on
  `SimpleGraph`. See `../ROADMAP.md` §13/§15 and `../DESIGN.md`
  *Migrating Phases 1–11 …* (decided against wholesale migration).
- **`Graph`-native `(k,ℓ)`-sparsity is fresh, defined `Set`-side**
  (`Set.ncard` of edge sets, `ℕ`, `[Finite]`) — **not** migrated from
  the Phase 9/10 `SimpleGraph` `IsSparse`. One conversion layer
  (sparsity-count ↔ matroid-rank), not two. See `../DESIGN.md`
  *Set/Finset and rank-flavor boundary …* item 1.
- **Graph-level defs under `namespace Graph`** (dot-notation on
  `G : Graph α β`, beside `Graph.cycleMatroid`). See `../ROADMAP.md` §15.

## Lemma checklist

Leaf-level to-do list is the `body-bar.tex` dep-graph (four red
tree-packing nodes as of phase open).

- [x] **Rank adapter** (no dedicated blueprint node; internal glue) —
  `Matroid.Union_pow_rank_eq`, `Set`/`ℕ`/`ncard`/`[Finite]` restatement of
  the partition formula for the constant `k`-fold union, in
  `BodyBar/TreePacking.lean`. Built generic over `Matroid α` (cycleMatroid
  is its first consumer, applied directly). Its prerequisite
  `Matroid.Union_rank_eq` (indexed generalization of `matroid_partition'`)
  landed in `Matroid/Constructions/Union.lean`.
- [x] `def:graph-sparse` — `Graph` `(k,ℓ)`-sparsity + tightness,
  `Set`-side, edge-subset-indexed (`Graph.IsSparse` / `Graph.IsTight` /
  `Graph.spanningVerts` in `BodyBar/TreePacking.lean`).
- [x] **Cycle-matroid rank formula** (`eRk` form; no blueprint node, internal glue) — two forms in
  `BodyBar/TreePacking.lean`: `Graph.cycleMatroid_eRk_add_numberOfComponents_restrict`
  (`r(E') + c(G ↾ E') = |V(G)|`, full vertex set) and
  `Graph.cycleMatroid_eRk_add_numberOfComponents_spanningVerts`
  (`r(E') + c((G ↾ E') - Isol(G ↾ E')) = |spanningVerts E'|`, the sparsity-side form), the latter
  via the cancellation lemma `Graph.vertexSet_deleteVerts_isolatedSet_restrict`
  (`V(G ↾ E') \ Isol(G ↾ E') = spanningVerts E'`). The `r(E') = |V'| − c(E')` half of
  `thm:unionPow-cycle-indep-iff-sparse`, now in `spanningVerts` shape.
- [x] `thm:unionPow-cycle-indep-iff-sparse` — independence in the
  `k`-fold cycle-matroid union ⟺ `(k,k)`-sparse (Whiteley Cor 3), green:
  `Graph.unionPow_cycleMatroid_indep_iff_isSparse_restrict`. Matroid-side half
  (`Matroid.Union_pow_indep_iff_count`), easy graphic half
  (`Graph.isSparse_of_forall_le_cycleMatroid_rk`), forward
  (`Graph.isSparse_restrict_of_union_pow_indep`), and hard reverse via component decomposition
  (`Graph.le_mul_cycleMatroid_rk_of_isSparse_restrict`) all landed; assembled iff composes the
  forward half with `Union_pow_indep_iff_count` fed by the reverse count lemma.
- [x] `thm:tutte-nash-williams` — edge-disjoint union of `k` forests ⟺
  `(k,k)`-sparse, green: `Graph.tutte_nash_williams` (with the internal-glue
  packing predicate `Graph.IsForestPacking`). Bridges union-independence at
  `E' = E(G)` (`unionPow_cycleMatroid_indep_iff_isSparse_restrict` + `restrict_self`)
  to the acyclic cover (`Matroid.union_indep_iff` + `cycleMatroid_indep`); disjointness
  free via `Fintype.exists_disjointed_le` + `IsAcyclicSet.anti`.
- [x] `cor:k-spanning-trees` — under connectivity + `(k,k)`-tightness the `k` forests
  are spanning trees, green: `Graph.isSpanningTreePacking_of_isTight` (with internal-glue
  predicate `Graph.IsSpanningTreePacking` and per-copy core
  `Graph.isMaximalAcyclicSet_of_isForestPacking_of_isTight`). Conclusion phrased as a per-copy
  maximal-acyclic-set (= base of `cycleMatroid`; spanning tree on connected `G` via
  `IsMaximalAcyclicSet.isTree`); connectivity required for the spanning-tree framing.

## Decisions made during this phase

- **Spanning-tree conclusion = per-copy maximal acyclic set + connectivity hypothesis.**
  `cor:k-spanning-trees`'s "spanning tree" is `G.IsMaximalAcyclicSet (Fs i)` (= base of
  `cycleMatroid`), upgraded to a literal tree via `IsMaximalAcyclicSet.isTree` only on a connected
  `G`. The corollary therefore takes `hconn : G.Connected`: with `ℓ = k` tightness and `c(G) > 1`
  the rank `r = |V| − c < |V| − 1`, so the per-copy `|Fs i| = r` equality cannot give a `|V|−1`-edge
  spanning tree. Blueprint statement + the (deferred) `thm:tay-witness` updated to state connectivity
  explicitly.

## Blockers / open questions

- **`Matroid.Graphic` import was broken — RESOLVED (fork re-pin).**
  Importing `Matroid.Graphic` (the `cycleMatroid` source) transitively
  pulls `apnelson1/Matroid`'s `Matroid/Uniform/Basic.lean`, whose
  `unifOn_rankPos_iff` (line 104) `simp` no longer closed its goal under
  our mathlib pin (mathlib-master drift; `unsolved goals`). Pin-bumping was
  ruled out (upstream `origin/main` is 7 wip commits ahead with
  `Uniform/Basic.lean` unchanged, so the breakage persists at HEAD), and
  local vendoring of `cycleMatroid` is impractical (~2280-job transitive
  closure). **Fix:** a one-commit fork off our exact pin `e6852ce` —
  `bryangingechen/Matroid` branch `combinatorial-rigidity-fix`, commit
  `08d517f`, replacing the broken `simp` with an explicit positivity
  `rw` chain. `lakefile.toml` + `lake-manifest.json` now pin that fork;
  **mathlib rev is unchanged (`21b745f`)**, so Phases 1–12 are unaffected.
  No upstream PR by request (trivial; upstream tracks mathlib master and
  will resolve it eventually). Retire the fork once upstream re-greens.
  The fix verified: `Matroid.Graphic` and the full project build green.
- **`Graph.cycleMatroid` rank formula — RESOLVED.** The needed `r(E') = |V'| − c(E')`
  identity landed as `cycleMatroid_eRk_add_numberOfComponents_restrict` (`eRk`/`encard`
  form, `r(E') + c(G ↾ E') = |V|`). It specializes `Graphic.lean`'s
  `eRank_cycleMatroid_add_numberOfComponents` (the `eRk + c = |V|.encard` form, applied
  to `G ↾ E'`) to the rank of a subset, through `cycleMatroid_restrict` +
  `Matroid.eRank_restrict`. **The `spanningVerts`-vs-`V(G)` bridge is now also RESOLVED:**
  `cycleMatroid_eRk_add_numberOfComponents_spanningVerts` gives the `spanningVerts`-side form
  `r(E') + c((G ↾ E') - Isol(G ↾ E')) = |spanningVerts E'|`, via the cancellation lemma
  `vertexSet_deleteVerts_isolatedSet_restrict` (`V(G ↾ E') \ Isol(G ↾ E') = spanningVerts E'`)
  + `cycleMatroid_deleteVerts_isolatedSet` (deleting isolated verts keeps the cycle matroid).
  The isolated-vertex singleton components cancel on both sides, so the next commit consumes
  the `spanningVerts` form directly with no further cancellation work.
- **`k`-fold union shape — RESOLVED.** The adapter phrases the `k`-fold
  union as `Matroid.Union (fun _ : Fin k ↦ M)` (single `Matroid.Union`
  over a constant `Fin k` family), which the `adjMap_rank_eq` +
  `sum'_rk_eq_rk_sum` route consumes cleanly; the `∑ᵢ → k·` collapse is
  one `Finset.sum_const` step.

## Hand-off / next phase

Phase 13 is complete: `BodyBar/TreePacking.lean` ships the `Graph`-native
`(k,ℓ)`-sparsity/tightness predicate, the `k`-fold-union rank adapter, the
union-independence ⟺ sparsity iff (`unionPow_cycleMatroid_indep_iff_isSparse_restrict`),
Tutte–Nash-Williams (`tutte_nash_williams`), and the spanning-tree refinement
(`isSpanningTreePacking_of_isTight`). All four owned `body-bar.tex` nodes green.

**Unlocks Phase 14** (`k`-frame matroid = `k`-fold cycle-matroid union, Whiteley Thm 1;
`BodyBar/KFrame.lean`, scoped in `body-bar.tex`'s `thm:k-frame-union-cycle` node). Phase 14's
matroid-union target is exactly `Matroid.Union (fun _ : Fin k ↦ G.cycleMatroid)`, the union object
Phase 13 already characterizes — so Phase 14 builds the linear `k`-frame matroid `F(G,X)` (via
`Matroid.ofFun` over indeterminate two-extensor coefficients) and proves it equals that union by
Whiteley's column-reorder / monomial argument (§2.1). **Smallest first commit:** open
`notes/Phase14.md` + define `F(G,X)` (the `Matroid.ofFun` linear matroid on `E(G)` from the
indeterminate body-bar row map), flipping the `body-bar.tex` `def:k-frame-matroid` node; assess the
union-equality proof once the definition's `Matroid.ofFun` indep-characterization is in hand.
