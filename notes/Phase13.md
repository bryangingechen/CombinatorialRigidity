# Phase 13 — Tutte–Nash-Williams tree-packing (work log)

**Status:** in progress.

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

**Just opened.** No Lean yet; the four `body-bar.tex` tree-packing nodes
(`def:graph-sparse`, `thm:unionPow-cycle-indep-iff-sparse`,
`thm:tutte-nash-williams`, `cor:k-spanning-trees`) are red and form the
to-do list. The phase-open commit is docs-only (status surfaces synced;
this file created), mirroring Phase 12's Layer-0 pattern — the blueprint
chapter was already populated when Phase 12 scoped Phases 13–15.

**Next concrete commit:** the *thin rank adapter* — open a new file
`CombinatorialRigidity/BodyBar/TreePacking.lean` that restates Phase 12's
`matroid_partition'` (and/or `matroid_partition_eRk'`) for the `k`-fold
union of `Graph.cycleMatroid` in `Set`-`Y` / `ℕ` / `Set.ncard` /
`[Finite]` idiom, absorbing the `rk`/`eRk`/`ncard` + `Fintype`/
`DecidableEq`/finite-rank plumbing once. Per `../DESIGN.md` *Set/Finset
and rank-flavor boundary at the matroid layer (Phases 13–15)* item 2, the
adapter is built now (at phase open, against the real first consumer),
not speculatively earlier. Then `def:graph-sparse` (`Set`-side per that
DESIGN note, item 1), then the two theorems + corollary.

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

- [ ] **Rank adapter** (no dedicated blueprint node; internal glue) —
  `Set`/`ℕ`/`ncard`/`[Finite]` restatement of `matroid_partition'` for
  the `k`-fold `Graph.cycleMatroid` union. In
  `BodyBar/TreePacking.lean`.
- [ ] `def:graph-sparse` — `Graph` `(k,ℓ)`-sparsity + tightness,
  `Set`-side.
- [ ] `thm:unionPow-cycle-indep-iff-sparse` — independence in the
  `k`-fold cycle-matroid union ⟺ `(k,k)`-sparse (Whiteley Cor 3).
- [ ] `thm:tutte-nash-williams` — edge-disjoint union of `k` forests ⟺
  `(k,k)`-sparse.
- [ ] `cor:k-spanning-trees` — under `(k,k)`-tightness the `k` forests
  are spanning trees.

## Decisions made during this phase

<none yet — phase just opened. Flat list is fine for a phase this size;
sub-organize only if it grows cleanup passes.>

## Blockers / open questions

- **`Graph.cycleMatroid` rank formula.** `thm:unionPow-cycle-indep-iff-sparse`
  needs `r(E') = |V'| − c(E')` on the cycle matroid. Confirm what the
  `apnelson1/Matroid` `Graphic.lean` API exposes (rank / circuit / basis
  = forest characterizations) before stating the bridge; may need a
  small mirror lemma if the rank-as-`|V|−c` form isn't directly there.
- **`k`-fold union shape.** Whether to phrase the `k`-fold union as an
  iterated `Matroid.union` or a single `Matroid.Union` over `Fin k` of a
  constant family — pick whichever the Phase-12 partition theorem's
  signature consumes most cleanly when the adapter is built.

## Hand-off / next phase
<written when the phase finishes; what unlocks Phase 14.>
