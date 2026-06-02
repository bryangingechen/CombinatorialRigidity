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

**`def:graph-sparse` landed (green).** `BodyBar/TreePacking.lean` now ships the
`Graph`-native sparsity/tightness predicate under `namespace Graph`:
`Graph.spanningVerts G E'` (vertices incident to some bar of `E'`, with helpers
`mem_spanningVerts` + `spanningVerts_subset_vertexSet`), `Graph.IsSparse G k ℓ`
(`∀ E' ⊆ E(G), E'.Nonempty → E'.ncard + ℓ ≤ k * (G.spanningVerts E').ncard`),
`Graph.IsTight G k ℓ` (sparse + global equality `E(G).ncard + ℓ = k * V(G).ncard`),
and `IsTight.isSparse`. Edge-subset-indexed (the shape the union-independence
theorem needs), `Set`-side throughout, count written additively. The blueprint
`def:graph-sparse` node is green (`\lean{Graph.IsSparse, Graph.IsTight}`).
Build + lint + `blueprint/verify.sh` all clean. **Next:**
`thm:unionPow-cycle-indep-iff-sparse` (see *Next concrete commit* below).

**Rank adapter landed.** `CombinatorialRigidity/BodyBar/TreePacking.lean`
ships `Matroid.Union_pow_rank_eq` — the constant-family `Set`-side
specialization of the partition formula for `Matroid.Union (fun _ : Fin k ↦
M)`, in `Set`-`Y` / `ℕ` / `Set.ncard` / `[Finite]` idiom (collapses
`∑ᵢ r(Y) = k · r(Y)`, bridges `Finset.univ \ Y`.card ↦ `(univ \ ↑Y).ncard`,
weakens `[Fintype]` ↦ `[Finite]`). Its prerequisite, the indexed partition
formula `Matroid.Union_rank_eq` (the `Fin ι` generalization of
`matroid_partition'`, proved by the same `adjMap_rank_eq` +
`sum'_rk_eq_rk_sum` route), landed beside `matroid_partition'` in
`Matroid/Constructions/Union.lean`. The adapter is generic over `Matroid α`
and does **not** import `Matroid.Graphic`; the `Graph.cycleMatroid` consumer
will apply it with `M := G.cycleMatroid` in the next commit.

Three `body-bar.tex` tree-packing nodes remain red
(`thm:unionPow-cycle-indep-iff-sparse`, `thm:tutte-nash-williams`,
`cor:k-spanning-trees`); `def:graph-sparse` is now green. The adapter has no
dedicated blueprint node (internal glue).

**Next concrete commit:** `thm:unionPow-cycle-indep-iff-sparse` — a bar set is
independent in `⋃ⱼ G.cycleMatroid` (`k` copies) iff `G` restricted to it is
`(k, k)`-sparse (Whiteley Cor 3). This is the first commit that imports
`Matroid.Graphic` (the `cycleMatroid` source — import now unblocked, see
*Blockers*, resolved); it bridges `Union_pow_rank_eq` (constant-`k`-fold
partition rank, already landed) against the cycle-matroid rank formula
`r(E') = |V'| − c(E')` via `Graph.IsSparse`. **Confirm the precise
`|V'| − c(E')` rank shape on `Graph.cycleMatroid` first** (see *Blockers*,
`Graphic.lean` exposes an `eRk + 1 = …` connected-component form) — that
identification is the substantive content; this commit may be larger than one
session, so a reasonable smaller landing is the cycle-matroid rank lemma alone.

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
- **`Graph.cycleMatroid` rank formula.** `thm:unionPow-cycle-indep-iff-sparse`
  needs `r(E') = |V'| − c(E')` on the cycle matroid. `Graphic.lean` exposes
  `cycleMatroid_indep` (= `IsAcyclicSet`), `cycleMatroid_isBase`
  (= `IsMaximalAcyclicSet`), `cycleMatroid_isBasis`, and an `eRk + 1 =
  |V|.encard` connected-component form (line ~235); confirm the precise
  `|V'| − c(E')` shape once the import blocker above is cleared.
- **`k`-fold union shape — RESOLVED.** The adapter phrases the `k`-fold
  union as `Matroid.Union (fun _ : Fin k ↦ M)` (single `Matroid.Union`
  over a constant `Fin k` family), which the `adjMap_rank_eq` +
  `sum'_rk_eq_rk_sum` route consumes cleanly; the `∑ᵢ → k·` collapse is
  one `Finset.sum_const` step.

## Hand-off / next phase
<written when the phase finishes; what unlocks Phase 14.>
