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

**Cycle-matroid rank formula — `V(G)` form AND `spanningVerts` form landed (green build).**
`BodyBar/TreePacking.lean` imports `Matroid.Graphic` (blocker cleared by the fork re-pin)
and ships two `eRk`-form rank formulas:
- `Graph.cycleMatroid_eRk_add_numberOfComponents_restrict`: for `E' ⊆ E(G)`,
  `r(E') + c(G ↾ E') = V(G).encard` (component count over the **full** `V(G)`).
- `Graph.cycleMatroid_eRk_add_numberOfComponents_spanningVerts`: for `E' ⊆ E(G)`,
  `r(E') + c((G ↾ E') - Isol(G ↾ E')) = (spanningVerts E').encard` — the
  **`spanningVerts`-side** form the sparsity bridge consumes (isolated-vertex singleton
  components cancelled on both sides). Its core is the cancellation lemma
  `Graph.vertexSet_deleteVerts_isolatedSet_restrict`: `V(G ↾ E') \ Isol(G ↾ E') =
  spanningVerts E'` (no `E' ⊆ E(G)` hypothesis — `spanningVerts` and `restrict_inc`
  agree on `e ∈ E' ∧ G.Inc e x` directly). The `spanningVerts` formula reuses
  `cycleMatroid_deleteVerts_isolatedSet` (deleting isolated verts keeps the cycle
  matroid) so its `eRk` still equals `G.cycleMatroid.eRk E'`, then applies
  `eRank_cycleMatroid_add_numberOfComponents` to `(G ↾ E') - Isol(G ↾ E')`.

Both are internal glue (no dedicated blueprint node, like the rank adapter). Build + lint +
warning-scan clean. **Next:** finish `thm:unionPow-cycle-indep-iff-sparse` — the
`spanningVerts`-vs-`V(G)` cancellation (the substantive gap flagged in the prior hand-off)
is now closed; what remains is the `ℕ`-cast + count glue (`eRk`↦`rk`, `encard`↦`ncard`
under `[Finite]`, relate `c' ≥ 1` on non-empty `E'`, tie union-independence to rank =
`ncard`, then compose with `Union_pow_rank_eq`). See *Next concrete commit* below.

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
`cor:k-spanning-trees`); `def:graph-sparse` is now green. The rank adapter, both
cycle-matroid rank formulas (`restrict` / `spanningVerts`), and the cancellation lemma are all
internal glue with no dedicated blueprint node.

**Next concrete commit:** finish `thm:unionPow-cycle-indep-iff-sparse` — a bar set
is independent in `⋃ⱼ G.cycleMatroid` (`k` copies) iff `G` restricted to it is
`(k, k)`-sparse (Whiteley Cor 3). The two halves it bridges have both landed:
`Union_pow_rank_eq` (constant-`k`-fold partition rank) and now
`cycleMatroid_eRk_add_numberOfComponents_restrict` (`V(G)`-form rank formula), and now
`cycleMatroid_eRk_add_numberOfComponents_spanningVerts` (`spanningVerts`-form,
`r(E') + c'(E') = |spanningVerts E'|`, with the `spanningVerts`-vs-`V(G)` cancellation
already discharged via `vertexSet_deleteVerts_isolatedSet_restrict`). Remaining work is the
`ℕ`-cast + count glue, with **no** `spanningVerts`-vs-`V(G)` gap left to fight:
1. Cast `eRk`↦`rk` and `encard`↦`ncard` in the `spanningVerts` formula (both finite under
   `[Finite β]` and `spanningVerts E' ⊆ V(G)`).
2. Use `c'(E') ≥ 1` on non-empty `E'` to turn the rank identity into the additive
   `(k,k)`-sparsity inequality `|E'| + k ≤ k·|spanningVerts E'|`.
3. Tie union-independence to full rank (`(Union …).Indep I ↔ rk I = |I|`) and compose with
   `Union_pow_rank_eq` applied at `Y = I` to get the `iff`.

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
- [ ] `thm:unionPow-cycle-indep-iff-sparse` — independence in the
  `k`-fold cycle-matroid union ⟺ `(k,k)`-sparse (Whiteley Cor 3). Rank formulas + adapter all
  landed; remaining is the `ℕ`-cast + `c' ≥ 1` count glue (no `spanningVerts`-vs-`V(G)` gap left).
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
<written when the phase finishes; what unlocks Phase 14.>
