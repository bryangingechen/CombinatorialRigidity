/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Induction.Operations

/-!
# Girth and the spanning short-cycle lemma (`sec:pencil-girth-chain`)

Phase 39 (PENCIL), Lean track: leaves **G1** and **G2** of the girth-and-chain design pass
(`notes/Phase39-design.md` § *Lean-track design pass (2026-09-15): checklist items 1–2*),
pinning `def:girth` and `lem:pencil-short-cycle-spanning` of
`blueprint/src/chapter/pencil.tex` § *Girth and degree-two chains under no proper rigid
subgraph*. G3 (girth forced by a degree-`≥ 3` vertex) and G4 (closed-neighbourhood
intersections) are not yet built here.

* `Graph.GirthGE` (`def:girth`): a *predicate* form of girth — `G` has girth at least `g`
  when no cycle of length `m` with `3 ≤ m < g` embeds in `G` — with its two monotonicities
  `Graph.GirthGE.mono` (a subgraph's girth is at least its supergraph's) and `Graph.GirthGE.anti`
  (a weaker lower bound is implied by a stronger one). The carrier is `Fin m`-indexed cyclic
  data (design-pass verdict V1), matching every cycle producer/consumer already in the tree
  (`isKDof_zero_of_cycle`, `cycle_isProperRigidSubgraph`) rather than the `apnelson1/Matroid`
  package's graph-level `IsCycle`/`IsCyclicWalk` or mathlib's `SimpleGraph.girth : ℕ∞`.
* `Graph.range_vtx_eq_vertexSet_of_cycle_of_noRigid` (`lem:pencil-short-cycle-spanning`): under
  "no proper rigid subgraph" (`n`-dof regime, `D = bodyBarDim n ≥ 3`), any cycle short enough to
  fit inside the `D`-dof regime (`3 ≤ m ≤ D`) must already span all of `V(G)` — else its
  vertex-induced subgraph, restricted to exactly the cycle's own edges (`(G ↾ range edge)[range
  vtx]`, so no chord is kept), would itself be a proper rigid subgraph
  (`isKDof_zero_of_cycle` + the `2 ≤ |V(H)|` / properness bookkeeping of
  `cycle_isProperRigidSubgraph`'s template), contradicting `hnp`.
-/

namespace Graph

open Set

variable {α β : Type*}

/-! ## The girth predicate and its monotonicities (`def:girth`, G1) -/

/-- `G` has girth at least `g`: no cycle on `m` vertices with `3 ≤ m < g` (`def:girth`). Stated
against `Fin m`-indexed cyclic data — injective `vtx`/`edge` with the cyclic links `edge i :
vtx i — vtx (i + 1)` — matching every cycle producer/consumer in the tree. Only cycles on `≥ 3`
vertices are counted, as usual (loops and parallel pairs are excluded by construction, since
`m ≥ 3`). -/
def GirthGE (G : Graph α β) (g : ℕ) : Prop :=
  ∀ ⦃m : ℕ⦄ (hm : 3 ≤ m) ⦃vtx : Fin m → α⦄ ⦃edge : Fin m → β⦄,
    Function.Injective vtx → Function.Injective edge →
    (∀ i : Fin m, G.IsLink (edge i) (vtx i) (vtx (i + ⟨1, by omega⟩))) → g ≤ m

/-- A subgraph's girth is at least its supergraph's: any cycle inside `H` is a cycle inside `G`
(links transport up along `H ≤ G` via `Graph.IsLink.of_le`), so `G`'s girth bound refutes any
cycle short enough to live in `H`. -/
theorem GirthGE.mono {G H : Graph α β} {g : ℕ} (hle : H ≤ G) (hG : G.GirthGE g) :
    H.GirthGE g :=
  fun _ hm _ _ hv he hl => hG hm hv he fun i => (hl i).of_le hle

/-- Girth `≥ g` implies girth `≥ g'` for any `g' ≤ g`: any cycle short enough to violate the
weaker bound would already violate the stronger one. -/
theorem GirthGE.anti {G : Graph α β} {g g' : ℕ} (hgg : g' ≤ g) (hG : G.GirthGE g) :
    G.GirthGE g' :=
  fun _ hm _ _ hv he hl => hgg.trans (hG hm hv he hl)

/-! ## A short cycle spans, under "no proper rigid subgraph" (`lem:pencil-short-cycle-spanning`,
G2) -/

/-- **A short cycle spans** (`lem:pencil-short-cycle-spanning`): if `G` has no proper rigid
subgraph in the `n`-dof regime (`D = bodyBarDim n ≥ 3`) and carries a cycle of length `m` with
`3 ≤ m ≤ D`, that cycle's vertex set is already all of `V(G)`.

The vertex-induced subgraph on `range vtx`, first restricted to exactly the cycle's own edges
(`H := (G ↾ range edge)[range vtx]`, so no chord survives — `G.induce (range vtx)` alone would
keep them), is `0`-dof by `isKDof_zero_of_cycle` and has `2 ≤ |V(H)|` by `hm` and injectivity of
`vtx`. If `range vtx` were a proper subset of `V(G)`, `H` would be a proper rigid subgraph,
contradicting `hnp`; `range vtx ⊆ V(G)` always holds (`(hlink i).left_mem`), so equality follows
from `ssubset_of_ne` by contradiction. -/
theorem range_vtx_eq_vertexSet_of_cycle_of_noRigid [Finite α] {G : Graph α β} {n : ℕ}
    (hD : 3 ≤ bodyBarDim n) (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n)
    {m : ℕ} (hm : 3 ≤ m) (hmD : m ≤ bodyBarDim n)
    {vtx : Fin m → α} {edge : Fin m → β}
    (hvtx : Function.Injective vtx) (hedge : Function.Injective edge)
    (hlink : ∀ i : Fin m, G.IsLink (edge i) (vtx i) (vtx (i + ⟨1, by omega⟩))) :
    Set.range vtx = V(G) := by
  classical
  have hsub : Set.range vtx ⊆ V(G) := by
    rintro x ⟨i, rfl⟩
    exact (hlink i).left_mem
  set H : Graph α β := (G.restrict (Set.range edge)).induce (Set.range vtx) with hHdef
  have hsub' : Set.range vtx ⊆ V(G.restrict (Set.range edge)) := hsub
  have hHle : H ≤ G := (induce_le hsub').trans restrict_le
  have hVH : V(H) = Set.range vtx := vertexSet_induce _ _
  have hEH : E(H) = Set.range edge := by
    rw [hHdef, edgeSet_induce]
    apply Set.Subset.antisymm
    · rintro e ⟨x, y, ⟨he, -⟩, -, -⟩
      exact he
    · rintro e ⟨j, rfl⟩
      exact ⟨vtx j, vtx (j + ⟨1, by omega⟩), ⟨⟨j, rfl⟩, hlink j⟩, ⟨j, rfl⟩,
        ⟨j + ⟨1, by omega⟩, rfl⟩⟩
  have hlink' : ∀ i : Fin m, H.IsLink (edge i) (vtx i) (vtx (i + ⟨1, by omega⟩)) := by
    intro i
    rw [hHdef, induce_isLink, restrict_isLink]
    exact ⟨⟨⟨i, rfl⟩, hlink i⟩, ⟨i, rfl⟩, ⟨i + ⟨1, by omega⟩, rfl⟩⟩
  have hKDof : H.IsKDof n 0 := isKDof_zero_of_cycle hD hm hmD hedge hlink' hVH hEH
  have hcard : 2 ≤ V(H).ncard := by
    rw [hVH, Set.ncard_range_of_injective hvtx, Nat.card_fin]; omega
  by_contra hne
  exact hnp H ⟨⟨hHle, hKDof⟩, hcard, by rw [hVH]; exact hsub.ssubset_of_ne hne⟩

end Graph
