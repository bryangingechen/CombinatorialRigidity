/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Induction.Operations

/-!
# Girth, spanning short cycles, and the girth bound at a hub (`sec:pencil-girth-chain`)

Phase 39 (PENCIL), Lean track: leaves **G1**, **G2** and **G3** of the girth-and-chain design pass
(`notes/Phase39-design.md` § *Lean-track design pass (2026-09-15): checklist items 1–2*),
pinning `def:girth`, `lem:pencil-short-cycle-spanning` and `lem:pencil-girth-of-hub` of
`blueprint/src/chapter/pencil.tex` § *Girth and degree-two chains under no proper rigid
subgraph*. G4 (closed-neighbourhood intersections at girth `≥ 5`) lives with `closedNbhd` in
`Molecule/Pencil/Motive.lean` and is not built here.

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
* `Graph.girthGE_of_noRigid_of_three_le_degree` (`lem:pencil-girth-of-hub`): in the same regime,
  a single vertex of degree `≥ 3` forces girth `≥ D + 1`. Any shorter cycle spans by the previous
  lemma, so the hub lies on it and its third edge is a chord; the arc the chord cuts off is a
  strictly shorter cycle, still long enough and short enough for the previous lemma, but no
  longer spanning.
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

/-! ## Girth exceeds `D` once some vertex has degree three (`lem:pencil-girth-of-hub`, G3) -/

/-- **A vertex of degree `≥ 3` forces girth `> D`** (`lem:pencil-girth-of-hub`): a simple graph
with no proper rigid subgraph in the `n`-dof regime (`D = bodyBarDim n ≥ 3`) and a vertex `w` of
degree at least three has girth at least `D + 1`.

Suppose a cycle on `m` vertices with `3 ≤ m ≤ D`. By `range_vtx_eq_vertexSet_of_cycle_of_noRigid`
it spans, so `w = vtx i₀` for some index and every other vertex is on it too. A third edge `g` at
`w`, distinct from the two cycle edges `edge i₀` and `edge (i₀ - 1)` there
(`exists_isLink_not_eq_of_three_le_degree`), is then distinct from *every* cycle edge (an edge
with `vtx i₀` as an endpoint is `edge t` only for `t ∈ {i₀, i₀ - 1}`, by injectivity of `vtx` and
`IsLink.eq_and_eq_or_eq_and_eq`), and its far end is `vtx j` with `j ∉ {i₀ - 1, i₀, i₀ + 1}` —
`j = i₀` is a loop, and either neighbour would make `g` parallel to a cycle edge
(`Simple.eq_of_isLink`). So `g` is a chord, and writing `j = i₀ + c` the arc
`vtx (i₀ + 0), …, vtx (i₀ + c)` closed by `g` is a cycle on `c.val + 1` vertices with
`3 ≤ c.val + 1 ≤ m - 1 ≤ D`. That cycle must span too, forcing `c.val + 1 = |V(G)| = m` —
impossible.

The re-indexing is the only delicate part: the arc lives on `Fin (c.val + 1)` while the ambient
cycle lives on `Fin m`, and the two moduli are bridged by `Fin.castLE` plus `Fin.val_add`
computations at the two ends of the arc (the successor of an interior index does not wrap, the
successor of the last one wraps to `0`). -/
theorem girthGE_of_noRigid_of_three_le_degree [Finite α] [Finite β] {G : Graph α β}
    [G.Simple] {n : ℕ} (hD : 3 ≤ bodyBarDim n)
    (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n)
    {w : α} (hw : 3 ≤ G.degree w) :
    G.GirthGE (bodyBarDim n + 1) := by
  classical
  intro m hm vtx edge hvtx hedge hlink
  by_contra hcon
  have hmD : m ≤ bodyBarDim n := by omega
  have : NeZero m := ⟨by omega⟩
  have hspan : Set.range vtx = V(G) :=
    range_vtx_eq_vertexSet_of_cycle_of_noRigid hD hnp hm hmD hvtx hedge hlink
  -- The cycle spans, so `w` lies on it.
  obtain ⟨g₀, z₀, hgz₀, -, -⟩ :=
    exists_isLink_not_eq_of_three_le_degree hw (edge 0) (edge 0)
  obtain ⟨i₀, rfl⟩ : w ∈ Set.range vtx := by rw [hspan]; exact hgz₀.left_mem
  -- A third edge `g` at `w`, avoiding the two cycle edges there; its far end is on the cycle.
  obtain ⟨g, z, hgz, hg1, hg2⟩ :=
    exists_isLink_not_eq_of_three_le_degree hw (edge i₀) (edge (i₀ - ⟨1, by omega⟩))
  obtain ⟨j, rfl⟩ : z ∈ Set.range vtx := by rw [hspan]; exact hgz.right_mem
  -- `g` is then distinct from *every* cycle edge.
  have hgne : ∀ t : Fin m, g ≠ edge t := by
    intro t hgt
    rcases (hgt ▸ hgz : G.IsLink (edge t) (vtx i₀) (vtx j)).eq_and_eq_or_eq_and_eq
      (hlink t) with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hg1 (by rw [hgt, hvtx h1])
    · refine hg2 ?_
      have ht : t = i₀ - ⟨1, by omega⟩ := by rw [hvtx h1]; abel
      rw [hgt, ht]
  -- `g` is a chord: its far end is neither `w` nor a cycle-neighbour of `w`.
  have hji : j ≠ i₀ := fun h => hgz.ne (by rw [h])
  have hj1 : j ≠ i₀ + ⟨1, by omega⟩ := by
    rintro rfl
    exact hg1 (Simple.eq_of_isLink hgz (hlink i₀))
  have hj2 : j + ⟨1, by omega⟩ ≠ i₀ := by
    intro h
    exact hgne j (Simple.eq_of_isLink hgz.symm (h ▸ hlink j))
  -- Write `j = i₀ + c`: the arc from `i₀` to `j` has `c.val + 1` vertices, `3 ≤ c.val + 1 ≤ m - 1`.
  obtain ⟨c, rfl⟩ : ∃ c : Fin m, j = i₀ + c := ⟨j - i₀, by abel⟩
  have hc0 : c ≠ 0 := by rintro rfl; exact hji (add_zero i₀)
  have hc1 : c ≠ ⟨1, by omega⟩ := by rintro rfl; exact hj1 rfl
  have hc2 : c + ⟨1, by omega⟩ ≠ 0 := by
    intro h
    exact hj2 (by rw [add_assoc, h, add_zero])
  have hcm : c.val < m := c.isLt
  have hcv0 : c.val ≠ 0 := fun h => hc0 (Fin.val_injective (by simpa using h))
  have hcv1 : c.val ≠ 1 := fun h => hc1 (Fin.val_injective (by simpa using h))
  have hcvm : c.val ≠ m - 1 := by
    intro h
    refine hc2 (Fin.val_injective ?_)
    have hmm : c.val + (⟨1, by omega⟩ : Fin m).val = m := by
      change c.val + 1 = m
      omega
    rw [Fin.val_add, hmm, Nat.mod_self, Fin.val_zero]
  have hpm : c.val + 1 ≤ m := by omega
  have h3p : 3 ≤ c.val + 1 := by omega
  have hpD : c.val + 1 ≤ bodyBarDim n := by omega
  have hshort : c.val + 1 ≤ m - 1 := by omega
  -- The arc `vtx (i₀ + 0), …, vtx (i₀ + c)`, closed by the chord `g`, is a shorter cycle.
  set vtx₂ : Fin (c.val + 1) → α := fun k => vtx (i₀ + Fin.castLE hpm k) with hv2
  set edge₂ : Fin (c.val + 1) → β :=
    fun k => if k.val < c.val then edge (i₀ + Fin.castLE hpm k) else g with he2
  have hvtx₂ : Function.Injective vtx₂ := by
    intro k k' h
    simp only [hv2] at h
    have h' := add_left_cancel (hvtx h)
    exact Fin.val_injective (by simpa using congrArg Fin.val h')
  have hedge₂ : Function.Injective edge₂ := by
    intro k k' h
    simp only [he2] at h
    by_cases hk : k.val < c.val
    · by_cases hk' : k'.val < c.val
      · rw [ite_eq_left hk, ite_eq_left hk'] at h
        have h' := add_left_cancel (hedge h)
        exact Fin.val_injective (by simpa using congrArg Fin.val h')
      · rw [ite_eq_left hk, ite_eq_right hk'] at h
        exact absurd h.symm (hgne _)
    · by_cases hk' : k'.val < c.val
      · rw [ite_eq_right hk, ite_eq_left hk'] at h
        exact absurd h (hgne _)
      · exact Fin.val_injective (by omega)
  have hlink₂ : ∀ k : Fin (c.val + 1),
      G.IsLink (edge₂ k) (vtx₂ k) (vtx₂ (k + ⟨1, by omega⟩)) := by
    intro k
    simp only [hv2, he2]
    by_cases hk : k.val < c.val
    · -- An interior index: the successor does not wrap, and the link is the cycle's own.
      rw [ite_eq_left hk]
      have hsucc : i₀ + Fin.castLE hpm k + (⟨1, by omega⟩ : Fin m)
          = i₀ + Fin.castLE hpm (k + ⟨1, by omega⟩) := by
        rw [add_assoc]
        congr 1
        refine Fin.val_injective ?_
        simp only [Fin.val_add, Fin.val_castLE]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [← hsucc]
      exact hlink _
    · -- The last index: the successor wraps to `0`, and the closing link is the chord `g`.
      rw [ite_eq_right hk]
      have hkc : k.val = c.val := by omega
      have h1 : Fin.castLE hpm k = c := Fin.val_injective (by simpa using hkc)
      have h2 : Fin.castLE hpm (k + ⟨1, by omega⟩) = 0 := by
        refine Fin.val_injective ?_
        rw [Fin.val_castLE, Fin.val_add, Fin.val_zero]
        change (k.val + 1) % (c.val + 1) = 0
        rw [hkc, Nat.mod_self]
      rw [h1, h2, add_zero]
      exact hgz.symm
  -- The shorter cycle would have to span as well, forcing `c.val + 1 = m`.
  have key : Set.range vtx₂ = V(G) :=
    range_vtx_eq_vertexSet_of_cycle_of_noRigid hD hnp h3p hpD hvtx₂ hedge₂ hlink₂
  have hcard : V(G).ncard = m := by
    rw [← hspan, Set.ncard_range_of_injective hvtx, Nat.card_fin]
  have hcard₂ : V(G).ncard = c.val + 1 := by
    rw [← key, Set.ncard_range_of_injective hvtx₂, Nat.card_fin]
  omega

end Graph
