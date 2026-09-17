/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Induction.ForestSurgery.ChainExtraction
import CombinatorialRigidity.Molecular.Induction.Girth

/-!
# The maximal degree-two chain's side graph (`sec:pencil-girth-chain`)

Phase 39 (PENCIL), Lean track: leaves **M3a**, **M3b**, **M1**, **M2**, **M4** and **M4′** of
the girth-and-chain design pass (`notes/Phase39-design.md` § *Lean-track design pass
(2026-09-15): checklist items 1–2*), pinning `lem:pencil-chain-side-connected`,
`lem:pencil-chain-walk-extension`, `lem:pencil-degree-two-chain` and
`lem:pencil-chain-side-distance` of `blueprint/src/chapter/pencil.tex` § *Girth and degree-two
chains under no proper rigid subgraph*.

* `Graph.connected_deleteVerts_interior_of_twoEdgeConnected` (M3a): deleting a path's interior
  (every vertex but the two ends) from a `2`-edge-connected graph leaves a connected side.
* `Graph.degree_deleteVerts_interior_add_one` (M3b): the side loses exactly one edge at each
  path end — the one edge running from that end into the deleted interior.
* `Graph.exists_cycleData_or_closed_or_terminated_of_twoEdgeConnected` (M1): a degree-`2` chain
  extends until it either exhausts a cycle, closes back onto its own start at a degree-`≥ 3`
  anchor, or terminates at a degree-`≥ 3` vertex.
* `Graph.cycleData_or_hubLollipop_or_hubChain_of_degree_two_pair` (M2): the consumed-shape
  trichotomy at a degree-`2` vertex's split arm — `G` is a cycle, or the maximal degree-`2`
  chain through it closes at a single hub (a lollipop), or it runs between two distinct hubs.
* `Graph.le_length_add_length_of_isPath_deleteVerts_interior_of_noRigid` (M4) and
  `Graph.le_length_add_eDist_deleteVerts_interior_of_noRigid` (M4′): with a hub at one chain
  end and no proper rigid subgraph, a side path between the two chain ends is long —
  `bodyBarDim n + 1 ≤ P.length + Q.length`, and its `Graph.eDist` form.

M3a/M3b, M1 and M2 need only `TwoEdgeConnected`/`Simple`/`Loopless` plus the interior's
degree-`2` closure, no girth; the private helpers below package the shared fact that an
interior vertex's only `G`-neighbours are its two path-flanking vertices
(`isLink_eq_of_degree_eq_two`, `ForestSurgery/ChainExtraction.lean`'s `chainData_of_isPath` is
the template). M4/M4′ are the one pair that consumes girth, through
`Induction/Girth.lean`'s `Graph.girthGE_of_noRigid_of_three_le_degree` (G3).
-/

namespace Graph

variable {α β : Type*}

/-! ## Shared `WList`-index bookkeeping -/

/-- Restatement of `WList.DInc_get_get_succ` with an explicit (non-dependent-let) ascribed type,
so it composes cleanly inside further `have`/`rw` reasoning. -/
private lemma dIncAt (P : WList α β) (m : ℕ) (hm : m < P.length) :
    P.DInc (P.edge[m]'(by rw [WList.length_edge]; omega)) (P.get m) (P.get (m + 1)) :=
  WList.DInc_get_get_succ hm

private lemma eq_zero_of_get_eq_first {P : WList α β} (hnd : P.vertex.Nodup)
    {j : ℕ} (hjle : j ≤ P.length) (heq : P.get j = P.first) : j = 0 := by
  classical
  have h1 := WList.idxOf_get hnd hjle
  rw [heq, WList.idxOf_first] at h1
  omega

private lemma eq_length_of_get_eq_last {P : WList α β} (hnd : P.vertex.Nodup)
    {j : ℕ} (hjle : j ≤ P.length) (heq : P.get j = P.last) : j = P.length := by
  classical
  have h1 := WList.idxOf_get hnd hjle
  rw [heq, WList.idxOf_last P hnd] at h1
  omega

private lemma idxOf_ne_zero_of_ne_first [DecidableEq α] {P : WList α β} {a : α}
    (haP : a ∈ P) (hanef : a ≠ P.first) : P.idxOf a ≠ 0 := by
  intro heq
  exact hanef (by rw [← WList.get_idxOf P haP, heq, WList.get_zero])

private lemma idxOf_ne_length_of_ne_last [DecidableEq α] {P : WList α β} {a : α}
    (haP : a ∈ P) (hanel : a ≠ P.last) : P.idxOf a ≠ P.length := by
  intro heq
  exact hanel (by rw [← WList.get_idxOf P haP, heq, WList.get_length])

private lemma idxOf_lt_length_of_ne_last [DecidableEq α] {P : WList α β} {a : α}
    (haP : a ∈ P) (hanel : a ≠ P.last) : P.idxOf a < P.length :=
  lt_of_le_of_ne (WList.idxOf_mem_le haP) (idxOf_ne_length_of_ne_last haP hanel)

private lemma idxOf_pred_lt_length_of_ne_first [DecidableEq α] {P : WList α β} {a : α}
    (haP : a ∈ P) (hanef : a ≠ P.first) : P.idxOf a - 1 < P.length := by
  have h1 := WList.idxOf_mem_le haP
  have h2 := idxOf_ne_zero_of_ne_first haP hanef
  omega

private lemma idxOf_pred_lt_edgeLength_of_ne_first [DecidableEq α] {P : WList α β} {a : α}
    (haP : a ∈ P) (hanef : a ≠ P.first) : P.idxOf a - 1 < P.edge.length := by
  rw [WList.length_edge]; exact idxOf_pred_lt_length_of_ne_first haP hanef

private lemma idxOf_lt_edgeLength_of_ne_last [DecidableEq α] {P : WList α β} {a : α}
    (haP : a ∈ P) (hanel : a ≠ P.last) : P.idxOf a < P.edge.length := by
  rw [WList.length_edge]; exact idxOf_lt_length_of_ne_last haP hanel

/-- **An interior vertex's only `G`-neighbours are its two path-flanking vertices**
(the shared fact behind M3a/M3b). If `a` is a vertex of the path `P` other than its two ends,
with every such interior vertex forced to `G`-degree `2` (`hdeg`), then any `G`-edge at `a` is
one of `a`'s two `P`-flanking edges: the incoming one from `P.get (P.idxOf a - 1)`, or the
outgoing one to `P.get (P.idxOf a + 1)`. Route: `isLink_eq_of_degree_eq_two` applied to the two
`dIncAt`-derived witnesses flanking `a`'s index, distinct by `P.edge_nodup`
(`ForestSurgery/ChainExtraction.lean`'s `chainData_of_isPath`, `closed_path_degree_two_spanning`
are the same idiom at general/boundary indices). -/
private lemma isLink_interior_iff_eq [DecidableEq α] [Finite β] {G : Graph α β} [G.Loopless]
    {P : WList α β} (hP : G.IsPath P)
    (hdeg : ∀ x ∈ P, x ≠ P.first → x ≠ P.last → G.degree x = 2)
    {a b : α} {e : β} (haP : a ∈ P) (hanef : a ≠ P.first) (hanel : a ≠ P.last)
    (hab : G.IsLink e a b) :
    (e = P.edge[P.idxOf a - 1]'(idxOf_pred_lt_edgeLength_of_ne_first haP hanef) ∧
      b = P.get (P.idxOf a - 1)) ∨
    (e = P.edge[P.idxOf a]'(idxOf_lt_edgeLength_of_ne_last haP hanel) ∧
      b = P.get (P.idxOf a + 1)) := by
  have hile : P.idxOf a ≤ P.length := WList.idxOf_mem_le haP
  have hgeti : P.get (P.idxOf a) = a := WList.get_idxOf P haP
  have hi0 : 0 < P.idxOf a := Nat.pos_of_ne_zero (idxOf_ne_zero_of_ne_first haP hanef)
  have hilt : P.idxOf a < P.length := idxOf_lt_length_of_ne_last haP hanel
  have hdeg2 : G.degree a = 2 := hdeg a haP hanef hanel
  have hb1 : G.IsLink (P.edge[P.idxOf a - 1]'(idxOf_pred_lt_edgeLength_of_ne_first haP hanef))
      a (P.get (P.idxOf a - 1)) := by
    have h := hP.isWalk.isLink_of_dInc (dIncAt P (P.idxOf a - 1)
      (idxOf_pred_lt_length_of_ne_first haP hanef))
    have heq1 := Nat.sub_add_cancel hi0
    rw [heq1, hgeti] at h
    exact h.symm
  have hb2 : G.IsLink (P.edge[P.idxOf a]'(idxOf_lt_edgeLength_of_ne_last haP hanel))
      a (P.get (P.idxOf a + 1)) := by
    have h := hP.isWalk.isLink_of_dInc (dIncAt P (P.idxOf a) hilt)
    rwa [hgeti] at h
  have hne : (P.edge[P.idxOf a - 1]'(idxOf_pred_lt_edgeLength_of_ne_first haP hanef)) ≠
      (P.edge[P.idxOf a]'(idxOf_lt_edgeLength_of_ne_last haP hanel)) := by
    intro h
    have := hP.edge_nodup.getElem_inj_iff.mp h
    omega
  rcases isLink_eq_of_degree_eq_two hdeg2 hne hb1 hb2 e b hab with rfl | rfl
  · exact Or.inl ⟨rfl, hb1.isLink_iff_eq.mp hab⟩
  · exact Or.inr ⟨rfl, hb2.isLink_iff_eq.mp hab⟩

/-! ## M3a/M3b — the side `G − chain interior` is connected, losing one edge at each end -/

/-- **M3a**: deleting a path's interior from a `2`-edge-connected graph leaves the side
connected (`lem:pencil-chain-side-connected`, first pin). Route: `P.first` survives (it is never
interior), and every side vertex is `ConnBetween`-reachable from it inside the side — run the
`G`-component argument of `preconnected_of_twoEdgeConnected` at the component `V'` of `P.first`
inside the side: if `V' ⊊ V(G − interior)`, the only possible `G`-edges leaving `V' ∪ interior`
are chain edges from an interior vertex to a path end not in `V'`, and `P.first ∈ V'` always, so
at most the very last chain edge (`P.last`'s) can escape — at most `1 < 2`, contradicting
`h2ec`. -/
theorem connected_deleteVerts_interior_of_twoEdgeConnected [Finite β] {G : Graph α β}
    [G.Loopless] (h2ec : G.TwoEdgeConnected) {P : WList α β} (hP : G.IsPath P)
    (hlen : 1 ≤ P.length)
    (hdeg : ∀ x ∈ P, x ≠ P.first → x ≠ P.last → G.degree x = 2) :
    (G - {x | x ∈ P ∧ x ≠ P.first ∧ x ≠ P.last}).Connected := by
  classical
  set interior : Set α := {x | x ∈ P ∧ x ≠ P.first ∧ x ≠ P.last} with hidef
  have hfirstG : P.first ∈ V(G) := hP.isWalk.first_mem
  have hfirstNotInt : P.first ∉ interior := fun h => h.2.1 rfl
  have hfirstH : P.first ∈ V(G - interior) := by
    rw [deleteVerts_vertexSet]; exact ⟨hfirstG, hfirstNotInt⟩
  rw [connected_iff]
  refine ⟨⟨P.first, hfirstH⟩, preconnected_of_exists_connBetween ⟨P.first, fun z hzH => ?_⟩⟩
  by_contra hz
  set V' : Set α := {w | w ∈ V(G - interior) ∧ (G - interior).ConnBetween P.first w} with hV'def
  have hV'sub : V' ⊆ V(G - interior) := fun w hw => hw.1
  have hfirstV' : P.first ∈ V' := ⟨hfirstH, ConnBetween.refl hfirstH⟩
  have hzV' : z ∉ V' := fun hz' => hz hz'.2
  have hzInt : z ∉ interior := (deleteVerts_vertexSet G interior ▸ hzH).2
  have hzW : z ∉ V' ∪ interior := by
    rintro (h | h)
    · exact hzV' h
    · exact hzInt h
  have hallButLast : ∀ j, j ≤ P.length → j ≠ P.length → P.get j ∈ V' ∪ interior := by
    intro j hjle hjne
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · exact Or.inl (by rw [hj0, WList.get_zero]; exact hfirstV')
    · exact Or.inr ⟨WList.get_mem P j,
        fun heq => hjpos.ne' (eq_zero_of_get_eq_first hP.nodup hjle heq),
        fun heq => hjne (eq_length_of_get_eq_last hP.nodup hjle heq)⟩
  have hsub : ∃ f : β, G.cutEdges (V' ∪ interior) ⊆ {f} := by
    refine ⟨P.edge[P.length - 1]'(by rw [WList.length_edge]; omega), ?_⟩
    rintro e ⟨heE, a, b, hab, haW, hbW⟩
    rcases haW with haV' | haInt
    · exfalso
      have haH : a ∈ V(G - interior) := hV'sub haV'
      have haInt' : a ∉ interior := (deleteVerts_vertexSet G interior ▸ haH).2
      have hbG : b ∈ V(G) := hab.right_mem
      have hbInt' : b ∉ interior := fun h => hbW (Or.inr h)
      have hbH : b ∈ V(G - interior) := by rw [deleteVerts_vertexSet]; exact ⟨hbG, hbInt'⟩
      have heH : (G - interior).IsLink e a b := by
        rw [deleteVerts_isLink_iff]; exact ⟨hab, haInt', hbInt'⟩
      exact hbW (Or.inl ⟨hbH, haV'.2.trans heH.connBetween⟩)
    · obtain ⟨haP, hanef, hanel⟩ := haInt
      rcases isLink_interior_iff_eq hP hdeg haP hanef hanel hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd (hallButLast (P.idxOf a - 1)
          (le_trans (Nat.sub_le _ _) (WList.idxOf_mem_le haP))
          (idxOf_pred_lt_length_of_ne_first haP hanef).ne) hbW
      · have hidxlt : P.idxOf a < P.length := idxOf_lt_length_of_ne_last haP hanel
        rcases eq_or_lt_of_le (show P.idxOf a + 1 ≤ P.length by omega) with heqlen | hltlen
        · have hidxeq : P.idxOf a = P.length - 1 := by omega
          exact Set.mem_singleton_iff.mpr (by simp [hidxeq])
        · exact absurd (hallButLast (P.idxOf a + 1) (by omega) (by omega)) hbW
  obtain ⟨f, hsub⟩ := hsub
  have hWsub : V' ∪ interior ⊆ V(G) := by
    rintro w (hw | hw)
    · exact (deleteVerts_vertexSet G interior ▸ hV'sub hw).1
    · exact hP.isWalk.vertex_mem_of_mem hw.1
  have hWne : (V' ∪ interior).Nonempty := ⟨P.first, Or.inl hfirstV'⟩
  have hWproper : V' ∪ interior ⊂ V(G) := by
    refine hWsub.ssubset_of_ne fun heq => hzW ?_
    have hzG : z ∈ V(G) := (deleteVerts_vertexSet G interior ▸ hzH).1
    exact heq ▸ hzG
  have hcut : 2 ≤ (G.cutEdges (V' ∪ interior)).ncard := h2ec _ hWne hWproper
  have hle1 := Set.ncard_le_ncard hsub (Set.finite_singleton _)
  rw [Set.ncard_singleton] at hle1
  omega

/-- **M3b**: the side loses exactly one edge at `P.first` — the one edge running into the
deleted interior (`lem:pencil-chain-side-connected`, second pin). Route:
`incEdges_deleteVerts` turns the side's incidence set at `P.first` into
`E(G, P.first) \ E(G, interior)`; the only member of that difference is the path's own first
edge (any other edge at `P.first` landing in `interior` would, by the interior classification
above, have to be one of *that* interior vertex's own two flanking edges — forcing it back to be
the first path edge by `Nodup`, per `lem:pencil-degree-two-chain`'s route) —
`Set.ncard_sdiff_singleton_add_one` closes the count. `2 ≤ P.length` is essential: at length `1`
there is no interior vertex to delete. -/
theorem degree_deleteVerts_interior_add_one [Finite β] {G : Graph α β} [G.Loopless]
    {P : WList α β} (hP : G.IsPath P) (hlen : 2 ≤ P.length)
    (hdeg : ∀ x ∈ P, x ≠ P.first → x ≠ P.last → G.degree x = 2) :
    (G - {x | x ∈ P ∧ x ≠ P.first ∧ x ≠ P.last}).degree P.first + 1 = G.degree P.first := by
  classical
  set interior : Set α := {x | x ∈ P ∧ x ≠ P.first ∧ x ≠ P.last} with hidef
  set firstEdge : β := P.edge[0]'(by rw [WList.length_edge]; omega) with hfedef
  have hlt0 : (0 : ℕ) < P.length := by omega
  have hfirstLink : G.IsLink firstEdge P.first (P.get 1) := by
    have h := hP.isWalk.isLink_of_dInc (dIncAt P 0 hlt0)
    rwa [WList.get_zero] at h
  have hget1ne_first : P.get 1 ≠ P.first := fun heq =>
    absurd (eq_zero_of_get_eq_first hP.nodup (by omega) heq) (by omega)
  have hget1ne_last : P.get 1 ≠ P.last := fun heq =>
    absurd (eq_length_of_get_eq_last hP.nodup (by omega) heq) (by omega)
  have hget1int : P.get 1 ∈ interior := ⟨WList.get_mem P 1, hget1ne_first, hget1ne_last⟩
  have hkey : ∀ e, e ∈ E(G, P.first) → (e ∈ E(G, interior) ↔ e = firstEdge) := by
    intro e heP
    constructor
    · rintro ⟨x, hxint, hxinc⟩
      obtain ⟨hxP, hxnef, hxnel⟩ := hxint
      have hidxle : P.idxOf x ≤ P.length := WList.idxOf_mem_le hxP
      have hidxlt : P.idxOf x < P.length :=
        lt_of_le_of_ne hidxle (idxOf_ne_length_of_ne_last hxP hxnel)
      obtain ⟨y0, hy0⟩ : ∃ y0, G.IsLink e P.first y0 := heP
      have hx0 : x = P.first ∨ x = y0 := hxinc.eq_or_eq_of_isLink hy0
      have hxy0 : x = y0 := hx0.resolve_left hxnef
      have hxfirst : G.IsLink e x P.first := by rw [hxy0]; exact hy0.symm
      rcases isLink_interior_iff_eq hP hdeg hxP hxnef hxnel hxfirst with ⟨rfl, hbeq⟩ | ⟨rfl, hbeq⟩
      · -- `e = P.edge[idxOf x - 1]`, and `P.first = P.get (idxOf x - 1)` forces `idxOf x = 1`.
        have hidx0 : P.idxOf x - 1 = 0 := eq_zero_of_get_eq_first hP.nodup (by omega) hbeq.symm
        rw [hfedef]
        simp [hidx0]
      · -- `e = P.edge[idxOf x]`, and `P.first = P.get (idxOf x + 1)` is impossible.
        exfalso
        have := eq_zero_of_get_eq_first hP.nodup (by omega) hbeq.symm
        have hidxpos : 0 < P.idxOf x := Nat.pos_of_ne_zero (idxOf_ne_zero_of_ne_first hxP hxnef)
        omega
    · rintro rfl
      exact ⟨P.get 1, hget1int, hfirstLink.inc_right⟩
  have hdiffEq : E(G, P.first) \ E(G, interior) = E(G, P.first) \ {firstEdge} := by
    ext e
    simp only [Set.mem_sdiff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨he1, he2⟩
      exact ⟨he1, fun h => he2 ((hkey e he1).mpr h)⟩
    · rintro ⟨he1, he2⟩
      exact ⟨he1, fun h => he2 ((hkey e he1).mp h)⟩
  have hcard : E(G - interior, P.first).ncard + 1 = E(G, P.first).ncard := by
    rw [incEdges_deleteVerts, hdiffEq]
    exact Set.ncard_sdiff_singleton_add_one hfirstLink.inc_left
  rw [degree_eq_ncard_inc, degree_eq_ncard_inc]
  exact hcard

/-! ## M1 — the uncapped chain-walk builder -/

/-- **A path is shorter than its host graph's vertex count.** Its `Nodup` vertex list has
`P.length + 1` entries, all `G`-vertices, so `P.length < |V(G)|`. This is the natural induction
cap for the chain-walk builder below, replacing E2d-4's externally supplied `n − P.length`
measure (`ForestSurgery/ChainExtraction.lean`'s `chainWalk_trichotomy`); the `ncard` form of the
Matroid package's `IsPath.length_le_encard`. -/
private lemma length_lt_ncard_vertexSet [Finite α] {G : Graph α β} {P : WList α β}
    (hP : G.IsPath P) : P.length < V(G).ncard := by
  have hle := Set.ncard_le_ncard hP.vertexSet_subset (Set.toFinite _)
  rw [hP.ncard_vertexSet] at hle
  omega

/-- **M1**: the uncapped chain-walk trichotomy (`lem:pencil-chain-walk-extension`). A path `P₀`
of a simple `2`-edge-connected graph whose vertices after the first all have degree `2` either
sits inside a graph that is itself a cycle, or extends to a closed walk returning to `P₀.first`
— which then has degree `≥ 3`, every other walk vertex having degree `2` — or extends to a
longer path whose interior vertices have degree `2` and whose last vertex has degree `≥ 3`.

Template: `chainWalk_trichotomy` (`ForestSurgery/ChainExtraction.lean`, Katoh–Tanigawa 2011
Lemma 4.6's walk-builder), with two changes. Its five minimality-sourced facts are re-sourced
from `TwoEdgeConnected` + `G.Simple` (the min-degree floor from
`two_le_degree_of_twoEdgeConnected`, the exit edge from
`exists_splitOff_data_of_degree_eq_two_of_twoEdgeConnected`, connectivity from
`preconnected_of_twoEdgeConnected`), and the "lollipop" closed walk at a degree-`≥ 3` anchor is
**kept** as the second alternative instead of being refuted against a no-proper-rigid-subgraph
hypothesis. The external cap `n` is replaced by `length_lt_ncard_vertexSet`, so the strong
induction runs on `|V(G)| − P.length`. -/
theorem exists_cycleData_or_closed_or_terminated_of_twoEdgeConnected [Finite α] [Finite β]
    {G : Graph α β} [G.Simple] (h2ec : G.TwoEdgeConnected)
    {P₀ : WList α β} (hP₀ : G.IsPath P₀) (hlen : 1 ≤ P₀.length)
    (hdeg : ∀ x ∈ P₀, x ≠ P₀.first → x ≠ P₀.last → G.degree x = 2)
    (hlast : G.degree P₀.last = 2) :
    Nonempty G.CycleData ∨
    (∃ C : WList α β, G.IsCyclicWalk C ∧ P₀.IsPrefix C ∧ 3 ≤ G.degree C.first ∧
      (∀ x ∈ C, x ≠ C.first → G.degree x = 2)) ∨
    (∃ P : WList α β, G.IsPath P ∧ P₀.IsPrefix P ∧
      (∀ x ∈ P, x ≠ P.first → x ≠ P.last → G.degree x = 2) ∧ 3 ≤ G.degree P.last) := by
  classical
  have hconn : G.Preconnected := preconnected_of_twoEdgeConnected h2ec
  -- The exit edge at a known degree-`2` vertex, sourced from `2`-edge-connectivity alone.
  have hexit : ∀ {v w : α} {e : β}, w ≠ v → G.IsLink e v w → G.degree v = 2 →
      ∃ y g, y ≠ v ∧ g ≠ e ∧ G.IsLink g v y := by
    intro v w e hwv hlink hdegv
    obtain ⟨a, b, eₐ, e_b, hav, hbv, -, -, hne, hla, hlb, hclosure⟩ :=
      exists_splitOff_data_of_degree_eq_two_of_twoEdgeConnected h2ec hlink.left_mem
        hlink.right_mem hwv hdegv
    rcases hclosure e w hlink with rfl | rfl
    · exact ⟨b, e_b, hbv, hne.symm, hlb⟩
    · exact ⟨a, eₐ, hav, hne, hla⟩
  -- The invariant: `P` extends `P₀`, its interior has degree `2`, and so does its last vertex.
  have main : ∀ P : WList α β, G.IsPath P → P₀.IsPrefix P → 1 ≤ P.length →
      (∀ x ∈ P, x ≠ P.first → x ≠ P.last → G.degree x = 2) → G.degree P.last = 2 →
      Nonempty G.CycleData ∨
      (∃ C : WList α β, G.IsCyclicWalk C ∧ P₀.IsPrefix C ∧ 3 ≤ G.degree C.first ∧
        (∀ x ∈ C, x ≠ C.first → G.degree x = 2)) ∨
      (∃ P' : WList α β, G.IsPath P' ∧ P₀.IsPrefix P' ∧
        (∀ x ∈ P', x ≠ P'.first → x ≠ P'.last → G.degree x = 2) ∧ 3 ≤ G.degree P'.last) := by
    intro P
    induction hM : V(G).ncard - P.length using Nat.strong_induction_on generalizing P with
    | _ M IH =>
    intro hP hpre hPlen1 hdegP hdeg2
    have hcap : P.length < V(G).ncard := length_lt_ncard_vertexSet hP
    have hV2 : 2 ≤ V(G).ncard := by omega
    set entry : β := P.edge[P.length - 1]'(by rw [WList.length_edge]; omega) with hentry_def
    have hentry : G.IsLink entry (P.get (P.length - 1)) P.last := by
      rw [hentry_def]
      have h := hP.isWalk.isLink_of_dInc (dIncAt P (P.length - 1) (by omega))
      have heq1 := Nat.sub_add_cancel (show 1 ≤ P.length by omega)
      rwa [heq1, WList.get_length] at h
    obtain ⟨y, g, hyne, hgne, hgy⟩ := hexit hentry.ne hentry.symm hdeg2
    -- `g` is not already a path edge: at the last index it would coincide with `entry`, and at
    -- any earlier index one of its two endpoints would have to be `P.last`.
    have hgP : g ∉ P.edge := by
      intro hgmem
      obtain ⟨k, hk, hke⟩ := List.getElem_of_mem hgmem
      have hk' : k < P.length := by rwa [WList.length_edge] at hk
      have hkey : G.IsLink g (P.get k) (P.get (k + 1)) := by
        have h := hP.isWalk.isLink_of_dInc (dIncAt P k hk')
        rwa [hke] at h
      by_cases hklast : k = P.length - 1
      · apply hgne
        subst hklast
        have heq1 := Nat.sub_add_cancel (show 1 ≤ P.length by omega)
        rw [heq1, WList.get_length] at hkey
        exact hkey.unique_edge hentry
      · have hlt1 : P.get k ≠ P.last := fun heq =>
          absurd (eq_length_of_get_eq_last hP.nodup hk'.le heq) (by omega)
        have hlt2 : P.get (k + 1) ≠ P.last := fun heq =>
          absurd (eq_length_of_get_eq_last hP.nodup (by omega) heq) (by omega)
        rcases hkey.eq_and_eq_or_eq_and_eq hgy with ⟨hk1, -⟩ | ⟨-, hk2⟩
        · exact hlt1 hk1
        · exact hlt2 hk2
    by_cases hyfirst : y = P.first
    · -- The walk closes back onto its own start.
      subst hyfirst
      by_cases hlen1 : P.length = 1
      · -- A length-`1` closing is a parallel pair, excluded by `G.Simple`.
        exfalso
        have h0 : P.length - 1 = 0 := by omega
        rw [h0, WList.get_zero] at hentry
        exact hgne (hentry.unique_edge hgy.symm).symm
      · have hlen2 : 2 ≤ P.length := by omega
        by_cases hstart2 : G.degree P.first = 2
        · -- Every vertex of the closed walk has degree `2`: `G` is a cycle.
          have hdeg_all : ∀ z ∈ P, G.degree z = 2 := by
            intro z hz
            by_cases hzf : z = P.first
            · rw [hzf]; exact hstart2
            · by_cases hzl : z = P.last
              · rw [hzl]; exact hdeg2
              · exact hdegP z hz hzf hzl
          obtain ⟨cy, -⟩ := cycleData_of_closed_path hP hlen2 hgy hgP hdeg_all hconn
          exact Or.inl ⟨cy⟩
        · -- The lollipop: the closed walk anchored at a degree-`≥ 3` start.
          have hstart3 : 3 ≤ G.degree P.first := by
            have := two_le_degree_of_twoEdgeConnected h2ec hP.isWalk.first_mem hV2
            omega
          refine Or.inr (Or.inl ⟨P.concat g P.first, hP.concat_isCyclicWalk hgy hgP,
            hpre.concat g P.first, ?_, ?_⟩)
          · rw [WList.concat_first]; exact hstart3
          · intro z hz hzne
            rw [WList.concat_first] at hzne
            rw [WList.mem_concat] at hz
            rcases hz with hz | rfl
            · by_cases hzl : z = P.last
              · rw [hzl]; exact hdeg2
              · exact hdegP z hz hzne hzl
            · exact absurd rfl hzne
    · by_cases hymem : y ∈ P
      · -- Impossible: an interior vertex's only edges are its two path edges, and `g` is not one.
        exfalso
        rcases isLink_interior_iff_eq hP hdegP hymem hyfirst hyne hgy.symm with
          ⟨rfl, -⟩ | ⟨rfl, -⟩
        · exact hgP (List.getElem_mem _)
        · exact hgP (List.getElem_mem _)
      · -- Extend, then test the new last vertex's degree.
        have hP'path : G.IsPath (P.concat g y) := concat_isPath_iff.mpr ⟨hP, hgy, hymem⟩
        have hP'deg : ∀ z ∈ P.concat g y, z ≠ (P.concat g y).first →
            z ≠ (P.concat g y).last → G.degree z = 2 := by
          intro z hz hzf hzl
          rw [WList.concat_first] at hzf
          rw [WList.concat_last] at hzl
          rw [WList.mem_concat] at hz
          rcases hz with hz | rfl
          · by_cases hzP : z = P.last
            · rw [hzP]; exact hdeg2
            · exact hdegP z hz hzf hzP
          · exact absurd rfl hzl
        by_cases hydeg3 : 3 ≤ G.degree y
        · exact Or.inr (Or.inr ⟨P.concat g y, hP'path, hpre.concat g y, hP'deg,
            by rw [WList.concat_last]; exact hydeg3⟩)
        · have hy2 : G.degree y = 2 := by
            have := two_le_degree_of_twoEdgeConnected h2ec hgy.right_mem hV2
            omega
          exact IH (V(G).ncard - (P.concat g y).length)
            (by rw [WList.concat_length]; omega) (P.concat g y) rfl hP'path
            (hpre.concat g y) (by rw [WList.concat_length]; omega) hP'deg
            (by rw [WList.concat_last]; exact hy2)
  exact main P₀ hP₀ (WList.isPrefix_refl P₀) hlen hdeg hlast

/-! ## M2 — the consumed-shape trichotomy at the split arm's hypotheses -/

/-- The one-sided form of M2, taking `G.degree a = 2` directly instead of the disjunction
`hab`. Route: M1 at `P₀ := cons v eₐ (nil a)` (a path since `v ≠ a`, `G.Simple` ⇒ loopless);
its first disjunct is this lemma's first; its second has `C.first = P₀.first = v` (prefix
preserves `first`) with `3 ≤ G.degree v`, refuted by `hdeg`; its third gives a path
`P₁ : v … w'` with `3 ≤ G.degree w'` and, since `a` has degree `2` while `w'` has degree
`≥ 3` (so `P₁ ≠ P₀`), `2 ≤ P₁.length`. M1 again at `P₀ := P₁.reverse` (`IsPath.reverse`;
`first = w'`, `last = v` of degree `2` = the new `hlast`, interior degree `2` inherited via
`mem_reverse`/`reverse_first`/`reverse_last`): its first disjunct is this lemma's first; its
second gives the lollipop at `w'` (`v ∈ C` via the prefix; `3 ≤ C.length` since a closed `C`
cannot equal the non-closed `P₁.reverse`, so the prefix is proper); its third gives the
two-hub chain (`3 ≤ P.length` likewise). -/
private lemma degree_two_pair_aux [Finite α] [Finite β] {G : Graph α β} [G.Simple]
    (h2ec : G.TwoEdgeConnected) {v a : α} {eₐ : β}
    (hdeg : G.degree v = 2) (hla : G.IsLink eₐ v a) (ha : G.degree a = 2) :
    Nonempty G.CycleData ∨
    (∃ C : WList α β, G.IsCyclicWalk C ∧ 3 ≤ G.degree C.first ∧
      (∀ x ∈ C, x ≠ C.first → G.degree x = 2) ∧ v ∈ C ∧ 3 ≤ C.length) ∨
    (∃ P : WList α β, G.IsPath P ∧ 3 ≤ G.degree P.first ∧ 3 ≤ G.degree P.last ∧
      (∀ x ∈ P, x ≠ P.first → x ≠ P.last → G.degree x = 2) ∧ v ∈ P ∧ 3 ≤ P.length) := by
  classical
  set P₀ : WList α β := WList.cons v eₐ (WList.nil a) with hP₀def
  have hP₀first : P₀.first = v := by simp [hP₀def]
  have hP₀last : P₀.last = a := by simp [hP₀def]
  have hP₀path : G.IsPath P₀ := by
    rw [hP₀def, cons_isPath_iff]
    exact ⟨by simpa using hla, nil_isPath hla.right_mem, by simpa using hla.ne⟩
  have hP₀deg : ∀ x ∈ P₀, x ≠ P₀.first → x ≠ P₀.last → G.degree x = 2 := by
    intro x hx hxfirst hxlast
    rw [hP₀def] at hx
    simp only [WList.mem_cons_iff, WList.mem_nil_iff] at hx
    rw [hP₀first] at hxfirst
    rw [hP₀last] at hxlast
    rcases hx with rfl | rfl
    · exact absurd rfl hxfirst
    · exact absurd rfl hxlast
  -- First M1 call: extend `P₀` until it closes or hits a hub.
  have hM1a := exists_cycleData_or_closed_or_terminated_of_twoEdgeConnected h2ec hP₀path
    (by rw [hP₀def]; simp) hP₀deg (by rw [hP₀last]; exact ha)
  rcases hM1a with hcyc | ⟨C, hCcyc, hCpre, hCfirst, hCdeg⟩ |
    ⟨P₁, hP₁path, hP₁pre, hP₁deg, hP₁last⟩
  · exact Or.inl hcyc
  · -- Impossible: a closed walk through `v` would need `3 ≤ G.degree v`, but `v` has degree `2`.
    exfalso
    have hCv : C.first = v := by rw [← hCpre.first_eq]; exact hP₀first
    rw [hCv] at hCfirst
    omega
  · -- `P₁ : v … w'` with hub `w'`; it strictly extends `P₀`, so `2 ≤ P₁.length`.
    have hP₁first : P₁.first = v := by rw [← hP₁pre.first_eq]; exact hP₀first
    have hP₁len2 : 2 ≤ P₁.length := by
      by_contra hcon
      have hle : P₀.length ≤ P₁.length := hP₁pre.length_le
      have hP₀len : P₀.length = 1 := by simp [hP₀def]
      have hge : P₁.length ≤ P₀.length := by omega
      have heq : P₀ = P₁ := hP₁pre.eq_of_length_ge hge
      rw [← heq, hP₀last] at hP₁last
      omega
    -- Second M1 call, at `P₁.reverse` (first `w'`, last `v` of degree `2`).
    set P₁r : WList α β := P₁.reverse with hP₁rdef
    have hP₁rfirst : P₁r.first = P₁.last := WList.reverse_first
    have hP₁rlast0 : P₁r.last = P₁.first := WList.reverse_last
    have hP₁rlast : P₁r.last = v := by rw [hP₁rlast0, hP₁first]
    have hP₁rlen : P₁r.length = P₁.length := WList.reverse_length
    have hP₁rpath : G.IsPath P₁r := hP₁path.reverse
    have hP₁rdeg : ∀ x ∈ P₁r, x ≠ P₁r.first → x ≠ P₁r.last → G.degree x = 2 := by
      intro x hx hxf hxl
      rw [hP₁rdef, WList.mem_reverse] at hx
      rw [hP₁rfirst] at hxf
      rw [hP₁rlast0] at hxl
      exact hP₁deg x hx hxl hxf
    have hvP₁r : v ∈ P₁r := by rw [← hP₁rlast]; exact WList.last_mem
    have hP₁rlen2 : 2 ≤ P₁r.length := by rw [hP₁rlen]; exact hP₁len2
    have hM1b := exists_cycleData_or_closed_or_terminated_of_twoEdgeConnected h2ec hP₁rpath
      (by omega) hP₁rdeg (by rw [hP₁rlast]; exact hdeg)
    rcases hM1b with hcyc | ⟨C, hCcyc, hCpre, hCfirst, hCdeg⟩ |
      ⟨P, hPpath, hPpre, hPdeg, hPlast3⟩
    · exact Or.inl hcyc
    · -- The lollipop: a closed walk anchored at hub `w' = P₁.last`, through `v`.
      have hCfirst_eq : C.first = P₁.last := by rw [← hCpre.first_eq, hP₁rfirst]
      have hvC : v ∈ C := hCpre.mem hvP₁r
      have hClen : 3 ≤ C.length := by
        have hle : P₁r.length ≤ C.length := hCpre.length_le
        by_contra hcon
        have hge : C.length ≤ P₁r.length := by omega
        have heq : P₁r = C := hCpre.eq_of_length_ge hge
        have hCclosed : C.first = C.last := hCcyc.isClosed.eq
        rw [← heq, hP₁rfirst, hP₁rlast] at hCclosed
        rw [hCclosed] at hP₁last
        omega
      refine Or.inr (Or.inl ⟨C, hCcyc, ?_, hCdeg, hvC, hClen⟩)
      rw [hCfirst_eq]; exact hP₁last
    · -- The two-hub chain: a path from hub `w' = P₁.last` through `v` to a second hub.
      have hPfirst_eq : P.first = P₁.last := by rw [← hPpre.first_eq, hP₁rfirst]
      have hvP : v ∈ P := hPpre.mem hvP₁r
      have hPlen3 : 3 ≤ P.length := by
        have hle : P₁r.length ≤ P.length := hPpre.length_le
        by_contra hcon
        have hge : P.length ≤ P₁r.length := by omega
        have heq : P₁r = P := hPpre.eq_of_length_ge hge
        rw [← heq, hP₁rlast] at hPlast3
        omega
      refine Or.inr (Or.inr ⟨P, hPpath, ?_, hPlast3, hPdeg, hvP, hPlen3⟩)
      rw [hPfirst_eq]; exact hP₁last

/-- **M2**: the consumed-shape trichotomy (`lem:pencil-degree-two-chain`) at the two
hypotheses of `hbareSplit`'s split arm (a degree-`2` vertex `v` and its two neighbours `a`,
`b` via distinct edges). Either `G` is a cycle, or the maximal degree-`2` chain through `v`
closes at a single hub `w'` (a lollipop: a closed walk anchored at a degree-`≥ 3` vertex,
running through `v`, all of whose other vertices have degree `2`), or it runs between two
distinct hubs (a path with both ends of degree `≥ 3`, `v` interior, all other interior
vertices of degree `2`). The consumer's `¬ G.PencilHub a ∨ ¬ G.PencilHub b` is `hab` by one
line (`a ∈ V(G)` from `hla.right_mem`, `¬ PencilHub a ↔ G.degree a < 3`, and
`two_le_degree_of_twoEdgeConnected`) — not part of this lemma. `5 ≤ |V|` and `hnp` are not
needed for the trichotomy itself (only for its girth consequences downstream). (The combinatorial
hypotheses quoted here are unchanged by the kernels' 2026-09-16 restatement — that added an
induction hypothesis and moved the antecedent/conclusion to `HasDistinctPencilRealization`;
see `Molecule/Pencil/Escape.lean`.) Route: WLOG
`G.degree a = 2` (`degree_two_pair_aux`, applied with `a`/`b` and `eₐ`/`e_b` swapped in the
other case) — the conclusion mentions neither `a` nor `b`, so no explicit swap lemma is
needed. -/
theorem cycleData_or_hubLollipop_or_hubChain_of_degree_two_pair [Finite α] [Finite β]
    {G : Graph α β} [G.Simple] (h2ec : G.TwoEdgeConnected)
    {v a b : α} {eₐ e_b : β} (hdeg : G.degree v = 2) (_hne : eₐ ≠ e_b)
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hab : G.degree a = 2 ∨ G.degree b = 2) :
    Nonempty G.CycleData ∨
    (∃ C : WList α β, G.IsCyclicWalk C ∧ 3 ≤ G.degree C.first ∧
      (∀ x ∈ C, x ≠ C.first → G.degree x = 2) ∧ v ∈ C ∧ 3 ≤ C.length) ∨
    (∃ P : WList α β, G.IsPath P ∧ 3 ≤ G.degree P.first ∧ 3 ≤ G.degree P.last ∧
      (∀ x ∈ P, x ≠ P.first → x ≠ P.last → G.degree x = 2) ∧ v ∈ P ∧ 3 ≤ P.length) :=
  hab.elim (degree_two_pair_aux h2ec hdeg hla) (degree_two_pair_aux h2ec hdeg hlb)

/-! ## M4/M4′ — side paths between the chain ends are long -/

/-- The cycle behind M4, stated against an arbitrary girth bound: a `G`-path `P` of length
`≥ 2` and a path `Q` of the side `G − P.interior` sharing `P`'s two ends close into a single
cycle on `P.length + Q.length` vertices, so any girth bound for `G` bounds that sum.

Route: `P`'s two ends are distinct (`first_ne_last_iff` at `2 ≤ P.length`), so `Q` is a `cons`,
`Q = cons P.first f Q₁`. Then `R := P ++ Q₁.reverse` is a `G`-path by `IsPath.append`: `Q₁`'s
vertices are side vertices, hence outside `P`'s interior, and they avoid `P.first` by `Q`'s own
`Nodup`, so `P.last` is the only vertex `P` and `Q₁.reverse` share. `R` runs from `P.first` to
`Q₁.first` and is closed by `f`, which is no edge of `R`: not of `Q₁` by `Q.edge_nodup`, and not
of `P` because `f`'s two endpoints are both outside `P`'s interior while every edge of `P`
(at `2 ≤ P.length`) has an interior endpoint. `exists_cyclic_data_of_closed_path` then packages
`R` as `Fin (R.length + 1)`-cyclic data, and `R.length + 1 = P.length + Q.length`. -/
private lemma le_length_add_length_of_girthGE {G : Graph α β} {g : ℕ} (hg : G.GirthGE g)
    {P : WList α β} (hP : G.IsPath P) (hlen : 2 ≤ P.length)
    {Q : WList α β} (hQ : (G - {x | x ∈ P ∧ x ≠ P.first ∧ x ≠ P.last}).IsPath Q)
    (hQf : Q.first = P.first) (hQl : Q.last = P.last) :
    g ≤ P.length + Q.length := by
  classical
  set interior : Set α := {x | x ∈ P ∧ x ≠ P.first ∧ x ≠ P.last} with hidef
  have hle : (G - interior) ≤ G := deleteVerts_le
  -- `P` has two distinct ends, so the side path `Q` carries at least one edge.
  have hPfl : P.first ≠ P.last :=
    (WList.first_ne_last_iff hP.nodup).mpr (WList.length_pos_iff.mp (by omega))
  obtain ⟨u, f, Q₁, rfl⟩ : ∃ u f Q₁, Q = WList.cons u f Q₁ :=
    WList.Nonempty.exists_cons
      ((WList.first_ne_last_iff hQ.nodup).mp (by rw [hQf, hQl]; exact hPfl))
  have hQedge : (WList.cons u f Q₁).edge.Nodup := hQ.edge_nodup
  rw [WList.first_cons] at hQf
  subst hQf
  rw [WList.last_cons] at hQl
  rw [WList.cons_length]
  rw [cons_isPath_iff] at hQ
  obtain ⟨hflink, hQ₁, huQ₁⟩ := hQ
  -- every vertex of `Q₁` is a side vertex, hence outside `P`'s interior
  have hsideNotInt : ∀ x ∈ Q₁, x ∉ interior := fun x hx =>
    (deleteVerts_vertexSet G interior ▸ hQ₁.isWalk.vertex_mem_of_mem hx).2
  have hQ₁G : G.IsPath Q₁.reverse := (hQ₁.of_le hle).reverse
  have hQ₁rf : Q₁.reverse.first = P.last := by rw [WList.reverse_first]; exact hQl
  have hQ₁rl : Q₁.reverse.last = Q₁.first := WList.reverse_last
  have hinter : ∀ x, x ∈ P → x ∈ Q₁.reverse → x = P.last := by
    intro x hxP hxQ
    rw [WList.mem_reverse] at hxQ
    have hxnot : x ∉ interior := hsideNotInt x hxQ
    by_contra hxne
    exact hxnot ⟨hxP, fun heq => huQ₁ (heq ▸ hxQ), hxne⟩
  set R : WList α β := P ++ Q₁.reverse with hRdef
  have hRpath : G.IsPath R := hP.append hQ₁G hQ₁rf.symm hinter
  have hRfirst : R.first = P.first := WList.append_first_of_eq hQ₁rf.symm
  have hRlast : R.last = Q₁.first := by rw [hRdef, WList.append_last, hQ₁rl]
  have hRlen : R.length = P.length + Q₁.length := by
    rw [hRdef, WList.append_length, WList.reverse_length]
  have hfG : G.IsLink f P.first Q₁.first := hflink.of_le hle
  have hfclose : G.IsLink f R.last R.first := by rw [hRlast, hRfirst]; exact hfG.symm
  -- `f` is no edge of `P`: both its ends avoid `P`'s interior, but every `P`-edge has one.
  have hfnotP : f ∉ P.edge := by
    intro hfP
    obtain ⟨k, hk, hkeq⟩ := List.getElem_of_mem hfP
    have hk' : k < P.length := by rwa [WList.length_edge] at hk
    have h : G.IsLink (P.edge[k]'hk) (P.get k) (P.get (k + 1)) :=
      hP.isWalk.isLink_of_dInc (dIncAt P k hk')
    rw [hkeq] at h
    rcases h.eq_and_eq_or_eq_and_eq hfG with ⟨h1, h2⟩ | ⟨_, h2⟩
    · have hk0 : k = 0 := eq_zero_of_get_eq_first hP.nodup hk'.le h1
      have hint : P.get (k + 1) ∈ interior :=
        ⟨WList.get_mem P (k + 1),
          fun heq => by
            have := eq_zero_of_get_eq_first hP.nodup (by omega) heq; omega,
          fun heq => by
            have := eq_length_of_get_eq_last hP.nodup (by omega) heq; omega⟩
      exact hsideNotInt Q₁.first WList.first_mem (h2 ▸ hint)
    · have := eq_zero_of_get_eq_first hP.nodup (by omega : k + 1 ≤ P.length) h2
      omega
  have hfnotR : f ∉ R.edge := by
    simp only [hRdef, WList.append_edge, List.mem_append, WList.reverse_edge, List.mem_reverse,
      not_or]
    refine ⟨hfnotP, fun hfQ₁ => ?_⟩
    rw [WList.cons_edge, List.nodup_cons] at hQedge
    exact hQedge.1 hfQ₁
  obtain ⟨vtx, edge, hvtx, hedge, hlink, -, -, -⟩ :=
    exists_cyclic_data_of_closed_path hRpath (by omega) hfclose hfnotR
  have := hg (m := R.length + 1) (by omega) hvtx hedge hlink
  omega

/-- **M4**: a side path between the two ends of a maximal degree-`2` chain is long
(`lem:pencil-chain-side-distance`, first pin). If `G` has no proper rigid subgraph in the
`n`-dof regime, `P` is a path of length `≥ 2` whose first vertex is a hub (degree `≥ 3`), and
`Q` is a path of the side `G − P.interior` joining `P`'s two ends, then
`bodyBarDim n + 1 ≤ P.length + Q.length`. Route: the hub forces girth `≥ bodyBarDim n + 1`
(`girthGE_of_noRigid_of_three_le_degree`, G3), and `P` together with `Q` closes into a single
cycle on `P.length + Q.length` vertices (`le_length_add_length_of_girthGE`).

At `bodyBarDim n = 6` and a chain of `m = P.length - 1` interior vertices this is the
`dist_{G − chain}(w, v) ≥ 6 - m` bound of the consumed shape: a direct `w`–`v` edge is a side
path with `Q.length = 1`, which the inequality refutes exactly for `m ≤ 4`. The interior's
degree-`2` closure `_hdeg` is not needed for the bound (the deleted set is defined
syntactically from `P`); it is kept in the signature because every consumer carries it and
`lem:pencil-chain-side-distance` states it. -/
theorem le_length_add_length_of_isPath_deleteVerts_interior_of_noRigid [Finite α] [Finite β]
    {G : Graph α β} [G.Simple] {n : ℕ} (hD : 3 ≤ bodyBarDim n)
    (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n)
    {P : WList α β} (hP : G.IsPath P) (hlen : 2 ≤ P.length)
    (_hdeg : ∀ x ∈ P, x ≠ P.first → x ≠ P.last → G.degree x = 2)
    (hfirst : 3 ≤ G.degree P.first)
    {Q : WList α β} (hQ : (G - {x | x ∈ P ∧ x ≠ P.first ∧ x ≠ P.last}).IsPath Q)
    (hQf : Q.first = P.first) (hQl : Q.last = P.last) :
    bodyBarDim n + 1 ≤ P.length + Q.length :=
  le_length_add_length_of_girthGE (girthGE_of_noRigid_of_three_le_degree hD hnp hfirst)
    hP hlen hQ hQf hQl

/-- **M4′**: the `ℕ∞` form of M4 (`lem:pencil-chain-side-distance`, second pin), stated against
the side's own `Graph.eDist` instead of a chosen side path. Route: if the two chain ends are not
`ConnBetween` in the side the distance is `⊤` and the bound is vacuous — which is why this form
needs no `2`-edge-connectivity; otherwise `ConnBetween.exists_isPath_length_eq_eDist` realizes
the distance by a side path and M4 closes it. -/
theorem le_length_add_eDist_deleteVerts_interior_of_noRigid [Finite α] [Finite β]
    {G : Graph α β} [G.Simple] {n : ℕ} (hD : 3 ≤ bodyBarDim n)
    (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n)
    {P : WList α β} (hP : G.IsPath P) (hlen : 2 ≤ P.length)
    (hdeg : ∀ x ∈ P, x ≠ P.first → x ≠ P.last → G.degree x = 2)
    (hfirst : 3 ≤ G.degree P.first) :
    ((bodyBarDim n + 1 : ℕ) : ℕ∞) ≤ (P.length : ℕ∞) +
      (G - {x | x ∈ P ∧ x ≠ P.first ∧ x ≠ P.last}).eDist P.first P.last := by
  by_cases hconn :
      (G - {x | x ∈ P ∧ x ≠ P.first ∧ x ≠ P.last}).ConnBetween P.first P.last
  · obtain ⟨Q, hQ, hQf, hQl, hQlen⟩ := hconn.exists_isPath_length_eq_eDist
    rw [← hQlen]
    exact_mod_cast le_length_add_length_of_isPath_deleteVerts_interior_of_noRigid hD hnp hP hlen
      hdeg hfirst hQ hQf hQl
  · rw [eDist_eq_top_iff.mpr hconn]
    simp

end Graph
