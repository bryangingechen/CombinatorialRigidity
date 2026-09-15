/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Induction.ForestSurgery.ChainExtraction
import CombinatorialRigidity.Molecular.Induction.Girth

/-!
# The maximal degree-two chain's side graph (`sec:pencil-girth-chain`)

Phase 39 (PENCIL), Lean track: leaves **M3a**, **M3b** and **M1** of the girth-and-chain design
pass (`notes/Phase39-design.md` § *Lean-track design pass (2026-09-15): checklist items 1–2*),
pinning `lem:pencil-chain-side-connected` and `lem:pencil-chain-walk-extension` of
`blueprint/src/chapter/pencil.tex` § *Girth and degree-two chains under no proper rigid
subgraph*. The trichotomy dispatch (M2) and the side-distance leaves (M4, M4′) are not built
here; they get their own sections below when landed.

* `Graph.connected_deleteVerts_interior_of_twoEdgeConnected` (M3a): deleting a path's interior
  (every vertex but the two ends) from a `2`-edge-connected graph leaves a connected side.
* `Graph.degree_deleteVerts_interior_add_one` (M3b): the side loses exactly one edge at each
  path end — the one edge running from that end into the deleted interior.
* `Graph.exists_cycleData_or_closed_or_terminated_of_twoEdgeConnected` (M1): a degree-`2` chain
  extends until it either exhausts a cycle, closes back onto its own start at a degree-`≥ 3`
  anchor, or terminates at a degree-`≥ 3` vertex.

All three leaves need only `TwoEdgeConnected`/`Simple`/`Loopless` plus the interior's degree-`2`
closure, no girth; the private helpers below package the shared fact that an interior vertex's
only `G`-neighbours are its two path-flanking vertices (`isLink_eq_of_degree_eq_two`,
`ForestSurgery/ChainExtraction.lean`'s `chainData_of_isPath` is the template).
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

end Graph
