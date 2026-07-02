/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Induction.ForestSurgery.Reduction
import Mathlib.Data.List.GetD

/-!
# Chain extraction at general `n` (KT Lemma 4.6, ENTRY leaf E2)

Phase 23g (`notes/Phase23g.md`; design `notes/Phase23-design.md` §(4.107), §(4.107.D),
§(4.107.G)). This file houses the **E2d** ladder — the maximal-chain walk-builder and the
Katoh–Tanigawa (2011) display (4.6)–(4.9) counting contradiction that discharges
`Graph.chainData_or_cycleData_of_noRigid` (the `E2` leaf of the ENTRY ladder, KT Lemma 4.6) — plus
the numeric linking fact **E2e**. New file (below-contract deviation from §(4.107.D)'s
`ForestSurgery/Reduction.lean` pin, settled in §(4.107.G.2): `Reduction.lean` is past the ~1500-LoC
tripwire, and only `Molecular/AlgebraicInduction/PanelLayer.lean` imports it, so the seam is clean.

This commit lands **E2d-1**, the path → `ChainData` bridge, the first rung of the ladder
(build order per §(4.107.G.5): E2d-1 → E2d-2 → E2d-3 → E2e → E2d-4 → E2d-5 → E2d-6 → E2d-7 →
E2-assembly):

* `isLink_eq_of_degree_eq_two`: at a degree-2 vertex, any two distinct incident edges are *all*
  of its incident edges — the closure helper the interior degree-2 vertices of a chain need.
* `chainData_of_isPath`: a length-`n` path all of whose non-endpoint vertices have this degree-2
  closure packages into a `Graph.ChainData n` (the chain disjunct of the E2d-4 walk-trichotomy).
-/

namespace Graph

variable {α β : Type*}

/-! ## E2d-1 — the path → `ChainData` bridge -/

/-- **A degree-2 vertex's incident edges are exactly its two named ones** (Katoh–Tanigawa 2011
Lemma 4.6, the interior degree-2 closure `deg_two` a chain vertex needs). Given `G.degree v = 2`
and two distinct edges `e₁ ≠ e₂` each incident to `v` (via `IsLink`), every `G`-edge at `v` is one
of them: the loopless incidence set `E(G, v)` has `ncard` exactly `G.degree v = 2`
(`degree_eq_ncard_inc`) and contains `{e₁, e₂}`, which itself has `ncard = 2` (`e₁ ≠ e₂`), so the
two sets coincide (`Set.eq_of_subset_of_ncard_le`). -/
theorem isLink_eq_of_degree_eq_two [Finite β] {G : Graph α β} [G.Loopless] {v x₁ x₂ : α}
    {e₁ e₂ : β} (hdeg : G.degree v = 2) (hne : e₁ ≠ e₂)
    (h₁ : G.IsLink e₁ v x₁) (h₂ : G.IsLink e₂ v x₂) :
    ∀ e x, G.IsLink e v x → e = e₁ ∨ e = e₂ := by
  have hsub : ({e₁, e₂} : Set β) ⊆ E(G, v) := by
    rintro e (rfl | rfl)
    exacts [h₁.inc_left, h₂.inc_left]
  have hE2 : E(G, v).ncard = 2 := by rw [← degree_eq_ncard_inc]; exact hdeg
  have hP2 : ({e₁, e₂} : Set β).ncard = 2 := Set.ncard_pair hne
  have heq : ({e₁, e₂} : Set β) = E(G, v) :=
    Set.eq_of_subset_of_ncard_le hsub (hE2.trans hP2.symm).le
  intro e x he
  have hmem : e ∈ E(G, v) := he.inc_left
  rw [← heq] at hmem
  simpa using hmem

/-- **A length-`n` path whose interior vertices all have degree `2` packages into a
`Graph.ChainData n`** (Katoh–Tanigawa 2011 Lemma 4.6, the chain disjunct; ENTRY leaf E2d-1,
`notes/Phase23-design.md` §(4.107.G.5)). The `WList`/`IsPath` walk `P` supplies the `Fin`-indexed
records at the boundary: `vtx i := P.get i`, `edge i := P.edge[i]`, with `vtx_inj`/`edge_inj` from
the path's vertex/edge `Nodup` (via `WList.idxOf_get` / `List.Nodup.getElem_inj_iff`), `link` the
per-index `DInc` fact (`WList.DInc_get_get_succ` + `IsWalk.isLink_of_dInc`), and `deg_two` at an
interior index `0 < i < d` from `hdeg` + `isLink_eq_of_degree_eq_two` applied to the two path edges
flanking that vertex (`P.edge[i-1]`, oriented in via `.symm`, and `P.edge[i]`, oriented out). -/
theorem chainData_of_isPath [Finite α] [Finite β] {G : Graph α β} [G.Loopless] {n : ℕ}
    {P : WList α β} (hP : G.IsPath P) (hlen : P.length = n) (hn : 1 ≤ n)
    (hdeg : ∀ x ∈ P, x ≠ P.first → x ≠ P.last → G.degree x = 2)
    {e₀ : β} (he₀ : e₀ ∉ E(G)) :
    Nonempty (G.ChainData n) := by
  classical
  -- The per-index outgoing `IsLink` fact, reused for both `link` and `deg_two`.
  have hlinkAt : ∀ (m : ℕ) (hm : m < P.length),
      G.IsLink (P.edge[m]'(by rw [WList.length_edge]; omega))
        (P.get m) (P.get (m + 1)) :=
    fun m hm => hP.isWalk.isLink_of_dInc (WList.DInc_get_get_succ hm)
  have hvtx_inj : Function.Injective (fun i : Fin (P.length + 1) => P.get (i : ℕ)) := by
    intro i j hij
    have hij' : P.get (i : ℕ) = P.get (j : ℕ) := hij
    have h1 := WList.idxOf_get hP.nodup (Nat.le_of_lt_succ i.isLt)
    have h2 := WList.idxOf_get hP.nodup (Nat.le_of_lt_succ j.isLt)
    rw [hij'] at h1
    exact Fin.ext (h1.symm.trans h2)
  have hedge_inj : Function.Injective
      (fun i : Fin P.length => P.edge[(i : ℕ)]'(by rw [WList.length_edge]; exact i.isLt)) := by
    intro i j hij
    have hij' : P.edge[(i : ℕ)]'(by rw [WList.length_edge]; exact i.isLt) =
        P.edge[(j : ℕ)]'(by rw [WList.length_edge]; exact j.isLt) := hij
    exact Fin.ext (hP.edge_nodup.getElem_inj_iff.mp hij')
  have hvtx_mem : ∀ i : Fin (P.length + 1), P.get (i : ℕ) ∈ V(G) :=
    fun i => hP.isWalk.vertex_mem_of_mem (WList.get_mem P (i : ℕ))
  have hlink : ∀ i : Fin P.length,
      G.IsLink (P.edge[(i : ℕ)]'(by rw [WList.length_edge]; exact i.isLt))
        (P.get (i : ℕ)) (P.get ((i : ℕ) + 1)) :=
    fun i => hlinkAt (i : ℕ) i.isLt
  have hdeg_two : ∀ i : Fin P.length, 0 < (i : ℕ) →
      ∀ e x, G.IsLink e (P.get (i : ℕ)) x →
        e = P.edge[(i : ℕ) - 1]'(by rw [WList.length_edge]; omega) ∨
        e = P.edge[(i : ℕ)]'(by rw [WList.length_edge]; exact i.isLt) := by
    intro i hi e x hex
    have hne_first : P.get (i : ℕ) ≠ P.first := by
      intro heq
      have h1 := WList.idxOf_get hP.nodup i.isLt.le
      rw [heq, WList.idxOf_first] at h1
      omega
    have hne_last : P.get (i : ℕ) ≠ P.last := by
      intro heq
      have h1 := WList.idxOf_get hP.nodup i.isLt.le
      rw [heq, WList.idxOf_last P hP.nodup] at h1
      have hilt := i.isLt
      omega
    have hdeg2 : G.degree (P.get (i : ℕ)) = 2 :=
      hdeg (P.get (i : ℕ)) (WList.get_mem P (i : ℕ)) hne_first hne_last
    have hin : G.IsLink (P.edge[(i : ℕ) - 1]'(by rw [WList.length_edge]; omega))
        (P.get (i : ℕ)) (P.get ((i : ℕ) - 1)) := by
      have h := hlinkAt ((i : ℕ) - 1) (by omega)
      have heq1 := Nat.sub_add_cancel (show 1 ≤ (i : ℕ) by omega)
      rw [heq1] at h
      exact h.symm
    have hout := hlinkAt (i : ℕ) i.isLt
    have hne_edges : P.edge[(i : ℕ) - 1]'(by rw [WList.length_edge]; omega) ≠
        P.edge[(i : ℕ)]'(by rw [WList.length_edge]; exact i.isLt) := by
      intro h
      have := hP.edge_nodup.getElem_inj_iff.mp h
      omega
    exact isLink_eq_of_degree_eq_two hdeg2 hne_edges hin hout e x hex
  exact ⟨{ d := P.length
           hd := by omega
           d_eq := hlen
           vtx := fun i => P.get (i : ℕ)
           edge := fun i => P.edge[(i : ℕ)]'(by rw [WList.length_edge]; exact i.isLt)
           e₀ := e₀
           vtx_mem := hvtx_mem
           vtx_inj := hvtx_inj
           link := hlink
           edge_inj := hedge_inj
           deg_two := hdeg_two
           e₀_fresh := he₀ }⟩

/-! ## E2d-2 — the cycle-branch confinement -/

/-- **A closed all-degree-2 path confines the whole (preconnected) graph** (Katoh–Tanigawa 2011
Lemma 4.6, the cycle disjunct; ENTRY leaf E2d-2, `notes/Phase23-design.md` §(4.107.G.5)). If `P` is
a path with `G.IsLink f P.last P.first` closing it into a cycle (`f` not already a path edge) and
every vertex of `P` has degree `2`, preconnectivity forces `V(G)`/`E(G)` to be exactly the
walk's vertices/edges: any `y ∈ V(G)` is joined to `P.first` by a `G`-walk, and induction along
it never leaves `P` — at each step the current vertex's known two incident edges (the flanking
path edges, or `f` at an endpoint) are *all* of its incident edges (`isLink_eq_of_degree_eq_two`),
and both known far ends already lie on `P`. Every edge of `G` is pinned the same way, from either
of its (now-confined) endpoints. -/
theorem closed_path_degree_two_spanning [Finite β] {G : Graph α β} [G.Loopless]
    {P : WList α β} (hP : G.IsPath P) (hconn : G.Preconnected) {f : β}
    (hf : G.IsLink f P.last P.first) (hfP : f ∉ P.edge)
    (hdeg : ∀ x ∈ P, G.degree x = 2) :
    V(G) = {x | x ∈ P} ∧ E(G) = insert f {e | e ∈ P.edge} := by
  classical
  -- `P` has at least one edge: otherwise `f` would be a loop at `P.first = P.last`.
  have hn0 : P.length ≠ 0 := fun h0 =>
    hf.ne (by rw [← WList.get_length P, h0, WList.get_zero])
  -- the per-index outgoing `IsLink` fact (as in E2d-1).
  have hlinkAt : ∀ (m : ℕ) (hm : m < P.length),
      G.IsLink (P.edge[m]'(by rw [WList.length_edge]; omega))
        (P.get m) (P.get (m + 1)) :=
    fun m hm => hP.isWalk.isLink_of_dInc (WList.DInc_get_get_succ hm)
  -- **The confinement closure**: stepping from a `P`-vertex along any `G`-edge stays on `P`
  -- (the vertex end) / among `P`'s edges plus `f` (the edge end). The friction-avoidance idiom
  -- (TACTICS-QUIRKS § 48) applies throughout: no `i - a + b`-shaped arithmetic in source text.
  have hclosure : ∀ x, x ∈ P → ∀ e y, G.IsLink e x y →
      y ∈ P ∧ e ∈ insert f {e | e ∈ P.edge} := by
    intro x hx e y hxy
    have hdeg2 : G.degree x = 2 := hdeg x hx
    set i := P.idxOf x
    have hi : i ≤ P.length := WList.idxOf_mem_le hx
    have hgeti : P.get i = x := WList.get_idxOf P hx
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · -- `x = P.first`: the two known edges are the entry path edge and `f`.
      have hxfirst : x = P.first := by rw [← hgeti, hi0, WList.get_zero]
      subst hxfirst
      have he1 : G.IsLink (P.edge[0]'(by rw [WList.length_edge]; omega)) P.first (P.get 1) := by
        have h := hlinkAt 0 (by omega)
        rwa [WList.get_zero] at h
      have hfx : G.IsLink f P.first P.last := hf.symm
      have hne : f ≠ P.edge[0]'(by rw [WList.length_edge]; omega) := by
        intro h
        apply hfP
        rw [h]
        exact List.getElem_mem (by rw [WList.length_edge]; omega)
      rcases isLink_eq_of_degree_eq_two hdeg2 hne hfx he1 e y hxy with rfl | rfl
      · have hy : y = P.last := hfx.isLink_iff_eq.mp hxy
        subst hy
        exact ⟨WList.last_mem, Set.mem_insert _ _⟩
      · have hy : y = P.get 1 := he1.isLink_iff_eq.mp hxy
        subst hy
        exact ⟨WList.get_mem P 1,
          Set.mem_insert_of_mem f (List.getElem_mem (by rw [WList.length_edge]; omega))⟩
    · rcases hi.lt_or_eq with hilt | hieq
      · -- interior: `0 < i < P.length`, the two flanking path edges.
        have hb1 : G.IsLink (P.edge[i - 1]'(by rw [WList.length_edge]; omega))
            x (P.get (i - 1)) := by
          have h := hlinkAt (i - 1) (by omega)
          have heq1 := Nat.sub_add_cancel (show 1 ≤ i by omega)
          rw [heq1, hgeti] at h
          exact h.symm
        have hb2 : G.IsLink (P.edge[i]'(by rw [WList.length_edge]; exact hilt))
            x (P.get (i + 1)) := by
          have h := hlinkAt i hilt
          rwa [hgeti] at h
        have hne : (P.edge[i - 1]'(by rw [WList.length_edge]; omega)) ≠
            (P.edge[i]'(by rw [WList.length_edge]; exact hilt)) := by
          intro h
          have := hP.edge_nodup.getElem_inj_iff.mp h
          omega
        rcases isLink_eq_of_degree_eq_two hdeg2 hne hb1 hb2 e y hxy with rfl | rfl
        · have hy : y = P.get (i - 1) := hb1.isLink_iff_eq.mp hxy
          subst hy
          exact ⟨WList.get_mem P (i - 1),
            Set.mem_insert_of_mem f (List.getElem_mem (by rw [WList.length_edge]; omega))⟩
        · have hy : y = P.get (i + 1) := hb2.isLink_iff_eq.mp hxy
          subst hy
          exact ⟨WList.get_mem P (i + 1),
            Set.mem_insert_of_mem f (List.getElem_mem (by rw [WList.length_edge]; exact hilt))⟩
      · -- `x = P.last`: the two known edges are the exit path edge and `f`.
        have hxlast : x = P.last := by rw [← hgeti, hieq, WList.get_length]
        subst hxlast
        have he2 : G.IsLink (P.edge[i - 1]'(by rw [WList.length_edge]; omega))
            P.last (P.get (i - 1)) := by
          have h := hlinkAt (i - 1) (by omega)
          have heq1 := Nat.sub_add_cancel (show 1 ≤ i by omega)
          rw [heq1, hgeti] at h
          exact h.symm
        have hne : f ≠ P.edge[i - 1]'(by rw [WList.length_edge]; omega) := by
          intro h
          apply hfP
          rw [h]
          exact List.getElem_mem (by rw [WList.length_edge]; omega)
        rcases isLink_eq_of_degree_eq_two hdeg2 hne hf he2 e y hxy with rfl | rfl
        · have hy : y = P.first := hf.isLink_iff_eq.mp hxy
          subst hy
          exact ⟨WList.first_mem, Set.mem_insert _ _⟩
        · have hy : y = P.get (i - 1) := he2.isLink_iff_eq.mp hxy
          subst hy
          exact ⟨WList.get_mem P (i - 1),
            Set.mem_insert_of_mem f (List.getElem_mem (by rw [WList.length_edge]; omega))⟩
  -- Following a `G`-walk from `P.first`, `hclosure` never lets it leave `P`.
  have haux : ∀ {w : WList α β}, G.IsWalk w → w.first ∈ P → w.last ∈ P := by
    intro w hw
    induction hw with
    | nil => exact id
    | cons hw h ih => exact fun hfirst => ih (hclosure _ hfirst _ _ h).1
  have hVsub : V(G) ⊆ {x | x ∈ P} := by
    intro y hy
    obtain ⟨w, hw, hwf, hwl⟩ := hconn P.first y hP.isWalk.first_mem hy
    have h1 : w.first ∈ P := by rw [hwf]; exact WList.first_mem
    have h2 := haux hw h1
    rwa [hwl] at h2
  refine ⟨Set.Subset.antisymm hVsub (fun x hx => hP.isWalk.vertex_mem_of_mem hx),
    Set.Subset.antisymm ?_ ?_⟩
  · intro e he
    obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he
    exact (hclosure x (hVsub hxy.left_mem) e y hxy).2
  · intro e he'
    rcases he' with rfl | he'
    · exact hf.edge_mem
    · exact hP.isWalk.edge_mem_of_mem he'

/-! ## E2d-3 — the closed-walk packaging -/

/-- **The shared `Fin`-cyclic packaging core** (Katoh–Tanigawa 2011 Lemma 4.6, the cycle disjunct;
ENTRY leaf E2d-3, `notes/Phase23-design.md` §(4.107.G.5)). A path `P` closed into a cycle by an
edge `f` (not already a path edge) repackages as `Fin (P.length + 1)`-cyclic data matching `P`'s
own vertex/edge sets on the nose: `vtx i := P.get i` (`WList.get` is already total); `edge i :=
P.edge.getD i f`, which is `P`'s own edge at interior indices and falls back to the closing edge
`f` exactly at the wrap-around index `P.length` (`P.edge.length = P.length` by `length_edge`, so
that index is the first out-of-range one for `List.getD`). This core serves both the `CycleData`
consumer below and the lollipop's E2c call (E2d-4) — the same indexing work, written once. -/
theorem exists_cyclic_data_of_closed_path {G : Graph α β} {P : WList α β}
    (hP : G.IsPath P) (h2 : 2 ≤ P.length) {f : β}
    (hf : G.IsLink f P.last P.first) (hfP : f ∉ P.edge) :
    ∃ (vtx : Fin (P.length + 1) → α) (edge : Fin (P.length + 1) → β),
      Function.Injective vtx ∧ Function.Injective edge ∧
      (∀ i, G.IsLink (edge i) (vtx i) (vtx (i + ⟨1, by omega⟩))) ∧
      vtx ⟨0, by omega⟩ = P.first ∧
      Set.range vtx = {x | x ∈ P} ∧ Set.range edge = insert f {e | e ∈ P.edge} := by
  classical
  -- the per-index outgoing `IsLink` fact (as in E2d-1/E2d-2).
  have hlinkAt : ∀ (k : ℕ) (hk : k < P.length),
      G.IsLink (P.edge[k]'(by rw [WList.length_edge]; omega))
        (P.get k) (P.get (k + 1)) :=
    fun k hk => hP.isWalk.isLink_of_dInc (WList.DInc_get_get_succ hk)
  refine ⟨fun i => P.get (i : ℕ), fun i => P.edge.getD (i : ℕ) f, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `vtx` injective (E2d-1's `hvtx_inj`).
    intro i j hij
    have hij' : P.get (i : ℕ) = P.get (j : ℕ) := hij
    have h1 := WList.idxOf_get hP.nodup (Nat.le_of_lt_succ i.isLt)
    have h2' := WList.idxOf_get hP.nodup (Nat.le_of_lt_succ j.isLt)
    rw [hij'] at h1
    exact Fin.ext (h1.symm.trans h2')
  · -- `edge` injective: interior indices via `edge_nodup`, the wrap-around index via `hfP`.
    intro i j hij
    have hij' : P.edge.getD (i : ℕ) f = P.edge.getD (j : ℕ) f := hij
    rcases (Nat.le_of_lt_succ i.isLt).lt_or_eq with hilt | hieq
    · rcases (Nat.le_of_lt_succ j.isLt).lt_or_eq with hjlt | hjeq
      · have hbi : (i : ℕ) < P.edge.length := by rw [WList.length_edge]; exact hilt
        have hbj : (j : ℕ) < P.edge.length := by rw [WList.length_edge]; exact hjlt
        rw [List.getD_eq_getElem (l := P.edge) (d := f) hbi,
          List.getD_eq_getElem (l := P.edge) (d := f) hbj] at hij'
        exact Fin.ext (hP.edge_nodup.getElem_inj_iff.mp hij')
      · exfalso
        have hbi : (i : ℕ) < P.edge.length := by rw [WList.length_edge]; exact hilt
        have hbj : P.edge.length ≤ (j : ℕ) := by rw [WList.length_edge]; omega
        rw [List.getD_eq_getElem (l := P.edge) (d := f) hbi,
          List.getD_eq_default (l := P.edge) (d := f) hbj] at hij'
        apply hfP
        rw [← hij']
        exact List.getElem_mem hbi
    · rcases (Nat.le_of_lt_succ j.isLt).lt_or_eq with hjlt | hjeq
      · exfalso
        have hbi : P.edge.length ≤ (i : ℕ) := by rw [WList.length_edge]; omega
        have hbj : (j : ℕ) < P.edge.length := by rw [WList.length_edge]; exact hjlt
        rw [List.getD_eq_default (l := P.edge) (d := f) hbi,
          List.getD_eq_getElem (l := P.edge) (d := f) hbj] at hij'
        apply hfP
        rw [hij']
        exact List.getElem_mem hbj
      · exact Fin.ext (hieq.trans hjeq.symm)
  · -- the cyclic link: interior indices via `hlinkAt`, the wrap-around index via `hf`.
    intro i
    change G.IsLink (P.edge.getD (i : ℕ) f) (P.get (i : ℕ))
      (P.get (((i + (⟨1, by omega⟩ : Fin (P.length + 1))) : Fin (P.length + 1)) : ℕ))
    rcases (Nat.le_of_lt_succ i.isLt).lt_or_eq with hilt | hieq
    · have hb : (i : ℕ) < P.edge.length := by rw [WList.length_edge]; exact hilt
      have hsucc : (((i + (⟨1, by omega⟩ : Fin (P.length + 1))) : Fin (P.length + 1)) : ℕ)
          = (i : ℕ) + 1 := Fin.val_add_eq_of_add_lt (by simp; omega)
      rw [List.getD_eq_getElem (l := P.edge) (d := f) hb, hsucc]
      exact hlinkAt (i : ℕ) hilt
    · have hb : P.edge.length ≤ (i : ℕ) := by rw [WList.length_edge]; omega
      have hsucc : (((i + (⟨1, by omega⟩ : Fin (P.length + 1))) : Fin (P.length + 1)) : ℕ) = 0 := by
        rw [Fin.val_add, hieq]
        simp
      rw [List.getD_eq_default (l := P.edge) (d := f) hb, hieq, WList.get_length, hsucc,
        WList.get_zero]
      exact hf
  · -- `vtx ⟨0, _⟩ = P.first`.
    change P.get ((⟨0, by omega⟩ : Fin (P.length + 1)) : ℕ) = P.first
    exact WList.get_zero P
  · -- `Set.range vtx = {x | x ∈ P}`.
    apply Set.Subset.antisymm
    · rintro x ⟨i, rfl⟩
      exact WList.get_mem P (i : ℕ)
    · intro x hx
      have hidx : P.idxOf x ≤ P.length := WList.idxOf_mem_le hx
      exact ⟨⟨P.idxOf x, by omega⟩, WList.get_idxOf P hx⟩
  · -- `Set.range edge = insert f {e | e ∈ P.edge}`.
    apply Set.Subset.antisymm
    · rintro _ ⟨i, rfl⟩
      change P.edge.getD (i : ℕ) f ∈ insert f {e | e ∈ P.edge}
      rcases (Nat.le_of_lt_succ i.isLt).lt_or_eq with hilt | hieq
      · have hb : (i : ℕ) < P.edge.length := by rw [WList.length_edge]; exact hilt
        rw [List.getD_eq_getElem (l := P.edge) (d := f) hb]
        exact Set.mem_insert_of_mem f (List.getElem_mem hb)
      · have hb : P.edge.length ≤ (i : ℕ) := by rw [WList.length_edge]; omega
        rw [List.getD_eq_default (l := P.edge) (d := f) hb]
        exact Set.mem_insert _ _
    · intro e he
      rcases he with heq | he
      · have hb : P.edge.length ≤ P.length := (WList.length_edge P).le
        exact ⟨⟨P.length, by omega⟩,
          by rw [heq]; exact List.getD_eq_default (l := P.edge) (d := f) hb⟩
      · obtain ⟨k, hk, hke⟩ := List.getElem_of_mem he
        have hk' : k < P.length := by rwa [WList.length_edge] at hk
        exact ⟨⟨k, by omega⟩, (List.getD_eq_getElem (l := P.edge) (d := f) hk).trans hke⟩

/-- **The `CycleData` consumer of the closed-walk core** (Katoh–Tanigawa 2011 Lemma 4.6, the
cycle disjunct; ENTRY leaf E2d-3, `notes/Phase23-design.md` §(4.107.G.5)). Combines the core's
`Fin`-cyclic data with E2d-2's confinement (`closed_path_degree_two_spanning`) to discharge
`CycleData`'s two surjectivity fields: `V(G) = {x | x ∈ P} = Set.range vtx` and likewise for
`E(G)`, so every `G`-vertex (resp. edge) is a cycle vertex (resp. edge). -/
theorem cycleData_of_closed_path [Finite α] [Finite β] {G : Graph α β} [G.Loopless]
    {P : WList α β} (hP : G.IsPath P) (h2 : 2 ≤ P.length) {f : β}
    (hf : G.IsLink f P.last P.first) (hfP : f ∉ P.edge)
    (hdeg : ∀ x ∈ P, G.degree x = 2) (hconn : G.Preconnected) :
    ∃ cy : G.CycleData, cy.m = P.length + 1 := by
  obtain ⟨vtx, edge, hvtx_inj, hedge_inj, hlink, -, hrv, hre⟩ :=
    exists_cyclic_data_of_closed_path hP h2 hf hfP
  obtain ⟨hVeq, hEeq⟩ := closed_path_degree_two_spanning hP hconn hf hfP hdeg
  refine ⟨{ m := P.length + 1
            hm := by omega
            vtx := vtx
            edge := edge
            vtx_inj := hvtx_inj
            edge_inj := hedge_inj
            link := hlink
            vtx_surj := fun x hx => by
              change x ∈ Set.range vtx
              rw [hrv]
              rwa [hVeq] at hx
            edge_surj := fun e he => by
              change e ∈ Set.range edge
              rw [hre]
              rwa [hEeq] at he }, rfl⟩

end Graph
