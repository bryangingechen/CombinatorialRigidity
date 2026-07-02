/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Induction.ForestSurgery.Reduction
import Mathlib.Data.List.GetD

/-!
# Chain extraction at general `n` (KT Lemma 4.6, ENTRY leaves E2 + E3)

Phase 23g (`notes/Phase23g.md`; design `notes/Phase23-design.md` §(4.107), §(4.107.D),
§(4.107.G)). This file houses the **E2d** ladder — the maximal-chain walk-builder and the
Katoh–Tanigawa (2011) display (4.6)–(4.9) counting contradiction that discharges
`Graph.chainData_or_cycleData_of_noRigid` (the `E2` leaf of the ENTRY ladder, KT Lemma 4.6) —
plus the numeric linking fact **E2e** and the general extractor **E3**. New file
(below-contract deviation from §(4.107.D)'s `ForestSurgery/Reduction.lean` pin, settled in
§(4.107.G.2): `Reduction.lean` is past the ~1500-LoC tripwire, and only
`Molecular/AlgebraicInduction/PanelLayer.lean` imports it, so the seam is clean.

Build order per §(4.107.G.5): E2d-1 → E2d-2 → E2d-3 → E2e → E2d-4 → E2d-5 → E2d-6 → E2d-7 →
E2-assembly → E3 — all landed. E2d-1/E2d-2/E2d-3/E2e/E2d-4/E2d-5/E2d-6/E2d-7 are the
path→`ChainData` bridge, the cycle-branch confinement, the closed-walk packaging, the numeric
linking fact, the capped-trichotomy walk-builder, chain-walk determinism, the charging bound
(fiber lemma + double count), and the KT (4.8)/(4.9) arithmetic close, respectively; E2-assembly
composes the ladder into `chainData_or_cycleData_of_noRigid` (§(4.107.D)'s pinned public
signature), closing the ENTRY leaf **E2** (KT Lemma 4.6) in full — see `notes/Phase23g.md` for
the per-leaf detail. This commit lands **E3**, `Graph.chainData_extract`: composes E2 with the
landed Lemma-4.8 stack (`splitOff_isMinimalKDof`/`splitOff_simple_of_noRigid_of_card`) at the
interior chain vertex `v₁`, discharging the ENTRY interface `hextract` at general `n`. E2's other
consumer, the Lemma-5.4 cycle brick **E5** (discharging `hcycle`), is next.
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

/-! ## E2e — the numeric linking fact -/

/-- **Katoh–Tanigawa 2011's display above (4.9)** (ENTRY leaf E2e,
`notes/Phase23-design.md` §(4.107.G.5)): for `D = bodyBarDim n ≥ 3` (the molecular regime
`n ≥ 2`, derived below via the `2D = n(n+1)` identity) and `i ≥ 3`, the KT (4.6)–(4.9) charging
count's linking inequality `i(n−2) + 2 ≤ (D−1)(i−2)` holds. Cast to `ℤ` and closed by `nlinarith`
against two nonnegative slack terms: `(n−2)(n−3) ≥ 0` (true for every natural `n`, since no
integer lies strictly between `2` and `3`) accounts for the `i = 3` floor case (equality at
`n = 2` and at `n = 3`), and `(i−3)(n²−n+2) ≥ 0` (the quadratic `n²−n+2` is always positive)
accounts for the slope in `i` above that floor. -/
theorem kt_lemma_46_linking {n i : ℕ} (hD : 3 ≤ bodyBarDim n) (hi : 3 ≤ i) :
    i * (n - 2) + 2 ≤ (bodyBarDim n - 1) * (i - 2) := by
  have hbb : 2 * bodyBarDim n = n * (n + 1) := by
    rw [bodyBarDim, Nat.mul_div_cancel' (Nat.even_mul_succ_self n).two_dvd]
  have hn2 : 2 ≤ n := by
    by_contra h
    have h' : n < 2 := by omega
    interval_cases n <;> omega
  have hD1 : 1 ≤ bodyBarDim n := by omega
  have hi2 : 2 ≤ i := by omega
  zify [hn2, hi2, hD1]
  have hbbZ : 2 * (bodyBarDim n : ℤ) = (n : ℤ) * ((n : ℤ) + 1) := by exact_mod_cast hbb
  have hslack : (0 : ℤ) ≤ ((n : ℤ) - 2) * ((n : ℤ) - 3) := by
    rcases Nat.lt_or_ge n 3 with h | h
    · have hn2' : n = 2 := by omega
      subst hn2'
      norm_num
    · have h3 : (3 : ℤ) ≤ (n : ℤ) := by exact_mod_cast h
      nlinarith
  have hquad : (0 : ℤ) ≤ (n : ℤ) ^ 2 - (n : ℤ) + 2 := by nlinarith [sq_nonneg (2 * (n : ℤ) - 1)]
  have hi3 : (0 : ℤ) ≤ (i : ℤ) - 3 := by
    have h3 : (3 : ℤ) ≤ (i : ℤ) := by exact_mod_cast hi
    linarith
  nlinarith [hbbZ, hslack, mul_nonneg hi3 hquad]

/-- **The lollipop's cap** (ENTRY leaf E2e companion, `notes/Phase23-design.md` §(4.107.G.5)):
`n ≤ bodyBarDim n`, via the `2 · bodyBarDim n = n(n+1)` identity — what keeps a `≤ n`-cycle's
vertex count `m ≤ n` inside the `D = bodyBarDim n` floor `isKDof_zero_of_cycle` needs
(E2d-4's lollipop-exclusion, §(4.107.G.7)(ii)). -/
theorem le_bodyBarDim (n : ℕ) : n ≤ bodyBarDim n := by
  have hbb : 2 * bodyBarDim n = n * (n + 1) := by
    rw [bodyBarDim, Nat.mul_div_cancel' (Nat.even_mul_succ_self n).two_dvd]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h2 : n * 2 ≤ n * (n + 1) := Nat.mul_le_mul_left n (by omega)
    omega

/-! ## E2d-4 — the capped trichotomy builder -/

/-- **The capped chain-walk trichotomy** (Katoh–Tanigawa 2011 Lemma 4.6, the walk-builder;
ENTRY leaf E2d-4, `notes/Phase23-design.md` §(4.107.G.3)/(G.5)). Starting from any incidence
`(v₀, f, x₀)` of a minimal `0`-dof-graph with no proper rigid subgraph, extend a path at its
last vertex (whose exit edge is supplied by the degree-`2` closure, `exists_splitOff_data_of_
degree_eq_two`): either the path reaches length `n` (the chain disjunct, bridged via
`chainData_of_isPath`), or it closes back onto its own start (the cycle disjunct, via
`cycleData_of_closed_path` when the start also has degree `2` — the "lollipop" degree-`≥ 3`
start is excluded, a parallel pair at length `2` via `G.Simple`, or via
`cycle_isProperRigidSubgraph` + `hnp` at length `≥ 3`), or its last vertex has degree `≥ 3`
(the terminated walk KT's charging count consumes). Strong induction on `n − P.length`. -/
theorem chainWalk_trichotomy [DecidableEq β] [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hD : 3 ≤ bodyBarDim n) (hV3 : 3 ≤ V(G).ncard) (hG : G.IsMinimalKDof n 0)
    (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n)
    (hfresh : ∃ e₀ : β, e₀ ∉ E(G))
    {v₀ x₀ : α} {f : β} (hf : G.IsLink f v₀ x₀) :
    (Nonempty (G.ChainData n) ∨ ∃ cy : G.CycleData, cy.m ≤ n) ∨
    ∃ P : WList α β, G.IsPath P ∧ P.first = v₀ ∧
      (∃ hne : P.Nonempty, hne.firstEdge = f) ∧
      1 ≤ P.length ∧ P.length ≤ n - 1 ∧
      (∀ x ∈ P, x ≠ P.first → x ≠ P.last → G.degree x = 2) ∧
      3 ≤ G.degree P.last := by
  classical
  obtain ⟨e₀, he₀⟩ := hfresh
  have hD1 : 1 ≤ bodyBarDim n := by omega
  have hD2 : 2 ≤ bodyBarDim n := by omega
  have hV2 : 2 ≤ V(G).ncard := by omega
  have hbb : 2 * bodyBarDim n = n * (n + 1) := by
    rw [bodyBarDim, Nat.mul_div_cancel' (Nat.even_mul_succ_self n).two_dvd]
  have hn2 : 2 ≤ n := by
    by_contra h
    have h' : n < 2 := by omega
    interval_cases n <;> omega
  haveI hsimp : G.Simple := simple_of_isMinimalKDof_of_noRigid hD2 hV3 hG hnp
  haveI hloop : G.Loopless := loopless_of_isMinimalKDof hG
  have hconn : G.Preconnected := preconnected_of_isKDof_zero hD1 hG.1
  have hnD : n ≤ bodyBarDim n := le_bodyBarDim n
  have hv₀G : v₀ ∈ V(G) := hf.left_mem
  have hx₀G : x₀ ∈ V(G) := hf.right_mem
  have hv₀x₀ : v₀ ≠ x₀ := hf.ne
  have hdegv0ge2 : 2 ≤ G.degree v₀ := two_le_degree_of_isKDof_zero hD1 hG.1 hv₀G hV2
  -- The per-`Q` outgoing-`IsLink` fact at an index, shared across the recursion (E2d-1/2/3 style).
  have hlinkAt : ∀ (Q : WList α β), G.IsWalk Q → ∀ (k : ℕ) (hk : k < Q.length),
      G.IsLink (Q.edge[k]'(by rw [WList.length_edge]; omega)) (Q.get k) (Q.get (k + 1)) :=
    fun Q hQ k hk => hQ.isLink_of_dInc (WList.DInc_get_get_succ hk)
  -- `get` is injective on `[0, Q.length]` for a Nodup-vertex `Q` (E2d-1's `hvtx_inj`, generalized).
  have hget_inj : ∀ (Q : WList α β), Q.vertex.Nodup → ∀ {i j : ℕ},
      i ≤ Q.length → j ≤ Q.length → Q.get i = Q.get j → i = j := by
    intro Q hQ i j hi hj hij
    have h1 := WList.idxOf_get hQ hi
    have h2 := WList.idxOf_get hQ hj
    rw [hij] at h1
    exact h1.symm.trans h2
  -- The trichotomy's exit-edge finder: the OTHER edge at a known degree-`2` vertex.
  have hexit : ∀ {v w : α} {e : β}, v ∈ V(G) → w ≠ v → G.IsLink e v w → G.degree v = 2 →
      ∃ x g, x ≠ v ∧ g ≠ e ∧ G.IsLink g v x ∧ ∀ e' y, G.IsLink e' v y → e' = e ∨ e' = g := by
    intro v w e hv hwv hlink hdeg
    obtain ⟨a, b, eₐ, e_b, hav, hbv, haG, hbG, hne, hla, hlb, hclosure⟩ :=
      exists_splitOff_data_of_degree_eq_two hD1 hG.1 hv hlink.right_mem hwv hdeg
    rcases hclosure e w hlink with rfl | rfl
    · exact ⟨b, e_b, hbv, hne.symm, hlb, hclosure⟩
    · exact ⟨a, eₐ, hav, hne, hla, fun e' y h => (hclosure e' y h).symm⟩
  have hP₀path : G.IsPath (WList.cons v₀ f (WList.nil x₀)) := by
    rw [cons_isPath_iff]
    exact ⟨by simpa using hf, nil_isPath hx₀G, by simpa using hv₀x₀⟩
  have hP₀deg : ∀ x ∈ WList.cons v₀ f (WList.nil x₀),
      x ≠ (WList.cons v₀ f (WList.nil x₀)).first →
      x ≠ (WList.cons v₀ f (WList.nil x₀)).last → G.degree x = 2 := by
    intro x hx hxfirst hxlast
    simp only [WList.mem_cons_iff, WList.mem_nil_iff, WList.first_cons, WList.last_cons,
      WList.nil_last] at hx hxfirst hxlast
    rcases hx with rfl | rfl
    · exact absurd rfl hxfirst
    · exact absurd rfl hxlast
  -- The general claim, by strong induction on `n − P.length` (Reduction.lean's precedent
  -- pattern: `induction hM : … using Nat.strong_induction_on generalizing P`).
  have main : ∀ P : WList α β, G.IsPath P → P.first = v₀ →
      (∃ hne : P.Nonempty, hne.firstEdge = f) → 1 ≤ P.length → P.length ≤ n →
      (∀ x ∈ P, x ≠ P.first → x ≠ P.last → G.degree x = 2) →
      (Nonempty (G.ChainData n) ∨ ∃ cy : G.CycleData, cy.m ≤ n) ∨
      ∃ P' : WList α β, G.IsPath P' ∧ P'.first = v₀ ∧
        (∃ hne : P'.Nonempty, hne.firstEdge = f) ∧
        1 ≤ P'.length ∧ P'.length ≤ n - 1 ∧
        (∀ x ∈ P', x ≠ P'.first → x ≠ P'.last → G.degree x = 2) ∧
        3 ≤ G.degree P'.last := by
    intro P
    induction hM : n - P.length using Nat.strong_induction_on generalizing P with
    | _ M IH =>
    intro hP hPfirst hPfe hPlen1 hPlen hdeg
    by_cases hlenn : P.length = n
    · -- `P.length = n`: the chain disjunct.
      exact Or.inl (Or.inl (chainData_of_isPath hP hlenn (by omega) hdeg he₀))
    · have hltn : P.length < n := by omega
      by_cases hdeg3 : 3 ≤ G.degree P.last
      · -- `3 ≤ degree P.last`: terminated.
        exact Or.inr ⟨P, hP, hPfirst, hPfe, hPlen1, by omega, hdeg, hdeg3⟩
      · -- `degree P.last = 2` (from the `0`-dof min-degree floor): trichotomy on the exit edge.
        have hPlastG : P.last ∈ V(G) := hP.isWalk.vertex_mem_of_mem WList.last_mem
        have hdeg2 : G.degree P.last = 2 := by
          have h2 := two_le_degree_of_isKDof_zero hD1 hG.1 hPlastG hV2
          omega
        obtain ⟨hne, hfe⟩ := hPfe
        set entry_edge : β := P.edge[P.length - 1]'(by rw [WList.length_edge]; omega)
          with hentry_def
        have hentry : G.IsLink entry_edge (P.get (P.length - 1)) P.last := by
          rw [hentry_def]
          have h := hlinkAt P hP.isWalk (P.length - 1) (by omega)
          have heq1 : P.length - 1 + 1 = P.length := by omega
          rwa [heq1, WList.get_length] at h
        have hentry_ne : P.get (P.length - 1) ≠ P.last := hentry.ne
        obtain ⟨x, g, -, hgne, hgx, -⟩ := hexit hPlastG hentry_ne hentry.symm hdeg2
        -- General fact (independent of the trichotomy branch): `g` is not already a path edge —
        -- either it lands back on the entry edge (excluded by `hgne`) or it would force a second
        -- path edge to touch `P.last`, impossible for a `Nodup`-vertex path.
        have hgP : g ∉ P.edge := by
          intro hgmem
          obtain ⟨k, hk, hke⟩ := List.getElem_of_mem hgmem
          have hk' : k < P.length := by rwa [WList.length_edge] at hk
          have hkey : G.IsLink g (P.get k) (P.get (k + 1)) := by
            have h := hlinkAt P hP.isWalk k hk'
            rwa [hke] at h
          by_cases hklast : k = P.length - 1
          · apply hgne
            rw [hklast] at hkey
            have heq1 : P.length - 1 + 1 = P.length := by omega
            rw [heq1, WList.get_length] at hkey
            exact hkey.unique_edge hentry
          · have hlt1 : P.get k ≠ P.last := by
              intro heq
              have := hget_inj P hP.nodup hk'.le le_rfl (heq.trans (WList.get_length P).symm)
              omega
            have hlt2 : P.get (k + 1) ≠ P.last := by
              intro heq
              have := hget_inj P hP.nodup (by omega) le_rfl (heq.trans (WList.get_length P).symm)
              omega
            rcases hkey.eq_and_eq_or_eq_and_eq hgx with ⟨hk1, -⟩ | ⟨-, hk2⟩
            · exact hlt1 hk1
            · exact hlt2 hk2
        by_cases hxfirst : x = P.first
        · -- Closed: `m := P.length + 1 ≤ n` (the cap already fired at length `n` above).
          subst hxfirst
          by_cases hlen1 : P.length = 1
          · -- length `2`: `entry_edge` and `g` are a parallel pair — excluded by `G.Simple`.
            exfalso
            have h0 : P.length - 1 = 0 := by omega
            rw [h0, WList.get_zero] at hentry
            exact hgne (hentry.unique_edge hgx.symm).symm
          · have hlen2 : 2 ≤ P.length := by omega
            have hdegPfirst : 2 ≤ G.degree P.first := by rw [hPfirst]; exact hdegv0ge2
            by_cases hstart2 : G.degree P.first = 2
            · -- genuine cycle.
              have hdeg_all : ∀ y ∈ P, G.degree y = 2 := by
                intro y hy
                by_cases hyfirst : y = P.first
                · rw [hyfirst]; exact hstart2
                · by_cases hylast : y = P.last
                  · rw [hylast]; exact hdeg2
                  · exact hdeg y hy hyfirst hylast
              obtain ⟨cy, hcym⟩ := cycleData_of_closed_path hP hlen2 hgx hgP hdeg_all hconn
              exact Or.inl (Or.inr ⟨cy, by omega⟩)
            · -- the lollipop (length `≥ 3`, anchor degree `≥ 3`): excluded via E2c + `hnp`.
              have hstart3 : 3 ≤ G.degree P.first := by omega
              obtain ⟨vtx, edge, hvtx_inj, hedge_inj, hlink, hvtx0, hrv, -⟩ :=
                exists_cyclic_data_of_closed_path hP hlen2 hgx hgP
              haveI : NeZero (P.length + 1) := ⟨by omega⟩
              have hdeg' : ∀ y ∈ P, y ≠ P.first → G.degree y = 2 := by
                intro y hy hyfirst
                by_cases hylast : y = P.last
                · rw [hylast]; exact hdeg2
                · exact hdeg y hy hyfirst hylast
              have hvtx_deg : ∀ i : Fin (P.length + 1),
                  i ≠ (⟨0, by omega⟩ : Fin (P.length + 1)) → G.degree (vtx i) = 2 := by
                intro i hi0
                have hmem : vtx i ∈ P := by
                  have hmem' : vtx i ∈ Set.range vtx := ⟨i, rfl⟩
                  rwa [hrv] at hmem'
                have hnefirst : vtx i ≠ P.first := by
                  rw [← hvtx0]
                  exact fun heq => hi0 (hvtx_inj heq)
                exact hdeg' (vtx i) hmem hnefirst
              have hcl : ∀ i : Fin (P.length + 1),
                  i ≠ (⟨0, by omega⟩ : Fin (P.length + 1)) → ∀ e y,
                    G.IsLink e (vtx i) y → e = edge (i - ⟨1, by omega⟩) ∨ e = edge i := by
                intro i hi0 e y hey
                have heq1 : (i - (⟨1, by omega⟩ : Fin (P.length + 1))) + ⟨1, by omega⟩ = i := by
                  abel
                have hin : G.IsLink (edge (i - ⟨1, by omega⟩)) (vtx i)
                    (vtx (i - ⟨1, by omega⟩)) := by
                  have h := hlink (i - (⟨1, by omega⟩ : Fin (P.length + 1)))
                  rw [heq1] at h
                  exact h.symm
                have hout : G.IsLink (edge i) (vtx i) (vtx (i + ⟨1, by omega⟩)) := hlink i
                have hne_edges : edge (i - ⟨1, by omega⟩) ≠ edge i := by
                  intro h
                  have hii : i - (⟨1, by omega⟩ : Fin (P.length + 1)) = i := hedge_inj h
                  have hi0' : i.val ≠ 0 := fun h0 => hi0 (Fin.ext h0)
                  have hle : (⟨1, by omega⟩ : Fin (P.length + 1)) ≤ i :=
                    show (1 : ℕ) ≤ i.val by omega
                  have hval : (i - (⟨1, by omega⟩ : Fin (P.length + 1))).val = i.val - 1 :=
                    Fin.sub_val_of_le hle
                  rw [hii] at hval
                  omega
                exact isLink_eq_of_degree_eq_two (hvtx_deg i hi0) hne_edges hin hout e y hey
              have hdeg_start3 : 3 ≤ G.degree (vtx (⟨0, by omega⟩ : Fin (P.length + 1))) := by
                rw [hvtx0]; exact hstart3
              have hm3 : 3 ≤ P.length + 1 := by omega
              have hmD : P.length + 1 ≤ bodyBarDim n := by omega
              obtain ⟨H, hH⟩ :=
                cycle_isProperRigidSubgraph hD hm3 hmD hvtx_inj hedge_inj hlink hcl hdeg_start3
              exact (hnp H hH).elim
        · -- `x ≠ P.first`.
          by_cases hxmem : x ∈ P
          · -- impossible: `x` interior has degree `2` with both incidences path edges; `g` isn't.
            exfalso
            by_cases hxlast : x = P.last
            · rw [hxlast] at hgx
              exact hgx.ne rfl
            · have hdegx : G.degree x = 2 := hdeg x hxmem hxfirst hxlast
              have hgetj : P.get (P.idxOf x) = x := WList.get_idxOf P hxmem
              have hj0 : P.idxOf x ≠ 0 := by
                intro h0
                apply hxfirst
                rw [← hgetj, h0, WList.get_zero]
              have hjlen : P.idxOf x ≠ P.length := by
                intro hjl
                apply hxlast
                rw [← hgetj, hjl, WList.get_length]
              have hjlt : P.idxOf x < P.length := by
                have := WList.idxOf_mem_le hxmem
                omega
              have hin : G.IsLink (P.edge[P.idxOf x - 1]'(by rw [WList.length_edge]; omega)) x
                  (P.get (P.idxOf x - 1)) := by
                have h := hlinkAt P hP.isWalk (P.idxOf x - 1) (by omega)
                have heq1 : P.idxOf x - 1 + 1 = P.idxOf x := by omega
                rw [heq1, hgetj] at h
                exact h.symm
              have hout : G.IsLink (P.edge[P.idxOf x]'(by rw [WList.length_edge]; exact hjlt)) x
                  (P.get (P.idxOf x + 1)) := by
                have h := hlinkAt P hP.isWalk (P.idxOf x) hjlt
                rwa [hgetj] at h
              have hne_edges : P.edge[P.idxOf x - 1]'(by rw [WList.length_edge]; omega) ≠
                  P.edge[P.idxOf x]'(by rw [WList.length_edge]; exact hjlt) := by
                intro h
                have := hP.edge_nodup.getElem_inj_iff.mp h
                omega
              rcases isLink_eq_of_degree_eq_two hdegx hne_edges hin hout g P.last hgx.symm with
                h | h
              · apply hgP; rw [h]; exact List.getElem_mem (by rw [WList.length_edge]; omega)
              · apply hgP; rw [h]; exact List.getElem_mem (by rw [WList.length_edge]; exact hjlt)
          · -- `x ∉ P`: extend.
            have hP'path : G.IsPath (P.concat g x) := concat_isPath_iff.mpr ⟨hP, hgx, hxmem⟩
            have hP'first : (P.concat g x).first = v₀ := by
              rw [WList.concat_first]; exact hPfirst
            have hP'fe : ∃ hne' : (P.concat g x).Nonempty, hne'.firstEdge = f :=
              ⟨WList.concat_nonempty P g x, by rw [hne.firstEdge_concat]; exact hfe⟩
            have hP'len1 : 1 ≤ (P.concat g x).length := by rw [WList.concat_length]; omega
            have hP'len : (P.concat g x).length ≤ n := by rw [WList.concat_length]; omega
            have hP'deg : ∀ y ∈ P.concat g x, y ≠ (P.concat g x).first →
                y ≠ (P.concat g x).last → G.degree y = 2 := by
              intro y hy hyfirst hylast
              rw [WList.concat_last] at hylast
              rw [WList.concat_first] at hyfirst
              rw [WList.mem_concat] at hy
              rcases hy with hy | rfl
              · by_cases hyPlast : y = P.last
                · rw [hyPlast]; exact hdeg2
                · exact hdeg y hy hyfirst hyPlast
              · exact absurd rfl hylast
            exact IH (n - (P.concat g x).length) (by rw [WList.concat_length]; omega)
              (P.concat g x) rfl hP'path hP'first hP'fe hP'len1 hP'len hP'deg
  exact main (WList.cons v₀ f (WList.nil x₀)) hP₀path (by simp)
    ⟨WList.cons_nonempty v₀ f (WList.nil x₀), rfl⟩ (by simp) (by simp; omega) hP₀deg

/-! ## E2d-5 — chain-walk determinism -/

/-- **Chain walks from a shared incidence are prefix-comparable** (Katoh–Tanigawa 2011
Lemma 4.6, the maximal-chain uniqueness the charging count needs; ENTRY leaf E2d-5,
`notes/Phase23-design.md` §(4.107.G.5)). Two paths sharing their first vertex and first edge,
each with all interior vertices of degree `2`, are comparable under `WList.IsPrefix`: structural
induction on the pair — the shared first edge forces a shared second vertex (`IsLink` endpoint
determinism), a nil tail is a prefix outright, and two nonempty tails share *their* first edge by
the degree-`2` closure (`isLink_eq_of_degree_eq_two`) at the shared second vertex, which is
interior to both paths (non-first since the start is fresh for the tail, non-last since the
tail's start is fresh for the tail's own tail). The charging count (E2d-6) consumes this three
ways: fiber-membership (a proper prefix ends at an interior vertex of the terminated walk),
distinctness of the two charged incidences, and equal-incidence ⟹ equal-walk. -/
theorem chainWalk_isPrefix_or_isPrefix [Finite β] {G : Graph α β} [G.Loopless]
    {P₁ P₂ : WList α β} (h₁ : G.IsPath P₁) (h₂ : G.IsPath P₂)
    (hfirst : P₁.first = P₂.first)
    (hfe : ∃ (hne₁ : P₁.Nonempty) (hne₂ : P₂.Nonempty), hne₁.firstEdge = hne₂.firstEdge)
    (hdeg₁ : ∀ x ∈ P₁, x ≠ P₁.first → x ≠ P₁.last → G.degree x = 2)
    (hdeg₂ : ∀ x ∈ P₂, x ≠ P₂.first → x ≠ P₂.last → G.degree x = 2) :
    P₁.IsPrefix P₂ ∨ P₂.IsPrefix P₁ := by
  induction P₁ generalizing P₂ with
  | nil x =>
    obtain ⟨hne₁, -, -⟩ := hfe
    exact absurd hne₁ WList.nil_not_nonempty
  | cons u e W ih =>
    obtain ⟨hne₁, hne₂, hfeq⟩ := hfe
    obtain ⟨u', e', W₂, rfl⟩ := hne₂.exists_cons
    obtain rfl : u = u' := hfirst
    obtain rfl : e = e' := hfeq
    obtain ⟨hl₁, hW₁, huW₁⟩ := cons_isPath_iff.mp h₁
    obtain ⟨hl₂, hW₂, huW₂⟩ := cons_isPath_iff.mp h₂
    -- The shared first edge forces a shared second vertex (`IsLink` endpoint determinism).
    have hsecond : W.first = W₂.first := (hl₁.isLink_iff_eq.mp hl₂).symm
    cases W with
    | nil x =>
      exact Or.inl (WList.IsPrefix.cons u e _ _ (WList.nil_isPrefix_iff.mpr hsecond.symm))
    | cons a f W' =>
      cases W₂ with
      | nil y =>
        exact Or.inr (WList.IsPrefix.cons u e _ _ (WList.nil_isPrefix_iff.mpr hsecond))
      | cons b g W₂' =>
        obtain rfl : a = b := hsecond
        obtain ⟨hlf, hW₁', haW₁'⟩ := cons_isPath_iff.mp hW₁
        obtain ⟨hlg, hW₂', haW₂'⟩ := cons_isPath_iff.mp hW₂
        have hl₁' : G.IsLink e u a := hl₁
        have hl₂' : G.IsLink e u a := hl₂
        have hua : u ≠ a := fun h => huW₁ (by rw [h]; exact WList.first_mem)
        have huW' : u ∉ W' := fun h => huW₁ (by rw [WList.mem_cons_iff]; exact Or.inr h)
        have huW₂' : u ∉ W₂' := fun h => huW₂ (by rw [WList.mem_cons_iff]; exact Or.inr h)
        -- The shared second vertex is interior to `P₁`, hence has degree `2`.
        have hdega : G.degree a = 2 := by
          refine hdeg₁ a ?_ (fun h => hua (show u = a from h.symm)) ?_
          · rw [WList.mem_cons_iff]
            exact Or.inr WList.first_mem
          · intro h
            have h' : a = W'.last := h
            exact haW₁' (by rw [h']; exact WList.last_mem)
        -- The entry edge `e` differs from both tails' first edges (its far end `u` is fresh).
        have hef : e ≠ f := by
          intro h
          subst h
          rcases hl₁'.eq_and_eq_or_eq_and_eq hlf with ⟨h1, -⟩ | ⟨h1, -⟩
          · exact hua h1
          · exact huW' (by rw [h1]; exact WList.first_mem)
        have heg : e ≠ g := by
          intro h
          subst h
          rcases hl₂'.eq_and_eq_or_eq_and_eq hlg with ⟨h1, -⟩ | ⟨h1, -⟩
          · exact hua h1
          · exact huW₂' (by rw [h1]; exact WList.first_mem)
        -- The degree-`2` closure at the shared second vertex pins `g` to `f`.
        rcases isLink_eq_of_degree_eq_two hdega hef hl₁'.symm hlf g W₂'.first hlg with hge | hgf
        · exact absurd hge heg.symm
        · subst hgf
          -- Both tails share their first vertex and first edge: recurse.
          have hdeg₁' : ∀ x ∈ WList.cons a g W', x ≠ (WList.cons a g W').first →
              x ≠ (WList.cons a g W').last → G.degree x = 2 := by
            intro x hx hxf hxl
            refine hdeg₁ x ?_ ?_ hxl
            · rw [WList.mem_cons_iff]
              exact Or.inr hx
            · intro h
              rw [show x = u from h] at hx
              exact huW₁ hx
          have hdeg₂' : ∀ x ∈ WList.cons a g W₂', x ≠ (WList.cons a g W₂').first →
              x ≠ (WList.cons a g W₂').last → G.degree x = 2 := by
            intro x hx hxf hxl
            refine hdeg₂ x ?_ ?_ hxl
            · rw [WList.mem_cons_iff]
              exact Or.inr hx
            · intro h
              rw [show x = u from h] at hx
              exact huW₂ hx
          rcases ih hW₁ hW₂ rfl
              ⟨WList.cons_nonempty a g W', WList.cons_nonempty a g W₂', rfl⟩ hdeg₁' hdeg₂' with
            h | h
          · exact Or.inl (WList.IsPrefix.cons u e _ _ h)
          · exact Or.inr (WList.IsPrefix.cons u e _ _ h)

/-! ## E2d-6 — the charging bound (fiber lemma) -/

/-- **The charging count's fiber lemma** (Katoh–Tanigawa 2011 (4.6)+(4.7), the per-incidence
uniqueness the double count needs; ENTRY leaf E2d-6, `notes/Phase23-design.md` §(4.107.G.4)/(G.5)
— the sanctioned candidate split-off, taken here because the choice bookkeeping for the full
`chainWalk_charging` double count runs long on its own). A chain walk `P` sharing its start
(vertex and first edge) with a **terminated** chain walk `T` — one whose last vertex has degree
`≥ 3` — and itself ending at a degree-`2` vertex, is a *proper* prefix of `T`: its own last
vertex sits at one of `T`'s `≤ T.length − 1` interior positions (`P.length < T.length`, and
`T.get P.length = P.last` by `IsPrefix.get_eq_of_length_ge`). By chain-walk determinism (E2d-5)
the two walks are prefix-comparable; the alternative (`T.IsPrefix P`) would place `T`'s
high-degree last vertex at an interior position of `P`, forced to degree `2` by `P`'s own
chain-walk hypothesis — absurd (and the equal-length sub-case forces `P = T` outright, against
the degree mismatch). -/
theorem chainWalk_isPrefix_of_terminated [Finite β] {G : Graph α β} [G.Loopless]
    {P T : WList α β} (hP : G.IsPath P) (hT : G.IsPath T)
    (hfirst : P.first = T.first)
    (hfe : ∃ (hneP : P.Nonempty) (hneT : T.Nonempty), hneP.firstEdge = hneT.firstEdge)
    (hPdeg : ∀ x ∈ P, x ≠ P.first → x ≠ P.last → G.degree x = 2)
    (hTdeg : ∀ x ∈ T, x ≠ T.first → x ≠ T.last → G.degree x = 2)
    (hTlen1 : 1 ≤ T.length) (hTdeg3 : 3 ≤ G.degree T.last)
    (hPdeg2 : G.degree P.last = 2) :
    P.IsPrefix T ∧ P.length < T.length := by
  classical
  have hne : P ≠ T := by rintro rfl; omega
  -- `P.get` is injective on `[0, P.length]` for the `Nodup`-vertex path `P` (the E2d-1/E2d-4
  -- `hget_inj` idiom, specialized to a single path).
  have hget_inj : ∀ {i j : ℕ}, i ≤ P.length → j ≤ P.length → P.get i = P.get j → i = j := by
    intro i j hi hj hij
    have h1 := WList.idxOf_get hP.nodup hi
    have h2 := WList.idxOf_get hP.nodup hj
    rw [hij] at h1
    exact h1.symm.trans h2
  rcases chainWalk_isPrefix_or_isPrefix hP hT hfirst hfe hPdeg hTdeg with hPT | hTP
  · refine ⟨hPT, ?_⟩
    rcases hPT.length_le.lt_or_eq with hlt | heq
    · exact hlt
    · exact absurd (hPT.eq_of_length_ge heq.ge) hne
  · exfalso
    rcases hTP.length_le.lt_or_eq with hlt | heq
    · -- `T` a proper prefix of `P`: `T.last` sits at `P`'s interior position `T.length`.
      have hgetT : P.get T.length = T.last := by
        have h := hTP.get_eq_of_length_ge (le_refl T.length)
        rw [WList.get_length] at h
        exact h.symm
      have hne1 : T.last ≠ P.first := by
        intro heq'
        have heq'' : P.get T.length = P.get 0 := by rw [hgetT, heq', WList.get_zero]
        have h0 := hget_inj hlt.le (Nat.zero_le _) heq''
        omega
      have hne2 : T.last ≠ P.last := by
        intro heq'
        have heq'' : P.get T.length = P.get P.length := by
          rw [hgetT, heq', WList.get_length]
        have h1 := hget_inj hlt.le le_rfl heq''
        omega
      have hmem : T.last ∈ P := by rw [← hgetT]; exact WList.get_mem P T.length
      have hd2 := hPdeg T.last hmem hne1 hne2
      omega
    · exact hne (hTP.eq_of_length_ge heq.ge).symm

/-! ## E2d-6 — the charging bound -/

/-- **The charging count's double-count bound** (Katoh–Tanigawa 2011 (4.6)+(4.7); ENTRY leaf
E2d-6, `notes/Phase23-design.md` §(4.107.G.4)/(G.5)). Under the all-starts-terminated hypothesis
`hterm` (the assembly's `by_contra` residue — E2d-4's terminated-walk conclusion re-quantified
over *every* incidence), `2·|X₂| ≤ (n−2)·Σ_{u : 3≤deg u} deg u`: reversing the terminated walk
out of a degree-`2` vertex `v` along one of its incident edges produces a chain-walk *into* `v`
from a high-degree incidence; the fiber lemma (`chainWalk_isPrefix_of_terminated`) places `v` at
one of that incidence's own terminated walk's `≤ n−2` interior positions, and determinism
(`chainWalk_isPrefix_or_isPrefix`, via the fiber lemma applied a second time) forces the map
`(v, e) ↦ (incidence, position)` — from pairs of a degree-`2` vertex with an incident edge into
pairs of a high-degree incidence with an interior position — to be injective. The bound follows
from `Set.ncard_le_ncard_of_injOn` plus two disjoint-union cardinality identities (the domain is
`2` copies of each `v ∈ X₂`, the incidence set `I` has `Σ_{u ∈ V₊} deg u` elements). The ambient
`0`-dof / floor hypotheses (`hG0`/`hD`/`hV2`, carried for interface uniformity with the rest of the
E2d ladder) are not needed by this leaf's own argument — `hterm`, `[G.Simple]`, and finiteness
already pin down the degree-`2` extraction and the fiber lemma's hypotheses; hence the
underscore-prefixed names. -/
theorem chainWalk_charging [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} [G.Simple] (_hG0 : G.IsKDof n 0)
    (_hD : 3 ≤ bodyBarDim n) (_hV2 : 2 ≤ V(G).ncard)
    (hterm : ∀ (v₀ x₀ : α) (f : β), G.IsLink f v₀ x₀ →
      ∃ P : WList α β, G.IsPath P ∧ P.first = v₀ ∧
        (∃ hne : P.Nonempty, hne.firstEdge = f) ∧ 1 ≤ P.length ∧ P.length ≤ n - 1 ∧
        (∀ x ∈ P, x ≠ P.first → x ≠ P.last → G.degree x = 2) ∧ 3 ≤ G.degree P.last) :
    2 * {v ∈ V(G) | G.degree v = 2}.ncard
      ≤ (n - 2) * ∑ᶠ u ∈ {u ∈ V(G) | 3 ≤ G.degree u}, G.degree u := by
  classical
  -- Turn `hterm` into a genuine (classical) choice function `Tfun`, naming each conjunct
  -- (`choose` leaves the `Prop`-witnessed inner existential `hTfe` bundled; a second `choose`
  -- splits it into the nonempty-witness function `hTne` and its firstEdge spec `hTfeEq`).
  choose Tfun hTpath hTfirst hTfe hTlen1 hTlen hTdeg hTdeg3 using hterm
  choose hTne hTfeEq using hTfe
  -- Reversing `Tfun a x f h` exposes the high-degree incidence a chain-walk into `a` starts
  -- from: destructure the reversal's `cons`-head.
  have hstep2 : ∀ (a x : α) (f : β) (h : G.IsLink f a x),
      ∃ (u : α) (e' : β) (R' : WList α β), (Tfun a x f h).reverse = WList.cons u e' R' :=
    fun a x f h => (hTne a x f h).reverse.exists_cons
  choose destU destE destR hdestEq using hstep2
  have hUeq : ∀ (a x : α) (f : β) (h : G.IsLink f a x),
      destU a x f h = (Tfun a x f h).last := by
    intro a x f h
    have h2 : (Tfun a x f h).reverse.first = (Tfun a x f h).last := WList.reverse_first
    rw [hdestEq a x f h] at h2
    simpa using h2
  have hlinkR : ∀ (a x : α) (f : β) (h : G.IsLink f a x),
      G.IsLink (destE a x f h) (destU a x f h) (destR a x f h).first := by
    intro a x f h
    have hp : G.IsPath (WList.cons (destU a x f h) (destE a x f h) (destR a x f h)) := by
      rw [← hdestEq a x f h]; exact (hTpath a x f h).reverse
    exact (cons_isPath_iff.mp hp).1
  have hUdeg3 : ∀ (a x : α) (f : β) (h : G.IsLink f a x), 3 ≤ G.degree (destU a x f h) := by
    intro a x f h; rw [hUeq a x f h]; exact hTdeg3 a x f h
  have hRevFirstEdge : ∀ (a x : α) (f : β) (h : G.IsLink f a x),
      ((hTne a x f h).reverse).firstEdge = destE a x f h := by
    intro a x f h; simp only [hdestEq a x f h, WList.Nonempty.firstEdge_cons]
  -- Two congruence facts: `Tfun`/`Nonempty.firstEdge` depend only on the walk they name (up to
  -- the standard endpoint-determinism of `IsLink`/proof irrelevance), regardless of the route
  -- used to derive the witnessing data.
  have hTfun_congr : ∀ (q q' w w' : α) (f f' : β) (hqq' : q = q') (hff' : f = f')
      (h1 : G.IsLink f q w) (h2 : G.IsLink f' q' w'), Tfun q w f h1 = Tfun q' w' f' h2 := by
    intro q q' w w' f f' hqq' hff' h1 h2
    subst hqq'; subst hff'
    obtain rfl : w' = w := h1.isLink_iff_eq.mp h2
    rfl
  have hfirstEdge_congr : ∀ {W1 W2 : WList α β} (heq : W1 = W2) (hw1 : W1.Nonempty)
      (hw2 : W2.Nonempty), hw1.firstEdge = hw2.firstEdge := by
    intro W1 W2 heq hw1 hw2; subst heq; rfl
  set X₂ : Set α := {v ∈ V(G) | G.degree v = 2} with hX₂def
  set Vge3 : Set α := {u ∈ V(G) | 3 ≤ G.degree u} with hVge3def
  set Dom : Set (α × β) := {p | p.1 ∈ X₂ ∧ G.Inc p.2 p.1} with hDomDef
  set I : Set (β × α) := ⋃ u ∈ Vge3, E(G, u) ×ˢ ({u} : Set α) with hIDef
  set Tgt : Set ((β × α) × ℕ) := I ×ˢ Set.Ico 1 (n - 1) with hTgtDef
  -- (A) `|Dom| = 2·|X₂|`: `Dom` is the disjoint (over `v`) union of one copy of `E(G,v)` per `v`.
  have hDomCard : Dom.ncard = 2 * X₂.ncard := by
    have hUnion : Dom = ⋃ v ∈ X₂, ({v} : Set α) ×ˢ E(G, v) := by
      ext ⟨v, e⟩
      simp only [hDomDef, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff,
        mem_incEdges_iff]
      constructor
      · rintro ⟨hv, he⟩; exact ⟨v, hv, rfl, he⟩
      · rintro ⟨i, hi, rfl, he⟩; exact ⟨hi, he⟩
    rw [hUnion, (Set.toFinite X₂).ncard_biUnion (fun v _ => Set.toFinite _)
      (fun v _ v' _ hvv' => Set.disjoint_left.mpr (by
        rintro ⟨a, b⟩ hmem hmem'
        rw [Set.mem_prod, Set.mem_singleton_iff] at hmem hmem'
        exact hvv' (hmem.1.symm.trans hmem'.1)))]
    have hpiece : ∀ v ∈ X₂, (({v} : Set α) ×ˢ E(G, v)).ncard = 2 := by
      intro v hv
      rw [Set.ncard_prod, Set.ncard_singleton, one_mul, ← degree_eq_ncard_inc]
      exact hv.2
    rw [finsum_mem_congr rfl hpiece, finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite X₂),
      Finset.sum_const, smul_eq_mul, ← Set.ncard_eq_toFinset_card]
    ring
  -- (B) `|I| = Σ_{u ∈ V₊} deg u`: `I` is the disjoint (over `u`) union of `E(G,u)`-copies.
  have hICard : I.ncard = ∑ᶠ u ∈ Vge3, G.degree u := by
    rw [hIDef, (Set.toFinite Vge3).ncard_biUnion (fun u _ => Set.toFinite _)
      (fun u _ u' _ huu' => Set.disjoint_left.mpr (by
        rintro ⟨a, b⟩ hmem hmem'
        rw [Set.mem_prod, Set.mem_singleton_iff] at hmem hmem'
        exact huu' (hmem.2.symm.trans hmem'.2)))]
    refine finsum_mem_congr rfl fun u _ => ?_
    rw [Set.ncard_prod, Set.ncard_singleton, mul_one, ← degree_eq_ncard_inc]
  -- The shared fiber-lemma application: reversing the terminated walk out of `(v, x, e)` is a
  -- proper prefix of the terminated walk out of the high-degree incidence it lands at.
  have hfiberFact : ∀ (v x : α) (e : β) (hvX₂ : v ∈ X₂) (hlink : G.IsLink e v x),
      ((Tfun v x e hlink).reverse).IsPrefix
          (Tfun (destU v x e hlink) (destR v x e hlink).first (destE v x e hlink)
            (hlinkR v x e hlink)) ∧
        ((Tfun v x e hlink).reverse).length <
          (Tfun (destU v x e hlink) (destR v x e hlink).first (destE v x e hlink)
            (hlinkR v x e hlink)).length := by
    intro v x e hvX₂ hlink
    have hRevFirst : (Tfun v x e hlink).reverse.first = destU v x e hlink := by
      rw [WList.reverse_first, hUeq v x e hlink]
    have hRevLast : (Tfun v x e hlink).reverse.last = v := by
      rw [WList.reverse_last]; exact hTfirst v x e hlink
    have hRevDeg : ∀ y ∈ (Tfun v x e hlink).reverse,
        y ≠ (Tfun v x e hlink).reverse.first → y ≠ (Tfun v x e hlink).reverse.last →
        G.degree y = 2 := by
      intro y hy hyfirst hylast
      rw [WList.mem_reverse] at hy
      rw [hRevFirst] at hyfirst
      rw [hRevLast] at hylast
      refine hTdeg v x e hlink y hy ?_ ?_
      · rw [hTfirst v x e hlink]; exact hylast
      · rw [hUeq v x e hlink] at hyfirst; exact hyfirst
    exact chainWalk_isPrefix_of_terminated (hTpath v x e hlink).reverse
      (hTpath (destU v x e hlink) (destR v x e hlink).first (destE v x e hlink)
        (hlinkR v x e hlink))
      (by
        rw [hRevFirst,
          hTfirst (destU v x e hlink) (destR v x e hlink).first (destE v x e hlink)
            (hlinkR v x e hlink)])
      ⟨(hTne v x e hlink).reverse,
        hTne (destU v x e hlink) (destR v x e hlink).first (destE v x e hlink)
          (hlinkR v x e hlink),
        by
          rw [hRevFirstEdge,
            hTfeEq (destU v x e hlink) (destR v x e hlink).first (destE v x e hlink)
              (hlinkR v x e hlink)]⟩
      hRevDeg
      (hTdeg (destU v x e hlink) (destR v x e hlink).first (destE v x e hlink)
        (hlinkR v x e hlink))
      (hTlen1 (destU v x e hlink) (destR v x e hlink).first (destE v x e hlink)
        (hlinkR v x e hlink))
      (hTdeg3 (destU v x e hlink) (destR v x e hlink).first (destE v x e hlink)
        (hlinkR v x e hlink))
      (by rw [hRevLast]; exact hvX₂.2)
  -- The charging map: a degree-`2` vertex `v` with an incident edge `e` charges the high-degree
  -- incidence reached by reversing the terminated walk out of `(v, e)`, at the length of that
  -- reversed walk (an interior position of the target incidence's own terminated walk).
  set Φ : α × β → (β × α) × ℕ := fun p =>
    if h : p.1 ∈ X₂ ∧ G.Inc p.2 p.1 then
      ((destE p.1 h.2.other p.2 h.2.isLink_other, destU p.1 h.2.other p.2 h.2.isLink_other),
        (Tfun p.1 h.2.other p.2 h.2.isLink_other).length)
    else ((p.2, p.1), 0) with hΦdef
  have hΦeval : ∀ (v : α) (e : β) (hvX₂ : v ∈ X₂) (hincv : G.Inc e v),
      Φ (v, e) = ((destE v hincv.other e hincv.isLink_other,
          destU v hincv.other e hincv.isLink_other),
        (Tfun v hincv.other e hincv.isLink_other).length) :=
    fun v e hvX₂ hincv => dif_pos ⟨hvX₂, hincv⟩
  have hMapsTo : ∀ p ∈ Dom, Φ p ∈ Tgt := by
    rintro ⟨v, e⟩ ⟨hvX₂, hincv⟩
    rw [hΦeval v e hvX₂ hincv, hTgtDef, Set.mem_prod]
    set x := hincv.other with hxdef
    set hlink : G.IsLink e v x := hincv.isLink_other with hlinkdef
    change (destE v x e hlink, destU v x e hlink) ∈ I ∧
      (Tfun v x e hlink).length ∈ Set.Ico 1 (n - 1)
    have hp := hfiberFact v x e hvX₂ hlink
    have hSlen := hTlen (destU v x e hlink) (destR v x e hlink).first (destE v x e hlink)
      (hlinkR v x e hlink)
    have hrevlen : (Tfun v x e hlink).reverse.length = (Tfun v x e hlink).length :=
      WList.reverse_length
    refine ⟨?_, Set.mem_Ico.mpr ⟨hTlen1 v x e hlink, by omega⟩⟩
    rw [hIDef]
    exact Set.mem_biUnion ⟨(hlinkR v x e hlink).left_mem, hUdeg3 v x e hlink⟩
      ⟨(hlinkR v x e hlink).inc_left, rfl⟩
  have hInjOn : Set.InjOn Φ Dom := by
    rintro ⟨v, e⟩ ⟨hvX₂, hincv⟩ ⟨v', e'⟩ ⟨hv'X₂, hincv'⟩ hΦeq
    rw [hΦeval v e hvX₂ hincv, hΦeval v' e' hv'X₂ hincv'] at hΦeq
    set x := hincv.other with hxdef
    set hlink : G.IsLink e v x := hincv.isLink_other with hlinkdef
    set x' := hincv'.other with hx'def
    set hlink' : G.IsLink e' v' x' := hincv'.isLink_other with hlink'def
    injection hΦeq with hfst hk
    injection hfst with hêeq hqeq
    have hSeq : Tfun (destU v x e hlink) (destR v x e hlink).first (destE v x e hlink)
          (hlinkR v x e hlink) =
        Tfun (destU v' x' e' hlink') (destR v' x' e' hlink').first (destE v' x' e' hlink')
          (hlinkR v' x' e' hlink') :=
      hTfun_congr _ _ _ _ _ _ hqeq hêeq (hlinkR v x e hlink) (hlinkR v' x' e' hlink')
    have hp1 := hfiberFact v x e hvX₂ hlink
    have hp2 := hfiberFact v' x' e' hv'X₂ hlink'
    rw [← hSeq] at hp2
    have hlenEq : (Tfun v x e hlink).reverse.length = (Tfun v' x' e' hlink').reverse.length := by
      rw [WList.reverse_length, WList.reverse_length, hk]
    have hPrevEq : (Tfun v x e hlink).reverse = (Tfun v' x' e' hlink').reverse := by
      rw [← hp1.1.take_eq, ← hp2.1.take_eq, hlenEq]
    have hTeq : Tfun v x e hlink = Tfun v' x' e' hlink' := by
      have h5 := congrArg WList.reverse hPrevEq
      rwa [WList.reverse_reverse, WList.reverse_reverse] at h5
    have hveq : v = v' := by
      have h3 := congrArg WList.first hTeq
      rwa [hTfirst v x e hlink, hTfirst v' x' e' hlink'] at h3
    have heeq : e = e' := by
      have h4 := hfirstEdge_congr hTeq (hTne v x e hlink) (hTne v' x' e' hlink')
      rwa [hTfeEq v x e hlink, hTfeEq v' x' e' hlink'] at h4
    rw [hveq, heeq]
  have hbound := Set.ncard_le_ncard_of_injOn Φ hMapsTo hInjOn
  rw [hDomCard, hTgtDef, Set.ncard_prod, Set.ncard_Ico_nat, hICard] at hbound
  have hn2 : (n - 1) - 1 = n - 2 := by omega
  rw [hn2] at hbound
  calc 2 * X₂.ncard ≤ (∑ᶠ u ∈ Vge3, G.degree u) * (n - 2) := hbound
    _ = (n - 2) * ∑ᶠ u ∈ Vge3, G.degree u := mul_comm _ _

/-! ## E2d-7 — the arithmetic close -/

/-- **The KT (4.8)/(4.9) arithmetic close** (Katoh–Tanigawa 2011 Lemma 4.6, the final
contradiction; ENTRY leaf E2d-7, `notes/Phase23-design.md` §(4.107.G.4)/(G.5)). Under the
all-starts-terminated hypothesis `hterm` (the E2-assembly's `by_contra` residue — E2d-4's
terminated-walk conclusion re-quantified over *every* incidence), the charging bound (E2d-6,
`chainWalk_charging`) and the numeric linking fact (E2e, `kt_lemma_46_linking`), summed over
`V₊ := {u ∈ V(G) | 3 ≤ deg u}`, force `D·|V(G)| ≤ (D−1)·|E(G)|` — directly contradicting the KT
4.5(i) edge bound `no_rigid_edge_count` at `k = 0`.

The chain (`notes/Phase23-design.md` §(4.107.G.4)): `kt_lemma_46_linking` summed pointwise over
`V₊`, reshaped to avoid a per-term `ℕ`-subtraction (`i(n−2)+2 ≤ (D−1)(i−2)` plus `(D−1)·2` on
both sides collapses the right-hand subtraction: `i(n−2) + 2D ≤ (D−1)i`), combines with the
charging bound (`2|X₂| ≤ (n−2)Σ_{V₊}deg`) to give `(D−1)·Σ_{V₊}deg ≥ 2|X₂| + 2D|V₊|`;
substituting the multigraph handshake (`Graph.handshake_degree_subtype`, vendored) split across
the min-degree-`2` partition `V(G) = X₂ ⊔ V₊` (E2a) — `Σ_{V₊}deg = 2|E| − 2|X₂|` — turns this
into `D·|V(G)| ≤ (D−1)·|E(G)|` after multiplying out and using `|V(G)| = |X₂| + |V₊|`. The
`V₊ = ∅` corner needs no separate case: the chain above degenerates gracefully (`Σ_{V₊}deg = 0`),
still yielding the same bound once combined with the handshake identity. -/
theorem chainWalk_terminated_contradiction [DecidableEq β] [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ}
    (hD : 3 ≤ bodyBarDim n) (hV3 : 3 ≤ V(G).ncard) (hG : G.IsMinimalKDof n 0)
    (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n)
    (hterm : ∀ (v₀ x₀ : α) (f : β), G.IsLink f v₀ x₀ →
      ∃ P : WList α β, G.IsPath P ∧ P.first = v₀ ∧
        (∃ hne : P.Nonempty, hne.firstEdge = f) ∧ 1 ≤ P.length ∧ P.length ≤ n - 1 ∧
        (∀ x ∈ P, x ≠ P.first → x ≠ P.last → G.degree x = 2) ∧ 3 ≤ G.degree P.last) :
    False := by
  classical
  have hD2 : 2 ≤ bodyBarDim n := by omega
  have hD1 : 1 ≤ bodyBarDim n := by omega
  have hVne : V(G).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  have hV2 : 2 ≤ V(G).ncard := by omega
  haveI hsimp : G.Simple := simple_of_isMinimalKDof_of_noRigid hD2 hV3 hG hnp
  haveI hloop : G.Loopless := loopless_of_isMinimalKDof hG
  haveI hGfin : G.Finite := { edgeSet_finite := Set.toFinite _, vertexSet_finite := Set.toFinite _ }
  -- The charging bound (E2d-6), folded against the min-degree-`2` partition `V(G) = X₂ ⊔ V₊`
  -- (E2a) once named — `set` retroactively folds `hcharge`'s literal set-builders.
  have hcharge := chainWalk_charging hG.1 hD hV2 hterm
  set X₂ : Set α := {v ∈ V(G) | G.degree v = 2} with hX₂def
  set Vge3 : Set α := {u ∈ V(G) | 3 ≤ G.degree u} with hVge3def
  have hpart : V(G) = X₂ ∪ Vge3 := by
    ext v
    simp only [hX₂def, hVge3def, Set.mem_union, Set.mem_setOf_eq]
    constructor
    · intro hv
      have h2 := two_le_degree_of_isKDof_zero hD1 hG.1 hv hV2
      rcases Nat.lt_or_ge (G.degree v) 3 with h | h
      · exact Or.inl ⟨hv, by omega⟩
      · exact Or.inr ⟨hv, h⟩
    · rintro (⟨hv, -⟩ | ⟨hv, -⟩) <;> exact hv
  have hdisj : Disjoint X₂ Vge3 := by
    rw [Set.disjoint_left]
    rintro v ⟨-, hv2⟩ ⟨-, hv3⟩
    omega
  have hVcard : V(G).ncard = X₂.ncard + Vge3.ncard := by
    rw [hpart]; exact Set.ncard_union_eq hdisj
  -- The handshake, split across the partition: `2|E| = 2|X₂| + Σ_{V₊} deg`.
  have hHS : 2 * E(G).ncard = 2 * X₂.ncard + ∑ᶠ u ∈ Vge3, G.degree u := by
    have hhand := handshake_degree_subtype G
    rw [hpart, finsum_mem_union hdisj (Set.toFinite X₂) (Set.toFinite Vge3)] at hhand
    have hX₂sum : ∑ᶠ v ∈ X₂, G.degree v = 2 * X₂.ncard := by
      have hpiece : ∀ v ∈ X₂, G.degree v = 2 := fun v hv => hv.2
      rw [finsum_mem_congr rfl hpiece, finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite X₂),
        Finset.sum_const, smul_eq_mul, ← Set.ncard_eq_toFinset_card]
      ring
    rw [hX₂sum] at hhand
    omega
  -- E2e summed pointwise over `V₊`, reshaped to avoid the per-term subtraction: adding `2(D−1)`
  -- to both sides of `kt_lemma_46_linking` collapses `(D−1)(i−2) + 2(D−1) = (D−1)i` and
  -- `2 + 2(D−1) = 2D`.
  set sVge3 := (Set.toFinite Vge3).toFinset with hsVge3
  have hlinkAlt : ∀ u ∈ sVge3, G.degree u * (n - 2) + 2 * bodyBarDim n ≤
      (bodyBarDim n - 1) * G.degree u := by
    intro u hu
    have hu3 : 3 ≤ G.degree u := ((Set.toFinite Vge3).mem_toFinset.mp hu).2
    have hlink := kt_lemma_46_linking hD hu3
    have hexp : (bodyBarDim n - 1) * (G.degree u - 2) + (bodyBarDim n - 1) * 2
        = (bodyBarDim n - 1) * G.degree u := by
      rw [← Nat.mul_add, Nat.sub_add_cancel (show 2 ≤ G.degree u by omega)]
    omega
  have hsum_link := Finset.sum_le_sum hlinkAlt
  have hsum_link' : (n - 2) * (∑ u ∈ sVge3, G.degree u) + 2 * bodyBarDim n * sVge3.card ≤
      (bodyBarDim n - 1) * ∑ u ∈ sVge3, G.degree u := by
    have e1 : ∑ u ∈ sVge3, (G.degree u * (n - 2) + 2 * bodyBarDim n)
        = (n - 2) * (∑ u ∈ sVge3, G.degree u) + 2 * bodyBarDim n * sVge3.card := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, smul_eq_mul]
      ring
    have e2 : ∑ u ∈ sVge3, (bodyBarDim n - 1) * G.degree u
        = (bodyBarDim n - 1) * ∑ u ∈ sVge3, G.degree u := (Finset.mul_sum _ _ _).symm
    rwa [e1, e2] at hsum_link
  have hSfin_eq : ∑ᶠ u ∈ Vge3, G.degree u = ∑ u ∈ sVge3, G.degree u :=
    finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite Vge3)
  have hVge3card : Vge3.ncard = sVge3.card := Set.ncard_eq_toFinset_card Vge3 (Set.toFinite Vge3)
  -- Fold `hcharge`/`hHS`'s `finsum` into the same `Finset.sum` `hsum_link'` is already stated
  -- over — avoids `zify` mis-normalizing a `finsum`-of-`finsum` cast (the `∑ᶠ u ∈ s, f u`
  -- notation's own definitional unfolding).
  rw [hSfin_eq] at hcharge hHS
  rw [← hVge3card] at hsum_link'
  -- Cast to `ℤ` for the final combination (KT (4.8)/(4.9)'s numeric close).
  have hn2 : 2 ≤ n := by
    have hbb : 2 * bodyBarDim n = n * (n + 1) := by
      rw [bodyBarDim, Nat.mul_div_cancel' (Nat.even_mul_succ_self n).two_dvd]
    by_contra h
    have h' : n < 2 := by omega
    interval_cases n <;> omega
  have hedge := no_rigid_edge_count hD2 hVne hG hnp
  have hHM : (bodyHingeMult n : ℤ) = (bodyBarDim n : ℤ) - 1 := by rw [bodyHingeMult]; omega
  zify [hn2, hD1] at hcharge hsum_link'
  zify at hHS hVcard
  rw [hHM] at hedge
  have hSfin_val : (∑ u ∈ sVge3, (G.degree u : ℤ)) =
      2 * (E(G).ncard : ℤ) - 2 * (X₂.ncard : ℤ) := by linarith [hHS]
  rw [hSfin_val] at hcharge hsum_link'
  have hDVc : (bodyBarDim n : ℤ) * (V(G).ncard : ℤ)
      = (bodyBarDim n : ℤ) * (X₂.ncard : ℤ) + (bodyBarDim n : ℤ) * (Vge3.ncard : ℤ) := by
    rw [hVcard]; ring
  have hVpos : 1 ≤ V(G).ncard := hVne.ncard_pos
  nlinarith [hcharge, hsum_link', hDVc, hedge, hVpos]

/-! ## E2-assembly — closing the ENTRY leaf E2 -/

/-- **Katoh–Tanigawa 2011 Lemma 4.6**, the ENTRY leaf **E2** (`notes/Phase23-design.md`
§(4.107.D)'s pinned public signature): a minimal `0`-dof graph on `≥ 3` vertices with no proper
rigid subgraph either packages a length-`n` chain (`Graph.ChainData n`) or a spanning-or-smaller
cycle (`Graph.CycleData` with `cy.m ≤ n`). `by_contra` refutes the goal, pushing the negation into
the capped trichotomy builder (E2d-4, `chainWalk_trichotomy`) at *every* incidence: its left
(chain-or-cycle) arm is exactly the negated goal, so only its right (terminated-walk) arm survives,
supplying the all-starts-terminated hypothesis `hterm` the arithmetic close (E2d-7,
`chainWalk_terminated_contradiction`) needs to derive `False`. E2d-1…E2d-3/E2e/E2d-5/E2d-6 enter
only through E2d-4/E2d-7's own hypotheses; **E2b is not consumed** (§(4.107.G.7)(i)) — the capped
builder starts from an arbitrary incidence rather than a degree-`2` vertex, so the assembly never
needs E2b's standalone existence witness. -/
theorem chainData_or_cycleData_of_noRigid [DecidableEq β] [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ}
    (hD : 3 ≤ bodyBarDim n) (hV3 : 3 ≤ V(G).ncard)
    (hG : G.IsMinimalKDof n 0)
    (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n)
    (hfresh : ∃ e₀ : β, e₀ ∉ E(G)) :
    Nonempty (G.ChainData n) ∨ ∃ cy : G.CycleData, cy.m ≤ n := by
  by_contra hcon
  have hterm : ∀ (v₀ x₀ : α) (f : β), G.IsLink f v₀ x₀ →
      ∃ P : WList α β, G.IsPath P ∧ P.first = v₀ ∧
        (∃ hne : P.Nonempty, hne.firstEdge = f) ∧ 1 ≤ P.length ∧ P.length ≤ n - 1 ∧
        (∀ x ∈ P, x ≠ P.first → x ≠ P.last → G.degree x = 2) ∧ 3 ≤ G.degree P.last := by
    intro v₀ x₀ f hf
    rcases chainWalk_trichotomy hD hV3 hG hnp hfresh hf with h | h
    · exact absurd h hcon
    · exact h
  exact chainWalk_terminated_contradiction hD hV3 hG hnp hterm

/-! ## E3 — the general extractor -/

/-- **The general chain/cycle extractor** (Katoh–Tanigawa 2011 Lemma 4.6 + Lemma 4.8(i)/(ii),
ENTRY leaf **E3**, `notes/Phase23-design.md` §(4.107.D)'s pinned public signature): composes
**E2** (`chainData_or_cycleData_of_noRigid`) with the landed Lemma-4.8 stack at the interior
chain vertex `v₁ = cd.vtx ⟨1, _⟩` — `splitOff_isMinimalKDof` (KT 4.8(i)),
`splitOff_simple_of_noRigid_of_card` (KT 6.7(ii)), and the two measure facts (`2 ≤ |V'|`,
`|V'| < |V|`) — to discharge the ENTRY interface `hextract` at general `n`: either a length-`n`
chain whose `v₁`-split is again a smaller minimal `0`-dof-graph, or a cycle on `≤ n` vertices
(forwarded unchanged from E2's right disjunct, feeding `hcycle`/E5). Composition only, no new
combinatorics — mirrors the `d = 3` discharge `chainData_extract_d3`'s split-fact list verbatim.
Below-contract file home (§(4.107.G.2)): `ChainExtraction.lean`, not §(4.107.D)'s literal
`Reduction.lean` pin — `Reduction.lean` already carries the E2d ladder + E2-assembly for the same
LoC-tripwire reason, and E3 is E2's sole consumer.

Chain disjunct: with `i := ⟨1, by omega⟩ : Fin cd.d` (needs `cd.d ≥ 2`, from `cd.d_eq : cd.d = n`
against the `n ≥ 2` floor `hD` forces via `2·bodyBarDim n = n(n+1)`), the predecessor/successor
chain edges out of `v₁ = cd.vtx i.castSucc` are already oriented and closed exactly as the pin's
literal `(cd.vtx ⟨1,_⟩) (cd.vtx ⟨0,_⟩) (cd.vtx ⟨2,_⟩)` slots need — the primitive fields
`deg_two`/`isLink_pred_edge`/`isLink_succ_edge`/`pred_edge_ne` read at `i` give the `(a, b) =
(vtx 0, vtx 2)` order directly (predecessor first, successor second), with no `splitOff_swap_ab`
reconciliation needed (contrast the `d = 3` adapter, whose fixed `vtx = ![b, v, a, c]` labeling
runs the other way). -/
theorem chainData_extract [DecidableEq β] [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} (hD : 6 ≤ bodyBarDim n) (hV3 : 3 ≤ V(G).ncard)
    (hG : G.IsMinimalKDof n 0) [G.Simple]
    (hfresh : ∀ G' : Graph α β, ∃ e₀ : β, e₀ ∉ E(G'))
    (hV4 : 4 ≤ V(G).ncard) (hnoRigid : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) :
    (∃ (cd : G.ChainData n) (hd2 : 2 ≤ cd.d),
      (G.splitOff (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨0, by omega⟩)
        (cd.vtx ⟨2, by omega⟩) cd.e₀).IsMinimalKDof n 0 ∧
      (G.splitOff (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨0, by omega⟩)
        (cd.vtx ⟨2, by omega⟩) cd.e₀).Simple ∧
      2 ≤ V(G.splitOff (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨0, by omega⟩)
        (cd.vtx ⟨2, by omega⟩) cd.e₀).ncard ∧
      V(G.splitOff (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨0, by omega⟩)
        (cd.vtx ⟨2, by omega⟩) cd.e₀).ncard < V(G).ncard) ∨
    ∃ cy : G.CycleData, cy.m ≤ n := by
  classical
  have hD3 : 3 ≤ bodyBarDim n := by omega
  have hD2 : 2 ≤ bodyBarDim n := by omega
  obtain ⟨e₀, he₀⟩ := hfresh G
  rcases chainData_or_cycleData_of_noRigid hD3 hV3 hG hnoRigid ⟨e₀, he₀⟩ with hchain | ⟨cy, hcym⟩
  · obtain ⟨cd⟩ := hchain
    left
    have hbb : 2 * bodyBarDim n = n * (n + 1) := by
      rw [bodyBarDim, Nat.mul_div_cancel' (Nat.even_mul_succ_self n).two_dvd]
    have hn2 : 2 ≤ n := by
      by_contra h
      have h' : n < 2 := by omega
      interval_cases n <;> omega
    have hd2 : 2 ≤ cd.d := by have := cd.d_eq; omega
    have hi : 0 < ((⟨1, by omega⟩ : Fin cd.d) : ℕ) := by simp
    have hav : cd.vtx (⟨0, by omega⟩ : Fin (cd.d + 1)) ≠ cd.vtx (⟨1, by omega⟩ : Fin (cd.d + 1)) :=
      (cd.castSucc_ne_pred_castSucc (i := ⟨1, by omega⟩) hi).symm
    have hbv : cd.vtx (⟨2, by omega⟩ : Fin (cd.d + 1)) ≠ cd.vtx (⟨1, by omega⟩ : Fin (cd.d + 1)) :=
      (cd.castSucc_ne_succ (⟨1, by omega⟩ : Fin cd.d)).symm
    have hvG : cd.vtx (⟨1, by omega⟩ : Fin (cd.d + 1)) ∈ V(G) := cd.vtx_mem _
    have haG : cd.vtx (⟨0, by omega⟩ : Fin (cd.d + 1)) ∈ V(G) := cd.vtx_mem _
    have hbG : cd.vtx (⟨2, by omega⟩ : Fin (cd.d + 1)) ∈ V(G) := cd.vtx_mem _
    have heab : cd.edge (⟨0, by omega⟩ : Fin cd.d) ≠ cd.edge (⟨1, by omega⟩ : Fin cd.d) :=
      cd.pred_edge_ne (i := ⟨1, by omega⟩) hi
    have hlea : G.IsLink (cd.edge (⟨0, by omega⟩ : Fin cd.d))
        (cd.vtx (⟨1, by omega⟩ : Fin (cd.d + 1))) (cd.vtx (⟨0, by omega⟩ : Fin (cd.d + 1))) :=
      cd.isLink_pred_edge (i := ⟨1, by omega⟩) hi
    have hleb : G.IsLink (cd.edge (⟨1, by omega⟩ : Fin cd.d))
        (cd.vtx (⟨1, by omega⟩ : Fin (cd.d + 1))) (cd.vtx (⟨2, by omega⟩ : Fin (cd.d + 1))) :=
      cd.isLink_succ_edge (⟨1, by omega⟩ : Fin cd.d)
    have hclv : ∀ e x, G.IsLink e (cd.vtx (⟨1, by omega⟩ : Fin (cd.d + 1))) x →
        e = cd.edge (⟨0, by omega⟩ : Fin cd.d) ∨ e = cd.edge (⟨1, by omega⟩ : Fin cd.d) :=
      cd.deg_two (⟨1, by omega⟩ : Fin cd.d) hi
    have he₀' : cd.e₀ ∉ E(G) := cd.e₀_fresh
    refine ⟨cd, hd2, ?_, ?_, ?_, ?_⟩
    · exact splitOff_isMinimalKDof hD2 hV3 hav hbv haG hbG hvG heab hlea hleb hclv he₀' hG hnoRigid
    · exact splitOff_simple_of_noRigid_of_card hD3 heab hlea hleb hV4 hnoRigid
    · rw [vertexSet_splitOff, Set.ncard_diff (by simpa using hvG) (Set.toFinite _),
        Set.ncard_singleton]
      omega
    · exact splitOff_vertexSet_ncard_lt hvG
  · exact Or.inr ⟨cy, hcym⟩

end Graph
