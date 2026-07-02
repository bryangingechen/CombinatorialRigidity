/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Induction.ForestSurgery.Reduction

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

end Graph
