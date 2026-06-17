/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Induction.Contraction

/-!
# The combinatorial induction — edge-splitting and acyclicity transport (KT Lemma 4.2)

Phase 20 (molecular-conjecture program; see `notes/MolecularConjecture.md`). The KT-Lemma-4.2 half
of the `Induction/` capstone (the `ForestSurgery/` subdirectory; split in the post-Phase-22l
molecular split round, `notes/Phase22l-perf.md`). On top of the contraction-minimality bridge
(`Induction/Contraction`), this file builds the acyclicity machinery the forest-surgery reduction
rests on:

* the **acyclicity transport** across the degree-2 short-circuit, the fiber-degree substrate, and
  the degree-2 reroute (forward and reverse) (`lem:forest-surgery-split`, surgery crux);
* the **edge-splitting extension** (`lem:edge-splitting`, Katoh–Tanigawa 2011 §3.4 Lemma 4.2).

The reduction + forest-surgery count + Theorem 4.9 built on top live in `ForestSurgery/Reduction`.
See `ROADMAP.md` §20 / `notes/Phase20.md` and the `sec:molecular-induction` dep-graph.
-/

namespace Graph

open Set Matroid

variable {α β : Type*}

/-! ## Acyclicity transport across the short-circuit (`lem:forest-surgery-split`, surgery crux)

The genuine combinatorial crux of the Katoh–Tanigawa 2011 Lemma 4.1 forest surgery: the
reroute of the `D` forests across the degree-2 vertex `v` must **preserve acyclicity** —
each rerouted forest of the splitting-off `G_v^{ab}` is still a forest. The fibers of the
multiplied splitting-off `G̃_v^{ab}` split into the *fresh* short-circuit fiber `ã̃b =
edgeFiber e₀ n` (the `D-1` parallel copies of the new edge `e₀`) and the *surviving* fibers
(`p.1 ≠ e₀`), which are exactly the fibers of `G̃` whose underlying `G`-edge avoids `v`.

The surviving part transports cleanly: deleting the fresh fiber from `G̃_v^{ab}` gives a
subgraph of `G̃` (`mulTilde_splitOff_deleteFiber_le`), because every non-`e₀` link of the
splitting-off is a link of `G` (it keeps `G`'s `e ≠ e₀` links avoiding `v`). So a
cycle-matroid-acyclic fiber set of `G̃_v^{ab}` that avoids `ã̃b` is acyclic in `G̃`
(`isAcyclicSet_mulTilde_of_splitOff_of_disjoint`) — the half of the surgery's
acyclicity-preservation that needs no rerouting (the forests with `dᶠ(v) ≤ 1`, which drop
their `v`-edge rather than swap onto `ã̃b`). The rerouting half (`dᶠ(v) = 2` forests
swapping their two `v`-edges for one `ã̃b` copy, with the `v`-traversing path lift) is landed
as `isAcyclicSet_splitOff_reroute` below; what remains of the still-red
`lem:forest-surgery-split` is only the per-`D`-forest bookkeeping assembly. -/

/-- **Deleting the fresh fiber from the multiplied splitting-off lands inside `G̃`**
(`lem:forest-surgery-split`, surgery crux). The multiplied splitting-off `G̃_v^{ab}` with
its fresh short-circuit fiber `ã̃b = edgeFiber e₀ n` deleted is a subgraph of the multiplied
original `G̃ = (D-1)·G`. Every surviving fiber `p` (`p.1 ≠ e₀`) of `G̃_v^{ab}` is a copy of
an `e₀`-distinct edge of `G` avoiding `v`, so it carries exactly the same link in `G̃` — the
splitting-off only *adds* the fresh `e₀`-fiber and *removes* the `v`-incident fibers, both of
which lie outside the deleted-fiber subgraph. This is the structural fact the acyclicity
transport `isAcyclicSet_mulTilde_of_splitOff_of_disjoint` runs on. -/
lemma mulTilde_splitOff_deleteFiber_le {G : Graph α β} {v a b : α} {e₀ : β} (n : ℕ) :
    ((G.splitOff v a b e₀).mulTilde n).deleteEdges (edgeFiber e₀ n) ≤ G.mulTilde n := by
  refine ⟨?_, ?_⟩
  · -- Vertex sets: `V(G̃_v^{ab}) = V(G) \ {v} ⊆ V(G) = V(G̃)`.
    intro x hx
    simp only [vertexSet_deleteEdges] at hx
    exact Set.diff_subset hx
  · -- Links: a surviving link of `G̃_v^{ab}` (`p.1 ≠ e₀`) is a link of `G̃`.
    intro p x y hp
    simp only [deleteEdges_isLink, mulTilde_isLink, splitOff_isLink] at hp
    obtain ⟨hlink | hlink, hpfiber⟩ := hp
    · simpa only [mulTilde_isLink] using hlink.2.1
    · -- The `e₀`-fiber case is excluded: `p.1 = e₀` puts `p ∈ edgeFiber e₀ n`.
      exact absurd (show p ∈ edgeFiber e₀ n from hlink.1) hpfiber

/-- **The multiplied vertex-removal lands inside the multiplied splitting-off**
(`lem:forest-surgery-split`, surgery crux, reverse inclusion). The converse companion of
`mulTilde_splitOff_deleteFiber_le`: the multiplied vertex-removal `(G_v)̃ = ((G - v))̃` is a
subgraph of the multiplied splitting-off `G̃_v^{ab}`, *provided the short-circuit edge `e₀`
is fresh* (`e₀ ∉ E(G)`): `(G.removeVertex v).mulTilde n ≤ (G.splitOff v a b e₀).mulTilde n`.
Both graphs carry the vertex set `V(G) \ {v}`; every fiber `p` of `(G_v)̃` is a copy of an
edge of `G` avoiding `v` (`removeVertex_isLink`), and freshness forces `p.1 ≠ e₀`, so
`splitOff` keeps that very link (its first disjunct). This is the structural fact the
rerouting half of the surgery runs on: the part of a `G̃`-forest avoiding `v` (the forests
with `dᶠ(v) ≤ 1` reduced to `G_v`) transports verbatim into `G̃_v^{ab}` — only the
`v`-traversing tree-path of a `dᶠ(v) = 2` forest needs the `ã̃b` swap. -/
lemma mulTilde_removeVertex_le_splitOff {G : Graph α β} {v a b : α} {e₀ : β} (n : ℕ)
    (he₀ : e₀ ∉ E(G)) :
    (G.removeVertex v).mulTilde n ≤ (G.splitOff v a b e₀).mulTilde n := by
  refine ⟨?_, ?_⟩
  · -- Vertex sets: both are `V(G) \ {v}` definitionally.
    intro x hx
    exact hx
  · -- Links: a link of `(G_v)̃` (a `v`-avoiding `G`-link) is a `splitOff` link (first disjunct).
    intro p x y hp
    simp only [mulTilde_isLink, removeVertex_isLink] at hp ⊢
    obtain ⟨hlink, hxv, hyv⟩ := hp
    rw [splitOff_isLink]
    refine Or.inl ⟨?_, hlink, hxv, hyv⟩
    -- `p.1 ≠ e₀`: `p.1 ∈ E(G)` (it carries the link `hlink`) but `e₀ ∉ E(G)`.
    rintro rfl; exact he₀ hlink.edge_mem

/-- **The surviving fibers of the multiplied splitting-off are exactly `E((G_v)̃)`**
(`lem:reduction-step`, splitting-off minimality transport; Katoh–Tanigawa 2011 Lemmas 4.7–4.8,
ground-set bridge). With the short-circuit edge `e₀` fresh (`e₀ ∉ E(G)`), the multiplied
splitting-off `G̃_v^{ab}` has ground set the disjoint union of the fresh short-circuit fiber
`ã̃b = edgeFiber e₀ n` and the surviving fibers, and the surviving fibers
(`E(G̃_v^{ab}) ∖ ã̃b`) are *precisely* the fibers of the multiplied vertex-removal
`(G_v)̃ = ((G − v))̃`:
`E((G_v^{ab}))̃ ∖ ã̃b = E((G_v))̃`.

This is the ground-set decomposition the by-hand base correspondence of KT 4.8 runs on:
splitting-off only *adds* the fresh `e₀`-fiber to and *removes* the two `v`-incident fibers
from `G̃`, so deleting the fresh fiber recovers exactly the `v`-free fibers — which are the
ground set of `M((G_v)̃)`. Sharpens the one-sided inclusions
`mulTilde_splitOff_deleteFiber_le` / `mulTilde_removeVertex_le_splitOff` to the edge-set
equality the base lift needs to identify the surviving matroid's ground set. The two `⊆`
directions are: a non-`e₀` fiber of `G̃_v^{ab}` carries a `v`-avoiding `G`-link (so its edge
lies in `E(G_v)`), and conversely a fiber of `(G_v)̃` is `v`-free with a fresh-distinct edge
(forced by `e₀ ∉ E(G)`), hence kept by `splitOff`'s first disjunct. -/
lemma edgeSet_mulTilde_splitOff_diff_fiber {G : Graph α β} {v a b : α} {e₀ : β} (n : ℕ)
    (he₀ : e₀ ∉ E(G)) :
    E((G.splitOff v a b e₀).mulTilde n) \ edgeFiber e₀ n = E((G.removeVertex v).mulTilde n) := by
  ext p
  simp only [Set.mem_diff, edgeFiber, Set.mem_setOf_eq, mem_edgeSet_mulTilde,
    edgeSet_splitOff, Set.mem_union]
  rw [removeVertex, edgeSet_deleteVerts]
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨(⟨rfl, _⟩ | ⟨_, x, y, hl, hx, hy⟩), hpne⟩
    · exact absurd rfl hpne
    · exact ⟨x, y, hl, hx, hy⟩
  · rintro ⟨x, y, hl, hx, hy⟩
    refine ⟨Or.inr ⟨?_, x, y, hl, hx, hy⟩, ?_⟩
    · rintro rfl; exact he₀ hl.edge_mem
    · rintro rfl; exact he₀ hl.edge_mem

/-- **A forest of the multiplied vertex-removal is a forest of the multiplied splitting-off**
(`lem:forest-surgery-split`, surgery crux, reverse acyclicity transport; Katoh–Tanigawa 2011
Lemma 4.1). The reverse companion of `isAcyclicSet_mulTilde_of_splitOff_of_disjoint`: any
cycle-matroid-acyclic fiber set `F` of the multiplied vertex-removal `(G_v)̃ = ((G - v))̃` is
acyclic in the multiplied splitting-off `G̃_v^{ab}`, whenever the short-circuit edge `e₀` is
fresh (`e₀ ∉ E(G)`):
`((G - v))̃.cycleMatroid.Indep F → ((G_v^{ab}))̃.cycleMatroid.Indep F`.

This is the half of the surgery's acyclicity-preservation that transports *into* `G̃_v^{ab}`
without rerouting: a forest of `G̃` reduced to the vertex-removal `G_v` (its `v`-edges
dropped) is a forest of `G̃_v^{ab}` verbatim, because deleting `v` strictly precedes the
short-circuit. No disjointness hypothesis is needed — `(G_v)̃` carries no `v`-incident fibers
at all, so it sits below `G̃_v^{ab}` unconditionally (`mulTilde_removeVertex_le_splitOff`); the
`v`-traversing tree-path that *does* need the `ã̃b` swap is the residual rerouting crux. -/
lemma isAcyclicSet_mulTilde_splitOff_of_removeVertex {G : Graph α β} {v a b : α} {e₀ : β}
    {n : ℕ} (he₀ : e₀ ∉ E(G)) {F : Set (β × Fin (bodyHingeMult n))}
    (hF : ((G.removeVertex v).mulTilde n).cycleMatroid.Indep F) :
    ((G.splitOff v a b e₀).mulTilde n).cycleMatroid.Indep F := by
  rw [cycleMatroid_indep] at hF ⊢
  exact hF.mono (mulTilde_removeVertex_le_splitOff n he₀)

/-- **Acyclicity transports across the short-circuit** (`lem:forest-surgery-split`, surgery
crux; Katoh–Tanigawa 2011 Lemma 4.1). A fiber set `F` that is cycle-matroid-independent
(acyclic) in the multiplied splitting-off `G̃_v^{ab}` and **disjoint from the fresh fiber**
`ã̃b = edgeFiber e₀ n` is acyclic in the multiplied original `G̃ = (D-1)·G`:
`(G̃_v^{ab}).cycleMatroid.Indep F → Disjoint F (edgeFiber e₀ n) → (G̃).cycleMatroid.Indep F`.

This is the half of the surgery's acyclicity-preservation that needs no rerouting — the
forests with `dᶠ(v) ≤ 1` at the degree-2 vertex `v`, which drop their single `v`-edge and
survive verbatim inside `G̃`. The transport routes through `mulTilde_splitOff_deleteFiber_le`
(deleting `ã̃b` from `G̃_v^{ab}` lands in `G̃`): `F`'s disjointness from `ã̃b` means `F` lives
in that deleted subgraph, where acyclicity is monotone up to `G̃` (`IsAcyclicSet.mono`,
`Graph.cycleMatroid_indep`). The rerouting half (the `dᶠ(v) = 2` forests swapping their two
`v`-edges for one `ã̃b` copy) is the residual crux of the still-red surgery. -/
lemma isAcyclicSet_mulTilde_of_splitOff_of_disjoint {G : Graph α β} {v a b : α} {e₀ : β}
    {n : ℕ} {F : Set (β × Fin (bodyHingeMult n))}
    (hF : ((G.splitOff v a b e₀).mulTilde n).cycleMatroid.Indep F)
    (hdisj : Disjoint F (edgeFiber e₀ n)) :
    (G.mulTilde n).cycleMatroid.Indep F := by
  rw [cycleMatroid_indep] at hF ⊢
  -- `F` is acyclic in `G̃_v^{ab}` and avoids the deleted fiber, hence acyclic in the
  -- deleted subgraph `G̃_v^{ab} ＼ ã̃b`.
  have hFdel : (((G.splitOff v a b e₀).mulTilde n).deleteEdges (edgeFiber e₀ n)).IsAcyclicSet F :=
      by
    refine ⟨?_, fun C hC hCF ↦ ?_⟩
    · rw [edgeSet_deleteEdges]
      exact Set.subset_diff.mpr ⟨hF.1, hdisj⟩
    · -- A cyclic walk in the deleted subgraph is one in `G̃_v^{ab}`, contradicting `hF`.
      exact hF.2 C (hC.of_le (deleteEdges_le)) hCF
  -- Transport acyclicity up the subgraph `… ＼ ã̃b ≤ G̃`.
  exact hFdel.mono (mulTilde_splitOff_deleteFiber_le n)

/-! ## Degree of a vertex in a fiber set (`lem:forest-surgery-split`, degree substrate)

The forest surgery of Katoh–Tanigawa 2011 Lemma 4.1 reroutes the `D` edge-disjoint
forests `F₀, …, F_{D-1}` of an `M(G̃)`-independent set across a degree-2 vertex `v`.
Per forest `Fᵢ`, the reroute is driven by the **degree of `v` in `Fᵢ`** — the number
`dᶠ(v)` of fibers of `Fᵢ` incident to `v` in `G̃`. KT's surgery splits the forests by
`dᶠ(v) ∈ {0, 1, 2}` (a forest meeting `v` at `0` fibers is untouched; at `1` fiber its
`v`-edge is dropped; at `2` fibers its two `v`-edges are swapped for one `ãb` copy),
and the `< D − 1` short-circuit-copy count `h' ≤ D − 2` is read off these per-forest
degrees.

This subsection lands the **degree substrate** the surgery bottoms out on: the set of
fibers of `G̃` incident to `v` (`fiberAtVertex`), the reduction of `G̃`-incidence to
`G`-incidence at the underlying edge (`mulTilde_inc`), the per-fiber-set degree
`fiberDegree`, and the count `|fibers at v in E(G̃)| = (D − 1)·|incident G-edges at v|`
(`fiberAtVertex_inter_edgeSet_ncard`) — so a *degree-2* vertex `v` of `G` has exactly
`2(D − 1)` incident fibers, the quantity the `h' ≤ D − 2` bound is counted against. The
acyclicity-preserving reroute itself (a `G̃ᵥᵃᵇ`-cycle through `ãb` lifts to a
`v`-traversing path of `G̃`) is landed as `isAcyclicSet_splitOff_reroute` (reroute wiring
step 2); what remains of the still-red `lem:forest-surgery-split` is only the per-`D`-forest
bookkeeping assembly. -/

/-- **The fibers of `G̃` incident to a vertex `v`** (`lem:forest-surgery-split`, degree
substrate): the set of fibers `p` of the multiplied graph `G̃ = (D-1)·G` with `v` as an
endpoint. These are the fibers the Katoh–Tanigawa 2011 Lemma 4.1 forest surgery reroutes
when it short-circuits the two edges through a degree-2 vertex `v`. -/
def fiberAtVertex (G : Graph α β) (n : ℕ) (v : α) : Set (β × Fin (bodyHingeMult n)) :=
  {p | (G.mulTilde n).Inc p v}

/-- **`G̃`-incidence reduces to `G`-incidence at the underlying edge**
(`lem:forest-surgery-split`, degree substrate): a fiber `p` of `G̃ = (D-1)·G` is incident
to a vertex `v` exactly when its underlying `G`-edge `p.1` is. Each parallel copy `p` of
an edge `e` of `G` carries the same incidences as `e`. -/
lemma mulTilde_inc {G : Graph α β} {n : ℕ} {p : β × Fin (bodyHingeMult n)} {v : α} :
    (G.mulTilde n).Inc p v ↔ G.Inc p.1 v := by
  rw [mulTilde, edgeMultiply_inc]

@[simp]
lemma mem_fiberAtVertex {G : Graph α β} {n : ℕ} {v : α} {p : β × Fin (bodyHingeMult n)} :
    p ∈ G.fiberAtVertex n v ↔ G.Inc p.1 v := by
  rw [fiberAtVertex, Set.mem_setOf_eq, mulTilde_inc]

/-- **The fibers at `v` are the copies of `v`'s incident edges**
(`lem:forest-surgery-split`, degree substrate): inside `E(G̃)`, the fibers incident to
`v` are exactly the fibers `ẽ` of the `G`-edges `e` incident to `v`. So the fibers at `v`
in `E(G̃)` partition by the underlying incident edge. -/
lemma fiberAtVertex_inter_edgeSet {G : Graph α β} {n : ℕ} {v : α} :
    G.fiberAtVertex n v ∩ E(G.mulTilde n) =
      {p : β × Fin (bodyHingeMult n) | p.1 ∈ {e | G.Inc e v}} := by
  ext p
  simp only [Set.mem_inter_iff, mem_fiberAtVertex, mem_edgeSet_mulTilde,
    Set.mem_setOf_eq]
  exact ⟨fun ⟨hinc, _⟩ ↦ hinc, fun hinc ↦ ⟨hinc, hinc.edge_mem⟩⟩

/-- **Count of the fibers at `v`** (`lem:forest-surgery-split`, degree substrate;
Katoh–Tanigawa 2011 Lemma 4.1). The number of fibers of `G̃ = (D-1)·G` incident to `v`
inside `E(G̃)` is `(D − 1)` times the number of `G`-edges incident to `v`:
`|fibers at v in E(G̃)| = bodyHingeMult n · |{e | G.Inc e v}|`. For a degree-2 vertex `v`
of `G` (exactly two incident edges) this is `2(D − 1)`, the total fiber count the surgery
distributes among the `D` forests and counts the `h' ≤ D − 2` short-circuit copies
against. -/
lemma fiberAtVertex_inter_edgeSet_ncard [Finite β] {G : Graph α β} {n : ℕ} {v : α} :
    (G.fiberAtVertex n v ∩ E(G.mulTilde n)).ncard
      = bodyHingeMult n * {e | G.Inc e v}.ncard := by
  rw [fiberAtVertex_inter_edgeSet]
  have hprod : {p : β × Fin (bodyHingeMult n) | p.1 ∈ {e | G.Inc e v}}
      = {e | G.Inc e v} ×ˢ (Set.univ : Set (Fin (bodyHingeMult n))) := by
    ext ⟨e, i⟩; simp
  rw [hprod, Set.ncard_prod, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin,
    mul_comm]

/-- **The degree of `v` in a fiber set `F`** (`lem:forest-surgery-split`, degree
substrate): the number `dᶠ(v)` of fibers of `F` incident to `v` in `G̃ = (D-1)·G`. This
is the per-forest quantity Katoh–Tanigawa 2011 Lemma 4.1's surgery splits on
(`dᶠ(v) ∈ {0, 1, 2}` when `v` is a degree-2 vertex), driving the reroute of each forest
`Fᵢ` across the short-circuit `ab`. -/
noncomputable def fiberDegree (G : Graph α β) (n : ℕ) (v : α)
    (F : Set (β × Fin (bodyHingeMult n))) : ℕ :=
  (F ∩ G.fiberAtVertex n v).ncard

/-- **Degree monotonicity** (`lem:forest-surgery-split`, degree substrate): the degree of
`v` in a subset `F' ⊆ F` is at most its degree in `F`. The surgery drops the `v`-edges of
each forest, reducing `dᶠ(v)`; this is the monotonicity that bounds the rerouted degrees. -/
lemma fiberDegree_mono [Finite β] {G : Graph α β} {n : ℕ} {v : α}
    {F' F : Set (β × Fin (bodyHingeMult n))} (h : F' ⊆ F) :
    G.fiberDegree n v F' ≤ G.fiberDegree n v F :=
  Set.ncard_le_ncard (Set.inter_subset_inter_left _ h) (Set.toFinite _)

/-- **The fiber-degree at `v` is bounded by the total fiber count at `v`**
(`lem:forest-surgery-split`, degree substrate). For a fiber set `F ⊆ E(G̃)`, the degree
`dᶠ(v)` is at most `(D − 1)·|incident G-edges at v|`; for a degree-2 vertex `v` this is
`2(D − 1)`, so the per-forest degrees sum to at most `2(D − 1)` across the `D` forests of
an independent set, the count the surgery's `h' ≤ D − 2` short-circuit bound rests on. -/
lemma fiberDegree_le [Finite β] {G : Graph α β} {n : ℕ} {v : α}
    {F : Set (β × Fin (bodyHingeMult n))} (hF : F ⊆ E(G.mulTilde n)) :
    G.fiberDegree n v F ≤ bodyHingeMult n * {e | G.Inc e v}.ncard := by
  rw [fiberDegree, ← fiberAtVertex_inter_edgeSet_ncard]
  refine Set.ncard_le_ncard (fun p hp ↦ ⟨hp.2, hF hp.1⟩) (Set.toFinite _)

/-- **The `v`-free part of a `G̃`-forest transports verbatim into `G̃_v^{ab}`**
(`lem:forest-surgery-split`, reroute wiring step 1; Katoh–Tanigawa 2011 Lemma 4.1). Given a
cycle-matroid-acyclic (forest) fiber set `F` of the multiplied graph `G̃ = (D-1)·G` and a
*fresh* short-circuit edge `e₀ ∉ E(G)`, the part of `F` avoiding the degree-2 vertex `v` —
`F ∖ fiberAtVertex v`, the fibers KT's surgery keeps untouched (`dᶠ(v) = 0` forests entirely,
and the surviving non-`v`-edges of the `dᶠ(v) ∈ {1,2}` forests) — is acyclic in the multiplied
splitting-off `G̃_v^{ab}`.

This is the half of KT 4.1's per-forest reroute that needs *no* `ã̃b` swap: every `v`-free
fiber `p` of `F` is a copy of a `v`-avoiding edge of `G`, hence a fiber of the multiplied
vertex-removal `(G_v)̃`. The `v`-free part is a subset of `F`, so acyclic in `G̃`; it lives in
`E((G_v)̃) ⊆ E(G̃)`, so by `IsAcyclicSet.anti_inter` along `(G_v)̃ = ((G − v))̃ ≤ G̃`
(`edgeMultiply_mono` of `deleteVerts_le`) it is acyclic already in `(G_v)̃`, and
`isAcyclicSet_mulTilde_splitOff_of_removeVertex` lifts that into `G̃_v^{ab}`. The residual
reroute crux — the `dᶠ(v) = 2` forest swapping its two `v`-edges for one `ã̃b` copy (a
`v`-traversing tree-path lift) — is the still-open second wiring step. -/
lemma isAcyclicSet_splitOff_of_diff_fiberAtVertex {G : Graph α β} {v a b : α} {e₀ : β}
    {n : ℕ} (he₀ : e₀ ∉ E(G)) {F : Set (β × Fin (bodyHingeMult n))}
    (hF : ((G.mulTilde n).cycleMatroid).Indep F) :
    ((G.splitOff v a b e₀).mulTilde n).cycleMatroid.Indep (F \ G.fiberAtVertex n v) := by
  rw [cycleMatroid_indep] at hF
  -- The `v`-free part lands in the ground set of the multiplied vertex-removal.
  have hsub : F \ G.fiberAtVertex n v ⊆ E((G.removeVertex v).mulTilde n) := by
    rintro p ⟨hpF, hpv⟩
    have hpE : p ∈ E(G.mulTilde n) := hF.1 hpF
    rw [mem_fiberAtVertex] at hpv
    rw [mem_edgeSet_mulTilde] at hpE
    obtain ⟨x, y, hl⟩ := exists_isLink_of_mem_edgeSet hpE
    rw [mem_edgeSet_mulTilde, removeVertex,
      edgeSet_deleteVerts, Set.mem_setOf_eq]
    exact ⟨x, y, hl, fun hx ↦ hpv (hx ▸ hl.inc_left), fun hy ↦ hpv (hy ▸ hl.inc_right)⟩
  -- Acyclic in `(G_v)̃` (subset of the `G̃`-forest, restricted to the smaller ground set),
  -- then lift to `G̃_v^{ab}`.
  apply isAcyclicSet_mulTilde_splitOff_of_removeVertex he₀
  rw [cycleMatroid_indep]
  have hle : (G.removeVertex v).mulTilde n ≤ G.mulTilde n :=
    edgeMultiply_mono (by rw [removeVertex]; exact deleteVerts_le) _
  have hanti := hF.anti (Set.diff_subset (t := G.fiberAtVertex n v))
  have := hanti.anti_inter hle
  rwa [Set.inter_eq_self_of_subset_right hsub] at this

/-! ## At most one fresh copy per forest (`lem:forest-surgery-split`, reroute count substrate)

The rerouting half of the Katoh–Tanigawa 2011 Lemma 4.1 forest surgery swaps the two
`v`-edges of each `dᶠ(v) = 2` forest for a *single* fresh copy of the short-circuit fiber
`ã̃b = edgeFiber e₀ n`. The bound that makes the `< D - 1` short-circuit-copy count
(`h' ≤ D - 2`) go through is that **each rerouted forest absorbs at most one `ã̃b` copy**:
an acyclic fiber set of the multiplied splitting-off `G̃_v^{ab}` cannot contain two distinct
parallel copies of `e₀`, since two parallel copies of the same edge between distinct
endpoints `a ≠ b` form a 2-cycle. Aggregated across the `D` forests this caps the total
`ã̃b`-copy count at `D`, and the per-forest single-copy fact is what drives the reroute's
edge-disjointness bookkeeping (the residual rerouting transport itself — a `v`-traversing
tree-path lift — is the still-open crux). -/

/-- **Two distinct parallel copies of the short-circuit edge form a 2-cycle**
(`lem:forest-surgery-split`, reroute count substrate). When the splitting-off `G_v^{ab}` at
a degree-2 vertex `v` with *distinct* neighbours `a ≠ b` (`a, b ≠ v`, `a, b ∈ V(G)`) inserts
its fresh edge `e₀`, any two distinct copies `p ≠ q` of `e₀` in the multiplied splitting-off
`G̃_v^{ab}` are a cycle-edge-set: `{p, q}` is `IsCycleSet` of `G̃_v^{ab}`. Both copies join
the same endpoints `a, b` (`splitOff`'s fresh-edge disjunct), so the length-2 closed walk
`a —p→ b —q→ a` is a cyclic walk. -/
lemma isCycleSet_pair_edgeFiber_splitOff {G : Graph α β} {v a b : α} {e₀ : β} {n : ℕ}
    (hab : a ≠ b) (ha : a ≠ v) (hb : b ≠ v) (haV : a ∈ V(G)) (hbV : b ∈ V(G))
    {p q : β × Fin (bodyHingeMult n)} (hp : p.1 = e₀) (hq : q.1 = e₀) (hpq : p ≠ q) :
    ((G.splitOff v a b e₀).mulTilde n).IsCycleSet {p, q} := by
  -- Both `p` and `q` are copies of `e₀`, hence links of `a, b` in `G̃_v^{ab}`.
  have hlink : ∀ r : β × Fin (bodyHingeMult n), r.1 = e₀ →
      ((G.splitOff v a b e₀).mulTilde n).IsLink r a b := by
    intro r hr
    rw [mulTilde_isLink, splitOff_isLink, hr]
    exact Or.inr ⟨rfl, ha, hb, haV, hbV, Or.inl ⟨rfl, rfl⟩⟩
  have hlinkp := hlink p hp
  have hlinkq := hlink q hq
  -- The length-2 closed walk `a —p→ b —q→ a`.
  refine ⟨WList.cons a p (WList.cons b q (WList.nil a)), ?_, by simp⟩
  have hwalk : ((G.splitOff v a b e₀).mulTilde n).IsWalk
      (WList.cons a p (WList.cons b q (WList.nil a))) := by
    rw [cons_isWalk_iff, cons_isWalk_iff, nil_isWalk_iff]
    exact ⟨hlinkp, hlinkq.symm, hlinkp.left_mem⟩
  refine ⟨⟨⟨hwalk, ?_⟩, by simp, ?_⟩, ?_⟩
  · -- Distinct edges `p ≠ q`.
    simp [hpq]
  · -- Closed: first vertex = last vertex.
    simp
  · -- No repeated vertices in the tail `[b, a]`: `a ≠ b`.
    simp [hab.symm]

/-- **A forest of the multiplied splitting-off carries at most one short-circuit copy**
(`lem:forest-surgery-split`, reroute count substrate; Katoh–Tanigawa 2011 Lemma 4.1). When the
splitting-off `G_v^{ab}` at a degree-2 vertex `v` with distinct neighbours `a ≠ b`
(`a, b ≠ v`, `a, b ∈ V(G)`) inserts its fresh edge `e₀`, any cycle-matroid-acyclic (forest)
fiber set `F` of the multiplied splitting-off `G̃_v^{ab}` meets the fresh short-circuit fiber
`ã̃b = edgeFiber e₀ n` in at most one element: `(F ∩ edgeFiber e₀ n).Subsingleton`.

Two distinct copies of `e₀` form a 2-cycle (`isCycleSet_pair_edgeFiber_splitOff`), so a forest
— containing no cycle — can keep at most one. This is the per-forest cap behind KT 4.1's
`< D - 1` short-circuit-copy count: across the `D` rerouted forests the total number of
`ã̃b` copies retained is at most `D`, each forest absorbing one swapped `v`-traversing path. -/
lemma fiber_inter_subsingleton_of_isAcyclicSet_splitOff {G : Graph α β}
    {v a b : α} {e₀ : β} {n : ℕ} (hab : a ≠ b) (ha : a ≠ v) (hb : b ≠ v) (haV : a ∈ V(G))
    (hbV : b ∈ V(G)) {F : Set (β × Fin (bodyHingeMult n))}
    (hF : ((G.splitOff v a b e₀).mulTilde n).cycleMatroid.Indep F) :
    (F ∩ edgeFiber e₀ n).Subsingleton := by
  rw [cycleMatroid_indep] at hF
  intro p hp q hq
  by_contra hpq
  -- `p, q` are distinct copies of `e₀` in `F`, so `{p, q}` is a cycle of `G̃_v^{ab}`.
  obtain ⟨C, hCG, hC, hCpq⟩ := isCycleSet_iff.mp
    (isCycleSet_pair_edgeFiber_splitOff hab ha hb haV hbV hp.2 hq.2 hpq)
  -- A cycle with edge set `{p, q} ⊆ F` contradicts the acyclicity of `F`.
  refine (not_isAcyclicSet_iff hF.1).mpr ⟨C, hC, hCG, ?_⟩ hF
  rw [← hCpq]
  exact Set.insert_subset hp.1 (Set.singleton_subset_iff.mpr hq.1)

/-- **Two distinct parallel copies of an edge of `G` form a 2-cycle in `G̃`**
(`lem:forest-surgery-count`, degree-cap substrate). If `e` is an edge of `G` linking two
*distinct* vertices `x ≠ y`, any two distinct copies `p ≠ q` of `e` in the multiplied graph
`G̃ = (D-1)·G` are a cycle-edge-set: `{p, q}` is `IsCycleSet` of `G̃`. Both copies link the
same endpoints `x, y`, so `x —p→ y —q→ x` is a length-2 cyclic walk. (This is the plain-`G̃`
analogue of `isCycleSet_pair_edgeFiber_splitOff`; it caps each forest's `v`-degree at `2`.) -/
lemma isCycleSet_pair_edgeFiber_mulTilde {G : Graph α β} {n : ℕ} {e : β} {x y : α}
    (hxy : x ≠ y) (hl : G.IsLink e x y)
    {p q : β × Fin (bodyHingeMult n)} (hp : p.1 = e) (hq : q.1 = e) (hpq : p ≠ q) :
    (G.mulTilde n).IsCycleSet {p, q} := by
  have hlink : ∀ r : β × Fin (bodyHingeMult n), r.1 = e → (G.mulTilde n).IsLink r x y :=
    fun r hr ↦ by rw [mulTilde_isLink, hr]; exact hl
  have hlinkp := hlink p hp
  have hlinkq := hlink q hq
  refine ⟨WList.cons x p (WList.cons y q (WList.nil x)), ?_, by simp⟩
  have hwalk : (G.mulTilde n).IsWalk (WList.cons x p (WList.cons y q (WList.nil x))) := by
    rw [cons_isWalk_iff, cons_isWalk_iff, nil_isWalk_iff]
    exact ⟨hlinkp, hlinkq.symm, hlinkp.left_mem⟩
  refine ⟨⟨⟨hwalk, ?_⟩, by simp, ?_⟩, ?_⟩
  · simp [hpq]
  · simp
  · simp [hxy.symm]

/-- **A `G̃`-forest holds at most one copy of any single edge** (`lem:forest-surgery-count`,
degree-cap substrate). For a cycle-matroid-acyclic (forest) fiber set `F` of `G̃` and an edge
`e` of `G` between *distinct* endpoints, `F` meets the fiber `ẽ = edgeFiber e n` in at most one
element. Two distinct copies of `e` form a 2-cycle (`isCycleSet_pair_edgeFiber_mulTilde`),
which a forest cannot contain. -/
lemma fiber_inter_subsingleton_of_isAcyclicSet_mulTilde {G : Graph α β} {n : ℕ} {e : β}
    {x y : α} (hxy : x ≠ y) (hl : G.IsLink e x y) {F : Set (β × Fin (bodyHingeMult n))}
    (hF : (G.mulTilde n).cycleMatroid.Indep F) : (F ∩ edgeFiber e n).Subsingleton := by
  rw [cycleMatroid_indep] at hF
  intro p hp q hq
  by_contra hpq
  obtain ⟨C, hCG, hC, hCpq⟩ := isCycleSet_iff.mp
    (isCycleSet_pair_edgeFiber_mulTilde hxy hl hp.2 hq.2 hpq)
  refine (not_isAcyclicSet_iff hF.1).mpr ⟨C, hC, hCG, ?_⟩ hF
  rw [← hCpq]
  exact Set.insert_subset hp.1 (Set.singleton_subset_iff.mpr hq.1)

/-! ## The degree-2 reroute preserves acyclicity (`lem:forest-surgery-split`, reroute wiring step 2)

The genuine combinatorial crux of the Katoh–Tanigawa 2011 Lemma 4.1 forest surgery: a balanced
forest `F` of `G̃` that uses **both** of its two `v`-edges (`dᶠ(v) = 2`: the `va`-copy `pa` and
the `vb`-copy `pb`) trades them for a single short-circuit copy `r` of the fresh edge `e₀`. The
rerouted forest `(F ∖ {pa, pb}) ∪ {r}` must stay acyclic in the multiplied splitting-off
`G̃_v^{ab}`.

The acyclicity rests on a **cycle-lift**: any cycle `C` of `G̃_v^{ab}` whose edges lie in
`(F ∖ {pa, pb}) ∪ {r}` lifts to a cyclic structure of `G̃` inside `F`, contradicting `F`'s
acyclicity. Two cases. If `C` avoids `r`, its edges lie in `F ∖ {pa, pb}` (so avoid the fresh
fiber), and deleting the fresh fiber from `G̃_v^{ab}` lands in `G̃`
(`mulTilde_splitOff_deleteFiber_le`), so `C` is already a cycle of `G̃` in `F`. If `C` uses `r` —
exactly once, as a trail has distinct edges — rotate `C` so `r` is its first edge,
`C = cons x r w'` with `{x, w'.first} = {a, b}`. The fresh edge `r` joins `a, b` in `G̃_v^{ab}`;
substituting the `v`-traversing 2-path `a —pa— v —pb— b` of `G̃` for `r` turns `C` into a closed
`G̃`-trail (the substituted `pa, pb ∉ E(w')`, distinct from each other and from `w'`'s edges), and
a closed trail contains a cycle (`IsTour.exists_isCyclicWalk`) whose edges are a sublist — hence
still inside `F = (F ∖ {pa, pb}) ∪ {pa, pb}`. Either way `F`
carries a `G̃`-cycle, contradiction. This is the last open wiring step; with it the per-forest
reroute map and the deficiency-relation assembly close `lem:forest-surgery-split`. -/

/-- **The degree-2 reroute preserves acyclicity** (`lem:forest-surgery-split`, reroute wiring
step 2; Katoh–Tanigawa 2011 Lemma 4.1 p.660). Let `v` be a degree-2 vertex of `G` with distinct
neighbours `a ≠ b` (`a, b ≠ v`, `a, b ∈ V(G)`) and `e₀ ∉ E(G)` the fresh short-circuit edge. Let
`F` be a `(G̃).cycleMatroid`-independent (forest) fiber set whose two `v`-incident fibers are
exactly `pa` (a `v—a` copy) and `pb` (a `v—b` copy) — the `dᶠ(v) = 2` case of the surgery — and
let `r` be any copy of `e₀` (`r.1 = e₀`). Then the **rerouted forest** `(F ∖ {pa, pb}) ∪ {r}`,
obtained by swapping the two `v`-edges for the single short-circuit copy `r`, is acyclic in the
multiplied splitting-off `G̃_v^{ab}`:
`((G.splitOff v a b e₀).mulTilde n).cycleMatroid.Indep (insert r (F \ {pa, pb}))`.

This is the rerouting half of KT 4.1's per-forest acyclicity preservation — the half
`isAcyclicSet_splitOff_of_diff_fiberAtVertex` (reroute wiring step 1, the `v`-free part) does
*not* cover. The proof lifts a hypothetical `G̃_v^{ab}`-cycle through `r` to a `G̃`-cycle inside
`F` (substituting `r` by the 2-path through `v`), contradicting acyclicity; see the section
preamble. -/
lemma isAcyclicSet_splitOff_reroute {G : Graph α β} {v a b : α} {e₀ : β} {n : ℕ}
    (ha : a ≠ v) (hb : b ≠ v) (haV : a ∈ V(G)) (hbV : b ∈ V(G))
    {F : Set (β × Fin (bodyHingeMult n))} {pa pb r : β × Fin (bodyHingeMult n)}
    (hF : ((G.mulTilde n).cycleMatroid).Indep F)
    (hpa : (G.mulTilde n).IsLink pa v a) (hpb : (G.mulTilde n).IsLink pb v b)
    (hpaF : pa ∈ F) (hpbF : pb ∈ F) (hpab : pa ≠ pb)
    (hFv : ∀ p ∈ F, (G.mulTilde n).Inc p v → p = pa ∨ p = pb)
    (hr : r.1 = e₀) (he₀ : e₀ ∉ E(G)) :
    ((G.splitOff v a b e₀).mulTilde n).cycleMatroid.Indep (insert r (F \ {pa, pb})) := by
  classical
  -- Abbreviations: the original `K = G̃` and the splitting-off `Ksp = G̃_v^{ab}`.
  set K := G.mulTilde n with hK
  set Ksp := (G.splitOff v a b e₀).mulTilde n with hKsp
  rw [cycleMatroid_indep] at hF
  -- The rerouted set lies in the ground set of `Ksp`.
  have hpaE : pa.1 ∈ E(G) := by
    rw [hK, mulTilde_isLink] at hpa; exact hpa.edge_mem
  have hpbE : pb.1 ∈ E(G) := by
    rw [hK, mulTilde_isLink] at hpb; exact hpb.edge_mem
  -- `pa, pb` are not copies of the fresh edge.
  have hpane₀ : pa.1 ≠ e₀ := fun h ↦ he₀ (h ▸ hpaE)
  have hpbne₀ : pb.1 ≠ e₀ := fun h ↦ he₀ (h ▸ hpbE)
  have hrE : r ∈ E(Ksp) := by
    rw [hKsp, mem_edgeSet_mulTilde, edgeSet_splitOff]
    exact Or.inl ⟨hr, ha, hb, haV, hbV⟩
  have hdiffsub : F \ {pa, pb} ⊆ E(Ksp) := by
    rintro p ⟨hpF, hp2⟩
    rw [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hp2
    have hpE : p ∈ E(K) := hF.1 hpF
    have hpv : ¬ K.Inc p v := fun hinc ↦ (hFv p hpF hinc).elim hp2.1 hp2.2
    -- `p` is a `v`-avoiding `G`-edge copy distinct from `e₀`, kept by `splitOff`.
    rw [hK, mem_edgeSet_mulTilde] at hpE
    obtain ⟨x, y, hl⟩ := exists_isLink_of_mem_edgeSet hpE
    have hxv : x ≠ v := fun hx ↦ hpv (hx ▸ (by
      rw [hK, mulTilde, edgeMultiply_inc]; exact hl.inc_left))
    have hyv : y ≠ v := fun hy ↦ hpv (hy ▸ (by
      rw [hK, mulTilde, edgeMultiply_inc]; exact hl.inc_right))
    have hpne₀ : p.1 ≠ e₀ := fun h ↦ he₀ (h ▸ hpE)
    rw [hKsp, mem_edgeSet_mulTilde, edgeSet_splitOff]
    exact Or.inr ⟨hpne₀, x, y, hl, hxv, hyv⟩
  set S := insert r (F \ {pa, pb}) with hS
  have hSE : S ⊆ E(Ksp) := Set.insert_subset hrE hdiffsub
  rw [cycleMatroid_indep, isAcyclicSet_iff]
  refine ⟨hSE, ?_⟩
  rw [restrict_isForest_iff']
  intro C hCS hCcyc
  -- The cycle's edges avoid `pa, pb` (they are kept off `S`).
  have hCnpa : pa ∉ C.edgeSet := fun h ↦ (Set.mem_of_mem_of_subset h hCS).elim
    (fun he ↦ hpane₀ (by rw [he, hr]))
    (fun ⟨_, hne⟩ ↦ hne (Or.inl rfl))
  have hCnpb : pb ∉ C.edgeSet := fun h ↦ (Set.mem_of_mem_of_subset h hCS).elim
    (fun he ↦ hpbne₀ (by rw [he, hr]))
    (fun ⟨_, hne⟩ ↦ hne (Or.inr rfl))
  by_cases hrC : r ∈ C.edgeSet
  · -- `C` uses the short-circuit copy `r`: substitute the 2-path through `v`.
    -- Rotate `C` so its first edge is `r`.
    obtain ⟨m, -, hne, hfe⟩ := WList.exists_rotate_firstEdge_eq (w := C) (e := r) hrC
    have hDcyc : Ksp.IsCyclicWalk (C.rotate m) := hCcyc.rotate m
    have hDE : (C.rotate m).edgeSet = C.edgeSet := WList.rotate_edgeSet C m
    -- Destructure the rotated walk: `C.rotate m = cons x r w'`.
    obtain ⟨x, e, w', heq⟩ := WList.nonempty_iff_exists_cons.mp (hne.rotate m)
    have her : e = r := by simp only [heq, WList.Nonempty.firstEdge_cons] at hfe; exact hfe
    subst her
    rw [heq] at hDcyc hDE
    -- `D₀ = cons x e w'` is closed, so `w'.last = x`.
    have hclosed : (WList.cons x e w').IsClosed := hDcyc.isClosed
    rw [WList.cons_isClosed_iff] at hclosed
    -- The first link of `D₀ = cons x e w'`: `e` joins `x` and `w'.first` in `Ksp`.
    have hwalk : Ksp.IsWalk (WList.cons x e w') := hDcyc.isWalk
    rw [cons_isWalk_iff] at hwalk
    obtain ⟨hrlink, hw'walk⟩ := hwalk
    -- `e` is a fresh-edge copy, so it joins exactly `a` and `b`.
    rw [hKsp, mulTilde_isLink, splitOff_isLink] at hrlink
    have hxw' : (x = a ∧ w'.first = b) ∨ (x = b ∧ w'.first = a) := by
      rcases hrlink with ⟨hne', _⟩ | ⟨_, _, _, _, _, hxy⟩
      · exact absurd hr hne'
      · exact hxy
    -- Edge bookkeeping on the cyclic walk `cons x e w'`: distinct edges, so `e ∉ E(w')`.
    have hnodup : (WList.cons x e w').edge.Nodup := hDcyc.edge_nodup
    rw [WList.cons_edge, List.nodup_cons] at hnodup
    obtain ⟨henw', hw'nodup⟩ := hnodup
    have hw'edge : ∀ p ∈ w'.edge, p ∈ F \ {pa, pb} := by
      intro p hp
      have hpS : p ∈ S := hCS (hDE ▸ (by
        rw [WList.cons_edgeSet]; exact Set.mem_insert_of_mem _ (WList.mem_edgeSet_iff.mpr hp)))
      refine (Set.mem_insert_iff.mp hpS).resolve_left ?_
      rintro rfl; exact henw' hp
    -- `w'` avoids the fresh fiber, hence lifts to a `K = G̃`-walk.
    have hw'fresh : Disjoint w'.edgeSet (edgeFiber e₀ n) := by
      rw [Set.disjoint_left]; intro p hp hpf
      have : p.1 = e₀ := hpf
      have hpEK : p ∈ E(K) := hF.1 (hw'edge p hp).1
      rw [hK, mem_edgeSet_mulTilde] at hpEK
      exact he₀ (this ▸ hpEK)
    have hw'K : K.IsWalk w' :=
      (isWalk_deleteEdges_iff.mpr ⟨hw'walk, hw'fresh⟩).of_le
        (mulTilde_splitOff_deleteFiber_le n)
    -- Build the `K`-substitute closed trail and extract a `K`-cycle inside `F`.
    have hkey : ∃ T : WList α (β × Fin (bodyHingeMult n)), K.IsTour T ∧ T.edgeSet ⊆ F := by
      rcases hxw' with ⟨hxa, hwb⟩ | ⟨hxb, hwa⟩
      · -- `x = a`, `w'.first = b`: substitute `a —pa— v —pb— b ⋯ a`.
        refine ⟨WList.cons a pa (WList.cons v pb w'), ?_, ?_⟩
        · refine ⟨⟨?_, ?_⟩, by simp, ?_⟩
          · rw [cons_isWalk_iff, cons_isWalk_iff]
            exact ⟨hpa.symm, hwb ▸ hpb, hw'K⟩
          · simp only [WList.cons_edge, List.nodup_cons, List.mem_cons]
            refine ⟨?_, ?_, hw'nodup⟩
            · rintro (h | h)
              · exact hpab h
              · exact (hw'edge pa h).2 (by simp)
            · exact fun h ↦ (hw'edge pb h).2 (by simp)
          · -- closed: first `a` = last `w'.last = x = a`.
            rw [WList.cons_isClosed_iff, WList.last_cons]; exact hxa ▸ hclosed
        · intro p hp
          simp only [WList.cons_edgeSet, Set.mem_insert_iff] at hp
          rcases hp with rfl | rfl | hp
          · exact hpaF
          · exact hpbF
          · exact (hw'edge p hp).1
      · -- `x = b`, `w'.first = a`: substitute `b —pb— v —pa— a ⋯ b`.
        refine ⟨WList.cons b pb (WList.cons v pa w'), ?_, ?_⟩
        · refine ⟨⟨?_, ?_⟩, by simp, ?_⟩
          · rw [cons_isWalk_iff, cons_isWalk_iff]
            exact ⟨hpb.symm, hwa ▸ hpa, hw'K⟩
          · simp only [WList.cons_edge, List.nodup_cons, List.mem_cons]
            refine ⟨?_, ?_, hw'nodup⟩
            · rintro (h | h)
              · exact hpab.symm h
              · exact (hw'edge pb h).2 (by simp)
            · exact fun h ↦ (hw'edge pa h).2 (by simp)
          · rw [WList.cons_isClosed_iff, WList.last_cons]; exact hxb ▸ hclosed
        · intro p hp
          simp only [WList.cons_edgeSet, Set.mem_insert_iff] at hp
          rcases hp with rfl | rfl | hp
          · exact hpbF
          · exact hpaF
          · exact (hw'edge p hp).1
    -- A `K`-tour contains a `K`-cycle whose edges are a sublist, hence inside `F`.
    obtain ⟨T, hT, hTF⟩ := hkey
    obtain ⟨C', hC', hsub⟩ := hT.exists_isCyclicWalk
    exact hF.2 C' hC' (hsub.edge_subset.trans hTF)
  · -- `C` avoids `r`, so its edges lie in `F ∖ {pa, pb}` and avoid the fresh fiber;
    -- `C` is then a cycle of `K = G̃` inside `F`, contradicting `hF`.
    have hCF : C.edgeSet ⊆ F := by
      intro p hp
      rcases Set.mem_of_mem_of_subset hp hCS with hpr | hpd
      · exact absurd (hpr ▸ hp) hrC
      · exact hpd.1
    have hCnofresh : Disjoint C.edgeSet (edgeFiber e₀ n) := by
      rw [Set.disjoint_left]
      intro p hp hpf
      have hpe₀ : p.1 = e₀ := hpf
      rcases Set.mem_of_mem_of_subset hp hCS with hpr | hpd
      · exact hrC (hpr ▸ hp)
      · have hpEK : p ∈ E(K) := hF.1 hpd.1
        rw [hK, mem_edgeSet_mulTilde] at hpEK
        exact he₀ (hpe₀ ▸ hpEK)
    -- Lift `C` to a cyclic walk of `K = G̃` inside `F`, contradicting `F` acyclic.
    have hCK : K.IsCyclicWalk C :=
      ((deleteEdges_isCyclicWalk_iff _ _).mpr ⟨hCcyc, hCnofresh⟩).of_le
        (mulTilde_splitOff_deleteFiber_le n)
    exact hF.2 C hCK hCF

/-! ## The reverse degree-2 swap preserves acyclicity (`lem:edge-splitting`, KT 4.2 forest core)

The reverse companion of `isAcyclicSet_splitOff_reroute`, and the genuinely new engine of the
edge-splitting extension (Katoh–Tanigawa 2011 Lemma 4.2, the forest core of the all-`k` layer).
Where the forward reroute trades a degree-2 forest's two `v`-edges for one short-circuit copy,
the reverse swap **undoes** that move: a forest `F'` of the multiplied splitting-off `G̃_v^{ab}`
that uses a short-circuit copy `r` of the fresh edge `e₀` trades it back for the two `v`-edges
`pa` (a `v—a` copy) and `pb` (a `v—b` copy). The swapped set `(F' ∖ {r}) ∪ {pa, pb}` must stay
acyclic in the multiplied original `G̃ = (D−1)·G`.

The acyclicity rests on the dual cycle-lift: any cycle `C` of `G̃` whose edges lie in
`(F' ∖ {r}) ∪ {pa, pb}` lifts to a cyclic structure of `G̃_v^{ab}` inside `F'`, contradicting
`F'`'s acyclicity. The fresh vertex `v` is incident in the swapped set to exactly `pa, pb`
(every fiber of `F'` lives in `E(G̃_v^{ab})`, which omits `v`), so a cycle either avoids both
`v`-edges or uses both — using exactly one would leave `v` with degree 1, impossible in a cycle.
If `C` avoids both, its edges lie in `F' ∖ {r} ⊆ E((G_v)̃)` (the short-circuit copies of `F'`
are a subsingleton, so removing `r` clears the fresh fiber), and `(G_v)̃ ≤ G̃_v^{ab}` lifts `C`
into `G̃_v^{ab}` inside `F'`. If `C` uses both, rotate it so `pa` is its first edge; its last
edge is forced to be `pb` (the only other `v`-edge in the swapped set, reached because `C`
closes at `v`), so `C = (a —pa— v —pb— b) ⋯ a` with the middle stretch `w₂` from `a` to `b`
avoiding `v`. Substituting the short-circuit copy `r` (which joins `a, b` in `G̃_v^{ab}`) for the
`v`-traversing 2-path turns `C` into a closed `G̃_v^{ab}`-trail whose edges sit inside `F'`,
hence contains a `G̃_v^{ab}`-cycle inside `F'`. Either way `F'` carries a cycle, contradiction.

This is the brick the all-`k` edge-splitting extension `splitOff_indep_extend_of_fiber_lt`
(KT 4.2(i)/(ii)) runs on: each split-side forest using one `e₀`-copy is converted up to a
`G̃`-forest using the two `v`-edges. Its companion pendant-insert brick — a `v`-avoiding
`G̃_v^{ab}`-forest absorbing a single `v`-edge copy — composes the landed acyclicity transport
`isAcyclicSet_mulTilde_of_splitOff_of_disjoint` with `acyclicSet_insert_vfiber_of_not_inc`. -/

/-- **The reverse degree-2 swap preserves acyclicity** (`lem:edge-splitting`, KT 4.2 forest
core; Katoh–Tanigawa 2011 Lemma 4.2 p.660). The reverse companion of
`isAcyclicSet_splitOff_reroute`. Let `v` be a vertex of `G` with distinct neighbours `a ≠ b`
(`a, b ≠ v`, `a, b ∈ V(G)`) and `e₀ ∉ E(G)` the fresh short-circuit edge. Let `F'` be a
`(G̃_v^{ab}).cycleMatroid`-independent (forest) fiber set of the multiplied splitting-off that
contains a copy `r` of `e₀` (`r.1 = e₀`, `r ∈ F'`), and let `pa, pb` be a `v—a` copy and a
`v—b` copy of `G̃` (necessarily distinct, since `a ≠ b`). Then the **reverse-swapped forest**
`(F' ∖ {r}) ∪ {pa, pb}`, obtained by trading the short-circuit copy `r` for the two `v`-edges,
is acyclic in the multiplied original `G̃ = (D−1)·G`:
`(G.mulTilde n).cycleMatroid.Indep (insert pa (insert pb (F' \ {r})))`.

This is the rerouting half of KT 4.2's per-forest acyclicity preservation, undoing the forward
`isAcyclicSet_splitOff_reroute` (the swap and the cycle-lift run in the opposite direction). The
proof lifts a hypothetical `G̃`-cycle through `pa, pb` to a `G̃_v^{ab}`-cycle inside `F'`
(substituting the 2-path through `v` by `r`), contradicting acyclicity; see the section
preamble. -/
lemma isAcyclicSet_mulTilde_of_splitOff_reroute {G : Graph α β} {v a b : α} {e₀ : β} {n : ℕ}
    (hab : a ≠ b) (ha : a ≠ v) (hb : b ≠ v) (haV : a ∈ V(G)) (hbV : b ∈ V(G))
    {F' : Set (β × Fin (bodyHingeMult n))} {pa pb r : β × Fin (bodyHingeMult n)}
    (hF' : ((G.splitOff v a b e₀).mulTilde n).cycleMatroid.Indep F')
    (hpa : (G.mulTilde n).IsLink pa v a) (hpb : (G.mulTilde n).IsLink pb v b)
    (hr : r.1 = e₀) (hrF' : r ∈ F') (he₀ : e₀ ∉ E(G)) :
    (G.mulTilde n).cycleMatroid.Indep (insert pa (insert pb (F' \ {r}))) := by
  classical
  -- Abbreviations: the original `K = G̃` and the splitting-off `Ksp = G̃_v^{ab}`.
  set K := G.mulTilde n with hK
  set Ksp := (G.splitOff v a b e₀).mulTilde n with hKsp
  rw [cycleMatroid_indep] at hF'
  -- `pa, pb` are not copies of the fresh edge (their `G`-edges live in `E(G)`, but `e₀` doesn't).
  have hpaE : pa.1 ∈ E(G) := by rw [hK, mulTilde_isLink] at hpa; exact hpa.edge_mem
  have hpbE : pb.1 ∈ E(G) := by rw [hK, mulTilde_isLink] at hpb; exact hpb.edge_mem
  have hpane₀ : pa.1 ≠ e₀ := fun h ↦ he₀ (h ▸ hpaE)
  have hpbne₀ : pb.1 ≠ e₀ := fun h ↦ he₀ (h ▸ hpbE)
  -- `pa, pb ∈ E(K)`.
  have hpaEK : pa ∈ E(K) := hpa.edge_mem
  have hpbEK : pb ∈ E(K) := hpb.edge_mem
  -- The fresh-fiber-avoiding core `F' ∖ {r}` lives in `E((G_v)̃)` (a forest holds ≤ 1 `e₀`-copy).
  have hsubsing : (F' ∩ edgeFiber e₀ n).Subsingleton :=
    fiber_inter_subsingleton_of_isAcyclicSet_splitOff hab ha hb haV hbV
      (by rw [cycleMatroid_indep]; exact hF')
  have hdiffdisj : Disjoint (F' \ {r}) (edgeFiber e₀ n) := by
    rw [Set.disjoint_left]
    rintro p ⟨hpF', hpr⟩ hpf
    have hrf : r ∈ F' ∩ edgeFiber e₀ n := ⟨hrF', by rw [edgeFiber, Set.mem_setOf_eq]; exact hr⟩
    have hpinter : p ∈ F' ∩ edgeFiber e₀ n := ⟨hpF', hpf⟩
    exact hpr (Set.mem_singleton_iff.mpr (hsubsing hpinter hrf))
  have hdiffGv : (F' \ {r}) ⊆ E((G.removeVertex v).mulTilde n) := by
    rw [← edgeSet_mulTilde_splitOff_diff_fiber n he₀]
    exact Set.subset_diff.mpr ⟨fun p hp ↦ hF'.1 hp.1, hdiffdisj⟩
  -- The swapped set lies in `E(K)`.
  have hSE : insert pa (insert pb (F' \ {r})) ⊆ E(K) := by
    refine Set.insert_subset hpaEK (Set.insert_subset hpbEK ?_)
    intro p hp
    exact (mulTilde_splitOff_deleteFiber_le n).edgeSet_mono
      (Set.mem_diff_of_mem (hF'.1 hp.1) (Set.disjoint_left.mp hdiffdisj hp))
  -- The core fibers avoid `v` (they live in `(G_v)̃`, which omits `v`).
  have hvnotinc : ∀ p ∈ F' \ {r}, ¬ K.Inc p v := by
    intro p hp hinc
    have hpE : p ∈ E((G.removeVertex v).mulTilde n) := hdiffGv hp
    rw [hK, mulTilde_inc] at hinc
    rw [mem_edgeSet_mulTilde] at hpE
    obtain ⟨x, y, hl⟩ := exists_isLink_of_mem_edgeSet hpE
    rw [removeVertex_isLink] at hl
    obtain ⟨hlink, hxv, hyv⟩ := hl
    rcases hinc with ⟨w, hw⟩
    rcases hlink.eq_and_eq_or_eq_and_eq hw with ⟨hxw, -⟩ | ⟨-, hyw⟩
    · exact hxv hxw
    · exact hyv hyw
  set S := insert pa (insert pb (F' \ {r})) with hS
  -- The only `v`-incident edges of `S` are `pa, pb`.
  have hSv : ∀ p ∈ S, K.Inc p v → p = pa ∨ p = pb := by
    intro p hp hinc
    rcases Set.mem_insert_iff.mp hp with h | h
    · exact Or.inl h
    · rcases Set.mem_insert_iff.mp h with h | h
      · exact Or.inr h
      · exact absurd hinc (hvnotinc p h)
  rw [cycleMatroid_indep, isAcyclicSet_iff]
  refine ⟨hSE, ?_⟩
  rw [restrict_isForest_iff']
  intro C hCS hCcyc
  -- Edges of `C` other than `pa, pb` lie in `F' ∖ {r}`.
  have hCedge : ∀ p ∈ C.edgeSet, p = pa ∨ p = pb ∨ p ∈ F' \ {r} := by
    intro p hp
    rcases Set.mem_insert_iff.mp (Set.mem_of_mem_of_subset hp hCS) with h | h
    · exact Or.inl h
    · rcases Set.mem_insert_iff.mp h with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  by_cases hpaC : pa ∈ C.edgeSet
  · -- `C` uses `pa`: it must also use `pb` (a cycle through `v` uses both `v`-edges).
    -- Rotate `C` so its first edge is `pa`.
    obtain ⟨m, -, hne, hfe⟩ := WList.exists_rotate_firstEdge_eq (w := C) (e := pa) hpaC
    have hDcyc : K.IsCyclicWalk (C.rotate m) := hCcyc.rotate m
    have hDE : (C.rotate m).edgeSet = C.edgeSet := WList.rotate_edgeSet C m
    obtain ⟨x, epa, w', heq⟩ := WList.nonempty_iff_exists_cons.mp (hne.rotate m)
    have hepa : epa = pa := by simp only [heq, WList.Nonempty.firstEdge_cons] at hfe; exact hfe
    rw [heq] at hDcyc hDE
    rw [hepa] at hDcyc hDE
    -- `D₀ = cons x pa w'` is closed, so `w'.last = x`.
    have hclosed : (WList.cons x pa w').IsClosed := hDcyc.isClosed
    rw [WList.cons_isClosed_iff] at hclosed
    -- The first link: `pa` joins `x` and `w'.first`; matched against `pa : v —a`.
    have hwalk : K.IsWalk (WList.cons x pa w') := hDcyc.isWalk
    rw [cons_isWalk_iff] at hwalk
    obtain ⟨hpalink, hw'walk⟩ := hwalk
    have hxw' : (v = x ∧ a = w'.first) ∨ (v = w'.first ∧ a = x) :=
      hpa.eq_and_eq_or_eq_and_eq hpalink
    -- Edge bookkeeping: `pa` is used once, so `pa ∉ E(w')`.
    have hnodup : (WList.cons x pa w').edge.Nodup := hDcyc.edge_nodup
    rw [WList.cons_edge, List.nodup_cons] at hnodup
    obtain ⟨hpanw', hw'nodup⟩ := hnodup
    -- The edges of `w'` lie in `C.edgeSet`.
    have hw'sub : w'.edgeSet ⊆ C.edgeSet := by
      intro p hp
      rw [← hDE, WList.cons_edgeSet]; exact Set.mem_insert_of_mem _ hp
    -- Uniform reorientation: a walk `wab` running `a → v` (reverse `w'` in the flipped case),
    -- with the same edge set, nodup, and avoiding `pa`.
    obtain ⟨wab, hwab_walk, hwab_first, hwab_last, hwab_edgeSet, hwab_nodup, hpa_nwab⟩ :
        ∃ wab : WList α (β × Fin (bodyHingeMult n)), K.IsWalk wab ∧ wab.first = a ∧
          wab.last = v ∧ wab.edgeSet = w'.edgeSet ∧ wab.edge.Nodup ∧ pa ∉ wab.edge := by
      rcases hxw' with ⟨hvx, haw'⟩ | ⟨hvw', hax⟩
      · exact ⟨w', hw'walk, haw'.symm, hvx ▸ hclosed.symm, rfl, hw'nodup, hpanw'⟩
      · refine ⟨w'.reverse, hw'walk.reverse,
          by rw [WList.reverse_first]; exact hclosed.symm.trans hax.symm,
          by rw [WList.reverse_last]; exact hvw'.symm, WList.reverse_edgeSet, ?_, ?_⟩
        · rw [WList.reverse_edge]; exact List.nodup_reverse.mpr hw'nodup
        · rw [WList.reverse_edge]; simpa using hpanw'
    -- `wab` is nonempty (`a ≠ v`), so its last edge `pb := wab.lastEdge` exists.
    have hwab_ne : wab.Nonempty := by
      by_contra hnil
      rw [WList.not_nonempty_iff] at hnil
      exact ha (hwab_first ▸ hwab_last ▸ hnil.first_eq_last)
    set qpb := hwab_ne.lastEdge with hqpb
    -- `qpb` is the last edge, incident to `wab.last = v`, and lies in `S`.
    have hqpb_mem : qpb ∈ wab.edge := hwab_ne.lastEdge_mem
    have hqpb_S : qpb ∈ S := hCS (hw'sub (hwab_edgeSet ▸ WList.mem_edgeSet_iff.mpr hqpb_mem))
    -- Decompose `wab = w₂.concat qpb v` with `w₂ = wab.dropLast` running `a → b`.
    set w₂ := wab.dropLast with hw₂
    have hwab_eq : w₂.concat qpb v = wab := by
      rw [hw₂, hqpb, ← hwab_last]; exact hwab_ne.concat_dropLast
    have hw₂_first : w₂.first = a := by rw [hw₂, WList.dropLast_first]; exact hwab_first
    -- The last link of `wab`: `qpb` joins `w₂.last` and `v`.
    have hconcat_walk : K.IsWalk (w₂.concat qpb v) := hwab_eq ▸ hwab_walk
    rw [concat_isWalk_iff] at hconcat_walk
    obtain ⟨hw₂_walk, hqpb_link⟩ := hconcat_walk
    -- `qpb` is `v`-incident, so `qpb = pa ∨ qpb = pb`; it is `≠ pa` (nodup), so `qpb = pb`.
    have hqpb_inc : K.Inc qpb v := hqpb_link.symm.inc_left
    have hqpb_eq : qpb = pb := by
      rcases hSv qpb hqpb_S hqpb_inc with h | h
      · exact absurd (hwab_edgeSet ▸ WList.mem_edgeSet_iff.mpr hqpb_mem)
          (h ▸ (fun hmem ↦ hpa_nwab (WList.mem_edgeSet_iff.mp (hwab_edgeSet ▸ hmem))))
      · exact h
    -- `w₂.last = b`: `qpb = pb` links `v, b` and `w₂.last, v`.
    have hw₂_last : w₂.last = b := by
      have := hqpb_eq ▸ hqpb_link
      rcases hpb.eq_and_eq_or_eq_and_eq this with ⟨hvw, hbv⟩ | ⟨hvv, hbw⟩
      · exact absurd hbv hb
      · exact hbw.symm
    -- `wab.edge = w₂.edge ++ [qpb]`, so `qpb ∉ w₂.edge` and `w₂.edge` is nodup.
    have hwab_edge_eq : wab.edge = w₂.edge ++ [qpb] := by
      rw [← hwab_eq, WList.concat_edge]
    rw [hwab_edge_eq, List.nodup_append] at hwab_nodup
    have hqpb_nw₂ : qpb ∉ w₂.edge :=
      fun h ↦ hwab_nodup.2.2 qpb h qpb (List.mem_singleton.mpr rfl) rfl
    have hw₂_nodup : w₂.edge.Nodup := hwab_nodup.1
    have hw₂_sub_wab : ∀ p ∈ w₂.edge, p ∈ wab.edge := fun p hp ↦ by
      rw [hwab_edge_eq]; exact List.mem_append_left _ hp
    -- `w₂`'s edges lie in `F' ∖ {r}` (they avoid `pa` and `pb`).
    have hw₂_edge_core : ∀ p ∈ w₂.edge, p ∈ F' \ {r} := by
      intro p hp
      have hpw' : p ∈ w'.edgeSet :=
        hwab_edgeSet ▸ WList.mem_edgeSet_iff.mpr (hw₂_sub_wab p hp)
      have hpne_pa : p ≠ pa := fun h ↦ hpa_nwab (h ▸ hw₂_sub_wab p hp)
      have hpne_pb : p ≠ pb := fun h ↦ hqpb_nw₂ (hqpb_eq ▸ h ▸ hp)
      rcases hCedge p (hw'sub hpw') with h | h | h
      · exact absurd h hpne_pa
      · exact absurd h hpne_pb
      · exact h
    -- The core edges lie in `E((G_v)̃)` and `E(F')` (subset of `F'`).
    have hw₂_edgeSet_Gv : w₂.edgeSet ⊆ E((G.removeVertex v).mulTilde n) := fun p hp ↦
      hdiffGv (hw₂_edge_core p (WList.mem_edgeSet_iff.mp hp))
    have hw₂_edge_F' : ∀ p ∈ w₂.edge, p ∈ F' := fun p hp ↦ (hw₂_edge_core p hp).1
    -- `w₂` is a walk of `(G_v)̃`, hence of `Ksp`.
    have hw₂_ne : w₂.Nonempty := by
      by_contra hnil
      rw [WList.not_nonempty_iff] at hnil
      exact hab (hw₂_first ▸ hw₂_last ▸ hnil.first_eq_last)
    have hle_Gv_K : (G.removeVertex v).mulTilde n ≤ K :=
      hK ▸ edgeMultiply_mono (removeVertex_le G v) _
    have hw₂_Gv : ((G.removeVertex v).mulTilde n).IsWalk w₂ :=
      hw₂_walk.isWalk_le_of_nonempty hle_Gv_K
        (by intro p hp; exact hw₂_edgeSet_Gv hp) hw₂_ne
    have hw₂_Ksp : Ksp.IsWalk w₂ := hw₂_Gv.of_le (mulTilde_removeVertex_le_splitOff n he₀)
    -- The short-circuit copy `r` joins `a, b` in `Ksp`.
    have hrlink : Ksp.IsLink r a b := by
      rw [hKsp, mulTilde_isLink, splitOff_isLink]
      exact Or.inr ⟨hr, ha, hb, haV, hbV, Or.inl ⟨rfl, rfl⟩⟩
    -- `r ∉ w₂.edge` (it lives in the fresh fiber, the core avoids it).
    have hr_nw₂ : r ∉ w₂.edge := fun h ↦ (hw₂_edge_core r h).2 rfl
    -- Build the closed `Ksp`-trail `T = w₂.concat r a`: `a → ⋯ → b —r— a`.
    set T := w₂.concat r a with hT
    have hT_walk : Ksp.IsWalk T := by
      rw [hT, concat_isWalk_iff]; exact ⟨hw₂_Ksp, hw₂_last ▸ hrlink.symm⟩
    have hT_tour : Ksp.IsTour T := by
      refine ⟨⟨hT_walk, ?_⟩, ?_, ?_⟩
      · rw [hT, WList.concat_edge, List.nodup_append]
        exact ⟨hw₂_nodup, List.nodup_singleton _,
          fun p hp q hq hpq ↦ hr_nw₂ (List.mem_singleton.mp hq ▸ hpq ▸ hp)⟩
      · rw [hT]; exact (WList.concat_nonempty w₂ r a)
      · rw [hT, WList.concat_isClosed_iff]; exact hw₂_first.symm
    have hT_edge_F' : T.edgeSet ⊆ F' := by
      rw [hT, WList.concat_edgeSet]
      exact Set.insert_subset hrF' (fun p hp ↦ hw₂_edge_F' p (WList.mem_edgeSet_iff.mp hp))
    -- A `Ksp`-tour contains a `Ksp`-cycle whose edges sit inside `F'`, contradicting `hF'`.
    obtain ⟨C', hC', hsub⟩ := hT_tour.exists_isCyclicWalk
    exact hF'.2 C' hC' (hsub.edge_subset.trans hT_edge_F')
  · -- `C` avoids `pa`. Then it also avoids `pb`, else it would use a single `v`-edge.
    have hpbC : pb ∉ C.edgeSet := by
      intro hpbC
      -- Rotate `C` so `pb` is its first edge; the other `v`-edge is forced to be `pa ∈ C`.
      obtain ⟨m, -, hne, hfe⟩ := WList.exists_rotate_firstEdge_eq (w := C) (e := pb) hpbC
      have hDcyc : K.IsCyclicWalk (C.rotate m) := hCcyc.rotate m
      have hDE : (C.rotate m).edgeSet = C.edgeSet := WList.rotate_edgeSet C m
      obtain ⟨x, epb, w', heq⟩ := WList.nonempty_iff_exists_cons.mp (hne.rotate m)
      have hepb : epb = pb := by simp only [heq, WList.Nonempty.firstEdge_cons] at hfe; exact hfe
      rw [heq] at hDcyc hDE
      rw [hepb] at hDcyc hDE
      have hclosed : (WList.cons x pb w').IsClosed := hDcyc.isClosed
      rw [WList.cons_isClosed_iff] at hclosed
      have hwalk : K.IsWalk (WList.cons x pb w') := hDcyc.isWalk
      rw [cons_isWalk_iff] at hwalk
      obtain ⟨hpblink, hw'walk⟩ := hwalk
      have hxw' : (v = x ∧ b = w'.first) ∨ (v = w'.first ∧ b = x) :=
        hpb.eq_and_eq_or_eq_and_eq hpblink
      have hnodup : (WList.cons x pb w').edge.Nodup := hDcyc.edge_nodup
      rw [WList.cons_edge, List.nodup_cons] at hnodup
      obtain ⟨hpbnw', hw'nodup⟩ := hnodup
      have hw'sub : w'.edgeSet ⊆ C.edgeSet := by
        intro p hp; rw [← hDE, WList.cons_edgeSet]; exact Set.mem_insert_of_mem _ hp
      -- Reorient to a walk `wba` running `b → v` (reverse in the flipped case).
      obtain ⟨wba, hwba_walk, hwba_first, hwba_last, hwba_edgeSet, hwba_nodup, hpb_nwba⟩ :
          ∃ wba : WList α (β × Fin (bodyHingeMult n)), K.IsWalk wba ∧ wba.first = b ∧
            wba.last = v ∧ wba.edgeSet = w'.edgeSet ∧ wba.edge.Nodup ∧ pb ∉ wba.edge := by
        rcases hxw' with ⟨hvx, hbw'⟩ | ⟨hvw', hbx⟩
        · exact ⟨w', hw'walk, hbw'.symm, hvx ▸ hclosed.symm, rfl, hw'nodup, hpbnw'⟩
        · refine ⟨w'.reverse, hw'walk.reverse,
            by rw [WList.reverse_first]; exact hclosed.symm.trans hbx.symm,
            by rw [WList.reverse_last]; exact hvw'.symm, WList.reverse_edgeSet, ?_, ?_⟩
          · rw [WList.reverse_edge]; exact List.nodup_reverse.mpr hw'nodup
          · rw [WList.reverse_edge]; simpa using hpbnw'
      -- `wba` is nonempty (`b ≠ v`); its last edge `qpa` is `v`-incident, distinct from `pb`.
      have hwba_ne : wba.Nonempty := by
        by_contra hnil
        rw [WList.not_nonempty_iff] at hnil
        exact hb (hwba_first ▸ hwba_last ▸ hnil.first_eq_last)
      set qpa := hwba_ne.lastEdge with hqpa
      have hqpa_mem : qpa ∈ wba.edge := hwba_ne.lastEdge_mem
      have hqpa_C : qpa ∈ C.edgeSet :=
        hw'sub (hwba_edgeSet ▸ WList.mem_edgeSet_iff.mpr hqpa_mem)
      -- Decompose `wba = (wba.dropLast).concat qpa v`; the last link makes `qpa` `v`-incident.
      have hwba_eq : wba.dropLast.concat qpa v = wba := by
        rw [hqpa, ← hwba_last]; exact hwba_ne.concat_dropLast
      have hconcat_walk : K.IsWalk (wba.dropLast.concat qpa v) := by rw [hwba_eq]; exact hwba_walk
      rw [concat_isWalk_iff] at hconcat_walk
      have hqpa_inc : K.Inc qpa v := hconcat_walk.2.symm.inc_left
      -- `qpa = pa ∨ qpa = pb`; it is `≠ pb` (nodup), so `qpa = pa ∈ C` — contradiction.
      have hqpa_ne_pb : qpa ≠ pb := fun h ↦ hpb_nwba (h ▸ hqpa_mem)
      have hqpa_eq : qpa = pa :=
        (hSv qpa (hCS hqpa_C) hqpa_inc).resolve_right hqpa_ne_pb
      exact hpaC (hqpa_eq ▸ hqpa_C)
    -- Both `v`-edges absent: `C` lives in `F' ∖ {r} ⊆ E((G_v)̃) ⊆ E(Ksp)`, lift the cycle.
    have hCcore : ∀ p ∈ C.edgeSet, p ∈ F' \ {r} := by
      intro p hp
      rcases hCedge p hp with h | h | h
      · exact absurd (h ▸ hp) hpaC
      · exact absurd (h ▸ hp) hpbC
      · exact h
    have hCGv : C.edgeSet ⊆ E((G.removeVertex v).mulTilde n) := fun p hp ↦ hdiffGv (hCcore p hp)
    -- `C` is a tour of `(G_v)̃`, hence a cyclic walk of `Ksp` inside `F'`.
    have hC_Gv_tour : ((G.removeVertex v).mulTilde n).IsTour C :=
      hCcyc.isTour.of_le_of_subset (hK ▸ edgeMultiply_mono (removeVertex_le G v) _)
        (fun p hp ↦ hCGv hp)
    have hC_Ksp_cyc : Ksp.IsCyclicWalk C :=
      ⟨hC_Gv_tour.of_le (mulTilde_removeVertex_le_splitOff n he₀), hCcyc.nodup⟩
    exact hF'.2 C hC_Ksp_cyc (fun p hp ↦ (hCcore p hp).1)

/-- **A split-off forest absorbs a `v`-edge copy as a pendant** (`lem:edge-splitting`, KT 4.2
forest core, the pendant-insert companion to `isAcyclicSet_mulTilde_of_splitOff_reroute`;
Katoh–Tanigawa 2011 Lemma 4.2 p.660). Let `F` be a `(G̃_v^{ab}).cycleMatroid`-independent
(forest) fiber set of the multiplied splitting-off that **avoids the fresh short-circuit fiber**
`ã̃b = edgeFiber e₀ n` (`Disjoint F (ã̃b)`, with `e₀ ∉ E(G)` fresh), and let `x` be a copy of a
`v`-incident `G`-edge linking `v` to a distinct vertex `w` (`(G̃).IsLink x v w`, `w ≠ v`). Then
`insert x F` is acyclic in the multiplied original `G̃ = (D−1)·G`:
`(G.mulTilde n).cycleMatroid.Indep (insert x F)`.

This is the brick KT 4.2's edge-splitting extension `splitOff_indep_extend_of_fiber_lt` runs on
for the forests that pick up a single `v`-edge (the `h' < i ≤ D−1` forests, which gain one
`eₐ`-copy, and `F_D`, which gains one `e_b`-copy). It composes the landed acyclicity transport
`isAcyclicSet_mulTilde_of_splitOff_of_disjoint` (a fresh-fiber-avoiding `G̃_v^{ab}`-forest is a
`G̃`-forest) with the redistribution kernel `acyclicSet_insert_vfiber_of_not_inc` (a `v`-avoiding
`G̃`-forest absorbs a `v`-edge as a pendant): the transported `F` avoids `v` (it lives in
`(G_v)̃`, which omits `v`), so the pendant insert applies. -/
lemma isAcyclicSet_mulTilde_insert_vfiber_of_splitOff {G : Graph α β} {v a b : α} {e₀ : β}
    {n : ℕ} (he₀ : e₀ ∉ E(G)) {F : Set (β × Fin (bodyHingeMult n))}
    {x : β × Fin (bodyHingeMult n)} {w : α}
    (hF : ((G.splitOff v a b e₀).mulTilde n).cycleMatroid.Indep F)
    (hdisj : Disjoint F (edgeFiber e₀ n)) (hxvw : (G.mulTilde n).IsLink x v w) (hwv : w ≠ v) :
    (G.mulTilde n).cycleMatroid.Indep (insert x F) := by
  -- Transport `F` down to `G̃`; it lives in `(G_v)̃`, so it avoids `v`.
  have hFK : (G.mulTilde n).cycleMatroid.Indep F :=
    isAcyclicSet_mulTilde_of_splitOff_of_disjoint hF hdisj
  have hFGv : F ⊆ E((G.removeVertex v).mulTilde n) := by
    rw [← edgeSet_mulTilde_splitOff_diff_fiber n he₀]
    rw [cycleMatroid_indep] at hF
    exact Set.subset_diff.mpr ⟨hF.1, hdisj⟩
  have hFv : ∀ p ∈ F, ¬ (G.mulTilde n).Inc p v := by
    intro p hp hinc
    have hpE : p ∈ E((G.removeVertex v).mulTilde n) := hFGv hp
    rw [mulTilde_inc] at hinc
    rw [mem_edgeSet_mulTilde] at hpE
    obtain ⟨y, z, hl⟩ := exists_isLink_of_mem_edgeSet hpE
    rw [removeVertex_isLink] at hl
    obtain ⟨hlink, hyv, hzv⟩ := hl
    obtain ⟨t, ht⟩ := hinc
    rcases hlink.eq_and_eq_or_eq_and_eq ht with ⟨hyw, -⟩ | ⟨-, hzw⟩
    · exact hyv hyw
    · exact hzv hzw
  exact acyclicSet_insert_vfiber_of_not_inc hFK hxvw hwv hFv

/-! ## The edge-splitting extension (`lem:edge-splitting`, KT Lemma 4.2)

The count-level assembly of the reverse forest surgery: Katoh–Tanigawa 2011 Lemma 4.2
(pp. 660–661). Where the forward surgery (`forest_surgery_count`, KT Lemma 4.1) reroutes a
forest packing of `M(G̃)` across the degree-2 vertex `v` *down* to one of the multiplied
splitting-off `M(G̃_v^{ab})`, this is the *up* direction: an independent set `I'` of
`M(G̃_v^{ab})` extends to an independent set `I` of `M(G̃)`, recovering the `v`-edges that
the splitting-off short-circuited away.

The construction partitions `I'` into `D = bodyBarDim n` edge-disjoint forests of
`G̃_v^{ab}` (`matroidMG_indep_iff_exists_forest_packing`, made disjoint by the `disjointed`
pattern), then trades each fresh short-circuit copy `r` of `ã̃b = edgeFiber e₀ n` for the two
`v`-edges it short-circuits — a `va`-copy `(eₐ, r.2)` and a `vb`-copy `(e_b, r.2)` — via the
reverse cycle-lift `isAcyclicSet_mulTilde_of_splitOff_reroute`; the one forest holding no
`ã̃b`-copy transports down verbatim (`isAcyclicSet_mulTilde_of_splitOff_of_disjoint`). Each
rerouted forest grows by exactly one (`−1` for `r`, `+2` for the recovered `v`-edges), the
pendant forest is unchanged, and the inserted copies are distinct across forests (distinct
`r.2`), so the union is again a `D`-forest packing — `M(G̃)`-independent.

This subsection ships the **full-fiber case** (KT 4.2(ii), `h' = D − 1`): when the whole
fresh fiber `ã̃b` lies in `I'`, all `D − 1` of its copies are recovered, giving the count
`|I| + 1 = |I'| + D` and the *survivor conjunct* `I ∖ (ẽₐ ∪ ẽ_b) = I' ∖ ã̃b` (the two sides
agree off the three special fibers). The survivor conjunct carries the 4.8(ii) minimality
transport (a base avoiding `ẽ` extends to a base still avoiding `ẽ`). -/

/-- **The edge-splitting extension, full-fiber case** (`lem:edge-splitting`, KT Lemma 4.2(ii);
Katoh–Tanigawa 2011 pp. 660–661). Let `v` be a degree-2 vertex of `G` with distinct
neighbours `a ≠ b` (`a, b ≠ v`), incident edges exactly `eₐ ≠ e_b` (`G.IsLink eₐ v a`,
`G.IsLink e_b v b`), and `e₀ ∉ E(G)` the fresh short-circuit edge, `D = bodyBarDim n ≥ 2`.
Given an `M(G̃_v^{ab})`-independent fiber set `I'` that **contains the whole fresh fiber**
`ã̃b = edgeFiber e₀ n` (`hsub`), there is an `M(G̃)`-independent set `I` with
`I.ncard + 1 = I'.ncard + bodyBarDim n` and the *survivor conjunct*
`I ∖ (ẽₐ ∪ ẽ_b) = I' ∖ ã̃b`.

This is KT 4.2's `h' = D − 1` arm: every one of the `D − 1` short-circuit copies of `I'` is
traded back for the `v`-edges it short-circuited. See the section preamble. -/
theorem splitOff_indep_extend_of_fiber_subset [DecidableEq β] [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} (hD : 2 ≤ bodyBarDim n) {v a b : α} {eₐ e_b e₀ : β}
    (hab : a ≠ b) (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b)
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (_hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b) (he₀ : e₀ ∉ E(G))
    {I' : Set (β × Fin (bodyHingeMult n))}
    (hI' : ((G.splitOff v a b e₀).matroidMG n).Indep I')
    (hsub : edgeFiber e₀ n ⊆ I') :
    ∃ I, (G.matroidMG n).Indep I ∧ I.ncard + 1 = I'.ncard + bodyBarDim n ∧
      I \ (edgeFiber eₐ n ∪ edgeFiber e_b n) = I' \ edgeFiber e₀ n := by
  classical
  haveI : Nonempty (Fin (bodyBarDim n)) := ⟨⟨0, lt_of_lt_of_le (by norm_num) hD⟩⟩
  have haV : a ∈ V(G) := hla.right_mem
  have hbV : b ∈ V(G) := hlb.right_mem
  -- `eₐ, e_b ≠ e₀` (they are edges of `G`, `e₀` is not).
  have heane₀ : eₐ ≠ e₀ := fun h ↦ he₀ (h ▸ hla.edge_mem)
  have hebne₀ : e_b ≠ e₀ := fun h ↦ he₀ (h ▸ hlb.edge_mem)
  -- Disjointify a forest packing of `I'` into a genuine partition.
  obtain ⟨hI'E, Fs₀, hcover₀, hindep₀⟩ :=
    (matroidMG_indep_iff_exists_forest_packing (G.splitOff v a b e₀) n).mp hI'
  set Ds := disjointed Fs₀ with hDs
  have hDscover : ⋃ i, Ds i = I' := by rw [hDs, iUnion_disjointed]; exact hcover₀
  have hDsindep : ∀ i, ((G.splitOff v a b e₀).mulTilde n).cycleMatroid.Indep (Ds i) :=
    fun i ↦ (hindep₀ i).subset (disjointed_le Fs₀ i)
  have hDsdisj : Pairwise (Function.onFun Disjoint Ds) := disjoint_disjointed Fs₀
  have hDssubI' : ∀ i, Ds i ⊆ I' := fun i ↦ hDscover ▸ Set.subset_iUnion Ds i
  -- Each forest holds at most one `e₀`-copy.
  have hsubsing : ∀ i, (Ds i ∩ edgeFiber e₀ n).Subsingleton := fun i ↦
    fiber_inter_subsingleton_of_isAcyclicSet_splitOff hab hav hbv haV hbV (hDsindep i)
  -- `S` = the forests holding an `e₀`-copy; for `i ∈ S`, `rOf i` is the unique such copy.
  set S : Finset (Fin (bodyBarDim n)) :=
    {i | (Ds i ∩ edgeFiber e₀ n).Nonempty} with hS
  have hSiff : ∀ i, i ∈ S ↔ (Ds i ∩ edgeFiber e₀ n).Nonempty := by
    intro i; simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
  -- A chosen `e₀`-copy per `S`-forest (else a placeholder).
  haveI : Nonempty (β × Fin (bodyHingeMult n)) := by
    obtain ⟨p, hp⟩ : (edgeFiber e₀ n).Nonempty := by
      rw [← Set.ncard_pos (Set.toFinite _), edgeFiber_ncard, bodyHingeMult]; omega
    exact ⟨p⟩
  set rOf : Fin (bodyBarDim n) → β × Fin (bodyHingeMult n) := fun i =>
    if h : (Ds i ∩ edgeFiber e₀ n).Nonempty then h.choose else Classical.arbitrary _ with hrOf
  have hrOf_mem : ∀ i ∈ S, rOf i ∈ Ds i ∩ edgeFiber e₀ n := by
    intro i hi
    have hne := (hSiff i).mp hi
    simp only [hrOf, dif_pos hne]; exact hne.choose_spec
  have hrOf1 : ∀ i ∈ S, (rOf i).1 = e₀ := fun i hi ↦ by
    have := (hrOf_mem i hi).2; rwa [edgeFiber, Set.mem_setOf_eq] at this
  -- The recovered `v`-edges: a `va`-copy and a `vb`-copy sharing `r`'s second coordinate.
  set paOf : Fin (bodyBarDim n) → β × Fin (bodyHingeMult n) := fun i => (eₐ, (rOf i).2) with hpaOf
  set pbOf : Fin (bodyBarDim n) → β × Fin (bodyHingeMult n) := fun i => (e_b, (rOf i).2) with hpbOf
  have hpaℓ : ∀ i, (G.mulTilde n).IsLink (paOf i) v a := fun i ↦ by
    rw [mulTilde_isLink, hpaOf]; exact hla
  have hpbℓ : ∀ i, (G.mulTilde n).IsLink (pbOf i) v b := fun i ↦ by
    rw [mulTilde_isLink, hpbOf]; exact hlb
  -- The rerouted family.
  set Fs : Fin (bodyBarDim n) → Set (β × Fin (bodyHingeMult n)) := fun i =>
    if i ∈ S then insert (paOf i) (insert (pbOf i) (Ds i \ {rOf i})) else Ds i with hFs
  -- `S.card = D − 1`: the whole `e₀`-fiber (`D − 1` copies) is partitioned one-per-`S`-forest.
  have hfibpart : ⋃ i, Ds i ∩ edgeFiber e₀ n = edgeFiber e₀ n := by
    rw [← Set.iUnion_inter, hDscover, Set.inter_eq_right.mpr hsub]
  have hScard : S.card = bodyBarDim n - 1 := by
    have hdisj_fib : Pairwise (Function.onFun Disjoint (fun i ↦ Ds i ∩ edgeFiber e₀ n)) :=
      fun i j hij ↦ (hDsdisj hij).mono Set.inter_subset_left Set.inter_subset_left
    have hsum : ∑ i, (Ds i ∩ edgeFiber e₀ n).ncard = bodyHingeMult n := by
      have hkey := Set.ncard_iUnion_of_finite (s := fun i ↦ Ds i ∩ edgeFiber e₀ n)
        (fun i ↦ Set.toFinite _) hdisj_fib
      rw [hfibpart, edgeFiber_ncard, finsum_eq_sum_of_fintype] at hkey
      exact hkey.symm
    -- Each term is `0` (off `S`) or `1` (on `S`).
    have hterm : ∀ i, (Ds i ∩ edgeFiber e₀ n).ncard = if i ∈ S then 1 else 0 := by
      intro i
      by_cases hi : i ∈ S
      · rw [if_pos hi]
        exact (Set.ncard_le_one_iff_subsingleton.mpr (hsubsing i)).antisymm
          (Set.Nonempty.ncard_pos (Set.toFinite _) ((hSiff i).mp hi))
      · have hemp : Ds i ∩ edgeFiber e₀ n = ∅ :=
          Set.not_nonempty_iff_eq_empty.mp (by rw [← hSiff i]; exact hi)
        rw [if_neg hi, hemp, Set.ncard_empty]
    simp only [hterm, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul,
      mul_one] at hsum
    rw [hsum, bodyHingeMult]
  -- `eₐ, e_b` are not edges of the splitting-off (they are `v`-incident in `G`), so no forest
  -- of `G̃_v^{ab}` holds a copy of either.
  have hnotin_of_vlink : ∀ {e w}, e ≠ e₀ → G.IsLink e v w → e ∉ E(G.splitOff v a b e₀) := by
    intro e w hne hl
    rw [edgeSet_splitOff]; rintro (⟨h, _⟩ | ⟨_, x, y, hl', hx, hy⟩)
    · exact hne h
    · rcases hl.eq_and_eq_or_eq_and_eq hl' with ⟨hvx, -⟩ | ⟨hvy, -⟩
      · exact hx hvx.symm
      · exact hy hvy.symm
  have hea_notin : eₐ ∉ E(G.splitOff v a b e₀) := hnotin_of_vlink heane₀ hla
  have heb_notin : e_b ∉ E(G.splitOff v a b e₀) := hnotin_of_vlink hebne₀ hlb
  -- No forest holds a copy of `eₐ` or `e_b`.
  have hDssubE : ∀ i, Ds i ⊆ E((G.splitOff v a b e₀).mulTilde n) :=
    fun i ↦ (hDsindep i).subset_ground
  have hpa_notDs : ∀ i j, paOf i ∉ Ds j := by
    intro i j hp
    have h1 := hDssubE j hp
    rw [mem_edgeSet_mulTilde, hpaOf] at h1; exact hea_notin h1
  have hpb_notDs : ∀ i j, pbOf i ∉ Ds j := by
    intro i j hp
    have h1 := hDssubE j hp
    rw [mem_edgeSet_mulTilde, hpbOf] at h1; exact heb_notin h1
  -- Each rerouted forest is acyclic in `G̃`.
  have hindep' : ∀ i, (G.mulTilde n).cycleMatroid.Indep (Fs i) := by
    intro i
    simp only [hFs]
    by_cases hi : i ∈ S
    · rw [if_pos hi]
      exact isAcyclicSet_mulTilde_of_splitOff_reroute hab hav hbv haV hbV (hDsindep i)
        (hpaℓ i) (hpbℓ i) (hrOf1 i hi) (hrOf_mem i hi).1 he₀
    · rw [if_neg hi]
      refine isAcyclicSet_mulTilde_of_splitOff_of_disjoint (hDsindep i) ?_
      rw [Set.disjoint_left]
      intro p hpD hpf
      exact ((hSiff i).not.mp hi) ⟨p, hpD, hpf⟩
  -- Distinctness: distinct `S`-forests carry distinct `e₀`-copies, hence distinct second
  -- coordinates, hence distinct recovered `v`-edges.
  have hrOf_ne : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → rOf i ≠ rOf j := by
    intro i hi j hj hij heq
    exact Set.disjoint_left.mp (hDsdisj hij) (hrOf_mem i hi).1 (heq ▸ (hrOf_mem j hj).1)
  have hrOf2_ne : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (rOf i).2 ≠ (rOf j).2 := by
    intro i hi j hj hij h2
    exact hrOf_ne i hi j hj hij (Prod.ext ((hrOf1 i hi).trans (hrOf1 j hj).symm) h2)
  -- `paOf i, pbOf i ∉ Ds i \ {rOf i}` (no `eₐ`/`e_b` copies in `Ds i`), and `paOf i ≠ pbOf i`.
  have hpa_ne_pb : ∀ i, paOf i ≠ pbOf i := fun i h ↦ heab (by
    have := (Prod.ext_iff.mp h).1; rwa [hpaOf, hpbOf] at this)
  -- A first-coordinate classifier for membership in `Fs k`: an `eₐ`-copy of `Fs k` is `paOf k`,
  -- an `e_b`-copy is `pbOf k`, and any other member lies in the core `Ds k`.
  have hFsmem : ∀ k p, p ∈ Fs k →
      (k ∈ S ∧ p = paOf k) ∨ (k ∈ S ∧ p = pbOf k) ∨ p ∈ Ds k := by
    intro k p hp
    simp only [hFs] at hp
    by_cases hk : k ∈ S
    · rw [if_pos hk] at hp
      rcases Set.mem_insert_iff.mp hp with rfl | hp'
      · exact Or.inl ⟨hk, rfl⟩
      rcases Set.mem_insert_iff.mp hp' with rfl | hp''
      · exact Or.inr (Or.inl ⟨hk, rfl⟩)
      · exact Or.inr (Or.inr hp''.1)
    · rw [if_neg hk] at hp; exact Or.inr (Or.inr hp)
  -- The core members of `Fs k` have first coordinate `≠ eₐ, e_b` (they live in `E(G̃_v^{ab})`).
  have hDs_fst : ∀ k p, p ∈ Ds k → p.1 ≠ eₐ ∧ p.1 ≠ e_b := by
    intro k p hp
    have hpE := hDssubE k hp
    rw [mem_edgeSet_mulTilde] at hpE
    exact ⟨fun h ↦ hea_notin (h ▸ hpE), fun h ↦ heb_notin (h ▸ hpE)⟩
  -- `paOf k` has first coord `eₐ`, `pbOf k` has `e_b`; core members have neither.
  have hpaOf_fst : ∀ k, (paOf k).1 = eₐ := fun k ↦ by rw [hpaOf]
  have hpbOf_fst : ∀ k, (pbOf k).1 = e_b := fun k ↦ by rw [hpbOf]
  -- Pairwise disjointness of the rerouted family.
  have hdisj' : Pairwise (Function.onFun Disjoint Fs) := by
    intro i j hij
    simp only [Function.onFun, Set.disjoint_left]
    intro p hpi hpj
    rcases hFsmem i p hpi with ⟨hiS, hpeqi⟩ | ⟨hiS, hpeqi⟩ | hpci <;>
      rcases hFsmem j p hpj with ⟨hjS, hpeqj⟩ | ⟨hjS, hpeqj⟩ | hpcj
    -- both `eₐ`-copies: `paOf i = paOf j`, forcing `(rOf i).2 = (rOf j).2`, contra `hrOf2_ne`.
    · exact hrOf2_ne i hiS j hjS hij (by
        have := (Prod.ext_iff.mp (hpeqi.symm.trans hpeqj)).2; simpa only [hpaOf] using this)
    · exact heab ((hpaOf_fst i) ▸ (hpbOf_fst j) ▸ hpeqi ▸ hpeqj ▸ rfl)
    · exact (hDs_fst j p hpcj).1 (hpeqi ▸ hpaOf_fst i)
    · exact heab ((hpaOf_fst j) ▸ (hpbOf_fst i) ▸ hpeqj ▸ hpeqi ▸ rfl)
    -- both `e_b`-copies: symmetric.
    · exact hrOf2_ne i hiS j hjS hij (by
        have := (Prod.ext_iff.mp (hpeqi.symm.trans hpeqj)).2; simpa only [hpbOf] using this)
    · exact (hDs_fst j p hpcj).2 (hpeqi ▸ hpbOf_fst i)
    · exact (hDs_fst i p hpci).1 (hpeqj ▸ hpaOf_fst j)
    · exact (hDs_fst i p hpci).2 (hpeqj ▸ hpbOf_fst j)
    -- both core: `p ∈ Ds i ∩ Ds j = ∅`.
    · exact Set.disjoint_left.mp (hDsdisj hij) hpci hpcj
  -- Set `I := ⋃ Fs i` and dispatch the three remaining conjuncts.
  refine ⟨⋃ i, Fs i, ?_, ?_, ?_⟩
  · -- `M(G̃)`-independence: `Fs` is a `D`-forest packing of `⋃ Fs i`.
    rw [matroidMG_indep_iff_exists_forest_packing]
    refine ⟨Set.iUnion_subset fun i ↦ (hindep' i).subset_ground, Fs, rfl, hindep'⟩
  · -- The count: every `S`-forest grows by one, the pendant is unchanged.
    -- For `i ∈ S`: `rOf i ∈ Ds i` is removed and `paOf i ≠ pbOf i ∉ Ds i` are added, net `+1`.
    have hshrink : ∀ i, (Fs i).ncard = (Ds i).ncard + (if i ∈ S then 1 else 0) := by
      intro i
      by_cases hi : i ∈ S
      · simp only [hFs, if_pos hi]
        have hpaD : paOf i ∉ insert (pbOf i) (Ds i \ {rOf i}) := by
          rw [Set.mem_insert_iff, not_or]
          exact ⟨hpa_ne_pb i, fun h ↦ hpa_notDs i i h.1⟩
        have hpbD : pbOf i ∉ Ds i \ {rOf i} := fun h ↦ hpb_notDs i i h.1
        rw [Set.ncard_insert_of_notMem hpaD (Set.toFinite _),
          Set.ncard_insert_of_notMem hpbD (Set.toFinite _),
          Set.ncard_diff_singleton_of_mem (hrOf_mem i hi).1]
        have hpos : 0 < (Ds i).ncard :=
          Set.Nonempty.ncard_pos (Set.toFinite _) ⟨rOf i, (hrOf_mem i hi).1⟩
        omega
      · simp only [hFs, if_neg hi, add_zero]
    have hsumFs : ∑ i, (Fs i).ncard = (⋃ i, Fs i).ncard := by
      rw [← finsum_eq_sum_of_fintype,
        ← Set.ncard_iUnion_of_finite (fun i ↦ Set.toFinite _) hdisj']
    have hsumDs : ∑ i, (Ds i).ncard = I'.ncard := by
      rw [← finsum_eq_sum_of_fintype,
        ← Set.ncard_iUnion_of_finite (fun i ↦ Set.toFinite _) hDsdisj, hDscover]
    have hsumeq : ∑ i, (Fs i).ncard = ∑ i, (Ds i).ncard + S.card := by
      rw [Finset.sum_congr rfl (fun i _ ↦ hshrink i), Finset.sum_add_distrib, Finset.sum_ite_mem,
        Finset.univ_inter, Finset.sum_const, smul_eq_mul, mul_one]
    rw [hsumFs, hsumDs] at hsumeq
    rw [hsumeq, hScard]; omega
  · -- The survivor conjunct: both sides equal the union of the cores `Ds i ∖ {rOf i}`.
    -- A sharper membership: off the three special fibers, `Fs i`-membership is `Ds i ∖ {rOf i}`.
    have hcoreFs : ∀ i p, p ∈ Fs i → p.1 ≠ e₀ → p.1 ≠ eₐ → p.1 ≠ e_b →
        p ∈ Ds i ∧ (i ∈ S → p ≠ rOf i) := by
      intro i p hp hp0 hpa hpb
      simp only [hFs] at hp
      by_cases hi : i ∈ S
      · rw [if_pos hi] at hp
        rcases Set.mem_insert_iff.mp hp with rfl | hp'
        · exact absurd (hpaOf_fst i) hpa
        rcases Set.mem_insert_iff.mp hp' with rfl | hp''
        · exact absurd (hpbOf_fst i) hpb
        · exact ⟨hp''.1, fun _ ↦ fun h ↦ hp''.2 (h ▸ rfl)⟩
      · rw [if_neg hi] at hp; exact ⟨hp, fun h ↦ absurd h hi⟩
    rw [← hDscover]
    apply Set.Subset.antisymm
    · rintro p ⟨hpU, hpab⟩
      rw [Set.mem_union, not_or] at hpab
      obtain ⟨hpa, hpb⟩ := hpab
      simp only [edgeFiber, Set.mem_setOf_eq] at hpa hpb
      rw [Set.mem_iUnion] at hpU
      obtain ⟨i, hpi⟩ := hpU
      -- `p` avoids `ẽₐ, ẽ_b`. If `p.1 = e₀`, `p = rOf i` is excluded by the sharper membership.
      by_cases hp0 : p.1 = e₀
      · exfalso
        -- `p ∈ Fs i`, `p.1 = e₀ ⟹ p ∈ Ds i` is an `e₀`-copy ⟹ `i ∈ S` and `p = rOf i`.
        have hpD : p ∈ Ds i := by
          rcases hFsmem i p hpi with ⟨hiS, rfl⟩ | ⟨hiS, rfl⟩ | hpD
          · exact absurd (hpaOf_fst i) hpa
          · exact absurd (hpbOf_fst i) hpb
          · exact hpD
        have hpf : p ∈ edgeFiber e₀ n := by rw [edgeFiber, Set.mem_setOf_eq]; exact hp0
        have hiS : i ∈ S := (hSiff i).mpr ⟨p, hpD, hpf⟩
        have hpeqr : p = rOf i := hsubsing i ⟨hpD, hpf⟩ (hrOf_mem i hiS)
        -- But `rOf i ∉ Fs i`: the reroute removes it (`≠ paOf i, pbOf i`, `∉ Ds i ∖ {rOf i}`).
        simp only [hFs, if_pos hiS] at hpi
        rw [hpeqr] at hpi
        rcases Set.mem_insert_iff.mp hpi with hpa' | hpi'
        · exact heane₀ (((hrOf1 i hiS).symm.trans (congrArg Prod.fst hpa')).trans
            (hpaOf_fst i)).symm
        rcases Set.mem_insert_iff.mp hpi' with hpb' | hpi''
        · exact hebne₀ (((hrOf1 i hiS).symm.trans (congrArg Prod.fst hpb')).trans
            (hpbOf_fst i)).symm
        · exact hpi''.2 rfl
      · refine ⟨Set.mem_iUnion.mpr ⟨i, (hcoreFs i p hpi hp0 hpa hpb).1⟩, ?_⟩
        rw [edgeFiber, Set.mem_setOf_eq]; exact hp0
    · rintro p ⟨hpU, hp0⟩
      rw [edgeFiber, Set.mem_setOf_eq] at hp0
      rw [Set.mem_iUnion] at hpU
      obtain ⟨i, hpi⟩ := hpU
      -- `p ∈ Ds i`, `p.1 ≠ e₀`. Its first coord is not `eₐ, e_b` (core lives in `E(G̃_v^{ab})`).
      obtain ⟨hpa, hpb⟩ := hDs_fst i p hpi
      refine ⟨Set.mem_iUnion.mpr ⟨i, ?_⟩, ?_⟩
      · -- `p ∈ Fs i`: if `i ∈ S`, `p ≠ rOf i` (else `p.1 = e₀`), so `p ∈ Ds i ∖ {rOf i} ⊆ Fs i`.
        simp only [hFs]
        by_cases hi : i ∈ S
        · rw [if_pos hi]
          refine Set.mem_insert_iff.mpr (Or.inr (Set.mem_insert_iff.mpr (Or.inr ⟨hpi, ?_⟩)))
          rw [Set.mem_singleton_iff]
          intro h; exact hp0 (h ▸ hrOf1 i hi)
        · rw [if_neg hi]; exact hpi
      · simp only [Set.mem_union, not_or, edgeFiber, Set.mem_setOf_eq]
        exact ⟨hpa, hpb⟩

/-- **The edge-splitting extension, partial-fiber case** (`lem:edge-splitting`, KT Lemma 4.2(i);
Katoh–Tanigawa 2011 pp. 660–661). Same degree-2 data as the full-fiber arm
`splitOff_indep_extend_of_fiber_subset`, but now the `M(G̃_v^{ab})`-independent set `I'` contains
**fewer than the whole** fresh fiber `ã̃b = edgeFiber e₀ n`
(`hlt : (I' ∩ ã̃b).ncard < bodyHingeMult n`, i.e. `h' < D − 1`). Then there is an
`M(G̃)`-independent set `I` with `I.ncard = I'.ncard + bodyBarDim n`,
the `e_b`-count `(I ∩ ẽ_b).ncard = (I' ∩ ã̃b).ncard + 1`, and the *survivor conjunct*
`I ∖ (ẽₐ ∪ ẽ_b) = I' ∖ ã̃b`.

This is KT 4.2's `h' < D − 1` arm. The `h'` short-circuit copies of `I'` are still traded for the
`v`-edges they short-circuit (the reverse cycle-lift, as in the full-fiber arm); additionally the
`D − 1 − h'` copy-free forests each absorb a fresh `eₐ`-pendant and one further forest an
`e_b`-pendant (`isAcyclicSet_mulTilde_insert_vfiber_of_splitOff`), so the packing gains `D` edges
with no `−1`
correction. The pendant copies draw their second coordinates from the index pool not already used by
the recovered `(eₐ, r.2)`/`(e_b, r.2)` copies, via an order iso onto the unused indices. See the
section preamble. -/
theorem splitOff_indep_extend_of_fiber_lt [DecidableEq β] [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} (hD : 2 ≤ bodyBarDim n) {v a b : α} {eₐ e_b e₀ : β}
    (hab : a ≠ b) (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b)
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (_hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b) (he₀ : e₀ ∉ E(G))
    {I' : Set (β × Fin (bodyHingeMult n))}
    (hI' : ((G.splitOff v a b e₀).matroidMG n).Indep I')
    (hlt : (I' ∩ edgeFiber e₀ n).ncard < bodyHingeMult n) :
    ∃ I, (G.matroidMG n).Indep I ∧ I.ncard = I'.ncard + bodyBarDim n ∧
      (I ∩ edgeFiber e_b n).ncard = (I' ∩ edgeFiber e₀ n).ncard + 1 ∧
      I \ (edgeFiber eₐ n ∪ edgeFiber e_b n) = I' \ edgeFiber e₀ n := by
  classical
  haveI : Nonempty (Fin (bodyBarDim n)) := ⟨⟨0, lt_of_lt_of_le (by norm_num) hD⟩⟩
  have haV : a ∈ V(G) := hla.right_mem
  have hbV : b ∈ V(G) := hlb.right_mem
  have heane₀ : eₐ ≠ e₀ := fun h ↦ he₀ (h ▸ hla.edge_mem)
  have hebne₀ : e_b ≠ e₀ := fun h ↦ he₀ (h ▸ hlb.edge_mem)
  -- Disjointify a forest packing of `I'` into a genuine partition (as in the full-fiber arm).
  obtain ⟨hI'E, Fs₀, hcover₀, hindep₀⟩ :=
    (matroidMG_indep_iff_exists_forest_packing (G.splitOff v a b e₀) n).mp hI'
  set Ds := disjointed Fs₀ with hDs
  have hDscover : ⋃ i, Ds i = I' := by rw [hDs, iUnion_disjointed]; exact hcover₀
  have hDsindep : ∀ i, ((G.splitOff v a b e₀).mulTilde n).cycleMatroid.Indep (Ds i) :=
    fun i ↦ (hindep₀ i).subset (disjointed_le Fs₀ i)
  have hDsdisj : Pairwise (Function.onFun Disjoint Ds) := disjoint_disjointed Fs₀
  have hsubsing : ∀ i, (Ds i ∩ edgeFiber e₀ n).Subsingleton := fun i ↦
    fiber_inter_subsingleton_of_isAcyclicSet_splitOff hab hav hbv haV hbV (hDsindep i)
  set S : Finset (Fin (bodyBarDim n)) :=
    {i | (Ds i ∩ edgeFiber e₀ n).Nonempty} with hS
  have hSiff : ∀ i, i ∈ S ↔ (Ds i ∩ edgeFiber e₀ n).Nonempty := by
    intro i; simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
  haveI : Nonempty (β × Fin (bodyHingeMult n)) := by
    obtain ⟨p, hp⟩ : (edgeFiber e₀ n).Nonempty := by
      rw [← Set.ncard_pos (Set.toFinite _), edgeFiber_ncard, bodyHingeMult]; omega
    exact ⟨p⟩
  set rOf : Fin (bodyBarDim n) → β × Fin (bodyHingeMult n) := fun i =>
    if h : (Ds i ∩ edgeFiber e₀ n).Nonempty then h.choose else Classical.arbitrary _ with hrOf
  have hrOf_mem : ∀ i ∈ S, rOf i ∈ Ds i ∩ edgeFiber e₀ n := by
    intro i hi
    have hne := (hSiff i).mp hi
    simp only [hrOf, dif_pos hne]; exact hne.choose_spec
  have hrOf1 : ∀ i ∈ S, (rOf i).1 = e₀ := fun i hi ↦ by
    have := (hrOf_mem i hi).2; rwa [edgeFiber, Set.mem_setOf_eq] at this
  -- `S.card = h'`: the `h'` copies of `I' ∩ ã̃b` are partitioned one-per-`S`-forest.
  set h' : ℕ := (I' ∩ edgeFiber e₀ n).ncard with hh'
  have hfibpart : ⋃ i, Ds i ∩ edgeFiber e₀ n = I' ∩ edgeFiber e₀ n := by
    rw [← Set.iUnion_inter, hDscover]
  have hScard : S.card = h' := by
    have hdisj_fib : Pairwise (Function.onFun Disjoint (fun i ↦ Ds i ∩ edgeFiber e₀ n)) :=
      fun i j hij ↦ (hDsdisj hij).mono Set.inter_subset_left Set.inter_subset_left
    have hsum : ∑ i, (Ds i ∩ edgeFiber e₀ n).ncard = h' := by
      have hkey := Set.ncard_iUnion_of_finite (s := fun i ↦ Ds i ∩ edgeFiber e₀ n)
        (fun i ↦ Set.toFinite _) hdisj_fib
      rw [hfibpart, finsum_eq_sum_of_fintype] at hkey
      exact hkey.symm
    have hterm : ∀ i, (Ds i ∩ edgeFiber e₀ n).ncard = if i ∈ S then 1 else 0 := by
      intro i
      by_cases hi : i ∈ S
      · rw [if_pos hi]
        exact (Set.ncard_le_one_iff_subsingleton.mpr (hsubsing i)).antisymm
          (Set.Nonempty.ncard_pos (Set.toFinite _) ((hSiff i).mp hi))
      · have hemp : Ds i ∩ edgeFiber e₀ n = ∅ :=
          Set.not_nonempty_iff_eq_empty.mp (by rw [← hSiff i]; exact hi)
        rw [if_neg hi, hemp, Set.ncard_empty]
    simp only [hterm, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul,
      mul_one] at hsum
    exact hsum
  -- The recovered `S`-forest `v`-edges, sharing each `r`'s second coordinate.
  set paOf : Fin (bodyBarDim n) → β × Fin (bodyHingeMult n) := fun i => (eₐ, (rOf i).2) with hpaOf
  set pbOf : Fin (bodyBarDim n) → β × Fin (bodyHingeMult n) := fun i => (e_b, (rOf i).2) with hpbOf
  have hpaℓ : ∀ i, (G.mulTilde n).IsLink (paOf i) v a := fun i ↦ by
    rw [mulTilde_isLink, hpaOf]; exact hla
  have hpbℓ : ∀ i, (G.mulTilde n).IsLink (pbOf i) v b := fun i ↦ by
    rw [mulTilde_isLink, hpbOf]; exact hlb
  -- The recovered second coordinates (one per `S`-forest), and the unused index pool.
  set Simg : Finset (Fin (bodyHingeMult n)) := S.image (fun i ↦ (rOf i).2) with hSimg
  have hrOf_ne : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → rOf i ≠ rOf j := by
    intro i hi j hj hij heq
    exact Set.disjoint_left.mp (hDsdisj hij) (hrOf_mem i hi).1 (heq ▸ (hrOf_mem j hj).1)
  have hrOf2_ne : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (rOf i).2 ≠ (rOf j).2 := by
    intro i hi j hj hij h2
    exact hrOf_ne i hi j hj hij (Prod.ext ((hrOf1 i hi).trans (hrOf1 j hj).symm) h2)
  have hSimg_card : Simg.card = h' := by
    rw [hSimg, Finset.card_image_of_injOn, hScard]
    intro i hi j hj h2
    by_contra hij
    exact hrOf2_ne i hi j hj hij h2
  set U : Finset (Fin (bodyHingeMult n)) := Finset.univ \ Simg with hU
  have hUcard : U.card = bodyHingeMult n - h' := by
    rw [hU, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
      hSimg_card]
  -- `h' < D − 1 = bodyHingeMult n`, so the pool `U` is nonempty.
  have hbHM : bodyHingeMult n = bodyBarDim n - 1 := by rw [bodyHingeMult]
  have hh'lt : h' < bodyHingeMult n := hlt
  have hUpos : 0 < U.card := by rw [hUcard]; omega
  have hUne : U.Nonempty := Finset.card_pos.mp hUpos
  -- Copy-free forests `T = Sᶜ`; `|T| = D − h' ≥ 1`. Designate `i_b := T.min'`.
  set T : Finset (Fin (bodyBarDim n)) := Sᶜ with hT
  have hTcard : T.card = bodyBarDim n - h' := by
    rw [hT, Finset.card_compl, Fintype.card_fin, hScard]
  have hTpos : 0 < T.card := by rw [hTcard]; rw [hbHM] at hh'lt; omega
  have hTne : T.Nonempty := Finset.card_pos.mp hTpos
  set i_b : Fin (bodyBarDim n) := T.min' hTne with hi_b
  have hi_bT : i_b ∈ T := T.min'_mem hTne
  have hi_bnotS : i_b ∉ S := by
    have := hi_bT; rwa [hT, Finset.mem_compl] at this
  -- The `eₐ`-pendant forests `Ta = T.erase i_b`; `|Ta| = D − 1 − h' = |U|`.
  set Ta : Finset (Fin (bodyBarDim n)) := T.erase i_b with hTa
  have hTaUcard : Ta.card = U.card := by
    rw [hTa, Finset.card_erase_of_mem hi_bT, hTcard, hUcard, hbHM]; omega
  -- An order iso `Ta ≃ U` assigning each `eₐ`-pendant forest a distinct unused index.
  set eTa : Fin Ta.card ≃o ↥Ta := Ta.orderIsoOfFin rfl with heTa
  set eU : Fin Ta.card ≃o ↥U := U.orderIsoOfFin hTaUcard.symm with heU
  set pcEquiv : ↥Ta ≃ ↥U := eTa.symm.trans eU |>.toEquiv with hpcEquiv
  set pc : Fin (bodyBarDim n) → Fin (bodyHingeMult n) := fun i =>
    if h : i ∈ Ta then ↑(pcEquiv ⟨i, h⟩) else U.min' hUne with hpc
  -- The `e_b`-pendant coordinate (a single unused index).
  set cb : Fin (bodyHingeMult n) := U.min' hUne with hcb
  have hcbU : cb ∈ U := U.min'_mem hUne
  -- `pc i ∈ U` for `i ∈ Ta`, and `pc` is injective on `Ta`.
  have hpcU : ∀ i ∈ Ta, pc i ∈ U := by
    intro i hi; simp only [hpc, dif_pos hi]; exact (pcEquiv ⟨i, hi⟩).2
  have hpc_inj : ∀ i ∈ Ta, ∀ j ∈ Ta, pc i = pc j → i = j := by
    intro i hi j hj heq
    simp only [hpc, dif_pos hi, dif_pos hj] at heq
    have : pcEquiv ⟨i, hi⟩ = pcEquiv ⟨j, hj⟩ := Subtype.ext heq
    have := pcEquiv.injective this
    exact congrArg Subtype.val this
  -- Membership in `U` excludes the recovered second coordinates `Simg`.
  have hU_notSimg : ∀ {c}, c ∈ U → c ∉ Simg := by
    intro c hc; rw [hU, Finset.mem_sdiff] at hc; exact hc.2
  -- The pendant `v`-edges link `v` to `a`/`b`.
  set qaOf : Fin (bodyBarDim n) → β × Fin (bodyHingeMult n) := fun i => (eₐ, pc i) with hqaOf
  set qb : β × Fin (bodyHingeMult n) := (e_b, cb) with hqb
  have hqaℓ : ∀ i, (G.mulTilde n).IsLink (qaOf i) v a := fun i ↦ by
    rw [mulTilde_isLink, hqaOf]; exact hla
  have hqbℓ : (G.mulTilde n).IsLink qb v b := by rw [mulTilde_isLink, hqb]; exact hlb
  -- The rerouted/pendant family.
  set Fs : Fin (bodyBarDim n) → Set (β × Fin (bodyHingeMult n)) := fun i =>
    if i ∈ S then insert (paOf i) (insert (pbOf i) (Ds i \ {rOf i}))
    else if i ∈ Ta then insert (qaOf i) (Ds i)
    else insert qb (Ds i) with hFs
  -- `eₐ, e_b` are not edges of the splitting-off (`v`-incident in `G`).
  have hnotin_of_vlink : ∀ {e w}, e ≠ e₀ → G.IsLink e v w → e ∉ E(G.splitOff v a b e₀) := by
    intro e w hne hl
    rw [edgeSet_splitOff]; rintro (⟨h, _⟩ | ⟨_, x, y, hl', hx, hy⟩)
    · exact hne h
    · rcases hl.eq_and_eq_or_eq_and_eq hl' with ⟨hvx, -⟩ | ⟨hvy, -⟩
      · exact hx hvx.symm
      · exact hy hvy.symm
  have hea_notin : eₐ ∉ E(G.splitOff v a b e₀) := hnotin_of_vlink heane₀ hla
  have heb_notin : e_b ∉ E(G.splitOff v a b e₀) := hnotin_of_vlink hebne₀ hlb
  have hDssubE : ∀ i, Ds i ⊆ E((G.splitOff v a b e₀).mulTilde n) :=
    fun i ↦ (hDsindep i).subset_ground
  -- No forest holds a copy of `eₐ` or `e_b` (its first coord is neither).
  have hDs_fst : ∀ k p, p ∈ Ds k → p.1 ≠ eₐ ∧ p.1 ≠ e_b := by
    intro k p hp
    have hpE := hDssubE k hp
    rw [mem_edgeSet_mulTilde] at hpE
    exact ⟨fun h ↦ hea_notin (h ▸ hpE), fun h ↦ heb_notin (h ▸ hpE)⟩
  have hpa_notDs : ∀ i j, paOf i ∉ Ds j := fun i j hp ↦ (hDs_fst j _ hp).1 (by rw [hpaOf])
  have hpb_notDs : ∀ i j, pbOf i ∉ Ds j := fun i j hp ↦ (hDs_fst j _ hp).2 (by rw [hpbOf])
  have hqa_notDs : ∀ i j, qaOf i ∉ Ds j := fun i j hp ↦ (hDs_fst j _ hp).1 (by rw [hqaOf])
  have hqb_notDs : ∀ j, qb ∉ Ds j := fun j hp ↦ (hDs_fst j _ hp).2 (by rw [hqb])
  -- The disjointness device: `Ds i` avoids `ã̃b` off `S`.
  have hDs_disj_fib : ∀ i ∉ S, Disjoint (Ds i) (edgeFiber e₀ n) := by
    intro i hi
    rw [Set.disjoint_left]
    intro p hpD hpf
    exact ((hSiff i).not.mp hi) ⟨p, hpD, hpf⟩
  -- Each forest of the family is acyclic in `G̃`.
  have hindep' : ∀ i, (G.mulTilde n).cycleMatroid.Indep (Fs i) := by
    intro i
    simp only [hFs]
    by_cases hi : i ∈ S
    · rw [if_pos hi]
      exact isAcyclicSet_mulTilde_of_splitOff_reroute hab hav hbv haV hbV (hDsindep i)
        (hpaℓ i) (hpbℓ i) (hrOf1 i hi) (hrOf_mem i hi).1 he₀
    · rw [if_neg hi]
      by_cases hia : i ∈ Ta
      · rw [if_pos hia]
        exact isAcyclicSet_mulTilde_insert_vfiber_of_splitOff he₀ (hDsindep i)
          (hDs_disj_fib i hi) (hqaℓ i) hav
      · rw [if_neg hia]
        exact isAcyclicSet_mulTilde_insert_vfiber_of_splitOff he₀ (hDsindep i)
          (hDs_disj_fib i hi) hqbℓ hbv
  -- First-coordinate classifier of `Fs k` membership.
  have hpaOf_fst : ∀ k, (paOf k).1 = eₐ := fun k ↦ by rw [hpaOf]
  have hpbOf_fst : ∀ k, (pbOf k).1 = e_b := fun k ↦ by rw [hpbOf]
  have hqaOf_fst : ∀ k, (qaOf k).1 = eₐ := fun k ↦ by rw [hqaOf]
  have hqb_fst : qb.1 = e_b := by rw [hqb]
  -- `i ∉ S ∧ i ∉ Ta ↔ i = i_b`.
  have hnotSnotTa : ∀ {i}, i ∉ S → i ∉ Ta → i = i_b := by
    intro i hiS hiTa
    by_contra hne
    exact hiTa (Finset.mem_erase.mpr ⟨hne, (hT ▸ Finset.mem_compl.mpr hiS)⟩)
  -- A member of `Fs k` is one of the special copies or a core member.
  have hFsmem : ∀ k p, p ∈ Fs k →
      (k ∈ S ∧ p = paOf k) ∨ (k ∈ S ∧ p = pbOf k) ∨ (k ∈ Ta ∧ p = qaOf k) ∨
        (k = i_b ∧ p = qb) ∨ p ∈ Ds k := by
    intro k p hp
    simp only [hFs] at hp
    by_cases hk : k ∈ S
    · rw [if_pos hk] at hp
      rcases Set.mem_insert_iff.mp hp with rfl | hp'
      · exact Or.inl ⟨hk, rfl⟩
      rcases Set.mem_insert_iff.mp hp' with rfl | hp''
      · exact Or.inr (Or.inl ⟨hk, rfl⟩)
      · exact Or.inr (Or.inr (Or.inr (Or.inr hp''.1)))
    · rw [if_neg hk] at hp
      by_cases hka : k ∈ Ta
      · rw [if_pos hka] at hp
        rcases Set.mem_insert_iff.mp hp with rfl | hp'
        · exact Or.inr (Or.inr (Or.inl ⟨hka, rfl⟩))
        · exact Or.inr (Or.inr (Or.inr (Or.inr hp')))
      · rw [if_neg hka] at hp
        rcases Set.mem_insert_iff.mp hp with rfl | hp'
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hnotSnotTa hk hka, rfl⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr hp')))
  -- The recovered second coords lie in `Simg`, the pendant second coords in `U`; `U ∩ Simg = ∅`.
  have hpaOf2 : ∀ i ∈ S, (paOf i).2 ∈ Simg := by
    intro i hi; rw [hpaOf]; exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  -- The `eₐ`-classifier: an `eₐ`-copy of `Fs k` is recovered (`S`, coord in `Simg`) or a pendant
  -- (`Ta`, coord in `U`).
  have hea_class : ∀ k p, p ∈ Fs k → p.1 = eₐ →
      (k ∈ S ∧ p.2 = (rOf k).2) ∨ (k ∈ Ta ∧ p.2 = pc k) := by
    intro k p hp hp1
    rcases hFsmem k p hp with ⟨hkS, rfl⟩ | ⟨hkS, rfl⟩ | ⟨hkTa, rfl⟩ | ⟨hkk, rfl⟩ | hc
    · exact Or.inl ⟨hkS, by rw [hpaOf]⟩
    · exact absurd ((hpbOf_fst k).symm.trans hp1) heab.symm
    · exact Or.inr ⟨hkTa, by rw [hqaOf]⟩
    · exact absurd (hqb_fst.symm.trans hp1) heab.symm
    · exact absurd hp1 (hDs_fst k p hc).1
  -- The `e_b`-classifier: an `e_b`-copy of `Fs k` is recovered (`S`, coord in `Simg`) or the
  -- unique `e_b`-pendant `qb` (`k = i_b`, coord `cb ∈ U`).
  have heb_class : ∀ k p, p ∈ Fs k → p.1 = e_b →
      (k ∈ S ∧ p.2 = (rOf k).2) ∨ (k = i_b ∧ p.2 = cb) := by
    intro k p hp hp1
    rcases hFsmem k p hp with ⟨hkS, rfl⟩ | ⟨hkS, rfl⟩ | ⟨hkTa, rfl⟩ | ⟨hkk, rfl⟩ | hc
    · exact absurd ((hpaOf_fst k).symm.trans hp1) heab
    · exact Or.inl ⟨hkS, by rw [hpbOf]⟩
    · exact absurd ((hqaOf_fst k).symm.trans hp1) heab
    · exact Or.inr ⟨hkk, by rw [hqb]⟩
    · exact absurd hp1 (hDs_fst k p hc).2
  -- A member of `Fs k` whose first coord is neither `eₐ` nor `e_b` lies in `Ds k`.
  have hcore_of_ne : ∀ k p, p ∈ Fs k → p.1 ≠ eₐ → p.1 ≠ e_b → p ∈ Ds k := by
    intro k p hp hpa hpb
    rcases hFsmem k p hp with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | hc
    · exact absurd (hpaOf_fst k) hpa
    · exact absurd (hpbOf_fst k) hpb
    · exact absurd (hqaOf_fst k) hpa
    · exact absurd hqb_fst hpb
    · exact hc
  -- Pairwise disjointness of the family.
  have hdisj' : Pairwise (Function.onFun Disjoint Fs) := by
    intro i j hij
    simp only [Function.onFun, Set.disjoint_left]
    intro p hpi hpj
    by_cases hp1a : p.1 = eₐ
    · -- `eₐ`-copy in both `Fs i` and `Fs j`: clashing coords across forests.
      rcases hea_class i p hpi hp1a with ⟨hiS, hi2⟩ | ⟨hiTa, hi2⟩ <;>
        rcases hea_class j p hpj hp1a with ⟨hjS, hj2⟩ | ⟨hjTa, hj2⟩
      · exact hrOf2_ne i hiS j hjS hij (hi2 ▸ hj2 ▸ rfl)
      · exact hU_notSimg (hi2 ▸ hj2 ▸ hpcU j hjTa) (hi2 ▸ hpaOf2 i hiS)
      · exact hU_notSimg (hj2 ▸ hi2 ▸ hpcU i hiTa) (hj2 ▸ hpaOf2 j hjS)
      · exact hij (hpc_inj i hiTa j hjTa (hi2 ▸ hj2 ▸ rfl))
    · by_cases hp1b : p.1 = e_b
      · -- `e_b`-copy in both: clashing coords across forests.
        rcases heb_class i p hpi hp1b with ⟨hiS, hi2⟩ | ⟨hii, hi2⟩ <;>
          rcases heb_class j p hpj hp1b with ⟨hjS, hj2⟩ | ⟨hjj, hj2⟩
        · exact hrOf2_ne i hiS j hjS hij (hi2 ▸ hj2 ▸ rfl)
        · exact hU_notSimg (hi2 ▸ hj2 ▸ hcbU) (hi2 ▸ hpaOf2 i hiS)
        · exact hU_notSimg (hj2 ▸ hi2 ▸ hcbU) (hj2 ▸ hpaOf2 j hjS)
        · exact hij (hii.trans hjj.symm)
      · -- core in both: `p ∈ Ds i ∩ Ds j = ∅`.
        exact Set.disjoint_left.mp (hDsdisj hij)
          (hcore_of_ne i p hpi hp1a hp1b) (hcore_of_ne j p hpj hp1a hp1b)
  have hpa_ne_pb : ∀ i, paOf i ≠ pbOf i := fun i h ↦ heab (by
    have := (Prod.ext_iff.mp h).1; rwa [hpaOf, hpbOf] at this)
  -- Every forest grows by exactly one.
  have hshrink : ∀ i, (Fs i).ncard = (Ds i).ncard + 1 := by
    intro i
    by_cases hi : i ∈ S
    · simp only [hFs, if_pos hi]
      have hpaD : paOf i ∉ insert (pbOf i) (Ds i \ {rOf i}) := by
        rw [Set.mem_insert_iff, not_or]
        exact ⟨hpa_ne_pb i, fun h ↦ hpa_notDs i i h.1⟩
      have hpbD : pbOf i ∉ Ds i \ {rOf i} := fun h ↦ hpb_notDs i i h.1
      rw [Set.ncard_insert_of_notMem hpaD (Set.toFinite _),
        Set.ncard_insert_of_notMem hpbD (Set.toFinite _),
        Set.ncard_diff_singleton_of_mem (hrOf_mem i hi).1]
      have hpos : 0 < (Ds i).ncard :=
        Set.Nonempty.ncard_pos (Set.toFinite _) ⟨rOf i, (hrOf_mem i hi).1⟩
      omega
    · simp only [hFs, if_neg hi]
      by_cases hia : i ∈ Ta
      · rw [if_pos hia, Set.ncard_insert_of_notMem (hqa_notDs i i) (Set.toFinite _)]
      · rw [if_neg hia, Set.ncard_insert_of_notMem (hqb_notDs i) (Set.toFinite _)]
  -- Sum bookkeeping: `∑ |Fs i| = ∑ |Ds i| + D = |I'| + D`.
  have hsumFs : ∑ i, (Fs i).ncard = (⋃ i, Fs i).ncard := by
    rw [← finsum_eq_sum_of_fintype,
      ← Set.ncard_iUnion_of_finite (fun i ↦ Set.toFinite _) hdisj']
  have hsumDs : ∑ i, (Ds i).ncard = I'.ncard := by
    rw [← finsum_eq_sum_of_fintype,
      ← Set.ncard_iUnion_of_finite (fun i ↦ Set.toFinite _) hDsdisj, hDscover]
  have hcount : (⋃ i, Fs i).ncard = I'.ncard + bodyBarDim n := by
    rw [← hsumFs, Finset.sum_congr rfl (fun i _ ↦ hshrink i), Finset.sum_add_distrib,
      hsumDs, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  refine ⟨⋃ i, Fs i, ?_, hcount, ?_, ?_⟩
  · -- `M(G̃)`-independence: `Fs` is a `D`-forest packing of `⋃ Fs i`.
    rw [matroidMG_indep_iff_exists_forest_packing]
    exact ⟨Set.iUnion_subset fun i ↦ (hindep' i).subset_ground, Fs, rfl, hindep'⟩
  · -- The `e_b`-count: the `e_b`-copies of `I` are the `h'` recovered `pbOf` (`i ∈ S`) plus the
    -- single pendant `qb`. These are disjoint (coords in `Simg` vs `U`), so the count is `h' + 1`.
    have hpbmem : ∀ i ∈ S, pbOf i ∈ (⋃ k, Fs k) := by
      intro i hi
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      simp only [hFs, if_pos hi]
      exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
    have hqbmem : qb ∈ (⋃ k, Fs k) := by
      refine Set.mem_iUnion.mpr ⟨i_b, ?_⟩
      have : i_b ∉ Ta := Finset.notMem_erase i_b T
      simp only [hFs, if_neg hi_bnotS, if_neg this]
      exact Set.mem_insert _ _
    -- Characterize `I ∩ ẽ_b` as the recovered copies plus the pendant.
    have hEb : (⋃ k, Fs k) ∩ edgeFiber e_b n =
        (pbOf '' (↑S : Set (Fin (bodyBarDim n)))) ∪ {qb} := by
      apply Set.Subset.antisymm
      · rintro p ⟨hpU, hpf⟩
        rw [edgeFiber, Set.mem_setOf_eq] at hpf
        rw [Set.mem_iUnion] at hpU
        obtain ⟨k, hpk⟩ := hpU
        rcases heb_class k p hpk hpf with ⟨hkS, hp2⟩ | ⟨hkk, hp2⟩
        · refine Or.inl ⟨k, hkS, Prod.ext ?_ ?_⟩
          · rw [hpbOf]; exact hpf.symm
          · rw [hpbOf]; exact hp2.symm
        · refine Or.inr (Prod.ext ?_ ?_)
          · rw [hqb]; exact hpf
          · rw [hqb]; exact hp2
      · rintro p (⟨i, hiS, rfl⟩ | rfl)
        · exact ⟨hpbmem i (by simpa using hiS), by rw [edgeFiber, Set.mem_setOf_eq, hpbOf]⟩
        · exact ⟨hqbmem, by rw [edgeFiber, Set.mem_setOf_eq, hqb]⟩
    rw [hEb]
    -- The two pieces are disjoint and have sizes `h'` and `1`.
    have hdisjpieces : Disjoint (pbOf '' (↑S : Set (Fin (bodyBarDim n)))) {qb} := by
      rw [Set.disjoint_right]
      rintro x rfl ⟨i, hiS, hpb⟩
      have hImg : (rOf i).2 ∈ Simg := Finset.mem_image.mpr ⟨i, by simpa using hiS, rfl⟩
      have hcoord : (rOf i).2 = cb := by
        have := (Prod.ext_iff.mp hpb).2; rw [hpbOf, hqb] at this; exact this
      exact hU_notSimg hcbU (hcoord ▸ hImg)
    rw [Set.ncard_union_eq hdisjpieces (Set.toFinite _) (Set.toFinite _), Set.ncard_singleton]
    have hpbinj : Set.InjOn pbOf (↑S : Set (Fin (bodyBarDim n))) := by
      intro i hi j hj heq
      by_contra hij
      refine hrOf2_ne i (by simpa using hi) j (by simpa using hj) hij ?_
      exact (Prod.ext_iff.mp heq).2
    rw [hpbinj.ncard_image, Set.ncard_coe_finset, hScard]
  · -- The survivor conjunct: both sides equal the union of the cores `Ds i` (`rOf i` removed for
    -- `i ∈ S`). The construction leaves `I` with no `e₀`-copy, matching `I' ∖ ẽ₀`.
    have hcoreFs : ∀ i p, p ∈ Fs i → p.1 ≠ e₀ → p.1 ≠ eₐ → p.1 ≠ e_b →
        p ∈ Ds i ∧ (i ∈ S → p ≠ rOf i) := by
      intro i p hp hp0 hpa hpb
      have hpD : p ∈ Ds i := hcore_of_ne i p hp hpa hpb
      refine ⟨hpD, fun hi h ↦ ?_⟩
      exact hp0 (h ▸ hrOf1 i hi)
    rw [← hDscover]
    apply Set.Subset.antisymm
    · rintro p ⟨hpU, hpab⟩
      rw [Set.mem_union, not_or] at hpab
      obtain ⟨hpa, hpb⟩ := hpab
      simp only [edgeFiber, Set.mem_setOf_eq] at hpa hpb
      rw [Set.mem_iUnion] at hpU
      obtain ⟨i, hpi⟩ := hpU
      by_cases hp0 : p.1 = e₀
      · -- `p ∈ Fs i` with `p.1 = e₀` would be an `e₀`-copy `rOf i` the reroute removed: impossible.
        exfalso
        have hpD : p ∈ Ds i := hcore_of_ne i p hpi hpa hpb
        have hpf : p ∈ edgeFiber e₀ n := by rw [edgeFiber, Set.mem_setOf_eq]; exact hp0
        have hiS : i ∈ S := (hSiff i).mpr ⟨p, hpD, hpf⟩
        have hpeqr : p = rOf i := hsubsing i ⟨hpD, hpf⟩ (hrOf_mem i hiS)
        -- but `rOf i ∉ Fs i`: the `S`-reroute removes it.
        simp only [hFs, if_pos hiS] at hpi
        rw [hpeqr] at hpi
        rcases Set.mem_insert_iff.mp hpi with hpa' | hpi'
        · exact heane₀ (((hrOf1 i hiS).symm.trans (congrArg Prod.fst hpa')).trans
            (hpaOf_fst i)).symm
        rcases Set.mem_insert_iff.mp hpi' with hpb' | hpi''
        · exact hebne₀ (((hrOf1 i hiS).symm.trans (congrArg Prod.fst hpb')).trans
            (hpbOf_fst i)).symm
        · exact hpi''.2 rfl
      · refine ⟨Set.mem_iUnion.mpr ⟨i, (hcoreFs i p hpi hp0 hpa hpb).1⟩, ?_⟩
        rw [edgeFiber, Set.mem_setOf_eq]; exact hp0
    · rintro p ⟨hpU, hp0⟩
      rw [edgeFiber, Set.mem_setOf_eq] at hp0
      rw [Set.mem_iUnion] at hpU
      obtain ⟨i, hpi⟩ := hpU
      obtain ⟨hpa, hpb⟩ := hDs_fst i p hpi
      refine ⟨Set.mem_iUnion.mpr ⟨i, ?_⟩, ?_⟩
      · -- `p ∈ Ds i` re-enters `Fs i`: for `i ∈ S` it survives the reroute (`p ≠ rOf i`); off `S`
        -- the family only inserts a fresh `v`-edge.
        simp only [hFs]
        by_cases hi : i ∈ S
        · rw [if_pos hi]
          refine Set.mem_insert_iff.mpr (Or.inr (Set.mem_insert_iff.mpr (Or.inr ⟨hpi, ?_⟩)))
          rw [Set.mem_singleton_iff]
          intro h; exact hp0 (h ▸ hrOf1 i hi)
        · rw [if_neg hi]
          by_cases hia : i ∈ Ta
          · rw [if_pos hia]; exact Set.mem_insert_of_mem _ hpi
          · rw [if_neg hia]; exact Set.mem_insert_of_mem _ hpi
      · simp only [Set.mem_union, not_or, edgeFiber, Set.mem_setOf_eq]
        exact ⟨hpa, hpb⟩

end Graph
