/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Induction.Contraction

/-!
# The combinatorial induction — forest surgery and Theorem 4.9 (`sec:molecular-induction`)

Phase 20 (molecular-conjecture program; see `notes/MolecularConjecture.md`). The capstone of the
`Induction/` subdirectory. On top of the contraction-minimality bridge (`Induction/Contraction`),
this file assembles Katoh–Tanigawa's Theorem 4.9 (Katoh–Tanigawa 2011 §3.4–3.5, §4):

* the **acyclicity transport** across the degree-2 short-circuit, the fiber-degree substrate, and
  the degree-2 reroute (`lem:forest-surgery-split`, surgery crux);
* circuits of the multiplied splitting-off meet the short-circuit, and splitting-off preserves
  minimal `0`-dof (`splitOff_isMinimalKDof`, `lem:reduction-step`);
* **Theorem 4.9** (`minimal_kdof_reduction`, `thm:minimal-kdof-reduction`): every minimal
  `0`-dof-graph reduces to the two-vertex double edge;
* the repacking descent (`exists_balanced_forest_packing`) and the **forest-surgery** count and
  assembly (`forest_surgery_count` / `forest_surgery_split`, `lem:forest-surgery-count`; KT
  Lemma 4.1).

This file's `minimal_kdof_reduction` is what the algebraic induction
(`Molecular/AlgebraicInduction/`, Phase 21+) realizes at the rigidity-matrix rank. See
`ROADMAP.md` §20 / `notes/Phase20.md` and the
`sec:molecular-induction` dep-graph.
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

/-! ## Circuits of the multiplied splitting-off meet the short-circuit (`lem:reduction-step`)

The conceptual heart of the splitting-off minimality transport (Katoh–Tanigawa 2011 Lemma
4.8(i), the claim labelled (4.10) in their proof). For a minimal `k`-dof-graph `G` with **no
proper rigid subgraph** and a degree-2 vertex `v` with neighbours `a, b` (`e₀ ∉ E(G)` fresh),
*every circuit `X` of the matroid `M(G̃_v^{ab})` of the splitting-off meets the fresh
short-circuit fiber* `ã̃b = edgeFiber e₀ n`.

This is KT's (4.10): if instead `X ∩ ã̃b = ∅`, then `X ⊆ E(G̃_v^{ab}) ∖ ã̃b = E(G̃_v) ⊆ E(G̃)`
(the ground-set bridge `edgeSet_mulTilde_splitOff_diff_fiber`), and since the two matroids
restrict identically to the surviving ground set `E(G̃_v)` (`matroidMG_restrict_mulTilde`
applied to `G̃_v ≤ G̃_v^{ab}` and to `G_v ≤ G`, both read off `Matroid.restrict_isCircuit_iff`),
`X` is also a circuit of `M(G̃)` — with `v ∉ V(X)`, since every fiber of `X` is a copy of a
`v`-avoiding edge of `G`. So `G[V(X)]` is a rigid subgraph (`circuit_induces_isRigidSubgraph`)
that is *proper* — it avoids `v`, and it spans at least two vertices because a circuit
contains an edge copy whose two `G`-ends are distinct (`[G.Loopless]`, the hypothesis the
`2 ≤ |V(H)|` conjunct of `IsProperRigidSubgraph` costs; the caller supplies it from
minimality via `loopless_of_isMinimalKDof`) — contradicting the no-proper-rigid hypothesis.

This is the matroidal claim the minimality transport `splitOff_isMinimalKDof` consumes: it is
exactly the statement that the surviving ground set `E(G̃_v)` is circuit-free, i.e. independent,
in `M(G̃_v^{ab})`. Katoh–Tanigawa use it to drive an iterated fundamental-circuit swap relocating
each `ã̃b` copy onto an `ẽ` copy; `splitOff_isMinimalKDof` instead consumes it directly, as the
fact that `E(G̃_v)` is a base of `M(G̃_v)` (so the swap induction is bypassed by a rank count).
Stated under no-proper-rigid plus looplessness — minimality of `G` itself is not needed
for (4.10); `[G.Loopless]` (which the caller derives from minimality) only feeds the
`2 ≤ |V(H)|` conjunct of the proper-rigid contradiction. -/
theorem circuit_splitOff_meets_fiber [DecidableEq β] [Finite α] [Finite β] {G : Graph α β}
    [G.Loopless] {n : ℕ} (hD : 1 ≤ bodyBarDim n) {v a b : α} {e₀ : β} (hvG : v ∈ V(G))
    (he₀ : e₀ ∉ E(G)) (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n)
    {X : Set (β × Fin (bodyHingeMult n))}
    (hX : ((G.splitOff v a b e₀).matroidMG n).IsCircuit X) :
    (X ∩ edgeFiber e₀ n).Nonempty := by
  classical
  rw [Set.nonempty_iff_ne_empty]
  intro hXe
  -- `X ⊆ E(G̃_v^{ab}) ∖ ã̃b = E(G̃_v)` (ground-set bridge).
  have hXground : X ⊆ E((G.splitOff v a b e₀).mulTilde n) := by
    have := hX.subset_ground; rwa [matroidMG, Matroid.restrict_ground_eq] at this
  have hXdisj : Disjoint X (edgeFiber e₀ n) := Set.disjoint_iff_inter_eq_empty.mpr hXe
  have hXsubGv : X ⊆ E((G.removeVertex v).mulTilde n) := by
    rw [← edgeSet_mulTilde_splitOff_diff_fiber n he₀]
    exact Set.subset_diff.mpr ⟨hXground, hXdisj⟩
  -- `G_v ≤ G_v^{ab}` at the graph level (every `v`-avoiding `G`-link survives, `e₀` being fresh).
  have hleGvSplit : G.removeVertex v ≤ G.splitOff v a b e₀ := by
    refine ⟨fun x hx => hx, fun p x y hp => ?_⟩
    rw [removeVertex_isLink] at hp
    obtain ⟨hlink, hxv, hyv⟩ := hp
    rw [splitOff_isLink]
    exact Or.inl ⟨fun h => he₀ (h ▸ hlink.edge_mem), hlink, hxv, hyv⟩
  have hleSplitMul : (G.removeVertex v).mulTilde n ≤ (G.splitOff v a b e₀).mulTilde n :=
    edgeMultiply_mono hleGvSplit _
  -- `M(G̃_v^{ab}) ↾ E(G̃_v) = M(G̃_v)`, so `X` is a circuit of `M(G̃_v)`.
  have hcircGv : ((G.removeVertex v).matroidMG n).IsCircuit X := by
    rw [← matroidMG_restrict_mulTilde hleGvSplit n,
      Matroid.restrict_isCircuit_iff hleSplitMul.edgeSet_mono]
    exact ⟨hX, hXsubGv⟩
  -- `M(G̃) ↾ E(G̃_v) = M(G̃_v)`, so `X` is a circuit of `M(G̃)`.
  have hleG : G.removeVertex v ≤ G := by
    rw [removeVertex]; exact deleteVerts_le
  have hcircG : (G.matroidMG n).IsCircuit X := by
    have hbridge := matroidMG_restrict_mulTilde hleG n
    rw [← hbridge] at hcircGv
    exact (Matroid.restrict_isCircuit_iff (edgeMultiply_mono hleG _).edgeSet_mono).mp hcircGv |>.1
  -- `G[V(X)]` is a rigid subgraph of `G`.
  have hrigid : (G.inducedSpan n X).IsRigidSubgraph G n :=
    circuit_induces_isRigidSubgraph hD hcircG
  -- `v ∉ V(X)`: every fiber of `X` is a copy of a `v`-avoiding edge.
  have hvnot : v ∉ V(G.inducedSpan n X) := by
    rw [vertexSet_inducedSpan, fiberSpan, mem_spanningVerts]
    rintro ⟨p, hpX, hinc⟩
    rw [mulTilde_inc] at hinc
    obtain ⟨w, hlw⟩ := hinc
    -- `p.1 ∈ E(G_v)`, so `p.1` carries a `v`-avoiding `G`-link, contradicting `G.IsLink p.1 v w`.
    have hpe : p.1 ∈ E(G.removeVertex v) := by
      have := hXsubGv hpX
      rwa [mem_edgeSet_mulTilde] at this
    obtain ⟨x, y, hlxy⟩ := exists_isLink_of_mem_edgeSet hpe
    rw [removeVertex_isLink] at hlxy
    obtain ⟨hlxyG, hxv, hyv⟩ := hlxy
    rcases hlw.left_eq_or_eq hlxyG with h | h
    · exact hxv h.symm
    · exact hyv h.symm
  -- A loopless circuit spans two distinct vertices; with `v ∉ V(X)`, `G[V(X)]` is *proper* rigid.
  have hV2 : 2 ≤ V(G.inducedSpan n X).ncard := by
    rw [vertexSet_inducedSpan, fiberSpan]
    obtain ⟨q, hq⟩ := hcircG.nonempty
    obtain ⟨x, y, hinc⟩ := exists_isLink_of_mem_edgeSet (hcircG.subset_ground hq)
    have hxy : x ≠ y := ((mulTilde_isLink G n).mp hinc).ne
    exact (Set.one_lt_ncard (Set.toFinite _)).mpr
      ⟨x, ⟨q, hq, hinc.inc_left⟩, y, ⟨q, hq, hinc.inc_right⟩, hxy⟩
  have hVsub : V(G.inducedSpan n X) ⊆ V(G) := by
    rw [vertexSet_inducedSpan, fiberSpan]
    exact (G.mulTilde n).spanningVerts_subset_vertexSet X
  exact hnp (G.inducedSpan n X)
    ⟨hrigid, hV2, hVsub.ssubset_of_ne (fun heq => hvnot (heq ▸ hvG))⟩

/-! ## Splitting-off preserves minimal `0`-dof (`lem:reduction-step`, splitting-off branch)

The full Katoh–Tanigawa 2011 Lemma 4.8(i): splitting off a degree-2 vertex `v` of a minimal
`0`-dof-graph `G` with **no proper rigid subgraph** again yields a minimal `0`-dof-graph
`G_v^{ab}`. This is the splitting-off branch of `lem:reduction-step` (the contraction branch is
`contraction_isMinimalKDof`); paired with `lem:reduction-measure` it drives the `|V|`-induction
of Theorem 4.9.

**A clean counting argument replaces KT's iterated swap.** Katoh–Tanigawa prove minimality by
an iterated fundamental-circuit swap (their (4.10) + the `i = 1,…,h` loop) that relocates each
short-circuit copy `(ab)ᵢ` onto an `eᵢ ∈ ẽ`. We bypass the induction with a rank/cardinality
comparison through the green `def = corank` bridge `isBase_ncard_add_deficiency_eq`:

* the **0-dof half** (`def(G̃_v^{ab}) = 0`) is `dof_tracking`'s two-sided bound squeezed against
  `def(G̃) = 0` and `def ≥ 0`;
* the surviving ground set `E(G̃_v) = E(G̃_v^{ab}) ∖ ã̃b` is a **base of `M(G̃_v)`**: it is
  independent in `M(G̃_v^{ab})` (`circuit_splitOff_meets_fiber` — KT's (4.10) — says no circuit
  avoids `ã̃b`, i.e. `E(G̃_v)` is circuit-free), and restriction descends it to `M(G̃_v)`, where
  it is the whole ground set;
* KT 4.7 (`def(G̃_v) > 0`): `G_v ≤ G` is a proper subgraph on `|V(G)| − 1 ≥ 2` vertices (the
  `hV3 : 3 ≤ |V(G)|` hypothesis — the splitting branch's standing regime, and genuinely needed:
  at `|V(G)| = 2` the double edge splits to a one-vertex loop graph whose empty base misses the
  fresh fiber), so under no-proper-rigid it is not `0`-dof, hence `def(G̃_v) > 0`;
* finally, any base `B'` of `M(G̃_v^{ab})` avoiding a fiber `ẽ` (`e ∈ E(G_v^{ab})`) has
  `|B'| ≤ |E(G̃_v)|` (case `e = e₀`: `B' ⊆ E(G̃_v)`; case `e ≠ e₀`: `B'` splits into `B' ∩ ã̃b`
  of size `≤ D − 1` and `B' ∩ E(G̃_v) ⊆ E(G̃_v) ∖ ẽ` of size `≤ |E(G̃_v)| − (D − 1)`). Via
  `isBase_ncard_add_deficiency_eq` on the two bases this forces `def(G̃_v) ≤ def(G̃_v^{ab}) = 0`,
  contradicting `def(G̃_v) > 0`. So every base meets every fiber: `G_v^{ab}` is minimal. -/
theorem splitOff_isMinimalKDof [DecidableEq β] [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hD : 2 ≤ bodyBarDim n) (hV3 : 3 ≤ V(G).ncard) {v a b : α} {e₀ eₐ e_b : β}
    (hav : a ≠ v) (hbv : b ≠ v) (haV : a ∈ V(G)) (hbV : b ∈ V(G)) (hvG : v ∈ V(G))
    (heab : eₐ ≠ e_b) (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b) (he₀ : e₀ ∉ E(G))
    (hG : G.IsMinimalKDof n 0) (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) :
    (G.splitOff v a b e₀).IsMinimalKDof n 0 := by
  classical
  haveI : G.Loopless := loopless_of_isMinimalKDof hG
  have hD1 : 1 ≤ bodyBarDim n := le_trans (by norm_num) hD
  set G' := G.splitOff v a b e₀ with hG'def
  set Gv := G.removeVertex v with hGvdef
  -- Vertex sets: `V(G') = V(Gv) = V(G) ∖ {v}`, nonempty (it contains `a`) and of size `≥ 2`.
  have hVeq : V(G') = V(G) \ {v} := vertexSet_splitOff G v a b e₀
  have hVveq : V(Gv) = V(G) \ {v} := vertexSet_removeVertex G v
  have hVne : V(G').Nonempty := by rw [hVeq]; exact ⟨a, haV, by simpa using hav⟩
  have hVvne : V(Gv).Nonempty := by rw [hVveq]; exact ⟨a, haV, by simpa using hav⟩
  have hVv2 : 2 ≤ V(Gv).ncard := by
    rw [hVveq, Set.ncard_diff (by simpa using hvG) (Set.toFinite _), Set.ncard_singleton]
    omega
  -- `Gv ≤ G` a proper subgraph (`v ∈ V(G)` is dropped); under no-proper-rigid, `def(G̃v) > 0`.
  have hleGvG : Gv ≤ G := by rw [hGvdef, removeVertex]; exact deleteVerts_le
  have hdefGv_pos : 0 < Gv.deficiency n := by
    rcases lt_or_eq_of_le (Gv.deficiency_nonneg n hVvne) with h | h
    · exact h
    · exfalso
      refine hnp Gv ⟨⟨hleGvG, h.symm⟩, hVv2, ?_⟩
      rw [hVveq]; exact Set.diff_singleton_ssubset.mpr hvG
  -- 0-dof half: `def(G̃') = 0` from `dof_tracking` squeezed against `def(G̃) = 0` and `def ≥ 0`.
  have hdofG : G.deficiency n = 0 := hG.1
  have htrack := dof_tracking hD hav hbv heab hla hlb hdeg2 he₀
  have hdefG'_zero : G'.deficiency n = 0 := by
    have h1 : G'.deficiency n ≤ G.deficiency n := htrack.2.1
    have h2 : 0 ≤ G'.deficiency n := G'.deficiency_nonneg n hVne
    rw [hdofG] at h1; omega
  refine ⟨hdefG'_zero, fun B' hB' e heG' => ?_⟩
  -- Prove the fiber-meeting by contradiction: assume `B' ∩ ẽ = ∅`.
  rw [Set.nonempty_iff_ne_empty]
  intro hBe
  -- `E(G̃') = ã̃b ⊔ E(G̃v)`: the fresh fiber and the surviving fibers.
  have hsplit_ground : E(G'.mulTilde n) \ edgeFiber e₀ n = E(Gv.mulTilde n) :=
    edgeSet_mulTilde_splitOff_diff_fiber n he₀
  have hfiberGround : edgeFiber e₀ n ⊆ E(G'.mulTilde n) :=
    edgeFiber_subset_edgeSet_mulTilde_splitOff n hav hbv haV hbV
  -- `B' ⊆ E(G̃')`, `|B'| = D(|V'|−1)` since `def(G̃') = 0`.
  have hB'ground : B' ⊆ E(G'.mulTilde n) := hB'.subset_ground
  have hB'card : (B'.ncard : ℤ) + 0 = bodyBarDim n * ((V(G').ncard : ℤ) - 1) := by
    have := G'.isBase_ncard_add_deficiency_eq n hD1 hVne hB'
    rwa [hdefG'_zero] at this
  -- `E(G̃v)` is a base of `M(G̃v)`: it is circuit-free in `M(G̃')` (KT (4.10)), hence
  -- independent there, and restriction descends it to the whole ground of `M(G̃v)`.
  have hGv_indep_in_G' : (G'.matroidMG n).Indep (E(Gv.mulTilde n)) := by
    rw [Matroid.indep_iff_forall_subset_not_isCircuit']
    refine ⟨fun C hCsub hC => ?_, ?_⟩
    · -- A circuit `C ⊆ E(G̃v)` avoids `ã̃b`, contradicting `circuit_splitOff_meets_fiber`.
      obtain ⟨p, hpC, hpfib⟩ := circuit_splitOff_meets_fiber hD1 hvG he₀ hnp hC
      have hpGv : p ∈ E(Gv.mulTilde n) := hCsub hpC
      rw [← hsplit_ground] at hpGv
      exact hpGv.2 hpfib
    · rw [matroidMG, Matroid.restrict_ground_eq, ← hsplit_ground]; exact Set.diff_subset
  have hleGvG' : Gv ≤ G' := by
    rw [hGvdef, hG'def]
    refine ⟨fun x hx => hx, fun p x y hp => ?_⟩
    rw [removeVertex_isLink] at hp
    obtain ⟨hlink, hxv, hyv⟩ := hp
    rw [splitOff_isLink]
    exact Or.inl ⟨fun h => he₀ (h ▸ hlink.edge_mem), hlink, hxv, hyv⟩
  have hGv_base : (Gv.matroidMG n).IsBase (E(Gv.mulTilde n)) := by
    have hg : (Gv.matroidMG n).E = E(Gv.mulTilde n) := by
      rw [matroidMG, Matroid.restrict_ground_eq]
    rw [← hg, ← Matroid.ground_indep_iff_isBase, hg, ← matroidMG_restrict_mulTilde hleGvG' n,
      Matroid.restrict_indep_iff]
    exact ⟨hGv_indep_in_G', subset_rfl⟩
  -- `|E(G̃v)| + def(G̃v) = D(|V v|−1) = D(|V'|−1)` (same vertex set `V(G)∖{v}`).
  have hEGvcard : (E(Gv.mulTilde n).ncard : ℤ) + Gv.deficiency n
      = bodyBarDim n * ((V(G').ncard : ℤ) - 1) := by
    have hb := Gv.isBase_ncard_add_deficiency_eq n hD1 hVvne hGv_base
    rw [hVveq] at hb; rw [hVeq]; exact hb
  -- Core cardinality bound: any base `B'` avoiding the fiber `ẽ` has `|B'| ≤ |E(G̃v)|`.
  have hB'le : B'.ncard ≤ E(Gv.mulTilde n).ncard := by
    by_cases he : e = e₀
    · -- `e = e₀`: `B'` avoids `ã̃b`, so `B' ⊆ E(G̃v)`.
      subst he
      have hB'sub : B' ⊆ E(Gv.mulTilde n) := by
        rw [← hsplit_ground]
        refine Set.subset_diff.mpr ⟨hB'ground, Set.disjoint_left.mpr fun p hpB' hpfib => ?_⟩
        exact absurd (Set.eq_empty_iff_forall_notMem.mp hBe p ⟨hpB', hpfib⟩) id
      exact Set.ncard_le_ncard hB'sub (Set.toFinite _)
    · -- `e ≠ e₀`: split `B'` into `B' ∩ ã̃b` (≤ D−1) and `B' ∩ E(G̃v) ⊆ E(G̃v) ∖ ẽ`.
      have heGv : edgeFiber e n ⊆ E(Gv.mulTilde n) := by
        intro p hp
        rw [edgeFiber, Set.mem_setOf_eq] at hp
        have heE : e ∈ E(Gv) := by
          have hmem : e ∈ E(G') := heG'
          rw [hG'def, edgeSet_splitOff] at hmem
          rcases hmem with ⟨rfl, _⟩ | ⟨_, x, y, hl, hx, hy⟩
          · exact absurd rfl he
          · have hlGv : Gv.IsLink e x y := by rw [hGvdef, removeVertex_isLink]; exact ⟨hl, hx, hy⟩
            exact hlGv.edge_mem
        rw [mem_edgeSet_mulTilde, hp]; exact heE
      -- Decompose `B' = (B' ∩ ã̃b) ∪ (B' ∩ E(G̃v))` since `B' ⊆ ã̃b ∪ E(G̃v) = E(G̃')`.
      have hcover : B' ⊆ edgeFiber e₀ n ∪ E(Gv.mulTilde n) := by
        intro p hpB'
        rcases em (p ∈ edgeFiber e₀ n) with hpf | hpf
        · exact Or.inl hpf
        · exact Or.inr (hsplit_ground ▸ ⟨hB'ground hpB', hpf⟩)
      have h1 : (B' ∩ edgeFiber e₀ n).ncard ≤ bodyHingeMult n := by
        calc (B' ∩ edgeFiber e₀ n).ncard ≤ (edgeFiber e₀ n).ncard :=
              Set.ncard_le_ncard Set.inter_subset_right (Set.toFinite _)
          _ = bodyHingeMult n := edgeFiber_ncard e₀ n
      have h2 : (B' ∩ E(Gv.mulTilde n)).ncard ≤ E(Gv.mulTilde n).ncard - bodyHingeMult n := by
        have hsub : B' ∩ E(Gv.mulTilde n) ⊆ E(Gv.mulTilde n) \ edgeFiber e n := by
          refine Set.subset_diff.mpr ⟨Set.inter_subset_right, Set.disjoint_left.mpr ?_⟩
          intro p hpB' hpfib
          exact absurd (Set.eq_empty_iff_forall_notMem.mp hBe p ⟨hpB'.1, hpfib⟩) id
        calc (B' ∩ E(Gv.mulTilde n)).ncard ≤ (E(Gv.mulTilde n) \ edgeFiber e n).ncard :=
              Set.ncard_le_ncard hsub (Set.toFinite _)
          _ = E(Gv.mulTilde n).ncard - (edgeFiber e n).ncard :=
              Set.ncard_diff heGv (Set.toFinite _)
          _ = E(Gv.mulTilde n).ncard - bodyHingeMult n := by rw [edgeFiber_ncard]
      have hcoverle : B'.ncard ≤ (B' ∩ edgeFiber e₀ n).ncard + (B' ∩ E(Gv.mulTilde n)).ncard := by
        calc B'.ncard ≤ ((B' ∩ edgeFiber e₀ n) ∪ (B' ∩ E(Gv.mulTilde n))).ncard := by
              refine Set.ncard_le_ncard ?_ (Set.toFinite _)
              rw [← Set.inter_union_distrib_left]
              exact Set.subset_inter (subset_refl _) hcover
          _ ≤ (B' ∩ edgeFiber e₀ n).ncard + (B' ∩ E(Gv.mulTilde n)).ncard :=
              Set.ncard_union_le _ _
      -- `|E(G̃v)| ≥ D − 1` (it contains `ẽ` of size `D − 1`), so the subtraction is exact.
      have hge : bodyHingeMult n ≤ E(Gv.mulTilde n).ncard := by
        calc bodyHingeMult n = (edgeFiber e n).ncard := (edgeFiber_ncard e n).symm
          _ ≤ E(Gv.mulTilde n).ncard := Set.ncard_le_ncard heGv (Set.toFinite _)
      omega
  -- Assemble: `D(|V'|−1) = |B'| ≤ |E(G̃v)| = D(|V'|−1) − def(G̃v)`, so `def(G̃v) ≤ 0` — contra.
  have hle : (B'.ncard : ℤ) ≤ (E(Gv.mulTilde n).ncard : ℤ) := by exact_mod_cast hB'le
  linarith [hB'card, hEGvcard, hle, hdefGv_pos]

/-! ## Theorem 4.9: reduction of minimal `0`-dof-graphs (`thm:minimal-kdof-reduction`)

The capstone of the combinatorial induction (Katoh–Tanigawa 2011 Theorem 4.9). Every
minimal `0`-dof-graph with `2 ≤ |V|` reduces to the two-vertex double edge by a sequence
of two operations — splitting off a reducible degree-2 vertex, and contracting a proper
rigid subgraph — each of which (`lem:reduction-step`) carries a minimal `0`-dof-graph to a
strictly smaller one (`lem:reduction-measure`). Phrased as the well-founded induction
principle this dichotomy + measure drives: a motive closed under the two-vertex base case
and the two reductions holds of every minimal `0`-dof-graph.

The splitting-off step needs the degree-2 vertex's two incident edges as explicit data
(the `eₐ`/`e_b` encoding `splitOff_isMinimalKDof` consumes). The bridge
`exists_splitOff_data_of_degree_eq_two` extracts it: a degree-2 vertex of a `0`-dof-graph
has its two incidences carried by two *distinct nonloop* edges (the `0`-dof
two-edge-connectivity rules out a single loop, which would also give degree 2), whose far
endpoints supply `a`, `b`. -/

/-- **A degree-2 vertex of a `0`-dof-graph carries splitting-off data**
(`thm:minimal-kdof-reduction`, the degree↔edges bridge for the splitting-off step). For
`D = bodyBarDim n ≥ 1`, a `0`-dof-graph
`G`, and a vertex `v` of multigraph degree exactly `2` with a distinct companion `b₀ ∈ V(G)`
(needed only to invoke two-edge-connectivity), the two incidences at `v` are carried by two
*distinct nonloop* edges `eₐ ≠ e_b`: the count `degree v = 2·#loops + #nonloops` together with
`#nonloops ≥ 2` (two-edge-connectivity, `two_le_crossingEdges_of_isKDof_zero`, via the singleton
cut `{v}` whose crossing edges are the nonloops at `v`) forces `#loops = 0` and `#nonloops = 2`.
The two nonloop edges' far endpoints `a, b ≠ v` lie in `V(G)`, and every `v`-incident edge is one
of them (the closure `hdeg2`). This is exactly the `eₐ`/`e_b`/`a`/`b` data `splitOff_isMinimalKDof`
consumes. -/
theorem exists_splitOff_data_of_degree_eq_two [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} (hD1 : 1 ≤ bodyBarDim n) (hG0 : G.IsKDof n 0) {v b₀ : α}
    (hvG : v ∈ V(G)) (hb₀G : b₀ ∈ V(G)) (hb₀v : b₀ ≠ v) (hdeg : G.degree v = 2) :
    ∃ (a b : α) (eₐ e_b : β), a ≠ v ∧ b ≠ v ∧ a ∈ V(G) ∧ b ∈ V(G) ∧ eₐ ≠ e_b ∧
      G.IsLink eₐ v a ∧ G.IsLink e_b v b ∧ ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b := by
  classical
  -- `degree v = 2·#loops + #nonloops`, and `#nonloops ≥ 2` (two-edge-connectivity).
  have hcount := G.degree_eq_ncard_add_ncard v
  have hcross : 2 ≤ (G.crossingEdges (cutLabeling {v} v b₀)).ncard :=
    two_le_crossingEdges_of_isKDof_zero hD1 hG0 (Set.mem_singleton v) hvG hb₀G
      (by simpa using hb₀v)
  have hnl2 : 2 ≤ {e | G.IsNonloopAt e v}.ncard :=
    le_trans hcross (Set.ncard_le_ncard crossingEdges_cutLabeling_singleton_subset
      (Set.toFinite _))
  -- Hence `#loops = 0` and `#nonloops = 2`.
  have hnl_eq : {e | G.IsNonloopAt e v}.ncard = 2 := by omega
  have hloop0 : {e | G.IsLoopAt e v}.ncard = 0 := by omega
  -- The two nonloop edges, distinct, with far endpoints.
  obtain ⟨eₐ, e_b, hne, hset⟩ := Set.ncard_eq_two.mp hnl_eq
  have hea : G.IsNonloopAt eₐ v := by
    have : eₐ ∈ {e | G.IsNonloopAt e v} := by rw [hset]; exact Set.mem_insert _ _
    exact this
  have heb : G.IsNonloopAt e_b v := by
    have : e_b ∈ {e | G.IsNonloopAt e v} := by rw [hset]; exact Set.mem_insert_of_mem _ rfl
    exact this
  obtain ⟨a, hav, hla⟩ := hea
  obtain ⟨b, hbv, hlb⟩ := heb
  -- Closure: every `v`-incident edge is `eₐ` or `e_b` (no loops at `v`).
  have hclosure : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b := by
    intro e x hlink
    have hinc : G.Inc e v := hlink.inc_left
    rcases hinc.isLoopAt_or_isNonloopAt with hloop | hnonloop
    · exact absurd (Set.eq_empty_iff_forall_notMem.mp
        (Set.ncard_eq_zero (Set.toFinite _) |>.mp hloop0) e hloop) id
    · have : e ∈ ({eₐ, e_b} : Set β) := hset ▸ hnonloop
      simpa [Set.mem_insert_iff] using this
  exact ⟨a, b, eₐ, e_b, hav, hbv, hla.right_mem, hlb.right_mem, hne, hla, hlb, hclosure⟩

/-- **Reduction of minimal `0`-dof-graphs** (`thm:minimal-kdof-reduction`; Katoh–Tanigawa 2011
Theorem 4.9). The combinatorial skeleton of the molecular conjecture's induction, phrased as the
well-founded induction principle that the reduction dichotomy + the vertex-count measure drive.

For `D = bodyBarDim n ≥ 3` (the molecular regime `n ≥ 2`), a motive `P` on graphs that

* holds for every minimal `0`-dof-graph on exactly two vertices (the two-vertex double edge,
  `hbase`),
* is reflected by splitting off a reducible degree-2 vertex — if `P` holds of the splitting-off
  `G_v^{ab}` then it holds of `G` (`hsplit`), and
* is reflected by contracting a proper rigid subgraph, given the induction hypothesis on every
  strictly-smaller minimal `0`-dof-graph (`hcontract`),

holds of every minimal `0`-dof-graph `G` with `2 ≤ |V(G)|`. The proof is the `|V|`-induction
(`lem:reduction-measure`): the base case `|V| = 2`; for `|V| ≥ 3`, either `G` has a proper rigid
subgraph — apply `hcontract` with the strong induction hypothesis — or it does not, in which case
`exists_degree_eq_two` (`lem:reducible-vertex`) supplies a degree-2 vertex,
`exists_splitOff_data_of_degree_eq_two` its two incident edges, and `splitOff_isMinimalKDof`
(`lem:reduction-step`) makes the splitting-off a strictly-smaller (`splitOff_vertexSet_ncard_lt`)
minimal `0`-dof-graph on which the induction hypothesis closes the `hsplit` premise.

The contraction branch is handed only the *existence* of a proper rigid subgraph together with
the strong induction hypothesis (rather than recursing on `rigidContract` internally): bridging
the matroid-side `contraction_isMinimalKDof` to a graph-level `(G.rigidContract H r).IsMinimalKDof`
is the graph↔matroid correspondence Phase 20 deliberately did not build (see `notes/Phase20.md`;
the Phase-21 N4 bridge `rigidContract_isMinimalKDof` has since closed it, and the Phase-22h
predicate repair makes proper rigid subgraphs span `≥ 2` vertices so the measure does drop —
the handed-IH shape stays because Case I genuinely consumes the IH at *two* objects, the block
and the contraction). The user discharges Case I from `H`. The splitting-off branch, fully
graph-level, recurses internally. The `hfresh` premise supplies an unused edge label for each
splitting-off (`splitOff` injects a fresh `e₀`); it holds whenever `β` is not exhausted by
`E(G)` — e.g. `β` infinite, or large relative to the edge count. This is the combinatorial
backbone the algebraic induction (Phases 21–23) realizes at the rigidity-matrix rank. -/
theorem minimal_kdof_reduction [DecidableEq β] [Finite α] [Finite β] {n : ℕ}
    (hD : 3 ≤ bodyBarDim n) (hfresh : ∀ G' : Graph α β, ∃ e₀ : β, e₀ ∉ E(G'))
    {P : Graph α β → Prop}
    (hbase : ∀ G : Graph α β, G.IsMinimalKDof n 0 → V(G).ncard = 2 → P G)
    (hsplit : ∀ (G : Graph α β) (v a b : α) (eₐ e_b e₀ : β),
      G.IsMinimalKDof n 0 → (∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) →
      v ∈ V(G) → a ≠ v → b ≠ v → a ∈ V(G) → b ∈ V(G) → eₐ ≠ e_b →
      G.IsLink eₐ v a → G.IsLink e_b v b → (∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b) →
      e₀ ∉ E(G) → P (G.splitOff v a b e₀) → P G)
    (hcontract : ∀ G : Graph α β, G.IsMinimalKDof n 0 → 3 ≤ V(G).ncard →
      (∃ H : Graph α β, H.IsProperRigidSubgraph G n) →
      (∀ G' : Graph α β, G'.IsMinimalKDof n 0 → 2 ≤ V(G').ncard →
        V(G').ncard < V(G).ncard → P G') → P G) :
    ∀ G : Graph α β, G.IsMinimalKDof n 0 → 2 ≤ V(G).ncard → P G := by
  classical
  have hD1 : 1 ≤ bodyBarDim n := le_trans (by norm_num) hD
  have hD2 : 2 ≤ bodyBarDim n := le_trans (by norm_num) hD
  -- Strong induction on the vertex count `|V(G)|`.
  intro G
  induction hN : V(G).ncard using Nat.strong_induction_on generalizing G with
  | _ N IH =>
  intro hG hV2
  rcases eq_or_lt_of_le hV2 with hVeq | hVlt
  · exact hbase G hG (hN.trans hVeq.symm)
  · -- `|V(G)| ≥ 3`: split on the existence of a proper rigid subgraph.
    have hV3 : 3 ≤ V(G).ncard := by rw [hN]; omega
    by_cases hrig : ∃ H : Graph α β, H.IsProperRigidSubgraph G n
    · -- Case I: contract a proper rigid subgraph (handed the strong induction hypothesis).
      refine hcontract G hG hV3 hrig (fun G' hG' hG'2 hlt => IH _ (hN ▸ hlt) _ rfl hG' hG'2)
    · -- Case II: no proper rigid subgraph ⟹ a reducible degree-2 vertex; split it off.
      push Not at hrig
      have hV2' : 2 ≤ V(G).ncard := by rw [hN]; exact hV2
      obtain ⟨v, hvG, hvdeg⟩ := exists_degree_eq_two hD hV2' hG hrig
      -- A companion vertex `b₀ ≠ v` (exists since `|V(G)| ≥ 2`).
      obtain ⟨b₀, hb₀G, hb₀v⟩ : ∃ b₀ ∈ V(G), b₀ ≠ v := by
        by_contra h
        push Not at h
        have hsub : V(G) ⊆ {v} := fun x hx => h x hx
        have : V(G).ncard ≤ 1 := by
          rw [← Set.ncard_singleton v]; exact Set.ncard_le_ncard hsub (Set.toFinite _)
        omega
      obtain ⟨a, b, eₐ, e_b, hav, hbv, haV, hbV, heab, hla, hlb, hdeg2⟩ :=
        exists_splitOff_data_of_degree_eq_two hD1 hG.1 hvG hb₀G hb₀v hvdeg
      -- A fresh edge label `e₀ ∉ E(G)` (the freshness hypothesis: `β` carries unused labels).
      obtain ⟨e₀, he₀⟩ := hfresh G
      have hsplitMin : (G.splitOff v a b e₀).IsMinimalKDof n 0 :=
        splitOff_isMinimalKDof hD2 hV3 hav hbv haV hbV hvG heab hla hlb hdeg2 he₀ hG hrig
      have hsmaller : V(G.splitOff v a b e₀).ncard < N :=
        hN ▸ splitOff_vertexSet_ncard_lt hvG
      have hsplit2 : 2 ≤ V(G.splitOff v a b e₀).ncard := by
        rw [vertexSet_splitOff]
        have hdv : (V(G) \ {v}).ncard = V(G).ncard - 1 := by
          rw [Set.ncard_diff (by simpa using hvG) (Set.toFinite _), Set.ncard_singleton]
        omega
      exact hsplit G v a b eₐ e_b e₀ hG hrig hvG hav hbv haV hbV heab hla hlb hdeg2 he₀
        (IH _ hsmaller _ rfl hsplitMin hsplit2)

/-! ### The repacking descent: a base admits a balanced forest packing
(`lem:forest-surgery-split`, the balanced-packing descent — outer loop)

This closes the balanced-packing assumption Katoh–Tanigawa 2011 Lemma 4.1 (p.660) glosses
(`rem:kt-lemma-41`~(2)): **a base of `M(G̃)` admits a `D`-forest packing in which every one
of the `D` forests meets the degree-2 vertex `v`.** The two halves and their assembly step
are green: the counting half (`isBase_vfiber_ncard_ge`: a base meets `≥ D` of the `2(D−1)`
fibers at `v`), the redistribution kernel (`acyclicSet_insert_vfiber_of_not_inc`: a
`v`-avoiding forest absorbs a free `v`-fiber as a pendant), and one rebalancing move
(`exists_packing_move_of_not_inc`). This is the **outer loop** that iterates the move to
termination.

The descent runs on a *disjoint* forest packing (a genuine partition of the base `B`, not
merely a cover), obtained by `disjointed` from the `Matroid.union_indep_iff` cover
(`matroidMG_indep_iff_exists_forest_packing`). Disjointness is the device that handles the
caveat the cover form leaves open — when a `v`-fiber `x` is moved into a `v`-avoiding forest
`F_j`, it is removed from every *other* forest, and disjointness guarantees `x` belonged to
exactly one donor, so at most one forest can lose `v`-incidence. The pigeonhole then makes
the move strictly safe: if `F_j` avoids `v`, then the `≥ D` `v`-fibers of `B` are partitioned
among the other `≤ D − 1` forests, so some forest `F_i` (`i ≠ j`) holds `≥ 2` of them; moving
one to `F_j` leaves `F_i` still meeting `v` while `F_j` now meets `v`, strictly raising the
count of `v`-meeting forests. A strong induction on the count of `v`-avoiding forests
terminates with a balanced packing. Off the Theorem-4.9 critical path (the deficiency route
already delivered Theorem 4.9); this discharges the deferred surgery TODO's last piece. -/

/-- A `v`-fiber (a copy of `eₐ` or `e_b`) is incident to `v` in `G̃`, and conversely a fiber
of `E(G̃)` incident to `v` is a `v`-fiber, when `eₐ`, `e_b` are the only `v`-incident edges. -/
private lemma vfiber_inc_iff {G : Graph α β} {n : ℕ} {v a b : α} {eₐ e_b : β}
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    {p : β × Fin (bodyHingeMult n)} (_hpE : p ∈ E(G.mulTilde n)) :
    (G.mulTilde n).Inc p v ↔ p ∈ edgeFiber eₐ n ∪ edgeFiber e_b n := by
  rw [mulTilde_inc]
  constructor
  · rintro ⟨w, hw⟩
    rcases hdeg2 p.1 w hw with h | h
    · exact Or.inl (by rw [edgeFiber, Set.mem_setOf_eq]; exact h)
    · exact Or.inr (by rw [edgeFiber, Set.mem_setOf_eq]; exact h)
  · rintro (h | h) <;> rw [edgeFiber, Set.mem_setOf_eq] at h <;> rw [h]
    · exact hla.inc_left
    · exact hlb.inc_left

/-- **The repacking descent (outer loop): a base admits a balanced forest packing**
(`lem:forest-surgery-split`; Katoh–Tanigawa 2011 Lemma 4.1 p.660). For a base `B` of
`M(G̃)` at a degree-2 vertex `v` (with `eₐ`, `e_b` its only incident edges, `D ≥ 2`), there
is a `D`-forest packing of `B` — `D = bodyBarDim n` cycle-matroid-independent fiber sets
covering `B` — in which **every** forest meets `v`. This is the balanced packing Katoh–
Tanigawa's Lemma 4.1 base-case proof assumes without justification; it is achievable, so
the missing step is a *gap, not an error*.

Proof: disjointify the `Matroid.union_indep_iff` cover of the base
(`matroidMG_indep_iff_exists_forest_packing`) into a genuine partition, then run a strong
induction on the number of `v`-avoiding forests. The base meets `≥ D` `v`-fibers
(`isBase_vfiber_ncard_ge`); if some forest avoids `v`, the pigeonhole forces another forest
to hold `≥ 2` of them, and the rebalancing move (`exists_packing_move_of_not_inc`, recipient
acyclic via `acyclicSet_insert_vfiber_of_not_inc`) shifts one over, strictly raising the
count of `v`-meeting forests while preserving disjointness. -/
theorem exists_balanced_forest_packing [DecidableEq β] [Finite α] [Finite β] {G : Graph α β}
    {n : ℕ} (hD : 2 ≤ bodyBarDim n) {v a b : α} {eₐ e_b : β}
    (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b)
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    {B : Set (β × Fin (bodyHingeMult n))} (hB : (G.matroidMG n).IsBase B) :
    ∃ Fs : Fin (bodyBarDim n) → Set (β × Fin (bodyHingeMult n)),
      (⋃ i, Fs i = B) ∧ (∀ i, ((G.mulTilde n).cycleMatroid).Indep (Fs i)) ∧
        (Pairwise (Function.onFun Disjoint Fs)) ∧
        (∀ i, ∃ p ∈ Fs i, (G.mulTilde n).Inc p v) := by
  classical
  haveI : Nonempty (Fin (bodyBarDim n)) := ⟨⟨0, lt_of_lt_of_le (by norm_num) hD⟩⟩
  set vfib := edgeFiber eₐ n ∪ edgeFiber e_b n with hvfib
  have hBE : B ⊆ E(G.mulTilde n) := by
    have := hB.subset_ground; rwa [matroidMG] at this
  have hinciff : ∀ p ∈ E(G.mulTilde n),
      ((G.mulTilde n).Inc p v ↔ p ∈ vfib) := fun p hp ↦ vfiber_inc_iff hla hlb hdeg2 hp
  have hcount : bodyBarDim n ≤ (B ∩ vfib).ncard :=
    isBase_vfiber_ncard_ge hD hav hbv heab hla hlb hdeg2 hB
  have hmeet_iff : ∀ F : Set (β × Fin (bodyHingeMult n)), F ⊆ B →
      ((∃ p ∈ F, (G.mulTilde n).Inc p v) ↔ (F ∩ vfib).Nonempty) := by
    intro F hF
    constructor
    · rintro ⟨p, hpF, hpinc⟩
      exact ⟨p, hpF, (hinciff p (hBE (hF hpF))).mp hpinc⟩
    · rintro ⟨p, hpF, hpv⟩
      exact ⟨p, hpF, (hinciff p (hBE (hF hpF))).mpr hpv⟩
  -- Disjointify the cover of `B` into a genuine partition (`disjointed` over `Fin D`).
  obtain ⟨Fs₀, hcover₀, hindep₀⟩ :=
    ((matroidMG_indep_iff_exists_forest_packing G n).mp hB.indep).2
  set Ds := disjointed Fs₀ with hDs
  have hDscover : ⋃ i, Ds i = B := by rw [hDs, iUnion_disjointed]; exact hcover₀
  have hDsindep : ∀ i, ((G.mulTilde n).cycleMatroid).Indep (Ds i) :=
    fun i ↦ (hindep₀ i).subset (disjointed_le Fs₀ i)
  have hDsdisj : Pairwise (Function.onFun Disjoint Ds) := disjoint_disjointed Fs₀
  -- Strong induction on the count of `v`-avoiding forests.
  suffices H : ∀ m : ℕ, ∀ Fs : Fin (bodyBarDim n) → Set (β × Fin (bodyHingeMult n)),
      (⋃ i, Fs i = B) → (∀ i, ((G.mulTilde n).cycleMatroid).Indep (Fs i)) →
      Pairwise (Function.onFun Disjoint Fs) →
      {i | (Fs i ∩ vfib) = ∅}.ncard ≤ m →
      ∃ Fs' : Fin (bodyBarDim n) → Set (β × Fin (bodyHingeMult n)),
        (⋃ i, Fs' i = B) ∧ (∀ i, ((G.mulTilde n).cycleMatroid).Indep (Fs' i)) ∧
          (Pairwise (Function.onFun Disjoint Fs')) ∧
          (∀ i, (Fs' i ∩ vfib).Nonempty) by
    obtain ⟨Fs', hc, hi, hd, hmeet⟩ :=
      H {i | (Ds i ∩ vfib) = ∅}.ncard Ds hDscover hDsindep hDsdisj le_rfl
    refine ⟨Fs', hc, hi, hd, fun i ↦ ?_⟩
    exact (hmeet_iff (Fs' i) (hc ▸ Set.subset_iUnion Fs' i)).mpr (hmeet i)
  intro m
  induction m with
  | zero =>
    intro Fs hcover hindep hdisj hle
    refine ⟨Fs, hcover, hindep, hdisj, fun i ↦ ?_⟩
    have hempty : {i | (Fs i ∩ vfib) = ∅} = ∅ := by
      rw [← Set.ncard_eq_zero (Set.toFinite _)]; omega
    by_contra hne
    have hmem : i ∈ {i | (Fs i ∩ vfib) = ∅} := Set.not_nonempty_iff_eq_empty.mp hne
    rw [hempty] at hmem; exact hmem
  | succ m ih =>
    intro Fs hcover hindep hdisj hle
    by_cases hbal : ∀ i, (Fs i ∩ vfib).Nonempty
    · exact ⟨Fs, hcover, hindep, hdisj, hbal⟩
    simp only [not_forall, Set.not_nonempty_iff_eq_empty] at hbal
    obtain ⟨j, hj⟩ := hbal
    have hssubB : ∀ i, Fs i ⊆ B := fun i ↦ hcover ▸ Set.subset_iUnion Fs i
    -- Pigeonhole: `∑_i |Fs i ∩ vfib| = |B ∩ vfib| ≥ D`, `j` contributes `0`,
    -- `D` indices ⟹ some `i` has `|Fs i ∩ vfib| ≥ 2`.
    have hpart : ∑ i, (Fs i ∩ vfib).ncard = (B ∩ vfib).ncard := by
      rw [← finsum_eq_sum_of_fintype,
        ← Set.ncard_iUnion_of_finite (fun i ↦ Set.toFinite _)
          (fun s t hst ↦ (hdisj hst).mono Set.inter_subset_left Set.inter_subset_left),
        ← Set.iUnion_inter, hcover]
    have hjzero : (Fs j ∩ vfib).ncard = 0 := by rw [hj]; exact Set.ncard_empty _
    obtain ⟨i, hij, hidonor⟩ : ∃ i, i ≠ j ∧ 2 ≤ (Fs i ∩ vfib).ncard := by
      by_contra hcon
      simp only [not_exists, not_and, not_le] at hcon
      have hbnd : ∀ k ∈ Finset.univ, (Fs k ∩ vfib).ncard ≤ (if k = j then 0 else 1) := by
        intro k _
        by_cases hkj : k = j
        · subst hkj; simp [hjzero]
        · simpa [hkj] using Nat.lt_succ_iff.mp (hcon k hkj)
      have hsum : ∑ k : Fin (bodyBarDim n), (if k = j then (0:ℕ) else 1)
          = bodyBarDim n - 1 := by
        have hcong : (∑ k : Fin (bodyBarDim n), if k = j then (0:ℕ) else 1)
            = (Finset.univ.filter (fun k => k ≠ j)).card := by
          rw [Finset.card_filter]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          by_cases h : k = j <;> simp [h]
        rw [hcong, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ j),
          Finset.card_univ, Fintype.card_fin]
      have hle' := Finset.sum_le_sum hbnd
      rw [hsum, hpart] at hle'
      omega
    -- Pick a spare `v`-fiber `x ∈ Fs i ∩ vfib`. `Fs i` holds `≥ 2`, so it is nonempty.
    obtain ⟨x, hxFi, hxvfib⟩ : (Fs i ∩ vfib).Nonempty := by
      rw [← Set.ncard_pos (Set.toFinite _)]; omega
    -- `x` is a non-loop `v`-fiber: `IsLink x v a` (if `eₐ`) or `IsLink x v b` (if `e_b`).
    have hxlink : ∃ w, (G.mulTilde n).IsLink x v w ∧ w ≠ v := by
      rcases hxvfib with hxe | hxe <;> rw [edgeFiber, Set.mem_setOf_eq] at hxe
      · exact ⟨a, by rw [mulTilde_isLink, hxe]; exact hla, hav⟩
      · exact ⟨b, by rw [mulTilde_isLink, hxe]; exact hlb, hbv⟩
    obtain ⟨w, hxvw, hwv⟩ := hxlink
    have hxB : x ∈ B := hssubB i hxFi
    -- `Fs j` avoids `v`: any `v`-incident fiber would be in `vfib`, but `Fs j ∩ vfib = ∅`.
    have hFjv : ∀ p ∈ Fs j, ¬ (G.mulTilde n).Inc p v := by
      intro p hpFj hpinc
      have : p ∈ Fs j ∩ vfib := ⟨hpFj, (hinciff p (hBE (hssubB j hpFj))).mp hpinc⟩
      rw [hj] at this; exact this
    -- The explicit move.
    set Fs' : Fin (bodyBarDim n) → Set (β × Fin (bodyHingeMult n)) :=
      fun k => if k = j then insert x (Fs j) else Fs k \ {x} with hFs'
    have hcover' : ⋃ k, Fs' k = B := by
      apply Set.Subset.antisymm
      · rintro p hp
        rw [Set.mem_iUnion] at hp
        obtain ⟨k, hk⟩ := hp
        by_cases hkj : k = j
        · subst hkj; simp only [hFs', ↓reduceIte] at hk
          rcases Set.mem_insert_iff.mp hk with rfl | hk'
          · exact hxB
          · exact hssubB k hk'
        · simp only [hFs', if_neg hkj] at hk; exact hssubB k hk.1
      · rw [← hcover]
        rintro p hp
        rw [Set.mem_iUnion] at hp ⊢
        obtain ⟨k, hk⟩ := hp
        by_cases hpx : p = x
        · exact ⟨j, by simp only [hFs', ↓reduceIte]; exact Set.mem_insert_iff.mpr (Or.inl hpx)⟩
        · by_cases hkj : k = j
          · subst hkj
            exact ⟨k, by simp only [hFs', ↓reduceIte]; exact Set.mem_insert_iff.mpr (Or.inr hk)⟩
          · exact ⟨k, by simp only [hFs', if_neg hkj]; exact ⟨hk, by simpa using hpx⟩⟩
    have hindep' : ∀ k, ((G.mulTilde n).cycleMatroid).Indep (Fs' k) := by
      intro k
      by_cases hkj : k = j
      · subst hkj
        simp only [hFs', ↓reduceIte]
        exact acyclicSet_insert_vfiber_of_not_inc (hindep k) hxvw hwv hFjv
      · simp only [hFs', if_neg hkj]; exact (hindep k).subset Set.diff_subset
    have hdisj' : Pairwise (Function.onFun Disjoint Fs') := by
      intro k l hkl
      simp only [Function.onFun, hFs']
      rcases eq_or_ne k j with rfl | hk
      · simp only [↓reduceIte, if_neg (Ne.symm hkl), Set.disjoint_left]
        rintro p hpins ⟨hpFl, hpx⟩
        rcases Set.mem_insert_iff.mp hpins with rfl | hpFj
        · exact hpx rfl
        · exact (hdisj (Ne.symm hkl)).le_bot ⟨hpFl, hpFj⟩
      · simp only [if_neg hk]
        rcases eq_or_ne l j with rfl | hl
        · simp only [↓reduceIte, Set.disjoint_right]
          rintro p hpins ⟨hpFk, hpx⟩
          rcases Set.mem_insert_iff.mp hpins with rfl | hpFj
          · exact hpx rfl
          · exact (hdisj hk).le_bot ⟨hpFk, hpFj⟩
        · simp only [if_neg hl]
          exact (hdisj hkl).mono Set.diff_subset Set.diff_subset
    -- The `v`-avoiding count strictly drops: `j` leaves it; `i` and others don't enter it.
    -- `x ∈ Fs' j ∩ vfib`, so `j` no longer avoids `v`.
    have hxFs'j : x ∈ Fs' j ∩ vfib :=
      ⟨by simp only [hFs', ↓reduceIte]; exact Set.mem_insert _ _, hxvfib⟩
    have hdrop : {k | (Fs' k ∩ vfib) = ∅}.ncard < {k | (Fs k ∩ vfib) = ∅}.ncard := by
      apply Set.ncard_lt_ncard _ (Set.toFinite _)
      constructor
      · -- `{k | Fs' k ∩ vfib = ∅} ⊆ {k | Fs k ∩ vfib = ∅}`.
        intro k hk
        simp only [Set.mem_setOf_eq] at hk ⊢
        by_cases hkj : k = j
        · subst hkj
          -- `Fs' j ⊇ {x}`, `x ∈ vfib`, so `Fs' j ∩ vfib ≠ ∅` — `hk` is impossible.
          exact absurd (hk ▸ hxFs'j) (Set.notMem_empty x)
        · -- `Fs' k = Fs k \ {x}`. Show `Fs k ∩ vfib = ∅`.
          simp only [hFs', if_neg hkj] at hk
          rw [Set.eq_empty_iff_forall_notMem] at hk ⊢
          intro p hp
          rcases eq_or_ne p x with hpx | hpx
          · -- `p = x ∈ Fs k`; disjointness with `x ∈ Fs i` forces `k = i`, but then
            -- `Fs i ∩ vfib` (card ≥ 2) has some `y ≠ x` surviving the deletion — contra `hk`.
            have hxFk : x ∈ Fs k := hpx ▸ hp.1
            have hki : k = i := by
              by_contra hne
              exact Set.disjoint_left.mp (hdisj (Ne.symm hne)) hxFi hxFk
            subst hki
            obtain ⟨y, hy, hyne⟩ := Set.exists_ne_of_one_lt_ncard hidonor x
            exact hk y ⟨⟨hy.1, by simpa using hyne⟩, hy.2⟩
          · exact hk p ⟨⟨hp.1, by simpa using hpx⟩, hp.2⟩
      · -- `j` is in the old avoiding-set but not the new one.
        refine fun hsub ↦ ?_
        have hjnew : (Fs' j ∩ vfib) = ∅ := hsub (show j ∈ {k | (Fs k ∩ vfib) = ∅} from hj)
        exact absurd (hjnew ▸ hxFs'j) (Set.notMem_empty x)
    exact ih Fs' hcover' hindep' hdisj' (by omega)

/-! ### The surgery count (`lem:forest-surgery-count`, Katoh–Tanigawa Lemma 4.1)

The cardinality bookkeeping that the corrected forest surgery rests on. Starting from a
*balanced* edge-disjoint `D`-forest packing of a base `I` of `M(G̃)` — every forest meets the
degree-2 vertex `v` (`exists_balanced_forest_packing`) — reroute each forest across `v`:

* a `v`-degree-`2` forest (one `eₐ`-copy `pa`, one `e_b`-copy `pb`) drops `{pa, pb}` and adds a
  *single* short-circuit copy `r = (e₀, pa.2)` of `ã̃b` (via `isAcyclicSet_splitOff_reroute`);
* a `v`-degree-`1` forest drops its lone `v`-fiber and adds **nothing**
  (acyclicity: `isAcyclicSet_splitOff_of_diff_fiberAtVertex`).

Every forest has `v`-degree `1` or `2` — at least `1` by balance, at most `2` because two copies
of the same `v`-edge form a `2`-cycle (`fiber_inter_subsingleton_of_isAcyclicSet_mulTilde`,
applied to `eₐ` and `e_b` separately, the only two edges at the degree-2 vertex `v`). So **every**
forest shrinks by exactly one (`|F'ᵢ| + 1 = |Fᵢ|`), and as the packing partitions `I`, the
rerouted union satisfies `|⋃ F'ᵢ| + D = |I|`. This is precisely Katoh–Tanigawa's accounting
`2h' + (D − h') = h` — `h` fibers dropped, `h'` short-circuit copies added, net `−D` — handling
the `dᶠ(v) = 1` forests their proof glosses. The added copies are distinct across the degree-`2`
forests: `r i = (e₀, (pa i).2)`, and the `pa i` (distinct `eₐ`-copies in disjoint forests) have
distinct second coordinates, so `≤ D − 1` such copies are needed and `D − 1` exist. Off the
Theorem-4.9 critical path (the deficiency route already delivered Theorem 4.9). -/

/-- **The surgery count `|⋃ F'ᵢ| + D = |I|`** (`lem:forest-surgery-count`; Katoh–Tanigawa 2011
Lemma 4.1 p.660). Let `v` be a degree-2 vertex of `G` with distinct neighbours `a ≠ b`
(`a, b ≠ v ∈ V(G)`, incident edges exactly `eₐ ≠ e_b`), `e₀ ∉ E(G)` fresh, `D = bodyBarDim n ≥ 2`.
Given a *balanced* edge-disjoint `D`-forest packing `Fs` of a fiber set `I` — `⋃ Fs i = I`, each
`Fs i` acyclic in `G̃`, pairwise disjoint, and **every** forest meets `v`
(`exists_balanced_forest_packing`) — there is a rerouted family `Fs'` that is an edge-disjoint
`D`-forest packing of the multiplied splitting-off `G̃_v^{ab}` whose union is `M(G̃_v^{ab})`-indep
and satisfies
`(⋃ i, Fs' i).ncard + bodyBarDim n = I.ncard`.

This is the corrected construction (the superseded `forest_surgery_split` was vacuous and assumed
away the `dᶠ(v) = 1` forests): every forest shrinks by exactly one because a degree-`2` forest
loses two `v`-fibers and gains one `ã̃b`-copy while a degree-`1` forest loses one and gains none.
See the section preamble. -/
theorem forest_surgery_count [DecidableEq β] [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hD : 2 ≤ bodyBarDim n) {v a b : α} {eₐ e_b e₀ : β}
    (hab : a ≠ b) (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b)
    (haV : a ∈ V(G)) (hbV : b ∈ V(G)) (he₀ : e₀ ∉ E(G))
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    {I : Set (β × Fin (bodyHingeMult n))}
    (Fs : Fin (bodyBarDim n) → Set (β × Fin (bodyHingeMult n)))
    (hcover : ⋃ i, Fs i = I) (hindep : ∀ i, ((G.mulTilde n).cycleMatroid).Indep (Fs i))
    (hdisj : Pairwise (Function.onFun Disjoint Fs))
    (hmeet : ∀ i, ∃ p ∈ Fs i, (G.mulTilde n).Inc p v) :
    ∃ Fs' : Fin (bodyBarDim n) → Set (β × Fin (bodyHingeMult n)),
      (∀ i, ((G.splitOff v a b e₀).mulTilde n).cycleMatroid.Indep (Fs' i)) ∧
      (Pairwise (Function.onFun Disjoint Fs')) ∧
      ((G.splitOff v a b e₀).matroidMG n).Indep (⋃ i, Fs' i) ∧
      (⋃ i, Fs' i).ncard + bodyBarDim n = I.ncard ∧
      ((⋃ i, Fs' i) ∩ edgeFiber e₀ n).ncard < bodyHingeMult n := by
  classical
  -- Each forest is finite (subset of the finite ground set).
  have hssubE : ∀ i, Fs i ⊆ E(G.mulTilde n) := fun i ↦ (hindep i).subset_ground
  -- `fiberAtVertex v ⊆ ẽₐ ∪ ẽ_b`: the only `v`-incident edges are `eₐ, e_b`.
  have hfibsub : G.fiberAtVertex n v ⊆ edgeFiber eₐ n ∪ edgeFiber e_b n := by
    intro p hp
    rw [mem_fiberAtVertex] at hp
    obtain ⟨x, hlx⟩ := hp
    rcases hdeg2 p.1 x hlx with h | h
    · exact Or.inl (by rw [edgeFiber, Set.mem_setOf_eq]; exact h)
    · exact Or.inr (by rw [edgeFiber, Set.mem_setOf_eq]; exact h)
  -- Per-edge subsingleton: a forest holds ≤ 1 copy of `eₐ`, ≤ 1 of `e_b`.
  have hsubₐ : ∀ i, (Fs i ∩ edgeFiber eₐ n).Subsingleton := fun i ↦
    fiber_inter_subsingleton_of_isAcyclicSet_mulTilde (Ne.symm hav) hla (hindep i)
  have hsub_b : ∀ i, (Fs i ∩ edgeFiber e_b n).Subsingleton := fun i ↦
    fiber_inter_subsingleton_of_isAcyclicSet_mulTilde (Ne.symm hbv) hlb (hindep i)
  -- `Fs i ∩ fiberAtVertex v = (Fs i ∩ ẽₐ) ∪ (Fs i ∩ ẽ_b)`, the two pieces disjoint.
  have hfibdecomp : ∀ i, Fs i ∩ G.fiberAtVertex n v
      = (Fs i ∩ edgeFiber eₐ n) ∪ (Fs i ∩ edgeFiber e_b n) := by
    intro i
    apply Set.Subset.antisymm
    · rintro p ⟨hpF, hpv⟩
      rcases hfibsub hpv with h | h
      · exact Or.inl ⟨hpF, h⟩
      · exact Or.inr ⟨hpF, h⟩
    · rintro p (⟨hpF, hp⟩ | ⟨hpF, hp⟩) <;> refine ⟨hpF, ?_⟩ <;>
        rw [edgeFiber, Set.mem_setOf_eq] at hp <;> rw [mem_fiberAtVertex, hp]
      · exact hla.inc_left
      · exact hlb.inc_left
  have hfibdisj : Disjoint (edgeFiber eₐ n) (edgeFiber e_b n) := by
    rw [Set.disjoint_left]; rintro p hp hp'
    rw [edgeFiber, Set.mem_setOf_eq] at hp hp'; exact heab (hp ▸ hp')
  -- Degree at `v` of each forest is `1` or `2`.
  have hdeg : ∀ i, (Fs i ∩ G.fiberAtVertex n v).ncard = 1 ∨
      (Fs i ∩ G.fiberAtVertex n v).ncard = 2 := by
    intro i
    have hle2 : (Fs i ∩ G.fiberAtVertex n v).ncard ≤ 2 := by
      rw [hfibdecomp i]
      refine le_trans (Set.ncard_union_le _ _) ?_
      have := (Set.ncard_le_one_iff_subsingleton).mpr (hsubₐ i)
      have := (Set.ncard_le_one_iff_subsingleton).mpr (hsub_b i)
      omega
    have hpos : 1 ≤ (Fs i ∩ G.fiberAtVertex n v).ncard := by
      obtain ⟨p, hpF, hpv⟩ := hmeet i
      have : (Fs i ∩ G.fiberAtVertex n v).Nonempty :=
        ⟨p, hpF, by rw [mem_fiberAtVertex, ← mulTilde_inc]; exact hpv⟩
      exact this.ncard_pos (Set.toFinite _)
    omega
  -- When `dᶠ(v) = 2`, the two pieces `Fs i ∩ ẽₐ` and `Fs i ∩ ẽ_b` are each singletons; extract
  -- the `eₐ`-copy `paOf i` and `e_b`-copy `pbOf i`.
  have hdeg2_split : ∀ i, (Fs i ∩ G.fiberAtVertex n v).ncard = 2 →
      ∃ pa pb, Fs i ∩ edgeFiber eₐ n = {pa} ∧ Fs i ∩ edgeFiber e_b n = {pb} := by
    intro i hi
    rw [hfibdecomp i,
      Set.ncard_union_eq (hfibdisj.mono Set.inter_subset_right Set.inter_subset_right)
        (Set.toFinite _) (Set.toFinite _)] at hi
    have hca := (Set.ncard_le_one_iff_subsingleton).mpr (hsubₐ i)
    have hcb := (Set.ncard_le_one_iff_subsingleton).mpr (hsub_b i)
    obtain ⟨pa, hpa⟩ := Set.ncard_eq_one.mp (by omega : (Fs i ∩ edgeFiber eₐ n).ncard = 1)
    obtain ⟨pb, hpb⟩ := Set.ncard_eq_one.mp (by omega : (Fs i ∩ edgeFiber e_b n).ncard = 1)
    exact ⟨pa, pb, hpa, hpb⟩
  -- A fixed inhabitant of the fiber type (the else-branch placeholder; `Fs 0` meets `v`).
  haveI : Nonempty (β × Fin (bodyHingeMult n)) := ⟨(hmeet ⟨0, by omega⟩).choose⟩
  -- Choose, per `dᶠ = 2` forest, the swapped-out pair; `r i := (e₀, (paOf i).2)` is the fresh copy.
  set paOf : Fin (bodyBarDim n) → β × Fin (bodyHingeMult n) := fun i =>
    if h : (Fs i ∩ G.fiberAtVertex n v).ncard = 2 then (hdeg2_split i h).choose
    else Classical.arbitrary _ with hpaOf
  set r : Fin (bodyBarDim n) → β × Fin (bodyHingeMult n) := fun i => (e₀, (paOf i).2) with hr
  have hr1 : ∀ i, (r i).1 = e₀ := fun i ↦ rfl
  -- For `dᶠ = 2` forests, `paOf i` is the unique `eₐ`-copy (so `paOf i ∈ Fs i`, `.1 = eₐ`).
  have hpaOf_mem : ∀ i, (Fs i ∩ G.fiberAtVertex n v).ncard = 2 →
      paOf i ∈ Fs i ∩ edgeFiber eₐ n := by
    intro i hi
    have hsing := (hdeg2_split i hi).choose_spec.choose_spec.1
    simp only [hpaOf, dif_pos hi]
    exact hsing.ge (Set.mem_singleton _)
  -- `r` is injective across the `dᶠ = 2` forests: distinct `eₐ`-copies in disjoint forests have
  -- distinct second coordinates.
  have hr_inj2 : ∀ i j, (Fs i ∩ G.fiberAtVertex n v).ncard = 2 →
      (Fs j ∩ G.fiberAtVertex n v).ncard = 2 → r i = r j → i = j := by
    intro i j hi hj hrij
    by_contra hij
    have hpi := hpaOf_mem i hi
    have hpj := hpaOf_mem j hj
    have hpi1 : (paOf i).1 = eₐ := hpi.2
    have hpj1 : (paOf j).1 = eₐ := hpj.2
    -- `paOf i = paOf j`: same first coord `eₐ`, same second coord (from `r i = r j`).
    rw [hr] at hrij
    simp only at hrij
    have hsnd : (paOf i).2 = (paOf j).2 := (Prod.ext_iff.mp hrij).2
    have heq : paOf i = paOf j := Prod.ext_iff.mpr ⟨hpi1.trans hpj1.symm, hsnd⟩
    exact Set.disjoint_left.mp (hdisj hij) hpi.1 (heq ▸ hpj.1)
  -- The fresh copy `r i` is never in any forest of `G̃` (those are `G`-edge copies; `e₀ ∉ E(G)`).
  have hr_notin : ∀ i j, r i ∉ Fs j := by
    intro i j hrFj
    have hrE : r i ∈ E(G.mulTilde n) := hssubE j hrFj
    rw [mem_edgeSet_mulTilde] at hrE
    exact he₀ ((hr1 i) ▸ hrE)
  -- The rerouted family.
  set Fs' : Fin (bodyBarDim n) → Set (β × Fin (bodyHingeMult n)) := fun i =>
    if (Fs i ∩ G.fiberAtVertex n v).ncard = 2 then insert (r i) (Fs i \ G.fiberAtVertex n v)
    else Fs i \ G.fiberAtVertex n v with hFs'
  -- `Fs i ∖ fiberAtVertex v ⊆ Fs' i ⊆ insert (r i) (Fs i ∖ fiberAtVertex v)`, both branches.
  have hFs'sub : ∀ i, Fs' i ⊆ insert (r i) (Fs i \ G.fiberAtVertex n v) := by
    intro i; simp only [hFs']; split
    · exact subset_rfl
    · exact Set.subset_insert _ _
  have hsubFs' : ∀ i, Fs i \ G.fiberAtVertex n v ⊆ Fs' i := by
    intro i; simp only [hFs']; split
    · exact Set.subset_insert _ _
    · exact subset_rfl
  -- Each rerouted forest is acyclic in `G̃_v^{ab}`.
  have hindep' : ∀ i, ((G.splitOff v a b e₀).mulTilde n).cycleMatroid.Indep (Fs' i) := by
    intro i
    simp only [hFs']
    by_cases hi : (Fs i ∩ G.fiberAtVertex n v).ncard = 2
    · rw [if_pos hi]
      obtain ⟨pa, pb, hSpa, hSpb⟩ := hdeg2_split i hi
      have hpaF : pa ∈ Fs i := (hSpa ▸ Set.mem_singleton pa).1
      have hpbF : pb ∈ Fs i := (hSpb ▸ Set.mem_singleton pb).1
      have hpaℓ : (G.mulTilde n).IsLink pa v a := by
        have : pa.1 = eₐ := by
          have := (hSpa ▸ Set.mem_singleton pa).2; rwa [edgeFiber, Set.mem_setOf_eq] at this
        rw [mulTilde_isLink, this]; exact hla
      have hpbℓ : (G.mulTilde n).IsLink pb v b := by
        have : pb.1 = e_b := by
          have := (hSpb ▸ Set.mem_singleton pb).2; rwa [edgeFiber, Set.mem_setOf_eq] at this
        rw [mulTilde_isLink, this]; exact hlb
      have hpab : pa ≠ pb := by
        rintro rfl
        exact hab (hpaℓ.right_unique hpbℓ)
      -- `pa, pb` are exactly the `v`-fibers of `Fs i` (degree-2 ⟹ no others).
      have hall : ∀ q ∈ Fs i, (G.mulTilde n).Inc q v → q = pa ∨ q = pb := by
        intro q hqF hqv
        have hqfib : q ∈ Fs i ∩ G.fiberAtVertex n v :=
          ⟨hqF, by rw [mem_fiberAtVertex, ← mulTilde_inc]; exact hqv⟩
        rw [hfibdecomp i] at hqfib
        rcases hqfib with hqa | hqb
        · exact Or.inl (hSpa ▸ hqa : q ∈ ({pa} : Set _))
        · exact Or.inr (hSpb ▸ hqb : q ∈ ({pb} : Set _))
      have hdiff : Fs i \ G.fiberAtVertex n v = Fs i \ {pa, pb} := by
        ext q
        simp only [Set.mem_diff, mem_fiberAtVertex, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hqF, hqv⟩
          refine ⟨hqF, fun hq ↦ hqv ?_⟩
          rcases hq with rfl | rfl
          · exact hpaℓ.inc_left
          · exact hpbℓ.inc_left
        · rintro ⟨hqF, hq2⟩
          exact ⟨hqF, fun hqv ↦ hq2 (hall q hqF (mulTilde_inc.mpr hqv))⟩
      rw [hdiff]
      exact isAcyclicSet_splitOff_reroute hav hbv haV hbV (hindep i) hpaℓ hpbℓ hpaF hpbF hpab
        hall (hr1 i) he₀
    · rw [if_neg hi]
      exact isAcyclicSet_splitOff_of_diff_fiberAtVertex he₀ (hindep i)
  -- `r i` lies in `Fs' i` only when `Fs i` has `v`-degree `2` (else `Fs' i ⊆ Fs i`, `r i ∉ Fs i`).
  have hrmem : ∀ i, r i ∈ Fs' i → (Fs i ∩ G.fiberAtVertex n v).ncard = 2 := by
    intro i hri
    by_contra hi
    simp only [hFs', if_neg hi] at hri
    exact hr_notin i i hri.1
  -- Pairwise disjoint: the `v`-free cores are disjoint, and `r i ∈ Fs' i` forces `dᶠ(i) = 2`,
  -- where `r` is injective.
  have hdisj' : Pairwise (Function.onFun Disjoint Fs') := by
    intro i j hij
    simp only [Function.onFun, Set.disjoint_left]
    intro p hpi hpj
    rcases Set.mem_insert_iff.mp (hFs'sub i hpi) with hri | hci <;>
      rcases Set.mem_insert_iff.mp (hFs'sub j hpj) with hrj | hcj
    · -- `p = r i = r j`: both forests took the insert branch (`dᶠ = 2`), and `r` is injective.
      exact hij (hr_inj2 i j (hrmem i (hri ▸ hpi)) (hrmem j (hrj ▸ hpj)) (hri.symm.trans hrj))
    · exact hr_notin i j (hri ▸ hcj.1)
    · exact hr_notin j i (hrj ▸ hci.1)
    · exact (hdisj hij).le_bot ⟨hci.1, hcj.1⟩
  -- The rerouted union is a forest packing of `G̃_v^{ab}`, hence `M(G̃_v^{ab})`-independent.
  have hMindep : ((G.splitOff v a b e₀).matroidMG n).Indep (⋃ i, Fs' i) := by
    rw [matroidMG_indep_iff_exists_forest_packing]
    refine ⟨?_, Fs', rfl, hindep'⟩
    refine Set.iUnion_subset fun i ↦ ?_
    have := hindep' i
    rw [cycleMatroid_indep, isAcyclicSet_iff] at this
    exact this.1
  -- The count: every forest shrinks by exactly one.
  -- `(Fs i).ncard = (Fs i \ fib).ncard + (Fs i ∩ fib).ncard`.
  have hpart_i : ∀ i, (Fs i \ G.fiberAtVertex n v).ncard + (Fs i ∩ G.fiberAtVertex n v).ncard
      = (Fs i).ncard := fun i ↦ by
    rw [add_comm]
    exact Set.ncard_inter_add_ncard_diff_eq_ncard (Fs i) (G.fiberAtVertex n v) (Set.toFinite _)
  -- `r i ∉ Fs i \ fib`, so the insert adds exactly one.
  have hrnotcore : ∀ i, r i ∉ Fs i \ G.fiberAtVertex n v := fun i hri ↦ hr_notin i i hri.1
  have hshrink : ∀ i, (Fs' i).ncard + 1 = (Fs i).ncard := by
    intro i
    by_cases hi : (Fs i ∩ G.fiberAtVertex n v).ncard = 2
    · have hcard' : (Fs' i).ncard = (Fs i \ G.fiberAtVertex n v).ncard + 1 := by
        simp only [hFs', if_pos hi]
        rw [Set.ncard_insert_of_notMem (hrnotcore i) (Set.toFinite _)]
      have := hpart_i i; omega
    · have h1 : (Fs i ∩ G.fiberAtVertex n v).ncard = 1 := (hdeg i).resolve_right hi
      have hcard' : (Fs' i).ncard = (Fs i \ G.fiberAtVertex n v).ncard := by
        simp only [hFs', if_neg hi]
      have := hpart_i i; omega
  -- `∑ |Fs' i| + D = ∑ |Fs i| = |I|`.
  have hsumFs' : ∑ i, (Fs' i).ncard = (⋃ i, Fs' i).ncard := by
    rw [← finsum_eq_sum_of_fintype,
      ← Set.ncard_iUnion_of_finite (fun i ↦ Set.toFinite _) hdisj']
  have hsumFs : ∑ i, (Fs i).ncard = I.ncard := by
    rw [← finsum_eq_sum_of_fintype,
      ← Set.ncard_iUnion_of_finite (fun i ↦ Set.toFinite _) hdisj, hcover]
  have hcount : (⋃ i, Fs' i).ncard + bodyBarDim n = I.ncard := by
    have hkey : ∑ i : Fin (bodyBarDim n), ((Fs' i).ncard + 1) = ∑ i, (Fs i).ncard :=
      Finset.sum_congr rfl (fun i _ ↦ hshrink i)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one] at hkey
    rw [← hsumFs', ← hsumFs, hkey]
  -- The `ã̃b`-fiber bound `|⋃ Fs' i ∩ ã̃b| < D − 1` (KT Lemma 4.1's second conclusion). The only
  -- `ã̃b = edgeFiber e₀ n` members of the reroute are the inserted copies `r i`, one per
  -- `dᶠ(v) = 2` forest; their number `h'` is `< D − 1`.
  -- Set of degree-2 forest indices `S`; `h' = |S|`.
  set S : Finset (Fin (bodyBarDim n)) :=
    {i | (Fs i ∩ G.fiberAtVertex n v).ncard = 2} with hS
  -- `⋃ Fs' i ∩ ã̃b ⊆ r '' S`: a fiber-`e₀` member of `Fs' j` is the inserted `r j` (the core
  -- `Fs j ∖ fib ⊆ E(G̃)` carries `G`-edges, copies avoiding the fresh `e₀`), forcing `dᶠ(j) = 2`.
  have hfibsub_e0 : (⋃ i, Fs' i) ∩ edgeFiber e₀ n ⊆ r '' (S : Set (Fin (bodyBarDim n))) := by
    rintro p ⟨hpU, hpf⟩
    rw [Set.mem_iUnion] at hpU
    obtain ⟨j, hpj⟩ := hpU
    rw [edgeFiber, Set.mem_setOf_eq] at hpf
    rcases Set.mem_insert_iff.mp (hFs'sub j hpj) with hrj | hcj
    · -- `p = r j`; `r j ∈ Fs' j` forces `dᶠ(j) = 2`, so `j ∈ S`.
      have hjS : j ∈ (S : Set (Fin (bodyBarDim n))) := by
        simp only [hS, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and]
        exact hrmem j (hrj ▸ hpj)
      exact ⟨j, hjS, hrj.symm⟩
    · -- core member: `p.1 ∈ E(G)`, contradicting `p.1 = e₀ ∉ E(G)`.
      have hpE : p ∈ E(G.mulTilde n) := hssubE j hcj.1
      rw [mem_edgeSet_mulTilde] at hpE
      exact absurd (hpf ▸ hpE) he₀
  -- `h' = |S| ≤ D − 2`: the base's `v`-fibers `h = ∑ (Fs i ∩ fib) = D + h'` are bounded by
  -- `|ẽₐ ∪ ẽ_b| = 2(D − 1)`.
  have hSle : S.card ≤ bodyBarDim n - 2 := by
    -- `∑ (Fs i ∩ fib).ncard = D + |S|` (each term is `1`, or `2` exactly on `S`).
    have hsum_fib : ∑ i, (Fs i ∩ G.fiberAtVertex n v).ncard = bodyBarDim n + S.card := by
      have hterm : ∀ i, (Fs i ∩ G.fiberAtVertex n v).ncard
          = 1 + (if (Fs i ∩ G.fiberAtVertex n v).ncard = 2 then 1 else 0) := by
        intro i; rcases hdeg i with h1 | h2
        · rw [h1, if_neg (by omega)]
        · rw [h2, if_pos rfl]
      calc ∑ i, (Fs i ∩ G.fiberAtVertex n v).ncard
          = ∑ i, (1 + (if (Fs i ∩ G.fiberAtVertex n v).ncard = 2 then 1 else 0)) :=
            Finset.sum_congr rfl (fun i _ ↦ hterm i)
        _ = bodyBarDim n + S.card := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              smul_eq_mul, mul_one, Finset.sum_boole, hS, Nat.cast_id]
    -- `∑ (Fs i ∩ fib) = |⋃ (Fs i ∩ fib)| ≤ |fiberAtVertex v ∩ E(G̃)| = 2(D − 1)`.
    have hdisj_fib : Pairwise (Function.onFun Disjoint (fun i ↦ Fs i ∩ G.fiberAtVertex n v)) :=
      fun i j hij ↦ (hdisj hij).mono Set.inter_subset_left Set.inter_subset_left
    have hsum_eq : ∑ i, (Fs i ∩ G.fiberAtVertex n v).ncard
        = (⋃ i, Fs i ∩ G.fiberAtVertex n v).ncard := by
      rw [← finsum_eq_sum_of_fintype,
        ← Set.ncard_iUnion_of_finite (fun i ↦ Set.toFinite _) hdisj_fib]
    have hUsub : (⋃ i, Fs i ∩ G.fiberAtVertex n v) ⊆ edgeFiber eₐ n ∪ edgeFiber e_b n := by
      refine Set.iUnion_subset fun i ↦ ?_
      exact fun p ⟨_, hpv⟩ ↦ hfibsub hpv
    have hUle : (⋃ i, Fs i ∩ G.fiberAtVertex n v).ncard ≤ 2 * bodyHingeMult n := by
      calc (⋃ i, Fs i ∩ G.fiberAtVertex n v).ncard
          ≤ (edgeFiber eₐ n ∪ edgeFiber e_b n).ncard := Set.ncard_le_ncard hUsub (Set.toFinite _)
        _ ≤ (edgeFiber eₐ n).ncard + (edgeFiber e_b n).ncard := Set.ncard_union_le _ _
        _ = 2 * bodyHingeMult n := by rw [edgeFiber_ncard, edgeFiber_ncard]; ring
    -- `D + |S| = ∑ ≤ 2(D − 1)`, so `|S| ≤ D − 2`. `D ≥ 2`, `D − 1 = bodyHingeMult n`.
    have hHM : bodyHingeMult n = bodyBarDim n - 1 := by rw [bodyHingeMult]
    omega
  -- Assemble: `|⋃ Fs' i ∩ ã̃b| ≤ |r '' S| ≤ |S| ≤ D − 2 < D − 1 = bodyHingeMult n`.
  have hfiblt : ((⋃ i, Fs' i) ∩ edgeFiber e₀ n).ncard < bodyHingeMult n := by
    have h1 : ((⋃ i, Fs' i) ∩ edgeFiber e₀ n).ncard ≤ (r '' (S : Set (Fin (bodyBarDim n)))).ncard :=
      Set.ncard_le_ncard hfibsub_e0 (Set.toFinite _)
    have h2 : (r '' (S : Set (Fin (bodyBarDim n)))).ncard ≤ S.card := by
      calc (r '' (S : Set (Fin (bodyBarDim n)))).ncard
          ≤ (S : Set (Fin (bodyBarDim n))).ncard := Set.ncard_image_le (Set.toFinite _)
        _ = S.card := by rw [Set.ncard_coe_finset]
    have hHM : bodyHingeMult n = bodyBarDim n - 1 := by rw [bodyHingeMult]
    omega
  exact ⟨Fs', hindep', hdisj', hMindep, hcount, hfiblt⟩

/-! ### The forest-surgery assembly (`lem:forest-surgery-split`, Katoh–Tanigawa Lemma 4.1)

The deficiency read-off that closes the splitting-off forest surgery. Starting from a base `B`
of `M(G̃)` at a degree-2 vertex `v`, a *balanced* `D`-forest packing exists
(`exists_balanced_forest_packing`); rerouting it across `v` (`forest_surgery_count`) yields a
`D`-forest packing of the multiplied splitting-off `G̃_v^{ab}` covering an `M(G̃_v^{ab})`-indep set
`I'` of size `|B| − D`. Hence `rank M(G̃_v^{ab}) ≥ |B| − D = rank M(G̃) − D`, and the
def\,=\,corank identity (`rank_add_deficiency_eq`, against the `D(|V| − 1)` trivial-motion
ambient — and `G̃_v^{ab}` has one fewer vertex) reads off
`def(G̃_v^{ab}) ≤ def(G̃)`, KT 4.1's intended conclusion. This is the same bound the
deficiency-count route delivers green as `splitOff_deficiency_le`; the surgery is off the
Theorem-4.9 critical path (`rem:kt-lemma-41`). -/

/-- **Forest surgery at a degree-2 vertex, splitting-off direction** (`lem:forest-surgery-split`;
Katoh–Tanigawa 2011 Lemma 4.1 p.660). Let `v` be a degree-2 vertex of `G` with distinct
neighbours `a ≠ b` (`a, b ≠ v ∈ V(G)`), incident edges exactly `eₐ ≠ e_b`, `e₀ ∉ E(G)` fresh,
`D = bodyBarDim n ≥ 2`, `V(G)` nonempty. Rerouting a balanced forest packing of a base of `M(G̃)`
across `v` (`exists_balanced_forest_packing` + `forest_surgery_count`) produces a forest packing
of `G̃_v^{ab}` of size `|base| − D`, an independent set of `M(G̃_v^{ab})`. The def\,=\,corank
identity then gives
`def(G̃_v^{ab}) ≤ def(G̃)`,
KT's Lemma 4.1 conclusion — the same bound the deficiency-count route delivers as
`splitOff_deficiency_le`. This is the assembled repair of the balanced-packing gloss
(`rem:kt-lemma-41`~(2)): the corrected `forest_surgery_count` handles the `dᶠ(v) = 1` forests
(drop their lone `v`-fiber, add no `ã̃b`-copy) that the superseded vacuous over-claim assumed
away. Off the Theorem-4.9 critical path. -/
theorem forest_surgery_split [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hD : 2 ≤ bodyBarDim n) {v a b : α} {eₐ e_b e₀ : β}
    (hab : a ≠ b) (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b)
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    (he₀ : e₀ ∉ E(G)) :
    (G.splitOff v a b e₀).deficiency n ≤ G.deficiency n := by
  classical
  haveI : Nonempty α := ⟨a⟩
  have hD1 : 1 ≤ bodyBarDim n := le_trans (by norm_num) hD
  have haV : a ∈ V(G) := hla.right_mem
  have hbV : b ∈ V(G) := hlb.right_mem
  have hvG : v ∈ V(G) := hla.left_mem
  have hVne : V(G).Nonempty := ⟨v, hvG⟩
  set H := G.splitOff v a b e₀ with hH
  have hVHne : V(H).Nonempty := ⟨a, by rw [hH, vertexSet_splitOff]; exact ⟨haV, hav⟩⟩
  -- A base `B` of `M(G̃)`, its balanced packing, and the reroute into `G̃_v^{ab}`.
  obtain ⟨B, hB⟩ := (G.matroidMG n).exists_isBase
  obtain ⟨Fs, hcover, hindep, hpdisj, hmeetv⟩ :=
    exists_balanced_forest_packing hD hav hbv heab hla hlb hdeg2 hB
  obtain ⟨Fs', _, _, hMindep, hcount, _⟩ :=
    forest_surgery_count hD hab hav hbv heab haV hbV he₀ hla hlb hdeg2 Fs hcover hindep
      hpdisj hmeetv
  -- `|⋃ Fs' i| ≤ rank M(G̃_v^{ab})`, and `|⋃ Fs' i| + D = |B|`.
  have hrkZ : (((⋃ i, Fs' i).ncard : ℤ)) ≤ ((H.matroidMG n).rank : ℤ) := by
    exact_mod_cast hMindep.ncard_le_rank
  have hcountZ : (((⋃ i, Fs' i).ncard : ℤ)) + (bodyBarDim n : ℤ) = (B.ncard : ℤ) := by
    exact_mod_cast hcount
  -- The two def = corank identities, and `|V(H)| = |V(G)| − 1`.
  have hBrank := G.isBase_ncard_add_deficiency_eq n hD1 hVne hB
  have hHrank := H.rank_add_deficiency_eq n hD1 hVHne
  have hVHcard : (V(H).ncard : ℤ) = (V(G).ncard : ℤ) - 1 := by
    rw [hH, vertexSet_splitOff, Set.ncard_diff_singleton_of_mem hvG]
    have : 0 < V(G).ncard := Set.ncard_pos (Set.toFinite _) |>.mpr hVne
    omega
  rw [hVHcard, mul_sub, mul_one] at hHrank
  -- Combine: `def(H̃) = D(|V|−2) − rank ≤ D(|V|−2) − (|B|−D) = D(|V|−1) − |B| = def(G̃)`.
  linarith [hrkZ, hcountZ, hBrank, hHrank]

/-! ### The matroid-base 4.3(ii) form at `k = 0` (`lem:case-III-claim-6-11-base`)

Katoh–Tanigawa 2011 Lemma 4.3(ii) at `k = 0` (the splitting-off matroid-base count; KT p.660),
the first missing-green prerequisite of KT Claim 6.11 (the `+1` redundant `ab`-row of §6.4.1;
`notes/Phase22d.md`). For a `0`-dof-graph `G` (`def(G̃) = 0`) with a degree-2 vertex `v`
(neighbours `a ≠ b`, incident edges exactly `eₐ ≠ e_b`, `e₀ ∉ E(G)` fresh), there is a **base**
`B'` of `M(G̃_v^{ab})` whose intersection with the short-circuit fiber `ã̃b = edgeFiber e₀ n` has
fewer than `D − 1 = bodyHingeMult n` copies — i.e. `ã̃b ⊄ B'`, so a redundant `ã̃b`-copy exists.

This is KT's own step-1 argument, run on the corrected forest surgery: rerouting a balanced
`D`-forest packing of a base of `M(G̃)` across `v` (`forest_surgery_count`) yields an
`M(G̃_v^{ab})`-independent set `I' = ⋃ Fs' i` with `|I'| + D = |base|` and `|I' ∩ ã̃b| < D − 1`
(KT Lemma 4.1's two conclusions). At `k = 0` the surgery's deficiency bound
(`splitOff_deficiency_le`, with `def ≥ 0`) gives `def(G̃_v^{ab}) = 0`, so
`rank M(G̃_v^{ab}) = D(|V \ {v}| − 1) = |base| − D = |I'|`; an independent set of full rank is a
base (`Indep.isBase_of_ncard`). That base `I'` carries the fiber bound. Needs `D = bodyBarDim n ≥ 2`
(so `G̃` has edge copies and the fiber `ã̃b` is nonempty). -/
theorem splitOff_exists_base_inter_fiber_lt [DecidableEq β] [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ}
    (hD : 2 ≤ bodyBarDim n) {v a b : α} {eₐ e_b e₀ : β}
    (hab : a ≠ b) (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b)
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    (he₀ : e₀ ∉ E(G)) (hG : G.IsKDof n 0) :
    ∃ B', ((G.splitOff v a b e₀).matroidMG n).IsBase B' ∧
      (B' ∩ edgeFiber e₀ n).ncard < bodyHingeMult n := by
  classical
  haveI : Nonempty α := ⟨a⟩
  have hD1 : 1 ≤ bodyBarDim n := le_trans (by norm_num) hD
  have haV : a ∈ V(G) := hla.right_mem
  have hbV : b ∈ V(G) := hlb.right_mem
  have hvG : v ∈ V(G) := hla.left_mem
  have hVne : V(G).Nonempty := ⟨v, hvG⟩
  set H := G.splitOff v a b e₀ with hH
  have hVHne : V(H).Nonempty := ⟨a, by rw [hH, vertexSet_splitOff]; exact ⟨haV, hav⟩⟩
  -- The reroute: an `M(H̃)`-independent `I' = ⋃ Fs' i`, `|I'| + D = |base|`, `|I' ∩ ã̃b| < D − 1`.
  obtain ⟨B, hB⟩ := (G.matroidMG n).exists_isBase
  obtain ⟨Fs, hcover, hindep, hpdisj, hmeetv⟩ :=
    exists_balanced_forest_packing hD hav hbv heab hla hlb hdeg2 hB
  obtain ⟨Fs', _, _, hMindep, hcount, hfiblt⟩ :=
    forest_surgery_count hD hab hav hbv heab haV hbV he₀ hla hlb hdeg2 Fs hcover hindep
      hpdisj hmeetv
  refine ⟨⋃ i, Fs' i, ?_, hfiblt⟩
  -- At `k = 0`: `def(H̃) = 0` (splitting off does not increase deficiency, and `def ≥ 0`).
  have hdofG : G.deficiency n = 0 := hG
  have hdefH_zero : H.deficiency n = 0 := by
    have hle : H.deficiency n ≤ G.deficiency n :=
      splitOff_deficiency_le hD1 hav hbv heab hla hlb hdeg2 he₀
    have hge : 0 ≤ H.deficiency n := H.deficiency_nonneg n hVHne
    rw [hdofG] at hle; omega
  -- `rank M(H̃) = D(|V \ {v}| − 1) = |base| − D = |I'|`, so `I'` is a base.
  have hHrank := H.rank_add_deficiency_eq n hD1 hVHne
  rw [hdefH_zero, add_zero] at hHrank
  have hBrank := G.isBase_ncard_add_deficiency_eq n hD1 hVne hB
  rw [hdofG, add_zero] at hBrank
  have hVHcard : (V(H).ncard : ℤ) = (V(G).ncard : ℤ) - 1 := by
    rw [hH, vertexSet_splitOff, Set.ncard_diff_singleton_of_mem hvG]
    have : 0 < V(G).ncard := Set.ncard_pos (Set.toFinite _) |>.mpr hVne
    omega
  -- `|I'| = |base| − D = D(|V|−1) − D = D(|V|−2) = rank M(H̃)`.
  have hcountZ : (((⋃ i, Fs' i).ncard : ℤ)) + (bodyBarDim n : ℤ) = (B.ncard : ℤ) := by
    exact_mod_cast hcount
  have hIcardZ : ((⋃ i, Fs' i).ncard : ℤ) = ((H.matroidMG n).rank : ℤ) := by
    rw [hVHcard, mul_sub, mul_one] at hHrank
    linarith [hcountZ, hBrank, hHrank]
  have hIcard : (H.matroidMG n).rank ≤ (⋃ i, Fs' i).ncard := by omega
  haveI : (H.matroidMG n).Finite := Matroid.finite_of_finite (M := H.matroidMG n)
  exact hMindep.isBase_of_ncard hIcard

/-! ### The Gap-3 combinatorial shell — `G − v` is a minimal `k'`-dof-graph with `k' ≤ D − 2`
(`lem:case-III-gap3-minimalKDof`)

The second factor of KT Claim 6.11's discharge (the `+1` redundant `ab`-row of §6.4.1;
`notes/Phase22d.md`), the *combinatorial* half of Katoh–Tanigawa 2011's nested-IH step
(KT p. 684–685, eq. (6.22) setup). With `G` a minimal `0`-dof-graph and `v` a degree-2
vertex, the vertex-removal `G_v := G − v = G_v^{ab} − ab` is itself a **minimal `k'`-dof-graph**
for `k' := def(G̃_v)`, and that deficiency is bounded by `0 ≤ k' ≤ D − 2`. The minimality is
KT Lemma 3.3 (`subgraph_minimality`, `G_v ≤ G`); the bound is the new content here, read off
the Gap-2 base.

The `k' ≤ D − 2` bound runs KT's own count on the Gap-2 base `B'` of `M(G̃_v^{ab})` with
`h := |ãb ∩ B'| < D − 1` (`splitOff_exists_base_inter_fiber_lt`): the surviving part
`B' ∖ ãb` lands in `E(G̃_v)` (`edgeSet_mulTilde_splitOff_diff_fiber`) and is independent in
`M(G̃_v) = M(G̃_v^{ab}) ↾ E(G̃_v)` (`matroidMG_restrict_mulTilde`, `G̃_v ≤ G̃_v^{ab}` via
`mulTilde_removeVertex_le_splitOff`), so
`rank M(G̃_v) ≥ |B' ∖ ãb| = |B'| − h`. At `k = 0` the splitting-off is itself `0`-dof
(`splitOff_deficiency_le` + nonneg), so `|B'| = D(|V ∖ v| − 1)`; with the def\,=\,corank
identity (`rank_add_deficiency_eq`, same vertex set `V(G) ∖ {v}`) this gives
`def(G̃_v) = D(|V ∖ v| − 1) − rank M(G̃_v) ≤ h < D − 1`, i.e. `≤ D − 2`. The lower bound
`0 ≤ def(G̃_v)` is `deficiency_nonneg` (`V(G_v)` is nonempty, containing `a`).

This is the green combinatorial shell of Gap 3: pure `M(G̃)` matroid theory, no rigidity
matrix. The eq. (6.22) *rank-at-the-fixed-seed* transfer it feeds — the genuinely-new analytic
kernel — is the next, deferred sub-phase (`notes/Phase22d.md` *Deferred sub-phases*). -/
theorem splitOff_removeVertex_minimalKDof [DecidableEq β] [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ}
    (hD : 2 ≤ bodyBarDim n) {v a b : α} {eₐ e_b e₀ : β}
    (hab : a ≠ b) (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b)
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    (he₀ : e₀ ∉ E(G)) (hG : G.IsMinimalKDof n 0) :
    (G.removeVertex v).IsMinimalKDof n ((G.removeVertex v).deficiency n) ∧
      0 ≤ (G.removeVertex v).deficiency n ∧
      (G.removeVertex v).deficiency n ≤ (bodyBarDim n : ℤ) - 2 := by
  classical
  haveI : Nonempty α := ⟨a⟩
  have hD1 : 1 ≤ bodyBarDim n := le_trans (by norm_num) hD
  have haV : a ∈ V(G) := hla.right_mem
  have hvG : v ∈ V(G) := hla.left_mem
  set Gv := G.removeVertex v with hGvdef
  set H := G.splitOff v a b e₀ with hHdef
  have hVne : V(G).Nonempty := ⟨v, hvG⟩
  have hVvne : V(Gv).Nonempty := ⟨a, by rw [hGvdef, vertexSet_removeVertex]; exact ⟨haV, hav⟩⟩
  have hVHne : V(H).Nonempty := ⟨a, by rw [hHdef, vertexSet_splitOff]; exact ⟨haV, hav⟩⟩
  -- Minimality: `G_v ≤ G` and `G` minimal `0`-dof, so `G_v` is minimal `def(G̃_v)`-dof.
  have hminimal : Gv.IsMinimalKDof n (Gv.deficiency n) :=
    subgraph_minimality (G.removeVertex_le v) hG rfl
  refine ⟨hminimal, Gv.deficiency_nonneg n hVvne, ?_⟩
  -- The Gap-2 base `B'` of `M(G̃_v^{ab})`: `|ãb ∩ B'| = h < D − 1`.
  obtain ⟨B', hB', hfiblt⟩ :=
    splitOff_exists_base_inter_fiber_lt hD hab hav hbv heab hla hlb hdeg2 he₀ hG.1
  -- `def(G̃_v^{ab}) = 0` at `k = 0`, so `|B'| = D(|V ∖ v| − 1)`.
  have hdefH_zero : H.deficiency n = 0 := by
    have hle : H.deficiency n ≤ G.deficiency n :=
      splitOff_deficiency_le hD1 hav hbv heab hla hlb hdeg2 he₀
    have hge : 0 ≤ H.deficiency n := H.deficiency_nonneg n hVHne
    rw [(hG.1 : G.deficiency n = 0)] at hle; omega
  have hB'card := H.isBase_ncard_add_deficiency_eq n hD1 hVHne hB'
  rw [hdefH_zero, add_zero] at hB'card
  -- `B' ∖ ãb ⊆ E(G̃_v)` (surviving fibers) and independent in `M(G̃_v)`.
  have hdiffsub : B' \ edgeFiber e₀ n ⊆ E(Gv.mulTilde n) := by
    rw [hGvdef, ← edgeSet_mulTilde_splitOff_diff_fiber n he₀]
    exact Set.diff_subset_diff_left hB'.subset_ground
  have hdiffindepGv : (Gv.matroidMG n).Indep (B' \ edgeFiber e₀ n) := by
    have hindepH : (H.matroidMG n).Indep (B' \ edgeFiber e₀ n) := hB'.indep.subset diff_subset
    rw [hGvdef] at hdiffsub ⊢
    rw [← matroidMG_restrict_mulTilde (G.removeVertex_le_splitOff he₀) n,
      Matroid.restrict_indep_iff]
    exact ⟨hindepH, hdiffsub⟩
  have hdiffleZ : ((B' \ edgeFiber e₀ n).ncard : ℤ) ≤ ((Gv.matroidMG n).rank : ℤ) := by
    exact_mod_cast hdiffindepGv.ncard_le_rank
  -- `|B' ∖ ãb| = |B'| − |B' ∩ ãb|`.
  have hsplit : (B' ∩ edgeFiber e₀ n).ncard + (B' \ edgeFiber e₀ n).ncard = B'.ncard :=
    Set.ncard_inter_add_ncard_diff_eq_ncard B' _ (Set.toFinite _)
  have hsplitZ : ((B' ∩ edgeFiber e₀ n).ncard : ℤ) + ((B' \ edgeFiber e₀ n).ncard : ℤ)
      = (B'.ncard : ℤ) := by exact_mod_cast hsplit
  -- The def = corank identity for `G̃_v`; `V(G_v) = V(H) = V(G) ∖ {v}`.
  have hGvrank := Gv.rank_add_deficiency_eq n hD1 hVvne
  have hVeq : (V(Gv).ncard : ℤ) = (V(H).ncard : ℤ) := by
    rw [hGvdef, hHdef, vertexSet_removeVertex, vertexSet_splitOff]
  -- `h < D − 1`, and `def(G̃_v) ≤ h`, so `def(G̃_v) ≤ D − 2`.
  have hfibltZ : ((B' ∩ edgeFiber e₀ n).ncard : ℤ) < (bodyHingeMult n : ℤ) := by
    exact_mod_cast hfiblt
  have hHM : (bodyHingeMult n : ℤ) = (bodyBarDim n : ℤ) - 1 := by rw [bodyHingeMult]; omega
  -- `def(G̃_v) = D(|V∖v|−1) − rank ≤ D(|V∖v|−1) − (|B'| − h) = h < D − 1`.
  rw [hVeq] at hGvrank
  linarith [hdiffleZ, hsplitZ, hB'card, hGvrank, hfibltZ, hHM]

/-- **The forest-surgery route to the KT-4.3 splitting-off deficiency bound**
(`cor:forest-surgery-deficiency`; narrative bridge). The deficiency bound
`def(G̃_v^{ab}) ≤ def(G̃)` that `dof_tracking` / Theorem 4.9 consume — landed on the
critical path by the deficiency-count `splitOff_deficiency_le` — is *also* the exact
conclusion of the off-path forest surgery `forest_surgery_split` (KT 4.1, splitting-off
direction). This lemma records that alternative route: it derives the same bound from the
forest reroute, the route Katoh–Tanigawa actually take. It is `@[deprecated]` in favour of
`splitOff_deficiency_le` because that deficiency-count lemma is the route the critical path
uses (and carries the weaker `1 ≤ bodyBarDim n`, no `a ≠ b`); this shim exists solely to
anchor the blueprint's narrative claim that the forest surgery reaches the same place, with
no Lean caller. The `@[deprecated]` shim pattern (and the `(since := "narrative-bridge")`
sentinel) is documented in `CombinatorialRigidity/CLAUDE.md` *Engineering conventions*. -/
@[deprecated splitOff_deficiency_le (since := "narrative-bridge")]
theorem splitOff_deficiency_le_of_forest_surgery [Finite α] [Finite β] {G : Graph α β}
    {n : ℕ} (hD : 2 ≤ bodyBarDim n) {v a b : α} {eₐ e_b e₀ : β}
    (hab : a ≠ b) (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b)
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    (he₀ : e₀ ∉ E(G)) :
    (G.splitOff v a b e₀).deficiency n ≤ G.deficiency n :=
  forest_surgery_split hD hab hav hbv heab hla hlb hdeg2 he₀

end Graph
