/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Induction.SplitOffDeficiency

/-!
# The combinatorial induction — the reducible vertex (`sec:molecular-induction`)

Phase 20 (molecular-conjecture program; see `notes/MolecularConjecture.md`). On top of the
deficiency tracking (`Induction/SplitOffDeficiency`), this file locates the degree-2 vertex the
reduction step operates on (Katoh–Tanigawa 2011 §4):

* every base of `M(G̃)` meets `≥ D` of the fibers at a degree-2 vertex, with the
  forest-packing redistribution kernel and one rebalancing move of the descent;
* the total fiber count and the **edge-count bound with no proper rigid subgraph**
  (`no_rigid_edge_count`, `lem:no-rigid-edge-count`, the F′ core);
* the **reducible vertex** (`exists_degree_le_two` / `exists_degree_eq_two`,
  `lem:reducible-vertex`, the F″ core), upgrading degree `≤ 2` to `= 2` via two-edge-connectivity;
* the graph operations `edgeSplit`, `collapseTo`, and the **rigid-subgraph contraction**
  `rigidContract` (`def:rigid-contraction`) with their basic lemmas.

The contraction-minimality and forest-surgery layers build on top in `Contraction` and
`ForestSurgery`. See `ROADMAP.md` §20 / `notes/Phase20.md` and the `sec:molecular-induction`
dep-graph.
-/

namespace Graph

open Set Matroid

variable {α β : Type*}

/-! ### Every base of `M(G̃)` meets ≥ `D` of the fibers at a degree-2 vertex
(`lem:forest-surgery-split`, the balanced-packing counting half)

The deferred forest surgery (`lem:forest-surgery-split`, KT~4.1) is gated on the
*balanced-packing* assumption Katoh–Tanigawa gloss (`rem:kt-lemma-41`~(2)): that a base of
`M(G̃)` admits a `D`-forest partition with **every** one of the `D` forests meeting the
degree-2 vertex `v`. The pure-counting half of that assumption is *true* and provable on
the green deficiency infrastructure: every base `B` of `M(G̃)` already contains **at least
`D`** of the `2(D−1)` fibers incident to `v`.

The argument is a rank count, **not** a forest reroute. Deleting `v`'s fibers from `B`
lands inside `E((G_v)̃)` (the only `v`-incident `G`-edges are `eₐ`, `e_b` by `hdeg2`, so a
surviving fiber's underlying edge avoids `v`), where the remainder is independent in
`M((G_v)̃) = M(G̃) ↾ E((G_v)̃)` (`matroidMG_restrict_mulTilde`). Hence
`|B ∖ v-fibers| ≤ rank M((G_v)̃)`, and the def\,$=$\,corank bridge
(`isBase_ncard_add_deficiency_eq` / `rank_add_deficiency_eq`) turns
`|B ∩ v-fibers| = |B| − |B ∖ v-fibers|` into
`≥ D + (def((G_v)̃) − def(G̃))`, which is `≥ D` by the removal bound
`removeVertex_deficiency_ge` (KT~4.4, `def(G̃) ≤ def((G_v)̃)`). Needs `2 ≤ bodyBarDim n`.

This reduces the open balanced-packing assumption to a *redistribution* question — given
`≥ D` `v`-fibers (each forest taking at most one `va`-copy and one `vb`-copy), can the `D`
forests be rechosen so each meets `v`? — isolating exactly the combinatorial step KT's
proof omits a justification for (`rem:kt-lemma-41`~(2)); the counting obstruction
("pigeonhole when `h < D`") cannot arise. -/
theorem isBase_vfiber_ncard_ge [DecidableEq β] [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hD : 2 ≤ bodyBarDim n) {v a b : α} {eₐ e_b : β}
    (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b)
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    {B : Set (β × Fin (bodyHingeMult n))} (hB : (G.matroidMG n).IsBase B) :
    bodyBarDim n ≤ (B ∩ (edgeFiber eₐ n ∪ edgeFiber e_b n)).ncard := by
  classical
  haveI : Nonempty α := ⟨a⟩
  have hD1 : 1 ≤ bodyBarDim n := le_trans (by norm_num) hD
  set H := G.removeVertex v with hH
  have hle : H ≤ G := by rw [hH, removeVertex]; exact G.deleteVerts_le
  have hvG : v ∈ V(G) := hla.left_mem
  have hVne : V(G).Nonempty := ⟨v, hvG⟩
  have hVHne : V(H).Nonempty := ⟨a, by rw [hH, vertexSet_removeVertex]; exact ⟨hla.right_mem, hav⟩⟩
  -- `v`-fibers and their cardinality `2(D−1)` is not needed; we only need the count `≥ D`.
  set vfib := edgeFiber eₐ n ∪ edgeFiber e_b n with hvfib
  -- The base lives inside `E(G̃)`.
  have hBground : B ⊆ E(G.mulTilde n) := by
    have := hB.subset_ground; rwa [matroidMG] at this
  -- Step 1: `B ∖ v-fibers ⊆ E((G_v)̃)`.
  have hdiffsub : B \ vfib ⊆ E(H.mulTilde n) := by
    rintro p ⟨hpB, hpnot⟩
    have hpE : p ∈ E(G.mulTilde n) := hBground hpB
    rw [mem_edgeSet_mulTilde] at hpE
    -- `p.1` is a `G`-edge; it is not `eₐ`/`e_b` (else `p ∈ vfib`), hence avoids `v`.
    have hp1ne : p.1 ≠ eₐ ∧ p.1 ≠ e_b := by
      constructor <;> intro hc <;> apply hpnot
      · exact Or.inl (by rw [edgeFiber, Set.mem_setOf_eq]; exact hc)
      · exact Or.inr (by rw [edgeFiber, Set.mem_setOf_eq]; exact hc)
    -- `p.1 ∈ E(G)` survives in `H = G_v`: neither endpoint is `v` (else `p.1 ∈ {eₐ, e_b}`).
    obtain ⟨x, y, hlink⟩ := G.exists_isLink_of_mem_edgeSet hpE
    have hxv : x ≠ v := by rintro rfl; exact absurd (hdeg2 p.1 y hlink) (by tauto)
    have hyv : y ≠ v := by rintro rfl; exact absurd (hdeg2 p.1 x hlink.symm) (by tauto)
    have hlinkH : H.IsLink p.1 x y := by rw [hH, removeVertex_isLink]; exact ⟨hlink, hxv, hyv⟩
    rw [mem_edgeSet_mulTilde]; exact hlinkH.edge_mem
  -- Step 2: `B ∖ v-fibers` is independent in `M((G_v)̃)`, so `|B ∖ v-fibers| ≤ rank M((G_v)̃)`.
  have hdiffindepG : (G.matroidMG n).Indep (B \ vfib) := hB.indep.subset diff_subset
  have hdiffindepH : (H.matroidMG n).Indep (B \ vfib) := by
    rw [← matroidMG_restrict_mulTilde hle n, Matroid.restrict_indep_iff]
    exact ⟨hdiffindepG, hdiffsub⟩
  have hdiffleZ : ((B \ vfib).ncard : ℤ) ≤ ((H.matroidMG n).rank : ℤ) := by
    exact_mod_cast hdiffindepH.ncard_le_rank
  -- Step 3: the two rank/deficiency identities, and `|V(H)| = |V(G)| − 1`.
  have hBrank := G.isBase_ncard_add_deficiency_eq n hD1 hVne hB
  have hHrank := H.rank_add_deficiency_eq n hD1 hVHne
  have hVGpos : 0 < V(G).ncard := Set.ncard_pos (Set.toFinite _) |>.mpr hVne
  have hVHcard : (V(H).ncard : ℤ) = (V(G).ncard : ℤ) - 1 := by
    rw [hH, vertexSet_removeVertex, Set.ncard_diff_singleton_of_mem hvG]
    omega
  rw [hVHcard] at hHrank
  -- Step 4: combine. `|B ∩ vfib| = |B| − |B ∖ vfib| ≥ D + (def(G̃ᵥ) − def(G̃)) ≥ D`.
  have hremoval := removeVertex_deficiency_ge hD hav hbv heab hla hlb hdeg2
  have hsplit : (B ∩ vfib).ncard + (B \ vfib).ncard = B.ncard :=
    Set.ncard_inter_add_ncard_diff_eq_ncard B vfib (Set.toFinite _)
  have hsplitZ : ((B ∩ vfib).ncard : ℤ) + ((B \ vfib).ncard : ℤ) = (B.ncard : ℤ) := by
    exact_mod_cast hsplit
  -- `hdiffleZ : |B∖vfib| ≤ rank M(G̃ᵥ)`; `hHrank : rank M(G̃ᵥ) + def(G̃ᵥ) = D(|V(G)|−1)`;
  -- `hremoval : def(G̃) ≤ def(G̃ᵥ)`; `hBrank : |B| + def(G̃) = D(|V(G)|−1)`; `hsplitZ`.
  have key : (bodyBarDim n : ℤ) ≤ ((B ∩ vfib).ncard : ℤ) := by
    linarith [hdiffleZ, hremoval, hBrank, hsplitZ, hHrank]
  exact_mod_cast key

/-! ### Redistribution kernel: a `v`-avoiding forest accepts any `v`-fiber as a pendant
(`lem:forest-surgery-split`, the balanced-packing redistribution half)

With the *counting* half of the balanced-packing assumption discharged
(`isBase_vfiber_ncard_ge`: a base meets `≥ D` of the `2(D−1)` fibers at the degree-2
vertex `v`), the residual *redistribution* question (`rem:kt-lemma-41`~(2)) is: given the
`D`-forest packing of a base and `≥ D` `v`-fibers among them, can the forests be rechosen
so each meets `v`? This kernel resolves it **affirmatively** — confirming Katoh–Tanigawa's
Lemma 4.1 proof has a *gap, not an error* (the balanced packing is achievable for a base).

The mechanism turns entirely on **`v` having degree 2** in `G`. A forest `F` (a
`(G̃).cycleMatroid`-independent fiber set) that contains no `v`-incident fiber has `v`
isolated in `G̃ ↾ F`; so for any `v`-fiber `x` (a copy of `eₐ` or `e_b`), `x` is a *pendant*
edge in `G̃ ↾ insert x F` — its `v`-endpoint has degree 1 — hence a bridge, and adding a
bridge to a forest keeps it a forest. So `insert x F` is again `(G̃).cycleMatroid`-
independent. The repacking descent (move a `v`-fiber from a forest holding two of them
into a `v`-avoiding forest; the pigeonhole donor always exists since `≥ D` fibers sit in
`< D` non-empty forests) strictly raises the number of `v`-meeting forests, terminating
with every forest meeting `v`. This kernel is the single load-bearing step of that descent;
the descent itself (a `Fin D → Set _` repacking with a well-founded measure) is the
remaining surgery work, off the Theorem-4.9 critical path. -/

/-- **A `v`-avoiding forest accepts a `v`-fiber as a pendant** (`lem:forest-surgery-split`,
balanced-packing redistribution kernel; Katoh–Tanigawa 2011 Lemma 4.1 p.660). Let `F` be a
`(G̃).cycleMatroid`-independent fiber set (a "forest") whose edges all *avoid* `v`
(`∀ p ∈ F, ¬ (G̃).Inc p v`), and let `x` be a fiber joining `v` to a distinct vertex `w`
(`(G̃).IsLink x v w`, `w ≠ v` — a *non-loop* copy of a `v`-incident `G`-edge, exactly the
shape of the `va`/`vb` fibers at a degree-2 vertex). Then `insert x F` is still
`(G̃).cycleMatroid`-independent. (The non-loop hypothesis is essential: a loop at `v` is
itself a cycle, so `insert (loop) F` is never acyclic.)

Proof: by `cycleMatroid_indep`, `insert x F` is acyclic iff `G̃ ↾ insert x F` is a forest;
since `F` is acyclic, it suffices (`IsForest.of_deleteEdges_singleton`) that `x` is a bridge
of `G̃ ↾ insert x F`. `x` is a bridge iff `v` and `w` are disconnected after deleting `x`
(`IsLink.isBridge_iff_not_connBetween`). But in `(G̃ ↾ insert x F) ＼ {x}` the vertex `v` is
*isolated*: its only `insert x F`-edge was `x`, now deleted, and no `F`-edge touches `v`. So
`Isolated.connBetween_iff_eq` forces any `v`–`w` connection to have `v = w`, contradicting
`w ≠ v`. This is the single combinatorial step KT's Lemma 4.1 base-case proof needs and
glosses; it holds because `v` has degree 2 (so a `v`-avoiding forest has `v` isolated). -/
theorem acyclicSet_insert_vfiber_of_not_inc {G : Graph α β} {n : ℕ}
    {F : Set (β × Fin (bodyHingeMult n))} {x : β × Fin (bodyHingeMult n)} {v w : α}
    (hF : ((G.mulTilde n).cycleMatroid).Indep F)
    (hxvw : (G.mulTilde n).IsLink x v w) (hwv : w ≠ v)
    (hFv : ∀ p ∈ F, ¬ (G.mulTilde n).Inc p v) :
    ((G.mulTilde n).cycleMatroid).Indep (insert x F) := by
  classical
  set K := G.mulTilde n with hK
  rw [Graph.cycleMatroid_indep] at hF ⊢
  have hxE : x ∈ E(K) := hxvw.edge_mem
  have hFE : F ⊆ E(K) := hF.1
  -- `insert x F ⊆ E(K)`.
  rw [Graph.isAcyclicSet_iff]
  refine ⟨Set.insert_subset hxE hFE, ?_⟩
  -- It suffices that `x` is a bridge of `K ↾ insert x F`, since deleting it leaves a forest.
  set R := K ↾ insert x F with hR
  have hRforest_del : (R ＼ {x}).IsForest := by
    have hFforest : (K ↾ F).IsForest := (Graph.restrict_isForest_iff hFE).mpr hF
    refine hFforest.anti ?_
    rw [hR, Graph.restrict_deleteEdges]
    refine Graph.restrict_le_restrict (Set.inter_subset_inter_right _ ?_)
    rintro p ⟨hpmem, hpne⟩
    exact (Set.mem_insert_iff.mp hpmem).resolve_left hpne
  have hxlinkR : R.IsLink x v w := by
    rw [hR, Graph.restrict_isLink]; exact ⟨Set.mem_insert _ _, hxvw⟩
  -- `x` is a bridge of `R`: deleting it isolates `v`, so no `v`–`w` path remains.
  have hbridge : R.IsBridge x := by
    rw [hxlinkR.isBridge_iff_not_connBetween]
    intro hconn
    -- `v` is isolated in `R ＼ {x}`.
    have hvisol : (R ＼ {x}).Isolated v := by
      constructor
      · intro e hinc
        rw [hR] at hinc
        have hincK : K.Inc e v ∧ e ∈ insert x F ∧ e ∉ ({x} : Set _) := by
          rw [Graph.deleteEdges_inc, Graph.restrict_inc] at hinc; tauto
        obtain ⟨hincK, hmem, hne⟩ := hincK
        have heF : e ∈ F := (Set.mem_insert_iff.mp hmem).resolve_left (by simpa using hne)
        exact hFv e heF hincK
      · have : v ∈ V(K) := hxvw.left_mem
        rw [Graph.vertexSet_deleteEdges, hR, Graph.vertexSet_restrict]
        exact this
    exact hwv ((hvisol.connBetween_iff_eq).mp hconn).symm
  exact Graph.IsForest.of_deleteEdges_singleton hbridge hRforest_del

/-! ### One rebalancing move of the forest-packing descent
(`lem:forest-surgery-split`, the balanced-packing redistribution descent step)

The two halves of the balanced-packing assumption — the counting half
(`isBase_vfiber_ncard_ge`: a base meets `≥ D` of the `v`-fibers) and the redistribution
kernel (`acyclicSet_insert_vfiber_of_not_inc`: a `v`-avoiding forest absorbs a free
`v`-fiber as a pendant) — assemble into the balanced packing through a **finite repacking
descent**: as long as some forest `Fs j` of the `D`-forest packing of a base avoids `v`,
*move* a spare `v`-fiber `x` into it, raising the count of `v`-meeting forests.

This lemma is the single load-bearing step of that descent: the **move preserves the
packing**. Given a forest packing `Fs : Fin D → Set _` covering `I` (`⋃ i, Fs i = I`, each
`Fs i` a `(G̃).cycleMatroid`-independent fiber set), a designated `v`-avoiding forest
`Fs j` (`∀ p ∈ Fs j, ¬ (G̃).Inc p v`), and a `v`-fiber `x ∈ I` (`(G̃).IsLink x v w`, `w ≠ v`),
the re-choice `Fs' i = insert x (Fs j)` at `i = j` and `Fs i ∖ {x}` elsewhere is again a
forest packing covering `I`. The recipient `Fs j` stays acyclic by the kernel (`x` is a
pendant at the isolated `v`); every donor `Fs i ∖ {x}` stays acyclic as a subset; and the
union is unchanged because `x ∈ I` is re-added at `j` while removed elsewhere. The new
forest `Fs' j` *meets* `v` (it contains `x`), so a descent driven by the count of
`v`-avoiding forests terminates with a balanced packing. The descent's well-founded measure
and the pigeonhole that always supplies such a spare `x` (`≥ D` fibers among `< D` non-empty
forests) are the remaining surgery work, off the Theorem-4.9 critical path. -/
theorem exists_packing_move_of_not_inc {G : Graph α β} {n : ℕ}
    {I : Set (β × Fin (bodyHingeMult n))}
    {Fs : Fin (bodyBarDim n) → Set (β × Fin (bodyHingeMult n))}
    (hcover : ⋃ i, Fs i = I) (hindep : ∀ i, ((G.mulTilde n).cycleMatroid).Indep (Fs i))
    {x : β × Fin (bodyHingeMult n)} {v w : α}
    (hxvw : (G.mulTilde n).IsLink x v w) (hwv : w ≠ v) (hxI : x ∈ I)
    {j : Fin (bodyBarDim n)} (hFjv : ∀ p ∈ Fs j, ¬ (G.mulTilde n).Inc p v) :
    ∃ Fs' : Fin (bodyBarDim n) → Set (β × Fin (bodyHingeMult n)),
      (⋃ i, Fs' i = I) ∧ (∀ i, ((G.mulTilde n).cycleMatroid).Indep (Fs' i)) ∧
        x ∈ Fs' j := by
  classical
  refine ⟨fun i => if i = j then insert x (Fs j) else Fs i \ {x}, ?_, ?_, ?_⟩
  · -- The union is unchanged: `x` is re-added at `j`, removed elsewhere, and `x ∈ I`.
    apply Set.Subset.antisymm
    · rintro p hp
      rw [Set.mem_iUnion] at hp
      obtain ⟨i, hi⟩ := hp
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl] at hi
        rcases Set.mem_insert_iff.mp hi with rfl | hi'
        · exact hxI
        · rw [← hcover]; exact Set.mem_iUnion.mpr ⟨i, hi'⟩
      · simp only [if_neg hij] at hi
        rw [← hcover]; exact Set.mem_iUnion.mpr ⟨i, hi.1⟩
    · rw [← hcover]
      rintro p hp
      rw [Set.mem_iUnion] at hp ⊢
      obtain ⟨i, hi⟩ := hp
      by_cases hpx : p = x
      · exact ⟨j, by rw [if_pos rfl]; exact Set.mem_insert_iff.mpr (Or.inl hpx)⟩
      · by_cases hij : i = j
        · subst hij
          exact ⟨i, by rw [if_pos rfl]; exact Set.mem_insert_iff.mpr (Or.inr hi)⟩
        · exact ⟨i, by simp only [if_neg hij]; exact ⟨hi, by simpa using hpx⟩⟩
  · intro i
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte]
      exact acyclicSet_insert_vfiber_of_not_inc (hindep i) hxvw hwv hFjv
    · simp only [if_neg hij]
      exact (hindep i).subset Set.diff_subset
  · simp only [↓reduceIte]; exact Set.mem_insert _ _

/-! ### Total fiber count of `G̃` (`lem:no-rigid-edge-count`, support)

The KT 4.5(i) edge-count bound (`lem:no-rigid-edge-count`, the prerequisite for the
existence of a reducible degree-2 vertex, KT 4.6) is a statement about `|E(G)|`, while the
matroid `M(G̃)` lives over the fiber set `E(G̃)`. The bridge is the elementary cardinality
identity `|E(G̃)| = (D − 1)·|E(G)|`: the multiplied graph `G̃ = (D−1)·G` replaces each edge
of `G` by `D − 1 = bodyHingeMult n` parallel copies (`Graph.edgeMultiply`), so its edge set
has `(D − 1)·|E(G)|` fibers. This is the per-edge `edgeFiber_ncard` (`|ẽ| = D − 1`) summed
over the `|E(G)|` edges, packaged as a single `mulTilde`-level count. It is the support fact
that lets the matroidal corank bound `corank M(G̃) ≤ D − 2` (the substantive content of KT
4.5(i), still to land — see `notes/Phase20.md` *Hand-off*) be read off as the graph-level
edge bound `(D−1)|E| < D(|V|−1) + (D−1)`, and it also feeds the degree-handshake
`∑_v d(v) = 2|E|` of the average-degree count (KT 4.6, the `F″` sub-step). -/

/-- **The fiber set of `G̃` has `(D − 1)·|E(G)|` elements** (`lem:no-rigid-edge-count`,
support): `|E(G̃)| = bodyHingeMult n · |E(G)| = (D − 1)·|E(G)|`, since the multiplied graph
`G̃ = (D−1)·G` (`mulTilde`, `Graph.edgeMultiply (bodyHingeMult n)`) replaces each edge of `G`
by `D − 1 = bodyHingeMult n` parallel fiber copies. Immediate from
`edgeMultiply_edgeSet_ncard`. This bridges the matroidal corank of `M(G̃)` (which counts
fibers of `E(G̃)`) to the graph-level edge count `|E(G)|` of the KT 4.5(i)/4.6 edge bound. -/
theorem mulTilde_edgeSet_ncard [Finite β] (G : Graph α β) (n : ℕ) :
    E(G.mulTilde n).ncard = bodyHingeMult n * E(G).ncard := by
  rw [mulTilde, edgeMultiply_edgeSet_ncard]

/-! ### The edge-count bound with no proper rigid subgraph (`lem:no-rigid-edge-count`, F′ core)

The matroidal heart of Katoh–Tanigawa 2011 Lemma 4.5(i) (printed p.663). For a minimal
`0`-dof-graph `G` with **no proper rigid subgraph** and `D = bodyBarDim n ≥ 2`, the redundant
fibers of `M(G̃)` concentrate on a single edge-fiber `ẽ` — equivalently the corank is at most
`D − 2` — giving the graph-level edge bound `(D−1)|E| < D(|V|−1) + (D−1)`.

The argument is Katoh–Tanigawa's fundamental-circuit swap (KT eq. 4.3, `Ẽ∖ẽ ⊂ B*`). Fix an
edge `e`, let `h* = minₐ |ẽ ∩ B|` over bases of `M(G̃)`, attained at `B*`; minimality of `G`
forces `h* ≥ 1` (every base meets `ẽ`). For any out-of-`B*` fiber `f ∉ ẽ`, the fundamental
circuit `X = fundCircuit f B*` induces a rigid `G[V(X)]` and — no proper rigid subgraph —
spans `V` (`fundCircuit_inducedSpan_vertexSet_eq`). Then `X ∩ ẽ ≠ ∅`: otherwise `X ⊆ Ẽ∖ẽ` and
`X − ej` (any `ej ∈ X`) is an independent set of full rank `D(|V|−1)` (it is `(D,D)`-tight on
`V(X) = V` by `circuit_induces_isTight`), hence a *base* avoiding `ẽ` — contradicting
minimality. The `X∩ẽ≠∅` step is therefore a direct base-meets-fiber contradiction, **not**
forest reasoning. A base exchange `B = insert f B* − ej` (with `ej ∈ X ∩ ẽ`, independent by
`Indep.mem_fundCircuit_iff`) then has `|B ∩ ẽ| = h* − 1 < h*`, contradicting the choice of
`B*`. So `Ẽ∖ẽ ⊆ B*`, and `|E(G̃)| = |B*| + (|ẽ| − h*) ≤ D(|V|−1) + (D − 2)`. -/

/-- **KT Lemma 4.5(i) edge-count bound, F′ swap core** (`lem:no-rigid-edge-count`;
Katoh–Tanigawa 2011 Lemma 4.5(i), printed p.663). For a minimal `0`-dof-graph `G` with **no
proper rigid subgraph** and `D = bodyBarDim n ≥ 2`,
`(D − 1)·|E(G)| < D·(|V(G)| − 1) + (D − 1)` (in `ℤ`, `|V|−1` written `V(G).ncard - 1`).
Equivalently `corank M(G̃) ≤ D − 2`: the fibers redundant in `M(G̃)` all concentrate on a
single edge-fiber. This is the edge bound Katoh–Tanigawa use to force a low-degree vertex
(`lem:reducible-vertex`).

Proof: the fundamental-circuit swap (KT eq. 4.3). For a fixed edge `e`, the minimum
`h* = minₐ |ẽ ∩ B|` over bases is `≥ 1` by minimality; every out-of-base fiber `f ∉ ẽ` has a
fundamental circuit spanning `V` (`fundCircuit_inducedSpan_vertexSet_eq`) that must meet `ẽ`
(else `X − ej` is a base avoiding `ẽ`, contradicting minimality — a base-meets-fiber step, not
forest reasoning), so a base exchange drops `|B ∩ ẽ|` below `h*` unless `f ∈ B*`. Hence
`Ẽ∖ẽ ⊆ B*`, and `|E(G̃)| = |B*| + (|ẽ| − h*) ≤ D(|V|−1) + (D−2)`. -/
theorem no_rigid_edge_count [DecidableEq β] [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hD : 2 ≤ bodyBarDim n) (hVne : V(G).Nonempty) (hG : G.IsMinimalKDof n 0)
    (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) :
    (bodyHingeMult n : ℤ) * E(G).ncard
      < bodyBarDim n * ((V(G).ncard : ℤ) - 1) + bodyHingeMult n := by
  classical
  haveI : G.Loopless := loopless_of_isMinimalKDof hG
  have hD1 : 1 ≤ bodyBarDim n := le_trans (by norm_num) hD
  have hHM : (bodyHingeMult n : ℤ) = (bodyBarDim n : ℤ) - 1 := by rw [bodyHingeMult]; omega
  set M := G.matroidMG n with hM
  -- `|E(G̃)| = (D−1)·|E(G)|`.
  have hEcard : E(G.mulTilde n).ncard = bodyHingeMult n * E(G).ncard := mulTilde_edgeSet_ncard G n
  -- Case `E(G) = ∅`: LHS `= 0`, RHS `≥ D−1 ≥ 1 > 0`.
  rcases eq_empty_or_nonempty E(G) with hEempty | hEne
  · rw [hEempty, Set.ncard_empty]
    have hVpos : 1 ≤ V(G).ncard := hVne.ncard_pos
    push_cast
    nlinarith [hD, hVpos]
  -- Pick an edge `e`; its fiber `ẽ = edgeFiber e n ⊆ E(G̃)`, `|ẽ| = D−1`.
  obtain ⟨e, he⟩ := hEne
  have hfiberE : edgeFiber e n ⊆ E(G.mulTilde n) := by
    intro p hp
    rw [mem_edgeSet_mulTilde, (show p.1 = e from hp)]; exact he
  -- The set of bases is finite and nonempty; `h* = minₐ |ẽ ∩ B|` is attained at `Bs`.
  have hbasesFin : {B | M.IsBase B}.Finite := by
    apply Set.Finite.subset ((Set.toFinite E(G.mulTilde n)).finite_subsets)
    intro B hB
    rw [Set.mem_setOf_eq] at hB
    exact hB.subset_ground
  have hbasesNe : {B | M.IsBase B}.Nonempty := M.exists_isBase
  obtain ⟨Bs, hBsmem, hBsmin⟩ :=
    Set.exists_min_image {B | M.IsBase B} (fun B => (edgeFiber e n ∩ B).ncard) hbasesFin hbasesNe
  rw [Set.mem_setOf_eq] at hBsmem
  set hstar := (edgeFiber e n ∩ Bs).ncard with hhstar
  -- `h* ≥ 1` from minimality: every base meets `ẽ`.
  have hstarpos : 1 ≤ hstar := by
    have hmeet := hG.2 Bs hBsmem e he
    rw [Set.inter_comm] at hmeet
    exact hmeet.ncard_pos
  -- Eq 4.3: `E(G̃) ∖ ẽ ⊆ Bs`.
  -- `|Bs| = D(|V|−1)` since `G` is `0`-dof.
  have hBscard : (Bs.ncard : ℤ) = bodyBarDim n * ((V(G).ncard : ℤ) - 1) := by
    have hb := G.isBase_ncard_add_deficiency_eq n hD1 hVne hBsmem
    rw [hM] at hBsmem
    rw [(hG.1 : G.deficiency n = 0)] at hb
    simpa using hb
  have h43 : E(G.mulTilde n) \ edgeFiber e n ⊆ Bs := by
    intro f hf
    by_contra hfB
    -- The fundamental circuit `X = fundCircuit f Bs` is a circuit spanning `V`.
    have hfE : f ∈ M.E := by rw [hM, matroidMG, Matroid.restrict_ground_eq]; exact hf.1
    set X := M.fundCircuit f Bs with hXdef
    have hXcirc : M.IsCircuit X := hBsmem.fundCircuit_isCircuit hfE hfB
    have hspan : V(G.inducedSpan n X) = V(G) :=
      fundCircuit_inducedSpan_vertexSet_eq hD1 hnp hBsmem hf.1 hfB
    have hfiberspan : (G.fiberSpan n X).ncard = V(G).ncard := by
      rw [← vertexSet_inducedSpan G n X, hspan]
    -- Step 3: `X ∩ ẽ ≠ ∅`. Else `X − ej` is a base avoiding `ẽ`, contradicting minimality.
    have hXmeet : (X ∩ edgeFiber e n).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro hXe
      obtain ⟨ej, hej⟩ := hXcirc.nonempty
      -- `X − ej` is independent of full size `D(|V|−1) = |Bs|`, hence a base.
      have hindep : M.Indep (X \ {ej}) := hXcirc.diff_singleton_indep hej
      have htight : (X \ {ej}).ncard + bodyBarDim n = bodyBarDim n * (G.fiberSpan n X).ncard :=
        circuit_induces_isTight (hM ▸ hXcirc) hej
      have hcard : (X \ {ej}).ncard = Bs.ncard := by
        have hVpos : 1 ≤ V(G).ncard := hVne.ncard_pos
        zify [hVpos] at hBscard ⊢
        rw [hfiberspan] at htight
        zify [hVpos] at htight
        linarith [hBscard, htight]
      obtain ⟨B', hB', hsub'⟩ := hindep.exists_isBase_superset
      have heqcard : (X \ {ej}).ncard = B'.ncard := by
        rw [hcard, hBsmem.ncard_eq_ncard_of_isBase hB']
      have hXeb : X \ {ej} = B' :=
        Set.eq_of_subset_of_ncard_le hsub' (le_of_eq heqcard.symm) (hB'.finite)
      have hbase : M.IsBase (X \ {ej}) := hXeb ▸ hB'
      -- But `X − ej ⊆ X ⊆ E(G̃) ∖ ẽ`, so it avoids `ẽ` — contradiction with minimality.
      have hXsub : X ⊆ E(G.mulTilde n) \ edgeFiber e n := by
        intro p hp
        refine ⟨hXcirc.subset_ground hp, fun hpe => ?_⟩
        exact absurd (Set.mem_empty_iff_false p |>.mp (hXe ▸ ⟨hp, hpe⟩)) id
      have hmeet := hG.2 (X \ {ej}) (hM ▸ hbase) e he
      obtain ⟨q, hq⟩ := hmeet
      exact (hXsub (Set.diff_subset hq.1)).2 hq.2
    -- Step 4: `ej ∈ X ∩ ẽ`; exchange `B = insert f (Bs − ej)` drops `|B ∩ ẽ|` below `h*`.
    obtain ⟨ej, hejX, hejfib⟩ := hXmeet
    have hpcl : f ∈ M.closure Bs := by rw [hBsmem.closure_eq]; exact hfE
    have hejdiff : M.Indep (insert f Bs \ {ej}) :=
      (hBsmem.indep.mem_fundCircuit_iff hpcl hfB).mp hejX
    -- `f ∉ ẽ` (since `f ∈ E(G̃) ∖ ẽ`), so `f ≠ ej` (as `ej ∈ ẽ`).
    have hfne : f ≠ ej := fun h => hf.2 (h ▸ hejfib)
    have hinsert_eq : insert f (Bs \ {ej}) = insert f Bs \ {ej} := by
      rw [Set.insert_diff_of_notMem _ (by simp [hfne])]
    have hBnew : M.IsBase (insert f (Bs \ {ej})) :=
      hBsmem.exchange_isBase_of_indep hfB (hinsert_eq ▸ hejdiff)
    -- `|ẽ ∩ B_new| < h*`: removing `ej ∈ ẽ` and adding `f ∉ ẽ` strictly drops the count.
    have hcount : (edgeFiber e n ∩ insert f (Bs \ {ej})).ncard < hstar := by
      have hfnotfib : f ∉ edgeFiber e n := hf.2
      have heq : edgeFiber e n ∩ insert f (Bs \ {ej}) = (edgeFiber e n ∩ Bs) \ {ej} := by
        ext p
        simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_diff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hpfib, rfl | ⟨hpBs, hpne⟩⟩
          · exact absurd hpfib hfnotfib
          · exact ⟨⟨hpfib, hpBs⟩, hpne⟩
        · rintro ⟨⟨hpfib, hpBs⟩, hpne⟩
          exact ⟨hpfib, Or.inr ⟨hpBs, hpne⟩⟩
      rw [heq, hhstar]
      refine Set.ncard_diff_singleton_lt_of_mem ⟨hejfib, ?_⟩ ((Set.toFinite _))
      -- `ej ∈ Bs`: `ej ∈ X ⊆ insert f Bs` and `ej ≠ f` (else `ej = f ∉ ẽ`, but `ej ∈ ẽ`).
      have hejins : ej ∈ insert f Bs := (M.fundCircuit_subset_insert f Bs) hejX
      rcases hejins with hejf | hejBs
      · exact absurd hejf.symm hfne
      · exact hejBs
    exact absurd (hBsmin _ (hM ▸ hBnew)) (by rw [Set.inter_comm] at hcount ⊢; omega)
  -- Final count: `|E(G̃)| = |Bs| + |E(G̃) ∖ Bs| ≤ D(|V|−1) + (D−1) − h* < D(|V|−1) + (D−1)`.
  have hBssub : Bs ⊆ E(G.mulTilde n) := by rw [hM] at hBsmem; exact hBsmem.subset_ground
  -- `|E(G̃) ∖ Bs| + |Bs| = |E(G̃)|`.
  have hsplit : (E(G.mulTilde n) \ Bs).ncard + Bs.ncard = E(G.mulTilde n).ncard :=
    Set.ncard_diff_add_ncard_of_subset hBssub
  -- `E(G̃) ∖ Bs ⊆ ẽ ∖ Bs` (since `E(G̃) ∖ ẽ ⊆ Bs`).
  have hdiffsub : E(G.mulTilde n) \ Bs ⊆ edgeFiber e n \ Bs := by
    intro p hp
    refine ⟨?_, hp.2⟩
    by_contra hpe
    exact hp.2 (h43 ⟨hp.1, hpe⟩)
  have hdiffle : (E(G.mulTilde n) \ Bs).ncard ≤ (edgeFiber e n \ Bs).ncard :=
    Set.ncard_le_ncard hdiffsub (Set.toFinite _)
  -- `|ẽ ∩ Bs| + |ẽ ∖ Bs| = |ẽ| = D − 1`.
  have hfibersplit : (edgeFiber e n ∩ Bs).ncard + (edgeFiber e n \ Bs).ncard = bodyHingeMult n := by
    rw [Set.ncard_inter_add_ncard_diff_eq_ncard _ _ (Set.toFinite _), edgeFiber_ncard]
  -- Assemble: cast to ℤ and close by linear arithmetic.
  have hVpos : 1 ≤ V(G).ncard := hVne.ncard_pos
  rw [hEcard] at hsplit
  zify at hsplit hfibersplit hdiffle hstarpos
  rw [hHM]
  rw [hHM] at hfibersplit
  -- `(D−1)|E| = |Bs| + |E∖Bs| ≤ D(|V|−1) + (D−1−h*) < D(|V|−1) + (D−1)` since `h* ≥ 1`.
  nlinarith [hsplit, hfibersplit, hdiffle, hstarpos, hBscard, hhstar]

/-! ### A low-degree vertex by the average-degree count (`lem:reducible-vertex`, F″ core)

Katoh–Tanigawa 2011 Lemma 4.6 forces a degree-`2` vertex in a minimal `0`-dof-graph with no
proper rigid subgraph. The arithmetic is the average-degree bound `d_avg = 2|E|/|V| <
2D/(D−1) ≤ 3` (for `D = bodyBarDim n ≥ 3`, the molecular regime `n ≥ 2`): with `2|E|/|V| <
3`, the multigraph **handshake** `∑_v deg(v) = 2|E|` (`Graph.handshake_degree_subtype`,
vendored from `apnelson1/Matroid`'s `Graph.degree`/`incFun` API) forces some vertex to have
degree `< 3`, i.e. `≤ 2`. The strict edge bound is the green KT 4.5(i) count
`no_rigid_edge_count`: `(D−1)|E| < D(|V|−1) + (D−1) = D|V| − 1`, which multiplied by `2` and
cancelled against `3(D−1)|V|` (using `D ≥ 3` and `|V| ≥ 1`) gives `2|E| < 3|V|`.

This is the F″ core of `lem:reducible-vertex`. Pairing it with two-edge-connectivity
(`two_le_crossingEdges_of_isKDof_zero`, KT 3.1, which rules out degree `≤ 1`) yields the
degree-`exactly`-2 vertex Theorem 4.9 splits off; that refinement and the full reducibility
packaging are the remaining `lem:reducible-vertex` work. -/

/-- **A minimal `0`-dof-graph with no proper rigid subgraph has a vertex of degree `≤ 2`**
(`lem:reducible-vertex`, F″ core; Katoh–Tanigawa 2011 Lemma 4.6, printed p.664). For
`D = bodyBarDim n ≥ 3` (the molecular regime `n ≥ 2`) and `V(G).Nonempty`, the average-degree
bound `2|E|/|V| < 2D/(D−1) ≤ 3` forces some `v ∈ V(G)` with multigraph degree `G.degree v ≤
2`. Combines the green KT 4.5(i) edge bound (`no_rigid_edge_count`) with the multigraph
handshake `∑_v deg(v) = 2|E|` (`Graph.handshake_degree_subtype`, vendored) via a Finset
pigeonhole (`Finset.exists_lt_of_sum_lt`). The two-edge-connectivity (KT 3.1) needed to
upgrade `≤ 2` to `= 2` is a separate step. -/
theorem exists_degree_le_two [DecidableEq β] [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hD : 3 ≤ bodyBarDim n) (hVne : V(G).Nonempty) (hG : G.IsMinimalKDof n 0)
    (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) :
    ∃ v ∈ V(G), G.degree v ≤ 2 := by
  classical
  haveI : G.Finite := { edgeSet_finite := Set.toFinite _, vertexSet_finite := Set.toFinite _ }
  have hD2 : 2 ≤ bodyBarDim n := le_trans (by norm_num) hD
  -- The KT 4.5(i) edge bound, read over ℤ: `(D−1)|E| < D(|V|−1) + (D−1)`.
  have hedge := no_rigid_edge_count hD2 hVne hG hnp
  -- The handshake `∑_{v ∈ V(G)} deg(v) = 2|E(G)|` over the finite vertex Finset.
  set s := G.vertexSet_finite.toFinset with hs
  have hhand : ∑ v ∈ s, G.degree v = 2 * E(G).ncard := by
    rw [hs, ← finsum_mem_eq_finite_toFinset_sum _ G.vertexSet_finite]
    exact handshake_degree_subtype G
  -- `2|E| < 3|V|` from the edge bound, using `D ≥ 3` and `|V| ≥ 1`.
  have hVpos : 1 ≤ V(G).ncard := hVne.ncard_pos
  have hHM : (bodyHingeMult n : ℤ) = (bodyBarDim n : ℤ) - 1 := by rw [bodyHingeMult]; omega
  have hsum_lt : ∑ v ∈ s, G.degree v < ∑ _v ∈ s, 3 := by
    rw [Finset.sum_const, hhand, smul_eq_mul]
    -- `|s| = |V(G)|`.
    have hscard : s.card = V(G).ncard := by
      rw [hs, ← Set.ncard_eq_toFinset_card _ G.vertexSet_finite]
    rw [hscard]
    -- `2|E| < 3|V|`: cast to ℤ and discharge with the edge bound.
    have h2D : (3 : ℤ) ≤ (bodyBarDim n : ℤ) := by exact_mod_cast hD
    zify
    nlinarith [hedge, hHM, hVpos, h2D]
  obtain ⟨v, hvs, hvdeg⟩ := Finset.exists_lt_of_sum_lt hsum_lt
  exact ⟨v, (by rwa [hs, Set.Finite.mem_toFinset] at hvs), by omega⟩

/-! ### Upgrading degree `≤ 2` to `= 2` via two-edge-connectivity (`lem:reducible-vertex`)

Katoh–Tanigawa 2011 Lemma 4.6 needs a degree-`exactly`-2 vertex, not merely a degree-`≤ 2`
one. The average-degree count (`exists_degree_le_two`) supplies the `≤ 2` half; the
`= 2` upgrade comes from two-edge-connectivity (`two_le_crossingEdges_of_isKDof_zero`, KT
3.1): a `0`-dof-graph admits no bridge cut, so the single-vertex cut `V' = {v}` has at
least two crossing edges, forcing `degree v ≥ 2`.

The bridge from the project's cut form (`crossingEdges`, an edge count) to the vendored
multigraph `Graph.degree` (an endpoint count) is the observation that the crossing edges
of the single-vertex cut `{v}` are exactly the *nonloop* edges at `v`: an edge crosses
`{v}` iff exactly one endpoint is `v`, which is `IsNonloopAt e v`. The multigraph degree
counts each nonloop edge once and each loop twice (`degree_eq_ncard_add_ncard`), so the
crossing count is at most the degree, and `2 ≤ crossing ≤ degree v` pins `degree v ≥ 2`. -/

/-- **Crossing edges of the single-vertex cut are nonloop edges at `v`**
(`lem:reducible-vertex`, cut↔degree bridge). The edges of `G` crossing the two-part cut
`{{v}, V(G) ∖ {v}}` (encoded by `cutLabeling {v} a b` with `a ≠ b`) are exactly the
*nonloop* edges incident to `v`: an edge crosses iff exactly one of its endpoints is `v`.
This is the structural fact linking the project's cut count `d_G(V')` to the vendored
multigraph degree `Graph.degree`. -/
lemma crossingEdges_cutLabeling_singleton_subset {G : Graph α β} {v a b : α}
    [∀ x, Decidable (x ∈ ({v} : Set α))] :
    G.crossingEdges (cutLabeling {v} a b) ⊆ {e | G.IsNonloopAt e v} := by
  rintro e ⟨heG, x, y, hlink, hfxy⟩
  -- `f x ≠ f y` with `f = cutLabeling {v} a b` forces exactly one of `x, y` to equal `v`.
  simp only [cutLabeling, Set.mem_singleton_iff] at hfxy
  rw [Set.mem_setOf_eq]
  by_cases hx : x = v
  · -- `x = v`, so `y ≠ v` (else `f x = f y`); `e` is a nonloop at `v` via the link `v, y`.
    subst hx
    have hy : y ≠ x := by rintro rfl; simp at hfxy
    exact ⟨y, hy, hlink⟩
  · -- `x ≠ v`, so `y = v` (else both map to `b`); `e` is a nonloop at `v` via `v, x`.
    by_cases hy : y = v
    · subst hy
      exact ⟨x, hx, hlink.symm⟩
    · simp [hx, hy] at hfxy

/-- **The cut-crossing count is at most the multigraph degree at `v`**
(`lem:reducible-vertex`, cut↔degree bridge). For the single-vertex cut `{v}`, the number of
crossing edges `d_G({v})` is at most the vendored multigraph degree `Graph.degree v`: the
crossing edges are the nonloop edges at `v` (`crossingEdges_cutLabeling_singleton_subset`),
and the degree counts each nonloop edge at least once
(`Graph.degree_eq_ncard_add_ncard`). -/
lemma crossingEdges_cutLabeling_singleton_ncard_le [Finite β] {G : Graph α β} {v a b : α}
    [∀ x, Decidable (x ∈ ({v} : Set α))] :
    (G.crossingEdges (cutLabeling {v} a b)).ncard ≤ G.degree v := by
  calc (G.crossingEdges (cutLabeling {v} a b)).ncard
      ≤ {e | G.IsNonloopAt e v}.ncard :=
        Set.ncard_le_ncard crossingEdges_cutLabeling_singleton_subset (Set.toFinite _)
    _ ≤ G.degree v := by rw [G.degree_eq_ncard_add_ncard v]; omega

/-- **A minimal `0`-dof-graph with no proper rigid subgraph and `|V| ≥ 2` has a vertex of
degree exactly `2`** (`lem:reducible-vertex`; Katoh–Tanigawa 2011 Lemma 4.6). For
`D = bodyBarDim n ≥ 3` (the molecular regime `n ≥ 2`) and `2 ≤ |V(G)|`, the average-degree
count (`exists_degree_le_two`) gives a vertex `v` of multigraph degree `≤ 2`, and
two-edge-connectivity (`two_le_crossingEdges_of_isKDof_zero`, KT 3.1) rules out
`degree v ≤ 1`: the single-vertex cut `{v}` would otherwise be a bridge cut, contradicting
that a `0`-dof-graph admits none. The bridge `crossingEdges_cutLabeling_singleton_ncard_le`
links the cut count `d_G({v}) ≥ 2` to `degree v ≥ 2`. This is the reducible degree-2 vertex
Theorem 4.9 splits off. -/
theorem exists_degree_eq_two [DecidableEq β] [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hD : 3 ≤ bodyBarDim n) (hV2 : 2 ≤ V(G).ncard) (hG : G.IsMinimalKDof n 0)
    (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) :
    ∃ v ∈ V(G), G.degree v = 2 := by
  classical
  have hD1 : 1 ≤ bodyBarDim n := le_trans (by norm_num) hD
  have hVne : V(G).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  -- The average-degree count supplies a vertex of degree `≤ 2`.
  obtain ⟨v, hvG, hvle⟩ := exists_degree_le_two hD hVne hG hnp
  refine ⟨v, hvG, ?_⟩
  -- Two-edge-connectivity forces `degree v ≥ 2`. Pick a second vertex `b ≠ v` for the cut.
  obtain ⟨b, hbG, hbv⟩ : ∃ b ∈ V(G), b ≠ v := by
    by_contra h
    push Not at h
    -- If every vertex of `G` equals `v`, then `V(G) ⊆ {v}` has `ncard ≤ 1`, contra `≥ 2`.
    have hsub : V(G) ⊆ {v} := fun x hx => h x hx
    have : V(G).ncard ≤ ({v} : Set α).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_singleton] at this
    omega
  -- The single-vertex cut `{v}`: `a = v ∈ {v}`, `b ∉ {v}`, both in `V(G)`.
  have hcross : 2 ≤ (G.crossingEdges (cutLabeling {v} v b)).ncard :=
    two_le_crossingEdges_of_isKDof_zero hD1 hG.1 (Set.mem_singleton v) hvG hbG
      (by simpa using hbv)
  -- The crossing count bounds the degree: `2 ≤ d_G({v}) ≤ degree v ≤ 2`.
  have hle := crossingEdges_cutLabeling_singleton_ncard_le (G := G) (v := v) (a := v) (b := b)
  omega

/-- **Edge-splitting** `H_{ab}^v` (`def:graph-operations`): the inverse of splitting-off.
Subdivide the edge `e₀` of `H` (joining `a` and `b`) by a fresh degree-2 vertex `v`,
replacing `e₀` with the path `a — v — b` carried by two fresh edges `e₁` (joining `a`,
`v`) and `e₂` (joining `v`, `b`). Every edge of `H` other than `e₀` is kept; the new
vertex `v` and the two new edges realize the subdivision. It satisfies
`(H_{ab}^v)_v^{ab} = H` (the `lem:forest-surgery-unsplit` identity, established later). -/
def edgeSplit (H : Graph α β) (a b v : α) (e₀ e₁ e₂ : β) : Graph α β where
  vertexSet := insert v V(H)
  IsLink e x y :=
    (e ≠ e₀ ∧ e ≠ e₁ ∧ e ≠ e₂ ∧ H.IsLink e x y) ∨
      (e = e₁ ∧ ((x = a ∧ y = v) ∨ (x = v ∧ y = a)) ∧ a ∈ V(H)) ∨
      (e = e₂ ∧ e ≠ e₁ ∧ ((x = v ∧ y = b) ∨ (x = b ∧ y = v)) ∧ b ∈ V(H))
  isLink_symm := by
    rintro e he x y (⟨h₀, h₁, h₂, h⟩ | ⟨he₁, hxy, ha⟩ | ⟨he₂, hne, hxy, hb⟩)
    · exact Or.inl ⟨h₀, h₁, h₂, h.symm⟩
    · exact Or.inr <| Or.inl
        ⟨he₁, hxy.symm.imp (fun ⟨p, q⟩ ↦ ⟨q, p⟩) (fun ⟨p, q⟩ ↦ ⟨q, p⟩), ha⟩
    · exact Or.inr <| Or.inr
        ⟨he₂, hne, hxy.symm.imp (fun ⟨p, q⟩ ↦ ⟨q, p⟩) (fun ⟨p, q⟩ ↦ ⟨q, p⟩), hb⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro e x y z w
      (⟨h₀, h₁, h₂, h⟩ | ⟨he, hxy, _⟩ | ⟨he, hne, hxy, _⟩)
      (⟨h₀', h₁', h₂', h'⟩ | ⟨he', hzw, _⟩ | ⟨he', hne', hzw, _⟩)
    · exact h.left_eq_or_eq h'
    · grind
    · grind
    · grind
    · rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hzw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
    · grind
    · grind
    · grind
    · rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hzw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  left_mem_of_isLink := by
    rintro e x y (⟨_, _, _, h⟩ | ⟨_, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), ha⟩ |
        ⟨_, _, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), hb⟩)
    · exact Set.mem_insert_of_mem _ h.left_mem
    · exact Set.mem_insert_of_mem _ ha
    · exact Set.mem_insert _ _
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ hb

@[simp]
lemma vertexSet_edgeSplit (H : Graph α β) (a b v : α) (e₀ e₁ e₂ : β) :
    V(H.edgeSplit a b v e₀ e₁ e₂) = insert v V(H) := rfl

@[simp]
lemma edgeSplit_isLink {H : Graph α β} {a b v : α} {e₀ e₁ e₂ : β} {e : β} {x y : α} :
    (H.edgeSplit a b v e₀ e₁ e₂).IsLink e x y ↔
      (e ≠ e₀ ∧ e ≠ e₁ ∧ e ≠ e₂ ∧ H.IsLink e x y) ∨
        (e = e₁ ∧ ((x = a ∧ y = v) ∨ (x = v ∧ y = a)) ∧ a ∈ V(H)) ∨
        (e = e₂ ∧ e ≠ e₁ ∧ ((x = v ∧ y = b) ∨ (x = b ∧ y = v)) ∧ b ∈ V(H)) := Iff.rfl

/-- **Collapse map** `collapseTo r S` (`def:rigid-contraction`, auxiliary): the vertex
map `α → α` sending every vertex of `S` to the representative `r` and fixing all others.
The vertex identification underlying rigid-subgraph contraction. -/
noncomputable def collapseTo (r : α) (S : Set α) : α → α :=
  open Classical in fun x => if x ∈ S then r else x

/-- **Rigid-subgraph contraction** `G / E(H)` (`def:rigid-contraction`): collapse the
vertex set `V(H)` of a (rigid) subgraph `H ≤ G` to a single representative vertex `r`,
discard the edges of `H`, and retain every other edge of `G` with its endpoints in `V(H)`
redirected to `r`. Realized as `(G.deleteEdges E(H)).map (collapseTo r V(H))`: deleting
`E(H)` discards the rigid subgraph's edges, and `map` identifies `V(H)` to `r`. On the
matroid side this is the matroid contraction `M(G̃) / E(H̃)` restricted to the surviving
fibers (used in `lem:contraction-minimality`). -/
noncomputable def rigidContract (G H : Graph α β) (r : α) : Graph α β :=
  (G.deleteEdges E(H)).map (collapseTo r V(H))

@[simp]
lemma vertexSet_rigidContract (G H : Graph α β) (r : α) :
    V(G.rigidContract H r) = collapseTo r V(H) '' V(G) := rfl

/-- **Rigid-subgraph contraction strictly decreases the vertex count** (`lem:reduction-step`,
the "reduces to a smaller graph" measure). Contracting a subgraph `H ≤ G` whose vertex set
`V(H) ⊆ V(G)` has at least two vertices collapses `V(H)` to the single representative `r`, so
`V(G / E(H)) = collapseTo r V(H) '' V(G)` has cardinality at most `|V(G)| − |V(H)| + 1 <
|V(G)|`. The `2 ≤ |V(H)|` hypothesis is the genuine requirement: collapsing a single-vertex
`H` is a vertex-set no-op (KT's Case I always contracts a proper rigid subgraph spanning at
least two vertices). This is the well-founded measure on which Katoh–Tanigawa 2011's
Theorem 4.9 inducts in the contraction branch. -/
lemma rigidContract_vertexSet_ncard_lt [Finite α] {G H : Graph α β} {r : α}
    (hHsub : V(H) ⊆ V(G)) (hH2 : 2 ≤ V(H).ncard) :
    V(G.rigidContract H r).ncard < V(G).ncard := by
  rw [vertexSet_rigidContract]
  calc (collapseTo r V(H) '' V(G)).ncard
      ≤ ((V(G) \ V(H)) ∪ {r}).ncard := by
        refine Set.ncard_le_ncard ?_ (Set.toFinite _)
        rintro _ ⟨x, hx, rfl⟩
        unfold collapseTo
        split_ifs with hxH
        · exact Or.inr rfl
        · exact Or.inl ⟨hx, hxH⟩
    _ ≤ (V(G) \ V(H)).ncard + 1 := by
        refine le_trans (Set.ncard_union_le _ _) ?_
        simp [Set.ncard_singleton]
    _ < V(G).ncard := by
        have h1 : (V(G) \ V(H)).ncard = V(G).ncard - V(H).ncard :=
          Set.ncard_diff hHsub (Set.toFinite _)
        have hVH : V(H).ncard ≤ V(G).ncard := Set.ncard_le_ncard hHsub (Set.toFinite _)
        omega

/-- **The exact vertex count of a rigid-subgraph contraction** (the count form of
`lem:reduction-step`, sharpening `rigidContract_vertexSet_ncard_lt`). Collapsing `V(H) ⊆ V(G)`
to its representative `r ∈ V(H)` sends `V(H)` to `{r}` and fixes `V(G) \ V(H)`, so the image
is exactly `(V(G) \ V(H)) ∪ {r}` with `r ∉ V(G) \ V(H)`: `|V(G/E(H))| = (|V(G)| − |V(H)|) + 1`.
This is the vertex-count bookkeeping the contraction-minimality bridge `rigidContract_isMinimalKDof`
needs to match the reduced matroid ambient `D(|V(G)|−|V(H)|)` against `D(|V(G/E(H))|−1)`. -/
lemma rigidContract_vertexSet_ncard [Finite α] {G H : Graph α β} {r : α} (hr : r ∈ V(H))
    (hHsub : V(H) ⊆ V(G)) :
    V(G.rigidContract H r).ncard = (V(G).ncard - V(H).ncard) + 1 := by
  rw [vertexSet_rigidContract]
  have hrG : r ∈ V(G) := hHsub hr
  have himg : collapseTo r V(H) '' V(G) = (V(G) \ V(H)) ∪ {r} := by
    ext x
    simp only [Set.mem_image, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      unfold collapseTo
      split_ifs with hyH
      · exact Or.inr rfl
      · exact Or.inl ⟨hy, hyH⟩
    · rintro (⟨hx, hxH⟩ | hxr)
      · exact ⟨x, hx, by unfold collapseTo; rw [if_neg hxH]⟩
      · exact ⟨r, hrG, by unfold collapseTo; rw [if_pos hr]; exact hxr.symm⟩
  rw [himg, Set.ncard_union_eq (by
    simp only [Set.disjoint_singleton_right, Set.mem_diff, not_and, not_not]; exact fun _ ↦ hr)
    (Set.toFinite _) (Set.toFinite _), Set.ncard_singleton, Set.ncard_diff hHsub (Set.toFinite _)]

/-- **The edge set of a rigid-subgraph contraction** (graph-side brick of
`lem:rigidContract-isMinimalKDof`). `rigidContract = (G ＼ E(H)).map (collapseTo r V(H))` is a
pure vertex-relabel of the `E(H)`-deletion, and `map` preserves the edge set, so
`E(G/E(H)) = E(G) \ E(H)` — the surviving edges are exactly `G`'s non-`H` edges. The
contraction-minimality bridge reads an edge `e ∈ E(G/E(H))` as `e ∈ E(G)` and `e ∉ E(H)`
through this identity. -/
lemma edgeSet_rigidContract (G H : Graph α β) (r : α) :
    E(G.rigidContract H r) = E(G) \ E(H) := by
  simp [rigidContract, edgeSet_deleteEdges]

/-- **Rigid-subgraph contraction is mathlib's graph contraction** (graph-side brick of
`lem:rigidContract-isMinimalKDof`). The project's `rigidContract G H r =
(G ＼ E(H)).map (collapseTo r V(H))` (delete-then-relabel) coincides with the vendored
`apnelson1/Matroid` graph contraction `(G ＼ E(H)) /[E(H), collapseTo r V(H)]`. The vendored
contraction `H' /[C, φ]` is `(φ ''ᴳ H') ＼ C`, but `H' = G ＼ E(H)` already has its edge set
`E(G) \ E(H)` disjoint from `C = E(H)`, so the trailing `＼ E(H)` is a no-op and
`contract_eq_map_of_disjoint` collapses it to the bare `map` form. This brick is the entry
point of the graph↔matroid bridge for `lem:rigidContract-isMinimalKDof`: it puts
`rigidContract` in the shape `cycleMatroid_contract` (and the `Matroid.Union`-of-`cycleMatroid`
substrate of `matroidMG`) is stated against. -/
lemma rigidContract_eq_contract (G H : Graph α β) (r : α) :
    G.rigidContract H r = (G.deleteEdges E(H)) /[E(H), collapseTo r V(H)] := by
  rw [contract_eq_map_of_disjoint (by simpa using Set.disjoint_sdiff_left), rigidContract]

end Graph
