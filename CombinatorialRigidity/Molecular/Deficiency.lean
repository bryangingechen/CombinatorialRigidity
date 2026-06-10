/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.BodyBar.BodyHinge

/-!
# The matroid `M(G̃)`, deficiency, and `k`-dof graphs (`sec:molecular-deficiency`)

Phase 19, the third phase of the molecular-conjecture program (Phases 17–26; see
`notes/MolecularConjecture.md`). Where `Molecular/RigidityMatrix.lean` (Phase 18)
built the *analytic* side — the panel-hinge rigidity matrix `R(G,p)`, its rank,
and the three rank lemmas — this file builds the *matroidal* side: the matroid
`M(G̃)`, the `D`-deficiency, the `k`-degree-of-freedom hierarchy, rigid subgraphs,
and the bridge `def(G̃) = corank M(G̃)` of Katoh–Tanigawa 2011
(*A proof of the molecular conjecture*, Discrete Comput. Geom. **45**, §2.5, §3).

This file lands the `sec:molecular-deficiency` dep-graph in dependency order. The
leaf node landing here:

* `matroidMG` (`def:matroid-MG`) — the matroid `M(G̃)`, where `G̃ = (D-1)·G` is the
  multiplied graph of Phase 16 (`Graph.edgeMultiply`, with `D = bodyBarDim n` so
  `D - 1 = bodyHingeMult n`). `M(G̃)` is the `(D,D)`-count matroid of `G̃` at the
  **boundary regime** `ℓ = 2k = D`: the `D`-fold union of the cycle (graphic)
  matroid of `G̃`, restricted to `E(G̃)`. This is *not* covered by the
  matroidal-regime construction of `CountMatroid.lean` (built for `ℓ < 2k`);
  `M(G̃)` is instead the `D`-fold graphic-matroid union of Phases 13/14, whose
  independence characterization is Tutte–Nash-Williams tree-packing.
* `matroidMG_indep_iff` (`def:matroid-MG`, the boundary-regime cleanliness check) —
  confirms the boundary regime is clean before the rest of the chapter relies on
  it: a bar set `E'` is independent in `M(G̃)` iff `E' ⊆ E(G̃)` and the
  edge-restricted subgraph `G̃ ↾ E'` is `(D,D)`-sparse, equivalently (by
  Tutte–Nash-Williams, `tutte_nash_williams`) decomposes into `D` edge-disjoint
  forests. The forward route is `unionPow_cycleMatroid_indep_iff_isSparse_restrict`
  (Phase 13) under matroid restriction `Matroid.restrict_indep_iff`.
* `partitionDef` / `deficiency` (`def:D-deficiency`) — the `D`-deficiency of a partition
  `P` of `V(G)`, `def(P) = D(|P| - 1) - (D-1)·d_G(P)`, and `def = max_P def(P)`. Partitions
  are encoded as labelings `f : α → α` (the fibers are the parts); `numParts` counts the
  parts `|P| = |f '' V(G)|` and `crossingEdges` collects the edges `d_G(P)` joining distinct
  parts. The deficiency is `ℤ`-valued (genuinely signed) and `≥ 0` by the trivial one-part
  partition (`partitionDef_one`).

* `IsKDof` / `IsMinimalKDof` / `edgeFiber` (`def:k-dof`) — `G` is a `k`-dof-graph
  when `def(G̃) = k`; minimal when additionally every base of `M(G̃)` meets every
  edge-fiber `ẽ` (the `D-1` parallel copies of `e ∈ E(G)`).
* `IsRigidSubgraph` / `IsProperRigidSubgraph` (`def:rigid-subgraph`) — a subgraph
  `H ≤ G` is *rigid* when it is `0`-dof, *proper rigid* when additionally
  `2 ≤ |V(H)|` and `V(H) ⊊ V(G)` (KT p. 659's `1 < |V′|`; without the lower bound a
  single vertex is vacuously rigid and "no proper rigid subgraph" is unsatisfiable).
  A *circuit* of `M(G̃)` is `Matroid.IsCircuit (G.matroidMG n)`.
* `matroidMG_restrict_mulTilde` (`lem:matroid-restrict-subgraph`) — the engine of
  KT Lemma 3.3: `M(G̃) ↾ E(H̃) = M(H̃)` for `H ≤ G`, via `Matroid.ext_indep` through
  `matroidMG_indep_iff` (so it never touches the `Matroid.Union` internals).
* `subgraph_minimality` (`lem:subgraph-minimality`, KT Lemma 3.3) — a subgraph
  `H ≤ G` of a minimal `k`-dof-graph `G`, with `def(H̃) = k'`, is a minimal
  `k'`-dof-graph. The base/fiber-meeting minimality transports from `G` to `H` over
  the restriction identity: a base `B'` of `M(H̃) = M(G̃) ↾ E(H̃)` extends to a base
  `B` of `M(G̃)` with `B' = B ∩ E(H̃)`, and each fiber `ẽ` of `e ∈ E(H) ⊆ E(G)` lies
  in `E(H̃)`, so `B ∩ ẽ ≠ ∅` (from `G`'s minimality) descends to `B' ∩ ẽ ≠ ∅`.

* `two_le_crossingEdges_of_isKDof_zero` (`lem:two-edge-conn`, KT Lemma 3.1) — a
  body-hinge-rigid (`0`-dof) graph is `2`-edge-connected, in cut form: any nonempty
  proper `V' ⊊ V(G)` separating `V(G)` has `d_G(V') ≥ 2`. (Mathlib has no
  edge-connectivity predicate for `Graph α β`, so the conclusion is the cut form KT's
  proof uses.) The bridge cut `{V', V∖V'}` (a two-part partition, `cutLabeling` /
  `numParts_cutLabeling`) would otherwise witness `def ≥ D - (D-1)·d_G(V') ≥ 1 > 0`
  through `partitionDef_le_deficiency`, contradicting `def = 0`.

* `rank_matroidMG_le` (`lem:rank-matroidMG-le`, the conjecture-relevant half of
  `thm:def-eq-corank`) — the rank upper bound `rank M(G̃) ≤ D·(|V(G)| - 1)` for
  `V(G).Nonempty`. Every base is `(D,D)`-sparse (boundary-regime cleanliness), so
  applying sparsity to the base itself gives `|B| + D ≤ D·|spanningVerts B| ≤ D·|V|`,
  i.e. `|B| ≤ D(|V|-1)`. This is the matroidal mirror of Phase 18's analytic
  `rank R(G,p) ≤ D(|V|-1)`; it is the upper-bound half the molecular conjecture
  (Thm 5.6) needs from the def = corank bridge — the reverse direction of the full
  Jackson–Jordán min–max identity (the partition attaining the rank) is deferred until
  a downstream node needs the full equality (risk #4, prove-vs-hypothesize).

* `isSparse_diff_singleton_of_isCircuit` (`lem:circuit-rigid`, KT Lemma 3.4 matroidal
  core) — for a circuit `X` of `M(G̃)` and `e ∈ X`, the set `X \ {e}` is `(D,D)`-sparse,
  equivalently an `M(G̃)`-basis of `X`: a circuit is exactly one edge short of being
  independent on its span. This is the upper-bound / maximal-sparse-subset form that KT's
  fundamental-circuit arguments (Phases 21–22) consume; the full `G[V(X)]`-is-rigid
  (`def = 0`, tightness *equality*) conclusion needs a vertex-induced-subgraph
  construction and is an early-Phase-20 deliverable.

* `rank_add_deficiency_eq` / `isBase_ncard_add_deficiency_eq` (`thm:def-eq-corank`;
  Jackson–Jordán 2009 Thm 6.1 / Cor 6.2) — the **def = corank bridge**
  `rank M(G̃) + def(G̃) = D(|V| - 1)` (equivalently `|B| + def(G̃) = D(|V| - 1)` for any
  base `B`), the `le_antisymm` of weak duality `rank_add_deficiency_le` (`def ≤ corank`) and
  its reverse `le_rank_add_deficiency` (`def ≥ corank`, the substantive JJ09 min–max content:
  the partition into the connected components of `G̃ ↾ Y₀`, for the Edmonds-optimal `Y₀`,
  attains the rank). Axiom-free.

See `ROADMAP.md` §19 / `notes/Phase19.md` and the `sec:molecular-deficiency`
dep-graph of `blueprint/src/chapter/deficiency.tex`.
-/

namespace Graph

open Set Matroid

variable {α β : Type*}

/-- The **multiplied graph** `G̃ = (D-1)·G` of the molecular conjecture
(`def:matroid-MG`), where `D = bodyBarDim n`. Each hinge (edge) of `G` is replaced
by the `D - 1 = bodyHingeMult n` parallel copies that the body-hinge reduction of
Phase 16 attaches to it (`Graph.edgeMultiply`); the edge type becomes
`β × Fin (bodyHingeMult n)`. This is the graph the matroid `M(G̃)` lives over. -/
def mulTilde (G : Graph α β) (n : ℕ) : Graph α (β × Fin (bodyHingeMult n)) :=
  G.edgeMultiply (bodyHingeMult n)

/-- **Edge-set membership of `G̃ = (D-1)·G`** (`def:matroid-MG`): a copy `p` is an edge of
the multiplied graph iff its underlying hinge `p.1` is an edge of `G`. The fused mirror of
the `mulTilde`/`edgeMultiply_edgeSet`/`Set.mem_setOf_eq` unfold tower; tagged `@[simp]` so a
bare `simp` reaches through the `mulTilde` `def` wrapper that does not unfold on its own. -/
@[simp]
lemma mem_edgeSet_mulTilde (G : Graph α β) (n : ℕ) {p : β × Fin (bodyHingeMult n)} :
    p ∈ E(G.mulTilde n) ↔ p.1 ∈ E(G) := Iff.rfl

/-- **Incidence of `G̃ = (D-1)·G`** (`def:matroid-MG`): the copy `p` links `x` and `y` in the
multiplied graph iff its underlying hinge `p.1` links them in `G`. The fused mirror of the
`mulTilde`/`edgeMultiply_isLink` unfold pair; `@[simp]` for the same wrapper reason as
`mem_edgeSet_mulTilde`. -/
@[simp]
lemma mulTilde_isLink (G : Graph α β) (n : ℕ) {p : β × Fin (bodyHingeMult n)} {x y : α} :
    (G.mulTilde n).IsLink p x y ↔ G.IsLink p.1 x y := Iff.rfl

/-- The **matroid `M(G̃)`** (`def:matroid-MG`; Katoh–Tanigawa 2011 §2.5): the
`(D,D)`-count matroid of the multiplied graph `G̃ = (D-1)·G` at the boundary regime
`ℓ = 2k = D` with `D = bodyBarDim n`. Concretely it is the `D`-fold union of the
cycle (graphic) matroid of `G̃`, restricted to the edge set `E(G̃)`.

This is the matroidal substrate of the molecular-conjecture program. The boundary
regime `ℓ = 2k = D` is *not* the matroidal regime `ℓ < 2k` of `CountMatroid.lean`;
`M(G̃)` is built instead from the `D`-fold graphic-matroid union of Phases 13/14
(`Matroid.Union (fun _ : Fin D ↦ (G̃).cycleMatroid)`), whose independence
characterization is Tutte–Nash-Williams tree-packing. The restriction `↾ E(G̃)` is
forced exactly as in Phase 14's `kFrameMatroid`: the vendored `Matroid.Union` has
ground set `univ : Set (β × Fin (bodyHingeMult n))`, so without the restriction
every non-edge would be a loop. -/
noncomputable def matroidMG [DecidableEq β] (G : Graph α β) (n : ℕ) :
    Matroid (β × Fin (bodyHingeMult n)) :=
  (Matroid.Union (fun _ : Fin (bodyBarDim n) ↦ (G.mulTilde n).cycleMatroid)) ↾ E(G.mulTilde n)

/-- **Boundary-regime cleanliness** of `M(G̃)` (`def:matroid-MG`): a bar set `E'` is
independent in `M(G̃)` if and only if `E' ⊆ E(G̃)` and the edge-restricted subgraph
`G̃ ↾ E'` is `(D,D)`-sparse, with `D = bodyBarDim n` and `G̃ = (D-1)·G`. This
confirms — as the first formalization step of Phase 19 — that the boundary regime
`ℓ = 2k = D` is clean before the rest of the chapter relies on it: the independent
sets of `M(G̃)` are exactly the `(D,D)`-sparse subsets of `G̃`.

By Tutte–Nash-Williams (`tutte_nash_williams`, applied to `G̃ ↾ E'`) these are
equivalently the bar subsets that decompose into `D` edge-disjoint forests. The
proof unfolds the restriction (`Matroid.restrict_indep_iff`) and feeds the
`D`-fold cycle-matroid union to Phase 13's
`unionPow_cycleMatroid_indep_iff_isSparse_restrict`. -/
theorem matroidMG_indep_iff [DecidableEq β] [Finite α] [Finite β] (G : Graph α β) (n : ℕ)
    {E' : Set (β × Fin (bodyHingeMult n))} :
    (G.matroidMG n).Indep E' ↔ E' ⊆ E(G.mulTilde n) ∧ ((G.mulTilde n) ↾ E').IsSparse
      (bodyBarDim n) (bodyBarDim n) := by
  rw [matroidMG, Matroid.restrict_indep_iff]
  constructor
  · rintro ⟨hindep, hsub⟩
    exact ⟨hsub, (unionPow_cycleMatroid_indep_iff_isSparse_restrict hsub).mp hindep⟩
  · rintro ⟨hsub, hsparse⟩
    exact ⟨(unionPow_cycleMatroid_indep_iff_isSparse_restrict hsub).mpr hsparse, hsub⟩

/-- The `(D,D)`-sparsity of a bar set `E'` inside the edge-restriction `G̃ ↾ S` agrees
with its `(D,D)`-sparsity inside `H̃ ↾ S` whenever `H ≤ G` and `S` lies within `E(H̃)`:
restriction to a fiber subset of the smaller graph cannot see the difference between
`H` and `G`. The edge sets coincide (`E(G̃ ↾ S) = S = E(H̃ ↾ S)`) and the spanned-vertex
counts coincide because the incidences of an edge `e ∈ E' ⊆ E(H̃)` agree under the
subgraph relation. This is the `IsSparse`-level engine of the matroid-restriction
identity `matroidMG_restrict_mulTilde`. -/
private theorem isSparse_restrict_mulTilde_congr {H G : Graph α β} (h : H ≤ G) (n : ℕ)
    {S : Set (β × Fin (bodyHingeMult n))} (hS : S ⊆ E(H.mulTilde n)) {E' : Set _} (hE' : E' ⊆ S) :
    ((G.mulTilde n) ↾ E').IsSparse (bodyBarDim n) (bodyBarDim n) ↔
      ((H.mulTilde n) ↾ E').IsSparse (bodyBarDim n) (bodyBarDim n) := by
  have hHG : H.mulTilde n ≤ G.mulTilde n := edgeMultiply_mono h _
  have hinc : ∀ e ∈ E', ∀ x, (G.mulTilde n).Inc e x ↔ (H.mulTilde n).Inc e x :=
    fun e he x ↦ (hHG.inc_congr (hS (hE' he))).symm
  have hspan : ∀ Y ⊆ E', ((G.mulTilde n) ↾ E').spanningVerts Y =
      ((H.mulTilde n) ↾ E').spanningVerts Y := by
    intro Y hY
    ext x
    simp only [mem_spanningVerts, restrict_inc]
    exact exists_congr fun e ↦ ⟨fun ⟨heY, hi, he⟩ ↦ ⟨heY, (hinc e he x).mp hi, he⟩,
      fun ⟨heY, hi, he⟩ ↦ ⟨heY, (hinc e he x).mpr hi, he⟩⟩
  have hedge : E((G.mulTilde n) ↾ E') = E((H.mulTilde n) ↾ E') := by
    rw [edgeSet_restrict, edgeSet_restrict, inter_eq_right.mpr (hE'.trans (hS.trans
      (hHG.edgeSet_mono))), inter_eq_right.mpr (hE'.trans hS)]
  constructor
  · intro hsp Y hYsub hYne
    have hYE' : Y ⊆ E' := hYsub.trans_eq (by rw [edgeSet_restrict,
      inter_eq_right.mpr (hE'.trans hS)])
    rw [← hspan Y hYE']
    exact hsp Y (hYsub.trans_eq hedge.symm) hYne
  · intro hsp Y hYsub hYne
    have hYE' : Y ⊆ E' := hYsub.trans_eq (by rw [edgeSet_restrict,
      inter_eq_right.mpr (hE'.trans (hS.trans hHG.edgeSet_mono))])
    rw [hspan Y hYE']
    exact hsp Y (hYsub.trans_eq hedge) hYne

/-- **Matroid restriction descends to subgraphs** (`lem:subgraph-minimality`, engine):
for `H ≤ G`, restricting `M(G̃)` to the edge set `E(H̃)` of the smaller multiplied graph
recovers `M(H̃)`, `M(G̃) ↾ E(H̃) = M(H̃)`. This is the matroid identity Katoh–Tanigawa's
Lemma 3.3 runs on: matroid restriction commutes with the `D`-fold cycle-matroid union
construction. Proved by `Matroid.ext_indep`, routing both sides through the
boundary-regime characterization `matroidMG_indep_iff` (an `E'` is independent in either
matroid iff it is `(D,D)`-sparse, and those sparsities agree by
`isSparse_restrict_mulTilde_congr`). -/
theorem matroidMG_restrict_mulTilde [DecidableEq β] [Finite α] [Finite β] {H G : Graph α β}
    (h : H ≤ G) (n : ℕ) :
    (G.matroidMG n) ↾ E(H.mulTilde n) = H.matroidMG n := by
  have hHG : H.mulTilde n ≤ G.mulTilde n := edgeMultiply_mono h _
  have hground : E(H.mulTilde n) ⊆ E(G.mulTilde n) := hHG.edgeSet_mono
  refine Matroid.ext_indep ?_ fun E' _ ↦ ?_
  · rw [Matroid.restrict_ground_eq, matroidMG, Matroid.restrict_ground_eq]
  · rw [Matroid.restrict_indep_iff, matroidMG_indep_iff, matroidMG_indep_iff]
    constructor
    · rintro ⟨⟨_, hsparse⟩, hsub⟩
      exact ⟨hsub, (isSparse_restrict_mulTilde_congr h n subset_rfl hsub).mp hsparse⟩
    · rintro ⟨hsub, hsparse⟩
      exact ⟨⟨hsub.trans hground, (isSparse_restrict_mulTilde_congr h n subset_rfl hsub).mpr
        hsparse⟩, hsub⟩

/-! ## `D`-deficiency (`def:D-deficiency`)

A *partition* `P` of `V(G)` is encoded by a labeling `f : α → α` (the kernel of `f`,
i.e. its fibers, give the parts; vertices outside `V(G)` are irrelevant). The
*number of parts* `|P|` is the number of distinct `f`-labels carried by the
vertices of `G`, `|f '' V(G)|`, and the *crossing-edge count* `d_G(P)` is the
number of edges of `G` whose two endpoints receive different labels. KT's
`def_{\tilde G}(P) = D(|P| - 1) - (D-1)·d_G(P)` (`D = bodyBarDim n`) is genuinely
signed — a fine partition crossing many edges has *negative* deficiency — so it is
`ℤ`-valued; the deficiency `def(\tilde G) = max_P def_{\tilde G}(P)` takes the
maximum and is `≥ 0` (witnessed by the trivial one-part partition, `partitionDef_one`). -/

/-- The number of edges of `G` **crossing** the partition `P` (encoded by a labeling
`f : α → α`): edges `e ∈ E(G)` with endpoints `x, y` such that `f x ≠ f y`. This is
`d_G(P)` in Katoh–Tanigawa 2011 §2.5. Counted with `Set.ncard` to match the project's
edge-counting idiom. -/
def crossingEdges (G : Graph α β) (f : α → α) : Set β :=
  {e ∈ E(G) | ∃ x y, G.IsLink e x y ∧ f x ≠ f y}

/-- The number of **parts** `|P|` of the partition of `V(G)` encoded by a labeling
`f : α → α`: the number of distinct labels carried by the vertices of `G`,
`|f '' V(G)|`. -/
noncomputable def numParts (G : Graph α β) (f : α → α) : ℕ := (f '' V(G)).ncard

/-- The **`D`-deficiency** of a partition `P` of `V(G)` (`def:D-deficiency`;
Katoh–Tanigawa 2011 §2.5): `def_{\tilde G}(P) = D(|P| - 1) - (D-1)·d_G(P)`, with
`D = bodyBarDim n`, `|P| = numParts G f` the number of parts, and `d_G(P) =
|crossingEdges G f|` the number of edges crossing `P`. `ℤ`-valued because the
quantity is genuinely signed (a fine partition crossing many edges is negative). -/
noncomputable def partitionDef (G : Graph α β) (n : ℕ) (f : α → α) : ℤ :=
  (bodyBarDim n : ℤ) * ((G.numParts f : ℤ) - 1)
    - (bodyBarDim n - 1 : ℤ) * (G.crossingEdges f).ncard

/-- The **`D`-deficiency** of `\tilde G` (`def:D-deficiency`; Katoh–Tanigawa 2011 §2.5):
`def(\tilde G) = max_P def_{\tilde G}(P)`, the maximum of `partitionDef` over all
partitions `P` of `V(G)`. Partitions are quantified as labelings `f : α → α`; over the
`ConditionallyCompleteLinearOrder` `ℤ` the supremum is taken with `iSup`, and under
`[Finite α]` it is a finite supremum, hence attained, bounded, and `≥ 0` (the trivial
one-part partition, `partitionDef_one`, witnesses `0`). It measures how far `\tilde G`
is from being independently realizable as a rigid body-hinge framework. -/
noncomputable def deficiency (G : Graph α β) (n : ℕ) : ℤ :=
  ⨆ f : α → α, G.partitionDef n f

/-- The trivial one-part partition (every vertex labeled identically) crosses no edge
and has a single part, so its `D`-deficiency is `0`. This is the witness that
`def(\tilde G) ≥ 0`. -/
theorem partitionDef_one (G : Graph α β) (n : ℕ) (a : α) (hne : V(G).Nonempty) :
    G.partitionDef n (fun _ => a) = 0 := by
  have hcross : G.crossingEdges (fun _ => a) = ∅ := by
    simp only [crossingEdges, Set.eq_empty_iff_forall_notMem, Set.mem_setOf_eq, not_and]
    rintro e _ ⟨x, y, _, hxy⟩
    exact hxy rfl
  have hparts : G.numParts (fun _ => a) = 1 := by
    rw [numParts]
    rw [show (fun _ : α => a) '' V(G) = {a} from ?_]
    · exact Set.ncard_singleton a
    · exact Set.eq_singleton_iff_nonempty_unique_mem.mpr
        ⟨hne.image _, fun _ hx => by obtain ⟨_, _, rfl⟩ := hx; rfl⟩
  rw [partitionDef, hcross, hparts]
  simp

/-- Under `[Finite α]` the partition-deficiency function `f ↦ def_{\tilde G}(P_f)` ranges
over a finite set (its domain `α → α` is finite), hence its range is bounded above. This
is what makes the `iSup`-form `deficiency` a genuine (attained) finite maximum rather than
the junk value `iSup` returns on an unbounded family; it feeds `le_ciSup` in
`partitionDef_le_deficiency`. -/
theorem bddAbove_range_partitionDef [Finite α] (G : Graph α β) (n : ℕ) :
    BddAbove (Set.range (G.partitionDef n)) :=
  (Set.finite_range _).bddAbove

/-- Each partition's `D`-deficiency is a lower bound for `def(\tilde G)`: `def_{\tilde G}(P_f)
≤ def(\tilde G)` for every labeling `f`. This is the `le_ciSup` half of
`deficiency = ⨆ f, partitionDef n f` and the engine behind every "a partition witnesses a
deficiency lower bound" step (the trivial one-part partition for `def ≥ 0`, and the
`{V', V∖V'}` cut partition used by the structural lemmas). -/
theorem partitionDef_le_deficiency [Finite α] (G : Graph α β) (n : ℕ) (f : α → α) :
    G.partitionDef n f ≤ G.deficiency n :=
  le_ciSup (G.bddAbove_range_partitionDef n) f

/-- The `D`-deficiency of a nonempty graph is nonnegative, `def(\tilde G) ≥ 0`: the trivial
one-part partition (`partitionDef_one`) has deficiency `0`, and `def` is an upper bound for
every partition (`partitionDef_le_deficiency`). The `k` in a `k`-dof graph is therefore
always `≥ 0` for `V(G).Nonempty`. -/
theorem deficiency_nonneg [Finite α] (G : Graph α β) (n : ℕ) (hne : V(G).Nonempty) :
    0 ≤ G.deficiency n := by
  obtain ⟨a, ha⟩ := hne
  calc (0 : ℤ) = G.partitionDef n (fun _ => a) := (G.partitionDef_one n a ⟨a, ha⟩).symm
    _ ≤ G.deficiency n := G.partitionDef_le_deficiency n _

/-! ## `k`-dof and minimal `k`-dof graphs (`def:k-dof`)

A multigraph `G` is a *`k`-dof-graph* (`k` degrees of freedom) when
`def(G̃) = k`; the `0`-dof case is exactly the body-hinge-rigid case
(`thm:body-hinge-tay`). `G` is a *minimal `k`-dof-graph* when, additionally, no
edge can be deleted without changing the deficiency — encoded matroidally as:
every base `B` of `M(G̃)` meets every *edge-fiber* `ẽ` (the `D-1` parallel
copies `{p | p.1 = e}` of an edge `e ∈ E(G)`). Minimal `k`-dof-graphs are the
objects the combinatorial induction of Phase 20 (Theorem 4.9) reduces to the
two-vertex double edge. -/

/-- The **edge-fiber** `ẽ` of an edge `e ∈ E(G)` in the multiplied graph
`G̃ = (D-1)·G` (`def:k-dof`): the `D - 1 = bodyHingeMult n` parallel copies of `e`,
i.e. the set `{p : β × Fin (bodyHingeMult n) | p.1 = e}`. A base of `M(G̃)` meets
`ẽ` exactly when it retains at least one of the `D-1` copies of `e`. -/
def edgeFiber (e : β) (n : ℕ) : Set (β × Fin (bodyHingeMult n)) := {p | p.1 = e}

/-- **The edge-fiber has `D - 1` elements** (`def:k-dof`): `|ẽ| = bodyHingeMult n =
D - 1`, the number of parallel copies of `e` in `G̃ = (D-1)·G`. This is the `|ã̃b| = D − 1`
bound the forest surgery of `lem:forest-surgery-split` (Katoh–Tanigawa 2011 Lemma 4.1)
counts against: the surgery uses fewer than `D - 1` copies of the short-circuit fiber. -/
@[simp]
lemma edgeFiber_ncard (e : β) (n : ℕ) : (edgeFiber e n).ncard = bodyHingeMult n := by
  have : edgeFiber e n = ({e} : Set β) ×ˢ (Set.univ : Set (Fin (bodyHingeMult n))) := by
    ext ⟨e', i⟩; simp [edgeFiber, eq_comm]
  rw [this, Set.ncard_prod, Set.ncard_singleton, Set.ncard_univ, Nat.card_eq_fintype_card,
    Fintype.card_fin, one_mul]

/-- `G` is a **`k`-dof-graph** (`def:k-dof`; Katoh–Tanigawa 2011 §2.5): its
multiplied graph `G̃ = (D-1)·G` has `D`-deficiency `def(G̃) = k`, with
`D = bodyBarDim n`. The `0`-dof case is exactly the body-hinge-rigid case
(`thm:body-hinge-tay`): `G̃` packs `D` edge-disjoint spanning trees. -/
def IsKDof (G : Graph α β) (n : ℕ) (k : ℤ) : Prop := G.deficiency n = k

/-- `G` is a **minimal `k`-dof-graph** (`def:k-dof`; Katoh–Tanigawa 2011 §2.5):
it is a `k`-dof-graph and every base `B` of `M(G̃)` meets every edge-fiber `ẽ`
of an edge `e ∈ E(G)` — no edge of `G` can be deleted without lowering the rank
of `M(G̃)`, hence changing the deficiency. The base/fiber-meeting condition is
phrased over `Matroid.IsBase` and `Graph.edgeFiber`. These are the objects the
combinatorial induction of Phase 20 (Theorem 4.9) reduces to the two-vertex
double edge. -/
def IsMinimalKDof [DecidableEq β] (G : Graph α β) (n : ℕ) (k : ℤ) : Prop :=
  G.IsKDof n k ∧ ∀ B, (G.matroidMG n).IsBase B → ∀ e ∈ E(G), (B ∩ edgeFiber e n).Nonempty

/-- **A minimal `k`-dof-graph is loopless** (the loopless-from-minimality brick of the
`d = 3` assembly, Phase 22h G5/G0; implicit in Katoh–Tanigawa 2011, who work with simple
graphs throughout). A loop `e` at `x` would put a copy `p ∈ ẽ` into some base `B` of
`M(G̃)` — the base/fiber-meeting conjunct of `IsMinimalKDof` forces `B ∩ ẽ ≠ ∅` — but the
singleton `{p}` is *dependent*: by boundary-regime cleanliness (`matroidMG_indep_iff`)
its independence would make `G̃ ↾ {p}` `(D,D)`-sparse, demanding `1 + D ≤ D·|{x}| = D`.
This is what lets the circuit-side producers of `IsProperRigidSubgraph` read off that a
circuit-induced subgraph spans at least two vertices. -/
theorem loopless_of_isMinimalKDof [DecidableEq β] [Finite α] [Finite β] {G : Graph α β}
    {n : ℕ} {k : ℤ} (hG : G.IsMinimalKDof n k) : G.Loopless where
  not_isLoopAt e x hloop := by
    obtain ⟨B, hB⟩ := (G.matroidMG n).exists_isBase
    obtain ⟨p, hpB, hpe⟩ := hG.2 B hB e hloop.edge_mem
    -- `{p}` is independent as a subset of the base `B` …
    have hindep : (G.matroidMG n).Indep {p} :=
      hB.indep.subset (Set.singleton_subset_iff.mpr hpB)
    rw [matroidMG_indep_iff] at hindep
    obtain ⟨hsub, hsparse⟩ := hindep
    -- … but `(D,D)`-sparsity fails on it: the loop copy spans the single vertex `x`.
    have hedge : E(G.mulTilde n ↾ ({p} : Set (β × Fin (bodyHingeMult n)))) = {p} := by
      rw [edgeSet_restrict, Set.inter_eq_right.mpr hsub]
    have hbound := hsparse {p} hedge.ge ⟨p, rfl⟩
    have hspan : ((G.mulTilde n) ↾ ({p} : Set (β × Fin (bodyHingeMult n)))).spanningVerts {p}
        ⊆ {x} := by
      rintro y ⟨q, hq, hinc⟩
      obtain ⟨hincG, -⟩ := restrict_inc.mp hinc
      obtain ⟨z, hlink⟩ := hincG
      have hq1 : q.1 = e := by rw [Set.mem_singleton_iff.mp hq]; exact hpe
      rw [mulTilde_isLink, hq1] at hlink
      exact Set.mem_singleton_iff.mpr (hloop.eq_of_isLink hlink).1.symm
    have hcard : (((G.mulTilde n) ↾ ({p} : Set (β × Fin (bodyHingeMult n)))).spanningVerts
        {p}).ncard ≤ 1 := by
      simpa using Set.ncard_le_ncard hspan (Set.finite_singleton x)
    rw [Set.ncard_singleton] at hbound
    have := Nat.mul_le_mul_left (bodyBarDim n) hcard
    omega

/-! ## Rigid subgraphs and circuits (`def:rigid-subgraph`)

A subgraph `H ⊆ G` (`H ≤ G`, the multigraph `Graph.IsSubgraph` order) is *rigid*
when it is `0`-dof — `def(H̃) = 0` — equivalently (`thm:body-hinge-tay`) `H̃` packs
`D` edge-disjoint spanning trees. It is a *proper* rigid subgraph when its vertex
set is a proper subset on at least two vertices, `2 ≤ |V(H)|` and `V(H) ⊊ V(G)`
(Katoh–Tanigawa 2011 p. 659 requires `1 < |V′|`; without the lower bound the
single-vertex no-edge subgraph is vacuously rigid, so "no proper rigid subgraph"
would be unsatisfiable on any `G` with `2 ≤ |V(G)|`). A *circuit* of `M(G̃)` is a
minimal dependent edge set; this is mathlib's `Matroid.IsCircuit (G.matroidMG n)`.
These are the structural objects the algebraic induction of Phases 21–23 reduces
against (rigid subgraphs feed Case I, circuits feed `lem:circuit-rigid`). -/

/-- `H` is a **rigid subgraph** of `G` (`def:rigid-subgraph`; Katoh–Tanigawa 2011 §3):
`H ≤ G` (a subgraph in the multigraph `Graph.IsSubgraph` order) and `H` is `0`-dof,
i.e. `def(H̃) = 0` with `H̃ = (D-1)·H` and `D = bodyBarDim n`. By
`thm:body-hinge-tay` this is exactly the body-hinge-rigid case: `H̃` packs `D`
edge-disjoint spanning trees. -/
def IsRigidSubgraph (H G : Graph α β) (n : ℕ) : Prop := H ≤ G ∧ H.IsKDof n 0

/-- `H` is a **proper rigid subgraph** of `G` (`def:rigid-subgraph`; Katoh–Tanigawa
2011 §3, p. 659): a rigid subgraph on at least two vertices whose vertex set is a
proper subset of `G`'s, `2 ≤ |V(H)|` and `V(H) ⊊ V(G)`. The `2 ≤ |V(H)|` lower bound
is KT's `1 < |V′|`: without it the single-vertex no-edge subgraph (vacuously `0`-dof —
every partition of one vertex has one part and no crossing edges) would make
`∃ H, IsProperRigidSubgraph` provable on any `G` with two vertices, so the standing
"no proper rigid subgraph" hypothesis of the Case-III layer would be unsatisfiable.
Proper rigid subgraphs are the case-I objects of the algebraic induction
(Phases 21–23). -/
def IsProperRigidSubgraph (H G : Graph α β) (n : ℕ) : Prop :=
  H.IsRigidSubgraph G n ∧ 2 ≤ V(H).ncard ∧ V(H) ⊂ V(G)

/-- A proper rigid subgraph has a nonempty vertex set (from the `2 ≤ |V(H)|`
conjunct) — the weakening the Case-I geometry consumers read off. -/
lemma IsProperRigidSubgraph.vertexSet_nonempty {H G : Graph α β} {n : ℕ}
    (h : H.IsProperRigidSubgraph G n) : V(H).Nonempty :=
  Set.nonempty_of_ncard_ne_zero (by have := h.2.1; omega)

/-! ## A triangle is `0`-dof (`lem:case-III`, the `splitOff`-simplicity triangle brick) -/

/-- **A triangle is body-hinge-rigid** (`0`-dof) for `D = bodyBarDim n ≥ 3`
(Katoh–Tanigawa 2011, "a triangle is a `0`-dof-graph", the `splitOff`-simplicity
obstruction of Lemma 6.7(ii)). Let `H` be a *triangle*: three distinct vertices
`x, y, z` pairwise joined by three distinct edges `exy, eyz, exz` (with `V(H) =
{x, y, z}` and `E(H) = {exy, eyz, exz}` exactly). Then `def(H̃) = 0`.

Unlike a circuit-induced rigid subgraph (`circuit_induces_isRigidSubgraph`), a
triangle at the regime `D ≥ 3` is *exactly* `(D,D)`-tight (`3(D−1) = 2D` at `D = 3`),
so no circuit of `M(H̃)` lives inside it and the circuit route does not apply.
Instead this is the direct `def ≤ 0` computation: `def(H̃) = ⨆_f def_{H̃}(P_f) ≤ 0`
by `ciSup_le`, because every partition `P_f` of the three vertices has `def_{H̃}(P_f)
= D(|P| − 1) − (D−1)·d(P) ≤ 0`. The three label-pattern cases (one part, two parts,
three parts) carry crossing-edge counts `d ∈ {0, 2, 3}` — the singleton-out-of-two
cut crosses both its edges, the all-distinct cut crosses all three — and the
arithmetic `(D−1)·d ≥ D(|P| − 1)` closes for `D ≥ 3` (`D ≥ 2` already suffices for
the two-part case; the three-part case is the binding `3(D−1) ≥ 2D ⟺ D ≥ 3`). With
`def(H̃) ≥ 0` (`deficiency_nonneg`) this forces `def(H̃) = 0`. -/
theorem isKDof_zero_of_triangle [Finite α] {H : Graph α β} {n : ℕ}
    (hD : 3 ≤ bodyBarDim n) {x y z : α} {exy eyz exz : β}
    (hxney : x ≠ y) (hynez : y ≠ z) (hxnez : x ≠ z)
    (hxy : H.IsLink exy x y) (hyz : H.IsLink eyz y z) (hxz : H.IsLink exz x z)
    (hVH : V(H) = {x, y, z})
    (hEH : E(H) = {exy, eyz, exz}) :
    H.IsKDof n 0 := by
  classical
  have hDpos : (1 : ℤ) ≤ (bodyBarDim n : ℤ) := by exact_mod_cast (by omega : 1 ≤ bodyBarDim n)
  have hne : V(H).Nonempty := ⟨x, by rw [hVH]; exact Set.mem_insert x _⟩
  haveI : Nonempty (α → α) := ⟨id⟩
  rw [IsKDof]
  refine le_antisymm ?_ (H.deficiency_nonneg n hne)
  -- `def(H̃) = ⨆_f def_{H̃}(P_f) ≤ 0`: each partition's deficiency is `≤ 0`.
  rw [deficiency]
  refine ciSup_le fun f ↦ ?_
  -- `numParts H f = |{f x, f y, f z}|`.
  have himg : f '' V(H) = {f x, f y, f z} := by
    rw [hVH]; ext w; simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨a, (rfl | rfl | rfl), rfl⟩ <;> tauto
    · rintro (rfl | rfl | rfl)
      exacts [⟨x, Or.inl rfl, rfl⟩, ⟨y, Or.inr (Or.inl rfl), rfl⟩, ⟨z, Or.inr (Or.inr rfl), rfl⟩]
  -- The three edges are pairwise distinct: a shared edge would force a shared endpoint pair.
  have hab_ne : exy ≠ eyz := fun h ↦ by
    obtain ⟨h1, _⟩ | ⟨h1, _⟩ := hxy.eq_and_eq_or_eq_and_eq (h ▸ hyz)
    exacts [hxney h1, hxnez h1]
  have hbc_ne : eyz ≠ exz := fun h ↦ by
    obtain ⟨h1, _⟩ | ⟨h1, _⟩ := hyz.eq_and_eq_or_eq_and_eq (h ▸ hxz)
    exacts [hxney h1.symm, hynez h1]
  have hac_ne : exy ≠ exz := fun h ↦ by
    obtain ⟨_, h2⟩ | ⟨h1, _⟩ := hxy.eq_and_eq_or_eq_and_eq (h ▸ hxz)
    exacts [hynez h2, hxnez h1]
  -- An edge of `H` crosses `P_f` iff its two endpoints disagree under `f`; the three edges
  -- are distinct, so each crossing condition is decided independently.
  have hmem_exy : exy ∈ H.crossingEdges f ↔ f x ≠ f y := by
    simp only [crossingEdges, Set.mem_setOf_eq, hEH, Set.mem_insert_iff, Set.mem_singleton_iff,
      true_or, true_and]
    refine ⟨fun ⟨p, q, hl, hd⟩ ↦ ?_, fun hd ↦ ⟨x, y, hxy, hd⟩⟩
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hxy.eq_and_eq_or_eq_and_eq hl
    exacts [hd, fun h ↦ hd h.symm]
  have hmem_eyz : eyz ∈ H.crossingEdges f ↔ f y ≠ f z := by
    simp only [crossingEdges, Set.mem_setOf_eq, hEH, Set.mem_insert_iff, Set.mem_singleton_iff,
      or_true, true_or, true_and]
    refine ⟨fun ⟨p, q, hl, hd⟩ ↦ ?_, fun hd ↦ ⟨y, z, hyz, hd⟩⟩
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hyz.eq_and_eq_or_eq_and_eq hl
    exacts [hd, fun h ↦ hd h.symm]
  have hmem_exz : exz ∈ H.crossingEdges f ↔ f x ≠ f z := by
    simp only [crossingEdges, Set.mem_setOf_eq, hEH, Set.mem_insert_iff, Set.mem_singleton_iff,
      or_true, true_and]
    refine ⟨fun ⟨p, q, hl, hd⟩ ↦ ?_, fun hd ↦ ⟨x, z, hxz, hd⟩⟩
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hxz.eq_and_eq_or_eq_and_eq hl
    exacts [hd, fun h ↦ hd h.symm]
  -- `crossingEdges H f ⊆ {exy, eyz, exz}`, so it is one of the explicit sub-collections.
  have hcross_sub : H.crossingEdges f ⊆ {exy, eyz, exz} := fun e he ↦ by
    have : e ∈ E(H) := he.1; rwa [hEH] at this
  -- The crux arithmetic: case on the three label equalities (the 5 consistent patterns;
  -- the two transitivity-violating combinations are absurd). For each pattern both the
  -- number of parts `|{f x, f y, f z}|` and the crossing count are pinned, and `omega`
  -- closes `D(|P| − 1) ≤ (D − 1)·d` (binding at `3(D−1) ≥ 2D`, i.e. `D ≥ 3`).
  rw [partitionDef, numParts, himg]
  set D : ℤ := (bodyBarDim n : ℤ) with hDdef
  by_cases hxy' : f x = f y <;> by_cases hyz' : f y = f z <;> by_cases hxz' : f x = f z
  -- (1) all equal: 1 part, 0 crossing edges.
  · have hpts : ({f x, f y, f z} : Set α).ncard = 1 := by
      rw [show ({f x, f y, f z} : Set α) = {f x} by rw [hxy', hyz']; simp]; simp
    have hcr : (H.crossingEdges f).ncard = 0 := by
      rw [show H.crossingEdges f = ∅ from Set.eq_empty_of_forall_notMem fun e he ↦ by
        rcases hcross_sub he with rfl | rfl | rfl
        exacts [hmem_exy.mp he hxy', hmem_eyz.mp he hyz', hmem_exz.mp he hxz']]
      exact Set.ncard_empty β
    rw [hpts, hcr]; push_cast; ring_nf; linarith
  -- (2) fx=fy, fy=fz, fx≠fz: impossible (transitivity).
  · exact absurd (hxy'.trans hyz') hxz'
  -- (3) fx=fy, fy≠fz, fx=fz: impossible (fz=fx=fy so fy=fz).
  · exact absurd (hxz' ▸ hxy'.symm) hyz'
  -- (4) fx=fy, fy≠fz, fx≠fz: 2 parts, edges yz & xz cross (d = 2).
  · have hpts : ({f x, f y, f z} : Set α).ncard = 2 := by
      rw [show ({f x, f y, f z} : Set α) = {f x, f z} by rw [hxy']; simp]
      rw [Set.ncard_pair hxz']
    have hcr : (H.crossingEdges f).ncard = 2 := by
      rw [show H.crossingEdges f = {eyz, exz} from Set.Subset.antisymm
        (fun e he ↦ by
          rcases hcross_sub he with rfl | rfl | rfl
          · exact absurd (hmem_exy.mp he) (not_not.mpr hxy')
          · exact Set.mem_insert _ _
          · exact Set.mem_insert_of_mem _ rfl)
        (fun e he ↦ by
          rcases he with rfl | rfl
          exacts [hmem_eyz.mpr hyz', hmem_exz.mpr hxz'])]
      exact Set.ncard_pair hbc_ne
    rw [hpts, hcr]; push_cast; nlinarith [hDpos]
  -- (5) fx≠fy, fy=fz, fx=fz: impossible (fx=fz=fy so fx=fy).
  · exact absurd (hxz'.trans hyz'.symm) hxy'
  -- (6) fx≠fy, fy=fz, fx≠fz: 2 parts, edges xy & xz cross (d = 2).
  · have hpts : ({f x, f y, f z} : Set α).ncard = 2 := by
      rw [show ({f x, f y, f z} : Set α) = {f x, f y} by rw [hyz']; simp]
      rw [Set.ncard_pair hxy']
    have hcr : (H.crossingEdges f).ncard = 2 := by
      rw [show H.crossingEdges f = {exy, exz} from Set.Subset.antisymm
        (fun e he ↦ by
          rcases hcross_sub he with rfl | rfl | rfl
          · exact Set.mem_insert _ _
          · exact absurd (hmem_eyz.mp he) (not_not.mpr hyz')
          · exact Set.mem_insert_of_mem _ rfl)
        (fun e he ↦ by
          rcases he with rfl | rfl
          exacts [hmem_exy.mpr hxy', hmem_exz.mpr hxz'])]
      exact Set.ncard_pair hac_ne
    rw [hpts, hcr]; push_cast; nlinarith [hDpos]
  -- (7) fx≠fy, fy≠fz, fx=fz: 2 parts, edges xy & yz cross (d = 2).
  · have hpts : ({f x, f y, f z} : Set α).ncard = 2 := by
      rw [show ({f x, f y, f z} : Set α) = {f x, f y} from by
        ext w; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, ← hxz']; tauto]
      rw [Set.ncard_pair hxy']
    have hcr : (H.crossingEdges f).ncard = 2 := by
      rw [show H.crossingEdges f = {exy, eyz} from Set.Subset.antisymm
        (fun e he ↦ by
          rcases hcross_sub he with rfl | rfl | rfl
          · exact Set.mem_insert _ _
          · exact Set.mem_insert_of_mem _ rfl
          · exact absurd (hmem_exz.mp he) (not_not.mpr hxz'))
        (fun e he ↦ by
          rcases he with rfl | rfl
          exacts [hmem_exy.mpr hxy', hmem_eyz.mpr hyz'])]
      exact Set.ncard_pair hab_ne
    rw [hpts, hcr]; push_cast; nlinarith [hDpos]
  -- (8) fx≠fy, fy≠fz, fx≠fz: 3 parts, all three edges cross (d = 3).
  · have hpts : ({f x, f y, f z} : Set α).ncard = 3 := by
      rw [Set.ncard_eq_three]; exact ⟨f x, f y, f z, hxy', hxz', hyz', rfl⟩
    have hcr : (H.crossingEdges f).ncard = 3 := by
      rw [show H.crossingEdges f = {exy, eyz, exz} from Set.Subset.antisymm hcross_sub
        (fun e he ↦ by
          rcases he with rfl | rfl | rfl
          exacts [hmem_exy.mpr hxy', hmem_eyz.mpr hyz', hmem_exz.mpr hxz'])]
      rw [Set.ncard_eq_three]; exact ⟨exy, eyz, exz, hab_ne, hac_ne, hbc_ne, rfl⟩
    rw [hpts, hcr]; push_cast; nlinarith [hDpos]

/-! ## A parallel pair is `0`-dof (G0 brick, Phase 22h) -/

/-- **A parallel pair is body-hinge-rigid** (`0`-dof) for `D = bodyBarDim n ≥ 2`
(the K₂-is-0-dof partition brick; sibling of `isKDof_zero_of_triangle`, used in G0
`simple_of_isMinimalKDof_of_noRigid`). Let `H` be a two-vertex multigraph: two distinct
vertices `x, y` pairwise joined by two distinct parallel edges `e₁, e₂` (with `V(H) = {x, y}`
and `E(H) = {e₁, e₂}` exactly). Then `def(H̃) = 0`.

Proof: `def ≤ 0` by `ciSup_le`, since for every partition `f`: if `f x = f y` (one part,
no crossings) the deficiency is `0`; if `f x ≠ f y` (two parts, both edges cross) the
deficiency is `D·1 − (D−1)·2 = 2 − D ≤ 0` for `D ≥ 2`. Combined with `def ≥ 0`
(`deficiency_nonneg`) this forces `def(H̃) = 0`. -/
theorem isKDof_zero_of_parallel_pair [Finite α] {H : Graph α β} {n : ℕ}
    (hD : 2 ≤ bodyBarDim n) {x y : α} {e₁ e₂ : β}
    (hxy : x ≠ y)
    (hl₁ : H.IsLink e₁ x y) (hl₂ : H.IsLink e₂ x y)
    (hne : e₁ ≠ e₂)
    (hVH : V(H) = {x, y})
    (hEH : E(H) = {e₁, e₂}) :
    H.IsKDof n 0 := by
  classical
  have hDpos : (1 : ℤ) ≤ (bodyBarDim n : ℤ) := by exact_mod_cast (by omega : 1 ≤ bodyBarDim n)
  have hD2 : (2 : ℤ) ≤ (bodyBarDim n : ℤ) := by exact_mod_cast hD
  have hne_v : V(H).Nonempty := ⟨x, by rw [hVH]; exact Set.mem_insert x _⟩
  haveI : Nonempty (α → α) := ⟨id⟩
  rw [IsKDof]
  refine le_antisymm ?_ (H.deficiency_nonneg n hne_v)
  rw [deficiency]
  refine ciSup_le fun f ↦ ?_
  -- `f '' V(H) = {f x, f y}`
  have himg : f '' V(H) = {f x, f y} := by
    rw [hVH]; ext w
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨a, (rfl | rfl), rfl⟩ <;> tauto
    · rintro (rfl | rfl)
      exacts [⟨x, Or.inl rfl, rfl⟩, ⟨y, Or.inr rfl, rfl⟩]
  -- The two crossing-edge membership biconditionals.
  have hmem₁ : e₁ ∈ H.crossingEdges f ↔ f x ≠ f y := by
    simp only [crossingEdges, Set.mem_setOf_eq, hEH, Set.mem_insert_iff, Set.mem_singleton_iff,
      true_or, true_and]
    refine ⟨fun ⟨p, q, hl, hd⟩ ↦ ?_, fun hd ↦ ⟨x, y, hl₁, hd⟩⟩
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hl₁.eq_and_eq_or_eq_and_eq hl
    exacts [hd, fun h ↦ hd h.symm]
  have hmem₂ : e₂ ∈ H.crossingEdges f ↔ f x ≠ f y := by
    simp only [crossingEdges, Set.mem_setOf_eq, hEH, Set.mem_insert_iff, Set.mem_singleton_iff,
      or_true, true_and]
    refine ⟨fun ⟨p, q, hl, hd⟩ ↦ ?_, fun hd ↦ ⟨x, y, hl₂, hd⟩⟩
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hl₂.eq_and_eq_or_eq_and_eq hl
    exacts [hd, fun h ↦ hd h.symm]
  have hcross_sub : H.crossingEdges f ⊆ {e₁, e₂} := fun e he ↦ by
    have : e ∈ E(H) := he.1; rwa [hEH] at this
  rw [partitionDef, numParts, himg]
  set D : ℤ := (bodyBarDim n : ℤ) with hDdef
  by_cases hfxy : f x = f y
  -- Case 1: same label → 1 part, 0 crossings.
  · have hpts : ({f x, f y} : Set α).ncard = 1 := by
      rw [show ({f x, f y} : Set α) = {f x} by rw [hfxy]; simp]; simp
    have hcr : (H.crossingEdges f).ncard = 0 := by
      rw [show H.crossingEdges f = ∅ from Set.eq_empty_of_forall_notMem fun e he ↦ by
        rcases hcross_sub he with rfl | rfl
        exacts [hmem₁.mp he hfxy, hmem₂.mp he hfxy]]
      exact Set.ncard_empty β
    rw [hpts, hcr]; push_cast; ring_nf; linarith
  -- Case 2: different labels → 2 parts, both edges cross.
  · have hpts : ({f x, f y} : Set α).ncard = 2 := Set.ncard_pair hfxy
    have hcr : (H.crossingEdges f).ncard = 2 := by
      rw [show H.crossingEdges f = {e₁, e₂} from Set.Subset.antisymm hcross_sub
        (fun e he ↦ by
          rcases he with rfl | rfl
          exacts [hmem₁.mpr hfxy, hmem₂.mpr hfxy])]
      exact Set.ncard_pair hne
    rw [hpts, hcr]; push_cast; nlinarith [hDpos, hD2]

/-! ## Subgraph minimality (`lem:subgraph-minimality`; KT Lemma 3.3) -/

/-- **Subgraph minimality** (`lem:subgraph-minimality`; Katoh–Tanigawa 2011 Lemma 3.3):
a subgraph `H ≤ G` of a minimal `k`-dof-graph `G` is itself a minimal `k'`-dof-graph,
where `k' = def(H̃)` is whatever deficiency `H` happens to have. (In particular a
*rigid* subgraph — `k' = 0` — of a minimal `k`-dof-graph is a minimal `0`-dof-graph,
the form used in Cases I/III of the algebraic induction.)

The deficiency half (`H.IsKDof n k'`) is supplied as a hypothesis (it is the definition
of `k'`); the content is the base/fiber-meeting minimality transport. The engine is the
matroid identity `M(G̃) ↾ E(H̃) = M(H̃)` (`matroidMG_restrict_mulTilde`): a base `B'` of
`M(H̃)` is an `M(G̃)`-basis of `E(H̃)` (`isBase_restrict_iff'`), so it extends to a base
`B ⊇ B'` of `M(G̃)` (`Indep.exists_isBase_superset`) with `B' = B ∩ E(H̃)` by maximality
(`IsBasis'.eq_of_subset_indep`). Each edge-fiber `ẽ` of an `e ∈ E(H) ⊆ E(G)` lies inside
`E(H̃)`, so `G`'s minimality (`B ∩ ẽ ≠ ∅`) transports to `B' ∩ ẽ = (B ∩ E(H̃)) ∩ ẽ =
B ∩ ẽ ≠ ∅`. -/
theorem subgraph_minimality [DecidableEq β] [Finite α] [Finite β] {H G : Graph α β}
    (h : H ≤ G) {n : ℕ} {k k' : ℤ} (hG : G.IsMinimalKDof n k) (hH : H.IsKDof n k') :
    H.IsMinimalKDof n k' := by
  refine ⟨hH, fun B' hB' e he ↦ ?_⟩
  -- `B'` is a base of `M(H̃) = M(G̃) ↾ E(H̃)`, hence an `M(G̃)`-basis of `E(H̃)`.
  rw [← matroidMG_restrict_mulTilde h n, Matroid.isBase_restrict_iff'] at hB'
  -- Extend the independent set `B'` to a base `B` of `M(G̃)`.
  obtain ⟨B, hB, hB'B⟩ := hB'.indep.exists_isBase_superset
  -- The edge-fiber of `e ∈ E(H)` lies inside `E(H̃)`.
  have hfiber : edgeFiber e n ⊆ E(H.mulTilde n) := by
    intro p hp
    rw [mem_edgeSet_mulTilde, (show p.1 = e from hp)]
    exact he
  -- `B' = B ∩ E(H̃)` by maximality of the basis.
  have hBeq : B' = B ∩ E(H.mulTilde n) :=
    hB'.eq_of_subset_indep (hB.indep.inter_right _)
      (Set.subset_inter hB'B hB'.subset) Set.inter_subset_right
  -- `G`'s minimality gives `B ∩ ẽ ≠ ∅`; restrict to `B'`.
  obtain ⟨p, hp⟩ := hG.2 B hB e (h.edgeSet_mono he)
  exact ⟨p, by rw [hBeq]; exact ⟨⟨hp.1, hfiber hp.2⟩, hp.2⟩⟩

/-! ## A circuit yields a rigid subgraph (`lem:circuit-rigid`; KT Lemma 3.4) -/

/-- **A circuit minus an edge is a maximal sparse subset** (`lem:circuit-rigid`;
Katoh–Tanigawa 2011 Lemma 3.4, matroidal core). Let `X` be a circuit of `M(G̃)` and
`e ∈ X`. Then `X \ {e}` is `(D,D)`-sparse — equivalently, an `M(G̃)`-basis of `X`
(`X \ {e}` is a maximal independent subset of `X`, and `X` itself is dependent). This
is the structural content KT's fundamental-circuit arguments consume (Lemmas 4.5,
6.10–6.11 of the algebraic induction, Phases 21–22): a circuit is exactly one edge
short of being independent on its vertex span.

KT's full Lemma 3.4 concludes that the vertex-induced subgraph `G[V(X)]` is *rigid*
(`0`-dof) — more precisely that `X − e` partitions into `D` edge-disjoint spanning
trees on `V(X)`, i.e. `|X − e| = D(|V(X)| − 1)` exactly. That tightness *equality*
(and the `def(G[V(X)]̃) = 0` reading of it) needs the **lower** bound `|X| >
D(|V(X)| − 1)` forced by `X` being dependent, which in this count matroid is the
reverse direction of the full `def = corank` min–max (`thm:def-eq-corank`, the JJ09
generic-rank identity, risk #4) — deferred with that node. The `(D,D)`-sparse /
basis form here is the upper-bound half, self-contained on the boundary-regime
cleanliness `matroidMG_indep_iff`. -/
theorem isSparse_diff_singleton_of_isCircuit [DecidableEq β] [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} {X : Set (β × Fin (bodyHingeMult n))}
    (hX : (G.matroidMG n).IsCircuit X) {e : β × Fin (bodyHingeMult n)} (he : e ∈ X) :
    ((G.mulTilde n) ↾ (X \ {e})).IsSparse (bodyBarDim n) (bodyBarDim n) ∧
      (G.matroidMG n).IsBasis (X \ {e}) X :=
  ⟨(matroidMG_indep_iff G n).mp (hX.diff_singleton_indep he) |>.2,
    hX.diff_singleton_isBasis he⟩

/-! ## Two-edge-connectivity (`lem:two-edge-conn`; KT Lemma 3.1)

A body-hinge-rigid (`0`-dof) graph `G` is `2`-edge-connected. Mathlib carries no
edge-connectivity predicate for the multigraph `Graph α β` (only for `SimpleGraph`),
so — as flagged in `notes/Phase19.md` — the lemma is phrased directly in the cut form
Katoh–Tanigawa's proof actually uses: for the cut `{V', V∖V'}` induced by a nonempty
proper vertex set `V' ⊊ V(G)`, the number of edges crossing the cut is `≥ 2`. A
crossing count of `≤ 1` would let the trivial bridge cut `{V', V∖V'}` witness
`def(G̃) ≥ D·(2-1) - (D-1)·d_G(P) ≥ D - (D-1) = 1`, contradicting `def(G̃) = 0`. -/

/-- The **cut labeling** of a vertex set `V'`: the labeling `f : α → α` collapsing `V'`
to a representative `a` and its complement to `b`. Its fibers on `V(G)` are `V'` and
`V(G) ∖ V'`, so it encodes the partition `P = {V', V∖V'}` whose crossing edges are
`d_G(V')`. Used by `lem:two-edge-conn` to feed a bridge cut to `partitionDef`. -/
def cutLabeling (V' : Set α) (a b : α) [∀ x, Decidable (x ∈ V')] : α → α :=
  fun x => if x ∈ V' then a else b

/-- The cut labeling of a vertex set `V'` separating `V(G)` (both `a ∈ V' ⊆ V(G)` and a
distinct `b ∈ V(G) ∖ V'`) has exactly two parts: `numParts G (cutLabeling V' a b) = 2`.
The image of `V(G)` is `{a, b}` (every vertex maps to one or the other; both are hit by
`a` itself and `b` itself), and `a ≠ b` because `b ∉ V'`. -/
theorem numParts_cutLabeling {G : Graph α β} {V' : Set α} {a b : α}
    [∀ x, Decidable (x ∈ V')] (ha : a ∈ V') (hb : b ∈ V(G)) (hbV' : b ∉ V')
    (haV : a ∈ V(G)) : G.numParts (cutLabeling V' a b) = 2 := by
  have hab : a ≠ b := fun h => hbV' (h ▸ ha)
  have himg : cutLabeling V' a b '' V(G) = {a, b} := by
    apply Set.Subset.antisymm
    · rintro _ ⟨x, _, rfl⟩
      by_cases hx : x ∈ V' <;> simp [cutLabeling, hx]
    · intro x hx
      rcases hx with hx | hx
      · exact ⟨a, haV, by rw [hx]; simp [cutLabeling, ha]⟩
      · refine ⟨b, hb, ?_⟩
        rw [Set.mem_singleton_iff] at hx
        rw [hx]; simp [cutLabeling, hbV']
  rw [numParts, himg, Set.ncard_pair hab]

/-- **Two-edge-connectivity in cut form** (`lem:two-edge-conn`; Katoh–Tanigawa 2011
Lemma 3.1): a body-hinge-rigid (`0`-dof) graph `G` admits no bridge cut. For a nonempty
proper vertex set `V' ⊊ V(G)` that separates `V(G)` (witnessed by `a ∈ V' ⊆ V(G)` and a
distinct `b ∈ V(G) ∖ V'`), at least two edges cross the cut `{V', V∖V'}`:
`2 ≤ d_G(V') = |crossingEdges G (cutLabeling V' a b)|`.

Proof (KT Lemma 3.1): the cut `{V', V∖V'}` is a two-part partition
(`numParts_cutLabeling`), so `def_{G̃}(P) = D·(2-1) - (D-1)·d_G(P) = D - (D-1)·d_G(P)`.
If `d_G(P) ≤ 1` then `def_{G̃}(P) ≥ D - (D-1) = 1 > 0 = def(G̃)`, contradicting that the
deficiency (an upper bound for every partition, `partitionDef_le_deficiency`) is `0`.
With `D = bodyBarDim n ≥ 1` this forces `d_G(P) ≥ 2`. -/
theorem two_le_crossingEdges_of_isKDof_zero [Finite α] {G : Graph α β} {n : ℕ}
    (hD : 1 ≤ bodyBarDim n) (hrigid : G.IsKDof n 0) {V' : Set α} {a b : α}
    [∀ x, Decidable (x ∈ V')] (ha : a ∈ V') (haV : a ∈ V(G)) (hb : b ∈ V(G))
    (hbV' : b ∉ V') : 2 ≤ (G.crossingEdges (cutLabeling V' a b)).ncard := by
  by_contra hlt
  push Not at hlt
  -- The cut is a two-part partition, so its deficiency is `D - (D-1)·d_G(P)`.
  have hle : G.partitionDef n (cutLabeling V' a b) ≤ G.deficiency n :=
    G.partitionDef_le_deficiency n _
  rw [partitionDef, numParts_cutLabeling ha hb hbV' haV, hrigid] at hle
  push_cast at hle
  -- `def(G̃) = 0`, so `D - (D-1)·d_G(P) ≤ 0`, i.e. `(D-1)·d_G(P) ≥ D`.
  have hc : ((G.crossingEdges (cutLabeling V' a b)).ncard : ℤ) ≤ 1 := by exact_mod_cast by omega
  -- With `d_G(P) ≤ 1` and `D ≥ 1`: `(D-1)·d_G(P) ≤ D-1 < D`. Contradiction.
  have hDpos : (1 : ℤ) ≤ (bodyBarDim n : ℤ) := by exact_mod_cast hD
  nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ (bodyBarDim n : ℤ) - 1)
    (by linarith : (0:ℤ) ≤ 1 - ((G.crossingEdges (cutLabeling V' a b)).ncard : ℤ))]

/-- **A body-hinge-rigid (`0`-dof) graph's multiplied graph is connected** (Track-A
N4a infrastructure below `lem:rigidContract-isMinimalKDof`; `notes/Phase22.md`). For a
`0`-dof graph `G` with `D = bodyBarDim n ≥ 2` (so `bodyHingeMult n = D - 1 ≥ 1`, i.e.
`G̃` carries an edge copy of each hinge — the regime KT works in, `n ≥ 2`), the multiplied
graph `G̃ = (D-1)·G` is preconnected: every pair of vertices is joined by a walk
(vacuous on the empty graph, so no nonemptiness hypothesis). This is the
hypothesis a `cycleMatroid`-under-vertex-collapse argument needs to license the
`collapseTo r V(H)` collapse on a proper rigid subgraph `H` (a disconnected `H` would
collapse several components to one representative, which is not the connected contraction
the cycle matroid sees).

Proof (the cut-partition contradiction of `two_le_crossingEdges_of_isKDof_zero`, run for
connectivity rather than two-edge-connectivity): if `G̃` were *not* preconnected, two
vertices `x, y ∈ V(G)` would lie in distinct components. The connected component
`V' = {z | G̃.ConnBetween x z}` is then a nonempty proper subset of `V(G)` that no edge of
`G` crosses — every `G`-edge `e` linking `u ∈ V'` to `v` lifts to a `G̃`-edge (copy `0`),
so `v` is connected to `x`, hence `v ∈ V'`. The induced two-part cut therefore has
`d_G(V') = 0`, so its deficiency is `D·(2-1) - (D-1)·0 = D ≥ 1 > 0 = def(G̃)`,
contradicting `partitionDef_le_deficiency`. -/
theorem mulTilde_preconnected_of_isKDof_zero [Finite α] {G : Graph α β} {n : ℕ}
    [NeZero (bodyHingeMult n)] (hrigid : G.IsKDof n 0) :
    (G.mulTilde n).Preconnected := by
  classical
  -- `bodyHingeMult n = D - 1 ≥ 1` (so `G̃` has edge copies), hence `D = bodyBarDim n ≥ 2`.
  have hmult : 1 ≤ bodyHingeMult n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hD : 2 ≤ bodyBarDim n := by rw [bodyHingeMult] at hmult; omega
  by_contra hcon
  -- Extract two vertices in distinct components.
  simp only [Preconnected, not_forall] at hcon
  obtain ⟨x, y, hx, hy, hxy⟩ := hcon
  -- `V(G̃) = V(G)` definitionally, so the extracted vertices are vertices of `G`.
  have hxV : x ∈ V(G) := hx
  have hyV : y ∈ V(G) := hy
  -- `V' = {z | x ⇝ z in G̃}` is the connected component of `x`.
  set V' : Set α := {z | (G.mulTilde n).ConnBetween x z} with hV'def
  have hxV' : x ∈ V' := ConnBetween.refl hx
  have hyV' : y ∉ V' := hxy
  -- `f = cutLabeling V' x y` is a genuine two-part partition (`x ∈ V'`, `y ∉ V'`, distinct).
  have hparts : G.numParts (cutLabeling V' x y) = 2 :=
    numParts_cutLabeling hxV' hyV hyV' hxV
  -- No edge of `G` crosses the cut: a crossing `G`-edge lifts (copy `0`) to a `G̃`-edge
  -- joining a vertex of `V'` to one outside, extending the component — impossible.
  have hcross : G.crossingEdges (cutLabeling V' x y) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro e ⟨_, u, v, hlink, hne'⟩
    -- The copy `(e, 0)` is a `G̃`-edge linking `u` and `v`.
    have hp : (G.mulTilde n).IsLink (e, (⟨0, hmult⟩ : Fin (bodyHingeMult n))) u v :=
      (mulTilde_isLink G n).mpr hlink
    have huv : (G.mulTilde n).ConnBetween u v := hp.connBetween
    -- `cutLabeling` takes only the two values `x, y`; `f u ≠ f v` forces one endpoint in
    -- `V'` and the other out, but the edge connects them, so both are in `V'`. Contradiction.
    by_cases hu : u ∈ V' <;> by_cases hv : v ∈ V'
    · exact hne' (by simp [cutLabeling, hu, hv])
    · exact hv ((hu.trans huv : (G.mulTilde n).ConnBetween x v))
    · exact hu ((hv.trans huv.symm : (G.mulTilde n).ConnBetween x u))
    · exact hne' (by simp [cutLabeling, hu, hv])
  -- The two-part, crossing-free cut witnesses `def(G̃) ≥ D ≥ 1 > 0`, contradicting `def = 0`.
  have hle : G.partitionDef n (cutLabeling V' x y) ≤ G.deficiency n :=
    G.partitionDef_le_deficiency n _
  rw [partitionDef, hparts, hcross, hrigid] at hle
  simp only [Set.ncard_empty, Nat.cast_ofNat, Nat.cast_zero, mul_zero, sub_zero] at hle
  have hDpos : (1 : ℤ) ≤ (bodyBarDim n : ℤ) := by exact_mod_cast (by omega : 1 ≤ bodyBarDim n)
  linarith

/-! ## The rank upper bound (`thm:def-eq-corank`, conjecture-relevant half) -/

theorem rank_matroidMG_le [DecidableEq β] [Finite α] [Finite β] (G : Graph α β) (n : ℕ)
    (hne : V(G).Nonempty) :
    (G.matroidMG n).rank ≤ bodyBarDim n * (V(G).ncard - 1) := by
  rw [Matroid.rank_def, Matroid.rk_le_iff]
  intro I hIsub hIndep
  rw [matroidMG_indep_iff] at hIndep
  obtain ⟨hsub, hsparse⟩ := hIndep
  rcases I.eq_empty_or_nonempty with rfl | hIne
  · simp
  -- Apply `(D,D)`-sparsity to `I` itself (`E(G̃ ↾ I) = I`): `|I| + D ≤ D·|spanningVerts I|`.
  have hIedge : E(G.mulTilde n ↾ I) = I := by rw [edgeSet_restrict, inter_eq_right.mpr hsub]
  have hkey := hsparse I hIedge.ge hIne
  -- The spanned vertices sit inside `V(G̃ ↾ I) = V(G̃) = V(G)`, so their count is `≤ |V|`.
  have hspanV : (G.mulTilde n ↾ I).spanningVerts I ⊆ V(G) := by
    refine ((G.mulTilde n ↾ I).spanningVerts_subset_vertexSet I).trans ?_
    rw [vertexSet_restrict]; exact subset_rfl
  have hcardV : ((G.mulTilde n ↾ I).spanningVerts I).ncard ≤ V(G).ncard :=
    Set.ncard_le_ncard hspanV V(G).toFinite
  -- `1 ≤ |V|` (nonempty), so `D·(|V|-1) = D·|V| - D` and the bound `|I| + D ≤ D·|V|` rearranges.
  have hV1 : 1 ≤ V(G).ncard := hne.ncard_pos
  calc I.ncard ≤ bodyBarDim n * V(G).ncard - bodyBarDim n := by
        have := Nat.mul_le_mul_left (bodyBarDim n) hcardV
        omega
    _ = bodyBarDim n * (V(G).ncard - 1) := by rw [Nat.mul_sub, Nat.mul_one]

/-! ## Partition-respecting cycle-matroid rank bound (`thm:def-eq-corank`, piece 1)

The leaf the weak-duality half of the def = corank bridge bottoms out on: for the
edge set `Y` of `G̃` whose every edge stays *within* a part of the partition `P`
encoded by `f` (no crossing edge), the cycle-matroid rank is bounded by
`r_{cycle}(Y) ≤ |V(G)| - |P|`. The point is *rank ≤ vertices − components* together
with *components ≥ #parts*: a within-part edge keeps connectivity inside a part, so
the connected components of `(G̃ ↾ Y)` refine the partition, hence there are at least
`|P| = numParts` of them. -/

/-- A labeling `f` that agrees across the endpoints of every edge of `Y` is constant
on each connected component of the restriction `H ↾ Y`: if `x` and `y` are joined by a
walk in `H ↾ Y`, then `f x = f y`. Proof by induction on the walk — each `cons` step is
an `H ↾ Y`-link, hence an `H`-link with edge in `Y`, so `f` agrees across it. The engine
of the components-refine-the-partition count in `rk_cycleMatroid_within_parts_le`. -/
private theorem label_eq_of_connBetween {α γ : Type*} {H : Graph α γ} {Y : Set γ}
    {f : α → α} (hY : ∀ e ∈ Y, ∀ x y, H.IsLink e x y → f x = f y) {x y : α}
    (h : (H ↾ Y).ConnBetween x y) : f x = f y := by
  obtain ⟨w, hw, rfl, rfl⟩ := h
  induction hw with
  | nil hx => rfl
  | cons hw hlink ih =>
    rw [Graph.restrict_isLink] at hlink
    rw [WList.first_cons, WList.last_cons, hY _ hlink.1 _ _ hlink.2]
    exact ih

/-- **Partition-respecting cycle-matroid rank bound** (`thm:def-eq-corank`, piece 1;
the components-refine-the-partition leaf). For the multiplied graph `G̃ = (D-1)·G`,
the edge set `Y` of within-part fibers under the partition `P` encoded by `f` (every
edge of `Y` joins two equally-labeled vertices) satisfies
`r_{cycle}(Y) + numParts f ≤ |V(G)|`, i.e. `r_{cycle}(Y) ≤ |V(G)| - |P|`.

Via the cycle-matroid rank–component identity `eRank + c = |V|` on the restriction
`G̃ ↾ Y` (which keeps every vertex, so `V(G̃ ↾ Y) = V(G̃) = V(G)`): the rank is
`|V(G)| - c(G̃ ↾ Y)`, and `c(G̃ ↾ Y) ≥ numParts f` because the labeling is constant on
each component (`label_eq_of_connBetween`), so the map sending a label to the component
of one of its vertices is injective. -/
theorem rk_cycleMatroid_within_parts_le [Finite α] [Finite β] (G : Graph α β)
    (n : ℕ) {Y : Set (β × Fin (bodyHingeMult n))} (hYE : Y ⊆ E(G.mulTilde n)) {f : α → α}
    (hY : ∀ p ∈ Y, ∀ x y, (G.mulTilde n).IsLink p x y → f x = f y) :
    (G.mulTilde n).cycleMatroid.rk Y + G.numParts f ≤ V(G).ncard := by
  haveI : Fintype α := Fintype.ofFinite α
  classical
  set H := G.mulTilde n with hH
  have hVH : V(H) = V(G) := by rw [hH, mulTilde]; rfl
  -- Rank–component identity on `H ↾ Y` (vertices preserved): `rk Y + c(H ↾ Y) = |V(G)|`.
  have hrank : H.cycleMatroid.eRk Y = (H ↾ Y).cycleMatroid.eRank := by
    rw [cycleMatroid_restrict, inter_eq_right.mpr hYE, Matroid.eRank_restrict]
  have hid : (H ↾ Y).cycleMatroid.eRank + c(H ↾ Y) = V(G).encard := by
    rw [eRank_cycleMatroid_add_numberOfComponents (H ↾ Y), vertexSet_restrict, hVH]
  -- Choose a total representative-vertex function for each label.
  have hrep : ∀ ℓ : α, ∃ x : α, ℓ ∈ f '' V(G) → x ∈ V(G) ∧ f x = ℓ := by
    intro ℓ
    by_cases hℓ : ℓ ∈ f '' V(G)
    · obtain ⟨x, hx, rfl⟩ := hℓ; exact ⟨x, fun _ => ⟨hx, rfl⟩⟩
    · exact ⟨ℓ, fun h => (hℓ h).elim⟩
  choose rep hrep using hrep
  -- The map `ℓ ↦ walkable (rep ℓ)` injects `f '' V(G)` into the components of `H ↾ Y`.
  have hmaps : Set.MapsTo (fun ℓ => (H ↾ Y).walkable (rep ℓ)) (f '' V(G)) (H ↾ Y).Components := by
    intro ℓ hℓ
    exact mem_components_iff_isCompOf.mpr
      (walkable_isCompOf (x := rep ℓ) (by rw [vertexSet_restrict, hVH]; exact (hrep ℓ hℓ).1))
  have hinj : Set.InjOn (fun ℓ => (H ↾ Y).walkable (rep ℓ)) (f '' V(G)) := by
    intro ℓ hℓ ℓ' hℓ' heq
    simp only [] at heq
    -- `rep ℓ'` lies in `walkable (rep ℓ)`, so the two reps are connected, hence equally labeled.
    have hmem : rep ℓ' ∈ V((H ↾ Y).walkable (rep ℓ)) := by
      rw [heq, mem_walkable_self_iff, vertexSet_restrict, hVH]; exact (hrep ℓ' hℓ').1
    rw [mem_walkable_iff] at hmem
    have hff := label_eq_of_connBetween hY hmem.symm
    rw [(hrep ℓ hℓ).2, (hrep ℓ' hℓ').2] at hff
    exact hff.symm
  have hle_enc : (f '' V(G)).encard ≤ c(H ↾ Y) :=
    Set.encard_le_encard_of_injOn hmaps hinj
  -- Cast to `ℕ`: everything is finite since `V(G).encard` is.
  have hfinV : V(G).encard ≠ ⊤ := by rw [Set.encard_ne_top_iff]; exact V(G).toFinite
  have hnp : (G.numParts f : ℕ∞) ≤ c(H ↾ Y) := by
    rw [numParts, Set.Finite.cast_ncard_eq ((f '' V(G)).toFinite)]; exact hle_enc
  -- `eRk Y = rk Y`, and `rk Y + numParts ≤ rk Y + c = |V(G)|`.
  have hrk_eq : (H.cycleMatroid.rk Y : ℕ∞) = (H ↾ Y).cycleMatroid.eRank := by
    rw [Matroid.cast_rk_eq_eRk_of_finite _ (Set.toFinite Y), hrank]
  have hsum : (H.cycleMatroid.rk Y : ℕ∞) + (G.numParts f : ℕ∞) ≤ (V(G).ncard : ℕ∞) := by
    rw [Set.Finite.cast_ncard_eq V(G).toFinite, ← hid, hrk_eq]
    gcongr
  exact_mod_cast hsum

/-! ## Weak duality (`thm:def-eq-corank`, piece 2)

For every partition `P` of `V(G)`, `rank M(G̃) + def_{G̃}(P) ≤ D(|V| - 1)`, hence
(maximising over `P`) `rank M(G̃) + def(G̃) ≤ D(|V| - 1)` — the `def ≤ corank`
half of the bridge. The Edmonds matroid-partition rank formula (`Union_pow_rk_eq`)
on `X := E(G̃)` with the non-crossing fibers `Y` bounds `rank M(G̃) ≤ D·r_cycle(Y) +
|E(G̃) ∖ Y|`; piece 1 (`rk_cycleMatroid_within_parts_le`) bounds `D·r_cycle(Y) ≤
D(|V| - |P|)`, and the bookkeeping leaf `|E(G̃) ∖ Y| = (D-1)·d_G(P)` (each crossing
edge contributes its `D-1` fibers) makes the two sides match. -/

/-- The **crossing fibers** of `G̃` under the partition `P` encoded by `f`: the fibers
`p ∈ E(G̃)` whose underlying edge `p.1` crosses `P`. Equivalently `E(G̃) ∖ Y` for the
non-crossing fibers `Y`. There are exactly `(D-1)·d_G(P)` of them — each of the
`d_G(P) = |crossingEdges G f|` crossing edges of `G` contributes its `D-1` parallel
copies. -/
private theorem ncard_crossing_fibers (G : Graph α β) (n : ℕ) (f : α → α) :
    {p : β × Fin (bodyHingeMult n) | p.1 ∈ G.crossingEdges f}.ncard =
      bodyHingeMult n * (G.crossingEdges f).ncard := by
  have hprod : {p : β × Fin (bodyHingeMult n) | p.1 ∈ G.crossingEdges f} =
      (G.crossingEdges f) ×ˢ (Set.univ : Set (Fin (bodyHingeMult n))) := by
    ext ⟨e, i⟩; simp
  rw [hprod, Set.ncard_prod, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin,
    mul_comm]

/-- **Weak duality for a single partition** (`thm:def-eq-corank`, piece 2): for the
partition `P` encoded by a labeling `f`, `rank M(G̃) + def_{G̃}(P) ≤ D(|V| - 1)`.
Via the Edmonds partition-rank formula `Union_pow_rk_eq` on `X := E(G̃)` and the
non-crossing fibers `Y = {p ∈ E(G̃) | p.1 ∉ crossingEdges}`: `rank M(G̃) =
rk_Union(E(G̃)) ≤ D·r_cycle(Y) + |E(G̃) ∖ Y|`, where `r_cycle(Y) ≤ |V| - |P|`
(`rk_cycleMatroid_within_parts_le`) and `|E(G̃) ∖ Y| = (D-1)·d_G(P)`
(`ncard_crossing_fibers`). -/
theorem rank_add_partitionDef_le [DecidableEq β] [Finite α] [Finite β] (G : Graph α β)
    (n : ℕ) (hD : 1 ≤ bodyBarDim n) (hne : V(G).Nonempty) (f : α → α) :
    (G.matroidMG n).rank + G.partitionDef n f ≤ bodyBarDim n * ((V(G).ncard : ℤ) - 1) := by
  haveI : Fintype α := Fintype.ofFinite α
  classical
  -- `rank M(G̃) = (Union).rk E(G̃)` (restrict to the ground set is the rank).
  have hrank : (G.matroidMG n).rank =
      (Matroid.Union (fun _ : Fin (bodyBarDim n) ↦ (G.mulTilde n).cycleMatroid)).rk
        E(G.mulTilde n) := by
    rw [matroidMG, Matroid.rank_def, Matroid.restrict_ground_eq,
      Matroid.restrict_rk_eq _ subset_rfl]
  -- The non-crossing fibers `Y ⊆ E(G̃)`.
  set Y : Set (β × Fin (bodyHingeMult n)) :=
    {p | p.1 ∈ E(G) ∧ p.1 ∉ G.crossingEdges f} with hY
  have hYsub : Y ⊆ E(G.mulTilde n) := by
    intro p hp; rw [mem_edgeSet_mulTilde]; exact hp.1
  -- `E(G̃) ∖ Y = {p | p.1 ∈ crossingEdges}`: crossing edges have `p.1 ∈ E(G)`.
  have hdiff : E(G.mulTilde n) \ Y = {p : β × Fin (bodyHingeMult n) | p.1 ∈ G.crossingEdges f} := by
    ext p
    simp only [hY, Set.mem_diff, mem_edgeSet_mulTilde, Set.mem_setOf_eq, not_and,
      not_not]
    constructor
    · rintro ⟨hpE, h⟩; exact h hpE
    · intro hp; exact ⟨(by exact hp.1 : p.1 ∈ E(G)), fun _ => hp⟩
  -- Edmonds rank formula: `rk_Union(E(G̃)) ≤ D·r_cycle(Y) + |E(G̃) ∖ Y|`.
  obtain ⟨_, hle⟩ := Union_pow_rk_eq (G.mulTilde n).cycleMatroid (bodyBarDim n) E(G.mulTilde n)
  have hbound := hle Y hYsub
  -- Within-part hypothesis for piece 1: a non-crossing fiber joins equally-labeled vertices.
  have hwithin : ∀ p ∈ Y, ∀ x y, (G.mulTilde n).IsLink p x y → f x = f y := by
    intro p hp x y hlink
    have hG : G.IsLink p.1 x y := by rw [mulTilde_isLink] at hlink; exact hlink
    by_contra hxy
    exact hp.2 ⟨hp.1, x, y, hG, hxy⟩
  have hpiece1 := G.rk_cycleMatroid_within_parts_le n hYsub hwithin
  -- Cardinality of the crossing fibers.
  have hcard : (E(G.mulTilde n) \ Y).ncard = bodyHingeMult n * (G.crossingEdges f).ncard := by
    rw [hdiff, ncard_crossing_fibers]
  -- Assemble in `ℕ`, then cast. `D = bodyBarDim n`, `D - 1 = bodyHingeMult n`.
  rw [hrank, partitionDef, numParts]
  -- `rank ≤ D·r_cycle(Y) + (D-1)·d_G(P)` and `r_cycle(Y) + |P| ≤ |V|`.
  have hkey : (Matroid.Union (fun _ : Fin (bodyBarDim n) ↦ (G.mulTilde n).cycleMatroid)).rk
      E(G.mulTilde n) ≤ bodyBarDim n * (G.mulTilde n).cycleMatroid.rk Y +
        bodyHingeMult n * (G.crossingEdges f).ncard := by
    rw [← hcard]; exact hbound
  -- `|V| ≥ 1` (nonempty); unfold `numParts` in piece 1 to match the goal's `(f '' V).ncard`.
  have hV1 : 1 ≤ V(G).ncard := hne.ncard_pos
  rw [numParts] at hpiece1
  -- `bodyHingeMult n = D - 1` as ℤ (clean since `D ≥ 1`).
  have hHM : (bodyHingeMult n : ℤ) = (bodyBarDim n : ℤ) - 1 := by rw [bodyHingeMult]; omega
  zify at hkey hpiece1
  rw [hHM] at hkey
  -- `r_cycle(Y) ≤ |V| - |P|` (piece 1) and `rank ≤ D·r + (D-1)·d` (Edmonds); combine.
  set R : ℤ := ((G.mulTilde n).cycleMatroid.rk Y : ℤ) with hR
  set D : ℤ := (bodyBarDim n : ℤ) with hDdef
  nlinarith [hkey, hpiece1, mul_le_mul_of_nonneg_left
    (show R ≤ (V(G).ncard : ℤ) - (f '' V(G)).ncard by linarith)
    (show (0:ℤ) ≤ D by positivity)]

/-- **Weak duality** (`thm:def-eq-corank`, the `def ≤ corank` half): maximising
`rank_add_partitionDef_le` over all partitions gives
`rank M(G̃) + def(G̃) ≤ D(|V| - 1)`. Equivalently `def(G̃) ≤ corank M(G̃)` inside the
rank-`D(|V|-1)` ambient. With the rank upper bound `rank_matroidMG_le`, this is one of
the two inequalities of the full bridge `thm:def-eq-corank`; the reverse direction (a
partition attaining the rank) is the remaining JJ09 min–max content. -/
theorem rank_add_deficiency_le [DecidableEq β] [Finite α] [Finite β] (G : Graph α β)
    (n : ℕ) (hD : 1 ≤ bodyBarDim n) (hne : V(G).Nonempty) :
    (G.matroidMG n).rank + G.deficiency n ≤ bodyBarDim n * ((V(G).ncard : ℤ) - 1) := by
  haveI : Nonempty (α → α) := ⟨fun _ => hne.choose⟩
  rw [deficiency]
  -- `⨆ def_P ≤ bound - rank` by `ciSup_le` on `rank_add_partitionDef_le`.
  have hbound : ⨆ f : α → α, G.partitionDef n f ≤
      bodyBarDim n * ((V(G).ncard : ℤ) - 1) - (G.matroidMG n).rank :=
    ciSup_le fun f => by linarith [G.rank_add_partitionDef_le n hD hne f]
  linarith

/-! ## The reverse inequality (`thm:def-eq-corank`, piece 3)

The substantive Jackson--Jordán min–max content: a vertex-partition `P` attaining the
rank, giving `rank M(G̃) + def_{G̃}(P) ≥ D(|V| - 1)`, equivalently
`def(G̃) ≥ corank M(G̃)`. The optimal edge set `Y₀ ⊆ E(G̃)` of the Edmonds
partition-rank formula (`Union_pow_rk_eq`, existence half) induces a partition `P`
of `V(G)`: the connected components of `G̃ ↾ Y₀`. For that partition the within-part
fibers are exactly `Y₀`, so `r_cycle(Y₀) = |V| - |P|`, and every crossing edge has all
`D-1` of its fibers outside `Y₀`, so `(D-1)·d_G(P) ≤ |E(G̃) ∖ Y₀|`. Together with the
optimal bound `D·r_cycle(Y₀) + |E(G̃) ∖ Y₀| ≤ rank` this gives the reverse inequality. -/

/-- A chosen vertex of a graph `K` (the component graph in `componentLabel`), or an
arbitrary vertex if `K` is empty. Factored through the graph so that the component label
depends only on the `walkable` *graph*, making it constant on a component a `congrArg`. -/
private noncomputable def pickVertex {α γ : Type*} [Nonempty α] (K : Graph α γ) : α := by
  classical exact if h : V(K).Nonempty then h.choose else Classical.arbitrary α

/-- The **component labeling** of a graph `H`: `componentLabel H x` is a chosen vertex of
the connected component (the `walkable` set) of `x`. It is constant on each component
(`componentLabel_eq_of_connBetween`) and connected to its own vertex
(`connBetween_componentLabel`), so its fibers on `V(H)` are exactly the connected
components — the partition the reverse direction of `thm:def-eq-corank` runs on. -/
private noncomputable def componentLabel {α γ : Type*} [Nonempty α] (H : Graph α γ) (x : α) : α :=
  pickVertex (H.walkable x)

private theorem pickVertex_mem {α γ : Type*} [Nonempty α] {K : Graph α γ} (h : V(K).Nonempty) :
    pickVertex K ∈ V(K) := by
  rw [pickVertex]; classical rw [dif_pos h]; exact h.choose_spec

private theorem connBetween_componentLabel {α γ : Type*} [Nonempty α] {H : Graph α γ} {x : α}
    (hx : x ∈ V(H)) : H.ConnBetween x (componentLabel H x) :=
  mem_walkable_iff.mp (pickVertex_mem ⟨x, mem_walkable hx⟩)

private theorem componentLabel_eq_of_connBetween {α γ : Type*} [Nonempty α] {H : Graph α γ}
    {x y : α} (h : H.ConnBetween x y) : componentLabel H x = componentLabel H y :=
  congrArg pickVertex h.walkable_eq_walkable

private theorem connBetween_of_componentLabel_eq {α γ : Type*} [Nonempty α] {H : Graph α γ}
    {x y : α} (hx : x ∈ V(H)) (hy : y ∈ V(H))
    (heq : componentLabel H x = componentLabel H y) : H.ConnBetween x y :=
  ((connBetween_componentLabel hx).trans (heq ▸ (connBetween_componentLabel hy).symm))

/-- The components of `H ↾ Y` number at most the parts of the component labeling `f`:
the map sending each part-label of `f` back to the component of one of its vertices is
the inverse of the component-to-label map, so the labels at least count the components.
This is the reverse of the `numParts ≤ c` inequality inside
`rk_cycleMatroid_within_parts_le`, and it gives the *exact* `r_cycle(Y) + numParts f = |V|`
for the component labeling. -/
private theorem numberOfComponents_le_numParts [Finite α] [Finite β] [Nonempty α] (G : Graph α β)
    (n : ℕ) {Y : Set (β × Fin (bodyHingeMult n))} :
    c((G.mulTilde n) ↾ Y) ≤ (G.numParts (componentLabel ((G.mulTilde n) ↾ Y)) : ℕ∞) := by
  classical
  set H := (G.mulTilde n) ↾ Y with hHdef
  have hVH : V(H) = V(G) := by rw [hHdef, vertexSet_restrict, mulTilde]; rfl
  set f := componentLabel H with hf
  -- A chosen representative vertex of each component.
  set rep : Graph α (β × Fin (bodyHingeMult n)) → α :=
    fun C => pickVertex C with hrep
  have hrepmem : ∀ C : Graph α (β × Fin (bodyHingeMult n)), C.IsCompOf H → rep C ∈ V(C) :=
    fun C hC => pickVertex_mem hC.nonempty
  -- Inject components into the label image `f '' V(G)`.
  have hmaps : Set.MapsTo (fun C => f (rep C)) H.Components (f '' V(G)) := by
    intro C hC
    have hCco : C.IsCompOf H := mem_components_iff_isCompOf.mp hC
    exact ⟨rep C, hVH ▸ vertexSet_mono hCco.le (hrepmem C hCco), rfl⟩
  have hinj : Set.InjOn (fun C => f (rep C)) H.Components := by
    intro C hC C' hC' heq
    have hCco : C.IsCompOf H := mem_components_iff_isCompOf.mp hC
    have hC'co : C'.IsCompOf H := mem_components_iff_isCompOf.mp hC'
    have hc := hrepmem C hCco
    have hc' := hrepmem C' hC'co
    have hconn := connBetween_of_componentLabel_eq (vertexSet_mono hCco.le hc)
      (vertexSet_mono hC'co.le hc') heq
    refine hCco.eq_of_not_disjoint hC'co (Set.not_disjoint_iff.mpr ⟨rep C, hc, ?_⟩)
    rw [hC'co.eq_walkable_of_mem_walkable hc', mem_walkable_iff]
    exact hconn.symm
  -- Components inject into the label image, so `c ≤ |f '' V|`.
  rw [NumberOfComponents, numParts, Set.Finite.cast_ncard_eq ((f '' V(G)).toFinite)]
  exact Set.encard_le_encard_of_injOn hmaps hinj

/-- For the component labeling of `G̃ ↾ Y`, the within-part fibers of `Y` together with the
parts exactly account for the vertices: `r_cycle(Y) + numParts f = |V|`. The `≤` is piece 1
(`rk_cycleMatroid_within_parts_le`, valid since every fiber of `Y` joins same-component, hence
equally-labeled, vertices); the `≥` is `numberOfComponents_le_numParts` plus the rank–component
identity `r_cycle(Y) = |V| - c(G̃ ↾ Y)`. This exactness is what turns the *upper* bound piece 1
gave for weak duality into the *lower* bound the reverse direction needs. -/
private theorem rk_add_numParts_componentLabel [Finite α] [Finite β] [Nonempty α] (G : Graph α β)
    (n : ℕ) {Y : Set (β × Fin (bodyHingeMult n))} (hYE : Y ⊆ E(G.mulTilde n)) :
    (G.mulTilde n).cycleMatroid.rk Y + G.numParts (componentLabel ((G.mulTilde n) ↾ Y))
      = V(G).ncard := by
  classical
  set H := (G.mulTilde n) ↾ Y with hHdef
  have hVH : V(H) = V(G) := by rw [hHdef, vertexSet_restrict, mulTilde]; rfl
  set f := componentLabel H with hf
  -- The fibers of `Y` join equally-labeled vertices (same component, `componentLabel` constant).
  have hwithin : ∀ p ∈ Y, ∀ x y, (G.mulTilde n).IsLink p x y → f x = f y := by
    intro p hp x y hlink
    have hHlink : H.IsLink p x y := by rw [hHdef, restrict_isLink]; exact ⟨hp, hlink⟩
    exact componentLabel_eq_of_connBetween (H := H) hHlink.connBetween
  -- `≤` from piece 1.
  have hle := G.rk_cycleMatroid_within_parts_le n hYE hwithin
  -- `≥` via the rank–component identity and `c ≤ numParts`.
  have hrank : (G.mulTilde n).cycleMatroid.eRk Y = H.cycleMatroid.eRank := by
    rw [hHdef, cycleMatroid_restrict, inter_eq_right.mpr hYE, Matroid.eRank_restrict]
  have hid : H.cycleMatroid.eRank + c(H) = V(G).encard := by
    rw [eRank_cycleMatroid_add_numberOfComponents H, hVH]
  have hrk_eq : ((G.mulTilde n).cycleMatroid.rk Y : ℕ∞) = H.cycleMatroid.eRank := by
    rw [Matroid.cast_rk_eq_eRk_of_finite _ (Set.toFinite Y), hrank]
  have hcle : c(H) ≤ (G.numParts f : ℕ∞) := G.numberOfComponents_le_numParts n (Y := Y)
  -- `|V| = eRank + c ≤ rk + numParts` in `ℕ∞`.
  have hge : (V(G).ncard : ℕ∞) ≤
      ((G.mulTilde n).cycleMatroid.rk Y : ℕ∞) + (G.numParts f : ℕ∞) := by
    rw [hrk_eq, Set.Finite.cast_ncard_eq V(G).toFinite]
    calc V(G).encard = H.cycleMatroid.eRank + c(H) := hid.symm
      _ ≤ H.cycleMatroid.eRank + (G.numParts f : ℕ∞) := by gcongr
  -- Combine `≤` (piece 1) and `≥` into the equality, in `ℕ`.
  have hge' : V(G).ncard ≤ (G.mulTilde n).cycleMatroid.rk Y + G.numParts f := by
    exact_mod_cast hge
  omega

/-- **Weak duality is tight: the reverse inequality** (`thm:def-eq-corank`, piece 3). For a
multigraph `G` with `V(G) ≠ ∅` and `D ≥ 1`, the partition `P` into the connected components
of `G̃ ↾ Y₀` (for the Edmonds-optimal edge set `Y₀`) attains
`rank M(G̃) + def_{G̃}(P) ≥ D(|V| - 1)`, hence `rank M(G̃) + def(G̃) ≥ D(|V| - 1)`, i.e.
`def(G̃) ≥ corank M(G̃)`. With `rank_add_deficiency_le` this is the full bridge.

The existence half of the Edmonds partition-rank formula (`Union_pow_rk_eq`) provides an
edge set `Y₀ ⊆ E(G̃)` with `D·r_cycle(Y₀) + |E(G̃) ∖ Y₀| ≤ rank M(G̃)`. For the component
labeling of `G̃ ↾ Y₀`: every fiber of `Y₀` joins same-component, hence equally-labeled,
vertices, so `Y₀` is non-crossing and `r_cycle(Y₀) + numParts f = |V|`
(`rk_add_numParts_componentLabel`); and every crossing edge's `D-1` fibers all lie outside
`Y₀` (their endpoints are in different components), so the crossing fibers
`{p | p.1 ∈ crossingEdges f}` (numbering `(D-1)·d_G(P)`, `ncard_crossing_fibers`) sit inside
`E(G̃) ∖ Y₀`, giving `(D-1)·d_G(P) ≤ |E(G̃) ∖ Y₀|`. Substituting,
`rank ≥ D(|V| - numParts f) + (D-1)·d_G(P) = D(|V|-1) - def_{G̃}(P)`. -/
theorem le_rank_add_deficiency [DecidableEq β] [Finite α] [Finite β] (G : Graph α β)
    (n : ℕ) (hD : 1 ≤ bodyBarDim n) (hne : V(G).Nonempty) :
    bodyBarDim n * ((V(G).ncard : ℤ) - 1) ≤ (G.matroidMG n).rank + G.deficiency n := by
  haveI : Fintype α := Fintype.ofFinite α
  haveI : Nonempty α := ⟨hne.choose⟩
  classical
  -- `rank M(G̃) = (Union).rk E(G̃)`.
  have hrank : (G.matroidMG n).rank =
      (Matroid.Union (fun _ : Fin (bodyBarDim n) ↦ (G.mulTilde n).cycleMatroid)).rk
        E(G.mulTilde n) := by
    rw [matroidMG, Matroid.rank_def, Matroid.restrict_ground_eq,
      Matroid.restrict_rk_eq _ subset_rfl]
  -- Edmonds-optimal `Y₀ ⊆ E(G̃)`.
  obtain ⟨⟨Y₀, hY₀sub, hY₀le⟩, _⟩ :=
    Union_pow_rk_eq (G.mulTilde n).cycleMatroid (bodyBarDim n) E(G.mulTilde n)
  set f := componentLabel ((G.mulTilde n) ↾ Y₀) with hf
  -- Piece: `r_cycle(Y₀) + numParts f = |V|`.
  have heq := G.rk_add_numParts_componentLabel n hY₀sub
  -- Crossing fibers sit inside `E(G̃) ∖ Y₀`.
  have hcrosssub : {p : β × Fin (bodyHingeMult n) | p.1 ∈ G.crossingEdges f}
      ⊆ E(G.mulTilde n) \ Y₀ := by
    rintro p hp
    obtain ⟨hpE, x, y, hlink, hxy⟩ := hp
    refine ⟨by rw [mem_edgeSet_mulTilde]; exact hpE, fun hpY₀ => hxy ?_⟩
    -- If `p ∈ Y₀`, its endpoints `x, y` are connected in `G̃ ↾ Y₀`, hence equally labeled.
    have hGlink : (G.mulTilde n).IsLink p x y := by rw [mulTilde_isLink]; exact hlink
    have hHlink : ((G.mulTilde n) ↾ Y₀).IsLink p x y := by
      rw [restrict_isLink]; exact ⟨hpY₀, hGlink⟩
    exact componentLabel_eq_of_connBetween (H := (G.mulTilde n) ↾ Y₀) hHlink.connBetween
  have hcrosscard : (bodyHingeMult n) * (G.crossingEdges f).ncard
      ≤ (E(G.mulTilde n) \ Y₀).ncard := by
    rw [← G.ncard_crossing_fibers n f]
    exact Set.ncard_le_ncard hcrosssub (E(G.mulTilde n) \ Y₀).toFinite
  -- The deficiency dominates this partition's deficiency.
  have hdef := G.partitionDef_le_deficiency n f
  rw [partitionDef, numParts] at hdef
  -- `|V| ≥ 1` and `D - 1 = bodyHingeMult n`.
  have hV1 : 1 ≤ V(G).ncard := hne.ncard_pos
  have hHM : (bodyHingeMult n : ℤ) = (bodyBarDim n : ℤ) - 1 := by rw [bodyHingeMult]; omega
  rw [hrank]
  -- Assemble in `ℤ`. `numParts f = (f '' V(G)).ncard`.
  rw [← hf, numParts] at heq
  zify at hY₀le hcrosscard heq
  rw [hHM] at hcrosscard
  set D : ℤ := (bodyBarDim n : ℤ) with hDdef
  set R : ℤ := ((G.mulTilde n).cycleMatroid.rk Y₀ : ℤ) with hR
  set NP : ℤ := ((f '' V(G)).ncard : ℤ) with hNP
  set RKU : ℤ := ((Matroid.Union (fun _ : Fin (bodyBarDim n) ↦ (G.mulTilde n).cycleMatroid)).rk
    E(G.mulTilde n) : ℤ) with hRKU
  set DC : ℤ := ((G.crossingEdges f).ncard : ℤ) with hDC
  set ED : ℤ := ((E(G.mulTilde n) \ Y₀).ncard : ℤ) with hED
  -- hY₀le : D * R + ED ≤ RKU ; heq : R + NP = |V| ; hcrosscard : (D-1)*DC ≤ ED
  -- hdef : def_P = D*(NP-1) - (D-1)*DC ≤ deficiency
  nlinarith [hdef, hY₀le, heq, hcrosscard]

/-! ## The def = corank bridge (`thm:def-eq-corank`; Jackson–Jordán) -/

/-- **`rank M(G̃) + def(G̃) = D(|V| - 1)`** (`thm:def-eq-corank`; Jackson–Jordán 2009 Thm 6.1):
the rank-deficiency identity, assembled from weak duality `rank_add_deficiency_le`
(`def ≤ corank`) and its reverse `le_rank_add_deficiency` (`def ≥ corank`, the substantive
JJ09 min–max content: a vertex-partition — the components of `G̃ ↾ Y₀` for the Edmonds-optimal
`Y₀` — attaining the rank). For `V(G) ≠ ∅` and `D = bodyBarDim n ≥ 1`. -/
theorem rank_add_deficiency_eq [DecidableEq β] [Finite α] [Finite β] (G : Graph α β)
    (n : ℕ) (hD : 1 ≤ bodyBarDim n) (hne : V(G).Nonempty) :
    (G.matroidMG n).rank + G.deficiency n = bodyBarDim n * ((V(G).ncard : ℤ) - 1) :=
  le_antisymm (G.rank_add_deficiency_le n hD hne) (G.le_rank_add_deficiency n hD hne)

/-- **`def(G̃) = corank M(G̃)`** in base form (`thm:def-eq-corank`; Jackson–Jordán 2009
Thm 6.1 / Cor 6.2): for any base `B` of `M(G̃)`, `|B| + def(G̃) = D(|V| - 1)`. The corank
`D(|V|-1) - |B|` against the trivial-motion ambient `D(|V|-1)` equals the deficiency; in
particular `def(G̃) = 0` (`G` body-hinge rigid) iff `|B| = D(|V|-1)`, i.e. `G̃` packs `D`
edge-disjoint spanning trees (Cor 6.2). This closes the Phase-18-inherited reconciliation
node `prop:rigidity-matrix-prop11`. -/
theorem isBase_ncard_add_deficiency_eq [DecidableEq β] [Finite α] [Finite β] (G : Graph α β)
    (n : ℕ) (hD : 1 ≤ bodyBarDim n) (hne : V(G).Nonempty) {B : Set (β × Fin (bodyHingeMult n))}
    (hB : (G.matroidMG n).IsBase B) :
    (B.ncard : ℤ) + G.deficiency n = bodyBarDim n * ((V(G).ncard : ℤ) - 1) := by
  rw [hB.ncard]; exact G.rank_add_deficiency_eq n hD hne

/-- **A rigid subgraph's multiplied graph packs `D` edge-disjoint forests on a base**
(`thm:def-eq-corank` Cor 6.2; Jackson–Jordán 2009, Katoh–Tanigawa 2011 §6.2). The
combinatorial substrate of the Case-I realization producer (`lem:case-I-realization`, Phase 22,
option (a)): a `0`-dof (body-hinge-rigid) graph `H` — `def(H̃) = 0` — has a base `B` of `M(H̃)`
that decomposes into `D = bodyBarDim n` edge-disjoint forests of `H̃ ↾ B`, with the full edge
count `|B| = D(|V(H)| − 1)`.

This is the prerequisite the per-leg rigid-seed construction needs: the single-forest brick
`exists_independent_rigidityRows_of_forest` yields only `(D−1)·|J|` independent rigidity rows from
*one* spanning forest, a factor `(D−1)/D` short of the full `D(|V(H)|−1)` that
`HasFullRankRealization k H` demands; reaching full rank needs the `D`-fold packing assembled here,
not a single tree. The base `B` is a maximal `(D,D)`-independent (hence `(D,D)`-sparse, via
`matroidMG_indep_iff`) edge subset, so `tutte_nash_williams` decomposes it into `D` edge-disjoint
forests; its cardinality is `rank M(H̃) = D(|V(H)|−1)` because `def(H̃) = 0`
(`isBase_ncard_add_deficiency_eq`). Regime `[NeZero (bodyHingeMult n)]` (`D ≥ 1`, also forcing the
copies that `mulTilde` needs); `V(H).Nonempty`.

The `↾ B` restriction is forced: a general rigid `H` may be over-braced (`def(H̃) = 0` with extra
edges), so the *whole* `H̃` need not be sparse — only a base packs into forests. The remaining
Track-A obstruction (`notes/Phase22.md` *Hand-off*, option (a)) is to stack the `D` forests'
rigidity rows to the full `D(|V(H)|−1)` count and produce the rigid seed; this lemma supplies the
forest packing those rows are read off. -/
theorem IsKDof.exists_isBase_isForestPacking [DecidableEq β] [Finite α] [Finite β]
    {H : Graph α β} {n : ℕ} [NeZero (bodyHingeMult n)]
    (hrig : H.IsKDof n 0) (hne : V(H).Nonempty) :
    ∃ B, (H.matroidMG n).IsBase B ∧ ((H.mulTilde n) ↾ B).IsForestPacking (bodyBarDim n) ∧
      (B.ncard : ℤ) = bodyBarDim n * ((V(H).ncard : ℤ) - 1) := by
  have hmult : 1 ≤ bodyHingeMult n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hD : 1 ≤ bodyBarDim n := by rw [bodyHingeMult] at hmult; omega
  obtain ⟨B, hB⟩ := (H.matroidMG n).exists_isBase
  refine ⟨B, hB, ?_, ?_⟩
  · -- `B` independent ⟹ `H̃ ↾ B` is `(D,D)`-sparse ⟹ packs `D` edge-disjoint forests.
    rw [tutte_nash_williams]
    exact ((matroidMG_indep_iff H n).mp hB.indep).2
  · -- `|B| = rank M(H̃) = D(|V(H)| − 1)` since `def(H̃) = 0`.
    have hcount := H.isBase_ncard_add_deficiency_eq n hD hne hB
    rw [hrig] at hcount
    linarith

end Graph
