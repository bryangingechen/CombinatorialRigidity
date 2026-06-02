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
  `∅ ≠ V(H) ⊊ V(G)`. A *circuit* of `M(G̃)` is `Matroid.IsCircuit (G.matroidMG n)`.
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

See `ROADMAP.md` §19 / `notes/Phase19.md` and the `sec:molecular-deficiency`
dep-graph of `blueprint/src/chapter/deficiency.tex`. The remaining nodes (KT Lemma 3.4
`lem:circuit-rigid`, and the bridge `thm:def-eq-corank`) land in subsequent commits.
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

/-! ## Rigid subgraphs and circuits (`def:rigid-subgraph`)

A subgraph `H ⊆ G` (`H ≤ G`, the multigraph `Graph.IsSubgraph` order) is *rigid*
when it is `0`-dof — `def(H̃) = 0` — equivalently (`thm:body-hinge-tay`) `H̃` packs
`D` edge-disjoint spanning trees. It is a *proper* rigid subgraph when its vertex
set is a nonempty proper subset `∅ ≠ V(H) ⊊ V(G)`. A *circuit* of `M(G̃)` is a
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
2011 §3): a rigid subgraph whose vertex set is a nonempty proper subset of `G`'s,
`∅ ≠ V(H) ⊊ V(G)`. Proper rigid subgraphs are the case-I objects of the algebraic
induction (Phases 21–23). -/
def IsProperRigidSubgraph (H G : Graph α β) (n : ℕ) : Prop :=
  H.IsRigidSubgraph G n ∧ V(H).Nonempty ∧ V(H) ⊂ V(G)

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
    rw [mulTilde, edgeMultiply_edgeSet, Set.mem_setOf_eq, (show p.1 = e from hp)]
    exact he
  -- `B' = B ∩ E(H̃)` by maximality of the basis.
  have hBeq : B' = B ∩ E(H.mulTilde n) :=
    hB'.eq_of_subset_indep (hB.indep.inter_right _)
      (Set.subset_inter hB'B hB'.subset) Set.inter_subset_right
  -- `G`'s minimality gives `B ∩ ẽ ≠ ∅`; restrict to `B'`.
  obtain ⟨p, hp⟩ := hG.2 B hB e (h.edgeSet_mono he)
  exact ⟨p, by rw [hBeq]; exact ⟨⟨hp.1, hfiber hp.2⟩, hp.2⟩⟩

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

end Graph
