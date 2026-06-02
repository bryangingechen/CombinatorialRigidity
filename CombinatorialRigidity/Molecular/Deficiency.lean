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

See `ROADMAP.md` §19 / `notes/Phase19.md` and the `sec:molecular-deficiency`
dep-graph of `blueprint/src/chapter/deficiency.tex`. The remaining nodes (the
structural lemmas KT 3.1/3.3/3.4, and the bridge `thm:def-eq-corank`) land in
subsequent commits.
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

end Graph
