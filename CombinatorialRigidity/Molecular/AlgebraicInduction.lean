/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.RigidityMatrix
public import CombinatorialRigidity.Molecular.Meet
public import Mathlib.Combinatorics.Graph.Subgraph

/-!
# The algebraic induction: Theorem 5.5 base, Cases I & II (`sec:molecular-algebraic-induction`)

Phase 21, the fifth proof stratum of the molecular-conjecture program (Phases 17–26; see
`notes/MolecularConjecture.md`). Where the combinatorial induction (Phase 20,
`Molecular/Induction.lean`) reduced every minimal `0`-dof-graph to the two-vertex double
edge (Theorem 4.9, `Graph.minimal_kdof_reduction`), this file *realizes* that reduction at
the rigidity-matrix rank: Katoh–Tanigawa 2011 (*A proof of the molecular conjecture*,
Discrete Comput. Geom. **45**, §5, §6.1–6.3) **Theorem 5.5** — every minimal `k`-dof-graph
`G` with `|V| ≥ 2` has a panel-hinge realization `(G,p)` with `rank R(G,p) = D(|V|−1) − k` —
its base case, Case I (proper rigid subgraph), and Case II (`k > 0` splitting). The crux
Case III (`k = 0`, no proper rigid subgraph) is deferred to Phases 22–23.

## The panel layer (`def:panel-hinge-framework`)

Katoh–Tanigawa's *panel-hinge* framework is a **hinge-coplanar** body-hinge framework: at
each vertex all incident hinges lie in a common hyperplane (KT 2011 p.647). The conjecture's
content is that this coplanarity constraint can be met *without losing rigidity*. The
Phase-18 `BodyHingeFramework` carries free hinges with no coplanarity, so the
realization-existence nodes need a **panel layer** on top (`DESIGN.md` *Panel-hinge =
hinge-coplanar body-hinge*). We take the panel-data form: a panel realization assigns each
body `v` a *hyperplane normal* `nᵥ ∈ ℝ^(k+2)`, and the hinge at an edge `e = uv` is the
codimension-2 intersection `panel(u) ∩ panel(v)` of the two panels. Its supporting
`k`-extensor — the screw-space element `ScrewSpace k = ⋀^k ℝ^(k+2)` the rigidity matrix
constrains — is the Grassmann–Cayley meet of the two panels, equivalently
`complementIso (nᵤ ∧ nᵥ)` (`panelSupportExtensor`): the join `nᵤ ∧ nᵥ` is the grade-2
extensor of the two normals (`normalsJoin`, in `⋀^2 ℝ^(k+2)`), and the complement iso
`complementIso : ⋀^2 V ≃ ⋀^(k+2−2) V = ⋀^k V` (Phase 21a, `Molecular/Meet.lean`) lands it in
`ScrewSpace k`. The only general-position condition — the two panels meet transversally — is
then exactly that the two normals are linearly independent
(`panelSupportExtensor_ne_zero_iff`), so coplanarity and transversality both live in the
extensor algebra and no affine-subspace-intersection plumbing is needed. This is the leaf the
panel layer rests on; the panel framework `PanelHingeFramework`, its body-hinge interpretation
`toBodyHinge`, and the coplanarity spec `IsHingeCoplanar` land on top in subsequent commits.

## The rank-induction nodes

This file lands the `sec:molecular-algebraic-induction` dep-graph in dependency order. The
regime-agnostic rank leaf nodes (retained verbatim under the panel layer):

* `RankHypothesis` (`def:rank-hypothesis`) — the realization hypothesis (6.1). Carried in
  the basis-free form of Phase 18 (`Molecular/RigidityMatrix.lean`): the panel-hinge rigidity
  matrix `R(G,p)` is the constraint family cutting out the null space
  `Z(G,p) = F.infinitesimalMotions`, and `rank R(G,p) = D|V| − dim Z(G,p)`
  (`def:rigidity-matrix`'s codimension form, `finrank_screwAssignment`). The target rank
  `rank R(G,p) = D(|V|−1) − k = D|V| − (D + k)` is therefore the null-space dimension
  `dim Z(G,p) = D + k`, the form carried here. (`D = screwDim k`.)
* `theorem_55_base` (`lem:theorem-55-base`) — the `|V| = 2`, `k = 0` base case: the
  two-vertex double edge with two non-parallel hinges (independent supporting extensors)
  realizes the full rank `D = D(2−1) − 0`, i.e. `dim Z(G,p) = D`. The framework is
  infinitesimally rigid (`Z(G,p) = trivialMotions`), so its null space is the `D`-dimensional
  trivial-motion space — exactly the parallel-hinges-full Lemma 5.3
  (`eq_of_hingeConstraint_two_parallel`, Phase 18 green) specialized to the two bodies.

## The rank in basis-free form

Phase 18 carries `rank R(G,p)` as a codimension: the column space is the screw-assignment
space `α → ScrewSpace k` of dimension `D|V|` (`finrank_screwAssignment`), and the null space
is `Z(G,p) = F.infinitesimalMotions`, so `rank R(G,p) = D|V| − dim Z(G,p)`. Rather than carry
the `ℤ`-valued rank and re-derive the column count at each node, the realization hypothesis is
stated directly on the null-space dimension: `RankHypothesis F k` asserts
`dim Z(G,p) = D + k`, the rearrangement of `rank R(G,p) = D(|V|−1) − k`. The two forms are
interchanged by `finrank_screwAssignment`; the null-space form is the one the rank lemmas of
Phase 18 (`finrank_pinnedMotions_add_screwDim`, `finrank_trivialMotions`) already speak.
-/

@[expose] public section

namespace CombinatorialRigidity.Molecular

variable {k : ℕ}

/-! ## The panel support extensor (`def:panel-support-extensor`, panel-layer leaf)

A **panel** at a body is a hyperplane of `ℝ^(k+1)`, carried by its normal vector
`n ∈ ℝ^(k+2)` (homogenized). The hinge at an edge `e = uv` is the codimension-2 intersection
`panel(u) ∩ panel(v)` of the two panels; its supporting `k`-extensor — the element of the
screw space `ScrewSpace k = ⋀^k ℝ^(k+2)` that the rigidity matrix constrains — is the
Grassmann–Cayley **meet** of the two panels. Concretely it is `complementIso (n_u ∧ n_v)`:
the join `n_u ∧ n_v` is the grade-2 extensor of the two normals (`normalsJoin`, landing in
`⋀^2 ℝ^(k+2)`), and the complement iso `complementIso : ⋀^2 V ≃ ⋀^(k+2−2) V = ⋀^k V`
(Phase 21a, `Molecular/Meet.lean`) carries it into `ScrewSpace k`.

This is the leaf the whole panel layer rests on: it produces the supporting extensor of a
panel hinge directly from the per-vertex normals, with the only general-position condition —
the two panels meeting transversally — being exactly the linear independence of the two
normals (`panelSupportExtensor_ne_zero_iff`). So coplanarity (both hinges at `v` lie in
`panel(v)` by construction) and transversality both live in the extensor algebra, and the
panel framework `PanelHingeFramework` (subsequent commit) carries only the per-vertex normals
with no affine-subspace-intersection plumbing. -/

/-- **The grade-2 join of two panel normals** (`def:panel-support-extensor`): the wedge
`n₁ ∧ n₂` of two normal vectors of `ℝ^(k+2)`, landing in the grade-2 piece
`⋀^2 ℝ^(k+2)`. The join of the two panels' poles, dual to the codimension-2 intersection of
the panels themselves; the `complementIso` of this is the panel hinge's supporting extensor
(`panelSupportExtensor`). -/
noncomputable def normalsJoin (n₁ n₂ : Fin (k + 2) → ℝ) :
    ⋀[ℝ]^2 (Fin (k + 2) → ℝ) :=
  exteriorPower.ιMulti ℝ 2 ![n₁, n₂]

/-- The underlying exterior-algebra element of `normalsJoin` is the Phase-17 grade-2 extensor
`extensor ![n₁, n₂]` of the two normals (bridge to the join / extensor API). -/
theorem normalsJoin_coe (n₁ n₂ : Fin (k + 2) → ℝ) :
    (normalsJoin n₁ n₂ : ExteriorAlgebra ℝ (Fin (k + 2) → ℝ)) = extensor ![n₁, n₂] := by
  rw [normalsJoin, exteriorPower.ιMulti_apply_coe, extensor_apply]

/-- **The join of two panel normals is nonzero iff the normals are independent**
(`def:panel-support-extensor`): `normalsJoin n₁ n₂ ≠ 0 ↔ LinearIndependent ℝ ![n₁, n₂]`. The
grade-2 extensor of two vectors vanishes exactly when they are linearly dependent
(`extensor_ne_zero_iff_linearIndependent`, Phase 17); this is the algebraic form of the two
panels meeting transversally (their normals not collinear), the only general-position
condition the panel layer needs. -/
theorem normalsJoin_ne_zero_iff (n₁ n₂ : Fin (k + 2) → ℝ) :
    normalsJoin n₁ n₂ ≠ 0 ↔ LinearIndependent ℝ ![n₁, n₂] := by
  rw [← extensor_ne_zero_iff_linearIndependent (d := k + 1) ![n₁, n₂],
    ← normalsJoin_coe, ne_eq, ne_eq, ← ZeroMemClass.coe_eq_zero (x := normalsJoin n₁ n₂)]

/-- **The panel support extensor** of a hinge between two panels with normals `n₁, n₂`
(`def:panel-support-extensor`): the supporting `k`-extensor `C(p(e)) ∈ ScrewSpace k` of the
codimension-2 intersection `panel(u) ∩ panel(v)`, given as the Grassmann–Cayley meet of the
two panels — the complement iso `complementIso : ⋀^2 V ≃ ⋀^(k+2−2) V` (Phase 21a) of their
grade-2 join `normalsJoin n₁ n₂`. The target grade `k + 2 − 2 = k` is exactly the screw-space
grade, so the result lands in `ScrewSpace k = ⋀^k ℝ^(k+2)` and is consumed verbatim by the
Phase-18 hinge constraint. This is the panel-layer source of supporting extensors, replacing
the body-hinge `affineSubspaceExtensor` of the free-hinge model with a coplanar-by-construction
panel hinge. -/
noncomputable def panelSupportExtensor (n₁ n₂ : Fin (k + 2) → ℝ) : ScrewSpace k :=
  complementIso (k := k) (j := 2) (by omega) (normalsJoin n₁ n₂)

/-- **The panel support extensor is nonzero iff the two panels are transversal**
(`def:panel-support-extensor`): `panelSupportExtensor n₁ n₂ ≠ 0 ↔ LinearIndependent ℝ ![n₁, n₂]`.
The complement iso is a linear equivalence (`complementIso`, Phase 21a), so it sends a nonzero
join to a nonzero extensor; combined with `normalsJoin_ne_zero_iff` the supporting extensor is
nonzero exactly when the two panel normals are independent, i.e. the panels meet
transversally in a genuine codimension-2 hinge. This is the general-position hypothesis the
panel realizations of Theorem 5.5 supply (the panel analogue of the body-hinge framework's
`affineSubspaceExtensor_ne_zero_iff`). -/
theorem panelSupportExtensor_ne_zero_iff (n₁ n₂ : Fin (k + 2) → ℝ) :
    panelSupportExtensor n₁ n₂ ≠ 0 ↔ LinearIndependent ℝ ![n₁, n₂] := by
  rw [panelSupportExtensor, ← normalsJoin_ne_zero_iff]
  exact map_ne_zero_iff _ (complementIso (by omega : 2 ≤ k + 2)).injective

namespace BodyHingeFramework

variable {α β : Type*}

/-- **The realization (generic-rank) hypothesis (6.1)** (`def:rank-hypothesis`): a panel-hinge
framework `(G,p)` realizes the target rank of a `k`-dof-graph when its null space has dimension
`dim Z(G,p) = D + k`, i.e. `rank R(G,p) = D|V| − dim Z(G,p) = D(|V|−1) − k`
(`finrank_screwAssignment`; `D = screwDim k`). This is the predicate Katoh–Tanigawa's
Theorem 5.5 establishes by induction on `|V|`; the base case (`theorem_55_base`) and Cases I/II
exhibit such a realization, and the nonparallel-when-simple refinement is supplied alongside by
the linear independence of the supporting extensors used in each construction. -/
def RankHypothesis (F : BodyHingeFramework k α β) (k' : ℤ) : Prop :=
  (Module.finrank ℝ F.infinitesimalMotions : ℤ) = screwDim k + k'

/-- A framework realizes the rank hypothesis at `k' = 0` exactly when it is infinitesimally
rigid (`def:rank-hypothesis`): the rigid case `rank R(G,p) = D(|V|−1)` is `dim Z(G,p) = D`, the
dimension of the trivial-motion space (`finrank_trivialMotions`), attained exactly when
`Z(G,p) = trivialMotions` (`infinitesimalMotions_eq_trivialMotions_iff`). The forward direction
uses that the trivial motions are a `D`-dimensional subspace of the null space
(`trivialMotions_le_infinitesimalMotions`) whose codimension-zero containment forces equality. -/
theorem rankHypothesis_zero_iff [Nonempty α] [Finite α] (F : BodyHingeFramework k α β) :
    F.RankHypothesis 0 ↔ F.IsInfinitesimallyRigid := by
  haveI : Fintype α := Fintype.ofFinite α
  rw [RankHypothesis, ← F.infinitesimalMotions_eq_trivialMotions_iff]
  constructor
  · intro h
    refine (Submodule.eq_of_le_of_finrank_le F.trivialMotions_le_infinitesimalMotions ?_).symm
    rw [F.finrank_trivialMotions]
    rw [add_zero] at h
    exact_mod_cast h.le
  · intro h
    rw [h, F.finrank_trivialMotions, add_zero]

/-- **Theorem 5.5, base case (`|V| = 2`)** (`lem:theorem-55-base`; Katoh–Tanigawa 2011 §5):
the two-vertex double edge realizes the target rank `D(|V|−1) − k = D − 0 = D` of the minimal
`0`-dof case. Concretely, if a body-hinge framework `F` on a two-body set `α` has two edges
`e₁, e₂` whose supporting extensors `C(p(e₁)), C(p(e₂))` are linearly independent (the
non-parallel-hinges, *general-position* hypothesis), and every link of `G` joins the two
distinct bodies `u v` carried by `e₁` and `e₂`, then `F` realizes the rank hypothesis at
`k' = 0` — equivalently `F.IsInfinitesimallyRigid` (`rankHypothesis_zero_iff`).

This is the parallel-hinges-full Lemma 5.3 (`eq_of_hingeConstraint_two_parallel`, Phase 18
green) specialized to the two bodies: the two `(D−1) × D` hinge-row blocks together have full
rank `D`, so the combined kernel on the relative screw is `{0}` and every infinitesimal motion
is trivial. -/
theorem theorem_55_base [Nonempty α] [Finite α] (F : BodyHingeFramework k α β)
    {e₁ e₂ : β} {u v : α} (huv : u ≠ v)
    (hgen : LinearIndependent ℝ ![F.supportExtensor e₁, F.supportExtensor e₂])
    (h₁ : F.graph.IsLink e₁ u v) (h₂ : F.graph.IsLink e₂ u v)
    (hcover : ∀ w, w = u ∨ w = v) :
    F.RankHypothesis 0 := by
  rw [rankHypothesis_zero_iff]
  intro S hS
  -- Both edges constrain the relative screw `S u - S v`; independence forces `S u = S v`.
  have key : S u = S v :=
    F.eq_of_hingeConstraint_two_parallel S hgen (hS e₁ u v h₁) (hS e₂ u v h₂)
  -- Every body is `u` or `v`, so the motion is constant.
  intro a b
  rcases hcover a with rfl | rfl <;> rcases hcover b with rfl | rfl <;>
    first | rfl | exact key | exact key.symm

/-- **The Case II rank-lift accounting** (`lem:case-II`, skeleton; Katoh–Tanigawa 2011 §6.3
Lemma 6.8): in the basis-free null-space convention, re-inserting a body `v` — equivalently
pinning it — shifts the realization count by exactly `D = screwDim k`. A framework `F` realizes
the target rank at `k'` (`RankHypothesis F k'`, i.e. `dim Z(G,p) = D + k'`) exactly when its
body-`v`-pinned motion subspace has dimension `k'`. This is the `+D` core of the panel-hinge
1-extension: the pinned subspace `pinnedMotions v` is the null space of the rigidity matrix with
`v`'s `D` columns deleted (the smaller framework `G - v`), and `finrank (pinnedMotions v) + D =
dim Z(G,p)` (pin-a-body Lemma 5.1, `finrank_pinnedMotions_add_screwDim`, Phase 18 green). Hence a
realization of the splitting-off `G_v^{ab}` at its inductive count lifts to a realization of `G`
at the same `k'`, the two new hinge-row blocks accounting for the `+D`. The geometric content —
*constructing* the extended framework from a realization of `G_v^{ab}` and the genericity step
(Claim 6.9) ensuring the supporting extensors are in general position — is the remainder of Case
II, deferred with the genericity device. -/
theorem rankHypothesis_iff_finrank_pinnedMotions [Nonempty α] [Finite α]
    (F : BodyHingeFramework k α β) (v : α) (k' : ℤ) :
    F.RankHypothesis k' ↔ (Module.finrank ℝ (F.pinnedMotions v) : ℤ) = k' := by
  rw [RankHypothesis, ← F.finrank_pinnedMotions_add_screwDim v]
  push_cast
  omega

/-! ## The framework-construction op (`def:framework-with-graph`)

Both inductive cases of Theorem 5.5 build a realization of `G` from a realization of a
*different* graph: Case I from the contraction `G/E(H)`, Case II from the splitting-off
`G_v^{ab}`. The shared, citation-free primitive both need is the ability to keep a hinge
assignment fixed while changing the underlying multigraph. We package this as `withGraph`:
the framework on a new graph `G'` carrying the same hinge map (hence the same supporting
extensors and hinge-row blocks).

The one fact this phase needs from it is the *graph-monotonicity* of the motion space: adding
edges (passing to a supergraph) can only shrink the null space `Z(G,p)`, since each new link
imposes another hinge constraint. Dually, deleting edges — the direction Cases I/II travel,
toward the smaller inductive graph — can only enlarge it. This is the combinatorial companion
to the span-monotonicity Lemma 5.2 (`infinitesimalMotions_mono_of_span_le`, fixed graph,
refining spans); together they bound how `rank R(G,p)` moves under the two ways a realization's
data can change. The base identity `withGraph_supportExtensor` (the hinge data, hence every
extensor, is untouched) is what lets the two compose. -/

/-- **The framework on a new graph** (`def:framework-with-graph`): replace the underlying
multigraph of `F` by `G'`, keeping the hinge assignment — hence every supporting extensor
`C(p(e))`, hinge-row block `r(p(e))`, and per-edge constraint. This is the carrier for the
inductive constructions of Cases I and II, which realize a *different* graph (the contraction
`G/E(H)`, the splitting-off `G_v^{ab}`) on the same hinge data of the parent framework. -/
@[simps]
def withGraph (F : BodyHingeFramework k α β) (G' : Graph α β) : BodyHingeFramework k α β where
  graph := G'
  hinge := F.hinge

@[simp]
theorem withGraph_supportExtensor (F : BodyHingeFramework k α β) (G' : Graph α β) (e : β) :
    (F.withGraph G').supportExtensor e = F.supportExtensor e := rfl

@[simp]
theorem withGraph_graph_self (F : BodyHingeFramework k α β) : F.withGraph F.graph = F := rfl

/-- **Graph monotonicity of the motion space** (`lem:motions-mono-of-graph-le`): a supergraph
imposes more hinge constraints, so its null space is contained in the subgraph's. If
`F'.graph ≤ F.graph` and `F'` carries the same hinge data as `F` (the supporting extensors
agree), then every infinitesimal motion of `F` is one of `F'`:
`F.infinitesimalMotions ≤ F'.infinitesimalMotions`. A motion of `F` meets the constraint at
every link of `F.graph`; each link of the smaller `F'.graph` is one of `F.graph`
(`Graph.IsLink.mono`), and the matching extensors carry the same constraint, so it meets every
constraint of `F'`.

The phase reaches this through `withGraph`: `F.infinitesimalMotions ≤ (F.withGraph G').
infinitesimalMotions` whenever `G' ≤ F.graph` (`infinitesimalMotions_le_withGraph_of_le`), the
"deleting edges enlarges the null space" half that Cases I/II use to pass to the smaller
inductive graph. -/
theorem infinitesimalMotions_mono_of_graph_le (F F' : BodyHingeFramework k α β)
    (hle : F'.graph ≤ F.graph)
    (hext : ∀ e, F'.supportExtensor e = F.supportExtensor e) :
    F.infinitesimalMotions ≤ F'.infinitesimalMotions := by
  intro S hS e u v he
  rw [hingeConstraint, hext e]
  exact hS e u v (Graph.IsLink.mono hle he)

/-- **Deleting edges enlarges the motion space** (`lem:motions-mono-of-graph-le`, `withGraph`
form): replacing `F.graph` by any subgraph `G' ≤ F.graph` (keeping the hinge data via
`withGraph`) can only grow the null space — `F.infinitesimalMotions ≤
(F.withGraph G').infinitesimalMotions`. This is the direction Cases I and II travel: from the
parent graph `G` toward the smaller inductive graph (the contraction `G/E(H)` or splitting-off
`G_v^{ab}`), where the realization count is supplied by the induction hypothesis. The supporting
extensors are untouched (`withGraph_supportExtensor`), so this is
`infinitesimalMotions_mono_of_graph_le` specialized to the `withGraph` carrier. -/
theorem infinitesimalMotions_le_withGraph_of_le (F : BodyHingeFramework k α β) {G' : Graph α β}
    (hle : G' ≤ F.graph) :
    F.infinitesimalMotions ≤ (F.withGraph G').infinitesimalMotions :=
  F.infinitesimalMotions_mono_of_graph_le (F.withGraph G') hle fun _ => rfl

/-- **The motion-space dimension does not increase under edge deletion** (`lem:motions-mono-of-
graph-le`, rank form): for `G' ≤ F.graph`, `finrank Z(G,p) ≤ finrank Z(G',p)`, equivalently
`rank R(G',p) ≤ rank R(G,p)` (the rank is the codimension `D|V| − finrank Z`,
`finrank_screwAssignment`). The supergraph has at least the rank of any of its subgraphs — the
"re-adding edges only grows the rank" monotonicity that lifts a realization of a minimal
`k`-dof spanning subgraph to one of the whole multigraph (the step `prop:rigidity-matrix-prop11`
uses to push Theorem 5.5 from minimal `k`-dof-graphs to all multigraphs). Immediate from the
inclusion `infinitesimalMotions_le_withGraph_of_le` and `Submodule.finrank_mono`. -/
theorem finrank_infinitesimalMotions_le_of_graph_le [Finite α] (F : BodyHingeFramework k α β)
    {G' : Graph α β} (hle : G' ≤ F.graph) :
    Module.finrank ℝ F.infinitesimalMotions ≤
      Module.finrank ℝ (F.withGraph G').infinitesimalMotions :=
  Submodule.finrank_mono (F.infinitesimalMotions_le_withGraph_of_le hle)

/-! ## Block-pinning a rigid subgraph (`def:pinned-motions-on`, Case I infra)

Case I of Theorem 5.5 contracts a *proper rigid subgraph* `H`: every body of `V(H)` collapses
to a single body of the contraction `G/E(H)`. The framework-side carrier of that move is
**block-pinning** — fixing the screws of *all* bodies of `V(H)` to zero, the set-level analogue
of `pinnedMotions v`. We package it as `pinnedMotionsOn s`, the infinitesimal motions vanishing
on every body of `s`; pinning a single body is the special case `s = {v}`
(`pinnedMotionsOn_singleton`), and the block pin is the infimum of the single-body pins over
`s` (`pinnedMotionsOn_eq_iInf`). This is the framework primitive Case I's block-triangular
gluing runs on; its `+D·|V(H)|`-style rank accounting (the generalization of the pin-a-body
identity `finrank_pinnedMotions_add_screwDim`) lands with the contraction realization once the
rigid block is placed. -/

/-- **Block-pinning at a set of bodies** (`def:pinned-motions-on`): the infinitesimal motions
`S` vanishing on *every* body of `s ⊆ α`, `∀ v ∈ s, S v = 0`. Fixing a whole block of bodies to
the zero screw is the algebraic effect of contracting them to one pinned body — the move Case I
makes on a rigid subgraph `H` (pin all of `V(H)`). Generalizes the single-body pin
`pinnedMotions v` (`pinnedMotionsOn_singleton`); carried as the submodule of
`infinitesimalMotions` cut out by the conjunction of vanishing conditions. -/
def pinnedMotionsOn (F : BodyHingeFramework k α β) (s : Set α) :
    Submodule ℝ (α → ScrewSpace k) where
  carrier := {S | F.IsInfinitesimalMotion S ∧ ∀ v ∈ s, S v = 0}
  add_mem' {S T} hS hT :=
    ⟨F.infinitesimalMotions.add_mem hS.1 hT.1,
      fun v hv => by rw [Pi.add_apply, hS.2 v hv, hT.2 v hv, add_zero]⟩
  zero_mem' := ⟨F.infinitesimalMotions.zero_mem, fun _ _ => rfl⟩
  smul_mem' c S hS :=
    ⟨F.infinitesimalMotions.smul_mem c hS.1,
      fun v hv => by rw [Pi.smul_apply, hS.2 v hv, smul_zero]⟩

@[simp]
theorem mem_pinnedMotionsOn (F : BodyHingeFramework k α β) (s : Set α) (S : α → ScrewSpace k) :
    S ∈ F.pinnedMotionsOn s ↔ F.IsInfinitesimalMotion S ∧ ∀ v ∈ s, S v = 0 :=
  Iff.rfl

/-- **Block-pinning a single body is body-pinning** (`def:pinned-motions-on`): pinning the
one-element block `{v}` recovers the pin-a-body subspace `pinnedMotions v` of Phase 18, so the
block pin is a genuine generalization. -/
@[simp]
theorem pinnedMotionsOn_singleton (F : BodyHingeFramework k α β) (v : α) :
    F.pinnedMotionsOn {v} = F.pinnedMotions v := by
  ext S
  simp [mem_pinnedMotionsOn, mem_pinnedMotions]

/-- **Block-pinning is the infimum of the single-body pins** (`def:pinned-motions-on`): for a
nonempty block, `pinnedMotionsOn s = ⨅ v ∈ s, pinnedMotions v`. A motion vanishes on the whole
block `s` exactly when it vanishes at each body of `s`, so the block pin is the intersection of
the single-body pins over `s` (the nonemptiness carries the shared `IsInfinitesimalMotion`
condition, which the empty infimum `⊤` would otherwise drop). This is the form Case I's
block-triangular accounting uses to relate the block pin to the per-body pin-a-body identity
(`finrank_pinnedMotions_add_screwDim`). -/
theorem pinnedMotionsOn_eq_iInf (F : BodyHingeFramework k α β) {s : Set α} (hs : s.Nonempty) :
    F.pinnedMotionsOn s = ⨅ v ∈ s, F.pinnedMotions v := by
  obtain ⟨w, hw⟩ := hs
  ext S
  simp only [mem_pinnedMotionsOn, Submodule.mem_iInf, mem_pinnedMotions]
  constructor
  · rintro ⟨hmot, hvan⟩ v hv
    exact ⟨hmot, hvan v hv⟩
  · intro h
    exact ⟨(h w hw).1, fun v hv => (h v hv).2⟩

/-- **Block-pinning shrinks under a larger block** (`def:pinned-motions-on`): pinning more bodies
can only cut the motion space, `s ⊆ t → pinnedMotionsOn t ≤ pinnedMotionsOn s`. Each extra pinned
body imposes one more vanishing condition. -/
theorem pinnedMotionsOn_mono (F : BodyHingeFramework k α β) {s t : Set α} (hst : s ⊆ t) :
    F.pinnedMotionsOn t ≤ F.pinnedMotionsOn s :=
  fun _ hS => ⟨hS.1, fun v hv => hS.2 v (hst hv)⟩

/-- **Block-pinning sits below any single-body pin in the block** (`def:pinned-motions-on`):
for `v ∈ s`, `pinnedMotionsOn s ≤ pinnedMotions v`. Pinning the whole block in particular pins
`v`. -/
theorem pinnedMotionsOn_le_pinnedMotions (F : BodyHingeFramework k α β) {s : Set α} {v : α}
    (hv : v ∈ s) :
    F.pinnedMotionsOn s ≤ F.pinnedMotions v :=
  fun _ hS => ⟨hS.1, hS.2 v hv⟩

end BodyHingeFramework

end CombinatorialRigidity.Molecular
