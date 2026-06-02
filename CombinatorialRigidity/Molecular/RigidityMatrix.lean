/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import CombinatorialRigidity.Molecular.Extensor

/-!
# The panel-hinge rigidity matrix `R(G,p)` (`sec:molecular-rigidity-matrix`)

Phase 18, the second phase of the molecular-conjecture program (Phases 17–26; see
`notes/MolecularConjecture.md`). Where the body-hinge chapter (Phase 16,
`BodyBar/BodyHinge.lean`) *defined* rigidity by reduction to body-bar on the
multiplied graph `(δ-1)·G` (a standard-basis witness, no honest geometry — the
*existence* form), this file builds the **genuine** panel-hinge / body-hinge
rigidity matrix `R(G,p)` of Katoh–Tanigawa 2011 (*A proof of the molecular
conjecture*, Discrete Comput. Geom. **45**, §2.2–2.4), on a realization `p`
assigning a `(d-2)`-dimensional affine *hinge* subspace to each edge.

This file lands the `sec:molecular-rigidity-matrix` dep-graph in dependency order.
The leaf node landing here:

* `BodyHingeFramework` (`def:hinge-constraint`) — a `d`-dimensional body-hinge
  framework `(G,p)` is a multigraph `G : Graph α β` together with a map `p`
  assigning each edge a *hinge*: a `(d-1)`-point family in `ℝ^d` whose affine span
  is a `(d-2)`-dimensional affine subspace. Reparametrizing `d = k+1` to clear the
  `ℕ`-subtraction, a hinge is `Fin k → Fin (k+1) → ℝ` (`k` points in `ℝ^(k+1)`),
  homogenizing to `ℝ^(k+2)`; its supporting `(d-1)`-extensor is the `k`-extensor
  `C(p(e)) = affineSubspaceExtensor (p e) ∈ ⋀^k ℝ^(k+2)` of Phase 17.
* `hingeConstraint` (`def:hinge-constraint`) — identifying an infinitesimal motion
  of a rigid body with a `D`-dimensional *screw center* `S(v)` living in the
  exterior algebra `ExteriorAlgebra ℝ (Fin (k+2) → ℝ)` (where `C(p(e))` lives), the
  hinge `p(e)` constrains the two screw centers `S(u), S(v)` of its endpoints
  `e = uv` to satisfy
  `S(u) - S(v) ∈ span C(p(e)) = Submodule.span ℝ {affineSubspaceExtensor (p e)}`.

## Carrier and dimension

Infinitesimal motions are `D`-dimensional screw centers with `D = (d+1 choose 2)`,
matching Phase 17's extensor space `⋀^(d-1) ℝ^(d+1) ≅ ℝ^D` (here, with `d = k+1`,
`⋀^k ℝ^(k+2)`). We carry the screw center as a full element of
`ExteriorAlgebra ℝ (Fin (k+2) → ℝ)` rather than as a coordinate vector in `ℝ^D`;
`span C(p(e))` is then literally a `Submodule` of that algebra and the hinge
constraint is a membership, with no coordinate identification needed yet. The
concrete `⋀^k ℝ^(k+2) ≅ ℝ^D` identification (and the orthogonal-complement block
`r(p(e))`) is deferred to `def:hinge-row-block` / `def:rigidity-matrix`.

Carrier for the multigraph: mathlib core `Graph α β` (the Phase 13–16 carrier).
Carrier for points: `Fin (k+1) → ℝ`, matching Phase 17's `affineSubspaceExtensor`.
-/

@[expose] public section

namespace CombinatorialRigidity.Molecular

open scoped Matrix

/-- The **screw-center space** of `d = k+1`-dimensional body-hinge rigidity: the
exterior algebra `ExteriorAlgebra ℝ (Fin (k+2) → ℝ)` in which the supporting
extensors `C(·) = affineSubspaceExtensor` of the hinges live. An infinitesimal
motion of a rigid body is a `D`-dimensional *screw center* `S(v)` in this space,
`D = (d+1 choose 2) = (k+2 choose 2)`; we carry the full algebra element rather
than a coordinate vector in `ℝ^D` so that `span C(p(e))` is literally a
`Submodule` of it (`def:hinge-constraint`). -/
abbrev ScrewSpace (k : ℕ) : Type :=
  ExteriorAlgebra ℝ (Fin (k + 2) → ℝ)

/-- A **`d = k+1`-dimensional body-hinge framework** `(G,p)` (`def:hinge-constraint`):
a multigraph `G : Graph α β` together with a *hinge assignment* `hinge` sending each
edge `e : β` to a family of `k` points in `ℝ^(k+1)`, whose affine span is the
`(d-2) = (k-1)`-dimensional affine *hinge* subspace `p(e)`. The supporting
`(d-1) = k`-extensor of the hinge is `C(p(e)) = affineSubspaceExtensor (hinge e)`
(Phase 17), an element of the screw space `⋀^k ℝ^(k+2)`.

The dimension is reparametrized `d = k + 1` (so points live in `ℝ^(k+1)`,
homogenizing to `ℝ^(k+2)`) to clear the `ℕ`-subtractions `d-1`, `d-2` that the
hinge / extensor arities would otherwise carry, matching the Phase 17
`omitTwoExtensor` reparametrization. -/
structure BodyHingeFramework (k : ℕ) (α β : Type*) where
  /-- The underlying multigraph; bodies are vertices, hinges are edges. -/
  graph : Graph α β
  /-- The hinge assignment: each edge `e` gets `k` points in `ℝ^(k+1)` spanning a
  `(k-1)`-dimensional affine hinge subspace. -/
  hinge : β → Fin k → Fin (k + 1) → ℝ

namespace BodyHingeFramework

variable {k : ℕ} {α β : Type*}

/-- The **supporting extensor** `C(p(e))` of the hinge at edge `e`
(`def:hinge-constraint`): the `(d-1) = k`-extensor `affineSubspaceExtensor (hinge e)`
of Phase 17, an element of the screw space `⋀^k ℝ^(k+2)`. It is nonzero exactly when
the `k` hinge points are affinely independent (`affineSubspaceExtensor_ne_zero_iff`),
i.e. when the hinge is a genuine `(k-1)`-dimensional affine subspace. -/
def supportExtensor (F : BodyHingeFramework k α β) (e : β) : ScrewSpace k :=
  affineSubspaceExtensor (F.hinge e)

theorem supportExtensor_apply (F : BodyHingeFramework k α β) (e : β) :
    F.supportExtensor e = affineSubspaceExtensor (F.hinge e) := rfl

/-- The **hinge constraint** at an edge `e = uv` (`def:hinge-constraint`): a screw
assignment `S : α → ScrewSpace k` meets the hinge constraint at `e` between
endpoints `u v : α` when the relative screw center lies in the span of the
supporting extensor,
`S u - S v ∈ span C(p(e)) = Submodule.span ℝ {C(p(e))}`.

This is the honest geometric constraint that the panel-hinge rigidity matrix
`R(G,p)` (`def:rigidity-matrix`) encodes; it supersedes Phase 16's
reduction-form `BodyBar/BodyHinge.lean` definition. -/
def hingeConstraint (F : BodyHingeFramework k α β) (S : α → ScrewSpace k)
    (e : β) (u v : α) : Prop :=
  S u - S v ∈ Submodule.span ℝ {F.supportExtensor e}

theorem hingeConstraint_iff (F : BodyHingeFramework k α β) (S : α → ScrewSpace k)
    (e : β) (u v : α) :
    F.hingeConstraint S e u v ↔
      S u - S v ∈ Submodule.span ℝ {affineSubspaceExtensor (F.hinge e)} :=
  Iff.rfl

/-- The **hinge-row block** `r(p(e))` at an edge `e` (`def:hinge-row-block`): the
orthogonal complement `(span C(p(e)))^⊥` of the hinge's supporting extensor, taken
basis-free as the **dual annihilator** of `span C(p(e))` inside the dual space
`Module.Dual ℝ (ScrewSpace k)`. Its elements are the row functionals `r_i(p(e))`; a
basis of it is the `(D-1)` rows of Katoh–Tanigawa's `(D-1) × D` matrix `r(p(e))`
(`D = (k+2 choose 2) = dim (ScrewSpace k)`, and `span C(p(e))` is `1`-dimensional
when the hinge is genuine, so its annihilator has dimension `D - 1`).

Carrying the orthogonal complement as the annihilator submodule keeps the screw
space as the full `ExteriorAlgebra` element (`def:hinge-constraint`): no explicit
`⋀^k ℝ^(k+2) ≅ ℝ^D` coordinate basis / inner-product structure is forced at this
node. The dot products `(S u - S v) · r_i(p(e))` of the blueprint become the
functional applications `r (S u - S v)`, and the orthogonality `v ⟂ span C ↔ r v = 0
∀ r ∈ (span C)^⊥` is exactly the field-level double-annihilator identity
`Subspace.dualAnnihilator_dualCoannihilator_eq`. -/
def hingeRowBlock (F : BodyHingeFramework k α β) (e : β) :
    Submodule ℝ (Module.Dual ℝ (ScrewSpace k)) :=
  (Submodule.span ℝ {F.supportExtensor e}).dualAnnihilator

theorem hingeRowBlock_apply (F : BodyHingeFramework k α β) (e : β) :
    F.hingeRowBlock e =
      (Submodule.span ℝ {affineSubspaceExtensor (F.hinge e)}).dualAnnihilator :=
  rfl

/-- **The hinge constraint as `(D-1)` linear equations** (`def:hinge-row-block`): a
screw assignment `S` meets the hinge constraint at `e = uv` (`def:hinge-constraint`)
exactly when the relative screw center `S u - S v` is annihilated by every row
functional `r ∈ r(p(e))` of the hinge-row block, i.e. `r (S u - S v) = 0` for all
`r ∈ F.hingeRowBlock e`. This is Katoh–Tanigawa's restatement
`(S(u) - S(v)) · r_i(p(e)) = 0`, `1 ≤ i ≤ D-1`.

The forward direction is `Submodule.dualAnnihilator` membership; the converse is the
field-level double-annihilator identity `Subspace.dualAnnihilator_dualCoannihilator_eq`
(`(span C)^⊥⊥ = span C`), which holds because `ScrewSpace k` is an `ℝ`-vector
space. -/
theorem hingeConstraint_iff_hingeRowBlock (F : BodyHingeFramework k α β)
    (S : α → ScrewSpace k) (e : β) (u v : α) :
    F.hingeConstraint S e u v ↔ ∀ r ∈ F.hingeRowBlock e, r (S u - S v) = 0 := by
  rw [hingeConstraint, hingeRowBlock]
  conv_lhs =>
    rw [← Subspace.dualAnnihilator_dualCoannihilator_eq
      (W := Submodule.span ℝ {F.supportExtensor e}), Submodule.mem_dualCoannihilator]

/-- **Infinitesimal motion** of a body-hinge framework `(G,p)` (`def:rigidity-matrix`): a
screw assignment `S : α → ScrewSpace k` is an infinitesimal motion when it satisfies the
hinge constraint (`def:hinge-constraint`) at *every* edge of `G`, i.e. for every edge `e`
linking endpoints `u v` (`G.IsLink e u v`), the relative screw center `S u - S v` lies in
`span C(p(e))`.

This is membership in the kernel of Katoh–Tanigawa's rigidity matrix `R(G,p)`
(`def:rigidity-matrix`): each oriented edge `e = uv` contributes the block row carrying the
hinge-row block `r(p(e))` in the `D` columns of `u` and `-r(p(e))` in those of `v` (zero
elsewhere), so a vanishing matrix-vector product is exactly the per-edge hinge constraint.
We keep the screw space the full `ExteriorAlgebra` element (`def:hinge-constraint`) and carry
`R(G,p)` as this constraint family on the screw-assignment space `α → ScrewSpace k` rather
than as an explicit `(D-1)|E| × D|V|` real coordinate matrix, matching the basis-free
hinge-row block (`def:hinge-row-block`). -/
def IsInfinitesimalMotion (F : BodyHingeFramework k α β) (S : α → ScrewSpace k) : Prop :=
  ∀ e u v, F.graph.IsLink e u v → F.hingeConstraint S e u v

theorem isInfinitesimalMotion_iff (F : BodyHingeFramework k α β) (S : α → ScrewSpace k) :
    F.IsInfinitesimalMotion S ↔
      ∀ e u v, F.graph.IsLink e u v →
        S u - S v ∈ Submodule.span ℝ {F.supportExtensor e} :=
  Iff.rfl

/-- The constraint of an infinitesimal motion is orientation-independent: it holds for an
oriented edge `e = uv` iff for the reversed orientation `e = vu`. This makes
`IsInfinitesimalMotion` well-defined on the undirected multigraph `G`, where `R(G,p)`'s block
rows come from unoriented edges. (The span of a single vector is closed under negation, and
`S v - S u = -(S u - S v)`.) -/
theorem hingeConstraint_comm (F : BodyHingeFramework k α β) (S : α → ScrewSpace k)
    (e : β) (u v : α) :
    F.hingeConstraint S e u v ↔ F.hingeConstraint S e v u := by
  rw [hingeConstraint, hingeConstraint, ← neg_sub (S v) (S u), Submodule.neg_mem_iff]

/-- The **null space** `Z(G,p)` of the panel-hinge rigidity matrix `R(G,p)`
(`def:rigidity-matrix`): the submodule of all infinitesimal motions inside the screw-assignment
space `α → ScrewSpace k`. By `def:rigidity-matrix` this is `Z(G,p) = ker R(G,p)`; carried
basis-free as the kernel cut out by the per-edge hinge constraints (`IsInfinitesimalMotion`),
its membership is `mem_infinitesimalMotions`. It is a submodule because each hinge constraint
is membership in the fixed subspace `span C(p(e))`, closed under the screw-assignment vector
operations. -/
def infinitesimalMotions (F : BodyHingeFramework k α β) :
    Submodule ℝ (α → ScrewSpace k) where
  carrier := {S | F.IsInfinitesimalMotion S}
  add_mem' {S T} hS hT e u v he := by
    have := hS e u v he
    have := hT e u v he
    rw [hingeConstraint] at *
    simpa [add_sub_add_comm] using Submodule.add_mem _ ‹_› ‹_›
  zero_mem' e u v _ := by simp [hingeConstraint]
  smul_mem' c S hS e u v he := by
    have := hS e u v he
    rw [hingeConstraint] at *
    simpa [Pi.smul_apply, ← smul_sub] using Submodule.smul_mem _ c ‹_›

@[simp]
theorem mem_infinitesimalMotions (F : BodyHingeFramework k α β) (S : α → ScrewSpace k) :
    S ∈ F.infinitesimalMotions ↔ F.IsInfinitesimalMotion S :=
  Iff.rfl

/-- A **trivial infinitesimal motion** (`lem:trivial-motions-rank-bound`): a screw
assignment that is the same screw center on every body, `S u = S v` for all `u v : α`.
These are the rigid-motion screws — the constant assignments — and they form the
`D`-dimensional subspace that the rank bound subtracts off. -/
def IsTrivialMotion (S : α → ScrewSpace k) : Prop :=
  ∀ u v, S u = S v

/-- Every trivial motion is an infinitesimal motion (`lem:trivial-motions-rank-bound`): a
constant screw assignment has `S u - S v = 0`, which lies in every hinge constraint's span,
so it satisfies the hinge constraint at every edge. -/
theorem isInfinitesimalMotion_of_isTrivialMotion (F : BodyHingeFramework k α β)
    {S : α → ScrewSpace k} (hS : IsTrivialMotion S) : F.IsInfinitesimalMotion S := by
  intro e u v _
  rw [hingeConstraint, hS u v, sub_self]
  exact Submodule.zero_mem _

/-- The **trivial-motion subspace** (`lem:trivial-motions-rank-bound`): the submodule of all
trivial infinitesimal motions (constant screw assignments) inside the screw-assignment space
`α → ScrewSpace k`. Katoh–Tanigawa's `D` standard trivial motions `S*_i` span this space, and
its dimension is `D = (k+2 choose 2)`; carried basis-free as the constant assignments, so the
explicit `D` count waits on the `⋀^k ℝ^(k+2) ≅ ℝ^D` coordinatization (`def:rigidity-matrix`).

The framework argument `F` is carried only to give the `F.trivialMotions` dot-notation API
parallel to `F.infinitesimalMotions`: the trivial-motion space depends only on `α` and `k` (the
constant assignments), not on the graph or hinges, hence the `@[nolint unusedArguments]`. -/
@[nolint unusedArguments]
def trivialMotions (_F : BodyHingeFramework k α β) : Submodule ℝ (α → ScrewSpace k) where
  carrier := {S | IsTrivialMotion S}
  add_mem' {S T} hS hT u v := by rw [Pi.add_apply, Pi.add_apply, hS u v, hT u v]
  zero_mem' u v := rfl
  smul_mem' c S hS u v := by rw [Pi.smul_apply, Pi.smul_apply, hS u v]

@[simp]
theorem mem_trivialMotions (F : BodyHingeFramework k α β) (S : α → ScrewSpace k) :
    S ∈ F.trivialMotions ↔ IsTrivialMotion S :=
  Iff.rfl

/-- The trivial motions lie inside the null space `Z(G,p)` (`lem:trivial-motions-rank-bound`):
`trivialMotions ≤ infinitesimalMotions`, since each constant assignment is an infinitesimal
motion (`isInfinitesimalMotion_of_isTrivialMotion`). -/
theorem trivialMotions_le_infinitesimalMotions (F : BodyHingeFramework k α β) :
    F.trivialMotions ≤ F.infinitesimalMotions :=
  fun _ hS => F.isInfinitesimalMotion_of_isTrivialMotion hS

/-- **Infinitesimal rigidity** of a body-hinge framework `(G,p)`
(`def:dof-generic`, `lem:trivial-motions-rank-bound`): every infinitesimal motion is trivial,
i.e. `Z(G,p) ⊆` the trivial motions. Equivalently `rank R(G,p) = D(|V|-1)`; the equality form
of the rank bound waits on the `⋀^k ℝ^(k+2) ≅ ℝ^D` coordinatization (`def:rigidity-matrix`). -/
def IsInfinitesimallyRigid (F : BodyHingeFramework k α β) : Prop :=
  F.infinitesimalMotions ≤ F.trivialMotions

theorem isInfinitesimallyRigid_iff (F : BodyHingeFramework k α β) :
    F.IsInfinitesimallyRigid ↔
      ∀ S, F.IsInfinitesimalMotion S → IsTrivialMotion S :=
  Iff.rfl

/-- Infinitesimal rigidity is the equality `Z(G,p) = trivialMotions` of the two submodules
(`lem:trivial-motions-rank-bound`): one inclusion always holds
(`trivialMotions_le_infinitesimalMotions`), so rigidity — the reverse inclusion — upgrades it to
equality. This is the basis-free form of `rank R(G,p) = D(|V|-1)`: the null space is exactly the
`D(|V|-1)`-corank trivial-motion space. -/
theorem infinitesimalMotions_eq_trivialMotions_iff (F : BodyHingeFramework k α β) :
    F.infinitesimalMotions = F.trivialMotions ↔ F.IsInfinitesimallyRigid :=
  ⟨fun h => h.le, fun h => le_antisymm h F.trivialMotions_le_infinitesimalMotions⟩

/-- The trivial-motion subspace is the **diagonal** of `α → ScrewSpace k`: the range of the
constant-assignment map `s ↦ (fun _ => s)`. This is the `D`-dimensional rigid-motion space of
`lem:trivial-motions-rank-bound`; the linear isomorphism `ScrewSpace k ≃ trivialMotions` it
gives (for `Nonempty α`) is what carries `finrank (trivialMotions) = D` once the
`⋀^k ℝ^(k+2) ≅ ℝ^D` coordinatization is in place (`def:rigidity-matrix`). -/
theorem trivialMotions_eq_range_const (F : BodyHingeFramework k α β) :
    F.trivialMotions =
      LinearMap.range (LinearMap.pi (fun _ : α => LinearMap.id) :
        ScrewSpace k →ₗ[ℝ] α → ScrewSpace k) := by
  ext S
  rw [mem_trivialMotions, LinearMap.mem_range]
  constructor
  · rintro hS
    rcases isEmpty_or_nonempty α with hα | ⟨⟨a⟩⟩
    · exact ⟨0, funext fun u => (hα.false u).elim⟩
    · exact ⟨S a, funext fun u => (hS u a).symm⟩
  · rintro ⟨s, rfl⟩ u v
    rfl

end BodyHingeFramework

end CombinatorialRigidity.Molecular
