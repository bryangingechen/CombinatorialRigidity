/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import CombinatorialRigidity.Mathlib.LinearAlgebra.Dimension.Constructions
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
`⋀^k ℝ^(k+2)`). We carry the screw center as an element of the **degree-`k` graded
piece** `⋀[ℝ]^k (Fin (k+2) → ℝ)` of the exterior algebra — the subspace in which the
supporting extensors `C(p(e)) = affineSubspaceExtensor (p e)` actually live
(`affineSubspaceExtensor_mem_exteriorPower`) — rather than a coordinate vector in `ℝ^D`;
`span C(p(e))` is then literally a `Submodule` of it and the hinge constraint is a
membership. The concrete `⋀^k ℝ^(k+2) ≅ ℝ^D` identification is realized as the `finrank`
equality `screwSpace_finrank : finrank ℝ (ScrewSpace k) = D` (rather than an explicit
basis), the numeric gate for the rank counts of `lem:trivial-motions-rank-bound` and the
degree of freedom of `def:dof-generic`.

Carrier for the multigraph: mathlib core `Graph α β` (the Phase 13–16 carrier).
Carrier for points: `Fin (k+1) → ℝ`, matching Phase 17's `affineSubspaceExtensor`.
-/

@[expose] public section

namespace CombinatorialRigidity.Molecular

open scoped Matrix

/-- The **screw dimension** `D = (d+1 choose 2) = (k+2 choose 2)` of `d = k+1`-dimensional
body-hinge rigidity: the dimension of the screw-center space `ScrewSpace k`, equal to the
dimension `binom(d+1, 2)` of the space of infinitesimal screw motions of a rigid body in
`ℝ^d` (Katoh–Tanigawa 2011 §2.2). -/
abbrev screwDim (k : ℕ) : ℕ := (k + 2).choose 2

/-- The **screw-center space** of `d = k+1`-dimensional body-hinge rigidity: the degree-`k`
graded piece `⋀[ℝ]^k (Fin (k+2) → ℝ)` of the exterior algebra, in which the supporting
extensors `C(·) = affineSubspaceExtensor` of the hinges live
(`affineSubspaceExtensor_mem_exteriorPower`). An infinitesimal motion of a rigid body is a
`D`-dimensional *screw center* `S(v)` in this space, `D = screwDim k = (k+2 choose 2)`
(`screwSpace_finrank`). We carry the screw center as the graded-piece element (a `Submodule`
of the full exterior algebra) rather than a coordinate vector in `ℝ^D`, so `span C(p(e))` is
literally a `Submodule` of it (`def:hinge-constraint`); the `⋀^k ℝ^(k+2) ≅ ℝ^D` identification
of the blueprint is realized by the `finrank` equality `screwSpace_finrank` rather than an
explicit basis. -/
abbrev ScrewSpace (k : ℕ) : Type :=
  ↥(⋀[ℝ]^k (Fin (k + 2) → ℝ))

/-- **The screw-center space has dimension `D = (k+2 choose 2)`** (`def:rigidity-matrix`,
the deferred `⋀^k ℝ^(k+2) ≅ ℝ^D` coordinatization). Since `ScrewSpace k` is the degree-`k`
graded piece of the exterior algebra of `ℝ^(k+2)`, its dimension is `(k+2).choose k`
(`exteriorPower.finrank_eq`), which equals `(k+2).choose 2 = screwDim k` by the symmetry
`binom(n, j) = binom(n, n-j)`. This is the numeric content of the blueprint's
`⋀^k ℝ^(k+2) ≅ ℝ^D` identification — carried as a `finrank` equality rather than an explicit
basis — and is the gate for every numeric rank count (`lem:trivial-motions-rank-bound`'s
`rank R ≤ D(|V|-1)`, the degree of freedom of `def:dof-generic`). -/
theorem screwSpace_finrank (k : ℕ) : Module.finrank ℝ (ScrewSpace k) = screwDim k := by
  rw [exteriorPower.finrank_eq, Module.finrank_pi, Fintype.card_fin, screwDim,
    ← Nat.choose_symm (Nat.le_add_left 2 k)]
  congr 1

/-- **At most `D` independent supporting extensors** (`def:rigidity-matrix`): any linearly
independent family of `m` screw-space elements has `m ≤ D = screwDim k`, since
`ScrewSpace k` is `D`-dimensional (`screwSpace_finrank`). This is the dimension bound a panel
*cycle* must respect — a cycle whose `m` supporting extensors are independent in the
`D`-dimensional screw space can have at most `m ≤ D` hinges, the upper half `|V| ≤ D` of
Katoh–Tanigawa Lemma 5.4's hypothesis `3 ≤ |V| ≤ D` (`lem:cycle-realization`). Immediate from
the finite-dimensionality bound `LinearIndependent.fintype_card_le_finrank`. -/
theorem card_le_screwDim_of_linearIndependent {k m : ℕ} (c : Fin m → ScrewSpace k)
    (h : LinearIndependent ℝ c) : m ≤ screwDim k := by
  have := h.fintype_card_le_finrank
  rwa [Fintype.card_fin, screwSpace_finrank] at this

/-- A **`d = k+1`-dimensional body-hinge framework** `(G,p)` (`def:hinge-constraint`):
a multigraph `G : Graph α β` together with, for each edge `e : β`, its supporting
`(d-1) = k`-extensor `C(p(e)) = supportExtensor e ∈ ⋀^k ℝ^(k+2)` — the screw-space
element the rigidity matrix constrains. In the affine model `p(e)` is a
`(d-2) = (k-1)`-dimensional affine *hinge* subspace spanned by `k` points of `ℝ^(k+1)`
and `C(p(e)) = affineSubspaceExtensor (p e)` (Phase 17, the smart constructor `ofHinge`);
the panel model (Phase 21, `PanelHingeFramework.toBodyHinge`) supplies it as a
Grassmann–Cayley meet of two panels instead. Carrying the support extensor directly as a
field decouples the rigidity-matrix rank theory from how the extensor arose, so both the
affine hinge and the panel hinge feed the same constraint family.

The dimension is reparametrized `d = k + 1` (so points live in `ℝ^(k+1)`,
homogenizing to `ℝ^(k+2)`) to clear the `ℕ`-subtractions `d-1`, `d-2` that the
hinge / extensor arities would otherwise carry, matching the Phase 17
`omitTwoExtensor` reparametrization. -/
structure BodyHingeFramework (k : ℕ) (α β : Type*) where
  /-- The underlying multigraph; bodies are vertices, hinges are edges. -/
  graph : Graph α β
  /-- The **supporting extensor** `C(p(e))` of the hinge at each edge `e`: the
  `(d-1) = k`-extensor in the screw space `⋀^k ℝ^(k+2)` whose span the relative screw
  center is constrained to lie in (`def:hinge-constraint`). It is nonzero exactly when the
  hinge is genuine (a `(k-1)`-dimensional affine subspace, resp. two transversal panels). -/
  supportExtensor : β → ScrewSpace k

namespace BodyHingeFramework

variable {k : ℕ} {α β : Type*}

/-- The **affine-hinge body-hinge framework** (`def:hinge-constraint`): the canonical
constructor from a *hinge assignment* `hinge` sending each edge `e : β` to a family of `k`
points in `ℝ^(k+1)`, whose affine span is the `(d-2) = (k-1)`-dimensional affine hinge
subspace `p(e)`. Its supporting extensor is `C(p(e)) = affineSubspaceExtensor (hinge e)`
(Phase 17), nonzero exactly when the `k` hinge points are affinely independent
(`affineSubspaceExtensor_ne_zero_iff`). This is the original Phase-18 free-hinge model; the
hinge-coplanar panel model is the alternative constructor `PanelHingeFramework.toBodyHinge`. -/
def ofHinge (G : Graph α β) (hinge : β → Fin k → Fin (k + 1) → ℝ) :
    BodyHingeFramework k α β where
  graph := G
  supportExtensor e :=
    ⟨affineSubspaceExtensor (hinge e), affineSubspaceExtensor_mem_exteriorPower (hinge e)⟩

@[simp]
theorem ofHinge_graph (G : Graph α β) (hinge : β → Fin k → Fin (k + 1) → ℝ) :
    (ofHinge G hinge).graph = G := rfl

theorem ofHinge_supportExtensor_coe (G : Graph α β) (hinge : β → Fin k → Fin (k + 1) → ℝ)
    (e : β) :
    ((ofHinge G hinge).supportExtensor e : ExteriorAlgebra ℝ (Fin (k + 2) → ℝ)) =
      affineSubspaceExtensor (hinge e) := rfl

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
      S u - S v ∈ Submodule.span ℝ {F.supportExtensor e} :=
  Iff.rfl

/-- The **hinge-row block** `r(p(e))` at an edge `e` (`def:hinge-row-block`): the
orthogonal complement `(span C(p(e)))^⊥` of the hinge's supporting extensor, taken
basis-free as the **dual annihilator** of `span C(p(e))` inside the dual space
`Module.Dual ℝ (ScrewSpace k)`. Its elements are the row functionals `r_i(p(e))`; a
basis of it is the `(D-1)` rows of Katoh–Tanigawa's `(D-1) × D` matrix `r(p(e))`
(`D = (k+2 choose 2) = dim (ScrewSpace k)`, and `span C(p(e))` is `1`-dimensional
when the hinge is genuine, so its annihilator has dimension `D - 1`).

Carrying the orthogonal complement as the annihilator submodule keeps the screw
space as the graded-piece element (`def:hinge-constraint`): no explicit
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
      (Submodule.span ℝ {F.supportExtensor e}).dualAnnihilator :=
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

/-- The **relative-screw evaluation** `screwDiff u v : (α → ScrewSpace k) →ₗ[ℝ] ScrewSpace k`
(`def:rigidity-matrix`): the linear map sending a screw assignment `S` to the relative screw
center `S u - S v` of the bodies `u, v`. It is the difference of the two coordinate projections
`proj u − proj v`; the per-edge hinge constraint (`def:hinge-constraint`) and the row functionals
of `R(G,p)` (`hingeRow`) are built from it. -/
def screwDiff (u v : α) : (α → ScrewSpace k) →ₗ[ℝ] ScrewSpace k :=
  (LinearMap.proj u : (α → ScrewSpace k) →ₗ[ℝ] ScrewSpace k) - LinearMap.proj v

@[simp]
theorem screwDiff_apply (u v : α) (S : α → ScrewSpace k) :
    screwDiff (k := k) u v S = S u - S v := by
  rw [screwDiff, LinearMap.sub_apply, LinearMap.proj_apply, LinearMap.proj_apply]

/-- A **row functional** of the panel-hinge rigidity matrix `R(G,p)` (`def:rigidity-matrix`): the
linear functional on the screw-assignment space `α → ScrewSpace k` sending `S ↦ r (S u − S v)`,
for a row `r` of the hinge-row block (`def:hinge-row-block`) at an oriented edge `e = uv`. This is
the coordinatized view of one row of `R(G,p)`: the block row of the oriented edge `e = uv` carries
the dual element `r` in `u`'s `D` columns and `−r` in `v`'s, zero elsewhere, so its dot product
with `S` is exactly `r (S u − S v)`. Built basis-free as `r ∘ₗ screwDiff u v` — the composite of
the relative-screw evaluation `screwDiff` with the hinge-row-block functional `r ∈ Module.Dual ℝ
(ScrewSpace k)` — so that the rigidity matrix is carried as the *family* of these functionals
(`rigidityRows`) and its null space `Z(G,p)` is their common kernel
(`infinitesimalMotions_eq_dualCoannihilator`). It depends only on the endpoints `u v` and the row
`r`, not on which edge `e` carries the hinge; the edge is recorded only at the family level
(`rigidityRows`, which pairs `u v` with the rows of the edge's hinge-row block). -/
def hingeRow (u v : α) (r : Module.Dual ℝ (ScrewSpace k)) :
    Module.Dual ℝ (α → ScrewSpace k) :=
  r ∘ₗ screwDiff (k := k) u v

@[simp]
theorem hingeRow_apply (u v : α) (r : Module.Dual ℝ (ScrewSpace k))
    (S : α → ScrewSpace k) :
    hingeRow (k := k) (α := α) u v r S = r (S u - S v) := by
  rw [hingeRow, LinearMap.comp_apply, screwDiff_apply]

/-- The **relative-screw evaluation is surjective at distinct bodies** (`def:rigidity-matrix`):
when `u ≠ v`, `screwDiff u v : (α → ScrewSpace k) →ₗ[ℝ] ScrewSpace k` (the map `S ↦ S u − S v`) is
surjective. Any target screw `x` is hit by the assignment placing `x` on `u` and `0` elsewhere
(`Function.update 0 u x`): at `u` it reads `x`, at the distinct `v` it reads `0`, so
`S u − S v = x`. This is the dual of the row-functional injectivity `hingeRow` carries
(`hingeRow_eq_dualMap`): a
genuine edge `e = uv` (distinct endpoints) reads every relative screw, so its block of rows
faithfully sees the whole hinge-row block. -/
theorem screwDiff_surjective {u v : α} (huv : u ≠ v) :
    Function.Surjective (screwDiff (k := k) (α := α) u v) := by
  classical
  intro x
  refine ⟨Function.update 0 u x, ?_⟩
  rw [screwDiff_apply, Function.update_self, Function.update_of_ne huv.symm, Pi.zero_apply,
    sub_zero]

/-- The **row functional is the dual map of the relative-screw evaluation** (`def:rigidity-matrix`):
`hingeRow u v r = (screwDiff u v).dualMap r`. Definitional — both sides are `r ∘ₗ screwDiff u v`
(`LinearMap.dualMap_apply'`) — but naming it lets the independence bridge
`linearIndependent_hingeRow` route through the dual-map injectivity
`LinearMap.dualMap_injective_of_surjective`. -/
theorem hingeRow_eq_dualMap (u v : α) (r : Module.Dual ℝ (ScrewSpace k)) :
    hingeRow (k := k) (α := α) u v r = (screwDiff (k := k) (α := α) u v).dualMap r :=
  rfl

/-- **The independence bridge: independent hinge-row functionals stay independent as rigidity rows**
(`def:rigidity-matrix`, the Case-I `hindep` brick). For a genuine edge `e = uv` with distinct
endpoints, if a family `r : ι → Module.Dual ℝ (ScrewSpace k)` of hinge-row-block functionals is
linearly independent, then so is the family of rigidity rows `i ↦ hingeRow u v (r i)` it induces on
the screw-assignment space `α → ScrewSpace k`. Because `screwDiff u v` is surjective at distinct
bodies (`screwDiff_surjective`), its dual map `(screwDiff u v).dualMap = hingeRow u v`
(`hingeRow_eq_dualMap`) is injective (`LinearMap.dualMap_injective_of_surjective`), and an injective
linear map preserves linear independence (`LinearIndependent.map'`).

This turns the independent supporting extensors of a rigid block
(`exists_independent_panelSupportExtensor`, through the `(D−1)`-dimensional hinge-row block
`finrank_hingeRowBlock`) into the independent rigidity-row subfamily the Case-I capstone
`hglue_of_realization` needs (`hindep`): one transversal hinge `e = uv` contributes `D − 1`
independent rows of `R(G,p)`, all routed through the *same* relative-screw evaluation, so block-row
independence is exactly hinge-row-block independence. -/
theorem linearIndependent_hingeRow {ι : Type*} {u v : α} (huv : u ≠ v)
    {r : ι → Module.Dual ℝ (ScrewSpace k)} (hr : LinearIndependent ℝ r) :
    LinearIndependent ℝ (fun i => hingeRow (k := k) (α := α) u v (r i)) := by
  have hinj : Function.Injective (screwDiff (k := k) (α := α) u v).dualMap :=
    LinearMap.dualMap_injective_of_surjective (screwDiff_surjective huv)
  simpa only [hingeRow_eq_dualMap] using hr.map' (screwDiff (k := k) (α := α) u v).dualMap
    (LinearMap.ker_eq_bot.2 hinj)

/-- The **rows of the panel-hinge rigidity matrix `R(G,p)`** (`def:rigidity-matrix`): the set of
all row functionals `hingeRow u v r` over every link `e = uv` of `G` and every row `r` of the
hinge-row block `r(p(e))` (`def:hinge-row-block`). This is the basis-free carrier of `R(G,p)` as
a *family of functionals* on the screw-assignment space `α → ScrewSpace k` — its span is the row
space of the matrix and its common kernel (the dual coannihilator of that span) is the null space
`Z(G,p) = infinitesimalMotions` (`infinitesimalMotions_eq_dualCoannihilator`). Carrying the matrix
this way (rather than as an explicit `(D−1)|E| × D|V|` real coordinate matrix) keeps the screw
space the graded-piece element and lets the rank arguments run through `Module.Dual`; it is the
view the Phase-21b genericity device parametrizes by the panel coordinates. -/
def rigidityRows (F : BodyHingeFramework k α β) : Set (Module.Dual ℝ (α → ScrewSpace k)) :=
  {φ | ∃ e u v, F.graph.IsLink e u v ∧ ∃ r ∈ F.hingeRowBlock e, φ = hingeRow u v r}

/-- **Infinitesimal motion** of a body-hinge framework `(G,p)` (`def:rigidity-matrix`): a
screw assignment `S : α → ScrewSpace k` is an infinitesimal motion when it satisfies the
hinge constraint (`def:hinge-constraint`) at *every* edge of `G`, i.e. for every edge `e`
linking endpoints `u v` (`G.IsLink e u v`), the relative screw center `S u - S v` lies in
`span C(p(e))`.

This is membership in the kernel of Katoh–Tanigawa's rigidity matrix `R(G,p)`
(`def:rigidity-matrix`): each oriented edge `e = uv` contributes the block row carrying the
hinge-row block `r(p(e))` in the `D` columns of `u` and `-r(p(e))` in those of `v` (zero
elsewhere), so a vanishing matrix-vector product is exactly the per-edge hinge constraint.
We keep the screw space the graded-piece element (`def:hinge-constraint`) and carry
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
    have := Submodule.smul_mem (ℝ ∙ F.supportExtensor e) c this
    rwa [smul_sub] at this

@[simp]
theorem mem_infinitesimalMotions (F : BodyHingeFramework k α β) (S : α → ScrewSpace k) :
    S ∈ F.infinitesimalMotions ↔ F.IsInfinitesimalMotion S :=
  Iff.rfl

/-- **The null space `Z(G,p)` is the common kernel of the rows of `R(G,p)`**
(`def:rigidity-matrix`): the infinitesimal-motion subspace equals the **dual coannihilator** of the
span of the rigidity rows,

  `F.infinitesimalMotions = (Submodule.span ℝ F.rigidityRows).dualCoannihilator`.

This is the coordinatized reading of `Z(G,p) = ker R(G,p)` against the basis-free row family
`rigidityRows` (`def:rigidity-matrix`): the dual coannihilator of a span is the common kernel of
the functionals (`Submodule.coe_dualCoannihilator_span`), so an infinitesimal motion is exactly a
screw assignment annihilated by every row functional `hingeRow e u v r` of every link `e = uv` and
every row `r` of the hinge-row block. The per-edge match is the row-block restatement of the hinge
constraint `hingeConstraint_iff_hingeRowBlock` (`r (S u − S v) = 0` for all `r ∈ r(p(e))`). This is
the load-bearing identity that lets the Phase-21b genericity device — which works on a `finrank`
upper bound for the `dualCoannihilator` of an affine family of functionals
(`LinearIndependent.finrank_dualCoannihilator_along_affine_path_cofinite`) — speak directly about
`dim Z(G,p)`. -/
theorem infinitesimalMotions_eq_dualCoannihilator (F : BodyHingeFramework k α β) :
    F.infinitesimalMotions = (Submodule.span ℝ F.rigidityRows).dualCoannihilator := by
  apply SetLike.coe_injective
  rw [Submodule.coe_dualCoannihilator_span]
  ext S
  simp only [SetLike.mem_coe, mem_infinitesimalMotions, Set.mem_setOf_eq]
  constructor
  · rintro hS φ ⟨e, u, v, he, r, hr, rfl⟩
    rw [hingeRow_apply]
    exact (hingeConstraint_iff_hingeRowBlock F S e u v).1 (hS e u v he) r hr
  · intro hS e u v he
    rw [hingeConstraint_iff_hingeRowBlock]
    intro r hr
    have := hS (hingeRow u v r) ⟨e, u, v, he, r, hr, rfl⟩
    rwa [hingeRow_apply] at this

/-- **A finite family of rows spans the rigidity row space** (`def:rigidity-matrix`,
the genericity device's finite-index input): when the body set `α` is finite, the screw-
assignment space `α → ScrewSpace k` is finite-dimensional (`finrank_screwAssignment`), hence so
is its dual `Module.Dual ℝ (α → ScrewSpace k)` (`Subspace.instModuleDualFiniteDimensional`), and
therefore every submodule of it is finitely generated — in particular `span ℝ F.rigidityRows`. So
there is a *finite* family `a : Fin n → Module.Dual ℝ (α → ScrewSpace k)` with the same span as
the (a priori infinite) row set `rigidityRows`,
`span ℝ (range a) = span ℝ F.rigidityRows` (`Submodule.fg_iff_exists_fin_generating_family`).

This supplies the finite-index spanning family `a` (with `hspanrows`) that the Phase-21b
genericity device's consumer-facing capstone `hglue_of_realization` requires of each consumer: the
device's engine needs a finite index type, and the constant-path route reads the corank off this
family at the single hand-built realization `F`. The remaining Case-I inputs (the matching-size
independent subfamily) come from `exists_independent_panelSupportExtensor` through the hinge-row
block. -/
theorem exists_finite_spanning_rigidityRows [Finite α] (F : BodyHingeFramework k α β) :
    ∃ (n : ℕ) (a : Fin n → Module.Dual ℝ (α → ScrewSpace k)),
      Submodule.span ℝ (Set.range a) = Submodule.span ℝ F.rigidityRows := by
  haveI : Fintype α := Fintype.ofFinite α
  have hfg : (Submodule.span ℝ F.rigidityRows).FG :=
    IsNoetherian.noetherian (Submodule.span ℝ F.rigidityRows)
  obtain ⟨n, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfg
  exact ⟨n, a, ha⟩

/-- **A transversal hinge's row block has dimension `D − 1`** (`def:hinge-row-block`,
the genericity device's row-count input): when the supporting extensor `C(p(e))` is nonzero —
the general-position condition that the hinge is a genuine codimension-2 intersection
(`panelSupportExtensor_ne_zero_iff`) — the hinge-row block `r(p(e)) = (span C(p(e)))^⊥` has
dimension `D − 1`, `finrank ℝ (F.hingeRowBlock e) = screwDim k − 1`. This is Katoh–Tanigawa's
`(D−1) × D` block-row count `1 ≤ i ≤ D−1` carried basis-free: the supporting extensor spans a
`1`-dimensional subspace of the `D`-dimensional screw space (`finrank_span_singleton`,
`screwSpace_finrank`), and the dual annihilator's dimension is the codimension
(`Subspace.finrank_add_finrank_dualAnnihilator_eq`). It is the per-edge brick that counts the
rigidity rows `rigidityRows` of a rigid block — the source of the matching-size independent
subfamily the Case-I capstone `hglue_of_realization` (Phase 21b) requires. -/
theorem finrank_hingeRowBlock (F : BodyHingeFramework k α β) {e : β}
    (he : F.supportExtensor e ≠ 0) :
    Module.finrank ℝ (F.hingeRowBlock e) = screwDim k - 1 := by
  have key := Subspace.finrank_add_finrank_dualAnnihilator_eq (K := ℝ)
    (Submodule.span ℝ {F.supportExtensor e})
  rw [screwSpace_finrank, finrank_span_singleton he, ← hingeRowBlock_apply] at key
  omega

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
its dimension is `D = screwDim k = (k+2 choose 2)`; carried basis-free as the constant
assignments. The screw-dimension count `D` is now available as the `finrank` equality
`screwSpace_finrank` (`def:rigidity-matrix`'s `⋀^k ℝ^(k+2) ≅ ℝ^D` coordinatization), so
`finrank (trivialMotions) = D` follows from the diagonal iso `trivialMotions_eq_range_const`.

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

/-- The constant-assignment map `s ↦ (fun _ => s)` is injective on a nonempty index type
(`lem:trivial-motions-rank-bound`): two constant assignments that agree everywhere agree at the
witnessing body, hence carry the same common screw center. This is what makes the diagonal map a
linear isomorphism `ScrewSpace k ≃ trivialMotions`, the basis-free form of "a trivial motion is
determined by its single common value". -/
theorem injective_const_pi [Nonempty α] :
    Function.Injective (LinearMap.pi (fun _ : α => LinearMap.id) :
      ScrewSpace k →ₗ[ℝ] α → ScrewSpace k) := by
  intro s t h
  have := congrFun h (Classical.arbitrary α)
  simpa using this

/-- **The trivial-motion space has dimension `D = (k+2 choose 2)`** for a nonempty body set
(`lem:trivial-motions-rank-bound`, `def:dof-generic`): `finrank ℝ (trivialMotions) = screwDim k`.
This is the numeric content of Katoh–Tanigawa's `D` standard trivial motions `S*_1, …, S*_D`. It
combines the diagonal identification `trivialMotions_eq_range_const` (the trivial motions are the
range of the injective constant-assignment map `s ↦ (fun _ => s)`, `injective_const_pi`) with the
screw-dimension count `screwSpace_finrank` (`finrank ℝ (ScrewSpace k) = D`, the
`⋀^k ℝ^(k+2) ≅ ℝ^D` coordinatization of `def:rigidity-matrix`): an injective linear map preserves
`finrank` (`LinearMap.finrank_range_of_inj`). -/
theorem finrank_trivialMotions [Nonempty α] (F : BodyHingeFramework k α β) :
    Module.finrank ℝ F.trivialMotions = screwDim k := by
  rw [trivialMotions_eq_range_const, LinearMap.finrank_range_of_inj injective_const_pi,
    screwSpace_finrank]

/-- **The screw-assignment space has dimension `D·|V|`** (`lem:trivial-motions-rank-bound`,
`def:dof-generic`): `finrank ℝ (α → ScrewSpace k) = D · |V|`, the column count `D|V|` of
Katoh–Tanigawa's rigidity matrix `R(G,p)`. From the product-space dimension `Module.finrank_pi`
and the screw-dimension count `screwSpace_finrank` (the `⋀^k ℝ^(k+2) ≅ ℝ^D` coordinatization of
`def:rigidity-matrix`). With `finrank_trivialMotions` this gives the numeric rank bound
`rank R(G,p) ≤ D|V| - D = D(|V|-1)` of `lem:trivial-motions-rank-bound` (the codimension of the
`D`-dimensional trivial kernel) and the degree of freedom of `def:dof-generic`. -/
theorem finrank_screwAssignment [Fintype α] :
    Module.finrank ℝ (α → ScrewSpace k) = screwDim k * Fintype.card α := by
  rw [Module.finrank_pi_const ℝ, screwSpace_finrank, mul_comm]

/-- **Two general-position parallel hinges intersect their constraint spans only at `0`**
(`lem:rank-parallel-full`, Katoh–Tanigawa Lemma 5.3, span form): if the supporting extensors
`C₁, C₂` of two hinges are linearly independent (the *general-position* hypothesis), then the
two one-dimensional constraint spans `span C₁` and `span C₂` meet only at the origin,
`span C₁ ⊓ span C₂ = ⊥`. This is the linear-algebra core of the lemma; the geometric
general-position hypothesis on the hinge points is `affineSubspaceExtensor`-independence,
supplied by the extensor-independence engine (`omitTwoExtensor_linearIndependent`,
Phase 17 Lemma 2.1) specialized to two hinges. -/
theorem span_inf_span_eq_bot_of_linearIndependent {c₁ c₂ : ScrewSpace k}
    (h : LinearIndependent ℝ ![c₁, c₂]) :
    Submodule.span ℝ {c₁} ⊓ Submodule.span ℝ {c₂} = ⊥ := by
  rw [← disjoint_iff, Submodule.disjoint_span_singleton' (by simpa using h.ne_zero 1)]
  rw [LinearIndependent.pair_iff' (by simpa using h.ne_zero 0)] at h
  rw [Submodule.mem_span_singleton]
  rintro ⟨a, ha⟩
  exact h a ha

/-- **Two general-position parallel hinges force the relative screw to zero**
(`lem:rank-parallel-full`, Katoh–Tanigawa Lemma 5.3): if two edges `e₁, e₂` of a body-hinge
framework `F` join the same pair of bodies `u, v` with hinges in general position — i.e. their
supporting extensors `C(p(e₁)), C(p(e₂))` are linearly independent — then any screw assignment
`S` satisfying the hinge constraint of *both* edges has equal screw centers on the two bodies,
`S u = S v`. Geometrically the two `(D-1) × D` hinge-row blocks together have full rank `D`
(`hingeRowBlock`), so the combined kernel on the relative screw `S u - S v` is `{0}`: this is
the base case `|V| = 2` of the conjecture's algebraic induction. The general-position
hypothesis on the hinge *points* is supplied by `omitTwoExtensor_linearIndependent`
(Phase 17 Lemma 2.1) specialized to the two hinges. -/
theorem eq_of_hingeConstraint_two_parallel (F : BodyHingeFramework k α β)
    (S : α → ScrewSpace k) {e₁ e₂ : β} {u v : α}
    (hgen : LinearIndependent ℝ ![F.supportExtensor e₁, F.supportExtensor e₂])
    (h₁ : F.hingeConstraint S e₁ u v) (h₂ : F.hingeConstraint S e₂ u v) :
    S u = S v := by
  have hmem : S u - S v ∈
      Submodule.span ℝ {F.supportExtensor e₁} ⊓ Submodule.span ℝ {F.supportExtensor e₂} :=
    ⟨h₁, h₂⟩
  rw [span_inf_span_eq_bot_of_linearIndependent hgen, Submodule.mem_bot, sub_eq_zero] at hmem
  exact hmem

/-- **An independent family of constraint spans admits no nonzero cycle of differences**
(`lem:cycle-realization`, the linear-algebra core of the `m`-body cycle): if `c : Fin m →
ScrewSpace k` is linearly independent and a family `d : Fin m → ScrewSpace k` has each
`d i ∈ span {c i}` with `∑ i, d i = 0`, then every `d i = 0`. This is the screw-space fact
behind Katoh–Tanigawa Lemma 5.4 for a cycle of length `m`: around a cycle the relative-screw
differences `d i = S(vᵢ) − S(vᵢ₊₁)` lie in the one-dimensional hinge spans `span C(p(eᵢ))`
and telescope to `∑ d i = 0`, so independence of the `m` supporting extensors forces every
difference to vanish — the `m`-edge generalization of
`span_inf_span_eq_bot_of_linearIndependent` (the `m = 2` antiparallel case). Each `d i` is a
scalar multiple `aᵢ • c i` (`Submodule.mem_span_singleton`), and `∑ aᵢ • c i = 0` with the
`c i` independent forces every `aᵢ = 0` (`Fintype.linearIndependent_iff`). -/
theorem eq_zero_of_mem_span_singleton_of_sum_eq_zero {m : ℕ}
    {c d : Fin m → ScrewSpace k} (hc : LinearIndependent ℝ c)
    (hd : ∀ i, d i ∈ Submodule.span ℝ {c i}) (hsum : ∑ i, d i = 0) (i : Fin m) :
    d i = 0 := by
  choose a ha using fun j => Submodule.mem_span_singleton.1 (hd j)
  have key : ∑ j, a j • c j = 0 := by rw [← hsum]; exact Finset.sum_congr rfl fun j _ => ha j
  rw [← ha i, Fintype.linearIndependent_iff.1 hc a key i, zero_smul]

/-- The **pinned-motion subspace** at a body `v` (`lem:rank-delete-vertex`): the infinitesimal
motions `S` that vanish on the pinned body, `S v = 0`. Pinning a body — fixing it to the zero
screw — is the algebraic effect of deleting the `D` columns of `v` from the rigidity matrix
`R(G,p)`; the surviving motions are exactly this subspace. Carried as the submodule of
`infinitesimalMotions` cut out by `S v = 0`. -/
def pinnedMotions (F : BodyHingeFramework k α β) (v : α) :
    Submodule ℝ (α → ScrewSpace k) where
  carrier := {S | F.IsInfinitesimalMotion S ∧ S v = 0}
  add_mem' {S T} hS hT :=
    ⟨F.infinitesimalMotions.add_mem hS.1 hT.1, by rw [Pi.add_apply, hS.2, hT.2, add_zero]⟩
  zero_mem' := ⟨F.infinitesimalMotions.zero_mem, rfl⟩
  smul_mem' c S hS :=
    ⟨F.infinitesimalMotions.smul_mem c hS.1, by rw [Pi.smul_apply, hS.2, smul_zero]⟩

@[simp]
theorem mem_pinnedMotions (F : BodyHingeFramework k α β) (v : α) (S : α → ScrewSpace k) :
    S ∈ F.pinnedMotions v ↔ F.IsInfinitesimalMotion S ∧ S v = 0 :=
  Iff.rfl

/-- Subtracting the constant screw `S v` from an infinitesimal motion `S` leaves an infinitesimal
motion (`lem:rank-delete-vertex`): the hinge constraint only sees the relative screws
`S u - S w`, which a constant shift `S u ↦ S u - S v` leaves unchanged. This is the
normalization underlying the pin-a-body fact of White--Whiteley~`whiteWhiteley1987`. -/
theorem isInfinitesimalMotion_sub_const (F : BodyHingeFramework k α β)
    {S : α → ScrewSpace k} (hS : F.IsInfinitesimalMotion S) (c : ScrewSpace k) :
    F.IsInfinitesimalMotion (fun u => S u - c) := by
  intro e u v he
  have := hS e u v he
  rw [hingeConstraint] at this ⊢
  simpa using this

/-- **The trivial and pinned motions intersect only at `0`** (`lem:rank-delete-vertex`): a
trivial motion (constant on every body) that also vanishes on the pinned body `v` is the zero
assignment, `trivialMotions ⊓ pinnedMotions v = ⊥`. The two `D`- and (`rank R`)-dimensional
summands are independent. -/
theorem trivialMotions_inf_pinnedMotions_eq_bot (F : BodyHingeFramework k α β) (v : α) :
    F.trivialMotions ⊓ F.pinnedMotions v = ⊥ := by
  rw [eq_bot_iff]
  rintro S ⟨hTriv, _, hv⟩
  rw [Submodule.mem_bot]
  exact funext fun u => (hTriv u v).trans hv

/-- **Every infinitesimal motion splits as trivial plus pinned** (`lem:rank-delete-vertex`):
`trivialMotions ⊔ pinnedMotions v = infinitesimalMotions`. Any motion `S` is the sum of the
trivial motion `fun _ => S v` (constant at the pinned body's screw) and the pinned motion
`fun u => S u - S v` (which vanishes at `v` and is still a motion by
`isInfinitesimalMotion_sub_const`). With
`trivialMotions_inf_pinnedMotions_eq_bot` this exhibits `Z(G,p)` as the internal direct sum of
the `D` trivial motions and the body-`v`-pinned motions. -/
theorem trivialMotions_sup_pinnedMotions (F : BodyHingeFramework k α β) (v : α) :
    F.trivialMotions ⊔ F.pinnedMotions v = F.infinitesimalMotions := by
  apply le_antisymm
  · rw [sup_le_iff]
    exact ⟨F.trivialMotions_le_infinitesimalMotions, fun S hS => hS.1⟩
  · intro S hS
    refine Submodule.mem_sup.2 ⟨fun _ => S v, fun u v' => rfl, fun u => S u - S v, ?_, ?_⟩
    · exact ⟨F.isInfinitesimalMotion_sub_const hS (S v), sub_self _⟩
    · exact funext fun u => by rw [Pi.add_apply, add_sub_cancel]

/-- **Pinning one body preserves rank** (`lem:rank-delete-vertex`, Katoh--Tanigawa Lemma 5.1):
deleting the `D` columns of a single body `v` from the rigidity matrix `R(G,p)` drops exactly the
`D` trivial-motion dimensions, leaving the rank unchanged. In the codimension form: the null
space `Z(G,p)` is the internal direct sum of the `D`-dimensional trivial motions and the
body-`v`-pinned motions, so

  `finrank (pinnedMotions v) + D = finrank Z(G,p)`,

equivalently `rank R(G,p) = rank R(G,p; V ∖ v)`. The `D` trivial motions
(`lem:trivial-motions-rank-bound`) normalize any motion to vanish on the pinned body
(`isInfinitesimalMotion_sub_const`), the pin-a-body motion-space fact of
White--Whiteley~`whiteWhiteley1987`. -/
theorem finrank_pinnedMotions_add_screwDim [Nonempty α] [Finite α]
    (F : BodyHingeFramework k α β) (v : α) :
    Module.finrank ℝ (F.pinnedMotions v) + screwDim k =
      Module.finrank ℝ F.infinitesimalMotions := by
  haveI : Fintype α := Fintype.ofFinite α
  have hdisj : F.trivialMotions ⊓ F.pinnedMotions v = ⊥ :=
    F.trivialMotions_inf_pinnedMotions_eq_bot v
  have hsup : F.trivialMotions ⊔ F.pinnedMotions v = F.infinitesimalMotions :=
    F.trivialMotions_sup_pinnedMotions v
  have key := Submodule.finrank_sup_add_finrank_inf_eq F.trivialMotions (F.pinnedMotions v)
  rw [hdisj, hsup, finrank_bot, add_zero, F.finrank_trivialMotions] at key
  omega

/-- **Refining the hinge spans shrinks the motion space** (`lem:rank-rotation-semicont`,
Katoh–Tanigawa Lemma 5.2, span/monotonicity form). If two body-hinge frameworks `F`, `F'`
share the same underlying multigraph and at every edge the constraint span of `F` is contained
in that of `F'` — i.e. `F'` is the *more general* (more constrained) realization, the generic
member of a rotation family — then every infinitesimal motion of `F'` is one of `F`:
`F'.infinitesimalMotions ≤ F.infinitesimalMotions`. The stronger (larger-span) constraints of
`F'` cut out a smaller null space.

This is the basis-free core of the lower-semicontinuity of `rank R(G,p)`: along a one-parameter
family rotating a panel, the generic realization has the *largest* supporting spans (the hinge
points in general position), hence the *smallest* motion space and the *largest* rank
(`finrank_infinitesimalMotions_le_of_span_le`). We carry it as this monotonicity-under-span-
refinement statement — matching the basis-free treatment of Lemmas 5.1/5.3 — rather than the
literal analytic one-parameter semicontinuity, which would force the parametrized
polynomial-entry coordinate matrix the design defers (the genericity-over-perturbation choice of
the risk register). -/
theorem infinitesimalMotions_mono_of_span_le (F F' : BodyHingeFramework k α β)
    (hgraph : F.graph = F'.graph)
    (hspan : ∀ e, Submodule.span ℝ {F'.supportExtensor e} ≤
      Submodule.span ℝ {F.supportExtensor e}) :
    F'.infinitesimalMotions ≤ F.infinitesimalMotions := by
  intro S hS e u v he
  rw [hingeConstraint]
  exact hspan e (hS e u v (hgraph ▸ he))

/-- **Rank is lower-semicontinuous under hinge-span refinement** (`lem:rank-rotation-semicont`,
Katoh–Tanigawa Lemma 5.2, rank form). If `F'` refines `F` — same graph, every constraint span
of `F` contained in that of `F'` — then the motion space of `F'` has no larger dimension than
that of `F`:

  `finrank Z(G, p') ≤ finrank Z(G, p)`,

equivalently `rank R(G, p) ≤ rank R(G, p')` (the rank is the codimension `D|V| − finrank Z` and
`finrank Z` only shrinks under refinement, `finrank_screwAssignment`). So the *generic* member of
a one-parameter rotation family — the one whose hinges are in general position, with the largest
supporting spans — attains the maximum rank, the content of Katoh–Tanigawa's Lemma 5.2: rank
cannot drop at a generic parameter. Immediate from the span-monotonicity
`infinitesimalMotions_mono_of_span_le` and `Submodule.finrank_mono`. -/
theorem finrank_infinitesimalMotions_le_of_span_le [Finite α]
    (F F' : BodyHingeFramework k α β) (hgraph : F.graph = F'.graph)
    (hspan : ∀ e, Submodule.span ℝ {F'.supportExtensor e} ≤
      Submodule.span ℝ {F.supportExtensor e}) :
    Module.finrank ℝ F'.infinitesimalMotions ≤ Module.finrank ℝ F.infinitesimalMotions :=
  Submodule.finrank_mono (F.infinitesimalMotions_mono_of_span_le F' hgraph hspan)

end BodyHingeFramework

end CombinatorialRigidity.Molecular
