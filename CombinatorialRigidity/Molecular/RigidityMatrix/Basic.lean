/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.Graph.Delete
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Rank
public import CombinatorialRigidity.Mathlib.Algebra.MvPolynomial.Funext
public import CombinatorialRigidity.Mathlib.LinearAlgebra.Dimension.Constructions
public import CombinatorialRigidity.Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import CombinatorialRigidity.Mathlib.LinearAlgebra.LinearIndependent.Basic
public import CombinatorialRigidity.Molecular.Extensor
public import CombinatorialRigidity.Molecular.Meet

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

This is the **core** of the `RigidityMatrix/` subdirectory (post-Phase-22l split round,
`notes/Phase22l-perf.md`): the dimension-agnostic rigidity-matrix API + the rank Lemmas 5.1–5.3,
plus the shared block-triangular-rank machinery (`columnOp`, the pinned-block independence lemmas).
The two leaves built on it are `RigidityMatrix/Bricks` (the vertex-disjoint / splice /
pinned-placement rank-addition bricks) and `RigidityMatrix/Claim612` (the `d=3` Claim-6.12 panel
geometry + candidate-row machinery). This file lands the `sec:molecular-rigidity-matrix`
dep-graph in dependency order. The leaf node landing here:

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

/-! ## The screw-center space `ScrewSpace` (the carrier `⋀^k ℝ^(k+2) ≅ ℝ^D`)

The screw dimension `D = (k+2 choose 2)`, the opaque-`def` carrier `ScrewSpace k` with its boundary
API (Phase 22l), and the `finrank (ScrewSpace k) = D` numeric gate (`screwSpace_finrank`) that every
rank count keys on. -/

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
explicit basis.

## Carrier API (Phase 22l, part 1 — pre-opacity)

The `mk` / `val` / `equivExteriorPower` API below is the stable boundary surface routing
every `ScrewSpace`-typed reach-in: it replaces the bare `⟨val, proof⟩` anonymous-constructor
and `Subtype.val` coercion idioms that the opaque head blocks. The carrier is now an **opaque
`def`** (Phase 22l flip, 2026-06-16) — a distinct, non-reducing head over the graded piece, so
the heavy `↥(⋀^k …)` type-expression no longer re-unfolds during defeq / `simp` / `rw` motives
over it (a diffuse `maxHeartbeats` cost behind the three former survivors — opacity cleared this
component; a follow-up `nlinarith`→`linarith` fix cleared the rest, so **0** overrides now remain;
`notes/Phase22l.md`, `notes/ScrewSpaceCarrier-design.md`). The defeq bridge to the graded piece is
`ScrewSpace_def`
(default-transparency `rfl`); the three module instances are `inferInstanceAs` over that bridge.
The carrier stays defeq to the graded piece at *default* transparency (so the spike's
coordinate transports are no-ops) but not at the *reducible/instance* transparency that drove
the cost — which is exactly the win. -/
def ScrewSpace (k : ℕ) : Type :=
  ↥(⋀[ℝ]^k (Fin (k + 2) → ℝ))

/-- **The defeq bridge** from the opaque `ScrewSpace` carrier to the underlying graded piece
`↥(⋀^k ℝ^(k+2))`. Holds by `rfl` at default transparency; used sparingly (the `mk` / `val` /
`equivExteriorPower` API routes the coercions through it so they survive the opacity flip). -/
theorem ScrewSpace_def (k : ℕ) :
    ScrewSpace k = ↥(⋀[ℝ]^k (Fin (k + 2) → ℝ)) := rfl

noncomputable instance (k : ℕ) : AddCommGroup (ScrewSpace k) :=
  inferInstanceAs (AddCommGroup ↥(⋀[ℝ]^k (Fin (k + 2) → ℝ)))

noncomputable instance (k : ℕ) : Module ℝ (ScrewSpace k) :=
  inferInstanceAs (Module ℝ ↥(⋀[ℝ]^k (Fin (k + 2) → ℝ)))

noncomputable instance (k : ℕ) : FiniteDimensional ℝ (ScrewSpace k) :=
  inferInstanceAs (FiniteDimensional ℝ ↥(⋀[ℝ]^k (Fin (k + 2) → ℝ)))

/-- **Constructor for the `ScrewSpace` carrier** from an exterior-algebra element with a
membership proof — the named replacement for the bare `⟨v, h⟩ : ScrewSpace k` anonymous
constructor, kept building once the carrier becomes an opaque `def` (Phase 22l). -/
def ScrewSpace.mk {k : ℕ} (v : ExteriorAlgebra ℝ (Fin (k + 2) → ℝ))
    (h : v ∈ ⋀[ℝ]^k (Fin (k + 2) → ℝ)) : ScrewSpace k :=
  (ScrewSpace_def k).symm ▸ (⟨v, h⟩ : ↥(⋀[ℝ]^k (Fin (k + 2) → ℝ)))

/-- **The underlying exterior-algebra element of a `ScrewSpace` carrier** — the named
replacement for the `Subtype.val` coercion `(C : ⋀[ℝ]^k …)`, kept building once the carrier
becomes an opaque `def` (Phase 22l). -/
def ScrewSpace.val {k : ℕ} (C : ScrewSpace k) : ExteriorAlgebra ℝ (Fin (k + 2) → ℝ) :=
  Subtype.val (ScrewSpace_def k ▸ C : ↥(⋀[ℝ]^k (Fin (k + 2) → ℝ)))

@[simp]
theorem ScrewSpace.val_mk {k : ℕ} (v : ExteriorAlgebra ℝ (Fin (k + 2) → ℝ))
    (h : v ∈ ⋀[ℝ]^k (Fin (k + 2) → ℝ)) : (ScrewSpace.mk v h).val = v := rfl

theorem ScrewSpace.val_mem {k : ℕ} (C : ScrewSpace k) :
    C.val ∈ ⋀[ℝ]^k (Fin (k + 2) → ℝ) :=
  (ScrewSpace_def k ▸ C : ↥(⋀[ℝ]^k (Fin (k + 2) → ℝ))).property

@[simp]
theorem ScrewSpace.val_smul {k : ℕ} (c : ℝ) (C : ScrewSpace k) :
    (c • C).val = c • C.val := rfl

@[simp]
theorem ScrewSpace.val_add {k : ℕ} (C D : ScrewSpace k) :
    (C + D).val = C.val + D.val := rfl

@[simp]
theorem ScrewSpace.val_zero {k : ℕ} : (0 : ScrewSpace k).val = 0 := rfl

@[simp]
theorem ScrewSpace.mk_val {k : ℕ} (C : ScrewSpace k) :
    ScrewSpace.mk C.val C.val_mem = C := rfl

theorem ScrewSpace.val_injective {k : ℕ} : Function.Injective (ScrewSpace.val (k := k)) :=
  fun _ _ h => Subtype.ext h

@[ext]
theorem ScrewSpace.ext {k : ℕ} {C D : ScrewSpace k} (h : C.val = D.val) : C = D :=
  ScrewSpace.val_injective h

/-- **The linear equivalence between the `ScrewSpace` carrier and the graded piece.** The
boundary `≃ₗ` for the basis / dual work; because the carrier is definitionally the graded
piece at default transparency (`ScrewSpace_def`, `notes/ScrewSpaceCarrier-design.md` §5 OQ3),
this is the `cast (ScrewSpace_def k)` transport — its `map_add'` / `map_smul'` are `rfl` and
the `_apply` / `_symm_apply` simp lemmas restate to the `cast`. (It cannot be `LinearEquiv.refl`
on the opaque head: the opaque carrier is not defeq to `↥(⋀^k …)` at the reducible transparency
`refl`'s apply lemmas need.) -/
noncomputable def ScrewSpace.equivExteriorPower (k : ℕ) :
    ScrewSpace k ≃ₗ[ℝ] ↥(⋀[ℝ]^k (Fin (k + 2) → ℝ)) where
  toFun C := cast (ScrewSpace_def k) C
  invFun C := cast (ScrewSpace_def k).symm C
  left_inv C := by simp [ScrewSpace_def]
  right_inv C := by simp [ScrewSpace_def]
  map_add' C D := rfl
  map_smul' c C := rfl

@[simp]
theorem ScrewSpace.equivExteriorPower_apply {k : ℕ} (C : ScrewSpace k) :
    ScrewSpace.equivExteriorPower k C = cast (ScrewSpace_def k) C := rfl

@[simp]
theorem ScrewSpace.equivExteriorPower_symm_apply {k : ℕ}
    (C : ↥(⋀[ℝ]^k (Fin (k + 2) → ℝ))) :
    (ScrewSpace.equivExteriorPower k).symm C = cast (ScrewSpace_def k).symm C := rfl

/-- **The screw-center space has dimension `D = (k+2 choose 2)`** (`def:rigidity-matrix`,
the deferred `⋀^k ℝ^(k+2) ≅ ℝ^D` coordinatization). Since `ScrewSpace k` is the degree-`k`
graded piece of the exterior algebra of `ℝ^(k+2)`, its dimension is `(k+2).choose k`
(`exteriorPower.finrank_eq`), which equals `(k+2).choose 2 = screwDim k` by the symmetry
`binom(n, j) = binom(n, n-j)`. This is the numeric content of the blueprint's
`⋀^k ℝ^(k+2) ≅ ℝ^D` identification — carried as a `finrank` equality rather than an explicit
basis — and is the gate for every numeric rank count (`lem:trivial-motions-rank-bound`'s
`rank R ≤ D(|V|-1)`, the degree of freedom of `def:dof-generic`). -/
theorem screwSpace_finrank (k : ℕ) : Module.finrank ℝ (ScrewSpace k) = screwDim k := by
  change Module.finrank ℝ ↥(⋀[ℝ]^k (Fin (k + 2) → ℝ)) = screwDim k
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

/-! ## `screwDim k` numeric arithmetic (general-`d` rank-count kit)

The three `Nat.choose` facts the symbolic-`k` realization spine needs in place of the
`d = 3` (`screwDim 2 = 6`) `decide` calls: the dimension is never zero
(`one_le_screwDim`), is at least `2` once the dimension floor `k ≥ 1` (i.e. `d = k+1 ≥ 2`)
holds (`two_le_screwDim`), and the `case_III_nested_rank_lower` eq.-(6.22) lower-bound
arithmetic `D − 2 ≤ D(|V'| − 1)` (`screwDim_sub_two_le_mul`). At `k = 0` the screw space is
the degenerate `⋀^0 = ℝ` with `screwDim 0 = (2).choose 2 = 1`, so the `≥ 2` facts genuinely
need the floor; the body-hinge regime always supplies `d = k + 1 ≥ 2`. -/

/-- **The screw dimension is positive** (`def:rigidity-matrix`): `D = screwDim k ≥ 1` for every
`k`. Immediate from `(k+2).choose 2 ≠ 0` (`Nat.choose_eq_zero_iff`: `2 ≤ k + 2`). The `k`-free
base fact the rank counts lean on; the floor-conditioned `2 ≤ screwDim k` is `two_le_screwDim`. -/
theorem one_le_screwDim {k : ℕ} : 1 ≤ screwDim k :=
  Nat.one_le_iff_ne_zero.mpr (by simp [screwDim, Nat.choose_eq_zero_iff])

/-- **The screw dimension is at least `2` in the body-hinge regime** (`def:rigidity-matrix`):
`D = screwDim k ≥ 2` once `k ≥ 1` (i.e. the ambient dimension `d = k + 1 ≥ 2`). The general-`d`
replacement for the `d = 3` `(2 : ℕ) ≤ screwDim 2` `decide`. Conditioned on the floor because
`screwDim 0 = (2).choose 2 = 1 < 2`; for `k ≥ 1` it follows from `screwDim 1 = (3).choose 2 = 3`
by monotonicity of `(· .choose 2)` (`Nat.choose_mono`). -/
theorem two_le_screwDim {k : ℕ} (hk : 1 ≤ k) : 2 ≤ screwDim k := by
  have h := Nat.choose_mono 2 (show 1 + 2 ≤ k + 2 by omega)
  simpa [screwDim] using le_trans (by decide) h

/-- **The screw dimension is at least `3` in the body-hinge regime** (`def:rigidity-matrix`):
`D = screwDim k ≥ 3` once `k ≥ 1` (i.e. the ambient dimension `d = k + 1 ≥ 2`). The general-`d`
floor the Case-II / Case-III spine producers need (their graph-side hypotheses
`3 ≤ bodyBarDim n` were `screwDim 2 = 6`-discharged at `d = 3`): with
`hn : bodyBarDim n = screwDim k`, `3 ≤ bodyBarDim n` follows from this. Same `Nat.choose_mono`
route as `two_le_screwDim` (it is
exactly `screwDim 1 = (3).choose 2 = 3 ≤ screwDim k`); conditioned on the floor because
`screwDim 0 = 1 < 3`. -/
theorem three_le_screwDim {k : ℕ} (hk : 1 ≤ k) : 3 ≤ screwDim k := by
  have h := Nat.choose_mono 2 (show 1 + 2 ≤ k + 2 by omega)
  simpa [screwDim] using h

/-- **The eq.-(6.22) lower-bound arithmetic** (`lem:case-III-nested-rank-lower`,
Katoh–Tanigawa 2011 §6.4.1 eq. (6.22)): `D − 2 ≤ D(m − 1)` whenever `m ≥ 2`. The general-`d`
replacement for the `d = 3` `screwDim 2 - 2 ≤ screwDim 2 * (|V'| − 1)` `decide`-led step in
`case_III_nested_rank_lower`, where `m = |V(G.splitOff …)|` is the (post-split, `≥ 2`) vertex
count. Pure `ℕ`-arithmetic: `D − 2 ≤ D = D · 1 ≤ D · (m − 1)` since `1 ≤ m − 1`. -/
theorem screwDim_sub_two_le_mul {k m : ℕ} (hm : 2 ≤ m) :
    screwDim k - 2 ≤ screwDim k * (m - 1) :=
  le_trans (Nat.sub_le _ _) (Nat.le_mul_of_pos_right _ (by omega))

/-! ## The panel-in-extensor predicate and the `BodyHingeFramework` carrier

`ExtensorInPanel` (a screw-space element lies in a hyperplane `n^⊥`) and the framework structure
`(graph, supportExtensor)` — the bridge from the screw space to the rigidity matrix `R(G,p)`. -/

/-- **A screw-space element `C` lies in a hyperplane `n^⊥`** (`def:genuine-hinge-realization`,
the per-link containment predicate of the honest bare motive M2; Phase 22i L0a). The `k`-extensor
`C ∈ ScrewSpace k` is *in the panel with normal `n`* when it is the extensor of `k` points of the
hyperplane `n^⊥ = {p | p ⬝ᵥ n = 0}`. The `k = 0` case (`extensor ![] = 1`) is degenerate and
satisfies the predicate vacuously; the relevant instances are `k = 2` (the `d = 3` producers,
where each link's `ScrewSpace 2` element is the meet of two hyperplanes, itself the extensor of
two common-perp points, `exists_extensor_eq_panelSupportExtensor` in `PanelLayer.lean`).
`C = 0` satisfies the predicate (degenerate `p`); nonzero-ness is M2's separate conjunct.
Scalars in the first slot absorb: `c • extensor p = extensor (update p 0 (c • p 0))`
(`AlternatingMap.map_update_smul`). -/
def ExtensorInPanel {k : ℕ} (C : ScrewSpace k) (n : Fin (k + 2) → ℝ) : Prop :=
  ∃ p : Fin k → Fin (k + 2) → ℝ,
    C.val = extensor p ∧ ∀ i, p i ⬝ᵥ n = 0

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

section RankArithmetic

/-! ### Rank-equation `ℤ`/`ℕ` cast plumbing

Two self-contained scalar bridges shared by the `k > 0`-split rank producer
(`PanelHingeFramework.case_II_realization_all_k`, CaseI.lean): both the lower-bound transfer
(`hrank_lb_nat`) and the rank-equality transfer (`hrankge_int`) re-run the *same* `Int.toNat` ↔
`ℕ`-subtraction bridge to move `D·(V−1) − k` between its `ℤ` form (from Brick A's `finrank` bound,
`D = screwDim 2`, `V = |V(G)|`) and its `ℕ`-`toNat` form (for the rank-polynomial transfer). Both
factor through the rank equation `N + (D−1) = D·(V−1) − k` (KT eq.~(6.12), `hNpD` in the producer:
`N` IH-old rows + `(D−1)` new rows = the target rank). Extracting them removes the dominant `CoeT`
typeclass-inference load the duplicated casts incurred (Phase 22j A1; `notes/PERFORMANCE.md`
*Producer helper-split design*). Pure scalar arithmetic — no rigidity content. -/

/-- **Side fact: `k.toNat ≤ D·(V−1)`** from the rank equation `N + (D−1) = D·(V−1) − k`
(Phase 22j A1; see the section preamble). With `N : ℕ` and `1 ≤ D` the right side `N + (D−1)`
is `ℤ`-nonnegative, so `k ≤ D·(V−1)`; the `ℕ`-`toNat` form follows. -/
theorem toNat_le_of_add_pred_eq {D V N : ℕ} {k : ℤ} (hV : 1 ≤ V) (hD : 1 ≤ D)
    (hNpD : (N : ℤ) + (D - 1) = D * ((V : ℤ) - 1) - k) :
    k.toNat ≤ D * (V - 1) := by
  have hk_le : (k.toNat : ℤ) ≤ ↑(D * (V - 1)) := by
    have hND : (0 : ℤ) ≤ (N : ℤ) + (D - 1) := by
      have : (1 : ℤ) ≤ D := by exact_mod_cast hD
      positivity
    rcases le_or_gt k 0 with hk0 | hk0
    · rw [Int.toNat_of_nonpos hk0]; positivity
    · rw [Int.toNat_of_nonneg (le_of_lt hk0)]
      push_cast [Nat.cast_sub hV]
      linarith [hNpD, hND]
  exact_mod_cast hk_le

/-- **`D·(V−1) − k.toNat = N + (D−1)`** from the rank equation `N + (D−1) = D·(V−1) − k`
(Phase 22j A1; see the section preamble). The `ℕ`-side identity feeding the rank-polynomial
transfer; `hk : 0 < k` pins `(k.toNat : ℤ) = k`, then both sides cast through
`toNat_le_of_add_pred_eq` and `hNpD`. -/
theorem sub_toNat_eq_of_add_pred_eq {D V N : ℕ} {k : ℤ} (hk : 0 < k) (hV : 1 ≤ V) (hD : 1 ≤ D)
    (hNpD : (N : ℤ) + (D - 1) = D * ((V : ℤ) - 1) - k) :
    D * (V - 1) - k.toNat = N + (D - 1) := by
  have hk_cast : (k.toNat : ℤ) = k := Int.toNat_of_nonneg (Int.le_of_lt hk)
  have hk_toNat_le : k.toNat ≤ D * (V - 1) := toNat_le_of_add_pred_eq hV hD hNpD
  have hZ : (↑(D * (V - 1) - k.toNat) : ℤ) = ↑(N + (D - 1)) := by
    rw [Nat.cast_sub hk_toNat_le]
    push_cast [Nat.cast_sub hV, Nat.cast_sub hD]
    rw [hk_cast]
    linarith [hNpD]
  exact_mod_cast hZ

end RankArithmetic

namespace BodyHingeFramework

variable {k : ℕ} {α β : Type*}

/-! ## The hinge constraint and the hinge-row block (`def:hinge-constraint`)

The affine-hinge constructor `ofHinge` and the per-edge constraint `S u − S v ∈ span C(p(e))`,
restated as the `(D−1)`-equation hinge-row block `(span C)^⊥`
(`hingeConstraint_iff_hingeRowBlock`). -/

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
    ScrewSpace.mk (affineSubspaceExtensor (hinge e))
      (affineSubspaceExtensor_mem_exteriorPower (hinge e))

@[simp]
theorem ofHinge_graph (G : Graph α β) (hinge : β → Fin k → Fin (k + 1) → ℝ) :
    (ofHinge G hinge).graph = G := rfl

theorem ofHinge_supportExtensor_val (G : Graph α β) (hinge : β → Fin k → Fin (k + 1) → ℝ)
    (e : β) :
    ((ofHinge G hinge).supportExtensor e).val = affineSubspaceExtensor (hinge e) := rfl

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
noncomputable def hingeRowBlock (F : BodyHingeFramework k α β) (e : β) :
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

/-! ## Rigidity rows: `screwDiff`, `hingeRow`, and the row family `rigidityRows`

The row functional `S ↦ r (S u − S v)` of `R(G,p)` and its algebra (swap, relabel, the
difference-collapse `hingeRow_sub_hingeRow_eq`, single-edge independence), plus the row-set carrier
`rigidityRows`. -/

/-- The **relative-screw evaluation** `screwDiff u v : (α → ScrewSpace k) →ₗ[ℝ] ScrewSpace k`
(`def:rigidity-matrix`): the linear map sending a screw assignment `S` to the relative screw
center `S u - S v` of the bodies `u, v`. It is the difference of the two coordinate projections
`proj u − proj v`; the per-edge hinge constraint (`def:hinge-constraint`) and the row functionals
of `R(G,p)` (`hingeRow`) are built from it. -/
noncomputable def screwDiff (u v : α) : (α → ScrewSpace k) →ₗ[ℝ] ScrewSpace k :=
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
noncomputable def hingeRow (u v : α) (r : Module.Dual ℝ (ScrewSpace k)) :
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

/-- **The row functional flips orientation by negating the block row** (`def:rigidity-matrix`):
`hingeRow u v r = hingeRow v u (-r)`. Reversing the oriented edge `e = uv → vu` negates the
relative screw center `S u - S v = -(S v - S u)`, which the linear `r` carries to a sign on the
row. This is the orientation-independence the unoriented graph `G` forces on `R(G,p)`'s block
rows: a rigidity row from a link `uv` is, in the reverse orientation `vu`, the same functional up
to the negated block row `-r ∈ r(p(e))` (the hinge-row block is a subspace, closed under negation).
The named form of the `hingeRow u v r = hingeRow v u (-r)` rewrite the rigidity-row span identities
(`span_panelRow_eq_rigidityRows`, `span_panelRow_linking_eq_rigidityRows`,
`span_rigidityRows_eq_sup_span_panelRow_edge`) repeatedly perform when a generating row's endpoints
match a link only up to swap (`IsLink.eq_and_eq_or_eq_and_eq`). -/
theorem hingeRow_swap (u v : α) (r : Module.Dual ℝ (ScrewSpace k)) :
    hingeRow (k := k) (α := α) u v r = hingeRow v u (-r) :=
  LinearMap.ext fun S => by rw [hingeRow_apply, hingeRow_apply, LinearMap.neg_apply, ← map_neg,
    neg_sub]

/-- **A body relabel transports a hinge row along its endpoint permutation**
(`lem:splitOff-rigidityRows-relabel`, the dual-of-`funLeft` half of KT eq.~(6.31); Katoh–Tanigawa
2011 §6.4.1, Phase 22h). Relabelling the screw assignments by a body map `ρ : α → α` is the linear
map `funLeft ρ : S ↦ S ∘ ρ`; its transpose `(funLeft ρ).dualMap` sends the hinge row
`hingeRow u v r` to the hinge row at the *relabelled* endpoints, `hingeRow (ρ u) (ρ v) r`:
`((funLeft ρ).dualMap (hingeRow u v r)) S = (hingeRow u v r)(S ∘ ρ) = r(S(ρ u) − S(ρ v))`. No
involution on `ρ` is needed — the identity holds for any body map — which makes it the clean export
of the `hdual` computation inlined in `rigidityRows_ofNormals_relabel`, the form the `M₃` arm's
candidate-row membership transport (the `ρ = (a v)` relabel) reads. -/
theorem hingeRow_funLeft_dualMap (u v : α) (r : Module.Dual ℝ (ScrewSpace k)) (ρ : α → α) :
    (LinearMap.funLeft ℝ (ScrewSpace k) ρ).dualMap (hingeRow (k := k) (α := α) u v r)
      = hingeRow (ρ u) (ρ v) r :=
  LinearMap.ext fun S => by
    rw [LinearMap.dualMap_apply, hingeRow_apply, hingeRow_apply, LinearMap.funLeft_apply,
      LinearMap.funLeft_apply]

/-- **The hinge-difference collapse: two rows sharing an endpoint subtract to a third hinge row**
(`def:rigidity-matrix`, the candidate-completion's eq.~(6.27) collapse algebra; Katoh–Tanigawa 2011
§6.4.1, Phase 22e). For a fixed hinge-row-block functional `r` and a common endpoint `w`,
`hingeRow u w r - hingeRow v w r = hingeRow u v r`: both rows read the relative screw against the
same `w`, so the shared `S w` cancels, `(S u - S w) - (S v - S w) = S u - S v`. This is the
algebraic heart of the candidate-completion transport (`panelRow_vb_sub_panelRow_ab_eq_hingeRow_va`,
eq.~(6.27)): the transported `(vb)`-row minus the inductive `(ab)`-row (sharing endpoint `b` and the
same supporting extensor) collapses to the pure `(va)`-hinge row `hingeRow v a ρ_g` — the candidate
row `w` whose column op makes it pure `v`-column. -/
theorem hingeRow_sub_hingeRow_eq (u v w : α) (r : Module.Dual ℝ (ScrewSpace k)) :
    hingeRow (k := k) (α := α) u w r - hingeRow v w r = hingeRow u v r :=
  LinearMap.ext fun S => by
    rw [LinearMap.sub_apply, hingeRow_apply, hingeRow_apply, hingeRow_apply, ← map_sub,
      sub_sub_sub_cancel_right]

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

/-! ## Infinitesimal motions and the null space `Z(G,p)`

The motion submodule as the common kernel of the rows (dual coannihilator), the span ↔ annihilator
duality (`span_rigidityRows_eq_dualAnnihilator_infinitesimalMotions`), finite spanning families, and
the per-edge `D−1` independent-row count (`finrank_hingeRowBlock`). -/

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

/-- **The rigidity-row span is the dual annihilator of the motion space** (`def:rigidity-matrix`,
the dual-side restatement of `infinitesimalMotions_eq_dualCoannihilator` over a finite body set).
When the body set `α` is finite, the screw-assignment dual is finite-dimensional, so the
finite-dimensional double-annihilator identity
(`Subspace.dualCoannihilator_dualAnnihilator_eq`) closes the loop
`span rigidityRows = (span rigidityRows).dualCoannihilator.dualAnnihilator =
Z.dualAnnihilator` (`Z = infinitesimalMotions`). This is the `Φ = Z.dualAnnihilator` step the
`injOn_extProj_dualMap_rigidityRows` family inlines, factored out so the motion-space transport
of the Case-I splice can read the rigidity-row span off the motions alone. -/
theorem span_rigidityRows_eq_dualAnnihilator_infinitesimalMotions [Finite α]
    (F : BodyHingeFramework k α β) :
    Submodule.span ℝ F.rigidityRows = F.infinitesimalMotions.dualAnnihilator := by
  haveI : Fintype α := Fintype.ofFinite α
  rw [F.infinitesimalMotions_eq_dualCoannihilator,
    Subspace.dualCoannihilator_dualAnnihilator_eq]

/-- **Equal motion spaces give equal rigidity-row spans** (`def:rigidity-matrix`, the rigidity-free
rank-invariance the Case-I splice's deficiency-aware relabel transport reads). Two body-hinge
frameworks with the *same* infinitesimal-motion space have the *same* rigidity-row span — at any
rank, with no rigidity hypothesis — because the span is the dual annihilator of the motions
(`span_rigidityRows_eq_dualAnnihilator_infinitesimalMotions`). This is what carries the rank of one
framework to another sharing its motion space (the selector-swap brick
`infinitesimalMotions_ofNormals_eq_of_ends_swap` supplies exactly such a motion-space equality). -/
theorem span_rigidityRows_eq_of_infinitesimalMotions_eq [Finite α]
    (F G : BodyHingeFramework k α β)
    (h : F.infinitesimalMotions = G.infinitesimalMotions) :
    Submodule.span ℝ F.rigidityRows = Submodule.span ℝ G.rigidityRows := by
  rw [F.span_rigidityRows_eq_dualAnnihilator_infinitesimalMotions,
    G.span_rigidityRows_eq_dualAnnihilator_infinitesimalMotions, h]

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

/-- **A single transversal hinge contributes `D − 1` independent rigidity rows**
(`def:rigidity-matrix`, the per-edge half of the Case-I `hindep`/`hmatch` assembly). For a genuine
edge `e = uv` with distinct endpoints (`u ≠ v`) whose supporting extensor is nonzero (the
transversal / general-position hinge, `panelSupportExtensor_ne_zero_iff`), there is a linearly
independent family of `D − 1 = screwDim k − 1` rigidity rows, all members of `F.rigidityRows`.
The family is `hingeRow u v` applied to a basis of the hinge-row block: the `(D−1)`-dimensional
hinge-row block `r(p(e))` (`finrank_hingeRowBlock`) has a basis of `D − 1` functionals, supplied
in ambient-coerced existence form by `Submodule.exists_linearIndependent_fin_of_finrank_eq` (so
the heavy `Module.Dual` of an exterior power is never unfolded). Each basis functional lies in
`r(p(e))`, so its `hingeRow u v` image is a rigidity row (witnessed by `e, u, v`), and the
basis-independent functionals stay independent as rigidity rows through the relative-screw
evaluation (`linearIndependent_hingeRow`). This is the per-edge brick that counts and produces the
matching-size independent rigidity-row subfamily the Case-I capstone `hglue_of_realization` needs:
each transversal hinge of a rigid block contributes exactly `D − 1` independent rows of `R(G,p)`,
all routed through the same `screwDiff u v`. -/
theorem exists_independent_rigidityRows_of_edge (F : BodyHingeFramework k α β) {e : β} {u v : α}
    (huv : u ≠ v) (hlink : F.graph.IsLink e u v) (he : F.supportExtensor e ≠ 0) :
    ∃ r : Fin (screwDim k - 1) → Module.Dual ℝ (α → ScrewSpace k),
      LinearIndependent ℝ r ∧ ∀ i, r i ∈ F.rigidityRows := by
  haveI : FiniteDimensional ℝ (ScrewSpace k) := inferInstance
  -- A basis of the `(D−1)`-dimensional hinge-row block, coerced out as ambient functionals.
  obtain ⟨c, hc, hmem⟩ := (F.hingeRowBlock e).exists_linearIndependent_fin_of_finrank_eq
    (F.finrank_hingeRowBlock he)
  -- Lift each block functional to a rigidity row through the relative-screw evaluation.
  refine ⟨fun i => hingeRow u v (c i), linearIndependent_hingeRow huv hc, fun i => ?_⟩
  exact ⟨e, u, v, hlink, c i, hmem i, rfl⟩

/-! ## Candidate-completion: column operation + pinned-block independence (KT eqs. (6.14)–(6.29))

The column operation `col_a += col_v` (`columnOp`) and the pin-a-body / off-`v` column-split
linear-independence engine (`linearIndependent_sum_pinned_block{,_augment}`,
`linearIndependent_sum_augment_candidateRow`) — the block-triangular `+1` for Cases II/III. -/

/-- **A rigidity row that vanishes off body `v`'s column factors through that column** (the pure
linear-algebra core of KT eq.~(6.28); Katoh–Tanigawa 2011 §6.4.1, Phase 22d). The candidate-%
completion row operation of eq.~(6.24)–(6.28) reduces the $(vb)i^*$-row of $R(G, p_1)$ to a row
whose $V \setminus \{v\}$ part is *all zero* — by definition, a functional `f` on the screw
assignments `α → ScrewSpace k` that vanishes on every assignment supported off `v` (`S v = 0 ⟹
f S = 0`). This lemma is the formal content of "such a row is determined by its `v`-column": writing
`S = Pi.single v (S v) + (S - Pi.single v (S v))`, the second summand is supported off `v` so `f`
kills it, leaving `f S = f (Pi.single v (S v)) = (f ∘ single v) (S v)`. Hence
`f = (f ∘ₗ single v) ∘ₗ proj v` factors through body `v`'s screw column.

This is exactly the structural input the candidate-completion's block-triangular rank lift needs:
the row-operation output of eq.~(6.28) becomes a *pure `v`-column* row `(Σⱼ λ_{(ab)j} rⱼ(q(ab)), 0)`
(eq.~(6.29)'s `(vb)i^*`-row), which then joins the $va$-block in the pin-a-body new block of
`linearIndependent_sum_pinned_block` — lifting `v`'s column contribution from `D − 1` to `D`, the
missing `+1` that takes the stratum-1 brick `D(|V|−1) − 1` to full `D(|V|−1)`. -/
theorem dualMap_eq_comp_single_proj_of_vanish_off [DecidableEq α]
    (f : Module.Dual ℝ (α → ScrewSpace k)) (v : α)
    (hvanish : ∀ S : α → ScrewSpace k, S v = 0 → f S = 0) :
    f = (f.comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v)).comp
      (LinearMap.proj v) := by
  refine LinearMap.ext fun S => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.coe_single]
  -- Split `S = (v-column part) + (off-`v` part)`; `f` kills the second by `hvanish`.
  have hz : f (S - Pi.single v (S v)) = 0 :=
    hvanish _ (by rw [Pi.sub_apply, Pi.single_eq_same, sub_self])
  rw [map_sub, sub_eq_zero] at hz
  exact hz

/-- **The candidate-completion column operation** `Φ = col_a += col_v` (Katoh–Tanigawa 2011
§6.4.1, eqs.~(6.14)–(6.15); Phase 22e). The change-of-variables automorphism on the screw
assignments `α → ScrewSpace k` that adds body `v`'s screw column to body `a`'s — modelled, since
the rigidity rows read relative screws `S u − S w`, as its *dual* substitution on the assignment:
`Φ S = Function.update S v (S v + S a)` (it is `col_a += col_v` acting on rows, equivalently
`row_v += row_a` on the column-vector `S`). It is a linear automorphism with inverse
`Φ⁻¹ S = Function.update S v (S v − S a)`; both directions need `v ≠ a` so that the update at `v`
leaves the `a`-coordinate fixed. A rank is invariant under this change of variables (precomposition
with a `≃ₗ`), so it certifies the candidate row's vanishing without changing any rank: it is the
device that makes the transported `(vb)i^*`-row `hingeRow v a ρ` (supported on *both* columns `v`
and `a`) into a pure `v`-column row in the operated frame — see `hingeRow_comp_columnOp_apply`. -/
@[simps! apply]
noncomputable def columnOp [DecidableEq α] {v a : α} (hva : v ≠ a) :
    (α → ScrewSpace k) ≃ₗ[ℝ] (α → ScrewSpace k) where
  toFun S := Function.update S v (S v + S a)
  invFun S := Function.update S v (S v - S a)
  map_add' S T := by
    refine funext fun x => ?_
    rcases eq_or_ne x v with rfl | hx
    · simp only [Function.update_self, Pi.add_apply]; abel
    · simp only [Function.update_of_ne hx, Pi.add_apply]
  map_smul' c S := by
    refine funext fun x => ?_
    rcases eq_or_ne x v with rfl | hx
    · simp only [Function.update_self, Pi.smul_apply, RingHom.id_apply, smul_add]
    · simp only [Function.update_of_ne hx, Pi.smul_apply, RingHom.id_apply]
  left_inv S := by
    refine funext fun x => ?_
    simp only
    rcases eq_or_ne x v with rfl | hx
    · rw [Function.update_self, Function.update_self, Function.update_of_ne hva.symm,
        add_sub_cancel_right]
    · rw [Function.update_of_ne hx, Function.update_of_ne hx]
  right_inv S := by
    refine funext fun x => ?_
    simp only
    rcases eq_or_ne x v with rfl | hx
    · rw [Function.update_self, Function.update_self, Function.update_of_ne hva.symm,
        sub_add_cancel]
    · rw [Function.update_of_ne hx, Function.update_of_ne hx]

/-- **The column operation is the identity on body `v`'s screw column** (the `comp Φ`-is-identity-
at-the-pin fact the candidate producers' `hrnpin`/`hspan` inputs need; Katoh–Tanigawa 2011
§6.4.1, Phase 22g). Applying `Φ = columnOp hvb` (`col_b += col_v`) to a screw assignment supported
only on body `v` (`single v x`) leaves it unchanged: at `v` it reads `(single v x) v + (single v x)
b = x + 0 = x` (using `v ≠ b`, so the distinct `b`-coordinate is `0`), and at every other body it
is `Function.update`-untouched. Hence precomposing the candidate producers' `(rn ·) ∘ₗ Φ ∘ₗ
single v` with the column op collapses to `(rn ·) ∘ₗ single v` — the form the L1/L2 leaves
(`linearIndependent_panelRow_comp_single_of_edge` / `span_panelRow_comp_single_of_edge`) supply
directly, so the candidate path feeds them with no extra `Φ`-rewrite. -/
theorem columnOp_apply_single [DecidableEq α] {v b : α} (hvb : v ≠ b) (x : ScrewSpace k) :
    columnOp (k := k) hvb (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v x)
      = LinearMap.single ℝ (fun _ : α => ScrewSpace k) v x := by
  funext y
  rcases eq_or_ne y v with rfl | hy
  · rw [columnOp_apply, Function.update_self, LinearMap.coe_single, Pi.single_eq_same,
      Pi.single_eq_of_ne hvb.symm, add_zero]
  · rw [columnOp_apply, Function.update_of_ne hy]

/-- **Operating then pinning to body `v` equals pinning directly** (the L1/L2 → candidate-producer
bridge; Katoh–Tanigawa 2011 §6.4.1, Phase 22g). For any row functional `g`, the candidate
producers' operated-and-pinned form `(g ∘ₗ Φ) ∘ₗ single v` (with `Φ = columnOp hvb`) equals the
bare pinned form `g ∘ₗ single v`, since `Φ` is the identity on body `v`'s screw column
(`columnOp_apply_single`). This lets the candidate producers' `hrnpin`/`hspan` inputs — stated on
the operated form `(rn ·) ∘ₗ Φ ∘ₗ single v` — be discharged directly from the L1/L2 leaves, which
supply the bare `(panelRow ·) ∘ₗ single v` form. -/
theorem comp_columnOp_comp_single [DecidableEq α] {v b : α} (hvb : v ≠ b)
    (g : Module.Dual ℝ (α → ScrewSpace k)) :
    (g.comp (columnOp (k := k) hvb).toLinearMap).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v)
      = g.comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v) :=
  LinearMap.ext fun x => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, columnOp_apply_single,
      LinearMap.comp_apply]

/-- **The candidate row becomes pure `v`-column in the operated frame** (KT eqs.~(6.14)–(6.16),
the eq.~(6.28) vanishing; Phase 22e). Precomposing the transported candidate row `hingeRow v a ρ`
of `R(G, p_1)` — supported on *both* body `v`'s and body `a`'s screw columns, with
`(hingeRow v a ρ) S = ρ(S v − S a)` — with the column operation `Φ = columnOp hva`
(`col_a += col_v`) reads `Φ S` at `v` as `S v + S a` and at `a` as `S a` (since `v ≠ a`), so
`(hingeRow v a ρ)(Φ S) = ρ((S v + S a) − S a) = ρ(S v)`: the `a`-column contribution cancels and
the row depends only on `v`'s column. This is KT's mechanism for the candidate-completion
vanishing — *not* the per-edge seam plus eq.~(6.43) — and is exactly the off-`v` vanishing
hypothesis `dualMap_eq_comp_single_proj_of_vanish_off` consumes (`S v = 0 ⟹ ρ(S v) = 0`). -/
theorem hingeRow_comp_columnOp_apply [DecidableEq α] {v a : α} (hva : v ≠ a)
    (ρ : Module.Dual ℝ (ScrewSpace k)) (S : α → ScrewSpace k) :
    hingeRow (k := k) (α := α) v a ρ (columnOp (k := k) hva S) = ρ (S v) := by
  rw [hingeRow_apply, columnOp_apply, columnOp_apply, Function.update_self,
    Function.update_of_ne hva.symm, add_sub_cancel_right]

/-- **The operated candidate row vanishes off `v`'s column** (KT eq.~(6.28); Phase 22e). Composing
the candidate row `hingeRow v a ρ` with the column operation `Φ = columnOp hva` gives a functional
on `α → ScrewSpace k` that kills every assignment supported off body `v`: by
`hingeRow_comp_columnOp_apply`, `(hingeRow v a ρ ∘ₗ Φ) S = ρ(S v)`, which is `ρ 0 = 0` whenever
`S v = 0`. Combined with `dualMap_eq_comp_single_proj_of_vanish_off`, this is the certificate that
in the column-operated frame the candidate row is a *pure `v`-column* row — the formal content of
KT eqs.~(6.27)–(6.28) and the missing structural input the candidate-completion needs. -/
theorem hingeRow_comp_columnOp_vanish_off [DecidableEq α] {v a : α} (hva : v ≠ a)
    (ρ : Module.Dual ℝ (ScrewSpace k)) (S : α → ScrewSpace k) (hS : S v = 0) :
    hingeRow (k := k) (α := α) v a ρ (columnOp (k := k) hva S) = 0 := by
  rw [hingeRow_comp_columnOp_apply hva ρ S, hS, map_zero]

/-- **The operated candidate row is a pure `v`-column row** (`lem:case-III-candidate-row`, the
eqs.~(6.27)–(6.28) packaging; Katoh–Tanigawa 2011 §6.4.1, Phase 22e). The combined certificate the
candidate-completion's `w`-assembly produces: precomposing the transported candidate row
`hingeRow v a ρ` of `R(G, p_1)` (supported on *both* columns `v` and `a`) with the column operation
`Φ = columnOp hva` (`col_a += col_v`) gives the operated row `w := (hingeRow v a ρ) ∘ₗ Φ`, and this
operated row factors through body `v`'s screw column:
`w = (w ∘ₗ single v) ∘ₗ proj v` — a *pure `v`-column* row. This is exactly the composition of the
two leaves the assembly threads: `hingeRow_comp_columnOp_vanish_off` (eqs.~(6.14)–(6.16): the
operated row kills every assignment supported off `v`) feeds the off-`v` vanishing hypothesis of
`dualMap_eq_comp_single_proj_of_vanish_off` (eq.~(6.28): a row vanishing off `v` is a pure
`v`-column row). The result is the eq.~(6.29) `(vb)i^*`-row that joins the `va`-block in
`linearIndependent_sum_pinned_block_augment`'s pin-a-body split — the missing `+1` taking the
stratum-1 brick `D(|V|−1) − 1` to full `D(|V|−1)`. -/
theorem comp_columnOp_eq_comp_single_proj [DecidableEq α] {v a : α} (hva : v ≠ a)
    (ρ : Module.Dual ℝ (ScrewSpace k)) :
    (hingeRow (k := k) (α := α) v a ρ).comp (columnOp (k := k) hva).toLinearMap
      = (((hingeRow (k := k) (α := α) v a ρ).comp (columnOp (k := k) hva).toLinearMap).comp
          (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v)).comp (LinearMap.proj v) :=
  dualMap_eq_comp_single_proj_of_vanish_off
    ((hingeRow (k := k) (α := α) v a ρ).comp (columnOp (k := k) hva).toLinearMap) v
    (fun S hS => by
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, hingeRow_comp_columnOp_vanish_off hva ρ S hS])

/-- **The star independence bridge: rows from distinct hinges at a common body are jointly
independent** (`def:rigidity-matrix`, the Case-I cross-hinge `hindep` step). Fix a body `v` and a
family of distinct other endpoints `w : J → α` (`hw` injective, `hwv` each `w j ≠ v`) — a *star*
of edges all incident to `v`, the shape a rigid block pinned at `v` presents. If for each `j : J`
the hinge-row functionals `r j : Iⱼ → Module.Dual ℝ (ScrewSpace k)` are linearly independent, then
the combined rigidity-row family `⟨j, i⟩ ↦ hingeRow (w j) v (r j i)` over the disjoint union
`Σ j, Iⱼ` is linearly independent on `α → ScrewSpace k`.

This is the cross-hinge step the per-edge brick `exists_independent_rigidityRows_of_edge` does not
cover: rows from *different* hinges go through *different* relative-screw evaluations
`screwDiff (w j) v`, so `linearIndependent_hingeRow`'s single-edge dual-map argument no longer
applies. The independence is instead the *pin-a-body* / disjoint-support count: evaluating a
vanishing combination at the screw assignment `Function.update 0 (w k) x` (place `x` on the body
`w k`, `0` elsewhere — legitimate since `w k ≠ v` and the `w j` are distinct) collapses it to
`∑ i, c⟨k,i⟩ • (r k i) x = 0` for all `x`, so per-hinge independence
(`Fintype.linearIndependent_iff` on `r k`) forces every coefficient at `k` to vanish. This is the
joint independence of the rigid block's hinge rows that `hglue_of_realization`'s `hindep` consumes
— each of the block's transversal hinges contributing its `D − 1` rows
(`exists_independent_rigidityRows_of_edge`), the rows of distinct hinges jointly independent because
they live on disjoint body-coordinate blocks once the common body is pinned. -/
theorem linearIndependent_hingeRow_star {J : Type*} [Finite J] {I : J → Type*}
    [∀ j, Finite (I j)] {v : α} {w : J → α} (hw : Function.Injective w) (hwv : ∀ j, w j ≠ v)
    {r : ∀ j, I j → Module.Dual ℝ (ScrewSpace k)} (hr : ∀ j, LinearIndependent ℝ (r j)) :
    LinearIndependent ℝ (fun p : Σ j, I j => hingeRow (k := k) (α := α) (w p.1) v (r p.1 p.2)) := by
  classical
  haveI : Fintype J := Fintype.ofFinite J
  haveI : ∀ j, Fintype (I j) := fun j => Fintype.ofFinite (I j)
  rw [Fintype.linearIndependent_iff]
  intro g hg k₀
  obtain ⟨j₀, i₀⟩ := k₀
  -- Evaluate the vanishing functional combination at `update 0 (w j₀) x`.
  have hval : ∀ x : ScrewSpace k, ∑ i, g ⟨j₀, i⟩ • (r j₀ i) x = 0 := by
    intro x
    have happ := LinearMap.congr_fun hg (Function.update (0 : α → ScrewSpace k) (w j₀) x)
    rw [LinearMap.sum_apply, LinearMap.zero_apply, Fintype.sum_sigma] at happ
    -- Every slice `j ≠ j₀` vanishes (its endpoint reads `0`); the `j₀` slice reads `x`.
    rw [Finset.sum_eq_single j₀] at happ
    · refine Eq.trans (Finset.sum_congr rfl (fun i _ => ?_)) happ
      rw [LinearMap.smul_apply, hingeRow_apply, Function.update_self,
        Function.update_of_ne (hwv j₀).symm, Pi.zero_apply, sub_zero]
    · intro j _ hjk
      refine Finset.sum_eq_zero (fun i _ => ?_)
      have hjw : w j ≠ w j₀ := fun h => hjk (hw h)
      rw [LinearMap.smul_apply, hingeRow_apply, Function.update_of_ne hjw,
        Function.update_of_ne (hwv j₀).symm]
      simp only [Pi.zero_apply, sub_zero, map_zero, smul_zero]
    · exact fun h => absurd (Finset.mem_univ j₀) h
  -- The collapsed sum is a vanishing combination of `r j₀`, independent by hypothesis.
  have hk : ∑ i, g ⟨j₀, i⟩ • r j₀ i = 0 :=
    LinearMap.ext fun x => by
      simpa [LinearMap.sum_apply, LinearMap.smul_apply] using hval x
  exact Fintype.linearIndependent_iff.1 (hr j₀) (fun i => g ⟨j₀, i⟩) hk i₀

/-- **N7b-3: the new-edge and old blocks are jointly independent (the pin-a-body column split)**
(`lem:case-II-placement-block-independent`; Katoh–Tanigawa 2011 §6.3). The pin-a-body column
decomposition (Lemma 5.1, `finrank_pinnedMotions_add_screwDim`) certifying the joint independence
of the two blocks the Case-II $1$-extension placement assembles: a *new* block `rn` of rigidity
rows carried by the re-inserted body `v`'s incident hinges, and an *old* block `ro` of rows of the
common subgraph `G − v`. The split is the body-`v` column: pinning the screw assignment to body `v`
alone (`Function.update 0 v x`) reads the old rows as `0` (their edges avoid `v`, `hold`) while
reading the new rows through `v`'s screw column (`rn i ∘ₗ LinearMap.single ℝ _ v`). So if the new
rows are independent *as functionals of `v`'s screw* (`hnewpin`, the $D-1$ column-block rows of
N7b-1) and the old rows are independent (`holdindep`, the $D(|V(G)|-2)$ inductive rows of N7b-2),
the union `Sum.elim rn ro` is independent: a vanishing combination, evaluated at `update 0 v x`,
collapses to the new block (old terms vanish by `hold`) and forces the new coefficients to vanish
by `hnewpin`; the residual is a vanishing combination of the old block, forcing the old
coefficients by `holdindep`. This is the panel-row form of the $1$-extension's exact `+D` rank lift
(`lem:case-II-rank-lift`); the assembly `lem:case-II-realization-placement` (N7b) feeds the union to
the device-closure glue `hasFullRankRealization_of_independent_panelRow`. -/
theorem linearIndependent_sum_pinned_block {ιn ιo : Type*} [Finite ιn] [Finite ιo]
    [DecidableEq α] {v : α}
    {rn : ιn → Module.Dual ℝ (α → ScrewSpace k)} {ro : ιo → Module.Dual ℝ (α → ScrewSpace k)}
    (hold : ∀ (j : ιo) (x : ScrewSpace k),
      ro j (Function.update (0 : α → ScrewSpace k) v x) = 0)
    (hnewpin : LinearIndependent ℝ
      (fun i : ιn => (rn i).comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v)))
    (holdindep : LinearIndependent ℝ ro) :
    LinearIndependent ℝ (Sum.elim rn ro) := by
  classical
  haveI : Fintype ιn := Fintype.ofFinite ιn
  haveI : Fintype ιo := Fintype.ofFinite ιo
  rw [Fintype.linearIndependent_iff]
  intro g hg
  -- Split the index sum over `ιn ⊕ ιo`.
  rw [Fintype.sum_sum_type] at hg
  simp only [Sum.elim_inl, Sum.elim_inr] at hg
  -- Step 1: evaluate at `update 0 v x` to kill the old block, isolating the new block.
  have hnew0 : ∑ i : ιn, g (.inl i) • (rn i).comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v)
      = 0 := by
    refine LinearMap.ext fun x => ?_
    have happ := LinearMap.congr_fun hg (Function.update (0 : α → ScrewSpace k) v x)
    rw [LinearMap.add_apply, LinearMap.zero_apply, LinearMap.sum_apply, LinearMap.sum_apply] at happ
    -- The old block reads `0` at `update 0 v x`.
    have holdsum : ∑ j : ιo, (g (.inr j) • ro j) (Function.update (0 : α → ScrewSpace k) v x)
        = 0 := Finset.sum_eq_zero fun j _ => by rw [LinearMap.smul_apply, hold j x, smul_zero]
    rw [holdsum, add_zero] at happ
    -- The new block collapses to the pinned functionals.
    rw [LinearMap.sum_apply, LinearMap.zero_apply]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) happ
    rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.coe_single,
      Pi.single]
  -- The new coefficients vanish by `hnewpin`.
  have hgn : ∀ i : ιn, g (.inl i) = 0 := Fintype.linearIndependent_iff.1 hnewpin _ hnew0
  -- Step 2: the residual is a vanishing combination of the old block.
  have hold0 : ∑ j : ιo, g (.inr j) • ro j = 0 := by
    rwa [Finset.sum_eq_zero (fun i _ => by rw [hgn i, zero_smul]), zero_add] at hg
  have hgo : ∀ j : ιo, g (.inr j) = 0 := Fintype.linearIndependent_iff.1 holdindep _ hold0
  rintro (i | j)
  · exact hgn i
  · exact hgo j

/-- **The restriction-bottom block-triangular augment (the sibling of
`linearIndependent_sum_pinned_block`, roles transposed)** (`lem:case-III-candidate-row`, the KT
eq.~(6.29) `t = 0` certification shape;
Katoh–Tanigawa 2011 §6.4.1, Phase 22h). The pin-a-body split `linearIndependent_sum_pinned_block`
proves `Sum.elim rn ro` independent from a *pinned* top block (`rn` independent on body `v`'s screw
column) and a *full*-strength bottom block (`ro` independent as ambient functionals, vanishing on
pure-`v` assignments). The `t = 0` hinge-level family of KT's eq.~(6.29) presents the transposed
shape: the **top** block `top` is the operated, pure-`v`-column candidate rows (vanishing on every
assignment supported off `v`, `htopvanish`), and the **bottom** block `bot` is the chosen split-off
rows carried as `F₀`-rows, independent only *after restriction to `V ∖ {v}`* (`hbotrestrict`, their
composites with the off-`v` projection `P_v S = Function.update S v 0`, expressed as
`id − single v ∘ proj v`). So the augment runs with the block-triangular argument the *other* way
round: evaluate a vanishing combination at the off-`v` assignment `Function.update S v 0` — the
pure-`v` top rows vanish there (`htopvanish`), leaving a vanishing combination of the restricted
bottom rows `bot ∘ P_v`, whose coefficients vanish by `hbotrestrict`; the residual is a vanishing
combination of `top` alone, and pinning to body `v`'s column (composing with `single v`) forces the
top coefficients by `htoppin`. This is the abstract count carrier of the M₁/M₂/M₃ arms' `t = 0`
certification (design §1.50(c)): the top is the candidate-completion's extra `D` rows, the bottom is
the `D(|V_v|−1)` split-off rows reproduced as `F₀`-rows, the union's independence the eq.~(6.29)
full `D(|V|−1)`. Graph-free and carrier-free pure linear algebra (the `ofNormals`/`withGraph` defeq
trap, TACTICS-QUIRKS §38, does not bite). -/
theorem linearIndependent_sum_restriction_block {ιt ιb : Type*} [Finite ιt] [Finite ιb]
    [DecidableEq α] {v : α}
    {top : ιt → Module.Dual ℝ (α → ScrewSpace k)} {bot : ιb → Module.Dual ℝ (α → ScrewSpace k)}
    (htopvanish : ∀ (i : ιt) (S : α → ScrewSpace k), S v = 0 → top i S = 0)
    (htoppin : LinearIndependent ℝ
      (fun i : ιt => (top i).comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v)))
    (hbotrestrict : LinearIndependent ℝ
      (fun j : ιb => (bot j).comp
        ((LinearMap.id : (α → ScrewSpace k) →ₗ[ℝ] (α → ScrewSpace k))
          - (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v).comp (LinearMap.proj v)))) :
    LinearIndependent ℝ (Sum.elim top bot) := by
  classical
  haveI : Fintype ιt := Fintype.ofFinite ιt
  haveI : Fintype ιb := Fintype.ofFinite ιb
  -- The off-`v` projection `P_v S = Function.update S v 0` (`id − single v ∘ proj v`).
  set P : (α → ScrewSpace k) →ₗ[ℝ] (α → ScrewSpace k) :=
    (LinearMap.id : (α → ScrewSpace k) →ₗ[ℝ] (α → ScrewSpace k))
      - (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v).comp (LinearMap.proj v) with hP
  -- `P S` zeroes the `v`-coordinate and fixes the rest.
  have hPv : ∀ (S : α → ScrewSpace k), (P S) v = 0 := fun S => by
    rw [hP, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      LinearMap.coe_single, Pi.sub_apply, Pi.single_eq_same, sub_self]
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fintype.sum_sum_type] at hg
  simp only [Sum.elim_inl, Sum.elim_inr] at hg
  -- Step 1: evaluate at `P S` (which has `(P S) v = 0`) to kill the top block, isolate the bottom.
  have hbot0 : ∑ j : ιb, g (.inr j) • (bot j).comp P = 0 := by
    refine LinearMap.ext fun S => ?_
    have happ := LinearMap.congr_fun hg (P S)
    rw [LinearMap.add_apply, LinearMap.zero_apply, LinearMap.sum_apply, LinearMap.sum_apply] at happ
    -- The top block vanishes at `P S` (its `v`-coordinate is `0`).
    have htopsum : ∑ i : ιt, (g (.inl i) • top i) (P S) = 0 :=
      Finset.sum_eq_zero fun i _ => by
        rw [LinearMap.smul_apply, htopvanish i (P S) (hPv S), smul_zero]
    rw [htopsum, zero_add] at happ
    -- The bottom block collapses to the restricted functionals at `S`.
    rw [LinearMap.sum_apply, LinearMap.zero_apply]
    refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) happ
    rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  -- The bottom coefficients vanish by `hbotrestrict`.
  have hgb : ∀ j : ιb, g (.inr j) = 0 := Fintype.linearIndependent_iff.1 hbotrestrict _ hbot0
  -- Step 2: the residual is a vanishing combination of the top block.
  have htop0 : ∑ i : ιt, g (.inl i) • top i = 0 := by
    have hbotzero : ∑ j : ιb, g (.inr j) • bot j = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [hgb j, zero_smul]
    rwa [hbotzero, add_zero] at hg
  -- Pin to body `v`'s column: the pinned residual vanishes, forcing the top coefficients.
  have htoppin0 : ∑ i : ιt, g (.inl i) •
      (top i).comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v) = 0 := by
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.sum_apply, LinearMap.zero_apply]
    have happ := LinearMap.congr_fun htop0 (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v x)
    rw [LinearMap.sum_apply, LinearMap.zero_apply] at happ
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) happ
    rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  have hgt : ∀ i : ιt, g (.inl i) = 0 :=
    Fintype.linearIndependent_iff.1 htoppin (fun i => g (.inl i)) htoppin0
  rintro (i | j)
  · exact hgt i
  · exact hgb j

/-- **The conditional `D`-row new block: the operated candidate row lifts the `va`-block from
`D − 1` to `D`** (`lem:case-III-candidate-row`, KT eq.~(6.29); Katoh–Tanigawa 2011 §6.4.1, the
candidate-completion's block-triangular `+1`, Phase 22e). The eq.~(6.29) assembly that takes the
stratum-1 brick `D(|V|−1) − 1` (`case_II_placement_eq612`) to full `D(|V|−1)` *conditional* on the
top-left `D × D` block being full rank. The new block is the `D − 1` rows `rn` of body `v`'s
`va`-hinge **plus** the candidate-completion's operated extra row `w` — the pure-`v`-column row
`hingeRow v a ρ_g ∘ₗ Φ` produced by the column op (`hingeRow_comp_columnOp_vanish_off` +
`dualMap_eq_comp_single_proj_of_vanish_off`, eq.~(6.28)); the old block is the `D(|V_v|−1)` rows
`ro` of the split-off `G_v^{ab} ∖ (ab)i^*` (vanishing at `update 0 v`, `hold`). The two blocks are
jointly independent — `Sum.elim (Sum.elim rn (fun _ : Unit => w)) ro` — provided the **augmented**
pinned new block `Sum.elim (rn ·∘ₗ single v) (w ∘ₗ single v)` of `D` functionals is independent on
body `v`'s `D`-dimensional screw column (`hnewpinaug`, KT's eq.~(6.29) top-left `D × D` full rank:
the `(va)`-block's `D − 1` pinned rows plus the operated `(vb)i^*`-row `w`'s `v`-column block, all
linearly independent). This is exactly `linearIndependent_sum_pinned_block` applied to the
augmented new block: `w` is a new-block row pinned through `v`'s column (the pure-`v`-column
property the caller establishes for the operated row, carried into `hnewpinaug`), so it joins `rn`
in the `hnewpin` slot rather than needing the old-block `hold` vanishing. The `+1` over the
stratum-1 brick is the extra `Unit` row; the count becomes
`((D − 1) + 1) + D(|V_v|−1) = D(|V|−1)`. -/
theorem linearIndependent_sum_pinned_block_augment {ιn ιo : Type*} [Finite ιn] [Finite ιo]
    [DecidableEq α] {v : α}
    {rn : ιn → Module.Dual ℝ (α → ScrewSpace k)} {ro : ιo → Module.Dual ℝ (α → ScrewSpace k)}
    {w : Module.Dual ℝ (α → ScrewSpace k)}
    (hold : ∀ (j : ιo) (x : ScrewSpace k),
      ro j (Function.update (0 : α → ScrewSpace k) v x) = 0)
    (hnewpinaug : LinearIndependent ℝ (Sum.elim
      (fun i : ιn => (rn i).comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v))
      (fun _ : Unit => w.comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v))))
    (holdindep : LinearIndependent ℝ ro) :
    LinearIndependent ℝ (Sum.elim (Sum.elim rn (fun _ : Unit => w)) ro) := by
  -- The pure-`v`-column row `w` joins the `va`-block as one more new-block row, pinned through
  -- `v`'s column exactly like `rn`; feed the augmented new block to the pin-a-body split.
  refine BodyHingeFramework.linearIndependent_sum_pinned_block (v := v) hold ?_ holdindep
  -- The augmented new block, composed with `single v`, *is* `hnewpinaug` — the two functions agree
  -- (`Sum.elim` distributes over the per-index `.comp (single v)`).
  have hfun : (fun i : ιn ⊕ Unit =>
      ((Sum.elim rn (fun _ : Unit => w)) i).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v))
      = Sum.elim
        (fun i : ιn => (rn i).comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v))
        (fun _ : Unit => w.comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v)) := by
    funext i; cases i <;> rfl
  rw [hfun]; exact hnewpinaug

/-- **Swapping the candidate row by an old/new-block combination preserves independence**
(`lem:case-III-candidate-row`, the abstract row-operation core of KT eq.~(6.27); Katoh–Tanigawa 2011
§6.4.1, Phase 22g). The candidate-completion family is
`Sum.elim (Sum.elim rn (fun _ : Unit => w)) ro`
— the new block `rn`, the old block `ro`, and the single candidate row `w`. The genericity-device
feed (`hasFullRankRealization_of_independent_panelRow_index`) needs every member of the independent
family to be a genuine `panelRow` of the candidate placement, but the per-candidate producers
(`linearIndependent_sum_{p2,p3,augment}_candidateRow`) deliver the candidate row in a `hingeRow`
form `w` that is *not* itself a panel row. KT's eq.~(6.27) closes this by a **row operation**: the
transported `(vb)i^*`-row `hingeRow v b ρ` (a genuine rigidity row, `exists_candidate_row_eq612`)
minus its inductive `(ab)`-part `wGv = hingeRow a b ρ` — an element of the *old* block's span —
collapses to the pure `(va)`-hinge candidate row `hingeRow v a ρ`. Adding a combination of the other
rows to one row of a matrix never changes its rank, and this lemma is that fact for the candidate
summand: if the family with candidate row `w` is linearly independent and `w'` differs from `w` by
an element of the span of the *remaining* rows `Sum.elim rn ro` (`hdiff`), then the family with the
swapped candidate row `w'` is again linearly independent.

The proof reassociates the `(ιn ⊕ Unit) ⊕ ιo` index to `(ιn ⊕ ιo) ⊕ Unit` (the candidate summand
last), so the row-space criterion `linearIndependent_sumElim_unit_iff` reads the independence as
`w ∉ span (range (Sum.elim rn ro))`; since `w' − w` lies in that span, `w'` is fresh iff `w` is.
Graph-free and carrier-free (pure linear algebra on the dual space), so the recurring
`ofNormals`/`withGraph` defeq trap (TACTICS-QUIRKS §38) does not bite. -/
theorem linearIndependent_sumElim_candidateRow_swap {ιn ιo : Type*}
    {rn : ιn → Module.Dual ℝ (α → ScrewSpace k)} {ro : ιo → Module.Dual ℝ (α → ScrewSpace k)}
    {w w' : Module.Dual ℝ (α → ScrewSpace k)}
    (hindep : LinearIndependent ℝ (Sum.elim (Sum.elim rn (fun _ : Unit => w)) ro))
    (hdiff : w' - w ∈ Submodule.span ℝ (Set.range (Sum.elim rn ro))) :
    LinearIndependent ℝ (Sum.elim (Sum.elim rn (fun _ : Unit => w')) ro) := by
  -- Reassociate the `(ιn ⊕ Unit) ⊕ ιo` index to `(ιn ⊕ ιo) ⊕ Unit`, putting the candidate
  -- summand last so the row-space criterion `linearIndependent_sumElim_unit_iff` applies.
  set e : (ιn ⊕ Unit) ⊕ ιo ≃ (ιn ⊕ ιo) ⊕ Unit :=
    ((Equiv.sumAssoc ιn Unit ιo).trans
      ((Equiv.refl ιn).sumCongr (Equiv.sumComm Unit ιo))).trans
      (Equiv.sumAssoc ιn ιo Unit).symm with he
  -- The reassociated family with candidate row `x` is `Sum.elim (Sum.elim rn ro) (Unit → x) ∘ e`.
  have hreassoc : ∀ x : Module.Dual ℝ (α → ScrewSpace k),
      Sum.elim (Sum.elim rn (fun _ : Unit => x)) ro
        = Sum.elim (Sum.elim rn ro) (fun _ : Unit => x) ∘ e := by
    intro x; funext i; rcases i with (i | u) | j <;> rfl
  -- Move `hindep` to the reassociated `Sum.elim base (Unit → w)` form.
  rw [hreassoc w, linearIndependent_equiv] at hindep
  -- The base block `Sum.elim rn ro` is independent (a sub-family of the augmented one).
  have hbase : LinearIndependent ℝ (Sum.elim rn ro) := by
    have := hindep.comp Sum.inl Sum.inl_injective
    simpa using this
  -- The row-space criterion: `w ∉ span (range base)`; `hdiff` transfers it to `w'`.
  have hw : w ∉ Submodule.span ℝ (Set.range (Sum.elim rn ro)) :=
    (linearIndependent_sumElim_unit_iff hbase w).1 hindep
  have hw' : w' ∉ Submodule.span ℝ (Set.range (Sum.elim rn ro)) := fun h =>
    hw (by simpa using sub_mem h hdiff)
  rw [hreassoc w', linearIndependent_equiv]
  exact (linearIndependent_sumElim_unit_iff hbase w').2 hw'

/-- **Swapping an entire `d`-fold candidate block by old/new-block combinations preserves
independence** (`lem:case-III-candidate-row`, the general-`d` chain row-correspondence of KT
eq.~(6.62); Katoh–Tanigawa 2011 §6.4.2, the CHAIN-1 generalization of the single-`Unit`
`linearIndependent_sumElim_candidateRow_swap` to the length-`d` chain). The candidate-completion
family is `Sum.elim (Sum.elim rn cand) ro` — the new block `rn`, the **block** of `d` candidate
rows `cand : ιc → Dual`, and the old block `ro`. KT's general-`d` Case III corrects *each* of the
`d` chain candidate rows by its own inductive `(ab)`-part (an element of the old/new blocks' span,
eq.~(6.62)): if the family with candidate block `cand` is linearly independent and `cand' i` differs
from `cand i` by an element of `span (range (Sum.elim rn ro))` for every chain index `i` (`hdiff`),
then the family with the swapped block `cand'` is again linearly independent.

The `Fin d`-indexed generalization of `linearIndependent_sumElim_candidateRow_swap` (the `Unit`
single-candidate version): the proof reassociates the `(ιn ⊕ ιc) ⊕ ιo` index to `(ιn ⊕ ιo) ⊕ ιc`
(the candidate block last) and applies the block row operation
`linearIndependent_sumElim_block_swap` with base `Sum.elim rn ro`, where each candidate's
correction `cand' i - cand i` lies in `span (range (Sum.elim rn ro))`. Graph-free and carrier-free
(pure linear algebra on the dual space), so the recurring `ofNormals`/`withGraph` defeq trap
(TACTICS-QUIRKS §38) does not bite. -/
theorem linearIndependent_sumElim_candidateBlock_swap {ιn ιo ιc : Type*}
    {rn : ιn → Module.Dual ℝ (α → ScrewSpace k)} {ro : ιo → Module.Dual ℝ (α → ScrewSpace k)}
    {cand cand' : ιc → Module.Dual ℝ (α → ScrewSpace k)}
    (hindep : LinearIndependent ℝ (Sum.elim (Sum.elim rn cand) ro))
    (hdiff : ∀ i, cand' i - cand i ∈ Submodule.span ℝ (Set.range (Sum.elim rn ro))) :
    LinearIndependent ℝ (Sum.elim (Sum.elim rn cand') ro) := by
  -- Reassociate `(ιn ⊕ ιc) ⊕ ιo` to `(ιn ⊕ ιo) ⊕ ιc`, putting the candidate block last so the
  -- block row operation `linearIndependent_sumElim_block_swap` (base first) applies.
  set e : (ιn ⊕ ιc) ⊕ ιo ≃ (ιn ⊕ ιo) ⊕ ιc :=
    ((Equiv.sumAssoc ιn ιc ιo).trans
      ((Equiv.refl ιn).sumCongr (Equiv.sumComm ιc ιo))).trans
      (Equiv.sumAssoc ιn ιo ιc).symm with he
  have hreassoc : ∀ c : ιc → Module.Dual ℝ (α → ScrewSpace k),
      Sum.elim (Sum.elim rn c) ro = Sum.elim (Sum.elim rn ro) c ∘ e := by
    intro c; funext i; rcases i with (i | u) | j <;> rfl
  rw [hreassoc cand', linearIndependent_equiv]
  rw [hreassoc cand, linearIndependent_equiv] at hindep
  exact linearIndependent_sumElim_block_swap hindep hdiff

/-- **The candidate-completion full block assembly: the operated augment transports back to the
original `D(|V|−1)`-size family** (`lem:case-III-candidate-row`, KT eqs.~(6.14)–(6.16), (6.29);
Katoh–Tanigawa 2011 §6.4.1, the candidate-completion's column-operated block-triangular `+1`,
Phase 22e). The producer that takes the stratum-1 brick's two blocks (`rn` the new `va`-block, `ro`
the old split-off block) plus the candidate row `w = hingeRow v a ρ` (supported on *both* columns
`v` and `a`) and assembles them into one linearly independent family
`Sum.elim (Sum.elim rn (fun _ : Unit => w)) ro` — the original (un-operated) rows of `R(G, p_1)`,
the missing `+1` lifting the brick's `D(|V|−1) − 1` to full `D(|V|−1)`.

The argument is KT's column operation `Φ = columnOp hva` (`col_a += col_v`, eqs.~(6.14)–(6.15)).
Precomposing the whole family with `Φ` (a linear automorphism, hence preserving independence via the
dual equivalence `Φ.dualMap`) turns it into the *operated* family
`Sum.elim (Sum.elim (rn ·∘ₗ Φ) (w ∘ₗ Φ)) (ro ·∘ₗ Φ)`, in which the candidate row `w ∘ₗ Φ` is a
**pure `v`-column** row (`hingeRow_comp_columnOp_vanish_off`, eq.~(6.28)): it joins the new block in
the pin-a-body augment (`linearIndependent_sum_pinned_block_augment`) rather than needing the
old-block vanishing. The old rows are unchanged by `Φ` *at the pin assignment* `update 0 v x` —
since `Φ` only modifies column `v` and `Φ (update 0 v x) = update 0 v x` (using `v ≠ a`, so column
`a` reads `0`), `(ro_j ∘ₗ Φ)(update 0 v x) = ro_j (update 0 v x) = 0` (`holdop` from `hold`); the
new rows' `v`-column pins are unchanged. So the operated family meets the augment's hypotheses,
with the eq.~(6.29) top-left `D × D` full rank `hnewpinaug` (the `va`-block's `D − 1` pinned rows
plus the operated `w`'s `v`-column) the **conditional** = Claim~6.12 territory, passed through. The
operated family's independence transports back through `Φ.dualMap` (injective) to give the original
family's independence. -/
theorem linearIndependent_sum_augment_candidateRow
    [DecidableEq α] {v a : α} (hva : v ≠ a) {ιn ιo : Type*} [Finite ιn] [Finite ιo]
    {rn : ιn → Module.Dual ℝ (α → ScrewSpace k)} {ro : ιo → Module.Dual ℝ (α → ScrewSpace k)}
    {ρ : Module.Dual ℝ (ScrewSpace k)}
    (hold : ∀ (j : ιo) (x : ScrewSpace k),
      ro j (Function.update (0 : α → ScrewSpace k) v x) = 0)
    (hnewpinaug : LinearIndependent ℝ (Sum.elim
      (fun i : ιn =>
        ((rn i).comp (columnOp (k := k) hva).toLinearMap).comp
          (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v))
      (fun _ : Unit =>
        ((hingeRow (k := k) (α := α) v a ρ).comp (columnOp (k := k) hva).toLinearMap).comp
          (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v))))
    (holdindep : LinearIndependent ℝ ro) :
    LinearIndependent ℝ
      (Sum.elim (Sum.elim rn (fun _ : Unit => hingeRow (k := k) (α := α) v a ρ)) ro) := by
  set Φ := columnOp (k := k) hva with hΦ
  have hker : LinearMap.ker Φ.dualMap.toLinearMap = ⊥ :=
    LinearMap.ker_eq_bot_of_injective Φ.dualMap.injective
  -- The operated old rows vanish at the pin assignment: `Φ (update 0 v x) = update 0 v x` (it only
  -- changes column `v`, to `x + 0 = x`, using `v ≠ a`), so `(ro_j ∘ Φ)(update 0 v x) = 0`.
  have hΦpin : ∀ x : ScrewSpace k, Φ (Function.update (0 : α → ScrewSpace k) v x)
      = Function.update (0 : α → ScrewSpace k) v x := by
    intro x
    funext y
    rcases eq_or_ne y v with rfl | hy
    · rw [hΦ, columnOp_apply, Function.update_self, Function.update_self,
        Function.update_of_ne hva.symm, Pi.zero_apply, add_zero]
    · rw [hΦ, columnOp_apply, Function.update_of_ne hy, Function.update_of_ne hy]
  have holdop : ∀ (j : ιo) (x : ScrewSpace k),
      ((ro j).comp Φ.toLinearMap) (Function.update (0 : α → ScrewSpace k) v x) = 0 := by
    intro j x
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, hΦpin x, hold j x]
  -- Assemble the *operated* augment: `w ∘ Φ` is the pure-`v`-column row, joining the new block.
  have hop : LinearIndependent ℝ (Sum.elim
      (Sum.elim (fun i : ιn => (rn i).comp Φ.toLinearMap)
        (fun _ : Unit => (hingeRow (k := k) (α := α) v a ρ).comp Φ.toLinearMap))
      (fun j : ιo => (ro j).comp Φ.toLinearMap)) :=
    linearIndependent_sum_pinned_block_augment (v := v) holdop hnewpinaug
      (holdindep.map' Φ.dualMap.toLinearMap hker)
  -- The operated family is `Φ.dualMap ∘ (original family)`; transport independence back through the
  -- injective dual equivalence `Φ.dualMap` (`g ↦ g ∘ₗ Φ`).
  have hcomp : (Sum.elim (Sum.elim (fun i : ιn => (rn i).comp Φ.toLinearMap)
        (fun _ : Unit => (hingeRow (k := k) (α := α) v a ρ).comp Φ.toLinearMap))
      (fun j : ιo => (ro j).comp Φ.toLinearMap))
      = Φ.dualMap ∘
        (Sum.elim (Sum.elim rn (fun _ : Unit => hingeRow (k := k) (α := α) v a ρ)) ro) := by
    funext i; rcases i with (i | i) | j <;> rfl
  rw [hcomp] at hop
  exact (Φ.dualMap.toLinearMap.linearIndependent_iff hker).1 hop

/-- **The restriction-bottom candidate-completion augment: the operated top block joins a
restriction-independent bottom block** (`lem:case-III-candidate-row`, the abstract core of the
M₁/M₂/M₃ arms' `t = 0` certification at the hinge-level family `F₀`; Katoh–Tanigawa 2011 §6.4.1,
eq.~(6.29), Phase 22h §1.50(c)). The restriction-bottom sibling of
`linearIndependent_sum_augment_candidateRow`: where that producer assembles the candidate
completion against a *pure-`v`-vanishing* old block (`hold`, the `case_III_*_of_line` shape), this
one assembles it against a bottom block independent only *after restriction to `V ∖ {v}`* — KT's
eq.~(6.29) bottom block at the `t = 0` candidate `F₀`, the `(vb)ⱼ`-rows whose restrictions to
`V ∖ {v}` reproduce the split's rows (design §1.50(c): the eq.~(6.29) bottom is
**restriction-independent**, not `v`-vanishing).

Same column operation `Φ = columnOp hva` (`col_a += col_v`, eqs.~(6.14)–(6.15)) makes the candidate
row `w = hingeRow v a ρ` and the `va`-block rows `rn` pure-`v`-column in the operated frame
(`hingeRow_comp_columnOp_vanish_off`; `hrnvanish` for the abstract `rn`); precomposing the whole
family with `Φ` (a linear automorphism, independence preserved via the injective dual equivalence
`Φ.dualMap`) turns it into the operated family
`Sum.elim (Sum.elim (rn ·∘ₗ Φ) (w ∘ₗ Φ)) (ro ·∘ₗ Φ)`. There the operated top block — the `va`-rows
plus the operated candidate row, all pure-`v`-column — meets the *top*-vanishing hypothesis of the
restriction-bottom augment `linearIndependent_sum_restriction_block`, the operated top is
pinned-independent on body `v`'s column (`hnewpinaug`, eq.~(6.29) top-left `D × D` full rank = the
Claim~6.12 conditional, passed through), and the operated bottom is independent after restriction to
`V ∖ {v}` (`hbotrestrict`). The augment fires, and the operated family's independence transports
back through `Φ.dualMap` (injective) to the original family
`Sum.elim (Sum.elim rn (fun _ : Unit => hingeRow v a ρ)) ro` — the eq.~(6.29) certified count at
`F₀`. Graph-free / carrier-free pure linear algebra (the `ofNormals`/`withGraph` defeq trap,
TACTICS-QUIRKS §38, does not bite). -/
theorem linearIndependent_sum_augment_candidateRow_restriction
    [DecidableEq α] {v a : α} (hva : v ≠ a) {ιn ιo : Type*} [Finite ιn] [Finite ιo]
    {rn : ιn → Module.Dual ℝ (α → ScrewSpace k)} {ro : ιo → Module.Dual ℝ (α → ScrewSpace k)}
    {ρ : Module.Dual ℝ (ScrewSpace k)}
    (hrnvanish : ∀ (i : ιn) (S : α → ScrewSpace k), S v = 0 →
      (rn i).comp (columnOp (k := k) hva).toLinearMap S = 0)
    (hnewpinaug : LinearIndependent ℝ (Sum.elim
      (fun i : ιn =>
        ((rn i).comp (columnOp (k := k) hva).toLinearMap).comp
          (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v))
      (fun _ : Unit =>
        ((hingeRow (k := k) (α := α) v a ρ).comp (columnOp (k := k) hva).toLinearMap).comp
          (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v))))
    (hbotrestrict : LinearIndependent ℝ
      (fun j : ιo => ((ro j).comp (columnOp (k := k) hva).toLinearMap).comp
        ((LinearMap.id : (α → ScrewSpace k) →ₗ[ℝ] (α → ScrewSpace k))
          - (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v).comp (LinearMap.proj v)))) :
    LinearIndependent ℝ
      (Sum.elim (Sum.elim rn (fun _ : Unit => hingeRow (k := k) (α := α) v a ρ)) ro) := by
  set Φ := columnOp (k := k) hva with hΦ
  have hker : LinearMap.ker Φ.dualMap.toLinearMap = ⊥ :=
    LinearMap.ker_eq_bot_of_injective Φ.dualMap.injective
  -- The operated top block `(rn ⊕ {w}) ∘ₗ Φ` vanishes on every assignment supported off `v`: the
  -- `rn`-part by `hrnvanish`, the operated candidate `w ∘ₗ Φ` by the columnOp vanish-off brick.
  have htopvanish : ∀ (i : ιn ⊕ Unit) (S : α → ScrewSpace k), S v = 0 →
      Sum.elim (fun i : ιn => (rn i).comp Φ.toLinearMap)
        (fun _ : Unit => (hingeRow (k := k) (α := α) v a ρ).comp Φ.toLinearMap) i S = 0 := by
    rintro (i | u) S hS
    · exact hrnvanish i S hS
    · rw [Sum.elim_inr, LinearMap.comp_apply, LinearEquiv.coe_coe,
        hingeRow_comp_columnOp_vanish_off hva ρ S hS]
  -- The operated top block is pinned-independent on body `v`'s column: `hnewpinaug` after the
  -- `Sum.elim`-of-pins is reassociated to the pin-of-`Sum.elim` shape.
  have htoppin : LinearIndependent ℝ
      (fun i : ιn ⊕ Unit =>
        (Sum.elim (fun i : ιn => (rn i).comp Φ.toLinearMap)
          (fun _ : Unit => (hingeRow (k := k) (α := α) v a ρ).comp Φ.toLinearMap) i).comp
          (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v)) := by
    convert hnewpinaug using 1
    funext i; rcases i with i | u <;> rfl
  -- The restriction-bottom augment fires on the operated family.
  have hop : LinearIndependent ℝ (Sum.elim
      (Sum.elim (fun i : ιn => (rn i).comp Φ.toLinearMap)
        (fun _ : Unit => (hingeRow (k := k) (α := α) v a ρ).comp Φ.toLinearMap))
      (fun j : ιo => (ro j).comp Φ.toLinearMap)) :=
    linearIndependent_sum_restriction_block (v := v) htopvanish htoppin hbotrestrict
  -- The operated family is `Φ.dualMap ∘ (original family)`; transport independence back through the
  -- injective dual equivalence `Φ.dualMap` (`g ↦ g ∘ₗ Φ`).
  have hcomp : (Sum.elim (Sum.elim (fun i : ιn => (rn i).comp Φ.toLinearMap)
        (fun _ : Unit => (hingeRow (k := k) (α := α) v a ρ).comp Φ.toLinearMap))
      (fun j : ιo => (ro j).comp Φ.toLinearMap))
      = Φ.dualMap ∘
        (Sum.elim (Sum.elim rn (fun _ : Unit => hingeRow (k := k) (α := α) v a ρ)) ro) := by
    funext i; rcases i with (i | i) | j <;> rfl
  rw [hcomp] at hop
  exact (Φ.dualMap.toLinearMap.linearIndependent_iff hker).1 hop

/-! ## Multi-edge rigidity-row independence over a rigid block (the Case-I `hindep` assembly)

The forest / multi-body generalization of single-edge row independence
(`linearIndependent_hingeRow_forest`, `exists_independent_rigidityRows_of_forest`) — the full-rank
input for the Case-I producer. -/

/-- **Cross-hinge independence over a rigid block of edges spanning many bodies**
(`def:rigidity-matrix`, the Case-I `hindep` step in its general form). The multi-body
generalization of `linearIndependent_hingeRow_star`: where the star fixes one common body `v`,
here each hinge `j : J` is oriented from a *private endpoint* `u j` — the "child" vertex of a
spanning forest of the rigid block, so the `u j` are distinct (`hu` injective) — to an arbitrary
*other endpoint* `other j`, subject only to the **forest separation** hypothesis `hsep`: no
other-endpoint of any hinge is the private endpoint of any hinge (`other j ≠ u j'` for all
`j, j'`; in particular `u j ≠ other j`). If for each `j` the hinge-row functionals
`r j : Iⱼ → Module.Dual ℝ (ScrewSpace k)` are linearly independent, the combined rigidity-row
family `⟨j, i⟩ ↦ hingeRow (u j) (other j) (r j i)` over `Σ j, Iⱼ` is linearly independent on
`α → ScrewSpace k`.

This is the cross-hinge step a genuine rigid block — a spanning tree / forest of the contracted
block, hinges spanning *multiple* bodies rather than a single pinned `v` — presents to
`hglue_of_realization`'s `hindep`. The star (`linearIndependent_hingeRow_star`) is the special
case `u = w`, `other = const v`: there `hsep` is `w j' ≠ v`, here it is the forest property that
each hinge has a private child vertex incident to no other hinge of the block. The proof is the
same *pin-a-body* / disjoint-support count, pinning the private endpoint `u j₀` rather than the
common body: evaluating a vanishing combination at the screw assignment `Function.update 0 (u j₀)
x` reads `0` on every hinge `j ≠ j₀` (its private endpoint `u j ≠ u j₀` by injectivity, its other
endpoint `other j ≠ u j₀` by `hsep`) and `x` on hinge `j₀` (its other endpoint `other j₀ ≠ u j₀`
again by `hsep`), collapsing to `∑ i, c⟨j₀,i⟩ • (r j₀ i) x = 0` for all `x`, so per-hinge
independence forces every coefficient at `j₀` to vanish. -/
theorem linearIndependent_hingeRow_forest {J : Type*} [Finite J] {I : J → Type*}
    [∀ j, Finite (I j)] {u other : J → α} (hu : Function.Injective u)
    (hsep : ∀ j j', other j ≠ u j')
    {r : ∀ j, I j → Module.Dual ℝ (ScrewSpace k)} (hr : ∀ j, LinearIndependent ℝ (r j)) :
    LinearIndependent ℝ
      (fun p : Σ j, I j => hingeRow (k := k) (α := α) (u p.1) (other p.1) (r p.1 p.2)) := by
  classical
  haveI : Fintype J := Fintype.ofFinite J
  haveI : ∀ j, Fintype (I j) := fun j => Fintype.ofFinite (I j)
  rw [Fintype.linearIndependent_iff]
  intro g hg k₀
  obtain ⟨j₀, i₀⟩ := k₀
  -- Evaluate the vanishing functional combination at `update 0 (u j₀) x`.
  have hval : ∀ x : ScrewSpace k, ∑ i, g ⟨j₀, i⟩ • (r j₀ i) x = 0 := by
    intro x
    have happ := LinearMap.congr_fun hg (Function.update (0 : α → ScrewSpace k) (u j₀) x)
    rw [LinearMap.sum_apply, LinearMap.zero_apply, Fintype.sum_sigma] at happ
    -- Every slice `j ≠ j₀` reads `0` at both endpoints; the `j₀` slice reads `x` at `u j₀`.
    rw [Finset.sum_eq_single j₀] at happ
    · refine Eq.trans (Finset.sum_congr rfl (fun i _ => ?_)) happ
      rw [LinearMap.smul_apply, hingeRow_apply, Function.update_self,
        Function.update_of_ne (hsep j₀ j₀), Pi.zero_apply, sub_zero]
    · intro j _ hjk
      refine Finset.sum_eq_zero (fun i _ => ?_)
      have hjw : u j ≠ u j₀ := fun h => hjk (hu h)
      rw [LinearMap.smul_apply, hingeRow_apply, Function.update_of_ne hjw,
        Function.update_of_ne (hsep j j₀)]
      simp only [Pi.zero_apply, sub_zero, map_zero, smul_zero]
    · exact fun h => absurd (Finset.mem_univ j₀) h
  -- The collapsed sum is a vanishing combination of `r j₀`, independent by hypothesis.
  have hk : ∑ i, g ⟨j₀, i⟩ • r j₀ i = 0 :=
    LinearMap.ext fun x => by
      simpa [LinearMap.sum_apply, LinearMap.smul_apply] using hval x
  exact Fintype.linearIndependent_iff.1 (hr j₀) (fun i => g ⟨j₀, i⟩) hk i₀

/-- **A rigid block's spanning forest of transversal hinges yields `(D−1)·|J|` independent
rigidity rows** (`def:rigidity-matrix`, the Case-I `hindep`/`hmatch` assembly in its general form).
This is the multi-body assembly the hand-off flagged: it combines the per-edge brick
`exists_independent_rigidityRows_of_edge` (each transversal hinge contributing `D − 1 = screwDim
k − 1` independent rows through the same relative-screw evaluation `screwDiff (u j) (other j)`) with
the cross-hinge combination `linearIndependent_hingeRow_forest` (rows of *distinct* hinges jointly
independent by the pin-a-body count over the spanning forest).

Concretely, for a family of hinges `j : J` of a rigid block oriented along a spanning forest — each
edge `e j` linking a *private endpoint* `u j` (the forest child, so `u` injective) to an arbitrary
`other j`, with the forest-separation hypothesis `hsep : ∀ j j', other j ≠ u j'` and every hinge
transversal (`he : F.supportExtensor (e j) ≠ 0`) — there is a linearly independent family of
rigidity rows indexed by the disjoint union `Σ j, Fin (screwDim k − 1)`, all members of
`F.rigidityRows`. The index type has cardinality `|J|·(screwDim k − 1)` (`Nat.card_sigma`), so this
is the matching-size independent subfamily `s` the Case-I capstone `hglue_of_realization` consumes:
its `hindep` is the joint independence and its `hmatch` count is `|J|·(D − 1)`, matched against the
contraction's inductive rank. The per-edge block functionals `c j` (a basis of the
`(D−1)`-dimensional hinge-row block `r(p(e j))`, `finrank_hingeRowBlock`) are extracted by
`exists_linearIndependent_fin_of_finrank_eq`, fed to `linearIndependent_hingeRow_forest` for the
joint independence, and witnessed as rigidity rows via the link `hlink j` and block membership. -/
theorem exists_independent_rigidityRows_of_forest (F : BodyHingeFramework k α β) {J : Type*}
    [Finite J] {u other : J → α} {e : J → β} (hu : Function.Injective u)
    (hsep : ∀ j j', other j ≠ u j') (hlink : ∀ j, F.graph.IsLink (e j) (u j) (other j))
    (he : ∀ j, F.supportExtensor (e j) ≠ 0) :
    ∃ r : (Σ _ : J, Fin (screwDim k - 1)) → Module.Dual ℝ (α → ScrewSpace k),
      LinearIndependent ℝ r ∧ ∀ p, r p ∈ F.rigidityRows := by
  classical
  haveI : FiniteDimensional ℝ (ScrewSpace k) := inferInstance
  -- Per-edge basis of the `(D−1)`-dimensional hinge-row block `r(p(e j))`.
  choose c hc hmem using fun j =>
    (F.hingeRowBlock (e j)).exists_linearIndependent_fin_of_finrank_eq
      (F.finrank_hingeRowBlock (he j))
  refine ⟨fun p => hingeRow (u p.1) (other p.1) (c p.1 p.2),
    linearIndependent_hingeRow_forest hu hsep hc, fun p => ?_⟩
  exact ⟨e p.1, u p.1, other p.1, hlink p.1, c p.1 p.2, hmem p.1 p.2, rfl⟩

/-! ## Trivial motions + infinitesimal rigidity: rank Lemmas 5.1–5.3 (KT §2.4)

The trivial (rigid-motion) subspace of dimension `D`, the rigidity predicates
(`IsInfinitesimallyRigid{,On}`), and the three rank lemmas — Lemma 5.1 (pin-a-body,
`finrank_pinnedMotions_add_screwDim`), Lemma 5.2 (semicontinuity,
`finrank_infinitesimalMotions_le_of_span_le`), Lemma 5.3 (parallel hinges,
`eq_of_hingeConstraint_two_parallel`). -/

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

/-- **Infinitesimal rigidity relative to a body set `s`** (`def:rank-hypothesis`, the
`V(G)`-relative motive): every infinitesimal motion is constant *on `s`*, `S u = S v` for all
`u v ∈ s`. This is the `α`-independent realization motive of the algebraic induction (Phase 21b):
the absolute form `IsInfinitesimallyRigid` (constancy on *all* of `α`) is unsatisfiable for a
graph `G` that does not span the ambient body type `α` — a body in `α ∖ V(G)` carries no hinge
constraint and is a free non-trivial motion — but the realization induction reduces to subgraphs
with strictly fewer vertices on the same fixed `α`. Read at `s = V(G)`, this asks only that
motions be constant on the bodies `G` actually carries, which is `rank R(G,p) = D(|V(G)|−1)` and
composes through the vertex-reducing induction. Taking `s = Set.univ` recovers the absolute form
(`isInfinitesimallyRigidOn_univ_iff`). -/
def IsInfinitesimallyRigidOn (F : BodyHingeFramework k α β) (s : Set α) : Prop :=
  ∀ S, F.IsInfinitesimalMotion S → ∀ u ∈ s, ∀ v ∈ s, S u = S v

theorem isInfinitesimallyRigidOn_iff (F : BodyHingeFramework k α β) (s : Set α) :
    F.IsInfinitesimallyRigidOn s ↔
      ∀ S, F.IsInfinitesimalMotion S → ∀ u ∈ s, ∀ v ∈ s, S u = S v :=
  Iff.rfl

/-- **Relative rigidity shrinks with the body set** (`def:rank-hypothesis`): a framework rigid on
`t` is rigid on any subset `s ⊆ t`. Constancy on the larger set forces constancy on the
smaller. -/
theorem IsInfinitesimallyRigidOn.mono (F : BodyHingeFramework k α β) {s t : Set α} (hst : s ⊆ t)
    (h : F.IsInfinitesimallyRigidOn t) : F.IsInfinitesimallyRigidOn s :=
  fun S hS u hu v hv => h S hS u (hst hu) v (hst hv)

/-- **Absolute rigidity is relative rigidity on all of `α`** (`def:rank-hypothesis`): the
`V(G)`-relative motive at `s = Set.univ` is exactly the absolute infinitesimal rigidity
`IsInfinitesimallyRigid` (every motion constant on every pair). -/
theorem isInfinitesimallyRigidOn_univ_iff (F : BodyHingeFramework k α β) :
    F.IsInfinitesimallyRigidOn Set.univ ↔ F.IsInfinitesimallyRigid := by
  rw [isInfinitesimallyRigidOn_iff, isInfinitesimallyRigid_iff]
  exact ⟨fun h S hS u v => h S hS u (Set.mem_univ u) v (Set.mem_univ v),
    fun h S hS u _ v _ => h S hS u v⟩

/-- **Absolute rigidity implies relative rigidity on any set** (`def:rank-hypothesis`): if every
infinitesimal motion is constant on *all* of `α` then in particular it is constant on `s`. This is
the direction the cycle / two-body base cases use — they prove the strong absolute statement when
`G` spans, which immediately gives the relative motive on `V(G)`. -/
theorem isInfinitesimallyRigidOn_of_isInfinitesimallyRigid (F : BodyHingeFramework k α β)
    (h : F.IsInfinitesimallyRigid) (s : Set α) : F.IsInfinitesimallyRigidOn s :=
  fun S hS u _ v _ => (F.isInfinitesimallyRigid_iff.mp h S hS) u v

/-- **Two overlapping rigid pieces glue to a rigid union** (`def:rank-hypothesis`, the splice-glue
of Case I; Katoh–Tanigawa 2011 §6.2/6.5). If a framework is infinitesimally rigid on each of two
body sets `s` and `t` that share a body `c ∈ s ∩ t`, then it is rigid on their union `s ∪ t`:
every motion is constant on `s` and constant on `t`, and the two constants agree at the shared
body `c`, so the motion is constant across all of `s ∪ t`. This is the `α`-independent geometric
core of the Case-I block-triangular splice — the rigid subgraph `H` (on `s = V(H)`) and the rigid
contraction `G/E(H)` (on `t = V(G/E(H))`) overlap at the contracted body and cover `V(G)`, so a
framework realizing both pieces realizes the parent rank. -/
theorem isInfinitesimallyRigidOn_union_of_inter (F : BodyHingeFramework k α β) {s t : Set α}
    {c : α} (hcs : c ∈ s) (hct : c ∈ t)
    (hs : F.IsInfinitesimallyRigidOn s) (ht : F.IsInfinitesimallyRigidOn t) :
    F.IsInfinitesimallyRigidOn (s ∪ t) := by
  intro S hS u hu v hv
  have key : ∀ x ∈ s ∪ t, S x = S c := by
    rintro x (hx | hx)
    · exact hs S hS x hx c hcs
    · exact ht S hS x hx c hct
  rw [key u hu, key v hv]

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
  have key := Submodule.finrank_sup_of_inf_eq_bot F.trivialMotions (F.pinnedMotions v) hdisj
  rw [hsup, F.finrank_trivialMotions] at key
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
