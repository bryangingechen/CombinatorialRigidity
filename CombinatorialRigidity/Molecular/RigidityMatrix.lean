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
explicit basis.

## Carrier API (Phase 22l, part 1 — pre-opacity)

The `mk` / `val` / `equivExteriorPower` API below is the stable boundary surface that the
forthcoming carrier-opacity flip (`abbrev` → opaque `def`; `notes/Phase22l.md`,
`notes/ScrewSpaceCarrier-design.md`) needs every reach-in routed through: it replaces the
bare `⟨val, proof⟩` anonymous-constructor and `Subtype.val` coercion idioms that an opaque
head would block. The carrier is still a reducible `abbrev` here, so this API is defeq-thin
(`mk`/`val` are the constructor/projection, `equivExteriorPower` is `LinearEquiv.refl`) and
adopting it is behaviour-preserving; the file-by-file migration of all reach-ins onto it is
what lets the eventual flip land project-green in one mechanical commit. -/
abbrev ScrewSpace (k : ℕ) : Type :=
  ↥(⋀[ℝ]^k (Fin (k + 2) → ℝ))

/-- **Constructor for the `ScrewSpace` carrier** from an exterior-algebra element with a
membership proof — the named replacement for the bare `⟨v, h⟩ : ScrewSpace k` anonymous
constructor, kept building once the carrier becomes an opaque `def` (Phase 22l). -/
def ScrewSpace.mk {k : ℕ} (v : ExteriorAlgebra ℝ (Fin (k + 2) → ℝ))
    (h : v ∈ ⋀[ℝ]^k (Fin (k + 2) → ℝ)) : ScrewSpace k :=
  (⟨v, h⟩ : ↥(⋀[ℝ]^k (Fin (k + 2) → ℝ)))

/-- **The underlying exterior-algebra element of a `ScrewSpace` carrier** — the named
replacement for the `Subtype.val` coercion `(C : ⋀[ℝ]^k …)`, kept building once the carrier
becomes an opaque `def` (Phase 22l). -/
def ScrewSpace.val {k : ℕ} (C : ScrewSpace k) : ExteriorAlgebra ℝ (Fin (k + 2) → ℝ) :=
  Subtype.val (C : ↥(⋀[ℝ]^k (Fin (k + 2) → ℝ)))

@[simp]
theorem ScrewSpace.val_mk {k : ℕ} (v : ExteriorAlgebra ℝ (Fin (k + 2) → ℝ))
    (h : v ∈ ⋀[ℝ]^k (Fin (k + 2) → ℝ)) : (ScrewSpace.mk v h).val = v := rfl

theorem ScrewSpace.val_mem {k : ℕ} (C : ScrewSpace k) :
    C.val ∈ ⋀[ℝ]^k (Fin (k + 2) → ℝ) :=
  (C : ↥(⋀[ℝ]^k (Fin (k + 2) → ℝ))).property

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
boundary `≃ₗ` for the basis / dual work; because the carrier is (and stays, through the
opacity flip) definitionally the graded piece, this is `LinearEquiv.refl`, so transports
across it are definitional no-ops (`notes/ScrewSpaceCarrier-design.md` §5 OQ3). -/
noncomputable def ScrewSpace.equivExteriorPower (k : ℕ) :
    ScrewSpace k ≃ₗ[ℝ] ↥(⋀[ℝ]^k (Fin (k + 2) → ℝ)) :=
  LinearEquiv.refl ℝ (ScrewSpace k)

@[simp]
theorem ScrewSpace.equivExteriorPower_apply {k : ℕ} (C : ScrewSpace k) :
    ScrewSpace.equivExteriorPower k C = C := rfl

@[simp]
theorem ScrewSpace.equivExteriorPower_symm_apply {k : ℕ}
    (C : ↥(⋀[ℝ]^k (Fin (k + 2) → ℝ))) :
    (ScrewSpace.equivExteriorPower k).symm C = C := rfl

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

/-- **The `D` panel-support 2-extensors of `4` linearly-independent homogeneous vectors span
`ScrewSpace 2`** (`lem:case-III-claim612-extensor-span`, Katoh–Tanigawa eq. (6.45) via Lemma 2.1).
At `d = 3` (`D = 6`, `ScrewSpace 2 = ⋀²ℝ⁴`, `finrank = 6`), for four linearly-independent
homogeneous vectors `pbar : Fin 4 → ℝ⁴` the `binom(4,2) = 6` panel-support `2`-extensors
`omitTwoExtensor pbar`
— one per pair, the join `pᵢ ∨ pⱼ` of the line through each pair — span all of
`⋀²ℝ⁴ = ScrewSpace 2`. By Lemma 2.1 (`omitTwoExtensor_linearIndependent_of_li` at `e = 2`) the six
are linearly independent in the `6`-dimensional `ScrewSpace 2`, and a linearly independent family of
`6 = finrank ℝ (ScrewSpace 2)` vectors is a basis, hence spans. This is the spanning input to the
Claim-6.12 contrapositive (`lem:case-III-claim612`): a single nonzero `r ∈ ScrewSpace 2`
annihilating every supporting extensor in the union (6.45) is forced to be `0`. The bare-LI
hypothesis is what the `d = 3` producer feeds directly (`exists_homogeneousIncidence_of_normals`),
sparing the de-homogenization to affine points (`notes/Phase22-realization-design.md` §1.42). -/
theorem span_omitTwoExtensor_eq_top {pbar : Fin 4 → Fin 4 → ℝ} (hp : LinearIndependent ℝ pbar) :
    Submodule.span ℝ
        (Set.range (fun q : {q : Fin 4 × Fin 4 // q.1 < q.2} =>
          (ScrewSpace.mk (omitTwoExtensor pbar (ne_of_lt q.2))
            (extensor_mem_exteriorPower _) : ScrewSpace 2))) = ⊤ := by
  set c : {q : Fin 4 × Fin 4 // q.1 < q.2} → ScrewSpace 2 :=
    fun q => ScrewSpace.mk (omitTwoExtensor pbar (ne_of_lt q.2))
      (extensor_mem_exteriorPower _)
  -- The coerced family is the Lemma-2.1 omit-two family, linearly independent; transport
  -- the independence through the (injective) submodule inclusion (the opaque carrier's
  -- `.val` is the underlying exterior-algebra element).
  have hcoe : LinearIndependent ℝ
      (fun q : {q : Fin 4 × Fin 4 // q.1 < q.2} =>
        omitTwoExtensor pbar (ne_of_lt q.2)) :=
    omitTwoExtensor_linearIndependent_of_li pbar hp
  have hLI : LinearIndependent ℝ c :=
    (LinearMap.linearIndependent_iff
      ((⋀[ℝ]^2 (Fin (2 + 2) → ℝ)).subtype.comp (ScrewSpace.equivExteriorPower 2).toLinearMap)
      (by rw [LinearMap.ker_comp, Submodule.ker_subtype, Submodule.comap_bot,
        LinearEquiv.ker])).1 hcoe
  -- `6 = finrank ℝ (ScrewSpace 2)`, so the LI family is a basis and spans.
  have hcard : Fintype.card {q : Fin 4 × Fin 4 // q.1 < q.2} = Module.finrank ℝ (ScrewSpace 2) := by
    rw [screwSpace_finrank]
    decide
  haveI : Nonempty {q : Fin 4 × Fin 4 // q.1 < q.2} := ⟨⟨(0, 1), by decide⟩⟩
  have hbasis := (basisOfLinearIndependentOfCardEqFinrank hLI hcard).span_eq
  rwa [coe_basisOfLinearIndependentOfCardEqFinrank] at hbasis

/-- **A functional annihilating a spanning set is zero** (`lem:case-III-claim612-orthseq-vanish`,
the Claim-6.12 contrapositive's non-degeneracy step). If a screw-space functional
`r : Module.Dual ℝ (ScrewSpace k)` vanishes on every element of a set `S` whose span is all of
`ScrewSpace k`, then `r = 0`. Two linear maps agreeing on a spanning set are equal
(`LinearMap.ext_on`); `r` agrees with the zero functional on `S` and `span S = ⊤`, so `r = 0` — the
non-degeneracy of the dual pairing on `ℝ^D`. This is
the final step of the Claim-6.12 contrapositive (`lem:case-III-claim612`): the common vector `r` is
orthogonal to every supporting extensor in KT's union (6.45), which the six panel-support extensors
of four affinely-independent points force to span `ScrewSpace 2` (`span_omitTwoExtensor_eq_top`), so
`r = 0`, contradicting `r ≠ 0`. -/
theorem eq_zero_of_annihilates_span_top {k : ℕ} {S : Set (ScrewSpace k)}
    (hS : Submodule.span ℝ S = ⊤) {r : Module.Dual ℝ (ScrewSpace k)}
    (hr : ∀ x ∈ S, r x = 0) : r = 0 :=
  -- `r` agrees with `0` on the spanning set `S`, hence everywhere (`LinearMap.ext_on`).
  LinearMap.ext_on hS (fun x hx => by simp [hr x hx])

/-- **The intersection of `< d+1` panel hyperplanes in `ℝ^(d+1)` is nonempty as a projective
locus** (`lem:case-III-claim612-points-affineIndep`, the existence half of KT eq. (6.45)'s point
choice; the `j`-hyperplane intersection brick). Given a family `n : Fin m → (Fin (d+1) → ℝ)` of
`m` panel normals with `m < d + 1`, the homogeneous incidence system `⟨p̄, n i⟩ = 0` for all `i`
has a *nonzero* solution `p̄ : Fin (d+1) → ℝ`: the `m × (d+1)` coefficient matrix has strictly more
columns than rows, so its null space is nontrivial. This is the geometric existence step behind
KT's "for any `j` of the hyperplanes their intersection forms a `(d-j)`-dimensional affine space"
(p. 698, eq. (6.67)): with `m = j` panels, the homogeneous (projective) solution set is a genuine
`(d+1-j)`-dimensional subspace, hence nonempty, so a representative homogeneous point exists on
every one of the chosen panels. (The *affine independence* of the four chosen points — that they
span an affine `3`-simplex at `d = 3` — is the genericity content of the full
`lem:case-III-claim612-points-affineIndep`, still red: it needs the affine-independence determinant
nonvanishing from the algebraic independence of the panel coefficients, `lem:genericity-device`.) -/
theorem exists_ne_zero_dotProduct_eq_zero {d m : ℕ} (hm : m < d + 1)
    (n : Fin m → Fin (d + 1) → ℝ) :
    ∃ p : Fin (d + 1) → ℝ, p ≠ 0 ∧ ∀ i, p ⬝ᵥ n i = 0 := by
  classical
  -- View the incidence system as the linear map `(Fin (d+1) → ℝ) → (Fin m → ℝ)`,
  -- `p ↦ (i ↦ ⟨p, n i⟩)`; its source outranks its target, so the kernel is nontrivial.
  set f : (Fin (d + 1) → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
    { toFun := fun p i => p ⬝ᵥ n i
      map_add' := fun p q => by ext i; simp [add_dotProduct]
      map_smul' := fun c p => by ext i; simp [smul_dotProduct] } with hf
  -- `finrank (ker f) = (d+1) - rank f ≥ (d+1) - m > 0`.
  have hrange : Module.finrank ℝ (LinearMap.range f) ≤ m := by
    refine le_trans (Submodule.finrank_le _) ?_
    simp
  have hker : 0 < Module.finrank ℝ (LinearMap.ker f) := by
    have hrk := f.finrank_range_add_finrank_ker
    rw [Module.finrank_pi, Fintype.card_fin] at hrk
    omega
  -- A positive-dimensional kernel is nontrivial, so it contains a nonzero vector.
  have hne : LinearMap.ker f ≠ ⊥ := by rw [Ne, ← Submodule.finrank_eq_zero]; omega
  obtain ⟨⟨p, hp⟩, hpne⟩ := @exists_ne _ (Submodule.nontrivial_iff_ne_bot.mpr hne) 0
  refine ⟨p, fun h => hpne (Subtype.ext (by simpa using h)), fun i => ?_⟩
  exact congrFun (LinearMap.mem_ker.mp hp) i

/-- **The product-route producer for generic affine independence**
(`lem:case-III-claim612-points-affineIndep`, the genericity-to-realization closure half). Suppose
the `d + 1` candidate points are built as functions `p : (σ → ℝ) → Fin (d+1) → Fin d → ℝ` of a
panel-coordinate seed `q : σ → ℝ`, and their affine-independence determinant — the homogenization
determinant `det (homogenize ∘ (p q)) : ℝ` of `affineIndependent_fin_iff_det_homogenize` — is the
evaluation of a *nonzero* multivariate polynomial `P : MvPolynomial σ ℝ` in `q` (`hdet`). Then there
is a seed `q` at which the points `p q` are **affinely independent**.

This is the genericity-free *closure* step: it composes the device's foundational non-root brick
`MvPolynomial.exists_eval_ne_zero` (over the infinite field `ℝ`, a nonzero polynomial does not
vanish identically; the same brick Case I uses to pick a shared seed) with the determinant
characterization `affineIndependent_fin_iff_det_homogenize` (Lemma 2.1, top-extensor form). It
carries the genericity *content* as the hypothesis `hdet` — that the affine-independence
determinant, as a function of the seed, is a nonzero polynomial — which is the irreducible
genericity remainder of N3a (KT p. 691/698, `lem:genericity-device`: the determinant is nonzero
because the panel coefficients are algebraically independent over `ℚ`). Parallel to the existence
half `exists_ne_zero_dotProduct_eq_zero`, this isolates the genuinely genericity-bearing fact
(`P ≠ 0`) from the surrounding linear-algebra glue. -/
theorem exists_affineIndependent_of_det_polynomial_ne_zero {d : ℕ} {σ : Type*}
    (p : (σ → ℝ) → Fin (d + 1) → Fin d → ℝ) {P : MvPolynomial σ ℝ} (hP : P ≠ 0)
    (hdet : ∀ q, MvPolynomial.eval q P = (Matrix.of fun i => homogenize (p q i)).det) :
    ∃ q : σ → ℝ, AffineIndependent ℝ (p q) := by
  -- A nonzero polynomial over the infinite field `ℝ` has a non-vanishing point.
  obtain ⟨q, hq⟩ := MvPolynomial.exists_eval_ne_zero hP
  -- At that seed the determinant is nonzero, so the points are affinely independent.
  exact ⟨q, (affineIndependent_fin_iff_det_homogenize (p q)).mpr (hdet q ▸ hq)⟩

/-- **The affine-independence determinant of polynomial-valued candidate points is a polynomial in
the seed** (`lem:case-III-claim612-points-affineIndep`, the determinant-polynomial bridge feeding
the closure half). Suppose the `d + 1` candidate points are built coordinate-by-coordinate as
multivariate polynomials in the panel-coordinate seed: a family `pp : Fin (d+1) → Fin d →
MvPolynomial σ ℝ`, with the point `p q i := fun j => eval q (pp i j)`. Then their
affine-independence determinant — the homogenization determinant
`det (homogenize ∘ (p q)) : ℝ` of `affineIndependent_fin_iff_det_homogenize` — is the evaluation at
`q` of a *single* polynomial `P : MvPolynomial σ ℝ`, namely the determinant of the
`(d+1) × (d+1)` polynomial matrix whose rows are the homogenized polynomial points
`Fin.snoc (pp i) 1`.

This discharges the `hdet` hypothesis of the closure producer
`exists_affineIndependent_of_det_polynomial_ne_zero`: the ring homomorphism `eval q` commutes with
`det` (`RingHom.map_det`) and with `Fin.snoc · 1` (it sends the constant final coordinate `1` to
`1`), so evaluating the polynomial determinant at `q` reproduces the real homogenization determinant
of the evaluated points. It isolates the *polynomial-in-the-seed* structure of the determinant from
the genuinely genericity-bearing fact that this polynomial is nonzero (`P ≠ 0`, the irreducible
remainder of N3a, the genericity device `lem:genericity-device`), exactly as the existence half
`exists_ne_zero_dotProduct_eq_zero` and the closure half
`exists_affineIndependent_of_det_polynomial_ne_zero` isolate their own ingredients. -/
theorem exists_detPolynomial_of_pointPolynomial {d : ℕ} {σ : Type*}
    (pp : Fin (d + 1) → Fin d → MvPolynomial σ ℝ) :
    ∃ P : MvPolynomial σ ℝ, ∀ q : σ → ℝ,
      MvPolynomial.eval q P
        = (Matrix.of fun i => homogenize (fun j => MvPolynomial.eval q (pp i j))).det := by
  classical
  -- `P` is the determinant of the polynomial matrix whose rows are the homogenized polynomial
  -- points `Fin.snoc (pp i) 1`. Evaluation at `q` is a ring hom, so it commutes with `det`.
  refine ⟨(Matrix.of fun i => Fin.snoc (pp i) 1).det, fun q => ?_⟩
  rw [(MvPolynomial.eval q).map_det]
  congr 1
  -- The evaluated polynomial matrix is the homogenization matrix of the evaluated points:
  -- `eval q` commutes with `Fin.snoc · 1` (it fixes the constant final coordinate `1`).
  ext i j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp [homogenize, Matrix.map_apply]
  · simp [homogenize, Matrix.map_apply]

/-- **The explicit good seed: four affinely-independent points realizing the
`Π(a)/Π(b)/Π(c)` incidence pattern** (`lem:case-III-claim612-points-affineIndep`, the `P ≠ 0`
existence witness; KT eq. (6.45) point choice). At `d = 3` there exist three panel normals
`n : Fin 3 → ℝ⁴` in *nonparallel* position (`LinearIndependent`) and four **affinely-independent**
points `p : Fin 4 → ℝ³` realizing the triple-intersection incidence pattern of KT eq. (6.45):
`p 0 ∈ Π(a) ∩ Π(b) ∩ Π(c)`, `p 1 ∈ Π(a) ∩ Π(b) ∖ Π(c)`, `p 2 ∈ Π(b) ∩ Π(c) ∖ Π(a)`,
`p 3 ∈ Π(c) ∩ Π(a) ∖ Π(b)`, where panel incidence `p i ∈ Π(u) ⟺ ⟨homogenize (p i), n u⟩ = 0`
(the `⬝ᵥ` of the homogenization with the panel normal).

This is the **existence-route residual** of `lem:case-III-claim612-points-affineIndep`: by the
converse of `MvPolynomial.exists_eval_ne_zero` (the foundational non-root brick the closure half
`exists_affineIndependent_of_det_polynomial_ne_zero` runs forward) and the determinant-polynomial
bridge `exists_detPolynomial_of_pointPolynomial`, the residual `P ≠ 0` of the cross-product
construction (the affine-independence determinant as a polynomial in the panel-coordinate seed) is
*logically equivalent* to exhibiting **one** seed at which the constructed points are affinely
independent — no algebraic independence of the seed is needed, exactly the existence/Zariski route
the pre-Phase-22d genericity sites (Claim 6.4/6.9) used. Here the witness is the coordinate-aligned
seed: panel normals `n_a = e₀`, `n_b = e₁`, `n_c = e₂` (the first three standard covectors of `ℝ⁴`,
hence linearly independent — the nonparallel hypothesis the framework supplies) and the standard
affine `3`-simplex `p = (0, e₃, e₁, e₂)` of `ℝ³` (origin plus three axis points). The incidence
pattern is then immediate from the coordinates: `homogenize (p i)` is orthogonal to exactly the
panel normals whose coordinate it vanishes at, and the `4 × 4` homogenization determinant is
`±1 ≠ 0` (`affineIndependent_fin_iff_det_homogenize` via the explicit `Matrix.det_succ_row_zero`
cofactor expansion). -/
theorem exists_affineIndependent_panel_incidence :
    ∃ (n : Fin 3 → Fin 4 → ℝ) (p : Fin 4 → Fin 3 → ℝ),
      AffineIndependent ℝ p ∧ LinearIndependent ℝ n ∧
      -- `p 0` lies on all three panels (the triple intersection)
      (∀ u, homogenize (p 0) ⬝ᵥ n u = 0) ∧
      -- `p 1 ∈ Π(a) ∩ Π(b) ∖ Π(c)`
      (homogenize (p 1) ⬝ᵥ n 0 = 0 ∧ homogenize (p 1) ⬝ᵥ n 1 = 0 ∧ homogenize (p 1) ⬝ᵥ n 2 ≠ 0) ∧
      -- `p 2 ∈ Π(b) ∩ Π(c) ∖ Π(a)`
      (homogenize (p 2) ⬝ᵥ n 1 = 0 ∧ homogenize (p 2) ⬝ᵥ n 2 = 0 ∧ homogenize (p 2) ⬝ᵥ n 0 ≠ 0) ∧
      -- `p 3 ∈ Π(c) ∩ Π(a) ∖ Π(b)`
      (homogenize (p 3) ⬝ᵥ n 2 = 0 ∧ homogenize (p 3) ⬝ᵥ n 0 = 0 ∧
        homogenize (p 3) ⬝ᵥ n 1 ≠ 0) := by
  classical
  refine ⟨![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0]],
    ![![0, 0, 0], ![0, 0, 1], ![1, 0, 0], ![0, 1, 0]], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Affine independence: the homogenization determinant of the standard simplex is `±1 ≠ 0`.
    rw [affineIndependent_fin_iff_det_homogenize,
      show (Matrix.of fun i => homogenize ((![![0, 0, 0], ![0, 0, 1], ![1, 0, 0], ![0, 1, 0]] :
          Fin 4 → Fin 3 → ℝ) i)) = !![(0 : ℝ), 0, 0, 1; 0, 0, 1, 1; 1, 0, 0, 1; 0, 1, 0, 1] from by
        ext i j; fin_cases i <;> fin_cases j <;> simp [homogenize, Fin.snoc]]
    rw [Matrix.det_succ_row_zero]
    simp [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove]
  · -- The three coordinate covectors are linearly independent.
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hg' := congrFun hg
    fin_cases i
    · simpa [Fin.sum_univ_succ] using hg' 0
    · simpa [Fin.sum_univ_succ] using hg' 1
    · simpa [Fin.sum_univ_succ] using hg' 2
  · intro u; fin_cases u <;> simp [homogenize, Fin.snoc, dotProduct, Fin.sum_univ_succ]
  · refine ⟨?_, ?_, ?_⟩ <;> simp [homogenize, Fin.snoc, dotProduct, Fin.sum_univ_succ]
  · refine ⟨?_, ?_, ?_⟩ <;> simp [homogenize, Fin.snoc, dotProduct, Fin.sum_univ_succ]
  · refine ⟨?_, ?_, ?_⟩ <;> simp [homogenize, Fin.snoc, dotProduct, Fin.sum_univ_succ]

/-- **The kept-points tabulation of the six spanning joins** (`lem:case-III-claim612`, N3a/N3b
glue; Katoh–Tanigawa 2011 §6.4.1 eq. (6.45), Phase 22g). For the four affinely-independent points
`p : Fin 4 → ℝ³` of `exists_affineIndependent_panel_incidence` (N3a) and a join
`q : {q // q.1 < q.2}` (the omitted pair), the spanning join
`omitTwoExtensor (homogenize ∘ p) (ne_of_lt q.2)` — the `2`-extensor of the two points **kept** by
the omit-two operation — is the point-join `extensor ![homogenize (p c), homogenize (p d)]` of the
two increasing complement indices `c < d` of `{q.1, q.2}`. This is the purely combinatorial
`orderEmbOfFin`-computation half of the per-join `hduality` witness (`case_III_claim612`): it pins
down, for each of the six joins, *which two points* span the join, so the `hduality` dispatch can
look up the panel(s) the join's line `pᵢpⱼ` lies in (the incidence tabulation of N3a) and supply the
two normals `{n_u, n'}` the per-line transfer
(`extensor_join_eq_zero_of_complementIso_eq_zero_dotProduct`) consumes.

The six joins and their kept (complement) pairs: `(0,1)↦(2,3)`, `(0,2)↦(1,3)`, `(0,3)↦(1,2)`,
`(1,2)↦(0,3)`, `(1,3)↦(0,2)`, `(2,3)↦(0,1)`. Graph-free; pure `Finset.orderEmbOfFin` arithmetic
(`Finset.orderEmbOfFin_unique`) on `Fin 4`. -/
theorem omitTwoExtensor_homogenize_eq_extensor_kept (p : Fin 4 → Fin 3 → ℝ)
    (q : {q : Fin 4 × Fin 4 // q.1 < q.2}) :
    ∃ c d : Fin 4, c < d ∧ c ≠ q.1.1 ∧ c ≠ q.1.2 ∧ d ≠ q.1.1 ∧ d ≠ q.1.2 ∧
      omitTwoExtensor (fun i => homogenize (p i)) (ne_of_lt q.2)
        = extensor ![homogenize (p c), homogenize (p d)] := by
  obtain ⟨⟨i, j⟩, hij⟩ := q
  -- The kept pair is the increasing enumeration `emb 0 < emb 1` of `{i, j}ᶜ` (`orderEmbOfFin`,
  -- `StrictMono`); both differ from `i, j` (`orderEmbOfFin_mem` lands in the complement). The join
  -- identity `omitTwoExtensor v = extensor (v ∘ emb) = extensor ![v (emb 0), v (emb 1)]` is then a
  -- `funext`.
  set emb := (({i, j} : Finset (Fin 4))ᶜ).orderEmbOfFin (card_compl_pair (ne_of_lt hij)) with hemb
  have hmem : ∀ k : Fin 2, emb k ≠ i ∧ emb k ≠ j := by
    intro k
    have h := Finset.orderEmbOfFin_mem (({i, j} : Finset (Fin 4))ᶜ)
      (card_compl_pair (ne_of_lt hij)) k
    rw [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at h
    exact ⟨(hemb ▸ h).1, (hemb ▸ h).2⟩
  refine ⟨emb 0, emb 1, emb.strictMono (by decide), (hmem 0).1, (hmem 0).2, (hmem 1).1,
    (hmem 1).2, ?_⟩
  rw [omitTwoExtensor]; congr 1; ext k; fin_cases k <;> rfl

/-- **A second panel normal through a line in `ℝ⁴`** (`lem:case-III-claim612`, N3a/N3b glue;
Phase 22g). Given two points `pi, pj : Fin 4 → ℝ` of a line `L = pi pj` and one normal `n_u`
to which both are dot-orthogonal (`pi ⬝ᵥ n_u = pj ⬝ᵥ n_u = 0`), with `n_u ≠ 0`, there is a
*second* normal `n'`, linearly independent from `n_u`, to which both points are also orthogonal —
i.e. a second hyperplane through the line `L`. This is the constructed second normal KT's
contrapositive needs for the three "opposite" joins `pᵢ ∨ pⱼ` (the joins through a single panel
`Π(u)`, eq. (6.45)): the per-line transfer
(`extensor_join_eq_zero_of_complementIso_eq_zero_dotProduct`, N3b) consumes a pair `{n_u, n'}` of
independent normals, but a single-panel join supplies only one panel normal directly, so the second
is read off the geometry here.

The common-perp space `W = {x | pi ⬝ᵥ x = 0 ∧ pj ⬝ᵥ x = 0}` is the kernel of
`x ↦ ![pi ⬝ᵥ x, pj ⬝ᵥ x] : ℝ⁴ → ℝ²`, so by rank–nullity `finrank W ≥ 4 − 2 = 2 > 1 = finrank
(span ℝ {n_u})`; the span is therefore a *proper* subspace of `W`, and `SetLike.exists_of_lt`
exhibits `n' ∈ W ∖ span ℝ {n_u}`, which `LinearIndependent.pair_iff'` upgrades to independence. -/
theorem exists_independent_perp_pair (pi pj n_u : Fin 4 → ℝ)
    (hi : pi ⬝ᵥ n_u = 0) (hj : pj ⬝ᵥ n_u = 0) (hn_u : n_u ≠ 0) :
    ∃ n' : Fin 4 → ℝ, LinearIndependent ℝ ![n_u, n'] ∧ pi ⬝ᵥ n' = 0 ∧ pj ⬝ᵥ n' = 0 := by
  -- The common-perp space as the kernel of the two-functional map `L x = ![pi ⬝ᵥ x, pj ⬝ᵥ x]`.
  set L : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
    Matrix.mulVecLin (Matrix.of ![pi, pj]) with hL
  have hmemW : ∀ x : Fin 4 → ℝ, x ∈ LinearMap.ker L ↔ pi ⬝ᵥ x = 0 ∧ pj ⬝ᵥ x = 0 := by
    intro x
    rw [LinearMap.mem_ker, hL, Matrix.mulVecLin_apply]
    rw [funext_iff]
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · have := h 0; simpa [Matrix.mulVec, Matrix.of_apply, dotProduct_comm] using this
      · have := h 1; simpa [Matrix.mulVec, Matrix.of_apply, dotProduct_comm] using this
    · rintro ⟨h0, h1⟩ i
      fin_cases i
      · simpa [Matrix.mulVec, Matrix.of_apply, dotProduct_comm] using h0
      · simpa [Matrix.mulVec, Matrix.of_apply, dotProduct_comm] using h1
  -- Rank–nullity: `finrank (ker L) ≥ 4 − 2 = 2`.
  have hker : 2 ≤ Module.finrank ℝ (LinearMap.ker L) := by
    have hrn := L.finrank_range_add_finrank_ker
    have hdom : Module.finrank ℝ (Fin 4 → ℝ) = 4 := by rw [Module.finrank_pi]; rfl
    have hcod : Module.finrank ℝ (LinearMap.range L) ≤ 2 := by
      calc Module.finrank ℝ (LinearMap.range L)
          ≤ Module.finrank ℝ (Fin 2 → ℝ) := Submodule.finrank_le _
        _ = 2 := by rw [Module.finrank_pi]; rfl
    omega
  -- `n_u ∈ ker L`, and `span ℝ {n_u}` is a *proper* subspace (its finrank is `1 < 2 ≤ finrank W`).
  have hn_uW : n_u ∈ LinearMap.ker L := (hmemW n_u).2 ⟨hi, hj⟩
  have hlt : Submodule.span ℝ {n_u} < LinearMap.ker L := by
    refine lt_of_le_of_ne ((Submodule.span_singleton_le_iff_mem _ _).2 hn_uW) ?_
    intro heq
    have h1 : Module.finrank ℝ (Submodule.span ℝ {n_u}) = 1 := finrank_span_singleton hn_u
    rw [heq] at h1
    omega
  obtain ⟨n', hn'W, hn'not⟩ := SetLike.exists_of_lt hlt
  obtain ⟨hi', hj'⟩ := (hmemW n').1 hn'W
  refine ⟨n', (LinearIndependent.pair_iff' hn_u).2 ?_, hi', hj'⟩
  intro a heq
  exact hn'not (heq ▸ Submodule.smul_mem _ a (Submodule.mem_span_singleton_self _))

/-- **The homogeneous incidence core of the witness points, parameterized by the real panel
normals** (`lem:case-III-claim612-points-affineIndep`, the (R1) reconciliation core; Katoh–Tanigawa
2011 §6.4.1 eq. (6.45), Phase 22g). Given **three** real panel normals `n : Fin 3 → ℝ⁴` in
*nonparallel* position (`LinearIndependent ℝ n` — the genericity the `d = 3` `hsplit` producer reads
off its GP split-leg, `notes/Phase22-realization-design.md` §1.41), there exist four homogeneous
coordinate vectors `pbar : Fin 4 → ℝ⁴` that are **linearly independent** and realize KT eq.
(6.45)'s triple-intersection incidence pattern *relative to the real `n`*: `pbar 0` lies on all
three panels (`⟨pbar 0, n u⟩ = 0`), and each `pbar (i+1)` lies on two of the panels but strictly off
the third.

This is the (R1) replacement, at the **homogeneous-vector** layer, for the hardcoded-normals
`exists_affineIndependent_panel_incidence` (which fixes `n = e₀,e₁,e₂`): the producer's witness
points must be orthogonal to the *real* split-leg panel normals `n_a, n_b, n_c`, not to a fixed
coordinate frame. The construction is **genericity-free** — it isolates the genericity-bearing
residual (the de-homogenization to affine `ℝ³` points, i.e. that the orthogonal vectors are not at
infinity) exactly as `exists_ne_zero_dotProduct_eq_zero` / the det-polynomial bricks above isolate
their own ingredients:

* the row matrix `A = of n : Matrix (Fin 3) (Fin 4) ℝ` has linearly independent rows, so
  `A.rank = 3` (`LinearIndependent.rank_matrix`); its image `range A.mulVecLin` then has
  `finrank = 3 = finrank ℝ³`, hence is all of `ℝ³`, so `A.mulVecLin` is **surjective**. Concretely,
  for *any* prescribed pairing target `t : Fin 3 → ℝ` there is `x : ℝ⁴` with `x ⬝ᵥ n u = t u` for
  all `u`. The three points `pbar 1, pbar 2, pbar 3` are the preimages of the standard-basis-like
  targets `(0,0,1)`, `(1,0,0)`, `(0,1,0)` (giving exactly the off-one-panel incidence), and `pbar 0`
  is the nonzero common-perp vector from `exists_ne_zero_dotProduct_eq_zero`;
* linear independence of the four `pbar` is the triangular argument on the incidence matrix: pairing
  `∑ gᵢ • pbar i = 0` against `n 0` kills all but `pbar 2` ⟹ `g 2 = 0`; against `n 1` ⟹ `g 3 = 0`;
  against `n 2` ⟹ `g 1 = 0`; then `g 0 • pbar 0 = 0` with `pbar 0 ≠ 0` ⟹ `g 0 = 0`. No genericity
  of `n` beyond `LinearIndependent` is used.

Graph-free; pure `Fin 4` panel geometry. The affine de-homogenization (the `pbar i = homogenize
(p i)` representatives, the genericity-bearing residual) is the remaining (R1) sub-leaf. -/
theorem exists_homogeneousIncidence_of_normals {n : Fin 3 → Fin 4 → ℝ}
    (hn : LinearIndependent ℝ n) :
    ∃ pbar : Fin 4 → Fin 4 → ℝ, LinearIndependent ℝ pbar ∧
      (∀ u, pbar 0 ⬝ᵥ n u = 0) ∧
      (pbar 1 ⬝ᵥ n 0 = 0 ∧ pbar 1 ⬝ᵥ n 1 = 0 ∧ pbar 1 ⬝ᵥ n 2 ≠ 0) ∧
      (pbar 2 ⬝ᵥ n 1 = 0 ∧ pbar 2 ⬝ᵥ n 2 = 0 ∧ pbar 2 ⬝ᵥ n 0 ≠ 0) ∧
      (pbar 3 ⬝ᵥ n 2 = 0 ∧ pbar 3 ⬝ᵥ n 0 = 0 ∧ pbar 3 ⬝ᵥ n 1 ≠ 0) := by
  classical
  -- The pairing map `x ↦ (u ↦ n u ⬝ᵥ x)` is `mulVecLin` of the row matrix `A = of n`; its rows are
  -- linearly independent, so `A.rank = 3 = finrank ℝ³`, hence `mulVecLin` is surjective.
  set A : Matrix (Fin 3) (Fin 4) ℝ := Matrix.of n with hA
  have hrow : A.rank = 3 := by
    have : LinearIndependent ℝ A.row := by
      rw [show A.row = n from rfl]; exact hn
    simpa using this.rank_matrix
  have hsurj : Function.Surjective A.mulVecLin := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    rw [show Module.finrank ℝ (Fin 3 → ℝ) = 3 from by rw [Module.finrank_pi]; rfl]
    exact hrow
  -- A preimage `x` of target `t : Fin 3 → ℝ` has `x ⬝ᵥ n u = t u` for all `u`.
  have hpre : ∀ t : Fin 3 → ℝ, ∃ x : Fin 4 → ℝ, ∀ u, x ⬝ᵥ n u = t u := by
    intro t
    obtain ⟨x, hx⟩ := hsurj t
    refine ⟨x, fun u => ?_⟩
    have := congrFun hx u
    rwa [Matrix.mulVecLin_apply, Matrix.mulVec, hA, dotProduct_comm] at this
  -- `pbar 0`: nonzero common-perp vector of all three normals (`3 < 4`).
  obtain ⟨p0, hp0ne, hp0⟩ := exists_ne_zero_dotProduct_eq_zero (by omega : 3 < 3 + 1) n
  -- `pbar 1, 2, 3`: preimages of `(0,0,1)`, `(1,0,0)`, `(0,1,0)`; read their pairings off cleanly.
  obtain ⟨p1, hp1⟩ := hpre ![0, 0, 1]
  obtain ⟨p2, hp2⟩ := hpre ![1, 0, 0]
  obtain ⟨p3, hp3⟩ := hpre ![0, 1, 0]
  have e10 : p1 ⬝ᵥ n 0 = 0 := by simpa using hp1 0
  have e11 : p1 ⬝ᵥ n 1 = 0 := by simpa using hp1 1
  have e12 : p1 ⬝ᵥ n 2 = 1 := by simpa using hp1 2
  have e20 : p2 ⬝ᵥ n 0 = 1 := by simpa using hp2 0
  have e21 : p2 ⬝ᵥ n 1 = 0 := by simpa using hp2 1
  have e22 : p2 ⬝ᵥ n 2 = 0 := by simpa using hp2 2
  have e30 : p3 ⬝ᵥ n 0 = 0 := by simpa using hp3 0
  have e31 : p3 ⬝ᵥ n 1 = 1 := by simpa using hp3 1
  have e32 : p3 ⬝ᵥ n 2 = 0 := by simpa using hp3 2
  -- Assemble the witness family and read its incidence off the clean pairings (`![…] i` reduces).
  set pbar : Fin 4 → Fin 4 → ℝ := ![p0, p1, p2, p3] with hpbar
  have hb0 : ∀ u, pbar 0 ⬝ᵥ n u = 0 := fun u => by simpa [hpbar] using hp0 u
  have hb1 : pbar 1 ⬝ᵥ n 0 = 0 ∧ pbar 1 ⬝ᵥ n 1 = 0 ∧ pbar 1 ⬝ᵥ n 2 ≠ 0 :=
    ⟨by simpa [hpbar] using e10, by simpa [hpbar] using e11, by simp [hpbar, e12]⟩
  have hb2 : pbar 2 ⬝ᵥ n 1 = 0 ∧ pbar 2 ⬝ᵥ n 2 = 0 ∧ pbar 2 ⬝ᵥ n 0 ≠ 0 :=
    ⟨by simpa [hpbar] using e21, by simpa [hpbar] using e22, by simp [hpbar, e20]⟩
  have hb3 : pbar 3 ⬝ᵥ n 2 = 0 ∧ pbar 3 ⬝ᵥ n 0 = 0 ∧ pbar 3 ⬝ᵥ n 1 ≠ 0 :=
    ⟨by simpa [hpbar] using e32, by simpa [hpbar] using e30, by simp [hpbar, e31]⟩
  refine ⟨pbar, ?_, hb0, hb1, hb2, hb3⟩
  -- Linear independence: the triangular argument on the incidence matrix.
  rw [Fintype.linearIndependent_iff]
  intro g hg
  -- Pairing `∑ gᵢ • pbar i = 0` against `n u` gives `∑ gᵢ (pbar i ⬝ᵥ n u) = 0`.
  have hpair : ∀ u : Fin 3, g 0 * (p0 ⬝ᵥ n u) + g 1 * (p1 ⬝ᵥ n u) + g 2 * (p2 ⬝ᵥ n u)
      + g 3 * (p3 ⬝ᵥ n u) = 0 := by
    intro u
    have hzero : (∑ i, g i • pbar i) ⬝ᵥ n u = 0 := by rw [hg]; simp
    rw [sum_dotProduct, Fin.sum_univ_four] at hzero
    simpa only [hpbar, smul_dotProduct, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.tail_cons] using hzero
  -- Each pairing isolates one coordinate (the unique `pbar i` off that panel).
  have hg2 : g 2 = 0 := by
    have h := hpair 0; rw [hp0 0, e10, e20, e30] at h; linarith
  have hg3 : g 3 = 0 := by
    have h := hpair 1; rw [hp0 1, e11, e21, e31] at h; linarith
  have hg1 : g 1 = 0 := by
    have h := hpair 2; rw [hp0 2, e12, e22, e32] at h; linarith
  -- With `g 1 = g 2 = g 3 = 0`, `hg` reduces to `g 0 • p0 = 0`, and `p0 ≠ 0` forces `g 0 = 0`.
  have hg0 : g 0 = 0 := by
    rw [Fin.sum_univ_four, hg1, hg2, hg3] at hg
    simp only [hpbar, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, zero_smul, add_zero] at hg
    exact (smul_eq_zero.mp hg).resolve_right hp0ne
  intro i; fin_cases i <;> assumption

/-- **The kept-points tabulation of the six spanning joins, at the homogeneous-vector layer**
(`lem:case-III-claim612`, the producer-direction (R1-affine) form; Katoh–Tanigawa 2011 §6.4.1
eq. (6.45), Phase 22g). The bare-`pbar` analogue of `omitTwoExtensor_homogenize_eq_extensor_kept`:
for a homogeneous family `pbar : Fin 4 → ℝ⁴` and a join `q : {q // q.1 < q.2}` (the omitted pair),
the spanning join `omitTwoExtensor pbar (ne_of_lt q.2)` is the point-join
`extensor ![pbar c, pbar d]` of the two increasing complement indices `c < d` of `{q.1, q.2}` — the
two points the join's line `p̄_c p̄_d` actually spans. The producer feeds `pbar` directly from
`exists_homogeneousIncidence_of_normals` (no affine de-homogenization, §1.42 R1-affine), so the
join-line lookup is stated against the bare family rather than `homogenize ∘ p`. Graph-free; pure
`Finset.orderEmbOfFin` arithmetic (same `orderEmbOfFin_unique` computation as the affine form). -/
theorem omitTwoExtensor_eq_extensor_kept (pbar : Fin 4 → Fin 4 → ℝ)
    (q : {q : Fin 4 × Fin 4 // q.1 < q.2}) :
    ∃ c d : Fin 4, c < d ∧ c ≠ q.1.1 ∧ c ≠ q.1.2 ∧ d ≠ q.1.1 ∧ d ≠ q.1.2 ∧
      omitTwoExtensor pbar (ne_of_lt q.2) = extensor ![pbar c, pbar d] := by
  obtain ⟨⟨i, j⟩, hij⟩ := q
  set emb := (({i, j} : Finset (Fin 4))ᶜ).orderEmbOfFin (card_compl_pair (ne_of_lt hij)) with hemb
  have hmem : ∀ k : Fin 2, emb k ≠ i ∧ emb k ≠ j := by
    intro k
    have h := Finset.orderEmbOfFin_mem (({i, j} : Finset (Fin 4))ᶜ)
      (card_compl_pair (ne_of_lt hij)) k
    rw [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at h
    exact ⟨(hemb ▸ h).1, (hemb ▸ h).2⟩
  refine ⟨emb 0, emb 1, emb.strictMono (by decide), (hmem 0).1, (hmem 0).2, (hmem 1).1,
    (hmem 1).2, ?_⟩
  rw [omitTwoExtensor]; congr 1; ext k; fin_cases k <;> rfl

/-- **The per-join witness line data from the homogeneous incidence** (`lem:case-III-claim612`, the
"extract the witness line `L`" leaf of the `d = 3` `hsplit` producer; Katoh–Tanigawa 2011 §6.4.1
eqs. (6.42)–(6.45), Phase 22g). The producer-direction analogue of the (now `hann`-obsolete)
`exists_hduality_witness_of_panel_incidence`: where that lemma carried a meet-annihilation premise
`hann` and concluded the per-join annihilation, this strips both and hands over only the **geometric
line data**, on the **homogeneous-vector** layer (bare `pbar`, fed by
`exists_homogeneousIncidence_of_normals`, §1.42 R1-affine). For each of the six joins `q`, it
produces a **discriminating witness index** `u : Fin 3` (so the witness panel normal is the real
split-leg normal `n u` — the `Fin 3`-valued M₁/M₂/M₃ dispatch input the `hcand`-discharge reads,
§1.50(a)), a second hyperplane `n'` through the join line `L = p̄_c p̄_d` independent from `n u`,
and the two kept points `pi = pbar c, pj = pbar d` the join spans — all four facts the candidate
placement needs: `LinearIndependent ![n u, n']`, the four `⬝ᵥ`-orthogonalities
`{pi, pj} ⊥ {n u, n'}`, and the join identity
`omitTwoExtensor pbar (ne_of_lt q.2) = extensor ![pi, pj]`.

This is exactly the input
`panelSupportExtensor_add_smul_left_ne_zero_of_join_ne_zero` (the Leaf-2b seed-from-line core)
consumes to turn Claim 6.12's existential witness `r̂(p̄_i ∨ p̄_j) ≠ 0` into the nonzero
candidate-row input `r̂(panelSupportExtensor (n_u + t • n') n_u) ≠ 0` the row-space criterion fires
on. The
construction mirrors `exists_hduality_witness_of_panel_incidence`'s two builders: the three joins
through `p̄ 0` lie on **two** N3a panels (use two real normals `n u, n w`); the three "opposite"
joins share **one** panel `Π(u)` (use `n u` and a constructed second normal from
`exists_independent_perp_pair`). Graph-free; pure `Fin 4` panel geometry. -/
theorem exists_line_data_of_homogeneousIncidence
    {n : Fin 3 → Fin 4 → ℝ} (hn : LinearIndependent ℝ n)
    {pbar : Fin 4 → Fin 4 → ℝ}
    (h0 : ∀ u, pbar 0 ⬝ᵥ n u = 0)
    (h1 : pbar 1 ⬝ᵥ n 0 = 0 ∧ pbar 1 ⬝ᵥ n 1 = 0)
    (h2 : pbar 2 ⬝ᵥ n 1 = 0 ∧ pbar 2 ⬝ᵥ n 2 = 0)
    (h3 : pbar 3 ⬝ᵥ n 2 = 0 ∧ pbar 3 ⬝ᵥ n 0 = 0) :
    ∀ q : {q : Fin 4 × Fin 4 // q.1 < q.2},
      ∃ (u : Fin 3) (n' pi pj : Fin 4 → ℝ), LinearIndependent ℝ ![n u, n'] ∧
        pi ⬝ᵥ n u = 0 ∧ pi ⬝ᵥ n' = 0 ∧ pj ⬝ᵥ n u = 0 ∧ pj ⬝ᵥ n' = 0 ∧
        omitTwoExtensor pbar (ne_of_lt q.2) = extensor ![pi, pj] := by
  -- Two N3a panel normals `n a, n b` are independent (subfamily of the independent `n`).
  have hpair : ∀ a b : Fin 3, a ≠ b → LinearIndependent ℝ ![n a, n b] := by
    intro a b hab
    have := hn.comp ![a, b] (by intro x y hxy; fin_cases x <;> fin_cases y <;> simp_all)
    rwa [show (n ∘ ![a, b]) = ![n a, n b] from by ext x; fin_cases x <;> rfl] at this
  -- **Two-panel join builder** (the three joins through `p̄ 0`): the kept points `e₁, e₂` both lie
  -- on panels `Π(u)` *and* `Π(w)` (two N3a normals); the discriminating witness normal is `n u`,
  -- the second hyperplane `n' = n w` (so `u : Fin 3` is the dispatch index the producer reads).
  have htwo : ∀ (q : {q : Fin 4 × Fin 4 // q.1 < q.2}) (u w : Fin 3) (e₁ e₂ : Fin 4 → ℝ),
      u ≠ w → e₁ ⬝ᵥ n u = 0 → e₁ ⬝ᵥ n w = 0 → e₂ ⬝ᵥ n u = 0 → e₂ ⬝ᵥ n w = 0 →
      omitTwoExtensor pbar (ne_of_lt q.2) = extensor ![e₁, e₂] →
      ∃ (u : Fin 3) (n' pi pj : Fin 4 → ℝ), LinearIndependent ℝ ![n u, n'] ∧
        pi ⬝ᵥ n u = 0 ∧ pi ⬝ᵥ n' = 0 ∧ pj ⬝ᵥ n u = 0 ∧ pj ⬝ᵥ n' = 0 ∧
        omitTwoExtensor pbar (ne_of_lt q.2) = extensor ![pi, pj] :=
    fun _ u w e₁ e₂ huw h1u h1w h2u h2w hkept =>
      ⟨u, n w, e₁, e₂, hpair u w huw, h1u, h1w, h2u, h2w, hkept⟩
  -- **One-panel join builder** (the three "opposite" joins, single shared panel `Π(u)`): both kept
  -- points lie on `Π(u)`; the discriminating witness normal is `n u` and
  -- `exists_independent_perp_pair` builds the second hyperplane `n'`.
  have hone : ∀ (q : {q : Fin 4 × Fin 4 // q.1 < q.2}) (u : Fin 3) (e₁ e₂ : Fin 4 → ℝ),
      e₁ ⬝ᵥ n u = 0 → e₂ ⬝ᵥ n u = 0 →
      omitTwoExtensor pbar (ne_of_lt q.2) = extensor ![e₁, e₂] →
      ∃ (u : Fin 3) (n' pi pj : Fin 4 → ℝ), LinearIndependent ℝ ![n u, n'] ∧
        pi ⬝ᵥ n u = 0 ∧ pi ⬝ᵥ n' = 0 ∧ pj ⬝ᵥ n u = 0 ∧ pj ⬝ᵥ n' = 0 ∧
        omitTwoExtensor pbar (ne_of_lt q.2) = extensor ![pi, pj] :=
    fun _ u e₁ e₂ h1u h2u hkept => by
      obtain ⟨n', hpair', h1', h2'⟩ :=
        exists_independent_perp_pair e₁ e₂ (n u) h1u h2u (hn.ne_zero u)
      exact ⟨u, n', e₁, e₂, hpair', h1u, h1', h2u, h2', hkept⟩
  -- The per-join kept-points identity (concrete `c, d` per join), from the general tabulation.
  have hkept : ∀ (q : {q : Fin 4 × Fin 4 // q.1 < q.2}) (c d : Fin 4), c < d →
      c ≠ q.1.1 → c ≠ q.1.2 → d ≠ q.1.1 → d ≠ q.1.2 →
      omitTwoExtensor pbar (ne_of_lt q.2) = extensor ![pbar c, pbar d] := by
    intro q c d hcd hc1 hc2 hd1 hd2
    obtain ⟨c', d', hcd', hc1', hc2', hd1', hd2', heq⟩ := omitTwoExtensor_eq_extensor_kept pbar q
    -- `c, d` and `c', d'` are both the increasing complement of `{q.1, q.2}`, hence equal.
    obtain rfl : c' = c := by omega
    obtain rfl : d' = d := by omega
    exact heq
  intro q
  obtain ⟨h1a, h1b⟩ := h1; obtain ⟨h2a, h2b⟩ := h2; obtain ⟨h3a, h3b⟩ := h3
  -- For each of the six joins, the kept points come off the increasing complement of the omitted
  -- pair, and the common panel(s) from the incidence tabulation: `(0,1)↦keep(2,3)`, `n2` (one);
  -- `(0,2)↦keep(1,3)`, `n0`; `(0,3)↦keep(1,2)`, `n1`; `(1,2)↦keep(0,3)`, `{n0,n2}` (two);
  -- `(1,3)↦keep(0,2)`, `{n1,n2}`; `(2,3)↦keep(0,1)`, `{n0,n1}`. The builders take `q` explicitly so
  -- the heavy `omitTwoExtensor` carrier need not be `whnf`'d to infer it (TACTICS-QUIRKS §38).
  fin_cases q
  · exact hone ⟨(0, 1), by decide⟩ 2 _ _ h2b h3a
      (hkept ⟨(0, 1), by decide⟩ 2 3 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact hone ⟨(0, 2), by decide⟩ 0 _ _ h1a h3b
      (hkept ⟨(0, 2), by decide⟩ 1 3 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact hone ⟨(0, 3), by decide⟩ 1 _ _ h1b h2a
      (hkept ⟨(0, 3), by decide⟩ 1 2 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact htwo ⟨(1, 2), by decide⟩ 0 2 _ _ (by decide) (h0 0) (h0 2) h3b h3a
      (hkept ⟨(1, 2), by decide⟩ 0 3 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact htwo ⟨(1, 3), by decide⟩ 1 2 _ _ (by decide) (h0 1) (h0 2) h2a h2b
      (hkept ⟨(1, 3), by decide⟩ 0 2 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact htwo ⟨(2, 3), by decide⟩ 0 1 _ _ (by decide) (h0 0) (h0 1) h1a h1b
      (hkept ⟨(2, 3), by decide⟩ 0 1 (by decide) (by decide) (by decide) (by decide) (by decide))

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

/-- **A row functional lies in the hinge-row block iff it annihilates the supporting extensor**
(`lem:case-III-claim612-block-iff-perp`, the membership half of KT's eq.~(6.42) row-space criterion;
Katoh–Tanigawa 2011 §6.4.1, Phase 22e). The hinge-row block `r(p(e)) = (span C(p(e)))^⊥` is the
dual annihilator of the line `span {C(p(e))}` (`hingeRowBlock`), so a candidate functional
`r̂ : Module.Dual ℝ (ScrewSpace k)` lies in it iff it annihilates the supporting extensor itself:
`r̂ ∈ r(p(e)) ⟺ r̂ (C(p(e))) = 0`. The forward direction evaluates the annihilator at
`C ∈ span {C}`; the converse scales `r̂ (a • C) = a • r̂ C = 0` across the span singleton. This is
the `(span C)^⊥` membership test the Claim-6.12 row-space criterion negates
(`r̂ ∉ (span C)^⊥ ⟺ r̂(C) ≠ 0`). -/
theorem mem_hingeRowBlock_iff (F : BodyHingeFramework k α β) (e : β)
    (r : Module.Dual ℝ (ScrewSpace k)) :
    r ∈ F.hingeRowBlock e ↔ r (F.supportExtensor e) = 0 := by
  rw [hingeRowBlock, Submodule.mem_dualAnnihilator]
  refine ⟨fun h => h _ (Submodule.mem_span_singleton_self _), fun h x hx => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
  rw [map_smul, h, smul_zero]

/-- **The Claim-6.12 row-space criterion: the candidate's top-left `D × D` block is full rank iff
`r̂(C) ≠ 0`** (`lem:case-III-claim612-block-iff-perp`, KT eq.~(6.42); Katoh–Tanigawa 2011 §6.4.1,
Phase 22e). Given the `D − 1` rows `rn` of a candidate's hinge block at `e` — linearly independent
and spanning the whole hinge-row block `r(p(e)) = (span C)^⊥` (the `(D−1)`-dimensional orthogonal
complement of the supporting line; `lem:case-II-placement-new-rows` supplies them) — the augmented
`D`-functional family (the `D − 1` block rows `rn` plus the candidate row `r̂`) is linearly
independent **iff** `r̂` is not orthogonal to the supporting extensor:
`r̂ ∉ (span C)^⊥ ⟺ r̂ (C(p(e))) ≠ 0`. The `D − 1` block rows already span the hyperplane
`(span C)^⊥`; appending `r̂` raises the dimension to `D` iff `r̂` is fresh
(`linearIndependent_sumElim_unit_iff`, the row-space criterion), and freshness off the hinge-row
block is exactly `r̂ (C) ≠ 0` (`mem_hingeRowBlock_iff`). This is the conditional `hnewpinaug` of the
candidate-completion assembly (`linearIndependent_sum_augment_candidateRow`) recast as a clean
orthogonality test — the eq.~(6.42) full-rank-of-the-top-left-block fact the `D`-candidate
disjunction (`lem:case-III-claim612`) discharges. -/
theorem linearIndependent_sumElim_candidateRow_iff (F : BodyHingeFramework k α β) (e : β)
    {ι : Type*} {rn : ι → Module.Dual ℝ (ScrewSpace k)} (hrn : LinearIndependent ℝ rn)
    (hspan : Submodule.span ℝ (Set.range rn) = F.hingeRowBlock e)
    (r : Module.Dual ℝ (ScrewSpace k)) :
    LinearIndependent ℝ (Sum.elim rn (fun _ : Unit => r)) ↔ r (F.supportExtensor e) ≠ 0 := by
  rw [linearIndependent_sumElim_unit_iff hrn, hspan, Ne, ← mem_hingeRowBlock_iff]

/-- **The operated candidate row pinned to `v`'s column is the candidate functional `ρ` itself**
(`lem:case-III-claim612-p2-placement`, the bridge feeding the row-space criterion to the
candidate-completion assembly; Katoh–Tanigawa 2011 §6.4.1, Phase 22e). Precomposing the candidate
row `hingeRow v b ρ` with the column op `Φ = columnOp hvb` (`col_b += col_v`) and then with body
`v`'s screw-column injection `single v` recovers `ρ` exactly: by `hingeRow_comp_columnOp_apply`,
`(hingeRow v b ρ ∘ₗ Φ) S = ρ(S v)`, and `single v x` reads `x` at `v`, so the composite is
`x ↦ ρ x`. This identifies the operated, pinned `(vb)i^*`-row — the candidate-completion's extra
top-left-block row — with the abstract candidate functional `ρ` on `ScrewSpace k`, so the row-space
criterion `linearIndependent_sumElim_candidateRow_iff` (stated on `ScrewSpace k`) reads directly on
the assembly's `hnewpinaug`. -/
theorem hingeRow_comp_columnOp_comp_single [DecidableEq α] {v b : α} (hvb : v ≠ b)
    (ρ : Module.Dual ℝ (ScrewSpace k)) :
    ((hingeRow (k := k) (α := α) v b ρ).comp (columnOp (k := k) hvb).toLinearMap).comp
      (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v) = ρ :=
  LinearMap.ext fun x => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      hingeRow_comp_columnOp_apply, LinearMap.single_apply, Pi.single_eq_same]

/-- **The operated, off-`v`-restricted `vb`-transport IS the `ab`-row** (KT eqs.~(6.26)–(6.28), the
membership-by-construction in functional form; Katoh–Tanigawa 2011 §6.4.1, Phase 22h). Brick 1 of
the W6 restriction-transport: composing the transported candidate row `hingeRow v b ρ` of
`R(G, p_1)` with the column op `Φ = columnOp hva` (`col_a += col_v`) and then the off-`v` projection
`P_v = id − single v ∘ₗ proj v` (W4's restriction) recovers the genuine `ab`-row `hingeRow a b ρ`.
The mechanism: `P_v S` zeroes the `v`-coordinate, so `(Φ (P_v S)) v = (P_v S) v + (P_v S) a = S a`
(using `v ≠ a`), while `(Φ (P_v S)) b = (P_v S) b = S b` (using `v ≠ b`, `Φ` only touches `v`);
hence `(hingeRow v b ρ)(Φ (P_v S)) = ρ(S a − S b) = (hingeRow a b ρ) S`. This is the reading of
KT's "`R(G, p_1; (vb)_j, v) = r_j(p_1(vb)) = r_j(q(ab))`" reproduction: in the operated, restricted
frame the `(vb)_j`-row coincides with the `(ab)_j`-row, so the certified `t = 0` family rebases onto
genuine `G_v^{ab}`-rows. -/
theorem hingeRow_comp_columnOp_comp_offProj [DecidableEq α] {v a b : α}
    (hva : v ≠ a) (hvb : v ≠ b) (ρ : Module.Dual ℝ (ScrewSpace k)) :
    ((hingeRow (k := k) (α := α) v b ρ).comp (columnOp (k := k) hva).toLinearMap).comp
        ((LinearMap.id : (α → ScrewSpace k) →ₗ[ℝ] (α → ScrewSpace k))
          - (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v).comp (LinearMap.proj v))
      = hingeRow (k := k) (α := α) a b ρ :=
  LinearMap.ext fun S => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, hingeRow_apply,
      hingeRow_apply, columnOp_apply, columnOp_apply, Function.update_self,
      Function.update_of_ne hvb.symm]
    -- `P_v S = S − single v (S v)`: zero at `v`, `S a`/`S b` at the distinct bodies `a`, `b`.
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      LinearMap.coe_single, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hva.symm,
      Pi.single_eq_of_ne hvb.symm, sub_zero, sub_self, zero_add]

/-- **A row reading nothing on `v`'s column is untouched by the operated restriction** (KT
eqs.~(6.26)–(6.28); Katoh–Tanigawa 2011 §6.4.1, Phase 22h). Brick 2 of the W6 restriction-transport:
when a functional `g` annihilates body `v`'s screw column (`g.comp (single v) = 0`), composing it
with the column op `Φ = columnOp hva` and the off-`v` projection `P_v` leaves it unchanged. Both
`Φ S = S + single v (S a)` and `P_v S = S − single v (S v)` differ from `S` only by `single v (·)`
terms, on which `g` vanishes, so `g (Φ (P_v S)) = g S`. This is the certificate that the genuine
`G_v`-rows (which read nothing on the re-inserted body `v`'s column) survive the operated
restriction verbatim — the "bottom rows are genuine `F₀`-rows" half of the W6 rebase, complementing
`hingeRow_comp_columnOp_comp_offProj`'s candidate-row tag. -/
theorem comp_columnOp_comp_offProj_of_single_eq_zero [DecidableEq α] {v a : α} (hva : v ≠ a)
    {g : Module.Dual ℝ (α → ScrewSpace k)}
    (hg : g.comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v) = 0) :
    (g.comp (columnOp (k := k) hva).toLinearMap).comp
        ((LinearMap.id : (α → ScrewSpace k) →ₗ[ℝ] (α → ScrewSpace k))
          - (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v).comp (LinearMap.proj v)) = g :=
  LinearMap.ext fun S => by
    -- `g (single v x) = 0` for every `x`, the pointwise form of `hg`.
    have hgsingle : ∀ x : ScrewSpace k,
        g (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v x) = 0 :=
      fun x => by rw [← LinearMap.comp_apply, hg, LinearMap.zero_apply]
    -- The off-`v` projection `P_v S = update S v 0` (`id − single v ∘ proj v`).
    set P : (α → ScrewSpace k) →ₗ[ℝ] (α → ScrewSpace k) :=
      (LinearMap.id : (α → ScrewSpace k) →ₗ[ℝ] (α → ScrewSpace k))
        - (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v).comp (LinearMap.proj v) with hP
    have hPv : ∀ (T : α → ScrewSpace k), P T = Function.update T v 0 := fun T => by
      funext y
      rw [hP]
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
        LinearMap.proj_apply, LinearMap.coe_single, Pi.sub_apply]
      rcases eq_or_ne y v with rfl | hy
      · rw [Pi.single_eq_same, sub_self, Function.update_self]
      · rw [Pi.single_eq_of_ne hy, sub_zero, Function.update_of_ne hy]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, hPv]
    -- `Φ (P_v S) = update S v (S a)`: `P_v` zeroes the `v`-coordinate, `Φ` then sets it to
    -- `(P_v S) v + (P_v S) a = 0 + S a = S a`.
    rw [show (columnOp (k := k) hva) (Function.update S v 0) = Function.update S v (S a) from by
      funext y
      unfold columnOp
      rcases eq_or_ne y v with rfl | hy
      · simp [Function.update_of_ne hva.symm]
      · simp [Function.update_of_ne hy]]
    -- `update S v (S a) = S + single v (S a − S v)`; `g` kills the `single v` term, leaving `g S`.
    have hupd : Function.update S v (S a)
        = S + LinearMap.single ℝ (fun _ : α => ScrewSpace k) v (S a - S v) := by
      funext y
      rcases eq_or_ne y v with rfl | hy
      · simp [Pi.single_eq_same]
      · simp [Function.update_of_ne hy, Pi.single_eq_of_ne hy]
    rw [hupd, map_add, hgsingle, add_zero]

/-- **A hinge row restricted to its tail body's screw column is the block functional** (the
column-restriction leaf of KT eq.~(6.43)/(6.44); Katoh–Tanigawa 2011 §6.4.1, Phase 22e). For a
hinge oriented out of body `a` (the tail) into a distinct body `b`, precomposing
`hingeRow a b ρ` with body `a`'s screw-column injection `single a` recovers `ρ` exactly:
`(hingeRow a b ρ)(single a x) = ρ((single a x) a − (single a x) b) = ρ(x − 0) = ρ x`, since
`single a x` reads `x` at `a` and `0` at the distinct `b`. This is the "the `ab`-row contributes
`ρ` to the `a`-column" half of the eq.~(6.43) `a`-column regrouping. -/
theorem hingeRow_comp_single_tail [DecidableEq α] {a b : α} (hab : a ≠ b)
    (ρ : Module.Dual ℝ (ScrewSpace k)) :
    (hingeRow (k := k) (α := α) a b ρ).comp
      (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a) = ρ :=
  LinearMap.ext fun x => by
    rw [LinearMap.comp_apply, hingeRow_apply, LinearMap.single_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne (Ne.symm hab), sub_zero]

/-- **A hinge row restricted to a body incident to neither endpoint is zero** (the
column-restriction leaf of KT eq.~(6.43)/(6.44); Katoh–Tanigawa 2011 §6.4.1, Phase 22e). When body
`a` is incident to neither endpoint of the hinge `uw` (`a ≠ u`, `a ≠ w`), precomposing
`hingeRow u w ρ` with body `a`'s screw-column injection `single a` is `0`: `single a x` reads `0`
at both `u` and `w`, so `(hingeRow u w ρ)(single a x) = ρ(0 − 0) = 0`. This is the
"every other edge contributes `0` to the `a`-column" half of the eq.~(6.43)/(6.44) regrouping ---
the degree-2-at-`a` fact that, in `G_v^{ab}`, only the `ab`- and `ac`-rows survive in body `a`'s
column. -/
theorem hingeRow_comp_single_off [DecidableEq α] {u w a : α} (hau : a ≠ u) (haw : a ≠ w)
    (ρ : Module.Dual ℝ (ScrewSpace k)) :
    (hingeRow (k := k) (α := α) u w ρ).comp
      (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a) = 0 :=
  LinearMap.ext fun x => by
    rw [LinearMap.comp_apply, hingeRow_apply, LinearMap.single_apply, Pi.single_eq_of_ne hau.symm,
      Pi.single_eq_of_ne haw.symm, sub_zero, map_zero, LinearMap.zero_apply]

/-- **The `p₂` candidate full block: the symmetric `va ↔ vb` candidate attains the full
`D(|V|−1)`-size family when `ρ` is not orthogonal to the supporting extensor**
(`lem:case-III-claim612-p2-placement`, KT eqs.~(6.19)/(6.30); Katoh–Tanigawa 2011 §6.4.1,
Phase 22e). The second of Claim~6.12's three candidates: split off at `v` along `vb` (rather than
`va`), the symmetric image of `p₁` under `a ↔ b`. It reuses the candidate-completion assembly
(`linearIndependent_sum_augment_candidateRow`) at the column op `Φ = columnOp hvb` for the edge `vb`
in place of `va`, and the row-space criterion (`linearIndependent_sumElim_candidateRow_iff`) at the
`vb`-hinge `e`: given the operated, `v`-pinned `vb`-block rows — the `D − 1` rows
`(rn ·∘ₗ Φ) ∘ₗ single v`, linearly independent (`hrnpin`) and spanning the whole hinge-row block
`r(p(e)) = (span C(e))^⊥` (`hspan`; `lem:case-II-placement-new-rows` supplies them at the
`vb`-hinge) — **if** the candidate functional `ρ` is not orthogonal to the supporting extensor,
`ρ(C(e)) ≠ 0`, **then** the full `p₂` family `Sum.elim (Sum.elim rn {hingeRow v b ρ}) ro` is
linearly independent. This is KT's `M₂` (eq.~(6.30)) full rank `⟺ r ∉ (span C(L'))^⊥` for the line
`L' ⊂ Π(b)` — the producer direction of the eq.~(6.42) row-space criterion the assembly consumes
through its operated `hnewpinaug`. The `λ_{(ab)j}` / `i^*` of the redundant-row decomposition are
unchanged between `M₁` and `M₂`: they live in `R(G_v^{ab}, q)`, common to both candidates and
independent of `p₁, p₂`. The bridge `hingeRow_comp_columnOp_comp_single` identifies the operated,
pinned candidate row with `ρ`, so the criterion's `ScrewSpace k`-level iff reads on the assembly's
`hnewpinaug` directly. -/
theorem linearIndependent_sum_p2_candidateRow (F : BodyHingeFramework k α β) (e : β)
    [DecidableEq α] {v b : α} (hvb : v ≠ b) {ιn ιo : Type*} [Finite ιn] [Finite ιo]
    {rn : ιn → Module.Dual ℝ (α → ScrewSpace k)} {ro : ιo → Module.Dual ℝ (α → ScrewSpace k)}
    {ρ : Module.Dual ℝ (ScrewSpace k)}
    (hold : ∀ (j : ιo) (x : ScrewSpace k),
      ro j (Function.update (0 : α → ScrewSpace k) v x) = 0)
    (holdindep : LinearIndependent ℝ ro)
    (hrnpin : LinearIndependent ℝ (fun i : ιn =>
      ((rn i).comp (columnOp (k := k) hvb).toLinearMap).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v)))
    (hspan : Submodule.span ℝ (Set.range (fun i : ιn =>
      ((rn i).comp (columnOp (k := k) hvb).toLinearMap).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v))) = F.hingeRowBlock e)
    (hr : ρ (F.supportExtensor e) ≠ 0) :
    LinearIndependent ℝ
      (Sum.elim (Sum.elim rn (fun _ : Unit => hingeRow (k := k) (α := α) v b ρ)) ro) := by
  refine linearIndependent_sum_augment_candidateRow hvb hold ?_ holdindep
  rw [hingeRow_comp_columnOp_comp_single hvb ρ]
  exact (linearIndependent_sumElim_candidateRow_iff F e hrnpin hspan ρ).2 hr

/-- **The `p₃` candidate full block: the third candidate split at the other degree-2 body `a`
along `ac` attains the full `D(|V|−1)`-size family when its candidate functional is not orthogonal
to the supporting extensor** (`lem:case-III-claim612-p3-placement`, KT eqs.~(6.31)–(6.41);
Katoh–Tanigawa 2011 §6.4.1, Phase 22e). The third of Claim~6.12's candidates, available because `a`
too is a degree-2 vertex: split off at `a` along `ac` (rather than splitting at `v`). The
isomorphism `G_v^{ab} ≅ G_a^{vc}` (`ρ : V∖{a} → V∖{v}`, `ρ(v) = a`, identity otherwise) is handled
**functionally**, not by an `ofNormals` graph swap: the candidate row is `hingeRow a c ρ_c` for the
candidate functional `ρ_c` on `ScrewSpace k`, and the producer is the *same* candidate-completion
assembly (`linearIndependent_sum_augment_candidateRow`) instantiated at the column op
`Φ = columnOp hac` for the edge `ac` in place of `va` — the split body is `a`, its operated endpoint
`c`. Its one hypothesis — the operated, `a`-pinned top-left block being full rank — is supplied by
the row-space criterion (`linearIndependent_sumElim_candidateRow_iff`) at the `ac`-hinge `e` once
the operated, pinned candidate row `(hingeRow a c ρ_c) ∘ Φ ∘ single a` is identified with `ρ_c`
itself (the column op makes it pure `a`-column with value `ρ_c(S_a)`,
`hingeRow_comp_columnOp_comp_single`), which holds iff `ρ_c(C(e)) ≠ 0`. This is KT's `M₃`
(eq.~(6.41)) full rank `⟺ r ∉ (span C(L''))^⊥` for the line `L'' ⊂ Π(c)` — the producer direction
of the eq.~(6.42) row-space criterion the assembly consumes through its operated `hnewpinaug`. The
link to the *same* common vector `r̂` the `M₁/M₂` criteria use is eq.~(6.44)
(`candidateRow_ac_eq_neg`): the `M₃` candidate functional `ρ_c` is `−r̂` restricted to the
`c`-endpoint, so the Claim-6.12 capstone (`lem:case-III-claim612`) reads its criterion off the
same `r̂`; N7 itself is the graph-free producer, so the recurring `ofNormals` defeq trap does not
bite. -/
theorem linearIndependent_sum_p3_candidateRow (F : BodyHingeFramework k α β) (e : β)
    [DecidableEq α] {a c : α} (hac : a ≠ c) {ιn ιo : Type*} [Finite ιn] [Finite ιo]
    {rn : ιn → Module.Dual ℝ (α → ScrewSpace k)} {ro : ιo → Module.Dual ℝ (α → ScrewSpace k)}
    {ρ : Module.Dual ℝ (ScrewSpace k)}
    (hold : ∀ (j : ιo) (x : ScrewSpace k),
      ro j (Function.update (0 : α → ScrewSpace k) a x) = 0)
    (holdindep : LinearIndependent ℝ ro)
    (hrnpin : LinearIndependent ℝ (fun i : ιn =>
      ((rn i).comp (columnOp (k := k) hac).toLinearMap).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a)))
    (hspan : Submodule.span ℝ (Set.range (fun i : ιn =>
      ((rn i).comp (columnOp (k := k) hac).toLinearMap).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a))) = F.hingeRowBlock e)
    (hr : ρ (F.supportExtensor e) ≠ 0) :
    LinearIndependent ℝ
      (Sum.elim (Sum.elim rn (fun _ : Unit => hingeRow (k := k) (α := α) a c ρ)) ro) := by
  refine linearIndependent_sum_augment_candidateRow hac hold ?_ holdindep
  rw [hingeRow_comp_columnOp_comp_single hac ρ]
  exact (linearIndependent_sumElim_candidateRow_iff F e hrnpin hspan ρ).2 hr

/-- **The `p₂` candidate selector: the `M₂` block is full rank when the common candidate vector is
not orthogonal to its supporting extensor** (`lem:case-III-claim612-p2-placement`, the selector
recast of the `p₂` producer; Katoh–Tanigawa 2011 §6.4.1, Phase 22g). The `case_III_claim612`
disjunction (`lem:case-III-claim612`) selects a candidate by the orthogonality test
`r̂(Cₘ) ≠ 0` on the *common* candidate vector `r̂`, where `Cₘ` is that block's supporting extensor
`C(p(e)) = F.supportExtensor e`. This packages `linearIndependent_sum_p2_candidateRow` into exactly
that selector shape `r̂(C(e)) ≠ 0 → LinearIndependent (Sum.elim (Sum.elim rn {hingeRow v b r̂}) ro)`
— the selector shape the `d = 3` `hsplit` producer's line-indexed candidate construction
(`case_III_hsplit_producer`) consumes — by taking the candidate functional `ρ := r̂` and the
supporting extensor `C := F.supportExtensor e`. Graph-free (abstract `F`); the producer's row-space
criterion already does all the work. -/
theorem linearIndependent_sum_p2_candidateRow_selector (F : BodyHingeFramework k α β) (e : β)
    [DecidableEq α] {v b : α} (hvb : v ≠ b) {ιn ιo : Type*} [Finite ιn] [Finite ιo]
    {rn : ιn → Module.Dual ℝ (α → ScrewSpace k)} {ro : ιo → Module.Dual ℝ (α → ScrewSpace k)}
    {r : Module.Dual ℝ (ScrewSpace k)}
    (hold : ∀ (j : ιo) (x : ScrewSpace k),
      ro j (Function.update (0 : α → ScrewSpace k) v x) = 0)
    (holdindep : LinearIndependent ℝ ro)
    (hrnpin : LinearIndependent ℝ (fun i : ιn =>
      ((rn i).comp (columnOp (k := k) hvb).toLinearMap).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v)))
    (hspan : Submodule.span ℝ (Set.range (fun i : ιn =>
      ((rn i).comp (columnOp (k := k) hvb).toLinearMap).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v))) = F.hingeRowBlock e) :
    r (F.supportExtensor e) ≠ 0 →
      LinearIndependent ℝ
        (Sum.elim (Sum.elim rn (fun _ : Unit => hingeRow (k := k) (α := α) v b r)) ro) :=
  fun hr => linearIndependent_sum_p2_candidateRow F e hvb hold holdindep hrnpin hspan hr

/-- **The `p₃` candidate selector: the `M₃` block is full rank when the common candidate vector is
not orthogonal to its supporting extensor** (`lem:case-III-claim612-p3-placement`, the selector
recast of the `p₃` producer; Katoh–Tanigawa 2011 §6.4.1, Phase 22g). The third candidate is split at
the other degree-2 body `a` along `ac`; its full-rank criterion is routed onto the *same* common
vector `r̂` by eq.~(6.44) (`candidateRow_ac_eq_neg`), so the selector test is again `r̂(C(e)) ≠ 0`
for the `ac`-hinge's supporting extensor `C = F.supportExtensor e`. This packages
`linearIndependent_sum_p3_candidateRow` into the `hsel₃` selector shape
`r̂(C(e)) ≠ 0 → LinearIndependent (Sum.elim (Sum.elim rn {hingeRow a c r̂}) ro)`
(`ρ := r̂`, `C := F.supportExtensor e`). Graph-free (abstract `F`). -/
theorem linearIndependent_sum_p3_candidateRow_selector (F : BodyHingeFramework k α β) (e : β)
    [DecidableEq α] {a c : α} (hac : a ≠ c) {ιn ιo : Type*} [Finite ιn] [Finite ιo]
    {rn : ιn → Module.Dual ℝ (α → ScrewSpace k)} {ro : ιo → Module.Dual ℝ (α → ScrewSpace k)}
    {r : Module.Dual ℝ (ScrewSpace k)}
    (hold : ∀ (j : ιo) (x : ScrewSpace k),
      ro j (Function.update (0 : α → ScrewSpace k) a x) = 0)
    (holdindep : LinearIndependent ℝ ro)
    (hrnpin : LinearIndependent ℝ (fun i : ιn =>
      ((rn i).comp (columnOp (k := k) hac).toLinearMap).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a)))
    (hspan : Submodule.span ℝ (Set.range (fun i : ιn =>
      ((rn i).comp (columnOp (k := k) hac).toLinearMap).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a))) = F.hingeRowBlock e) :
    r (F.supportExtensor e) ≠ 0 →
      LinearIndependent ℝ
        (Sum.elim (Sum.elim rn (fun _ : Unit => hingeRow (k := k) (α := α) a c r)) ro) :=
  fun hr => linearIndependent_sum_p3_candidateRow F e hac hold holdindep hrnpin hspan hr

/-- **The `M₁` candidate selector: the un-symmetrized `va`-split block is full rank when the common
candidate vector is not orthogonal to its supporting extensor** (`lem:case-III-candidate-row`, the
selector recast of the `M₁` candidate-completion assembly; Katoh–Tanigawa 2011 §6.4.1, Phase 22g).
The first of Claim~6.12's three candidates is `p₁` itself — split off at `v` along the *original*
edge `va` — so it has no separate producer: it is the candidate-completion assembly
(`linearIndependent_sum_augment_candidateRow`) applied directly at the column op `Φ = columnOp hva`
for the edge `va`, with the operated top-left block `hnewpinaug` supplied by the row-space criterion
(`linearIndependent_sumElim_candidateRow_iff`) at the `va`-hinge `e`. This packages it into the same
`hsel₁` selector shape
`r̂(C(e)) ≠ 0 → LinearIndependent (Sum.elim (Sum.elim rn {hingeRow v a r̂}) ro)`
that the `d = 3` `hsplit` producer's line-indexed candidate construction
(`case_III_hsplit_producer`) consumes, matching the `hsel₂`/`hsel₃` recasts. Unlike those two —
which delegate the `hnewpinaug`
discharge to the `p₂`/`p₃` producers — this one builds the operated block inline (there is no `M₁`
producer to delegate to): once the operated, pinned candidate row `(hingeRow v a r̂) ∘ Φ ∘ single v`
is identified with `r̂` (`hingeRow_comp_columnOp_comp_single`), the row-space criterion's
`ScrewSpace k`-level iff reads on `hnewpinaug` directly. Graph-free (abstract `F`). -/
theorem linearIndependent_sum_augment_candidateRow_selector (F : BodyHingeFramework k α β) (e : β)
    [DecidableEq α] {v a : α} (hva : v ≠ a) {ιn ιo : Type*} [Finite ιn] [Finite ιo]
    {rn : ιn → Module.Dual ℝ (α → ScrewSpace k)} {ro : ιo → Module.Dual ℝ (α → ScrewSpace k)}
    {r : Module.Dual ℝ (ScrewSpace k)}
    (hold : ∀ (j : ιo) (x : ScrewSpace k),
      ro j (Function.update (0 : α → ScrewSpace k) v x) = 0)
    (holdindep : LinearIndependent ℝ ro)
    (hrnpin : LinearIndependent ℝ (fun i : ιn =>
      ((rn i).comp (columnOp (k := k) hva).toLinearMap).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v)))
    (hspan : Submodule.span ℝ (Set.range (fun i : ιn =>
      ((rn i).comp (columnOp (k := k) hva).toLinearMap).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v))) = F.hingeRowBlock e) :
    r (F.supportExtensor e) ≠ 0 →
      LinearIndependent ℝ
        (Sum.elim (Sum.elim rn (fun _ : Unit => hingeRow (k := k) (α := α) v a r)) ro) :=
  fun hr => linearIndependent_sum_augment_candidateRow hva hold
    (by rw [hingeRow_comp_columnOp_comp_single hva r]
        exact (linearIndependent_sumElim_candidateRow_iff F e hrnpin hspan r).2 hr)
    holdindep

/-- **The common vector `r̂` of the `D`-candidate disjunction is nonzero**
(`lem:case-III-claim612-r-nonzero`, KT eq.~(6.42); Katoh–Tanigawa 2011 §6.4.1, Phase 22e).
The candidate row shared by all three
blocks `M₁/M₂/M₃` of Claim~6.12 is `r̂ := ∑_j λ_{(ab)j} r_j(q(ab))`, where the `r_j` are the
`D − 1` linearly independent rows of the `ab`-hinge block (`lem:case-II-placement-new-rows`) and
the coefficients `λ_{(ab)j}` come from the redundant-`ab`-row decomposition of eqs.~(6.24)/(6.25)
with the redundant index's coefficient pinned to `λ_{(ab)i^*} = 1`
(`exists_redundant_panelRow_ab_decomposition`). Since `r̂` is a linear combination of the
linearly independent `r_j` carrying the unit (hence nonzero) coefficient `1` on the member `i^*`,
it is nonzero (`linearIndependent_sum_smul_ne_zero`). This is the `r ≠ 0` leaf the Claim-6.12
capstone (`lem:case-III-claim612`) contradicts after the three blocks' joint dependence forces
`r̂ = 0`. -/
theorem candidateRow_ne_zero {ι : Type*} [Fintype ι] {r : ι → Module.Dual ℝ (ScrewSpace k)}
    (hr : LinearIndependent ℝ r) {lam : ι → ℝ} {i : ι} (hlam : lam i = 1) :
    ∑ j, lam j • r j ≠ 0 :=
  linearIndependent_sum_smul_ne_zero hr (i := i) (hlam ▸ one_ne_zero)

/-- **Eq.~(6.44): the `M₃` candidate row equals `−r̂`, routing the third candidate onto the same
common vector** (`lem:case-III-claim612-eq644`, KT eq.~(6.44); Katoh–Tanigawa 2011 §6.4.1,
Phase 22e). The `a`-column block of the eq.~(6.24) vanishing combination `g` is `0`
(`exists_redundant_panelRow_ab_decomposition_acolumn_zero`, eq.~(6.43)): `g.comp (single a) = 0`.
KT's eq.~(6.44) is what that restriction *says* once the combination is regrouped by which edge
each term sits on. In `G_v^{ab}` body `a` is a **degree-2** vertex --- only the `ab`- and `ac`-edges
are incident to it --- so by the column-restriction leaves (`hingeRow_comp_single_tail` /
`hingeRow_comp_single_off`) the only terms of `g` surviving in body `a`'s screw column are the
`ab`-sum, whose `a`-column restriction is the common candidate row `r̂ := ∑_j λ_{(ab)j} r_j(q(ab))`,
and the `ac`-sum, with restriction `rAC := ∑_j λ_{(ac)j} r_j(q(ac))`. Hence
`0 = g.comp (single a) = r̂ + rAC`, i.e.\ KT's eq.~(6.44)
\[ r̂ \;=\; -\,\mathrm{rAC} \;=\; -\sum_j λ_{(ac)j}\, r_j(q(ac)). \]
The `M₃` candidate's full-rank criterion is `rAC ∉ (\operatorname{span} C(L''))^\perp`
(`lem:case-III-claim612-p3-placement`); eq.~(6.44) rewrites it as `r̂ ⊥ C(L'')` --- the same common
vector `r̂` the `M₁/M₂` criteria use, which is exactly what lets the Claim-6.12 capstone
(`lem:case-III-claim612`) force the *single* `r̂` orthogonal to all of `C(L), C(L'), C(L'')` and so
to a spanning set, contradicting `r̂ ≠ 0`.

Stated abstractly (graph-free, matching the candidate-completion chain): the `ab`-sum and `ac`-sum
are explicit `hingeRow`-sums out of the common tail body `a` (into the distinct bodies `b`, `c`),
and `grest` is the remaining edges' contribution, which the degree-2-at-`a` fact (`hrest`: every
such edge is incident to neither endpoint at `a`) makes vanish on `a`'s column. The conclusion is
the `M₃` row `rAC := ∑_j λac_j • rac_j` equal to `-r̂` with `r̂ := ∑_j λab_j • rab_j`. The `ab`/`ac`
column restrictions are computed by `hingeRow_comp_single_tail`; the `grest` one by
`hingeRow_comp_single_off`. -/
theorem candidateRow_ac_eq_neg [DecidableEq α] {ιab ιac : Type*} [Fintype ιab] [Fintype ιac]
    {a b c : α} (hab : a ≠ b) (hac : a ≠ c)
    (lamAB : ιab → ℝ) (rab : ιab → Module.Dual ℝ (ScrewSpace k))
    (lamAC : ιac → ℝ) (rac : ιac → Module.Dual ℝ (ScrewSpace k))
    (grest : Module.Dual ℝ (α → ScrewSpace k))
    (hcol : ((∑ j, lamAB j • hingeRow (k := k) (α := α) a b (rab j))
        + (∑ j, lamAC j • hingeRow (k := k) (α := α) a c (rac j)) + grest).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a) = 0)
    (hrest : grest.comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a) = 0) :
    ∑ j, lamAC j • rac j = -∑ j, lamAB j • rab j := by
  refine eq_neg_of_add_eq_zero_right ?_
  -- Strip the `grest` term (`hrest`) and read the equation column-wise: at each `x : ScrewSpace k`
  -- the `ab`-sum and `ac`-sum restrict to their block-functional sums
  -- (`hingeRow_comp_single_tail`), the `grest` term vanishes (`hrest`), so the eq. (6.43) `0`
  -- reads `r̂ + rAC = 0` at `x`.
  rw [LinearMap.add_comp, LinearMap.add_comp, hrest, add_zero] at hcol
  refine LinearMap.ext fun x => ?_
  have hx := LinearMap.congr_fun hcol x
  have e1 : ∀ j, (hingeRow (k := k) (α := α) a b (rab j))
      (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a x) = rab j x :=
    fun j => LinearMap.congr_fun (hingeRow_comp_single_tail hab (rab j)) x
  have e2 : ∀ j, (hingeRow (k := k) (α := α) a c (rac j))
      (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a x) = rac j x :=
    fun j => LinearMap.congr_fun (hingeRow_comp_single_tail hac (rac j)) x
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, e1, e2, LinearMap.zero_apply] using hx

/-- **Claim 6.12 — for some line choice, the candidate block is full rank**
(`lem:case-III-claim612`, Katoh–Tanigawa 2011 §6.4.1, Claim 6.12, eqs. (6.30)–(6.45); Phase 22g).
The capstone of the candidate-selection argument at `d = 3`, stated as the **existential** it
actually is: KT's lines `L ⊂ Π(u)` are *freely chosen* (eqs. (6.12)/(6.42)), so the claim is that
*for some* choice the candidate's top-left `D × D` block is full rank — equivalently (the row-space
criterion `linearIndependent_sumElim_candidateRow_iff` at the candidate's hinge) the common
candidate row `r̂ := ∑_j λ_{(ab)j} r_j(q(ab))` is **not** orthogonal to that block's supporting
extensor. Since a candidate's hinge support is the panel-meet of a line `L` (PanelHinge, `rfl`) and
the panel-meet of a line through two of the four points is exactly one of their six joins
`pᵢ ∨ pⱼ = omitTwoExtensor (homogenize ∘ p)`, the existential is stated over those **six joins**:
`∃ q, r̂(pᵢ ∨ pⱼ) ≠ 0`.

The argument is a clean contrapositive of the existential. If `r̂` annihilated *every* one of the
six joins — KT's union-(6.45) "for *every* choice of lines `L ⊂ Π(a)`, `L' ⊂ Π(b)`, `L'' ⊂ Π(c)`"
— then since those six joins of four linearly-independent homogeneous vectors **span** `ScrewSpace 2
= ⋀²ℝ⁴` (`span_omitTwoExtensor_eq_top`, N1, via Lemma 2.1), `r̂` would annihilate their
span and so be `0` (`eq_zero_of_annihilates_span_top`, N2), contradicting `r̂ ≠ 0` (N5). The
annihilation hypothesis is *not* a carried premise: it is precisely the internal `by_contra`
negation `∀ q, r̂(join q) = 0`. The earlier three-fixed-`Cᵢ` disjunction conclusion
(`r̂(C₁) ≠ 0 ∨ r̂(C₂) ≠ 0 ∨ r̂(C₃) ≠ 0` at three *hardcoded* lines) was *mathematically
undischargeable* — three `2`-extensors span ≤ 3 of the 6 dimensions of `⋀²ℝ⁴`, so `r̂ ⊥ C₁,C₂,C₃`
cannot force `r̂ = 0`; only the full line sweep (Lemma 2.1) does. The producer
(`case_III_hsplit_producer`) consumes the existential by building its candidate placement so
its hinge line *is* the witness join's line `L = p̄ᵢ p̄ⱼ`. The points enter at the
**homogeneous-vector**
layer (bare `LinearIndependent ℝ pbar`, fed by `exists_homogeneousIncidence_of_normals`); no affine
de-homogenization is needed (`notes/Phase22-realization-design.md` §1.42, R1-affine). -/
theorem case_III_claim612
    {r : Module.Dual ℝ (ScrewSpace 2)} (hr : r ≠ 0)
    {pbar : Fin 4 → Fin 4 → ℝ} (hp : LinearIndependent ℝ pbar) :
    ∃ q : {q : Fin 4 × Fin 4 // q.1 < q.2},
      r ⟨omitTwoExtensor pbar (ne_of_lt q.2),
        extensor_mem_exteriorPower _⟩ ≠ 0 := by
  -- Contrapositive of the existential: if `r̂` annihilated *every* one of the six panel-support
  -- joins of the four affinely-independent points, it would annihilate their span `= ⋀²ℝ⁴`
  -- (`span_omitTwoExtensor_eq_top`, N1, via Lemma 2.1) and so be `0`
  -- (`eq_zero_of_annihilates_span_top`, N2), contradicting `r̂ ≠ 0` (N5). The annihilation
  -- `∀ q, r̂(join q) = 0` is the internal `by_contra` negation — KT's union-(6.45) "for *every*
  -- choice of lines" hypothesis — not a premise carried in.
  by_contra h
  push Not at h
  exact hr (eq_zero_of_annihilates_span_top (span_omitTwoExtensor_eq_top hp)
    (by rintro x ⟨q, rfl⟩; exact h q))

/-- **The six-join `hduality` witness assembly from the panel-incidence data** (`lem:case-III`,
the N3a → `hduality` glue of the `d = 3` `hsplit` producer; Katoh–Tanigawa 2011 §6.4.1 eqs.
(6.42)–(6.45), Phase 22g). This produces the per-join witness function `case_III_claim612`'s
`hduality` hypothesis quantifies over, from the N3a panel-incidence data
(`exists_affineIndependent_panel_incidence`: three panel normals `n : Fin 3 → ℝ⁴`,
`LinearIndependent`, and four affinely-independent points `p : Fin 4 → ℝ³` with the
triple-intersection incidence tabulation) and the **failed-block annihilation** hypothesis `hann`:
`r` annihilates the panel-meet `C(L) = complementIso (n u ∧ m)` of *every* line `L ⊂ Π(u)` — i.e.
of panel `Π(u)` (the normal `n u`) with any second hyperplane `m` independent from `n u` (KT's "for
any choice of lines `L ⊂ Π(a)`, `L' ⊂ Π(b)`, `L'' ⊂ Π(c)`", eqs. (6.42)–(6.44), what the failed
contrapositive supplies on each of the three failed candidate blocks).

For each of the six joins `q`, the kept pair `(c, d)` (the complement of the omitted pair,
`omitTwoExtensor_homogenize_eq_extensor_kept`) determines a *common* panel `Π(u)` the join line
`p̄_c p̄_d` lies in (each endpoint pair of the four points shares ≥ 1 panel, from the incidence
tabulation): the three joins through `p 0` share two panels (use the panel normal `n u` and a second
panel normal), the three "opposite" joins share one panel (use `n u` and a *constructed* second
normal `n'` through the line, `exists_independent_perp_pair`). Either way the brick's pair
`{n_u, n'}` is independent with both kept points orthogonal to both, and `hann` supplies the meet
annihilation, completing the witness. Graph-free (pure `Fin 4` panel geometry); the `r`/`Cᵢ`/`p`
data is supplied by the producer at instantiation. -/
theorem exists_hduality_witness_of_panel_incidence
    {r : Module.Dual ℝ (ScrewSpace 2)}
    {n : Fin 3 → Fin 4 → ℝ} (hn : LinearIndependent ℝ n)
    {p : Fin 4 → Fin 3 → ℝ}
    (h0 : ∀ u, homogenize (p 0) ⬝ᵥ n u = 0)
    (h1 : homogenize (p 1) ⬝ᵥ n 0 = 0 ∧ homogenize (p 1) ⬝ᵥ n 1 = 0)
    (h2 : homogenize (p 2) ⬝ᵥ n 1 = 0 ∧ homogenize (p 2) ⬝ᵥ n 2 = 0)
    (h3 : homogenize (p 3) ⬝ᵥ n 2 = 0 ∧ homogenize (p 3) ⬝ᵥ n 0 = 0)
    (hann : ∀ (u : Fin 3) (m : Fin 4 → ℝ), LinearIndependent ℝ ![n u, m] →
      r (complementIso (k := 2) (j := 2) (by omega)
        ⟨extensor ![n u, m], extensor_mem_exteriorPower _⟩) = 0) :
    ∀ q : {q : Fin 4 × Fin 4 // q.1 < q.2},
      ∃ (n_u n' pi pj : Fin 4 → ℝ), LinearIndependent ℝ ![n_u, n'] ∧
        pi ⬝ᵥ n_u = 0 ∧ pi ⬝ᵥ n' = 0 ∧ pj ⬝ᵥ n_u = 0 ∧ pj ⬝ᵥ n' = 0 ∧
        omitTwoExtensor (fun i => homogenize (p i)) (ne_of_lt q.2) = extensor ![pi, pj] ∧
        r (complementIso (k := 2) (j := 2) (by omega)
            ⟨extensor ![n_u, n'], extensor_mem_exteriorPower _⟩) = 0 := by
  -- Two N3a panel normals `n a, n b` are independent (subfamily of the independent `n`).
  have hpair : ∀ a b : Fin 3, a ≠ b → LinearIndependent ℝ ![n a, n b] := by
    intro a b hab
    have := hn.comp ![a, b] (by intro x y hxy; fin_cases x <;> fin_cases y <;> simp_all)
    rwa [show (n ∘ ![a, b]) = ![n a, n b] from by ext x; fin_cases x <;> rfl] at this
  -- **Two-panel join builder** (the three joins through `p 0`): the kept points `e₁ = homogenize
  -- (p k₁)`, `e₂ = homogenize (p k₂)` both lie on panels `Π(u)` *and* `Π(w)` (two N3a normals), and
  -- the join `omitTwoExtensor … = extensor ![e₁, e₂]`; `hann u (n w)` supplies the meet annihil.
  have htwo : ∀ (q : {q : Fin 4 × Fin 4 // q.1 < q.2}) (u w : Fin 3) (e₁ e₂ : Fin 4 → ℝ),
      u ≠ w → e₁ ⬝ᵥ n u = 0 → e₁ ⬝ᵥ n w = 0 → e₂ ⬝ᵥ n u = 0 → e₂ ⬝ᵥ n w = 0 →
      omitTwoExtensor (fun i => homogenize (p i)) (ne_of_lt q.2) = extensor ![e₁, e₂] →
      ∃ (n_u n' pi pj : Fin 4 → ℝ), LinearIndependent ℝ ![n_u, n'] ∧
        pi ⬝ᵥ n_u = 0 ∧ pi ⬝ᵥ n' = 0 ∧ pj ⬝ᵥ n_u = 0 ∧ pj ⬝ᵥ n' = 0 ∧
        omitTwoExtensor (fun i => homogenize (p i)) (ne_of_lt q.2) = extensor ![pi, pj] ∧
        r (complementIso (k := 2) (j := 2) (by omega)
            ⟨extensor ![n_u, n'], extensor_mem_exteriorPower _⟩) = 0 :=
    fun _ u w e₁ e₂ huw h1u h1w h2u h2w hkept =>
      ⟨n u, n w, e₁, e₂, hpair u w huw, h1u, h1w, h2u, h2w, hkept, hann u (n w) (hpair u w huw)⟩
  -- **One-panel join builder** (the three "opposite" joins, single shared panel `Π(u)`): both kept
  -- points lie on `Π(u)` (`e₁, e₂ ⊥ n u`); `exists_independent_perp_pair` builds a second
  -- hyperplane `n'` through the line, and `hann u n'` supplies the meet annihilation.
  have hone : ∀ (q : {q : Fin 4 × Fin 4 // q.1 < q.2}) (u : Fin 3) (e₁ e₂ : Fin 4 → ℝ),
      e₁ ⬝ᵥ n u = 0 → e₂ ⬝ᵥ n u = 0 →
      omitTwoExtensor (fun i => homogenize (p i)) (ne_of_lt q.2) = extensor ![e₁, e₂] →
      ∃ (n_u n' pi pj : Fin 4 → ℝ), LinearIndependent ℝ ![n_u, n'] ∧
        pi ⬝ᵥ n_u = 0 ∧ pi ⬝ᵥ n' = 0 ∧ pj ⬝ᵥ n_u = 0 ∧ pj ⬝ᵥ n' = 0 ∧
        omitTwoExtensor (fun i => homogenize (p i)) (ne_of_lt q.2) = extensor ![pi, pj] ∧
        r (complementIso (k := 2) (j := 2) (by omega)
            ⟨extensor ![n_u, n'], extensor_mem_exteriorPower _⟩) = 0 :=
    fun _ u e₁ e₂ h1u h2u hkept => by
      obtain ⟨n', hpair', h1', h2'⟩ :=
        exists_independent_perp_pair e₁ e₂ (n u) h1u h2u (hn.ne_zero u)
      exact ⟨n u, n', e₁, e₂, hpair', h1u, h1', h2u, h2', hkept, hann u n' hpair'⟩
  -- The per-join kept-points identity (concrete `c, d` per join), from the general tabulation.
  have hkept : ∀ (q : {q : Fin 4 × Fin 4 // q.1 < q.2}) (c d : Fin 4), c < d →
      c ≠ q.1.1 → c ≠ q.1.2 → d ≠ q.1.1 → d ≠ q.1.2 →
      omitTwoExtensor (fun i => homogenize (p i)) (ne_of_lt q.2)
        = extensor ![homogenize (p c), homogenize (p d)] := by
    intro q c d hcd hc1 hc2 hd1 hd2
    obtain ⟨c', d', hcd', hc1', hc2', hd1', hd2', heq⟩ :=
      omitTwoExtensor_homogenize_eq_extensor_kept p q
    -- `c, d` and `c', d'` are both the increasing complement of `{q.1, q.2}`, hence equal.
    obtain rfl : c' = c := by omega
    obtain rfl : d' = d := by omega
    exact heq
  intro q
  obtain ⟨h1a, h1b⟩ := h1; obtain ⟨h2a, h2b⟩ := h2; obtain ⟨h3a, h3b⟩ := h3
  -- For each of the six joins, the kept points (`hkept`) come off the increasing complement of the
  -- omitted pair, and the common panel(s) from the incidence tabulation: `(0,1)↦keep(2,3)`, `n2`
  -- (one panel); `(0,2)↦keep(1,3)`, `n0`; `(0,3)↦keep(1,2)`, `n1`; `(1,2)↦keep(0,3)`, `{n0,n2}`
  -- (two); `(1,3)↦keep(0,2)`, `{n1,n2}`; `(2,3)↦keep(0,1)`, `{n0,n1}`. The builders take `q`
  -- explicitly so the heavy `omitTwoExtensor`/`complementIso` carrier need not be `whnf`'d to infer
  -- it (TACTICS-QUIRKS §38).
  fin_cases q
  · exact hone ⟨(0, 1), by decide⟩ 2 _ _ h2b h3a
      (hkept ⟨(0, 1), by decide⟩ 2 3 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact hone ⟨(0, 2), by decide⟩ 0 _ _ h1a h3b
      (hkept ⟨(0, 2), by decide⟩ 1 3 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact hone ⟨(0, 3), by decide⟩ 1 _ _ h1b h2a
      (hkept ⟨(0, 3), by decide⟩ 1 2 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact htwo ⟨(1, 2), by decide⟩ 0 2 _ _ (by decide) (h0 0) (h0 2) h3b h3a
      (hkept ⟨(1, 2), by decide⟩ 0 3 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact htwo ⟨(1, 3), by decide⟩ 1 2 _ _ (by decide) (h0 1) (h0 2) h2a h2b
      (hkept ⟨(1, 3), by decide⟩ 0 2 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact htwo ⟨(2, 3), by decide⟩ 0 1 _ _ (by decide) (h0 0) (h0 1) h1a h1b
      (hkept ⟨(2, 3), by decide⟩ 0 1 (by decide) (by decide) (by decide) (by decide) (by decide))

/-- **The witness panel-meet a nonzero screw functional fails to annihilate**
(`lem:case-III-claim612-line-in-panel-union`, the Claim 6.12 → candidate-row glue of the `d = 3`
`hsplit` producer's `n_a`/`n_b` arms, KT eq. (6.45); Phase 22h). The forward (existence) dual of
`extensor_join_eq_zero_of_complementIso_eq_zero_dotProduct`: rather than transferring annihilation,
it produces, from a **nonzero** functional `r` and the homogeneous incidence data of four
affinely-independent points `pbar` against three independent panel normals `n`, a
**discriminating index** `u : Fin 3` and a line `L` in panel `Π(n u)` whose **panel-meet**
`C(L) = complementIso (n u ∧ n')` the functional `r` does *not* annihilate.

This is the contrapositive of KT's Claim 6.12 union argument made constructive: Claim 6.12
(`case_III_claim612`) supplies a witness join `pᵢ ∨ pⱼ = omitTwoExtensor pbar (ne_of_lt q.2)` with
`r(pᵢ ∨ pⱼ) ≠ 0`; the per-join line data (`exists_line_data_of_homogeneousIncidence`) exhibits the
join line `L = pᵢ pⱼ` inside a panel `Π(n u)` with a second hyperplane `n'`; and the per-line
duality (`extensor_join_eq_zero_of_complementIso_eq_zero_dotProduct`, contrapositive) forces
`r(C(L)) ≠ 0` from `r(pᵢ ∨ pⱼ) ≠ 0`. The resulting `u`, `{n u, n'}` with
`r(complementIso (n u ∧ n')) ≠ 0` is the nonzero-candidate-row input the producer's eq. (6.12)
candidate placement consumes (its hinge line is built to be exactly this witness line `L`); the
returned `u : Fin 3` is the M₁/M₂/M₃ dispatch index the `hcand`-discharge reads (§1.50(a)).
Graph-free (pure `Fin 4` / `⋀²ℝ⁴` geometry, off the `ofNormals` `whnf` trap, TACTICS-QUIRKS §38);
the `r`/`pbar`/`n` data is supplied by the producer at instantiation. -/
theorem exists_complementIso_ne_zero_of_homogeneousIncidence
    {r : Module.Dual ℝ (ScrewSpace 2)} (hr : r ≠ 0)
    {pbar : Fin 4 → Fin 4 → ℝ} (hp : LinearIndependent ℝ pbar)
    {n : Fin 3 → Fin 4 → ℝ} (hn : LinearIndependent ℝ n)
    (h0 : ∀ u, pbar 0 ⬝ᵥ n u = 0)
    (h1 : pbar 1 ⬝ᵥ n 0 = 0 ∧ pbar 1 ⬝ᵥ n 1 = 0)
    (h2 : pbar 2 ⬝ᵥ n 1 = 0 ∧ pbar 2 ⬝ᵥ n 2 = 0)
    (h3 : pbar 3 ⬝ᵥ n 2 = 0 ∧ pbar 3 ⬝ᵥ n 0 = 0) :
    ∃ (u : Fin 3) (n' : Fin 4 → ℝ), LinearIndependent ℝ ![n u, n'] ∧
      r (complementIso (k := 2) (j := 2) (by omega)
        ⟨extensor ![n u, n'], extensor_mem_exteriorPower _⟩) ≠ 0 := by
  -- Claim 6.12: a witness join `pᵢ ∨ pⱼ = omitTwoExtensor pbar (ne_of_lt q.2)` with `r(·) ≠ 0`.
  obtain ⟨q, hq⟩ := case_III_claim612 hr hp
  -- The per-join line data: the join line `L = pᵢ pⱼ ⊂ Π(n u)` for a discriminating index
  -- `u : Fin 3` (the witness panel normal is the real split-leg normal `n u`), and a second
  -- hyperplane `n'`.
  obtain ⟨u, n', pi, pj, hpair, hi_u, hi_u', hj_u, hj_u', hkept⟩ :=
    exists_line_data_of_homogeneousIncidence hn h0 h1 h2 h3 q
  refine ⟨u, n', hpair, fun hC => hq ?_⟩
  -- Contrapositive of the per-line duality: `r(C(L)) = 0` forces `r(pᵢ ∨ pⱼ) = 0`, i.e.
  -- `r` annihilates the witness join — contradicting `hq`.
  rw [show (⟨omitTwoExtensor pbar (ne_of_lt q.2), extensor_mem_exteriorPower _⟩ :
        ⋀[ℝ]^2 (Fin 4 → ℝ)) = ⟨extensor ![pi, pj], extensor_mem_exteriorPower _⟩ from
      Subtype.ext hkept]
  exact extensor_join_eq_zero_of_complementIso_eq_zero_dotProduct (n u) n' pi pj hpair
    hi_u hi_u' hj_u hj_u' r hC

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

/-! ## Vertex-disjoint block-rank addition (the cut-edge brick)

The block-rank inequality for a cut-partitioned body-hinge framework: when the edge set
decomposes into two side groups (each internal to one of two disjoint vertex sets `V₁` and
`V(G) ∖ V₁`) and at most one crossing edge, the rigidity-row span has dimension at least
the sum of the two side-spans plus the cut block's dimension.  This is the core of KT's
Lemma 6.1 block-triangular rank-addition argument (Katoh–Tanigawa 2011 §6.1, p. 672).

The proof key: the V₁- and V₂-side spans read disjoint coordinate blocks of the screw
assignment, making them mutually disjoint submodules; the cut-block span is disjoint from
their join via the flow-sum functional (summing `φ(update 0 w x)` over `w ∈ V₁` annihilates
both side spans but returns the cut-block functional, so an element in the intersection must
be zero). -/

section CutEdgeBrick

-- `open Classical` is needed for `Decidable (a ∈ V₁)` in `zeroOutsideV₁`'s if/else and
-- for `DecidableEq α` in `flowSum`'s `Pi.single`. The linter is disabled for this command.
set_option linter.style.openClassical false
open Classical
open scoped Graph

variable {α β : Type*} {k : ℕ}

/-- **The V₁-projection map**: zeroes the screw assignment outside `V₁`.  Used to separate
the V₁-side span from the V₂-side span: side-1 rows commute with the projection (they read
only V₁ bodies), side-2 rows vanish under it (they read only V₂ bodies). -/
private noncomputable def zeroOutsideV₁ (V₁ : Set α) :
    (α → ScrewSpace k) →ₗ[ℝ] (α → ScrewSpace k) where
  toFun S a := if a ∈ V₁ then S a else 0
  map_add' S T := by ext a; simp [ite_add_ite]
  map_smul' c S := by ext a; simp [smul_ite]

@[simp]
private lemma zeroOutsideV₁_mem (V₁ : Set α) (S : α → ScrewSpace k) {a : α} (ha : a ∈ V₁) :
    zeroOutsideV₁ V₁ S a = S a := if_pos ha

@[simp]
private lemma zeroOutsideV₁_not_mem (V₁ : Set α) (S : α → ScrewSpace k) {a : α} (ha : a ∉ V₁) :
    zeroOutsideV₁ V₁ S a = 0 := if_neg ha

/-- A hinge row with both endpoints in `V₁` commutes with the V₁-projection: the row value
is unchanged when the screw assignment is zeroed outside `V₁`. -/
private lemma hingeRow_comp_zeroOutsideV₁ (V₁ : Set α) {u v : α} (hu : u ∈ V₁) (hv : v ∈ V₁)
    (r : Module.Dual ℝ (ScrewSpace k)) :
    (hingeRow (k := k) (α := α) u v r).comp (zeroOutsideV₁ V₁) = hingeRow u v r := by
  ext S
  simp [hingeRow_apply, zeroOutsideV₁_mem V₁ S hu, zeroOutsideV₁_mem V₁ S hv]

/-- A hinge row with both endpoints outside `V₁` vanishes at any V₁-projection output. -/
private lemma hingeRow_comp_zeroOutsideV₁_of_not_mem (V₁ : Set α) {u v : α}
    (hu : u ∉ V₁) (hv : v ∉ V₁) (r : Module.Dual ℝ (ScrewSpace k)) :
    (hingeRow (k := k) (α := α) u v r).comp (zeroOutsideV₁ V₁) = 0 := by
  ext S
  simp [hingeRow_apply, zeroOutsideV₁_not_mem V₁ S hu, zeroOutsideV₁_not_mem V₁ S hv]

/-- Every element of the V₁-side rigidity-row span commutes with the V₁-projection: for
`φ ∈ span(F[V₁].rigidityRows)`, `φ(zeroOutsideV₁ S) = φ(S)` for all `S`. -/
private lemma mem_span_rigidityRows_induce_comp_zeroOutsideV₁ {F : BodyHingeFramework k α β}
    {V₁ : Set α} {φ : Module.Dual ℝ (α → ScrewSpace k)}
    (hφ : φ ∈ Submodule.span ℝ (⟨F.graph.induce V₁, F.supportExtensor⟩ :
      BodyHingeFramework k α β).rigidityRows) :
    φ.comp (zeroOutsideV₁ V₁) = φ := by
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨e, u, v, he, r, _, rfl⟩ := hφ
    simp only [Graph.induce_isLink] at he
    exact hingeRow_comp_zeroOutsideV₁ V₁ he.2.1 he.2.2 r
  | zero => ext; simp
  | add x y _ _ hx hy =>
    rw [LinearMap.add_comp, hx, hy]
  | smul a x _ hx =>
    rw [LinearMap.smul_comp, hx]

/-- Every element of the V₂-side rigidity-row span vanishes when composed with the
V₁-projection: for `φ ∈ span(F[V₂].rigidityRows)`, `φ ∘ zeroOutsideV₁ = 0`. -/
private lemma mem_span_rigidityRows_induce_comp_zeroOutsideV₁_eq_zero
    {F : BodyHingeFramework k α β} {V₁ : Set α} {φ : Module.Dual ℝ (α → ScrewSpace k)}
    (hφ : φ ∈ Submodule.span ℝ (⟨F.graph.induce (V(F.graph) \ V₁), F.supportExtensor⟩ :
      BodyHingeFramework k α β).rigidityRows) :
    φ.comp (zeroOutsideV₁ V₁) = 0 := by
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨e, u, v, he, r, _, rfl⟩ := hφ
    simp only [Graph.induce_isLink, Set.mem_diff] at he
    exact hingeRow_comp_zeroOutsideV₁_of_not_mem V₁ he.2.1.2 he.2.2.2 r
  | zero => ext; simp
  | add x y _ _ hx hy =>
    rw [LinearMap.add_comp, hx, hy, add_zero]
  | smul a x _ hx =>
    rw [LinearMap.smul_comp, hx, smul_zero]

/-- **The two side spans are disjoint**: `span(F[V₁].rigidityRows) ⊓ span(F[V₂].rigidityRows) = ⊥`.
The V₁-projection commutes with span(F[V₁]) (side-1 rows read only V₁) and annihilates
span(F[V₂]) (side-2 rows read only V₂ = V(G) ∖ V₁); any element in the intersection is both
fixed by and annihilated by the projection, hence zero. -/
theorem span_rigidityRows_induce_inf_eq_bot {F : BodyHingeFramework k α β} (V₁ : Set α) :
    Submodule.span ℝ (⟨F.graph.induce V₁, F.supportExtensor⟩ :
        BodyHingeFramework k α β).rigidityRows ⊓
    Submodule.span ℝ (⟨F.graph.induce (V(F.graph) \ V₁), F.supportExtensor⟩ :
        BodyHingeFramework k α β).rigidityRows = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro φ ⟨h1, h2⟩
  -- From h1: φ = φ.comp (zeroOutsideV₁ V₁) (V₁-side rows commute with projection)
  have hfix : φ.comp (zeroOutsideV₁ V₁) = φ :=
    mem_span_rigidityRows_induce_comp_zeroOutsideV₁ h1
  -- From h2: φ.comp (zeroOutsideV₁ V₁) = 0 (V₂-side rows vanish under projection)
  have hzero : φ.comp (zeroOutsideV₁ V₁) = 0 :=
    mem_span_rigidityRows_induce_comp_zeroOutsideV₁_eq_zero h2
  exact hfix.symm.trans hzero

/-- The flow-sum linear map `Φ(φ) = ∑_{w ∈ V₁} φ(update 0 w ·)`: a functional from
`Module.Dual ℝ (α → ScrewSpace k)` to `Module.Dual ℝ (ScrewSpace k)`. Used to separate
the cut-block span from the join of the two side spans: S₁ and S₂ rows give `Φ = 0` (flow
sums cancel / V₂-bodies vanish), but a cut row `hingeRow u v r` with `u ∈ V₁, v ∉ V₁`
gives `Φ = r`. -/
private noncomputable def flowSum [Fintype α] (V₁ : Set α) :
    Module.Dual ℝ (α → ScrewSpace k) →ₗ[ℝ] Module.Dual ℝ (ScrewSpace k) where
  toFun φ := ∑ w ∈ V₁.toFinset, φ.comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) w)
  map_add' φ ψ := by
    simp [Finset.sum_add_distrib, LinearMap.add_comp]
  map_smul' c φ := by
    simp [Finset.smul_sum, LinearMap.smul_comp]

private lemma flowSum_hingeRow_both_mem [Fintype α] {V₁ : Set α}
    {u v : α} (hu : u ∈ V₁) (hv : v ∈ V₁)
    (r : Module.Dual ℝ (ScrewSpace k)) :
    flowSum V₁ (hingeRow (k := k) (α := α) u v r) = 0 := by
  -- Use LinearMap.ext to avoid the ext-on-exterior-power trap (TACTICS-QUIRKS §32).
  -- The sum telescopes: ∑_{w ∈ V₁} r((single_w y) u) - r((single_w y) v)
  --   = r y - r y = 0, since only the w=u (resp. w=v) term contributes.
  apply LinearMap.ext; intro y
  simp only [flowSum, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply,
    LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.comp_apply, LinearMap.coe_single, hingeRow_apply, map_sub]
  rw [Finset.sum_sub_distrib]
  -- ∑_{w ∈ V₁.toFinset} r ((single w y) u) = r y (only w=u contributes)
  have hsu : ∑ w ∈ V₁.toFinset, r ((Pi.single w y : α → ScrewSpace k) u) = r y := by
    rw [Finset.sum_eq_single u
      (fun w _ hwu => by simp [Pi.single_eq_of_ne (Ne.symm hwu)])
      (fun hu' => absurd (Set.mem_toFinset.mpr hu) hu')]
    simp [Pi.single_eq_same]
  -- ∑_{w ∈ V₁.toFinset} r ((single w y) v) = r y (only w=v contributes)
  have hsv : ∑ w ∈ V₁.toFinset, r ((Pi.single w y : α → ScrewSpace k) v) = r y := by
    rw [Finset.sum_eq_single v
      (fun w _ hwv => by simp [Pi.single_eq_of_ne (Ne.symm hwv)])
      (fun hv' => absurd (Set.mem_toFinset.mpr hv) hv')]
    simp [Pi.single_eq_same]
  rw [hsu, hsv, sub_self]

private lemma flowSum_hingeRow_both_not_mem [Fintype α] {V₁ : Set α}
    {u v : α} (hu : u ∉ V₁) (hv : v ∉ V₁) (r : Module.Dual ℝ (ScrewSpace k)) :
    flowSum V₁ (hingeRow (k := k) (α := α) u v r) = 0 := by
  apply LinearMap.ext; intro y
  simp only [flowSum, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply,
    LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.comp_apply, LinearMap.coe_single, hingeRow_apply]
  refine Finset.sum_eq_zero (fun w hw => ?_)
  rw [Pi.single_eq_of_ne (show u ≠ w from fun (h : u = w) => hu (h ▸ Set.mem_toFinset.mp hw)),
      Pi.single_eq_of_ne (show v ≠ w from fun (h : v = w) => hv (h ▸ Set.mem_toFinset.mp hw))]
  simp

private lemma flowSum_hingeRow_mem_not_mem [Fintype α] {V₁ : Set α}
    {u v : α} (hu : u ∈ V₁) (hv : v ∉ V₁) (r : Module.Dual ℝ (ScrewSpace k)) :
    flowSum V₁ (hingeRow (k := k) (α := α) u v r) = r := by
  simp only [flowSum, LinearMap.coe_mk, AddHom.coe_mk]
  -- The sum over V₁.toFinset collapses to the w = u term (all other terms are 0):
  -- • w = u: (single u x) u = x, (single u x) v = 0 (since v ≠ u, as v ∉ V₁, u ∈ V₁)
  --   → hingeRow u v r applied to (single u x) = r (x - 0) = r x.
  -- • w ≠ u, w ∈ V₁: (single w x) u = 0, (single w x) v = 0 (v ∉ V₁ so w ≠ v)
  --   → r (0 - 0) = 0.
  rw [Finset.sum_eq_single (f := fun w => (hingeRow (k := k) (α := α) u v r).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) w))
      u
      (fun w hw hwu => ?_)
      (fun hu' => absurd (Set.mem_toFinset.mpr hu) hu')]
  · -- w = u term: r
    apply LinearMap.ext; intro x
    simp only [LinearMap.comp_apply, LinearMap.coe_single, Pi.single, hingeRow_apply]
    rw [Function.update_self,
        Function.update_of_ne (fun (h : v = u) => hv (h ▸ hu))]
    simp
  · -- w ≠ u, w ∈ V₁.toFinset: term = 0
    apply LinearMap.ext; intro x
    simp only [LinearMap.comp_apply, LinearMap.coe_single, Pi.single, hingeRow_apply,
               LinearMap.zero_apply]
    rw [Function.update_of_ne (Ne.symm hwu),
        Function.update_of_ne (fun (h : v = w) => hv (h ▸ Set.mem_toFinset.mp hw))]
    simp

/-- The flow sum annihilates every element of the V₁-side span: for
`φ ∈ span(F[V₁].rigidityRows)`, `Φ(φ) = 0`. -/
private lemma flowSum_mem_span_induce_V₁_eq_zero [Fintype α]
    {F : BodyHingeFramework k α β} {V₁ : Set α}
    {φ : Module.Dual ℝ (α → ScrewSpace k)}
    (hφ : φ ∈ Submodule.span ℝ (⟨F.graph.induce V₁, F.supportExtensor⟩ :
      BodyHingeFramework k α β).rigidityRows) :
    flowSum V₁ φ = 0 := by
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨e, u, v, he, r, _, rfl⟩ := hφ
    simp only [Graph.induce_isLink] at he
    exact flowSum_hingeRow_both_mem he.2.1 he.2.2 r
  | zero => simp only [map_zero]
  | add x y _ _ hx hy =>
    rw [map_add, hx, hy, add_zero]
  | smul a x _ hx =>
    rw [map_smul, hx, smul_zero]

/-- The flow sum annihilates every element of the V₂-side span. -/
private lemma flowSum_mem_span_induce_V₂_eq_zero [Fintype α]
    {F : BodyHingeFramework k α β} {V₁ : Set α}
    {φ : Module.Dual ℝ (α → ScrewSpace k)}
    (hφ : φ ∈ Submodule.span ℝ (⟨F.graph.induce (V(F.graph) \ V₁), F.supportExtensor⟩ :
      BodyHingeFramework k α β).rigidityRows) :
    flowSum V₁ φ = 0 := by
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨e, u, v, he, r, _, rfl⟩ := hφ
    simp only [Graph.induce_isLink, Set.mem_diff] at he
    exact flowSum_hingeRow_both_not_mem he.2.1.2 he.2.2.2 r
  | zero => simp only [map_zero]
  | add x y _ _ hx hy =>
    rw [map_add, hx, hy, add_zero]
  | smul a x _ hx =>
    rw [map_smul, hx, smul_zero]

/-- **Vertex-disjoint block-rank addition** (`lem:rigidityRows-cut-rank-add`; KT Lemma 6.1
block-triangular core; Phase 22i L4a). For a body-hinge framework `F` whose link set
partitions over a cut `V₁ ⊂ V(F.graph)` with at most one crossing edge, the rigidity-row
span's dimension is at least the sum of the two side-spans plus `(D−1)·|cut|`. This is
Katoh–Tanigawa 2011 §6.1 Lemma 6.1's block-triangular rank-addition, the row-rank lower
bound underlying the not-2-edge-connected induction case.

Proof: the two side-spans are disjoint (V₁/V₂ projection argument), the cut block is
disjoint from their join (flow-sum argument). The three pieces jointly embed into the full
span, giving the rank lower bound by `Submodule.finrank_sup_of_inf_eq_bot` (disjoint sups). -/
theorem le_finrank_span_rigidityRows_of_cut [Finite α] [Finite β]
    (F : BodyHingeFramework k α β) {V₁ : Set α} {C : Set β}
    (hC_ncard : C.ncard ≤ 1)
    (hC_ext : ∀ e u v, F.graph.IsLink e u v → F.supportExtensor e ≠ 0)
    (_hE₁ : ∀ e u v, F.graph.IsLink e u v → e ∉ C →
      u ∈ V₁ ∧ v ∈ V₁ ∨ u ∉ V₁ ∧ v ∉ V₁)
    (hcut_mem : ∀ e ∈ C, ∃ u v, F.graph.IsLink e u v ∧ u ∈ V₁ ∧ v ∉ V₁) :
    Module.finrank ℝ (Submodule.span ℝ
        (⟨F.graph.induce V₁, F.supportExtensor⟩ : BodyHingeFramework k α β).rigidityRows) +
      (screwDim k - 1) * C.ncard +
      Module.finrank ℝ (Submodule.span ℝ
        (⟨F.graph.induce (V(F.graph) \ V₁), F.supportExtensor⟩ :
          BodyHingeFramework k α β).rigidityRows) ≤
    Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  haveI : Fintype β := Fintype.ofFinite β
  set F₁ : BodyHingeFramework k α β := ⟨F.graph.induce V₁, F.supportExtensor⟩
  set F₂ : BodyHingeFramework k α β := ⟨F.graph.induce (V(F.graph) \ V₁), F.supportExtensor⟩
  set S₁ := Submodule.span ℝ F₁.rigidityRows
  set S₂ := Submodule.span ℝ F₂.rigidityRows
  set S := Submodule.span ℝ F.rigidityRows
  -- Step 0: The cut-block span Sc and its dimension.
  -- When |C| = 0, the cut block contributes 0. When |C| = 1, it contributes D−1.
  rcases Nat.eq_zero_or_pos C.ncard with hzero | hpos
  · -- Disconnected case: |C| = 0. The sum is finrank(S₁) + 0 + finrank(S₂).
    simp only [hzero, Nat.mul_zero, add_zero]
    -- S₁ ≤ S and S₂ ≤ S.
    have hS₁S : S₁ ≤ S := by
      apply Submodule.span_le.mpr
      rintro φ ⟨e, u, v, he, r, hr, rfl⟩
      simp only [F₁, Graph.induce_isLink] at he
      exact Submodule.subset_span ⟨e, u, v, he.1, r, hr, rfl⟩
    have hS₂S : S₂ ≤ S := by
      apply Submodule.span_le.mpr
      rintro φ ⟨e, u, v, he, r, hr, rfl⟩
      simp only [F₂, Graph.induce_isLink] at he
      exact Submodule.subset_span ⟨e, u, v, he.1, r, hr, rfl⟩
    have hdisj : S₁ ⊓ S₂ = ⊥ := span_rigidityRows_induce_inf_eq_bot V₁
    have hstep := Submodule.finrank_sup_of_inf_eq_bot S₁ S₂ hdisj
    calc Module.finrank ℝ ↥S₁ + Module.finrank ℝ ↥S₂
        = Module.finrank ℝ ↥(S₁ ⊔ S₂) := hstep.symm
      _ ≤ Module.finrank ℝ ↥S := Submodule.finrank_mono (sup_le hS₁S hS₂S)
  · -- Connected case: |C| = 1. The cut block contributes screwDim k - 1.
    -- Get the unique cut edge and its endpoint data.
    have hcut_eq : C.ncard = 1 := Nat.le_antisymm hC_ncard hpos
    -- The cut block: span of hingeRows at the cut edge.
    obtain ⟨e_cut, he_cut_eq⟩ := Set.ncard_eq_one.mp hcut_eq
    obtain ⟨u₀, v₀, hl_cut, hu₀, hv₀⟩ := hcut_mem e_cut (he_cut_eq ▸ Set.mem_singleton e_cut)
    have huv₀ : u₀ ≠ v₀ := fun h => hv₀ (h ▸ hu₀)
    -- The cut hinge rows span a (D-1)-dimensional subspace.
    set Sc := Submodule.span ℝ {φ | ∃ r ∈ F.hingeRowBlock e_cut,
      φ = hingeRow (k := k) (α := α) u₀ v₀ r}
    -- finrank(Sc) = screwDim k - 1.
    have hCcut : F.supportExtensor e_cut ≠ 0 := hC_ext e_cut u₀ v₀ hl_cut
    have hSc_rk : Module.finrank ℝ Sc = screwDim k - 1 := by
      have hfin := finrank_hingeRowBlock F hCcut
      -- Sc = image of hingeRow u₀ v₀ (·) applied to hingeRowBlock e_cut
      have heq : Sc = (F.hingeRowBlock e_cut).map
          ((screwDiff (k := k) (α := α) u₀ v₀).dualMap) := by
        simp only [Sc, hingeRow_eq_dualMap]
        -- {φ | ∃ r ∈ hingeRowBlock, φ = dualMap r} = dualMap '' ↑hingeRowBlock
        -- then span (dualMap '' hingeRowBlock) = (span hingeRowBlock).map dualMap
        -- = hingeRowBlock.map dualMap
        have hset : {φ : Module.Dual ℝ (α → ScrewSpace k) | ∃ r ∈ F.hingeRowBlock e_cut,
            φ = (screwDiff u₀ v₀).dualMap r} =
            (screwDiff (k := k) (α := α) u₀ v₀).dualMap '' ↑(F.hingeRowBlock e_cut) := by
          ext ψ
          simp only [Set.mem_setOf_eq, Set.mem_image]
          exact ⟨fun ⟨r, hr, h⟩ => ⟨r, hr, h.symm⟩,
                 fun ⟨r, hr, h⟩ => ⟨r, hr, h.symm⟩⟩
        rw [hset, Submodule.span_image, Submodule.span_eq]
      have hinj : Function.Injective (screwDiff (k := k) (α := α) u₀ v₀).dualMap :=
        LinearMap.dualMap_injective_of_surjective (screwDiff_surjective huv₀)
      -- finrank(Sc) = finrank(image of injective map) = finrank(hingeRowBlock) = D-1
      have hinj_comp : Function.Injective
          ⇑((screwDiff (k := k) (α := α) u₀ v₀).dualMap.comp (F.hingeRowBlock e_cut).subtype) :=
        hinj.comp Subtype.coe_injective
      have hrk : Module.finrank ℝ ↥((F.hingeRowBlock e_cut).map
            (screwDiff (k := k) (α := α) u₀ v₀).dualMap) = screwDim k - 1 := by
        rw [show (F.hingeRowBlock e_cut).map (screwDiff u₀ v₀).dualMap =
              ((screwDiff u₀ v₀).dualMap.comp (F.hingeRowBlock e_cut).subtype).range from
            by rw [LinearMap.range_comp, Submodule.range_subtype],
            LinearMap.finrank_range_of_inj hinj_comp, hfin]
      rw [heq, hrk]
    -- Sc ⊆ S
    have hScS : Sc ≤ S := by
      apply Submodule.span_le.mpr
      rintro φ ⟨r, hr, rfl⟩
      exact Submodule.subset_span ⟨e_cut, u₀, v₀, hl_cut, r, hr, rfl⟩
    -- S₁ ≤ S and S₂ ≤ S.
    have hS₁S : S₁ ≤ S := by
      apply Submodule.span_le.mpr
      rintro φ ⟨e, u, v, he, r, hr, rfl⟩
      simp only [F₁, Graph.induce_isLink] at he
      exact Submodule.subset_span ⟨e, u, v, he.1, r, hr, rfl⟩
    have hS₂S : S₂ ≤ S := by
      apply Submodule.span_le.mpr
      rintro φ ⟨e, u, v, he, r, hr, rfl⟩
      simp only [F₂, Graph.induce_isLink] at he
      exact Submodule.subset_span ⟨e, u, v, he.1, r, hr, rfl⟩
    -- S₁ ⊓ S₂ = ⊥.
    have hdisj12 : S₁ ⊓ S₂ = ⊥ := span_rigidityRows_induce_inf_eq_bot V₁
    -- Sc ⊓ (S₁ ⊔ S₂) = ⊥: flow-sum argument.
    -- Key: for φ ∈ Sc, flowSum V₁ extracts the block functional; for φ ∈ S₁⊔S₂, flowSum = 0.
    -- Hence any element of the intersection has flowSum = 0 AND equal to the block functional
    -- of its Sc-representation, forcing the block functional to be 0, hence φ = 0.
    --
    -- We realize Sc as the image of the injective map `hingeRow u₀ v₀` from hingeRowBlock.
    -- The flow sum is the left inverse: flowSum V₁ ∘ hingeRow u₀ v₀ = id on the block.
    -- So from φ ∈ Sc with flowSum V₁ φ = 0, we get φ = hingeRow u₀ v₀ (flowSum V₁ φ) = 0.
    -- Key identity: for any φ ∈ Sc, φ = hingeRow u₀ v₀ (flowSum V₁ φ).
    -- The flow sum is a left inverse of hingeRow u₀ v₀ on the Sc generators.
    have hkey_id : ∀ φ ∈ Sc, φ = hingeRow (k := k) (α := α) u₀ v₀ (flowSum V₁ φ) := by
      intro φ hφSc
      induction hφSc using Submodule.span_induction with
      | mem φ hφ =>
        obtain ⟨r, _, rfl⟩ := hφ
        rw [flowSum_hingeRow_mem_not_mem hu₀ hv₀ r]
      | zero =>
        simp only [map_zero, hingeRow_eq_dualMap, map_zero]
      | add x y _ _ hx hy =>
        -- goal: x + y = hingeRow u₀ v₀ (flowSum V₁ (x + y))
        -- hx : x = hingeRow u₀ v₀ (flowSum V₁ x)
        -- hy : y = hingeRow u₀ v₀ (flowSum V₁ y)
        conv_rhs =>
          rw [map_add, hingeRow_eq_dualMap, map_add, ← hingeRow_eq_dualMap, ← hingeRow_eq_dualMap]
        rw [← hx, ← hy]
      | smul a x _ hx =>
        -- goal: a • x = hingeRow u₀ v₀ (flowSum V₁ (a • x))
        conv_rhs =>
          rw [map_smul, hingeRow_eq_dualMap, map_smul, ← hingeRow_eq_dualMap]
        rw [← hx]
    have hdisjc12 : Sc ⊓ (S₁ ⊔ S₂) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro φ ⟨hφSc, hφS12⟩
      -- From S₁⊔S₂: flowSum V₁ φ = 0.
      have hflow0 : flowSum V₁ φ = 0 := by
        obtain ⟨φ₁, hφ₁, φ₂, hφ₂, rfl⟩ := Submodule.mem_sup.mp hφS12
        simp only [map_add, flowSum_mem_span_induce_V₁_eq_zero hφ₁,
          flowSum_mem_span_induce_V₂_eq_zero hφ₂, add_zero]
      -- From the key identity: φ = hingeRow u₀ v₀ (flowSum V₁ φ) = hingeRow u₀ v₀ 0 = 0.
      rw [hkey_id φ hφSc, hflow0]
      simp [hingeRow_eq_dualMap, map_zero]
    -- Combine: finrank(S₁) + (D-1) + finrank(S₂) ≤ finrank(S).
    have step1 : Module.finrank ℝ ↥(S₁ ⊔ S₂) = Module.finrank ℝ ↥S₁ + Module.finrank ℝ ↥S₂ :=
      Submodule.finrank_sup_of_inf_eq_bot S₁ S₂ hdisj12
    have step2 : Module.finrank ℝ ↥(Sc ⊔ (S₁ ⊔ S₂)) =
        Module.finrank ℝ ↥Sc + Module.finrank ℝ ↥(S₁ ⊔ S₂) :=
      Submodule.finrank_sup_of_inf_eq_bot Sc (S₁ ⊔ S₂) hdisjc12
    rw [hcut_eq, Nat.mul_one]
    calc Module.finrank ℝ ↥S₁ + (screwDim k - 1) + Module.finrank ℝ ↥S₂
        = (screwDim k - 1) + Module.finrank ℝ ↥(S₁ ⊔ S₂) := by rw [step1]; ring
      _ = Module.finrank ℝ ↥(Sc ⊔ (S₁ ⊔ S₂)) := by rw [step2, hSc_rk]
      _ ≤ Module.finrank ℝ ↥S := Submodule.finrank_mono
          (sup_le hScS (sup_le hS₁S hS₂S))

end CutEdgeBrick

section SpliceBrick

variable {α β : Type*} {k : ℕ}

-- letI instance-shadowing for AddCommGroup ↥S in the h_rn subproof is elaboration-heavy
-- (the Semiring/AddCommMonoid vs. Ring/AddCommGroup instance diamond for submodule subtypes);
/-- **General-rank shared-body splice block-rank addition** (`lem:rigidityRows-splice-rank-add`;
KT Lemma 6.2 eqs.\ (6.3)–(6.5); Phase 22i L5a-i). Block-triangular rank-addition for a
shared-body split: given a linear endomorphism `D` of the rigidity-row dual space, a "rigid
block" submodule `SH = span(FH.rigidityRows)` lying in the kernel of `D`, and a "contraction
block" `Sc = span(Fc.rigidityRows)` whose image under `D` embeds in the image of the full span
`S = span(F.rigidityRows)`, the two block finranks satisfy

  `finrank SH + finrank Sc ≤ finrank S`.

This is the row-space version of KT's lower-triangular block-rank inequality (eq. (6.3)):
the `H`-block rows vanish under `D` (the top-right `0` of the block-triangular matrix, from
`hingeRow_comp_extProj_eq_zero`), and the contraction rows survive under `D` at their full
rank (Lemma 5.1 / `finrank_pinnedMotions_add_screwDim`, the column-deletion rank invariance
captured by `hInj`). Unlike L4a's vertex-disjoint cut (`le_finrank_span_rigidityRows_of_cut`,
where the split is disjoint by a vertex-projection argument), the two blocks share the
contracted body `r = v*`; the "disjointness" is the kernel containment `SH ≤ ker D` rather
than a geometric vertex partition.

Proof: rank-nullity for `D` restricted to `S` gives
`finrank(S.map D) + finrank(S ⊓ ker D) = finrank S`.
`SH ≤ S ⊓ ker D` (from `hFH_le` and `hFH_ker`) bounds the kernel term below by `finrank SH`.
`hFc_surv_le` and `hInj` bound the image term below by `finrank Sc`.
Adding gives the conclusion. -/
theorem le_finrank_span_rigidityRows_of_splice [Finite α] [Finite β]
    (F FH Fc : BodyHingeFramework k α β)
    (D : Module.Dual ℝ (α → ScrewSpace k) →ₗ[ℝ] Module.Dual ℝ (α → ScrewSpace k))
    (hFH_le : Submodule.span ℝ FH.rigidityRows ≤ Submodule.span ℝ F.rigidityRows)
    (hFH_ker : Submodule.span ℝ FH.rigidityRows ≤ LinearMap.ker D)
    (hFc_surv_le : (Submodule.span ℝ Fc.rigidityRows).map D ≤
                    (Submodule.span ℝ F.rigidityRows).map D)
    (hInj : Module.finrank ℝ ↥(Submodule.span ℝ Fc.rigidityRows) =
             Module.finrank ℝ ↥((Submodule.span ℝ Fc.rigidityRows).map D)) :
    Module.finrank ℝ ↥(Submodule.span ℝ FH.rigidityRows) +
    Module.finrank ℝ ↥(Submodule.span ℝ Fc.rigidityRows) ≤
    Module.finrank ℝ ↥(Submodule.span ℝ F.rigidityRows) := by
  haveI : Fintype α := Fintype.ofFinite α
  haveI : Fintype β := Fintype.ofFinite β
  haveI : FiniteDimensional ℝ (Module.Dual ℝ (α → ScrewSpace k)) := inferInstance
  set SH := Submodule.span ℝ FH.rigidityRows with hSH_def
  set Sc := Submodule.span ℝ Fc.rigidityRows with hSc_def
  set S := Submodule.span ℝ F.rigidityRows with hS_def
  -- Rank-nullity for D restricted to S: finrank(S.map D) + finrank(S ⊓ ker D) = finrank S.
  -- Route: let N = comap S.subtype (ker D) ≤ ↥S (the kernel of D|_S inside ↥S).
  -- Quotient rank-nullity on ↥S with N gives finrank(↥S ⧸ N) + finrank N = finrank S.
  -- Then ↥S ⧸ N ≅ (D.comp S.subtype).range = S.map D via quotKerEquivRange,
  -- and finrank N = finrank(S ⊓ ker D) via finrank_map_subtype_eq + map_comap_subtype.
  have h_rn : Module.finrank ℝ ↥(S.map D) + Module.finrank ℝ ↥(S ⊓ LinearMap.ker D) =
      Module.finrank ℝ ↥S := by
    -- letI (not haveI) forces AddCommGroup ↥S to shadow the global AddCommMonoid ↥S instance,
    -- enabling Ring/AddCommGroup paths for domRestrict and finrank_quotient_add_finrank.
    letI hSAG : AddCommGroup ↥S := S.addCommGroup
    have hq : Module.finrank ℝ (↥S ⧸ (D.domRestrict S).ker) +
        Module.finrank ℝ ↥(D.domRestrict S).ker = Module.finrank ℝ ↥S :=
      (D.domRestrict S).ker.finrank_quotient_add_finrank
    have heq : Module.finrank ℝ (↥S ⧸ (D.domRestrict S).ker) =
        Module.finrank ℝ ↥(S.map D) := by
      have h := LinearEquiv.finrank_eq (D.domRestrict S).quotKerEquivRange
      rw [LinearMap.range_domRestrict] at h
      exact h
    have hker : Module.finrank ℝ ↥(D.domRestrict S).ker =
        Module.finrank ℝ ↥(S ⊓ LinearMap.ker D) := by
      rw [LinearMap.ker_domRestrict,
          ← Submodule.finrank_map_subtype_eq S (Submodule.comap S.subtype (LinearMap.ker D)),
          Submodule.map_comap_subtype]
    linarith
  -- SH ≤ S ⊓ ker D, so finrank SH ≤ finrank(S ⊓ ker D).
  have h_SH_le_inf : SH ≤ S ⊓ LinearMap.ker D := le_inf hFH_le hFH_ker
  have h_SH_le : Module.finrank ℝ ↥SH ≤ Module.finrank ℝ ↥(S ⊓ LinearMap.ker D) :=
    Submodule.finrank_mono h_SH_le_inf
  -- Sc.map D ≤ S.map D, so finrank Sc ≤ finrank(S.map D).
  have h_Sc_le : Module.finrank ℝ ↥Sc ≤ Module.finrank ℝ ↥(S.map D) :=
    hInj.le.trans (Submodule.finrank_mono hFc_surv_le)
  linarith

end SpliceBrick

section PinnedPlacementBrick

variable {α β : Type*} {k : ℕ}

/-- **Span-level pinned-placement block-rank lower bound**
(`lem:rigidityRows-pinned-placement-rank-add`; the eq.~(6.12) placement core shared by KT Lemma 6.8
(Case II / `k > 0` split) and Lemma 6.10 (Case III); Phase 22j). The span-transport analogue of the
splice brick (`le_finrank_span_rigidityRows_of_splice`), for the *pin-a-body* (splitting) geometry
rather than the *collapse* (`extProj`-projected-column) geometry: given a body-hinge framework `F`,
a body `v`, a **new block** of functionals `rn : ιn → Module.Dual ℝ (α → ScrewSpace k)` independent
through `v`'s screw column (`hnewpin`) and lying in `span F.rigidityRows` (`hnew_span`), and an
**old block** `ro : ιo → …` that (a) vanishes on `v`'s screw column (`hold`), (b) is independent
(`holdindep`), and (c) lies in `span F.rigidityRows` (`hold_span`), the two block sizes satisfy

  `Nat.card ιn + Nat.card ιo ≤ finrank (span F.rigidityRows)`.

The proof is the `hrank_lb` skeleton of the KT Lemma 6.8 producer `case_II_realization_all_k` lifted
out (Phase 22i L6b, CaseI.lean): the block-triangular pin-a-body split
(`linearIndependent_sum_pinned_block`) makes the combined family `Sum.elim rn ro` independent; its
span lies in `span F.rigidityRows` (`hnew_span`/`hold_span`); and `finrank_span_eq_card` +
`Submodule.finrank_mono` of the combined span give the count. **No new linear algebra** — the
abstraction's value is in the *callers'* discharge of `hold_span` (the genuinely-new content): the
`splitOff` `e₀ = e_a + e_b` row decomposition for Lemma 6.8, the `removeVertex`+relabel
`hingeRow ∈ span` interface for Case III, and `Submodule.subset_span ∘ panelRow_mem_rigidityRows`
under a literal `Gv ≤ G`. Unlike the literal placement bricks (`case_II_placement_eq612`), the
conclusion keys on `span F.rigidityRows` membership, **not** literal `F.rigidityRows` membership, so
every real reduction graph (collapse / `splitOff` / relabel — which land rows only in the span)
fits. Carrier-free at the block level (the row functionals are arbitrary duals); the
`ofNormals`/`withGraph` defeq trap (TACTICS-QUIRKS §38) does not bite. -/
theorem le_finrank_span_rigidityRows_of_pinned_placement [Finite α] [Finite β]
    [DecidableEq α] {ιn ιo : Type*} [Finite ιn] [Finite ιo] (F : BodyHingeFramework k α β) {v : α}
    {rn : ιn → Module.Dual ℝ (α → ScrewSpace k)} {ro : ιo → Module.Dual ℝ (α → ScrewSpace k)}
    (hold : ∀ (j : ιo) (x : ScrewSpace k),
      ro j (Function.update (0 : α → ScrewSpace k) v x) = 0)
    (hnewpin : LinearIndependent ℝ
      (fun i : ιn => (rn i).comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v)))
    (holdindep : LinearIndependent ℝ ro)
    (hnew_span : ∀ i : ιn, rn i ∈ Submodule.span ℝ F.rigidityRows)
    (hold_span : ∀ j : ιo, ro j ∈ Submodule.span ℝ F.rigidityRows) :
    Nat.card ιn + Nat.card ιo ≤ Module.finrank ℝ ↥(Submodule.span ℝ F.rigidityRows) := by
  haveI : Fintype α := Fintype.ofFinite α
  haveI : Fintype ιn := Fintype.ofFinite ιn
  haveI : Fintype ιo := Fintype.ofFinite ιo
  -- The combined family `Sum.elim rn ro` is independent by the pin-a-body block split.
  have hunion : LinearIndependent ℝ (Sum.elim rn ro) :=
    linearIndependent_sum_pinned_block (v := v) hold hnewpin holdindep
  -- Its span lies in `span F.rigidityRows` (both blocks are span members).
  have hcomb_le : Submodule.span ℝ (Set.range (Sum.elim rn ro)) ≤
      Submodule.span ℝ F.rigidityRows := by
    rw [Submodule.span_le]
    rintro _ ⟨(i | j), rfl⟩
    · exact hnew_span i
    · exact hold_span j
  -- `finrank (combined span) = |ιn ⊕ ιo|`, then monotonicity gives the count bound.
  have hmono := Submodule.finrank_mono hcomb_le
  rw [finrank_span_eq_card hunion, Fintype.card_sum,
    ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at hmono
  exact hmono

/-- **The `+1` augment of the pinned-placement block-rank lower bound**
(`lem:rigidityRows-pinned-placement-rank-add`; the Case-III variant routing through the augmented
pin-a-body split `linearIndependent_sum_pinned_block_augment`, KT eq.~(6.29) shape; Phase 22j). The
sibling of `le_finrank_span_rigidityRows_of_pinned_placement` that lifts the new block by one extra
candidate row `w` pinned through body `v`'s screw column (`hnewpinaug`, the augmented top-left
`D × D` full-rank block), supplying Case III's `+1` over the stratum-1
`D(|V|−1) − 1` count. With `w` lying in `span F.rigidityRows` (`hw_span`) the count becomes

  `Nat.card ιn + 1 + Nat.card ιo ≤ finrank (span F.rigidityRows)`.

Proof: the augmented combined family `Sum.elim (Sum.elim rn (fun _ : Unit => w)) ro` is independent
by `linearIndependent_sum_pinned_block_augment`; its span lies in `span F.rigidityRows`; and
`finrank_span_eq_card` + `Submodule.finrank_mono` give the count
(`Nat.card (ιn ⊕ Unit) + Nat.card ιo = Nat.card ιn + 1 + Nat.card ιo`). The `Unit` summand is the
extra candidate row. Same span-transport interface, callers, and carrier-freeness as the unaugmented
brick. -/
theorem le_finrank_span_rigidityRows_of_pinned_placement_augment [Finite α] [Finite β]
    [DecidableEq α] {ιn ιo : Type*} [Finite ιn] [Finite ιo] (F : BodyHingeFramework k α β) {v : α}
    {rn : ιn → Module.Dual ℝ (α → ScrewSpace k)} {ro : ιo → Module.Dual ℝ (α → ScrewSpace k)}
    {w : Module.Dual ℝ (α → ScrewSpace k)}
    (hold : ∀ (j : ιo) (x : ScrewSpace k),
      ro j (Function.update (0 : α → ScrewSpace k) v x) = 0)
    (hnewpinaug : LinearIndependent ℝ (Sum.elim
      (fun i : ιn => (rn i).comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v))
      (fun _ : Unit => w.comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v))))
    (holdindep : LinearIndependent ℝ ro)
    (hnew_span : ∀ i : ιn, rn i ∈ Submodule.span ℝ F.rigidityRows)
    (hw_span : w ∈ Submodule.span ℝ F.rigidityRows)
    (hold_span : ∀ j : ιo, ro j ∈ Submodule.span ℝ F.rigidityRows) :
    Nat.card ιn + 1 + Nat.card ιo ≤ Module.finrank ℝ ↥(Submodule.span ℝ F.rigidityRows) := by
  haveI : Fintype α := Fintype.ofFinite α
  haveI : Fintype ιn := Fintype.ofFinite ιn
  haveI : Fintype ιo := Fintype.ofFinite ιo
  -- The augmented combined family is independent by the augmented pin-a-body split.
  have hunion : LinearIndependent ℝ (Sum.elim (Sum.elim rn (fun _ : Unit => w)) ro) :=
    linearIndependent_sum_pinned_block_augment (v := v) hold hnewpinaug holdindep
  -- Its span lies in `span F.rigidityRows` (`rn`, `w`, and `ro` are all span members).
  have hcomb_le : Submodule.span ℝ
      (Set.range (Sum.elim (Sum.elim rn (fun _ : Unit => w)) ro)) ≤
      Submodule.span ℝ F.rigidityRows := by
    rw [Submodule.span_le]
    rintro _ ⟨((i | _) | j), rfl⟩
    · exact hnew_span i
    · exact hw_span
    · exact hold_span j
  -- `finrank (combined span) = |(ιn ⊕ Unit) ⊕ ιo|`, then monotonicity gives the count bound.
  have hmono := Submodule.finrank_mono hcomb_le
  rw [finrank_span_eq_card hunion, Fintype.card_sum, Fintype.card_sum, Fintype.card_unit,
    ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at hmono
  exact hmono

end PinnedPlacementBrick

end BodyHingeFramework

end CombinatorialRigidity.Molecular
