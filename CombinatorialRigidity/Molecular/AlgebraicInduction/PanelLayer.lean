/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.RigidityMatrix.Basic
import Mathlib.LinearAlgebra.Quotient.Pi
import CombinatorialRigidity.Molecular.Deficiency

/-!
# Panel support extensors, their coordinates, and the deficiency bound

The definitions and lemmas on panels of `sec:molecular-algebraic-induction-panel` and of
`sec:molecular-algebraic-induction-base`, the forms of `lem:rows-polynomial-in-normals`, and the
deficiency bound of `sec:molecular-deficiency-rank-bound`. Katoh and Tanigawa call a body-hinge
framework a panel-hinge framework if the hinges at each body lie in a common hyperplane, its panel
(2011, *A proof of the molecular conjecture*, Discrete Comput. Geom. **45**, p. 648), and they build
the hinge of an edge `uv` as the intersection of the panels of `u` and `v` (§5.1, p. 668). We give a
panel by a normal vector in `K^(k+2)`, in homogeneous coordinates, and the hinge of two panels with
normals `n₁` and `n₂` by its extensor `C(n₁, n₂) = *(n₁ ∨ n₂)`, the panel support extensor
(`def:panel-support-extensor`). As in `RigidityMatrix/Basic.lean`, `d = k + 1`. The file proves:

* for the join `normalsJoin n₁ n₂` of two normals and the panel support extensor: linearity in the
  first normal, the sign under a swap, that they are nonzero iff the normals are linearly
  independent, that panel support extensors are independent iff their joins are
  (`lem:panel-support-extensor-independence`), and that the panel support extensor is a join of
  `d − 1` vectors of both panels (`lem:panel-support-extensor-join`);
* vectors orthogonal to given normals, two independent extensors in one panel
  (`lem:extensor-pair-in-panel`), and a nonzero extensor in two panels;
* normals whose panel support extensors are independent: up to `D` pairs
  (`lem:exists-independent-panel-extensor`), a triangle (`lem:triangle-normals`) and a cycle
  (`lem:cycle-normals`);
* the forms `annihRow` that vanish on a hinge, which span its hinge-row block, and the coordinates
  of the panel support extensor and of these forms as polynomials of degree two in the normals
  (`lem:rows-polynomial-in-normals`);
* the deficiency bound `D + def(G̃) ≤ dim Z(G,p)` (`lem:deficiency-rank-bound`) and its form with
  bodies outside `V(G)` (`lem:relative-deficiency-rank-bound`), by counting the motions constant on
  the parts of a partition;
* that the two forms of `D` agree, `bodyBarDim n = screwDim k`, only at `n = k + 1`.
-/

namespace CombinatorialRigidity.Molecular

variable {k : ℕ}
variable {K : Type*} [Field K]

/-! ## The panel support extensor (`def:panel-support-extensor`)

A panel is a hyperplane of `K^(k+1)`, given by a normal vector `n ∈ K^(k+2)` in homogeneous
coordinates. The hinge of two panels with normals `n₁` and `n₂` is their intersection, and its
extensor is their meet `complementIso (n₁ ∨ n₂)`, where the join `n₁ ∨ n₂ = normalsJoin n₁ n₂` lies
in `⋀² K^(k+2)` and `complementIso : ⋀² K^(k+2) ≃ ⋀^k K^(k+2)` is the complement isomorphism of
`Meet.lean` (`def:meet-complement-iso`). It is nonzero iff `n₁` and `n₂` are linearly independent
(`panelSupportExtensor_ne_zero_iff`), and a nondegenerate hinge lies in both panels
(`lem:panel-support-extensor-join`). -/

/-- **The join of two normals** (the join `n₁ ∨ n₂` of `def:panel-support-extensor`):
`n₁ ∧ n₂ = ιMulti K 2 ![n₁, n₂]` in `⋀² K^(k+2)`. The panel support extensor is its image under the
complement isomorphism (`panelSupportExtensor`). -/
noncomputable def normalsJoin (n₁ n₂ : Fin (k + 2) → K) :
    ⋀[K]^2 (Fin (k + 2) → K) :=
  exteriorPower.ιMulti K 2 ![n₁, n₂]

/-- **The join of two normals is their extensor**: as an element of the exterior algebra,
`normalsJoin n₁ n₂ = extensor ![n₁, n₂]` (`def:extensor`). -/
theorem normalsJoin_coe (n₁ n₂ : Fin (k + 2) → K) :
    (normalsJoin n₁ n₂ : ExteriorAlgebra K (Fin (k + 2) → K)) = extensor ![n₁, n₂] := by
  rw [normalsJoin, exteriorPower.ιMulti_apply_coe, extensor_apply]

/-- **The coordinates of the join of two normals are `2 × 2` minors** (a step of
`lem:rows-polynomial-in-normals`): in the basis of `⋀² K^(k+2)` indexed by the 2-element subsets
`s = {i < j}` of `Fin (k+2)`, the coordinate of `normalsJoin n₁ n₂` at `s` is
`n₁ i * n₂ j − n₁ j * n₂ i`, by `exteriorPower.basis_repr_apply`,
`exteriorPower.ιMultiDual_apply_ιMulti` and `Matrix.det_fin_two`. So the coordinates are polynomials
of degree two in the normals. -/
theorem normalsJoin_basis_repr (n₁ n₂ : Fin (k + 2) → K)
    (s : Set.powersetCard (Fin (k + 2)) 2) :
    ((Pi.basisFun K (Fin (k + 2))).exteriorPower 2).repr (normalsJoin n₁ n₂) s =
      n₁ ((s : Finset (Fin (k + 2))).orderEmbOfFin s.2 0)
          * n₂ ((s : Finset (Fin (k + 2))).orderEmbOfFin s.2 1)
        - n₁ ((s : Finset (Fin (k + 2))).orderEmbOfFin s.2 1)
          * n₂ ((s : Finset (Fin (k + 2))).orderEmbOfFin s.2 0) := by
  rw [normalsJoin, exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti,
    Matrix.det_fin_two]
  simp only [Matrix.of_apply, Set.powersetCard.ofFinEmbEquiv_symm_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rfl

/-- **The minors of `normalsJoin_basis_repr` as polynomials** (a step of
`lem:rows-polynomial-in-normals`): normals for the bodies are a point `q : α × Fin (k+2) → K`, with
`q (a, i)` the coordinate `i` of the normal of `a`. For bodies `u`, `v` and `s = {i < j}`,
`normalsJoinPoly u v s = X (u, i) * X (v, j) − X (u, j) * X (v, i)`, whose value at `q` is the
coordinate at `s` of the join of the normals of `u` and `v` (`normalsJoinPoly_eval`). -/
noncomputable def normalsJoinPoly {α : Type*} (u v : α) (s : Set.powersetCard (Fin (k + 2)) 2) :
    MvPolynomial (α × Fin (k + 2)) K :=
  MvPolynomial.X (u, (s : Finset (Fin (k + 2))).orderEmbOfFin s.2 0)
      * MvPolynomial.X (v, (s : Finset (Fin (k + 2))).orderEmbOfFin s.2 1)
    - MvPolynomial.X (u, (s : Finset (Fin (k + 2))).orderEmbOfFin s.2 1)
      * MvPolynomial.X (v, (s : Finset (Fin (k + 2))).orderEmbOfFin s.2 0)

/-- **The value of `normalsJoinPoly`** (a step of `lem:rows-polynomial-in-normals`): at `q`, it is
the coordinate at `s` of `normalsJoin (q (u, ·)) (q (v, ·))` (`normalsJoin_basis_repr`). -/
theorem normalsJoinPoly_eval {α : Type*} (u v : α) (q : α × Fin (k + 2) → K)
    (s : Set.powersetCard (Fin (k + 2)) 2) :
    MvPolynomial.eval q (normalsJoinPoly u v s) =
      ((Pi.basisFun K (Fin (k + 2))).exteriorPower 2).repr
        (normalsJoin (fun i => q (u, i)) (fun i => q (v, i))) s := by
  rw [normalsJoin_basis_repr, normalsJoinPoly]
  simp only [map_sub, map_mul, MvPolynomial.eval_X]

/-- **`normalsJoinPoly` has degree at most two** (a step of `lem:rows-polynomial-in-normals`): it is
a difference of two products of two variables. -/
theorem normalsJoinPoly_totalDegree_le {α : Type*} (u v : α)
    (s : Set.powersetCard (Fin (k + 2)) 2) :
    (normalsJoinPoly (K := K) u v s).totalDegree ≤ 2 := by
  have hprod : ∀ a b : α × Fin (k + 2),
      (MvPolynomial.X (R := K) a * MvPolynomial.X b).totalDegree ≤ 2 :=
    fun a b => (MvPolynomial.totalDegree_mul _ _).trans
      (by rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X])
  rw [normalsJoinPoly]
  exact (MvPolynomial.totalDegree_sub _ _).trans (max_le (hprod _ _) (hprod _ _))

/-- **The join of two normals is nonzero iff they are linearly independent** (the remark after
`def:extensor`): `normalsJoin n₁ n₂ ≠ 0 ↔ LinearIndependent K ![n₁, n₂]`, by
`extensor_ne_zero_iff_linearIndependent`. For nonzero normals, this says that the hyperplanes `n₁^⊥`
and `n₂^⊥` are distinct. -/
theorem normalsJoin_ne_zero_iff (n₁ n₂ : Fin (k + 2) → K) :
    normalsJoin n₁ n₂ ≠ 0 ↔ LinearIndependent K ![n₁, n₂] := by
  rw [← extensor_ne_zero_iff_linearIndependent (d := k + 1) ![n₁, n₂],
    ← normalsJoin_coe, ne_eq, ne_eq, ← ZeroMemClass.coe_eq_zero (x := normalsJoin n₁ n₂)]

/-- **Swapping the normals negates the join**: `normalsJoin n₂ n₁ = −normalsJoin n₁ n₂`, as
`ιMulti K 2` is alternating (`AlternatingMap.map_swap`). `panelSupportExtensor_swap` is its form for
the panel support extensor. -/
theorem normalsJoin_swap (n₁ n₂ : Fin (k + 2) → K) :
    normalsJoin n₂ n₁ = -normalsJoin (k := k) n₁ n₂ := by
  rw [normalsJoin, normalsJoin]
  have hsw : (![n₁, n₂] : Fin 2 → Fin (k + 2) → K) ∘ Equiv.swap 0 1 = ![n₂, n₁] := by
    funext i; fin_cases i <;> simp
  rw [← hsw, (exteriorPower.ιMulti K 2).map_swap (v := ![n₁, n₂]) (Fin.zero_ne_one)]

/-- **The join of a normal with itself is zero**: `normalsJoin n n = 0`, as `ιMulti K 2` is
alternating (`AlternatingMap.map_eq_zero_of_eq`). -/
theorem normalsJoin_self (n : Fin (k + 2) → K) : normalsJoin (k := k) n n = 0 := by
  rw [normalsJoin]
  exact (exteriorPower.ιMulti K 2).map_eq_zero_of_eq ![n, n] (i := 0) (j := 1) rfl (by decide)

/-- **Adding a multiple of the second normal to the first keeps the join**:
`normalsJoin (n₁ + t • n₂) n₂ = normalsJoin n₁ n₂`. By linearity in the first normal
(`AlternatingMap.map_update_add`, `AlternatingMap.map_update_smul`) the left side is
`normalsJoin n₁ n₂ + t • normalsJoin n₂ n₂`, and `normalsJoin n₂ n₂ = 0` (`normalsJoin_self`).
`panelSupportExtensor_add_smul_right` is its form for the panel support extensor. -/
theorem normalsJoin_add_smul_right (n₁ n₂ : Fin (k + 2) → K) (t : K) :
    normalsJoin (n₁ + t • n₂) n₂ = normalsJoin n₁ n₂ := by
  -- First-column linearity, then the `t • normalsJoin n₂ n₂` term vanishes (equal columns).
  have h1 : normalsJoin (n₁ + t • n₂) n₂ = normalsJoin n₁ n₂ + t • normalsJoin n₂ n₂ := by
    rw [normalsJoin, normalsJoin, normalsJoin,
      show (![n₁ + t • n₂, n₂] : Fin 2 → Fin (k + 2) → K)
        = Function.update ![n₁, n₂] 0 (n₁ + t • n₂) from by funext i; fin_cases i <;> simp,
      show (n₁ + t • n₂ : Fin (k + 2) → K) = ![n₁, n₂] 0 + t • ![n₂, n₂] 0 from by simp,
      (exteriorPower.ιMulti K 2).map_update_add, (exteriorPower.ιMulti K 2).map_update_smul]
    congr 2
    all_goals (funext i; fin_cases i <;> simp)
  simp only [h1, normalsJoin_self, smul_zero, add_zero]

/-- **The join is additive in the first normal**:
`normalsJoin (n₁ + n₂) n₃ = normalsJoin n₁ n₃ + normalsJoin n₂ n₃`
(`AlternatingMap.map_update_add`). `panelSupportExtensor_add_left` is its form for the panel support
extensor. -/
theorem normalsJoin_add_left (n₁ n₂ n₃ : Fin (k + 2) → K) :
    normalsJoin (n₁ + n₂) n₃ = normalsJoin (k := k) n₁ n₃ + normalsJoin n₂ n₃ := by
  rw [normalsJoin, normalsJoin, normalsJoin,
    show (![n₁ + n₂, n₃] : Fin 2 → Fin (k + 2) → K)
      = Function.update ![n₁, n₃] 0 (n₁ + n₂) from by funext i; fin_cases i <;> simp,
    show (n₁ + n₂ : Fin (k + 2) → K) = ![n₁, n₃] 0 + ![n₂, n₃] 0 from by simp,
    (exteriorPower.ιMulti K 2).map_update_add]
  congr 2
  all_goals (funext i; fin_cases i <;> simp)

/-- **The join is homogeneous in the first normal**:
`normalsJoin (c • n₁) n₂ = c • normalsJoin n₁ n₂` (`AlternatingMap.map_update_smul`).
`panelSupportExtensor_smul_left` is its form for the panel support extensor. -/
theorem normalsJoin_smul_left (c : K) (n₁ n₂ : Fin (k + 2) → K) :
    normalsJoin (c • n₁) n₂ = c • normalsJoin (k := k) n₁ n₂ := by
  rw [normalsJoin, normalsJoin,
    show (![c • n₁, n₂] : Fin 2 → Fin (k + 2) → K)
      = Function.update ![n₁, n₂] 0 (c • n₁) from by funext i; fin_cases i <;> simp,
    show (c • n₁ : Fin (k + 2) → K) = c • ![n₁, n₂] 0 from by simp,
    (exteriorPower.ιMulti K 2).map_update_smul]
  congr 2
  all_goals (funext i; fin_cases i <;> simp)

/-- **The panel support extensor** (`def:panel-support-extensor`): `C(n₁, n₂)` is
`complementIso (normalsJoin n₁ n₂)`, the image of the join of the two normals under the complement
isomorphism `⋀² K^(k+2) ≃ ⋀^k K^(k+2)` (`def:meet-complement-iso`), an element of the screw space
`ScrewSpace K k = ⋀^k K^(k+2)`. For linearly independent normals it is the meet of the two panels,
an extensor of their intersection (`lem:panel-support-extensor-join`). -/
noncomputable def panelSupportExtensor (n₁ n₂ : Fin (k + 2) → K) : ScrewSpace K k :=
  complementIso (k := k) (j := 2) (by omega) (normalsJoin n₁ n₂)

/-- **The panel support extensor is nonzero iff the normals are linearly independent** (the remark
after `def:panel-support-extensor`): `complementIso` is injective, and the join is nonzero iff the
normals are independent (`normalsJoin_ne_zero_iff`). For nonzero normals, the hinge of two panels is
nondegenerate iff the panels are distinct. -/
theorem panelSupportExtensor_ne_zero_iff (n₁ n₂ : Fin (k + 2) → K) :
    panelSupportExtensor n₁ n₂ ≠ 0 ↔ LinearIndependent K ![n₁, n₂] := by
  rw [panelSupportExtensor, ← normalsJoin_ne_zero_iff]
  exact map_ne_zero_iff _ (complementIso (by omega : 2 ≤ k + 2)).injective

/-- **Swapping the normals negates the panel support extensor**:
`panelSupportExtensor n₂ n₁ = −panelSupportExtensor n₁ n₂`, from `normalsJoin_swap`, as
`complementIso` is linear. The hinge constraint asks that `S u − S v` lie in the span of the
extensor, which the sign does not change; so the order in which a framework records the two ends of
an edge does not change its motions
(`PanelHingeFramework.infinitesimalMotions_ofNormals_eq_of_ends_swap`). -/
theorem panelSupportExtensor_swap (n₁ n₂ : Fin (k + 2) → K) :
    panelSupportExtensor n₂ n₁ = -panelSupportExtensor (k := k) n₁ n₂ := by
  rw [panelSupportExtensor, panelSupportExtensor, normalsJoin_swap]
  exact map_neg _ _

/-- **The panel support extensor is additive in the first normal**: from `normalsJoin_add_left`, as
`complementIso` is linear. With `panelSupportExtensor_smul_left`, the hinge `C(n_u + t • n', n_r)`
is affine in `t`, as Case III's candidate uses
(`PanelHingeFramework.caseIIICandidate_panelRow_eq_add_smul`). -/
theorem panelSupportExtensor_add_left (n₁ n₂ n₃ : Fin (k + 2) → K) :
    panelSupportExtensor (n₁ + n₂) n₃
      = panelSupportExtensor (k := k) n₁ n₃ + panelSupportExtensor n₂ n₃ := by
  rw [panelSupportExtensor, panelSupportExtensor, panelSupportExtensor, normalsJoin_add_left]
  exact map_add _ _ _

/-- **The panel support extensor is homogeneous in the first normal**:
`panelSupportExtensor (c • n₁) n₂ = c • panelSupportExtensor n₁ n₂`, from `normalsJoin_smul_left`.
-/
theorem panelSupportExtensor_smul_left (c : K) (n₁ n₂ : Fin (k + 2) → K) :
    panelSupportExtensor (c • n₁) n₂ = c • panelSupportExtensor (k := k) n₁ n₂ := by
  rw [panelSupportExtensor, panelSupportExtensor, normalsJoin_smul_left]
  exact map_smul _ _ _

/-- **Adding a multiple of the second normal to the first keeps the panel support extensor**:
`C(n₁ + t • n₂, n₂) = C(n₁, n₂)`, from `normalsJoin_add_smul_right`. In the proof of KT Lemma 6.8,
with `n₁ = n_a` and `n₂ = n_b`, the body `v` that is put back with the normal `n_a + t • n_b` has at
the edge `vb` the hinge of `ab`, as KT eq. (6.12) asks (p. 678). -/
theorem panelSupportExtensor_add_smul_right (n₁ n₂ : Fin (k + 2) → K) (t : K) :
    panelSupportExtensor (n₁ + t • n₂) n₂ = panelSupportExtensor (k := k) n₁ n₂ := by
  rw [panelSupportExtensor, panelSupportExtensor, normalsJoin_add_smul_right]

/-- **The hinge of `va` at that normal**: `C(n₁ + t • n₂, n₁) = (−t) • C(n₁, n₂)`, by linearity in
the first normal, `normalsJoin_self` and `normalsJoin_swap`. With `n₁ = n_a` and `n₂ = n_b` as in
`panelSupportExtensor_add_smul_right`, the hinge of `va` is nondegenerate when `t ≠ 0` and
`C(n_a, n_b) ≠ 0`, and it lies in the panel of `a`, as KT eq. (6.12) asks of the hinge `L` of `va`
(p. 678). At `t = 0` it would be degenerate. -/
theorem panelSupportExtensor_add_smul_left (n₁ n₂ : Fin (k + 2) → K) (t : K) :
    panelSupportExtensor (n₁ + t • n₂) n₁ = (-t) • panelSupportExtensor (k := k) n₁ n₂ := by
  -- First-column linearity: `normalsJoin (n₁+t•n₂) n₁ = normalsJoin n₁ n₁ + t • normalsJoin n₂ n₁`.
  have h1 : normalsJoin (n₁ + t • n₂) n₁ = normalsJoin n₁ n₁ + t • normalsJoin n₂ n₁ := by
    rw [normalsJoin, normalsJoin, normalsJoin,
      show (![n₁ + t • n₂, n₁] : Fin 2 → Fin (k + 2) → K)
        = Function.update ![n₁, n₁] 0 (n₁ + t • n₂) from by funext i; fin_cases i <;> simp,
      show (n₁ + t • n₂ : Fin (k + 2) → K) = ![n₁, n₁] 0 + t • ![n₂, n₁] 0 from by simp,
      (exteriorPower.ιMulti K 2).map_update_add, (exteriorPower.ιMulti K 2).map_update_smul]
    congr 2
    all_goals (funext i; fin_cases i <;> simp)
  have hjoin : normalsJoin (n₁ + t • n₂) n₁ = (-t) • normalsJoin (k := k) n₁ n₂ := by
    rw [h1, normalsJoin_self, normalsJoin_swap]; module
  rw [panelSupportExtensor, panelSupportExtensor, hjoin]
  exact map_smul _ _ _

/-- **The panel support extensor as the complement of an extensor**:
`C(n₁, n₂) = complementIso (extensor ![n₁, n₂])`, from `normalsJoin_coe`. `Meet.lean` states its
lemmas in this form (`extensor_join_proportional_complementIso_meet`), and the proofs of Case III
and of `lem:panel-support-extensor-join` apply them through it. -/
theorem panelSupportExtensor_eq_complementIso_extensor (n₁ n₂ : Fin (k + 2) → K) :
    panelSupportExtensor n₁ n₂
      = complementIso (k := k) (j := 2) (by omega)
          ⟨extensor ![n₁, n₂], extensor_mem_exteriorPower _⟩ := by
  rw [panelSupportExtensor]
  exact congrArg _ (Subtype.ext (normalsJoin_coe n₁ n₂))

/-- **`m` independent vectors orthogonal to `r` normals, for `m + r ≤ k + 2`**: for
`N : Fin r → K^(k+2)` there are `m` linearly independent vectors `p i` with `p i ⬝ᵥ N j = 0` for all
`i` and `j`. The kernel of the map `x ↦ (N j ⬝ᵥ x)_j` to `K^r` has dimension at least
`(k + 2) − r ≥ m` (`LinearMap.finrank_range_add_finrank_ker`), and
`exists_linearIndependent_of_le_finrank` gives the vectors in it. The lemmas below for `K⁴` are the
cases `r = m = 2` and `r = 1`, `m = 3`. -/
theorem exists_linearIndependent_perp_of_normals {r m : ℕ} (N : Fin r → Fin (k + 2) → K)
    (hmr : m + r ≤ k + 2) :
    ∃ p : Fin m → Fin (k + 2) → K, LinearIndependent K p ∧ ∀ i j, p i ⬝ᵥ N j = 0 := by
  classical
  -- The pairing map `L x = (j ↦ Nⱼ ⬝ᵥ x)` as the `Matrix.mulVecLin` of the `r × (k+2)` matrix.
  set A : Matrix (Fin r) (Fin (k + 2)) K := Matrix.of N with hA
  set L : (Fin (k + 2) → K) →ₗ[K] (Fin r → K) := A.mulVecLin with hL
  -- `hmemW`: `x ∈ ker L ↔ ∀ j, x ⬝ᵥ Nⱼ = 0`.
  have hmemW : ∀ x : Fin (k + 2) → K, x ∈ LinearMap.ker L ↔ ∀ j, x ⬝ᵥ N j = 0 := by
    intro x
    rw [LinearMap.mem_ker, hL, Matrix.mulVecLin_apply]
    -- `(A.mulVec x) j = Nⱼ ⬝ᵥ x`, reducing `Matrix.of N j` to `Nⱼ` via `Matrix.of_apply`.
    have hmv : ∀ j, A.mulVec x j = N j ⬝ᵥ x := fun j => by
      simp [hA, Matrix.mulVec, dotProduct, Matrix.of_apply]
    constructor
    · intro hx j; rw [dotProduct_comm, ← hmv]; exact congrFun hx j
    · intro hperp; ext j; simpa [hmv, dotProduct_comm] using hperp j
  -- rank-nullity: `finrank (ker L) ≥ (k+2) - r ≥ m`.
  have hrange : Module.finrank K (LinearMap.range L) ≤ r := by
    refine le_trans (Submodule.finrank_le _) ?_; simp
  have hker : m ≤ Module.finrank K (LinearMap.ker L) := by
    have hrk := L.finrank_range_add_finrank_ker
    rw [show Module.finrank K (Fin (k + 2) → K) = k + 2 from by
      rw [Module.finrank_pi, Fintype.card_fin]] at hrk
    omega
  -- `exists_linearIndependent_of_le_finrank` extracts an LI family `f : Fin m → ker L`.
  obtain ⟨f, hfli⟩ := exists_linearIndependent_of_le_finrank (R := K) (M := LinearMap.ker L) hker
  -- `p i = (f i).val`, which lies in `ker L` hence is orthogonal to every normal.
  refine ⟨fun i => (f i).val, ?_, fun i j => (hmemW _).mp (f i).prop j⟩
  -- LI of `f` in the subtype lifts to LI of `p = f.val` in the ambient space.
  exact hfli.map' L.ker.subtype (Submodule.ker_subtype _)

/-- **Three independent vectors orthogonal to a normal of `K⁴`**: for `n : K⁴`, there are three
linearly independent vectors orthogonal to `n` (all of `K⁴` when `n = 0`), the case `r = 1`,
`m = 3`, `k = 2` of `exists_linearIndependent_perp_of_normals`. It serves
`lem:extensor-pair-through-point` and `lem:extensor-pair-through-given-point`. -/
theorem exists_three_perp (n : Fin 4 → K) :
    ∃ v : Fin 3 → Fin 4 → K, LinearIndependent K v ∧ ∀ i, v i ⬝ᵥ n = 0 := by
  obtain ⟨v, hvli, hperp⟩ :=
    exists_linearIndependent_perp_of_normals (k := 2) ![n] (m := 3) (le_refl 4)
  exact ⟨v, hvli, fun i => by simpa using hperp i 0⟩

/-- **Two independent extensors in one panel of `K^(k+2)`** (the form for `K^(d+1)` after
`lem:extensor-pair-in-panel`): for `1 ≤ k` and `n : K^(k+2)`, there are `p, q : Fin k → K^(k+2)`,
with every `p i` and `q i` orthogonal to `n`, whose extensors are linearly independent in
`ScrewSpace K k`. Katoh and Tanigawa realize the double edge by two coincident panels with two
distinct hinges in them (KT Lemma 5.3, p. 669), and the realizations of the base of KT Theorem 5.5
(`lem:theorem-55-base-producer-single`, `lem:theorem-55-base-producer-parallel`) and of KT Lemma 6.2
(`lem:case-I-realization-nonsimple`) take their hinges from this.

Take `k + 1` linearly independent vectors `v` orthogonal to `n`
(`exists_linearIndependent_perp_of_normals`), and `p = v ∘ Fin.castSucc`, `q = v ∘ Fin.succ`. The
extensors of distinct `k`-subsets of an independent family are independent
(`exteriorPower.ιMulti_family_linearIndependent_field`), and the two subsets are distinct as
`k ≥ 1`; at `k = 0` both are empty. The independence passes to `ScrewSpace K k` through its
injective inclusion into the exterior algebra. -/
theorem exists_linearIndependent_extensor_pair_perp_grade (hk : 1 ≤ k) (n : Fin (k + 2) → K) :
    ∃ p q : Fin k → Fin (k + 2) → K,
      (∀ i, p i ⬝ᵥ n = 0) ∧ (∀ i, q i ⬝ᵥ n = 0) ∧
      LinearIndependent K
        ![(ScrewSpace.mk (extensor p) (extensor_mem_exteriorPower _) : ScrewSpace K k),
          ScrewSpace.mk (extensor q) (extensor_mem_exteriorPower _)] := by
  classical
  -- `k+1` LI vectors in the single panel `n^⊥` (`r = 1, m = k+1`, `(k+1)+1 ≤ k+2`).
  obtain ⟨v, hvli, hvperp⟩ :=
    exists_linearIndependent_perp_of_normals (k := k) ![n] (m := k + 1) (by omega)
  refine ⟨v ∘ Fin.castSucc, v ∘ Fin.succ, ?_, ?_, ?_⟩
  · intro i; simpa using hvperp _ 0
  · intro i; simpa using hvperp _ 0
  · -- The two distinct `k`-subsets of `Fin (k+1)`: `{0,…,k-1}` (castSucc) and `{1,…,k}` (succ).
    set sc : Set.powersetCard (Fin (k + 1)) k :=
      Set.powersetCard.ofFinEmbEquiv Fin.castSuccOrderEmb with hsc
    set ss : Set.powersetCard (Fin (k + 1)) k :=
      Set.powersetCard.ofFinEmbEquiv (Fin.succOrderEmb k) with hss
    -- The whole `ιMulti_family` is LI; restrict to the two-element index family `![sc, ss]`.
    have hfam := exteriorPower.ιMulti_family_linearIndependent_field
      (K := K) (n := k) (v := v) hvli
    have hscss : sc ≠ ss := by
      rw [hsc, hss, Ne, Set.powersetCard.ofFinEmbEquiv.apply_eq_iff_eq]
      intro he
      -- The two embeddings differ at index `0`: `castSucc 0 = 0 ≠ 1 = succ 0` (needs `1 ≤ k`).
      have := congrArg (fun f => (f : Fin k ↪o Fin (k + 1)) ⟨0, hk⟩) he
      simp [Fin.castSuccOrderEmb, Fin.succOrderEmb, Fin.castSucc, Fin.succ,
        Fin.castAdd, Fin.castLE, Fin.ext_iff] at this
    have hidx_inj : Function.Injective (![sc, ss] : Fin 2 → Set.powersetCard (Fin (k + 1)) k) := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all
    have hpair := hfam.comp _ hidx_inj
    -- Identify `ιMulti_family v sc/ss` (as `⋀^k`-members) with the goal's two extensors.
    have hval_c : (exteriorPower.ιMulti_family K k v sc
        : ↥(⋀[K]^k (Fin (k + 2) → K)))
        = ⟨extensor (v ∘ Fin.castSucc), extensor_mem_exteriorPower _⟩ := by
      apply Subtype.ext
      rw [exteriorPower.ιMulti_family_apply_coe, hsc, ExteriorAlgebra.ιMulti_family,
        Set.powersetCard.ofFinEmbEquiv.symm_apply_apply]
      rfl
    have hval_s : (exteriorPower.ιMulti_family K k v ss
        : ↥(⋀[K]^k (Fin (k + 2) → K)))
        = ⟨extensor (v ∘ Fin.succ), extensor_mem_exteriorPower _⟩ := by
      apply Subtype.ext
      rw [exteriorPower.ιMulti_family_apply_coe, hss, ExteriorAlgebra.ιMulti_family,
        Set.powersetCard.ofFinEmbEquiv.symm_apply_apply]
      rfl
    -- Transport LI through the injective inclusion `ScrewSpace K k ↪ ExteriorAlgebra`.
    rw [← LinearMap.linearIndependent_iff
      ((⋀[K]^k (Fin (k + 2) → K)).subtype.comp (ScrewSpace.equivExteriorPower K k).toLinearMap)
      (by rw [LinearMap.ker_comp, Submodule.ker_subtype, Submodule.comap_bot, LinearEquiv.ker])]
    -- `Subtype.val ∘ equivExteriorPower = ScrewSpace.val`, so the transported `mk`-extensor's
    -- ambient value is just its `extensor`.
    have hcoe : ∀ C : ScrewSpace K k,
        ((⋀[K]^k (Fin (k + 2) → K)).subtype.comp
          (ScrewSpace.equivExteriorPower K k).toLinearMap) C = C.val := fun _ => rfl
    -- The transported family equals `Subtype.val ∘ ιMulti_family v ∘ ![sc, ss]`.
    have hfun : ((⋀[K]^k (Fin (k + 2) → K)).subtype.comp
        (ScrewSpace.equivExteriorPower K k).toLinearMap) ∘
        ![(ScrewSpace.mk (extensor (v ∘ Fin.castSucc))
            (extensor_mem_exteriorPower _) : ScrewSpace K k),
          ScrewSpace.mk (extensor (v ∘ Fin.succ)) (extensor_mem_exteriorPower _)]
        = (Subtype.val ∘ exteriorPower.ιMulti_family K k v) ∘ ![sc, ss] := by
      ext i
      fin_cases i
      · simp only [Function.comp_apply, hcoe]
        exact (congrArg Subtype.val hval_c).symm
      · simp only [Function.comp_apply, hcoe]
        exact (congrArg Subtype.val hval_s).symm
    rw [hfun, Function.comp_assoc]
    -- LI of the subtype-valued `hpair` lifts through the injective `Submodule.subtype`.
    exact hpair.map' (⋀[K]^k (Fin (k + 2) → K)).subtype (Submodule.ker_subtype _)

/-- **Two independent extensors in one plane of `K⁴`** (`lem:extensor-pair-in-panel`): the case
`k = 2` of `exists_linearIndependent_extensor_pair_perp_grade`. No declaration uses it; the
realizations use the form for every `k`. -/
theorem exists_linearIndependent_extensor_pair_perp (n : Fin 4 → K) :
    ∃ p q : Fin 2 → Fin 4 → K,
      (∀ i, p i ⬝ᵥ n = 0) ∧ (∀ i, q i ⬝ᵥ n = 0) ∧
      LinearIndependent K
        ![(ScrewSpace.mk (extensor p) (extensor_mem_exteriorPower _) : ScrewSpace K 2),
          ScrewSpace.mk (extensor q) (extensor_mem_exteriorPower _)] :=
  exists_linearIndependent_extensor_pair_perp_grade (k := 2) (by norm_num) n

/-- **The panel support extensor as a join** (`lem:panel-support-extensor-join`): for `k ≥ 1` and
linearly independent normals `n₁ n₂ : K^(k+2)`, `C(n₁, n₂)` is the extensor of some `k` vectors
`p i`, each orthogonal to `n₁` and `n₂`. Take `k` linearly independent vectors `q` orthogonal to
both (`exists_linearIndependent_perp_of_normals`). By
`extensor_join_proportional_complementIso_meet` (`lem:meet-two-hyperplanes`),
`c • C(n₁, n₂) = extensor q` for some `c`, and `c ≠ 0` as `extensor q ≠ 0`
(`extensor_ne_zero_iff_linearIndependent`). Replacing `q 0` by `c⁻¹ • q 0` (`extensor_update_smul`)
gives `p`, still orthogonal to both normals. -/
theorem exists_extensor_eq_panelSupportExtensor_gen [NeZero k] {n₁ n₂ : Fin (k + 2) → K}
    (h : LinearIndependent K ![n₁, n₂]) :
    ∃ p : Fin k → Fin (k + 2) → K,
      (panelSupportExtensor (k := k) n₁ n₂).val = extensor p ∧
      ∀ i, p i ⬝ᵥ n₁ = 0 ∧ p i ⬝ᵥ n₂ = 0 := by
  -- Step 1: `k` LI common-perp points of `![n₁, n₂]`.
  obtain ⟨q, hqli, hqperp⟩ :=
    exists_linearIndependent_perp_of_normals (k := k) ![n₁, n₂] (m := k) (le_refl _)
  have hq_perp : ∀ i, q i ⬝ᵥ n₁ = 0 ∧ q i ⬝ᵥ n₂ = 0 :=
    fun i => ⟨by simpa using hqperp i 0, by simpa using hqperp i 1⟩
  -- Step 2: the meet of two hyperplanes, with the hypotheses in `Module.Basis.toDual` form.
  have htoDual : ∀ i j,
      (Pi.basisFun K (Fin (k + 2))).toDual (q i) ((![n₁, n₂] : Fin 2 → _) j) = 0 := by
    intro i j
    rw [Pi.basisFun_toDual_apply]
    fin_cases j
    · simpa [dotProduct] using (hq_perp i).1
    · simpa [dotProduct] using (hq_perp i).2
  obtain ⟨c, hc⟩ :=
    extensor_join_proportional_complementIso_meet (k := k) ![n₁, n₂] q hqli h htoDual
  -- `c ≠ 0`: `extensor q ≠ 0` (LI of `q`), so the proportionality scalar is invertible.
  have hqne : (⟨extensor q, extensor_mem_exteriorPower q⟩ : ⋀[K]^k (Fin (k + 2) → K)) ≠ 0 := by
    rw [Ne, Subtype.ext_iff]; exact (extensor_ne_zero_iff_linearIndependent q).2 hqli
  have hcne : c ≠ 0 := by
    rintro rfl; rw [zero_smul] at hc; exact hqne hc.symm
  -- Step 3: rescale the first slot of `q` by `c⁻¹`. From `hc` (in `⋀^k`):
  -- `c • complementIso X = ⟨extensor q⟩`, so `complementIso X = c⁻¹ • ⟨extensor q⟩`.
  have hcomp : (panelSupportExtensor (k := k) n₁ n₂).val = c⁻¹ • extensor q := by
    have hc' : (complementIso (k := k) (j := 2) (by omega)
        ⟨extensor ![n₁, n₂], extensor_mem_exteriorPower _⟩ :
          ⋀[K]^k (Fin (k + 2) → K))
        = c⁻¹ • (⟨extensor q, extensor_mem_exteriorPower q⟩ : ⋀[K]^k (Fin (k + 2) → K)) := by
      rw [← hc]; exact (inv_smul_smul₀ hcne _).symm
    rw [panelSupportExtensor_eq_complementIso_extensor]
    have := congrArg (Subtype.val (p := fun x => x ∈ ⋀[K]^k (Fin (k + 2) → K))) hc'
    simpa only [Submodule.coe_smul, ScrewSpace.val] using this
  refine ⟨Function.update q 0 (c⁻¹ • q 0), ?_, fun i => ?_⟩
  · -- `(panelSupportExtensor n₁ n₂).val = extensor (update q 0 (c⁻¹ • q 0))`.
    rw [extensor_update_smul]; exact hcomp
  · -- Orthogonality of `update q 0 (c⁻¹ • q 0)` to both normals.
    rcases eq_or_ne i 0 with rfl | hi
    · rw [Function.update_self]
      exact ⟨by rw [smul_dotProduct, (hq_perp 0).1, smul_zero],
        by rw [smul_dotProduct, (hq_perp 0).2, smul_zero]⟩
    · rw [Function.update_of_ne hi]; exact hq_perp i

/-- **The panel support extensor as a join, in `K⁴`**: the case `k = 2` of
`exists_extensor_eq_panelSupportExtensor_gen`. Its users are `extensorInPanel_panelSupportExtensor`
and two lemmas of `Molecule/Pencil/Statement.lean` (`lem:pencil-transport-in-to-through`,
`lem:pencil-transport-through-to-in`). -/
theorem exists_extensor_eq_panelSupportExtensor {n₁ n₂ : Fin 4 → K}
    (h : LinearIndependent K ![n₁, n₂]) :
    ∃ p : Fin 2 → Fin 4 → K,
      (panelSupportExtensor (k := 2) n₁ n₂).val = extensor p ∧
      ∀ i, p i ⬝ᵥ n₁ = 0 ∧ p i ⬝ᵥ n₂ = 0 :=
  exists_extensor_eq_panelSupportExtensor_gen (k := 2) h

/-- **The panel support extensor lies in both panels** (`ExtensorInPanel`,
`def:genuine-hinge-realization`): for linearly independent `n₁ n₂ : K⁴`, `C(n₁, n₂)` lies in the
panel of `n₁` and in that of `n₂`, the same vectors serving for both
(`exists_extensor_eq_panelSupportExtensor`). It serves `lem:cycle-pencil-realization`. -/
theorem extensorInPanel_panelSupportExtensor {n₁ n₂ : Fin 4 → K}
    (h : LinearIndependent K ![n₁, n₂]) :
    ExtensorInPanel (panelSupportExtensor (k := 2) n₁ n₂) n₁ ∧
    ExtensorInPanel (panelSupportExtensor (k := 2) n₁ n₂) n₂ := by
  obtain ⟨p, heq, hperp⟩ := exists_extensor_eq_panelSupportExtensor h
  exact ⟨⟨p, heq, fun i => (hperp i).1⟩, ⟨p, heq, fun i => (hperp i).2⟩⟩

/-- **A nonzero extensor in two panels**: for any `n₁ n₂ : K^(k+2)`, some nonzero
`C : ScrewSpace K k` lies in both panels (`ExtensorInPanel`). The vectors orthogonal to `n₁` and
`n₂` form a space of dimension at least `k` whether or not `n₁` and `n₂` are independent
(`exists_linearIndependent_perp_of_normals`), and the extensor of `k` independent ones is nonzero
(`extensor_ne_zero_iff_linearIndependent`). The proof of KT Lemma 6.1
(`lem:case-cut-edge-realization`) takes the hinge of the cut edge from it. -/
theorem exists_extensor_in_two_panels_grade (n₁ n₂ : Fin (k + 2) → K) :
    ∃ C : ScrewSpace K k, C ≠ 0 ∧ ExtensorInPanel C n₁ ∧ ExtensorInPanel C n₂ := by
  -- `k` LI common-perp points in `n₁^⊥ ∩ n₂^⊥` (dim ≥ k), with no transversality needed.
  obtain ⟨p, hpli, hperp⟩ :=
    exists_linearIndependent_perp_of_normals (k := k) ![n₁, n₂] (m := k) (by omega)
  have hp_perp : ∀ i, p i ⬝ᵥ n₁ = 0 ∧ p i ⬝ᵥ n₂ = 0 :=
    fun i => ⟨by simpa using hperp i 0, by simpa using hperp i 1⟩
  -- Build `C = mk (extensor p) _ : ScrewSpace K k`.
  refine ⟨ScrewSpace.mk (extensor p) (extensor_mem_exteriorPower _), ?_,
         ⟨p, rfl, fun i => (hp_perp i).1⟩, ⟨p, rfl, fun i => (hp_perp i).2⟩⟩
  -- `C ≠ 0` because `extensor p ≠ 0`, which follows from `hpli`.
  intro heq
  exact (extensor_ne_zero_iff_linearIndependent p).mpr hpli (congr_arg ScrewSpace.val heq)

/-- **At most one shear makes a normal dependent on another**: if `n_a` and `n_b` are linearly
independent, at most one `t` makes `n_a + t • n'` and `n_b` linearly dependent. For two such
`t₁ ≠ t₂`, with `c₁ • n_b = n_a + t₁ • n'` and `c₂ • n_b = n_a + t₂ • n'`, subtracting puts `n'` in
`span {n_b}`, and then `n_a` too. Case III (`PanelHingeFramework.case_III_realization_of_rank`)
passes this set of `t` to `PanelHingeFramework.caseIIICandidate_exists_good_shear`, which chooses a
shear outside it. -/
theorem setOf_not_shear_linearIndependent_subsingleton (n_a n' n_b : Fin (k + 2) → K)
    (hgab : LinearIndependent K ![n_a, n_b]) :
    {t : K | ¬ LinearIndependent K ![n_a + t • n', n_b]}.Subsingleton := by
  -- `n_b ≠ 0` (the second entry of the independent pair `![n_a, n_b]`).
  have hn_b : n_b ≠ 0 := by
    have := hgab.ne_zero 1; simpa using this
  -- No multiple of `n_b` is `n_a`: `![n_b, n_a]` is independent (`LinearIndependent.pair_iff'`).
  have hgba : LinearIndependent K ![n_b, n_a] := by
    have hsw : (![n_a, n_b] : Fin 2 → Fin (k + 2) → K) ∘ Equiv.swap 0 1 = ![n_b, n_a] := by
      funext i; fin_cases i <;> simp
    rw [← hsw]; exact hgab.comp _ (Equiv.swap 0 1).injective
  have hna_not : ∀ c : K, c • n_b ≠ n_a := (LinearIndependent.pair_iff' hn_b).mp hgba
  -- A value `t` is *bad* when `n_a + t • n'` is collinear with `n_b`, i.e. `c • n_b = n_a + t•n'`
  -- for some `c` (the pair `![n_b, n_a + t•n']` dependent; `LinearIndependent.pair_iff'`).
  have hbad : ∀ t : K, ¬ LinearIndependent K ![n_a + t • n', n_b] →
      ∃ c : K, c • n_b = n_a + t • n' := by
    intro t hb
    -- `![n_a + t•n', n_b]` dep ⟺ `![n_b, n_a + t•n']` dep ⟺ `¬ ∀ c, c • n_b ≠ n_a + t•n'`.
    have hbsw : ¬ LinearIndependent K ![n_b, n_a + t • n'] := by
      intro h
      apply hb
      have hsw : (![n_b, n_a + t • n'] : Fin 2 → Fin (k + 2) → K) ∘ Equiv.swap 0 1
          = ![n_a + t • n', n_b] := by funext i; fin_cases i <;> simp
      rw [← hsw]; exact h.comp _ (Equiv.swap 0 1).injective
    rw [LinearIndependent.pair_iff' hn_b] at hbsw
    push Not at hbsw
    exact hbsw
  -- Any two bad `t`s coincide.
  intro t₁ hb₁ t₂ hb₂
  by_contra hne
  obtain ⟨c₁, hc₁⟩ := hbad t₁ hb₁
  obtain ⟨c₂, hc₂⟩ := hbad t₂ hb₂
  -- Subtract `c₁ • n_b = n_a + t₁•n'` and `c₂ • n_b = n_a + t₂•n'`:
  -- `(c₁ - c₂) • n_b = (t₁ - t₂) • n'`, so `n' = ((c₁-c₂)/(t₁-t₂)) • n_b` (`t₁ ≠ t₂`).
  have htd : t₁ - t₂ ≠ 0 := sub_ne_zero.mpr hne
  have hsub : (c₁ - c₂) • n_b = (t₁ - t₂) • n' := by
    simp only [sub_smul, hc₁, hc₂]; abel
  have hn' : n' = ((c₁ - c₂) / (t₁ - t₂)) • n_b := by
    simp only [div_eq_inv_mul, mul_smul, hsub, inv_smul_smul₀ htd]
  -- Then `n_a = c₁ • n_b - t₁ • n' ∈ span {n_b}`, contradicting `hna_not`.
  apply hna_not (c₁ - t₁ * ((c₁ - c₂) / (t₁ - t₂)))
  rw [sub_smul, mul_smul, ← hn', hc₁]; abel

/-- **The panel support extensors of a family of pairs of normals are the images of their joins** (a
step of `lem:panel-support-extensor-independence`):
`(fun i ↦ C(n₁ i, n₂ i)) = complementIso ∘ (fun i ↦ normalsJoin (n₁ i) (n₂ i))`, by definition. -/
theorem panelSupportExtensor_eq_complementIso_comp_normalsJoin
    {m : ℕ} (n₁ n₂ : Fin m → Fin (k + 2) → K) :
    (fun i => panelSupportExtensor (n₁ i) (n₂ i)) =
      (complementIso (k := k) (j := 2) (by omega)) ∘ (fun i => normalsJoin (n₁ i) (n₂ i)) := by
  funext i
  rfl

/-- **Independence of panel support extensors** (`lem:panel-support-extensor-independence`): the
extensors `C(n₁ i, n₂ i)`, `i < m`, are linearly independent iff the joins `n₁ i ∨ n₂ i` are, as the
complement isomorphism is a linear isomorphism (`complementIso`). The proofs of
`lem:exists-independent-panel-extensor`, `lem:triangle-normals`, `lem:cycle-normals` and KT
Lemma 6.5 (`lem:case-I-realization-h65`) use it. -/
theorem panelSupportExtensor_linearIndependent_iff
    {m : ℕ} (n₁ n₂ : Fin m → Fin (k + 2) → K) :
    LinearIndependent K (fun i => panelSupportExtensor (n₁ i) (n₂ i)) ↔
      LinearIndependent K (fun i => normalsJoin (n₁ i) (n₂ i)) := by
  rw [panelSupportExtensor_eq_complementIso_comp_normalsJoin]
  exact (complementIso (k := k) (j := 2) (by omega)).toLinearMap.linearIndependent_iff_of_injOn
    (LinearMap.injOn_of_disjoint_ker le_rfl (by simp [LinearEquiv.ker]))

/-- **The join of two standard basis vectors is a basis vector of `⋀² K^(k+2)`** (a step of
`lem:exists-independent-panel-extensor`, `lem:triangle-normals` and `lem:cycle-normals`): for
`s = {i < j}`, the join of the standard basis vectors `e_i` and `e_j` is the member at `s` of the
basis family `exteriorPower.ιMulti_family K 2 (Pi.basisFun K (Fin (k+2)))`, by definition
(`Set.powersetCard.ofFinEmbEquiv_symm_apply`). -/
theorem normalsJoin_basisFun_orderEmbOfFin (s : Set.powersetCard (Fin (k + 2)) 2) :
    normalsJoin (Pi.basisFun K (Fin (k + 2)) ((s : Finset (Fin (k + 2))).orderEmbOfFin s.2 0))
      (Pi.basisFun K (Fin (k + 2)) ((s : Finset (Fin (k + 2))).orderEmbOfFin s.2 1))
      = exteriorPower.ιMulti_family K 2 (Pi.basisFun K (Fin (k + 2))) s := by
  rw [normalsJoin]
  apply Subtype.ext
  rw [exteriorPower.ιMulti_apply_coe, exteriorPower.ιMulti_family_apply_coe]
  congr 1
  rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
  ext i; fin_cases i <;> rfl

/-- **Up to `D` independent joins of standard basis vectors**
(`lem:exists-independent-panel-extensor`): for `m ≤ D = screwDim k`, there are `m` pairs of normals
whose joins are linearly independent in `⋀² K^(k+2)`. The 2-element subsets of `Fin (k+2)` number
`D` (`Set.powersetCard.card`), so `m` of them can be chosen, and the joins of the corresponding
pairs of standard basis vectors are members of a basis (`normalsJoin_basisFun_orderEmbOfFin`,
`exteriorPower.ιMulti_family_linearIndependent_ofBasis`). The pairs need not be the normals of the
ends of the edges of a cycle (the remark after `lem:exists-independent-panel-extensor`); those of
`exists_cycle_normals` are. -/
theorem exists_independent_normalsJoin {m : ℕ} (hm : m ≤ screwDim k) :
    ∃ n₁ n₂ : Fin m → Fin (k + 2) → K,
      LinearIndependent K (fun i => normalsJoin (n₁ i) (n₂ i)) := by
  have hcard : Fintype.card (Set.powersetCard (Fin (k + 2)) 2) = screwDim k := by
    rw [← Nat.card_eq_fintype_card, Set.powersetCard.card, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  obtain ⟨g⟩ : Nonempty (Fin m ↪ Set.powersetCard (Fin (k + 2)) 2) := by
    apply Function.Embedding.nonempty_of_card_le
    rw [Fintype.card_fin, hcard]; exact hm
  set b := Pi.basisFun K (Fin (k + 2)) with hb
  refine ⟨fun i => b ((↑(g i) : Finset (Fin (k + 2))).orderEmbOfFin (g i).2 0),
    fun i => b ((↑(g i) : Finset (Fin (k + 2))).orderEmbOfFin (g i).2 1), ?_⟩
  have hfam : (fun i => normalsJoin (b ((↑(g i) : Finset (Fin (k + 2))).orderEmbOfFin (g i).2 0))
      (b ((↑(g i) : Finset (Fin (k + 2))).orderEmbOfFin (g i).2 1)))
      = (exteriorPower.ιMulti_family K 2 b) ∘ g := by
    funext i; exact normalsJoin_basisFun_orderEmbOfFin (g i)
  rw [hfam]
  exact (exteriorPower.ιMulti_family_linearIndependent_ofBasis K 2 b).comp g g.injective

/-- **Up to `D` independent panel support extensors** (`lem:exists-independent-panel-extensor`): for
`m ≤ D`, there are `m` pairs of normals whose panel support extensors are linearly independent, from
`exists_independent_normalsJoin` and `panelSupportExtensor_linearIndependent_iff`. The bound `m ≤ D`
is `lem:cycle-realization-dim-bound`. No declaration uses the lemma: the realization of a cycle
takes its normals from `exists_cycle_normals` (`rem:case-I-kt-steps`). -/
theorem exists_independent_panelSupportExtensor {m : ℕ} (hm : m ≤ screwDim k) :
    ∃ n₁ n₂ : Fin m → Fin (k + 2) → K,
      LinearIndependent K (fun i => panelSupportExtensor (n₁ i) (n₂ i)) := by
  obtain ⟨n₁, n₂, h⟩ := exists_independent_normalsJoin (K := K) (k := k) hm
  exact ⟨n₁, n₂, (panelSupportExtensor_linearIndependent_iff n₁ n₂).mpr h⟩

/-- **The pairs of an independent triple are independent** (a step of `lem:case-I-realization-h65`):
from `LinearIndependent K ![n₀, n₁, n₂]`, the pairs `![n₀, n₁]`, `![n₀, n₂]` and `![n₁, n₂]` are
linearly independent (`LinearIndependent.comp` along the three embeddings of `Fin 2`). -/
theorem triLI_subpairs (n₀ n₁ n₂ : Fin (k + 2) → K)
    (htriLI : LinearIndependent K (![n₀, n₁, n₂] : Fin 3 → Fin (k + 2) → K)) :
    LinearIndependent K (![n₀, n₁] : Fin 2 → Fin (k + 2) → K) ∧
      LinearIndependent K (![n₀, n₂] : Fin 2 → Fin (k + 2) → K) ∧
      LinearIndependent K (![n₁, n₂] : Fin 2 → Fin (k + 2) → K) := by
  set T : Fin 3 → Fin (k + 2) → K := ![n₀, n₁, n₂] with hT
  refine ⟨?_, ?_, ?_⟩
  · have h := htriLI.comp (![0, 1] : Fin 2 → Fin 3) (by decide)
    have he : T ∘ (![0, 1] : Fin 2 → Fin 3) = ![n₀, n₁] := by funext i; fin_cases i <;> rfl
    rwa [he] at h
  · have h := htriLI.comp (![0, 2] : Fin 2 → Fin 3) (by decide)
    have he : T ∘ (![0, 2] : Fin 2 → Fin 3) = ![n₀, n₂] := by funext i; fin_cases i <;> rfl
    rwa [he] at h
  · have h := htriLI.comp (![1, 2] : Fin 2 → Fin 3) (by decide)
    have he : T ∘ (![1, 2] : Fin 2 → Fin 3) = ![n₁, n₂] := by funext i; fin_cases i <;> rfl
    rwa [he] at h

/-- **Two joins with a common normal are independent if the three normals are** (a step of
`lem:case-I-realization-h65`): if `n_v`, `n_a` and `n_b` are linearly independent, so are
`n_v ∨ n_a` and `n_v ∨ n_b`. In the proof of KT Lemma 6.5 the hinges of `va` and `vb` are then
independent, as the panel of `v` does not contain the intersection of those of `a` and `b` (KT
p. 676).

A relation `c₁ (n_v ∨ n_a) + c₂ (n_v ∨ n_b) = 0` is `n_v ∨ (c₁ n_a + c₂ n_b) = 0`, by the linearity
of the join and `normalsJoin_swap`. If `c₁ n_a + c₂ n_b ≠ 0`, it and `n_v` are then dependent
(`normalsJoin_ne_zero_iff`), against the independence of the three; otherwise `c₁ = c₂ = 0`, as
`n_a` and `n_b` are independent. -/
theorem normalsJoin_pair_linearIndependent_of_triLI
    (n_v n_a n_b : Fin (k + 2) → K)
    (htriLI : LinearIndependent K (![n_v, n_a, n_b] : Fin 3 → Fin (k + 2) → K)) :
    LinearIndependent K
      (![normalsJoin (k := k) n_v n_a, normalsJoin (k := k) n_v n_b] : Fin 2 → _) := by
  obtain ⟨hLI_va, -, hLI_ab⟩ := triLI_subpairs n_v n_a n_b htriLI
  rw [LinearIndependent.pair_iff]
  intro c₁ c₂ hcomb
  -- `hcomb : c₁ • normalsJoin n_v n_a + c₂ • normalsJoin n_v n_b = 0`; rewrite to a single join.
  have hjoin : normalsJoin (k := k) n_v (c₁ • n_a + c₂ • n_b) = 0 := by
    have hrw : normalsJoin (k := k) n_v (c₁ • n_a + c₂ • n_b)
        = c₁ • normalsJoin (k := k) n_v n_a + c₂ • normalsJoin (k := k) n_v n_b := by
      simp only [normalsJoin_swap (c₁ • n_a + c₂ • n_b) n_v, normalsJoin_add_left,
        normalsJoin_smul_left, normalsJoin_swap n_a n_v, normalsJoin_swap n_b n_v,
        smul_neg, neg_add_rev]
      abel
    rw [hrw]; exact hcomb
  by_cases hcomb0 : c₁ • n_a + c₂ • n_b = (0 : Fin (k + 2) → K)
  · exact LinearIndependent.pair_iff.mp hLI_ab c₁ c₂ hcomb0
  · exfalso
    have hnotLI : ¬LinearIndependent K (![n_v, c₁ • n_a + c₂ • n_b] : Fin 2 → Fin (k + 2) → K) := by
      intro hLI
      exact absurd ((normalsJoin_ne_zero_iff n_v _).mpr hLI) (by rwa [ne_eq, not_not])
    rw [LinearIndependent.pair_iff] at hnotLI
    push Not at hnotLI
    obtain ⟨s₁, s₂, hscomb, hne⟩ := hnotLI
    have hsc₂ : s₂ ≠ 0 := by
      intro h
      rw [h, zero_smul, add_zero] at hscomb
      have hn_v_ne : n_v ≠ 0 := LinearIndependent.ne_zero (i := (0 : Fin 2)) hLI_va
      exact hne ((smul_eq_zero.mp hscomb).resolve_right hn_v_ne) h
    have htri_dep : s₁ • n_v + (s₂ * c₁) • n_a + (s₂ * c₂) • n_b = (0 : Fin (k + 2) → K) := by
      funext i
      have hi := congr_fun hscomb i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hi ⊢
      linear_combination hi
    have htriLI_iff := Fintype.linearIndependent_iff.mp htriLI
    have hcoeffs_zero := htriLI_iff (![s₁, s₂ * c₁, s₂ * c₂]) (by
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one]
      exact htri_dep)
    have hc₁ : c₁ = 0 :=
      (mul_eq_zero.mp (by have := hcoeffs_zero 1; simpa using this)).resolve_left hsc₂
    have hc₂ : c₂ = 0 :=
      (mul_eq_zero.mp (by have := hcoeffs_zero 2; simpa using this)).resolve_left hsc₂
    exact hcomb0 (by rw [hc₁, hc₂]; simp)

-- Private helpers for `exists_triangle_normals` below.
-- Extracted as standalone lemmas to avoid context-explosion timeouts in the main proof.

/-- The join of two standard basis vectors `e_i` and `e_j` with `i < j` is nonzero: it is the member
at `{i, j}` of the basis family of `⋀² K^(k+2)` (`normalsJoin_basisFun_orderEmbOfFin`), which is
linearly independent (`exteriorPower.ιMulti_family_linearIndependent_ofBasis`). -/
private theorem normalsJoin_basisFun_ne_zero_of_lt {i j : Fin (k + 2)} (h : i < j) :
    normalsJoin (Pi.basisFun K (Fin (k + 2)) i) (Pi.basisFun K (Fin (k + 2)) j) ≠ 0 := by
  have hcard := Finset.card_pair (Fin.ne_of_lt h)
  have hne := (exteriorPower.ιMulti_family_linearIndependent_ofBasis K 2
    (Pi.basisFun K (Fin (k + 2)))).ne_zero ⟨{i, j}, hcard⟩
  have hoE0 : ({i, j} : Finset (Fin (k + 2))).orderEmbOfFin hcard 0 = i := by
    have := @Finset.orderEmbOfFin_zero (Fin (k + 2)) _ {i, j} 2 hcard (by norm_num)
    simp only [show (⟨0, by norm_num⟩ : Fin 2) = 0 from rfl] at this
    rw [this]; simp [Finset.min'_insert, Finset.min'_singleton, le_of_lt h]
  have hoE1 : ({i, j} : Finset (Fin (k + 2))).orderEmbOfFin hcard 1 = j := by
    have := @Finset.orderEmbOfFin_last (Fin (k + 2)) _ {i, j} 2 hcard (by norm_num)
    simp only [show (⟨2 - 1, by norm_num⟩ : Fin 2) = 1 from rfl] at this
    rw [this]; simp [Finset.max'_insert, Finset.max'_singleton, le_of_lt h]
  rw [← normalsJoin_basisFun_orderEmbOfFin, hoE0, hoE1] at hne
  exact hne

/-- The join of two standard-basis vectors `eᵢ eⱼ` (for `i < j`) equals the `{i,j}`-member of
the `ιMulti_family` basis. Used to rewrite the sorted-pair family into the `ιMulti_family` range
so that `ιMulti_family_linearIndependent_ofBasis.comp` applies. -/
private theorem normalsJoin_eq_ιMulti_family_pair {i j : Fin (k + 2)} (h : i < j) :
    normalsJoin (Pi.basisFun K (Fin (k + 2)) i) (Pi.basisFun K (Fin (k + 2)) j) =
      exteriorPower.ιMulti_family K 2 (Pi.basisFun K (Fin (k + 2)))
        ⟨{i, j}, Finset.card_pair (Fin.ne_of_lt h)⟩ := by
  have hcard := Finset.card_pair (Fin.ne_of_lt h)
  rw [← normalsJoin_basisFun_orderEmbOfFin ⟨{i, j}, hcard⟩]
  congr 2
  · have := @Finset.orderEmbOfFin_zero (Fin (k + 2)) _ {i, j} 2 hcard (by norm_num)
    simp only [show (⟨0, by norm_num⟩ : Fin 2) = 0 from rfl] at this
    rw [this]; simp [Finset.min'_insert, Finset.min'_singleton, le_of_lt h]
  · have := @Finset.orderEmbOfFin_last (Fin (k + 2)) _ {i, j} 2 hcard (by norm_num)
    simp only [show (⟨2 - 1, by norm_num⟩ : Fin 2) = 1 from rfl] at this
    rw [this]; simp [Finset.max'_insert, Finset.max'_singleton, le_of_lt h]

/-- The joins of the cyclic pairs `(e₀, e₁)`, `(e₁, e₂)`, `(e₂, e₀)` are unit multiples of those of
the sorted pairs `(e₀, e₁)`, `(e₁, e₂)`, `(e₀, e₂)`, by `1`, `1` and `−1` (`normalsJoin_swap`). So
`LinearIndependent.units_smul_iff` reduces the independence of the first family to that of the
second. -/
private theorem basisFun3_normalsJoin_cyclic_eq_units_smul (hk : 1 ≤ k) :
    (fun i => normalsJoin
      (![Pi.basisFun K (Fin (k + 2)) ⟨0, by omega⟩,
         Pi.basisFun K (Fin (k + 2)) ⟨1, by omega⟩,
         Pi.basisFun K (Fin (k + 2)) ⟨2, by omega⟩] i)
      (![Pi.basisFun K (Fin (k + 2)) ⟨1, by omega⟩,
         Pi.basisFun K (Fin (k + 2)) ⟨2, by omega⟩,
         Pi.basisFun K (Fin (k + 2)) ⟨0, by omega⟩] i)) =
    (![Units.mk0 (1 : K) (by norm_num), Units.mk0 (1 : K) (by norm_num),
        Units.mk0 (-1 : K) (by norm_num)] : Fin 3 → Kˣ) •
    (![normalsJoin (Pi.basisFun K (Fin (k + 2)) ⟨0, by omega⟩)
                   (Pi.basisFun K (Fin (k + 2)) ⟨1, by omega⟩),
       normalsJoin (Pi.basisFun K (Fin (k + 2)) ⟨1, by omega⟩)
                   (Pi.basisFun K (Fin (k + 2)) ⟨2, by omega⟩),
       normalsJoin (Pi.basisFun K (Fin (k + 2)) ⟨0, by omega⟩)
                   (Pi.basisFun K (Fin (k + 2)) ⟨2, by omega⟩)] : Fin 3 → _) := by
  funext i; fin_cases i
  · change normalsJoin (Pi.basisFun K (Fin (k + 2)) ⟨0, by omega⟩)
                       (Pi.basisFun K (Fin (k + 2)) ⟨1, by omega⟩)
           = (Units.mk0 (1 : K) (by norm_num) : Kˣ) •
               normalsJoin (Pi.basisFun K (Fin (k + 2)) ⟨0, by omega⟩)
                           (Pi.basisFun K (Fin (k + 2)) ⟨1, by omega⟩)
    rw [Units.smul_def, Units.val_mk0, one_smul]
  · change normalsJoin (Pi.basisFun K (Fin (k + 2)) ⟨1, by omega⟩)
                       (Pi.basisFun K (Fin (k + 2)) ⟨2, by omega⟩)
           = (Units.mk0 (1 : K) (by norm_num) : Kˣ) •
               normalsJoin (Pi.basisFun K (Fin (k + 2)) ⟨1, by omega⟩)
                           (Pi.basisFun K (Fin (k + 2)) ⟨2, by omega⟩)
    rw [Units.smul_def, Units.val_mk0, one_smul]
  · change normalsJoin (Pi.basisFun K (Fin (k + 2)) ⟨2, by omega⟩)
                       (Pi.basisFun K (Fin (k + 2)) ⟨0, by omega⟩)
           = (Units.mk0 (-1 : K) (by norm_num) : Kˣ) •
               normalsJoin (Pi.basisFun K (Fin (k + 2)) ⟨0, by omega⟩)
                           (Pi.basisFun K (Fin (k + 2)) ⟨2, by omega⟩)
    rw [normalsJoin_swap, Units.smul_def, Units.val_mk0]; module

/-- The sorted normal family `(e₀,e₁), (e₁,e₂), (e₀,e₂)` equals `ιMulti_family ∘ index-map`,
where the index map sends each position to the corresponding 2-element subset `{eᵢ, eⱼ}`.
Uses `let` for `h01 h12 h02` so that after `intro`, the proof terms in the goal exactly match
`Finset.card_pair (Fin.ne_of_lt hXX)`, enabling `normalsJoin_eq_ιMulti_family_pair` directly. -/
private theorem basisFun3_normalsJoin_sorted_family (hk : 1 ≤ k) :
    let h01 : (⟨0, by omega⟩ : Fin (k + 2)) < ⟨1, by omega⟩ := by simp only [Fin.mk_lt_mk]; omega
    let h12 : (⟨1, by omega⟩ : Fin (k + 2)) < ⟨2, by omega⟩ := by simp only [Fin.mk_lt_mk]; omega
    let h02 : (⟨0, by omega⟩ : Fin (k + 2)) < ⟨2, by omega⟩ := by simp only [Fin.mk_lt_mk]; omega
    (![normalsJoin (Pi.basisFun K (Fin (k + 2)) ⟨0, by omega⟩)
                   (Pi.basisFun K (Fin (k + 2)) ⟨1, by omega⟩),
       normalsJoin (Pi.basisFun K (Fin (k + 2)) ⟨1, by omega⟩)
                   (Pi.basisFun K (Fin (k + 2)) ⟨2, by omega⟩),
       normalsJoin (Pi.basisFun K (Fin (k + 2)) ⟨0, by omega⟩)
                   (Pi.basisFun K (Fin (k + 2)) ⟨2, by omega⟩)] : Fin 3 → _)
      = (exteriorPower.ιMulti_family K 2 (Pi.basisFun K (Fin (k + 2)))) ∘
          ![⟨{⟨0, by omega⟩, ⟨1, by omega⟩}, Finset.card_pair (Fin.ne_of_lt h01)⟩,
            ⟨{⟨1, by omega⟩, ⟨2, by omega⟩}, Finset.card_pair (Fin.ne_of_lt h12)⟩,
            ⟨{⟨0, by omega⟩, ⟨2, by omega⟩}, Finset.card_pair (Fin.ne_of_lt h02)⟩] := by
  intro h01 h12 h02
  funext i; fin_cases i
  · exact normalsJoin_eq_ιMulti_family_pair h01
  · exact normalsJoin_eq_ιMulti_family_pair h12
  · exact normalsJoin_eq_ιMulti_family_pair h02

/-- **Normals for a triangle with independent hinges** (`lem:triangle-normals`): for `k ≥ 1`, that
is, `d ≥ 2`, the standard basis vectors `n₀ = e₀`, `n₁ = e₁` and `n₂ = e₂` of `K^(k+2)` have nonzero
joins `n₀ ∨ n₁`, `n₁ ∨ n₂` and `n₂ ∨ n₀`, and linearly independent panel support extensors
`C(n₀, n₁)`, `C(n₁, n₂)` and `C(n₂, n₀)`. Up to the sign of `n₂ ∨ n₀ = −(n₀ ∨ n₂)`, the three joins
are distinct members of the basis of `⋀² K^(k+2)` (`normalsJoin_eq_ιMulti_family_pair`), and
`panelSupportExtensor_linearIndependent_iff` passes their independence to the extensors. Its one
user is `PanelHingeFramework.hasGenericFullRankRealization_of_triangle`
(`lem:triangle-realization`); the realization of a cycle takes its normals from
`exists_cycle_normals`, whose case `m = 3` is this lemma up to the form of the family. -/
theorem exists_triangle_normals (hk : 1 ≤ k) :
    ∃ n₀ n₁ n₂ : Fin (k + 2) → K,
      (normalsJoin n₀ n₁ ≠ 0 ∧ normalsJoin n₁ n₂ ≠ 0 ∧ normalsJoin n₂ n₀ ≠ 0) ∧
      LinearIndependent K
        (fun i => panelSupportExtensor (![n₀, n₁, n₂] i) (![n₁, n₂, n₀] i)) := by
  have h01 : (⟨0, by omega⟩ : Fin (k + 2)) < ⟨1, by omega⟩ := by
    simp only [Fin.mk_lt_mk]; omega
  have h12 : (⟨1, by omega⟩ : Fin (k + 2)) < ⟨2, by omega⟩ := by
    simp only [Fin.mk_lt_mk]; omega
  have h02 : (⟨0, by omega⟩ : Fin (k + 2)) < ⟨2, by omega⟩ := by
    simp only [Fin.mk_lt_mk]; omega
  set s₀₁ : Set.powersetCard (Fin (k + 2)) 2 :=
    ⟨{⟨0, by omega⟩, ⟨1, by omega⟩}, Finset.card_pair (Fin.ne_of_lt h01)⟩ with hs₀₁
  set s₁₂ : Set.powersetCard (Fin (k + 2)) 2 :=
    ⟨{⟨1, by omega⟩, ⟨2, by omega⟩}, Finset.card_pair (Fin.ne_of_lt h12)⟩ with hs₁₂
  set s₀₂ : Set.powersetCard (Fin (k + 2)) 2 :=
    ⟨{⟨0, by omega⟩, ⟨2, by omega⟩}, Finset.card_pair (Fin.ne_of_lt h02)⟩ with hs₀₂
  refine ⟨Pi.basisFun K (Fin (k + 2)) ⟨0, by omega⟩,
          Pi.basisFun K (Fin (k + 2)) ⟨1, by omega⟩,
          Pi.basisFun K (Fin (k + 2)) ⟨2, by omega⟩, ?_, ?_⟩
  · -- Pairwise nonvanishing: each cyclic pair (n₀,n₁), (n₁,n₂), (n₂,n₀) has nJ ≠ 0.
    refine ⟨normalsJoin_basisFun_ne_zero_of_lt h01,
            normalsJoin_basisFun_ne_zero_of_lt h12, ?_⟩
    -- normalsJoin n₂ n₀ = -(normalsJoin n₀ n₂) ≠ 0 since normalsJoin n₀ n₂ ≠ 0.
    rw [normalsJoin_swap]
    exact neg_ne_zero.mpr (normalsJoin_basisFun_ne_zero_of_lt h02)
  · -- Extensor LI: cyclic family is LI via units-smul + ιMulti_family basis LI.
    rw [panelSupportExtensor_linearIndependent_iff,
        basisFun3_normalsJoin_cyclic_eq_units_smul hk,
        LinearIndependent.units_smul_iff,
        basisFun3_normalsJoin_sorted_family hk]
    apply (exteriorPower.ιMulti_family_linearIndependent_ofBasis K 2
      (Pi.basisFun K (Fin (k + 2)))).comp
    -- Injectivity of the three-element index map `![s₀₁, s₁₂, s₀₂]`.
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · change s₀₁ = s₁₂ at hij
      exfalso; simp only [s₀₁, s₁₂] at hij
      have := Finset.ext_iff.mp (Subtype.mk_eq_mk.mp hij) ⟨0, by omega⟩; simp at this
    · change s₀₁ = s₀₂ at hij
      exfalso; simp only [s₀₁, s₀₂] at hij
      have := Finset.ext_iff.mp (Subtype.mk_eq_mk.mp hij) ⟨1, by omega⟩; simp at this
    · change s₁₂ = s₀₁ at hij
      exfalso; simp only [s₁₂, s₀₁] at hij
      have := Finset.ext_iff.mp (Subtype.mk_eq_mk.mp hij) ⟨0, by omega⟩; simp at this
    · rfl
    · change s₁₂ = s₀₂ at hij
      exfalso; simp only [s₁₂, s₀₂] at hij
      have := Finset.ext_iff.mp (Subtype.mk_eq_mk.mp hij) ⟨1, by omega⟩; simp at this
    · change s₀₂ = s₀₁ at hij
      exfalso; simp only [s₀₂, s₀₁] at hij
      have := Finset.ext_iff.mp (Subtype.mk_eq_mk.mp hij) ⟨1, by omega⟩; simp at this
    · change s₀₂ = s₁₂ at hij
      exfalso; simp only [s₀₂, s₁₂] at hij
      have := Finset.ext_iff.mp (Subtype.mk_eq_mk.mp hij) ⟨1, by omega⟩; simp at this
    · rfl

-- Private helpers for `exists_cycle_normals` below.

/-- The grade-2 join of two **distinct** standard-basis vectors is nonzero, in either order:
`normalsJoin eᵢ eⱼ ≠ 0` for `i ≠ j`. Lifts the `i < j` form `normalsJoin_basisFun_ne_zero_of_lt`
to plain distinctness via the antisymmetry `normalsJoin_swap` (the reversed order contributes a
harmless `-1`). -/
private theorem normalsJoin_basisFun_ne_zero_of_ne {i j : Fin (k + 2)} (h : i ≠ j) :
    normalsJoin (Pi.basisFun K (Fin (k + 2)) i) (Pi.basisFun K (Fin (k + 2)) j) ≠ 0 := by
  rcases lt_or_gt_of_ne h with hlt | hlt
  · exact normalsJoin_basisFun_ne_zero_of_lt hlt
  · rw [normalsJoin_swap]
    exact neg_ne_zero.mpr (normalsJoin_basisFun_ne_zero_of_lt hlt)

/-- The join of two distinct standard basis vectors as a basis vector of `⋀² K^(k+2)` up to sign:
`normalsJoin e_i e_j = ε • ιMulti_family {i, j}`, with `ε = 1` if `i < j` and `ε = −1` otherwise.
The set `{i, j} = {j, i}` does not depend on the order (`Finset.pair_comm`), and `normalsJoin_swap`
gives the sign when `j < i`. It writes the joins of `exists_cycle_normals`, whose last pair
`(m − 1, 0)` is in decreasing order, as unit multiples of members of the basis. -/
private theorem normalsJoin_basisFun_eq_sign_smul {i j : Fin (k + 2)} (h : i ≠ j) :
    normalsJoin (Pi.basisFun K (Fin (k + 2)) i) (Pi.basisFun K (Fin (k + 2)) j)
      = (if i < j then (1 : Kˣ) else Units.mk0 (-1 : K) (by norm_num)) •
          exteriorPower.ιMulti_family K 2 (Pi.basisFun K (Fin (k + 2)))
            ⟨{i, j}, Finset.card_pair h⟩ := by
  by_cases hlt : i < j
  · rw [ite_eq_left hlt, one_smul]
    exact normalsJoin_eq_ιMulti_family_pair hlt
  · have hji : j < i := (lt_or_gt_of_ne h).resolve_left hlt
    have hset : (⟨{j, i}, Finset.card_pair (Fin.ne_of_lt hji)⟩ :
          Set.powersetCard (Fin (k + 2)) 2) = ⟨{i, j}, Finset.card_pair h⟩ :=
      Subtype.ext (Finset.pair_comm j i)
    rw [ite_eq_right hlt, normalsJoin_swap, normalsJoin_eq_ιMulti_family_pair hji, hset,
      Units.smul_def, Units.val_mk0]
    module

/-- **Normals for a cycle with independent hinges** (`lem:cycle-normals`): for `3 ≤ m ≤ k + 2`, that
is, `m ≤ d + 1`, the normals `nrm i = e_i` (standard basis vectors, along `Fin.castLE`) have nonzero
joins `nrm i ∨ nrm (i + 1)` and linearly independent panel support extensors
`C(nrm i, nrm (i + 1))`, with indices mod `m`. The `m` pairs `{i, i + 1}`, the edges of a cycle on
`Fin m`, are distinct as `m ≥ 3`, so up to sign the joins are `m` distinct members of the basis of
`⋀² K^(k+2)` (`normalsJoin_basisFun_eq_sign_smul`,
`exteriorPower.ιMulti_family_linearIndependent_ofBasis`, `LinearIndependent.units_smul_iff`), and
`panelSupportExtensor_linearIndependent_iff` passes their independence to the extensors. The
realization of a cycle (`lem:cycle-realization`) takes its normals from it, and its rigidity from
`theorem_55_cycle` (`lem:cycle-realization-rigid`). -/
theorem exists_cycle_normals {m : ℕ} [NeZero m] (hm3 : 3 ≤ m) (hmk : m ≤ k + 2) :
    ∃ nrm : Fin m → Fin (k + 2) → K,
      (∀ i : Fin m, normalsJoin (nrm i) (nrm (i + 1)) ≠ 0) ∧
      LinearIndependent K fun i : Fin m => panelSupportExtensor (nrm i) (nrm (i + 1)) := by
  -- Consecutive cyclic indices are distinct after `Fin.castLE` (else `1 = 0` in `Fin m`).
  have hne : ∀ i : Fin m, (Fin.castLE hmk i : Fin (k + 2)) ≠ Fin.castLE hmk (i + 1) := by
    intro i h
    rw [Fin.castLE_inj] at h
    have h1 : (1 : Fin m) = 0 := add_eq_left.mp h.symm
    have hv := congrArg Fin.val h1
    rw [Fin.val_one', Fin.val_zero, Nat.mod_eq_of_lt (by omega : 1 < m)] at hv
    omega
  refine ⟨fun i => Pi.basisFun K (Fin (k + 2)) (Fin.castLE hmk i), fun i => ?_, ?_⟩
  · -- Nonvanishing: each cyclic pair joins two distinct basis vectors.
    exact normalsJoin_basisFun_ne_zero_of_ne (hne i)
  · -- Extensor LI ↔ grade-2-join LI, then units-smul + `⋀²`-basis-family LI.
    rw [panelSupportExtensor_linearIndependent_iff]
    have h1ne : (1 : Fin m) ≠ 0 := by
      intro h; have hv := congrArg Fin.val h
      rw [Fin.val_one', Fin.val_zero, Nat.mod_eq_of_lt (by omega : 1 < m)] at hv; omega
    have h2ne : (1 + 1 : Fin m) ≠ 0 := by
      intro h; have hv := congrArg Fin.val h
      rw [Fin.val_add, Fin.val_one', Fin.val_zero, Nat.mod_eq_of_lt (by omega : 1 < m),
        Nat.mod_eq_of_lt (by omega : 1 + 1 < m)] at hv; omega
    -- The cyclic-edge index map into the 2-subsets is injective (this is where `m ≥ 3` is used).
    have hι_inj : Function.Injective (fun i : Fin m =>
        (⟨{Fin.castLE hmk i, Fin.castLE hmk (i + 1)}, Finset.card_pair (hne i)⟩ :
          Set.powersetCard (Fin (k + 2)) 2)) := by
      intro a b hab
      replace hab : ({Fin.castLE hmk a, Fin.castLE hmk (a + 1)} : Finset (Fin (k + 2)))
          = {Fin.castLE hmk b, Fin.castLE hmk (b + 1)} := congrArg Subtype.val hab
      have hma : Fin.castLE hmk a ∈
          ({Fin.castLE hmk b, Fin.castLE hmk (b + 1)} : Finset (Fin (k + 2))) := by
        rw [← hab]; exact Finset.mem_insert_self _ _
      have hma1 : Fin.castLE hmk (a + 1) ∈
          ({Fin.castLE hmk b, Fin.castLE hmk (b + 1)} : Finset (Fin (k + 2))) := by
        rw [← hab]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      simp only [Finset.mem_insert, Finset.mem_singleton, Fin.castLE_inj] at hma hma1
      rcases hma with h | h
      · exact h
      · exfalso
        rcases hma1 with h' | h'
        · rw [h, add_assoc] at h'
          exact h2ne (add_eq_left.mp h')
        · rw [h] at h'
          exact h1ne (add_eq_left.mp (add_right_cancel h'))
    -- Decompose the cyclic join family as unit scalars times the sorted `ιMulti_family` subfamily.
    have hEq : (fun i : Fin m => normalsJoin (Pi.basisFun K (Fin (k + 2)) (Fin.castLE hmk i))
          (Pi.basisFun K (Fin (k + 2)) (Fin.castLE hmk (i + 1))))
        = (fun i : Fin m => if (Fin.castLE hmk i : Fin (k + 2)) < Fin.castLE hmk (i + 1)
              then (1 : Kˣ) else Units.mk0 (-1 : K) (by norm_num))
          • (fun i : Fin m => exteriorPower.ιMulti_family K 2 (Pi.basisFun K (Fin (k + 2)))
              ⟨{Fin.castLE hmk i, Fin.castLE hmk (i + 1)}, Finset.card_pair (hne i)⟩) := by
      funext i
      rw [Pi.smul_apply']
      exact normalsJoin_basisFun_eq_sign_smul (hne i)
    rw [hEq, LinearIndependent.units_smul_iff]
    exact (exteriorPower.ιMulti_family_linearIndependent_ofBasis K 2
      (Pi.basisFun K (Fin (k + 2)))).comp _ hι_inj

/-- **The coordinates of the panel support extensor as polynomials** (a step of
`lem:rows-polynomial-in-normals`): for bodies `u`, `v` and a `k`-subset `t` of `Fin (k+2)`,
`panelSupportPoly u v t = ∑ s, c(t, s) * normalsJoinPoly u v s`, where `c(t, s)` is the coordinate
at `t` of the image under `complementIso` of the basis vector at `s` of `⋀² K^(k+2)`. As
`complementIso` is linear, its value at the normals `q` is the coordinate at `t` of
`C(q (u, ·), q (v, ·))` (`panelSupportPoly_eval`), and it has degree at most two
(`panelSupportPoly_totalDegree_le`). -/
noncomputable def panelSupportPoly {α : Type*} (u v : α) (t : Set.powersetCard (Fin (k + 2)) k) :
    MvPolynomial (α × Fin (k + 2)) K :=
  ∑ s : Set.powersetCard (Fin (k + 2)) 2,
    MvPolynomial.C
        (((Pi.basisFun K (Fin (k + 2))).exteriorPower k).repr
          (complementIso (k := k) (j := 2) (by omega)
            ((Pi.basisFun K (Fin (k + 2))).exteriorPower 2 s)) t)
      * normalsJoinPoly u v s

/-- **The value of `panelSupportPoly`** (a step of `lem:rows-polynomial-in-normals`): at `q`, it is
the coordinate at `t` of `C(q (u, ·), q (v, ·))`. The proof writes the join in the basis of
`⋀² K^(k+2)` (`Basis.sum_repr`), passes the sum through the linear form
`Finsupp.lapply t ∘ₗ repr ∘ₗ complementIso` (`map_sum`), and evaluates each term
(`normalsJoinPoly_eval`). -/
theorem panelSupportPoly_eval {α : Type*} (u v : α) (q : α × Fin (k + 2) → K)
    (t : Set.powersetCard (Fin (k + 2)) k) :
    MvPolynomial.eval q (panelSupportPoly u v t) =
      ((Pi.basisFun K (Fin (k + 2))).exteriorPower k).repr
        (panelSupportExtensor (fun i => q (u, i)) (fun i => q (v, i))) t := by
  rw [panelSupportPoly, map_sum]
  rw [panelSupportExtensor,
    ← ((Pi.basisFun K (Fin (k + 2))).exteriorPower 2).sum_repr
      (normalsJoin (fun i => q (u, i)) (fun i => q (v, i)))]
  -- Push the `⋀^k`-basis `repr (·) t` of `complementIso (∑ …)` through the two sums as the linear
  -- functional `Finsupp.lapply t ∘ₗ repr ∘ₗ complementIso` (codomain `K`, sidestepping the
  -- `Finsupp`-codomain `map_sum` snag that blocks pushing `repr` directly).
  rw [show ((Pi.basisFun K (Fin (k + 2))).exteriorPower k).repr
        ((complementIso (by omega : (2 : ℕ) ≤ k + 2))
          (∑ x, (((Pi.basisFun K (Fin (k + 2))).exteriorPower 2).repr
              (normalsJoin (fun i => q (u, i)) (fun i => q (v, i)))) x •
            (((Pi.basisFun K (Fin (k + 2))).exteriorPower 2) x))) t
      = (Finsupp.lapply t ∘ₗ
          ((Pi.basisFun K (Fin (k + 2))).exteriorPower k).repr.toLinearMap ∘ₗ
            (complementIso (by omega : (2 : ℕ) ≤ k + 2)).toLinearMap)
        (∑ x, (((Pi.basisFun K (Fin (k + 2))).exteriorPower 2).repr
            (normalsJoin (fun i => q (u, i)) (fun i => q (v, i)))) x •
          (((Pi.basisFun K (Fin (k + 2))).exteriorPower 2) x)) from rfl,
    map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, normalsJoinPoly_eval, map_smul, smul_eq_mul,
    LinearMap.comp_apply, Finsupp.lapply_apply, LinearMap.comp_apply, mul_comm]
  rfl

/-- **`panelSupportPoly` has degree at most two** (a step of `lem:rows-polynomial-in-normals`): it
is a sum of constants times the polynomials `normalsJoinPoly`, each of degree at most two
(`normalsJoinPoly_totalDegree_le`). -/
theorem panelSupportPoly_totalDegree_le {α : Type*} (u v : α)
    (t : Set.powersetCard (Fin (k + 2)) k) :
    (panelSupportPoly (K := K) u v t).totalDegree ≤ 2 := by
  rw [panelSupportPoly]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun s _ => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  exact normalsJoinPoly_totalDegree_le u v s

/-! ## The forms that vanish on a hinge (`lem:rows-polynomial-in-normals`)

The hinge-row block of an edge whose hinge has the extensor `C` is the space `(span {C})^⊥` of the
forms that vanish at `C` (`def:hinge-row-block`). It is spanned by the forms
`C_{t₁} e_{t₂}^* − C_{t₂} e_{t₁}^*` for the pairs `(t₁, t₂)` of coordinates, where `C_t` is the
coordinate of `C` at `t` and `e_t^*` the dual basis form: each vanishes at `C`, and when `C ≠ 0`
they span the block. They are linear in `C`, so for a panel support extensor their coordinates are
polynomials of degree two in the normals. -/

/-- **The standard basis of the screw space** (the coordinates of `lem:rows-polynomial-in-normals`):
the basis of `⋀^k K^(k+2)` induced by the standard basis of `K^(k+2)`, indexed by the `k`-subsets of
`Fin (k+2)`, transported to `ScrewSpace K k` by `ScrewSpace.equivExteriorPower`. Its coordinates are
those that `panelSupportPoly` gives (`panelSupportPoly_eval`). -/
noncomputable def screwBasis (k : ℕ) :
    Module.Basis (Set.powersetCard (Fin (k + 2)) k) K (ScrewSpace K k) :=
  ((Pi.basisFun K (Fin (k + 2))).exteriorPower k).map (ScrewSpace.equivExteriorPower K k).symm

/-- **The coordinates in `screwBasis` are those in the basis of `⋀^k K^(k+2)`**, by `rfl`, as
`ScrewSpace.equivExteriorPower` is a cast. It lets the lemmas on `panelSupportPoly`, stated in the
second basis, and on `annihRow`, stated in the first, be combined. -/
theorem screwBasis_repr_apply (C : ScrewSpace K k) (t : Set.powersetCard (Fin (k + 2)) k) :
    (screwBasis k).repr C t = ((Pi.basisFun K (Fin (k + 2))).exteriorPower k).repr C t := rfl

/-- **The form of a pair of coordinates that vanishes at a screw** (the forms of
`lem:rows-polynomial-in-normals`): for `C ∈ ScrewSpace K k` and coordinates `t₁`, `t₂`, the form
`C_{t₁} • e_{t₂}^* − C_{t₂} • e_{t₁}^*` in `screwBasis`, that is,
`x ↦ C_{t₁} x_{t₂} − C_{t₂} x_{t₁}`. It vanishes at `C` (`annihRow_apply_self`), the forms of all
pairs span the forms that vanish at `C` when `C ≠ 0` (`span_annihRow_eq_dualAnnihilator`), and it is
linear in `C` (`annihRow_add`, `annihRow_smul`). -/
noncomputable def annihRow (C : ScrewSpace K k) (t₁ t₂ : Set.powersetCard (Fin (k + 2)) k) :
    Module.Dual K (ScrewSpace K k) :=
  (screwBasis k).repr C t₁ • (screwBasis k).coord t₂
    - (screwBasis k).repr C t₂ • (screwBasis k).coord t₁

@[simp]
theorem annihRow_apply (C : ScrewSpace K k) (t₁ t₂ : Set.powersetCard (Fin (k + 2)) k)
    (x : ScrewSpace K k) :
    annihRow C t₁ t₂ x =
      (screwBasis k).repr C t₁ * (screwBasis k).repr x t₂
        - (screwBasis k).repr C t₂ * (screwBasis k).repr x t₁ := by
  simp [annihRow]

/-- **The form `annihRow C t₁ t₂` vanishes at `C`**: its value there is
`C_{t₁} C_{t₂} − C_{t₂} C_{t₁}`. So it lies in the hinge-row block of a hinge with the extensor `C`.
-/
theorem annihRow_apply_self (C : ScrewSpace K k) (t₁ t₂ : Set.powersetCard (Fin (k + 2)) k) :
    annihRow C t₁ t₂ C = 0 := by
  rw [annihRow_apply]; ring

/-- **`annihRow` is additive in the screw**:
`annihRow (C + C') t₁ t₂ = annihRow C t₁ t₂ + annihRow C' t₁ t₂`, as each coordinate is linear. With
`annihRow_smul` and `panelSupportExtensor_add_left`, the forms of Case III's candidate hinge
`C(n_u + t • n', n_r)` are affine in `t`
(`PanelHingeFramework.caseIIICandidate_panelRow_eq_add_smul`). -/
theorem annihRow_add (C C' : ScrewSpace K k) (t₁ t₂ : Set.powersetCard (Fin (k + 2)) k) :
    annihRow (C + C') t₁ t₂ = annihRow C t₁ t₂ + annihRow (k := k) C' t₁ t₂ := by
  simp only [annihRow, map_add, Finsupp.add_apply, add_smul]
  abel

/-- **`annihRow` is homogeneous in the screw**: `annihRow (c • C) t₁ t₂ = c • annihRow C t₁ t₂`, as
each coordinate is linear. -/
theorem annihRow_smul (c : K) (C : ScrewSpace K k) (t₁ t₂ : Set.powersetCard (Fin (k + 2)) k) :
    annihRow (c • C) t₁ t₂ = c • annihRow (k := k) C t₁ t₂ := by
  simp only [annihRow, map_smul, Finsupp.smul_apply, smul_sub, smul_eq_mul, mul_smul]

/-- **`annihRow` changes sign with the screw**: `annihRow (−C) t₁ t₂ = −annihRow C t₁ t₂`, the case
`c = −1` of `annihRow_smul`. With `panelSupportExtensor_swap` and `hingeRow_swap`, it shows that a
panel row does not depend on the order in which the selector records the ends of its edge
(`PanelHingeFramework.ofNormals_panelRow_eq_hingeRow_of_ends_or_swap`). -/
theorem annihRow_neg (C : ScrewSpace K k) (t₁ t₂ : Set.powersetCard (Fin (k + 2)) k) :
    annihRow (-C) t₁ t₂ = -annihRow (k := k) C t₁ t₂ := by
  rw [show (-C) = (-1 : K) • C from (neg_one_smul K C).symm, annihRow_smul]
  module

/-- **The forms `annihRow C t₁ t₂` span the forms that vanish at `C`**
(`lem:rows-polynomial-in-normals`, the spanning): for `C ≠ 0`, their span is `(span {C})^⊥`, the
hinge-row block of a hinge with the extensor `C` (`def:hinge-row-block`). Each vanishes at `C`
(`annihRow_apply_self`). Conversely, take `t₀` with `C_{t₀} ≠ 0`. A form `f` that vanishes at `C` is
`∑_t (f(b_t) / C_{t₀}) • annihRow C t₀ t`: the two sides agree at each basis vector `b_s`, directly
for `s ≠ t₀`, and for `s = t₀` because `∑_t C_t f(b_t) = f C = 0`. -/
theorem span_annihRow_eq_dualAnnihilator (C : ScrewSpace K k) (hC : C ≠ 0) :
    Submodule.span K (Set.range (fun p : Set.powersetCard (Fin (k + 2)) k
        × Set.powersetCard (Fin (k + 2)) k => annihRow C p.1 p.2))
      = (Submodule.span K {C}).dualAnnihilator := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨⟨t₁, t₂⟩, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_dualAnnihilator]
    intro c hc
    rw [Submodule.mem_span_singleton] at hc
    obtain ⟨r, rfl⟩ := hc
    rw [map_smul, annihRow_apply_self, smul_zero]
  · intro f hf
    classical
    rw [Submodule.mem_dualAnnihilator] at hf
    have hfC : f C = 0 := hf C (Submodule.mem_span_singleton_self C)
    -- A coordinate `t₀` with `C_{t₀} ≠ 0`, available because `C ≠ 0`.
    obtain ⟨t₀, ht₀⟩ : ∃ t₀, (screwBasis k).repr C t₀ ≠ 0 := by
      by_contra h
      refine hC (Module.Basis.forall_coord_eq_zero_iff (screwBasis k) |>.1 fun t => ?_)
      rw [Module.Basis.coord_apply]
      exact not_not.1 fun ht => h ⟨t, ht⟩
    -- The Kronecker-delta form of the basis coordinates of a basis vector.
    have hδ : ∀ i j : Set.powersetCard (Fin (k + 2)) k,
        (screwBasis k).repr (screwBasis k i) j = if i = j then (1 : K) else 0 :=
      fun i j => Module.Basis.repr_self_apply (screwBasis k) (i := i) j
    -- `f C = ∑_t C_t · f(b t)` (the dual-basis expansion of `f C`), which is `0`.
    have hfC' : ∑ t, (screwBasis k).repr C t * f (screwBasis k t) = 0 := by
      rw [← hfC]
      conv_rhs => rw [← (screwBasis k).sum_repr C, map_sum]
      exact Finset.sum_congr rfl fun t _ => by rw [map_smul, smul_eq_mul]
    -- `f` is the explicit combination `∑_t (f (b t) / C_{t₀}) • annihRow C t₀ t`.
    have hsum : f = ∑ t, (f (screwBasis k t) / (screwBasis k).repr C t₀) • annihRow C t₀ t := by
      refine (screwBasis k).ext fun s => ?_
      rw [LinearMap.sum_apply]
      simp only [LinearMap.smul_apply, smul_eq_mul, annihRow_apply, hδ]
      rcases eq_or_ne s t₀ with hs | hs
      · subst hs
        -- Each summand is `(f(b x)/C_s)·(C_s·[s=x] − C_x·[s=s])`; split into two sums.
        have hsplit : ∀ x, f (screwBasis k x) / (screwBasis k).repr C s
            * ((screwBasis k).repr C s * (if s = x then (1 : K) else 0)
              - (screwBasis k).repr C x * (if s = s then (1 : K) else 0))
            = f (screwBasis k x) / (screwBasis k).repr C s
                * ((screwBasis k).repr C s * (if s = x then (1 : K) else 0))
              - f (screwBasis k x) / (screwBasis k).repr C s * (screwBasis k).repr C x := by
          intro x; rw [ite_eq_left rfl, mul_one]; ring
        rw [Finset.sum_congr rfl fun x _ => hsplit x, Finset.sum_sub_distrib]
        have h1 : ∑ x, f (screwBasis k x) / (screwBasis k).repr C s
            * ((screwBasis k).repr C s * (if s = x then (1 : K) else 0)) = f (screwBasis k s) := by
          rw [Finset.sum_eq_single s]
          · rw [ite_eq_left rfl, mul_one, div_mul_cancel₀ _ ht₀]
          · intro x _ hxs; rw [ite_eq_right (fun h => hxs h.symm), mul_zero, mul_zero]
          · intro h; exact absurd (Finset.mem_univ s) h
        have h2 : ∑ x, f (screwBasis k x) / (screwBasis k).repr C s
            * (screwBasis k).repr C x = 0 := by
          have hreorg : ∑ x, f (screwBasis k x) / (screwBasis k).repr C s
              * (screwBasis k).repr C x
              = (∑ x, (screwBasis k).repr C x * f (screwBasis k x))
                / (screwBasis k).repr C s := by
            rw [Finset.sum_div]
            exact Finset.sum_congr rfl fun x _ => by ring
          rw [hreorg, hfC', zero_div]
        rw [h1, h2, sub_zero]
      · rw [Finset.sum_eq_single s]
        · rw [ite_eq_left rfl, ite_eq_right hs, mul_zero, sub_zero, mul_one,
            div_mul_cancel₀ _ ht₀]
        · intro t _ hts
          rw [ite_eq_right (fun h => hts h.symm), ite_eq_right hs]; ring
        · intro h; exact absurd (Finset.mem_univ s) h
    rw [hsum]
    refine Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span ⟨(t₀, t), rfl⟩

/-- **The coordinates of the forms `annihRow` as polynomials in the normals** (a step of
`lem:rows-polynomial-in-normals`): for bodies `u`, `v`, the coordinate at the basis vector `b_s` of
`annihRow C(q (u, ·), q (v, ·)) t₁ t₂` is `[t₂ = s] C_{t₁} − [t₁ = s] C_{t₂}`, the value at `q` of
`annihRowPoly u v t₁ t₂ s = [t₂ = s] panelSupportPoly u v t₁ − [t₁ = s] panelSupportPoly u v t₂`
(`annihRowPoly_eval`), of degree at most two (`annihRowPoly_totalDegree_le`). -/
noncomputable def annihRowPoly {α : Type*} (u v : α)
    (t₁ t₂ s : Set.powersetCard (Fin (k + 2)) k) : MvPolynomial (α × Fin (k + 2)) K :=
  (if t₂ = s then panelSupportPoly u v t₁ else 0)
    - (if t₁ = s then panelSupportPoly u v t₂ else 0)

/-- **The value of `annihRowPoly`** (`lem:rows-polynomial-in-normals`): at the normals `q`, it is
the coordinate at `screwBasis k s` of the form `annihRow C(q (u, ·), q (v, ·)) t₁ t₂`
(`panelSupportPoly_eval`). -/
theorem annihRowPoly_eval {α : Type*} (u v : α) (q : α × Fin (k + 2) → K)
    (t₁ t₂ s : Set.powersetCard (Fin (k + 2)) k) :
    MvPolynomial.eval q (annihRowPoly u v t₁ t₂ s) =
      annihRow (panelSupportExtensor (fun i => q (u, i)) (fun i => q (v, i))) t₁ t₂
        (screwBasis k s) := by
  rw [annihRowPoly, annihRow_apply, map_sub,
    Module.Basis.repr_self_apply (screwBasis k) (i := s) t₂,
    Module.Basis.repr_self_apply (screwBasis k) (i := s) t₁,
    apply_ite (MvPolynomial.eval q), apply_ite (MvPolynomial.eval q),
    map_zero, panelSupportPoly_eval, panelSupportPoly_eval, mul_ite, mul_one, mul_zero,
    mul_ite, mul_one, mul_zero, ← screwBasis_repr_apply, ← screwBasis_repr_apply]
  congr 1
  · rcases eq_or_ne t₂ s with h | h
    · rw [ite_eq_left h, ite_eq_left h.symm]
    · rw [ite_eq_right h, ite_eq_right fun h' => h h'.symm]
  · rcases eq_or_ne t₁ s with h | h
    · rw [ite_eq_left h, ite_eq_left h.symm]
    · rw [ite_eq_right h, ite_eq_right fun h' => h h'.symm]

/-- **`annihRowPoly` has degree at most two** (`lem:rows-polynomial-in-normals`): each branch is
`panelSupportPoly`, of degree at most two (`panelSupportPoly_totalDegree_le`), or `0`. No
declaration uses it. -/
theorem annihRowPoly_totalDegree_le {α : Type*} (u v : α)
    (t₁ t₂ s : Set.powersetCard (Fin (k + 2)) k) :
    (annihRowPoly (K := K) u v t₁ t₂ s).totalDegree ≤ 2 := by
  refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_) <;>
    · split
      · exact panelSupportPoly_totalDegree_le u v _
      · rw [MvPolynomial.totalDegree_zero]; omega

/-! ## The deficiency bound (`lem:deficiency-rank-bound`, `lem:relative-deficiency-rank-bound`)

A partition `P` of `V(G)` is given by a labeling `f : α → α` whose fibres meet `V(G)` in the parts.
The screw assignments constant on each fibre form a space `W_f` of dimension `D` times the number of
labels (`partitionConstant`, `finrank_partitionConstant`). Such an assignment meets the hinge
constraint at an edge inside a part; at an edge between two parts with a nondegenerate hinge, the
constraint is `D − 1` linear conditions. So the motions in `W_f` (`partitionMotions`) have dimension
at least `D·|P| − (D−1)·d_G(P) = D + def_{G̃}(P)`, and a partition of the largest deficiency gives
`D + def(G̃) ≤ dim Z(G,p)` (`lem:deficiency-rank-bound`). This bound, which holds at every
realization, is one of the two inequalities of the rank formula in Katoh and Tanigawa's
Proposition 2.3 (KT p. 655), which they credit to Jackson and Jordán
(`prop:rigidity-matrix-prop11`). Jackson and Jordán derive its rank form from a count of independent
rows (2010, *The generic rank of body–bar-and-hinge frameworks*, European J. Combin. **31**, §4,
pp. 580–581). -/

namespace BodyHingeFramework

variable {α β : Type*}

/-- **Constant on each part** (the partitions of `def:D-deficiency`, given by labels): `S` is
constant on each part of the partition that `f : α → α` gives if `S u = S v` whenever `f u = f v`.
-/
def IsPartitionConstant (f : α → α) (S : α → ScrewSpace K k) : Prop :=
  ∀ u v, f u = f v → S u = S v

/-- **The assignments constant on each part** (a step of `lem:deficiency-rank-bound`): the subspace
`W_f` of the screw assignments constant on each fibre of `f` (`IsPartitionConstant`), with no hinge
constraint. It has dimension `D·|range f|` (`finrank_partitionConstant`). -/
def partitionConstant (f : α → α) : Submodule K (α → ScrewSpace K k) where
  carrier := {S | IsPartitionConstant f S}
  add_mem' {S T} hS hT u v huv := by simp only [Pi.add_apply, hS u v huv, hT u v huv]
  zero_mem' _ _ _ := rfl
  smul_mem' c S hS u v huv := by rw [Pi.smul_apply, Pi.smul_apply, hS u v huv]

@[simp]
theorem mem_partitionConstant (f : α → α) (S : α → ScrewSpace K k) :
    S ∈ partitionConstant (k := k) f ↔ IsPartitionConstant f S :=
  Iff.rfl

/-- **`W_f` is the image of the assignments on the labels** (a step of `lem:deficiency-rank-bound`):
`partitionConstant f` is the range of `LinearMap.funLeft` along
`Set.rangeFactorization f : α → range f`, as an assignment is constant on each fibre of `f` iff it
factors through `f`. As `Set.rangeFactorization f` is onto, `LinearMap.funLeft` is injective, and
`W_f` has dimension `D·|range f|` (`finrank_partitionConstant`). -/
theorem partitionConstant_eq_range_funLeft (f : α → α) :
    partitionConstant (k := k) f =
      LinearMap.range (LinearMap.funLeft K (ScrewSpace K k) (Set.rangeFactorization f)) := by
  ext S
  rw [mem_partitionConstant, LinearMap.mem_range]
  constructor
  · intro hS
    refine ⟨fun b => S b.2.choose, funext fun a => ?_⟩
    rw [LinearMap.funLeft_apply]
    exact (hS _ a (Set.rangeFactorization f a).2.choose_spec)
  · rintro ⟨g, rfl⟩ u v huv
    rw [LinearMap.funLeft_apply, LinearMap.funLeft_apply]
    congr 1
    exact Subtype.ext huv

/-- **`W_f` has dimension `D·|range f|`** (a step of `lem:deficiency-rank-bound`): it is the image
of the assignments on `range f` (`partitionConstant_eq_range_funLeft`) under an injective map
(`LinearMap.funLeft_injective_of_surjective`), and those form a space of dimension `D·|range f|`
(`finrank_screwAssignment`). -/
theorem finrank_partitionConstant [Finite α] (f : α → α) :
    Module.finrank K (partitionConstant (K := K) (k := k) f) =
      screwDim k * Nat.card (Set.range f) := by
  have : Fintype α := Fintype.ofFinite α
  have : Fintype (Set.range f) := Fintype.ofFinite _
  rw [partitionConstant_eq_range_funLeft,
    LinearMap.finrank_range_of_inj
      (LinearMap.funLeft_injective_of_surjective K (ScrewSpace K k) _
        Set.rangeFactorization_surjective),
    finrank_screwAssignment, Nat.card_eq_fintype_card]

/-- **`D·|P| ≤ dim W_f`** (a step of `lem:deficiency-rank-bound`): the number of parts is
`|P| = numParts G f = |f '' V(G)|`, and `f '' V(G) ⊆ range f` (`finrank_partitionConstant`). The
labels of bodies outside `V(G)` can make the bound strict. -/
theorem mul_numParts_le_finrank_partitionConstant [Finite α] (G : Graph α β) (f : α → α) :
    screwDim k * G.numParts f ≤ Module.finrank K (partitionConstant (K := K) (k := k) f) := by
  rw [finrank_partitionConstant]
  refine Nat.mul_le_mul_left _ ?_
  rw [Graph.numParts, Nat.card_coe_set_eq, ← Set.image_univ]
  exact Set.ncard_le_ncard (Set.image_mono (Set.subset_univ _)) (Set.toFinite _)

/-- **The motions constant on each part** (a step of `lem:deficiency-rank-bound`):
`partitionMotions f = Z(G,p) ⊓ W_f`. At a partition of the largest deficiency they have dimension at
least `D + def(G̃)` (`screwDim_add_deficiency_le_finrank_infinitesimalMotions`). -/
noncomputable def partitionMotions (F : BodyHingeFramework K k α β) (f : α → α) :
    Submodule K (α → ScrewSpace K k) :=
  F.infinitesimalMotions ⊓ partitionConstant f

theorem partitionMotions_eq (F : BodyHingeFramework K k α β) (f : α → α) :
    F.partitionMotions f = F.infinitesimalMotions ⊓ partitionConstant f :=
  rfl

/-- **The motions constant on each part are motions** (a step of `lem:deficiency-rank-bound`):
`partitionMotions f ≤ Z(G,p)`. -/
theorem partitionMotions_le_infinitesimalMotions (F : BodyHingeFramework K k α β) (f : α → α) :
    F.partitionMotions f ≤ F.infinitesimalMotions :=
  inf_le_left

/-! ### The bound by rank–nullity

The bound `D·|P| − (D−1)·d_G(P) ≤ dim partitionMotions f` is rank–nullity for the linear map
`partitionCutMap`, which sends `S` to the relative screws `S u_e − S v_e` at the edges `e` between
two parts, modulo the lines `span {C(p(e))}` of their hinges. On `W_f` its kernel is
`partitionMotions f`, as an assignment constant on each part meets the hinge constraint at every
other edge, and its codomain has dimension `(D−1)·d_G(P)` when those hinges are nondegenerate. -/

/-- **An edge between two parts has two ends with different labels**: membership in
`crossingEdges G f` unfolds to `e ∈ E(G)` and `∃ x y, G.IsLink e x y ∧ f x ≠ f y`, from which
`crossingEndpoints` chooses. -/
theorem exists_isLink_of_mem_crossingEdges (G : Graph α β) (f : α → α)
    (e : ↥(G.crossingEdges f)) : ∃ x y, G.IsLink (e : β) x y ∧ f x ≠ f y :=
  e.2.2

/-- **The chosen ends of an edge between two parts**: a pair `(u_e, v_e)` of ends of `e` with
different labels, chosen once by `Classical.choose` (`exists_isLink_of_mem_crossingEdges`). The
choice does not depend on the screw assignment, so `partitionCutMap` is linear. -/
noncomputable def crossingEndpoints (G : Graph α β) (f : α → α)
    (e : ↥(G.crossingEdges f)) : α × α :=
  ((exists_isLink_of_mem_crossingEdges G f e).choose,
    (exists_isLink_of_mem_crossingEdges G f e).choose_spec.choose)

theorem crossingEndpoints_isLink (G : Graph α β) (f : α → α)
    (e : ↥(G.crossingEdges f)) :
    G.IsLink (e : β) (crossingEndpoints G f e).1 (crossingEndpoints G f e).2 :=
  (exists_isLink_of_mem_crossingEdges G f e).choose_spec.choose_spec.1

/-- **The lines of the hinges between parts**: the subspace `N_f` of the families
`g : crossingEdges G f → ScrewSpace K k` with `g e ∈ span {C(p(e))}` for every `e`. The quotient by
it is the codomain of `partitionCutMap`, of dimension `(D−1)·d_G(P)` when those hinges are
nondegenerate (`finrank_partitionCutMap_codomain`). It is one `Submodule.pi`, rather than a product
of quotients, so that the codomain is a quotient by one submodule. -/
noncomputable def crossingSpanPi (F : BodyHingeFramework K k α β) (f : α → α) :
    Submodule K (↥(F.graph.crossingEdges f) → ScrewSpace K k) :=
  Submodule.pi Set.univ fun e => Submodule.span K {F.supportExtensor (e : β)}

/-- **The cut at the edges between parts** (a step of `lem:deficiency-rank-bound`): the linear map
that sends a screw assignment `S` to the family of relative screws `S u_e − S v_e` at the edges `e`
between two parts (`crossingEndpoints`), modulo `N_f = crossingSpanPi f`. On `W_f` its kernel is
`partitionMotions f` (`partitionCutMap_ker_inf`), and its codomain has dimension `(D−1)·d_G(P)`
(`finrank_partitionCutMap_codomain`). -/
noncomputable def partitionCutMap (F : BodyHingeFramework K k α β) (f : α → α) :
    (α → ScrewSpace K k) →ₗ[K]
      ((↥(F.graph.crossingEdges f) → ScrewSpace K k) ⧸ F.crossingSpanPi f) :=
  (F.crossingSpanPi f).mkQ ∘ₗ
    LinearMap.pi fun e =>
      LinearMap.proj (R := K) (φ := fun _ : α => ScrewSpace K k) (crossingEndpoints F.graph f e).1
        - LinearMap.proj (R := K) (φ := fun _ : α => ScrewSpace K k)
            (crossingEndpoints F.graph f e).2

theorem partitionCutMap_apply_eq_zero_iff (F : BodyHingeFramework K k α β) (f : α → α)
    (S : α → ScrewSpace K k) :
    F.partitionCutMap f S = 0 ↔
      ∀ e : ↥(F.graph.crossingEdges f),
        S (crossingEndpoints F.graph f e).1 - S (crossingEndpoints F.graph f e).2
          ∈ Submodule.span K {F.supportExtensor (e : β)} := by
  rw [partitionCutMap, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    crossingSpanPi, Submodule.mem_pi]
  refine forall_congr' fun e => ?_
  simp only [Set.mem_univ, true_implies, LinearMap.pi_apply, LinearMap.sub_apply,
    LinearMap.proj_apply]

/-- **On `W_f` the kernel of the cut is `partitionMotions f`** (a step of
`lem:deficiency-rank-bound`): an assignment `S ∈ W_f` lies in the kernel iff it is an infinitesimal
motion. At an edge between two parts, vanishing modulo `span {C(p(e))}` at the chosen ends is the
hinge constraint, up to the order of the ends, as the span is closed under negation; at an edge
inside a part, `S u = S v` by constancy on the parts. Conversely, a motion meets the constraint at
the chosen ends. -/
theorem partitionCutMap_ker_inf (F : BodyHingeFramework K k α β) (f : α → α) :
    LinearMap.ker (F.partitionCutMap f) ⊓ partitionConstant f = F.partitionMotions f := by
  rw [partitionMotions_eq]
  apply le_antisymm
  · rintro S ⟨hker, hconst⟩
    refine Submodule.mem_inf.mpr ⟨?_, hconst⟩
    rw [mem_infinitesimalMotions]
    intro e u v he
    rw [hingeConstraint]
    by_cases hcross : e ∈ F.graph.crossingEdges f
    · -- Crossing edge: read the constraint off the chosen endpoints, swap to `u v`.
      have hk := (F.partitionCutMap_apply_eq_zero_iff f S).mp (LinearMap.mem_ker.mp hker)
        ⟨e, hcross⟩
      have hlink := crossingEndpoints_isLink F.graph f ⟨e, hcross⟩
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := he.eq_and_eq_or_eq_and_eq hlink
      · exact hk
      · rw [← neg_sub]; exact Submodule.neg_mem _ hk
    · -- Non-crossing edge: `f u = f v`, so `S u = S v` by part-constancy.
      have hfuv : f u = f v := by
        by_contra hne
        exact hcross ⟨he.edge_mem, u, v, he, hne⟩
      rw [hconst u v hfuv, sub_self]
      exact Submodule.zero_mem _
  · rintro S ⟨hmot, hconst⟩
    refine Submodule.mem_inf.mpr ⟨?_, hconst⟩
    rw [LinearMap.mem_ker, F.partitionCutMap_apply_eq_zero_iff f S]
    exact fun e =>
      (F.mem_infinitesimalMotions S).mp hmot _ _ _ (crossingEndpoints_isLink F.graph f e)

/-- **The codomain of the cut has dimension `(D−1)·d_G(P)`** (a step of
`lem:deficiency-rank-bound`): if the hinge of every edge between two parts is nondegenerate (`hC`),
the quotient of the families on the `d_G(P)` edges between parts by `N_f` is the product of the
quotients `ScrewSpace K k ⧸ span {C(p(e))}` (`Submodule.quotientPi`), each of dimension `D − 1`. -/
theorem finrank_partitionCutMap_codomain [Finite β]
    (F : BodyHingeFramework K k α β) (f : α → α)
    (hC : ∀ e ∈ F.graph.crossingEdges f, F.supportExtensor e ≠ 0) :
    Module.finrank K ((↥(F.graph.crossingEdges f) → ScrewSpace K k) ⧸ F.crossingSpanPi f)
      = (screwDim k - 1) * (F.graph.crossingEdges f).ncard := by
  have : Fintype β := Fintype.ofFinite β
  have : Fintype ↥(F.graph.crossingEdges f) := Fintype.ofFinite _
  classical
  -- The single `Submodule.pi` quotient splits as the product of fiber quotients
  -- `∀ e, ScrewSpace K k ⧸ span C(e)`, each of dimension `D − 1` (as `C(e) ≠ 0`).
  have hsplit : Module.finrank K
      ((↥(F.graph.crossingEdges f) → ScrewSpace K k) ⧸ F.crossingSpanPi f)
      = Module.finrank K ((e : ↥(F.graph.crossingEdges f)) →
          ScrewSpace K k ⧸ Submodule.span K {F.supportExtensor e}) :=
    (Submodule.quotientPi (Ms := fun _ : ↥(F.graph.crossingEdges f) => ScrewSpace K k)
      (fun e => Submodule.span K {F.supportExtensor (e : β)})).finrank_eq
  rw [hsplit, Module.finrank_pi_fintype]
  have hsumm : ∀ e : ↥(F.graph.crossingEdges f),
      Module.finrank K (ScrewSpace K k ⧸ Submodule.span K {F.supportExtensor (e : β)})
        = screwDim k - 1 := by
    intro e
    have key := Submodule.finrank_quotient_add_finrank
      (Submodule.span K {F.supportExtensor (e : β)})
    rw [finrank_span_singleton (hC e e.2), screwSpace_finrank] at key
    omega
  rw [Finset.sum_congr rfl fun e _ => hsumm e, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, mul_comm]

/-- **The motions constant on each part have dimension at least `D·|P| − (D−1)·d_G(P)`** (a step of
`lem:deficiency-rank-bound`): for a partition `f` whose edges between parts have nondegenerate
hinges (`hC`), in `ℤ`. By rank–nullity for `partitionCutMap f` on the screw assignments and
`dim (ker ⊔ W_f) ≤ D|α|`, `dim partitionMotions f ≥ dim W_f − (D−1)·d_G(P)`
(`partitionCutMap_ker_inf`, `finrank_partitionCutMap_codomain`), and `dim W_f ≥ D·|P|`
(`mul_numParts_le_finrank_partitionConstant`).
`screwDim_add_deficiency_le_finrank_infinitesimalMotions` applies it at a partition of the largest
deficiency. -/
theorem screwDim_mul_numParts_sub_le_finrank_partitionMotions [Finite α] [Finite β]
    (F : BodyHingeFramework K k α β) (f : α → α)
    (hC : ∀ e ∈ F.graph.crossingEdges f, F.supportExtensor e ≠ 0) :
    (screwDim k : ℤ) * F.graph.numParts f
        - (screwDim k - 1 : ℤ) * (F.graph.crossingEdges f).ncard
      ≤ (Module.finrank K (F.partitionMotions f) : ℤ) := by
  have : Fintype α := Fintype.ofFinite α
  have : Fintype ↥(F.graph.crossingEdges f) := Fintype.ofFinite _
  -- Work with the **full** cut `partitionCutMap f` on `α → ScrewSpace K k` (a plain pi, light
  -- instances), combining its rank-nullity with the `ker ⊓ W_f` dimension inequality.
  -- Rank-nullity: `finrank (range) + finrank (ker) = finrank (α → ScrewSpace K k) = D·|α|`.
  have hfull : Module.finrank K (LinearMap.range (F.partitionCutMap f))
      + Module.finrank K (LinearMap.ker (F.partitionCutMap f)) = screwDim k * Fintype.card α := by
    rw [LinearMap.finrank_range_add_finrank_ker, finrank_screwAssignment]
  -- `finrank (range) ≤ finrank codomain = (D−1)·d_G(P)`, distributed `D·d_G(P) − d_G(P)`
  -- so its `D·d_G(P)` and `d_G(P)` atoms line up with the (ℤ-distributed) goal for `omega`.
  have hrange : Module.finrank K (LinearMap.range (F.partitionCutMap f))
      ≤ screwDim k * (F.graph.crossingEdges f).ncard - (F.graph.crossingEdges f).ncard := by
    have := (LinearMap.range (F.partitionCutMap f)).finrank_le.trans_eq
      (F.finrank_partitionCutMap_codomain f hC)
    rwa [Nat.sub_mul, one_mul] at this
  -- `partitionMotions f = ker ⊓ W_f`, so by `Submodule.finrank_sup_add_finrank_inf_eq` and
  -- `finrank (ker ⊔ W_f) ≤ D·|α|`:
  -- `finrank (partitionMotions) ≥ finrank (ker) + finrank W_f − D·|α|`.
  have hinf : Module.finrank K (LinearMap.ker (F.partitionCutMap f))
        + Module.finrank K (partitionConstant (K := K) (k := k) f)
      ≤ Module.finrank K (F.partitionMotions f) + screwDim k * Fintype.card α := by
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.ker (F.partitionCutMap f)) (partitionConstant (k := k) f)
    rw [partitionCutMap_ker_inf] at hsup
    have hle : Module.finrank K
          (↥(LinearMap.ker (F.partitionCutMap f) ⊔ partitionConstant (k := k) f))
        ≤ screwDim k * Fintype.card α := by
      rw [← finrank_screwAssignment (K := K) (α := α) (k := k)]
      exact Submodule.finrank_le _
    omega
  -- `finrank W_f ≥ D·|P|`.
  have hWf := mul_numParts_le_finrank_partitionConstant (K := K) (k := k) F.graph f
  have hD : 1 ≤ screwDim k := Nat.choose_pos (by omega)
  have hdle : (F.graph.crossingEdges f).ncard ≤ screwDim k * (F.graph.crossingEdges f).ncard :=
    Nat.le_mul_of_pos_left _ (by omega)
  rw [sub_mul, one_mul]
  zify [hdle] at hrange ⊢
  zify at hfull hinf hWf
  omega

/-- **The two forms of `D` agree only at `n = k + 1`**: if `bodyBarDim n = screwDim k`, then
`n = k + 1`. Doubling clears the halves, `n(n + 1) = (k + 2)(k + 1)`, and `m ↦ m(m + 1)` is strictly
increasing (`nlinarith`). The statements that take both the dimension `n` of `def(G̃)` and the grade
`k` of the screw space use it to recover `n = k + 1`. -/
theorem _root_.Graph.eq_add_one_of_bodyBarDim_eq_screwDim {n k : ℕ}
    (hn : Graph.bodyBarDim n = screwDim k) : n = k + 1 := by
  have key : ∀ m : ℕ, 2 * Nat.choose m 2 = m * (m - 1) := fun m => by
    rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self m).two_dvd]
  have hbb : 2 * Graph.bodyBarDim n = n * (n + 1) := by
    rw [Graph.bodyBarDim, Nat.mul_div_cancel' (Nat.even_mul_succ_self n).two_dvd]
  have hsd : 2 * screwDim k = (k + 2) * (k + 1) := by
    rw [show screwDim k = Nat.choose (k + 2) 2 from rfl, key (k + 2),
      show k + 2 - 1 = k + 1 from rfl]
  have hprod : n * (n + 1) = (k + 2) * (k + 1) := by omega
  nlinarith [hprod]

/-- **`bodyBarDim n = screwDim (n − 1)` for `n ≥ 1`**, the converse of
`Graph.eq_add_one_of_bodyBarDim_eq_screwDim`. A statement can then take one `n` and the grade
`n − 1`, without a separate `k` and the hypothesis `bodyBarDim n = screwDim k`. It is here rather
than in `RigidityMatrix/Basic.lean` with `screwDim` because `Graph.bodyBarDim` is defined in
`BodyBar/Framework.lean`, which is not a `module` file, and a `module` file imports only `module`
files (`LEAN-OPS.md` *Module-system conversion*). -/
theorem _root_.Graph.bodyBarDim_eq_screwDim_sub_one {n : ℕ} (hn : 1 ≤ n) :
    Graph.bodyBarDim n = screwDim (n - 1) := by
  rw [Graph.bodyBarDim, screwDim, Nat.choose_two_right,
    show n - 1 + 2 = n + 1 by omega, show n + 1 - 1 = n by omega, Nat.mul_comm]

/-- **The deficiency bound** (`lem:deficiency-rank-bound`): for a nonempty finite set of bodies,
with the hinges at the edges of `G` nondegenerate (`hC`), `D + def(G̃) ≤ dim Z(G,p)`, the deficiency
taken for `n = k + 1`; that is, `rank R(G,p) ≤ D(|V| − 1) − def(G̃)`. Take a partition `f` of the
largest deficiency (`exists_eq_ciSup_of_finite`, a finite supremum). As
`screwDim k = bodyBarDim (k + 1)`, `D·|P| − (D−1)·d_G(P) = D + def(G̃)` there, and the motions
constant on its parts have at least that dimension
(`screwDim_mul_numParts_sub_le_finrank_partitionMotions`). It is one of the two inequalities of the
rank formula in KT Proposition 2.3 (p. 655; `prop:rigidity-matrix-prop11`); Jackson and Jordán
derive its rank form from a count of independent rows (2010, §4, pp. 580–581). -/
theorem screwDim_add_deficiency_le_finrank_infinitesimalMotions [Nonempty α] [Finite α] [Finite β]
    (F : BodyHingeFramework K k α β)
    (hC : ∀ e u v, F.graph.IsLink e u v → F.supportExtensor e ≠ 0) :
    (screwDim k : ℤ) + F.graph.deficiency (k + 1)
      ≤ (Module.finrank K F.infinitesimalMotions : ℤ) := by
  have : Fintype α := Fintype.ofFinite α
  -- `D = screwDim k = bodyBarDim (k+1)` reconciles the screw-space and body-bar `D` conventions.
  have hDcast : (Graph.bodyBarDim (k + 1) : ℤ) = (screwDim k : ℤ) := by
    have : Graph.bodyBarDim (k + 1) = screwDim k := by
      rw [Graph.bodyBarDim, screwDim, Nat.choose_two_right,
        show k + 2 - 1 = k + 1 from rfl, Nat.mul_comm]
    exact_mod_cast this
  -- Pick a partition `f` of `V(G)` attaining `def(G̃)` (a finite supremum under `[Finite α]`).
  obtain ⟨f, hf⟩ := exists_eq_ciSup_of_finite (f := F.graph.partitionDef (k + 1))
  rw [Graph.deficiency, ← hf]
  -- The dimension lower bound at this `f`, and the transfer `partitionMotions f ≤ Z`.
  have hlb := F.screwDim_mul_numParts_sub_le_finrank_partitionMotions f fun e he => by
    obtain ⟨_, x, y, hlink, _⟩ := he
    exact hC e x y hlink
  have hmono : Module.finrank K (F.partitionMotions f)
      ≤ Module.finrank K F.infinitesimalMotions :=
    Submodule.finrank_mono (F.partitionMotions_le_infinitesimalMotions f)
  -- `D·|P| − (D−1)·d_G(P) = D + partitionDef(P)`, so the lower bound reads `D + def ≤ dim Z`.
  rw [Graph.partitionDef, hDcast]
  zify at hmono
  linarith [hlb, hmono]

/-! ### The bound with bodies outside `V(G)` (`lem:relative-deficiency-rank-bound`)

With the bodies outside `V(G)`, the bound reads `D·(|V(G)ᶜ| + 1) + def(G̃) ≤ dim Z(G,p)`. Its proof
counts `|range f|` in place of the number of parts, as `dim W_f = D·|range f|` exactly
(`finrank_partitionConstant`). At a labeling with the same parts on `V(G)` and the same edges
between parts as a partition of the largest deficiency, whose labels on `V(G)` are vertices of `G`
(`Graph.exists_normalized_labeling`, `Molecular/Deficiency.lean`), the range has `|P| + |V(G)ᶜ|`
elements. -/

/-- **The bound with `|range f|` for the number of parts** (a step of
`lem:relative-deficiency-rank-bound`): `D·|range f| − (D−1)·d_G(P) ≤ dim partitionMotions f`, by the
proof of `screwDim_mul_numParts_sub_le_finrank_partitionMotions` with `dim W_f = D·|range f|`
(`finrank_partitionConstant`). -/
theorem screwDim_mul_range_card_sub_le_finrank_partitionMotions [Finite α] [Finite β]
    (F : BodyHingeFramework K k α β) (f : α → α)
    (hC : ∀ e ∈ F.graph.crossingEdges f, F.supportExtensor e ≠ 0) :
    (screwDim k : ℤ) * Nat.card (Set.range f)
        - (screwDim k - 1 : ℤ) * (F.graph.crossingEdges f).ncard
      ≤ (Module.finrank K (F.partitionMotions f) : ℤ) := by
  have : Fintype α := Fintype.ofFinite α
  have : Fintype ↥(F.graph.crossingEdges f) := Fintype.ofFinite _
  have hfull : Module.finrank K (LinearMap.range (F.partitionCutMap f))
      + Module.finrank K (LinearMap.ker (F.partitionCutMap f)) = screwDim k * Fintype.card α := by
    rw [LinearMap.finrank_range_add_finrank_ker, finrank_screwAssignment]
  have hrange : Module.finrank K (LinearMap.range (F.partitionCutMap f))
      ≤ screwDim k * (F.graph.crossingEdges f).ncard - (F.graph.crossingEdges f).ncard := by
    have := (LinearMap.range (F.partitionCutMap f)).finrank_le.trans_eq
      (F.finrank_partitionCutMap_codomain f hC)
    rwa [Nat.sub_mul, one_mul] at this
  have hinf : Module.finrank K (LinearMap.ker (F.partitionCutMap f))
        + Module.finrank K (partitionConstant (K := K) (k := k) f)
      ≤ Module.finrank K (F.partitionMotions f) + screwDim k * Fintype.card α := by
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.ker (F.partitionCutMap f)) (partitionConstant (k := k) f)
    rw [partitionCutMap_ker_inf] at hsup
    have hle : Module.finrank K
          (↥(LinearMap.ker (F.partitionCutMap f) ⊔ partitionConstant (k := k) f))
        ≤ screwDim k * Fintype.card α := by
      rw [← finrank_screwAssignment (K := K) (α := α) (k := k)]
      exact Submodule.finrank_le _
    omega
  -- `finrank W_f = D·|range f|` exactly.
  have hWf : screwDim k * Nat.card (Set.range f)
      = Module.finrank K (partitionConstant (K := K) (k := k) f) := by
    rw [finrank_partitionConstant]
  have hD : 1 ≤ screwDim k := Nat.choose_pos (by omega)
  have hdle : (F.graph.crossingEdges f).ncard ≤ screwDim k * (F.graph.crossingEdges f).ncard :=
    Nat.le_mul_of_pos_left _ (by omega)
  rw [sub_mul, one_mul]
  zify [hdle] at hrange ⊢
  zify at hfull hinf hWf
  omega

/-- **The relative deficiency bound** (`lem:relative-deficiency-rank-bound`): if
`bodyBarDim n = screwDim k`, `V(G)` is nonempty and the hinges at the edges of `G` are
nondegenerate, then `D·(|V(G)ᶜ| + 1) + def(G̃) ≤ dim Z(G,p)`, where `V(G)ᶜ` is the set of the bodies
outside `V(G)`. A partition `f₀` of the largest deficiency is relabelled by
`Graph.exists_normalized_labeling` as `g`, with the same parts and edges between parts and
`|range g| = numParts f₀ + |V(G)ᶜ|`, and the bound with `|range g|`
(`screwDim_mul_range_card_sub_le_finrank_partitionMotions`) applies at `g`. -/
theorem screwDim_mul_compl_add_deficiency_le_finrank_infinitesimalMotions
    [Finite α] [Finite β] {n : ℕ}
    (F : BodyHingeFramework K k α β)
    (hn : Graph.bodyBarDim n = screwDim k)
    (hne : F.graph.vertexSet.Nonempty)
    (hC : ∀ e u v, F.graph.IsLink e u v → F.supportExtensor e ≠ 0) :
    (screwDim k : ℤ) * (F.graph.vertexSetᶜ.ncard + 1) + F.graph.deficiency n
      ≤ (Module.finrank K F.infinitesimalMotions : ℤ) := by
  have : Nonempty α := ⟨hne.some⟩
  -- Pick the def-attaining partition `f₀`, and normalize it into `V(G)`.
  obtain ⟨f₀, hf₀⟩ := exists_eq_ciSup_of_finite (f := F.graph.partitionDef n)
  rw [Graph.deficiency, ← hf₀]
  obtain ⟨g, -, -, hcross, hrange_g, -⟩ := F.graph.exists_normalized_labeling f₀
  -- Apply the `|range g|`-form motion bound.
  have hCg : ∀ e ∈ F.graph.crossingEdges g, F.supportExtensor e ≠ 0 := fun e he => by
    obtain ⟨_, x, y, hlink, _⟩ := he
    exact hC e x y hlink
  have hlb := F.screwDim_mul_range_card_sub_le_finrank_partitionMotions g hCg
  have hmono : Module.finrank K (F.partitionMotions g)
      ≤ Module.finrank K F.infinitesimalMotions :=
    Submodule.finrank_mono (F.partitionMotions_le_infinitesimalMotions g)
  rw [hrange_g, hcross] at hlb
  have hDcast : (Graph.bodyBarDim n : ℤ) = (screwDim k : ℤ) := by exact_mod_cast hn
  have hpdef_eq : F.graph.partitionDef n f₀
      = (screwDim k : ℤ) * ((F.graph.numParts f₀ : ℤ) - 1)
        - (screwDim k - 1 : ℤ) * (F.graph.crossingEdges f₀).ncard := by
    simp [Graph.partitionDef, hDcast]
  zify at hmono hlb ⊢
  linarith [hpdef_eq]

end BodyHingeFramework

end CombinatorialRigidity.Molecular
