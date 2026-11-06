/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Mathlib.LinearAlgebra.Pi
public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Lift
public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Arms
public import CombinatorialRigidity.Molecular.Molecule.Pencil.Pair
public import CombinatorialRigidity.Molecular.AlgebraicInduction.DeficiencyBound

/-!
# One lift suffices, and lifts restrict to a subgraph

The two nodes of `blueprint/src/chapter/pencil-d.tex` that follow `def:pencil-d-lift-attains`:

* `lem:pencil-d-lift-one-witness`: `LiftAttains` is homogeneous in each body (`bodyWeight`); one
  lift of least `dim L̃` (`liftSpaceTilde`) of the target rank gives the general lift attaining
  (`liftAttains_of_least`); the least value is taken generally
  (`exists_holdsGenerally_finrank_liftSpaceTilde_le`), so a general realization with one suffices
  (`liftAttains_of_holdsGenerally`).
* `lem:pencil-d-lift-transfer`: the lifts of a subgraph that attain form a nonempty Zariski-open
  set of the maps (`lift_transfer`).
-/

@[expose] public section

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

/-! ## Homogeneous in each body -/

/-- The weight of the variable `(v, i)` of the normals: its body `v`, so that a polynomial
weighted homogeneous for it is homogeneous in each normal `b⁰_v` (`def:pencil-d-lift-attains`). -/
noncomputable def bodyWeight : α × Fin 4 → (α →₀ ℕ) := fun p => Finsupp.single p.1 1

/-- Scaling the normals by `c_v` scales a monomial by `c^(weight)`. -/
theorem eval_smul_monomial (μ : α × Fin 4 →₀ ℕ) (b : α × Fin 4 → K) (c : α → K) :
    MvPolynomial.eval (fun p => c p.1 * b p) (MvPolynomial.monomial μ (1 : K)) =
      MvPolynomial.eval c (MvPolynomial.monomial (Finsupp.weight bodyWeight μ) 1) *
        MvPolynomial.eval b (MvPolynomial.monomial μ 1) := by
  simp only [MvPolynomial.eval_monomial, one_mul, mul_pow]
  rw [Finsupp.prod_mul, Finsupp.weight_apply, Finsupp.prod_sum_index (fun _ => pow_zero _)
    (fun _ _ _ => pow_add _ _ _)]
  congr 1
  refine Finsupp.prod_congr fun p _ => ?_
  rw [bodyWeight, Finsupp.smul_single, smul_eq_mul, mul_one,
    Finsupp.prod_single_index (h := fun x k => c x ^ k) (pow_zero (c p.1))]

/-- **Homogenizing in each body** (`lem:pencil-d-lift-one-witness`, the last step of (1)): if
`Q₀(b₀) ≠ 0`, some component `Q` of `Q₀` of one degree in each `b_v` has `Q(b₀) ≠ 0`, and wherever
`Q(b) ≠ 0` some nonzero scalars `c_v` have `Q₀(cb) ≠ 0`: as a polynomial in `c`, `Q₀(cb)` has `Q(b)`
as a coefficient, and its product with `∏ c_v` has a non-root. -/
theorem exists_weightedHomogeneousComponent_of_eval_ne_zero [Infinite K] [Finite α]
    {Q₀ : MvPolynomial (α × Fin 4) K} {b₀ : α × Fin 4 → K} (h : MvPolynomial.eval b₀ Q₀ ≠ 0) :
    ∃ d : α →₀ ℕ,
      MvPolynomial.eval b₀ (MvPolynomial.weightedHomogeneousComponent bodyWeight d Q₀) ≠ 0 ∧
      ∀ b, MvPolynomial.eval b (MvPolynomial.weightedHomogeneousComponent bodyWeight d Q₀) ≠ 0 →
        ∃ c : α → K, (∀ v, c v ≠ 0) ∧ MvPolynomial.eval (fun p => c p.1 * b p) Q₀ ≠ 0 := by
  classical
  have := Fintype.ofFinite α
  -- `Q₀(b₀)` is the sum of its components' values
  have hsum : ∀ b, MvPolynomial.eval b Q₀ = ∑ μ ∈ Q₀.support,
      Q₀.coeff μ * MvPolynomial.eval b (MvPolynomial.monomial μ 1) := by
    intro b
    conv_lhs => rw [Q₀.as_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial, one_mul]
  have hcomp : ∀ b d, MvPolynomial.eval b (MvPolynomial.weightedHomogeneousComponent bodyWeight d
      Q₀) = ∑ μ ∈ Q₀.support with Finsupp.weight bodyWeight μ = d,
        Q₀.coeff μ * MvPolynomial.eval b (MvPolynomial.monomial μ 1) := by
    intro b d
    rw [MvPolynomial.weightedHomogeneousComponent_apply, map_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial, one_mul]
  obtain ⟨d, hd⟩ : ∃ d, MvPolynomial.eval b₀
      (MvPolynomial.weightedHomogeneousComponent bodyWeight d Q₀) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply h
    rw [hsum, ← Finset.sum_fiberwise_of_maps_to (g := Finsupp.weight bodyWeight)
      (t := Q₀.support.image (Finsupp.weight bodyWeight))
      (fun μ hμ => Finset.mem_image_of_mem _ hμ)]
    refine Finset.sum_eq_zero fun d' _ => ?_
    rw [← hcomp]; exact hall d'
  refine ⟨d, hd, fun b hb => ?_⟩
  set R : MvPolynomial α K := ∑ μ ∈ Q₀.support, MvPolynomial.monomial
    (Finsupp.weight bodyWeight μ) (Q₀.coeff μ * MvPolynomial.eval b (MvPolynomial.monomial μ 1))
  have hR : ∀ c, MvPolynomial.eval c R = MvPolynomial.eval (fun p => c p.1 * b p) Q₀ := by
    intro c
    rw [hsum, map_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [eval_smul_monomial, MvPolynomial.eval_monomial, MvPolynomial.eval_monomial,
      MvPolynomial.eval_monomial]
    ring
  have hcoeff : R.coeff d = MvPolynomial.eval b
      (MvPolynomial.weightedHomogeneousComponent bodyWeight d Q₀) := by
    rw [hcomp, MvPolynomial.coeff_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [MvPolynomial.coeff_monomial]
  have hR0 : R ≠ 0 := fun h0 => hb (by rw [← hcoeff, h0]; rfl)
  have hX : (∏ v, MvPolynomial.X v : MvPolynomial α K) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun v _ => MvPolynomial.X_ne_zero v
  obtain ⟨c, hc⟩ := MvPolynomial.exists_eval_ne_zero (mul_ne_zero hR0 hX)
  rw [map_mul, map_prod] at hc
  refine ⟨c, fun v h0 => ?_, ?_⟩
  · exact hc (by rw [Finset.prod_eq_zero (Finset.mem_univ v) (by simpa using h0), mul_zero])
  · rw [← hR]; exact left_ne_zero_of_mul hc

/-! ## One lift suffices -/

/-- **The space `L̃(b⁰)`** (`lem:pencil-d-lift-one-witness`): pairs `(ζ, ψ)` of a map on the
bodies (at `Sum.inl`) and linear forms `ψ_v` on `K⁴` (their coordinates, at `Sum.inr (v, i)`),
with `ζ_w = ψ_v(b⁰_w)` for every body `v` and `w` in its closed neighbourhood. -/
def liftSpaceTilde (G : Graph α β) (b0 : α → Fin 4 → K) : Submodule K (α ⊕ α × Fin 4 → K) where
  carrier := {z | ∀ v ∈ V(G), ∀ w ∈ G.closedNbhd v, z (.inl w) = ∑ i, z (.inr (v, i)) * b0 w i}
  add_mem' {x y} hx hy v hv w hw := by
    simp [hx v hv w hw, hy v hv w hw, Finset.sum_add_distrib, add_mul]
  zero_mem' := by simp
  smul_mem' c x hx v hv w hw := by simp [hx v hv w hw, Finset.mul_sum, mul_assoc]

open Classical in
/-- **The matrix `A(b⁰)`** of `lem:pencil-d-lift-one-witness`, with entries polynomial in the
normals: the row of a body `v` and `w` in its closed neighbourhood is
`(ζ, ψ) ↦ ζ_w − ψ_v(b⁰_w)`; every other row is zero. -/
noncomputable def liftMatrixPoly (G : Graph α β) :
    Matrix (α × α) (α ⊕ α × Fin 4) (MvPolynomial (α × Fin 4) K) :=
  fun p c => if p.1 ∈ V(G) ∧ p.2 ∈ G.closedNbhd p.1 then
    Sum.elim (fun u => if u = p.2 then 1 else 0)
      (fun q => if q.1 = p.1 then -MvPolynomial.X (p.2, q.2) else 0) c
  else 0

/-- `L̃(b⁰)` is the kernel of `A(b⁰)` (`lem:pencil-d-lift-one-witness`). -/
theorem liftSpaceTilde_eq_ker [Fintype α] (G : Graph α β) (b0 : α → Fin 4 → K) :
    liftSpaceTilde G b0 = LinearMap.ker ((liftMatrixPoly (K := K) G).map
      (MvPolynomial.eval fun p => b0 p.1 p.2)).mulVecLin := by
  classical
  ext z
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, funext_iff, Pi.zero_apply]
  have key : ∀ v w, ((liftMatrixPoly (K := K) G).map
      (MvPolynomial.eval fun p => b0 p.1 p.2) *ᵥ z) (v, w) =
      if v ∈ V(G) ∧ w ∈ G.closedNbhd v then z (.inl w) - ∑ i, z (.inr (v, i)) * b0 w i else 0 := by
    intro v w
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, liftMatrixPoly]
    split_ifs with h
    · rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, apply_ite, map_one, map_zero, map_neg,
        MvPolynomial.eval_X, ite_mul, one_mul, zero_mul, neg_mul, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true, Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_neg_distrib,
        sub_eq_add_neg, mul_comm]
    · simp
  simp only [key]
  constructor
  · rintro hz ⟨v, w⟩
    split_ifs with h
    · rw [hz v h.1 w h.2, sub_self]
    · rfl
  · intro hz v hv w hw
    have := hz (v, w)
    rw [ite_eq_left ⟨hv, hw⟩] at this
    exact sub_eq_zero.1 this

/-- A lift gives a member of `L̃`: its forms extend to `K⁴` (`LinearMap.exists_extend`). -/
theorem exists_mem_liftSpaceTilde_of_mem_liftSpace {G : Graph α β} {b0 : α → Fin 4 → K}
    {P0 : α → Submodule K (Fin 4 → K)} (hP0 : ∀ v ∈ V(G), ∀ w ∈ G.closedNbhd v, b0 w ∈ P0 v)
    {lam : (α → K) × ((v : α) → Module.Dual K (P0 v))} (hlam : lam ∈ liftSpace G b0 P0) :
    ∃ z ∈ liftSpaceTilde G b0, ∀ w, z (.inl w) = lam.1 w := by
  choose ψ hψ using fun v => LinearMap.exists_extend (lam.2 v)
  refine ⟨Sum.elim lam.1 fun q => ψ q.1 (Pi.single q.2 1), fun v hv w hw => ?_, fun w => rfl⟩
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [hlam v hv w hw (hP0 v hv w hw), ← hψ v, LinearMap.comp_apply, Submodule.subtype_apply,
    LinearMap.pi_apply_eq_sum_univ_single (ψ v) (b0 w)]
  simp only [smul_eq_mul, mul_comm]

/-- A member of `L̃` gives a lift: the forms restricted to `Π⁰_v`. -/
theorem exists_mem_liftSpace_of_mem_liftSpaceTilde {G : Graph α β} {b0 : α → Fin 4 → K}
    (P0 : α → Submodule K (Fin 4 → K)) {z : α ⊕ α × Fin 4 → K} (hz : z ∈ liftSpaceTilde G b0) :
    ∃ lam ∈ liftSpace G b0 P0, lam.1 = fun w => z (.inl w) := by
  let ψ : α → Module.Dual K (Fin 4 → K) := fun v =>
    { toFun := fun x => ∑ i, z (.inr (v, i)) * x i
      map_add' := fun x y => by simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring }
  exact ⟨(fun w => z (.inl w), fun v => (ψ v).domRestrict (P0 v)),
    fun v hv w hw _ => hz v hv w hw, rfl⟩

theorem isPolyFun_sum {σ ι : Type*} (t : Finset ι) {f : ι → (σ → K) → K}
    (hf : ∀ i, IsPolyFun (f i)) : IsPolyFun fun s => ∑ i ∈ t, f i s := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using isPolyFun_const (σ := σ) (0 : K)
  | insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a).add ih

theorem liftVec_eq_sum {r : ℕ} (p : Fin 4 → K) (u : Fin r → K) :
    liftVec p u = ∑ i, p i • liftVec (Pi.single i 1) 0 + ∑ i, u i • liftVec 0 (Pi.single i 1) := by
  have hpu : (p, u) = ∑ i, p i • ((Pi.single i 1 : Fin 4 → K), (0 : Fin r → K)) +
      ∑ i, u i • ((0 : Fin 4 → K), (Pi.single i 1 : Fin r → K)) := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.fst_sum, Prod.smul_fst, smul_zero, Finset.sum_const_zero,
        add_zero]
      funext j; simp [Finset.sum_apply, Pi.single_apply]
    · simp only [Prod.snd_add, Prod.snd_sum, Prod.smul_snd, smul_zero, Finset.sum_const_zero,
        zero_add]
      funext j; simp [Finset.sum_apply, Pi.single_apply]
  rw [← liftVecEquiv_apply (p, u), hpu, map_add, map_sum, map_sum]
  simp only [map_smul, liftVecEquiv_apply]

theorem isPolyFun_liftVec {σ : Type*} {r : ℕ} {p : (σ → K) → Fin 4 → K}
    {u : (σ → K) → Fin r → K} (hp : ∀ i, IsPolyFun fun s => p s i)
    (hu : ∀ i, IsPolyFun fun s => u s i) (j : Fin (r + 1 + 1 + 2)) :
    IsPolyFun fun s => liftVec (p s) (u s) j := by
  have key : (fun s => liftVec (p s) (u s) j) = fun s => ∑ i, p s i * liftVec (Pi.single i 1) 0 j +
      ∑ i, u s i * liftVec 0 (Pi.single i 1) j := by
    funext s
    rw [liftVec_eq_sum]
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [key]
  exact (isPolyFun_sum _ fun i => (hp i).mul (isPolyFun_const _)).add
    (isPolyFun_sum _ fun i => (hu i).mul (isPolyFun_const _))

/-- The normals of a lift are independent at the ends of a link where those of `b⁰` are. -/
theorem linearIndependent_liftNormal {r : ℕ} {b0 : α → Fin 4 → K} (ζ : Fin r → α → K)
    {u v : α} (h : LinearIndependent K ![b0 u, b0 v]) :
    LinearIndependent K ![liftNormal b0 ζ u, liftNormal b0 ζ v] := by
  refine LinearIndependent.of_comp liftProj ?_
  convert h using 1
  funext i; fin_cases i <;> exact liftProj_liftVec _ _

/-- The lift space only reads the normals on `V(G)`. -/
theorem liftSpace_congr {G : Graph α β} {b0 b0' : α → Fin 4 → K}
    {P0 : α → Submodule K (Fin 4 → K)} (h : ∀ v ∈ V(G), b0' v = b0 v) :
    liftSpace G b0' P0 = liftSpace G b0 P0 := by
  ext lam
  simp only [mem_liftSpace]
  refine forall₂_congr fun v hv => forall₂_congr fun w hw => ?_
  have hw' := h w (Graph.closedNbhd_subset_vertexSet hv hw)
  constructor
  · intro h' hb
    have e : (⟨b0' w, hw' ▸ hb⟩ : P0 v) = ⟨b0 w, hb⟩ := Subtype.ext hw'
    rw [h' (hw' ▸ hb), e]
  · intro h' hb
    have e : (⟨b0 w, hw' ▸ hb⟩ : P0 v) = ⟨b0' w, hb⟩ := Subtype.ext hw'.symm
    rw [h' (hw' ▸ hb), e]

/-- The rank only reads the normals on `V(G)`. -/
theorem finrank_ofNormals_congr {k : ℕ} {G : Graph α β} {ends : β → α × α}
    (hlinks : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2)
    {q q' : α → Fin (k + 2) → K} (h : ∀ v ∈ V(G), q' v = q v) :
    Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := k) G ends
        (fun p => q' p.1 p.2)).toBodyHinge.rigidityRows)
      = Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := k) G ends
        (fun p => q p.1 p.2)).toBodyHinge.rigidityRows) := by
  set F₁ := (PanelHingeFramework.ofNormals (k := k) G ends (fun p => q' p.1 p.2)).toBodyHinge
  set F₂ := (PanelHingeFramework.ofNormals (k := k) G ends (fun p => q p.1 p.2)).toBodyHinge
  have hprop : ∀ e u v, F₁.graph.IsLink e u v →
      ∃ c' : K, c' ≠ 0 ∧ c' • F₁.supportExtensor e = F₂.supportExtensor e := by
    intro e u v he
    have h0 := hlinks e u v he
    refine ⟨1, one_ne_zero, ?_⟩
    rw [one_smul]
    change panelSupportExtensor (q' (ends e).1) (q' (ends e).2) =
      panelSupportExtensor (q (ends e).1) (q (ends e).2)
    rw [h _ h0.left_mem, h _ h0.right_mem]
  rw [span_rigidityRows_eq_of_supportExtensor_proportional F₁ F₂ rfl hprop]

/-- Scaling and patching off `V(G)` keep a nondegenerate realization in dimension three. -/
theorem exists_isNondeg_of_smul {G : Graph α β} {F : BodyHingeFramework K 2 α β}
    {b0 b' : α → Fin 4 → K} {P0 : α → Submodule K (Fin 4 → K)}
    (hnd : IsNondegPencilPlaneRealization G F b0 P0) {c : α → K} (hc : ∀ v ∈ V(G), c v ≠ 0)
    (hb' : ∀ v ∈ V(G), b' v = c v • b0 v) :
    ∃ F' : BodyHingeFramework K 2 α β, IsNondegPencilPlaneRealization G F' b' P0 := by
  have hlink : ∀ e u v, G.IsLink e u v → LinearIndependent K ![b' u, b' v] := by
    intro e u v he
    have h2 := (hnd.2.1 e u v he).units_smul ![Units.mk0 (c u) (hc u he.left_mem),
      Units.mk0 (c v) (hc v he.right_mem)]
    convert h2 using 1
    funext i; fin_cases i
    · simp [Units.smul_def, hb' u he.left_mem]
    · simp [Units.smul_def, hb' v he.right_mem]
  obtain ⟨F', hF'⟩ := exists_hasPencilPlaneRealization (k := 2) (G := G) (β := β) (b := b')
    (plane := P0) (fun v hv => by rw [hb' v hv]; exact smul_ne_zero (hc v hv) (hnd.1.1.2.1 v hv))
    hlink (fun v hv => hnd.1.2.1 v hv) (fun v hv w hw => by
      rw [hb' w (Graph.closedNbhd_subset_vertexSet hv hw)]
      exact (P0 v).smul_mem _ (hnd.1.normal_mem_plane_of_mem_closedNbhd hv hw))
  refine ⟨F', hF', hlink, fun v hv hhub => ?_, hnd.2.2.2⟩
  exact LinearIndepOn.of_smul_eq (hnd.2.2.1 v hv hhub) fun w hw =>
    ⟨c w, hc w (Graph.closedNbhd_subset_vertexSet hv hw),
      hb' w (Graph.closedNbhd_subset_vertexSet hv hw)⟩

/-- With no body there is no row. -/
theorem finrank_span_rigidityRows_eq_zero_of_vertexSet {k : ℕ} {F : BodyHingeFramework K k α β}
    (h : V(F.graph) = ∅) : Module.finrank K (Submodule.span K F.rigidityRows) = 0 := by
  have : F.rigidityRows = ∅ := by
    ext φ
    simp only [BodyHingeFramework.rigidityRows, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
      iff_false, not_exists, not_and]
    intro e u v he
    have := he.left_mem
    rw [h] at this
    exact absurd this (Set.notMem_empty u)
  rw [this, Submodule.span_empty, finrank_bot]

/-- **The rank of a lift is at most the target** (the bound of
`lem:relative-deficiency-rank-bound`), as its hinges are nonzero. -/
theorem finrank_liftNormal_le [Finite α] [Finite β] {r : ℕ} {G : Graph α β} {ends : β → α × α}
    (hlinks : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2) {b0 : α → Fin 4 → K}
    (hlink : ∀ e u v, G.IsLink e u v → LinearIndependent K ![b0 u, b0 v])
    (hne : V(G).Nonempty) (ζ : Fin r → α → K) :
    (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := r + 1 + 1) G ends
        (fun p => liftNormal b0 ζ p.1 p.2)).toBodyHinge.rigidityRows) : ℤ)
      ≤ screwDim (r + 1 + 1) * ((V(G).ncard : ℤ) - 1) - G.deficiency (r + 1 + 2) := by
  refine BodyHingeFramework.finrank_span_rigidityRows_add_deficiency_le _
    (Graph.bodyBarDim_add_one_eq_screwDim (r + 1 + 1)) hne fun e u v he _ => ?_
  have h0 := hlinks e u v he
  change panelSupportExtensor (liftNormal b0 ζ (ends e).1) (liftNormal b0 ζ (ends e).2) ≠ 0
  rw [panelSupportExtensor_ne_zero_iff]
  exact linearIndependent_liftNormal ζ (hlink e _ _ h0)

/-- **One lift suffices** (`lem:pencil-d-lift-one-witness`, part (1)): a nondegenerate realization
`r* = (b*, Π*)` in dimension three at which `dim L̃(b*)` is least, with a lift of rank `tgt_d(G)`,
makes the general lift attain. The Lean takes the lift's maps through `L̃` by the polynomial section
of `A(b⁰)` (`Matrix.exists_mvPolynomial_section_mulVec_eq_zero`, one per lift parameter); the rank
polynomial (`PanelHingeFramework.exists_rankPolynomial_of_le_finrank_linking`) and the
homogenization (`exists_weightedHomogeneousComponent_of_eval_ne_zero`) complete it. -/
theorem liftAttains_of_least [Infinite K] [Finite α] [Finite β] {r : ℕ} {G : Graph α β}
    {F : BodyHingeFramework K 2 α β} {b : α → Fin 4 → K} {P : α → Submodule K (Fin 4 → K)}
    (hnd : IsNondegPencilPlaneRealization G F b P)
    (hleast : ∀ (F' : BodyHingeFramework K 2 α β) (b' : α → Fin 4 → K)
      (P' : α → Submodule K (Fin 4 → K)), IsNondegPencilPlaneRealization G F' b' P' →
      Module.finrank K (liftSpaceTilde G b) ≤ Module.finrank K (liftSpaceTilde G b'))
    {lam : Fin r → (α → K) × ((v : α) → Module.Dual K (P v))}
    (hlam : ∀ i, lam i ∈ liftSpace G b P) {ends : β → α × α}
    (hlinks : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2)
    (hrank : (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := r + 1 + 1) G
        ends (fun p => liftNormal b (fun i => (lam i).1) p.1 p.2)).toBodyHinge.rigidityRows) : ℤ)
      = screwDim (r + 1 + 1) * ((V(G).ncard : ℤ) - 1) - G.deficiency (r + 1 + 2)) :
    LiftAttains K r G := by
  classical
  have := Fintype.ofFinite α
  have hP : ∀ v ∈ V(G), ∀ w ∈ G.closedNbhd v, b w ∈ P v := fun v hv w hw =>
    hnd.1.normal_mem_plane_of_mem_closedNbhd hv hw
  choose z hz hzl using fun i => exists_mem_liftSpaceTilde_of_mem_liftSpace hP (hlam i)
  set q₀ : α × Fin 4 → K := fun p => b p.1 p.2 with hq₀
  have hz₀ : ∀ i, (liftMatrixPoly (K := K) G).map (MvPolynomial.eval q₀) *ᵥ z i = 0 := fun i => by
    have := hz i
    rw [liftSpaceTilde_eq_ker] at this
    exact this
  choose D Z hD₀ hZ₀ _ hZker using fun i =>
    Matrix.exists_mvPolynomial_section_mulVec_eq_zero (liftMatrixPoly (K := K) G) (hz₀ i)
  -- the normals of the lift through the sections, polynomial in the normals
  let nrm : (α × Fin 4 → K) → α × Fin (r + 1 + 1 + 2) → K := fun q p =>
    liftVec (fun j => q (p.1, j)) (fun i => MvPolynomial.eval q (Z i (.inl p.1))) p.2
  have hnrm_poly : ∀ p, IsPolyFun fun q => nrm q p := fun p =>
    isPolyFun_liftVec (fun j => isPolyFun_apply (p.1, j)) (fun i => ⟨Z i (.inl p.1), fun _ => rfl⟩)
      p.2
  have hnrm : ∀ (q : α × Fin 4 → K) (ζ : Fin r → α → K),
      (∀ i v, MvPolynomial.eval q (Z i (.inl v)) = ζ i v) →
      nrm q = fun p => liftNormal (fun v j => q (v, j)) ζ p.1 p.2 := by
    intro q ζ hζ
    funext p
    simp only [nrm, liftNormal, hζ]
  have hnrm₀ : nrm q₀ = fun p => liftNormal b (fun i => (lam i).1) p.1 p.2 :=
    hnrm q₀ _ fun i v => by rw [← hzl i v, ← hZ₀ i]
  -- the rank polynomial at `b`
  have hlink₀ : ∀ e u v, G.IsLink e u v → LinearIndependent K ![b u, b v] := hnd.2.1
  have hne₀ : ∀ e, G.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals (k := r + 1 + 1) G ends (nrm q₀)).toBodyHinge.supportExtensor e
        ≠ 0 := by
    intro e he
    rw [hnrm₀]
    change panelSupportExtensor (liftNormal b _ (ends e).1) (liftNormal b _ (ends e).2) ≠ 0
    rw [panelSupportExtensor_ne_zero_iff]
    exact linearIndependent_liftNormal _ (hlink₀ e _ _ he)
  obtain ⟨Pr, hPr₀, hPr⟩ := PanelHingeFramework.exists_rankPolynomial_of_le_finrank_linking G ends
    hlinks hne₀ le_rfl
  obtain ⟨Pc, hPc⟩ := IsPolyFun.comp Pr hnrm_poly
  -- `Q₀`, with the bodies off `V(G)` fixed at `b`
  set Q₀ : MvPolynomial (α × Fin 4) K := (∏ i, D i) * Pc with hQ₀def
  set patch : α × Fin 4 → MvPolynomial (α × Fin 4) K := fun p =>
    if p.1 ∈ V(G) then MvPolynomial.X p else MvPolynomial.C (q₀ p)
  set Q₁ := MvPolynomial.bind₁ patch Q₀
  have hQ₁ : ∀ q, MvPolynomial.eval q Q₁ =
      MvPolynomial.eval (fun p => if p.1 ∈ V(G) then q p else q₀ p) Q₀ := by
    intro q
    rw [MvPolynomial.eval_bind₁]
    refine congrArg (fun f => MvPolynomial.eval f Q₀) (funext fun p => ?_)
    simp only [patch]
    split_ifs <;> simp
  have hQ₀₀ : MvPolynomial.eval q₀ Q₀ ≠ 0 := by
    rw [hQ₀def, map_mul, map_prod, ← hPc]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => hD₀ i) hPr₀
  have hQ₁₀ : MvPolynomial.eval q₀ Q₁ ≠ 0 := by
    have e : (fun p => if p.1 ∈ V(G) then q₀ p else q₀ p) = q₀ := funext fun p => by
      split_ifs <;> rfl
    rw [hQ₁, e]; exact hQ₀₀
  obtain ⟨d, hd₀, hd⟩ := exists_weightedHomogeneousComponent_of_eval_ne_zero hQ₁₀
  refine ⟨ends, hlinks, MvPolynomial.weightedHomogeneousComponent bodyWeight d Q₁, ?_,
    ⟨d, MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous _ _⟩,
    ⟨F, b, P, hnd, hd₀⟩, ?_⟩
  · -- the variables are bodies of `G`
    intro p hp
    rw [MvPolynomial.mem_vars_iff_mem_support] at hp
    obtain ⟨μ, hμ, hpμ⟩ := hp
    have hμ' : μ ∈ Q₁.support := by
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_weightedHomogeneousComponent] at hμ
      rw [MvPolynomial.mem_support_iff]
      split_ifs at hμ
      · exact hμ
      · exact absurd rfl hμ
    have hpv : p ∈ Q₁.vars := MvPolynomial.mem_vars_iff_mem_support p |>.2 ⟨μ, hμ', hpμ⟩
    obtain ⟨p', -, hp'⟩ := Finset.mem_biUnion.1 (MvPolynomial.vars_bind₁ patch Q₀ hpv)
    simp only [patch] at hp'
    split_ifs at hp' with h
    · rw [MvPolynomial.vars_X, Finset.mem_singleton] at hp'
      rw [hp']; exact h
    · simp at hp'
  · intro F' b0 P0 hnd' hQ
    obtain ⟨c, hc, hcQ⟩ := hd _ hQ
    -- `b̃`: `c b⁰` on `V(G)`, `b` off it
    set bt : α → Fin 4 → K := fun v j => if v ∈ V(G) then c v * b0 v j else b v j with hbt
    have hbtV : ∀ v ∈ V(G), bt v = c v • b0 v := fun v hv => by
      funext j; simp [hbt, hv]
    have hQ₀t : MvPolynomial.eval (fun p => bt p.1 p.2) Q₀ ≠ 0 := by
      rw [hQ₁] at hcQ
      have e : (fun p : α × Fin 4 => if p.1 ∈ V(G) then c p.1 * b0 p.1 p.2 else q₀ p) =
          fun p => bt p.1 p.2 := funext fun p => by
        simp only [hbt, q₀]
      rwa [e] at hcQ
    obtain ⟨Ft, hndt⟩ := exists_isNondeg_of_smul hnd' (fun v _ => hc v) hbtV
    rw [hQ₀def, map_mul, map_prod] at hQ₀t
    have hDt : ∀ i, MvPolynomial.eval (fun p => bt p.1 p.2) (D i) ≠ 0 := fun i =>
      Finset.prod_ne_zero_iff.1 (left_ne_zero_of_mul hQ₀t) i (Finset.mem_univ i)
    have hPct := right_ne_zero_of_mul hQ₀t
    rw [← hPc] at hPct
    -- the sections lie in `L̃(b̃)`
    have hge : Module.finrank K (LinearMap.ker ((liftMatrixPoly (K := K) G).map
        (MvPolynomial.eval q₀)).mulVecLin) ≤ Module.finrank K (LinearMap.ker
        ((liftMatrixPoly (K := K) G).map (MvPolynomial.eval fun p => bt p.1 p.2)).mulVecLin) := by
      rw [← liftSpaceTilde_eq_ker, ← liftSpaceTilde_eq_ker]
      exact hleast _ _ _ hndt
    have hZt : ∀ i, (fun c => MvPolynomial.eval (fun p => bt p.1 p.2) (Z i c)) ∈
        liftSpaceTilde G bt := fun i => by
      rw [liftSpaceTilde_eq_ker]
      exact hZker i _ hge (hDt i)
    choose lt hlt hlt1 using fun i => exists_mem_liftSpace_of_mem_liftSpaceTilde P0 (hZt i)
    -- the rank at `b̃`
    have hnrmt : nrm (fun p => bt p.1 p.2) = fun p => liftNormal bt (fun i => (lt i).1) p.1 p.2 :=
      hnrm (fun p => bt p.1 p.2) (fun i => (lt i).1) fun i v => by rw [hlt1 i]
    have hrkt : (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := r + 1 + 1)
        G ends (fun p => liftNormal bt (fun i => (lt i).1) p.1 p.2)).toBodyHinge.rigidityRows) : ℤ)
        = screwDim (r + 1 + 1) * ((V(G).ncard : ℤ) - 1) - G.deficiency (r + 1 + 2) := by
      rcases V(G).eq_empty_or_nonempty with hV | hV
      · rw [← hrank, finrank_span_rigidityRows_eq_zero_of_vertexSet hV,
          finrank_span_rigidityRows_eq_zero_of_vertexSet hV]
      · refine le_antisymm (finrank_liftNormal_le hlinks hndt.2.1 hV _) ?_
        rw [← hrank, ← hnrm₀, ← hnrmt]
        exact_mod_cast hPr _ hPct
    -- back to `b⁰`: patch, then unscale
    refine ⟨fun i => liftSmul (fun v => (c v)⁻¹) (lt i), fun i => ?_, ?_⟩
    · have h1 : lt i ∈ liftSpace G (fun v => c v • b0 v) P0 := by
        rw [← liftSpace_congr hbtV]; exact hlt i
      have h2 := (liftSmul_mem_liftSpace_iff (fun v _ => inv_ne_zero (hc v))
        (b0 := fun v => c v • b0 v)).2 h1
      rwa [liftSpace_congr (b0 := b0) fun v _ => by
        rw [smul_smul, inv_mul_cancel₀ (hc v), one_smul]] at h2
    · have e1 : ∀ v, liftNormal (fun v => c v • b0 v) (fun i => (lt i).1) v =
          c v • liftNormal b0 (fun i => (liftSmul (fun v => (c v)⁻¹) (lt i)).1) v := by
        intro v
        rw [← liftNormal_smul]
        congr 1
        funext i v'
        simp [liftSmul, mul_inv_cancel_left₀ (hc v')]
      have h1 := finrank_ofNormals_congr (k := r + 1 + 1) hlinks
        (q := liftNormal (fun v => c v • b0 v) (fun i => (lt i).1))
        (q' := liftNormal bt (fun i => (lt i).1)) fun v hv => by
          simp only [liftNormal, hbtV v hv]
      have h2 : (fun p : α × Fin (r + 1 + 1 + 2) =>
          liftNormal (fun v => c v • b0 v) (fun i => (lt i).1) p.1 p.2) =
          fun p => (c p.1 • liftNormal b0 (fun i => (liftSmul (fun v => (c v)⁻¹) (lt i)).1) p.1)
            p.2 := funext fun p => by rw [e1]
      have h3 := finrank_span_rigidityRows_ofNormals_smul (k := r + 1 + 1) hlinks
        (fun v _ => hc v) (liftNormal b0 fun i => (liftSmul (fun v => (c v)⁻¹) (lt i)).1)
      rw [← hrkt, h1, h2, h3]

/-- Rescaling the normals on `V(G)` keeps `dim L̃`. -/
theorem finrank_liftSpaceTilde_smul {G : Graph α β} {b b' : α → Fin 4 → K} {c : α → K}
    (hc : ∀ v ∈ V(G), c v ≠ 0) (hb' : ∀ v ∈ V(G), b' v = c v • b v) :
    Module.finrank K (liftSpaceTilde G b') = Module.finrank K (liftSpaceTilde G b) := by
  classical
  let scale : α ⊕ α × Fin 4 → K := Sum.elim (fun w => if w ∈ V(G) then c w else 1) fun _ => 1
  have hscale : ∀ x, scale x ≠ 0 := by
    rintro (w | q)
    · by_cases hw : w ∈ V(G) <;> simp [scale, hw, hc w]
    · simp [scale]
  let E : (α ⊕ α × Fin 4 → K) ≃ₗ[K] (α ⊕ α × Fin 4 → K) :=
    LinearEquiv.piCongrRight fun x => LinearEquiv.smulOfNeZero K K (scale x) (hscale x)
  have hE : ∀ z x, E z x = scale x * z x := fun z x => rfl
  have key : liftSpaceTilde G b' = (liftSpaceTilde G b).map (E : (α ⊕ α × Fin 4 → K) →ₗ[K] _) := by
    ext y
    rw [Submodule.mem_map_equiv]
    simp only [liftSpaceTilde, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
      Set.mem_ofPred_eq]
    refine forall₂_congr fun v hv => forall₂_congr fun w hw => ?_
    have hwV := Graph.closedNbhd_subset_vertexSet hv hw
    have hs : ∀ x, E.symm y x = (scale x)⁻¹ * y x := fun x => by
      rw [eq_inv_mul_iff_mul_eq₀ (hscale x), ← hE, LinearEquiv.apply_symm_apply]
    simp only [hs, scale, Sum.elim_inl, Sum.elim_inr, ite_eq_left hwV, inv_one, one_mul, hb' w hwV,
      Pi.smul_apply, smul_eq_mul]
    rw [inv_mul_eq_iff_eq_mul₀ (hc w hwV), Finset.mul_sum]
    refine Eq.congr_right (Finset.sum_congr rfl fun i _ => by ring)
  rw [key, LinearEquiv.finrank_map_eq]


theorem isZariskiOpen_eval_ne_zero {σ : Type*} (R : MvPolynomial σ K) :
    IsZariskiOpen {s : σ → K | MvPolynomial.eval s R ≠ 0} := fun _ hs => ⟨R, hs, fun _ h => h⟩

theorem isZariskiOpen_ne_zero_of_isPolyFun {σ : Type*} {f : (σ → K) → K} (hf : IsPolyFun f) :
    IsZariskiOpen {s | f s ≠ 0} := by
  obtain ⟨c, hc⟩ := hf
  intro s hs
  exact ⟨c, by rwa [← hc], fun s' hs' => by rwa [Set.mem_ofPred_eq, hc]⟩

/-- **A property that holds on a Zariski-open set of parameters meeting `U(G)` holds generally**
(the remark after `lem:pencil-d-steer`). -/
theorem HoldsGenerally.of_isZariskiOpen {G : Graph α β} {hubSel nbrSel : α → Fin 3 → Option α}
    {p : (α → Fin 4 → K) → (α → Submodule K (Fin 4 → K)) → Prop}
    {S : Set (α × Fin 7 × Fin 4 → K)} (hS : IsZariskiOpen S) {s₀ : α × Fin 7 × Fin 4 → K}
    (hs₀ : s₀ ∈ steerSet G hubSel nbrSel) (hs₀S : s₀ ∈ S)
    (h : ∀ s ∈ steerSet G hubSel nbrSel, s ∈ S →
      p (steerPoint hubSel s) (fun v => dotPerp (K ∙ steerNormal hubSel nbrSel G s v))) :
    HoldsGenerally G hubSel nbrSel p := by
  obtain ⟨R, hR0, hR⟩ := hS s₀ hs₀S
  exact ⟨R, ⟨s₀, hs₀, hR0⟩, fun s hs hRs => h s hs (hR s hRs)⟩

/-- **`dim L̃` takes its least value at a general nondegenerate realization**
(`lem:pencil-d-lift-one-witness`, a step of part (2)): some `N` bounds `dim L̃` below at every
nondegenerate realization in dimension three, and is attained generally. `N` is the least value on
`U(G)`, least among all nondegenerate realizations as each is `r(s)` up to scalars
(`exists_mem_steerSet_of_isNondeg`, `finrank_liftSpaceTilde_smul`); `dim L̃` is at most `N` off
the zero set of the polynomial of the section at a point where it is least
(`Matrix.exists_mvPolynomial_section_mulVec_eq_zero` at `z₀ = 0`). -/
theorem exists_holdsGenerally_finrank_liftSpaceTilde_le [Finite α] {G : Graph α β}
    {hubSel nbrSel : α → Fin 3 → Option α}
    (hHubSel : ∀ v, IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v))
    (hNbrSel : ∀ v, ¬ G.PencilHub v → IsFin3SelectorOf (G.closedNbhd v) (nbrSel v))
    (hfeas : PencilNondegFeasible K G) :
    ∃ N : ℕ, (∀ (F' : BodyHingeFramework K 2 α β) (b' : α → Fin 4 → K)
      (P' : α → Submodule K (Fin 4 → K)), IsNondegPencilPlaneRealization G F' b' P' →
        N ≤ Module.finrank K (liftSpaceTilde G b')) ∧
      HoldsGenerally (K := K) G hubSel nbrSel fun b0 _ =>
        Module.finrank K (liftSpaceTilde G b0) ≤ N := by
  classical
  have := Fintype.ofFinite α
  obtain ⟨s₀, hs₀⟩ := (steerSet_nonempty_iff (K := K) hHubSel hNbrSel).2 hfeas
  set S : Set ℕ := {n | ∃ s ∈ steerSet (K := K) G hubSel nbrSel,
    Module.finrank K (liftSpaceTilde G (steerPoint hubSel s)) = n} with hS
  have hSne : S.Nonempty := ⟨_, s₀, hs₀, rfl⟩
  obtain ⟨s₁, hs₁, hs₁min⟩ := Nat.sInf_mem hSne
  refine ⟨sInf S, fun F' b' P' hnd' => ?_, ?_⟩
  · obtain ⟨s, hs, hpt, -⟩ := exists_mem_steerSet_of_isNondeg hHubSel hNbrSel hnd'
    choose! c hc hceq using hpt
    rw [← finrank_liftSpaceTilde_smul hc hceq]
    exact Nat.sInf_le ⟨s, hs, rfl⟩
  set q₁ : α × Fin 4 → K := fun p => steerPoint hubSel s₁ p.1 p.2
  obtain ⟨D, -, hD₀, -, hDle, -⟩ := Matrix.exists_mvPolynomial_section_mulVec_eq_zero
    (liftMatrixPoly (K := K) G) (q₀ := q₁) (z₀ := 0) (by simp)
  obtain ⟨R₂, hR₂⟩ := IsPolyFun.comp D (f := fun (s : α × Fin 7 × Fin 4 → K) p =>
    steerPoint hubSel s p.1 p.2) fun p => isPolyFun_steerPoint hubSel p.1 p.2
  refine ⟨R₂, ⟨s₁, hs₁, by rw [← hR₂]; exact hD₀⟩, fun s _ hsR => ?_⟩
  have hle := hDle (fun p => steerPoint hubSel s p.1 p.2) (by rw [← hR₂] at hsR; exact hsR)
  rw [← liftSpaceTilde_eq_ker, ← liftSpaceTilde_eq_ker] at hle
  rw [← hs₁min]
  exact hle

/-- **One lift suffices, at a general realization** (`lem:pencil-d-lift-one-witness`, part (2)):
if a general nondegenerate realization in dimension three has a lift of rank `tgt_d(G)`, the
general lift attains. `dim L̃` takes its least value generally
(`exists_holdsGenerally_finrank_liftSpaceTilde_le`), and two nonempty Zariski-open subsets of
`U(G)` meet. -/
theorem liftAttains_of_holdsGenerally [Infinite K] [Finite α] [Finite β] {r : ℕ} {G : Graph α β}
    {hubSel nbrSel : α → Fin 3 → Option α}
    (hHubSel : ∀ v, IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v))
    (hNbrSel : ∀ v, ¬ G.PencilHub v → IsFin3SelectorOf (G.closedNbhd v) (nbrSel v))
    {ends : β → α × α} (hlinks : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2)
    (h : HoldsGenerally G hubSel nbrSel fun b0 P0 =>
      ∃ lam : Fin r → (α → K) × ((v : α) → Module.Dual K (P0 v)),
        (∀ i, lam i ∈ liftSpace G b0 P0) ∧
        (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := r + 1 + 1) G ends
          (fun p => liftNormal b0 (fun i => (lam i).1) p.1 p.2)).toBodyHinge.rigidityRows) : ℤ)
          = screwDim (r + 1 + 1) * ((V(G).ncard : ℤ) - 1) - G.deficiency (r + 1 + 2)) :
    LiftAttains K r G := by
  obtain ⟨R₁, ⟨s₀, hs₀, hR₁s₀⟩, hR₁⟩ := h
  obtain ⟨N, hN, R₂, ⟨s₂, hs₂, hR₂s₂⟩, hR₂⟩ := exists_holdsGenerally_finrank_liftSpaceTilde_le
    hHubSel hNbrSel ((steerSet_nonempty_iff (K := K) hHubSel hNbrSel).1 ⟨s₀, hs₀⟩)
  obtain ⟨s, ⟨hsU, hsR₁⟩, hsR₂⟩ := IsZariskiOpen.exists_mem_inter
    ((isZariskiOpen_steerSet hHubSel hNbrSel).inter (isZariskiOpen_eval_ne_zero R₁))
    (isZariskiOpen_eval_ne_zero R₂) ⟨hs₀, hR₁s₀⟩ (show s₂ ∈ {s | MvPolynomial.eval s R₂ ≠ 0} from
      hR₂s₂)
  obtain ⟨lam, hlam, hrank⟩ := hR₁ s hsU hsR₁
  have hle := hR₂ s hsU hsR₂
  obtain ⟨-, F, hnd⟩ := hsU
  exact liftAttains_of_least hnd (fun F' b' P' hnd' => hle.trans (hN F' b' P' hnd')) hlam hlinks
    hrank

/-! ## Lifts restrict to a subgraph -/

theorem eval_congr_vars {σ : Type*} {φ : MvPolynomial σ K} {x y : σ → K}
    (h : ∀ p ∈ φ.vars, x p = y p) : MvPolynomial.eval x φ = MvPolynomial.eval y φ :=
  MvPolynomial.hom_congr_vars (f₁ := MvPolynomial.eval x) (f₂ := MvPolynomial.eval y)
    (by ext; simp) (fun i hi _ => by simp [h i hi]) rfl

/-- **A polynomial homogeneous in each block scales by a monomial** (the homogeneity used after
`lem:pencil-d-steer` and in `lem:pencil-d-lift-transfer`): for the blocks `g : σ → ι` and `φ`
weighted homogeneous of degree `d` for `p ↦ single (g p) 1`, `φ(c·x) = c^d φ(x)`. -/
theorem eval_smul_of_isWeightedHomogeneous {σ ι : Type*} (g : σ → ι) {φ : MvPolynomial σ K}
    {d : ι →₀ ℕ} (hφ : MvPolynomial.IsWeightedHomogeneous (fun p => Finsupp.single (g p) 1) φ d)
    (x : σ → K) (c : ι → K) :
    MvPolynomial.eval (fun p => c (g p) * x p) φ =
      MvPolynomial.eval c (MvPolynomial.monomial d 1) * MvPolynomial.eval x φ := by
  classical
  conv_lhs => rw [φ.as_sum]
  conv_rhs => rw [φ.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hw := hφ (MvPolynomial.mem_support_iff.1 hμ)
  simp only [MvPolynomial.eval_monomial, one_mul, mul_pow]
  rw [Finsupp.prod_mul, ← hw, Finsupp.weight_apply, Finsupp.prod_sum_index (fun _ => pow_zero _)
    (fun _ _ _ => pow_add _ _ _)]
  have : (μ.prod fun p e => c (g p) ^ e) = μ.prod fun p e =>
      ((e • Finsupp.single (g p) 1 : ι →₀ ℕ).prod fun i k => c i ^ k) := by
    refine Finsupp.prod_congr fun p _ => ?_
    rw [Finsupp.smul_single, smul_eq_mul, mul_one,
      Finsupp.prod_single_index (h := fun i k => c i ^ k) (pow_zero (c (g p)))]
  rw [this]; ring

/-- The rank does not depend on the selector of the links. -/
theorem finrank_ofNormals_ends {k : ℕ} {G : Graph α β} {ends ends' : β → α × α}
    (h : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2)
    (h' : ∀ e u v, G.IsLink e u v → G.IsLink e (ends' e).1 (ends' e).2)
    (q : α × Fin (k + 2) → K) :
    Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := k) G ends
        q).toBodyHinge.rigidityRows) =
      Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := k) G ends'
        q).toBodyHinge.rigidityRows) := by
  set F₁ := (PanelHingeFramework.ofNormals (k := k) G ends q).toBodyHinge
  set F₂ := (PanelHingeFramework.ofNormals (k := k) G ends' q).toBodyHinge
  have hr : PanelHingeFramework.RecordsLinks G ends :=
    (PanelHingeFramework.recordsLinks_iff_forall_isLink).2 h
  have hr' : PanelHingeFramework.RecordsLinks G ends' :=
    (PanelHingeFramework.recordsLinks_iff_forall_isLink).2 h'
  have hprop : ∀ e u v, F₁.graph.IsLink e u v →
      ∃ c' : K, c' ≠ 0 ∧ c' • F₁.supportExtensor e = F₂.supportExtensor e := by
    intro e u v he
    change ∃ c' : K, c' ≠ 0 ∧ c' • panelSupportExtensor (fun i => q ((ends e).1, i))
      (fun i => q ((ends e).2, i)) = panelSupportExtensor (fun i => q ((ends' e).1, i))
      (fun i => q ((ends' e).2, i))
    rcases hr.eq_or_swap he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases hr'.eq_or_swap he with ⟨h1', h2'⟩ | ⟨h1', h2'⟩ <;>
      simp only [h1, h2, h1', h2']
    · exact ⟨1, one_ne_zero, one_smul _ _⟩
    · exact ⟨-1, neg_ne_zero.2 one_ne_zero, by
        rw [neg_one_smul, panelSupportExtensor_swap, neg_neg]⟩
    · exact ⟨-1, neg_ne_zero.2 one_ne_zero, by
        rw [neg_one_smul, panelSupportExtensor_swap, neg_neg]⟩
    · exact ⟨1, one_ne_zero, one_smul _ _⟩
  rw [span_rigidityRows_eq_of_supportExtensor_proportional F₁ F₂ rfl hprop]

/-- **A nondegenerate realization in dimension three from its conditions**, for normals `b` and
vectors `n` with `b_w · n_v = 0` on every closed neighbourhood (the step of
`lem:pencil-d-steer` that makes `U(G)` open, for any graph). -/
theorem exists_isNondeg_dotPerp_iff {G : Graph α β} {b n : α → Fin 4 → K}
    (horth : ∀ v ∈ V(G), ∀ w ∈ G.closedNbhd v, b w ⬝ᵥ n v = 0) :
    (∃ F : BodyHingeFramework K 2 α β,
      IsNondegPencilPlaneRealization G F b (fun v => dotPerp (K ∙ n v))) ↔
      (∀ v ∈ V(G), b v ≠ 0) ∧ (∀ v ∈ V(G), n v ≠ 0) ∧
      (∀ u v, G.Adj u v → LinearIndependent K ![b u, b v]) ∧
      (∀ v ∈ V(G), LinearIndepOn K n (G.closedHubNbhd v)) ∧
      (∀ v ∈ V(G), ¬ G.PencilHub v → LinearIndepOn K b (G.closedNbhd v)) := by
  constructor
  · rintro ⟨F, hreal, hcond⟩
    have hn : ∀ v ∈ V(G), n v ≠ 0 := fun v hv h0 => by
      have := hreal.2.1 v hv
      simp only [finrank_dotPerp] at this
      rw [h0, Submodule.span_singleton_eq_bot.2 rfl, finrank_bot] at this
      simp at this
    obtain ⟨h1, h2, h3⟩ := (pencilNondegConditions_dotPerp_iff hn).1 hcond
    exact ⟨hreal.1.2.1, hn, fun u v ⟨e, he⟩ => h1 e u v he, h2, h3⟩
  · rintro ⟨hb, hn, h1, h2, h3⟩
    obtain ⟨F, hF⟩ := exists_hasPencilPlaneRealization (k := 2) (G := G) (β := β) (b := b)
      (plane := fun v => dotPerp (K ∙ n v)) hb (fun e u v he => h1 u v ⟨e, he⟩)
      (fun v hv => finrank_dotPerp_span_singleton_of_ne_zero (hn v hv))
      (fun v hv w hw => mem_dotPerp_span_singleton.2 (horth v hv w hw))
    exact ⟨F, hF, (pencilNondegConditions_dotPerp_iff hn).2
      ⟨fun e u v he => h1 u v ⟨e, he⟩, h2, h3⟩⟩

/-- The conditions of `exists_isNondeg_dotPerp_iff` at polynomial families are open. -/
theorem isZariskiOpen_nondegConditions [Finite α] {σ : Type*} (G : Graph α β)
    {b n : (σ → K) → α → Fin 4 → K} (hb : ∀ v i, IsPolyFun fun s => b s v i)
    (hn : ∀ v i, IsPolyFun fun s => n s v i) :
    IsZariskiOpen {s | (∀ v ∈ V(G), b s v ≠ 0) ∧ (∀ v ∈ V(G), n s v ≠ 0) ∧
      (∀ u v, G.Adj u v → LinearIndependent K ![b s u, b s v]) ∧
      (∀ v ∈ V(G), LinearIndepOn K (n s) (G.closedHubNbhd v)) ∧
      (∀ v ∈ V(G), ¬ G.PencilHub v → LinearIndepOn K (b s) (G.closedNbhd v))} := by
  refine IsZariskiOpen.and ?_ (IsZariskiOpen.and ?_ (IsZariskiOpen.and ?_
    (IsZariskiOpen.and ?_ ?_)))
  · exact isZariskiOpen_forall fun v => isZariskiOpen_imp _ <|
      isZariskiOpen_ne_zero (K := K) _ (hb v)
  · exact isZariskiOpen_forall fun v => isZariskiOpen_imp _ <|
      isZariskiOpen_ne_zero (K := K) _ (hn v)
  · refine isZariskiOpen_forall fun u => isZariskiOpen_forall fun v => isZariskiOpen_imp _ ?_
    refine isZariskiOpen_linearIndependent_univ (fun s => ![b s u, b s v]) fun i j => ?_
    fin_cases i
    exacts [hb u j, hb v j]
  · exact isZariskiOpen_forall fun v => isZariskiOpen_imp _ <|
      isZariskiOpen_linearIndependent _ (fun i j => hn i j) _
  · exact isZariskiOpen_forall fun v => isZariskiOpen_imp _ <| isZariskiOpen_imp _ <|
      isZariskiOpen_linearIndependent _ (fun i j => hb i j) _

/-- Two nonzero vectors with the same orthogonal are proportional. -/
theorem exists_smul_of_dotPerp_eq {N : ℕ} {x y : Fin N → K} (hx : x ≠ 0)
    (h : dotPerp (K ∙ x) = dotPerp (K ∙ y)) : ∃ d : K, d ≠ 0 ∧ x = d • y := by
  have h' := congrArg dotPerp h
  rw [dotPerp_dotPerp, dotPerp_dotPerp] at h'
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.1 (h' ▸ Submodule.mem_span_singleton_self x)
  refine ⟨d, fun h0 => hx (by rw [← hd, h0, zero_smul]), hd.symm⟩

/-- The pair `(b, n)` as a point of the coordinates of `E` in `lem:pencil-d-lift-transfer`. -/
def bnPoint (b n : α → Fin 4 → K) : α × Fin 2 × Fin 4 → K := fun p => ![b p.1, n p.1] p.2.1 p.2.2

/-- Scaling by scalars nonzero everywhere keeps a polynomial homogeneous in each block nonzero. -/
theorem eval_smul_ne_zero_of_isWeightedHomogeneous {σ ι : Type*} (g : σ → ι)
    {φ : MvPolynomial σ K} {d : ι →₀ ℕ}
    (hφ : MvPolynomial.IsWeightedHomogeneous (fun p => Finsupp.single (g p) 1) φ d)
    {x : σ → K} (hx : MvPolynomial.eval x φ ≠ 0) {c : ι → K} (hc : ∀ i, c i ≠ 0) :
    MvPolynomial.eval (fun p => c (g p) * x p) φ ≠ 0 := by
  rw [eval_smul_of_isWeightedHomogeneous g hφ, MvPolynomial.eval_monomial, one_mul]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hc i)) hx

/-- The chart's orthogonality on a subgraph's closed neighbourhoods. -/
theorem steerPoint_dotProduct_steerNormal_of_le {G H : Graph α β} (hHG : H ≤ G)
    {hubSel nbrSel : α → Fin 3 → Option α}
    (hHubSel : ∀ v, IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v))
    (hNbrSel : ∀ v, ¬ G.PencilHub v → IsFin3SelectorOf (G.closedNbhd v) (nbrSel v))
    (s : α × Fin 7 × Fin 4 → K) {v w : α} (hw : w ∈ H.closedNbhd v) :
    steerPoint hubSel s w ⬝ᵥ steerNormal hubSel nbrSel G s v = 0 := by
  refine steerPoint_dotProduct_steerNormal hHubSel hNbrSel s ?_
  rcases hw with rfl | ⟨e, he⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨e, he.of_le hHG⟩

/-- Selectors of the closed hub-neighbourhoods and closed neighbourhoods of a feasible graph (the
fixed order of `lem:pencil-d-steer`). -/
theorem exists_steer_selectors [Finite α] [Finite β] {G : Graph α β}
    (hfeas : PencilNondegFeasible K G) :
    ∃ hubSel nbrSel : α → Fin 3 → Option α,
      (∀ v, IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v)) ∧
      (∀ v, ¬ G.PencilHub v → IsFin3SelectorOf (G.closedNbhd v) (nbrSel v)) := by
  obtain ⟨F, normal, point, h⟩ := hfeas
  obtain ⟨_seed, hubSel, nbrSel, hWF, -⟩ := exists_pencilSeed_of_nondeg h
  exact ⟨hubSel, nbrSel, hWF.1, hWF.2.1⟩

/-- **Lifts restrict to a subgraph** (`lem:pencil-d-lift-transfer`): for `H = G[V']`, under (T1)
and (T2), if the general lift of `H` attains, then at a general nondegenerate realization `r⁰` of
`G` in dimension three, `r⁰|_H` is a nondegenerate realization of `H`, and the `λ ∈ 𝓛(r⁰)^m` at
which the panel-hinge framework on `H` with the normals of the lift by `λ` has rank `tgt_d(H)` form
a nonempty Zariski-open subset of `𝓛(r⁰)^m` (open in the coordinates of the maps `ζ^i`, on which
the lift's normals depend). -/
theorem lift_transfer [Infinite K] [Finite α] [Finite β] {r : ℕ} {G : Graph α β} {V' : Set α}
    (hV'G : V' ⊆ V(G)) (hV' : V'.Nonempty) {hubSel nbrSel : α → Fin 3 → Option α}
    (hHubSel : ∀ v, IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v))
    (hNbrSel : ∀ v, ¬ G.PencilHub v → IsFin3SelectorOf (G.closedNbhd v) (nbrSel v))
    {ends : β → α × α}
    (hlinksH : ∀ e u v, (G.induce V').IsLink e u v →
      (G.induce V').IsLink e (ends e).1 (ends e).2)
    (hT1 : ∃ E : MvPolynomial (α × Fin 2 × Fin 4) K, (∀ p ∈ E.vars, p.1 ∈ V') ∧
      (∃ d : α × Fin 2 →₀ ℕ, MvPolynomial.IsWeightedHomogeneous
        (fun p : α × Fin 2 × Fin 4 => Finsupp.single (p.1, p.2.1) 1) E d) ∧
      (∃ (F : BodyHingeFramework K 2 α β) (b n : α → Fin 4 → K),
        IsNondegPencilPlaneRealization (G.induce V') F b (fun v => dotPerp (K ∙ n v)) ∧
        MvPolynomial.eval (bnPoint b n) E ≠ 0) ∧
      ∀ (F : BodyHingeFramework K 2 α β) (b n : α → Fin 4 → K),
        IsNondegPencilPlaneRealization (G.induce V') F b (fun v => dotPerp (K ∙ n v)) →
        MvPolynomial.eval (bnPoint b n) E ≠ 0 →
        ∃ (F' : BodyHingeFramework K 2 α β) (b' : α → Fin 4 → K)
          (P' : α → Submodule K (Fin 4 → K)), IsNondegPencilPlaneRealization G F' b' P' ∧
          (∀ v ∈ V', b' v = b v) ∧ ∀ v ∈ V', 2 ≤ (G.induce V').degree v →
            P' v = dotPerp (K ∙ n v))
    (hT2 : HoldsGenerally (K := K) G hubSel nbrSel fun b0 P0 =>
      ∀ ζ ∈ liftMaps (G.induce V') b0 P0, ∃ ζ' ∈ liftMaps G b0 P0, ∀ v ∈ V', ζ' v = ζ v)
    (hH : LiftAttains K r (G.induce V')) :
    HoldsGenerally (K := K) G hubSel nbrSel fun b0 P0 =>
      (∃ F : BodyHingeFramework K 2 α β, IsNondegPencilPlaneRealization (G.induce V') F b0 P0) ∧
      (∃ lam : Fin r → (α → K) × ((v : α) → Module.Dual K (P0 v)),
        (∀ i, lam i ∈ liftSpace G b0 P0) ∧
        (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := r + 1 + 1)
          (G.induce V') ends
            (fun p => liftNormal b0 (fun i => (lam i).1) p.1 p.2)).toBodyHinge.rigidityRows) : ℤ)
          = screwDim (r + 1 + 1) * ((V(G.induce V').ncard : ℤ) - 1) -
            (G.induce V').deficiency (r + 1 + 2)) ∧
      ∀ lam : Fin r → (α → K) × ((v : α) → Module.Dual K (P0 v)),
        (∀ i, lam i ∈ liftSpace G b0 P0) →
        (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := r + 1 + 1)
          (G.induce V') ends
            (fun p => liftNormal b0 (fun i => (lam i).1) p.1 p.2)).toBodyHinge.rigidityRows) : ℤ)
          = screwDim (r + 1 + 1) * ((V(G.induce V').ncard : ℤ) - 1) -
            (G.induce V').deficiency (r + 1 + 2) →
        ∃ R : MvPolynomial (Fin r × α) K, MvPolynomial.eval (fun p => (lam p.1).1 p.2) R ≠ 0 ∧
          ∀ lam' : Fin r → (α → K) × ((v : α) → Module.Dual K (P0 v)),
            (∀ i, lam' i ∈ liftSpace G b0 P0) →
            MvPolynomial.eval (fun p => (lam' p.1).1 p.2) R ≠ 0 →
            (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := r + 1 + 1)
              (G.induce V') ends
                (fun p => liftNormal b0 (fun i => (lam' i).1) p.1 p.2)).toBodyHinge.rigidityRows)
            : ℤ)
              = screwDim (r + 1 + 1) * ((V(G.induce V').ncard : ℤ) - 1) -
                (G.induce V').deficiency (r + 1 + 2) := by
  classical
  set H := G.induce V' with hHdef
  have hVH : V(H) = V' := rfl
  have hHG : H ≤ G := Graph.induce_le hV'G
  obtain ⟨endsH, hlinksH', QH, hQvars, ⟨dQ, hQhom⟩, ⟨FQ, bQ, PQ, hndQ, hQ0⟩, hQmain⟩ := hH
  obtain ⟨E, hEvars, ⟨dE, hEhom⟩, ⟨FE, bE, nE, hndE, hE0⟩, hEmain⟩ := hT1
  -- the chart of `H`
  obtain ⟨hubSelH, nbrSelH, hHubSelH, hNbrSelH⟩ :=
    exists_steer_selectors ((gradedPencilNondegFeasible_two_iff H).1 ⟨FE, bE, _, hndE⟩)
  -- a nondegenerate realization of `H` in the chart, up to scalars nonzero everywhere
  have hscale : ∀ (F : BodyHingeFramework K 2 α β) (b : α → Fin 4 → K)
      (P : α → Submodule K (Fin 4 → K)), IsNondegPencilPlaneRealization H F b P →
      ∃ s ∈ steerSet (K := K) H hubSelH nbrSelH, ∃ c : α → K, (∀ v, c v ≠ 0) ∧
        (∀ v ∈ V', steerPoint hubSelH s v = c v • b v) ∧
        ∀ v ∈ V', dotPerp (K ∙ steerNormal hubSelH nbrSelH H s v) = P v := by
    intro F b P hnd
    obtain ⟨s, hs, hpt, hpl⟩ := exists_mem_steerSet_of_isNondeg hHubSelH hNbrSelH hnd
    choose! c hc hceq using hpt
    refine ⟨s, hs, fun v => if v ∈ V' then c v else 1, fun v => ?_, fun v hv => ?_, hpl⟩
    · by_cases hv : v ∈ V'
      · simp only [ite_eq_left hv]; exact hc v hv
      · simp [hv]
    · simp only [ite_eq_left hv]; exact hceq v hv
  -- the polynomials of `E` and `Q_H` on `Γ(H)`
  obtain ⟨PE, hPE⟩ := IsPolyFun.comp E (f := fun s : α × Fin 7 × Fin 4 → K =>
    bnPoint (steerPoint hubSelH s) (steerNormal hubSelH nbrSelH H s)) fun p => by
      obtain ⟨v, j, i⟩ := p
      fin_cases j
      · simpa [bnPoint] using isPolyFun_steerPoint (K := K) hubSelH v i
      · simpa [bnPoint] using isPolyFun_steerNormal (K := K) hubSelH nbrSelH H v i
  obtain ⟨PQ', hPQ'⟩ := IsPolyFun.comp QH (f := fun (s : α × Fin 7 × Fin 4 → K)
    (p : α × Fin 4) => steerPoint hubSelH s p.1 p.2) fun p => isPolyFun_steerPoint hubSelH p.1 p.2
  obtain ⟨sE, hsE, cE, hcE, hptE, hplE⟩ := hscale FE bE _ hndE
  have hnE : ∀ v ∈ V', ∃ d : K, d ≠ 0 ∧ steerNormal hubSelH nbrSelH H sE v = d • nE v :=
    fun v hv => exists_smul_of_dotPerp_eq (hsE.1 v hv).2 (hplE v hv)
  choose! dE' hdE' hdEeq using hnE
  have hPEsE : MvPolynomial.eval sE PE ≠ 0 := by
    rw [← hPE]
    dsimp only
    let cc : α × Fin 2 → K := fun q => ![cE q.1, if q.1 ∈ V' then dE' q.1 else 1] q.2
    have hcc : ∀ q, cc q ≠ 0 := fun ⟨v, j⟩ => by
      fin_cases j
      · exact hcE v
      · by_cases hv : v ∈ V' <;> simp [cc, hv, hdE' v]
    have h := eval_smul_ne_zero_of_isWeightedHomogeneous (fun p : α × Fin 2 × Fin 4 => (p.1, p.2.1))
      hEhom hE0 hcc
    have e : MvPolynomial.eval (bnPoint (steerPoint hubSelH sE)
        (steerNormal hubSelH nbrSelH H sE)) E =
        MvPolynomial.eval (fun p => cc (p.1, p.2.1) * bnPoint bE nE p) E := by
      refine eval_congr_vars fun p hp => ?_
      obtain ⟨v, j, i⟩ := p
      have hv : v ∈ V' := hEvars _ hp
      fin_cases j
      · simp [bnPoint, cc, hptE v hv]
      · simp [bnPoint, cc, hv, hdEeq v hv]
    rw [e]; exact h
  obtain ⟨sQ, hsQ, cQ, hcQ, hptQ, -⟩ := hscale FQ bQ PQ hndQ
  have hPQsQ : MvPolynomial.eval sQ PQ' ≠ 0 := by
    rw [← hPQ']
    dsimp only
    have h := eval_smul_ne_zero_of_isWeightedHomogeneous (Prod.fst : α × Fin 4 → α) hQhom hQ0 hcQ
    have e : MvPolynomial.eval (fun p : α × Fin 4 => steerPoint hubSelH sQ p.1 p.2) QH =
        MvPolynomial.eval (fun p : α × Fin 4 => cQ p.1 * bQ p.1 p.2) QH :=
      eval_congr_vars fun p hp => by simp [hptQ p.1 (hQvars p hp)]
    rw [e]; exact h
  -- a realization `r_H` of `H` with `E ≠ 0` and `Q_H ≠ 0`
  obtain ⟨sH, ⟨hsHU, hsHE⟩, hsHQ⟩ := IsZariskiOpen.exists_mem_inter
    ((isZariskiOpen_steerSet hHubSelH hNbrSelH).inter (isZariskiOpen_eval_ne_zero PE))
    (isZariskiOpen_eval_ne_zero PQ') ⟨hsE, hPEsE⟩ hPQsQ
  set bH := steerPoint hubSelH sH
  set nH := steerNormal hubSelH nbrSelH H sH
  obtain ⟨-, FH, hndH⟩ := hsHU
  have hcondH := (exists_isNondeg_dotPerp_iff (G := H) (b := bH) (n := nH)
    fun v _ w hw => steerPoint_dotProduct_steerNormal hHubSelH hNbrSelH sH hw).1 ⟨FH, hndH⟩
  have hEH : MvPolynomial.eval (bnPoint bH nH) E ≠ 0 := (hPE sH).trans_ne hsHE
  have hQH : MvPolynomial.eval (fun p : α × Fin 4 => bH p.1 p.2) QH ≠ 0 :=
    (hPQ' sH).trans_ne hsHQ
  -- (T1): a realization of `G` through `r_H`, and in the chart of `G`
  obtain ⟨F', b', P', hnd', hb', hP'⟩ := hEmain FH bH nH hndH hEH
  obtain ⟨s₁, hs₁, hpt₁, hpl₁⟩ := exists_mem_steerSet_of_isNondeg hHubSel hNbrSel hnd'
  have hs₁c := (mem_steerSet_iff hHubSel hNbrSel).1 hs₁
  choose! c₁ hc₁ hc₁eq using hpt₁
  let bG : (α × Fin 7 × Fin 4 → K) → α → Fin 4 → K := fun s => steerPoint hubSel s
  let nG : (α × Fin 7 × Fin 4 → K) → α → Fin 4 → K := fun s => steerNormal hubSel nbrSel G s
  have hcond₁ : (∀ v ∈ V(H), bG s₁ v ≠ 0) ∧ (∀ v ∈ V(H), nG s₁ v ≠ 0) ∧
      (∀ u v, H.Adj u v → LinearIndependent K ![bG s₁ u, bG s₁ v]) ∧
      (∀ v ∈ V(H), LinearIndepOn K (nG s₁) (H.closedHubNbhd v)) ∧
      (∀ v ∈ V(H), ¬ H.PencilHub v → LinearIndepOn K (bG s₁) (H.closedNbhd v)) := by
    refine ⟨fun v hv => hs₁c.1 v (hV'G hv), fun v hv => hs₁c.2.1 v (hV'G hv),
      fun u v ⟨e, he⟩ => hs₁c.2.2.1 u v ⟨e, he.of_le hHG⟩, fun v hv => ?_, fun v hv hhub => ?_⟩
    · refine LinearIndepOn.of_smul_eq (hcondH.2.2.2.1 v hv) fun w hw => ?_
      have hwV : w ∈ V' := hw.1.1
      have hdeg : 2 ≤ H.degree w := by have := hw.1.2; omega
      have heq : dotPerp (K ∙ nG s₁ w) = dotPerp (K ∙ nH w) := by
        rw [hpl₁ w (hV'G hwV), hP' w hwV hdeg]
      exact exists_smul_of_dotPerp_eq (hs₁c.2.1 w (hV'G hwV)) heq
    · refine LinearIndepOn.of_smul_eq (hcondH.2.2.2.2 v hv hhub) fun w hw => ?_
      have hwV : w ∈ V' := Graph.closedNbhd_subset_vertexSet hv hw
      exact ⟨c₁ w, hc₁ w (hV'G hwV), by
        change steerPoint hubSel s₁ w = _
        rw [hc₁eq w (hV'G hwV), hb' w hwV]⟩
  have hQ₁ : MvPolynomial.eval (fun p : α × Fin 4 => bG s₁ p.1 p.2) QH ≠ 0 := by
    have h := eval_smul_ne_zero_of_isWeightedHomogeneous (Prod.fst : α × Fin 4 → α) hQhom hQH
      (c := fun v => if v ∈ V' then c₁ v else 1) fun v => by
        by_cases hv : v ∈ V'
        · simp only [ite_eq_left hv]; exact hc₁ v (hV'G hv)
        · simp [hv]
    have e : MvPolynomial.eval (fun p : α × Fin 4 => bG s₁ p.1 p.2) QH =
        MvPolynomial.eval (fun p : α × Fin 4 => (if p.1 ∈ V' then c₁ p.1 else 1) * bH p.1 p.2) QH :=
      eval_congr_vars fun p hp => by
        have hv : p.1 ∈ V' := hQvars p hp
        simp only [ite_eq_left hv, bG, hc₁eq p.1 (hV'G hv), hb' p.1 hv, Pi.smul_apply, smul_eq_mul]
    rw [e]; exact h
  -- the polynomials on `Γ(G)`
  have hbG : ∀ v i, IsPolyFun fun s => bG s v i := fun v i => isPolyFun_steerPoint hubSel v i
  have hnG : ∀ v i, IsPolyFun fun s => nG s v i := fun v i =>
    isPolyFun_steerNormal hubSel nbrSel G v i
  obtain ⟨Rnd, hRnd₁, hRnd⟩ := isZariskiOpen_nondegConditions H hbG hnG s₁ hcond₁
  obtain ⟨RQ, hRQ⟩ := IsPolyFun.comp QH (f := fun (s : α × Fin 7 × Fin 4 → K) (p : α × Fin 4) =>
    bG s p.1 p.2) fun p => hbG p.1 p.2
  obtain ⟨RT, ⟨s₂, hs₂, hRT₂⟩, hRT⟩ := hT2
  refine ⟨Rnd * RQ * RT, ?_, fun s hsU hR => ?_⟩
  · have h₁ : MvPolynomial.eval s₁ (Rnd * RQ) ≠ 0 := by
      rw [map_mul, ← hRQ]; exact mul_ne_zero hRnd₁ hQ₁
    obtain ⟨s, hs1, hsU, hs2⟩ := IsZariskiOpen.exists_mem_inter
      (isZariskiOpen_eval_ne_zero (Rnd * RQ))
      ((isZariskiOpen_steerSet hHubSel hNbrSel).inter (isZariskiOpen_eval_ne_zero RT)) h₁
      ⟨hs₂, hRT₂⟩
    exact ⟨s, hsU, by rw [map_mul]; exact mul_ne_zero hs1 hs2⟩
  rw [map_mul, map_mul] at hR
  have hnd_s := hRnd s (left_ne_zero_of_mul (left_ne_zero_of_mul hR))
  have hQs : MvPolynomial.eval (fun p : α × Fin 4 => bG s p.1 p.2) QH ≠ 0 :=
    (hRQ s).trans_ne (right_ne_zero_of_mul (left_ne_zero_of_mul hR))
  have hT2s := hRT s hsU (right_ne_zero_of_mul hR)
  obtain ⟨FHs, hndHs⟩ := (exists_isNondeg_dotPerp_iff (G := H) (b := bG s) (n := nG s)
    fun v _ w hw => steerPoint_dotProduct_steerNormal_of_le hHG hHubSel hNbrSel s hw).2 hnd_s
  have hlinkH : ∀ e u v, H.IsLink e u v → LinearIndependent K ![bG s u, bG s v] :=
    fun e u v he => hnd_s.2.2.1 u v ⟨e, he⟩
  refine ⟨⟨FHs, hndHs⟩, ?_, fun lam hlam hrk => ?_⟩
  · -- nonempty: a lift of `r⁰|_H` of rank `tgt_d(H)`, through (T2)
    obtain ⟨lamH, hlamH, hrkH⟩ := hQmain FHs (bG s) _ hndHs hQs
    choose ζG hζG hζGeq using fun i => hT2s _ ⟨lamH i, hlamH i, rfl⟩
    choose lamG hlamG hlamGeq using fun i => Submodule.mem_map.1 (hζG i)
    refine ⟨lamG, hlamG, ?_⟩
    rw [← hrkH, finrank_ofNormals_ends hlinksH hlinksH']
    congr 1
    refine finrank_ofNormals_congr hlinksH' fun v hv => ?_
    simp only [liftNormal]
    congr 1
    funext i
    exact (congrFun (hlamGeq i) v).trans (hζGeq i v hv)
  · -- open: the rank polynomial in the coordinates of the maps
    have hnrm_poly : ∀ p : α × Fin (r + 1 + 1 + 2), IsPolyFun fun ζc : Fin r × α → K =>
        liftVec (bG s p.1) (fun i => ζc (i, p.1)) p.2 := fun p =>
      isPolyFun_liftVec (p := fun _ => bG s p.1) (u := fun ζc i => ζc (i, p.1))
        (fun j => isPolyFun_const _) (fun i => isPolyFun_apply (i, p.1)) p.2
    have hrecH : PanelHingeFramework.RecordsLinks H ends :=
      (PanelHingeFramework.recordsLinks_iff_forall_isLink).2 hlinksH
    have hne₀ : ∀ e, H.IsLink e (ends e).1 (ends e).2 →
        (PanelHingeFramework.ofNormals (k := r + 1 + 1) H ends
          (fun p => liftNormal (bG s) (fun i => (lam i).1) p.1 p.2)
          hrecH).toBodyHinge.supportExtensor e ≠ 0 := by
      intro e he
      rw [PanelHingeFramework.toBodyHinge_supportExtensor, panelSupportExtensor_ne_zero_iff]
      exact linearIndependent_liftNormal (fun i v => (lam i).1 v) (hlinkH e _ _ he)
    obtain ⟨Pr, hPr₀, hPr⟩ := PanelHingeFramework.exists_rankPolynomial_of_le_finrank_linking H
      ends hlinksH hne₀ le_rfl
    obtain ⟨R, hR⟩ := IsPolyFun.comp Pr hnrm_poly
    have hRe : ∀ lam' : Fin r → (α → K) × ((v : α) → Module.Dual K (dotPerp (K ∙ nG s v))),
        MvPolynomial.eval (fun p => (lam' p.1).1 p.2) R =
        MvPolynomial.eval (fun p => liftNormal (bG s) (fun i => (lam' i).1) p.1 p.2) Pr :=
      fun lam' => (hR _).symm
    refine ⟨R, by rw [hRe]; exact hPr₀, fun lam' _ hR' => ?_⟩
    refine le_antisymm (finrank_liftNormal_le hlinksH hlinkH (by rwa [hVH]) _) ?_
    rw [← hrk]
    rw [hRe] at hR'
    exact_mod_cast hPr _ hR'

end CombinatorialRigidity.Molecular
