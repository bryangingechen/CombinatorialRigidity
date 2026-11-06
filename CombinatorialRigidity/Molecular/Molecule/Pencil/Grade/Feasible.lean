/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Nondegenerate
public import CombinatorialRigidity.Molecular.Molecule.Pencil.Steer
public import CombinatorialRigidity.Mathlib.Algebra.MvPolynomial.Monad

/-!
# Nondegeneracy-feasibility in every dimension

`lem:pencil-d-nondegenerate-feasible` (`blueprint/src/chapter/pencil-d.tex`,
`sec:pencil-d-nondegenerate`): in grade `k ≥ 2` a multigraph on finitely many bodies is
nondegeneracy-feasible (`GradedPencilNondegFeasible`) exactly when its conditions are met by some
point configuration and subspaces (`gradedPencilNondegFeasible_iff`).

The module first sets up the *polynomial functions* of a coordinate vector (`IsPolyFun`) and the
*Zariski-open* sets they cut out (`IsZariskiOpen`) with their closure lemmas, and
`exists_hasPencilPlaneRealization`, which builds a pencil plane realization from a point
configuration meeting condition (1). The feasibility proof then finds, for each body and each set of
its hub-neighbourhood, a projection to three coordinates that is injective on the subspaces
(`exists_rowsMap_two`, `exists_rowsMap_three`), and combines them over a Zariski-open set of
projections.
-/

@[expose] public section

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

/-! ## Polynomial functions and Zariski-open sets -/

/-- A function of the coordinates `s : σ → K` that is a polynomial in them. -/
def IsPolyFun {σ : Type*} (f : (σ → K) → K) : Prop :=
  ∃ c : MvPolynomial σ K, ∀ s, f s = MvPolynomial.eval s c

theorem isPolyFun_const {σ : Type*} (a : K) : IsPolyFun (σ := σ) fun _ => a :=
  ⟨MvPolynomial.C a, fun s => by simp⟩

theorem isPolyFun_apply {σ : Type*} (i : σ) : IsPolyFun fun s : σ → K => s i :=
  ⟨MvPolynomial.X i, fun s => by simp⟩

theorem IsPolyFun.add {σ : Type*} {f g : (σ → K) → K} (hf : IsPolyFun f) (hg : IsPolyFun g) :
    IsPolyFun fun s => f s + g s := by
  obtain ⟨c, hc⟩ := hf; obtain ⟨d, hd⟩ := hg
  exact ⟨c + d, fun s => by simp [hc, hd]⟩

theorem IsPolyFun.mul {σ : Type*} {f g : (σ → K) → K} (hf : IsPolyFun f) (hg : IsPolyFun g) :
    IsPolyFun fun s => f s * g s := by
  obtain ⟨c, hc⟩ := hf; obtain ⟨d, hd⟩ := hg
  exact ⟨c * d, fun s => by simp [hc, hd]⟩

/-- **A polynomial of polynomial functions is a polynomial function** (`MvPolynomial.bind₁`). -/
theorem IsPolyFun.comp {σ τ : Type*} (P : MvPolynomial τ K) {f : (σ → K) → τ → K}
    (hf : ∀ t, IsPolyFun fun s => f s t) : IsPolyFun fun s => MvPolynomial.eval (f s) P := by
  choose c hc using hf
  refine ⟨MvPolynomial.bind₁ c P, fun s => ?_⟩
  rw [MvPolynomial.eval_bind₁, show (fun t => MvPolynomial.eval s (c t)) = f s from
    funext fun t => (hc t s).symm]

/-- `cross₃` of vectors with polynomial coordinates has polynomial coordinates. -/
theorem isPolyFun_cross₃ {σ : Type*} {x y z : (σ → K) → Fin 4 → K}
    (hx : ∀ i, IsPolyFun fun s => x s i) (hy : ∀ i, IsPolyFun fun s => y s i)
    (hz : ∀ i, IsPolyFun fun s => z s i) (i : Fin 4) :
    IsPolyFun fun s => cross₃ (x s) (y s) (z s) i := by
  choose X hX using hx
  choose Y hY using hy
  choose Z hZ using hz
  refine ⟨cross₃Poly X Y Z i, fun s => ?_⟩
  rw [cross₃Poly_eval, show (fun j => MvPolynomial.eval s (X j)) = x s from
      funext fun j => (hX j s).symm, show (fun j => MvPolynomial.eval s (Y j)) = y s from
      funext fun j => (hY j s).symm, show (fun j => MvPolynomial.eval s (Z j)) = z s from
      funext fun j => (hZ j s).symm]

/-- **A Zariski-open set of points** of `σ → K`: each of its points has a polynomial nonzero there
whose non-roots all lie in the set (`Graph.X0AttainsGrade`'s form of "a Zariski-open subset"). -/
def IsZariskiOpen {σ : Type*} (U : Set (σ → K)) : Prop :=
  ∀ s ∈ U, ∃ R : MvPolynomial σ K, MvPolynomial.eval s R ≠ 0 ∧
    ∀ s', MvPolynomial.eval s' R ≠ 0 → s' ∈ U

theorem isZariskiOpen_univ {σ : Type*} : IsZariskiOpen (Set.univ : Set (σ → K)) :=
  fun _ _ => ⟨1, by simp, fun _ _ => trivial⟩

theorem isZariskiOpen_forall {σ ι : Type*} [Finite ι] {p : ι → (σ → K) → Prop}
    (h : ∀ i, IsZariskiOpen {s | p i s}) : IsZariskiOpen {s | ∀ i, p i s} := by
  classical
  have := Fintype.ofFinite ι
  intro s hs
  choose R hR0 hR using fun i => h i s (hs i)
  refine ⟨∏ i, R i, ?_, fun s' hs' i => hR i s' ?_⟩
  · rw [map_prod]; exact Finset.prod_ne_zero_iff.2 fun i _ => hR0 i
  · rw [map_prod] at hs'
    exact fun h0 => hs' (Finset.prod_eq_zero (Finset.mem_univ i) h0)

theorem isZariskiOpen_imp {σ : Type*} (c : Prop) {p : (σ → K) → Prop}
    (h : IsZariskiOpen {s | p s}) : IsZariskiOpen {s | c → p s} := by
  by_cases hc : c
  · simpa [hc] using h
  · simpa [hc] using (isZariskiOpen_univ (K := K) (σ := σ))

theorem IsZariskiOpen.inter {σ : Type*} {U V : Set (σ → K)} (hU : IsZariskiOpen U)
    (hV : IsZariskiOpen V) : IsZariskiOpen (U ∩ V) := by
  have h := isZariskiOpen_forall (ι := Bool) (p := fun b s => s ∈ if b then U else V)
    (fun b => by cases b <;> simpa)
  convert h using 1
  ext s; simp [and_comm]

theorem IsZariskiOpen.and {σ : Type*} {p q : (σ → K) → Prop} (hp : IsZariskiOpen {s | p s})
    (hq : IsZariskiOpen {s | q s}) : IsZariskiOpen {s | p s ∧ q s} :=
  hp.inter hq

/-- **Independence of a family with polynomial coordinates is open**
(`exists_polynomial_ne_zero_of_linearIndependent_at_reindex`). -/
theorem isZariskiOpen_linearIndependent {σ ι : Type*} [Finite ι] {n : ℕ}
    (f : (σ → K) → ι → Fin n → K) (hf : ∀ i j, IsPolyFun fun s => f s i j) (t : Set ι) :
    IsZariskiOpen {s | LinearIndependent K fun i : t => f s i} := by
  choose c hc using hf
  intro s₀ hs₀
  obtain ⟨R, hR0, hR⟩ := exists_polynomial_ne_zero_of_linearIndependent_at_reindex
    (finCongr (Module.finrank_fin_fun K)) f c (LinearEquiv.refl K (Fin n → K))
    (fun s i j => hc i j s) hs₀
  exact ⟨R, hR0, hR⟩

theorem isZariskiOpen_ne_zero {σ : Type*} {n : ℕ} (f : (σ → K) → Fin n → K)
    (hf : ∀ j, IsPolyFun fun s => f s j) : IsZariskiOpen {s | f s ≠ 0} := by
  have h := isZariskiOpen_linearIndependent (ι := Unit) (fun s _ => f s) (fun _ j => hf j)
    Set.univ
  convert h using 1
  ext s
  simp only [Set.mem_ofPred_eq]
  have : Unique (Set.univ : Set Unit) := ⟨⟨⟨(), trivial⟩⟩, fun _ => Subtype.ext rfl⟩
  exact (linearIndependent_unique_iff (v := fun _ : (Set.univ : Set Unit) => f s)).symm

/-- **Two nonempty Zariski-open sets meet**, over an infinite field
(`lem:pencil-x0-fibre-intersection` in the ambient space). -/
theorem IsZariskiOpen.exists_mem_inter [Infinite K] {σ : Type*} {U V : Set (σ → K)}
    (hU : IsZariskiOpen U) (hV : IsZariskiOpen V) {s₁ s₂ : σ → K} (h₁ : s₁ ∈ U) (h₂ : s₂ ∈ V) :
    ∃ s, s ∈ U ∧ s ∈ V := by
  obtain ⟨R₁, hR₁0, hR₁⟩ := hU s₁ h₁
  obtain ⟨R₂, hR₂0, hR₂⟩ := hV s₂ h₂
  obtain ⟨s, hs⟩ := MvPolynomial.exists_eval_ne_zero_of_forall_ne_zero ![R₁, R₂] fun i => by
    fin_cases i
    · exact fun h => hR₁0 (by simp [show R₁ = 0 from h])
    · exact fun h => hR₂0 (by simp [show R₂ = 0 from h])
  exact ⟨s, hR₁ s (by simpa using hs 0), hR₂ s (by simpa using hs 1)⟩

/-! ## A pencil realization from its incidences -/

/-- **A pencil realization from normals and subspaces** (part (1) of
`lem:pencil-d-point-configuration`, with some framework): nonzero normals on `V(G)`, independent at
the ends of every link, and three-dimensional subspaces containing the normals of the closed
neighbourhoods give a pencil realization. On a nonempty `α` it is `toPatchedBodyHinge` at the
selector `G.endsOf`; on an empty `α`, a constant nonzero hinge. -/
theorem exists_hasPencilPlaneRealization {k : ℕ} [NeZero k] {G : Graph α β}
    {b : α → Fin (k + 2) → K} {plane : α → Submodule K (Fin (k + 2) → K)}
    (hne : ∀ v ∈ V(G), b v ≠ 0)
    (hind : ∀ e u v, G.IsLink e u v → LinearIndependent K ![b u, b v])
    (hdim : ∀ v ∈ V(G), Module.finrank K (plane v) = 3)
    (hmem : ∀ v ∈ V(G), ∀ w ∈ G.closedNbhd v, b w ∈ plane v) :
    ∃ F : BodyHingeFramework K k α β, HasPencilPlaneRealization G F b plane := by
  rcases isEmpty_or_nonempty α with hα | hα
  · refine ⟨⟨G, fun _ => panelSupportExtensor (Pi.single 0 1) (Pi.single 1 1)⟩,
      ⟨rfl, fun v => isEmptyElim v, fun e => ?_, fun e u => isEmptyElim u⟩,
      fun v => isEmptyElim v, fun v => isEmptyElim v, fun e u => isEmptyElim u⟩
    rw [panelSupportExtensor_ne_zero_iff]
    exact linearIndependent_single_zero_one
  · have : Inhabited α := Classical.inhabited_of_nonempty hα
    exact ⟨_, PanelHingeFramework.hasPencilPlaneRealization_toPatchedBodyHinge
      (PanelHingeFramework.ofNormals G G.endsOf fun p => b p.1 p.2) hne hind hdim hmem⟩

theorem isZariskiOpen_linearIndependent_univ {σ ι : Type*} [Finite ι] {n : ℕ}
    (f : (σ → K) → ι → Fin n → K) (hf : ∀ i j, IsPolyFun fun s => f s i j) :
    IsZariskiOpen {s | LinearIndependent K (f s)} := by
  convert isZariskiOpen_linearIndependent f hf Set.univ using 1
  ext s
  exact (linearIndepOn_univ_iff (R := K) (v := f s)).symm

/-- A vector off two subspaces of a third that lies in neither. -/
theorem exists_mem_notMem_two {V : Type*} [AddCommGroup V] [Module K V] {L A B : Submodule K V}
    (hA : ¬ L ≤ A) (hB : ¬ L ≤ B) : ∃ x ∈ L, x ∉ A ∧ x ∉ B := by
  obtain ⟨a, ha, haA⟩ := Set.not_subset.1 hA
  obtain ⟨c, hc, hcB⟩ := Set.not_subset.1 hB
  by_cases haB : a ∈ B
  · by_cases hcA : c ∈ A
    · refine ⟨a + c, L.add_mem ha hc, fun h => haA ?_, fun h => hcB ?_⟩
      · simpa using A.sub_mem h hcA
      · simpa using B.sub_mem h haB
    · exact ⟨c, hc, hcA, hcB⟩
  · exact ⟨a, ha, haA, haB⟩

theorem finrank_sup_span_singleton_of_notMem {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {L : Submodule K V} {x : V} (hx : x ∉ L) :
    Module.finrank K (L ⊔ K ∙ x : Submodule K V) = Module.finrank K L + 1 := by
  have hx0 : x ≠ 0 := fun h => hx (h ▸ L.zero_mem)
  have hinf : L ⊓ K ∙ x = ⊥ := by
    rw [eq_bot_iff]
    intro y ⟨hyL, hyx⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hyx
    by_cases hc : c = 0
    · simp [hc]
    · exact absurd (by simpa [hc] using L.smul_mem c⁻¹ hyL) hx
  have := Submodule.finrank_sup_add_finrank_inf_eq L (K ∙ x)
  rw [hinf, finrank_bot, finrank_span_singleton hx0] at this
  omega

/-- The linear map with the rows `r i`, `x ↦ (r i ⬝ᵥ x)_i`. -/
def rowsMap {N : ℕ} (r : Fin 4 → Fin N → K) : (Fin N → K) →ₗ[K] (Fin 4 → K) :=
  Matrix.mulVecLin (Matrix.of r)

theorem rowsMap_apply {N : ℕ} (r : Fin 4 → Fin N → K) (x : Fin N → K) (i : Fin 4) :
    rowsMap r x i = r i ⬝ᵥ x := rfl

/-- A row map is injective on `P` when the orthogonal of `P` and three of its rows span. -/
theorem injOn_rowsMap {N : ℕ} {r : Fin 4 → Fin N → K} {P : Submodule K (Fin N → K)}
    {i j l : Fin 4} (h : dotPerp P ⊔ K ∙ r i ⊔ K ∙ r j ⊔ K ∙ r l = ⊤) :
    Set.InjOn (rowsMap r) P := by
  rw [← LinearMap.disjoint_ker_iff_injOn, Submodule.disjoint_def]
  intro x hxP hx
  have hx' : ∀ t, r t ⬝ᵥ x = 0 := fun t => by
    have := congrFun (LinearMap.mem_ker.1 hx) t
    rwa [rowsMap_apply] at this
  have hmem : x ∈ dotPerp (dotPerp P ⊔ K ∙ r i ⊔ K ∙ r j ⊔ K ∙ r l) := by
    simp only [dotPerp_sup, Submodule.mem_inf, mem_dotPerp_span_singleton]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rw [← dotPerp_dotPerp P] at hxP; exact hxP
    all_goals rw [dotProduct_comm]; exact hx' _
  rwa [h, dotPerp_top, Submodule.mem_bot] at hmem

/-- Three vectors added one at a time to a subspace of codimension three fill the space. -/
theorem eq_top_of_chain {N : ℕ} {L T : Submodule K (Fin N → K)} {x y f : Fin N → K}
    (hL : L ≤ T) (hx : x ∈ T) (hy : y ∈ T) (hf : f ∈ T) (h1 : x ∉ L) (h2 : y ∉ L ⊔ K ∙ x)
    (h3 : f ∉ L ⊔ K ∙ x ⊔ K ∙ y) (hd : Module.finrank K L + 3 = N) : T = ⊤ := by
  have e1 := finrank_sup_span_singleton_of_notMem h1
  have e2 := finrank_sup_span_singleton_of_notMem h2
  have e3 := finrank_sup_span_singleton_of_notMem h3
  have hle : L ⊔ K ∙ x ⊔ K ∙ y ⊔ K ∙ f ≤ T := by
    simp only [sup_le_iff, Submodule.span_singleton_le_iff_mem]
    exact ⟨⟨⟨hL, hx⟩, hy⟩, hf⟩
  refine Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le T) ?_)
  have := Submodule.finrank_mono hle
  simp only [Module.finrank_fin_fun]
  omega

theorem mem_span_single_zero_of_eq_zero {y : Fin 4 → K} (h1 : y 1 = 0) (h2 : y 2 = 0)
    (h3 : y 3 = 0) : y ∈ K ∙ (Pi.single 0 1 : Fin 4 → K) := by
  refine Submodule.mem_span_singleton.2 ⟨y 0, ?_⟩
  funext t; fin_cases t <;> simp [h1, h2, h3]

/-- **The three forms** (the core of `exists_rowsMap_three`): for subspaces `L₁, L₂, L₃` of
codimension three, pairwise of codimension at most two, none in another, spanning a hyperplane
`H`, there are `μ_i ∈ L_i` such that `L_i` and the other two `μ_j` span `H`: each chosen off at most
two proper subspaces of `L_i` (`exists_mem_notMem_two`). -/
theorem exists_forms_three {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {N : ℕ} {L₁ L₂ L₃ H : Submodule K V}
    (d₁ : Module.finrank K L₁ + 3 = N) (d₂ : Module.finrank K L₂ + 3 = N)
    (d₃ : Module.finrank K L₃ + 3 = N) (dH : Module.finrank K H + 1 = N)
    (s₁₂ : N ≤ Module.finrank K (L₁ ⊔ L₂ : Submodule K V) + 2)
    (s₁₃ : N ≤ Module.finrank K (L₁ ⊔ L₃ : Submodule K V) + 2)
    (hLLL : L₁ ⊔ L₂ ⊔ L₃ = H)
    (n₃₁ : ¬ L₃ ≤ L₁) (n₃₂ : ¬ L₃ ≤ L₂) (n₂₃ : ¬ L₂ ≤ L₃) :
    ∃ μ₁ ∈ L₁, ∃ μ₂ ∈ L₂, ∃ μ₃ ∈ L₃, μ₃ ∉ L₁ ∧ μ₂ ∉ L₁ ⊔ K ∙ μ₃ ∧ μ₃ ∉ L₂ ∧
      μ₁ ∉ L₂ ⊔ K ∙ μ₃ ∧ μ₂ ∉ L₃ ∧ μ₁ ∉ L₃ ⊔ K ∙ μ₂ := by
  have h₁₂H : L₁ ⊔ L₂ ≤ H := hLLL ▸ le_sup_left
  have h₁₃H : L₁ ⊔ L₃ ≤ H := hLLL ▸ sup_le (le_sup_left.trans le_sup_left) le_sup_right
  have f₁₂ := Submodule.finrank_mono h₁₂H
  have f₁₃ := Submodule.finrank_mono h₁₃H
  -- `μ₃`
  obtain ⟨μ₃, hμ₃, h3₁, h3₂, h3₁₂⟩ : ∃ μ₃ ∈ L₃, μ₃ ∉ L₁ ∧ μ₃ ∉ L₂ ∧
      (Module.finrank K (L₁ ⊔ L₂ : Submodule K V) + 1 ≠ N → μ₃ ∉ L₁ ⊔ L₂) := by
    by_cases hc : Module.finrank K (L₁ ⊔ L₂ : Submodule K V) + 1 = N
    · obtain ⟨μ, hμ, h1, h2⟩ := exists_mem_notMem_two n₃₁ n₃₂
      exact ⟨μ, hμ, h1, h2, fun h => absurd hc h⟩
    · have hn : ¬ L₃ ≤ L₁ ⊔ L₂ := fun h => by
        rw [sup_eq_left.2 h] at hLLL; rw [hLLL] at hc; exact hc dH
      obtain ⟨μ, hμ, h1, -⟩ := exists_mem_notMem_two hn hn
      exact ⟨μ, hμ, fun h => h1 (Submodule.mem_sup_left h),
        fun h => h1 (Submodule.mem_sup_right h), fun _ => h1⟩
  -- `μ₂`
  obtain ⟨μ₂, hμ₂, h2a, h2₃, h2₁₃⟩ : ∃ μ₂ ∈ L₂, μ₂ ∉ L₁ ⊔ K ∙ μ₃ ∧ μ₂ ∉ L₃ ∧
      (Module.finrank K (L₁ ⊔ L₃ : Submodule K V) + 1 ≠ N → μ₂ ∉ L₁ ⊔ L₃) := by
    have hA : ¬ L₂ ≤ L₁ ⊔ K ∙ μ₃ := fun h => by
      have hs : L₁ ⊔ L₂ ≤ L₁ ⊔ K ∙ μ₃ := sup_le le_sup_left h
      have e := finrank_sup_span_singleton_of_notMem h3₁
      have := Submodule.finrank_mono hs
      by_cases hc : Module.finrank K (L₁ ⊔ L₂ : Submodule K V) + 1 = N
      · omega
      · have heq : L₁ ⊔ L₂ = L₁ ⊔ K ∙ μ₃ := Submodule.eq_of_le_of_finrank_le hs (by omega)
        exact h3₁₂ hc (heq ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self μ₃))
    by_cases hc : Module.finrank K (L₁ ⊔ L₃ : Submodule K V) + 1 = N
    · obtain ⟨μ, hμ, h1, h2⟩ := exists_mem_notMem_two hA n₂₃
      exact ⟨μ, hμ, h1, h2, fun h => absurd hc h⟩
    · have hB : ¬ L₂ ≤ L₁ ⊔ L₃ := fun h => by
        have h' : L₁ ⊔ L₂ ⊔ L₃ ≤ L₁ ⊔ L₃ := sup_le (sup_le le_sup_left h) le_sup_right
        rw [hLLL] at h'
        have := Submodule.finrank_mono h'
        omega
      obtain ⟨μ, hμ, h1, h2⟩ := exists_mem_notMem_two hA hB
      exact ⟨μ, hμ, h1, fun h => h2 (Submodule.mem_sup_right h), fun _ => h2⟩
  -- `μ₁`
  have hA : ¬ L₁ ≤ L₂ ⊔ K ∙ μ₃ := fun h => by
    have hs : L₁ ⊔ L₂ ≤ L₂ ⊔ K ∙ μ₃ := sup_le h le_sup_left
    have e := finrank_sup_span_singleton_of_notMem h3₂
    have := Submodule.finrank_mono hs
    by_cases hc : Module.finrank K (L₁ ⊔ L₂ : Submodule K V) + 1 = N
    · omega
    · have heq : L₁ ⊔ L₂ = L₂ ⊔ K ∙ μ₃ := Submodule.eq_of_le_of_finrank_le hs (by omega)
      exact h3₁₂ hc (heq ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self μ₃))
  have hB : ¬ L₁ ≤ L₃ ⊔ K ∙ μ₂ := fun h => by
    have hs : L₁ ⊔ L₃ ≤ L₃ ⊔ K ∙ μ₂ := sup_le h le_sup_left
    have e := finrank_sup_span_singleton_of_notMem h2₃
    have := Submodule.finrank_mono hs
    by_cases hc : Module.finrank K (L₁ ⊔ L₃ : Submodule K V) + 1 = N
    · omega
    · have heq : L₁ ⊔ L₃ = L₃ ⊔ K ∙ μ₂ := Submodule.eq_of_le_of_finrank_le hs (by omega)
      exact h2₁₃ hc (heq ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self μ₂))
  obtain ⟨μ₁, hμ₁, h1a, h1b⟩ := exists_mem_notMem_two hA hB
  exact ⟨μ₁, hμ₁, μ₂, hμ₂, μ₃, hμ₃, h3₁, h2a, h3₂, h1a, h2₃, h1b⟩

theorem not_dotPerp_le_dotPerp {N : ℕ} {P Q : Submodule K (Fin N → K)}
    (hP : Module.finrank K P = 3) (hPQ : Module.finrank K (P ⊓ Q : Submodule K _) ≤ 2) :
    ¬ dotPerp Q ≤ dotPerp P := fun h => by
  have h' := dotPerp_antitone h
  rw [dotPerp_dotPerp, dotPerp_dotPerp] at h'
  rw [inf_eq_left.2 h'] at hPQ; omega

/-- The rows of `rowsMap` that vanish on a subspace. -/
theorem rowsMap_apply_eq_zero {N : ℕ} {r : Fin 4 → Fin N → K} {P : Submodule K (Fin N → K)}
    {t : Fin 4} (ht : r t ∈ dotPerp P) {x : Fin N → K} (hx : x ∈ P) : rowsMap r x t = 0 :=
  mem_dotPerp.1 ht x hx

/-- **One projection for a set of three subspaces** (a step of
`lem:pencil-d-nondegenerate-feasible`): three-dimensional `P₁, P₂, P₃ ∋ b ≠ 0`, pairwise meeting
in dimension at most two and all three in dimension at most one, have a linear map `π` to `K⁴`,
injective on each, whose images meet in dimension at most one. Its rows are a form `f` with
`f(b) ≠ 0` and forms `μ_i` vanishing on `P_i` (`exists_forms_three`). -/
theorem exists_rowsMap_three {N : ℕ} {b : Fin N → K} (hb : b ≠ 0)
    {P₁ P₂ P₃ : Submodule K (Fin N → K)} (hb₁ : b ∈ P₁) (hb₂ : b ∈ P₂) (hb₃ : b ∈ P₃)
    (d₁ : Module.finrank K P₁ = 3) (d₂ : Module.finrank K P₂ = 3)
    (d₃ : Module.finrank K P₃ = 3)
    (h₁₂ : Module.finrank K (P₁ ⊓ P₂ : Submodule K (Fin N → K)) ≤ 2)
    (h₁₃ : Module.finrank K (P₁ ⊓ P₃ : Submodule K (Fin N → K)) ≤ 2)
    (h₂₃ : Module.finrank K (P₂ ⊓ P₃ : Submodule K (Fin N → K)) ≤ 2)
    (h₁₂₃ : Module.finrank K (P₁ ⊓ P₂ ⊓ P₃ : Submodule K (Fin N → K)) ≤ 1) :
    ∃ r : Fin 4 → Fin N → K, Set.InjOn (rowsMap r) P₁ ∧ Set.InjOn (rowsMap r) P₂ ∧
      Set.InjOn (rowsMap r) P₃ ∧
      Module.finrank K (P₁.map (rowsMap r) ⊓ P₂.map (rowsMap r) ⊓ P₃.map (rowsMap r) :
        Submodule K (Fin 4 → K)) ≤ 1 := by
  have N4 : 4 ≤ N := by
    have := Submodule.finrank_sup_add_finrank_inf_eq P₁ P₂
    have := Submodule.finrank_le (P₁ ⊔ P₂)
    rw [Module.finrank_fin_fun] at this
    omega
  have dL₁ := finrank_dotPerp_add P₁
  have dL₂ := finrank_dotPerp_add P₂
  have dL₃ := finrank_dotPerp_add P₃
  have dH : Module.finrank K (dotPerp (K ∙ b)) + 1 = N := by
    have := finrank_dotPerp_add (K ∙ b); rwa [finrank_span_singleton hb] at this
  have hLH : ∀ {P : Submodule K (Fin N → K)}, b ∈ P → dotPerp P ≤ dotPerp (K ∙ b) := fun h =>
    dotPerp_antitone ((Submodule.span_singleton_le_iff_mem _ _).2 h)
  have s₁₂ : N ≤ Module.finrank K (dotPerp P₁ ⊔ dotPerp P₂ : Submodule K _) + 2 := by
    have := finrank_dotPerp_add (P₁ ⊓ P₂); rw [dotPerp_inf] at this; omega
  have s₁₃ : N ≤ Module.finrank K (dotPerp P₁ ⊔ dotPerp P₃ : Submodule K _) + 2 := by
    have := finrank_dotPerp_add (P₁ ⊓ P₃); rw [dotPerp_inf] at this; omega
  have hLLL : dotPerp P₁ ⊔ dotPerp P₂ ⊔ dotPerp P₃ = dotPerp (K ∙ b) := by
    refine Submodule.eq_of_le_of_finrank_le (sup_le (sup_le (hLH hb₁) (hLH hb₂)) (hLH hb₃)) ?_
    have := finrank_dotPerp_add (P₁ ⊓ P₂ ⊓ P₃); rw [dotPerp_inf, dotPerp_inf] at this; omega
  have h₃₂ : Module.finrank K (P₃ ⊓ P₂ : Submodule K _) ≤ 2 := by rwa [inf_comm]
  obtain ⟨μ₁, hμ₁, μ₂, hμ₂, μ₃, hμ₃, h3₁, h2a, h3₂, h1a, h2₃, h1b⟩ :=
    exists_forms_three (by omega) (by omega) (by omega) dH s₁₂ s₁₃ hLLL
      (not_dotPerp_le_dotPerp d₁ h₁₃) (not_dotPerp_le_dotPerp d₂ h₂₃)
      (not_dotPerp_le_dotPerp d₃ h₃₂)
  obtain ⟨f, -, hf⟩ : ∃ f ∈ (⊤ : Submodule K (Fin N → K)), f ∉ dotPerp (K ∙ b) := by
    refine IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.2 fun h => ?_)
    rw [h, finrank_top, Module.finrank_fin_fun] at dH; omega
  have hLHs : ∀ {x : Fin N → K}, x ∈ dotPerp (K ∙ b) → ∀ {L : Submodule K (Fin N → K)},
      L ≤ dotPerp (K ∙ b) → L ⊔ K ∙ x ≤ dotPerp (K ∙ b) := fun hx _ hL =>
    sup_le hL ((Submodule.span_singleton_le_iff_mem _ _).2 hx)
  have hsub : ∀ {x y : Fin N → K} {L : Submodule K (Fin N → K)}, x ∈ dotPerp (K ∙ b) →
      y ∈ dotPerp (K ∙ b) → L ≤ dotPerp (K ∙ b) → f ∉ L ⊔ K ∙ x ⊔ K ∙ y :=
    fun hx hy hL h => hf (hLHs hy (hLHs hx hL) h)
  have m₁ := hLH hb₁ hμ₁
  have m₂ := hLH hb₂ hμ₂
  have m₃ := hLH hb₃ hμ₃
  have chain : ∀ {L : Submodule K (Fin N → K)} {x y : Fin N → K}, x ∉ L → y ∉ L ⊔ K ∙ x →
      L ≤ dotPerp (K ∙ b) → x ∈ dotPerp (K ∙ b) → y ∈ dotPerp (K ∙ b) →
      Module.finrank K L + 3 = N → L ⊔ K ∙ f ⊔ K ∙ y ⊔ K ∙ x = ⊤ := by
    intro L x y h1 h2 hL hx hy hd
    exact eq_top_of_chain (x := x) (y := y) (f := f)
      (le_sup_left.trans (le_sup_left.trans le_sup_left)) (Submodule.mem_sup_right
        (Submodule.mem_span_singleton_self _)) (Submodule.mem_sup_left (Submodule.mem_sup_right
        (Submodule.mem_span_singleton_self _))) (Submodule.mem_sup_left (Submodule.mem_sup_left
        (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)))) h1 h2
        (hsub hx hy hL) hd
  refine ⟨![f, μ₁, μ₂, μ₃], ?_, ?_, ?_, ?_⟩
  · exact injOn_rowsMap (i := 0) (j := 2) (l := 3) (chain h3₁ h2a (hLH hb₁) m₃ m₂ (by omega))
  · exact injOn_rowsMap (i := 0) (j := 1) (l := 3) (chain h3₂ h1a (hLH hb₂) m₃ m₁ (by omega))
  · exact injOn_rowsMap (i := 0) (j := 1) (l := 2) (chain h2₃ h1b (hLH hb₃) m₂ m₁ (by omega))
  · have hle : (P₁.map (rowsMap ![f, μ₁, μ₂, μ₃]) ⊓ P₂.map (rowsMap ![f, μ₁, μ₂, μ₃]) ⊓
        P₃.map (rowsMap ![f, μ₁, μ₂, μ₃]) : Submodule K (Fin 4 → K)) ≤
        K ∙ (Pi.single 0 1 : Fin 4 → K) := by
      rintro y ⟨⟨⟨x₁, hx₁, rfl⟩, ⟨x₂, hx₂, hy₂⟩⟩, ⟨x₃, hx₃, hy₃⟩⟩
      refine mem_span_single_zero_of_eq_zero ?_ ?_ ?_
      · exact rowsMap_apply_eq_zero (t := 1) hμ₁ hx₁
      · rw [← hy₂]; exact rowsMap_apply_eq_zero (t := 2) hμ₂ hx₂
      · rw [← hy₃]; exact rowsMap_apply_eq_zero (t := 3) hμ₃ hx₃
    calc _ ≤ Module.finrank K (K ∙ (Pi.single 0 1 : Fin 4 → K)) := Submodule.finrank_mono hle
      _ = 1 := finrank_span_singleton (by simp)

/-- **One projection for a set of two subspaces** (a step of
`lem:pencil-d-nondegenerate-feasible`): three-dimensional `P₁ ≠ P₂ ∋ b ≠ 0` have a linear map to
`K⁴`, injective on both, whose images meet in dimension at most two. Its rows are `f` with
`f(b) ≠ 0`, `μ_i` vanishing on `P_i` and not on the other, and `g` vanishing at `b`. -/
theorem exists_rowsMap_two {N : ℕ} {b : Fin N → K} (hb : b ≠ 0)
    {P₁ P₂ : Submodule K (Fin N → K)} (hb₁ : b ∈ P₁) (hb₂ : b ∈ P₂)
    (d₁ : Module.finrank K P₁ = 3) (d₂ : Module.finrank K P₂ = 3)
    (h₁₂ : Module.finrank K (P₁ ⊓ P₂ : Submodule K (Fin N → K)) ≤ 2) :
    ∃ r : Fin 4 → Fin N → K, Set.InjOn (rowsMap r) P₁ ∧ Set.InjOn (rowsMap r) P₂ ∧
      Module.finrank K (P₁.map (rowsMap r) ⊓ P₂.map (rowsMap r) : Submodule K (Fin 4 → K)) ≤ 2 := by
  have N4 : 4 ≤ N := by
    have := Submodule.finrank_sup_add_finrank_inf_eq P₁ P₂
    have := Submodule.finrank_le (P₁ ⊔ P₂)
    rw [Module.finrank_fin_fun] at this
    omega
  have dL₁ := finrank_dotPerp_add P₁
  have dL₂ := finrank_dotPerp_add P₂
  have dH : Module.finrank K (dotPerp (K ∙ b)) + 1 = N := by
    have := finrank_dotPerp_add (K ∙ b); rwa [finrank_span_singleton hb] at this
  have hLH : ∀ {P : Submodule K (Fin N → K)}, b ∈ P → dotPerp P ≤ dotPerp (K ∙ b) := fun h =>
    dotPerp_antitone ((Submodule.span_singleton_le_iff_mem _ _).2 h)
  have h₂₁ : Module.finrank K (P₂ ⊓ P₁ : Submodule K _) ≤ 2 := by rwa [inf_comm]
  obtain ⟨μ₁, hμ₁, h1, -⟩ := exists_mem_notMem_two (not_dotPerp_le_dotPerp d₂ h₂₁)
    (not_dotPerp_le_dotPerp d₂ h₂₁)
  obtain ⟨μ₂, hμ₂, h2, -⟩ := exists_mem_notMem_two (not_dotPerp_le_dotPerp d₁ h₁₂)
    (not_dotPerp_le_dotPerp d₁ h₁₂)
  have hprop : ∀ {L : Submodule K (Fin N → K)} {x : Fin N → K}, Module.finrank K L + 3 = N →
      ¬ dotPerp (K ∙ b) ≤ L ⊔ K ∙ x := fun {L x} hL h => by
    have := Submodule.finrank_mono h
    have := Submodule.finrank_add_le_finrank_add_finrank L (K ∙ x)
    have := finrank_span_le_card (R := K) ({x} : Set (Fin N → K))
    simp at this
    omega
  obtain ⟨g, hg, hg₁, hg₂⟩ := exists_mem_notMem_two (hprop (L := dotPerp P₁) (x := μ₂)
    (by omega)) (hprop (L := dotPerp P₂) (x := μ₁) (by omega))
  obtain ⟨f, -, hf⟩ : ∃ f ∈ (⊤ : Submodule K (Fin N → K)), f ∉ dotPerp (K ∙ b) := by
    refine IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.2 fun h => ?_)
    rw [h, finrank_top, Module.finrank_fin_fun] at dH; omega
  have hLHs : ∀ {x : Fin N → K}, x ∈ dotPerp (K ∙ b) → ∀ {L : Submodule K (Fin N → K)},
      L ≤ dotPerp (K ∙ b) → L ⊔ K ∙ x ≤ dotPerp (K ∙ b) := fun hx _ hL =>
    sup_le hL ((Submodule.span_singleton_le_iff_mem _ _).2 hx)
  have chain : ∀ {L : Submodule K (Fin N → K)} {x y : Fin N → K}, x ∉ L → y ∉ L ⊔ K ∙ x →
      L ≤ dotPerp (K ∙ b) → x ∈ dotPerp (K ∙ b) → y ∈ dotPerp (K ∙ b) →
      Module.finrank K L + 3 = N → L ⊔ K ∙ f ⊔ K ∙ x ⊔ K ∙ y = ⊤ := by
    intro L x y h1 h2 hL hx hy hd
    refine eq_top_of_chain (x := x) (y := y) (f := f)
      (le_sup_left.trans (le_sup_left.trans le_sup_left)) (Submodule.mem_sup_left
        (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)))
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
      (Submodule.mem_sup_left (Submodule.mem_sup_left
        (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)))) h1 h2
      (fun h => hf (hLHs hy (hLHs hx hL) h)) hd
  refine ⟨![f, μ₁, μ₂, g], ?_, ?_, ?_⟩
  · exact injOn_rowsMap (i := 0) (j := 2) (l := 3)
      (chain h2 hg₁ (hLH hb₁) (hLH hb₂ hμ₂) hg (by omega))
  · exact injOn_rowsMap (i := 0) (j := 1) (l := 3)
      (chain h1 hg₂ (hLH hb₂) (hLH hb₁ hμ₁) hg (by omega))
  · have hle : (P₁.map (rowsMap ![f, μ₁, μ₂, g]) ⊓ P₂.map (rowsMap ![f, μ₁, μ₂, g]) :
        Submodule K (Fin 4 → K)) ≤ Submodule.span K (Set.range ![(Pi.single 0 1 : Fin 4 → K),
          Pi.single 3 1]) := by
      rintro y ⟨⟨x₁, hx₁, rfl⟩, ⟨x₂, hx₂, hy₂⟩⟩
      have e1 : rowsMap ![f, μ₁, μ₂, g] x₁ 1 = 0 := rowsMap_apply_eq_zero (t := 1) hμ₁ hx₁
      have e2 : rowsMap ![f, μ₁, μ₂, g] x₁ 2 = 0 := by
        rw [← hy₂]; exact rowsMap_apply_eq_zero (t := 2) hμ₂ hx₂
      refine (Submodule.mem_span_range_iff_exists_fun K).2 ⟨![rowsMap ![f, μ₁, μ₂, g] x₁ 0,
        rowsMap ![f, μ₁, μ₂, g] x₁ 3], ?_⟩
      funext t; fin_cases t <;> simp [Fin.sum_univ_two, e1, e2]
    calc _ ≤ _ := Submodule.finrank_mono hle
      _ ≤ 2 := by
        have := finrank_range_le_card (R := K) ![(Pi.single 0 1 : Fin 4 → K), Pi.single 3 1]
        rwa [Set.finrank, Fintype.card_fin] at this

/-! ## Feasibility in every dimension: the general projection -/

theorem isPolyFun_rowsMap {N : ℕ} (y : Fin N → K) (i : Fin 4) :
    IsPolyFun fun x : Fin 4 × Fin N → K => rowsMap (fun i j => x (i, j)) y i :=
  ⟨∑ j, MvPolynomial.X (i, j) * MvPolynomial.C (y j), fun x => by
    simp [rowsMap_apply, dotProduct]⟩

theorem rowsMap_matrix {N : ℕ} (π : (Fin N → K) →ₗ[K] (Fin 4 → K)) :
    rowsMap (fun i j => π (Pi.single j 1) i) = π := by
  refine LinearMap.ext fun y => funext fun i => ?_
  rw [rowsMap_apply, LinearMap.pi_apply_eq_sum_univ π y]
  simp only [dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]
  congr 2
  have : (Pi.single j 1 : Fin N → K) = fun t => if j = t then 1 else 0 := by
    funext t; simp [Pi.single_apply, eq_comm]
  rw [this]

/-- A linear map that keeps a spanning family of `P` independent is injective on `P`. -/
theorem injOn_of_linearIndependent_comp {N M : ℕ} {π : (Fin N → K) →ₗ[K] (Fin M → K)}
    {P : Submodule K (Fin N → K)} {β : Fin 3 → Fin N → K}
    (hβ : Submodule.span K (Set.range β) = P) (hLI : LinearIndependent K (π ∘ β)) :
    Set.InjOn π P := by
  have hmap : P.map π = Submodule.span K (Set.range (π ∘ β)) := by
    rw [← hβ, Submodule.map_span, Set.range_comp]
  have h1 : Module.finrank K (P.map π) = 3 := by
    rw [hmap, finrank_span_eq_card hLI, Fintype.card_fin]
  have h2 : Module.finrank K P ≤ 3 := by
    have := finrank_range_le_card (R := K) β
    rwa [Set.finrank, Fintype.card_fin, hβ] at this
  have hrn := LinearMap.finrank_range_add_finrank_ker (π.domRestrict P)
  rw [LinearMap.range_domRestrict, h1] at hrn
  have hker : LinearMap.ker (π.domRestrict P) = ⊥ :=
    Submodule.finrank_eq_zero.1 (by omega)
  intro x hx y hy hxy
  have := LinearMap.ker_eq_bot.1 hker (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy
  exact congrArg Subtype.val this

theorem comp_eq_vec3 {N M : ℕ} (π : (Fin N → K) →ₗ[K] (Fin M → K)) (β : Fin 3 → Fin N → K) :
    π ∘ β = ![π (β 0), π (β 1), π (β 2)] := by
  funext j; fin_cases j <;> rfl

/-- **The image of a subspace is the orthogonal of `ν`** (a step of
`lem:pencil-d-nondegenerate-feasible`): where `ν = πβ₀ × πβ₁ × πβ₂ ≠ 0`, for a spanning family
`β` of `P`, `π` is injective on `P` and `πP = ν^⊥`. -/
theorem map_eq_dotPerp_cross₃ {N : ℕ} {π : (Fin N → K) →ₗ[K] (Fin 4 → K)}
    {P : Submodule K (Fin N → K)} {β : Fin 3 → Fin N → K}
    (hβ : Submodule.span K (Set.range β) = P)
    (hν : cross₃ (π (β 0)) (π (β 1)) (π (β 2)) ≠ 0) :
    Set.InjOn π P ∧ P.map π = dotPerp (K ∙ cross₃ (π (β 0)) (π (β 1)) (π (β 2))) := by
  have hLI : LinearIndependent K (π ∘ β) := by
    rw [comp_eq_vec3]; exact (cross₃_ne_zero_iff_linearIndependent _ _ _).1 hν
  refine ⟨injOn_of_linearIndependent_comp hβ hLI, ?_⟩
  have hmap : P.map π = Submodule.span K (Set.range (π ∘ β)) := by
    rw [← hβ, Submodule.map_span, Set.range_comp]
  rw [hmap]
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rw [Submodule.span_le, Set.range_subset_iff]
    intro j
    rw [SetLike.mem_coe, mem_dotPerp_span_singleton, dotProduct_comm]
    fin_cases j
    exacts [cross₃_dotProduct_fst _ _ _, cross₃_dotProduct_snd _ _ _,
      cross₃_dotProduct_thd _ _ _]
  · rw [finrank_span_eq_card hLI, Fintype.card_fin,
      finrank_dotPerp_span_singleton_of_ne_zero hν]

theorem cross₃_ne_zero_of_injOn {N : ℕ} {π : (Fin N → K) →ₗ[K] (Fin 4 → K)}
    {P : Submodule K (Fin N → K)} {β : Fin 3 → Fin N → K}
    (hβ : Submodule.span K (Set.range β) = P) (hβLI : LinearIndependent K β)
    (hinj : Set.InjOn π P) : cross₃ (π (β 0)) (π (β 1)) (π (β 2)) ≠ 0 := by
  rw [cross₃_ne_zero_iff_linearIndependent, ← comp_eq_vec3]
  exact hβLI.map_injOn π (hβ ▸ hinj)

/-- **Finitely many nonempty Zariski-open sets meet**, over an infinite field. -/
theorem exists_forall_mem_of_isZariskiOpen [Infinite K] {σ ι : Type*} [Finite ι]
    {U : ι → Set (σ → K)} (hU : ∀ i, IsZariskiOpen (U i)) (hne : ∀ i, (U i).Nonempty) :
    ∃ s, ∀ i, s ∈ U i := by
  choose s₀ hs₀ using hne
  choose R hR0 hR using fun i => hU i (s₀ i) (hs₀ i)
  obtain ⟨s, hs⟩ := exists_common_eval_ne_zero_of_forall_exists R fun i => ⟨s₀ i, hR0 i⟩
  exact ⟨s, fun i => hR i s (hs i)⟩

/-- An injective linear map on a three-dimensional subspace of `K^N` to `K⁴`. -/
theorem exists_injOn_of_finrank_eq_three {N : ℕ} {P : Submodule K (Fin N → K)}
    (hP : Module.finrank K P = 3) :
    ∃ π : (Fin N → K) →ₗ[K] (Fin 4 → K), Set.InjOn π P := by
  let e : P ≃ₗ[K] (Fin 3 → K) := (Module.finBasisOfFinrankEq K P hP).equivFun
  let ι : (Fin 3 → K) →ₗ[K] (Fin 4 → K) :=
    Function.ExtendByZero.linearMap K K (Fin.castSucc : Fin 3 → Fin 4)
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (ι ∘ₗ e.toLinearMap)
  refine ⟨g, fun x hx y hy hxy => ?_⟩
  have hx' : g x = ι (e ⟨x, hx⟩) := LinearMap.congr_fun hg ⟨x, hx⟩
  have hy' : g y = ι (e ⟨y, hy⟩) := LinearMap.congr_fun hg ⟨y, hy⟩
  have h : ι (e ⟨x, hx⟩) = ι (e ⟨y, hy⟩) := hx'.symm.trans (hxy.trans hy')
  have hι : Function.Injective ι := fun a c hac => by
    funext j
    have := congrFun hac j.castSucc
    simpa [ι, Fin.castSucc_injective, Function.Injective.extend_apply] using this
  exact congrArg Subtype.val (e.injective (hι h))

/-- **One projection for one set** (a step of `lem:pencil-d-nondegenerate-feasible`, (b) at one
body and one set): `exists_rowsMap_two` or `exists_rowsMap_three`, as a nondegenerate set has at
most three members. -/
theorem exists_injOn_finrank_iInf_map_le {N : ℕ} {G : Graph α β} {b : α → Fin N → K}
    {plane : α → Submodule K (Fin N → K)} (hb : ∀ v ∈ V(G), b v ≠ 0)
    (hdim : ∀ v ∈ V(G), Module.finrank K (plane v) = 3)
    (hmem : ∀ v ∈ V(G), ∀ w ∈ G.closedNbhd v, b w ∈ plane v)
    (hcond : PencilNondegConditions G b plane) {v : α} (hv : v ∈ V(G)) {S : Finset α}
    (hS : (S : Set α) ⊆ G.closedHubNbhd v) (h2 : 2 ≤ S.card) :
    ∃ π : (Fin N → K) →ₗ[K] (Fin 4 → K), (∀ w ∈ S, Set.InjOn π (plane w)) ∧
      Module.finrank K (⨅ w ∈ S, (plane w).map π : Submodule K (Fin 4 → K)) + S.card ≤ 4 := by
  classical
  have hwV : ∀ w ∈ S, w ∈ V(G) := fun w hw => (hS hw).1.1
  have hbw : ∀ w ∈ S, b v ∈ plane w := fun w hw => hmem w (hwV w hw) v (by
    rcases (hS hw).2 with rfl | ⟨e, he⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨e, he.symm⟩)
  have hc := hcond.2.2 v hv S hS h2
  have hpair : ∀ w₁ ∈ S, ∀ w₂ ∈ S, w₁ ≠ w₂ →
      Module.finrank K (plane w₁ ⊓ plane w₂ : Submodule K (Fin N → K)) ≤ 2 := by
    intro w₁ h₁ w₂ h₂ hne
    have hsub : (({w₁, w₂} : Finset α) : Set α) ⊆ G.closedHubNbhd v := by
      intro x hx
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      exacts [hS h₁, hS h₂]
    have := hcond.2.2 v hv {w₁, w₂} hsub (by rw [Finset.card_pair hne])
    rw [Finset.card_pair hne, Finset.iInf_insert, Finset.iInf_singleton] at this
    omega
  have hcard : S.card ≤ 3 := by
    have hle : K ∙ b v ≤ ⨅ w ∈ S, plane w := le_iInf₂ fun w hw =>
      (Submodule.span_singleton_le_iff_mem _ _).2 (hbw w hw)
    have := Submodule.finrank_mono hle
    rw [finrank_span_singleton (hb v hv)] at this
    omega
  rcases (show S.card = 2 ∨ S.card = 3 by omega) with h | h
  · obtain ⟨w₁, w₂, hne, rfl⟩ := Finset.card_eq_two.1 h
    have m₁ : w₁ ∈ ({w₁, w₂} : Finset α) := by simp
    have m₂ : w₂ ∈ ({w₁, w₂} : Finset α) := by simp
    obtain ⟨r, hr₁, hr₂, hr⟩ := exists_rowsMap_two (hb v hv) (hbw w₁ m₁) (hbw w₂ m₂)
      (hdim w₁ (hwV w₁ m₁)) (hdim w₂ (hwV w₂ m₂)) (hpair w₁ m₁ w₂ m₂ hne)
    refine ⟨rowsMap r, fun w hw => ?_, ?_⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl <;> assumption
    · rw [Finset.iInf_insert, Finset.iInf_singleton, Finset.card_pair hne]; omega
  · obtain ⟨w₁, w₂, w₃, h12, h13, h23, rfl⟩ := Finset.card_eq_three.1 h
    have m₁ : w₁ ∈ ({w₁, w₂, w₃} : Finset α) := by simp
    have m₂ : w₂ ∈ ({w₁, w₂, w₃} : Finset α) := by simp
    have m₃ : w₃ ∈ ({w₁, w₂, w₃} : Finset α) := by simp
    have h₁₂₃ : Module.finrank K
        (plane w₁ ⊓ plane w₂ ⊓ plane w₃ : Submodule K (Fin N → K)) ≤ 1 := by
      rw [Finset.iInf_insert, Finset.iInf_insert, Finset.iInf_singleton, h, ← inf_assoc] at hc
      omega
    obtain ⟨r, hr₁, hr₂, hr₃, hr⟩ := exists_rowsMap_three (hb v hv) (hbw w₁ m₁) (hbw w₂ m₂)
      (hbw w₃ m₃) (hdim w₁ (hwV w₁ m₁)) (hdim w₂ (hwV w₂ m₂)) (hdim w₃ (hwV w₃ m₃))
      (hpair w₁ m₁ w₂ m₂ h12) (hpair w₁ m₁ w₃ m₃ h13) (hpair w₂ m₂ w₃ m₃ h23) h₁₂₃
    refine ⟨rowsMap r, fun w hw => ?_, ?_⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl <;> assumption
    · rw [Finset.iInf_insert, Finset.iInf_insert, Finset.iInf_singleton, h, ← inf_assoc]; omega

/-- **A projection to `K⁴` keeping nondegeneracy** (the core of
`lem:pencil-d-nondegenerate-feasible`): a linear map `π : K^N → K⁴` injective on every `Π_v` and
satisfying (b) at every body and set. Each requirement is the independence of vectors with
polynomial coordinates in the entries of `π` (`ν_w`, the `cross₃` of `π` on a basis of `Π_w`), so
open, and holds at some `π` (`exists_injOn_of_finrank_eq_three`,
`exists_injOn_finrank_iInf_map_le`); finitely many meet (`exists_forall_mem_of_isZariskiOpen`). -/
theorem exists_proj_of_pencilNondegConditions [Infinite K] [Finite α] {N : ℕ} {G : Graph α β}
    {b : α → Fin N → K} {plane : α → Submodule K (Fin N → K)}
    (hb : ∀ v ∈ V(G), b v ≠ 0) (hdim : ∀ v ∈ V(G), Module.finrank K (plane v) = 3)
    (hmem : ∀ v ∈ V(G), ∀ w ∈ G.closedNbhd v, b w ∈ plane v)
    (hcond : PencilNondegConditions G b plane) :
    ∃ π : (Fin N → K) →ₗ[K] (Fin 4 → K), (∀ v ∈ V(G), Set.InjOn π (plane v)) ∧
      ∀ v ∈ V(G), ∀ S : Finset α, (S : Set α) ⊆ G.closedHubNbhd v → 2 ≤ S.card →
        Module.finrank K (⨅ w ∈ S, (plane w).map π : Submodule K (Fin 4 → K)) + S.card ≤ 4 := by
  classical
  have hβ : ∀ w, ∃ β : Fin 3 → Fin N → K, w ∈ V(G) →
      LinearIndependent K β ∧ Submodule.span K (Set.range β) = plane w := by
    intro w
    by_cases hw : w ∈ V(G)
    · let B := Module.finBasisOfFinrankEq K (plane w) (hdim w hw)
      refine ⟨(plane w).subtype ∘ B, fun _ => ⟨B.linearIndependent.map' _
        (Submodule.ker_subtype _), ?_⟩⟩
      rw [Set.range_comp, ← Submodule.map_span, B.span_eq, Submodule.map_top,
        Submodule.range_subtype]
    · exact ⟨0, fun h => absurd h hw⟩
  choose β hβ using hβ
  let π : (Fin 4 × Fin N → K) → (Fin N → K) →ₗ[K] (Fin 4 → K) := fun x =>
    rowsMap fun i j => x (i, j)
  let ν : (Fin 4 × Fin N → K) → α → Fin 4 → K := fun x w =>
    cross₃ (π x (β w 0)) (π x (β w 1)) (π x (β w 2))
  have hπpoly : ∀ y i, IsPolyFun fun x => π x y i := fun y i => isPolyFun_rowsMap y i
  have hνpoly : ∀ w i, IsPolyFun fun x => ν x w i := fun w i =>
    isPolyFun_cross₃ (hπpoly _) (hπpoly _) (hπpoly _) i
  have hmat : ∀ π₀ : (Fin N → K) →ₗ[K] (Fin 4 → K),
      π (fun p => π₀ (Pi.single p.2 1) p.1) = π₀ := fun π₀ => rowsMap_matrix π₀
  -- `(b)` from the independence of the `ν_w`, and back
  have hreq : ∀ x {S : Finset α}, (∀ w ∈ S, w ∈ V(G)) →
      (LinearIndepOn K (ν x) (S : Set α) ↔ (∀ w ∈ S, Set.InjOn (π x) (plane w)) ∧
        Module.finrank K (⨅ w ∈ S, (plane w).map (π x) : Submodule K (Fin 4 → K)) + S.card
          ≤ 4) := by
    intro x S hSV
    constructor
    · intro hLI
      have hne : ∀ w ∈ S, ν x w ≠ 0 := fun w hw => hLI.ne_zero hw
      have hm := fun w (hw : w ∈ S) => map_eq_dotPerp_cross₃ (hβ w (hSV w hw)).2 (hne w hw)
      refine ⟨fun w hw => (hm w hw).1, ?_⟩
      have heq : (⨅ w ∈ S, (plane w).map (π x)) = ⨅ w ∈ S, dotPerp (K ∙ ν x w) :=
        iInf_congr fun w => iInf_congr fun hw => (hm w hw).2
      rw [heq]
      exact (finrank_iInf_dotPerp_add_card_le_iff (ν x) S).2 hLI
    · rintro ⟨hinj, hdimS⟩
      have hm := fun w (hw : w ∈ S) => map_eq_dotPerp_cross₃ (hβ w (hSV w hw)).2
        (cross₃_ne_zero_of_injOn (hβ w (hSV w hw)).2 (hβ w (hSV w hw)).1 (hinj w hw))
      have heq : (⨅ w ∈ S, (plane w).map (π x)) = ⨅ w ∈ S, dotPerp (K ∙ ν x w) :=
        iInf_congr fun w => iInf_congr fun hw => (hm w hw).2
      rw [heq] at hdimS
      exact (finrank_iInf_dotPerp_add_card_le_iff (ν x) S).1 hdimS
  let U : α ⊕ (α × Finset α) → Set (Fin 4 × Fin N → K) := fun i => match i with
    | .inl w => {x | w ∈ V(G) → LinearIndependent K (π x ∘ β w)}
    | .inr p => {x | (p.1 ∈ V(G) ∧ (p.2 : Set α) ⊆ G.closedHubNbhd p.1 ∧ 2 ≤ p.2.card) →
        LinearIndepOn K (ν x) (p.2 : Set α)}
  have hUo : ∀ i, IsZariskiOpen (U i) := by
    rintro (w | ⟨v, S⟩)
    · exact isZariskiOpen_imp _ (isZariskiOpen_linearIndependent_univ (fun x => π x ∘ β w)
        fun j i => hπpoly _ i)
    · exact isZariskiOpen_imp _ (isZariskiOpen_linearIndependent (fun x => ν x)
        (fun w i => hνpoly w i) _)
  have hUne : ∀ i, (U i).Nonempty := by
    rintro (w | ⟨v, S⟩)
    · by_cases hw : w ∈ V(G)
      · obtain ⟨π₀, hπ₀⟩ := exists_injOn_of_finrank_eq_three (hdim w hw)
        refine ⟨fun p => π₀ (Pi.single p.2 1) p.1, fun _ => ?_⟩
        rw [hmat]
        exact (hβ w hw).1.map_injOn π₀ ((hβ w hw).2 ▸ hπ₀)
      · exact ⟨0, fun h => absurd h hw⟩
    · by_cases hc : v ∈ V(G) ∧ (S : Set α) ⊆ G.closedHubNbhd v ∧ 2 ≤ S.card
      · obtain ⟨hv, hS, h2⟩ := hc
        obtain ⟨π₀, hinj, hdimS⟩ :=
          exists_injOn_finrank_iInf_map_le hb hdim hmem hcond hv hS h2
        refine ⟨fun p => π₀ (Pi.single p.2 1) p.1, fun _ => ?_⟩
        change LinearIndepOn K (ν (fun p => π₀ (Pi.single p.2 1) p.1)) (S : Set α)
        have h' := (hreq (fun p => π₀ (Pi.single p.2 1) p.1) fun w hw => (hS hw).1.1).2
        rw [hmat] at h'
        exact h' ⟨hinj, hdimS⟩
      · exact ⟨0, fun h => absurd h hc⟩
  obtain ⟨x, hx⟩ := exists_forall_mem_of_isZariskiOpen hUo hUne
  refine ⟨π x, fun v hv => injOn_of_linearIndependent_comp (hβ v hv).2 (hx (.inl v) hv),
    fun v hv S hS h2 => ?_⟩
  have hSV : ∀ w ∈ S, w ∈ V(G) := fun w hw => (hS hw).1.1
  exact ((hreq x hSV).1 (hx (.inr (v, S)) ⟨hv, hS, h2⟩)).2

/-- **Nondegeneracy-feasibility does not depend on the dimension**
(`lem:pencil-d-nondegenerate-feasible`), at grade `k ≥ 2`, that is `d = k + 1 ≥ 3`. -/
theorem gradedPencilNondegFeasible_iff [Infinite K] [Finite α] {k : ℕ} (hk : 2 ≤ k)
    (G : Graph α β) : GradedPencilNondegFeasible K k G ↔ PencilNondegFeasible K G := by
  rw [← gradedPencilNondegFeasible_two_iff]
  constructor
  · rintro ⟨F, b, plane, hreal, hcond⟩
    have hmem : ∀ v ∈ V(G), ∀ w ∈ G.closedNbhd v, b w ∈ plane v := fun v hv w hw =>
      hreal.normal_mem_plane_of_mem_closedNbhd hv hw
    obtain ⟨π, hinj, hπS⟩ := exists_proj_of_pencilNondegConditions hreal.1.2.1 hreal.2.1 hmem
      hcond
    have hspan : ∀ {s : Set α} {v : α}, v ∈ V(G) → s ⊆ G.closedNbhd v →
        Set.InjOn π (Submodule.span K (b '' s)) := fun {s v} hv hs =>
      (hinj v hv).mono (Submodule.span_le.2 (by
        rintro _ ⟨w, hw, rfl⟩; exact hmem v hv w (hs hw)))
    have hlink : ∀ e u v, G.IsLink e u v → LinearIndependent K ![π (b u), π (b v)] := by
      intro e u v he
      have := (hcond.1 e u v he).map_injOn π (by
        have h := hspan (s := {u, v}) he.left_mem (by
          rintro x (rfl | rfl)
          exacts [Or.inl rfl, Or.inr ⟨e, he⟩])
        rwa [Set.image_pair, ← Matrix.range_cons_cons_empty] at h)
      convert this using 1
      funext i; fin_cases i <;> rfl
    obtain ⟨F', hF'⟩ := exists_hasPencilPlaneRealization (k := 2) (G := G) (β := β)
      (b := fun v => π (b v)) (plane := fun v => (plane v).map π)
      (fun v hv h0 => hreal.1.2.1 v hv ((hinj v hv) (hreal.2.2.1 v hv) (plane v).zero_mem
        (by rw [h0, map_zero])))
      hlink (fun v hv => by rw [finrank_map_of_injOn π (hinj v hv), hreal.2.1 v hv])
      (fun v hv w hw => Submodule.mem_map_of_mem (hmem v hv w hw))
    refine ⟨F', _, _, hF', hlink, fun v hv hhub => ?_, fun v hv S hS h2 => hπS v hv S hS h2⟩
    exact (hcond.2.1 v hv hhub).map_injOn π (hspan hv subset_rfl)
  · rintro ⟨F, b, plane, hnd⟩
    exact ⟨_, _, _, hnd.map_gradeEmbed hk⟩

end CombinatorialRigidity.Molecular
