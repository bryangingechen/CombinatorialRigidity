/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Configuration

/-!
# Coplanarity is linear in the heights, in every dimension

`lem:pencil-d-condition-linear` (`blueprint/src/chapter/pencil-d.tex`, `sec:pencil-d-induction`):
over an admissible picture `q`, the points of the configuration `(q, z)` with `m` heights at the
closed neighbourhood of a body `v` span a subspace of `K^(m+3)` of dimension at most three exactly
when each height `z^i` agrees there with an affine function `h_i ⬝ᵥ (x, y, 1)` of the picture. They
then span the image `Π_v` of the injective linear map `σ_h : K³ → K^(m+3)`,
`c ↦ (c 0, c 1, (h_i ⬝ᵥ c)_i, c 2)` (`gradeSigma`), and `Π_v^⊥` is spanned by the `m` independent
vectors `n^i = (h_i 0, h_i 1, -e_i, h_i 2)` (`gradeSigmaPerp`). In particular `z ∈ L(q)^m` exactly
when every closed neighbourhood spans at most three dimensions.

The projection `π` of `K^(m+3)` to the coordinates `0`, `1` and the last takes the point of `w` to
its homogeneous picture point. Admissibility makes `π` map the span `S` of a closed neighbourhood
onto `K³`, so `dim S ≤ 3` makes `π` an isomorphism of `S` onto `K³`, and the height coordinates of
its inverse are the linear forms `h_i ⬝ᵥ ·`. This replaces the one plane normal of the `d = 3`
proof (`Graph.IsAdmissiblePicture.mem_liftingSpace_iff_coplanar`), which does not generalize.

## Main definitions

* `gradeSigma`: the map `σ_h`.
* `gradeSigmaPerp`: the vectors `n^i` spanning the orthogonal of its image.

## Main results

* `gradeSigma_injective`, `finrank_range_gradeSigma`: `σ_h` is injective, of rank three.
* `dotPerp_range_gradeSigma`, `linearIndependent_gradeSigmaPerp`: `Π^⊥ = span {n^i}`, and the
  `n^i` are independent.
* `pencilConfigPointGrade_eq_gradeSigma_iff`: the point of `w` is `σ_h (x_w, y_w, 1)` exactly when
  every height agrees with `h` at `w`.
* `Graph.IsAdmissiblePicture.finrank_span_pencilConfigPointGrade_closedNbhd_le_iff`: the
  equivalence at one body.
* `Graph.IsAdmissiblePicture.span_pencilConfigPointGrade_closedNbhd_eq_range`: the span is
  `Π_v = range σ_h`.
* `Graph.IsAdmissiblePicture.mem_liftingSpaceGrade_iff_finrank_span_closedNbhd_le`: the "in
  particular".
-/

@[expose] public section

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*} {m : ℕ}

/-! ## The map `σ_h` and the vectors `n^i` -/

/-- **The map `σ_h`** (`lem:pencil-d-condition-linear`): for `m` coefficient triples
`h_i = (a^i, c^i, e^i)`, the linear map `K³ → K^(m+3)`,
`(ξ, η, ω) ↦ (ξ, η, a^1 ξ + c^1 η + e^1 ω, …, a^m ξ + c^m η + e^m ω, ω)`, built from its blocks as
`pencilConfigPointGrade` is (`gradeMk`). It keeps the coordinates `0`, `1` and the last
(`gradeSigma_apply`), so it is injective (`gradeSigma_injective`). -/
def gradeSigma (h : Fin m → Fin 3 → K) : (Fin 3 → K) →ₗ[K] (Fin (m + 1 + 2) → K) where
  toFun c := gradeMk (c 0) (c 1) (fun i => h i ⬝ᵥ c) (c 2)
  map_add' c c' := by
    rw [gradeMk_add]
    exact gradeMk_ext rfl rfl (funext fun i => by simp [dotProduct_add]) rfl
  map_smul' r c := by
    rw [RingHom.id_apply, gradeMk_smul]
    exact gradeMk_ext rfl rfl (funext fun i => by simp [dotProduct_smul]) rfl

theorem gradeSigma_apply (h : Fin m → Fin 3 → K) (c : Fin 3 → K) :
    gradeSigma h c = gradeMk (c 0) (c 1) (fun i => h i ⬝ᵥ c) (c 2) := rfl

/-- **`σ_h` is injective**: it keeps the coordinates `0`, `1` and the last. -/
theorem gradeSigma_injective (h : Fin m → Fin 3 → K) : Function.Injective (gradeSigma h) := by
  intro c c' hcc
  have h0 := congr_fun hcc 0
  have h1 := congr_fun hcc 1
  have h2 := congr_fun hcc (Fin.last (m + 2))
  simp only [gradeSigma_apply, gradeMk_apply_zero, gradeMk_apply_one, gradeMk_apply_last]
    at h0 h1 h2
  funext j
  fin_cases j
  · exact h0
  · exact h1
  · exact h2

/-- **The image `Π` of `σ_h` is three-dimensional**, as `σ_h` is injective. -/
theorem finrank_range_gradeSigma (h : Fin m → Fin 3 → K) :
    Module.finrank K (LinearMap.range (gradeSigma h)) = 3 := by
  rw [LinearMap.finrank_range_of_inj (gradeSigma_injective h)]
  simp

/-- **The vectors `n^i` orthogonal to the image of `σ_h`** (`lem:pencil-d-condition-linear`):
`n^i = (a^i, c^i, -e_i, e^i)` for `h_i = (a^i, c^i, e^i)`, where `e_i` is the `i`-th standard basis
vector of the heights, so that
`n^i ⬝ᵥ (ξ, η, ζ, ω) = a^i ξ + c^i η - ζ^i + e^i ω` (`gradeSigmaPerp_dotProduct_gradeMk`). -/
def gradeSigmaPerp (h : Fin m → Fin 3 → K) (i : Fin m) : Fin (m + 1 + 2) → K :=
  gradeMk (h i 0) (h i 1) (-Pi.single i 1) (h i 2)

theorem gradeSigmaPerp_dotProduct_gradeMk (h : Fin m → Fin 3 → K) (i : Fin m) (x y : K)
    (u : Fin m → K) (w : K) :
    gradeSigmaPerp h i ⬝ᵥ gradeMk x y u w = h i 0 * x + h i 1 * y - u i + h i 2 * w := by
  rw [gradeSigmaPerp, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp [gradeMk, -Fin.succ_last, Pi.single_apply]
  ring

theorem gradeSigmaPerp_dotProduct_gradeSigma (h : Fin m → Fin 3 → K) (i : Fin m)
    (c : Fin 3 → K) : gradeSigmaPerp h i ⬝ᵥ gradeSigma h c = 0 := by
  rw [gradeSigma_apply, gradeSigmaPerp_dotProduct_gradeMk]
  simp [dotProduct, Fin.sum_univ_three]

/-- **The `n^i` are linearly independent**: their height blocks are `-e_i`. -/
theorem linearIndependent_gradeSigmaPerp (h : Fin m → Fin 3 → K) :
    LinearIndependent K (gradeSigmaPerp h) := by
  let π : (Fin (m + 1 + 2) → K) →ₗ[K] (Fin m → K) :=
    LinearMap.funLeft K K (fun j : Fin m => j.castSucc.succ.succ)
  refine LinearIndependent.of_comp π ?_
  have : (π ∘ gradeSigmaPerp h) = -fun i => Pi.single i 1 := by
    funext i
    change gradeHeights (gradeSigmaPerp h i) = _
    simp [gradeSigmaPerp]
  rw [this]
  exact (Pi.linearIndependent_single_one (Fin m) K).neg

/-- **`Π^⊥` is spanned by the `n^i`** (`lem:pencil-d-condition-linear`): the orthogonal of the
image of `σ_h` (`dotPerp`) is the span of the `m` vectors `gradeSigmaPerp h i`. Each is orthogonal
to the image (`gradeSigmaPerp_dotProduct_gradeSigma`), they are independent
(`linearIndependent_gradeSigmaPerp`), and the orthogonal has dimension `(m + 3) − 3 = m`
(`finrank_dotPerp`, `finrank_range_gradeSigma`). -/
theorem dotPerp_range_gradeSigma (h : Fin m → Fin 3 → K) :
    dotPerp (LinearMap.range (gradeSigma h))
      = Submodule.span K (Set.range (gradeSigmaPerp h)) := by
  symm
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rw [Submodule.span_le, Set.range_subset_iff]
    intro i
    rw [SetLike.mem_coe, mem_dotPerp]
    rintro _ ⟨c, rfl⟩
    exact gradeSigmaPerp_dotProduct_gradeSigma h i c
  · rw [finrank_span_eq_card (linearIndependent_gradeSigmaPerp h), finrank_dotPerp,
      finrank_range_gradeSigma]
    simp

/-! ## The points of a closed neighbourhood -/

/-- **The point of a body is `σ_h` of its picture point exactly when its heights agree with `h`**:
`b_w = σ_h (x_w, y_w, 1)` exactly when `z^i_w = h_i ⬝ᵥ (x_w, y_w, 1)` for every height `i`, the two
sides agreeing in the coordinates `0`, `1` and the last. -/
theorem pencilConfigPointGrade_eq_gradeSigma_iff (q : α × Fin 2 → K) (z : α × Fin m → K)
    (h : Fin m → Fin 3 → K) (w : α) :
    pencilConfigPointGrade q z w = gradeSigma h (pencilPicturePoint q w) ↔
      ∀ i, z (w, i) = h i ⬝ᵥ pencilPicturePoint q w := by
  rw [pencilConfigPointGrade_eq_gradeMk, gradeSigma_apply]
  constructor
  · intro hw i
    have := congr_arg gradeHeights hw
    simp only [gradeHeights_gradeMk] at this
    exact congr_fun this i
  · intro hw
    exact gradeMk_ext rfl rfl (funext hw) rfl

/-- **The points of a closed neighbourhood span the image of `σ_h`**
(`lem:pencil-d-condition-linear`, its second sentence): over an admissible picture, if every height
agrees on the closed neighbourhood of `v ∈ V(G)` with the affine function `h_i`, the span of the
points there is the image `Π_v` of `σ_h`. It lies in the image
(`pencilConfigPointGrade_eq_gradeSigma_iff`), which has dimension three
(`finrank_range_gradeSigma`), and contains three independent points
(`linearIndependent_pencilConfigPointGrade_of_linearIndependent_pencilPicturePoint`). -/
theorem _root_.Graph.IsAdmissiblePicture.span_pencilConfigPointGrade_closedNbhd_eq_range
    {G : Graph α β} {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) {z : α × Fin m → K}
    {v : α} (hv : v ∈ V(G)) {h : Fin m → Fin 3 → K}
    (hh : ∀ i, ∀ w ∈ G.closedNbhd v, z (w, i) = h i ⬝ᵥ pencilPicturePoint q w) :
    Submodule.span K (pencilConfigPointGrade q z '' G.closedNbhd v)
      = LinearMap.range (gradeSigma h) := by
  have hle : Submodule.span K (pencilConfigPointGrade q z '' G.closedNbhd v)
      ≤ LinearMap.range (gradeSigma h) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨pencilPicturePoint q w,
      ((pencilConfigPointGrade_eq_gradeSigma_iff q z h w).2 fun i => hh i w hw).symm⟩
  refine Submodule.eq_of_le_of_finrank_le hle ?_
  rw [finrank_range_gradeSigma]
  obtain ⟨t, ht, hli⟩ := hq.2 v hv
  have hli' :=
    linearIndependent_pencilConfigPointGrade_of_linearIndependent_pencilPicturePoint z hli
  calc 3 = Module.finrank K
        (Submodule.span K (Set.range fun i => pencilConfigPointGrade q z (t i))) := by
          rw [finrank_span_eq_card hli']; simp
    _ ≤ _ := Submodule.finrank_mono (Submodule.span_mono ?_)
  rintro _ ⟨i, rfl⟩
  exact ⟨t i, ht i, rfl⟩

/-- **Coplanarity is linear in the heights, at one body** (`lem:pencil-d-condition-linear`, its
first sentence): over an admissible picture, the points of the configuration `(q, z)` with `m`
heights at the closed neighbourhood of `v ∈ V(G)` span a subspace of dimension at most three exactly
when each height agrees there with an affine function `h_i ⬝ᵥ (x, y, 1)` of the picture.

The "if" half is `Graph.IsAdmissiblePicture.span_pencilConfigPointGrade_closedNbhd_eq_range`. For
the "only if" half, the projection `π` to the coordinates `0`, `1` and the last maps the span `S`
onto `K³`, as it takes three independent points of `S` to independent picture points; so
`dim S ≤ 3 = dim K³` makes `π` an isomorphism `e` of `S` onto `K³`
(`LinearMap.injective_iff_surjective_of_finrank_eq_finrank`). Every point of the closed
neighbourhood is `e⁻¹` of its picture point, and the `i`-th height coordinate of `e⁻¹` is a linear
form on `K³`, `h_i ⬝ᵥ ·` (`LinearMap.pi_apply_eq_sum_univ`). -/
theorem _root_.Graph.IsAdmissiblePicture.finrank_span_pencilConfigPointGrade_closedNbhd_le_iff
    {G : Graph α β} {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) (z : α × Fin m → K)
    {v : α} (hv : v ∈ V(G)) :
    Module.finrank K (Submodule.span K (pencilConfigPointGrade q z '' G.closedNbhd v)) ≤ 3 ↔
      ∃ h : Fin m → Fin 3 → K,
        ∀ i, ∀ w ∈ G.closedNbhd v, z (w, i) = h i ⬝ᵥ pencilPicturePoint q w := by
  constructor
  · intro hS
    classical
    set S := Submodule.span K (pencilConfigPointGrade q z '' G.closedNbhd v) with hSdef
    -- `π` keeps the coordinates `0`, `1` and the last.
    let π : (Fin (m + 1 + 2) → K) →ₗ[K] (Fin 3 → K) :=
      LinearMap.funLeft K K ![0, 1, Fin.last (m + 2)]
    have hπ : ∀ w, π (pencilConfigPointGrade q z w) = pencilPicturePoint q w := by
      intro w; funext j; fin_cases j <;> simp [π, pencilPicturePoint]
    have hmem : ∀ w ∈ G.closedNbhd v, pencilConfigPointGrade q z w ∈ S :=
      fun w hw => Submodule.subset_span ⟨w, hw, rfl⟩
    obtain ⟨t, ht, hli⟩ := hq.2 v hv
    -- `π` maps `S` onto `K³`.
    have hsurj : Function.Surjective (π.domRestrict S) := by
      rw [← LinearMap.range_eq_top, eq_top_iff,
        ← hli.span_eq_top_of_card_eq_finrank (by simp), Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨⟨_, hmem (t i) (ht i)⟩, hπ (t i)⟩
    have hdim : Module.finrank K S = Module.finrank K (Fin 3 → K) :=
      le_antisymm (by simpa using hS) (LinearMap.finrank_le_finrank_of_surjective hsurj)
    have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hsurj
    let e : S ≃ₗ[K] (Fin 3 → K) := LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩
    let σ : (Fin 3 → K) →ₗ[K] (Fin (m + 1 + 2) → K) := S.subtype ∘ₗ e.symm.toLinearMap
    have hσ : ∀ w ∈ G.closedNbhd v,
        σ (pencilPicturePoint q w) = pencilConfigPointGrade q z w := by
      intro w hw
      have : e ⟨_, hmem w hw⟩ = pencilPicturePoint q w := hπ w
      simp only [σ, LinearMap.comp_apply, LinearEquiv.coe_coe, ← this,
        LinearEquiv.symm_apply_apply, Submodule.subtype_apply]
    -- The height coordinates of `σ` are linear forms.
    let ℓ : Fin m → (Fin 3 → K) →ₗ[K] K := fun i =>
      LinearMap.proj (i.castSucc.succ.succ : Fin (m + 1 + 2)) ∘ₗ σ
    refine ⟨fun i j => ℓ i (fun k => if j = k then 1 else 0), fun i w hw => ?_⟩
    rw [← pencilConfigPointGrade_apply_height q z w i, ← hσ w hw]
    change ℓ i (pencilPicturePoint q w) = _
    rw [LinearMap.pi_apply_eq_sum_univ (ℓ i), dotProduct]
    exact Finset.sum_congr rfl fun j _ => by rw [smul_eq_mul, mul_comm]
  · rintro ⟨h, hh⟩
    rw [hq.span_pencilConfigPointGrade_closedNbhd_eq_range hv hh, finrank_range_gradeSigma]

/-- **`z ∈ L(q)^m` exactly when every closed neighbourhood spans at most three dimensions**
(`lem:pencil-d-condition-linear`, its last sentence): over an admissible picture, heights `z`
vanishing off `V(G)` lie in `L(q)^m` (`Graph.liftingSpaceGrade`) exactly when the points of every
closed neighbourhood span a subspace of dimension at most three. It is
`Graph.IsAdmissiblePicture.finrank_span_pencilConfigPointGrade_closedNbhd_le_iff` at every body.
Lean's `Graph.liftingSpace` holds heights that vanish off `V(G)`, hence `hs`, as in the `d = 3`
form `Graph.IsAdmissiblePicture.mem_liftingSpace_iff_coplanar`. -/
theorem _root_.Graph.IsAdmissiblePicture.mem_liftingSpaceGrade_iff_finrank_span_closedNbhd_le
    {G : Graph α β} {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) {z : α × Fin m → K}
    (hs : ∀ i, ∀ w ∉ V(G), z (w, i) = 0) :
    z ∈ G.liftingSpaceGrade q m ↔ ∀ v ∈ V(G),
      Module.finrank K (Submodule.span K (pencilConfigPointGrade q z '' G.closedNbhd v)) ≤ 3 := by
  rw [Graph.mem_liftingSpaceGrade]
  constructor
  · intro hz v hv
    choose h hh using fun i => (hz i).2 v hv
    exact (hq.finrank_span_pencilConfigPointGrade_closedNbhd_le_iff z hv).2 ⟨h, hh⟩
  · intro hS i
    refine ⟨hs i, fun v hv => ?_⟩
    obtain ⟨h, hh⟩ := (hq.finrank_span_pencilConfigPointGrade_closedNbhd_le_iff z hv).1 (hS v hv)
    exact ⟨h i, hh i⟩

end CombinatorialRigidity.Molecular
