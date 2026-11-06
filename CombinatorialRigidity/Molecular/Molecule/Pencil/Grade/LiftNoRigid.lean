/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Mathlib.LinearAlgebra.Pi
public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.LiftCutEdge
public import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.GenericBase

/-!
# The general lift attains without a planar-rigid set

`lem:pencil-d-lift-no-rigid` of `blueprint/src/chapter/pencil-d.tex`: a graph that satisfies the
standing hypotheses, is nondegeneracy-feasible and has no planar-rigid set, and whose general
configuration attains in dimension `d = r + 3`, has its general lift attaining in dimension `d`
(`liftAttains_of_forall_deficiency_two_ne_zero`).

A nondegenerate configuration `(q, z⁰)` over a general picture is the realization `r*` in dimension
three, as at `d = 3`
(`Graph.IsX0Graph.hasGenericPencilRealization_of_forall_deficiency_two_ne_zero`): its first height
`z⁰` has the planes of any two distinct bodies distinct (`exists_planeDiff_ne_zero_poly`), and the
other heights of an attaining `z` are a lift of it
(`mem_liftMaps_pencilConfigPoint_iff`, `liftNormal_pencilConfigPoint`). `dim L̃` is least at `r*`
(`liftAttains_of_least`): at a configuration it is `dim L(q)` plus a count of free coordinates
(`finrank_liftSpaceTilde_pencilConfigPoint`, `liftFreeCoords`), at a general realization the
points rescale to a configuration over an admissible picture
(`exists_pencilConfigPoint_of_dotProduct`), and `q` is a main picture.

Two steps are stated for any graph with no planar-rigid set, for `lem:pencil-d-ear-free`: the
distinct planes (`exists_planeDiff_ne_zero_poly`) and `dim L̃` at a configuration
(`finrank_liftSpaceTilde_pencilConfigPoint`).
-/

@[expose] public section

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

/-! ## `L̃` at a configuration -/

/-- **The coordinates of `L̃` the lifting system does not see**: the maps off `V(G)`, the forms
off `V(G)`, and the third coordinate of the forms on `V(G)`. -/
def liftFreeCoords (G : Graph α β) : Submodule K (α ⊕ α × Fin 4 → K) where
  carrier := {e | (∀ w ∈ V(G), e (.inl w) = 0) ∧ ∀ v ∈ V(G), ∀ i, i ≠ 2 → e (.inr (v, i)) = 0}
  add_mem' {x y} hx hy := ⟨fun w hw => by simp [hx.1 w hw, hy.1 w hw],
    fun v hv i hi => by simp [hx.2 v hv i hi, hy.2 v hv i hi]⟩
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩
  smul_mem' c x hx := ⟨fun w hw => by simp [hx.1 w hw], fun v hv i hi => by simp [hx.2 v hv i hi]⟩

/-- The embedding `(a₀, a₁, a₂) ↦ (a₀, a₁, 0, a₂)` of affine coefficients into forms on `K⁴`. -/
def planeForm (a : Fin 3 → K) : Fin 4 → K := ![a 0, a 1, 0, a 2]

open Classical in
/-- From `L̃` to the lifting system: the maps on `V(G)`, and at every body of `G` the affine
coefficients of its form along the plane `h_v`. -/
noncomputable def liftTildeToLk (G : Graph α β) (h : α → Fin 3 → K) :
    (α ⊕ α × Fin 4 → K) →ₗ[K] (α ⊕ α × Fin 3 → K) where
  toFun y := Sum.elim (fun w => if w ∈ V(G) then y (.inl w) else 0)
    (fun p => if p.1 ∈ V(G) then y (.inr (p.1, ![0, 1, 3] p.2)) + y (.inr (p.1, 2)) * h p.1 p.2
      else 0)
  map_add' y y' := by
    funext c; rcases c with w | ⟨v, i⟩ <;> simp only [Sum.elim_inl, Sum.elim_inr, Pi.add_apply] <;>
      split_ifs <;> ring
  map_smul' a y := by
    funext c; rcases c with w | ⟨v, i⟩ <;>
      simp only [Sum.elim_inl, Sum.elim_inr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] <;>
      split_ifs <;> ring

open Classical in
/-- From `L̃` to its free coordinates. -/
noncomputable def liftTildeToFree (G : Graph α β) :
    (α ⊕ α × Fin 4 → K) →ₗ[K] (α ⊕ α × Fin 4 → K) where
  toFun y := Sum.elim (fun w => if w ∈ V(G) then 0 else y (.inl w))
    (fun p => if p.1 ∈ V(G) ∧ p.2 ≠ 2 then 0 else y (.inr p))
  map_add' y y' := by
    funext c; rcases c with w | ⟨v, i⟩ <;> simp only [Sum.elim_inl, Sum.elim_inr, Pi.add_apply] <;>
      split_ifs <;> ring
  map_smul' a y := by
    funext c; rcases c with w | ⟨v, i⟩ <;>
      simp only [Sum.elim_inl, Sum.elim_inr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] <;>
      split_ifs <;> ring

open Classical in
/-- From the lifting system and the free coordinates to `L̃`: the form `(h₀, h₁, 0, h₂)` of the
affine coefficients, moved along the normal `(−h_v, 1)` of the plane by the free third
coordinate. -/
noncomputable def liftTildeOfLk (G : Graph α β) (h : α → Fin 3 → K) :
    (α ⊕ α × Fin 3 → K) × (α ⊕ α × Fin 4 → K) →ₗ[K] (α ⊕ α × Fin 4 → K) where
  toFun xe := Sum.elim (fun w => xe.1 (.inl w) + xe.2 (.inl w))
    (fun p => planeForm (fun i => xe.1 (.inr (p.1, i))) p.2 + xe.2 (.inr p) -
      if p.1 ∈ V(G) then xe.2 (.inr (p.1, 2)) * planeForm (h p.1) p.2 else 0)
  map_add' y y' := by
    funext c; rcases c with w | ⟨v, i⟩
    · simp only [Sum.elim_inl, Prod.fst_add, Prod.snd_add, Pi.add_apply]; ring
    · simp only [Sum.elim_inr, Prod.fst_add, Prod.snd_add, Pi.add_apply]
      split_ifs <;> fin_cases i <;> simp [planeForm] <;> ring
  map_smul' a y := by
    funext c; rcases c with w | ⟨v, i⟩
    · simp only [Sum.elim_inl, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
        RingHom.id_apply]; ring
    · simp only [Sum.elim_inr, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
        RingHom.id_apply]
      split_ifs <;> fin_cases i <;> simp [planeForm] <;> ring

theorem liftTildeToLk_mem [Fintype α] {G : Graph α β} {q : α × Fin 2 → K} {z : α → K}
    {h : α → Fin 3 → K}
    (hh : ∀ v ∈ V(G), ∀ w ∈ G.closedNbhd v, z w = h v ⬝ᵥ pencilPicturePoint q w)
    {y : α ⊕ α × Fin 4 → K} (hy : y ∈ liftSpaceTilde G (pencilConfigPoint q z)) :
    liftTildeToLk G h y ∈
      LinearMap.ker ((G.liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin := by
  rw [Graph.mem_ker_liftingMatrix_iff]
  refine ⟨fun w hw => by simp [liftTildeToLk, hw], fun v hv w hw => ?_,
    fun v hv i => by simp [liftTildeToLk, hv]⟩
  have hwV := Graph.closedNbhd_subset_vertexSet hv hw
  simp only [liftTildeToLk, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl, Sum.elim_inr,
    ite_eq_left hwV, ite_eq_left hv]
  rw [hy v hv w hw]
  simp [Fin.sum_univ_four, dotProduct, Fin.sum_univ_three, pencilConfigPoint, pencilPicturePoint,
    hh v hv w hw]
  ring

theorem liftTildeToFree_mem (G : Graph α β) (y : α ⊕ α × Fin 4 → K) :
    liftTildeToFree G y ∈ liftFreeCoords (K := K) G :=
  ⟨fun w hw => by simp [liftTildeToFree, hw], fun v hv i hi => by simp [liftTildeToFree, hv, hi]⟩

theorem eq_zero_of_liftTildeToLk_eq_zero {G : Graph α β} {h : α → Fin 3 → K}
    {y : α ⊕ α × Fin 4 → K} (h₁ : liftTildeToLk G h y = 0) (h₂ : liftTildeToFree G y = 0) :
    y = 0 := by
  funext c
  rcases c with w | ⟨v, i⟩
  · have e₁ := congr_fun h₁ (.inl w)
    have e₂ := congr_fun h₂ (.inl w)
    simp only [liftTildeToLk, liftTildeToFree, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl,
      Pi.zero_apply] at e₁ e₂
    by_cases hw : w ∈ V(G) <;> simp_all
  · have e₂ := congr_fun h₂ (.inr (v, i))
    simp only [liftTildeToFree, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inr,
      Pi.zero_apply] at e₂
    by_cases hv : v ∈ V(G)
    · have h2 : y (.inr (v, 2)) = 0 := by
        have := congr_fun h₂ (.inr (v, 2))
        simpa [liftTildeToFree] using this
      have e₁ : ∀ j, y (.inr (v, ![0, 1, 3] j)) = 0 := fun j => by
        have := congr_fun h₁ (.inr (v, j))
        simpa [liftTildeToLk, hv, h2] using this
      fin_cases i
      · exact e₁ 0
      · exact e₁ 1
      · exact h2
      · exact e₁ 2
    · simpa [hv] using e₂

theorem liftTildeOfLk_mem [Fintype α] {G : Graph α β} {q : α × Fin 2 → K} {z : α → K}
    {h : α → Fin 3 → K}
    (hh : ∀ v ∈ V(G), ∀ w ∈ G.closedNbhd v, z w = h v ⬝ᵥ pencilPicturePoint q w)
    {x : α ⊕ α × Fin 3 → K}
    (hx : x ∈ LinearMap.ker ((G.liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin)
    {e : α ⊕ α × Fin 4 → K} (he : e ∈ liftFreeCoords (K := K) G) :
    liftTildeOfLk G h (x, e) ∈ liftSpaceTilde G (pencilConfigPoint q z) := by
  rw [Graph.mem_ker_liftingMatrix_iff] at hx
  intro v hv w hw
  have hwV := Graph.closedNbhd_subset_vertexSet hv hw
  have he0 : ∀ i, i ≠ 2 → e (.inr (v, i)) = 0 := he.2 v hv
  simp only [liftTildeOfLk, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl, Sum.elim_inr,
    ite_eq_left hv, he.1 w hwV, add_zero]
  rw [hx.2.1 v hv w hw]
  simp [Fin.sum_univ_four, dotProduct, Fin.sum_univ_three, pencilConfigPoint, pencilPicturePoint,
    planeForm, he0 0 (by decide), he0 1 (by decide), he0 3 (by decide), hh v hv w hw]
  ring

theorem eq_zero_of_liftTildeOfLk_eq_zero [Fintype α] {G : Graph α β} {q : α × Fin 2 → K}
    {h : α → Fin 3 → K} {x : α ⊕ α × Fin 3 → K}
    (hx : x ∈ LinearMap.ker ((G.liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin)
    {e : α ⊕ α × Fin 4 → K} (he : e ∈ liftFreeCoords (K := K) G)
    (h0 : liftTildeOfLk G h (x, e) = 0) : x = 0 ∧ e = 0 := by
  rw [Graph.mem_ker_liftingMatrix_iff] at hx
  have hc : ∀ c, liftTildeOfLk G h (x, e) c = 0 := fun c => congr_fun h0 c
  have hinl : ∀ w, x (.inl w) = 0 ∧ e (.inl w) = 0 := by
    intro w
    have := hc (.inl w)
    simp only [liftTildeOfLk, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl] at this
    by_cases hw : w ∈ V(G)
    · rw [he.1 w hw, add_zero] at this; exact ⟨this, he.1 w hw⟩
    · rw [hx.1 w hw, zero_add] at this; exact ⟨hx.1 w hw, this⟩
  have hinr : ∀ v, (∀ i, x (.inr (v, i)) = 0) ∧ ∀ i, e (.inr (v, i)) = 0 := by
    intro v
    have hv' := fun i => hc (.inr (v, i))
    simp only [liftTildeOfLk, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inr] at hv'
    by_cases hv : v ∈ V(G)
    · simp only [ite_eq_left hv] at hv'
      have he0 : ∀ i, i ≠ 2 → e (.inr (v, i)) = 0 := he.2 v hv
      have h2 : e (.inr (v, 2)) = 0 := by simpa [planeForm] using hv' 2
      refine ⟨fun i => ?_, fun i => ?_⟩
      · fin_cases i
        · simpa [planeForm, h2, he0 0 (by decide)] using hv' 0
        · simpa [planeForm, h2, he0 1 (by decide)] using hv' 1
        · simpa [planeForm, h2, he0 3 (by decide)] using hv' 3
      · by_cases hi : i = 2
        · rw [hi]; exact h2
        · exact he0 i hi
    · simp only [ite_eq_right hv, sub_zero] at hv'
      have hx0 : ∀ i, x (.inr (v, i)) = 0 := hx.2.2 v hv
      refine ⟨hx0, fun i => ?_⟩
      have := hv' i
      have hpf : planeForm (fun i => x (.inr (v, i))) = 0 := by
        funext j; fin_cases j <;> simp [planeForm, hx0]
      rwa [hpf, Pi.zero_apply, zero_add] at this
  refine ⟨funext fun c => ?_, funext fun c => ?_⟩
  · rcases c with w | ⟨v, i⟩
    exacts [(hinl w).1, (hinr v).1 i]
  · rcases c with w | ⟨v, i⟩
    exacts [(hinl w).2, (hinr v).2 i]

/-- **`dim L̃` at a configuration** (`lem:pencil-d-lift-no-rigid`, `L(b⁰) = L(q)` in dimension): at
the points of a configuration `(q, z)` with `z ∈ L(q)`, `L̃` has the dimension of the solutions of
the lifting system at `q` plus that of the free coordinates (`liftFreeCoords`), which does not
depend on `(q, z)`. A form at a body `v` of `G` is the form of its affine coefficients along the
plane `h_v` of `z`, moved by its third coordinate along the normal of that plane. -/
theorem finrank_liftSpaceTilde_pencilConfigPoint_ker [Fintype α] {G : Graph α β}
    {q : α × Fin 2 → K} {z : α → K} (hz : z ∈ G.liftingSpace q) :
    Module.finrank K (liftSpaceTilde G (pencilConfigPoint q z)) =
      Module.finrank K (LinearMap.ker ((G.liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin) +
        Module.finrank K (liftFreeCoords (K := K) G) := by
  obtain ⟨-, hz2⟩ := hz
  choose! h hh using hz2
  set Lk := LinearMap.ker ((G.liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin
  set L := liftSpaceTilde G (pencilConfigPoint q z)
  set E := liftFreeCoords (K := K) G
  rw [← Module.finrank_prod]
  refine le_antisymm ?_ ?_
  · let f : L →ₗ[K] Lk × E := LinearMap.prod
      (((liftTildeToLk G h).domRestrict L).codRestrict Lk fun y => liftTildeToLk_mem hh y.2)
      (((liftTildeToFree G).domRestrict L).codRestrict E fun y => liftTildeToFree_mem G y.1)
    refine LinearMap.finrank_le_finrank_of_injective (f := f) ?_
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h1 := congrArg (fun p => (p.1 : α ⊕ α × Fin 3 → K)) hy
    have h2 := congrArg (fun p => (p.2 : α ⊕ α × Fin 4 → K)) hy
    exact Subtype.ext (eq_zero_of_liftTildeToLk_eq_zero h1 h2)
  · let g : Lk × E →ₗ[K] L :=
      ((liftTildeOfLk G h).comp ((Lk.subtype).prodMap E.subtype)).codRestrict L fun xe =>
        liftTildeOfLk_mem hh xe.1.2 xe.2.2
    refine LinearMap.finrank_le_finrank_of_injective (f := g) ?_
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨x, e⟩ hxe
    have := eq_zero_of_liftTildeOfLk_eq_zero x.2 e.2 (congrArg Subtype.val hxe)
    exact Prod.ext (Subtype.ext this.1) (Subtype.ext this.2)

/-- **`dim L̃` at a configuration over an admissible picture**: `dim L(q)` plus the free
coordinates. -/
theorem finrank_liftSpaceTilde_pencilConfigPoint [Finite α] {G : Graph α β}
    {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) {z : α → K} (hz : z ∈ G.liftingSpace q) :
    Module.finrank K (liftSpaceTilde G (pencilConfigPoint q z)) =
      Module.finrank K (G.liftingSpace q) + Module.finrank K (liftFreeCoords (K := K) G) := by
  have := Fintype.ofFinite α
  rw [finrank_liftSpaceTilde_pencilConfigPoint_ker hz, Graph.finrank_ker_liftingMatrix hq]

/-- **`L(b⁰) = L(q)` at a configuration** (`lem:pencil-d-lift-no-rigid`): at the points of a
configuration `(q, z)` with `z ∈ L(q)`, a map `ζ` is the map of a lift exactly when it agrees on
every closed neighbourhood with an affine function of the picture, as the height `z` is one
there. -/
theorem mem_liftMaps_pencilConfigPoint_iff {G : Graph α β} {q : α × Fin 2 → K} {z : α → K}
    (hz : z ∈ G.liftingSpace q) {P0 : α → Submodule K (Fin 4 → K)}
    (hP0 : ∀ v ∈ V(G), ∀ w ∈ G.closedNbhd v, pencilConfigPoint q z w ∈ P0 v) {ζ : α → K} :
    ζ ∈ liftMaps G (pencilConfigPoint q z) P0 ↔
      ∀ v ∈ V(G), ∃ h : Fin 3 → K, ∀ w ∈ G.closedNbhd v, ζ w = h ⬝ᵥ pencilPicturePoint q w := by
  rw [mem_liftMaps_iff hP0]
  refine forall₂_congr fun v hv => ?_
  obtain ⟨h₀, hh₀⟩ := hz.2 v hv
  constructor
  · rintro ⟨ψ, hψ⟩
    refine ⟨![ψ (Pi.single 0 1) + ψ (Pi.single 2 1) * h₀ 0,
      ψ (Pi.single 1 1) + ψ (Pi.single 2 1) * h₀ 1,
      ψ (Pi.single 3 1) + ψ (Pi.single 2 1) * h₀ 2], fun w hw => ?_⟩
    have hψb : ψ (pencilConfigPoint q z w) =
        ∑ i, pencilConfigPoint q z w i * ψ (Pi.single i 1) := by
      rw [LinearMap.pi_apply_eq_sum_univ_single ψ]
      simp only [smul_eq_mul]
    rw [hψ w hw, hψb]
    simp only [Fin.sum_univ_four, pencilConfigPoint, dotProduct, Fin.sum_univ_three,
      pencilPicturePoint, hh₀ w hw]
    simp
    ring
  · rintro ⟨h, hh⟩
    refine ⟨{ toFun := fun p => h 0 * p 0 + h 1 * p 1 + h 2 * p 3
              map_add' := fun p p' => by simp only [Pi.add_apply]; ring
              map_smul' := fun c p => by
                simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring },
      fun w hw => ?_⟩
    simp [hh w hw, dotProduct, Fin.sum_univ_three, pencilPicturePoint, pencilConfigPoint]

/-! ## The planes of a general solution -/

/-- **The planes of a general solution are pairwise distinct** (`lem:pencil-d-lift-no-rigid`, a step
shared with `lem:pencil-d-ear-free`): let `G` be simple, with at least three members in every closed
neighbourhood and `def₂(G[Y]) ≠ 0` for every set `Y` of at least two bodies. Off the zero set of a
nonzero polynomial in the picture, some polynomial `ℓ` is nonzero at a solution of the lifting
system, and at every non-root of `ℓ` the planes of any two distinct bodies differ. `P` is the
product of the polynomials of `exists_planes_separate` (`lem:pencil-x0-planes-separate`), and `ℓ`
the product of one coordinate of `h_u − h_w` per pair, nonzero at one solution
(`exists_mem_forall_eval_ne_zero`, `lem:pencil-x0-fibre-intersection`). -/
theorem exists_planeDiff_ne_zero_poly [Infinite K] [Fintype α] [Finite β] {G : Graph α β}
    (hSimple : G.Simple) (h3 : ∀ v ∈ V(G), 3 ≤ (G.closedNbhd v).ncard)
    (hS : ∀ Y ⊆ V(G), 2 ≤ Y.ncard → (G.induce Y).deficiency 2 ≠ 0) :
    ∃ P : MvPolynomial (α × Fin 2) K, P ≠ 0 ∧ ∀ q, MvPolynomial.eval q P ≠ 0 →
      ∃ ℓ : MvPolynomial (α ⊕ α × Fin 3) K,
        (∃ x ∈ LinearMap.ker ((G.liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin,
          MvPolynomial.eval x ℓ ≠ 0) ∧
        ∀ x, MvPolynomial.eval x ℓ ≠ 0 → ∀ u ∈ V(G), ∀ w ∈ V(G), u ≠ w →
          planeDiff u w x ≠ 0 := by
  classical
  have hsep : ∀ p : α × α, ∃ P : MvPolynomial (α × Fin 2) K, P ≠ 0 ∧
      (p.1 ≠ p.2 → p.1 ∈ V(G) → p.2 ∈ V(G) → ∀ q, MvPolynomial.eval q P ≠ 0 →
        ∃ x ∈ LinearMap.ker ((G.liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin,
          planeDiff p.1 p.2 x ≠ 0) := by
    intro p
    by_cases hp : p.1 ≠ p.2 ∧ p.1 ∈ V(G) ∧ p.2 ∈ V(G)
    · obtain ⟨P, hP0, hP⟩ := exists_planes_separate (K := K) hSimple h3 hS hp.1 hp.2.1 hp.2.2
      exact ⟨P, hP0, fun _ _ _ => hP⟩
    · exact ⟨1, one_ne_zero, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hp⟩
  choose Psep hPsep0 hPsep using hsep
  refine ⟨∏ p, Psep p, Finset.prod_ne_zero_iff.mpr fun p _ => hPsep0 p, fun q hq => ?_⟩
  rw [map_prod] at hq
  have hq' := Finset.prod_ne_zero_iff.mp hq
  set Lk := LinearMap.ker ((G.liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin
  have hwit : ∀ p : α × α, ∃ ℓ : MvPolynomial (α ⊕ (α × Fin 3)) K,
      (∃ x ∈ Lk, MvPolynomial.eval x ℓ ≠ 0) ∧
      (p.1 ≠ p.2 → p.1 ∈ V(G) → p.2 ∈ V(G) → ∀ x, MvPolynomial.eval x ℓ ≠ 0 →
        planeDiff p.1 p.2 x ≠ 0) := by
    intro p
    by_cases hp : p.1 ≠ p.2 ∧ p.1 ∈ V(G) ∧ p.2 ∈ V(G)
    · obtain ⟨x, hx, hxd⟩ := hPsep p hp.1 hp.2.1 hp.2.2 q (hq' p (Finset.mem_univ _))
      obtain ⟨i, hi⟩ : ∃ i, planeDiff p.1 p.2 x i ≠ 0 := by
        by_contra hc
        push Not at hc
        exact hxd (funext hc)
      refine ⟨MvPolynomial.X (Sum.inr (p.1, i)) - MvPolynomial.X (Sum.inr (p.2, i)),
        ⟨x, hx, by simpa [planeDiff_apply] using hi⟩, fun _ _ _ y hy hd => hy ?_⟩
      have := congr_fun hd i
      simp only [planeDiff_apply, Pi.zero_apply] at this
      simp [this]
    · exact ⟨1, ⟨0, Lk.zero_mem, by simp⟩, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hp⟩
  choose ℓ hℓex hℓ using hwit
  obtain ⟨x, hxL, hxall⟩ := exists_mem_forall_eval_ne_zero (L := Lk) ℓ hℓex
  refine ⟨∏ p, ℓ p, ⟨x, hxL, by
    rw [map_prod]; exact Finset.prod_ne_zero_iff.mpr fun p _ => hxall p⟩,
    fun y hy u hu w hw huw => ?_⟩
  rw [map_prod] at hy
  exact hℓ (u, w) huw hu hw y (Finset.prod_ne_zero_iff.mp hy (u, w) (Finset.mem_univ _))

/-! ## A realization as a configuration -/

/-- **Points on one plane with the same picture points agree in their combinations**: if the
configuration points of `t i` are all orthogonal to `n` with `n₂ ≠ 0` (they lie on a plane that is
not vertical), a combination of their picture points that vanishes vanishes on the points. -/
theorem sum_smul_pencilConfigPoint_eq_zero {q : α × Fin 2 → K} {z : α → K} {n : Fin 4 → K}
    (hn2 : n 2 ≠ 0) {ι : Type*} [Fintype ι] {t : ι → α}
    (ht : ∀ i, pencilConfigPoint q z (t i) ⬝ᵥ n = 0) {a : ι → K}
    (ha : ∑ i, a i • pencilPicturePoint q (t i) = 0) :
    ∑ i, a i • pencilConfigPoint q z (t i) = 0 := by
  have h0 : ∑ i, a i * q (t i, 0) = 0 := by
    simpa [Finset.sum_apply, pencilPicturePoint] using congr_fun ha 0
  have h1 : ∑ i, a i * q (t i, 1) = 0 := by
    simpa [Finset.sum_apply, pencilPicturePoint] using congr_fun ha 1
  have h2 : ∑ i, a i = 0 := by
    simpa [Finset.sum_apply, pencilPicturePoint] using congr_fun ha 2
  have hz : ∑ i, a i * z (t i) = 0 := by
    have hsum : ∑ i, a i * (pencilConfigPoint q z (t i) ⬝ᵥ n) = 0 := by simp [ht]
    have e : ∑ i, a i * (pencilConfigPoint q z (t i) ⬝ᵥ n) = n 0 * ∑ i, a i * q (t i, 0) +
        n 1 * ∑ i, a i * q (t i, 1) + n 2 * ∑ i, a i * z (t i) + n 3 * ∑ i, a i := by
      simp only [dotProduct, Fin.sum_univ_four, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [pencilConfigPoint, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      simp
      ring
    rw [e, h0, h1, h2] at hsum
    simpa [hn2] using hsum
  funext j
  fin_cases j <;> simp [Finset.sum_apply, pencilConfigPoint, h0, h1, h2, hz]

/-- **A realization in dimension three as a configuration** (`lem:pencil-d-lift-no-rigid`, the
least lift space): let the points `b` and normals `n` have `b_w · n_v = 0` on every closed
neighbourhood, `b_v` of nonzero last coordinate and `n_v` of nonzero third coordinate at every body,
the points of adjacent bodies independent, and at every body three members of its closed
neighbourhood with independent points. Rescaled to last coordinate `1`, the points are those of a
configuration `(q', z')` over an admissible picture with `z' ∈ L(q')`, and `dim L̃` is unchanged
(`finrank_liftSpaceTilde_smul`). The Lean asks for the two nonzero coordinates, which hold at a
general realization. -/
theorem exists_pencilConfigPoint_of_dotProduct {G : Graph α β} {b n : α → Fin 4 → K}
    (hbn : ∀ v ∈ V(G), ∀ w ∈ G.closedNbhd v, b w ⬝ᵥ n v = 0)
    (hb3 : ∀ v ∈ V(G), b v 3 ≠ 0) (hn2 : ∀ v ∈ V(G), n v 2 ≠ 0)
    (hlink : ∀ u v, G.Adj u v → LinearIndependent K ![b u, b v])
    {sel : α → Fin 3 → α} (hsel : ∀ v ∈ V(G), (∀ i, sel v i ∈ G.closedNbhd v) ∧
      LinearIndependent K (fun i => b (sel v i))) :
    ∃ q' : α × Fin 2 → K, ∃ z' : α → K, G.IsAdmissiblePicture q' ∧ z' ∈ G.liftingSpace q' ∧
      Module.finrank K (liftSpaceTilde G (pencilConfigPoint q' z')) =
        Module.finrank K (liftSpaceTilde G b) := by
  classical
  set q' : α × Fin 2 → K := fun p => (b p.1 3)⁻¹ * b p.1 (![0, 1] p.2) with hq'
  set z' : α → K := fun w => if w ∈ V(G) then (b w 3)⁻¹ * b w 2 else 0 with hz'
  have hpt : ∀ w ∈ V(G), pencilConfigPoint q' z' w = (b w 3)⁻¹ • b w := by
    intro w hw
    funext i
    fin_cases i <;> simp [pencilConfigPoint, q', z', hw, inv_mul_cancel₀ (hb3 w hw)]
  have hpn : ∀ v ∈ V(G), ∀ w ∈ G.closedNbhd v, pencilConfigPoint q' z' w ⬝ᵥ n v = 0 := by
    intro v hv w hw
    rw [hpt w (Graph.closedNbhd_subset_vertexSet hv hw), smul_dotProduct, hbn v hv w hw, smul_zero]
  refine ⟨q', z', ⟨fun e u v he heq => ?_, fun v hv => ⟨sel v, (hsel v hv).1, ?_⟩⟩,
    ⟨fun w hw => by simp [z', hw], fun v hv => ?_⟩, ?_⟩
  · -- the two ends of a link have distinct picture points
    have hu := he.left_mem
    have hv := he.right_mem
    have key := sum_smul_pencilConfigPoint_eq_zero (q := q') (z := z') (hn2 u hu)
      (t := ![u, v]) (fun i => by
        fin_cases i
        · exact hpn u hu u (Or.inl rfl)
        · exact hpn u hu v (Or.inr ⟨e, he⟩))
      (a := ![1, -1]) (by simp [Fin.sum_univ_two, heq])
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      one_smul, neg_smul, ← sub_eq_add_neg, sub_eq_zero, hpt u hu, hpt v hv] at key
    have := (LinearIndependent.pair_iff.1 (hlink u v ⟨e, he⟩)) (b u 3)⁻¹ (-(b v 3)⁻¹)
      (by rw [neg_smul, key, add_neg_cancel])
    exact inv_ne_zero (hb3 u hu) this.1
  · -- three members of a closed neighbourhood with independent picture points
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have key := sum_smul_pencilConfigPoint_eq_zero (q := q') (z := z') (hn2 v hv)
      (t := sel v) (fun i => hpn v hv _ ((hsel v hv).1 i)) hg
    have hsV : ∀ i, sel v i ∈ V(G) := fun i =>
      Graph.closedNbhd_subset_vertexSet hv ((hsel v hv).1 i)
    simp only [hpt _ (hsV _), smul_smul] at key
    intro i
    have := Fintype.linearIndependent_iff.1 (hsel v hv).2 _ key i
    exact (mul_eq_zero.1 this).resolve_right (inv_ne_zero (hb3 _ (hsV i)))
  · -- `z'` is affine on every closed neighbourhood
    refine ⟨fun j => -(n v 2)⁻¹ * n v (![0, 1, 3] j), fun w hw => ?_⟩
    have hwV := Graph.closedNbhd_subset_vertexSet hv hw
    have e := hpn v hv w hw
    rw [hpt w hwV] at e
    simp only [smul_dotProduct, smul_eq_mul, mul_eq_zero, inv_eq_zero, hb3 w hwV, false_or] at e
    simp only [dotProduct, Fin.sum_univ_four, Fin.sum_univ_three] at e ⊢
    simp only [z', q', pencilPicturePoint, ite_eq_left hwV]
    have h2 := hn2 v hv
    have h3 := hb3 w hwV
    simp
    field_simp
    linear_combination e
  · exact finrank_liftSpaceTilde_smul (c := fun v => (b v 3)⁻¹)
      (fun v hv => inv_ne_zero (hb3 v hv)) hpt

/-! ## Without a planar-rigid set -/

/-- **The lift of a configuration by its other heights** (`lem:pencil-d-lift-no-rigid`): the lift
of the configuration `(q, z⁰)` in dimension three by the columns `z¹, …, z^r` has the points of the
configuration `(q, z)` with `r + 1` heights. -/
theorem liftNormal_pencilConfigPoint {r : ℕ} (q : α × Fin 2 → K) (z : α × Fin (r + 1) → K)
    (w : α) :
    liftNormal (pencilConfigPoint q fun v => z (v, 0)) (fun i v => z (v, i.succ)) w =
      pencilConfigPointGrade q z w :=
  gradeMk_ext rfl rfl (Fin.cons_self_tail fun i => z (w, i)) rfl

/-- **The general lift attains without a planar-rigid set** (`lem:pencil-d-lift-no-rigid`): let `K`
be infinite and `d = r + 3`, and let `G` satisfy the standing hypotheses, be
nondegeneracy-feasible and have `def₂(G[Y]) ≠ 0` for every set `Y` of at least two bodies. If the
general configuration of `G` attains in dimension `d`, then the general lift of `G` attains in
dimension `d`.

Proof. A picture `q` off the zero sets of the attaining polynomial, the main-picture polynomial
(`Graph.exists_mvPolynomial_isMainPicture`), the determinants of every three distinct bodies
(`exists_det_poly`) and the planes polynomial (`exists_planeDiff_ne_zero_poly`). One point of the
space of the heights `z ∈ L(q)^{r+1}` and the planes of their first column makes the attaining
polynomial and the planes polynomial nonzero (`MvPolynomial.exists_mem_eval_ne_zero₂`). The
configuration `(q, z⁰)` is then nondegenerate (`isNondeg_pencilConfig_of_planeDiff`), and its lift
by the other columns is the configuration `(q, z)` (`mem_liftMaps_pencilConfigPoint_iff`,
`liftNormal_pencilConfigPoint`), of the deficiency rank. `dim L̃` is least there: a general
nondegenerate realization has `dim L̃` least (`exists_holdsGenerally_finrank_liftSpaceTilde_le`),
points of nonzero last coordinate, normals of nonzero third coordinate and three independent points
in every closed neighbourhood, so it is a configuration over an admissible picture `q'`
(`exists_pencilConfigPoint_of_dotProduct`), and `dim L(q) ≤ dim L(q')` as `q` is a main picture
(`finrank_liftSpaceTilde_pencilConfigPoint`). `liftAttains_of_least` concludes. -/
theorem liftAttains_of_forall_deficiency_two_ne_zero [Infinite K] [Finite α] [Finite β] (r : ℕ)
    {G : Graph α β} (hG : G.IsX0Graph) (hfeas : PencilNondegFeasible K G)
    (hrig : ∀ Y ⊆ V(G), 2 ≤ Y.ncard → (G.induce Y).deficiency 2 ≠ 0)
    (hatt : G.X0AttainsGrade K (r + 1)) :
    LiftAttains K r G := by
  classical
  have := Fintype.ofFinite α
  have : G.Simple := hG.simple
  obtain ⟨hF1, -⟩ := hfeas.hub_conditions
  obtain ⟨ends, Patt, hends, hPatt0, hPatt⟩ := hatt
  have h3 := hG.three_le_ncard_closedNbhd
  obtain ⟨Pm, hPm0, hPm⟩ := G.exists_mvPolynomial_isMainPicture (K := K) hG.simple.toLoopless h3
  obtain ⟨Ppl, hPpl0, hPpl⟩ := exists_planeDiff_ne_zero_poly (K := K) hG.simple h3 hrig
  -- general position at every triple of distinct bodies
  have hgpP : ∀ t : α × α × α, ∃ D : MvPolynomial (α × Fin 2) K, D ≠ 0 ∧
      (t.1 ≠ t.2.1 → t.1 ≠ t.2.2 → t.2.1 ≠ t.2.2 → ∀ q, MvPolynomial.eval q D ≠ 0 →
        LinearIndependent K ![pencilPicturePoint q t.1, pencilPicturePoint q t.2.1,
          pencilPicturePoint q t.2.2]) := by
    intro t
    by_cases ht : t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2
    · obtain ⟨D, hD0, hD⟩ := exists_det_poly (K := K) t.1 t.2.1 t.2.2 ht.1 ht.2.1 ht.2.2
      exact ⟨D, hD0, fun _ _ _ => hD⟩
    · exact ⟨1, one_ne_zero, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ ht⟩
  choose Dgp hDgp0 hDgp using hgpP
  set Q : MvPolynomial (α × Fin 2) K := Patt * Pm * Ppl * ∏ t, Dgp t with hQdef
  have hQ0 : Q ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero hPatt0 hPm0) hPpl0)
    (Finset.prod_ne_zero_iff.mpr fun t _ => hDgp0 t)
  obtain ⟨q, hq⟩ := MvPolynomial.exists_eval_ne_zero hQ0
  rw [hQdef, map_mul, map_mul, map_mul, map_prod] at hq
  have hqatt := left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hq))
  have hqm := right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hq))
  have hqpl := right_ne_zero_of_mul (left_ne_zero_of_mul hq)
  have hqgp := Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hq)
  obtain ⟨hadm, R, ⟨z₀, hz₀, hRz₀⟩, hrank⟩ := hPatt q hqatt
  have hmain := hPm q hqm
  obtain ⟨ℓ, ⟨x₁, hx₁, hℓx₁⟩, hℓ⟩ := hPpl q hqpl
  set Lk := LinearMap.ker ((G.liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin with hLk
  -- the heights and the planes of their first column, in one space
  set col : α ⊕ α × Fin 3 → (α × Fin (r + 1)) ⊕ (α × Fin 3) :=
    Sum.elim (fun w => Sum.inl (w, 0)) Sum.inr with hcol
  set S : Submodule K ((α × Fin (r + 1)) ⊕ (α × Fin 3) → K) :=
    (G.liftingSpaceGrade q (r + 1)).comap (LinearMap.funLeft K K Sum.inl) ⊓
      Lk.comap (LinearMap.funLeft K K col) with hSdef
  have hSR : ∃ X ∈ S, MvPolynomial.eval X (MvPolynomial.rename Sum.inl R) ≠ 0 := by
    have hcol0 : (fun w => z₀ (w, 0)) ∈ G.liftingSpace q := Graph.mem_liftingSpaceGrade.1 hz₀ 0
    rw [← G.map_ker_liftingMatrix q] at hcol0
    obtain ⟨x₀, hx₀, hx₀e⟩ := hcol0
    refine ⟨Sum.elim z₀ (fun p => x₀ (Sum.inr p)), Submodule.mem_inf.2 ⟨hz₀, ?_⟩, ?_⟩
    · have e : (fun c => Sum.elim z₀ (fun p => x₀ (Sum.inr p)) (col c)) = x₀ := by
        funext c
        rcases c with w | p
        · exact (congr_fun hx₀e w).symm
        · rfl
      change (fun c => Sum.elim z₀ (fun p => x₀ (Sum.inr p)) (col c)) ∈ Lk
      rw [e]; exact hx₀
    · rw [MvPolynomial.eval_rename]; exact hRz₀
  have hSℓ : ∃ X ∈ S, MvPolynomial.eval X (MvPolynomial.rename col ℓ) ≠ 0 := by
    have e : (fun c => Sum.elim (fun p : α × Fin (r + 1) => if p.2 = 0 then x₁ (Sum.inl p.1) else 0)
        (fun p => x₁ (Sum.inr p)) (col c)) = x₁ := by
      funext c
      rcases c with w | p <;> simp [col]
    refine ⟨Sum.elim (fun p => if p.2 = 0 then x₁ (Sum.inl p.1) else 0) (fun p => x₁ (Sum.inr p)),
      Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
    · rw [Submodule.mem_comap, Graph.mem_liftingSpaceGrade]
      intro i
      by_cases hi : i = 0
      · subst hi
        rw [← G.map_ker_liftingMatrix q]
        exact ⟨x₁, hx₁, rfl⟩
      · have e : (fun w => (LinearMap.funLeft K K Sum.inl) (Sum.elim
            (fun p : α × Fin (r + 1) => if p.2 = 0 then x₁ (Sum.inl p.1) else 0)
            (fun p => x₁ (Sum.inr p))) (w, i)) = 0 := funext fun w => by simp [hi]
        rw [e]; exact zero_mem _
    · change (fun c => Sum.elim (fun p : α × Fin (r + 1) => if p.2 = 0 then x₁ (Sum.inl p.1) else 0)
        (fun p => x₁ (Sum.inr p)) (col c)) ∈ Lk
      rw [e]; exact hx₁
    · rw [MvPolynomial.eval_rename]
      change MvPolynomial.eval (fun c => Sum.elim
        (fun p : α × Fin (r + 1) => if p.2 = 0 then x₁ (Sum.inl p.1) else 0)
        (fun p => x₁ (Sum.inr p)) (col c)) ℓ ≠ 0
      rw [e]; exact hℓx₁
  obtain ⟨X, ⟨hXz, hXx⟩, hXR, hXℓ⟩ := MvPolynomial.exists_mem_eval_ne_zero₂ hSR hSℓ
  rw [MvPolynomial.eval_rename] at hXR hXℓ
  set z : α × Fin (r + 1) → K := X ∘ Sum.inl with hzdef
  set x : α ⊕ α × Fin 3 → K := X ∘ col with hxdef
  have hz : z ∈ G.liftingSpaceGrade q (r + 1) := hXz
  have hx : x ∈ Lk := hXx
  have hpd := hℓ x hXℓ
  have hz0 : (fun v => z (v, 0)) ∈ G.liftingSpace q := by
    rw [← G.map_ker_liftingMatrix q]; exact ⟨x, hx, rfl⟩
  -- the configuration `(q, z⁰)` is nondegenerate
  let sel : α → Fin 3 → α := fun v => if hv : v ∈ V(G) then (hadm.2 v hv).choose else fun _ => v
  have hsel : ∀ v ∈ V(G), (∀ i, sel v i ∈ G.closedNbhd v) ∧
      LinearIndependent K (fun i => pencilPicturePoint q (sel v i)) := by
    intro v hv
    simp only [sel, hv, ↓reduceDIte]
    exact (hadm.2 v hv).choose_spec
  have hnd3 := isNondeg_pencilConfig_of_planeDiff (K := K) hF1 hadm
    (fun v w₁ w₂ _ _ _ h1 h2 h12 => hDgp (v, w₁, w₂) (Ne.symm h1) (Ne.symm h2) h12 q
      (hqgp _ (Finset.mem_univ _)))
    hx (fun e a b hl _ _ => hpd a hl.left_mem b hl.right_mem hl.ne)
    (fun v hv _ a ha b hb hab => hpd a ha.1.1 b hb.1.1 hab) hends hsel
  have hnd := hnd3.toPlane
  set b : α → Fin 4 → K := pencilConfigPoint q fun v => z (v, 0) with hbdef
  set P : α → Submodule K (Fin 4 → K) :=
    fun v => dotPerp (K ∙ pencilNormalOfPicture q (fun v => z (v, 0)) sel v) with hPdef
  -- its lift by the other heights has the deficiency rank
  have hP : ∀ v ∈ V(G), ∀ w ∈ G.closedNbhd v, b w ∈ P v := fun v hv w hw =>
    hnd.1.normal_mem_plane_of_mem_closedNbhd hv hw
  have hcols : ∀ i : Fin r, (fun w => z (w, i.succ)) ∈ liftMaps G b P := fun i =>
    (mem_liftMaps_pencilConfigPoint_iff hz0 hP).2 fun v hv =>
      (Graph.mem_liftingSpaceGrade.1 hz i.succ).2 v hv
  choose lam hlam hlam1 using fun i => Submodule.mem_map.1 (hcols i)
  have hlam1' : (fun i => (lam i).1) = fun i w => z (w, i.succ) := funext fun i => hlam1 i
  have hrk : (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := r + 1 + 1) G
      ends (fun p => liftNormal b (fun i => (lam i).1) p.1 p.2)).toBodyHinge.rigidityRows) : ℤ)
      = screwDim (r + 1 + 1) * ((V(G).ncard : ℤ) - 1) - G.deficiency (r + 1 + 2) := by
    have e : (fun p : α × Fin (r + 1 + 1 + 2) => liftNormal b (fun i w => z (w, i.succ)) p.1 p.2) =
        fun p => pencilConfigPointGrade q z p.1 p.2 :=
      funext fun p => congrFun (liftNormal_pencilConfigPoint q z p.1) p.2
    rw [hlam1', e]
    exact hrank z hz hXR
  -- `dim L̃` is least at `b`
  obtain ⟨hubSel, nbrSel, hHubSel, hNbrSel⟩ := exists_steer_selectors hfeas
  obtain ⟨N, hN, hgen⟩ := exists_holdsGenerally_finrank_liftSpaceTilde_le hHubSel hNbrSel hfeas
  obtain ⟨s₀, hs₀, hs₀pt, hs₀pl⟩ := exists_mem_steerSet_of_isNondeg hHubSel hNbrSel hnd
  choose! c hc hceq using hs₀pt
  have hs₀U := (mem_steerSet_iff hHubSel hNbrSel).1 hs₀
  have hselV : ∀ v ∈ V(G), ∀ i, sel v i ∈ V(G) := fun v hv i =>
    Graph.closedNbhd_subset_vertexSet hv ((hsel v hv).1 i)
  have hgen2 : HoldsGenerally G hubSel nbrSel fun b0 P0 => ∀ v ∈ V(G), b0 v 3 ≠ 0 ∧
      (Pi.single 2 1 : Fin 4 → K) ∉ P0 v ∧ LinearIndependent K fun i => b0 (sel v i) := by
    refine HoldsGenerally.of_isZariskiOpen (S := {s | ∀ v, v ∈ V(G) →
      steerPoint hubSel s v 3 ≠ 0 ∧ steerNormal hubSel nbrSel G s v 2 ≠ 0 ∧
        LinearIndependent K fun i => steerPoint hubSel s (sel v i)}) ?_ hs₀ ?_ ?_
    · exact isZariskiOpen_forall fun v => isZariskiOpen_imp _ <|
        (isZariskiOpen_ne_zero_of_isPolyFun (isPolyFun_steerPoint hubSel v 3)).and <|
        (isZariskiOpen_ne_zero_of_isPolyFun (isPolyFun_steerNormal hubSel nbrSel G v 2)).and <|
        isZariskiOpen_linearIndependent_univ (fun s i => steerPoint hubSel s (sel v i))
          fun i j => isPolyFun_steerPoint hubSel (sel v i) j
    · intro v hv
      refine ⟨by simp [hceq v hv, pencilConfigPoint, hc v hv], fun h2 => ?_, ?_⟩
      · -- the normal at `s₀` is not horizontal: it would vanish on three independent picture points
        have hm : ![steerNormal hubSel nbrSel G s₀ v 0, steerNormal hubSel nbrSel G s₀ v 1,
            steerNormal hubSel nbrSel G s₀ v 3] = 0 := by
          refine (hsel v hv).2.eq_zero_of_forall_dotProduct_eq_zero fun i => ?_
          have h := steerPoint_dotProduct_steerNormal hHubSel hNbrSel s₀ ((hsel v hv).1 i)
          rw [hceq _ (hselV v hv i), smul_dotProduct, smul_eq_mul, mul_eq_zero] at h
          have h' := h.resolve_left (hc _ (hselV v hv i))
          simp only [dotProduct, Fin.sum_univ_four, pencilConfigPoint, h2] at h'
          simp [dotProduct, Fin.sum_univ_three, pencilPicturePoint]
          simp at h'
          linear_combination h'
        apply hs₀U.2.1 v hv
        funext j
        fin_cases j
        · exact congr_fun hm 0
        · exact congr_fun hm 1
        · exact h2
        · exact congr_fun hm 2
      · have e : (fun i => steerPoint hubSel s₀ (sel v i)) =
            fun i => (Units.mk0 _ (hc _ (hselV v hv i))) • b (sel v i) := funext fun i => by
          rw [hceq _ (hselV v hv i)]; rfl
        rw [e]
        exact (linearIndependent_pencilConfigPoint_of_linearIndependent_pencilPicturePoint _
          (hsel v hv).2).units_smul _
    · intro s _ hsS v hv
      obtain ⟨h1, h2, h3⟩ := hsS v hv
      refine ⟨h1, fun hmem => h2 ?_, h3⟩
      rwa [mem_dotPerp_span_singleton, single_dotProduct, one_mul] at hmem
  obtain ⟨R', ⟨s, hsU, hsR'⟩, hR'⟩ := HoldsGenerally.and hHubSel hNbrSel hgen hgen2
  obtain ⟨hsN, hs2⟩ := hR' s hsU hsR'
  obtain ⟨-, -, hadj, -, -⟩ := (mem_steerSet_iff hHubSel hNbrSel).1 hsU
  obtain ⟨q', z', hadm', hz', hfr'⟩ := exists_pencilConfigPoint_of_dotProduct
    (n := steerNormal hubSel nbrSel G s)
    (fun v _ w hw => steerPoint_dotProduct_steerNormal hHubSel hNbrSel s hw)
    (fun v hv => (hs2 v hv).1)
    (fun v hv h0 => (hs2 v hv).2.1 (by
      rw [mem_dotPerp_span_singleton, single_dotProduct, one_mul]; exact h0))
    hadj (sel := sel) fun v hv => ⟨(hsel v hv).1, (hs2 v hv).2.2⟩
  have hleast : ∀ (F' : BodyHingeFramework K 2 α β) (b' : α → Fin 4 → K)
      (P' : α → Submodule K (Fin 4 → K)), IsNondegPencilPlaneRealization G F' b' P' →
      Module.finrank K (liftSpaceTilde G b) ≤ Module.finrank K (liftSpaceTilde G b') := by
    intro F' b' P' hnd'
    refine le_trans ?_ (hN F' b' P' hnd')
    refine le_trans ?_ hsN
    rw [← hfr', hbdef, finrank_liftSpaceTilde_pencilConfigPoint hadm hz0,
      finrank_liftSpaceTilde_pencilConfigPoint hadm' hz']
    exact Nat.add_le_add_right (hmain.2 q' hadm') _
  exact liftAttains_of_least hnd hleast hlam hends hrk

end CombinatorialRigidity.Molecular
