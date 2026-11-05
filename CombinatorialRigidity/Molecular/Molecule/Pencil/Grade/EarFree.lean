/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.LiftNoRigid
public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.GoodEar

/-!
# Extending the points of the rigid set

`lem:pencil-d-ear-extend` of `blueprint/src/chapter/pencil-d.tex`, `sec:pencil-d-generic`
(`exists_earExtend_poly`): at the good ear `W₀`, `x` of `lem:pencil-d-good-ear`, with
`X = W₀ \ {x}`, the points `b_v(t)` of `X` read from the hubs of `G` in `X` alone (a selector
`hubSelL` of `H_L[v]`, `Γ_L` read inside `Γ(G)`'s parameter type) are, off the zero set of a
nonzero polynomial `E_L`, nonzero multiples of the points `b⁰_v(s)` of some `s ∈ Γ(G)`.

* The polynomial (`exists_earExtend_cond_poly`): conditions (a) `b_v(t) ≠ 0` and (b)
  `b_v(t) · m_u ≠ 0` for `u` off the selector of `v`, each open and witnessed where its slots
  (and `m_u`) are the standard basis (`exists_gamma_eq_of_injective`, `hubSlotPos`); `E_L` is the
  product of one polynomial per condition.
* The extension: the normals `n_u` of the hubs outside `W₀` are chosen in
  `A_u = {b_w : w ∈ X, w ~ u}^⊥`, one closed hub-neighbourhood at a time
  (`exists_linearIndepOn_of_finrank`): each `A_u` has dimension at least three, or at least two
  and misses `m_v` by (b), as a second neighbour of `u` in `X` is not adjacent to `v`. One point of
  `∏ A_u` serves every `v ∈ X` (`exists_mem_forall_eval_ne_zero`), and the auxiliary vectors of `v`
  complete the independent normals of its closed hub-neighbourhood, orthogonal to `b_v(t)`, to a
  triple whose `cross₃` is a nonzero multiple of it (`exists_fill_cross₃_eq_smul_of_selector`).
-/

@[expose] public section

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

/-! ## The places of the chart's slots -/

/-- The dot product of vectors with polynomial coordinates is a polynomial. -/
theorem isPolyFun_dotProduct {σ : Type*} {n : ℕ} {f g : (σ → K) → Fin n → K}
    (hf : ∀ i, IsPolyFun fun s => f s i) (hg : ∀ i, IsPolyFun fun s => g s i) :
    IsPolyFun fun s => f s ⬝ᵥ g s := by
  choose F hF using hf
  choose G hG using hg
  exact ⟨∑ i, F i * G i, fun s => by simp [dotProduct, hF, hG]⟩

/-- The coordinates of slot `i` of a selector `sel` at `v` in `Γ(G)`: `(w, 0)` for the body `w` in
it, and `(v, i + 1)` at an empty slot. -/
def hubSlotPos (sel : Fin 3 → Option α) (v : α) (i : Fin 3) : α × Fin 7 :=
  match sel i with
  | some w => (w, 0)
  | none => (v, ⟨i + 1, by omega⟩)

/-- Slot `i` of the chart at `s ∈ Γ(G)` is the vector of `s` at the place `hubSlotPos`. -/
theorem hubSlotNormal_ofGamma (s : α × Fin 7 × Fin 4 → K) (hubSel : α → Fin 3 → Option α)
    (v : α) (i : Fin 3) :
    hubSlotNormal (PencilSeed.ofGamma s) hubSel v i =
      fun k => s ((hubSlotPos (hubSel v) v i).1, (hubSlotPos (hubSel v) v i).2, k) := by
  unfold hubSlotNormal hubSlotPos
  rcases hubSel v i with _ | w <;> rfl

/-- A selector puts no body in two slots, so its slots have distinct places. -/
theorem hubSlotPos_injective {s : Set α} {sel : Fin 3 → Option α} (hsel : IsFin3SelectorOf s sel)
    (v : α) : Function.Injective (hubSlotPos sel v) := by
  intro i j hij
  unfold hubSlotPos at hij
  rcases hi : sel i with _ | w <;> rcases hj : sel j with _ | w' <;> simp only [hi, hj] at hij
  · exact Fin.ext (by simpa using congrArg (fun p : α × Fin 7 => (p.2 : ℕ)) hij)
  · exact absurd (congrArg (fun p : α × Fin 7 => (p.2 : ℕ)) hij) (by simp)
  · exact absurd (congrArg (fun p : α × Fin 7 => (p.2 : ℕ)) hij) (by simp)
  · obtain rfl : w = w' := congrArg Prod.fst hij
    exact hsel.2.2 i j w hi hj

/-- The place `(u, 0)` of a body `u` that the selector does not list is none of its slots'. -/
theorem hubSlotPos_ne_of_notMem {s : Set α} {sel : Fin 3 → Option α} (hsel : IsFin3SelectorOf s sel)
    {u : α} (hu : u ∉ s) (v : α) (i : Fin 3) : hubSlotPos sel v i ≠ (u, 0) := by
  unfold hubSlotPos
  rcases hi : sel i with _ | w
  · intro h
    exact absurd (congrArg (fun p : α × Fin 7 => (p.2 : ℕ)) h) (by simp)
  · intro h
    obtain rfl : w = u := congrArg Prod.fst h
    exact hu (hsel.1 i w hi)

/-- **Parameters with given vectors at distinct places**: the places of `Γ(G)` are free
coordinates, so any vectors can be put at distinct ones. -/
theorem exists_gamma_eq_of_injective {ι : Type*} {p : ι → α × Fin 7} (hp : Function.Injective p)
    (w : ι → Fin 4 → K) : ∃ t : α × Fin 7 × Fin 4 → K, ∀ i k, t ((p i).1, (p i).2, k) = w i k := by
  classical
  refine ⟨fun c => if h : ∃ i, p i = (c.1, c.2.1) then w h.choose c.2.2 else 0, fun i k => ?_⟩
  have h : ∃ j, p j = ((p i).1, (p i).2) := ⟨i, rfl⟩
  simp only [h, ↓reduceDIte]
  rw [hp h.choose_spec]

/-- `cross₃ e₀ e₁ e₂ · e₃ = det 1 = 1`. -/
theorem cross₃_single_dotProduct_single :
    cross₃ (Pi.single 0 1) (Pi.single 1 1) (Pi.single 2 1) ⬝ᵥ (Pi.single 3 1 : Fin 4 → K) = 1 := by
  rw [dotProduct_cross₃]
  have : Matrix.of ![Pi.single 0 1, Pi.single 1 1, Pi.single 2 1, (Pi.single 3 1 : Fin 4 → K)] =
      1 := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  rw [this, Matrix.det_one]

/-! ## The chart at any selector -/

/-- **The point of the chart is orthogonal to the hub normals its selector lists**, for a selector
of any set (`dotProduct_pencilChartPoint_hubNormal_of_mem_closedHubNbhd` at the closed
hub-neighbourhood). -/
theorem dotProduct_pencilChartPoint_hubNormal_of_selector {s : Set α} {v w : α}
    (seed : PencilSeed K α) {hubSel : α → Fin 3 → Option α}
    (hSel : IsFin3SelectorOf s (hubSel v)) (hw : w ∈ s) :
    pencilChartPoint seed hubSel v ⬝ᵥ seed.hubNormal w = 0 := by
  obtain ⟨i, hi⟩ := hSel.2.1 w hw
  have hslot : hubSlotNormal seed hubSel v i = seed.hubNormal w := by
    simp [hubSlotNormal, hi]
  rw [pencilChartPoint, ← hslot]
  exact cross₃_dotProduct_apply_self (hubSlotNormal seed hubSel v) i

/-- **A nonzero point of the chart makes the hub normals its selector lists independent**: its
three slots are independent (`cross₃_ne_zero_iff_linearIndependent`), and the filled ones are the
members of the set, one each (`IsFin3SelectorOf.exists_equiv_isSome`). -/
theorem linearIndepOn_hubNormal_of_selector {s : Set α} {v : α}
    (seed : PencilSeed K α) {hubSel : α → Fin 3 → Option α}
    (hSel : IsFin3SelectorOf s (hubSel v)) (hne : pencilChartPoint seed hubSel v ≠ 0) :
    LinearIndepOn K seed.hubNormal s := by
  have hLI := (cross₃_ne_zero_iff_linearIndependent _ _ _).mp hne
  obtain ⟨e, he⟩ := hSel.exists_equiv_isSome
  refine (linearIndependent_equiv' e ?_).mp
    (((linearIndependent_hubSlotNormal_iff seed hubSel v).mp hLI).comp _ Subtype.val_injective)
  funext i
  simp only [Function.comp_apply, hubSlotNormal, he i]

/-! ## `lem:pencil-d-ear-extend` -/

/-- **A vector of `A` off `S`**, for `dim S ≤ 2`, when `dim A ≥ 3`, or `dim A ≥ 2` and `A` misses a
vector of `S`: otherwise `A ≤ S`, so `A = S` by dimension. -/
theorem exists_mem_notMem_of_finrank {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {A S : Submodule K V} (hS : Module.finrank K S ≤ 2)
    (h : 3 ≤ Module.finrank K A ∨ (2 ≤ Module.finrank K A ∧ ∃ m ∈ S, m ∉ A)) :
    ∃ y ∈ A, y ∉ S := by
  by_contra hc
  push Not at hc
  have hle : A ≤ S := fun y hy => hc y hy
  have hfr := Submodule.finrank_mono hle
  rcases h with h | ⟨h, m, hmS, hmA⟩
  · omega
  · have := Submodule.eq_of_le_of_finrank_eq hle (by omega)
    exact hmA (this ▸ hmS)

/-- **The polynomial `E_L`** (a step of `lem:pencil-d-ear-extend`, conditions (a) and (b)): off its
zero set every chart point `b_v(t)`, `v ∈ X`, is nonzero, and has nonzero dot product with `m_u`
for every `u` its selector does not list. Each condition is open and holds where the vectors of
its slots (and `m_u`) are the standard basis. -/
theorem exists_earExtend_cond_poly [Infinite K] [Finite α] {X : Set α} {H : α → Set α}
    {hubSelL : α → Fin 3 → Option α} (hL : ∀ v ∈ X, IsFin3SelectorOf (H v) (hubSelL v)) :
    ∃ E : MvPolynomial (α × Fin 7 × Fin 4) K, (∃ t, MvPolynomial.eval t E ≠ 0) ∧
      ∀ t, MvPolynomial.eval t E ≠ 0 → (∀ v ∈ X, steerPoint hubSelL t v ≠ 0) ∧
        ∀ v ∈ X, ∀ u, u ∉ H v → steerPoint hubSelL t v ⬝ᵥ (fun k => t (u, 0, k)) ≠ 0 := by
  classical
  have := Fintype.ofFinite α
  have hpt : ∀ (t : α × Fin 7 × Fin 4 → K) v, (∀ i k, t ((hubSlotPos (hubSelL v) v i).1,
      (hubSlotPos (hubSelL v) v i).2, k) = (Pi.single (Fin.castSucc i) 1 : Fin 4 → K) k) →
      steerPoint hubSelL t v = cross₃ (Pi.single 0 1) (Pi.single 1 1) (Pi.single 2 1) := by
    intro t v ht
    have hslot : ∀ i, hubSlotNormal (PencilSeed.ofGamma t) hubSelL v i =
        Pi.single (Fin.castSucc i) 1 := fun i => by
      rw [hubSlotNormal_ofGamma]; funext k; exact ht i k
    rw [steerPoint, pencilChartPoint, hslot, hslot, hslot]
    rfl
  have hA : ∀ v : α, ∃ R : MvPolynomial (α × Fin 7 × Fin 4) K, R ≠ 0 ∧
      ∀ t, MvPolynomial.eval t R ≠ 0 → v ∈ X → steerPoint hubSelL t v ≠ 0 := by
    intro v
    by_cases hv : v ∈ X
    · obtain ⟨t₀, ht₀⟩ := exists_gamma_eq_of_injective (hubSlotPos_injective (hL v hv) v)
        (fun i => (Pi.single (Fin.castSucc i) 1 : Fin 4 → K))
      have hne : steerPoint hubSelL t₀ v ≠ 0 := by
        intro h0
        have h1 := cross₃_single_dotProduct_single (K := K)
        rw [← hpt t₀ v ht₀, h0, zero_dotProduct] at h1
        exact zero_ne_one h1
      obtain ⟨R, hR0, hR⟩ := isZariskiOpen_ne_zero (fun t => steerPoint hubSelL t v)
        (isPolyFun_steerPoint hubSelL v) t₀ hne
      exact ⟨R, fun h => hR0 (by rw [h, map_zero]), fun t ht _ => hR t ht⟩
    · exact ⟨1, one_ne_zero, fun _ _ h => absurd h hv⟩
  have hB : ∀ p : α × α, ∃ R : MvPolynomial (α × Fin 7 × Fin 4) K, R ≠ 0 ∧
      ∀ t, MvPolynomial.eval t R ≠ 0 → p.1 ∈ X → p.2 ∉ H p.1 →
        steerPoint hubSelL t p.1 ⬝ᵥ (fun k => t (p.2, 0, k)) ≠ 0 := by
    rintro ⟨v, u⟩
    by_cases hvu : v ∈ X ∧ u ∉ H v
    · set pos : Option (Fin 3) → α × Fin 7 := fun o => o.elim (u, 0) (hubSlotPos (hubSelL v) v)
      have hinj : Function.Injective pos := by
        rintro (_ | i) (_ | j) h
        · rfl
        · exact absurd h.symm (hubSlotPos_ne_of_notMem (hL v hvu.1) hvu.2 v j)
        · exact absurd h (hubSlotPos_ne_of_notMem (hL v hvu.1) hvu.2 v i)
        · exact congrArg some (hubSlotPos_injective (hL v hvu.1) v h)
      obtain ⟨t₀, ht₀⟩ := exists_gamma_eq_of_injective hinj
        (fun o => o.elim (Pi.single 3 1) (fun i => (Pi.single (Fin.castSucc i) 1 : Fin 4 → K)))
      have hne : steerPoint hubSelL t₀ v ⬝ᵥ (fun k => t₀ (u, 0, k)) ≠ 0 := by
        rw [hpt t₀ v (fun i k => ht₀ (some i) k)]
        have hu : (fun k => t₀ (u, 0, k)) = Pi.single 3 1 := funext fun k => ht₀ none k
        rw [hu, cross₃_single_dotProduct_single]
        exact one_ne_zero
      have hpoly : IsPolyFun fun t : α × Fin 7 × Fin 4 → K =>
          steerPoint hubSelL t v ⬝ᵥ (fun k => t (u, 0, k)) :=
        isPolyFun_dotProduct (isPolyFun_steerPoint hubSelL v) (fun k => isPolyFun_apply _)
      obtain ⟨R, hR0, hR⟩ := isZariskiOpen_ne_zero_of_isPolyFun hpoly t₀ hne
      exact ⟨R, fun h => hR0 (by rw [h, map_zero]), fun t ht _ _ => hR t ht⟩
    · exact ⟨1, one_ne_zero, fun _ _ h1 h2 => absurd ⟨h1, h2⟩ hvu⟩
  choose RA hRA0 hRA using hA
  choose RB hRB0 hRB using hB
  have hE0 : (∏ v, RA v) * ∏ p, RB p ≠ 0 := mul_ne_zero
    (Finset.prod_ne_zero_iff.2 fun v _ => hRA0 v) (Finset.prod_ne_zero_iff.2 fun p _ => hRB0 p)
  refine ⟨(∏ v, RA v) * ∏ p, RB p, MvPolynomial.exists_eval_ne_zero hE0, fun t ht => ?_⟩
  rw [map_mul, map_prod, map_prod] at ht
  have hta := Finset.prod_ne_zero_iff.1 (left_ne_zero_of_mul ht)
  have htb := Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul ht)
  exact ⟨fun v hv => hRA v t (hta v (Finset.mem_univ _)) hv,
    fun v hv u hu => hRB (v, u) t (htb _ (Finset.mem_univ _)) hv hu⟩

/-- **Choosing the normals outside, one at a time** (a step of `lem:pencil-d-ear-extend`, the
extension): let `C` have at most three members, `m` be independent on `C ∩ X`, and each
`u ∈ C \ X` have a subspace `A_u` of dimension at least three, or of dimension at least two missing
`m_v` for some `v ∈ C ∩ X`. Then some `n` with `n_u ∈ A_u` at every `u` makes `m` on `X`, `n` off
it, independent on `C`. -/
theorem exists_linearIndepOn_of_finrank [Finite α] {C X : Set α} [DecidablePred (· ∈ X)]
    {m : α → Fin 4 → K}
    {Au : α → Submodule K (Fin 4 → K)} {v : α} (hC : C.ncard ≤ 3)
    (hm : LinearIndepOn K m (C ∩ X))
    (hAu : ∀ u ∈ C \ X, 3 ≤ Module.finrank K (Au u) ∨
      (2 ≤ Module.finrank K (Au u) ∧ v ∈ C ∩ X ∧ m v ∉ Au u)) :
    ∃ n ∈ (⨅ u, (Au u).comap (LinearMap.funLeft K K (Prod.mk u)) :
        Submodule K (α × Fin 4 → K)),
      LinearIndepOn K (fun h => if h ∈ X then m h else fun k => n (h, k)) C := by
  classical
  set A : Submodule K (α × Fin 4 → K) := ⨅ u, (Au u).comap (LinearMap.funLeft K K (Prod.mk u))
    with hA
  set F : (α × Fin 4 → K) → α → Fin 4 → K := fun n h => if h ∈ X then m h else fun k => n (h, k)
    with hF
  have hmemA : ∀ n, n ∈ A ↔ ∀ u, (fun k => n (u, k)) ∈ Au u := fun n => by
    simp only [hA, Submodule.mem_iInf, Submodule.mem_comap]; rfl
  suffices key : ∀ O : Finset α, (↑O : Set α) ⊆ C \ X →
      ∃ n ∈ A, LinearIndepOn K (F n) ((C ∩ X) ∪ ↑O) by
    have hfin : (C \ X).Finite := Set.toFinite _
    obtain ⟨n, hn, hli⟩ := key hfin.toFinset (by simp)
    refine ⟨n, hn, ?_⟩
    rwa [Set.Finite.coe_toFinset, Set.inter_union_sdiff] at hli
  intro O
  induction O using Finset.induction_on with
  | empty =>
    intro _
    refine ⟨0, A.zero_mem, ?_⟩
    rw [Finset.coe_empty, Set.union_empty]
    exact hm.congr fun h hh => by simp [hF, hh.2]
  | insert u O hu ih =>
    intro hsub
    rw [Finset.coe_insert, Set.insert_subset_iff] at hsub
    obtain ⟨n, hn, hli⟩ := ih hsub.2
    set T := (C ∩ X) ∪ (↑O : Set α) with hT
    have huT : u ∉ T := by
      rintro (⟨-, huX⟩ | huO)
      · exact hsub.1.2 huX
      · exact hu huO
    have hTC : insert u T ⊆ C := by
      refine Set.insert_subset hsub.1.1 (Set.union_subset Set.inter_subset_left ?_)
      exact fun w hw => (hsub.2 hw).1
    have hTcard : T.ncard ≤ 2 := by
      have := Set.ncard_le_ncard hTC (Set.toFinite _)
      rw [Set.ncard_insert_of_notMem huT (Set.toFinite _)] at this
      omega
    have hS : Module.finrank K (Submodule.span K (F n '' T)) ≤ 2 :=
      (finrank_span_le_ncard _ (Set.toFinite _)).trans
        ((Set.ncard_image_le (Set.toFinite _)).trans hTcard)
    obtain ⟨y, hyA, hyS⟩ : ∃ y ∈ Au u, y ∉ Submodule.span K (F n '' T) := by
      refine exists_mem_notMem_of_finrank hS ?_
      rcases hAu u hsub.1 with h | ⟨h, hv, hmv⟩
      · exact Or.inl h
      · refine Or.inr ⟨h, m v, Submodule.subset_span ⟨v, Or.inl hv, ?_⟩, hmv⟩
        simp [hF, hv.2]
    set n' : α × Fin 4 → K := fun c => if c.1 = u then y c.2 else n c with hn'
    have hn'A : n' ∈ A := by
      rw [hmemA] at hn ⊢
      intro w
      by_cases hw : w = u
      · subst hw; simpa [hn'] using hyA
      · simpa [hn', hw] using hn w
    have heq : Set.EqOn (F n) (F n') T := by
      intro h hh
      have hhu : h ≠ u := fun e => huT (e ▸ hh)
      simp only [hF, hn', hhu, ite_false]
    have hFu : F n' u = y := by
      simp only [hF, hn', hsub.1.2, ite_false, ite_true]
    refine ⟨n', hn'A, ?_⟩
    rw [Finset.coe_insert, Set.union_insert, linearIndepOn_insert huT]
    refine ⟨hli.congr heq, ?_⟩
    rw [← Set.image_congr heq, hFu]
    exact hyS

/-- **Extending the points of the rigid set** (`lem:pencil-d-ear-extend`): let `K` be infinite, `G`
nondegeneracy-feasible, `W₀`, `x`, `a`, `b` a good ear (`Graph.IsPencilGoodEar`) and
`X = W₀ \ {x}`. Read `Γ_L` inside `Γ(G)`'s parameter type, its point `b_v(t)` at a selector
`hubSelL v` of `H_L[v]`, the pencil hubs of `G` in the closed neighbourhood of `v` in `G[X]`.
Some polynomial `E_L` with a non-root has, at each of its non-roots `t`, parameters `s` of `Γ(G)`
whose points `b⁰_v(s)`, `v ∈ X`, are nonzero multiples of the `b_v(t)`.

Proof. `E_L` is `exists_earExtend_cond_poly`'s. At `t`, put `m_h = t(h, 0)` at every body of `X`
and, outside `X`, a normal `n_u ∈ A_u = {b_w(t) : w ∈ X, w ~ u}^⊥`. The closed hub-neighbourhood
of `v ∈ X` in `G` is `H_L[v]`, whose `m` are independent and orthogonal to `b_v(t)`, and hubs `u`
outside `W₀` (`x` is not a hub). Each such `u` has at most two neighbours in `X` (part (v) of
`lem:pencil-d-good-ear`), so `dim A_u ≥ 2`; then `v` is a hub, and either `u` has no other
neighbour in `X` and `A_u = b_v(t)^⊥`, or a second one `v₂`, not adjacent to `v` (no triangle
with two hubs), and `m_v ∉ A_u` by (b). So `exists_linearIndepOn_of_finrank` makes the normals of
each closed hub-neighbourhood independent at some point of `∏ A_u`, an open condition there, and
`exists_mem_forall_eval_ne_zero` gives one point for every `v ∈ X`. The auxiliary vectors of `v`
complete them to a triple whose `cross₃` is a nonzero multiple of `b_v(t)`
(`exists_fill_cross₃_eq_smul_of_selector`). The chapter's moment curve and its case analysis on
`O_v` are not used. -/
theorem exists_earExtend_poly [Infinite K] [Finite α] {G : Graph α β}
    (hfeas : PencilNondegFeasible K G) {W₀ : Set α} {x a b : α}
    (hW : G.IsPencilGoodEar W₀ x a b) {hubSel : α → Fin 3 → Option α}
    (hHubSel : ∀ v, IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v))
    {hubSelL : α → Fin 3 → Option α}
    (hL : ∀ v ∈ W₀ \ {x},
      IsFin3SelectorOf {h | h ∈ (G.induce (W₀ \ {x})).closedNbhd v ∧ G.PencilHub h} (hubSelL v)) :
    ∃ E : MvPolynomial (α × Fin 7 × Fin 4) K, (∃ t, MvPolynomial.eval t E ≠ 0) ∧
      ∀ t, MvPolynomial.eval t E ≠ 0 → ∃ s : α × Fin 7 × Fin 4 → K,
        ∀ v ∈ W₀ \ {x}, ∃ c : K, c ≠ 0 ∧ steerPoint hubSel s v = c • steerPoint hubSelL t v := by
  classical
  have := Fintype.ofFinite α
  obtain ⟨hF1, hF2⟩ := hfeas.hub_conditions
  set X := W₀ \ {x} with hX
  set H : α → Set α := fun v => {h | h ∈ (G.induce X).closedNbhd v ∧ G.PencilHub h} with hH
  obtain ⟨E, hE, hEt⟩ := exists_earExtend_cond_poly (K := K) (H := H) hL
  refine ⟨E, hE, fun t ht => ?_⟩
  obtain ⟨hb0, hbm⟩ := hEt t ht
  set bt := steerPoint hubSelL t with hbt
  set m : α → Fin 4 → K := fun h k => t (h, 0, k) with hm
  have hxhub : ¬ G.PencilHub x := fun h => by have := h.2; rw [hW.degree_eq] at this; omega
  -- the closed hub-neighbourhood of `v ∈ X`: `H_L[v]` and hubs outside `W₀`
  have hCX : ∀ v ∈ X, ∀ h ∈ G.closedHubNbhd v, h ∈ X → h ∈ H v := by
    rintro v hv h ⟨hhub, rfl | ⟨e, he⟩⟩ hhX
    · exact ⟨Or.inl rfl, hhub⟩
    · exact ⟨Or.inr ⟨e, he.induce hv hhX⟩, hhub⟩
  have hCout : ∀ v ∈ X, ∀ u ∈ G.closedHubNbhd v, u ∉ X → u ∈ V(G) \ W₀ ∧ G.Adj u v := by
    rintro v hv u ⟨hhub, rfl | ⟨e, he⟩⟩ huX
    · exact absurd hv huX
    · refine ⟨⟨hhub.1, fun huW => ?_⟩, ⟨e, he.symm⟩⟩
      have hux : u = x := by
        by_contra hux
        exact huX ⟨huW, hux⟩
      exact hxhub (hux ▸ hhub)
  have horthm : ∀ v ∈ X, ∀ h ∈ H v, m h ⬝ᵥ bt v = 0 := fun v hv h hh => by
    rw [dotProduct_comm]
    exact dotProduct_pencilChartPoint_hubNormal_of_selector _ (hL v hv) hh
  have hlim : ∀ v ∈ X, LinearIndepOn K m (H v) := fun v hv =>
    linearIndepOn_hubNormal_of_selector _ (hL v hv) (hb0 v hv)
  set Au : α → Submodule K (Fin 4 → K) :=
    fun u => dotPerp (Submodule.span K (bt '' {w | w ∈ X ∧ G.Adj u w})) with hAu
  set A : Submodule K (α × Fin 4 → K) := ⨅ u, (Au u).comap (LinearMap.funLeft K K (Prod.mk u))
    with hA
  set F : (α × Fin 4 → K) → α → Fin 4 → K := fun n h => if h ∈ X then m h else fun k => n (h, k)
    with hF
  -- each closed hub-neighbourhood of `X` is independent at some point of `A`
  have hex : ∀ v ∈ X, ∃ n ∈ A, LinearIndepOn K (F n) (G.closedHubNbhd v) := by
    intro v hv
    have hmC : LinearIndepOn K m (G.closedHubNbhd v ∩ X) :=
      (hlim v hv).mono fun h hh => hCX v hv h hh.1 hh.2
    refine exists_linearIndepOn_of_finrank (C := G.closedHubNbhd v) (X := X) (m := m) (Au := Au)
      (v := v) (hF1 v) hmC fun u hu => ?_
    obtain ⟨⟨huV, huW⟩, huv⟩ := hCout v hv u hu.1 hu.2
    have hvhub : G.PencilHub v := hW.hub_of_outside v hv.1 ⟨u, ⟨huV, huW⟩, huv.symm⟩
    by_cases hN : ∃ v₂, v₂ ∈ X ∧ G.Adj u v₂ ∧ v₂ ≠ v
    · obtain ⟨v₂, hv₂X, huv₂, hv₂v⟩ := hN
      refine Or.inr ⟨?_, ⟨⟨hvhub, Or.inl rfl⟩, hv⟩, fun hmA => ?_⟩
      · have hN2 : {w | w ∈ X ∧ G.Adj u w}.ncard ≤ 2 :=
          (Set.ncard_le_ncard (s := {w | w ∈ X ∧ G.Adj u w}) (t := {w | w ∈ W₀ ∧ G.Adj u w})
            (fun w hw => ⟨hw.1.1, hw.2⟩) (Set.toFinite _)).trans
            (hW.outside u ⟨huV, huW⟩).1
        have hsp := (finrank_span_le_ncard (R := K) _ (Set.toFinite _)).trans
          ((Set.ncard_image_le (f := bt) (Set.toFinite _)).trans hN2)
        rw [hAu, finrank_dotPerp]
        omega
      · have h0 := mem_dotPerp.1 hmA (bt v₂) (Submodule.subset_span ⟨v₂, ⟨hv₂X, huv₂⟩, rfl⟩)
        refine hbm v₂ hv₂X v (fun hvH => ?_) (by rw [dotProduct_comm]; exact h0)
        rcases hvH.1 with rfl | ⟨e, he⟩
        · exact hv₂v rfl
        · obtain ⟨e₁, he₁⟩ := huv
          obtain ⟨e₂, he₂⟩ := huv₂
          exact hF2 e₂ e₁ e v₂ u v (fun h => hu.2 (h ▸ hv₂X)) (fun h => hu.2 (h ▸ hv)) hv₂v
            he₂.symm he₁ he.1.symm hu.1.1 hvhub
    · push Not at hN
      refine Or.inl ?_
      have hsub : Submodule.span K (bt '' {w | w ∈ X ∧ G.Adj u w}) ≤ K ∙ bt v := by
        rw [Submodule.span_le]
        rintro _ ⟨w, ⟨hwX, huw⟩, rfl⟩
        rw [hN w hwX huw]
        exact Submodule.mem_span_singleton_self _
      have h1 := (Submodule.finrank_mono hsub).trans
        ((finrank_span_le_ncard (R := K) {bt v} (Set.toFinite _)).trans (Set.ncard_singleton _).le)
      rw [hAu, finrank_dotPerp]
      omega
  -- one point of `A` for all of them
  have hR : ∀ v : α, ∃ R : MvPolynomial (α × Fin 4) K, (∃ n ∈ A, MvPolynomial.eval n R ≠ 0) ∧
      ∀ n, MvPolynomial.eval n R ≠ 0 → v ∈ X → LinearIndepOn K (F n) (G.closedHubNbhd v) := by
    intro v
    by_cases hv : v ∈ X
    · obtain ⟨n₀, hn₀A, hn₀⟩ := hex v hv
      have hopen := isZariskiOpen_linearIndependent (K := K) F (fun h k => by
        by_cases hh : h ∈ X
        · simpa [hF, hh] using isPolyFun_const (σ := α × Fin 4) (m h k)
        · simpa [hF, hh] using isPolyFun_apply (K := K) (h, k)) (G.closedHubNbhd v)
      obtain ⟨R, hR0, hR⟩ := hopen n₀ hn₀
      exact ⟨R, ⟨n₀, hn₀A, hR0⟩, fun n hn _ => hR n hn⟩
    · exact ⟨1, ⟨0, A.zero_mem, by simp⟩, fun _ _ h => absurd h hv⟩
  choose R hRex hR using hR
  obtain ⟨n, hnA, hn⟩ := exists_mem_forall_eval_ne_zero (L := A) R hRex
  -- the auxiliary vectors at every `v ∈ X`
  have hfill : ∀ v, ∃ fill : Fin 3 → Fin 4 → K, v ∈ X → ∃ c : K, c ≠ 0 ∧
      cross₃ (hubSlotOf (F n) (hubSel v) fill 0) (hubSlotOf (F n) (hubSel v) fill 1)
        (hubSlotOf (F n) (hubSel v) fill 2) = c • bt v := by
    intro v
    by_cases hv : v ∈ X
    · obtain ⟨fill, -, hc⟩ := exists_fill_cross₃_eq_smul_of_selector (hb0 v hv) (hHubSel v)
        (hR v n (hn v) hv) fun w hw => by
          by_cases hwX : w ∈ X
          · simp only [hF, hwX, ite_true]
            exact horthm v hv w (hCX v hv w hw hwX)
          · obtain ⟨-, hwv⟩ := hCout v hv w hw hwX
            have hmem := (Submodule.mem_iInf _).1 hnA w
            rw [Submodule.mem_comap] at hmem
            have hFw : F n w = (LinearMap.funLeft K K (Prod.mk w)) n := by
              simp only [hF, hwX, ite_false]; rfl
            rw [hFw]
            exact mem_dotPerp.1 hmem (bt v) (Submodule.subset_span ⟨v, ⟨hv, hwv⟩, rfl⟩)
      exact ⟨fill, fun _ => hc⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose fill hfill using hfill
  refine ⟨(⟨F n, fill, fun _ _ => 0⟩ : PencilSeed K α).toGamma, fun v hv => ?_⟩
  obtain ⟨c, hc0, hc⟩ := hfill v hv
  refine ⟨c, hc0, ?_⟩
  rw [steerPoint, PencilSeed.ofGamma_toGamma]
  exact hc

end CombinatorialRigidity.Molecular
