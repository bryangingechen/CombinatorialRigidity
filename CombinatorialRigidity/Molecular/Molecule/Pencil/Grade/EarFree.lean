/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.LiftNoRigid
public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.GoodEar

/-!
# Extending the points of the rigid set, and the rest of it lifts only trivially

`lem:pencil-d-ear-extend` and `lem:pencil-d-ear-free` of `blueprint/src/chapter/pencil-d.tex`,
`sec:pencil-d-generic`.

`lem:pencil-d-ear-extend` (`exists_earExtend_poly`): at the good ear `W₀`, `x` of
`lem:pencil-d-good-ear`, with
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

`lem:pencil-d-ear-free` (`holdsGenerally_earFree`): at a general nondegenerate realization of `G`
in dimension three, every lift of `Y = G[X]` is trivial, so the ear's condition holds. Four steps:

* The algebra at one realization (`earFree_of_finrank_liftSpaceTilde_le`): (a) closed
  neighbourhoods of rank three, (b) the points of `X` spanning and (c) `dim L̃ ≤ 4 +` the free
  coordinates make the trivial lifts and the free coordinates all of `L̃`
  (`liftTildeOfTrivial`, `isTrivialLift_of_finrank_liftSpaceTilde_le`), and a lift of `G − x`
  restricts to one of `Y` (`earLift_of_isTrivialLift`).
* A configuration of `Y` (`exists_earFree_config`) over a main picture with distinct planes, where
  (a), (b) (`span_pencilConfigPoint_eq_top`) and (c) hold; the good ear gives its hypotheses
  (`Graph.IsPencilGoodEar.rest`).
* The configuration in `Γ_L` (`exists_earFree_gammaL`): the plane normals at the hubs, independent
  on each `H_L[v]` (`linearIndepOn_planeNormal_of_subset`), completed by auxiliary vectors
  (`exists_steerPoint_eq_smul`).
* Into `G`: (a), (b), (c) are open (`isZariskiOpen_earFreeCond`,
  `isZariskiOpen_finrank_liftSpaceTilde_le`) and unchanged by rescaling (`earFreeCond_of_smul`), so
  they pass from `t₀ ∈ Γ_L` through `E_L` to `Γ(G)` and meet `U(G)`.
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
(`exists_fill_cross₃_eq_smul_of_selector`). -/
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

/-! ## `lem:pencil-d-ear-free`: the algebra at one realization -/

open Classical in
/-- **The trivial lifts and the free coordinates, in `L̃`** (a step of `lem:pencil-d-ear-free`): the
form `c` on `K⁴` gives the map `w ↦ c · b⁰_w` and the form `c` at every body; the free coordinates
`e` (`liftFreeCoords`) are added, the third coordinate of the form at a body `v` of `G` moved along
a vector `n_v` (a normal of the points of its closed neighbourhood) instead of the third axis. -/
noncomputable def liftTildeOfTrivial (G : Graph α β) (b0 n : α → Fin 4 → K) :
    (Fin 4 → K) × (α ⊕ α × Fin 4 → K) →ₗ[K] (α ⊕ α × Fin 4 → K) where
  toFun ce := Sum.elim (fun w => ce.1 ⬝ᵥ b0 w + ce.2 (.inl w))
    (fun p => ce.1 p.2 + if p.1 ∈ V(G) then ce.2 (.inr (p.1, 2)) * n p.1 p.2 else ce.2 (.inr p))
  map_add' y y' := by
    funext c; rcases c with w | ⟨v, i⟩
    · simp only [Sum.elim_inl, Prod.fst_add, Prod.snd_add, Pi.add_apply, add_dotProduct]; ring
    · simp only [Sum.elim_inr, Prod.fst_add, Prod.snd_add, Pi.add_apply]; split_ifs <;> ring
  map_smul' a y := by
    funext c; rcases c with w | ⟨v, i⟩
    · simp only [Sum.elim_inl, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
        RingHom.id_apply, smul_dotProduct]; ring
    · simp only [Sum.elim_inr, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
        RingHom.id_apply]; split_ifs <;> ring

/-- `liftTildeOfTrivial` lands in `L̃` when each `n_v` is orthogonal to the points of the closed
neighbourhood of `v`. -/
theorem liftTildeOfTrivial_mem {G : Graph α β} {b0 n : α → Fin 4 → K}
    (hn : ∀ v ∈ V(G), ∀ w ∈ G.closedNbhd v, n v ⬝ᵥ b0 w = 0) (c : Fin 4 → K)
    {e : α ⊕ α × Fin 4 → K} (he : e ∈ liftFreeCoords (K := K) G) :
    liftTildeOfTrivial G b0 n (c, e) ∈ liftSpaceTilde G b0 := by
  intro v hv w hw
  have hwV := Graph.closedNbhd_subset_vertexSet hv hw
  have key := hn v hv w hw
  simp only [liftTildeOfTrivial, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl, Sum.elim_inr,
    ite_eq_left hv, he.1 w hwV, add_zero, add_mul, Finset.sum_add_distrib]
  simp only [dotProduct, mul_assoc, ← Finset.mul_sum] at key ⊢
  rw [key, mul_zero, add_zero]

/-- `liftTildeOfTrivial` is injective on the free coordinates when the points of `V(G)` span `K⁴`
and every `n_v` is nonzero: the maps give `c = 0`, then each coordinate of `e`. -/
theorem eq_zero_of_liftTildeOfTrivial_eq_zero {G : Graph α β} {b0 n : α → Fin 4 → K}
    (hspan : Submodule.span K (b0 '' V(G)) = ⊤) (hn0 : ∀ v ∈ V(G), n v ≠ 0) {c : Fin 4 → K}
    {e : α ⊕ α × Fin 4 → K} (he : e ∈ liftFreeCoords (K := K) G)
    (h0 : liftTildeOfTrivial G b0 n (c, e) = 0) : c = 0 ∧ e = 0 := by
  have hc : ∀ x, liftTildeOfTrivial G b0 n (c, e) x = 0 := fun x => congr_fun h0 x
  have hcb : ∀ w ∈ V(G), c ⬝ᵥ b0 w = 0 := fun w hw => by
    simpa [liftTildeOfTrivial, he.1 w hw] using hc (.inl w)
  have hc0 : c = 0 := by
    have hmem : c ∈ dotPerp (⊤ : Submodule K (Fin 4 → K)) := by
      rw [← hspan, mem_dotPerp]
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy => obtain ⟨w, hw, rfl⟩ := hy; exact hcb w hw
      | zero => simp
      | add y y' _ _ h h' => rw [dotProduct_add, h, h', add_zero]
      | smul a y _ h => rw [dotProduct_smul, h, smul_zero]
    have := finrank_dotPerp (⊤ : Submodule K (Fin 4 → K))
    rw [finrank_top, Module.finrank_fin_fun, Nat.sub_self, Submodule.finrank_eq_zero] at this
    rw [this] at hmem
    exact (Submodule.mem_bot K).1 hmem
  subst hc0
  refine ⟨rfl, funext fun x => ?_⟩
  rcases x with w | ⟨v, i⟩
  · by_cases hw : w ∈ V(G)
    · exact he.1 w hw
    · simpa [liftTildeOfTrivial] using hc (.inl w)
  · by_cases hv : v ∈ V(G)
    · have h2 : e (.inr (v, 2)) = 0 := by
        obtain ⟨j, hj⟩ := Function.ne_iff.1 (hn0 v hv)
        have := hc (.inr (v, j))
        simp only [liftTildeOfTrivial, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inr,
          ite_eq_left hv, Pi.zero_apply, zero_add, mul_eq_zero] at this
        exact this.resolve_right hj
      by_cases hi : i = 2
      · rw [hi]; exact h2
      · exact he.2 v hv i hi
    · simpa [liftTildeOfTrivial, hv] using hc (.inr (v, i))

/-- **Every lift is trivial under the three conditions** (a step of `lem:pencil-d-ear-free`, the
algebra at one realization): let the points of every closed neighbourhood of `G` lie in its
subspace, of dimension at most three, and span at least three dimensions (a); let the points of
`V(G)` span `K⁴` (b); and let `dim L̃ ≤ 4 +` the free coordinates (c). Then every lift is
trivial.

Proof. By (a) each subspace is the span of the points of its closed neighbourhood, which have a
nonzero normal `n_v`. By (b) the trivial lifts and the free coordinates, moved along the `n_v`,
embed in `L̃` (`liftTildeOfTrivial`), in dimension `4 +` the free coordinates, so by (c) they are
all of `L̃`. A lift extends to a member of `L̃` (`exists_mem_liftSpaceTilde_of_mem_liftSpace`),
whose maps are then `w ↦ c · b⁰_w`; its form at `v` agrees with `c` on the points of the closed
neighbourhood, which span the subspace. -/
theorem isTrivialLift_of_finrank_liftSpaceTilde_le [Finite α] {G : Graph α β}
    {b0 : α → Fin 4 → K} {P0 : α → Submodule K (Fin 4 → K)}
    (hP0 : ∀ v ∈ V(G), ∀ w ∈ G.closedNbhd v, b0 w ∈ P0 v)
    (hP3 : ∀ v ∈ V(G), Module.finrank K (P0 v) ≤ 3)
    (h3 : ∀ v ∈ V(G), 3 ≤ Module.finrank K (Submodule.span K (b0 '' G.closedNbhd v)))
    (hspan : Submodule.span K (b0 '' V(G)) = ⊤)
    (hdim : Module.finrank K (liftSpaceTilde G b0) ≤
      4 + Module.finrank K (liftFreeCoords (K := K) G)) :
    ∀ lam ∈ liftSpace G b0 P0, IsTrivialLift G b0 P0 lam := by
  classical
  have := Fintype.ofFinite α
  -- the points of each closed neighbourhood span its subspace
  have hle : ∀ v ∈ V(G), Submodule.span K (b0 '' G.closedNbhd v) ≤ P0 v := fun v hv =>
    Submodule.span_le.2 (by rintro _ ⟨w, hw, rfl⟩; exact hP0 v hv w hw)
  have heq : ∀ v ∈ V(G), Submodule.span K (b0 '' G.closedNbhd v) = P0 v := fun v hv =>
    Submodule.eq_of_le_of_finrank_le (hle v hv) ((hP3 v hv).trans (h3 v hv))
  -- a nonzero vector orthogonal to each closed neighbourhood
  have hn : ∀ v, ∃ m : Fin 4 → K, v ∈ V(G) → m ≠ 0 ∧ ∀ w ∈ G.closedNbhd v, m ⬝ᵥ b0 w = 0 := by
    intro v
    by_cases hv : v ∈ V(G)
    · have hfr := finrank_dotPerp (Submodule.span K (b0 '' G.closedNbhd v))
      have h4 := (Submodule.finrank_mono (hle v hv)).trans (hP3 v hv)
      obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p :=
        dotPerp (Submodule.span K (b0 '' G.closedNbhd v))) (fun hbot => by
          rw [hbot, finrank_bot] at hfr; omega)
      exact ⟨m, fun _ => ⟨hm0, fun w hw => mem_dotPerp.1 hm _
        (Submodule.subset_span ⟨w, hw, rfl⟩)⟩⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose n hn using hn
  set F := liftFreeCoords (K := K) G
  set L := liftSpaceTilde G b0
  set Ψ : (Fin 4 → K) × F →ₗ[K] (α ⊕ α × Fin 4 → K) :=
    (liftTildeOfTrivial G b0 n).comp (LinearMap.id.prodMap F.subtype) with hΨ
  have hΨinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨c, e⟩ h0
    have := eq_zero_of_liftTildeOfTrivial_eq_zero hspan (fun v hv => (hn v hv).1) e.2 h0
    exact Prod.ext this.1 (Subtype.ext this.2)
  have hΨL : LinearMap.range Ψ ≤ L := by
    rintro _ ⟨⟨c, e⟩, rfl⟩
    exact liftTildeOfTrivial_mem (fun v hv => (hn v hv).2) c e.2
  have hrange : LinearMap.range Ψ = L := by
    refine Submodule.eq_of_le_of_finrank_le hΨL ?_
    rw [LinearMap.finrank_range_of_inj hΨinj, Module.finrank_prod, Module.finrank_fin_fun]
    exact hdim
  intro lam hlam
  obtain ⟨z, hzL, hz⟩ := exists_mem_liftSpaceTilde_of_mem_liftSpace hP0 hlam
  obtain ⟨⟨c, e⟩, rfl⟩ : z ∈ LinearMap.range Ψ := hrange ▸ hzL
  have h1 : ∀ w ∈ V(G), lam.1 w = c ⬝ᵥ b0 w := fun w hw => by
    rw [← hz w]
    simp [hΨ, liftTildeOfTrivial, e.2.1 w hw]
  refine ⟨dotProductBilin K K c, fun v hv => ⟨by simpa using h1 v hv, ?_⟩⟩
  -- the forms agree on the points of the closed neighbourhood, which span the subspace
  have key : ∀ p ∈ Submodule.span K (b0 '' G.closedNbhd v), ∀ hp : p ∈ P0 v,
      lam.2 v ⟨p, hp⟩ = c ⬝ᵥ p := by
    intro p hp
    induction hp using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, hw, rfl⟩ := hy
      intro h
      rw [← hlam v hv w hw h]
      exact h1 w (Graph.closedNbhd_subset_vertexSet hv hw)
    | zero =>
      intro h
      rw [dotProduct_zero, show (⟨0, h⟩ : P0 v) = 0 from rfl, map_zero]
    | add y y' hy hy' h h' =>
      intro hp
      have e : (⟨y + y', hp⟩ : P0 v) = ⟨y, hle v hv hy⟩ + ⟨y', hle v hv hy'⟩ := rfl
      rw [e, map_add, h, h', dotProduct_add]
    | smul a y hy h =>
      intro hp
      have e : (⟨a • y, hp⟩ : P0 v) = a • ⟨y, hle v hv hy⟩ := rfl
      rw [e, map_smul, h, dotProduct_smul]
  ext ⟨p, hp⟩
  rw [key p ((heq v hv).symm ▸ hp) hp]
  simp

/-- **The ear's condition from the trivial lifts of the rest** (a step of `lem:pencil-d-ear-free`,
the consequence): if every lift of `G[X]`, `X ⊆ V(G) \ {x}`, is trivial and `a, b ∈ X`, then a
lift of `G − x`, a lift of `G[X]` too, has forms at `a` and `b` that are restrictions of one form
`ψ`, so they agree at `b⁰_x`. -/
theorem earLift_of_isTrivialLift {G : Graph α β} {X : Set α} {b0 : α → Fin 4 → K}
    {P0 : α → Submodule K (Fin 4 → K)} {x a b : α} (hX : X ⊆ V(G) \ {x}) (ha : a ∈ X) (hb : b ∈ X)
    (htriv : ∀ lam ∈ liftSpace (G.induce X) b0 P0, IsTrivialLift (G.induce X) b0 P0 lam) :
    ∀ lam ∈ liftSpace (G.induce (V(G) \ {x})) b0 P0, ∀ (ha : b0 x ∈ P0 a) (hb : b0 x ∈ P0 b),
      lam.2 a ⟨b0 x, ha⟩ = lam.2 b ⟨b0 x, hb⟩ := by
  intro lam hlam hxa hxb
  have hle := G.induce_mono_right hX
  obtain ⟨ψ, hψ⟩ := htriv lam fun v hv w hw h =>
    hlam v (Graph.vertexSet_mono hle hv) w (Graph.closedNbhd_mono hle v hw) h
  rw [(hψ a (by simpa using ha)).2, (hψ b (by simpa using hb)).2]
  rfl

/-- **The rest of the rigid set lifts only trivially, at one realization** (`lem:pencil-d-ear-free`,
sub-lemma (1)): at a good ear, with `X = W₀ \ {x}` and `Y = G[X]`, let the points of every closed
neighbourhood of `G` lie in its subspace, of dimension at most three (as at a realization in
`U(G)`), and let the points satisfy (a), (b) and (c) for `Y`. Then the predicate of
`holdsGenerally_earFree` holds there: the closed neighbourhoods of `Y` have rank exactly three, the
points of `X` span, every lift of `Y` is trivial (`isTrivialLift_of_finrank_liftSpaceTilde_le`),
and the ear's condition holds (`earLift_of_isTrivialLift`; `a, b ∈ X` as `x` is not linked to
itself). -/
theorem earFree_of_finrank_liftSpaceTilde_le [Finite α] {G : Graph α β} (hS : G.Simple)
    {W₀ : Set α} {x a b : α} (hW : G.IsPencilGoodEar W₀ x a b) {b0 : α → Fin 4 → K}
    {P0 : α → Submodule K (Fin 4 → K)}
    (hP0 : ∀ v ∈ V(G), ∀ w ∈ G.closedNbhd v, b0 w ∈ P0 v)
    (hP3 : ∀ v ∈ V(G), Module.finrank K (P0 v) ≤ 3)
    (h3 : ∀ v ∈ W₀ \ {x},
      3 ≤ Module.finrank K (Submodule.span K (b0 '' (G.induce (W₀ \ {x})).closedNbhd v)))
    (hspan : Submodule.span K (b0 '' (W₀ \ {x})) = ⊤)
    (hdim : Module.finrank K (liftSpaceTilde (G.induce (W₀ \ {x})) b0) ≤
      4 + Module.finrank K (liftFreeCoords (K := K) (G.induce (W₀ \ {x})))) :
    ((∀ v ∈ W₀ \ {x},
        Module.finrank K (Submodule.span K (b0 '' (G.induce (W₀ \ {x})).closedNbhd v)) = 3) ∧
      Submodule.span K (b0 '' (W₀ \ {x})) = ⊤ ∧
      (∀ lam ∈ liftSpace (G.induce (W₀ \ {x})) b0 P0,
        IsTrivialLift (G.induce (W₀ \ {x})) b0 P0 lam)) ∧
    ∀ lam ∈ liftSpace (G.induce (V(G) \ {x})) b0 P0, ∀ (ha : b0 x ∈ P0 a) (hb : b0 x ∈ P0 b),
      lam.2 a ⟨b0 x, ha⟩ = lam.2 b ⟨b0 x, hb⟩ := by
  have := hS.toLoopless
  set X := W₀ \ {x} with hX
  have hXV : X ⊆ V(G) \ {x} := Set.sdiff_subset_sdiff_left hW.subset
  have hYle : G.induce X ≤ G := Graph.induce_le (hXV.trans Set.sdiff_subset)
  have hP0Y : ∀ v ∈ V(G.induce X), ∀ w ∈ (G.induce X).closedNbhd v, b0 w ∈ P0 v :=
    fun v hv w hw => hP0 v (Graph.vertexSet_mono hYle hv) w (Graph.closedNbhd_mono hYle v hw)
  have hle3 : ∀ v ∈ X,
      Module.finrank K (Submodule.span K (b0 '' (G.induce X).closedNbhd v)) ≤ 3 := fun v hv =>
    (Submodule.finrank_mono (Submodule.span_le.2 (by
      rintro _ ⟨w, hw, rfl⟩; exact hP0Y v (by simpa using hv) w hw))).trans
      (hP3 v (hXV hv).1)
  have htriv := isTrivialLift_of_finrank_liftSpaceTilde_le (G := G.induce X) hP0Y
    (fun v hv => hP3 v (Graph.vertexSet_mono hYle hv)) (fun v hv => h3 v (by simpa using hv))
    (by simpa using hspan) hdim
  refine ⟨⟨fun v hv => le_antisymm (hle3 v hv) (h3 v hv), hspan, htriv⟩,
    earLift_of_isTrivialLift hXV ⟨hW.a_mem, ?_⟩ ⟨hW.b_mem, ?_⟩ htriv⟩
  · exact fun h => hW.adj_a.ne (h ▸ rfl)
  · exact fun h => hW.adj_b.ne (h ▸ rfl)

/-! ## `lem:pencil-d-ear-free`: a configuration of the rest -/

/-- **The points of a configuration span `K⁴` when two planes differ** (a step of
`lem:pencil-d-ear-free`, (b) at the configuration of `Y`): a form vanishing on the points vanishes
on two closed neighbourhoods, so it is a multiple of both plane normals
(`Graph.IsAdmissiblePicture.exists_smul_eq_interpolant`), which are independent
(`planeNormal_pair`). -/
theorem span_pencilConfigPoint_eq_top [Fintype α] {G : Graph α β} {q : α × Fin 2 → K}
    (hq : G.IsAdmissiblePicture q) {x : α ⊕ (α × Fin 3) → K}
    (hx : x ∈ LinearMap.ker ((G.liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin)
    {u w : α} (hu : u ∈ V(G)) (hw : w ∈ V(G)) (hpd : planeDiff u w x ≠ 0) :
    Submodule.span K (pencilConfigPoint q (fun a => x (Sum.inl a)) '' V(G)) = ⊤ := by
  set S := Submodule.span K (pencilConfigPoint q (fun a => x (Sum.inl a)) '' V(G))
  obtain ⟨-, hk, -⟩ := Graph.mem_ker_liftingMatrix_iff.1 hx
  have hbot : dotPerp S = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun c hc => ?_
    by_contra hc0
    have hcS : ∀ v ∈ V(G), ∀ y ∈ G.closedNbhd v,
        c ⬝ᵥ pencilConfigPoint q (fun a => x (Sum.inl a)) y = 0 := fun v hv y hy =>
      mem_dotPerp.1 hc _ (Submodule.subset_span ⟨y, Graph.closedNbhd_subset_vertexSet hv hy, rfl⟩)
    obtain ⟨c₁, hc₁, e₁⟩ := hq.exists_smul_eq_interpolant hu (hk u hu) hc0 (hcS u hu)
    obtain ⟨c₂, -, e₂⟩ := hq.exists_smul_eq_interpolant hw (hk w hw) hc0 (hcS w hw)
    have hne : (fun i => x (Sum.inr (u, i))) ≠ fun i => x (Sum.inr (w, i)) := fun heq =>
      hpd (funext fun i => by
        rw [planeDiff_apply, Pi.zero_apply, sub_eq_zero]; exact congr_fun heq i)
    have e₁' : c = c₁ • planeNormal (fun i => x (Sum.inr (u, i))) := e₁
    have e₂' : c = c₂ • planeNormal (fun i => x (Sum.inr (w, i))) := e₂
    have hLI := planeNormal_pair hne
    rw [LinearIndependent.pair_iff] at hLI
    have h0 : c₁ • planeNormal (fun i => x (Sum.inr (u, i))) +
        (-c₂) • planeNormal (fun i => x (Sum.inr (w, i))) = 0 := by
      rw [neg_smul, ← e₁', ← e₂', add_neg_cancel]
    exact hc₁ (hLI c₁ (-c₂) h0).1
  have h4 := finrank_dotPerp S
  rw [hbot, finrank_bot] at h4
  exact Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le S)
    (by rw [Module.finrank_fin_fun]; omega))

/-- **A configuration of the rest of the rigid set** (`lem:pencil-d-ear-free`, sub-lemma (2), the
configuration of `Y`): let `Y` be simple with a body, at least three members in every closed
neighbourhood, `def₂(Y[Z]) ≠ 0` for every `Z` of at least two bodies and `def₂(Y) = 1`. Some
admissible picture `q`, with the picture points of any three distinct bodies independent, has a
solution `(z, h)` of the lifting system whose planes differ at any two distinct bodies; its points
span `K⁴` and `dim L̃ = 4 +` the free coordinates.

Proof. `q` is off the main-picture polynomial (`Graph.exists_mvPolynomial_isMainPicture`), the
planes polynomial of `exists_planeDiff_ne_zero_poly` (which gives the solution) and the
determinants (`exists_det_poly`). The points span by `span_pencilConfigPoint_eq_top` at a body and
a neighbour; `dim L̃ = dim L(q) +` the free coordinates (`finrank_liftSpaceTilde_pencilConfigPoint`)
and `dim L(q) = 3 + def₂(Y) = 4` at a main picture
(`Graph.IsMainPicture.finrank_liftingSpace_eq`). -/
theorem exists_earFree_config [Infinite K] [Fintype α] [Finite β] {Y : Graph α β}
    (hSimple : Y.Simple) (h3 : ∀ v ∈ V(Y), 3 ≤ (Y.closedNbhd v).ncard)
    (hS : ∀ Z ⊆ V(Y), 2 ≤ Z.ncard → (Y.induce Z).deficiency 2 ≠ 0)
    (hdef : Y.deficiency 2 = 1) (hne : V(Y).Nonempty) :
    ∃ q : α × Fin 2 → K,
      ∃ x ∈ LinearMap.ker ((Y.liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin,
      Y.IsAdmissiblePicture q ∧
      (∀ u v w : α, u ≠ v → u ≠ w → v ≠ w → LinearIndependent K
        ![pencilPicturePoint q u, pencilPicturePoint q v, pencilPicturePoint q w]) ∧
      (∀ u ∈ V(Y), ∀ w ∈ V(Y), u ≠ w → planeDiff u w x ≠ 0) ∧
      Submodule.span K (pencilConfigPoint q (fun a => x (Sum.inl a)) '' V(Y)) = ⊤ ∧
      Module.finrank K (liftSpaceTilde Y (pencilConfigPoint q (fun a => x (Sum.inl a)))) =
        4 + Module.finrank K (liftFreeCoords (K := K) Y) := by
  classical
  obtain ⟨Pm, hPm0, hPm⟩ := Y.exists_mvPolynomial_isMainPicture (K := K) hSimple.toLoopless h3
  obtain ⟨Ppl, hPpl0, hPpl⟩ := exists_planeDiff_ne_zero_poly (K := K) hSimple h3 hS
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
  set Q : MvPolynomial (α × Fin 2) K := Pm * Ppl * ∏ t, Dgp t with hQdef
  have hQ0 : Q ≠ 0 := mul_ne_zero (mul_ne_zero hPm0 hPpl0)
    (Finset.prod_ne_zero_iff.mpr fun t _ => hDgp0 t)
  obtain ⟨q, hq⟩ := MvPolynomial.exists_eval_ne_zero hQ0
  rw [hQdef, map_mul, map_mul, map_prod] at hq
  have hqm := left_ne_zero_of_mul (left_ne_zero_of_mul hq)
  have hqpl := right_ne_zero_of_mul (left_ne_zero_of_mul hq)
  have hqgp := Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hq)
  have hmain := hPm q hqm
  obtain ⟨ℓ, ⟨x, hx, hℓx⟩, hℓ⟩ := hPpl q hqpl
  have hpd := hℓ x hℓx
  obtain ⟨v, hv⟩ := hne
  obtain ⟨w, hw, hwv⟩ := Set.exists_ne_of_one_lt_ncard (s := Y.closedNbhd v)
    (by have := h3 v hv; omega) v
  have hwV := Graph.closedNbhd_subset_vertexSet hv hw
  have hz : (fun a => x (Sum.inl a)) ∈ Y.liftingSpace q := by
    rw [← Y.map_ker_liftingMatrix q]; exact ⟨x, hx, rfl⟩
  refine ⟨q, x, hx, hmain.1, fun u v w h1 h2 h3 => hDgp (u, v, w) h1 h2 h3 q
    (hqgp _ (Finset.mem_univ _)), hpd, span_pencilConfigPoint_eq_top hmain.1 hx hwV hv
      (hpd w hwV v hv hwv), ?_⟩
  rw [finrank_liftSpaceTilde_pencilConfigPoint hmain.1 hz]
  have := Graph.IsMainPicture.finrank_liftingSpace_eq (K := K) hSimple ⟨v, hv⟩ h3 hmain
  rw [hdef] at this
  omega

/-- **The rest of a good ear meets the hypotheses of its configuration** (the trace of
`exists_earFree_config` against `Graph.IsPencilGoodEar`): `Y = G[W₀ \ {x}]` is simple (the instance
`G[X].Simple`), has at least three members in every closed neighbourhood (each body has degree at
least two in `Y`, part (iii); `Graph.three_le_ncard_closedNbhd`), `def₂(Y[Z]) ≠ 0`
(`Graph.induce_induce_of_subset`, part (iii)), `def₂(Y) = 1` and at least three bodies. -/
theorem _root_.Graph.IsPencilGoodEar.rest [Finite α] {G : Graph α β} (hS : G.Simple)
    {W₀ : Set α} {x a b : α} (hW : G.IsPencilGoodEar W₀ x a b) :
    (G.induce (W₀ \ {x})).Simple ∧
      (∀ v ∈ V(G.induce (W₀ \ {x})), 3 ≤ ((G.induce (W₀ \ {x})).closedNbhd v).ncard) ∧
      (∀ Z ⊆ V(G.induce (W₀ \ {x})), 2 ≤ Z.ncard →
        ((G.induce (W₀ \ {x})).induce Z).deficiency 2 ≠ 0) ∧
      (G.induce (W₀ \ {x})).deficiency 2 = 1 ∧ V(G.induce (W₀ \ {x})).Nonempty := by
  have := hS
  have hYS : (G.induce (W₀ \ {x})).Simple := inferInstance
  refine ⟨hYS, fun v hv => Graph.three_le_ncard_closedNbhd hYS
    (hW.two_le_degree v (by simpa using hv)), fun Z hZ hZ2 => ?_, hW.deficiency_eq, ?_⟩
  · rw [Graph.vertexSet_induce] at hZ
    rw [Graph.induce_induce_of_subset G hZ]
    exact hW.deficiency_ne Z hZ hZ2
  · rw [Graph.vertexSet_induce]
    exact Set.nonempty_of_ncard_ne_zero (by have := hW.three_le; omega)

/-! ## `lem:pencil-d-ear-free`: the configuration in `Γ_L` -/

/-- **Plane normals on part of a closed neighbourhood are independent** (a step of
`lem:pencil-d-ear-free`, the configuration in `Γ_L`, by the argument of
`lem:pencil-x0-conjunct-three`): at a solution of the lifting system whose planes differ at any two
distinct bodies, over a picture with the picture points of any three distinct bodies independent,
the plane normals of at most three members of the closed neighbourhood of `v` are independent, if
`v` is one of them when there are three. Two distinct planes have independent normals
(`planeNormal_pair`); for `v` and two neighbours `w₁`, `w₂`, the differences `h_{w_i} − h_v` vanish
at the picture points of `v` and `w_i` only, so they are independent (`planeNormal_triple`), as in
`isNondeg_pencilConfig_of_planeDiff`. -/
theorem linearIndepOn_planeNormal_of_subset [Fintype α] {Y : Graph α β} {q : α × Fin 2 → K}
    {x : α ⊕ (α × Fin 3) → K}
    (hx : x ∈ LinearMap.ker ((Y.liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin)
    (hgp : ∀ u v w : α, u ≠ v → u ≠ w → v ≠ w → LinearIndependent K
      ![pencilPicturePoint q u, pencilPicturePoint q v, pencilPicturePoint q w])
    (hpd : ∀ u ∈ V(Y), ∀ w ∈ V(Y), u ≠ w → planeDiff u w x ≠ 0) {v : α} (hv : v ∈ V(Y))
    {T : Set α} (hT : T ⊆ Y.closedNbhd v) (hcard : T.ncard ≤ 3) (hTv : 3 ≤ T.ncard → v ∈ T) :
    LinearIndepOn K (fun s => planeNormal (fun i => x (Sum.inr (s, i)))) T := by
  set h : α → Fin 3 → K := fun s i => x (Sum.inr (s, i)) with hhdef
  obtain ⟨-, k2, -⟩ := Graph.mem_ker_liftingMatrix_iff.1 hx
  have hPD : ∀ a ∈ V(Y), ∀ b ∈ V(Y), a ≠ b → h a ≠ h b := fun a ha b hb hab heq =>
    hpd a ha b hb hab (funext fun i => by
      rw [planeDiff_apply, Pi.zero_apply, sub_eq_zero]; exact congr_fun heq i)
  have hTV : T ⊆ V(Y) := hT.trans (Graph.closedNbhd_subset_vertexSet hv)
  rcases Nat.lt_or_ge T.ncard 1 with h0 | h1
  · rw [(Set.ncard_eq_zero (s := T) (Set.toFinite _)).mp (by omega)]
    exact linearIndepOn_empty _ _
  rcases Nat.lt_or_ge T.ncard 2 with h1' | h2
  · obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp (show T.ncard = 1 by omega)
    rw [ha]
    exact LinearIndepOn.singleton (planeNormal_ne_zero _)
  rcases Nat.lt_or_ge T.ncard 3 with h2' | h3
  · obtain ⟨a, b, hab, hS⟩ := Set.ncard_eq_two.mp (show T.ncard = 2 by omega)
    have haV : a ∈ V(Y) := hTV (hS ▸ Set.mem_insert a _)
    have hbV : b ∈ V(Y) := hTV (hS ▸ Set.mem_insert_of_mem a rfl)
    rw [hS]
    exact (LinearIndepOn.pair_iff_linearIndependent hab).2
      (planeNormal_pair (hPD a haV b hbV hab))
  -- three members: `v` and two of its neighbours
  have hvT := hTv h3
  obtain ⟨w₁, w₂, h12, hw⟩ := Set.ncard_eq_two.mp (show (T \ {v}).ncard = 2 by
    rw [Set.ncard_sdiff_singleton_of_mem hvT]; omega)
  have hST : T = {v, w₁, w₂} := by
    rw [← hw, Set.insert_sdiff_singleton, Set.insert_eq_of_mem hvT]
  have hw1T : w₁ ∈ T \ {v} := hw ▸ Set.mem_insert _ _
  have hw2T : w₂ ∈ T \ {v} := hw ▸ Set.mem_insert_of_mem _ rfl
  have hv1 : w₁ ≠ v := hw1T.2
  have hv2 : w₂ ≠ v := hw2T.2
  obtain ⟨e₁, hl₁⟩ : ∃ e, Y.IsLink e v w₁ := (hT hw1T.1).resolve_left hv1
  obtain ⟨e₂, hl₂⟩ : ∃ e, Y.IsLink e v w₂ := (hT hw2T.1).resolve_left hv2
  have hw1V := hl₁.right_mem
  have hw2V := hl₂.right_mem
  have hgp' := hgp v w₁ w₂ hv1.symm hv2.symm h12
  have hdiff : ∀ w ∈ Y.closedNbhd v, ∀ y, y ∈ Y.closedNbhd v → y ∈ Y.closedNbhd w →
      w ∈ V(Y) → (h w - h v) ⬝ᵥ pencilPicturePoint q y = 0 := by
    intro w _ y hyv hyw hwV
    rw [sub_dotProduct, ← k2 w hwV y hyw, ← k2 v hv y hyv, sub_self]
  have hvN1 : v ∈ Y.closedNbhd w₁ := Or.inr ⟨e₁, hl₁.symm⟩
  have hvN2 : v ∈ Y.closedNbhd w₂ := Or.inr ⟨e₂, hl₂.symm⟩
  have hw1N : w₁ ∈ Y.closedNbhd v := Or.inr ⟨e₁, hl₁⟩
  have hw2N : w₂ ∈ Y.closedNbhd v := Or.inr ⟨e₂, hl₂⟩
  have d1v := hdiff w₁ hw1N v (Or.inl rfl) hvN1 hw1V
  have d1w := hdiff w₁ hw1N w₁ hw1N (Or.inl rfl) hw1V
  have d2v := hdiff w₂ hw2N v (Or.inl rfl) hvN2 hw2V
  have d2w := hdiff w₂ hw2N w₂ hw2N (Or.inl rfl) hw2V
  have hd1 : h w₁ - h v ≠ 0 := sub_ne_zero.mpr (hPD w₁ hw1V v hv hv1)
  have hd2 : h w₂ - h v ≠ 0 := sub_ne_zero.mpr (hPD w₂ hw2V v hv hv2)
  have d2w1 : (h w₂ - h v) ⬝ᵥ pencilPicturePoint q w₁ ≠ 0 := fun h0 =>
    hd2 (eq_zero_of_dotProduct_triple hgp' d2v h0 d2w)
  have d1w2 : (h w₁ - h v) ⬝ᵥ pencilPicturePoint q w₂ ≠ 0 := fun h0 =>
    hd1 (eq_zero_of_dotProduct_triple hgp' d1v d1w h0)
  have hLId : LinearIndependent K ![h w₁ - h v, h w₂ - h v] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have e1 := congrArg (fun y => y ⬝ᵥ pencilPicturePoint q w₁) hst
    have e2 := congrArg (fun y => y ⬝ᵥ pencilPicturePoint q w₂) hst
    simp only [add_dotProduct, smul_dotProduct, d1w, d2w, smul_eq_mul, mul_zero,
      zero_add, add_zero, zero_dotProduct] at e1 e2
    exact ⟨(mul_eq_zero.mp e2).resolve_right d1w2, (mul_eq_zero.mp e1).resolve_right d2w1⟩
  rw [hST]
  exact linearIndepOn_triple_of_linearIndependent _ (planeNormal_triple hLId)

/-- **Chart points at given multiples** (a step of `lem:pencil-d-ear-free`, `t₀ ∈ Γ_L`): vectors
`m` independent on each `H v` and orthogonal to a nonzero `B v` there are the vectors `m_h` of some
`t` whose chart points are nonzero multiples of the `B v`; the auxiliary vectors of `v` complete
them (`exists_fill_cross₃_eq_smul_of_selector`). -/
theorem exists_steerPoint_eq_smul {X : Set α} {H : α → Set α}
    {hubSelL : α → Fin 3 → Option α} (hL : ∀ v ∈ X, IsFin3SelectorOf (H v) (hubSelL v))
    {m B : α → Fin 4 → K} (hB : ∀ v ∈ X, B v ≠ 0) (hLI : ∀ v ∈ X, LinearIndepOn K m (H v))
    (horth : ∀ v ∈ X, ∀ w ∈ H v, m w ⬝ᵥ B v = 0) :
    ∃ t : α × Fin 7 × Fin 4 → K, ∀ v ∈ X, ∃ c : K, c ≠ 0 ∧ steerPoint hubSelL t v = c • B v := by
  classical
  have hfill : ∀ v, ∃ fill : Fin 3 → Fin 4 → K, v ∈ X → ∃ c : K, c ≠ 0 ∧
      cross₃ (hubSlotOf m (hubSelL v) fill 0) (hubSlotOf m (hubSelL v) fill 1)
        (hubSlotOf m (hubSelL v) fill 2) = c • B v := by
    intro v
    by_cases hv : v ∈ X
    · obtain ⟨fill, -, hc⟩ := exists_fill_cross₃_eq_smul_of_selector (hB v hv) (hL v hv)
        (hLI v hv) (horth v hv)
      exact ⟨fill, fun _ => hc⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose fill hfill using hfill
  refine ⟨(⟨m, fill, fun _ _ => 0⟩ : PencilSeed K α).toGamma, fun v hv => ?_⟩
  obtain ⟨c, hc0, hc⟩ := hfill v hv
  refine ⟨c, hc0, ?_⟩
  rw [steerPoint, PencilSeed.ofGamma_toGamma]
  exact hc

/-- **The configuration in `Γ_L`** (`lem:pencil-d-ear-free`, sub-lemma (3), `t₀ ∈ Γ_L`): at a
solution `(z, h)` of the lifting system of `Y = G[W₀ \ {x}]` as `exists_earFree_config` gives it,
some `t₀` has every chart point `b_v(t₀)`, `v ∈ X`, at the selector `hubSelL v` of `H_L[v]` a
nonzero multiple of the configuration point `b_v`. The `m_h` are the plane normals
`(h₀, h₁, −1, h₂)`, orthogonal to the points of the closed neighbourhood, and independent on each
`H_L[v]` (`linearIndepOn_planeNormal_of_subset`): `H_L[v]` lies in the closed hub-neighbourhood of
`v` in `G`, of at most three members, and contains `v` when it has three, as the closed
neighbourhood of a body that is not a hub has at most three members. -/
theorem exists_earFree_gammaL [Fintype α] [Finite β] {G : Graph α β}
    (hfeas : PencilNondegFeasible K G) {W₀ : Set α} {x a b : α}
    (hW : G.IsPencilGoodEar W₀ x a b) {hubSelL : α → Fin 3 → Option α}
    (hL : ∀ v ∈ W₀ \ {x},
      IsFin3SelectorOf {h | h ∈ (G.induce (W₀ \ {x})).closedNbhd v ∧ G.PencilHub h} (hubSelL v))
    {q : α × Fin 2 → K} {y : α ⊕ (α × Fin 3) → K}
    (hy : y ∈ LinearMap.ker (((G.induce (W₀ \ {x})).liftingMatrix K).map
      (MvPolynomial.eval q)).mulVecLin)
    (hgp : ∀ u v w : α, u ≠ v → u ≠ w → v ≠ w → LinearIndependent K
      ![pencilPicturePoint q u, pencilPicturePoint q v, pencilPicturePoint q w])
    (hpd : ∀ u ∈ V(G.induce (W₀ \ {x})), ∀ w ∈ V(G.induce (W₀ \ {x})), u ≠ w →
      planeDiff u w y ≠ 0) :
    ∃ t₀ : α × Fin 7 × Fin 4 → K, ∀ v ∈ W₀ \ {x}, ∃ c : K, c ≠ 0 ∧
      steerPoint hubSelL t₀ v = c • pencilConfigPoint q (fun a => y (Sum.inl a)) v := by
  obtain ⟨hF1, -⟩ := hfeas.hub_conditions
  set X := W₀ \ {x} with hX
  set Y := G.induce X with hY
  set H : α → Set α := fun v => {h | h ∈ Y.closedNbhd v ∧ G.PencilHub h} with hH
  obtain ⟨-, k2, -⟩ := Graph.mem_ker_liftingMatrix_iff.1 hy
  have hYle : Y ≤ G := Graph.induce_le ((Set.sdiff_subset_sdiff_left hW.subset).trans
    Set.sdiff_subset)
  refine exists_steerPoint_eq_smul (H := H) hL
    (m := fun s => planeNormal fun i => y (Sum.inr (s, i)))
    (fun v _ h0 => by simpa [pencilConfigPoint] using congr_fun h0 3) (fun v hv => ?_)
    (fun v hv w hw => ?_)
  · have hvY : v ∈ V(Y) := by simpa [hY] using hv
    have hHC : H v ⊆ G.closedHubNbhd v := by
      rintro h ⟨rfl | ⟨e, he⟩, hh⟩
      · exact ⟨hh, Or.inl rfl⟩
      · exact ⟨hh, Or.inr ⟨e, he.of_le hYle⟩⟩
    have hcard : (H v).ncard ≤ 3 :=
      (Set.ncard_le_ncard hHC (Set.toFinite _)).trans (hF1 v)
    refine linearIndepOn_planeNormal_of_subset hy hgp hpd hvY (fun h hh => hh.1) hcard
      fun h3 => ⟨Or.inl rfl, ?_⟩
    by_contra hnh
    have hsub : H v ⊆ G.closedNbhd v \ {v} := fun h hh =>
      ⟨Graph.closedNbhd_mono hYle v hh.1, fun h' => hnh (h' ▸ hh.2)⟩
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 := Set.ncard_sdiff_singleton_of_mem (show v ∈ G.closedNbhd v from Or.inl rfl)
    have h4 := ncard_closedNbhd_le_three_of_not_pencilHub (G := G) hnh
    omega
  · have hwY : w ∈ V(Y) := Graph.closedNbhd_subset_vertexSet (by simpa [hY] using hv) hw.1
    have hvw : v ∈ Y.closedNbhd w := by
      rcases hw.1 with rfl | ⟨e, he⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨e, he.symm⟩
    have := k2 w hwY v hvw
    simp [planeNormal, pencilConfigPoint, dotProduct, Fin.sum_univ_four, pencilPicturePoint,
      Fin.sum_univ_three] at this ⊢
    linear_combination -this

/-! ## `lem:pencil-d-ear-free`: into `G` -/

/-- The span of an independent family on a set has the size of the set. -/
theorem finrank_span_image_of_linearIndepOn {V : Type*} [AddCommGroup V] [Module K V]
    {f : α → V} {r : Set α} (hr : LinearIndepOn K f r) :
    Module.finrank K (Submodule.span K (f '' r)) = r.ncard := by
  rw [← hr.injOn.ncard_image]
  exact finrank_span_set_eq_ncard hr.id_image

/-- **`dim L̃ ≤ N` is Zariski-open** in parameters on which the points are polynomial (a step of
`lem:pencil-d-ear-free`, (c)): at each point where it holds, the polynomial of the section
(`Matrix.exists_mvPolynomial_section_mulVec_eq_zero` on `liftMatrixPoly`, at `z₀ = 0`), composed
with the points, bounds `dim L̃` by its value there, as in
`exists_holdsGenerally_finrank_liftSpaceTilde_le`. -/
theorem isZariskiOpen_finrank_liftSpaceTilde_le [Finite α] {σ : Type*}
    {P : (σ → K) → α → Fin 4 → K} (hP : ∀ v i, IsPolyFun fun s => P s v i) (G : Graph α β)
    (N : ℕ) : IsZariskiOpen {s | Module.finrank K (liftSpaceTilde G (P s)) ≤ N} := by
  classical
  have := Fintype.ofFinite α
  intro s₀ hs₀
  obtain ⟨D, -, hD₀, -, hDle, -⟩ := Matrix.exists_mvPolynomial_section_mulVec_eq_zero
    (liftMatrixPoly (K := K) G) (q₀ := fun p => P s₀ p.1 p.2) (z₀ := 0) (by simp)
  obtain ⟨R, hR⟩ := IsPolyFun.comp D (f := fun s p => P s p.1 p.2) fun p => hP p.1 p.2
  refine ⟨R, by rw [← hR]; exact hD₀, fun s hs => ?_⟩
  have hle := hDle (fun p => P s p.1 p.2) (by rw [← hR] at hs; exact hs)
  rw [← liftSpaceTilde_eq_ker, ← liftSpaceTilde_eq_ker] at hle
  exact hle.trans hs₀

/-- **The three conditions are Zariski-open** (a step of `lem:pencil-d-ear-free`): (a) as the
independence of a fixed triple `sel v` at every body, (b) as the independence of the points on a
fixed set `r`, and (c) (`isZariskiOpen_finrank_liftSpaceTilde_le`). -/
theorem isZariskiOpen_earFreeCond [Finite α] {σ : Type*} {P : (σ → K) → α → Fin 4 → K}
    (hP : ∀ v i, IsPolyFun fun s => P s v i) (G : Graph α β) (sel : α → Fin 3 → α) (r : Set α)
    (N : ℕ) :
    IsZariskiOpen {s | (∀ v ∈ V(G), LinearIndependent K fun i => P s (sel v i)) ∧
      LinearIndepOn K (P s) r ∧ Module.finrank K (liftSpaceTilde G (P s)) ≤ N} :=
  (isZariskiOpen_forall fun v => isZariskiOpen_imp _ (isZariskiOpen_linearIndependent_univ
    (fun s i => P s (sel v i)) fun _ _ => hP _ _)).and
    ((isZariskiOpen_linearIndependent P (fun _ _ => hP _ _) r).and
      (isZariskiOpen_finrank_liftSpaceTilde_le hP G N))

/-- **The three conditions do not change when the points are rescaled** on `V(G)` by nonzero
scalars (a step of `lem:pencil-d-ear-free`; `finrank_liftSpaceTilde_smul` for (c)). -/
theorem earFreeCond_of_smul {G : Graph α β} {sel : α → Fin 3 → α} {r : Set α} {N : ℕ}
    {B B' : α → Fin 4 → K} (hsel : ∀ v ∈ V(G), ∀ i, sel v i ∈ V(G)) (hr : r ⊆ V(G))
    (hc : ∀ v ∈ V(G), ∃ c : K, c ≠ 0 ∧ B' v = c • B v)
    (h : (∀ v ∈ V(G), LinearIndependent K fun i => B (sel v i)) ∧ LinearIndepOn K B r ∧
      Module.finrank K (liftSpaceTilde G B) ≤ N) :
    (∀ v ∈ V(G), LinearIndependent K fun i => B' (sel v i)) ∧ LinearIndepOn K B' r ∧
      Module.finrank K (liftSpaceTilde G B') ≤ N := by
  choose! c hc0 hceq using hc
  refine ⟨fun v hv => ?_, linearIndepOn_of_forall_smul (fun w hw => ⟨c w, hc0 w (hr hw),
    hceq w (hr hw)⟩) h.2.1, by rw [finrank_liftSpaceTilde_smul hc0 hceq]; exact h.2.2⟩
  have := (h.1 v hv).units_smul fun i => Units.mk0 (c (sel v i)) (hc0 _ (hsel v hv i))
  convert this using 1
  funext i
  simp [hceq _ (hsel v hv i), Units.smul_def]

/-- **The rest of the rigid set lifts only trivially** (`lem:pencil-d-ear-free`): let `K` be
infinite, `G` simple and nondegeneracy-feasible, `W₀`, `x`, `a`, `b` a good ear
(`Graph.IsPencilGoodEar`), `X = W₀ \ {x}` and `Y = G[X]`. At a general nondegenerate realization of
`G` in dimension three, at any selectors of `G`, the points of every closed neighbourhood of `Y`
span three dimensions, the points of `X` span `K⁴`, and every lift of `Y` is trivial; and the ear's
condition `EarLiftCondition` holds at the same selectors.

Proof. A configuration `(q, z)` of `Y` (`exists_earFree_config`, on `Graph.IsPencilGoodEar.rest`)
satisfies (a), at the admissible triples `sel v` of `q`, (b), on a set `r ⊆ X` of four bodies with
independent points (`exists_linearIndepOn_extension`), and (c). Some `t₀` has chart points that are
nonzero multiples of its points (`exists_earFree_gammaL`), so the three conditions, open
(`isZariskiOpen_earFreeCond`) and unchanged by rescaling (`earFreeCond_of_smul`), hold off the zero
set of a polynomial on `Γ_L` nonzero at `t₀`. A non-root `t₁` of it and of `E_L`
(`exists_earExtend_poly`) gives parameters `s₁` of `Γ(G)` at which they hold; so they hold on a
Zariski-open set meeting `U(G)` (`steerSet_nonempty_iff`, `IsZariskiOpen.exists_mem_inter`), that
is generally (`HoldsGenerally.of_isZariskiOpen`). At a realization in `U(G)` the points of each
closed neighbourhood lie in its subspace, of dimension three, and
`earFree_of_finrank_liftSpaceTilde_le` concludes. -/
theorem holdsGenerally_earFree [Infinite K] [Finite α] [Finite β] {G : Graph α β}
    (hS : G.Simple) (hfeas : PencilNondegFeasible K G) {W₀ : Set α} {x a b : α}
    (hW : G.IsPencilGoodEar W₀ x a b) {hubSel nbrSel : α → Fin 3 → Option α}
    (hHubSel : ∀ v, IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v))
    (hNbrSel : ∀ v, ¬ G.PencilHub v → IsFin3SelectorOf (G.closedNbhd v) (nbrSel v)) :
    HoldsGenerally (K := K) G hubSel nbrSel (fun b0 P0 =>
      (∀ v ∈ W₀ \ {x},
        Module.finrank K (Submodule.span K (b0 '' (G.induce (W₀ \ {x})).closedNbhd v)) = 3) ∧
      Submodule.span K (b0 '' (W₀ \ {x})) = ⊤ ∧
      (∀ lam ∈ liftSpace (G.induce (W₀ \ {x})) b0 P0,
        IsTrivialLift (G.induce (W₀ \ {x})) b0 P0 lam)) ∧
    EarLiftCondition (K := K) G hubSel nbrSel x a b := by
  classical
  have := Fintype.ofFinite α
  obtain ⟨hF1, -⟩ := hfeas.hub_conditions
  set X := W₀ \ {x} with hX
  set Y := G.induce X with hY
  have hVY : V(Y) = X := Graph.vertexSet_induce G X
  have hYle : Y ≤ G := Graph.induce_le ((Set.sdiff_subset_sdiff_left hW.subset).trans
    Set.sdiff_subset)
  -- a configuration of `Y`, its fixed triples and a fixed quadruple
  obtain ⟨hYS, hY3, hYdef0, hYdef, hYne⟩ := hW.rest hS
  obtain ⟨q, y, hy, hadm, hgp, hpd, hspan, hdim⟩ :=
    exists_earFree_config (K := K) hYS hY3 hYdef0 hYdef hYne
  set bc := pencilConfigPoint q (fun a => y (Sum.inl a)) with hbc
  choose! sel hsel using hadm.2
  have hselV : ∀ v ∈ V(Y), ∀ i, sel v i ∈ V(Y) := fun v hv i =>
    Graph.closedNbhd_subset_vertexSet hv ((hsel v hv).1 i)
  obtain ⟨r, hrX, -, hrspan, hrLI⟩ := exists_linearIndepOn_extension (K := K) (v := bc)
    (s := ∅) (t := V(Y)) (linearIndepOn_empty _ _) (Set.empty_subset _)
  have hr4 : r.ncard = 4 := by
    have h := finrank_span_image_of_linearIndepOn hrLI
    have htop : Submodule.span K (bc '' r) = ⊤ := by
      rw [eq_top_iff, ← hspan, Submodule.span_le]; exact hrspan
    rw [htop, finrank_top, Module.finrank_fin_fun] at h; omega
  set N := 4 + Module.finrank K (liftFreeCoords (K := K) Y) with hN
  have hcond : (∀ v ∈ V(Y), LinearIndependent K fun i => bc (sel v i)) ∧ LinearIndepOn K bc r ∧
      Module.finrank K (liftSpaceTilde Y bc) ≤ N :=
    ⟨fun v hv => linearIndependent_pencilConfigPoint_of_linearIndependent_pencilPicturePoint _
      (hsel v hv).2, hrLI, hdim.le⟩
  -- the configuration in `Γ_L`
  have hHL : ∀ v, ∃ sl : Fin 3 → Option α,
      IsFin3SelectorOf {h | h ∈ Y.closedNbhd v ∧ G.PencilHub h} sl := by
    intro v
    refine exists_isFin3SelectorOf_of_ncard_le_three ((Set.ncard_le_ncard (t := G.closedHubNbhd v)
      ?_ (Set.toFinite _)).trans (hF1 v))
    rintro h ⟨rfl | ⟨e, he⟩, hh⟩
    · exact ⟨hh, Or.inl rfl⟩
    · exact ⟨hh, Or.inr ⟨e, he.of_le hYle⟩⟩
  choose hubSelL hL using hHL
  obtain ⟨t₀, ht₀⟩ := exists_earFree_gammaL hfeas hW (fun v _ => hL v) hy hgp hpd
  have hcond₀ := earFreeCond_of_smul (B' := steerPoint hubSelL t₀) hselV hrX
    (fun v hv => ht₀ v hv) hcond
  obtain ⟨RL, hRL0, hRL⟩ := isZariskiOpen_earFreeCond (isPolyFun_steerPoint hubSelL) Y sel r N
    t₀ hcond₀
  -- into `Γ(G)` by `E_L`
  obtain ⟨E, ⟨t', ht'⟩, hE⟩ := exists_earExtend_poly hfeas hW hHubSel (fun v _ => hL v)
  obtain ⟨t₁, ht₁E, ht₁R⟩ := IsZariskiOpen.exists_mem_inter (isZariskiOpen_eval_ne_zero E)
    (isZariskiOpen_eval_ne_zero RL) (show t' ∈ {t | MvPolynomial.eval t E ≠ 0} from ht') hRL0
  obtain ⟨s₁, hs₁⟩ := hE t₁ ht₁E
  have hcond₁ := earFreeCond_of_smul (B' := steerPoint hubSel s₁) hselV hrX
    (fun v hv => hs₁ v hv) (hRL t₁ ht₁R)
  have hopen := isZariskiOpen_earFreeCond (isPolyFun_steerPoint (K := K) hubSel) Y sel r N
  obtain ⟨s₀, hs₀⟩ := (steerSet_nonempty_iff (K := K) hHubSel hNbrSel).2 hfeas
  obtain ⟨s₂, hs₂U, hs₂C⟩ := IsZariskiOpen.exists_mem_inter
    (isZariskiOpen_steerSet hHubSel hNbrSel) hopen hs₀ hcond₁
  -- the conclusion at a general realization
  have H := HoldsGenerally.of_isZariskiOpen (K := K) (G := G) (hubSel := hubSel) (nbrSel := nbrSel)
    (p := fun b0 P0 => ((∀ v ∈ X,
        Module.finrank K (Submodule.span K (b0 '' Y.closedNbhd v)) = 3) ∧
      Submodule.span K (b0 '' X) = ⊤ ∧
      (∀ lam ∈ liftSpace Y b0 P0, IsTrivialLift Y b0 P0 lam)) ∧
      ∀ lam ∈ liftSpace (G.induce (V(G) \ {x})) b0 P0, ∀ (ha : b0 x ∈ P0 a) (hb : b0 x ∈ P0 b),
        lam.2 a ⟨b0 x, ha⟩ = lam.2 b ⟨b0 x, hb⟩) hopen hs₂U hs₂C fun s hsU hsC => by
    obtain ⟨hC1, hC2, hC3⟩ := hsC
    refine earFree_of_finrank_liftSpaceTilde_le hS hW (fun v _ w hw =>
      mem_dotPerp_span_singleton.2 (steerPoint_dotProduct_steerNormal hHubSel hNbrSel s hw))
      (fun v hv => (finrank_dotPerp_span_singleton_of_ne_zero (hsU.1 v hv).2).le)
      (fun v hv => ?_) ?_ hC3
    · have hli := hC1 v hv
      have h3 := finrank_span_eq_card hli
      rw [Fintype.card_fin] at h3
      rw [← h3]
      refine Submodule.finrank_mono (Submodule.span_mono ?_)
      rintro _ ⟨i, rfl⟩
      exact ⟨sel v i, (hsel v hv).1 i, rfl⟩
    · have h := finrank_span_image_of_linearIndepOn hC2
      rw [hr4] at h
      have htop : Submodule.span K (steerPoint hubSel s '' r) = ⊤ :=
        Submodule.eq_top_of_finrank_eq (by rw [h, Module.finrank_fin_fun])
      rw [eq_top_iff, ← htop]
      exact Submodule.span_mono (Set.image_mono hrX)
  exact ⟨H.mono fun _ _ h => h.1, H.mono fun _ _ h => h.2⟩

end CombinatorialRigidity.Molecular
