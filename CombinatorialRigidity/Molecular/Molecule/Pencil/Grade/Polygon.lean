module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Embedding
public import CombinatorialRigidity.Mathlib.Data.Fin.Basic
public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Carrier

/-!
# Closed polygons with independent joins, in every dimension

The polygon half of `blueprint/src/chapter/pencil-d.tex`, `sec:pencil-d-long`: the five nodes
`lem:pencil-d-polygon-normal`, `lem:pencil-d-polygon-star`, `lem:pencil-d-polygon-insert`,
`lem:pencil-d-polygons` and `lem:pencil-d-polygon-collapse`, the placements behind a long cycle and
a long open ear in dimension `d = k + 1` (Phase 40's `d = 3` hexagon made `d`-general). The
constructions are those of the CERT workbook (`notes/attacks/cert/workbook.md`), S1, S2, S4, S5, S6
and S7, as the chapter cites them.

A *closed `n`-gon* is `Y : Fin n → Fin (k + 2) → K` (`[NeZero n]`), with indices read cyclically in
`Fin n`. Its *joins* are `normalsJoin (Y j) (Y (j + 1))` (`def:join`), and it has *independent
joins* when they are linearly independent. There is no polygon definition: the carrier is the
function and the predicate is `LinearIndependent K fun j => normalsJoin (Y j) (Y (j + 1))`. The
points `gradeMk 0 0 0 1`, `gradeMk 1 0 0 1`, `gradeMk 0 1 0 1` are the chapter's `P₀`, `P₁`, `P₂`,
and `screwDim (m + 1)` is `D`.

* `linearIndependent_polygon_vertices` and `exists_linearEquiv_polygon_normal`:
  `lem:pencil-d-polygon-normal`, parts (1) and (2). Three consecutive vertices are independent,
  and a last-coordinate-preserving linear equivalence puts them at `P₁, P₀, P₂`.
* `exists_normalsJoin_notMem_span_polygon`: `lem:pencil-d-polygon-star`, a vertex and a vector
  whose join leaves the span of the polygon's joins, when `n < D`.
* `exists_insertNth_linearIndependent_join`: `lem:pencil-d-polygon-insert`, a vertex inserted after
  `Y i` keeps the joins independent, over a field of at least four elements.
* `exists_polygon_linearIndependent_join`: `lem:pencil-d-polygons`, an `n`-gon with independent
  joins and `Y (-1), Y 0, Y 1 = P₁, P₀, P₂`, for `3 ≤ n ≤ D`.
* `polygonCollapse`, `polygonCollapseEdge` and their lemmas: `lem:pencil-d-polygon-collapse`, at
  index level. The chapter's closed `D`-gon `Y` is not in these statements: a consumer places the
  body `c j` at `Y (polygonCollapse D M j)`, and the lemmas say which `D` edges of the cycle on `M`
  bodies carry the joins `J_0, ..., J_{D-1}`.

Helpers: `normalsJoin` is linear in its second argument too (`normalsJoin_add_right`,
`normalsJoin_smul_right`), vanishes at `0` (`normalsJoin_zero_left`) and has every 2 × 2 minor as a
linear functional on `⋀²` (`exists_linearMap_normalsJoin_eq`), which is how the star and the base
triangle avoid a basis of `⋀²`. The `Fin` index lemmas for the insertion are in
`Mathlib/Data/Fin/Basic.lean`.
-/

@[expose] public section

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {k m : ℕ}

/-! ## Joins: linearity in the second normal, and a minor -/

/-- The join is additive in its second argument, by antisymmetry from `normalsJoin_add_left`. -/
theorem normalsJoin_add_right (a b c : Fin (k + 2) → K) :
    normalsJoin a (b + c) = normalsJoin (k := k) a b + normalsJoin a c := by
  rw [normalsJoin_swap, normalsJoin_add_left, neg_add, ← normalsJoin_swap, ← normalsJoin_swap]

/-- The join is homogeneous in its second argument, by antisymmetry from `normalsJoin_smul_left`. -/
theorem normalsJoin_smul_right (t : K) (a b : Fin (k + 2) → K) :
    normalsJoin a (t • b) = t • normalsJoin (k := k) a b := by
  rw [normalsJoin_swap, normalsJoin_smul_left, normalsJoin_swap b a, smul_neg]

/-- Every `2 × 2` minor of two linear functionals is a linear functional on `⋀²`: `φ (a ∨ b) = ψ₁ a
* ψ₂ b - ψ₂ a * ψ₁ b`. It is the determinant of the alternating map `![a, b] ↦ ![ψ₁, ψ₂]`, and
detects independence of joins without a basis of `⋀²`. -/
theorem exists_linearMap_normalsJoin_eq (ψ₁ ψ₂ : (Fin (k + 2) → K) →ₗ[K] K) :
    ∃ φ : ⋀[K]^2 (Fin (k + 2) → K) →ₗ[K] K,
      ∀ a b, φ (normalsJoin a b) = ψ₁ a * ψ₂ b - ψ₂ a * ψ₁ b := by
  refine ⟨exteriorPower.alternatingMapLinearEquiv
    ((Matrix.detRowAlternating : (Fin 2 → K) [⋀^Fin 2]→ₗ[K] K).compLinearMap
      (LinearMap.pi ![ψ₁, ψ₂])), fun a b => ?_⟩
  rw [normalsJoin, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  change Matrix.det (Matrix.of fun i => LinearMap.pi ![ψ₁, ψ₂] (![a, b] i)) = _
  simp [Matrix.det_fin_two]

/-! ## Three consecutive vertices (`lem:pencil-d-polygon-normal`) -/

/-- `lem:pencil-d-polygon-normal`, part (1) (CERT workbook, S1). In a closed `n`-gon with `3 ≤ n`
and independent joins, any three consecutive vertices `Y (i - 1)`, `Y i`, `Y (i + 1)` are
linearly independent. The join `J (i - 1)` is nonzero, so the first two are independent; a
relation `Y (i + 1) = α Y (i - 1) + β Y i` makes `J i = -α J (i - 1)`, a nontrivial relation
among joins at the distinct indices `i - 1` and `i` (distinct since `3 ≤ n`). -/
theorem linearIndependent_polygon_vertices {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    {Y : Fin n → Fin (k + 2) → K}
    (hY : LinearIndependent K fun j => normalsJoin (Y j) (Y (j + 1))) (i : Fin n) :
    LinearIndependent K ![Y (i - 1), Y i, Y (i + 1)] := by
  have hne : i - 1 ≠ i := by
    intro h
    have h1 : (1 : Fin n) = 0 := by
      have := congrArg (fun x => i - x) h
      simpa using this
    have := congrArg Fin.val h1
    rw [Fin.val_one', Fin.val_zero, Nat.one_mod_eq_one.mpr (by omega)] at this
    exact one_ne_zero this
  have hpair : LinearIndependent K
      ![normalsJoin (Y (i - 1)) (Y i), normalsJoin (Y i) (Y (i + 1))] := by
    have h := hY.comp ![i - 1, i] (by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [eq_comm])
    convert h using 1
    funext j; fin_cases j <;> simp
  have h2 : LinearIndependent K ![Y (i - 1), Y i] :=
    (normalsJoin_ne_zero_iff _ _).1 (hpair.ne_zero 0)
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at hg
  by_cases h3 : g 2 = 0
  · rw [h3, zero_smul, add_zero] at hg
    have := LinearIndependent.pair_iff.1 h2 _ _ hg
    intro j; fin_cases j
    exacts [this.1, this.2, h3]
  · exfalso
    have hrel : (-g 0) • normalsJoin (Y (i - 1)) (Y i)
        + g 2 • normalsJoin (Y i) (Y (i + 1)) = 0 := by
      have e : g 2 • Y (i + 1) = -(g 0 • Y (i - 1) + g 1 • Y i) := eq_neg_of_add_eq_zero_right hg
      have e2 : g 2 • normalsJoin (Y i) (Y (i + 1)) = g 0 • normalsJoin (Y (i - 1)) (Y i) := by
        rw [← normalsJoin_smul_right, e, ← neg_one_smul K, normalsJoin_smul_right,
          normalsJoin_add_right, normalsJoin_smul_right, normalsJoin_smul_right, normalsJoin_self,
          smul_zero, add_zero, normalsJoin_swap (Y i), smul_smul, smul_neg, ← neg_smul]
        simp
      rw [e2, ← add_smul, neg_add_cancel, zero_smul]
    exact h3 (LinearIndependent.pair_iff.1 hpair _ _ hrel).2

/-- The chapter's `P₁`, `P₀`, `P₂` are linearly independent: read off the coordinates `0`, `1` and
the last. -/
theorem linearIndependent_gradeMk_P :
    LinearIndependent K ![(gradeMk 1 0 0 1 : Fin (m + 1 + 2) → K), gradeMk 0 0 0 1,
      gradeMk 0 1 0 1] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at hg
  have h0 := congrFun hg 0
  have h1 := congrFun hg 1
  have hl := congrFun hg (Fin.last (m + 2))
  simp at h0 h1 hl
  intro j; fin_cases j <;> simp <;> grind

/-- `lem:pencil-d-polygon-normal`, part (2) (CERT workbook, S2 (a)). For a closed `n`-gon with
independent joins and every vertex of last coordinate `1`, and any index `i`, a linear
equivalence `g` of the ambient space keeps the last coordinate, sends `Y (i - 1)`, `Y i`, `Y (i
+ 1)` to `P₁`, `P₀`, `P₂`, and the polygon `g (Y j)` has independent joins and last coordinates
`1`. The route differs from the chapter's `(M (x̄ - ω ȳ_i), ω)`: extend the basis map of part
(1) to an equivalence `g₁` (`Submodule.exists_linearEquiv_restrict_eq`), then correct its last
coordinate by the transvection `v ↦ v + φ v • P₀` with `φ = f ∘ g₁⁻¹ - f`, `f` the last
coordinate (`φ` vanishes on `P₁, P₀, P₂`). The joins map by `exteriorPower_map_normalsJoin`, and
the induced map of `⋀²` is injective, as `g⁻¹` induces its inverse. -/
theorem exists_linearEquiv_polygon_normal {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    {Y : Fin n → Fin (m + 1 + 2) → K} (hY1 : ∀ j, Y j (Fin.last (m + 2)) = 1)
    (hY : LinearIndependent K fun j => normalsJoin (Y j) (Y (j + 1))) (i : Fin n) :
    ∃ g : (Fin (m + 1 + 2) → K) ≃ₗ[K] (Fin (m + 1 + 2) → K),
      (∀ v, g v (Fin.last (m + 2)) = v (Fin.last (m + 2))) ∧
      g (Y (i - 1)) = gradeMk 1 0 0 1 ∧ g (Y i) = gradeMk 0 0 0 1 ∧
      g (Y (i + 1)) = gradeMk 0 1 0 1 ∧
      LinearIndependent K (fun j => normalsJoin (g (Y j)) (g (Y (j + 1)))) ∧
      ∀ j, g (Y j) (Fin.last (m + 2)) = 1 := by
  set P : Fin 3 → Fin (m + 1 + 2) → K := ![gradeMk 1 0 0 1, gradeMk 0 0 0 1, gradeMk 0 1 0 1]
    with hPdef
  set T : Fin 3 → Fin (m + 1 + 2) → K := ![Y (i - 1), Y i, Y (i + 1)] with hTdef
  have hT : LinearIndependent K T := linearIndependent_polygon_vertices hn hY i
  have hP : LinearIndependent K P := linearIndependent_gradeMk_P
  obtain ⟨g₁, hg₁⟩ := Submodule.exists_linearEquiv_restrict_eq
    ((Module.Basis.span hT).equiv (Module.Basis.span hP) (Equiv.refl _))
  have hg₁T : ∀ a, g₁ (T a) = P a := by
    intro a
    have := hg₁ (Module.Basis.span hT a)
    rw [Module.Basis.equiv_apply, Equiv.refl_apply, Module.Basis.span_apply,
      Module.Basis.span_apply] at this
    exact this.symm
  -- the last coordinate, and the transvection correcting it
  set f : (Fin (m + 1 + 2) → K) →ₗ[K] K := LinearMap.proj (Fin.last (m + 2)) with hfdef
  set φ : (Fin (m + 1 + 2) → K) →ₗ[K] K := f ∘ₗ g₁.symm.toLinearMap - f with hφdef
  have hfP : ∀ a, f (P a) = 1 := by intro a; fin_cases a <;> simp [hfdef, hPdef]
  have hfT : ∀ a, f (T a) = 1 := by intro a; fin_cases a <;> simp [hfdef, hTdef, hY1]
  have hφP : ∀ a, φ (P a) = 0 := by
    intro a
    have e := hg₁T a
    simp only [hφdef, LinearMap.sub_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← e, LinearEquiv.symm_apply_apply, hfT, e, hfP, sub_self]
  have hφ0 : φ (P 1) = 0 := hφP 1
  set h : (Fin (m + 1 + 2) → K) ≃ₗ[K] (Fin (m + 1 + 2) → K) :=
    LinearEquiv.ofLinearMap (LinearMap.id + φ.smulRight (P 1))
      (LinearMap.id - φ.smulRight (P 1))
      (LinearMap.ext fun v => by
        simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
          LinearMap.id_apply, LinearMap.smulRight_apply, map_sub, map_smul, hφ0]
        module)
      (LinearMap.ext fun v => by
        simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
          LinearMap.id_apply, LinearMap.smulRight_apply, map_add, map_smul, hφ0]
        module) with hhdef
  have hgT : ∀ a, (g₁.trans h) (T a) = P a := by
    intro a
    simp [hg₁T, hhdef, hφP]
  have hh : ∀ x, h x = x + φ x • P 1 := fun x => by
    rw [hhdef, LinearEquiv.coe_ofLinearMap]
    rfl
  have hlast : ∀ v, (g₁.trans h) v (Fin.last (m + 2)) = v (Fin.last (m + 2)) := by
    intro v
    have h1 : P 1 (Fin.last (m + 2)) = 1 := hfP 1
    rw [LinearEquiv.trans_apply, hh, Pi.add_apply, Pi.smul_apply, h1, smul_eq_mul, mul_one]
    simp only [hφdef, LinearMap.sub_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, hfdef, LinearMap.proj_apply]
    ring
  have hker : LinearMap.ker (exteriorPower.map 2 (g₁.trans h).toLinearMap) = ⊥ := by
    refine LinearMap.ker_eq_bot_of_inverse (g := exteriorPower.map 2 (g₁.trans h).symm.toLinearMap)
      ?_
    rw [← exteriorPower.map_comp, LinearEquiv.symm_comp, exteriorPower.map_id]
  refine ⟨g₁.trans h, hlast, hgT 0, hgT 1, hgT 2, ?_, fun j => by rw [hlast, hY1]⟩
  have := hY.map' _ hker
  convert this using 1
  funext j
  simp only [Function.comp_apply, LinearEquiv.coe_coe, exteriorPower_map_normalsJoin]


/-! ## A line through a vertex off the span of the joins (`lem:pencil-d-polygon-star`) -/

/-- The exterior square of `K^(k+2)` has dimension `D = screwDim k`. -/
theorem finrank_exteriorPower_two_eq_screwDim :
    Module.finrank K (⋀[K]^2 (Fin (k + 2) → K)) = screwDim k := by
  rw [exteriorPower.finrank_eq, Module.finrank_pi, Fintype.card_fin]

/-- The join with a zero first argument vanishes. -/
theorem normalsJoin_zero_left (b : Fin (k + 2) → K) : normalsJoin (0 : Fin (k + 2) → K) b = 0 := by
  simpa using normalsJoin_smul_left (0 : K) (0 : Fin (k + 2) → K) b

/-- `lem:pencil-d-polygon-star` (CERT workbook, S4). A closed `n`-gon with independent joins and `n
< D = screwDim k` has a vertex `Y i` and a vector `u` with `Y i ∨ u` outside the span `W(Y)` of
its joins. If the vertices span the space, every join lies in `W(Y)` by linearity in the first
point, and the joins span `⋀²` (`exteriorPower.ιMulti_span`), against `dim W(Y) = n < D`.
Otherwise take `u` outside the span `S` of the vertices, a functional `ψ₂` vanishing on `S` but
not at `u`, and `ψ₁` with `ψ₁ (Y 0) ≠ 0` (`Y 0 ≠ 0` as `J 0 ≠ 0`); the minor `ψ₁ a * ψ₂ b - ψ₂ a
* ψ₁ b` kills `W(Y)` but not `Y 0 ∨ u`. This replaces the chapter's two basis arguments; the
only input from `lem:pencil-d-polygon-normal` is the nonvanishing of `J 0`. -/
theorem exists_normalsJoin_notMem_span_polygon {n : ℕ} [NeZero n]
    {Y : Fin n → Fin (k + 2) → K}
    (hY : LinearIndependent K fun j => normalsJoin (Y j) (Y (j + 1))) (hnD : n < screwDim k) :
    ∃ i u, normalsJoin (Y i) u ∉
      Submodule.span K (Set.range fun j => normalsJoin (Y j) (Y (j + 1))) := by
  set W := Submodule.span K (Set.range fun j => normalsJoin (Y j) (Y (j + 1))) with hW
  have hWn : Module.finrank K W = n := by
    rw [hW, finrank_span_eq_card hY, Fintype.card_fin]
  by_cases hS : Submodule.span K (Set.range Y) = ⊤
  · by_contra! hcon
    have hall : ∀ a b, normalsJoin a b ∈ W := by
      intro a b
      have ha : a ∈ Submodule.span K (Set.range Y) := hS ▸ Submodule.mem_top
      induction ha using Submodule.span_induction with
      | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hcon i b
      | zero => rw [normalsJoin_zero_left]; exact W.zero_mem
      | add x y _ _ hx hy => rw [normalsJoin_add_left]; exact W.add_mem hx hy
      | smul t x _ hx => rw [normalsJoin_smul_left]; exact W.smul_mem t hx
    have htop : W = ⊤ := by
      rw [eq_top_iff, ← exteriorPower.ιMulti_span, Submodule.span_le]
      rintro _ ⟨v, rfl⟩
      have hv : v = ![v 0, v 1] := by funext j; fin_cases j <;> rfl
      rw [hv]
      exact hall _ _
    have := hWn
    rw [htop, finrank_top, finrank_exteriorPower_two_eq_screwDim] at this
    omega
  · obtain ⟨u, hu⟩ : ∃ u, u ∉ Submodule.span K (Set.range Y) := by
      by_contra! h
      exact hS (eq_top_iff.2 fun x _ => h x)
    have hY0 : Y 0 ≠ 0 := by
      intro h
      have := hY.ne_zero 0
      rw [h, normalsJoin_zero_left] at this
      exact this rfl
    obtain ⟨ψ₁, hψ₁⟩ : ∃ ψ₁ : Module.Dual K (Fin (k + 2) → K), ψ₁ (Y 0) ≠ 0 := by
      by_contra! h
      exact hY0 ((Module.forall_dual_apply_eq_zero_iff K (Y 0)).1 h)
    obtain ⟨ψ₂, hψ₂u, hψ₂S⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hu inferInstance
    have hψ₂Y : ∀ j, ψ₂ (Y j) = 0 := by
      intro j
      have : ψ₂ (Y j) ∈ (Submodule.span K (Set.range Y)).map ψ₂ :=
        Submodule.mem_map_of_mem (Submodule.subset_span ⟨j, rfl⟩)
      rwa [hψ₂S, Submodule.mem_bot] at this
    obtain ⟨φ, hφ⟩ := exists_linearMap_normalsJoin_eq ψ₁ ψ₂
    refine ⟨0, u, fun hmem => ?_⟩
    have hφW : W ≤ LinearMap.ker φ := by
      rw [hW, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      simp [hφ, hψ₂Y]
    have := hφW hmem
    rw [LinearMap.mem_ker, hφ, hψ₂Y, zero_mul, sub_zero] at this
    exact mul_ne_zero hψ₁ hψ₂u this

/-! ## Inserting a vertex (`lem:pencil-d-polygon-insert`) -/

/-- A line `v + t • w` with `v ∉ S` meets the subspace `S` for at most one parameter `t`: two such
parameters force `w ∈ S`, hence `v ∈ S`. -/
theorem eq_of_add_smul_mem_of_add_smul_mem {V : Type*} [AddCommGroup V] [Module K V]
    {S : Submodule K V} {v : V} (hv : v ∉ S) (w : V) {t₁ t₂ : K} (h₁ : v + t₁ • w ∈ S)
    (h₂ : v + t₂ • w ∈ S) : t₁ = t₂ := by
  by_contra hne
  have hw : w ∈ S := by
    have := S.sub_mem h₁ h₂
    rw [show v + t₁ • w - (v + t₂ • w) = (t₁ - t₂) • w by module] at this
    exact (S.smul_mem_iff (sub_ne_zero.2 hne)).1 this
  exact hv (by simpa using S.sub_mem h₁ (S.smul_mem t₁ hw))

/-- `lem:pencil-d-polygon-insert` (CERT workbook, S5). Let `K` have at least four elements, `Y` be a
closed `n`-gon with independent joins and last coordinates `1`, and `Y i ∨ u ∉ W(Y)`. Then some
`y` of last coordinate `1` makes the `(n + 1)`-gon with `y` inserted after `Y i` (`Fin.insertNth
i.succ y Y`) have independent joins. Take `y = (Y i + t u) / (1 + t ω)`, `ω` the last coordinate
of `u`, for `t` outside `{0, -ω⁻¹}` and the one bad value. The new joins are multiples of the
family `(J j)_{j ≠ i}, Y i ∨ u, J i + t (u ∨ Y (i + 1))`, which is independent unless `J i + t
(u ∨ Y (i + 1))` lies in the span `A` of the other `n` members; since `J i ∉ A`, that happens
for at most one `t` (`eq_of_add_smul_mem_of_add_smul_mem`), in place of the chapter's minor
`δ(t)`. -/
theorem exists_insertNth_linearIndependent_join (hK : 4 ≤ ENat.card K) {n : ℕ} [NeZero n]
    {Y : Fin n → Fin (k + 2) → K} (hY1 : ∀ j, Y j (Fin.last (k + 1)) = 1)
    (hY : LinearIndependent K fun j => normalsJoin (Y j) (Y (j + 1)))
    {i : Fin n} {u : Fin (k + 2) → K}
    (hu : normalsJoin (Y i) u ∉
      Submodule.span K (Set.range fun j => normalsJoin (Y j) (Y (j + 1)))) :
    ∃ y : Fin (k + 2) → K, y (Fin.last (k + 1)) = 1 ∧
      LinearIndependent K fun j : Fin (n + 1) =>
        normalsJoin ((Fin.insertNth i.succ y Y : Fin (n + 1) → Fin (k + 2) → K) j)
          ((Fin.insertNth i.succ y Y : Fin (n + 1) → Fin (k + 2) → K) (j + 1)) := by
  classical
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne n)
  set J : Fin (n + 1) → ⋀[K]^2 (Fin (k + 2) → K) := fun j => normalsJoin (Y j) (Y (j + 1))
    with hJ
  set R := Submodule.span K (J '' {i}ᶜ) with hR
  have hJiR : J i ∉ R := hY.notMem_span_image (by simp)
  have hrange : Set.range J = insert (J i) (J '' {i}ᶜ) := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      by_cases hj : j = i
      · exact Or.inl (by rw [hj])
      · exact Or.inr ⟨j, hj, rfl⟩
    · rintro (rfl | ⟨j, -, rfl⟩) <;> exact ⟨_, rfl⟩
  have hWn : Module.finrank K (Submodule.span K (Set.range J)) = n + 1 := by
    rw [finrank_span_eq_card hY, Fintype.card_fin]
  have hRn : Module.finrank K R + 1 = n + 1 := by
    rw [← hWn, hrange, Submodule.span_insert, sup_comm, Submodule.finrank_sup_span_singleton hJiR]
  set a := normalsJoin (Y i) u with ha
  have haW : a ∉ Submodule.span K (insert (J i) (J '' {i}ᶜ)) := by rwa [← hrange]
  set A := Submodule.span K (insert a (J '' {i}ᶜ)) with hA
  have haR : a ∉ R := fun h => haW (Submodule.span_mono (Set.subset_insert _ _) h)
  have hAn : Module.finrank K A = Module.finrank K R + 1 := by
    rw [hA, Submodule.span_insert, sup_comm, Submodule.finrank_sup_span_singleton haR]
  have hJiA : J i ∉ A := fun h => haW (mem_span_insert_exchange h hJiR)
  set w := normalsJoin u (Y (i + 1)) with hw
  set ω := u (Fin.last (k + 1)) with hω
  set t₀ : K := if h : ∃ t : K, J i + t • w ∈ A then h.choose else 0 with ht₀
  obtain ⟨t, ht⟩ := Finset.exists_notMem_of_card_lt_enatCard (s := {0, -ω⁻¹, t₀}) (by
    refine lt_of_lt_of_le ?_ hK
    exact_mod_cast Nat.lt_of_le_of_lt Finset.card_le_three (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
  obtain ⟨ht0, htω, htt₀⟩ := ht
  have hc : 1 + t * ω ≠ 0 := by
    intro h
    have hω0 : ω ≠ 0 := by rintro h0; rw [h0, mul_zero, add_zero] at h; exact one_ne_zero h
    exact htω (by field_simp; linear_combination h)
  have hbad : J i + t • w ∉ A := by
    intro hmem
    have hex : ∃ t : K, J i + t • w ∈ A := ⟨t, hmem⟩
    have := eq_of_add_smul_mem_of_add_smul_mem hJiA w hmem hex.choose_spec
    exact htt₀ (by rw [ht₀, dite_eq_left hex]; exact this)
  set c := 1 + t * ω with hcdef
  set y : Fin (k + 2) → K := c⁻¹ • (Y i + t • u) with hy
  refine ⟨y, ?_, ?_⟩
  · simp only [hy, Pi.smul_apply, Pi.add_apply, hY1, smul_eq_mul, ← hω, ← hcdef]
    exact inv_mul_cancel₀ hc
  set Z := Fin.insertNth (α := fun _ => Fin (k + 2) → K) i.succ y Y with hZ
  set NJ := fun j : Fin (n + 1 + 1) => normalsJoin (Z j) (Z (j + 1)) with hNJ
  set S := Submodule.span K (Set.range NJ) with hS
  have hRS : R ≤ S := by
    rw [hR, Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩
    refine Submodule.subset_span ⟨i.succ.succAbove j, ?_⟩
    simp only [hNJ, hZ, hJ]
    rw [Fin.succ_succAbove_add_one i j hj, Fin.insertNth_apply_succAbove,
      Fin.insertNth_apply_succAbove]
  have hNJi : NJ i.castSucc = (c⁻¹ * t) • a := by
    simp only [hNJ, hZ]
    rw [Fin.coeSucc_eq_succ, Fin.insertNth_apply_same, ← Fin.succ_succAbove_self,
      Fin.insertNth_apply_succAbove, hy, normalsJoin_smul_right, normalsJoin_add_right,
      normalsJoin_self, zero_add, normalsJoin_smul_right, smul_smul]
  have hNJs : NJ i.succ = c⁻¹ • (J i + t • w) := by
    simp only [hNJ, hZ, hJ, hw]
    rw [Fin.succ_add_one_eq_succAbove, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove,
      hy, normalsJoin_smul_left, normalsJoin_add_left, normalsJoin_smul_left]
  have haS : a ∈ S := by
    have : (c⁻¹ * t)⁻¹ • NJ i.castSucc = a := by
      rw [hNJi, smul_smul, inv_mul_cancel₀ (mul_ne_zero (inv_ne_zero hc) ht0), one_smul]
    rw [← this]
    exact S.smul_mem _ (Submodule.subset_span ⟨_, rfl⟩)
  have hJS : J i + t • w ∈ S := by
    have : c • NJ i.succ = J i + t • w := by rw [hNJs, smul_smul, mul_inv_cancel₀ hc, one_smul]
    rw [← this]
    exact S.smul_mem _ (Submodule.subset_span ⟨_, rfl⟩)
  have hAS : A ⊔ K ∙ (J i + t • w) ≤ S := by
    refine sup_le ?_ ((Submodule.span_singleton_le_iff_mem _ _).2 hJS)
    rw [hA, Submodule.span_le]
    rintro _ (rfl | hx)
    · exact haS
    · exact hRS (Submodule.subset_span hx)
  rw [linearIndependent_iff_card_le_finrank_span, Fintype.card_fin, Set.finrank]
  have := Submodule.finrank_mono hAS
  rw [Submodule.finrank_sup_span_singleton hbad, hAn] at this
  change _ ≤ Module.finrank K S
  omega

/-! ## Closed polygons with independent joins (`lem:pencil-d-polygons`) -/

/-- The base case of `lem:pencil-d-polygons`: the triangle `(P₀, P₁, P₂)` has independent joins.
Three `2 × 2` minors (`exists_linearMap_normalsJoin_eq`, on the coordinate pairs `0, 1`, `0,
last` and `1, last`) separate the three joins, in place of the chapter's basis of `⋀²`. -/
theorem linearIndependent_join_triangle :
    LinearIndependent K fun j : Fin 3 =>
      normalsJoin ((![gradeMk 0 0 0 1, gradeMk 1 0 0 1, gradeMk 0 1 0 1] :
        Fin 3 → Fin (m + 1 + 2) → K) j)
        ((![gradeMk 0 0 0 1, gradeMk 1 0 0 1, gradeMk 0 1 0 1] :
          Fin 3 → Fin (m + 1 + 2) → K) (j + 1)) := by
  obtain ⟨φ01, h01⟩ := exists_linearMap_normalsJoin_eq (K := K) (k := m + 1)
    (LinearMap.proj 0) (LinearMap.proj 1)
  obtain ⟨φ0L, h0L⟩ := exists_linearMap_normalsJoin_eq (K := K) (k := m + 1)
    (LinearMap.proj 0) (LinearMap.proj (Fin.last (m + 2)))
  obtain ⟨φ1L, h1L⟩ := exists_linearMap_normalsJoin_eq (K := K) (k := m + 1)
    (LinearMap.proj 1) (LinearMap.proj (Fin.last (m + 2)))
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have e01 := congrArg φ01 hg
  have e0L := congrArg φ0L hg
  have e1L := congrArg φ1L hg
  simp [Fin.sum_univ_three, h01, h0L, h1L] at e01 e0L e1L
  intro j; fin_cases j <;> simp <;> grind

/-- The induction behind `lem:pencil-d-polygons`: for every `n` with `n + 3 ≤ D`, an `(n + 3)`-gon
with independent joins and last coordinates `1`. The base is the triangle
(`linearIndependent_join_triangle`), the step the star and the insertion
(`exists_normalsJoin_notMem_span_polygon`, `exists_insertNth_linearIndependent_join`). -/
theorem exists_polygon_linearIndependent_join_aux (hK : 4 ≤ ENat.card K) :
    ∀ n : ℕ, n + 3 ≤ screwDim (m + 1) → ∃ Y : Fin (n + 3) → Fin (m + 1 + 2) → K,
      (∀ j, Y j (Fin.last (m + 2)) = 1) ∧
        LinearIndependent K fun j => normalsJoin (Y j) (Y (j + 1))
  | 0, _ => ⟨![gradeMk 0 0 0 1, gradeMk 1 0 0 1, gradeMk 0 1 0 1],
      fun j => by fin_cases j <;> simp, linearIndependent_join_triangle⟩
  | n + 1, h => by
    obtain ⟨Y, hY1, hY⟩ := exists_polygon_linearIndependent_join_aux hK n (by omega)
    obtain ⟨i, u, hu⟩ := exists_normalsJoin_notMem_span_polygon hY (by omega)
    obtain ⟨y, hy1, hy⟩ := exists_insertNth_linearIndependent_join hK hY1 hY hu
    refine ⟨Fin.insertNth i.succ y Y, fun j => ?_, hy⟩
    refine Fin.succAboveCases i.succ ?_ (fun j => ?_) j
    · rw [Fin.insertNth_apply_same]; exact hy1
    · rw [Fin.insertNth_apply_succAbove]; exact hY1 j

/-- `lem:pencil-d-polygons` (CERT workbook, S6 (C1), with S2 (a) at `i = 0`). Over a field of at
least four elements, for every `3 ≤ n ≤ D = screwDim (m + 1)` there is a closed `n`-gon with
independent joins, last coordinates `1`, and `Y (-1) = P₁`, `Y 0 = P₀`, `Y 1 = P₂`: the polygon
of `exists_polygon_linearIndependent_join_aux`, moved by `exists_linearEquiv_polygon_normal` at
`i = 0`. -/
theorem exists_polygon_linearIndependent_join (hK : 4 ≤ ENat.card K) {n : ℕ} [NeZero n]
    (hn : 3 ≤ n) (hnD : n ≤ screwDim (m + 1)) :
    ∃ Y : Fin n → Fin (m + 1 + 2) → K, (∀ j, Y j (Fin.last (m + 2)) = 1) ∧
      LinearIndependent K (fun j => normalsJoin (Y j) (Y (j + 1))) ∧
      Y (-1) = gradeMk 1 0 0 1 ∧ Y 0 = gradeMk 0 0 0 1 ∧ Y 1 = gradeMk 0 1 0 1 := by
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 3 := ⟨n - 3, by omega⟩
  obtain ⟨Y, hY1, hY⟩ := exists_polygon_linearIndependent_join_aux hK n hnD
  obtain ⟨g, -, h0, h1, h2, hli, hlast⟩ := exists_linearEquiv_polygon_normal hn hY1 hY 0
  rw [zero_sub] at h0
  rw [zero_add] at h2
  exact ⟨fun j => g (Y j), hlast, hli, h0, h1, h2⟩

/-! ## A long cycle or ear on a closed polygon (`lem:pencil-d-polygon-collapse`) -/

/-- `π_M` of `lem:pencil-d-polygon-collapse` (CERT workbook, S7), at index level: the map from the
`M` bodies of a long cycle (or the `M = k + 1` bodies `c_0, ..., c_k` of an ear) to the `N`
vertices of a closed `N`-gon, `j ↦ N - 1` if `j + 1 = M`, else `min j (N - 2)`. The bodies
`c_{N-2}, ..., c_{M-2}` share the vertex `N - 2`, and the last body sits at `N - 1`. A consumer
places the body `c j` at `Y (polygonCollapse N M j)`. -/
def polygonCollapse (N M : ℕ) [NeZero N] (j : Fin M) : Fin N :=
  ⟨if (j : ℕ) + 1 = M then N - 1 else min j (N - 2), by
    have := NeZero.pos N; split_ifs <;> omega⟩

/-- The edge of the cycle on `M` bodies carrying the join `J_l` of the `N`-gon
(`lem:pencil-d-polygon-collapse`, part (1)): `l ↦ l` for `l + 2 < N`, else `l + (M - N)` (so `N
- 2 ↦ M - 2` and `N - 1 ↦ M - 1`). The edge `e` is the one from the body `e` to the body `e +
1`. -/
def polygonCollapseEdge (N M : ℕ) [NeZero M] (l : Fin N) : Fin M :=
  ⟨(if (l : ℕ) + 2 < N then (l : ℕ) else l + (M - N)) % M, Nat.mod_lt _ (NeZero.pos M)⟩

/-- The value of `polygonCollapseEdge`: no reduction mod `M` is needed when `N ≤ M`. -/
theorem val_polygonCollapseEdge {N M : ℕ} [NeZero M] (hNM : N ≤ M) (l : Fin N) :
    (polygonCollapseEdge N M l : ℕ) = if (l : ℕ) + 2 < N then (l : ℕ) else l + (M - N) := by
  have := l.isLt
  simp only [polygonCollapseEdge]
  split_ifs <;> exact Nat.mod_eq_of_lt (by omega)

/-- The value of `polygonCollapse`, by definition. -/
theorem val_polygonCollapse {N M : ℕ} [NeZero N] (j : Fin M) :
    (polygonCollapse N M j : ℕ) = if (j : ℕ) + 1 = M then N - 1 else min j (N - 2) := rfl

/-- `lem:pencil-d-polygon-collapse`, part (1), distinctness: for `N ≤ M` the `N` edges
`polygonCollapseEdge N M l` are distinct. -/
theorem polygonCollapseEdge_injective {N M : ℕ} [NeZero M] (hNM : N ≤ M) :
    Function.Injective (polygonCollapseEdge N M) := by
  intro l l' h
  have hl := l.isLt
  have hl' := l'.isLt
  rw [Fin.ext_iff, val_polygonCollapseEdge hNM, val_polygonCollapseEdge hNM] at h
  ext
  split_ifs at h <;> omega

/-- `lem:pencil-d-polygon-collapse`, part (1), the joins. For `2 ≤ N ≤ M`, the edge `e =
polygonCollapseEdge N M l` runs from the body `e` to the body `e + 1`, and `polygonCollapse N M
e = l` and `polygonCollapse N M (e + 1) = l + 1`. So with the body `c j` at `Y (polygonCollapse
N M j)`, the join at this edge is `Y l ∨ Y (l + 1) = J_l`, and with
`polygonCollapseEdge_injective` the `N` distinct edges carry `J_0, ..., J_{N-1}`: this is how
the chapter's “their joins are `J_0, ..., J_{D-1}`” follows from the index-level statements. For
an ear (`M = k + 1`) the last edge, from `c_k` to the cyclic `c_0 = c_{k+1}`, is the edge `c_k
b` once `b` is placed at the vertex of `c_0` (`Y 0`). -/
theorem polygonCollapse_polygonCollapseEdge {N M : ℕ} [NeZero N] [NeZero M] (hN : 2 ≤ N)
    (hNM : N ≤ M) (l : Fin N) :
    polygonCollapse N M (polygonCollapseEdge N M l) = l ∧
      polygonCollapse N M (polygonCollapseEdge N M l + 1) = l + 1 := by
  obtain ⟨N, rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  obtain ⟨M, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  have hl := l.isLt
  constructor
  · rw [Fin.ext_iff, val_polygonCollapse, val_polygonCollapseEdge hNM]
    split_ifs <;> omega
  · rw [Fin.ext_iff, val_polygonCollapse, Fin.val_add_one', Fin.val_add_one',
      val_polygonCollapseEdge hNM]
    split_ifs <;> omega

/-- The value of `-1` in `Fin N` is `N - 1`. -/
theorem val_neg_one_fin {N : ℕ} [NeZero N] : ((-1 : Fin N) : ℕ) = N - 1 := by
  have := NeZero.pos N
  rcases Nat.lt_or_ge N 2 with h | h
  · obtain rfl : N = 1 := by omega
    simp
  · rw [Fin.val_neg', Fin.val_one', Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega)]

/-- `lem:pencil-d-polygon-collapse`, part (2): the first body sits at the vertex `0`
(`a` at `Y 0`). -/
theorem polygonCollapse_zero {N M : ℕ} [NeZero N] [NeZero M] (hM : 2 ≤ M) :
    polygonCollapse N M 0 = 0 := by
  rw [Fin.ext_iff, val_polygonCollapse, Fin.val_zero, Fin.val_zero]
  split_ifs <;> omega

/-- `lem:pencil-d-polygon-collapse`, part (2): the second body sits at the vertex `1` (`x_1` at `Y
1`), for `3 ≤ N` and `3 ≤ M`. -/
theorem polygonCollapse_one {N M : ℕ} [NeZero N] [NeZero M] (hN : 3 ≤ N) (hM : 3 ≤ M) :
    polygonCollapse N M 1 = 1 := by
  rw [Fin.ext_iff, val_polygonCollapse, Fin.val_one', Fin.val_one', Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]
  split_ifs <;> omega

/-- `lem:pencil-d-polygon-collapse`, part (2): the last body sits at the last vertex (`x_k` at `Y
(-1) = Y (D - 1)`, for `M = k + 1`). The end body `b` of an ear, at `Y 0`, is the consumer's
placement. -/
theorem polygonCollapse_neg_one {N M : ℕ} [NeZero N] [NeZero M] :
    polygonCollapse N M (-1) = -1 := by
  have := NeZero.pos M
  rw [Fin.ext_iff, val_polygonCollapse, val_neg_one_fin, val_neg_one_fin]
  split_ifs <;> omega

end CombinatorialRigidity.Molecular
