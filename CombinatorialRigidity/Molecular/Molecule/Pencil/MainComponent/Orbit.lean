/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.Short

/-!
# Open ears with one or two interior bodies at non-adjacent ends

The steps of the induction on the general configuration at an open ear on `V₁` with one or two
interior bodies, `a − x 0 − b` or `a − x 0 − x 1 − b`, whose ends `a` and `b` are not adjacent
(`thm:pencil-x0-open-ear-one`, `thm:pencil-x0-open-ear-two-orbit`, `sec:main-component-orbit`). An
ear is given as in `MainComponent/Ear.lean`. Both steps assume
`def₂(G[V₁]; a, b) + 2 ≤ def₂(G[V₁])`: every partition of `V₁` with `a` and `b` in one part falls at
least two below the planar deficiency of `G[V₁]`, so `a ≠ b` (`Graph.ne_of_deficiencyMerged_lt`),
which the steps therefore do not assume. With one interior body the step also assumes
`def₃(G[V₁]) ≤ def₃(G)`; with two, no bound on `def₃(G)`, but that the general configuration of
`G₁ = G.splitOff (x 1) (x 0) b (e 1)`, `G` with `x 1` suppressed and the label `e 1` of `x 0 − x 1`
relinked to `x 0 − b`, attains. The steps follow the scheme of `sec:main-component-cut`
(`MainComponent/Cut.lean`), with the ear rank formula
(`BodyHingeFramework.finrank_span_rigidityRows_ear_eq`, `lem:block-rank-ear`) for the count: they
prove the inequality `(⋆)` of `sec:main-component-short` (`MainComponent/Short.lean`) at one and at
two interior bodies, a lower bound on `dim(ρ + Λ)`, where `ρ` is the space of relative screws of `a`
and `b` in `G[V₁]` and `Λ` the span of the joins of the ear.

The hypothesis on the merged deficiency places the planes of the two ends. Suppressing the body of a
one-body ear `a − x 0 − b` on `V₁` leaves `G[V₁]` with the edge `ab` added
(`Graph.splitOff_oneEar`), whose planar deficiency is at least two below that of `G[V₁]`
(`Graph.splitOff_deficiency_add_le_of_deficiencyMerged`, `lem:splitoff-deficiency-merged`). So at a
general picture its lifting space is at least two smaller than that of `G[V₁]`, by Jackson and
Jordán's equality at `G[V₁] + ab` (`thm:pencil-jj-equality`) and
`lem:pencil-lifting-space-deficiency` at `G[V₁]`, and the two incidence functionals
`(z, h) ↦ (h_a − h_b) · (q_a, 1)` and `(z, h) ↦ (h_a − h_b) · (q_b, 1)` are independent on the
solutions of the lifting system of `G[V₁]` (`Graph.two_le_finrank_map_planeDiff`,
`lem:pencil-flag-genericity`). At a general solution the point of each end lies off the plane of the
other.

With one interior body, `(⋆)` asks no more than `dim(ρ + Λ) ≥ 2`, as `def₃(G[V₁]) ≤ def₃(G)`, and
the two joins of the ear give this at every admissible picture. A solution for `G` restricts to one
for `G[V₁]` at which `h_a − h_b` vanishes at the picture point of `x 0`, so the picture of `x 0` is
chosen together with the solution, as a point of their incidence off the zero sets of a polynomial
in the solution and of one in the picture (`exists_incidence`, `lem:pencil-one-ear-incidence`). This
gives the base configuration (`Graph.exists_oneEar_base`, `lem:pencil-one-ear-base`), stated for any
simple graph with such an ear and any polynomial in the picture, so that the step with two interior
bodies can apply it to `G₁`.

With two interior bodies the count is against `G₁`. It has the one-body ear `a − x 0 − b` on `V₁`
and the same `G[V₁]`, it is simple with `a` and `b` not adjacent, and its deficiency is at most that
of `G` (`Graph.splitOff_deficiency_le_of_eq_left`, `lem:splitoff-deficiency-reuse`). The base
configuration of `G₁`, taken where `G₁` also has its target, puts the point `y` of `x 0` on both end
planes, with the point of each end off the plane of the other, and the ear rank formula at `G₁`
gives `dim W`, `W` the span of `ρ` and the two joins of its ear. Placing `x 0` on the plane of `a`
and `x 1` on that of `b` then gains a dimension unless `W` is the whole screw space
(`exists_insertion_two`, `lem:pencil-insertion-two`), and with
`Graph.deficiency_induce_add_le_of_ear` (`lem:deficiency-ear`) this is `(⋆)` at two interior bodies.
The heights follow the points through the ear data (`def:pencil-ear-data`,
`MainComponent/EarGen.lean`), and a general ear datum gives the configuration of `G`, as in the
second stage of `sec:main-component-short`.

## Main results

* `Graph.X0Attains.of_openEar_one`: `thm:pencil-x0-open-ear-one`, if `G` satisfies the standing
  hypotheses, with an open ear `a − x 0 − b` on `V₁` whose ends are not adjacent,
  `def₃(G[V₁]) ≤ def₃(G)` and `def₂(G[V₁]; a, b) + 2 ≤ def₂(G[V₁])`, the general configuration of
  `G` attains when that of `G[V₁]` does.
* `Graph.X0Attains.of_openEar_two_of_splitOff`: `thm:pencil-x0-open-ear-two-orbit`, the same with
  two interior bodies, `a − x 0 − x 1 − b`, under the bound on the merged deficiency alone, when the
  general configurations of `G[V₁]` and of `G₁` attain.
* `Graph.exists_oneEar_base`: `lem:pencil-one-ear-base`, the base configuration of a one-body ear;
  `incidencePoly` and `eval_incidencePoly`, steps of it.
* `Graph.splitOff_oneEar`: a step of `lem:pencil-one-ear-base` and of the split-off step
  (`MainComponent/SplitOff.lean`), suppressing the body of a one-body ear leaves `G[V₁]` with the
  edge `ab` added.
* `exists_incidence`: `lem:pencil-one-ear-incidence`, an incidence meets two open conditions;
  `exists_dotProduct_eq_zero_ne_zero`, a step of it.
* `splitOff_ear_two` and `splitOff_ear_two_simple`: steps of `thm:pencil-x0-open-ear-two-orbit`,
  `G₁` has the open ear `a − x 0 − b` on `V₁`, and is simple with non-adjacent ends when `G` is.
-/

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

/-! ## Suppressing the body of a one-body ear -/

/-- **Suppressing the body of a one-body ear** (a step of `lem:pencil-one-ear-base`,
`lem:pencil-splitoff-flexes` and `thm:pencil-x0-splitoff`): if
`H` has the open ear `a − x 0 − b` on `V₁`, then suppressing `x 0` and relinking its label `e 0` to
`a − b` leaves the bodies `V₁`, keeps every link of `H[V₁]`, and grows the closed neighbourhoods of
`a` and `b` by each other only; and every link of `H` with the label `e 0` has `x 0` as an end. -/
theorem _root_.Graph.splitOff_oneEar {H : Graph α β} {V₁ : Set α} {x : Fin 1 → α} {a b : α}
    {e : Fin 2 → β} (hcover : V(H) = V₁ ∪ Set.range x) (hxV₁ : ∀ i, x i ∉ V₁) (ha : a ∈ V₁)
    (hb : b ∈ V₁)
    (hpath : ∀ i : Fin 2,
      H.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ)) :
    V(H) \ {x 0} = V₁ ∧ (∀ u w, H.IsLink (e 0) u w → u = x 0 ∨ w = x 0) ∧
      (∀ f u w, (H.induce V₁).IsLink f u w → (H.splitOff (x 0) a b (e 0)).IsLink f u w) ∧
      ∀ v ∈ V₁, ∀ w ∈ (H.splitOff (x 0) a b (e 0)).closedNbhd v,
        w ∈ (H.induce V₁).closedNbhd v ∨ (v = a ∧ w = b) ∨ (v = b ∧ w = a) := by
  have hrange : Set.range x = {x 0} := by
    ext w; simp [Fin.exists_fin_one, eq_comm]
  have hV : V(H) \ {x 0} = V₁ := by
    rw [hcover, hrange, Set.union_sdiff_right]
    exact Set.sdiff_singleton_eq_self (hxV₁ 0)
  have l0 : H.IsLink (e 0) a (x 0) := hpath 0
  have he0 : ∀ u w, H.IsLink (e 0) u w → u = x 0 ∨ w = x 0 := by
    intro u w h
    rcases h.eq_and_eq_or_eq_and_eq l0 with ⟨-, h⟩ | ⟨h, -⟩
    exacts [Or.inr h, Or.inl h]
  refine ⟨hV, he0, ?_, ?_⟩
  · rintro f u w ⟨hf, hu, hw⟩
    have hu0 : u ≠ x 0 := fun h => hxV₁ 0 (h ▸ hu)
    have hw0 : w ≠ x 0 := fun h => hxV₁ 0 (h ▸ hw)
    refine Or.inl ⟨?_, hf, hu0, hw0⟩
    rintro rfl
    rcases he0 u w hf with h | h
    exacts [hu0 h, hw0 h]
  · rintro v hv w (rfl | ⟨f, hf⟩)
    · exact Or.inl (Or.inl rfl)
    rcases hf with ⟨-, hf, hv0, hw0⟩ | ⟨-, -, -, -, -, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · have hwV : w ∈ V₁ := by
        have := hf.right_mem
        rw [← hV]
        exact ⟨this, hw0⟩
      exact Or.inl (Or.inr ⟨f, hf, hv, hwV⟩)
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)

/-! ## An incidence meets two open conditions (`lem:pencil-one-ear-incidence`) -/

/-- **A point on the zero line of one affine function and off that of another** (a step of
`lem:pencil-one-ear-incidence`): read `c, d ∈ K³` as the affine functions `q ↦ c · (q, 1)` and
`q ↦ d · (q, 1)` on `K²`. If `c` is nonconstant and `d` is not a multiple of `c`, some `q` has
`c(q) = 0 ≠ d(q)`: an affine function vanishing on the zero line of a nonconstant one is a multiple
of it. -/
theorem exists_dotProduct_eq_zero_ne_zero {c d : Fin 3 → K} (hc : c 0 ≠ 0 ∨ c 1 ≠ 0)
    (hd : d ∉ K ∙ c) : ∃ q : Fin 2 → K, c ⬝ᵥ ![q 0, q 1, 1] = 0 ∧ d ⬝ᵥ ![q 0, q 1, 1] ≠ 0 := by
  by_contra! H
  apply hd
  rcases hc with hc | hc
  · have h0 := H ![-(c 2) / c 0, 0] (by
      simp [dotProduct, Fin.sum_univ_three]; field_simp; ring)
    have h1 := H ![-(c 2 + c 1) / c 0, 1] (by
      simp [dotProduct, Fin.sum_univ_three]; field_simp; ring)
    simp [dotProduct, Fin.sum_univ_three] at h0 h1
    field_simp at h0 h1
    have e1 : d 0 / c 0 * c 1 = d 1 := by
      field_simp; linear_combination (-1 : K) * h1 + h0
    have e2 : d 0 / c 0 * c 2 = d 2 := by
      field_simp; linear_combination (-1 : K) * h0
    refine Submodule.mem_span_singleton.mpr ⟨d 0 / c 0, ?_⟩
    funext i
    fin_cases i
    · simp [hc]
    · simpa using e1
    · simpa using e2
  · have h0 := H ![0, -(c 2) / c 1] (by
      simp [dotProduct, Fin.sum_univ_three]; field_simp; ring)
    have h1 := H ![1, -(c 2 + c 0) / c 1] (by
      simp [dotProduct, Fin.sum_univ_three]; field_simp; ring)
    simp [dotProduct, Fin.sum_univ_three] at h0 h1
    field_simp at h0 h1
    have e0 : d 1 / c 1 * c 0 = d 0 := by
      field_simp; linear_combination (-1 : K) * h1 + h0
    have e2 : d 1 / c 1 * c 2 = d 2 := by
      field_simp; linear_combination (-1 : K) * h0
    refine Submodule.mem_span_singleton.mpr ⟨d 1 / c 1, ?_⟩
    funext i
    fin_cases i
    · simpa using e0
    · simp [hc]
    · simpa using e2

/-- **An incidence meets two open conditions** (`lem:pencil-one-ear-incidence`). Let `K` be
infinite, `L` a subspace of `K^σ` for a finite `σ`, and `D : K^σ → K³` linear with `dim D(L) ≥ 2`,
`D z` read as the affine function `q ↦ D z · (q, 1)` on `K²`. Let `A` be a polynomial in the
coordinates of `σ`, nonzero somewhere on `L`, and `B` a nonzero polynomial on `K²`. Then some
`z ∈ L` and `q ∈ K²` have `D z · (q, 1) = 0`, `A(z) ≠ 0` and `B(q) ≠ 0`.

Proof. Some `z₀ ∈ L` has `A(z₀) ≠ 0` and `D z₀` nonconstant
(`MvPolynomial.exists_mem_eval_ne_zero₂`, `lem:pencil-x0-fibre-intersection`), and some `u ∈ L` has
`D u` not a multiple of `D z₀`. For `q ∈ K²` and `s ∈ K`, the point `s (D u (q) z₀ − D z₀ (q) u)` of
`L` and `q` lie on the incidence, and `A` at that point is a polynomial in `(q, s)`. It is nonzero
at a `q` on the zero line of `D z₀` off that of `D u` (`exists_dotProduct_eq_zero_ne_zero`) and
`s = D u (q)⁻¹`, where the point is `z₀`. A common non-root of it and of `B` gives `z` and `q`. -/
theorem exists_incidence [Infinite K] {σ : Type*} [Finite σ] {L : Submodule K (σ → K)}
    (D : (σ → K) →ₗ[K] (Fin 3 → K)) (hD : 2 ≤ Module.finrank K (L.map D))
    {A : MvPolynomial σ K} (hA : ∃ z ∈ L, MvPolynomial.eval z A ≠ 0)
    {B : MvPolynomial (Fin 2) K} (hB : B ≠ 0) :
    ∃ z ∈ L, ∃ q : Fin 2 → K, D z ⬝ᵥ ![q 0, q 1, 1] = 0 ∧ MvPolynomial.eval z A ≠ 0 ∧
      MvPolynomial.eval q B ≠ 0 := by
  classical
  have : Fintype σ := Fintype.ofFinite σ
  -- the one-dimensional span bound
  have hspan1 : ∀ v : Fin 3 → K, Module.finrank K (K ∙ v) ≤ 1 :=
    fun v => (finrank_span_le_card ({v} : Set (Fin 3 → K))).trans (by simp)
  -- a point of `L` where `D` is nonconstant
  have hnc : ∃ z₁ ∈ L, D z₁ 0 ≠ 0 ∨ D z₁ 1 ≠ 0 := by
    by_contra! H
    have hle : L.map D ≤ K ∙ (![0, 0, 1] : Fin 3 → K) := by
      rintro _ ⟨z, hz, rfl⟩
      refine Submodule.mem_span_singleton.mpr ⟨D z 2, ?_⟩
      funext i
      fin_cases i <;> simp [(H z hz).1, (H z hz).2]
    have := (Submodule.finrank_mono hle).trans (hspan1 _)
    omega
  -- the linear polynomial `z ↦ D z j`
  set ℓ : Fin 3 → MvPolynomial σ K := fun j =>
    ∑ i, MvPolynomial.C (D (fun k => if i = k then 1 else 0) j) * MvPolynomial.X i with hℓ
  have hℓev : ∀ z j, MvPolynomial.eval z (ℓ j) = D z j := by
    intro z j
    rw [LinearMap.pi_apply_eq_sum_univ D z]
    simp [hℓ, Finset.sum_apply, mul_comm]
  -- `z₀`: `A z₀ ≠ 0` and `D z₀` nonconstant
  obtain ⟨z₁, hz₁, hz₁'⟩ := hnc
  have hz₀ : ∃ z₀ ∈ L, MvPolynomial.eval z₀ A ≠ 0 ∧ (D z₀ 0 ≠ 0 ∨ D z₀ 1 ≠ 0) := by
    rcases hz₁' with h | h
    · obtain ⟨z₀, hz₀, h1, h2⟩ := MvPolynomial.exists_mem_eval_ne_zero₂ hA
        ⟨z₁, hz₁, by rwa [hℓev]⟩
      exact ⟨z₀, hz₀, h1, Or.inl (by rwa [hℓev] at h2)⟩
    · obtain ⟨z₀, hz₀, h1, h2⟩ := MvPolynomial.exists_mem_eval_ne_zero₂ hA
        ⟨z₁, hz₁, (by rwa [hℓev] : MvPolynomial.eval z₁ (ℓ 1) ≠ 0)⟩
      exact ⟨z₀, hz₀, h1, Or.inr (by rwa [hℓev] at h2)⟩
  obtain ⟨z₀, hz₀L, hAz₀, hz₀nc⟩ := hz₀
  -- `u`: `D u ∉ K (D z₀)`
  obtain ⟨u, huL, hu⟩ : ∃ u ∈ L, D u ∉ K ∙ D z₀ := by
    by_contra! H
    have hle : L.map D ≤ K ∙ D z₀ := by rintro _ ⟨u, hu, rfl⟩; exact H u hu
    have := (Submodule.finrank_mono hle).trans (hspan1 _)
    omega
  obtain ⟨q₀, hq₀c, hq₀d⟩ := exists_dotProduct_eq_zero_ne_zero hz₀nc hu
  -- the parametrization of the incidence
  set Lpoly : (Fin 3 → K) → MvPolynomial (Fin 2 ⊕ Unit) K := fun c =>
    MvPolynomial.C (c 0) * MvPolynomial.X (Sum.inl 0) +
      MvPolynomial.C (c 1) * MvPolynomial.X (Sum.inl 1) + MvPolynomial.C (c 2) with hLpoly
  have hLev : ∀ (c : Fin 3 → K) (pt : Fin 2 ⊕ Unit → K),
      MvPolynomial.eval pt (Lpoly c) = c ⬝ᵥ ![pt (Sum.inl 0), pt (Sum.inl 1), 1] := by
    intro c pt
    simp [hLpoly, dotProduct, Fin.sum_univ_three, mul_comm]
  set Z : (Fin 2 ⊕ Unit → K) → σ → K := fun pt =>
    pt (Sum.inr ()) • ((D u ⬝ᵥ ![pt (Sum.inl 0), pt (Sum.inl 1), 1]) • z₀ -
      (D z₀ ⬝ᵥ ![pt (Sum.inl 0), pt (Sum.inl 1), 1]) • u) with hZ
  set F : MvPolynomial (Fin 2 ⊕ Unit) K := MvPolynomial.bind₁ (fun i =>
    MvPolynomial.X (Sum.inr ()) * (Lpoly (D u) * MvPolynomial.C (z₀ i) -
      Lpoly (D z₀) * MvPolynomial.C (u i))) A with hF
  have hFev : ∀ pt, MvPolynomial.eval pt F = MvPolynomial.eval (Z pt) A := by
    intro pt
    rw [hF, MvPolynomial.eval_bind₁]
    refine congrArg (fun f => MvPolynomial.eval f A) ?_
    funext i
    simp [hZ, hLev, mul_comm]
  have hZL : ∀ pt, Z pt ∈ L := fun pt =>
    L.smul_mem _ (L.sub_mem (L.smul_mem _ hz₀L) (L.smul_mem _ huL))
  have hZinc : ∀ pt, D (Z pt) ⬝ᵥ ![pt (Sum.inl 0), pt (Sum.inl 1), 1] = 0 := by
    intro pt
    simp only [hZ, map_smul, map_sub, smul_dotProduct, sub_dotProduct, smul_eq_mul]
    ring
  set pt₀ : Fin 2 ⊕ Unit → K := Sum.elim q₀ (fun _ => (D u ⬝ᵥ ![q₀ 0, q₀ 1, 1])⁻¹) with hpt₀
  have hF₀ : MvPolynomial.eval pt₀ F ≠ 0 := by
    rw [hFev]
    have : Z pt₀ = z₀ := by
      simp only [hZ, hpt₀, Sum.elim_inl, Sum.elim_inr, hq₀c, zero_smul, sub_zero, smul_smul,
        inv_mul_cancel₀ hq₀d, one_smul]
    rwa [this]
  have hB' : MvPolynomial.rename Sum.inl B ≠ (0 : MvPolynomial (Fin 2 ⊕ Unit) K) := by
    intro h
    exact hB (MvPolynomial.rename_injective _ Sum.inl_injective (h.trans (map_zero _).symm))
  have hFne : F ≠ 0 := fun h => hF₀ (by rw [h, map_zero])
  obtain ⟨pt, hptF, hptB⟩ := MvPolynomial.exists_eval_ne_zero₂ hFne hB'
  refine ⟨Z pt, hZL pt, fun i => pt (Sum.inl i), ?_, by rwa [hFev] at hptF, ?_⟩
  · exact hZinc pt
  · rw [MvPolynomial.eval_rename] at hptB
    exact hptB

/-! ## The base configuration of a one-body ear (`lem:pencil-one-ear-base`) -/

/-- **The incidence functional as a polynomial** (a step of `lem:pencil-one-ear-base`): for
`u ∈ K³`, `(z, h) ↦ (h_a − h_b) · u`, a linear polynomial in the coordinates of the lifting system,
the heights `z` and the coefficient vectors `h` (`eval_incidencePoly`). At `u = (q_a, 1)` and
`u = (q_b, 1)` it gives the two functionals of `lem:pencil-flag-genericity`. -/
noncomputable def incidencePoly (a b : α) (u : Fin 3 → K) : MvPolynomial (α ⊕ (α × Fin 3)) K :=
  ∑ i, MvPolynomial.C (u i) *
    (MvPolynomial.X (Sum.inr (a, i)) - MvPolynomial.X (Sum.inr (b, i)))

theorem eval_incidencePoly (a b : α) (u : Fin 3 → K) (x : α ⊕ (α × Fin 3) → K) :
    MvPolynomial.eval x (incidencePoly a b u) = planeDiff a b x ⬝ᵥ u := by
  simp [incidencePoly, dotProduct, planeDiff_apply, mul_comm]

open Classical in
/-- **The base configuration of a one-body ear** (`lem:pencil-one-ear-base`). Let `K` be infinite
and `H` simple, with an open ear `a − x 0 − b` on `V₁` whose ends are not adjacent; let
`G′ = H[V₁]`, let the general configuration of `G′` attain, with `def₂(G′; a, b) + 2 ≤ def₂(G′)`,
and let `B` be a nonzero polynomial in the picture coordinates whose non-roots are admissible for
`H`. Then there are a picture `q` with `B(q) ≠ 0` and a polynomial `A` in the coordinates of the
lifting system of `H`, nonzero at one of its solutions at `q`, such that every solution `(z, h)` at
`q` with `A(z, h) ≠ 0` has `(h_a − h_b) · (q_a, 1) ≠ 0` and `(h_a − h_b) · (q_b, 1) ≠ 0`, the point
of each end off the plane of the other, and gives `G′` its target rank `6(|V₁| − 1) − def₃(G′)` at
`(q, z)`.

Proof. `H` with `x 0` suppressed is `G′ + ab`, `G′` with the edge `ab` added
(`Graph.splitOff_oneEar`), simple as `a` and `b` are not adjacent, with
`def₂(G′ + ab) + 2 ≤ def₂(G′)` (`Graph.splitOff_deficiency_add_le_of_deficiencyMerged`,
`lem:splitoff-deficiency-merged`). At a picture `q′` off `B`, off the polynomial of the attainment
at `G′` and off that of Jackson and Jordán's equality at `G′ + ab`
(`Graph.exists_mvPolynomial_finrank_liftingSpace_eq`, `thm:pencil-jj-equality`), the lifting space
of `G′ + ab` is at least two smaller than that of `G′`
(`Graph.three_add_deficiency_le_finrank_liftingSpace`, `lem:pencil-lifting-space-deficiency`), so
`(z, h) ↦ h_a − h_b` has rank at least two on the solutions for `G′`
(`Graph.two_le_finrank_map_planeDiff`, `lem:pencil-flag-genericity`). `exists_incidence` then gives
a solution for `G′` off `A`, the product of the polynomial in the heights of the attainment at `G′`
and the two incidence functionals at `q′`, and a picture point of `x 0`, with `q′` elsewhere, off
`B` and at which `h_a − h_b` vanishes. Moving `x 0` there gives `q`, and the solution extends to
`x 0`, with the value of the plane of `a` there as its height and the coefficients of the plane
through the three points of its closed neighbourhood
(`Graph.IsAdmissiblePicture.exists_dotProduct_of_ncard_closedNbhd_le_three`,
`lem:pencil-three-points`). `A` reads only `V₁` and the planes at `a` and `b`. -/
theorem _root_.Graph.exists_oneEar_base [Infinite K] [Fintype α] [Finite β] {H : Graph α β}
    (hS : H.Simple) {V₁ : Set α} {x : Fin 1 → α} {a b : α} {e : Fin 2 → β}
    (hcover : V(H) = V₁ ∪ Set.range x) (hxV₁ : ∀ i, x i ∉ V₁) (ha : a ∈ V₁) (hb : b ∈ V₁)
    (hpath : ∀ i : Fin 2,
      H.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (hsep : ∀ f u w, H.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁)
    (hnadj : ¬ H.Adj a b) (h₁ : (H.induce V₁).X0Attains K)
    (hδ₂ : (H.induce V₁).deficiencyMerged 2 a b + 2 ≤ (H.induce V₁).deficiency 2)
    {B : MvPolynomial (α × Fin 2) K} (hB : B ≠ 0)
    (hBadm : ∀ q, MvPolynomial.eval q B ≠ 0 → H.IsAdmissiblePicture q) :
    ∃ (q : α × Fin 2 → K) (A : MvPolynomial (α ⊕ (α × Fin 3)) K),
      MvPolynomial.eval q B ≠ 0 ∧
      (∃ xk ∈ LinearMap.ker ((H.liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin,
        MvPolynomial.eval xk A ≠ 0) ∧
      ∀ xk ∈ LinearMap.ker ((H.liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin,
        MvPolynomial.eval xk A ≠ 0 →
        planeDiff a b xk ⬝ᵥ pencilPicturePoint q a ≠ 0 ∧
        planeDiff a b xk ⬝ᵥ pencilPicturePoint q b ≠ 0 ∧
        ∀ ends : β → α × α, (∀ f u w, (H.induce V₁).IsLink f u w →
            (H.induce V₁).IsLink f (ends f).1 (ends f).2) →
          (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 2)
            (H.induce V₁) ends (fun p => pencilConfigPoint q (fun w => xk (Sum.inl w))
              p.1 p.2)).toBodyHinge.rigidityRows) : ℤ) =
            screwDim 2 * ((V₁.ncard : ℤ) - 1) - (H.induce V₁).deficiency 3 := by
  set G' := H.induce V₁ with hG'
  set H' := H.splitOff (x 0) a b (e 0) with hH'
  obtain ⟨hV₁, he0, hle', hN⟩ := Graph.splitOff_oneEar hcover hxV₁ ha hb hpath
  have hx0 : x 0 ∉ V₁ := hxV₁ 0
  have hax : a ≠ x 0 := fun h => hx0 (h ▸ ha)
  have hbx : b ≠ x 0 := fun h => hx0 (h ▸ hb)
  have hV₁H : V₁ ⊆ V(H) := hcover ▸ Set.subset_union_left
  have hx0H : x 0 ∈ V(H) := hcover ▸ Or.inr ⟨0, rfl⟩
  have hVH' : V(H') = V₁ := by rw [hH', Graph.vertexSet_splitOff, hV₁]
  -- `G′` is admissible somewhere, so `G′ + ab` has three members in every closed neighbourhood
  obtain ⟨ends₁, P₁, hends₁, hP₁, hgood₁⟩ := h₁
  obtain ⟨q₀, hq₀⟩ := MvPolynomial.exists_eval_ne_zero hP₁
  have hadm₀ := (hgood₁ q₀ hq₀).1
  have h3' : ∀ v ∈ V(H'), 3 ≤ (H'.closedNbhd v).ncard := by
    intro v hv
    rw [hVH'] at hv
    refine (hadm₀.three_le_ncard_closedNbhd hv).trans (Set.ncard_le_ncard ?_ (Set.toFinite _))
    rintro w (rfl | ⟨f, hf⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨f, hle' f _ _ hf⟩
  have hS' : H'.Simple := Graph.splitOff_simple_of_not_adj hS
    (Graph.ne_of_deficiencyMerged_lt (hδ₂.trans_lt' (by omega))) hnadj
  obtain ⟨PJ, hPJ, hJJ⟩ := Graph.exists_mvPolynomial_finrank_liftingSpace_eq (K := K) hS'
    ⟨a, hVH' ▸ ha⟩ h3'
  -- the base picture `q'`
  obtain ⟨q', hq'⟩ := MvPolynomial.exists_eval_ne_zero (mul_ne_zero (mul_ne_zero hP₁ hPJ) hB)
  rw [map_mul, map_mul] at hq'
  obtain ⟨hadm', R₁, ⟨z₁, hz₁, hR₁⟩, hatt₁⟩ :=
    hgood₁ q' (left_ne_zero_of_mul (left_ne_zero_of_mul hq'))
  obtain ⟨-, hJJ'⟩ := hJJ q' (right_ne_zero_of_mul (left_ne_zero_of_mul hq'))
  have hBq' := right_ne_zero_of_mul hq'
  -- the lifting space drops by at least two from `G′` to `G′ + ab`
  have hflat := Graph.three_add_deficiency_le_finrank_liftingSpace hadm' ⟨a, ha⟩
  have hdef2 := Graph.splitOff_deficiency_add_le_of_deficiencyMerged (n := 2) (by decide) hV₁
    hax hbx (hV₁H ha) (hV₁H hb) he0
    (by have h2 : ((Graph.bodyBarDim 2 : ℤ) - 1) = 2 := rfl; rw [h2]; exact hδ₂)
  have hdim :
      Module.finrank K (H'.liftingSpace q') + 2 ≤ Module.finrank K (G'.liftingSpace q') := by
    have : ((Module.finrank K (H'.liftingSpace q') : ℤ)) + 2 ≤
        Module.finrank K (G'.liftingSpace q') := by
      rw [hJJ']
      have h2 : ((Graph.bodyBarDim 2 : ℤ) - 1) = 2 := rfl
      rw [h2] at hdef2
      linarith
    exact_mod_cast this
  have hU2 := Graph.two_le_finrank_map_planeDiff hadm' (G' := G') (H := H') hVH' hN hdim
  set L := LinearMap.ker ((G'.liftingMatrix K).map (MvPolynomial.eval q')).mulVecLin with hL
  have hD : 2 ≤ Module.finrank K (L.map (planeDiff a b)) := by
    refine hU2.trans ?_
    rw [Submodule.map_comp]
    exact Submodule.finrank_map_le _ _
  -- the open condition `A`: `G′` attains, and both incidence functionals are nonzero
  set A : MvPolynomial (α ⊕ (α × Fin 3)) K := MvPolynomial.rename Sum.inl (restrictPoly V₁ R₁) *
    (incidencePoly a b (pencilPicturePoint q' a) * incidencePoly a b (pencilPicturePoint q' b))
    with hAdef
  have hAev : ∀ y : α ⊕ (α × Fin 3) → K, MvPolynomial.eval y A =
      MvPolynomial.eval (Graph.liftingRestrict V₁ (fun w => y (Sum.inl w))) R₁ *
        ((planeDiff a b y ⬝ᵥ pencilPicturePoint q' a) *
          (planeDiff a b y ⬝ᵥ pencilPicturePoint q' b)) := by
    intro y
    rw [hAdef, map_mul, map_mul, MvPolynomial.eval_rename, eval_restrictPoly, eval_incidencePoly,
      eval_incidencePoly]
    rfl
  have hA₀ : ∃ y ∈ L, MvPolynomial.eval y A ≠ 0 := by
    -- `G′`'s attaining heights lift to the kernel
    have hz₁' : z₁ ∈ L.map (LinearMap.funLeft K K Sum.inl) := by
      rw [hL, G'.map_ker_liftingMatrix q']; exact hz₁
    obtain ⟨y₁, hy₁, hy₁z⟩ := hz₁'
    have h1 : ∃ y ∈ L,
        MvPolynomial.eval y (MvPolynomial.rename Sum.inl (restrictPoly V₁ R₁)) ≠ 0 := by
      refine ⟨y₁, hy₁, ?_⟩
      rw [MvPolynomial.eval_rename, eval_restrictPoly]
      have hy : y₁ ∘ Sum.inl = z₁ := hy₁z
      have : Graph.liftingRestrict V₁ (y₁ ∘ Sum.inl) = z₁ := by
        rw [hy]; funext w
        by_cases hw : w ∈ V₁
        · simp [Graph.liftingRestrict_apply, hw]
        · simp [Graph.liftingRestrict_apply, hw, hz₁.1 w hw]
      rwa [this]
    -- the two incidence functionals are onto `K²` on the kernel
    have htop : L.map ((Matrix.of ![pencilPicturePoint q' a, pencilPicturePoint q' b]).mulVecLin
        ∘ₗ planeDiff a b) = ⊤ := by
      refine Submodule.eq_top_of_finrank_eq ?_
      have := Submodule.finrank_le (L.map ((Matrix.of ![pencilPicturePoint q' a,
        pencilPicturePoint q' b]).mulVecLin ∘ₗ planeDiff a b))
      rw [Module.finrank_fin_fun] at this ⊢
      omega
    obtain ⟨y₂, hy₂, hy₂e⟩ : (fun _ => (1 : K)) ∈ L.map
        ((Matrix.of ![pencilPicturePoint q' a, pencilPicturePoint q' b]).mulVecLin ∘ₗ
          planeDiff a b) := by rw [htop]; trivial
    have h2 : ∃ y ∈ L, MvPolynomial.eval y (incidencePoly a b (pencilPicturePoint q' a) *
        incidencePoly a b (pencilPicturePoint q' b)) ≠ 0 := by
      refine ⟨y₂, hy₂, ?_⟩
      rw [map_mul, eval_incidencePoly, eval_incidencePoly]
      have e0 := congr_fun hy₂e 0
      have e1 := congr_fun hy₂e 1
      simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, Matrix.mulVec, Matrix.of_apply]
        at e0 e1
      rw [dotProduct_comm] at e0 e1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e0 e1
      rw [e0, e1]; exact mul_ne_zero one_ne_zero one_ne_zero
    obtain ⟨y, hy, hy1, hy2⟩ := MvPolynomial.exists_mem_eval_ne_zero₂ h1 h2
    exact ⟨y, hy, by rw [hAdef, map_mul]; exact mul_ne_zero hy1 hy2⟩
  -- the picture polynomial of the ear body
  set By : MvPolynomial (Fin 2) K := MvPolynomial.bind₁ (fun p : α × Fin 2 =>
    if p.1 = x 0 then MvPolynomial.X p.2 else MvPolynomial.C (q' p)) B with hBy
  set qf : (Fin 2 → K) → α × Fin 2 → K := fun qy p => if p.1 = x 0 then qy p.2 else q' p
    with hqf
  have hByev : ∀ qy, MvPolynomial.eval qy By = MvPolynomial.eval (qf qy) B := by
    intro qy
    rw [hBy, MvPolynomial.eval_bind₁]
    refine congrArg (fun f => MvPolynomial.eval f B) ?_
    funext p
    by_cases hp : p.1 = x 0 <;> simp [hqf, hp]
  have hBy0 : By ≠ 0 := by
    intro h
    have hq : qf (fun i => q' (x 0, i)) = q' := by
      funext p
      obtain ⟨w, i⟩ := p
      by_cases hp : w = x 0
      · subst hp; simp [hqf]
      · simp [hqf, hp]
    have := hByev (fun i => q' (x 0, i))
    rw [h, map_zero, hq] at this
    exact hBq' this.symm
  -- the incidence (`exists_incidence`)
  obtain ⟨xg, hxgL, qy, hinc, hAxg, hBqy⟩ := exists_incidence (planeDiff a b) hD hA₀ hBy0
  set q := qf qy with hqdef
  rw [hByev] at hBqy
  have hadmH := hBadm q hBqy
  have hqV₁ : ∀ w ∈ V₁, ∀ i, q (w, i) = q' (w, i) := by
    intro w hw i
    have : w ≠ x 0 := fun h => hx0 (h ▸ hw)
    simp [hqdef, hqf, this]
  have hppV₁ : ∀ w ∈ V₁, pencilPicturePoint q w = pencilPicturePoint q' w := by
    intro w hw; funext i; fin_cases i <;> simp [pencilPicturePoint, hqV₁ w hw]
  have hppx : pencilPicturePoint q (x 0) = ![qy 0, qy 1, 1] := by
    funext i; fin_cases i <;> simp [pencilPicturePoint, hqdef, hqf]
  obtain ⟨hxg1, hxg2, hxg3⟩ := Graph.liftingMatrix_mulVec_eq_zero_iff.mp (LinearMap.mem_ker.mp hxgL)
  -- the heights: those of `G′`, and at the ear body the value of the plane of `a`
  set la : Fin 3 → K := fun i => xg (Sum.inr (a, i)) with hla
  set lb : Fin 3 → K := fun i => xg (Sum.inr (b, i)) with hlb
  have hinc' : la ⬝ᵥ ![qy 0, qy 1, 1] = lb ⬝ᵥ ![qy 0, qy 1, 1] := by
    have : planeDiff a b xg = la - lb := by funext i; rfl
    rw [this, sub_dotProduct, sub_eq_zero] at hinc
    exact hinc
  set zf : α → K := fun w => if w = x 0 then la ⬝ᵥ ![qy 0, qy 1, 1] else xg (Sum.inl w) with hzf
  obtain ⟨hy, hhy⟩ := hadmH.exists_dotProduct_of_ncard_closedNbhd_le_three hx0H
    (H.ncard_closedNbhd_ear_le_three (Function.injective_of_subsingleton x) hxV₁ ha hb hpath hsep 0)
    zf
  set xk : α ⊕ (α × Fin 3) → K := Sum.elim zf
    (fun p => if p.1 = x 0 then hy p.2 else xg (Sum.inr p)) with hxkdef
  have hxk : xk ∈ LinearMap.ker ((H.liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Graph.liftingMatrix_mulVec_eq_zero_iff]
    refine ⟨fun w hw => ?_, fun v hv w hw => ?_, fun v hv i => ?_⟩
    · have hw0 : w ≠ x 0 := fun h => hw (h ▸ hx0H)
      have hw1 : w ∉ V₁ := fun h => hw (hV₁H h)
      simp [hxkdef, hzf, hw0, hxg1 w hw1]
    · by_cases hv0 : v = x 0
      · subst hv0
        simp only [hxkdef, Sum.elim_inl, Sum.elim_inr, ite_true]
        exact hhy w hw
      · have hvV₁ : v ∈ V₁ := by
          rw [hcover] at hv
          rcases hv with hv | ⟨i, rfl⟩
          · exact hv
          · exact absurd (by fin_cases i; rfl) hv0
        simp only [hxkdef, Sum.elim_inl, Sum.elim_inr, hv0, ite_false]
        rcases H.mem_closedNbhd_induce_of_ear (k := 1) le_rfl hxV₁ ha hb hpath hsep hvV₁ hw with
          hw' | ⟨rfl, hw'⟩ | ⟨rfl, hw'⟩
        · have hwV : w ∈ V₁ := Graph.closedNbhd_subset_vertexSet hvV₁ hw'
          have hw0 : w ≠ x 0 := fun h => hx0 (h ▸ hwV)
          simp only [hzf, hw0, ite_false]
          rw [hxg2 v hvV₁ w hw', hppV₁ w hwV]
        · have : w = x 0 := hw'
          subst this
          simp only [hzf, ite_true, hppx]
          rfl
        · have : w = x 0 := hw'
          subst this
          simp only [hzf, ite_true, hppx]
          exact hinc'
    · have hv0 : v ≠ x 0 := fun h => hv (h ▸ hx0H)
      have hv1 : v ∉ V₁ := fun h => hv (hV₁H h)
      simp [hxkdef, hv0, hxg3 v hv1 i]
  -- `A` reads only `V₁` and the planes at `a`, `b`
  have hAeq : MvPolynomial.eval xk A = MvPolynomial.eval xg A := by
    rw [hAev, hAev]
    have h1 : Graph.liftingRestrict V₁ (fun w => xk (Sum.inl w)) =
        Graph.liftingRestrict V₁ (fun w => xg (Sum.inl w)) := by
      funext w
      by_cases hw : w ∈ V₁
      · have hw0 : w ≠ x 0 := fun h => hx0 (h ▸ hw)
        simp [Graph.liftingRestrict_apply, hw, hxkdef, hzf, hw0]
      · simp [Graph.liftingRestrict_apply, hw]
    have h2 : planeDiff a b xk = planeDiff a b xg := by
      funext i; simp [planeDiff_apply, hxkdef, hax, hbx]
    rw [h1, h2]
  refine ⟨q, A, hBqy, ⟨xk, hxk, by rw [hAeq]; exact hAxg⟩, fun xk' hxk' hA' => ?_⟩
  rw [hAev] at hA'
  obtain ⟨hR, hia, hib⟩ : _ ∧ _ ∧ _ :=
    ⟨left_ne_zero_of_mul hA', left_ne_zero_of_mul (right_ne_zero_of_mul hA'),
      right_ne_zero_of_mul (right_ne_zero_of_mul hA')⟩
  refine ⟨by rwa [hppV₁ a ha], by rwa [hppV₁ b hb], fun ends hends => ?_⟩
  -- `G′` attains at the restriction of `xk'`
  have hmem : (fun w => xk' (Sum.inl w)) ∈ H.liftingSpace q := by
    rw [← H.map_ker_liftingMatrix q]
    exact ⟨xk', hxk', rfl⟩
  have hz' := Graph.liftingRestrict_mem_liftingSpace (Graph.induce_le hV₁H) hmem
  rw [Graph.liftingSpace_congr (G := G') (q := q) (q' := q') hqV₁] at hz'
  have hr := hatt₁ _ hz' hR
  rw [PanelHingeFramework.finrank_span_rigidityRows_ofNormals_congr G' hends₁ hends
    (q' := fun p => pencilConfigPoint q (fun w => xk' (Sum.inl w)) p.1 p.2) (fun w hw t => ?_)]
    at hr
  · exact hr
  · have hw' : w ∈ V₁ := hw
    change pencilConfigPoint q' (Graph.liftingRestrict V(G') fun w => xk' (Sum.inl w)) w t =
      pencilConfigPoint q (fun w => xk' (Sum.inl w)) w t
    rw [pencilConfigPoint_liftingRestrict V(G') q' _ hw t]
    fin_cases t <;> simp [pencilConfigPoint, hqV₁ w hw']

/-! ## An open ear with one interior body (`thm:pencil-x0-open-ear-one`) -/

open Classical in
/-- **An open ear with one interior body** (`thm:pencil-x0-open-ear-one`). Let `G` satisfy the
standing hypotheses, with an open ear `a − x 0 − b` on `V₁` whose ends are not adjacent, and let
`def₃(G[V₁]) ≤ def₃(G)` and `def₂(G[V₁]; a, b) + 2 ≤ def₂(G[V₁])`. If the general configuration of
`G[V₁]` attains, so does that of `G`.

Proof. `Graph.exists_oneEar_base` at `G`, with the main-picture polynomial of `G`, gives a main
picture `q` of `G` and heights `z ∈ L_G(q)` at which `G[V₁]` has its target. The closed
neighbourhood of `x 0` is `{a, x 0, b}`, whose picture points are not collinear, so the two joins of
the ear are independent (`linearIndependent_pointJoin_pair`) and `dim(ρ + Λ) ≥ 2`
(`card_le_finrank_of_linearIndependent_pointJoin`, `lem:pencil-ear-hinge-span`). The ear rank
formula then adds at least `5 · 2 + 2 − 6 = 6` to the rank, no less than the growth
`6 − def₃(G) + def₃(G[V₁])` of the target, and `Graph.x0Attains_of_exists`
(`lem:pencil-x0-one-witness`) concludes. -/
theorem _root_.Graph.X0Attains.of_openEar_one [Infinite K] [Finite α] [Finite β]
    {G : Graph α β} (hG : G.IsX0Graph) {V₁ : Set α} {x : Fin 1 → α} {a b : α}
    {e : Fin 2 → β} (hcover : V(G) = V₁ ∪ Set.range x) (hxV₁ : ∀ i, x i ∉ V₁) (ha : a ∈ V₁)
    (hb : b ∈ V₁)
    (hpath : ∀ i : Fin 2,
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (hsep : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁)
    (hnadj : ¬ G.Adj a b)
    (h₁ : (G.induce V₁).X0Attains K)
    (hdef : (G.induce V₁).deficiency 3 ≤ G.deficiency 3)
    (hδ₂ : (G.induce V₁).deficiencyMerged 2 a b + 2 ≤ (G.induce V₁).deficiency 2) :
    G.X0Attains K := by
  have : Fintype α := Fintype.ofFinite α
  have hV : V(G).Nonempty := hG.connected.nonempty
  have : Inhabited α := ⟨a⟩
  have hinj := Function.injective_of_subsingleton x
  have hab : a ≠ b := Graph.ne_of_deficiencyMerged_lt (hδ₂.trans_lt' (by omega))
  have hax : x 0 ≠ a := fun h => hxV₁ 0 (h ▸ ha)
  have hbx : x 0 ≠ b := fun h => hxV₁ 0 (h ▸ hb)
  obtain ⟨Pm, hPm, hmain⟩ := G.exists_mvPolynomial_isMainPicture (K := K)
    hG.simple.toLoopless hG.three_le_ncard_closedNbhd
  obtain ⟨q, A, hq, ⟨xk, hxk, hA⟩, hgood⟩ := G.exists_oneEar_base hG.simple hcover hxV₁ ha hb
    hpath hsep hnadj h₁ hδ₂ hPm (fun q hq => (hmain q hq).1)
  have hqmain := hmain q hq
  set z : α → K := fun w => xk (Sum.inl w) with hzdef
  have hz : z ∈ G.liftingSpace q := by
    rw [← G.map_ker_liftingMatrix q]; exact ⟨xk, hxk, rfl⟩
  set ends := G.endsOf
  have hends : ∀ f u w, G.IsLink f u w → G.IsLink f (ends f).1 (ends f).2 :=
    fun f _ _ hf => G.isLink_endsOf hf.edge_mem
  have hr₁ := (hgood xk hxk hA).2.2 ends (G.isLink_ends_induce hends V₁)
  -- the ear rank formula, with two independent joins of the ear
  set F := (PanelHingeFramework.ofNormals (k := 2) G ends
    (fun p => pencilConfigPoint q z p.1 p.2)).toBodyHinge
  have hC : ∀ i, F.supportExtensor (e i) ≠ 0 :=
    fun i => hqmain.1.supportExtensor_ne_zero hends z (hpath i)
  have hear := BodyHingeFramework.finrank_span_rigidityRows_ear_eq F hinj hxV₁ ha hb hab hpath
    hsep hC
  have hx0G : x 0 ∈ V(G) := hcover ▸ Or.inr ⟨0, rfl⟩
  have hN : G.closedNbhd (x 0) ⊆ {a, x 0, b} := by
    intro w hw
    rcases G.closedNbhd_ear_subset hinj hxV₁ ha hb hpath hsep 0 hw with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  have hli := linearIndependent_pointJoin_pair (linearIndependent_pencilConfigPoint_triple z
    (hqmain.1.linearIndependent_of_closedNbhd_subset hx0G hN))
  have hl2 : ∀ i, G.IsLink (![e 0, e 1] i) (![a, x 0] i) (![x 0, b] i) := by
    intro i; fin_cases i
    · exact hpath 0
    · exact hpath 1
  have hdim := card_le_finrank_of_linearIndependent_pointJoin hends (pencilConfigPoint q z)
    ![a, x 0] ![x 0, b] ![e 0, e 1] hl2
    (by convert hli using 1; funext i; fin_cases i <;> rfl)
    ((⟨F.graph.induce V₁, F.supportExtensor⟩ : BodyHingeFramework K 2 α β).relScrews a b
      ⊔ Submodule.span K (Set.range (F.supportExtensor ∘ e)))
    (fun i => Submodule.mem_sup_right (Submodule.subset_span (by fin_cases i <;> exact ⟨_, rfl⟩)))
  rw [Fintype.card_fin] at hdim
  -- the body count
  have hcount : (V(G).ncard : ℤ) = V₁.ncard + 1 := by
    rw [hcover]; exact_mod_cast Set.ncard_union_range_of_injective hinj hxV₁
  refine Graph.x0Attains_of_exists hV ends hends hqmain hz ?_
  have e1 : (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
      = (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 2) (G.induce V₁)
          ends (fun p => pencilConfigPoint q z p.1 p.2)).toBodyHinge.rigidityRows) : ℤ)
        + ((screwDim 2 : ℤ) - 1) * (1 + 1)
        + (Module.finrank K ↥((⟨F.graph.induce V₁, F.supportExtensor⟩ :
              BodyHingeFramework K 2 α β).relScrews a b
            ⊔ Submodule.span K (Set.range (F.supportExtensor ∘ e))) : ℤ)
        - (screwDim 2 : ℤ) := hear
  rw [e1, hr₁, hcount]
  have hs : (screwDim 2 : ℤ) = 6 := rfl
  rw [hs]
  have hdim' : (2 : ℤ) ≤ (Module.finrank K ↥((⟨F.graph.induce V₁, F.supportExtensor⟩ :
      BodyHingeFramework K 2 α β).relScrews a b
        ⊔ Submodule.span K (Set.range (F.supportExtensor ∘ e))) : ℤ) := by exact_mod_cast hdim
  linarith

/-! ## Suppressing the second interior body of a two-body ear -/

/-- **Suppressing the second interior body of a two-body ear** (a step of
`thm:pencil-x0-open-ear-two-orbit`): suppressing `x 1` and relinking `e 1` to `x 0 − b` leaves the
ear `a − x 0 − b` on `V₁`, with the labels `e 0, e 1`. -/
theorem splitOff_ear_two {G : Graph α β} {V₁ : Set α} {x : Fin 2 → α} {a b : α}
    {e : Fin 3 → β} (hcover : V(G) = V₁ ∪ Set.range x) (hinj : Function.Injective x)
    (hxV₁ : ∀ i, x i ∉ V₁) (ha : a ∈ V₁) (hb : b ∈ V₁) (hab : a ≠ b)
    (hpath : ∀ i : Fin 3,
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (hsep : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁) :
    V(G.splitOff (x 1) (x 0) b (e 1)) = V₁ ∪ Set.range ![x 0] ∧
      Function.Injective ![x 0] ∧ (∀ i, ![x 0] i ∉ V₁) ∧
      (∀ i : Fin 2, (G.splitOff (x 1) (x 0) b (e 1)).IsLink (![e 0, e 1] i)
        (pathVertex a ![x 0] b i.castSucc) (pathVertex a ![x 0] b i.succ)) ∧
      (∀ f u w, (G.splitOff (x 1) (x 0) b (e 1)).IsLink f u w →
        (∀ i, f ≠ ![e 0, e 1] i) → u ∈ V₁ ∧ w ∈ V₁) := by
  have hax : ∀ i, x i ≠ a := fun i h => hxV₁ i (h ▸ ha)
  have hbx : ∀ i, x i ≠ b := fun i h => hxV₁ i (h ▸ hb)
  have he := pathEdge_injective hinj hax hbx hab hpath
  have l0 : G.IsLink (e 0) a (x 0) := hpath 0
  have l1 : G.IsLink (e 1) (x 0) (x 1) := hpath 1
  have l2 : G.IsLink (e 2) (x 1) b := hpath 2
  have e01 : e 0 ≠ e 1 := fun h => by simpa using he h
  have x01 : x 0 ≠ x 1 := fun h => absurd (hinj h) (by decide)
  refine ⟨?_, fun i j _ => Subsingleton.elim i j, fun i => by fin_cases i; exact hxV₁ 0, ?_, ?_⟩
  · ext w
    simp only [Graph.vertexSet_splitOff, hcover, Set.mem_sdiff, Set.mem_union, Set.mem_range,
      Set.mem_singleton_iff, Fin.exists_fin_succ, Fin.exists_fin_zero, Matrix.cons_val_zero,
      Fin.succ_zero_eq_one]
    constructor
    · rintro ⟨h | rfl | rfl | h, hw⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl rfl)
      · exact absurd rfl hw
      · exact h.elim
    · rintro (h | rfl | h)
      · exact ⟨Or.inl h, fun h' => hxV₁ 1 (h' ▸ h)⟩
      · exact ⟨Or.inr (Or.inl rfl), x01⟩
      · exact h.elim
  · intro i
    fin_cases i
    · exact Or.inl ⟨e01, l0, (hax 1).symm, x01⟩
    · exact Or.inr ⟨rfl, x01, (hbx 1).symm, l1.left_mem, l2.right_mem, Or.inl ⟨rfl, rfl⟩⟩
  · intro f u w hf hfe
    rcases hf with ⟨hne, hf, hu, hw⟩ | ⟨rfl, -⟩
    · refine hsep f u w hf (fun i => ?_)
      fin_cases i
      · exact hfe 0
      · exact hne
      · rintro rfl
        rcases hf.eq_and_eq_or_eq_and_eq l2 with ⟨h, -⟩ | ⟨-, h⟩
        · exact hu h
        · exact hw h
    · exact absurd rfl (hfe 1)

/-- **Suppressing the second interior body of a two-body ear keeps the graph simple and the ends not
adjacent** (a step of `thm:pencil-x0-open-ear-two-orbit`): if `G` is simple and `a` and `b` are not
adjacent in it, the same holds of `G.splitOff (x 1) (x 0) b (e 1)`. -/
theorem splitOff_ear_two_simple {G : Graph α β} (hS : G.Simple) {V₁ : Set α} {x : Fin 2 → α}
    {a b : α} {e : Fin 3 → β} (hxV₁ : ∀ i, x i ∉ V₁) (ha : a ∈ V₁) (hb : b ∈ V₁) (hab : a ≠ b)
    (hpath : ∀ i : Fin 3,
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (hsep : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁) (hnadj : ¬ G.Adj a b) :
    (G.splitOff (x 1) (x 0) b (e 1)).Simple ∧ ¬ (G.splitOff (x 1) (x 0) b (e 1)).Adj a b := by
  have hax : ∀ i, x i ≠ a := fun i h => hxV₁ i (h ▸ ha)
  have hbx : ∀ i, x i ≠ b := fun i h => hxV₁ i (h ▸ hb)
  have l0 : G.IsLink (e 0) a (x 0) := hpath 0
  have l2 : G.IsLink (e 2) (x 1) b := hpath 2
  have x01 : x 0 ≠ x 1 := (injective_of_isLink_pathVertex_two hS.toLoopless hpath).ne (by decide)
  -- no edge of `G` other than `e 1`, which the split-off relinks, joins `x 0` to `b`
  have hno : ∀ f, f ≠ e 1 → ¬ G.IsLink f (x 0) b := by
    intro f hf hl
    by_cases hfe : ∃ i, f = e i
    · obtain ⟨i, rfl⟩ := hfe
      fin_cases i
      · rcases hl.eq_and_eq_or_eq_and_eq l0 with ⟨h, -⟩ | ⟨-, h⟩
        exacts [hax 0 h, hab h.symm]
      · exact hf rfl
      · rcases hl.eq_and_eq_or_eq_and_eq l2 with ⟨h, -⟩ | ⟨h, -⟩
        exacts [x01 h, hbx 0 h]
    · exact hxV₁ 0 (hsep f _ _ hl (fun i h => hfe ⟨i, h⟩)).1
  refine ⟨Graph.splitOff_simple (fun f u w h => ?_) (fun f₁ f₂ u w h₁ h₂ => ?_), ?_⟩
  · rcases h with ⟨-, h, -, -⟩ | ⟨-, -, -, -, -, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact h.ne
    · exact hbx 0
    · exact (hbx 0).symm
  · rcases h₁ with ⟨hf₁, h₁, -, -⟩ | ⟨rfl, -, -, -, -, h₁⟩ <;>
      rcases h₂ with ⟨hf₂, h₂, -, -⟩ | ⟨rfl, -, -, -, -, h₂⟩
    · exact hS.eq_of_isLink h₁ h₂
    · rcases h₂ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      exacts [absurd h₁ (hno _ hf₁), absurd h₁.symm (hno _ hf₁)]
    · rcases h₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      exacts [absurd h₂ (hno _ hf₂), absurd h₂.symm (hno _ hf₂)]
    · rfl
  · rintro ⟨f, hf⟩
    rcases hf with ⟨-, hf, -, -⟩ | ⟨-, -, -, -, -, ⟨h, -⟩ | ⟨h, -⟩⟩
    · exact hnadj ⟨f, hf⟩
    · exact hax 0 h.symm
    · exact hab h


/-! ## Two interior bodies at non-adjacent ends (`thm:pencil-x0-open-ear-two-orbit`) -/

open Classical in
/-- **An open ear with two interior bodies at non-adjacent ends**
(`thm:pencil-x0-open-ear-two-orbit`). Let `G` satisfy the standing hypotheses, with an open ear
`a − x 0 − x 1 − b` on `V₁` whose ends are not adjacent, let `def₂(G[V₁]; a, b) + 2 ≤ def₂(G[V₁])`,
and let `G₁ = G.splitOff (x 1) (x 0) b (e 1)` be `G` with `x 1` suppressed, the freed label `e 1`
relinked to `x 0 − b`. If the general configurations of `G[V₁]` and of `G₁` attain, so does that of
`G`.

Proof. `G₁` has the open ear `a − x 0 − b` on `V₁` (`splitOff_ear_two`), is simple with `a` and `b`
not adjacent (`splitOff_ear_two_simple`), and has the same `G[V₁]` (`induce_splitOff_ear`).
`Graph.exists_oneEar_base` at `G₁`, with the product of the polynomial of the attainment at `G₁` and
the main-picture polynomial of `G`, gives a picture `q`, and a second fibre intersection
(`MvPolynomial.exists_mem_eval_ne_zero₂`) a solution of the lifting system of `G₁` at `q` at which
`G[V₁]` and `G₁` have their targets, with the planes `la` at `a` and `lb` at `b`. There the point
`y` of `x 0` lies on both planes and the point of each end off the plane of the other, and the ear
rank formula at `G₁` gives `s = dim(ρ + span(p_a ∨ y, y ∨ p_b)) = 2 + def₃(G[V₁]) − def₃(G₁)`.
`exists_insertion_two` gives affine points `x₁` on `la` and `x₂` on `lb` with
`dim(ρ + Λ) ≥ min(s + 1, 6)`, `Λ` the span of `p_a ∨ x₁`, `x₁ ∨ x₂` and `x₂ ∨ p_b`, which is at
least `3 + def₃(G[V₁]) − def₃(G)`, `(⋆)` at two interior bodies, by
`Graph.splitOff_deficiency_le_of_eq_left` (`lem:splitoff-deficiency-reuse`) and
`Graph.deficiency_induce_add_le_of_ear` (`lem:deficiency-ear`). Over the base data
`(q, z|V₁, la, lb)` the points `x₁` and `x₂` of `x 0` and `x 1` are the configuration of one ear
datum, so the span bound holds off the zero set of a polynomial in the ear data that is nonzero
there (`exists_mvPolynomial_le_finrank_sup_span_pointJoin`). At a common non-root with the
main-picture polynomial of `G`, where the rank of `G[V₁]` and `ρ` are those of the base data, the
ear rank formula at `G` gives `G` its target. -/
theorem _root_.Graph.X0Attains.of_openEar_two_of_splitOff [Infinite K] [Finite α] [Finite β]
    {G : Graph α β} (hG : G.IsX0Graph) {V₁ : Set α} {x : Fin 2 → α} {a b : α}
    {e : Fin 3 → β} (hcover : V(G) = V₁ ∪ Set.range x) (hxV₁ : ∀ i, x i ∉ V₁) (ha : a ∈ V₁)
    (hb : b ∈ V₁)
    (hpath : ∀ i : Fin 3,
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (hsep : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁)
    (hnadj : ¬ G.Adj a b)
    (h₁ : (G.induce V₁).X0Attains K)
    (h₂ : (G.splitOff (x 1) (x 0) b (e 1)).X0Attains K)
    (hδ₂ : (G.induce V₁).deficiencyMerged 2 a b + 2 ≤ (G.induce V₁).deficiency 2) :
    G.X0Attains K := by
  have : Fintype α := Fintype.ofFinite α
  have hV : V(G).Nonempty := hG.connected.nonempty
  have : Inhabited α := ⟨a⟩
  have hinj := injective_of_isLink_pathVertex_two hG.simple.toLoopless hpath
  have hab : a ≠ b := Graph.ne_of_deficiencyMerged_lt (hδ₂.trans_lt' (by omega))
  have hax : ∀ i, x i ≠ a := fun i h => hxV₁ i (h ▸ ha)
  have hbx : ∀ i, x i ≠ b := fun i h => hxV₁ i (h ▸ hb)
  have l0 : G.IsLink (e 0) a (x 0) := hpath 0
  have l1 : G.IsLink (e 1) (x 0) (x 1) := hpath 1
  have l2 : G.IsLink (e 2) (x 1) b := hpath 2
  have x01 : x 0 ≠ x 1 := fun h => absurd (hinj h) (by decide)
  have hV₁G : V₁ ⊆ V(G) := hcover ▸ Set.subset_union_left
  -- `G₁`, `G` with `x 1` suppressed: `G[V₁]` with the ear `a − x 0 − b`
  set G₁ := G.splitOff (x 1) (x 0) b (e 1) with hG₁
  obtain ⟨hcover₁, hinj₁, hxV₁₁, hpath₁, hsep₁⟩ :=
    splitOff_ear_two hcover hinj hxV₁ ha hb hab hpath hsep
  obtain ⟨hS₁, hnadj₁⟩ := splitOff_ear_two_simple hG.simple hxV₁ ha hb hab hpath hsep hnadj
  have he₁ : ∀ y y', G.IsLink (e 1) y y' → y ∉ V₁ ∨ y' ∉ V₁ := by
    intro y y' h
    rcases h.eq_and_eq_or_eq_and_eq l1 with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Or.inl (hxV₁ 0)
    · exact Or.inl (hxV₁ 1)
  obtain ⟨hle₁, hind⟩ := induce_splitOff_ear (x := x) (e₀ := e 1) (w := b) hcover hxV₁
    ⟨1, rfl⟩ (hxV₁ 0) he₁
  -- the polynomials: `G`'s main pictures and `G₁`'s attainment
  obtain ⟨Pm, hPm, hmain⟩ := G.exists_mvPolynomial_isMainPicture (K := K)
    hG.simple.toLoopless hG.three_le_ncard_closedNbhd
  obtain ⟨ends₂, P₂, hends₂, hP₂, hgood₂⟩ := h₂
  -- the base configuration of the one-body ear of `G₁`
  obtain ⟨q, A, hqB, ⟨xk₀, hxk₀, hA₀⟩, hgood⟩ := G₁.exists_oneEar_base hS₁ hcover₁ hxV₁₁ ha hb
    hpath₁ hsep₁ hnadj₁ (hind ▸ h₁) (hind ▸ hδ₂) (mul_ne_zero hP₂ hPm)
    (fun q hq => (hgood₂ q (by rw [map_mul] at hq; exact left_ne_zero_of_mul hq)).1)
  rw [map_mul] at hqB
  obtain ⟨hadm₂, R₂, ⟨z₂, hz₂, hR₂⟩, hatt₂⟩ := hgood₂ q (left_ne_zero_of_mul hqB)
  have hPmq := right_ne_zero_of_mul hqB
  -- a second fibre intersection, in the lifting system of `G₁`: `G₁` has its target too
  set L₁ := LinearMap.ker ((G₁.liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin with hL₁
  obtain ⟨xk, hxk, hxkR, hxkA⟩ : ∃ xk ∈ L₁,
      MvPolynomial.eval xk (MvPolynomial.rename Sum.inl R₂) ≠ 0 ∧ MvPolynomial.eval xk A ≠ 0 := by
    refine MvPolynomial.exists_mem_eval_ne_zero₂ ?_ ⟨xk₀, hxk₀, hA₀⟩
    have hz₂' : z₂ ∈ L₁.map (LinearMap.funLeft K K Sum.inl) := by
      rw [hL₁, G₁.map_ker_liftingMatrix q]; exact hz₂
    obtain ⟨y₂, hy₂, hy₂z⟩ := hz₂'
    refine ⟨y₂, hy₂, ?_⟩
    rw [MvPolynomial.eval_rename]
    have : y₂ ∘ Sum.inl = z₂ := hy₂z
    rwa [this]
  obtain ⟨hoa, hob, hrkV₁⟩ := hgood xk hxk hxkA
  set z : α → K := fun w => xk (Sum.inl w) with hzdef
  have hz : z ∈ G₁.liftingSpace q := by
    rw [← G₁.map_ker_liftingMatrix q]; exact ⟨xk, hxk, rfl⟩
  rw [MvPolynomial.eval_rename] at hxkR
  have hr₂ := hatt₂ z hz hxkR
  set la : Fin 3 → K := fun i => xk (Sum.inr (a, i)) with hla
  set lb : Fin 3 → K := fun i => xk (Sum.inr (b, i)) with hlb
  obtain ⟨-, hxk2, -⟩ := Graph.liftingMatrix_mulVec_eq_zero_iff.mp (LinearMap.mem_ker.mp hxk)
  have haV₁ : a ∈ V(G₁) := hcover₁ ▸ Or.inl ha
  have hbV₁ : b ∈ V(G₁) := hcover₁ ▸ Or.inl hb
  have hzla : ∀ w ∈ G₁.closedNbhd a, z w = la ⬝ᵥ pencilPicturePoint q w := hxk2 a haV₁
  have hzlb : ∀ w ∈ G₁.closedNbhd b, z w = lb ⬝ᵥ pencilPicturePoint q w := hxk2 b hbV₁
  -- the selectors
  set ends := G.endsOf with hendsdef
  have hends : ∀ f u w, G.IsLink f u w → G.IsLink f (ends f).1 (ends f).2 :=
    fun f _ _ hf => G.isLink_endsOf hf.edge_mem
  set ends₁ := Function.update ends (e 1) (x 0, b) with hends₁def
  have hends₁ : ∀ f u w, G₁.IsLink f u w → G₁.IsLink f (ends₁ f).1 (ends₁ f).2 :=
    fun f _ _ hf => G.isLink_update_splitOff hends (hpath₁ 1) f hf
  have hendsI := G.isLink_ends_induce hends V₁
  have hnot : ∀ f u w, (G.induce V₁).IsLink f u w → f ≠ e 1 := by
    rintro f u w ⟨hf, hu, hw⟩ rfl
    rcases he₁ u w hf with h | h
    exacts [h hu, h hw]
  have hendsI₁ : ∀ f u w, (G₁.induce V₁).IsLink f u w →
      (G₁.induce V₁).IsLink f (ends₁ f).1 (ends₁ f).2 := by
    rw [hind]
    intro f u w hf
    rw [hends₁def, Function.update_of_ne (hnot f u w hf)]
    exact hendsI f u w hf
  -- the ear rank formula at `G₁`: `rank G₁ = rank G[V₁] + 4 + s`
  set c₁ : α × Fin 4 → K := fun p => pencilConfigPoint q z p.1 p.2 with hc₁
  set F₁ := (PanelHingeFramework.ofNormals (k := 2) G₁ ends₁ c₁).toBodyHinge with hF₁
  have hC₁ : ∀ i, F₁.supportExtensor (![e 0, e 1] i) ≠ 0 :=
    fun i => hadm₂.supportExtensor_ne_zero hends₁ z (hpath₁ i)
  have hear₁ := BodyHingeFramework.finrank_span_rigidityRows_ear_eq F₁ hinj₁ hxV₁₁ ha hb hab
    hpath₁ hsep₁ hC₁
  have hrk₁ : (Module.finrank K ↥(Submodule.span K
      (⟨F₁.graph.induce V₁, F₁.supportExtensor⟩ : BodyHingeFramework K 2 α β).rigidityRows) : ℤ) =
      screwDim 2 * ((V₁.ncard : ℤ) - 1) - (G.induce V₁).deficiency 3 := by
    have h := hrkV₁ ends₁ hendsI₁
    rw [show (G₁.induce V₁).deficiency 3 = (G.induce V₁).deficiency 3 by rw [hind]] at h
    exact h
  set ρM := (⟨F₁.graph.induce V₁, F₁.supportExtensor⟩ : BodyHingeFramework K 2 α β).relScrews a b
    with hρM
  set ρJ := ρM.map (screwComplementIso (K := K)).symm.toLinearMap with hρJ
  set pa := pencilConfigPoint q z a with hpa
  set y := pencilConfigPoint q z (x 0) with hy
  set pb := pencilConfigPoint q z b with hpb
  rw [span_supportExtensor_comp_eq_map_pointJoin hends₁ c₁ (![e 0, e 1])
    (fun i => pathVertex a ![x 0] b i.castSucc) (fun i => pathVertex a ![x 0] b i.succ) hpath₁,
    finrank_sup_map_screwComplementIso] at hear₁
  have hjoins₁ : Set.range (fun i : Fin 2 => pointJoin
      (fun j => c₁ (pathVertex a ![x 0] b i.castSucc, j))
      (fun j => c₁ (pathVertex a ![x 0] b i.succ, j))) = {pointJoin pa y, pointJoin y pb} := by
    rw [show (fun i : Fin 2 => pointJoin (fun j => c₁ (pathVertex a ![x 0] b i.castSucc, j))
      (fun j => c₁ (pathVertex a ![x 0] b i.succ, j))) = ![pointJoin pa y, pointJoin y pb] from by
        funext i; fin_cases i <;> rfl]
    simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rw [hjoins₁] at hear₁
  -- the counts
  have hcount : (V(G).ncard : ℤ) = V₁.ncard + 2 := by
    rw [hcover]; exact_mod_cast Set.ncard_union_range_of_injective hinj hxV₁
  have hcount₁ : (V(G₁).ncard : ℤ) = V₁.ncard + 1 := by
    rw [hcover₁]; exact_mod_cast Set.ncard_union_range_of_injective hinj₁ hxV₁₁
  have hdeg2 : ∀ e' y', G.IsLink e' (x 1) y' → e' = e 1 ∨ e' = e 2 := by
    intro e' y' hl
    by_cases h : ∃ i, e' = e i
    · obtain ⟨i, rfl⟩ := h
      fin_cases i
      · rcases hl.eq_and_eq_or_eq_and_eq l0 with ⟨h1, -⟩ | ⟨h1, -⟩
        exacts [absurd h1 (hax 1), absurd h1 x01.symm]
      · exact Or.inl rfl
      · exact Or.inr rfl
    · exact absurd (hsep e' _ _ hl (fun i h' => h ⟨i, h'⟩)).1 (hxV₁ 1)
  have hdef₁ : G₁.deficiency 3 ≤ G.deficiency 3 :=
    Graph.splitOff_deficiency_le_of_eq_left (n := 3) (by decide) x01 (hbx 1).symm l1.symm l2 hdeg2
  have hdefG : (G.induce V₁).deficiency 3 + 2 + 1 - (Graph.bodyBarDim 3 : ℤ) ≤ G.deficiency 3 :=
    Graph.deficiency_induce_add_le_of_ear (n := 3) (k := 2) (by decide) (by omega) hcover hinj
      hxV₁ ha hb hpath hsep
  have hs6 : (screwDim 2 : ℤ) = 6 := rfl
  have hb6 : (Graph.bodyBarDim 3 : ℤ) = 6 := rfl
  -- `s = dim(ρ + span(p_a ∨ y, y ∨ p_b)) = 2 + def₃(G[V₁]) − def₃(G₁)`
  have hs : (Module.finrank K ↥(ρJ ⊔ Submodule.span K {pointJoin pa y, pointJoin y pb}) : ℤ) =
      2 + (G.induce V₁).deficiency 3 - G₁.deficiency 3 := by
    have h1 : (Module.finrank K (Submodule.span K F₁.rigidityRows) : ℤ) =
        screwDim 2 * ((V(G₁).ncard : ℤ) - 1) - G₁.deficiency 3 := by
      rw [← hr₂]
      exact_mod_cast PanelHingeFramework.finrank_span_rigidityRows_ofNormals_congr G₁ hends₁
        hends₂ (fun _ _ _ => rfl)
    rw [hear₁, hrk₁, hcount₁, hs6, ← hρJ] at h1
    push_cast at h1
    linarith
  -- put `x 1` back (`exists_insertion_two`): `y` on both planes, the point of each end off the
  -- plane of the other
  have hxa : x 0 ∈ G₁.closedNbhd a := Or.inr ⟨e 0, hpath₁ 0⟩
  have hxb : x 0 ∈ G₁.closedNbhd b := Or.inr ⟨e 1, (hpath₁ 1).symm⟩
  have hza : z a = la ⬝ᵥ pencilPicturePoint q a := hzla a (Or.inl rfl)
  have hzb : z b = lb ⬝ᵥ pencilPicturePoint q b := hzlb b (Or.inl rfl)
  have hdiff : ∀ u, planeDiff a b xk ⬝ᵥ u = la ⬝ᵥ u - lb ⬝ᵥ u := by
    intro u; rw [← sub_dotProduct]; rfl
  obtain ⟨x₁, x₂, hx₁3, hx₁a, hx₂3, hx₂b, hins⟩ := exists_insertion_two ρJ la lb
    (pa := pa) (y := y) (pb := pb)
    (by rw [hpa, planarProj_pencilConfigPoint]; exact hza)
    (by rw [hpb, planarProj_pencilConfigPoint]; exact hzb)
    (by rw [hy, planarProj_pencilConfigPoint]; exact hzla _ hxa)
    (by rw [hy, planarProj_pencilConfigPoint]; exact hzlb _ hxb) rfl rfl rfl
    (by
      rw [hpa, planarProj_pencilConfigPoint]
      intro h
      apply hoa
      rw [hdiff, ← hza]
      exact sub_eq_zero.mpr h)
    (by
      rw [hpb, planarProj_pencilConfigPoint]
      intro h
      apply hob
      rw [hdiff, ← hzb]
      exact sub_eq_zero.mpr h.symm)
  -- the ear data of `G` over the base `(q, z|V₁, la, lb)`
  set z₁ := Graph.liftingRestrict V₁ z with hz₁def
  set cfg := earConfig V₁ q z₁ (x 0) (x 1) (Set.range x) la lb with hcfgdef
  set P := earPointPoly (K := K) V₁ q z₁ (x 0) (x 1) (Set.range x) la lb with hPdef
  have hPc : ∀ s, (fun p => MvPolynomial.eval s (P p)) = cfg s :=
    fun s => funext (eval_earPointPoly V₁ q z₁ (x 0) (x 1) (Set.range x) la lb s)
  have hcV₁ : ∀ s w, w ∈ V₁ → ∀ j, cfg s (w, j) = c₁ (w, j) := by
    intro s w hw j
    rw [hcfgdef, earConfig_of_mem s hw j, hc₁]
    exact pencilConfigPoint_liftingRestrict V₁ q z hw j
  set pt : ((α × Fin 2) ⊕ α → K) → α → Fin 4 → K := fun s w j => cfg s (w, j) with hpt
  have hevpt : ∀ s w, (fun j => MvPolynomial.eval s (P (w, j))) = pt s w :=
    fun s w => funext fun j => congrFun (hPc s) (w, j)
  have hpta : ∀ s, pt s a = pa := fun s => funext fun j => hcV₁ s a ha j
  have hptb : ∀ s, pt s b = pb := fun s => funext fun j => hcV₁ s b hb j
  -- the ear datum with `x 0` at `x₁` and `x 1` at `x₂`
  set sw : (α × Fin 2) ⊕ α → K := Sum.elim (fun p => if p.1 = x 0 then ![x₁ 0, x₁ 1] p.2
    else if p.1 = x 1 then ![x₂ 0, x₂ 1] p.2 else q p) (fun _ => 0) with hsw
  have hpt0 : pt sw (x 0) = x₁ := by
    simp only [pt]
    rw [earConfig_first sw (hxV₁ 0)]
    funext j
    fin_cases j
    · simp [hsw, liftPlane]
    · simp [hsw, liftPlane]
    · simp [hsw, liftPlane, hx₁a, planarProj_apply, hx₁3]
    · simp [liftPlane, hx₁3]
  have hpt1 : pt sw (x 1) = x₂ := by
    simp only [pt]
    rw [earConfig_last sw (hxV₁ 1) x01.symm]
    funext j
    fin_cases j
    · simp [hsw, liftPlane, x01.symm]
    · simp [hsw, liftPlane, x01.symm]
    · simp [hsw, liftPlane, hx₂b, planarProj_apply, hx₂3, x01.symm]
    · simp [liftPlane, hx₂3]
  have hjoinsG : ∀ s, (fun i : Fin 3 =>
      pointJoin (fun j => MvPolynomial.eval s (P (pathVertex a x b i.castSucc, j)))
        (fun j => MvPolynomial.eval s (P (pathVertex a x b i.succ, j)))) =
      ![pointJoin (pt s a) (pt s (x 0)), pointJoin (pt s (x 0)) (pt s (x 1)),
        pointJoin (pt s (x 1)) (pt s b)] := by
    intro s; funext i; rw [hevpt, hevpt]; fin_cases i <;> rfl
  have hrange : ∀ u v w t : ScrewSpace K 2, u = v → Set.range ![u, w, t] = {v, w, t} := by
    rintro u v w t rfl
    simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  -- the span bound at that ear datum, `≥ 3 + def₃(G[V₁]) − def₃(G)`
  set n₀ := (3 + (G.induce V₁).deficiency 3 - G.deficiency 3).toNat with hn₀
  have hNt : n₀ ≤ Module.finrank K ↥(ρJ ⊔ Submodule.span K (Set.range fun i : Fin 3 =>
      pointJoin (fun j => MvPolynomial.eval sw (P (pathVertex a x b i.castSucc, j)))
        (fun j => MvPolynomial.eval sw (P (pathVertex a x b i.succ, j))))) := by
    rw [hjoinsG, hrange _ _ _ _ rfl, hpta, hpt0, hpt1, hptb]
    refine le_trans ?_ hins
    rw [le_min_iff]
    constructor
    · refine Int.toNat_le.mpr ?_
      push_cast
      linarith
    · refine Int.toNat_le.mpr ?_
      push_cast
      rw [hb6] at hdefG
      linarith
  obtain ⟨Qs, hQs₀, hQs⟩ := exists_mvPolynomial_le_finrank_sup_span_pointJoin ρJ P
    (fun i : Fin 3 => pathVertex a x b i.castSucc) (fun i => pathVertex a x b i.succ) hNt
  -- the ear data of `G`: a common non-root `s₀`, main for `G`
  set sstar : (α × Fin 2) ⊕ α → K := Sum.elim q (fun _ => 0) with hsstar
  have hpicstar : earPicture V₁ q sstar = q := by
    funext p; by_cases hp : p.1 ∈ V₁ <;> simp [earPicture, hp, hsstar]
  have hPm'₀ : MvPolynomial.eval sstar (MvPolynomial.bind₁ (earPicturePoly V₁ q) Pm) ≠ 0 := by
    rwa [eval_bind₁_earPicturePoly, hpicstar]
  have hne0 : ∀ {Q : MvPolynomial ((α × Fin 2) ⊕ α) K} {s}, MvPolynomial.eval s Q ≠ 0 → Q ≠ 0 :=
    fun h hQ => h (by rw [hQ, map_zero])
  obtain ⟨s₀, hs₀a, hs₀b⟩ := MvPolynomial.exists_eval_ne_zero₂ (hne0 hQs₀) (hne0 hPm'₀)
  rw [eval_bind₁_earPicturePoly] at hs₀b
  have hqmain₀ := hmain _ hs₀b
  -- the heights of the ear data are heights of `G`
  have hpp : ∀ s, ∀ w ∈ V₁,
      pencilPicturePoint (earPicture V₁ q s) w = pencilPicturePoint q w := by
    intro s w hw; funext i; fin_cases i <;> simp [pencilPicturePoint, earPicture_of_mem s hw]
  have hz₁G : z₁ ∈ (G.induce V₁).liftingSpace q := by
    have := Graph.liftingRestrict_mem_liftingSpace (Graph.induce_le (hcover₁ ▸
      Set.subset_union_left : V₁ ⊆ V(G₁))) hz
    rwa [hind] at this
  have hz₁s : ∀ s, z₁ ∈ (G.induce V₁).liftingSpace (earPicture V₁ q s) := by
    intro s
    rw [Graph.liftingSpace_congr (G := G.induce V₁) (q := earPicture V₁ q s) (q' := q)
      (fun w hw i => earPicture_of_mem s hw i)]
    exact hz₁G
  have hlas : ∀ s, ∀ p ∈ (G.induce V₁).closedNbhd a,
      z₁ p = la ⬝ᵥ pencilPicturePoint (earPicture V₁ q s) p := by
    intro s p hp
    have hpV : p ∈ V₁ := Graph.closedNbhd_subset_vertexSet ha hp
    have hp₁ : p ∈ G₁.closedNbhd a := by
      rcases hp with rfl | ⟨f, hf⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨f, hf.of_le hle₁⟩
    rw [hpp s p hpV, ← hzla p hp₁]
    simp [hz₁def, Graph.liftingRestrict_apply, hpV]
  have hlbs : ∀ s, ∀ p ∈ (G.induce V₁).closedNbhd b,
      z₁ p = lb ⬝ᵥ pencilPicturePoint (earPicture V₁ q s) p := by
    intro s p hp
    have hpV : p ∈ V₁ := Graph.closedNbhd_subset_vertexSet hb hp
    have hp₁ : p ∈ G₁.closedNbhd b := by
      rcases hp with rfl | ⟨f, hf⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨f, hf.of_le hle₁⟩
    rw [hpp s p hpV, ← hzlb p hp₁]
    simp [hz₁def, Graph.liftingRestrict_apply, hpV]
  have hz₀ := Graph.earHeight_mem_liftingSpace (k := 2) le_rfl hcover hinj hxV₁ ha hb hab
    hpath hsep hqmain₀.1 (hz₁s s₀) (hlas s₀) (hlbs s₀) (fun w => s₀ (Sum.inr w))
  -- what `G`'s frameworks read on `V₁`: `G₁`'s hinges
  have hCG : ∀ s f u w, (G.induce V₁).IsLink f u w →
      (PanelHingeFramework.ofNormals (k := 2) G ends (cfg s)).toBodyHinge.supportExtensor f =
        F₁.supportExtensor f := by
    intro s f u w hf
    obtain ⟨-, h1, h2⟩ := hendsI f u w hf
    simp only [hF₁, PanelHingeFramework.toBodyHinge_supportExtensor,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_ends, hends₁def,
      Function.update_of_ne (hnot f u w hf)]
    congr 1 <;> funext j
    · exact hcV₁ s _ h1 j
    · exact hcV₁ s _ h2 j
  have hF₁V : (⟨F₁.graph.induce V₁, F₁.supportExtensor⟩ : BodyHingeFramework K 2 α β) =
      ⟨G.induce V₁, F₁.supportExtensor⟩ := by
    rw [show F₁.graph = G₁ from rfl, hind]
  have hρG : ∀ s, (⟨G.induce V₁, (PanelHingeFramework.ofNormals (k := 2) G ends
      (cfg s)).toBodyHinge.supportExtensor⟩ : BodyHingeFramework K 2 α β).relScrews a b = ρM := by
    intro s
    rw [hρM, hF₁V]
    exact BodyHingeFramework.relScrews_congr (G.induce V₁) (hCG s) a b
  have hrkG : ∀ s, (Module.finrank K ↥(Submodule.span K (⟨G.induce V₁,
      (PanelHingeFramework.ofNormals (k := 2) G ends (cfg s)).toBodyHinge.supportExtensor⟩ :
        BodyHingeFramework K 2 α β).rigidityRows) : ℤ) =
      screwDim 2 * ((V₁.ncard : ℤ) - 1) - (G.induce V₁).deficiency 3 := by
    intro s
    rw [BodyHingeFramework.finrank_span_rigidityRows_congr (G.induce V₁) (hCG s), ← hF₁V]
    exact hrk₁
  -- the ear rank formula at `G`
  have hC : ∀ i, (PanelHingeFramework.ofNormals (k := 2) G ends
      (cfg s₀)).toBodyHinge.supportExtensor (e i) ≠ 0 :=
    fun i => hqmain₀.1.supportExtensor_ne_zero hends _ (hpath i)
  have hear : (Module.finrank K ↥(Submodule.span K (PanelHingeFramework.ofNormals (k := 2) G ends
      (cfg s₀)).toBodyHinge.rigidityRows) : ℤ)
      = (Module.finrank K ↥(Submodule.span K (⟨G.induce V₁, (PanelHingeFramework.ofNormals
            (k := 2) G ends (cfg s₀)).toBodyHinge.supportExtensor⟩ :
              BodyHingeFramework K 2 α β).rigidityRows) : ℤ)
        + ((screwDim 2 : ℤ) - 1) * (2 + 1)
        + (Module.finrank K ↥((⟨G.induce V₁, (PanelHingeFramework.ofNormals (k := 2) G ends
              (cfg s₀)).toBodyHinge.supportExtensor⟩ : BodyHingeFramework K 2 α β).relScrews a b
            ⊔ Submodule.span K (Set.range ((PanelHingeFramework.ofNormals (k := 2) G ends
              (cfg s₀)).toBodyHinge.supportExtensor ∘ e))) : ℤ)
        - (screwDim 2 : ℤ) :=
    BodyHingeFramework.finrank_span_rigidityRows_ear_eq _ hinj hxV₁ ha hb hab hpath hsep hC
  rw [hrkG s₀, hρG s₀, span_supportExtensor_comp_eq_map_pointJoin hends (cfg s₀) e
    (fun i => pathVertex a x b i.castSucc) (fun i => pathVertex a x b i.succ) hpath,
    finrank_sup_map_screwComplementIso, ← hρJ] at hear
  have hspan₀ := hQs s₀ hs₀a
  refine Graph.x0Attains_of_exists hV ends hends hqmain₀ hz₀ ?_
  change _ ≤ (Module.finrank K ↥(Submodule.span K (PanelHingeFramework.ofNormals (k := 2) G ends
    (cfg s₀)).toBodyHinge.rigidityRows) : ℤ)
  rw [hear, hcount, hs6]
  have h₀ : ((3 + (G.induce V₁).deficiency 3 - G.deficiency 3 : ℤ)) ≤ (n₀ : ℤ) :=
    Int.self_le_toNat _
  have h₁ : (n₀ : ℤ) ≤ (Module.finrank K ↥(ρJ ⊔ Submodule.span K (Set.range fun i : Fin 3 =>
      pointJoin (fun j => MvPolynomial.eval s₀ (P (pathVertex a x b i.castSucc, j)))
        (fun j => MvPolynomial.eval s₀ (P (pathVertex a x b i.succ, j))))) : ℤ) := by
    exact_mod_cast hspan₀
  rw [show (fun i : Fin 3 =>
      pointJoin (fun j => MvPolynomial.eval s₀ (P (pathVertex a x b i.castSucc, j)))
        (fun j => MvPolynomial.eval s₀ (P (pathVertex a x b i.succ, j)))) =
      fun i => pointJoin (fun j => cfg s₀ (pathVertex a x b i.castSucc, j))
        (fun j => cfg s₀ (pathVertex a x b i.succ, j))
    from funext fun i => by rw [hevpt, hevpt]] at h₁
  linarith

end CombinatorialRigidity.Molecular
