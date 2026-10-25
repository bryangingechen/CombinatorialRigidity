import CombinatorialRigidity.Molecular.AlgebraicInduction.GenericityDevice
import CombinatorialRigidity.Mathlib.Basic.Countable.Defs

/-! The witnesses of the recon on Katoh and Tanigawa's nonparallel panels (Phase 41b, item 1,
2026-10-24, at commit `c45211e2`; not part of the library). `homogenize` (`Extensor.lean`) appends
the coordinate `1` last, so the panel of a normal `n` is `{x | dir n ⬝ᵥ x + n last = 0}`, with
`dir n = Fin.init n` its first `k + 1` coordinates: KT's `c(v)` (KT §5.1, p. 668, where
`Π(v) = {x | x · c(v) + 1 = 0}`). The candidate predicate `IsNonparallel` asks the direction parts
of two distinct bodies to be independent. It implies general position, is the triple condition
with `e_last`, makes two panels meet, and is strictly stronger (a parallel pair in general
position). The moment curve meets it for `1 ≤ k`, nothing meets it at `k = 0` on two bodies, and
the polynomial of `exists_generalPosition_polynomial` already certifies it for `1 ≤ k`. Route B: a
generic full-rank realization gives a nonparallel one of the same rank, by the genericity device.
`notes/Phase41-design.md` §2 records the verdict. Check it from the repository root with
`lake lean notes/reconcile-formal/NonparallelWitness.lean`: no errors or warnings, and the
`#print axioms` give `[propext, Classical.choice, Quot.sound]`. -/

open CombinatorialRigidity.Molecular
open scoped Graph Matrix

namespace Recon41bNonparallel

variable {K : Type*} [Field K] {k : ℕ} {α β : Type*}

/-- The direction part of a homogeneous normal: its first `k + 1` coordinates. -/
def dir (n : Fin (k + 2) → K) : Fin (k + 1) → K := fun i => n i.castSucc

omit [Field K] in
/-- It is mathlib's `Fin.init`, the left inverse of `Fin.snoc`, which `homogenize` uses. -/
theorem dir_eq_init (n : Fin (k + 2) → K) : dir n = Fin.init n := rfl

/-- The panel of `n` in affine coordinates: `homogenize` appends the coordinate `1` last, so
`homogenize x ⬝ᵥ n = dir n ⬝ᵥ x + n last`. -/
theorem homogenize_dotProduct (x : Fin (k + 1) → K) (n : Fin (k + 2) → K) :
    homogenize x ⬝ᵥ n = dir n ⬝ᵥ x + n (Fin.last (k + 1)) := by
  simp [dotProduct, Fin.sum_univ_castSucc, dir, mul_comm]

/-- Candidate predicate: the panels of any two distinct bodies are nonparallel. -/
def IsNonparallel (P : PanelHingeFramework K k α β) : Prop :=
  ∀ a b : α, a ≠ b → LinearIndependent K ![dir (P.normal a), dir (P.normal b)]

theorem pair_of_dir {u v : Fin (k + 2) → K} (h : LinearIndependent K ![dir u, dir v]) :
    LinearIndependent K ![u, v] := by
  rw [LinearIndependent.pair_iff] at h ⊢
  intro s t hst
  apply h s t
  funext i
  simpa [dir] using congr_fun hst i.castSucc

theorem IsNonparallel.isGeneralPosition {P : PanelHingeFramework K k α β}
    (h : IsNonparallel P) : P.IsGeneralPosition :=
  fun a b hab => pair_of_dir (h a b hab)

/-- The projective form: the direction parts are independent iff `e_last`, `u`, `v` are, i.e. iff
the meet of the two panels is not contained in the hyperplane at infinity. -/
theorem dir_pair_iff_triple (u v : Fin (k + 2) → K) :
    LinearIndependent K ![dir u, dir v] ↔
      LinearIndependent K ![Pi.single (Fin.last (k + 1)) 1, u, v] := by
  rw [LinearIndependent.pair_iff, Fintype.linearIndependent_iff]
  constructor
  · intro h g hg i
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at hg
    have h12 : g 1 = 0 ∧ g 2 = 0 := h (g 1) (g 2) (by
      funext i
      have := congr_fun hg i.castSucc
      simpa [dir, Pi.single_apply, Fin.castSucc_ne_last] using this)
    have h0 : g 0 = 0 := by
      have := congr_fun hg (Fin.last _)
      simpa [h12.1, h12.2] using this
    fin_cases i <;> simp [h0, h12.1, h12.2]
  · intro h s t hst
    have key := h ![-(s * u (Fin.last _) + t * v (Fin.last _)), s, t] (by
      funext j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp [Fin.sum_univ_three]
      · have := congr_fun hst i
        simpa [Fin.sum_univ_three, dir, Pi.single_apply, Fin.castSucc_ne_last] using this)
    exact ⟨by simpa using key 1, by simpa using key 2⟩

/-- Nonparallel panels meet: if the direction parts are independent, some affine point lies on both
panels (the rank-2 system `dir u ⬝ᵥ x = -u last`, `dir v ⬝ᵥ x = -v last` is solvable). -/
theorem exists_common_point {u v : Fin (k + 2) → K} (h : LinearIndependent K ![dir u, dir v]) :
    ∃ x : Fin (k + 1) → K, homogenize x ⬝ᵥ u = 0 ∧ homogenize x ⬝ᵥ v = 0 := by
  have hsurj := (show LinearIndependent K (Matrix.of ![dir u, dir v]).row from h).mulVec_surjective
  obtain ⟨x, hx⟩ := hsurj ![-u (Fin.last _), -v (Fin.last _)]
  refine ⟨x, ?_, ?_⟩
  · have := congr_fun hx 0
    simp only [Matrix.mulVec, Matrix.of_apply, Matrix.cons_val_zero] at this
    rw [homogenize_dotProduct, this]; ring
  · have := congr_fun hx 1
    simp only [Matrix.mulVec, Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val_zero] at this
    rw [homogenize_dotProduct]
    change (fun j => dir v j) ⬝ᵥ x + _ = 0
    rw [this]; ring

/-- General position does not give nonparallel panels: at `k = 1` (lines in the plane) the normals
`(1, 0, 0)` and `(1, 0, 1)` are independent, their direction parts are equal, and their panels, the
lines `x₀ = 0` and `x₀ = -1`, have no common point. -/
theorem generalPosition_not_nonparallel :
    LinearIndependent K ![(![1, 0, 0] : Fin 3 → K), ![1, 0, 1]] ∧
      ¬ LinearIndependent K ![dir (k := 1) (![1, 0, 0] : Fin 3 → K), dir ![1, 0, 1]] ∧
      ∀ x : Fin 2 → K, ¬ (homogenize x ⬝ᵥ (![1, 0, 0] : Fin 3 → K) = 0 ∧
        homogenize x ⬝ᵥ (![1, 0, 1] : Fin 3 → K) = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [LinearIndependent.pair_iff]
    intro s t hst
    have h0 : s + t = 0 := by simpa using congr_fun hst 0
    have h2 : t = 0 := by simpa using congr_fun hst 2
    exact ⟨by rw [h2, add_zero] at h0; exact h0, h2⟩
  · intro h
    rw [LinearIndependent.pair_iff] at h
    have := h 1 (-1) (by funext i; fin_cases i <;> simp [dir])
    exact one_ne_zero this.1
  · rintro x ⟨h1, h2⟩
    rw [homogenize_dotProduct] at h1 h2
    have h1' : x 0 = 0 := by simpa [dir, dotProduct, Fin.sum_univ_two] using h1
    have h2' : x 0 + 1 = 0 := by simpa [dir, dotProduct, Fin.sum_univ_two] using h2
    rw [h1', zero_add] at h2'
    exact one_ne_zero h2'

/-- The direction part of a moment-curve point at `k + 1` is the moment-curve point at `k`. -/
theorem dir_momentCurve (k' : ℕ) (t : K) :
    dir (k := k' + 1) (PanelHingeFramework.momentCurve t) =
      PanelHingeFramework.momentCurve (k := k') t := by
  funext i; simp [dir]

/-- The moment curve `(1, t, …, t^(k+1))` gives nonparallel panels for `1 ≤ k` and distinct
parameters: the affine coordinate is the last, `t^(k+1)`, and the direction part is the moment
curve one degree down, whose two points are independent. -/
theorem momentCurve_nonparallel (hk : 1 ≤ k) {s t : K} (hst : s ≠ t) :
    LinearIndependent K ![dir (k := k) (PanelHingeFramework.momentCurve s),
      dir (PanelHingeFramework.momentCurve t)] := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [dir_momentCurve, dir_momentCurve]
  exact PanelHingeFramework.momentCurve_pair_linearIndependent hst

/-- At `k = 0` (`d = 1`) no two panels are nonparallel: direction parts lie in `K¹`. -/
theorem not_nonparallel_k0 (u v : Fin 2 → K) :
    ¬ LinearIndependent K ![dir (k := 0) u, dir v] := by
  intro h
  have := h.fintype_card_le_finrank
  simp at this

/-- So `IsNonparallel` is false at `k = 0` as soon as there are two bodies. -/
theorem not_isNonparallel_k0 (P : PanelHingeFramework K 0 α β) {a b : α} (hab : a ≠ b) :
    ¬ IsNonparallel P :=
  fun h => not_nonparallel_k0 _ _ (h a b hab)

open PanelHingeFramework in
/-- The polynomial of `exists_generalPosition_polynomial` (the product of the leading minors on
coordinates `0` and `1`) already certifies nonparallel panels for `1 ≤ k`: coordinates `0` and `1`
are direction coordinates once the last coordinate is `k + 1 ≥ 2`. -/
theorem isNonparallel_of_eval_ne_zero [Fintype α] (hk : 1 ≤ k) (G : Graph α β)
    (ends : β → α × α) (hlinks : RecordsLinks G ends) (q : α × Fin (k + 2) → K)
    (hq : MvPolynomial.eval q (∏ p ∈ Finset.univ.offDiag, pairLeadingMinorPoly (K := K) p.1 p.2)
      ≠ 0) :
    IsNonparallel (ofNormals (k := k) G ends q hlinks) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  intro a b hab
  rw [map_prod, Finset.prod_ne_zero_iff] at hq
  have hfac := hq (a, b) (Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, hab⟩)
  rw [eval_pairLeadingMinorPoly] at hfac
  exact pair_linearIndependent_of_leading_minor_ne_zero (k := k') (by simpa [dir] using hfac)

open PanelHingeFramework in
/-- Route B: a generic full-rank realization of a loopless graph gives a nonparallel one of the
same rank, by the genericity device (the rank polynomial at the old normals times the leading-minor
product), in the place of KT Lemma 5.2's rotation. The induction is not touched. -/
theorem exists_nonparallel_of_generic [Infinite K] [Finite α] [Finite β] {n : ℕ} (hk : 1 ≤ k)
    (hn : Graph.bodyBarDim n = screwDim k) {G : Graph α β} [G.Loopless]
    (hne : V(G).Nonempty) (h : HasGenericFullRankRealization K k n G) :
    ∃ Q : PanelHingeFramework K k α β, Q.graph = G ∧ IsNonparallel Q ∧
      (Module.finrank K (Submodule.span K Q.toBodyHinge.rigidityRows) : ℤ)
        = screwDim k * ((V(G).ncard : ℤ) - 1) - G.deficiency n := by
  classical
  have : Fintype α := Fintype.ofFinite α
  obtain ⟨Q, hQg, hQgp, hQrank, -⟩ := h
  have hrec : RecordsLinks G Q.ends := hQg ▸ Q.isLink_ends
  have hends : ∀ e u v, G.IsLink e u v → G.IsLink e (Q.ends e).1 (Q.ends e).2 :=
    recordsLinks_iff_forall_isLink.mp hrec
  have hself : ofNormals (k := k) G Q.ends (fun p => Q.normal p.1 p.2) = Q :=
    ofNormals_eq_self_of_graph_eq Q hQg
  have hne₀ : ∀ e, G.IsLink e (Q.ends e).1 (Q.ends e).2 →
      (ofNormals (k := k) G Q.ends (fun p => Q.normal p.1 p.2)).toBodyHinge.supportExtensor e
        ≠ 0 := by
    intro e he
    rw [hself]
    exact Q.supportExtensor_ne_zero_of_isGeneralPosition hQgp he.ne
  obtain ⟨Q_rk, hQrk0, hQrk⟩ :=
    exists_rankPolynomial_of_le_finrank_linking G Q.ends hends hne₀
      (N := Module.finrank K (Submodule.span K Q.toBodyHinge.rigidityRows))
      (le_of_eq (by rw [hself]))
  set Q_np :=
    ∏ p ∈ (Finset.univ : Finset α).offDiag, pairLeadingMinorPoly (K := K) (k := k) p.1 p.2
  have hQnp_ne : Q_np ≠ 0 := by
    obtain ⟨f, hf⟩ := Countable.exists_injective_of_infinite α K
    intro h0
    have hmc : MvPolynomial.eval (fun p => momentCurve (k := k) (f p.1) p.2) Q_np ≠ 0 := by
      rw [map_prod, Finset.prod_ne_zero_iff]
      rintro ⟨a, b⟩ hab
      rw [Finset.mem_offDiag] at hab
      rw [eval_pairLeadingMinorPoly]
      simp only [momentCurve_apply, Fin.val_zero, pow_zero, pow_one, one_mul, mul_one]
      rw [sub_ne_zero]
      exact fun h => hab.2.2 (hf h.symm)
    exact hmc (by rw [h0, map_zero])
  have hQrk_ne : Q_rk ≠ 0 := fun h0 => hQrk0 (by rw [h0, map_zero])
  obtain ⟨q, hq⟩ := MvPolynomial.exists_eval_ne_zero (mul_ne_zero hQrk_ne hQnp_ne)
  rw [map_mul] at hq
  have hq_rk : MvPolynomial.eval q Q_rk ≠ 0 := left_ne_zero_of_mul hq
  have hq_np : MvPolynomial.eval q Q_np ≠ 0 := right_ne_zero_of_mul hq
  have hnp := isNonparallel_of_eval_ne_zero hk G Q.ends hrec q hq_np
  refine ⟨ofNormals G Q.ends q, rfl, hnp, ?_⟩
  have hlb := hQrk q hq_rk
  have hub := BodyHingeFramework.finrank_span_rigidityRows_add_deficiency_le
    (ofNormals (k := k) G Q.ends q).toBodyHinge hn (by simpa using hne) (fun e u v he => by
      simp only [toBodyHinge_graph, ofNormals_graph] at he
      exact supportExtensor_ne_zero_of_isGeneralPosition _ hnp.isGeneralPosition
        (by simpa using (hends e u v he).ne))
  simp only [toBodyHinge_graph, ofNormals_graph] at hub
  refine le_antisymm hub ?_
  rw [← hQrank]
  exact_mod_cast hlb

end Recon41bNonparallel

#print axioms Recon41bNonparallel.dir_pair_iff_triple
#print axioms Recon41bNonparallel.exists_common_point
#print axioms Recon41bNonparallel.generalPosition_not_nonparallel
#print axioms Recon41bNonparallel.momentCurve_nonparallel
#print axioms Recon41bNonparallel.isNonparallel_of_eval_ne_zero
#print axioms Recon41bNonparallel.exists_nonparallel_of_generic
