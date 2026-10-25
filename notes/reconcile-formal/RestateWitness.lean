import CombinatorialRigidity.Molecular.AlgebraicInduction.PanelHinge
import CombinatorialRigidity.Molecular.Deficiency

/-! The witnesses of the recon for RESTATE's open (Phase 41b, 2026-10-24, at commit `3a627b3d`;
not part of the library). Q1: at the double edge, Theorem 5.6's restated conclusion fails in the
meet model, so general position is asked for simple `G` only. Q3: `HasGenericFullRankRealization`'s
last conjunct is the field `isLink_ends`, once `Q.graph = G`. Also: two `hswap` hypotheses and the
rows form's link conjunct follow from the field. `notes/Phase41-design.md` §2 records the verdict.
Check it from the repository root with `lake lean notes/reconcile-formal/RestateWitness.lean`: no
errors, and the two `#print axioms` give `[propext, Classical.choice, Quot.sound]`. -/

open CombinatorialRigidity.Molecular
open scoped Graph

namespace Recon41b

variable {K : Type*} [Field K] {k : ℕ} {α β : Type*}

/-- Q3: the last conjunct of `HasGenericFullRankRealization` is the field, once `Q.graph = G`. -/
theorem lastConjunct_of_field (Q : PanelHingeFramework K k α β) {G : Graph α β}
    (hQg : Q.graph = G) :
    ∀ e u v, G.IsLink e u v →
      ((Q.ends e).1 = u ∧ (Q.ends e).2 = v) ∨ ((Q.ends e).1 = v ∧ (Q.ends e).2 = u) :=
  fun _ _ _ he => (hQg ▸ Q.isLink_ends).eq_or_swap he

/-- Q3: `HasGenericFullRankRealization` without its last conjunct is the same predicate. -/
theorem hasGenericFullRankRealization_iff (n : ℕ) (G : Graph α β) :
    PanelHingeFramework.HasGenericFullRankRealization K k n G ↔
      ∃ Q : PanelHingeFramework K k α β, Q.graph = G ∧ Q.IsGeneralPosition ∧
        ((Module.finrank K (Submodule.span K Q.toBodyHinge.rigidityRows) : ℤ)
          = screwDim k * ((V(G).ncard : ℤ) - 1) - G.deficiency n) := by
  constructor
  · rintro ⟨Q, hg, hgp, hr, -⟩
    exact ⟨Q, hg, hgp, hr⟩
  · rintro ⟨Q, hg, hgp, hr⟩
    exact ⟨Q, hg, hgp, hr, lastConjunct_of_field Q hg⟩

/-- Q1: at the double edge, a meet-model panel framework whose hinges are nonzero on `E(G)` is not
infinitesimally rigid: both hinges are `±` the meet of the same two normals. -/
theorem banana_not_rigid (Q : PanelHingeFramework K k (Fin 2) (Fin 4))
    (hQg : Q.graph = Graph.banana (0 : Fin 2) 1 ({0, 1} : Set (Fin 4)))
    (hC : ∀ e ∈ E(Graph.banana (0 : Fin 2) 1 ({0, 1} : Set (Fin 4))),
      Q.toBodyHinge.supportExtensor e ≠ 0) :
    ¬ Q.toBodyHinge.IsInfinitesimallyRigid := by
  set C : ScrewSpace K k := panelSupportExtensor (k := k) (Q.normal 0) (Q.normal 1) with hCdef
  have hext : ∀ e ∈ ({0, 1} : Set (Fin 4)), Q.toBodyHinge.supportExtensor e = C ∨
      Q.toBodyHinge.supportExtensor e = -C := by
    intro e he
    have hl : Q.graph.IsLink e 0 1 := by
      rw [hQg, Graph.banana_isLink]; exact ⟨he, Or.inl ⟨rfl, rfl⟩⟩
    rcases Q.isLink_ends.eq_or_swap hl with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; rw [PanelHingeFramework.toBodyHinge_supportExtensor, h1, h2]
    · right; rw [PanelHingeFramework.toBodyHinge_supportExtensor, h1, h2, panelSupportExtensor_swap]
  have h0mem : (0 : Fin 4) ∈ ({0, 1} : Set (Fin 4)) := by simp
  have hC0 : C ≠ 0 := by
    intro h0
    apply hC 0 (by simp)
    rcases hext 0 h0mem with h | h <;> rw [h, h0]
    exact neg_zero
  intro hrig
  have hm1 : C ∈ K ∙ -C := Submodule.mem_span_singleton.mpr ⟨-1, by simp⟩
  have hm2 : -C ∈ K ∙ C := Submodule.neg_mem _ (Submodule.mem_span_singleton_self C)
  have hm3 : -C ∈ K ∙ -C := Submodule.mem_span_singleton_self _
  have hm4 : C ∈ K ∙ C := Submodule.mem_span_singleton_self _
  let S : Fin 2 → ScrewSpace K k := Pi.single 0 C
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have hS : Q.toBodyHinge.IsInfinitesimalMotion S := by
    intro e u v he
    rw [PanelHingeFramework.toBodyHinge_graph, hQg, Graph.banana_isLink] at he
    obtain ⟨heE, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := he <;> rw [BodyHingeFramework.hingeConstraint] <;>
      rcases hext e heE with h | h <;> rw [h] <;>
      simp only [S, Pi.single_eq_same, Pi.single_eq_of_ne h10, sub_zero, zero_sub] <;>
      first | exact hm1 | exact hm2 | exact hm3 | exact hm4
  have htriv := hrig hS
  have h01 : S 0 = S 1 := htriv 0 1
  simp only [S, Pi.single_eq_same, Pi.single_eq_of_ne h10] at h01
  exact hC0 h01

/-- Q1: the double edge has deficiency zero, so KT Theorem 5.6's target there is rigidity. -/
theorem banana_deficiency_zero :
    (Graph.banana (0 : Fin 2) 1 ({0, 1} : Set (Fin 4))).deficiency 2 = 0 :=
  Graph.isKDof_zero_of_parallel_pair (by decide) (x := 0) (y := 1) (e₁ := 0) (e₂ := 1)
    (by decide) (by simp) (by simp) (by decide) (by simp) (by simp)

/-- Q1: so Theorem 5.6's restated conclusion (nondegenerate hinges on `E(G)`, the floor) is false
at the double edge in the meet model, at `n = 2`, `k = 1`; a fortiori with general position. -/
theorem restated_theorem56_false_at_banana :
    ¬ ∃ Q : PanelHingeFramework ℝ 1 (Fin 2) (Fin 4),
        Q.graph = Graph.banana (0 : Fin 2) 1 ({0, 1} : Set (Fin 4)) ∧
        (∀ e ∈ E(Graph.banana (0 : Fin 2) 1 ({0, 1} : Set (Fin 4))),
          Q.toBodyHinge.supportExtensor e ≠ 0) ∧
        Q.toBodyHinge.RankHypothesis
          ((Graph.banana (0 : Fin 2) 1 ({0, 1} : Set (Fin 4))).deficiency 2) := by
  rintro ⟨Q, hQg, hC, hrank⟩
  rw [banana_deficiency_zero] at hrank
  exact banana_not_rigid Q hQg hC ((BodyHingeFramework.rankHypothesis_zero_iff _).mp hrank)

/-- Other: `hswap` of `infinitesimalMotions_ofNormals_eq_of_ends_swap` / `hasGenericRealization_
transport_ends` follows from two selectors that both record the links of `G`. -/
theorem hswap_of_recordsLinks {G : Graph α β} {ends ends' : β → α × α}
    (hlinks : PanelHingeFramework.RecordsLinks G ends)
    (hlinks' : PanelHingeFramework.RecordsLinks G ends') :
    ∀ e u v, G.IsLink e u v →
      ((ends' e).1 = (ends e).1 ∧ (ends' e).2 = (ends e).2) ∨
      ((ends' e).1 = (ends e).2 ∧ (ends' e).2 = (ends e).1) :=
  fun _ _ _ he => (hlinks'.isLink he).eq_and_eq_or_eq_and_eq (hlinks.isLink he)

/-- Other: the rows form's / GP4 form's link conjunct, from the field. -/
theorem hends_of_field (Q : PanelHingeFramework K k α β) {G : Graph α β} (hQg : Q.graph = G) :
    ∀ e u v, G.IsLink e u v → G.IsLink e (Q.ends e).1 (Q.ends e).2 :=
  PanelHingeFramework.recordsLinks_iff_forall_isLink.mp (hQg ▸ Q.isLink_ends)

end Recon41b

#print axioms Recon41b.hasGenericFullRankRealization_iff
#print axioms Recon41b.restated_theorem56_false_at_banana
