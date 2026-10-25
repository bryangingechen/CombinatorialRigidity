/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Duality
public import CombinatorialRigidity.Molecular.Molecule.Theorem56

/-!
# Molecular realizations at the target rank

The molecular realization of `thm:panel-hinge-iff-molecular`, as
`sec:molecule-modelling-general-position` presents it: a simple graph `G` that spans a nonempty set
of bodies in `ℝ³`, with more than `6(|V| - 1)` labels, has a molecular realization whose motion
space has dimension `D + def(G̃)` and whose centres are in general position up to order four. Katoh
and Tanigawa deduce from their Theorem 5.6, by projective duality, that a simple graph has a
molecular realization at this rank (KT p. 671); infinitesimal rigidity is invariant under a polarity
(Crapo and Whiteley 1982, §3.6).

The centres are the poles of the normals of the panel-hinge realization `Q` of
`lem:theorem-56-general-position` (`PanelHingeFramework.exists_rankHypothesis_isGeneralPosition4`),
which have nonzero last coordinates: the centre `c v` is the first three coordinates of `Q.normal v`
divided by its last. Then

* the homogenized pole `(c v, 1)` is the normal `Q.normal v` rescaled by the nonzero
  `Q.normal v (Fin.last 3)⁻¹`, so the panel-hinge framework on the homogenized poles differs from
  `Q` only by a per-edge nonzero rescaling of the supporting extensors — hence has the same motion
  space and realized rank (`thm:projective-invariance`; the proof shows it from the equal spans of
  the supporting extensors by `infinitesimalMotions_mono_of_span_le`, in both directions);
* the polarity (`lem:panel-hinge-dual-molecular`, `rankHypothesis_ofNormals_homogenize_iff`)
  transfers that rank to the *molecular* framework on the centres `c`; and
* linear independence of four or fewer normals is, through the homogenization
  (`affineIndependent_iff_linearIndependent_homogenize`), affine independence of their poles, so the
  centres are in general position up to order four (`SimpleGraph.IsGeneralPositionPlacement`).

## Main results

* `CombinatorialRigidity.Molecular.exists_molecular_rankHypothesis_generalPosition`: a simple graph
  that spans a nonempty set of bodies in `ℝ³`, with more than `6(|V| - 1)` labels, has a molecular
  realization on centres in general position up to order four with `dim Z = D + def(G̃)`, whose
  endpoint selector records every `G`-link.
-/

@[expose] public section

open scoped Matrix Graph
open WithLp

namespace CombinatorialRigidity.Molecular

variable {α β : Type*}

/-- **Molecular realizations at the target rank** (`thm:panel-hinge-iff-molecular`; Katoh and
Tanigawa 2011, p. 671): for a simple graph `G` that spans a nonempty set of bodies in `ℝ³`, with
more than `6(|V| - 1)` labels, there is an endpoint selector `ends` and a placement `c : α → ℝ³` of
the atom centres such that

* the **molecular** framework on `c` realizes the target rank `dim Z = D + def(G̃)`
  (`RankHypothesis (G.deficiency 3)`);
* the centres are in general position up to order four (`SimpleGraph.IsGeneralPositionPlacement`);
  and
* `ends` records every `G`-link (`∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2`) — the
  `hends` compatibility fact the square-graph dictionary (`molecular_finrank_motions_eq_square_ker`)
  needs for the *same* `ends` this theorem returns.

`molecule_rank_lower_bound` (`lem:molecule-rank-lower-bound`) applies it with the square-graph
dictionary.

The proof takes the poles as centres: KT Theorem 5.6 with the poles in general position
(`PanelHingeFramework.exists_rankHypothesis_isGeneralPosition4`) supplies a panel realization `Q` at
the target rank with normals in general position up to order four; dehomogenizing each normal by its
(nonzero) last coordinate gives the centres `c`; the homogenized poles are `Q`'s normals rescaled by
nonzero scalars, so the panel framework on them has the same motion space as `Q`
(`infinitesimalMotions_mono_of_span_le`, since only the hinge spans enter the constraint); the
polarity (`rankHypothesis_ofNormals_homogenize_iff`) transfers the rank to the molecular framework;
and order-four linear independence of the normals is order-four affine independence of the poles
(`affineIndependent_iff_linearIndependent_homogenize`). -/
theorem exists_molecular_rankHypothesis_generalPosition [Finite α] [Finite β]
    (hcard : 6 * (Nat.card α - 1) < Nat.card β)
    (G : Graph α β) (hne : V(G).Nonempty) (hspan : V(G) = Set.univ) (hSimple : G.Simple) :
    ∃ (ends : β → α × α) (c : α → EuclideanSpace ℝ (Fin 3)),
      (molecularOfCentres G ends c).RankHypothesis (G.deficiency 3)
      ∧ SimpleGraph.IsGeneralPositionPlacement c
      ∧ (∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2) := by
  classical
  -- Step 1: the general-position form of Theorem 5.6 supplies a panel realization `Q`.
  obtain ⟨Q, hQg, _hQC, hQrank, hQgp4, -⟩ :=
    PanelHingeFramework.exists_rankHypothesis_isGeneralPosition4 hcard G hne hspan hSimple
  have hQends : ∀ e u v, G.IsLink e u v → G.IsLink e (Q.ends e).1 (Q.ends e).2 :=
    hQg ▸ PanelHingeFramework.recordsLinks_iff_forall_isLink.mp Q.isLink_ends
  -- The last coordinates of `Q`'s normals are nonzero (general position up to order four).
  have hw : ∀ a, Q.normal a (Fin.last 3) ≠ 0 := hQgp4.1
  -- The atom centres are the dehomogenized poles of `Q`'s normals.
  set c : α → EuclideanSpace ℝ (Fin 3) :=
    fun a => toLp 2 (fun i : Fin 3 => (Q.normal a (Fin.last 3))⁻¹ * Q.normal a i.castSucc)
    with hc_def
  -- The homogenized pole `(c a, 1)` is the normal `Q.normal a` rescaled by its inverse last coord.
  have hhomog : ∀ a, homogenize (ofLp (c a)) = (Q.normal a (Fin.last 3))⁻¹ • Q.normal a := by
    intro a
    funext i
    simp only [hc_def, WithLp.ofLp_toLp]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [homogenize_last]
      simp only [Pi.smul_apply, smul_eq_mul]
      exact (inv_mul_cancel₀ (hw a)).symm
    · rw [homogenize_castSucc]
      simp only [Pi.smul_apply, smul_eq_mul]
  -- The panel support extensor is homogeneous in its second normal too (swap + first-column form).
  have smul_right : ∀ (t : ℝ) (n₁ n₂ : Fin (2 + 2) → ℝ),
      panelSupportExtensor n₁ (t • n₂) = t • panelSupportExtensor (k := 2) n₁ n₂ := by
    intro t n₁ n₂
    rw [panelSupportExtensor_swap (t • n₂) n₁, panelSupportExtensor_smul_left,
      panelSupportExtensor_swap n₁ n₂, smul_neg, neg_neg]
  refine ⟨Q.ends, c, ?_, ?_, hQends⟩
  · -- `RankHypothesis`: `Q`'s rank, across the rescaling and the polarity.
    rw [← rankHypothesis_ofNormals_homogenize_iff G Q.ends (hlinks := by link_tac) c
      (G.deficiency 3)]
    set P := PanelHingeFramework.ofNormals (k := 2) G Q.ends
      (fun p => homogenize (ofLp (c p.1)) p.2) with hP
    -- `P` (on the homogenized poles) has `Q`'s motion space (its extensors are `Q`'s, rescaled).
    have hspaneq : ∀ e, Submodule.span ℝ {P.toBodyHinge.supportExtensor e}
          = Submodule.span ℝ {Q.toBodyHinge.supportExtensor e} := by
      intro e
      have hL : P.toBodyHinge.supportExtensor e
          = ((Q.normal (Q.ends e).1 (Fin.last 3))⁻¹ * (Q.normal (Q.ends e).2 (Fin.last 3))⁻¹)
            • Q.toBodyHinge.supportExtensor e := by
        change panelSupportExtensor (homogenize (ofLp (c (Q.ends e).1)))
              (homogenize (ofLp (c (Q.ends e).2)))
            = ((Q.normal (Q.ends e).1 (Fin.last 3))⁻¹ * (Q.normal (Q.ends e).2 (Fin.last 3))⁻¹)
              • panelSupportExtensor (Q.normal (Q.ends e).1) (Q.normal (Q.ends e).2)
        rw [hhomog (Q.ends e).1, hhomog (Q.ends e).2, panelSupportExtensor_smul_left,
          smul_right, smul_smul]
      rw [hL]
      exact Submodule.span_singleton_smul_eq
        (mul_ne_zero (inv_ne_zero (hw (Q.ends e).1)) (inv_ne_zero (hw (Q.ends e).2))).isUnit _
    have hmotions : P.toBodyHinge.infinitesimalMotions = Q.toBodyHinge.infinitesimalMotions :=
      le_antisymm
        (Q.toBodyHinge.infinitesimalMotions_mono_of_span_le _ hQg (fun e => (hspaneq e).le))
        (P.toBodyHinge.infinitesimalMotions_mono_of_span_le _ hQg.symm (fun e => (hspaneq e).ge))
    change (Module.finrank ℝ P.toBodyHinge.infinitesimalMotions : ℤ) = screwDim 2 + G.deficiency 3
    rw [hmotions]
    exact hQrank
  · -- General position of the centres = order-four linear independence of the normals.
    intro s hs
    -- Linear independence of the homogenized poles, by rescaling `Q`'s order-four independence.
    have hLIhom : LinearIndependent ℝ (fun a : ↥s => homogenize (ofLp (c ↑a))) := by
      have hkey := (hQgp4.2 s hs).units_smul
        (fun a : ↥s => Units.mk0 ((Q.normal ↑a (Fin.last 3))⁻¹) (inv_ne_zero (hw ↑a)))
      have heq : ((fun a : ↥s => Units.mk0 ((Q.normal ↑a (Fin.last 3))⁻¹) (inv_ne_zero (hw ↑a)))
              • (fun a : ↥s => Q.normal ↑a))
            = fun a : ↥s => homogenize (ofLp (c ↑a)) := by
        funext a
        simp only [Pi.smul_apply', Units.smul_def, Units.val_mk0]
        exact (hhomog ↑a).symm
      rwa [heq] at hkey
    -- Affine independence of the poles, then transport across `toLp` to the centres.
    have hAIpole : AffineIndependent ℝ (fun a : ↥s => ofLp (c ↑a)) :=
      (affineIndependent_iff_linearIndependent_homogenize (fun a : ↥s => ofLp (c ↑a))).mpr hLIhom
    set f : (Fin 3 → ℝ) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3) :=
      (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toLinearMap.toAffineMap with hf
    have hfinj : Function.Injective f := by
      rw [hf, LinearMap.coe_toAffineMap]
      exact (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.injective
    have hcomp : (⇑f ∘ fun a : ↥s => ofLp (c ↑a)) = fun a : ↥s => c ↑a := by
      funext a
      change f (ofLp (c ↑a)) = c ↑a
      rw [hf, LinearMap.coe_toAffineMap]
      exact WithLp.toLp_ofLp 2 (c ↑a)
    rw [← hcomp]
    exact hAIpole.map' f hfinj

end CombinatorialRigidity.Molecular
