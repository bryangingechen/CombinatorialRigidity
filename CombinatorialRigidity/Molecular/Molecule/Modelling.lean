/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Duality
import CombinatorialRigidity.Molecular.Molecule.Theorem56

/-!
# The rank-carrying panel-hinge ↔ molecular equivalence (`thm:panel-hinge-iff-molecular`)

Phase 25, leaf W7 (second half; `notes/Phase25-design.md` §2.6). This file composes the two
Phase-25 endpoints into the load-bearing existence statement the molecule-application capstone
(Corollary 5.7, Phase 26) consumes: a simple spanning graph `G` in `ℝ³` carries a **molecular**
realization whose motion space attains the target dimension `dim Z = D + def(G̃)` and whose atom
centres are in general position up to order four.

The construction is the projective **pole bridge**. Theorem 5.6 in its general-position form
(`PanelHingeFramework.exists_rankHypothesis_isGeneralPosition4`, leaf W6) supplies a *panel*-hinge
realization `Q` at the target rank whose normals are in general position up to order four — in
particular each normal has a nonvanishing last coordinate. Dehomogenizing each normal by its last
coordinate produces the atom centres `c v` (its pole), and:

* the homogenized pole `(c v, 1)` is the normal `Q.normal v` rescaled by the nonzero
  `Q.normal v (Fin.last 3)⁻¹`, so the panel-hinge framework on the homogenized poles differs from
  `Q` only by a per-edge nonzero rescaling of the supporting extensors — hence has the same motion
  space and realized rank (`thm:projective-invariance`, the rescaling sibling
  `infinitesimalMotions_scaleExtensor`, applied through the span-refinement primitive
  `infinitesimalMotions_mono_of_span_le`);
* the projective-duality lemma `lem:panel-hinge-dual-molecular`
  (`rankHypothesis_ofNormals_homogenize_iff`) then transports that realized rank across the polarity
  to the *molecular* framework on the centres `c`; and
* order-four linear independence of the normals is, through the homogenization bridge
  `affineIndependent_iff_linearIndependent_homogenize`, exactly order-four affine independence of
  the poles, i.e. `SimpleGraph.IsGeneralPositionPlacement c`.

See `notes/Phase25.md` and `notes/Phase25-design.md` §2.6 (leaf W7), and
`blueprint/src/chapter/molecule-modelling.tex` (`thm:panel-hinge-iff-molecular`).

## Main results

* `CombinatorialRigidity.Molecular.exists_molecular_rankHypothesis_generalPosition` — the
  rank-carrying panel-hinge ⇔ molecular equivalence in existence form: a simple spanning graph on
  `≥ 1` body in `ℝ³` with enough hinge labels has a molecular realization on centres in general
  position up to order four attaining `dim Z = D + def(G̃)`, whose endpoint selector genuinely
  records every `G`-link.
-/

open scoped Matrix Graph
open WithLp

namespace CombinatorialRigidity.Molecular

variable {α β : Type*}

set_option linter.unusedDecidableInType false in
/-- **The rank-carrying panel-hinge ⇔ molecular equivalence, existence form**
(`thm:panel-hinge-iff-molecular`; Katoh–Tanigawa 2011 p. 671, the modelling equivalence Whiteley
[35] / Jackson–Jordán 2008 state; Phase 25 leaf W7, §2.6 of `notes/Phase25-design.md`). For a simple
spanning graph `G` on `≥ 1` body in `ℝ³` with enough hinge labels there is an endpoint selector
`ends` and a placement `c : α → ℝ³` of the atom centres such that

* the **molecular** framework on `c` realizes the target rank `dim Z = D + def(G̃)`
  (`RankHypothesis (G.deficiency 3)`);
* the centres are in general position up to order four (`SimpleGraph.IsGeneralPositionPlacement`);
  and
* `ends` genuinely records every `G`-link (`∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1
  (ends e).2`) — the `hends` compatibility fact the square-graph dictionary
  (`molecular_finrank_motions_eq_square_ker`) needs for the *same* `ends` this theorem returns.

This is the endpoint the molecule-application capstone (Corollary 5.7, Phase 26) consumes on the
molecular side; the bar-joint side of the dictionary is `molecular_finrank_motions_eq_square_ker`.

The proof is the projective pole bridge: Theorem 5.6's general-position form
(`PanelHingeFramework.exists_rankHypothesis_isGeneralPosition4`) supplies a panel realization `Q` at
the target rank with normals in general position up to order four; dehomogenizing each normal by its
(nonzero) last coordinate gives the centres `c`; the homogenized poles are `Q`'s normals rescaled by
nonzero scalars, so the panel framework on them has the same motion space as `Q`
(`infinitesimalMotions_mono_of_span_le`, since only the hinge spans enter the constraint); the
projective-duality lemma (`rankHypothesis_ofNormals_homogenize_iff`) carries the rank to the
molecular framework; and order-four linear independence of the normals is order-four affine
independence of the poles (`affineIndependent_iff_linearIndependent_homogenize`).

`[DecidableEq β]` is used through the Theorem-5.6 producer but does not appear in the conclusion's
type; the `unusedDecidableInType` suppression is correct here, as in
`exists_rankHypothesis_isGeneralPosition4`. -/
theorem exists_molecular_rankHypothesis_generalPosition
    [Nonempty α] [Finite α] [Finite β] [DecidableEq β]
    (hcard : 6 * (Nat.card α - 1) < Nat.card β)
    (G : Graph α β) (hne : V(G).Nonempty) (hspan : V(G) = Set.univ) (hSimple : G.Simple) :
    ∃ (ends : β → α × α) (c : α → EuclideanSpace ℝ (Fin 3)),
      (molecularOfCentres G ends c).RankHypothesis (G.deficiency 3)
      ∧ SimpleGraph.IsGeneralPositionPlacement c
      ∧ (∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2) := by
  classical
  -- Step 1: the general-position form of Theorem 5.6 supplies a panel realization `Q`.
  obtain ⟨Q, hQg, hQends, _hQC, hQrank, hQgp4⟩ :=
    PanelHingeFramework.exists_rankHypothesis_isGeneralPosition4 hcard G hne hspan hSimple
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
  · -- RankHypothesis: transport `Q`'s rank across the rescaling + the projective duality.
    rw [← rankHypothesis_ofNormals_homogenize_iff G Q.ends c (G.deficiency 3)]
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
