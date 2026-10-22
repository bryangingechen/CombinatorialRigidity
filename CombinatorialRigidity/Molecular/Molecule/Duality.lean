/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Dictionary
import CombinatorialRigidity.Molecular.Molecule.ProjectiveInvariance
import CombinatorialRigidity.Molecular.AlgebraicInduction.PanelHinge

/-!
# The polarity, and the panel-hinge framework dual to a molecular framework

The polarity of projective `3`-space as a linear automorphism of the screw space, and the
correspondence it gives between molecular and panel-hinge frameworks, as
`sec:molecule-modelling-projective` presents them (`lem:polarity-join`,
`lem:panel-hinge-dual-molecular`). A polarity sends points to planes and lines to lines. Crapo and
Whiteley 1982 (§3.6) observe that it preserves the infinitesimal motions of a body-hinge framework,
and Katoh and Tanigawa 2011 (pp. 650 and 671) that it sends a hinge-concurrent body-hinge framework
to a panel-hinge framework.

The polarity is `screwComplementIso`, the complement isomorphism `complementIso` of `Meet.lean`
(`def:meet-complement-iso`) on `⋀² K⁴`, conjugated by the boundary equivalence
`ScrewSpace.equivExteriorPower`. The panel support extensor is `C(n₁, n₂) = complementIso (n₁ ∨ n₂)`
(`def:panel-support-extensor`), and the extensor `lineExtensor a b` of a molecular hinge is the join
`â ∨ b̂`, so the polarity sends the hinge through `a` and `b` to `C(â, b̂)`
(`screwComplementIso_lineExtensor`). Hence the panel-hinge framework with the normal
`ĉ(v) = (c v, 1)` at each body `v` is the molecular framework on the centres `c`, on the same
multigraph and selector, transported along the polarity (`BodyHingeFramework.mapExtensor`), and
`thm:projective-invariance` transfers the dimension of the motion space, the rank hypothesis,
rigidity and the nondegeneracy of each hinge.

## Main definitions

* `screwComplementIso`: the polarity, a linear automorphism of `ScrewSpace K 2` over any field `K`.

## Main results

* `screwComplementIso_lineExtensor`: `screwComplementIso (lineExtensor a b)` is the panel support
  extensor of `â` and `b̂`.
* `molecularOfCentres_mapExtensor_screwComplementIso`: the panel-hinge framework with the normals
  `ĉ(v)` is the molecular framework on the centres `c` transported along the polarity.
* `finrank_infinitesimalMotions_ofNormals_homogenize`, `rankHypothesis_ofNormals_homogenize_iff`,
  `isInfinitesimallyRigid_ofNormals_homogenize_iff` and
  `supportExtensor_ofNormals_homogenize_ne_zero_iff`: the two frameworks have motion spaces of the
  same dimension, satisfy the same rank hypotheses, are infinitesimally rigid together, and have
  nonzero hinges at the same edge labels.
-/

open scoped Matrix
open WithLp

namespace CombinatorialRigidity.Molecular

variable {V β : Type*}

/-! ## The projective polarity as a screw-space automorphism -/

/-- **The polarity** (`lem:polarity-join`): the complement isomorphism
`complementIso : ⋀²K⁴ ≃ₗ ⋀^(2+2−2)K⁴ = ⋀²K⁴` of `Meet.lean` (`def:meet-complement-iso`), conjugated
by the boundary equivalence `ScrewSpace.equivExteriorPower`, so that it acts on the screw space
`ScrewSpace K 2` itself, over any field `K`. It is the automorphism `Λ` at which
`lem:panel-hinge-dual-molecular` applies `thm:projective-invariance`: the map that a correlation
induces on the lines of projective `3`-space (Crapo and Whiteley 1982, §3.6). Over `ℝ` it sends the
extensor of the line through two points `a` and `b` to that of the meet of the planes with the
normals `â` and `b̂` (`screwComplementIso_lineExtensor`), the panels that Katoh and Tanigawa attach
to `a` and `b` (KT §5.1, p. 668). -/
noncomputable def screwComplementIso {K : Type*} [Field K] : ScrewSpace K 2 ≃ₗ[K] ScrewSpace K 2 :=
  (ScrewSpace.equivExteriorPower K 2) ≪≫ₗ
    complementIso (k := 2) (j := 2) (by omega) ≪≫ₗ
    (ScrewSpace.equivExteriorPower K 2).symm

/-- **The extensor of a line is the join of the homogenized points** (a step of
`lem:polarity-join`): `ScrewSpace.equivExteriorPower ℝ 2 (lineExtensor a b) = normalsJoin (â) (b̂)`.
Both are the element `exteriorPower.ιMulti ℝ 2 ![â, b̂] = extensor ![â, b̂]` of `⋀²ℝ⁴`
(`equivExteriorPower_mk_extensor`, `normalsJoin`). -/
theorem equivExteriorPower_lineExtensor (a b : Fin 3 → ℝ) :
    ScrewSpace.equivExteriorPower ℝ 2 (lineExtensor a b)
      = normalsJoin (homogenize a) (homogenize b) := by
  rw [lineExtensor, equivExteriorPower_mk_extensor, normalsJoin]

/-- **The polarity on the extensor of a line** (`lem:polarity-join`):
`screwComplementIso (lineExtensor a b) = panelSupportExtensor (â) (b̂)`. The extensor `â ∨ b̂` of
the line through `a` and `b` and the join `normalsJoin â b̂` are the same element
`extensor ![â, b̂]` (`equivExteriorPower_lineExtensor`), and `panelSupportExtensor` is
`complementIso ∘ normalsJoin` by definition. -/
theorem screwComplementIso_lineExtensor (a b : Fin 3 → ℝ) :
    screwComplementIso (lineExtensor a b)
      = panelSupportExtensor (homogenize a) (homogenize b) := by
  rw [screwComplementIso, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    equivExteriorPower_lineExtensor, panelSupportExtensor,
    ScrewSpace.equivExteriorPower_symm_apply]
  rfl

/-! ## The dual correspondence: the two frameworks are transports of one another -/

/-- **The panel-hinge framework on the homogenized centres is the polarity transport of the
molecular framework** (`lem:panel-hinge-dual-molecular`, the dual correspondence): for a placement
`c : V → ℝ³` of body centres, the body-hinge interpretation of the panel-hinge framework whose
panel normal at each body `v` is the homogenized centre `(c v, 1)` equals the molecular framework
on the centres `c` transported along the fixed screw automorphism `screwComplementIso`
(`thm:projective-invariance` at `Λ := screwComplementIso`). Both frameworks carry the same
multigraph `G`, and edgewise their supporting extensors agree by the extensor-level polarity
identity `screwComplementIso_lineExtensor`. -/
theorem molecularOfCentres_mapExtensor_screwComplementIso
    (G : Graph V β) (ends : β → V × V) (c : V → EuclideanSpace ℝ (Fin 3)) :
    (molecularOfCentres G ends c).mapExtensor screwComplementIso
      = (PanelHingeFramework.ofNormals G ends
          (fun p => homogenize (ofLp (c p.1)) p.2)).toBodyHinge := by
  have hsupp : ((molecularOfCentres G ends c).mapExtensor screwComplementIso).supportExtensor
      = (PanelHingeFramework.ofNormals G ends
          (fun p => homogenize (ofLp (c p.1)) p.2)).toBodyHinge.supportExtensor := by
    funext e
    simp only [BodyHingeFramework.mapExtensor_supportExtensor, molecularOfCentres_supportExtensor,
      screwComplementIso_lineExtensor, PanelHingeFramework.toBodyHinge_supportExtensor,
      PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal]
  exact congrArg (BodyHingeFramework.mk (k := 2) G) hsupp

/-- **The two motion spaces have equal dimension** (`lem:panel-hinge-dual-molecular`): the
infinitesimal-motion space of the panel-hinge framework on the homogenized centres and that of the
molecular framework on the centres have the same dimension, since one is the image of the other
under a linear automorphism (`molecularOfCentres_mapExtensor_screwComplementIso`,
`finrank_infinitesimalMotions_mapExtensor`). Equivalently the realized ranks agree. -/
theorem finrank_infinitesimalMotions_ofNormals_homogenize
    (G : Graph V β) (ends : β → V × V) (c : V → EuclideanSpace ℝ (Fin 3)) :
    Module.finrank ℝ (PanelHingeFramework.ofNormals G ends
        (fun p => homogenize (ofLp (c p.1)) p.2)).toBodyHinge.infinitesimalMotions
      = Module.finrank ℝ (molecularOfCentres G ends c).infinitesimalMotions := by
  rw [← molecularOfCentres_mapExtensor_screwComplementIso,
    BodyHingeFramework.finrank_infinitesimalMotions_mapExtensor]

/-- **The rank hypothesis transfers across the duality** (`lem:panel-hinge-dual-molecular`,
`def:rank-hypothesis`): the panel-hinge framework on the homogenized centres satisfies
`dim Z = D + k'` iff the molecular framework on the centres does, since the polarity transport
preserves the motion-space dimension (`finrank_infinitesimalMotions_ofNormals_homogenize`). -/
theorem rankHypothesis_ofNormals_homogenize_iff
    (G : Graph V β) (ends : β → V × V) (c : V → EuclideanSpace ℝ (Fin 3)) (k' : ℤ) :
    (PanelHingeFramework.ofNormals G ends
        (fun p => homogenize (ofLp (c p.1)) p.2)).toBodyHinge.RankHypothesis k'
      ↔ (molecularOfCentres G ends c).RankHypothesis k' := by
  rw [← molecularOfCentres_mapExtensor_screwComplementIso,
    BodyHingeFramework.rankHypothesis_mapExtensor]

/-- **Infinitesimal rigidity transfers across the duality** (`lem:panel-hinge-dual-molecular`): the
panel-hinge framework on the homogenized centres is infinitesimally rigid iff the molecular
framework on the centres is, since transport along the polarity carries motions to motions and
trivial to trivial (`isInfinitesimallyRigid_mapExtensor`). -/
theorem isInfinitesimallyRigid_ofNormals_homogenize_iff
    (G : Graph V β) (ends : β → V × V) (c : V → EuclideanSpace ℝ (Fin 3)) :
    (PanelHingeFramework.ofNormals G ends
        (fun p => homogenize (ofLp (c p.1)) p.2)).toBodyHinge.IsInfinitesimallyRigid
      ↔ (molecularOfCentres G ends c).IsInfinitesimallyRigid := by
  rw [← molecularOfCentres_mapExtensor_screwComplementIso,
    BodyHingeFramework.isInfinitesimallyRigid_mapExtensor]

/-- **Nondegenerate hinges correspond across the duality** (`lem:panel-hinge-dual-molecular`): the
panel hinge at `e` is nondegenerate (nonzero supporting extensor, i.e. its two panels are
transversal) iff the molecular hinge at `e` is nondegenerate (its two endpoint centres are
distinct), since a linear automorphism sends nonzero to nonzero
(`supportExtensor_mapExtensor_ne_zero`). -/
theorem supportExtensor_ofNormals_homogenize_ne_zero_iff
    (G : Graph V β) (ends : β → V × V) (c : V → EuclideanSpace ℝ (Fin 3)) (e : β) :
    (PanelHingeFramework.ofNormals G ends
        (fun p => homogenize (ofLp (c p.1)) p.2)).toBodyHinge.supportExtensor e ≠ 0
      ↔ (molecularOfCentres G ends c).supportExtensor e ≠ 0 := by
  rw [← molecularOfCentres_mapExtensor_screwComplementIso,
    BodyHingeFramework.supportExtensor_mapExtensor_ne_zero]

end CombinatorialRigidity.Molecular
