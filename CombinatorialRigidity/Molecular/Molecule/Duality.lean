/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Dictionary
import CombinatorialRigidity.Molecular.Molecule.ProjectiveInvariance
import CombinatorialRigidity.Molecular.AlgebraicInduction.PanelHinge

/-!
# The panel-hinge ↔ molecular projective duality (`lem:panel-hinge-dual-molecular`)

Phase 25, leaf W7 (`notes/Phase25-design.md` §1.3, §2.2). In `ℝ³` the projective polarity sends
points to planes and lines to lines; Crapo–Whiteley's projective invariance of infinitesimal
rigidity (§2.2, `thm:projective-invariance`) then makes a hinge-concurrent body-hinge (molecular)
framework and its dual panel-hinge framework transports of one another along the fixed screw
automorphism the polarity induces.

The whole duality is already in tree: the landed panel layer factors through the projective
polarity as `panelSupportExtensor = complementIso ∘ normalsJoin`
(`AlgebraicInduction/PanelLayer.lean`), and the molecular hinge extensor `lineExtensor a b` shares
its underlying `⋀²`-element `extensor ![â, b̂]` with the grade-2 join `normalsJoin â b̂`. So the
polarity is the meet-complement isomorphism `complementIso` (Phase 21a, `Molecular/Meet.lean`)
conjugated by the boundary equivalence `ScrewSpace.equivExteriorPower` — a fixed linear automorphism
`screwComplementIso` of `ScrewSpace 2 = ⋀²ℝ⁴` — and this file needs *no* new duality machinery
beyond instantiating the extensor-transport family `BodyHingeFramework.mapExtensor` (leaf W2) at
`Λ := screwComplementIso`.

## Main definitions

* `screwComplementIso` — the projective polarity of `ℝ³` as a linear automorphism of the screw
  space `ScrewSpace 2`, i.e. `complementIso` conjugated by `ScrewSpace.equivExteriorPower`.

## Main results

* `screwComplementIso_lineExtensor` — the extensor-level polarity identity `screwComplementIso
  (lineExtensor a b) = panelSupportExtensor (â) (b̂)` (join of the poles ↔ meet of the panels).
* `molecularOfCentres_mapExtensor_screwComplementIso` — the dual correspondence: the panel-hinge
  framework on the homogenized centres is the transport of the molecular framework on the centres
  along `screwComplementIso`.
* `finrank_infinitesimalMotions_ofNormals_homogenize`,
  `rankHypothesis_ofNormals_homogenize_iff`,
  `isInfinitesimallyRigid_ofNormals_homogenize_iff`,
  `supportExtensor_ofNormals_homogenize_ne_zero_iff` — the motion-space dimension, realized rank
  (`RankHypothesis`), infinitesimal rigidity, and genuine-hinge condition all agree between the two
  sides, since transport along a linear automorphism preserves each (leaf W2).

See `notes/Phase25.md` and `notes/Phase25-design.md` §1.3, §2.2 (leaf W7), and
`blueprint/src/chapter/molecule-modelling.tex` (`lem:panel-hinge-dual-molecular`).
-/

open scoped Matrix
open WithLp

namespace CombinatorialRigidity.Molecular

variable {V β : Type*}

/-! ## The projective polarity as a screw-space automorphism -/

/-- **The projective polarity of `ℝ³` as a linear automorphism of the screw space**
(`lem:panel-hinge-dual-molecular`; Crapo–Whiteley 1982 §3.6, the correlation case): the
meet-complement isomorphism `complementIso : ⋀²ℝ⁴ ≃ₗ ⋀^(2+2−2)ℝ⁴ = ⋀²ℝ⁴` (Phase 21a,
`Molecular/Meet.lean`), conjugated by the boundary equivalence `ScrewSpace.equivExteriorPower`
so that it acts on the screw carrier `ScrewSpace 2` directly. This is the fixed automorphism
`Λ` of `thm:projective-invariance` that the panel-hinge ↔ molecular duality transports along;
under the standard polarity (KT §5.1) it carries the line through two poles to the meet of the
two panels. -/
noncomputable def screwComplementIso : ScrewSpace 2 ≃ₗ[ℝ] ScrewSpace 2 :=
  (ScrewSpace.equivExteriorPower 2) ≪≫ₗ
    complementIso (k := 2) (j := 2) (by omega) ≪≫ₗ
    (ScrewSpace.equivExteriorPower 2).symm

/-- **The boundary equivalence carries the line extensor to the grade-2 join of the homogenized
points** (`lem:panel-hinge-dual-molecular`): `ScrewSpace.equivExteriorPower 2 (lineExtensor a b) =
normalsJoin (â) (b̂)`. Both are the same underlying `⋀²ℝ⁴`-element
`exteriorPower.ιMulti ℝ 2 ![â, b̂] = extensor ![â, b̂]` (`equivExteriorPower_mk_extensor`,
`normalsJoin`). -/
theorem equivExteriorPower_lineExtensor (a b : Fin 3 → ℝ) :
    ScrewSpace.equivExteriorPower 2 (lineExtensor a b)
      = normalsJoin (homogenize a) (homogenize b) := by
  rw [lineExtensor, equivExteriorPower_mk_extensor, normalsJoin]

/-- **The extensor-level polarity identity** (`lem:panel-hinge-dual-molecular`, the
Grassmann–Cayley duality "join of poles = complement of the panel-normal join"):
`screwComplementIso (lineExtensor a b) = panelSupportExtensor (â) (b̂)`. The line `2`-extensor
`â ∨ b̂` (the molecular hinge through `a`, `b`) and the grade-2 join `normalsJoin â b̂` share the
underlying element `extensor ![â, b̂]` (`equivExteriorPower_lineExtensor`), and
`panelSupportExtensor = complementIso ∘ normalsJoin` by definition, so applying the conjugated
complement iso `screwComplementIso` to the line extensor reproduces the panel support extensor of
the two homogenized normals. -/
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
    rw [BodyHingeFramework.mapExtensor_supportExtensor, molecularOfCentres_supportExtensor,
      screwComplementIso_lineExtensor, PanelHingeFramework.toBodyHinge_supportExtensor,
      PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal,
      PanelHingeFramework.ofNormals_normal]
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

/-- **The realized-rank hypothesis transfers across the duality** (`lem:panel-hinge-dual-molecular`,
`def:rank-hypothesis`): the panel-hinge framework on the homogenized centres realizes the target
rank `dim Z = D + k'` iff the molecular framework on the centres does, since the polarity transport
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

/-- **Genuine hinges correspond across the duality** (`lem:panel-hinge-dual-molecular`): the panel
hinge at `e` is genuine (nonzero supporting extensor, i.e. its two panels are transversal) iff the
molecular hinge at `e` is genuine (its two endpoint centres are distinct), since a linear
automorphism sends nonzero to nonzero (`supportExtensor_mapExtensor_ne_zero`). -/
theorem supportExtensor_ofNormals_homogenize_ne_zero_iff
    (G : Graph V β) (ends : β → V × V) (c : V → EuclideanSpace ℝ (Fin 3)) (e : β) :
    (PanelHingeFramework.ofNormals G ends
        (fun p => homogenize (ofLp (c p.1)) p.2)).toBodyHinge.supportExtensor e ≠ 0
      ↔ (molecularOfCentres G ends c).supportExtensor e ≠ 0 := by
  rw [← molecularOfCentres_mapExtensor_screwComplementIso,
    BodyHingeFramework.supportExtensor_mapExtensor_ne_zero]

end CombinatorialRigidity.Molecular
