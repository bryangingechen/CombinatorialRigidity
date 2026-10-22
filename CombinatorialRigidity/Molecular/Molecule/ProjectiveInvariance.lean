/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.AlgebraicInduction.Pinning

/-!
# Projective invariance of infinitesimal rigidity

The transport of a body-hinge framework along a linear automorphism `Λ` of the screw space, and the
invariance of its motions, as `sec:molecule-modelling-projective` presents them
(`thm:projective-invariance`). Crapo and Whiteley 1982 (§3.6) observe that a projective
transformation of space, a collineation or a correlation, is a nonsingular linear map of the
homogeneous coordinates, and that it induces a linear automorphism `Λ` of the space of screws, which
carries a panel structure to a panel structure by transforming its hinges and takes instantaneous
motions to instantaneous motions. A body-hinge framework is read through the spans of its supporting
extensors alone (the hinge constraint `S u − S v ∈ span {C(p(e))}`, `hingeConstraint`), so the
argument is a transport: the framework `F.mapExtensor Λ` (`RigidityMatrix/Basic.lean`), with the
same graph and the supporting extensor `Λ C(p(e))` at each edge `e`, has as motions the images of
those of `F` under `S ↦ Λ ∘ S`. So the dimension of the motion space, the rank hypothesis and
infinitesimal rigidity are unchanged. The proofs use only that `Λ` is linear and invertible, so the
results hold over any field `K` and in every dimension. The rank of the rigidity matrix is compared
directly by `finrank_span_rigidityRows_mapExtensor` (`lem:screw-map-rows`,
`GenericLift/HingeGeneric.lean`).

The motion space is also unchanged when each supporting extensor is multiplied by a nonzero scalar
(`scaleExtensor`), as only the spans enter the hinge constraint.

`lem:panel-hinge-dual-molecular` applies the theorem to the polarity (`Molecule/Duality.lean`).

## Main definitions

* `BodyHingeFramework.scaleExtensor F c`: each supporting extensor multiplied by `c e : K`.

## Main results

* `BodyHingeFramework.infinitesimalMotions_mapExtensor`: `Z(mapExtensor F Λ)` is the image of `Z(F)`
  under the bodywise map `S ↦ Λ ∘ S`.
* `BodyHingeFramework.finrank_infinitesimalMotions_mapExtensor`,
  `BodyHingeFramework.rankHypothesis_mapExtensor`: the dimension of the motion space, and hence the
  rank hypothesis (`RankHypothesis`), are preserved.
* `BodyHingeFramework.isInfinitesimallyRigid_mapExtensor`,
  `BodyHingeFramework.isInfinitesimallyRigidOn_mapExtensor`: infinitesimal rigidity transfers.
* `BodyHingeFramework.supportExtensor_mapExtensor_ne_zero`: a hinge is nondegenerate on one side iff
  on the other.
* `BodyHingeFramework.infinitesimalMotions_scaleExtensor`: multiplying each supporting extensor by a
  nonzero scalar leaves the motion space unchanged.
-/

namespace CombinatorialRigidity.Molecular

variable {k : ℕ} {K : Type*} [Field K]

namespace BodyHingeFramework

variable {α β : Type*}

/-! ## Transport along a screw-space automorphism (`thm:projective-invariance`) -/

/-- **A linear automorphism carries a span to the span of the image** (a step of
`thm:projective-invariance`): for a linear automorphism `Λ` of the screw space, `Λ w` lies in
`span {Λ C}` iff `w` lies in `span {C}`, as `Λ` is linear and injective. The hinge constraint reads
only these spans. -/
theorem apply_mem_span_singleton_apply (Λ : ScrewSpace K k ≃ₗ[K] ScrewSpace K k)
    (C w : ScrewSpace K k) :
    Λ w ∈ Submodule.span K {Λ C} ↔ w ∈ Submodule.span K {C} := by
  simp only [Submodule.mem_span_singleton]
  refine ⟨fun ⟨a, ha⟩ => ⟨a, Λ.injective ?_⟩, fun ⟨a, ha⟩ => ⟨a, ?_⟩⟩
  · rw [map_smul]; exact ha
  · rw [← ha, map_smul]

/-- **The hinge constraint transports along `Λ`** (a step of `thm:projective-invariance`): a screw
assignment `S` meets the hinge constraint of `F` at `e = uv` iff the transported assignment `Λ ∘ S`
meets the hinge constraint of `F.mapExtensor Λ` there. Immediate from
`apply_mem_span_singleton_apply` applied to the relative screw `S u − S v`. -/
theorem hingeConstraint_mapExtensor (F : BodyHingeFramework K k α β)
    (Λ : ScrewSpace K k ≃ₗ[K] ScrewSpace K k) (S : α → ScrewSpace K k) (e : β) (u v : α) :
    (F.mapExtensor Λ).hingeConstraint (fun w => Λ (S w)) e u v ↔ F.hingeConstraint S e u v := by
  simp only [hingeConstraint, mapExtensor_supportExtensor, ← map_sub]
  exact apply_mem_span_singleton_apply Λ (F.supportExtensor e) (S u - S v)

/-- **Infinitesimal motions transport along `Λ`** (a step of `thm:projective-invariance`): `S` is an
infinitesimal motion of `F` iff `Λ ∘ S` is an infinitesimal motion of `F.mapExtensor Λ`. The graph
is unchanged and each hinge constraint transports (`hingeConstraint_mapExtensor`). -/
theorem isInfinitesimalMotion_mapExtensor (F : BodyHingeFramework K k α β)
    (Λ : ScrewSpace K k ≃ₗ[K] ScrewSpace K k) (S : α → ScrewSpace K k) :
    (F.mapExtensor Λ).IsInfinitesimalMotion (fun w => Λ (S w)) ↔ F.IsInfinitesimalMotion S := by
  constructor
  · intro h e u v he
    exact (F.hingeConstraint_mapExtensor Λ S e u v).mp (h e u v he)
  · intro h e u v he
    exact (F.hingeConstraint_mapExtensor Λ S e u v).mpr (h e u v he)

/-- **Infinitesimal motions transport along `Λ`, at the transported assignment** (a step of
`thm:projective-invariance`): a screw assignment `T` is a motion of `F.mapExtensor Λ` iff `Λ⁻¹ ∘ T`
is a motion of `F`. This is `isInfinitesimalMotion_mapExtensor` at `S = Λ⁻¹ ∘ T`, as
`Λ (Λ⁻¹ (T w)) = T w`. -/
theorem isInfinitesimalMotion_mapExtensor' (F : BodyHingeFramework K k α β)
    (Λ : ScrewSpace K k ≃ₗ[K] ScrewSpace K k) (T : α → ScrewSpace K k) :
    (F.mapExtensor Λ).IsInfinitesimalMotion T
      ↔ F.IsInfinitesimalMotion (fun w => Λ.symm (T w)) := by
  simpa only [LinearEquiv.apply_symm_apply]
    using F.isInfinitesimalMotion_mapExtensor Λ (fun w => Λ.symm (T w))

/-- **The motion space transports along `Λ`** (`thm:projective-invariance`, the first statement):
the infinitesimal-motion space `Z(F.mapExtensor Λ)` is the image of `Z(F)` under the bodywise linear
automorphism `S ↦ Λ ∘ S` (`LinearEquiv.piCongrRight`). This is the projective invariance of Crapo
and Whiteley 1982, §3.6, for every linear automorphism of the screw space. -/
theorem infinitesimalMotions_mapExtensor (F : BodyHingeFramework K k α β)
    (Λ : ScrewSpace K k ≃ₗ[K] ScrewSpace K k) :
    (F.mapExtensor Λ).infinitesimalMotions
      = F.infinitesimalMotions.map
          (LinearEquiv.piCongrRight fun _ : α => Λ : (α → ScrewSpace K k) →ₗ[K] _) := by
  ext T
  rw [Submodule.mem_map_equiv, mem_infinitesimalMotions, mem_infinitesimalMotions,
    isInfinitesimalMotion_mapExtensor']
  have hsymm : (LinearEquiv.piCongrRight fun _ : α => Λ).symm T = fun w => Λ.symm (T w) := by
    ext w
    rw [LinearEquiv.piCongrRight_symm, LinearEquiv.piCongrRight_apply]
  rw [hsymm]

/-- **The motion-space dimension is preserved** (`thm:projective-invariance`): transporting along
a screw-space automorphism `Λ` leaves `dim Z(G,p)` unchanged, since `Z(F.mapExtensor Λ)` is the
image of `Z(F)` under a linear equivalence (`infinitesimalMotions_mapExtensor`,
`LinearEquiv.finrank_map_eq`). Equivalently the realized rank `rank R(G,p)` is unchanged. -/
theorem finrank_infinitesimalMotions_mapExtensor (F : BodyHingeFramework K k α β)
    (Λ : ScrewSpace K k ≃ₗ[K] ScrewSpace K k) :
    Module.finrank K (F.mapExtensor Λ).infinitesimalMotions
      = Module.finrank K F.infinitesimalMotions := by
  rw [infinitesimalMotions_mapExtensor]
  exact LinearEquiv.finrank_map_eq _ _

/-- **The rank hypothesis transfers** (`thm:projective-invariance`, `def:rank-hypothesis`):
`F.mapExtensor Λ` satisfies `dim Z = D + k'` iff `F` does, because the transport preserves the
dimension of the motion space (`finrank_infinitesimalMotions_mapExtensor`). -/
theorem rankHypothesis_mapExtensor (F : BodyHingeFramework K k α β)
    (Λ : ScrewSpace K k ≃ₗ[K] ScrewSpace K k) (k' : ℤ) :
    (F.mapExtensor Λ).RankHypothesis k' ↔ F.RankHypothesis k' := by
  rw [RankHypothesis, RankHypothesis, finrank_infinitesimalMotions_mapExtensor]

/-! ## Rigidity transfer -/

/-- **Triviality of a motion transports along `Λ`** (a step of `thm:projective-invariance`): `Λ ∘ S`
is a trivial motion (constant) iff `S` is, since `Λ` is injective. -/
theorem isTrivialMotion_map_iff (Λ : ScrewSpace K k ≃ₗ[K] ScrewSpace K k) (S : α → ScrewSpace K k) :
    IsTrivialMotion (fun w => Λ (S w)) ↔ IsTrivialMotion S :=
  ⟨fun h u v => Λ.injective (h u v), fun h u v => by dsimp only; rw [h u v]⟩

/-- **Infinitesimal rigidity transfers along `Λ`** (`thm:projective-invariance`): `F.mapExtensor Λ`
is infinitesimally rigid iff `F` is. Every motion of one framework is `Λ ∘ (·)` of a motion of the
other (`isInfinitesimalMotion_mapExtensor`), and triviality transports (`isTrivialMotion_map_iff`),
so "every motion is trivial" holds on one side iff on the other. -/
theorem isInfinitesimallyRigid_mapExtensor (F : BodyHingeFramework K k α β)
    (Λ : ScrewSpace K k ≃ₗ[K] ScrewSpace K k) :
    (F.mapExtensor Λ).IsInfinitesimallyRigid ↔ F.IsInfinitesimallyRigid := by
  rw [isInfinitesimallyRigid_iff, isInfinitesimallyRigid_iff]
  constructor
  · intro h S hS
    have h1 : (F.mapExtensor Λ).IsInfinitesimalMotion (fun w => Λ (S w)) :=
      (F.isInfinitesimalMotion_mapExtensor Λ S).mpr hS
    exact (isTrivialMotion_map_iff Λ S).mp (h _ h1)
  · intro h T hT
    have h1 : F.IsInfinitesimalMotion (fun w => Λ.symm (T w)) :=
      (F.isInfinitesimalMotion_mapExtensor' Λ T).mp hT
    intro u v
    exact Λ.symm.injective (h _ h1 u v)

/-- **Infinitesimal rigidity on a set of bodies transfers along `Λ`** (the form of
`isInfinitesimallyRigid_mapExtensor` on a set `s`): `F.mapExtensor Λ` is infinitesimally rigid on
`s` iff `F` is, by the same argument restricted to the pairs of bodies in `s`. No declaration uses
it. -/
theorem isInfinitesimallyRigidOn_mapExtensor (F : BodyHingeFramework K k α β)
    (Λ : ScrewSpace K k ≃ₗ[K] ScrewSpace K k) (s : Set α) :
    (F.mapExtensor Λ).IsInfinitesimallyRigidOn s ↔ F.IsInfinitesimallyRigidOn s := by
  rw [isInfinitesimallyRigidOn_iff, isInfinitesimallyRigidOn_iff]
  constructor
  · intro h S hS u hu v hv
    have h1 : (F.mapExtensor Λ).IsInfinitesimalMotion (fun w => Λ (S w)) :=
      (F.isInfinitesimalMotion_mapExtensor Λ S).mpr hS
    exact Λ.injective (h _ h1 u hu v hv)
  · intro h T hT u hu v hv
    have h1 : F.IsInfinitesimalMotion (fun w => Λ.symm (T w)) :=
      (F.isInfinitesimalMotion_mapExtensor' Λ T).mp hT
    exact Λ.symm.injective (h _ h1 u hu v hv)

/-- **Nondegenerate hinges transfer along `Λ`** (`thm:projective-invariance`, the second statement):
the supporting extensor at `e` is nonzero after the transport iff it was before, since a linear
equivalence sends nonzero vectors to nonzero vectors. -/
theorem supportExtensor_mapExtensor_ne_zero (F : BodyHingeFramework K k α β)
    (Λ : ScrewSpace K k ≃ₗ[K] ScrewSpace K k) (e : β) :
    (F.mapExtensor Λ).supportExtensor e ≠ 0 ↔ F.supportExtensor e ≠ 0 := by
  simp only [mapExtensor_supportExtensor, ne_eq, map_eq_zero_iff Λ Λ.injective]

/-! ## Multiplying the supporting extensors by nonzero scalars -/

/-- **The framework with rescaled supporting extensors** (the framework of the third statement of
`thm:projective-invariance`): the same graph, with the supporting extensor `c e • C(p(e))` at each
edge `e`. When every `c e` is nonzero it has the motions of `F`, as every hinge span is unchanged
(`infinitesimalMotions_scaleExtensor`). -/
noncomputable def scaleExtensor (F : BodyHingeFramework K k α β) (c : β → K) :
    BodyHingeFramework K k α β where
  graph := F.graph
  supportExtensor e := c e • F.supportExtensor e

@[simp]
theorem scaleExtensor_graph (F : BodyHingeFramework K k α β) (c : β → K) :
    (F.scaleExtensor c).graph = F.graph := rfl

@[simp]
theorem scaleExtensor_supportExtensor (F : BodyHingeFramework K k α β) (c : β → K) (e : β) :
    (F.scaleExtensor c).supportExtensor e = c e • F.supportExtensor e := rfl

/-- **A nonzero rescaling leaves each hinge span unchanged** (a step of
`thm:projective-invariance`): `span {c e • C(p(e))} = span {C(p(e))}` when `c e ≠ 0`, since a
nonzero scalar is a unit (`Submodule.span_singleton_smul_eq`). -/
theorem span_singleton_scaleExtensor (F : BodyHingeFramework K k α β) {c : β → K}
    (hc : ∀ e, c e ≠ 0) (e : β) :
    Submodule.span K {(F.scaleExtensor c).supportExtensor e}
      = Submodule.span K {F.supportExtensor e} := by
  rw [scaleExtensor_supportExtensor]
  exact Submodule.span_singleton_smul_eq (hc e).isUnit _

/-- **Multiplying the supporting extensors by nonzero scalars preserves the motion space**
(`thm:projective-invariance`, the third statement): if every `c e ≠ 0` then
`Z(F.scaleExtensor c) = Z(F)`. Only the hinge spans enter the constraint, and they are unchanged
(`span_singleton_scaleExtensor`), so the motion spaces are equal, and so are their dimensions, the
rank hypothesis and rigidity. -/
theorem infinitesimalMotions_scaleExtensor (F : BodyHingeFramework K k α β) {c : β → K}
    (hc : ∀ e, c e ≠ 0) :
    (F.scaleExtensor c).infinitesimalMotions = F.infinitesimalMotions :=
  le_antisymm
    (F.infinitesimalMotions_mono_of_span_le (F.scaleExtensor c) rfl
      fun e => (F.span_singleton_scaleExtensor hc e).le)
    ((F.scaleExtensor c).infinitesimalMotions_mono_of_span_le F rfl
      fun e => (F.span_singleton_scaleExtensor hc e).ge)

end BodyHingeFramework

end CombinatorialRigidity.Molecular
