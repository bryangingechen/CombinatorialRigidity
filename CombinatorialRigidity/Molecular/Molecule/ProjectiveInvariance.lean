/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.AlgebraicInduction.Pinning

/-!
# Projective invariance of infinitesimal rigidity (extensor transport)

Phase 25 (`sec:molecule-modelling`, `thm:projective-invariance`). Crapo–Whiteley 1982 §3.6:
a projective transformation of `ℝ³` — a collineation or a correlation (polarity) — is a
non-singular linear map on the projective coordinates, and it induces an invertible linear
map `Λ` on the screw space `⋀² ℝ⁴ = ScrewSpace ℝ 2` that carries a panel structure to a panel
structure by transforming the hinges, sending instantaneous motions to instantaneous motions.
Since a body-hinge framework is read entirely through the *spans* of its supporting extensors
(the hinge constraint `S u − S v ∈ span {C(p(e))}`, `hingeConstraint`), that argument is a
pure **transport lemma**: transporting `(G, p)` along an invertible `Λ` — keeping the graph and
replacing each supporting extensor `C(p(e))` by `Λ C(p(e))` — carries the motion space
`Z(G,p)` isomorphically to its image under the bodywise map `S ↦ Λ ∘ S`, so the motion-space
dimension, the realized rank, and infinitesimal rigidity are all unchanged. No analytic
projective geometry is needed; the statement is dimension-general.

The correlation (polarity) case is the one the molecule modelling equivalence consumes: the
landed panel layer already factors the projective polarity through the meet-complement
isomorphism (`PanelHingeFramework.panelSupportExtensor = complementIso ∘ normalsJoin`), a fixed
linear equivalence of `⋀² ℝ⁴`, so `lem:panel-hinge-dual-molecular` is this transport at
`Λ := complementIso` with no new duality machinery.

A second, small sibling (`scaleExtensor`): the motion space is likewise unchanged under a
per-edge *nonzero rescaling* of the supporting extensors, since only the spans enter the hinge
constraint. This is the normalization from homogeneous (projective) to affine data.

See `notes/Phase25.md`, `notes/Phase25-design.md` §1.2/§3 (leaf W2), and
`blueprint/src/chapter/molecule-modelling.tex` (`thm:projective-invariance`).

## Main definitions

* `BodyHingeFramework.mapExtensor F Λ` — transport `F` along a linear automorphism `Λ` of the
  screw space (the panel structure induced by a projective transformation / polarity).
* `BodyHingeFramework.scaleExtensor F c` — rescale each supporting extensor by `c e : ℝ`.

## Main results

* `BodyHingeFramework.infinitesimalMotions_mapExtensor` — `Z(mapExtensor F Λ)` is the image of
  `Z(F)` under the bodywise map `S ↦ Λ ∘ S`.
* `BodyHingeFramework.finrank_infinitesimalMotions_mapExtensor`,
  `BodyHingeFramework.rankHypothesis_mapExtensor` — the motion-space dimension and hence the
  realized rank (`RankHypothesis`) are preserved.
* `BodyHingeFramework.isInfinitesimallyRigid_mapExtensor`,
  `BodyHingeFramework.isInfinitesimallyRigidOn_mapExtensor` — infinitesimal rigidity transfers.
* `BodyHingeFramework.supportExtensor_mapExtensor_ne_zero` — hinges are genuine on one side iff
  on the other.
* `BodyHingeFramework.infinitesimalMotions_scaleExtensor` — per-edge nonzero rescaling leaves
  the motion space unchanged.
-/

namespace CombinatorialRigidity.Molecular

variable {k : ℕ}

namespace BodyHingeFramework

variable {α β : Type*}

/-! ## Transport along a screw-space automorphism (`thm:projective-invariance`) -/

/-- **Transport a body-hinge framework along a linear automorphism `Λ` of the screw space**
(`thm:projective-invariance`; Crapo–Whiteley 1982 §3.6): keep the multigraph and replace each
supporting extensor `C(p(e))` by `Λ C(p(e))`. This is the panel structure a projective
transformation (collineation) or correlation (polarity) of `ℝ³` induces via the linear map it
puts on the screw space `⋀² ℝ⁴`. -/
noncomputable def mapExtensor (F : BodyHingeFramework ℝ k α β)
    (Λ : ScrewSpace ℝ k ≃ₗ[ℝ] ScrewSpace ℝ k) :
    BodyHingeFramework ℝ k α β where
  graph := F.graph
  supportExtensor e := Λ (F.supportExtensor e)

@[simp]
theorem mapExtensor_graph (F : BodyHingeFramework ℝ k α β)
    (Λ : ScrewSpace ℝ k ≃ₗ[ℝ] ScrewSpace ℝ k) :
    (F.mapExtensor Λ).graph = F.graph := rfl

@[simp]
theorem mapExtensor_supportExtensor (F : BodyHingeFramework ℝ k α β)
    (Λ : ScrewSpace ℝ k ≃ₗ[ℝ] ScrewSpace ℝ k) (e : β) :
    (F.mapExtensor Λ).supportExtensor e = Λ (F.supportExtensor e) := rfl

/-- **An automorphism carries a one-dimensional span isomorphically** (`thm:projective-invariance`):
for a linear automorphism `Λ` of the screw space, `Λ w` lies in `span {Λ C}` iff `w` lies in
`span {C}`. Both spans are one-dimensional and `Λ` restricts to a bijection between them; this is
the algebraic core of the transport (the hinge constraint reads only these spans). -/
theorem apply_mem_span_singleton_apply (Λ : ScrewSpace ℝ k ≃ₗ[ℝ] ScrewSpace ℝ k)
    (C w : ScrewSpace ℝ k) :
    Λ w ∈ Submodule.span ℝ {Λ C} ↔ w ∈ Submodule.span ℝ {C} := by
  simp only [Submodule.mem_span_singleton]
  refine ⟨fun ⟨a, ha⟩ => ⟨a, Λ.injective ?_⟩, fun ⟨a, ha⟩ => ⟨a, ?_⟩⟩
  · rw [map_smul]; exact ha
  · rw [← ha, map_smul]

/-- **The hinge constraint transports along `Λ`** (`thm:projective-invariance`): a screw
assignment `S` meets the hinge constraint of `F` at `e = uv` iff the transported assignment
`Λ ∘ S` meets the hinge constraint of `F.mapExtensor Λ` there. Immediate from
`apply_mem_span_singleton_apply` applied to the relative screw `S u − S v`. -/
theorem hingeConstraint_mapExtensor (F : BodyHingeFramework ℝ k α β)
    (Λ : ScrewSpace ℝ k ≃ₗ[ℝ] ScrewSpace ℝ k) (S : α → ScrewSpace ℝ k) (e : β) (u v : α) :
    (F.mapExtensor Λ).hingeConstraint (fun w => Λ (S w)) e u v ↔ F.hingeConstraint S e u v := by
  simp only [hingeConstraint, mapExtensor_supportExtensor, ← map_sub]
  exact apply_mem_span_singleton_apply Λ (F.supportExtensor e) (S u - S v)

/-- **Infinitesimal motions transport along `Λ`** (`thm:projective-invariance`, pointwise form):
`S` is an infinitesimal motion of `F` iff `Λ ∘ S` is an infinitesimal motion of
`F.mapExtensor Λ`. The graph is unchanged and each hinge constraint transports
(`hingeConstraint_mapExtensor`). -/
theorem isInfinitesimalMotion_mapExtensor (F : BodyHingeFramework ℝ k α β)
    (Λ : ScrewSpace ℝ k ≃ₗ[ℝ] ScrewSpace ℝ k) (S : α → ScrewSpace ℝ k) :
    (F.mapExtensor Λ).IsInfinitesimalMotion (fun w => Λ (S w)) ↔ F.IsInfinitesimalMotion S := by
  constructor
  · intro h e u v he
    exact (F.hingeConstraint_mapExtensor Λ S e u v).mp (h e u v he)
  · intro h e u v he
    exact (F.hingeConstraint_mapExtensor Λ S e u v).mpr (h e u v he)

/-- **Infinitesimal motions transport along `Λ`, `T`-form** (`thm:projective-invariance`): a screw
assignment `T` is a motion of `F.mapExtensor Λ` iff its `Λ⁻¹`-pullback `Λ⁻¹ ∘ T` is a motion of
`F`. The convenient restatement of `isInfinitesimalMotion_mapExtensor` with the transported
assignment named directly, obtained by taking `S := Λ⁻¹ ∘ T` and `Λ (Λ⁻¹ (T w)) = T w`. -/
theorem isInfinitesimalMotion_mapExtensor' (F : BodyHingeFramework ℝ k α β)
    (Λ : ScrewSpace ℝ k ≃ₗ[ℝ] ScrewSpace ℝ k) (T : α → ScrewSpace ℝ k) :
    (F.mapExtensor Λ).IsInfinitesimalMotion T
      ↔ F.IsInfinitesimalMotion (fun w => Λ.symm (T w)) := by
  simpa only [LinearEquiv.apply_symm_apply]
    using F.isInfinitesimalMotion_mapExtensor Λ (fun w => Λ.symm (T w))

/-- **The motion space transports along `Λ`** (`thm:projective-invariance`, the main statement):
the infinitesimal-motion space `Z(F.mapExtensor Λ)` is the image of `Z(F)` under the bodywise
linear automorphism `S ↦ Λ ∘ S` (`LinearEquiv.piCongrRight`). This is Crapo–Whiteley's projective
invariance: transporting the panel structure along `Λ` carries motions to motions
isomorphically. -/
theorem infinitesimalMotions_mapExtensor (F : BodyHingeFramework ℝ k α β)
    (Λ : ScrewSpace ℝ k ≃ₗ[ℝ] ScrewSpace ℝ k) :
    (F.mapExtensor Λ).infinitesimalMotions
      = F.infinitesimalMotions.map
          (LinearEquiv.piCongrRight fun _ : α => Λ : (α → ScrewSpace ℝ k) →ₗ[ℝ] _) := by
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
theorem finrank_infinitesimalMotions_mapExtensor (F : BodyHingeFramework ℝ k α β)
    (Λ : ScrewSpace ℝ k ≃ₗ[ℝ] ScrewSpace ℝ k) :
    Module.finrank ℝ (F.mapExtensor Λ).infinitesimalMotions
      = Module.finrank ℝ F.infinitesimalMotions := by
  rw [infinitesimalMotions_mapExtensor]
  exact LinearEquiv.finrank_map_eq _ _

/-- **The realized-rank hypothesis transfers** (`thm:projective-invariance`, `def:rank-hypothesis`):
`F.mapExtensor Λ` realizes the target rank `dim Z = D + k'` iff `F` does, because transport
preserves the motion-space dimension (`finrank_infinitesimalMotions_mapExtensor`). -/
theorem rankHypothesis_mapExtensor (F : BodyHingeFramework ℝ k α β)
    (Λ : ScrewSpace ℝ k ≃ₗ[ℝ] ScrewSpace ℝ k) (k' : ℤ) :
    (F.mapExtensor Λ).RankHypothesis k' ↔ F.RankHypothesis k' := by
  rw [RankHypothesis, RankHypothesis, finrank_infinitesimalMotions_mapExtensor]

/-! ## Rigidity transfer -/

/-- **Triviality of a motion transports along `Λ`** (`thm:projective-invariance`): `Λ ∘ S` is a
trivial (rigid) motion iff `S` is, since `Λ` is injective. -/
theorem isTrivialMotion_map_iff (Λ : ScrewSpace ℝ k ≃ₗ[ℝ] ScrewSpace ℝ k) (S : α → ScrewSpace ℝ k) :
    IsTrivialMotion (fun w => Λ (S w)) ↔ IsTrivialMotion S :=
  ⟨fun h u v => Λ.injective (h u v), fun h u v => by dsimp only; rw [h u v]⟩

/-- **Infinitesimal rigidity transfers along `Λ`** (`thm:projective-invariance`): `F.mapExtensor Λ`
is infinitesimally rigid iff `F` is. Every motion of one framework is `Λ ∘ (·)` of a motion of the
other (`isInfinitesimalMotion_mapExtensor`), and triviality transports (`isTrivialMotion_map_iff`),
so "every motion is trivial" holds on one side iff on the other. -/
theorem isInfinitesimallyRigid_mapExtensor (F : BodyHingeFramework ℝ k α β)
    (Λ : ScrewSpace ℝ k ≃ₗ[ℝ] ScrewSpace ℝ k) :
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

/-- **Relative infinitesimal rigidity transfers along `Λ`** (`thm:projective-invariance`,
`def:rank-hypothesis`): `F.mapExtensor Λ` is infinitesimally rigid on a body set `s` iff `F` is.
Same argument as the absolute form, restricted to the pairs of bodies in `s`. -/
theorem isInfinitesimallyRigidOn_mapExtensor (F : BodyHingeFramework ℝ k α β)
    (Λ : ScrewSpace ℝ k ≃ₗ[ℝ] ScrewSpace ℝ k) (s : Set α) :
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

/-- **Genuine hinges transfer along `Λ`** (`thm:projective-invariance`): the supporting extensor
at `e` is nonzero (a genuine hinge) after transport iff it was before, since a linear equivalence
sends nonzero to nonzero. -/
theorem supportExtensor_mapExtensor_ne_zero (F : BodyHingeFramework ℝ k α β)
    (Λ : ScrewSpace ℝ k ≃ₗ[ℝ] ScrewSpace ℝ k) (e : β) :
    (F.mapExtensor Λ).supportExtensor e ≠ 0 ↔ F.supportExtensor e ≠ 0 := by
  rw [mapExtensor_supportExtensor, ne_eq, ne_eq, map_eq_zero_iff Λ Λ.injective]

/-! ## Per-edge nonzero rescaling (normalization from homogeneous to affine data) -/

/-- **Rescale each supporting extensor by a scalar** (`thm:projective-invariance`): keep the graph
and replace `C(p(e))` by `c e • C(p(e))`. When every `c e ≠ 0` this is the normalization from
homogeneous (projective) coordinates to affine data; it leaves every hinge span — hence the whole
motion space — unchanged (`infinitesimalMotions_scaleExtensor`). -/
noncomputable def scaleExtensor (F : BodyHingeFramework ℝ k α β) (c : β → ℝ) :
    BodyHingeFramework ℝ k α β where
  graph := F.graph
  supportExtensor e := c e • F.supportExtensor e

@[simp]
theorem scaleExtensor_graph (F : BodyHingeFramework ℝ k α β) (c : β → ℝ) :
    (F.scaleExtensor c).graph = F.graph := rfl

@[simp]
theorem scaleExtensor_supportExtensor (F : BodyHingeFramework ℝ k α β) (c : β → ℝ) (e : β) :
    (F.scaleExtensor c).supportExtensor e = c e • F.supportExtensor e := rfl

/-- **A nonzero rescaling leaves each hinge span unchanged** (`thm:projective-invariance`):
`span {c e • C(p(e))} = span {C(p(e))}` when `c e ≠ 0`, since a nonzero scalar is a unit
(`Submodule.span_singleton_smul_eq`). -/
theorem span_singleton_scaleExtensor (F : BodyHingeFramework ℝ k α β) {c : β → ℝ}
    (hc : ∀ e, c e ≠ 0) (e : β) :
    Submodule.span ℝ {(F.scaleExtensor c).supportExtensor e}
      = Submodule.span ℝ {F.supportExtensor e} := by
  rw [scaleExtensor_supportExtensor]
  exact Submodule.span_singleton_smul_eq (hc e).isUnit _

/-- **Per-edge nonzero rescaling preserves the motion space** (`thm:projective-invariance`, the
rescaling sibling): if every `c e ≠ 0` then `Z(F.scaleExtensor c) = Z(F)`. Only the hinge spans
enter the constraint, and they are unchanged (`span_singleton_scaleExtensor`), so the motion
spaces are literally equal — hence so are the dimension, realized rank, and rigidity. -/
theorem infinitesimalMotions_scaleExtensor (F : BodyHingeFramework ℝ k α β) {c : β → ℝ}
    (hc : ∀ e, c e ≠ 0) :
    (F.scaleExtensor c).infinitesimalMotions = F.infinitesimalMotions :=
  le_antisymm
    (F.infinitesimalMotions_mono_of_span_le (F.scaleExtensor c) rfl
      fun e => (F.span_singleton_scaleExtensor hc e).le)
    ((F.scaleExtensor c).infinitesimalMotions_mono_of_span_le F rfl
      fun e => (F.span_singleton_scaleExtensor hc e).ge)

end BodyHingeFramework

end CombinatorialRigidity.Molecular
