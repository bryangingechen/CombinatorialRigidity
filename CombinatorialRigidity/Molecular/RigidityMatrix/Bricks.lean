/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.RigidityMatrix.Basic

/-!
# Body-hinge block-rank addition bricks (`sec:molecular-rigidity-matrix`)

The three rank-addition *bricks* of the panel-hinge rigidity matrix, carved out of the tail of
`RigidityMatrix.lean` (Phase 18) into this leaf for file size / navigability (the post-Phase-22
molecular split round; `notes/PERFORMANCE.md`). Each is a lower bound on the rigidity-row span
dimension of a structurally-decomposed body-hinge framework — the building blocks of KT's
Lemma 6.1 block-triangular rank-addition argument (Katoh–Tanigawa 2011 §6.1):

* `le_finrank_span_rigidityRows_of_cut` (`section CutEdgeBrick`) — the vertex-disjoint
  cut-partition brick.
* `le_finrank_span_rigidityRows_of_splice` (`section SpliceBrick`) — the shared-vertex splice
  brick.
* `le_finrank_span_rigidityRows_of_pinned_placement{,_augment}` (`section
  PinnedPlacementBrick`) — the pinned-placement brick.

The file also carries the **vertex 2-cut layer** (`section TwoCutCarriers`, Phase 39 item 6,
Layer B): the carriers `relScrews` (`ρ̄_{uv}`), `jointRows`, `jointMotions` (`M_U`) and
`weldedRank` of the cut-pair rank laws, with the joint's row count `finrank_span_jointRows`, the
welded-rank identity `weldedRank_eq` (`rank_w = rank + ρ`), the welded codimension
`weldedRank_add_finrank_jointMotions_bot` (`rank_w + dim M_⊥ = screwDim k·|α|`), the gluing
identity at a 2-cut `finrank_span_rigidityRows_twoCut_eq_of_isLink` (Phase 40g; at induced sides
`finrank_span_rigidityRows_vertexTwoCut_eq`), and its cut-vertex case
`finrank_span_rigidityRows_cutVertex_eq` (Phase 40e: the ranks simply add).
Its own section header is their index; these are the objects the Layer-C losses in
`Molecule/Pencil/TwoCut.lean` are stated in.

These depend only on the core `BodyHingeFramework` API in `RigidityMatrix.lean`; nothing in the
core depends on them (they were the file's tail), so this is a clean forward-dependency leaf.
This split is rename-free — every declaration keeps its `CombinatorialRigidity.Molecular`
namespace, so the blueprint `\lean{…}` pins and `checkdecls` are unaffected.
-/

public section

namespace CombinatorialRigidity.Molecular

open scoped Matrix

variable {K : Type*} [Field K]

namespace BodyHingeFramework

variable {k : ℕ} {α β : Type*}

/-! ## Vertex-disjoint block-rank addition (the cut-edge brick)

The block-rank inequality for a cut-partitioned body-hinge framework: when the edge set
decomposes into two side groups (each internal to one of two disjoint vertex sets `V₁` and
`V(G) ∖ V₁`) and at most one crossing edge, the rigidity-row span has dimension at least
the sum of the two side-spans plus the cut block's dimension.  This is the core of KT's
Lemma 6.1 block-triangular rank-addition argument (Katoh–Tanigawa 2011 §6.1, p. 672).

The proof key: the V₁- and V₂-side spans read disjoint coordinate blocks of the screw
assignment, making them mutually disjoint submodules; the cut-block span is disjoint from
their join via the flow-sum functional (summing `φ(update 0 w x)` over `w ∈ V₁` annihilates
both side spans but returns the cut-block functional, so an element in the intersection must
be zero). -/

section CutEdgeBrick

-- `open Classical` is needed for `Decidable (a ∈ V₁)` in `zeroOutsideV₁`'s if/else and
-- for `DecidableEq α` in `flowSum`'s `Pi.single`. The linter is disabled for this command.
set_option linter.style.openClassical false
open Classical
open scoped Graph

variable {α β : Type*} {k : ℕ}

/-- **The V₁-projection map**: zeroes the screw assignment outside `V₁`.  Used to separate
the V₁-side span from the V₂-side span: side-1 rows commute with the projection (they read
only V₁ bodies), side-2 rows vanish under it (they read only V₂ bodies). -/
private noncomputable def zeroOutsideV₁ (V₁ : Set α) :
    (α → ScrewSpace K k) →ₗ[K] (α → ScrewSpace K k) where
  toFun S a := if a ∈ V₁ then S a else 0
  map_add' S T := by ext a; simp [ite_add_ite]
  map_smul' c S := by ext a; simp [smul_ite]

@[simp]
private lemma zeroOutsideV₁_mem (V₁ : Set α) (S : α → ScrewSpace K k) {a : α} (ha : a ∈ V₁) :
    zeroOutsideV₁ V₁ S a = S a := ite_eq_left ha

@[simp]
private lemma zeroOutsideV₁_not_mem (V₁ : Set α) (S : α → ScrewSpace K k) {a : α} (ha : a ∉ V₁) :
    zeroOutsideV₁ V₁ S a = 0 := ite_eq_right ha

/-- A hinge row with both endpoints in `V₁` commutes with the V₁-projection: the row value
is unchanged when the screw assignment is zeroed outside `V₁`. -/
private lemma hingeRow_comp_zeroOutsideV₁ (V₁ : Set α) {u v : α} (hu : u ∈ V₁) (hv : v ∈ V₁)
    (r : Module.Dual K (ScrewSpace K k)) :
    (hingeRow (k := k) (α := α) u v r).comp (zeroOutsideV₁ V₁) = hingeRow u v r := by
  ext S
  simp [hingeRow_apply, zeroOutsideV₁_mem V₁ S hu, zeroOutsideV₁_mem V₁ S hv]

/-- A hinge row with both endpoints outside `V₁` vanishes at any V₁-projection output. -/
private lemma hingeRow_comp_zeroOutsideV₁_of_not_mem (V₁ : Set α) {u v : α}
    (hu : u ∉ V₁) (hv : v ∉ V₁) (r : Module.Dual K (ScrewSpace K k)) :
    (hingeRow (k := k) (α := α) u v r).comp (zeroOutsideV₁ V₁) = 0 := by
  ext S
  simp [hingeRow_apply, zeroOutsideV₁_not_mem V₁ S hu, zeroOutsideV₁_not_mem V₁ S hv]

/-- Every element of the V₁-side rigidity-row span commutes with the V₁-projection: for
`φ ∈ span(F[V₁].rigidityRows)`, `φ(zeroOutsideV₁ S) = φ(S)` for all `S`. -/
private lemma mem_span_rigidityRows_induce_comp_zeroOutsideV₁ {F : BodyHingeFramework K k α β}
    {V₁ : Set α} {φ : Module.Dual K (α → ScrewSpace K k)}
    (hφ : φ ∈ Submodule.span K (⟨F.graph.induce V₁, F.supportExtensor⟩ :
      BodyHingeFramework K k α β).rigidityRows) :
    φ.comp (zeroOutsideV₁ V₁) = φ := by
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨e, u, v, he, r, _, rfl⟩ := hφ
    simp only [Graph.induce_isLink] at he
    exact hingeRow_comp_zeroOutsideV₁ V₁ he.2.1 he.2.2 r
  | zero => ext; simp
  | add x y _ _ hx hy =>
    rw [LinearMap.add_comp, hx, hy]
  | smul a x _ hx =>
    rw [LinearMap.smul_comp, hx]

/-- Every element of the V₂-side rigidity-row span vanishes when composed with the
V₁-projection: for `φ ∈ span(F[V₂].rigidityRows)`, `φ ∘ zeroOutsideV₁ = 0`. -/
private lemma mem_span_rigidityRows_induce_comp_zeroOutsideV₁_eq_zero
    {F : BodyHingeFramework K k α β} {V₁ : Set α} {φ : Module.Dual K (α → ScrewSpace K k)}
    (hφ : φ ∈ Submodule.span K (⟨F.graph.induce (V(F.graph) \ V₁), F.supportExtensor⟩ :
      BodyHingeFramework K k α β).rigidityRows) :
    φ.comp (zeroOutsideV₁ V₁) = 0 := by
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨e, u, v, he, r, _, rfl⟩ := hφ
    simp only [Graph.induce_isLink, Set.mem_sdiff] at he
    exact hingeRow_comp_zeroOutsideV₁_of_not_mem V₁ he.2.1.2 he.2.2.2 r
  | zero => ext; simp
  | add x y _ _ hx hy =>
    simp only [LinearMap.add_comp, hx, hy, add_zero]
  | smul a x _ hx =>
    rw [LinearMap.smul_comp, hx, smul_zero]

/-- **The two side spans are disjoint**: `span(F[V₁].rigidityRows) ⊓ span(F[V₂].rigidityRows) = ⊥`.
The V₁-projection commutes with span(F[V₁]) (side-1 rows read only V₁) and annihilates
span(F[V₂]) (side-2 rows read only V₂ = V(G) ∖ V₁); any element in the intersection is both
fixed by and annihilated by the projection, hence zero. -/
theorem span_rigidityRows_induce_inf_eq_bot {F : BodyHingeFramework K k α β} (V₁ : Set α) :
    Submodule.span K (⟨F.graph.induce V₁, F.supportExtensor⟩ :
        BodyHingeFramework K k α β).rigidityRows ⊓
    Submodule.span K (⟨F.graph.induce (V(F.graph) \ V₁), F.supportExtensor⟩ :
        BodyHingeFramework K k α β).rigidityRows = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro φ ⟨h1, h2⟩
  -- From h1: φ = φ.comp (zeroOutsideV₁ V₁) (V₁-side rows commute with projection)
  have hfix : φ.comp (zeroOutsideV₁ V₁) = φ :=
    mem_span_rigidityRows_induce_comp_zeroOutsideV₁ h1
  -- From h2: φ.comp (zeroOutsideV₁ V₁) = 0 (V₂-side rows vanish under projection)
  have hzero : φ.comp (zeroOutsideV₁ V₁) = 0 :=
    mem_span_rigidityRows_induce_comp_zeroOutsideV₁_eq_zero h2
  exact hfix.symm.trans hzero

/-- The flow-sum linear map `Φ(φ) = ∑_{w ∈ V₁} φ(update 0 w ·)`: a functional from
`Module.Dual K (α → ScrewSpace K k)` to `Module.Dual K (ScrewSpace K k)`. Used to separate
the cut-block span from the join of the two side spans: S₁ and S₂ rows give `Φ = 0` (flow
sums cancel / V₂-bodies vanish), but a cut row `hingeRow u v r` with `u ∈ V₁, v ∉ V₁`
gives `Φ = r`. -/
private noncomputable def flowSum [Fintype α] (V₁ : Set α) :
    Module.Dual K (α → ScrewSpace K k) →ₗ[K] Module.Dual K (ScrewSpace K k) where
  toFun φ := ∑ w ∈ V₁.toFinset, φ.comp (LinearMap.single K (fun _ : α => ScrewSpace K k) w)
  map_add' φ ψ := by
    simp [Finset.sum_add_distrib, LinearMap.add_comp]
  map_smul' c φ := by
    simp [Finset.smul_sum, LinearMap.smul_comp]

private lemma flowSum_hingeRow_both_mem [Fintype α] {V₁ : Set α}
    {u v : α} (hu : u ∈ V₁) (hv : v ∈ V₁)
    (r : Module.Dual K (ScrewSpace K k)) :
    flowSum V₁ (hingeRow (k := k) (α := α) u v r) = 0 := by
  -- Use LinearMap.ext to avoid the ext-on-exterior-power trap (TACTICS-QUIRKS §32).
  -- The sum telescopes: ∑_{w ∈ V₁} r((single_w y) u) - r((single_w y) v)
  --   = r y - r y = 0, since only the w=u (resp. w=v) term contributes.
  apply LinearMap.ext; intro y
  simp only [flowSum, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply,
    LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.comp_apply, LinearMap.coe_single, hingeRow_apply, map_sub]
  rw [Finset.sum_sub_distrib]
  -- ∑_{w ∈ V₁.toFinset} r ((single w y) u) = r y (only w=u contributes)
  have hsu : ∑ w ∈ V₁.toFinset, r ((Pi.single w y : α → ScrewSpace K k) u) = r y := by
    rw [Finset.sum_eq_single u
      (fun w _ hwu => by simp [Pi.single_eq_of_ne (Ne.symm hwu)])
      (fun hu' => absurd (Set.mem_toFinset.mpr hu) hu')]
    simp [Pi.single_eq_same]
  -- ∑_{w ∈ V₁.toFinset} r ((single w y) v) = r y (only w=v contributes)
  have hsv : ∑ w ∈ V₁.toFinset, r ((Pi.single w y : α → ScrewSpace K k) v) = r y := by
    rw [Finset.sum_eq_single v
      (fun w _ hwv => by simp [Pi.single_eq_of_ne (Ne.symm hwv)])
      (fun hv' => absurd (Set.mem_toFinset.mpr hv) hv')]
    simp [Pi.single_eq_same]
  rw [hsu, hsv, sub_self]

private lemma flowSum_hingeRow_both_not_mem [Fintype α] {V₁ : Set α}
    {u v : α} (hu : u ∉ V₁) (hv : v ∉ V₁) (r : Module.Dual K (ScrewSpace K k)) :
    flowSum V₁ (hingeRow (k := k) (α := α) u v r) = 0 := by
  apply LinearMap.ext; intro y
  simp only [flowSum, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply,
    LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.comp_apply, LinearMap.coe_single, hingeRow_apply]
  refine Finset.sum_eq_zero (fun w hw => ?_)
  rw [Pi.single_eq_of_ne (show u ≠ w from fun (h : u = w) => hu (h ▸ Set.mem_toFinset.mp hw)),
      Pi.single_eq_of_ne (show v ≠ w from fun (h : v = w) => hv (h ▸ Set.mem_toFinset.mp hw))]
  simp

private lemma flowSum_hingeRow_mem_not_mem [Fintype α] {V₁ : Set α}
    {u v : α} (hu : u ∈ V₁) (hv : v ∉ V₁) (r : Module.Dual K (ScrewSpace K k)) :
    flowSum V₁ (hingeRow (k := k) (α := α) u v r) = r := by
  simp only [flowSum, LinearMap.coe_mk, AddHom.coe_mk]
  -- The sum over V₁.toFinset collapses to the w = u term (all other terms are 0):
  -- • w = u: (single u x) u = x, (single u x) v = 0 (since v ≠ u, as v ∉ V₁, u ∈ V₁)
  --   → hingeRow u v r applied to (single u x) = r (x - 0) = r x.
  -- • w ≠ u, w ∈ V₁: (single w x) u = 0, (single w x) v = 0 (v ∉ V₁ so w ≠ v)
  --   → r (0 - 0) = 0.
  rw [Finset.sum_eq_single (f := fun w => (hingeRow (k := k) (α := α) u v r).comp
        (LinearMap.single K (fun _ : α => ScrewSpace K k) w))
      u
      (fun w hw hwu => ?_)
      (fun hu' => absurd (Set.mem_toFinset.mpr hu) hu')]
  · -- w = u term: r
    apply LinearMap.ext; intro x
    simp only [LinearMap.comp_apply, LinearMap.coe_single, Pi.single, hingeRow_apply]
    rw [Function.update_self,
        Function.update_of_ne (fun (h : v = u) => hv (h ▸ hu))]
    simp
  · -- w ≠ u, w ∈ V₁.toFinset: term = 0
    apply LinearMap.ext; intro x
    simp only [LinearMap.comp_apply, LinearMap.coe_single, Pi.single, hingeRow_apply,
               LinearMap.zero_apply]
    rw [Function.update_of_ne (Ne.symm hwu),
        Function.update_of_ne (fun (h : v = w) => hv (h ▸ Set.mem_toFinset.mp hw))]
    simp

/-- The flow sum annihilates every element of the V₁-side span: for
`φ ∈ span(F[V₁].rigidityRows)`, `Φ(φ) = 0`. -/
private lemma flowSum_mem_span_induce_V₁_eq_zero [Fintype α]
    {F : BodyHingeFramework K k α β} {V₁ : Set α}
    {φ : Module.Dual K (α → ScrewSpace K k)}
    (hφ : φ ∈ Submodule.span K (⟨F.graph.induce V₁, F.supportExtensor⟩ :
      BodyHingeFramework K k α β).rigidityRows) :
    flowSum V₁ φ = 0 := by
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨e, u, v, he, r, _, rfl⟩ := hφ
    simp only [Graph.induce_isLink] at he
    exact flowSum_hingeRow_both_mem he.2.1 he.2.2 r
  | zero => simp only [map_zero]
  | add x y _ _ hx hy =>
    simp only [map_add, hx, hy, add_zero]
  | smul a x _ hx =>
    rw [map_smul, hx, smul_zero]

/-- The flow sum annihilates every element of the V₂-side span. -/
private lemma flowSum_mem_span_induce_V₂_eq_zero [Fintype α]
    {F : BodyHingeFramework K k α β} {V₁ : Set α}
    {φ : Module.Dual K (α → ScrewSpace K k)}
    (hφ : φ ∈ Submodule.span K (⟨F.graph.induce (V(F.graph) \ V₁), F.supportExtensor⟩ :
      BodyHingeFramework K k α β).rigidityRows) :
    flowSum V₁ φ = 0 := by
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨e, u, v, he, r, _, rfl⟩ := hφ
    simp only [Graph.induce_isLink, Set.mem_sdiff] at he
    exact flowSum_hingeRow_both_not_mem he.2.1.2 he.2.2.2 r
  | zero => simp only [map_zero]
  | add x y _ _ hx hy =>
    simp only [map_add, hx, hy, add_zero]
  | smul a x _ hx =>
    rw [map_smul, hx, smul_zero]

/-- **Vertex-disjoint block-rank addition** (`lem:rigidityRows-cut-rank-add`; KT Lemma 6.1
block-triangular core; Phase 22i L4a). For a body-hinge framework `F` whose link set
partitions over a cut `V₁ ⊂ V(F.graph)` with at most one crossing edge, the rigidity-row
span's dimension is at least the sum of the two side-spans plus `(D−1)·|cut|`. This is
Katoh–Tanigawa 2011 §6.1 Lemma 6.1's block-triangular rank-addition, the row-rank lower
bound underlying the not-2-edge-connected induction case.

Proof: the two side-spans are disjoint (V₁/V₂ projection argument), the cut block is
disjoint from their join (flow-sum argument). The three pieces jointly embed into the full
span, giving the rank lower bound by `Submodule.finrank_sup_of_inf_eq_bot` (disjoint sups). -/
-- `unusedArguments` FALSE POSITIVE: the `Fintype.ofFinite` bridge in the proof body
-- needs this instance to elaborate; it does not survive into the proof term.
@[nolint unusedArguments]
theorem le_finrank_span_rigidityRows_of_cut [Finite α] [Finite β]
    (F : BodyHingeFramework K k α β) {V₁ : Set α} {C : Set β}
    (hC_ncard : C.ncard ≤ 1)
    (hC_ext : ∀ e u v, F.graph.IsLink e u v → F.supportExtensor e ≠ 0)
    (_hE₁ : ∀ e u v, F.graph.IsLink e u v → e ∉ C →
      u ∈ V₁ ∧ v ∈ V₁ ∨ u ∉ V₁ ∧ v ∉ V₁)
    (hcut_mem : ∀ e ∈ C, ∃ u v, F.graph.IsLink e u v ∧ u ∈ V₁ ∧ v ∉ V₁) :
    Module.finrank K (Submodule.span K
        (⟨F.graph.induce V₁, F.supportExtensor⟩ : BodyHingeFramework K k α β).rigidityRows) +
      (screwDim k - 1) * C.ncard +
      Module.finrank K (Submodule.span K
        (⟨F.graph.induce (V(F.graph) \ V₁), F.supportExtensor⟩ :
          BodyHingeFramework K k α β).rigidityRows) ≤
    Module.finrank K (Submodule.span K F.rigidityRows) := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have : Fintype β := Fintype.ofFinite β
  set F₁ : BodyHingeFramework K k α β := ⟨F.graph.induce V₁, F.supportExtensor⟩
  set F₂ : BodyHingeFramework K k α β := ⟨F.graph.induce (V(F.graph) \ V₁), F.supportExtensor⟩
  set S₁ := Submodule.span K F₁.rigidityRows
  set S₂ := Submodule.span K F₂.rigidityRows
  set S := Submodule.span K F.rigidityRows
  -- Step 0: The cut-block span Sc and its dimension.
  -- When |C| = 0, the cut block contributes 0. When |C| = 1, it contributes D−1.
  rcases Nat.eq_zero_or_pos C.ncard with hzero | hpos
  · -- Disconnected case: |C| = 0. The sum is finrank(S₁) + 0 + finrank(S₂).
    simp only [hzero, Nat.mul_zero, add_zero]
    -- S₁ ≤ S and S₂ ≤ S.
    have hS₁S : S₁ ≤ S := by
      apply Submodule.span_le.mpr
      rintro φ ⟨e, u, v, he, r, hr, rfl⟩
      simp only [F₁, Graph.induce_isLink] at he
      exact Submodule.subset_span ⟨e, u, v, he.1, r, hr, rfl⟩
    have hS₂S : S₂ ≤ S := by
      apply Submodule.span_le.mpr
      rintro φ ⟨e, u, v, he, r, hr, rfl⟩
      simp only [F₂, Graph.induce_isLink] at he
      exact Submodule.subset_span ⟨e, u, v, he.1, r, hr, rfl⟩
    have hdisj : S₁ ⊓ S₂ = ⊥ := span_rigidityRows_induce_inf_eq_bot V₁
    have hstep := Submodule.finrank_sup_of_inf_eq_bot S₁ S₂ hdisj
    calc Module.finrank K ↥S₁ + Module.finrank K ↥S₂
        = Module.finrank K ↥(S₁ ⊔ S₂) := hstep.symm
      _ ≤ Module.finrank K ↥S := Submodule.finrank_mono (sup_le hS₁S hS₂S)
  · -- Connected case: |C| = 1. The cut block contributes screwDim k - 1.
    -- Get the unique cut edge and its endpoint data.
    have hcut_eq : C.ncard = 1 := Nat.le_antisymm hC_ncard hpos
    -- The cut block: span of hingeRows at the cut edge.
    obtain ⟨e_cut, he_cut_eq⟩ := Set.ncard_eq_one.mp hcut_eq
    obtain ⟨u₀, v₀, hl_cut, hu₀, hv₀⟩ := hcut_mem e_cut (he_cut_eq ▸ Set.mem_singleton e_cut)
    have huv₀ : u₀ ≠ v₀ := fun h => hv₀ (h ▸ hu₀)
    -- The cut hinge rows span a (D-1)-dimensional subspace.
    set Sc := Submodule.span K {φ | ∃ r ∈ F.hingeRowBlock e_cut,
      φ = hingeRow (k := k) (α := α) u₀ v₀ r}
    -- finrank(Sc) = screwDim k - 1.
    have hCcut : F.supportExtensor e_cut ≠ 0 := hC_ext e_cut u₀ v₀ hl_cut
    have hSc_rk : Module.finrank K Sc = screwDim k - 1 := by
      have hfin := finrank_hingeRowBlock F hCcut
      -- Sc = image of hingeRow u₀ v₀ (·) applied to hingeRowBlock e_cut
      have heq : Sc = (F.hingeRowBlock e_cut).map
          ((screwDiff (k := k) (α := α) u₀ v₀).dualMap) := by
        simp only [Sc, hingeRow_eq_dualMap]
        -- {φ | ∃ r ∈ hingeRowBlock, φ = dualMap r} = dualMap '' ↑hingeRowBlock
        -- then span (dualMap '' hingeRowBlock) = (span hingeRowBlock).map dualMap
        -- = hingeRowBlock.map dualMap
        have hset : {φ : Module.Dual K (α → ScrewSpace K k) | ∃ r ∈ F.hingeRowBlock e_cut,
            φ = (screwDiff u₀ v₀).dualMap r} =
            (screwDiff (k := k) (α := α) u₀ v₀).dualMap '' ↑(F.hingeRowBlock e_cut) := by
          ext ψ
          simp only [Set.mem_ofPred_eq, Set.mem_image]
          exact ⟨fun ⟨r, hr, h⟩ => ⟨r, hr, h.symm⟩,
                 fun ⟨r, hr, h⟩ => ⟨r, hr, h.symm⟩⟩
        rw [hset, Submodule.span_image, Submodule.span_eq]
      have hinj : Function.Injective (screwDiff (K := K) (k := k) (α := α) u₀ v₀).dualMap :=
        LinearMap.dualMap_injective_of_surjective (screwDiff_surjective (K := K) huv₀)
      -- finrank(Sc) = finrank(image of injective map) = finrank(hingeRowBlock) = D-1
      have hinj_comp : Function.Injective
          ⇑((screwDiff (k := k) (α := α) u₀ v₀).dualMap.comp (F.hingeRowBlock e_cut).subtype) :=
        hinj.comp Subtype.coe_injective
      have hrk : Module.finrank K ↥((F.hingeRowBlock e_cut).map
            (screwDiff (k := k) (α := α) u₀ v₀).dualMap) = screwDim k - 1 := by
        rw [show (F.hingeRowBlock e_cut).map (screwDiff u₀ v₀).dualMap =
              ((screwDiff u₀ v₀).dualMap.comp (F.hingeRowBlock e_cut).subtype).range from
            by rw [LinearMap.range_comp, Submodule.range_subtype],
            LinearMap.finrank_range_of_inj hinj_comp, hfin]
      rw [heq, hrk]
    -- Sc ⊆ S
    have hScS : Sc ≤ S := by
      apply Submodule.span_le.mpr
      rintro φ ⟨r, hr, rfl⟩
      exact Submodule.subset_span ⟨e_cut, u₀, v₀, hl_cut, r, hr, rfl⟩
    -- S₁ ≤ S and S₂ ≤ S.
    have hS₁S : S₁ ≤ S := by
      apply Submodule.span_le.mpr
      rintro φ ⟨e, u, v, he, r, hr, rfl⟩
      simp only [F₁, Graph.induce_isLink] at he
      exact Submodule.subset_span ⟨e, u, v, he.1, r, hr, rfl⟩
    have hS₂S : S₂ ≤ S := by
      apply Submodule.span_le.mpr
      rintro φ ⟨e, u, v, he, r, hr, rfl⟩
      simp only [F₂, Graph.induce_isLink] at he
      exact Submodule.subset_span ⟨e, u, v, he.1, r, hr, rfl⟩
    -- S₁ ⊓ S₂ = ⊥.
    have hdisj12 : S₁ ⊓ S₂ = ⊥ := span_rigidityRows_induce_inf_eq_bot V₁
    -- Sc ⊓ (S₁ ⊔ S₂) = ⊥: flow-sum argument.
    -- Key: for φ ∈ Sc, flowSum V₁ extracts the block functional; for φ ∈ S₁⊔S₂, flowSum = 0.
    -- Hence any element of the intersection has flowSum = 0 AND equal to the block functional
    -- of its Sc-representation, forcing the block functional to be 0, hence φ = 0.
    --
    -- We realize Sc as the image of the injective map `hingeRow u₀ v₀` from hingeRowBlock.
    -- The flow sum is the left inverse: flowSum V₁ ∘ hingeRow u₀ v₀ = id on the block.
    -- So from φ ∈ Sc with flowSum V₁ φ = 0, we get φ = hingeRow u₀ v₀ (flowSum V₁ φ) = 0.
    -- Key identity: for any φ ∈ Sc, φ = hingeRow u₀ v₀ (flowSum V₁ φ).
    -- The flow sum is a left inverse of hingeRow u₀ v₀ on the Sc generators.
    have hkey_id : ∀ φ ∈ Sc, φ = hingeRow (k := k) (α := α) u₀ v₀ (flowSum V₁ φ) := by
      intro φ hφSc
      induction hφSc using Submodule.span_induction with
      | mem φ hφ =>
        obtain ⟨r, _, rfl⟩ := hφ
        rw [flowSum_hingeRow_mem_not_mem hu₀ hv₀ r]
      | zero =>
        simp only [map_zero, hingeRow_eq_dualMap, map_zero]
      | add x y _ _ hx hy =>
        -- goal: x + y = hingeRow u₀ v₀ (flowSum V₁ (x + y))
        -- hx : x = hingeRow u₀ v₀ (flowSum V₁ x)
        -- hy : y = hingeRow u₀ v₀ (flowSum V₁ y)
        conv_rhs =>
          rw [map_add, hingeRow_eq_dualMap, map_add, ← hingeRow_eq_dualMap, ← hingeRow_eq_dualMap]
        rw [← hx, ← hy]
      | smul a x _ hx =>
        -- goal: a • x = hingeRow u₀ v₀ (flowSum V₁ (a • x))
        conv_rhs =>
          rw [map_smul, hingeRow_eq_dualMap, map_smul, ← hingeRow_eq_dualMap]
        rw [← hx]
    have hdisjc12 : Sc ⊓ (S₁ ⊔ S₂) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro φ ⟨hφSc, hφS12⟩
      -- From S₁⊔S₂: flowSum V₁ φ = 0.
      have hflow0 : flowSum V₁ φ = 0 := by
        obtain ⟨φ₁, hφ₁, φ₂, hφ₂, rfl⟩ := Submodule.mem_sup.mp hφS12
        simp only [map_add, flowSum_mem_span_induce_V₁_eq_zero hφ₁,
          flowSum_mem_span_induce_V₂_eq_zero hφ₂, add_zero]
      -- From the key identity: φ = hingeRow u₀ v₀ (flowSum V₁ φ) = hingeRow u₀ v₀ 0 = 0.
      rw [hkey_id φ hφSc, hflow0]
      simp [hingeRow_eq_dualMap, map_zero]
    -- Combine: finrank(S₁) + (D-1) + finrank(S₂) ≤ finrank(S).
    have step1 : Module.finrank K ↥(S₁ ⊔ S₂) = Module.finrank K ↥S₁ + Module.finrank K ↥S₂ :=
      Submodule.finrank_sup_of_inf_eq_bot S₁ S₂ hdisj12
    have step2 : Module.finrank K ↥(Sc ⊔ (S₁ ⊔ S₂)) =
        Module.finrank K ↥Sc + Module.finrank K ↥(S₁ ⊔ S₂) :=
      Submodule.finrank_sup_of_inf_eq_bot Sc (S₁ ⊔ S₂) hdisjc12
    rw [hcut_eq, Nat.mul_one]
    calc Module.finrank K ↥S₁ + (screwDim k - 1) + Module.finrank K ↥S₂
        = (screwDim k - 1) + Module.finrank K ↥(S₁ ⊔ S₂) := by rw [step1]; ring
      _ = Module.finrank K ↥(Sc ⊔ (S₁ ⊔ S₂)) := by rw [step2, hSc_rk]
      _ ≤ Module.finrank K ↥S := Submodule.finrank_mono
          (sup_le hScS (sup_le hS₁S hS₂S))

/-- **Single-edge row-drop bound** (`sec:pencil-reduction` rank infra; Phase 39 W5-L5 L5-cut-i,
the cut-arm route verdict's new brick — `notes/Phase39-design.md` §"W5 leaf decomposition" L5).
When every link of `G'` is either a link of the smaller graph `Gs` or the single extra edge `e₀`
(same supporting extensor on both sides), dropping `e₀`'s rows costs at most its block dimension:
`finrank (span rows(G')) ≤ finrank (span rows(Gs)) + (screwDim k − 1)`.

This converts the cut-arm IH rank at the edge-closed side `Gᵢ⁺ = G.induce (Vᵢ ∪ {far})`
(`Gs := G.induce Vᵢ`, `G' := Gᵢ⁺`, whose links are exactly the side's plus the cut edge) into the
bare induced-side lower bound `finrank_span_rigidityRows_cutEdge_eq` consumes as `hlbᵢ`: the
`(screwDim k − 1)` dropped here is exactly the `(D−1)·|C|` crossing term that assembly recovers,
so the arithmetic balances. Proof: every generating row of `G'` lies in `span rows(Gs) ⊔ Sc`,
where `Sc` is the image of `e₀`'s hinge-row block under `hingeRow u₀ v₀` — a swapped-orientation
generator `hingeRow v₀ u₀ r` is the image of the negated block row (`hingeRow_swap`, the block
being a subspace) — and `Sc`'s dimension is at most the block's `screwDim k − 1`
(`Submodule.finrank_map_le`, `finrank_hingeRowBlock`). -/
theorem finrank_span_rigidityRows_le_add_of_links_subset {k : ℕ} [Finite α]
    {G' Gs : Graph α β} (ext : β → ScrewSpace K k) {e₀ : β} {u₀ v₀ : α}
    (hl₀ : G'.IsLink e₀ u₀ v₀) (hext₀ : ext e₀ ≠ 0)
    (hlinks : ∀ e u v, G'.IsLink e u v → Gs.IsLink e u v ∨ e = e₀) :
    Module.finrank K (Submodule.span K
        (⟨G', ext⟩ : BodyHingeFramework K k α β).rigidityRows)
      ≤ Module.finrank K (Submodule.span K
        (⟨Gs, ext⟩ : BodyHingeFramework K k α β).rigidityRows) + (screwDim k - 1) := by
  classical
  have : Fintype α := Fintype.ofFinite α
  set F' : BodyHingeFramework K k α β := ⟨G', ext⟩ with hF'def
  set Fs : BodyHingeFramework K k α β := ⟨Gs, ext⟩ with hFsdef
  set Ss := Submodule.span K Fs.rigidityRows with hSsdef
  set Sc : Submodule K (Module.Dual K (α → ScrewSpace K k)) :=
    (F'.hingeRowBlock e₀).map ((screwDiff (k := k) (α := α) u₀ v₀).dualMap) with hScdef
  -- Every generating row of `G'` lands in `Ss ⊔ Sc`.
  have hle : Submodule.span K F'.rigidityRows ≤ Ss ⊔ Sc := by
    rw [Submodule.span_le]
    rintro φ ⟨e, u, v, hl, r, hr, rfl⟩
    rcases hlinks e u v hl with hs | rfl
    · exact Submodule.mem_sup_left (Submodule.subset_span ⟨e, u, v, hs, r, hr, rfl⟩)
    · rcases hl.eq_and_eq_or_eq_and_eq hl₀ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · -- Aligned orientation: the row is the block image on the nose.
        rw [hingeRow_eq_dualMap]
        exact Submodule.mem_sup_right (Submodule.mem_map_of_mem hr)
      · -- Swapped orientation: the row is the image of the negated block row.
        rw [hingeRow_swap, hingeRow_eq_dualMap]
        exact Submodule.mem_sup_right (Submodule.mem_map_of_mem (neg_mem hr))
  -- The cut-block image has dimension at most `screwDim k − 1`.
  have hSc : Module.finrank K ↥Sc ≤ screwDim k - 1 := by
    have hmap := Submodule.finrank_map_le
      ((screwDiff (k := k) (α := α) u₀ v₀).dualMap) (F'.hingeRowBlock e₀)
    rwa [finrank_hingeRowBlock F' hext₀] at hmap
  -- Assemble: rank of the sup is at most the sum of the ranks.
  have hsup : Module.finrank K ↥(Ss ⊔ Sc)
      ≤ Module.finrank K ↥Ss + Module.finrank K ↥Sc := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq Ss Sc
    omega
  calc Module.finrank K ↥(Submodule.span K F'.rigidityRows)
      ≤ Module.finrank K ↥(Ss ⊔ Sc) := Submodule.finrank_mono hle
    _ ≤ Module.finrank K ↥Ss + Module.finrank K ↥Sc := hsup
    _ ≤ Module.finrank K ↥Ss + (screwDim k - 1) := Nat.add_le_add_left hSc _

/-- **A body joined by one hinge adds at least the hinge's block to the rank**
(`lem:block-rank-cut`, the pendant-body case; Phase 40e BRIDGE). If `e₀ = u₀w₀` is the only link
of `G` from `V₁` to `w₀ ∉ V₁`, and every hinge of `G` is nonzero, then adding `w₀` to `V₁` raises
the rank of the induced framework by at least `screwDim k − 1`:
`finrank (span rows(G[V₁])) + (screwDim k − 1) ≤ finrank (span rows(G[V₁ ∪ {w₀}]))`.
The lower-bound companion of `finrank_span_rigidityRows_le_add_of_links_subset`, and the rank
side of `Graph.deficiency_induce_union_singleton` (`Molecule/Pencil/Motive.lean`).

Proof: the cut-edge brick `le_finrank_span_rigidityRows_of_cut` inside `G[V₁ ∪ {w₀}]` at `V₁`,
whose only crossing edge is `e₀`; the `V₁` side re-induces to `G[V₁]`, and the singleton side's
rank is dropped. -/
theorem add_le_finrank_span_rigidityRows_induce_union_singleton [Finite α] [Finite β]
    {G : Graph α β} (ext : β → ScrewSpace K k) {V₁ : Set α} {e₀ : β} {u₀ w₀ : α}
    (hl₀ : G.IsLink e₀ u₀ w₀) (hu₀ : u₀ ∈ V₁) (hw₀ : w₀ ∉ V₁)
    (honly : ∀ e u, G.IsLink e u w₀ → u ∈ V₁ → e = e₀)
    (hext : ∀ e u v, G.IsLink e u v → ext e ≠ 0) :
    Module.finrank K (Submodule.span K
        (⟨G.induce V₁, ext⟩ : BodyHingeFramework K k α β).rigidityRows) + (screwDim k - 1)
      ≤ Module.finrank K (Submodule.span K
        (⟨G.induce (V₁ ∪ {w₀}), ext⟩ : BodyHingeFramework K k α β).rigidityRows) := by
  have hbrick := le_finrank_span_rigidityRows_of_cut
    (⟨G.induce (V₁ ∪ {w₀}), ext⟩ : BodyHingeFramework K k α β) (V₁ := V₁) (C := {e₀})
    (by simp) (fun e u v hl => hext e u v hl.1) ?_ ?_
  · have hind : (G.induce (V₁ ∪ {w₀})).induce V₁ = G.induce V₁ :=
      Graph.ext rfl fun e x y => by
        simp only [Graph.induce_isLink]
        exact ⟨fun ⟨⟨hl, _, _⟩, hx, hy⟩ => ⟨hl, hx, hy⟩,
          fun ⟨hl, hx, hy⟩ => ⟨⟨hl, Or.inl hx, Or.inl hy⟩, hx, hy⟩⟩
    dsimp only at hbrick
    rw [hind, Set.ncard_singleton, Nat.mul_one] at hbrick
    omega
  · rintro e u v ⟨hl, hu, hv⟩ he
    have hne : e ≠ e₀ := he
    by_cases hu₁ : u ∈ V₁ <;> by_cases hv₁ : v ∈ V₁
    · exact Or.inl ⟨hu₁, hv₁⟩
    · obtain rfl : v = w₀ := hv.resolve_left hv₁
      exact absurd (honly e u hl hu₁) hne
    · obtain rfl : u = w₀ := hu.resolve_left hu₁
      exact absurd (honly e v hl.symm hv₁) hne
    · exact Or.inr ⟨hu₁, hv₁⟩
  · rintro e rfl
    exact ⟨u₀, w₀, ⟨hl₀, Or.inl hu₀, Or.inr rfl⟩, hu₀, hw₀⟩

end CutEdgeBrick

section SpliceBrick

variable {α β : Type*} {k : ℕ}

-- letI instance-shadowing for AddCommGroup ↥S in the h_rn subproof is elaboration-heavy
-- (the Semiring/AddCommMonoid vs. Ring/AddCommGroup instance diamond for submodule subtypes);
/-- **General-rank shared-body splice block-rank addition** (`lem:rigidityRows-splice-rank-add`;
KT Lemma 6.2 eqs.\ (6.3)–(6.5); Phase 22i L5a-i). Block-triangular rank-addition for a
shared-body split: given a linear endomorphism `D` of the rigidity-row dual space, a "rigid
block" submodule `SH = span(FH.rigidityRows)` lying in the kernel of `D`, and a "contraction
block" `Sc = span(Fc.rigidityRows)` whose image under `D` embeds in the image of the full span
`S = span(F.rigidityRows)`, the two block finranks satisfy

  `finrank SH + finrank Sc ≤ finrank S`.

This is the row-space version of KT's lower-triangular block-rank inequality (eq. (6.3)):
the `H`-block rows vanish under `D` (the top-right `0` of the block-triangular matrix, from
`hingeRow_comp_extProj_eq_zero`), and the contraction rows survive under `D` at their full
rank (Lemma 5.1 / `finrank_pinnedMotions_add_screwDim`, the column-deletion rank invariance
captured by `hInj`). Unlike L4a's vertex-disjoint cut (`le_finrank_span_rigidityRows_of_cut`,
where the split is disjoint by a vertex-projection argument), the two blocks share the
contracted body `r = v*`; the "disjointness" is the kernel containment `SH ≤ ker D` rather
than a geometric vertex partition.

Proof: rank-nullity for `D` restricted to `S` gives
`finrank(S.map D) + finrank(S ⊓ ker D) = finrank S`.
`SH ≤ S ⊓ ker D` (from `hFH_le` and `hFH_ker`) bounds the kernel term below by `finrank SH`.
`hFc_surv_le` and `hInj` bound the image term below by `finrank Sc`.
Adding gives the conclusion. -/
-- `unusedArguments` FALSE POSITIVE: the `Fintype.ofFinite` bridge in the proof body
-- needs this instance to elaborate; it does not survive into the proof term.
@[nolint unusedArguments]
theorem le_finrank_span_rigidityRows_of_splice [Finite α] [Finite β]
    (F FH Fc : BodyHingeFramework K k α β)
    (D : Module.Dual K (α → ScrewSpace K k) →ₗ[K] Module.Dual K (α → ScrewSpace K k))
    (hFH_le : Submodule.span K FH.rigidityRows ≤ Submodule.span K F.rigidityRows)
    (hFH_ker : Submodule.span K FH.rigidityRows ≤ LinearMap.ker D)
    (hFc_surv_le : (Submodule.span K Fc.rigidityRows).map D ≤
                    (Submodule.span K F.rigidityRows).map D)
    (hInj : Module.finrank K ↥(Submodule.span K Fc.rigidityRows) =
             Module.finrank K ↥((Submodule.span K Fc.rigidityRows).map D)) :
    Module.finrank K ↥(Submodule.span K FH.rigidityRows) +
    Module.finrank K ↥(Submodule.span K Fc.rigidityRows) ≤
    Module.finrank K ↥(Submodule.span K F.rigidityRows) := by
  have : Fintype α := Fintype.ofFinite α
  have : Fintype β := Fintype.ofFinite β
  have : FiniteDimensional K (Module.Dual K (α → ScrewSpace K k)) := inferInstance
  set SH := Submodule.span K FH.rigidityRows with hSH_def
  set Sc := Submodule.span K Fc.rigidityRows with hSc_def
  set S := Submodule.span K F.rigidityRows with hS_def
  -- Rank-nullity for D restricted to S: finrank(S.map D) + finrank(S ⊓ ker D) = finrank S.
  -- Route: let N = comap S.subtype (ker D) ≤ ↥S (the kernel of D|_S inside ↥S).
  -- Quotient rank-nullity on ↥S with N gives finrank(↥S ⧸ N) + finrank N = finrank S.
  -- Then ↥S ⧸ N ≅ (D.comp S.subtype).range = S.map D via quotKerEquivRange,
  -- and finrank N = finrank(S ⊓ ker D) via finrank_map_subtype_eq + map_comap_subtype.
  have h_rn : Module.finrank K ↥(S.map D) + Module.finrank K ↥(S ⊓ LinearMap.ker D) =
      Module.finrank K ↥S := by
    -- letI (not haveI) forces AddCommGroup ↥S to shadow the global AddCommMonoid ↥S instance,
    -- enabling Ring/AddCommGroup paths for domRestrict and finrank_quotient_add_finrank.
    let hSAG : AddCommGroup ↥S := S.addCommGroup
    have hq : Module.finrank K (↥S ⧸ (D.domRestrict S).ker) +
        Module.finrank K ↥(D.domRestrict S).ker = Module.finrank K ↥S :=
      (D.domRestrict S).ker.finrank_quotient_add_finrank
    have heq : Module.finrank K (↥S ⧸ (D.domRestrict S).ker) =
        Module.finrank K ↥(S.map D) := by
      have h := LinearEquiv.finrank_eq (D.domRestrict S).quotKerEquivRange
      rw [LinearMap.range_domRestrict] at h
      exact h
    have hker : Module.finrank K ↥(D.domRestrict S).ker =
        Module.finrank K ↥(S ⊓ LinearMap.ker D) := by
      rw [LinearMap.ker_domRestrict,
          ← Submodule.finrank_map_subtype_eq S (Submodule.comap S.subtype (LinearMap.ker D)),
          Submodule.map_comap_subtype]
    linarith
  -- SH ≤ S ⊓ ker D, so finrank SH ≤ finrank(S ⊓ ker D).
  have h_SH_le_inf : SH ≤ S ⊓ LinearMap.ker D := le_inf hFH_le hFH_ker
  have h_SH_le : Module.finrank K ↥SH ≤ Module.finrank K ↥(S ⊓ LinearMap.ker D) :=
    Submodule.finrank_mono h_SH_le_inf
  -- Sc.map D ≤ S.map D, so finrank Sc ≤ finrank(S.map D).
  have h_Sc_le : Module.finrank K ↥Sc ≤ Module.finrank K ↥(S.map D) :=
    hInj.le.trans (Submodule.finrank_mono hFc_surv_le)
  linarith

end SpliceBrick

section PinnedPlacementBrick

variable {α β : Type*} {k : ℕ}

/-- **Span-level pinned-placement block-rank lower bound**
(`lem:rigidityRows-pinned-placement-rank-add`; the eq.~(6.12) placement core shared by KT Lemma 6.8
(Case II / `k > 0` split) and Lemma 6.10 (Case III); Phase 22j). The span-transport analogue of the
splice brick (`le_finrank_span_rigidityRows_of_splice`), for the *pin-a-body* (splitting) geometry
rather than the *collapse* (`extProj`-projected-column) geometry: given a body-hinge framework `F`,
a body `v`, a **new block** of functionals `rn : ιn → Module.Dual K (α → ScrewSpace K k)`
independent
through `v`'s screw column (`hnewpin`) and lying in `span F.rigidityRows` (`hnew_span`), and an
**old block** `ro : ιo → …` that (a) vanishes on `v`'s screw column (`hold`), (b) is independent
(`holdindep`), and (c) lies in `span F.rigidityRows` (`hold_span`), the two block sizes satisfy

  `Nat.card ιn + Nat.card ιo ≤ finrank (span F.rigidityRows)`.

The proof is the `hrank_lb` skeleton of the KT Lemma 6.8 producer `case_II_realization_all_k` lifted
out (Phase 22i L6b, CaseI.lean): the block-triangular pin-a-body split
(`linearIndependent_sum_pinned_block`) makes the combined family `Sum.elim rn ro` independent; its
span lies in `span F.rigidityRows` (`hnew_span`/`hold_span`); and `finrank_span_eq_card` +
`Submodule.finrank_mono` of the combined span give the count. **No new linear algebra** — the
abstraction's value is in the *callers'* discharge of `hold_span` (the genuinely-new content): the
`splitOff` `e₀ = e_a + e_b` row decomposition for Lemma 6.8, the `removeVertex`+relabel
`hingeRow ∈ span` interface for Case III, and `Submodule.subset_span ∘ panelRow_mem_rigidityRows`
under a literal `Gv ≤ G`. Unlike the literal placement bricks (`case_II_placement_eq612`), the
conclusion keys on `span F.rigidityRows` membership, **not** literal `F.rigidityRows` membership, so
every real reduction graph (collapse / `splitOff` / relabel — which land rows only in the span)
fits. Carrier-free at the block level (the row functionals are arbitrary duals); the
`ofNormals`/`withGraph` defeq trap (TACTICS-QUIRKS §38) does not bite. -/
theorem le_finrank_span_rigidityRows_of_pinned_placement [Finite α]
    [DecidableEq α] {ιn ιo : Type*} [Finite ιn] [Finite ιo] (F : BodyHingeFramework K k α β) {v : α}
    {rn : ιn → Module.Dual K (α → ScrewSpace K k)} {ro : ιo → Module.Dual K (α → ScrewSpace K k)}
    (hold : ∀ (j : ιo) (x : ScrewSpace K k),
      ro j (Function.update (0 : α → ScrewSpace K k) v x) = 0)
    (hnewpin : LinearIndependent K
      (fun i : ιn => (rn i).comp (LinearMap.single K (fun _ : α => ScrewSpace K k) v)))
    (holdindep : LinearIndependent K ro)
    (hnew_span : ∀ i : ιn, rn i ∈ Submodule.span K F.rigidityRows)
    (hold_span : ∀ j : ιo, ro j ∈ Submodule.span K F.rigidityRows) :
    Nat.card ιn + Nat.card ιo ≤ Module.finrank K ↥(Submodule.span K F.rigidityRows) := by
  have : Fintype α := Fintype.ofFinite α
  have : Fintype ιn := Fintype.ofFinite ιn
  have : Fintype ιo := Fintype.ofFinite ιo
  -- The combined family `Sum.elim rn ro` is independent by the pin-a-body block split.
  have hunion : LinearIndependent K (Sum.elim rn ro) :=
    linearIndependent_sum_pinned_block (v := v) hold hnewpin holdindep
  -- Its span lies in `span F.rigidityRows` (both blocks are span members).
  have hcomb_le : Submodule.span K (Set.range (Sum.elim rn ro)) ≤
      Submodule.span K F.rigidityRows := by
    rw [Submodule.span_le]
    rintro _ ⟨(i | j), rfl⟩
    · exact hnew_span i
    · exact hold_span j
  -- `finrank (combined span) = |ιn ⊕ ιo|`, then monotonicity gives the count bound.
  have hmono := Submodule.finrank_mono hcomb_le
  rw [finrank_span_eq_card hunion, Fintype.card_sum,
    ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at hmono
  exact hmono

/-- **The `+1` augment of the pinned-placement block-rank lower bound**
(`lem:rigidityRows-pinned-placement-rank-add`; the Case-III variant routing through the augmented
pin-a-body split `linearIndependent_sum_pinned_block_augment`, KT eq.~(6.29) shape; Phase 22j). The
sibling of `le_finrank_span_rigidityRows_of_pinned_placement` that lifts the new block by one extra
candidate row `w` pinned through body `v`'s screw column (`hnewpinaug`, the augmented top-left
`D × D` full-rank block), supplying Case III's `+1` over the stratum-1
`D(|V|−1) − 1` count. With `w` lying in `span F.rigidityRows` (`hw_span`) the count becomes

  `Nat.card ιn + 1 + Nat.card ιo ≤ finrank (span F.rigidityRows)`.

Proof: the augmented combined family `Sum.elim (Sum.elim rn (fun _ : Unit => w)) ro` is independent
by `linearIndependent_sum_pinned_block_augment`; its span lies in `span F.rigidityRows`; and
`finrank_span_eq_card` + `Submodule.finrank_mono` give the count
(`Nat.card (ιn ⊕ Unit) + Nat.card ιo = Nat.card ιn + 1 + Nat.card ιo`). The `Unit` summand is the
extra candidate row. Same span-transport interface, callers, and carrier-freeness as the unaugmented
brick. -/
theorem le_finrank_span_rigidityRows_of_pinned_placement_augment [Finite α]
    [DecidableEq α] {ιn ιo : Type*} [Finite ιn] [Finite ιo] (F : BodyHingeFramework K k α β) {v : α}
    {rn : ιn → Module.Dual K (α → ScrewSpace K k)} {ro : ιo → Module.Dual K (α → ScrewSpace K k)}
    {w : Module.Dual K (α → ScrewSpace K k)}
    (hold : ∀ (j : ιo) (x : ScrewSpace K k),
      ro j (Function.update (0 : α → ScrewSpace K k) v x) = 0)
    (hnewpinaug : LinearIndependent K (Sum.elim
      (fun i : ιn => (rn i).comp (LinearMap.single K (fun _ : α => ScrewSpace K k) v))
      (fun _ : Unit => w.comp (LinearMap.single K (fun _ : α => ScrewSpace K k) v))))
    (holdindep : LinearIndependent K ro)
    (hnew_span : ∀ i : ιn, rn i ∈ Submodule.span K F.rigidityRows)
    (hw_span : w ∈ Submodule.span K F.rigidityRows)
    (hold_span : ∀ j : ιo, ro j ∈ Submodule.span K F.rigidityRows) :
    Nat.card ιn + 1 + Nat.card ιo ≤ Module.finrank K ↥(Submodule.span K F.rigidityRows) := by
  have : Fintype α := Fintype.ofFinite α
  have : Fintype ιn := Fintype.ofFinite ιn
  have : Fintype ιo := Fintype.ofFinite ιo
  -- The augmented combined family is independent by the augmented pin-a-body split.
  have hunion : LinearIndependent K (Sum.elim (Sum.elim rn (fun _ : Unit => w)) ro) :=
    linearIndependent_sum_pinned_block_augment (v := v) hold hnewpinaug holdindep
  -- Its span lies in `span F.rigidityRows` (`rn`, `w`, and `ro` are all span members).
  have hcomb_le : Submodule.span K
      (Set.range (Sum.elim (Sum.elim rn (fun _ : Unit => w)) ro)) ≤
      Submodule.span K F.rigidityRows := by
    rw [Submodule.span_le]
    rintro _ ⟨((i | _) | j), rfl⟩
    · exact hnew_span i
    · exact hw_span
    · exact hold_span j
  -- `finrank (combined span) = |(ιn ⊕ Unit) ⊕ ιo|`, then monotonicity gives the count bound.
  have hmono := Submodule.finrank_mono hcomb_le
  rw [finrank_span_eq_card hunion, Fintype.card_sum, Fintype.card_sum, Fintype.card_unit,
    ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at hmono
  exact hmono

end PinnedPlacementBrick

/-! ## Relative screws, the joint rows, and the welded rank (the vertex 2-cut layer)

The carriers of the vertex-2-cut rank laws (Phase 39 item 6, Layer B): the objects the gluing
identity at a vertex 2-cut `{u, v}` and the welded bound are stated in.  The informal statements
are the PENCIL attack workbook's §§ S7, S10(ii) and S14(i)
(`notes/pencil/workbook/attack-smark.md`), read against this file's carrier by the item-6 carrier
recon (`notes/Phase39-design.md` § *Item-6 carrier recon (2026-09-16)*, which pins each signature
below).  `relScrews` and `jointRows` are pinned by `def:relative-screws`, the gluing identity by
`cor:block-rank-vertex-two-cut` and its edge-partitioned generalization by
`lem:block-rank-two-cut` (Phase 40g); `jointMotions`, `weldedRank` and their laws carry no
blueprint node yet (Phase 39's decision D5; their pins move to a first consumer,
`notes/Phase40g.md`).

* `relScrews` (`ρ̄_{uv}`) — the space of **relative screw centers** `S v − S u` realized by
  infinitesimal motions of the framework.  Its dimension `ρ` is what the two sides of a vertex
  2-cut exchange through the cut pair.
* `jointRows U u v` — the rigidity rows of the **joint** at the body pair `u, v` that confines the
  relative screw to `U`: the hinge rows `hingeRow u v r` over the annihilator block
  `U^⊥ = U.dualAnnihilator`.  At `U = ⊥` (annihilator `⊤`) this is the full **rigid weld**
  `S u = S v`; general `U` is the body-bar-hinge reading of S7(ii), whose laws are deferred
  (`notes/Phase39.md` *Lemma checklist*, item 6) — the annihilator phrasing makes the weld and
  those profiles one definition.
* `jointMotions` (`M_U`) — the motions obeying that joint constraint, the motion-side object of
  S7(i).
* `weldedRank` — the rigidity-row rank of the framework with `u, v` welded rigidly together, the
  `rank_w` of S14(i).

`finrank_span_jointRows` is the layer's first fact: at a genuine pair of **distinct** bodies the
joint contributes exactly `screwDim k − dim U` independent rows — in particular `screwDim k` for
the weld.  The layer's headline identity is `weldedRank_eq` (B4): welding a **distinct** pair costs
exactly `dim ρ̄_{uv}`, `rank_w = rank + ρ`.  It turns on B3
(`inf_span_rigidityRows_span_jointRows_top`) — the weld rows a framework already implies are exactly
the ones annihilating `ρ̄_{uv}` — with the orientation bookkeeping in `map_screwDiff_comm` and the
`U = ⊥` unfolding in `span_jointRows_bot`.  The layer's other identity is the **gluing identity at
a 2-cut** (B5′/B6′): two graphs whose links partition the framework's, each inside a vertex set,
the two sets overlapping inside a cut pair `{u, v}`, meet, as row spans, exactly in
`jointRows (ρ̄₁ ⊔ ρ̄₂) u v` (`inf_span_rigidityRows_of_twoCut_of_isLink`), so their ranks sum to
the whole rank plus the `screwDim k − dim (ρ̄₁ ⊔ ρ̄₂)` rows they share
(`finrank_span_rigidityRows_twoCut_eq_of_isLink`, stated in `ℤ`) — and, unlike its combinatorial
counterpart `Graph.deficiency_eq_of_vertexTwoCut`, it needs no non-adjacency of the pair.  At the
induced sides of a vertex 2-cut these are B5/B6 (`inf_span_rigidityRows_of_vertexTwoCut`,
`finrank_span_rigidityRows_vertexTwoCut_eq`); the general sides serve an ear whose ends are
adjacent (`MainComponent/Ear.lean`), where the side induced on the path is not the path.  At a
cut *vertex* (`u = v`) no relative screw survives and the ranks add outright
(`finrank_span_rigidityRows_cutVertex_eq`, Phase 40e).
Keep the `screwDiff v u` orientation of `relScrews` /
`jointMotions` as written: the whole layer, and the Layer-C losses above it, are stated against
it (it is immaterial to the mathematics — a submodule is closed under negation — but not to the
`rw`s). -/

section TwoCutCarriers

/-- The **relative-screw space** `ρ̄_{uv}` of a body pair (`notes/pencil/workbook/attack-smark.md`
§ S7): the image of the motion space `Z(G,p) = infinitesimalMotions` under the relative-screw
evaluation `screwDiff v u : S ↦ S v − S u`, i.e. the subspace of `ScrewSpace K k` of relative screw
centers that some infinitesimal motion of the framework realizes between the bodies `u` and `v`.

It is the object a vertex 2-cut `{u, v}` couples the two sides through: a side's rank and its welded
rank differ by exactly `dim ρ̄_{uv}` at a distinct pair (`weldedRank_eq`, the `rank_w = rank + ρ` of
B4), and the gluing identity at the cut (`finrank_span_rigidityRows_vertexTwoCut_eq`, B6) adds the
two sides' ranks and subtracts the codimension of the join `ρ̄₁ ⊔ ρ̄₂`.  The two extremes are
definitional:
`relScrews = ⊥` says every infinitesimal motion moves `u` and `v` as one body, and
`relScrews = ⊤` that every relative screw center is realized by some motion. -/
noncomputable def relScrews (F : BodyHingeFramework K k α β) (u v : α) :
    Submodule K (ScrewSpace K k) :=
  Submodule.map (screwDiff v u) F.infinitesimalMotions

/-- **Relative screws read the hinges only on the links** of the graph (Phase 40h SHORT): two
hinge assignments on `H` agreeing at every link have the same relative screws at every pair. The
motion space reads the hinges only through the constraints at links (`IsInfinitesimalMotion`). -/
theorem relScrews_congr (H : Graph α β) {C C' : β → ScrewSpace K k}
    (h : ∀ f u w, H.IsLink f u w → C f = C' f) (a b : α) :
    (⟨H, C⟩ : BodyHingeFramework K k α β).relScrews a b =
      (⟨H, C'⟩ : BodyHingeFramework K k α β).relScrews a b := by
  have hZ : (⟨H, C⟩ : BodyHingeFramework K k α β).infinitesimalMotions =
      (⟨H, C'⟩ : BodyHingeFramework K k α β).infinitesimalMotions :=
    infinitesimalMotions_eq_of_isLink_supportExtensor _ _ rfl fun f u w hf => (h f u w hf).symm
  rw [relScrews, relScrews, hZ]

/-- The **joint rows** at a body pair `u, v` confining the relative screw to `U`
(`notes/pencil/workbook/attack-smark.md` § S7(ii)): the set of rigidity-row functionals
`hingeRow u v r` as `r` ranges over the annihilator `U^⊥ = U.dualAnnihilator ⊆ Module.Dual K
(ScrewSpace K k)`.  A screw assignment `S` is annihilated by all of them exactly when
`S u − S v ∈ U` (the double-annihilator identity over a field), so these are the rows the joint
adds to `R(G,p)`.

Two instances matter, and the annihilator phrasing makes them **one** definition.  At `U = ⊥` the
annihilator is `⊤`, the rows are all of `hingeRow u v '' Module.Dual K (ScrewSpace K k)` and the
joint is the **rigid weld** `S u = S v` — the instance the welded rank `weldedRank` and the
consumed welded bound S14(i) use.  At general `U` the joint is S7(ii)'s body-bar-hinge reading
(`6 − dim U` bars between `u` and `v` along a spanning set of `U^⊥`), whose laws are deferred off
the consumed path.

This takes no framework: the joint's rows depend only on the pair and on `U`, and they are adjoined
to a framework's own rows by a union (`weldedRank`). -/
noncomputable def jointRows (U : Submodule K (ScrewSpace K k)) (u v : α) :
    Set (Module.Dual K (α → ScrewSpace K k)) :=
  (fun r => hingeRow u v r) '' U.dualAnnihilator

/-- The **`U`-constrained motion space** `M_U` at a body pair
(`notes/pencil/workbook/attack-smark.md` § S7(i)): the infinitesimal motions whose relative screw
center at `u, v` lies in `U`, i.e. `F.infinitesimalMotions ⊓ comap (screwDiff v u) U`.  S7(ii) reads
it as the motion space of the body-bar-hinge framework `G ∪ bars(U^⊥)` — the common kernel of
`F.rigidityRows ∪ jointRows U u v`; the two constraints match because `U` is closed under negation,
so `S v − S u ∈ U` and `S u − S v ∈ U` say the same thing.

The motion-side companion of `jointRows`: `S7(i)`'s fibre identity
`M_U(H)/M(H/uv) ≅ ρ̄ ∩ U` reads it against the welded framework.  Motion-side statements over this
carrier are `|α|`-laden — `infinitesimalMotions` lives over **all** of `α`, not over `V(G)` — which
is why the item-6 laws are stated rank-side and the one law that cannot be is deferred
(`notes/Phase39.md` *Lemma checklist*, item 6, *Normalization*). -/
noncomputable def jointMotions (F : BodyHingeFramework K k α β)
    (U : Submodule K (ScrewSpace K k)) (u v : α) : Submodule K (α → ScrewSpace K k) :=
  F.infinitesimalMotions ⊓ Submodule.comap (screwDiff v u) U

/-- The **welded rank** of a framework at a body pair (`notes/pencil/workbook/attack-smark.md`
§ S14(i)'s `rank_w`): the dimension of the span of the framework's own rigidity rows together with
the rigid weld's joint rows at `u, v` (`jointRows ⊥ u v`) — the row rank of the framework *with the
pair welded*, taken on `F`'s own screw-assignment space rather than on a contracted body set.

Stating the weld as *extra rows on the same space* (rather than as the rigidity matrix of the
contracted graph `G/uv`) is what keeps the welded rank comparable to `F`'s own rank; the fact about
it is `weldedRank = rank + dim ρ̄_{uv}` at a distinct pair (`weldedRank_eq`), which is the whole
linear-algebraic content of the transcribed welded bound `ρ ≤ δ + a`.  It is deliberately *not*
identified with a rank of `R(G/uv, p)` on the contracted body set: the two differ by the weld's own
rows, and that offset is exactly where the recon's first `weldedLoss` normalization was wrong
(`notes/Phase39-design.md` § *Item-6 carrier recon*, the loss carriers).  The combinatorial side of
that comparison is `Graph.deficiencyMerged` (`Molecular/Deficiency.lean`), the deficiency over
labelings that identify `u` with `v`. -/
noncomputable def weldedRank (F : BodyHingeFramework K k α β) (u v : α) : ℕ :=
  Module.finrank K
    (Submodule.span K (F.rigidityRows ∪ jointRows (⊥ : Submodule K (ScrewSpace K k)) u v))

/-- **The joint rows span the image of the annihilator block under the relative-screw dual map**:
`span (jointRows U u v) = (U.dualAnnihilator).map (screwDiff u v).dualMap`.  The generating set is
already the image of a *submodule* under a linear map (`hingeRow u v = (screwDiff u v).dualMap`,
`hingeRow_eq_dualMap`), so taking its span only reassembles that image
(`Submodule.span_image` + `Submodule.span_eq`, the same two steps the cut brick's `Sc` computation
above performs inline).

This is the unfolding lemma `jointRows` is used through — both by `finrank_span_jointRows` here and
by the rows-vs-motions arguments above it — so that no consumer has to see the `Set.image` in the
definition.  The opening `Set.image_congr'` is not cosmetic: `Submodule.span_image` is keyed on
`span K (⇑?f '' _)` and will not unify its `?f` with the definition's bare lambda, even though
`hingeRow_eq_dualMap` holds by `rfl` (`notes/FRICTION.md`, the `Submodule.span_image` coe-form
idiom). -/
theorem span_jointRows_eq_map_dualAnnihilator {u v : α} (U : Submodule K (ScrewSpace K k)) :
    Submodule.span K (jointRows (α := α) U u v)
      = U.dualAnnihilator.map (screwDiff (K := K) (k := k) (α := α) u v).dualMap := by
  rw [jointRows, Set.image_congr' (fun r => hingeRow_eq_dualMap (k := k) (α := α) u v r),
    Submodule.span_image, Submodule.span_eq]

/-- **The joint at a distinct body pair contributes exactly `screwDim k − dim U` independent rows**
(`notes/pencil/workbook/attack-smark.md` § S7(ii)-(iii), the row-side count of the
`6 − dim U` bars): for `u ≠ v`,
`finrank (span (jointRows U u v)) = screwDim k − finrank U`.

Two steps, and `u ≠ v` enters only in the second.  The span is the image of the annihilator block
`U^⊥` under `(screwDiff u v).dualMap` (`span_jointRows_eq_map_dualAnnihilator`), whose dimension is
`finrank U^⊥ = screwDim k − finrank U` (`Subspace.finrank_add_finrank_dualAnnihilator_eq` and
`screwSpace_finrank`) **provided** the map is injective on it — which is where distinctness is
used: `screwDiff u v` is surjective at distinct bodies (`screwDiff_surjective`), so its dual map is
injective (`LinearMap.dualMap_injective_of_surjective`), exactly as in the independence bridge
`linearIndependent_hingeRow`.  At coincident bodies the rows all vanish (`hingeRow_self`) and the
count fails for every `U ≠ ⊤`.

The `ℕ` subtraction is honest here rather than truncating: `finrank U ≤ screwDim k` always
(`U ≤ ⊤` in a space of dimension `screwDim k`), and the additive form
`finrank U + finrank U^⊥ = screwDim k` is what the proof actually uses.  At `U = ⊥` it says the
rigid weld contributes a full `screwDim k` rows, the instance `weldedRank` reads. -/
theorem finrank_span_jointRows {u v : α} (huv : u ≠ v) (U : Submodule K (ScrewSpace K k)) :
    Module.finrank K (Submodule.span K (jointRows (α := α) U u v))
      = screwDim k - Module.finrank K U := by
  have hinj : Function.Injective (screwDiff (K := K) (k := k) (α := α) u v).dualMap :=
    LinearMap.dualMap_injective_of_surjective (screwDiff_surjective huv)
  -- The span is `U^⊥` transported by an injective map, so it has `U^⊥`'s dimension.
  have hfr : Module.finrank K (Submodule.span K (jointRows (α := α) U u v))
      = Module.finrank K U.dualAnnihilator := by
    rw [span_jointRows_eq_map_dualAnnihilator,
      ← (Submodule.equivMapOfInjective _ hinj U.dualAnnihilator).finrank_eq]
  -- `dim U + dim U^⊥ = dim (ScrewSpace K k) = screwDim k`.
  have hsum := Subspace.finrank_add_finrank_dualAnnihilator_eq U
  rw [screwSpace_finrank] at hsum
  omega

/-- **The relative-screw image is orientation-blind**: `map (screwDiff v u) Z = map (screwDiff u v)
Z` for every submodule `Z` of screw assignments.  `screwDiff` is antisymmetric — both sides are
`proj u - proj v` up to order, so `screwDiff v u = -screwDiff u v` by `neg_sub` alone — and a
submodule is closed under negation, which is mathlib's `Submodule.map_neg`.

This is where the layer's one orientation mismatch is paid.  `relScrews` is defined with
`screwDiff v u` (S7's `ρ̄_{uv}`), while `jointRows` and its unfolding
`span_jointRows_eq_map_dualAnnihilator` run on `(screwDiff u v).dualMap`; the carriers' docstrings
say in prose that the difference is immaterial to the mathematics, and this lemma is what makes it a
fact the `rw`s can use.  It is *not* immaterial to the syntax: neither orientation rewrites into the
other without it. -/
theorem map_screwDiff_comm (Z : Submodule K (α → ScrewSpace K k)) (u v : α) :
    Submodule.map (screwDiff (K := K) (k := k) v u) Z
      = Submodule.map (screwDiff (K := K) (k := k) u v) Z := by
  have hneg : screwDiff (K := K) (k := k) (α := α) v u
      = -screwDiff (K := K) (k := k) (α := α) u v := by
    simp only [screwDiff, neg_sub]
  rw [hneg, Submodule.map_neg]

/-- **The rigid weld's rows are exactly the functionals that factor through the relative screw**:
at `U = ⊥` the annihilator is `⊤`, so `span (jointRows ⊥ u v) = range (screwDiff u v).dualMap` —
all of `S ↦ r (S u − S v)`, as `r` ranges over the whole of `Module.Dual K (ScrewSpace K k)`.

The `U = ⊥` instance of `span_jointRows_eq_map_dualAnnihilator`, in the range form the weld
arguments want: it is the shape `inf_span_rigidityRows_span_jointRows_top` intersects the
framework's own row span against, and the count `finrank_span_jointRows huv ⊥` says this range
occupies a full `screwDim k` dimensions. -/
theorem span_jointRows_bot (u v : α) :
    Submodule.span K (jointRows (α := α) (⊥ : Submodule K (ScrewSpace K k)) u v)
      = LinearMap.range (screwDiff (K := K) (k := k) u v).dualMap := by
  rw [span_jointRows_eq_map_dualAnnihilator, Submodule.dualAnnihilator_bot, Submodule.map_top]

/-- **The weld rows a framework already implies are exactly the weld rows that annihilate
`ρ̄_{uv}`** (Layer B3, `notes/pencil/workbook/attack-smark.md` § S14(i)): the rigidity-row span of
`F` meets the rigid weld's joint rows precisely in the joint rows of the relative-screw space,
`span F.rigidityRows ⊓ span (jointRows ⊥ u v) = span (jointRows (F.relScrews u v) u v)`.

This is the layer's pivot, and it reads off two annihilator identities.  A functional in the weld's
span is `r ∘ₗ screwDiff u v` for some `r` (`span_jointRows_bot`); it lies in
`span F.rigidityRows = Z.dualAnnihilator`
(`span_rigidityRows_eq_dualAnnihilator_infinitesimalMotions`, which is where `[Finite α]` is
needed) exactly when it kills every infinitesimal motion `S ∈ Z`, i.e. exactly when `r` kills every
relative screw `S u − S v`, i.e. when `r ∈ (ρ̄_{uv})^⊥` — and those `r` are precisely the ones
`jointRows (F.relScrews u v) u v` is generated by.  The orientation flip between `relScrews`'
`screwDiff v u` and the rows' `screwDiff u v` is paid by `map_screwDiff_comm`.

Distinctness of `u, v` is *not* needed: it enters the layer only in the row *count*
(`finrank_span_jointRows`), never in this identity.  Nor is `[Finite β]` (which the carrier recon
pinned): the route never touches the edge set.  Combined with the count, this gives the
welded-rank identity `weldedRank_eq`. -/
theorem inf_span_rigidityRows_span_jointRows_top [Finite α]
    (F : BodyHingeFramework K k α β) (u v : α) :
    Submodule.span K F.rigidityRows
        ⊓ Submodule.span K (jointRows (⊥ : Submodule K (ScrewSpace K k)) u v)
      = Submodule.span K (jointRows (F.relScrews u v) u v) := by
  rw [F.span_rigidityRows_eq_dualAnnihilator_infinitesimalMotions, span_jointRows_bot,
    span_jointRows_eq_map_dualAnnihilator, relScrews, map_screwDiff_comm]
  apply le_antisymm
  · rintro φ ⟨hφZ, r, rfl⟩
    refine ⟨r, ?_, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_dualAnnihilator] at hφZ ⊢
    rintro w ⟨S, hS, rfl⟩
    exact hφZ S hS
  · rintro φ ⟨r, hr, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_dualAnnihilator] at hr
    refine ⟨?_, r, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_dualAnnihilator]
    intro S hS
    exact hr _ ⟨S, hS, rfl⟩

/-- **Welding a distinct body pair costs exactly the dimension of its relative-screw space**
(Layer B4, the `rank_w = rank + ρ` of `notes/pencil/workbook/attack-smark.md` § S14(i)): for
`u ≠ v`, `weldedRank u v = finrank (span F.rigidityRows) + finrank (F.relScrews u v)`.

This single identity is the whole linear-algebraic content of the transcribed welded bound
`ρ ≤ δ + a` — it is what lets the informal argument read a side's welded rank off its own rank and
the dimension `ρ` the cut pair exchanges.

The proof is the dimension formula `finrank (P ⊔ Q) + finrank (P ⊓ Q) = finrank P + finrank Q`
(`Submodule.finrank_sup_add_finrank_inf_eq`) at `P = span F.rigidityRows` and `Q = span (jointRows
⊥ u v)`, after `Submodule.span_union` turns `weldedRank`'s `span (rows ∪ weld)` into `P ⊔ Q`.  Both
of the other two terms are instances of the joint count `finrank_span_jointRows` at the *same*
`u ≠ v`: `finrank Q = screwDim k` at `U = ⊥`, and `finrank (P ⊓ Q) = screwDim k − finrank ρ̄_{uv}`
through B3 (`inf_span_rigidityRows_span_jointRows_top`).  The two `screwDim k`'s then cancel.  The
`ℕ` subtraction never truncates because `finrank ρ̄_{uv} ≤ screwDim k` (`Submodule.finrank_le` and
`screwSpace_finrank`), which is supplied to `omega` explicitly. -/
theorem weldedRank_eq [Finite α] (F : BodyHingeFramework K k α β) {u v : α} (huv : u ≠ v) :
    F.weldedRank u v
      = Module.finrank K (Submodule.span K F.rigidityRows)
        + Module.finrank K (F.relScrews u v) := by
  have hbot : Module.finrank K
      (Submodule.span K (jointRows (α := α) (⊥ : Submodule K (ScrewSpace K k)) u v))
      = screwDim k := by
    rw [finrank_span_jointRows huv, finrank_bot, Nat.sub_zero]
  have hinf : Module.finrank K
      ↥(Submodule.span K F.rigidityRows
        ⊓ Submodule.span K (jointRows (α := α) (⊥ : Submodule K (ScrewSpace K k)) u v))
      = screwDim k - Module.finrank K (F.relScrews u v) := by
    rw [F.inf_span_rigidityRows_span_jointRows_top u v, finrank_span_jointRows huv]
  have hle : Module.finrank K (F.relScrews u v) ≤ screwDim k := by
    have h := Submodule.finrank_le (F.relScrews u v)
    rwa [screwSpace_finrank] at h
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span K F.rigidityRows)
    (Submodule.span K (jointRows (α := α) (⊥ : Submodule K (ScrewSpace K k)) u v))
  rw [weldedRank, Submodule.span_union]
  omega

/-- **The welded rank is a codimension** (Layer B7, `notes/pencil/workbook/attack-smark.md`
§ S14(i)): at a distinct body pair,

  `weldedRank u v + finrank (jointMotions ⊥ u v) = screwDim k · |α|`,

so the welded row rank counts exactly the directions the welded motion space `M_⊥(H)` leaves out
of the ambient screw-assignment space.  This is the weld's analogue of the complement brick
`finrank_span_rigidityRows_add_finrank_infinitesimalMotions`
(`AlgebraicInduction/GenericityDevice.lean`), and it is what turns a *lower* bound on the welded
motions into an *upper* bound on `weldedRank` — the pivot of the welded bound `0 ≤ a_w`
(`BodyHingeFramework.weldedLoss_nonneg`, Layer C2ℓ in `Molecule/Pencil/TwoCut.lean`).

Three annihilator identities and one dimension count.  `Submodule.span_union` splits
`weldedRank`'s generating set into `span F.rigidityRows ⊔ span (jointRows ⊥ u v)`; the first
factor is `Z.dualAnnihilator`
(`span_rigidityRows_eq_dualAnnihilator_infinitesimalMotions`, the only place `[Finite α]` is
needed), and the second is `(ker (screwDiff u v)).dualAnnihilator` — `span_jointRows_bot` puts it
in range form and `LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_surjective` converts, which
is where `u ≠ v` enters (`screwDiff_surjective`).  A join of annihilators is the annihilator of
the meet (`Subspace.dualAnnihilator_inf_eq`, used right-to-left; it lives in `namespace Subspace`,
**not** `Submodule`, and needs no finite-dimensionality), and that meet **is** `jointMotions ⊥ u
v`.  The count is then `Subspace.finrank_add_finrank_dualAnnihilator_eq` against
`finrank_screwAssignment`.

**The `comap ⊥` / `ker` step needs its own bridge, and `map_screwDiff_comm` does not serve
there.**  `jointMotions` is defined with `comap (screwDiff v u)` while the weld's rows run on
`(screwDiff u v).dualMap`; `map_screwDiff_comm` pays that orientation on the *image* side only.
On the `comap` side the flip is `Submodule.comap_bot` followed by `sub_eq_zero` and one `.symm`
(`hker` below) — four lines, but not skippable.

No `[Finite β]`: the route never touches the edge set. -/
theorem weldedRank_add_finrank_jointMotions_bot [Finite α]
    (F : BodyHingeFramework K k α β) {u v : α} (huv : u ≠ v) :
    F.weldedRank u v + Module.finrank K (F.jointMotions ⊥ u v)
      = screwDim k * Nat.card α := by
  have : Fintype α := Fintype.ofFinite α
  -- The orientation flip on the `comap` side; `map_screwDiff_comm` does not reach here.
  have hker : Submodule.comap (screwDiff (K := K) (k := k) (α := α) v u) ⊥
      = LinearMap.ker (screwDiff (K := K) (k := k) (α := α) u v) := by
    rw [Submodule.comap_bot]
    ext S
    simp only [LinearMap.mem_ker, screwDiff_apply, sub_eq_zero]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  have hj : F.jointMotions ⊥ u v
      = F.infinitesimalMotions ⊓ LinearMap.ker (screwDiff (K := K) (k := k) (α := α) u v) := by
    rw [jointMotions, hker]
  have hspanweld :
      Submodule.span K (jointRows (α := α) (⊥ : Submodule K (ScrewSpace K k)) u v)
        = (LinearMap.ker (screwDiff (K := K) (k := k) (α := α) u v)).dualAnnihilator := by
    rw [span_jointRows_bot, LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_surjective _
      (screwDiff_surjective huv)]
  have hsup : Submodule.span K
        (F.rigidityRows ∪ jointRows (⊥ : Submodule K (ScrewSpace K k)) u v)
      = (F.jointMotions ⊥ u v).dualAnnihilator := by
    rw [Submodule.span_union, F.span_rigidityRows_eq_dualAnnihilator_infinitesimalMotions,
      hspanweld, ← Subspace.dualAnnihilator_inf_eq, hj]
  rw [weldedRank, hsup]
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq (F.jointMotions ⊥ u v)
  rw [finrank_screwAssignment, ← Nat.card_eq_fintype_card] at h
  omega

/-- **A functional killing a screw-assignment subspace that already contains the coincidence
subspace factors through the relative screw**: for `u ≠ v` and any `W` with
`ker (screwDiff u v) ≤ W`,

  `W.dualAnnihilator = ((W.map (screwDiff u v)).dualAnnihilator).map (screwDiff u v).dualMap`.

Both inclusions are bookkeeping on the one identity `(screwDiff u v).dualMap r = r ∘ₗ screwDiff u
v`.  `⊇` needs no hypothesis at all: an `r` killing the image of `W` makes `r ∘ₗ screwDiff u v`
kill `W`.  `⊆` is where both hypotheses enter — `φ ∈ W^⊥ ≤ (ker (screwDiff u v))^⊥` by
antitonicity (`Submodule.dualAnnihilator_anti`), and at a **distinct** pair the relative-screw
evaluation is surjective (`screwDiff_surjective`), so that annihilator *is* the range of its dual
map (`LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_surjective`); hence
`φ = r ∘ₗ screwDiff u v` for some `r`, and the `⊇` computation run backwards puts that `r` in the
image's annihilator.

This is the linear-algebraic core of the 2-cut gluing identity
`inf_span_rigidityRows_of_twoCut_of_isLink` (B5′), where `W = Z₁ ⊔ Z₂` is the join of the two
sides' motion spaces and `ker (screwDiff u v) ≤ W` is the geometric content
(`mem_sup_infinitesimalMotions_of_isLink`).  The general form — any surjective `f` and any
`W ⊇ ker f` — is upstream-eligible; it is kept private and `screwDiff`-specialized here
(`notes/FRICTION.md`). -/
private theorem dualAnnihilator_eq_map_dualMap_screwDiff {u v : α} (huv : u ≠ v)
    (W : Submodule K (α → ScrewSpace K k))
    (hker : LinearMap.ker (screwDiff (K := K) (k := k) (α := α) u v) ≤ W) :
    W.dualAnnihilator
      = (W.map (screwDiff (K := K) (k := k) (α := α) u v)).dualAnnihilator.map
          (screwDiff (K := K) (k := k) (α := α) u v).dualMap := by
  refine le_antisymm (fun φ hφ => ?_) ?_
  · have hmem : φ ∈ LinearMap.range (screwDiff (K := K) (k := k) (α := α) u v).dualMap := by
      rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_surjective _
        (screwDiff_surjective huv)]
      exact Submodule.dualAnnihilator_anti hker hφ
    rw [LinearMap.mem_range] at hmem
    obtain ⟨r, rfl⟩ := hmem
    refine ⟨r, ?_, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_dualAnnihilator]
    rintro y ⟨S, hS, rfl⟩
    simpa using (Submodule.mem_dualAnnihilator _).1 hφ S hS
  · rintro φ ⟨r, hr, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_dualAnnihilator] at hr
    rw [Submodule.mem_dualAnnihilator]
    exact fun S hS => hr _ ⟨S, hS, rfl⟩

/-- **An assignment constant on a side is an infinitesimal motion of that side**: if every link of
`G` has both ends in `V` and `S a = c` for every `a ∈ V`, then `S` is a motion of `⟨G, C⟩`. Each
hinge constraint reads `c − c = 0 ∈ span {C e}`; no geometry is used, and nothing at all is
assumed about `S` off `V`.

Both the `c = 0` instance ("`S` vanishes on `V`") and the general one are consumed by
`mem_sup_infinitesimalMotions_of_isLink`.  It is read off the *definition* of
`infinitesimalMotions`, whose constraint quantifies only over the graph's own links. -/
theorem isInfinitesimalMotion_of_eqOn_of_isLink (G : Graph α β) (C : β → ScrewSpace K k)
    {V : Set α} (hV : ∀ e x y, G.IsLink e x y → x ∈ V ∧ y ∈ V)
    {S : α → ScrewSpace K k} {c : ScrewSpace K k} (hS : ∀ a ∈ V, S a = c) :
    (⟨G, C⟩ : BodyHingeFramework K k α β).IsInfinitesimalMotion S := by
  intro e x y he
  obtain ⟨hx, hy⟩ := hV e x y he
  rw [hingeConstraint_iff, hS x hx, hS y hy, sub_self]
  exact Submodule.zero_mem _

/-- **An assignment that moves the cut pair alike splits across a 2-cut**: let every link of `G₁`
lie inside `V₁` and every link of `G₂` inside `V₂`, with the sides overlapping inside the pair
(`V₁ ∩ V₂ ⊆ {u, v}`). If `S u = S v`, the assignment `S` is the sum of a motion of side 1 and a
motion of side 2,

  `S ∈ (⟨G₁, C⟩).infinitesimalMotions ⊔ (⟨G₂, C⟩).infinitesimalMotions`.

One explicit `if` does it: `A a = if a ∈ V₂ then S v else S a` is constant on `V₂`, hence a motion
of side 2, and `S − A` vanishes on `V₁` — off `V₂` by construction, and on `V₁ ∩ V₂ ⊆ {u, v}`
because `S u = S v` is exactly the value `A` carries there — hence a motion of side 1
(`isInfinitesimalMotion_of_eqOn_of_isLink` twice).

Read dually this is `ker (screwDiff u v) ≤ Z₁ ⊔ Z₂`, the one geometric input of the 2-cut gluing
identity `inf_span_rigidityRows_of_twoCut_of_isLink`: the only motions the two sides fail to
generate between them are those that separate `u` from `v`.  Neither `u ≠ v` nor any relation
between the two graphs is used; at `u = v` it gives the cut-vertex identity
`finrank_span_rigidityRows_cutVertex_eq`. -/
theorem mem_sup_infinitesimalMotions_of_isLink (G₁ G₂ : Graph α β) (C : β → ScrewSpace K k)
    {V₁ V₂ : Set α} {u v : α}
    (h₁ : ∀ e x y, G₁.IsLink e x y → x ∈ V₁ ∧ y ∈ V₁)
    (h₂ : ∀ e x y, G₂.IsLink e x y → x ∈ V₂ ∧ y ∈ V₂)
    (hoverlap : V₁ ∩ V₂ ⊆ {u, v}) {S : α → ScrewSpace K k} (hS : S u = S v) :
    S ∈ (⟨G₁, C⟩ : BodyHingeFramework K k α β).infinitesimalMotions
        ⊔ (⟨G₂, C⟩ : BodyHingeFramework K k α β).infinitesimalMotions := by
  classical
  refine Submodule.mem_sup.2 ⟨S - (fun a => if a ∈ V₂ then S v else S a), ?_,
    (fun a => if a ∈ V₂ then S v else S a), ?_, by abel⟩
  · refine (mem_infinitesimalMotions _ _).2
      (isInfinitesimalMotion_of_eqOn_of_isLink G₁ C h₁ (c := 0) ?_)
    intro a ha
    by_cases hb : a ∈ V₂
    · have hau : a = u ∨ a = v := by simpa using hoverlap ⟨ha, hb⟩
      rcases hau with rfl | rfl
      · simp [hb, hS]
      · simp [hb]
    · simp [hb]
  · exact (mem_infinitesimalMotions _ _).2
      (isInfinitesimalMotion_of_eqOn_of_isLink G₂ C h₂ (c := S v) (fun a ha => by simp [ha]))

/-- **The rigidity rows read the graph only through its links**: two graphs with the same links
give the same rows at the same hinges (their vertex sets may differ). -/
theorem rigidityRows_congr_isLink {G₁ G₂ : Graph α β} (C : β → ScrewSpace K k)
    (h : ∀ e x y, G₁.IsLink e x y ↔ G₂.IsLink e x y) :
    (⟨G₁, C⟩ : BodyHingeFramework K k α β).rigidityRows
      = (⟨G₂, C⟩ : BodyHingeFramework K k α β).rigidityRows := by
  ext φ
  simp only [rigidityRows, Set.mem_ofPred_eq, h]
  rfl

/-- **Link-partitioning sides split the row set**: if the links of `F.graph` are exactly those of
`G₁` together with those of `G₂`, then `F.rigidityRows` is the union of the two sides' rows at
`F`'s hinges.  No row is re-indexed: the hinge-row block is the *same* submodule on both sides,
since `hingeRowBlock` reads only `supportExtensor e`, which the sides inherit unchanged.

This is the row-side half of the rank identity `finrank_span_rigidityRows_twoCut_eq_of_isLink`
(B6′), where `Submodule.span_union` turns it into a join of the two side spans.  Unlike the
disjoint cut brick's side-span inclusions (`le_finrank_span_rigidityRows_of_cut`) it is an
*equality* — a 2-cut leaves no crossing edge to account for separately. -/
private theorem rigidityRows_eq_union_of_isLink (F : BodyHingeFramework K k α β)
    (G₁ G₂ : Graph α β)
    (hlink : ∀ e x y, F.graph.IsLink e x y ↔ G₁.IsLink e x y ∨ G₂.IsLink e x y) :
    F.rigidityRows
      = (⟨G₁, F.supportExtensor⟩ : BodyHingeFramework K k α β).rigidityRows
        ∪ (⟨G₂, F.supportExtensor⟩ : BodyHingeFramework K k α β).rigidityRows := by
  ext φ
  constructor
  · rintro ⟨e, x, y, he, r, hr, rfl⟩
    rcases (hlink e x y).1 he with h | h
    · exact Or.inl ⟨e, x, y, h, r, hr, rfl⟩
    · exact Or.inr ⟨e, x, y, h, r, hr, rfl⟩
  · rintro (⟨e, x, y, he, r, hr, rfl⟩ | ⟨e, x, y, he, r, hr, rfl⟩)
    · exact ⟨e, x, y, (hlink e x y).2 (Or.inl he), r, hr, rfl⟩
    · exact ⟨e, x, y, (hlink e x y).2 (Or.inr he), r, hr, rfl⟩

/-- **Link-separating vertex sets give link-partitioning induced sides**: if every link of `G` has
both ends in `V₁` or both in `V₂`, its links are those of `G[V₁]` together with those of
`G[V₂]` (`Graph.induce_isLink`). -/
private theorem isLink_iff_induce_or_induce {G : Graph α β} {V₁ V₂ : Set α}
    (hsep : ∀ e x y, G.IsLink e x y → (x ∈ V₁ ∧ y ∈ V₁) ∨ (x ∈ V₂ ∧ y ∈ V₂)) (e : β) (x y : α) :
    G.IsLink e x y ↔ (G.induce V₁).IsLink e x y ∨ (G.induce V₂).IsLink e x y := by
  refine ⟨fun he => ?_, fun he => ?_⟩
  · rcases hsep e x y he with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact Or.inl ⟨he, hx, hy⟩
    · exact Or.inr ⟨he, hx, hy⟩
  · rcases he with he | he <;> exact he.1

/-- **B5′: the two sides of a 2-cut meet exactly in the joint rows of their joined relative-screw
spaces** (C1′ of `notes/pencil/workbook/attack-smark.md` §§ S10(ii), S14(i)): let every link of
`G₁` lie inside `V₁` and every link of `G₂` inside `V₂`, with `V₁ ∩ V₂ ⊆ {u, v}` and `u ≠ v`. Then

  `span (⟨G₁, C⟩).rigidityRows ⊓ span (⟨G₂, C⟩).rigidityRows = span (jointRows (ρ̄₁ ⊔ ρ̄₂) u v)`,

with `ρ̄ᵢ = (⟨Gᵢ, C⟩).relScrews u v`.  Both sides are rewritten through the annihilator picture and
what is left is bookkeeping.  A functional lies in both row spans exactly when it kills `Z₁ ⊔ Z₂`
(`span_rigidityRows_eq_dualAnnihilator_infinitesimalMotions`, the only place `[Finite α]` is
needed, and `Submodule.dualAnnihilator_sup_eq`); the right-hand side is the image of
`(ρ̄₁ ⊔ ρ̄₂)^⊥ = (map (screwDiff u v) (Z₁ ⊔ Z₂))^⊥` under `(screwDiff u v).dualMap`
(`span_jointRows_eq_map_dualAnnihilator` and `Submodule.map_sup`, with the orientation flip paid
by `map_screwDiff_comm`).  The identity between the two is
`dualAnnihilator_eq_map_dualMap_screwDiff` at `W = Z₁ ⊔ Z₂`, whose one geometric input is
`mem_sup_infinitesimalMotions_of_isLink` — an assignment moving `u` and `v` alike splits across
the cut.

**Genuinely new against the landed** `le_finrank_span_rigidityRows_of_cut`, which has
vertex-*disjoint* sides and is an inequality, where this has overlapping sides and both
directions.  Unlike the combinatorial 2-cut law `Graph.deficiency_eq_of_vertexTwoCut` it needs
**no** `¬ G.Adj u v`: a cut edge `uv` contributes the *same rows* on either side, so it cannot
disturb a row-span intersection.  The sides are any two graphs, not induced subgraphs: an ear
whose ends `a, b` are adjacent has as far side the path, while the subgraph induced on the path's
bodies also contains the edge `ab` (`BodyHingeFramework.finrank_span_rigidityRows_ear_eq`). -/
theorem inf_span_rigidityRows_of_twoCut_of_isLink [Finite α] (G₁ G₂ : Graph α β)
    (C : β → ScrewSpace K k) {V₁ V₂ : Set α} {u v : α} (huv : u ≠ v)
    (h₁ : ∀ e x y, G₁.IsLink e x y → x ∈ V₁ ∧ y ∈ V₁)
    (h₂ : ∀ e x y, G₂.IsLink e x y → x ∈ V₂ ∧ y ∈ V₂)
    (hoverlap : V₁ ∩ V₂ ⊆ {u, v}) :
    Submodule.span K (⟨G₁, C⟩ : BodyHingeFramework K k α β).rigidityRows
        ⊓ Submodule.span K (⟨G₂, C⟩ : BodyHingeFramework K k α β).rigidityRows
      = Submodule.span K (jointRows
          ((⟨G₁, C⟩ : BodyHingeFramework K k α β).relScrews u v
            ⊔ (⟨G₂, C⟩ : BodyHingeFramework K k α β).relScrews u v) u v) := by
  -- The geometric input, stated before `set` abstracts the two sides.
  have hmem : ∀ S : α → ScrewSpace K k, S u = S v →
      S ∈ (⟨G₁, C⟩ : BodyHingeFramework K k α β).infinitesimalMotions
          ⊔ (⟨G₂, C⟩ : BodyHingeFramework K k α β).infinitesimalMotions :=
    fun _ hS => mem_sup_infinitesimalMotions_of_isLink G₁ G₂ C h₁ h₂ hoverlap hS
  set F₁ : BodyHingeFramework K k α β := ⟨G₁, C⟩
  set F₂ : BodyHingeFramework K k α β := ⟨G₂, C⟩
  -- Both sides become annihilators of `Z₁ ⊔ Z₂`, resp. of its image under `screwDiff u v`.
  rw [F₁.span_rigidityRows_eq_dualAnnihilator_infinitesimalMotions,
    F₂.span_rigidityRows_eq_dualAnnihilator_infinitesimalMotions,
    ← Submodule.dualAnnihilator_sup_eq, span_jointRows_eq_map_dualAnnihilator,
    relScrews, relScrews, map_screwDiff_comm F₁.infinitesimalMotions u v,
    map_screwDiff_comm F₂.infinitesimalMotions u v, ← Submodule.map_sup]
  refine dualAnnihilator_eq_map_dualMap_screwDiff huv _ ?_
  intro S hS
  rw [LinearMap.mem_ker, screwDiff_apply, sub_eq_zero] at hS
  exact hmem S hS

/-- **B6′: gluing ranks at a 2-cut** (C1 of `notes/pencil/workbook/attack-smark.md` § S10(ii)):
let the links of `F.graph` be exactly those of `G₁` together with those of `G₂`, every link of
`Gᵢ` inside `Vᵢ`, with `V₁ ∩ V₂ ⊆ {u, v}` and `u ≠ v`. Then, at `F`'s hinges,

  `rank(G) = rank(G₁) + rank(G₂) + dim (ρ̄₁ ⊔ ρ̄₂) − screwDim k`,

an identity in `ℤ` between rigidity-row-span dimensions (`rank = finrank (span rigidityRows)`,
`ρ̄ᵢ = (⟨Gᵢ, F.supportExtensor⟩).relScrews u v`).  It is the dimension formula
`Submodule.finrank_sup_add_finrank_inf_eq` over the two side spans: their **join** is the whole
row span (`rigidityRows_eq_union_of_isLink` with `Submodule.span_union` — the one place `hlink` is
used), and their **meet** is the joint of the joined relative-screw spaces (B5′,
`inf_span_rigidityRows_of_twoCut_of_isLink`), of dimension `screwDim k − dim (ρ̄₁ ⊔ ρ̄₂)` by the
joint count `finrank_span_jointRows` at the same `u ≠ v`.  So the two sides share exactly the
`screwDim k` weld-type rows that the cut pair's relative screws do not already annihilate, and
that overlap is what the `− screwDim k` corrects for.

The `ℤ` statement (unlike B4's `ℕ`) is what makes the right-hand side a genuine difference; the
`ℕ` subtraction inside the proof never truncates, `dim (ρ̄₁ ⊔ ρ̄₂) ≤ screwDim k` being handed to
`omega` explicitly — the `weldedRank_eq` skeleton.  No covering of `V(F.graph)` by the sides is
needed: vertices outside both sides carry no rows. -/
theorem finrank_span_rigidityRows_twoCut_eq_of_isLink [Finite α]
    (F : BodyHingeFramework K k α β) (G₁ G₂ : Graph α β) {V₁ V₂ : Set α} {u v : α}
    (huv : u ≠ v)
    (h₁ : ∀ e x y, G₁.IsLink e x y → x ∈ V₁ ∧ y ∈ V₁)
    (h₂ : ∀ e x y, G₂.IsLink e x y → x ∈ V₂ ∧ y ∈ V₂)
    (hoverlap : V₁ ∩ V₂ ⊆ {u, v})
    (hlink : ∀ e x y, F.graph.IsLink e x y ↔ G₁.IsLink e x y ∨ G₂.IsLink e x y) :
    (Module.finrank K ↥(Submodule.span K F.rigidityRows) : ℤ)
      = (Module.finrank K ↥(Submodule.span K
            (⟨G₁, F.supportExtensor⟩ : BodyHingeFramework K k α β).rigidityRows) : ℤ)
        + (Module.finrank K ↥(Submodule.span K
            (⟨G₂, F.supportExtensor⟩ : BodyHingeFramework K k α β).rigidityRows) : ℤ)
        + (Module.finrank K ↥((⟨G₁, F.supportExtensor⟩ :
              BodyHingeFramework K k α β).relScrews u v
            ⊔ (⟨G₂, F.supportExtensor⟩ : BodyHingeFramework K k α β).relScrews u v) : ℤ)
        - (screwDim k : ℤ) := by
  -- Both inputs are stated before `set` abstracts the two sides.
  have hkey := inf_span_rigidityRows_of_twoCut_of_isLink G₁ G₂ F.supportExtensor huv h₁ h₂
    hoverlap
  have hrows := F.rigidityRows_eq_union_of_isLink G₁ G₂ hlink
  set F₁ : BodyHingeFramework K k α β := ⟨G₁, F.supportExtensor⟩
  set F₂ : BodyHingeFramework K k α β := ⟨G₂, F.supportExtensor⟩
  -- `dim (P ⊔ Q) + dim (P ⊓ Q) = dim P + dim Q`, with the meet counted by B5′ + the joint count.
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span K F₁.rigidityRows) (Submodule.span K F₂.rigidityRows)
  rw [hkey, finrank_span_jointRows huv] at hsup
  rw [hrows, Submodule.span_union]
  have hle : Module.finrank K ↥(F₁.relScrews u v ⊔ F₂.relScrews u v) ≤ screwDim k := by
    have h := Submodule.finrank_le (F₁.relScrews u v ⊔ F₂.relScrews u v)
    rwa [screwSpace_finrank] at h
  omega

/-- **B5: the two sides of a vertex 2-cut meet exactly in the joint rows of their joined
relative-screw spaces** (Layer B5): for `u ≠ v` and sides overlapping exactly in the cut pair
(`V₁ ∩ V₂ = {u, v}`),

  `span (F[V₁]).rigidityRows ⊓ span (F[V₂]).rigidityRows = span (jointRows (ρ̄₁ ⊔ ρ̄₂) u v)`,

with `ρ̄ᵢ = (F[Vᵢ]).relScrews u v`.  It is B5′ (`inf_span_rigidityRows_of_twoCut_of_isLink`) at
the induced sides `G[V₁]`, `G[V₂]`, whose links lie in `V₁`, `V₂` by definition.  Of `hoverlap`
only the `⊆` half is consumed, and neither the covering `V₁ ∪ V₂ = V(F.graph)` nor the edge
separation is needed; nor is `¬ G.Adj u v`. -/
theorem inf_span_rigidityRows_of_vertexTwoCut [Finite α]
    (F : BodyHingeFramework K k α β) {V₁ V₂ : Set α} {u v : α} (huv : u ≠ v)
    (hoverlap : V₁ ∩ V₂ = {u, v}) :
    Submodule.span K (⟨F.graph.induce V₁, F.supportExtensor⟩ :
          BodyHingeFramework K k α β).rigidityRows
        ⊓ Submodule.span K (⟨F.graph.induce V₂, F.supportExtensor⟩ :
          BodyHingeFramework K k α β).rigidityRows
      = Submodule.span K (jointRows
          ((⟨F.graph.induce V₁, F.supportExtensor⟩ :
              BodyHingeFramework K k α β).relScrews u v
            ⊔ (⟨F.graph.induce V₂, F.supportExtensor⟩ :
              BodyHingeFramework K k α β).relScrews u v) u v) :=
  inf_span_rigidityRows_of_twoCut_of_isLink _ _ _ huv (fun _ _ _ he => he.2)
    (fun _ _ _ he => he.2) hoverlap.le

/-- **B6: gluing ranks at a vertex 2-cut** (Layer B6): for `u ≠ v`, sides overlapping exactly in
the cut pair and every link internal to one side,

  `rank(G) = rank(G[V₁]) + rank(G[V₂]) + dim (ρ̄₁ ⊔ ρ̄₂) − screwDim k`,

in `ℤ`, with `ρ̄ᵢ = (F[Vᵢ]).relScrews u v`.  It is B6′
(`finrank_span_rigidityRows_twoCut_eq_of_isLink`) at the induced sides, whose links partition
`F.graph`'s by `hsep`.  The covering `V₁ ∪ V₂ = V(F.graph)` is not needed.

This is the linear-algebraic half of S10(ii)'s attainment criterion, whose combinatorial half is
`Graph.deficiency_eq_of_vertexTwoCut'`; Layer C's `pencilLoss_vertexTwoCut` differences the two. -/
theorem finrank_span_rigidityRows_vertexTwoCut_eq [Finite α]
    (F : BodyHingeFramework K k α β) {V₁ V₂ : Set α} {u v : α} (huv : u ≠ v)
    (hoverlap : V₁ ∩ V₂ = {u, v})
    (hsep : ∀ e x y, F.graph.IsLink e x y → (x ∈ V₁ ∧ y ∈ V₁) ∨ (x ∈ V₂ ∧ y ∈ V₂)) :
    (Module.finrank K ↥(Submodule.span K F.rigidityRows) : ℤ)
      = (Module.finrank K ↥(Submodule.span K (⟨F.graph.induce V₁, F.supportExtensor⟩ :
            BodyHingeFramework K k α β).rigidityRows) : ℤ)
        + (Module.finrank K ↥(Submodule.span K (⟨F.graph.induce V₂, F.supportExtensor⟩ :
            BodyHingeFramework K k α β).rigidityRows) : ℤ)
        + (Module.finrank K ↥((⟨F.graph.induce V₁, F.supportExtensor⟩ :
              BodyHingeFramework K k α β).relScrews u v
            ⊔ (⟨F.graph.induce V₂, F.supportExtensor⟩ :
              BodyHingeFramework K k α β).relScrews u v) : ℤ)
        - (screwDim k : ℤ) :=
  F.finrank_span_rigidityRows_twoCut_eq_of_isLink _ _ huv (fun _ _ _ he => he.2)
    (fun _ _ _ he => he.2) hoverlap.le (isLink_iff_induce_or_induce hsep)

/-- **Ranks add at a cut vertex** (`lem:block-rank-cut-vertex`; Phase 40e, informal (MC-52)(ii)):
for sides overlapping in at most one body `v` and every link internal to one side,

  `rank(G) = rank(G[V₁]) + rank(G[V₂])`,

at every body-hinge framework.  It is the gluing identity above with the cut pair collapsed to
`u = v`, where no relative screw survives: the two side row spans meet in `0`, since every screw
assignment is a motion of one side plus a motion of the other
(`mem_sup_infinitesimalMotions_of_isLink` at `u = v`, where its `S u = S v` is `rfl`), and a row
span is the annihilator of its motions. The join is the whole row span
(`rigidityRows_eq_union_of_isLink`), so the dimensions add. -/
theorem finrank_span_rigidityRows_cutVertex_eq [Finite α]
    (F : BodyHingeFramework K k α β) {V₁ V₂ : Set α} {v : α} (hoverlap : V₁ ∩ V₂ ⊆ {v})
    (hsep : ∀ e x y, F.graph.IsLink e x y → (x ∈ V₁ ∧ y ∈ V₁) ∨ (x ∈ V₂ ∧ y ∈ V₂)) :
    Module.finrank K (Submodule.span K F.rigidityRows)
      = Module.finrank K (Submodule.span K (⟨F.graph.induce V₁, F.supportExtensor⟩ :
          BodyHingeFramework K k α β).rigidityRows)
        + Module.finrank K (Submodule.span K (⟨F.graph.induce V₂, F.supportExtensor⟩ :
          BodyHingeFramework K k α β).rigidityRows) := by
  -- Both inputs are stated before `set` abstracts the two sides.
  have hmem : ∀ S : α → ScrewSpace K k,
      S ∈ (⟨F.graph.induce V₁, F.supportExtensor⟩ :
            BodyHingeFramework K k α β).infinitesimalMotions
          ⊔ (⟨F.graph.induce V₂, F.supportExtensor⟩ :
            BodyHingeFramework K k α β).infinitesimalMotions :=
    fun _ => mem_sup_infinitesimalMotions_of_isLink (F.graph.induce V₁) (F.graph.induce V₂)
      F.supportExtensor (u := v) (v := v) (fun _ _ _ he => he.2) (fun _ _ _ he => he.2)
      (by rwa [Set.pair_eq_singleton]) rfl
  have hrows := F.rigidityRows_eq_union_of_isLink _ _ (isLink_iff_induce_or_induce hsep)
  set F₁ : BodyHingeFramework K k α β := ⟨F.graph.induce V₁, F.supportExtensor⟩
  set F₂ : BodyHingeFramework K k α β := ⟨F.graph.induce V₂, F.supportExtensor⟩
  have hinf : Submodule.span K F₁.rigidityRows ⊓ Submodule.span K F₂.rigidityRows = ⊥ := by
    rw [F₁.span_rigidityRows_eq_dualAnnihilator_infinitesimalMotions,
      F₂.span_rigidityRows_eq_dualAnnihilator_infinitesimalMotions,
      ← Submodule.dualAnnihilator_sup_eq, Submodule.eq_top_iff'.mpr hmem,
      Submodule.dualAnnihilator_top]
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span K F₁.rigidityRows) (Submodule.span K F₂.rigidityRows)
  rw [hinf, finrank_bot, add_zero] at hsup
  rw [hrows, Submodule.span_union, hsup]

end TwoCutCarriers

end BodyHingeFramework

end CombinatorialRigidity.Molecular
