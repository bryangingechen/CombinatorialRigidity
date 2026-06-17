/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.RigidityMatrix

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

These depend only on the core `BodyHingeFramework` API in `RigidityMatrix.lean`; nothing in the
core depends on them (they were the file's tail), so this is a clean forward-dependency leaf.
This split is rename-free — every declaration keeps its `CombinatorialRigidity.Molecular`
namespace, so the blueprint `\lean{…}` pins and `checkdecls` are unaffected.
-/

public section

namespace CombinatorialRigidity.Molecular

open scoped Matrix

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
    (α → ScrewSpace k) →ₗ[ℝ] (α → ScrewSpace k) where
  toFun S a := if a ∈ V₁ then S a else 0
  map_add' S T := by ext a; simp [ite_add_ite]
  map_smul' c S := by ext a; simp [smul_ite]

@[simp]
private lemma zeroOutsideV₁_mem (V₁ : Set α) (S : α → ScrewSpace k) {a : α} (ha : a ∈ V₁) :
    zeroOutsideV₁ V₁ S a = S a := if_pos ha

@[simp]
private lemma zeroOutsideV₁_not_mem (V₁ : Set α) (S : α → ScrewSpace k) {a : α} (ha : a ∉ V₁) :
    zeroOutsideV₁ V₁ S a = 0 := if_neg ha

/-- A hinge row with both endpoints in `V₁` commutes with the V₁-projection: the row value
is unchanged when the screw assignment is zeroed outside `V₁`. -/
private lemma hingeRow_comp_zeroOutsideV₁ (V₁ : Set α) {u v : α} (hu : u ∈ V₁) (hv : v ∈ V₁)
    (r : Module.Dual ℝ (ScrewSpace k)) :
    (hingeRow (k := k) (α := α) u v r).comp (zeroOutsideV₁ V₁) = hingeRow u v r := by
  ext S
  simp [hingeRow_apply, zeroOutsideV₁_mem V₁ S hu, zeroOutsideV₁_mem V₁ S hv]

/-- A hinge row with both endpoints outside `V₁` vanishes at any V₁-projection output. -/
private lemma hingeRow_comp_zeroOutsideV₁_of_not_mem (V₁ : Set α) {u v : α}
    (hu : u ∉ V₁) (hv : v ∉ V₁) (r : Module.Dual ℝ (ScrewSpace k)) :
    (hingeRow (k := k) (α := α) u v r).comp (zeroOutsideV₁ V₁) = 0 := by
  ext S
  simp [hingeRow_apply, zeroOutsideV₁_not_mem V₁ S hu, zeroOutsideV₁_not_mem V₁ S hv]

/-- Every element of the V₁-side rigidity-row span commutes with the V₁-projection: for
`φ ∈ span(F[V₁].rigidityRows)`, `φ(zeroOutsideV₁ S) = φ(S)` for all `S`. -/
private lemma mem_span_rigidityRows_induce_comp_zeroOutsideV₁ {F : BodyHingeFramework k α β}
    {V₁ : Set α} {φ : Module.Dual ℝ (α → ScrewSpace k)}
    (hφ : φ ∈ Submodule.span ℝ (⟨F.graph.induce V₁, F.supportExtensor⟩ :
      BodyHingeFramework k α β).rigidityRows) :
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
    {F : BodyHingeFramework k α β} {V₁ : Set α} {φ : Module.Dual ℝ (α → ScrewSpace k)}
    (hφ : φ ∈ Submodule.span ℝ (⟨F.graph.induce (V(F.graph) \ V₁), F.supportExtensor⟩ :
      BodyHingeFramework k α β).rigidityRows) :
    φ.comp (zeroOutsideV₁ V₁) = 0 := by
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨e, u, v, he, r, _, rfl⟩ := hφ
    simp only [Graph.induce_isLink, Set.mem_diff] at he
    exact hingeRow_comp_zeroOutsideV₁_of_not_mem V₁ he.2.1.2 he.2.2.2 r
  | zero => ext; simp
  | add x y _ _ hx hy =>
    rw [LinearMap.add_comp, hx, hy, add_zero]
  | smul a x _ hx =>
    rw [LinearMap.smul_comp, hx, smul_zero]

/-- **The two side spans are disjoint**: `span(F[V₁].rigidityRows) ⊓ span(F[V₂].rigidityRows) = ⊥`.
The V₁-projection commutes with span(F[V₁]) (side-1 rows read only V₁) and annihilates
span(F[V₂]) (side-2 rows read only V₂ = V(G) ∖ V₁); any element in the intersection is both
fixed by and annihilated by the projection, hence zero. -/
theorem span_rigidityRows_induce_inf_eq_bot {F : BodyHingeFramework k α β} (V₁ : Set α) :
    Submodule.span ℝ (⟨F.graph.induce V₁, F.supportExtensor⟩ :
        BodyHingeFramework k α β).rigidityRows ⊓
    Submodule.span ℝ (⟨F.graph.induce (V(F.graph) \ V₁), F.supportExtensor⟩ :
        BodyHingeFramework k α β).rigidityRows = ⊥ := by
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
`Module.Dual ℝ (α → ScrewSpace k)` to `Module.Dual ℝ (ScrewSpace k)`. Used to separate
the cut-block span from the join of the two side spans: S₁ and S₂ rows give `Φ = 0` (flow
sums cancel / V₂-bodies vanish), but a cut row `hingeRow u v r` with `u ∈ V₁, v ∉ V₁`
gives `Φ = r`. -/
private noncomputable def flowSum [Fintype α] (V₁ : Set α) :
    Module.Dual ℝ (α → ScrewSpace k) →ₗ[ℝ] Module.Dual ℝ (ScrewSpace k) where
  toFun φ := ∑ w ∈ V₁.toFinset, φ.comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) w)
  map_add' φ ψ := by
    simp [Finset.sum_add_distrib, LinearMap.add_comp]
  map_smul' c φ := by
    simp [Finset.smul_sum, LinearMap.smul_comp]

private lemma flowSum_hingeRow_both_mem [Fintype α] {V₁ : Set α}
    {u v : α} (hu : u ∈ V₁) (hv : v ∈ V₁)
    (r : Module.Dual ℝ (ScrewSpace k)) :
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
  have hsu : ∑ w ∈ V₁.toFinset, r ((Pi.single w y : α → ScrewSpace k) u) = r y := by
    rw [Finset.sum_eq_single u
      (fun w _ hwu => by simp [Pi.single_eq_of_ne (Ne.symm hwu)])
      (fun hu' => absurd (Set.mem_toFinset.mpr hu) hu')]
    simp [Pi.single_eq_same]
  -- ∑_{w ∈ V₁.toFinset} r ((single w y) v) = r y (only w=v contributes)
  have hsv : ∑ w ∈ V₁.toFinset, r ((Pi.single w y : α → ScrewSpace k) v) = r y := by
    rw [Finset.sum_eq_single v
      (fun w _ hwv => by simp [Pi.single_eq_of_ne (Ne.symm hwv)])
      (fun hv' => absurd (Set.mem_toFinset.mpr hv) hv')]
    simp [Pi.single_eq_same]
  rw [hsu, hsv, sub_self]

private lemma flowSum_hingeRow_both_not_mem [Fintype α] {V₁ : Set α}
    {u v : α} (hu : u ∉ V₁) (hv : v ∉ V₁) (r : Module.Dual ℝ (ScrewSpace k)) :
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
    {u v : α} (hu : u ∈ V₁) (hv : v ∉ V₁) (r : Module.Dual ℝ (ScrewSpace k)) :
    flowSum V₁ (hingeRow (k := k) (α := α) u v r) = r := by
  simp only [flowSum, LinearMap.coe_mk, AddHom.coe_mk]
  -- The sum over V₁.toFinset collapses to the w = u term (all other terms are 0):
  -- • w = u: (single u x) u = x, (single u x) v = 0 (since v ≠ u, as v ∉ V₁, u ∈ V₁)
  --   → hingeRow u v r applied to (single u x) = r (x - 0) = r x.
  -- • w ≠ u, w ∈ V₁: (single w x) u = 0, (single w x) v = 0 (v ∉ V₁ so w ≠ v)
  --   → r (0 - 0) = 0.
  rw [Finset.sum_eq_single (f := fun w => (hingeRow (k := k) (α := α) u v r).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) w))
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
    {F : BodyHingeFramework k α β} {V₁ : Set α}
    {φ : Module.Dual ℝ (α → ScrewSpace k)}
    (hφ : φ ∈ Submodule.span ℝ (⟨F.graph.induce V₁, F.supportExtensor⟩ :
      BodyHingeFramework k α β).rigidityRows) :
    flowSum V₁ φ = 0 := by
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨e, u, v, he, r, _, rfl⟩ := hφ
    simp only [Graph.induce_isLink] at he
    exact flowSum_hingeRow_both_mem he.2.1 he.2.2 r
  | zero => simp only [map_zero]
  | add x y _ _ hx hy =>
    rw [map_add, hx, hy, add_zero]
  | smul a x _ hx =>
    rw [map_smul, hx, smul_zero]

/-- The flow sum annihilates every element of the V₂-side span. -/
private lemma flowSum_mem_span_induce_V₂_eq_zero [Fintype α]
    {F : BodyHingeFramework k α β} {V₁ : Set α}
    {φ : Module.Dual ℝ (α → ScrewSpace k)}
    (hφ : φ ∈ Submodule.span ℝ (⟨F.graph.induce (V(F.graph) \ V₁), F.supportExtensor⟩ :
      BodyHingeFramework k α β).rigidityRows) :
    flowSum V₁ φ = 0 := by
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨e, u, v, he, r, _, rfl⟩ := hφ
    simp only [Graph.induce_isLink, Set.mem_diff] at he
    exact flowSum_hingeRow_both_not_mem he.2.1.2 he.2.2.2 r
  | zero => simp only [map_zero]
  | add x y _ _ hx hy =>
    rw [map_add, hx, hy, add_zero]
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
theorem le_finrank_span_rigidityRows_of_cut [Finite α] [Finite β]
    (F : BodyHingeFramework k α β) {V₁ : Set α} {C : Set β}
    (hC_ncard : C.ncard ≤ 1)
    (hC_ext : ∀ e u v, F.graph.IsLink e u v → F.supportExtensor e ≠ 0)
    (_hE₁ : ∀ e u v, F.graph.IsLink e u v → e ∉ C →
      u ∈ V₁ ∧ v ∈ V₁ ∨ u ∉ V₁ ∧ v ∉ V₁)
    (hcut_mem : ∀ e ∈ C, ∃ u v, F.graph.IsLink e u v ∧ u ∈ V₁ ∧ v ∉ V₁) :
    Module.finrank ℝ (Submodule.span ℝ
        (⟨F.graph.induce V₁, F.supportExtensor⟩ : BodyHingeFramework k α β).rigidityRows) +
      (screwDim k - 1) * C.ncard +
      Module.finrank ℝ (Submodule.span ℝ
        (⟨F.graph.induce (V(F.graph) \ V₁), F.supportExtensor⟩ :
          BodyHingeFramework k α β).rigidityRows) ≤
    Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  haveI : Fintype β := Fintype.ofFinite β
  set F₁ : BodyHingeFramework k α β := ⟨F.graph.induce V₁, F.supportExtensor⟩
  set F₂ : BodyHingeFramework k α β := ⟨F.graph.induce (V(F.graph) \ V₁), F.supportExtensor⟩
  set S₁ := Submodule.span ℝ F₁.rigidityRows
  set S₂ := Submodule.span ℝ F₂.rigidityRows
  set S := Submodule.span ℝ F.rigidityRows
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
    calc Module.finrank ℝ ↥S₁ + Module.finrank ℝ ↥S₂
        = Module.finrank ℝ ↥(S₁ ⊔ S₂) := hstep.symm
      _ ≤ Module.finrank ℝ ↥S := Submodule.finrank_mono (sup_le hS₁S hS₂S)
  · -- Connected case: |C| = 1. The cut block contributes screwDim k - 1.
    -- Get the unique cut edge and its endpoint data.
    have hcut_eq : C.ncard = 1 := Nat.le_antisymm hC_ncard hpos
    -- The cut block: span of hingeRows at the cut edge.
    obtain ⟨e_cut, he_cut_eq⟩ := Set.ncard_eq_one.mp hcut_eq
    obtain ⟨u₀, v₀, hl_cut, hu₀, hv₀⟩ := hcut_mem e_cut (he_cut_eq ▸ Set.mem_singleton e_cut)
    have huv₀ : u₀ ≠ v₀ := fun h => hv₀ (h ▸ hu₀)
    -- The cut hinge rows span a (D-1)-dimensional subspace.
    set Sc := Submodule.span ℝ {φ | ∃ r ∈ F.hingeRowBlock e_cut,
      φ = hingeRow (k := k) (α := α) u₀ v₀ r}
    -- finrank(Sc) = screwDim k - 1.
    have hCcut : F.supportExtensor e_cut ≠ 0 := hC_ext e_cut u₀ v₀ hl_cut
    have hSc_rk : Module.finrank ℝ Sc = screwDim k - 1 := by
      have hfin := finrank_hingeRowBlock F hCcut
      -- Sc = image of hingeRow u₀ v₀ (·) applied to hingeRowBlock e_cut
      have heq : Sc = (F.hingeRowBlock e_cut).map
          ((screwDiff (k := k) (α := α) u₀ v₀).dualMap) := by
        simp only [Sc, hingeRow_eq_dualMap]
        -- {φ | ∃ r ∈ hingeRowBlock, φ = dualMap r} = dualMap '' ↑hingeRowBlock
        -- then span (dualMap '' hingeRowBlock) = (span hingeRowBlock).map dualMap
        -- = hingeRowBlock.map dualMap
        have hset : {φ : Module.Dual ℝ (α → ScrewSpace k) | ∃ r ∈ F.hingeRowBlock e_cut,
            φ = (screwDiff u₀ v₀).dualMap r} =
            (screwDiff (k := k) (α := α) u₀ v₀).dualMap '' ↑(F.hingeRowBlock e_cut) := by
          ext ψ
          simp only [Set.mem_setOf_eq, Set.mem_image]
          exact ⟨fun ⟨r, hr, h⟩ => ⟨r, hr, h.symm⟩,
                 fun ⟨r, hr, h⟩ => ⟨r, hr, h.symm⟩⟩
        rw [hset, Submodule.span_image, Submodule.span_eq]
      have hinj : Function.Injective (screwDiff (k := k) (α := α) u₀ v₀).dualMap :=
        LinearMap.dualMap_injective_of_surjective (screwDiff_surjective huv₀)
      -- finrank(Sc) = finrank(image of injective map) = finrank(hingeRowBlock) = D-1
      have hinj_comp : Function.Injective
          ⇑((screwDiff (k := k) (α := α) u₀ v₀).dualMap.comp (F.hingeRowBlock e_cut).subtype) :=
        hinj.comp Subtype.coe_injective
      have hrk : Module.finrank ℝ ↥((F.hingeRowBlock e_cut).map
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
    have step1 : Module.finrank ℝ ↥(S₁ ⊔ S₂) = Module.finrank ℝ ↥S₁ + Module.finrank ℝ ↥S₂ :=
      Submodule.finrank_sup_of_inf_eq_bot S₁ S₂ hdisj12
    have step2 : Module.finrank ℝ ↥(Sc ⊔ (S₁ ⊔ S₂)) =
        Module.finrank ℝ ↥Sc + Module.finrank ℝ ↥(S₁ ⊔ S₂) :=
      Submodule.finrank_sup_of_inf_eq_bot Sc (S₁ ⊔ S₂) hdisjc12
    rw [hcut_eq, Nat.mul_one]
    calc Module.finrank ℝ ↥S₁ + (screwDim k - 1) + Module.finrank ℝ ↥S₂
        = (screwDim k - 1) + Module.finrank ℝ ↥(S₁ ⊔ S₂) := by rw [step1]; ring
      _ = Module.finrank ℝ ↥(Sc ⊔ (S₁ ⊔ S₂)) := by rw [step2, hSc_rk]
      _ ≤ Module.finrank ℝ ↥S := Submodule.finrank_mono
          (sup_le hScS (sup_le hS₁S hS₂S))

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
theorem le_finrank_span_rigidityRows_of_splice [Finite α] [Finite β]
    (F FH Fc : BodyHingeFramework k α β)
    (D : Module.Dual ℝ (α → ScrewSpace k) →ₗ[ℝ] Module.Dual ℝ (α → ScrewSpace k))
    (hFH_le : Submodule.span ℝ FH.rigidityRows ≤ Submodule.span ℝ F.rigidityRows)
    (hFH_ker : Submodule.span ℝ FH.rigidityRows ≤ LinearMap.ker D)
    (hFc_surv_le : (Submodule.span ℝ Fc.rigidityRows).map D ≤
                    (Submodule.span ℝ F.rigidityRows).map D)
    (hInj : Module.finrank ℝ ↥(Submodule.span ℝ Fc.rigidityRows) =
             Module.finrank ℝ ↥((Submodule.span ℝ Fc.rigidityRows).map D)) :
    Module.finrank ℝ ↥(Submodule.span ℝ FH.rigidityRows) +
    Module.finrank ℝ ↥(Submodule.span ℝ Fc.rigidityRows) ≤
    Module.finrank ℝ ↥(Submodule.span ℝ F.rigidityRows) := by
  haveI : Fintype α := Fintype.ofFinite α
  haveI : Fintype β := Fintype.ofFinite β
  haveI : FiniteDimensional ℝ (Module.Dual ℝ (α → ScrewSpace k)) := inferInstance
  set SH := Submodule.span ℝ FH.rigidityRows with hSH_def
  set Sc := Submodule.span ℝ Fc.rigidityRows with hSc_def
  set S := Submodule.span ℝ F.rigidityRows with hS_def
  -- Rank-nullity for D restricted to S: finrank(S.map D) + finrank(S ⊓ ker D) = finrank S.
  -- Route: let N = comap S.subtype (ker D) ≤ ↥S (the kernel of D|_S inside ↥S).
  -- Quotient rank-nullity on ↥S with N gives finrank(↥S ⧸ N) + finrank N = finrank S.
  -- Then ↥S ⧸ N ≅ (D.comp S.subtype).range = S.map D via quotKerEquivRange,
  -- and finrank N = finrank(S ⊓ ker D) via finrank_map_subtype_eq + map_comap_subtype.
  have h_rn : Module.finrank ℝ ↥(S.map D) + Module.finrank ℝ ↥(S ⊓ LinearMap.ker D) =
      Module.finrank ℝ ↥S := by
    -- letI (not haveI) forces AddCommGroup ↥S to shadow the global AddCommMonoid ↥S instance,
    -- enabling Ring/AddCommGroup paths for domRestrict and finrank_quotient_add_finrank.
    letI hSAG : AddCommGroup ↥S := S.addCommGroup
    have hq : Module.finrank ℝ (↥S ⧸ (D.domRestrict S).ker) +
        Module.finrank ℝ ↥(D.domRestrict S).ker = Module.finrank ℝ ↥S :=
      (D.domRestrict S).ker.finrank_quotient_add_finrank
    have heq : Module.finrank ℝ (↥S ⧸ (D.domRestrict S).ker) =
        Module.finrank ℝ ↥(S.map D) := by
      have h := LinearEquiv.finrank_eq (D.domRestrict S).quotKerEquivRange
      rw [LinearMap.range_domRestrict] at h
      exact h
    have hker : Module.finrank ℝ ↥(D.domRestrict S).ker =
        Module.finrank ℝ ↥(S ⊓ LinearMap.ker D) := by
      rw [LinearMap.ker_domRestrict,
          ← Submodule.finrank_map_subtype_eq S (Submodule.comap S.subtype (LinearMap.ker D)),
          Submodule.map_comap_subtype]
    linarith
  -- SH ≤ S ⊓ ker D, so finrank SH ≤ finrank(S ⊓ ker D).
  have h_SH_le_inf : SH ≤ S ⊓ LinearMap.ker D := le_inf hFH_le hFH_ker
  have h_SH_le : Module.finrank ℝ ↥SH ≤ Module.finrank ℝ ↥(S ⊓ LinearMap.ker D) :=
    Submodule.finrank_mono h_SH_le_inf
  -- Sc.map D ≤ S.map D, so finrank Sc ≤ finrank(S.map D).
  have h_Sc_le : Module.finrank ℝ ↥Sc ≤ Module.finrank ℝ ↥(S.map D) :=
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
a body `v`, a **new block** of functionals `rn : ιn → Module.Dual ℝ (α → ScrewSpace k)` independent
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
theorem le_finrank_span_rigidityRows_of_pinned_placement [Finite α] [Finite β]
    [DecidableEq α] {ιn ιo : Type*} [Finite ιn] [Finite ιo] (F : BodyHingeFramework k α β) {v : α}
    {rn : ιn → Module.Dual ℝ (α → ScrewSpace k)} {ro : ιo → Module.Dual ℝ (α → ScrewSpace k)}
    (hold : ∀ (j : ιo) (x : ScrewSpace k),
      ro j (Function.update (0 : α → ScrewSpace k) v x) = 0)
    (hnewpin : LinearIndependent ℝ
      (fun i : ιn => (rn i).comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v)))
    (holdindep : LinearIndependent ℝ ro)
    (hnew_span : ∀ i : ιn, rn i ∈ Submodule.span ℝ F.rigidityRows)
    (hold_span : ∀ j : ιo, ro j ∈ Submodule.span ℝ F.rigidityRows) :
    Nat.card ιn + Nat.card ιo ≤ Module.finrank ℝ ↥(Submodule.span ℝ F.rigidityRows) := by
  haveI : Fintype α := Fintype.ofFinite α
  haveI : Fintype ιn := Fintype.ofFinite ιn
  haveI : Fintype ιo := Fintype.ofFinite ιo
  -- The combined family `Sum.elim rn ro` is independent by the pin-a-body block split.
  have hunion : LinearIndependent ℝ (Sum.elim rn ro) :=
    linearIndependent_sum_pinned_block (v := v) hold hnewpin holdindep
  -- Its span lies in `span F.rigidityRows` (both blocks are span members).
  have hcomb_le : Submodule.span ℝ (Set.range (Sum.elim rn ro)) ≤
      Submodule.span ℝ F.rigidityRows := by
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
theorem le_finrank_span_rigidityRows_of_pinned_placement_augment [Finite α] [Finite β]
    [DecidableEq α] {ιn ιo : Type*} [Finite ιn] [Finite ιo] (F : BodyHingeFramework k α β) {v : α}
    {rn : ιn → Module.Dual ℝ (α → ScrewSpace k)} {ro : ιo → Module.Dual ℝ (α → ScrewSpace k)}
    {w : Module.Dual ℝ (α → ScrewSpace k)}
    (hold : ∀ (j : ιo) (x : ScrewSpace k),
      ro j (Function.update (0 : α → ScrewSpace k) v x) = 0)
    (hnewpinaug : LinearIndependent ℝ (Sum.elim
      (fun i : ιn => (rn i).comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v))
      (fun _ : Unit => w.comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v))))
    (holdindep : LinearIndependent ℝ ro)
    (hnew_span : ∀ i : ιn, rn i ∈ Submodule.span ℝ F.rigidityRows)
    (hw_span : w ∈ Submodule.span ℝ F.rigidityRows)
    (hold_span : ∀ j : ιo, ro j ∈ Submodule.span ℝ F.rigidityRows) :
    Nat.card ιn + 1 + Nat.card ιo ≤ Module.finrank ℝ ↥(Submodule.span ℝ F.rigidityRows) := by
  haveI : Fintype α := Fintype.ofFinite α
  haveI : Fintype ιn := Fintype.ofFinite ιn
  haveI : Fintype ιo := Fintype.ofFinite ιo
  -- The augmented combined family is independent by the augmented pin-a-body split.
  have hunion : LinearIndependent ℝ (Sum.elim (Sum.elim rn (fun _ : Unit => w)) ro) :=
    linearIndependent_sum_pinned_block_augment (v := v) hold hnewpinaug holdindep
  -- Its span lies in `span F.rigidityRows` (`rn`, `w`, and `ro` are all span members).
  have hcomb_le : Submodule.span ℝ
      (Set.range (Sum.elim (Sum.elim rn (fun _ : Unit => w)) ro)) ≤
      Submodule.span ℝ F.rigidityRows := by
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

end BodyHingeFramework

end CombinatorialRigidity.Molecular
