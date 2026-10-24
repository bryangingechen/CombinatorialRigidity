/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.RigidityMatrix.Basic

/-!
# Rank-addition lemmas for body-hinge frameworks

The rank-addition lemmas of `sec:molecular-rigidity-matrix-blocks`, which compute or bound the rank
of `R(G,p)` from the ranks of pieces of `G`; the rank is the dimension of the row space
`span F.rigidityRows`. The file proves:

* rank addition at a cut edge, from the proof of Katoh and Tanigawa's Lemma 6.1 (2011, *A proof of
  the molecular conjecture*, Discrete Comput. Geom. **45**, p. 672; `lem:block-rank-cut`), and the
  bound `rank R(G',p) ≤ rank R(G_s,p) + D − 1` when `G'` has one edge more than `G_s`
  (`finrank_span_rigidityRows_le_add_of_links_subset`);
* block-triangular rank addition, from the proof of KT Lemma 6.2 (pp. 673–674;
  `lem:rigidityRows-splice-rank-add`), and rank addition at one body, from the proofs of KT
  Lemmas 6.8 and 6.10 (`lem:rigidityRows-pinned-placement-rank-add`);
* the relative screws and the joint rows of two bodies (`def:relative-screws`), and the rank of a
  framework glued from two pieces that share two bodies (`lem:block-rank-two-cut`,
  `cor:block-rank-vertex-two-cut`) or one (`lem:block-rank-cut-vertex`).

`Basic.lean` defines the rows of `R(G,p)` and proves the rank lemmas of KT §5.
-/

public section

namespace CombinatorialRigidity.Molecular

open scoped Matrix

variable {K : Type*} [Field K]

namespace BodyHingeFramework

variable {k : ℕ} {α β : Type*}

/-! ## Rank addition at a cut edge (`lem:block-rank-cut`)

Let `V₁` be a set of bodies and `V₂ = V(G) ∖ V₁`. The row spaces of `G[V₁]` and `G[V₂]` meet in `0`,
as their forms read the screws of disjoint sets of bodies (`span_rigidityRows_induce_inf_eq_bot`,
through `zeroOutsideV₁`). The rows of an edge from `V₁` to `V₂` meet the sum of the two in `0`: the
map `flowSum V₁`, `φ ↦ ∑ w ∈ V₁, φ ∘ₗ single w`, vanishes on both row spaces and recovers the form
`r` from the row `hingeRow u v r` of such an edge. -/

section CutEdgeBrick

-- `open Classical` is needed for `Decidable (a ∈ V₁)` in `zeroOutsideV₁`'s if/else, and for
-- `DecidableEq α` and `V₁.toFinset` in `flowSum`. The linter is off for the rest of the section.
set_option linter.style.openClassical false
open Classical
open scoped Graph

variable {α β : Type*} {k : ℕ}

/-- **The screw assignment zeroed outside `V₁`.** A row of `G[V₁]` takes the same value at `S` and
at `zeroOutsideV₁ V₁ S`, as it reads only bodies of `V₁`; a row of `G[V(G) ∖ V₁]` vanishes at
`zeroOutsideV₁ V₁ S`, as it reads only bodies outside `V₁`. -/
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

/-- A row whose ends both lie in `V₁` takes the same value at `S` and at `zeroOutsideV₁ V₁ S`. -/
private lemma hingeRow_comp_zeroOutsideV₁ (V₁ : Set α) {u v : α} (hu : u ∈ V₁) (hv : v ∈ V₁)
    (r : Module.Dual K (ScrewSpace K k)) :
    (hingeRow (k := k) (α := α) u v r).comp (zeroOutsideV₁ V₁) = hingeRow u v r := by
  ext S
  simp [hingeRow_apply, zeroOutsideV₁_mem V₁ S hu, zeroOutsideV₁_mem V₁ S hv]

/-- A row whose ends both lie outside `V₁` vanishes at `zeroOutsideV₁ V₁ S`. -/
private lemma hingeRow_comp_zeroOutsideV₁_of_not_mem (V₁ : Set α) {u v : α}
    (hu : u ∉ V₁) (hv : v ∉ V₁) (r : Module.Dual K (ScrewSpace K k)) :
    (hingeRow (k := k) (α := α) u v r).comp (zeroOutsideV₁ V₁) = 0 := by
  ext S
  simp [hingeRow_apply, zeroOutsideV₁_not_mem V₁ S hu, zeroOutsideV₁_not_mem V₁ S hv]

/-- Every form `φ` in the row space of `G[V₁]` has `φ ∘ₗ zeroOutsideV₁ V₁ = φ`. -/
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

/-- Every form `φ` in the row space of `G[V(G) ∖ V₁]` has `φ ∘ₗ zeroOutsideV₁ V₁ = 0`. -/
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

/-- **The row spaces of the two sides meet in `0`**: the row spaces of `G[V₁]` and of
`G[V(G) ∖ V₁]`, at the hinges of `F`, have intersection `⊥`. A form in both satisfies
`φ = φ ∘ₗ zeroOutsideV₁ V₁ = 0`. -/
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

/-- **The flow sum** `φ ↦ ∑ w ∈ V₁, φ ∘ₗ single w`, a linear map from the forms on screw assignments
to the forms on the screw space. It vanishes on the rows of edges inside `V₁` (the terms of the two
ends cancel) and on those of edges outside `V₁` (every term vanishes), and it sends the row
`hingeRow u v r` of an edge with `u ∈ V₁` and `v ∉ V₁` to `r`. -/
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

/-- The flow sum vanishes on the row space of `G[V₁]`. -/
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

/-- The flow sum vanishes on the row space of `G[V(G) ∖ V₁]`. -/
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

/-- **Rank addition at a cut edge** (`lem:block-rank-cut`; from the proof of KT Lemma 6.1, p. 672):
let `V₁` be a set of bodies, `V₂ = V(G) ∖ V₁`, and `C` a set of edges with `C.ncard ≤ 1`, each edge
of `C` linking a body of `V₁` to one outside `V₁` (`hcut_mem`), and let the supporting extensor be
nonzero at every link (`hC_ext`). Then, at the hinges of `F`,

  `rank R(G[V₁]) + (D − 1)·|C| + rank R(G[V₂]) ≤ rank R(G)`,

the ranks being the dimensions of the row spaces. The row spaces of `G[V₁]` and of `G[V₂]` meet in
`0` (`span_rigidityRows_induce_inf_eq_bot`); the rows of the edge of `C` span a space of dimension
`D − 1` (`finrank_hingeRowBlock`, and `hingeRow u v` is injective), which meets their sum in `0`
(`flowSum`); and the dimensions add (`Submodule.finrank_sup_of_inf_eq_bot`). `C` need not hold every
link from `V₁` to the rest: further links only add rows. -/
theorem le_finrank_span_rigidityRows_of_cut [Finite α]
    (F : BodyHingeFramework K k α β) {V₁ : Set α} {C : Set β}
    (hC_ncard : C.ncard ≤ 1)
    (hC_ext : ∀ e u v, F.graph.IsLink e u v → F.supportExtensor e ≠ 0)
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
  set F₁ : BodyHingeFramework K k α β := ⟨F.graph.induce V₁, F.supportExtensor⟩
  set F₂ : BodyHingeFramework K k α β := ⟨F.graph.induce (V(F.graph) \ V₁), F.supportExtensor⟩
  set S₁ := Submodule.span K F₁.rigidityRows
  set S₂ := Submodule.span K F₂.rigidityRows
  set S := Submodule.span K F.rigidityRows
  -- The rows of the edge of `C` add `0` when `C` is empty and `D − 1` when it has one edge.
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

/-- **Removing one edge lowers the rank by at most `D − 1`** (a step of `lem:block-rank-path`): if
every link of `G'` is a link of `Gs` or is the edge `e₀`, which links `u₀` and `v₀` in `G'` and has
a nonzero supporting extensor, then at the same hinges `rank R(G') ≤ rank R(Gs) + (D − 1)`.

Every row of `G'` lies in the row space of `Gs` plus the image `Sc` of the hinge-row block of `e₀`
under `hingeRow u₀ v₀` (a row of `e₀` in the other orientation is the image of the negated form,
`hingeRow_swap`), and `Sc` has dimension at most `D − 1` (`Submodule.finrank_map_le`,
`finrank_hingeRowBlock`). -/
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

/-- **A body joined by one edge adds at least `D − 1` to the rank** (`lem:block-rank-cut`, its
second claim): if `e₀` links `u₀ ∈ V₁` to `w₀ ∉ V₁` and every supporting extensor at a link of
`G` is nonzero, then at the same hinges `rank R(G[V₁]) + (D − 1) ≤ rank R(G[V₁ ∪ {w₀}])`. It is
`le_finrank_span_rigidityRows_of_cut` in `G[V₁ ∪ {w₀}]` at `V₁` with `C = {e₀}`: the side `V₁`
induces `G[V₁]`, and the rank of the side `{w₀}` is dropped.
`finrank_span_rigidityRows_le_add_of_links_subset` bounds the rank the other way, and
`Graph.deficiency_induce_union_singleton`, `def(G[V₁ ∪ {w₀}]) = def(G[V₁]) + 1`, is the counterpart
for the deficiency. -/
theorem add_le_finrank_span_rigidityRows_induce_union_singleton [Finite α]
    {G : Graph α β} (ext : β → ScrewSpace K k) {V₁ : Set α} {e₀ : β} {u₀ w₀ : α}
    (hl₀ : G.IsLink e₀ u₀ w₀) (hu₀ : u₀ ∈ V₁) (hw₀ : w₀ ∉ V₁)
    (hext : ∀ e u v, G.IsLink e u v → ext e ≠ 0) :
    Module.finrank K (Submodule.span K
        (⟨G.induce V₁, ext⟩ : BodyHingeFramework K k α β).rigidityRows) + (screwDim k - 1)
      ≤ Module.finrank K (Submodule.span K
        (⟨G.induce (V₁ ∪ {w₀}), ext⟩ : BodyHingeFramework K k α β).rigidityRows) := by
  have hbrick := le_finrank_span_rigidityRows_of_cut
    (⟨G.induce (V₁ ∪ {w₀}), ext⟩ : BodyHingeFramework K k α β) (V₁ := V₁) (C := {e₀})
    (by simp) (fun e u v hl => hext e u v hl.1) ?_
  · have hind : (G.induce (V₁ ∪ {w₀})).induce V₁ = G.induce V₁ :=
      Graph.ext rfl fun e x y => by
        simp only [Graph.induce_isLink]
        exact ⟨fun ⟨⟨hl, _, _⟩, hx, hy⟩ => ⟨hl, hx, hy⟩,
          fun ⟨hl, hx, hy⟩ => ⟨⟨hl, Or.inl hx, Or.inl hy⟩, hx, hy⟩⟩
    dsimp only at hbrick
    rw [hind, Set.ncard_singleton, Nat.mul_one] at hbrick
    omega
  · rintro e rfl
    exact ⟨u₀, w₀, ⟨hl₀, Or.inl hu₀, Or.inr rfl⟩, hu₀, hw₀⟩

end CutEdgeBrick

section SpliceBrick

variable {α β : Type*} {k : ℕ}

/-- **Block-triangular rank addition** (`lem:rigidityRows-splice-rank-add`; from the proof of KT
Lemma 6.2, eqs. (6.3)–(6.5), pp. 673–674): let `F`, `FH` and `Fc` be body-hinge frameworks with row
spaces `R`, `R_H` and `R_c`, and let `D` be a linear map from the forms on screw assignments to
themselves (`π` in the blueprint). If `R_H ≤ R` (`hFH_le`), `R_H ≤ ker D` (`hFH_ker`),
`D(R_c) ≤ D(R)` (`hFc_surv_le`) and `D` keeps the dimension of `R_c` (`hInj`), then

  `rank R(FH) + rank R(Fc) ≤ rank R(F)`.

By rank-nullity for `D` on `R`, `dim R = dim D(R) + dim (R ⊓ ker D)`; the first two hypotheses bound
the second term below by `dim R_H`, and the other two bound the first below by `dim R_c`. In Case I,
`F` realizes `G`, `FH` is its restriction to a rigid subgraph `H`, `Fc` realizes the contraction
`G/E(H)`, and `D` deletes the columns of `V(H)` (`lem:extProj-preserves-rank-of-inter`). -/
theorem le_finrank_span_rigidityRows_of_splice [Finite α]
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
    -- `let` (not `have`) puts the instance `AddCommGroup ↥S` in the context, for `domRestrict` and
    -- `Submodule.finrank_quotient_add_finrank`, which ask for an `AddCommGroup`.
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

/-- **Rank addition at one body** (`lem:rigidityRows-pinned-placement-rank-add`; from the proofs of
KT Lemmas 6.8 and 6.10): let `v` be a body, `rn` forms whose restrictions to the screw assignments
that vanish off `v` are linearly independent (`hnewpin`), and `ro` linearly independent forms that
vanish at those assignments (`hold`, `holdindep`), all in the row space of `F` (`hnew_span`,
`hold_span`). Then `|ιn| + |ιo| ≤ rank R(F)`: the forms are jointly linearly independent
(`linearIndependent_sum_pinned_block`) and lie in the row space.

The forms need not be rows of `F`. In Case II (`PanelHingeFramework.case_II_realization_all_k`), the
forms `rn` are the `D − 1` rows of an edge at `v`, and the forms `ro` rows of the graph obtained by
splitting off `v`, which lie in the row space of `R(F)` without being its rows. Katoh and Tanigawa
read such counts off block-triangular forms of the rigidity matrix (KT eqs. (6.16) and (6.29),
pp. 679 and 686). -/
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
  -- `Sum.elim rn ro` is independent (`linearIndependent_sum_pinned_block`).
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

/-- **Rank addition at one body, with one more form** (`lem:rigidityRows-pinned-placement-rank-add`,
its second claim): with `rn` and `ro` as in `le_finrank_span_rigidityRows_of_pinned_placement` and a
form `w` in the row space such that the restrictions of `rn` and `w` to the screw assignments that
vanish off `v` are linearly independent (`hnewpinaug`), `|ιn| + 1 + |ιo| ≤ rank R(F)`. The forms are
jointly linearly independent (`linearIndependent_sum_pinned_block_augment`) and lie in the row
space. -/
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
  -- The family with `w` is independent (`linearIndependent_sum_pinned_block_augment`).
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

/-! ## Relative screws, joint rows, and gluing at two bodies (`def:relative-screws`)

The relative screws `relScrews u v` of a framework, `ρ_{uv}` of `def:relative-screws`, are the
values `S v − S u` of its infinitesimal motions, and the joint rows `jointRows U u v` are the forms
`S ↦ r (S u − S v)` with `r` vanishing on `U`. At distinct bodies the joint rows span a space of
dimension `D − dim U` (`finrank_span_jointRows`).

Let `G₁` and `G₂` be graphs whose links together are those of `G`, the links of `Gᵢ` inside a set
`Vᵢ` of bodies, with `V₁ ∩ V₂ ⊆ {u, v}` and `u ≠ v`. Their row spaces meet in the span of the joint
rows that confine the relative screw to `ρ₁ + ρ₂`, where `ρᵢ` are their relative screws at `u, v`
(`inf_span_rigidityRows_of_twoCut_of_isLink`), so that

  `rank R(G) = rank R(G₁) + rank R(G₂) + dim (ρ₁ + ρ₂) − D`

(`lem:block-rank-two-cut`). At induced subgraphs this is `cor:block-rank-vertex-two-cut`, and when
the two sets share at most one body the ranks add (`lem:block-rank-cut-vertex`). `relScrews` takes
`S v − S u` and the joint rows `S u − S v`; the two orientations give the same spaces, and
`map_screwDiff_comm` is what lets the rewrites pass between them. -/

section TwoCutCarriers

/-- **The relative screws** `ρ_{uv}(G,p)` of two bodies (`def:relative-screws`): the image of the
motions `Z(G,p)` under `screwDiff v u : S ↦ S v − S u`, the screws of `v` relative to `u` that some
infinitesimal motion realizes. Two sides glued at `u` and `v` interact through them
(`lem:block-rank-two-cut`). `relScrews = ⊥` says that every motion moves `u` and `v` alike, and
`relScrews = ⊤` that every relative screw is realized by a motion. -/
@[expose] noncomputable def relScrews (F : BodyHingeFramework K k α β) (u v : α) :
    Submodule K (ScrewSpace K k) :=
  Submodule.map (screwDiff v u) F.infinitesimalMotions

/-- **The relative screws read the supporting extensors only at the links**: two hinge assignments
on `H` that agree at every link give the same relative screws at every pair of bodies, as they give
the same motions (`infinitesimalMotions_eq_of_isLink_supportExtensor`). -/
theorem relScrews_congr (H : Graph α β) {C C' : β → ScrewSpace K k}
    (h : ∀ f u w, H.IsLink f u w → C f = C' f) (a b : α) :
    (⟨H, C⟩ : BodyHingeFramework K k α β).relScrews a b =
      (⟨H, C'⟩ : BodyHingeFramework K k α β).relScrews a b := by
  have hZ : (⟨H, C⟩ : BodyHingeFramework K k α β).infinitesimalMotions =
      (⟨H, C'⟩ : BodyHingeFramework K k α β).infinitesimalMotions :=
    infinitesimalMotions_eq_of_isLink_supportExtensor _ _ rfl fun f u w hf => (h f u w hf).symm
  rw [relScrews, relScrews, hZ]

/-- **The joint rows** at bodies `u` and `v` that confine the relative screw to `U`
(`def:relative-screws`): the forms `hingeRow u v r` on screw assignments, for `r` in the annihilator
`U^⊥ = U.dualAnnihilator` of `U`. A screw assignment `S` is killed by all of them exactly when
`S u − S v ∈ U`, as `U` is the annihilator of `U^⊥` over a field. At `U = ⊥` they force `S u = S v`.
For an edge `e` from `u` to `v`, the joint rows that confine the relative screw to `span C(p(e))`
span the same space as the rows of `e`. They depend on `u`, `v` and `U` only, not on a framework. -/
noncomputable def jointRows (U : Submodule K (ScrewSpace K k)) (u v : α) :
    Set (Module.Dual K (α → ScrewSpace K k)) :=
  (fun r => hingeRow u v r) '' U.dualAnnihilator

/-- **The joint rows span the image of the annihilator under the dual map of the relative screw**:
`span (jointRows U u v) = (U.dualAnnihilator).map (screwDiff u v).dualMap`. The joint rows are the
image of the submodule `U^⊥` under `hingeRow u v = (screwDiff u v).dualMap` (`hingeRow_eq_dualMap`),
so their span is that image (`Submodule.span_image`, `Submodule.span_eq`), as in the proof of
`le_finrank_span_rigidityRows_of_cut`. `finrank_span_jointRows` and
`inf_span_rigidityRows_of_twoCut_of_isLink` use the joint rows through this lemma. Its first step,
`Set.image_congr'`, rewrites the definition's `fun r => hingeRow u v r` to
`(screwDiff u v).dualMap`, the form `Submodule.span_image` needs. -/
theorem span_jointRows_eq_map_dualAnnihilator {u v : α} (U : Submodule K (ScrewSpace K k)) :
    Submodule.span K (jointRows (α := α) U u v)
      = U.dualAnnihilator.map (screwDiff (K := K) (k := k) (α := α) u v).dualMap := by
  rw [jointRows, Set.image_congr' (fun r => hingeRow_eq_dualMap (k := k) (α := α) u v r),
    Submodule.span_image, Submodule.span_eq]

/-- **At distinct bodies the joint rows span a space of dimension `D − dim U`**: for `u ≠ v`,
`finrank (span (jointRows U u v)) = screwDim k − finrank U`.

The span is the image of `U^⊥` under `(screwDiff u v).dualMap`
(`span_jointRows_eq_map_dualAnnihilator`), which is injective as `screwDiff u v` is onto at distinct
bodies (`screwDiff_surjective`, `LinearMap.dualMap_injective_of_surjective`); and
`dim U + dim U^⊥ = D` (`Subspace.finrank_add_finrank_dualAnnihilator_eq`, `screwSpace_finrank`). The
subtraction in `ℕ` does not truncate, as `dim U ≤ D`. At `u = v` the rows all vanish
(`hingeRow_self`), and the count fails for every `U ≠ ⊤`. At `U = ⊥` the joint rows span a space of
dimension `D`. -/
theorem finrank_span_jointRows {u v : α} (huv : u ≠ v) (U : Submodule K (ScrewSpace K k)) :
    Module.finrank K (Submodule.span K (jointRows (α := α) U u v))
      = screwDim k - Module.finrank K U := by
  have hinj : Function.Injective (screwDiff (K := K) (k := k) (α := α) u v).dualMap :=
    LinearMap.dualMap_injective_of_surjective (screwDiff_surjective huv)
  -- The span is the image of `U^⊥` under an injective map, so it has the dimension of `U^⊥`.
  have hfr : Module.finrank K (Submodule.span K (jointRows (α := α) U u v))
      = Module.finrank K U.dualAnnihilator := by
    rw [span_jointRows_eq_map_dualAnnihilator,
      ← (Submodule.equivMapOfInjective _ hinj U.dualAnnihilator).finrank_eq]
  -- `dim U + dim U^⊥ = dim (ScrewSpace K k) = screwDim k`.
  have hsum := Subspace.finrank_add_finrank_dualAnnihilator_eq U
  rw [screwSpace_finrank] at hsum
  omega

/-- **The relative screws do not depend on the orientation**:
`map (screwDiff v u) Z = map (screwDiff u v) Z` for every subspace `Z` of the screw assignments, as
`screwDiff v u = −screwDiff u v` (`neg_sub`) and a subspace is closed under negation
(`Submodule.map_neg`). `relScrews` is stated with `screwDiff v u` and the joint rows with
`(screwDiff u v).dualMap`, and neither form rewrites to the other without this lemma. -/
theorem map_screwDiff_comm (Z : Submodule K (α → ScrewSpace K k)) (u v : α) :
    Submodule.map (screwDiff (K := K) (k := k) v u) Z
      = Submodule.map (screwDiff (K := K) (k := k) u v) Z := by
  have hneg : screwDiff (K := K) (k := k) (α := α) v u
      = -screwDiff (K := K) (k := k) (α := α) u v := by
    simp only [screwDiff, neg_sub]
  rw [hneg, Submodule.map_neg]

/-- **A form that vanishes on a subspace containing the kernel of the relative screw factors through
it**: for `u ≠ v` and a subspace `W` of the screw assignments with `ker (screwDiff u v) ≤ W`,

  `W.dualAnnihilator = ((W.map (screwDiff u v)).dualAnnihilator).map (screwDiff u v).dualMap`.

`⊇` needs neither hypothesis: if `r` vanishes on the image of `W`, then `r ∘ₗ screwDiff u v`
vanishes on `W`. `⊆`: a form `φ` that vanishes on `W` vanishes on `ker (screwDiff u v)`
(`Submodule.dualAnnihilator_anti`), and as `screwDiff u v` is onto (`screwDiff_surjective`), the
forms that vanish on its kernel are the range of its dual map
(`LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_surjective`); so `φ = r ∘ₗ screwDiff u v`, and
`r` vanishes on the image of `W`. In `inf_span_rigidityRows_of_twoCut_of_isLink`, `W` is the sum of
the two sides' motions, and `ker (screwDiff u v) ≤ W` is `mem_sup_infinitesimalMotions_of_isLink`.
It holds for any surjective linear map `f` and any `W ⊇ ker f`. -/
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

/-- **An assignment constant on a set that contains the ends of every link is a motion**: if every
link of `G` has both ends in `V` and `S a = c` for every `a ∈ V`, then `S` is a motion of `⟨G, C⟩`,
whatever its values off `V`: each hinge constraint reads `c − c = 0`.
`mem_sup_infinitesimalMotions_of_isLink` uses it at `c = 0` and at a general `c`. -/
theorem isInfinitesimalMotion_of_eqOn_of_isLink (G : Graph α β) (C : β → ScrewSpace K k)
    {V : Set α} (hV : ∀ e x y, G.IsLink e x y → x ∈ V ∧ y ∈ V)
    {S : α → ScrewSpace K k} {c : ScrewSpace K k} (hS : ∀ a ∈ V, S a = c) :
    (⟨G, C⟩ : BodyHingeFramework K k α β).IsInfinitesimalMotion S := by
  intro e x y he
  obtain ⟨hx, hy⟩ := hV e x y he
  rw [hingeConstraint_iff, hS x hx, hS y hy, sub_self]
  exact Submodule.zero_mem _

/-- **An assignment that moves `u` and `v` alike is a sum of motions of the two sides**: let every
link of `G₁` lie inside `V₁` and every link of `G₂` inside `V₂`, with `V₁ ∩ V₂ ⊆ {u, v}`. If
`S u = S v`, then

  `S ∈ (⟨G₁, C⟩).infinitesimalMotions ⊔ (⟨G₂, C⟩).infinitesimalMotions`.

The assignment `A a = if a ∈ V₂ then S v else S a` is constant on `V₂`, hence a motion of the second
side, and `S − A` vanishes on `V₁`: off `V₂` by its definition, and on `V₁ ∩ V₂ ⊆ {u, v}` because
`S u = S v` (`isInfinitesimalMotion_of_eqOn_of_isLink` twice). That is, `ker (screwDiff u v)` lies
in the sum of the motions, the geometric step of `inf_span_rigidityRows_of_twoCut_of_isLink`.
Neither `u ≠ v` nor any relation between `G₁` and `G₂` is used; at `u = v` it gives
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

/-- **Two graphs whose links together are those of `F.graph` split its rows**: then `F.rigidityRows`
is the union of the rows of the two graphs at the hinges of `F`. The hinge-row block reads only the
supporting extensor, which the two graphs keep. `finrank_span_rigidityRows_twoCut_eq_of_isLink`
takes the span of this union (`Submodule.span_union`). -/
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

/-- **Two sides glued at two bodies meet in joint rows** (`lem:block-rank-two-cut`, its first
claim): let every link of `G₁` lie inside `V₁` and every link of `G₂` inside `V₂`, with
`V₁ ∩ V₂ ⊆ {u, v}` and `u ≠ v`. Then

  `span (⟨G₁, C⟩).rigidityRows ⊓ span (⟨G₂, C⟩).rigidityRows = span (jointRows (ρ₁ ⊔ ρ₂) u v)`,

where `ρᵢ = (⟨Gᵢ, C⟩).relScrews u v`. For finitely many bodies a row space is the space of forms
that vanish on the motions (`span_rigidityRows_eq_dualAnnihilator_infinitesimalMotions`), so a form
lies in both row spaces exactly when it vanishes on `Z₁ ⊔ Z₂` (`Submodule.dualAnnihilator_sup_eq`).
The right side is the image of `(ρ₁ ⊔ ρ₂)^⊥ = (map (screwDiff u v) (Z₁ ⊔ Z₂))^⊥` under
`(screwDiff u v).dualMap` (`span_jointRows_eq_map_dualAnnihilator`, `Submodule.map_sup`,
`map_screwDiff_comm`). The two agree by `dualAnnihilator_eq_map_dualMap_screwDiff` at `W = Z₁ ⊔ Z₂`,
whose hypothesis is `mem_sup_infinitesimalMotions_of_isLink`.

Unlike `le_finrank_span_rigidityRows_of_cut`, the sides may share bodies, and the statement is an
equality. It does not ask that `u` and `v` be non-adjacent: an edge from `u` to `v` gives the same
rows on either side. The sides need not be induced subgraphs: for an ear whose ends `a` and `b` are
adjacent, the far side is the path, while the subgraph induced on its bodies also has the edge `ab`
(`finrank_span_rigidityRows_ear_eq`). -/
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

/-- **Rank gluing at two bodies** (`lem:block-rank-two-cut`): let the links of `F.graph` be those of
`G₁` together with those of `G₂`, every link of `Gᵢ` inside `Vᵢ`, with `V₁ ∩ V₂ ⊆ {u, v}` and
`u ≠ v`. Then, at the hinges of `F`,

  `rank R(G) = rank R(G₁) + rank R(G₂) + dim (ρ₁ ⊔ ρ₂) − D`

in `ℤ`, where `ρᵢ = (⟨Gᵢ, F.supportExtensor⟩).relScrews u v` and the rank is the dimension of the
row space. It is `Submodule.finrank_sup_add_finrank_inf_eq` for the two row spaces: their sum is the
row space of `F` (`rigidityRows_eq_union_of_isLink`, `Submodule.span_union`; this is where `hlink`
is used), and their intersection is the span of the joint rows
(`inf_span_rigidityRows_of_twoCut_of_isLink`), of dimension `D − dim (ρ₁ ⊔ ρ₂)`
(`finrank_span_jointRows`). The subtraction is in `ℤ`; in the proof, the subtraction in `ℕ` does not
truncate, as `dim (ρ₁ ⊔ ρ₂) ≤ D`. The sides need not cover `V(F.graph)`: a body on no edge adds no
rows. -/
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
  -- `dim (P ⊔ Q) + dim (P ⊓ Q) = dim P + dim Q`, the intersection by
  -- `inf_span_rigidityRows_of_twoCut_of_isLink` and its dimension by `finrank_span_jointRows`.
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span K F₁.rigidityRows) (Submodule.span K F₂.rigidityRows)
  rw [hkey, finrank_span_jointRows huv] at hsup
  rw [hrows, Submodule.span_union]
  have hle : Module.finrank K ↥(F₁.relScrews u v ⊔ F₂.relScrews u v) ≤ screwDim k := by
    have h := Submodule.finrank_le (F₁.relScrews u v ⊔ F₂.relScrews u v)
    rwa [screwSpace_finrank] at h
  omega

/-- **Two induced sides glued at two bodies meet in joint rows** (`cor:block-rank-vertex-two-cut`,
its first claim): for `u ≠ v` and `V₁ ∩ V₂ = {u, v}`,

  `span (F[V₁]).rigidityRows ⊓ span (F[V₂]).rigidityRows = span (jointRows (ρ₁ ⊔ ρ₂) u v)`,

with `ρᵢ = (F[Vᵢ]).relScrews u v`: `inf_span_rigidityRows_of_twoCut_of_isLink` at the induced
subgraphs `G[V₁]` and `G[V₂]`, whose links lie inside `V₁` and `V₂`. The proof uses only
`V₁ ∩ V₂ ⊆ {u, v}`. -/
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

/-- **Rank gluing at a vertex `2`-cut** (`cor:block-rank-vertex-two-cut`): for `u ≠ v`,
`V₁ ∩ V₂ = {u, v}` and every link of `G` inside `V₁` or inside `V₂`,

  `rank R(G) = rank R(G[V₁]) + rank R(G[V₂]) + dim (ρ₁ ⊔ ρ₂) − D`

in `ℤ`, with `ρᵢ = (F[Vᵢ]).relScrews u v`: `finrank_span_rigidityRows_twoCut_eq_of_isLink` at the
induced subgraphs, whose links are those of `G` by `hsep`. The proof uses only `V₁ ∩ V₂ ⊆ {u, v}`,
and the sets need not cover `V(G)`. -/
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

/-- **Rank addition at a cut vertex** (`lem:block-rank-cut-vertex`): for `V₁ ∩ V₂ ⊆ {v}` and every
link of `G` inside `V₁` or inside `V₂`, at every body-hinge framework,

  `rank R(G) = rank R(G[V₁]) + rank R(G[V₂])`.

Every screw assignment is a motion of `G[V₁]` plus a motion of `G[V₂]`
(`mem_sup_infinitesimalMotions_of_isLink` at `u = v`, where `S u = S v` holds by `rfl`), so the two
row spaces, the forms that vanish on the motions, meet in `0`; their sum is the row space of `G`
(`rigidityRows_eq_union_of_isLink`), and the dimensions add. -/
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
