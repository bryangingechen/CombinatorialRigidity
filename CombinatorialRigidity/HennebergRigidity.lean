/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Framework
import CombinatorialRigidity.Henneberg

/-!
# Rigidity preservation under Henneberg moves (dim 2)

Phase 5 milestone 2. The Type I and Type II Henneberg moves both preserve injective generic
rigidity in dimension 2. The proofs are rank-nullity arguments on the rigidity map: a `restrict :
ker ((typeI/II _).RigidityMap p_ext) →ₗ[ℝ] ker (G.RigidityMap p)` map `x ↦ x ∘ some` is built per
move, shown to be injective via the new edges through `none`, and the kernel-dim bound transports
via `LinearMap.finrank_le_finrank_of_injective`.

The Type II move's "place `q` on the line through `p a, p b`" construction requires the
*non-collinear* hypothesis `LinearIndependent ℝ ![p b - p a, p c - p a]`; the unconditional
wrapper `typeII_isGenericallyRigidInj_two` discharges this gap via a perpendicular perturbation
of the placement of `c`, justified by openness of infinitesimal rigidity
(`IsInfinitesimallyRigid.eventually`).

## Main theorems

* `SimpleGraph.Henneberg.typeI_isInfinitesimallyRigid_extend` — rank-nullity conditional core for
  Type I.
* `SimpleGraph.Henneberg.typeI_isGenericallyRigidInj_two` — unconditional Type I preservation.
* `SimpleGraph.Henneberg.typeII_isInfinitesimallyRigid_extend` — rank-nullity conditional core for
  Type II (input: `q` collinear with `(p a, p b)`; `(q - p a, q - p c)` LI).
* `SimpleGraph.Henneberg.typeII_isGenericallyRigidInj_two_of_nonCollinear` — Type II preservation
  conditional on non-collinearity.
* `SimpleGraph.Henneberg.typeII_isGenericallyRigidInj_two` — unconditional Type II preservation;
  composes the perpendicular-perturbation helper with the conditional theorem.

## Project context

This file extracts the Phase 5 milestone-2 rigidity-preservation work from `Henneberg.lean`,
which otherwise hosts only Phase 3 (Henneberg moves, edge sets, Laman preservation, iso
decomposition) and Phase 5 milestone 1 (the reverse-decomposition theorem with Laman preservation).
The split decouples `Henneberg.lean` from the analysis/linear-algebra imports needed here.

See `ROADMAP.md` §5 and `notes/Phase5.md` for the Phase 5 plan.
-/

open scoped InnerProductSpace Topology

namespace SimpleGraph

variable {V : Type*}

namespace Henneberg

/-- Injectivity of an `Option`-extended placement: if `p` is injective and the new value `q`
sits outside `Set.range p`, the function `fun w : Option V => w.elim q p` is injective.

The `Option`-extension shape comes from the Henneberg moves: `none` represents the fresh vertex,
placed at `q`; `some _` keeps the old placement. The 4-way `rintro` proof recurs in every
unconditional rigidity-preservation theorem (`typeI`/`typeII_isGenericallyRigidInj_two`); this
helper factors it. -/
private lemma injective_option_elim {V α : Type*}
    {p : V → α} (hp : Function.Injective p) {q : α} (hq : q ∉ Set.range p) :
    Function.Injective (fun w : Option V => w.elim q p) := by
  rintro (_ | u) (_ | v) h
  · rfl
  · exact (hq ⟨v, h.symm⟩).elim
  · exact (hq ⟨u, h⟩).elim
  · exact congrArg some (hp h)

/-- In `EuclideanSpace ℝ (Fin 2)`, every line `Submodule.span ℝ {v}` (with `v ≠ 0`) is a proper
subspace, so admits a non-member. The off-line construction in `exists_off_line_off_finite_dim_two`
and the perpendicular-perturbation direction in `exists_nonCollinear_rigid_placement_dim_two` both
need this; the helper consolidates the `finrank_span_singleton` / `finrank_euclideanSpace_fin` /
`SetLike.exists_not_mem_of_ne_top` chain. -/
private lemma exists_not_mem_span_singleton_dim_two
    {v : EuclideanSpace ℝ (Fin 2)} (hv : v ≠ 0) :
    ∃ w : EuclideanSpace ℝ (Fin 2),
      w ∉ Submodule.span ℝ ({v} : Set _) := by
  refine SetLike.exists_not_mem_of_ne_top _ ?_
  intro h_top
  have h1 := finrank_span_singleton (K := ℝ) hv
  rw [h_top, finrank_top] at h1
  have h2 := finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2)
  omega

/-- In `EuclideanSpace ℝ (Fin 2)`, a vector `u` orthogonal to two linearly independent vectors is
zero. The size-2 LI family spans (`Fin 2`'s cardinality matches `finrank`), so the orthogonal
complement is `⊥`. -/
private lemma eq_zero_of_orthogonal_dim_two
    {v₁ v₂ u : EuclideanSpace ℝ (Fin 2)}
    (hLI : LinearIndependent ℝ ![v₁, v₂])
    (h₁ : ⟪v₁, u⟫_ℝ = 0) (h₂ : ⟪v₂, u⟫_ℝ = 0) : u = 0 := by
  have h_span_top : Submodule.span ℝ (Set.range ![v₁, v₂]) = ⊤ :=
    hLI.span_eq_top_of_card_eq_finrank (by simp)
  have h_u_perp : u ∈ (Submodule.span ℝ (Set.range ![v₁, v₂]))ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      rcases hw with ⟨i, rfl⟩
      fin_cases i
      · simpa using h₁
      · simpa using h₂
    | zero => exact inner_zero_left _
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul c x _ hx => rw [inner_smul_left, hx]; simp
  rwa [h_span_top, Submodule.top_orthogonal_eq_bot, Submodule.mem_bot] at h_u_perp

/-- **Conditional Type I rigidity preservation in dim 2.** If `p : Framework V 2` is
infinitesimally rigid for `G` and `q : EuclideanSpace ℝ (Fin 2)` is a placement of the new vertex
for which the displacements `q - p a` and `q - p b` are linearly independent, then the extended
placement `fun w => w.elim q p` is infinitesimally rigid for `typeI G a b`.

The rank-nullity heart of `typeI_isGenericallyRigid_two`. The proof builds a linear injection
from `ker ((typeI G a b).RigidityMap p_ext)` into `ker (G.RigidityMap p)` via the restriction
`x ↦ x ∘ some`: it lands in the right kernel because every `G`-edge lifts to a `typeI G a b`-edge
with the same rigidity-row formula, and it is injective because the two new edges through `none`
pin down `x none` completely whenever `q - p a` and `q - p b` are linearly independent. -/
theorem typeI_isInfinitesimallyRigid_extend [Fintype V] {G : SimpleGraph V}
    {p : Framework V 2} (hp : G.IsInfinitesimallyRigid p) {a b : V}
    {q : EuclideanSpace ℝ (Fin 2)}
    (hLI : LinearIndependent ℝ ![q - p a, q - p b]) :
    (typeI G a b).IsInfinitesimallyRigid (fun w : Option V => w.elim q p) := by
  classical
  set p_ext : Framework (Option V) 2 := fun w : Option V => w.elim q p with hp_ext_def
  -- The restriction map `x ↦ x ∘ some` lands in `ker (G.RigidityMap p)`: every `G`-edge `s(u, v)`
  -- lifts to `s(some u, some v) ∈ (typeI G a b).edgeSet` with the same rigidity-row formula.
  have h_into : ∀ x : Framework (Option V) 2,
      x ∈ LinearMap.ker ((typeI G a b).RigidityMap p_ext) →
        x ∘ some ∈ LinearMap.ker (G.RigidityMap p) := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    ext ⟨e, he⟩
    induction e with
    | h u v =>
      have h_some : s(some u, some v) ∈ (typeI G a b).edgeSet := he
      have key := congr_fun hx ⟨s(some u, some v), h_some⟩
      simp only [rigidityMap_apply, Pi.zero_apply] at key
      simpa [rigidityMap_apply] using key
  -- Kernel-to-kernel linear map.
  let restrict : LinearMap.ker ((typeI G a b).RigidityMap p_ext) →ₗ[ℝ]
      LinearMap.ker (G.RigidityMap p) :=
    { toFun := fun x => ⟨x.1 ∘ some, h_into x.1 x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  -- Injectivity: any two kernel elements agreeing on `some _` agree at `none` too, because the
  -- two new edges through `none` orthogonalize `x.1 none - y.1 none` against the LI pair
  -- `(q - p a, q - p b)`, forcing the difference to vanish.
  have h_inj : Function.Injective restrict := by
    intro x y hxy
    apply Subtype.ext
    funext w
    have h_some : ∀ v, x.1 (some v) = y.1 (some v) := fun v =>
      congr_fun (congrArg Subtype.val hxy) v
    rcases w with _ | v
    swap
    · exact h_some v
    -- Case `w = none`. Extract the two new-edge constraints for both `x` and `y`.
    have h_a_edge : s((none : Option V), some a) ∈ (typeI G a b).edgeSet := by simp
    have h_b_edge : s((none : Option V), some b) ∈ (typeI G a b).edgeSet := by simp
    have hxa := congr_fun (LinearMap.mem_ker.mp x.2) ⟨s(none, some a), h_a_edge⟩
    have hxb := congr_fun (LinearMap.mem_ker.mp x.2) ⟨s(none, some b), h_b_edge⟩
    have hya := congr_fun (LinearMap.mem_ker.mp y.2) ⟨s(none, some a), h_a_edge⟩
    have hyb := congr_fun (LinearMap.mem_ker.mp y.2) ⟨s(none, some b), h_b_edge⟩
    simp only [rigidityMap_apply, Pi.zero_apply] at hxa hxb hya hyb
    -- `p_ext none = q`, `p_ext (some _) = p _` by defeq through `set`.
    change ⟪q - p a, x.1 none - x.1 (some a)⟫_ℝ = 0 at hxa
    change ⟪q - p b, x.1 none - x.1 (some b)⟫_ℝ = 0 at hxb
    change ⟪q - p a, y.1 none - y.1 (some a)⟫_ℝ = 0 at hya
    change ⟪q - p b, y.1 none - y.1 (some b)⟫_ℝ = 0 at hyb
    have h_perp_a : ⟪q - p a, x.1 none - y.1 none⟫_ℝ = 0 := by
      have hsubst : x.1 none - y.1 none =
          (x.1 none - x.1 (some a)) - (y.1 none - y.1 (some a)) := by
        rw [h_some a]; abel
      rw [hsubst, inner_sub_right, hxa, hya, sub_zero]
    have h_perp_b : ⟪q - p b, x.1 none - y.1 none⟫_ℝ = 0 := by
      have hsubst : x.1 none - y.1 none =
          (x.1 none - x.1 (some b)) - (y.1 none - y.1 (some b)) := by
        rw [h_some b]; abel
      rw [hsubst, inner_sub_right, hxb, hyb, sub_zero]
    exact sub_eq_zero.mp (eq_zero_of_orthogonal_dim_two hLI h_perp_a h_perp_b)
  -- Rank-nullity: `finrank (ker (typeI _)) ≤ finrank (ker G) ≤ 3`.
  change Module.finrank ℝ (LinearMap.ker ((typeI G a b).RigidityMap p_ext)) ≤ 2 * (2 + 1) / 2
  exact (LinearMap.finrank_le_finrank_of_injective h_inj).trans hp

/-- In `EuclideanSpace ℝ (Fin 2)`, given two distinct points `pa, pb` and a finite "to-avoid" set
`S`, there is a point `q ∉ S` with `q - pa` and `q - pb` linearly independent. The geometric
content is "off the line through `pa` and `pb`, and off `S`"; the one-parameter family
`q t := pa + t • v` for any `v ∉ span ℝ {pb - pa}` realizes both conditions on a cofinite set of
`t ∈ ℝ`. -/
private lemma exists_off_line_off_finite_dim_two
    (pa pb : EuclideanSpace ℝ (Fin 2)) (hab : pa ≠ pb)
    (S : Set (EuclideanSpace ℝ (Fin 2))) (hS : S.Finite) :
    ∃ q : EuclideanSpace ℝ (Fin 2),
      LinearIndependent ℝ ![q - pa, q - pb] ∧ q ∉ S := by
  have hd : pb - pa ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  -- Step 1. `Submodule.span ℝ {pb - pa}` is a proper subspace (finrank 1 < 2), so it has a
  -- non-member `v`.
  obtain ⟨v, hv_outside⟩ := exists_not_mem_span_singleton_dim_two hd
  have hv_ne_zero : v ≠ 0 := fun hv0 => hv_outside (hv0 ▸ zero_mem _)
  -- Step 2. The family `f t := pa + t • v` is injective in `t`.
  have hf_inj : Function.Injective (fun t : ℝ => pa + t • v) := fun t₁ t₂ h => by
    have h_smul : t₁ • v = t₂ • v := add_left_cancel h
    have h_sub : (t₁ - t₂) • v = 0 := by rw [sub_smul, h_smul, sub_self]
    rcases smul_eq_zero.mp h_sub with h0 | h0
    · linarith
    · exact (hv_ne_zero h0).elim
  -- Step 3. The "bad" `t`-set (yields `t = 0` or `f t ∈ S`) is finite; pick `t` outside.
  set bad : Set ℝ := {0} ∪ (fun t : ℝ => pa + t • v) ⁻¹' S with hbad_def
  have hbad_fin : bad.Finite := (Set.finite_singleton _).union (hS.preimage hf_inj.injOn)
  obtain ⟨t, ht⟩ := hbad_fin.exists_notMem
  have ht_ne : t ≠ 0 := fun h0 => ht (by simp [hbad_def, h0])
  have hq_notmem : pa + t • v ∉ S := fun h_mem => ht (by simp [hbad_def, h_mem])
  -- Step 4. Stage the LI claim as a row-op on `LinearIndependent ℝ ![v, pb - pa]`.
  refine ⟨pa + t • v, ?_, hq_notmem⟩
  have hLI_v_d :
      LinearIndependent ℝ (![v, pb - pa] : Fin 2 → EuclideanSpace ℝ (Fin 2)) := by
    rw [linearIndependent_fin2]
    refine ⟨hd, fun a h_eq => hv_outside ?_⟩
    rw [Submodule.mem_span_singleton]
    exact ⟨a, h_eq⟩
  have h_form :
      (![pa + t • v - pa, pa + t • v - pb] : Fin 2 → EuclideanSpace ℝ (Fin 2)) =
        ![t • v + (0 : ℝ) • (pb - pa), t • v + (-1 : ℝ) • (pb - pa)] := by
    ext i
    fin_cases i <;> simp
    abel
  rw [h_form, LinearIndependent.pair_add_smul_add_smul_iff]
  refine ⟨hLI_v_d, ?_⟩
  intro h_eq
  apply ht_ne
  linarith

/-- **Type I preserves injective generic rigidity in dim 2.** Given an injectively generically
rigid `G` in dim 2 and `a ≠ b` in `V`, the Henneberg Type I extension `typeI G a b` is again
injectively generically rigid in dim 2. The proof picks a `q : EuclideanSpace ℝ (Fin 2)` off both
the line through `p a, p b` (via `exists_off_line_off_finite_dim_two`) and the image of `p`, then
appeals to `typeI_isInfinitesimallyRigid_extend` for rigidity of the extended placement
`fun w => w.elim q p` and to the off-image condition for its injectivity. -/
theorem typeI_isGenericallyRigidInj_two [Fintype V] {G : SimpleGraph V}
    (hG : G.IsGenericallyRigidInj 2) {a b : V} (hab : a ≠ b) :
    (typeI G a b).IsGenericallyRigidInj 2 := by
  obtain ⟨p, hp_rig, hp_inj⟩ := hG
  have hpab : p a ≠ p b := fun h => hab (hp_inj h)
  obtain ⟨q, hLI, hq_notmem⟩ :=
    exists_off_line_off_finite_dim_two (p a) (p b) hpab (Set.range p)
      (Set.finite_range p)
  exact ⟨fun w : Option V => w.elim q p, typeI_isInfinitesimallyRigid_extend hp_rig hLI,
    injective_option_elim hp_inj hq_notmem⟩

/-! ### Type II preservation of rigidity in dim 2

The classical Whiteley/Jordán argument: place the new vertex `q` on the *line* through `p a` and
`p b`. The three new edges' constraints then split into a "deleted-edge recovery" (the constraint
`⟪p a - p b, x (some a) - x (some b)⟫ = 0` falls out of the new edges at `none ↔ some a` and
`none ↔ some b`, both lying along the common direction `p b - p a`) and an "injectivity" piece
(the new edge at `none ↔ some c`, in an independent direction, pins `x none`).

The argument requires `p a, p b, p c` to be **non-collinear** — otherwise `q - p c` also lies in
the `p b - p a` direction, the LI condition fails, and the extended placement is genuinely
non-rigid (a 1-parameter family of "vertical" infinitesimal motions of `none` is unconstrained).
The conditional theorem below takes the appropriate `q` as input; the unconditional wrapper
strengthens the input rigid placement to one with non-collinear `(p a, p b, p c)` via the
perturbation helper `exists_nonCollinear_rigid_placement_dim_two`, which uses openness of
infinitesimal rigidity (`IsInfinitesimallyRigid.eventually` in `Framework.lean`). -/

/-- **Conditional Type II rigidity preservation in dim 2.** If `p` is infinitesimally rigid for
`G`, `G.Adj a b`, and `q : EuclideanSpace ℝ (Fin 2)` is a placement of the new vertex satisfying
the collinearity condition `q - p a = α • (p b - p a)` with `α ≠ 0, 1` (so `q` is on the line
through `p a, p b`, distinct from both) AND the linear-independence condition
`LinearIndependent ℝ ![q - p a, q - p c]` (the new vertex's direction to `p c` is off the line),
then the extended placement `fun w => w.elim q p` is infinitesimally rigid for `typeII G a b c`.

The rank-nullity heart of `typeII_isGenericallyRigidInj_two_of_nonCollinear`. The proof builds a
linear injection from `ker ((typeII G a b c).RigidityMap p_ext)` into `ker (G.RigidityMap p)` via
the restriction `x ↦ x ∘ some`. The new ingredient over typeI is that for the deleted edge
`s(a, b)` (no corresponding typeII edge), the kernel constraint is recovered from the two
collinear-direction new edges at `none ↔ some a` and `none ↔ some b`. -/
theorem typeII_isInfinitesimallyRigid_extend [Fintype V] {G : SimpleGraph V}
    {p : Framework V 2} (hp : G.IsInfinitesimallyRigid p) {a b c : V}
    {q : EuclideanSpace ℝ (Fin 2)} {α : ℝ}
    (hα0 : α ≠ 0) (hα1 : α ≠ 1) (hcoll : q - p a = α • (p b - p a))
    (hLI : LinearIndependent ℝ ![q - p a, q - p c]) :
    (typeII G a b c).IsInfinitesimallyRigid (fun w : Option V => w.elim q p) := by
  classical
  set p_ext : Framework (Option V) 2 := fun w : Option V => w.elim q p with hp_ext_def
  -- `q - p b = (α - 1) • (p b - p a)` follows from the collinearity hypothesis.
  have hcoll_b : q - p b = (α - 1) • (p b - p a) := by
    have h1 : q - p b = (q - p a) - (p b - p a) := by abel
    rw [h1, hcoll, sub_smul, one_smul]
  -- Restriction map `x ↦ x ∘ some` lands in `ker (G.RigidityMap p)`.
  have h_into : ∀ x : Framework (Option V) 2,
      x ∈ LinearMap.ker ((typeII G a b c).RigidityMap p_ext) →
        x ∘ some ∈ LinearMap.ker (G.RigidityMap p) := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    -- New-edge constraints at `none ↔ some a` and `none ↔ some b`.
    have h_a_edge : s((none : Option V), some a) ∈ (typeII G a b c).edgeSet := by simp
    have h_b_edge : s((none : Option V), some b) ∈ (typeII G a b c).edgeSet := by simp
    have hxa := congr_fun hx ⟨s(none, some a), h_a_edge⟩
    have hxb := congr_fun hx ⟨s(none, some b), h_b_edge⟩
    simp only [rigidityMap_apply, Pi.zero_apply] at hxa hxb
    change ⟪q - p a, x none - x (some a)⟫_ℝ = 0 at hxa
    change ⟪q - p b, x none - x (some b)⟫_ℝ = 0 at hxb
    -- Strip the scalar to obtain `⟪p b - p a, _⟫ = 0` form.
    have hxa' : ⟪p b - p a, x none - x (some a)⟫_ℝ = 0 := by
      have h := hxa
      rw [hcoll, real_inner_smul_left] at h
      exact (mul_eq_zero.mp h).resolve_left hα0
    have hxb' : ⟪p b - p a, x none - x (some b)⟫_ℝ = 0 := by
      have h := hxb
      rw [hcoll_b, real_inner_smul_left] at h
      exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hα1)
    -- The deleted-edge constraint: subtract the two strip results.
    have h_deleted : ⟪p a - p b, x (some a) - x (some b)⟫_ℝ = 0 := by
      have hsub : x (some a) - x (some b) =
          (x none - x (some b)) - (x none - x (some a)) := by abel
      have h_pba : ⟪p b - p a, x (some a) - x (some b)⟫_ℝ = 0 := by
        rw [hsub, inner_sub_right, hxb', hxa', sub_zero]
      have hflip : p a - p b = -(p b - p a) := by abel
      rw [hflip, inner_neg_left, neg_eq_zero]; exact h_pba
    -- Edge-membership check.
    ext ⟨e, he⟩
    induction e with
    | h u v =>
      have h_uv : G.Adj u v := he
      by_cases h_eq : s(u, v) = s(a, b)
      · -- Deleted edge: recover via `h_deleted` (with Sym2 symmetry). Use `rw` on named hyps
        -- rather than `rfl`-rcases to avoid `subst` eliminating `a`/`b` from the context.
        simp only [rigidityMap_apply, Pi.zero_apply, Function.comp_apply]
        change ⟪p u - p v, x (some u) - x (some v)⟫_ℝ = 0
        rcases Sym2.eq_iff.mp h_eq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]; exact h_deleted
        · rw [h1, h2,
            show p b - p a = -(p a - p b) from by abel,
            show x (some b) - x (some a) = -(x (some a) - x (some b)) from by abel,
            inner_neg_neg]
          exact h_deleted
      · -- Non-deleted edge: lift to typeII edge.
        have h_typeII : s(some u, some v) ∈ (typeII G a b c).edgeSet :=
          show (typeII G a b c).Adj (some u) (some v) from ⟨h_uv, h_eq⟩
        have key := congr_fun hx ⟨s(some u, some v), h_typeII⟩
        simp only [rigidityMap_apply, Pi.zero_apply] at key
        simpa [rigidityMap_apply, Function.comp_apply] using key
  -- Kernel-to-kernel linear map.
  let restrict : LinearMap.ker ((typeII G a b c).RigidityMap p_ext) →ₗ[ℝ]
      LinearMap.ker (G.RigidityMap p) :=
    { toFun := fun x => ⟨x.1 ∘ some, h_into x.1 x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  -- Injectivity: the new edges at `none ↔ some a` and `none ↔ some c` orthogonalize
  -- `x.1 none - y.1 none` against the LI pair `(q - p a, q - p c)`.
  have h_inj : Function.Injective restrict := by
    intro x y hxy
    apply Subtype.ext
    funext w
    have h_some : ∀ v, x.1 (some v) = y.1 (some v) := fun v =>
      congr_fun (congrArg Subtype.val hxy) v
    rcases w with _ | v
    swap
    · exact h_some v
    -- Case `w = none`. Use new-edge constraints at `none ↔ some a` and `none ↔ some c`.
    have h_a_edge : s((none : Option V), some a) ∈ (typeII G a b c).edgeSet := by simp
    have h_c_edge : s((none : Option V), some c) ∈ (typeII G a b c).edgeSet := by simp
    have hxa := congr_fun (LinearMap.mem_ker.mp x.2) ⟨s(none, some a), h_a_edge⟩
    have hxc := congr_fun (LinearMap.mem_ker.mp x.2) ⟨s(none, some c), h_c_edge⟩
    have hya := congr_fun (LinearMap.mem_ker.mp y.2) ⟨s(none, some a), h_a_edge⟩
    have hyc := congr_fun (LinearMap.mem_ker.mp y.2) ⟨s(none, some c), h_c_edge⟩
    simp only [rigidityMap_apply, Pi.zero_apply] at hxa hxc hya hyc
    change ⟪q - p a, x.1 none - x.1 (some a)⟫_ℝ = 0 at hxa
    change ⟪q - p c, x.1 none - x.1 (some c)⟫_ℝ = 0 at hxc
    change ⟪q - p a, y.1 none - y.1 (some a)⟫_ℝ = 0 at hya
    change ⟪q - p c, y.1 none - y.1 (some c)⟫_ℝ = 0 at hyc
    have h_perp_a : ⟪q - p a, x.1 none - y.1 none⟫_ℝ = 0 := by
      have hsubst : x.1 none - y.1 none =
          (x.1 none - x.1 (some a)) - (y.1 none - y.1 (some a)) := by
        rw [h_some a]; abel
      rw [hsubst, inner_sub_right, hxa, hya, sub_zero]
    have h_perp_c : ⟪q - p c, x.1 none - y.1 none⟫_ℝ = 0 := by
      have hsubst : x.1 none - y.1 none =
          (x.1 none - x.1 (some c)) - (y.1 none - y.1 (some c)) := by
        rw [h_some c]; abel
      rw [hsubst, inner_sub_right, hxc, hyc, sub_zero]
    exact sub_eq_zero.mp (eq_zero_of_orthogonal_dim_two hLI h_perp_a h_perp_c)
  -- Rank-nullity: `finrank (ker (typeII _)) ≤ finrank (ker G) ≤ 3`.
  change Module.finrank ℝ (LinearMap.ker ((typeII G a b c).RigidityMap p_ext)) ≤ 2 * (2 + 1) / 2
  exact (LinearMap.finrank_le_finrank_of_injective h_inj).trans hp

/-- In `EuclideanSpace ℝ (Fin 2)`, given distinct points `pa, pb`, a third point `pc` with
`(pa, pb, pc)` non-collinear, and a finite "to-avoid" set `S`, there is a `q := pa + α • (pb - pa)`
on the line through `pa, pb` (with `α ≠ 0, 1`) such that `q ∉ S` and
`LinearIndependent ℝ ![q - pa, q - pc]`. The geometric content is: parametrize the line through
`pa, pb` by `α`; the LI condition is automatic from `(pa, pb, pc)` non-collinearity for any
`α ≠ 0`; the off-set and `α ≠ 1` conditions are each violated by at most finitely many `α`. -/
private lemma exists_typeII_q_on_line_dim_two
    (pa pb pc : EuclideanSpace ℝ (Fin 2)) (hab : pa ≠ pb)
    (hLI_abc : LinearIndependent ℝ ![pb - pa, pc - pa])
    (S : Set (EuclideanSpace ℝ (Fin 2))) (hS : S.Finite) :
    ∃ (α : ℝ) (q : EuclideanSpace ℝ (Fin 2)),
      α ≠ 0 ∧ α ≠ 1 ∧ q - pa = α • (pb - pa) ∧
      LinearIndependent ℝ ![q - pa, q - pc] ∧ q ∉ S := by
  have hd : pb - pa ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  -- Parametrize the line: `f α := pa + α • (pb - pa)`.
  set f : ℝ → EuclideanSpace ℝ (Fin 2) := fun α => pa + α • (pb - pa) with hf_def
  have hf_inj : Function.Injective f := fun α₁ α₂ h => by
    have h_smul : α₁ • (pb - pa) = α₂ • (pb - pa) := add_left_cancel h
    have h_sub : (α₁ - α₂) • (pb - pa) = 0 := by rw [sub_smul, h_smul, sub_self]
    rcases smul_eq_zero.mp h_sub with h0 | h0
    · linarith
    · exact (hd h0).elim
  -- The "bad" `α`-set: `{0, 1} ∪ f⁻¹(S)`.
  set bad : Set ℝ := ({0, 1} : Set ℝ) ∪ (f ⁻¹' S) with hbad_def
  have hbad_fin : bad.Finite :=
    ((Set.finite_singleton _).insert _).union (hS.preimage hf_inj.injOn)
  obtain ⟨α, hα⟩ := hbad_fin.exists_notMem
  have hα0 : α ≠ 0 := fun h => hα (by simp [hbad_def, h])
  have hα1 : α ≠ 1 := fun h => hα (by simp [hbad_def, h])
  have hq_notmem : f α ∉ S := fun h_mem => hα (by simp [hbad_def, h_mem])
  refine ⟨α, f α, hα0, hα1, ?_, ?_, hq_notmem⟩
  · -- `f α - pa = α • (pb - pa)` by definition.
    simp [hf_def]
  · -- LI of `![q - pa, q - pc]`: stage as a row-op on `![pb - pa, pc - pa]`.
    have h_form :
        (![f α - pa, f α - pc] : Fin 2 → EuclideanSpace ℝ (Fin 2)) =
          ![α • (pb - pa) + (0 : ℝ) • (pc - pa),
            α • (pb - pa) + (-1 : ℝ) • (pc - pa)] := by
      ext i
      fin_cases i <;> simp [hf_def]
      abel
    rw [h_form, LinearIndependent.pair_add_smul_add_smul_iff]
    refine ⟨hLI_abc, ?_⟩
    intro h_eq
    apply hα0
    linarith

/-- **Type II preserves injective generic rigidity in dim 2, given non-collinear neighbors.**
Given an injectively generically rigid `G` in dim 2 *witnessed by a placement* `p` *for which*
`(p a, p b, p c)` *is non-collinear*, the Type II extension `typeII G a b c` is again
injectively generically rigid in dim 2.

The non-collinearity hypothesis is essential — see the section docstring above. Removing it
requires an openness-of-rigidity argument (any rigid placement can be perturbed to a non-collinear
one while preserving rigidity); the perturbation is packaged in
`exists_nonCollinear_rigid_placement_dim_two`, used to land the unconditional
`typeII_isGenericallyRigidInj_two` below. -/
theorem typeII_isGenericallyRigidInj_two_of_nonCollinear [Fintype V] {G : SimpleGraph V}
    {p : Framework V 2} (hp_rig : G.IsInfinitesimallyRigid p) (hp_inj : Function.Injective p)
    {a b c : V} (hab : a ≠ b)
    (hLI_abc : LinearIndependent ℝ ![p b - p a, p c - p a]) :
    (typeII G a b c).IsGenericallyRigidInj 2 := by
  have hpab : p a ≠ p b := fun h => hab (hp_inj h)
  obtain ⟨α, q, hα0, hα1, hcoll, hLI, hq_notmem⟩ :=
    exists_typeII_q_on_line_dim_two (p a) (p b) (p c) hpab hLI_abc (Set.range p)
      (Set.finite_range p)
  exact ⟨fun w : Option V => w.elim q p,
    typeII_isInfinitesimallyRigid_extend hp_rig hα0 hα1 hcoll hLI,
    injective_option_elim hp_inj hq_notmem⟩

/-- **Openness-of-rigidity helper: produce a non-collinear rigid placement.** Given any injective
generically rigid `G` in dim 2 and three distinct vertices `a, b, c`, there is an injective rigid
placement `p` for which `(p a, p b, p c)` is non-collinear (i.e.,
`LinearIndependent ℝ ![p b - p a, p c - p a]`).

The proof: if the IH placement `p₀` already has the LI condition, use it. Otherwise
`p₀ c - p₀ a = γ⁻¹ • (p₀ b - p₀ a)` for some nonzero `γ`; pick a direction `w ∉ span (p₀ b - p₀ a)`
and perturb `p₀ c` to `p₀ c + t • w`. By `IsInfinitesimallyRigid.eventually` and continuity, the
perturbed placement stays rigid and injective on an open neighborhood of `t = 0` in `ℝ`; for any
`t ≠ 0` in this neighborhood, `p_t t c - p_t t a = γ⁻¹ • (p₀ b - p₀ a) + t • w` is no longer in
`span (p₀ b - p₀ a)`, so LI holds. Extract a witness from `𝓝[≠] 0` (which is `NeBot` in `ℝ`).

This is the openness-of-IR closure of the Phase 5 milestone 2 collinearity gap; it lifts
`typeII_isGenericallyRigidInj_two_of_nonCollinear` to the unconditional
`typeII_isGenericallyRigidInj_two` below. -/
private lemma exists_nonCollinear_rigid_placement_dim_two [Fintype V] {G : SimpleGraph V}
    (h : G.IsGenericallyRigidInj 2) {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ p : Framework V 2, G.IsInfinitesimallyRigid p ∧ Function.Injective p ∧
      LinearIndependent ℝ ![p b - p a, p c - p a] := by
  classical
  obtain ⟨p₀, hp₀_rig, hp₀_inj⟩ := h
  by_cases hLI₀ : LinearIndependent ℝ ![p₀ b - p₀ a, p₀ c - p₀ a]
  · exact ⟨p₀, hp₀_rig, hp₀_inj, hLI₀⟩
  -- Perturbation branch: `(p₀ a, p₀ b, p₀ c)` is collinear.
  have hpa_ne_pb : p₀ a ≠ p₀ b := fun heq => hab (hp₀_inj heq)
  have hpa_ne_pc : p₀ a ≠ p₀ c := fun heq => hac (hp₀_inj heq)
  have hd_ne_zero : p₀ b - p₀ a ≠ 0 := sub_ne_zero.mpr (Ne.symm hpa_ne_pb)
  have hdac_ne_zero : p₀ c - p₀ a ≠ 0 := sub_ne_zero.mpr (Ne.symm hpa_ne_pc)
  -- Collinearity coefficient `γ`: `γ • (p₀ c - p₀ a) = p₀ b - p₀ a` with `γ ≠ 0`.
  rw [linearIndependent_fin2] at hLI₀
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hLI₀
  push Not at hLI₀
  obtain ⟨γ, hγ⟩ := hLI₀ hdac_ne_zero
  have hγ_ne_zero : γ ≠ 0 := by
    intro hg; rw [hg, zero_smul] at hγ; exact hd_ne_zero hγ.symm
  have h_pca_decomp : p₀ c - p₀ a = γ⁻¹ • (p₀ b - p₀ a) := by
    rw [← hγ, ← smul_assoc, smul_eq_mul, inv_mul_cancel₀ hγ_ne_zero, one_smul]
  -- Perturbation direction `w` outside `span {p₀ b - p₀ a}` (proper subspace of `ℝ²`).
  obtain ⟨w, hw_outside⟩ := exists_not_mem_span_singleton_dim_two hd_ne_zero
  have hw_ne_zero : w ≠ 0 := fun h0 => hw_outside (h0 ▸ zero_mem _)
  -- The auxiliary LI `![w, p₀ b - p₀ a]`, used to invoke `pair_add_smul_add_smul_iff`.
  have h_LI_w_d : LinearIndependent ℝ
      (![w, p₀ b - p₀ a] : Fin 2 → EuclideanSpace ℝ (Fin 2)) := by
    rw [linearIndependent_fin2]
    refine ⟨hd_ne_zero, fun s heq => hw_outside ?_⟩
    rw [Submodule.mem_span_singleton]
    exact ⟨s, heq⟩
  -- Perturbation `p_t t := Function.update p₀ c (p₀ c + t • w)`.
  let p_t : ℝ → Framework V 2 := fun t => Function.update p₀ c (p₀ c + t • w)
  have h_p_t_c : ∀ t, p_t t c = p₀ c + t • w := fun _ =>
    Function.update_self c _ p₀
  have h_p_t_ne : ∀ t (v : V), v ≠ c → p_t t v = p₀ v := fun _ v hvc =>
    Function.update_of_ne hvc _ p₀
  have h_p_t_a : ∀ t, p_t t a = p₀ a := fun t => h_p_t_ne t a hac
  have h_p_t_b : ∀ t, p_t t b = p₀ b := fun t => h_p_t_ne t b hbc
  have h_p_t_cont : Continuous p_t := by
    refine continuous_pi (fun v => ?_)
    by_cases hvc : v = c
    · have h : (fun t : ℝ => p_t t v) = fun t => p₀ c + t • w := by
        funext t; rw [hvc, h_p_t_c]
      rw [h]
      exact continuous_const.add (continuous_id.smul continuous_const)
    · have h : (fun t : ℝ => p_t t v) = fun _ => p₀ v :=
        funext (fun t => h_p_t_ne t v hvc)
      rw [h]
      exact continuous_const
  have h_p_t_zero : p_t 0 = p₀ := by
    funext v
    by_cases hvc : v = c
    · rw [hvc, h_p_t_c]; simp
    · rw [h_p_t_ne 0 v hvc]
  -- Rigidity: an open neighborhood of `t = 0`.
  have h_rig_ev : ∀ᶠ t in 𝓝 (0 : ℝ), G.IsInfinitesimallyRigid (p_t t) := by
    have h_ev_p := hp₀_rig.eventually
    rw [← h_p_t_zero] at h_ev_p
    exact h_p_t_cont.continuousAt.tendsto.eventually h_ev_p
  -- Injectivity: an open neighborhood of `t = 0` (each `v ≠ c` is continuous-separated from `c`).
  have h_inj_ev : ∀ᶠ t in 𝓝 (0 : ℝ), Function.Injective (p_t t) := by
    have h_each : ∀ v ∈ Finset.univ.filter (fun v : V => v ≠ c),
        ∀ᶠ t in 𝓝 (0 : ℝ), p_t t v ≠ p_t t c := by
      intro v hv
      rw [Finset.mem_filter] at hv
      have hvc := hv.2
      have h_cont : Continuous (fun t : ℝ => p_t t v - p_t t c) :=
        ((continuous_apply v).comp h_p_t_cont).sub
          ((continuous_apply c).comp h_p_t_cont)
      have h_zero_ne : p_t 0 v - p_t 0 c ≠ 0 := by
        rw [h_p_t_zero]
        exact sub_ne_zero.mpr (fun heq => hvc (hp₀_inj heq))
      have h_ev := h_cont.continuousAt.eventually_ne h_zero_ne
      filter_upwards [h_ev] with t ht
      exact sub_ne_zero.mp ht
    have h_all := (Finset.univ.filter (fun v : V => v ≠ c)).eventually_all.mpr h_each
    filter_upwards [h_all] with t ht
    intro u v heq
    by_cases huc : u = c
    · by_cases hvc : v = c
      · rw [huc, hvc]
      · subst huc
        exfalso
        exact ht v (by simp [hvc]) heq.symm
    · by_cases hvc : v = c
      · subst hvc
        exfalso
        exact ht u (by simp [huc]) heq
      · have hu : p_t t u = p₀ u := by simp [p_t, Function.update_of_ne huc]
        have hv : p_t t v = p₀ v := by simp [p_t, Function.update_of_ne hvc]
        exact hp₀_inj (hu ▸ hv ▸ heq)
  -- LI of the perturbed pair, for any `t ≠ 0`. The collinear `p₀ c - p₀ a = γ⁻¹ • (p₀ b - p₀ a)`
  -- plus the `t • w` perturbation become linearly independent of `p₀ b - p₀ a` for `t ≠ 0`.
  have h_LI_perturbed : ∀ t : ℝ, t ≠ 0 →
      LinearIndependent ℝ ![p_t t b - p_t t a, p_t t c - p_t t a] := by
    intro t ht_ne
    have h_form :
        (![p_t t b - p_t t a, p_t t c - p_t t a] : Fin 2 → EuclideanSpace ℝ (Fin 2)) =
          ![(0 : ℝ) • w + (1 : ℝ) • (p₀ b - p₀ a), t • w + γ⁻¹ • (p₀ b - p₀ a)] := by
      funext i
      fin_cases i
      · change p_t t b - p_t t a = (0 : ℝ) • w + (1 : ℝ) • (p₀ b - p₀ a)
        rw [h_p_t_a t, h_p_t_b t, zero_smul, one_smul, zero_add]
      · change p_t t c - p_t t a = t • w + γ⁻¹ • (p₀ b - p₀ a)
        rw [h_p_t_a t, h_p_t_c t,
          show (p₀ c + t • w) - p₀ a = (p₀ c - p₀ a) + t • w from by abel, h_pca_decomp]
        abel
    rw [h_form, LinearIndependent.pair_add_smul_add_smul_iff]
    refine ⟨h_LI_w_d, ?_⟩
    simp [ht_ne.symm]
  -- Combine rigid + injective into one `∀ᶠ` on `𝓝[≠] 0`, extract a witness `t ≠ 0`.
  have h_combined : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      G.IsInfinitesimallyRigid (p_t t) ∧ Function.Injective (p_t t) ∧ t ≠ 0 := by
    filter_upwards [(h_rig_ev.and h_inj_ev).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t ⟨hrig, hinj⟩ ht_ne
    exact ⟨hrig, hinj, ht_ne⟩
  obtain ⟨t, hrig, hinj, ht_ne⟩ := h_combined.exists
  exact ⟨p_t t, hrig, hinj, h_LI_perturbed t ht_ne⟩

/-- **Type II preserves injective generic rigidity in dim 2 (unconditional).** Given an injectively
generically rigid `G` in dim 2 and three distinct vertices `a, b, c`, the Type II Henneberg
extension `typeII G a b c` is again injectively generically rigid in dim 2.

The proof passes the IH through `exists_nonCollinear_rigid_placement_dim_two` to obtain a placement
on which `(p a, p b, p c)` is non-collinear (the original IH placement may have a collinear
triple, in which case we perturb the placement of `c` perpendicular to the line through `p a, p b`
to break collinearity while preserving rigidity, by openness of infinitesimal rigidity), then
invokes the conditional `typeII_isGenericallyRigidInj_two_of_nonCollinear`.

**Phase 5 milestone 2 closure.** -/
theorem typeII_isGenericallyRigidInj_two [Fintype V] {G : SimpleGraph V}
    (hG : G.IsGenericallyRigidInj 2) {a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (typeII G a b c).IsGenericallyRigidInj 2 := by
  obtain ⟨p, hp_rig, hp_inj, hLI⟩ :=
    exists_nonCollinear_rigid_placement_dim_two hG hab hac hbc
  exact typeII_isGenericallyRigidInj_two_of_nonCollinear hp_rig hp_inj hab hLI

end Henneberg

end SimpleGraph
