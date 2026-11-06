/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.RigidityMatrix.Basic

/-!
# The column operation, the trivial motions and the rank lemmas for body-hinge frameworks

The second half of `RigidityMatrix/Basic.lean`, split off at its column-operation section. It holds
three sections of the rigidity-matrix chapter (`sec:molecular-rigidity-matrix`), after Katoh and
Tanigawa (2011, *A proof of the molecular conjecture*, Discrete Comput. Geom. **45**, §§2.3–2.4 and
5, and the equations of §6 named below):

* the column operation of KT eqs. (6.14)–(6.15) and the blocks of independent forms of KT eqs.
  (6.16) and (6.26)–(6.29), pp. 679 and 685–686 (`lem:case-III-columnop`,
  `lem:case-III-vanish-off-column`, `lem:case-III-transport-collapse`,
  `lem:case-II-placement-block-independent`, `lem:case-III-conditional-block`);
* the joint independence of the rows at hinges with ends of their own, for a star forest
  (`lem:own-end-rows-independent`, `lem:forest-rows-independent`);
* the trivial motions and the bound `rank R(G,p) ≤ D(|V| − 1)` (`def:trivial-motions-rigid`,
  `lem:trivial-motions-rank-bound`); KT Lemmas 5.1 and 5.3 (`lem:rank-delete-vertex`,
  `lem:rank-parallel-full`); and the comparison of two frameworks whose hinges have nested spans
  (`lem:rank-rotation-semicont`).

The definitions of the screw space, the hinge constraint, the rows of `R(G,p)` and the motions are
in `Basic.lean`.
-/

@[expose] public section

namespace CombinatorialRigidity.Molecular

open scoped Matrix

variable {K : Type*} [Field K]

namespace BodyHingeFramework

variable {k' k : ℕ} {α β : Type*}

/-! ## The column operation and blocks of independent forms (KT eqs. (6.14)–(6.29))

The column operation of KT eqs. (6.14)–(6.15) (`columnOp`), the forms that depend only on the screw
of one body, and the joint independence of a family of forms independent at a body `v` with a family
of forms that vanish at the screw assignments that vanish off `v`
(`linearIndependent_sum_pinned_block`), with its variants for Cases II and III. -/

/-- **A form that vanishes where `S v = 0` depends only on `S v`**
(`lem:case-III-vanish-off-column`; the form of KT eq. (6.28), p. 686): if `f S = 0` for every screw
assignment `S` with `S v = 0`, then `f = (f ∘ₗ single v) ∘ₗ proj v`, that is,
`f S = f (single v (S v))`. The assignment `S − single v (S v)` vanishes at `v`, so `f` kills it. In
KT eq. (6.28), the row operations leave a row whose entries outside the columns of `v` are zero. -/
theorem dualMap_eq_comp_single_proj_of_vanish_off [DecidableEq α]
    (f : Module.Dual K (α → ScrewSpace K k)) (v : α)
    (hvanish : ∀ S : α → ScrewSpace K k, S v = 0 → f S = 0) :
    f = (f.comp (LinearMap.single K (fun _ : α => ScrewSpace K k) v)).comp
      (LinearMap.proj v) := by
  refine LinearMap.ext fun S => ?_
  simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.coe_single]
  -- Split `S = (v-column part) + (off-`v` part)`; `f` kills the second by `hvanish`.
  have hz : f (S - Pi.single v (S v)) = 0 :=
    hvanish _ (by rw [Pi.sub_apply, Pi.single_eq_same, sub_self])
  rw [map_sub, sub_eq_zero] at hz
  exact hz

/-- **The column operation** `Φ` (`lem:case-III-columnop`; KT eqs. (6.14)–(6.15), p. 679): for
bodies `v ≠ a`, the linear automorphism `Φ S = Function.update S v (S v + S a)` of the screw
assignments, with inverse `S ↦ Function.update S v (S v − S a)`; both fix the value at `a`, as
`a ≠ v`. Replacing each row `f` of a rigidity matrix by `f ∘ₗ Φ` adds the columns of `v` to those of
`a`, and leaves the rank unchanged. The row `hingeRow v a ρ` becomes `S ↦ ρ (S v)`
(`hingeRow_comp_columnOp_apply`). -/
@[simps! apply]
noncomputable def columnOp [DecidableEq α] {v a : α} (hva : v ≠ a) :
    (α → ScrewSpace K k) ≃ₗ[K] (α → ScrewSpace K k) where
  toFun S := Function.update S v (S v + S a)
  invFun S := Function.update S v (S v - S a)
  map_add' S T := by
    refine funext fun x => ?_
    rcases eq_or_ne x v with rfl | hx
    · simp only [Function.update_self, Pi.add_apply]; abel
    · simp only [Function.update_of_ne hx, Pi.add_apply]
  map_smul' c S := by
    refine funext fun x => ?_
    rcases eq_or_ne x v with rfl | hx
    · simp only [Function.update_self, Pi.smul_apply, RingHom.id_apply, smul_add]
    · simp only [Function.update_of_ne hx, Pi.smul_apply, RingHom.id_apply]
  left_inv S := by
    refine funext fun x => ?_
    simp only
    rcases eq_or_ne x v with rfl | hx
    · simp only [Function.update_self, Function.update_of_ne hva.symm,
        add_sub_cancel_right]
    · rw [Function.update_of_ne hx, Function.update_of_ne hx]
  right_inv S := by
    refine funext fun x => ?_
    simp only
    rcases eq_or_ne x v with rfl | hx
    · simp only [Function.update_self, Function.update_of_ne hva.symm,
        sub_add_cancel]
    · rw [Function.update_of_ne hx, Function.update_of_ne hx]

/-- **`Φ` fixes the screw assignments that vanish off `v`** (from the proof of
`lem:case-III-columnop`): for `v ≠ b` and `Φ = columnOp hvb`, `Φ (single v x) = single v x`. At `v`
the value is `x + 0`, as `b ≠ v`, and elsewhere `Φ` changes nothing. -/
theorem columnOp_apply_single [DecidableEq α] {v b : α} (hvb : v ≠ b) (x : ScrewSpace K k) :
    columnOp (k := k) hvb (LinearMap.single K (fun _ : α => ScrewSpace K k) v x)
      = LinearMap.single K (fun _ : α => ScrewSpace K k) v x := by
  funext y
  rcases eq_or_ne y v with rfl | hy
  · simp only [columnOp_apply, Function.update_self, LinearMap.coe_single, Pi.single_eq_same,
      Pi.single_eq_of_ne hvb.symm, add_zero]
  · rw [columnOp_apply, Function.update_of_ne hy]

/-- **Composing with `Φ` keeps a form's columns of `v`** (from the proof of
`lem:case-III-columnop`): `(g ∘ₗ Φ) ∘ₗ single v = g ∘ₗ single v` for every form `g` on screw
assignments, by `columnOp_apply_single`. -/
theorem comp_columnOp_comp_single [DecidableEq α] {v b : α} (hvb : v ≠ b)
    (g : Module.Dual K (α → ScrewSpace K k)) :
    (g.comp (columnOp (k := k) hvb).toLinearMap).comp
        (LinearMap.single K (fun _ : α => ScrewSpace K k) v)
      = g.comp (LinearMap.single K (fun _ : α => ScrewSpace K k) v) :=
  LinearMap.ext fun x => by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, columnOp_apply_single]

/-- **After `Φ`, the form `hingeRow v a ρ` reads only `S v`** (`lem:case-III-columnop`; KT
eqs. (6.14)–(6.16), p. 679): `(hingeRow v a ρ) (Φ S) = ρ (S v)`, as `Φ S` has the value `S v + S a`
at `v` and `S a` at `a`. -/
theorem hingeRow_comp_columnOp_apply [DecidableEq α] {v a : α} (hva : v ≠ a)
    (ρ : Module.Dual K (ScrewSpace K k)) (S : α → ScrewSpace K k) :
    hingeRow (k := k) (α := α) v a ρ (columnOp (k := k) hva S) = ρ (S v) := by
  simp only [hingeRow_apply, columnOp_apply, Function.update_self,
    Function.update_of_ne hva.symm, add_sub_cancel_right]

/-- **After `Φ`, the form `hingeRow v a ρ` vanishes where `S v = 0`** (`lem:case-III-columnop`): by
`hingeRow_comp_columnOp_apply`, its value is `ρ (S v) = ρ 0 = 0`. -/
theorem hingeRow_comp_columnOp_vanish_off [DecidableEq α] {v a : α} (hva : v ≠ a)
    (ρ : Module.Dual K (ScrewSpace K k)) (S : α → ScrewSpace K k) (hS : S v = 0) :
    hingeRow (k := k) (α := α) v a ρ (columnOp (k := k) hva S) = 0 := by
  rw [hingeRow_comp_columnOp_apply hva ρ S, hS, map_zero]

/-- **After `Φ`, the form `hingeRow v a ρ` factors through `S v`**
(`lem:case-III-transport-collapse`, its last claim; KT eq. (6.28), p. 686): with
`w = (hingeRow v a ρ) ∘ₗ Φ`, `w = (w ∘ₗ single v) ∘ₗ proj v`. By
`hingeRow_comp_columnOp_vanish_off`, `w` vanishes where `S v = 0`, and
`dualMap_eq_comp_single_proj_of_vanish_off` applies. -/
theorem comp_columnOp_eq_comp_single_proj [DecidableEq α] {v a : α} (hva : v ≠ a)
    (ρ : Module.Dual K (ScrewSpace K k)) :
    (hingeRow (k := k) (α := α) v a ρ).comp (columnOp (k := k) hva).toLinearMap
      = (((hingeRow (k := k) (α := α) v a ρ).comp (columnOp (k := k) hva).toLinearMap).comp
          (LinearMap.single K (fun _ : α => ScrewSpace K k) v)).comp (LinearMap.proj v) :=
  dualMap_eq_comp_single_proj_of_vanish_off
    ((hingeRow (k := k) (α := α) v a ρ).comp (columnOp (k := k) hva).toLinearMap) v
    (fun S hS => by
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, hingeRow_comp_columnOp_vanish_off hva ρ S hS])

/-- **The forms of a star are independent** (`lem:own-end-rows-independent`, the case of a star):
let `w : J → α` be distinct bodies other than a body `v`, and for each `j` let the forms `r j i` on
the screw space be linearly independent. Then the forms `hingeRow (w j) v (r j i)` over `Σ j, I j`
are linearly independent.

Evaluate a vanishing combination at `Function.update 0 (w j₀) x`. The forms of `j ≠ j₀` vanish
there, as `w j ≠ w j₀` and `v ≠ w j₀`, and those of `j₀` take the values `r j₀ i x`. So the
coefficients of `j₀` give a vanishing combination of the forms `r j₀ i`, and they are zero. -/
theorem linearIndependent_hingeRow_star {J : Type*} [Finite J] {I : J → Type*}
    [∀ j, Finite (I j)] {v : α} {w : J → α} (hw : Function.Injective w) (hwv : ∀ j, w j ≠ v)
    {r : ∀ j, I j → Module.Dual K (ScrewSpace K k)} (hr : ∀ j, LinearIndependent K (r j)) :
    LinearIndependent K (fun p : Σ j, I j => hingeRow (k := k) (α := α) (w p.1) v (r p.1 p.2)) := by
  classical
  have : Fintype J := Fintype.ofFinite J
  have : ∀ j, Fintype (I j) := fun j => Fintype.ofFinite (I j)
  rw [Fintype.linearIndependent_iff]
  intro g hg k₀
  obtain ⟨j₀, i₀⟩ := k₀
  -- Evaluate the vanishing functional combination at `update 0 (w j₀) x`.
  have hval : ∀ x : ScrewSpace K k, ∑ i, g ⟨j₀, i⟩ • (r j₀ i) x = 0 := by
    intro x
    have happ := LinearMap.congr_fun hg (Function.update (0 : α → ScrewSpace K k) (w j₀) x)
    rw [LinearMap.sum_apply, LinearMap.zero_apply, Fintype.sum_sigma] at happ
    -- Every slice `j ≠ j₀` vanishes (its endpoint reads `0`); the `j₀` slice reads `x`.
    rw [Finset.sum_eq_single j₀] at happ
    · refine Eq.trans (Finset.sum_congr rfl (fun i _ => ?_)) happ
      simp only [LinearMap.smul_apply, hingeRow_apply, Function.update_self,
        Function.update_of_ne (hwv j₀).symm, Pi.zero_apply, sub_zero]
    · intro j _ hjk
      refine Finset.sum_eq_zero (fun i _ => ?_)
      have hjw : w j ≠ w j₀ := fun h => hjk (hw h)
      rw [LinearMap.smul_apply, hingeRow_apply, Function.update_of_ne hjw,
        Function.update_of_ne (hwv j₀).symm]
      simp only [Pi.zero_apply, sub_zero, map_zero, smul_zero]
    · exact fun h => absurd (Finset.mem_univ j₀) h
  -- The collapsed sum is a vanishing combination of `r j₀`, independent by hypothesis.
  have hk : ∑ i, g ⟨j₀, i⟩ • r j₀ i = 0 :=
    LinearMap.ext fun x => by
      simpa [LinearMap.sum_apply, LinearMap.smul_apply] using hval x
  exact Fintype.linearIndependent_iff.1 (hr j₀) (fun i => g ⟨j₀, i⟩) hk i₀

/-- **Forms independent at `v` and forms vanishing at `v` are jointly independent**
(`lem:case-II-placement-block-independent`): let `rn` be forms on screw assignments whose
restrictions to the assignments that vanish off `v`, `rn i ∘ₗ single v`, are linearly independent
(`hnewpin`), and `ro` linearly independent forms (`holdindep`) that vanish at those assignments
(`hold`). Then `Sum.elim rn ro` is linearly independent.

Evaluate a vanishing combination at `Function.update 0 v x`: the forms `ro` vanish there, so the
coefficients of `rn` vanish by `hnewpin`; what is left is a vanishing combination of `ro`. -/
theorem linearIndependent_sum_pinned_block {ιn ιo : Type*} [Finite ιn] [Finite ιo]
    [DecidableEq α] {v : α}
    {rn : ιn → Module.Dual K (α → ScrewSpace K k)} {ro : ιo → Module.Dual K (α → ScrewSpace K k)}
    (hold : ∀ (j : ιo) (x : ScrewSpace K k),
      ro j (Function.update (0 : α → ScrewSpace K k) v x) = 0)
    (hnewpin : LinearIndependent K
      (fun i : ιn => (rn i).comp (LinearMap.single K (fun _ : α => ScrewSpace K k) v)))
    (holdindep : LinearIndependent K ro) :
    LinearIndependent K (Sum.elim rn ro) := by
  classical
  have : Fintype ιn := Fintype.ofFinite ιn
  have : Fintype ιo := Fintype.ofFinite ιo
  rw [Fintype.linearIndependent_iff]
  intro g hg
  -- Split the index sum over `ιn ⊕ ιo`.
  rw [Fintype.sum_sum_type] at hg
  simp only [Sum.elim_inl, Sum.elim_inr] at hg
  -- Step 1: evaluate at `update 0 v x` to kill the old block, isolating the new block.
  have hnew0 : ∑ i : ιn, g (.inl i) •
      (rn i).comp (LinearMap.single K (fun _ : α => ScrewSpace K k) v) = 0 := by
    refine LinearMap.ext fun x => ?_
    have happ := LinearMap.congr_fun hg (Function.update (0 : α → ScrewSpace K k) v x)
    rw [LinearMap.add_apply, LinearMap.zero_apply, LinearMap.sum_apply, LinearMap.sum_apply] at happ
    -- The old block reads `0` at `update 0 v x`.
    have holdsum : ∑ j : ιo, (g (.inr j) • ro j) (Function.update (0 : α → ScrewSpace K k) v x)
        = 0 := Finset.sum_eq_zero fun j _ => by rw [LinearMap.smul_apply, hold j x, smul_zero]
    rw [holdsum, add_zero] at happ
    -- The new block collapses to the pinned functionals.
    rw [LinearMap.sum_apply, LinearMap.zero_apply]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) happ
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.coe_single,
      Pi.single]
  -- The new coefficients vanish by `hnewpin`.
  have hgn : ∀ i : ιn, g (.inl i) = 0 := Fintype.linearIndependent_iff.1 hnewpin _ hnew0
  -- Step 2: the residual is a vanishing combination of the old block.
  have hold0 : ∑ j : ιo, g (.inr j) • ro j = 0 := by
    rwa [Finset.sum_eq_zero (fun i _ => by rw [hgn i, zero_smul]), zero_add] at hg
  have hgo : ∀ j : ιo, g (.inr j) = 0 := Fintype.linearIndependent_iff.1 holdindep _ hold0
  rintro (i | j)
  · exact hgn i
  · exact hgo j

/-- **Forms that depend only on `S v`, and forms independent off `v`** (a step of
`lem:case-III-candidate-row`; the shape of KT eq. (6.29), p. 686): let the forms `top` vanish where
`S v = 0` (`htopvanish`), with restrictions to the assignments that vanish off `v` linearly
independent (`htoppin`), and let the restrictions of the forms `bot` to the other bodies,
`bot j ∘ₗ (id − single v ∘ₗ proj v)`, be linearly independent (`hbotrestrict`). Then
`Sum.elim top bot` is linearly independent.

Evaluate a vanishing combination at `S` with its value at `v` replaced by `0`: the forms `top`
vanish there, so the coefficients of `bot` vanish by `hbotrestrict`; then those of `top` vanish by
`htoppin`. It is `linearIndependent_sum_pinned_block` with the roles of the columns of `v` and of
the other columns exchanged. -/
theorem linearIndependent_sum_restriction_block {ιt ιb : Type*} [Finite ιt] [Finite ιb]
    [DecidableEq α] {v : α}
    {top : ιt → Module.Dual K (α → ScrewSpace K k)} {bot : ιb → Module.Dual K (α → ScrewSpace K k)}
    (htopvanish : ∀ (i : ιt) (S : α → ScrewSpace K k), S v = 0 → top i S = 0)
    (htoppin : LinearIndependent K
      (fun i : ιt => (top i).comp (LinearMap.single K (fun _ : α => ScrewSpace K k) v)))
    (hbotrestrict : LinearIndependent K
      (fun j : ιb => (bot j).comp
        ((LinearMap.id : (α → ScrewSpace K k) →ₗ[K] (α → ScrewSpace K k))
          - (LinearMap.single K (fun _ : α => ScrewSpace K k) v).comp (LinearMap.proj v)))) :
    LinearIndependent K (Sum.elim top bot) := by
  classical
  have : Fintype ιt := Fintype.ofFinite ιt
  have : Fintype ιb := Fintype.ofFinite ιb
  -- The off-`v` projection `P_v S = Function.update S v 0` (`id − single v ∘ proj v`).
  set P : (α → ScrewSpace K k) →ₗ[K] (α → ScrewSpace K k) :=
    (LinearMap.id : (α → ScrewSpace K k) →ₗ[K] (α → ScrewSpace K k))
      - (LinearMap.single K (fun _ : α => ScrewSpace K k) v).comp (LinearMap.proj v) with hP
  -- `P S` zeroes the `v`-coordinate and fixes the rest.
  have hPv : ∀ (S : α → ScrewSpace K k), (P S) v = 0 := fun S => by
    rw [hP, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      LinearMap.coe_single, Pi.sub_apply, Pi.single_eq_same, sub_self]
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fintype.sum_sum_type] at hg
  simp only [Sum.elim_inl, Sum.elim_inr] at hg
  -- Step 1: evaluate at `P S` (which has `(P S) v = 0`) to kill the top block, isolate the bottom.
  have hbot0 : ∑ j : ιb, g (.inr j) • (bot j).comp P = 0 := by
    refine LinearMap.ext fun S => ?_
    have happ := LinearMap.congr_fun hg (P S)
    rw [LinearMap.add_apply, LinearMap.zero_apply, LinearMap.sum_apply, LinearMap.sum_apply] at happ
    -- The top block vanishes at `P S` (its `v`-coordinate is `0`).
    have htopsum : ∑ i : ιt, (g (.inl i) • top i) (P S) = 0 :=
      Finset.sum_eq_zero fun i _ => by
        rw [LinearMap.smul_apply, htopvanish i (P S) (hPv S), smul_zero]
    rw [htopsum, zero_add] at happ
    -- The bottom block collapses to the restricted functionals at `S`.
    rw [LinearMap.sum_apply, LinearMap.zero_apply]
    refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) happ
    rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  -- The bottom coefficients vanish by `hbotrestrict`.
  have hgb : ∀ j : ιb, g (.inr j) = 0 := Fintype.linearIndependent_iff.1 hbotrestrict _ hbot0
  -- Step 2: the residual is a vanishing combination of the top block.
  have htop0 : ∑ i : ιt, g (.inl i) • top i = 0 := by
    have hbotzero : ∑ j : ιb, g (.inr j) • bot j = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [hgb j, zero_smul]
    rwa [hbotzero, add_zero] at hg
  -- Pin to body `v`'s column: the pinned residual vanishes, forcing the top coefficients.
  have htoppin0 : ∑ i : ιt, g (.inl i) •
      (top i).comp (LinearMap.single K (fun _ : α => ScrewSpace K k) v) = 0 := by
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.sum_apply, LinearMap.zero_apply]
    have happ := LinearMap.congr_fun htop0 (LinearMap.single K (fun _ : α => ScrewSpace K k) v x)
    rw [LinearMap.sum_apply, LinearMap.zero_apply] at happ
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) happ
    rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  have hgt : ∀ i : ιt, g (.inl i) = 0 :=
    Fintype.linearIndependent_iff.1 htoppin (fun i => g (.inl i)) htoppin0
  rintro (i | j)
  · exact hgt i
  · exact hgb j

/-- **Forms independent at `v`, in two families, and forms vanishing at `v`** (a step of
`lem:case-III-conditional-block`): if the restrictions of the forms `rn` and `wc` to the screw
assignments that vanish off `v` are jointly linearly independent (`hnewpinaug`), and the forms `ro`
are as in `linearIndependent_sum_pinned_block` (`hold`, `holdindep`), then
`Sum.elim (Sum.elim rn wc) ro` is linearly independent: that lemma, with `Sum.elim rn wc` as the
first family. -/
theorem linearIndependent_sum_pinned_block_augment_block {ιn ιo ιc : Type*}
    [Finite ιn] [Finite ιo] [Finite ιc]
    [DecidableEq α] {v : α}
    {rn : ιn → Module.Dual K (α → ScrewSpace K k)} {ro : ιo → Module.Dual K (α → ScrewSpace K k)}
    {wc : ιc → Module.Dual K (α → ScrewSpace K k)}
    (hold : ∀ (j : ιo) (x : ScrewSpace K k),
      ro j (Function.update (0 : α → ScrewSpace K k) v x) = 0)
    (hnewpinaug : LinearIndependent K (Sum.elim
      (fun i : ιn => (rn i).comp (LinearMap.single K (fun _ : α => ScrewSpace K k) v))
      (fun i : ιc => (wc i).comp (LinearMap.single K (fun _ : α => ScrewSpace K k) v))))
    (holdindep : LinearIndependent K ro) :
    LinearIndependent K (Sum.elim (Sum.elim rn wc) ro) := by
  -- The forms `wc` join `rn` in the first family of `linearIndependent_sum_pinned_block`.
  refine BodyHingeFramework.linearIndependent_sum_pinned_block (v := v) hold ?_ holdindep
  -- The first family, composed with `single v`, is the family of `hnewpinaug` (`Sum.elim`
  -- commutes with `.comp (single v)`).
  have hfun : (fun i : ιn ⊕ ιc =>
      ((Sum.elim rn wc) i).comp
        (LinearMap.single K (fun _ : α => ScrewSpace K k) v))
      = Sum.elim
        (fun i : ιn => (rn i).comp (LinearMap.single K (fun _ : α => ScrewSpace K k) v))
        (fun i : ιc => (wc i).comp (LinearMap.single K (fun _ : α => ScrewSpace K k) v)) := by
    funext i; cases i <;> rfl
  rw [hfun]; exact hnewpinaug

/-- **Two blocks of independent forms, with one more form independent at `v`**
(`lem:case-III-conditional-block`; for KT eq. (6.29), p. 686): if the restrictions of the forms `rn`
and of a form `w` to the screw assignments that vanish off `v` are linearly independent, and the
forms `ro` are linearly independent and vanish at those assignments, then `rn`, `w` and `ro` are
jointly linearly independent. It is the case `ιc = Unit` of
`linearIndependent_sum_pinned_block_augment_block`. -/
theorem linearIndependent_sum_pinned_block_augment {ιn ιo : Type*} [Finite ιn] [Finite ιo]
    [DecidableEq α] {v : α}
    {rn : ιn → Module.Dual K (α → ScrewSpace K k)} {ro : ιo → Module.Dual K (α → ScrewSpace K k)}
    {w : Module.Dual K (α → ScrewSpace K k)}
    (hold : ∀ (j : ιo) (x : ScrewSpace K k),
      ro j (Function.update (0 : α → ScrewSpace K k) v x) = 0)
    (hnewpinaug : LinearIndependent K (Sum.elim
      (fun i : ιn => (rn i).comp (LinearMap.single K (fun _ : α => ScrewSpace K k) v))
      (fun _ : Unit => w.comp (LinearMap.single K (fun _ : α => ScrewSpace K k) v))))
    (holdindep : LinearIndependent K ro) :
    LinearIndependent K (Sum.elim (Sum.elim rn (fun _ : Unit => w)) ro) :=
  -- The case `ιc = Unit` of `linearIndependent_sum_pinned_block_augment_block`.
  linearIndependent_sum_pinned_block_augment_block (wc := fun _ : Unit => w) hold hnewpinaug
    holdindep

/-- **The rows of `va`, the form `hingeRow v a ρ` and forms independent off `v`, through the column
operation** (a step of `lem:case-III-candidate-row`; KT eqs. (6.14)–(6.16) and (6.29), pp. 679 and
686): let `Φ = columnOp hva`. Suppose that the forms `rn i ∘ₗ Φ` vanish where `S v = 0`
(`hrnvanish`); that the restrictions of the forms `rn i ∘ₗ Φ` and `(hingeRow v a ρ) ∘ₗ Φ` to the
screw assignments that vanish off `v` are linearly independent (`hnewpinaug`); and that the
restrictions of the forms `ro j ∘ₗ Φ` to the other bodies are linearly independent (`hbotrestrict`).
Then `rn`, `hingeRow v a ρ` and `ro` are jointly linearly independent.

The forms composed with `Φ` satisfy `linearIndependent_sum_restriction_block`, the form
`(hingeRow v a ρ) ∘ₗ Φ` by `hingeRow_comp_columnOp_vanish_off`, and composing with `Φ` is an
injective linear map of the forms. -/
theorem linearIndependent_sum_augment_candidateRow_restriction
    [DecidableEq α] {v a : α} (hva : v ≠ a) {ιn ιo : Type*} [Finite ιn] [Finite ιo]
    {rn : ιn → Module.Dual K (α → ScrewSpace K k)} {ro : ιo → Module.Dual K (α → ScrewSpace K k)}
    {ρ : Module.Dual K (ScrewSpace K k)}
    (hrnvanish : ∀ (i : ιn) (S : α → ScrewSpace K k), S v = 0 →
      (rn i).comp (columnOp (k := k) hva).toLinearMap S = 0)
    (hnewpinaug : LinearIndependent K (Sum.elim
      (fun i : ιn =>
        ((rn i).comp (columnOp (k := k) hva).toLinearMap).comp
          (LinearMap.single K (fun _ : α => ScrewSpace K k) v))
      (fun _ : Unit =>
        ((hingeRow (k := k) (α := α) v a ρ).comp (columnOp (k := k) hva).toLinearMap).comp
          (LinearMap.single K (fun _ : α => ScrewSpace K k) v))))
    (hbotrestrict : LinearIndependent K
      (fun j : ιo => ((ro j).comp (columnOp (k := k) hva).toLinearMap).comp
        ((LinearMap.id : (α → ScrewSpace K k) →ₗ[K] (α → ScrewSpace K k))
          - (LinearMap.single K (fun _ : α => ScrewSpace K k) v).comp (LinearMap.proj v)))) :
    LinearIndependent K
      (Sum.elim (Sum.elim rn (fun _ : Unit => hingeRow (k := k) (α := α) v a ρ)) ro) := by
  set Φ := columnOp (K := K) (k := k) hva with hΦ
  have hker : LinearMap.ker Φ.dualMap.toLinearMap = ⊥ :=
    LinearMap.ker_eq_bot_of_injective Φ.dualMap.injective
  -- The composed forms `rn i ∘ₗ Φ` and `(hingeRow v a ρ) ∘ₗ Φ` vanish where `S v = 0`: the
  -- first by `hrnvanish`, the second by `hingeRow_comp_columnOp_vanish_off`.
  have htopvanish : ∀ (i : ιn ⊕ Unit) (S : α → ScrewSpace K k), S v = 0 →
      Sum.elim (fun i : ιn => (rn i).comp Φ.toLinearMap)
        (fun _ : Unit => (hingeRow (k := k) (α := α) v a ρ).comp Φ.toLinearMap) i S = 0 := by
    rintro (i | u) S hS
    · exact hrnvanish i S hS
    · rw [Sum.elim_inr, LinearMap.comp_apply, LinearEquiv.coe_coe,
        hingeRow_comp_columnOp_vanish_off hva ρ S hS]
  -- Their restrictions to the assignments that vanish off `v` are independent: `hnewpinaug`,
  -- with `Sum.elim` commuted with `.comp (single v)`.
  have htoppin : LinearIndependent K
      (fun i : ιn ⊕ Unit =>
        (Sum.elim (fun i : ιn => (rn i).comp Φ.toLinearMap)
          (fun _ : Unit => (hingeRow (k := k) (α := α) v a ρ).comp Φ.toLinearMap) i).comp
          (LinearMap.single K (fun _ : α => ScrewSpace K k) v)) := by
    convert hnewpinaug using 1
    funext i; rcases i with i | u <;> rfl
  -- `linearIndependent_sum_restriction_block` applies to the composed forms.
  have hop : LinearIndependent K (Sum.elim
      (Sum.elim (fun i : ιn => (rn i).comp Φ.toLinearMap)
        (fun _ : Unit => (hingeRow (k := k) (α := α) v a ρ).comp Φ.toLinearMap))
      (fun j : ιo => (ro j).comp Φ.toLinearMap)) :=
    linearIndependent_sum_restriction_block (v := v) htopvanish htoppin hbotrestrict
  -- The composed family is `Φ.dualMap` applied to the original one; `Φ.dualMap` is injective
  -- (`g ↦ g ∘ₗ Φ`), so the original family is independent.
  have hcomp : (Sum.elim (Sum.elim (fun i : ιn => (rn i).comp Φ.toLinearMap)
        (fun _ : Unit => (hingeRow (k := k) (α := α) v a ρ).comp Φ.toLinearMap))
      (fun j : ιo => (ro j).comp Φ.toLinearMap))
      = Φ.dualMap ∘
        (Sum.elim (Sum.elim rn (fun _ : Unit => hingeRow (k := k) (α := α) v a ρ)) ro) := by
    funext i; rcases i with (i | i) | j <;> rfl
  rw [hcomp] at hop
  exact (Φ.dualMap.toLinearMap.linearIndependent_iff hker).1 hop

/-! ## Joint row independence at hinges with ends of their own (a star forest)

The rows of several hinges are jointly independent when each hinge has an end that no other hinge
meets (`linearIndependent_hingeRow_starForest`, `exists_independent_rigidityRows_of_starForest`),
the multi-body form of `linearIndependent_hingeRow_star`. -/

/-- **The forms of hinges with ends of their own are jointly independent**
(`lem:own-end-rows-independent`, its claim for linear forms). Each hinge `j : J` runs from an end
`u j` of its own to an other end `other j`: the `u j` are distinct (`hu`), and no other end is any
hinge's own end (`hsep : ∀ j j', other j ≠ u j'`; in particular `u j ≠ other j`). The pairs
`(u j, other j)` then form a *star forest*, a forest each of whose components is a star: each
`u j` is a leaf whose one neighbour is `other j`. Not every forest is one: the edges of a path with
three edges allow no such choice of ends. If for each `j` the forms
`r j : Iⱼ → Module.Dual K (ScrewSpace K k)` are linearly independent, the forms
`⟨j, i⟩ ↦ hingeRow (u j) (other j) (r j i)` over `Σ j, Iⱼ` are linearly independent on
`α → ScrewSpace K k`.

`linearIndependent_hingeRow_star` is the case of one star, `u = w` and `other = const v`. The proof
evaluates a vanishing combination at the screw assignment `Function.update 0 (u j₀) x`: a hinge
`j ≠ j₀` reads `0` at both ends (`u j ≠ u j₀` by `hu`, `other j ≠ u j₀` by `hsep`) and the hinge
`j₀` reads `x` at `u j₀` and `0` at `other j₀`, so `∑ i, c⟨j₀,i⟩ • (r j₀ i) x = 0` for every `x`,
and every coefficient at `j₀` vanishes, as the forms `r j₀` are independent. -/
theorem linearIndependent_hingeRow_starForest {J : Type*} [Finite J] {I : J → Type*}
    [∀ j, Finite (I j)] {u other : J → α} (hu : Function.Injective u)
    (hsep : ∀ j j', other j ≠ u j')
    {r : ∀ j, I j → Module.Dual K (ScrewSpace K k)} (hr : ∀ j, LinearIndependent K (r j)) :
    LinearIndependent K
      (fun p : Σ j, I j => hingeRow (k := k) (α := α) (u p.1) (other p.1) (r p.1 p.2)) := by
  classical
  have : Fintype J := Fintype.ofFinite J
  have : ∀ j, Fintype (I j) := fun j => Fintype.ofFinite (I j)
  rw [Fintype.linearIndependent_iff]
  intro g hg k₀
  obtain ⟨j₀, i₀⟩ := k₀
  -- Evaluate the vanishing functional combination at `update 0 (u j₀) x`.
  have hval : ∀ x : ScrewSpace K k, ∑ i, g ⟨j₀, i⟩ • (r j₀ i) x = 0 := by
    intro x
    have happ := LinearMap.congr_fun hg (Function.update (0 : α → ScrewSpace K k) (u j₀) x)
    rw [LinearMap.sum_apply, LinearMap.zero_apply, Fintype.sum_sigma] at happ
    -- Every slice `j ≠ j₀` reads `0` at both endpoints; the `j₀` slice reads `x` at `u j₀`.
    rw [Finset.sum_eq_single j₀] at happ
    · refine Eq.trans (Finset.sum_congr rfl (fun i _ => ?_)) happ
      simp only [LinearMap.smul_apply, hingeRow_apply, Function.update_self,
        Function.update_of_ne (hsep j₀ j₀), Pi.zero_apply, sub_zero]
    · intro j _ hjk
      refine Finset.sum_eq_zero (fun i _ => ?_)
      have hjw : u j ≠ u j₀ := fun h => hjk (hu h)
      rw [LinearMap.smul_apply, hingeRow_apply, Function.update_of_ne hjw,
        Function.update_of_ne (hsep j j₀)]
      simp only [Pi.zero_apply, sub_zero, map_zero, smul_zero]
    · exact fun h => absurd (Finset.mem_univ j₀) h
  -- The collapsed sum is a vanishing combination of `r j₀`, independent by hypothesis.
  have hk : ∑ i, g ⟨j₀, i⟩ • r j₀ i = 0 :=
    LinearMap.ext fun x => by
      simpa [LinearMap.sum_apply, LinearMap.smul_apply] using hval x
  exact Fintype.linearIndependent_iff.1 (hr j₀) (fun i => g ⟨j₀, i⟩) hk i₀

/-- **Edges with ends of their own give `(D − 1)·|J|` independent rigidity rows**
(`lem:own-end-rows-independent`, its form for rows). Let each edge `e j` link an end `u j` of its
own to `other j` (`hlink`; `hu` and `hsep` as in `linearIndependent_hingeRow_starForest`, so the
edges form a star forest), with `F.supportExtensor (e j) ≠ 0` at each edge (`he`). Then there is a
linearly independent family of members of `F.rigidityRows` indexed by `Σ j, Fin (screwDim k − 1)`,
of cardinality `|J|·(D − 1)` with `D = screwDim k` (`Nat.card_sigma`).

The `D − 1` forms of each edge are a basis of its hinge-row block (`finrank_hingeRowBlock`,
extracted by `Submodule.exists_linearIndependent_fin_of_finrank_eq`), and
`linearIndependent_hingeRow_starForest` makes the rows of all the edges jointly independent; the
link `hlink j` and the block membership witness each as a rigidity row. -/
theorem exists_independent_rigidityRows_of_starForest (F : BodyHingeFramework K k α β) {J : Type*}
    [Finite J] {u other : J → α} {e : J → β} (hu : Function.Injective u)
    (hsep : ∀ j j', other j ≠ u j') (hlink : ∀ j, F.graph.IsLink (e j) (u j) (other j))
    (he : ∀ j, F.supportExtensor (e j) ≠ 0) :
    ∃ r : (Σ _ : J, Fin (screwDim k - 1)) → Module.Dual K (α → ScrewSpace K k),
      LinearIndependent K r ∧ ∀ p, r p ∈ F.rigidityRows := by
  classical
  have : FiniteDimensional K (ScrewSpace K k) := inferInstance
  -- Per-edge basis of the `(D−1)`-dimensional hinge-row block `r(p(e j))`.
  choose c hc hmem using fun j =>
    (F.hingeRowBlock (e j)).exists_linearIndependent_fin_of_finrank_eq
      (F.finrank_hingeRowBlock (he j))
  refine ⟨fun p => hingeRow (u p.1) (other p.1) (c p.1 p.2),
    linearIndependent_hingeRow_starForest hu hsep hc, fun p => ?_⟩
  exact ⟨e p.1, u p.1, other p.1, hlink p.1, c p.1 p.2, hmem p.1 p.2, rfl⟩

/-- **The rows of a forest of nondegenerate hinges are independent**
(`lem:forest-rows-independent`). Let `T ≤ F.graph` be a forest (`Graph.IsForest`) with
`F.supportExtensor e ≠ 0` at each edge `e` of `T`, the edge labels being finite. Then there is a
linearly independent family of members of `F.rigidityRows` indexed by
`Σ _ : T.edgeSet, Fin (screwDim k − 1)`, `D − 1` rows per edge. Unlike
`exists_independent_rigidityRows_of_starForest`, no edge needs an end of its own: a path with three
edges is a forest.

The proof is by induction on the number of edges, for rows at the links of `T` itself. A forest
with an edge has a pendant edge `e` at a body `x` (`Graph.IsForest.exists_isPendant`), and `T` less
`e` is a forest (`Graph.IsForest.anti`) none of whose edges is at `x`. Its rows vanish on the screw
assignments supported at `x`, where the `D − 1` rows `hingeRow x y (c i)` of `e`, for a basis `c` of
its hinge-row block (`finrank_hingeRowBlock`), read `c`; so `linearIndependent_sum_pinned_block`
makes the two families jointly independent, and they are the rows of `T` reindexed. -/
theorem exists_independent_rigidityRows_of_isForest [Finite β] (F : BodyHingeFramework K k α β)
    {T : Graph α β} (hT : T.IsForest) (hTF : T ≤ F.graph)
    (he : ∀ e ∈ T.edgeSet, F.supportExtensor e ≠ 0) :
    ∃ r : (Σ _ : T.edgeSet, Fin (screwDim k - 1)) → Module.Dual K (α → ScrewSpace K k),
      LinearIndependent K r ∧ ∀ p, r p ∈ F.rigidityRows := by
  classical
  have : FiniteDimensional K (ScrewSpace K k) := inferInstance
  -- The stronger claim, by induction on the number of edges: each row is one of a link of `T`.
  suffices key : ∀ (n : ℕ) (T : Graph α β), T.IsForest → T.edgeSet.ncard = n →
      (∀ e ∈ T.edgeSet, F.supportExtensor e ≠ 0) →
      ∃ r : (Σ _ : T.edgeSet, Fin (screwDim k - 1)) → Module.Dual K (α → ScrewSpace K k),
        LinearIndependent K r ∧
          ∀ p, ∃ u v, T.IsLink p.1 u v ∧ ∃ ρ ∈ F.hingeRowBlock p.1, r p = hingeRow u v ρ by
    obtain ⟨r, hr, hmem⟩ := key _ T hT rfl he
    refine ⟨r, hr, fun p => ?_⟩
    obtain ⟨u, v, hl, ρ, hρ, hp⟩ := hmem p
    exact ⟨p.1, u, v, hl.of_le hTF, ρ, hρ, hp⟩
  intro n
  induction n with
  | zero =>
    intro T _ hn _
    have hE : T.edgeSet = ∅ := (Set.ncard_eq_zero T.edgeSet.toFinite).1 hn
    have : IsEmpty (Σ _ : T.edgeSet, Fin (screwDim k - 1)) :=
      ⟨fun p => by simpa [hE] using p.1.2⟩
    exact ⟨isEmptyElim, linearIndependent_empty_type, isEmptyElim⟩
  | succ n ih =>
    intro T hT hn he
    have : T.EdgeFinite := ⟨T.edgeSet.toFinite⟩
    obtain ⟨e, x, hpend⟩ := hT.exists_isPendant (Set.nonempty_of_ncard_ne_zero (by omega))
    obtain ⟨y, hyx, hxy⟩ := hpend.isNonloopAt
    have heT := hpend.edge_mem
    -- `T` less its pendant edge `e`: a forest with `n` edges, none of them at `x`.
    have hn' : (T.deleteEdges {e}).edgeSet.ncard = n := by
      rw [Graph.edgeSet_deleteEdges, Set.ncard_sdiff_singleton_of_mem heT]; omega
    obtain ⟨r', hr', hmem'⟩ := ih (T.deleteEdges {e}) (hT.anti Graph.deleteEdges_le) hn'
      fun f hf => he f hf.1
    obtain ⟨c, hc, hcmem⟩ := (F.hingeRowBlock e).exists_linearIndependent_fin_of_finrank_eq
      (F.finrank_hingeRowBlock (he e heT))
    -- The old rows vanish on the assignments supported at `x`; `e`'s rows read `c` there.
    have hold : ∀ (p : Σ _ : (T.deleteEdges {e}).edgeSet, Fin (screwDim k - 1))
        (s : ScrewSpace K k), r' p (Function.update (0 : α → ScrewSpace K k) x s) = 0 := by
      intro p s
      obtain ⟨u, v, hl, ρ, -, hp⟩ := hmem' p
      have hl := hl.of_le Graph.deleteEdges_le
      have hu : u ≠ x := fun h => p.1.2.2 (hpend.edge_unique (h ▸ hl.inc_left))
      have hv : v ≠ x := fun h => p.1.2.2 (hpend.edge_unique (h ▸ hl.inc_right))
      simp [hp, hu, hv]
    have hnew : LinearIndependent K fun i => (hingeRow (k := k) x y (c i)).comp
        (LinearMap.single K (fun _ : α => ScrewSpace K k) x) := by
      convert hc using 1
      ext i s
      simp [hingeRow_apply, hyx]
    have hjoint := linearIndependent_sum_pinned_block hold hnew hr'
    -- Reindex: the edges of `T` are `e` and those of `T` less `e`.
    let σ : (Σ _ : T.edgeSet, Fin (screwDim k - 1)) →
        Fin (screwDim k - 1) ⊕ (Σ _ : (T.deleteEdges {e}).edgeSet, Fin (screwDim k - 1)) :=
      fun p => if h : p.1.1 = e then .inl p.2 else .inr ⟨⟨p.1.1, p.1.2, h⟩, p.2⟩
    have hσ : Function.Injective σ := by
      rintro ⟨⟨f, hf⟩, i⟩ ⟨⟨g, hg⟩, j⟩ h
      by_cases hfe : f = e <;> by_cases hge : g = e <;> simp_all [σ, Subtype.ext_iff]
    refine ⟨Sum.elim (fun i => hingeRow x y (c i)) r' ∘ σ, hjoint.comp σ hσ, ?_⟩
    rintro ⟨⟨f, hf⟩, i⟩
    by_cases hfe : f = e
    · subst hfe
      exact ⟨x, y, hxy, c i, hcmem i, by simp [σ]⟩
    · obtain ⟨u, v, hl, ρ, hρ, hp⟩ := hmem' ⟨⟨f, hf, hfe⟩, i⟩
      exact ⟨u, v, hl.of_le Graph.deleteEdges_le, ρ, hρ, by simp [σ, hfe, hp]⟩

/-! ## Trivial motions, rigidity and the rank lemmas (KT §§2.3–2.4 and 5)

The trivial motions, of dimension `D` (`lem:trivial-motions-rank-bound`); infinitesimal rigidity,
and rigidity on a set of bodies; KT Lemma 5.1 (`finrank_pinnedMotions_add_screwDim`,
`lem:rank-delete-vertex`) and Lemma 5.3 (`eq_of_hingeConstraint_two_parallel`,
`lem:rank-parallel-full`); and the comparison of two frameworks whose hinges have nested spans
(`lem:rank-rotation-semicont`), which is not KT Lemma 5.2. -/

/-- **A trivial screw assignment** (`def:trivial-motions-rigid`; KT §2.3, p. 653): `S u = S v` for
all bodies `u` and `v`. The trivial assignments are infinitesimal motions
(`isInfinitesimalMotion_of_isTrivialMotion`), and they form a space of dimension `D` when there is a
body (`finrank_trivialMotions`). -/
def IsTrivialMotion (S : α → ScrewSpace K k) : Prop :=
  ∀ u v, S u = S v

/-- Every trivial motion is an infinitesimal motion (`lem:trivial-motions-rank-bound`): a
constant screw assignment has `S u - S v = 0`, which lies in every hinge constraint's span,
so it satisfies the hinge constraint at every edge. -/
theorem isInfinitesimalMotion_of_isTrivialMotion (F : BodyHingeFramework K k α β)
    {S : α → ScrewSpace K k} (hS : IsTrivialMotion S) : F.IsInfinitesimalMotion S := by
  intro e u v _
  rw [hingeConstraint, hS u v, sub_self]
  exact Submodule.zero_mem _

/-- **The space of trivial motions** (`def:trivial-motions-rigid`): the constant screw assignments,
a subspace of `α → ScrewSpace K k`. Katoh and Tanigawa's `D` motions `S*_i` are a basis of it (KT
p. 654); it is the image of the screw space under `s ↦ (fun _ => s)`
(`trivialMotions_eq_range_const`), of dimension `D` when there is a body (`finrank_trivialMotions`).

The framework `_F` is an argument only so that `F.trivialMotions` reads as `F.infinitesimalMotions`
does; the space does not depend on it. -/
def trivialMotions (_F : BodyHingeFramework K k α β) : Submodule K (α → ScrewSpace K k) where
  carrier := {S | IsTrivialMotion S}
  add_mem' {S T} hS hT u v := by simp only [Pi.add_apply, hS u v, hT u v]
  zero_mem' u v := rfl
  smul_mem' c S hS u v := by rw [Pi.smul_apply, Pi.smul_apply, hS u v]

@[simp]
theorem mem_trivialMotions (F : BodyHingeFramework K k α β) (S : α → ScrewSpace K k) :
    S ∈ F.trivialMotions ↔ IsTrivialMotion S :=
  Iff.rfl

/-- **The trivial motions are motions** (a step of `lem:trivial-motions-rank-bound`):
`trivialMotions ≤ infinitesimalMotions`, by `isInfinitesimalMotion_of_isTrivialMotion`. -/
theorem trivialMotions_le_infinitesimalMotions (F : BodyHingeFramework K k α β) :
    F.trivialMotions ≤ F.infinitesimalMotions :=
  fun _ hS => F.isInfinitesimalMotion_of_isTrivialMotion hS

/-- **Infinitesimal rigidity** (`def:trivial-motions-rigid`; KT §2.3, p. 653): every infinitesimal
motion is trivial, `Z(G,p) ≤ trivialMotions`. It holds exactly when `Z(G,p)` is the space of trivial
motions (`infinitesimalMotions_eq_trivialMotions_iff`), which has dimension `D` when there is a body
(`finrank_trivialMotions`); that is, when `rank R(G,p) = D(|V| − 1)`
(`lem:trivial-motions-rank-bound`). -/
def IsInfinitesimallyRigid (F : BodyHingeFramework K k α β) : Prop :=
  F.infinitesimalMotions ≤ F.trivialMotions

theorem isInfinitesimallyRigid_iff (F : BodyHingeFramework K k α β) :
    F.IsInfinitesimallyRigid ↔
      ∀ S, F.IsInfinitesimalMotion S → IsTrivialMotion S :=
  Iff.rfl

/-- **Infinitesimal rigidity on a set `s` of bodies** (the rank form of `def:rank-hypothesis` at
deficiency zero): every infinitesimal motion is constant on `s`. All frameworks have the same bodies
`α`, and a body of `α` that is not a vertex of `G` moves freely; on `s = V(G)` the condition is the
rank `D(|V(G)| − 1)` (`rem:rank-hypothesis-relative`). On `s = Set.univ` it is infinitesimal
rigidity (`isInfinitesimallyRigidOn_univ_iff`). -/
def IsInfinitesimallyRigidOn (F : BodyHingeFramework K k α β) (s : Set α) : Prop :=
  ∀ S, F.IsInfinitesimalMotion S → ∀ u ∈ s, ∀ v ∈ s, S u = S v

theorem isInfinitesimallyRigidOn_iff (F : BodyHingeFramework K k α β) (s : Set α) :
    F.IsInfinitesimallyRigidOn s ↔
      ∀ S, F.IsInfinitesimalMotion S → ∀ u ∈ s, ∀ v ∈ s, S u = S v :=
  Iff.rfl

/-- **Rigidity on a set gives rigidity on its subsets** (`def:rank-hypothesis`): a motion constant
on `t` is constant on every `s ⊆ t`. -/
theorem IsInfinitesimallyRigidOn.mono (F : BodyHingeFramework K k α β) {s t : Set α} (hst : s ⊆ t)
    (h : F.IsInfinitesimallyRigidOn t) : F.IsInfinitesimallyRigidOn s :=
  fun S hS u hu v hv => h S hS u (hst hu) v (hst hv)

/-- **Rigidity on all of `α` is infinitesimal rigidity** (`def:rank-hypothesis`):
`F.IsInfinitesimallyRigidOn Set.univ ↔ F.IsInfinitesimallyRigid`. -/
theorem isInfinitesimallyRigidOn_univ_iff (F : BodyHingeFramework K k α β) :
    F.IsInfinitesimallyRigidOn Set.univ ↔ F.IsInfinitesimallyRigid := by
  rw [isInfinitesimallyRigidOn_iff, isInfinitesimallyRigid_iff]
  exact ⟨fun h S hS u v => h S hS u (Set.mem_univ u) v (Set.mem_univ v),
    fun h S hS u _ v _ => h S hS u v⟩

/-- **Rigidity on two sets with a common body gives rigidity on their union** (a step of
`lem:case-I-splice-seed`): if every motion is constant on `s` and on `t`, and `c ∈ s ∩ t`, then
every motion takes the value `S c` on `s ∪ t`. In Case I the vertex set of the rigid subgraph `H`
and that of the contraction `G/E(H)` share the body to which `H` is contracted, and cover `V(G)`. -/
theorem isInfinitesimallyRigidOn_union_of_inter (F : BodyHingeFramework K k α β) {s t : Set α}
    {c : α} (hcs : c ∈ s) (hct : c ∈ t)
    (hs : F.IsInfinitesimallyRigidOn s) (ht : F.IsInfinitesimallyRigidOn t) :
    F.IsInfinitesimallyRigidOn (s ∪ t) := by
  intro S hS u hu v hv
  have key : ∀ x ∈ s ∪ t, S x = S c := by
    rintro x (hx | hx)
    · exact hs S hS x hx c hcs
    · exact ht S hS x hx c hct
  rw [key u hu, key v hv]

/-- **Infinitesimal rigidity is the equality `Z(G,p) = trivialMotions`**
(`lem:trivial-motions-rank-bound`): the trivial motions are always motions
(`trivialMotions_le_infinitesimalMotions`), so rigidity, the other inclusion, gives the equality. -/
theorem infinitesimalMotions_eq_trivialMotions_iff (F : BodyHingeFramework K k α β) :
    F.infinitesimalMotions = F.trivialMotions ↔ F.IsInfinitesimallyRigid :=
  ⟨fun h => h.le, fun h => le_antisymm h F.trivialMotions_le_infinitesimalMotions⟩

/-- **The trivial motions are the constant assignments** (a step of
`lem:trivial-motions-rank-bound`): `trivialMotions` is the image of `s ↦ (fun _ => s)`. With
`injective_const_pi` it gives their dimension `D` (`finrank_trivialMotions`). -/
theorem trivialMotions_eq_range_const (F : BodyHingeFramework K k α β) :
    F.trivialMotions =
      LinearMap.range (LinearMap.pi (fun _ : α => LinearMap.id) :
        ScrewSpace K k →ₗ[K] α → ScrewSpace K k) := by
  ext S
  rw [mem_trivialMotions, LinearMap.mem_range]
  constructor
  · rintro hS
    rcases isEmpty_or_nonempty α with hα | ⟨⟨a⟩⟩
    · exact ⟨0, funext fun u => (hα.false u).elim⟩
    · exact ⟨S a, funext fun u => (hS u a).symm⟩
  · rintro ⟨s, rfl⟩ u v
    rfl

/-- **The map `s ↦ (fun _ => s)` is injective when there is a body** (a step of
`lem:trivial-motions-rank-bound`): two constant assignments that agree agree at a body. -/
theorem injective_const_pi [Nonempty α] :
    Function.Injective (LinearMap.pi (fun _ : α => LinearMap.id) :
      ScrewSpace K k →ₗ[K] α → ScrewSpace K k) := by
  intro s t h
  have := congrFun h (Classical.arbitrary α)
  simpa using this

/-- **The trivial motions have dimension `D`** (`lem:trivial-motions-rank-bound`; KT p. 654): when
there is a body, `finrank K F.trivialMotions = screwDim k`. They are the image of the injective map
`s ↦ (fun _ => s)` (`trivialMotions_eq_range_const`, `injective_const_pi`), which preserves
dimension (`LinearMap.finrank_range_of_inj`), and the screw space has dimension `D`
(`screwSpace_finrank`). -/
theorem finrank_trivialMotions [Nonempty α] (F : BodyHingeFramework K k α β) :
    Module.finrank K F.trivialMotions = screwDim k := by
  rw [trivialMotions_eq_range_const, LinearMap.finrank_range_of_inj injective_const_pi,
    screwSpace_finrank]

/-- **The screw assignments have dimension `D|V|`** (a step of `lem:trivial-motions-rank-bound`):
`finrank K (α → ScrewSpace K k) = screwDim k * Fintype.card α`, the number of columns of `R(G,p)`
(`Module.finrank_pi_const`, `screwSpace_finrank`). With `finrank_trivialMotions` it gives
`rank R(G,p) = D|V| − dim Z(G,p) ≤ D(|V| − 1)`. -/
theorem finrank_screwAssignment [Fintype α] :
    Module.finrank K (α → ScrewSpace K k) = screwDim k * Fintype.card α := by
  rw [Module.finrank_pi_const K, screwSpace_finrank, mul_comm]

/-- **The spans of two independent screws meet in `0`** (`lem:rank-parallel-full`; the step of KT
Lemma 5.3, p. 670): if `c₁` and `c₂` are linearly independent, then `span {c₁} ⊓ span {c₂} = ⊥`. Two
hinges spanned by `d − 1` of `d + 1` affinely independent points, omitting different pairs, have
independent extensors by KT Lemma 2.1 (`omitTwoExtensor_linearIndependent`). -/
theorem span_inf_span_eq_bot_of_linearIndependent {c₁ c₂ : ScrewSpace K k}
    (h : LinearIndependent K ![c₁, c₂]) :
    Submodule.span K {c₁} ⊓ Submodule.span K {c₂} = ⊥ := by
  rw [← disjoint_iff, Submodule.disjoint_span_singleton' (by simpa using h.ne_zero 1)]
  rw [LinearIndependent.pair_iff' (by simpa using h.ne_zero 0)] at h
  rw [Submodule.mem_span_singleton]
  rintro ⟨a, ha⟩
  exact h a ha

/-- **Two parallel edges with independent hinges fix the relative screw** (`lem:rank-parallel-full`;
KT Lemma 5.3, pp. 669–670): if the edges `e₁` and `e₂` join the bodies `u` and `v`, with linearly
independent supporting extensors, then every screw assignment that satisfies both hinge constraints
has `S u = S v`. The difference `S u − S v` lies in both spans
(`span_inf_span_eq_bot_of_linearIndependent`). The graph with two bodies and two such edges is the
base case of the algebraic induction (`lem:theorem-55-base`). -/
theorem eq_of_hingeConstraint_two_parallel (F : BodyHingeFramework K k α β)
    (S : α → ScrewSpace K k) {e₁ e₂ : β} {u v : α}
    (hgen : LinearIndependent K ![F.supportExtensor e₁, F.supportExtensor e₂])
    (h₁ : F.hingeConstraint S e₁ u v) (h₂ : F.hingeConstraint S e₂ u v) :
    S u = S v := by
  have hmem : S u - S v ∈
      Submodule.span K {F.supportExtensor e₁} ⊓ Submodule.span K {F.supportExtensor e₂} :=
    ⟨h₁, h₂⟩
  rw [span_inf_span_eq_bot_of_linearIndependent hgen, Submodule.mem_bot, sub_eq_zero] at hmem
  exact hmem

/-- **Independent screws admit no vanishing sum of nonzero multiples** (a step of
`lem:cycle-realization-rigid`): if the screws `c i` are linearly independent, `d i ∈ span {c i}` for
each `i`, and `∑ i, d i = 0`, then every `d i = 0`. Write `d i = a i • c i`
(`Submodule.mem_span_singleton`); then every `a i = 0` (`Fintype.linearIndependent_iff`). It is the
step behind the cycles of KT Lemma 5.4 (p. 670): around a cycle of bodies `vᵢ` whose supporting
extensors are independent, the differences `d i = S(vᵢ) − S(vᵢ₊₁)` of a motion satisfy these
hypotheses, so the motion is constant on the cycle. The case of two screws is
`span_inf_span_eq_bot_of_linearIndependent`. -/
theorem eq_zero_of_mem_span_singleton_of_sum_eq_zero {m : ℕ}
    {c d : Fin m → ScrewSpace K k} (hc : LinearIndependent K c)
    (hd : ∀ i, d i ∈ Submodule.span K {c i}) (hsum : ∑ i, d i = 0) (i : Fin m) :
    d i = 0 := by
  choose a ha using fun j => Submodule.mem_span_singleton.1 (hd j)
  have key : ∑ j, a j • c j = 0 := by rw [← hsum]; exact Finset.sum_congr rfl fun j _ => ha j
  rw [← ha i, Fintype.linearIndependent_iff.1 hc a key i, zero_smul]

/-- **The motions that vanish at a body `v`** (the space `pinned(v)` of `lem:rank-delete-vertex`):
the infinitesimal motions `S` with `S v = 0`. Deleting the `D` columns of `v` from `R(G,p)` leaves
the matrix whose null space consists of their restrictions to the other bodies. -/
def pinnedMotions (F : BodyHingeFramework K k α β) (v : α) :
    Submodule K (α → ScrewSpace K k) where
  carrier := {S | F.IsInfinitesimalMotion S ∧ S v = 0}
  add_mem' {S T} hS hT :=
    ⟨F.infinitesimalMotions.add_mem hS.1 hT.1, by simp only [Pi.add_apply, hS.2, hT.2, add_zero]⟩
  zero_mem' := ⟨F.infinitesimalMotions.zero_mem, rfl⟩
  smul_mem' c S hS :=
    ⟨F.infinitesimalMotions.smul_mem c hS.1, by rw [Pi.smul_apply, hS.2, smul_zero]⟩

@[simp]
theorem mem_pinnedMotions (F : BodyHingeFramework K k α β) (v : α) (S : α → ScrewSpace K k) :
    S ∈ F.pinnedMotions v ↔ F.IsInfinitesimalMotion S ∧ S v = 0 :=
  Iff.rfl

/-- **A motion minus a constant assignment is a motion** (a step of `lem:rank-delete-vertex`): the
hinge constraints read only the differences `S u − S w`, which subtracting `c` from every value does
not change. -/
theorem isInfinitesimalMotion_sub_const (F : BodyHingeFramework K k α β)
    {S : α → ScrewSpace K k} (hS : F.IsInfinitesimalMotion S) (c : ScrewSpace K k) :
    F.IsInfinitesimalMotion (fun u => S u - c) := by
  intro e u v he
  have := hS e u v he
  rw [hingeConstraint] at this ⊢
  simpa using this

/-- **The trivial motions and the motions that vanish at `v` meet in `0`**
(`lem:rank-delete-vertex`): a constant assignment with value `0` at `v` is zero. With
`trivialMotions_sup_pinnedMotions` it makes `Z(G,p)` their direct sum. -/
theorem trivialMotions_inf_pinnedMotions_eq_bot (F : BodyHingeFramework K k α β) (v : α) :
    F.trivialMotions ⊓ F.pinnedMotions v = ⊥ := by
  rw [eq_bot_iff]
  rintro S ⟨hTriv, _, hv⟩
  rw [Submodule.mem_bot]
  exact funext fun u => (hTriv u v).trans hv

/-- **Every motion is a trivial motion plus one that vanishes at `v`** (`lem:rank-delete-vertex`):
`trivialMotions ⊔ pinnedMotions v = infinitesimalMotions`. A motion `S` is the constant assignment
with value `S v` plus `u ↦ S u − S v`, which vanishes at `v` and is a motion
(`isInfinitesimalMotion_sub_const`). -/
theorem trivialMotions_sup_pinnedMotions (F : BodyHingeFramework K k α β) (v : α) :
    F.trivialMotions ⊔ F.pinnedMotions v = F.infinitesimalMotions := by
  apply le_antisymm
  · rw [sup_le_iff]
    exact ⟨F.trivialMotions_le_infinitesimalMotions, fun S hS => hS.1⟩
  · intro S hS
    refine Submodule.mem_sup.2 ⟨fun _ => S v, fun u v' => rfl, fun u => S u - S v, ?_, ?_⟩
    · exact ⟨F.isInfinitesimalMotion_sub_const hS (S v), sub_self _⟩
    · exact funext fun u => by rw [Pi.add_apply, add_sub_cancel]

/-- **Deleting the columns of one body keeps the rank** (`lem:rank-delete-vertex`; KT Lemma 5.1,
pp. 667–668): for finitely many bodies, at least one,

  `finrank (pinnedMotions v) + D = finrank Z(G,p)`,

as `Z(G,p)` is the direct sum of the trivial motions, of dimension `D`, and the motions that vanish
at `v` (`trivialMotions_inf_pinnedMotions_eq_bot`, `trivialMotions_sup_pinnedMotions`).
Equivalently, deleting the `D` columns of `v` from `R(G,p)` does not change its rank. Katoh and
Tanigawa cite White and Whiteley (1987, §2) for the fact that fixing a body does not change the
space of nontrivial motions (KT p. 668). -/
theorem finrank_pinnedMotions_add_screwDim [Nonempty α] [Finite α]
    (F : BodyHingeFramework K k α β) (v : α) :
    Module.finrank K (F.pinnedMotions v) + screwDim k =
      Module.finrank K F.infinitesimalMotions := by
  have : Fintype α := Fintype.ofFinite α
  have hdisj : F.trivialMotions ⊓ F.pinnedMotions v = ⊥ :=
    F.trivialMotions_inf_pinnedMotions_eq_bot v
  have hsup : F.trivialMotions ⊔ F.pinnedMotions v = F.infinitesimalMotions :=
    F.trivialMotions_sup_pinnedMotions v
  have key := Submodule.finrank_sup_of_inf_eq_bot F.trivialMotions (F.pinnedMotions v) hdisj
  rw [hsup, F.finrank_trivialMotions] at key
  omega

/-- **Smaller hinge spans give fewer motions** (`lem:rank-rotation-semicont`): if `F` and `F'` have
the same multigraph and `span C'(e) ≤ span C(e)` at every edge label `e`, where `C` and `C'` are the
supporting extensors of `F` and `F'`, then every motion of `F'` is one of `F`. At a link `e` from
`u` to `v`, `S u − S v ∈ span C'(e) ≤ span C(e)`. When all the extensors are nonzero, the hypothesis
says that the spans are equal; the inclusion can be strict at an edge with `C'(e) = 0 ≠ C(e)`. It is
not KT Lemma 5.2, which rotates a panel without lowering the rank (KT p. 669). -/
theorem infinitesimalMotions_mono_of_span_le (F F' : BodyHingeFramework K k α β)
    (hgraph : F.graph = F'.graph)
    (hspan : ∀ e, Submodule.span K {F'.supportExtensor e} ≤
      Submodule.span K {F.supportExtensor e}) :
    F'.infinitesimalMotions ≤ F.infinitesimalMotions := by
  intro S hS e u v he
  rw [hingeConstraint]
  exact hspan e (hS e u v (hgraph ▸ he))

/-- **Smaller hinge spans give a motion space of no larger dimension**
(`lem:rank-rotation-semicont`): for finitely many bodies and `F`, `F'` as in
`infinitesimalMotions_mono_of_span_le`, `finrank Z(G,p') ≤ finrank Z(G,p)`, so
`rank R(G,p) ≤ rank R(G,p')`, the rank being `D|V| − finrank Z` (`finrank_screwAssignment`).
`Submodule.finrank_mono` on `infinitesimalMotions_mono_of_span_le`. -/
theorem finrank_infinitesimalMotions_le_of_span_le [Finite α]
    (F F' : BodyHingeFramework K k α β) (hgraph : F.graph = F'.graph)
    (hspan : ∀ e, Submodule.span K {F'.supportExtensor e} ≤
      Submodule.span K {F.supportExtensor e}) :
    Module.finrank K F'.infinitesimalMotions ≤ Module.finrank K F.infinitesimalMotions :=
  Submodule.finrank_mono (F.infinitesimalMotions_mono_of_span_le F' hgraph hspan)

end BodyHingeFramework

end CombinatorialRigidity.Molecular
