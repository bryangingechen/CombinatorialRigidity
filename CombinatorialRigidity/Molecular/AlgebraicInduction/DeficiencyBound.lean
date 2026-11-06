/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Deficiency
public import CombinatorialRigidity.Molecular.RigidityMatrix.ColumnOperation
public import Mathlib.LinearAlgebra.Quotient.Pi

/-!
# The deficiency bound `D + def(G̃) ≤ dim Z(G,p)`

The third section of the former `PanelLayer.lean`, `lem:deficiency-rank-bound` and
`lem:relative-deficiency-rank-bound`: the screw assignments constant on the parts of a partition,
their dimension, the motions among them, and the resulting lower bound on the dimension of the
motion space `Z(G,p)` by `D + def(G̃)`, with its form for bodies outside `V(G)`, and that the two
forms of `D` agree, `bodyBarDim n = screwDim k`, only at `n = k + 1`. It needs only the deficiency
and the rigidity matrix, not the panels of `PanelLayer.lean`.
-/

@[expose] public section

namespace CombinatorialRigidity.Molecular

variable {k' k : ℕ}
variable {K : Type*} [Field K]

/-! ## The deficiency bound (`lem:deficiency-rank-bound`, `lem:relative-deficiency-rank-bound`)

A partition `P` of `V(G)` is given by a labeling `f : α → α` whose fibres meet `V(G)` in the parts.
The screw assignments constant on each fibre form a space `W_f` of dimension `D` times the number of
labels (`partitionConstant`, `finrank_partitionConstant`). Such an assignment meets the hinge
constraint at an edge inside a part; at an edge between two parts with a nondegenerate hinge, the
constraint is `D − 1` linear conditions. So the motions in `W_f` (`partitionMotions`) have dimension
at least `D·|P| − (D−1)·d_G(P) = D + def_{G̃}(P)`, and a partition of the largest deficiency gives
`D + def(G̃) ≤ dim Z(G,p)` (`lem:deficiency-rank-bound`). This bound, which holds at every
realization, is one of the two inequalities of the rank formula in Katoh and Tanigawa's
Proposition 2.3 (KT p. 655), which they credit to Jackson and Jordán
(`prop:rigidity-matrix-prop11`). Jackson and Jordán derive its rank form from a count of independent
rows (2010, *The generic rank of body–bar-and-hinge frameworks*, European J. Combin. **31**, §4,
pp. 580–581). -/

namespace BodyHingeFramework

variable {α β : Type*}

/-- **Constant on each part** (the partitions of `def:D-deficiency`, given by labels): `S` is
constant on each part of the partition that `f : α → α` gives if `S u = S v` whenever `f u = f v`.
-/
def IsPartitionConstant (f : α → α) (S : α → ScrewSpace K k) : Prop :=
  ∀ u v, f u = f v → S u = S v

/-- **The assignments constant on each part** (a step of `lem:deficiency-rank-bound`): the subspace
`W_f` of the screw assignments constant on each fibre of `f` (`IsPartitionConstant`), with no hinge
constraint. It has dimension `D·|range f|` (`finrank_partitionConstant`). -/
def partitionConstant (f : α → α) : Submodule K (α → ScrewSpace K k) where
  carrier := {S | IsPartitionConstant f S}
  add_mem' {S T} hS hT u v huv := by simp only [Pi.add_apply, hS u v huv, hT u v huv]
  zero_mem' _ _ _ := rfl
  smul_mem' c S hS u v huv := by rw [Pi.smul_apply, Pi.smul_apply, hS u v huv]

@[simp]
theorem mem_partitionConstant (f : α → α) (S : α → ScrewSpace K k) :
    S ∈ partitionConstant (k := k) f ↔ IsPartitionConstant f S :=
  Iff.rfl

/-- **`W_f` is the image of the assignments on the labels** (a step of `lem:deficiency-rank-bound`):
`partitionConstant f` is the range of `LinearMap.funLeft` along
`Set.rangeFactorization f : α → range f`, as an assignment is constant on each fibre of `f` iff it
factors through `f`. As `Set.rangeFactorization f` is onto, `LinearMap.funLeft` is injective, and
`W_f` has dimension `D·|range f|` (`finrank_partitionConstant`). -/
theorem partitionConstant_eq_range_funLeft (f : α → α) :
    partitionConstant (k := k) f =
      LinearMap.range (LinearMap.funLeft K (ScrewSpace K k) (Set.rangeFactorization f)) := by
  ext S
  rw [mem_partitionConstant, LinearMap.mem_range]
  constructor
  · intro hS
    refine ⟨fun b => S b.2.choose, funext fun a => ?_⟩
    rw [LinearMap.funLeft_apply]
    exact (hS _ a (Set.rangeFactorization f a).2.choose_spec)
  · rintro ⟨g, rfl⟩ u v huv
    rw [LinearMap.funLeft_apply, LinearMap.funLeft_apply]
    congr 1
    exact Subtype.ext huv

/-- **`W_f` has dimension `D·|range f|`** (a step of `lem:deficiency-rank-bound`): it is the image
of the assignments on `range f` (`partitionConstant_eq_range_funLeft`) under an injective map
(`LinearMap.funLeft_injective_of_surjective`), and those form a space of dimension `D·|range f|`
(`finrank_screwAssignment`). -/
theorem finrank_partitionConstant [Finite α] (f : α → α) :
    Module.finrank K (partitionConstant (K := K) (k := k) f) =
      screwDim k * Nat.card (Set.range f) := by
  have : Fintype α := Fintype.ofFinite α
  have : Fintype (Set.range f) := Fintype.ofFinite _
  rw [partitionConstant_eq_range_funLeft,
    LinearMap.finrank_range_of_inj
      (LinearMap.funLeft_injective_of_surjective K (ScrewSpace K k) _
        Set.rangeFactorization_surjective),
    finrank_screwAssignment, Nat.card_eq_fintype_card]

/-- **`D·|P| ≤ dim W_f`** (a step of `lem:deficiency-rank-bound`): the number of parts is
`|P| = numParts G f = |f '' V(G)|`, and `f '' V(G) ⊆ range f` (`finrank_partitionConstant`). The
labels of bodies outside `V(G)` can make the bound strict. -/
theorem mul_numParts_le_finrank_partitionConstant [Finite α] (G : Graph α β) (f : α → α) :
    screwDim k * G.numParts f ≤ Module.finrank K (partitionConstant (K := K) (k := k) f) := by
  rw [finrank_partitionConstant]
  refine Nat.mul_le_mul_left _ ?_
  rw [Graph.numParts, Nat.card_coe_set_eq, ← Set.image_univ]
  exact Set.ncard_le_ncard (Set.image_mono (Set.subset_univ _)) (Set.toFinite _)

/-- **The motions constant on each part** (a step of `lem:deficiency-rank-bound`):
`partitionMotions f = Z(G,p) ⊓ W_f`. At a partition of the largest deficiency they have dimension at
least `D + def(G̃)` (`screwDim_add_deficiency_le_finrank_infinitesimalMotions`). -/
noncomputable def partitionMotions (F : BodyHingeFramework K k α β) (f : α → α) :
    Submodule K (α → ScrewSpace K k) :=
  F.infinitesimalMotions ⊓ partitionConstant f

theorem partitionMotions_eq (F : BodyHingeFramework K k α β) (f : α → α) :
    F.partitionMotions f = F.infinitesimalMotions ⊓ partitionConstant f :=
  rfl

/-- **The motions constant on each part are motions** (a step of `lem:deficiency-rank-bound`):
`partitionMotions f ≤ Z(G,p)`. -/
theorem partitionMotions_le_infinitesimalMotions (F : BodyHingeFramework K k α β) (f : α → α) :
    F.partitionMotions f ≤ F.infinitesimalMotions :=
  inf_le_left

/-! ### The bound by rank–nullity

The bound `D·|P| − (D−1)·d_G(P) ≤ dim partitionMotions f` is rank–nullity for the linear map
`partitionCutMap`, which sends `S` to the relative screws `S u_e − S v_e` at the edges `e` between
two parts, modulo the lines `span {C(p(e))}` of their hinges. On `W_f` its kernel is
`partitionMotions f`, as an assignment constant on each part meets the hinge constraint at every
other edge, and its codomain has dimension `(D−1)·d_G(P)` when those hinges are nondegenerate. -/

/-- **An edge between two parts has two ends with different labels**: membership in
`crossingEdges G f` unfolds to `e ∈ E(G)` and `∃ x y, G.IsLink e x y ∧ f x ≠ f y`, from which
`crossingEndpoints` chooses. -/
theorem exists_isLink_of_mem_crossingEdges (G : Graph α β) (f : α → α)
    (e : ↥(G.crossingEdges f)) : ∃ x y, G.IsLink (e : β) x y ∧ f x ≠ f y :=
  e.2.2

/-- **The chosen ends of an edge between two parts**: a pair `(u_e, v_e)` of ends of `e` with
different labels, chosen once by `Classical.choose` (`exists_isLink_of_mem_crossingEdges`). The
choice does not depend on the screw assignment, so `partitionCutMap` is linear. -/
noncomputable def crossingEndpoints (G : Graph α β) (f : α → α)
    (e : ↥(G.crossingEdges f)) : α × α :=
  ((exists_isLink_of_mem_crossingEdges G f e).choose,
    (exists_isLink_of_mem_crossingEdges G f e).choose_spec.choose)

theorem crossingEndpoints_isLink (G : Graph α β) (f : α → α)
    (e : ↥(G.crossingEdges f)) :
    G.IsLink (e : β) (crossingEndpoints G f e).1 (crossingEndpoints G f e).2 :=
  (exists_isLink_of_mem_crossingEdges G f e).choose_spec.choose_spec.1

/-- **The lines of the hinges between parts**: the subspace `N_f` of the families
`g : crossingEdges G f → ScrewSpace K k` with `g e ∈ span {C(p(e))}` for every `e`. The quotient by
it is the codomain of `partitionCutMap`, of dimension `(D−1)·d_G(P)` when those hinges are
nondegenerate (`finrank_partitionCutMap_codomain`). It is one `Submodule.pi`, rather than a product
of quotients, so that the codomain is a quotient by one submodule. -/
noncomputable def crossingSpanPi (F : BodyHingeFramework K k α β) (f : α → α) :
    Submodule K (↥(F.graph.crossingEdges f) → ScrewSpace K k) :=
  Submodule.pi Set.univ fun e => Submodule.span K {F.supportExtensor (e : β)}

/-- **The cut at the edges between parts** (a step of `lem:deficiency-rank-bound`): the linear map
that sends a screw assignment `S` to the family of relative screws `S u_e − S v_e` at the edges `e`
between two parts (`crossingEndpoints`), modulo `N_f = crossingSpanPi f`. On `W_f` its kernel is
`partitionMotions f` (`partitionCutMap_ker_inf`), and its codomain has dimension `(D−1)·d_G(P)`
(`finrank_partitionCutMap_codomain`). -/
noncomputable def partitionCutMap (F : BodyHingeFramework K k α β) (f : α → α) :
    (α → ScrewSpace K k) →ₗ[K]
      ((↥(F.graph.crossingEdges f) → ScrewSpace K k) ⧸ F.crossingSpanPi f) :=
  (F.crossingSpanPi f).mkQ ∘ₗ
    LinearMap.pi fun e =>
      LinearMap.proj (R := K) (φ := fun _ : α => ScrewSpace K k) (crossingEndpoints F.graph f e).1
        - LinearMap.proj (R := K) (φ := fun _ : α => ScrewSpace K k)
            (crossingEndpoints F.graph f e).2

theorem partitionCutMap_apply_eq_zero_iff (F : BodyHingeFramework K k α β) (f : α → α)
    (S : α → ScrewSpace K k) :
    F.partitionCutMap f S = 0 ↔
      ∀ e : ↥(F.graph.crossingEdges f),
        S (crossingEndpoints F.graph f e).1 - S (crossingEndpoints F.graph f e).2
          ∈ Submodule.span K {F.supportExtensor (e : β)} := by
  rw [partitionCutMap, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    crossingSpanPi, Submodule.mem_pi]
  refine forall_congr' fun e => ?_
  simp only [Set.mem_univ, true_implies, LinearMap.pi_apply, LinearMap.sub_apply,
    LinearMap.proj_apply]

/-- **On `W_f` the kernel of the cut is `partitionMotions f`** (a step of
`lem:deficiency-rank-bound`): an assignment `S ∈ W_f` lies in the kernel iff it is an infinitesimal
motion. At an edge between two parts, vanishing modulo `span {C(p(e))}` at the chosen ends is the
hinge constraint, up to the order of the ends, as the span is closed under negation; at an edge
inside a part, `S u = S v` by constancy on the parts. Conversely, a motion meets the constraint at
the chosen ends. -/
theorem partitionCutMap_ker_inf (F : BodyHingeFramework K k α β) (f : α → α) :
    LinearMap.ker (F.partitionCutMap f) ⊓ partitionConstant f = F.partitionMotions f := by
  rw [partitionMotions_eq]
  apply le_antisymm
  · rintro S ⟨hker, hconst⟩
    refine Submodule.mem_inf.mpr ⟨?_, hconst⟩
    rw [mem_infinitesimalMotions]
    intro e u v he
    rw [hingeConstraint]
    by_cases hcross : e ∈ F.graph.crossingEdges f
    · -- Crossing edge: read the constraint off the chosen endpoints, swap to `u v`.
      have hk := (F.partitionCutMap_apply_eq_zero_iff f S).mp (LinearMap.mem_ker.mp hker)
        ⟨e, hcross⟩
      have hlink := crossingEndpoints_isLink F.graph f ⟨e, hcross⟩
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := he.eq_and_eq_or_eq_and_eq hlink
      · exact hk
      · rw [← neg_sub]; exact Submodule.neg_mem _ hk
    · -- Non-crossing edge: `f u = f v`, so `S u = S v` by part-constancy.
      have hfuv : f u = f v := by
        by_contra hne
        exact hcross ⟨he.edge_mem, u, v, he, hne⟩
      rw [hconst u v hfuv, sub_self]
      exact Submodule.zero_mem _
  · rintro S ⟨hmot, hconst⟩
    refine Submodule.mem_inf.mpr ⟨?_, hconst⟩
    rw [LinearMap.mem_ker, F.partitionCutMap_apply_eq_zero_iff f S]
    exact fun e =>
      (F.mem_infinitesimalMotions S).mp hmot _ _ _ (crossingEndpoints_isLink F.graph f e)

/-- **The codomain of the cut has dimension `(D−1)·d_G(P)`** (a step of
`lem:deficiency-rank-bound`): if the hinge of every edge between two parts is nondegenerate (`hC`),
the quotient of the families on the `d_G(P)` edges between parts by `N_f` is the product of the
quotients `ScrewSpace K k ⧸ span {C(p(e))}` (`Submodule.quotientPi`), each of dimension `D − 1`. -/
theorem finrank_partitionCutMap_codomain [Finite β]
    (F : BodyHingeFramework K k α β) (f : α → α)
    (hC : ∀ e ∈ F.graph.crossingEdges f, F.supportExtensor e ≠ 0) :
    Module.finrank K ((↥(F.graph.crossingEdges f) → ScrewSpace K k) ⧸ F.crossingSpanPi f)
      = (screwDim k - 1) * (F.graph.crossingEdges f).ncard := by
  have : Fintype β := Fintype.ofFinite β
  have : Fintype ↥(F.graph.crossingEdges f) := Fintype.ofFinite _
  classical
  -- The single `Submodule.pi` quotient splits as the product of fiber quotients
  -- `∀ e, ScrewSpace K k ⧸ span C(e)`, each of dimension `D − 1` (as `C(e) ≠ 0`).
  have hsplit : Module.finrank K
      ((↥(F.graph.crossingEdges f) → ScrewSpace K k) ⧸ F.crossingSpanPi f)
      = Module.finrank K ((e : ↥(F.graph.crossingEdges f)) →
          ScrewSpace K k ⧸ Submodule.span K {F.supportExtensor e}) :=
    (Submodule.quotientPi (Ms := fun _ : ↥(F.graph.crossingEdges f) => ScrewSpace K k)
      (fun e => Submodule.span K {F.supportExtensor (e : β)})).finrank_eq
  rw [hsplit, Module.finrank_pi_fintype]
  have hsumm : ∀ e : ↥(F.graph.crossingEdges f),
      Module.finrank K (ScrewSpace K k ⧸ Submodule.span K {F.supportExtensor (e : β)})
        = screwDim k - 1 := by
    intro e
    have key := Submodule.finrank_quotient_add_finrank
      (Submodule.span K {F.supportExtensor (e : β)})
    rw [finrank_span_singleton (hC e e.2), screwSpace_finrank] at key
    omega
  rw [Finset.sum_congr rfl fun e _ => hsumm e, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, mul_comm]

/-- **The motions constant on each part have dimension at least `D·|P| − (D−1)·d_G(P)`** (a step of
`lem:deficiency-rank-bound`): for a partition `f` whose edges between parts have nondegenerate
hinges (`hC`), in `ℤ`. By rank–nullity for `partitionCutMap f` on the screw assignments and
`dim (ker ⊔ W_f) ≤ D|α|`, `dim partitionMotions f ≥ dim W_f − (D−1)·d_G(P)`
(`partitionCutMap_ker_inf`, `finrank_partitionCutMap_codomain`), and `dim W_f ≥ D·|P|`
(`mul_numParts_le_finrank_partitionConstant`).
`screwDim_add_deficiency_le_finrank_infinitesimalMotions` applies it at a partition of the largest
deficiency. -/
theorem screwDim_mul_numParts_sub_le_finrank_partitionMotions [Finite α] [Finite β]
    (F : BodyHingeFramework K k α β) (f : α → α)
    (hC : ∀ e ∈ F.graph.crossingEdges f, F.supportExtensor e ≠ 0) :
    (screwDim k : ℤ) * F.graph.numParts f
        - (screwDim k - 1 : ℤ) * (F.graph.crossingEdges f).ncard
      ≤ (Module.finrank K (F.partitionMotions f) : ℤ) := by
  have : Fintype α := Fintype.ofFinite α
  have : Fintype ↥(F.graph.crossingEdges f) := Fintype.ofFinite _
  -- Work with the **full** cut `partitionCutMap f` on `α → ScrewSpace K k` (a plain pi, light
  -- instances), combining its rank-nullity with the `ker ⊓ W_f` dimension inequality.
  -- Rank-nullity: `finrank (range) + finrank (ker) = finrank (α → ScrewSpace K k) = D·|α|`.
  have hfull : Module.finrank K (LinearMap.range (F.partitionCutMap f))
      + Module.finrank K (LinearMap.ker (F.partitionCutMap f)) = screwDim k * Fintype.card α := by
    rw [LinearMap.finrank_range_add_finrank_ker, finrank_screwAssignment]
  -- `finrank (range) ≤ finrank codomain = (D−1)·d_G(P)`, distributed `D·d_G(P) − d_G(P)`
  -- so its `D·d_G(P)` and `d_G(P)` atoms line up with the (ℤ-distributed) goal for `omega`.
  have hrange : Module.finrank K (LinearMap.range (F.partitionCutMap f))
      ≤ screwDim k * (F.graph.crossingEdges f).ncard - (F.graph.crossingEdges f).ncard := by
    have := (LinearMap.range (F.partitionCutMap f)).finrank_le.trans_eq
      (F.finrank_partitionCutMap_codomain f hC)
    rwa [Nat.sub_mul, one_mul] at this
  -- `partitionMotions f = ker ⊓ W_f`, so by `Submodule.finrank_sup_add_finrank_inf_eq` and
  -- `finrank (ker ⊔ W_f) ≤ D·|α|`:
  -- `finrank (partitionMotions) ≥ finrank (ker) + finrank W_f − D·|α|`.
  have hinf : Module.finrank K (LinearMap.ker (F.partitionCutMap f))
        + Module.finrank K (partitionConstant (K := K) (k := k) f)
      ≤ Module.finrank K (F.partitionMotions f) + screwDim k * Fintype.card α := by
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.ker (F.partitionCutMap f)) (partitionConstant (k := k) f)
    rw [partitionCutMap_ker_inf] at hsup
    have hle : Module.finrank K
          (↥(LinearMap.ker (F.partitionCutMap f) ⊔ partitionConstant (k := k) f))
        ≤ screwDim k * Fintype.card α := by
      rw [← finrank_screwAssignment (K := K) (α := α) (k := k)]
      exact Submodule.finrank_le _
    omega
  -- `finrank W_f ≥ D·|P|`.
  have hWf := mul_numParts_le_finrank_partitionConstant (K := K) (k := k) F.graph f
  have hD : 1 ≤ screwDim k := Nat.choose_pos (by omega)
  have hdle : (F.graph.crossingEdges f).ncard ≤ screwDim k * (F.graph.crossingEdges f).ncard :=
    Nat.le_mul_of_pos_left _ (by omega)
  rw [sub_mul, one_mul]
  zify [hdle] at hrange ⊢
  zify at hfull hinf hWf
  omega

/-- **The two forms of `D` agree only at `n = k + 1`**: if `bodyBarDim n = screwDim k`, then
`n = k + 1`. Doubling clears the halves, `n(n + 1) = (k + 2)(k + 1)`, and `m ↦ m(m + 1)` is strictly
increasing (`nlinarith`). The statements that take both the dimension `n` of `def(G̃)` and the grade
`k` of the screw space use it to recover `n = k + 1`. -/
theorem _root_.Graph.eq_add_one_of_bodyBarDim_eq_screwDim {n k : ℕ}
    (hn : Graph.bodyBarDim n = screwDim k) : n = k + 1 := by
  have key : ∀ m : ℕ, 2 * Nat.choose m 2 = m * (m - 1) := fun m => by
    rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self m).two_dvd]
  have hbb : 2 * Graph.bodyBarDim n = n * (n + 1) := by
    rw [Graph.bodyBarDim, Nat.mul_div_cancel' (Nat.even_mul_succ_self n).two_dvd]
  have hsd : 2 * screwDim k = (k + 2) * (k + 1) := by
    rw [show screwDim k = Nat.choose (k + 2) 2 from rfl, key (k + 2),
      show k + 2 - 1 = k + 1 from rfl]
  have hprod : n * (n + 1) = (k + 2) * (k + 1) := by omega
  nlinarith [hprod]

/-- **`bodyBarDim n = screwDim (n − 1)` for `n ≥ 1`**, the converse of
`Graph.eq_add_one_of_bodyBarDim_eq_screwDim`. A statement can then take one `n` and the grade
`n − 1`, without a separate `k` and the hypothesis `bodyBarDim n = screwDim k`. It is here rather
than in `RigidityMatrix/Basic.lean` with `screwDim` because `Graph.bodyBarDim` is defined in
`BodyBar/Framework.lean`, which is not a `module` file, and a `module` file imports only `module`
files (`LEAN-OPS.md` *Module-system conversion*). -/
theorem _root_.Graph.bodyBarDim_eq_screwDim_sub_one {n : ℕ} (hn : 1 ≤ n) :
    Graph.bodyBarDim n = screwDim (n - 1) := by
  rw [Graph.bodyBarDim, screwDim, Nat.choose_two_right,
    show n - 1 + 2 = n + 1 by omega, show n + 1 - 1 = n by omega, Nat.mul_comm]

/-- **`bodyBarDim (k + 1) = screwDim k`**, the form of `bodyBarDim_eq_screwDim_sub_one` with the
grade `k` given and `n = k + 1` (so no `1 ≤ n` side condition). It reconciles the body-bar and
screw-space conventions for `D`. -/
theorem _root_.Graph.bodyBarDim_add_one_eq_screwDim (k : ℕ) :
    Graph.bodyBarDim (k + 1) = screwDim k :=
  Graph.bodyBarDim_eq_screwDim_sub_one (Nat.le_add_left 1 k)

/-- **The deficiency bound** (`lem:deficiency-rank-bound`): for a nonempty finite set of bodies,
with the hinge nondegenerate at the edges of `G` whose two ends differ (`hC`; a loop never crosses a
partition), `D + def(G̃) ≤ dim Z(G,p)`, the deficiency
taken for `n = k + 1`; that is, `rank R(G,p) ≤ D(|V| − 1) − def(G̃)`. Take a partition `f` of the
largest deficiency (`exists_eq_ciSup_of_finite`, a finite supremum). As
`screwDim k = bodyBarDim (k + 1)`, `D·|P| − (D−1)·d_G(P) = D + def(G̃)` there, and the motions
constant on its parts have at least that dimension
(`screwDim_mul_numParts_sub_le_finrank_partitionMotions`). It is one of the two inequalities of the
rank formula in KT Proposition 2.3 (p. 655; `prop:rigidity-matrix-prop11`); Jackson and Jordán
derive its rank form from a count of independent rows (2010, §4, pp. 580–581). -/
theorem screwDim_add_deficiency_le_finrank_infinitesimalMotions [Nonempty α] [Finite α] [Finite β]
    (F : BodyHingeFramework K k α β)
    (hC : ∀ e u v, F.graph.IsLink e u v → u ≠ v → F.supportExtensor e ≠ 0) :
    (screwDim k : ℤ) + F.graph.deficiency (k + 1)
      ≤ (Module.finrank K F.infinitesimalMotions : ℤ) := by
  have : Fintype α := Fintype.ofFinite α
  -- `D = screwDim k = bodyBarDim (k+1)` reconciles the screw-space and body-bar `D` conventions.
  have hDcast : (Graph.bodyBarDim (k + 1) : ℤ) = (screwDim k : ℤ) := by
    exact_mod_cast Graph.bodyBarDim_add_one_eq_screwDim k
  -- Pick a partition `f` of `V(G)` attaining `def(G̃)` (a finite supremum under `[Finite α]`).
  obtain ⟨f, hf⟩ := exists_eq_ciSup_of_finite (f := F.graph.partitionDef (k + 1))
  rw [Graph.deficiency, ← hf]
  -- The dimension lower bound at this `f`, and the transfer `partitionMotions f ≤ Z`.
  have hlb := F.screwDim_mul_numParts_sub_le_finrank_partitionMotions f fun e he => by
    obtain ⟨_, x, y, hlink, hxy⟩ := he
    exact hC e x y hlink fun h => hxy (h ▸ rfl)
  have hmono : Module.finrank K (F.partitionMotions f)
      ≤ Module.finrank K F.infinitesimalMotions :=
    Submodule.finrank_mono (F.partitionMotions_le_infinitesimalMotions f)
  -- `D·|P| − (D−1)·d_G(P) = D + partitionDef(P)`, so the lower bound reads `D + def ≤ dim Z`.
  rw [Graph.partitionDef, hDcast]
  zify at hmono
  linarith [hlb, hmono]

/-! ### The bound with bodies outside `V(G)` (`lem:relative-deficiency-rank-bound`)

With the bodies outside `V(G)`, the bound reads `D·(|V(G)ᶜ| + 1) + def(G̃) ≤ dim Z(G,p)`. Its proof
counts `|range f|` in place of the number of parts, as `dim W_f = D·|range f|` exactly
(`finrank_partitionConstant`). At a labeling with the same parts on `V(G)` and the same edges
between parts as a partition of the largest deficiency, whose labels on `V(G)` are vertices of `G`
(`Graph.exists_normalized_labeling`, `Molecular/Deficiency.lean`), the range has `|P| + |V(G)ᶜ|`
elements. -/

/-- **The bound with `|range f|` for the number of parts** (a step of
`lem:relative-deficiency-rank-bound`): `D·|range f| − (D−1)·d_G(P) ≤ dim partitionMotions f`, by the
proof of `screwDim_mul_numParts_sub_le_finrank_partitionMotions` with `dim W_f = D·|range f|`
(`finrank_partitionConstant`). -/
theorem screwDim_mul_range_card_sub_le_finrank_partitionMotions [Finite α] [Finite β]
    (F : BodyHingeFramework K k α β) (f : α → α)
    (hC : ∀ e ∈ F.graph.crossingEdges f, F.supportExtensor e ≠ 0) :
    (screwDim k : ℤ) * Nat.card (Set.range f)
        - (screwDim k - 1 : ℤ) * (F.graph.crossingEdges f).ncard
      ≤ (Module.finrank K (F.partitionMotions f) : ℤ) := by
  have : Fintype α := Fintype.ofFinite α
  have : Fintype ↥(F.graph.crossingEdges f) := Fintype.ofFinite _
  have hfull : Module.finrank K (LinearMap.range (F.partitionCutMap f))
      + Module.finrank K (LinearMap.ker (F.partitionCutMap f)) = screwDim k * Fintype.card α := by
    rw [LinearMap.finrank_range_add_finrank_ker, finrank_screwAssignment]
  have hrange : Module.finrank K (LinearMap.range (F.partitionCutMap f))
      ≤ screwDim k * (F.graph.crossingEdges f).ncard - (F.graph.crossingEdges f).ncard := by
    have := (LinearMap.range (F.partitionCutMap f)).finrank_le.trans_eq
      (F.finrank_partitionCutMap_codomain f hC)
    rwa [Nat.sub_mul, one_mul] at this
  have hinf : Module.finrank K (LinearMap.ker (F.partitionCutMap f))
        + Module.finrank K (partitionConstant (K := K) (k := k) f)
      ≤ Module.finrank K (F.partitionMotions f) + screwDim k * Fintype.card α := by
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.ker (F.partitionCutMap f)) (partitionConstant (k := k) f)
    rw [partitionCutMap_ker_inf] at hsup
    have hle : Module.finrank K
          (↥(LinearMap.ker (F.partitionCutMap f) ⊔ partitionConstant (k := k) f))
        ≤ screwDim k * Fintype.card α := by
      rw [← finrank_screwAssignment (K := K) (α := α) (k := k)]
      exact Submodule.finrank_le _
    omega
  -- `finrank W_f = D·|range f|` exactly.
  have hWf : screwDim k * Nat.card (Set.range f)
      = Module.finrank K (partitionConstant (K := K) (k := k) f) := by
    rw [finrank_partitionConstant]
  have hD : 1 ≤ screwDim k := Nat.choose_pos (by omega)
  have hdle : (F.graph.crossingEdges f).ncard ≤ screwDim k * (F.graph.crossingEdges f).ncard :=
    Nat.le_mul_of_pos_left _ (by omega)
  rw [sub_mul, one_mul]
  zify [hdle] at hrange ⊢
  zify at hfull hinf hWf
  omega

/-- **The relative deficiency bound** (`lem:relative-deficiency-rank-bound`): if
`bodyBarDim n = screwDim k`, `V(G)` is nonempty and the hinge is nondegenerate at the edges of `G`
that are not loops (`hC`; a loop never crosses a partition), then
`D·(|V(G)ᶜ| + 1) + def(G̃) ≤ dim Z(G,p)`, where `V(G)ᶜ` is the set of the bodies outside `V(G)`.
A partition `f₀` of the largest deficiency is relabelled by `Graph.exists_normalized_labeling` as
`g`, with the same parts and edges between parts and `|range g| = numParts f₀ + |V(G)ᶜ|`, and
the bound with `|range g|` (`screwDim_mul_range_card_sub_le_finrank_partitionMotions`) applies at
`g`. -/
theorem screwDim_mul_compl_add_deficiency_le_finrank_infinitesimalMotions
    [Finite α] [Finite β] {n : ℕ}
    (F : BodyHingeFramework K k α β)
    (hn : Graph.bodyBarDim n = screwDim k)
    (hne : F.graph.vertexSet.Nonempty)
    (hC : ∀ e u v, F.graph.IsLink e u v → u ≠ v → F.supportExtensor e ≠ 0) :
    (screwDim k : ℤ) * (F.graph.vertexSetᶜ.ncard + 1) + F.graph.deficiency n
      ≤ (Module.finrank K F.infinitesimalMotions : ℤ) := by
  have : Nonempty α := ⟨hne.some⟩
  -- Pick the def-attaining partition `f₀`, and normalize it into `V(G)`.
  obtain ⟨f₀, hf₀⟩ := exists_eq_ciSup_of_finite (f := F.graph.partitionDef n)
  rw [Graph.deficiency, ← hf₀]
  obtain ⟨g, -, -, hcross, hrange_g, -⟩ := F.graph.exists_normalized_labeling f₀
  -- Apply the `|range g|`-form motion bound.
  have hCg : ∀ e ∈ F.graph.crossingEdges g, F.supportExtensor e ≠ 0 := fun e he => by
    obtain ⟨_, x, y, hlink, hxy⟩ := he
    exact hC e x y hlink fun h => hxy (h ▸ rfl)
  have hlb := F.screwDim_mul_range_card_sub_le_finrank_partitionMotions g hCg
  have hmono : Module.finrank K (F.partitionMotions g)
      ≤ Module.finrank K F.infinitesimalMotions :=
    Submodule.finrank_mono (F.partitionMotions_le_infinitesimalMotions g)
  rw [hrange_g, hcross] at hlb
  have hDcast : (Graph.bodyBarDim n : ℤ) = (screwDim k : ℤ) := by exact_mod_cast hn
  have hpdef_eq : F.graph.partitionDef n f₀
      = (screwDim k : ℤ) * ((F.graph.numParts f₀ : ℤ) - 1)
        - (screwDim k - 1 : ℤ) * (F.graph.crossingEdges f₀).ncard := by
    simp [Graph.partitionDef, hDcast]
  zify at hmono hlb ⊢
  linarith [hpdef_eq]

end BodyHingeFramework

end CombinatorialRigidity.Molecular
