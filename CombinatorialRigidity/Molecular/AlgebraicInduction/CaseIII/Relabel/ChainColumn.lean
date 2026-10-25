/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.AlgebraicInduction.CaseIII.Relabel.Arm

/-!
# Case III: the form `r` along a chain (KT eq. (6.66))

Lemmas for Case III of KT Theorem 5.5 (Katoh and Tanigawa 2011, *A proof of the molecular
conjecture*, Discrete Comput. Geom. **45**, §6.4), presented in
`sec:molecular-algebraic-induction-caseIII`. For a chain `v₀ ⋯ v_d` with `d ≥ 3`, `2 ≤ i ≤ d − 1`,
`σ_i = shiftPerm i.castSucc` and `q_i = q ∘ σ_i`, let `hingeRow v₀ v₂ ρ₀` be a combination of rows
of `ofNormals (G − v₁) ends₀ q`. The file proves:

* that the terms of the combination at the edge `v_i v_{i+1}`, restricted to `v_i`, sum to `−ρ₀`
  (`interior_group_acolumn_eq_neg_baseRedundancy`), by induction along the chain from the relation
  at each interior vertex (`interiorGroup_acolumn_adjacency`,
  `anchor_group_acolumn_eq_baseRedundancy`, `interior_group_eq_baseRedundancy`): KT eq. (6.66),
  p. 698;
* the second claim of `lem:case-III-chain-eq666`, that `hingeRow v_{i+1} v_{i−1} (−ρ₀)` lies in the
  row space of `R(G − v_i, q_i)` (`chainData_relabel_arm_hρGv`), from the moves along the chain
  (`chainData_freshEdge_slot_mem`) and the vanishing of `ρ₀` on the hinges of the edges of the chain
  in `G − v_i` (`chainData_freshEdge_slot_perp_ends₀`).

`CaseIII/Relabel/ForkedArm.lean` proves the first claim of `lem:case-III-chain-eq666`.
-/

@[expose] public section

namespace CombinatorialRigidity.Molecular

variable {k : ℕ}

open scoped Graph

variable {α β : Type*}

variable {K : Type*} [Field K]

/-! ## The restriction of a combination of rows to a body

Steps of `lem:case-III-chain-eq666`. For a combination `∑ c_j hingeRow (uv j) (vv j) (rv j)`, the
restriction to the screw assignments that vanish off a body `a` (the composite with `single a`) is
that of its terms at `a`, as a term restricts to `0` at a body it does not meet (KT p. 691;
`edgeIndexedCombination_comp_single_eq_incident`). When each `rv j` lies in the block of rows at
`ev j`, the restriction of the terms at one label `e` to any body lies in the block at `e`
(`edgeGroup_acolumn_mem_block`). -/

/-- **The restriction to a body is that of the terms at it** (a step of `lem:case-III-chain-eq666`):
the restriction of `∑ c_j hingeRow (uv j) (vv j) (rv j)` to `a` equals that of the sum of its terms
with `a = uv j` or `a = vv j`, as every other term restricts to `0` (`hingeRow_comp_single_off`). -/
theorem BodyHingeFramework.edgeIndexedCombination_comp_single_eq_incident [DecidableEq α]
    (a : α) {n : ℕ} (c : Fin n → K) (uv vv : Fin n → α)
    (rv : Fin n → Module.Dual K (ScrewSpace K k)) :
    (∑ j, c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
        (LinearMap.single K (fun _ : α => ScrewSpace K k) a)
      = (∑ j ∈ Finset.univ.filter (fun j => a = uv j ∨ a = vv j),
          c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
        (LinearMap.single K (fun _ : α => ScrewSpace K k) a) := by
  -- Split the full sum into the `a`-incident part and the off-`a` part.
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => a = uv j ∨ a = vv j),
    LinearMap.add_comp]
  -- The off-`a` part's `a`-column vanishes: each summand has `a ≠ uv j` and `a ≠ vv j`.
  have hoff : (∑ j ∈ Finset.univ.filter (fun j => ¬ (a = uv j ∨ a = vv j)),
        c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
      (LinearMap.single K (fun _ : α => ScrewSpace K k) a) = 0 := by
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, LinearMap.coe_sum, Finset.sum_apply, LinearMap.zero_apply]
    refine Finset.sum_eq_zero fun j hj => ?_
    obtain ⟨hau, hav⟩ := not_or.mp (Finset.mem_filter.mp hj).2
    rw [LinearMap.smul_apply, ← LinearMap.comp_apply,
      BodyHingeFramework.hingeRow_comp_single_off hau hav, LinearMap.zero_apply, smul_zero]
  rw [hoff, add_zero]

/-- **The terms at one label, restricted to a body, lie in its block** (a step of
`lem:case-III-chain-eq666`): if each `rv j` lies in the block of rows of `Fva` at `ev j` (`hrv`),
then for every label `e` and body `p`, the restriction to `p` of the sum of the terms with
`ev j = e` lies in the block of rows of `Fva` at `e`. Each such term restricts to `rv j`, `−rv j` or
`0`, as `p` is `uv j`, `vv j` or neither (`hingeRow_comp_single_tail`, `hingeRow_swap`,
`hingeRow_comp_single_off`; the term is `0` when `uv j = vv j`), and the block is a subspace. No
link is assumed. `chainData_freshEdge_perp_of_baseRedundancy` and
`baseRedundancy_perp_interior_reproduced_panel` (`CaseIII/Relabel/ForkedArm.lean`) apply it where
the sum is `−ρ₀`. -/
theorem BodyHingeFramework.edgeGroup_acolumn_mem_block [DecidableEq α] [DecidableEq β]
    {Fva : BodyHingeFramework K k α β} {e : β} {p : α}
    {m : ℕ} (c : Fin m → K) (ev : Fin m → β) (uv vv : Fin m → α)
    (rv : Fin m → Module.Dual K (ScrewSpace K k))
    (hrv : ∀ j, rv j ∈ Fva.hingeRowBlock (ev j)) :
    (∑ j ∈ Finset.univ.filter (fun j => ev j = e),
        c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
      (LinearMap.single K (fun _ : α => ScrewSpace K k) p) ∈ Fva.hingeRowBlock e := by
  classical
  -- Distribute the column restriction over the filtered sum, then close by the block's submodule
  -- closure (`sum_mem`/`smul_mem`).
  rw [show (∑ j ∈ Finset.univ.filter (fun j => ev j = e),
        c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
        (LinearMap.single K (fun _ : α => ScrewSpace K k) p)
      = ∑ j ∈ Finset.univ.filter (fun j => ev j = e),
          (c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
          (LinearMap.single K (fun _ : α => ScrewSpace K k) p)
      from LinearMap.ext fun x => by
        simp only [LinearMap.comp_apply, LinearMap.coe_sum, Finset.sum_apply]]
  refine Submodule.sum_mem _ fun j hj => ?_
  have hje : ev j = e := (Finset.mem_filter.mp hj).2
  -- the summand's row `rv j ∈ block e` (after `ev j = e`).
  have hrvj : rv j ∈ Fva.hingeRowBlock e := hje ▸ hrv j
  -- distribute the column over the scalar.
  rw [LinearMap.smul_comp]
  refine Submodule.smul_mem _ _ ?_
  -- read the column as `±rv j` (tail / swapped tail) or `0` (off both endpoints), each a block
  -- member (the block is a submodule, neg-/zero-closed). Loop-safe: `p = uv j = vv j` gives a zero
  -- hinge row (`hingeRow x x ρ = 0`).
  by_cases hpu : p = uv j
  · by_cases hpv : p = vv j
    · -- `p = uv j = vv j`: `hingeRow (uv j) (vv j) (rv j) = hingeRow p p (rv j)`, a zero row.
      have hzero : BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)
          = (0 : Module.Dual K (α → ScrewSpace K k)) := by
        rw [← hpu, ← hpv]
        exact LinearMap.ext fun x => by simp only [BodyHingeFramework.hingeRow_apply, sub_self,
          map_zero, LinearMap.zero_apply]
      rw [hzero, LinearMap.zero_comp]
      exact (Fva.hingeRowBlock e).zero_mem
    · -- `p = uv j ≠ vv j`: tail column is `rv j`.
      rw [hpu, BodyHingeFramework.hingeRow_comp_single_tail (hpu ▸ hpv)]
      exact hrvj
  · by_cases hpv : p = vv j
    · -- `p = vv j ≠ uv j`: swap to `hingeRow (vv j) (uv j) (−rv j)`, tail column is `−rv j`.
      have hvu : vv j ≠ uv j := fun he => hpu (hpv.trans he)
      rw [hpv, BodyHingeFramework.hingeRow_swap (uv j) (vv j) (rv j),
        BodyHingeFramework.hingeRow_comp_single_tail hvu]
      exact (Fva.hingeRowBlock e).neg_mem hrvj
    · -- `p` off both endpoints: zero column.
      rw [BodyHingeFramework.hingeRow_comp_single_off hpu hpv]
      exact (Fva.hingeRowBlock e).zero_mem

/-! ## KT eq. (6.66) along the chain: the relation at an interior vertex

Steps of `lem:case-III-chain-eq666`. Let `∑ c_j hingeRow (uv j) (vv j) (rv j)` be
`hingeRow v₀ v₂ ρ₀`, each `ev j` joining `uv j` and `vv j` in `G`. At an interior vertex `v_i`, the
terms at `v_i` are at the two edges `v_{i−1} v_i` and `v_i v_{i+1}`, the only edges of `G` there. If
`v_i` is neither `v₀` nor `v₂`, the restriction of the combination to `v_i` vanishes, so the terms
at the two edges restrict at `v_i` to opposite forms (`interiorGroup_acolumn_adjacency`), as in the
proof of KT eq. (6.44) (p. 691). With the relation at `v₂` and the induction along the chain in the
next sections, this gives KT eq. (6.66) (p. 698): the terms at `v_i v_{i+1}`, restricted to `v_i`,
sum to `−ρ₀` (`interior_group_acolumn_eq_neg_baseRedundancy`). -/

/-- **The relation at an interior vertex** (a step of `lem:case-III-chain-eq666`; as KT eq. (6.44),
p. 691, at `v_i`): for `1 ≤ i ≤ d − 1`, let each `ev j` join `uv j` and `vv j` in `G` (`hlink`), and
let the restriction of `∑ c_j hingeRow (uv j) (vv j) (rv j)` to `v_i` vanish (`hcol`). Then the
restriction to `v_i` of the sum of the terms at `v_i v_{i+1}` is minus that of the terms at
`v_{i−1} v_i`. The terms at `v_i` are those at the two edges, the only edges of `G` at `v_i`
(`ChainData.deg_two_split`), which are distinct (`edge_inj`), so the restriction of the combination
is the sum of the two (`edgeIndexedCombination_comp_single_eq_incident`). -/
theorem _root_.Graph.ChainData.interiorGroup_acolumn_adjacency [DecidableEq α] [DecidableEq β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) {i : Fin cd.d} (hi : 0 < (i : ℕ))
    {m : ℕ} (c : Fin m → K) (ev : Fin m → β) (uv vv : Fin m → α)
    (rv : Fin m → Module.Dual K (ScrewSpace K k))
    (hlink : ∀ j, G.IsLink (ev j) (uv j) (vv j))
    (hcol : (∑ j, c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
        (LinearMap.single K (fun _ : α => ScrewSpace K k) (cd.vtx i.castSucc)) = 0) :
    (∑ j ∈ Finset.univ.filter (fun j => ev j = cd.edge i),
        c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
      (LinearMap.single K (fun _ : α => ScrewSpace K k) (cd.vtx i.castSucc))
    = -(∑ j ∈ Finset.univ.filter (fun j => ev j = cd.edge ⟨(i : ℕ) - 1, by omega⟩),
        c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
      (LinearMap.single K (fun _ : α => ScrewSpace K k) (cd.vtx i.castSucc)) := by
  classical
  set a := cd.vtx i.castSucc with ha
  set ei := cd.edge i with hei
  set ep := cd.edge ⟨(i : ℕ) - 1, by omega⟩ with hep
  -- The two chain edges are distinct (`edge_inj`); each is a `G`-link incident to `a`.
  have hep_ne_ei : ep ≠ ei := (cd.pred_edge_ne hi)
  have hlink_ei : G.IsLink ei a (cd.vtx i.succ) := cd.isLink_succ_edge i
  have hlink_ep : G.IsLink ep a (cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc) :=
    cd.isLink_pred_edge hi
  -- A term at `edge i` (resp. `edge (i−1)`) meets `a` (the ends of the edge).
  have hinc_ei : ∀ j, ev j = ei → a = uv j ∨ a = vv j := fun j hj =>
    (((hlink j).symm.eq_and_eq_or_eq_and_eq (hj ▸ hlink_ei)).imp (·.1.symm) (·.2.symm)).symm
  have hinc_ep : ∀ j, ev j = ep → a = uv j ∨ a = vv j := fun j hj =>
    (((hlink j).symm.eq_and_eq_or_eq_and_eq (hj ▸ hlink_ep)).imp (·.1.symm) (·.2.symm)).symm
  -- Every term at `a` is at `edge i` or `edge (i−1)` (the two edges at the interior vertex).
  have hdeg : ∀ j, (a = uv j ∨ a = vv j) → ev j = ei ∨ ev j = ep := by
    intro j hj
    rcases hj with h | h
    · refine cd.deg_two_split hi (ev j) (vv j) ?_
      rw [← ha, h]; exact hlink j
    · refine cd.deg_two_split hi (ev j) (uv j) ?_
      rw [← ha, h]; exact (hlink j).symm
  -- The `a`-column of `g` is that of its `a`-incident sub-combination (`_eq_incident`); rewrite the
  -- vanishing `hcol` accordingly.
  rw [BodyHingeFramework.edgeIndexedCombination_comp_single_eq_incident a c uv vv rv] at hcol
  -- Partition the incident index set by `ev = edge i`: the `edge i`-part is the `edge i`-group, the
  -- complement (within incident) is the `edge (i−1)`-group (deg-2 closure + `edge_inj` disjoint).
  rw [← Finset.sum_filter_add_sum_filter_not
      (Finset.univ.filter (fun j => a = uv j ∨ a = vv j)) (fun j => ev j = ei),
    LinearMap.add_comp] at hcol
  have he_ei : (Finset.univ.filter (fun j => a = uv j ∨ a = vv j)).filter (fun j => ev j = ei)
      = Finset.univ.filter (fun j => ev j = ei) := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun j _ => ?_
    exact ⟨fun h => h.2, fun h => ⟨hinc_ei j h, h⟩⟩
  have he_ep : (Finset.univ.filter (fun j => a = uv j ∨ a = vv j)).filter (fun j => ¬ ev j = ei)
      = Finset.univ.filter (fun j => ev j = ep) := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun j _ => ?_
    constructor
    · rintro ⟨hinc, hni⟩
      exact (hdeg j hinc).resolve_left hni
    · rintro hj
      exact ⟨hinc_ep j hj, fun h => hep_ne_ei (hj ▸ h)⟩
  rw [he_ei, he_ep] at hcol
  exact eq_neg_of_add_eq_zero_left hcol

/-! ## The relation at `v₂`

In `G − v₁` the edge `v₁v₂` is gone, so the terms of a combination of rows of `G − v₁` that meet
`v₂` are at `v₂v₃` (`hdeg1`). The terms at `v₂v₃`, restricted to `v₂`, are then the restriction of
the combination, that of `hingeRow ab₁ ab₂ ρ₀` (`anchor_group_acolumn_eq_baseRedundancy`): with
`ab₂ = v₂`, the form `−ρ₀`. This starts the induction. -/

/-- **The relation at `v₂`** (a step of `lem:case-III-chain-eq666`): for `d ≥ 3`, let
`∑ c_j hingeRow (uv j) (vv j) (rv j)` be `hingeRow ab₁ ab₂ ρ₀` (`hcomb`), with each `ev j` joining
`uv j` and `vv j` in `G` (`hlink`), and let every term at `v₂` be at `v₂v₃` (`hdeg1`). Then the
restriction to `v₂` of the terms at `v₂v₃` equals that of `hingeRow ab₁ ab₂ ρ₀`: the terms at `v₂`
are those at `v₂v₃`, by `hdeg1` and as `v₂v₃` meets `v₂`, and
`edgeIndexedCombination_comp_single_eq_incident` applies. -/
theorem _root_.Graph.ChainData.anchor_group_acolumn_eq_baseRedundancy [DecidableEq α]
    [DecidableEq β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (h3 : 3 ≤ cd.d)
    {m : ℕ} (c : Fin m → K) (ev : Fin m → β) (uv vv : Fin m → α)
    (rv : Fin m → Module.Dual K (ScrewSpace K k))
    {ab₁ ab₂ : α} {ρ₀ : Module.Dual K (ScrewSpace K k)}
    (hlink : ∀ j, G.IsLink (ev j) (uv j) (vv j))
    (hcomb : (∑ j, c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j))
      = BodyHingeFramework.hingeRow ab₁ ab₂ ρ₀)
    (hdeg1 : ∀ j, (cd.vtx ⟨2, by omega⟩ = uv j ∨ cd.vtx ⟨2, by omega⟩ = vv j) →
      ev j = cd.edge ⟨2, by omega⟩) :
    (∑ j ∈ Finset.univ.filter (fun j => ev j = cd.edge ⟨2, by omega⟩),
        c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
      (LinearMap.single K (fun _ : α => ScrewSpace K k) (cd.vtx ⟨2, by omega⟩))
    = (BodyHingeFramework.hingeRow ab₁ ab₂ ρ₀).comp
      (LinearMap.single K (fun _ : α => ScrewSpace K k) (cd.vtx ⟨2, by omega⟩)) := by
  classical
  set a := cd.vtx ⟨2, by omega⟩ with ha
  set e2 := cd.edge ⟨2, by omega⟩ with he2
  -- `edge 2` links `vtx 2 — vtx 3` in `G` (`link ⟨2,_⟩`): a `G`-link incident to `a = vtx 2`.
  have hlink_e2 : G.IsLink e2 a (cd.vtx ⟨3, by omega⟩) := by
    have h := cd.link ⟨2, by omega⟩
    simpa only [he2, ha, Fin.castSucc_mk, Fin.succ_mk] using h
  -- A term at `edge 2` meets `a` (its ends are those of `edge 2`, by `IsLink` uniqueness).
  have hinc_e2 : ∀ j, ev j = e2 → a = uv j ∨ a = vv j := fun j hj =>
    (((hlink j).symm.eq_and_eq_or_eq_and_eq (hj ▸ hlink_e2)).imp (·.1.symm) (·.2.symm)).symm
  -- The `a`-incident index set equals the `edge 2`-index set: `⊆` by the degree-1 closure `hdeg1`,
  -- `⊇` by `hinc_e2`.
  have hset : Finset.univ.filter (fun j => a = uv j ∨ a = vv j)
      = Finset.univ.filter (fun j => ev j = e2) := by
    refine Finset.filter_congr fun j _ => ?_
    exact ⟨fun h => hdeg1 j h, fun h => hinc_e2 j h⟩
  -- The `a`-column of `g = hingeRow ab₁ ab₂ ρ₀` is that of its `a`-incident sub-combination
  -- (`_eq_incident`); `hset` rewrites the incident set to the `edge 2`-set.
  rw [← hcomb, BodyHingeFramework.edgeIndexedCombination_comp_single_eq_incident a c uv vv rv, hset]

/-! ## The induction along the chain

A form `hingeRow x y ρ` restricts to `ρ` at `x` and to `−ρ` at `y`
(`hingeRow_comp_single_endpoint_flip`), so the terms at an edge restrict to opposite forms at its
two ends (`edgeGroup_comp_single_endpoint_flip`). With the relation at `v_{i+1}`, the restriction to
`v_{i+1}` of the terms at `v_{i+1} v_{i+2}` is then the restriction to `v_i` of those at
`v_i v_{i+1}` (`interior_group_eq_baseRedundancy`). -/

/-- **A form at a pair restricts to opposite forms at its two ends** (a step of
`lem:case-III-chain-eq666`): for `x ≠ y`, the restriction of `hingeRow x y ρ` to `y` is minus its
restriction to `x`, as they are `−ρ` and `ρ` (`hingeRow_comp_single_tail`, `hingeRow_swap`). -/
theorem BodyHingeFramework.hingeRow_comp_single_endpoint_flip [DecidableEq α] {x y : α}
    (hxy : x ≠ y) (ρ : Module.Dual K (ScrewSpace K k)) :
    (BodyHingeFramework.hingeRow (k := k) (α := α) x y ρ).comp
        (LinearMap.single K (fun _ : α => ScrewSpace K k) y)
      = -(BodyHingeFramework.hingeRow (k := k) (α := α) x y ρ).comp
        (LinearMap.single K (fun _ : α => ScrewSpace K k) x) := by
  rw [BodyHingeFramework.hingeRow_comp_single_tail hxy,
    BodyHingeFramework.hingeRow_swap x y ρ,
    BodyHingeFramework.hingeRow_comp_single_tail (Ne.symm hxy)]

/-- **The terms at one edge restrict to opposite forms at its two ends** (a step of
`lem:case-III-chain-eq666`): let `e` join `p ≠ q` in `G`, and let each `ev j` join `uv j` and `vv j`
in `G` (`hlink`). Then the restriction to `q` of the sum of the terms at `e` is minus its
restriction to `p`: each such term is at the pair `p`, `q` in one order or the other, and
`hingeRow_comp_single_endpoint_flip` applies. -/
theorem BodyHingeFramework.edgeGroup_comp_single_endpoint_flip [DecidableEq α] [DecidableEq β]
    {G : Graph α β} {e : β} {p q : α} (hpq : p ≠ q) (hpq_link : G.IsLink e p q)
    {m : ℕ} (c : Fin m → K) (ev : Fin m → β) (uv vv : Fin m → α)
    (rv : Fin m → Module.Dual K (ScrewSpace K k))
    (hlink : ∀ j, G.IsLink (ev j) (uv j) (vv j)) :
    (∑ j ∈ Finset.univ.filter (fun j => ev j = e),
        c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
      (LinearMap.single K (fun _ : α => ScrewSpace K k) q)
    = -(∑ j ∈ Finset.univ.filter (fun j => ev j = e),
        c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
      (LinearMap.single K (fun _ : α => ScrewSpace K k) p) := by
  classical
  -- Reduce the `LinearMap` equality to scalar equality at each `x`, distribute the column
  -- restriction over the filtered sum on both sides, and compare per summand.
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.coe_sum, Finset.sum_apply]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  -- The term `j` is at `e`, so its ends are `p` and `q` (`IsLink` uniqueness).
  have hje : ev j = e := (Finset.mem_filter.mp hj).2
  have hjlink : G.IsLink e (uv j) (vv j) := hje ▸ hlink j
  -- Its endpoints are `{p, q}` in one of the two orders; the per-summand endpoint-column flip
  -- (`hingeRow_comp_single_endpoint_flip`) gives the per-summand negation either way.
  have hflip : (BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
        (LinearMap.single K (fun _ : α => ScrewSpace K k) q)
      = -(BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
        (LinearMap.single K (fun _ : α => ScrewSpace K k) p) := by
    rcases (hpq_link.eq_and_eq_or_eq_and_eq hjlink) with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · -- `p = uv j`, `q = vv j`: the flip `col@q = −col@p` at endpoints `(uv j, vv j)`.
      subst hp hq
      exact BodyHingeFramework.hingeRow_comp_single_endpoint_flip hpq (rv j)
    · -- `p = vv j`, `q = uv j`: the flip at `(uv j, vv j)` gives `col@(vv j) = −col@(uv j)`; the
      -- goal `col@(uv j) = −col@(vv j)` is its `neg`-flipped form.
      subst hp hq
      rw [BodyHingeFramework.hingeRow_comp_single_endpoint_flip (Ne.symm hpq) (rv j), neg_neg]
  rw [LinearMap.smul_apply, LinearMap.smul_apply, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
    hflip, LinearMap.neg_apply, smul_neg]

/-- **The induction along the chain** (a step of `lem:case-III-chain-eq666`; KT eq. (6.66), p. 698):
for `d ≥ 3`, let `∑ c_j hingeRow (uv j) (vv j) (rv j)` be `hingeRow v₀ v₂ ρ₀` (`hcomb`), with each
`ev j` joining `uv j` and `vv j` in `G` (`hlink`), and let every term at `v₂` be at `v₂v₃`
(`hdeg1`). Then for `2 ≤ i ≤ d − 1`, the restriction to `v_i` of the sum of the terms at
`v_i v_{i+1}` equals the restriction of `hingeRow v₀ v₂ ρ₀` to `v₂`.

By induction on `i` from `anchor_group_acolumn_eq_baseRedundancy`. The vertex `v_{i+1}` is neither
`v₀` nor `v₂`, so the restriction of `hingeRow v₀ v₂ ρ₀` to it vanishes
(`hingeRow_comp_single_off`); the terms at `v_{i+1} v_{i+2}` then restrict there to minus those at
`v_i v_{i+1}` (`interiorGroup_acolumn_adjacency`), which restrict at `v_{i+1}` to minus their
restriction at `v_i` (`edgeGroup_comp_single_endpoint_flip`). The vanishing holds only off `v₀` and
`v₂`: at `v₂` the restriction of `hingeRow v₀ v₂ ρ₀` is `−ρ₀`. -/
theorem _root_.Graph.ChainData.interior_group_eq_baseRedundancy [DecidableEq α] [DecidableEq β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (h3 : 3 ≤ cd.d)
    {m : ℕ} (c : Fin m → K) (ev : Fin m → β) (uv vv : Fin m → α)
    (rv : Fin m → Module.Dual K (ScrewSpace K k))
    {ρ₀ : Module.Dual K (ScrewSpace K k)}
    (hlink : ∀ j, G.IsLink (ev j) (uv j) (vv j))
    (hcomb : (∑ j, c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j))
      = BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ₀)
    (hdeg1 : ∀ j, (cd.vtx ⟨2, by omega⟩ = uv j ∨ cd.vtx ⟨2, by omega⟩ = vv j) →
      ev j = cd.edge ⟨2, by omega⟩)
    (i : ℕ) (h2i : 2 ≤ i) (hid : i < cd.d) :
    (∑ j ∈ Finset.univ.filter (fun j => ev j = cd.edge ⟨i, by omega⟩),
        c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
      (LinearMap.single K (fun _ : α => ScrewSpace K k) (cd.vtx ⟨i, by omega⟩))
    = (BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ₀).comp
      (LinearMap.single K (fun _ : α => ScrewSpace K k) (cd.vtx ⟨2, by omega⟩)) := by
  classical
  induction i, h2i using Nat.le_induction with
  | base =>
    exact cd.anchor_group_acolumn_eq_baseRedundancy h3 c ev uv vv rv hlink hcomb hdeg1
  | succ i h2i ih =>
    -- `i + 1 < cd.d` (the current bound); `i` is in range for the induction hypothesis.
    have hid' : i < cd.d := by omega
    -- The vertex `vtx (i+1)` (`i+1 ≥ 3`) is neither `vtx 0` nor `vtx 2` (`vtx_ne`).
    have hne₁ : cd.vtx (⟨i + 1, by omega⟩ : Fin cd.d).castSucc ≠ cd.vtx ⟨0, by omega⟩ :=
      cd.vtx_ne (m := i + 1) _ _ (by omega)
    have hne₂ : cd.vtx (⟨i + 1, by omega⟩ : Fin cd.d).castSucc ≠ cd.vtx ⟨2, by omega⟩ :=
      cd.vtx_ne (m := i + 1) _ _ (by omega)
    -- The restriction of the combination to `vtx (i+1)` vanishes: it is that of
    -- `hingeRow (vtx 0) (vtx 2) ρ₀`, and `vtx (i+1)` is neither end (`hingeRow_comp_single_off`).
    have hcol_loc : (∑ j, c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
        (LinearMap.single K (fun _ : α => ScrewSpace K k)
          (cd.vtx (⟨i + 1, by omega⟩ : Fin cd.d).castSucc)) = 0 := by
      rw [hcomb, BodyHingeFramework.hingeRow_comp_single_off hne₁ hne₂]
    -- `interiorGroup_acolumn_adjacency` at `vtx (i+1)` (index `⟨i+1, _⟩ : Fin cd.d`, `0 < i+1`):
    -- the terms at `edge (i+1)` restrict there to minus those at `edge i`.
    have hadj := cd.interiorGroup_acolumn_adjacency (i := ⟨i + 1, by omega⟩) (by simp)
      c ev uv vv rv hlink (by simpa using hcol_loc)
    -- Index arithmetic: `⟨i+1,_⟩.castSucc = ⟨i+1,_⟩`, `⟨(i+1)−1,_⟩ = ⟨i,_⟩`.
    have hcs : (⟨i + 1, by omega⟩ : Fin cd.d).castSucc = (⟨i + 1, by omega⟩ : Fin (cd.d + 1)) :=
      Fin.ext rfl
    have hpred : (⟨(i + 1 : ℕ) - 1, by omega⟩ : Fin cd.d) = (⟨i, by omega⟩ : Fin cd.d) :=
      Fin.ext (by simp)
    rw [hcs, hpred] at hadj
    -- `edge i` links `vtx i — vtx (i+1)` (`cd.link ⟨i,_⟩`), with the two endpoints distinct.
    have hlink_i : G.IsLink (cd.edge ⟨i, by omega⟩) (cd.vtx ⟨i, by omega⟩)
        (cd.vtx ⟨i + 1, by omega⟩) := by
      have h := cd.link (⟨i, by omega⟩ : Fin cd.d)
      simpa only [Fin.castSucc_mk, Fin.succ_mk] using h
    have hpq : (cd.vtx ⟨i, by omega⟩ : α) ≠ cd.vtx ⟨i + 1, by omega⟩ :=
      cd.vtx_ne (by omega) (by omega) (by omega)
    -- The terms at `edge i` restrict at their head `vtx (i+1)` to minus their restriction at their
    -- tail `vtx i`, which cancels the sign of `hadj`.
    have hflip := BodyHingeFramework.edgeGroup_comp_single_endpoint_flip
      (e := cd.edge ⟨i, by omega⟩) hpq hlink_i c ev uv vv rv hlink
    -- `colTail (i+1) = −(edge i-group @ vtx (i+1)) = −(−(edge i-group @ vtx i)) = colTail i = RHS`.
    rw [hadj, hflip, neg_neg]
    exact ih hid'

/-! ## The value `−ρ₀`

The restriction of `hingeRow v₀ v₂ ρ₀` to `v₂` is `−ρ₀` (`hingeRow_swap`,
`hingeRow_comp_single_tail`), so the terms at every edge `v_i v_{i+1}` with `2 ≤ i ≤ d − 1`,
restricted to `v_i`, sum to `−ρ₀`. This is KT eq. (6.66) (p. 698), where Katoh and Tanigawa write
`±r`, the sign depending on the orientations. -/

/-- **The terms at `v_i v_{i+1}`, restricted to `v_i`, sum to `−ρ₀`** (a step of
`lem:case-III-chain-eq666`; KT eq. (6.66), p. 698): under the hypotheses of
`interior_group_eq_baseRedundancy`, for `2 ≤ i ≤ d − 1`, the restriction to `v_i` of the sum of the
terms at `v_i v_{i+1}` is `−ρ₀`, the restriction of `hingeRow v₀ v₂ ρ₀` to `v₂`. -/
theorem _root_.Graph.ChainData.interior_group_acolumn_eq_neg_baseRedundancy [DecidableEq α]
    [DecidableEq β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (h3 : 3 ≤ cd.d)
    {m : ℕ} (c : Fin m → K) (ev : Fin m → β) (uv vv : Fin m → α)
    (rv : Fin m → Module.Dual K (ScrewSpace K k))
    {ρ₀ : Module.Dual K (ScrewSpace K k)}
    (hlink : ∀ j, G.IsLink (ev j) (uv j) (vv j))
    (hcomb : (∑ j, c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j))
      = BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ₀)
    (hdeg1 : ∀ j, (cd.vtx ⟨2, by omega⟩ = uv j ∨ cd.vtx ⟨2, by omega⟩ = vv j) →
      ev j = cd.edge ⟨2, by omega⟩)
    (i : ℕ) (h2i : 2 ≤ i) (hid : i < cd.d) :
    (∑ j ∈ Finset.univ.filter (fun j => ev j = cd.edge ⟨i, by omega⟩),
        c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
      (LinearMap.single K (fun _ : α => ScrewSpace K k) (cd.vtx ⟨i, by omega⟩))
    = -ρ₀ := by
  classical
  -- `interior_group_eq_baseRedundancy`: the restriction is that of `hingeRow (vtx 0) (vtx 2) ρ₀`
  -- to `vtx 2`. That form is `hingeRow (vtx 2) (vtx 0) (−ρ₀)` (`hingeRow_swap`), whose restriction
  -- to `vtx 2` is `−ρ₀` (`hingeRow_comp_single_tail`), as `vtx 2 ≠ vtx 0` (`vtx_ne`).
  rw [cd.interior_group_eq_baseRedundancy h3 c ev uv vv rv hlink hcomb hdeg1 i h2i hid,
    BodyHingeFramework.hingeRow_swap,
    BodyHingeFramework.hingeRow_comp_single_tail (cd.vtx_ne _ _ (by omega))]

/-! ## The normals of the moves

Steps of `lem:case-III-chain-eq666`. After `i − 1` steps, the moves along the chain have the normals
`shiftSeedAdv q (i − 1)`, which are `q` composed with the product of the transpositions of the steps
(`shiftSeedAdv_eq_prod_shiftSeedSwap`). That product is `σ_i = shiftPerm i.castSucc`
(`shiftPerm_eq_prod_map_swap_shiftBodyListAsc`), so the normals are `q_i = q ∘ σ_i`
(`shiftSeedAdv_eq_funLeft_shiftPerm`). -/

omit [Field K] in
/-- **The normals after `s` steps, as one renaming** (a step of `lem:case-III-chain-eq666`):
`shiftSeedAdv q s` is `q` composed, on the bodies, with the product
`shiftSeedSwap 0 * ⋯ * shiftSeedSwap (s − 1)`. By induction on `s`, the last factor taken off by
`List.ofFn_succ'` and `List.prod_concat`. -/
theorem _root_.Graph.ChainData.shiftSeedAdv_eq_prod_shiftSeedSwap [DecidableEq α]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (q : α × Fin (k + 2) → K) (s : ℕ) :
    cd.shiftSeedAdv q s
      = fun p => q ((List.ofFn fun t : Fin s => cd.shiftSeedSwap t).prod p.1, p.2) := by
  induction s with
  | zero => simp only [Graph.ChainData.shiftSeedAdv_zero, List.ofFn_zero, List.prod_nil,
      Equiv.Perm.coe_one, _root_.id, Prod.mk.eta]
  | succ s ih =>
    rw [Graph.ChainData.shiftSeedAdv_succ, ih]
    funext p
    -- `ofFn` (over `Fin (s+1)`) peels the last swap off the right (`ofFn_succ'`), and the product
    -- of a `concat` head-applies the trailing swap (`(P * swap) x = P (swap x)`), matching
    -- `shiftSeedAdv`'s recursion `Q (s+1) p = Q s (swap p.1, p.2)`.
    rw [List.ofFn_succ', List.prod_concat]
    simp only [Fin.val_last, Equiv.Perm.coe_mul, Function.comp_apply, Fin.val_castSucc]

omit [Field K] in
/-- **The normals after `i − 1` steps are `q ∘ σ_i`** (a step of `lem:case-III-chain-eq666`): for
`1 ≤ i ≤ d − 1`, `shiftSeedAdv q (i − 1)` is `q ∘ σ_i` (`fun p => q (σ_i p.1, p.2)`) for
`σ_i = shiftPerm i.castSucc`, the normals `q_i` of KT eq. (6.55) (p. 694). The product of the
transpositions (`shiftSeedAdv_eq_prod_shiftSeedSwap`) is `σ_i`
(`shiftPerm_eq_prod_map_swap_shiftBodyListAsc`), as `shiftSeedSwap s` is the transposition of the
step `s` of `shiftBodyListAsc i` (`getElem_shiftBodyListAsc`, `shiftSeedSwap_eq`). -/
theorem _root_.Graph.ChainData.shiftSeedAdv_eq_funLeft_shiftPerm [DecidableEq α]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (q : α × Fin (k + 2) → K) (i : Fin cd.d)
    (hi : 1 ≤ (i : ℕ)) :
    cd.shiftSeedAdv q ((i : ℕ) - 1)
      = fun p => q (cd.shiftPerm i.castSucc p.1, p.2) := by
  rw [cd.shiftSeedAdv_eq_prod_shiftSeedSwap q ((i : ℕ) - 1)]
  -- The product of the `i − 1` transpositions is `shiftPerm i.castSucc`
  -- (`shiftPerm_eq_prod_map_swap_shiftBodyListAsc`), once the transpositions are matched one by one
  -- (`shiftSeedSwap s = swap (vₛ₊₂) (vₛ₊₁)`).
  have hlist : (List.ofFn fun t : Fin ((i : ℕ) - 1) => cd.shiftSeedSwap t)
      = (cd.shiftBodyListAsc i).map (fun b => Equiv.swap b.2.1 b.1) := by
    refine List.ext_getElem (by simp only [List.length_ofFn, List.length_map,
      cd.length_shiftBodyListAsc]) fun s h₁ h₂ => ?_
    simp only [List.getElem_ofFn, List.getElem_map, cd.getElem_shiftBodyListAsc]
    have hs : s + 2 < cd.d + 1 := by
      simp only [List.length_ofFn] at h₁; have := i.2; omega
    rw [cd.shiftSeedSwap_eq hs]
  rw [hlist, ← cd.shiftPerm_eq_prod_map_swap_shiftBodyListAsc i]

/-! ## The form at the new edge of `G_i`, from the moves

A step of `lem:case-III-chain-eq666`. The moves along the chain take `hingeRow v₀ v₂ ρ₀` from the
row space of `G − v₁` into that of `G − v_i` (`shiftBodyListAsc_foldl_mem_span_rigidityRows`), where
it is the sum of the forms `hingeRow v_s v_{s+1} ρ₀` at the edges of the chain, `s < i − 1`, and the
form `hingeRow v_{i−1} v_{i+1} ρ₀` at the new edge of `G_i` (`wstep_foldl_freshEdge_slot_mem`). -/

/-- **The form at the new edge of `G_i` lies in the row space of `G − v_i`** (a step of
`lem:case-III-chain-eq666`): for `1 ≤ i ≤ d − 1`, let `ends` give each link of `G` its ends in some
order (`hrec`), let `hingeRow v₀ v₂ ρ₀` lie in the span of the rows of `ofNormals (G − v₁) ends q`
(`hφ`), and let `ρ₀` vanish on the hinge of `F = ofNormals (G − v_i) ends (shiftSeedAdv q (i − 1))`
at each edge `v_s v_{s+1}` with `s + 1 < i` (`hperp`). Then `hingeRow v_{i−1} v_{i+1} ρ₀` lies in
the span of the rows of `F`.

The moves put `hingeRow v₀ v₂ ρ₀` in the row space of `F`, as the sum of the forms
`hingeRow v_s v_{s+1} ρ₀`, `s < i − 1`, and `hingeRow v_{i−1} v_{i+1} ρ₀`; the first are rows of `F`
by `hperp` (`freshEdge_surviving_row_mem`), so the last lies in the row space. Katoh and Tanigawa
make this step with the row correspondence of KT eq. (6.62) and the row operations of KT eq. (6.63)
(pp. 696–697). `chainData_relabel_arm_hρGv` applies it with the selector `ends₀`. -/
theorem _root_.Graph.ChainData.chainData_freshEdge_slot_mem [DecidableEq α]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (i : Fin (cd.d + 1))
    (hi : 1 ≤ (i : ℕ)) (hid : (i : ℕ) < cd.d)
    (ends : β → α × α) (q : α × Fin (k + 2) → K)
    (hrec : ∀ f x y, G.IsLink f x y → ends f = (x, y) ∨ ends f = (y, x))
    {ρ₀ : Module.Dual K (ScrewSpace K k)}
    -- `hingeRow (vtx 0) (vtx 2) ρ₀` in the row space of `G − v₁`:
    (hφ : BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ₀ ∈
      Submodule.span K
        (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩)) ends
          (cd.shiftSeedAdv q 0)).toBodyHinge.rigidityRows)
    -- `ρ₀` vanishes on the hinge of each edge `v_s v_{s+1}` of `G − vᵢ`, `s + 1 < i`:
    (hperp : ∀ s : ℕ, (hs : s + 1 < (i : ℕ)) → ρ₀ ((PanelHingeFramework.ofNormals
        (G.removeVertex (cd.vtx ⟨(i : ℕ), by omega⟩)) ends
          (cd.shiftSeedAdv q ((i : ℕ) - 1))).toBodyHinge.supportExtensor
          (cd.edge ⟨s, by omega⟩)) = 0) :
    BodyHingeFramework.hingeRow (cd.vtx ⟨(i : ℕ) - 1, by omega⟩) (cd.vtx ⟨(i : ℕ) + 1, by omega⟩) ρ₀
      ∈ Submodule.span K (PanelHingeFramework.ofNormals
        (G.removeVertex (cd.vtx ⟨(i : ℕ), by omega⟩)) ends
          (cd.shiftSeedAdv q ((i : ℕ) - 1))).toBodyHinge.rigidityRows := by
  classical
  have hG := PanelHingeFramework.RecordsLinks.of_pair hrec
  -- `i` as an element of `Fin cd.d`, for `shiftBodyListAsc_foldl_mem_span_rigidityRows`.
  let i' : Fin cd.d := ⟨(i : ℕ), hid⟩
  have hi'v : (i' : ℕ) = (i : ℕ) := rfl
  -- the framework `Fva = ofNormals (G − vᵢ) ends (shiftSeedAdv q (i−1))`.
  set Fva := (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨(i : ℕ), by omega⟩)) ends
    (cd.shiftSeedAdv q ((i : ℕ) - 1))).toBodyHinge with hFva
  -- the `ℕ → α` vertex function for the telescope: `w s = vtx (min s d)` (agrees with `vtx s` on
  -- the range `[0, i+1] ⊆ [0, d]` the fold touches).
  let w : ℕ → α := fun s => cd.vtx ⟨min s cd.d, Nat.lt_succ_of_le (min_le_right s cd.d)⟩
  have hws : ∀ s : ℕ, (h : s < cd.d + 1) → s ≤ cd.d → w s = cd.vtx ⟨s, h⟩ := by
    intro s h hs; exact congrArg cd.vtx (Fin.ext (min_eq_left hs))
  -- `w` is injective on `[0, (i−1)+2] = [0, i+1] ⊆ [0, d]` (`vtx_inj` + `min` collapse).
  have hinj : Set.InjOn w (Set.Iic (((i : ℕ) - 1) + 2)) := by
    intro x hx y hy hxy
    rw [Set.mem_Iic] at hx hy
    rw [hws x (by omega) (by omega), hws y (by omega) (by omega)] at hxy
    have := congrArg Fin.val (cd.vtx_inj hxy); omega
  -- `shiftBodyFrameworkAsc (i'−1) = Fva` (the normals `shiftSeedAdv q (i−1)`, the graph
  -- `G − v_{(i−1)+1} = G − vᵢ`).
  have hidx : (⟨((i' : ℕ) - 1) + 1, by have := i'.2; omega⟩ : Fin (cd.d + 1))
      = ⟨(i : ℕ), by omega⟩ := Fin.ext (by simp only [hi'v]; omega)
  have hFvaEq : cd.shiftBodyFrameworkAsc (s := (i' : ℕ) - 1) (by have := i'.2; omega) ends hG q
      = Fva := by
    rw [Graph.ChainData.shiftBodyFrameworkAsc, hFva]
    congr 2
    rw [Graph.ChainData.shiftBodyGraph]
    exact congrArg (fun x => G.removeVertex (cd.vtx x)) hidx
  -- fold start framework `shiftBodyFrameworkAsc 0 = ofNormals (G − v₁) ends (shiftSeedAdv q 0)`.
  have hFvaStart : cd.shiftBodyFrameworkAsc (s := 0) (by have := i'.2; omega) ends hG q
      = (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩)) ends
          (cd.shiftSeedAdv q 0)).toBodyHinge := by
    rfl
  -- The moves take `hingeRow (vtx 0) (vtx 2) ρ₀` into the row space of
  -- `shiftBodyFrameworkAsc (i−1) = Fva`.
  have hfold := cd.shiftBodyListAsc_foldl_mem_span_rigidityRows i' ends q hrec
    (φ := BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ₀)
    (hFvaStart ▸ hφ)
  rw [hFvaEq] at hfold
  -- The body list `shiftBodyListAsc i'` is the telescope's `List.ofFn (· ↦ (w (s+1), w (s+2),
  -- w (s+3)))` shape (`w s = vtx s` on the touched range `s ≤ i+1 ≤ d`); and `vtx 0/2 = w 0/2`.
  have hbodies : cd.shiftBodyListAsc i'
      = List.ofFn fun s : Fin ((i' : ℕ) - 1) =>
          (w ((s : ℕ) + 1), w ((s : ℕ) + 2), w ((s : ℕ) + 3)) := by
    rw [Graph.ChainData.shiftBodyListAsc]
    congr 1
    funext s
    rw [hws ((s : ℕ) + 1) (by omega) (by omega), hws ((s : ℕ) + 2) (by omega) (by omega),
      hws ((s : ℕ) + 3) (by omega) (by omega)]
  have hw02 : BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ₀
      = BodyHingeFramework.hingeRow (w 0) (w 2) ρ₀ := by
    rw [hws 0 (by omega) (by omega), hws 2 (by omega) (by omega)]
  rw [hbodies, hw02] at hfold
  -- `hsurv`: each form `hingeRow (w s) (w (s+1)) ρ₀` at an edge of `G − vᵢ` is a row
  -- (`freshEdge_surviving_row_mem`, from `hperp s`).
  have hsurv : ∀ s ∈ Finset.range ((i' : ℕ) - 1),
      BodyHingeFramework.hingeRow (w s) (w (s + 1)) ρ₀ ∈ Submodule.span K Fva.rigidityRows := by
    intro s hs
    rw [Finset.mem_range] at hs
    rw [hws s (by omega) (by omega), hws (s + 1) (by omega) (by omega)]
    -- `freshEdge_surviving_row_mem`'s framework `ofNormals (G − vᵢ) ends (shiftSeedAdv q (i−1))`
    -- is exactly `Fva` (up to the `set` abbreviation).
    exact cd.freshEdge_surviving_row_mem i s (by omega) ρ₀ (hperp s (by omega))
  -- `wstep_foldl_freshEdge_slot_mem` with `m = i' − 1 = i − 1`: the form
  -- `hingeRow (w m) (w (m+2)) ρ₀` is the moved form minus the `m` rows.
  have hslot := BodyHingeFramework.wstep_foldl_freshEdge_slot_mem w ((i' : ℕ) - 1) hinj ρ₀ hfold
    hsurv
  -- the form is the conclusion, as `w m = vtx (i−1)` and `w (m+2) = vtx (i+1)`.
  rw [hws ((i' : ℕ) - 1) (by omega) (by omega),
    hws (((i' : ℕ) - 1) + 2) (by omega) (by omega)] at hslot
  convert hslot using 4
  omega

/-- **`ρ₀` vanishes on the hinge of `v_s v_{s+1}`** (a step of `lem:case-III-chain-eq666`; KT
eq. (6.66), p. 698): for `d ≥ 3` and `2 ≤ s ≤ d − 1`, let `∑ c_j hingeRow (uv j) (vv j) (rv j)` be
`hingeRow v₀ v₂ ρ₀` (`hcomb`), where each `ev j` joins `uv j` and `vv j` in `G` (`hlink`), each
`rv j` lies in the block of rows of `F = ofNormals (G − v_i) ends qρ` at `ev j` (`hrv`), and every
term at `v₂` is at `v₂v₃` (`hdeg1`). Then `ρ₀` vanishes on the hinge of `F` at `v_s v_{s+1}`: the
terms at `v_s v_{s+1}`, restricted to `v_s`, sum to `−ρ₀`
(`interior_group_acolumn_eq_neg_baseRedundancy`), a form in the block of rows at `v_s v_{s+1}`
(`edgeGroup_acolumn_mem_block`). `chainData_freshEdge_slot_perp_ends₀` applies it with `i = 1`, at
the edge `v_{s+1} v_{s+2}`. -/
theorem _root_.Graph.ChainData.chainData_freshEdge_perp_of_baseRedundancy
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (h3 : 3 ≤ cd.d)
    (i : Fin (cd.d + 1)) (s : ℕ) (h2s : 2 ≤ s) (hsd : s < cd.d)
    {ends : β → α × α} {qρ : α × Fin (k + 2) → K}
    {m : ℕ} (c : Fin m → K) (ev : Fin m → β) (uv vv : Fin m → α)
    (rv : Fin m → Module.Dual K (ScrewSpace K k))
    {ρ₀ : Module.Dual K (ScrewSpace K k)}
    -- `hingeRow v₀ v₂ ρ₀` as a combination of forms in the blocks of rows of
    -- `ofNormals (G − vᵢ) ends qρ`:
    (hlink : ∀ j, G.IsLink (ev j) (uv j) (vv j))
    {hlinks : PanelHingeFramework.RecordsLinks (G.removeVertex (cd.vtx i)) ends}
    (hrv : ∀ j, rv j ∈ (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i)) ends
      qρ).toBodyHinge.hingeRowBlock (ev j))
    (hcomb : (∑ j, c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j))
      = BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ₀)
    -- every term at `vtx 2` is at `edge 2`:
    (hdeg1 : ∀ j, (cd.vtx ⟨2, by omega⟩ = uv j ∨ cd.vtx ⟨2, by omega⟩ = vv j) →
      ev j = cd.edge ⟨2, by omega⟩) :
    ρ₀ ((PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i)) ends
      qρ).toBodyHinge.supportExtensor (cd.edge ⟨s, by omega⟩)) = 0 := by
  classical
  set Fva := (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i)) ends qρ).toBodyHinge
    with hFva
  -- The terms at `edge s`, restricted to `vtx s`, sum to `−ρ₀`, which so lies in
  -- `Fva.hingeRowBlock (edge s)` (`edgeGroup_acolumn_mem_block`).
  have hcolval := cd.interior_group_acolumn_eq_neg_baseRedundancy h3 c ev uv vv rv hlink hcomb
    hdeg1 s h2s hsd
  have hmem := Fva.edgeGroup_acolumn_mem_block (e := cd.edge ⟨s, by omega⟩)
    (p := cd.vtx ⟨s, by omega⟩) c ev uv vv rv hrv
  rw [hcolval] at hmem
  -- `−ρ₀ ∈ block (edge s) ⟹ ρ₀ ∈ block ⟹ ρ₀ ⊥ supportExtensor (edge s)`.
  have hρ₀mem : ρ₀ ∈ Fva.hingeRowBlock (cd.edge ⟨s, by omega⟩) := by
    have := (Fva.hingeRowBlock (cd.edge ⟨s, by omega⟩)).neg_mem hmem
    rwa [neg_neg] at this
  exact (Fva.mem_hingeRowBlock_iff (cd.edge ⟨s, by omega⟩) ρ₀).1 hρ₀mem

/-! ## The form at the new edge of `G_i` in the row space of `R(G − v_i, q_i)`

The second claim of `lem:case-III-chain-eq666`. With the selector `ends₀`, the hinge of `G − v_i` at
`v_s v_{s+1}`, at the normals `q_i`, is up to sign that of `G − v₁` at `v_{s+1} v_{s+2}` when
`s ≥ 1`, and at `v₀v₂` when `s = 0` (KT eq. (6.59), p. 694), so `ρ₀` vanishes on it
(`chainData_freshEdge_slot_perp_ends₀`), and the moves along the chain put the form at the new edge
of `G_i` in the row space (`chainData_relabel_arm_hρGv`). -/

/-- **`ρ₀` vanishes on the hinges of the edges of the chain in `G − v_i`** (a step of
`lem:case-III-chain-eq666`; KT eq. (6.59), p. 694): for `d ≥ 3` and `s + 1 < i ≤ d − 1`, let `ends₀`
give each link of `G` its ends in some order (`hrec`) and `e₀` the ends `v₀` and `v₂` in some order
(`hrece₀`), let `hingeRow v₀ v₂ ρ₀` be a combination at `ofNormals (G − v₁) ends₀ q` as in
`chainData_freshEdge_perp_of_baseRedundancy` (`hlink`, `hrv`, `hcomb`, `hdeg1`), and let `ρ₀` vanish
on its hinge at `e₀` (`hρe₀`). Then `ρ₀` vanishes on the hinge of
`ofNormals (G − v_i) ends₀ (q ∘ σ_i)` at `v_s v_{s+1}`, for `σ_i = shiftPerm i.castSucc`.

That hinge is `±C(q_i(v_s), q_i(v_{s+1}))`, by `hrec`. For `s ≥ 1`, `σ_i` maps `v_s` and `v_{s+1}`
to `v_{s+1}` and `v_{s+2}` (`shiftPerm_apply_interior`), so it is `±` the hinge of `G − v₁` at
`v_{s+1} v_{s+2}`, on which `ρ₀` vanishes (`chainData_freshEdge_perp_of_baseRedundancy`). For
`s = 0`, `σ_i` fixes `v₀` and maps `v₁` to `v₂`, so it is `±` the hinge at `e₀` (`hrece₀`), on which
`ρ₀` vanishes (`hρe₀`). -/
theorem _root_.Graph.ChainData.chainData_freshEdge_slot_perp_ends₀
    [DecidableEq α]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (h3 : 3 ≤ cd.d)
    (i : Fin cd.d) (s : ℕ) (hs1i : s + 1 < (i : ℕ))
    {ends₀ : β → α × α} {q : α × Fin (k + 2) → K}
    {m : ℕ} (c : Fin m → K) (ev : Fin m → β) (uv vv : Fin m → α)
    (rv : Fin m → Module.Dual K (ScrewSpace K k))
    {ρ₀ : Module.Dual K (ScrewSpace K k)}
    -- `ends₀` gives each link of `G` its ends, and `e₀` the ends `v₀` and `v₂`:
    (hrec : ∀ f x y, G.IsLink f x y → ends₀ f = (x, y) ∨ ends₀ f = (y, x))
    (hrece₀ : ends₀ cd.e₀ = (cd.vtx ⟨0, by omega⟩, cd.vtx ⟨2, by omega⟩) ∨
      ends₀ cd.e₀ = (cd.vtx ⟨2, by omega⟩, cd.vtx ⟨0, by omega⟩))
    -- `hingeRow v₀ v₂ ρ₀` as a combination at `ofNormals (G − v₁) ends₀ q`:
    (hlink : ∀ j, G.IsLink (ev j) (uv j) (vv j))
    (hrv : ∀ j, rv j ∈ (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩))
      ends₀ q).toBodyHinge.hingeRowBlock (ev j))
    (hcomb : (∑ j, c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j))
      = BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ₀)
    (hdeg1 : ∀ j, (cd.vtx ⟨2, by omega⟩ = uv j ∨ cd.vtx ⟨2, by omega⟩ = vv j) →
      ev j = cd.edge ⟨2, by omega⟩)
    -- `ρ₀` vanishes on the hinge of `e₀` there:
    (hρe₀ : ρ₀ ((PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩))
      ends₀ q).toBodyHinge.supportExtensor cd.e₀) = 0) :
    ρ₀ ((PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i.castSucc)) ends₀
        (fun p => q (cd.shiftPerm i.castSucc p.1, p.2))).toBodyHinge.supportExtensor
          (cd.edge ⟨s, by have := i.isLt; omega⟩)) = 0 := by
  classical
  have hid : (i : ℕ) < cd.d := i.isLt
  set qρ : α × Fin (k + 2) → K := fun p => q (cd.shiftPerm i.castSucc p.1, p.2) with hqρ
  -- The `ends₀`-form support extensor at `edge s` reads the panel of `qρ` at `ends₀ (edge s)`.
  rw [PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_ends,
    PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal]
  -- `ends₀ (edge s)` records the chain link `(vtx s, vtx (s+1))` (up to orientation).
  have hrecS := hrec (cd.edge ⟨s, by omega⟩) (cd.vtx ⟨s, by omega⟩) (cd.vtx ⟨s + 1, by omega⟩)
    (by have h := cd.link ⟨s, by omega⟩
        simpa only [Fin.castSucc_mk, Fin.succ_mk] using h)
  -- `qρ (vtx (s+1), ·) = q (vtx (s+2), ·)` (`shiftPerm_apply_interior`, `1 ≤ s+1 < i`).
  have hqsp1 : (fun j => qρ (cd.vtx ⟨s + 1, by omega⟩, j))
      = (fun j => q (cd.vtx ⟨s + 2, by omega⟩, j)) := by
    funext j; rw [hqρ]; dsimp only
    rw [cd.shiftPerm_apply_interior i.castSucc (by omega)
      (by simp only [Fin.val_castSucc]; omega)]
  rcases Nat.eq_zero_or_pos s with hs0 | hs0
  · -- HEAD `s = 0`: `qρ (vtx 0, ·) = q (vtx 0, ·)` (off-cycle fix); the panel is the `e₀` panel.
    subst hs0
    have hq0 : (fun j => qρ (cd.vtx ⟨0, by omega⟩, j))
        = (fun j => q (cd.vtx ⟨0, by omega⟩, j)) := by
      funext j; rw [hqρ]; dsimp only
      rw [cd.shiftPerm_apply_vtx_off i.castSucc (by omega) (Or.inl rfl)]
    -- `hρe₀` at the `ends₀`-form, via `hrece₀`: `base.supportExtensor e₀ = ± panel (q v₀) (q v₂)`.
    have hρe₀' : ρ₀ (panelSupportExtensor (fun j => q (cd.vtx ⟨0, by omega⟩, j))
        (fun j => q (cd.vtx ⟨2, by omega⟩, j))) = 0 := by
      rw [PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_ends,
        PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal] at hρe₀
      rcases hrece₀ with he | he
      · rw [he] at hρe₀; exact hρe₀
      · rwa [he, panelSupportExtensor_swap, map_neg, neg_eq_zero] at hρe₀
    rcases hrecS with he | he
    · rw [he]; dsimp only; rw [hq0, hqsp1]; exact hρe₀'
    · rw [he]; dsimp only; rw [hq0, hqsp1, panelSupportExtensor_swap, map_neg, hρe₀', neg_zero]
  · -- INTERIOR `s ≥ 1`: `qρ (vtx s, ·) = q (vtx (s+1), ·)` (`shiftPerm_apply_interior`, `1 ≤ s`).
    have hqs : (fun j => qρ (cd.vtx ⟨s, by omega⟩, j))
        = (fun j => q (cd.vtx ⟨s + 1, by omega⟩, j)) := by
      funext j; rw [hqρ]; dsimp only
      rw [cd.shiftPerm_apply_interior i.castSucc (by omega)
        (by simp only [Fin.val_castSucc]; omega)]
    -- `ρ₀` vanishes on the hinge of `G − v₁` at `edge (s+1)`
    -- (`chainData_freshEdge_perp_of_baseRedundancy` at `i = 1`), which is `± panel`.
    have hbase := cd.chainData_freshEdge_perp_of_baseRedundancy h3 ⟨1, by omega⟩ (s + 1) (by omega)
      (by omega) c ev uv vv rv hlink hrv hcomb hdeg1 (ρ₀ := ρ₀)
    rw [PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_ends,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal] at hbase
    -- `ends₀ (edge (s+1))` records `(vtx (s+1), vtx (s+2))` (up to orientation).
    have hrecS1 := hrec (cd.edge ⟨s + 1, by omega⟩) (cd.vtx ⟨s + 1, by omega⟩)
      (cd.vtx ⟨s + 2, by omega⟩)
      (by have h := cd.link ⟨s + 1, by omega⟩
          simpa only [Fin.castSucc_mk, Fin.succ_mk] using h)
    have hbase' : ρ₀ (panelSupportExtensor (fun j => q (cd.vtx ⟨s + 1, by omega⟩, j))
        (fun j => q (cd.vtx ⟨s + 2, by omega⟩, j))) = 0 := by
      rcases hrecS1 with he | he
      · rw [he] at hbase; exact hbase
      · rwa [he, panelSupportExtensor_swap, map_neg, neg_eq_zero] at hbase
    rcases hrecS with he | he
    · rw [he]; dsimp only; rw [hqs, hqsp1]; exact hbase'
    · rw [he]; dsimp only; rw [hqs, hqsp1, panelSupportExtensor_swap, map_neg, hbase', neg_zero]

/-- **The form at the new edge of `G_i` lies in the row space of `R(G − v_i, q_i)`**
(`lem:case-III-chain-eq666`, the second claim; KT eq. (6.66), p. 698): for `d ≥ 3`, `2 ≤ i ≤ d − 1`,
`σ_i = shiftPerm i.castSucc` and `q_i = q ∘ σ_i`, let `ends₀` give each link of `G` its ends in some
order (`hrec`) and `e₀` the ends `v₀` and `v₂` in some order (`hrece₀`), let `hingeRow v₀ v₂ ρ₀` lie
in the span of the rows of `ofNormals (G − v₁) ends₀ q` (`hφ`) and be a combination at it as in
`chainData_freshEdge_perp_of_baseRedundancy` (`hlink`, `hrv`, `hcomb`, `hdeg1`), and let `ρ₀` vanish
on its hinge at `e₀` (`hρe₀`). Then `hingeRow v_{i+1} v_{i−1} (−ρ₀)` lies in the span of the rows of
`ofNormals (G − v_i) ends₀ q_i`.

The form is `hingeRow v_{i−1} v_{i+1} ρ₀` (`hingeRow_swap`), which `chainData_freshEdge_slot_mem`
puts in the row space at the normals `shiftSeedAdv q (i − 1) = q_i`
(`shiftSeedAdv_eq_funLeft_shiftPerm`), with the vanishing on the hinges of the edges of the chain
from `chainData_freshEdge_slot_perp_ends₀`. `chainData_dispatch_interior`
(`CaseIII/Realization.lean`) applies it. -/
theorem _root_.Graph.ChainData.chainData_relabel_arm_hρGv
    [DecidableEq α]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (h3 : 3 ≤ cd.d)
    (i : Fin cd.d) (h2i : 2 ≤ (i : ℕ))
    {ends₀ : β → α × α} {q : α × Fin (k + 2) → K}
    {m : ℕ} (c : Fin m → K) (ev : Fin m → β) (uv vv : Fin m → α)
    (rv : Fin m → Module.Dual K (ScrewSpace K k))
    {ρ₀ : Module.Dual K (ScrewSpace K k)}
    -- `ends₀` gives each link of `G` its ends, and `e₀` the ends `v₀` and `v₂`:
    (hrec : ∀ f x y, G.IsLink f x y → ends₀ f = (x, y) ∨ ends₀ f = (y, x))
    (hrece₀ : ends₀ cd.e₀ = (cd.vtx ⟨0, by omega⟩, cd.vtx ⟨2, by omega⟩) ∨
      ends₀ cd.e₀ = (cd.vtx ⟨2, by omega⟩, cd.vtx ⟨0, by omega⟩))
    -- `hingeRow v₀ v₂ ρ₀` as a combination at `ofNormals (G − v₁) ends₀ q`:
    (hlink : ∀ j, G.IsLink (ev j) (uv j) (vv j))
    (hrv : ∀ j, rv j ∈ (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩))
      ends₀ q).toBodyHinge.hingeRowBlock (ev j))
    (hcomb : (∑ j, c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j))
      = BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ₀)
    (hdeg1 : ∀ j, (cd.vtx ⟨2, by omega⟩ = uv j ∨ cd.vtx ⟨2, by omega⟩ = vv j) →
      ev j = cd.edge ⟨2, by omega⟩)
    -- and in the row space of `ofNormals (G − v₁) ends₀ q`:
    (hφ : BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ₀ ∈
      Submodule.span K (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩))
        ends₀ q).toBodyHinge.rigidityRows)
    -- `ρ₀` vanishes on the hinge of `e₀` there:
    (hρe₀ : ρ₀ ((PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩))
      ends₀ q).toBodyHinge.supportExtensor cd.e₀) = 0) :
    BodyHingeFramework.hingeRow (cd.vtx i.succ)
        (cd.vtx (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc) (-ρ₀)
      ∈ Submodule.span K (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i.castSucc))
        ends₀ (fun p => q (cd.shiftPerm i.castSucc p.1, p.2))).toBodyHinge.rigidityRows := by
  classical
  -- The normals `qρ = q ∘ σ_i`.
  set qρ : α × Fin (k + 2) → K := fun p => q (cd.shiftPerm i.castSucc p.1, p.2) with hqρ
  -- The bound `i < d`.
  have hid : (i : ℕ) < cd.d := i.isLt
  -- `hingeRow_swap`: the form is `hingeRow vᵢ₋₁ vᵢ₊₁ ρ₀`.
  rw [BodyHingeFramework.hingeRow_swap (cd.vtx i.succ)
    (cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc) (-ρ₀), neg_neg]
  -- The normals `qρ` are `shiftSeedAdv q (i−1)` (`shiftSeedAdv_eq_funLeft_shiftPerm`).
  have hP3 : cd.shiftSeedAdv q ((i : ℕ) - 1) = qρ := by
    rw [hqρ]; exact cd.shiftSeedAdv_eq_funLeft_shiftPerm q i (by omega)
  -- The vertices `vtx (i−1).castSucc` and `vtx i.succ` of the conclusion are the `vtx ⟨(i:ℕ)−1, _⟩`
  -- and `vtx ⟨(i:ℕ)+1, _⟩` of `chainData_freshEdge_slot_mem`.
  have hidx1 : cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc
      = cd.vtx ⟨(i : ℕ) - 1, by omega⟩ :=
    congrArg cd.vtx (Fin.ext (by simp only [Fin.val_castSucc]))
  have hidx2 : cd.vtx i.succ = cd.vtx ⟨(i : ℕ) + 1, by omega⟩ :=
    congrArg cd.vtx (Fin.ext (by simp only [Fin.val_succ]))
  rw [hidx1, hidx2, ← hP3]
  -- `chainData_freshEdge_slot_mem` at the selector `ends₀`, from `hφ` and the hinges of the edges
  -- of the chain.
  refine cd.chainData_freshEdge_slot_mem ⟨(i : ℕ), by omega⟩
    (show 1 ≤ (i : ℕ) by omega) (show (i : ℕ) < cd.d from hid) ends₀ q ?hrec ?hφ ?hperp
  case hrec => exact hrec
  case hφ =>
    -- `hφ`, as `shiftSeedAdv q 0 = q`.
    rw [cd.shiftSeedAdv_zero]; exact hφ
  case hperp =>
    -- the hinge of each edge `v_s v_{s+1}`, `s + 1 < i` (`chainData_freshEdge_slot_perp_ends₀`).
    intro s hs
    rw [hP3]
    exact cd.chainData_freshEdge_slot_perp_ends₀ h3 i s hs c ev uv vv rv hrec hrece₀
      hlink hrv hcomb hdeg1 hρe₀


end CombinatorialRigidity.Molecular
