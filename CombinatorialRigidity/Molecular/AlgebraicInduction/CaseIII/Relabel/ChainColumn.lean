/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.AlgebraicInduction.CaseIII.Relabel.Arm

/-!
# The algebraic induction — Case III relabel: the eq.~(6.44) chain-induction column machinery

Phase 22 (molecular-conjecture program). Fourth file of the `CaseIII/Relabel/` subdirectory (the
Phase-23c split of `CaseIII/Relabel.lean`, `notes/Phase23c.md`). The base regroup-at-interior
degree-2
column foundation, the eq.~(6.44) chain-induction (step kernel / anchor / endpoint-flip + the
induction), the interior edge-group `−ρ₀` tail-column reading
(`funLeft_dualMap_interior_group_acolumn_eq_neg_baseRedundancy`), the seed-bridge identities, the
general-`i` fresh-edge slot membership + perp transports, and the carried-hypothesis chain arm
`chainData_relabel_arm_hρGv`. Built on `Relabel/Arm`; consumed by the forked arm in
`Relabel/ForkedArm`.

See `ROADMAP.md` §22 and the `sec:molecular-algebraic-induction-caseIII` dep-graph in
`blueprint/src/chapter/algebraic-induction/case-iii.tex`.
-/

namespace CombinatorialRigidity.Molecular

variable {k : ℕ}

open scoped Graph

variable {α β : Type*}

/-! ### The base regroup-at-interior-degree-2-vertex column foundation (CHAIN-2c-ii-arm, A-3)

The mechanical column-restriction core the (a′-i) base regroup-at-interior-degree-2-vertex producer
threads through (`notes/Phase23-design.md` §(o‴)(I.8.9); Phase 23b). The A-1 producer
`exists_candidateRow_bottomRows_of_rigidOn` now exposes the candidate row `hρGv` in the
**edge-grouped** form `hingeRow (ab) ρ = ∑ⱼ cGv j • hingeRow (uvGv j)(vvGv j)(rvGv j)` (via
`exists_edgeIndexed_combination_of_mem_span_rigidityRows`); the regroup at a degree-2 interior chain
vertex `a` collects the summands incident to `a` into its two incident-edge groups and discards the
rest. The genuinely-mechanical heart of that regrouping is this lemma: the `a`-column of the sum
over the *non-incident* summands (both endpoints `≠ a`) vanishes — KT eq.~(6.43)/(6.66)'s "every
edge off `a` contributes `0` to the `a`-column", the `grest` half of the eq.~(6.43) witness
`candidate_perp_two_incident_supportExtensors` (A-2) consumes. Framework-free (`hingeRow` reads only
endpoints + screw functional, not the graph), zero blast radius. -/

/-- **The `a`-column of an edge-indexed `hingeRow` combination over summands off `a` vanishes**
(CHAIN-2c-ii-arm, the base regroup column foundation; KT 2011 §6.4.1 eq.~(6.43)/(6.66), Phase 23b).
For a finite ℝ-combination `∑ⱼ cⱼ • hingeRow (uv j)(vv j)(rv j)` in which **every** summand's two
endpoints avoid body `a` (`a ≠ uv j` and `a ≠ vv j`), precomposing with `a`'s screw-column injection
`single a` is `0`: each summand vanishes on the `a`-column by `hingeRow_comp_single_off`, and the
column restriction is additive. This is the `grest`-half (the off-`a` rest vanishes on `a`'s column)
of the eq.~(6.43) regrouping of an edge-grouped redundancy `hρGv` at a degree-2 interior chain
vertex — the `hrest` obligation `candidate_perp_two_incident_supportExtensors` (A-2) /
`freshEdge_surviving_row_mem_of_witness` (A-3) consume. -/
theorem BodyHingeFramework.edgeIndexedCombination_comp_single_off [DecidableEq α]
    (a : α) {n : ℕ} (c : Fin n → ℝ) (uv vv : Fin n → α)
    (rv : Fin n → Module.Dual ℝ (ScrewSpace k))
    (hoff : ∀ j, a ≠ uv j ∧ a ≠ vv j) :
    (∑ j, c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
      (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a) = 0 := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, LinearMap.coe_sum, Finset.sum_apply, LinearMap.zero_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [LinearMap.smul_apply, ← LinearMap.comp_apply,
    BodyHingeFramework.hingeRow_comp_single_off (hoff j).1 (hoff j).2, LinearMap.zero_apply,
    smul_zero]

/-- **The `a`-column of an edge-indexed `hingeRow` combination is its `a`-incident sub-combination's
column** (CHAIN-2c-ii-arm, the base regroup column-isolation core; KT 2011 §6.4.1 eq.~(6.43)/(6.66),
Phase 23b). For a finite ℝ-combination `∑ⱼ cⱼ • hingeRow (uv j)(vv j)(rv j)`, precomposing with body
`a`'s screw-column injection `single a` equals doing so for the restriction to the summands
**incident** to `a` (those with `a = uv j ∨ a = vv j`): split the index set by incidence at `a`, and
the off-`a` part's `a`-column vanishes by `edgeIndexedCombination_comp_single_off`
(`hingeRow_comp_single_off` per summand). This is the column-algebra core of the eq.~(6.43)
regrouping of an edge-grouped redundancy `hρGv` at a degree-2 interior chain vertex `a`: the regroup
proper then uses the degree-2 graph fact (only the two incident chain edges meet `a`) to partition
the incident summands into the `(ab)`/`(ac)` groups `candidate_perp_two_incident_supportExtensors`
(A-2) / `freshEdge_surviving_row_mem_of_witness` (A-3) consume. Framework-free, zero blast
radius. -/
theorem BodyHingeFramework.edgeIndexedCombination_comp_single_eq_incident [DecidableEq α]
    (a : α) {n : ℕ} (c : Fin n → ℝ) (uv vv : Fin n → α)
    (rv : Fin n → Module.Dual ℝ (ScrewSpace k)) :
    (∑ j, c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a)
      = (∑ j ∈ Finset.univ.filter (fun j => a = uv j ∨ a = vv j),
          c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a) := by
  -- Split the full sum into the `a`-incident part and the off-`a` part.
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => a = uv j ∨ a = vv j),
    LinearMap.add_comp]
  -- The off-`a` part's `a`-column vanishes: each summand has `a ≠ uv j` and `a ≠ vv j`.
  have hoff : (∑ j ∈ Finset.univ.filter (fun j => ¬ (a = uv j ∨ a = vv j)),
        c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
      (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a) = 0 := by
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, LinearMap.coe_sum, Finset.sum_apply, LinearMap.zero_apply]
    refine Finset.sum_eq_zero fun j hj => ?_
    obtain ⟨hau, hav⟩ := not_or.mp (Finset.mem_filter.mp hj).2
    rw [LinearMap.smul_apply, ← LinearMap.comp_apply,
      BodyHingeFramework.hingeRow_comp_single_off hau hav, LinearMap.zero_apply, smul_zero]
  rw [hoff, add_zero]

/-- **A single chain-edge group's screw column lands in that edge's hinge-row block**
(CHAIN-2c-ii-arm, the base regroup block-membership core; KT 2011 §6.4.1 eq.~(6.43)/(6.66),
Phase 23b). For an edge-indexed `hingeRow` combination whose every summand `j` carries a
hinge-row-block row `rvⱼ ∈ Fva.hingeRowBlock (evⱼ)`, the screw column at a body `p`
of the **`e`-group** sub-combination (the summands with `evⱼ = e`)
lies in `Fva.hingeRowBlock e`:

`(∑_{evⱼ = e} cⱼ • hingeRow (uvⱼ)(vvⱼ)(rvⱼ)).comp (single p) ∈ Fva.hingeRowBlock e`.

Each summand `j` carried by `e` links `{u, v}` (the link uniqueness pins its endpoints to `e`'s),
so its column at `p` is `±rvⱼ` (`hingeRow_comp_single_tail`/`_swap` at the matching endpoint, or `0`
off both endpoints by `hingeRow_comp_single_off`) — in every case a `block`-member (`rvⱼ ∈ block e`,
closed under scaling and negation). Summing over the group keeps the membership (the block is a
submodule). This is the block-membership half of the eq.~(6.43)/(6.66) regrouping: the `e`-group's
column, read at any body `p`, is `⊥ C(p(e))` — exactly the per-edge perp
`chainData_freshEdge_slot_mem` consumes once the chain induction (LEAF 4) identifies the column with
`−ρ₀`. Framework-bound (the block depends on `Fva`), zero blast radius. -/
theorem BodyHingeFramework.edgeGroup_acolumn_mem_block [DecidableEq α] [DecidableEq β]
    {Fva : BodyHingeFramework k α β} {e : β} {p : α}
    {m : ℕ} (c : Fin m → ℝ) (ev : Fin m → β) (uv vv : Fin m → α)
    (rv : Fin m → Module.Dual ℝ (ScrewSpace k))
    (hrv : ∀ j, rv j ∈ Fva.hingeRowBlock (ev j)) :
    (∑ j ∈ Finset.univ.filter (fun j => ev j = e),
        c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
      (LinearMap.single ℝ (fun _ : α => ScrewSpace k) p) ∈ Fva.hingeRowBlock e := by
  classical
  -- Distribute the column restriction over the filtered sum, then close by the block's submodule
  -- closure (`sum_mem`/`smul_mem`).
  rw [show (∑ j ∈ Finset.univ.filter (fun j => ev j = e),
        c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) p)
      = ∑ j ∈ Finset.univ.filter (fun j => ev j = e),
          (c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
          (LinearMap.single ℝ (fun _ : α => ScrewSpace k) p)
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
          = (0 : Module.Dual ℝ (α → ScrewSpace k)) := by
        rw [← hpu, ← hpv]
        exact LinearMap.ext fun x => by rw [BodyHingeFramework.hingeRow_apply, sub_self, map_zero,
          LinearMap.zero_apply]
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

/-! ### The eq.~(6.44) chain-induction step kernel (CHAIN-2c-ii-arm, LEAF 1)

The step kernel of the KT eq.~(6.66) `±r` chain induction
(`notes/Phase23-design.md` §(o‴)(I.8.9-SETTLE), LEAF 1; Phase 23b). At a **deeper** interior
degree-2 chain vertex `a = vtx i.castSucc`
(`2 ≤ i ≤ d−1`) the global base redundancy `g`, exposed edge-grouped as
`∑ⱼ cⱼ • hingeRow (uvⱼ)(vvⱼ)(rvⱼ)` (each summand a `G`-link `evⱼ = uvⱼvvⱼ`), has its `a`-column
governed entirely by the two incident chain edges `edge i` and `edge (i−1)` (the interior degree-2
closure `deg_two_split`: no other `G`-edge meets `a`). Reading the global column-vanishing
`g.comp (single a) = 0` (KT eq.~(6.43)) through the column-isolation core
`edgeIndexedCombination_comp_single_eq_incident` (only `a`-incident summands contribute to the
`a`-column) and partitioning the incident summands by which of the two chain edges carries them
gives KT's eq.~(6.44) at `a`: the successor-edge group's `a`-column is *minus* the predecessor-edge
group's. The two "groups" are the `a`-column restrictions of the per-edge sub-combinations — screw
functionals (`Module.Dual ℝ (ScrewSpace k)`) the chain induction propagates as `±ρ₀`. -/

/-- **The eq.~(6.44) chain-induction step kernel: the two incident chain-edge groups' `a`-columns
cancel** (CHAIN-2c-ii-arm, the `hρGv` regroup chain induction LEAF 1; Katoh–Tanigawa 2011 §6.4.1
eq.~(6.44)/§6.4.2 eq.~(6.66), `notes/Phase23-design.md` §(o‴)(I.8.9-SETTLE); Phase 23b). Let
`g = ∑ⱼ cⱼ • hingeRow (uvⱼ)(vvⱼ)(rvⱼ)` be an edge-indexed `hingeRow` combination in which each
summand `j` is a genuine `G`-link `evⱼ` from `uvⱼ` to `vvⱼ`. At an **interior** chain vertex
`a = cd.vtx i.castSucc` (`0 < i`, so `1 ≤ i ≤ d−1`) — degree-2 in `G` by `cd.deg_two`, its only
incident edges the successor `edge i` and predecessor `edge (i−1)` — the global `a`-column vanishing
`g.comp (single a) = 0` forces the `a`-columns of the two incident-edge sub-combinations to cancel:

`(∑_{evⱼ = edge i} cⱼ • hingeRow (uvⱼ)(vvⱼ)(rvⱼ)).comp (single a)
  = −(∑_{evⱼ = edge (i−1)} cⱼ • hingeRow (uvⱼ)(vvⱼ)(rvⱼ)).comp (single a)`.

The `a`-column restriction `(·).comp (single a)` is orientation-agnostic (it reads `±rvⱼ` per
summand by `hingeRow_comp_single_tail`/`_off`), so the conclusion is exactly the adjacency relation
`group(edge i) = −group(edge (i−1))` the chain induction's step uses, no re-orientation needed.
The proof: the column-isolation core `edgeIndexedCombination_comp_single_eq_incident` reduces the
`a`-column to the `a`-incident summands; the interior degree-2 closure `cd.deg_two_split` partitions
those (disjointly, `edge_inj`) into the `edge i`- and `edge (i−1)`-groups (each chain edge meets `a`
by `cd.isLink_succ_edge`/`cd.isLink_pred_edge`, and every incident summand is one of the two by
`deg_two_split`). Framework-free, zero blast radius. -/
theorem _root_.Graph.ChainData.interiorGroup_acolumn_adjacency [DecidableEq α] [DecidableEq β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) {i : Fin cd.d} (hi : 0 < (i : ℕ))
    {m : ℕ} (c : Fin m → ℝ) (ev : Fin m → β) (uv vv : Fin m → α)
    (rv : Fin m → Module.Dual ℝ (ScrewSpace k))
    (hlink : ∀ j, G.IsLink (ev j) (uv j) (vv j))
    (hcol : (∑ j, c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) (cd.vtx i.castSucc)) = 0) :
    (∑ j ∈ Finset.univ.filter (fun j => ev j = cd.edge i),
        c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
      (LinearMap.single ℝ (fun _ : α => ScrewSpace k) (cd.vtx i.castSucc))
    = -(∑ j ∈ Finset.univ.filter (fun j => ev j = cd.edge ⟨(i : ℕ) - 1, by omega⟩),
        c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
      (LinearMap.single ℝ (fun _ : α => ScrewSpace k) (cd.vtx i.castSucc)) := by
  classical
  set a := cd.vtx i.castSucc with ha
  set ei := cd.edge i with hei
  set ep := cd.edge ⟨(i : ℕ) - 1, by omega⟩ with hep
  -- The two chain edges are distinct (`edge_inj`); each is a `G`-link incident to `a`.
  have hep_ne_ei : ep ≠ ei := (cd.pred_edge_ne hi)
  have hlink_ei : G.IsLink ei a (cd.vtx i.succ) := cd.isLink_succ_edge i
  have hlink_ep : G.IsLink ep a (cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc) :=
    cd.isLink_pred_edge hi
  -- A summand carried by `edge i` (resp. `edge (i−1)`) is incident to `a` (same-edge endpoints).
  have hinc_ei : ∀ j, ev j = ei → a = uv j ∨ a = vv j := fun j hj =>
    (((hlink j).symm.eq_and_eq_or_eq_and_eq (hj ▸ hlink_ei)).imp (·.1.symm) (·.2.symm)).symm
  have hinc_ep : ∀ j, ev j = ep → a = uv j ∨ a = vv j := fun j hj =>
    (((hlink j).symm.eq_and_eq_or_eq_and_eq (hj ▸ hlink_ep)).imp (·.1.symm) (·.2.symm)).symm
  -- Every `a`-incident summand is carried by `edge i` or `edge (i−1)` (interior degree-2 closure).
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

/-! ### The eq.~(6.44) chain-induction anchor (CHAIN-2c-ii-arm, LEAF 2)

The base case of the KT eq.~(6.66) `±r` chain induction
(`notes/Phase23-design.md` §(o‴)(I.8.9-SETTLE), LEAF 2; Phase 23b). The chain induction is anchored
at the **first surviving interior chain vertex** `v₂ = cd.vtx 2`. At the base `v₁`-split
`G_v = G − vtx 1`, the `v₁`-removal kills `v₂`'s *predecessor* chain edge `edge 1 = v₁v₂` (which has
the removed apex as an endpoint), so `v₂` is **degree-ONE** in `G_v` — its only surviving incident
edge is the *successor* chain edge `edge 2 = v₂v₃` (the base-side de-risk verdict
`i3_base_interior_acolumn_single_deRisk`, §(o‴)(I.8.9-RESULT)). The candidate row `hρGv`, exposed
edge-grouped over `G_v`-links as `∑ⱼ cⱼ • hingeRow (uvⱼ)(vvⱼ)(rvⱼ) = hingeRow (ab) ρ₀` (the A-1
producer's eq.~(6.66) output), therefore has its `v₂`-column governed entirely by the single
`edge 2`-group: reading the candidate identity through the column-isolation core
`edgeIndexedCombination_comp_single_eq_incident` (only `v₂`-incident summands contribute) and the
degree-1 closure (every `v₂`-incident summand is `edge 2`) gives KT's anchor — the `edge 2`-group's
`v₂`-column equals the candidate row's `v₂`-column, which `hingeRow_comp_single_tail`/`_off` reads
as `±ρ₀` (the `e₀ = v₀v₂`-group of KT's eq.~(6.43) contributing `ρ₀`, the surviving sign absorbed by
the consumer's `neg_mem`). The `v₂`-column restriction `(·).comp (single v₂)` is the
orientation-agnostic screw functional the chain induction propagates as `±ρ₀`. -/

/-- **The eq.~(6.44) chain-induction anchor: the first interior chain-edge group's `v₂`-column is
the candidate row's `v₂`-column** (CHAIN-2c-ii-arm, the `hρGv` regroup chain induction LEAF 2;
Katoh–Tanigawa 2011 §6.4.2 eq.~(6.66) base / §6.4.1 eq.~(6.43), `notes/Phase23-design.md`
§(o‴)(I.8.9-SETTLE); Phase 23b). Let `g = ∑ⱼ cⱼ • hingeRow (uvⱼ)(vvⱼ)(rvⱼ)` be the candidate row
`hρGv` exposed edge-grouped over `G_v`-links (each summand `j` a genuine `G`-link `evⱼ` from `uvⱼ`
to `vvⱼ`), so `g` equals the candidate row `hingeRow ab₁ ab₂ ρ₀` (the A-1 producer's `hcomb`). At
the **first surviving interior chain vertex** `cd.vtx ⟨2, _⟩` — degree-ONE in `G_v = G − vtx 1`, its
only incident summand-edge the successor chain edge `edge ⟨2, _⟩` (the de-risked `hdeg1`) — the
candidate identity forces the `edge 2`-group's `v₂`-column to equal the candidate row's `v₂`-column:

`(∑_{evⱼ = edge 2} cⱼ • hingeRow (uvⱼ)(vvⱼ)(rvⱼ)).comp (single v₂)
  = (hingeRow ab₁ ab₂ ρ₀).comp (single v₂)`.

This is the chain induction's base case `P(2)` in the same `v₂`-column form as the step kernel
LEAF 1 (`interiorGroup_acolumn_adjacency`): the right-hand side is `±ρ₀` once the consumer reads it
through `hingeRow_comp_single_tail`/`_off` (LEAF 4), and the `e₀ = v₀v₂`-group of KT's eq.~(6.43)
contributing `ρ₀` is exactly this candidate row's tail-column. The proof: the column-isolation core
`edgeIndexedCombination_comp_single_eq_incident` reduces the `v₂`-column of `g` to its `v₂`-incident
summands; the degree-1 closure `hdeg1` (every `v₂`-incident summand is `edge 2`, since the
predecessor edge is shorn off at the base) together with "every `edge 2`-summand is `v₂`-incident"
(`hlink` + `IsLink` uniqueness at `edge 2 = v₂v₃`) collapses that to the `edge 2`-group; reading the
candidate identity `hcomb` on the `v₂`-column closes it. Framework-free, zero blast radius. -/
theorem _root_.Graph.ChainData.anchor_group_acolumn_eq_baseRedundancy [DecidableEq α]
    [DecidableEq β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (h3 : 3 ≤ cd.d)
    {m : ℕ} (c : Fin m → ℝ) (ev : Fin m → β) (uv vv : Fin m → α)
    (rv : Fin m → Module.Dual ℝ (ScrewSpace k))
    {ab₁ ab₂ : α} {ρ₀ : Module.Dual ℝ (ScrewSpace k)}
    (hlink : ∀ j, G.IsLink (ev j) (uv j) (vv j))
    (hcomb : (∑ j, c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j))
      = BodyHingeFramework.hingeRow ab₁ ab₂ ρ₀)
    (hdeg1 : ∀ j, (cd.vtx ⟨2, by omega⟩ = uv j ∨ cd.vtx ⟨2, by omega⟩ = vv j) →
      ev j = cd.edge ⟨2, by omega⟩) :
    (∑ j ∈ Finset.univ.filter (fun j => ev j = cd.edge ⟨2, by omega⟩),
        c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
      (LinearMap.single ℝ (fun _ : α => ScrewSpace k) (cd.vtx ⟨2, by omega⟩))
    = (BodyHingeFramework.hingeRow ab₁ ab₂ ρ₀).comp
      (LinearMap.single ℝ (fun _ : α => ScrewSpace k) (cd.vtx ⟨2, by omega⟩)) := by
  classical
  set a := cd.vtx ⟨2, by omega⟩ with ha
  set e2 := cd.edge ⟨2, by omega⟩ with he2
  -- `edge 2` links `vtx 2 — vtx 3` in `G` (`link ⟨2,_⟩`): a `G`-link incident to `a = vtx 2`.
  have hlink_e2 : G.IsLink e2 a (cd.vtx ⟨3, by omega⟩) := by
    have h := cd.link ⟨2, by omega⟩
    simpa only [he2, ha, Fin.castSucc_mk, Fin.succ_mk] using h
  -- A summand carried by `edge 2` is incident to `a` (its endpoints are `a`'s, by `IsLink` uniq).
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

/-! ### The eq.~(6.44) chain-induction endpoint-column flip + the induction itself
(CHAIN-2c-ii-arm, LEAF 3)

The `Nat.le_induction` chaining LEAF 2 (base) and LEAF 1 (step) into the closed form
`(edge i-group).comp (single vᵢ) = ±ρ₀` for every interior chain edge (`2 ≤ i ≤ d−1`); the `±`
sign alternates `(−1)^i` along the chain
(`notes/Phase23-design.md` §(o‴)(I.8.9-SETTLE), LEAF 3; Phase 23b). LEAF 1 relates the two incident
chain edges' columns *at their shared vertex* `vᵢ` (`group(edge i) @ vᵢ = −group(edge (i−1)) @ vᵢ`);
to chain that with the previous step's `P(i−1)` (about `group(edge (i−1)) @ v_{i−1}`, its *tail*
column) the step must flip `group(edge (i−1))`'s column from its head endpoint `vᵢ` back to its tail
`v_{i−1}` — the "two-endpoint-column orientation bookkeeping" of the shape-check note (ii). The flip
is the per-summand `hingeRow` antisymmetry: a hinge row's two endpoint-columns are negatives of each
other (`hingeRow_comp_single_endpoint_flip`), summed over an edge-group whose summands all link the
same pair `{vᵢ, vᵢ₋₁}` (`G`-link uniqueness at `edge (i−1)`). -/

/-- **A hinge row's two endpoint-columns are negatives of each other** (the per-summand orientation
bookkeeping of the eq.~(6.44) chain induction LEAF 3; Katoh–Tanigawa 2011 §6.4.1 eq.~(6.44),
Phase 23b). For a hinge `hingeRow x y ρ` between distinct bodies `x ≠ y`, the screw column at the
head `y` is *minus* the column at the tail `x`: `(hingeRow x y ρ).comp (single y) =
−(hingeRow x y ρ).comp (single x)`. Both columns are `±ρ` (`hingeRow_comp_single_tail` at `x` gives
`ρ`; the swap `hingeRow x y ρ = hingeRow y x (−ρ)` + tail at `y` gives `−ρ`), so they negate. This
is the antisymmetry the chain induction uses to flip an edge-group's column between its two
endpoints. -/
theorem BodyHingeFramework.hingeRow_comp_single_endpoint_flip [DecidableEq α] {x y : α}
    (hxy : x ≠ y) (ρ : Module.Dual ℝ (ScrewSpace k)) :
    (BodyHingeFramework.hingeRow (k := k) (α := α) x y ρ).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) y)
      = -(BodyHingeFramework.hingeRow (k := k) (α := α) x y ρ).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) x) := by
  rw [BodyHingeFramework.hingeRow_comp_single_tail hxy,
    BodyHingeFramework.hingeRow_swap x y ρ,
    BodyHingeFramework.hingeRow_comp_single_tail (Ne.symm hxy)]

/-- **An edge-group's two endpoint-columns are negatives of each other** (the edge-group form of
`hingeRow_comp_single_endpoint_flip`, the eq.~(6.44) chain induction LEAF 3; Katoh–Tanigawa 2011
§6.4.1 eq.~(6.44), Phase 23b). Let `∑ⱼ cⱼ • hingeRow (uvⱼ)(vvⱼ)(rvⱼ)` be an edge-indexed `hingeRow`
combination (each summand `j` a `G`-link `evⱼ`), and let `p ≠ q` be the two endpoints of a chain
edge `e`. Then the `e`-group's screw column at `q` is *minus* its column at `p`:

`(∑_{evⱼ = e} cⱼ • hingeRow (uvⱼ)(vvⱼ)(rvⱼ)).comp (single q)
  = −(∑_{evⱼ = e} cⱼ • hingeRow (uvⱼ)(vvⱼ)(rvⱼ)).comp (single p)`.

Each summand carried by `e` links `{p, q}` (`IsLink` uniqueness, `hpq`), so its two endpoint-columns
negate by `hingeRow_comp_single_endpoint_flip` regardless of its internal orientation (one of two
mirror `hingeRow_swap` cases). Summing the per-summand flip over the group gives the group flip.
This is the "two-endpoint-column orientation bookkeeping" the chain induction's step uses to move an
edge-group's column from its head endpoint to its tail. Framework-free, zero blast radius. -/
theorem BodyHingeFramework.edgeGroup_comp_single_endpoint_flip [DecidableEq α] [DecidableEq β]
    {G : Graph α β} {e : β} {p q : α} (hpq : p ≠ q) (hpq_link : G.IsLink e p q)
    {m : ℕ} (c : Fin m → ℝ) (ev : Fin m → β) (uv vv : Fin m → α)
    (rv : Fin m → Module.Dual ℝ (ScrewSpace k))
    (hlink : ∀ j, G.IsLink (ev j) (uv j) (vv j)) :
    (∑ j ∈ Finset.univ.filter (fun j => ev j = e),
        c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
      (LinearMap.single ℝ (fun _ : α => ScrewSpace k) q)
    = -(∑ j ∈ Finset.univ.filter (fun j => ev j = e),
        c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
      (LinearMap.single ℝ (fun _ : α => ScrewSpace k) p) := by
  classical
  -- Reduce the `LinearMap` equality to scalar equality at each `x`, distribute the column
  -- restriction over the filtered sum on both sides, and compare per summand.
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.coe_sum, Finset.sum_apply]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  -- The summand `j` is carried by `e`, so it links `{p, q}` (`IsLink` uniqueness).
  have hje : ev j = e := (Finset.mem_filter.mp hj).2
  have hjlink : G.IsLink e (uv j) (vv j) := hje ▸ hlink j
  -- Its endpoints are `{p, q}` in one of the two orders; the per-summand endpoint-column flip
  -- (`hingeRow_comp_single_endpoint_flip`) gives the per-summand negation either way.
  have hflip : (BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) q)
      = -(BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) p) := by
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

/-- **The eq.~(6.44) chain induction: every interior chain edge-group's tail-column equals the
anchor's** (CHAIN-2c-ii-arm, the `hρGv` regroup chain induction LEAF 3; Katoh–Tanigawa 2011 §6.4.1
eq.~(6.44)/§6.4.2 eq.~(6.66), `notes/Phase23-design.md` §(o‴)(I.8.9-SETTLE); Phase 23b). For the
**single base redundancy** `g = ∑ⱼ cⱼ • hingeRow (uvⱼ)(vvⱼ)(rvⱼ)` (each summand a `G`-link `evⱼ`)
exposed edge-grouped as the candidate row `hingeRow ab₁ ab₂ ρ₀` (A-1's `hcomb`), whose two endpoints
are the **redundant edge's** chain endpoints `ab₁ = vtx 0`, `ab₂ = vtx 2` (KT eq.~(6.52)'s
`(v₀v₂)`-block redundancy `r`; `hab₁`/`hab₂`), the `edge i`-group's screw column at its **tail**
vertex `vtx i` is the **same** for every interior chain edge `2 ≤ i ≤ d−1`, equal to the anchor
(`edge 2`) column:

`(∑_{evⱼ = edge i} cⱼ • hingeRow (uvⱼ)(vvⱼ)(rvⱼ)).comp (single (vtx i))
  = (hingeRow ab₁ ab₂ ρ₀).comp (single (vtx 2))`.

This is KT eq.~(6.66) — the single redundancy `r` carried with a *consistent* tail-column value
across the chain. The `±` of KT's prose is a per-edge orientation artifact absorbed by the
tail-column reading (`hingeRow_comp_single_endpoint_flip`): the step `P(i) → P(i+1)` applies LEAF 1
(`interiorGroup_acolumn_adjacency` at `i+1`, the `vtx (i+1)`-column adjacency `group(edge (i+1)) =
−group(edge i)`) then flips `group(edge i)`'s column from its head `vtx (i+1)` back to its tail
`vtx i` (`edgeGroup_comp_single_endpoint_flip`, the `−` cancelling LEAF 1's), leaving the value
unchanged; the base `P(2)` is LEAF 2 (`anchor_group_acolumn_eq_baseRedundancy`). The consumer reads
the common value as `±ρ₀` (LEAF 4, `hingeRow_comp_single_tail`/`_off`). Framework-free, zero blast
radius.

**Caller-satisfiability (the corrective, 2026-06-20).** LEAF 1's per-vertex column-vanishing `hcol`
is **not** assumed `∀ a` here — that would be jointly contradictory with `hcomb` for a non-zero
`r̂`: a screw functional on `α → ScrewSpace k` vanishing on every coordinate injection `single a` is
itself `0` (for `[Finite α]`, `LinearMap.pi_ext`), so `hcomb ∧ (∀a, g.comp (single a) = 0)` forces
`hingeRow ab₁ ab₂ ρ₀ = 0`, and the real `hρGv` caller (whose `r̂ = hingeRow (vtx 0)(vtx 2) ρ₀` has
`vtx 2`-column `ρ₀ ≠ 0`) cannot supply it. Instead the step **derives** the column-vanishing it
needs at the deeper step vertex `vtx (i+1)` (`i+1 ≥ 3`, off **both** redundant-edge endpoints
`vtx 0`, `vtx 2` by `vtx_ne`) **internally** from `hcomb` + `hingeRow_comp_single_off`: there
`g.comp (single (vtx (i+1))) = (hingeRow ab₁ ab₂ ρ₀).comp (single (vtx (i+1))) = 0`. This is the
honest content — the anchor `vtx 2` column of `r̂` is `ρ₀ ≠ 0` (LEAF 2 handles it separately, no
`hcol`), and only the deeper step vertices are off `r̂`'s support. -/
theorem _root_.Graph.ChainData.interior_group_eq_baseRedundancy [DecidableEq α] [DecidableEq β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (h3 : 3 ≤ cd.d)
    {m : ℕ} (c : Fin m → ℝ) (ev : Fin m → β) (uv vv : Fin m → α)
    (rv : Fin m → Module.Dual ℝ (ScrewSpace k))
    {ab₁ ab₂ : α} {ρ₀ : Module.Dual ℝ (ScrewSpace k)}
    (hlink : ∀ j, G.IsLink (ev j) (uv j) (vv j))
    (hcomb : (∑ j, c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j))
      = BodyHingeFramework.hingeRow ab₁ ab₂ ρ₀)
    (hab₁ : ab₁ = cd.vtx ⟨0, by omega⟩) (hab₂ : ab₂ = cd.vtx ⟨2, by omega⟩)
    (hdeg1 : ∀ j, (cd.vtx ⟨2, by omega⟩ = uv j ∨ cd.vtx ⟨2, by omega⟩ = vv j) →
      ev j = cd.edge ⟨2, by omega⟩)
    (i : ℕ) (h2i : 2 ≤ i) (hid : i < cd.d) :
    (∑ j ∈ Finset.univ.filter (fun j => ev j = cd.edge ⟨i, by omega⟩),
        c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
      (LinearMap.single ℝ (fun _ : α => ScrewSpace k) (cd.vtx ⟨i, by omega⟩))
    = (BodyHingeFramework.hingeRow ab₁ ab₂ ρ₀).comp
      (LinearMap.single ℝ (fun _ : α => ScrewSpace k) (cd.vtx ⟨2, by omega⟩)) := by
  classical
  induction i, h2i using Nat.le_induction with
  | base =>
    exact cd.anchor_group_acolumn_eq_baseRedundancy h3 c ev uv vv rv hlink hcomb hdeg1
  | succ i h2i ih =>
    -- `i + 1 < cd.d` (the current bound); the predecessor `i` is in range for the IH.
    have hid' : i < cd.d := by omega
    -- The deeper step vertex `vtx (i+1)` (`i+1 ≥ 3`) is off **both** redundant-edge endpoints
    -- `ab₁ = vtx 0`, `ab₂ = vtx 2` (distinct chain indices, `vtx_ne`).
    have hne₁ : cd.vtx (⟨i + 1, by omega⟩ : Fin cd.d).castSucc ≠ ab₁ := by
      rw [hab₁, Fin.castSucc_mk]
      exact cd.vtx_ne (m := i + 1) (m' := 0) (by omega) (by omega) (by omega)
    have hne₂ : cd.vtx (⟨i + 1, by omega⟩ : Fin cd.d).castSucc ≠ ab₂ := by
      rw [hab₂, Fin.castSucc_mk]
      exact cd.vtx_ne (m := i + 1) (m' := 2) (by omega) (by omega) (by omega)
    -- Derive LEAF 1's per-vertex column-vanishing at `vtx (i+1)` INTERNALLY from `hcomb`: the
    -- candidate row `hingeRow ab₁ ab₂ ρ₀` has a zero `vtx (i+1)`-column (off both endpoints,
    -- `hingeRow_comp_single_off`). This is the corrective — `hcol` is NOT assumed `∀ a`.
    have hcol_loc : (∑ j, c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k)
          (cd.vtx (⟨i + 1, by omega⟩ : Fin cd.d).castSucc)) = 0 := by
      rw [hcomb, BodyHingeFramework.hingeRow_comp_single_off hne₁ hne₂]
    -- LEAF 1 at the deeper interior vertex `vtx (i+1)` (index `⟨i+1, _⟩ : Fin cd.d`, `0 < i+1`):
    -- the `edge (i+1)`-group's `vtx (i+1)`-column is `−` the `edge i`-group's `vtx (i+1)`-column.
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
    -- Flip the `edge i`-group's column from its head `vtx (i+1)` to its tail `vtx i`: the head
    -- column is `−` the tail column, cancelling LEAF 1's sign.
    have hflip := BodyHingeFramework.edgeGroup_comp_single_endpoint_flip
      (e := cd.edge ⟨i, by omega⟩) hpq hlink_i c ev uv vv rv hlink
    -- `colTail (i+1) = −(edge i-group @ vtx (i+1)) = −(−(edge i-group @ vtx i)) = colTail i = RHS`.
    rw [hadj, hflip, neg_neg]
    exact ih hid'

/-! ### The chain-induction consumer reading: every interior edge-group's tail column is `−ρ₀`
(CHAIN-2c-ii-arm, LEAF 4)

The consumer adapter that turns LEAF 3's *constant common tail column* into the concrete value the
`hρGv` arm consumes: the redundant base row `hingeRow ab₁ ab₂ ρ₀` (`ab₁ = vtx 0`, `ab₂ = vtx 2`, the
eq.~(6.52) spliced edge `e₀ = v₀v₂`) read on its head body `ab₂ = vtx 2`'s screw column is `−ρ₀`
(`hingeRow_swap` + `hingeRow_comp_single_tail`), so LEAF 3's constant value
`(hingeRow ab₁ ab₂ ρ₀).comp (single (vtx 2)) = −ρ₀`. Composed with LEAF 3, every interior chain
edge-group's screw column at its tail body `vᵢ` equals `−ρ₀` (`2 ≤ i ≤ d−1`):

`(∑_{evⱼ = edge i} cⱼ • hingeRow (uvⱼ)(vvⱼ)(rvⱼ)).comp (single vᵢ) = −ρ₀`.

This is KT eq.~(6.66)'s `±r` — the single redundancy `r` carried with the constant screw-column
value `−ρ₀` along the whole interior chain (the `±` is absorbed into the orientation-agnostic
tail-column reading, see LEAF 3). The `hρGv` arm wiring consumes it: the `neg_mem` flips it to the
engine slot's `ρ₀`, and `freshEdge_surviving_row_mem` (via the A-2 carrier) reads it as the per-edge
perp discharge. Framework-free, zero blast radius. -/
theorem _root_.Graph.ChainData.interior_group_acolumn_eq_neg_baseRedundancy [DecidableEq α]
    [DecidableEq β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (h3 : 3 ≤ cd.d)
    {m : ℕ} (c : Fin m → ℝ) (ev : Fin m → β) (uv vv : Fin m → α)
    (rv : Fin m → Module.Dual ℝ (ScrewSpace k))
    {ab₁ ab₂ : α} {ρ₀ : Module.Dual ℝ (ScrewSpace k)}
    (hlink : ∀ j, G.IsLink (ev j) (uv j) (vv j))
    (hcomb : (∑ j, c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j))
      = BodyHingeFramework.hingeRow ab₁ ab₂ ρ₀)
    (hab₁ : ab₁ = cd.vtx ⟨0, by omega⟩) (hab₂ : ab₂ = cd.vtx ⟨2, by omega⟩)
    (hdeg1 : ∀ j, (cd.vtx ⟨2, by omega⟩ = uv j ∨ cd.vtx ⟨2, by omega⟩ = vv j) →
      ev j = cd.edge ⟨2, by omega⟩)
    (i : ℕ) (h2i : 2 ≤ i) (hid : i < cd.d) :
    (∑ j ∈ Finset.univ.filter (fun j => ev j = cd.edge ⟨i, by omega⟩),
        c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)).comp
      (LinearMap.single ℝ (fun _ : α => ScrewSpace k) (cd.vtx ⟨i, by omega⟩))
    = -ρ₀ := by
  classical
  -- LEAF 3: the `edge i`-group's tail column is the constant base value
  -- `(hingeRow ab₁ ab₂ ρ₀).comp (single (vtx 2))`.
  rw [cd.interior_group_eq_baseRedundancy h3 c ev uv vv rv hlink hcomb hab₁ hab₂ hdeg1 i h2i hid]
  -- The redundant base row read on its head body `ab₂ = vtx 2`: `hingeRow ab₁ ab₂ ρ₀ =
  -- hingeRow ab₂ ab₁ (−ρ₀)` (`hingeRow_swap`), whose tail column at `ab₂` is `−ρ₀`
  -- (`hingeRow_comp_single_tail`). `ab₁ ≠ ab₂` (distinct chain vertices `vtx 0`/`vtx 2`).
  have hne : ab₂ ≠ ab₁ := by
    rw [hab₁, hab₂]
    exact fun he => by have : (2 : ℕ) = 0 := congrArg Fin.val (cd.vtx_inj he); omega
  rw [← hab₂, BodyHingeFramework.hingeRow_swap ab₁ ab₂ ρ₀,
    BodyHingeFramework.hingeRow_comp_single_tail hne]

/-- **The candidate-transported `±r` column value is `−ρ₀`** (`lem:case-III general-d`, the
option-(A) chain arm's `hrCol` bridge, Phase 23c §I.8.24(4.5)(α); Katoh–Tanigawa 2011 §6.4.2 eqs.
(6.62)/(6.66), the `±r` redundancy carried with constant screw-column value `−ρ₀` across the cycle
relabel). The `notMem_span_mkQ_pmR_row_of_gate` discriminator leaf (`Candidate.lean`) consumes the
`±r` row's column value at the re-inserted candidate body `vᵢ`; this leaf supplies it. The
candidate-`i` `±r` row is the relabel image `(funLeft (shiftPerm i.castSucc)⁻¹).dualMap` of the base
interior edge-`i`-group `φ = ∑_{evⱼ = edge i} cⱼ • hingeRow (uvⱼ)(vvⱼ)(rvⱼ)` (KT (6.56): the
candidate seed `qᵢ = q₁ ∘ ρᵢ` pairs with the **inverse** cycle relabel `(shiftPerm i.castSucc)⁻¹` on
the rows). Reading that candidate row at the candidate base body `vᵢ₋₁ = vtx (i−1)`'s screw column
`single (vtx (i−1))` equals, by the column-naturality bridge `funLeft_dualMap_comp_single`, reading
the base group `φ` at body `((shiftPerm i.castSucc)⁻¹).symm (vtx (i−1)) = shiftPerm i.castSucc
(vtx (i−1)) = vtx i`'s column — which is the base `−ρ₀` of
`interior_group_acolumn_eq_neg_baseRedundancy` (the column read at `vtx i`, `2 ≤ i ≤ d−1`). So the
member MOVES (the row is the relabel image) while the abstract redundancy `ρ₀` stays fixed (the
column value is the constant `−ρ₀`) — the wall-escape, KT's (6.66). At the `d = 3` `M₃` instance
`i = 2` the cycle `shiftPerm 2 = (v₁ v₂)` is the single swap and this is the M₃ arm's
`hingeRow_funLeft_dualMap` + `hingeRow_comp_single_tail` step at length 1. -/
theorem _root_.Graph.ChainData.funLeft_dualMap_interior_group_acolumn_eq_neg_baseRedundancy
    [DecidableEq α] [DecidableEq β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (h3 : 3 ≤ cd.d)
    {m : ℕ} (c : Fin m → ℝ) (ev : Fin m → β) (uv vv : Fin m → α)
    (rv : Fin m → Module.Dual ℝ (ScrewSpace k))
    {ab₁ ab₂ : α} {ρ₀ : Module.Dual ℝ (ScrewSpace k)}
    (hlink : ∀ j, G.IsLink (ev j) (uv j) (vv j))
    (hcomb : (∑ j, c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j))
      = BodyHingeFramework.hingeRow ab₁ ab₂ ρ₀)
    (hab₁ : ab₁ = cd.vtx ⟨0, by omega⟩) (hab₂ : ab₂ = cd.vtx ⟨2, by omega⟩)
    (hdeg1 : ∀ j, (cd.vtx ⟨2, by omega⟩ = uv j ∨ cd.vtx ⟨2, by omega⟩ = vv j) →
      ev j = cd.edge ⟨2, by omega⟩)
    (i : ℕ) (h2i : 2 ≤ i) (hid : i < cd.d) :
    ((LinearMap.funLeft ℝ (ScrewSpace k)
          (cd.shiftPerm (⟨i, by omega⟩ : Fin (cd.d + 1))).symm).dualMap
        (∑ j ∈ Finset.univ.filter (fun j => ev j = cd.edge ⟨i, by omega⟩),
          c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j))).comp
      (LinearMap.single ℝ (fun _ : α => ScrewSpace k) (cd.vtx ⟨i - 1, by omega⟩))
    = -ρ₀ := by
  -- The cycle `shiftPerm ⟨i,_⟩` reads at index `i` (the cycle of `[vtx 1, …, vtx i]`).
  -- Column-naturality (`funLeft_dualMap_comp_single`) at `σ = (shiftPerm ⟨i,_⟩).symm`,
  -- `w = vtx (i−1)`: the candidate column at `vtx (i−1)` is the base group's column at
  -- `σ.symm (vtx (i−1)) = shiftPerm ⟨i,_⟩ (vtx (i−1)) = vtx i`.
  rw [BodyHingeFramework.funLeft_dualMap_comp_single, Equiv.symm_symm]
  -- `shiftPerm ⟨i,_⟩` sends the interior `vtx (i−1)` to `vtx i` (`shiftPerm_apply_interior`,
  -- `1 ≤ i−1 < i`); rewrite the column index `vtx (i−1) ↦ vtx i`.
  have hkey := cd.shiftPerm_apply_interior (⟨i, by omega⟩ : Fin (cd.d + 1))
    (j := i - 1) (by omega) (by simp only; omega)
  have hidx : (⟨(i - 1) + 1, by omega⟩ : Fin (cd.d + 1)) = (⟨i, by omega⟩ : Fin (cd.d + 1)) := by
    simp only [Fin.mk.injEq]; omega
  rw [hidx] at hkey
  rw [hkey]
  -- The base group's column at `vtx i` is `−ρ₀` (eq. (6.66)).
  exact cd.interior_group_acolumn_eq_neg_baseRedundancy h3 c ev uv vv rv hlink hcomb hab₁ hab₂
    hdeg1 i h2i hid

/-! ### P3 — the seed bridge `shiftSeedAdv = q ∘ shiftPerm` (CHAIN-2c-ii-arm)

The seed-advancing fold `shiftBodyListAsc_foldl_mem_span_rigidityRows` proves the `hρGv` span
membership at the *fold* seed `shiftSeedAdv q (i − 1)` — the base seed `q` post-composed (on the
vertex slot) with the first `i − 1` cycle swaps `(v₂ v₁), …, (vᵢ vᵢ₋₁)`, applied one per step.
The arm engine `case_III_arm_realization`, by contrast, binds its candidate seed as `qρ = q ∘
shiftPerm i.castSucc` (KT eq. (6.56), the candidate seed `qᵢ = q₁ ∘ ρᵢ`). These two must coincide
for the fold's span output to feed the engine's `hρGv` slot. They do: the `i − 1` ascending cycle
swaps composed left-to-right ARE `shiftPerm i.castSucc` (the permutation-level G1 bridge
`shiftPerm_eq_prod_map_swap_shiftBodyListAsc`).

The bridge (flagged P3, §(o‴)(I.8.4)/(I.8) — "the fold seed = the engine seed"). At the `d = 3`
`M₃` instance `i = 2` the cycle `shiftPerm 2 = (v₁ v₂)` is the single swap, and `shiftSeedAdv q 1 =
q ∘ swap` is the engine's `qρ` verbatim (zero-regression). -/

/-- **The seed accumulator as a swap-product reindex of `q`** (the P3 closed form). The
seed-advancing accumulator `shiftSeedAdv q s` post-composes the base seed `q` on its vertex slot
with the product of the first `s` per-step cycle swaps `[shiftSeedSwap 0, …, shiftSeedSwap (s−1)]`
(read left-to-right, head outermost). Proved by induction on `s`: the base is `prod [] = 1`, and the
step peels the last swap off `List.ofFn (· + 1)` via `ofFn_succ'` + `List.prod_concat`
(so `(P * swap) x = P (swap x)`), matching `shiftSeedAdv`'s recursion `Q (s+1) = Q s ∘ swap`.
Graph-free over the carrier. -/
theorem _root_.Graph.ChainData.shiftSeedAdv_eq_prod_shiftSeedSwap [DecidableEq α]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (q : α × Fin (k + 2) → ℝ) (s : ℕ) :
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

/-- **P3 — the fold seed equals the engine seed `q ∘ shiftPerm i.castSucc`** (CHAIN-2c-ii-arm;
the flagged seed bridge `shiftSeedAdv_eq_funLeft_shiftPerm`, design §(o‴)(I.8.4)).
The seed-advancing fold's accumulator at the top step `shiftSeedAdv q (i − 1)` (the seed feeding
`shiftBodyListAsc_foldl_mem_span_rigidityRows`'s span output) coincides with the relabel arm
engine's candidate seed `qρ = fun p => q (shiftPerm i.castSucc p.1, p.2)` (KT eq. (6.56)) — for a
nondegenerate interior candidate `i` (`1 ≤ i`). The proof reads `shiftSeedAdv q (i − 1)` as the
product of the `i − 1` per-step swaps (`shiftSeedAdv_eq_prod_shiftSeedSwap`), then identifies that
product with `shiftPerm i.castSucc` via the permutation-level G1 bridge
`shiftPerm_eq_prod_map_swap_shiftBodyListAsc` (whose `s`-th swap `swap (vtx (s+2)) (vtx (s+1))` is
exactly `shiftSeedSwap s` over the in-range cycle, by `getElem_shiftBodyListAsc` +
`shiftSeedSwap_eq`). Graph-free over the carrier; the `d = 3` `i = 2` instance is the single-swap
`M₃` seed (zero-regression). -/
theorem _root_.Graph.ChainData.shiftSeedAdv_eq_funLeft_shiftPerm [DecidableEq α]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (q : α × Fin (k + 2) → ℝ) (i : Fin cd.d)
    (hi : 1 ≤ (i : ℕ)) :
    cd.shiftSeedAdv q ((i : ℕ) - 1)
      = fun p => q (cd.shiftPerm i.castSucc p.1, p.2) := by
  rw [cd.shiftSeedAdv_eq_prod_shiftSeedSwap q ((i : ℕ) - 1)]
  -- The `i − 1`-fold swap product is `shiftPerm i.castSucc` (the ascending G1 bridge), after
  -- matching the per-step swaps element-for-element (`shiftSeedSwap s = swap (vₛ₊₂) (vₛ₊₁)`).
  have hlist : (List.ofFn fun t : Fin ((i : ℕ) - 1) => cd.shiftSeedSwap t)
      = (cd.shiftBodyListAsc i).map (fun b => Equiv.swap b.2.1 b.1) := by
    refine List.ext_getElem (by simp only [List.length_ofFn, List.length_map,
      cd.length_shiftBodyListAsc]) fun s h₁ h₂ => ?_
    simp only [List.getElem_ofFn, List.getElem_map, cd.getElem_shiftBodyListAsc]
    have hs : s + 2 < cd.d + 1 := by
      simp only [List.length_ofFn] at h₁; have := i.2; omega
    rw [cd.shiftSeedSwap_eq hs]
  rw [hlist, ← cd.shiftPerm_eq_prod_map_swap_shiftBodyListAsc i]

/-! ### The general-`i` `hρGv` fresh-edge slot membership (CHAIN-2c-ii-arm, LEAF 5 core)

The general-candidate-`i` lift of the `i = 3` de-risk gate `i3_freshEdge_slot_mem_deRisk` from the
abstract span carrier `S` to the *concrete* fold framework, threading the genuinely-new infra of
LEAF-ρ1/the chain induction into the engine `hρGv` slot. Given the W6b base redundancy
`hingeRow (vtx 0) (vtx 2) ρ₀ ∈ span (G − v₁) rows` and, for each surviving interior chain edge
`edge s` (`s + 1 < (i : ℕ)`), the per-edge perp `ρ₀ ⊥ Fva.supportExtensor (edge s)` (the P2 content
the chain induction LEAF 4 + the A-2 carrier supply), the fresh-edge slot row
`hingeRow (vtx (i−1)) (vtx (i+1)) ρ₀` — the engine `case_III_arm_realization.hρGv` slot
`hingeRow vᵢ₋₁ vᵢ₊₁ ρ` at candidate `i` — reaches the candidate framework's rigidity-row span.

The assembly: feed the base redundancy through the landed seed-advancing W9a fold
(`shiftBodyListAsc_foldl_mem_span_rigidityRows`, output span at `shiftBodyFrameworkAsc (i−1) =
ofNormals (G − vᵢ) ends (shiftSeedAdv q (i−1))`), giving `W φ ∈ span`; the landed closed-form
telescope `wstep_foldl_freshEdge_slot_mem` then peels the slot row off `W φ` minus the `m = i − 1`
genuine surviving chain-edge rows, each supplied by `freshEdge_surviving_row_mem` from its per-edge
perp. KT eq. (6.66) realized concretely. The `d = 3` `M₃` `case hρGv` is the `i = 2` (`m = 1`,
single-summand) special case (zero-regression). This isolates LEAF 5's hard core; the arm wiring
`chainData_relabel_arm` rewrites the fold seed `shiftSeedAdv q (i−1)` to the engine seed `qρ`
(P3 `shiftSeedAdv_eq_funLeft_shiftPerm`), flips the orientation (`hingeRow_swap`), and discharges
the per-edge perps from LEAF 4 + A-2. -/
theorem _root_.Graph.ChainData.chainData_freshEdge_slot_mem [DecidableEq α]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (i : Fin (cd.d + 1))
    (hi : 1 ≤ (i : ℕ)) (hid : (i : ℕ) < cd.d)
    (ends : β → α × α) (q : α × Fin (k + 2) → ℝ)
    (hrec : ∀ f x y, G.IsLink f x y → ends f = (x, y) ∨ ends f = (y, x))
    {ρ₀ : Module.Dual ℝ (ScrewSpace k)}
    -- the W6b base redundancy `hingeRow (vtx 0)(vtx 2) ρ₀ ∈ span (G − v₁) rows`:
    (hφ : BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ₀ ∈
      Submodule.span ℝ
        (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩)) ends
          (cd.shiftSeedAdv q 0)).toBodyHinge.rigidityRows)
    -- the per-edge perp obligations (P2: each surviving chain-edge panel is ⊥ ρ₀):
    (hperp : ∀ s : ℕ, (hs : s + 1 < (i : ℕ)) → ρ₀ ((PanelHingeFramework.ofNormals
        (G.removeVertex (cd.vtx ⟨(i : ℕ), by omega⟩)) ends
          (cd.shiftSeedAdv q ((i : ℕ) - 1))).toBodyHinge.supportExtensor
          (cd.edge ⟨s, by omega⟩)) = 0) :
    BodyHingeFramework.hingeRow (cd.vtx ⟨(i : ℕ) - 1, by omega⟩) (cd.vtx ⟨(i : ℕ) + 1, by omega⟩) ρ₀
      ∈ Submodule.span ℝ (PanelHingeFramework.ofNormals
        (G.removeVertex (cd.vtx ⟨(i : ℕ), by omega⟩)) ends
          (cd.shiftSeedAdv q ((i : ℕ) - 1))).toBodyHinge.rigidityRows := by
  classical
  -- the `Fin cd.d` version of the candidate index (for the fold lemma + the seed bridge).
  let i' : Fin cd.d := ⟨(i : ℕ), hid⟩
  have hi'v : (i' : ℕ) = (i : ℕ) := rfl
  -- the candidate framework `Fva = ofNormals (G − vᵢ) ends (shiftSeedAdv q (i−1))`.
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
  -- `shiftBodyFrameworkAsc (i'−1) = Fva` (seed `shiftSeedAdv q (i−1)`, graph
  -- `G − v_{(i−1)+1} = G − vᵢ`).
  have hidx : (⟨((i' : ℕ) - 1) + 1, by have := i'.2; omega⟩ : Fin (cd.d + 1))
      = ⟨(i : ℕ), by omega⟩ := Fin.ext (by simp only [hi'v]; omega)
  have hFvaEq : cd.shiftBodyFrameworkAsc (s := (i' : ℕ) - 1) (by have := i'.2; omega) ends q
      = Fva := by
    rw [Graph.ChainData.shiftBodyFrameworkAsc, hFva]
    congr 2
    rw [Graph.ChainData.shiftBodyGraph]
    exact congrArg (fun x => G.removeVertex (cd.vtx x)) hidx
  -- fold start framework `shiftBodyFrameworkAsc 0 = ofNormals (G − v₁) ends (shiftSeedAdv q 0)`.
  have hFvaStart : cd.shiftBodyFrameworkAsc (s := 0) (by have := i'.2; omega) ends q
      = (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩)) ends
          (cd.shiftSeedAdv q 0)).toBodyHinge := by
    rw [Graph.ChainData.shiftBodyFrameworkAsc, Graph.ChainData.shiftBodyGraph]
  -- `hW`: the seed-advancing fold lands `W φ ∈ span Fva.rigidityRows` (`shiftBodyFrameworkAsc
  -- (i−1) = Fva`, after feeding the base redundancy `hφ` matched to the start framework).
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
  -- the `hsurv` summands: each surviving chain-edge row `hingeRow (w s) (w (s+1)) ρ₀ ∈ span`
  -- via `freshEdge_surviving_row_mem` from its per-edge perp `hperp s`.
  have hsurv : ∀ s ∈ Finset.range ((i' : ℕ) - 1),
      BodyHingeFramework.hingeRow (w s) (w (s + 1)) ρ₀ ∈ Submodule.span ℝ Fva.rigidityRows := by
    intro s hs
    rw [Finset.mem_range] at hs
    rw [hws s (by omega) (by omega), hws (s + 1) (by omega) (by omega)]
    -- `freshEdge_surviving_row_mem`'s framework `ofNormals (G − vᵢ) ends (shiftSeedAdv q (i−1))`
    -- is exactly `Fva` (up to the `set` abbreviation).
    exact cd.freshEdge_surviving_row_mem i s (by omega) ρ₀ (hperp s (by omega))
  -- Apply the telescope (`m = i' − 1 = i − 1`): peel the slot row `hingeRow (w m) (w (m+2)) ρ₀`
  -- off the fold output minus the `m` genuine surviving rows.
  have hslot := BodyHingeFramework.wstep_foldl_freshEdge_slot_mem w ((i' : ℕ) - 1) hinj ρ₀ hfold
    hsurv
  -- the slot row is the conclusion after `w m = vtx (i−1)`, `w (m+2) = vtx (i+1)`.
  rw [hws ((i' : ℕ) - 1) (by omega) (by omega),
    hws (((i' : ℕ) - 1) + 2) (by omega) (by omega)] at hslot
  convert hslot using 4
  omega

/-- **The per-edge perp discharge from the eq.~(6.52) two-edge witness** (CHAIN-2c-ii-arm, the
`hρGv` P2 A-2 composition step; `notes/Phase23-design.md` §(o‴)(I.8.3.v-SETTLED) Route A,
§(o‴)(I.8.9-SETTLE); Phase 23b). The single-edge form of the per-edge perp that
`chainData_freshEdge_slot_mem`'s `hperp` slot consumes: from the eq.~(6.52) `λ`-grouped two-edge
witness at the surviving edge's interior degree-2 chain vertex `vtx (s+1)` (the same witness the W6b
producer `exists_candidateRow_bottomRows_of_rigidOn` supplies, A-1), the common candidate redundancy
`ρ₀ = ∑_j λ_{(ab)j} (rab j)` is ⊥ the candidate framework's `supportExtensor (edge s)`.

The interior vertex `a := vtx (s+1)` is degree-2 with the two incident chain edges `e_c := edge s`
(to its predecessor `b := vtx s`) and `e_d := edge (s+1)` (to its successor `c := vtx (s+2)`).
Feeding the witness perps `hperp_ab`/`hperp_ac` and the eq.~(6.43) column vanishing `hcol`/`hrest`
through `candidate_perp_two_incident_supportExtensors` (A-2, KT eq.~(6.44)) yields the perp at
`e_c = edge s`; the supplied regroup identity `hρ₀` (`∑_j λ_{(ab)j} (rab j) = ρ₀`, the chain
induction LEAF 4's `group = ±ρ₀` reading) rewrites it onto the shared `ρ₀` of the slot core. This
is the exact `hperp s` shape `chainData_freshEdge_slot_mem` takes per surviving chain edge; the arm
`chainData_relabel_arm` calls it once per `s + 1 < i` to supply that slot's `hperp` from the
witnesses. Self-contained over the explicit witness, zero blast radius. -/
theorem _root_.Graph.ChainData.chainData_freshEdge_perp_of_witness [DecidableEq α]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (i : Fin (cd.d + 1)) (s : ℕ)
    (hsd : s + 1 < cd.d)
    {ends : β → α × α} {qρ : α × Fin (k + 2) → ℝ}
    {ιab ιac : Type*} [Fintype ιab] [Fintype ιac]
    (lamAB : ιab → ℝ) (rab : ιab → Module.Dual ℝ (ScrewSpace k))
    (lamAC : ιac → ℝ) (rac : ιac → Module.Dual ℝ (ScrewSpace k))
    (grest : Module.Dual ℝ (α → ScrewSpace k))
    {ρ₀ : Module.Dual ℝ (ScrewSpace k)}
    -- the regroup identity: the `(ab)`-group is the shared slot redundancy `ρ₀` (LEAF 4):
    (hρ₀ : (∑ j, lamAB j • rab j) = ρ₀)
    -- the per-edge witness-row perps, in the candidate framework `Fva = ofNormals (G−vᵢ)`:
    (hperp_ab : ∀ j, rab j ((PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i)) ends qρ)
      |>.toBodyHinge.supportExtensor (cd.edge ⟨s, by omega⟩)) = 0)
    (hperp_ac : ∀ j, rac j ((PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i)) ends qρ)
      |>.toBodyHinge.supportExtensor (cd.edge ⟨s + 1, by omega⟩)) = 0)
    -- the eq.~(6.43) column vanishing at the degree-2 interior vertex `a = vtx (s+1)`:
    (hcol : ((∑ j, lamAB j • BodyHingeFramework.hingeRow (k := k) (α := α)
          (cd.vtx ⟨s + 1, by omega⟩) (cd.vtx ⟨s, by omega⟩) (rab j))
        + (∑ j, lamAC j • BodyHingeFramework.hingeRow (k := k) (α := α)
          (cd.vtx ⟨s + 1, by omega⟩) (cd.vtx ⟨s + 2, by omega⟩) (rac j)) + grest).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) (cd.vtx ⟨s + 1, by omega⟩)) = 0)
    (hrest : grest.comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) (cd.vtx ⟨s + 1, by omega⟩)) = 0) :
    ρ₀ ((PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i)) ends qρ)
      |>.toBodyHinge.supportExtensor (cd.edge ⟨s, by omega⟩)) = 0 := by
  classical
  set Fva := (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i)) ends qρ).toBodyHinge
    with hFva
  -- The interior vertex `a = vtx (s+1)` differs from its two chain neighbours `b = vtx s`,
  -- `c = vtx (s+2)` (distinct chain indices, `vtx_inj`).
  have hab : cd.vtx ⟨s + 1, by omega⟩ ≠ cd.vtx ⟨s, by omega⟩ :=
    fun he => by have : s + 1 = s := congrArg Fin.val (cd.vtx_inj he); omega
  have hac : cd.vtx ⟨s + 1, by omega⟩ ≠ cd.vtx ⟨s + 2, by omega⟩ :=
    fun he => by have : s + 1 = s + 2 := congrArg Fin.val (cd.vtx_inj he); omega
  -- A-2 (KT eq.~(6.44)): the common candidate `∑_j λ_{(ab)j} (rab j)` is ⊥ the panel at the
  -- surviving edge `e_c = edge s`; rewrite onto the shared `ρ₀` via the regroup identity.
  have hperp := (Fva.candidate_perp_two_incident_supportExtensors hab hac lamAB rab lamAC rac grest
    hperp_ab hperp_ac hcol hrest).1
  rwa [hρ₀] at hperp

/-- **The per-edge perp discharged from the single candidate-framework base redundancy**
(CHAIN-2c-ii-arm, the `hρGv` P2 Route-W all-`i` lift; `notes/Phase23-design.md`
§(o‴)(I.8.9-SETTLE); Phase 23b). The witness-free closure of the per-edge perpendicularity that
`chainData_freshEdge_slot_mem` consumes: instead of supplying the eq.~(6.52) two-edge witness
vertex-by-vertex (`chainData_freshEdge_perp_of_witness`), it is discharged for **every** deeper
interior surviving chain edge `edge s` (`2 ≤ s`, `s < cd.d`) from the *one* candidate-framework base
redundancy, exposed edge-grouped (A-1's `hcomb`,
`exists_edgeIndexed_combination_of_mem_span_rigidityRows`).

The mechanism is KT eq.~(6.66)'s iterated degree-2 `±r` carry, now closed in two landed halves:
- the **chain induction LEAF 4** (`interior_group_acolumn_eq_neg_baseRedundancy`) — the `edge
  s`-group's screw column at its tail vertex `vtx s` is `−ρ₀`, the single redundancy `r` carried
  with a constant column value along the chain (eq.~(6.44) iterated, anchored at the spliced
  `e₀ = v₀v₂`);
- the **column-in-block core** (`edgeGroup_acolumn_mem_block`) — that same `edge s`-group column
  lies in `Fva.hingeRowBlock (edge s)` (each summand carried by `edge s` reads
  `±rv j ∈ block (edge s)` on the column, the block closed under negation and zero).

Combining, `−ρ₀ ∈ Fva.hingeRowBlock (edge s)`, so `ρ₀ ∈ Fva.hingeRowBlock (edge s)`
(negation-closed), which is exactly `ρ₀ ⊥ Fva.supportExtensor (edge s)` (`mem_hingeRowBlock_iff`).
No per-vertex witness production, no eq.~(6.52) `λ`-data threading — the arm `chainData_relabel_arm`
supplies the slot core's `hperp` for all deeper surviving edges from this one base redundancy. The
first surviving edge (the degree-1 anchor `edge 2`) is the `s = 2` instance (LEAF 4's base `P(2)`).
Framework-bound, zero blast radius. -/
theorem _root_.Graph.ChainData.chainData_freshEdge_perp_of_baseRedundancy
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (h3 : 3 ≤ cd.d)
    (i : Fin (cd.d + 1)) (s : ℕ) (h2s : 2 ≤ s) (hsd : s < cd.d)
    {ends : β → α × α} {qρ : α × Fin (k + 2) → ℝ}
    {m : ℕ} (c : Fin m → ℝ) (ev : Fin m → β) (uv vv : Fin m → α)
    (rv : Fin m → Module.Dual ℝ (ScrewSpace k))
    {ρ₀ : Module.Dual ℝ (ScrewSpace k)}
    -- the candidate-framework `Fva = ofNormals (G − vᵢ)` edge-grouped base redundancy (A-1 `hcomb`)
    (hlink : ∀ j, G.IsLink (ev j) (uv j) (vv j))
    (hrv : ∀ j, rv j ∈ (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i)) ends
      qρ).toBodyHinge.hingeRowBlock (ev j))
    (hcomb : (∑ j, c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j))
      = BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ₀)
    -- the degree-1-at-anchor closure (the first surviving interior vertex `vtx 2`):
    (hdeg1 : ∀ j, (cd.vtx ⟨2, by omega⟩ = uv j ∨ cd.vtx ⟨2, by omega⟩ = vv j) →
      ev j = cd.edge ⟨2, by omega⟩) :
    ρ₀ ((PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i)) ends
      qρ).toBodyHinge.supportExtensor (cd.edge ⟨s, by omega⟩)) = 0 := by
  classical
  set Fva := (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i)) ends qρ).toBodyHinge
    with hFva
  -- The `edge s`-group's `vtx s`-column is `−ρ₀` (chain induction LEAF 4), and lands in
  -- `Fva.hingeRowBlock (edge s)` (the column-in-block core). So `−ρ₀ ∈ block (edge s)`.
  have hcolval := cd.interior_group_acolumn_eq_neg_baseRedundancy h3 c ev uv vv rv hlink hcomb
    rfl rfl hdeg1 s h2s hsd
  have hmem := Fva.edgeGroup_acolumn_mem_block (e := cd.edge ⟨s, by omega⟩)
    (p := cd.vtx ⟨s, by omega⟩) c ev uv vv rv hrv
  rw [hcolval] at hmem
  -- `−ρ₀ ∈ block (edge s) ⟹ ρ₀ ∈ block ⟹ ρ₀ ⊥ supportExtensor (edge s)`.
  have hρ₀mem : ρ₀ ∈ Fva.hingeRowBlock (cd.edge ⟨s, by omega⟩) := by
    have := (Fva.hingeRowBlock (cd.edge ⟨s, by omega⟩)).neg_mem hmem
    rwa [neg_neg] at this
  exact (Fva.mem_hingeRowBlock_iff (cd.edge ⟨s, by omega⟩) ρ₀).1 hρ₀mem

/-! ### The i=3 candidate-level edge-grouped transport de-risk (CHAIN-2c-ii-arm)

The row-352 GAP-FOUND recon (`notes/Phase23-design.md` §(o‴)(I.8); Phase 23b) located the single
remaining gap between the landed `hρGv` pieces and the arm `chainData_relabel_arm`: the per-edge
perp leaf `chainData_freshEdge_perp_of_baseRedundancy` consumes the edge-grouped base redundancy
`hcomb` together with the per-summand block memberships `hrv : ∀ j, rv j ∈ Fva.hingeRowBlock (ev j)`
**at the CANDIDATE framework** `Fva = ofNormals (G − vᵢ) endsσρ qρ`, but the W6b producer A-1
(`exists_candidateRow_bottomRows_of_rigidOn`) supplies the edge-grouped redundancy only at the
**BASE** framework `ofNormals (G − v₁) ends q` (`Candidate.lean`). No landed lemma transports the
edge-grouped block memberships from base to candidate (candidate-level `hrv` appears only as a
hypothesis, never a conclusion).

The flagged subtlety (de-risk-first, row-321 discipline): A-1's base summand edges `ev j` are
ARBITRARY `(G − v₁)`-links — they need NOT be `shiftEdgePerm`-images of candidate chain edges. The
de-risk question is whether the per-summand block transport is nonetheless clean: does
`rv j ∈ (base).hingeRowBlock (ev j)` transport to a candidate block membership without re-grouping?

**Verdict (this lemma, ground-truth in Lean): YES — the per-summand transport is a clean bijective
re-index, NOT a re-grouping.** The candidate framework's `hingeRowBlock` at an ARBITRARY edge `f`
equals the base framework's `hingeRowBlock` at `(shiftEdgePerm i) f` (the support extensors coincide
under the relabel, `ofNormals_supportExtensor_relabel_perm`, for *every* edge — the base graph is
irrelevant since `supportExtensor` reads only `ends`/`normal`). So A-1's base membership
`rv j ∈ (base).hingeRowBlock (ev j)` is exactly the candidate membership
`rv j ∈ Fva.hingeRowBlock ((shiftEdgePerm i).symm (ev j))` — i.e. the candidate-side summand edges
are the `(shiftEdgePerm i)⁻¹`-images of A-1's base edges, a BIJECTIVE re-labelling of the existing
summands (no summand is dropped, split, or merged). This resolves Q1/Q2/Q3 of the de-risk: the
non-alignment of `ev j` with chain edges is a **non-issue**, because the block correspondence holds
for arbitrary edges and the downstream chain induction (LEAVES 1–4) groups summands by *filtering*
`ev j = cd.edge ⟨i⟩` and discards non-incident contributions via the degree-2 closure — it never
requires the summand edges to be aligned. The transport leaf
`chainData_candidateRow_edgeGrouped_transport` therefore decomposes into: (1) carry `hrv` via this
block correspondence under the `(shiftEdgePerm i).symm`-re-index of the edge family; (2) carry the
combination `hcomb` across the `(funLeft (shiftPerm i.castSucc).symm).dualMap` relabel (as
`chainData_bottom_relabel` carries genuine rows); (3) the chain `G`-links carry by `cd.link`
combinatorics. NO motive/IH/contract change.

This `i = 3`/single-edge de-risk anchors the verdict at the first honest case before any transport
leaf signature is pinned (the row-321 failure mode is a confident pin ahead of the de-risk). -/
theorem _root_.Graph.ChainData.i3_candidateBlock_transport_deRisk
    [DecidableEq α] [DecidableEq β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (i : Fin cd.d)
    {ends₀ : β → α × α} {q : α × Fin (k + 2) → ℝ}
    (f : β) {r : Module.Dual ℝ (ScrewSpace k)}
    -- A-1's base block membership at an ARBITRARY base edge `f` (the W6b producer's `hrv j`):
    (hbase : r ∈ (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i.castSucc))
        ends₀ q).toBodyHinge.hingeRowBlock f) :
    -- transports to the candidate framework's block at the `(shiftEdgePerm i)⁻¹`-image of `f`:
    r ∈ (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i.castSucc))
        (fun e => ((cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).1,
          (cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).2))
        (fun p => q (cd.shiftPerm i.castSucc p.1, p.2))).toBodyHinge.hingeRowBlock
          ((cd.shiftEdgePerm i).symm f) := by
  classical
  -- The candidate block at `g := σ⁻¹ f` equals the base block at `σ (σ⁻¹ f) = f` (support extensors
  -- coincide for ANY edge under the relabel; graph-independent).
  rw [BodyHingeFramework.hingeRowBlock,
    PanelHingeFramework.ofNormals_supportExtensor_relabel_perm (cd.shiftPerm i.castSucc)
      (cd.shiftEdgePerm i) ((cd.shiftEdgePerm i).symm f),
    Equiv.apply_symm_apply]
  -- Now the candidate block at `σ⁻¹ f` is literally the base block at `f` (the two base frameworks
  -- differ only in their irrelevant graph; `supportExtensor` reads only `ends₀`/`q`).
  simpa only [BodyHingeFramework.hingeRowBlock, PanelHingeFramework.toBodyHinge_supportExtensor,
    PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal] using hbase

/-- **T-1 — the candidate-level edge-grouped transport, block half** (CHAIN-2c-ii-arm, the de-risked
half of the row-352 GAP transport leaf `chainData_candidateRow_edgeGrouped_transport`;
`notes/Phase23-design.md` §(o‴)(I.8.10) sub-leaf T-1; KT 2011 §6.4.2 eqs. (6.59)/(6.62) the
index-shift panel correspondence; Phase 23b).

The all-`i`/`∀ j` lift of the single-edge de-risk anchor `i3_candidateBlock_transport_deRisk`: A-1's
edge-grouped base output (`exists_candidateRow_bottomRows_of_rigidOn`, `Candidate.lean`) carries a
family of per-summand block memberships `rvGv j ∈ (base).hingeRowBlock (evGv j)` over **arbitrary**
base links `evGv j`, but `chainData_freshEdge_perp_of_baseRedundancy`'s `hrv` (h3) wants them at the
**candidate** framework `Fva = ofNormals (G − vᵢ) endsσρ qρ`. This lemma transports each summand's
membership to the candidate block at the `(shiftEdgePerm i)⁻¹`-image of its base edge — a clean
BIJECTIVE re-index of the family (no summand dropped, split, or merged), per the de-risk verdict
(Q2-with-a-twist). The candidate-side edge family the perp leaf then consumes is
`evGv' j := (shiftEdgePerm i).symm (evGv j)`.

Each `j` is the anchor at `f := evGv j`; the proof is a per-summand replay. TRANSPORT, no new math:
no motive/IH/contract change, no genuinely-new-math fork. d=3 (`i = 2`) is the landed `M₃` swap
involution. -/
theorem _root_.Graph.ChainData.chainData_candidateRow_edgeGrouped_transport_blocks
    [DecidableEq α] [DecidableEq β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (i : Fin cd.d)
    {ends₀ : β → α × α} {q : α × Fin (k + 2) → ℝ}
    {m : ℕ} (evGv : Fin m → β) (rvGv : Fin m → Module.Dual ℝ (ScrewSpace k))
    -- A-1's edge-grouped base block memberships at arbitrary base links `evGv j` (the W6b
    -- producer's `hrv`, at the base framework `ofNormals (G − vᵢ) ends₀ q`):
    (hrv : ∀ j, rvGv j ∈ (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i.castSucc))
        ends₀ q).toBodyHinge.hingeRowBlock (evGv j)) :
    -- transport to the candidate framework's block at the `(shiftEdgePerm i)⁻¹`-re-indexed edges:
    ∀ j, rvGv j ∈ (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i.castSucc))
        (fun e => ((cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).1,
          (cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).2))
        (fun p => q (cd.shiftPerm i.castSucc p.1, p.2))).toBodyHinge.hingeRowBlock
          ((cd.shiftEdgePerm i).symm (evGv j)) :=
  fun j => cd.i3_candidateBlock_transport_deRisk i (evGv j) (hrv j)

/-- **T-2 — the candidate-level edge-grouped transport, combination half** (CHAIN-2c-ii-arm, the
`hcomb`-relabel half of the row-352 GAP transport leaf
`chainData_candidateRow_edgeGrouped_transport`; `notes/Phase23-design.md` §(o‴)(I.8.10) sub-leaf
T-2; KT 2011 §6.4.2 eqs.~(6.62)/(6.66) the index-shift row correspondence; Phase 23b).

Carries A-1's base combination identity
`hingeRow x y ρ = ∑ⱼ c j • hingeRow (uv j) (vv j) (rv j)`
(`exists_candidateRow_bottomRows_of_rigidOn`'s edge-grouped tail, `Candidate.lean`, over the base
endpoints `x y` of the fresh pair) across the relabel `(funLeft σ.symm).dualMap` (`σ = shiftPerm
i.castSucc`) to the candidate orientation
`hingeRow (σ.symm x) (σ.symm y) ρ = ∑ⱼ c j • hingeRow (σ.symm (uv j)) (σ.symm (vv j)) (rv j)`.

The relabel is a single linear map, so it distributes over the finite sum (`map_sum`) and the
scalar multiples (`map_smul`); each `hingeRow` summand transports endpoint-wise by
`hingeRow_funLeft_dualMap` (`(funLeft ρ).dualMap (hingeRow u v r) = hingeRow (ρ u) (ρ v) r`, no
involution on `ρ` needed). This is **exactly** the linearity step `chainData_bottom_relabel`
(`:1939`) performs on a single genuine row, lifted across the `∑ⱼ c j • ·`. The endpoint relabel
`uv' j := σ.symm (uv j)` makes the candidate combination's RHS match the `(shiftEdgePerm i)⁻¹`-re-
indexed links T-3 supplies. TRANSPORT, no new math: no motive/IH/contract change. d=3 (`i = 2`) is
the landed `M₃` single-swap involution. -/
theorem _root_.Graph.ChainData.chainData_candidateRow_edgeGrouped_transport_comb
    [DecidableEq α]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (i : Fin cd.d)
    {m : ℕ} (c : Fin m → ℝ) (uv vv : Fin m → α)
    (rv : Fin m → Module.Dual ℝ (ScrewSpace k))
    {x y : α} {ρ : Module.Dual ℝ (ScrewSpace k)}
    -- A-1's base combination identity (`exists_candidateRow_bottomRows_of_rigidOn`):
    (hcomb : BodyHingeFramework.hingeRow x y ρ
      = ∑ j, c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)) :
    -- the `(funLeft σ.symm).dualMap`-relabelled candidate-orientation combination:
    BodyHingeFramework.hingeRow ((cd.shiftPerm i.castSucc).symm x)
        ((cd.shiftPerm i.castSucc).symm y) ρ
      = ∑ j, c j • BodyHingeFramework.hingeRow ((cd.shiftPerm i.castSucc).symm (uv j))
          ((cd.shiftPerm i.castSucc).symm (vv j)) (rv j) := by
  -- Apply the linear relabel `(funLeft σ.symm).dualMap` to both sides of A-1's identity, then
  -- read each `hingeRow` summand endpoint-wise by `hingeRow_funLeft_dualMap`.
  have hmap := congrArg
    (LinearMap.funLeft ℝ (ScrewSpace k) (cd.shiftPerm i.castSucc).symm).dualMap hcomb
  rw [BodyHingeFramework.hingeRow_funLeft_dualMap, map_sum] at hmap
  simp only [map_smul, BodyHingeFramework.hingeRow_funLeft_dualMap] at hmap
  exact hmap

/-- **STEP 2 — the single-scalar per-edge perp transport, base → candidate** (CHAIN-2c-ii-arm, the
last un-landed piece of the `hρGv` perp slot; `notes/Phase23-design.md` §(o‴)(I.8.11) STEP 2/STEP
2′; KT 2011 §6.4.2 eqs.~(6.62)/(6.66) the index-shift panel correspondence; Phase 23b).

The route-settling recon (§(o‴)(I.8.11)) replaced the mis-targeted row-354 *family* transport
(`chainData_candidateRow_edgeGrouped_transport_{blocks,comb}`, now orphaned) with this single-scalar
transport: KT works entirely at the base `(G₁,q₁) = G − v₁`, and the only thing crossing to the
candidate-`i` framework is the *scalar* perpendicularity. The base perp at the `shiftEdgePerm`-image
of the candidate chain edge transports to the candidate framework's perp at that edge:

- `(candidate).supportExtensor (edge s) = (base).supportExtensor (shiftEdgePerm i (edge s))`
  (`ofNormals_supportExtensor_relabel_perm` — support extensors coincide under the `(ρ, σ)` relabel
  for *every* edge, with `(ρ, σ) = (shiftPerm i.castSucc, shiftEdgePerm i)`);
- `shiftEdgePerm i (edge s) = edge (s + 1)` for an interior step (`1 ≤ s`, `s + 1 < i`,
  `shiftEdgePerm_apply_edge_interior`) and `= e₀` for the head step `s = 0`
  (`shiftEdgePerm_apply_edge_zero`, the STEP 2′ branch — the splice-panel annihilation `hρe₀` A-1
  already supplies). The two branches merge under `if s = 0 then e₀ else edge (s + 1)`;
- `supportExtensor` reads only `ends`/`normal` (`ofNormals_ends`/`ofNormals_normal`), so the base
  perp's graph is irrelevant — it is taken at an arbitrary `Gb` and bridged to the candidate split
  graph `G − vᵢ` for free.

The candidate `ends`/`q` are the relabelled forms `(endsσρ, qρ)` of A-1's base `ends₀`/`q` (the same
forms `ofNormals_relabel_perm` / `chainData_bottom_relabel` produce); in the arm the base perp comes
from STEP 1 (`chainData_freshEdge_perp_of_baseRedundancy` at base index `⟨1⟩`, no transport) or
`hρe₀`, and this lemma feeds `chainData_freshEdge_slot_mem`'s `hperp s`. TRANSPORT, no new math: no
motive/IH/contract change, no new-math fork. d=3 (`i = 2`) is the landed `M₃` involution. -/
theorem _root_.Graph.ChainData.chainData_freshEdge_perp_transport_base_to_candidate
    [DecidableEq α] [DecidableEq β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (i : Fin cd.d) (hi : 1 ≤ (i : ℕ))
    (s : ℕ) (hs1i : s + 1 < (i : ℕ))
    {Gb : Graph α β} {ends₀ : β → α × α} {q : α × Fin (k + 2) → ℝ}
    {ρ₀ : Module.Dual ℝ (ScrewSpace k)}
    -- the base perp at the `shiftEdgePerm`-image of the candidate chain edge (STEP 1 / `hρe₀`):
    (hbase : ρ₀ ((PanelHingeFramework.ofNormals Gb ends₀ q).toBodyHinge.supportExtensor
        (if s = 0 then cd.e₀ else cd.edge ⟨s + 1, by have := i.isLt; omega⟩)) = 0) :
    -- transports to the candidate framework's perp at `edge s`:
    ρ₀ ((PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i.castSucc))
        (fun e => ((cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).1,
          (cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).2))
        (fun p => q (cd.shiftPerm i.castSucc p.1, p.2))).toBodyHinge.supportExtensor
          (cd.edge ⟨s, by have := i.isLt; omega⟩)) = 0 := by
  classical
  -- The candidate-framework support extensor at `edge s` equals the base framework's at
  -- `σ (edge s) = shiftEdgePerm i (edge s)` (graph-independent; the relabel coincidence lemma).
  rw [PanelHingeFramework.ofNormals_supportExtensor_relabel_perm (cd.shiftPerm i.castSucc)
    (cd.shiftEdgePerm i) (cd.edge ⟨s, by have := i.isLt; omega⟩)]
  -- Resolve `σ (edge s)`: `e₀` at the head (`s = 0`), `edge (s+1)` interior (`1 ≤ s`, `s+1 < i`).
  rcases Nat.eq_zero_or_pos s with hs0 | hs0
  · subst hs0
    rw [cd.shiftEdgePerm_apply_edge_zero i hi]
    -- Bridge the base graph `G − vᵢ` to `Gb`: `supportExtensor` reads only `ends₀`/`q`.
    simpa only [if_pos rfl, PanelHingeFramework.toBodyHinge_supportExtensor,
      PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal] using hbase
  · rw [cd.shiftEdgePerm_apply_edge_interior i hs0 hs1i]
    simpa only [if_neg (by omega : ¬ s = 0), PanelHingeFramework.toBodyHinge_supportExtensor,
      PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal] using hbase

/-- **STEP 1 ∘ STEP 2 — the per-edge perp the slot core consumes, from A-1's base data**
(CHAIN-2c-ii-arm, the `chainData_relabel_arm` `hperp` feed; `notes/Phase23-design.md`
§(o‴)(I.8.11) STEP 3; KT 2011 §6.4.2 eqs.~(6.62)/(6.66); Phase 23b). The composition the arm
assembly invokes once per surviving chain edge `s` (`s + 1 < i`): it produces the candidate-`i`
framework's perp `ρ₀ ⊥ Fva.supportExtensor (edge s)` — exactly `chainData_freshEdge_slot_mem`'s
`hperp s` shape — directly from the W6b base outputs (A-1,
`exists_candidateRow_bottomRows_of_rigidOn` at the base `(G₁, q₁) = G − v₁`), with no
candidate-framework redundancy hypothesis.

The two halves are the LANDED STEP 1 (`chainData_freshEdge_perp_of_baseRedundancy`, the
witness-free per-edge perp at the BASE) and STEP 2
(`chainData_freshEdge_perp_transport_base_to_candidate`, the single-scalar base → candidate
transport):
* for an **interior** surviving edge (`1 ≤ s`), STEP 1 at base index `⟨1⟩` (so its framework is the
  base `ofNormals (G − v₁) ends₀ q`) and edge index `t := s + 1` (`2 ≤ s + 1 < cd.d`) gives the BASE
  perp `ρ₀ ⊥ (base).supportExtensor (edge (s+1))`; STEP 2 (`Gb := G − v₁`) carries it to the
  candidate perp at `edge s`;
* for the **head** edge `s = 0`, the base perp at `e₀` is the splice-panel annihilation `hρe₀` A-1
  already supplies (`ρ₀ ⊥ (base).supportExtensor e₀`), and STEP 2′ carries it to `edge 0`.

The `if s = 0 then e₀ else edge (s+1)` of STEP 2's `hbase` slot merges the two branches. The base
edge-grouped redundancy (`hlink`/`hrv`/`hcomb`/`hdeg1`) is A-1's at the base framework
`ofNormals (G − v₁) ends₀ q` (NOT the candidate `endsσρ`/`qρ` — STEP 1 runs at the base, the
row-352/354 level mismatch's fix, §(o‴)(I.8.11)); the produced perp is at the candidate framework
`endsσρ`/`qρ`, exactly the slot core's `Fva`. TRANSPORT + the landed base leaf, no new math: no
motive/IH/contract change, no genuinely-new-math fork. d=3 (`i = 2`) is the landed `M₃` cycle. -/
theorem _root_.Graph.ChainData.chainData_freshEdge_slot_perp
    [DecidableEq α] [DecidableEq β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (h3 : 3 ≤ cd.d)
    (i : Fin cd.d) (hi : 1 ≤ (i : ℕ)) (s : ℕ) (hs1i : s + 1 < (i : ℕ))
    {ends₀ : β → α × α} {q : α × Fin (k + 2) → ℝ}
    {m : ℕ} (c : Fin m → ℝ) (ev : Fin m → β) (uv vv : Fin m → α)
    (rv : Fin m → Module.Dual ℝ (ScrewSpace k))
    {ρ₀ : Module.Dual ℝ (ScrewSpace k)}
    -- A-1's base edge-grouped redundancy, at the BASE framework `ofNormals (G − v₁) ends₀ q`:
    (hlink : ∀ j, G.IsLink (ev j) (uv j) (vv j))
    (hrv : ∀ j, rv j ∈ (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩))
      ends₀ q).toBodyHinge.hingeRowBlock (ev j))
    (hcomb : (∑ j, c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j))
      = BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ₀)
    (hdeg1 : ∀ j, (cd.vtx ⟨2, by omega⟩ = uv j ∨ cd.vtx ⟨2, by omega⟩ = vv j) →
      ev j = cd.edge ⟨2, by omega⟩)
    -- A-1's splice-panel annihilation `hρe₀` (the `s = 0` base perp at `e₀`):
    (hρe₀ : ρ₀ ((PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩))
      ends₀ q).toBodyHinge.supportExtensor cd.e₀) = 0) :
    ρ₀ ((PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i.castSucc))
        (fun e => ((cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).1,
          (cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).2))
        (fun p => q (cd.shiftPerm i.castSucc p.1, p.2))).toBodyHinge.supportExtensor
          (cd.edge ⟨s, by have := i.isLt; omega⟩)) = 0 := by
  -- STEP 2 carries the base perp at `if s = 0 then e₀ else edge (s+1)` to the candidate.
  refine cd.chainData_freshEdge_perp_transport_base_to_candidate i hi s hs1i
    (Gb := G.removeVertex (cd.vtx ⟨1, by omega⟩)) (ends₀ := ends₀) (q := q) ?_
  -- STEP 1 supplies the base perp: `e₀` at the head (`hρe₀`), `edge (s+1)` interior (`s ≥ 1`).
  rcases Nat.eq_zero_or_pos s with hs0 | hs0
  · subst hs0; rw [if_pos rfl]; exact hρe₀
  · rw [if_neg (by omega : ¬ s = 0)]
    -- STEP 1 (`chainData_freshEdge_perp_of_baseRedundancy`) at base index `⟨1⟩`, edge index `s+1`.
    exact cd.chainData_freshEdge_perp_of_baseRedundancy h3 ⟨1, by omega⟩ (s + 1) (by omega)
      (by have := i.isLt; omega) c ev uv vv rv hlink hrv hcomb hdeg1

/-- **The engine `hρGv` slot at the candidate framework, from A-1's base data** (CHAIN-2c-ii-arm,
the `chainData_relabel_arm` `hρGv` slot; `notes/Phase23-design.md` §(o‴)(I.8.11) STEP 3; KT 2011
§6.4.2 eqs.~(6.56)/(6.64)/(6.66); Phase 23b). The exact `hρGv` slot the arm closer feeds
`case_III_arm_realization` at an interior candidate `i` (`2 ≤ i ≤ d−1`): the fresh-edge candidate
row `hingeRow vᵢ₊₁ vᵢ₋₁ (−ρ₀)` (engine roles `a := vᵢ₊₁`, `b := vᵢ₋₁`, candidate functional `−ρ₀`,
the M₃ sign convention) reaches `span (ofNormals (G − vᵢ) endsσρ qρ).rigidityRows`, where
`qρ`/`endsσρ` are the inverse-cycle relabelled base seed/selector the engine's candidate framework
carries.

The composition (no new math, the arm's hardest slot pre-assembled): `hingeRow_swap` flips the
engine row to `hingeRow vᵢ₋₁ vᵢ₊₁ ρ₀`, which the LEAF-5 slot core `chainData_freshEdge_slot_mem`
produces in `span (ofNormals (G − vᵢ) endsσρ (shiftSeedAdv q (i−1))).rigidityRows`; the P3 seed
bridge `shiftSeedAdv_eq_funLeft_shiftPerm` identifies that fold seed with the engine seed `qρ`. The
slot core's two obligations are discharged from A-1's BASE edge-grouped redundancy (`hlink`/`hrv`/
`hcomb`/`hdeg1` at the base `G − v₁`) + the splice annihilation `hρe₀`: the base redundancy `hφ`
feeds the start fold directly, and every per-edge perp `hperp s` is the LANDED STEP 1∘STEP 2
composition `chainData_freshEdge_slot_perp` (one call per surviving edge `s + 1 < i`). The `d = 3`
`M₃` arm's `case hρGv` (`case_III_arm_realization_M3`, `Relabel.lean`) is the `i = 2` (`m = 1`)
single-summand special case — there the lone surviving row is the reproduced `e_b`-row off `hρe₀`,
which is exactly the `s = 0` branch here (zero-regression). Pure assembly over LANDED leaves; no
motive/IH/contract change, no genuinely-new-math fork. -/
theorem _root_.Graph.ChainData.chainData_relabel_arm_hρGv
    [DecidableEq α] [DecidableEq β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (h3 : 3 ≤ cd.d)
    (i : Fin cd.d) (h2i : 2 ≤ (i : ℕ))
    {ends₀ : β → α × α} {q : α × Fin (k + 2) → ℝ}
    {m : ℕ} (c : Fin m → ℝ) (ev : Fin m → β) (uv vv : Fin m → α)
    (rv : Fin m → Module.Dual ℝ (ScrewSpace k))
    {ρ₀ : Module.Dual ℝ (ScrewSpace k)}
    (hrec : ∀ f x y, G.IsLink f x y →
      (fun e => ((cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).1,
        (cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).2)) f = (x, y) ∨
      (fun e => ((cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).1,
        (cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).2)) f = (y, x))
    -- A-1's base edge-grouped redundancy, at the un-relabelled BASE framework
    -- `ofNormals (G − v₁) ends₀ q` (the STEP 1∘STEP 2 composition's base data):
    (hlink : ∀ j, G.IsLink (ev j) (uv j) (vv j))
    (hrv : ∀ j, rv j ∈ (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩))
      ends₀ q).toBodyHinge.hingeRowBlock (ev j))
    (hcomb : (∑ j, c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j))
      = BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ₀)
    (hdeg1 : ∀ j, (cd.vtx ⟨2, by omega⟩ = uv j ∨ cd.vtx ⟨2, by omega⟩ = vv j) →
      ev j = cd.edge ⟨2, by omega⟩)
    -- A-1's base redundancy as a span membership at the RELABELLED selector `endsσρ`, the fold's
    -- start framework `ofNormals (G − v₁) endsσρ q` the LEAF-5 slot core consumes:
    (hφ : BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ₀ ∈
      Submodule.span ℝ (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩))
        (fun e => ((cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).1,
          (cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).2))
        q).toBodyHinge.rigidityRows)
    -- A-1's splice-panel annihilation `hρe₀` (the `s = 0` base perp at `e₀`), at the un-relabelled
    -- base selector `ends₀` (the composition's STEP 2′ base data):
    (hρe₀ : ρ₀ ((PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩))
      ends₀ q).toBodyHinge.supportExtensor cd.e₀) = 0) :
    BodyHingeFramework.hingeRow (cd.vtx i.succ)
        (cd.vtx (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc) (-ρ₀)
      ∈ Submodule.span ℝ (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i.castSucc))
        (fun e => ((cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).1,
          (cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).2))
        (fun p => q (cd.shiftPerm i.castSucc p.1, p.2))).toBodyHinge.rigidityRows := by
  classical
  -- The relabelled candidate selector `endsσρ` and the engine candidate seed `qρ`.
  set endsσρ : β → α × α :=
    fun e => ((cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).1,
      (cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).2) with hendsσρ
  set qρ : α × Fin (k + 2) → ℝ := fun p => q (cd.shiftPerm i.castSucc p.1, p.2) with hqρ
  -- The `Fin (cd.d + 1)` form of the candidate index `i`.
  have hid : (i : ℕ) < cd.d := i.isLt
  -- `hingeRow_swap` flips the engine row to the slot-core orientation `hingeRow vᵢ₋₁ vᵢ₊₁ ρ₀`.
  rw [BodyHingeFramework.hingeRow_swap (cd.vtx i.succ)
    (cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc) (-ρ₀), neg_neg]
  -- P3: the engine seed `qρ` is the slot core's fold seed `shiftSeedAdv q (i−1)`.
  have hP3 : cd.shiftSeedAdv q ((i : ℕ) - 1) = qρ := by
    rw [hqρ]; exact cd.shiftSeedAdv_eq_funLeft_shiftPerm q i (by omega)
  -- Match the conclusion's vertex indices `vtx (i−1).castSucc`/`vtx i.succ` to the slot core's
  -- `vtx ⟨(i:ℕ)−1, _⟩`/`vtx ⟨(i:ℕ)+1, _⟩` shapes.
  have hidx1 : cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc
      = cd.vtx ⟨(i : ℕ) - 1, by omega⟩ :=
    congrArg cd.vtx (Fin.ext (by simp only [Fin.val_castSucc]))
  have hidx2 : cd.vtx i.succ = cd.vtx ⟨(i : ℕ) + 1, by omega⟩ :=
    congrArg cd.vtx (Fin.ext (by simp only [Fin.val_succ]))
  rw [hidx1, hidx2, ← hP3]
  -- LEAF-5 slot core: peel the slot row off the fold, the base redundancy `hφ` + per-edge perps.
  refine cd.chainData_freshEdge_slot_mem ⟨(i : ℕ), by omega⟩
    (show 1 ≤ (i : ℕ) by omega) (show (i : ℕ) < cd.d from hid) endsσρ q ?hrec ?hφ ?hperp
  case hrec => exact hrec
  case hφ =>
    -- the base redundancy `hingeRow (vtx 0)(vtx 2) ρ₀ ∈ span (G − v₁) rows` (A-1), with the start
    -- fold seed `shiftSeedAdv q 0` reduced to the base seed `q`.
    rw [cd.shiftSeedAdv_zero]; exact hφ
  case hperp =>
    -- each surviving chain-edge perp is the LANDED STEP 1∘STEP 2 composition.
    intro s hs
    rw [hP3]
    exact cd.chainData_freshEdge_slot_perp h3 i (by omega) s hs c ev uv vv rv
      hlink hrv hcomb hdeg1 hρe₀


end CombinatorialRigidity.Molecular
