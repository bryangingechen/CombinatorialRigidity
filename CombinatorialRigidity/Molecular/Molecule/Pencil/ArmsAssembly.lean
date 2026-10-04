/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.Arms

/-!
# The pencil reduction — the base arm (Phase 39 PENCIL)

Split out of `Molecule/Pencil/Arms.lean` (`40-cleanup` task 28b, the `≤1500`-LoC tripwire): the
**base arm** `L5` of the W3 leaf decomposition's four induction arms
(`hasPencilRealization_of_ncard_le_two`), the last non-wrapper leaf, discharging every loopless
multigraph on at most two bodies. The bare-motive wrapper `L7` this file also carried,
`pencil_conjecture_of_arms`, retired at the `40-simplify` cleanup round's PI sanction (2026-10-04,
`notes/pencil/adjudications.md`): its conclusion follows from the headline `pencil_conjecture`
over an infinite field, with no caller left once `pencil_conjecture_of_arms_pair` and
`pencil_conjecture_of_X0` superseded it.

This split is rename-free — every declaration keeps its `CombinatorialRigidity.Molecular`
namespace, so the blueprint `\lean{...}` pins and `checkdecls` are unaffected.

See `notes/Phase39.md`, `notes/Phase39-design.md` (§W3 leaf decomposition), and
`blueprint/src/chapter/pencil.tex`.
-/

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K]
variable {α β : Type*}

/-! ## W3-L5: the base arm (`lem:pencil-base-case`, Phase 39)

The last non-wrapper W3 leaf: every loopless multigraph on at most two bodies has a pencil
realization at the deficiency rank. Three shapes, dispatched on `E(G)`, sharing one pencil pair
`(q₀, Ce, Cf)` from `exists_linearIndependent_extensor_pair_through_point` at a fixed normal `n₀`:
- **edgeless** (covers both `|V| = 1` and `|V| = 2` with no edges): rank `0` against
  `def = D(|V|-1)` (`Graph.deficiency_of_edgeSet_empty`), realized by the all-`Ce` framework (no
  per-link obligation to discharge).
- **single edge**: rank `D - 1` against `def = 1` (`Graph.deficiency_of_single_edge`), realized by
  one genuine hinge — the lower bound is the landed `D - 1`-independent-rows brick
  (`exists_independent_rigidityRows_of_edge`), the upper bound the B2 deficiency cap
  (`finrank_span_rigidityRows_add_deficiency_le`).
- **parallel class of `m ≥ 2` edges** (no minimality assumed, so `m` is unbounded): rank `D`
  against `def = 0`, via the landed two-hinge producer `theorem_55_base` (which needs only two
  genuine parallel hinges `e ≠ f`, not `E(G) = {e, f}` exactly) — any further edges reuse the
  second hinge `Cf` and cost nothing (mirrors the loop arm's extension pattern,
  `hasPencilRealization_of_isLoopAt`). The deficiency-`0` fact is the restriction argument
  `isKDof_zero_of_parallel_pair` on `H := G ↾ {e, f}` transported to `G` by
  `deficiency_le_deficiency_of_le_vertexSet_eq` (mirrors
  `edgeSet_ncard_le_two_of_isMinimalKDof_of_ncard_two`). -/
theorem hasPencilRealization_of_ncard_le_two [Finite α] [Finite β] {G : Graph α β}
    (hloop : G.Loopless) (hne : V(G).Nonempty) (hV2 : V(G).ncard ≤ 2) :
    HasPencilRealization K 3 G := by
  classical
  have := hloop
  have hb6 : Graph.bodyBarDim 3 = screwDim 2 := Graph.bodyBarDim_eq_screwDim_sub_one (by norm_num)
  -- A fixed nonzero panel normal, and the pencil pair (independent hinges through a common point)
  -- reused across the single-edge and parallel-class cases.
  set n₀ : Fin 4 → K := Pi.single 0 1 with hn₀
  have hn₀_ne : n₀ ≠ 0 := by
    intro h; have := congr_fun h 0; simp [hn₀, Pi.single_eq_same] at this
  obtain ⟨q₀, Ce, Cf, hq₀_ne, hq₀_perp, hCe_in, hCf_in, hCe_thru, hCf_thru, hCEF_li⟩ :=
    exists_linearIndependent_extensor_pair_through_point (K := K) n₀
  have hCe_ne : Ce ≠ 0 := by simpa using hCEF_li.ne_zero 0
  have hCf_ne : Cf ≠ 0 := by simpa using hCEF_li.ne_zero 1
  by_cases hE : E(G) = ∅
  · -- Edgeless: rank `0` against `def = D(|V|-1)`, for either `|V| = 1` or `|V| = 2`.
    set F : BodyHingeFramework K 2 α β := { graph := G, supportExtensor := fun _ => Ce } with hF
    have hFg : F.graph = G := rfl
    have hnoLink : ∀ e u v, ¬ G.IsLink e u v := fun e u v hlink => by
      have hmem : e ∈ E(G) := hlink.edge_mem; rw [hE] at hmem; exact hmem
    have hrows : F.rigidityRows = ∅ := by
      ext φ; simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨e, u, v, hlink, -⟩; exact hnoLink e u v (hFg ▸ hlink)
    have hfinrank : Module.finrank K (Submodule.span K F.rigidityRows) = 0 := by
      rw [hrows, Submodule.span_empty, finrank_bot]
    refine ⟨F, fun _ => n₀, fun _ => q₀, ⟨⟨hFg, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
    · exact fun v _ => hn₀_ne
    · exact fun _ => hCe_ne
    · exact fun e u v hlink => absurd hlink (hnoLink e u v)
    · exact fun v _ => hq₀_ne
    · exact fun v _ => hq₀_perp
    · exact fun e u v hlink => absurd hlink (hnoLink e u v)
    · rw [hfinrank, Graph.deficiency_of_edgeSet_empty hE, hb6]
      push_cast; ring
  · -- Nonempty edges force `|V(G)| = 2` (a single vertex would be loop-free ⟹ edgeless).
    have hE' : E(G).Nonempty := Set.nonempty_iff_ne_empty.mpr hE
    have hVpos : 0 < V(G).ncard := hne.ncard_pos
    have hV2eq : V(G).ncard = 2 := by
      rcases (show V(G).ncard = 1 ∨ V(G).ncard = 2 by omega) with hV1 | hV2eq'
      · exfalso
        obtain ⟨v₀, hv₀⟩ := Set.ncard_eq_one.mp hV1
        obtain ⟨e, he⟩ := hE'
        obtain ⟨p, q, hlink⟩ := G.exists_isLink_of_mem_edgeSet he
        have hpv : p ∈ V(G) := hlink.left_mem
        have hqv : q ∈ V(G) := hlink.right_mem
        rw [hv₀, Set.mem_singleton_iff] at hpv hqv
        rw [hpv, hqv] at hlink
        exact G.not_isLoopAt e v₀ hlink
      · exact hV2eq'
    obtain ⟨x, y, hxy, hVG⟩ := Set.ncard_eq_two.mp hV2eq
    have hlinks : ∀ f, f ∈ E(G) → G.IsLink f x y := by
      intro f hf
      obtain ⟨p, q, hlink⟩ := G.exists_isLink_of_mem_edgeSet hf
      have hpV : p ∈ V(G) := hlink.left_mem
      have hqV : q ∈ V(G) := hlink.right_mem
      rw [hVG] at hpV hqV
      rcases Set.mem_insert_iff.mp hpV with rfl | rfl <;>
      rcases Set.mem_insert_iff.mp hqV with rfl | rfl
      · exact absurd rfl hlink.ne
      · exact hlink
      · exact hlink.symm
      · exact absurd rfl hlink.ne
    rcases (show E(G).ncard = 1 ∨ 2 ≤ E(G).ncard by have := hE'.ncard_pos; omega) with hE1 | hge2
    · -- Single edge: rank `D - 1 = 5` against `def = 1`.
      obtain ⟨e, hEe⟩ := Set.ncard_eq_one.mp hE1
      have heE : e ∈ E(G) := by rw [hEe]; exact Set.mem_singleton e
      have hl_e : G.IsLink e x y := hlinks e heE
      set F : BodyHingeFramework K 2 α β :=
        { graph := G, supportExtensor := fun e' => if e' = e then Ce else Cf } with hF
      have hFg : F.graph = G := rfl
      have hFe : F.supportExtensor e = Ce := by simp [hF]
      have hlink_eq_e : ∀ e' u v, G.IsLink e' u v → e' = e := by
        intro e' u v he'
        have hmem : e' ∈ E(G) := he'.edge_mem
        rw [hEe] at hmem; exact hmem
      have hsupp_nz : ∀ e', F.supportExtensor e' ≠ 0 := by
        intro e'; simp only [hF]; split
        · exact hCe_ne
        · exact hCf_ne
      have hC : ∀ e' u v, G.IsLink e' u v → F.supportExtensor e' ≠ 0 :=
        fun e' _ _ _ => hsupp_nz e'
      refine ⟨F, fun _ => n₀, fun _ => q₀, ⟨⟨hFg, ?_, hsupp_nz, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
      · exact fun v _ => hn₀_ne
      · intro e' u v hlink
        have he'e := hlink_eq_e e' u v hlink; subst he'e
        rw [hFe]; exact ⟨hCe_in, hCe_in⟩
      · exact fun v _ => hq₀_ne
      · exact fun v _ => hq₀_perp
      · intro e' u v hlink
        have he'e := hlink_eq_e e' u v hlink; subst he'e
        rw [hFe]; exact ⟨hCe_thru, hCe_thru⟩
      · -- rank: sandwiched between the B2 upper bound and the `D-1`-independent-rows lower bound.
        have hdef : G.deficiency 3 = 1 :=
          Graph.deficiency_of_single_edge (n := 3) (by decide) hxy hl_e hVG hEe
        have hub := F.finrank_span_rigidityRows_add_deficiency_le (n := 3) hb6 hne hC
        rw [hFg] at hub
        obtain ⟨r, hr_li, hr_mem⟩ :=
          F.exists_independent_rigidityRows_of_edge (u := x) (v := y) hxy hl_e (hFe ▸ hCe_ne)
        have hspan_le : Submodule.span K (Set.range r) ≤ Submodule.span K F.rigidityRows :=
          Submodule.span_mono (Set.range_subset_iff.mpr hr_mem)
        have hcard : Module.finrank K (Submodule.span K (Set.range r)) = 5 := by
          rw [finrank_span_eq_card hr_li, Fintype.card_fin]; decide
        have hmono : 5 ≤ Module.finrank K (Submodule.span K F.rigidityRows) := by
          have hm := Submodule.finrank_mono hspan_le; rwa [hcard] at hm
        have hscrew_nat : screwDim 2 = 6 := by decide
        have htarget : screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency 3 = 5 := by
          rw [hV2eq, hdef, hscrew_nat]; norm_num
        rw [htarget] at hub ⊢
        exact le_antisymm hub (by exact_mod_cast hmono)
    · -- Parallel class of `m ≥ 2` edges: rank `D = 6` against `def = 0`.
      obtain ⟨t, htE, ht2⟩ := Set.exists_subset_card_eq (s := E(G)) (n := 2) hge2
      obtain ⟨e, f, hef, hteq⟩ := Set.ncard_eq_two.mp ht2
      have heE : e ∈ E(G) := htE (hteq ▸ Set.mem_insert e {f})
      have hfE : f ∈ E(G) := htE (hteq ▸ Set.mem_insert_of_mem e (Set.mem_singleton f))
      have hl_e : G.IsLink e x y := hlinks e heE
      have hl_f : G.IsLink f x y := hlinks f hfE
      set F : BodyHingeFramework K 2 α β :=
        { graph := G, supportExtensor := fun e' => if e' = e then Ce else Cf } with hF
      have hFg : F.graph = G := rfl
      have hFe : F.supportExtensor e = Ce := by simp [hF]
      have hFf : F.supportExtensor f = Cf := by simp [hF, hef.symm]
      refine ⟨F, fun _ => n₀, fun _ => q₀, ⟨⟨hFg, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
      · exact fun v _ => hn₀_ne
      · intro e'
        simp only [hF]; split
        · exact hCe_ne
        · exact hCf_ne
      · intro e' u v hlink
        by_cases he' : e' = e
        · subst he'; rw [hFe]; exact ⟨hCe_in, hCe_in⟩
        · have hFe' : F.supportExtensor e' = Cf := by simp [hF, he']
          rw [hFe']; exact ⟨hCf_in, hCf_in⟩
      · exact fun v _ => hq₀_ne
      · exact fun v _ => hq₀_perp
      · intro e' u v hlink
        by_cases he' : e' = e
        · subst he'; rw [hFe]; exact ⟨hCe_thru, hCe_thru⟩
        · have hFe' : F.supportExtensor e' = Cf := by simp [hF, he']
          rw [hFe']; exact ⟨hCf_thru, hCf_thru⟩
      · -- rank: full `D = 6` via `theorem_55_base` + bridge B1.
        have hdef0 : G.deficiency 3 = 0 := by
          set H := G ↾ ({e, f} : Set β) with hH_def
          have hHle : H ≤ G := Graph.restrict_le
          have hHl_e : H.IsLink e x y := by
            rw [hH_def, Graph.restrict_isLink]; exact ⟨Set.mem_insert e _, hl_e⟩
          have hHl_f : H.IsLink f x y := by
            rw [hH_def, Graph.restrict_isLink]; exact ⟨Set.mem_insert_of_mem _ rfl, hl_f⟩
          have hVH : V(H) = {x, y} := by rw [hH_def, Graph.vertexSet_restrict, hVG]
          have hEH : E(H) = {e, f} := by
            rw [hH_def, Graph.edgeSet_restrict]
            exact Set.inter_eq_right.mpr
              (Set.insert_subset_iff.mpr ⟨heE, Set.singleton_subset_iff.mpr hfE⟩)
          have hH0 : H.IsKDof 3 0 :=
            Graph.isKDof_zero_of_parallel_pair (n := 3) (by decide) hxy hHl_e hHl_f hef hVH hEH
          have hVHeq : V(H) = V(G) := by rw [hVH, hVG]
          have hdle :=
            Graph.deficiency_le_deficiency_of_le_vertexSet_eq (n := 3) (by decide) hHle hVHeq
          have hdnn := G.deficiency_nonneg 3 hne
          have hH0' : H.deficiency 3 = 0 := hH0.deficiency_eq
          omega
        have hgen : LinearIndependent K ![F.supportExtensor e, F.supportExtensor f] := by
          rw [hFe, hFf]; exact hCEF_li
        have hrig : F.IsInfinitesimallyRigidOn {x, y} := F.theorem_55_base hxy hgen hl_e hl_f
        have hrigV : F.IsInfinitesimallyRigidOn F.graph.vertexSet := by
          rw [hFg, hVG]; exact hrig
        have hB1 :=
          (F.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows hne).mp hrigV
        rw [hFg] at hB1
        have hscrew_nat : screwDim 2 = 6 := by decide
        rw [hV2eq, hscrew_nat] at hB1
        norm_num at hB1
        have htarget : screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency 3 = 6 := by
          rw [hV2eq, hdef0, hscrew_nat]; norm_num
        rw [htarget]
        exact_mod_cast hB1

end CombinatorialRigidity.Molecular
