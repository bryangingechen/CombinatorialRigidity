/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Induction.ReducibleVertex
import CombinatorialRigidity.Molecular.Molecule.Pencil.Habitat
import CombinatorialRigidity.Molecular.Molecule.Pencil.Steer
import CombinatorialRigidity.Molecular.Molecule.Pencil.Base
import CombinatorialRigidity.Molecular.Molecule.Pencil.Pair2

/-!
# W5-L7a — the safe-split IH generic half (Phase 39 PENCIL)

The split arm of the pencil induction (`hsplit` of `pencil_conjecture_of_arms_pair`,
`Pencil/Pair2.lean:1229`) must, given a safe degree-`2` split vertex `v` (`hsafe`, at least one of
its two neighbours `a`, `b` not a pencil hub), extend the induction hypothesis's `PencilPair` on the
split-off graph `G′ = G.splitOff v a b e₀` into the *generic* half `HasGenericPencilRealization K 3
G′` needed to feed the rank-extension assembly (W5-L7b, `notes/Phase39-design.md` §"W5-L7 research
recon" "Lean decomposition"). This file lands exactly that step, chaining the landed W5-L6 leaves:

* `PencilNondegFeasible K G` (the `PencilPair` generic-conjunct antecedent) supplies
  `∀ w, (G.closedHubNbhd w).ncard ≤ 3` (`ncard_closedHubNbhd_le_three_of_isNondegPencilRealization`,
  `Motive.lean`);
* the safe split transfers this bound to `G′`
  (`ncard_closedHubNbhd_splitOff_le_three_of_safe`, L6a-transfer, `Habitat.lean`);
* in parallel, `G′` is triangle-free
  (`Graph.splitOff_triangleFree_of_noRigid`, L6d, `Habitat.lean`);
* together these give `PencilNondegFeasible K G′`
  (`pencilNondegFeasible_of_ncard_closedHubNbhd_le_three_of_triangleFree`, L6b, `Steer.lean`);
* `G′.Simple` (`Graph.splitOff_simple_of_noRigid_of_card`, L6c, `Induction/Operations.lean`) lets
  the IH's generic conjunct fire on `G′`.

Purely combinatorial glue — no new mathematics; this leaf does *not* touch kernel (K) (the escape
`≢0` obligation) or the safe-vertex-existence dispatch (L6a-safe-exists, whose rigid `k = 0` half
stays a bounded `have`-hypothesis carried elsewhere).

This file also lands the companion **W5-L7b** — the rank-to-generic steering assembly
`hasGenericPencilRealization_of_independent_pencilRow_target` (re-pinned 2026-07-30, after the
`escapePoly` build BLOCKED; `notes/Phase39-design.md` §"W5-L7 research recon" "Lean decomposition";
signature corrected 2026-07-30 to `[Inhabited α]`, catching a statement-level `G.endsOf` gap the
route recon's drop to `[Nonempty α]` missed — see that section), which turns kernel (K)'s carried
rank-increment consequence (`hEsc`: a correct hub-selector, a seed, and a deficiency-target-size
`pencilRow` subfamily independent at that seed) — together with `≤ 3` closed hub-neighbourhoods and
triangle-freeness — into a generic pencil realization of the *un-split* `G` at the deficiency-rank
target. Split-data-free (no `v`/`a`/`b`/`e₀`); the L7c hsplit assembly composes L7a's output
through (K)'s discharge into this leaf's `hEsc` (below).

This file also lands **W5-L7c-5** — `pencilPair_of_splitOff_of_habitat`, the `5 ≤ |V|` hsplit
producer (`notes/Phase39-design.md` §"W5-L7 research recon" "L7c decomposition"): given the
split-arm habitat, kernel (K)'s carried `hK` implication, kernel (K-bare)'s carried `hbareSplit`
implication, and the induction hypothesis on strictly smaller graphs, produces `PencilPair K 3 G`.
The two carried kernels partition cleanly by `PencilNondegFeasible K G`: feasible chains L7a's
`G′`-generic output through `hK` into L7b; infeasible discharges the bare half directly via
`hbareSplit` fed the IH's `G′`-bare half.

This file finally lands **W5-L7c-6** — `pencil_conjecture_of_hcontract_hK_hbareSplit`, the
successor wrapper closing `hsplit` in full (`notes/Phase39-design.md` §"W5-L7 research recon" "L7c
decomposition"). It builds the `hsplit` hypothesis `pencil_conjecture_of_arms_pair`
(`Pair2.lean`) still takes by dispatching on `V(G).ncard`: `= 3`/`= 4` go to the direct-witness
base leaves `pencilPair_of_habitat_ncard_eq_three`/`_four` (`Base.lean`), and `5 ≤ V(G).ncard`
goes to this file's own `pencilPair_of_splitOff_of_habitat`, fed a fresh edge from the caller's
`∀`-form supply `hfresh`. The result carries exactly `hcontract` (unchanged, W4's obligation),
the two open kernels `hK`/`hbareSplit` ((K)/(K-bare), both user-adjudicated to be carried this
session), and `hfresh` (a mechanical S1 bookkeeping item, still open) — every other hypothesis of
the pencil reduction is now internal.

See `notes/Phase39.md`, `notes/Phase39-design.md` (§"W5-L7 research recon"), and
`blueprint/src/chapter/pencil.tex`.
-/

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K]
variable {α β : Type*}

/-! ## W5-L7a: the safe-split IH generic half (Phase 39 PENCIL) -/

/-- **W5-L7a — the safe-split IH generic half** (Phase 39 PENCIL; `notes/Phase39-design.md`
§"W5-L7 research recon" "Lean decomposition"). Given the split-arm hypotheses at a **safe**
degree-`2` vertex `v` — its two named neighbours `a`, `b` linked by distinct edges `eₐ ≠ e_b`, at
least one of them not a pencil hub (`hsafe`) — together with `G.Simple`, `G`'s own nondegeneracy
feasibility, and the induction hypothesis on strictly smaller graphs, produces a *generic* pencil
realization of the split-off graph `G′ = G.splitOff v a b e₀`. Chains the landed W5-L6 leaves
verbatim (see the file docstring); purely combinatorial glue, no new mathematics. -/
theorem hasGenericPencilRealization_of_splitOff_of_safe
    [Nonempty α] [Finite α] [Finite β] [Infinite K] {G : Graph α β} [G.Simple]
    {v a b : α} {eₐ e_b e₀ : β}
    (hV : 5 ≤ V(G).ncard)
    (hnoRigid : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G 3)
    (hdeg : G.degree v = 2)
    (heab : eₐ ≠ e_b) (hG_ea : G.IsLink eₐ v a) (hG_eb : G.IsLink e_b v b)
    (hsafe : ¬ G.PencilHub a ∨ ¬ G.PencilHub b)
    (hfeas : PencilNondegFeasible K G)
    (hIH : ∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard → PencilPair K 3 G') :
    HasGenericPencilRealization K 3 (G.splitOff v a b e₀) := by
  classical
  haveI : Inhabited α := Classical.inhabited_of_nonempty inferInstance
  have hab : a ≠ b := fun h => heab (Graph.Simple.eq_of_isLink hG_ea (h ▸ hG_eb))
  have hexa : ∃ eₐ, G.IsLink eₐ v a := ⟨eₐ, hG_ea⟩
  have hexb : ∃ e_b, G.IsLink e_b v b := ⟨e_b, hG_eb⟩
  have hD6 : (6 : ℕ) ≤ Graph.bodyBarDim 3 := Graph.six_le_bodyBarDim (by norm_num)
  obtain ⟨F, normal, point, hnd⟩ := hfeas
  -- `∀ w, (G.closedHubNbhd w).ncard ≤ 3`: at `w ∈ V(G)` from the nondeg witness; off `V(G)` the
  -- closed hub-neighbourhood is empty (both membership disjuncts force `w ∈ V(G)`).
  have hcard : ∀ w, (G.closedHubNbhd w).ncard ≤ 3 := by
    intro w
    by_cases hw : w ∈ V(G)
    · exact ncard_closedHubNbhd_le_three_of_isNondegPencilRealization hnd hw
    · have hempty : G.closedHubNbhd w = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro x ⟨hxhub, rfl | ⟨e, hlink⟩⟩
        · exact hw hxhub.1
        · exact hw hlink.left_mem
      rw [hempty]; simp
  have hcard' : ∀ w, ((G.splitOff v a b e₀).closedHubNbhd w).ncard ≤ 3 :=
    ncard_closedHubNbhd_splitOff_le_three_of_safe hab hexa hexb hsafe hcard
  have htf' : ∀ e₁ e₂ e₃ x y z, x ≠ y → y ≠ z → x ≠ z →
      (G.splitOff v a b e₀).IsLink e₁ x y → (G.splitOff v a b e₀).IsLink e₂ y z →
      (G.splitOff v a b e₀).IsLink e₃ z x → False :=
    Graph.splitOff_triangleFree_of_noRigid (by omega) hV hnoRigid hdeg hexa hexb hab
  haveI hG'simple : (G.splitOff v a b e₀).Simple :=
    Graph.splitOff_simple_of_noRigid_of_card (by omega) heab hG_ea hG_eb (by omega) hnoRigid
  have hG'feas : PencilNondegFeasible K (G.splitOff v a b e₀) :=
    pencilNondegFeasible_of_ncard_closedHubNbhd_le_three_of_triangleFree hcard' htf'
  have hV'lt : V(G.splitOff v a b e₀).ncard < V(G).ncard :=
    Graph.splitOff_vertexSet_ncard_lt hG_ea.left_mem
  have hV'ne : V(G.splitOff v a b e₀).Nonempty := by
    refine ⟨a, ?_⟩
    rw [Graph.vertexSet_splitOff]
    exact Set.mem_diff_singleton.mpr ⟨hG_ea.right_mem, hG_ea.ne.symm⟩
  exact (hIH _ hV'ne hV'lt).1 hG'simple hG'feas

/-! ## W5-L7b: the rank-to-generic steering assembly (Phase 39 PENCIL)

The companion assembly discharging kernel (K)'s carried rank-increment consequence into a generic
pencil realization of the *un-split* graph `G` itself (`notes/Phase39-design.md` §"W5-L7 research
recon" "Lean decomposition", the L7b re-pin after the `escapePoly` build BLOCKED). Split-data-free:
given `G` simple, nonempty, `≤ 3` closed hub-neighbourhoods (`hcard`), triangle-free (`htf`), and an
∃-witnessed correct hub-selector `hubSel` together with a seed `q` and an edge-indexed set `s` of
size the deficiency target on which the `pencilRow` subfamily is linearly independent (`hEsc` — the
carried form of kernel (K)'s rank-increment consequence, `hK` in the L7c hsplit assembly),
produces a generic pencil realization of `G` at that same target rank.

**Signature correction (2026-07-30, this commit):** the route recon's pin used `[Nonempty α]`, but
`hEsc`'s own *type* — not just its proof — reads `G.endsOf` (`pencilRow hubSel G.endsOf q i`), and
`Graph.endsOf` (`Induction/Operations.lean`) needs `[Inhabited α]` for its off-`E(G)` junk value;
`Nonempty → Inhabited` is deliberately not a registered instance in this project (every other landed
leaf derives it locally via `Classical.inhabited_of_nonempty` *inside* a tactic proof, which cannot
reach a statement-level occurrence). Fixed by taking `[Inhabited α]` directly (subsuming
`[Nonempty α]` for existence purposes; the proof body needs nothing else from it). The `hK` pin
(design doc, same section) has the identical `pencilRow … G.endsOf …` shape in its conclusion and
needs the same correction — flagged there for the L7c builder.

Route (`notes/Phase39-design.md`, same section): the two "satisfiable-somewhere" chart-point
families the L6b-i assembly (`Steer.lean`) also needs — one per body
(`exists_coord_linearIndepOn_pencilChartPoint_perBody`), one per adjacent pair
(`…_adjacentPair`) — convert to seed-polynomials
(`exists_polynomial_ne_zero_of_linearIndependent_pencilChartPoint`) and steer to one common seed
*alongside* `hEsc`'s own `pencilRow` independence via the engine's product-route workhorse
(`exists_common_seed_pencilRow_and_polynomials`, `Engine.lean:476`); reconstruct the standing
`PencilChartWF` conjuncts at the common seed (the L6b-i body, `Steer.lean:1271`), re-choose
`fillNbr` (`exists_fillNbr_pencilChartWF_of_standing`), read off the realization
(`isNondegPencilRealization_pencilChartFramework_of_pencilChartWF`), and pinch the rank at the
common seed, transported to the `fillNbr`-re-chosen seed by `pencilChartFramework_congr` (the
v-f-6 rank thread, `Steer.lean:693ff`, with `G` in place of `G.induce V₁` and no re-seed step —
`hEsc` already supplies the seed directly, unlike v-f-6 there is no `IsNondegPencilRealization`
witness to re-seed from). No new mathematics; every call is a landed pattern. -/

/-- **W5-L7b — the rank-to-generic steering assembly** (Phase 39 PENCIL; `notes/Phase39-design.md`
§"W5-L7 research recon" "Lean decomposition", the re-pinned L7b, `[Inhabited α]`-corrected). From
`G.Simple`, `V(G)` nonempty, `≤ 3` closed hub-neighbourhoods, triangle-freeness, and kernel (K)'s
carried rank-increment consequence `hEsc` (a correct hub-selector, a seed, and a
deficiency-target-size `pencilRow` subfamily independent at that seed, indexed by genuine edges),
produces a generic pencil realization of `G` at the deficiency-rank target. See the file docstring
for the route and the signature correction. -/
theorem hasGenericPencilRealization_of_independent_pencilRow_target
    [Inhabited α] [Finite α] [Finite β] [Infinite K] {G : Graph α β} [G.Simple]
    (hGne : V(G).Nonempty)
    (hcard : ∀ v, (G.closedHubNbhd v).ncard ≤ 3)
    (htf : ∀ e₁ e₂ e₃ x y z, x ≠ y → y ≠ z → x ≠ z →
      G.IsLink e₁ x y → G.IsLink e₂ y z → G.IsLink e₃ z x → False)
    (hEsc : ∃ (hubSel : α → Fin 3 → Option α) (q : α × Fin 4 × Fin 4 → K)
        (s : Set (β × Set.powersetCard (Fin 4) 2 × Set.powersetCard (Fin 4) 2)),
      (∀ w, IsFin3SelectorOf (G.closedHubNbhd w) (hubSel w)) ∧
      (∀ i ∈ s, (i : β × _ × _).1 ∈ E(G)) ∧
      ((Nat.card s : ℤ) = screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency 3) ∧
      LinearIndependent K (fun i : s => pencilRow hubSel G.endsOf q (i : β × _ × _))) :
    HasGenericPencilRealization K 3 G := by
  classical
  haveI : G.Loopless := ‹G.Simple›.toLoopless
  obtain ⟨hubSel, q₀, s, hHubSel, hslink, hscard, hsLI⟩ := hEsc
  -- Global non-hub neighbour selectors (needed for the fourth `PencilChartWF` conjunct).
  have hnbr : ∀ v, ∃ sel : Fin 3 → Option α,
      ¬ G.PencilHub v → IsFin3SelectorOf (G.closedNbhd v) sel := by
    intro v
    by_cases hv : G.PencilHub v
    · exact ⟨fun _ => none, fun h => absurd hv h⟩
    · obtain ⟨sel, hsel⟩ :=
        exists_isFin3SelectorOf_of_ncard_le_three (Set.toFinite _)
          (ncard_closedNbhd_le_three_of_not_pencilHub hv)
      exact ⟨sel, fun _ => hsel⟩
  choose nbrSel hNbrSel using hnbr
  -- The per-body / adjacent-pair satisfiable-somewhere point conditions, as polynomials.
  have hpolyA : ∀ v : α, ∃ Q : MvPolynomial (α × Fin 4 × Fin 4) K,
      (∃ q, MvPolynomial.eval q Q ≠ 0) ∧
      (∀ q, MvPolynomial.eval q Q ≠ 0 →
        LinearIndepOn K (pencilChartPoint (PencilSeed.ofCoord q) hubSel)
          (if G.PencilHub v then ({v} : Set α) else G.closedNbhd v)) := by
    intro v
    obtain ⟨q, hq⟩ : ∃ q : α × Fin 4 × Fin 4 → K,
        LinearIndepOn K (pencilChartPoint (PencilSeed.ofCoord q) hubSel)
          (if G.PencilHub v then ({v} : Set α) else G.closedNbhd v) :=
      exists_coord_linearIndepOn_pencilChartPoint_perBody hcard htf hubSel hHubSel v
    obtain ⟨Q, hQ0, hQ⟩ :=
      exists_polynomial_ne_zero_of_linearIndependent_pencilChartPoint hubSel id hq
    exact ⟨Q, ⟨q, hQ0⟩, fun q' hq' => hQ q' hq'⟩
  choose PA hPA0 hPA using hpolyA
  have hpolyB : ∀ p : α × α, ∃ Q : MvPolynomial (α × Fin 4 × Fin 4) K,
      (∃ q, MvPolynomial.eval q Q ≠ 0) ∧
      (∀ q, MvPolynomial.eval q Q ≠ 0 →
        LinearIndepOn K (pencilChartPoint (PencilSeed.ofCoord q) hubSel)
          (if G.Adj p.1 p.2 then ({p.1, p.2} : Set α) else ∅)) := by
    intro p
    obtain ⟨q, hq⟩ : ∃ q : α × Fin 4 × Fin 4 → K,
        LinearIndepOn K (pencilChartPoint (PencilSeed.ofCoord q) hubSel)
          (if G.Adj p.1 p.2 then ({p.1, p.2} : Set α) else ∅) :=
      exists_coord_linearIndepOn_pencilChartPoint_adjacentPair hcard htf hubSel hHubSel p
    obtain ⟨Q, hQ0, hQ⟩ :=
      exists_polynomial_ne_zero_of_linearIndependent_pencilChartPoint hubSel id hq
    exact ⟨Q, ⟨q, hQ0⟩, fun q' hq' => hQ q' hq'⟩
  choose PB hPB0 hPB using hpolyB
  -- One common seed for the rank rows (`hEsc`'s own) and the point conditions.
  have hPsome : ∀ i : α ⊕ (α × α), ∃ q, MvPolynomial.eval q ((Sum.elim PA PB) i) ≠ 0 := by
    rintro (v | p)
    · exact hPA0 v
    · exact hPB0 p
  obtain ⟨q, hqrows, hqP⟩ := exists_common_seed_pencilRow_and_polynomials hubSel G.endsOf hsLI
    (Sum.elim PA PB) hPsome
  have hcondA : ∀ v, LinearIndepOn K (pencilChartPoint (PencilSeed.ofCoord q) hubSel)
      (if G.PencilHub v then ({v} : Set α) else G.closedNbhd v) :=
    fun v => hPA v q (hqP (Sum.inl v))
  have hcondB : ∀ u v, LinearIndepOn K (pencilChartPoint (PencilSeed.ofCoord q) hubSel)
      (if G.Adj u v then ({u, v} : Set α) else ∅) :=
    fun u v => hPB (u, v) q (hqP (Sum.inr (u, v)))
  -- Reconstruct the standing `PencilChartWF` conditions at the common seed.
  have hptnz : ∀ v, pencilChartPoint (PencilSeed.ofCoord q) hubSel v ≠ 0 := by
    intro v
    by_cases hv : G.PencilHub v
    · have h := hcondA v; rw [if_pos hv] at h
      exact (linearIndepOn_singleton_iff K).mp h
    · have h := hcondA v; rw [if_neg hv] at h
      exact (linearIndepOn_singleton_iff K).mp (h.mono (Set.singleton_subset_iff.mpr (Or.inl rfl)))
  have hhub_LI : ∀ v, LinearIndependent K
      ![hubSlotNormal (PencilSeed.ofCoord q) hubSel v 0,
        hubSlotNormal (PencilSeed.ofCoord q) hubSel v 1,
        hubSlotNormal (PencilSeed.ofCoord q) hubSel v 2] := by
    intro v
    have h := hptnz v
    rw [pencilChartPoint] at h
    exact (cross₃_ne_zero_iff_linearIndependent _ _ _).mp h
  have hpt_LI : ∀ e u v, G.IsLink e u v → LinearIndependent K
      ![pencilChartPoint (PencilSeed.ofCoord q) hubSel u,
        pencilChartPoint (PencilSeed.ofCoord q) hubSel v] := by
    intro e u v hl
    have h := hcondB u v; rw [if_pos hl.adj] at h
    rw [LinearIndependent.pair_iff]
    exact (LinearIndepOn.pair_iff (pencilChartPoint (PencilSeed.ofCoord q) hubSel) hl.ne).mp h
  have hnbr_some : ∀ v, ¬ G.PencilHub v →
      LinearIndepOn K (nbrSlotPoint (PencilSeed.ofCoord q) hubSel nbrSel v)
        {i | (nbrSel v i).isSome} := by
    intro v hv
    have h := hcondA v; rw [if_neg hv] at h
    exact linearIndepOn_nbrSlotPoint_isSome_of_pencilChartPoint (PencilSeed.ofCoord q)
      (hNbrSel v hv) h
  obtain ⟨seed', hhub_eq, hfill_eq, hWF'⟩ :=
    exists_fillNbr_pencilChartWF_of_standing hHubSel hNbrSel hhub_LI hpt_LI hnbr_some
  have hnd' := isNondegPencilRealization_pencilChartFramework_of_pencilChartWF hWF'
  -- Pinch the rank at the common seed, transported to the `fillNbr`-re-chosen seed.
  have hpcp_eq : pencilChartPoint seed' hubSel = pencilChartPoint (PencilSeed.ofCoord q) hubSel :=
    pencilChartPoint_congr hubSel hhub_eq hfill_eq
  have hgcongr : pencilChartFramework (PencilSeed.ofCoord q) hubSel G
      = pencilChartFramework seed' hubSel G :=
    pencilChartFramework_congr hubSel G hpcp_eq.symm
  have hSuppNe' : ∀ e, (pencilChartFramework seed' hubSel G).supportExtensor e ≠ 0 := hnd'.1.1.2.2.1
  have hC : ∀ e u v, G.IsLink e u v →
      (pencilChartFramework (PencilSeed.ofCoord q) hubSel G).supportExtensor e ≠ 0 := by
    intro e u v _
    rw [hgcongr]; exact hSuppNe' e
  have hn : Graph.bodyBarDim 3 = screwDim 2 := Graph.bodyBarDim_eq_screwDim_sub_one (by norm_num)
  have hrankq := finrank_span_rigidityRows_pencilChartFramework_eq_of_independent_pencilRow
    hn hGne hubSel hC hslink hqrows hscard
  have hrankOut : (Module.finrank K (Submodule.span K
        (pencilChartFramework seed' hubSel G).rigidityRows) : ℤ)
      = screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency 3 := by
    rw [← hgcongr]; exact hrankq
  exact ⟨pencilChartFramework seed' hubSel G, pencilChartNormal seed' hubSel nbrSel G,
    pencilChartPoint seed' hubSel, hnd', hrankOut⟩

/-! ## W5-L7c-5: the `5 ≤ |V|` hsplit producer (Phase 39 PENCIL)

The L7c hsplit assembly's ordered leaf (`notes/Phase39-design.md` §"W5-L7 research recon" "L7c
decomposition") carrying both open kernels: (K)'s rank-increment implication `hK` and (K-bare)'s
bare split-extension implication `hbareSplit` (both user-adjudicated to be carried rather than
discharged this session — see the design doc residues (i)/(ii) and `notes/Phase39.md` *Blockers*).
Route: `G.Simple` from `hloop` + `hnoRigid` (`simple_of_loopless_of_noRigid`, the L7c-1 reuse
pointer); a safe adjacent degree-`2` pair `(v, a₀)`
(`exists_adjacent_degree_two_pair_of_noRigid_of_degree_two`, closing L6a-safe-exists's rigid `k = 0`
half at this call site); split data at `v`
(`exists_splitOff_data_of_degree_eq_two_of_twoEdgeConnected`, L7c-2, using `a₀` itself as the
extractor's distinctness witness); align the found `v`–`a₀` edge against the extractor's `eₐ`/`e_b`
closure clause (whichever of `a`, `b` equals `a₀` is no hub, since `a₀` has degree `2 < 3` —
`hsafe`). Then split on `PencilNondegFeasible K G`: **feasible** chains L7a's `G′`-generic output
through `hK` (its output shape is identical to L7b's own `hEsc`) into L7b, forgetting to the bare
half (`hasPencilRealization_of_generic`); **infeasible** discharges the generic conjunct vacuously
and the bare half via `hbareSplit` fed the IH's `G′`-bare half. -/

set_option linter.unusedDecidableInType false in
/-- **W5-L7c-5 — the `5 ≤ |V|` hsplit producer** (Phase 39 PENCIL; `notes/Phase39-design.md`
§"W5-L7 research recon" "L7c decomposition"). Given the split-arm habitat at `5 ≤ |V(G)|` —
loopless, two-edge-connected, no proper rigid subgraph, some degree-`2` vertex, a fresh edge
available — together with kernel (K)'s carried rank-increment implication `hK`, kernel (K-bare)'s
carried bare split-extension implication `hbareSplit`, and the induction hypothesis on strictly
smaller graphs, produces `PencilPair K 3 G`. See the section docstring above for the route. -/
theorem pencilPair_of_splitOff_of_habitat
    [Inhabited α] [Finite α] [Finite β] [DecidableEq β] [Infinite K] {G : Graph α β}
    (hloop : G.Loopless) (hV : 5 ≤ V(G).ncard) (h2ec : G.TwoEdgeConnected)
    (hnoRigid : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G 3)
    (hdeg2 : ∃ v ∈ V(G), G.degree v = 2)
    (hfresh : ∃ e₀ : β, e₀ ∉ E(G))
    (hK : ∀ (G : Graph α β) (v a b : α) (eₐ e_b e₀ : β), G.Simple → 5 ≤ V(G).ncard →
      G.TwoEdgeConnected → (∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G 3) →
      G.degree v = 2 → eₐ ≠ e_b → G.IsLink eₐ v a → G.IsLink e_b v b →
      (¬ G.PencilHub a ∨ ¬ G.PencilHub b) → e₀ ∉ E(G) →
      HasGenericPencilRealization K 3 (G.splitOff v a b e₀) →
      ∃ (hubSel : α → Fin 3 → Option α) (q : α × Fin 4 × Fin 4 → K)
        (s : Set (β × Set.powersetCard (Fin 4) 2 × Set.powersetCard (Fin 4) 2)),
        (∀ w, IsFin3SelectorOf (G.closedHubNbhd w) (hubSel w)) ∧
        (∀ i ∈ s, (i : β × _ × _).1 ∈ E(G)) ∧
        ((Nat.card s : ℤ) = screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency 3) ∧
        LinearIndependent K (fun i : s => pencilRow hubSel G.endsOf q (i : β × _ × _)))
    (hbareSplit : ∀ (G : Graph α β) (v a b : α) (eₐ e_b e₀ : β), G.Simple → 5 ≤ V(G).ncard →
      G.TwoEdgeConnected → (∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G 3) →
      G.degree v = 2 → eₐ ≠ e_b → G.IsLink eₐ v a → G.IsLink e_b v b →
      (¬ G.PencilHub a ∨ ¬ G.PencilHub b) → e₀ ∉ E(G) →
      ¬ PencilNondegFeasible K G →
      HasPencilRealization K 3 (G.splitOff v a b e₀) →
      HasPencilRealization K 3 G)
    (hIH : ∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard → PencilPair K 3 G') :
    PencilPair K 3 G := by
  classical
  have hD6 : (6 : ℕ) ≤ Graph.bodyBarDim 3 := Graph.six_le_bodyBarDim (by norm_num)
  have hSimple : G.Simple :=
    Graph.simple_of_loopless_of_noRigid (n := 3) (by omega) (by omega) hloop hnoRigid
  haveI : G.Simple := hSimple
  haveI : G.Loopless := hloop
  obtain ⟨e₀, he₀⟩ := hfresh
  obtain ⟨v, a₀, hvV, ha₀V, hvdeg, ha₀deg, elink, helink⟩ :=
    Graph.exists_adjacent_degree_two_pair_of_noRigid_of_degree_two hD6 (by omega) h2ec hnoRigid
      hdeg2
  obtain ⟨a, b, eₐ, e_b, -, -, -, -, heab, hea, heb, hclosure⟩ :=
    Graph.exists_splitOff_data_of_degree_eq_two_of_twoEdgeConnected h2ec hvV ha₀V helink.ne.symm
      hvdeg
  -- Align the found safe pair `(v, a₀)` against the extractor's `eₐ`/`e_b` closure clause:
  -- whichever of `a`, `b` the edge `elink` lands on equals `a₀`, hence has degree `2` and is no
  -- hub.
  have hsafe : ¬ G.PencilHub a ∨ ¬ G.PencilHub b := by
    rcases hclosure elink a₀ helink with h | h
    · left
      have haa₀ : a = a₀ := hea.right_unique (h ▸ helink)
      intro hhub
      have h2 := hhub.2
      rw [haa₀, ha₀deg] at h2
      omega
    · right
      have hba₀ : b = a₀ := heb.right_unique (h ▸ helink)
      intro hhub
      have h2 := hhub.2
      rw [hba₀, ha₀deg] at h2
      omega
  have hV'lt : V(G.splitOff v a b e₀).ncard < V(G).ncard :=
    Graph.splitOff_vertexSet_ncard_lt hvV
  have hV'ne : V(G.splitOff v a b e₀).Nonempty := by
    refine ⟨a, ?_⟩
    rw [Graph.vertexSet_splitOff]
    exact Set.mem_diff_singleton.mpr ⟨hea.right_mem, hea.ne.symm⟩
  by_cases hfeas : PencilNondegFeasible K G
  · -- Feasible: L7a's `G′`-generic output, fed through `hK` (identical shape to L7b's `hEsc`)
    -- into L7b, forgets to the bare half.
    have hgenG' : HasGenericPencilRealization K 3 (G.splitOff v a b e₀) :=
      hasGenericPencilRealization_of_splitOff_of_safe hV hnoRigid hvdeg heab hea heb hsafe hfeas
        hIH
    have hcard : ∀ w, (G.closedHubNbhd w).ncard ≤ 3 := by
      intro w
      by_cases hw : w ∈ V(G)
      · obtain ⟨F, normal, point, hnd⟩ := hfeas
        exact ncard_closedHubNbhd_le_three_of_isNondegPencilRealization hnd hw
      · have hempty : G.closedHubNbhd w = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          rintro x ⟨hxhub, rfl | ⟨e, hlink⟩⟩
          · exact hw hxhub.1
          · exact hw hlink.left_mem
        rw [hempty]; simp
    have htf : ∀ e₁ e₂ e₃ x y z, x ≠ y → y ≠ z → x ≠ z →
        G.IsLink e₁ x y → G.IsLink e₂ y z → G.IsLink e₃ z x → False := by
      intro e₁ e₂ e₃ x y z hxy hyz hxz hl₁ hl₂ hl₃
      obtain ⟨H, hH⟩ := Graph.triangle_isProperRigidSubgraph (n := 3) (by omega) hl₁.symm hl₂
        hl₃.symm hxz (by omega)
      exact hnoRigid H hH
    have hEsc := hK G v a b eₐ e_b e₀ hSimple hV h2ec hnoRigid hvdeg heab hea heb hsafe he₀ hgenG'
    have hgen : HasGenericPencilRealization K 3 G :=
      hasGenericPencilRealization_of_independent_pencilRow_target
        (Set.nonempty_of_ncard_ne_zero (by omega)) hcard htf hEsc
    exact ⟨fun _ _ => hgen, hasPencilRealization_of_generic hgen⟩
  · -- Infeasible: the generic conjunct is vacuous; the bare half comes from `hbareSplit` fed
    -- the IH's `G′`-bare half.
    refine ⟨fun _ hf => absurd hf hfeas, ?_⟩
    exact hbareSplit G v a b eₐ e_b e₀ hSimple hV h2ec hnoRigid hvdeg heab hea heb hsafe he₀ hfeas
      (hIH _ hV'ne hV'lt).2

/-! ## W5-L7c-6: the successor wrapper closing `hsplit` (Phase 39 PENCIL)

The final leaf of the L7c hsplit assembly (`notes/Phase39-design.md` §"W5-L7 research recon" "L7c
decomposition"): wraps `pencil_conjecture_of_arms_pair` (`Pair2.lean`) into its successor, replacing
the `hsplit` hypothesis by the `|V| ∈ {3, 4}` vs `5 ≤ |V|` dispatch to the three landed producers
(`pencilPair_of_habitat_ncard_eq_three`/`_four`, `pencilPair_of_splitOff_of_habitat`). The
successor's own hypotheses are exactly the residue: `hcontract` unchanged, the two carried kernels
`hK`/`hbareSplit`, and the mechanical `∀`-form fresh-edge supply `hfresh` (residue (iv), still a
follow-up S1 discharge, not attempted here). -/

set_option linter.unusedDecidableInType false in
/-- **W5-L7c-6 — the successor wrapper closing `hsplit`** (Phase 39 PENCIL;
`notes/Phase39-design.md` §"W5-L7 research recon" "L7c decomposition"). The pencil conjecture,
conditional on the contraction arm (`hcontract`, unchanged from `pencil_conjecture_of_arms_pair`),
kernel (K)'s carried rank-increment implication `hK`, kernel (K-bare)'s carried bare
split-extension implication `hbareSplit`, and a mechanical `∀`-form fresh-edge supply `hfresh`.
Builds `hsplit` internally by dispatching on `V(G).ncard`: `= 3`/`= 4` to the direct-witness base
leaves (`Base.lean`), `5 ≤` to `pencilPair_of_splitOff_of_habitat` above, fed a fresh edge from
`hfresh`. -/
theorem pencil_conjecture_of_hcontract_hK_hbareSplit [Inhabited α] [Finite α] [Finite β]
    [DecidableEq β] [Infinite K]
    (hcontract : ∀ G : Graph α β, G.Loopless → 3 ≤ V(G).ncard →
      (∃ H : Graph α β, H.IsProperRigidSubgraph G 3) →
      (∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard →
        PencilPair K 3 G') →
      PencilPair K 3 G)
    (hK : ∀ (G : Graph α β) (v a b : α) (eₐ e_b e₀ : β), G.Simple → 5 ≤ V(G).ncard →
      G.TwoEdgeConnected → (∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G 3) →
      G.degree v = 2 → eₐ ≠ e_b → G.IsLink eₐ v a → G.IsLink e_b v b →
      (¬ G.PencilHub a ∨ ¬ G.PencilHub b) → e₀ ∉ E(G) →
      HasGenericPencilRealization K 3 (G.splitOff v a b e₀) →
      ∃ (hubSel : α → Fin 3 → Option α) (q : α × Fin 4 × Fin 4 → K)
        (s : Set (β × Set.powersetCard (Fin 4) 2 × Set.powersetCard (Fin 4) 2)),
        (∀ w, IsFin3SelectorOf (G.closedHubNbhd w) (hubSel w)) ∧
        (∀ i ∈ s, (i : β × _ × _).1 ∈ E(G)) ∧
        ((Nat.card s : ℤ) = screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency 3) ∧
        LinearIndependent K (fun i : s => pencilRow hubSel G.endsOf q (i : β × _ × _)))
    (hbareSplit : ∀ (G : Graph α β) (v a b : α) (eₐ e_b e₀ : β), G.Simple → 5 ≤ V(G).ncard →
      G.TwoEdgeConnected → (∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G 3) →
      G.degree v = 2 → eₐ ≠ e_b → G.IsLink eₐ v a → G.IsLink e_b v b →
      (¬ G.PencilHub a ∨ ¬ G.PencilHub b) → e₀ ∉ E(G) →
      ¬ PencilNondegFeasible K G →
      HasPencilRealization K 3 (G.splitOff v a b e₀) →
      HasPencilRealization K 3 G)
    (hfresh : ∀ G' : Graph α β, G'.Loopless → (∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G' 3) →
      (∃ v ∈ V(G'), G'.degree v = 2) → 3 ≤ V(G').ncard → ∃ e₀ : β, e₀ ∉ E(G'))
    (G : Graph α β) (hspan : V(G) = Set.univ) :
    PencilPair K 3 G := by
  classical
  have hsplit : ∀ G : Graph α β, G.Loopless → 3 ≤ V(G).ncard → G.TwoEdgeConnected →
      (∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G 3) →
      (∃ v ∈ V(G), G.degree v = 2) →
      (∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard → PencilPair K 3 G') →
      PencilPair K 3 G := by
    intro G hloop hV h2ec hnoRigid hdeg2 hIH
    by_cases h3 : V(G).ncard = 3
    · exact pencilPair_of_habitat_ncard_eq_three hloop h3 h2ec hnoRigid
    · by_cases h4 : V(G).ncard = 4
      · exact pencilPair_of_habitat_ncard_eq_four hloop h4 h2ec hnoRigid
      · exact pencilPair_of_splitOff_of_habitat hloop (by omega) h2ec hnoRigid hdeg2
          (hfresh G hloop hnoRigid hdeg2 hV) hK hbareSplit hIH
  exact pencil_conjecture_of_arms_pair hcontract hsplit G hspan

end CombinatorialRigidity.Molecular
