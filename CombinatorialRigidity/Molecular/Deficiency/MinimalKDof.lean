/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Deficiency.Corank

/-!
# Small minimal `k`-dof-graphs, fresh edge labels and relabelling the edges

The minimal `k`-dof-graphs of `Molecular/Deficiency.lean` with at most two vertices, the base case
of Katoh and Tanigawa's proof of their Theorem 5.5 (2011, *A proof of the molecular conjecture*,
Discrete Comput. Geom. **45**, §6), and two consequences of KT eq. (2.4)
(`Molecular/Deficiency/Corank.lean`) for the labels of the edges: a minimal `k`-dof-graph leaves a
label unused when there are enough of them, and relabelling the edges along an embedding keeps the
deficiencies and minimality. The blueprint presents the trichotomy in `sec:molecular-deficiency`,
and the labels in `sec:molecular-algebraic-induction-base`.

## Main definitions

* `Graph.embedEdges` (`def:pencil-embed-edges`).

## Main results

* `Graph.isMinimalKDof_ncard_le_two_trichotomy` — the minimal `k`-dof-graphs with at most two
  vertices (`lem:two-vertex-trichotomy`).
* `Graph.freshEdgeSupply_of_card_lt` — a minimal `k`-dof-graph leaves a label unused when
  `D(|α| - 1) < |β|` (`rem:fresh-edge-supply`).
* `Graph.deficiency_embedEdges`, `Graph.IsMinimalKDof.embedEdges` — relabelling keeps the
  deficiencies and minimality (`lem:embed-edges-simple-deficiency`, `lem:embed-edges-minimal`).
-/

@[expose] public section

namespace Graph

open Set Matroid

variable {α β : Type*}

/-! ## The minimal `k`-dof-graphs with at most two vertices (`lem:two-vertex-trichotomy`)

The base case `|V| = 2` of Katoh and Tanigawa's proof of their Theorem 5.5 (2011, §6, p. 671), with
the case `|V| = 1`: the deficiency of a graph with no edge and of a single edge, the bound of two
edges on two vertices, and the three cases. -/

/-- **The deficiency of a graph with no edge** (a step of `lem:two-vertex-trichotomy`): if
`E(G) = ∅`, then `def(G̃) = D(|V(G)| − 1)`. No labeling crosses an edge, so its value is
`D(|f '' V(G)| − 1) ≤ D(|V(G)| − 1)`, as `f '' V(G)` has at most `|V(G)|` elements; the labeling
`id`, with a part for each vertex, attains the bound. -/
theorem deficiency_of_edgeSet_empty [Finite α] {G : Graph α β} {n : ℕ}
    (hE : E(G) = ∅) :
    G.deficiency n = (bodyBarDim n : ℤ) * ((V(G).ncard : ℤ) - 1) := by
  classical
  have : Nonempty (α → α) := ⟨id⟩
  have hcross : ∀ f : α → α, G.crossingEdges f = ∅ := fun f ↦ by
    simp only [crossingEdges, hE, Set.mem_empty_iff_false, false_and, Set.ofPred_false]
  refine le_antisymm ?_ ?_
  · -- `def ≤ D(|V| − 1)`: each partition is at most the discrete one.
    rw [deficiency]
    refine ciSup_le fun f ↦ ?_
    rw [partitionDef, hcross f, Set.ncard_empty, Nat.cast_zero, mul_zero, sub_zero, numParts]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have := Set.ncard_image_le (f := f) (s := V(G)) (Set.toFinite _)
    linarith
  · -- `def ≥ D(|V| − 1)`: `f = id` achieves the bound.
    have hid : G.partitionDef n id = (bodyBarDim n : ℤ) * ((V(G).ncard : ℤ) - 1) := by
      rw [partitionDef, hcross id, Set.ncard_empty, Nat.cast_zero, mul_zero, sub_zero,
        numParts, Set.image_id]
    linarith [G.partitionDef_le_deficiency n id, hid.symm.le]

/-- **The deficiency of a single edge** (a step of `lem:two-vertex-trichotomy`): if
`V(G) = {x, y}` with `x ≠ y`, `E(G) = {e}` and `e` joins `x` and `y`, then `def(G̃) = 1`, for every
`D`. A labeling with `f x ≠ f y` has two parts and one crossing edge, so its value is
`D − (D−1) = 1`, and one with `f x = f y` has value `0`. -/
theorem deficiency_of_single_edge [Finite α] {G : Graph α β} {n : ℕ}
    {x y : α} (hxy : x ≠ y) {e : β}
    (hl : G.IsLink e x y) (hV : V(G) = {x, y}) (hE : E(G) = {e}) :
    G.deficiency n = 1 := by
  classical
  have : Nonempty (α → α) := ⟨id⟩
  have hne : V(G).Nonempty := ⟨x, by rw [hV]; exact Set.mem_insert x _⟩
  refine le_antisymm ?_ ?_
  · -- `def ≤ 1`: each partition gives `def_P ≤ 1`.
    rw [deficiency]
    refine ciSup_le fun f ↦ ?_
    -- `f '' V(G) = {f x, f y}`
    have himg : f '' V(G) = {f x, f y} := by
      rw [hV]; ext w
      simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨a, (rfl | rfl), rfl⟩ <;> tauto
      · rintro (rfl | rfl)
        exacts [⟨x, Or.inl rfl, rfl⟩, ⟨y, Or.inr rfl, rfl⟩]
    -- membership in crossingEdges
    have hmem : e ∈ G.crossingEdges f ↔ f x ≠ f y := by
      simp only [crossingEdges, Set.mem_ofPred_eq, hE, Set.mem_singleton_iff, true_and]
      refine ⟨fun ⟨p, q, hl', hd⟩ ↦ ?_, fun hd ↦ ⟨x, y, hl, hd⟩⟩
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hl.eq_and_eq_or_eq_and_eq hl'
      exacts [hd, fun h ↦ hd h.symm]
    have hcross_sub : G.crossingEdges f ⊆ {e} := fun e' he' ↦ by
      have : e' ∈ E(G) := he'.1; rwa [hE] at this
    rw [partitionDef, numParts, himg]
    set D : ℤ := (bodyBarDim n : ℤ)
    by_cases hfxy : f x = f y
    · -- same label: 1 part, 0 crossings → def_P ≤ 1
      have hpts : ({f x, f y} : Set α).ncard = 1 := by
        rw [show ({f x, f y} : Set α) = {f x} by rw [hfxy]; simp]; simp
      have hcr : (G.crossingEdges f).ncard = 0 := by
        have hempty : G.crossingEdges f = ∅ :=
          Set.eq_empty_of_forall_notMem fun e' he' ↦ by
            rcases hcross_sub he' with rfl; exact hmem.mp he' hfxy
        simp [hempty]
      rw [hpts, hcr]; push_cast; linarith
    · -- different labels: 2 parts, 1 crossing → def_P = D − (D−1) = 1 ≤ 1
      have hpts : ({f x, f y} : Set α).ncard = 2 := Set.ncard_pair hfxy
      have hcr : (G.crossingEdges f).ncard = 1 := by
        rw [show G.crossingEdges f = {e} from Set.Subset.antisymm hcross_sub
          (fun e' he' ↦ by rcases he' with rfl; exact hmem.mpr hfxy)]
        exact Set.ncard_singleton e
      rw [hpts, hcr]; push_cast; linarith
  · -- `def ≥ 1`: the two-part partition `f₀ = fun v ↦ if v = x then x else y` witnesses
    -- `def_P = D - (D-1) = 1`.
    set f₀ : α → α := fun v ↦ if v = x then x else y with hf₀_def
    have hf₀img : f₀ '' V(G) = {x, y} := by
      have hfx : f₀ x = x := by simp [hf₀_def]
      have hfy : f₀ y = y := by simp [hf₀_def, hxy.symm]
      rw [hV, Set.image_insert_eq, Set.image_singleton, hfx, hfy]
    have hf₀cross : G.crossingEdges f₀ = {e} := by
      apply Set.Subset.antisymm
      · intro e' he'; have : e' ∈ E(G) := he'.1; rwa [hE] at this
      · intro e' he'
        rw [Set.mem_singleton_iff] at he'; subst he'
        refine ⟨hl.edge_mem, x, y, hl, ?_⟩
        simp only [hf₀_def, ite_eq_left rfl, ite_eq_right hxy.symm]; exact hxy
    have hfun : G.partitionDef n f₀ = 1 := by
      rw [partitionDef, numParts, hf₀img, hf₀cross, Set.ncard_pair hxy, Set.ncard_singleton]
      push_cast; ring
    linarith [G.partitionDef_le_deficiency n f₀, hfun.symm.le]

/-- **A minimal `k`-dof-graph on two vertices has at most two edges** (a step of
`lem:two-vertex-trichotomy`), for `D ≥ 2`. Katoh and Tanigawa deduce it from their Lemma 3.2, a
minimal `k`-dof-graph is not `3`-edge-connected (2011, pp. 657 and 671); the proof here is direct.

`G` has no loops (`loopless_of_isMinimalKDof`), so each edge joins the two vertices `x, y`. Suppose
that `G` has three edges `e₁, e₂, e₃`. Then `H = G ↾ {e₁, e₂}` is a `0`-dof-graph
(`isKDof_zero_of_parallel_pair`), so a base `B_H` of `M(H̃)` has `D` elements by KT eq. (2.4)
(`isBase_ncard_add_deficiency_eq`), and it is independent in `M(G̃)`
(`matroidMG_restrict_mulTilde`). So `rank M(G̃) ≥ D`, and KT eq. (2.4) for `G`, with `k ≥ 0`, gives
`k = 0` and `B_H` a base of `M(G̃)`. But `B_H ⊆ E(H̃)` misses the copies of `e₃`, against the
minimality of `G`. -/
theorem edgeSet_ncard_le_two_of_isMinimalKDof_of_ncard_two [DecidableEq β] [Finite α]
    [Finite β] {G : Graph α β} {n : ℕ} {k : ℤ} (hD : 2 ≤ bodyBarDim n)
    (hG : G.IsMinimalKDof n k) (hV : V(G).ncard = 2) : E(G).ncard ≤ 2 := by
  by_contra hlt
  push Not at hlt
  have hLl := loopless_of_isMinimalKDof hG
  obtain ⟨x, y, hne, hVG⟩ := Set.ncard_eq_two.mp hV
  -- Extract three distinct edges using Set.ncard_eq_three.
  obtain ⟨t, htE, ht3⟩ := Set.exists_subset_card_eq (s := E(G)) (n := 3) (by omega)
  obtain ⟨e₁, e₂, e₃, hne₁₂, hne₁₃, hne₂₃, hteq⟩ := Set.ncard_eq_three.mp ht3
  have he₁ : e₁ ∈ E(G) := htE (hteq ▸ Set.mem_insert _ _)
  have he₂ : e₂ ∈ E(G) := htE (hteq ▸ Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have he₃ : e₃ ∈ E(G) := htE (hteq ▸ Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  -- Each edge links x to y (looplessness + V(G) = {x, y}).
  have linkxy : ∀ f, f ∈ E(G) → G.IsLink f x y := by
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
  have hlink₁ : G.IsLink e₁ x y := linkxy e₁ he₁
  have hlink₂ : G.IsLink e₂ x y := linkxy e₂ he₂
  -- Restriction H = G ↾ {e₁, e₂} is 0-dof.
  set H := G ↾ ({e₁, e₂} : Set β) with hH_def
  have hHle : H ≤ G := restrict_le
  have hHL1 : H.IsLink e₁ x y := by
    simp only [hH_def, restrict_isLink]; exact ⟨Set.mem_insert e₁ _, hlink₁⟩
  have hHL2 : H.IsLink e₂ x y := by
    simp only [hH_def, restrict_isLink]; exact ⟨Set.mem_insert_of_mem _ rfl, hlink₂⟩
  have hVH : V(H) = {x, y} := by
    simp only [hH_def, vertexSet_restrict, hVG]
  have hEH : E(H) = {e₁, e₂} := by
    simp only [hH_def, edgeSet_restrict]
    exact Set.inter_eq_right.mpr
      (Set.insert_subset_iff.mpr ⟨he₁, Set.singleton_subset_iff.mpr he₂⟩)
  have hH0 : H.IsKDof n 0 :=
    isKDof_zero_of_parallel_pair hD hne hHL1 hHL2 hne₁₂ hVH hEH
  have hHne : V(H).Nonempty := hVH ▸ ⟨x, Set.mem_insert x _⟩
  have hD1 : 1 ≤ bodyBarDim n := by omega
  -- Get a base B_H of M(H̃) and compute |B_H|.
  obtain ⟨B_H, hB_H⟩ := H.matroidMG n |>.exists_isBase
  have hVH2 : V(H).ncard = 2 := by
    rw [hVH]; exact Set.ncard_pair hne
  have hBsize : (B_H.ncard : ℤ) = (bodyBarDim n : ℤ) := by
    have heq := H.isBase_ncard_add_deficiency_eq n hD1 hHne hB_H
    rw [hH0, hVH2] at heq; push_cast at heq; linarith
  -- B_H is M(G̃)-independent via the restriction identity.
  have hBindep : (G.matroidMG n).Indep B_H := by
    have hrestr : ((G.matroidMG n) ↾ E(H.mulTilde n)).Indep B_H := by
      rw [matroidMG_restrict_mulTilde hHle]; exact hB_H.indep
    rw [restrict_indep_iff] at hrestr; exact hrestr.1
  -- rank M(G̃) ≥ D and k = 0.
  have hne_G : V(G).Nonempty := ⟨x, by rw [hVG]; exact Set.mem_insert x _⟩
  -- rank + def = D(|V|-1) = D·1 = D.
  have hRD_eq : (G.matroidMG n).rank + G.deficiency n = bodyBarDim n * ((V(G).ncard : ℤ) - 1) :=
    G.rank_add_deficiency_eq n hD1 hne_G
  have hk_val : k = G.deficiency n := hG.deficiency_eq.symm
  -- rank M(G̃) ≥ D: B_H is D-element independent.
  have hMFin : (G.matroidMG n).Finite := Matroid.finite_of_finite (M := G.matroidMG n)
  have hrank_ge : (bodyBarDim n : ℤ) ≤ (G.matroidMG n).rank := by
    have hle := hBindep.ncard_le_rank
    have : (B_H.ncard : ℤ) ≤ ((G.matroidMG n).rank : ℤ) := by exact_mod_cast hle
    linarith [hBsize]
  -- k = 0.
  have hkle : k ≤ 0 := by
    have : (G.matroidMG n).rank + k = bodyBarDim n := by
      rw [← hk_val, hV] at hRD_eq; push_cast at hRD_eq; linarith
    linarith
  have hkge : 0 ≤ k := hk_val ▸ G.deficiency_nonneg n hne_G
  have hk0 : k = 0 := le_antisymm hkle hkge
  -- rank M(G̃) = D.
  have hrank_D : (G.matroidMG n).rank = bodyBarDim n := by
    have hdef0 : G.deficiency n = 0 := hk_val.symm.trans hk0
    rw [← hk_val, hV] at hRD_eq; push_cast at hRD_eq; linarith [hdef0]
  -- B_H is a base of M(G̃).
  have hBbase : (G.matroidMG n).IsBase B_H := by
    apply hBindep.isBase_of_ncard
    rw [hrank_D]; exact_mod_cast hBsize.symm.le
  -- e₃ hits B_H (minimality of G); but B_H ⊆ E(H̃) avoids e₃.
  obtain ⟨p, hpBH, hpe₃⟩ := hG.2 B_H hBbase e₃ he₃
  have hpH : p ∈ E(H.mulTilde n) := hB_H.subset_ground hpBH
  simp only [hH_def, mem_edgeSet_mulTilde] at hpH
  simp only [edgeSet_restrict, Set.mem_inter_iff,
    Set.mem_insert_iff, Set.mem_singleton_iff] at hpH
  simp only [mem_edgeFiber] at hpe₃
  obtain ⟨-, h | h⟩ := hpH <;> simp_all

/-- **The minimal `k`-dof-graphs with at most two vertices** (`lem:two-vertex-trichotomy`; KT
p. 671): for `D ≥ 2`, a minimal `k`-dof-graph `G` with one or two vertices satisfies one of
- `E(G) = ∅` and `k = D(|V(G)| − 1)`, with one or two vertices;
- `V(G) = {x, y}` with `x ≠ y`, `E(G) = {e}`, `e` joins `x` and `y`, and `k = 1`;
- `V(G) = {x, y}` with `x ≠ y`, `E(G) = {e, f}` with `e ≠ f`, both join `x` and `y`, and `k = 0`.

With one vertex, `G` has no edge, as it has no loop (`loopless_of_isMinimalKDof`). With two, it has
at most two edges (`edgeSet_ncard_le_two_of_isMinimalKDof_of_ncard_two`), and the three cases are
`deficiency_of_edgeSet_empty`, `deficiency_of_single_edge` and `isKDof_zero_of_parallel_pair`. -/
theorem isMinimalKDof_ncard_le_two_trichotomy [DecidableEq β] [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} {k : ℤ} (hD : 2 ≤ bodyBarDim n)
    (hG : G.IsMinimalKDof n k) (hne : V(G).Nonempty) (hV : V(G).ncard ≤ 2) :
    (E(G) = ∅ ∧ k = (bodyBarDim n : ℤ) * ((V(G).ncard : ℤ) - 1)) ∨
    (∃ x y e, x ≠ y ∧ V(G) = {x, y} ∧ E(G) = {e} ∧ G.IsLink e x y ∧ k = 1) ∨
    (∃ x y e f, x ≠ y ∧ e ≠ f ∧ V(G) = {x, y} ∧ E(G) = {e, f} ∧
      G.IsLink e x y ∧ G.IsLink f x y ∧ k = 0) := by
  classical
  have hLl := loopless_of_isMinimalKDof hG
  -- Dispatch on |V| = 1 vs. |V| = 2.
  have hVpos : 0 < V(G).ncard := hne.ncard_pos
  rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt hVpos) with hV1 | hV1
  · -- |V| ≥ 2 but ≤ 2 → |V| = 2.
    have hV2 : V(G).ncard = 2 := le_antisymm hV hV1
    obtain ⟨x, y, hxy, hVG⟩ := Set.ncard_eq_two.mp hV2
    have hEle2 : E(G).ncard ≤ 2 :=
      edgeSet_ncard_le_two_of_isMinimalKDof_of_ncard_two hD hG hV2
    -- Each edge links x to y.
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
    -- Case on |E| = 0, 1, or 2.
    rcases Nat.eq_zero_or_pos (E(G).ncard) with hE0 | hEpos
    · have hE : E(G) = ∅ := by rwa [← Set.ncard_eq_zero (Set.toFinite _)]
      exact Or.inl ⟨hE, hG.deficiency_eq.symm.trans (deficiency_of_edgeSet_empty hE)⟩
    · -- |E| = 1 or |E| = 2
      have hE12 : E(G).ncard = 1 ∨ E(G).ncard = 2 := by omega
      rcases hE12 with hE1 | hE2
      · obtain ⟨e, hE⟩ := Set.ncard_eq_one.mp hE1
        have hlinkxy : G.IsLink e x y := hlinks e (hE ▸ Set.mem_singleton e)
        exact Or.inr (Or.inl ⟨x, y, e, hxy, hVG, hE, hlinkxy,
          hG.deficiency_eq.symm.trans (deficiency_of_single_edge hxy hlinkxy hVG hE)⟩)
      · obtain ⟨e₁, e₂, hne₁₂, hE⟩ := Set.ncard_eq_two.mp hE2
        have hl₁ : G.IsLink e₁ x y := hlinks e₁ (hE ▸ Set.mem_insert e₁ _)
        have hl₂ : G.IsLink e₂ x y := hlinks e₂ (hE ▸ Set.mem_insert_of_mem _ rfl)
        have hk0 : k = 0 :=
          hG.deficiency_eq.symm.trans (isKDof_zero_of_parallel_pair hD hxy hl₁ hl₂ hne₁₂ hVG hE)
        exact Or.inr (Or.inr ⟨x, y, e₁, e₂, hxy, hne₁₂, hVG, hE, hl₁, hl₂, hk0⟩)
  · -- |V| = 1: looplessness forces E = ∅.
    have hV1' : V(G).ncard = 1 := hV1.symm
    obtain ⟨a, hVa⟩ := Set.ncard_eq_one.mp hV1'
    have hE : E(G) = ∅ := by
      ext e; simp only [Set.mem_empty_iff_false, iff_false]
      intro he
      obtain ⟨p, q, hlink⟩ := G.exists_isLink_of_mem_edgeSet he
      have hpV : p ∈ V(G) := hlink.left_mem
      have hqV : q ∈ V(G) := hlink.right_mem
      rw [hVa] at hpV hqV
      rw [Set.mem_singleton_iff] at hpV hqV
      exact hlink.ne (hpV ▸ hqV ▸ rfl)
    exact Or.inl ⟨hE, hG.deficiency_eq.symm.trans (deficiency_of_edgeSet_empty hE)⟩

/-! ## Fresh edge labels (`rem:fresh-edge-supply`)

The graphs of the induction take their edges from one type `β` of labels, and an operation that
adds an edge needs a label that the graph does not use. A minimal `k`-dof-graph `G` has at most
`D(|V(G)| - 1) - def(G̃)` edges, so when `D(|α| - 1) < |β|` some label is unused. Minimality is
needed: a graph whose edges are loops at one vertex can use every label. -/

/-- **A minimal `k`-dof-graph has at most `D(|V(G)| - 1) - def(G̃)` edges** (a step of
`rem:fresh-edge-supply`): for `D ≥ 1` and `V(G)` nonempty, `|E(G)| + def(G̃) ≤ D(|V(G)| - 1)`. A
base `B` of `M(G̃)` meets the copies of every edge of `G`, as `G` is minimal, so
`E(G) ⊆ Prod.fst '' B` and `|E(G)| ≤ |B|`; and `|B| + def(G̃) = D(|V(G)| - 1)` by KT eq. (2.4)
(`isBase_ncard_add_deficiency_eq`). -/
theorem edgeSet_ncard_add_deficiency_le_of_isMinimalKDof
    [DecidableEq β] [Finite α] [Finite β] {G : Graph α β} {n : ℕ} {k : ℤ}
    (hD : 1 ≤ bodyBarDim n) (hne : V(G).Nonempty) (hG : G.IsMinimalKDof n k) :
    (E(G).ncard : ℤ) + G.deficiency n ≤ bodyBarDim n * ((V(G).ncard : ℤ) - 1) := by
  obtain ⟨B, hB⟩ := (G.matroidMG n).exists_isBase
  have hsub : E(G) ⊆ Prod.fst '' B := by
    intro e he
    obtain ⟨p, hpB, hpe⟩ := hG.2 B hB e he
    rw [mem_edgeFiber] at hpe
    exact ⟨p, hpB, hpe⟩
  have hle : (E(G).ncard : ℤ) ≤ (B.ncard : ℤ) := by
    have := (Set.ncard_le_ncard hsub).trans (Set.ncard_image_le (s := B) (f := Prod.fst))
    exact_mod_cast this
  linarith [hle, G.isBase_ncard_add_deficiency_eq n hD hne hB]

/-- **A fresh edge label** (`rem:fresh-edge-supply`): for `D ≥ 1` and `D(|α| - 1) < |β|`, every
minimal `c`-dof-graph `G'` on `α`, for every `c`, leaves some label `e₀ ∉ E(G')`. Suppose that
`E(G')` is all of `β`. Then `β` is nonempty, as `|β| > 0`, so `G'` has an edge and a vertex, and
`|β| = |E(G')| ≤ D(|V(G')| - 1) ≤ D(|α| - 1) < |β|` by
`edgeSet_ncard_add_deficiency_le_of_isMinimalKDof` and `deficiency_nonneg`. The induction of KT
Theorem 5.5 assumes this bound or a form of its conclusion (`rem:fresh-edge-supply`). -/
theorem freshEdgeSupply_of_card_lt [DecidableEq β] [Finite α] [Finite β] {n : ℕ}
    (hD : 1 ≤ bodyBarDim n) (hcard : bodyBarDim n * (Nat.card α - 1) < Nat.card β) :
    ∀ (c : ℤ) (G' : Graph α β), G'.IsMinimalKDof n c → ∃ e₀ : β, e₀ ∉ E(G') := by
  intro c G' hG'
  by_contra hcon
  push Not at hcon
  have hEuniv : E(G') = Set.univ := Set.eq_univ_of_forall hcon
  -- `β` is nonempty: the RHS of `hcard` dominates a nonnegative left side.
  have hβpos : 0 < Nat.card β := lt_of_le_of_lt (Nat.zero_le _) hcard
  obtain ⟨e₀ne⟩ : Nonempty β := (Nat.card_pos_iff.mp hβpos).1
  -- an edge forces a vertex, so `V(G')` is nonempty and `α` is (locally) nonempty.
  have he₀ : e₀ne ∈ E(G') := hEuniv ▸ Set.mem_univ e₀ne
  obtain ⟨x, _, hlink⟩ := G'.exists_isLink_of_mem_edgeSet he₀
  have hVne : V(G').Nonempty := ⟨x, hlink.left_mem⟩
  have hαpos : 1 ≤ Nat.card α := Nat.card_pos_iff.mpr ⟨⟨x⟩, ‹Finite α›⟩
  -- headroom, cast to `ℤ` (real subtraction now, since both sides are `≥ 1`).
  have hcardZ : (bodyBarDim n : ℤ) * ((Nat.card α : ℤ) - 1) < (Nat.card β : ℤ) := by
    zify [hαpos] at hcard
    exact hcard
  -- the edge-count bound + nonnegativity of the deficiency, cast against `α`'s bound.
  have hbound := G'.edgeSet_ncard_add_deficiency_le_of_isMinimalKDof hD hVne hG'
  have hdefnn := G'.deficiency_nonneg n hVne
  have hVle : (V(G').ncard : ℤ) ≤ (Nat.card α : ℤ) := by
    have h1 := Set.ncard_le_ncard (Set.subset_univ V(G'))
    rw [Set.ncard_univ] at h1
    exact_mod_cast h1
  have hDnn : (0 : ℤ) ≤ bodyBarDim n := by positivity
  have hVle' : (V(G').ncard : ℤ) - 1 ≤ (Nat.card α : ℤ) - 1 := by linarith
  have hmul : (bodyBarDim n : ℤ) * ((V(G').ncard : ℤ) - 1) ≤
      (bodyBarDim n : ℤ) * ((Nat.card α : ℤ) - 1) :=
    mul_le_mul_of_nonneg_left hVle' hDnn
  have hEeq : (E(G').ncard : ℤ) = (Nat.card β : ℤ) := by rw [hEuniv, Set.ncard_univ]
  linarith [hbound, hdefnn, hmul, hcardZ, hEeq]

/-! ## Relabelling the edges (`def:pencil-embed-edges`, `lem:embed-edges-simple-deficiency`,
`lem:embed-edges-minimal`)

Relabelling the edges of `G` along an embedding `ι : β ↪ β'` keeps the bodies, the adjacencies and
the deficiencies, and it keeps minimality (`IsMinimalKDof.embedEdges`). It is the transport that
drops the bound on the edge labels from the main results: a graph on `β` is relabelled into
`β ⊕ Fin N`, where the fresh-label supply holds (`freshEdgeSupply_padded`). -/

/-- **Relabel the edges of `G` along an embedding `ι : β ↪ β'`** (`def:pencil-embed-edges`): the
graph on `V(G)` with an edge `ι e` linking `x` and `y` for every link `e` of `G`. It has the same
vertices, adjacencies and closed neighbourhoods as `G`, so the deficiencies
(`lem:embed-edges-simple-deficiency`), the lifting space and admissibility
(`lem:pencil-jj-embed-edges`) are unchanged; only the label type grows, which is what
lets the dimension of the lifting space be drawn from the planar case of KT Theorem 5.6 with no
supply of spare labels assumed (`fmlnote:pencil-jj-embed-edges`). -/
def embedEdges {β' : Type*} (G : Graph α β) (ι : β ↪ β') : Graph α β' where
  vertexSet := V(G)
  IsLink e x y := ∃ e₀, ι e₀ = e ∧ G.IsLink e₀ x y
  isLink_symm := by
    rintro e -
    exact ⟨fun x y ⟨e₀, he, h⟩ => ⟨e₀, he, h.symm⟩⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro e x y v w ⟨e₀, rfl, h⟩ ⟨e₁, he, h'⟩
    obtain rfl := ι.injective he
    exact h.left_eq_or_eq h'
  left_mem_of_isLink := by
    rintro e x y ⟨e₀, -, h⟩
    exact h.left_mem

section embedEdges

variable {β' : Type*} {G : Graph α β} {ι : β ↪ β'}

/-- Relabelling keeps the bodies (a step of `lem:embed-edges-simple-deficiency`, whose proof names
it). -/
@[simp]
theorem vertexSet_embedEdges : V(G.embedEdges ι) = V(G) := rfl

/-- The links of the relabelled graph are the relabelled links (a step of
`lem:embed-edges-simple-deficiency`, whose proof names it). -/
theorem embedEdges_isLink {e : β'} {x y : α} :
    (G.embedEdges ι).IsLink e x y ↔ ∃ e₀, ι e₀ = e ∧ G.IsLink e₀ x y := Iff.rfl

/-- The edges of the relabelled graph are the relabelled edges (a step of
`lem:embed-edges-simple-deficiency`, whose proof names it). -/
theorem edgeSet_embedEdges : E(G.embedEdges ι) = ι '' E(G) := by
  ext e
  refine ⟨fun ⟨x, y, e₀, he, h⟩ => ⟨e₀, h.edge_mem, he⟩, ?_⟩
  rintro ⟨e₀, he₀, rfl⟩
  obtain ⟨x, y, h⟩ := G.exists_isLink_of_mem_edgeSet he₀
  exact ⟨x, y, e₀, rfl, h⟩

/-- **Relabelling keeps a simple graph simple** (`lem:embed-edges-simple-deficiency`, its first
clause). -/
theorem Simple.embedEdges (hG : G.Simple) : (G.embedEdges ι).Simple where
  not_isLoopAt := by
    rintro e x ⟨e₀, -, h⟩
    exact hG.toLoopless.not_isLoopAt e₀ x h
  eq_of_isLink := by
    rintro e f x y ⟨e₀, rfl, h⟩ ⟨f₀, rfl, h'⟩
    rw [hG.eq_of_isLink h h']

/-- **Relabelling keeps every deficiency** (`lem:embed-edges-simple-deficiency`, its second
clause): a partition crosses the images of the edges it crossed before. -/
theorem deficiency_embedEdges (n : ℕ) :
    (G.embedEdges ι).deficiency n = G.deficiency n := by
  have hcross : ∀ f : α → α, (G.embedEdges ι).crossingEdges f = ι '' G.crossingEdges f := by
    intro f
    ext e
    simp only [Graph.crossingEdges, Graph.edgeSet_embedEdges, Graph.embedEdges_isLink,
      Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨⟨e₀, he₀, rfl⟩, x, y, ⟨e₁, he₁, h⟩, hxy⟩
      obtain rfl := ι.injective he₁
      exact ⟨e₁, ⟨he₀, x, y, h, hxy⟩, rfl⟩
    · rintro ⟨e₀, ⟨he₀, x, y, h, hxy⟩, rfl⟩
      exact ⟨⟨e₀, he₀, rfl⟩, x, y, ⟨e₀, rfl, h⟩, hxy⟩
  have hdef : ∀ f : α → α, (G.embedEdges ι).partitionDef n f = G.partitionDef n f := by
    intro f
    simp only [Graph.partitionDef, Graph.numParts, Graph.vertexSet_embedEdges, hcross,
      Set.ncard_image_of_injective _ ι.injective]
  simp only [Graph.deficiency, hdef]

/-- Deleting an edge of a minimal `c`-dof-graph raises the deficiency. -/
theorem deficiency_lt_of_isMinimalKDof [DecidableEq β] [Finite α] [Finite β] {G : Graph α β}
    {n : ℕ} {c : ℤ} (hD : 1 ≤ Graph.bodyBarDim n) (hG : G.IsMinimalKDof n c) {e : β}
    (he : e ∈ E(G)) : G.deficiency n < (G ↾ (E(G) \ {e})).deficiency n := by
  classical
  set G'' := G ↾ (E(G) \ {e}) with hG''
  have hle : G'' ≤ G := Graph.restrict_le
  have hV : V(G'') = V(G) := Graph.vertexSet_restrict ..
  have hne : V(G).Nonempty := by
    obtain ⟨x, y, h⟩ := G.exists_isLink_of_mem_edgeSet he
    exact ⟨x, h.left_mem⟩
  have hge := Graph.deficiency_le_deficiency_of_le_vertexSet_eq hD hle hV
  refine lt_of_le_of_ne hge fun heq => ?_
  obtain ⟨B, hB⟩ := (G''.matroidMG n).exists_isBase
  have hBindep : (G.matroidMG n).Indep B := by
    have hrestr : ((G.matroidMG n).restrict E(G''.mulTilde n)).Indep B := by
      rw [Graph.matroidMG_restrict_mulTilde hle]; exact hB.indep
    exact (Matroid.restrict_indep_iff.mp hrestr).1
  have hBsize := G''.isBase_ncard_add_deficiency_eq n hD (hV ▸ hne) hB
  have hrank := G.rank_add_deficiency_eq n hD hne
  have : (G.matroidMG n).Finite := Matroid.finite_of_finite (M := G.matroidMG n)
  have hBbase : (G.matroidMG n).IsBase B := by
    apply hBindep.isBase_of_ncard
    rw [hV, ← heq] at hBsize
    have : (B.ncard : ℤ) = (G.matroidMG n).rank := by linarith
    exact_mod_cast this.symm.le
  obtain ⟨p, hpB, hpe⟩ := hG.2 B hBbase e he
  have hp : p ∈ E(G''.mulTilde n) := hB.subset_ground hpB
  rw [Graph.mem_edgeSet_mulTilde, hG'', Graph.edgeSet_restrict] at hp
  rw [Graph.mem_edgeFiber] at hpe
  exact hp.2.2 hpe

/-- A `c`-dof-graph whose every edge deletion raises the deficiency is minimal. -/
theorem isMinimalKDof_of_deficiency_lt [DecidableEq β] [Finite α] [Finite β] {G : Graph α β}
    {n : ℕ} {c : ℤ} (hD : 1 ≤ Graph.bodyBarDim n) (hc : G.deficiency n = c)
    (hlt : ∀ e ∈ E(G), G.deficiency n < (G ↾ (E(G) \ {e})).deficiency n) :
    G.IsMinimalKDof n c := by
  classical
  refine ⟨hc, fun B hB e he => ?_⟩
  set G'' := G ↾ (E(G) \ {e}) with hG''
  have hle : G'' ≤ G := Graph.restrict_le
  have hV : V(G'') = V(G) := Graph.vertexSet_restrict ..
  have hne : V(G).Nonempty := by
    obtain ⟨x, y, h⟩ := G.exists_isLink_of_mem_edgeSet he
    exact ⟨x, h.left_mem⟩
  by_contra hBe
  rw [Set.not_nonempty_iff_eq_empty] at hBe
  have hBsub : B ⊆ E(G''.mulTilde n) := by
    intro p hp
    have hpG : p ∈ E(G.mulTilde n) := hB.subset_ground hp
    rw [Graph.mem_edgeSet_mulTilde] at hpG ⊢
    rw [hG'', Graph.edgeSet_restrict]
    refine ⟨hpG, hpG, fun hpe => ?_⟩
    rw [Set.eq_empty_iff_forall_notMem] at hBe
    exact hBe p ⟨hp, by rw [Graph.mem_edgeFiber]; exact hpe⟩
  have hBindep : (G''.matroidMG n).Indep B := by
    have hrestr : ((G.matroidMG n).restrict E(G''.mulTilde n)).Indep B :=
      Matroid.restrict_indep_iff.mpr ⟨hB.indep, hBsub⟩
    rwa [Graph.matroidMG_restrict_mulTilde hle] at hrestr
  have : (G''.matroidMG n).Finite := Matroid.finite_of_finite (M := G''.matroidMG n)
  have hBrank : (B.ncard : ℤ) ≤ (G''.matroidMG n).rank := by exact_mod_cast hBindep.ncard_le_rank
  have hBcard := G.isBase_ncard_add_deficiency_eq n hD hne hB
  have hrank'' := G''.rank_add_deficiency_eq n hD (hV ▸ hne)
  rw [hV] at hrank''
  have := hlt e he
  linarith

/-- Restricting to all edges but one commutes with the relabelling. -/
theorem embedEdges_restrict_diff {G : Graph α β} {ι : β ↪ β'} (e : β) :
    (G.embedEdges ι) ↾ (E(G.embedEdges ι) \ {ι e}) = (G ↾ (E(G) \ {e})).embedEdges ι := by
  refine Graph.ext rfl fun f x y => ?_
  simp only [Graph.restrict_isLink, Graph.embedEdges_isLink, Graph.edgeSet_embedEdges,
    Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_image]
  constructor
  · rintro ⟨⟨-, hne⟩, e₀, rfl, h⟩
    exact ⟨e₀, rfl, ⟨h.edge_mem, fun h' => hne (h' ▸ rfl)⟩, h⟩
  · rintro ⟨e₀, rfl, ⟨-, hne⟩, h⟩
    exact ⟨⟨⟨e₀, h.edge_mem, rfl⟩, fun h' => hne (ι.injective h')⟩, e₀, rfl, h⟩

/-- The relabelled graph of a minimal `c`-dof-graph is a minimal `c`-dof-graph. -/
theorem IsMinimalKDof.embedEdges [DecidableEq β] [DecidableEq β'] [Finite α] [Finite β]
    [Finite β'] {G : Graph α β} {n : ℕ} {c : ℤ} (hD : 1 ≤ Graph.bodyBarDim n)
    (hG : G.IsMinimalKDof n c) (ι : β ↪ β') : (G.embedEdges ι).IsMinimalKDof n c := by
  refine isMinimalKDof_of_deficiency_lt hD
    ((Graph.deficiency_embedEdges n).trans hG.deficiency_eq) fun e' he' => ?_
  rw [Graph.edgeSet_embedEdges] at he'
  obtain ⟨e, he, rfl⟩ := he'
  rw [embedEdges_restrict_diff, Graph.deficiency_embedEdges, Graph.deficiency_embedEdges]
  exact deficiency_lt_of_isMinimalKDof hD hG he

/-- **The fresh-label supply at the padded label type** (`rem:fresh-edge-supply`): for `D ≥ 1`,
every minimal `c`-dof-graph on `α` with labels in `β ⊕ Fin (D(|α| - 1) + 1)` leaves some label
outside its edge set. It is `freshEdgeSupply_of_card_lt` at that type, whose cardinality
`|β| + D(|α| - 1) + 1` exceeds `D(|α| - 1)`. -/
theorem freshEdgeSupply_padded [DecidableEq β] [Finite α] [Finite β] {n : ℕ}
    (hD : 1 ≤ bodyBarDim n) :
    ∀ (c : ℤ) (G' : Graph α (β ⊕ Fin (bodyBarDim n * (Nat.card α - 1) + 1))),
      G'.IsMinimalKDof n c → ∃ e₀, e₀ ∉ E(G') :=
  freshEdgeSupply_of_card_lt hD (by rw [Nat.card_sum, Nat.card_fin]; omega)

end embedEdges

end Graph
