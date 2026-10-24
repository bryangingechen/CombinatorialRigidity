/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Induction.Operations

/-!
# The combinatorial induction: the deficiency after splitting off and after removal

Results of the combinatorial induction (`sec:molecular-induction-dof`) after Katoh and Tanigawa
(2011, *A proof of the molecular conjecture*, Discrete Comput. Geom. **45**, §4.1). For a vertex `v`
of a multigraph `G` whose only edges `eₐ` and `e_b` join it to `a, b ≠ v`, and `D = bodyBarDim n`,
it proves by comparing the values of partitions (`def:D-deficiency`):

* the bounds `def(G̃) - 1 ≤ def(G̃_v^{ab}) ≤ def(G̃)` of KT Lemma 4.3(i)
  (`lem:splitoff-deficiency`), the upper bound also when the new edge takes the label `eₐ`
  (`lem:splitoff-deficiency-reuse`);
* the bound `def(G̃) ≤ def(G̃_v)` of KT Lemma 4.4 (`lem:removal-deficiency`), and the three bounds
  together (`lem:dof-tracking`);
* a bound on the deficiency after splitting off from the merged deficiency of `G - v` at `a` and `b`
  (`lem:splitoff-deficiency-merged`), for `main-component.tex`.

Katoh and Tanigawa prove these bounds with forests (`rem:kt-lemma-41`, `rem:kt-lemma-44`).
-/

@[expose] public section

namespace Graph

open Set Matroid

variable {α β : Type*}

/-! ## Splitting off does not raise the deficiency (`lem:splitoff-deficiency`)

The upper bound `def(G̃_v^{ab}) ≤ def(G̃)` of KT Lemma 4.3(i) (p. 661), without forests
(`rem:kt-lemma-41` (3)). A partition `P'` of `V(G) ∖ {v}` extends to a partition `P` of `V(G)` by
adding `v` to the part of `a` (`f = update f' v (f' a)`). Then `|P| = |P'|`, `eₐ` joins two vertices
of one part of `P`, `e_b` joins two parts of `P` exactly when the new edge `ab` joins two parts of
`P'`, and every other edge has the same ends in both graphs. So the value of `P'` for `G̃_v^{ab}` is
at most that of `P` for `G̃`. -/

/-- The common proof of `splitOff_deficiency_le` and `splitOff_deficiency_le_of_eq_left`: the label
`e₀` of the new edge is either not an edge of `G` or `eₐ` (`he₀`). In both cases `e₀` does not join
two parts of the extended partition, which is all the proof uses of it. -/
private theorem splitOff_deficiency_le_aux [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hD : 1 ≤ bodyBarDim n) {v a b : α} {e₀ eₐ e_b : β}
    (hav : a ≠ v) (hbv : b ≠ v)
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    (he₀ : e₀ ∉ E(G) ∨ e₀ = eₐ) :
    (G.splitOff v a b e₀).deficiency n ≤ G.deficiency n := by
  classical
  set H := G.splitOff v a b e₀ with hH
  have haV : a ∈ V(G) := hla.right_mem
  have hbV : b ∈ V(G) := hlb.right_mem
  -- It suffices to bound each partition `P'` of `H` by `def(G̃)`.
  have : Nonempty α := ⟨a⟩
  rw [deficiency]
  refine ciSup_le fun f' => ?_
  -- Extend `f'` to a partition `f` of `V(G)` by dropping `v` into `a`'s block.
  set f := Function.update f' v (f' a) with hf
  have hfne : ∀ x, x ≠ v → f x = f' x := fun x hx => Function.update_of_ne hx _ _
  have hfv : f v = f' a := Function.update_self v (f' a) f'
  -- Step 1: the number of parts is unchanged.
  have hparts : G.numParts f = H.numParts f' := by
    rw [numParts, numParts, vertexSet_splitOff]
    congr 1
    apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      by_cases hxv : x = v
      · subst hxv
        exact ⟨a, ⟨haV, by simpa using hav⟩, by rw [hfv]⟩
      · exact ⟨x, ⟨hx, by simpa using hxv⟩, (hfne x hxv).symm⟩
    · rintro _ ⟨x, ⟨hx, hxv⟩, rfl⟩
      exact ⟨x, hx, hfne x (by simpa using hxv)⟩
  have hfa : f a = f' a := hfne a hav
  -- `e₀` does not cross `f`: it is not an edge of `G`, or it is `eₐ`, whose ends `v` and `a` both
  -- have the label `f' a`.
  have he₀cross : e₀ ∉ G.crossingEdges f := by
    rcases he₀ with he₀ | rfl
    · exact fun h => he₀ h.1
    · rintro ⟨-, x, y, hlink, hxy⟩
      rcases hla.eq_and_eq_or_eq_and_eq hlink with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hxy (by rw [hfv, hfa])
      · exact hxy (by rw [hfv, hfa])
  -- Step 2: the crossing-edge count does not increase, via the injection `e_b ↦ e₀`.
  have hcross : (G.crossingEdges f).ncard ≤ (H.crossingEdges f').ncard := by
    -- `f` and `f'` agree away from `v`; `f b = f' b` (since `b ≠ v`).
    have hfb : f b = f' b := hfne b hbv
    refine Set.ncard_le_ncard_of_injOn (fun e => if e = e_b then e₀ else e) ?_ ?_ ?_
    · -- maps crossing edges of `G` to crossing edges of `H`
      rintro e he
      obtain ⟨heG, x, y, hlink, hxy⟩ := id he
      by_cases hev : e = e_b
      · -- `e_b` ↦ `e₀`: `e₀` links `a, b` in `H`, and `f' a ≠ f' b` (since `e_b` crosses).
        simp only [ite_eq_left hev]
        rw [hev] at hlink
        -- The endpoints `{x, y}` of `e_b` are `{v, b}`, so `f x ≠ f y` gives `f' a ≠ f' b`.
        have hab' : f' a ≠ f' b := by
          rcases hlb.eq_and_eq_or_eq_and_eq hlink with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rwa [hfv, hfb] at hxy
          · rw [hfv, hfb] at hxy; exact fun h => hxy h.symm
        have hl₀ : H.IsLink e₀ a b := by
          rw [hH, splitOff_isLink]
          exact Or.inr ⟨rfl, hav, hbv, haV, hbV, Or.inl ⟨rfl, rfl⟩⟩
        exact ⟨hl₀.edge_mem, a, b, hl₀, hab'⟩
      · -- `e ≠ e_b`: `e` avoids `v`, survives in `H`, crosses with the same labels.
        simp only [ite_eq_right hev]
        -- `e` is not incident to `v`: else `e ∈ {eₐ, e_b}` and `eₐ`/`e_b`-incident edges
        -- through `v` get equal labels or contradict `e ≠ e_b`.
        have hxv : x ≠ v ∧ y ≠ v := by
          refine ⟨fun hxv => hxy ?_, fun hyv => hxy ?_⟩
          · -- `x = v`: `e` through `v` is `eₐ` (not `e_b`), so `y = a`; then `f x = f y`.
            subst hxv
            rcases hdeg2 e y hlink with rfl | rfl
            · obtain ⟨_, rfl⟩ | ⟨_, hav'⟩ := hla.eq_and_eq_or_eq_and_eq hlink
              · rw [hfv, hfa]
              · exact absurd hav' hav
            · exact absurd rfl hev
          · -- `y = v`: symmetric.
            subst hyv
            rcases hdeg2 e x hlink.symm with rfl | rfl
            · obtain ⟨_, rfl⟩ | ⟨_, hav'⟩ := hla.eq_and_eq_or_eq_and_eq hlink.symm
              · rw [hfv, hfa]
              · exact absurd hav' hav
            · exact absurd rfl hev
        have hee₀ : e ≠ e₀ := fun h => he₀cross (h ▸ he)
        refine ⟨?_, x, y, ?_, ?_⟩
        · have : H.IsLink e x y := by
            rw [hH, splitOff_isLink]; exact Or.inl ⟨hee₀, hlink, hxv.1, hxv.2⟩
          exact this.edge_mem
        · rw [hH, splitOff_isLink]; exact Or.inl ⟨hee₀, hlink, hxv.1, hxv.2⟩
        · rwa [hfne x hxv.1, hfne y hxv.2] at hxy
    · -- injectivity on `crossingEdges G f`: `g` is identity except `e_b ↦ e₀`, and `e₀` never
      -- crosses `f` (`he₀cross`), so no surviving crossing edge collides with it.
      intro e1 he1 e2 he2 hg
      dsimp only at hg
      by_cases h1 : e1 = e_b <;> by_cases h2 : e2 = e_b
      · rw [h1, h2]
      · rw [ite_eq_left h1, ite_eq_right h2] at hg
        exact absurd (by rw [hg]; exact he2) he₀cross
      · rw [ite_eq_right h1, ite_eq_left h2] at hg
        exact absurd (by rw [← hg]; exact he1) he₀cross
      · rwa [ite_eq_right h1, ite_eq_right h2] at hg
    · exact Set.toFinite _
  -- Combine: `partitionDef_G(f) ≥ partitionDef_H(f')`, then bound by the supremum.
  have hmono : H.partitionDef n f' ≤ G.partitionDef n f := by
    rw [partitionDef, partitionDef, hparts]
    have hD1 : (0 : ℤ) ≤ (bodyBarDim n : ℤ) - 1 := by
      have : (1 : ℤ) ≤ (bodyBarDim n : ℤ) := by exact_mod_cast hD
      linarith
    nlinarith [Int.ofNat_le.mpr hcross]
  exact hmono.trans (G.partitionDef_le_deficiency n f)

/-- **Splitting off does not raise the deficiency** (`lem:splitoff-deficiency`; KT Lemma 4.3(i)):
let `D ≥ 1`, let `eₐ` and `e_b` be the only edges of `G` at `v` (`hdeg2`), joining it to `a, b ≠ v`,
and let the label `e₀` of the new edge not be an edge of `G`. Then `def(G̃_v^{ab}) ≤ def(G̃)`. A
partition `P'` of `V(G) ∖ {v}` extends to one `P` of `V(G)` by adding `v` to the part of `a`, with
`|P| = |P'|`, and the map sending `e_b` to `e₀` and fixing the other edges is injective from the
edges of `G` across `P` to those of `G_v^{ab}` across `P'`. -/
theorem splitOff_deficiency_le [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hD : 1 ≤ bodyBarDim n) {v a b : α} {e₀ eₐ e_b : β}
    (hav : a ≠ v) (hbv : b ≠ v)
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    (he₀ : e₀ ∉ E(G)) :
    (G.splitOff v a b e₀).deficiency n ≤ G.deficiency n :=
  splitOff_deficiency_le_aux hD hav hbv hla hlb hdeg2 (Or.inl he₀)

/-! ### The new edge with the label `eₐ` (`lem:splitoff-deficiency-reuse`)

The upper bound when the new edge `ab` takes the label `eₐ` (`G.splitOff v a b eₐ`), the form in
which the open-ear steps of `main-component.tex` suppress a vertex of degree two
(`sec:main-component-short`). `eₐ` does not join two parts of the extended partition, as its ends
`v` and `a` are in one part, so the proof of `splitOff_deficiency_le` goes through. -/

/-- **Suppressing a vertex of degree two** (`lem:splitoff-deficiency-reuse`): under the hypotheses
of `splitOff_deficiency_le`, with the label `eₐ` for the new edge, `def(G̃'') ≤ def(G̃)`, where
`G'' = G.splitOff v a b eₐ` is `G` with the end `v` of `eₐ` replaced by `b`, and with `v` and `e_b`
deleted. It is the case `e₀ = eₐ` of `splitOff_deficiency_le_aux`. -/
theorem splitOff_deficiency_le_of_eq_left [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hD : 1 ≤ bodyBarDim n) {v a b : α} {eₐ e_b : β}
    (hav : a ≠ v) (hbv : b ≠ v)
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b) :
    (G.splitOff v a b eₐ).deficiency n ≤ G.deficiency n :=
  splitOff_deficiency_le_aux hD hav hbv hla hlb hdeg2 (Or.inr rfl)

/-! ### Splitting off with a gap in the merged deficiency (`lem:splitoff-deficiency-merged`)

The open-ear steps of `main-component.tex` at non-adjacent ends use this bound
(`sec:main-component-orbit`). Let `G' = G[V(G) ∖ {v}]`, and let `H` be `G` split off at `v` with the
label `e₀`, all of whose links in `G` are at `v`. Then `H` is `G'` with one more edge `e₀` joining
`a` and `b`. A partition that separates `a` and `b` has one more edge across it in `H` than in `G'`,
so its value drops by `D - 1`; one with `a` and `b` in one part has value at most the merged
deficiency (`deficiencyMerged`). -/

/-- **Splitting off with a gap in the merged deficiency** (`lem:splitoff-deficiency-merged`): let
`D ≥ 1`, let `a, b ≠ v` be vertices of `G`, let every link of `e₀` in `G` be at `v` (`he₀`), and let
`V₁ = V(G) ∖ {v}`, `G' = G[V₁]` and `H = G.splitOff v a b e₀`. If the merged deficiency of `G'` at
`a` and `b` is at most `def(G̃') - (D - 1)` (`hδ`), then so is `def(H̃)`. -/
theorem splitOff_deficiency_add_le_of_deficiencyMerged [Finite α] [Finite β] {G : Graph α β}
    {n : ℕ} (hD : 1 ≤ bodyBarDim n) {V₁ : Set α} {v a b : α} {e₀ : β} (hV₁ : V(G) \ {v} = V₁)
    (hav : a ≠ v) (hbv : b ≠ v) (haV : a ∈ V(G)) (hbV : b ∈ V(G))
    (he₀ : ∀ x y, G.IsLink e₀ x y → x = v ∨ y = v)
    (hδ : (G.induce V₁).deficiencyMerged n a b + ((bodyBarDim n : ℤ) - 1) ≤
      (G.induce V₁).deficiency n) :
    (G.splitOff v a b e₀).deficiency n + ((bodyBarDim n : ℤ) - 1) ≤ (G.induce V₁).deficiency n := by
  set H := G.splitOff v a b e₀ with hH
  set G' := G.induce V₁ with hG'
  have hVH : V(H) = V(G') := by rw [hH, vertexSet_splitOff, hV₁]; rfl
  have hne : Nonempty (α → α) := ⟨id⟩
  -- every link of `G'` is a link of `H`, and `e₀` is not an edge of `G'`
  have hle : ∀ f x y, G'.IsLink f x y → H.IsLink f x y := by
    rintro f x y ⟨hf, hx, hy⟩
    have hxv : x ≠ v := fun h => by rw [← hV₁] at hx; exact hx.2 h
    have hyv : y ≠ v := fun h => by rw [← hV₁] at hy; exact hy.2 h
    refine Or.inl ⟨?_, hf, hxv, hyv⟩
    rintro rfl
    rcases he₀ x y hf with h | h
    exacts [hxv h, hyv h]
  have he₀G' : e₀ ∉ E(G') := by
    intro h
    obtain ⟨x, y, hl⟩ := G'.exists_isLink_of_mem_edgeSet h
    obtain ⟨hf, hx, hy⟩ := hl
    rw [← hV₁] at hx hy
    rcases he₀ x y hf with h | h
    exacts [hx.2 h, hy.2 h]
  rw [deficiency]
  have hsup : ∀ f : α → α, H.partitionDef n f + ((bodyBarDim n : ℤ) - 1) ≤ G'.deficiency n := by
    intro f
    have hnp : H.numParts f = G'.numParts f := by rw [numParts, numParts, hVH]
    have hsub : G'.crossingEdges f ⊆ H.crossingEdges f := by
      rintro f' ⟨hf', x, y, hl, hxy⟩
      exact ⟨(hle f' x y hl).edge_mem, x, y, hle f' x y hl, hxy⟩
    have hDn : (0 : ℤ) ≤ (bodyBarDim n : ℤ) - 1 := by
      have : (1 : ℤ) ≤ bodyBarDim n := by exact_mod_cast hD
      linarith
    by_cases hab : f a = f b
    · have h1 : (G'.crossingEdges f).ncard ≤ (H.crossingEdges f).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
      have h2 := G'.partitionDef_le_deficiencyMerged n hab
      have h3 : H.partitionDef n f ≤ G'.partitionDef n f := by
        rw [partitionDef, partitionDef, hnp]
        have : ((G'.crossingEdges f).ncard : ℤ) ≤ (H.crossingEdges f).ncard := by exact_mod_cast h1
        nlinarith
      linarith
    · -- `e₀` crosses in `H`
      have hvab : a ≠ v ∧ b ≠ v ∧ a ∈ V(G) ∧ b ∈ V(G) := ⟨hav, hbv, haV, hbV⟩
      · have he₀H : e₀ ∈ H.crossingEdges f :=
          ⟨(show H.IsLink e₀ a b from Or.inr ⟨rfl, hvab.1, hvab.2.1, hvab.2.2.1, hvab.2.2.2,
            Or.inl ⟨rfl, rfl⟩⟩).edge_mem, a, b,
            Or.inr ⟨rfl, hvab.1, hvab.2.1, hvab.2.2.1, hvab.2.2.2, Or.inl ⟨rfl, rfl⟩⟩, hab⟩
        have hnot : e₀ ∉ G'.crossingEdges f := fun h => he₀G' h.1
        have h1 : (G'.crossingEdges f).ncard + 1 ≤ (H.crossingEdges f).ncard := by
          rw [← Set.ncard_insert_of_notMem hnot (Set.toFinite _)]
          exact Set.ncard_le_ncard (Set.insert_subset he₀H hsub) (Set.toFinite _)
        have h2 := G'.partitionDef_le_deficiency n f
        rw [partitionDef] at h2 ⊢
        rw [hnp]
        have : ((G'.crossingEdges f).ncard : ℤ) + 1 ≤ (H.crossingEdges f).ncard := by
          exact_mod_cast h1
        nlinarith
  exact (ciSup_le fun f => by linarith [hsup f] : ⨆ f, H.partitionDef n f ≤
    G'.deficiency n - ((bodyBarDim n : ℤ) - 1)) |> fun h => by linarith

/-! ### Splitting off lowers the deficiency by at most one (`lem:splitoff-deficiency`)

The lower bound `def(G̃) - 1 ≤ def(G̃_v^{ab})` of KT Lemma 4.3(i), with which `G_v^{ab}` is a
`k`-dof-graph or a `(k - 1)`-dof-graph when `G` is a `k`-dof-graph. Take a partition `f` of `V(G)`
of value `def(G̃)` (`exists_eq_ciSup_of_finite`), and the same labels on `V(G) ∖ {v}`. If another
vertex has the label of `v`, the number of parts is unchanged, and the edges across do not increase,
as the new edge `ab` crosses only if `eₐ` or `e_b` does. If `v` is alone in its part, there is one
part fewer, and both `eₐ` and `e_b` cross while `ab` replaces at most one of them, so the value
drops by at most `D - (D - 1) = 1`. -/

/-- **Splitting off lowers the deficiency by at most one** (`lem:splitoff-deficiency`; KT
Lemma 4.3(i)): let `D ≥ 1`, let edges `eₐ ≠ e_b` of `G` join `v` to `a, b ≠ v`, and let the label
`e₀` of the new edge not be an edge of `G`. Then `def(G̃) - 1 ≤ def(G̃_v^{ab})`. With
`splitOff_deficiency_le`, `G_v^{ab}` is a `k`-dof-graph or a `(k - 1)`-dof-graph when `G` is a
`k`-dof-graph. The proof compares partitions as above. -/
theorem splitOff_deficiency_ge [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hD : 1 ≤ bodyBarDim n) {v a b : α} {e₀ eₐ e_b : β}
    (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b)
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b) (he₀ : e₀ ∉ E(G)) :
    G.deficiency n - 1 ≤ (G.splitOff v a b e₀).deficiency n := by
  classical
  set H := G.splitOff v a b e₀ with hH
  have haV : a ∈ V(G) := hla.right_mem
  have hbV : b ∈ V(G) := hlb.right_mem
  have hD1 : (0 : ℤ) ≤ (bodyBarDim n : ℤ) - 1 := by
    have : (1 : ℤ) ≤ (bodyBarDim n : ℤ) := by exact_mod_cast hD
    linarith
  -- Pick a partition `f` of `V(G)` attaining `def(G̃)` (finite supremum).
  have : Nonempty α := ⟨a⟩
  obtain ⟨f, hf⟩ := exists_eq_ciSup_of_finite (f := G.partitionDef n)
  rw [deficiency, ← hf]
  -- It suffices to bound the same labeling `f` (restricted to `V(H) = V(G) ∖ {v}`) below.
  refine le_trans ?_ (H.partitionDef_le_deficiency n f)
  -- `eₐ`, `e_b ∈ E(G)`, and both differ from `e₀`.
  have heaG : eₐ ∈ E(G) := hla.edge_mem
  have hebG : e_b ∈ E(G) := hlb.edge_mem
  have heae₀ : eₐ ≠ e₀ := fun h => he₀ (h ▸ heaG)
  have hebe₀ : e_b ≠ e₀ := fun h => he₀ (h ▸ hebG)
  -- `eₐ`, `e_b` are dropped by the splitting-off (they are `v`-incident), so `∉ E(H)`.
  have heaH : eₐ ∉ E(H) := by
    rw [hH, edgeSet_splitOff]
    rintro (⟨h, _⟩ | ⟨_, x, y, hl, hxv, hyv⟩)
    · exact heae₀ h
    · rcases hla.eq_and_eq_or_eq_and_eq hl with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact hxv rfl
      · exact hyv rfl
  have hebH : e_b ∉ E(H) := by
    rw [hH, edgeSet_splitOff]
    rintro (⟨h, _⟩ | ⟨_, x, y, hl, hxv, hyv⟩)
    · exact hebe₀ h
    · rcases hlb.eq_and_eq_or_eq_and_eq hl with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact hxv rfl
      · exact hyv rfl
  by_cases hshared : ∃ w ∈ V(G), w ≠ v ∧ f w = f v
  · -- Case: `v`'s label `f v` is shared, so `|P|` is unchanged.
    have hparts : H.numParts f = G.numParts f := by
      obtain ⟨w, hwV, hwv, hfw⟩ := hshared
      rw [numParts, numParts, vertexSet_splitOff]
      congr 1
      apply Set.Subset.antisymm
      · rintro _ ⟨x, hx, rfl⟩; exact ⟨x, hx.1, rfl⟩
      · rintro _ ⟨x, hx, rfl⟩
        by_cases hxv : x = v
        · exact ⟨w, ⟨hwV, by simpa using hwv⟩, by rw [hfw, hxv]⟩
        · exact ⟨x, ⟨hx, by simpa using hxv⟩, rfl⟩
    -- Crossing edges of `H` inject into crossing edges of `G` (`e₀ ↦` a crossing `v`-edge).
    have hcross : (H.crossingEdges f).ncard ≤ (G.crossingEdges f).ncard := by
      refine Set.ncard_le_ncard_of_injOn
        (fun e => if e = e₀ then (if f v = f a then e_b else eₐ) else e) ?_ ?_ (Set.toFinite _)
      · rintro e ⟨heH, x, y, hlink, hxy⟩
        by_cases hee₀ : e = e₀
        · -- `e₀` crosses `f`: its endpoints are `a, b`, so `f a ≠ f b`.
          rw [hH, splitOff_isLink] at hlink
          rcases hlink with ⟨hne, _⟩ | ⟨_, _, _, _, _, hxy'⟩
          · exact absurd hee₀ hne
          have hab : f a ≠ f b := by
            rcases hxy' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hxy
            · exact fun h => hxy h.symm
          simp only [ite_eq_left hee₀]
          by_cases hfva : f v = f a
          · -- map to `e_b`: `e_b` links `v, b`, `f v = f a ≠ f b`, so `e_b` crosses.
            simp only [ite_eq_left hfva]
            exact ⟨hebG, v, b, hlb, by rw [hfva]; exact hab⟩
          · -- map to `eₐ`: `eₐ` links `v, a`, `f v ≠ f a`, so `eₐ` crosses.
            simp only [ite_eq_right hfva]
            exact ⟨heaG, v, a, hla, hfva⟩
        · simp only [ite_eq_right hee₀]
          rw [hH, splitOff_isLink] at hlink
          rcases hlink with ⟨_, hl, _, _⟩ | ⟨rfl, _⟩
          · exact ⟨hl.edge_mem, x, y, hl, hxy⟩
          · exact absurd rfl hee₀
      · -- injectivity: identity off `e₀`; `e₀ ↦ eₐ`/`e_b ∉ E(H)`, so no surviving edge hits it.
        intro e1 he1 e2 he2 hg
        dsimp only at hg
        -- A surviving crossing edge of `H` lies in `E(H)`, hence is neither `eₐ` nor `e_b`.
        have hne : ∀ {e}, e ∈ H.crossingEdges f → e ≠ e₀ →
            e ≠ (if f v = f a then e_b else eₐ) := by
          rintro e ⟨heH, -⟩ - rfl
          by_cases hfva : f v = f a
          · rw [ite_eq_left hfva] at heH; exact hebH heH
          · rw [ite_eq_right hfva] at heH; exact heaH heH
        by_cases h1 : e1 = e₀ <;> by_cases h2 : e2 = e₀
        · rw [h1, h2]
        · rw [ite_eq_left h1, ite_eq_right h2] at hg; exact absurd hg.symm (hne he2 h2)
        · rw [ite_eq_right h1, ite_eq_left h2] at hg; exact absurd hg (hne he1 h1)
        · rwa [ite_eq_right h1, ite_eq_right h2] at hg
    rw [partitionDef, partitionDef, hparts]
    nlinarith [Int.ofNat_le.mpr hcross]
  · -- Case: `v` is isolated in its part (`f v` carried only by `v`).
    push Not at hshared
    -- `|P|` drops by exactly `1`: `f '' V(G) = insert (f v) (f '' V(H))`, `f v ∉ f '' V(H)`.
    have hfv_notin : f v ∉ f '' V(H) := by
      rintro ⟨w, hwV, hfw⟩
      rw [hH, vertexSet_splitOff] at hwV
      exact hshared w hwV.1 (by simpa using hwV.2) hfw
    have hvV : v ∈ V(G) := hla.left_mem
    have himg : f '' V(G) = insert (f v) (f '' V(H)) := by
      rw [hH, vertexSet_splitOff]
      apply Set.Subset.antisymm
      · rintro _ ⟨x, hx, rfl⟩
        by_cases hxv : x = v
        · exact Set.mem_insert_iff.mpr (Or.inl (by rw [hxv]))
        · exact Set.mem_insert_iff.mpr (Or.inr ⟨x, ⟨hx, by simpa using hxv⟩, rfl⟩)
      · rintro _ (rfl | ⟨x, hx, rfl⟩)
        · exact ⟨v, hvV, rfl⟩
        · exact ⟨x, hx.1, rfl⟩
    have hparts : (G.numParts f : ℤ) = (H.numParts f : ℤ) + 1 := by
      rw [numParts, numParts, himg, Set.ncard_insert_of_notMem hfv_notin (Set.toFinite _)]
      push_cast; ring
    -- `eₐ`, `e_b` both cross `f` (since `f a ≠ f v` and `f b ≠ f v`), and `eₐ ∉ E(H)`.
    have hfav : f a ≠ f v := hshared a haV hav
    have hfbv : f b ≠ f v := hshared b hbV hbv
    have hea_cross : eₐ ∈ G.crossingEdges f := ⟨heaG, v, a, hla, fun h => hfav h.symm⟩
    have heb_cross : e_b ∈ G.crossingEdges f := ⟨hebG, v, b, hlb, fun h => hfbv h.symm⟩
    -- Crossing edges of `H` inject into crossing edges of `G` *minus* `eₐ`: drop by ≥ 1.
    have hcross : (H.crossingEdges f).ncard + 1 ≤ (G.crossingEdges f).ncard := by
      have hsub : insert eₐ ((fun e => if e = e₀ then e_b else e) '' H.crossingEdges f)
          ⊆ G.crossingEdges f := by
        rintro e (rfl | ⟨e', he', rfl⟩)
        · exact hea_cross
        · obtain ⟨heH', x, y, hlink, hxy⟩ := he'
          by_cases hee₀ : e' = e₀
          · -- `e₀` crosses ⟹ `f a ≠ f b` ⟹ `e_b` crosses (map `e₀ ↦ e_b`).
            simp only [ite_eq_left hee₀]
            rw [hH, splitOff_isLink, hee₀] at hlink
            rcases hlink with ⟨hne, _⟩ | ⟨_, _, _, _, _, hxy'⟩
            · exact absurd rfl hne
            exact heb_cross
          · simp only [ite_eq_right hee₀]
            rw [hH, splitOff_isLink] at hlink
            rcases hlink with ⟨_, hl, _, _⟩ | ⟨rfl, _⟩
            · exact ⟨hl.edge_mem, x, y, hl, hxy⟩
            · exact absurd rfl hee₀
      have hinj : Set.InjOn (fun e => if e = e₀ then e_b else e) (H.crossingEdges f) := by
        intro e1 he1 e2 he2 hg
        dsimp only at hg
        have hne : ∀ {e}, e ∈ H.crossingEdges f → e ≠ e₀ → e ≠ e_b := by
          rintro e ⟨heH, -⟩ - rfl; exact hebH heH
        by_cases h1 : e1 = e₀ <;> by_cases h2 : e2 = e₀
        · rw [h1, h2]
        · rw [ite_eq_left h1, ite_eq_right h2] at hg; exact absurd hg.symm (hne he2 h2)
        · rw [ite_eq_right h1, ite_eq_left h2] at hg; exact absurd hg (hne he1 h1)
        · rwa [ite_eq_right h1, ite_eq_right h2] at hg
      have hnotmem : eₐ ∉ (fun e => if e = e₀ then e_b else e) '' H.crossingEdges f := by
        rintro ⟨e', he', hg⟩
        dsimp only at hg
        by_cases hee₀ : e' = e₀
        · rw [ite_eq_left hee₀] at hg; exact heab hg.symm
        · rw [ite_eq_right hee₀] at hg; exact heaH (hg ▸ he'.1)
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_insert_of_notMem hnotmem (Set.toFinite _), hinj.ncard_image] at this
      omega
    rw [partitionDef, partitionDef]
    have : (G.numParts f : ℤ) = (H.numParts f : ℤ) + 1 := hparts
    nlinarith [Int.ofNat_le.mpr hcross, this]

/-! ### Removal does not lower the deficiency (`lem:removal-deficiency`)

The bound `def(G̃) ≤ def(G̃_v)` of KT Lemma 4.4 (p. 662), without forests; Katoh and Tanigawa prove
it with forests (`rem:kt-lemma-44`). Take a partition `f` of `V(G)` of value `def(G̃)` and the same
labels on `V(G) ∖ {v}`. The edges of `G_v` across it are those of `G` across it other than `eₐ` and
`e_b`, so `c ∈ {0, 1, 2}` fewer edges cross. If another vertex has the label of `v`, the number of
parts is unchanged, and the value rises by `(D - 1)c`. If `v` is alone in its part, there is one
part fewer, but `a` and `b` are in other parts, so `c = 2`, and the value rises by
`2(D - 1) - D = D - 2 ≥ 0`, as `D ≥ 2`. -/

/-- **Removal does not lower the deficiency** (`lem:removal-deficiency`; KT Lemma 4.4, p. 662): let
`D ≥ 2`, and let the distinct edges `eₐ` and `e_b` be the only edges of `G` at `v` (`hdeg2`),
joining it to `a, b ≠ v`. Then `def(G̃) ≤ def(G̃_v)`; so if `G` is a `k`-dof-graph, `def(G̃_v) ≥ k`.
The proof compares partitions as above. -/
theorem removeVertex_deficiency_ge [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hD : 2 ≤ bodyBarDim n) {v a b : α} {eₐ e_b : β}
    (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b)
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b) :
    G.deficiency n ≤ (G.removeVertex v).deficiency n := by
  classical
  set H := G.removeVertex v with hH
  have haV : a ∈ V(G) := hla.right_mem
  have hbV : b ∈ V(G) := hlb.right_mem
  have hD1 : (0 : ℤ) ≤ (bodyBarDim n : ℤ) - 1 := by
    have : (1 : ℤ) ≤ (bodyBarDim n : ℤ) := by exact_mod_cast (le_trans (by norm_num) hD)
    linarith
  -- Pick a partition `f` of `V(G)` attaining `def(G̃)` (finite supremum).
  have : Nonempty α := ⟨a⟩
  obtain ⟨f, hf⟩ := exists_eq_ciSup_of_finite (f := G.partitionDef n)
  rw [deficiency, ← hf]
  -- It suffices to bound the same labeling `f` on `V(H) = V(G) ∖ {v}` below.
  refine le_trans ?_ (H.partitionDef_le_deficiency n f)
  have heaG : eₐ ∈ E(G) := hla.edge_mem
  have hebG : e_b ∈ E(G) := hlb.edge_mem
  -- The crossing edges of `H = Gᵥ` inject into those of `G`: identity, surviving `v`-free.
  have hcross_sub : H.crossingEdges f ⊆ G.crossingEdges f := by
    rintro e ⟨heH, x, y, hlink, hxy⟩
    rw [hH, removeVertex_isLink] at hlink
    exact ⟨hlink.1.edge_mem, x, y, hlink.1, hxy⟩
  -- A crossing edge of `G` that is **not** a crossing edge of `H` must be `v`-incident,
  -- hence `eₐ` or `e_b` (`hdeg2`).
  have hcross_diff : ∀ {e}, e ∈ G.crossingEdges f → e ∉ H.crossingEdges f →
      e = eₐ ∨ e = e_b := by
    rintro e ⟨heG, x, y, hlink, hxy⟩ hnotH
    by_cases hxv : x = v
    · subst hxv; exact hdeg2 e y hlink
    · by_cases hyv : y = v
      · subst hyv; exact hdeg2 e x hlink.symm
      · have hlinkH : H.IsLink e x y := by rw [hH, removeVertex_isLink]; exact ⟨hlink, hxv, hyv⟩
        exact absurd ⟨hlinkH.edge_mem, x, y, hlinkH, hxy⟩ hnotH
  by_cases hshared : ∃ w ∈ V(G), w ≠ v ∧ f w = f v
  · -- Case: `v`'s label `f v` is shared, so `|P|` is unchanged. Crossing count does not
    -- increase (`hcross_sub`), so the per-partition deficiency does not decrease.
    have hparts : H.numParts f = G.numParts f := by
      obtain ⟨w, hwV, hwv, hfw⟩ := hshared
      rw [numParts, numParts, hH, vertexSet_removeVertex]
      congr 1
      apply Set.Subset.antisymm
      · rintro _ ⟨x, hx, rfl⟩; exact ⟨x, hx.1, rfl⟩
      · rintro _ ⟨x, hx, rfl⟩
        by_cases hxv : x = v
        · exact ⟨w, ⟨hwV, by simpa using hwv⟩, by rw [hfw, hxv]⟩
        · exact ⟨x, ⟨hx, by simpa using hxv⟩, rfl⟩
    have hcross : (H.crossingEdges f).ncard ≤ (G.crossingEdges f).ncard :=
      Set.ncard_le_ncard hcross_sub (Set.toFinite _)
    rw [partitionDef, partitionDef, hparts]
    nlinarith [Int.ofNat_le.mpr hcross]
  · -- Case: `v` is isolated in its part (`f v` carried only by `v`).
    push Not at hshared
    -- `|P|` drops by exactly `1`: `f '' V(G) = insert (f v) (f '' V(H))`, `f v ∉ f '' V(H)`.
    have hfv_notin : f v ∉ f '' V(H) := by
      rintro ⟨w, hwV, hfw⟩
      rw [hH, vertexSet_removeVertex] at hwV
      exact hshared w hwV.1 (by simpa using hwV.2) hfw
    have hvV : v ∈ V(G) := hla.left_mem
    have himg : f '' V(G) = insert (f v) (f '' V(H)) := by
      rw [hH, vertexSet_removeVertex]
      apply Set.Subset.antisymm
      · rintro _ ⟨x, hx, rfl⟩
        by_cases hxv : x = v
        · exact Set.mem_insert_iff.mpr (Or.inl (by rw [hxv]))
        · exact Set.mem_insert_iff.mpr (Or.inr ⟨x, ⟨hx, by simpa using hxv⟩, rfl⟩)
      · rintro _ (rfl | ⟨x, hx, rfl⟩)
        · exact ⟨v, hvV, rfl⟩
        · exact ⟨x, hx.1, rfl⟩
    have hparts : (G.numParts f : ℤ) = (H.numParts f : ℤ) + 1 := by
      rw [numParts, numParts, himg, Set.ncard_insert_of_notMem hfv_notin (Set.toFinite _)]
      push_cast; ring
    -- `eₐ`, `e_b` both cross `f` (since `f a ≠ f v` and `f b ≠ f v`), but are not crossing
    -- edges of `H` (they are `v`-incident, dropped by `removeVertex`).
    have hfav : f a ≠ f v := hshared a haV hav
    have hfbv : f b ≠ f v := hshared b hbV hbv
    have hea_cross : eₐ ∈ G.crossingEdges f := ⟨heaG, v, a, hla, fun h => hfav h.symm⟩
    have heb_cross : e_b ∈ G.crossingEdges f := ⟨hebG, v, b, hlb, fun h => hfbv h.symm⟩
    have hea_notH : eₐ ∉ H.crossingEdges f := by
      rintro ⟨heH, x, y, hlink, _⟩
      rw [hH, removeVertex_isLink] at hlink
      rcases hla.eq_and_eq_or_eq_and_eq hlink.1 with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact hlink.2.1 rfl
      · exact hlink.2.2 rfl
    have heb_notH : e_b ∉ H.crossingEdges f := by
      rintro ⟨heH, x, y, hlink, _⟩
      rw [hH, removeVertex_isLink] at hlink
      rcases hlb.eq_and_eq_or_eq_and_eq hlink.1 with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact hlink.2.1 rfl
      · exact hlink.2.2 rfl
    -- Crossing count drops by ≥ 2: `H.crossingEdges f ∪ {eₐ, e_b} ⊆ G.crossingEdges f`,
    -- with `eₐ ≠ e_b` and both `∉ H.crossingEdges f`.
    have hcross : (H.crossingEdges f).ncard + 2 ≤ (G.crossingEdges f).ncard := by
      have hsub : insert eₐ (insert e_b (H.crossingEdges f)) ⊆ G.crossingEdges f := by
        rintro e (rfl | rfl | he)
        · exact hea_cross
        · exact heb_cross
        · exact hcross_sub he
      have hbnotin : e_b ∉ H.crossingEdges f := heb_notH
      have hanotin : eₐ ∉ insert e_b (H.crossingEdges f) := by
        rw [Set.mem_insert_iff]; push Not; exact ⟨heab, hea_notH⟩
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      rwa [Set.ncard_insert_of_notMem hanotin (Set.toFinite _),
        Set.ncard_insert_of_notMem hbnotin (Set.toFinite _)] at this
    rw [partitionDef, partitionDef]
    nlinarith [Int.ofNat_le.mpr hcross, hparts]

/-! ### The deficiency after splitting off and after removal (`lem:dof-tracking`) -/

/-- **The deficiency after splitting off and after removal** (`lem:dof-tracking`; KT Lemmas 4.3(i)
and 4.4): let `D ≥ 2`, let the distinct edges `eₐ` and `e_b` be the only edges of `G` at `v`,
joining it to `a, b ≠ v`, and let `e₀ ∉ E(G)`. Then
`def(G̃) - 1 ≤ def(G̃_v^{ab}) ≤ def(G̃) ≤ def(G̃_v)`, by `splitOff_deficiency_ge`,
`splitOff_deficiency_le` and `removeVertex_deficiency_ge`. -/
theorem dof_tracking [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hD : 2 ≤ bodyBarDim n) {v a b : α} {e₀ eₐ e_b : β}
    (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b)
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    (he₀ : e₀ ∉ E(G)) :
    G.deficiency n - 1 ≤ (G.splitOff v a b e₀).deficiency n ∧
      (G.splitOff v a b e₀).deficiency n ≤ G.deficiency n ∧
      G.deficiency n ≤ (G.removeVertex v).deficiency n :=
  have hD1 : 1 ≤ bodyBarDim n := le_trans (by norm_num) hD
  ⟨splitOff_deficiency_ge hD1 hav hbv heab hla hlb he₀,
    splitOff_deficiency_le hD1 hav hbv hla hlb hdeg2 he₀,
    removeVertex_deficiency_ge hD hav hbv heab hla hlb hdeg2⟩

end Graph
