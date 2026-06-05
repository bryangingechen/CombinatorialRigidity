/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Induction.Operations

/-!
# The combinatorial induction — deficiency tracking under the operations (`sec:molecular-induction`)

Phase 20 (molecular-conjecture program; see `notes/MolecularConjecture.md`). On top of the graph
operations (`Induction/Operations`), this file tracks how the `D`-deficiency moves under
splitting-off and vertex removal (Katoh–Tanigawa 2011 §4):

* **splitting-off does not increase the deficiency** and lowers it by at most one
  (`splitOff_deficiency_le` / `splitOff_deficiency_ge`, `lem:splitoff-deficiency`; KT 4.3(ii));
* **vertex removal raises the deficiency** (`removeVertex_deficiency_ge`, `lem:removal-deficiency`;
  KT Lemma 4.4);
* the combined degrees-of-freedom bookkeeping (`dof_tracking`, `lem:dof-tracking`; KT 4.3–4.5).

The reducible-vertex, contraction-minimality, and forest-surgery layers build on top in
`ReducibleVertex`, `Contraction`, and `ForestSurgery`. See `ROADMAP.md` §20 / `notes/Phase20.md`
and the `sec:molecular-induction` dep-graph.
-/

namespace Graph

open Set Matroid

variable {α β : Type*}

/-! ## Splitting-off does not increase the deficiency (`lem:splitoff-deficiency`)

The substantive splitting-off fact the combinatorial induction consumes (Katoh–Tanigawa
2011 Lemma 4.3(i)), established directly via the **deficiency-count route** that bypasses
the forest surgery of `lem:forest-surgery-split` (see `rem:kt-lemma-41` /
`notes/Phase20.md` *Replan*). For a degree-2 vertex `v` of `G` with neighbours `a, b`,
splitting-off `G_v^{ab}` does not increase the deficiency: `def(G̃_v^{ab}) ≤ def(G̃)`.

The proof is a per-partition comparison on the green `deficiency` infrastructure of
`Molecular/Deficiency.lean`, *no forests*. Take any partition `P'` of
`V(G_v^{ab}) = V(G) ∖ {v}` and extend it to a partition `P` of `V(G)` by dropping `v`
into `a`'s block (`f = update f' v (f' a)`). Then `|P| = |P'|` (the label of `v`, `f' a`,
is already carried by `a ∈ V(G) ∖ {v}`), and the crossing-edge count does not increase:
the `va`-edge no longer crosses `P` (both endpoints carry `f' a`), the `vb`-edge crosses
`P` exactly when the short-circuit `e₀ = ab` crosses `P'`, and every other edge survives
verbatim with the same crossing status. So `def_{G̃}(P) ≥ def_{G̃_v^{ab}}(P')`, and taking
`P'` over the supremum gives `def(G̃) ≥ def(G̃_v^{ab})`. -/

/-- **Splitting-off does not increase the deficiency** (`lem:splitoff-deficiency`,
KT Lemma 4.3(i)). Let `v` be a degree-2 vertex of `G` with neighbours `a, b`, carried by
two distinct edges `eₐ` (joining `v, a`) and `e_b` (joining `v, b`) that are the *only*
edges of `G` incident to `v` (`hdeg2`), with `a, b ≠ v`. With the short-circuit label
`e₀` fresh (`e₀ ∉ E(G)`), the splitting-off `G_v^{ab}` satisfies
`def(G̃_v^{ab}) ≤ def(G̃)`.

Proved by the deficiency-count route (no forest surgery): each partition `P'` of
`V(G) ∖ {v}` extends to a partition `P` of `V(G)` (drop `v` into `a`'s block) with
`|P| = |P'|` and `d_G(P) ≤ d_{G_v^{ab}}(P')`, via the crossing-edge injection
`e_b ↦ e₀`, identity elsewhere. See `rem:kt-lemma-41` and `notes/Phase20.md` for why this
replaces KT's forest surgery (`lem:forest-surgery-split`). -/
theorem splitOff_deficiency_le [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hD : 1 ≤ bodyBarDim n) {v a b : α} {e₀ eₐ e_b : β}
    (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b)
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    (he₀ : e₀ ∉ E(G)) :
    (G.splitOff v a b e₀).deficiency n ≤ G.deficiency n := by
  classical
  set H := G.splitOff v a b e₀ with hH
  have haV : a ∈ V(G) := hla.right_mem
  have hbV : b ∈ V(G) := hlb.right_mem
  -- It suffices to bound each partition `P'` of `H` by `def(G̃)`.
  haveI : Nonempty α := ⟨a⟩
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
  -- Step 2: the crossing-edge count does not increase, via the injection `e_b ↦ e₀`.
  have hcross : (G.crossingEdges f).ncard ≤ (H.crossingEdges f').ncard := by
    -- `f` and `f'` agree away from `v`; `f v = f' a` and `f b = f' b` (since `b ≠ v`).
    have hfb : f b = f' b := hfne b hbv
    have hfa : f a = f' a := hfne a hav
    refine Set.ncard_le_ncard_of_injOn (fun e => if e = e_b then e₀ else e) ?_ ?_ ?_
    · -- maps crossing edges of `G` to crossing edges of `H`
      rintro e ⟨heG, x, y, hlink, hxy⟩
      by_cases hev : e = e_b
      · -- `e_b` ↦ `e₀`: `e₀` links `a, b` in `H`, and `f' a ≠ f' b` (since `e_b` crosses).
        simp only [if_pos hev]
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
        simp only [if_neg hev]
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
        have hee₀ : e ≠ e₀ := fun h => he₀ (h ▸ heG)
        refine ⟨?_, x, y, ?_, ?_⟩
        · have : H.IsLink e x y := by
            rw [hH, splitOff_isLink]; exact Or.inl ⟨hee₀, hlink, hxv.1, hxv.2⟩
          exact this.edge_mem
        · rw [hH, splitOff_isLink]; exact Or.inl ⟨hee₀, hlink, hxv.1, hxv.2⟩
        · rwa [hfne x hxv.1, hfne y hxv.2] at hxy
    · -- injectivity on `crossingEdges G f`: `g` is identity except `e_b ↦ e₀ ∉ E(G)`.
      intro e1 he1 e2 he2 hg
      dsimp only at hg
      have hmemG : ∀ {e}, e ∈ G.crossingEdges f → e ∈ E(G) := fun h => h.1
      by_cases h1 : e1 = e_b <;> by_cases h2 : e2 = e_b
      · rw [h1, h2]
      · -- `g e1 = e₀ = e2`, but `e2 ∈ E(G)` and `e₀ ∉ E(G)`.
        rw [if_pos h1, if_neg h2] at hg
        exact absurd (hg ▸ hmemG he2) he₀
      · rw [if_neg h1, if_pos h2] at hg
        exact absurd (hg.symm ▸ hmemG he1) he₀
      · rwa [if_neg h1, if_neg h2] at hg
    · exact Set.toFinite _
  -- Combine: `partitionDef_G(f) ≥ partitionDef_H(f')`, then bound by the supremum.
  have hmono : H.partitionDef n f' ≤ G.partitionDef n f := by
    rw [partitionDef, partitionDef, hparts]
    have hD1 : (0 : ℤ) ≤ (bodyBarDim n : ℤ) - 1 := by
      have : (1 : ℤ) ≤ (bodyBarDim n : ℤ) := by exact_mod_cast hD
      linarith
    nlinarith [Int.ofNat_le.mpr hcross]
  exact hmono.trans (G.partitionDef_le_deficiency n f)

/-! ### Splitting-off lowers the deficiency by at most one (`lem:splitoff-deficiency`, KT 4.3(ii))

The companion lower bound to `splitOff_deficiency_le`: splitting-off at a degree-2 vertex
`v` drops the deficiency by at most `1`, `def(G̃_v^{ab}) ≥ def(G̃) − 1`. Combined with the
upper bound `def(G̃_v^{ab}) ≤ def(G̃)` (`splitOff_deficiency_le`), this pins
`def(G̃_v^{ab}) ∈ {def(G̃), def(G̃) − 1}` — the "`G_v^{ab}` is a `k`-dof-graph or a
`(k−1)`-dof-graph" alternative of KT Lemma 4.3(i)/(ii). The dof-tracking assembly
(`lem:dof-tracking`) consumes this two-sided bound; the matroid-base characterization of
*which* of the two holds (`∃` base `B'` with `|ã̃b ∩ B'| < D − 1`) is KT's reading via the
deferred forest surgery (`rem:kt-lemma-41`) and is not needed for Theorem 4.9.

The proof is again a per-partition deficiency-count comparison, *no forests*, dual to
`splitOff_deficiency_le`: take a partition `f` of `V(G)` attaining `def(G̃)` (finite
supremum, `exists_eq_ciSup_of_finite`), reuse the *same* labeling on `V(G) ∖ {v}`, and
case-split on whether `v`'s label is shared by another vertex.
* If `v`'s label is shared, `|P|` is unchanged and the crossing count does not increase
  (the `va`/`vb` edges leaving and the short-circuit `ab` entering crosses at most as
  often), so `def_{G̃_v^{ab}}(P) ≥ def_{G̃}(P) = def(G̃)`.
* If `v` is isolated in its part, `|P|` drops by exactly `1` and the crossing count drops
  by at least `1` (both `va`, `vb` left, `ab` enters), so `def_{G̃_v^{ab}}(P) ≥
  D(|P| − 2) − (D−1)(d_G(P) − 1) = def(G̃) − 1`. -/

/-- **Splitting-off lowers the deficiency by at most one** (`lem:splitoff-deficiency`,
KT Lemma 4.3(i)/(ii) refinement). With the same degree-2 hypotheses as
`splitOff_deficiency_le` (the two `v`-incident edges `eₐ`, `e_b` and the fresh `e₀ ∉ E(G)`),
`def(G̃) − 1 ≤ def(G̃_v^{ab})`. Together with `splitOff_deficiency_le` this confines the
splitting-off deficiency to `{def(G̃), def(G̃) − 1}`: `G_v^{ab}` is a `k`-dof- or a
`(k−1)`-dof-graph.

Proved by the deficiency-count route (no forest surgery), dual to `splitOff_deficiency_le`:
a partition `f` attaining `def(G̃)` is reused on `V(G) ∖ {v}`; a case split on whether `v`'s
label is shared bounds the change in parts and crossing edges. See `rem:kt-lemma-41` and
`notes/Phase20.md` for why the matroid-base form of KT 4.3(ii) is off the Theorem-4.9
critical path. -/
theorem splitOff_deficiency_ge [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hD : 1 ≤ bodyBarDim n) {v a b : α} {e₀ eₐ e_b : β}
    (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b)
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    (he₀ : e₀ ∉ E(G)) :
    G.deficiency n - 1 ≤ (G.splitOff v a b e₀).deficiency n := by
  classical
  set H := G.splitOff v a b e₀ with hH
  have haV : a ∈ V(G) := hla.right_mem
  have hbV : b ∈ V(G) := hlb.right_mem
  have hD1 : (0 : ℤ) ≤ (bodyBarDim n : ℤ) - 1 := by
    have : (1 : ℤ) ≤ (bodyBarDim n : ℤ) := by exact_mod_cast hD
    linarith
  -- Pick a partition `f` of `V(G)` attaining `def(G̃)` (finite supremum).
  haveI : Nonempty α := ⟨a⟩
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
          simp only [if_pos hee₀]
          by_cases hfva : f v = f a
          · -- map to `e_b`: `e_b` links `v, b`, `f v = f a ≠ f b`, so `e_b` crosses.
            simp only [if_pos hfva]
            exact ⟨hebG, v, b, hlb, by rw [hfva]; exact hab⟩
          · -- map to `eₐ`: `eₐ` links `v, a`, `f v ≠ f a`, so `eₐ` crosses.
            simp only [if_neg hfva]
            exact ⟨heaG, v, a, hla, hfva⟩
        · simp only [if_neg hee₀]
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
          · rw [if_pos hfva] at heH; exact hebH heH
          · rw [if_neg hfva] at heH; exact heaH heH
        by_cases h1 : e1 = e₀ <;> by_cases h2 : e2 = e₀
        · rw [h1, h2]
        · rw [if_pos h1, if_neg h2] at hg; exact absurd hg.symm (hne he2 h2)
        · rw [if_neg h1, if_pos h2] at hg; exact absurd hg (hne he1 h1)
        · rwa [if_neg h1, if_neg h2] at hg
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
            simp only [if_pos hee₀]
            rw [hH, splitOff_isLink, hee₀] at hlink
            rcases hlink with ⟨hne, _⟩ | ⟨_, _, _, _, _, hxy'⟩
            · exact absurd rfl hne
            exact heb_cross
          · simp only [if_neg hee₀]
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
        · rw [if_pos h1, if_neg h2] at hg; exact absurd hg.symm (hne he2 h2)
        · rw [if_neg h1, if_pos h2] at hg; exact absurd hg (hne he1 h1)
        · rwa [if_neg h1, if_neg h2] at hg
      have hnotmem : eₐ ∉ (fun e => if e = e₀ then e_b else e) '' H.crossingEdges f := by
        rintro ⟨e', he', hg⟩
        dsimp only at hg
        by_cases hee₀ : e' = e₀
        · rw [if_pos hee₀] at hg; exact heab hg.symm
        · rw [if_neg hee₀] at hg; exact heaH (hg ▸ he'.1)
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_insert_of_notMem hnotmem (Set.toFinite _), hinj.ncard_image] at this
      omega
    rw [partitionDef, partitionDef]
    have : (G.numParts f : ℤ) = (H.numParts f : ℤ) + 1 := hparts
    nlinarith [Int.ofNat_le.mpr hcross, this]

/-! ### Vertex removal raises the deficiency (`lem:removal-deficiency`, KT Lemma 4.4)

The other half of the local dof bookkeeping at a degree-2 vertex `v`: deleting `v`
(`removeVertex`) does **not** decrease the deficiency, `def(G̃) ≤ def(G̃ᵥ)`. Equivalently,
if `def(G̃) = k` then `def(G̃ᵥ) ≥ k` — Katoh–Tanigawa 2011 Lemma 4.4 (p.662).

This is proved by the **same deficiency-count route** that carried `splitOff_deficiency_le`
/ `splitOff_deficiency_ge`, *no forests* — refuting `notes/Phase20.md` *Finding 2* (which
had claimed KT 4.4's lower bound is not a deficiency-counting fact, gated on the unsplit
forest surgery). The removal case is in fact structurally *simpler* than splitting-off:
`removeVertex v = deleteVerts {v}` adds **no** fresh edge `e₀`/`ab`, so the crossing count
strictly drops with no replacement. Take a partition `f` of `V(G)` attaining `def(G̃) = k`
(finite supremum), and reuse the *same* labeling on `V(Gᵥ) = V(G) ∖ {v}`. The crossing
edges of `Gᵥ` are exactly the crossing edges of `G` other than the two `v`-incident edges
`eₐ`, `e_b` (`hdeg2`), so `d_{Gᵥ}(P) = d_G(P) − c` with `c ∈ {0, 1, 2}` the number of
`v`-edges that crossed. Case-split on whether `v`'s label is shared:
* **shared** — `|P|` unchanged, so `def_{Gᵥ}(P) = k + (D−1)·c ≥ k` (the dropped `v`-edges
  *help*, since `partitionDef` carries `−(D−1)·d`; we only need `d_{Gᵥ}(P) ≤ d_G(P)`).
* **isolated** — `|P|` drops by exactly `1`, but `v`'s neighbours `a, b` are then forced
  into *different* blocks from `v`, so **both** `eₐ` and `e_b` crossed (`c = 2`), giving
  `def_{Gᵥ}(P) = k − D + 2(D−1) = k + (D−2) ≥ k`. The `+2(D−1)` crossing-drop exactly
  pays for the `−D` part-loss precisely because `D ≥ 2`.

The `2 ≤ bodyBarDim n` hypothesis (strengthening the bare `1 ≤ bodyBarDim n` the
splitting-off lemmas carry) is where the molecular regime `n ≥ 2 ⟹ D = n(n+1)/2 ≥ 3`
enters; it is the genuine signature difference from `splitOff_deficiency_ge`, forcing the
isolated case to break even. Degree-2 (`hdeg2`: `eₐ`, `e_b` are the only `v`-incident
edges) is what forces `c = 2` in the isolated case. -/

/-- **Vertex removal raises the deficiency** (`lem:removal-deficiency`, KT Lemma 4.4,
p.662). Let `v` be a degree-2 vertex of `G` with neighbours `a, b`, carried by the two
distinct edges `eₐ` (joining `v, a`) and `e_b` (joining `v, b`) that are the *only* edges
of `G` incident to `v` (`hdeg2`), with `a, b ≠ v`. With `D = bodyBarDim n ≥ 2`, vertex
removal does not decrease the deficiency: `def(G̃) ≤ def(G̃ᵥ)`. So if `G` is a `k`-dof-graph
then `G_v` has `def(G̃ᵥ) ≥ k`.

Proved by the deficiency-count route (no forest surgery), parallel to
`splitOff_deficiency_ge` but simpler — there is no fresh short-circuit edge, so the
crossing count strictly drops. A partition `f` attaining `def(G̃)` is reused on
`V(G) ∖ {v}`; a case split on whether `v`'s label is shared bounds the change in parts and
crossing edges. In the isolated case both `v`-edges necessarily cross (`c = 2`), and the
`D ≥ 2` hypothesis makes the `+2(D−1)` crossing-drop pay for the `−D` part-loss. This is
the deficiency-count proof that **refutes** `notes/Phase20.md` *Finding 2*'s claim that
KT 4.4 needed the unsplit forest surgery. See `notes/Phase20.md` and `rem:kt-lemma-44`. -/
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
  haveI : Nonempty α := ⟨a⟩
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

/-! ### Degrees of freedom under vertex removal and splitting-off (`lem:dof-tracking`, KT 4.3–4.5)

The local degree-of-freedom bookkeeping at a degree-2 vertex `v`, packaged from the three
green per-partition deficiency bounds. For a `k`-dof-graph `G` (`def(G̃) = k`) with a
degree-2 vertex `v` of neighbours `a, b`:
* the splitting-off `G_v^{ab}` is a `k`-dof- or a `(k−1)`-dof-graph — `def(G̃_v^{ab}) ∈
  {k, k − 1}` — by `splitOff_deficiency_le` (`≤ k`) and `splitOff_deficiency_ge` (`≥ k − 1`);
* the removal `G_v` is at least a `k`-dof-graph — `def(G̃_v) ≥ k` — by
  `removeVertex_deficiency_ge`.

These are the dof-conservation laws the combinatorial induction (KT 4.6–4.9) tracks: each
reduction step (splitting-off or vertex removal) keeps the deficiency `k` invariant or drops
it by exactly one, so the target `k` is preserved along the reduction chain. KT phrases the
"which alternative" refinement (whether `G_v^{ab}` keeps `k` or drops to `k − 1`) via the
fundamental-circuit count of the new edge `ab` through the forest surgery (`rem:kt-lemma-41`);
that refinement is off the Theorem-4.9 critical path (the induction consumes only the
two-sided bound), so it is omitted. -/

/-- **Degrees of freedom under vertex removal and splitting-off** (`lem:dof-tracking`,
KT Lemmas 4.3–4.5). Let `v` be a degree-2 vertex of `G` with neighbours `a, b`, carried by
the two distinct edges `eₐ`/`e_b` that are the *only* edges of `G` incident to `v`
(`hdeg2`), and let `D = bodyBarDim n ≥ 2`. If `G` is a `k`-dof-graph (`def(G̃) = k`), then
with the fresh short-circuit label `e₀ ∉ E(G)`:
* `def(G̃) − 1 ≤ def(G̃_v^{ab}) ≤ def(G̃)` — the splitting-off `G_v^{ab}` is a `k`-dof- or a
  `(k−1)`-dof-graph;
* `def(G̃) ≤ def(G̃_v)` — the removal `G_v` has deficiency `≥ k`.

A packaging lemma over the three deficiency-count bounds `splitOff_deficiency_le`,
`splitOff_deficiency_ge`, `removeVertex_deficiency_ge` (no forests; see `rem:kt-lemma-41`).
These are the dof-conservation laws the induction toward Theorem 4.9 tracks. -/
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
  ⟨splitOff_deficiency_ge hD1 hav hbv heab hla hlb hdeg2 he₀,
    splitOff_deficiency_le hD1 hav hbv heab hla hlb hdeg2 he₀,
    removeVertex_deficiency_ge hD hav hbv heab hla hlb hdeg2⟩

end Graph
