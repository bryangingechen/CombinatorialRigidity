import CombinatorialRigidity

/-! The witness of 41d's item R (Phase 41, 2026-10-29, at commit `953367f0`; not part of the
library). It checks route A's combinatorial half for KT Theorem 4.9's principle
(`notes/Phase41-design.md` §2, *Item R's recon*): the deficiency chain that the principle calls
holds when the label `e₀` of the new edge of `G_v^{ab}` is only outside `E(G − v)`, so the principle
needs no `hfresh`. Names are the witness's, in `Graph.Recon41Reduction`; a primed name is the
landed declaration under the weaker hypothesis, its proof the landed one with the edits the arc
lists.

Proved, with no `sorry`:
* `notMem_edgeSet_removeVertex`, and `notMem_edgeSet_removeVertex_iff`: when `eₐ` and `e_b` are the
  only edges at `v`, `e₀ ∉ E(G − v)` iff `e₀ ∉ E(G)` or `e₀ ∈ {eₐ, e_b}`.
* The chain under `e₀ ∉ E(G − v)`: `removeVertex_le_splitOff'`,
  `edgeSet_mulTilde_splitOff_diff_fiber'`, `circuit_splitOff_meets_fiber'`,
  `splitOff_deficiency_le'` (the landed private `splitOff_deficiency_le_aux`, generalized),
  `dof_tracking'`, and `splitOff_isMinimalKDof'` (KT Lemma 4.8(i)), which no longer uses
  `eₐ ≠ e_b`. `splitOff_deficiency_ge'` (KT Lemma 4.3(i)'s lower bound) asks nothing of `e₀`.
* `minimal_kdof_reduction'`: the principle with no `hfresh`, its split case given `P` at
  `G_v^{ab}` for every label `e₀ ∉ E(G − v)` of the new edge. It implies the landed principle
  (`minimal_kdof_reduction_of'`) and the reading with one such label
  (`minimal_kdof_reduction_of_one_label`).
* UNSTATED's U4 without `hfresh`: `minimal_kdof_reduction_sequence`, its step `KTReductionStep`
  taking a split-off at a label `e₀ ∉ E(G − v)` (the copy in `UnstatedWitness.lean` takes
  `e₀ ∉ E(G)`, with `hfresh`).

Check it from the repository root with `lake lean notes/reconcile-formal/ReductionWitness.lean`: no
errors or warnings, and the `#print axioms` give `[propext, Classical.choice, Quot.sound]`. -/

open scoped Graph

namespace Graph.Recon41Reduction

open Set Matroid

variable {α β : Type*}

/-! ## The weaker hypothesis -/

/-- A label outside `E(G)` is outside `E(G − v)`. -/
theorem notMem_edgeSet_removeVertex {G : Graph α β} {e : β} (he : e ∉ E(G)) (v : α) :
    e ∉ E(G.removeVertex v) :=
  fun h => he ((G.removeVertex_le v).edgeSet_mono h)

/-- When `eₐ` and `e_b` are the only edges at `v`, a label is outside `E(G − v)` iff it is outside
`E(G)` or is `eₐ` or `e_b`. -/
theorem notMem_edgeSet_removeVertex_iff {G : Graph α β} {v a b : α} {e₀ eₐ e_b : β}
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b) :
    e₀ ∉ E(G.removeVertex v) ↔ e₀ ∉ E(G) ∨ e₀ = eₐ ∨ e₀ = e_b := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    obtain ⟨hG, ha, hb⟩ := hc
    obtain ⟨x, y, hl⟩ := exists_isLink_of_mem_edgeSet hG
    by_cases hx : x = v
    · subst hx
      exact (hdeg2 e₀ y hl).elim ha hb
    by_cases hy : y = v
    · subst hy
      exact (hdeg2 e₀ x hl.symm).elim ha hb
    exact h (removeVertex_isLink.mpr ⟨hl, hx, hy⟩).edge_mem
  · rintro (h | rfl | rfl) hmem
    · exact notMem_edgeSet_removeVertex h v hmem
    · obtain ⟨x, y, hl⟩ := exists_isLink_of_mem_edgeSet hmem
      obtain ⟨hlG, hx, hy⟩ := removeVertex_isLink.mp hl
      rcases hla.eq_and_eq_or_eq_and_eq hlG with ⟨h, -⟩ | ⟨h, -⟩
      · exact hx h.symm
      · exact hy h.symm
    · obtain ⟨x, y, hl⟩ := exists_isLink_of_mem_edgeSet hmem
      obtain ⟨hlG, hx, hy⟩ := removeVertex_isLink.mp hl
      rcases hlb.eq_and_eq_or_eq_and_eq hlG with ⟨h, -⟩ | ⟨h, -⟩
      · exact hx h.symm
      · exact hy h.symm

/-! ## The chain under `e₀ ∉ E(G − v)` -/

/-- `removeVertex_le_splitOff` under `e₀ ∉ E(G − v)`: a link of `G − v` is not `e₀`. -/
theorem removeVertex_le_splitOff' {G : Graph α β} {v a b : α} {e₀ : β}
    (he₀ : e₀ ∉ E(G.removeVertex v)) : G.removeVertex v ≤ G.splitOff v a b e₀ := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [vertexSet_splitOff]
    rw [vertexSet_removeVertex] at hx
    exact hx
  · intro e x y h
    have h' := removeVertex_isLink.mp h
    rw [splitOff_isLink]
    exact Or.inl ⟨fun hee => he₀ (hee ▸ h.edge_mem), h'.1, h'.2.1, h'.2.2⟩

/-- `edgeSet_mulTilde_splitOff_diff_fiber` under `e₀ ∉ E(G − v)`. -/
theorem edgeSet_mulTilde_splitOff_diff_fiber' {G : Graph α β} {v a b : α} {e₀ : β} (n : ℕ)
    (he₀ : e₀ ∉ E(G.removeVertex v)) :
    E((G.splitOff v a b e₀).mulTilde n) \ edgeFiber e₀ n = E((G.removeVertex v).mulTilde n) := by
  ext p
  simp only [Set.mem_sdiff, mem_edgeFiber, mem_edgeSet_mulTilde,
    edgeSet_splitOff, Set.mem_union]
  constructor
  · rintro ⟨(⟨rfl, _⟩ | ⟨_, x, y, hl, hx, hy⟩), hpne⟩
    · exact absurd rfl hpne
    · exact (removeVertex_isLink.mpr ⟨hl, hx, hy⟩).edge_mem
  · intro hp
    obtain ⟨x, y, hl⟩ := exists_isLink_of_mem_edgeSet hp
    obtain ⟨hlG, hx, hy⟩ := removeVertex_isLink.mp hl
    refine ⟨Or.inr ⟨?_, x, y, hlG, hx, hy⟩, ?_⟩
    · rintro h; exact he₀ (h ▸ hp)
    · rintro h; exact he₀ (h ▸ hp)

/-- `circuit_splitOff_meets_fiber` (KT eq. (4.10)) under `e₀ ∉ E(G − v)`; the landed proof, with
the two calls above. -/
theorem circuit_splitOff_meets_fiber' [DecidableEq β] [Finite α] [Finite β] {G : Graph α β}
    [G.Loopless] {n : ℕ} (hD : 1 ≤ bodyBarDim n) {v a b : α} {e₀ : β} (hvG : v ∈ V(G))
    (he₀ : e₀ ∉ E(G.removeVertex v)) (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n)
    {X : Set (β × Fin (bodyHingeMult n))}
    (hX : ((G.splitOff v a b e₀).matroidMG n).IsCircuit X) :
    (X ∩ edgeFiber e₀ n).Nonempty := by
  classical
  rw [Set.nonempty_iff_ne_empty]
  intro hXe
  -- `X ⊆ E(G̃_v^{ab}) ∖ ẽ₀ = E(G̃_v)` (ground-set bridge).
  have hXground : X ⊆ E((G.splitOff v a b e₀).mulTilde n) := by
    have := hX.subset_ground; rwa [matroidMG, Matroid.restrict_ground_eq] at this
  have hXdisj : Disjoint X (edgeFiber e₀ n) := Set.disjoint_iff_inter_eq_empty.mpr hXe
  have hXsubGv : X ⊆ E((G.removeVertex v).mulTilde n) := by
    rw [← edgeSet_mulTilde_splitOff_diff_fiber' n he₀]
    exact Set.subset_sdiff.mpr ⟨hXground, hXdisj⟩
  -- `G_v ≤ G_v^{ab}`: every link of `G` that avoids `v` survives, as `e₀ ∉ E(G − v)`.
  have hleGvSplit : G.removeVertex v ≤ G.splitOff v a b e₀ := removeVertex_le_splitOff' he₀
  have hleSplitMul : (G.removeVertex v).mulTilde n ≤ (G.splitOff v a b e₀).mulTilde n :=
    edgeMultiply_mono hleGvSplit _
  -- `M(G̃_v^{ab}) ↾ E(G̃_v) = M(G̃_v)`, so `X` is a circuit of `M(G̃_v)`.
  have hcircGv : ((G.removeVertex v).matroidMG n).IsCircuit X := by
    rw [← matroidMG_restrict_mulTilde hleGvSplit n,
      Matroid.restrict_isCircuit_iff hleSplitMul.edgeSet_mono]
    exact ⟨hX, hXsubGv⟩
  -- `M(G̃) ↾ E(G̃_v) = M(G̃_v)`, so `X` is a circuit of `M(G̃)`.
  have hleG : G.removeVertex v ≤ G := by
    rw [removeVertex]; exact deleteVerts_le
  have hcircG : (G.matroidMG n).IsCircuit X := by
    have hbridge := matroidMG_restrict_mulTilde hleG n
    rw [← hbridge] at hcircGv
    exact (Matroid.restrict_isCircuit_iff (edgeMultiply_mono hleG _).edgeSet_mono).mp hcircGv |>.1
  -- `G[V(X)]` is a rigid subgraph of `G`.
  have hrigid : (G.inducedSpan n X).IsRigidSubgraph G n :=
    circuit_induces_isRigidSubgraph hD hcircG
  -- `v ∉ V(X)`: every fiber of `X` is a copy of a `v`-avoiding edge.
  have hvnot : v ∉ V(G.inducedSpan n X) := by
    rw [vertexSet_inducedSpan, fiberSpan, mem_spanningVerts]
    rintro ⟨p, hpX, hinc⟩
    rw [mulTilde_inc] at hinc
    obtain ⟨w, hlw⟩ := hinc
    -- `p.1 ∈ E(G_v)`, so `p.1` carries a `v`-avoiding `G`-link, contradicting `G.IsLink p.1 v w`.
    have hpe : p.1 ∈ E(G.removeVertex v) := by
      have := hXsubGv hpX
      rwa [mem_edgeSet_mulTilde] at this
    obtain ⟨x, y, hlxy⟩ := exists_isLink_of_mem_edgeSet hpe
    rw [removeVertex_isLink] at hlxy
    obtain ⟨hlxyG, hxv, hyv⟩ := hlxy
    rcases hlw.left_eq_or_eq hlxyG with h | h
    · exact hxv h.symm
    · exact hyv h.symm
  -- A loopless circuit spans two distinct vertices; with `v ∉ V(X)`, `G[V(X)]` is *proper* rigid.
  have hV2 : 2 ≤ V(G.inducedSpan n X).ncard := by
    rw [vertexSet_inducedSpan, fiberSpan]
    obtain ⟨q, hq⟩ := hcircG.nonempty
    obtain ⟨x, y, hinc⟩ := exists_isLink_of_mem_edgeSet (hcircG.subset_ground hq)
    have hxy : x ≠ y := ((mulTilde_isLink G n).mp hinc).ne
    exact (Set.one_lt_ncard (Set.toFinite _)).mpr
      ⟨x, ⟨q, hq, hinc.inc_left⟩, y, ⟨q, hq, hinc.inc_right⟩, hxy⟩
  have hVsub : V(G.inducedSpan n X) ⊆ V(G) := by
    rw [vertexSet_inducedSpan, fiberSpan]
    exact (G.mulTilde n).spanningVerts_subset_vertexSet X
  exact hnp (G.inducedSpan n X)
    ⟨hrigid, hV2, hVsub.ssubset_of_ne (fun heq => hvnot (heq ▸ hvG))⟩

/-- `splitOff_deficiency_le` (KT Lemma 4.3(i), upper bound) under `e₀ ∉ E(G − v)`: the landed
`splitOff_deficiency_le_aux`, whose `he₀cross` (`e₀` crosses no part) becomes "no edge across the
partition other than `e_b` is `e₀`", as such an edge avoids `v`. -/
theorem splitOff_deficiency_le' [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hD : 1 ≤ bodyBarDim n) {v a b : α} {e₀ eₐ e_b : β}
    (hav : a ≠ v) (hbv : b ≠ v)
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    (he₀ : e₀ ∉ E(G.removeVertex v)) :
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
  -- An edge of `G` across `f` other than `e_b` avoids `v`: at `v` it would be `eₐ`, whose ends `v`
  -- and `a` both have the label `f' a`. So it is an edge of `G − v`, and not `e₀`.
  have hcross_v : ∀ e x y, G.IsLink e x y → f x ≠ f y → e ≠ e_b → x ≠ v := by
    intro e x y hlink hxy hev hxv
    subst hxv
    rcases hdeg2 e y hlink with rfl | rfl
    · rcases hla.eq_and_eq_or_eq_and_eq hlink with ⟨-, rfl⟩ | ⟨-, hav'⟩
      · exact hxy (by rw [hfv, hfa])
      · exact hav hav'
    · exact hev rfl
  have he₀cross : ∀ e ∈ G.crossingEdges f, e ≠ e_b → e ≠ e₀ := by
    rintro e ⟨-, x, y, hlink, hxy⟩ hev hee
    exact he₀ (hee ▸ (removeVertex_isLink.mpr ⟨hlink, hcross_v e x y hlink hxy hev,
      hcross_v e y x hlink.symm (Ne.symm hxy) hev⟩).edge_mem)
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
        have hee₀ : e ≠ e₀ := he₀cross e he hev
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
        exact (he₀cross e2 he2 h2 hg.symm).elim
      · rw [ite_eq_right h1, ite_eq_left h2] at hg
        exact (he₀cross e1 he1 h1 hg).elim
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


/-- KT Lemma 4.3(i)'s lower bound, with no hypothesis on the label `e₀`. -/
theorem splitOff_deficiency_ge' [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hD : 1 ≤ bodyBarDim n) {v a b : α} {e₀ eₐ e_b : β}
    (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b)
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b) :
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
  -- `eₐ`, `e_b ∈ E(G)`.
  have heaG : eₐ ∈ E(G) := hla.edge_mem
  have hebG : e_b ∈ E(G) := hlb.edge_mem
  -- An edge of `H` other than `e₀` is an edge of `G` away from `v`: neither `eₐ` nor `e_b`.
  have hHne : ∀ e ∈ E(H), e ≠ e₀ → e ≠ eₐ ∧ e ≠ e_b := by
    intro e heH hee₀
    rw [hH, edgeSet_splitOff] at heH
    rcases heH with ⟨h, _⟩ | ⟨_, x, y, hl, hxv, hyv⟩
    · exact absurd h hee₀
    · refine ⟨?_, ?_⟩
      · rintro rfl
        rcases hla.eq_and_eq_or_eq_and_eq hl with ⟨rfl, _⟩ | ⟨rfl, _⟩
        · exact hxv rfl
        · exact hyv rfl
      · rintro rfl
        rcases hlb.eq_and_eq_or_eq_and_eq hl with ⟨rfl, _⟩ | ⟨rfl, _⟩
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
          rintro e ⟨heH, -⟩ hne₀
          by_cases hfva : f v = f a
          · rw [ite_eq_left hfva]; exact (hHne e heH hne₀).2
          · rw [ite_eq_right hfva]; exact (hHne e heH hne₀).1
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
          rintro e ⟨heH, -⟩ hne₀; exact (hHne e heH hne₀).2
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
        · rw [ite_eq_right hee₀] at hg; exact (hHne e' he'.1 hee₀).1 hg
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_insert_of_notMem hnotmem (Set.toFinite _), hinj.ncard_image] at this
      omega
    rw [partitionDef, partitionDef]
    have : (G.numParts f : ℤ) = (H.numParts f : ℤ) + 1 := hparts
    nlinarith [Int.ofNat_le.mpr hcross, this]

/-- `lem:dof-tracking` under `e₀ ∉ E(G − v)`. -/
theorem dof_tracking' [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hD : 2 ≤ bodyBarDim n) {v a b : α} {e₀ eₐ e_b : β}
    (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b)
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    (he₀ : e₀ ∉ E(G.removeVertex v)) :
    G.deficiency n - 1 ≤ (G.splitOff v a b e₀).deficiency n ∧
      (G.splitOff v a b e₀).deficiency n ≤ G.deficiency n ∧
      G.deficiency n ≤ (G.removeVertex v).deficiency n :=
  have hD1 : 1 ≤ bodyBarDim n := le_trans (by norm_num) hD
  ⟨splitOff_deficiency_ge' hD1 hav hbv heab hla hlb,
    splitOff_deficiency_le' hD1 hav hbv hla hlb hdeg2 he₀,
    removeVertex_deficiency_ge hD hav hbv heab hla hlb hdeg2⟩

/-- `splitOff_isMinimalKDof` (KT Lemma 4.8(i)) under `e₀ ∉ E(G − v)`: the landed proof with the
upper bound called directly (`dof_tracking`'s other bounds unused, and with them `eₐ ≠ e_b`) and
the three chain lemmas above. -/
theorem splitOff_isMinimalKDof' [DecidableEq β] [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hD : 2 ≤ bodyBarDim n) (hV3 : 3 ≤ V(G).ncard) {v a b : α} {e₀ eₐ e_b : β}
    (hav : a ≠ v) (hbv : b ≠ v) (hla : G.IsLink eₐ v a)
    (hlb : G.IsLink e_b v b) (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    (he₀ : e₀ ∉ E(G.removeVertex v))
    (hG : G.IsMinimalKDof n 0) (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) :
    (G.splitOff v a b e₀).IsMinimalKDof n 0 := by
  classical
  have haV : a ∈ V(G) := hla.right_mem
  have hbV : b ∈ V(G) := hlb.right_mem
  have hvG : v ∈ V(G) := hla.left_mem
  have : G.Loopless := loopless_of_isMinimalKDof hG
  have hD1 : 1 ≤ bodyBarDim n := le_trans (by norm_num) hD
  set G' := G.splitOff v a b e₀ with hG'def
  set Gv := G.removeVertex v with hGvdef
  -- Vertex sets: `V(G') = V(Gv) = V(G) ∖ {v}`, nonempty (it contains `a`) and of size `≥ 2`.
  have hVeq : V(G') = V(G) \ {v} := vertexSet_splitOff G v a b e₀
  have hVveq : V(Gv) = V(G) \ {v} := vertexSet_removeVertex G v
  have hVne : V(G').Nonempty := by rw [hVeq]; exact ⟨a, haV, by simpa using hav⟩
  have hVvne : V(Gv).Nonempty := by rw [hVveq]; exact ⟨a, haV, by simpa using hav⟩
  have hVv2 : 2 ≤ V(Gv).ncard := by
    rw [hVveq, Set.ncard_sdiff (by simpa using hvG) (Set.toFinite _), Set.ncard_singleton]
    omega
  -- `Gv ≤ G` a proper subgraph (`v ∈ V(G)` is dropped); under no-proper-rigid, `def(G̃v) > 0`.
  have hleGvG : Gv ≤ G := by rw [hGvdef, removeVertex]; exact deleteVerts_le
  have hdefGv_pos : 0 < Gv.deficiency n := by
    rcases lt_or_eq_of_le (Gv.deficiency_nonneg n hVvne) with h | h
    · exact h
    · exfalso
      refine hnp Gv ⟨⟨hleGvG, h.symm⟩, hVv2, ?_⟩
      rw [hVveq]; exact Set.sdiff_singleton_ssubset.mpr hvG
  -- 0-dof half: `def(G̃') = 0`, the upper bound squeezed against `def(G̃) = 0` and `def ≥ 0`.
  have hdofG : G.deficiency n = 0 := hG.deficiency_eq
  have hdefG'_zero : G'.deficiency n = 0 := by
    have h1 : G'.deficiency n ≤ G.deficiency n :=
      splitOff_deficiency_le' hD1 hav hbv hla hlb hdeg2 he₀
    have h2 : 0 ≤ G'.deficiency n := G'.deficiency_nonneg n hVne
    rw [hdofG] at h1; omega
  refine ⟨hdefG'_zero, fun B' hB' e heG' => ?_⟩
  -- Prove the fiber-meeting by contradiction: assume `B' ∩ ẽ = ∅`.
  rw [Set.nonempty_iff_ne_empty]
  intro hBe
  -- `E(G̃') = ẽ₀ ⊔ E(G̃v)`: the copies of `ab` and those of the edges of `Gv`.
  have hsplit_ground : E(G'.mulTilde n) \ edgeFiber e₀ n = E(Gv.mulTilde n) :=
    edgeSet_mulTilde_splitOff_diff_fiber' n he₀
  have hfiberGround : edgeFiber e₀ n ⊆ E(G'.mulTilde n) :=
    edgeFiber_subset_edgeSet_mulTilde_splitOff n hav hbv haV hbV
  -- `B' ⊆ E(G̃')`, `|B'| = D(|V'|−1)` since `def(G̃') = 0`.
  have hB'ground : B' ⊆ E(G'.mulTilde n) := hB'.subset_ground
  have hB'card : (B'.ncard : ℤ) + 0 = bodyBarDim n * ((V(G').ncard : ℤ) - 1) := by
    have := G'.isBase_ncard_add_deficiency_eq n hD1 hVne hB'
    rwa [hdefG'_zero] at this
  -- `E(G̃v)` is a base of `M(G̃v)`: it is circuit-free in `M(G̃')` (KT (4.10)), hence
  -- independent there, and restriction descends it to the whole ground of `M(G̃v)`.
  have hGv_indep_in_G' : (G'.matroidMG n).Indep (E(Gv.mulTilde n)) := by
    rw [Matroid.indep_iff_forall_subset_not_isCircuit']
    refine ⟨fun C hCsub hC => ?_, ?_⟩
    · -- A circuit `C ⊆ E(G̃v)` avoids `ẽ₀`, contradicting `circuit_splitOff_meets_fiber`.
      obtain ⟨p, hpC, hpfib⟩ := circuit_splitOff_meets_fiber' hD1 hvG he₀ hnp hC
      have hpGv : p ∈ E(Gv.mulTilde n) := hCsub hpC
      rw [← hsplit_ground] at hpGv
      exact hpGv.2 hpfib
    · rw [matroidMG, Matroid.restrict_ground_eq, ← hsplit_ground]; exact Set.sdiff_subset
  have hleGvG' : Gv ≤ G' := by
    rw [hGvdef, hG'def]
    exact removeVertex_le_splitOff' he₀
  have hGv_base : (Gv.matroidMG n).IsBase (E(Gv.mulTilde n)) := by
    have hg : (Gv.matroidMG n).E = E(Gv.mulTilde n) := by
      rw [matroidMG, Matroid.restrict_ground_eq]
    rw [← hg, ← Matroid.ground_indep_iff_isBase, hg, ← matroidMG_restrict_mulTilde hleGvG' n,
      Matroid.restrict_indep_iff]
    exact ⟨hGv_indep_in_G', subset_rfl⟩
  -- `|E(G̃v)| + def(G̃v) = D(|V v|−1) = D(|V'|−1)` (same vertex set `V(G)∖{v}`).
  have hEGvcard : (E(Gv.mulTilde n).ncard : ℤ) + Gv.deficiency n
      = bodyBarDim n * ((V(G').ncard : ℤ) - 1) := by
    have hb := Gv.isBase_ncard_add_deficiency_eq n hD1 hVvne hGv_base
    rw [hVveq] at hb; rw [hVeq]; exact hb
  -- Core cardinality bound: any base `B'` avoiding the fiber `ẽ` has `|B'| ≤ |E(G̃v)|`.
  have hB'le : B'.ncard ≤ E(Gv.mulTilde n).ncard := by
    by_cases he : e = e₀
    · -- `e = e₀`: `B'` avoids `ẽ₀`, so `B' ⊆ E(G̃v)`.
      subst he
      have hB'sub : B' ⊆ E(Gv.mulTilde n) := by
        rw [← hsplit_ground]
        refine Set.subset_sdiff.mpr ⟨hB'ground, Set.disjoint_left.mpr fun p hpB' hpfib => ?_⟩
        exact absurd (Set.eq_empty_iff_forall_notMem.mp hBe p ⟨hpB', hpfib⟩) id
      exact Set.ncard_le_ncard hB'sub (Set.toFinite _)
    · -- `e ≠ e₀`: split `B'` into `B' ∩ ẽ₀` (≤ D−1) and `B' ∩ E(G̃v) ⊆ E(G̃v) ∖ ẽ`.
      have heGv : edgeFiber e n ⊆ E(Gv.mulTilde n) := by
        intro p hp
        rw [mem_edgeFiber] at hp
        have heE : e ∈ E(Gv) := by
          have hmem : e ∈ E(G') := heG'
          rw [hG'def, edgeSet_splitOff] at hmem
          rcases hmem with ⟨rfl, _⟩ | ⟨_, x, y, hl, hx, hy⟩
          · exact absurd rfl he
          · have hlGv : Gv.IsLink e x y := by rw [hGvdef, removeVertex_isLink]; exact ⟨hl, hx, hy⟩
            exact hlGv.edge_mem
        rw [mem_edgeSet_mulTilde, hp]; exact heE
      -- Decompose `B' = (B' ∩ ẽ₀) ∪ (B' ∩ E(G̃v))` since `B' ⊆ ẽ₀ ∪ E(G̃v) = E(G̃')`.
      have hcover : B' ⊆ edgeFiber e₀ n ∪ E(Gv.mulTilde n) := by
        intro p hpB'
        rcases em (p ∈ edgeFiber e₀ n) with hpf | hpf
        · exact Or.inl hpf
        · exact Or.inr (hsplit_ground ▸ ⟨hB'ground hpB', hpf⟩)
      have h1 : (B' ∩ edgeFiber e₀ n).ncard ≤ bodyHingeMult n := by
        calc (B' ∩ edgeFiber e₀ n).ncard ≤ (edgeFiber e₀ n).ncard :=
              Set.ncard_le_ncard Set.inter_subset_right (Set.toFinite _)
          _ = bodyHingeMult n := edgeFiber_ncard e₀ n
      have h2 : (B' ∩ E(Gv.mulTilde n)).ncard ≤ E(Gv.mulTilde n).ncard - bodyHingeMult n := by
        have hsub : B' ∩ E(Gv.mulTilde n) ⊆ E(Gv.mulTilde n) \ edgeFiber e n := by
          refine Set.subset_sdiff.mpr ⟨Set.inter_subset_right, Set.disjoint_left.mpr ?_⟩
          intro p hpB' hpfib
          exact absurd (Set.eq_empty_iff_forall_notMem.mp hBe p ⟨hpB'.1, hpfib⟩) id
        calc (B' ∩ E(Gv.mulTilde n)).ncard ≤ (E(Gv.mulTilde n) \ edgeFiber e n).ncard :=
              Set.ncard_le_ncard hsub (Set.toFinite _)
          _ = E(Gv.mulTilde n).ncard - (edgeFiber e n).ncard :=
              Set.ncard_sdiff heGv (Set.toFinite _)
          _ = E(Gv.mulTilde n).ncard - bodyHingeMult n := by rw [edgeFiber_ncard]
      have hcoverle : B'.ncard ≤ (B' ∩ edgeFiber e₀ n).ncard + (B' ∩ E(Gv.mulTilde n)).ncard := by
        calc B'.ncard ≤ ((B' ∩ edgeFiber e₀ n) ∪ (B' ∩ E(Gv.mulTilde n))).ncard := by
              refine Set.ncard_le_ncard ?_ (Set.toFinite _)
              rw [← Set.inter_union_distrib_left]
              exact Set.subset_inter (subset_refl _) hcover
          _ ≤ (B' ∩ edgeFiber e₀ n).ncard + (B' ∩ E(Gv.mulTilde n)).ncard :=
              Set.ncard_union_le _ _
      -- `|E(G̃v)| ≥ D − 1` (it contains `ẽ` of size `D − 1`), so the subtraction is exact.
      have hge : bodyHingeMult n ≤ E(Gv.mulTilde n).ncard := by
        calc bodyHingeMult n = (edgeFiber e n).ncard := (edgeFiber_ncard e n).symm
          _ ≤ E(Gv.mulTilde n).ncard := Set.ncard_le_ncard heGv (Set.toFinite _)
      omega
  -- Assemble: `D(|V'|−1) = |B'| ≤ |E(G̃v)| = D(|V'|−1) − def(G̃v)`, so `def(G̃v) ≤ 0` — contra.
  have hle : (B'.ncard : ℤ) ≤ (E(Gv.mulTilde n).ncard : ℤ) := by exact_mod_cast hB'le
  linarith [hB'card, hEGvcard, hle, hdefGv_pos]


/-! ## KT Theorem 4.9's principle without `hfresh`

`hsplit` is given `P` at `G_v^{ab}` for every label `e₀ ∉ E(G − v)` of the new edge: the labels at
which the formal splitting off is `G_v^{ab}` (`fmlnote:graph-operations`). One of them is `eₐ`. -/

/-- KT Theorem 4.9's principle (`thm:minimal-kdof-reduction` (ii)) without `hfresh`; the landed
proof, with `hsplit` called at the two edges at `v` and given the induction hypothesis at every
label `e₀ ∉ E(G − v)`. -/
theorem minimal_kdof_reduction' [DecidableEq β] [Finite α] [Finite β] {n : ℕ}
    (hD : 3 ≤ bodyBarDim n) {P : Graph α β → Prop}
    (hbase : ∀ G : Graph α β, G.IsMinimalKDof n 0 → V(G).ncard = 2 → P G)
    (hsplit : ∀ (G : Graph α β) (v a b : α) (eₐ e_b : β),
      G.IsMinimalKDof n 0 → (∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) →
      v ∈ V(G) → a ≠ v → b ≠ v → a ∈ V(G) → b ∈ V(G) → eₐ ≠ e_b →
      G.IsLink eₐ v a → G.IsLink e_b v b → (∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b) →
      (∀ e₀ : β, e₀ ∉ E(G.removeVertex v) → P (G.splitOff v a b e₀)) → P G)
    (hcontract : ∀ G : Graph α β, G.IsMinimalKDof n 0 → 3 ≤ V(G).ncard →
      (∃ H : Graph α β, H.IsProperRigidSubgraph G n) →
      (∀ G' : Graph α β, G'.IsMinimalKDof n 0 → 2 ≤ V(G').ncard →
        V(G').ncard < V(G).ncard → P G') → P G) :
    ∀ G : Graph α β, G.IsMinimalKDof n 0 → 2 ≤ V(G).ncard → P G := by
  classical
  have hD1 : 1 ≤ bodyBarDim n := le_trans (by norm_num) hD
  have hD2 : 2 ≤ bodyBarDim n := le_trans (by norm_num) hD
  intro G
  induction hN : V(G).ncard using Nat.strong_induction_on generalizing G with
  | _ N IH =>
  intro hG hV2
  rcases eq_or_lt_of_le hV2 with hVeq | hVlt
  · exact hbase G hG (hN.trans hVeq.symm)
  · have hV3 : 3 ≤ V(G).ncard := by rw [hN]; omega
    by_cases hrig : ∃ H : Graph α β, H.IsProperRigidSubgraph G n
    · exact hcontract G hG hV3 hrig (fun G' hG' hG'2 hlt => IH _ (hN ▸ hlt) _ rfl hG' hG'2)
    · push Not at hrig
      have hV2' : 2 ≤ V(G).ncard := by rw [hN]; exact hV2
      obtain ⟨v, hvG, hvdeg⟩ := exists_degree_eq_two hD hV2' hG
        (twoEdgeConnected_of_isKDof_zero hD1 hG.1) hrig
      obtain ⟨b₀, hb₀G, hb₀v⟩ : ∃ b₀ ∈ V(G), b₀ ≠ v := by
        by_contra h
        push Not at h
        have hsub : V(G) ⊆ {v} := fun x hx => h x hx
        have : V(G).ncard ≤ 1 := by
          rw [← Set.ncard_singleton v]; exact Set.ncard_le_ncard hsub (Set.toFinite _)
        omega
      obtain ⟨a, b, eₐ, e_b, hav, hbv, haV, hbV, heab, hla, hlb, hdeg2⟩ :=
        exists_splitOff_data_of_degree_eq_two hD1 hG.1 hvG hb₀G hb₀v hvdeg
      refine hsplit G v a b eₐ e_b hG hrig hvG hav hbv haV hbV heab hla hlb hdeg2 fun e₀ he₀ => ?_
      have hsplit2 : 2 ≤ V(G.splitOff v a b e₀).ncard := by
        rw [vertexSet_splitOff]
        have hdv : (V(G) \ {v}).ncard = V(G).ncard - 1 := by
          rw [Set.ncard_sdiff (by simpa using hvG) (Set.toFinite _), Set.ncard_singleton]
        omega
      exact IH _ (hN ▸ splitOff_vertexSet_ncard_lt hvG) _ rfl
        (splitOff_isMinimalKDof' hD2 hV3 hav hbv hla hlb hdeg2 he₀ hG hrig) hsplit2

/-- The landed principle, with `hfresh` and `hsplit` at a label outside `E(G)`, follows from
`minimal_kdof_reduction'`: the restatement is a strengthening. -/
theorem minimal_kdof_reduction_of' [DecidableEq β] [Finite α] [Finite β] {n : ℕ}
    (hD : 3 ≤ bodyBarDim n)
    (hfresh : ∀ G' : Graph α β, G'.IsMinimalKDof n 0 → ∃ e₀ : β, e₀ ∉ E(G'))
    {P : Graph α β → Prop}
    (hbase : ∀ G : Graph α β, G.IsMinimalKDof n 0 → V(G).ncard = 2 → P G)
    (hsplit : ∀ (G : Graph α β) (v a b : α) (eₐ e_b e₀ : β),
      G.IsMinimalKDof n 0 → (∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) →
      v ∈ V(G) → a ≠ v → b ≠ v → a ∈ V(G) → b ∈ V(G) → eₐ ≠ e_b →
      G.IsLink eₐ v a → G.IsLink e_b v b → (∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b) →
      e₀ ∉ E(G) → P (G.splitOff v a b e₀) → P G)
    (hcontract : ∀ G : Graph α β, G.IsMinimalKDof n 0 → 3 ≤ V(G).ncard →
      (∃ H : Graph α β, H.IsProperRigidSubgraph G n) →
      (∀ G' : Graph α β, G'.IsMinimalKDof n 0 → 2 ≤ V(G').ncard →
        V(G').ncard < V(G).ncard → P G') → P G) :
    ∀ G : Graph α β, G.IsMinimalKDof n 0 → 2 ≤ V(G).ncard → P G :=
  minimal_kdof_reduction' hD hbase
    (fun G v a b eₐ e_b hG hnp hvG hav hbv haV hbV heab hla hlb hdeg2 hP =>
      have ⟨e₀, he₀⟩ := hfresh G hG
      hsplit G v a b eₐ e_b e₀ hG hnp hvG hav hbv haV hbV heab hla hlb hdeg2 he₀
        (hP e₀ (notMem_edgeSet_removeVertex he₀ v)))
    hcontract

/-- The other reading of `hsplit`, `P` at one label `e₀ ∉ E(G − v)`, also follows. -/
theorem minimal_kdof_reduction_of_one_label [DecidableEq β] [Finite α] [Finite β] {n : ℕ}
    (hD : 3 ≤ bodyBarDim n) {P : Graph α β → Prop}
    (hbase : ∀ G : Graph α β, G.IsMinimalKDof n 0 → V(G).ncard = 2 → P G)
    (hsplit : ∀ (G : Graph α β) (v a b : α) (eₐ e_b e₀ : β),
      G.IsMinimalKDof n 0 → (∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) →
      v ∈ V(G) → a ≠ v → b ≠ v → a ∈ V(G) → b ∈ V(G) → eₐ ≠ e_b →
      G.IsLink eₐ v a → G.IsLink e_b v b → (∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b) →
      e₀ ∉ E(G.removeVertex v) → P (G.splitOff v a b e₀) → P G)
    (hcontract : ∀ G : Graph α β, G.IsMinimalKDof n 0 → 3 ≤ V(G).ncard →
      (∃ H : Graph α β, H.IsProperRigidSubgraph G n) →
      (∀ G' : Graph α β, G'.IsMinimalKDof n 0 → 2 ≤ V(G').ncard →
        V(G').ncard < V(G).ncard → P G') → P G) :
    ∀ G : Graph α β, G.IsMinimalKDof n 0 → 2 ≤ V(G).ncard → P G :=
  minimal_kdof_reduction' hD hbase
    (fun G v a b eₐ e_b hG hnp hvG hav hbv haV hbV heab hla hlb hdeg2 hP =>
      have hea : eₐ ∉ E(G.removeVertex v) :=
        (notMem_edgeSet_removeVertex_iff hla hlb hdeg2).mpr (Or.inr (Or.inl rfl))
      hsplit G v a b eₐ e_b eₐ hG hnp hvG hav hbv haV hbV heab hla hlb hdeg2 hea (hP eₐ hea))
    hcontract

/-! ## UNSTATED's U4 without `hfresh` -/

/-- One step of KT Theorem 4.9's sequence, the split-off's label `e₀ ∉ E(G − v)`. -/
def KTReductionStep [DecidableEq β] (n : ℕ) (G G' : Graph α β) : Prop :=
  G'.IsMinimalKDof n 0 ∧
    ((∃ (v a b : α) (eₐ e_b e₀ : β), v ∈ V(G) ∧ a ≠ v ∧ b ≠ v ∧ eₐ ≠ e_b ∧
        G.IsLink eₐ v a ∧ G.IsLink e_b v b ∧ (∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b) ∧
        e₀ ∉ E(G.removeVertex v) ∧ G' = G.splitOff v a b e₀) ∨
      (∃ (H : Graph α β) (r : α), H.IsProperRigidSubgraph G n ∧ r ∈ V(H) ∧
        G' = G.rigidContract H r))

/-- The double edge on two vertices. -/
def IsDoubleEdge (G : Graph α β) : Prop :=
  ∃ x y e f, x ≠ y ∧ e ≠ f ∧ V(G) = {x, y} ∧ E(G) = {e, f} ∧ G.IsLink e x y ∧ G.IsLink f x y

/-- S22 (KT Theorem 4.9 (i)) without `hfresh`, from `minimal_kdof_reduction'`. -/
theorem minimal_kdof_reduction_sequence [DecidableEq β] [Finite α] [Finite β] {n : ℕ}
    (hD : 3 ≤ bodyBarDim n) (G : Graph α β) (hG : G.IsMinimalKDof n 0) (hV : 2 ≤ V(G).ncard) :
    ∃ Gm : Graph α β, Relation.ReflTransGen (KTReductionStep n) G Gm ∧ IsDoubleEdge Gm := by
  have hD2 : 2 ≤ bodyBarDim n := le_trans (by norm_num) hD
  have : NeZero (bodyHingeMult n) := ⟨by rw [bodyHingeMult]; omega⟩
  have hbase : ∀ G : Graph α β, G.IsMinimalKDof n 0 → V(G).ncard = 2 →
      ∃ Gm, Relation.ReflTransGen (KTReductionStep n) G Gm ∧ IsDoubleEdge Gm := by
    intro G hG hV2
    have hne : V(G).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
    rcases isMinimalKDof_ncard_le_two_trichotomy hD2 hG hne hV2.le with
      ⟨-, hk⟩ | ⟨-, -, -, -, -, -, -, hk⟩ | ⟨x, y, e, f, hxy, hef, hVG, hEG, he, hf, -⟩
    · rw [hV2] at hk; push_cast at hk; omega
    · omega
    · exact ⟨G, .refl, x, y, e, f, hxy, hef, hVG, hEG, he, hf⟩
  refine minimal_kdof_reduction' hD
    (P := fun G => ∃ Gm, Relation.ReflTransGen (KTReductionStep n) G Gm ∧ IsDoubleEdge Gm)
    hbase ?_ ?_ G hG hV
  · intro G v a b eₐ e_b hG hnp hvG hav hbv haV hbV heab hla hlb hdeg hP
    have hea : eₐ ∉ E(G.removeVertex v) :=
      (notMem_edgeSet_removeVertex_iff hla hlb hdeg).mpr (Or.inr (Or.inl rfl))
    obtain ⟨Gm, hGm, hdbl⟩ := hP eₐ hea
    have h2 : 2 ≤ V(G).ncard := by
      have hsub : ({v, a} : Set α) ⊆ V(G) :=
        Set.insert_subset hvG (Set.singleton_subset_iff.mpr haV)
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      rwa [Set.ncard_pair hav.symm] at this
    rcases eq_or_lt_of_le h2 with h2 | h3
    · exact hbase G hG h2.symm
    have hmin := splitOff_isMinimalKDof' hD2 h3 hav hbv hla hlb hdeg hea hG hnp
    exact ⟨Gm, .head ⟨hmin, .inl ⟨v, a, b, eₐ, e_b, eₐ, hvG, hav, hbv, heab, hla, hlb, hdeg, hea,
      rfl⟩⟩ hGm, hdbl⟩
  · intro G hG hV3 ⟨H, hH⟩ IH
    obtain ⟨r, hr⟩ := hH.vertexSet_nonempty
    have hsub : V(H) ⊆ V(G) := hH.1.1.vertexSet_mono
    have hcount := rigidContract_vertexSet_ncard (G := G) hr hsub
    have hH2 := hH.2.1
    have hlt : V(H).ncard < V(G).ncard := Set.ncard_lt_ncard hH.2.2 (Set.toFinite _)
    have hmin := rigidContract_isMinimalKDof hG hH hr
    obtain ⟨Gm, hGm, hdbl⟩ := IH _ hmin (by omega) (by omega)
    exact ⟨Gm, .head ⟨hmin, .inr ⟨H, r, hH, hr, rfl⟩⟩ hGm, hdbl⟩

end Graph.Recon41Reduction

#print axioms Graph.Recon41Reduction.splitOff_deficiency_ge'
#print axioms Graph.Recon41Reduction.splitOff_isMinimalKDof'
#print axioms Graph.Recon41Reduction.minimal_kdof_reduction'
#print axioms Graph.Recon41Reduction.minimal_kdof_reduction_of'
#print axioms Graph.Recon41Reduction.minimal_kdof_reduction_of_one_label
#print axioms Graph.Recon41Reduction.minimal_kdof_reduction_sequence
