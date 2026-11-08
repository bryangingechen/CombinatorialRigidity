import CombinatorialRigidity

/-!
# Phase 43c, SPRIME's pin: Theorem S′ at `d = 3` as a spike, and the liveness walk

Banked at SPRIME's pin (`notes/Phase43c.md` item 2, 2026-11-08), written against HEAD
`2b010699` (43c's slice 1). Primed names, and the prefix `SprimeSpike.tr` for the transported
constants, so it still runs after the slices land; the walk names landed constants by literals,
and one absent after a slice is reported, not an error. Run from the repo root:

  lake lean notes/pencil-natural/SprimeSpike.lean

(at the pin: no error, no warning, about a minute), and pipe the output to
`notes/pencil-natural/sprime_walk.py` for the blueprint side of the walk and the sweep.

1. **NEW-1** (`Graph.exists_deficiency_three_induce_eq_zero_of_deficiency_two_lt'`, the body of
   `Graph.deficiencyMerged_two_add_two_le_of_three_le` extracted), **NEW-2**
   (`Graph.IsOpenEar.exists_additiveCoreAt_of_deficiency_induce_eq_zero'`,
   `Graph.IsOpenEar.exists_additiveCoreAt_of_partitionDef_nonpos` less its first step), and
   **S′ at `d = 3`** (`Graph.IsX0Graph.exists_additiveCore'`: the blocking hypothesis on
   `Graph.ChainUsable'`, which drops the `k = 2` merged-equality and the `k = 1` split-off
   disjuncts; the conclusion unchanged), with no `sorry`, on the standard three axioms. Each
   landed form is its spike's type with the changed constants mapped (`#sprime_mapped_same`).
2. **The coverage on S′**: `Graph.X0Reduces'` (the landed clauses less `openEarTwo` and
   `splitOff`), its attainment (the landed proof less two arms), the chain step less its two
   arms, and `Graph.IsX0Graph.x0Reduces_of_sparse`'s source elaborated against S′.
3. **Transport**: every landed constant that depends on a changed one is re-added with the
   changed constants replaced (`sprimeMap`), and the kernel re-checks its landed proof term. The
   four main results transport, their transported types are the landed ones (`SAME TYPE ...:
   true`), on the standard three axioms; so their statements stay byte-identical, and the cut,
   cycle and contraction reductions use only the kept clauses.
4. **The liveness walk** (`#sprime_walk`), before against after over the whole project, with the
   zone `D` of the deletions and the roots outside it: at the pin, 18 DEAD, 3 ORPHAN, 23
   UNREACHED (reached by no root before SPRIME: pinned nodes hold them, and four loose ones
   predate it), 17 MAPPED, 26 RECHECKED.
5. **The slices** (`#sprime_slices`): slice B deletes 10 constants with no surviving user, and
   orphans exactly slice C's 13; slice C deletes those with no surviving user, and orphans none.
   After the pin the PI added the `d = 3` core bound's two declarations to slice B (12 in all,
   `notes/Phase43c.md` item 4); they had no user, so they orphan nothing. Once slice A landed, the
   orphans also list NEW-1 and NEW-2: the after-world reads S′ as the spike's primed form, which
   uses the primed copies; the landed S′ uses the landed ones.
-/

open scoped Graph

/-! ## NEW-1 -/

namespace Graph

variable {α β : Type*}

/-- NEW-1, as a spike. -/
theorem exists_deficiency_three_induce_eq_zero_of_deficiency_two_lt' [Finite α] [Finite β]
    {G : Graph α β}
    (hSv : ∀ X ⊆ V(G), 2 ≤ X.ncard → 1 ≤ (G.induce X).partitionDef 2 id) {a b : α}
    (ha : a ∈ V(G)) (hb : b ∈ V(G)) (hab : a ≠ b) (hnadj : ¬ G.Adj a b)
    (hlt : G.deficiency 2 < G.deficiencyMerged 2 a b + 2) :
    ∃ Z ⊆ V(G), a ∈ Z ∧ b ∈ Z ∧ 3 ≤ Z.ncard ∧ (G.induce Z).deficiency 3 = 0 := by
  have : Nonempty (α → α) := ⟨id⟩
  have hnn := partitionDef_induce_id_nonneg hSv
  have : Nonempty {f : α → α // f a = f b} := ⟨⟨fun _ => a, rfl⟩⟩
  obtain ⟨⟨f, hfab⟩, hf⟩ := exists_eq_ciSup_of_finite
    (f := fun f : {f : α → α // f a = f b} => G.partitionDef 2 f.1)
  rw [← Graph.deficiencyMerged] at hf
  set Z : Set α := {w ∈ V(G) | f w = f a} with hZ
  have hK := partitionDef_add_partitionDef_induce_id_le (G := G) (n := 2) f ha
    (fun Y hY hne => hnn Y (hY.trans Set.sdiff_subset) hne)
  have hid := G.partitionDef_le_deficiency 2 id
  have hZ1 : (G.induce Z).partitionDef 2 id ≤ 1 := by linarith
  have hZV : Z ⊆ V(G) := fun w hw => hw.1
  have haZ : a ∈ Z := ⟨ha, rfl⟩
  have hbZ : b ∈ Z := ⟨hb, hfab.symm⟩
  have hZ2 : 2 ≤ Z.ncard := by
    have := Set.ncard_le_ncard (Set.pair_subset haZ hbZ) (Set.toFinite _)
    rwa [Set.ncard_pair hab] at this
  rcases Nat.lt_or_ge Z.ncard 3 with hZ3 | hZ3
  · -- `Z = {a, b}`, a pair with no edge, has `s = 3`
    exfalso
    have hZab : Z = {a, b} := (Set.eq_of_subset_of_ncard_le (Set.pair_subset haZ hbZ)
      (by rw [Set.ncard_pair hab]; omega) (Set.toFinite _)).symm
    have hbna : b ∉ ({a} : Set α) := fun h' => hab (Set.mem_singleton_iff.mp h').symm
    have hval := partitionDef_induce_insert (G := G) (n := 2) hbna id
    rw [ite_eq_right (by simpa using hbna), bodyBarDim_two,
      partitionDef_induce_singleton_id] at hval
    have hT : ({e | ∃ y ∈ ({a} : Set α), G.IsLink e b y ∧ id y ≠ id b} : Set β) = ∅ := by
      ext e
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, exists_eq_left,
        Set.mem_empty_iff_false, iff_false, not_and]
      exact fun hl _ => hnadj ⟨e, hl.symm⟩
    rw [hT, Set.ncard_empty] at hval
    push_cast at hval
    rw [hZab, Set.pair_comm] at hZ1
    linarith
  · exact ⟨Z, hZV, haZ, hbZ, hZ3,
      deficiency_three_induce_eq_zero_of_tight (fun Y hY => hSv Y (hY.trans hZV)) hZ3 hZ1⟩

/-- `lem:deficiency-two-body-chain`'s current statement, from NEW-1 (if the PI keeps it). -/
theorem deficiencyMerged_two_add_two_le' [Finite α] [Finite β] {G : Graph α β}
    (hSv : ∀ X ⊆ V(G), 2 ≤ X.ncard → 1 ≤ (G.induce X).partitionDef 2 id) {a b : α}
    (ha : a ∈ V(G)) (hb : b ∈ V(G)) (hab : a ≠ b) (hnadj : ¬ G.Adj a b)
    (hδ : G.deficiencyMerged 3 a b ≠ G.deficiency 3) :
    G.deficiencyMerged 2 a b + 2 ≤ G.deficiency 2 := by
  by_contra hlt
  obtain ⟨Z, hZV, haZ, hbZ, -, hZd⟩ :=
    exists_deficiency_three_induce_eq_zero_of_deficiency_two_lt' hSv ha hb hab hnadj
      (not_le.mp hlt)
  exact hδ (deficiencyMerged_eq_deficiency_of_mem (by decide) hZV hZd haZ hbZ)

end Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

/-! ## NEW-2 -/

/-- NEW-2, as a spike: `exists_additiveCoreAt_of_partitionDef_nonpos` less its first step. -/
theorem _root_.Graph.IsOpenEar.exists_additiveCoreAt_of_deficiency_induce_eq_zero'
    [Finite α] [Finite β] {G : Graph α β}
    (hG : G.IsX0Graph) {n : ℕ} (hD : 3 ≤ Graph.bodyBarDim n)
    (hSv : ∀ X ⊆ V(G), 2 ≤ X.ncard → 1 ≤ (G.induce X).partitionDef 2 id)
    {V₁ : Set α} {k : ℕ} {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β}
    (hear : G.IsOpenEar V₁ x a b e) (hk : 2 ≤ k) {Y : Set α} (hYV₁ : Y ⊆ V₁)
    (hY2 : 2 ≤ Y.ncard) (hYd : (G.induce Y).deficiency n = 0) :
    ∃ W r, x ⟨0, by omega⟩ ∉ W ∧ r ∈ W ∧ W ⊂ V(G) ∧ 2 ≤ W.ncard ∧
      (G.induce W).deficiency n = 0 ∧
      (G.induce W).deficiency 2 + (G.rigidContract (G.induce W) r).deficiency 2 ≤
        G.deficiency 2 ∧
      ∀ u ∉ W, ∀ c₁ ∈ W, ∀ c₂ ∈ W, G.Adj u c₁ → G.Adj u c₂ → c₁ = c₂ := by
  have := hG.simple
  have := hG.simple.toLoopless
  set i₁ : Fin k := ⟨0, by omega⟩ with hi₁
  set i₂ : Fin k := ⟨1, by omega⟩ with hi₂
  have hV₁ : V₁ ⊆ V(G) := hear.cover ▸ Set.subset_union_left
  -- the links at `x 0` go to `a` and `x 1`
  have hl₁ : G.IsLink (e 0) (x i₁) a := by
    have := hear.isLink_first
    rw [pathVertex_eq_of_val_eq_succ a x b (i := i₁) (by simp [hi₁])] at this
    exact this.symm
  have hl₂ : G.IsLink (e 1) (x i₁) (x i₂) := by
    have := hear.isLink 1
    rwa [pathVertex_eq_of_val_eq_succ a x b (i := i₁) (by simp [hi₁]; omega),
      pathVertex_eq_of_val_eq_succ a x b (i := i₂) (by simp [hi₂]; omega)] at this
  have hnbr : ∀ c, G.Adj (x i₁) c → c = a ∨ c = x i₂ := by
    rintro c ⟨f, hf⟩
    rcases hear.isLink_interior i₁ hf with rfl | rfl
    · rw [show i₁.castSucc = 0 from Fin.ext (by simp [hi₁])] at hf
      exact Or.inl (hf.right_unique hl₁)
    · have h1 : i₁.succ = 1 := by
        ext
        simp only [Fin.val_succ, hi₁, Fin.val_one', Nat.mod_eq_of_lt (show 1 < k + 1 by omega)]
      rw [h1] at hf
      exact Or.inr (hf.right_unique hl₂)
  refine hG.exists_additiveCore_of_rigidAt hD hSv (X₀ := {x i₁}) Set.subsingleton_singleton
    (Set.singleton_subset_iff.mpr (hear.cover ▸ Or.inr ⟨i₁, rfl⟩))
    (fun y hy => ⟨hV₁ (hYV₁ hy),
      fun h => hear.notMem i₁ (Set.mem_singleton_iff.mp h ▸ hYV₁ hy)⟩) hY2 hYd
    (fun h => absurd h (Set.singleton_ne_empty _))
    (fun y hy => by rw [Set.mem_singleton_iff.mp hy, hear.degree_eq_two]) ?_ |>.imp
      fun W ⟨r, hWX₀, h⟩ => ⟨r, fun hx => (hWX₀ hx).2 rfl, h⟩
  rintro y hy W hW hW2 hWd c₁ hc₁ c₂ hc₂ h₁ h₂
  rw [Set.mem_singleton_iff] at hy
  subst hy
  -- `x 1` has at most one neighbour in `W`, so it lies outside the rigid set `W`
  have hx₂W : x i₂ ∉ W := by
    intro hx₂
    have h2 := Graph.two_le_degree_of_isKDof_zero (G := G.induce W) (n := n) (by omega)
      hWd hx₂ hW2
    have hlt := Graph.degree_induce_lt_of_adj hx₂ (fun h => (hW h).2 rfl) ⟨e 1, hl₂.symm⟩
    have := hear.degree_eq_two i₂
    omega
  have ha : ∀ c ∈ W, G.Adj (x i₁) c → c = a := fun c hc hadj =>
    (hnbr c hadj).resolve_right fun h => hx₂W (h ▸ hc)
  rw [ha c₁ hc₁ h₁, ha c₂ hc₂ h₂]

/-- `lem:pencil-d-chain-core`'s current statement, from NEW-2: the first step and NEW-2. Its
type is the landed `Graph.IsOpenEar.exists_additiveCoreAt_of_partitionDef_nonpos`'s. -/
theorem _root_.Graph.IsOpenEar.exists_additiveCoreAt_of_partitionDef_nonpos'
    [Finite α] [Finite β] {G : Graph α β}
    (hG : G.IsX0Graph) {n : ℕ} (hD : 3 ≤ Graph.bodyBarDim n)
    (hSv : ∀ X ⊆ V(G), 2 ≤ X.ncard → 1 ≤ (G.induce X).partitionDef 2 id)
    {V₁ : Set α} {k : ℕ} {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β}
    (hear : G.IsOpenEar V₁ x a b e) (hk : 2 ≤ k) (hs : (G.induce V₁).partitionDef n id ≤ 0) :
    ∃ W r, x ⟨0, by omega⟩ ∉ W ∧ r ∈ W ∧ W ⊂ V(G) ∧ 2 ≤ W.ncard ∧
      (G.induce W).deficiency n = 0 ∧
      (G.induce W).deficiency 2 + (G.rigidContract (G.induce W) r).deficiency 2 ≤
        G.deficiency 2 ∧
      ∀ u ∉ W, ∀ c₁ ∈ W, ∀ c₂ ∈ W, G.Adj u c₁ → G.Adj u c₂ → c₁ = c₂ := by
  have hV₁2 : 2 ≤ V₁.ncard := by
    have := Set.ncard_le_ncard (Set.pair_subset hear.left_mem hear.right_mem) (Set.toFinite _)
    rwa [Set.ncard_pair hear.ne] at this
  obtain ⟨Y, hYV₁, hY2, hYd⟩ := Graph.exists_deficiency_induce_eq_zero_of_partitionDef_id_nonpos
    (hear.cover ▸ Set.subset_union_left) hV₁2 hs
  exact hear.exists_additiveCoreAt_of_deficiency_induce_eq_zero' hG hD hSv hk hYV₁ hY2 hYd

/-! ## S′ at `d = 3` -/

/-- The usable chains of S′: `def:pencil-x0-usable-chain` less the `k = 2` merged-equality and the
`k = 1` split-off disjuncts. -/
def _root_.Graph.ChainUsable' (G : Graph α β) (V₁ : Set α) (k : ℕ) (a b : α) : Prop :=
  3 ≤ k ∨
  (k = 2 ∧ ¬ G.Adj a b ∧
    (G.induce V₁).deficiencyMerged 2 a b + 2 ≤ (G.induce V₁).deficiency 2) ∨
  (k = 1 ∧ (G.induce V₁).deficiencyMerged 3 a b = (G.induce V₁).deficiency 3)

variable [Finite α] [Finite β]

/-- **S′ at `d = 3`**, as a spike: `Graph.IsX0Graph.exists_additiveCore` on the weaker blocking
hypothesis `¬ ChainUsable'`, its conclusion unchanged. -/
theorem _root_.Graph.IsX0Graph.exists_additiveCore' {G : Graph α β} (hG : G.IsX0Graph)
    (h2c : ∀ v ∈ V(G), (G.induce (V(G) \ {v})).Connected)
    (hhub : ∃ w ∈ V(G), G.degree w ≠ 2)
    (hS : ∀ X ⊆ V(G), 2 ≤ X.ncard → (G.induce X).deficiency 2 ≠ 0)
    (hblk : ∀ (V₁ : Set α) (k : ℕ) (x : Fin k → α) (a b : α) (e : Fin (k + 1) → β),
      G.IsChain V₁ x a b e → ¬ G.ChainUsable' V₁ k a b) :
    ∃ W r, r ∈ W ∧ W ⊂ V(G) ∧ 2 ≤ W.ncard ∧ (G.induce W).deficiency 3 = 0 ∧
      (G.induce W).deficiency 2 + (G.rigidContract (G.induce W) r).deficiency 2 ≤
        G.deficiency 2 ∧
      ∀ u ∉ W, ∀ c₁ ∈ W, ∀ c₂ ∈ W, G.Adj u c₁ → G.Adj u c₂ → c₁ = c₂ := by
  have hD : 3 ≤ Graph.bodyBarDim 3 := by decide
  have hSv := Graph.one_le_partitionDef_induce_id hS
  by_contra hcore
  -- a chain with two interior bodies has adjacent ends: otherwise it is usable, or its ends lie
  -- in a rigid set of `G[V₁]` (NEW-1), which gives a core avoiding `x 0` (NEW-2)
  have hk2 : ∀ (V₁ : Set α) (x : Fin 2 → α) (a b : α) (e : Fin 3 → β),
      G.IsChain V₁ x a b e → G.Adj a b := by
    intro V₁ x a b e hC
    by_contra hnadj
    have hlt : (G.induce V₁).deficiency 2 < (G.induce V₁).deficiencyMerged 2 a b + 2 :=
      not_le.mp fun h => hblk _ _ _ _ _ _ hC (Or.inr (Or.inl ⟨rfl, hnadj, h⟩))
    have hSv' : ∀ X ⊆ V(G.induce V₁), 2 ≤ X.ncard →
        1 ≤ ((G.induce V₁).induce X).partitionDef 2 id := fun X hX hX2 => by
      have hX' : X ⊆ V₁ := hX
      rw [Graph.induce_induce_of_subset G hX']
      exact hSv X (hX'.trans (hC.cover ▸ Set.subset_union_left)) hX2
    have hnadj' : ¬ (G.induce V₁).Adj a b := fun ⟨f, hf⟩ => hnadj ⟨f, hf.1⟩
    obtain ⟨Z, hZ, -, -, hZ3, hZd⟩ :=
      Graph.exists_deficiency_three_induce_eq_zero_of_deficiency_two_lt' hSv' hC.left_mem
        hC.right_mem hC.ne hnadj' hlt
    have hZV₁ : Z ⊆ V₁ := hZ
    rw [Graph.induce_induce_of_subset G hZV₁] at hZd
    obtain ⟨W, r, -, h⟩ := hC.toIsOpenEar.exists_additiveCoreAt_of_deficiency_induce_eq_zero' hG
      hD hSv le_rfl hZV₁ (by omega) hZd
    exact hcore ⟨W, r, h⟩
  -- `X₀ = {x₀}`: a body of degree two and a rigid set avoiding it give a core
  have hX₀ : ∀ x₀ ∈ V(G), G.degree x₀ = 2 → ∀ Y ⊆ V(G) \ {x₀}, 2 ≤ Y.ncard →
      (G.induce Y).deficiency 3 = 0 → False := by
    intro x₀ hx₀V hx₀2 Y hYx₀ hY2 hYd
    obtain ⟨W, r, -, h⟩ := hG.exists_additiveCore_of_rigidAt hD hSv (X₀ := {x₀})
      Set.subsingleton_singleton (Set.singleton_subset_iff.mpr hx₀V) hYx₀ hY2 hYd
      (fun h => absurd h (Set.singleton_ne_empty x₀))
      (fun y hy => by rw [Set.mem_singleton_iff.mp hy, hx₀2]) (by
        rintro y hy W hW hW2 hWd c₁ hc₁ c₂ hc₂ h₁ h₂
        rw [Set.mem_singleton_iff] at hy
        subst hy
        by_contra hne
        have hWV : W ⊆ V(G) := hW.trans Set.sdiff_subset
        have hyW : y ∉ W := fun h => (hW h).2 rfl
        -- a neighbour of degree two in a rigid set would have degree `≤ 1` there
        have hhub : ∀ c ∈ W, G.Adj y c → 3 ≤ G.degree c := by
          intro c hc hyc
          have h2 := Graph.two_le_degree_of_isKDof_zero (G := G.induce W) (n := 3) (by omega)
            hWd hc hW2
          have hlt := Graph.degree_induce_lt_of_adj hc hyW hyc.symm
          have := hG.two_le_degree c (hWV hc)
          by_contra h3
          omega
        obtain ⟨e₁, he₁⟩ := h₁
        obtain ⟨e₂, he₂⟩ := h₂
        have hC₁ := hG.isChain_one hx₀2 he₁.symm he₂ hne (hhub c₁ hc₁ ⟨e₁, he₁⟩)
          (hhub c₂ hc₂ ⟨e₂, he₂⟩)
        apply hblk _ _ _ _ _ _ hC₁ (Or.inr (Or.inr ⟨rfl, ?_⟩))
        have hWd' : ((G.induce (V(G) \ {y})).induce W).deficiency 3 = 0 := by
          rwa [Graph.induce_induce_of_subset G hW]
        exact Graph.deficiencyMerged_eq_deficiency_of_mem (by omega) hW hWd' hc₁ hc₂)
    exact hcore ⟨W, r, h⟩
  -- `X₀ = ∅`: when `def₃(G) > 0`, a rigid set gives a core
  have hempty : G.deficiency 3 ≠ 0 → ∀ Y ⊆ V(G), 2 ≤ Y.ncard →
      (G.induce Y).deficiency 3 = 0 → False := by
    intro hrig Y hYV hY2 hYd
    obtain ⟨W, r, -, h⟩ := hG.exists_additiveCore_of_rigidAt hD hSv (X₀ := ∅)
      Set.subsingleton_empty (Set.empty_subset _) (by simpa using hYV) hY2 hYd (fun _ => hrig)
      (by simp) (by simp)
    exact hcore ⟨W, r, h⟩
  by_cases hadj : ∃ v w, G.degree v = 2 ∧ G.degree w = 2 ∧ G.Adj v w
  · -- two adjacent bodies of degree two: their chain has two interior bodies and adjacent ends,
    -- and its `4`-cycle is rigid
    obtain ⟨v', w', hv'2, hw'2, hv'w'⟩ := hadj
    obtain ⟨V₁', k', x', a', b', e', hC', hv'x'⟩ := hG.exists_isChain h2c hhub hv'2
    have h2 := hC'.two_le_of_adj hv'x' hv'w' hw'2
    have h3 : k' < 3 := Nat.lt_of_not_le fun h => hblk _ _ _ _ _ _ hC' (Or.inl h)
    obtain rfl : k' = 2 := by omega
    obtain ⟨hcycV, hcyc2, hcycd⟩ :=
      hC'.toIsOpenEar.deficiency_three_induce_cycle (hk2 _ _ _ _ _ hC') hSv
    by_cases hrig : G.deficiency 3 = 0
    · obtain ⟨x₀, hx₀V, hx₀2, hx₀s⟩ :=
        hG.exists_degree_eq_two_notMem hSv (s := {x' 0, x' 1})
          ((Set.ncard_pair_le _ _).trans (by norm_num))
      refine hX₀ x₀ hx₀V hx₀2 _ (fun y hy => ⟨hcycV hy, ?_⟩) hcyc2 hcycd
      rintro rfl
      rcases hy with rfl | rfl | rfl | rfl
      · exact absurd hx₀2 (by have := hC'.three_le_degree_left; omega)
      · exact hx₀s (Or.inl rfl)
      · exact hx₀s (Or.inr rfl)
      · exact absurd hx₀2 (by have := hC'.three_le_degree_right; omega)
    · exact hempty hrig _ hcycV hcyc2 hcycd
  · -- no two bodies of degree two adjacent
    push Not at hadj
    have hhubs : ∀ v w, G.degree v = 2 → G.Adj v w → 3 ≤ G.degree w := by
      intro v w hv2' hvw
      have := hG.two_le_degree w hvw.right_mem
      by_contra h3
      exact hadj v w hv2' (by omega) hvw
    by_cases hrig : G.deficiency 3 = 0
    · obtain ⟨v, hv, hv2, -⟩ := hG.exists_degree_eq_two_notMem hSv (s := ∅) (by simp)
      have hval := hG.partitionDef_three_induce_diff_nonpos hhubs hv hv2
      have hcard : 2 ≤ (V(G) \ {v}).ncard := by
        have h3 : 3 ≤ V(G).ncard := hG.three_le_ncard_vertexSet
        rw [Set.ncard_sdiff_singleton_of_mem hv]; omega
      obtain ⟨Y, hYs, hY2, hYd3⟩ :=
        Graph.exists_deficiency_induce_eq_zero_of_partitionDef_id_nonpos
          (G := G) (n := 3) Set.sdiff_subset hcard hval
      exact hX₀ v hv hv2 Y hYs hY2 hYd3
    · have hpos : 0 < G.deficiency 3 := by
        have := Graph.deficiency_nonneg G 3 hG.connected.nonempty
        omega
      exact hcore (hG.exists_core_of_deficiency_three_pos le_rfl hSv hhubs hpos)

end CombinatorialRigidity.Molecular

/-! ## The coverage on S′: `X0Reduces` less `openEarTwo` and `splitOff` -/

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

/-- `def:pencil-x0-reduces` less the clauses `openEarTwo` and `splitOff`: eleven constructors,
each the landed one's, verbatim. -/
inductive _root_.Graph.X0Reduces' (P : Graph α β → Prop) (G : Graph α β) : Prop
  | flat (hdef : G.deficiency 2 = G.deficiency 3)
  | cutVertex {V₁ V₂ : Set α} {v : α} (hcover : V₁ ∪ V₂ = V(G)) (hoverlap : V₁ ∩ V₂ = {v})
      (hsep : ∀ e x y, G.IsLink e x y → (x ∈ V₁ ∧ y ∈ V₁) ∨ (x ∈ V₂ ∧ y ∈ V₂))
      (h₁ : P (G.induce V₁)) (h₂ : P (G.induce V₂))
  | bridgePath {V₁ V₂ : Set α} {k : ℕ} {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β}
      (hcover : V(G) = V₁ ∪ Set.range x ∪ V₂) (hdisj : Disjoint V₁ V₂)
      (hxV₁ : ∀ i, x i ∉ V₁) (hxV₂ : ∀ i, x i ∉ V₂) (hinj : Function.Injective x)
      (ha : a ∈ V₁) (hb : b ∈ V₂)
      (hpath : ∀ i : Fin (k + 1),
        G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
      (hsep : ∀ f u v, G.IsLink f u v → (∀ i, f ≠ e i) →
        (u ∈ V₁ ∧ v ∈ V₁) ∨ (u ∈ V₂ ∧ v ∈ V₂))
      (h₁ : P (G.induce V₁)) (h₂ : P (G.induce V₂))
  | cycle {k : ℕ} {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β} {f : β}
      (hk : 1 ≤ k) (hcover : V(G) = {a, b} ∪ Set.range x) (hinj : Function.Injective x)
      (hxa : ∀ i, x i ≠ a) (hxb : ∀ i, x i ≠ b) (hab : a ≠ b) (hf : G.IsLink f a b)
      (hpath : ∀ i : Fin (k + 1),
        G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
      (honly : ∀ g u w, G.IsLink g u w → (∀ i, g ≠ e i) → g = f)
  | openEar {V₁ : Set α} {k : ℕ} {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β}
      (hear : G.IsOpenEar V₁ x a b e) (hk : 5 ≤ k) (h₁ : P (G.induce V₁))
  | openEarFour {V₁ : Set α} {x : Fin 4 → α} {a b : α} {e : Fin 5 → β}
      (hear : G.IsOpenEar V₁ x a b e) (h₁ : P (G.induce V₁))
      (h₂ : P (G.splitOff (x 1) (x 0) (x 2) (e 1)))
  | openEarThree {V₁ : Set α} {x : Fin 3 → α} {a b : α} {e : Fin 4 → β}
      (hear : G.IsOpenEar V₁ x a b e) (h₁ : P (G.induce V₁))
      (h₂ : P (G.splitOff (x 1) (x 0) (x 2) (e 1)))
  | openEarTwoSplitOff {V₁ : Set α} {x : Fin 2 → α} {a b : α} {e : Fin 3 → β}
      (hear : G.IsOpenEar V₁ x a b e) (hnadj : ¬ G.Adj a b) (h₁ : P (G.induce V₁))
      (h₂ : P (G.splitOff (x 1) (x 0) b (e 1)))
      (hδ₂ : (G.induce V₁).deficiencyMerged 2 a b + 2 ≤ (G.induce V₁).deficiency 2)
  | openEarOne {V₁ : Set α} {x : Fin 1 → α} {a b : α} {e : Fin 2 → β}
      (hear : G.IsOpenEar V₁ x a b e) (hnadj : ¬ G.Adj a b) (h₁ : P (G.induce V₁))
      (hdef : (G.induce V₁).deficiency 3 ≤ G.deficiency 3)
      (hδ₂ : (G.induce V₁).deficiencyMerged 2 a b + 2 ≤ (G.induce V₁).deficiency 2)
  | rigidContract (htec : G.TwoEdgeConnected) {W : Set α} {r : α} (hr : r ∈ W)
      (hWss : W ⊂ V(G)) (hW2 : 2 ≤ W.ncard) (hdef : (G.induce W).deficiency 2 = 0)
      (hatt : ∀ u ∉ W, ∀ c₁ ∈ W, ∀ c₂ ∈ W, G.Adj u c₁ → G.Adj u c₂ → c₁ = c₂)
      (hc : P (G.rigidContract (G.induce W) r))
  | additiveContract (htec : G.TwoEdgeConnected) {W : Set α} {r : α} (hr : r ∈ W)
      (hWss : W ⊂ V(G)) (hW2 : 2 ≤ W.ncard) (hdef3 : (G.induce W).deficiency 3 = 0)
      (hadd : (G.induce W).deficiency 2 + (G.rigidContract (G.induce W) r).deficiency 2 ≤
        G.deficiency 2)
      (hatt : ∀ u ∉ W, ∀ c₁ ∈ W, ∀ c₂ ∈ W, G.Adj u c₁ → G.Adj u c₂ → c₁ = c₂)
      (hH : P (G.induce W)) (hc : P (G.rigidContract (G.induce W) r))

/-- `thm:pencil-x0-reduction-attains`(1) on the eleven clauses: the landed proof less two arms. -/
theorem _root_.Graph.X0Reduces'.x0Attains [Infinite K] [Finite α] [Finite β]
    {P : Graph α β → Prop} {G : Graph α β} (hG : G.IsX0Graph)
    (hP : ∀ G' : Graph α β, P G' → G'.X0Attains K) (h : G.X0Reduces' P) : G.X0Attains K := by
  cases h with
  | flat hdef =>
    exact Graph.x0Attains_of_deficiency_two_eq_three hG.connected hG.simple
      hG.three_le_ncard_closedNbhd hdef
  | cutVertex hcover hoverlap hsep h₁ h₂ =>
    exact Graph.X0Attains.of_cutVertex hG hcover hoverlap hsep (hP _ h₁) (hP _ h₂)
  | bridgePath hcover hdisj hxV₁ hxV₂ hinj ha hb hpath hsep h₁ h₂ =>
    exact Graph.X0Attains.of_bridgePath hG hcover hdisj hxV₁ hxV₂ hinj ha hb hpath hsep
      (hP _ h₁) (hP _ h₂)
  | cycle hk hcover hinj hxa hxb hab hf hpath honly =>
    exact Graph.X0Attains.of_cycle hk hcover hinj hxa hxb hab hf hpath honly
  | openEar hear hk h₁ =>
    exact Graph.X0Attains.of_openEar hG hk hear.cover hear.inj hear.notMem hear.left_mem
      hear.right_mem hear.ne hear.isLink hear.sep (hP _ h₁)
  | openEarFour hear h₁ h₂ =>
    exact Graph.X0Attains.of_openEar_four hG hear.cover hear.inj hear.notMem hear.left_mem
      hear.right_mem hear.ne hear.isLink hear.sep (hP _ h₁) (hP _ h₂)
  | openEarThree hear h₁ h₂ =>
    exact Graph.X0Attains.of_openEar_three hG hear.cover hear.inj hear.notMem hear.left_mem
      hear.right_mem hear.ne hear.isLink hear.sep (hP _ h₁) (hP _ h₂)
  | openEarTwoSplitOff hear hnadj h₁ h₂ hδ₂ =>
    exact Graph.X0Attains.of_openEar_two_of_splitOff hG hear.cover hear.notMem hear.left_mem
      hear.right_mem hear.isLink hear.sep hnadj (hP _ h₁) (hP _ h₂) hδ₂
  | openEarOne hear hnadj h₁ hdef hδ₂ =>
    exact Graph.X0Attains.of_openEar_one hG hear.cover hear.notMem hear.left_mem hear.right_mem
      hear.isLink hear.sep hnadj (hP _ h₁) hdef hδ₂
  | rigidContract htec hr hWss hW2 hdef hatt hc =>
    exact Graph.X0Attains.of_rigidContract hG htec hr hWss hW2 hdef hatt (hP _ hc)
  | additiveContract htec hr hWss hW2 hdef3 hadd hatt hH hc =>
    exact Graph.X0Attains.of_additiveContract hG htec hr hWss hW2 hdef3 hadd hatt
      (hP _ hH) (hP _ hc)

variable [Finite α] [Finite β]

/-- `lem:pencil-x0-chain-reduces` on S′'s usable chains: the landed proof less the `k = 2`
merged-equality and the `k = 1` split-off arms. -/
theorem _root_.Graph.IsChain.x0Reduces_of_chainUsable' {G : Graph α β} (hG : G.IsX0Graph)
    (h2c : ∀ v ∈ V(G), (G.induce (V(G) \ {v})).Connected)
    (hSv : ∀ X ⊆ V(G), 2 ≤ X.ncard → 1 ≤ (G.induce X).partitionDef 2 id)
    {V₁ : Set α} {k : ℕ} {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β}
    (hC : G.IsChain V₁ x a b e) (hu : G.ChainUsable' V₁ k a b) : G.X0Reduces' G.X0Below := by
  have hear := hC.toIsOpenEar
  have h₁ : G.X0Below (G.induce V₁) :=
    ⟨hC.isX0Graph_induce hG h2c, hear.ncard_lt hC.one_le⟩
  have hxV : ∀ i, x i ∈ V(G) := fun i => hear.cover ▸ Set.mem_union_right _ ⟨i, rfl⟩
  rcases hu with hk | ⟨rfl, hnadj, hδ₂⟩ | ⟨rfl, hδ⟩
  · rcases Nat.lt_or_ge k 5 with hk5 | hk5
    · obtain rfl | rfl : k = 3 ∨ k = 4 := by omega
      · exact .openEarThree hear h₁
          ⟨hear.isX0Graph_splitOff_three hG, Graph.splitOff_vertexSet_ncard_lt (hxV 1)⟩
      · exact .openEarFour hear h₁
          ⟨hear.isX0Graph_splitOff_four hG, Graph.splitOff_vertexSet_ncard_lt (hxV 1)⟩
    · exact .openEar hear hk5 h₁
  · exact .openEarTwoSplitOff hear hnadj h₁
      ⟨hear.isX0Graph_splitOff_orbit hG, Graph.splitOff_vertexSet_ncard_lt (hxV 1)⟩ hδ₂
  · obtain ⟨hnadj, hδ₂⟩ := hear.not_adj_and_two_le_pairDelta_two hSv
    exact .openEarOne hear hnadj h₁ (hear.deficiency_induce_le hδ) hδ₂

/-- `Graph.IsX0Graph.x0Reduces_of_sparse`'s source, verbatim but for the primes: the landed
consumer of Theorem S elaborates against S′. -/
theorem _root_.Graph.IsX0Graph.x0Reduces_of_sparse' {G : Graph α β} (hG : G.IsX0Graph)
    (h2c : ∀ v ∈ V(G), (G.induce (V(G) \ {v})).Connected) (htec : G.TwoEdgeConnected)
    (hhub : ∃ w ∈ V(G), G.degree w ≠ 2)
    (hS : ∀ X ⊆ V(G), 2 ≤ X.ncard → (G.induce X).deficiency 2 ≠ 0) :
    G.X0Reduces' G.X0Below := by
  have hSv := Graph.one_le_partitionDef_induce_id hS
  by_cases hu : ∃ (V₁ : Set α) (k : ℕ) (x : Fin k → α) (a b : α) (e : Fin (k + 1) → β),
      G.IsChain V₁ x a b e ∧ G.ChainUsable' V₁ k a b
  · obtain ⟨V₁, k, x, a, b, e, hC, hCu⟩ := hu
    exact hC.x0Reduces_of_chainUsable' hG h2c hSv hCu
  · push Not at hu
    obtain ⟨W, r, hr, hWss, hW2, hdef3, hadd, hatt⟩ := hG.exists_additiveCore' h2c hhub hS hu
    exact .additiveContract htec hr hWss hW2 hdef3 hadd hatt
      ⟨Graph.isX0Graph_induce_of_deficiency_eq_zero hG.simple hWss.subset hW2 (by decide) hdef3,
        Set.ncard_lt_ncard hWss⟩
      ⟨Graph.isX0Graph_rigidContract_induce hG htec hr hWss hatt,
        Graph.rigidContract_vertexSet_ncard_lt hWss.subset hW2⟩

end CombinatorialRigidity.Molecular

/-! ## Transport: the landed proof terms, re-checked by the kernel against the new objects

`#sprime_transport c` re-adds every project constant that `c` depends on and that mentions a
changed constant (transitively), with each changed constant replaced by its spike form
(`sprimeMap`), under the prefix `SprimeSpike.tr`. A dependency that cannot be transported (a
`cases` on the landed `X0Reduces`, a use of `openEarTwo` or `splitOff`) is an error naming it; a
companion of a mapped declaration (its recursor, its constructors, its equation lemmas) is
regenerated with it and read as itself. The
names are literals, not resolved: after slice B the landed forms are the new ones, and transport
reads them unchanged. -/

open Lean Meta Elab Command

-- the kernel checks each transported declaration synchronously, so a rejection is thrown and named
set_option Elab.async false

/-- A kept constructor of `X0Reduces` and its spike form. -/
def sprimeCtor (s : String) : Name × Name :=
  (`Graph.X0Reduces ++ .mkSimple s, `Graph.X0Reduces' ++ .mkSimple s)

/-- The changed constants and their spike forms. -/
def sprimeMap : List (Name × Name) :=
  [(`Graph.X0Reduces, `Graph.X0Reduces'), sprimeCtor "flat",
    sprimeCtor "cutVertex", sprimeCtor "bridgePath", sprimeCtor "cycle", sprimeCtor "openEar",
    sprimeCtor "openEarFour", sprimeCtor "openEarThree", sprimeCtor "openEarTwoSplitOff",
    sprimeCtor "openEarOne", sprimeCtor "rigidContract", sprimeCtor "additiveContract",
    (`Graph.X0Reduces.x0Attains, `Graph.X0Reduces'.x0Attains),
    (`Graph.ChainUsable, `Graph.ChainUsable'),
    (`Graph.IsChain.x0Reduces_of_chainUsable, `Graph.IsChain.x0Reduces_of_chainUsable'),
    (`Graph.IsX0Graph.exists_additiveCore, `Graph.IsX0Graph.exists_additiveCore'),
    (`Graph.IsOpenEar.exists_additiveCoreAt_of_partitionDef_nonpos,
      `Graph.IsOpenEar.exists_additiveCoreAt_of_partitionDef_nonpos')]

/-- A constant of a project module (not of this file). -/
def sprimeIsProjMod (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!.getRoot == `CombinatorialRigidity
  | none => false

/-- The project constants that `roots` depend on, in post-order (dependencies first), through
project constants, not expanding a constant of `stop` (the mapped ones); a cycle (an inductive type
and its constructors) is cut where it closes. -/
def sprimePostOrder (env : Environment) (roots : List Name)
    (stop : Std.HashMap Name (Option Name)) : Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut out : Array Name := #[]
  let mut stack : Array (Name × Bool) := (roots.map (·, false)).toArray.reverse
  while !stack.isEmpty do
    let (n, done) := stack.back!
    stack := stack.pop
    if done then
      out := out.push n
      continue
    if seen.contains n then continue
    seen := seen.insert n
    stack := stack.push (n, true)
    if stop.contains n then continue
    if let some ci := env.find? n then
      for m in ci.getUsedConstantsAsSet do
        if m != n && !seen.contains m && sprimeIsProjMod env m then stack := stack.push (m, false)
  return out

/-- The initial transport state: the changed constants, mapped. -/
def sprimeInit : Std.HashMap Name (Option Name) :=
  sprimeMap.foldl (fun m (a, b) => m.insert a (some b)) {}

/-- A companion of a mapped declaration: a constant, not itself mapped, whose name extends a
mapped one (`Graph.X0Reduces.rec`, `Graph.X0Reduces.openEarTwo`, `Graph.ChainUsable.eq_1`). -/
def sprimeCompanion (c : Name) : Bool :=
  !sprimeInit.contains c && sprimeMap.any fun (a, _) => a != c && a.isPrefixOf c

/-- Transport every constant of `order` (post-order) that mentions a mapped constant, updating the
map `mp` (a constant's transported name, or `none` if it needs none). -/
def sprimeTransportOrder (order : Array Name) (mp₀ : Std.HashMap Name (Option Name)) :
    CommandElabM (Std.HashMap Name (Option Name)) := do
  let mut mp := mp₀
  for c in order do
    if mp.contains c then continue
    -- a companion of a mapped declaration (its recursor, `casesOn`, constructors, equation
    -- lemmas) is regenerated with it: not transported, read as itself
    if sprimeCompanion c then
      mp := mp.insert c none
      continue
    let env ← getEnv
    let some ci := env.find? c | throwError "transport: unknown {c}"
    let need := ci.getUsedConstantsAsSet.toList.any fun m => m != c && ((mp[m]?).bind id).isSome
    unless need do
      mp := mp.insert c none
      continue
    let c' := `SprimeSpike.tr ++ c
    unless env.contains c' do
      let m := mp
      let f (e : Expr) : Expr := e.replace fun
        | .const n ls => (m[n]?).bind id |>.map (Expr.const · ls)
        | _ => none
      let decl : Declaration ← match ci with
        | .thmInfo v =>
          let w : TheoremVal :=
            { v with name := c', type := f v.type, value := f v.value, all := [c'] }
          pure (.thmDecl w)
        | .defnInfo v =>
          let w : DefinitionVal :=
            { v with name := c', type := f v.type, value := f v.value, all := [c'] }
          pure (.defnDecl w)
        | _ => throwError "transport: {c} mentions a changed constant and is neither a theorem \
            nor a definition"
      try
        liftCoreM <| addDecl decl
      catch ex =>
        throwError "transport: the kernel rejects {c}: {ex.toMessageData}"
    mp := mp.insert c (some c')
  return mp

elab "#sprime_transport " ids:ident* : command => do
  let roots := ids.toList.map (·.getId)
  let order := sprimePostOrder (← getEnv) roots sprimeInit
  let mp ← sprimeTransportOrder order sprimeInit
  for r in roots do
    logInfo m!"TRANSPORT {r} ↦ {(mp[r]?).bind id}"
  let n : Nat := order.foldl (fun acc c => if ((mp[c]?).bind id).isSome && !sprimeInit.contains c
    then acc + 1 else acc) 0
  logInfo m!"{order.size} project constants in the closure; {n} transported"

#sprime_transport Graph.IsX0Graph.x0Attains Graph.X0Attains.of_twoEdgeConnected

/-! ## The main results through the transport

Each main result is transported (or needs no transport), and its transported type is the landed
one's: the statements stay byte-identical. -/

#sprime_transport CombinatorialRigidity.Molecular.pencil_realization_theorem
  CombinatorialRigidity.Molecular.pencilPair_of_nonempty
  Graph.graded_pencil_conditioned_pair Graph.graded_pencil_realization_theorem

/-- The landed constant and its transported form have one type (universe parameters renamed
positionally); a constant with no transported form is reported as such. -/
elab "#sprime_same " ids:ident* : command => do
  let env ← getEnv
  for i in ids do
    let a := i.getId
    let b := `SprimeSpike.tr ++ a
    let some ca := env.find? a | throwError "unknown {a}"
    match env.find? b with
    | none => logInfo m!"SAME TYPE {a}: no transported form (it mentions no changed constant)"
    | some cb =>
      let ok := ca.levelParams.length == cb.levelParams.length &&
        ca.type == cb.type.instantiateLevelParams cb.levelParams
          (ca.levelParams.map Level.param)
      logInfo m!"SAME TYPE {a} ~ {b}: {ok}"

#sprime_same CombinatorialRigidity.Molecular.pencil_realization_theorem
  CombinatorialRigidity.Molecular.pencilPair_of_nonempty
  Graph.graded_pencil_conditioned_pair Graph.graded_pencil_realization_theorem
  Graph.IsX0Graph.x0Attains Graph.X0Attains.of_twoEdgeConnected

/-- The landed constant's type, with the changed constants mapped (`sprimeMap`), is the spike
form's: a mapped declaration's signature changes only through the changed constants it names. -/
elab "#sprime_mapped_same " a:ident b:ident : command => do
  let env ← getEnv
  let (na, nb) := (a.getId, b.getId)
  -- a landed constant a slice deleted is reported, as the walk reports it (slice B, 2026-11-08)
  let some ca := env.find? na | logInfo m!"SAME TYPE UP TO THE MAP {na}: absent"
  let some cb := env.find? nb | throwError "unknown {nb}"
  let mp := sprimeInit
  let f (e : Expr) : Expr := e.replace fun
    | .const n ls => (mp[n]?).bind id |>.map (Expr.const · ls)
    | _ => none
  let tb := cb.type.instantiateLevelParams cb.levelParams (ca.levelParams.map Level.param)
  let same := ca.levelParams.length == cb.levelParams.length && f ca.type == tb
  -- a proof inside the statement (`x ⟨0, by omega⟩`) may differ as a term: then defeq
  let defeq ← liftTermElabM <| Meta.isDefEq (f ca.type) tb
  logInfo m!"SAME TYPE UP TO THE MAP {na} ~ {nb}: syntactically {same}, defeq {defeq}"

#sprime_mapped_same Graph.IsX0Graph.exists_additiveCore Graph.IsX0Graph.exists_additiveCore'
#sprime_mapped_same Graph.IsChain.x0Reduces_of_chainUsable Graph.IsChain.x0Reduces_of_chainUsable'
#sprime_mapped_same Graph.X0Reduces.x0Attains Graph.X0Reduces'.x0Attains
#sprime_mapped_same Graph.IsOpenEar.exists_additiveCoreAt_of_partitionDef_nonpos
  Graph.IsOpenEar.exists_additiveCoreAt_of_partitionDef_nonpos'
#sprime_mapped_same Graph.deficiencyMerged_two_add_two_le Graph.deficiencyMerged_two_add_two_le'

#print axioms Graph.IsX0Graph.exists_additiveCore'
#print axioms SprimeSpike.tr.CombinatorialRigidity.Molecular.pencil_realization_theorem
#print axioms SprimeSpike.tr.CombinatorialRigidity.Molecular.pencilPair_of_nonempty
#print axioms SprimeSpike.tr.Graph.graded_pencil_conditioned_pair
#print axioms SprimeSpike.tr.Graph.graded_pencil_realization_theorem
#print axioms Graph.exists_deficiency_three_induce_eq_zero_of_deficiency_two_lt'
#print axioms Graph.IsOpenEar.exists_additiveCoreAt_of_deficiency_induce_eq_zero'
#print axioms Graph.IsOpenEar.exists_additiveCoreAt_of_partitionDef_nonpos'
#print axioms Graph.IsX0Graph.x0Reduces_of_sparse'



/-! ## The liveness walk

`D` is the zone where SPRIME deletes: the modules `Pencil.MainComponent.*`, `Pencil.Grade.TheoremS`
and `Induction.SparseDeficiency`. The roots are every constant of a project module outside `D`,
and the two main results inside it (`pencil_realization_theorem`, `pencilPair_of_nonempty`).
*Before* reads every constant's landed body; *after* reads a constant's transported body where it
has one (the spike's form for a mapped one), and a spike constant's own body, so the after-world is
the kernel-checked world of the transport. Reported, one line each, for the script
`notes/pencil-natural/sprime_walk.py`:

* `SPRIME DEAD`: a constant of `D` reached before and not after;
* `SPRIME UNREACHED`: a constant of `D` reached by no root even before (a pin may hold it);
* `SPRIME ORPHAN`: a constant outside `D` with a user before and none after, to a fixpoint (its
  users all dead or orphaned; the roots are recomputed without the orphans);
* `SPRIME MAPPED`: a landed constant whose after-form is the spike's (its statement or proof
  changes);
* `SPRIME RECHECKED`: a landed constant whose source is unchanged and whose proof term the kernel
  re-checked against the mapped ones (the transport).

Each line carries the module and the declaration's line range. Auxiliary constants (recursors,
matchers, equation lemmas, `_`-prefixed components) are followed but not reported. -/

/-- The module of a constant, `none` for one of this file. -/
def sprimeModuleOf (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun idx => env.header.moduleNames[idx.toNat]!

/-- A constant of `D`. -/
def sprimeInD (env : Environment) (n : Name) : Bool :=
  match sprimeModuleOf env n with
  | some m =>
    (`CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent).isPrefixOf m ||
      m == `CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.TheoremS ||
      m == `CombinatorialRigidity.Molecular.Induction.SparseDeficiency
  | none => false

/-- An auxiliary constant: not reported. -/
def sprimeIsAux (env : Environment) (n : Name) : Bool :=
  n.isInternalDetail || isAuxRecursor env n || isNoConfusion env n ||
    (match env.find? n with | some (.recInfo _) => true | _ => false) ||
    (match n with
      | .str _ s => s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "eq_" ||
          s == "ctorIdx" || s.startsWith "ctorElim" || s == "noConfusionType" || s == "below" ||
          s == "ibelow" || s == "brecOn" || s == "binductionOn"
      | _ => true)

/-- The after-world reading of a landed constant: its transported or spike form, if any. -/
def sprimeRead (fwd : Std.HashMap Name (Option Name)) (n : Name) : Name :=
  ((fwd[n]?).bind id).getD n

/-- Reachability from `roots`. With `after`, each landed constant is read by `sprimeRead`, and a
transported or spike name met in a body is mapped back to its landed constant (`bwd`); a spike
constant with no landed counterpart is followed as itself. Returns the reached constants (landed
names, and the spike's new ones). -/
def sprimeReach (env : Environment) (roots : Array Name) (after : Bool)
    (fwd : Std.HashMap Name (Option Name)) (bwd : Std.HashMap Name Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack := roots
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let src := if after then sprimeRead fwd n else n
    if let some ci := env.find? src then
      for m in ci.getUsedConstantsAsSet do
        let m' := if after then bwd.getD m m else m
        let proj := match sprimeModuleOf env m' with
          | some md => md.getRoot == `CombinatorialRigidity
          | none => true
        if proj && !seen.contains m' then stack := stack.push m'
  return seen

/-- The constants a constant's (before or after) body uses, landed names. -/
def sprimeUses (env : Environment) (after : Bool) (fwd : Std.HashMap Name (Option Name))
    (bwd : Std.HashMap Name Name) (n : Name) : Array Name := Id.run do
  let src := if after then sprimeRead fwd n else n
  let some ci := env.find? src | return #[]
  let mut out := #[]
  for m in ci.getUsedConstantsAsSet do
    let m' := if after then bwd.getD m m else m
    if m' != n then out := out.push m'
  return out

def sprimeLine (env : Environment) (tag : String) (n : Name) : CommandElabM String := do
  let mod := (sprimeModuleOf env n).getD `this_file
  let rng ← liftCoreM (findDeclarationRanges? n)
  let (a, b) := match rng with
    | some r => (r.range.pos.line, r.range.endPos.line)
    | none => (0, 0)
  return s!"SPRIME {tag} {mod} {a} {b} {(privateToUserName? n).getD n}"

elab "#sprime_walk" : command => do
  let env ← getEnv
  let main : Array Name := #[`CombinatorialRigidity.Molecular.pencil_realization_theorem,
    `CombinatorialRigidity.Molecular.pencilPair_of_nonempty]
  let projMod := env.constants.fold (init := #[]) fun acc n _ =>
    if sprimeIsProjMod env n then acc.push n else acc
  let outside := projMod.filter fun n => !sprimeInD env n
  -- the after-world: transport every root
  let order := sprimePostOrder env (outside ++ main).toList sprimeInit
  let fwd ← sprimeTransportOrder order sprimeInit
  let env ← getEnv
  let bwd : Std.HashMap Name Name := fwd.fold (init := {}) fun acc a b =>
    match b with | some b => acc.insert b a | none => acc
  let before := sprimeReach env (outside ++ main) false fwd bwd
  -- users, before and after
  let mut usersB : Std.HashMap Name NameSet := {}
  for n in before.toList do
    for m in sprimeUses env false fwd bwd n do
      usersB := usersB.insert m ((usersB.getD m {}).insert n)
  let mut orph : NameSet := {}
  let mut after : NameSet := {}
  let mut changed := true
  let mut rounds : Nat := 0
  while changed do
    changed := false
    rounds := rounds + 1
    let roots := (outside.filter fun n => !orph.contains n) ++ main
    after := sprimeReach env roots true fwd bwd
    let mut usersA : Std.HashMap Name NameSet := {}
    for n in after.toList do
      for m in sprimeUses env true fwd bwd n do
        usersA := usersA.insert m ((usersA.getD m {}).insert n)
    for m in outside do
      if orph.contains m || sprimeIsAux env m then continue
      if (usersB.getD m {}).isEmpty then continue
      let live := (usersA.getD m {}).toList.filter fun u => !orph.contains u
      if live.isEmpty then
        orph := orph.insert m
        changed := true
  let mut lines : Array String := #[]
  for n in projMod do
    if sprimeIsAux env n then continue
    if sprimeInD env n then
      if !before.contains n then lines := lines.push (← sprimeLine env "UNREACHED" n)
      else if !after.contains n then lines := lines.push (← sprimeLine env "DEAD" n)
    else if orph.contains n then lines := lines.push (← sprimeLine env "ORPHAN" n)
    if sprimeInit.contains n then lines := lines.push (← sprimeLine env "MAPPED" n)
    else if ((fwd[n]?).bind id).isSome then lines := lines.push (← sprimeLine env "RECHECKED" n)
  let sorted := lines.qsort (· < ·)
  logInfo m!"SPRIME WALK: {projMod.size} project constants, {outside.size} outside D; \
    before {before.size}, after {after.size}; orphan rounds {rounds}\n\
    {"\n".intercalate sorted.toList}"

#sprime_walk

/-! ## The slices' deletion sets

Slice B (S′) deletes what loses its last user with S′, the general form and the two constructors;
slice C deletes the two steps and what only they use. For each slice, on the cumulative deletion
set, read in the after-world: (a) the surviving constants that use a deleted one (a slice must
restate or delete them); (b) the orphans, constants whose every after-world user is deleted, to a
fixpoint (auxiliary declarations followed, not reported). After slice B the orphans should be
exactly slice C's set, and after slice C there should be none. Names are literals; a name absent
from the environment (after the slices land) is reported, not an error. -/

/-- Slice B's deletions. -/
def sprimeSliceB : List Name :=
  [`Graph.ChainUsableAt, `Graph.IsX0Graph.exists_additiveCoreAt,
    `Graph.chainUsable_iff_chainUsableAt_three,
    `Graph.X0Reduces.openEarTwo, `Graph.X0Reduces.splitOff,
    `Graph.IsOpenEar.isX0Graph_splitOff_one,
    `Graph.deficiencyMerged_add_bodyBarDim_sub_one_le, `Graph.deficiencyMerged_three_add_five_le,
    `Graph.deficiencyMerged_two_add_two_le_of_three_le, `Graph.deficiencyMerged_two_add_two_le,
    -- the `d = 3` core bound, at the PI's word after the pin (`notes/Phase43c.md` item 4): no Lean
    -- user before SPRIME, so no orphan and no surviving user; listed for the sweep
    `Graph.deficiency_three_induce_eq_zero_of_le, `Graph.partitionDef_induce_id_le_of_maximal]

/-- Slice C's deletions. -/
def sprimeSliceC : List Name :=
  [`Graph.X0Attains.of_openEar_two, `Graph.X0Attains.of_splitOff,
    `Graph.finrank_span_rigidityRows_splitOff_special, `Graph.planeDiff_eq_zero_of_splitOff,
    `CombinatorialRigidity.Molecular.exists_mem_forall_add_smul_eq_zero,
    `CombinatorialRigidity.Molecular.PanelHingeFramework.finite_setOf_finrank_lt_of_curve,
    `Graph.ker_liftingMatrix_congr, `Graph.ker_liftingMatrix_le_of_le,
    `CombinatorialRigidity.Molecular.BodyHingeFramework.finrank_span_rigidityRows_eq_add_of_motions,
    `Graph.mem_liftingSpace_oneEar,
    `dotProduct_add_smul, `dotProduct_smul_add_smul, `MvPolynomial.polynomial_eval_aeval]

/-- The declaration a constant belongs to (a private name read as its user name). -/
def sprimeBase (n : Name) : Name := (privateToUserName? n).getD n

/-- `u` is in `D` or is an auxiliary declaration of one of its members. -/
partial def sprimeCovered (D : NameSet) (u : Name) : Bool :=
  let rec go (x : Name) : Bool :=
    D.contains x || match x with
      | .str p _ => go p
      | .num p _ => go p
      | .anonymous => false
  D.contains u || go (sprimeBase u)

elab "#sprime_slices" : command => do
  let env ← getEnv
  let projMod := env.constants.fold (init := #[]) fun acc n _ =>
    if sprimeIsProjMod env n then acc.push n else acc
  -- the deleted constants are read as themselves (one of B's needs no transport to be judged)
  let init := (sprimeSliceB ++ sprimeSliceC).foldl (fun m d => m.insert d none) sprimeInit
  let order := sprimePostOrder env projMod.toList init
  let fwd ← sprimeTransportOrder order init
  let env ← getEnv
  let bwd : Std.HashMap Name Name := fwd.fold (init := {}) fun acc a b =>
    match b with | some b => acc.insert b a | none => acc
  -- users in the after-world, over every landed constant (live or not)
  let mut users : Std.HashMap Name (Array Name) := {}
  let mut usersHead : Std.HashMap Name (Array Name) := {}
  for n in projMod do
    for m in sprimeUses env true fwd bwd n do
      users := users.insert m ((users.getD m #[]).push n)
    for m in sprimeUses env false fwd bwd n do
      usersHead := usersHead.insert m ((usersHead.getD m #[]).push n)
  let mut cum : NameSet := {}
  for (label, sl) in [("B", sprimeSliceB), ("C", sprimeSliceC)] do
    let absent := sl.filter fun d => !env.contains d
    cum := sl.foldl (·.insert ·) cum
    let mut viol : Array String := #[]
    for d in sl do
      for u in users.getD d #[] do
        if !sprimeCovered cum u && !sprimeCompanion u then viol := viol.push s!"{d} <- {u}"
    let mut dead := cum
    let mut orph : Array Name := #[]
    let mut changed := true
    while changed do
      changed := false
      for n in projMod do
        if dead.contains n || sprimeIsAux env n || sprimeCovered dead n then continue
        if (usersHead.getD n #[]).isEmpty then continue
        let us := (users.getD n #[]).filter fun u => !sprimeCovered dead u && u != n
        if us.isEmpty then
          dead := dead.insert n
          changed := true
          orph := orph.push n
    let mut members : Array String := #[]
    for d in sl do
      if env.contains d then members := members.push (← sprimeLine env s!"SLICE-{label}" d)
    logInfo m!"SPRIME SLICE {label}: {sl.length} deleted ({absent.length} absent: {absent}), \
      {cum.size} in all; surviving users of a deleted constant: {viol.size}\n\
      {"\n".intercalate viol.toList}\nORPHANS ({orph.size}): {orph.toList}\n\
      {"\n".intercalate members.toList}"

#sprime_slices
