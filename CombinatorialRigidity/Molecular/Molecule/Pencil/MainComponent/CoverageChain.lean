/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.Coverage

/-!
# Chains and the cycle in the `X₀` covering theorem (Phase 40m CHAINS B1)

The maximal ear through bodies of degree two, and the two consequences the covering theorem
needs: every body of degree two lies on a chain, and a graph satisfying (H) all of whose bodies
have degree two is a cycle (`blueprint/src/chapter/main-component.tex`,
`sec:main-component-coverage`; (MC-79)ff). One core, the maximal ear
`Graph.IsOpenEar.exists_maximal`, serves both: strong induction on `V₁.ncard`, by
`Graph.IsOpenEar.symm` and `Graph.IsOpenEar.cons`, extending one more body at a time while an end
has degree two and is not adjacent to the other end.

## Main statements

* `Graph.IsChain` — **a chain** (`def:pencil-x0-chain`): an open ear whose interior bodies have
  degree two and whose ends have degree at least three.
* `Graph.IsOpenEar.exists_maximal` — **the maximal ear**: every open ear of a graph satisfying (H)
  extends, through bodies of degree two at its ends, to one each of whose ends is a hub or
  adjacent to the other end.
* `Graph.IsX0Graph.exists_isChain` — **chain extraction** (`lem:pencil-x0-chain-exists`): in a
  2-connected (H)-graph with a hub, every body of degree two lies on a chain.
* `Graph.IsX0Graph.x0Reduces_of_forall_degree_eq_two` — **the cycle**
  (`lem:pencil-x0-cycle-reduces`): a graph satisfying (H) all of whose bodies have degree two is a
  cycle, and reduces by BASE (`Graph.X0Reduces.cycle`'s format).
-/

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {α β : Type*}

/-! ## Path sequences -/

/-- The path sequence with one more body `a` in front of `x`, started at `a'`. -/
theorem pathVertex_cons {k : ℕ} (a' a : α) (x : Fin k → α) (b : α) :
    pathVertex a' (Fin.cons a x) b = Fin.cons a' (pathVertex a x b) := by
  rw [pathVertex, pathVertex, Fin.cons_snoc_eq_snoc_cons]

/-- The path edges of the sequence extended by one more body `a` in front, from `a'` along
`g`. -/
theorem isLink_pathVertex_cons {G : Graph α β} {k : ℕ} {x : Fin k → α} {a b a' : α}
    {e : Fin (k + 1) → β} {g : β}
    (hpath : ∀ i : Fin (k + 1),
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (hg : G.IsLink g a' a) :
    ∀ i : Fin (k + 2), G.IsLink ((Fin.cons g e : Fin (k + 2) → β) i)
      (pathVertex a' (Fin.cons a x) b i.castSucc) (pathVertex a' (Fin.cons a x) b i.succ) := by
  rw [pathVertex_cons]
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_zero, Fin.cons_succ, pathVertex_zero]
    exact hg
  · rw [Fin.cons_succ, ← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
    exact hpath j

/-- The path edges of the sequence read from its other end. -/
theorem isLink_pathVertex_rev {G : Graph α β} {k : ℕ} {x : Fin k → α} {a b : α}
    {e : Fin (k + 1) → β}
    (hpath : ∀ i : Fin (k + 1),
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ)) :
    ∀ i : Fin (k + 1), G.IsLink ((e ∘ Fin.rev) i)
      (pathVertex b (x ∘ Fin.rev) a i.castSucc) (pathVertex b (x ∘ Fin.rev) a i.succ) := by
  intro i
  rw [pathVertex_rev, pathVertex_rev, Fin.rev_castSucc, Fin.rev_succ]
  exact (hpath i.rev).symm

/-- A position of the path sequence lying in a set that avoids the interior is an end. -/
theorem val_eq_zero_or_of_pathVertex_mem {k : ℕ} {x : Fin k → α} {a b : α} {V : Set α}
    (hxV : ∀ i, x i ∉ V) {m : Fin (k + 2)} (hm : pathVertex a x b m ∈ V) :
    m.val = 0 ∨ m.val = k + 1 := by
  rcases pathVertex_cases a x b m with ⟨h, -⟩ | ⟨i, -, h⟩ | ⟨h, -⟩
  · exact Or.inl h
  · exact absurd (h ▸ hm) (hxV i)
  · exact Or.inr h

/-- The body at a position of value one. -/
theorem pathVertex_eq_of_val_eq_zero {k : ℕ} (a : α) (x : Fin k → α) (b : α) {m : Fin (k + 2)}
    (hm : m.val = 0) : pathVertex a x b m = a := by
  rcases pathVertex_cases a x b m with ⟨-, h⟩ | ⟨i, h', -⟩ | ⟨h', -⟩
  · exact h
  · omega
  · omega

/-- The body at a position of value `k + 1`. -/
theorem pathVertex_eq_of_val_eq_last {k : ℕ} (a : α) (x : Fin k → α) (b : α) {m : Fin (k + 2)}
    (hm : m.val = k + 1) : pathVertex a x b m = b := by
  rcases pathVertex_cases a x b m with ⟨h', -⟩ | ⟨i, h', -⟩ | ⟨-, h⟩
  · omega
  · omega
  · exact h

/-! ## Open ears -/

/-- An open ear read from its other end. -/
theorem _root_.Graph.IsOpenEar.symm {G : Graph α β} {V₁ : Set α} {k : ℕ} {x : Fin k → α}
    {a b : α} {e : Fin (k + 1) → β} (h : G.IsOpenEar V₁ x a b e) :
    G.IsOpenEar V₁ (x ∘ Fin.rev) b a (e ∘ Fin.rev) where
  cover := by rw [h.cover, Fin.rev_surjective.range_comp]
  inj := h.inj.comp Fin.rev_injective
  notMem := fun i => h.notMem _
  left_mem := h.right_mem
  right_mem := h.left_mem
  ne := h.ne.symm
  isLink := isLink_pathVertex_rev h.isLink
  sep := fun f u w hf hfe => h.sep f u w hf fun i => by simpa using hfe i.rev

/-- An open ear extended by its end `a` into the interior, from a new end `a'`. -/
theorem _root_.Graph.IsOpenEar.cons {G : Graph α β} {V₁ : Set α} {k : ℕ} {x : Fin k → α}
    {a b a' : α} {e : Fin (k + 1) → β} {g : β} (h : G.IsOpenEar V₁ x a b e)
    (hg : G.IsLink g a' a) (ha' : a' ∈ V₁) (ha'a : a' ≠ a) (ha'b : a' ≠ b)
    (honly : ∀ f y, G.IsLink f a y → f = e 0 ∨ f = g) :
    G.IsOpenEar (V₁ \ {a}) (Fin.cons a x) a' b (Fin.cons g e) where
  cover := by
    rw [h.cover, Fin.range_cons]
    ext y
    simp only [Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_insert_iff]
    have := h.left_mem
    constructor
    · rintro (hy | hy)
      · by_cases hya : y = a
        · exact Or.inr (Or.inl hya)
        · exact Or.inl ⟨hy, hya⟩
      · exact Or.inr (Or.inr hy)
    · rintro (⟨hy, -⟩ | rfl | hy)
      · exact Or.inl hy
      · exact Or.inl this
      · exact Or.inr hy
  inj := Fin.cons_injective_iff.mpr ⟨fun ⟨i, hi⟩ => h.notMem i (hi ▸ h.left_mem), h.inj⟩
  notMem := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · rw [Fin.cons_succ]; exact fun hj => h.notMem j hj.1
  left_mem := ⟨ha', ha'a⟩
  right_mem := ⟨h.right_mem, fun hb => h.ne (Set.mem_singleton_iff.mp hb).symm⟩
  ne := ha'b
  isLink := isLink_pathVertex_cons h.isLink hg
  sep := by
    intro f u w hf hfe
    have hfg : f ≠ g := by simpa using hfe 0
    have hfe' : ∀ i, f ≠ e i := fun i => by simpa using hfe i.succ
    obtain ⟨hu, hw⟩ := h.sep f u w hf hfe'
    refine ⟨⟨hu, fun hua => ?_⟩, ⟨hw, fun hwa => ?_⟩⟩
    · rw [Set.mem_singleton_iff] at hua
      rw [hua] at hf
      rcases honly f w hf with h' | h'
      · exact hfe' 0 h'
      · exact hfg h'
    · rw [Set.mem_singleton_iff] at hwa
      rw [hwa] at hf
      rcases honly f u hf.symm with h' | h'
      · exact hfe' 0 h'
      · exact hfg h'

/-- The path sequence of an open ear is injective. -/
theorem _root_.Graph.IsOpenEar.injective_pathVertex {G : Graph α β} {V₁ : Set α} {k : ℕ}
    {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β} (h : G.IsOpenEar V₁ x a b e) :
    Function.Injective (pathVertex a x b) :=
  pathVertex_injective h.inj (fun i hi => h.notMem i (hi ▸ h.left_mem))
    (fun i hi => h.notMem i (hi ▸ h.right_mem)) h.ne

/-- The only path edge at `a` is the first. -/
theorem _root_.Graph.IsOpenEar.eq_zero_of_isLink_left {G : Graph α β} {V₁ : Set α} {k : ℕ}
    {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β} (h : G.IsOpenEar V₁ x a b e) {i : Fin (k + 1)}
    {y : α} (hl : G.IsLink (e i) a y) : i = 0 := by
  have hpv := h.injective_pathVertex
  have h0 : pathVertex a x b 0 = a := pathVertex_zero a x b
  rcases hl.left_eq_or_eq (h.isLink i) with h' | h'
  · have := congrArg Fin.val (hpv (h'.symm.trans h0.symm))
    exact Fin.ext (by simpa using this)
  · have := congrArg Fin.val (hpv (h'.symm.trans h0.symm))
    simp at this

/-- The only path edge at `b` is the last. -/
theorem _root_.Graph.IsOpenEar.eq_last_of_isLink_right {G : Graph α β} {V₁ : Set α} {k : ℕ}
    {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β} (h : G.IsOpenEar V₁ x a b e) {i : Fin (k + 1)}
    {y : α} (hl : G.IsLink (e i) b y) : i = Fin.last k := by
  have := h.symm.eq_zero_of_isLink_left (i := i.rev) (y := y) (by simpa using hl)
  rw [← Fin.rev_rev i, this, Fin.rev_zero]

/-- Every link at an interior body of an open ear is one of its two path edges. -/
theorem _root_.Graph.IsOpenEar.isLink_interior {G : Graph α β} {V₁ : Set α} {k : ℕ}
    {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β} (hear : G.IsOpenEar V₁ x a b e) (i : Fin k)
    {f : β} {y : α} (hf : G.IsLink f (x i) y) : f = e i.castSucc ∨ f = e i.succ := by
  have hax : ∀ j, x j ≠ a := fun j h => hear.notMem j (h ▸ hear.left_mem)
  have hbx : ∀ j, x j ≠ b := fun j h => hear.notMem j (h ▸ hear.right_mem)
  by_cases hfe : ∃ j, f = e j
  · obtain ⟨j, rfl⟩ := hfe
    rcases hf.left_eq_or_eq (hear.isLink j) with h | h
    · have := (pathVertex_eq_x_iff hear.inj hax hbx _ i).mp h.symm
      right; congr 1; ext; simp only [Fin.val_castSucc, Fin.val_succ] at this ⊢; omega
    · have := (pathVertex_eq_x_iff hear.inj hax hbx _ i).mp h.symm
      left; congr 1; ext; simp only [Fin.val_castSucc, Fin.val_succ] at this ⊢; omega
  · push Not at hfe
    exact absurd (hear.sep f _ _ hf hfe).1 (hear.notMem i)

/-- The interior bodies of an open ear of a loopless graph have degree two. -/
theorem _root_.Graph.IsOpenEar.degree_eq_two {G : Graph α β} [G.Loopless]
    {V₁ : Set α} {k : ℕ} {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β}
    (h : G.IsOpenEar V₁ x a b e) (i : Fin k) : G.degree (x i) = 2 := by
  have hax : ∀ j, x j ≠ a := fun j hj => h.notMem j (hj ▸ h.left_mem)
  have hbx : ∀ j, x j ≠ b := fun j hj => h.notMem j (hj ▸ h.right_mem)
  have hinj := pathEdge_injective h.inj hax hbx h.ne h.isLink
  have h₁ : G.IsLink (e i.castSucc) (x i) (pathVertex a x b i.castSucc.castSucc) := by
    have := h.isLink i.castSucc
    rw [pathVertex_eq_of_val_eq_succ a x b (m := i.castSucc.succ) (i := i) (by simp)] at this
    exact this.symm
  have h₂ : G.IsLink (e i.succ) (x i) (pathVertex a x b i.succ.succ) := by
    have := h.isLink i.succ
    rwa [pathVertex_eq_of_val_eq_succ a x b (m := i.succ.castSucc) (i := i) (by simp)] at this
  rw [Graph.degree_eq_ncard_inc]
  have hE : E(G, x i) = {e i.castSucc, e i.succ} := by
    ext f
    constructor
    · rintro ⟨y, hy⟩
      rcases h.isLink_interior i hy with rfl | rfl <;> simp
    · rintro (rfl | rfl)
      · exact h₁.inc_left
      · exact h₂.inc_left
  rw [hE, Set.ncard_pair fun h' => by
    have := congrArg Fin.val (hinj h'); simp at this]

/-- A neighbour outside `V₁` of a body of `V₁` is reached by a path edge at an end. -/
theorem _root_.Graph.IsOpenEar.exists_eq_of_isLink_notMem {G : Graph α β} {V₁ : Set α} {k : ℕ}
    {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β} (h : G.IsOpenEar V₁ x a b e) {y z : α}
    {f : β} (hy : y ∈ V₁) (hf : G.IsLink f y z) (hz : z ∉ V₁) :
    (y = a ∧ f = e 0) ∨ (y = b ∧ f = e (Fin.last k)) := by
  by_cases hfe : ∃ i, f = e i
  · obtain ⟨i, rfl⟩ := hfe
    rcases hf.eq_and_eq_or_eq_and_eq (h.isLink i) with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · rcases val_eq_zero_or_of_pathVertex_mem h.notMem hy with h0 | h0
      · exact Or.inl ⟨pathVertex_eq_of_val_eq_zero _ _ _ h0,
          congrArg e (Fin.ext (by simpa using h0))⟩
      · simp only [Fin.val_castSucc] at h0; omega
    · rcases val_eq_zero_or_of_pathVertex_mem h.notMem hy with h0 | h0
      · simp at h0
      · exact Or.inr ⟨pathVertex_eq_of_val_eq_last _ _ _ h0,
          congrArg e (Fin.ext (by simp only [Fin.val_succ] at h0; simp; omega))⟩
  · push Not at hfe
    exact absurd (h.sep f y z hf hfe).2 hz

/-- The first path edge, from `a`. -/
theorem _root_.Graph.IsOpenEar.isLink_first {G : Graph α β} {V₁ : Set α} {k : ℕ}
    {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β} (h : G.IsOpenEar V₁ x a b e) :
    G.IsLink (e 0) a (pathVertex a x b 1) := by
  have := h.isLink 0
  rwa [Fin.castSucc_zero, pathVertex_zero, Fin.succ_zero_eq_one] at this

/-- The last path edge, from `b`. -/
theorem _root_.Graph.IsOpenEar.isLink_last {G : Graph α β} {V₁ : Set α} {k : ℕ}
    {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β} (h : G.IsOpenEar V₁ x a b e) :
    G.IsLink (e (Fin.last k)) b (pathVertex a x b (Fin.last k).castSucc) := by
  have := h.isLink (Fin.last k)
  rw [Fin.succ_last, pathVertex_last] at this
  exact this.symm

/-- A nonempty open ear's side `V₁` has fewer bodies than `G`. -/
theorem _root_.Graph.IsOpenEar.ncard_lt [Finite α] {G : Graph α β} {V₁ : Set α} {k : ℕ}
    {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β} (hear : G.IsOpenEar V₁ x a b e)
    (hk : 1 ≤ k) : V₁.ncard < V(G).ncard := by
  refine Set.ncard_lt_ncard ?_
  refine (Set.ssubset_iff_of_subset (hear.cover ▸ Set.subset_union_left)).mpr
    ⟨x ⟨0, hk⟩, ?_, hear.notMem _⟩
  rw [hear.cover]
  exact Set.mem_union_right _ ⟨_, rfl⟩

/-! ## The maximal ear -/

/-- In a connected graph, a nonempty set of bodies closed under adjacency is everything. -/
theorem _root_.Graph.Connected.vertexSet_subset_of_forall_adj {G : Graph α β}
    (hG : G.Connected) {T : Set α} (hT : T.Nonempty) (hTV : T ⊆ V(G))
    (hcl : ∀ u ∈ T, ∀ z, G.Adj u z → z ∈ T) : V(G) ⊆ T := by
  by_contra hns
  obtain ⟨y, hy, z, hz, hyz⟩ := (Graph.connected_iff_forall_exists_adj hG.nonempty).mp hG T
    (hTV.ssubset_of_ne fun h => hns h.symm.subset) hT
  exact hz.2 (hcl y hy z hyz)

/-- At an end `a` of degree two, the second link: `a`'s edges are `e 0` and one more, `g`, to a
body `a'` of `V₁`, and `g` is no path edge. -/
theorem _root_.Graph.IsOpenEar.exists_isLink_of_degree_eq_two [Finite β]
    {G : Graph α β} [G.Simple] {V₁ : Set α} {k : ℕ} {x : Fin k → α} {a b : α}
    {e : Fin (k + 1) → β} (h : G.IsOpenEar V₁ x a b e) (ha : G.degree a = 2) :
    ∃ a' g, G.IsLink g a a' ∧ a' ≠ a ∧ (∀ i, g ≠ e i) ∧
      ∀ f y, G.IsLink f a y → f = e 0 ∨ f = g := by
  have h0 : G.IsLink (e 0) a (pathVertex a x b 1) := by
    have := h.isLink 0
    rwa [Fin.castSucc_zero, pathVertex_zero, Fin.succ_zero_eq_one] at this
  have hN : N(G, a).ncard = 2 := by rw [← Graph.degree_eq_ncard_adj]; exact ha
  obtain ⟨a', ha'N, ha'p⟩ :=
    Set.exists_ne_of_one_lt_ncard (s := N(G, a)) (by omega) (pathVertex a x b 1)
  obtain ⟨g, hg⟩ := ha'N
  have hg0 : g ≠ e 0 := by
    rintro rfl
    exact ha'p (h0.right_unique hg).symm
  have hge : ∀ i, g ≠ e i := by
    rintro i rfl
    exact hg0 (by rw [h.eq_zero_of_isLink_left hg])
  refine ⟨a', g, hg, fun h' => ?_, hge,
    Graph.isLink_eq_of_degree_eq_two ha (Ne.symm hg0) h0 hg⟩
  rw [h'] at hg
  exact Graph.Loopless.not_isLoopAt g a hg

/-- One step of the maximal ear: an end `a` of degree two not adjacent to `b` extends. -/
theorem _root_.Graph.IsOpenEar.exists_cons [Finite β] {G : Graph α β} [G.Simple]
    {V₁ : Set α} {k : ℕ} {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β}
    (h : G.IsOpenEar V₁ x a b e) (ha : G.degree a = 2) (hab : ¬ G.Adj a b) :
    ∃ a' g, G.IsOpenEar (V₁ \ {a}) (Fin.cons a x) a' b (Fin.cons g e) := by
  obtain ⟨a', g, hg, ha'a, hge, honly⟩ := h.exists_isLink_of_degree_eq_two ha
  refine ⟨a', g, h.cons hg.symm (h.sep g a a' hg hge).2 ha'a (fun h' => hab ?_) honly⟩
  exact ⟨g, h' ▸ hg⟩

/-- **The maximal ear**: every open ear of a graph satisfying (H) extends, through bodies of
degree two at its ends, to one each of whose ends is a hub or adjacent to the other end. -/
theorem _root_.Graph.IsOpenEar.exists_maximal [Finite α] [Finite β] {G : Graph α β}
    (hG : G.IsX0Graph) {V₁ : Set α} {k : ℕ} {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β}
    (h : G.IsOpenEar V₁ x a b e) :
    ∃ (V₂ : Set α) (m : ℕ) (y : Fin m → α) (c d : α) (f : Fin (m + 1) → β),
      G.IsOpenEar V₂ y c d f ∧ Set.range x ⊆ Set.range y ∧
      (3 ≤ G.degree c ∨ G.Adj c d) ∧ (3 ≤ G.degree d ∨ G.Adj c d) := by
  have := hG.simple
  induction hn : V₁.ncard using Nat.strong_induction_on generalizing V₁ k x a b e with
  | _ n ih =>
  have hlt : ∀ c ∈ V₁, (V₁ \ {c}).ncard < n := fun c hc =>
    hn ▸ Set.ncard_sdiff_singleton_lt_of_mem hc (Set.toFinite _)
  have hV : V₁ ⊆ V(G) := h.cover ▸ Set.subset_union_left
  by_cases hA : 3 ≤ G.degree a ∨ G.Adj a b
  · by_cases hB : 3 ≤ G.degree b ∨ G.Adj a b
    · exact ⟨V₁, k, x, a, b, e, h, subset_rfl, hA, hB⟩
    · push Not at hB
      have hb2 : G.degree b = 2 := by
        have := hG.two_le_degree b (hV h.right_mem); omega
      obtain ⟨b', g, h'⟩ := h.symm.exists_cons hb2 fun hba => hB.2 hba.symm
      obtain ⟨V₂, m, y, c, d, f, hy, hsub, hc, hd⟩ := ih _ (hlt b h.right_mem) h' rfl
      refine ⟨V₂, m, y, c, d, f, hy, ?_, hc, hd⟩
      refine subset_trans ?_ hsub
      rw [Fin.range_cons, Fin.rev_surjective.range_comp]
      exact Set.subset_insert _ _
  · push Not at hA
    have ha2 : G.degree a = 2 := by
      have := hG.two_le_degree a (hV h.left_mem); omega
    obtain ⟨a', g, h'⟩ := h.exists_cons ha2 hA.2
    obtain ⟨V₂, m, y, c, d, f, hy, hsub, hc, hd⟩ := ih _ (hlt a h.left_mem) h' rfl
    refine ⟨V₂, m, y, c, d, f, hy, ?_, hc, hd⟩
    refine subset_trans ?_ hsub
    rw [Fin.range_cons]
    exact Set.subset_insert _ _

/-! ## Chains -/

/-- A **chain** of `G` (Step MC16's notation): an open ear whose interior bodies have degree two
and whose ends have degree at least three. -/
structure _root_.Graph.IsChain (G : Graph α β) (V₁ : Set α) {k : ℕ} (x : Fin k → α) (a b : α)
    (e : Fin (k + 1) → β) : Prop extends G.IsOpenEar V₁ x a b e where
  one_le : 1 ≤ k
  degree_eq_two : ∀ i, G.degree (x i) = 2
  three_le_degree_left : 3 ≤ G.degree a
  three_le_degree_right : 3 ≤ G.degree b

/-- A body of degree two has two links, to distinct neighbours. -/
theorem _root_.Graph.IsX0Graph.exists_isLink_pair {G : Graph α β} (hG : G.IsX0Graph) {v : α}
    (hdeg : G.degree v = 2) :
    ∃ c₁ c₂ e₁ e₂, G.IsLink e₁ c₁ v ∧ G.IsLink e₂ v c₂ ∧ c₁ ≠ c₂ := by
  have := hG.simple
  rw [Graph.degree_eq_ncard_adj] at hdeg
  obtain ⟨c₁, c₂, hne, hN⟩ := Set.ncard_eq_two.mp hdeg
  obtain ⟨e₁, he₁⟩ : G.Adj v c₁ := (hN ▸ Set.mem_insert c₁ {c₂} : c₁ ∈ N(G, v))
  obtain ⟨e₂, he₂⟩ : G.Adj v c₂ := (hN ▸ Set.mem_insert_of_mem c₁ rfl : c₂ ∈ N(G, v))
  exact ⟨c₁, c₂, e₁, e₂, he₁.symm, he₂, hne⟩

/-- A body of degree two with distinct neighbours is a one-body open ear. -/
theorem _root_.Graph.IsX0Graph.isOpenEar_one [Finite β] {G : Graph α β} (hG : G.IsX0Graph)
    {x c₁ c₂ : α} {e₁ e₂ : β} (hx : G.degree x = 2) (h₁ : G.IsLink e₁ c₁ x)
    (h₂ : G.IsLink e₂ x c₂) (hne : c₁ ≠ c₂) :
    G.IsOpenEar (V(G) \ {x}) ![x] c₁ c₂ ![e₁, e₂] := by
  have := hG.simple
  have hloop := hG.simple.toLoopless
  have hc₁x : c₁ ≠ x := fun h => hloop.not_isLoopAt e₁ x (h ▸ h₁)
  have hc₂x : c₂ ≠ x := fun h => hloop.not_isLoopAt e₂ x (h ▸ h₂)
  have he : e₁ ≠ e₂ := by
    rintro rfl
    rcases h₁.left_eq_or_eq h₂ with h | h
    · exact hc₁x h
    · exact hne h
  have hxV : x ∈ V(G) := h₂.left_mem
  refine ⟨?_, fun i j _ => Subsingleton.elim i j, ?_, ⟨h₁.left_mem, hc₁x⟩,
    ⟨h₂.right_mem, hc₂x⟩, hne, ?_, ?_⟩
  · ext y
    simp only [Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_range]
    constructor
    · intro hy
      by_cases hyx : y = x
      · exact Or.inr ⟨0, by simp [hyx]⟩
      · exact Or.inl ⟨hy, hyx⟩
    · rintro (⟨hy, -⟩ | ⟨i, rfl⟩)
      · exact hy
      · simpa using hxV
  · intro i h
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact h.2 rfl
  · intro i
    fin_cases i
    · exact h₁
    · exact h₂
  · intro f u w hf hfe
    have hf1 : f ≠ e₁ := hfe 0
    have hf2 : f ≠ e₂ := hfe 1
    refine ⟨⟨hf.left_mem, fun hu => ?_⟩, ⟨hf.right_mem, fun hw => ?_⟩⟩
    · rw [hu] at hf
      rcases Graph.isLink_eq_of_degree_eq_two hx he h₁.symm h₂ f w hf with h | h
      · exact hf1 h
      · exact hf2 h
    · rw [hw] at hf
      rcases Graph.isLink_eq_of_degree_eq_two hx he h₁.symm h₂ f u hf.symm with h | h
      · exact hf1 h
      · exact hf2 h

/-- A body of degree two between two hubs is a one-body chain. -/
theorem _root_.Graph.IsX0Graph.isChain_one [Finite β] {G : Graph α β} (hG : G.IsX0Graph)
    {x c₁ c₂ : α} {e₁ e₂ : β} (hx : G.degree x = 2) (h₁ : G.IsLink e₁ c₁ x)
    (h₂ : G.IsLink e₂ x c₂) (hne : c₁ ≠ c₂) (hc₁ : 3 ≤ G.degree c₁) (hc₂ : 3 ≤ G.degree c₂) :
    G.IsChain (V(G) \ {x}) ![x] c₁ c₂ ![e₁, e₂] :=
  ⟨hG.isOpenEar_one hx h₁ h₂ hne, le_rfl, fun i => by
    obtain rfl : i = 0 := Subsingleton.elim _ _
    simpa using hx, hc₁, hc₂⟩

/-- Every body of the path sequence lies on the ear's closed path. -/
theorem pathVertex_mem_insert_insert_range {k : ℕ} (a : α) (x : Fin k → α) (b : α)
    (m : Fin (k + 2)) : pathVertex a x b m ∈ insert b (insert a (Set.range x)) := by
  rcases pathVertex_cases a x b m with ⟨-, h⟩ | ⟨i, -, h⟩ | ⟨-, h⟩ <;> rw [h]
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨i, rfl⟩)
  · exact Or.inl rfl

/-- An ear of `k ≥ 1` bodies whose ends are adjacent, with `a` of degree two: every neighbour of
`a` or of an interior body lies on the closed path `a − x − b − a`. -/
theorem _root_.Graph.IsOpenEar.adj_mem_of_adj_of_degree_eq_two [Finite β] {G : Graph α β}
    [G.Simple] {V₁ : Set α} {k : ℕ} {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β}
    (h : G.IsOpenEar V₁ x a b e) (hk : 1 ≤ k) {g : β} (hg : G.IsLink g a b)
    (ha : G.degree a = 2) :
    ∀ u ∈ insert a (Set.range x), ∀ z, G.Adj u z → z ∈ insert b (insert a (Set.range x)) := by
  have h0 : G.IsLink (e 0) a (pathVertex a x b 1) := by
    have := h.isLink 0
    rwa [Fin.castSucc_zero, pathVertex_zero, Fin.succ_zero_eq_one] at this
  have hg0 : e 0 ≠ g := by
    intro h'
    rw [h'] at h0
    have h1 : pathVertex a x b 1 = x ⟨0, hk⟩ := pathVertex_eq_of_val_eq_succ a x b (by simp)
    exact h.notMem ⟨0, hk⟩ (h1 ▸ (hg.right_unique h0) ▸ h.right_mem)
  rintro u (rfl | ⟨i, rfl⟩) z ⟨f, hf⟩
  · rcases Graph.isLink_eq_of_degree_eq_two ha hg0 h0 hg f z hf with rfl | rfl
    · rw [← h0.right_unique hf]
      exact pathVertex_mem_insert_insert_range _ _ _ _
    · rw [← hg.right_unique hf]
      exact Or.inl rfl
  · rcases h.isLink_interior i hf with rfl | rfl
    · rcases hf.eq_and_eq_or_eq_and_eq (h.isLink i.castSucc) with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
        exact pathVertex_mem_insert_insert_range _ _ _ _
    · rcases hf.eq_and_eq_or_eq_and_eq (h.isLink i.succ) with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
        exact pathVertex_mem_insert_insert_range _ _ _ _

/-- **A closed ear at a cut vertex, or all of `G`**: in a 2-connected (H)-graph with a hub, no
ear of `k ≥ 1` bodies has adjacent ends one of which has degree two. -/
theorem _root_.Graph.IsOpenEar.false_of_adj_of_degree_eq_two [Finite β]
    {G : Graph α β} (hG : G.IsX0Graph)
    (h2c : ∀ v ∈ V(G), (G.induce (V(G) \ {v})).Connected)
    (hhub : ∃ w ∈ V(G), G.degree w ≠ 2) {V₁ : Set α} {k : ℕ} {x : Fin k → α} {a b : α}
    {e : Fin (k + 1) → β} (h : G.IsOpenEar V₁ x a b e) (hk : 1 ≤ k) (hadj : G.Adj a b)
    (ha : G.degree a = 2) : False := by
  have := hG.simple
  obtain ⟨g, hg⟩ := hadj
  have hcl := h.adj_mem_of_adj_of_degree_eq_two hk hg ha
  have hV : V₁ ⊆ V(G) := h.cover ▸ Set.subset_union_left
  have hxV : ∀ i, x i ∈ V(G) := fun i => h.cover ▸ Or.inr ⟨i, rfl⟩
  have hxb : ∀ i, x i ≠ b := fun i hi => h.notMem i (hi ▸ h.right_mem)
  have hbV : b ∈ V(G) := hV h.right_mem
  set S : Set α := insert a (Set.range x) with hS
  by_cases hT : V(G) ⊆ insert b S
  · -- `G` is the cycle `a − x − b − a`: every body has degree two
    obtain ⟨w, hw, hw2⟩ := hhub
    have hb2 : G.degree b = 2 := by
      refine le_antisymm ?_ (hG.two_le_degree b hbV)
      rw [Graph.degree_eq_ncard_inc]
      have hsub : E(G, b) ⊆ {e (Fin.last k), g} := by
        rintro f ⟨z, hz⟩
        by_cases hfe : ∃ i, f = e i
        · obtain ⟨i, rfl⟩ := hfe
          exact Or.inl (by rw [h.eq_last_of_isLink_right hz])
        · push Not at hfe
          have hz₁ := (h.sep f b z hz hfe).2
          rcases hT hz.right_mem with rfl | rfl | ⟨i, rfl⟩
          · exact absurd hz (Graph.Loopless.not_isLoopAt f z)
          · exact Or.inr (Graph.Simple.eq_of_isLink hz hg.symm)
          · exact absurd hz₁ (h.notMem i)
      exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_pair_le _ _)
    rcases hT hw with rfl | rfl | ⟨i, rfl⟩
    · exact hw2 hb2
    · exact hw2 ha
    · exact hw2 (h.degree_eq_two i)
  · -- `b` cuts `S` off the rest of `G`
    obtain ⟨w, hw, hwT⟩ := Set.not_subset.mp hT
    have hconn := h2c b hbV
    have hSH : S ⊆ V(G.induce (V(G) \ {b})) := by
      rintro u (rfl | ⟨i, rfl⟩)
      · exact ⟨hV h.left_mem, h.ne⟩
      · exact ⟨hxV i, hxb i⟩
    obtain ⟨s, hs, t, ht, hst⟩ :=
      (Graph.connected_iff_forall_exists_adj ⟨a, hSH (Set.mem_insert a _)⟩).mp hconn S
        (hSH.ssubset_of_ne fun hSeq => hwT (Or.inr (hSeq ▸ ⟨hw, fun hwb => hwT (Or.inl hwb)⟩)))
        ⟨a, Set.mem_insert a _⟩
    obtain ⟨f, hf⟩ := hst
    rw [Graph.induce_isLink] at hf
    rcases hcl s hs t ⟨f, hf.1⟩ with rfl | ht'
    · exact hf.2.2.2 rfl
    · exact ht.2 ht'

/-- **Chain extraction**: in a 2-connected (H)-graph with a hub, every body of degree two lies on
a chain. -/
theorem _root_.Graph.IsX0Graph.exists_isChain [Finite α] [Finite β] {G : Graph α β}
    (hG : G.IsX0Graph) (h2c : ∀ v ∈ V(G), (G.induce (V(G) \ {v})).Connected)
    (hhub : ∃ w ∈ V(G), G.degree w ≠ 2) {v : α} (_hv : v ∈ V(G)) (hdeg : G.degree v = 2) :
    ∃ (V₁ : Set α) (k : ℕ) (x : Fin k → α) (a b : α) (e : Fin (k + 1) → β),
      G.IsChain V₁ x a b e ∧ v ∈ Set.range x := by
  have := hG.simple
  obtain ⟨c₁, c₂, e₁, e₂, h₁, h₂, hne⟩ := hG.exists_isLink_pair hdeg
  obtain ⟨V₂, m, y, c, d, f, hy, hsub, hc, hd⟩ :=
    (hG.isOpenEar_one hdeg h₁ h₂ hne).exists_maximal hG
  have hvy : v ∈ Set.range y := hsub ⟨0, rfl⟩
  have hm : 1 ≤ m := by
    obtain ⟨i, -⟩ := hvy
    exact Nat.one_le_iff_ne_zero.mpr fun h0 => (h0 ▸ i).elim0
  have hV : V₂ ⊆ V(G) := hy.cover ▸ Set.subset_union_left
  refine ⟨V₂, m, y, c, d, f, ⟨hy, hm, hy.degree_eq_two, ?_, ?_⟩, hvy⟩
  · rcases hc with hc | hc
    · exact hc
    · by_contra h3
      exact hy.false_of_adj_of_degree_eq_two hG h2c hhub hm hc
        (by have := hG.two_le_degree c (hV hy.left_mem); omega)
  · rcases hd with hd | hd
    · exact hd
    · by_contra h3
      exact hy.symm.false_of_adj_of_degree_eq_two hG h2c hhub hm hd.symm
        (by have := hG.two_le_degree d (hV hy.right_mem); omega)

/-- **The cycle**: a graph satisfying (H) all of whose bodies have degree two is a cycle, and
reduces by BASE (`of_cycle`'s format). -/
theorem _root_.Graph.IsX0Graph.x0Reduces_of_forall_degree_eq_two [Finite α] [Finite β]
    {G : Graph α β} (hG : G.IsX0Graph) (h2 : ∀ v ∈ V(G), G.degree v = 2) :
    G.X0Reduces G.X0Below := by
  have := hG.simple
  obtain ⟨v, hv⟩ := hG.connected.nonempty
  obtain ⟨c₁, c₂, e₁, e₂, h₁, h₂, hne⟩ := hG.exists_isLink_pair (h2 v hv)
  obtain ⟨V₂, m, y, c, d, f, hy, hsub, hc, -⟩ :=
    (hG.isOpenEar_one (h2 v hv) h₁ h₂ hne).exists_maximal hG
  have hm : 1 ≤ m := by
    obtain ⟨i, -⟩ := hsub ⟨0, rfl⟩
    exact Nat.one_le_iff_ne_zero.mpr fun h0 => (h0 ▸ i).elim0
  have hV : V₂ ⊆ V(G) := hy.cover ▸ Set.subset_union_left
  have hc2 := h2 c (hV hy.left_mem)
  have hd2 := h2 d (hV hy.right_mem)
  obtain ⟨g, hg⟩ : G.Adj c d := hc.resolve_left (by omega)
  have hcl := hy.adj_mem_of_adj_of_degree_eq_two hm hg hc2
  have hcl' := hy.symm.adj_mem_of_adj_of_degree_eq_two hm hg.symm hd2
  have hrange : Set.range (y ∘ Fin.rev) = Set.range y := Fin.rev_surjective.range_comp y
  rw [hrange] at hcl'
  -- the closed path is all of `G`
  have hT : V(G) ⊆ insert d (insert c (Set.range y)) := by
    refine hG.connected.vertexSet_subset_of_forall_adj ⟨d, Set.mem_insert _ _⟩ ?_ ?_
    · rintro u (rfl | rfl | ⟨i, rfl⟩)
      · exact hV hy.right_mem
      · exact hV hy.left_mem
      · exact hy.cover ▸ Or.inr ⟨i, rfl⟩
    · rintro u (rfl | hu) z hz
      · rcases hcl' u (Set.mem_insert u _) z hz with rfl | rfl | hz'
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl rfl
        · exact Or.inr (Or.inr hz')
      · exact hcl u hu z hz
  have hxa : ∀ i, y i ≠ c := fun i hi => hy.notMem i (hi ▸ hy.left_mem)
  have hxb : ∀ i, y i ≠ d := fun i hi => hy.notMem i (hi ▸ hy.right_mem)
  refine .cycle hm ?_ hy.inj hxa hxb hy.ne hg hy.isLink ?_
  · refine le_antisymm (fun u hu => ?_) (fun u hu => ?_)
    · rcases hT hu with rfl | rfl | hu'
      · exact Or.inl (Or.inr rfl)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr hu'
    · rcases hu with (rfl | rfl) | ⟨i, rfl⟩
      · exact hV hy.left_mem
      · exact hV hy.right_mem
      · exact hy.cover ▸ Or.inr ⟨i, rfl⟩
  · -- the one non-path edge
    have h0 : G.IsLink (f 0) c (pathVertex c y d 1) := by
      have := hy.isLink 0
      rwa [Fin.castSucc_zero, pathVertex_zero, Fin.succ_zero_eq_one] at this
    have hg0 : f 0 ≠ g := by
      intro h'
      rw [h'] at h0
      have h1 : pathVertex c y d 1 = y ⟨0, hm⟩ := pathVertex_eq_of_val_eq_succ c y d (by simp)
      exact hy.notMem ⟨0, hm⟩ (h1 ▸ (hg.right_unique h0) ▸ hy.right_mem)
    intro g' u w hl hne'
    have hu := (hy.sep g' u w hl hne').1
    rcases hT hl.left_mem with rfl | rfl | ⟨i, rfl⟩
    · -- at `d`
      have hlast : G.IsLink (f (Fin.last m)) u (pathVertex c y u (Fin.last m).castSucc) := by
        have := hy.isLink (Fin.last m)
        rw [Fin.succ_last, pathVertex_last] at this
        exact this.symm
      have hgl : f (Fin.last m) ≠ g := by
        intro h'
        have := congrArg Fin.val (hy.eq_zero_of_isLink_left (i := Fin.last m) (y := u) (h' ▸ hg))
        simp at this
        omega
      rcases Graph.isLink_eq_of_degree_eq_two hd2 hgl hlast hg.symm g' w hl with h' | h'
      · exact absurd h' (hne' _)
      · exact h'
    · rcases Graph.isLink_eq_of_degree_eq_two hc2 hg0 h0 hg g' w hl with h' | h'
      · exact absurd h' (hne' _)
      · exact h'
    · exact absurd hu (hy.notMem i)

/-! ## Plumbing for Theorem S -/

/-- (H) forces three bodies. -/
theorem _root_.Graph.IsX0Graph.three_le_ncard_vertexSet [Finite α] {G : Graph α β}
    (hG : G.IsX0Graph) :
    3 ≤ V(G).ncard := by
  obtain ⟨v, hv⟩ := hG.connected.nonempty
  refine (hG.three_le_ncard_closedNbhd v hv).trans (Set.ncard_le_ncard ?_ (Set.toFinite _))
  rintro w (rfl | ⟨e, he⟩)
  · exact hv
  · exact he.right_mem

/-- The identity partition's crossing edges are all of `E(G)`. -/
theorem _root_.Graph.IsX0Graph.crossingEdges_id {G : Graph α β} (hG : G.IsX0Graph) :
    G.crossingEdges id = E(G) := by
  ext e
  refine ⟨fun h => h.1, fun he => ?_⟩
  obtain ⟨x, y, hl⟩ := Graph.exists_isLink_of_mem_edgeSet he
  refine ⟨he, x, y, hl, fun hxy => ?_⟩
  exact hG.simple.toLoopless.not_isLoopAt e x (by rw [show y = x from hxy.symm] at hl; exact hl)

/-- A chain through a body adjacent to another body of degree two has two or more bodies. -/
theorem _root_.Graph.IsChain.two_le_of_adj {G : Graph α β} {V₁ : Set α} {k : ℕ}
    {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β} (hC : G.IsChain V₁ x a b e) {v w : α}
    (hv : v ∈ Set.range x) (hvw : G.Adj v w) (hw : G.degree w = 2) : 2 ≤ k := by
  obtain ⟨i, rfl⟩ := hv
  by_contra hk
  have hk1 := hC.one_le
  obtain rfl : k = 1 := by omega
  obtain rfl : i = 0 := Subsingleton.elim _ _
  obtain ⟨f, hf⟩ := hvw
  have l0 : G.IsLink (e 0) a (x 0) := hC.isLink 0
  have l1 : G.IsLink (e 1) (x 0) b := hC.isLink 1
  rcases hC.toIsOpenEar.isLink_interior 0 hf with rfl | rfl
  · have : w = a := (l0.symm.right_unique hf).symm
    have := hC.three_le_degree_left
    subst_vars; omega
  · have : w = b := (l1.right_unique hf).symm
    have := hC.three_le_degree_right
    subst_vars; omega

/-- Losing a neighbour lowers the degree. -/
theorem _root_.Graph.degree_induce_lt_of_adj [Finite β] {G : Graph α β} {W : Set α} {c x : α}
    (hc : c ∈ W) (hx : x ∉ W) (hadj : G.Adj c x) : (G.induce W).degree c < G.degree c := by
  rw [Graph.degree_eq_ncard_add_ncard, Graph.degree_eq_ncard_add_ncard]
  obtain ⟨f, hf⟩ := hadj
  have hloop : {e | (G.induce W).IsLoopAt e c} ⊆ {e | G.IsLoopAt e c} := fun e he =>
    (show G.IsLink e c c ∧ c ∈ W ∧ c ∈ W from he).1
  have hnl : {e | (G.induce W).IsNonloopAt e c} ⊂ {e | G.IsNonloopAt e c} := by
    have hsub : {e | (G.induce W).IsNonloopAt e c} ⊆ {e | G.IsNonloopAt e c} := by
      rintro e ⟨y, hy, he⟩
      exact ⟨y, hy, (show G.IsLink e c y ∧ c ∈ W ∧ y ∈ W from he).1⟩
    refine (Set.ssubset_iff_of_subset hsub).mpr
      ⟨f, ⟨x, fun h => hx (h ▸ hc), hf⟩, ?_⟩
    rintro ⟨y, hy, hfy⟩
    have hfy' : G.IsLink f c y ∧ c ∈ W ∧ y ∈ W := hfy
    rcases hf.right_eq_or_eq hfy'.1 with h | h
    · exact hx (h ▸ hc)
    · exact hx (h ▸ hfy'.2.2)
  have h1 := Set.ncard_le_ncard hloop (Set.toFinite _)
  have h2 := Set.ncard_lt_ncard hnl (Set.toFinite _)
  omega

/-- The edges from a body into a set avoiding it are at most its degree. -/
theorem _root_.Graph.ncard_setOf_isLink_le_degree [Finite β] {G : Graph α β} {x : α}
    {Y : Set α} (hx : x ∉ Y) : ({e | ∃ y ∈ Y, G.IsLink e x y} : Set β).ncard ≤ G.degree x := by
  rw [Graph.degree_eq_ncard_add_ncard]
  have hsub : ({e | ∃ y ∈ Y, G.IsLink e x y} : Set β) ⊆ {e | G.IsNonloopAt e x} :=
    fun e ⟨y, hy, he⟩ => ⟨y, fun h => hx (h ▸ hy), he⟩
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

/-- In a simple graph, a body with at most one neighbour in `W` sends at most one edge there. -/
theorem _root_.Graph.ncard_setOf_isLink_le_one [Finite β] {G : Graph α β} (hG : G.Simple) {x : α}
    {W : Set α} (hatt : ∀ c₁ ∈ W, ∀ c₂ ∈ W, G.Adj x c₁ → G.Adj x c₂ → c₁ = c₂) :
    ({e | ∃ y ∈ W, G.IsLink e x y} : Set β).ncard ≤ 1 := by
  refine Set.ncard_le_one_iff_subsingleton.mpr fun e ⟨y, hy, he⟩ f ⟨z, hz, hf⟩ => ?_
  obtain rfl := hatt y hy z hz ⟨e, he⟩ ⟨f, hf⟩
  exact hG.eq_of_isLink he hf

end CombinatorialRigidity.Molecular
