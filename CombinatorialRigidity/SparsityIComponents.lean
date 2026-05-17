/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Sparsity

/-!
# Matroidal-regime I-components and augmentation for `(k, ℓ)`-sparsity

The Phase 7 matroid-side scaffolding on top of `Sparsity.lean`, in the
matroidal regime `ℓ < 2 * k` (Whiteley 1996, Lee–Streinu 2008). Two
subsections:

* **Maximal `I`-blocks (I-components).** For a sparse edge set `I` and a
  Finset `X ⊆ V` with `|X| ≥ 2`, the family of `(fromEdgeSet I)`-tight
  Finsets containing `X` is closed under pairwise union; their union
  `G.maxBlock k ℓ X` is itself `G`-tight when non-empty (the maximal
  `I`-block containing `X`). Distinct I-components share at most one
  vertex, hence are edge-disjoint.
* **Matroid augmentation.** For sparse `I, J ⊆ E(K_V)` with `|I| < |J|`,
  some `e ∈ J \ I` extends `I` to a sparser set
  (`IsSparse.exists_aug_of_lt_two_mul`). The combinatorial heart of the
  `(k, ℓ)`-count matroid (`CountMatroid.lean`).

Split out from `Sparsity.lean` at the post-Phase-8 perf pass per the
audit in `notes/PERFORMANCE.md` *Post-Phase-8 file-structure audit →
Split candidates ranked by leverage* §1: this block has exactly one
downstream consumer (`CountMatroid.lean` uses
`IsSparse.exists_aug_of_lt_two_mul` once), so eight of the ten
downstream files can drop ~354 LoC of matroid-regime machinery from
their transitive import set.
-/

public section

namespace SimpleGraph

variable {V : Type*}

/-! ### Matroidal-regime maximal I-blocks (I-components)

For a `(k, ℓ)`-sparse edge set `I` in the matroidal regime `ℓ < 2 * k`, the family of
`(fromEdgeSet I)`-tight Finsets containing a fixed Finset `X ⊆ V` with `|X| ≥ 2` is
closed under pairwise union (`IsTightOn.union_inter_of_pair`); the union of the whole
family — `G.maxBlock k ℓ X` — is therefore itself `G`-tight when
non-empty, the maximal `I`-block containing `X` (or *I-component* of `X`, in
Lee–Streinu's terminology). Distinct I-components share at most one vertex, hence are
edge-disjoint: each non-free I-edge lies in a unique I-component. This scaffolding
drives Phase 7's `(k, ℓ)`-augmentation lemma `IsSparse.exists_aug_of_lt_two_mul`
(Commit 17c). -/

section IComponents

variable [Finite V]

/-- Predicate: some `G`-tight Finset contains `X`. The `maxBlock X` is non-empty
exactly when this holds. Defined for any graph; the matroidal-regime closure
properties (`IsSparse.maxBlock_isTightOn` and friends) need additional sparsity. -/
def HasBlock (G : SimpleGraph V) (k ℓ : ℕ) (X : Finset V) : Prop :=
  ∃ S : Finset V, G.IsTightOn k ℓ S ∧ X ⊆ S

/-- **Maximal block at a Finset `X`** (a.k.a. *`G`-component of `X`* in the
matroidal regime when `G` is sparse), as a Set. The union of all `G`-tight
Finsets containing `X`, viewed as vertices of `V`. The `Finset`-valued version
(after finiteness) is `maxBlock` below. -/
def maxBlockSet (G : SimpleGraph V) (k ℓ : ℕ) (X : Finset V) : Set V :=
  ⋃ (S : Finset V) (_ : G.IsTightOn k ℓ S ∧ X ⊆ S), (↑S : Set V)

/-- `maxBlockSet` is finite when `V` is. -/
lemma maxBlockSet_finite (G : SimpleGraph V) (k ℓ : ℕ) (X : Finset V) :
    (G.maxBlockSet k ℓ X).Finite :=
  (Set.toFinite (Set.univ : Set V)).subset (Set.subset_univ _)

/-- **Maximal block at `X`**, as a `Finset`. -/
noncomputable def maxBlock (G : SimpleGraph V) (k ℓ : ℕ) (X : Finset V) : Finset V :=
  (G.maxBlockSet_finite k ℓ X).toFinset

/-- Membership in `maxBlock`. -/
lemma mem_maxBlock {G : SimpleGraph V} {k ℓ : ℕ} {X : Finset V} {x : V} :
    x ∈ G.maxBlock k ℓ X ↔ ∃ S : Finset V,
      G.IsTightOn k ℓ S ∧ X ⊆ S ∧ x ∈ S := by
  unfold maxBlock
  rw [Set.Finite.mem_toFinset]
  unfold maxBlockSet
  simp [Set.mem_iUnion, and_assoc]

/-- Every `G`-tight Finset containing `X` is contained in `maxBlock X`. -/
lemma subset_maxBlock {G : SimpleGraph V} {k ℓ : ℕ} {X S : Finset V}
    (hS : G.IsTightOn k ℓ S) (hXS : X ⊆ S) :
    S ⊆ G.maxBlock k ℓ X := fun x hxS => by
  rw [mem_maxBlock]
  exact ⟨S, hS, hXS, hxS⟩

/-- `X ⊆ maxBlock X` whenever `HasBlock X`. -/
lemma subset_maxBlock_of_hasBlock {G : SimpleGraph V} {k ℓ : ℕ} {X : Finset V}
    (hB : G.HasBlock k ℓ X) :
    X ⊆ G.maxBlock k ℓ X := by
  obtain ⟨S, hS, hXS⟩ := hB
  exact hXS.trans (subset_maxBlock hS hXS)

/-- **`maxBlock X` is `G`-tight** in the matroidal regime `ℓ < 2*k`, for sparse
`G`, provided `|X| ≥ 2` and some `G`-tight Finset contains `X`. The proof reduces
to "the Set-union of pairwise-union-closed `G`-tight Finsets is itself a
`G`-tight Finset" — a Finset-level closure argument. -/
lemma IsSparse.maxBlock_isTightOn {G : SimpleGraph V} {k ℓ : ℕ}
    (hI : G.IsSparse k ℓ) (hℓ : ℓ < 2 * k)
    {X : Finset V} (hX_card : 2 ≤ X.card) (hB : G.HasBlock k ℓ X) :
    G.IsTightOn k ℓ (G.maxBlock k ℓ X) := by
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hX_card
  -- The maxBlock equals the join of the Finset family {S | G-tight ∧ X ⊆ S}.
  -- We prove the equality `maxBlock X = F.sup id` for an explicit Finset F via
  -- a separate auxiliary lemma path, then run `Finset.sup_mem`.
  -- Strategy: use a noncomputable Fintype instance to express the family as a
  -- `Finset (Finset V)`, then prove the maxBlock coincides with its `Finset.sup`.
  letI : Fintype V := Fintype.ofFinite V
  classical
  set F : Finset (Finset V) := (Finset.univ : Finset (Finset V)).filter
    (fun S => G.IsTightOn k ℓ S ∧ X ⊆ S) with hF_def
  -- maxBlock X = F.sup id as Finsets (set extensionality).
  have h_maxBlock_eq : G.maxBlock k ℓ X = F.sup id := by
    apply Finset.ext
    intro x
    rw [mem_maxBlock]
    simp only [Finset.mem_sup, hF_def, Finset.mem_filter, Finset.mem_univ, true_and,
      id_eq]
    constructor
    · rintro ⟨S, hS, hXS, hxS⟩; exact ⟨S, ⟨hS, hXS⟩, hxS⟩
    · rintro ⟨S, ⟨hS, hXS⟩, hxS⟩; exact ⟨S, hS, hXS, hxS⟩
  rw [h_maxBlock_eq]
  -- Auxiliary predicate P closed under (∅, ⊔) containing every G-tight S ⊇ X.
  let P : Set (Finset V) :=
    { T | T = ∅ ∨ (G.IsTightOn k ℓ T ∧ X ⊆ T) }
  have hP_bot : (∅ : Finset V) ∈ P := Or.inl rfl
  have hP_join : ∀ T₁ ∈ P, ∀ T₂ ∈ P, T₁ ⊔ T₂ ∈ P := by
    intro T₁ hT₁ T₂ hT₂
    rcases hT₁ with hT₁ | ⟨hT₁_tight, hT₁_X⟩
    · subst hT₁; simpa using hT₂
    · rcases hT₂ with hT₂ | ⟨hT₂_tight, hT₂_X⟩
      · subst hT₂; simpa using Or.inr ⟨hT₁_tight, hT₁_X⟩
      · refine Or.inr ⟨?_, hT₁_X.trans Finset.subset_union_left⟩
        exact (hT₁_tight.union_inter_of_pair hℓ hT₂_tight hI huv
          (hT₁_X hu) (hT₁_X hv) (hT₂_X hu) (hT₂_X hv)).1
  have hP_id : ∀ S ∈ F, (id S) ∈ P := by
    intro S hS
    rcases Finset.mem_filter.mp hS with ⟨_, hS_tight, hS_X⟩
    exact Or.inr ⟨hS_tight, hS_X⟩
  have h_sup_in_P : F.sup id ∈ P := Finset.sup_mem P hP_bot hP_join F id hP_id
  -- F.sup id is non-empty since hB witnesses non-emptiness.
  obtain ⟨S₀, hS₀_tight, hS₀_X⟩ := hB
  have h_S₀_in_F : S₀ ∈ F :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS₀_tight, hS₀_X⟩
  have h_u_in_sup : u ∈ F.sup id :=
    (Finset.le_sup (f := id) h_S₀_in_F) (hS₀_X hu)
  rcases h_sup_in_P with h_empty | ⟨h_tight, _⟩
  · rw [h_empty] at h_u_in_sup
    exact absurd h_u_in_sup (Finset.notMem_empty u)
  · exact h_tight

/-- **Edge-disjointness of distinct components.** For sparse `G` in the
matroidal regime, if `Y ⊆ maxBlock X` with both `|X|, |Y| ≥ 2`, then
`maxBlock Y = maxBlock X`. Two distinct non-empty components therefore share
at most one vertex (and so contain no common off-diagonal edge of `K_V`). -/
lemma IsSparse.maxBlock_eq_of_subset_maxBlock {G : SimpleGraph V} {k ℓ : ℕ}
    (hI : G.IsSparse k ℓ) (hℓ : ℓ < 2 * k)
    {X Y : Finset V} (hX_card : 2 ≤ X.card) (hY_card : 2 ≤ Y.card)
    (hBX : G.HasBlock k ℓ X) (hY_sub : Y ⊆ G.maxBlock k ℓ X) :
    G.maxBlock k ℓ Y = G.maxBlock k ℓ X := by
  classical
  have h_X_in_maxX : X ⊆ G.maxBlock k ℓ X := subset_maxBlock_of_hasBlock hBX
  have h_maxX_tight : G.IsTightOn k ℓ (G.maxBlock k ℓ X) :=
    hI.maxBlock_isTightOn hℓ hX_card hBX
  -- `maxBlock X` itself is a G-tight Finset ⊇ Y, hence ⊆ maxBlock Y.
  have h_maxX_sub_maxY : G.maxBlock k ℓ X ⊆ G.maxBlock k ℓ Y :=
    subset_maxBlock h_maxX_tight hY_sub
  -- Reverse: maxBlock Y is G-tight (HasBlock Y witnessed by maxBlock X), and shares
  -- ≥ 2 vertices with maxBlock X, so their union is G-tight + ⊇ X + ⊆ maxBlock X.
  have h_BY : G.HasBlock k ℓ Y := ⟨G.maxBlock k ℓ X, h_maxX_tight, hY_sub⟩
  have h_maxY_tight : G.IsTightOn k ℓ (G.maxBlock k ℓ Y) :=
    hI.maxBlock_isTightOn hℓ hY_card h_BY
  have h_Y_in_maxY : Y ⊆ G.maxBlock k ℓ Y := subset_maxBlock_of_hasBlock h_BY
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hY_card
  have h_union := (h_maxX_tight.union_inter_of_pair hℓ h_maxY_tight hI huv
    (hY_sub hu) (hY_sub hv) (h_Y_in_maxY hu) (h_Y_in_maxY hv)).1
  have h_union_X : X ⊆ G.maxBlock k ℓ X ∪ G.maxBlock k ℓ Y :=
    h_X_in_maxX.trans Finset.subset_union_left
  have h_maxY_sub_maxX : G.maxBlock k ℓ Y ⊆ G.maxBlock k ℓ X :=
    Finset.subset_union_right.trans (subset_maxBlock h_union h_union_X)
  exact Finset.Subset.antisymm h_maxY_sub_maxX h_maxX_sub_maxY

end IComponents

/-! ### Augmentation in the matroidal regime (`ℓ < 2 * k`)

The combinatorial heart of the `(k, ℓ)`-count matroid (Whiteley 1996, Lee–Streinu 2008):
for `(k, ℓ)`-sparse edge sets `I, J ⊆ E(K_V)` with `|I| < |J|`, some `e ∈ J \ I` extends
`I` to a sparser set. The proof argues by contradiction via the *I-component* partition
(`SimpleGraph.maxBlock` from the previous section): if no augmentation exists, every
`e ∈ J \ I` forces its endpoints into a (non-trivial) I-component, which then accounts
for `e`. J-sparsity at each I-component vs I-tightness at the same component bounds the
J-edge count from above by the I-edge count; the free edges (no endpoints in any
I-component) on the J-side embed into the I-side; summing gives `|J| ≤ |I|`. -/

section Augmentation

variable [Finite V]

/-- **Off-diagonality of edges gives `u ≠ v`.** Pair-form specialization of
mathlib's `SimpleGraph.not_isDiag_of_mem_edgeSet` (applied to `⊤`) through
`Sym2.mk_isDiag_iff`. -/
private lemma ne_of_mem_top_edgeSet {V : Type*} {u v : V}
    (he : s(u, v) ∈ (⊤ : SimpleGraph V).edgeSet) : u ≠ v :=
  Sym2.mk_isDiag_iff.not.mp ((⊤ : SimpleGraph V).not_isDiag_of_mem_edgeSet he)

/-- **Matroid augmentation in the matroidal regime.** For finite `V` and `ℓ < 2 * k`,
if `I, J ⊆ E(K_V)` are both `(k, ℓ)`-sparse with `|I| < |J|`, then some `e ∈ J \ I`
extends `I` to a `(k, ℓ)`-sparse edge set: `(fromEdgeSet (insert e I)).IsSparse k ℓ`.

The combinatorial axiom of the `(k, ℓ)`-count matroid (Whiteley 1996, Lee–Streinu 2008).
Proof via the I-component decomposition: assuming no augmentation, every `e ∈ J \ I` is
forced into a component (`SimpleGraph.maxBlock` of its endpoints), and the partition
identity `|J| = ∑_C |edgesIn(J) C| + |J_free| ≤ ∑_C |edgesIn(I) C| + |I_free| = |I|`
contradicts `|I| < |J|`. -/
theorem IsSparse.exists_aug_of_lt_two_mul {k ℓ : ℕ} (hℓ : ℓ < 2 * k)
    {I J : Set (Sym2 V)} (hI : (fromEdgeSet I).IsSparse k ℓ)
    (hJ : (fromEdgeSet J).IsSparse k ℓ)
    (hI_off : I ⊆ (⊤ : SimpleGraph V).edgeSet)
    (hJ_off : J ⊆ (⊤ : SimpleGraph V).edgeSet)
    (hcard : I.ncard < J.ncard) :
    ∃ e ∈ J \ I, (fromEdgeSet (insert e I)).IsSparse k ℓ := by
  by_contra h_no_aug
  push Not at h_no_aug
  -- Setup: V is a Fintype, top.edgeSet is finite, so I, J are finite.
  letI : Fintype V := Fintype.ofFinite V
  classical
  have h_top_fin : ((⊤ : SimpleGraph V).edgeSet).Finite := (⊤ : SimpleGraph V).edgeSet.toFinite
  have hI_fin : I.Finite := h_top_fin.subset hI_off
  have hJ_fin : J.Finite := h_top_fin.subset hJ_off
  -- (Step 1) For each e ∈ J \ I, the I-component `maxBlock e.toFinset` is well-defined.
  -- `hBlock e he_diff : HasBlock e.toFinset`.
  have hBlock : ∀ {e : Sym2 V}, e ∈ J \ I → (fromEdgeSet I).HasBlock k ℓ e.toFinset := by
    intro e ⟨he_J, he_I⟩
    induction e with | h u v => ?_
    rw [Sym2.toFinset_mk_eq]
    have huv : u ≠ v := ne_of_mem_top_edgeSet (hJ_off he_J)
    obtain ⟨S, hu_S, hv_S, hS_tight⟩ :=
      hI.exists_isTightOn_of_insert_not_sparse huv he_I (h_no_aug s(u, v) ⟨he_J, he_I⟩)
    refine ⟨S, hS_tight, ?_⟩
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  -- Anchor finset of an edge: `{u, v}` for `e = s(u, v)`. Has card 2 off-diag.
  have h_toFinset_card_two : ∀ {e : Sym2 V}, e ∈ J \ I → 2 ≤ e.toFinset.card := fun he_diff =>
    (Sym2.card_toFinset_of_not_isDiag _
      ((⊤ : SimpleGraph V).not_isDiag_of_mem_edgeSet (hJ_off he_diff.1))).ge
  -- (Step 2) Comps: the Finset of distinct I-components of edges in J \ I.
  -- Using J as the indexing source; for e ∉ J\I we'll see this never matters.
  have hdiff_fin : (J \ I).Finite := hJ_fin.subset Set.diff_subset
  set diff_fin : Finset (Sym2 V) := hdiff_fin.toFinset with hdiff_def
  set Comps : Finset (Finset V) :=
    diff_fin.image (fun e => (fromEdgeSet I).maxBlock k ℓ e.toFinset) with hComps_def
  have hmem_diff : ∀ {e : Sym2 V}, e ∈ diff_fin ↔ e ∈ J \ I := by
    intro e; rw [hdiff_def]; exact Set.Finite.mem_toFinset _
  -- (Step 3) Each C ∈ Comps is I-tight (non-empty), has |C| ≥ 2.
  have hC_tight : ∀ C ∈ Comps, (fromEdgeSet I).IsTightOn k ℓ C := by
    intro C hC
    rw [hComps_def, Finset.mem_image] at hC
    obtain ⟨e, he_diff, rfl⟩ := hC
    rw [hmem_diff] at he_diff
    exact hI.maxBlock_isTightOn hℓ (h_toFinset_card_two he_diff) (hBlock he_diff)
  have hC_card_two : ∀ C ∈ Comps, 2 ≤ C.card := by
    intro C hC
    rw [hComps_def, Finset.mem_image] at hC
    obtain ⟨e, he_diff, rfl⟩ := hC
    rw [hmem_diff] at he_diff
    -- maxBlock contains the anchor, which has card 2.
    have h_anchor_sub : e.toFinset ⊆ (fromEdgeSet I).maxBlock k ℓ e.toFinset :=
      subset_maxBlock_of_hasBlock (hBlock he_diff)
    exact (h_toFinset_card_two he_diff).trans (Finset.card_le_card h_anchor_sub)
  -- (Step 4) Edge-disjointness: every off-diag e ∈ K_V is in at most one C ∈ Comps,
  -- where "e is in C" means `e.toFinset ⊆ C`.
  have h_edge_uniq : ∀ {e : Sym2 V}, e ∈ (⊤ : SimpleGraph V).edgeSet →
      ∀ C₁ ∈ Comps, ∀ C₂ ∈ Comps,
        e.toFinset ⊆ C₁ → e.toFinset ⊆ C₂ → C₁ = C₂ := by
    intro e he_top C₁ hC₁ C₂ hC₂ h1 h2
    -- Both C₁ and C₂ are maxBlocks; e.toFinset ⊆ both ∩ has card 2.
    rw [hComps_def, Finset.mem_image] at hC₁ hC₂
    obtain ⟨e₁, he₁_diff, rfl⟩ := hC₁
    obtain ⟨e₂, he₂_diff, rfl⟩ := hC₂
    rw [hmem_diff] at he₁_diff he₂_diff
    -- Reduce both equalities to `maxBlock e.toFinset`.
    have he_card_two : 2 ≤ e.toFinset.card :=
      (Sym2.card_toFinset_of_not_isDiag _ ((⊤ : SimpleGraph V).not_isDiag_of_mem_edgeSet he_top)).ge
    have h_eq₁ : (fromEdgeSet I).maxBlock k ℓ e.toFinset
        = (fromEdgeSet I).maxBlock k ℓ e₁.toFinset :=
      hI.maxBlock_eq_of_subset_maxBlock hℓ (h_toFinset_card_two he₁_diff) he_card_two
        (hBlock he₁_diff) h1
    have h_eq₂ : (fromEdgeSet I).maxBlock k ℓ e.toFinset
        = (fromEdgeSet I).maxBlock k ℓ e₂.toFinset :=
      hI.maxBlock_eq_of_subset_maxBlock hℓ (h_toFinset_card_two he₂_diff) he_card_two
        (hBlock he₂_diff) h2
    rw [← h_eq₁, ← h_eq₂]
  -- (Step 5) Partition pieces and disjointness.
  -- The "components piece" for X: ⋃_{C ∈ Comps} X ∩ ↑C.sym2.
  -- For e off-diag in C.sym2, e.toFinset ⊆ C. (The off-diag hypothesis is not needed;
  -- `Sym2.coe_toFinset` bridges the Sym2-to-Set coercion to the Finset.toFinset version.)
  have h_toFinset_sub_iff : ∀ {e : Sym2 V} {C : Finset V},
      e ∈ ((↑C : Set V).sym2) ↔ e.toFinset ⊆ C := by
    intro e C
    rw [Set.mem_sym2_iff_subset, ← Sym2.coe_toFinset, Finset.coe_subset]
  -- The components partition: pairwise disjoint X ∩ ↑C.sym2.
  have h_pairwiseDisjoint : ∀ {X : Set (Sym2 V)}, X ⊆ (⊤ : SimpleGraph V).edgeSet →
      (↑Comps : Set (Finset V)).PairwiseDisjoint (fun C : Finset V => X ∩ (↑C : Set V).sym2) := by
    intro X hX C₁ hC₁ C₂ hC₂ hC12
    refine Set.disjoint_left.mpr ?_
    intro e ⟨he_X, he_C₁⟩ ⟨_, he_C₂⟩
    refine hC12 ?_
    exact h_edge_uniq (hX he_X) C₁ hC₁ C₂ hC₂
      (h_toFinset_sub_iff.mp he_C₁) (h_toFinset_sub_iff.mp he_C₂)
  -- (Step 7) For each C ∈ Comps: J-card on C ≤ I-card on C (I-tightness + J-sparsity).
  have h_C_ineq : ∀ C ∈ Comps,
      (J ∩ (↑C : Set V).sym2).ncard ≤ (I ∩ (↑C : Set V).sym2).ncard := by
    intro C hC
    have hC_I_tight := hC_tight C hC
    have hC_size : ℓ ≤ k * C.card := by unfold IsTightOn at hC_I_tight; omega
    have hC_J_sparse := hJ C hC_size
    rw [edgesIn_fromEdgeSet_of_off_diag hJ_off (↑C : Set V)] at hC_J_sparse
    rw [← edgesIn_fromEdgeSet_of_off_diag hI_off (↑C : Set V)]
    unfold IsTightOn at hC_I_tight
    omega
  -- (Step 8) Decompose I and J into "in some component" + "free", and count.
  -- For X (= I or J), Xfree := X \ ⋃_{C ∈ Comps} (↑C).sym2.
  set CompsUnion : Set (Sym2 V) :=
    ⋃ (C : Finset V) (_ : C ∈ Comps), ((↑C : Set V).sym2) with hCU_def
  -- (Step 8a) Partition each X = (X ∩ CompsUnion) ⊔ (X \ CompsUnion).
  have h_split : ∀ {X : Set (Sym2 V)}, X.Finite →
      X.ncard = (X ∩ CompsUnion).ncard + (X \ CompsUnion).ncard := fun {X} hX_fin =>
    (Set.ncard_inter_add_ncard_diff_eq_ncard X CompsUnion hX_fin).symm
  -- (Step 8b) X ∩ CompsUnion = ⋃_C (X ∩ ↑C.sym2); pairwise disjoint by edge-uniqueness.
  -- Therefore (X ∩ CompsUnion).ncard = ∑_C (X ∩ ↑C.sym2).ncard.
  have h_compsUnion_ncard : ∀ {X : Set (Sym2 V)}, X ⊆ (⊤ : SimpleGraph V).edgeSet → X.Finite →
      (X ∩ CompsUnion).ncard = ∑ C ∈ Comps, (X ∩ (↑C : Set V).sym2).ncard := by
    intro X hX hX_fin
    have h_inter_iUnion : X ∩ CompsUnion =
        ⋃ C ∈ (↑Comps : Set (Finset V)), X ∩ (↑C : Set V).sym2 := by
      rw [hCU_def]
      ext e
      simp only [Set.mem_inter_iff, Set.mem_iUnion, Finset.mem_coe]
      tauto
    rw [h_inter_iUnion]
    have h_pd : (↑Comps : Set (Finset V)).PairwiseDisjoint
        (fun C : Finset V => X ∩ (↑C : Set V).sym2) := h_pairwiseDisjoint hX
    have h_finset_fin : Set.Finite (↑Comps : Set (Finset V)) := Comps.finite_toSet
    have h_each_fin : ∀ C ∈ (↑Comps : Set (Finset V)), (X ∩ (↑C : Set V).sym2).Finite :=
      fun _ _ => hX_fin.subset Set.inter_subset_left
    rw [Set.Finite.ncard_biUnion h_finset_fin h_each_fin h_pd, finsum_mem_coe_finset]
  -- (Step 8c) The free part: every e ∈ J \ CompsUnion lies in I (and outside CompsUnion).
  -- Because every e ∈ J \ I would (by contradiction hypothesis) be inside some I-component.
  have h_free_sub : J \ CompsUnion ⊆ I \ CompsUnion := by
    intro e ⟨he_J, he_notIn⟩
    refine ⟨?_, he_notIn⟩
    by_contra he_notI
    -- e ∈ J \ I, so e.toFinset ⊆ maxBlock e.toFinset ∈ Comps, so e ∈ ↑C.sym2 ⊆ CompsUnion.
    have he_diff : e ∈ J \ I := ⟨he_J, he_notI⟩
    have h_block := hBlock he_diff
    have h_sub : e.toFinset ⊆ (fromEdgeSet I).maxBlock k ℓ e.toFinset :=
      subset_maxBlock_of_hasBlock h_block
    have he_in : e ∈ (↑((fromEdgeSet I).maxBlock k ℓ e.toFinset) : Set V).sym2 :=
      h_toFinset_sub_iff.mpr h_sub
    apply he_notIn
    rw [hCU_def]
    refine Set.mem_iUnion.mpr ⟨(fromEdgeSet I).maxBlock k ℓ e.toFinset, ?_⟩
    refine Set.mem_iUnion.mpr ⟨?_, he_in⟩
    rw [hComps_def]
    refine Finset.mem_image.mpr ⟨e, ?_, rfl⟩
    rw [hmem_diff]; exact he_diff
  -- (Step 9) Assemble: |J| ≤ |I|.
  have hI_compsUnion := h_compsUnion_ncard hI_off hI_fin
  have hJ_compsUnion := h_compsUnion_ncard hJ_off hJ_fin
  have hJ_split := h_split hJ_fin
  have hI_split := h_split hI_fin
  have h_diff_le : (J \ CompsUnion).ncard ≤ (I \ CompsUnion).ncard :=
    Set.ncard_le_ncard h_free_sub (hI_fin.subset Set.diff_subset)
  have h_sum_le : ∑ C ∈ Comps, (J ∩ (↑C : Set V).sym2).ncard ≤
      ∑ C ∈ Comps, (I ∩ (↑C : Set V).sym2).ncard :=
    Finset.sum_le_sum h_C_ineq
  have h_total : J.ncard ≤ I.ncard := by
    rw [hJ_split, hI_split, hJ_compsUnion, hI_compsUnion]
    exact Nat.add_le_add h_sum_le h_diff_le
  omega

end Augmentation

end SimpleGraph
