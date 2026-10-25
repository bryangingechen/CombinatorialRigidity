/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.AlgebraicInduction.PanelHinge

/-!
# The rank at generic normals, and counting rows and motions

Lemmas for the proof of KT Theorem 5.5 (Katoh and Tanigawa 2011, *A proof of the molecular
conjecture*, Discrete Comput. Geom. **45**, §§5–6), presented in
`sec:molecular-algebraic-induction-genericity` and `sec:molecular-algebraic-induction-relative`. The
file proves:

* that rows independent at one choice of normals bound the motions at some normals
  (`lem:relative-device-count`), and give a realization rigid on `V(G)`
  (`lem:realization-of-independent-rows`);
* that rows of one framework that are rows of another stay independent
  (`lem:case-II-placement-old-rows`);
* the dimension of the motions and the rank of a framework rigid on `V(G)`
  (`lem:case-II-placement-old-rows-extract`), and the bound on the rank by the deficiency
  (`lem:relative-deficiency-rank-bound`, in `sec:molecular-deficiency-rank-bound`);
* independent rows from a bound on the rank (`lem:independent-rows-of-rank`) and from rigidity
  (`lem:case-II-placement-old-rows-extract`);
* a polynomial in the normals off whose zeros a bound on the rank holds (`lem:genericity-device`,
  `lem:rank-polynomial-of-le-finrank`), and its forms for frameworks rigid on a set of bodies;
* that a generic full-rank realization has nondegenerate hinges (`lem:generic-yields-genuine-hinge`,
  in `sec:molecular-algebraic-induction-base`).
-/

@[expose] public section

namespace CombinatorialRigidity.Molecular

variable {k : ℕ}
variable {K : Type*} [Field K]

open scoped Graph

variable {α β : Type*}

/-! ## Independent rows at one choice of normals bound the motions (`lem:relative-device-count`)

The lemmas of this section find their normals off the zeros of a minor of the rows, as in
`lem:rank-polynomial-of-le-finrank`. The blueprint's proofs take the given normals, which satisfy
the same bound. -/

/-- **Independent forms at one point bound the motions at another** (a step of
`lem:relative-device-count`): let `F p` be body-hinge frameworks on the bodies `α`, indexed by the
points `p : σ → K`, with forms `g p i` whose coordinates under `φ` are the values at `p` of
polynomials `c i j` (`hg`), and whose common kernel contains the motions of `F p` (`hcoord`). If the
forms indexed by `s` are linearly independent at `p₀`, there is a point `p` with
`#s + dim Z(F p) ≤ D|α|`. `exists_finrank_dualCoannihilator_polynomial`, for `K` infinite, gives a
point at which the common kernel of the forms has dimension at most `D|α| − #s`
(`finrank_screwAssignment`), and that kernel contains `Z(F p)`. The hypotheses give the bound at
`p₀` itself. Only `exists_good_realization_reindex` uses it. -/
theorem exists_good_realization [Infinite K] [Fintype α] {ι σ : Type*} [Finite ι]
    (F : (σ → K) → BodyHingeFramework K k α β)
    (g : (σ → K) → ι → Module.Dual K (α → ScrewSpace K k))
    (c : ι → Fin (Module.finrank K (Module.Dual K (α → ScrewSpace K k))) → MvPolynomial σ K)
    (φ : Module.Dual K (α → ScrewSpace K k)
      ≃ₗ[K] (Fin (Module.finrank K (Module.Dual K (α → ScrewSpace K k))) → K))
    (hg : ∀ p i j, φ (g p i) j = MvPolynomial.eval p (c i j))
    (hcoord : ∀ p, (F p).infinitesimalMotions
      ≤ (Submodule.span K (Set.range (g p))).dualCoannihilator)
    {p₀ : σ → K} {s : Set ι}
    (hindep : LinearIndependent K (fun i : s => g p₀ i)) :
    ∃ p : σ → K, Nat.card s + Module.finrank K (F p).infinitesimalMotions
      ≤ screwDim k * Fintype.card α := by
  obtain ⟨p, hp⟩ := exists_finrank_dualCoannihilator_polynomial g c φ hg hindep
  refine ⟨p, ?_⟩
  rw [BodyHingeFramework.finrank_screwAssignment (K := K) (k := k) (α := α)] at hp
  exact le_trans (by gcongr; exact Submodule.finrank_mono (hcoord p)) hp

/-- **The same, with the coordinates indexed by any type** (a step of `lem:relative-device-count`):
`exists_good_realization` with `φ` valued in `ν → K`, for a type `ν` in bijection `e` with
`Fin (finrank …)`, so that the coordinates can be those of the standard basis of
`α → ScrewSpace K k`. It composes `φ` with the reindexing `LinearEquiv.funCongrLeft K K e`. Only
`exists_good_realization_ofParam` uses it. -/
theorem exists_good_realization_reindex [Infinite K] [Fintype α] {ι ν σ : Type*} [Finite ι]
    (e : Fin (Module.finrank K (Module.Dual K (α → ScrewSpace K k))) ≃ ν)
    (F : (σ → K) → BodyHingeFramework K k α β)
    (g : (σ → K) → ι → Module.Dual K (α → ScrewSpace K k))
    (c : ι → ν → MvPolynomial σ K)
    (φ : Module.Dual K (α → ScrewSpace K k) ≃ₗ[K] (ν → K))
    (hg : ∀ p i j, φ (g p i) j = MvPolynomial.eval p (c i j))
    (hcoord : ∀ p, (F p).infinitesimalMotions
      ≤ (Submodule.span K (Set.range (g p))).dualCoannihilator)
    {p₀ : σ → K} {s : Set ι}
    (hindep : LinearIndependent K (fun i : s => g p₀ i)) :
    ∃ p : σ → K, Nat.card s + Module.finrank K (F p).infinitesimalMotions
      ≤ screwDim k * Fintype.card α :=
  exists_good_realization F g (fun i j => c i (e j)) (φ.trans (LinearEquiv.funCongrLeft K K e))
    (fun p i j => by simp only [LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply,
      LinearMap.funLeft_apply, hg]) hcoord hindep

/-- **Independent rows of a panel-hinge framework bound its motions at some normals** (a step of
`lem:relative-device-count`): if `ends` gives every edge label a link of `G` (`hends`) and the rows
`panelRow ends i` of `ofNormals G ends q₀` indexed by `s` are linearly independent, there are
normals `q` with `#s + dim Z(G,q) ≤ D|α|`. The coordinates of the rows in the standard basis
`Pi.basis (fun _ => screwBasis k)` are the polynomials `annihRowPoly` in the normals, scaled by
`[u = a] − [v = a]` at the body `a` for an edge with selected ends `u` and `v` (`hg`, by
`annihRowPoly_eval`; `lem:rows-polynomial-in-normals`). The rows lie in the row space at every `q`,
so their common kernel contains the motions (`hcoord`), and `exists_good_realization_reindex`
applies. The normals `q₀` satisfy the bound themselves. Only `exists_relative_full_count_ofParam`
uses it. -/
theorem PanelHingeFramework.exists_good_realization_ofParam [Infinite K] [Fintype α]
    (G : Graph α β) (ends : β → α × α) [Finite β]
    (hends : ∀ e, G.IsLink e (ends e).1 (ends e).2)
    {q₀ : α × Fin (k + 2) → K}
    {s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)}
    (hindep : LinearIndependent K
      (fun i : s => (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.panelRow ends i)) :
    ∃ q : α × Fin (k + 2) → K,
      Nat.card s + Module.finrank K
        (PanelHingeFramework.ofNormals G ends q).toBodyHinge.infinitesimalMotions
        ≤ screwDim k * Fintype.card α := by
  classical
  -- The body-hinge family parametrized by free normal assignments `q`.
  set F : (α × Fin (k + 2) → K) → BodyHingeFramework K k α β :=
    fun q => (PanelHingeFramework.ofNormals G ends q).toBodyHinge with hF
  -- The standard basis of `α → ScrewSpace K k` and the dual-basis identification `φ`.
  set B : Module.Basis (Σ _ : α, Set.powersetCard (Fin (k + 2)) k) K (α → ScrewSpace K k) :=
    Pi.basis (fun _ : α => screwBasis k) with hB
  set φ : Module.Dual K (α → ScrewSpace K k)
      ≃ₗ[K] ((Σ _ : α, Set.powersetCard (Fin (k + 2)) k) → K) := B.dualBasis.equivFun with hφ
  -- The cardinality bridge: `card ν = finrank (Dual (α → ScrewSpace K k))`.
  have hcard : Fintype.card (Σ _ : α, Set.powersetCard (Fin (k + 2)) k)
      = Module.finrank K (Module.Dual K (α → ScrewSpace K k)) := by
    rw [Subspace.dual_finrank_eq, Module.finrank_eq_card_basis B]
  let e : Fin (Module.finrank K (Module.Dual K (α → ScrewSpace K k)))
      ≃ (Σ _ : α, Set.powersetCard (Fin (k + 2)) k) :=
    (Fintype.equivFinOfCardEq hcard).symm
  -- The row family and its polynomial coordinates.
  set g : (α × Fin (k + 2) → K)
      → (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)
      → Module.Dual K (α → ScrewSpace K k) :=
    fun q i => (F q).panelRow ends i with hg_def
  set c : (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)
      → (Σ _ : α, Set.powersetCard (Fin (k + 2)) k) → MvPolynomial (α × Fin (k + 2)) K :=
    fun i j => ((if (ends i.1).1 = j.1 then (1 : K) else 0)
        - (if (ends i.1).2 = j.1 then 1 else 0))
      • annihRowPoly (ends i.1).1 (ends i.1).2 i.2.1 i.2.2 j.2 with hc_def
  -- The evaluation identity `hg`: each row coordinate is the panel polynomial `c`.
  have hg : ∀ q i j, φ (g q i) j = MvPolynomial.eval q (c i j) := by
    intro q i j
    obtain ⟨a, t⟩ := j
    -- `φ (g q i) ⟨a,t⟩ = (g q i) (B ⟨a,t⟩)`; unfold `g`, `panelRow`, `φ`, the support extensor.
    rw [hφ, Module.Basis.dualBasis_equivFun, hg_def, hc_def, hB, Pi.basis_apply]
    change BodyHingeFramework.panelRow _ ends i (Pi.single a (screwBasis k t)) = _
    rw [BodyHingeFramework.panelRow, BodyHingeFramework.hingeRow_apply, hF,
      PanelHingeFramework.toBodyHinge_supportExtensor,
      PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal,
      PanelHingeFramework.ofNormals_normal, MvPolynomial.smul_eval, annihRowPoly_eval]
    -- `B⟨a,t⟩ u − B⟨a,t⟩ v = ([u=a]−[v=a])•screwBasis t`; push `annihRow` through by linearity,
    -- then settle the boole arithmetic `[u=a] − [v=a]` per case.
    rw [Pi.single_apply, Pi.single_apply]
    by_cases hu : (ends i.1).1 = a <;> by_cases hv : (ends i.1).2 = a <;>
      simp only [hu, hv, ite_true, ite_false, sub_zero, zero_sub, sub_self, map_zero,
        map_neg, one_mul, neg_mul, zero_mul]
  -- The span containment `hcoord`: the panel rows lie in the rigidity rows (at any hinges), so
  -- their span is contained and the coannihilator reversed.
  have hsub : ∀ q, Submodule.span K (Set.range (g q)) ≤ Submodule.span K (F q).rigidityRows := by
    intro q
    rw [Submodule.span_le, hg_def]
    rintro _ ⟨⟨e', t₁, t₂⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨e', (ends e').1, (ends e').2, ?_,
      annihRow ((F q).supportExtensor e') t₁ t₂, ?_, rfl⟩
    · rw [hF]; exact hends e'
    · rw [BodyHingeFramework.hingeRowBlock_apply, Submodule.mem_dualAnnihilator]
      intro x hx
      rw [Submodule.mem_span_singleton] at hx
      obtain ⟨r, rfl⟩ := hx
      rw [map_smul, annihRow_apply_self, smul_zero]
  have hcoord : ∀ q, (F q).infinitesimalMotions
      ≤ (Submodule.span K (Set.range (g q))).dualCoannihilator := by
    intro q
    rw [(F q).infinitesimalMotions_eq_dualCoannihilator]
    exact Submodule.dualCoannihilator_anti (hsub q)
  exact exists_good_realization_reindex e F g c φ hg hcoord hindep

/-- **Independent rows bound the motions** (`lem:relative-device-count`): if `ends` gives every edge
label a link of `G`, `V(G)` is nonempty, and at the normals `q₀` some `m ≥ D(|V(G)| − 1)` rows
`panelRow ends i` of `ofNormals G ends q₀` are linearly independent (`hindep`, `hcard`), there are
normals `q` with `dim Z(G,q) ≤ D(|V(G)ᶜ| + 1)`. It takes `q` from `exists_good_realization_ofParam`
and substitutes `|α| = |V(G)| + |V(G)ᶜ|` (`Set.ncard_add_ncard_compl`). Only
`hasFullRankRealization_of_independent_panelRow` uses it. -/
theorem PanelHingeFramework.exists_relative_full_count_ofParam [Infinite K] [Finite α]
    (G : Graph α β) (ends : β → α × α) [Finite β]
    (hends : ∀ e, G.IsLink e (ends e).1 (ends e).2) (hne : V(G).Nonempty)
    {q₀ : α × Fin (k + 2) → K}
    {s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)}
    (hindep : LinearIndependent K
      (fun i : s => (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.panelRow ends i))
    (hcard : screwDim k * (V(G).ncard - 1) ≤ Nat.card s) :
    ∃ q : α × Fin (k + 2) → K,
      Module.finrank K
        (PanelHingeFramework.ofNormals G ends q).toBodyHinge.infinitesimalMotions
        ≤ screwDim k * ((V(G))ᶜ.ncard + 1) := by
  have : Fintype α := Fintype.ofFinite α
  obtain ⟨q, hq⟩ := PanelHingeFramework.exists_good_realization_ofParam G ends hends hindep
  refine ⟨q, ?_⟩
  -- `1 ≤ |V(G)|` since `V(G)` is nonempty.
  have h1 : 1 ≤ V(G).ncard := (Set.ncard_pos (Set.toFinite _)).2 hne
  -- The product identities `omega` needs: `D·|α| = D·|V(G)| + D·|V(G)ᶜ|`, the relative target
  -- `D·(|V(G)| − 1) = D·|V(G)| − D`, and the goal's `D·(|V(G)ᶜ| + 1) = D·|V(G)ᶜ| + D`.
  have hsplit : screwDim k * Fintype.card α
      = screwDim k * V(G).ncard + screwDim k * (V(G))ᶜ.ncard := by
    rw [← Nat.mul_add, Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card]
  rw [Nat.mul_succ]
  rw [Nat.mul_sub, Nat.mul_one] at hcard
  have hge : screwDim k ≤ screwDim k * V(G).ncard := Nat.le_mul_of_pos_right _ h1
  omega

/-- **A rigid realization from independent rows** (`lem:realization-of-independent-rows`): under the
hypotheses of `exists_relative_full_count_ofParam`, `G` has a full-rank realization: at the normals
`q` of that lemma, `ofNormals G ends q` is infinitesimally rigid on `V(G)`
(`isInfinitesimallyRigidOn_vertexSet_of_finrank_le`). No declaration uses it. -/
theorem PanelHingeFramework.hasFullRankRealization_of_independent_panelRow
    [Infinite K] [Finite α] [Finite β]
    (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e, G.IsLink e (ends e).1 (ends e).2) (hne : V(G).Nonempty)
    {q₀ : α × Fin (k + 2) → K}
    {s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)}
    (hindep : LinearIndependent K
      (fun i : s => (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.panelRow ends i))
    (hcard : screwDim k * (V(G).ncard - 1) ≤ Nat.card s) :
    PanelHingeFramework.HasFullRankRealization K k G := by
  obtain ⟨q, hq⟩ :=
    PanelHingeFramework.exists_relative_full_count_ofParam G ends hends hne hindep hcard
  refine ⟨PanelHingeFramework.ofNormals G ends q,
    PanelHingeFramework.ofNormals_graph G ends q, ?_⟩
  have hG : (PanelHingeFramework.ofNormals G ends q).toBodyHinge.graph = G := rfl
  have hrig := (PanelHingeFramework.ofNormals G ends q).toBodyHinge
    |>.isInfinitesimallyRigidOn_vertexSet_of_finrank_le (by rw [hG]; exact hne)
      (by rw [hG]; exact hq)
  rw [hG] at hrig
  exact hrig

/-! ## Rows shared by two frameworks (`lem:case-II-placement-old-rows`) -/

/-- **Rows shared by two frameworks** (`lem:case-II-placement-old-rows`): let `f : s₂ → s₁` be
injective, and let the row `panelRow ends₂ i` of `ofNormals G₂ ends₂ q₂` be the row
`panelRow ends₁ (f i)` of `ofNormals G₁ ends₁ q₁` for every `i ∈ s₂` (`hrow`). If the rows of the
first framework indexed by `s₁` are linearly independent, so are those of the second indexed by
`s₂`: they are a subfamily, along `f`, of an independent family (`LinearIndependent.comp`).

A row depends only on the selector's pair at its edge label and on the normals there
(`toBodyHinge_supportExtensor`), not on the graph. So `hrow` holds, with `f` the identity, at labels
where `ends₁` and `ends₂` agree and `q₁` and `q₂` agree at both ends; for instance at the edges that
`G` and the graph `G_v^{ab}` obtained by splitting off `v` share (`lem:splitoff-edge-substitution`).
`case_II_placement_eq612` uses it, and no main result uses that. -/
theorem PanelHingeFramework.exists_independent_panelRow_transport {α β : Type*}
    (G₁ G₂ : Graph α β) (ends₁ ends₂ : β → α × α) (q₁ q₂ : α × Fin (k + 2) → K)
    {hlinks₁ : RecordsLinks G₁ ends₁} {hlinks₂ : RecordsLinks G₂ ends₂}
    {s₁ s₂ : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)}
    (f : s₂ → s₁) (hf : Function.Injective f)
    (hrow : ∀ i : s₂, (PanelHingeFramework.ofNormals G₂ ends₂ q₂).toBodyHinge.panelRow ends₂
        (i : β × _ × _)
      = (PanelHingeFramework.ofNormals G₁ ends₁ q₁).toBodyHinge.panelRow ends₁
        ((f i : s₁) : β × _ × _))
    (hindep : LinearIndependent K (fun i : s₁ =>
      (PanelHingeFramework.ofNormals G₁ ends₁ q₁).toBodyHinge.panelRow ends₁ (i : β × _ × _))) :
    LinearIndependent K (fun i : s₂ =>
      (PanelHingeFramework.ofNormals G₂ ends₂ q₂).toBodyHinge.panelRow ends₂ (i : β × _ × _)) := by
  have h := hindep.comp f hf
  have he : (fun i : s₂ =>
        (PanelHingeFramework.ofNormals G₂ ends₂ q₂).toBodyHinge.panelRow ends₂ (i : β × _ × _))
      = ((fun i : s₁ =>
        (PanelHingeFramework.ofNormals G₁ ends₁ q₁).toBodyHinge.panelRow ends₁ (i : β × _ × _))
          ∘ f) := funext hrow
  rw [he]; exact h

/-! ## The motions and the rank of a framework rigid on a set of bodies -/

/-- **The motions of a framework rigid on a set `s`** (a step of `lem:case-I-realization` and of
`lem:case-II-placement-old-rows-extract`): if `s` is nonempty and every motion is constant on `s`,
then `dim Z(G,p) ≤ D(|sᶜ| + 1)`. For a body `v₀ ∈ s`, a motion that vanishes at `v₀` vanishes on
`s`, so the single-body pin `pinnedMotions v₀` is the block pin `pinnedMotionsOn s`
(`pinnedMotionsOn_mono` for the other inclusion), of dimension at most `D·|sᶜ|`
(`finrank_pinnedMotionsOn_le`); KT Lemma 5.1 (p. 667) adds `D`
(`finrank_pinnedMotions_add_screwDim`). The bound can be strict, as a body of `V(G) ∖ s` can lie on
an edge; at `s = V(G)` it is an equality
(`finrank_infinitesimalMotions_of_isInfinitesimallyRigidOn_vertexSet`). -/
theorem BodyHingeFramework.finrank_infinitesimalMotions_le_of_isInfinitesimallyRigidOn
    [Finite α] (F : BodyHingeFramework K k α β) {s : Set α} (hne : s.Nonempty)
    (hrig : F.IsInfinitesimallyRigidOn s) :
    Module.finrank K F.infinitesimalMotions ≤ screwDim k * (sᶜ.ncard + 1) := by
  have : Fintype α := Fintype.ofFinite α
  obtain ⟨v₀, hv₀⟩ := hne
  have : Nonempty α := ⟨v₀⟩
  -- Rigidity on `s` equates the single-body pin at `v₀ ∈ s` with the block pin on `s`.
  have hpin : F.pinnedMotions v₀ = F.pinnedMotionsOn s := by
    rw [← F.pinnedMotionsOn_singleton]
    refine le_antisymm (fun S hS => ?_)
      (F.pinnedMotionsOn_mono (Set.singleton_subset_iff.2 hv₀))
    rw [F.mem_pinnedMotionsOn] at hS ⊢
    refine ⟨hS.1, fun w hw => ?_⟩
    rw [hrig S hS.1 w hw v₀ hv₀, hS.2 v₀ rfl]
  -- `dim Z = finrank (pinnedMotions v₀) + D = finrank (pinnedMotionsOn s) + D ≤ D·|sᶜ| + D`.
  have hadd := F.finrank_pinnedMotions_add_screwDim v₀
  have hle := F.finrank_pinnedMotionsOn_le s
  rw [hpin] at hadd
  rw [Nat.mul_succ]
  omega

/-- **The motions of a framework rigid on `V(G)`** (`lem:case-II-placement-old-rows-extract`, its
first claim): if `V(G)` is nonempty and every motion is constant on `V(G)` (`hrig`), then
`dim Z(G,p) = D(|V(G)ᶜ| + 1)`. The bound `≤` is
`finrank_infinitesimalMotions_le_of_isInfinitesimallyRigidOn` at `s = V(G)`. Conversely, for a body
`v₀ ∈ V(G)`, the block pin `pinnedMotionsOn V(G)`, of dimension `D·|V(G)ᶜ|`
(`finrank_pinnedMotionsOn_vertexSet`, `lem:relative-screw-split`), lies in the single-body pin
`pinnedMotions v₀` (`pinnedMotionsOn_le_pinnedMotions`), of dimension `dim Z(G,p) − D` (KT Lemma
5.1, p. 667; `finrank_pinnedMotions_add_screwDim`). The converse is
`isInfinitesimallyRigidOn_vertexSet_of_finrank_le` (`lem:isInfRigidOn-of-relative-count`). -/
theorem BodyHingeFramework.finrank_infinitesimalMotions_of_isInfinitesimallyRigidOn_vertexSet
    [Finite α] (F : BodyHingeFramework K k α β) (hne : F.graph.vertexSet.Nonempty)
    (hrig : F.IsInfinitesimallyRigidOn F.graph.vertexSet) :
    Module.finrank K F.infinitesimalMotions = screwDim k * ((F.graph.vertexSet)ᶜ.ncard + 1) := by
  refine le_antisymm (F.finrank_infinitesimalMotions_le_of_isInfinitesimallyRigidOn hne hrig) ?_
  obtain ⟨v₀, hv₀⟩ := hne
  have : Nonempty α := ⟨v₀⟩
  -- `D·|V(G)ᶜ| = finrank (pinnedMotionsOn V(G)) ≤ finrank (pinnedMotions v₀) = dim Z − D`.
  have hle := Submodule.finrank_mono (F.pinnedMotionsOn_le_pinnedMotions hv₀)
  rw [F.finrank_pinnedMotionsOn_vertexSet] at hle
  have hadd := F.finrank_pinnedMotions_add_screwDim v₀
  rw [Nat.mul_succ]
  omega

/-- **Rank–nullity for the rigidity matrix** (the identity `dim Z(G,p) = D|W| − rank R(G,p)` of
`def:rigidity-matrix`): for a body-hinge framework on finitely many bodies `α`,
`rank R(G,p) + dim Z(G,p) = D·|α|`, as `Z(G,p)` is the common kernel of the rows
(`infinitesimalMotions_eq_dualCoannihilator`, `Subspace.finrank_add_finrank_dualAnnihilator_eq`). -/
theorem BodyHingeFramework.finrank_span_rigidityRows_add_finrank_infinitesimalMotions
    [Finite α] (F : BodyHingeFramework K k α β) :
    Module.finrank K (Submodule.span K F.rigidityRows)
      + Module.finrank K F.infinitesimalMotions
      = screwDim k * Nat.card α := by
  have : Fintype α := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card]
  set Φ : Subspace K (Module.Dual K (α → ScrewSpace K k)) := Submodule.span K F.rigidityRows
  have hcompl : Module.finrank K Φ + Module.finrank K Φ.dualCoannihilator
      = Module.finrank K (α → ScrewSpace K k) := by
    rw [Subspace.finrank_dualCoannihilator_eq, Subspace.finrank_add_finrank_dualAnnihilator_eq,
      Subspace.dual_finrank_eq]
  rw [← F.infinitesimalMotions_eq_dualCoannihilator, BodyHingeFramework.finrank_screwAssignment]
    at hcompl
  linarith

/-- **The rank of a framework rigid on `V(G)`** (a step of `lem:case-II-placement-old-rows-extract`
and of the lemmas that use it): if `V(G)` is nonempty and every motion is constant on `V(G)`, then
`rank R(G,p) = D(|V(G)| − 1)`. The rank is `D|α| − dim Z(G,p)`
(`finrank_span_rigidityRows_add_finrank_infinitesimalMotions`), and `dim Z(G,p) = D(|V(G)ᶜ| + 1)`
(`finrank_infinitesimalMotions_of_isInfinitesimallyRigidOn_vertexSet`). No condition on the hinges
is needed; the rows `panelRow` span the row space only at nondegenerate hinges
(`span_panelRow_eq_rigidityRows`). -/
theorem BodyHingeFramework.finrank_span_rigidityRows_of_rigidOn
    [Finite α] (F : BodyHingeFramework K k α β) (hnev : F.graph.vertexSet.Nonempty)
    (hrig : F.IsInfinitesimallyRigidOn F.graph.vertexSet) :
    Module.finrank K (Submodule.span K F.rigidityRows)
      = screwDim k * (F.graph.vertexSet.ncard - 1) := by
  have hZ := F.finrank_infinitesimalMotions_of_isInfinitesimallyRigidOn_vertexSet hnev hrig
  have hcompl := F.finrank_span_rigidityRows_add_finrank_infinitesimalMotions
  have h1 : 1 ≤ F.graph.vertexSet.ncard := (Set.ncard_pos (Set.toFinite _)).2 hnev
  have hsplit : screwDim k * Nat.card α
      = screwDim k * F.graph.vertexSet.ncard + screwDim k * (F.graph.vertexSet)ᶜ.ncard := by
    rw [← Nat.mul_add, Set.ncard_add_ncard_compl]
  rw [Nat.mul_succ] at hZ
  rw [Nat.mul_sub, Nat.mul_one]
  omega

/-- **Rigidity on `V(G)` is the rank `D(|V(G)| − 1)`** (`rem:rank-hypothesis-relative` at deficiency
zero): if `V(G)` is nonempty, every motion is constant on `V(G)` if and only if
`rank R(G,p) = D(|V(G)| − 1)`. Forward, `finrank_span_rigidityRows_of_rigidOn`; backward,
rank–nullity (`finrank_span_rigidityRows_add_finrank_infinitesimalMotions`) gives
`dim Z(G,p) = D(|V(G)ᶜ| + 1)`, and `isInfinitesimallyRigidOn_vertexSet_of_finrank_le` gives
rigidity. No condition on the hinges is needed. -/
theorem BodyHingeFramework.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows
    [Finite α] (F : BodyHingeFramework K k α β) (hne : F.graph.vertexSet.Nonempty) :
    F.IsInfinitesimallyRigidOn F.graph.vertexSet ↔
      Module.finrank K (Submodule.span K F.rigidityRows)
        = screwDim k * (F.graph.vertexSet.ncard - 1) := by
  have : Fintype α := Fintype.ofFinite α
  constructor
  · exact F.finrank_span_rigidityRows_of_rigidOn hne
  · intro hcount
    apply isInfinitesimallyRigidOn_vertexSet_of_finrank_le F hne
    -- Rank–nullity (`finrank_span_rigidityRows_add_finrank_infinitesimalMotions`).
    have hcompl := F.finrank_span_rigidityRows_add_finrank_infinitesimalMotions
    have hsplit : screwDim k * Nat.card α
        = screwDim k * F.graph.vertexSet.ncard + screwDim k * (F.graph.vertexSet)ᶜ.ncard := by
      rw [← Nat.mul_add, Set.ncard_add_ncard_compl]
    have h1 : 1 ≤ F.graph.vertexSet.ncard := (Set.ncard_pos (Set.toFinite _)).2 hne
    -- `finrank Z = D·|α| − D·(|V|−1) = D + D·|Vᶜ| = D·(|Vᶜ|+1)`.
    -- Lift to ℤ to handle the Nat subtraction in `hcount`.
    zify [h1] at hcount hcompl hsplit ⊢
    linarith

/-- **The rank is at most the target rank** (`lem:relative-deficiency-rank-bound`, its rank form):
if `bodyBarDim n = screwDim k` (`hn`), `V(G)` is nonempty and the hinge at every link is
nondegenerate (`hC`), then `rank R(G,p) ≤ D(|V(G)| − 1) − def(G̃)`, in `ℤ`. It is the form for
motions, `screwDim_mul_compl_add_deficiency_le_finrank_infinitesimalMotions`, with rank–nullity
(`finrank_span_rigidityRows_add_finrank_infinitesimalMotions`) and `|α| = |V(G)| + |V(G)ᶜ|`. -/
theorem BodyHingeFramework.finrank_span_rigidityRows_add_deficiency_le
    [Finite α] [Finite β] {n : ℕ}
    (F : BodyHingeFramework K k α β)
    (hn : Graph.bodyBarDim n = screwDim k)
    (hne : F.graph.vertexSet.Nonempty)
    (hC : ∀ e u v, F.graph.IsLink e u v → F.supportExtensor e ≠ 0) :
    (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
      ≤ screwDim k * (F.graph.vertexSet.ncard - 1 : ℤ) - F.graph.deficiency n := by
  have : Fintype α := Fintype.ofFinite α
  have hcompl := F.finrank_span_rigidityRows_add_finrank_infinitesimalMotions
  have hhub := F.screwDim_mul_compl_add_deficiency_le_finrank_infinitesimalMotions hn hne hC
  have hsplit : screwDim k * Nat.card α
      = screwDim k * F.graph.vertexSet.ncard + screwDim k * F.graph.vertexSetᶜ.ncard := by
    rw [← Nat.mul_add,
      Set.ncard_add_ncard_compl F.graph.vertexSet (Set.toFinite _) (Set.toFinite _)]
  have h1 : 1 ≤ F.graph.vertexSet.ncard := (Set.ncard_pos (Set.toFinite _)).2 hne
  rw [Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at hcompl
  zify [h1] at hcompl hhub hsplit ⊢
  linarith

/-! ## Independent rows from rigidity or from a bound on the rank -/

/-- **Independent rows of a framework rigid on `V(G)`** (`lem:case-II-placement-old-rows-extract`,
its second claim): if `ends` gives every edge label a link of `G` (`hends`), every hinge is
nondegenerate (`hne`, at every label), `V(G)` is nonempty and every motion is constant on `V(G)`,
then some `D(|V(G)| − 1)` rows `panelRow ends i` are linearly independent. The rows span the row
space (`span_panelRow_eq_rigidityRows`), of dimension `D(|V(G)| − 1)`
(`finrank_span_rigidityRows_of_rigidOn`), and `Submodule.exists_fun_fin_finrank_span_eq` picks a
basis among them; their indices form the set `s`.

A star forest gives fewer rows: `exists_independent_rigidityRows_of_starForest` gives `D − 1` at
each of its edges, at most `(D − 1)(|V| − 1)` in all, fewer than `D(|V| − 1)` when `|V| ≥ 2`. No
declaration uses this lemma: `exists_independent_panelRow_subfamily_of_rigidOn_linking` is the form
the proofs use, which asks `hends` and `hne` only at links. -/
theorem BodyHingeFramework.exists_independent_panelRow_subfamily_of_rigidOn
    [Finite α] [Finite β] (F : BodyHingeFramework K k α β) {ends : β → α × α}
    (hends : ∀ e, F.graph.IsLink e (ends e).1 (ends e).2)
    (hne : ∀ e, F.supportExtensor e ≠ 0)
    (hnev : F.graph.vertexSet.Nonempty)
    (hrig : F.IsInfinitesimallyRigidOn F.graph.vertexSet) :
    ∃ s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      Nat.card s = screwDim k * (F.graph.vertexSet.ncard - 1) ∧
      LinearIndependent K (fun i : s => F.panelRow ends (i : β × _ × _)) := by
  classical
  have : Fintype α := Fintype.ofFinite α
  set T := Set.range (F.panelRow ends) with hT
  have : Module.Finite K (Submodule.span K T) :=
    Module.Finite.span_of_finite K (Set.finite_range _)
  -- At nondegenerate hinges the panel rows span the rigidity rows
  -- (`span_panelRow_eq_rigidityRows`), whose span has dimension `D(|V| − 1)`
  -- (`finrank_span_rigidityRows_of_rigidOn`).
  have hfin : Module.finrank K (Submodule.span K T)
      = screwDim k * (F.graph.vertexSet.ncard - 1) := by
    rw [hT, F.span_panelRow_eq_rigidityRows hends hne]
    exact F.finrank_span_rigidityRows_of_rigidOn hnev hrig
  -- Extract a `Fin (D(|V| − 1))`-indexed independent subfamily of *actual* panel rows.
  obtain ⟨f, hfmem, hfspan, hfindep⟩ := Submodule.exists_fun_fin_finrank_span_eq K T
  choose idx hidx using hfmem
  -- Re-index each chosen row by its `(edge, ⋀^k-pair)`; injective since the rows are independent.
  set j : Fin (Module.finrank K (Submodule.span K T))
      → (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k) :=
    fun i => idx i with hj
  have hjinj : Function.Injective j := by
    intro a b hab
    rw [hj] at hab
    simp only at hab
    have : f a = f b := by rw [← hidx a, ← hidx b, hab]
    exact hfindep.injective this
  refine ⟨Set.range j, ?_, ?_⟩
  · simp only [Nat.card_range_of_injective hjinj, Nat.card_eq_fintype_card, Fintype.card_fin, hfin]
  · -- The `range j`-subfamily of `panelRow` is `f` reindexed across `Equiv.ofInjective j`.
    have hreindex : (fun i : Set.range j => F.panelRow ends (i : β × _ × _))
        ∘ (Equiv.ofInjective j hjinj) = f := by
      funext a
      simp only [Function.comp_apply, Equiv.ofInjective_apply]
      rw [hj]
      exact hidx a
    have hindep2 :=
      hfindep.comp (Equiv.ofInjective j hjinj).symm (Equiv.ofInjective j hjinj).symm.injective
    rw [← hreindex, Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] at hindep2
    exact hindep2

/-- **Independent rows from a bound on the rank** (`lem:independent-rows-of-rank`): if `ends` gives
every link of `G` its ends (`hends`), the hinge at every link is nondegenerate (`hne`) and
`N ≤ rank R(G,p)`, then some `N` rows `panelRow ends i` at links of `G` are linearly independent.
The rows at links span the row space (`span_panelRow_linking_eq_rigidityRows`);
`Submodule.exists_fun_fin_finrank_span_eq` picks a basis among them, and its first `N` members
(`Fin.castLE`) are the rows, indexed by their edge and pair of coordinates. -/
theorem BodyHingeFramework.exists_independent_panelRow_subfamily_of_le_finrank
    [Finite α] [Finite β] (F : BodyHingeFramework K k α β) {ends : β → α × α}
    (hends : ∀ e u v, F.graph.IsLink e u v → F.graph.IsLink e (ends e).1 (ends e).2)
    (hne : ∀ e, F.graph.IsLink e (ends e).1 (ends e).2 → F.supportExtensor e ≠ 0)
    {N : ℕ} (hN : N ≤ Module.finrank K (Submodule.span K F.rigidityRows)) :
    ∃ s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      (∀ i ∈ s, F.graph.IsLink (i : β × _ × _).1 (ends (i : β × _ × _).1).1
        (ends (i : β × _ × _).1).2) ∧
      Nat.card s = N ∧
      LinearIndependent K (fun i : s => F.panelRow ends (i : β × _ × _)) := by
  classical
  have : Fintype α := Fintype.ofFinite α
  -- The linking-edge index subtype and the panel-row family restricted to it.
  set L := {i : β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k //
    F.graph.IsLink i.1 (ends i.1).1 (ends i.1).2} with hL
  set T := Set.range (fun i : L => F.panelRow ends (i : β × _ × _)) with hT
  have : Module.Finite K (Submodule.span K T) :=
    Module.Finite.span_of_finite K (Set.finite_range _)
  -- The linking-edge panel rows span the rigidity rows, so the rank bound transports to `span T`.
  have hNle : N ≤ Module.finrank K (Submodule.span K T) := by
    rw [hT, F.span_panelRow_linking_eq_rigidityRows hends hne]; exact hN
  -- Extract the full `Fin (finrank (span T))`-indexed independent linking-panel-row family.
  obtain ⟨f, hfmem, hfspan, hfindep⟩ := Submodule.exists_fun_fin_finrank_span_eq K T
  choose idx hidx using hfmem
  -- Cut to the first `N` members through `Fin.castLE hNle`, re-indexing each by its
  -- `(linking edge, ⋀^k-pair)` index.
  set j : Fin N → L := fun i => idx (Fin.castLE hNle i) with hj
  set j' : Fin N → (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k) :=
    fun i => (j i : β × _ × _) with hj'
  have hj'inj : Function.Injective j' := by
    intro a b hab
    rw [hj', hj] at hab
    have hidxab : idx (Fin.castLE hNle a) = idx (Fin.castLE hNle b) := Subtype.coe_injective hab
    have : f (Fin.castLE hNle a) = f (Fin.castLE hNle b) := by
      rw [← hidx (Fin.castLE hNle a), ← hidx (Fin.castLE hNle b), hidxab]
    exact Fin.castLE_injective hNle (hfindep.injective this)
  refine ⟨Set.range j', ?_, ?_, ?_⟩
  · rintro i ⟨a, rfl⟩; exact (j a).2
  · rw [Nat.card_range_of_injective hj'inj, Nat.card_eq_fintype_card, Fintype.card_fin]
  · -- The `range j'`-subfamily of `panelRow` is `f ∘ Fin.castLE hNle` reindexed across
    -- `Equiv.ofInjective j'`.
    have hreindex : (fun i : Set.range j' => F.panelRow ends (i : β × _ × _))
        ∘ (Equiv.ofInjective j' hj'inj) = f ∘ Fin.castLE hNle := by
      funext a
      simp only [Function.comp_apply, Equiv.ofInjective_apply]
      rw [hj', hj]
      exact hidx (Fin.castLE hNle a)
    have hindep2 :=
      (hfindep.comp (Fin.castLE hNle) (Fin.castLE_injective hNle)).comp
        (Equiv.ofInjective j' hj'inj).symm (Equiv.ofInjective j' hj'inj).symm.injective
    rw [← hreindex, Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] at hindep2
    exact hindep2

/-- **Independent rows at links of a framework rigid on `V(G)`** (a step of
`lem:generic-realization-of-rigid`, `lem:claim-6-4`, `lem:case-II-realization-placement` and
`lem:case-I-realization-h65`): `exists_independent_panelRow_subfamily_of_rigidOn` with `hends` and
`hne` asked only at links: some `D(|V(G)| − 1)` rows at links of `G` are linearly independent. It is
`exists_independent_panelRow_subfamily_of_le_finrank` at `N = D(|V(G)| − 1)`, the rank of
`finrank_span_rigidityRows_of_rigidOn`. -/
theorem BodyHingeFramework.exists_independent_panelRow_subfamily_of_rigidOn_linking
    [Finite α] [Finite β] (F : BodyHingeFramework K k α β) {ends : β → α × α}
    (hends : ∀ e u v, F.graph.IsLink e u v → F.graph.IsLink e (ends e).1 (ends e).2)
    (hne : ∀ e, F.graph.IsLink e (ends e).1 (ends e).2 → F.supportExtensor e ≠ 0)
    (hnev : F.graph.vertexSet.Nonempty)
    (hrig : F.IsInfinitesimallyRigidOn F.graph.vertexSet) :
    ∃ s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      (∀ i ∈ s, F.graph.IsLink (i : β × _ × _).1 (ends (i : β × _ × _).1).1
        (ends (i : β × _ × _).1).2) ∧
      Nat.card s = screwDim k * (F.graph.vertexSet.ncard - 1) ∧
      LinearIndependent K (fun i : s => F.panelRow ends (i : β × _ × _)) :=
  F.exists_independent_panelRow_subfamily_of_le_finrank hends hne
    (F.finrank_span_rigidityRows_of_rigidOn hnev hrig).ge

/-- **Independent rows at links of a framework rigid on a set `s`** (a step of
`lem:case-I-realization`): if `ends` gives every link of `G` its ends, the hinge at every link is
nondegenerate, `s` is nonempty and every motion is constant on `s`, then some `t` of at least
`D(|s| − 1)` rows at links of `G` are linearly independent. Rank–nullity
(`finrank_span_rigidityRows_add_finrank_infinitesimalMotions`) and
`finrank_infinitesimalMotions_le_of_isInfinitesimallyRigidOn` bound the rank below by `D(|s| − 1)`,
and the rows at links span the row space (`span_panelRow_linking_eq_rigidityRows`). Only
`exists_rankPolynomial_of_rigidOn_linking_set` uses it. -/
theorem BodyHingeFramework.exists_independent_panelRow_subfamily_of_rigidOn_linking_set
    [Finite α] [Finite β] (F : BodyHingeFramework K k α β) {ends : β → α × α} {s : Set α}
    (hends : ∀ e u v, F.graph.IsLink e u v → F.graph.IsLink e (ends e).1 (ends e).2)
    (hne : ∀ e, F.graph.IsLink e (ends e).1 (ends e).2 → F.supportExtensor e ≠ 0)
    (hnes : s.Nonempty)
    (hrig : F.IsInfinitesimallyRigidOn s) :
    ∃ t : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      (∀ i ∈ t, F.graph.IsLink (i : β × _ × _).1 (ends (i : β × _ × _).1).1
        (ends (i : β × _ × _).1).2) ∧
      screwDim k * (s.ncard - 1) ≤ Nat.card t ∧
      LinearIndependent K (fun i : t => F.panelRow ends (i : β × _ × _)) := by
  classical
  have : Fintype α := Fintype.ofFinite α
  -- The linking-edge index subtype and the panel-row family restricted to it.
  set L := {i : β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k //
    F.graph.IsLink i.1 (ends i.1).1 (ends i.1).2} with hL
  set T := Set.range (fun i : L => F.panelRow ends (i : β × _ × _)) with hT
  have : Module.Finite K (Submodule.span K T) :=
    Module.Finite.span_of_finite K (Set.finite_range _)
  -- Rigidity on `s` bounds the motions by `D·(|sᶜ| + 1)`.
  have hZ : Module.finrank K F.infinitesimalMotions ≤ screwDim k * (sᶜ.ncard + 1) :=
    F.finrank_infinitesimalMotions_le_of_isInfinitesimallyRigidOn hnes hrig
  have h1 : 1 ≤ s.ncard := (Set.ncard_pos (Set.toFinite _)).2 hnes
  have hsplit : screwDim k * Nat.card α = screwDim k * s.ncard + screwDim k * sᶜ.ncard := by
    rw [← Nat.mul_add, Set.ncard_add_ncard_compl]
  -- The linking-edge panel-row span has dimension `≥ D|α| − dim Z ≥ D(|s| − 1)` (rigid on `s`).
  have hfin : screwDim k * (s.ncard - 1) ≤ Module.finrank K (Submodule.span K T) := by
    -- At nondegenerate hinges the panel rows at links span the rigidity rows
    -- (`span_panelRow_linking_eq_rigidityRows`); rank–nullity
    -- (`finrank_span_rigidityRows_add_finrank_infinitesimalMotions`).
    rw [hT, F.span_panelRow_linking_eq_rigidityRows hends hne]
    have hcompl := F.finrank_span_rigidityRows_add_finrank_infinitesimalMotions
    rw [Nat.mul_sub, Nat.mul_one]
    rw [Nat.mul_succ] at hZ
    omega
  -- Extract an independent subfamily of `finrank (span T) ≥ D(|s|−1)` *actual* linking panel rows.
  obtain ⟨f, hfmem, hfspan, hfindep⟩ := Submodule.exists_fun_fin_finrank_span_eq K T
  choose idx hidx using hfmem
  -- Re-index each chosen row by its underlying `(linking edge, ⋀^k-pair)` index.
  set j : Fin (Module.finrank K (Submodule.span K T)) → L := fun i => idx i with hj
  set j' : Fin (Module.finrank K (Submodule.span K T))
      → (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k) :=
    fun i => (j i : β × _ × _) with hj'
  have hj'inj : Function.Injective j' := by
    intro a b hab
    rw [hj', hj] at hab
    have hidxab : idx a = idx b := Subtype.coe_injective hab
    have : f a = f b := by rw [← hidx a, ← hidx b, hidxab]
    exact hfindep.injective this
  refine ⟨Set.range j', ?_, ?_, ?_⟩
  · rintro i ⟨a, rfl⟩; exact (j a).2
  · rw [Nat.card_range_of_injective hj'inj, Nat.card_eq_fintype_card, Fintype.card_fin]
    exact hfin
  · -- The `range j'`-subfamily of `panelRow` is `f` reindexed across `Equiv.ofInjective j'`.
    have hreindex : (fun i : Set.range j' => F.panelRow ends (i : β × _ × _))
        ∘ (Equiv.ofInjective j' hj'inj) = f := by
      funext a
      simp only [Function.comp_apply, Equiv.ofInjective_apply]
      rw [hj', hj]
      exact hidx a
    have hindep2 :=
      hfindep.comp (Equiv.ofInjective j' hj'inj).symm (Equiv.ofInjective j' hj'inj).symm.injective
    rw [← hreindex, Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] at hindep2
    exact hindep2

/-! ## The rank off the zeros of a polynomial (`lem:rank-polynomial-of-le-finrank`)

The first lemma gives, for rows independent at the normals `q₀`, a polynomial in the normals that
does not vanish at `q₀` and off whose zeros the rows stay independent; the others apply it to rows
that rigidity or a bound on the rank gives. -/

/-- **Independent rows stay independent off the zeros of a polynomial** (a step of
`lem:rank-polynomial-of-le-finrank`, `lem:generic-realization-of-rigid` and
`lem:case-I-realization`): if the rows `panelRow ends i` of `ofNormals G ends q₀` indexed by `s` are
linearly independent, there is a polynomial `Q` with `Q(q₀) ≠ 0` such that they are linearly
independent at every `q` with `Q(q) ≠ 0`. The coordinates of the rows in the standard basis
`Pi.basis (fun _ => screwBasis k)` are the polynomials `annihRowPoly` in the normals, scaled by
`[u = a] − [v = a]` at the body `a` for an edge with selected ends `u` and `v` (`annihRowPoly_eval`,
`lem:rows-polynomial-in-normals`), and `Q` is a maximal minor of them that does not vanish at `q₀`
(`exists_polynomial_ne_zero_of_linearIndependent_at`). -/
theorem PanelHingeFramework.exists_rankPolynomial_of_linearIndependent [Finite α] [Finite β]
    (G : Graph α β) (ends : β → α × α) {q₀ : α × Fin (k + 2) → K}
    {hlinks : RecordsLinks G ends}
    {s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)}
    (hindep : LinearIndependent K
      (fun i : s => (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.panelRow ends i)) :
    ∃ Q : MvPolynomial (α × Fin (k + 2)) K, MvPolynomial.eval q₀ Q ≠ 0 ∧
      ∀ q : α × Fin (k + 2) → K, MvPolynomial.eval q Q ≠ 0 →
        LinearIndependent K
          (fun i : s => (PanelHingeFramework.ofNormals G ends q).toBodyHinge.panelRow ends i) := by
  classical
  have : Fintype α := Fintype.ofFinite α
  -- The standard basis of `α → ScrewSpace K k`, its dual-basis identification `φ`, and the bridge
  -- to the canonical `Fin (finrank …)` index that the mirror lemma's `c`/`φ` require.
  set B : Module.Basis (Σ _ : α, Set.powersetCard (Fin (k + 2)) k) K (α → ScrewSpace K k) :=
    Pi.basis (fun _ : α => screwBasis k) with hB
  have hcard : Fintype.card (Σ _ : α, Set.powersetCard (Fin (k + 2)) k)
      = Module.finrank K (Module.Dual K (α → ScrewSpace K k)) := by
    rw [Subspace.dual_finrank_eq, Module.finrank_eq_card_basis B]
  let e : Fin (Module.finrank K (Module.Dual K (α → ScrewSpace K k)))
      ≃ (Σ _ : α, Set.powersetCard (Fin (k + 2)) k) :=
    (Fintype.equivFinOfCardEq hcard).symm
  set φ : Module.Dual K (α → ScrewSpace K k)
      ≃ₗ[K] (Fin (Module.finrank K (Module.Dual K (α → ScrewSpace K k))) → K) :=
    B.dualBasis.equivFun.trans (LinearEquiv.funCongrLeft K K e) with hφ
  -- The row family and its degree-2 panel-polynomial coordinates, pulled back along `e`.
  set g : (α × Fin (k + 2) → K)
      → (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)
      → Module.Dual K (α → ScrewSpace K k) :=
    fun q i => (PanelHingeFramework.ofNormals G ends q).toBodyHinge.panelRow ends i with hg_def
  set c : (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)
      → Fin (Module.finrank K (Module.Dual K (α → ScrewSpace K k)))
      → MvPolynomial (α × Fin (k + 2)) K :=
    fun i j => ((if (ends i.1).1 = (e j).1 then (1 : K) else 0)
        - (if (ends i.1).2 = (e j).1 then 1 else 0))
      • annihRowPoly (ends i.1).1 (ends i.1).2 i.2.1 i.2.2 (e j).2 with hc_def
  -- The evaluation identity: each row coordinate is the panel polynomial `c`.
  have hg : ∀ q i j, φ (g q i) j = MvPolynomial.eval q (c i j) := by
    intro q i j
    rw [hφ, LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
      Module.Basis.dualBasis_equivFun, hg_def, hc_def]
    rcases hej : e j with ⟨a, t⟩
    simp only [hej]
    simp only [hB, Pi.basis_apply]
    change BodyHingeFramework.panelRow _ ends i (Pi.single a (screwBasis k t)) = _
    rw [BodyHingeFramework.panelRow, BodyHingeFramework.hingeRow_apply,
      PanelHingeFramework.toBodyHinge_supportExtensor,
      PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal,
      PanelHingeFramework.ofNormals_normal, MvPolynomial.smul_eval, annihRowPoly_eval]
    rw [Pi.single_apply, Pi.single_apply]
    by_cases hu : (ends i.1).1 = a <;> by_cases hv : (ends i.1).2 = a <;>
      simp only [hu, hv, ite_true, ite_false, sub_zero, zero_sub, sub_self, map_zero,
        map_neg, one_mul, neg_mul, zero_mul]
  -- A maximal minor (`exists_polynomial_ne_zero_of_linearIndependent_at`).
  obtain ⟨Q, hQ₀, hQ⟩ :=
    exists_polynomial_ne_zero_of_linearIndependent_at g c φ hg
      (p₀ := q₀) (s := s) (by simpa only [hg_def] using hindep)
  exact ⟨Q, hQ₀, fun q hq => by simpa only [hg_def] using hQ q hq⟩

/-- **A framework rigid on `V(G)` gives a rank polynomial** (a step of
`lem:generic-realization-of-rigid`): if `ends` gives every link of `G` its ends, the hinge of
`ofNormals G ends q₀` at every link is nondegenerate (`hne`), `V(G)` is nonempty and the framework
is rigid on `V(G)`, then there are rows `s` at links of `G`, at least `D(|V(G)| − 1)` of them, and a
polynomial `Q` with `Q(q₀) ≠ 0`, such that the rows indexed by `s` are linearly independent at
every `q` with `Q(q) ≠ 0`. The rows are those of
`exists_independent_panelRow_subfamily_of_rigidOn_linking`, and `Q` is that of
`exists_rankPolynomial_of_linearIndependent`. -/
theorem PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking [Finite α] [Finite β]
    (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2)
    {q₀ : α × Fin (k + 2) → K}
    (hne : ∀ e, G.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.supportExtensor e ≠ 0)
    (hnev : V(G).Nonempty)
    (hrig : (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.IsInfinitesimallyRigidOn V(G)) :
    ∃ (s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k))
      (Q : MvPolynomial (α × Fin (k + 2)) K),
      (∀ i ∈ s, G.IsLink (i : β × _ × _).1 (ends (i : β × _ × _).1).1
        (ends (i : β × _ × _).1).2) ∧
      screwDim k * (V(G).ncard - 1) ≤ Nat.card s ∧ MvPolynomial.eval q₀ Q ≠ 0 ∧
      ∀ q : α × Fin (k + 2) → K, MvPolynomial.eval q Q ≠ 0 →
        LinearIndependent K
          (fun i : s => (PanelHingeFramework.ofNormals G ends q).toBodyHinge.panelRow ends i) := by
  set F := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge with hF
  -- Some `D(|V(G)|−1)` panel rows at links of `G` are independent at `q₀`.
  obtain ⟨s, hsupp, hscard, hsindep⟩ :=
    F.exists_independent_panelRow_subfamily_of_rigidOn_linking
      (ends := ends) (by simpa [hF] using hends) (by simpa [hF] using hne)
      (by simpa [hF] using hnev)
      (by simpa [hF] using hrig)
  obtain ⟨Q, hQ₀, hQ⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_linearIndependent G ends hsindep
  exact ⟨s, Q, hsupp, hscard.ge, hQ₀, hQ⟩

/-- **A rank bound off the zeros of a polynomial** (`lem:rank-polynomial-of-le-finrank`, and
`lem:genericity-device` in the terms of KT §5.1): if `ends` gives every link of `G` its ends, the
hinge of `ofNormals G ends q₀` at every link is nondegenerate, and `N ≤ rank R(G,q₀)`, then there is
a polynomial `Q` with `Q(q₀) ≠ 0` such that `N ≤ rank R(G,q)` at every `q` with `Q(q) ≠ 0`. Some `N`
rows at links are independent at `q₀` (`exists_independent_panelRow_subfamily_of_le_finrank`), and
`Q` is a maximal minor of them (`exists_rankPolynomial_of_linearIndependent`). Where `Q(q) ≠ 0`
they are independent and lie in the row space, as they are at links, so the rank is at least `N`
(`finrank_span_eq_card`). It assumes no rigidity: the proofs of Case II
(`case_II_realization_all_k`) and of KT Lemma 6.1 (p. 672; `case_cut_edge_realization_gp_gen`) apply
it at deficient realizations. -/
theorem PanelHingeFramework.exists_rankPolynomial_of_le_finrank_linking [Finite α] [Finite β]
    (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2)
    {q₀ : α × Fin (k + 2) → K}
    (hne : ∀ e, G.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.supportExtensor e ≠ 0)
    {N : ℕ} (hN : N ≤ Module.finrank K
        (Submodule.span K (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.rigidityRows)) :
    ∃ Q : MvPolynomial (α × Fin (k + 2)) K,
      MvPolynomial.eval q₀ Q ≠ 0 ∧
      ∀ q : α × Fin (k + 2) → K, MvPolynomial.eval q Q ≠ 0 →
        N ≤ Module.finrank K
          (Submodule.span K (PanelHingeFramework.ofNormals G ends q).toBodyHinge.rigidityRows) := by
  set F := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge with hF
  -- Some `N` panel rows at links are independent at `q₀`
  -- (`exists_independent_panelRow_subfamily_of_le_finrank`).
  obtain ⟨s, hsupp, hscard, hsindep⟩ :=
    F.exists_independent_panelRow_subfamily_of_le_finrank
      (ends := ends) (by simpa [hF] using hends) (by simpa [hF] using hne) (by simpa [hF] using hN)
  obtain ⟨Q, hQ₀, hQ⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_linearIndependent G ends hsindep
  -- At any non-root `q`, the `s`-subfamily is independent; transfer to `rank ≥ N`.
  refine ⟨Q, hQ₀, fun q hq => ?_⟩
  set F' := (PanelHingeFramework.ofNormals G ends q).toBodyHinge with hF'
  have hLI : LinearIndependent K (fun i : s => F'.panelRow ends (i : β × _ × _)) := hQ q hq
  have : Fintype s := Fintype.ofFinite s
  -- The `s`-subfamily range is contained in the rigidity rows of `F'`.
  have hsub : Submodule.span K (Set.range (fun i : s => F'.panelRow ends (i : β × _ × _)))
      ≤ Submodule.span K F'.rigidityRows := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨⟨e', t₁, t₂⟩, hi⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨e', (ends e').1, (ends e').2, hsupp (e', t₁, t₂) hi,
      annihRow (F'.supportExtensor e') t₁ t₂, ?_, rfl⟩
    rw [BodyHingeFramework.hingeRowBlock_apply, Submodule.mem_dualAnnihilator]
    intro x hx
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨r, rfl⟩ := hx
    rw [map_smul, annihRow_apply_self, smul_zero]
  -- `N = Nat.card s = Fintype.card s = finrank (span subfam) ≤ finrank (span rigidityRows)`.
  calc N = Nat.card s := hscard.symm
    _ = Fintype.card s := Nat.card_eq_fintype_card
    _ = Module.finrank K
          (Submodule.span K (Set.range (fun i : s => F'.panelRow ends (i : β × _ × _)))) :=
        (finrank_span_eq_card hLI).symm
    _ ≤ Module.finrank K (Submodule.span K F'.rigidityRows) := Submodule.finrank_mono hsub

/-- **A framework rigid on a set `s` gives a rank polynomial, at links** (a step of
`lem:case-I-realization`): `exists_rankPolynomial_of_rigidOn_linking` with rigidity on a nonempty
set `s` in place of `V(G)`, and at least `D(|s| − 1)` rows
(`exists_independent_panelRow_subfamily_of_rigidOn_linking_set`). The proof of KT Lemma 6.3 (p. 674)
applies it to `H` at `s = V(H)`
(`hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set_kdof`, in `CaseI.lean`). -/
theorem PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking_set [Finite α] [Finite β]
    (G : Graph α β) (ends : β → α × α) {s : Set α}
    (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2)
    {q₀ : α × Fin (k + 2) → K}
    (hne : ∀ e, G.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.supportExtensor e ≠ 0)
    (hnes : s.Nonempty)
    (hrig : (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.IsInfinitesimallyRigidOn s) :
    ∃ (t : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k))
      (Q : MvPolynomial (α × Fin (k + 2)) K),
      (∀ i ∈ t, G.IsLink (i : β × _ × _).1 (ends (i : β × _ × _).1).1
        (ends (i : β × _ × _).1).2) ∧
      screwDim k * (s.ncard - 1) ≤ Nat.card t ∧ MvPolynomial.eval q₀ Q ≠ 0 ∧
      ∀ q : α × Fin (k + 2) → K, MvPolynomial.eval q Q ≠ 0 →
        LinearIndependent K
          (fun i : t => (PanelHingeFramework.ofNormals G ends q).toBodyHinge.panelRow ends i) := by
  set F := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge with hF
  -- At least `D(|s|−1)` panel rows at links of `G` are independent at `q₀`.
  obtain ⟨t, hsupp, hscard, hsindep⟩ :=
    F.exists_independent_panelRow_subfamily_of_rigidOn_linking_set
      (ends := ends) (s := s) (by simpa [hF] using hends) (by simpa [hF] using hne)
      hnes (by simpa [hF] using hrig)
  obtain ⟨Q, hQ₀, hQ⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_linearIndependent G ends hsindep
  exact ⟨t, Q, hsupp, hscard, hQ₀, hQ⟩

/-! ## Nondegenerate hinges from a generic realization (`lem:generic-yields-genuine-hinge`) -/

/-- **A generic full-rank realization has nondegenerate hinges**
(`lem:generic-yields-genuine-hinge`): for `k ≥ 1` (`[NeZero k]`), a loopless multigraph `G` with
`|V(G)| ≥ 2` that has a generic full-rank realization `Q` has a nondegenerate-hinge panel
realization (`HasPanelRealization`, `def:genuine-hinge-realization`), the body-hinge framework of
`Q` with its normals:

* each normal is nonzero, as general position at `v` and another body `w ∈ V(G)` makes `Q.normal v`
  and `Q.normal w` linearly independent;
* the hinge at each link is nonzero: `Q.ends` gives the link its ends (the last conjunct of
  `HasGenericFullRankRealization`), which differ as `G` has no loops (`IsLink.ne`), and general
  position gives `supportExtensor_ne_zero_of_isGeneralPosition`;
* the hinge lies in the panels of both ends: it is the join of a basis of the meet of the two
  hyperplanes (`exists_extensor_eq_panelSupportExtensor_gen`, `lem:panel-support-extensor-join`),
  which needs `k ≥ 1`;
* the rank is the same conjunct of both predicates.

The theorems that use it, in `Theorem55.lean`, apply it to simple graphs. -/
theorem hasPanelRealization_of_generic [NeZero k] {n : ℕ} {G : Graph α β} [G.Loopless] [Finite α]
    (hV : 2 ≤ V(G).ncard)
    (h : PanelHingeFramework.HasGenericFullRankRealization K k n G) :
    HasPanelRealization K k n G := by
  obtain ⟨Q, hQg, hQgp, hQrank, hQrec⟩ := h
  have hne : V(G).Nonempty := (Set.ncard_pos (Set.toFinite _)).mp (by omega)
  refine ⟨Q.toBodyHinge, Q.normal, ?_, ?_, ?_, ?_⟩
  · -- F.graph = G
    rw [PanelHingeFramework.toBodyHinge_graph]; exact hQg
  · -- ∀ v ∈ V(G), Q.normal v ≠ 0
    intro v _hv
    obtain ⟨w, _hwV, hwne⟩ := Set.exists_ne_of_one_lt_ncard (show 1 < V(G).ncard by omega) v
    have hli := hQgp v w hwne.symm
    intro heq
    exact hli.ne_zero 0 (by simp [Matrix.cons_val_zero, heq])
  · -- ∀ e u v, G.IsLink e u v → (supportExtensor e ≠ 0) ∧ ExtensorInPanel ... u ∧ ... v
    intro e u v he
    have hends := hQrec e u v he
    -- (Q.ends e).1 ≠ (Q.ends e).2 via link-recording + IsLink.ne.
    have hends_ne : (Q.ends e).1 ≠ (Q.ends e).2 := by
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> [rw [h1, h2]; rw [h1, h2]] <;>
        [exact he.ne; exact he.ne.symm]
    refine ⟨PanelHingeFramework.supportExtensor_ne_zero_of_isGeneralPosition Q hQgp hends_ne, ?_⟩
    -- The panels: `exists_extensor_eq_panelSupportExtensor_gen` at the selected order of the ends.
    -- One `?_` for the conjunction `ExtensorInPanel ... u ∧ ExtensorInPanel ... v`.
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · -- Case: (Q.ends e).1 = u, (Q.ends e).2 = v
      -- supportExtensor e = panelSupportExtensor (Q.normal u) (Q.normal v)
      have hsupp : Q.toBodyHinge.supportExtensor e =
          panelSupportExtensor (Q.normal u) (Q.normal v) := by
        rw [PanelHingeFramework.toBodyHinge_supportExtensor, h1, h2]
      obtain ⟨p, hp, hperp⟩ := exists_extensor_eq_panelSupportExtensor_gen (hQgp u v he.ne)
      have hval : (Q.toBodyHinge.supportExtensor e).val = extensor p :=
        congr_arg ScrewSpace.val hsupp ▸ hp
      exact ⟨⟨p, hval, fun i => (hperp i).1⟩, ⟨p, hval, fun i => (hperp i).2⟩⟩
    · -- Case: (Q.ends e).1 = v, (Q.ends e).2 = u
      -- supportExtensor e = panelSupportExtensor (Q.normal v) (Q.normal u)
      have hsupp : Q.toBodyHinge.supportExtensor e =
          panelSupportExtensor (Q.normal v) (Q.normal u) := by
        rw [PanelHingeFramework.toBodyHinge_supportExtensor, h1, h2]
      obtain ⟨p, hp, hperp⟩ := exists_extensor_eq_panelSupportExtensor_gen (hQgp v u he.ne.symm)
      have hval : (Q.toBodyHinge.supportExtensor e).val = extensor p :=
        congr_arg ScrewSpace.val hsupp ▸ hp
      exact ⟨⟨p, hval, fun i => (hperp i).2⟩, ⟨p, hval, fun i => (hperp i).1⟩⟩
  · -- Rank: direct from hQrank.
    exact hQrank

end CombinatorialRigidity.Molecular
