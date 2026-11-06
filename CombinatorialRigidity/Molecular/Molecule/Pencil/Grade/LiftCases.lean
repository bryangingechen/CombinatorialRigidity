/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.LiftSmall
public import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.Ear
public import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.GenericSteer

/-!
# The pendant, the ear and the pendant triangle

The nodes `lem:pencil-d-lift-pendant`, `lem:pencil-d-lift-ear` and
`lem:pencil-d-lift-pendant-triangle` of `blueprint/src/chapter/pencil-d.tex`,
`sec:pencil-d-generic`: three cases of the induction on the bodies. Each is the lift step across a
deleted body or two: (T1) a nondegenerate realization of `H` extends (the steer lemma gives a
realization of `G` restricting to one of `H`; the polynomial `E` is a product of minors of the
closed hub-neighbourhoods in `G`, and at the ear one of `b_a · n_b`, `b_b · n_a`), (T2) the lift
maps extend (`lift_transfer`), and the rank is the transferred one plus the deleted bodies'.

* `liftAttains_of_pendant`: a body of degree one; the cut is its edge, the rank adds `D - 1`
  (`pendant_rank`).
* `liftAttains_of_ear`: a body `x` of degree two with hub neighbours `a ≠ b`, under the new
  predicate `EarLiftCondition` (the lifts of `G - x` agree at `x`: `ζ_x = φ_a(b⁰_x) = φ_b(b⁰_x)`);
  the rank by `lem:block-rank-ear`.
* `liftAttains_of_pendantTriangle`: adjacent bodies of degree two joined to a body of degree at
  least four; their lifts are read off that of `c`, and the triangle is rigid of rank `2D`.
-/

@[expose] public section

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

/-! ## Shared steps -/

/-- A nondegenerate realization in the polarity form is one with normals `point` and subspaces
`normal^⊥`. -/
theorem IsNondegPencilRealization.toPlane {G : Graph α β} {F : BodyHingeFramework K 2 α β}
    {normal point : α → Fin 4 → K} (hnd : IsNondegPencilRealization G F normal point) :
    IsNondegPencilPlaneRealization G (F.mapExtensor screwComplementIso) point
      (fun v => dotPerp (K ∙ normal v)) :=
  ⟨hasPencilPlaneRealization_mapExtensor_screwComplementIso hnd.1,
    (pencilNondegConditions_dotPerp_iff hnd.1.1.2.1).2 hnd.2⟩

/-- A property true at every point of `U(G)`, nonempty, holds generally. -/
theorem HoldsGenerally.of_forall {G : Graph α β} {hubSel nbrSel : α → Fin 3 → Option α}
    {p : (α → Fin 4 → K) → (α → Submodule K (Fin 4 → K)) → Prop}
    (hne : (steerSet (K := K) G hubSel nbrSel).Nonempty)
    (h : ∀ s ∈ steerSet (K := K) G hubSel nbrSel,
      p (steerPoint hubSel s) (fun v => dotPerp (K ∙ steerNormal hubSel nbrSel G s v))) :
    HoldsGenerally G hubSel nbrSel p :=
  ⟨1, ⟨hne.some, hne.some_mem, by simp⟩, fun s hs _ => h s hs⟩

theorem HoldsGenerally.mono {G : Graph α β} {hubSel nbrSel : α → Fin 3 → Option α}
    {p q : (α → Fin 4 → K) → (α → Submodule K (Fin 4 → K)) → Prop}
    (h : HoldsGenerally G hubSel nbrSel p)
    (hpq : ∀ s ∈ steerSet (K := K) G hubSel nbrSel,
      p (steerPoint hubSel s) (fun v => dotPerp (K ∙ steerNormal hubSel nbrSel G s v)) →
      q (steerPoint hubSel s) (fun v => dotPerp (K ∙ steerNormal hubSel nbrSel G s v))) :
    HoldsGenerally G hubSel nbrSel q := by
  obtain ⟨R, hR0, hR⟩ := h
  exact ⟨R, hR0, fun s hs hRs => hpq s hs (hR s hs hRs)⟩


/-- **The variables of a polynomial homogeneous in each block** lie in the blocks of its degree. -/
theorem mem_support_of_mem_vars_of_isWeightedHomogeneous {σ ι : Type*} (g : σ → ι)
    {φ : MvPolynomial σ K} {d : ι →₀ ℕ}
    (h : MvPolynomial.IsWeightedHomogeneous (fun p => Finsupp.single (g p) 1) φ d) {p : σ}
    (hp : p ∈ φ.vars) : g p ∈ d.support := by
  classical
  obtain ⟨m, hm, hmp⟩ := (MvPolynomial.mem_vars_iff_mem_support p).1 hp
  have hw := h (MvPolynomial.mem_support_iff.1 hm)
  rw [Finsupp.mem_support_iff, ← hw, Finsupp.weight_apply, Finsupp.sum, Finsupp.finsetSum_apply]
  refine ne_of_gt (lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun q =>
    (m q • Finsupp.single (g q) 1 : ι →₀ ℕ) (g p)) (fun _ _ => Nat.zero_le _) hmp))
  simp only [Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_eq_same]
  exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hmp)

/-- **A minor certifying an independence** (the `E` of the cases' (T1)): if the vectors of block
`j` at the bodies of `S` are linearly independent at `x₀`, a minor of them is a polynomial
homogeneous in each block, with its variables in `S`, nonzero at `x₀`, whose non-roots keep them
independent. -/
theorem exists_minorPoly [Finite α] (S : Set α) (j : Fin 2) {x₀ : α × Fin 2 × Fin 4 → K}
    (h : LinearIndepOn K (fun w i => x₀ (w, j, i)) S) :
    ∃ E : MvPolynomial (α × Fin 2 × Fin 4) K, (∀ p ∈ E.vars, p.1 ∈ S) ∧
      (∃ d : α × Fin 2 →₀ ℕ, MvPolynomial.IsWeightedHomogeneous
        (fun p : α × Fin 2 × Fin 4 => Finsupp.single (p.1, p.2.1) 1) E d) ∧
      MvPolynomial.eval x₀ E ≠ 0 ∧
      ∀ x, MvPolynomial.eval x E ≠ 0 → LinearIndepOn K (fun w i => x (w, j, i)) S := by
  classical
  have : Fintype S := Fintype.ofFinite S
  let P : Matrix S (Fin 4) (MvPolynomial (α × Fin 2 × Fin 4) K) :=
    Matrix.of fun w i => MvPolynomial.X ((w : α), j, i)
  have hrow : ∀ x : α × Fin 2 × Fin 4 → K,
      (P.map (MvPolynomial.eval x)).row = fun w : S => fun i => x ((w : α), j, i) := by
    intro x; funext w i; simp [P, Matrix.row]
  obtain ⟨e, he⟩ := Matrix.exists_submatrix_det_ne_zero_of_linearIndependent_rows
    (M := P.map (MvPolynomial.eval x₀)) (by rw [hrow]; exact h)
  have heval : ∀ x : α × Fin 2 × Fin 4 → K,
      MvPolynomial.eval x (Matrix.of (fun w w' : S => P w (e w'))).det
        = (Matrix.of (fun w w' : S => (P.map (MvPolynomial.eval x)) w (e w'))).det := by
    intro x; rw [(MvPolynomial.eval x).map_det]; rfl
  have hhom : MvPolynomial.IsWeightedHomogeneous
      (fun p : α × Fin 2 × Fin 4 => Finsupp.single (p.1, p.2.1) 1)
      (Matrix.of (fun w w' : S => P w (e w'))).det (∑ w : S, Finsupp.single ((w : α), j) 1) := by
    rw [Matrix.det_apply']
    refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun σ _ => ?_
    have := (MvPolynomial.isWeightedHomogeneous_C
      (w := fun p : α × Fin 2 × Fin 4 => Finsupp.single (p.1, p.2.1) 1)
      (↑↑(Equiv.Perm.sign σ) : K)).mul (MvPolynomial.IsWeightedHomogeneous.prod Finset.univ
        (fun w : S => Matrix.of (fun w w' : S => P w (e w')) (σ w) w)
        (fun w : S => Finsupp.single (((σ w : S) : α), j) 1) fun w _ =>
          MvPolynomial.isWeightedHomogeneous_X K _ _)
    rw [zero_add, Equiv.sum_comp σ (fun w : S => Finsupp.single ((w : α), j) 1)] at this
    convert this using 1
    simp
  refine ⟨_, fun p hp => ?_, ⟨_, hhom⟩, by rw [heval]; exact he, fun x hx => ?_⟩
  · have := mem_support_of_mem_vars_of_isWeightedHomogeneous
      (fun p : α × Fin 2 × Fin 4 => (p.1, p.2.1)) hhom hp
    rw [Finsupp.mem_support_iff, Finsupp.finsetSum_apply] at this
    obtain ⟨w, -, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero this
    rw [Finsupp.single_apply] at hw
    split_ifs at hw with hpw
    · rw [← (Prod.mk.inj hpw).1]; exact w.2
    · exact absurd rfl hw
  · have := Matrix.linearIndependent_rows_of_specialized_submatrix_det_ne_zero
      (P.map (MvPolynomial.eval x)).row (RingHom.id K) e (by
        rw [RingHom.id_apply]
        change (Matrix.of fun w w' => (P.map (MvPolynomial.eval x)) w (e w')).det ≠ 0
        rw [← heval]; exact hx)
    rw [hrow] at this
    exact this

/-- A vector outside a subspace of smaller dimension. -/
theorem exists_mem_notMem_of_finrank_lt {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {p q : Submodule K V} (h : Module.finrank K p < Module.finrank K q) :
    ∃ x ∈ q, x ∉ p := by
  by_contra hcon
  push Not at hcon
  exact absurd (Submodule.finrank_mono (show q ≤ p from hcon)) (by omega)

/-- A nonzero vector orthogonal to three given ones. -/
theorem exists_ne_zero_orth_three (x y z : Fin 4 → K) :
    ∃ t : Fin 4 → K, t ≠ 0 ∧ x ⬝ᵥ t = 0 ∧ y ⬝ᵥ t = 0 ∧ z ⬝ᵥ t = 0 := by
  obtain ⟨t, ht0, ht⟩ := exists_ne_zero_dotProduct_eq_zero (K := K) (d := 3) (m := 3)
    (by norm_num) ![x, y, z]
  exact ⟨t, ht0, by simpa [dotProduct_comm] using ht 0, by simpa [dotProduct_comm] using ht 1,
    by simpa [dotProduct_comm] using ht 2⟩

/-- The orthogonality of a realization with subspaces `n^⊥`. -/
theorem IsNondegPencilPlaneRealization.dotProduct_eq_zero {G : Graph α β}
    {F : BodyHingeFramework K 2 α β} {b n : α → Fin 4 → K}
    (hnd : IsNondegPencilPlaneRealization G F b (fun v => dotPerp (K ∙ n v))) :
    ∀ v ∈ V(G), ∀ w ∈ G.closedNbhd v, b w ⬝ᵥ n v = 0 := fun _ hv _ hw =>
  mem_dotPerp_span_singleton.1 (hnd.1.normal_mem_plane_of_mem_closedNbhd hv hw)

omit [Field K] in
theorem bnPoint_one (b n : α → Fin 4 → K) : (fun w i => bnPoint b n (w, 1, i)) = n := rfl


/-! ## `lem:pencil-d-lift-pendant` -/

section Pendant

variable {G : Graph α β} {v u : α}

/-- At a pendant body `v` with neighbour `u`, the closed neighbourhood of a body other than `u` and
`v` misses `v`. -/
theorem pendant_notMem_closedNbhd (hNv : ∀ y, G.Adj v y → y = u) {y : α} (hyv : y ≠ v)
    (hyu : y ≠ u) : v ∉ G.closedNbhd y := by
  rintro (h | ⟨e, he⟩)
  · exact hyv h.symm
  · exact hyu (hNv y ⟨e, he.symm⟩)

theorem closedNbhd_induce_sdiff_singleton {y : α} (hy : y ∈ V(G)) (hyv : y ≠ v) :
    (G.induce (V(G) \ {v})).closedNbhd y = G.closedNbhd y \ {v} := by
  ext z
  simp only [Graph.closedNbhd, Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff,
    Graph.induce_isLink]
  constructor
  · rintro (rfl | ⟨e, he, -, hz⟩)
    · exact ⟨Or.inl rfl, hyv⟩
    · exact ⟨Or.inr ⟨e, he⟩, hz.2⟩
  · rintro ⟨rfl | ⟨e, he⟩, hzv⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨e, he, ⟨hy, hyv⟩, he.right_mem, hzv⟩

/-- **(T1) at a pendant body** (of `liftAttains_of_pendant`): a nondegenerate realization of
`H = G - v` whose vectors are independent on the closed hub-neighbourhoods in `G` extends. -/
theorem pendant_T1 [Finite α] [Finite β] (hS : G.Simple) (hNv : ∀ y, G.Adj v y → y = u)
    (hvu : G.Adj v u)
    {F : BodyHingeFramework K 2 α β} {b n : α → Fin 4 → K}
    (hnd : IsNondegPencilPlaneRealization (G.induce (V(G) \ {v})) F b
      (fun y => dotPerp (K ∙ n y)))
    (hhub : ∀ y, LinearIndepOn K n (G.closedHubNbhd y)) :
    ∃ (F' : BodyHingeFramework K 2 α β) (b' : α → Fin 4 → K) (P' : α → Submodule K (Fin 4 → K)),
      IsNondegPencilPlaneRealization G F' b' P' ∧ (∀ y ∈ V(G) \ {v}, b' y = b y) ∧
      ∀ y ∈ V(G) \ {v}, 2 ≤ (G.induce (V(G) \ {v})).degree y → P' y = dotPerp (K ∙ n y) := by
  classical
  have := hS
  set H := G.induce (V(G) \ {v}) with hH
  have huv : u ≠ v := hvu.ne.symm
  have hu : u ∈ V(H) := ⟨hvu.right_mem, huv⟩
  obtain ⟨hb0, hn0, hlink, -, hnhub⟩ := (exists_isNondeg_dotPerp_iff hnd.dotProduct_eq_zero).1
    ⟨F, hnd⟩
  have horth := hnd.dotProduct_eq_zero
  have hvhub : ¬ G.PencilHub v := fun h => by
    have := h.2
    have : G.degree v ≤ 1 := by
      rw [Graph.degree_eq_ncard_adj]
      calc N(G, v).ncard ≤ ({u} : Set α).ncard :=
            Set.ncard_le_ncard (fun y hy => hNv y hy) (Set.toFinite _)
        _ = 1 := Set.ncard_singleton u
    omega
  have hhubV : ∀ y, ∀ z ∈ G.closedHubNbhd y, z ≠ v := fun y z hz hzv => hvhub (hzv ▸ hz.1)
  -- the bodies of `H` other than `u` keep their closed neighbourhoods
  have hcl : ∀ y ∈ V(H), y ≠ u → G.closedNbhd y = H.closedNbhd y := by
    intro y hy hyu
    rw [closedNbhd_induce_sdiff_singleton hy.1 hy.2, Set.sdiff_singleton_eq_self
      (pendant_notMem_closedNbhd hNv hy.2 hyu)]
  have hclu : G.closedNbhd u = insert v (H.closedNbhd u) := by
    rw [closedNbhd_induce_sdiff_singleton hu.1 huv, Set.insert_sdiff_singleton,
      Set.insert_eq_of_mem (Or.inr (let ⟨e, he⟩ := hvu; ⟨e, he.symm⟩))]
  have hclv : G.closedNbhd v = {v, u} := by
    ext z
    refine ⟨?_, ?_⟩
    · rintro (rfl | ⟨e, he⟩)
      · exact Or.inl rfl
      · exact Or.inr (hNv z ⟨e, he⟩)
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr (let ⟨e, he⟩ := hvu; ⟨e, he⟩)
  have hdegH : ∀ y ∈ V(H), y ≠ u → H.degree y = G.degree y := by
    intro y hy hyu
    rw [Graph.degree_eq_ncard_adj, Graph.degree_eq_ncard_adj]
    congr 1
    ext z
    refine ⟨fun ⟨e, he⟩ => ⟨e, he.1⟩, fun ⟨e, he⟩ => ⟨e, he, hy, he.right_mem, ?_⟩⟩
    rintro rfl
    exact hyu (hNv y ⟨e, he.symm⟩)
  -- the two cases: `u` a hub of `G`, or of degree two
  by_cases hhu : G.PencilHub u
  · -- `b'_v ∈ n_u^⊥` off `K b_u`, and `n'_v` orthogonal to both
    obtain ⟨p, hp, hpu⟩ := exists_mem_notMem_of_finrank_lt (p := K ∙ b u)
      (q := dotPerp (K ∙ n u)) (by
        rw [finrank_dotPerp_span_singleton_of_ne_zero (hn0 u hu)]
        exact lt_of_le_of_lt (by simpa using finrank_span_le_card ({b u} : Set (Fin 4 → K)))
          (by norm_num))
    obtain ⟨t, ht0, htu, htp, -⟩ := exists_ne_zero_orth_three (b u) p 0
    set b' := Function.update b v p
    set n' := Function.update n v t
    have hpi : LinearIndependent K ![b u, p] := (LinearIndependent.pair_iff' (hb0 u hu)).2
      fun a ha => hpu (ha ▸ Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
    have hp0 : p ≠ 0 := fun h => hpu (h ▸ Submodule.zero_mem _)
    have hb'v : b' v = p := Function.update_self _ _ _
    have hn'v : n' v = t := Function.update_self _ _ _
    have hb' : ∀ y, y ≠ v → b' y = b y := fun y hy => Function.update_of_ne hy _ _
    have hn' : ∀ y, y ≠ v → n' y = n y := fun y hy => Function.update_of_ne hy _ _
    have hHv : ∀ y ∈ V(H), ∀ z ∈ H.closedNbhd y, z ≠ v := fun y hy z hz =>
      (Graph.closedNbhd_subset_vertexSet hy hz).2
    have horth' : ∀ y ∈ V(G), ∀ z ∈ G.closedNbhd y, b' z ⬝ᵥ n' y = 0 := by
      intro y hy z hz
      by_cases hyv : y = v
      · subst hyv
        rw [hclv] at hz
        rcases hz with rfl | rfl
        · rw [hb'v, hn'v, ← htp, dotProduct_comm]
        · rw [hb' z huv, hn'v, ← htu, dotProduct_comm]
      rw [hn' y hyv]
      by_cases hyu : y = u
      · subst hyu
        rw [hclu] at hz
        rcases hz with rfl | hz
        · rw [hb'v]; exact mem_dotPerp_span_singleton.1 hp
        · rw [hb' z (hHv y hu z hz)]; exact horth y hu z hz
      · rw [hcl y ⟨hy, hyv⟩ hyu] at hz
        rw [hb' z (hHv y ⟨hy, hyv⟩ z hz)]
        exact horth y ⟨hy, hyv⟩ z hz
    obtain ⟨F', hF'⟩ := (exists_isNondeg_dotPerp_iff horth').2 ⟨fun y hy => by
        by_cases hyv : y = v
        · rw [hyv, hb'v]; exact hp0
        · rw [hb' y hyv]; exact hb0 y ⟨hy, hyv⟩,
      fun y hy => by
        by_cases hyv : y = v
        · rw [hyv, hn'v]; exact ht0
        · rw [hn' y hyv]; exact hn0 y ⟨hy, hyv⟩,
      fun y z hyz => by
        by_cases hyv : y = v
        · subst hyv
          rw [hNv z hyz, hb'v, hb' u huv]
          exact LinearIndependent.pair_symm_iff.1 hpi
        by_cases hzv : z = v
        · subst hzv
          rw [hNv y hyz.symm, hb'v, hb' u huv]
          exact hpi
        rw [hb' y hyv, hb' z hzv]
        obtain ⟨e, he⟩ := hyz
        exact hlink y z ⟨e, he, ⟨he.left_mem, hyv⟩, he.right_mem, hzv⟩,
      fun y _ => (hhub y).congr fun z hz => (hn' z (hhubV y z hz)).symm,
      fun y hy hyhub => by
        by_cases hyv : y = v
        · subst hyv
          rw [hclv, LinearIndepOn.pair_iff_linearIndependent huv.symm, hb'v, hb' u huv]
          exact LinearIndependent.pair_symm_iff.1 hpi
        have hyu : y ≠ u := fun h => hyhub (h ▸ hhu)
        rw [hcl y ⟨hy, hyv⟩ hyu]
        refine (hnhub y ⟨hy, hyv⟩ fun h => hyhub ⟨hy, ?_⟩).congr fun z hz =>
          (hb' z (hHv y ⟨hy, hyv⟩ z hz)).symm
        rw [← hdegH y ⟨hy, hyv⟩ hyu]; exact h.2⟩
    exact ⟨F', b', _, hF', fun y hy => hb' y hy.2, fun y hy _ => by rw [hn' y hy.2]⟩
  · -- `u` of degree at most two: `b'_v` off the span `W` of the closed neighbourhood of `u` in `H`,
    -- and `n'_u = n'_v` orthogonal to both
    have hHv : ∀ y ∈ V(H), ∀ z ∈ H.closedNbhd y, z ≠ v := fun y hy z hz =>
      (Graph.closedNbhd_subset_vertexSet hy hz).2
    have hvH : v ∉ H.closedNbhd u := fun h => hHv u hu v h rfl
    have hHcl2 : (H.closedNbhd u).ncard ≤ 2 := by
      have hcl3 := ncard_closedNbhd_le_three_of_not_pencilHub (G := G) hhu
      rw [hclu, Set.ncard_insert_of_notMem hvH] at hcl3; omega
    set W := Submodule.span K (b '' H.closedNbhd u) with hWdef
    have hW : Module.finrank K W ≤ 2 := (finrank_span_le_ncard _ (Set.toFinite _)).trans
      ((Set.ncard_image_le (Set.toFinite _)).trans hHcl2)
    obtain ⟨p, -, hpW⟩ := exists_mem_notMem_of_finrank_lt (p := W) (q := ⊤)
      (by rw [finrank_top, Module.finrank_fin_fun]; omega)
    obtain ⟨t, ht, ht0⟩ := exists_mem_notMem_of_finrank_lt (p := ⊥)
      (q := dotPerp (Submodule.span K (insert p (b '' H.closedNbhd u)))) (by
        rw [finrank_bot, finrank_dotPerp]
        have h1 := finrank_span_le_ncard (R := K) (insert p (b '' H.closedNbhd u)) (Set.toFinite _)
        have h2 := Set.ncard_insert_le p (b '' H.closedNbhd u)
        have h3 := Set.ncard_image_le (f := b) (Set.toFinite (H.closedNbhd u))
        omega)
    have ht0' : t ≠ 0 := by simpa using ht0
    have htp : p ⬝ᵥ t = 0 := by
      rw [dotProduct_comm]; exact mem_dotPerp.1 ht p (Submodule.subset_span (Set.mem_insert _ _))
    have htW : ∀ z ∈ H.closedNbhd u, b z ⬝ᵥ t = 0 := fun z hz => by
      rw [dotProduct_comm]
      exact mem_dotPerp.1 ht _ (Submodule.subset_span (Set.mem_insert_of_mem _ ⟨z, hz, rfl⟩))
    have hp0 : p ≠ 0 := fun h => hpW (h ▸ Submodule.zero_mem _)
    have huu : u ∈ H.closedNbhd u := Or.inl rfl
    have hpi : LinearIndependent K ![b u, p] := (LinearIndependent.pair_iff' (hb0 u hu)).2
      fun a ha => hpW (ha ▸ Submodule.smul_mem _ _ (Submodule.subset_span ⟨u, huu, rfl⟩))
    set b' := Function.update b v p
    set n' := Function.update (Function.update n v t) u t
    have hb'v : b' v = p := Function.update_self _ _ _
    have hn'v : n' v = t := by simp [n', Function.update_of_ne huv.symm]
    have hn'u : n' u = t := Function.update_self _ _ _
    have hb' : ∀ y, y ≠ v → b' y = b y := fun y hy => Function.update_of_ne hy _ _
    have hn' : ∀ y, y ≠ v → y ≠ u → n' y = n y := fun y hy hyu => by
      simp [n', Function.update_of_ne hy, Function.update_of_ne hyu]
    have hHhub : ¬ H.PencilHub u := fun h => hhu ⟨hu.1, by
      have h3 := h.2
      rw [Graph.degree_eq_ncard_adj] at h3 ⊢
      exact h3.trans (Set.ncard_le_ncard (fun z ⟨e, he⟩ => ⟨e, he.1⟩) (Set.toFinite _))⟩
    have hdegu : H.degree u ≤ 1 := by
      have := hS.mono (Graph.induce_le Set.sdiff_subset : H ≤ G)
      have hnot : u ∉ N(H, u) := fun h => h.ne rfl
      rw [Graph.closedNbhd_eq_insert, Set.ncard_insert_of_notMem hnot] at hHcl2
      rw [Graph.degree_eq_ncard_adj]; omega
    have horth' : ∀ y ∈ V(G), ∀ z ∈ G.closedNbhd y, b' z ⬝ᵥ n' y = 0 := by
      intro y hy z hz
      by_cases hyv : y = v
      · subst hyv
        rw [hclv] at hz
        rcases hz with rfl | rfl
        · rw [hb'v, hn'v, htp]
        · rw [hb' z huv, hn'v]; exact htW z huu
      by_cases hyu : y = u
      · subst hyu
        rw [hclu] at hz
        rcases hz with rfl | hz
        · rw [hb'v, hn'u, htp]
        · rw [hb' z (hHv y hu z hz), hn'u]; exact htW z hz
      · rw [hcl y ⟨hy, hyv⟩ hyu] at hz
        rw [hb' z (hHv y ⟨hy, hyv⟩ z hz), hn' y hyv hyu]
        exact horth y ⟨hy, hyv⟩ z hz
    obtain ⟨F', hF'⟩ := (exists_isNondeg_dotPerp_iff horth').2 ⟨fun y hy => by
        by_cases hyv : y = v
        · rw [hyv, hb'v]; exact hp0
        · rw [hb' y hyv]; exact hb0 y ⟨hy, hyv⟩,
      fun y hy => by
        by_cases hyv : y = v
        · rw [hyv, hn'v]; exact ht0'
        by_cases hyu : y = u
        · rw [hyu, hn'u]; exact ht0'
        · rw [hn' y hyv hyu]; exact hn0 y ⟨hy, hyv⟩,
      fun y z hyz => by
        by_cases hyv : y = v
        · subst hyv
          rw [hNv z hyz, hb'v, hb' u huv]
          exact LinearIndependent.pair_symm_iff.1 hpi
        by_cases hzv : z = v
        · subst hzv
          rw [hNv y hyz.symm, hb'v, hb' u huv]
          exact hpi
        rw [hb' y hyv, hb' z hzv]
        obtain ⟨e, he⟩ := hyz
        exact hlink y z ⟨e, he, ⟨he.left_mem, hyv⟩, he.right_mem, hzv⟩,
      fun y _ => (hhub y).congr fun z hz =>
        (hn' z (hhubV y z hz) fun h => hhu (h ▸ hz.1)).symm,
      fun y hy hyhub => by
        by_cases hyv : y = v
        · subst hyv
          rw [hclv, LinearIndepOn.pair_iff_linearIndependent huv.symm, hb'v, hb' u huv]
          exact LinearIndependent.pair_symm_iff.1 hpi
        by_cases hyu : y = u
        · subst hyu
          rw [hclu]
          refine LinearIndepOn.insert ((hnhub y hu hHhub).congr fun z hz =>
            (hb' z (hHv y hu z hz)).symm) ?_
          rw [hb'v, Set.image_congr (fun z hz => hb' z (hHv y hu z hz))]
          exact hpW
        rw [hcl y ⟨hy, hyv⟩ hyu]
        refine (hnhub y ⟨hy, hyv⟩ fun h => hyhub ⟨hy, ?_⟩).congr fun z hz =>
          (hb' z (hHv y ⟨hy, hyv⟩ z hz)).symm
        rw [← hdegH y ⟨hy, hyv⟩ hyu]; exact h.2⟩
    refine ⟨F', b', _, hF', fun y hy => hb' y hy.2, fun y hy h2 => ?_⟩
    have hyu : y ≠ u := fun h => by subst h; omega
    rw [hn' y hy.2 hyu]

/-- The closed neighbourhoods at a pendant body. -/
theorem pendant_closedNbhds (hS : G.Simple) (hNv : ∀ y, G.Adj v y → y = u) (hvu : G.Adj v u) :
    (∀ y ∈ V(G), y ≠ v → y ≠ u → G.closedNbhd y = (G.induce (V(G) \ {v})).closedNbhd y) ∧
    G.closedNbhd u = insert v ((G.induce (V(G) \ {v})).closedNbhd u) ∧
    G.closedNbhd v = {v, u} := by
  have := hS
  have huv : u ≠ v := hvu.ne.symm
  refine ⟨fun y hy hyv hyu => ?_, ?_, ?_⟩
  · rw [closedNbhd_induce_sdiff_singleton hy hyv, Set.sdiff_singleton_eq_self
      (pendant_notMem_closedNbhd hNv hyv hyu)]
  · rw [closedNbhd_induce_sdiff_singleton hvu.right_mem huv, Set.insert_sdiff_singleton,
      Set.insert_eq_of_mem (Or.inr (let ⟨e, he⟩ := hvu; ⟨e, he.symm⟩))]
  · ext z
    refine ⟨?_, ?_⟩
    · rintro (rfl | ⟨e, he⟩)
      · exact Or.inl rfl
      · exact Or.inr (hNv z ⟨e, he⟩)
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr (let ⟨e, he⟩ := hvu; ⟨e, he⟩)

/-- **(T2) at a pendant body** (of `liftAttains_of_pendant`): `ζ_v = ψ_u(b⁰_v)`. -/
theorem pendant_T2 (hS : G.Simple) (hNv : ∀ y, G.Adj v y → y = u) (hvu : G.Adj v u)
    {hubSel nbrSel : α → Fin 3 → Option α}
    (hHubSel : ∀ v, IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v))
    (hNbrSel : ∀ v, ¬ G.PencilHub v → IsFin3SelectorOf (G.closedNbhd v) (nbrSel v))
    (hne : (steerSet (K := K) G hubSel nbrSel).Nonempty) :
    HoldsGenerally (K := K) G hubSel nbrSel fun b0 P0 =>
      ∀ ζ ∈ liftMaps (G.induce (V(G) \ {v})) b0 P0, ∃ ζ' ∈ liftMaps G b0 P0,
        ∀ y ∈ V(G) \ {v}, ζ' y = ζ y := by
  classical
  have huv : u ≠ v := by have := hS; exact hvu.ne.symm
  obtain ⟨hcl, hclu, hclv⟩ := pendant_closedNbhds hS hNv hvu
  refine HoldsGenerally.of_forall hne fun s hs ζ hζ => ?_
  have hP0G : ∀ y ∈ V(G), ∀ z ∈ G.closedNbhd y,
      steerPoint hubSel s z ∈ dotPerp (K ∙ steerNormal hubSel nbrSel G s y) := fun y _ z hz =>
    mem_dotPerp_span_singleton.2 (steerPoint_dotProduct_steerNormal hHubSel hNbrSel s hz)
  have hP0H : ∀ y ∈ V(G.induce (V(G) \ {v})), ∀ z ∈ (G.induce (V(G) \ {v})).closedNbhd y,
      steerPoint hubSel s z ∈ dotPerp (K ∙ steerNormal hubSel nbrSel G s y) := fun y _ z hz =>
    mem_dotPerp_span_singleton.2 (steerPoint_dotProduct_steerNormal_of_le
      (Graph.induce_le Set.sdiff_subset) hHubSel hNbrSel s hz)
  rw [mem_liftMaps_iff hP0H] at hζ
  obtain ⟨ψu, hψu⟩ := hζ u ⟨hvu.right_mem, huv⟩
  refine ⟨Function.update ζ v (ψu (steerPoint hubSel s v)), (mem_liftMaps_iff hP0G).2
    fun y hy => ?_, fun y hy => Function.update_of_ne hy.2 _ _⟩
  have hHv : ∀ y' ∈ V(G.induce (V(G) \ {v})), ∀ z ∈ (G.induce (V(G) \ {v})).closedNbhd y',
      z ≠ v := fun y' hy' z hz => (Graph.closedNbhd_subset_vertexSet hy' hz).2
  have huH : u ∈ V(G.induce (V(G) \ {v})) := ⟨hvu.right_mem, huv⟩
  by_cases hyv : y = v
  · subst hyv
    refine ⟨ψu, fun z hz => ?_⟩
    rw [hclv] at hz
    rcases hz with rfl | rfl
    · rw [Function.update_self]
    · rw [Function.update_of_ne huv]; exact hψu _ (Or.inl rfl)
  by_cases hyu : y = u
  · subst hyu
    refine ⟨ψu, fun z hz => ?_⟩
    rw [hclu] at hz
    rcases hz with rfl | hz
    · rw [Function.update_self]
    · rw [Function.update_of_ne (hHv _ huH z hz)]; exact hψu z hz
  obtain ⟨ψ, hψ⟩ := hζ y ⟨hy, hyv⟩
  refine ⟨ψ, fun z hz => ?_⟩
  rw [hcl y hy hyv hyu] at hz
  rw [Function.update_of_ne (hHv _ ⟨hy, hyv⟩ z hz)]; exact hψ z hz

/-- The cut at a pendant body is its one edge, and the deficiency rises by one. -/
theorem pendant_deficiency [Finite α] [Finite β] (hS : G.Simple)
    (hNv : ∀ y, G.Adj v y → y = u) (hvu : G.Adj v u) (n : ℕ) :
    G.deficiency n = (G.induce (V(G) \ {v})).deficiency n + 1 := by
  classical
  have := hS
  have hv : v ∈ V(G) := hvu.left_mem
  obtain ⟨e₀, he₀⟩ := hvu
  have hcut : G.cutEdges (V(G) \ {v}) = {e₀} := by
    ext e
    refine ⟨?_, ?_⟩
    · rintro ⟨-, x, y, hl, hx, hy⟩
      have hyv : y = v := by
        by_contra h; exact hy ⟨hl.right_mem, h⟩
      subst hyv
      have hxu : x = u := hNv x ⟨e, hl.symm⟩
      subst hxu
      exact hl.symm.unique_edge he₀
    · rintro rfl
      exact ⟨he₀.edge_mem, u, v, he₀.symm, ⟨he₀.right_mem, he₀.adj.ne.symm⟩, fun h => h.2 rfl⟩
  have hssub : V(G) \ {v} ⊂ V(G) := Set.sdiff_singleton_ssubset.2 hv
  have h := Graph.deficiency_eq_of_cutEdges_ncard_le_one (n := n) hssub
    (by rw [hcut, Set.ncard_singleton])
  rw [hcut, Set.ncard_singleton, Set.sdiff_sdiff_cancel_left (Set.singleton_subset_iff.2 hv)] at h
  have hE : E(G.induce {v}) = ∅ := by
    ext e
    simp only [Set.mem_empty_iff_false, iff_false]
    intro he
    obtain ⟨x, y, hl⟩ := (G.induce {v}).exists_isLink_of_mem_edgeSet he
    obtain ⟨hl, rfl, rfl⟩ := hl
    exact hl.adj.ne rfl
  rw [Graph.deficiency_of_edgeSet_empty hE] at h
  simp only [Graph.vertexSet_induce, Set.ncard_singleton] at h
  push_cast at h
  linarith

/-- **The rank at a pendant body** (of `liftAttains_of_pendant`): the hinge of `uv` adds
`D - 1`, and the deficiency rises by one. -/
theorem pendant_rank [Finite α] [Finite β] (hS : G.Simple) (hNv : ∀ y, G.Adj v y → y = u)
    (hvu : G.Adj v u) {r : ℕ} {ends : β → α × α}
    (hends : Graph.RecordsLinks G ends) {b0 : α → Fin 4 → K}
    (hlink : ∀ e x y, G.IsLink e x y → LinearIndependent K ![b0 x, b0 y]) (ζ : Fin r → α → K)
    (hH : (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := r + 1 + 1)
        (G.induce (V(G) \ {v})) ends (fun p => liftNormal b0 ζ p.1 p.2)).toBodyHinge.rigidityRows)
        : ℤ) = screwDim (r + 1 + 1) * ((V(G.induce (V(G) \ {v})).ncard : ℤ) - 1) -
          (G.induce (V(G) \ {v})).deficiency (r + 1 + 2)) :
    (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := r + 1 + 1) G ends
        (fun p => liftNormal b0 ζ p.1 p.2)).toBodyHinge.rigidityRows) : ℤ)
      = screwDim (r + 1 + 1) * ((V(G).ncard : ℤ) - 1) - G.deficiency (r + 1 + 2) := by
  classical
  have := hS
  have hv : v ∈ V(G) := hvu.left_mem
  obtain ⟨e₀, he₀⟩ := hvu
  have hext : ∀ e x y, G.IsLink e x y →
      (PanelHingeFramework.ofNormals (k := r + 1 + 1) G ends
        (fun p => liftNormal b0 ζ p.1 p.2)).toBodyHinge.supportExtensor e ≠ 0 := by
    intro e x y he
    change panelSupportExtensor (liftNormal b0 ζ (ends e).1) (liftNormal b0 ζ (ends e).2) ≠ 0
    rw [panelSupportExtensor_ne_zero_iff]
    exact linearIndependent_liftNormal ζ (hlink e _ _ (hends.isLink he))
  have hadd := BodyHingeFramework.add_le_finrank_span_rigidityRows_induce_union_singleton
    (G := G) (V₁ := V(G) \ {v}) _ he₀.symm ⟨he₀.right_mem, he₀.adj.ne.symm⟩ (fun h => h.2 rfl)
    hext
  rw [Set.sdiff_union_of_subset (Set.singleton_subset_iff.2 hv), Graph.induce_vertexSet] at hadd
  have hup := finrank_liftNormal_le hends hlink ⟨v, hv⟩ ζ
  have hdef := pendant_deficiency hS hNv ⟨e₀, he₀⟩ (r + 1 + 2)
  have hcard : (V(G.induce (V(G) \ {v}))).ncard + 1 = V(G).ncard :=
    Set.ncard_sdiff_singleton_add_one hv (Set.toFinite _)
  have h1 : 1 ≤ screwDim (r + 1 + 1) := one_le_screwDim
  refine le_antisymm hup ?_
  have hadd' : ((Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals
      (k := r + 1 + 1) (G.induce (V(G) \ {v})) ends
      (fun p => liftNormal b0 ζ p.1 p.2)).toBodyHinge.rigidityRows) : ℕ) : ℤ) +
      ((screwDim (r + 1 + 1) : ℤ) - 1) ≤
      (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := r + 1 + 1) G ends
        (fun p => liftNormal b0 ζ p.1 p.2)).toBodyHinge.rigidityRows) : ℤ) := by
    have := hadd
    exact_mod_cast this
  rw [hH] at hadd'
  rw [hdef, ← hcard]
  push_cast
  linarith

/-- At a body of degree one adjacent to `u`, every neighbour is `u`. -/
theorem eq_of_adj_of_degree_eq_one (hS : G.Simple) (hv : G.degree v = 1)
    (hvu : G.Adj v u) : ∀ y, G.Adj v y → y = u := by
  have := hS
  rw [Graph.degree_eq_ncard_adj] at hv
  obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 hv
  have hu : u ∈ N(G, v) := hvu
  rw [ha] at hu
  intro y hy
  have : y ∈ N(G, v) := hy
  rw [ha] at this
  exact this.trans hu.symm

/-- The closed hub-neighbourhood of a body off `V(G)` is empty. -/
theorem closedHubNbhd_eq_empty_of_notMem {y : α} (hy : y ∉ V(G)) : G.closedHubNbhd y = ∅ := by
  ext w
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hw, rfl | ⟨e, he⟩⟩
  · exact hy hw.1
  · exact hy he.left_mem

/-- The links of an induced subgraph are recorded by any selector recording those of `G`: the form
at links of `Graph.RecordsLinks.induce`. -/
theorem induce_isLink_ends {ends : β → α × α} (hends : Graph.RecordsLinks G ends) (V' : Set α) :
    ∀ e x y, (G.induce V').IsLink e x y → (G.induce V').IsLink e (ends e).1 (ends e).2 :=
  fun _ _ _ => (hends.induce V').isLink

/-- **`lem:pencil-d-lift-pendant`.** -/
theorem liftAttains_of_pendant [Infinite K] [Finite α] [Finite β] (r : ℕ) {G : Graph α β}
    (hS : G.Simple) (hfeas : PencilNondegFeasible K G) {v u : α} (hv : G.degree v = 1)
    (hvu : G.Adj v u) :
    PencilNondegFeasible K (G.induce (V(G) \ {v})) ∧
      (LiftAttains K r (G.induce (V(G) \ {v})) → LiftAttains K r G) := by
  classical
  have := hS
  have := Fintype.ofFinite α
  have hNv := eq_of_adj_of_degree_eq_one hS hv hvu
  have huv : u ≠ v := hvu.ne.symm
  have hvhub : ¬ G.PencilHub v := fun h => by have := h.2; omega
  -- (T1)'s realization: the steer lemma, `v` being no hub
  obtain ⟨F₀, normal₀, point₀, hndG, hndH⟩ :=
    exists_isNondegPencilRealization_restrict_of_demoted hS hfeas
      (Graph.induce_le Set.sdiff_subset : G.induce (V(G) \ {v}) ≤ G) (fun y hy _ _ z hyz hnyz => by
        have hzv : z = v := by
          by_contra hzv
          obtain ⟨e, he⟩ := hyz
          exact hnyz ⟨e, he, hy, he.right_mem, hzv⟩
        exact hzv ▸ hvhub)
  refine ⟨⟨_, _, _, hndH⟩, fun hH => ?_⟩
  obtain ⟨hubSel, nbrSel, hHubSel, hNbrSel⟩ := exists_steer_selectors hfeas
  have hne : (steerSet (K := K) G hubSel nbrSel).Nonempty :=
    (steerSet_nonempty_iff hHubSel hNbrSel).2 hfeas
  have : Inhabited α := ⟨u⟩
  have hends := Graph.recordsLinks_endsOf G
  -- (T1): `E` the minors of the closed hub-neighbourhoods in `G`
  have hind₀ : ∀ y, LinearIndepOn K (fun w i => bnPoint point₀ normal₀ (w, 1, i))
      (G.closedHubNbhd y) := fun y => by
    rw [bnPoint_one]
    by_cases hy : y ∈ V(G)
    · exact hndG.2.2.1 y hy
    · rw [closedHubNbhd_eq_empty_of_notMem hy]; exact linearIndepOn_empty K _
  choose E hEvars hEhom hE0 hEind using fun y => exists_minorPoly (G.closedHubNbhd y) 1 (hind₀ y)
  choose dE hdE using hEhom
  have hT1 : ∃ E : MvPolynomial (α × Fin 2 × Fin 4) K, (∀ p ∈ E.vars, p.1 ∈ V(G) \ {v}) ∧
      (∃ d : α × Fin 2 →₀ ℕ, MvPolynomial.IsWeightedHomogeneous
        (fun p : α × Fin 2 × Fin 4 => Finsupp.single (p.1, p.2.1) 1) E d) ∧
      (∃ (F : BodyHingeFramework K 2 α β) (b n : α → Fin 4 → K),
        IsNondegPencilPlaneRealization (G.induce (V(G) \ {v})) F b (fun v => dotPerp (K ∙ n v)) ∧
        MvPolynomial.eval (bnPoint b n) E ≠ 0) ∧
      ∀ (F : BodyHingeFramework K 2 α β) (b n : α → Fin 4 → K),
        IsNondegPencilPlaneRealization (G.induce (V(G) \ {v})) F b (fun v => dotPerp (K ∙ n v)) →
        MvPolynomial.eval (bnPoint b n) E ≠ 0 →
        ∃ (F' : BodyHingeFramework K 2 α β) (b' : α → Fin 4 → K)
          (P' : α → Submodule K (Fin 4 → K)), IsNondegPencilPlaneRealization G F' b' P' ∧
          (∀ v' ∈ V(G) \ {v}, b' v' = b v') ∧ ∀ v' ∈ V(G) \ {v},
            2 ≤ (G.induce (V(G) \ {v})).degree v' → P' v' = dotPerp (K ∙ n v') := by
    refine ⟨∏ y, E y, fun p hp => ?_, ⟨∑ y, dE y,
      MvPolynomial.IsWeightedHomogeneous.prod _ _ _ fun y _ => hdE y⟩,
      ⟨_, point₀, normal₀, hndH.toPlane, ?_⟩, fun F b n hnd hE => pendant_T1 hS hNv hvu hnd
        fun y => ?_⟩
    · obtain ⟨y, -, hy⟩ := Finset.mem_biUnion.1 (MvPolynomial.vars_prod _ hp)
      have hmem := hEvars y p hy
      exact ⟨hmem.1.1, fun h => hvhub (h ▸ hmem.1)⟩
    · rw [map_prod]; exact Finset.prod_ne_zero_iff.2 fun y _ => hE0 y
    · rw [map_prod] at hE
      have := hEind y (bnPoint b n) (Finset.prod_ne_zero_iff.1 hE y (Finset.mem_univ _))
      rwa [bnPoint_one] at this
  have htr := lift_transfer (K := K) (r := r) (V' := V(G) \ {v}) Set.sdiff_subset
    ⟨u, hvu.right_mem, huv⟩ hHubSel hNbrSel (hends.induce _) hT1
    (pendant_T2 hS hNv hvu hHubSel hNbrSel hne) hH
  refine liftAttains_of_holdsGenerally hHubSel hNbrSel hends (htr.mono fun s hs h => ?_)
  obtain ⟨-, ⟨lam, hlam, hrk⟩, -⟩ := h
  refine ⟨lam, hlam, pendant_rank hS hNv hvu hends (fun e x y he => ?_) _ hrk⟩
  exact ((mem_steerSet_iff hHubSel hNbrSel).1 hs).2.2.1 x y ⟨e, he⟩

end Pendant

/-! ## `lem:pencil-d-lift-ear` -/

/-- **The ear's condition** (`lem:pencil-d-lift-ear`'s hypothesis, `lem:pencil-d-ear-free`'s
consequence). -/
def EarLiftCondition (G : Graph α β) (hubSel nbrSel : α → Fin 3 → Option α) (x a b : α) : Prop :=
  HoldsGenerally (K := K) G hubSel nbrSel fun b0 P0 =>
    ∀ lam ∈ liftSpace (G.induce (V(G) \ {x})) b0 P0, ∀ (ha : b0 x ∈ P0 a) (hb : b0 x ∈ P0 b),
      lam.2 a ⟨b0 x, ha⟩ = lam.2 b ⟨b0 x, hb⟩

section Ear

variable {G : Graph α β} {x a b : α}

/-- The joins of `p ∨ q` and `q ∨ w` at three independent vectors are independent. -/
theorem linearIndependent_normalsJoin_pair {k : ℕ} {p q w : Fin (k + 2) → K}
    (h : LinearIndependent K ![p, q, w]) :
    LinearIndependent K ![normalsJoin p q, normalsJoin q w] := by
  obtain ⟨f₁, h₁p, h₁q, h₁w⟩ := exists_dual_three h 1 0 0
  obtain ⟨f₂, h₂p, h₂q, h₂w⟩ := exists_dual_three h 0 1 0
  obtain ⟨f₃, h₃p, h₃q, h₃w⟩ := exists_dual_three h 0 0 1
  obtain ⟨φ₁₂, hφ₁₂⟩ := exists_linearMap_normalsJoin_eq f₁ f₂
  obtain ⟨φ₂₃, hφ₂₃⟩ := exists_linearMap_normalsJoin_eq f₂ f₃
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have e₁ := congrArg φ₁₂ hst
  have e₂ := congrArg φ₂₃ hst
  simp only [map_add, map_smul, map_zero, hφ₁₂, hφ₂₃, h₁p, h₁q, h₁w, h₂p, h₂q, h₂w, h₃p, h₃q, h₃w,
    smul_eq_mul] at e₁ e₂
  constructor
  · linear_combination e₁
  · linear_combination e₂


/-- **(T2) at the ear** (of `liftAttains_of_ear`): `ζ_x = φ_a(b⁰_x) = φ_b(b⁰_x)`, by the ear's
condition. -/
theorem ear_T2 (hS : G.Simple) (hNx : ∀ y, G.Adj x y → y = a ∨ y = b)
    (hxa : G.Adj x a) (hxb : G.Adj x b) (hab : a ≠ b) (hxhub : ¬ G.PencilHub x)
    {hubSel nbrSel : α → Fin 3 → Option α}
    (hHubSel : ∀ v, IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v))
    (hNbrSel : ∀ v, ¬ G.PencilHub v → IsFin3SelectorOf (G.closedNbhd v) (nbrSel v))
    (hcond : EarLiftCondition (K := K) G hubSel nbrSel x a b) :
    HoldsGenerally (K := K) G hubSel nbrSel fun b0 P0 =>
      ∀ ζ ∈ liftMaps (G.induce (V(G) \ {x})) b0 P0, ∃ ζ' ∈ liftMaps G b0 P0,
        ∀ y ∈ V(G) \ {x}, ζ' y = ζ y := by
  classical
  have := hS
  have hax : a ≠ x := hxa.ne.symm
  have hbx : b ≠ x := hxb.ne.symm
  refine hcond.mono fun s hs hc ζ hζ => ?_
  set b0 := steerPoint hubSel s with hb0
  set P0 : α → Submodule K (Fin 4 → K) := fun v => dotPerp (K ∙ steerNormal hubSel nbrSel G s v)
  have hP0G : ∀ y ∈ V(G), ∀ z ∈ G.closedNbhd y, b0 z ∈ P0 y := fun y _ z hz =>
    mem_dotPerp_span_singleton.2 (steerPoint_dotProduct_steerNormal hHubSel hNbrSel s hz)
  have hxa' : b0 x ∈ P0 a := hP0G a hxa.right_mem x (Or.inr (let ⟨e, he⟩ := hxa; ⟨e, he.symm⟩))
  have hxb' : b0 x ∈ P0 b := hP0G b hxb.right_mem x (Or.inr (let ⟨e, he⟩ := hxb; ⟨e, he.symm⟩))
  obtain ⟨lam, hlam, rfl⟩ := Submodule.mem_map.1 hζ
  refine ⟨Function.update lam.1 x (lam.2 a ⟨b0 x, hxa'⟩), (mem_liftMaps_iff hP0G).2
    fun y hy => ?_, fun y hy => Function.update_of_ne hy.2 _ _⟩
  by_cases hyx : y = x
  · subst hyx
    have hcl : G.closedNbhd y = {y, a, b} := by
      ext z
      refine ⟨?_, ?_⟩
      · rintro (rfl | ⟨e, he⟩)
        · exact Or.inl rfl
        · rcases hNx z ⟨e, he⟩ with rfl | rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)
      · rintro (rfl | rfl | rfl)
        · exact Or.inl rfl
        · exact Or.inr (let ⟨e, he⟩ := hxa; ⟨e, he⟩)
        · exact Or.inr (let ⟨e, he⟩ := hxb; ⟨e, he⟩)
    have hli := ((mem_steerSet_iff hHubSel hNbrSel).1 hs).2.2.2.2 y hy hxhub
    rw [hcl] at hli
    obtain ⟨ψ, hψa, hψx, hψb⟩ := exists_dual_three (LinearIndepOn.triple hli
      (Or.inr (Or.inl rfl)) (Or.inl rfl) (Or.inr (Or.inr rfl)) hax hbx.symm hab) (lam.1 a)
      (lam.2 a ⟨b0 y, hxa'⟩) (lam.1 b)
    refine ⟨ψ, fun z hz => ?_⟩
    rw [hcl] at hz
    rcases hz with rfl | rfl | rfl
    · rw [Function.update_self, hψx]
    · rw [Function.update_of_ne hax, hψa]
    · rw [Function.update_of_ne hbx, hψb]
  · obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend (lam.2 y)
    have hψ' : ∀ z (hz : b0 z ∈ P0 y), ψ (b0 z) = lam.2 y ⟨b0 z, hz⟩ := fun z hz => by
      rw [← hψ]; rfl
    refine ⟨ψ, fun z hz => ?_⟩
    by_cases hzx : z = x
    · subst hzx
      rw [Function.update_self, hψ' z (hP0G y hy z hz)]
      have hy' : y = a ∨ y = b := by
        rcases hz with h | ⟨e, he⟩
        · exact absurd h.symm hyx
        · exact hNx y ⟨e, he.symm⟩
      rcases hy' with rfl | rfl
      · rfl
      · exact hc lam hlam hxa' _
    · rw [Function.update_of_ne hzx, hψ' z (hP0G y hy z hz)]
      refine hlam y ⟨hy, hyx⟩ z ?_ _
      rw [closedNbhd_induce_sdiff_singleton hy hyx]
      exact ⟨hz, hzx⟩

/-- The hinges at the two edges of the ear are independent. -/
theorem ear_hinges_linearIndependent {k : ℕ} {ends : β → α × α}
    (hends : Graph.RecordsLinks G ends) {e₀ e₁ : β}
    (he₀ : G.IsLink e₀ a x) (he₁ : G.IsLink e₁ x b) {nv : α → Fin (k + 2) → K}
    (hli : LinearIndependent K ![nv a, nv x, nv b]) :
    LinearIndependent K ![panelSupportExtensor (nv (ends e₀).1) (nv (ends e₀).2),
      panelSupportExtensor (nv (ends e₁).1) (nv (ends e₁).2)] := by
  have h0 : LinearIndependent K ![panelSupportExtensor (nv a) (nv x),
      panelSupportExtensor (nv x) (nv b)] := by
    have := (panelSupportExtensor_linearIndependent_iff (k := k) ![nv a, nv x] ![nv x, nv b]).2
      (by convert linearIndependent_normalsJoin_pair hli using 1; funext i; fin_cases i <;> rfl)
    convert this using 1; funext i; fin_cases i <;> rfl
  rcases hends.eq_or_swap he₀ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
  rcases hends.eq_or_swap he₁ with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
  simp only [h1, h2, h3, h4, panelSupportExtensor_swap (nv a) (nv x),
    panelSupportExtensor_swap (nv x) (nv b), LinearIndependent.pair_neg_left_iff,
    LinearIndependent.pair_neg_right_iff] <;> exact h0

/-- **The rank at the ear** (of `liftAttains_of_ear`): `lem:block-rank-ear` with one interior body
adds at least `2(D - 1) + 2 - D = D`, and `def_d(H) ≤ def_d(G)`. -/
theorem ear_rank [Finite α] [Finite β] (hS : G.Simple) (hNx : ∀ y, G.Adj x y → y = a ∨ y = b)
    (hxa : G.Adj x a) (hxb : G.Adj x b) (hab : a ≠ b) {r : ℕ} {ends : β → α × α}
    (hends : Graph.RecordsLinks G ends) {b0 : α → Fin 4 → K}
    (hlink : ∀ e x y, G.IsLink e x y → LinearIndependent K ![b0 x, b0 y])
    (hli : LinearIndependent K ![b0 a, b0 x, b0 b]) (ζ : Fin r → α → K)
    (hdef : (G.induce (V(G) \ {x})).deficiency (r + 1 + 2) ≤ G.deficiency (r + 1 + 2))
    (hH : (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := r + 1 + 1)
        (G.induce (V(G) \ {x})) ends (fun p => liftNormal b0 ζ p.1 p.2)).toBodyHinge.rigidityRows)
        : ℤ) = screwDim (r + 1 + 1) * ((V(G.induce (V(G) \ {x})).ncard : ℤ) - 1) -
          (G.induce (V(G) \ {x})).deficiency (r + 1 + 2)) :
    (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := r + 1 + 1) G ends
        (fun p => liftNormal b0 ζ p.1 p.2)).toBodyHinge.rigidityRows) : ℤ)
      = screwDim (r + 1 + 1) * ((V(G).ncard : ℤ) - 1) - G.deficiency (r + 1 + 2) := by
  classical
  have := hS
  have hx : x ∈ V(G) := hxa.left_mem
  obtain ⟨e₀, he₀⟩ := hxa
  obtain ⟨e₁, he₁⟩ := hxb
  set F := (PanelHingeFramework.ofNormals (k := r + 1 + 1) G ends
    (fun p => liftNormal b0 ζ p.1 p.2)).toBodyHinge with hF
  have hlin : LinearIndependent K ![liftNormal b0 ζ a, liftNormal b0 ζ x, liftNormal b0 ζ b] :=
    LinearIndependent.of_comp liftProj (by
      convert hli using 1; funext i; fin_cases i <;> exact liftProj_liftVec _ _)
  have hC := ear_hinges_linearIndependent hends he₀.symm he₁ hlin
  have hear := BodyHingeFramework.finrank_span_rigidityRows_ear_eq F (V₁ := V(G) \ {x})
    (k := 1) (x := ![x]) (a := a) (b := b) (e := ![e₀, e₁]) (fun i j _ => Subsingleton.elim i j)
    (fun i h => h.2 (by fin_cases i; rfl)) ⟨he₀.right_mem, he₀.adj.ne.symm⟩
    ⟨he₁.right_mem, he₁.adj.ne.symm⟩ hab (fun i => by
      fin_cases i
      · exact he₀.symm
      · change G.IsLink _ _ _
        simpa [pathVertex] using he₁) (fun f u w hf hne => by
      have hf : G.IsLink f u w := hf
      refine ⟨⟨hf.left_mem, ?_⟩, ⟨hf.right_mem, ?_⟩⟩
      · rintro rfl
        rcases hNx w ⟨f, hf⟩ with rfl | rfl
        · exact hne 0 (hf.unique_edge he₀)
        · exact hne 1 (hf.unique_edge he₁)
      · rintro rfl
        rcases hNx u ⟨f, hf.symm⟩ with rfl | rfl
        · exact hne 0 (hf.unique_edge he₀.symm)
        · exact hne 1 (hf.symm.unique_edge he₁) ) (fun i => by
      fin_cases i
      · exact (LinearIndependent.ne_zero 0 hC)
      · exact (LinearIndependent.ne_zero 1 hC))
  have hsup : 2 ≤ Module.finrank K ↥((⟨F.graph.induce (V(G) \ {x}), F.supportExtensor⟩ :
      BodyHingeFramework K (r + 1 + 1) α β).relScrews a b ⊔
        Submodule.span K (Set.range (F.supportExtensor ∘ ![e₀, e₁]))) := by
    refine le_trans ?_ (Submodule.finrank_mono le_sup_right)
    have : (F.supportExtensor ∘ ![e₀, e₁]) = ![panelSupportExtensor
        (liftNormal b0 ζ (ends e₀).1) (liftNormal b0 ζ (ends e₀).2),
        panelSupportExtensor (liftNormal b0 ζ (ends e₁).1) (liftNormal b0 ζ (ends e₁).2)] := by
      funext i; fin_cases i <;> rfl
    rw [this, finrank_span_eq_card hC]; simp
  have hup := finrank_liftNormal_le hends hlink ⟨x, hx⟩ ζ
  have hcard : (V(G.induce (V(G) \ {x}))).ncard + 1 = V(G).ncard :=
    Set.ncard_sdiff_singleton_add_one hx (Set.toFinite _)
  refine le_antisymm hup ?_
  change (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ) = _ at hear
  have hH' : (Module.finrank K (Submodule.span K (⟨F.graph.induce (V(G) \ {x}),
      F.supportExtensor⟩ : BodyHingeFramework K (r + 1 + 1) α β).rigidityRows) : ℤ) = _ := hH
  rw [hear, hH', ← hcard]
  push_cast
  have : ((2 : ℕ) : ℤ) ≤ _ := Nat.cast_le.2 hsup
  push_cast at this
  nlinarith

/-- **(T1) at the ear** (of `liftAttains_of_ear`): `b'_x` on `Π_a ∩ Π_b` off the span of `b_a`
and `b_b`. -/
theorem ear_T1 [Finite α] (hS : G.Simple) (hNx : ∀ y, G.Adj x y → y = a ∨ y = b)
    (hxa : G.Adj x a) (hxb : G.Adj x b) (hab : a ≠ b) (hxhub : ¬ G.PencilHub x)
    (hahub : G.PencilHub a) (hbhub : G.PencilHub b)
    {F : BodyHingeFramework K 2 α β} {bv nv : α → Fin 4 → K}
    (hnd : IsNondegPencilPlaneRealization (G.induce (V(G) \ {x})) F bv
      (fun y => dotPerp (K ∙ nv y)))
    (hhub : ∀ y, LinearIndepOn K nv (G.closedHubNbhd y))
    (hdot : bv a ⬝ᵥ nv b ≠ 0 ∨ bv b ⬝ᵥ nv a ≠ 0) :
    ∃ (F' : BodyHingeFramework K 2 α β) (b' : α → Fin 4 → K) (P' : α → Submodule K (Fin 4 → K)),
      IsNondegPencilPlaneRealization G F' b' P' ∧ (∀ y ∈ V(G) \ {x}, b' y = bv y) ∧
      ∀ y ∈ V(G) \ {x}, 2 ≤ (G.induce (V(G) \ {x})).degree y → P' y = dotPerp (K ∙ nv y) := by
  classical
  have := hS
  set H := G.induce (V(G) \ {x}) with hH
  have hax : a ≠ x := hxa.ne.symm
  have hbx : b ≠ x := hxb.ne.symm
  have haH : a ∈ V(H) := ⟨hxa.right_mem, hax⟩
  have hbH : b ∈ V(H) := ⟨hxb.right_mem, hbx⟩
  obtain ⟨hb0, hn0, hlink, -, hnhub⟩ := (exists_isNondeg_dotPerp_iff hnd.dotProduct_eq_zero).1
    ⟨F, hnd⟩
  have horth := hnd.dotProduct_eq_zero
  have hHv : ∀ y ∈ V(H), ∀ z ∈ H.closedNbhd y, z ≠ x := fun y hy z hz =>
    (Graph.closedNbhd_subset_vertexSet hy hz).2
  -- `n_a`, `n_b` independent: the closed hub-neighbourhood of `x`
  have hnab : LinearIndependent K ![nv a, nv b] := by
    have h := hhub x
    have hsub : ({a, b} : Set α) ⊆ G.closedHubNbhd x := by
      rintro z (rfl | rfl)
      · exact ⟨hahub, Or.inr (let ⟨e, he⟩ := hxa; ⟨e, he⟩)⟩
      · exact ⟨hbhub, Or.inr (let ⟨e, he⟩ := hxb; ⟨e, he⟩)⟩
    have := (h.mono hsub)
    exact (LinearIndepOn.pair_iff_linearIndependent hab).1 this
  set L := dotPerp (K ∙ nv a) ⊓ dotPerp (K ∙ nv b) with hL
  have hLeq : L = dotPerp (Submodule.span K (Set.range ![nv a, nv b])) := by
    ext y
    rw [hL, Submodule.mem_inf, mem_dotPerp_span_singleton, mem_dotPerp_span_singleton,
      mem_dotPerp_span_range, Fin.forall_fin_two]
    rfl
  have hLdim : Module.finrank K L = 2 := by
    rw [hLeq, finrank_dotPerp, finrank_span_eq_card hnab]; simp
  set W := Submodule.span K (Set.range ![bv a, bv b]) with hW
  have hbab : LinearIndependent K ![bv a, bv b] := by
    refine (LinearIndependent.pair_iff' (hb0 a haH)).2 fun c hc => ?_
    have hbb : bv b ⬝ᵥ nv b = 0 := horth b hbH b (Or.inl rfl)
    have haa : bv a ⬝ᵥ nv a = 0 := horth a haH a (Or.inl rfl)
    rcases hdot with h | h
    · rw [← hc, smul_dotProduct, smul_eq_mul, mul_eq_zero] at hbb
      rcases hbb with rfl | hbb
      · exact hb0 b hbH (by rw [← hc, zero_smul])
      · exact h hbb
    · rw [← hc, smul_dotProduct, smul_eq_mul, haa, mul_zero] at h
      exact h rfl
  obtain ⟨p, hpL, hpW⟩ : ∃ p ∈ L, p ∉ W := by
    by_contra hcon
    push Not at hcon
    have hWdim : Module.finrank K W ≤ 2 := by
      have := finrank_range_le_card (R := K) ![bv a, bv b]
      rw [Set.finrank, Fintype.card_fin] at this
      exact this
    have heq := Submodule.eq_of_le_of_finrank_le (show L ≤ W from hcon) (by omega)
    have ha' : bv a ∈ L := heq ▸ Submodule.subset_span ⟨0, rfl⟩
    have hb' : bv b ∈ L := heq ▸ Submodule.subset_span ⟨1, rfl⟩
    rcases hdot with h | h
    · exact h (mem_dotPerp_span_singleton.1 ha'.2)
    · exact h (mem_dotPerp_span_singleton.1 hb'.1)
  obtain ⟨t, ht0, hta, htp, htb⟩ := exists_ne_zero_orth_three (bv a) p (bv b)
  have hp0 : p ≠ 0 := fun h => hpW (h ▸ Submodule.zero_mem _)
  have hpa : p ⬝ᵥ nv a = 0 := mem_dotPerp_span_singleton.1 hpL.1
  have hpb : p ⬝ᵥ nv b = 0 := mem_dotPerp_span_singleton.1 hpL.2
  have hpi : ∀ y ∈ ({a, b} : Set α), LinearIndependent K ![bv y, p] := by
    rintro y hy
    have hy0 : bv y ≠ 0 := by rcases hy with rfl | rfl; exacts [hb0 _ haH, hb0 _ hbH]
    refine (LinearIndependent.pair_iff' hy0).2 fun c hc => hpW (hc ▸ Submodule.smul_mem _ _ ?_)
    rcases hy with rfl | rfl
    exacts [Submodule.subset_span ⟨0, rfl⟩, Submodule.subset_span ⟨1, rfl⟩]
  set b' := Function.update bv x p
  set n' := Function.update nv x t
  have hb'x : b' x = p := Function.update_self _ _ _
  have hn'x : n' x = t := Function.update_self _ _ _
  have hb' : ∀ y, y ≠ x → b' y = bv y := fun y hy => Function.update_of_ne hy _ _
  have hn' : ∀ y, y ≠ x → n' y = nv y := fun y hy => Function.update_of_ne hy _ _
  have hclx : G.closedNbhd x = {x, a, b} := by
    ext z
    refine ⟨?_, ?_⟩
    · rintro (rfl | ⟨e, he⟩)
      · exact Or.inl rfl
      · rcases hNx z ⟨e, he⟩ with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
    · rintro (rfl | rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr (let ⟨e, he⟩ := hxa; ⟨e, he⟩)
      · exact Or.inr (let ⟨e, he⟩ := hxb; ⟨e, he⟩)
  have hxcl : ∀ y, y ≠ x → x ∈ G.closedNbhd y → y = a ∨ y = b := by
    rintro y hyx (h | ⟨e, he⟩)
    · exact absurd h.symm hyx
    · exact hNx y ⟨e, he.symm⟩
  have hcl : ∀ y ∈ V(G), y ≠ x → y ≠ a → y ≠ b → G.closedNbhd y = H.closedNbhd y := by
    intro y hy hyx hya hyb
    rw [closedNbhd_induce_sdiff_singleton hy hyx,
      Set.sdiff_singleton_eq_self fun h => (hxcl y hyx h).elim hya hyb]
  have horth' : ∀ y ∈ V(G), ∀ z ∈ G.closedNbhd y, b' z ⬝ᵥ n' y = 0 := by
    intro y hy z hz
    by_cases hyx : y = x
    · subst hyx
      rw [hclx] at hz
      rw [hn'x]
      rcases hz with rfl | rfl | rfl
      · rw [hb'x]; rw [dotProduct_comm] at htp ⊢; assumption
      · rw [hb' z hax]; rw [dotProduct_comm] at hta ⊢; assumption
      · rw [hb' z hbx]; rw [dotProduct_comm] at htb ⊢; assumption
    rw [hn' y hyx]
    by_cases hzx : z = x
    · subst hzx
      rw [hb'x]
      rcases hxcl y hyx hz with rfl | rfl
      exacts [hpa, hpb]
    · rw [hb' z hzx]
      refine horth y ⟨hy, hyx⟩ z ?_
      rw [closedNbhd_induce_sdiff_singleton hy hyx]; exact ⟨hz, hzx⟩
  obtain ⟨F', hF'⟩ := (exists_isNondeg_dotPerp_iff horth').2 ⟨fun y hy => by
        by_cases hyx : y = x
        · rw [hyx, hb'x]; exact hp0
        · rw [hb' y hyx]; exact hb0 y ⟨hy, hyx⟩,
      fun y hy => by
        by_cases hyx : y = x
        · rw [hyx, hn'x]; exact ht0
        · rw [hn' y hyx]; exact hn0 y ⟨hy, hyx⟩,
      fun y z hyz => by
        by_cases hyx : y = x
        · subst hyx
          rw [hb'x]
          rcases hNx z hyz with rfl | rfl
          · rw [hb' z hax]; exact LinearIndependent.pair_symm_iff.1 (hpi z (Or.inl rfl))
          · rw [hb' z hbx]; exact LinearIndependent.pair_symm_iff.1 (hpi z (Or.inr rfl))
        by_cases hzx : z = x
        · subst hzx
          rw [hb'x, hb' y hyx]
          exact hpi y (by rcases hNx y hyz.symm with h | h <;> simp [h])
        rw [hb' y hyx, hb' z hzx]
        obtain ⟨e, he⟩ := hyz
        exact hlink y z ⟨e, he, ⟨he.left_mem, hyx⟩, he.right_mem, hzx⟩,
      fun y _ => (hhub y).congr fun z hz => (hn' z fun h => hxhub (h ▸ hz.1)).symm,
      fun y hy hyhub => by
        by_cases hyx : y = x
        · subst hyx
          rw [hclx]
          have hab' : LinearIndepOn K b' {a, b} := by
            rw [LinearIndepOn.pair_iff_linearIndependent hab, hb' a hax, hb' b hbx]
            exact hbab
          refine hab'.insert ?_
          rw [hb'x, Set.image_pair, hb' a hax, hb' b hbx, ← Matrix.range_cons_cons_empty]
          exact hpW
        have hya : y ≠ a := fun h => hyhub (h ▸ hahub)
        have hyb : y ≠ b := fun h => hyhub (h ▸ hbhub)
        rw [hcl y hy hyx hya hyb]
        refine (hnhub y ⟨hy, hyx⟩ fun h => hyhub ⟨hy, ?_⟩).congr fun z hz =>
          (hb' z (hHv y ⟨hy, hyx⟩ z hz)).symm
        have h3 := h.2
        rw [Graph.degree_eq_ncard_adj] at h3 ⊢
        refine h3.trans (Set.ncard_le_ncard (fun z ⟨e, he⟩ => ⟨e, he.1⟩) (Set.toFinite _))⟩
  exact ⟨F', b', _, hF', fun y hy => hb' y hy.2, fun y hy _ => by rw [hn' y hy.2]⟩

/-- The dot product `b_u · n_w` as a polynomial in the coordinates of `E`. -/
noncomputable def bnDotPoly (u w : α) : MvPolynomial (α × Fin 2 × Fin 4) K :=
  ∑ i, MvPolynomial.X (u, 0, i) * MvPolynomial.X (w, 1, i)

theorem eval_bnDotPoly (b n : α → Fin 4 → K) (u w : α) :
    MvPolynomial.eval (bnPoint b n) (bnDotPoly u w) = b u ⬝ᵥ n w := by
  simp [bnDotPoly, dotProduct, bnPoint]

theorem isWeightedHomogeneous_bnDotPoly (u w : α) :
    MvPolynomial.IsWeightedHomogeneous
      (fun p : α × Fin 2 × Fin 4 => Finsupp.single (p.1, p.2.1) 1) (bnDotPoly (K := K) u w)
      (Finsupp.single (u, 0) 1 + Finsupp.single (w, 1) 1) :=
  MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun _ _ =>
    (MvPolynomial.isWeightedHomogeneous_X K _ _).mul (MvPolynomial.isWeightedHomogeneous_X K _ _)

/-- Three independent vectors do not lie in the orthogonal of two independent ones. -/
theorem not_three_le_of_orth {p q w m l : Fin 4 → K} (hli : LinearIndependent K ![p, q, w])
    (hml : LinearIndependent K ![m, l]) (hpm : p ⬝ᵥ m = 0) (hqm : q ⬝ᵥ m = 0)
    (hwm : w ⬝ᵥ m = 0) (hpl : p ⬝ᵥ l = 0) (hql : q ⬝ᵥ l = 0) (hwl : w ⬝ᵥ l = 0) : False := by
  have hle : Submodule.span K (Set.range ![p, q, w]) ≤
      dotPerp (Submodule.span K (Set.range ![m, l])) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, mem_dotPerp_span_range]
    intro j
    fin_cases i <;> fin_cases j <;> simpa
  have h1 := Submodule.finrank_mono hle
  rw [finrank_span_eq_card hli, finrank_dotPerp, finrank_span_eq_card hml] at h1
  simp at h1

/-- **`lem:pencil-d-lift-ear`.** -/
theorem liftAttains_of_ear [Infinite K] [Finite α] [Finite β] (r : ℕ) {G : Graph α β}
    (hS : G.Simple) (hfeas : PencilNondegFeasible K G) {x a b : α} (hx : G.degree x = 2)
    (hxa : G.Adj x a) (hxb : G.Adj x b) (hab : a ≠ b) (ha : G.PencilHub a) (hb : G.PencilHub b)
    (hdef : (G.induce (V(G) \ {x})).deficiency (r + 1 + 2) ≤ G.deficiency (r + 1 + 2)) :
    PencilNondegFeasible K (G.induce (V(G) \ {x})) ∧
      ∀ {hubSel nbrSel : α → Fin 3 → Option α},
        (∀ v, IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v)) →
        (∀ v, ¬ G.PencilHub v → IsFin3SelectorOf (G.closedNbhd v) (nbrSel v)) →
        EarLiftCondition (K := K) G hubSel nbrSel x a b →
        LiftAttains K r (G.induce (V(G) \ {x})) → LiftAttains K r G := by
  classical
  have := hS
  have := Fintype.ofFinite α
  have hax : a ≠ x := hxa.ne.symm
  have hbx : b ≠ x := hxb.ne.symm
  have hxV : x ∈ V(G) := hxa.left_mem
  have hNx : ∀ y, G.Adj x y → y = a ∨ y = b := by
    intro y hy
    by_contra hcon
    push Not at hcon
    have hsub : ({a, b, y} : Set α) ⊆ N(G, x) := by
      rintro z (rfl | rfl | rfl); exacts [hxa, hxb, hy]
    have h3 : ({a, b, y} : Set α).ncard = 3 :=
      Set.ncard_eq_three.2 ⟨a, b, y, hab, Ne.symm hcon.1, Ne.symm hcon.2, rfl⟩
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [h3, ← Graph.degree_eq_ncard_adj, hx] at this
    omega
  have hxhub : ¬ G.PencilHub x := fun h => by have := h.2; omega
  obtain ⟨F₀, normal₀, point₀, hndG, hndH⟩ :=
    exists_isNondegPencilRealization_restrict_of_demoted hS hfeas
      (Graph.induce_le Set.sdiff_subset : G.induce (V(G) \ {x}) ≤ G) (fun y hy _ _ z hyz hnyz => by
        have hzx : z = x := by
          by_contra hzx
          obtain ⟨e, he⟩ := hyz
          exact hnyz ⟨e, he, hy, he.right_mem, hzx⟩
        exact hzx ▸ hxhub)
  refine ⟨⟨_, _, _, hndH⟩, fun {hubSel nbrSel} hHubSel hNbrSel hcond hH => ?_⟩
  have hne : (steerSet (K := K) G hubSel nbrSel).Nonempty :=
    (steerSet_nonempty_iff hHubSel hNbrSel).2 hfeas
  have : Inhabited α := ⟨x⟩
  have hends := Graph.recordsLinks_endsOf G
  -- (T1): `E` the minors of the closed hub-neighbourhoods in `G`, times one of `b_a · n_b`,
  -- `b_b · n_a` nonzero at the steer lemma's realization
  have hind₀ : ∀ y, LinearIndepOn K (fun w i => bnPoint point₀ normal₀ (w, 1, i))
      (G.closedHubNbhd y) := fun y => by
    rw [bnPoint_one]
    by_cases hy : y ∈ V(G)
    · exact hndG.2.2.1 y hy
    · rw [closedHubNbhd_eq_empty_of_notMem hy]; exact linearIndepOn_empty K _
  choose E hEvars hEhom hE0 hEind using fun y => exists_minorPoly (G.closedHubNbhd y) 1 (hind₀ y)
  choose dE hdE using hEhom
  have horth₀ := hndG.toPlane.dotProduct_eq_zero
  have hdot₀ : point₀ a ⬝ᵥ normal₀ b ≠ 0 ∨ point₀ b ⬝ᵥ normal₀ a ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hli := LinearIndepOn.triple (hndG.2.2.2 x hxV hxhub) (Or.inl rfl)
      (Or.inr (let ⟨e, he⟩ := hxa; ⟨e, he⟩)) (Or.inr (let ⟨e, he⟩ := hxb; ⟨e, he⟩)) hax.symm hab
      hbx.symm
    have hml : LinearIndependent K ![normal₀ a, normal₀ b] := by
      have h := (hndG.2.2.1 x hxV).mono (show ({a, b} : Set α) ⊆ G.closedHubNbhd x by
        rintro z (rfl | rfl)
        · exact ⟨ha, Or.inr (let ⟨e, he⟩ := hxa; ⟨e, he⟩)⟩
        · exact ⟨hb, Or.inr (let ⟨e, he⟩ := hxb; ⟨e, he⟩)⟩)
      exact (LinearIndepOn.pair_iff_linearIndependent hab).1 h
    have hxa' : x ∈ G.closedNbhd a := Or.inr (let ⟨e, he⟩ := hxa; ⟨e, he.symm⟩)
    have hxb' : x ∈ G.closedNbhd b := Or.inr (let ⟨e, he⟩ := hxb; ⟨e, he.symm⟩)
    exact not_three_le_of_orth hli hml (horth₀ a hxa.right_mem x hxa')
      (horth₀ a hxa.right_mem a (Or.inl rfl)) hcon.2 (horth₀ b hxb.right_mem x hxb') hcon.1
      (horth₀ b hxb.right_mem b (Or.inl rfl))
  obtain ⟨u₁, w₁, hu₁, hw₁, hD₀, hD⟩ : ∃ u₁ w₁, u₁ ∈ ({a, b} : Set α) ∧
      w₁ ∈ ({a, b} : Set α) ∧ point₀ u₁ ⬝ᵥ normal₀ w₁ ≠ 0 ∧
      ∀ bv nv : α → Fin 4 → K, bv u₁ ⬝ᵥ nv w₁ ≠ 0 →
        bv a ⬝ᵥ nv b ≠ 0 ∨ bv b ⬝ᵥ nv a ≠ 0 := by
    rcases hdot₀ with h | h
    · exact ⟨a, b, Or.inl rfl, Or.inr rfl, h, fun _ _ h => Or.inl h⟩
    · exact ⟨b, a, Or.inr rfl, Or.inl rfl, h, fun _ _ h => Or.inr h⟩
  have hab_mem : ∀ y ∈ ({a, b} : Set α), y ∈ V(G) \ {x} := by
    rintro y (rfl | rfl)
    exacts [⟨hxa.right_mem, hax⟩, ⟨hxb.right_mem, hbx⟩]
  have hT1 : ∃ E : MvPolynomial (α × Fin 2 × Fin 4) K, (∀ p ∈ E.vars, p.1 ∈ V(G) \ {x}) ∧
      (∃ d : α × Fin 2 →₀ ℕ, MvPolynomial.IsWeightedHomogeneous
        (fun p : α × Fin 2 × Fin 4 => Finsupp.single (p.1, p.2.1) 1) E d) ∧
      (∃ (F : BodyHingeFramework K 2 α β) (b n : α → Fin 4 → K),
        IsNondegPencilPlaneRealization (G.induce (V(G) \ {x})) F b (fun v => dotPerp (K ∙ n v)) ∧
        MvPolynomial.eval (bnPoint b n) E ≠ 0) ∧
      ∀ (F : BodyHingeFramework K 2 α β) (b n : α → Fin 4 → K),
        IsNondegPencilPlaneRealization (G.induce (V(G) \ {x})) F b (fun v => dotPerp (K ∙ n v)) →
        MvPolynomial.eval (bnPoint b n) E ≠ 0 →
        ∃ (F' : BodyHingeFramework K 2 α β) (b' : α → Fin 4 → K)
          (P' : α → Submodule K (Fin 4 → K)), IsNondegPencilPlaneRealization G F' b' P' ∧
          (∀ v' ∈ V(G) \ {x}, b' v' = b v') ∧ ∀ v' ∈ V(G) \ {x},
            2 ≤ (G.induce (V(G) \ {x})).degree v' → P' v' = dotPerp (K ∙ n v') := by
    refine ⟨(∏ y, E y) * bnDotPoly u₁ w₁, fun p hp => ?_, ⟨(∑ y, dE y) +
      (Finsupp.single (u₁, 0) 1 + Finsupp.single (w₁, 1) 1),
      (MvPolynomial.IsWeightedHomogeneous.prod _ _ _ fun y _ => hdE y).mul
        (isWeightedHomogeneous_bnDotPoly u₁ w₁)⟩,
      ⟨_, point₀, normal₀, hndH.toPlane, ?_⟩, fun F bv nv hnd hE => ?_⟩
    · rcases Finset.mem_union.1 (MvPolynomial.vars_mul _ _ hp) with hp | hp
      · obtain ⟨y, -, hy⟩ := Finset.mem_biUnion.1 (MvPolynomial.vars_prod _ hp)
        have hmem := hEvars y p hy
        exact ⟨hmem.1.1, fun h => hxhub (h ▸ hmem.1)⟩
      · have := mem_support_of_mem_vars_of_isWeightedHomogeneous
          (fun p : α × Fin 2 × Fin 4 => (p.1, p.2.1)) (isWeightedHomogeneous_bnDotPoly u₁ w₁) hp
        rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply,
          Finsupp.single_apply] at this
        split_ifs at this with h1 h2 h2
        · exact (Prod.mk.inj h1).1 ▸ hab_mem u₁ hu₁
        · exact (Prod.mk.inj h1).1 ▸ hab_mem u₁ hu₁
        · exact (Prod.mk.inj h2).1 ▸ hab_mem w₁ hw₁
        · simp at this
    · rw [map_mul, map_prod, eval_bnDotPoly]
      exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun y _ => hE0 y) hD₀
    · rw [map_mul, map_prod, eval_bnDotPoly] at hE
      refine ear_T1 hS hNx hxa hxb hab hxhub ha hb hnd (fun y => ?_)
        (hD bv nv (right_ne_zero_of_mul hE))
      have := hEind y (bnPoint bv nv)
        (Finset.prod_ne_zero_iff.1 (left_ne_zero_of_mul hE) y (Finset.mem_univ _))
      rwa [bnPoint_one] at this
  have htr := lift_transfer (K := K) (r := r) (V' := V(G) \ {x}) Set.sdiff_subset
    ⟨a, hxa.right_mem, hax⟩ hHubSel hNbrSel (hends.induce _) hT1
    (ear_T2 hS hNx hxa hxb hab hxhub hHubSel hNbrSel hcond) hH
  refine liftAttains_of_holdsGenerally hHubSel hNbrSel hends (htr.mono fun s hs h => ?_)
  obtain ⟨-, ⟨lam, hlam, hrk⟩, -⟩ := h
  have hsU := (mem_steerSet_iff hHubSel hNbrSel).1 hs
  refine ⟨lam, hlam, ear_rank hS hNx hxa hxb hab hends (fun e x y he => hsU.2.2.1 x y ⟨e, he⟩)
    (LinearIndepOn.triple (hsU.2.2.2.2 x hxV hxhub) (Or.inr (let ⟨e, he⟩ := hxa; ⟨e, he⟩))
      (Or.inl rfl) (Or.inr (let ⟨e, he⟩ := hxb; ⟨e, he⟩)) hax hbx.symm hab) _ hdef hrk⟩

end Ear

/-! ## `lem:pencil-d-lift-pendant-triangle` -/

section PendantTriangle

variable {G : Graph α β} {x₁ x₂ c : α}

/-- At a body of degree two with distinct neighbours `a` and `b`, every neighbour is one of them. -/
theorem eq_or_eq_of_degree_eq_two [Finite α] (hS : G.Simple) {x a b : α}
    (hx : G.degree x = 2) (hxa : G.Adj x a) (hxb : G.Adj x b) (hab : a ≠ b) :
    ∀ y, G.Adj x y → y = a ∨ y = b := by
  have := hS
  intro y hy
  by_contra hcon
  push Not at hcon
  have hsub : ({a, b, y} : Set α) ⊆ N(G, x) := by
    rintro z (rfl | rfl | rfl); exacts [hxa, hxb, hy]
  have h3 : ({a, b, y} : Set α).ncard = 3 :=
    Set.ncard_eq_three.2 ⟨a, b, y, hab, Ne.symm hcon.1, Ne.symm hcon.2, rfl⟩
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [h3, ← Graph.degree_eq_ncard_adj, hx] at this
  omega

/-- The closed neighbourhood of a body with at most the neighbours `a` and `b`. -/
theorem closedNbhd_eq_of_nbrs {x a b : α} (hNx : ∀ y, G.Adj x y → y = a ∨ y = b)
    (hxa : G.Adj x a) (hxb : G.Adj x b) : G.closedNbhd x = {x, a, b} := by
  ext z
  refine ⟨?_, ?_⟩
  · rintro (rfl | ⟨e, he⟩)
    · exact Or.inl rfl
    · rcases hNx z ⟨e, he⟩ with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (let ⟨e, he⟩ := hxa; ⟨e, he⟩)
    · exact Or.inr (let ⟨e, he⟩ := hxb; ⟨e, he⟩)

/-- The closed neighbourhood in the graph with a set of bodies deleted. -/
theorem closedNbhd_induce_sdiff {S : Set α} {y : α} (hy : y ∈ V(G)) (hyS : y ∉ S) :
    (G.induce (V(G) \ S)).closedNbhd y = G.closedNbhd y \ S := by
  ext z
  simp only [Graph.closedNbhd, Set.mem_ofPred_eq, Set.mem_sdiff, Graph.induce_isLink]
  constructor
  · rintro (rfl | ⟨e, he, -, hz⟩)
    · exact ⟨Or.inl rfl, hyS⟩
    · exact ⟨Or.inr ⟨e, he⟩, hz.2⟩
  · rintro ⟨rfl | ⟨e, he⟩, hzS⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨e, he, ⟨hy, hyS⟩, he.right_mem, hzS⟩

/-- Two independent members of a set give an independent pair. -/
theorem LinearIndepOn.pair_of_mem {N : ℕ} {f : α → Fin N → K} {S : Set α}
    (h : LinearIndepOn K f S) {p q : α} (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q) :
    LinearIndependent K ![f p, f q] := by
  have := h.comp (fun i : Fin 2 => (⟨![p, q] i, by fin_cases i <;> assumption⟩ : S)) (by
    intro i j hij
    simp only [Subtype.mk.injEq] at hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm])
  convert this using 1
  funext i; fin_cases i <;> rfl

/-- The closed neighbourhoods at a pendant triangle `x₁ x₂ c`. -/
theorem pendantTri_closedNbhds (hS : G.Simple) (hN₁ : ∀ y, G.Adj x₁ y → y = x₂ ∨ y = c)
    (hN₂ : ∀ y, G.Adj x₂ y → y = x₁ ∨ y = c) (h₁₂ : G.Adj x₁ x₂) (h₁c : G.Adj x₁ c)
    (h₂c : G.Adj x₂ c) :
    (∀ y ∈ V(G), y ≠ x₁ → y ≠ x₂ → y ≠ c →
      G.closedNbhd y = (G.induce (V(G) \ {x₁, x₂})).closedNbhd y) ∧
    (∀ z ∈ G.closedNbhd c, z = x₁ ∨ z = x₂ ∨ z ∈ (G.induce (V(G) \ {x₁, x₂})).closedNbhd c) ∧
    G.closedNbhd x₁ = {x₁, x₂, c} ∧ G.closedNbhd x₂ = {x₂, x₁, c} := by
  have := hS
  have hcV : c ∈ V(G) := h₁c.right_mem
  have hcT : c ∉ ({x₁, x₂} : Set α) := by
    rintro (h | h)
    · exact h₁c.ne h.symm
    · exact h₂c.ne h.symm
  refine ⟨fun y hy h1 h2 hyc => ?_, fun z hz => ?_, closedNbhd_eq_of_nbrs hN₁ h₁₂ h₁c,
    closedNbhd_eq_of_nbrs hN₂ h₁₂.symm h₂c⟩
  · have hyT : y ∉ ({x₁, x₂} : Set α) := by
      rintro (h | h)
      · exact h1 h
      · exact h2 h
    rw [closedNbhd_induce_sdiff hy hyT]
    symm
    refine sdiff_eq_left.2 (Set.disjoint_left.2 fun z hz hzT => ?_)
    rcases hz with h | ⟨e, he⟩
    · rw [h] at hzT; exact hyT hzT
    · rcases hzT with h | h
      · rw [h] at he
        rcases hN₁ y ⟨e, he.symm⟩ with h | h
        exacts [h2 h, hyc h]
      · rw [(Set.mem_singleton_iff.1 h)] at he
        rcases hN₂ y ⟨e, he.symm⟩ with h | h
        exacts [h1 h, hyc h]
  · by_cases hzT : z ∈ ({x₁, x₂} : Set α)
    · rcases hzT with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rw [closedNbhd_induce_sdiff hcV hcT]
      exact Or.inr (Or.inr ⟨hz, hzT⟩)


/-- An edge at `x₁` or `x₂` lies in the triangle. -/
theorem pendantTri_mem (hN₁ : ∀ y, G.Adj x₁ y → y = x₂ ∨ y = c)
    (hN₂ : ∀ y, G.Adj x₂ y → y = x₁ ∨ y = c) :
    ∀ y z, G.Adj y z → (y = x₁ ∨ y = x₂ ∨ z = x₁ ∨ z = x₂) →
      y ∈ ({x₁, x₂, c} : Set α) ∧ z ∈ ({x₁, x₂, c} : Set α) := by
  intro y z hyz h
  rcases h with h | h | h | h
  · rw [h] at hyz ⊢
    rcases hN₁ z hyz with h' | h'
    · rw [h']; exact ⟨Or.inl rfl, Or.inr (Or.inl rfl)⟩
    · rw [h']; exact ⟨Or.inl rfl, Or.inr (Or.inr rfl)⟩
  · rw [h] at hyz ⊢
    rcases hN₂ z hyz with h' | h'
    · rw [h']; exact ⟨Or.inr (Or.inl rfl), Or.inl rfl⟩
    · rw [h']; exact ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩
  · rw [h] at hyz ⊢
    rcases hN₁ y hyz.symm with h' | h'
    · rw [h']; exact ⟨Or.inr (Or.inl rfl), Or.inl rfl⟩
    · rw [h']; exact ⟨Or.inr (Or.inr rfl), Or.inl rfl⟩
  · rw [h] at hyz ⊢
    rcases hN₂ y hyz.symm with h' | h'
    · rw [h']; exact ⟨Or.inl rfl, Or.inr (Or.inl rfl)⟩
    · rw [h']; exact ⟨Or.inr (Or.inr rfl), Or.inr (Or.inl rfl)⟩

/-- **(T1) at a pendant triangle** (of `liftAttains_of_pendantTriangle`): a nondegenerate
realization of `H = G - {x₁, x₂}` whose vectors are independent on the closed hub-neighbourhoods
in `G` extends: `b'_{x₁}`, `b'_{x₂}` in `n_c^⊥` completing `b_c` to an independent triple, and
`n'_{x₁} = n'_{x₂} = n_c`. -/
theorem pendantTri_T1 [Finite α] (hS : G.Simple)
    (hN₁ : ∀ y, G.Adj x₁ y → y = x₂ ∨ y = c) (hN₂ : ∀ y, G.Adj x₂ y → y = x₁ ∨ y = c)
    (h₁₂ : G.Adj x₁ x₂) (h₁c : G.Adj x₁ c) (h₂c : G.Adj x₂ c) (hchub : G.PencilHub c)
    (hx₁hub : ¬ G.PencilHub x₁) (hx₂hub : ¬ G.PencilHub x₂)
    {F : BodyHingeFramework K 2 α β} {b n : α → Fin 4 → K}
    (hnd : IsNondegPencilPlaneRealization (G.induce (V(G) \ {x₁, x₂})) F b
      (fun y => dotPerp (K ∙ n y)))
    (hhub : ∀ y, LinearIndepOn K n (G.closedHubNbhd y)) :
    ∃ (F' : BodyHingeFramework K 2 α β) (b' : α → Fin 4 → K) (P' : α → Submodule K (Fin 4 → K)),
      IsNondegPencilPlaneRealization G F' b' P' ∧ (∀ y ∈ V(G) \ {x₁, x₂}, b' y = b y) ∧
      ∀ y ∈ V(G) \ {x₁, x₂}, 2 ≤ (G.induce (V(G) \ {x₁, x₂})).degree y →
        P' y = dotPerp (K ∙ n y) := by
  classical
  have := hS
  set H := G.induce (V(G) \ {x₁, x₂}) with hH
  have h12 : x₁ ≠ x₂ := h₁₂.ne
  have h1c : x₁ ≠ c := h₁c.ne
  have h2c : x₂ ≠ c := h₂c.ne
  have hcV : c ∈ V(G) := h₁c.right_mem
  have hnotT : ∀ {y}, y ≠ x₁ → y ≠ x₂ → y ∉ ({x₁, x₂} : Set α) := by
    rintro y h1 h2 (h | h)
    · exact h1 h
    · exact h2 h
  have hne12 : ∀ {y}, y ∉ ({x₁, x₂} : Set α) → y ≠ x₁ ∧ y ≠ x₂ := fun h =>
    ⟨fun e => h (Or.inl e), fun e => h (Or.inr e)⟩
  have hcH : c ∈ V(H) := ⟨hcV, hnotT h1c.symm h2c.symm⟩
  obtain ⟨hb0, hn0, hlink, -, hnhub⟩ := (exists_isNondeg_dotPerp_iff hnd.dotProduct_eq_zero).1
    ⟨F, hnd⟩
  have horth := hnd.dotProduct_eq_zero
  have hHv : ∀ y ∈ V(H), ∀ z ∈ H.closedNbhd y, z ≠ x₁ ∧ z ≠ x₂ := fun y hy z hz =>
    hne12 (Graph.closedNbhd_subset_vertexSet hy hz).2
  obtain ⟨hcl, hclc, hcl₁, hcl₂⟩ := pendantTri_closedNbhds hS hN₁ hN₂ h₁₂ h₁c h₂c
  have hhubV : ∀ y, ∀ z ∈ G.closedHubNbhd y, z ≠ x₁ ∧ z ≠ x₂ := fun y z hz =>
    ⟨fun h => hx₁hub (h ▸ hz.1), fun h => hx₂hub (h ▸ hz.1)⟩
  -- the new points, in `n_c^⊥` and completing `b_c`
  obtain ⟨p₀, hp₀L, hp₀W⟩ := exists_mem_notMem_of_finrank_lt (p := K ∙ b c)
    (q := dotPerp (K ∙ n c)) (by
      rw [finrank_dotPerp_span_singleton_of_ne_zero (hn0 c hcH)]
      exact lt_of_le_of_lt (by simpa using finrank_span_le_card ({b c} : Set (Fin 4 → K)))
        (by norm_num))
  have hW2 : Module.finrank K (Submodule.span K ({p₀, b c} : Set (Fin 4 → K))) ≤ 2 :=
    (finrank_span_le_ncard _ (Set.toFinite _)).trans
      ((Set.ncard_insert_le _ _).trans (by simp))
  obtain ⟨p₁, hp₁L, hp₁W⟩ := exists_mem_notMem_of_finrank_lt
    (p := Submodule.span K ({p₀, b c} : Set (Fin 4 → K))) (q := dotPerp (K ∙ n c)) (by
      rw [finrank_dotPerp_span_singleton_of_ne_zero (hn0 c hcH)]
      exact lt_of_le_of_lt hW2 (by norm_num))
  have hp₀0 : p₀ ≠ 0 := fun h => hp₀W (h ▸ Submodule.zero_mem _)
  have hp₁0 : p₁ ≠ 0 := fun h => hp₁W (h ▸ Submodule.zero_mem _)
  have hp₀n : p₀ ⬝ᵥ n c = 0 := mem_dotPerp_span_singleton.1 hp₀L
  have hp₁n : p₁ ⬝ᵥ n c = 0 := mem_dotPerp_span_singleton.1 hp₁L
  obtain ⟨b', hb'1, hb'2, hb'⟩ : ∃ b' : α → Fin 4 → K, b' x₁ = p₁ ∧ b' x₂ = p₀ ∧
      ∀ y, y ≠ x₁ → y ≠ x₂ → b' y = b y :=
    ⟨Function.update (Function.update b x₁ p₁) x₂ p₀, by
      rw [Function.update_of_ne h12, Function.update_self], Function.update_self _ _ _,
      fun y h1 h2 => by rw [Function.update_of_ne h2, Function.update_of_ne h1]⟩
  obtain ⟨n', hn'1, hn'2, hn'⟩ : ∃ n' : α → Fin 4 → K, n' x₁ = n c ∧ n' x₂ = n c ∧
      ∀ y, y ≠ x₁ → y ≠ x₂ → n' y = n y :=
    ⟨Function.update (Function.update n x₁ (n c)) x₂ (n c), by
      rw [Function.update_of_ne h12, Function.update_self], Function.update_self _ _ _,
      fun y h1 h2 => by rw [Function.update_of_ne h2, Function.update_of_ne h1]⟩
  have hbc : b' c = b c := hb' c h1c.symm h2c.symm
  have hbT : LinearIndepOn K b' ({x₁, x₂, c} : Set α) := by
    have h0 : LinearIndepOn K b' ({c} : Set α) := by
      rw [linearIndepOn_singleton_iff, hbc]; exact hb0 c hcH
    have h1 : LinearIndepOn K b' ({x₂, c} : Set α) := by
      refine h0.insert ?_
      rw [Set.image_singleton, hb'2, hbc]
      exact hp₀W
    refine h1.insert ?_
    rw [Set.image_pair, hb'1, hb'2, hbc]
    exact hp₁W
  have hbT' : LinearIndepOn K b' ({x₂, x₁, c} : Set α) := by
    rw [Set.insert_comm]; exact hbT
  have hTmem := pendantTri_mem hN₁ hN₂
  have horth' : ∀ y ∈ V(G), ∀ z ∈ G.closedNbhd y, b' z ⬝ᵥ n' y = 0 := by
    intro y hy z hz
    by_cases hy1 : y = x₁
    · rw [hy1] at hz ⊢
      rw [hcl₁] at hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rw [hn'1]
      rcases hz with h | h | h
      · rw [h, hb'1]; exact hp₁n
      · rw [h, hb'2]; exact hp₀n
      · rw [h, hbc]; exact horth c hcH c (Or.inl rfl)
    by_cases hy2 : y = x₂
    · rw [hy2] at hz ⊢
      rw [hcl₂] at hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rw [hn'2]
      rcases hz with h | h | h
      · rw [h, hb'2]; exact hp₀n
      · rw [h, hb'1]; exact hp₁n
      · rw [h, hbc]; exact horth c hcH c (Or.inl rfl)
    rw [hn' y hy1 hy2]
    by_cases hyc : y = c
    · rw [hyc] at hz ⊢
      rcases hclc z hz with h | h | h
      · rw [h, hb'1]; exact hp₁n
      · rw [h, hb'2]; exact hp₀n
      · rw [hb' z (hHv c hcH z h).1 (hHv c hcH z h).2]; exact horth c hcH z h
    · have hyH : y ∈ V(H) := ⟨hy, hnotT hy1 hy2⟩
      rw [hcl y hy hy1 hy2 hyc] at hz
      rw [hb' z (hHv y hyH z hz).1 (hHv y hyH z hz).2]
      exact horth y hyH z hz
  obtain ⟨F', hF'⟩ := (exists_isNondeg_dotPerp_iff horth').2 ⟨fun y hy => by
      by_cases hy1 : y = x₁
      · rw [hy1, hb'1]; exact hp₁0
      by_cases hy2 : y = x₂
      · rw [hy2, hb'2]; exact hp₀0
      · rw [hb' y hy1 hy2]; exact hb0 y ⟨hy, hnotT hy1 hy2⟩,
    fun y hy => by
      by_cases hy1 : y = x₁
      · rw [hy1, hn'1]; exact hn0 c hcH
      by_cases hy2 : y = x₂
      · rw [hy2, hn'2]; exact hn0 c hcH
      · rw [hn' y hy1 hy2]; exact hn0 y ⟨hy, hnotT hy1 hy2⟩,
    fun y z hyz => by
      by_cases hT : y = x₁ ∨ y = x₂ ∨ z = x₁ ∨ z = x₂
      · obtain ⟨hy, hz⟩ := hTmem y z hyz hT
        exact LinearIndepOn.pair_of_mem hbT hy hz hyz.ne
      · push Not at hT
        rw [hb' y hT.1 hT.2.1, hb' z hT.2.2.1 hT.2.2.2]
        obtain ⟨e, he⟩ := hyz
        exact hlink y z ⟨e, he, ⟨he.left_mem, hnotT hT.1 hT.2.1⟩,
          he.right_mem, hnotT hT.2.2.1 hT.2.2.2⟩,
    fun y _ => (hhub y).congr fun z hz =>
      (hn' z (hhubV y z hz).1 (hhubV y z hz).2).symm,
    fun y hy hyhub => by
      by_cases hy1 : y = x₁
      · rw [hy1, hcl₁]; exact hbT
      by_cases hy2 : y = x₂
      · rw [hy2, hcl₂]; exact hbT'
      have hyc : y ≠ c := fun h => hyhub (h ▸ hchub)
      have hyH : y ∈ V(H) := ⟨hy, hnotT hy1 hy2⟩
      rw [hcl y hy hy1 hy2 hyc]
      refine (hnhub y hyH fun h => hyhub ⟨hy, ?_⟩).congr fun z hz =>
        (hb' z (hHv y hyH z hz).1 (hHv y hyH z hz).2).symm
      have h3 := h.2
      rw [Graph.degree_eq_ncard_adj] at h3 ⊢
      exact h3.trans (Set.ncard_le_ncard (fun z ⟨e, he⟩ => ⟨e, he.1⟩) (Set.toFinite _))⟩
  exact ⟨F', b', _, hF', fun y hy => hb' y (hne12 hy.2).1 (hne12 hy.2).2, fun y hy _ => by
    rw [hn' y (hne12 hy.2).1 (hne12 hy.2).2]⟩

/-- **(T2) at a pendant triangle** (of `liftAttains_of_pendantTriangle`):
`ζ_{xᵢ} = ψ_c(b⁰_{xᵢ})`. -/
theorem pendantTri_T2 (hS : G.Simple)
    (hN₁ : ∀ y, G.Adj x₁ y → y = x₂ ∨ y = c) (hN₂ : ∀ y, G.Adj x₂ y → y = x₁ ∨ y = c)
    (h₁₂ : G.Adj x₁ x₂) (h₁c : G.Adj x₁ c) (h₂c : G.Adj x₂ c)
    {hubSel nbrSel : α → Fin 3 → Option α}
    (hHubSel : ∀ v, IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v))
    (hNbrSel : ∀ v, ¬ G.PencilHub v → IsFin3SelectorOf (G.closedNbhd v) (nbrSel v))
    (hne : (steerSet (K := K) G hubSel nbrSel).Nonempty) :
    HoldsGenerally (K := K) G hubSel nbrSel fun b0 P0 =>
      ∀ ζ ∈ liftMaps (G.induce (V(G) \ {x₁, x₂})) b0 P0, ∃ ζ' ∈ liftMaps G b0 P0,
        ∀ y ∈ V(G) \ {x₁, x₂}, ζ' y = ζ y := by
  classical
  have := hS
  have h12 : x₁ ≠ x₂ := h₁₂.ne
  have h1c : x₁ ≠ c := h₁c.ne
  have h2c : x₂ ≠ c := h₂c.ne
  have hnotT : ∀ {y}, y ≠ x₁ → y ≠ x₂ → y ∉ ({x₁, x₂} : Set α) := by
    rintro y h1 h2 (h | h)
    · exact h1 h
    · exact h2 h
  have hne12 : ∀ {y}, y ∉ ({x₁, x₂} : Set α) → y ≠ x₁ ∧ y ≠ x₂ := fun h =>
    ⟨fun e => h (Or.inl e), fun e => h (Or.inr e)⟩
  obtain ⟨hcl, hclc, hcl₁, hcl₂⟩ := pendantTri_closedNbhds hS hN₁ hN₂ h₁₂ h₁c h₂c
  have hcH : c ∈ V(G.induce (V(G) \ {x₁, x₂})) := ⟨h₁c.right_mem, hnotT h1c.symm h2c.symm⟩
  refine HoldsGenerally.of_forall hne fun s hs ζ hζ => ?_
  have hP0G : ∀ y ∈ V(G), ∀ z ∈ G.closedNbhd y,
      steerPoint hubSel s z ∈ dotPerp (K ∙ steerNormal hubSel nbrSel G s y) := fun y _ z hz =>
    mem_dotPerp_span_singleton.2 (steerPoint_dotProduct_steerNormal hHubSel hNbrSel s hz)
  have hP0H : ∀ y ∈ V(G.induce (V(G) \ {x₁, x₂})),
      ∀ z ∈ (G.induce (V(G) \ {x₁, x₂})).closedNbhd y,
      steerPoint hubSel s z ∈ dotPerp (K ∙ steerNormal hubSel nbrSel G s y) := fun y _ z hz =>
    mem_dotPerp_span_singleton.2 (steerPoint_dotProduct_steerNormal_of_le
      (Graph.induce_le Set.sdiff_subset) hHubSel hNbrSel s hz)
  rw [mem_liftMaps_iff hP0H] at hζ
  obtain ⟨ψ, hψ⟩ := hζ c hcH
  obtain ⟨ζ', hζ'1, hζ'2, hζ'⟩ : ∃ ζ' : α → K, ζ' x₁ = ψ (steerPoint hubSel s x₁) ∧
      ζ' x₂ = ψ (steerPoint hubSel s x₂) ∧ ∀ y, y ≠ x₁ → y ≠ x₂ → ζ' y = ζ y :=
    ⟨Function.update (Function.update ζ x₁ (ψ (steerPoint hubSel s x₁))) x₂
      (ψ (steerPoint hubSel s x₂)), by rw [Function.update_of_ne h12, Function.update_self],
      Function.update_self _ _ _,
      fun y h1 h2 => by rw [Function.update_of_ne h2, Function.update_of_ne h1]⟩
  have hHv : ∀ y' ∈ V(G.induce (V(G) \ {x₁, x₂})),
      ∀ z ∈ (G.induce (V(G) \ {x₁, x₂})).closedNbhd y', z ≠ x₁ ∧ z ≠ x₂ := fun y' hy' z hz =>
    hne12 (Graph.closedNbhd_subset_vertexSet hy' hz).2
  have hψc : ζ' c = ψ (steerPoint hubSel s c) := by
    rw [hζ' c h1c.symm h2c.symm]; exact hψ c (Or.inl rfl)
  refine ⟨ζ', (mem_liftMaps_iff hP0G).2 fun y hy => ?_, fun y hy =>
    hζ' y (hne12 hy.2).1 (hne12 hy.2).2⟩
  by_cases hy1 : y = x₁
  · refine ⟨ψ, fun z hz => ?_⟩
    rw [hy1, hcl₁] at hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with h | h | h
    · rw [h, hζ'1]
    · rw [h, hζ'2]
    · rw [h]; exact hψc
  by_cases hy2 : y = x₂
  · refine ⟨ψ, fun z hz => ?_⟩
    rw [hy2, hcl₂] at hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with h | h | h
    · rw [h, hζ'2]
    · rw [h, hζ'1]
    · rw [h]; exact hψc
  by_cases hyc : y = c
  · refine ⟨ψ, fun z hz => ?_⟩
    rw [hyc] at hz
    rcases hclc z hz with h | h | h
    · rw [h, hζ'1]
    · rw [h, hζ'2]
    · rw [hζ' z (hHv c hcH z h).1 (hHv c hcH z h).2]; exact hψ z h
  · have hyH : y ∈ V(G.induce (V(G) \ {x₁, x₂})) := ⟨hy, hnotT hy1 hy2⟩
    obtain ⟨ψ', hψ'⟩ := hζ y hyH
    refine ⟨ψ', fun z hz => ?_⟩
    rw [hcl y hy hy1 hy2 hyc] at hz
    rw [hζ' z (hHv y hyH z hz).1 (hHv y hyH z hz).2]; exact hψ' z hz

/-- **The rank at a pendant triangle** (of `liftAttains_of_pendantTriangle`): the ranks of `H` and
of the rigid triangle add at the cut vertex `c`, and so do the deficiencies, the triangle's being
zero. -/
theorem pendantTri_rank [Finite α] [Finite β] (hS : G.Simple)
    (hN₁ : ∀ y, G.Adj x₁ y → y = x₂ ∨ y = c) (hN₂ : ∀ y, G.Adj x₂ y → y = x₁ ∨ y = c)
    (h₁₂ : G.Adj x₁ x₂) (h₁c : G.Adj x₁ c) (h₂c : G.Adj x₂ c) {r : ℕ} {ends : β → α × α}
    (hends : Graph.RecordsLinks G ends) {b0 : α → Fin 4 → K}
    (hlink : ∀ e x y, G.IsLink e x y → LinearIndependent K ![b0 x, b0 y])
    (hli : LinearIndependent K ![b0 x₁, b0 x₂, b0 c]) (ζ : Fin r → α → K)
    (hH : (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := r + 1 + 1)
        (G.induce (V(G) \ {x₁, x₂})) ends
        (fun p => liftNormal b0 ζ p.1 p.2)).toBodyHinge.rigidityRows) : ℤ) =
        screwDim (r + 1 + 1) * ((V(G.induce (V(G) \ {x₁, x₂})).ncard : ℤ) - 1) -
          (G.induce (V(G) \ {x₁, x₂})).deficiency (r + 1 + 2)) :
    (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := r + 1 + 1) G ends
        (fun p => liftNormal b0 ζ p.1 p.2)).toBodyHinge.rigidityRows) : ℤ)
      = screwDim (r + 1 + 1) * ((V(G).ncard : ℤ) - 1) - G.deficiency (r + 1 + 2) := by
  classical
  have := hS
  have h12 : x₁ ≠ x₂ := h₁₂.ne
  have h1c : x₁ ≠ c := h₁c.ne
  have h2c : x₂ ≠ c := h₂c.ne
  have hcV : c ∈ V(G) := h₁c.right_mem
  have hx₁V : x₁ ∈ V(G) := h₁₂.left_mem
  have hx₂V : x₂ ∈ V(G) := h₁₂.right_mem
  have hTmem := pendantTri_mem hN₁ hN₂
  set V₁ := V(G) \ {x₁, x₂} with hV₁
  set V₂ : Set α := {x₁, x₂, c} with hV₂
  have hV₂G : V₂ ⊆ V(G) := by
    intro z hz
    simp only [V₂, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with h | h | h
    · rw [h]; exact hx₁V
    · rw [h]; exact hx₂V
    · rw [h]; exact hcV
  have hcT : c ∉ ({x₁, x₂} : Set α) := by
    rintro (h | h)
    · exact h1c h.symm
    · exact h2c h.symm
  have hcover : V₁ ∪ V₂ = V(G) := by
    refine Set.Subset.antisymm (Set.union_subset Set.sdiff_subset hV₂G) fun z hz => ?_
    by_cases hzT : z ∈ ({x₁, x₂} : Set α)
    · rcases hzT with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inl ⟨hz, hzT⟩
  have hoverlap : V₁ ∩ V₂ = {c} := by
    ext z
    constructor
    · rintro ⟨⟨-, hz1⟩, hz2⟩
      rcases hz2 with h | h | h
      · exact absurd (Or.inl h) hz1
      · exact absurd (Or.inr h) hz1
      · exact h
    · intro h
      rw [Set.mem_singleton_iff] at h
      rw [h]
      exact ⟨⟨hcV, hcT⟩, Or.inr (Or.inr rfl)⟩
  have hsepG : ∀ e x y, G.IsLink e x y → (x ∈ V₁ ∧ y ∈ V₁) ∨ (x ∈ V₂ ∧ y ∈ V₂) := by
    intro e x y hl
    by_cases hT : x = x₁ ∨ x = x₂ ∨ y = x₁ ∨ y = x₂
    · exact Or.inr (hTmem x y ⟨e, hl⟩ hT)
    · push Not at hT
      exact Or.inl ⟨⟨hl.left_mem, fun h => by rcases h with h | h; exacts [hT.1 h, hT.2.1 h]⟩,
        ⟨hl.right_mem, fun h => by rcases h with h | h; exacts [hT.2.2.1 h, hT.2.2.2 h]⟩⟩
  -- the rank adds at the cut vertex `c`
  have hrows : Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := r + 1 + 1)
        G ends (fun p => liftNormal b0 ζ p.1 p.2)).toBodyHinge.rigidityRows)
      = Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := r + 1 + 1)
          (G.induce V₁) ends (fun p => liftNormal b0 ζ p.1 p.2)).toBodyHinge.rigidityRows)
        + Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := r + 1 + 1)
          (G.induce V₂) ends (fun p => liftNormal b0 ζ p.1 p.2)).toBodyHinge.rigidityRows) :=
    BodyHingeFramework.finrank_span_rigidityRows_cutVertex_eq _ (V₁ := V₁) (V₂ := V₂) (v := c)
      hoverlap.subset hsepG
  -- the triangle is rigid, of rank `2D`
  obtain ⟨e₀, he₀⟩ := h₁₂
  obtain ⟨e₁, he₁⟩ := h₂c
  obtain ⟨e₂, he₂⟩ := h₁c
  have hx₁₂ : x₁ ∈ V₂ := Or.inl rfl
  have hx₂₂ : x₂ ∈ V₂ := Or.inr (Or.inl rfl)
  have hc₂ : c ∈ V₂ := Or.inr (Or.inr rfl)
  have hlin : LinearIndependent K ![liftNormal b0 ζ x₁, liftNormal b0 ζ x₂, liftNormal b0 ζ c] :=
    LinearIndependent.of_comp liftProj (by
      convert hli using 1; funext i; fin_cases i <;> exact liftProj_liftVec _ _)
  have hTri := finrank_triangle (K := K) (G := G.induce V₂) (k := r + 1 + 1) h12 h2c h1c
    (Graph.vertexSet_induce G V₂) ((Graph.induce_isLink G V₂ e₀ x₁ x₂).mpr ⟨he₀, hx₁₂, hx₂₂⟩)
    ((Graph.induce_isLink G V₂ e₁ x₂ c).mpr ⟨he₁, hx₂₂, hc₂⟩)
    ((Graph.induce_isLink G V₂ e₂ c x₁).mpr ⟨he₂.symm, hc₂, hx₁₂⟩) (hends.induce V₂) hlin
  have hneT : V(G.induce V₂).Nonempty := ⟨x₁, hx₁₂⟩
  have hupT := finrank_liftNormal_le (G := G.induce V₂) (hends.induce V₂)
    (fun e u v h => hlink e u v h.1) hneT ζ
  rw [hTri] at hupT
  have hV₂card : V(G.induce V₂).ncard = 3 :=
    Set.ncard_eq_three.2 ⟨x₁, x₂, c, h12, h1c, h2c, rfl⟩
  have hdefT := (G.induce V₂).deficiency_nonneg (r + 1 + 2) hneT
  rw [hV₂card] at hupT
  push_cast at hupT
  have hdefT0 : (G.induce V₂).deficiency (r + 1 + 2) = 0 := by linarith
  have hdef := Graph.deficiency_eq_add_of_cutVertex hS.toLoopless (r + 1 + 2) hcover hoverlap hsepG
  have hcard : V₁.ncard + 2 = V(G).ncard := by
    have h2 : ({x₁, x₂} : Set α).ncard = 2 := Set.ncard_pair h12
    have h3 := Set.ncard_le_ncard (show ({x₁, x₂} : Set α) ⊆ V(G) from
      Set.insert_subset hx₁V (Set.singleton_subset_iff.2 hx₂V)) (Set.toFinite _)
    rw [hV₁, Set.ncard_sdiff (Set.insert_subset hx₁V (Set.singleton_subset_iff.2 hx₂V)), h2]
    omega
  have hcardZ : (V(G).ncard : ℤ) = V₁.ncard + 2 := by exact_mod_cast hcard.symm
  change (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := r + 1 + 1) G
    ends (fun p => liftNormal b0 ζ p.1 p.2)).toBodyHinge.rigidityRows) : ℤ) = _
  rw [hrows, hTri, hdef, hdefT0, hcardZ]
  push_cast
  rw [Graph.vertexSet_induce] at hH
  linarith

/-- **`lem:pencil-d-lift-pendant-triangle`.** The pin takes (T1), (T2) and the rank of the
chapter's proof in the template of `liftAttains_of_pendant`: (T1) the steer lemma and the minors of
the closed hub-neighbourhoods (`pendantTri_T1`), (T2) the maps of `c` read off at the two bodies
(`pendantTri_T2`), the rank by the cut vertex `c` (`pendantTri_rank`). -/
theorem liftAttains_of_pendantTriangle [Infinite K] [Finite α] [Finite β] (r : ℕ)
    {G : Graph α β} (hS : G.Simple) (hfeas : PencilNondegFeasible K G) {x₁ x₂ c : α}
    (h₁ : G.degree x₁ = 2) (h₂ : G.degree x₂ = 2) (h₁₂ : G.Adj x₁ x₂) (h₁c : G.Adj x₁ c)
    (h₂c : G.Adj x₂ c) (hc : 4 ≤ G.degree c) :
    PencilNondegFeasible K (G.induce (V(G) \ {x₁, x₂})) ∧
      (LiftAttains K r (G.induce (V(G) \ {x₁, x₂})) → LiftAttains K r G) := by
  classical
  have := hS
  have := Fintype.ofFinite α
  have h12 : x₁ ≠ x₂ := h₁₂.ne
  have h1c : x₁ ≠ c := h₁c.ne
  have h2c : x₂ ≠ c := h₂c.ne
  have hcV : c ∈ V(G) := h₁c.right_mem
  have hN₁ := eq_or_eq_of_degree_eq_two hS h₁ h₁₂ h₁c h2c
  have hN₂ := eq_or_eq_of_degree_eq_two hS h₂ h₁₂.symm h₂c h1c
  have hx₁hub : ¬ G.PencilHub x₁ := fun h => by have := h.2; omega
  have hx₂hub : ¬ G.PencilHub x₂ := fun h => by have := h.2; omega
  have hchub : G.PencilHub c := ⟨hcV, by omega⟩
  have hcT : c ∉ ({x₁, x₂} : Set α) := by
    rintro (h | h)
    · exact h1c h.symm
    · exact h2c h.symm
  -- (T1)'s realization: the steer lemma, the lost neighbours `x₁`, `x₂` being no hubs
  obtain ⟨F₀, normal₀, point₀, hndG, hndH⟩ :=
    exists_isNondegPencilRealization_restrict_of_demoted hS hfeas
      (Graph.induce_le Set.sdiff_subset : G.induce (V(G) \ {x₁, x₂}) ≤ G)
      (fun y hy _ _ z hyz hnyz => by
        have hz : z = x₁ ∨ z = x₂ := by
          by_contra hcon
          push Not at hcon
          obtain ⟨e, he⟩ := hyz
          exact hnyz ⟨e, he, hy, he.right_mem, fun h => by
            rcases h with h | h; exacts [hcon.1 h, hcon.2 h]⟩
        rcases hz with h | h
        · exact h ▸ hx₁hub
        · exact h ▸ hx₂hub)
  refine ⟨⟨_, _, _, hndH⟩, fun hH => ?_⟩
  obtain ⟨hubSel, nbrSel, hHubSel, hNbrSel⟩ := exists_steer_selectors hfeas
  have hne : (steerSet (K := K) G hubSel nbrSel).Nonempty :=
    (steerSet_nonempty_iff hHubSel hNbrSel).2 hfeas
  have : Inhabited α := ⟨c⟩
  have hends := Graph.recordsLinks_endsOf G
  -- (T1): `E` the minors of the closed hub-neighbourhoods in `G`
  have hind₀ : ∀ y, LinearIndepOn K (fun w i => bnPoint point₀ normal₀ (w, 1, i))
      (G.closedHubNbhd y) := fun y => by
    rw [bnPoint_one]
    by_cases hy : y ∈ V(G)
    · exact hndG.2.2.1 y hy
    · rw [closedHubNbhd_eq_empty_of_notMem hy]; exact linearIndepOn_empty K _
  choose E hEvars hEhom hE0 hEind using fun y => exists_minorPoly (G.closedHubNbhd y) 1 (hind₀ y)
  choose dE hdE using hEhom
  have hT1 : ∃ E : MvPolynomial (α × Fin 2 × Fin 4) K, (∀ p ∈ E.vars, p.1 ∈ V(G) \ {x₁, x₂}) ∧
      (∃ d : α × Fin 2 →₀ ℕ, MvPolynomial.IsWeightedHomogeneous
        (fun p : α × Fin 2 × Fin 4 => Finsupp.single (p.1, p.2.1) 1) E d) ∧
      (∃ (F : BodyHingeFramework K 2 α β) (b n : α → Fin 4 → K),
        IsNondegPencilPlaneRealization (G.induce (V(G) \ {x₁, x₂})) F b
          (fun v => dotPerp (K ∙ n v)) ∧ MvPolynomial.eval (bnPoint b n) E ≠ 0) ∧
      ∀ (F : BodyHingeFramework K 2 α β) (b n : α → Fin 4 → K),
        IsNondegPencilPlaneRealization (G.induce (V(G) \ {x₁, x₂})) F b
          (fun v => dotPerp (K ∙ n v)) → MvPolynomial.eval (bnPoint b n) E ≠ 0 →
        ∃ (F' : BodyHingeFramework K 2 α β) (b' : α → Fin 4 → K)
          (P' : α → Submodule K (Fin 4 → K)), IsNondegPencilPlaneRealization G F' b' P' ∧
          (∀ v' ∈ V(G) \ {x₁, x₂}, b' v' = b v') ∧ ∀ v' ∈ V(G) \ {x₁, x₂},
            2 ≤ (G.induce (V(G) \ {x₁, x₂})).degree v' → P' v' = dotPerp (K ∙ n v') := by
    refine ⟨∏ y, E y, fun p hp => ?_, ⟨∑ y, dE y,
      MvPolynomial.IsWeightedHomogeneous.prod _ _ _ fun y _ => hdE y⟩,
      ⟨_, point₀, normal₀, hndH.toPlane, ?_⟩, fun F b n hnd hE =>
        pendantTri_T1 hS hN₁ hN₂ h₁₂ h₁c h₂c hchub hx₁hub hx₂hub hnd fun y => ?_⟩
    · obtain ⟨y, -, hy⟩ := Finset.mem_biUnion.1 (MvPolynomial.vars_prod _ hp)
      have hmem := hEvars y p hy
      exact ⟨hmem.1.1, fun h => by
        rcases h with h | h
        · exact hx₁hub (h ▸ hmem.1)
        · exact hx₂hub ((Set.mem_singleton_iff.1 h) ▸ hmem.1)⟩
    · rw [map_prod]; exact Finset.prod_ne_zero_iff.2 fun y _ => hE0 y
    · rw [map_prod] at hE
      have := hEind y (bnPoint b n) (Finset.prod_ne_zero_iff.1 hE y (Finset.mem_univ _))
      rwa [bnPoint_one] at this
  have htr := lift_transfer (K := K) (r := r) (V' := V(G) \ {x₁, x₂}) Set.sdiff_subset
    ⟨c, hcV, hcT⟩ hHubSel hNbrSel (hends.induce _) hT1
    (pendantTri_T2 hS hN₁ hN₂ h₁₂ h₁c h₂c hHubSel hNbrSel hne) hH
  refine liftAttains_of_holdsGenerally hHubSel hNbrSel hends (htr.mono fun s hs h => ?_)
  obtain ⟨-, ⟨lam, hlam, hrk⟩, -⟩ := h
  have hsU := (mem_steerSet_iff hHubSel hNbrSel).1 hs
  have hx₁V : x₁ ∈ V(G) := h₁₂.left_mem
  have hcl₁ := (pendantTri_closedNbhds hS hN₁ hN₂ h₁₂ h₁c h₂c).2.2.1
  refine ⟨lam, hlam, pendantTri_rank hS hN₁ hN₂ h₁₂ h₁c h₂c hends
    (fun e x y he => hsU.2.2.1 x y ⟨e, he⟩) ?_ _ hrk⟩
  have hli := hsU.2.2.2.2 x₁ hx₁V hx₁hub
  rw [hcl₁] at hli
  exact LinearIndepOn.triple hli (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) h12
    h2c h1c

end PendantTriangle

end CombinatorialRigidity.Molecular
